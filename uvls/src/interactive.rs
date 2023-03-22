use crate::ast::*;
use crate::{
    semantic::RootSymbol,
    smt::{self, Binding, SmtModel},
};
use hashbrown::HashMap;
use serde::{Deserialize, Serialize};
use std::sync::Arc;
use tokio::{
    select, spawn,
    sync::{mpsc, oneshot},
};
use tokio_util::sync::CancellationToken;
use tower_lsp::lsp_types::*;
use ustr::Ustr;

use crate::semantic::Context;

#[derive(Deserialize, Debug)]
#[serde(untagged)]
pub enum ValueConfig {
    Number(f64),
    Bool(bool),
}
#[derive(Deserialize, Debug)]
pub struct FileConfig {
    selections: Vec<(String, ValueConfig)>,
}
#[derive(Deserialize, Debug)]
pub struct Config {
    files: Vec<(Url, FileConfig)>,
    base_file: Url,
    timestamp: String,
}

#[derive(Deserialize, Debug)]
pub struct OpenSessionParams {
    initial_config: Config,
    base_model: Url,
}
#[derive(Serialize, Debug)]
#[serde(tag = "type")]
pub enum ValueInfo {
    Feature {
        value: bool,
        fixed: bool,
        unsat: bool,
    },
    Attribute {
        value: f64,
        start: f64,
        end: f64,
        unsat: bool,
    },
}
#[derive(Serialize, Debug)]
pub struct ValueState {
    name: Ustr,
    range: Range,
    info: ValueInfo,
    children: Vec<ValueState>,
}

#[derive(Serialize, Debug)]
pub struct FileState {
    uri: Url,
    content: Vec<ValueState>,
}

#[derive(Serialize, Debug)]
pub struct State {
    files: Vec<FileState>,
    timestamp: String,
    info: String,
}

#[derive(Serialize, Debug)]
pub struct Response {
    model: State,
    session: String,
}

use std::error;
type IResult<T> = std::result::Result<T, Box<dyn error::Error>>;
pub enum Message {
    Update(
        Config,
        oneshot::Sender<Result<Response, String>>,
        Option<String>,
    ),
    Close(String),
}
pub fn config_to_sym(
    conf: Config,
    ctx: &Binding,
) -> Result<(HashMap<RootSymbol, bool>, HashMap<RootSymbol, f64>)> {
    let mut features = HashMap::new();
    let mut attribs = HashMap::new();
    for (uri, conf) in conf.files.iter() {
        if let Some(file) = ctx.root().file_by_uri(uri){
            let file_id = ctx.root().file_id(uri).unwrap();
            for (path, val) in conf.selections.iter().map(|(path, val)| {
                (
                    path.split(".").map(|i| Ustr::from(i)).collect::<Vec<_>>(),
                    val,
                )
            }) {
                if let Some(sym) = file
                    .lookup(Symbol::Root, &path, |sym| {
                        matches!(
                            sym,
                            Symbol::Root | Symbol::Feature(..) | Symbol::Attribute(..)
                        )
                    })
                    .next()
                {
                    match (sym,val){
                        (Symbol::Attribute(..),ValueConfig::Number(num))=>{attribs.insert(RootSymbol { file: file_id,sym }, *num);},
                        (Symbol::Feature(..),ValueConfig::Bool(num))=>{features.insert(RootSymbol { file: file_id,sym }, *num);},
                        _=>return 
                    }

                }
                //write!(&mut out,"",ctx.bind(sym,file_id).unwrap());
            }
        }
    }
    Ok((features,attribs))


}
pub fn define_attribs(
    file: &AstDocument,
    ctx: &Binding,
    redefine_attribs: &HashMap<RootSymbol, f64>,
)->Option<String> {
    let out = String::new();
    for m in ctx.members(){
        let file = ctx.root().file(m);
        for  i in file.all_attributes(){
            match file.value(i).unwrap(){
                Value::Number(mut num)=>{
                    if let Some(rnum) = redefine_attribs.get(&RootSymbol{file:m,sym:i}){
                        num = *rnum;
                    }
                    write!(out,"(assert  (! (= {} (ite {}  {:?} 0.0)  )named c{}))")

                }
                _=>{

                }

            }

        }

    }
    Some(out)

}

pub async fn create_model(
    conf: Config,
    session: String,
    timestamp: String,
    ctx: &Context,
) -> IResult<(SmtModel, Response, u64)> {
    let root = ctx
        .snapshot_sync(&conf.base_file, ctx.latest_timestamp(&conf.base_file).await)
        .await
        .ok_or_else(|| "shutdown")?;
    let base_id = root.file_id(&conf.base_file).ok_or("internal error")?;
    let members = root.fs().recursive_imports(base_id);
    let binding = Binding::new(&root, &members);
    let model_src = smt::smtlib_model(&binding, false)
        .await
        .ok_or("failed to create model source")?;
    let cancel = CancellationToken::new();
    let mut model = SmtModel::new(model_src, &cancel).await?;
    if !model.check_sat(&cancel).await? {
        Ok((
            model,
            Response {
                session,
                model: State {
                    files: vec![],
                    timestamp,
                    info: "the underlying model is inconsistent".into(),
                },
            },
            root.revision(),
        ))
    } else {
        Err("")?
    }
}
pub async fn session(
    mut rx: mpsc::Receiver<Message>,
    ctx: Arc<Context>,
    id: String,
    initial_conf: Config,
    initial_res: oneshot::Sender<Result<Response, String>>,
) {
    loop {
        let msg = select! {
            _=ctx.shutdown.cancelled()=>break,
            Some(msg) = rx.recv()=>msg,
            else => break
        };
        match msg {
            Message::Update(conf, res, ..) => {}
            Message::Close(..) => {}
        }
    }
}

pub async fn handler(mut rx: mpsc::Receiver<Message>, ctx: Arc<Context>) {
    let mut sessions = HashMap::new();
    let mut counter: u64 = 0;
    loop {
        let msg = select! {
            _=ctx.shutdown.cancelled()=>break,
            Some(msg) = rx.recv()=>msg,
            else => break
        };
        match msg {
            Message::Update(conf, res, None) => {
                let (tx, rx) = mpsc::channel(32);
                let session_id = format!("s{counter}");
                counter += 1;
                sessions.insert(session_id.clone(), tx);
                let _ = spawn(session(rx, ctx.clone(), session_id, conf, res));
            }
            Message::Update(conf, res, Some(id)) => {
                if let Some(tx) = sessions.get(&id) {
                    let _ = tx.send(Message::Update(conf, res, Some(id))).await;
                } else {
                    let _ = res.send(Response{});
                }
            }
            Message::Close(id) => {
                if let Some(tx) = sessions.get(&id) {
                    let _ = tx.send(Message::Close(id)).await;
                }
            }
        }
    }
}
