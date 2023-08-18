#![allow(non_snake_case)]
use crate::ast::Type;
use crate::module::ModuleSymbol;
use crate::webview::*;
//Render UVL content to HTML
fn Spinner(cx: Scope) -> Element {
    cx.render(rsx! {
    svg{
        width:"24",
        height:"24",
        view_box:"0 0 24 24",
        xmlns:"http://www.w3.or,urig/2000/svg",
        path{
            class:"spinner-bg",
            opacity:".25",
            d:"M12,1A11,11,0,1,0,23,12,11,11,0,0,0,12,1Zm0,19a8,8,0,1,1,8-8A8,8,0,0,1,12,20Z"
        }
        circle{
            class:"spinner",
            cx:"12",
            cy:"2.5",
            r:"1.5"
        }

    }})
}
//Icons taken from https://heroicons.com/ as SVG
#[inline_props]
fn Icon(cx: Scope, icon: Icon, class: Option<&'static str>) -> Element {
    let paths:&[_] =  match icon {
        Icon::File => {&["M19.5 14.25v-2.625a3.375 3.375 0 00-3.375-3.375h-1.5A1.125 1.125 0 0113.5 7.125v-1.5a3.375 3.375 0 00-3.375-3.375H8.25m2.25 0H5.625c-.621 0-1.125.504-1.125 1.125v17.25c0 .621.504 1.125 1.125 1.125h12.75c.621 0 1.125-.504 1.125-1.125V11.25a9 9 0 00-9-9z"]}
        Icon::Feature => {&["M4.745 3A23.933 23.933 0 003 12c0 3.183.62 6.22 1.745 9M19.5 3c.967 2.78 1.5 5.817 1.5 9s-.533 6.22-1.5 9M8.25 8.885l1.444-.89a.75.75 0 011.105.402l2.402 7.206a.75.75 0 001.104.401l1.445-.889m-8.25.75l.213.09a1.687 1.687 0 002.062-.617l4.45-6.676a1.688 1.688 0 012.062-.618l.213.09"]}
        Icon::Attribute => {&[
            "M9.594 3.94c.09-.542.56-.94 1.11-.94h2.593c.55 0 1.02.398 1.11.94l.213 1.281c.063.374.313.686.645.87.074.04.147.083.22.127.324.196.72.257 1.075.124l1.217-.456a1.125 1.125 0 011.37.49l1.296 2.247a1.125 1.125 0 01-.26 1.431l-1.003.827c-.293.24-.438.613-.431.992a6.759 6.759 0 010 .255c-.007.378.138.75.43.99l1.005.828c.424.35.534.954.26 1.43l-1.298 2.247a1.125 1.125 0 01-1.369.491l-1.217-.456c-.355-.133-.75-.072-1.076.124a6.57 6.57 0 01-.22.128c-.331.183-.581.495-.644.869l-.213 1.28c-.09.543-.56.941-1.11.941h-2.594c-.55 0-1.02-.398-1.11-.94l-.213-1.281c-.062-.374-.312-.686-.644-.87a6.52 6.52 0 01-.22-.127c-.325-.196-.72-.257-1.076-.124l-1.217.456a1.125 1.125 0 01-1.369-.49l-1.297-2.247a1.125 1.125 0 01.26-1.431l1.004-.827c.292-.24.437-.613.43-.992a6.932 6.932 0 010-.255c.007-.378-.138-.75-.43-.99l-1.004-.828a1.125 1.125 0 01-.26-1.43l1.297-2.247a1.125 1.125 0 011.37-.491l1.216.456c.356.133.751.072 1.076-.124.072-.044.146-.087.22-.128.332-.183.582-.495.644-.869l.214-1.281z",
            "M15 12a3 3 0 11-6 0 3 3 0 016 0z"                    
            ]}
        Icon::Expand => {
            &["M19.5 8.25l-7.5 7.5-7.5-7.5"]
        }
        Icon::Collapse => {
            &["M8.25 4.5l7.5 7.5-7.5 7.5"]
        }
        Icon::Attributes => {&["M10.5 6h9.75M10.5 6a1.5 1.5 0 11-3 0m3 0a1.5 1.5 0 10-3 0M3.75 6H7.5m3 12h9.75m-9.75 0a1.5 1.5 0 01-3 0m3 0a1.5 1.5 0 00-3 0m-3.75 0H7.5m9-6h3.75m-3.75 0a1.5 1.5 0 01-3 0m3 0a1.5 1.5 0 00-3 0m-9.75 0h9.75"]}
        Icon::Circle=>{
            &["M15 12H9m12 0a9 9 0 11-18 0 9 9 0 0118 0z"]
        }
        Icon::CircleCheck=>{
            &["M9 12.75L11.25 15 15 9.75M21 12a9 9 0 11-18 0 9 9 0 0118 0z"]
        }
        Icon::CircleCross=>{
            &["M9.75 9.75l4.5 4.5m0-4.5l-4.5 4.5M21 12a9 9 0 11-18 0 9 9 0 0118 0z"]
        }
        Icon::CirclePlus=>{
            &["M12 9v6m3-3H9m12 0a9 9 0 11-18 0 9 9 0 0118 0z"]
        }
        Icon::Link=>{
            &[
                "M13.5 6H5.25A2.25 2.25 0 003 8.25v10.5A2.25 2.25 0 005.25 21h10.5A2.25 2.25 0 0018 18.75V10.5m-10.5 6L21 3m0 0h-5.25M21 3v5.25"
            ]
        }
    };
    let paths = paths.iter().map(|p| {
        rsx! {
            path{
                stroke_linecap:"round",
                stroke_linejoin:"round",
                d:"{p}"
            }
        }
    });
    let class = class.unwrap_or("icon");

    cx.render(rsx! {
        svg{
            xmlns:"http://www.w3.org/2000/svg",
            fill:"none",
            view_box:"0 0 24 24",
            stroke_width:"1.5",
            stroke:"currentColor",
            class:"{class}",
            paths
        }
    })
}
#[derive(Props)]
struct ConfigInputProps<'a> {
    #[props(!optional)]
    config: Option<&'a ConfigValue>,
    #[props(!optional)]
    base: Option<&'a ConfigValue>,
    ty: Type,
    unsat: bool,
    sym: ModuleSymbol,
    tag: u8,
}
fn to_number(input: &str) -> String {
    let mut split = input.split('.');
    let first = split
        .next()
        .unwrap()
        .chars()
        .filter(|c| match c {
            '0'..='9' => true,
            _ => false,
        })
        .collect();
    if let Some(second) = split.next() {
        let second: String = second
            .chars()
            .filter(|c| match c {
                '0'..='9' => true,
                _ => false,
            })
            .collect();
        format!("{first}.{second}")
    } else {
        first
    }
}
#[inline_props]
fn RealInput(cx: Scope, init_val: f64, sym: ModuleSymbol, tag: u8) -> Element {
    let tx = use_coroutine_handle::<UIAction>(cx).unwrap();
    let val = use_state(cx, || init_val.to_string());
    cx.render(rsx! {
        input{
            class:"input-value",
            r#type:"number",
            required:true,
            value:"{val}",
            oninput:move |e|{
                val.set(to_number(&e.value));
                tx.send(UIAction::Set(*sym,*tag,ConfigValue::Number(val.parse().unwrap_or(0.0))));

            }
        }
    })
}

fn ConfigInput<'a>(cx: Scope<'a, ConfigInputProps<'a>>) -> Element {
    let ConfigInputProps {
        ty,
        unsat,
        config,
        base,
        sym,
        tag,
    } = &cx.props;
    let tx = use_coroutine_handle::<UIAction>(cx).unwrap();

    if let Some(config) = config {
        let rest = rsx! {
            rsx!{button{
                class:"delete-btn",
                onclick:move |_|{
                    tx.send(UIAction::Unset(*sym,*tag));
                },
                Icon{icon:Icon::CircleCross,class:"btn-icon"}
            }}
            if *unsat{
                rsx!{span{
                    class:"unsat",
                    "UNSAT CONFIG"
                }}
            }
        };
        let inputs = match config {
            ConfigValue::Bool(b) => rsx! {
                div{
                    class:"value-btn",
                    onclick:move |_|{
                        tx.send(UIAction::Set(*sym,*tag,ConfigValue::Bool(!b)));
                    },
                    "{b}"
                }
            },
            ConfigValue::Number(num) => rsx! {
                RealInput{
                    sym:*sym,
                    init_val:*num,
                    tag:*tag,
                }
            },
            ConfigValue::String(x) => rsx! {
                input{
                    class:"input-value",
                    r#type:"text",
                    value:"{x}",
                    oninput:move |e|{

                        tx.send(UIAction::Set(*sym,*tag,ConfigValue::String(e.value.replace('"',""))));
                        cx.needs_update();

                    }
                }
            },
            _ => rsx! { div {
                config.to_string()
            }},
        };
        cx.render(rsx! {
            div{
                class:"config",
                inputs
                rest

            }

        })
    } else {
        cx.render(rsx!{
            div{
                class:"value-slot",
                onclick:move |_|{
                    tx.send(UIAction::Set(*sym,*tag,base.cloned().unwrap_or(ConfigValue::default(*ty))));
                },
                if let Some(val) = base{
                    if *ty == Type::String{
                        rsx!{"\"{val}\""}
                    }
                    else{
                        rsx!{"{val}"}
                    }
                }
                else{
                    rsx!{"?"}
                }
            }
        })
    }
}

#[inline_props]
fn Value(cx: Scope, value: UIEntryValue, sym: ModuleSymbol, tag: u8) -> Element {
    match value {
        UIEntryValue::Attributes(..) => None,
        UIEntryValue::File { .. } => None,
        UIEntryValue::Feature {
            config,
            smt_value,
            ty,
            unsat,
            ..
        } => cx.render(rsx! {
            ConfigInput{
                config:config.as_ref(),
                base:smt_value.as_ref(),
                unsat:*unsat,
                sym:*sym,
                ty:*ty,
                tag:*tag,
            }
        }),

        UIEntryValue::Link {
            config,
            smt_value,
            ty,
            unsat,
            ..
        } => cx.render(rsx! {
            ConfigInput{
                config:config.as_ref(),
                base:smt_value.as_ref(),
                unsat:*unsat,
                sym:*sym,
                ty:*ty,
                tag:*tag,
            }
        }),
        UIEntryValue::Attribute {
            config,
            default,
            unsat,
            ..
        } => cx.render(rsx! {
            ConfigInput{
                config:config.as_ref(),
                base:Some(default),
                unsat:*unsat,
                sym:*sym,
                ty:default.ty(),
                tag:*tag,
            }
        }),
    }
}
fn icon(value: &UIEntryValue) -> Icon {
    match value {
        UIEntryValue::Attributes(..) => Icon::Attributes,
        UIEntryValue::File { .. } => Icon::File,
        UIEntryValue::Feature { .. } => Icon::Feature,
        UIEntryValue::Attribute { .. } => Icon::Attribute,
        UIEntryValue::Link { .. } => Icon::Link,
    }
}
#[inline_props]
fn FileEntry(cx: Scope, node: UIEntry, leaf: bool, sym: ModuleSymbol, tag: u8) -> Element {
    let pad = node.depth * 30;
    let ui_task = use_coroutine_handle::<UIAction>(cx).unwrap();
    let val = rsx! {Value{value:node.value.clone(),sym:*sym,tag:*tag}};
    let name = match &node.value {
        UIEntryValue::File { alias, name } => {
            if let Some(alias) = alias {
                format!("{}", alias)
            } else {
                format!("{}", name)
            }
        }
        UIEntryValue::Link { name, .. } => name.clone(),
        UIEntryValue::Attribute { name, .. }
        | UIEntryValue::Feature { name, .. }
        | UIEntryValue::Attributes(name) => format!("{}", name),
    };

    let icon = icon(&node.value);
    let name = match &node.value {
        UIEntryValue::Attribute { .. }
        | UIEntryValue::Feature { .. }
        | UIEntryValue::File { .. } => rsx! {
            span{
                class:"name-sel",
                onclick: move |_|{
                    ui_task.send(UIAction::ShowSym(*sym,*tag));
                },
                name
                Icon{icon:icon}
            }
        },
        UIEntryValue::Link { tgt, .. } => rsx! {
            span{
                class:"name-sel",
                onclick: move |_|{
                    ui_task.send(UIAction::ShowSym(*tgt,*tag));
                },
                name
                Icon{icon:icon}
            }

        },
        _ => rsx! {
            span{
                class:"name",
                name
                Icon{icon:icon}
            }
        },
    };

    if *leaf {
        cx.render(rsx! {
           tr{
                td{
                    span{
                        style:"padding-left:{pad}px",
                        name
                    }
                }
                td{
                    class:"value-row",
                    val
                }
           }
        })
    } else {
        cx.render(rsx! {
           tr{
                td{
                    div{
                        style:"padding-left:{pad}px",
                        class:"entry",
                        span{
                            class:"toggle",
                            onclick:move |_|{
                                ui_task.send(UIAction::ToggleEntry(*sym,*tag))
                            },
                            if node.open{
                                rsx!{Icon{icon:Icon::Collapse}}

                            }
                            else{
                                rsx!{Icon{icon:Icon::Expand}}

                            }
                        }
                        name
                    }
                }
                td{
                    class:"value-row",
                    val
                }
           }
        })
    }
}
fn file_values_iter<'a, 'b>(state: &'b UIConfigState) -> impl Iterator<Item = LazyNodes<'a, 'b>>
where
    'a: 'b,
{
    let mut closed = None;
    let tag = state.tag;
    state
        .entries
        .iter()
        .enumerate()
        .filter(move |(_, (_, v))| {
            if closed.map(|d| d < v.depth).unwrap_or(false) {
                false
            } else {
                if v.open {
                    closed = None
                } else {
                    closed = Some(v.depth)
                }
                true
            }
        })
        .map(move |(i, (k, v))| {
            let leaf = state
                .entries
                .get_index(i + 1)
                .map(|(_, vn)| vn.depth <= v.depth)
                .unwrap_or(true);
            //Resolve link
            if let UIEntryValue::Link{name,tgt,..} = &v.value{
                let UIEntryValue::Feature {  config, smt_value, ty, unsat,.. }  = &state.entries[tgt].value else{
                    panic!()
                };

                rsx! {
                    FileEntry{node:UIEntry{
                        open:v.open,
                        depth:v.depth,
                        value: UIEntryValue::Link{
                            tgt:*k,
                            name:name.clone(),
                            config:config.clone(),
                            smt_value:smt_value.clone(),
                            ty:*ty,
                            unsat:*unsat
                        }
                    },leaf:leaf,sym:*tgt,key:"{k:?}",tag:tag}
                }
            }
            else{
                rsx! {
                    FileEntry{node:v.clone(),leaf:leaf,sym:*k,key:"{k:?}",tag:tag}
                }
            }
        })
}

pub fn App(cx: Scope<AppProps>) -> Element {
    let config = use_ref(cx, UIConfigState::default);
    let state = use_ref(cx, || UIState {
        solver_active: false,
        sat: SatState::UNKNOWN,
        sync: UISyncState::Dirty,
        dir: "".into(),
        file_name: "".into(),
        show: false,
    });
    let ui_tx = use_coroutine(cx, |rx: UnboundedReceiver<UIAction>| {
        let pipeline = cx.props.pipeline.clone();
        let init = cx.props.initial.clone();
        let id = cx.props.id;
        to_owned![state, config];
        async move {
            if let Err(r) = ui_main(id, pipeline, state.clone(), config, rx, init).await {
                state.with_mut(|state| {
                    state.sync = UISyncState::InternalError(format!("{}", r));
                });
            }
        }
    });
    let lock = config.read();
    let state_lock = state.read();
    match state_lock.sync.clone() {
        UISyncState::InternalError(err) => cx.render(rsx! {
            div {
                "configuration error: {err}"
            }
        }),

        UISyncState::Dirty => cx.render(rsx! {
            div{
                class:"loading",
                "Loading Model"
                Spinner{}
            }
        }),
        UISyncState::Valid => {
            let values = file_values_iter(&lock);
            let solver_state = if state_lock.solver_active {
                "active"
            } else {
                "idle"
            };
            cx.render(rsx! {
                div {
                    ul{
                        li{
                            "OutputFile: "
                            input{
                                r#type:"text",
                                value:"{state_lock.file_name}",
                                oninput: |e|{
                                    state.with_mut(|state|state.file_name = e.value.clone())
                                }

                            }
                        }
                        li{
                            "SAT State: "
                            a{
                                class: if matches!(&state_lock.sat,SatState::SAT){
                                    "sat"
                                }
                                else{
                                    "unsat"
                                },
                                "{state_lock.sat:?}"
                            }
                        }
                        li{
                            "Solver State: "
                            a{
                                "{solver_state}"
                            }
                        }
                        li{
                            button{
                                class:"btn-save",
                                onclick: move |_|{
                                    ui_tx.send(UIAction::Save);
                                },
                                "Save"

                            }
                        }

                        li{
                            button{
                                class:"btn-save",
                                onclick: move |_|{
                                    ui_tx.send(UIAction::Show);
                                },
                                if !state_lock.show{
                                    rsx!{"Show"}
                                }
                                else{
                                    rsx!{"Hide"}

                                }
                            }
                        }
                        li{
                            button{
                                class:"btn-save",
                                onclick: move |_|{
                                    ui_tx.send(UIAction::ExpandAll);
                                },
                                rsx!{"Expand All"}
                            }
                        }
                        li{
                            button{
                                class:"btn-save",
                                onclick: move |_|{
                                    ui_tx.send(UIAction::CollapseAll);
                                },
                                rsx!{"Collapse All"}
                            }
                        }
                    }
                    "Files:"
                    table{
                        thead{
                            tr{
                                th{
                                    "Path"
                                }
                                th{
                                    "Configuration"
                                }
                            }
                        }
                        values
                    }
                }
            })
        }
    }
}
