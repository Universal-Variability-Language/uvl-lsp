use std::collections::HashMap;
use std::sync::Arc;

use crate::core::*;
use regex::Regex;
use tower_lsp::jsonrpc::Result;
use tower_lsp::lsp_types::*;

pub fn rename_dash(
    params: CodeActionParams,
    diagnostic: Diagnostic,
    snapshot: std::result::Result<Option<(Draft, Arc<RootGraph>)>, tower_lsp::jsonrpc::Error>,
) -> Result<Option<CodeActionResponse>> {
    if let Ok(Some((Draft::UVL { source, .. }, ..))) = snapshot {
        let start_byte = byte_offset(&diagnostic.range.start, &source);
        let end_byte = byte_offset(&diagnostic.range.end, &source);
        let name = source.slice(start_byte..end_byte).as_str().unwrap();
        let new_name = name.replace("-", "_").to_string();

        let code_action_replace = CodeAction {
            title: format!("Rename to: {}", new_name),
            kind: Some(CodeActionKind::QUICKFIX),
            edit: Some(WorkspaceEdit {
                changes: Some(HashMap::<Url, Vec<TextEdit>>::from([(
                    params.text_document.uri.clone(),
                    vec![TextEdit {
                        range: diagnostic.range,
                        new_text: new_name.clone(),
                    }],
                )])),
                document_changes: None,
                change_annotations: None,
            }),
            is_preferred: Some(true),
            diagnostics: Some(vec![diagnostic.clone()]),
            ..Default::default()
        };
        let code_action_quotes = CodeAction {
            title: format!("Rename to: {}", format!("\"{}\"", name)),
            kind: Some(CodeActionKind::QUICKFIX),
            edit: Some(WorkspaceEdit {
                changes: Some(HashMap::<Url, Vec<TextEdit>>::from([(
                    params.text_document.uri.clone(),
                    vec![TextEdit {
                        range: diagnostic.range,
                        new_text: format!("\"{}\"", name),
                    }],
                )])),
                document_changes: None,
                change_annotations: None,
            }),
            is_preferred: Some(true),
            diagnostics: Some(vec![diagnostic.clone()]),
            ..Default::default()
        };
        return Ok(Some(vec![
            CodeActionOrCommand::CodeAction(code_action_replace),
            CodeActionOrCommand::CodeAction(code_action_quotes),
        ]));
    } else {
        return Ok(None);
    }
}

pub fn reference_to_string(
    params: CodeActionParams,
    diagnostic: Diagnostic,
    snapshot: std::result::Result<Option<(Draft, Arc<RootGraph>)>, tower_lsp::jsonrpc::Error>,
) -> Result<Option<CodeActionResponse>> {
    if let Ok(Some((Draft::UVL { source, .. }, ..))) = snapshot {
        let start_byte = byte_offset(&diagnostic.range.start, &source);
        let end_byte = byte_offset(&diagnostic.range.end, &source);
        let name = source.slice(start_byte..end_byte).as_str().unwrap();
        let new_name = name.replace("\"", "\'").to_string();

        if !name.contains("\"") {
            return Ok(None);
        }

        let code_action_replace = CodeAction {
            title: format!("Replace double by single quotation marks: {}", new_name),
            kind: Some(CodeActionKind::QUICKFIX),
            edit: Some(WorkspaceEdit {
                changes: Some(HashMap::<Url, Vec<TextEdit>>::from([(
                    params.text_document.uri.clone(),
                    vec![TextEdit {
                        range: diagnostic.range,
                        new_text: new_name.clone(),
                    }],
                )])),
                document_changes: None,
                change_annotations: None,
            }),
            is_preferred: Some(true),
            diagnostics: Some(vec![diagnostic.clone()]),
            ..Default::default()
        };
        return Ok(Some(vec![CodeActionOrCommand::CodeAction(
            code_action_replace,
        )]));
    } else {
        return Ok(None);
    }
}

pub fn add_indentation(
    params: CodeActionParams,
    diagnostic: Diagnostic,
    snapshot: std::result::Result<Option<(Draft, Arc<RootGraph>)>, tower_lsp::jsonrpc::Error>,
) -> Result<Option<CodeActionResponse>> {
    if let Ok(Some((Draft::UVL { source, .. }, ..))) = snapshot {
        let start_byte = byte_offset(&diagnostic.range.start, &source);
        let end_byte = byte_offset(&diagnostic.range.end, &source);
        let name = source.slice(start_byte..end_byte).as_str().unwrap();
        let new_name = format!("\t{}", name);

        let code_action_replace = CodeAction {
            title: "add indentation".to_string(),
            kind: Some(CodeActionKind::QUICKFIX),
            edit: Some(WorkspaceEdit {
                changes: Some(HashMap::<Url, Vec<TextEdit>>::from([(
                    params.text_document.uri.clone(),
                    vec![TextEdit {
                        range: diagnostic.range,
                        new_text: new_name.clone(),
                    }],
                )])),
                document_changes: None,
                change_annotations: None,
            }),
            is_preferred: Some(true),
            diagnostics: Some(vec![diagnostic.clone()]),
            ..Default::default()
        };
        return Ok(Some(vec![CodeActionOrCommand::CodeAction(
            code_action_replace,
        )]));
    } else {
        return Ok(None);
    }
}

pub fn surround_with_double_quotes(
    params: CodeActionParams,
    diagnostic: Diagnostic,
    snapshot: std::result::Result<Option<(Draft, Arc<RootGraph>)>, tower_lsp::jsonrpc::Error>,
) -> Result<Option<CodeActionResponse>> {
    if let Ok(Some((Draft::UVL { source, .. }, ..))) = snapshot {
        let start_byte = byte_offset(&diagnostic.range.start, &source);
        let end_byte = byte_offset(&diagnostic.range.end, &source);
        let name = source.slice(start_byte..end_byte).as_str().unwrap();
        let new_name = format!("\"{}\"", name);

        let code_action_replace = CodeAction {
            title: format!("add double quotes: {}", new_name),
            kind: Some(CodeActionKind::QUICKFIX),
            edit: Some(WorkspaceEdit {
                changes: Some(HashMap::<Url, Vec<TextEdit>>::from([(
                    params.text_document.uri.clone(),
                    vec![TextEdit {
                        range: diagnostic.range,
                        new_text: new_name.clone(),
                    }],
                )])),
                document_changes: None,
                change_annotations: None,
            }),
            is_preferred: Some(true),
            diagnostics: Some(vec![diagnostic.clone()]),
            ..Default::default()
        };
        return Ok(Some(vec![CodeActionOrCommand::CodeAction(
            code_action_replace,
        )]));
    } else {
        return Ok(None);
    }
}

pub fn starts_with_number(
    params: CodeActionParams,
    diagnostic: Diagnostic,
    snapshot: std::result::Result<Option<(Draft, Arc<RootGraph>)>, tower_lsp::jsonrpc::Error>,
) -> Result<Option<CodeActionResponse>> {
    if let Ok(Some((Draft::UVL { source, .. }, ..))) = snapshot.clone() {
        let start_byte = byte_offset(&diagnostic.range.start, &source);
        let end_byte = byte_offset(&diagnostic.range.end, &source);
        let name = source.slice(start_byte..end_byte).as_str().unwrap();

        let re = Regex::new(r"^\d+").unwrap();
        let number = re.find(name).unwrap().as_str();
        let new_name = format!("{}_{}", &name[number.len()..], number);

        let code_action_number_to_back = CodeAction {
            title: format!("move number to the back: {}", new_name),
            kind: Some(CodeActionKind::QUICKFIX),
            edit: Some(WorkspaceEdit {
                changes: Some(HashMap::<Url, Vec<TextEdit>>::from([(
                    params.text_document.uri.clone(),
                    vec![TextEdit {
                        range: diagnostic.range,
                        new_text: new_name.clone(),
                    }],
                )])),
                document_changes: None,
                change_annotations: None,
            }),
            is_preferred: Some(true),
            diagnostics: Some(vec![diagnostic.clone()]),
            ..Default::default()
        };

        let mut result = vec![CodeActionOrCommand::CodeAction(code_action_number_to_back)];
        match surround_with_double_quotes(params, diagnostic, snapshot) {
            Ok(Some(v)) => result.append(v.to_owned().as_mut()),
            _ => (),
        }
        return Ok(Some(result));
    } else {
        return Ok(None);
    }
}
