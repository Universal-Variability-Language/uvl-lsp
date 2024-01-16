use std::collections::HashMap;
use std::fmt::format;
use std::sync::Arc;

use crate::core::*;
use nom::Compare;
use regex::Regex;
use tower_lsp::jsonrpc::Result;
use tower_lsp::lsp_types::*;

/// Adds the quickfixes if the feature name contains a dash
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

        // Replaces dash with an underscore
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

        // Puts the complete feature name in quotes
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

/// Adds indentation if the feature is at the same indentation level as keywords
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

/// Adds the quickfix to write the full name in double quotes if the feature starts with a number
pub fn surround_with_double_quotes(
    params: CodeActionParams,
    diagnostic: Diagnostic,
    snapshot: std::result::Result<Option<(Draft, Arc<RootGraph>)>, tower_lsp::jsonrpc::Error>,
) -> Result<Option<CodeActionResponse>> {
    if let Ok(Some((Draft::UVL { source, .. }, ..))) = snapshot {
        let start_byte = byte_offset(&diagnostic.range.start, &source);
        let end_byte = byte_offset(&diagnostic.range.end, &source);
        let name = source
            .slice(start_byte..end_byte)
            .as_str()
            .unwrap()
            .replace("\n", "")
            .replace("\r", "");
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

/// Adds the quickfixes if the feature name starts with a number
pub fn starts_with_number(
    params: CodeActionParams,
    diagnostic: Diagnostic,
    snapshot: std::result::Result<Option<(Draft, Arc<RootGraph>)>, tower_lsp::jsonrpc::Error>,
) -> Result<Option<CodeActionResponse>> {
    if let Ok(Some((Draft::UVL { source, .. }, ..))) = snapshot.clone() {
        let start_byte = byte_offset(&diagnostic.range.start, &source);
        let end_byte = byte_offset(&diagnostic.range.end, &source);
        let name = &source
            .slice(start_byte..end_byte)
            .as_str()
            .unwrap()
            .trim()
            .replace("\n", "")
            .replace("\r", "");

        let re = Regex::new(r"^\d+").unwrap();
        let number = match re.find(name) {
            Some(x) => x.as_str(),
            None => "",
        };
        let new_name = format!("{}_{}", &name[number.len()..], number);

        // The number at the beginning of the feature name is appended to the end
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

        // The entire feature is placed in double_quotes
        match surround_with_double_quotes(params, diagnostic, snapshot) {
            Ok(Some(v)) => result.append(v.to_owned().as_mut()),
            _ => (),
        }
        return Ok(Some(result));
    } else {
        return Ok(None);
    }
}

/// Checks all possible types of quickfixes for the wrong/missing language_level in features
pub fn wrong_language_level(
    params: CodeActionParams,
    diagnostic: Diagnostic,
    snapshot: std::result::Result<Option<(Draft, Arc<RootGraph>)>, tower_lsp::jsonrpc::Error>,
) -> Result<Option<CodeActionResponse>> {
    let mut result: Vec<CodeActionOrCommand> = vec![];
    // adds the missing language level
    match add_language_level(params.clone(), diagnostic.clone(), snapshot.clone()) {
        Ok(Some(v)) => result.append(v.to_owned().as_mut()),
        _ => (),
    }
    // the wrong feature type will be deleted
    match drop_feature(params.clone(), diagnostic.clone(), snapshot.clone()) {
        Ok(Some(v)) => result.append(v.to_owned().as_mut()),
        _ => (),
    }
    // adds the feature type as an attribute
    match add_type_as_attribute(params.clone(), diagnostic.clone(), snapshot.clone()) {
        Ok(Some(v)) => result.append(v.to_owned().as_mut()),
        _ => (),
    }

    // result set that is returned
    return Ok(Some(result));
}

/// Checks all possible types of quickfixes for the wrong/missing language_level in constraints
pub fn wrong_language_level_constraint(
    params: CodeActionParams,
    diagnostic: Diagnostic,
    snapshot: std::result::Result<Option<(Draft, Arc<RootGraph>)>, tower_lsp::jsonrpc::Error>,
) -> Result<Option<CodeActionResponse>> {
    let mut result: Vec<CodeActionOrCommand> = vec![];
    // adds the missing language level
    match add_language_level(params.clone(), diagnostic.clone(), snapshot.clone()) {
        Ok(Some(v)) => result.append(v.to_owned().as_mut()),
        _ => (),
    }
    // the incorrect restriction is completely deleted
    match drop_constraint(params.clone(), diagnostic.clone(), snapshot.clone()) {
        Ok(Some(v)) => result.append(v.to_owned().as_mut()),
        _ => (),
    }

    // result set that is returned
    return Ok(Some(result));
}

/// Adds the quickfix to include the missing language_level
pub fn add_language_level(
    params: CodeActionParams,
    diagnostic: Diagnostic,
    snapshot: std::result::Result<Option<(Draft, Arc<RootGraph>)>, tower_lsp::jsonrpc::Error>,
) -> Result<Option<CodeActionResponse>> {
    if let Ok(Some((Draft::UVL { source, .. }, ..))) = snapshot.clone() {
        let reg_sub_lvl = Regex::new(r"\[.*\]").unwrap(); // get position of include
        let reg_sub = Regex::new(r"^[^\(]*").unwrap(); // get position of include
        let reg_indent = Regex::new(r"^[^(n\\)]*").unwrap(); // get position of include
        let code = source.to_string();

        // get the position of 'include'
        let range = match code.find("include") {
            Some(0) => Range::new(
                Position {
                    line: 0,
                    character: 0,
                },
                Position {
                    line: 0,
                    character: 7,
                },
            ),
            Some(n) => {
                // calculate the indentation of 'include'
                let indent = if code[0..n].contains("\n") {
                    match reg_indent.find(&code[0..n].chars().rev().collect::<String>()) {
                        Some(m) => m.as_str().len() - 1,
                        _ => 0,
                    }
                } else {
                    n
                } as u32;

                Range::new(
                    Position {
                        line: 0,
                        character: 0,
                    },
                    Position {
                        line: code[0..n].matches("\n").count() as u32,
                        character: indent + 7,
                    },
                )
            }
            None => return Ok(None),
        };

        // lvl as stated by the error message
        let lvl = diagnostic
            .message
            .split_whitespace()
            .nth(7)
            .unwrap_or_default();

        // retrieve right include from error message
        let new_include = match reg_sub.find(lvl) {
            None => return Ok(None),
            Some(l) => {
                let sub_lvl = match reg_sub_lvl.find(lvl) {
                    None => "",
                    Some(s) => {
                        let sl = s.as_str();
                        if sl.len() < 3 {
                            ""
                        } else {
                            match &sl[1..sl.len() - 1] {
                                "FeatureCardinality" => ".feature-cardinality",
                                "Aggregate" => ".aggregate-function",
                                "GroupCardinality" => ".group-cardinality",
                                "NumericConstraints" => ".numeric-constraints",
                                "StringConstraints" => ".string-constraints",
                                _ => "",
                            }
                        }
                    }
                };
                format!("{}{}", l.as_str(), sub_lvl)
            }
        };

        // assemble the corresponding code_action as a solution
        let code_action_add_include = CodeAction {
            title: format!("add {:?} to includes", new_include),
            kind: Some(CodeActionKind::QUICKFIX),
            edit: Some(WorkspaceEdit {
                changes: Some(HashMap::<Url, Vec<TextEdit>>::from([(
                    params.text_document.uri.clone(),
                    vec![TextEdit {
                        range: range,
                        new_text: format!("include\n\t{}", new_include),
                    }],
                )])),
                document_changes: None,
                change_annotations: None,
            }),
            is_preferred: Some(true),
            diagnostics: Some(vec![diagnostic.clone()]),
            ..Default::default()
        };

        // result set that is returned
        let result = vec![CodeActionOrCommand::CodeAction(
            code_action_add_include.clone(),
        )];

        return Ok(Some(result));
    } else {
        return Ok(None);
    }
}

/// Adds the quickfix to completely delete the corresponding constraint
pub fn drop_constraint(
    params: CodeActionParams,
    diagnostic: Diagnostic,
    snapshot: std::result::Result<Option<(Draft, Arc<RootGraph>)>, tower_lsp::jsonrpc::Error>,
) -> Result<Option<CodeActionResponse>> {
    if let Ok(Some((Draft::UVL { source, .. }, ..))) = snapshot {
        let start_byte = byte_offset(&diagnostic.range.start, &source);
        let mut end_byte = byte_offset(&diagnostic.range.end, &source);

        // Find the end position at the end of the respective line and create the new range
        while end_byte < source.len_chars()
            && source.slice(end_byte - 1..end_byte).as_str().unwrap() != "\r"
        {
            end_byte += 1;
        }
        let new_range: Range = Range {
            start: (diagnostic.range.start),
            end: (byte_to_line_col(end_byte, &source)),
        };

        // Output name for quickfix / text of the complete line
        let name = source
            .slice(start_byte..end_byte)
            .as_str()
            .unwrap()
            .replace("\n", "")
            .replace("\r", "");

        // assemble the corresponding code_action as a solution
        let code_action_drop_constraint = CodeAction {
            title: format!("drop constraint: {:?}", name),
            kind: Some(CodeActionKind::QUICKFIX),
            edit: Some(WorkspaceEdit {
                changes: Some(HashMap::<Url, Vec<TextEdit>>::from([(
                    params.text_document.uri.clone(),
                    vec![TextEdit {
                        range: new_range,
                        new_text: "".to_string(),
                    }],
                )])),
                document_changes: None,
                change_annotations: None,
            }),
            is_preferred: Some(true),
            diagnostics: Some(vec![diagnostic.clone()]),
            ..Default::default()
        };

        // result set that is returned
        return Ok(Some(vec![CodeActionOrCommand::CodeAction(
            code_action_drop_constraint,
        )]));
    } else {
        return Ok(None);
    }
}

/// Adds the quickfix to completely delete the corresponding feature
pub fn drop_feature(
    params: CodeActionParams,
    diagnostic: Diagnostic,
    snapshot: std::result::Result<Option<(Draft, Arc<RootGraph>)>, tower_lsp::jsonrpc::Error>,
) -> Result<Option<CodeActionResponse>> {
    if let Ok(Some((Draft::UVL { source, .. }, ..))) = snapshot {
        let start_byte = byte_offset(&diagnostic.range.start, &source);
        let end_byte = byte_offset(&diagnostic.range.end, &source);

        // Name of feature including type
        let name = source
            .slice(start_byte..end_byte)
            .as_str()
            .unwrap()
            .replace("\n", "")
            .replace("\r", "");
        let parts: Vec<&str> = name.split_whitespace().collect();

        // assemble the corresponding code_action as a solution
        let code_action_drop_feature = CodeAction {
            title: format!("drop {:?}", parts.first().unwrap().to_string()),
            kind: Some(CodeActionKind::QUICKFIX),
            edit: Some(WorkspaceEdit {
                changes: Some(HashMap::<Url, Vec<TextEdit>>::from([(
                    params.text_document.uri.clone(),
                    vec![TextEdit {
                        range: diagnostic.range,
                        new_text: parts.last().unwrap().to_string(),
                    }],
                )])),
                document_changes: None,
                change_annotations: None,
            }),
            is_preferred: Some(true),
            diagnostics: Some(vec![diagnostic.clone()]),
            ..Default::default()
        };

        // result set that is returned
        return Ok(Some(vec![CodeActionOrCommand::CodeAction(
            code_action_drop_feature,
        )]));
    } else {
        return Ok(None);
    }
}

/// Adds the quickfix to append the feature's corresponding Type as an attribute
pub fn add_type_as_attribute(
    params: CodeActionParams,
    diagnostic: Diagnostic,
    snapshot: std::result::Result<Option<(Draft, Arc<RootGraph>)>, tower_lsp::jsonrpc::Error>,
) -> Result<Option<CodeActionResponse>> {
    if let Ok(Some((Draft::UVL { source, .. }, ..))) = snapshot {
        let start_byte = byte_offset(&diagnostic.range.start, &source);
        let mut end_byte = byte_offset(&diagnostic.range.end, &source);

        // Find the end position at the end of the respective line and create the new range
        while end_byte < source.len_chars()
            && source.slice(end_byte - 1..end_byte).as_str().unwrap() != "\r"
        {
            end_byte += 1;
        }
        let new_range: Range = Range {
            start: (diagnostic.range.start),
            end: (byte_to_line_col(end_byte, &source)),
        };

        // text of the complete line
        let mut name = source
            .slice(start_byte..end_byte)
            .as_str()
            .unwrap()
            .replace("\n", "")
            .replace("\r", "");

        // split cardinality string and attribute string if available
        if name.contains("]{") {
            name = name.replace("]{", "] {");
        }

        // splitting the name into parts
        let parts: Vec<&str> = name.split_whitespace().collect();

        // create one part for cardinality
        let mut has_cardinality = false;
        let mut cardinality_string: String = String::new();

        for part in parts.iter().skip(2) {
            if part.contains("cardinality") {
                has_cardinality = true;
            }

            if has_cardinality {
                cardinality_string.push_str(part);
                if cardinality_string.contains("]") {
                    break;
                }
                cardinality_string.push(' ')
            }
        }
        let spaced_cardinality_string: String = format!(" {}", cardinality_string);

        //create one part for attributes
        let mut has_attributes = false;
        let mut attributes_string: String = String::new();

        for part in parts.iter().skip(2) {
            if part.contains("{") {
                has_attributes = true;
            }

            if has_attributes {
                attributes_string.push_str(part);
                if attributes_string.contains("}") {
                    break;
                }
                attributes_string.push(' ')
            }
        }

        // create grouped parts
        // 0 = Current Type
        // 1 = Feature name
        // 2 = cardinality
        // 3 = attributes
        // 4 = default value of current type
        let mut grouped_parts: Vec<&str> = Vec::new();
        grouped_parts.push(parts.get(0).unwrap());
        grouped_parts.push(parts.get(1).unwrap());
        grouped_parts.push(if cardinality_string.is_empty() {
            &cardinality_string
        } else {
            &spaced_cardinality_string
        });
        grouped_parts.push(&attributes_string);

        // adds the default values ​​for the corresponding types
        match grouped_parts.get(0).unwrap() {
            &"Boolean" => grouped_parts.insert(4, " true"),
            &"String" => grouped_parts.insert(4, " ''"),
            &"Integer" => grouped_parts.insert(4, " 0"),
            &"Real" => grouped_parts.insert(4, " 0.0"),
            _ => info!("unknown type"),
        };

        // the result replaces the current line.
        // here for no attributes
        let mut result: String = format!(
            "{}{} {{{}{}}}",
            grouped_parts.get(1).unwrap(),
            grouped_parts.get(2).unwrap(),
            grouped_parts.get(0).unwrap(),
            grouped_parts.get(4).unwrap()
        )
        .to_string();

        //here for attributes to append the current Type
        if !grouped_parts.get(3).unwrap().is_empty() {
            let attributes = grouped_parts.get(3).unwrap().to_string();
            let attribute_without_bracket = &attributes[0..attributes.len() - 1];
            let new_attributes = format!(
                "{}, {}{}}}",
                attribute_without_bracket,
                grouped_parts.get(0).unwrap(),
                grouped_parts.get(4).unwrap()
            );

            result = format!(
                "{}{} {}",
                grouped_parts.get(1).unwrap(),
                grouped_parts.get(2).unwrap(),
                new_attributes,
            )
            .to_string();
        }
        ///////////////////// constraint edit
        info!("source: {:#?}", source);

        // text of the complete line
        let mut constraints = source.slice(end_byte..source.len_chars()).as_str().unwrap();
        info!("constraints: {:#?}", constraints);

        let mut x = vec![TextEdit {
            range: new_range,
            new_text: result.clone(),
        }];

        let allowed_prefix_suffix = vec![" ", ">", "<", "=", "(", ")"];
        // Find the end position at the end of the respective line and create the new range
        while end_byte + grouped_parts.get(1).unwrap().len() + 1 < source.len_chars() {
            let part = source
                .slice(end_byte..end_byte + grouped_parts.get(1).unwrap().len())
                .as_str()
                .unwrap();

            if part.contains(grouped_parts.get(1).unwrap().to_owned())
                && allowed_prefix_suffix
                    .contains(&source.slice(end_byte - 1..end_byte).as_str().unwrap())
                && allowed_prefix_suffix.contains(
                    &source
                        .slice(
                            end_byte + grouped_parts.get(1).unwrap().len()
                                ..grouped_parts.get(1).unwrap().len() + 1,
                        )
                        .as_str()
                        .unwrap(),
                )
            {
                let constraint_range: Range = Range {
                    start: (byte_to_line_col(end_byte, &source)),
                    end: (byte_to_line_col(
                        end_byte + grouped_parts.get(1).unwrap().len(),
                        &source,
                    )),
                };
                let res = format!("{}.{}", grouped_parts[1], grouped_parts[0]);
                x.push(TextEdit {
                    range: constraint_range,
                    new_text: res,
                });
            }
            end_byte += 1;
        }

        // assemble the corresponding code_action as a solution
        let code_action_add_type_as_attribute = CodeAction {
            title: format!(
                "convert {:?} to attribute",
                grouped_parts.get(0).unwrap().to_string()
            ),
            kind: Some(CodeActionKind::QUICKFIX),
            edit: Some(WorkspaceEdit {
                changes: Some(HashMap::<Url, Vec<TextEdit>>::from([(
                    params.text_document.uri.clone(),
                    x,
                )])),
                document_changes: None,
                change_annotations: None,
            }),
            is_preferred: Some(true),
            diagnostics: Some(vec![diagnostic.clone()]),
            ..Default::default()
        };

        // result set that is returned
        return Ok(Some(vec![CodeActionOrCommand::CodeAction(
            code_action_add_type_as_attribute,
        )]));
    } else {
        return Ok(None);
    }
}
