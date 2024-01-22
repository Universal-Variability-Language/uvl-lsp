use std::collections::HashMap;
use std::sync::Arc;

use crate::core::*;
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

/// Checks all possible types of quickfixes for the wrong/missing language_level
pub fn wrong_language_level(
    params: CodeActionParams,
    diagnostic: Diagnostic,
    snapshot: std::result::Result<Option<(Draft, Arc<RootGraph>)>, tower_lsp::jsonrpc::Error>,
) -> Result<Option<CodeActionResponse>> {
    let mut result: Vec<CodeActionOrCommand> = vec![];
    match add_language_level(params.clone(), diagnostic.clone(), snapshot.clone()) {
        Ok(Some(v)) => result.append(v.to_owned().as_mut()),
        _ => (),
    }
    match drop_feature(params.clone(), diagnostic.clone(), snapshot.clone()) {
        Ok(Some(v)) => result.append(v.to_owned().as_mut()),
        _ => (),
    }
    match add_type_as_attribute(params.clone(), diagnostic.clone(), snapshot.clone()) {
        Ok(Some(v)) => result.append(v.to_owned().as_mut()),
        _ => (),
    }

    return Ok(Some(result));
}

pub fn wrong_language_level_constraint(
    params: CodeActionParams,
    diagnostic: Diagnostic,
    snapshot: std::result::Result<Option<(Draft, Arc<RootGraph>)>, tower_lsp::jsonrpc::Error>,
) -> Result<Option<CodeActionResponse>> {
    let mut result: Vec<CodeActionOrCommand> = vec![];
    match add_language_level(params.clone(), diagnostic.clone(), snapshot.clone()) {
        Ok(Some(v)) => result.append(v.to_owned().as_mut()),
        _ => (),
    }
    match drop_constraint(params.clone(), diagnostic.clone(), snapshot.clone()) {
        Ok(Some(v)) => result.append(v.to_owned().as_mut()),
        _ => (),
    }
    match convert_sum_constraint(params.clone(), diagnostic.clone(), snapshot.clone()) {
        Ok(Some(v)) => result.append(v.to_owned().as_mut()),
        _ => (),
    }
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

        while end_byte < source.len_chars()
            && source.slice(end_byte - 1..end_byte).as_str().unwrap() != "\r"
        {
            end_byte += 1;
        }

        let new_range: Range = Range {
            start: (diagnostic.range.start),
            end: (byte_to_line_col(end_byte, &source)),
        };

        let name = source
            .slice(start_byte..end_byte)
            .as_str()
            .unwrap()
            .replace("\n", "")
            .replace("\r", "");
        let code_action_drop = CodeAction {
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
        return Ok(Some(vec![CodeActionOrCommand::CodeAction(
            code_action_drop,
        )]));
    } else {
        return Ok(None);
    }
}
/// Adds the quickfix to roll out sum() functions
pub fn convert_sum_constraint(
    params: CodeActionParams,
    diagnostic: Diagnostic,
    snapshot: std::result::Result<Option<(Draft, Arc<RootGraph>)>, tower_lsp::jsonrpc::Error>,
) -> Result<Option<CodeActionResponse>> {
    if let Ok(Some((Draft::UVL { source, .. }, ..))) = snapshot {
        let start_byte = byte_offset(&diagnostic.range.start, &source);
        let end_byte = byte_offset(&diagnostic.range.end, &source);
        let constraint = source
            .slice(start_byte..end_byte)
            .as_str()
            .unwrap()
            .replace("\n", "")
            .replace("\r", "")
            .to_string();
        //quickfix is only neccessary if it is a sum() function
        if constraint.contains("sum(") {
            // find the attribute name
            let constraint_parts: Vec<&str> = constraint.split_whitespace().collect();
            let start_bytes = constraint_parts[0].find("(").unwrap_or(0) + 1;
            let end_bytes = constraint_parts[0]
                .find(")")
                .unwrap_or(constraint_parts[0].len());
            let attribute = &constraint_parts[0][start_bytes..end_bytes];

            // find all occurances of the attribute
            let mut res = String::new();
            let mut attribute_range_start_byte = byte_offset(&Position::new(0, 0), &source);
            let mut attribute_range_end_byte = attribute_range_start_byte;
            let mut is_not_constraints = true;
            let types = ["Integer", "String", "Real", "Boolean"];

            //check for attribute line by line
            while attribute_range_end_byte < source.len_chars() && is_not_constraints {
                attribute_range_end_byte += 1;
                attribute_range_start_byte = attribute_range_end_byte;
                while source
                    .slice(attribute_range_end_byte - 1..attribute_range_end_byte)
                    .as_str()
                    .unwrap()
                    != "\r"
                    && attribute_range_end_byte < source.len_chars()
                {
                    attribute_range_end_byte += 1;
                }

                let source_string = source
                    .slice(attribute_range_start_byte..attribute_range_end_byte)
                    .as_str()
                    .unwrap();
                let source_parts: Vec<&str> = source_string.split_whitespace().collect();
                //stop checking for attribute if the constraint section is reached
                for element in source_parts.iter() {
                    if element.contains("constraints") && source_parts.len() == 1 {
                        let is_constraint_key = source
                            .slice(attribute_range_start_byte..attribute_range_start_byte + 11)
                            .as_str()
                            .unwrap();
                        if is_constraint_key == "constraints" {
                            is_not_constraints = false;
                            break;
                        }
                    }
                    // append feature to sum if it contains the attribute
                    if element.contains(&attribute) {
                        if res.is_empty() {
                            //if feature has type the feature name is in index 1
                            if types.contains(source_parts.get(0).unwrap()) {
                                res.push_str(source_parts.get(1).unwrap());
                            } else {
                                res.push_str(source_parts.get(0).unwrap());
                            }
                            res.push_str(".");
                            res.push_str(attribute);
                        } else {
                            res.push_str(" + ");
                            if types.contains(source_parts.get(0).unwrap()) {
                                res.push_str(source_parts.get(1).unwrap());
                            } else {
                                res.push_str(source_parts.get(0).unwrap());
                            }
                            res.push_str(".");
                            res.push_str(attribute);
                        }
                    }
                }
            }
            res = format!("({})", res);
            let cons = format!("sum({})", attribute);
            let result = constraint.replacen(&cons, res.as_str(), 1);

            let code_action_add_type_as_attribute = CodeAction {
                title: format!("Roll out sum() function"),
                kind: Some(CodeActionKind::QUICKFIX),
                edit: Some(WorkspaceEdit {
                    changes: Some(HashMap::<Url, Vec<TextEdit>>::from([(
                        params.text_document.uri.clone(),
                        vec![TextEdit {
                            range: diagnostic.range,
                            new_text: result,
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
                code_action_add_type_as_attribute,
            )]));
        } else {
            return Ok(None);
        }
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

        let name = source
            .slice(start_byte..end_byte)
            .as_str()
            .unwrap()
            .replace("\n", "")
            .replace("\r", "");
        let parts: Vec<&str> = name.split_whitespace().collect();
        let code_action_drop = CodeAction {
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
        return Ok(Some(vec![CodeActionOrCommand::CodeAction(
            code_action_drop,
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

        while end_byte < source.len_chars()
            && source.slice(end_byte - 1..end_byte).as_str().unwrap() != "\r"
        {
            end_byte += 1;
        }

        let new_range: Range = Range {
            start: (diagnostic.range.start),
            end: (byte_to_line_col(end_byte, &source)),
        };

        let mut name = source
            .slice(start_byte..end_byte)
            .as_str()
            .unwrap()
            .replace("\n", "")
            .replace("\r", "");

        //split cardinality string and attribute string
        if name.contains("]{") {
            name = name.replace("]{", "] {");
        }

        let parts: Vec<&str> = name.split_whitespace().collect();

        //create one part for cardinality
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

        //create grouped parts
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
        match grouped_parts.get(0).unwrap() {
            &"Boolean" => grouped_parts.insert(4, " true"),
            &"String" => grouped_parts.insert(4, " ''"),
            &"Integer" => grouped_parts.insert(4, " 0"),
            &"Real" => grouped_parts.insert(4, " 0.0"),
            _ => info!("unknown type"),
        };

        //the result replaces the current line. here for no attributes
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

        let code_action_add_type_as_attribute = CodeAction {
            title: format!(
                "convert {:?} to attribute",
                grouped_parts.get(0).unwrap().to_string()
            ),
            kind: Some(CodeActionKind::QUICKFIX),
            edit: Some(WorkspaceEdit {
                changes: Some(HashMap::<Url, Vec<TextEdit>>::from([(
                    params.text_document.uri.clone(),
                    vec![TextEdit {
                        range: new_range,
                        new_text: result,
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
            code_action_add_type_as_attribute,
        )]));
    } else {
        return Ok(None);
    }
}
