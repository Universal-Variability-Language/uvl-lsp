
#include <algorithm>
#include <cassert>
#include <cstring>
#include <cwctype>
#include <memory>
#include <stdio.h>
#include <tree_sitter/parser.h>
#include <vector>

#include <iostream>
enum TokenType {
  INDENT,
  DEDENT,
  NEW_LINE,
  COMMENT,
  CLOSE_PARE, //)
  CLOSE_BRAK, //]
  CLOSE_CURL, //}
  TOKEN_TYPE_MAX_LEN,
};

bool is_error_revovery(const bool *valid_symbols) {
  bool val = true;
  for (int i = 0; i < TOKEN_TYPE_MAX_LEN; i++) {
    val &= valid_symbols[i];
  }
  return val;
}

struct Scanner {
  Scanner() { deserialize(0, 0); }
  unsigned serialize(char *buffer) {
    unsigned length = std::min((unsigned)indent_stack.size() - 1,
                               TREE_SITTER_SERIALIZATION_BUFFER_SIZE / 2u);
    uint16_t *src = indent_stack.data() + 1;
    std::copy(src, src + length, (uint16_t *)buffer);
    return length * 2;
  }
  void deserialize(const char *buffer, unsigned length) {
    indent_stack.clear();
    indent_stack.push_back(0);
    const unsigned cnt = length / 2;
    indent_stack.resize(cnt + 1);
    if (length > 0) {
      const uint16_t *src = (uint16_t *)buffer;

      std::copy(src, src + cnt, indent_stack.data() + 1);
    }
  }
  bool scan(TSLexer *lexer, const bool *valid_symbols) {
    bool inside_bracket = valid_symbols[CLOSE_PARE] ||
                          valid_symbols[CLOSE_CURL] ||
                          valid_symbols[CLOSE_BRAK];
    // std::cout<<"Error Recovery:
    // "<<is_error_revovery(valid_symbols)<<std::endl;
    bool found_end_of_line = 0;
    uint16_t next_indent = 0;
    int32_t first_comment_indent_lenght = -1;
    lexer->mark_end(lexer);
    auto skip = [&]() { lexer->advance(lexer, false); };
    bool scan_ident = 1, eof = 0;

    // std::cout<<"scanning:";
    while (scan_ident) {
      // std::cout<<(char)lexer->lookahead;
      switch (lexer->lookahead) {
      case 0:
        next_indent = 0;
        found_end_of_line = true;
        eof = 1;
        scan_ident = 0;
        break;
      case '\n':
        next_indent = 0;
        found_end_of_line = true;
        skip();
        break;
      case '\r':
        next_indent = 0;
        skip();
        break;
      case '\t':
        next_indent += 4;
        skip();
        break;
      case '\f':
        next_indent = 0;
        skip();
        break;
      case ' ':
        next_indent++;
        skip();
        break;
      case '/':
        skip();
        if (lexer->lookahead == '/') {
          skip();
          first_comment_indent_lenght = next_indent;
          while (lexer->lookahead && lexer->lookahead != '\n') {
            skip();
          }
          skip();
          next_indent = 0;
        } else {
          scan_ident = 0;
        }
        break;
      default:
        scan_ident = 0;
      }
    }
    /*
    std::cout<<"|"<<std::endl;
    std::cout<<"Stack: ";
    for(auto i:indent_stack){
        std::cout<<i<<" ";
    }
    std::cout<<std::endl;
    */
    if (found_end_of_line) {
      if (!indent_stack.empty()) {
        uint16_t cur_indent = indent_stack.back();
        // std::cout<<cur_indent<<next_indent<<std::endl;
        if (valid_symbols[INDENT] && next_indent > cur_indent) {
          indent_stack.push_back(next_indent);
          lexer->result_symbol = INDENT;
          // std::cout<<"indent"<<std::endl;
          return true;
        }
        if ((valid_symbols[DEDENT] ||
             (!valid_symbols[NEW_LINE] && !inside_bracket)) &&
            next_indent < cur_indent &&
            first_comment_indent_lenght < cur_indent) {

          indent_stack.pop_back();
          lexer->result_symbol = DEDENT;
          // std::cout<<"DEDENT"<<std::endl;
          return true;
        }
      }
      if (valid_symbols[NEW_LINE] && !is_error_revovery(valid_symbols)) {

        lexer->result_symbol = NEW_LINE;
        return true;
      }
    }
    return false;
  }
  std::vector<uint16_t> indent_stack;
};

extern "C" {

void *tree_sitter_uvl_external_scanner_create() { return new Scanner(); }

bool tree_sitter_uvl_external_scanner_scan(void *payload, TSLexer *lexer,
                                           const bool *valid_symbols) {
  Scanner *scanner = static_cast<Scanner *>(payload);
  return scanner->scan(lexer, valid_symbols);
}

unsigned tree_sitter_uvl_external_scanner_serialize(void *payload,
                                                    char *buffer) {
  Scanner *scanner = static_cast<Scanner *>(payload);
  return scanner->serialize(buffer);
}

void tree_sitter_uvl_external_scanner_deserialize(void *payload,
                                                  const char *buffer,
                                                  unsigned length) {
  Scanner *scanner = static_cast<Scanner *>(payload);
  scanner->deserialize(buffer, length);
}

void tree_sitter_uvl_external_scanner_destroy(void *payload) {
  Scanner *scanner = static_cast<Scanner *>(payload);
  delete scanner;
}
}
