#lang racket
(require parser-tools/lex
         (prefix-in re- parser-tools/lex-sre)
         parser-tools/yacc)
(provide (all-defined-out))

(define-tokens a (CHR GROUP))
(define-empty-tokens b (ALT STAR PLUS LP RP))

(define-lex-abbrevs
  (char (re-or (char-range "A" "z") (char-range "0" "9") ",")))

(define-lex-trans group
  (syntax-rules ()
    ((_ char) (re-+ char))))

(define regex-lexer
  (lexer
   ("|" (token-ALT))
   ("+" (token-PLUS))
   ("*" (token-STAR))
   ("(" (token-LP))
   (")" (token-RP))
   (char (token-CHR lexeme))
   ((re-: "[" (re-+ char) "]") (token-GROUP lexeme))
   (whitespace (simple-math-lexer input-port))
   ((eof) (token-EOF))))
