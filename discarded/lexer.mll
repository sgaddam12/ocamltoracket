{
	open Parser
	exception Eof
}
let digit = ['0'-'9']
let alpha = ['a'-'z''A'-'Z']
let lower = ['a'-'z']
let upper = ['A'-'Z']
let symbol = ['!' '$' '%' '&' '*' '+' '-' '.' '/' ':' '<' '=' '>' '?' '@' '^' '|' '~']
let whitechar = [' ''t''n''r''f''v']
let special = ['(' ')' ',' ';' '[' ']' '`' '{' '}']
let graphic = [lower upper symbol digit special '_' ':' '"' ''']

let decimal  = digit+

let cntrl   = [upper '@' '[' '\\' ']' '^' '_']
(*let ascii   = '^' | cntrl | "NUL" | SOH | STX | ETX | EOT | ENQ | ACK
         | BEL | BS | HT | LF | VT | FF | CR | SO | SI | DLE
         | DC1 | DC2 | DC3 | DC4 | NAK | SYN | ETB | CAN | EM
         | SUB | ESC | FS | GS | RS | US | SP | DEL*)
let charesc = ['a' 'b' 'f' 'n' 'r' 't' 'v' '\\' '"' ''' '&']
let escape  = '\\'charesc | '\\'cntrl | '\\''^' | '\\'decimal
let gap     = whitechar+
let string  = graphic '#' '\\' '"' '\' | " " | escape | gap

rule token = parse
| white+ { token lexbuf }
| digit+'.'digit* as tkn { TokFloat(tkn) }
| digit+ as tkn { TokInt(tkn) }
| '*'')'		{ TokLNestedComment }
| '*'')'		{ TokRNestedComment }	
| '('			{ TokLParen }
| ')'			{ TokRParen }
| '{'			{ TokLBrace }
| '}'			{ TokRBrace }
| '['			{ TokLBrack }
| ']'			{ TokRBrack }
| '[''|'		{ TokLBrackPipe }
| '|'']'		{ TokRBrackPipe }
| '-''>'		{ TokArrow }
| '<''-'		{ TokBackArrow }
| ':'			{ TokColon }
| ':''='		{ TokColonEq }
| ':'':'		{ TokCons }
| ';'			{ TokSemi }
| ';'';'		{ TokSemiSemi }

| '='			{ TokEq }
| '*'			{ TokStar }
| '''			{ TokTick }
| '+'           { TokPlus }
| '+''.'		{ TokPlusDot }
| '-'			{ TokMinus }
| '-''.'		{ TokMinusDot }
| '!'			{ TokBang }

| '_'			{ TokUnderscore }
| ','			{ TokComma }

| '&''&'		{ TokLAnd }
| '|''|'		{ TokLOr }
| '|'			{ TokPipe }
| '.'			{ TokDot }
| '.''.'		{ TokDotDot }

| "and"         { TokAnd }
| "as"          { TokAs }
| "begin"       { TokBegin }
| "else"        { TokElse }
| "end"         { TokEnd }
| "exception"   { TokException }
| "false"       { TokFalse }
| "fun"         { TokFun }
| "function"    { TokFunction }
| "if"          { TokIf }
| "in"          { TokIn }
| "let"         { TokLet }
| "match"       { TokMatch }
| "module"      { TokModule }
| "mutable"     { TokMutable }
| "of"          { TokOf }
| "open"        { TokOpen }
| "or"          { TokOr }
| "rec"         { TokRec }
| "then"        { TokThen }
| "true"        { TokTrue }
| "try"         { TokTry }
| "type"        { TokType }
| "when"        { TokWhen }
| "with"        { TokWith }

| ['=' '<' '>' '|' '&' '$'] as tkn { TokInfixOp0(tkn) }
| '!''='                    as tkn { TokInfixOp0(tkn) }
| ['@' '^'] 				as tkn { TokInfixOp1(tkn) }
| ['+' '-'] 				as tkn { TokInfixOp2(tkn) }
| ['*' '/' '%']          	as tkn { TokInfixOp3(tkn) }
| "mod"                     as tkn { TokInfixOp3(tkn) }
| '*''*'                	as tkn { TokInfixOp4(tkn) }

| lower | ('_'[alpha digit '_' ''']*) as tkn { TokId(tkn) }
| upper | ('_'[alpha digit '_' ''']*) as tkn { TokCon(tkn) }

| '"'string*'"'           			as tkn { TokString(tkn) }
| ''' printable '#' ['''] ''' 		as tkn { TokChar(tkn) }

| _ as lxm { Printf.printf "Illegal character %c" lxm; failwith "Bad input" }