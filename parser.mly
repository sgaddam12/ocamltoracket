%{
   
%}

%token <string> TokId
%token <string> TokCon
%token <string> TokString
%token <string> TokChar
%token <string> TokInt
%token <string> TokFloat
%token TokLParen
%token TokRParen
%token TokLBrace
%token TokRBrace
%token TokLBrack
%token TokRBrack
%token TokLBrackPipe
%token TokRBrackPipe
%token TokAnd
%token TokAs
%token TokBegin
%token TokElse
%token TokEnd
%token TokException
%token TokFalse
%token TokFun
%token TokFunction
%token TokIf
%token TokIn
%token TokLet
%token TokMatch
%token TokModule
%token TokMutable
%token TokOf
%token TokOpen
%token TokOr
%token TokRec
%token TokThen
%token TokTrue
%token TokTry
%token TokType
%token TokWhen
%token TokWith
%token TokLAnd
%token TokLOr
%token TokTick
%token TokStar
%token TokPlus
%token TokPlusDot
%token TokMinus
%token TokMinusDot
%token TokArrow
%token TokBackArrow
%token TokBang
%token TokDot
%token TokDotLBrack
%token TokDotLParen
%token TokDotDot
%token TokColon
%token TokColonEq
%token TokComma
%token TokSemi
%token TokSemiSemi
%token TokEq
%token TokNe
%token TokLt
%token TokGt
%token TokLe
%token TokGe
%token TokUnderscore
%token TokPipe
%token TokCons
%token <string> TokInfixOp0
%token <string> TokInfixOp1
%token <string> TokInfixOp2
%token <string> TokInfixOp3
%token <string> TokInfixOp4
%token TokEOF
%type <Ast.expr list> main
%%

%nonassoc TokIn
%nonassoc below_SEMI
%nonassoc TokSemi
%nonassoc TokLet
%nonassoc TokFunction TokWith
%nonassoc TokAnd
%nonassoc TokThen
%nonassoc TokElse
%nonassoc TokBackArrow
%nonassoc TokColonEq
%nonassoc TokAs
%left     TokPipe
%nonassoc below_COMMA
%left     TokComma
%right    TokArrow
%right    TokLOr TokOr
%right    TokLAnd
%nonassoc below_INFIX
%left  TokInfixOp0 TokEq
%right TokInfixOp1
%nonassoc below_LBRACKETAT
%right TokCons
%left  TokInfixOp2 TokPlus TokPlusDot TokMinus TokMinusDot
%left  TokInfixOp3 TokStar
%right TokInfixOp4
%nonassoc unary_minus
%nonassoc constr
%nonassoc constr_app
%nonassoc below_SHARP
%nonassoc below_DOT
%nonassoc TokDot
%nonassoc TokBang TokBegin TokChar TokCon TokFalse TokFloat TokInt TokLBrace TokLBrack TokId TokLParen TokString TokTrue

main:
| Structure                         { $1 }
;
Structure:
| GetPosition SeqExpr GetPosition DeclList { locDecl $1 $3 (fun s -> DEvl s $2) :: $4 }
| DeclList { $1 }
;
DeclList:
| { }              		   { [] }
| TokSemiSemi Structure    { $2 }
| Decl DeclList            { $1 :: $2 }
;
Decl:
| GetPosition TokLetRecFlag LetBindings GetPosition
  { locDecl $1 $5 (fun s -> DFun s $3 (reverse $4)) }
| GetPosition TokType TypeDecls GetPosition
  { locDecl $1 $4 (fun s -> DTyp s (reverse $3)) }
| GetPosition TokException DataDecl GetPosition
  { locDecl $1 $4 (fun s -> DExn s $3) }
;
LetBindings:
| LetBinding                    { [$1] }
| LetBindings TokAnd LetBinding  { $3 :: $1 }
;
LetBinding:
| ValIdent FunBinding   { (VarPat (getSrcSpanMaybe $1) (getVal $1), $2) }
| Pattern TokEqual SeqExpr   { ($1, $3) }
;
FunBinding:
| TokEqual SeqExpr        { $2 }
| TypeConstraint TokEqual SeqExpr { $3 }
| SimplePattern FunBinding { Lam (mergeLocated $1 $2) $1 $2 Nothing }
;
TypeConstraint:
| TokSemi Type { $2 }
;
TypeDecls:
| TypeDecl                  { [$1] }
| TypeDecls TokAnd TypeDecl  { $3 :: $1 }
;
TypeDecl:
| MaybeTyVars ident TokEqual TypeRhs  { TypeDecl (getId $2) $1 $4 }
;
MaybeTyVars:
| {}                 		  { [] }
| TyVar                       { [$1] }
| TokLParen TyVarList TokRParen      { reverse $2 }
;
TyVarList:
| TyVar                       { [$1] }
| TyVarList TokComma TyVar         { $3 :: $1 }
;
TyVar:
| ''' ident                  { (getId $2) }
;
TypeRhs:
| Type              { Alias $1 }
| TokRBrace LabelDecls MaybeSemi TokLBrace { TRec (reverse $2) }
| DataDecls         { Alg (reverse $1) }
| TokPipe DataDecls     { Alg (reverse $2) }

LabelDecls:
| LabelDecl                     { [$1] }
| LabelDecls TokSemi LabelDecl      { $3 :: $1 }
;
LabelDecl:
| MutFlag Label TokSemi Type              { ($2, $1, $4) }
;
DataDecls:
| DataDecl                    { [$1] }
| DataDecls TokPipe DataDecl      { $3 : $1 }
;
DataDecl:
| TokCon DataArgs              { DataDecl (getCon $1) $2 (error "parseDataDecl") }

DataArgs:
| {}		                 { [] }
| TokOf TypeList               { (reverse $2) }
;
(*Patterns*)

Pattern:
| SimplePattern         { $1 }
| Pattern TokAs ValIdent { AsPat (mergeLocated $1 $3) $1 (getVal $3) }
| PatternCommaList %prec below_COMMA     { TuplePat (mergeLocated (last $1) (head $1)) (reverse $1) }
| TokCon Pattern      %prec constr_app      { ConPat (mergeLocated $1 $2) (getCon $1) (Just $2) }
| Pattern TokCons Pattern                   { ConsPat (mergeLocated $1 $3) $1 $3 }
| Pattern TokPipe Pattern                    { OrPat (mergeLocated $1 $3) $1 $3 }
;
SimplePattern:
| ValIdent  %prec below_INFIX  { VarPat (getSrcSpanMaybe $1) (getVal $1) }
| SimplePatternNotIdent        { $1 }
;
SimplePatternNotIdent:
| TokUnderscore                     { WildPat (getSrcSpanMaybe $1) }
| SignedLiteral                     { LitPat (getSrcSpanMaybe $1) (getVal $1) }
| SignedLiteral TokDotDot SignedLiteral  { IntervalPat (mergeLocated $1 $3) (getVal $1) (getVal $3) }
| TokLBrack PatternSemiList TokRBrack           { ListPat (mergeLocated $1 $3) (reverse $2) }
| TokLParen Pattern TokRParen                   { $2 }
| TokLParen Pattern TokCon Type TokRParen          { ConstraintPat (mergeLocated $1 $5) $2 $4 }
| ConLongIdent                      { ConPat (getSrcSpanMaybe $1) (getVal $1) Nothing }
;
PatternCommaList:
| PatternCommaList TokComma Pattern  { $3 :: $1 }
| Pattern TokComma Pattern           { [$3, $1] }
;
PatternSemiList:
| PatternSemiList TokSemi Pattern  { $3 :: $1 }
| Pattern                      { [$1] }
;
(*Expressions*)

SeqExpr:
| Expr     %prec below_SEMI  { $1 }
| Expr TokColon                   { $1 }
| Expr TokColon SeqExpr           { Seq (mergeLocated $1 $3) $1 $3 }
;
Expr:
| SimpleExpr      %prec below_SHARP         { $1 }
| SimpleExpr SimpleExprList                 { mkApps (mergeLocated $1 (head $2)) $1 (reverse $2) }
| ConLongIdent SimpleExpr %prec below_SHARP { mkConApp (mergeLocated $1 $2) (getVal $1) [$2] }
| TokLet RecFlag LetBindings TokIn SeqExpr    { Let (mergeLocated $1 $5) $2 (reverse $3) $5 }
| TokFunction MaybePipe AltList              { mkFunction (mergeLocated $1 (thd3 (head $3))) (reverse $3) }
| TokFun SimplePattern FunDef                { Lam (mergeLocated $1 $3) $2 $3 Nothing }
| TokMatch SeqExpr TokWith MaybePipe AltList  { Case (mergeLocated $1 (thd3 (head $5))) $2 (reverse $5) }
| TokTry SeqExpr TokWith MaybePipe AltList    { Try (mergeLocated $1 (thd3 (head $5))) $2 (reverse $5) }
| ExprCommaList   %prec below_COMMA         { Tuple (mergeLocated (last $1) (head $1)) (reverse $1) }
| TokIf SeqExpr TokThen Expr TokElse Expr      { Ite (mergeLocated $1 $6) $2 $4 $6 }
| TokIf SeqExpr TokThen Expr                  { Ite (mergeLocated $1 $4) $2 $4 (Var (mergeLocated $1 $4) "()") }
| Expr TokCons Expr                            { mkConApp (mergeLocated $1 $3) "::" [$1, $3] }
| TokLParen TokCons TokRParen TokLParen Expr TokComma Expr TokRParen        { mkConApp (mergeLocated $1 $8) "::" [$5, $7] }
| SimpleExpr TokDot LongIdent TokBackArrow Expr        { SetField (mergeLocated $1 $5) $1 (getVal $3) $5 }
(*-- NOTE: imperative features disabled
-- | SimpleExpr '.' '(' SeqExpr ')' "<-" Expr  { mkApps (Var "Array.set") [$1, $4, $7] }
-- | SimpleExpr '.' '[' SeqExpr ']' "<-" Expr  { mkApps (Var "String.set") [$1, $4, $7] }*)
| Expr TokColonEq Expr                            { mkInfix (mergeLocated $1 $3) $1 (Var (getSrcSpanMaybe $2) ":=") $3 }
| Expr TokLAnd Expr                            { mkInfix (mergeLocated $1 $3) $1 (Var (getSrcSpanMaybe $2) "&&") $3 }
| Expr TokLOr Expr                            { mkInfix (mergeLocated $1 $3) $1 (Var (getSrcSpanMaybe $2) "||") $3 }
| Expr TokOr Expr                            { mkInfix (mergeLocated $1 $3) $1 (Var (getSrcSpanMaybe $2) "||") $3 }
| Expr TokInfixOp0 Expr                          { mkInfix (mergeLocated $1 $3) $1 (Var (getSrcSpanMaybe $2) (getInfix0 $2)) $3 }
| Expr TokEq    Expr                          { mkInfix (mergeLocated $1 $3) $1 (Var (getSrcSpanMaybe $2) "=") $3 }
| Expr TokInfixOp1 Expr                          { mkInfix (mergeLocated $1 $3) $1 (Var (getSrcSpanMaybe $2) (getInfix1 $2)) $3 }
| Expr TokPlus    Expr                          { mkInfix (mergeLocated $1 $3) $1 (Var (getSrcSpanMaybe $2) "+") $3 }
| Expr TokPlusDot   Expr                          { mkInfix (mergeLocated $1 $3) $1 (Var (getSrcSpanMaybe $2) "+.") $3 }
| Expr TokMinus    Expr                          { mkInfix (mergeLocated $1 $3) $1 (Var (getSrcSpanMaybe $2) "-") $3 }
| Expr TokMinusDot   Expr                          { mkInfix (mergeLocated $1 $3) $1 (Var (getSrcSpanMaybe $2) "-.") $3 }
| Expr TokInfixOp2 Expr                          { mkInfix (mergeLocated $1 $3) $1 (Var (getSrcSpanMaybe $2) (getInfix2 $2)) $3 }
| Expr TokInfixOp3 Expr                          { mkInfix (mergeLocated $1 $3) $1 (Var (getSrcSpanMaybe $2) (getInfix3 $2)) $3 }
| Expr TokStar    Expr                          { mkInfix (mergeLocated $1 $3) $1 (Var (getSrcSpanMaybe $2) "*") $3 }
| Expr TokInfixOp4 Expr                          { mkInfix (mergeLocated $1 $3) $1 (Var (getSrcSpanMaybe $2) (getInfix4 $2)) $3 }
| Subtractive Expr %prec unary_minus        { mkUMinus (mergeLocated $1 $2) (getVal $1) $2 }
;
SimpleExpr:
| ValLongIdent          { Var (getSrcSpanMaybe $1) (getVal $1) }
| ConLongIdent %prec constr  { mkConApp (getSrcSpanMaybe $1) (getVal $1) [] }
| Value                 { (getVal $1) }
| SimpleExpr TokDot TokLBrack SeqExpr TokRBrack     { mkApps (mergeLocated $1 $5) (Var (mergeLocated $1 $5) "String.get") [$1, $4] }
| SimpleExpr TokDot TokLParen SeqExpr TokRParen     { mkApps (mergeLocated $1 $5) (Var (mergeLocated $1 $5) "Array.get")  [$1, $4] }
| SimpleExpr TokDot LongIdent        { Field (mergeLocated $1 $3) $1 (getVal $3) }
| TokBang SimpleExpr        { mkApps (mergeLocated $1 $2) (Var (getSrcSpanMaybe $1) "!") [$2] }
| TokLParen SeqExpr TokRParen       { $2 }
| TokLBrackPipe ExprSemiList MaybeSemi TokRBrackPipe { Array (mergeLocated $1 $4) (reverse $2) Nothing }
| TokLBrace RecordExpr TokRBrace    { Record (mergeLocated $1 $3) $2 Nothing }
| TokBegin SeqExpr TokEnd { $2 }
| TokBegin TokEnd        { Var (mergeLocated $1 $2) "()" }
| TokLBrack ExprSemiList MaybeSemi TokRBrack  { List (mergeLocated $1 $4) (reverse $2) Nothing }
;
SimpleExprList:
| SimpleExpr                  { [$1] }
| SimpleExprList SimpleExpr   { $2 :: $1 }
;
RecordExpr:
: LabelExprList               { $1 }
;
LabelExprList:
| LabelExpr                     { [$1] }
| LabelExpr TokColon LabelExprList   { $1 :: $3 }
| LabelExpr TokColon                 { [$1] }
;
LabelExpr:
| LongIdent TokEq Expr            { (getVal $1, $3) }
;
ExprCommaList:
| ExprCommaList TokComma Expr   { $3 :: $1 }
| Expr TokComma Expr            { [$3, $1] }
;
ExprSemiList:
| Expr                    { [$1] }
| ExprSemiList TokComma Expr   { $3 :: $1 }
;
AltList:
| Alt                   { [$1] }
| AltList TokPipe Alt       { $3 :: $1 }
;
Alt:
| Pattern TokArrow SeqExpr                 { ($1, Nothing, $3) }
| Pattern TokWhen SeqExpr TokArrow SeqExpr  { ($1, Just $3, $5) }
;
FunDef:
| TokArrow SeqExpr          { $2 }
| SimplePattern FunDef  { Lam (mergeLocated $1 $2) $1 $2 Nothing }
;
Value:
| TokString    { L (getSrcSpanMaybe $1) (VS (getSrcSpanMaybe $1) (read (getString $1))) }
| TokChar     { L (getSrcSpanMaybe $1) (VC (getSrcSpanMaybe $1) (read (getChar $1))) }
| TokInt       { L (getSrcSpanMaybe $1) (VI (getSrcSpanMaybe $1) (read (getInt $1))) }
| TokFloat     { L (getSrcSpanMaybe $1) (VD (getSrcSpanMaybe $1) (read (getFloat $1))) }
| TokTrue    { L (getSrcSpanMaybe $1) (VB (getSrcSpanMaybe $1) True) }
| TokFalse   { L (getSrcSpanMaybe $1) (VB (getSrcSpanMaybe $1) False) }
;
Literal:
| TokString    { L (getSrcSpanMaybe $1) (LS (read (getString $1))) }
| TokChar     { L (getSrcSpanMaybe $1) (LC (read (getChar $1))) }
| TokInt       { L (getSrcSpanMaybe $1) (LI (read (getInt $1))) }
| TokFloat     { L (getSrcSpanMaybe $1) (LD (read (getFloat $1))) }
| TokTrue   { L (getSrcSpanMaybe $1) (LB True) }
| TokFalse   { L (getSrcSpanMaybe $1) (LB False) }
;
SignedLiteral:
| Literal   { $1 }
| TokMinus TokInt   { L (mergeLocated $1 $2) (LI (negate (read (getInt $2)))) }
| TokMinus TokFloat { L (mergeLocated $1 $2) (LD (negate (read (getFloat $2)))) }
| TokPlus TokInt  { L (mergeLocated $1 $2) (LI (read (getInt $2))) }
| TokPlus TokFloat { L (mergeLocated $1 $2) (LD (read (getFloat $2))) }
;
Subtractive:
| TokMinus          { L (getSrcSpanMaybe $1) "-" }
| TokMinusDot         { L (getSrcSpanMaybe $1) "-." }
;
(*Types*)

Type:
| SimpleTypeOrTuple  { $1 }
| Type TokArrow Type     { $1 :-> $3 }
;
SimpleTypeOrTuple:
| SimpleType   %prec below_LBRACKETAT   { $1 }
| SimpleType TokStar TypeList               { TTup ($1 :: reverse $3) }
;
TypeList:
| SimpleType   %prec below_LBRACKETAT   { [$1] }
| TypeList TokStar SimpleType               { $3 :: $1 }
;
SimpleType:
| SimpleType2           %prec below_SHARP { $1 }
| TokLParen TypeCommaList TokRParen %prec below_SHARP { case $2 of { [a] -> a } }

SimpleType2:
| ''' ident                       { TVar (getId $2) }
| LongIdent                        { tCon (getVal $1) }
| TokLParen TokRParen                         { tCon tUNIT }
| SimpleType2 LongIdent            { mkTApps (getVal $2) [$1] }
| TokLParen TypeCommaList TokRParen LongIdent  { mkTApps (getVal $4) (reverse $2) }
;
TypeCommaList:
| Type                         { [$1] }
| TypeCommaList TokComma Type       { $3 :: $1 }
;
(*Misc*)

Label:
| TokId              { getId $1 }
;
ValIdent:
| TokId              { L (getSrcSpanMaybe $1) (getId $1) }
| TokLParen Operator TokRParen   { L (mergeLocated $1 $3) (getVal $2) }
;
ValLongIdent:
| ValIdent                  { $1 }
| ModLongIdent TokDot ValIdent { L (mergeLocated $1 $3) (getVal $1 ++ "." ++ getVal $3) }
;
LongIdent:
| TokId                  { L (getSrcSpanMaybe $1) (getId $1) }
| ModLongIdent '.' TokId { L (mergeLocated $1 $3) (getVal $1 ++ "." ++ getId $3) }
;
ConLongIdent:
| ModLongIdent %prec below_DOT { $1 }
| TokLBrack TokRBrack                      { L (mergeLocated $1 $2) "[]" }
| TokLParen TokRParen                      { L (mergeLocated $1 $2) "()" }
;
ModLongIdent:
| TokCon                    { L (getSrcSpanMaybe $1) (getCon $1) }
| ModLongIdent TokDot TokCon   { L (mergeLocated $1 $3) (getVal $1 ++ "." ++ getCon $3) }
;
Operator:
| TokInfixOp0             { L (getSrcSpanMaybe $1) (getInfix0 $1) }
| TokInfixOp1             { L (getSrcSpanMaybe $1) (getInfix1 $1) }
| TokInfixOp2             { L (getSrcSpanMaybe $1) (getInfix2 $1) }
| TokInfixOp3             { L (getSrcSpanMaybe $1) (getInfix3 $1) }
| TokInfixOp4             { L (getSrcSpanMaybe $1) (getInfix4 $1) }
| TokBang                { L (getSrcSpanMaybe $1) "!" }
| TokColonEq               { L (getSrcSpanMaybe $1) ":=" }
| TokPlus                { L (getSrcSpanMaybe $1) "+" }
| TokPlusDot               { L (getSrcSpanMaybe $1) "+." }
| TokMinus                { L (getSrcSpanMaybe $1) "-" }
| TokMinusDot               { L (getSrcSpanMaybe $1) "-." }
| TokStar                { L (getSrcSpanMaybe $1) "*" }
| TokEq                { L (getSrcSpanMaybe $1) "=" }
;

RecFlag:
| {} 		{ NonRec }
| TokRec       { Rec }
;
MutFlag:
| {} 		{ NonMut }
| TokMutable   { Mut }
;
MaybePipe:
| {}		      { () }
| TokPipe              { () }
;
MaybeSemi:
| {}      { () }
| TokSemi              { () }
;
GetPosition
| {}      {% getPosition }
;
