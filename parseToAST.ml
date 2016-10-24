open Parse
open Lexing
open Location
open Parsetree
open Asttypes
open Longident

let read_sig filename =
	Location.input_name := filename ;
	let handle =
	try open_in filename
	with Sys_error msg -> prerr_endline msg; exit 1
	in
	let buf = Lexing.from_channel handle in
	Location.init buf filename ;
	let ast = Parse.implementation buf in
	close_in handle ;
	ast;;

let locError {loc_start = {pos_fname = fnamestart; pos_lnum = lnumstart; pos_bol = bolstart; pos_cnum = cnumstart;};
				loc_end = {pos_fname = fnameend; pos_lnum = lnumend; pos_bol = bolend; pos_cnum = cnumend;};
				loc_ghost = ghostbool;} =
				failwith ("Failed to account for: " ^ string_of_int lnumstart ^ ":" ^ string_of_int cnumstart ^ " to " ^ string_of_int lnumend ^ ":" ^ string_of_int cnumend ^ ".\n");;

let next_reg =
  let n = ref 0 in
  (fun () -> (let temp = !n in n:=!n+1; temp))
;;

let genFunctionVar () = 
	let x = next_reg () in
	"functionVar" ^ (string_of_int x)
;;

let rec patternDescMatcher patterndesc loc =
	match patterndesc with
	| Ppat_var {txt = s; loc = loc1;} -> " " ^ (varConverter s) ^ " "
	| Ppat_or (patt1, patt2) -> "(or " ^ (patternMatcher patt1 loc) ^ " " ^ (patternMatcher patt2 loc) ^ ") "
	| Ppat_constant const -> (constantMatcher const loc)
	| Ppat_any -> "_ "
	| Ppat_tuple explist -> "(list " ^ (List.fold_right (fun a b -> (patternMatcher a loc) ^ " " ^ b) explist "") ^ ")"
	| Ppat_construct ({txt = Lident "::"; loc = newloc;}, _) | Ppat_construct ({txt = Lident "[]"; loc = newloc;}, _) -> 
		"(list " ^ (listPatternMatcher patterndesc newloc) ^ ")"
	| Ppat_construct ({txt = Lident "()"; loc = newloc;}, None) -> "void"
	| Ppat_construct ({txt = Lident typ; loc = newloc;}, opt) -> "(" ^ typ ^ " " ^ (typeArgumentMatcher loc opt) ^ ")"
	| _ -> print_string "Pattern description matcher failed.\n"; locError loc
and varConverter s =
	Str.global_replace (Str.regexp "\'") "tick" s
and typeArgumentMatcher loc = function
	| Some {ppat_desc = pdesc; ppat_loc = loc1; ppat_attributes = ppatattr;} ->
		(match pdesc with 
		| Ppat_tuple patlist -> List.fold_left (fun str pat -> str ^ " " ^ (patternMatcher pat loc1)) "" patlist
		| _ -> " " ^ patternDescMatcher pdesc loc1)
		(*| _ -> print_string "unexpected patternDesc in typeArgumentMatcher"; locError loc)*)
	| None -> ""
and listPatternMatcher patterndesc newloc =
	match patterndesc with
	| Ppat_construct(_, Some {ppat_desc = pdesc1; ppat_loc = newloc1; ppat_attributes = ppatattr1;}) -> 
		(match pdesc1 with
		| Ppat_tuple (hd::{ppat_desc = pdesc2; ppat_loc = newloc2; ppat_attributes = ppatattr2;}::tl) -> 
			(match pdesc2 with
				| Ppat_construct ({txt = Lident "::"; loc = newloc;}, _) | Ppat_construct ({txt = Lident "[]"; loc = newloc;}, _) ->
					(patternMatcher hd newloc2) ^ " " ^ (listPatternMatcher pdesc2 newloc2)
				| _ -> (patternMatcher hd newloc2) ^ " " ^
						(patternMatcher {ppat_desc = pdesc2; ppat_loc = newloc2; ppat_attributes = ppatattr2;} newloc2) ^ "...")
		| _ -> print_string "There is an unexpected tuple error in listPatternMatcher.\n"; locError newloc)
	| Ppat_construct(_, None) -> ""
	| _ -> print_string "Incorrect expression description matcher used: listPatternMatcher.\n"; locError newloc
and patternMatcher pattern loc = 
	match pattern with
	| {ppat_desc = pdesc; ppat_loc = loc1; ppat_attributes = ppatattr;} ->
		patternDescMatcher pdesc loc1
and expressionDescMatcher expressiondesc loc =
	match expressiondesc with
	| Pexp_function ({pc_lhs = pclhs; pc_guard = pcguard; pc_rhs = pcrhs;}::[]) -> 
		expressionDescMatcher (Pexp_fun ("", None, pclhs, pcrhs)) loc;
	| Pexp_function _ -> 
		print_string "Pexp_function should not have reached here. 'function' matches are done in pexpfunMatcher.\n"; locError loc
	| Pexp_fun (arglabel, expressionopt, pattern, expression) -> 
		let (args, resultExpression) = pexpfunMatcher expressiondesc loc
		in "(match-lambda** [(" ^ args ^ ") " ^ resultExpression ^ "])"
	| Pexp_match (expression, caselist) -> (pexpmatchMatcher expressiondesc loc)
	| Pexp_ident {txt = t; loc = locid;} -> longidentMatcher t locid
	| Pexp_constant const -> constantMatcher const loc
	| Pexp_let (recflag, valuebindings, exp) -> letMatcher expressiondesc loc
	| Pexp_apply (exp1, explist) -> applyMatcher expressiondesc loc
	| Pexp_tuple explist -> tupleMatcher expressiondesc loc
	| Pexp_construct ({txt = Lident "::"; loc = newloc;}, _) ->  
		listMatcher expressiondesc newloc
	| Pexp_construct ({txt = Lident "[]"; loc = newloc;}, _) ->
		"(list)"
	| Pexp_ifthenelse (exp1, exp2, expopt) ->
		(match expopt with 
		| Some exp3 -> "(if " ^ (expressionMatcher exp1 loc) ^ " " ^ (expressionMatcher exp2 loc) ^ " " ^ (expressionMatcher exp3 loc) ^ ")"
		| None -> "(if " ^ (expressionMatcher exp1 loc) ^ " " ^ (expressionMatcher exp2 loc) ^ ")")
	| Pexp_sequence (exp1, exp2) -> "(begin " ^ (expressionMatcher exp1 loc) ^ " " ^ (expressionMatcher exp2 loc) ^ ")"
	| Pexp_construct ({txt = Lident "()"; loc = newloc;}, None) -> "void"
	| Pexp_construct ({txt = Lident "true"; loc = newloc;}, None) -> "true"
	| Pexp_construct ({txt = Lident "false"; loc = newloc;}, None) -> "false"
	| Pexp_assert exp -> let assertExp = {pexp_desc = (Pexp_ident {txt = Lident "assert"; loc = loc;}); pexp_loc = loc; pexp_attributes = [];} in
		expressionDescMatcher (Pexp_apply (assertExp, [("", exp)])) loc
	| Pexp_construct ({txt = Lident typ; loc = newloc;}, Some exp) -> let {pexp_desc = expdesc; pexp_loc = newloc; pexp_attributes = pexpattr;} = exp in
		"(" ^ typ ^ " " ^
		(match expdesc with
		| Pexp_tuple explist -> (List.fold_left (fun str exp -> str ^ " " ^ (expressionMatcher exp newloc)) "" explist)
		| _ -> expressionDescMatcher expdesc loc) ^ ")"
	| Pexp_construct ({txt = Lident typ; loc = newloc;}, None) -> "(" ^ typ ^ ")"
	| _ -> print_string "Expression description matcher failed.\n"; locError loc
and expressionMatcher expression loc  =
	match expression with
	| {pexp_desc = expdesc; pexp_loc = loc4; pexp_attributes = pexpattr;} ->
		expressionDescMatcher expdesc loc4 
and listMatcher expressiondesc loc = 
	match expressiondesc with
	| Pexp_construct(_, Some e) -> 
		let {pexp_desc = expdesc1; pexp_loc = newloc1; pexp_attributes = pexpattr1;} = e in
		(match expdesc1 with
		| Pexp_tuple (hd::{pexp_desc = expdesc2; pexp_loc = newloc2; pexp_attributes = pexpattr2;}::tl) -> 
			"(cons " ^ (expressionMatcher hd newloc2) ^ " " ^ (listMatcher expdesc2 newloc2) ^ ")"
		| _ -> print_string "Unexpected tuple error in listMatcher.\n"; locError loc)
	| Pexp_construct(_, None) -> "(list)"
	| _ -> expressionDescMatcher expressiondesc loc
and caseListMatcher caselist loc = 
	match caselist with
	| {pc_lhs = pclhs; pc_guard = pcguard; pc_rhs = pcrhs;}::casetl -> 
		let pcstring = 
		(match pcguard with
		| Some exp -> print_string "Haven't accounted for pcguard expressions.\n"; locError loc
		| None -> "") in
		"\n[ " ^ (patternMatcher pclhs loc) ^ pcstring ^ " " ^ (expressionMatcher pcrhs loc) ^ " ] "
		^ (caseListMatcher casetl loc)
	| [] -> ""
and pexpfunMatcher expressiondesc loc =
	match expressiondesc with
	| (Pexp_fun (arglabel, expressionopt, pattern, expression)) ->
		let stringopt = 
			(match expressionopt with
			| Some exp -> print_string "Haven't account for expression options under Pexp_fun.\n"; locError loc
			| None -> "") in
		let arg = arglabel ^ stringopt ^ (patternMatcher pattern loc) in
		let {pexp_desc = expdesc; pexp_loc = newloc; pexp_attributes = pexpattr;} = expression in
			(match expdesc with 
			| Pexp_fun (_, _, _, _) -> 
				let (args, resExp) = (pexpfunMatcher expdesc newloc) in (arg ^ args, resExp)
			| Pexp_function caselist -> let newvar = genFunctionVar () in 
				let matchExp = {pexp_desc = (Pexp_ident {txt = (Lident newvar); loc = loc;}); pexp_loc = loc; pexp_attributes = pexpattr;} in
				(newvar, expressionDescMatcher (Pexp_match (matchExp, caselist)) loc)
			| _ -> (arg, (expressionMatcher expression loc )))
	| _ -> print_string "Incorrect expression description matcher used: fun.\n"; locError loc
and pexpmatchMatcher expressiondesc loc =
	match expressiondesc with
	| (Pexp_match (expression, caselist)) ->
		" (match " ^ (expressionMatcher expression loc) ^ (caseListMatcher caselist loc) ^ ") ";
	| _ -> print_string "Incorrect expression description matcher used: match.\n"; locError loc
and longidentMatcher t loc =
	(match t with 
	| Lident s -> identConverter s
	| Ldot (newt, s) -> (longidentMatcher newt loc) ^ (identConverter s)
	| Lapply (newt1, newt2) -> (longidentMatcher newt1 loc) ^ (longidentMatcher newt2 loc))
and identConverter s = 
	(match s with
	| "&&" -> "and"
	| "||" -> "or"
	| "~-" -> "-"
	| "~+" -> "+"
	| _ -> Str.global_replace (Str.regexp "\'") "tick" s)
and constantMatcher const loc = 
	match const with
	| Const_int x -> " " ^ (string_of_int x) ^ " "
	| Const_char c -> " " ^ (String.make 1 c) ^ " "
	| Const_string (s, Some st) -> " \"" ^ (racketFormat s) ^ "\" " ^ st ^" "
	| Const_string (s, None) -> " \"" ^ (racketFormat s) ^ "\" "
	| Const_float f -> " " ^ f ^ " "
	| Const_int32 _ | Const_int64 _ | Const_nativeint _ -> print_string "Haven't implemented additional constants.\n"; locError loc
and racketFormat s = 
	let s = Str.global_replace (Str.regexp "\\\n") "~n" (Str.global_replace (Str.regexp "%d") "~a" (Str.global_replace (Str.regexp "%s") "~s" s))
	in Str.global_replace (Str.regexp "\'") "tick" s
and letMatcher letexp loc =
	match letexp with
	| Pexp_let(Nonrecursive, valuebindings, exp) -> "(match-let* (" ^ (letValueBinder valuebindings loc) ^ ") " ^ (expressionMatcher exp loc) ^ ")"
	| Pexp_let(Recursive, valuebindings, exp) -> "(letrec (" ^ (letValueBinder valuebindings loc) ^ ") " ^ (expressionMatcher exp loc) ^ ")"
	| _ -> print_string "Incorrect expression description matcher used: let.\n"; locError loc
and letValueBinder valuebindings loc =
	match valuebindings with
	| {	pvb_pat = pvbpat;
		pvb_expr = pvbexpr;
		pvb_attributes = pvbattr;
		pvb_loc = loc2;}::valuetl -> "[" ^ (patternMatcher pvbpat loc2) ^ " " ^ (expressionMatcher pvbexpr loc2) ^ "] "
	| [] -> ""
and applyMatcher applyExp loc =
	let rec argumentEval ls =
		match ls with
		| (arglabel, exp)::tl -> " " ^ arglabel ^ " " ^ (expressionMatcher exp loc) ^ " " ^ (argumentEval tl)
		| [] -> ""
	in
	match applyExp with
	| Pexp_apply (exp1, ls) -> "(" ^ (expressionMatcher exp1 loc) ^ (argumentEval ls) ^ ") "
	| _ -> print_string "Incorrect expression description matcher used: apply.\n"; locError loc
and tupleMatcher tupleExp loc =
	match tupleExp with
	| Pexp_tuple (hd::tl) -> "(cons " ^ (expressionMatcher hd loc) ^ " " ^ (tupleMatcher (Pexp_tuple tl) loc) ^ " )"
	| Pexp_tuple [] -> "null"
	| _ -> print_string "Incorrect expression description matcher used: tuple.\n"; locError loc
and strdescMatcher strdesc loc rackprog = 
	match strdesc with
	| Pstr_value(recflag, valuebinding) -> 
		(match valuebinding with
		| {	pvb_pat = pvbpat;
			pvb_expr = pvbexpr;
			pvb_attributes = pvbattr;
			pvb_loc = loc2;}::vbindtl -> 
			rackprog := !rackprog ^ "(define " ^ (patternMatcher pvbpat loc2);
			rackprog := !rackprog ^ (expressionMatcher pvbexpr loc2) ^ ")\n";
			strdescMatcher (Pstr_value (recflag, vbindtl)) loc rackprog
		| [] -> ())
	| Pstr_eval(exp, attributes) -> rackprog := !rackprog ^ (expressionMatcher exp loc) ^ "\n"
	| Pstr_type typedecs -> rackprog := (List.fold_left (fun str typ -> (structCreater typ) ^ "\n" ^ str) "" typedecs) ^ !rackprog ^
		(List.fold_left (fun str typ -> (typeDecMatcher typ) ^ "\n" ^ str) "" typedecs)
	| _ -> print_string "Did not match all of string descriptions.\n"; locError loc
and typeDecMatcher = function
	| { ptype_name = {txt = name; loc = typloc};
  		ptype_params = typparams;
  		ptype_cstrs = typcstrs;
  		ptype_kind = typkind;
  		ptype_private = typpriv;
  		ptype_manifest = typmanif;
  		ptype_attributes = typattrs;
  		ptype_loc = loc} -> "(define " ^ name ^ "/c\n" ^ "(flat-murec-contract " ^ typeKindMatcher name loc typkind ^ "\n" ^ name ^ "/c))"
and typeKindMatcher parentName loc = function
	| Ptype_variant constrdecs -> let orUnifier = ref "" in 
		let variantTypes = (List.fold_left (fun str typ -> str ^ "\n" ^ (constrDecMatcher orUnifier typ)) "" constrdecs) in
		"(" ^ variantTypes ^ "\n[" ^ parentName ^ "/c (or/c" ^ !orUnifier ^ ")])"
	| _ -> print_string "This typekind has not been implemented yet.\n"; locError loc
and constrDecMatcher orUnifier = function
	| {pcd_name = {txt = name; loc = newloc;}; pcd_args = args; pcd_res = res; pcd_loc = loc; pcd_attributes = attrs;} ->
		let cName = name ^ "/c" in orUnifier := !orUnifier ^ " " ^ cName;
		"[" ^ cName ^ " (struct/c " ^ name ^ " " ^ (List.fold_left (fun str core -> str ^ " " ^ (coreTypeMatcher core)) "" args) ^ ")]"
and coreTypeMatcher = function
	| {ptyp_desc = truecore; ptyp_loc = loc; ptyp_attributes = attrs;} ->
		(match truecore with
		| Ptyp_constr ({txt = Lident s; loc = newloc;}, []) -> (racketTypeMapper s)
		| _ -> print_string "This core_type_desc hasn't been implemented yet.\n"; locError loc)
and racketTypeMapper s = 
	(match s with
	| "int" -> "integer?"
	| "string" -> "string?"
	| _ -> s ^ "/c")
and structCreater = function
	{ ptype_name = {txt = name; loc = typloc};
  		ptype_params = typparams;
  		ptype_cstrs = typcstrs;
  		ptype_kind = typkind;
  		ptype_private = typpriv;
  		ptype_manifest = typmanif;
  		ptype_attributes = typattrs;
  		ptype_loc = loc} -> structTypeKindMatcher loc typkind
and structTypeKindMatcher loc = function
	| Ptype_variant constrdecs -> (List.fold_left (fun str typ -> str ^ "\n" ^ (structConstrDecMatcher typ)) "" constrdecs)
	| _ -> print_string "This typekind has not been implemented yet for structs.\n"; locError loc
and structConstrDecMatcher = function
	| {pcd_name = {txt = name; loc = newloc;}; pcd_args = args; pcd_res = res; pcd_loc = loc; pcd_attributes = attrs;} ->
		let expressionNextReg = let n = ref 0 in (fun () -> (let temp = !n in n:=!n+1; temp)) in
		"(struct " ^ name ^ " (" ^ (List.fold_left (fun str core -> str ^ " " ^ (structArgumentCreator expressionNextReg core)) "" args) ^ "))"
and structArgumentCreator nextRegFunc = function
	| {ptyp_desc = truecore; ptyp_loc = loc; ptyp_attributes = attrs;} ->
		(match truecore with
		| Ptyp_constr ({txt = Lident s; loc = newloc;}, []) -> "e" ^ (string_of_int (nextRegFunc ()))
		| _ -> print_string "This core_type_desc hasn't been implemented yet for structs.\n"; locError loc)
and toRacket ast rackprog = 
	match ast with
	| {pstr_desc = strdesc; pstr_loc = loc1;}::asttl ->
		strdescMatcher strdesc loc1 rackprog; toRacket asttl rackprog
	| [] -> ()
;;

let z = (ref "");;
toRacket (read_sig Sys.argv.(1)) z;;
z := "(define print_string write)
(define print_int write)
(define /. /)
(define +. +)
(define *. *)
(define -. -)
(define int_of_float values)
(define open_out open-output-file)
(define Formatsprintf format)
(define Formatprintf printf)
(define output_string fprintf)
(define char_of_int integer->char)
(define (output_char chan char) (write-char char chan))
(define close_out close-output-port)
(define Syscommand system)
(define (assert bool)
    (cond
      [(not bool) raise 'AssertionError]))
(define Arrayof_list list->vector)
(define Arraymake make-vector)
(define Arrayget vector-ref)
(define Arrayset vector-set!)
(define (ref x) (make-vector 1 x))
(define (:= x y) (vector-set! x 0 y))
(define (! x) (vector-ref x 0))
(define RandomStatemake vector->pseudo-random-generator)
(define RandomStateint random)
(define float_of_int values)
(define ^ string-append)
(define failwith error)
(define @ append)
(define mod remainder)
(define abs_float abs)
(define Printfsprintf printf)
(define-syntax-rule (ignore x) (void))
(define Listlength length)
(define Listrev reverse)
(define Listappend append)
(define Listfold_left foldl)
(define Listfold_right foldr)
(define == equal?)
(define (!= x y) (not (equal? x y)))\n" ^ !z;;
z := "#lang racket\n" ^ !z;;
let outputstr = Str.global_replace (Str.regexp ".ml") ".rkt" Sys.argv.(1) in
output_string (open_out outputstr) !z;;