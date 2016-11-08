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

let funcs = ref [];;

let funcAdder s = 
	if (not (List.mem s !funcs)) then funcs := (s::!funcs);;

let funcPrint () =
	List.iter (fun s -> print_string (s ^ "\n")) !funcs;;

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

let globenv = Hashtbl.create 10;;

let letenv = Hashtbl.create 10;;

let rec patternDescMatcher patterndesc loc =
	match patterndesc with
	| Ppat_var {txt = s; loc = loc1;} -> " " ^ (getCurrentName (varConverter s)) ^ " "
	| Ppat_or (patt1, patt2) -> "(or " ^ (patternMatcher patt1 loc) ^ " " ^ (patternMatcher patt2 loc) ^ ") "
	| Ppat_constant const -> (constantMatcher const loc)
	| Ppat_any -> "_ "
	| Ppat_tuple explist -> "(ocamltuple (list " ^ (List.fold_right (fun a b -> (patternMatcher a loc) ^ " " ^ b) explist "") ^ "))"
	| Ppat_construct ({txt = Lident "::"; loc = newloc;}, _) | Ppat_construct ({txt = Lident "[]"; loc = newloc;}, _) -> 
		"(list " ^ (listPatternMatcher patterndesc newloc) ^ ")"
	| Ppat_construct ({txt = Lident "()"; loc = newloc;}, None) -> "void"
	| Ppat_construct ({txt = Lident typ as lid; loc = newloc;}, None) -> longidentMatcher lid loc
	| Ppat_construct ({txt = Lident typ as lid; loc = newloc;}, opt) -> let typname = longidentMatcher lid loc in 
		"(" ^ typname ^ " " ^ (typeArgumentMatcher loc opt) ^ ")"
	| _ -> print_string "Pattern description matcher failed.\n"; locError loc
and varConverter ?toplvl:(b = false) s = 
	let s = Str.global_replace (Str.regexp "'") ">tick<" s
	in let s = Str.global_replace (Str.regexp "|") ">pipe<" s
	in let s = Str.global_replace (Str.regexp "\\") "\\\\\\\\" s in
	if b then
		s
	else if (Hashtbl.mem letenv s) then 
		Hashtbl.find letenv s 
	else if (Hashtbl.mem globenv s) then 
		Hashtbl.find globenv s 
	else s
and getCurrentName s =
	if (Hashtbl.mem letenv s) then s else if (Hashtbl.mem globenv s) then Hashtbl.find globenv s else s
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
and caseListFunctionMatcher caselist loc = 
	match caselist with
	| {pc_lhs = pclhs; pc_guard = pcguard; pc_rhs = pcrhs;}::casetl -> 
		let pcstring = 
		(match pcguard with
		| Some exp -> " #:when " ^ expressionMatcher exp loc
		| None -> "") in 
		"\n[(" ^ (patternMatcher pclhs loc) ^ ")" ^ pcstring ^ " " ^ (expressionMatcher pcrhs loc) ^ " ] "
		^ (caseListFunctionMatcher casetl loc)
	| [] -> ""
and getEnvCaseList loc = function
	| {pc_lhs = {ppat_desc = pdesc; ppat_loc = loc1; ppat_attributes = ppatattr;}; pc_guard = pcguard; pc_rhs = pcrhs;}::casetl -> 
		(getEnv loc pdesc)@(getEnvCaseList loc casetl)
	| [] -> []
and expressionDescMatcher expressiondesc loc =
	match expressiondesc with
	| Pexp_function caselist -> updateLocEnv letenv (getEnvCaseList loc caselist);
		"(match-lambda** " ^ (caseListFunctionMatcher caselist loc) ^ ")"
	| Pexp_fun (arglabel, expressionopt, pattern, expression) -> 
		let exp = expressionMatcher expression loc in
		let {ppat_desc = pdesc; ppat_loc = loc1; ppat_attributes = ppatattr;} = pattern in 
		updateLocEnv letenv (getEnv loc pdesc);
		let pat = patternDescMatcher pdesc loc
		in "(match-lambda [" ^ pat ^ " " ^ exp ^ "])"
	| Pexp_match (expression, caselist) -> updateLocEnv letenv (getEnvCaseList loc caselist); (pexpmatchMatcher expressiondesc loc)
	| Pexp_ident {txt = t; loc = locid;} -> longidentMatcher t locid
	| Pexp_constant const -> constantMatcher const loc
	| Pexp_let (recflag, valuebindings, exp) -> letMatcher expressiondesc loc
	| Pexp_apply (exp1, explist) -> applyMatcher expressiondesc loc
	| Pexp_tuple explist -> "(ocamltuple (list " ^ (List.fold_right (fun a b -> (expressionMatcher a loc) ^ " " ^ b) explist "") ^ "))"
	| Pexp_construct ({txt = Lident "::"; loc = newloc;}, _) ->  
		listMatcher expressiondesc newloc
	| Pexp_construct ({txt = Lident "[]"; loc = newloc;}, _) ->
		"(list)"
	| Pexp_ifthenelse (exp1, exp2, expopt) ->
		(match expopt with 
		| Some exp3 -> "(if " ^ (expressionMatcher exp1 loc) ^ " " ^ (expressionMatcher exp2 loc) ^ " " ^ (expressionMatcher exp3 loc) ^ ")"
		| None -> "(if " ^ (expressionMatcher exp1 loc) ^ " " ^ (expressionMatcher exp2 loc) ^ "(void))")
	| Pexp_sequence (exp1, exp2) -> "(begin " ^ (expressionMatcher exp1 loc) ^ " " ^ (expressionMatcher exp2 loc) ^ ")"
	| Pexp_construct ({txt = Lident "()"; loc = newloc;}, None) -> "void"
	| Pexp_construct ({txt = Lident "true"; loc = newloc;}, None) -> "true"
	| Pexp_construct ({txt = Lident "false"; loc = newloc;}, None) -> "false"
	| Pexp_assert exp -> let assertExp = {pexp_desc = (Pexp_ident {txt = Lident "assert"; loc = loc;}); pexp_loc = loc; pexp_attributes = [];} in
		expressionDescMatcher (Pexp_apply (assertExp, [("", exp)])) loc
	| Pexp_try (exp, caselist) -> tryMatcher expressiondesc loc
	| Pexp_construct ({txt = Lident typ as lid; loc = newloc;}, Some exp) -> let {pexp_desc = expdesc; pexp_loc = newloc; pexp_attributes = pexpattr;} = exp in
		"(" ^ (longidentMatcher lid loc) ^ " " ^
		(match expdesc with
		| Pexp_tuple explist -> (List.fold_left (fun str exp -> str ^ " " ^ (expressionMatcher exp newloc)) "" explist)
		| _ -> expressionDescMatcher expdesc loc) ^ ")"
	| Pexp_construct ({txt = Lident typ as lid; loc = newloc;}, None) -> "(" ^ (longidentMatcher lid newloc) ^ ")"
	| Pexp_for (pattern, exp1, exp2, _, exp3) -> "(for ([" ^ patternMatcher pattern loc ^ " (in-range " 
		^ expressionMatcher exp1 loc ^ expressionMatcher exp2 loc ^ ")]) " ^ expressionMatcher exp3 loc ^ ")"
	| Pexp_field (exp, {txt = l; loc = newloc;}) -> 
		let s = "field" ^ expressionMatcher exp loc ^ longidentMatcher l loc in funcAdder s; s
	| _ -> print_string "Expression description matcher failed.\n"; locError loc
and tryMatcher expressiondesc loc = 
	match expressiondesc with
	| Pexp_try (exp, caselist) -> "(with-handlers (" ^ caseListExceptionMatcher caselist loc ^ ") " ^ expressionMatcher exp loc ^ ")"
	| _ -> print_string "Incorrect expression description matcher used: try.\n"; locError loc
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
		| Some exp -> " #:when " ^ expressionMatcher exp loc
		| None -> "") in
		"\n[ " ^ (patternMatcher pclhs loc) ^ pcstring ^ " " ^ (expressionMatcher pcrhs loc) ^ " ] "
		^ (caseListMatcher casetl loc)
	| [] -> ""
and caseListExceptionMatcher caselist loc =
	match caselist with
	| {pc_lhs = pclhs; pc_guard = pcguard; pc_rhs = pcrhs;}::casetl -> 
		let pcstring = 
		(match pcguard with
		| Some exp -> " #:when " ^ expressionMatcher exp loc
		| None -> "") in
		"\n[ " ^ (patternMatcher pclhs loc) ^ pcstring ^ " (lambda (exn) " ^ (expressionMatcher pcrhs loc) ^ ")] "
		^ (caseListMatcher casetl loc)
	| [] -> ""
and pexpfunMatcher expressiondesc loc =
	match expressiondesc with
	| (Pexp_fun (arglabel, expressionopt, pattern, expression)) ->
		let stringopt = 
			(match expressionopt with
			| Some exp -> print_string "Haven't accounted for expression options under Pexp_fun.\n"; locError loc
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
		" (match " ^ (expressionMatcher expression loc) ^ (caseListMatcher caselist loc) ^ ") "
	| _ -> print_string "Incorrect expression description matcher used: match.\n"; locError loc
and longidentMatcher ?toplvl:(b = false) t loc =
	(match t with 
	| Lident s -> identConverter b s
	| Ldot (newt, s) -> (longidentMatcher ~toplvl:true newt loc) ^ (identConverter b s)
	| Lapply (newt1, newt2) -> (longidentMatcher ~toplvl:true newt1 loc) ^ (longidentMatcher ~toplvl:true newt2 loc))
and identConverter b s = 
	let s = (match s with
	| "+" -> "intplus"
	| "-" -> "intminus"
	| "/" -> "intdivide"
	| "*" -> "intmult"
	| "&&" -> "and"
	| "||" -> "or"
	| "|>" -> "pipe>"
	| "==" -> "equal?"
	| _ -> let s = Str.global_replace (Str.regexp "'") ">tick<" s
			in let s = Str.global_replace (Str.regexp "|") ">pipe<" s
			in Str.global_replace (Str.regexp "\\") "\\\\\\\\" s) in 
	if b then
		s
	else if (Hashtbl.mem letenv s) then 
		Hashtbl.find letenv s 
	else if (Hashtbl.mem globenv s) then 
		Hashtbl.find globenv s 
	else s
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
	in let s = Str.global_replace (Str.regexp "'") ">tick<" s
			in let s = Str.global_replace (Str.regexp "|") ">pipe<" s
			in Str.global_replace (Str.regexp "\\") "\\\\\\\\" s
and letMatcher letexp loc =
	match letexp with
	| Pexp_let(Nonrecursive, valuebindings, exp) -> 
	updateLocEnv letenv (getEnvValueBindings loc valuebindings);
	"(match-let* (" ^ (letValueBinder valuebindings loc) ^ ") " ^ (expressionMatcher exp loc) ^ ")"
	| Pexp_let(Recursive, valuebindings, exp) -> 
	updateLocEnv letenv (getEnvValueBindings loc valuebindings);
	"(letrec (" ^ (letValueBinder valuebindings loc) ^ ")\n" ^ (expressionMatcher exp loc) ^ ")"
	| _ -> print_string "Incorrect expression description matcher used: let.\n"; locError loc
and updateLocEnv tbl = function
	| h::t -> Hashtbl.add tbl h h; updateLocEnv tbl t
	| [] -> ()
and getEnvValueBindings loc = function
	| {	pvb_pat = {ppat_desc = pdesc; ppat_loc = loc1; ppat_attributes = ppatattr;};
		pvb_expr = pvbexpr;
		pvb_attributes = pvbattr;
		pvb_loc = loc2;}::valuetl -> (getEnv loc pdesc)@(getEnvValueBindings loc valuetl)
	| [] -> []
and letValueBinder valuebindings loc =
	match valuebindings with
	| {	pvb_pat = pvbpat;
		pvb_expr = pvbexpr;
		pvb_attributes = pvbattr;
		pvb_loc = loc2;}::valuetl -> let joiner = if (valuetl = []) then "" else "\n" in let exprstr = (expressionMatcher pvbexpr loc2) in
		"[" ^ (patternMatcher pvbpat loc2) ^ " " ^ exprstr ^ "]" ^ joiner ^ letValueBinder valuetl loc
	| [] -> ""
and applyMatcher applyExp loc =
	let rec argumentEval ls =
		match ls with
		| (arglabel, exp)::tl -> let (count, str) = argumentEval tl in
			(count + 1, arglabel ^ " " ^ (expressionMatcher exp loc) ^ ") " ^ str)
		| [] -> (0, "")
	in
	match applyExp with
	| Pexp_apply (exp1, ls) -> let id = (expressionMatcher exp1 loc) in
	funcAdder id; let (count, args) = argumentEval ls in let parens = String.make count '(' in
	if (id = "raise" || id = "Printexc.to_string") then parens ^ id ^ " '" ^ args ^ ") " else
	parens ^ id ^ " " ^ args
	| _ -> print_string "Incorrect expression description matcher used: apply.\n"; locError loc
and strdescMatcher strdesc loc rackprog = 
	match strdesc with
	| Pstr_value(recflag, valuebinding) -> 
		(match valuebinding with
		| {	pvb_pat = {ppat_desc = pdesc; ppat_loc = loc1; ppat_attributes = ppatattr;} as pvbpat;
			pvb_expr = pvbexpr;
			pvb_attributes = pvbattr;
			pvb_loc = loc2;}::vbindtl -> let defineType =
			(match pdesc with
				| Ppat_var _ -> "(define "
				| _ -> "(match-define ") in
			let exprstr = (expressionMatcher pvbexpr loc2) in
			let localenv = getEnv loc1 pdesc in 
			updateEnv globenv localenv; Hashtbl.clear letenv;
			rackprog := !rackprog ^ defineType ^ (patternMatcher pvbpat loc2);
			rackprog := !rackprog ^ exprstr ^ ")\n";
			strdescMatcher (Pstr_value (recflag, vbindtl)) loc rackprog
		| [] -> ())
	| Pstr_eval(exp, attributes) -> rackprog := !rackprog ^ (expressionMatcher exp loc) ^ "\n"
	| Pstr_type typedecs -> let structCreations = (List.fold_left (fun str typ -> (structCreator typ) ^ "\n" ^ str) "" typedecs) in
		rackprog := !rackprog ^ structCreations ^
		(List.fold_left (fun str typ -> (typeDecMatcher typ) ^ "\n" ^ str) "" typedecs)
	| _ -> print_string "Did not match all of string descriptions.\n"; locError loc
and getEnv loc1 = function
	| Ppat_var {txt = s; loc = _;} -> [varConverter ~toplvl:true s]
	| Ppat_or ({ppat_desc = patt1; ppat_loc = _; ppat_attributes = _;}, {ppat_desc = patt2; ppat_loc = _; ppat_attributes = _;}) -> 
	(getEnv loc1 patt1)@(getEnv loc1 patt2)
	| Ppat_constant const -> []
	| Ppat_any -> []
	| Ppat_tuple (h::t) -> (match h with
		| {ppat_desc = pdesc; ppat_loc = _; ppat_attributes = _;} ->
		(getEnv loc1 pdesc)@(getEnv loc1 (Ppat_tuple t)))
	| Ppat_tuple [] -> []
	| Ppat_construct ({txt = Lident "::"; loc = _;}, Some {ppat_desc = pdesc; ppat_loc = _; ppat_attributes = _;}) -> getEnv loc1 pdesc
	| Ppat_construct ({txt = Lident "[]"; loc = _;}, None) -> []
	| Ppat_construct ({txt = Lident "()"; loc = _;}, None) -> []
	| Ppat_construct ({txt = Lident typ as lid; loc = _;}, None) -> [longidentMatcher ~toplvl:true lid loc1]
	| Ppat_construct ({txt = Lident typ as lid; loc = _;}, Some {ppat_desc = pdesc; ppat_loc = _; ppat_attributes = _;}) -> [longidentMatcher ~toplvl:true lid loc1]
	| _ -> print_string "Did not match all patterns in environment getter.\n"; locError loc1
and updateEnv tbl env = 
	match env with
	| a::t -> 
	if (Hashtbl.mem tbl a) then
		let f = fresh a in Hashtbl.add tbl a f
	else
		Hashtbl.add tbl a a
	| [] -> ()
and fresh a =
	let suff = string_of_int (next_reg ()) in a ^ ">SHADOW<" ^ suff
and typeDecMatcher = function
	| { ptype_name = {txt = name; loc = typloc};
  		ptype_params = typparams;
  		ptype_cstrs = typcstrs;
  		ptype_kind = typkind;
  		ptype_private = typpriv;
  		ptype_manifest = typmanif;
  		ptype_attributes = typattrs;
  		ptype_loc = loc} ->
  		let newname = 
  		(if (Hashtbl.mem globenv name) then
  			(let z = fresh name in (Hashtbl.add globenv name z); z)
  		else
  			((Hashtbl.add globenv name name); name))
  		in
  		"(define " ^ newname ^ "/c\n" ^ "(flat-murec-contract " ^ typeKindMatcher newname loc typkind ^ "\n" ^ newname ^ "/c))"
and typeKindMatcher parentName loc = function
	| Ptype_variant constrdecs -> let orUnifier = ref "" in 
		let variantTypes = (List.fold_left (fun str typ -> str ^ "\n" ^ (constrDecMatcher orUnifier typ)) "" constrdecs) in
		"(" ^ variantTypes ^ "\n[" ^ parentName ^ "/c (or/c" ^ !orUnifier ^ ")])"
	| _ -> print_string "This typekind has not been implemented yet.\n"; locError loc
and constrDecMatcher orUnifier = function
	| {pcd_name = {txt = name; loc = newloc;}; pcd_args = args; pcd_res = res; pcd_loc = loc; pcd_attributes = attrs;} ->
		let name = Hashtbl.find globenv name in
		let cName = name ^ "/c" in orUnifier := !orUnifier ^ " " ^ cName;
		"[" ^ cName ^ " (struct/c " ^ name ^ " " ^ (List.fold_left (fun str core -> str ^ " " ^ (coreTypeMatcher core)) "" args) ^ ")]"
and coreTypeMatcher = function
	| {ptyp_desc = truecore; ptyp_loc = loc; ptyp_attributes = attrs;} ->
		(match truecore with
		| Ptyp_constr ({txt = Lident s as lid; loc = newloc;}, []) -> (racketTypeMapper (longidentMatcher ~toplvl:true lid loc))
		| _ -> print_string "This core_type_desc hasn't been implemented yet.\n"; locError loc)
and racketTypeMapper s = 
	(match s with
	| "int" -> "integer?"
	| "string" -> "string?"
	| _ -> (Hashtbl.find globenv s) ^ "/c")
and structCreator = function
	{ ptype_name = {txt = name; loc = typloc};
  		ptype_params = typparams;
  		ptype_cstrs = typcstrs;
  		ptype_kind = typkind;
  		ptype_private = typpriv;
  		ptype_manifest = typmanif;
  		ptype_attributes = typattrs;
  		ptype_loc = loc} -> structTypeKindMatcher typloc typkind
and structTypeKindMatcher loc = function
	| Ptype_variant constrdecs -> (List.fold_left (fun str typ -> str ^ "\n" ^ (structConstrDecMatcher typ)) "" constrdecs)
	| _ -> print_string "This typekind has not been implemented yet for structs.\n"; locError loc
and structConstrDecMatcher = function
	| {pcd_name = {txt = name; loc = newloc;}; pcd_args = args; pcd_res = res; pcd_loc = loc; pcd_attributes = attrs;} ->
		let expressionNextReg = let n = ref 0 in (fun () -> (let temp = !n in n:=!n+1; temp)) in
		let newName = 
		(if (Hashtbl.mem globenv name) then 
			(let z = fresh name in (Hashtbl.add globenv name z); z)
		else 
			((Hashtbl.add globenv name name); name)) in
		"(struct " ^ newName ^ " (" ^ (List.fold_left (fun str core -> str ^ " " ^ (structArgumentCreator expressionNextReg core)) "" args) ^ "))"
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

Hashtbl.clear globenv;;
Hashtbl.add globenv "list" "list";;
let z = (ref "");;
toRacket (read_sig Sys.argv.(1)) z;;
z := 
"(define (count-format-string-args s)
  (count (curry equal? #\\~) (string->list s)))
(define (curry-format func)
  (lambda (format-string)
    (let ([num-args (count-format-string-args format-string)])
    (letrec ([arg-taker (lambda (list-args)
      (lambda (arg)
        (let ([new-list-args (append list-args (list arg))])
        (if (= (length new-list-args) num-args) (func (apply format format-string new-list-args)) (arg-taker new-list-args)))))])
    (arg-taker '())))))

(define Printfkprintf (lambda (f) (curry-format f)))
(define-struct ocamltuple (x))
(define print_string (match-lambda [s (if (string? s) (write s) (error `ExpectedString))]))
(define print_int (match-lambda [i (if (exact-integer? i) (write i) (error `ExpectedInteger))]))
(define /. (match-lambda [x (match-lambda [y (if (and (flonum? x) (flonum? y)) (/ x y) (error `ExpectedFlonum))])]))
(define +. (match-lambda [x (match-lambda [y (if (and (flonum? x) (flonum? y)) (+ x y) (error `ExpectedFlonum))])]))
(define -. (match-lambda [x (match-lambda [y (if (and (flonum? x) (flonum? y)) (- x y) (error `ExpectedFlonum))])]))
(define *. (match-lambda [x (match-lambda [y (if (and (flonum? x) (flonum? y)) (* x y) (error `ExpectedFlonum))])]))
(define ~-. (match-lambda [x (if (flonum? x) (- 0 x) (error `ExpectedFlonum))]))
(define ~+. (match-lambda [x (if (flonum? x) (+ 0 x) (error `ExpectedFlonum))]))
(define intdivide (match-lambda [x (match-lambda [y (if (and (exact-integer? x) (exact-integer? y)) (truncate (/ x y)) (error 'ExpectedInteger))])]))
(define intmult (match-lambda [x (match-lambda [y (if (and (exact-integer? x) (exact-integer? y)) (* x y) (error 'ExpectedInteger))])]))
(define intplus (match-lambda [x (match-lambda [y (if (and (exact-integer? x) (exact-integer? y)) (+ x y) (error 'ExpectedInteger))])]))
(define intminus (match-lambda [x (match-lambda [y (if (and (exact-integer? x) (exact-integer? y)) (- x y) (error 'ExpectedInteger))])]))
(define ~- (match-lambda [x (if (exact-integer? x) (- 0 x) (error `ExpectedInteger))]))
(define ~+ (match-lambda [x (if (exact-integer? x) (+ 0 x) (error `ExpectedInteger))]))
(define int_of_float (match-lambda [x (if (inexact? x) (inexact->exact (truncate x)) (error \"Expected float\"))]))
(define open_out (match-lambda [s (open-output-file s)]))
(define Formatsprintf (curry-format (lambda (n) n)))
(define Formatprintf (curry-format (lambda (n) (write n))))
(define output_string (match-lambda [output (match-lambda [s (fprintf output s)])]))
(define char_of_int (match-lambda [c (integer->char c)]))
(define string_of_int (match-lambda [x (if (integer? x) (number->string x) (error \"Expected int\"))]))
(define int_of_string (match-lambda [x (if (string? (string->number x)) (string->number x) (error \"Expected string of integer\"))]))
(define output_char (match-lambda [chan (match-lambda [char (write-char char chan)])]))
(define close_out (match-lambda [out (close-output-port out)]))
(define Syscommand (match-lambda [command (system command)]))
(define assert (match-lambda [bool
    (cond
      [(not bool) raise 'AssertionError])]))
(define Arrayof_list (match-lambda [l (list->vector l)]))
(define Arraymake (match-lambda [size (match-lambda [init (make-vector size init)])]))
(define Arrayget (match-lambda [vec (match-lambda [pos (vector-ref vec pos)])]))
(define Arrayset (match-lambda [vec (match-lambda [pos (match-lambda [init (vector-set! vec pos init)])])]))
(define ref (match-lambda [x (make-vector 1 x)]))
(define := (match-lambda [x (match-lambda [y (vector-set! x 0 y)])]))
(define ! (match-lambda [x (vector-ref x 0)]))
(define RandomStatemake (match-lambda [x (let ([randgen (make-pseudo-random-generator)])
                              (begin
                                (vector->pseudo-random-generator! randgen (Arrayof_list (list 1 2 3 4 5 6)))
                                randgen))]))
(define RandomStateint (match-lambda [t (match-lambda [i (random t i)])]))
(define float_of_int (match-lambda [x (if (exact-integer? x) (exact->inexact x) (error \"Expected int\"))]))
(define ^ (match-lambda [x (match-lambda [y (string-append x y)])]))
(define failwith (match-lambda [sym (error sym)]))
(define @ (match-lambda [x (match-lambda [y (append x y)])]))
(define mod (match-lambda [x (match-lambda [y (if (and (exact-integer? x) (exact-integer? y)) (remainder x y) (error 'ExpectedInteger))])]))
(define abs_float (match-lambda [f (if (flonum? f) (abs f) (error `ExpectedFlonum))]))
(define Printfsprintf Formatsprintf)
(define-syntax-rule (ignore x) (void))
(define Listlength (match-lambda [l (length l)]))
(define Listrev (match-lambda [l (reverse l)]))
(define Listappend (match-lambda [x (match-lambda [y (append x y)])]))
(define Listfold_left (match-lambda [x (match-lambda [y (match-lambda [z (foldl x y z)])])]))
(define Listfold_right (match-lambda [x (match-lambda [y (match-lambda [z (foldr x y z)])])]))
(define != (match-lambda [x (match-lambda [y (not (equal? x y))])]))
(define fieldlistlength (match-lambda [x (length x)]))
(define mod_float (match-lambda [x (match-lambda [y (if (and (flonum? x) (flonum? y)) (- x (* (truncate ( / x y)) y)) (error `ExpectedFlonum))])]))
(define Stringconcat (match-lambda [s (match-lambda [l (string-join l s)])]))
(define string_of_float (match-lambda [x (if (flonum? x) (number->string x) (error \"Expected float\"))]))
(define float_of_string (match-lambda [x (+ (string->number x) 0.0)]))
(define <. (match-lambda [x (match-lambda [y (< x y)])]))
(define Printffprintf (lambda (out) (curry-format (curry fprintf out))))
(define Printfprintf Formatprintf)
(define atan2 (match-lambda [x (match-lambda [y (if (and (flonum? x) (flonum? y)) (atan (/ y x)) (error 'ExpectedFlonum))])]))
(define Listmem (match-lambda [x (match-lambda [l (member x l)])]))
(define Listnth (match-lambda [l (match-lambda [y (list-ref l y)])]))
(define fieldlistrev (match-lambda [l (reverse l)]))
(struct Some (x))
(struct None ())
(define get (match-lambda [opt (match opt
                   [(Some x) x]
                   [None raise `No_value])]))
(define Stringset (match-lambda [s (match-lambda [i (match-lambda [c (string-set! s i c)])])]))
(define print_newline (match-lambda [void (newline)]))
(define Listiter (match-lambda [f (match-lambda [l (for-each f l)])]))
(define Listconcat (match-lambda [l (foldr append (list) l)]))
(define fst (match-lambda [l (car l)]))
(define snd (match-lambda [l (cdr l)]))
(define Printexcto_string (match-lambda [exc (symbol->string exc)]))
(define log10 (match-lambda [n (if (flonum? n) (/ (log n) (log 10)) (error 'ExpectedFlonum))]))
(define <> (match-lambda [a (match-lambda [b (not (= a b))])]))
(define >pipe<> (match-lambda [arg (match-lambda [f (f arg)])]))
(define Listtl (match-lambda [l (rest l)]))
(define Stringlength (match-lambda [s (string-length s)]))
(define Stringget (match-lambda [s (match-lambda [i (string-ref s i)])]))
(define Listcombine (match-lambda [l1 (match-lambda [l2
  (foldr (lambda (e1 e2 acc) (cons (list e1 e2) acc))
         '()
         l1 l2)])]))
(define Listsplit (match-lambda [l1
  (foldr (lambda (e1 acc) (match e1
                            [(list f s) (match acc
                                          [(list a b) (list (cons f a) (cons s b))])])) (list '() '()) l1)]))
(define Listmap (match-lambda [f (match-lambda [l (map f l)])])) 
(define Listhd (match-lambda [l (first l)]))
(define ** (match-lambda [x (match-lambda [y (if (and (flonum? x) (flonum? y)) (expt x y) (error 'ExpectedFlonum))])]))
(define float (match-lambda [i (float_of_int i)]))
(define max_float 1.7976931348623157e+308)
(define & (match-lambda [x (match-lambda [y (and x y)])]))
(define min_float 2.2250738585072014e-308)\n" ^ !z;;
z := "#lang racket\n" ^ !z;;
let outputstr = "./translated/" ^ (Str.global_replace (Str.regexp ".ml") ".rkt" Sys.argv.(1)) in
output_string (open_out outputstr) !z;;
(*and asDissecter {ppat_desc = pdesc; ppat_loc = loc1; ppat_attributes = ppatattr;} loc =
	match pdesc with
	| Ppat_alias (pattern, {txt = s; loc = newloc;}) -> let (rems, remn) = asDissecter pattern loc
	("(let " ^ (longidentMatcher s) ^ " " ^ rems, 1 + remn)
	| Ppat_or (patt1, patt2) -> let (rems, remn) = asDissecter patt1 loc in
		let (remss, remnn) = asDissecter patt2 loc in
		(rems ^ remss, remn + remnn)
	| 
	| _ -> ("", 0)

	and tupleMatcher tupleExp loc =
	match tupleExp with
	| Pexp_tuple (hd::tl) -> "(tuple " ^ (expressionMatcher hd loc) ^ " " ^ (tupleMatcher (Pexp_tuple tl) loc) ^ " )"
	| Pexp_tuple [] -> "null"
	| _ -> print_string "Incorrect expression description matcher used: tuple.\n"; locError loc*)

(*(require 
  (rename-in racket/base [define define-original]) 
  (for-syntax syntax/parse)) 
(define-syntax (define stx) 
   (syntax-parse stx 
     [(define i:id v:expr) (if (identifier-binding #'i) 
                               #'(set! i v) 
                               #'(define-original i v))] 
     [(define (f:id arg:id ...) body ...) 
        (if (identifier-binding #'f) 
            #'(set! f (lambda (arg ...) body ...)) 
            #'(define-original (f arg ...) body ...))]))
(require syntax/parse/define
         (for-syntax syntax/parse ; for syntax-parse
                     syntax/stx)) ; for stx-map

(begin-for-syntax
  ;; defs->set!s : Syntax -> Syntax
  ;; A helper function for match-set!, to transform define-values into set!-values
  (define (defs->set!s defs)
    (syntax-parse defs #:literals (begin define-values)
      [(define-values [x ...] expr)
       #'(set!-values [x ...] expr)]
      [(begin defs ...)
       #:with (set!s ...) (stx-map defs->set!s #'(defs ...))
       #'(begin set!s ...)])))

(define-syntax-parser match-set!
  [(match-set! pat expr)
   #:with defs
   (local-expand #'(match-define pat expr) (syntax-local-context) #f)
   (defs->set!s #'defs)])*)