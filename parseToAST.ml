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
		let {ppat_desc = pdesc; ppat_loc = loc1; ppat_attributes = ppatattr;} = pattern in 
		updateLocEnv letenv (getEnv loc pdesc);
		let (args, resultExpression) = pexpfunMatcher expressiondesc loc
		in "(match-lambda** [(" ^ args ^ ") " ^ resultExpression ^ "])"
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
		| (arglabel, exp)::tl -> arglabel ^ " " ^ (expressionMatcher exp loc) ^ " " ^ (argumentEval tl) ^ " "
		| [] -> ""
	in
	match applyExp with
	| Pexp_apply (exp1, ls) -> let id = (expressionMatcher exp1 loc) in funcAdder id; 
	if (id = "raise" || id = "Printexc.to_string") then "(" ^ id ^ " '" ^ (argumentEval ls) ^ ") " else
	"(" ^ id ^ " " ^ (argumentEval ls) ^ ") "
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
"(define (Printfkprintf f . l) (f (apply format l)))
(define-struct ocamltuple (x))
(define print_string write)
(define print_int write)
(define (/. x y) (if (and (flonum? x) (flonum? y)) (/ x y) (error `ExpectedFlonum)))
(define (+. x y) (if (and (flonum? x) (flonum? y)) (+ x y) (error `ExpectedFlonum)))
(define (*. x y) (if (and (flonum? x) (flonum? y)) (* x y) (error `ExpectedFlonum)))
(define (-. x y) (if (and (flonum? x) (flonum? y)) (- x y) (error `ExpectedFlonum)))
(define (~-. x) (if (flonum? x) (- 0 x) (error `ExpectedFlonum)))
(define (~+. x) (if (flonum? x) (+ 0 x) (error `ExpectedFlonum)))
(define (intdivide x y) (if (and (exact-integer? x) (exact-integer? y)) (truncate (/ x y)) (error 'ExpectedInteger)))
(define (intmult x y) (if (and (exact-integer? x) (exact-integer? y)) (* x y) (error 'ExpectedInteger)))
(define (intplus x y) (if (and (exact-integer? x) (exact-integer? y)) (+ x y) (error 'ExpectedInteger)))
(define (intminus x y) (if (and (exact-integer? x) (exact-integer? y)) (- x y) (error 'ExpectedInteger)))
(define (~- x) (if (exact-integer? x) (- 0 x) (error `ExpectedInteger)))
(define (~+ x) (if (exact-integer? x) (+ 0 x) (error `ExpectedInteger))
(define (int_of_float x) (if (inexact? x) (inexact->exact (truncate x)) (error \"Expected float\")))
(define open_out open-output-file)
(define Formatsprintf format)
(define Formatprintf printf)
(define output_string fprintf)
(define char_of_int integer->char)
(define (string_of_int x) (if (integer? x) (number->string x) (error \"Expected int\")))
(define (int_of_string x) (if (string? (string->number x)) (string->number x) (error \"Expected string of integer\")))
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
(define (RandomStatemake v) (let ([randgen (make-pseudo-random-generator)])
                              (begin
                                (vector->pseudo-random-generator! randgen (Arrayof_list (list 1 2 3 4 5 6)))
                                randgen)))
(define RandomStateint random)
(define (float_of_int x) (if (exact-integer? x) (exact->inexact x) (error \"Expected int\")))
(define ^ string-append)
(define failwith error)
(define (@ x y) (append x y))
(define mod remainder)
(define abs_float abs)
(define Printfsprintf printf)
(define-syntax-rule (ignore x) (void))
(define Listlength length)
(define Listrev reverse)
(define (Listappend x y) (append x y))
(define Listfold_left foldl)
(define Listfold_right foldr)
(define (!= x y) (not (equal? x y)))
(define fieldlistlength length)
(define (mod_float x y) (- x (* (truncate ( / x y)) y)))
(define (Stringconcat s l) (string-join l s))
(define (string_of_float x) (if (inexact? x) (number->string x) (error \"Expected float\")))
(define (float_of_string x) (+ (string->number) 0.0))
(define <. <)
(define Printffprintf fprintf)
(define Printfprintf printf)
(define (atan2 y x) (atan (/ y x)))
(define Listmem member)
(define Listnth list-ref)
(define fieldlistrev reverse)
(struct Some (x))
(struct None ())
(define (get opt) (match opt
                   [(Some x) x]
                   [None raise `No_value]))
(define Stringset string-set!)
(define (print_newline void) (newline))
(define Listiter for-each)
(define (Listconcat l) (foldr append (list) l))
(define fst car)
(define snd cdr)
(define Printexcto_string symbol->string)
(define (log10 n) (/ (log n) (log 10)))
(define (<> a b) (not (= a b)))
(define (>pipe<> arg f) (f arg))
(define Listtl rest)
(define Stringlength string-length)
(define Stringget string-ref)
(define (Listcombine l1 l2)
  (foldr (lambda (e1 e2 acc) (cons (list e1 e2) acc))
         '()
         l1 l2))
(define (Listsplit l1)
  (foldr (lambda (e1 acc) (match e1
                            [(list f s) (match acc
                                          [(list a b) (list (cons f a) (cons s b))])])) (list '() '()) l1))
(define Listmap map)
(define Listhd first)
(define ** expt)
(define float float_of_int)
(define max_float 1.7976931348623157e+308)
(define (& x y) (and x y))
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