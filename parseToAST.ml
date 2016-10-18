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
				failwith ("failed to account for: start is c:" ^ string_of_int cnumstart ^ " l:" ^ string_of_int lnumstart ^ " and end is c:" ^ string_of_int cnumend ^ " l:" ^ string_of_int lnumend);;


let rec patternDescMatcher patterndesc loc =
	match patterndesc with
	| Ppat_var {txt = s; loc = loc1;} -> " " ^ s ^ " "
	| Ppat_or (patt1, patt2) -> "(or " ^ (patternMatcher patt1 loc) ^ " " ^ (patternMatcher patt2 loc) ^ ") "
	| Ppat_constant const -> (constantMatcher const loc)
	| Ppat_any -> "_ "
	| Ppat_tuple explist -> "(list " ^ (List.fold_right (fun a b -> (patternMatcher a loc) ^ " " ^ b) explist "") ^ ")"
	| Ppat_construct ({txt = Lident "::"; loc = newloc;}, _) | Ppat_construct ({txt = Lident "[]"; loc = newloc;}, _) -> 
		"(list " ^ (listPatternMatcher patterndesc newloc) ^ ")"
	| _ -> print_string "patterndescmatcher failed"; locError loc
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
		| _ -> failwith "unexpected tuple error in listMatcher")
	| Ppat_construct(_, None) -> ""
	| _ -> failwith "incorrect expressiondesc matcher used: listMatcher"
and patternMatcher pattern loc = 
	match pattern with
	| {ppat_desc = pdesc; ppat_loc = loc1; ppat_attributes = ppatattr;} ->
		patternDescMatcher pdesc loc1
and expressionDescMatcher expressiondesc loc =
	match expressiondesc with 
	| Pexp_function caselist -> 
		failwith "not implemented1"
	| Pexp_fun (arglabel, expressionopt, pattern, expression) -> 
		let (args, resultExpression) = pexpfunMatcher expressiondesc loc
		in "(match-lambda** [(" ^ args ^ ") " ^ resultExpression ^ "])"
	| Pexp_match (expression, caselist) -> (pexpmatchMatcher expressiondesc loc)
	| Pexp_ident {txt = t; loc = locid;} -> longidentMatcher t locid
	| Pexp_constant const -> constantMatcher const loc
	| Pexp_let (recflag, valuebindings, exp) -> letMatcher expressiondesc loc
	| Pexp_apply (exp1, explist) -> applyMatcher expressiondesc loc
	| Pexp_tuple explist -> tupleMatcher expressiondesc loc
	| Pexp_construct ({txt = Lident "::"; loc = newloc;}, _) | Pexp_construct ({txt = Lident "[]"; loc = newloc;}, _) -> 
		"(list " ^ (listMatcher expressiondesc newloc) ^ ")"
	| Pexp_ifthenelse (exp1, exp2, expopt) ->
		(match expopt with 
		| Some exp3 -> "(if " ^ (expressionMatcher exp1 loc) ^ " " ^ (expressionMatcher exp2 loc) ^ " " ^ (expressionMatcher exp3 loc) ^ ")"
		| None -> "(if " ^ (expressionMatcher exp1 loc) ^ " " ^ (expressionMatcher exp2 loc) ^ ")")
	| Pexp_sequence (exp1, exp2) -> "(begin " ^ (expressionMatcher exp1 loc) ^ " " ^ (expressionMatcher exp2 loc) ^ ")"
	| Pexp_construct ({txt = Lident "()"; loc = newloc;}, None) -> "void"
	| _ -> print_string "expressiondescmatcher failed"; locError loc
and expressionMatcher expression loc  =
	match expression with
	| {pexp_desc = expdesc; pexp_loc = loc4; pexp_attributes = pexpattr;} ->
		expressionDescMatcher expdesc loc4 
and listMatcher expressiondesc loc = 
	match expressiondesc with
	| Pexp_construct(_, Some {pexp_desc = expdesc1; pexp_loc = newloc1; pexp_attributes = pexpattr1;}) -> 
		(match expdesc1 with
		| Pexp_tuple (hd::{pexp_desc = expdesc2; pexp_loc = newloc2; pexp_attributes = pexpattr2;}::tl) -> 
			(expressionMatcher hd newloc2) ^ " " ^ (listMatcher expdesc2 newloc2)
		| _ -> failwith "unexpected tuple error in listMatcher")
	| Pexp_construct(_, None) -> ""
	| _ -> failwith "incorrect expressiondesc matcher used: listMatcher"
and caseListMatcher caselist loc = 
	match caselist with
	| {pc_lhs = pclhs; pc_guard = pcguard; pc_rhs = pcrhs;}::casetl -> 
		let pcstring = 
		(match pcguard with
		| Some exp -> failwith "not implemented some pcguard"
		| None -> "") in
		"\n[ " ^ (patternMatcher pclhs loc) ^ pcstring ^ " " ^ (expressionMatcher pcrhs loc) ^ " ] "
		^ (caseListMatcher casetl loc)
	| [] -> ""
and pexpfunMatcher expressiondesc loc =
	match expressiondesc with
	| (Pexp_fun (arglabel, expressionopt, pattern, expression)) ->
		let stringopt = 
			(match expressionopt with
			| Some exp -> failwith "not implemented some expopt"
			| None -> "") in
		let arg = arglabel ^ stringopt ^ (patternMatcher pattern loc) in
		let {pexp_desc = expdesc; pexp_loc = newloc; pexp_attributes = pexpattr;} = expression in
			(match expdesc with 
			| Pexp_fun (_, _, _, _) -> 
				let (args, resExp) = (pexpfunMatcher expdesc newloc) in (arg ^ args, resExp)
			| _ -> (arg, (expressionMatcher expression loc )))
	| _ -> failwith "incorrect expressiondesc matcher used: fun"
and pexpmatchMatcher expressiondesc loc =
	match expressiondesc with
	| (Pexp_match (expression, caselist)) ->
		" (match " ^ (expressionMatcher expression loc) ^ (caseListMatcher caselist loc) ^ ") ";
	| _ -> failwith "incorrect expressiondesc matcher used: match"
and longidentMatcher t loc =
	match t with 
	| Lident s -> s
	| Ldot (newt, s) -> (longidentMatcher newt loc) ^ s
	| Lapply (newt1, newt2) -> (longidentMatcher newt1 loc) ^ (longidentMatcher newt2 loc)
and constantMatcher const loc = 
	match const with
	| Const_int x -> " " ^ (string_of_int x) ^ " "
	| Const_char c -> " " ^ (String.make 1 c) ^ " "
	| Const_string (s, Some st) -> " \"" ^ s ^ "\" " ^ st ^" "
	| Const_string (s, None) -> " \"" ^ s ^ "\" "
	| Const_float f -> " " ^ f ^ ".0 "
	| Const_int32 _ | Const_int64 _ | Const_nativeint _ -> print_string "not implemented constant"; locError loc
and letMatcher letexp loc =
	match letexp with
	| Pexp_let(Nonrecursive, valuebindings, exp) -> "(match-let* (" ^ (letValueBinder valuebindings loc) ^ ") " ^ (expressionMatcher exp loc) ^ ")"
	| Pexp_let(Recursive, valuebindings, exp) -> "(letrec (" ^ (letValueBinder valuebindings loc) ^ ") " ^ (expressionMatcher exp loc) ^ ")"
	| _ -> failwith "incorrect expressiondesc matcher used: let"
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
	| _ -> failwith "incorrect expressiondesc matcher used: apply"
and tupleMatcher tupleExp loc =
	match tupleExp with
	| Pexp_tuple (hd::tl) -> "(cons " ^ (expressionMatcher hd loc) ^ " " ^ (tupleMatcher (Pexp_tuple tl) loc) ^ " )"
	| Pexp_tuple [] -> "null"
	| _ -> failwith "incorrect expressiondesc matcher used: tuple"
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
	| _ -> print_string "did not match all of strdesc"; locError loc
and toRacket ast rackprog = 
	match ast with
	| {pstr_desc = strdesc; pstr_loc = loc1;}::asttl ->
		strdescMatcher strdesc loc1 rackprog; toRacket asttl rackprog
	| [] -> ()
;;

let z = (ref "");;
toRacket (read_sig "exampletranslate.ml") z;;
print_string !z;;