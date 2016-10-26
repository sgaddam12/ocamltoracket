(*source: http://www.rosettacode.org/wiki/Execute_a_system_command#OCaml*)
let check_exit_status = function
  | Unix.WEXITED 0 -> ()
  | Unix.WEXITED r -> Printf.eprintf "warning: the process terminated with exit code (%d)\n%!" r
  | Unix.WSIGNALED n -> Printf.eprintf "warning: the process was killed by a signal (number: %d)\n%!" n
  | Unix.WSTOPPED n -> Printf.eprintf "warning: the process was stopped by a signal (number: %d)\n%!" n
;;
 
let syscall env cmd =
  let ic, oc, ec = Unix.open_process_full cmd env in
  let buf1 = Buffer.create 96
  and buf2 = Buffer.create 48 in
  (try
     while true do Buffer.add_channel buf1 ic 1 done
   with End_of_file -> ());
  (try
     while true do Buffer.add_channel buf2 ec 1 done
   with End_of_file -> ());
  let exit_status = Unix.close_process_full (ic, oc, ec) in
  check_exit_status exit_status;
  (Buffer.contents buf1,
   Buffer.contents buf2);;

let process file = 
(let env = (Unix.environment ()) in 
let (s1, s2) = (syscall env ("ocaml ./unify/" ^ file)) in 
let typregex1 = Str.regexp "Error: This expression has type" in
let typregex2 = Str.regexp "but an expression was expected of type" in
if (String.trim s2 = "") then 
(syscall env ("cp ./unify/" ^ file ^ " ./safe/")) 
else 
	try 
		Str.search_forward typregex2 s2 0; (Str.search_forward typregex1 s2 0); (syscall env ("cp ./unify/" ^ file ^ " ./safe/")) 
	with _ -> (syscall env ("cp ./unify/" ^ file ^ " ./quarantine/"))); ();;

let dir = "./unify/" in let files = Sys.readdir dir in Array.iter process files;;