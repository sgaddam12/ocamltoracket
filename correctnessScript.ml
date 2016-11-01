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
let env = (Unix.environment ()) in 
let (s1, s2) = (syscall env ("myprog.exe " ^ file)) in 
let typregex = Str.regexp "Fatal error: exception Failure" in
	try 
		Str.search_forward typregex s2 0;
    let oc = open_out_gen [Open_creat; Open_text; Open_append] 0o640 "translationResults.txt" in
    output_string oc (file ^ "\n" ^ s2 ^ "\n");
    close_out oc
	with _ -> ();;


let dir = "./" in let files = Sys.readdir dir in Array.iter process files;;