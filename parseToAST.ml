open Parse

let parseToAST file =
  let handle =
    try open_in file
    with Sys_error msg -> prerr_endline msg; exit 1
  in
  let buf = Lexing.from_channel handle in
  let ast = Parse.implementation buf in
  close_in handle ;
  ast