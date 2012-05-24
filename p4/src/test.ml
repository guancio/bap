#load "str.cma";;

open Str;;
open Printf;;

let bap_path = "/opt/bap-0.4/utils/";;
let stp_path = "/opt/stp-svn/bin/";;


let tocheck =
    ("abs1", (* function name *)
     "param $> 0x80000000:u32",  (* Preconditions *)
     "(R_EAX:u32 $>= 0:u32) & (R_EAX:u32 $<= param | R_EAX:u32 $<= -param)
     " (* Postconditions *),
                               (* Unit blocks *)
      ("S", 0, 0x14,
       "param:u32 = mem:?u32[R_ESP:u32+4:u32, e_little]:u32 \n \
        oldESP:u32 = R_ESP:u32", (* Old state save*)
       "", "")::                 (* start-end *)
      []
     ) ::
    ("sqrt1", 
     "xparam $>= 0:u32",
     "
    	        (R_EAX * R_EAX $<= xparam) & \
    		((R_EAX+1:u32) * (R_EAX+1:u32) $> xparam)
     ",
     ("S", 0x15, 0x31,
      "xparam:u32 = mem:?u32[R_ESP:u32+8:u32, e_little]:u32",
      "", "") ::
     ("W", 0x36, 0x4f,
      "xparam:u32 = mem:?u32[R_EBP:u32+8:u32, e_little]:u32",
      "mem:?u32[R_EBP:u32-8:u32, e_little]:u32 $<= xparam",
      " (let yvalue:u32 :=  mem:?u32[R_EBP:u32-4:u32, e_little]:u32 in
            let sqvalue:u32 := mem:?u32[R_EBP:u32-8:u32, e_little]:u32 in
            (yvalue*yvalue $<= xparam) &
    	    (sqvalue == (yvalue+1:u32)*(yvalue+1:u32))
            )
    	  "
     ) ::
     ("S", 0x54, 0x58,
      "xparam:u32 = mem:?u32[R_EBP:u32+8:u32, e_little]:u32",
      "", "") ::
     []) ::
(*
	        (R_EAX:u32 $>= 0:u32) & \

	    (yvalue $>= 0:u32) &
            (yvalue $<= 0x0000b504:u32) &
            (R_EBP == 0x8:u32)

    ("main1", 1, 2, "", "pre", "post") ::
*)
    [];;


let read_lines file_name = 
  let rec read_file channel = 
    try
      let line = input_line channel in line :: (read_file channel)
      with End_of_file -> close_in channel; []
  in read_file (open_in file_name)
;;

let write_lines file_name lines =
  let f_out = open_out (file_name) in
  List.map (fprintf f_out "%s\n") lines;
  close_out f_out 
;;

let bap_toil () =
  Sys.command (bap_path ^ "toil -bin ../tests/example.o -o ../tests/example.il")
;;
let bap_topredicate name =
  Sys.command (bap_path ^ "topredicate -il ../tests/processing/" ^ name^ ".il -post goal -stp-out ../tests/processing/" ^ name^ ".stp");
;;
let stp_prove name =
  Sys.command (stp_path ^ "stp ../tests/processing/" ^ name^ "_2.stp");
;;

let rec filter_il_block il currline (minline, maxline) =
    match il with
      	[] -> []
      | "" :: rs -> filter_il_block rs currline (minline, maxline)
      |	line :: rs -> 
        if String.length line > 10 && String.compare (String.sub line ((String.length line) -10) 10) "@str \"ret\""= 0 then filter_il_block rs currline (minline, maxline)
        else if compare (String.sub line 0 4) "addr" = 0
        then begin
          let addstr = List.nth (Str.split(Str.regexp " ") line) 1 in
          let addnum = int_of_string (addstr) in
          if addnum > maxline then []
	  else if addnum < minline then filter_il_block rs addnum (minline, maxline)
          else line:: filter_il_block rs addnum (minline, maxline)
        end
        else if (currline >= minline) && (currline <= maxline) then line :: filter_il_block rs currline (minline, maxline)
	else filter_il_block rs currline (minline, maxline)
;;

let stp_assert_to_query stp_code =
  let rec filter lines =
    match lines with
    [] -> []
    | "ASSERT(" :: rs -> "QUERY(" :: filter rs
    | "QUERY(FALSE);" :: rs -> filter rs 
    | x::rs -> x :: filter rs
  in filter stp_code
;;

let main () =
  bap_toil;
  let ilcode = read_lines "../tests/example.il" in
  let check_func (name, pre, post, blocks) = 
    let rec check_block name count pre post blocks =
      match blocks with
        [] -> true
      | ("S", startline, endline, statesave, "", "") :: rs ->
              let block_pre =
                  match rs with
                     [] -> pre
                   | ("W", startline, endline, statesave, condition, invariant) :: _ -> sprintf "(~(%s) & (%s))" condition invariant
                   | _ -> print_string "***************** UNSUPPORTED *****************\n"; "true"
              in
              let il_block = sprintf "%s\n" statesave ::
                     sprintf "precondition:bool = (%s)\n" block_pre ::
                     filter_il_block ilcode 0 (startline, endline) @
                     (sprintf "\ngoal:bool = (~precondition | %s)\n" post ::
                     []) in
              let il_block_name = name ^ (string_of_int count) in
              let il_block_path = "../tests/processing/" ^ il_block_name ^ ".il" in
              let stp_block_path = "../tests/processing/"^ il_block_name ^ ".stp" in
              let stp_patched_path = "../tests/processing/"^ il_block_name ^ "_2.stp" in
              write_lines il_block_path il_block;
              bap_topredicate il_block_name;
              let stp_code = read_lines stp_block_path in
              let stp_code = stp_assert_to_query stp_code in
              write_lines stp_patched_path stp_code;
              stp_prove il_block_name;
              check_block name (count+1) pre "true" rs
      | ("W", startline, endline, statesave, condition, invariant) :: rs ->
              let block_pre = sprintf "((%s) & (%s))" condition invariant in
              let il_block = sprintf "%s\n" statesave ::
                     sprintf "precondition:bool = (%s)\n" block_pre ::
                     filter_il_block ilcode 0 (startline, endline) @
                     (sprintf "\ngoal:bool = (~precondition | %s)\n" invariant ::
                     []) in
              let il_block_name = name ^ (string_of_int count) in
              let il_block_path = "../tests/processing/" ^ il_block_name ^ ".il" in
              let stp_block_path = "../tests/processing/"^ il_block_name ^ ".stp" in
              let stp_patched_path = "../tests/processing/"^ il_block_name ^ "_2.stp" in
              write_lines il_block_path il_block;
              bap_topredicate il_block_name;
              let stp_code = read_lines stp_block_path in
              let stp_code = stp_assert_to_query stp_code in
              write_lines stp_patched_path stp_code;
              stp_prove il_block_name;
              check_block name (count+1) pre invariant rs
      | _ -> print_string "***************** UNSUPPORTED *****************\n"; false
    in
      check_block name 1 pre post (List.rev blocks)
  in
    List.map check_func tocheck; 
    ();;

    


let () = main ()
