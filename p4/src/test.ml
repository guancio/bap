#load "str.cma";;

open Str;;
open Printf;;

let bap_path = "../../bap-0.4/utils/";;
let stp_path = "../../stp/bin/";;

let tocheck =
    ("abs1", 0, 0x14,
    	     "param:u32 = mem:?u32[R_ESP:u32+4:u32, e_little]:u32 \n \
	      mem1:?u32 = mem \n \
	      oldESP:u32 = R_ESP:u32",
    	     "param $> 0x80000000:u32 & \
	      oldESP $>10:u32 & oldESP $<0xffff:u32",
	     "(R_EAX:u32 $>= 0:u32) & (R_EAX:u32 $<= param | R_EAX:u32 $<= -param) & \
	     ((anyaddr:u32 >= oldESP-4:u32 & anyaddr:u32 < oldESP-4:u32+4:u32) |( mem[anyaddr, e_little]:u8 == mem1[anyaddr, e_little]:u8))
	     "
	     ) ::
    ("sqrt1", 0x54, 0x58,
    	      "xparam:u32 = mem:?u32[R_EBP:u32+8:u32, e_little]:u32 \n \
	       yparam:u32 = mem:?u32[R_EBP:u32-8:u32, e_little]:u32 \n \
	       sqparam:u32 =  mem:?u32[R_EBP:u32-4:u32, e_little]:u32 \n \
	       mem1:?u32 = mem",
	       "(yparam*yparam $<= xparam) &
	        (sqparam == (yparam+1:u32)*(yparam+1:u32)) &
		(yparam $> 0:u32) &
		(sqparam $> xparam)
	       ",
	       "
	        (R_EAX:u32 $>= 0:u32) & \
	        (R_EAX * R_EAX $<= xparam) & \
		((R_EAX+1:u32) * (R_EAX+1:u32) $> xparam) & \
		(mem[anyaddr:u32, e_little]:u8 == mem1[anyaddr, e_little]:u8)
	       ") ::
(*
    ("main1", 1, 2, "", "pre", "post") ::
*)
    [];;

let main () =
  let rec read_file channel = 
    try
      let line = input_line channel in line :: (read_file channel)
    with End_of_file -> close_in channel; []
  in

  Sys.command (bap_path ^ "toil -bin ../tests/example.o -o ../tests/example.il");
  let channel = open_in "../tests/example.il" in
  let ilcode = read_file channel in
  
  let rec filter code currline minline maxline =
    match code with
      	[] -> []
      | "" :: rs -> filter rs currline minline maxline
      |	line :: rs -> 
        if String.length line > 10 && String.compare (String.sub line ((String.length line) -10) 10) "@str \"ret\""= 0 then filter rs currline minline maxline
        else if compare (String.sub line 0 4) "addr" = 0
        then begin
          let addstr = List.nth (Str.split(Str.regexp " ") line) 1 in
          let addnum = int_of_string (addstr) in
          if addnum > maxline then []
	  else if addnum < minline then filter rs addnum minline maxline
          else line:: filter rs addnum minline maxline
        end
        else if (currline >= minline) && (currline <= maxline) then line :: filter rs currline minline maxline
	else filter rs currline minline maxline
  in
  let check_func func_desc = 
    match func_desc with (name, startline, endline, statesave, pre, post) ->
    let function_out = open_out ("../tests/processing/" ^ name ^ ".il") in
    
    fprintf function_out "%s\n\n" statesave;
    fprintf function_out "precondition:bool = (%s)\n\n" pre;
    
    List.map (fprintf function_out "%s\n") (filter ilcode 0 startline endline);
    fprintf function_out "\n\ngoal:bool = (~precondition | %s)\n" post;
    close_out function_out; 
    Sys.command (bap_path ^ "topredicate -il ../tests/processing/" ^ name^ ".il -post goal -stp-out ../tests/processing/" ^ name^ ".stp");
    
    let channel = open_in ("../tests/processing/"^ name ^ ".stp") in
    let stp_code = read_file channel in    

    let rec filter lines =
       match lines with
          [] -> []
        | "ASSERT(" :: rs -> "QUERY(" :: filter rs
        | "QUERY(FALSE);" :: rs -> filter rs
	| x::rs -> x :: filter rs
    in
    let stp_out = open_out ("../tests/processing/" ^ name ^ "2.stp") in
    List.map (fprintf stp_out "%s\n") (filter stp_code);
    close_out stp_out; 

    Sys.command (stp_path ^ "stp ../tests/processing/" ^ name^ "2.stp");
    true
  in
    List.map check_func tocheck; 
    ();;

    


let () = main ()