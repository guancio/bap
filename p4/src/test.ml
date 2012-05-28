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
     "xparam $>= 0:u32 & xparam $< 0x7ffd3e09:u32",
     "
    	        (R_EAX * R_EAX $<= xparam) & \
    		((R_EAX+1:u32) * (R_EAX+1:u32) $> xparam) &
		(R_EAX $>= 0:u32)
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
    	    (sqvalue == (yvalue+1:u32)*(yvalue+1:u32)) &
	    (yvalue $>= 0:u32) &
	    (xparam $< 0x7ffd3e09:u32) &
            (yvalue $<= 0xb502:u32)
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

*)
    ("main1",
	"(param $> 0:u32)",
	"R_EAX $>=0:u32",
	("S", 0x59, 0x62, "param:u32:= mem:?u32[R_ESP:u32+8:u32, e_little]:u32", "", "") ::
	("C", 0x65, 0x65, "let xparam:u32:= mem:?u32[R_ESP:u32, e_little]:u32 in" , "abs1", "")::
	("S", 0x6a, 0x70, "", "", "") ::
	("C", 0x73, 0x73, "let xparam:u32:= mem:?u32[R_ESP:u32, e_little]:u32 in" , "sqrt1", "")::
	("S", 0x78, 0x7f, "", "", "")::
	[]
	)::
    [];;

let find_f fname =
  let rec in_find_f lst =
     match lst with
        (lfname, pre, post, blocks) :: rs ->
  	  if lfname = fname then (lfname, pre, post, tocheck)
	  else in_find_f rs
  in in_find_f tocheck
;;
	

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
  print_string ("predicate:" ^ name ^"\n");
  Sys.command (bap_path ^ "topredicate -il ../tests/processing/" ^ name^ ".il -post goal -stp-out ../tests/processing/" ^ name^ ".stp -o ../tests/processing/" ^ name ^ "_wp.il");
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


let fix_free_vars pre =
	let rec in_fix_free exp =
		match exp with
		  [] -> [] 
		| line :: rs ->
			try
			let first_eq = Str.search_forward (Str.regexp "=") line 0 in
			let first_mem = Str.search_forward (Str.regexp "mem") line 0 in
			let second_mem = Str.search_forward (Str.regexp "mem") line first_eq in
			let second_mem_end = Str.search_forward (Str.regexp ":") line second_mem in
			let mem_name = String.sub line second_mem (second_mem_end-second_mem) in
			(sprintf "let %s:?u32:= mem:?u32 in " mem_name) ::[]
			with Not_found -> in_fix_free rs
	in (in_fix_free pre) @ pre
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
		   | ("C", startline, endline, statesave, fname, "") :: _ -> "true"
                   | _ -> print_string "***************** UNSUPPORTED *****************\n"; "true"
              in
              let il_block = sprintf "%s\n" statesave ::
                     sprintf "precondition:bool = (%s)\n" block_pre ::
                     filter_il_block ilcode 0 (startline, endline) @
                     (sprintf "\ngoal:bool = (~precondition | %s)\n" post ::
                     []) in
              let il_block_name = name ^ (string_of_int count) in
              let il_block_path = "../tests/processing/" ^ il_block_name ^ ".il" in
	      let il_wp_path = "../tests/processing/" ^ il_block_name ^ "_wp.il" in
              let stp_block_path = "../tests/processing/"^ il_block_name ^ ".stp" in
              let stp_patched_path = "../tests/processing/"^ il_block_name ^ "_2.stp" in
              write_lines il_block_path il_block;
              bap_topredicate il_block_name;
	      (match rs with
		  ("C", startline, endline, statesave, fname, "") :: others ->
			let pre_block = read_lines il_wp_path in
			let pre_block = fix_free_vars pre_block in
			let pre_block = 
				"let wpre:bool := ("  ::
				(sprintf "let R_EAX:u32 := free_var%d:u32 in" count) ::
				pre_block @ (") in " ::[]) in
			
			let (fname, fpre, fpost, blocks) =  find_f fname in
			let fpost = Str.split (Str.regexp "\n") fpost in
			let post_block = 
				"let f_post:bool := (" ::
				(sprintf "let R_EAX:u32 := free_var%d:u32 in" count) ::
				fpost @ (") in "::[]) in
			
                        let fpre_block = Str.split (Str.regexp "\n") fpre in
			let fpre_block =
				"let f_pre:bool := (" ::
				fpre_block @ (") in " ::[]) in
			let wp =
				(statesave:: [] ) @
				pre_block @
				post_block @
				fpre_block	
			in
			let wp_str = String.concat "\n" wp in
			let wp_str = wp_str^("(f_pre) & ((~ f_post) | wpre)") in
			print_int (count+2);
			check_block name (count+2) pre wp_str others
		| _ -> 
	              	let stp_code = read_lines stp_block_path in
        	      	let stp_code = stp_assert_to_query stp_code in
              		write_lines stp_patched_path stp_code;
              		stp_prove il_block_name;
              		check_block name (count+1) pre "true" rs
		)
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
