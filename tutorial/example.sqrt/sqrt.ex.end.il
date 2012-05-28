xparam:u32 = mem:?u32[R_EBP:u32+8:u32, e_little]:u32

precondition:bool = ((~(mem:?u32[R_EBP:u32-8:u32, e_little]:u32 $<= xparam) & ( (let yvalue:u32 :=  mem:?u32[R_EBP:u32-4:u32, e_little]:u32 in
            let sqvalue:u32 := mem:?u32[R_EBP:u32-8:u32, e_little]:u32 in
            (yvalue*yvalue $<= xparam) &
    	    (sqvalue == (yvalue+1:u32)*(yvalue+1:u32)) &
	    (yvalue $>= 0:u32) &
	    (xparam $< 0x7ffd3e09:u32) &
            (yvalue $<= 0xb502:u32)
            )
    	  )))

addr 0x54 @asm "mov    -0x4(%ebp),%eax"
label pc_0x54
R_EAX:u32 = mem:?u32[R_EBP:u32 + -4:u32, e_little]:u32
addr 0x57 @asm "leave  "
label pc_0x57
R_ESP:u32 = R_EBP:u32
R_EBP:u32 = mem:?u32[R_ESP:u32, e_little]:u32
R_ESP:u32 = R_ESP:u32 + 4:u32
addr 0x58 @asm "ret    "
label pc_0x58
ra_97:u32 = mem:?u32[R_ESP:u32, e_little]:u32
R_ESP:u32 = R_ESP:u32 + 4:u32

goal:bool = (~precondition | 
    	        (R_EAX * R_EAX $<= xparam) & ((R_EAX+1:u32) * (R_EAX+1:u32) $> xparam) &
		(R_EAX $>= 0:u32)
     )

