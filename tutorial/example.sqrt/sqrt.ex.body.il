xparam:u32 = mem:?u32[R_EBP:u32+8:u32, e_little]:u32

precondition:bool = (((mem:?u32[R_EBP:u32-8:u32, e_little]:u32 $<= xparam) & ( (let yvalue:u32 :=  mem:?u32[R_EBP:u32-4:u32, e_little]:u32 in
            let sqvalue:u32 := mem:?u32[R_EBP:u32-8:u32, e_little]:u32 in
            (yvalue*yvalue $<= xparam) &
    	    (sqvalue == (yvalue+1:u32)*(yvalue+1:u32)) &
	    (yvalue $>= 0:u32) &
	    (xparam $< 0x7ffd3e09:u32) &
            (yvalue $<= 0xb502:u32)
            )
    	  )))

addr 0x36 @asm "addl   $0x1,-0x4(%ebp)"
label pc_0x36
t_87:u32 = mem:?u32[R_EBP:u32 + -4:u32, e_little]:u32
mem:?u32 =
  mem:?u32 with [R_EBP:u32 + -4:u32, e_little]:u32 =
  mem:?u32[R_EBP:u32 + -4:u32, e_little]:u32 + 1:u32
R_CF:bool = mem:?u32[R_EBP:u32 + -4:u32, e_little]:u32 < t_87:u32
R_AF:bool =
  0x10:u32 ==
  (0x10:u32 &
  (mem:?u32[R_EBP:u32 + -4:u32, e_little]:u32 ^ t_87:u32 ^ 1:u32))
R_OF:bool =
  high:bool((t_87:u32 ^ -2:u32) &
            (t_87:u32 ^ mem:?u32[R_EBP:u32 + -4:u32, e_little]:u32))
R_PF:bool =
  ~low:bool(mem:?u32[R_EBP:u32 + -4:u32, e_little]:u32 >> 7:u32 ^
            mem:?u32[R_EBP:u32 + -4:u32, e_little]:u32 >> 6:u32 ^
            mem:?u32[R_EBP:u32 + -4:u32, e_little]:u32 >> 5:u32 ^
            mem:?u32[R_EBP:u32 + -4:u32, e_little]:u32 >> 4:u32 ^
            mem:?u32[R_EBP:u32 + -4:u32, e_little]:u32 >> 3:u32 ^
            mem:?u32[R_EBP:u32 + -4:u32, e_little]:u32 >> 2:u32 ^
            mem:?u32[R_EBP:u32 + -4:u32, e_little]:u32 >> 1:u32 ^
            mem:?u32[R_EBP:u32 + -4:u32, e_little]:u32)
R_SF:bool = high:bool(mem:?u32[R_EBP:u32 + -4:u32, e_little]:u32)
R_ZF:bool = 0:u32 == mem:?u32[R_EBP:u32 + -4:u32, e_little]:u32
addr 0x3a @asm "mov    -0x4(%ebp),%eax"
label pc_0x3a
R_EAX:u32 = mem:?u32[R_EBP:u32 + -4:u32, e_little]:u32
addr 0x3d @asm "lea    0x1(%eax),%edx"
label pc_0x3d
R_EDX:u32 = R_EAX:u32 + 1:u32
addr 0x40 @asm "mov    -0x4(%ebp),%eax"
label pc_0x40
R_EAX:u32 = mem:?u32[R_EBP:u32 + -4:u32, e_little]:u32
addr 0x43 @asm "add    $0x1,%eax"
label pc_0x43
t_88:u32 = R_EAX:u32
R_EAX:u32 = R_EAX:u32 + 1:u32
R_CF:bool = R_EAX:u32 < t_88:u32
R_AF:bool = 0x10:u32 == (0x10:u32 & (R_EAX:u32 ^ t_88:u32 ^ 1:u32))
R_OF:bool = high:bool((t_88:u32 ^ -2:u32) & (t_88:u32 ^ R_EAX:u32))
R_PF:bool =
  ~low:bool(R_EAX:u32 >> 7:u32 ^ R_EAX:u32 >> 6:u32 ^ R_EAX:u32 >> 5:u32 ^
            R_EAX:u32 >> 4:u32 ^ R_EAX:u32 >> 3:u32 ^ R_EAX:u32 >> 2:u32 ^
            R_EAX:u32 >> 1:u32 ^ R_EAX:u32)
R_SF:bool = high:bool(R_EAX:u32)
R_ZF:bool = 0:u32 == R_EAX:u32
addr 0x46 @asm "imul   %edx,%eax"
label pc_0x46
T_32t1_90:u32 = R_EAX:u32
T_32t0_89:u32 = R_EDX:u32
T_32t2_91:u32 = T_32t0_89:u32 * T_32t1_90:u32
R_EAX:u32 = T_32t2_91:u32
/*eflags thunk: smul*/
T_6:u64 =
  extend:u64(low:u32(T_32t0_89:u32)) * extend:u64(low:u32(T_32t1_90:u32))
T_7:u32 = low:u32(T_6:u64)
T_8:u32 = high:u32(T_6:u64)
R_CF:bool = T_8:u32 <> T_7:u32 $>> 0x1f:u32
T_9:u8 = low:u8(T_6:u64)
R_PF:bool =
  ~low:bool(T_9:u8 >> 7:u8 ^ T_9:u8 >> 6:u8 ^
            (T_9:u8 >> 5:u8 ^ T_9:u8 >> 4:u8) ^
            (T_9:u8 >> 3:u8 ^ T_9:u8 >> 2:u8 ^ (T_9:u8 >> 1:u8 ^ T_9:u8)))
R_AF:bool = false
R_ZF:bool = T_7:u32 == 0:u32
R_SF:bool = low:bool(T_7:u32 >> 0x1f:u32)
R_OF:bool = R_CF:bool
addr 0x49 @asm "mov    %eax,-0x8(%ebp)"
label pc_0x49
mem:?u32 = mem:?u32 with [R_EBP:u32 + -8:u32, e_little]:u32 = R_EAX:u32
addr 0x4c @asm "mov    -0x8(%ebp),%eax"
label pc_0x4c
R_EAX:u32 = mem:?u32[R_EBP:u32 + -8:u32, e_little]:u32
addr 0x4f @asm "cmp    0x8(%ebp),%eax"
label pc_0x4f
t_96:u32 = R_EAX:u32 - mem:?u32[R_EBP:u32 + 8:u32, e_little]:u32
R_CF:bool = R_EAX:u32 < mem:?u32[R_EBP:u32 + 8:u32, e_little]:u32
R_AF:bool =
  0x10:u32 ==
  (0x10:u32 &
  (t_96:u32 ^ R_EAX:u32 ^ mem:?u32[R_EBP:u32 + 8:u32, e_little]:u32))
R_OF:bool =
  high:bool((R_EAX:u32 ^ mem:?u32[R_EBP:u32 + 8:u32, e_little]:u32) &
            (R_EAX:u32 ^ t_96:u32))
R_PF:bool =
  ~low:bool(t_96:u32 >> 7:u32 ^ t_96:u32 >> 6:u32 ^ t_96:u32 >> 5:u32 ^
            t_96:u32 >> 4:u32 ^ t_96:u32 >> 3:u32 ^ t_96:u32 >> 2:u32 ^
            t_96:u32 >> 1:u32 ^ t_96:u32)
R_SF:bool = high:bool(t_96:u32)
R_ZF:bool = 0:u32 == t_96:u32

goal:bool = (~precondition |  (let yvalue:u32 :=  mem:?u32[R_EBP:u32-4:u32, e_little]:u32 in
            let sqvalue:u32 := mem:?u32[R_EBP:u32-8:u32, e_little]:u32 in
            (yvalue*yvalue $<= xparam) &
    	    (sqvalue == (yvalue+1:u32)*(yvalue+1:u32)) &
	    (yvalue $>= 0:u32) &
	    (xparam $< 0x7ffd3e09:u32) &
            (yvalue $<= 0xb502:u32)
            )
    	  )

