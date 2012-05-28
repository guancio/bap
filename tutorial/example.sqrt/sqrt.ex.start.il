xparam:u32 = mem:?u32[R_ESP:u32+8:u32, e_little]:u32

precondition:bool = (xparam $>= 0:u32 & xparam $< 0x7ffd3e09:u32)

addr 0x15 @asm "push   %ebp"
label pc_0x15
t_77:u32 = R_EBP:u32
R_ESP:u32 = R_ESP:u32 - 4:u32
mem:?u32 = mem:?u32 with [R_ESP:u32, e_little]:u32 = t_77:u32
addr 0x16 @asm "mov    %esp,%ebp"
label pc_0x16
R_EBP:u32 = R_ESP:u32
addr 0x18 @asm "sub    $0x10,%esp"
label pc_0x18
t_78:u32 = R_ESP:u32
R_ESP:u32 = R_ESP:u32 - 0x10:u32
R_CF:bool = t_78:u32 < 0x10:u32
R_AF:bool = 0x10:u32 == (0x10:u32 & (R_ESP:u32 ^ t_78:u32 ^ 0x10:u32))
R_OF:bool = high:bool((t_78:u32 ^ 0x10:u32) & (t_78:u32 ^ R_ESP:u32))
R_PF:bool =
  ~low:bool(R_ESP:u32 >> 7:u32 ^ R_ESP:u32 >> 6:u32 ^ R_ESP:u32 >> 5:u32 ^
            R_ESP:u32 >> 4:u32 ^ R_ESP:u32 >> 3:u32 ^ R_ESP:u32 >> 2:u32 ^
            R_ESP:u32 >> 1:u32 ^ R_ESP:u32)
R_SF:bool = high:bool(R_ESP:u32)
R_ZF:bool = 0:u32 == R_ESP:u32
addr 0x1b @asm "movl   $0x0,-0x4(%ebp)"
label pc_0x1b
mem:?u32 = mem:?u32 with [R_EBP:u32 + -4:u32, e_little]:u32 = 0:u32
addr 0x22 @asm "mov    -0x4(%ebp),%eax"
label pc_0x22
R_EAX:u32 = mem:?u32[R_EBP:u32 + -4:u32, e_little]:u32
addr 0x25 @asm "lea    0x1(%eax),%edx"
label pc_0x25
R_EDX:u32 = R_EAX:u32 + 1:u32
addr 0x28 @asm "mov    -0x4(%ebp),%eax"
label pc_0x28
R_EAX:u32 = mem:?u32[R_EBP:u32 + -4:u32, e_little]:u32
addr 0x2b @asm "add    $0x1,%eax"
label pc_0x2b
t_79:u32 = R_EAX:u32
R_EAX:u32 = R_EAX:u32 + 1:u32
R_CF:bool = R_EAX:u32 < t_79:u32
R_AF:bool = 0x10:u32 == (0x10:u32 & (R_EAX:u32 ^ t_79:u32 ^ 1:u32))
R_OF:bool = high:bool((t_79:u32 ^ -2:u32) & (t_79:u32 ^ R_EAX:u32))
R_PF:bool =
  ~low:bool(R_EAX:u32 >> 7:u32 ^ R_EAX:u32 >> 6:u32 ^ R_EAX:u32 >> 5:u32 ^
            R_EAX:u32 >> 4:u32 ^ R_EAX:u32 >> 3:u32 ^ R_EAX:u32 >> 2:u32 ^
            R_EAX:u32 >> 1:u32 ^ R_EAX:u32)
R_SF:bool = high:bool(R_EAX:u32)
R_ZF:bool = 0:u32 == R_EAX:u32
addr 0x2e @asm "imul   %edx,%eax"
label pc_0x2e
T_32t1:u32 = R_EAX:u32
T_32t0:u32 = R_EDX:u32
T_32t2_82:u32 = T_32t0:u32 * T_32t1:u32
R_EAX:u32 = T_32t2_82:u32
/*eflags thunk: smul*/
T_2:u64 = extend:u64(low:u32(T_32t0:u32)) * extend:u64(low:u32(T_32t1:u32))
T_3:u32 = low:u32(T_2:u64)
T_4:u32 = high:u32(T_2:u64)
R_CF:bool = T_4:u32 <> T_3:u32 $>> 0x1f:u32
T_5:u8 = low:u8(T_2:u64)
R_PF:bool =
  ~low:bool(T_5:u8 >> 7:u8 ^ T_5:u8 >> 6:u8 ^
            (T_5:u8 >> 5:u8 ^ T_5:u8 >> 4:u8) ^
            (T_5:u8 >> 3:u8 ^ T_5:u8 >> 2:u8 ^ (T_5:u8 >> 1:u8 ^ T_5:u8)))
R_AF:bool = false
R_ZF:bool = T_3:u32 == 0:u32
R_SF:bool = low:bool(T_3:u32 >> 0x1f:u32)
R_OF:bool = R_CF:bool
addr 0x31 @asm "mov    %eax,-0x8(%ebp)"
label pc_0x31
mem:?u32 = mem:?u32 with [R_EBP:u32 + -8:u32, e_little]:u32 = R_EAX:u32

goal:bool = (~precondition |  (let yvalue:u32 :=  mem:?u32[R_EBP:u32-4:u32, e_little]:u32 in
            let sqvalue:u32 := mem:?u32[R_EBP:u32-8:u32, e_little]:u32 in
            (yvalue*yvalue $<= xparam) &
    	    (sqvalue == (yvalue+1:u32)*(yvalue+1:u32)) &
	    (yvalue $>= 0:u32) &
	    (xparam $< 0x7ffd3e09:u32) &
            (yvalue $<= 0xb502:u32)
            )
    	  )

