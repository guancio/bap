addr 0x21 @asm "addl   $0x1,-0x8(%ebp)"
label pc_0x21
t_78:u32 = mem:?u32[R_EBP:u32 + -8:u32, e_little]:u32
mem:?u32 =
  mem:?u32 with [R_EBP:u32 + -8:u32, e_little]:u32 =
  mem:?u32[R_EBP:u32 + -8:u32, e_little]:u32 + 1:u32
R_CF:bool = mem:?u32[R_EBP:u32 + -8:u32, e_little]:u32 < t_78:u32
R_AF:bool =
  0x10:u32 ==
  (0x10:u32 &
  (mem:?u32[R_EBP:u32 + -8:u32, e_little]:u32 ^ t_78:u32 ^ 1:u32))
R_OF:bool =
  high:bool((t_78:u32 ^ -2:u32) &
            (t_78:u32 ^ mem:?u32[R_EBP:u32 + -8:u32, e_little]:u32))
R_PF:bool =
  ~low:bool(mem:?u32[R_EBP:u32 + -8:u32, e_little]:u32 >> 7:u32 ^
            mem:?u32[R_EBP:u32 + -8:u32, e_little]:u32 >> 6:u32 ^
            mem:?u32[R_EBP:u32 + -8:u32, e_little]:u32 >> 5:u32 ^
            mem:?u32[R_EBP:u32 + -8:u32, e_little]:u32 >> 4:u32 ^
            mem:?u32[R_EBP:u32 + -8:u32, e_little]:u32 >> 3:u32 ^
            mem:?u32[R_EBP:u32 + -8:u32, e_little]:u32 >> 2:u32 ^
            mem:?u32[R_EBP:u32 + -8:u32, e_little]:u32 >> 1:u32 ^
            mem:?u32[R_EBP:u32 + -8:u32, e_little]:u32)
R_SF:bool = high:bool(mem:?u32[R_EBP:u32 + -8:u32, e_little]:u32)
R_ZF:bool = 0:u32 == mem:?u32[R_EBP:u32 + -8:u32, e_little]:u32
addr 0x25 @asm "mov    -0x8(%ebp),%eax"
label pc_0x25
R_EAX:u32 = mem:?u32[R_EBP:u32 + -8:u32, e_little]:u32
addr 0x28 @asm "lea    0x1(%eax),%edx"
label pc_0x28
R_EDX:u32 = R_EAX:u32 + 1:u32
addr 0x2b @asm "mov    -0x8(%ebp),%eax"
label pc_0x2b
R_EAX:u32 = mem:?u32[R_EBP:u32 + -8:u32, e_little]:u32
addr 0x2e @asm "add    $0x1,%eax"
label pc_0x2e
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
addr 0x31 @asm "imul   %edx,%eax"
label pc_0x31
T_32t1_81:u32 = R_EAX:u32
T_32t0_80:u32 = R_EDX:u32
T_32t2_82:u32 = T_32t0_80:u32 * T_32t1_81:u32
R_EAX:u32 = T_32t2_82:u32
/*eflags thunk: smul*/
T_4:u64 =
  extend:u64(low:u32(T_32t0_80:u32)) * extend:u64(low:u32(T_32t1_81:u32))
T_5:u32 = low:u32(T_4:u64)
T_6:u32 = high:u32(T_4:u64)
R_CF:bool = T_6:u32 <> T_5:u32 $>> 0x1f:u32
T_7:u8 = low:u8(T_4:u64)
R_PF:bool =
  ~low:bool(T_7:u8 >> 7:u8 ^ T_7:u8 >> 6:u8 ^
            (T_7:u8 >> 5:u8 ^ T_7:u8 >> 4:u8) ^
            (T_7:u8 >> 3:u8 ^ T_7:u8 >> 2:u8 ^ (T_7:u8 >> 1:u8 ^ T_7:u8)))
R_AF:bool = false
R_ZF:bool = T_5:u32 == 0:u32
R_SF:bool = low:bool(T_5:u32 >> 0x1f:u32)
R_OF:bool = R_CF:bool
addr 0x34 @asm "mov    %eax,-0x4(%ebp)"
label pc_0x34
mem:?u32 = mem:?u32 with [R_EBP:u32 + -4:u32, e_little]:u32 = R_EAX:u32
addr 0x37 @asm "mov    -0x4(%ebp),%eax"
label pc_0x37
R_EAX:u32 = mem:?u32[R_EBP:u32 + -4:u32, e_little]:u32
addr 0x3a @asm "cmp    0x8(%ebp),%eax"
label pc_0x3a
t_87:u32 = R_EAX:u32 - mem:?u32[R_EBP:u32 + 8:u32, e_little]:u32
R_CF:bool = R_EAX:u32 < mem:?u32[R_EBP:u32 + 8:u32, e_little]:u32
R_AF:bool =
  0x10:u32 ==
  (0x10:u32 &
  (t_87:u32 ^ R_EAX:u32 ^ mem:?u32[R_EBP:u32 + 8:u32, e_little]:u32))
R_OF:bool =
  high:bool((R_EAX:u32 ^ mem:?u32[R_EBP:u32 + 8:u32, e_little]:u32) &
            (R_EAX:u32 ^ t_87:u32))
R_PF:bool =
  ~low:bool(t_87:u32 >> 7:u32 ^ t_87:u32 >> 6:u32 ^ t_87:u32 >> 5:u32 ^
            t_87:u32 >> 4:u32 ^ t_87:u32 >> 3:u32 ^ t_87:u32 >> 2:u32 ^
            t_87:u32 >> 1:u32 ^ t_87:u32)
R_SF:bool = high:bool(t_87:u32)
R_ZF:bool = 0:u32 == t_87:u32

goal:bool = ( mem:?u32[R_EBP:u32 + -4:u32, e_little]:u32 == ( mem:?u32[R_EBP:u32 + -8:u32, e_little]:u32 + 1:u32) * ( mem:?u32[R_EBP:u32 + -8:u32, e_little]:u32 + 1:u32)) & ( mem:?u32[R_EBP:u32 + -8:u32, e_little]:u32) * ( mem:?u32[R_EBP:u32 + -8:u32, e_little]:u32) $<= ( mem:?u32[R_EBP:u32 + 16:u32, e_little]:u32)