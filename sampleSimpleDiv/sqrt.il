addr 0x0 @asm "push   %ebp"
label pc_0x0
t:u32 = R_EBP:u32
R_ESP:u32 = R_ESP:u32 - 4:u32
mem:?u32 = mem:?u32 with [R_ESP:u32, e_little]:u32 = t:u32
addr 0x1 @asm "mov    %esp,%ebp"
label pc_0x1
R_EBP:u32 = R_ESP:u32
addr 0x3 @asm "sub    $0x10,%esp"
label pc_0x3
t_69:u32 = R_ESP:u32
R_ESP:u32 = R_ESP:u32 - 0x10:u32
R_CF:bool = t_69:u32 < 0x10:u32
R_AF:bool = 0x10:u32 == (0x10:u32 & (R_ESP:u32 ^ t_69:u32 ^ 0x10:u32))
R_OF:bool = high:bool((t_69:u32 ^ 0x10:u32) & (t_69:u32 ^ R_ESP:u32))
R_PF:bool =
  ~low:bool(R_ESP:u32 >> 7:u32 ^ R_ESP:u32 >> 6:u32 ^ R_ESP:u32 >> 5:u32 ^
            R_ESP:u32 >> 4:u32 ^ R_ESP:u32 >> 3:u32 ^ R_ESP:u32 >> 2:u32 ^
            R_ESP:u32 >> 1:u32 ^ R_ESP:u32)
R_SF:bool = high:bool(R_ESP:u32)
R_ZF:bool = 0:u32 == R_ESP:u32
addr 0x6 @asm "movl   $0x0,-0xc(%ebp)"
label pc_0x6
mem:?u32 = mem:?u32 with [R_EBP:u32 + 0xfffffff4:u32, e_little]:u32 = 0:u32
addr 0xd @asm "mov    -0xc(%ebp),%eax"
label pc_0xd
R_EAX:u32 = mem:?u32[R_EBP:u32 + 0xfffffff4:u32, e_little]:u32
addr 0x10 @asm "imul   -0xc(%ebp),%eax"
label pc_0x10
T_32t1:u32 = R_EAX:u32
T_32t5:u32 = R_EBP:u32
T_32t4:u32 = T_32t5:u32 + 0xfffffff4:u32
T_32t0:u32 = mem:?u32[T_32t4:u32, e_little]:u32
T_32t2:u32 = T_32t0:u32 * T_32t1:u32
R_EAX:u32 = T_32t2:u32
/*eflags thunk: smul*/
T_0:u64 = extend:u64(low:u32(T_32t0:u32)) * extend:u64(low:u32(T_32t1:u32))
T_1:u32 = low:u32(T_0:u64)
T_2:u32 = high:u32(T_0:u64)
R_CF:bool = T_2:u32 <> T_1:u32 $>> 0x1f:u32
T_3:u8 = low:u8(T_0:u64)
R_PF:bool =
  ~low:bool(T_3:u8 >> 7:u8 ^ T_3:u8 >> 6:u8 ^
            (T_3:u8 >> 5:u8 ^ T_3:u8 >> 4:u8) ^
            (T_3:u8 >> 3:u8 ^ T_3:u8 >> 2:u8 ^ (T_3:u8 >> 1:u8 ^ T_3:u8)))
R_AF:bool = false
R_ZF:bool = T_1:u32 == 0:u32
R_SF:bool = low:bool(T_1:u32 >> 0x1f:u32)
R_OF:bool = R_CF:bool
addr 0x14 @asm "mov    %eax,-0x8(%ebp)"
label pc_0x14
mem:?u32 = mem:?u32 with [R_EBP:u32 + -8:u32, e_little]:u32 = R_EAX:u32
addr 0x17 @asm "addl   $0x1,-0xc(%ebp)"
label pc_0x17
t_80:u32 = mem:?u32[R_EBP:u32 + 0xfffffff4:u32, e_little]:u32
mem:?u32 =
  mem:?u32 with [R_EBP:u32 + 0xfffffff4:u32, e_little]:u32 =
  mem:?u32[R_EBP:u32 + 0xfffffff4:u32, e_little]:u32 + 1:u32
R_CF:bool = mem:?u32[R_EBP:u32 + 0xfffffff4:u32, e_little]:u32 < t_80:u32
R_AF:bool =
  0x10:u32 ==
  (0x10:u32 &
  (mem:?u32[R_EBP:u32 + 0xfffffff4:u32, e_little]:u32 ^ t_80:u32 ^ 1:u32))
R_OF:bool =
  high:bool((t_80:u32 ^ -2:u32) &
            (t_80:u32 ^ mem:?u32[R_EBP:u32 + 0xfffffff4:u32, e_little]:u32))
R_PF:bool =
  ~low:bool(mem:?u32[R_EBP:u32 + 0xfffffff4:u32, e_little]:u32 >> 7:u32 ^
            mem:?u32[R_EBP:u32 + 0xfffffff4:u32, e_little]:u32 >> 6:u32 ^
            mem:?u32[R_EBP:u32 + 0xfffffff4:u32, e_little]:u32 >> 5:u32 ^
            mem:?u32[R_EBP:u32 + 0xfffffff4:u32, e_little]:u32 >> 4:u32 ^
            mem:?u32[R_EBP:u32 + 0xfffffff4:u32, e_little]:u32 >> 3:u32 ^
            mem:?u32[R_EBP:u32 + 0xfffffff4:u32, e_little]:u32 >> 2:u32 ^
            mem:?u32[R_EBP:u32 + 0xfffffff4:u32, e_little]:u32 >> 1:u32 ^
            mem:?u32[R_EBP:u32 + 0xfffffff4:u32, e_little]:u32)
R_SF:bool = high:bool(mem:?u32[R_EBP:u32 + 0xfffffff4:u32, e_little]:u32)
R_ZF:bool = 0:u32 == mem:?u32[R_EBP:u32 + 0xfffffff4:u32, e_little]:u32
addr 0x1b @asm "mov    -0xc(%ebp),%eax"
label pc_0x1b
R_EAX:u32 = mem:?u32[R_EBP:u32 + 0xfffffff4:u32, e_little]:u32
addr 0x1e @asm "imul   -0xc(%ebp),%eax"
label pc_0x1e
T_32t1_82:u32 = R_EAX:u32
T_32t5_86:u32 = R_EBP:u32
T_32t4_85:u32 = T_32t5_86:u32 + 0xfffffff4:u32
T_32t0_81:u32 = mem:?u32[T_32t4_85:u32, e_little]:u32
T_32t2_83:u32 = T_32t0_81:u32 * T_32t1_82:u32
R_EAX:u32 = T_32t2_83:u32
/*eflags thunk: smul*/
T_4:u64 =
  extend:u64(low:u32(T_32t0_81:u32)) * extend:u64(low:u32(T_32t1_82:u32))
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
addr 0x22 @asm "mov    %eax,-0x4(%ebp)"
label pc_0x22
mem:?u32 = mem:?u32 with [R_EBP:u32 + -4:u32, e_little]:u32 = R_EAX:u32
addr 0x25 @asm "mov    -0x8(%ebp),%eax"
label pc_0x25
R_EAX:u32 = mem:?u32[R_EBP:u32 + -8:u32, e_little]:u32
addr 0x28 @asm "cmp    0x8(%ebp),%eax"
label pc_0x28
t_91:u32 = R_EAX:u32 - mem:?u32[R_EBP:u32 + 8:u32, e_little]:u32
R_CF:bool = R_EAX:u32 < mem:?u32[R_EBP:u32 + 8:u32, e_little]:u32
R_AF:bool =
  0x10:u32 ==
  (0x10:u32 &
  (t_91:u32 ^ R_EAX:u32 ^ mem:?u32[R_EBP:u32 + 8:u32, e_little]:u32))
R_OF:bool =
  high:bool((R_EAX:u32 ^ mem:?u32[R_EBP:u32 + 8:u32, e_little]:u32) &
            (R_EAX:u32 ^ t_91:u32))
R_PF:bool =
  ~low:bool(t_91:u32 >> 7:u32 ^ t_91:u32 >> 6:u32 ^ t_91:u32 >> 5:u32 ^
            t_91:u32 >> 4:u32 ^ t_91:u32 >> 3:u32 ^ t_91:u32 >> 2:u32 ^
            t_91:u32 >> 1:u32 ^ t_91:u32)
R_SF:bool = high:bool(t_91:u32)
R_ZF:bool = 0:u32 == t_91:u32
addr 0x2b @asm "jl     0x0000000000000017"
label pc_0x2b
cjmp R_SF:bool ^ R_OF:bool, 0x17:u32, "nocjmp0"
label nocjmp0
addr 0x2d @asm "mov    -0xc(%ebp),%eax"
label pc_0x2d
R_EAX:u32 = mem:?u32[R_EBP:u32 + 0xfffffff4:u32, e_little]:u32
addr 0x30 @asm "sub    $0x1,%eax"
label pc_0x30
t_92:u32 = R_EAX:u32
R_EAX:u32 = R_EAX:u32 - 1:u32
goal:bool = R_EAX:u32>=0:u32
R_CF:bool = t_92:u32 < 1:u32
R_AF:bool = 0x10:u32 == (0x10:u32 & (R_EAX:u32 ^ t_92:u32 ^ 1:u32))
R_OF:bool = high:bool((t_92:u32 ^ 1:u32) & (t_92:u32 ^ R_EAX:u32))
R_PF:bool =
  ~low:bool(R_EAX:u32 >> 7:u32 ^ R_EAX:u32 >> 6:u32 ^ R_EAX:u32 >> 5:u32 ^
            R_EAX:u32 >> 4:u32 ^ R_EAX:u32 >> 3:u32 ^ R_EAX:u32 >> 2:u32 ^
            R_EAX:u32 >> 1:u32 ^ R_EAX:u32)
R_SF:bool = high:bool(R_EAX:u32)
R_ZF:bool = 0:u32 == R_EAX:u32
addr 0x33 @asm "leave  "
label pc_0x33
R_ESP:u32 = R_EBP:u32
R_EBP:u32 = mem:?u32[R_ESP:u32, e_little]:u32
R_ESP:u32 = R_ESP:u32 + 4:u32
addr 0x34 @asm "ret    "
label pc_0x34
ra:u32 = mem:?u32[R_ESP:u32, e_little]:u32
R_ESP:u32 = R_ESP:u32 + 4:u32
jmp ra:u32 @str "ret"


