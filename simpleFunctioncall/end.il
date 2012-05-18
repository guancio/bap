addr 0x1a @asm "call   0x000000000000001b"
label pc_0x1a
R_ESP:u32 = R_ESP:u32 - 4:u32
mem:?u32 = mem:?u32 with [R_ESP:u32, e_little]:u32 = 0x1f:u32
addr 0x1f @asm "mov    %eax,0x1c(%esp)"
label pc_0x1f
mem:?u32 = mem:?u32 with [R_ESP:u32 + 0x1c:u32, e_little]:u32 = R_EAX:u32
addr 0x23 @asm "cmpl   $0x7fffffff,0x1c(%esp)"
label pc_0x23
t_71:u32 = mem:?u32[R_ESP:u32 + 0x1c:u32, e_little]:u32 - 0x7fffffff:u32
R_CF:bool = mem:?u32[R_ESP:u32 + 0x1c:u32, e_little]:u32 < 0x7fffffff:u32
R_AF:bool =
  0x10:u32 ==
  (0x10:u32 &
  (t_71:u32 ^ mem:?u32[R_ESP:u32 + 0x1c:u32, e_little]:u32 ^ 0x7fffffff:u32))
R_OF:bool =
  high:bool((mem:?u32[R_ESP:u32 + 0x1c:u32, e_little]:u32 ^ 0x7fffffff:u32) &
            (mem:?u32[R_ESP:u32 + 0x1c:u32, e_little]:u32 ^ t_71:u32))
R_PF:bool =
  ~low:bool(t_71:u32 >> 7:u32 ^ t_71:u32 >> 6:u32 ^ t_71:u32 >> 5:u32 ^
            t_71:u32 >> 4:u32 ^ t_71:u32 >> 3:u32 ^ t_71:u32 >> 2:u32 ^
            t_71:u32 >> 1:u32 ^ t_71:u32)
R_SF:bool = high:bool(t_71:u32)
R_ZF:bool = 0:u32 == t_71:u32
addr 0x2b @asm "je     0x0000000000000032"
label pc_0x2b
cjmp R_ZF:bool, 0x32:u32, "nocjmp0"
label nocjmp0
addr 0x2d @asm "addl   $0x1,0x1c(%esp)"
label pc_0x2d
t_72:u32 = mem:?u32[R_ESP:u32 + 0x1c:u32, e_little]:u32
mem:?u32 =
  mem:?u32 with [R_ESP:u32 + 0x1c:u32, e_little]:u32 =
  mem:?u32[R_ESP:u32 + 0x1c:u32, e_little]:u32 + 1:u32
R_CF:bool = mem:?u32[R_ESP:u32 + 0x1c:u32, e_little]:u32 < t_72:u32
R_AF:bool =
  0x10:u32 ==
  (0x10:u32 &
  (mem:?u32[R_ESP:u32 + 0x1c:u32, e_little]:u32 ^ t_72:u32 ^ 1:u32))
R_OF:bool =
  high:bool((t_72:u32 ^ -2:u32) &
            (t_72:u32 ^ mem:?u32[R_ESP:u32 + 0x1c:u32, e_little]:u32))
R_PF:bool =
  ~low:bool(mem:?u32[R_ESP:u32 + 0x1c:u32, e_little]:u32 >> 7:u32 ^
            mem:?u32[R_ESP:u32 + 0x1c:u32, e_little]:u32 >> 6:u32 ^
            mem:?u32[R_ESP:u32 + 0x1c:u32, e_little]:u32 >> 5:u32 ^
            mem:?u32[R_ESP:u32 + 0x1c:u32, e_little]:u32 >> 4:u32 ^
            mem:?u32[R_ESP:u32 + 0x1c:u32, e_little]:u32 >> 3:u32 ^
            mem:?u32[R_ESP:u32 + 0x1c:u32, e_little]:u32 >> 2:u32 ^
            mem:?u32[R_ESP:u32 + 0x1c:u32, e_little]:u32 >> 1:u32 ^
            mem:?u32[R_ESP:u32 + 0x1c:u32, e_little]:u32)
R_SF:bool = high:bool(mem:?u32[R_ESP:u32 + 0x1c:u32, e_little]:u32)
R_ZF:bool = 0:u32 == mem:?u32[R_ESP:u32 + 0x1c:u32, e_little]:u32
addr 0x32 @asm "mov    0x1c(%esp),%eax"
label pc_0x32
R_EAX:u32 = mem:?u32[R_ESP:u32 + 0x1c:u32, e_little]:u32
addr 0x36 @asm "leave  "
label pc_0x36
R_ESP:u32 = R_EBP:u32
R_EBP:u32 = mem:?u32[R_ESP:u32, e_little]:u32
R_ESP:u32 = R_ESP:u32 + 4:u32
addr 0x37 @asm "ret    "
label pc_0x37
ra:u32 = mem:?u32[R_ESP:u32, e_little]:u32
R_ESP:u32 = R_ESP:u32 + 4:u32


goal:bool = R_EAX:u32 $>=1:u32