addr 0x0 @asm "push   %ebp"
label pc_0x0
t:u32 = R_EBP:u32
R_ESP:u32 = R_ESP:u32 - 4:u32
mem:?u32 = mem:?u32 with [R_ESP:u32, e_little]:u32 = t:u32
addr 0x1 @asm "mov    %esp,%ebp"
label pc_0x1
R_EBP:u32 = R_ESP:u32
addr 0x3 @asm "and    $0xfffffff0,%esp"
label pc_0x3
R_ESP:u32 = R_ESP:u32 & 0xfffffff0:u32
R_OF:bool = false
R_CF:bool = false
R_AF:bool = unknown "AF is undefined after and":bool
R_PF:bool =
  ~low:bool(R_ESP:u32 >> 7:u32 ^ R_ESP:u32 >> 6:u32 ^ R_ESP:u32 >> 5:u32 ^
            R_ESP:u32 >> 4:u32 ^ R_ESP:u32 >> 3:u32 ^ R_ESP:u32 >> 2:u32 ^
            R_ESP:u32 >> 1:u32 ^ R_ESP:u32)
R_SF:bool = high:bool(R_ESP:u32)
R_ZF:bool = 0:u32 == R_ESP:u32
addr 0x6 @asm "sub    $0x20,%esp"
label pc_0x6
t_69:u32 = R_ESP:u32
R_ESP:u32 = R_ESP:u32 - 0x20:u32
R_CF:bool = t_69:u32 < 0x20:u32
R_AF:bool = 0x10:u32 == (0x10:u32 & (R_ESP:u32 ^ t_69:u32 ^ 0x20:u32))
R_OF:bool = high:bool((t_69:u32 ^ 0x20:u32) & (t_69:u32 ^ R_ESP:u32))
R_PF:bool =
  ~low:bool(R_ESP:u32 >> 7:u32 ^ R_ESP:u32 >> 6:u32 ^ R_ESP:u32 >> 5:u32 ^
            R_ESP:u32 >> 4:u32 ^ R_ESP:u32 >> 3:u32 ^ R_ESP:u32 >> 2:u32 ^
            R_ESP:u32 >> 1:u32 ^ R_ESP:u32)
R_SF:bool = high:bool(R_ESP:u32)
R_ZF:bool = 0:u32 == R_ESP:u32
addr 0x9 @asm "mov    0x8(%ebp),%eax"
label pc_0x9
R_EAX:u32 = mem:?u32[R_EBP:u32 + 8:u32, e_little]:u32
addr 0xc @asm "mov    %eax,(%esp)"
label pc_0xc
mem:?u32 = mem:?u32 with [R_ESP:u32, e_little]:u32 = R_EAX:u32
addr 0xf @asm "call   0x0000000000000010"
label pc_0xf
R_ESP:u32 = R_ESP:u32 - 4:u32
mem:?u32 = mem:?u32 with [R_ESP:u32, e_little]:u32 = 0x14:u32
jmp 0x10:u32 @str "call"
addr 0x14 @asm "mov    %eax,0x18(%esp)"
label pc_0x14
mem:?u32 = mem:?u32 with [R_ESP:u32 + 0x18:u32, e_little]:u32 = R_EAX:u32
addr 0x18 @asm "mov    0x18(%esp),%eax"
label pc_0x18
R_EAX:u32 = mem:?u32[R_ESP:u32 + 0x18:u32, e_little]:u32
addr 0x1c @asm "mov    %eax,(%esp)"
label pc_0x1c
mem:?u32 = mem:?u32 with [R_ESP:u32, e_little]:u32 = R_EAX:u32
addr 0x1f @asm "call   0x0000000000000020"
label pc_0x1f
R_ESP:u32 = R_ESP:u32 - 4:u32
mem:?u32 = mem:?u32 with [R_ESP:u32, e_little]:u32 = 0x24:u32
jmp 0x20:u32 @str "call"
addr 0x24 @asm "mov    %eax,0x1c(%esp)"
label pc_0x24
mem:?u32 = mem:?u32 with [R_ESP:u32 + 0x1c:u32, e_little]:u32 = R_EAX:u32
addr 0x28 @asm "mov    0x1c(%esp),%eax"
label pc_0x28
R_EAX:u32 = mem:?u32[R_ESP:u32 + 0x1c:u32, e_little]:u32
addr 0x2c @asm "leave  "
label pc_0x2c
R_ESP:u32 = R_EBP:u32
R_EBP:u32 = mem:?u32[R_ESP:u32, e_little]:u32
R_ESP:u32 = R_ESP:u32 + 4:u32
addr 0x2d @asm "ret    "
label pc_0x2d
ra:u32 = mem:?u32[R_ESP:u32, e_little]:u32
R_ESP:u32 = R_ESP:u32 + 4:u32
jmp ra:u32 @str "ret"


