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
addr 0xc @asm "add    $0x1,%eax"
label pc_0xc
t_70:u32 = R_EAX:u32
R_EAX:u32 = R_EAX:u32 + 1:u32
R_CF:bool = R_EAX:u32 < t_70:u32
R_AF:bool = 0x10:u32 == (0x10:u32 & (R_EAX:u32 ^ t_70:u32 ^ 1:u32))
R_OF:bool = high:bool((t_70:u32 ^ -2:u32) & (t_70:u32 ^ R_EAX:u32))
R_PF:bool =
  ~low:bool(R_EAX:u32 >> 7:u32 ^ R_EAX:u32 >> 6:u32 ^ R_EAX:u32 >> 5:u32 ^
            R_EAX:u32 >> 4:u32 ^ R_EAX:u32 >> 3:u32 ^ R_EAX:u32 >> 2:u32 ^
            R_EAX:u32 >> 1:u32 ^ R_EAX:u32)
R_SF:bool = high:bool(R_EAX:u32)
R_ZF:bool = 0:u32 == R_EAX:u32
addr 0xf @asm "mov    %eax,0x1c(%esp)"
label pc_0xf
mem:?u32 = mem:?u32 with [R_ESP:u32 + 0x1c:u32, e_little]:u32 = R_EAX:u32
addr 0x13 @asm "mov    0x1c(%esp),%eax"
label pc_0x13
R_EAX:u32 = mem:?u32[R_ESP:u32 + 0x1c:u32, e_little]:u32
addr 0x17 @asm "mov    %eax,(%esp)"
label pc_0x17
mem:?u32 = mem:?u32 with [R_ESP:u32, e_little]:u32 = R_EAX:u32

wp2:bool = 
 let abs1param:u32 := mem:?u32[R_ESP:u32, e_little]:u32 in
 let abs1pre:bool := abs1param $> 0x80000000:u32 in
 let abs1post:bool := freevar1:u32 $>= 0:u32 in
 let wp3:bool := (
     let R_EAX:u32 := freevar1 in
     let R_ESP_1:u32 := R_ESP in
     let mem_47:?u32 := mem in
     let R_ESP:u32 := R_ESP_1:u32 - 4:u32 in
     let mem:?u32 := mem_47:?u32 with [R_ESP:u32, e_little]:u32 = 0x1f:u32 in
     let temp:u32 := R_ESP:u32 + 0x1c:u32 in
     let mem_77:?u32 := mem:?u32 with [temp:u32, e_little]:u32 = R_EAX:u32 in
     let temp_79:u32 := mem_77:?u32[temp:u32, e_little]:u32 in
     let t_71:u32 := temp_79:u32 - 0x7fffffff:u32 in
     let R_ZF:bool := 0:u32 == t_71:u32 in
     let mem_120:?u32 := mem_77:?u32 in
     (~R_ZF:bool |
     (let R_EAX_125:u32 := mem_120:?u32[temp:u32, e_little]:u32 in
     let goal:bool := 1:u32 $<= R_EAX_125:u32 in goal:bool)) &
     (~~R_ZF:bool |
     (let mem_138:?u32 :=
     mem_77:?u32 with [temp:u32, e_little]:u32 =
     temp_79:u32 + 1:u32 in
     let mem_120:?u32 := mem_138:?u32 in
     let R_EAX_125:u32 := mem_120:?u32[temp:u32, e_little]:u32 in
     let goal:bool := 1:u32 $<= R_EAX_125:u32 in goal:bool))
 ) in
 (abs1pre & ((~abs1post) | wp3))
