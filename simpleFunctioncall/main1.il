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

pabsaddr:u32 = mem:?u32[R_ESP:u32, e_little]:u32
pabsvalue:u32 = mem:?u32[paddr:u32, e_little]:u32
abspre:bool = pabsvalue $> 0x10000000:u32
notabspost:bool = ~(freevar2:u32 $>=0:u32)
wp2subst:bool = let R_EAX:u32:= freevar2 in
let temp:u32 := R_ESP:u32 + 0x18:u32 in
let mem:?u32 := mem_47:?u32 with [temp:u32, e_little]:u32 = R_EAX:u32 in
let R_EAX_87:u32 := mem:?u32[temp:u32, e_little]:u32 in
let mem_88:?u32 := mem:?u32 with [R_ESP:u32, e_little]:u32 = R_EAX_87:u32 in
let paddr:u32 := mem_88:?u32[R_ESP:u32, e_little]:u32 in
let pvalue:u32 := mem_88:?u32[paddr:u32, e_little]:u32 in
let sqrtpre:bool := 0:u32 $<= pvalue:u32 in
let temp_94:u32 := freevar1:u32 + 1:u32 in
let notpost:bool :=
                     ~(freevar1:u32 * freevar1:u32 $<= pvalue:u32 &
                      pvalue:u32 $< temp_94:u32 * temp_94:u32)
                     in
let temp_101:u32 := R_ESP:u32 + 0x1c:u32 in
let mem_102:?u32 :=
                     mem_47_78:?u32 with [temp_101:u32, e_little]:u32 =
                     freevar1:u32 in
let R_EAX_75:u32 := mem_102:?u32[temp_101:u32, e_little]:u32 in
let wp3:bool :=
                 0:u32 $<= R_EAX_75:u32 &
                 R_EAX_75:u32 * R_EAX_75:u32 * R_EAX_75:u32 * R_EAX_75:u32 $<=
                 param:u32 in
let goal:bool := sqrtpre:bool & (notpost:bool | wp3:bool) in goal:bool
goal:bool = abspre & (notabspost | wp2subst)


We have the final WP in main1.stp