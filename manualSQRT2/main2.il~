addr 0x14 @asm "mov    %eax,0x18(%esp)"
label pc_0x14
mem:?u32 = mem:?u32 with [R_ESP:u32 + 0x18:u32, e_little]:u32 = R_EAX:u32
addr 0x18 @asm "mov    0x18(%esp),%eax"
label pc_0x18
R_EAX:u32 = mem:?u32[R_ESP:u32 + 0x18:u32, e_little]:u32
addr 0x1c @asm "mov    %eax,(%esp)"
label pc_0x1c
mem:?u32 = mem:?u32 with [R_ESP:u32, e_little]:u32 = R_EAX:u32

paddr:u32 = mem:?u32[R_ESP:u32, e_little]:u32
pvalue:u32 = mem:?u32[paddr:u32, e_little]:u32
sqrtpre:bool = pvalue $>= 0:u32
notpost:bool = ~(freevar1:u32*freevar1 $<= pvalue & (freevar1+1:u32)*(freevar1+1:u32) $> pvalue)
wpsubs:bool = let R_EAX:u32:= freevar1 in
let temp:u32 := R_ESP:u32 + 0x1c:u32 in
let mem:?u32 := mem_47:?u32 with [temp:u32, e_little]:u32 = R_EAX:u32 in
let R_EAX_75:u32 := mem:?u32[temp:u32, e_little]:u32 in
let wp3:bool :=
                  0:u32 $<= R_EAX_75:u32 &
                  R_EAX_75:u32 * R_EAX_75:u32 * R_EAX_75:u32 * R_EAX_75:u32 $<=
                  param:u32 in wp3:bool
goal:bool = sqrtpre & (notpost | wpsubs)
