addr 0x14 @asm "mov    %eax,0x18(%esp)"
label pc_0x14
mem:?u32 = mem:?u32 with [R_ESP:u32 + 0x18:u32, e_little]:u32 = R_EAX:u32
addr 0x18 @asm "mov    0x18(%esp),%eax"
label pc_0x18
R_EAX:u32 = mem:?u32[R_ESP:u32 + 0x18:u32, e_little]:u32
addr 0x1c @asm "mov    %eax,(%esp)"
label pc_0x1c
mem:?u32 = mem:?u32 with [R_ESP:u32, e_little]:u32 = R_EAX:u32

goal:bool =
let sqrtparam:u32 := mem:?u32[R_ESP:u32, e_little]:u32 in
let sqrtpre:bool := sqrtparam $>= 0:u32 in
let sqrtpost:bool := (freevar1:u32 * freevar1 $<= sqrtparam) &
   ((freevar1+1:u32) * (freevar1+1:u32) $> sqrtparam)  &
   freevar1 $>= 0:u32 &
   freevar1 $<= 0x0000b504:u32
   in
let wp3:bool := (
  let R_EAX:u32 := freevar1 in
  let temp:u32 := R_ESP:u32 + 0x1c:u32 in
  let mem:?u32 := mem:?u32 with [temp:u32, e_little]:u32 = R_EAX:u32 in
  let R_EAX_75:u32 := mem:?u32[temp:u32, e_little]:u32 in
  let goal:bool :=
                  0:u32 $<= R_EAX_75:u32 &
                  R_EAX_75:u32 * R_EAX_75:u32 * R_EAX_75:u32 * R_EAX_75:u32 $<=
                  param:u32 * param:u32 in
  goal:bool
) in
(sqrtpre) & ((~ sqrtpost) | wp3)