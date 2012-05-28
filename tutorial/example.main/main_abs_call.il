goal:bool =
 let absparam:u32 := mem:?u32[R_ESP:u32, e_little]:u32 in
 let abspre:bool := absparam $> 0x80000000:u32 in
 let abspost:bool := (freevar2:u32 $>=0:u32) &
                     ((freevar2 $<= absparam) | (freevar2 $<= ~absparam)) in
let wp1b:bool :=
 (
    let R_EAX:u32 := freevar2 in
    let mem_47:?u32 := mem in
    let temp:u32 := R_ESP:u32 + 0x18:u32 in
    let mem:?u32 := mem_47:?u32 with [temp:u32, e_little]:u32 = R_EAX:u32 in
    let R_EAX_85:u32 := mem:?u32[temp:u32, e_little]:u32 in
    let mem_86:?u32 := mem:?u32 with [R_ESP:u32, e_little]:u32 = R_EAX_85:u32 in
    let sqrtparam:u32 := mem_86:?u32[R_ESP:u32, e_little]:u32 in
    let sqrtpre:bool := 0:u32 $<= sqrtparam:u32 in
    let temp_92:u32 := freevar1:u32 + 1:u32 in
    let sqrtpost:bool :=  
    freevar1:u32 * freevar1:u32 $<= sqrtparam:u32 &
    sqrtparam:u32 $< temp_92:u32 * temp_92:u32 &
    0:u32 $<= freevar1:u32 & freevar1:u32 $<= 0xb504:u32 in
    let temp_102:u32 := R_ESP:u32 + 0x1c:u32 in
    let mem_103:?u32 :=  
    mem_86:?u32 with [temp_102:u32, e_little]:u32 =
    freevar1:u32 in
    let R_EAX_75:u32 := mem_103:?u32[temp_102:u32, e_little]:u32 in
    let goal:bool :=  
    0:u32 $<= R_EAX_75:u32 &
    R_EAX_75:u32 * R_EAX_75:u32 * R_EAX_75:u32 * R_EAX_75:u32 $<=
    param:u32 * param:u32 in
    let goal_114:bool := sqrtpre:bool & (~sqrtpost:bool | goal:bool) in
    goal_114:bool
 )
 in  
 (abspre & ((~abspost) | wp1b:bool))
