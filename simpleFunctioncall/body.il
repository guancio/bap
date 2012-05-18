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