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

goal:bool = R_EAX $>=0:u32 & R_EAX*R_EAX*R_EAX*R_EAX $<= param:u32