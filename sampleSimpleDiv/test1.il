addr 0x0 @asm "idivl  0x18(%ebp)"
label pc_0x0
x:u32 = R_EBP:u32
x:u32 = x:u32 - 0x5:u32
R_EBP:u32 = x:u32
goal:bool = R_EBP:u32 > 10:u32
