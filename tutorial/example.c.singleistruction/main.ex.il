precondition:bool = (R_EAX:u32 $> 0:u32)

addr 0x0 @asm "add    $0x1,%eax"
label pc_0x0
t:u32 = R_EAX:u32
R_EAX:u32 = R_EAX:u32 + 1:u32
R_CF:bool = R_EAX:u32 < t:u32
R_AF:bool = 0x10:u32 == (0x10:u32 & (R_EAX:u32 ^ t:u32 ^ 1:u32))
R_OF:bool = high:bool((t:u32 ^ -2:u32) & (t:u32 ^ R_EAX:u32))
R_PF:bool =
  ~low:bool(R_EAX:u32 >> 7:u32 ^ R_EAX:u32 >> 6:u32 ^ R_EAX:u32 >> 5:u32 ^
            R_EAX:u32 >> 4:u32 ^ R_EAX:u32 >> 3:u32 ^ R_EAX:u32 >> 2:u32 ^
            R_EAX:u32 >> 1:u32 ^ R_EAX:u32)
R_SF:bool = high:bool(R_EAX:u32)
R_ZF:bool = 0:u32 == R_EAX:u32

goal:bool = (~precondition)|(R_EAX $> 0:u32)

