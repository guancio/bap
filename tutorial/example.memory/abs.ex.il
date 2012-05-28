param:u32 = mem:?u32[R_ESP:u32+4:u32, e_little]:u32
oldmem:?u32 = mem:?u32
precondition:bool = (param $> 0x80000000:u32)
oldESP:u32 = R_ESP:u32


addr 0x0 @asm "push   %ebp"
label pc_0x0
t:u32 = R_EBP:u32
R_ESP:u32 = R_ESP:u32 - 4:u32
mem:?u32 = mem:?u32 with [R_ESP:u32, e_little]:u32 = t:u32
addr 0x1 @asm "mov    %esp,%ebp"
label pc_0x1
R_EBP:u32 = R_ESP:u32
addr 0x3 @asm "cmpl   $0x0,0x8(%ebp)"
label pc_0x3
t_69:u32 = mem:?u32[R_EBP:u32 + 8:u32, e_little]:u32 - 0:u32
R_CF:bool = mem:?u32[R_EBP:u32 + 8:u32, e_little]:u32 < 0:u32
R_AF:bool =
  0x10:u32 ==
  (0x10:u32 & (t_69:u32 ^ mem:?u32[R_EBP:u32 + 8:u32, e_little]:u32 ^ 0:u32))
R_OF:bool =
  high:bool((mem:?u32[R_EBP:u32 + 8:u32, e_little]:u32 ^ 0:u32) &
            (mem:?u32[R_EBP:u32 + 8:u32, e_little]:u32 ^ t_69:u32))
R_PF:bool =
  ~low:bool(t_69:u32 >> 7:u32 ^ t_69:u32 >> 6:u32 ^ t_69:u32 >> 5:u32 ^
            t_69:u32 >> 4:u32 ^ t_69:u32 >> 3:u32 ^ t_69:u32 >> 2:u32 ^
            t_69:u32 >> 1:u32 ^ t_69:u32)
R_SF:bool = high:bool(t_69:u32)
R_ZF:bool = 0:u32 == t_69:u32
addr 0x7 @asm "jns    0x0000000000000010"
label pc_0x7
cjmp ~R_SF:bool, 0x10:u32, "nocjmp0"
label nocjmp0
addr 0x9 @asm "mov    0x8(%ebp),%eax"
label pc_0x9
R_EAX:u32 = mem:?u32[R_EBP:u32 + 8:u32, e_little]:u32
addr 0xc @asm "neg    %eax"
label pc_0xc
T_32t2:u32 = R_EAX:u32
T_32t3:u32 = 0:u32 - T_32t2:u32
R_EAX:u32 = T_32t3:u32
/*eflags thunk: sub*/
T_0:u32 = 0:u32 - T_32t2:u32
R_CF:bool = 0:u32 < T_32t2:u32
T_1:u8 = low:u8(T_0:u32)
R_PF:bool =
  ~low:bool(T_1:u8 >> 7:u8 ^ T_1:u8 >> 6:u8 ^
            (T_1:u8 >> 5:u8 ^ T_1:u8 >> 4:u8) ^
            (T_1:u8 >> 3:u8 ^ T_1:u8 >> 2:u8 ^ (T_1:u8 >> 1:u8 ^ T_1:u8)))
R_AF:bool = 1:u32 == (0x10:u32 & (T_0:u32 ^ (0:u32 ^ T_32t2:u32)))
R_ZF:bool = T_0:u32 == 0:u32
R_SF:bool = 1:u32 == (1:u32 & T_0:u32 >> 0x1f:u32)
R_OF:bool =
  1:u32 == (1:u32 & ((0:u32 ^ T_32t2:u32) & (0:u32 ^ T_0:u32)) >> 0x1f:u32)
addr 0xe @asm "jmp    0x0000000000000013"
label pc_0xe
jmp 0x13:u32
addr 0x10 @asm "mov    0x8(%ebp),%eax"
label pc_0x10
R_EAX:u32 = mem:?u32[R_EBP:u32 + 8:u32, e_little]:u32
addr 0x13 @asm "pop    %ebp"
label pc_0x13
R_EBP:u32 = mem:?u32[R_ESP:u32, e_little]:u32
R_ESP:u32 = R_ESP:u32 + 4:u32
addr 0x14 @asm "ret    "
label pc_0x14
ra:u32 = mem:?u32[R_ESP:u32, e_little]:u32
R_ESP:u32 = R_ESP:u32 + 4:u32
/*jmp ra:u32 @str "ret"*/



goal:bool = (~precondition | 
	(
	(R_EAX:u32 $>= 0:u32) & (R_EAX:u32 $<= param | R_EAX:u32 $<= -param) &
	(((freememloc:u32 == oldESP-4:u32) | (freememloc:u32 == oldESP-3:u32) | (freememloc:u32 == oldESP-2:u32) | (freememloc:u32 == oldESP-1:u32)) | mem[freememloc:u32, e_little]:u8 == oldmem[freememloc, e_little]:u8)
     )
)
