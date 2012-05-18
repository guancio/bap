#!/usr/bin/python

data = open("sqrt.il").read()
pos = data.rfind("R_EAX:u32 =")

before = data[:pos]
after = data[pos:].split("\n")

res = before + after[0] + "\n"
res += "goal:bool = R_EAX:u32>=0:u32\n"
res += "\n".join(after[1:])

open("sqrt.il", "w").write(res)
