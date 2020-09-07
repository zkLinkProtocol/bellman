high = 0x2f6


def ror(n,rotations,width=32):
    return (2^width-1)&(n>>rotations|n<<(width-rotations))


# print bin(high) + bin(mid) + bin(low)
# print bin(full)

res = 0
acc = 1
base = 4
input = ror(full, 7)

c0 = 0x9a6
c1 = 0x695
c2 = 0x8ac
c3 = 0x5c9
c4 = 0x126
c5 = 0x6
full_c = 0x61265c98ac6959a6

res = 0
base = 4^6
acc = 1
for i in [c0, c1, c2, c3, c4, c5]:
    res += i * acc
    acc *= base
    
print hex(res)

print bin(0x6c)