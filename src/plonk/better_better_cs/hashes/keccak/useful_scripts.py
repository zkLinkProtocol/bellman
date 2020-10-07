# p = 21888242871839275222246405745257275088548364400416034343698204186575808495617
# print 14^67 < p

table = [0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 0, 1, 1, 0, 1, 0]

def func(a, b, c, d, c1, c2, c3, c4):
    return c1 * a + c2 * b + c3* c + c4 * d


from itertools import product

def check(c1, c2, c3, c4):
    map = {}
    for it in product(xrange(2), repeat=4):
        idx = 8 * it[0] + 4 * it[1] + 2 * it[2] + it[3] 
        num = func(it[0], it[1], it[2], it[3], c1, c2, c3, c4)
        if num in map:
            value = map[num]
            if value != table[idx]:
                return false
        else:
             map[num] = table[idx]
    return true


for it in product(xrange(1, 4), repeat=4):
    if check(it[0], it[1], it[2], it[3]):
        print it
        
print "final"