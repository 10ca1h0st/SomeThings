from heapq import heapify,heappush,heappop
from itertools import count
def huffman(seq,frq):
    num=count()
    trees=list(zip(frq,num,seq))
    #(frq,num,seq)代表(概率,编号,树)
    #编号是用来在概率相同的情况下区别两棵树的
    heapify(trees)
    
    while len(trees)>1:
        print(trees)
        print("------")
        fa,_,a=heappop(trees)
        fb,_,b=heappop(trees)
        print(a)
        print(b)
        print("------")
        n=next(num)
        heappush(trees,(fa+fb,n,[a,b]))
        #heapify(trees)
    return trees

code_map={}
def codes(tree,prefix=""):
    if tree in list('abcdefghi'):
        code_map[tree]=prefix
        return
    for bit,child in zip('01',tree):
        codes(child,prefix+bit)