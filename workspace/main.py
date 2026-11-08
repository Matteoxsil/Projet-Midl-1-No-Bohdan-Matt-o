from datastructs import *
from codageRegle import *
from tests import *

test_general()

p, q=Var("p"), Var("q")

exemplesSeqs = [Seq([p], p), Seq([Not(Impl(p, q))], And(p, Not(q))), Seq([p], q)]

print("------ Exemples ------")
for seq in exemplesSeqs:
    if prove_seq(seq) == [[]]:
        print(seq, "prouvable")
    else:
        print(seq, "non prouvable")