from datastructs import *
from codageRegle import *

##Fonctions de test.
def test_insert_forms():
    """ Tests de insert_forms """
    print("Testing insert_forms...")
    a, b = Var('a'), Var('b')
    assert (insert_forms([FF()], And(Var('a'), Var('b')))) == [FF(), And(Var('a'), Var('b'))]
    assert insert_forms([a], b) == [a, b]
    assert insert_forms([a, b], b) == [a, b] #pas de doublons
    g = [a]
    insert_forms(g, b) == [a, b]
    assert g == [a]                          # g n'est pas modifiée
    print("------All tests OK------\n")


def test_next_proof_state():
    """ Tests de next_proof_state (ProofStateV0)"""

    print("Testing next_proof_state...")
    a,b,c=Var("a"),Var("b"),Var("c")
    
    #test de sequent avec s_t
    ps0=ProofStateV0([Seq([a],a)])
    ps1=next_proof_state(ps0)
    assert(ps1 == ([[Seq([a, Not(a)], FF())]]))

    #test de sequent avec n_t
    ps0=ProofStateV0([Seq([Not(Not(a))],FF())])
    ps1=next_proof_state(ps0)
    assert(ps1 == [[Seq([Not(Not(a)), a], FF())]])

    #test de sequent avec a_and_t.
    ps0=ProofStateV0([Seq([And(a,b)],FF())])
    ps1=next_proof_state(ps0)
    assert(ps1 == [[Seq([And(a, b), a, b], FF())]])

    #test de sequent avec a_or_t
    ps0=ProofStateV0([Seq([Not(Or(a,b))],FF())])
    ps1=next_proof_state(ps0)
    assert(ps1 == [[Seq([Not(Or(a,b)), Not(a), Not(b)], FF())]])

    #test de sequent avec a_impl_t
    ps0=ProofStateV0([Seq([Not(Impl(a,b))],FF())])
    ps1=next_proof_state(ps0)
    assert(ps1 == [[Seq([Not(Impl(a,b)), a, Not(b)], FF())]])

    #test de sequent avec b_and_t.
    ps0=ProofStateV0([Seq([Not(And(a,b))],FF())])
    ps1=next_proof_state(ps0)
    assert(ps1 == [[Seq([Not(And(a,b)), Not(a)], FF()), Seq([Not(And(a,b)), Not(b)], FF())]])

    #test de sequent avec b_or_t
    ps0=ProofStateV0([Seq([Or(a,b)],FF())])
    ps1=next_proof_state(ps0)
    assert(ps1 == [[Seq([Or(a,b), a], FF()), Seq([Or(a,b), b], FF())]])

    #test de sequent avec b_impl_t
    ps0=ProofStateV0([Seq([Impl(a,b)],FF())])
    ps1=next_proof_state(ps0)
    assert(ps1 == [[Seq([Impl(a,b), Not(a)], FF()), Seq([Impl(a,b), b], FF())]])

    #Test d'axiome AxC
    ps0=ProofStateV0([Seq([a, Not(a)], FF())])
    ps1=next_proof_state(ps0)
    assert(ps1 == [[]])

    #Test d'axiome AxF
    ps0=ProofStateV0([Seq([FF()], FF())])
    ps1=next_proof_state(ps0)
    assert(ps1 == [[]])

    #Tets de plusieurs règles
    ps0=ProofStateV0([Seq([And(a, b), Not(Not(c)),], FF())])
    ps1=next_proof_state(ps0)
    assert(ps1 == [[Seq([And(a, b), Not(Not(c)), a, b], FF())], [Seq([And(a, b), Not(Not(c)), c], FF())]])

    #Conditions d'arrêt
    ps0=ProofStateV0([Seq([And(a,b), a, b], FF())])
    ps1=next_proof_state(ps0)
    assert(ps1 == [])

    ps0=ProofStateV0([Seq([Not(And(a,b)), Not(a)],FF())])
    ps1=next_proof_state(ps0)
    assert(ps1 == [])

    #Test aucune règle
    ps0=ProofStateV0([Seq([a],FF())])
    ps1=next_proof_state(ps0)
    assert(ps1 == [])

    print("------All tests OK------\n")


def test_sol_proof_state():
    """ Tests de sol_proof_state (ProofStateV0)"""

    print("Testing sol_proof_state...")
    
    a,b=Var("a"),Var("b")
    #cas sans rien à prouver
    assert sol_proof_state([]) == True
    assert (sol_proof_state([Seq([a],FF())]) == False)
    assert (sol_proof_state([Seq([Not(Not(a))],FF())]) == False)
    assert (sol_proof_state([Seq([a], b)]) == False)
    print("------All tests OK------\n")


def test_prove_seq():
    """ Tests de prove_seq (ProofStateV0)"""
    print("Testing prove_seq...")
    a,b,c=Var("a"),Var("b"),Var("c")
    assert prove_seq(Seq([a], a)) == [[]] # [[]] signifie que le séquent est prouvable
    assert prove_seq(Seq([], Impl(a, a))) == [[]]
    assert prove_seq(Seq([Or(a, b)], a)) == []
    assert prove_seq(Seq([a], b)) == []   # []   signifie que le séquent est non prouvable
    print ("------All tests OK------\n")


def test_general():
    test_insert_forms()
    test_next_proof_state()
    test_sol_proof_state()
    test_prove_seq()
    print("Tout les tests ont reussis\n")

if __name__ == "__main__":
    test_general()