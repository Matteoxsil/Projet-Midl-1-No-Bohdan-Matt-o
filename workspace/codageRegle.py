from datastructs import *
from typing import TypeVar


def is_in(fs : list[Form], f:Form) -> bool:
    """ Teste si la formule f apprtient à la liste fs """
    for i in range(len(fs)):
        if fs[i] == f:
            return True
    return False

## fonction not_both_in(a ,b, g) qui correspond a
## - a n'appartient pas a gamma ou b n'appartient pas a gamma.

def not_both_in(a:Form, b:Form ,g:list[Form]) -> bool:
    """ Renvoie True si soit a ou b n'apprtient pas à gamma """
    return not is_in(g, a) or not is_in(g, b)


def none_in(a:Form, b:Form ,g:list[Form]) -> bool:
    """ Renvoie True si aucune de deux formules n'est présente """
    return not is_in(g,a) and not is_in(g,b)


## fonction insert_forms qui evite les doublons
def insert_forms(fs : list[Form], f:Form) -> list[Form]:
    """ Renvoie une nouvelle liste fs + f à la fin (pas de doublons) """
    if is_in(fs, f):
        return fs
    else:
        return fs + [f]

    
##règles 
def s_t_appcond (fs: list[Form], s: Seq) -> bool:
    """ Condition d'applicabilité de la règle (S) """
    match (fs , s):
        case ([], Seq(_,a)):
            return (a != FF ())
        case _:
            return(False)
        
        
def s_t_action (fs: list[Form], s: Seq) -> list[Seq ]:
    """ Action de la règle (S) """
    match (fs , s):
        case ([], Seq(g,a)):
            return ([ Seq( insert_forms (g, Not(a)), FF ())])
        case _:
            return ([])



def axc_t_appcond(fs:list[Form], s:Seq)->bool:
    """ Condition d'applicabilité de l'axiome (AxC)

        Les hypothèses contiennent A et ¬A, elles sont donc contradictoires
    """
    match (fs , s):
        case ([a], Seq(g,FF() )):
            return (Not(a) in g)
        case _:
            return (False)


def axc_t_action(fs:list[Form], s:Seq)->list[Seq]:
    """ Action de l'axiome (AxC): aucun séquent successeur (renvoie liste vide) """
    return []


def axf_t_appcond(fs:list[Form], s:Seq)->bool:
    """ Condition d'applicabilité de l'axiome (AxF) """
    match(fs, s):
        case ([], Seq(g, FF())):
            return (FF() in g)
        case _:
            return (False)

def axf_t_action(fs:list[Form], s:Seq)->list[Seq]:
    """ Action de l'axiome (AxF): aucun séquent successeur (renvoie liste vide) """
    return []


    
##La Negation: Not(Not(a)) donne a
def n_t_appcond (fs: list[Form], s: Seq) -> bool:
    """ Condition d'applicabilité de la règle (N) """
    match (fs , s):
        case ([Not(Not(a))], Seq(g,FF())):
            return (a not in g)
        case _:
            return(False)

        
def n_t_action (fs: list[Form], s: Seq) -> list[Seq ]:
    """ Action de la règle (N) """
    match (fs , s):
        case ([Not(Not(a))], Seq(g,FF() )):
            return ([ Seq( insert_forms (g, a), FF ())])
        case _:
            return ([])

        
## a_and_t
def a_and_t_appcond (fs: list[Form], s: Seq) -> bool:
    """ Condition d'applicabilité de la règle (a∧) """
    match (fs , s):
        case ([ And(a,b)], Seq(g,FF() )):
            return ( not_both_in (a, b, g))
        case _:
            return (False)


def a_and_t_action(fs:list[Form], s:Seq) -> list[Seq]:
    """ Action de la règle (a∧) """
    match(fs, s):
        case([And(a,b)], Seq(g,FF() )):
            return ([ Seq( insert_forms(insert_forms (g, a), b), FF ())])
        case _:
            return ([])

##a_or_t
## c'est équivalent a a_and_t donc c'est la même chose avec les not
def a_or_t_appcond(fs:list[Form], s:Seq) -> bool:
    """ Condition d'applicabilité de la règle (a∨) """
    match (fs , s):
        case ([ Not(Or(a,b))], Seq(g,FF() )):
            return ( not_both_in (Not(a), Not(b), g))
        case _:
            return (False)

        
def a_or_t_action(fs:list[Form], s:Seq) -> list[Seq]:
    """ Action de la règle (a∨) """
    match(fs, s):
        case([Not(Or(a,b))], Seq(g,FF() )):
            return ([ Seq( insert_forms(insert_forms (g, Not(a)), Not(b)), FF ())])
        case _:
            return ([])

        
##a_impl_t
def a_impl_t_appcond(fs:list[Form], s:Seq) -> bool:
    """ Condition d'applicabilité de la règle (a→) """
    match (fs , s):
        case ([ Not(Impl(a,b))], Seq(g,FF() )):
            return (not_both_in(a,Not(b),g))
        case _:
            return (False)

         
def a_impl_t_action(fs:list[Form], s:Seq) -> list[Seq]:
    """ Action de la règle (a→) """
    match(fs, s):
        case ([ Not(Impl(a,b))], Seq(g,FF() )):
            return ([ Seq( insert_forms(insert_forms (g, a), Not(b)), FF ())])
        case _:
            return ([])

#b_or_t
##pour la terminairson (à mettre dans le rapport), il faut appliquer
##la règle ssi ni a ni b n'appartient à gamma
##car sinon on a a ou b, mais si on a deja soit a soit b, alors on a évidemment
##a ou b
def b_or_t_appcond(fs:list[Form], s:Seq) -> bool:
    """ Condition d'applicabilité de la règle (b∨) """
    match (fs , s):
        case ([ Or(a,b)], Seq(g,FF() )):
            return ( none_in(a, b, g))
        case _:
            return (False)

         
def b_or_t_action(fs:list[Form], s:Seq) -> list[Seq]:
    """ Action de la règle (b∨) """
    match(fs, s):
        case([Or(a,b)], Seq(g,FF() )):
            return ([ Seq(insert_forms (g, a), FF ()),Seq(insert_forms (g, b), FF ()) ])
        case _:
            return ([])

##b_and_t
##les conditions sont les mêmes que pour b_or_t car la règle est équivalent
def b_and_t_appcond(fs:list[Form], s:Seq) -> bool:
    """ Condition d'applicabilité de la règle (b∧) """
    match (fs , s):
        case ([ Not(And(a,b))], Seq(g,FF() )):
            return ( none_in(Not(a), Not(b), g))
        case _:
            return (False)

         
def b_and_t_action(fs:list[Form], s:Seq) -> list[Seq]:
    """ Action de la règle (b∧) """
    match(fs, s):
        case([Not(And(a,b))], Seq(g,FF() )):
            return ([ Seq(insert_forms (g, Not(a)), FF ()),Seq(insert_forms (g, Not(b)), FF ()) ])
        case _:
            return ([])

# b_impl_t_action
##a -> b = non a ou b, donc b_impl_t est équivalent a b_or_t, donc les
## conditions sont les mêmes
def b_impl_t_appcond(fs:list[Form], s:Seq) -> bool:
    """ Condition d'applicabilité de la règle (b→) """
    match (fs , s):
        case ([ Impl(a,b)], Seq(g,FF() )):
            return ( none_in(Not(a), b, g))
        case _:
            return (False)

         
def b_impl_t_action(fs:list[Form], s:Seq) -> list[Seq]:
    """ Action de la règle (b→) """
    match(fs, s):
        case([Impl(a,b)], Seq(g,FF() )):
            return ([ Seq(insert_forms (g, Not(a)), FF ()),Seq(insert_forms (g, b), FF ()) ])
        case _:
            return ([])

        
##rules 
s_t_rule = Rule("s_t", s_t_appcond, s_t_action)
n_t_rule = Rule("n_t", n_t_appcond, n_t_action)
axc_t_rule = Rule("axc_t", axc_t_appcond, axc_t_action)
axf_t_rule = Rule("axf_t", axf_t_appcond, axf_t_action)
a_and_t_rule = Rule("a_and_t", a_and_t_appcond, a_and_t_action)
a_or_t_rule = Rule("a_or_t", a_or_t_appcond, a_or_t_action)
a_impl_t_rule = Rule("a_impl_t", a_impl_t_appcond,a_impl_t_action)
b_and_t_rule = Rule("b_and_t", b_and_t_appcond, b_and_t_action)
b_or_t_rule = Rule("b_or_t", b_or_t_appcond, b_or_t_action)
b_impl_t_rule = Rule("b_impl_t",b_impl_t_appcond,b_impl_t_action)

#listeRegleEtAxiomes n'est pas specifique à une fonction donc variable globale
listeRegleEtAxiomes = [s_t_rule, n_t_rule, axc_t_rule, axf_t_rule, 
                       a_and_t_rule, a_or_t_rule, a_impl_t_rule, 
                       b_and_t_rule, b_or_t_rule, b_impl_t_rule ] 


#petite fonction pour mieux voir ce qu'on fait et pouvoir etudier comment fonctionne un code
def affichage_proofstate(ps:ProofStateV0):
    for s in ps:
        print(s)
        print("="*20)

def affichage_states(state:list[ProofStateV0]):
    for ps in state:
        affichage_proofstate(ps)

def next_proof_state(ps : ProofStateV0) -> list[ProofStateV0]:
    """ Calcule les états de preuve successeurs de ps.

        ps: état de preuve non vide (liste des séquents qui restent à prouver)

        Pour chaque règle et chaque formule cible possible de ps[0], 
        si la règle est applicable, on construit un nouvel état

        Renvoie la liste des états. 
        Une liste vide signifie qu'aucune règle n'est applicable au premier séquent
    """
    #on choisi donc le premier sequent
    sequentEtudie = ps[0]

    nouvelleEtatPreuve = list() #liste de proostatesV0

    # fs = []
    if s_t_rule.appcond([], sequentEtudie):
        nouvelleEtatPreuve.append(s_t_rule.action([], sequentEtudie) + ps[1:])

    if axf_t_rule.appcond([], sequentEtudie):
        nouvelleEtatPreuve.append(axf_t_rule.action([], sequentEtudie) + ps[1:])

    for hyp in sequentEtudie.hyps:     
        for regle in listeRegleEtAxiomes:
            if regle.appcond([hyp], sequentEtudie):
                # Le premier séquent est remplacé par des séquents successeurs
                # Aucun pour un axiome: il disparaît, les autres sont conservés
                nouvelleEtatPreuve.append(regle.action([hyp], sequentEtudie) + ps[1:]) 

    return nouvelleEtatPreuve


PS = TypeVar("PS")
def dfs (nexts: Callable [[PS], list[PS]],sol: Callable [[PS], bool],states: list[PS]) -> list[PS]:
    #affichage_states(states)
    
    if states == []:
        return ([])
    else:
        if sol(states[0]):
            return [states[0]]
            # si vous souhaitez continuer la recherche , decommentez :
            # return [states [0]] + dfs(nexts , sol , nexts(states [0]) + states [1:])
        else:
            return dfs(nexts , sol , nexts(states [0]) + states [1:])
        

def sol_proof_state (ps: ProofStateV0) -> bool:
    """ Renvoie True si l'état de preuve est vide: tous les séquents ont été fermés par un axiome, la preuve est terminée """
    if len(ps) != 0:
        return False
    else:
        return True

def init_state(seq: Seq) -> list[ProofStateV0]:
    """ Construit la liste d'états initiale dfs à partir du séquent à prouver """
    return [[seq]]

def prove_seq(seq: Seq) -> list[ProofStateV0]:
    """ Recherche une preuve de seq en utilisant dfs """
    return dfs(next_proof_state, sol_proof_state, init_state(seq))

