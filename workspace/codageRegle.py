from datastructs import *



def is_in(fs : list[Form], f:Form) -> bool:
    for i in range(len(fs)):
        if fs[i] == f:
            return True
    return False

## fonction not both in(a ,b, g) qui correspond a
## - a n'appartient pas a gamma ou b n'appartient pas a gamma.

def not_both_in(a:Form, b:Form ,g:list[Form]) -> bool:
    return not is_in(g, a) or not is_in(g, b)

def none_in(a:Form, b:Form ,g:list[Form]) -> bool:
    return not is_in(g,a) and not is_in(g,b)


## fonction insert_forms qui evite les doublons
def insert_forms(fs : list[Form], f:Form) -> list[Form]:
    if is_in(fs, f):
        return fs
    else:
        return fs.append(f)
    
##règles 
def s_t_appcond (fs: list[Form], s: Seq) -> bool:
    match (fs , s):
        case ([], Seq(_,a)):
            return (a != FF ())
        case _:
            return(False)
        
def s_t_action (fs: list[Form], s: Seq) -> list[Seq ]:
    match (fs , s):
        case ([], Seq(g,a)):
            return ([ Seq( insert_forms (g, [Not(a)]), FF ())])
        case _:
            return ([])
#concernant ça, c'est l'axiome AxC donc pour moi utile car elle permet de terminer une preuve (sans ça on a rien pour le faire)
#après niveau implémentation jsp encore trop, je suis en train de faire la fonction next proof state donc je ferai un retour plus tard
##Axiome Complementaire/contradiction(si g donne a et non(a) alors g donne false)
# ##TODO à discuter si necessaire: different des autres regles, semble inutile
# def contradiction_appcond(fs:list[Form], s:Seq)->bool:
#     match (fs , s):
#             case ([a], Seq(g,FF() )):
#                 return (not(a) in g)
#             case _:
#                 return (False)



##par contre sur cette partie là c'est pas bon, l'axiome n'ajoute aucune formule au séquent
#il ne faut pas ajouter not(a)
#par contre qu'est ce que doit renvoyer la fonction cette fonction je ne sais pas
#en tout cas il ne faut pas rajouter de nouvelle hyp pour suite a un axiome
# def contradiction_action(fs:list[Form], s:Seq)->list[Seq]:
#     match (fs , s):
#             case ([a], Seq(g,FF() )):
#                 return ([Seq(insert_forms(g,not(a)),FF())])
#             case _:
#                 return ([])
    
##La Negation: Not(Not(a)) donne a
def n_t_appcond (fs: list[Form], s: Seq) -> bool:
    match (fs , s):
        case ([Not(Not(a))], Seq(g,FF())):
            return (a not in g)
        case _:
            return(False)
        
def n_t_action (fs: list[Form], s: Seq) -> list[Seq ]:
    match (fs , s):
        case ([Not(Not(a))], Seq(g,FF() )):
            return ([ Seq( insert_forms (g, a), FF ())])
        case _:
            return ([])
        
## a_and_t
def a_and_t_appcond (fs: list[Form], s: Seq) -> bool:
    match (fs , s):
        case ([ And(a,b)], Seq(g,FF() )):
            return ( not_both_in (a, b, g))
        case _:
            return (False)

def a_and_t_action(fs:list[Form], s:Seq) -> list[Seq]:
    match(fs, s):
        case([And(a,b)], Seq(g,FF() )):
            return ([ Seq( insert_forms(insert_forms (g, a), b), FF ())])
        case _:
            return ([])

##a_or_t
## c'est équivalent a a_and_t donc c'est la même chose avec les not
def a_or_t_appcond(fs:list[Form], s:Seq) -> bool:
     match (fs , s):
            case ([ Not(Or(a,b))], Seq(g,FF() )):
                return ( not_both_in (Not(a), Not(b), g))
            case _:
                return (False)
def a_or_t_action(fs:list[Form], s:Seq) -> list[Seq]:
    match(fs, s):
        case([Not(Or(a,b))], Seq(g,FF() )):
            return ([ Seq( insert_forms(insert_forms (g, Not(a)), Not(b)), FF ())])
        case _:
            return ([])
##a_impl_t
def a_impl_t_appcond(fs:list[Form], s:Seq) -> bool:
     match (fs , s):
            case ([ Not(Impl(a,b))], Seq(g,FF() )):
                return (not_both_in(a,not(b),g))
            case _:
                return (False)
def a_impl_t_action(fs:list[Form], s:Seq) -> list[Seq]:
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
     match (fs , s):
            case ([ Or(a,b)], Seq(g,FF() )):
                return ( none_in(a, b, g))
            case _:
                return (False)
         
def b_or_t_action(fs:list[Form], s:Seq) -> list[Seq]:
    match(fs, s):
        case([Or(a,b)], Seq(g,FF() )):
            return ([ Seq(insert_forms (g, a), FF ()),Seq(insert_forms (g, b), FF ()) ])
        case _:
            return ([])

##b_and_t
##les conditions sont les mêmes que pour b_or_t car la règle est équivalent
def b_and_t_appcond(fs:list[Form], s:Seq) -> bool:
     match (fs , s):
            case ([ Not(And(a,b))], Seq(g,FF() )):
                return ( none_in(Not(a), Not(b), g))
            case _:
                return (False)
         
def b_and_t_action(fs:list[Form], s:Seq) -> list[Seq]:
    match(fs, s):
        case([Not(And(a,b))], Seq(g,FF() )):
            return ([ Seq(insert_forms (g, Not(a)), FF ()),Seq(insert_forms (g, Not(b)), FF ()) ])
        case _:
            return ([])

# b_impl_t_action
##a -> b = non a ou b, donc b_impl_t est équivalent a b_or_t, donc les
## conditions sont les mêmes
def b_impl_t_appcond(fs:list[Form], s:Seq) -> bool:
     match (fs , s):
            case ([ Impl(a,b)], Seq(g,FF() )):
                return ( none_in(Not(a), b, g))
            case _:
                return (False)
         
def b_impl_t_action(fs:list[Form], s:Seq) -> list[Seq]:
    match(fs, s):
        case([Impl(a,b)], Seq(g,FF() )):
            return ([ Seq(insert_forms (g, Not(a)), FF ()),Seq(insert_forms (g, b), FF ()) ])
        case _:
            return ([])
##rules 
s_t_rule = Rule("s_t", s_t_appcond, s_t_action)
n_t_rule = Rule("n_t", n_t_appcond, n_t_action)
#Place pour axC p eventuel
a_and_t_rule = Rule("a_and_t", a_and_t_appcond, a_and_t_action)
a_or_t_rule = Rule("a_and_t", a_or_t_appcond, a_or_t_action)
a_impl_t_rule = Rule("a_impl_t", a_impl_t_appcond,a_impl_t_action)
b_and_t_rule = Rule("b_and_t", b_and_t_appcond, b_and_t_action)
b_or_t_rule = Rule("b_and_t", b_or_t_appcond, b_or_t_action)
b_impl_t_rule = Rule("b_impl_t",b_impl_t_appcond,b_impl_t_action)


##4.3
##alors proposition, pour les axiomes, le renvoie sera une liste vide
##de cet façon on comprend que le séquent est resolu
##si vous avez d'autres idées vous pouvez les implémenter, on peut en discuter etc
#mais étant donné que les axiomes n'ajoute rien a l'ensemble des hypothèse...

#edit : a priori de ce que je vois dans le sujet, les axiomes suprimesnt le sequent résolu de l'état de preuve 
#je ne sais pas encore si on peut le coder dans l'implémentation des axiomes ou si il faut le faire dans cette fonction
#si jamais on ne peut pas le faire dans l'axiome
#il faut juste rajouter après le if regle.appcond(...) un if regle not in listeAxiomes then suite du code classique,
##le sinon etant on ne le met pas dans le nouvel etat de preuve, donc ça correspond a un rien
def next_proof_state(ps : ProofStateV0) -> list[ProofStateV0]:
    #on choisi donc le premier sequent
    sequentEtudie = ps[0]
    #j'ai un doute sur si on peut utiliser Calculus au lieu de faire une liste de règle a la main
    ##dans le doute j'ai fait ça
    listeRegleEtAxiomes = [s_t_rule,a_and_t_rule, a_or_t_rule ] #à remplir quand toutes les règles seront codées
    nouvelleEtatPreuve = list() #liste de proostatesV0
    ##jsp si on le garde ça, ou si juste le proofstate contient une close vide
    #jsp si ça marche, si c'ets nécéssaire a voir au moment du test
    if s_t_rule.appcond([], sequentEtudie):
        nouvelleEtatPreuve.append(s_t_rule.action([], sequentEtudie))

    for hyp in sequentEtudie.concl:
            
        for regle in listeRegleEtAxiomes:
            if regle.appcond([hyp], sequentEtudie):
                nouvelleEtatPreuve.append(regle.action([hyp], sequentEtudie))

    return nouvelleEtatPreuve

def test():
    #test de sequent avec a_and_t. Ne fonctionne pas, on la reverras
    a,b,c=Var("a"),Var("b"),Var("c")
    ps0=ProofStateV0([Seq([And(a,b)],FF())])
    ps1=next_proof_state(ps0)
    print(ps1)

#test()