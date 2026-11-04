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
    
## a_and_t
def a_and_t_appcond (fs: list[Form], s: Seq) -> bool:
    match (fs , s):
        case ([ And(a,b)], Seq(g,FF() )):
            return ( not_both_in (a, b, g))     
                #TODO ce ne serait pas not(a) et not(b)? Puisque la regle est applicable ssi a and b sont dans g
                ## reponse : ça c'est donné dans le sujet, et l'explication du pourquoi pas not both in et pas none in est que on acquiert de l'info même si il n'y a que un des deux dedans
                ##exemple, si on a A et B qui appartient a gamma, alors, même si on a deja A qui appartient a gamma, on gagne de l'information en ajoutant B a gamma
                
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
                    #TODO ce ne serait pas none_in(a,b,g)? Puisque la regle est applicable ssi not(a) and not(b) sont dans g
                    # va voir la réponse que j'ai faite sur a_and_t, et dis moi si ça te convainc
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
                return (not (Impl(a,b) in g))
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
a_and_t_rule = Rule("a_and_t", a_and_t_appcond, a_and_t_action)
a_or_t_rule = Rule("a_and_t", a_or_t_appcond, a_or_t_action)

b_and_t_rule = Rule("b_and_t", b_and_t_appcond, b_and_t_action)
b_or_t_rule = Rule("b_and_t", b_or_t_appcond, b_or_t_action)
b_impl_t_rule = Rule("b_impl_t",b_impl_t_appcond,b_impl_t_action)
