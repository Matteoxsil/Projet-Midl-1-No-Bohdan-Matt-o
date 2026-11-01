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

## a_and_t
def a_and_t_appcond (fs: list[Form], s: Seq) -> bool:
    match (fs , s):
        case ([ And(a,b)], Seq(g,False )):
            return ( not_both_in (a, b, g))
        case _:
            return (False)

def a_and_t_action(fs:list[Form], s:Seq) -> list[Seq]:
    match(fs, s):
        case([And(a,b)], Seq(g,False )):
            return ([ Seq( insert_forms(insert_forms (g, a), b), FF ())])
        case _:
            return ([])

##a_or_t
## c'est équivalent a a_and_t donc c'est la même chose avec les not
def a_or_t_appcond(fs:list[Form], s:Seq) -> bool:
     match (fs , s):
            case ([ Not(Or(a,b))], Seq(g,False )):
                return ( not_both_in (Not(a), Not(b), g))
            case _:
                return (False)
def a_or_t_action(fs:list[Form], s:Seq) -> list[Seq]:
    match(fs, s):
        case([Not(Or(a,b))], Seq(g,False )):
            return ([ Seq( insert_forms(insert_forms (g, Not(a)), Not(b)), FF ())])
        case _:
            return ([])


#b_or_t
##pour la terminairson (à mettre dans le rapport), il faut appliquer
##la règle ssi ni a ni b n'appartient à gamma
##car sinon on a a ou b, mais si on a deja soit a soit b, alors on a évidemment
##a ou b
def b_or_t_appcond(fs:list[Form], s:Seq) -> bool:
     match (fs , s):
            case ([ Or(a,b)], Seq(g,False )):
                return ( none_in(a, b, g))
            case _:
                return (False)
         
def b_or_t_action(fs:list[Form], s:Seq) -> list[Seq]:
    match(fs, s):
        case([Or(a,b)], Seq(g,False )):
            return ([ Seq(insert_forms (g, a), FF ()),Seq(insert_forms (g, b), FF ()) ])
        case _:
            return ([])

##b_and_t
##les conditions sont les mêmes que pour b_or_t car la règle est équivalent
def b_and_t_appcond(fs:list[Form], s:Seq) -> bool:
     match (fs , s):
            case ([ Not(And(a,b))], Seq(g,False )):
                return ( none_in(Not(a), Not(b), g))
            case _:
                return (False)
         
def b_and_t_action(fs:list[Form], s:Seq) -> list[Seq]:
    match(fs, s):
        case([Not(And(a,b))], Seq(g,False )):
            return ([ Seq(insert_forms (g, Not(a)), FF ()),Seq(insert_forms (g, Not(b)), FF ()) ])
        case _:
            return ([])

# b_impl_t_action
##a -> b = non a ou b, donc b_impl_t est équivalent a b_or_t, donc les
## conditions sont les mêmes
def b_impl_t_appcond(fs:list[Form], s:Seq) -> bool:
     match (fs , s):
            case ([ Impl(a,b)], Seq(g,False )):
                return ( none_in(Not(a), b, g))
            case _:
                return (False)
         
def b_impl_t_action(fs:list[Form], s:Seq) -> list[Seq]:
    match(fs, s):
        case([Impl(a,b)], Seq(g,False )):
            return ([ Seq(insert_forms (g, Not(a)), FF ()),Seq(insert_forms (g, b), FF ()) ])
        case _:
            return ([])
##rules 
s_t_rule = Rule("s_t", s_t_appcond, s_t_action)
a_and_t_rule = Rule("a_and_t", a_and_t_appcond, a_and_t_action)
a_or_t_rule = Rule("a_and_t", a_or_t_appcond, a_or_t_action)

##rules 
s_t_rule = Rule("s_t", s_t_appcond, s_t_action)
a_and_t_rule = Rule("a_and_t", a_and_t_appcond, a_and_t_action)
a_or_t_rule = Rule("a_and_t", a_or_t_appcond, a_or_t_action)
