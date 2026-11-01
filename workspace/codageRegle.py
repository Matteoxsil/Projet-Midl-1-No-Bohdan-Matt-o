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

##rules 
s_t_rule = Rule("s_t", s_t_appcond, s_t_action)
a_and_t_rule = Rule("a_and_t", a_and_t_appcond, a_and_t_action)
a_or_t_rule = Rule("a_and_t", a_or_t_appcond, a_or_t_action)