import z3

#region Z3-specific funtions
def createZ3Vars(input_list, num_holes):
    z3vars=[] #2D list of holes and possibilities for each hole
    for h in range(num_holes):
        hole_possibilities=[]
        for i in range(len(input_list)):
            # print(h,i)
            hole_possibilities.append(z3.Bool(str(h)+str(i))) # z3vars[h][i] = z3.Bool(str(h)+str(i)) #creating bools to use "and, not, or"
        z3vars.append(hole_possibilities)
    return z3vars

def Checksat(_solver, z3vars):
    if _solver.check() == z3.sat:
        mod = _solver.model()
        #print(mod) #prints unsorted in relation to inputs, so using evaluate to print result according to input:
        res = [[mod.evaluate(z3vars[i][j]) for j in range(len(z3vars[0])) ] for i in range(len(z3vars)) ]
        print(res)
    else:
        print("No solution")

#region Constraints
#NOTE: Must create rules up to num_holes-1 :). With more experience you can automate these rule creations 
def rule_OneCorrect_WrongPlace(input_string):
    pass
def rule_OneCorrect_RightPlace(input_string):
    pass
def rule_TwoCorrect_WrongPlace(input_string):
    pass
def rule_TwoCorrect_RightPlace(input_string):
    pass
def rule_NothingCorrect(input_string):
    pass
#endregion
#endregion

if __name__=="__main__":
    print("hello")

    #region Inputs
    input_list = ['0','1','2'] #possible inputs (pigeons)
    num_holes = 3
    #endregion

    mysolver = z3.Solver()

    #creating z3 inputs. Let a boolean variable v(x,y) denote that hole x has input y
    z3vars=createZ3Vars(input_list, num_holes) #2D list of holes and possibilities for each hole
    print(z3vars)


    #region Clauses
    #Clause 1: all holes must have an input
    #For each posisble input in a hole, only one must be true and the rest false: 
    clause1=[] #Ors for each list of hs
    for h_bools in z3vars: #for each sublist in this list
        # clause1.append(z3.Xor()) #Xor for at only one must be true and the rest false, but not working so must use combination of Or and And
        clause1.append(z3.Or(h_bools)) #Or for at least one must be true
        
        #"And" piece
        for e in range(len(h_bools)-1): #each element must have -xi ^ -xj appended for the whole list
            for counter in range(e+1,len(h_bools)):
                clause1.append(z3.Not(z3.And(h_bools[e], h_bools[counter])))

    print(clause1)
    mysolver.add(clause1)

    #Clause 2: if a hole is filled with a number, it cannot be filled by another at the same time (max 1 num per hole)
    #For each posisble input in a hole, if one is true then the rest must be false
    # "And" piece in Clause 1 :), reaching the xor state

    #Clause 3: "non-repetition": if a number is already in a hole it cannot be selected again for another hole. (if you want to allow repeated numbers, one trick is to create a dictionary and temporarily use a "unique" number)
    #For each hole, if one input is true then the same input must be false in other holes
    clause3=[]
    for j in range(len(z3vars[0])):
        #get "and" bools
        temp_ands=[]
        for i in range(len(z3vars)):
            temp_ands.append(z3vars[i][j])

        #add "and" bools in equaions
        clause3.append(z3.Not(z3.And(temp_ands))) #PROBLEM here, adds 3 ands but must add 2 ands for each like in previous clause (use counter)

    print(clause3)
    mysolver.add(clause3)

    #Check solution
    Checksat(mysolver, z3vars)
    #endregion
