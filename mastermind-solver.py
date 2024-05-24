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

#region Clauses
#Clause 1: all holes must have an input. For each posisble input in a hole, at least one is true
def clause_At_least_one_num_true(z3vars):
    clause1=[] #Ors for each list of hs
    for h_bools in z3vars: #for each sublist in this list
        clause1.append(z3.Or(h_bools)) #Or for at least one must be true
    return clause1

#Clause 2: if a hole is filled with a number, it cannot be filled by another at the same time (max 1 num per hole)
def clause_Only_one_hole_per_num(z3vars):
    clause1=[] #Ors for each list of hs
    for h_bools in z3vars: #for each sublist in this list
        #"And" piece
        for e in range(len(h_bools)-1): #each element must have -xi ^ -xj appended for the whole list
            for counter in range(e+1,len(h_bools)):
                clause1.append(z3.Not(z3.And(h_bools[e], h_bools[counter])))
    return clause1

#For each posisble input in a hole, only one must be true and the rest false: 
def clause_Only_one_num_true(z3vars):
    #Xor for at only one must be true and the rest false, using combination of Or and And
    return clause_At_least_one_num_true(z3vars) + clause_Only_one_num_per_hole(z3vars) #Can use this alone instead of clause1 and 2 combined individually

#Clause 3: "non-repetition": if a number is already in a hole it cannot be selected again for another hole. (if you want to allow repeated numbers, one trick is to create a dictionary and temporarily use a "unique" number)
#For each hole, if one input is true then the same input must be false in other holes
def clause_Only_one_num_per_hole(z3vars):
    clause3=[]
    for j in range(len(z3vars[0])): #len of an h list since they're all similar length
        #get "and" bools
        for i in range(len(z3vars)-1): #double pointer, one that iterates till end of the list while one is stationary for each iteration
            for counter in range(i+1, len(z3vars)):
                clause3.append(z3.Not(z3.And(z3vars[i][j], z3vars[counter][j])))
    return clause3
#endregion

#region Constraints
#NOTE: Must create rules up to num_holes-1 :). With more experience you can automate these rule creations 
def rule_OneCorrect_WrongPlace(input_string):
    user_input_list = list(input_string)
    print(user_input_list)
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
    # #For each posisble input in a hole, at least one must be true: 
    # clause1=clause_At_least_one_num_true(z3vars) #Ors for each list of hs
    # print(clause1)
    # mysolver.add(clause1)

    # #Clause 2: if a hole is filled with a number, it cannot be filled by another at the same time (max 1 num per hole)
    # #For each posisble input in a hole, if one is true then the rest must be false
    # # "And" piece in Clause 1 :), reaching the xor state
    # clause2=clause_Only_one_hole_per_num(z3vars)
    # print(clause2)
    # mysolver.add(clause2)

    #Clause 1' (instead of 1 and 2 above combined): For each posisble input in a hole, only one must be true and the rest false: 
    clause1= clause_Only_one_num_true(z3vars)
    print(clause1)
    mysolver.add(clause1)


    #Clause 3: "non-repetition": if a number is already in a hole it cannot be selected again for another hole. (if you want to allow repeated numbers, one trick is to create a dictionary and temporarily use a "unique" number)
    #For each hole, if one input is true then the same input must be false in other holes
    clause3=clause_Only_one_num_per_hole(z3vars)
    print(clause3)
    mysolver.add(clause3)

    #Check solution
    Checksat(mysolver, z3vars)
    #endregion
