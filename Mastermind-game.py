import random

#Mastermind game guessing a sequence of Distinct integers between 1 and a limit within a sequence length
"""NOTE: 
- No checks for redundant numbers here, the assumption for now is that the user will NOT input redundant numbers
- No checks if user inputs non-integers or out of bounds numbers, assumption is user will abide by instruction
"""

num_options = 8
len_sequence = 4

def GenerateRandomNum(limit=num_options):
    randnum = random.randint(1,num_options)
    return randnum

def GenerateSequence():
    i=0
    sequence=""
    while i<len_sequence:
        randnum = str(GenerateRandomNum())
        while randnum in sequence:
            randnum = str(GenerateRandomNum())
        sequence = sequence + randnum
        i=i+1
    return sequence

def CheckAnswer (user_input, sequence):
    num_correctinplace = 0
    num_correctoutplace = 0

    i=0
    while i<len_sequence:
        if user_input[i]==sequence[i]:
            num_correctinplace+=1
        elif user_input[i] in sequence:
            num_correctoutplace+=1
        i=i+1
    return "You have "+str(num_correctinplace)+" Correct in place and "+str(num_correctoutplace)+" Correct but Not in place"


if __name__ == "__main__":
    print("\n--------- WELCOME TO MASTERMIND! ----------\n")
    sequence = GenerateSequence()
    print ("Guess the sequence of "+str(len_sequence)+" numbers between 1 and "+str(num_options)+";\nIf you wish to give up, press q:\n****")
    print("Enter "+str(len_sequence)+" number between 1 and "+str(num_options))
    #Debugging
    # print(sequence)

    user_input = ""
    while user_input != sequence:        
        user_input = input()
        #Debugging
        # print(user_input)
        
        if user_input=="q":
            print(sequence)
            quit()

        if len(user_input)!=len_sequence:
            print("Please only write a sequence of "+str(len_sequence)+" numbers between 1 and "+str(num_options))
            continue

        print(CheckAnswer(user_input, sequence))
    
    print("All 4 are correct, Congratulations!!! :) ")