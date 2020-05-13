import copy

def parse1(s):
 if len(s) == 1 or s == "_|_":
  return True
 val =[n for n in range(len(s)) if (s == "("+ s[1:n] + " /\ " + s[n+4:len(s)-1]+ ")" and parse1(s[1:n]) and parse1(s[n+4:len(s)-1])) or (s == "(" +s[1:n] + " -> " + s[n+4:len(s)-1] + ")" and parse1(s[1:n]) and parse1(s[n+4:len(s)-1])) or (s == "("+ s[1:n] + " \/ " + s[n+4:len(s)-1]+")" and parse1(s[1:n]) and parse1(s[n+4:len(s)-1] ) ) ]   
 if val!=[]:
  return True
 return False

def parse(o, s):
 val =[n for n in range(len(s)) if s == s[0:n] + o + s[n+len(o):] and parse1(s[1:n]) and parse1(s[n+len(o):len(s)-1])]
 if val !=[] :
  n = val[0]
  return [s[1:n],s[n+len(o):len(s)-1]]
 else:
  return []

print 
print "PyGen G3i/G3m IPC Automatic Prover v1.2"
print "   by Clarence Protin 2019  "
print "type help() for command list"

def help():
 print "seq = newseq(f) - defines the sequent  [] = > f"
 print "addfor(deq,f) - adds f to antecedent of sequent seq"
 print "proof(seq) - searches for proof" 
 print "bproof(seq,k) -  limited depth search"


def newseq(f):
 aux = [[[],[f]]]
 print disp(aux)
 return aux

def addfor(a,f):
 a[0][0].append(f)
 return a



def LROr(State, Proof, sequent, formula):
 return ROr(State, Proof, sequent, formula,0)

def RROr(State, Proof, sequent, formula):
 return ROr(State, Proof, sequent, formula,1)

def disp(state):
 if state == []:
  return "Q.E.D."
 a= ""
 for seq in range(len(state)):
   a = a +"("+str(seq + 1)+") "+ nice(state[seq][0]) + " => " + nice(state[seq][1]) + "   "
 return a

def dproof(proof):
 print(nice(proof))
 return

def nice(l):
 val = ""
 if len(l) > 0:
  for n in range(len(l)-1):
   val = val + l[n] + ", "
  val = val + l[len(l)-1]
 return val


def SetEq(list1,list2):
 if len(list1)!= len(list2):
  return False
 for n in range(len(list1)):
  if list1[n] not in list2:
   return False
 return True

def SeqEq(seq1,seq2):    
 if seq1[1][0] == seq2[1][0]:
  if SetEq(seq1[0],seq2[0]):
   return True
 return False 


def InStat(seq,stat):
 if len(stat) == 0 or len(seq)== 0:
  return False
 for n in range(len(stat)):
  if SeqEq(seq,stat[n]):
    return True
 return False
 
def MemJoin(state,mem):
  for n in range(len(state)):
    if not InStat(state[n],mem):
      mem.append(state[n])
  return mem           

def StatInc(stat1,stat2):
 if len(stat1)== 0 or len(stat2)==0:
     return False    
 for n in range(len(stat1)):
   if InStat(stat1[n],stat2):
    return True
 return False


def RImp(state, proof, sequent, formula):
 if sequent > len(state)-1:
  return [state,proof,[]]
 if formula > len(state[sequent][0]):
  return [state,proof,[]]
 aux = parse(" -> ", state[sequent][1][0])
 if aux == []:
  return [state, proof,[]]
 state[sequent][1].pop()
 state[sequent][1].append(aux[1])
 state[sequent][0].append(aux[0])
 proof.append([2, sequent])
 val = [state, proof, [state[sequent]]]
 return val

def LAnd(state, proof, sequent,formula):
 if sequent > len(state)-1:
  return [state,proof,[]]
 if formula > len(state[sequent][0])-1:
  return [state,proof,[]]
 aux = parse(" /\ ", state[sequent][0][formula])
 if aux == []:
   return [state,proof,[]]
 state[sequent][0].pop(formula)
 state[sequent][0].append(aux[0])
 state[sequent][0].append(aux[1])  
 proof.append([6, sequent, formula])
 val = [state,proof,[state[sequent]]]
 return val

def ROr(state, proof, sequent, formula, i):
 if sequent > len(state)-1:
  return [state,proof,[]]
 if formula > len(state[sequent][0]):
  return [state,proof,[]]
 aux = parse(" \/ ", state[sequent][1][0])
 if aux ==[]:
  return [state,proof,[]]
 state[sequent][1].pop(0)
 state[sequent][1].append(aux[i])  
 proof.append([7, sequent, i])
 val = [state,proof,[state[sequent]]]
 return val

def RAnd(state, proof,sequent, formula):
 if sequent > len(state)-1:
  return [state,proof,[]]
 if formula > len(state[sequent][0]):
  return [state,proof,[]]
 aux = parse(" /\ ", state[sequent][1][0])
 if aux ==[]:
  return [state,proof,[]]
 left = []
 le = copy.deepcopy(state[sequent])
 left.append(le)
 left[0][1].pop(0)
 left[0][1].append(aux[0])
 right = []
 re = copy.deepcopy(state[sequent])
 right.append(re)
 right[0][1].pop(0)
 right[0][1].append(aux[1])
 state.pop(sequent)
 state = state + left 
 state = state + right
 proof.append([1, sequent])
 val = [state, proof, left + right ]
 return val

def LOr(state, proof, sequent,formula):
 if sequent > len(state)-1:
  return [state,proof,[]]
 if formula > len(state[sequent][0])-1:
  return [state,proof,[]]
 aux = parse(" \/ ", state[sequent][0][formula])
 if aux ==[]:
  return [state,proof,[]]
 left = []
 le = copy.deepcopy(state[sequent])
 left.append(le)
 left[0][0].pop(formula)
 left[0][0].append(aux[0])
 right = []
 re = copy.deepcopy(state[sequent])
 right.append(re)
 right[0][0].pop(formula)
 right[0][0].append(aux[1])
 state.pop(sequent)
 state = state + left 
 state = state + right
 val = [state,proof, left + right]
 proof.append([3, formula, sequent])
 return val

def LImp(state, proof, sequent, formula):
 if sequent > len(state)-1:
  return [state,proof,[]]
 if formula > len(state[sequent][0])-1:
  return [state,proof,[]]
 aux = parse(" -> ", state[sequent][0][formula])
 if aux ==[]:
  return [state,proof,[]]
 left = []
 le = copy.deepcopy(state[sequent])
 left.append(le)
 right = []
 re = copy.deepcopy(state[sequent])
 right.append(re)
 state.pop(sequent)
 x = LImp2(left,formula) + LImp1(right,formula)
 state = state + x
 y = copy.deepcopy(x)
 proof.append([5, sequent, formula])
 val = [state, proof, y]
 return val

def LImp1(proof, formula):
 aux = parse(" -> ", proof[0][0][formula])
 proof[0][0].pop(formula)
 proof[0][0].append(aux[1])
 return proof 

def LImp2(proof, formula):
 aux = parse(" -> ", proof[0][0][formula])
 proof[0][1].pop(0)
 proof[0][1].append(aux[0])
 return proof

def Ax(state, proof, sequent, formula):
 if sequent > len(state)-1:
  return [state,proof,[]]
 if formula > len(state[sequent][0]):
  return [state,proof,[]]
 if (len(state[sequent][1][0]) == 1 or state[sequent][1][0]=="_|_" ) and  state[sequent][1][0] in state[sequent][0]:
  state.pop(sequent)
  proof.append([0,sequent])
 val = [state,proof, []]
 return val

def LAbs(state, proof, sequent,formula):
 if sequent > len(state)-1:
  return [state,proof,[]]
 if formula > len(state[sequent][0])-1:
  return [state,proof,[]]
 if state[sequent][0][formula] == "_|_":
  state.pop(sequent)
  proof.append([4,sequent, formula])
 val = [state, proof,[]]
 return val


Lmoves = {0:Ax, 1:LAbs, 2:LImp, 3: LAnd, 4: LOr }
Rmoves = {0:RImp, 1: RAnd,  2: LROr , 3: RROr}
moves = {0:Ax, 1:LAbs, 2:LImp, 3: LAnd, 4: LOr, 5:RImp, 6: RAnd,  7: LROr , 8: RROr}
tmoves = {0:"Ax", 1:"LAbs", 2:"LImp", 3: "LAnd", 4: "LOr", 5:"RImp", 6: "RAnd",  7: "LROr" , 8: "RROr"}


fdictionary = {0:Ax, 1:RAnd, 2:RImp, 3:LOr, 4:LAbs, 5:LImp, 6:LAnd, 7:ROr }
sdictionary = {0:"Ax", 1:"RAnd", 2:"RImp", 3:"LOr", 4:"LAbs", 5:"LImp", 6:"LAnd", 7:"ROr" }


def fread(code,state):
 if code[0]< 3:
  return fdictionary[code[0]](copy.deepcopy(state),[],code[1],0)[0]
 else:
  if code[0]< 7:
   return fdictionary[code[0]](copy.deepcopy(state),[],code[1],code[2])[0]
  else:
   return fdictionary[code[0]](copy.deepcopy(state),[],code[1],0, code[2])[0]


def fcompute(codelist,state):
 print disp(state)
 for code in codelist:
  state = fread(code,state)
  print disp(state), sread(code)
 return state


def sread(code):
 if code[0]< 3:
  return sdictionary[code[0]]+str(code[1]+1)             
 else:
  if code[0]< 7:
   return sdictionary[code[0]]+str(code[1]+1) + "f" + str(code[2]+1)
  else:
   return sdictionary[code[0]]+str(code[1]+1) +"i" +str(code[2]+1)


def scompute(codelist):
 val = []
 for code in codelist:
   val.append(sread(code))
 return val

def read1(code,state):
 return moves[int(code[0])](copy.deepcopy(state),[],int(code[1]),int(code[2]))[0]

def read2(codelist, state):
 for code in codelist:
  if read1(code,copy.deepcopy(state))!= state:
   state = read1(code,state)
  else:
   return False
 return state

def check(codelist,state):
 if read2(codelist,state) == []:
  return True
 else:
  return False

def trans(codelist):
 s = []
 for cod in codelist:
  if int(cod[0])< 5:
   s.append(tmoves[int(cod[0])]+"S"+cod[1]+"f"+cod[2])
  else:
   s.append(tmoves[int(cod[0])]+"S"+cod[1])
 return s

def prove(state, proof,mem): 
 if state == []:
  return ["SUCCEED",proof] 
 for s in range(len(state)):
  if len(state[s][0]) != 0 and parse(" -> ", state[s][1][0]) == []:
   for f in range(len(state[s][0])):
    for m in range(5):
     aux =  Lmoves[m](copy.deepcopy(state),copy.deepcopy(proof), s,f) 
     
     
        
     if aux[0]!= state and not StatInc(aux[2],mem):
      if prove(copy.deepcopy(aux[0]), copy.deepcopy(aux[1]),copy.deepcopy(mem) + copy.deepcopy(aux)[2] )[0] != "FAIL":
       return prove(copy.deepcopy(aux[0]), copy.deepcopy(aux[1]),copy.deepcopy(mem) + copy.deepcopy(aux)[2] )                 
     
  for m in range(4):
   aux2 = Rmoves[m](copy.deepcopy(state),copy.deepcopy(proof) , s,0)      
   if aux2[0]!= state and not StatInc(aux2[2],mem):
    if prove(copy.deepcopy(aux2)[0], copy.deepcopy(aux2)[1],copy.deepcopy(mem) + copy.deepcopy(aux2)[2]  )[0]!="FAIL":
     return prove(copy.deepcopy(aux2)[0], copy.deepcopy(aux2)[1], copy.deepcopy(mem) + copy.deepcopy(aux2)[2] )
      
 return ["FAIL",proof]

def proof(state):
 fcompute(prove(state,[],[])[1],state)
 return 






def prove1(state, proof,k):
 if k == 0:

  return ["FAIL", proof]
 if state == []:
  
  return ["SUCCEED",proof] 
 for s in range(len(state)):
  if len(state[s][0]) != 0 and parse(" -> ", state[s][1][0],) == []:
   for f in range(len(state[s][0])):
    for m in range(5):
     if Lmoves[m](copy.deepcopy(state),copy.deepcopy(proof), s,f)[0]!= state:
      if prove1(Lmoves[m](copy.deepcopy(state),copy.deepcopy(proof), s,f)[0], Lmoves[m](copy.deepcopy(state),copy.deepcopy(proof), s,f)[1],k-1)[0] != "FAIL":
       return prove1(Lmoves[m](copy.deepcopy(state),copy.deepcopy(proof), s,f)[0], Lmoves[m](copy.deepcopy(state),copy.deepcopy(proof), s,f)[1],k-1)
     
  for m in range(4):
   if Rmoves[m](copy.deepcopy(state),copy.deepcopy(proof) , s,0)[0]!= state:
    if prove1(Rmoves[m](copy.deepcopy(state),copy.deepcopy(proof), s,0)[0], Rmoves[m](copy.deepcopy(state),copy.deepcopy(proof), s,0)[1],k-1)[0]!="FAIL":
     return prove1(Rmoves[m](copy.deepcopy(state),copy.deepcopy(proof), s,0)[0], Rmoves[m](copy.deepcopy(state),copy.deepcopy(proof), s,0)[1],k-1 )
 return ["FAIL",proof]

def bproof(state,k):
 aux = prove1(state,[],k)
 if aux[0] == "SUCCEED": 
  fcompute(aux[1],state)
 return 

def sproof(state,k):
 for n in range(1,k+1):
  print n
  aux = prove1(state,[],n)
  if aux[0] == "SUCCEED": 
   fcompute(aux[1],state)
   return 
   
   
test = "((A -> (B -> C)) -> ((A -> B) -> (A -> C)))"

