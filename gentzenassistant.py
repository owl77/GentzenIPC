import copy

State = []
Proof = []


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
print "Gentzen G1i/G1m Proof Assistant v0.2"
print
print "type help() for command list"


def help():
 print "new(f), disp(), proof(), Ax(s), Abs(s), LC(s,f), LW(s,f), RC(s), RImp(s), LImp(s,f), LAnd(s,f,i), LOr(s,f), RAnd(s), ROr(s,i)"

def new(f):
 if parse1(f):
  seq = [[],[]]
  seq[1].append(f)
  State.append(seq)
  disp()
 else:
  print "Syntax Error !"
 return



def disp():
 global State
 if State == []:
  print "Q.E.D."
 for seq in range(len(State)):
  print("("+str(seq +1)+") "+ nice(State[seq][0]) + " => " + nice(State[seq][1]) + "   "),
 return

def proof():
 global Proof
 print(nice(Proof))
 return

def nice(l):
 val = ""
 if len(l) > 0:
  for n in range(len(l)-1):
   val = val + l[n] + ", "
  val = val + l[len(l)-1]
 return val

def clear():
 global State
 State = []
 return

def RImp(sequent):
 sequent = sequent -1
 global Proof
 aux = parse(" -> ", State[sequent][1][0])
 if aux == []:
  return
 State[sequent][1].pop()
 State[sequent][1].append(aux[1])
 State[sequent][0].append(aux[0])  
 disp()
 Proof.append("RImpS" + str(sequent+ 1))
 return

def LAnd(sequent,formula,i):
 global Proof
 sequent = sequent -1
 formula = formula -1
 i = i -1
 aux = parse(" /\ ", State[sequent][0][formula])
 if aux == []:
   return
 State[sequent][0].pop(formula)
 State[sequent][0].append(aux[i])  
 disp()
 Proof.append("LAndS" + str(sequent+1)+"f"+str(formula+1)+"i"+str(i+1))
 return


def ROr(sequent,i):
 global Proof
 sequent = sequent -1
 i = i -1
 aux = parse(" \/ ", State[sequent][1][0])
 if aux ==[]:
  return
 State[sequent][1].pop(0)
 State[sequent][1].append(aux[i])  
 disp()
 Proof.append("ROrS" + str(sequent+1)+"i"+str(i+1))
 return



def RAnd(sequent):
 global State
 global Proof
 sequent = sequent -1
 aux = parse(" /\ ", State[sequent][1][0])
 if aux ==[]:
  return
 left = []
 le = copy.deepcopy(State[sequent])
 left.append(le)
 left[0][1].pop(0)
 left[0][1].append(aux[0])
 right = []
 re = copy.deepcopy(State[sequent])
 right.append(re)
 right[0][1].pop(0)
 right[0][1].append(aux[1])
 State.pop(sequent)
 State = State + left 
 State = State + right
 disp()
 Proof.append("RAndS" + str(sequent+1))
 return


def LOr(sequent,formula):
 global State
 global Proof
 sequent = sequent -1
 formula = formula -1
 aux = parse(" \/ ", State[sequent][0][formula])
 if aux ==[]:
  return
 left = []
 le = copy.deepcopy(State[sequent])
 left.append(le)
 left[0][0].pop(formula)
 left[0][0].append(aux[0])
 right = []
 re = copy.deepcopy(State[sequent])
 right.append(re)
 right[0][0].pop(formula)
 right[0][0].append(aux[1])
 State.pop(sequent)
 State = State + left 
 State = State + right
 disp()
 Proof.append("LOrS" + str(sequent+1))
 return

def LImp(sequent, formula):
 global State
 global Proof
 sequent = sequent -1
 formula = formula -1
 aux = parse(" -> ", State[sequent][0][formula])
 if aux ==[]:
  return
 left = []
 le = copy.deepcopy(State[sequent])
 left.append(le)
 right = []
 re = copy.deepcopy(State[sequent])
 right.append(re)
 State.pop(sequent)
 State = State + LImp2(left,formula) 
 State = State + LImp1(right, formula)
 disp()
 Proof.append("LImpS" + str(sequent+1) +"f"+str(formula+1))
 return

def LImp1(proof, formula):
 aux = parse(" -> ", proof[0][0][formula])
 proof[0][0].pop(formula)
 proof[0][0].append(aux[1])
 return proof 

def LImp2(proof, formula):
 aux = parse(" -> ", proof[0][0][formula])
 proof[0][0].pop(formula)
 proof[0][1].pop(0)
 proof[0][1].append(aux[0])
 return proof

def Ax(sequent):
 sequent = sequent -1
 global State
 global Proof
 if len(State[sequent][0])== 1 and State[sequent][0][0] == State[sequent][1][0]:
  State.pop(sequent)
  Proof.append("AxS"+str(sequent+1))
  disp() 
 return

def LAbs(sequent):
 global State
 global Proof
 sequent = sequent -1
 if len(State[sequent][0])== 1 and State[sequent][0][0] == "_|_" and State[sequent][1] == []:
  State.pop(sequent)
  Proof.append("LAbs"+str(sequent+1))
  disp() 
 return




def LW(sequent, formula):
 global State
 sequent = sequent -1
 formula = formula -1
 State[sequent][0].pop(formula)
 Proof.append("LWS"+str(sequent+1)+"f"+str(formula+1)) 
 disp()
 return


def LC(sequent, formula):
 global State
 sequent = sequent -1
 formula = formula -1
 aux = State[sequent][0][formula]
 State[sequent][0].append(aux)
 Proof.append("LCS"+str(sequent+1)+"f"+str(formula+1))
 disp() 
 return


def RW(sequent):
 global State
 sequent = sequent -1
 State[sequent][1].pop(0)
 Proof.append("RWS"+str(sequent+1))
 disp() 
 return


