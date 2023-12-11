from z3 import *

#variables
i,j = Ints('i j')
JoinTotal = Int('JoinTotal')
SignFlag = Array('SignFlag', IntSort(), IntSort())
ISignFlagI = Int('ISignFlagI')
wa = Array('wa', IntSort(), RealSort())
IwaI = Int('IwaI')
W = Array('W', IntSort(), IntSort())
IW_nextI = Int('IW_nextI')
W_next = Array('W_next', IntSort(), IntSort())
tmpwa = Array('tmpwa', IntSort(), RealSort())
ItmpwaI = Int('ItmpwaI')
Rtemp = Array('Rtemp', IntSort(), ArraySort(IntSort(), RealSort()))
IRtemp1I = Int('IRtemp1I')
IRtemp2I = Int('IRtemp2I')
s = Solver()

#Contract

A1 = And(ISignFlagI>=JoinTotal, JoinTotal<=5, IRtemp1I==3, IRtemp2I==5)
A2 = (ForAll(j, Implies(And(j>=0, j<JoinTotal), SignFlag[j]<IwaI)))
Assumptions = And(A1, A2)
G1 = And(IW_nextI==3, ItmpwaI==5)
G2_1 = ForAll(j, Implies(And(j>=0, j < JoinTotal),And(tmpwa[j]==wa[SignFlag[j]])))
G2_2 = ForAll(j, Implies(And(j>=JoinTotal), tmpwa[j]==0))
G3 = Implies(JoinTotal >= 3, ForAll(i, Implies(And(i>=0, i<3), W_next[i] == (Rtemp[i][0]*tmpwa[0]+Rtemp[i][1]*tmpwa[1]+Rtemp[i][2]*tmpwa[2]+Rtemp[i][3]*tmpwa[3]+Rtemp[i][4]*tmpwa[4]))))
G4 = Implies(JoinTotal < 3, ForAll(i, Implies(And(i>=0, i<3), W_next[i]==0)))
Guarantees = And(G1, G2_1, G2_2 ,G3, G4)
s.add(Implies(Assumptions, Guarantees))
s.add(Assumptions)
########
