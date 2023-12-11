from z3 import *

#variables
IGiI=Int('IGiI')
IWI=Int('IWI')
IangleI=Int('IangleI')
IGiI=Int('IGiI')
IrateI=Int('IrateI')
IangleI_next=Int('IangleI_next')
IGiI_next=Int('IGiI_next')
IrateI_next=Int('IrateI_next')
workmode=Int('workmode')
flgSP=Int('flgSP')
Gi=RealVector('Gi',2)
Gi_next=RealVector('Gi_next',2)
angle=RealVector('angle',3)
angle_next=RealVector('angle_next',3)
rate=RealVector('rate',3)
rate_next=RealVector('rate_next',3)
W=RealVector('W',3)
piyaw=Const('piyaw', RealSort())
royaw=Const('royaw', RealSort())

#Contract
s = Solver()
Assumptions = And(IGiI==2, IWI==3)
Case1 = Implies(workmode==51, Implies(flgSP==235, And(angle_next[0]==royaw, angle_next[1]==piyaw, Gi_next[0]==royaw, Gi_next[1]==piyaw)))
Case2 = Implies(workmode==51, Implies(flgSP!=235, And(angle_next[0]==Gi[0], angle_next[1]==Gi[1], Gi_next[0]==Gi[0], Gi_next[1]==Gi[1])))
Case3 = Implies(workmode!=51, And(angle_next[0]==0, angle_next[1]==0, Gi_next[0]==Gi[0], Gi_next[1]==Gi[1]))
Case4 = And(rate_next[0]==W[0], rate_next[1]==W[1], rate_next[2]==W[2])
Guarantees = And(IangleI_next==2, IGiI_next==2, IrateI_next==3, Case1, Case2, Case3, Case4)
s.add(Implies(Assumptions, Guarantees))
s.add(Assumptions)
########
