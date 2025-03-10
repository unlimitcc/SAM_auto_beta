from z3 import *

#invariables
m_workMode = Int('m_workMode')
m_workMode_next = Int('m_workMode_next')
m_countMode = Int('m_countMode')
m_countMode_next = Int('m_countMode_next')
m_countPublic = Int('m_countPublic')
m_countPublic_next = Int('m_countPublic_next')
time_D2P = Int('time_D2P')
time_D2P_overtime = Int('time_D2P_overtime')
flgSP = Int('flgSP')
piyaw = Real('piyaw')
royaw = Real('royaw')
temp = Real('temp')
pGyroRate = Array('pGyroRate', IntSort(), RealSort())
s = Solver()
#Contract
s.add(Implies(And(m_workMode==0, Or(m_countMode>800, m_countPublic>280)), m_workMode_next==17))
s.add(Implies(And(m_workMode==17, m_countMode>4500), m_workMode_next==34))
s.add(Implies(And(m_workMode==34, m_countMode>5000), m_workMode_next==17))
s.add(Implies(And(m_workMode==17, flgSP==1, Or(piyaw>0.25, piyaw<-0.25), m_countPublic>12, m_countMode<=4500), m_workMode_next==51))
s.add(Implies(And(m_workMode==34, flgSP==1, Or(royaw>1.0, royaw<-1.0), m_countPublic>12, m_countMode<=5000), m_workMode_next==51))
s.add(Implies(And(m_workMode==0, m_countMode<=800, m_countPublic<=280), m_workMode_next==0))
s.add(Implies(And(m_workMode==17, Or(flgSP!=1, piyaw<0.25, piyaw>-0.25, m_countPublic<=12), m_countMode<=4500), m_workMode_next==17))
s.add(Implies(And(m_workMode==34, Or(flgSP!=1, royaw<1.0, royaw>-1.0, m_countPublic<=12), m_countMode<=5000), m_workMode_next==34))
s.add(Implies(m_workMode==51, m_workMode_next==51)) 
s.add(m_countMode==8192)
s.add(m_countMode_next==0)
s.add(m_countPublic==0)
s.add(m_countPublic_next==0)
s.add(m_workMode==34)
s.add(m_workMode_next==17)
s.add(flgSP==235)
s.add(pGyroRate[0]==-0.0215000007)
s.add(pGyroRate[1]==-0.124200001)
s.add(pGyroRate[2]==0.00579999993)
s.add(piyaw==0.178499997)
s.add(royaw==-0.498600006)
s.add(time_D2P==280)
s.add(time_D2P_overtime==800)
print(s.check())




