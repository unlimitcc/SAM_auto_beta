from z3 import *

#variable
powerState = Int('powerState')
cntPowerOn = Int('cntPowerOn')
cntPowerOn_next = Int('cntPowerOn_next')
cntPowerOff = Int('cntPowerOff')
cntPowerOff_next = Int('cntPowerOff_next')
powerPr1 = Int('powerPr1')
powerPr1_next = Int('powerPr1_next')
bPowerOnOk = Int('bPowerOnOk')
bPowerOnOk_next = Int('bPowerOnOk_next')
numOnPeriod = Const('numOnPeriod', IntSort())
numOnPeriod_next = Const('numOnPeriod_next', IntSort())
numOffPeriod = Const('numOffPeriod', IntSort())
numOffPeriod_next = Const('numOffPeriod_next', IntSort())
#Contract1
s = Solver()
s.add(numOffPeriod == 2)
s.add(numOnPeriod == 30)
Assumptions = Or(powerState == 0, powerState == 255)
Case1 = And(powerState == 0, cntPowerOff < numOffPeriod, powerPr1_next == 0, cntPowerOn_next == cntPowerOn, cntPowerOff_next == cntPowerOff + 1)
Case2 = And(powerState == 0, cntPowerOff >= numOffPeriod, bPowerOnOk_next == 0, powerPr1_next == 0, cntPowerOn_next == 0, cntPowerOff_next == cntPowerOff)
Case3 = And(powerPr1 == 0, powerState == 255, cntPowerOn_next > numOnPeriod, bPowerOnOk_next == 1, powerPr1_next == 255, cntPowerOn_next == cntPowerOn + 1, cntPowerOff_next == 0)
Case4 = And(powerPr1 == 0, powerState == 255, cntPowerOn_next <= numOnPeriod, powerPr1_next == 0, cntPowerOn_next == cntPowerOn + 1, cntPowerOff_next == cntPowerOff)
Case5 = And(powerState != 0, Or(powerPr1 != 0, powerState != 255), powerPr1_next == powerState, cntPowerOn_next == cntPowerOn, cntPowerOff_next == cntPowerOff)
Unchange = And(numOnPeriod_next == numOnPeriod, numOffPeriod_next == numOffPeriod)
Guarantees = And(Or(Case1, Case2, Case3, Case4, Case5), Unchange)
s.add(Implies(Assumptions, Guarantees))
s.add(Assumptions)
#####
