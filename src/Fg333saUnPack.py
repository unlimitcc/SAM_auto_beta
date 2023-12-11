from z3 import *

#variables
IpRecvbufI = Int('IpRecvbufI')
gf = Real('gf')
wt0 = Real('wt0')
wt0_next = Real('wt0_next')
dtime = Real('dtime')
glwd1 = Int('glwd1')
glwd2 = Int('glwd2')
dlwd = Int('dlwd')
status = Int('status')
pRecvbuf = IntVector('pRecvbuf', 17)

s = Solver()
#Contract
Assumptions = (IpRecvbufI>=17)
Assign1 = (wt0==((2**12)*pRecvbuf[2]+(2**8)*pRecvbuf[3]+(2**4)*pRecvbuf[4]+pRecvbuf[5])/(3*10**6*0.0174532925199433))
Assign2 = (glwd1==(2**4)*pRecvbuf[6]+pRecvbuf[7])
Assign3 = (glwd2==(2**4)*pRecvbuf[8]+pRecvbuf[9])
Assign4 = (dlwd==(2**4)*pRecvbuf[10]+pRecvbuf[11])
Assign5 = (status==pRecvbuf[16])
Assign6 = (gf==wt0_next*dtime)
Guarantees = And(Assign1, Assign2, Assign3, Assign4, Assign5, Assign6)
s.add(Implies(Assumptions, Guarantees))
s.add(Assumptions)
####
