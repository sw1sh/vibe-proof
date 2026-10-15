import random, sys
sys.path.insert(0, "/Users/swish/.claude/jobs/b8cd2926/tmp/r30prize/verify-C3-longones")
src = open("/Users/swish/.claude/jobs/b8cd2926/tmp/r30prize/verify-C3-longones/t7_stress.py").read()
src = src.replace("    tot += 1\n", "    tot += 1\n    Ns.append(N); Ps.append(P); nchk.append(sum(1 for t in range(T+9+P, N) if c[t]==0)); nfail.append(len(kf))\n")
src = src.replace("tot = keyv = perv = 0", "tot = keyv = perv = 0\nNs=[];Ps=[];nchk=[];nfail=[]")
exec(compile(src, "t7", "exec"))
print("mean N", sum(Ns)/len(Ns), "max N", max(Ns), "mean P", sum(Ps)/len(Ps), "max P", max(Ps))
print("white cells checked past bound:", sum(nchk), " key failures before bound (all trials):", sum(nfail))
