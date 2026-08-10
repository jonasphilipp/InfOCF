
from interim_generator import samplingCKB, makeCKB
from inference.weak_c_inference import WeakCInference
from extinf.weakcz3_imp import WeakCz3IMP

seed = 10
while True:
    seed+=1
    S,R, l,u= 50,50,2,6
    v,c, ckb = samplingCKB(S,R,l,u,seed)
    wci = WeakCInference(ckb)
    #wci = WeakCz3IMP(ckb)
    print("--------------------")
    for i,c in ckb.conditionals.items():
        if False == (wci.inference(c)):
            print(S,R,l,u,seed)
            makeCKB(ckb.signature, ckb.conditionals.values(), f'bb{seed}.cl')
            break

