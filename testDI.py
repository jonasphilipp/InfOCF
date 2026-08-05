
from interim_generator import samplingCKB
from inference.weak_c_inference import WeakCInference

while True:
	v,c, ckb = samplingCKB(20,20,4,8)
	wci = WeakCInference(ckb)	
	print("--------------------")
	for i,c in ckb.conditionals.items():
		if False == (wci.inference(c)):
			print(c)

