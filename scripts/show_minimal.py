from inference.inference_manager import InferenceManager
from parser.Wrappers import parse_belief_base

# belief base and queries provided dircetly as string. providing a filepath of belief base and
# queries is also viable. see show.py for demonstration
bb = ['bb102.cl', 'bb103.cl', 'bb105.cl', 'bb111.cl', 'bb114.cl', 'bb116.cl', 'bb117.cl', 'bb120.cl', 'bb121.cl', 'bb126.cl', 'bb127.cl', 'bb129.cl', 'bb12.cl', 'bb131.cl', 'bb132.cl', 'bb133.cl', 'bb134.cl', 'bb137.cl', 'bb139.cl', 'bb142.cl', 'bb146.cl', 'bb148.cl', 'bb149.cl', 'bb14.cl', 'bb151.cl', 'bb152.cl', 'bb153.cl', 'bb155.cl', 'bb157.cl', 'bb158.cl', 'bb159.cl', 'bb160.cl', 'bb161.cl', 'bb166.cl', 'bb16.cl', 'bb17.cl', 'bb19.cl', 'bb1.cl', 'bb20.cl', 'bb25.cl', 'bb28.cl', 'bb2.cl', 'bb33.cl', 'bb35.cl', 'bb39.cl', 'bb40.cl', 'bb41.cl', 'bb42.cl', 'bb43.cl', 'bb47.cl', 'bb49.cl', 'bb50.cl', 'bb51.cl', 'bb53.cl', 'bb54.cl', 'bb56.cl', 'bb5.cl', 'bb61.cl', 'bb64.cl', 'bb66.cl', 'bb69.cl', 'bb75.cl', 'bb76.cl', 'bb77.cl', 'bb82.cl', 'bb86.cl', 'bb88.cl', 'bb93.cl', 'bb95.cl', 'bb96.cl', 'bb97.cl', 'bb99.cl']
bb = ['bb19.cl']
#for i in [12,14,16,17,19,1,20,25,2,5]:
for i in bb:#
    with open(f'../../InfOCF/{i}') as f:
        belief_base_string=f.read()
    #belief_base_string = "signature\nb,p,f,w\n\nconditionals\nbirds_ecsqaru_23_paper_45{\n(f|b),\n(!f|p),\n(b|p),\n(w|b)\n}"
    #queries_string = "(f|p),(!f|p)"


    # parse the belief base and the queries
    belief_base = parse_belief_base(belief_base_string)
    #queries = parse_queries(queries_string)


    # select the inference system according to which the inferences are to be performed
    # possible options at this time are 'p-entailment', 'system-z', 'system-w', 'c-inference' and 'lex_inf'
    inference_system = "system-w"

    # instanciate inference operator parameterized by belief_base and inference_system
    #inference_manager = InferenceManager(belief_base, inference_system, pmaxsat_solver='z3',weakly=True)
    inference_manager = InferenceManager(belief_base, inference_system,weakly=True)

    # perform inference on collection of queries
    results = inference_manager.inference(belief_base)


    # results are provided as pandas dataframe
    print(results)


# results can be saved as csv
# uncomment lines below to do so

# import os
# filename = os.path.join('output', 'show_minimal_results.csv')
# results.to_csv(filename)
