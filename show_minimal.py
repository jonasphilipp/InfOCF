from parser.Wrappers import parse_belief_base, parse_queries
from inference.inference_operator import InferenceOperator


# belief base and queries provided dircetly as string. providing a filepath of belief base and 
# queries is also viable. see show.py for demonstration
belief_base_string = "signature\nb,p,f,w\n\nconditionals\nbirds_ecsqaru_23_paper_45{\n(f|b),\n(!f|p),\n(b|p),\n(w|b)\n}"
queries_string = '(f|p),(!f|p)'


# parse the belief base and the queries
belief_base = parse_belief_base(belief_base_string)
queries = parse_queries(queries_string)




# select the inference system according to which the inferences are to be performed
# possible options at this time are 'p-entailment', 'system-z', 'system-w', 'c-inference' and 'lex_inf'
inference_system = 'c-inference'

class Dummy:
	def __init__(self, conditionals):
		self.conditionals=conditionals
		self.name = ''
	
# instanciate inference operator parameterized by belief_base and inference_system
inference_operator = InferenceOperator(belief_base, inference_system)
queries = Dummy(queries)
# perform inference on collection of queries
results = inference_operator.inference(queries)
T = results['index']==1
print((results[T]['result'][0]))





# results are provided as pandas dataframe
#print(results)


# results can be saved as csv
# uncomment lines below to do so

#import os
#filename = os.path.join('output', 'show_minimal_results.csv')
#results.to_csv(filename)
