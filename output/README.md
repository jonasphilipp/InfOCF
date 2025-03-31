# Benchmarking results format 'foiks_longest_cqueries.csv' and 'foiks_tough_queries.zip'
Every benchmark instance of 'foiks_longest_cqueries.csv' is indenified by 4 numbers: \
(signature size,amount of conditonals,index ckb,index query). \
'foiks_tough_queries.zip' contains the corresponding CKB's and query files.\
For example: (signature size,amount of conditonals,index ckb,index query) = (60,60,46,3) \
means that this result refers to 'randomTest_60_60_46.cl' and the third query in 'randomQueries_60_60_46.cl' 
which are contained in the file 'foiks_tough_queries.zip' after unzipping.
All times refer only to c-inference. \
While they do also contain a corresponding result for System Z and System P, 
the times for those system were not measured.


## Naming legend for 'foiks_longest_cqueries.csv'
### compile time ckb (ms) 
Refers to the combined time of 'compiling the CKB' and 'optimizing the CKB' using a maxsat-solver.
Time in miliseconds, indicated with 'ms' in parenthesis.

### compile time query (ms)	
Refers to the combined time of 'compiling the query' and 'optimizing the query' using a maxsat-solver.
Time in miliseconds, indicated with 'ms' in parenthesis.

### solve time query (ms)	
Refers to the time it took to solve the CSP that corresponds to the query and the CKB.
Time in miliseconds, indicated with 'ms' in parenthesis.

### result c representation	
Result of the c-inference that corresponds to the query and the CKB, obtained by solving the CSP.
'sat' means the query does not follow.
'unsat' means the query does follow.

### result system z	
Result of the 'System Z'-inference that corresponds to the query and the CKB.
'False' means the query does not follow.
'True' means the query does follow.
Timing was not measured for this inference, as it was so fast we did not consider it relevant/interesting enough.

### result system p
Result of the 'System P'-inference that corresponds to the query and the CKB.
'False' means the query does not follow.
'True' means the query does follow.
Timing was not measured for this inference, as it was so fast we did not consider it relevant/interesting enough.

## Naming legend in 'foiks_tough_queries.zip'
### 'randomTest_a_b_c.cl'
Contains a CKB. \
'a' refers to the number of different variables in the CKB \
'b' refers to the number of conditionals in the CKB \
'c' is an index number used to distinguish CKB's with equal number of variables and conditionals

### 'randomQueries_a_b_c.cl'
Contains queries compatibale with 'randomTest_a_b_c.cl'



# Benchmarking results format cinf_sum_longest_queries.csv' and 'sum_archive.zip'
'cinf_sum_longest_queries.csv' and 'sum_archive.zip' are strucutred in a similiar way. 



## Naming legend for 'cinf_sum_longest_queries.csv'

### preprocessing_time	
Refers to the combined time of 'compiling the CKB' and 'optimizing the CKB' using a maxsat-solver.
### inference_time	
Refers to the time it took to solve the CSP that corresponds to the query and the CKB.
### translation_time	
Refers to the time it took to transate the internal representation of the CSP into an file in the smt2 format
### preprocessing_timeout	
indicates whether preprocessing ('compilation and optimization') hitted the timeout limit
### inference_timeout	
indicates whether solving the CSP hitted the timeout limit
### belief_base
Filename of the belief base 
