## Benchmarking results format
Every benchmark instance of 'folks_longest_cqueries.csv' is indenified by 4 numbers: (signature size,amount of conditonals,index ckb,index query).
'folks_tough_queries.zip' contains the corresponding CKB's and query files.
For example: (signature size,amount of conditonals,index ckb,index query) = (60,60,46,3)
means that this result refers to 'randomTest_60_60_46.cl' and the third query in 'randomQueries_60_60_46.cl'

'cinf_sum_longest_queries.csv' and 'sum_archive.zip' are strucutred in a similiar way.


## Naming scheme
### 'randomTest_a_b_c.cl'
Contains a CKB. \
'a' refers to the number of different variables in the CKB \
'b' refers to the number of conditionals in the CKB \
'c' is an index number used to distinguish CKB's with equal number of variables and conditionals

### 'randomQueries_a_b_c.cl'
Contains queries compatibale with 'randomTest_a_b_c.cl'


