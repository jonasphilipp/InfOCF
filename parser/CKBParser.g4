parser grammar CKBParser;
options{ tokenVocab=CKBLexer;}
ckbs: ckb;

ckb: signature conditionals+;

signature: 
	SIGN  myid (COMMA myid)*
	;
myid :  
	num=ID 
	;

conditionals: 
	COND  name=ID  LBRA conditional (COMMA  conditional)*  RBRA
	;


conditional: 
	LPAR consequent=formula  SEP antecedent=formula RPAR #StrongConditional
	|LL consequent=formula  SEP antecedent=formula RL #WeakConditional
	;

formula: NOT formula    			#Negation
	| left=formula COMMA right=formula      #And
	| left=formula OR right=formula       	#Or
	| LPAR formula RPAR	   		#Paren
	| atom=ID 				#Var
	; 

