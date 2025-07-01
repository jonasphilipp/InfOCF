
grammar CKB;

ckbs: signature conditionals+;

signature:
    NEWLINE* 'signature' NEWLINE+ myid;

myid:
	num=ID ',' myid
        |num=ID NEWLINE
	;


conditionals:
	 NEWLINE* 'conditionals' NEWLINE+ name=ID NEWLINE*  '{' NEWLINE*  '}' NEWLINE*
	| NEWLINE* 'conditionals' NEWLINE+ name=ID NEWLINE*  '{' NEWLINE* condition '}'  NEWLINE* conditionals*
	;

condition:
	 '(' consequent=formula '|' antecedent=formula ')' ',' NEWLINE* condition
	| '(' consequent=formula '|' antecedent=formula ')' NEWLINE*
        ;


formula:
	 '!' formula 				#Negation
	| left=formula ',' right=formula				#And
	| left=formula ';' right=formula				#Or
	| '(' formula ')'				#Paren
	| atom=ID 				#Var
	;


ID: ([A-Z]|[a-z])([0-9]|[a-z]|[A-Z]|'_'|'-')* ;
WS: (' '|'\t') -> skip;
COMMENT: '//' ~( '\r' | '\n' )* -> skip;
BLOCKCOMMENT : '/*' .*? '*/' -> skip;
NEWLINE: '\r' '\n' | '\n' | '\r' ;
