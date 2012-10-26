/* Examples for testing */

 lambda X. lambda x:X. x; 
 (lambda X. lambda x:X. x) [All X.X->X]; 

lambda x:Top. x;
 (lambda x:Top. x) (lambda x:Top. x);
(lambda x:Top->Top. x) (lambda x:Top. x);


lambda X<:Top->Top. lambda x:X. x x; 

