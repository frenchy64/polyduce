/* type match: s / t ==> \exists \sigma such that s\sigma... <= t \sigma...*/
/* example 1 */
 match (Int -> Bool) ^ ((R \ Int) -> (R \ Int)) / (A -> B) ;
 match (Int -> Bool) / (A -> B) ;
 match ((R \ Int) -> (R \ Int)) / (A -> B) ;
 match (Int v (R \ Int)) -> (Bool v (R \ Int)) / (A -> B) ;
/* example 2 */
 match (Int -> Int) ^ (Bool -> Int) / (Int v Bool) -> A ;
 match (Int -> Int) / (Int v Bool) -> A;
 match (Bool -> Int) / (Int v Bool) -> A;
 match (Int v Bool) -> (Int v Int) / (Int v Bool) -> A;
/* example 3 */
 match -(false -> Bool) ^ - (true -> Int) / -(Bool -> A);
/* example 4 : (t1 -> s2) ^ (t2 -> s2) < (t1 ^ t2) -> (s1 ^ s2) */
 match ((Int -> Int) -> (Bool -> Bool)) ^ ((Bool -> Bool) -> (Int -> Int)) / A -> ((Int -> Int) ^ (Bool -> Bool));
 match ((Int -> Int) -> (Bool -> Bool)) / A -> ((Int -> Int) ^ (Bool -> Bool));
 match ((Bool -> Bool) -> (Int -> Int)) / A -> ((Int -> Int) ^ (Bool -> Bool));
 match ((Int -> Int) v (Bool -> Bool)) -> ((Bool -> Bool) v (Int -> Int)) / A -> ((Int -> Int) ^ (Bool -> Bool));
/* example 5 */
 match ((Int , Int) v (Bool , Bool)) -> Int / (A , B) -> Int ;
 match -((Int , Int) v (Bool , Bool))  / -(A , B) ;
/* example 6 */
 match (Int , Bool) -> Int / ((A \ ((1 , 1) v (0 -> 1))) -> Int) v ((B , C) -> Int) ;
/*>> Seleted: [[TVar 0A <= (((0 -> 1) v (int , (Singleton tt v Singleton ff))) v (1 , 1))]] unwanted!! */
/* no matter what is chosed, the domain will be empty!! */
/* example 7 */
 match ( ((Int -> Int) , Int) ^ ((Bool -> Bool) , Int)) / ((A -> Int) , Int);

 match -((Int,Bool) v A) / -(B,C) ;

match Int / A v B;
match (Int, Bool) / (A,A) v(B,B);
match (Int, Bool) / (A, B) v (C,D);


 match (Int , (Int v Bool)) / (A, Int) v (B, Bool);
 match ((Int, Int) , (Int v Bool)) / (A, Int) v ((B, Int), Bool);
 match ((Int, Int) , (Int v Bool)) / ((A, Int), Int) v ((B, Int), Bool);

 match (Int, Int) / A v (B, C);

 match A -> B/ (Int -> Int) ^ ((Bool) -> (Bool));
 match A -> A/ (Int -> Int) ^ ((Bool) -> (Bool));
 match (Int, B->B) / (A, (Int -> Int) ^ (Bool -> Bool));

/* to expand s (or t) */
/*(1) basic cases */
match (Int -> Int ) v (Bool -> Bool) / A -> A;
match A -> A / (Int -> Int ) ^ (Bool -> Bool);
/* failure cases */
match Int -> Bool / (Int -> A) ^ (A -> Bool);
match (Int -> A) v (A -> Bool) / Int -> Bool;
/*(2) implicit cases (due to the decompostion of product) */
match (t1 v t2, A -> A) / (t1, Int -> Int) v (t2, Bool -> Bool) ;
match (t1 v t2, Int -> Bool) / (t1, Int -> A) v (t2, A -> Bool) ;
/* failture */
match ((t1 -> t1) ^ (t2 -> t2), Int -> Bool) / (t1 -> t1, Int -> A) ^ (t2 -> t2, A -> Bool) ;
/*(3) involved arrow cases */
match t -> (A -> A) / t -> ( (Int -> Int ) ^ (Bool -> Bool) );
/* is equivalent to  */
match t -> (A -> A) / ( t -> (Int -> Int ) ) ^ ( t -> (Bool -> Bool) );
/* but how about ?? */
match t -> (A -> A) / t -> ( ((Int -> Int ) ^ (Bool -> Bool)) v ((char -> char ) ^ (string -> string)) );
/* // */
match ( A -> A ) -> t  / ( (Int -> Int ) v (Bool -> Bool) ) -> t ;
/* is equivalent to  */
match ( A -> A ) -> t / ( (Int -> Int ) -> t )  ^ ( (Bool -> Bool)-> t );

/* more involved ??? */
match t -> (t1 v t2, A -> A) / t-> ((t1, Int -> Int) v (t2, Bool -> Bool)) ;
match ( (t1, Int -> A) v (t2, A -> Bool) ) -> t / ((t1 v t2, Int -> Bool)) -> t;

/* needs two substitutions for basic types?? */
/* no false <= A <= (-Int v Nat) */
match (A ^ Int) v (-A ^ Bool) / Nat v true; 
match (A -> Int, Int) v ((Int, true) ^ A) / (false, false) v ( (1 -> 0) -> Int, Int);
match A v (-A, Bool) / Int v (-(1,1), Bool);
/* substitute A twice, B once */
match (A -> (Int -> Int)) v ((Bool -> Bool) -> A) / ((Bool -> Bool) -> (Int -> Int)) v ( (((Bool -> Bool) v B) v (Int -> Int)) -> (((Int -> Int) ^ B) v (Bool -> Bool)) );
/* omega */
match ((A -> (Int -> Int)) v ((Bool -> Bool) -> A)) / ((Bool -> Bool) -> (Int -> Int)) v ( (B -> B) -> (( Bool -> Bool) ^ (Int -> Int)) );
/* A twice, B once(B = 0 or B = Int) */
match ((A -> (Int -> Int)) v ((Bool -> Bool) -> A))  / ((Bool -> Bool) -> (Int -> Int)) v ( (( Bool -> Bool) v (Int -> Int)) -> ((B -> B) v (Bool -> Bool)) );
/* A twice, B twice */
match ((A -> (Int -> Int)) v ((Bool -> Bool) -> A) v (Bool, Bool) )  / ((Bool -> Bool) -> (Int -> Int)) v ( (( Bool -> Bool) v (Int -> Int)) -> ((B -> B) v (Bool -> Bool)) ) v (B , B);

/* m deponds m? */
/* fails */
match (A, (Int -> Int) -> (char -> char)) v (string -> string, A -> (char -> char)) / (Bool -> Bool, (Int -> Int) -> (char -> char)) v (string -> string, (char -> char) -> (char -> char));
/* m = 3 */
match (A, (string -> string) -> (char -> char)) v (string -> string, A -> (char -> char)) / (Bool -> Bool, (string -> string) -> (char -> char)) v (string -> string, (char -> char) -> (char -> char));

/* n =1, m = 3, m deponds on type s!! */
match (((Bool -> Bool) ^ (char -> char)) -> (Bool -> Bool), (Int -> Int) -> (B -> B)) / (A -> (Bool -> Bool), (A -> A));
/* m = 2 */
match ((Bool -> Bool) ^ (Int -> Int)) -> (B -> B) / A -> A;
/* fail */
match ((Bool -> Bool) -> A, (A -> (Int -> Int))) / ((Bool -> Bool) -> ((Bool -> Bool) ^ (char -> char)), (B -> B) -> (Int -> Int) ) ;
/* fail */
match A -> A / (B -> B) -> ((Bool -> Bool) ^ (Int -> Int));

/* n = 1, m = 2 or n = 2, m = 1 */
match (Int, ((Int -> Int) ^ (Bool -> Bool))-> Int) v (Bool, Bool -> (B -> B)) / (Int, A -> Int) v (Bool, Bool -> A);
match (A -> Int) v (Bool, A) / (((Int, Int -> Int) v (Bool, Bool -> Bool)) -> Int) v (Bool, (Int, B -> Int) v (Bool, Bool -> B));

/* A -> A <= (Int -> Int) ^ (Bool -> Bool) */
/* A -> A <= B <= (Int -> Int) ^ (Bool -> Bool) */
/* B -> B  <= (A -> A) -> ((Int -> Int) ^ (Bool -> Bool)) */
/* B -> B <= C <= (A -> A) -> ((Int -> Int) ^ (Bool -> Bool)) */
match C -> C / (B -> B) -> ((A -> A) -> ((Int -> Int) ^ (Bool -> Bool)));

match (mu x. ((B,x) v nil)) -> (mu x. ((B,x) v nil)) / (A,A) -> A;
