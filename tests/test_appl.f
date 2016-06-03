/* applications */
 appl (A -> B) -> (mu x. (A,x) v nil) -> (mu x . (B,x) v nil) . (Int -> Bool) v ((R \Int) -> (R \ Int)) ;
 appl (A -> B) -> (mu x. (A,x) v nil) -> (mu x . (B,x) v nil) . (Int -> Bool) ^ ((R \Int) -> (R \ Int)) ;
 appl (((Int -> Int) ^ (Bool -> Bool))-> Int) -> Int . (A -> B) -> Int;
/* */
 appl ((Int v Bool)-> A) -> A . (Int -> Int) ^ (Bool -> Int);
 appl (Int -> Bool) ^ (Int -> Int) . Int;
 appl (Int -> A) -> A . (Int -> Bool) ^ (Int -> Int);
 appl ((A -> B), Int) -> ((mu x. (A,x) v nil) , Int) -> ((mu x . (B,x) v nil) , Int) . (((Int -> Bool) ^ ((R \Int) -> (R \ Int))), Int);
 appl ((A -> B), (C -> D )) -> ((mu x. (A,x) v nil) , (mu x. (C,x) v nil)  ) -> ((mu x . (B,x) v nil) , (mu x. (D,x) v nil)  ) . (((Int -> Bool) ^ ((R \Int) -> (R \ Int))), ((Int -> Bool) ^ ((R1 \Int) -> (R1 \ Int)))  );
 appl ((A -> B), (C -> D )) -> ((A-> B) , (C -> D)) . (((Int -> Bool) ^ ((R \Int) -> (R \ Int))), ((Int -> Bool) ^ ((R1 \Int) -> (R1 \ Int)))  );
 appl ((A -> B) -> t1 ) -> t2 . ((Int -> Bool) ^ ((R \Int) -> (R \ Int))) -> t1;
/* which result to choose */
/* A >= Int, B>= Int, or A >= Int \B , B >= Int \ A ?? */
 appl (A -> Int) ^ (B -> Bool) . Int;
/* can we seperate the union ? */
/* 0 or Int v Bool */
 appl (Int -> Int) v (Bool -> Bool) . A;
/* 0 */
 appl (Int ^ Bool) -> (Int v Bool) . A;
/* OMEGA or Int v Bool */
 appl ((Int -> Int) -> Int) v ((Bool -> Bool) -> Bool) . A -> A;
/* OMEGA */
 appl ((Int -> Int) ^ (Bool -> Bool)) -> (Int v Bool) . A -> A;
/* A or (B,C) */
 appl ((Int , Bool) -> (Bool, Int)) ^ ((A \ (Int, Bool)) -> (A\ (Int, Bool))). (B, C);
/* */
 appl (A -> B) -> (mu x. (A,x) v nil) -> (mu x . (B,x) v nil) . ((Int -> Int) -> (Int -> Int)) ^ ((Bool -> Bool) -> (Bool -> Bool)) ;
 appl (A -> (B^ (Int -> Int))) -> (mu x. (A,x) v nil) -> (mu x . (B,x) v nil) . ((Int -> Int) -> (Int -> Int)) ^ ((Bool -> Bool) -> (Bool -> Bool)) ;

 appl ((Int -> Int) ^ (Bool -> Bool) ^ (string -> (string, string))) -> t . (A -> A) ^ (B -> (B,B));
 appl ( (B , Int) -> (Int, B)) -> B . (Int, A) -> (A, Int);
 appl ( (Int, A) -> (A, Int)) -> (A -> A) . (B, B) -> (B,B);
 appl ( (A, R) -> (R, A)) -> (A -> R) . (B, B) -> (B,B);
 appl (A -> (A,A)) -> A -> A . (B,B) -> B;

/* test whether it needs a union for the domain */
 appl A -> A . (Int v Bool);
 appl (A,Int) -> (Int,A) . ((Int v Bool),Int);
 appl (A,Int) -> (Int,A) . (Int,Int) v (Bool, Int);

 appl (A,B) -> (B,A) . (Int,Bool) v (Bool,Int);
 appl ((A,B),Int) -> (Int,(B,A)) . ((Int,Bool) v (Bool,Int), Int);
 appl ((A,B),Int) -> (Int,(B,A)) . ((Int,Bool) , Int)v ((Bool,Int), Int);

 appl (A -> A) -> (A -> A) . (Int -> Int) v (Bool -> Bool);
 appl ((A -> A),Int) -> (Int,(A -> A)) . ((Int -> Int) v (Bool -> Bool), Int);
 appl ((A -> A),Int) -> (Int,(A -> A)) . ((Int -> Int), Int) v ((Bool -> Bool), Int);

 appl (A -> Int) -> (A -> Int) . ((Int v Bool) -> Int);
 /* the same to the above ... the match has problems */
 appl (A -> Int) -> (A -> Int) . (Int -> Int) ^ (Bool -> Int);
 appl (Int -> A) -> (Int -> A) . (Int -> (Int v Bool));
 /* different from the above */
 appl (Int -> A) -> (Int -> A) . (Int -> Int) v (Int -> Bool);
 
 appl ((A,B) -> Int) -> ((A,B) -> Int) . ((Int, Bool) v (Bool, Int)) -> Int;
/* the same to the above .*/
 appl ((A,B) -> Int) -> ((A,B) -> Int) . ((Int,Bool) -> Int) ^ ((Bool,Int) -> Int);
 appl (Int -> (A,B)) -> (Int -> (B,A)) . (Int -> ((Int,Bool) v (Bool,Int)));
 appl (Int -> (A,B)) -> (Int -> (B,A)) . (Int -> (Int,Bool)) v (Int -> (Bool,Int));

 appl ((A->A) -> Int) -> ((A ->A) -> Int) . ((Int -> Int) v (Bool -> Bool)) -> Int;
/* the same to the above .*/
 appl ((A->A) -> Int) -> ((A->A) -> Int) . ((Int -> Int) -> Int) ^ ((Bool -> Bool) -> Int);
 appl (Int -> (A->A)) -> (Int -> (A->A)) . (Int -> ((Int -> Int) v (Bool -> Bool)));
 appl (Int -> (A->A)) -> (Int -> (A->A)) . (Int -> (Int -> Int)) v (Int -> (Bool -> Bool));

 /* no (s1,s2) <: v_{i} (t1,t2)\theta_i (no maxima decomposition)*/
 appl  ((Int,A -> A) v (A, Bool)) -> (A -> A) . (Int, (Bool -> Bool)v Bool);
 /* unsound (s1,s2) <: (v_{i} t1 \theta_i , v_{i} t2 \theta_i) */
 appl ( (A -> A, Int -> Int) v (Int -> A, Bool)) -> (A -> A) . ( ( ( Int -> Int) v (Bool -> Bool)) ^ (Int -> (Int v Bool)) , (Int -> Int)v Bool);
 /* unsound (s1,s2) <: (v_{i} (v_{l} t_l^1) \theta_i , v_{i} (v_{l} t_1^2) \theta_i) */
 appl ( (Int,Int) v (Bool,Bool)) -> (Int -> Bool) . (Int v Bool, Int v Bool);	
/* t. (s1 v s2) != (t. s1) v (t. s2) */
appl (Int -> Bool) -> (Int -> Bool) . (Int -> A)  v (A -> Bool);
/* implict intersection in t */
appl ((Int, Int -> Int) v (Bool, Bool -> Bool)) -> (Int v Bool) . (Int v Bool, (A -> A));
appl ((Int v Bool, (Int -> Int) ^ (Bool -> Bool)) ) -> (Int v Bool) . (Int v Bool, (A -> A));
/* expand n and m at the same time */
/*appl ( A -> A, (int -> int) ^ (bool -> bool)) -> (A -> A) . ((char -> char) v (B -> B), (B -> B)) ;*/
/* H(n) is not correct */
appl ( (true, (Int -> A)) v (false, (A -> Bool)) ) -> (A -> A) . (Bool, Int -> Bool) ;
appl ( (Nat, (Int -> A)) v ([-- 0], (A -> Bool)) ) -> (A -> A) . (Int, Int -> Bool) ;

/* should not substitute the type variables in the type of function or agruments */
/* (mu x. (B,x)v nil) */
appl (A -> A) . (mu x. (B,x)v nil); 



