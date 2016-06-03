/* 1::Int */
1 + 2 - 3 * 4 / 5;
/* true::Bool */
1 > 3 || 4 <: 5 && !(6 == 7);
/* true::Bool */
0 < 1 && 4 % 2 == 0;
/* (30,true) */
(5 * 6 , 8 < 9);
/* 9 */
pi1 (9 , 8);
/* (3,12) */
pi2 (5+6, (1+2, 3 * 4));
/* 1 */
true in true ? 1 : 2;
/* 2 */
if true then 2 else 1;

/* fun */
def id1 = lambda (Int-> Int; Bool -> Bool) x. x;

/* 6 */
def fab = (mu f (Int -> Int) lambda x . if x <: 1 then 1 else (x * (f (x - 1))));
fab 3;

/* special: true :: Bool */
/* (mu f ( (1 ^ - ( Bool -> Int)) -> Bool ) lambda x . true) (mu t ( 0 -> 1) lambda x . x);*/

/* non-well-defined */
lambda ((A -> A) -> (A -> A))  x . x ;
lambda (A -> A; B->B; C->C) x. x;

/* id */
def id1 = lambda (A -> A) x. x;
def id2 = lambda (A -> A) x. id1 (id1 x);
def id3 = lambda (A -> A) x. (id1 id1) x;
id1 (3+4,1==2);
id2 (3+4,1==2);
id3 (3+4,1==2);

/* even */
def even = lambda (Int -> Bool; (A \ Int) -> (A \Int)) x. x in Int ? (x % 2 == 0) : x;
even 2;
even false;
even 5;

/* map */
/* the following definition does not type because the syntactic   */
/* sugar described in the Appendix E of Part 1 is not implemented */

def map_wrong = lambda ( (A -> B) -> (mu x . ((A,x) v nil)) -> (mu y . ((B,y) v nil)) )  x .  ( mu f ( (mu x . ((A,x) v nil)) -> (mu y . ((B,y) v nil)) ) lambda y .  y in nil ? nil : ((x (pi1 y)), (f (pi2 y))));


/* map written without the syntactic sugar of Appendix E in the Part 1 */
/* using the syntactic sugar it corresponds to writing map as          */
/*  lambda (...) x .                                                   */
/*    mu f (...) lambda y .                                            */
/*      (z = y) in nil ?                                               */
/*         nil :                                                       */
/*         ((x (pi1 z)), (f (pi2 z))));                                */
def map = lambda ( (A -> B) -> (mu x . ((A,x) v nil)) -> (mu y . ((B,y) v nil)) )  x .  ( mu f ( (mu x . ((A,x) v nil)) -> (mu y . ((B,y) v nil)) ) lambda y .( (lambda ( nil -> nil ; (A,(mu x . ((A,x) v nil))) ->  (B,(mu x . ((B,x) v nil))) ) z . z in nil ? nil : ((x (pi1 z)), (f (pi2 z)))) y));

/* map even */
def mapeven = map even;
mapeven (1,(2,nil));

/* */
(mu f1 ( (A -> B, C->D) -> Int) lambda x . 1)  ((mu f2 (Int -> Int; Bool -> Bool) lambda x . x), (mu f2 (Int -> Int; Bool -> Bool) lambda x . x) );
/* */
( mu f ( (Int -> Int) -> Int) lambda x. 0) (mu id (A -> A) lambda x. x) ;

