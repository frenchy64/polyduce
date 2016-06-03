/* Some simple subtyping tests                           */
/* (when the subtyping s<:t does not hold the algorithm) */
/* (returns False, and a "witness", that is, a value   ) */
/* (that inhabits s\t, together with an assignment of  ) */
/* (the variables in s\t that better shows why the     ) */
/* (witness inhabits the type                          ) */

subtype (A -> Bool, B -> B) <: (Int v Bool -> Int, A -> B);
subtype Int -> Int <: A -> A;
subtype Int -> Int <: 0 -> 1;
subtype (A -> C) ^ (B -> C) <: (A v B) -> C ;
subtype (A v B) -> C <: (A -> C) ^ (B -> C) ;


/* Simple type level application of map to pretty                           */
/* pretty :: Int -> String ;                                                */
/* map ::  ( (A -> B) -> (mu x . ((A,x) v nil)) -> (mu y . ((B,y) v nil)) ) */

appl  ( (A -> B) -> (mu x . ((A,x) v nil)) -> (mu y . ((B,y) v nil)) ) . Int -> String;


/* a function with the type of map  applied   */
/* to and argument with the type of even      */ 
/* even :: (Int -> Bool)  ^ ( A\Int -> A\Int) */

appl ( (A -> B) -> (mu x . ((A,x) v nil)) -> (mu y . ((B,y) v nil)) ) . (Int -> Bool)  ^ ( A\Int -> A\Int);



/* map as written in both Part 1 and Part 2. NOTA BENE:             */
/* the following definition does not type because the syntactic     */
/* sugar described in the Appendix E of Part 1 (boldface belong     */
/* symbol) is not implemented                                       */

def map_wrong = lambda ( (A -> B) -> (mu x . ((A,x) v nil)) -> (mu y . ((B,y) v nil)) )  x .  ( mu f ( (mu x . ((A,x) v nil)) -> (mu y . ((B,y) v nil)) ) lambda y .  y in nil ? nil : ((x (pi1 y)), (f (pi2 y))));


/* map written WITH the syntactic sugar of Appendix E in Part 1      */
/* notice the "y = y" in the type case                               */

def map = lambda ( (A -> B) -> (mu x . ((A,x) v nil)) -> (mu y . ((B,y) v nil)) )  x .  ( mu f ( (mu x . ((A,x) v nil)) -> (mu y . ((B,y) v nil)) ) lambda y .  y = y  in nil ? nil : ((x (pi1 y)), (f (pi2 y))));

/* map written using syntactic sugar for lists */
def map = lambda ( (A -> B) -> ([ A ] -> [ B ]) )  x . mu f ( [ A ] -> [ B ] ) lambda y . y = y in nil ? (nil) : ((((x) (pi1 (y))) , ((f) (pi2 (y)))));

/* map written WITHOUT using the syntactic sugar of Appendix E in     */
/* Part 1; using the syntactic sugar it corresponds to writing map as */
/*  lambda (...) x .                                                  */
/*    mu f (...) lambda y .                                           */
/*      (z = y) in nil ?                                              */
/*         nil :                                                      */
/*         ((x (pi1 z)), (f (pi2 z))));                               */

def mapfull = lambda ( (A -> B) -> (mu x . ((A,x) v nil)) -> (mu y . ((B,y) v nil)) )  x .  ( mu f ( (mu x . ((A,x) v nil)) -> (mu y . ((B,y) v nil)) ) lambda y .( (lambda ( nil -> nil ; (A,(mu x . ((A,x) v nil))) ->  (B,(mu x . ((B,x) v nil))) ) z . z in nil ? nil : ((x (pi1 z)), (f (pi2 z)))) y));


/* even */

def even = lambda (Int -> Bool; (A \ Int) -> (A \Int)) x. x in Int ? (x % 2 == 0) : x;


/* map even */
def mapeven = map even;


/* Some function of type (Int -> Int)-> Int -> Int  */

def f = lambda ((Int -> Int)-> Int -> Int) g. lambda (Int -> Int) x. g (x+1) ;


/* polymorphic identity */

def id = lambda (A -> A) x. x ;

def fid = f id ;


/* application f id */

appl ((Int -> Int) -> Int -> Int) . (A -> A) ;


/* appl g id */

appl (((Int -> Int) -> Int -> Int) ^ (( Bool -> Bool) -> Bool -> Bool)) . (A -> A);


/* random tests */

fid false;
id 1 ;
f id 1;

even 2;
even false;
even 5;

/* map even applied to a list containing only integer values */

mapeven (1,(2,nil));


/* map even applied to a list containing also non integer values */

mapeven (1,(id,(2,nil)));

/* fold applied to some overloaded function */

appl  ( (A -> B -> B)-> (mu x . ((A, x) v nil)) -> B -> B ) . ((Int -> Int -> Int) ^ (Bool -> Int -> Int) ) ;

/* The result is: */
/*    >> Applying ((A -> (B -> B)) -> ((mu x . ((A , x) v nil)) -> (B -> B))) to ((Int -> (Int -> Int)) ^ (Bool -> (Int -> Int))) : (((nil -> (B -> B)) ^ ((mu x . (((Int v Bool) , x) v nil)) -> (0 -> 0))) ^ ((mu x . (((Int v Bool) , x) v nil)) -> (Int -> Int)))*/
/*     >> simplifying as :                                      */
/* we obtain an intersection of three types:                    */
/* the first type is [ (Int v Bool)* ] -> Int -> Int:           */
/*    ((((mu x . (((Int v Bool) , x) v nil)) -> (Int -> Int)) ^ */
/* the second is the case where the accumulator is 0 and        */
/* therefore the result will be 0                               */
/*    ((mu x . (((Int v Bool) , x) v nil)) -> (0 -> 0))) ^      */
/* the third case is when the initial list is empty, then the   */
/* accumulator is returned unchanged whatever its type is       */
/*     nil -> (B -> B)                                          */


/* application of an overaloaded function to a polymorphic one  */

appl (((Int -> Int) ^ (Bool -> Bool)) -> (Int v Bool) -> (Int v Bool)) . (A -> A) ;
