
/* test_empty_list */

 subtype        Int <: 1 ;
 subtype        a ^ Int <: a ;
 subtype        1 <: 1 ;
 subtype         0 <: 0 ;
 subtype         0 <: 1 ;

     subtype    Nat <: Int ;
     subtype    [1 -- 5 ] <: [ 0 -- ] ;
     subtype    [0 -- ] <: Int ;
     subtype    [1 -- 5 ] <: [ 1 -- ] ;
     subtype    [1 -- 5 ] <: [ 1 -- 5 ] ;

     subtype    1 -> a <: 1 ;
     subtype    a -> b ^ Int <: a -> b ;

     subtype    a -> b <: a -> b ;
     subtype    1 -> a <: 1 -> 1 ;
     subtype    a -> b <: 0 -> 1 ;
     subtype    (a -> c) ^ (b -> c) <: (a v b) -> c ;
     subtype    (a v b) ^ (a v c) <: a v ( b ^ c) ;
     subtype    a v ( b ^ c) <: (a v b) ^ (a v c) ;
     subtype    (a,b) ^ (c,d) <: ((a ^ c) , (b ^ d)) ;
     /*subtype    mu x . t ^ x <: mu x . t ^ t ^ x ;*/
     subtype    ( a , b v c) <: (a,b) v (a,c) ;
     subtype    mu x . Int -> (Nat , x) <: mu x . Nat -> (Int , x) ;
     subtype     mu x . (a,x) <: mu y . (a,y) ; 


/* test_not_empty_list */

     subtype    1 <: Int ;
     subtype    1 <: 0 ;

     subtype    a -> b <: a ;
     subtype    1 -> a <: 0 ;
     subtype    1 -> a <: 1 -> 0 ;
     subtype    a -> b <: a -> c ;

     subtype    Int <: [ 0 -- ] ;
     subtype    [1 -- 5 ] <: [ 1 -- 4 ] ;
     subtype    Int <: Nat ;


/* test_variable_empty_list */ 

     subtype    X <: 1 ;
     subtype    A -> B <: 0 -> 0 ;
     subtype    A -> B <: 0 -> 1 ;
     subtype    A <: A ;
     subtype    A ^ (A,a) <: A ;
     subtype    (A,B) ^ (C,D) <: ((A ^ C) , (B ^ D))  ;
     subtype    (A v B) ^ (A v C) <: A v ( B ^ C) ;
     subtype    A v ( B ^ C) <: (A v B) ^ (A v C) ;
     subtype    (A -> C) ^ (B -> C) <: (A v B) -> C ;


/* test_variable_not_empty */
     subtype    X <: 0 ;        
     subtype    A -> B <: 1 -> 1 ;

      /* There are not rules to satisfy this constraint even if set theoretically this is true  */
     subtype    ( a , X ) <: (a , - a) v ( X , a ) ;

     subtype    A <: B ;
     subtype    A <: c ;
     subtype    A ^ (A,a) <: c ;

/* empty examples in paper */
	 /* (1) the meta-theoretic property: (A -> C) ^ (B -> C) ~ (A v B) -> C  */
	subtype (A -> C) ^ (B -> C) <: (A v B) -> C ;
	subtype (A v B) -> C <: (A -> C) ^ (B -> C) ;
	
	 /* (2) the common distributive laws: ((A v B),C) ~ (A,C) v (B,C)  */
	subtype ((A v B),C) <: (A,C) v (B,C) ;
	subtype (A,C) v (B,C) <: ((A v B),C) ;
	
	 /* (3) combination (1) and (2)  */
	subtype ((A,C) -> D1) ^ ((B,C) -> D2) <: (A v B,C) -> (D1 v D2) ;

	 /* (4) A-list  */
	 /* A-list contains the A-list with an even number of elements  */
	subtype mu x. ((A, (A,x)) v nil) <: mu x. ((A,x) v nil) ;
	 /* A-list contains the A-list with an odd number of elements  */
	subtype mu x. ((A, (A,x)) v (A, nil)) <: mu x. ((A,x) v nil) ;
	 /* A-list is equivalent to the union of the two above  */
	subtype (mu x. ((A, (A,x)) v nil)) v (mu x. ((A, (A,x)) v (A, nil))) <: mu x. ((A,x) v nil) ;
	subtype mu x. ((A,x) v nil) <: (mu x. ((A, (A,x)) v nil)) v (mu x. ((A, (A,x)) v (A, nil))) ;

	 /* (5) an example of non-trivial containment  */
	subtype A ^ (A,t) <: A ;

	 /* (6) non-trivial containments involving arrows  */
	subtype 1 -> 0 <: A -> B ;
	subtype A -> B <: 0 -> 1 ;

	 /* (7) a proof of Pierce's law  */
	 /* -A v B is equivalent to A => B (classic proposition logic)  */
	subtype 1 <: -( -( -A v B) v A) v A ;

	 /* (8) the fundamental property for all non-empty set: B ~ (B ^ A) v (B ^ -A)  */
	subtype (B ^ A) v (B ^ -A) <: B ;
	subtype B <: (B ^ A) v (B ^ -A) ;
	 /* then  */
	subtype 1 <: - (-((B ^ A) v (B ^ -A)) v 0) v (-B v 0) ;

	 /* (11) subtle relation whose meaning is not clear at first sight  */
	subtype (A1 -> B1) <: ((A1 ^ A2) -> (B1 ^ B2)) v - (A2 -> (B2 ^ -B1)) ;
	
	 /* (13) some potentially looping examples  */
	subtype (mu x . ((a,(a,x)) v nil)) ^ X <: mu y.((a,y) v nil) ;
	subtype mu x . (A ^ (A, x)) <: 0  ;
	subtype mu x . (A ^ ((A, x) v nil)) <: mu y . ((A, y) v nil)  ;
	subtype mu x . (( a, (a,x))  ^ X) <:  mu y. (a,y) ;
	subtype mu x . (((A1,A2) v A) ^ (((A1,A2) v A), x)) <: 0 ;
	subtype mu x . (((A1,A2) v A) ^ ((((A1,A2) v A), x) v nil)) <: mu y . ((((A1,A2) v A), y) v nil)  ;
	subtype mu x . (((A1 -> A2) v A) ^ ((((A1 -> A2) v A), x) v nil)) <: mu y . ((((A1 -> A2) v A), y) v nil)  ;
        subtype mu x . (mu y1 . ((A, y1) v nil) ^ ((mu y1 . ((A, y1) v nil), x) v nil)) <: mu y . ((mu y1 . ((A, y1) v nil), y) v nil)  ;
	 /* without folding, it takes more time  */
	subtype mu x . (B ^ ((A1 -> A2) v A ) ^ ((((A1 -> A2) v A), x) v nil)) <: mu y . ((((A1 -> A2) v A), y) v nil) ;  /*  */
        subtype mu x . (B ^ ((A1 -> A2) v A ) ^ ((((A1 -> A2) v A), x) v nil)) ^ -( mu y . ((((A1 -> A2) v A), y) v nil)) <: 0 ;  /*  */
	subtype mu x . (B ^ ((A1 -> A2) v A ) ^ ((((A1 -> A2) v A), x) v nil)) ^ -( mu y . (B ^((((A1 -> A2) v A), y) v nil))) <: 0 ;  /*  */
	 /* it needs to propagate the substitution informations  */        
	subtype mu x . (A ^ ((A,(A,x)) v nil)) <: mu y . ((A, y) v nil)  ;

	 /* (14) the other examples  */
	subtype (a^b, a) <: 0 ;


/* nonempty examples in paper */
	 /* (5) type variables are not basic types, the follow example doesn't hold  */
	subtype A ^ (A,t) <: t1 -> t2 ;

	 /* (9) no stuttering since the following example returns false  */
	subtype (nil, A) <: (nil, -nil) v (A, nil) ;

	 /* (10) the necessity for the tricky substitution ((X1, X2) v A)/A : the following example is wrong if (b v (b,t))/A  */
	subtype (A,t) ^ A <: ((1,1),t) ; 

	 /* (13) notice that the following example does not hold  */
	subtype (-A -> B) <: ((1 -> 0) -> B) ;

	 /* (14) some potentially looping examples  */
	subtype mu x . (A ^ ((A, x) v nil)) <: 0  ;
	subtype mu x . (((A1,A2) v A) ^ ((((A1,A2) v A), x) v nil)) <: 0 ;
 subtype  ((mu x . (( Int, x) v nil)) -> (mu x . ((Bool , x) v nil))) ^ ( (mu x . (((A \ Int), x) v nil)) -> (mu x . (((A \ Int), x) v nil)) )  <: ((mu x . (( Int, x) v nil)) -> (mu x . ((Bool , x) v nil))) ^ ( (mu x . (((A \ Int), x) v nil)) -> (mu x . (((A \ Int), x) v nil)) ) ^ ( (mu x . (((A v Int), x) v nil)) -> (mu x . ((((A\ Int) v Bool), x) v nil)) );

/* interesting subtyping relations for arrows */

/*(1) (A -> C) ^ (B -> C) == (A v B) -> C */
subtype (A -> C) ^ (B -> C) <: (A v B) -> C;
subtype (A v B) -> C <: (A -> C) ^ (B -> C);

/*(2) (A -> C) v (B -> C) <= (A ^ B) -> C */
subtype (A -> C) v (B -> C) <: (A ^ B) -> C;
subtype (A ^ B) -> C <: (A -> C) v (B -> C);

/*(3) (C -> A) ^ (C -> B) == C -> (A ^ B)  */
subtype (C -> A) ^ (C -> B) <: C -> (A ^ B);
subtype C -> (A ^ B) <: (C -> A) ^ (C -> B);

/*(4) (C -> A) v (C -> B) <= C -> (A v B)  */
subtype (C -> A) v (C -> B) <: C -> (A v B);
subtype C -> (A v B) <: (C -> A) v (C -> B);


