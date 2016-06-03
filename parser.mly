/*  
 *  Yacc grammar for the parser.  The files parser.mli and parser.ml
 *  are generated automatically from parser.mly.
 */

%{
open Support.Error
open Support.Pervasive
open Ast
let tybinding = Hashtbl.create 17
%}

/* ---------------------------------------------------------------------- */
/* Preliminaries */

/* We first list all the tokens mentioned in the parsing rules
   below.  The names of the tokens are common to the parser and the
   generated lexical analyzer.  Each token is annotated with the type
   of data that it carries; normally, this is just file information
   (which is used by the parser to annotate the abstract syntax trees
   that it constructs), but sometimes -- in the case of identifiers and
   constant values -- more information is provided.
 */

/* Keyword tokens */
%token <Support.Error.info> LAMBDA
%token <Support.Error.info> MU
%token <Support.Error.info> PI1
%token <Support.Error.info> PI2
%token <Support.Error.info> LET
%token <Support.Error.info> IN
%token <Support.Error.info> TRUE
%token <Support.Error.info> FALSE
%token <Support.Error.info> BOOL
%token <Support.Error.info> NAT
%token <Support.Error.info> INT
%token <Support.Error.info> TYPE
%token <Support.Error.info> NIL
/*%token <Support.Error.info> UNIT
%token <Support.Error.info> UUNIT*/
%token <Support.Error.info> CHECK
%token <Support.Error.info> MATCH
%token <Support.Error.info> SUBTYPE
%token <Support.Error.info> APPL
%token <Support.Error.info> IF
%token <Support.Error.info> THEN
%token <Support.Error.info> ELSE
%token <Support.Error.info> DEF


/* Identifier and constant value tokens */
%token <string Support.Error.withinfo> UCID  /* uppercase-initial */
%token <string Support.Error.withinfo> LCID  /* lowercase/symbolic-initial */
%token <int Support.Error.withinfo> INTV


/* Symbolic tokens */
%token <Support.Error.info> TIMES
%token <Support.Error.info> ARROW
%token <Support.Error.info> DIV
%token <Support.Error.info> MOD

%token <Support.Error.info> ADD
%token <Support.Error.info> MINUS

%token <Support.Error.info> AND
%token <Support.Error.info> OR
%token <Support.Error.info> NEG


%token <Support.Error.info> CUP
%token <Support.Error.info> CAP
%token <Support.Error.info> SETMINUS
%token <Support.Error.info> NOT

%token <Support.Error.info> LPAREN
%token <Support.Error.info> RPAREN
%token <Support.Error.info> LSQUARE
%token <Support.Error.info> RSQUARE

%token <Support.Error.info> BOUNDED
%token <Support.Error.info> DOT
%token <Support.Error.info> COMMA
%token <Support.Error.info> QUES
%token <Support.Error.info> COLON

%token <Support.Error.info> EQEQ
%token <Support.Error.info> LT
%token <Support.Error.info> GT
%token <Support.Error.info> LE
%token <Support.Error.info> GE
%token <Support.Error.info> NEQ
%token <Support.Error.info> EQ
%token <Support.Error.info> SEMI
%token <Support.Error.info> EOF

%left DOT
%left COMMA QUES COLON
%left OR
%left AND
%left LT GT LE GE EQEQ NEQ
%left ADD MINUS
%right ARROW		/* lowest precedence */
%left TIMES DIV MOD		/* lowest precedence */
%left CUP CAP SETMINUS	/* medium precedence */
%nonassoc NOT NEG		/* highest precedence */



/* ---------------------------------------------------------------------- */
/* The starting production of the generated parser is the syntactic class
   toplevel.  The type that is returned when a toplevel is recognized is
     Syntax.context -> (Syntax.command list * Syntax.context) 
   that is, the parser returns to the user program a function that,
   when given a naming context, returns a fully parsed list of
   Syntax.commands and the new naming context that results when
   all the names bound in these commands are defined.

   All of the syntactic productions in the parser follow the same pattern:
   they take a context as argument and return a fully parsed abstract
   syntax tree (and, if they involve any constructs that bind variables
   in some following phrase, a new context).
   
*/

%start toplevel topcommand
%type <Ast.command list> toplevel
%type <Ast.command> topcommand
%%

/* ---------------------------------------------------------------------- */
/* Main body of the parser definition */

/* The top level of a file is a sequence of commands, each terminated
   by a semicolon. */
toplevel :
  | EOF
      { [] }
  | command SEMI toplevel
      { $1::$3 }
;

topcommand : 
  | command { $1 }
  | command EOF { $1 }
;
  
/* A top-level command */
command : /* Ast.command */
  | Expr 
      { Eval(exprInfo $1, "_", $1) }
  | DEF LCID EQ Expr
      { Eval($1, $2.v, $4)}
  | MATCH Type DIV Type 
      { let ty1 = Hashtbl.clear tybinding; $2 tybinding in
        let ty2 = Hashtbl.clear tybinding; $4 tybinding in 
        MatTy($1, ty1, ty2)}
  | SUBTYPE Type LE Type 
      { let ty1 = Hashtbl.clear tybinding; $2 tybinding in
        let ty2 = Hashtbl.clear tybinding; $4 tybinding in 
        SubTy($1, ty1, ty2)}
/*  | CHECK Type GE Type 
      { let ty1 = Hashtbl.clear tybinding; $2 tybinding in
        let ty2 = Hashtbl.clear tybinding; $4 tybinding in 
        SubTy($1, ty2, ty1)}*/
  | APPL Type DOT Type 
      { let ty1 = Hashtbl.clear tybinding; $2 tybinding in
        let ty2 = Hashtbl.clear tybinding; $4 tybinding in 
        AppTy($1, ty1, ty2)}
  | CHECK Type QUES 
      { let ty1 = Hashtbl.clear tybinding; $2 tybinding in
        UnfTy($1, ty1)}
;

/* type expressions */
Type : /* Hashtbl -> Ast.term */
  | INT
      { fun tybinding -> `IntAny}
  | NAT
      { fun tybinding -> `Right(0)}
  | NIL
      { fun tybinding -> `Singleton("nil")}
  | TRUE
      { fun tybinding -> `True} /* `Singleton("tt") */
  | FALSE
      { fun tybinding -> `False} /* `Singleton("ff") */
  | BOOL
      { fun tybinding -> `Bool} /* `Cup(`Singleton("tt"),`Singleton("ff")) */
/*  | SINGLETON
      { fun tybinding -> `SingletonAny}*/
  | LCID
      { fun tybinding -> if Hashtbl.mem tybinding $1.v then `MVar($1.v) else `Singleton($1.v) }
  | UCID
      { fun tybinding -> `TVar(0,$1.v) }
  | INTV
      { fun tybinding -> if $1.v = 0 then `Not(`Any) 
                         else if $1.v = 1 then `Any else `Bounded($1.v,$1.v) }
  | LSQUARE INTV BOUNDED INTV RSQUARE
      { fun tybinding -> `Bounded($2.v,$4.v)}
  | LSQUARE BOUNDED INTV RSQUARE
      { fun tybinding -> `Left($3.v) }
  | LSQUARE INTV BOUNDED RSQUARE
      { fun tybinding -> `Right($2.v) }			
  | LSQUARE Type RSQUARE 
      { fun tybinding -> 
        let fresh = SubType.fresh "list" in
        `Mu(fresh,`Cup(`Prod($2 tybinding,`MVar(fresh)), `Singleton("nil")))
      }
  | LPAREN Type RPAREN
      { $2 }
  | Type COMMA Type
      { fun tybinding -> `Prod($1 tybinding, $3 tybinding) }
  | Type ARROW Type
      { fun tybinding -> `Arrow($1 tybinding, $3 tybinding) }
  | Type CUP Type
      { fun tybinding -> `Cup($1 tybinding, $3 tybinding) }
  | Type CAP Type
      { fun tybinding -> `Cap($1 tybinding, $3 tybinding) }
  | Type SETMINUS Type 
      { fun tybinding -> `Cap($1 tybinding, `Not($3 tybinding)) }
  | MINUS Type %prec NOT
      { fun tybinding -> `Not($2 tybinding) }
  | MU LCID DOT Type
      { fun tybinding ->  Hashtbl.add tybinding $2.v (); 
        let ty = $4 tybinding in
        if List.mem $2.v (SubType.tlmuv ty) then error $1 "Illegal recursive types"
        else `Mu($2.v, $4 tybinding) }
;


Expr :  /* Ast.expr */
  | AppExpr 
      { $1 }
  | MU LCID LPAREN Interface RPAREN LAMBDA LCID DOT Expr
      { let ft = Core.type4inter $4 in 
        if TypeMatch.isdomain ft then TmFun ($1, $2.v, $4, $7.v, $9) 
        else error $3 "Not a Domain Type" 
      }
  | LAMBDA LPAREN Interface RPAREN LCID DOT Expr
      { let ft = Core.type4inter $3 in 
        if TypeMatch.isdomain ft then TmFun ($1, "", $3, $5.v, $7) 
        else error $2 "Not a Domain Type" 
      }

  | Expr AND Expr
      { TmBoolAnd ($2, $1, $3) }
  | Expr OR Expr
      { TmBoolOr ($2, $1, $3) }
  | NEG Expr 
      { TmBoolNeg ($1, $2) }

  | Expr ADD Expr
      { TmIntAdd ($2, $1, $3) }
  | Expr MINUS Expr
      { TmIntMinus ($2, $1, $3) }
  | Expr TIMES Expr
      { TmIntTimes ($2, $1, $3) }
  | Expr DIV Expr
      { TmIntDiv ($2, $1, $3) }
  | Expr MOD Expr
      { TmIntMod ($2, $1, $3) }
/*  | MINUS Expr %prec NOT
      { TmIntUMinus($1, $2) }*/

  | Expr LT Expr
      { TmIntLt ($2, $1, $3) }
  | Expr EQEQ Expr
      { TmIntEq ($2, $1, $3) }
  | Expr LE Expr
      { TmBoolOr ($2, TmIntLt ($2, $1, $3), TmIntEq($2, $1, $3)) }
  | Expr GE Expr
      { TmBoolOr ($2, TmIntLt ($2, $3, $1), TmIntEq($2, $1, $3)) }
  | Expr GT Expr
      { TmIntLt ($2, $3, $1) }
  | Expr NEQ Expr
      { TmBoolOr ($2, TmIntLt ($2, $1, $3), TmIntLt ($2, $3, $1)) }

  | Expr COMMA Expr
      { TmPair ($2, $1, $3) }
  | PI1 Expr
      { TmPi1 ($1, $2) }
  | PI2 Expr
      { TmPi2 ($1, $2) }

  | Expr IN Type QUES Expr COLON Expr
      { let ty1 = Hashtbl.clear tybinding; $3 tybinding in
        if TypeMatch.isground ty1 then TmCase ($2, "_", $1, ty1, $5, $7)
        else error $2 "Non-ground Condition Type"}
  | LCID EQ Expr IN Type QUES Expr COLON Expr
      { let ty1 = Hashtbl.clear tybinding; $5 tybinding in
        if TypeMatch.isground ty1 then TmCase ($4, $1.v, $3, ty1, $7, $9)
        else error $2 "Non-ground Condition Type"}

  | IF Expr THEN Expr ELSE Expr
      { TmCase ($1, "_", $2, `True, $4, $6)} /* `Singleton("tt") */

  | LET LCID EQ Expr IN Expr
      { TmLet ($1, $2.v, $4, $6)}
;


AppExpr :
  | AExpr 
      { $1 }
  | AppExpr AExpr
      { TmApp(exprInfo $1, $1, $2)  }
;

AExpr :
  | LPAREN Expr RPAREN
      { $2 }
  | LCID
      { TmVar ($1.i, $1.v) }
  | NIL
      { TmNil($1) }
  | TRUE
      { TmBool($1, true) }
  | FALSE
      { TmBool($1, false) }
  | INTV
      { TmInt ($1.i, $1.v) }
;


Interface : /* (Ast.term * Ast.term) list */
   | Type ARROW Type
      { let ty1 = Hashtbl.clear tybinding; $1 tybinding in
        let ty2 = Hashtbl.clear tybinding; $3 tybinding in [(ty1, ty2)]
        (*let vars1 = SubType.vars ty1 and vars2 = SubType.vars ty2 in
        if (SubType.issubset vars1 vars2) && (SubType.issubset vars2 vars1) then 
        begin if TypeMatch.isposnegvar ty2 then error $2 "Bipolar Type Variables"
              else [(ty1, ty2)] 
        end
        else error $2 "Unmatched Type Variables"*) }
   | Type ARROW Type SEMI Interface
      { let ty1 = Hashtbl.clear tybinding; $1 tybinding in
        let ty2 = Hashtbl.clear tybinding; $3 tybinding in (ty1, ty2)::$5
        (*let vars1 = SubType.vars ty1 and vars2 = SubType.vars ty2 in
        if (SubType.issubset vars1 vars2) && (SubType.issubset vars2 vars1) then 
        begin if TypeMatch.isposnegvar ty2 then error $2 "Bipolar Type Variables"
              else (ty1, ty2)::$5
        end  
        else error $2 "Unmatched Type Variables"*) }



/*   */
