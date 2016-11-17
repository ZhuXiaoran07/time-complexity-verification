// Copyright (c) 2014-2016 K Team. All Rights Reserved.
//require "../builtins/model-checker.k" 
module IMP-SYNTAX
//imports MODEL-CHECKER-HOOKS
  syntax AExp  ::= Int | String | Id
                 | "++" Id
                 | "read" "(" ")"
                 > AExp "/" AExp              [left, strict, division]
				 | AExp "%" AExp              [left, strict]
                 > AExp "+" AExp              [left, strict]
				 |  AExp "-" AExp              [left, strict]
                 > "spawn" Block
                 > Id "=" AExp                [strict(2)]
                 | "(" AExp ")"               [bracket]
  syntax BExp  ::= Bool
                 | AExp "<=" AExp             [seqstrict, latex({#1}\leq{#2})]
				 | AExp "==" AExp             [seqstrict, latex({#1}\leq{#2})]
				 | AExp ">" AExp             [seqstrict, latex({#1}\leq{#2})]
                 | "!" BExp                   [strict]
                 > BExp "&&" BExp             [left, strict(1)]
                 | "(" BExp ")"               [bracket]
  syntax Block ::= "{" Stmts "}"
  syntax Stmt  ::= Block
                 | AExp ";"                   [strict]
                 | "if" "(" BExp ")"
                   Block "else" Block         [strict(1)]
                 | "while" "(" BExp ")" Block
                 | "int" Ids ";"
                 | "print" "(" AExps ")" ";"
                 | "halt" ";"
                 > "join" AExp ";"            [strict]

  syntax Ids   ::= List{Id,","}
  syntax AExps ::= List{AExp,","}
  syntax Stmts ::= List{Stmt,""}
endmodule


module IMP
  imports IMP-SYNTAX
  syntax KResult ::= Int | Bool | String

  configuration <T color="yellow">
                  <threads color="orange">
                    <thread multiplicity="*" color="blue">
                      <k color="green"> $PGM:Stmts </k>
                      <env color="LightSkyBlue"> .Map </env>
                      <id color="black"> 0 </id>
                    </thread>
                  </threads>
                  <store color="red"> .Map </store>
				   
                  <in color="magenta" stream="stdin"> .List </in>
                  <out color="Orchid" stream="stdout"> .List </out>
				   <time> 0 </time>
                </T>

// AExp
  rule <k> X:Id => I ...</k>
       <env>... X |-> N ...</env>
       <store>... N |-> I ...</store>
       	   [lookup]
  rule <k> ++X => I +Int 1 ...</k>
       <env>... X |-> N ...</env>
       <store>... N |-> (I => I +Int 1) ...</store> 
       <time> M=>M+Int 1 </time> 	   [increment]
  rule <k> read() => I ...</k>
       <in> ListItem(I:Int) => .List ...</in>  [read]
  rule <k>(I1 / I2 => I1 /Int I2)...</k> <time> M=>M+Int 1 </time>   requires I2 =/=Int 0
  rule <k>(I1 + I2 => I1 +Int I2)...</k><time> M=>M+Int 1</time>
rule <k>(I1 - I2 => I1 -Int I2)...</k><time> M=>M+Int 1</time>  
  rule <k>(Str1 + Str2 => Str1 +String Str2)...</k><time> M=>M+Int 1 </time> 
  rule <k>(I1 % I2 => I1 %Int I2)...</k><time> M=>M+Int 1</time> requires I2 =/=Int 0
// BExp
  rule <k>(I1 <= I2 => I1 <=Int I2)...</k><time> M=>M+Int 1 </time>
  rule <k>(I1 == I2 => I1 ==Int I2)...</k><time> M=>M+Int 1 </time>
  rule <k>(I1 > I2 => I1 >Int I2)...</k><time> M=>M+Int 1 </time>
  rule <k>(! T => notBool T)...</k><time> M=>M+Int 1 </time>
  rule <k>(true && B => B)...</k><time> M=>M+Int 1 </time>
  rule <k>(false && _ => false)...</k><time> M=>M+Int 1 </time>
// Block
  rule <k> {Ss} => Ss ~> Rho ...</k> <env> Rho </env>  [structural]
  rule <k> Rho => . ...</k> <env> _ => Rho </env>    [structural]
// Stmt
  rule _:Int; => .
  rule <k> X = I:Int => I ...</k>
       <env>... X |-> N ...</env>
       <store>... N |-> (_ => I) ...</store> 
		<time> M=>M+Int 1 </time>[assignment]
  rule if (true)  S else _ => S
  rule if (false) _ else S => S
  rule while (B) S => if (B) {S while (B) S} else {.Stmts}  [structural]

  rule <k> int (X,Xs => Xs); ...</k>
       <env> Rho => Rho[X <- !N:Int] </env>
       <store>... .Map => !N |-> 0 ...</store>
	   <time> M=>M+Int 1 </time>
  rule int .Ids; => .  [structural]

  syntax Printable ::= Int | String
/* currently it is necessary to subsort Printable to AExp,
  but future K should be able to infer that automatically. */
  syntax AExp ::= Printable
  context print(HOLE:AExp, AEs:AExps);
  
  rule <k> print(P:Printable,AEs => AEs); ...</k>
       <out>... .List => ListItem(P) </out>  [print]
  rule print(.AExps); => .  [structural]

  rule <k> halt; ~> _ => . </k>

  rule <k> spawn S => !T:Int ...</k> <env> Rho </env>
       (.Bag => <thread>... <k> S </k> <env> Rho </env> <id> !T </id> ...</thread>)
  rule <k> join(T:Int); => . ...</k>
       <thread>... <k> . </k> <id> T </id> ...</thread>

// Stmts
  rule .Stmts => .                 [structural]
  rule S:Stmt Ss:Stmts => S ~> Ss  [structural]
  
// verification ids
  syntax Id ::= "n"     [token]
              | "sum"   [token]
			  | "a"	    [token]
			  | "b"     [token]
			  | "c"      [token]
 syntax Stmt ::= "Time""("Int"," Int")"   [function]
   rule Time(I1, I2)=> .K  requires I2 >=Int 0
endmodule