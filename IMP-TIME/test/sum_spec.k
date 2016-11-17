
module SUM-SPEC
  imports IMP
rule
  <threads><thread>...
    <k>
      while (!(n <= 0)) {
        sum = sum + n;
        n = n + -1;
      }
    =>
      .K
   ... </k>
    <env>...
      n   |-> LN:Int
      sum |-> LSUM:Int
    ...</env>
  ...</thread></threads>
  <store>...
    LN   |-> (N:Int => 0)
    LSUM |-> (S:Int => S':Int)
  ...</store>
  <time>T:Int=>T+Int T1</time>
requires N >=Int 0
ensures (T1>Int 6*Int N )


rule
  <threads><thread>...
    <k>
      int n, sum;
      n = N:Int;
      sum = 0;
      while (!(n <= 0)) {
        sum = sum + n;
        n = n + -1;
      }
    =>
      .K
    ...</k>
    <env>
      .Map
    =>
      n   |-> ?LN:Int
      sum |-> ?LSUM:Int
    </env>
  ...</thread></threads>
  <store>...
    .Map
  =>
    ?LN   |-> 0
    ?LSUM |-> S'
  ...</store>
  //<time>T:Int=>T+Int 14*Int N +Int 12</time>
  <time>T:Int=>_</time>
requires N >=Int 0
endmodule
