module GCD_SPEC
  imports IMP
  rule 
  <threads><thread>...
    <k>
	 while (!(a == b)) 
		{
			if(!(a<=b)) {a=a-b;}
			else {b=b-a;}
		}
		
=>
.
...
</k>
<env>
	  a|->LA:Int
	  b|->LB:Int
	  ...
	  </env>
	  ...</thread></threads>
	  <store>...
	  LA|->(A:Int=>D:Int)
	  LB|->(B:Int=>D:Int) 
	  ...</store>
	  
	  <time>N:Int=>N+Int T +Int 2</time>
	  
	  requires A>Int 0 andBool B>Int 0
	  ensures  T <=Int (A+Int B)*Int 6

	
	  
endmodule	  