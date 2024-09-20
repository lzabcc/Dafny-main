/* 
  Dafny Tutorial 2: Sequences and Stacks, Predicates and Assertions

  In this tutorial we introduce a simple stack model using the functional 
  style of programming.
  
*/
type intStack = seq<int>

//e1
predicate isEmpty(s: intStack)
{
    |s| == 0
}

function push(s: intStack, x: int): intStack
{
    s + [x]
}

//e3
function top(s: intStack): int
requires !isEmpty(s)
{
    s[|s|-1]
}

function pop(s: intStack): intStack
requires !isEmpty(s)
{
   s[..|s|-1] 
}




method testStack() returns (r: intStack)
{

  
  var s: intStack := [20, 30, 15, 40, 60, 100, 80];

  var t: int := top(s);

  assert pop(push(s,100)) == s;

  
  assert forall e: int :: 5 <= e < |s| ==> s[e] > 5;

  //e4
  assert t == 80;

  //e5
  assert forall x: int :: pop(push(s, x)) == s;


  //e5
  assert forall st: intStack, x: int :: pop(push(st, x)) == st;

  //e6
  assert forall e: int :: 0 <= e < |s| ==> s[e] >= 5 && 200 >= s[e];
 
  //e7

  assert exists e: int :: 0 <= e < |s| && (20 <=s[e] && s[e] <= 60);

  assert exists e: int :: 0 <= e < |s| && s[e] > 40;
  //assert exists  e: int :: 5 <= e < |s| ==> s[e] > 20000000;

  r:= s;
}

method Main()
{
    var t:=testStack();
    print "Stack tested\nStack is ", t, "\n";
}
