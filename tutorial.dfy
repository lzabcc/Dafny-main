/* 
  First example of Dafny code

  In vscode, with the dafny plugin installed, code should be syntax highlighted
  with a "tick" mark in the left hand column alongside the method header.

  Changing the "ensures" postcondition to "0 <= x" should change the tick to a cross,
  and highlight the code which leads to the postcondition not being satisfied.

 */

method Abs(x: int) returns (y: int)
  ensures y >= 0 && ((x < 0 && y == -x) || (x >= 0 && y == x))
{
  if x<0
    { return - x; }
  else
    { return x; }

}

method Sums(x: int, y: int) returns (m: int, n: int)
requires x > -1/2
ensures m > n
{
  var a: int;
  m := x;
  n := y;
  a := 2 * m + n;
  n := n - 1;
  m := a;
  return m, n;
}


/*
  Functions are also available and can be used in annotations. Note that names are case
  sensitive, so Abs (method) and abs (function) are different items.
 */

function abs(x: int): int
{
  if x < 0 then -x else x
}

/*
  A method in Dafny can return more than one variable. The example below
  returns two integer variables. There are 2 postconditions - but are they proven?
 */
method MultipleReturns(x: int, y: int) returns (more: int, less: int)
  ensures less < x && x < more
  requires 0 < y
{
  more := x + y;
  less := x - y;
}

method Max(a: int, b: int) returns (c: int)
  requires a<b
{
   if a<b 
   { c := a; return c;}
   else { return b;}
}

method TestAbs()
{
  var v := Abs(-3);
  assert 0 <= v;
  assert v == 3;
}

