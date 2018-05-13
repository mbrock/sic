function pow(x: int, n: nat): int {
  if (n == 0) then
    1
   else
    x * pow(x, n - 1)
}


lemma powexplemma(x: int, n: nat)
  ensures pow(x, n) * pow(x, n) == pow(x, n + n)
{
  if (n > 0) {
    powexplemma(x, n-1);
  }
}

lemma powbaselemma(x: int, n: nat)
  ensures pow(x, n) * pow(x, n) == pow(x * x, n)
{
  if (n > 0) {
    powbaselemma(x, n-1);
  }
}

method rpow(x: int, n: nat) returns (res: int)
  ensures res == pow(x, n)
{
  var xx: int := x;
  var nn: nat := n;
  var rr: int := 1;
  while nn > 0
    decreases nn
    invariant pow(x,n) == rr * pow(xx, nn)
  {
    if (nn % 2 == 1) {
      rr := xx * rr;
    }

    nn := nn / 2;
    if (nn > 0) {
      var x0: int := xx;
      xx := xx * xx;
      calc {
            pow(xx, nn);
         == pow(x0 * x0, nn);
         == { powbaselemma(x0, nn); }
            pow(x0, nn) * pow(x0, nn);
         == { powexplemma(x0, nn); }
            pow(x0, nn + nn);
      }
    }
  }
  return rr;
}
