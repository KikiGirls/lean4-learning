
def pellSeqMod (p : Nat) : Nat → Nat
  | 0 => 1 % p
  | 1 => 15 % p
  | (n+2) => ((14 * pellSeqMod p (n+1) + p * p - pellSeqMod p n) % p)

def isQR (p : Nat) (a : Nat) : Bool :=
  (List.range p).any fun x => (x * x) % p == a % p

def findPeriod (p : Nat) : Nat :=
  let a0 := pellSeqMod p 0
  let a1 := pellSeqMod p 1
  Id.run do
    let mut n := 1
    while n < 500 do
      if pellSeqMod p n == a0 && pellSeqMod p (n+1) == a1 then return n
      n := n + 1
    return 0

def isKilledByPrime (p : Nat) (k : Nat) : Bool :=
  let period := findPeriod p
  if period == 0 then false
  else
    let inv2 := (List.range p).find? (fun x => (2 * x) % p == 1) |>.getD 0
    let kmod := k % period
    let a := pellSeqMod p kmod
    let half := (a + 1) * inv2 % p
    !isQR p half

-- Check which primes kill k=119
#eval [53, 59, 61, 67, 73, 79, 83, 89, 97].filter fun p => isKilledByPrime p 119
