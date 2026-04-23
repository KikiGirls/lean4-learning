
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
    while n < 1000 do
      if pellSeqMod p n == a0 && pellSeqMod p (n+1) == a1 then return n
      n := n + 1
    return 0

def isKilledByPrime (p : Nat) (k : Nat) : Bool :=
  let period := findPeriod p
  let inv2 := (List.range p).find? (fun x => (2 * x) % p == 1) |>.getD 0
  let kmod := k % period
  let a := pellSeqMod p kmod
  let half := (a + 1) * inv2 % p
  !isQR p half

def checkCovering (primes : List Nat) (N : Nat) : List Nat :=
  (List.range N).drop 1 |>.filter fun k =>
    !primes.any fun p => isKilledByPrime p k

-- Add more primes to cover the gaps
-- uncovered: [44, 65, 119, 120, 209, ...]
-- Let me check what primes kill k=44
#eval [5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113].filter fun p => isKilledByPrime p 44
