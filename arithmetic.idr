module Main

--- some examples from the docs
fiveIsFive: 5 = 5
fiveIsFive = Refl

plusReducesS : (n:Nat) -> (m:Nat) -> S (plus n m) = plus n (S m)
plusReducesS Z m = Refl
plusReducesS (S k) m = cong (plusReducesS k m)

--- addComm

-- Base case
addCommBase : m = plus m 0
-- Bring m into scope manually, since it's implicit
addCommBase {m = Z} = Refl -- 0 = 0
addCommBase {m = (S k)} = let rec = addCommBase {m=k} in
                              rewrite rec in Refl

-- Lemma: show that S (plus m k) = plus m (S k)
addComm_S : (k : Nat) -> (m : Nat) -> S (plus m k) = plus m (S k)
addComm_S k Z = Refl
addComm_S k (S j) = rewrite addComm_S k j in Refl

-- Proof of commutative property of addition
addComm : (n : Nat) -> (m : Nat) -> n + m = m + n
addComm Z m = addCommBase
addComm (S k) m = rewrite addComm k m in addComm_S k m

--- addAssoc

--- mulComm
--- mulAssoc
--- mulDist

main : IO ()
main = putStrLn "compiled successfully"