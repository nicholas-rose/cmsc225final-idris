module Main

--- some examples from the docs
fiveIsFive: 5 = 5
fiveIsFive = Refl

plusReducesS : (n:Nat) -> (m:Nat) -> S (plus n m) = plus n (S m)
plusReducesS Z m = Refl
plusReducesS (S k) m = cong (plusReducesS k m)

{-# 
  Induction on Nats
  From https://docs.idris-lang.org/en/latest/proofs/inductive.html
#-}
indNat : (P : Nat -> Type) ->                   -- Property to show (motive)
          (P Z) ->                              -- Base case
          ((k : Nat) -> (P k) -> (P (S k))) ->  -- Inductive step
          (x : Nat) ->                          -- Show for all x
          P x
indNat P base step Z = base
indNat P base step (S k) = step k (indNat P base step k)

{-# 
  Commutative property of addition
#-}
-- The first proof is provided in the tutorial and uses pattern matching
-- Base case
addCommZero : m = plus m 0
-- Bring m into scope manually, since it's implicit
addCommZero {m = Z} = Refl -- 0 = 0
addCommZero {m = (S k)} = let rec = addCommZero {m=k} in
                              rewrite rec in Refl

-- Lemma: show that S (plus m k) = plus m (S k)
addComm_S : (k : Nat) -> (m : Nat) -> S (plus m k) = plus m (S k)
addComm_S k Z = Refl
addComm_S k (S j) = rewrite addComm_S k j in Refl

-- Proof of commutative property of addition
addComm : (n : Nat) -> (m : Nat) -> plus n m = plus m n
addComm Z m = addCommZero
addComm (S k) m = rewrite addComm k m in addComm_S k m


-- Inductive proof of additive commutativity, similar to the one in Arithmetic.pie
addCommMot : (n : Nat) -> Type
addCommMot n = (m : Nat) -> plus n m = plus m n

addCommBase : (m : Nat) -> m = plus m 0
addCommBase m = addCommZero {m=m}

addCommStep : (k : Nat) -> 
              ((m : Nat) -> plus k m = plus m k) ->
              (m : Nat) -> S (plus k m) = plus m (S k)
addCommStep k hyp m = rewrite (hyp m) in addComm_S k m

addCommInd : (n, m : Nat) -> plus n m = plus m n
addCommInd n = indNat addCommMot addCommBase addCommStep n

-- Test cases
-- Tell compiler to read 7 as Nat instead of Int
seven : Nat
seven = 7

addCommTest : Main.seven = Main.seven
addCommTest = addComm 3 4

addCommIndTest : Main.seven = Main.seven
addCommIndTest = addCommInd 3 4

{-# 
  Associative property of addition
#-}
-- addAssoc

{-# 
  Commutative property of multiplication
#-}
-- mulComm

{-# 
  Associative property of multiplication
#-}
-- mulAssoc

{-# 
  Distributive property of multiplication
#-}
-- mulDist

main : IO ()
main = putStrLn "compiled successfully"