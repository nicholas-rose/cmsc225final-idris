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
addAssoc : (a : Nat) -> (b : Nat) -> (c : Nat) -> plus a (plus b c) = plus (plus a b) c

{-# 
  Commutative property of multiplication
#-}
-- mulComm
-- x*y = (x-1)*y + x
addZero : (m : Nat) -> m = plus m 0
addZero Z = Refl -- 0 = 0
addZero (S k) = let rec = addZero k in 
    rewrite rec in Refl

mulZero : (m : Nat) -> mult 0 m = 0
mulZero m = Refl
    
mulOne : (m : Nat) -> mult m 1 = m
mulOne Z = Refl
mulOne (S k) = let rec = mulOne k in 
    rewrite rec in Refl

mulCommZero : (m : Nat) -> mult 0 m = mult m 0
mulCommZero Z = Refl
mulCommZero (S k) = let rec = mulCommZero k in 
    rewrite rec in Refl



mulCommInd : (k : Nat) -> (b : Nat) -> mult b (S k)  = plus b (mult k b) 
mulCommInd Z b     = trans (mulOne b) (trans (addZero b) (cong (sym (mulZero b))))
mulCommInd (S j) b = (cong {f=(plus b)} (mulCommInd j b))
-- helpMulCommIndStep : 
-- mult b (S (S j)) = plus b (plus b (mult j b))

-- mult b (S j) = (plus b (mult j b)


mulComm : (a : Nat) -> (b : Nat) -> mult a b = mult b a
mulComm Z b         = mulCommZero b
mulComm (S k) b = sym (mulCommInd k b) -- sym (mulCommInd k b)

{-# 
  Associative property of multiplication
#-}
-- mulAssoc
mulAssoc : (a : Nat) -> (b : Nat) -> (c : Nat) -> mult a (mult b c) = mult (mult a b) c

{-# 
  Distributive property of multiplication
#-}
-- mulDist
mulDist : (a : Nat) -> (b : Nat) -> (c : Nat) -> mult a (plus b c) = plus (mult a b) (mult a c)

main : IO ()
main = putStrLn "compiled successfully"