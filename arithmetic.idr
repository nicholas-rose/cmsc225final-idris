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

-- CongS
CongS : {a : Nat} -> {b : Nat} -> (a = b) -> (S a = S b)
CongS Refl = Refl

-- addAssoc
addAssoc : (a : Nat) -> (b : Nat) -> (c : Nat) -> plus (plus a b) c = plus a (plus b c)
addAssoc Z b c = Refl
addAssoc (S a) b c = CongS (addAssoc a b c)

-- Test Cases
nine : Nat
nine = 9

addAssocTest : Main.nine = Main.nine
addAssocTest = addAssoc 2 3 4

{-# 
  Associative property of multiplication
#-}
-- mulAssoc

{-# 
  Distributive property of multiplication:
  Abby Herman, Uday Saharia, Vivian Wu, Kseniia Korotenko
#-}

------------Symmetric Property of Equality----------
symm : (a = b) -> (b = a)
symm Refl = Refl

------------addAssoc------------
---addAssoc : (a : Nat) -> (b : Nat) -> (c : Nat) -> ((a + b) + c = a + (b + c))
---addAssoc Z b c = Refl
---addAssoc (S k) b c = rewrite (addAssoc k b c) in Refl

--Zero Property of Multiplication: n * 0 = 0
multZero : (n : Nat) -> (mult n Z = Z)
multZero Z = Refl
multZero (S k) = multZero k

--distributiveMultAdd: x*(y+z) = (x*y) + (x*z)
disMultPlus : (x: Nat) -> (y: Nat) -> (z: Nat) -> (mult x (plus y z) = plus (mult x y) (mult x z)) 
distMultPlus Z _ _ = Refl 
distMultPlus n Z m = rewrite (multZero n) in Refl
distMultPlus x y Z = rewrite (addComm y Z) in 
                           (rewrite (multZero x) in 
                           (rewrite addComm (mult x y) Z in Refl))
distMultPlus (S x) y z = rewrite (distMultPlus x y z) in 
                            (rewrite (symm (addAssoc (plus y z) (mult x y) (mult x z))) in 
                            (rewrite (addComm y z) in 
                            (rewrite (addAssoc z y (mult x y)) in 
                            (rewrite (addComm z (plus y (mult x y))) in 
                            (rewrite (addAssoc (plus y (mult x y)) z (mult x z)) in Refl)))))


--distributiveAddMult: (x+y)*z = (x*z) + (y*z)  
distPlusMult : (x : Nat) -> (y : Nat) -> (z : Nat) -> (mult (plus x y) z = plus (mult x z) (mult y z))
distPlusMult Z _ _ = Refl		
distPlusMult x Z z = rewrite (addComm x Z) in 
                           (rewrite (addComm (mult x z) Z ) in Refl)
distPlusMult x y Z = rewrite (multZero y) in 
                           (rewrite (multZero (plus x y)) in 
                           (rewrite (multZero x) in Refl))
distPlusMult (S x) y z = rewrite (distPlusMult x y z) in 
                            (rewrite addAssoc z (mult x z) (mult y z) in Refl)


--******* Distributive Property Test Cases *********--
zero : Nat
zero = 0

one : Nat
one = 1

two : Nat
two = 2

three : Nat
three = 3

four : Nat
four = 4

five : Nat
five = 5

six : Nat
six = 6

eight : Nat
eight = 8


--***Mult Add: a*(b+c) = (a*b) + (a*c)***
distMultPlusTest1 : Main.zero = Main.zero
distMultPlusTest1 = distMultPlus 0 0 0

distMultPlusTest2 : Main.zero = Main.zero
distMultPlusTest2 = distMultPlus 0 1 2

distMultPlusTest3 : Main.one = Main.one
distMultPlusTest3 = distMultPlus 1 1 0

distMultPlusTest4 : Main.six = Main.six
distMultPlusTest4 = distMultPlus 2 1 2

distMultPlusTest5 : Main.five = Main.five
distMultPlusTest5 = distMultPlus 1 1 4

--***Add Mult: (a+b)*c = (a*c) + (b*c)***
distPlusMultTest1 : Main.zero = Main.zero
distPlusMultTest1 = distPlusMult 0 0 0

distPlusMultTest2 : Main.two = Main.two
distPlusMultTest2 = distPlusMult 0 1 2

distPlusMultTest3 : Main.zero = Main.zero
distPlusMultTest3 = distPlusMult 1 1 0

distPlusMultTest4 : Main.six = Main.six
distPlusMultTest4 = distPlusMult 2 1 2

distPlusMultTest5 : Main.eight = Main.eight
distPlusMultTest5 = distPlusMult 1 1 4

{-# 
  Commutative property of Multiplication
  Nick Rose
#-}
mulZero : (m : Nat) -> mult 0 m = 0
mulZero m = Refl

mulCommZero : (m : Nat) -> mult m 0 = mult 0 m
mulCommZero Z = Refl
mulCommZero (S k) = let rec = mulCommZero k in 
    rewrite rec in Refl

mulOne : (m : Nat) -> mult m 1 = m
mulOne Z = Refl
mulOne (S k) = let rec = mulOne k in 
    rewrite rec in Refl

succPlusOne : (m : Nat) -> (S m) = plus m 1
succPlusOne Z = Refl
succPlusOne (S m) = let rec = succPlusOne m in rewrite rec in Refl

mulComm : (a, b : Nat) -> mult a b = mult b a
mulComm a Z      = mulCommZero a
mulComm a (S b') = 
    (trans                                          -- mult a b = mult b a
        (trans                                          -- mult a (S b') = plus (mult a b') a
            (cong {f=(mult a)} (succPlusOne b'))            -- mult a (S b') = mult a (plus b' 1)
            (distMultPlus a b' 1))                   -- mult a (plus b' 1) = plus (mult a b') a
        (trans                                          -- plus (mult a b') (mult a 1) = plus a (mult b' a)
            (cong {f=(plus (mult a b'))} (mulOne a))        -- plus (mult a b') (mult a 1) = plus (mult a b') a
            (trans                                          -- plus (mult a b') a = plus a (mult b' a)
                (addComm (mult a b') a)                         -- plus a (mult b' a) = plus (mult b' a) a
                (cong {f=(plus a)} (mulComm a b')))))           -- plus (mult b' a) a = plus (mult a b') a

-- mulComm Tests
mulCommTest1 : Main.zero * Main.one = Main.one * Main.zero 
mulCommTest1 = mulComm 0 1

mulCommTest2 : Main.two * Main.four = Main.four * Main.two 
mulCommTest2 = mulComm 2 4

{-#
  Associative property of Multiplication
  Avery Kriegel
#-}

-- a = Z base-case: trivial 0 = 0
mulAssoc_Z : Z = Z
mulAssoc_Z = Refl

-- a = S k inductive-case:
mulAssoc_S : (k : Nat) -> (b : Nat) -> (c : Nat) -> plus (mult b c) (mult (mult k b) c) = mult (plus b (mult k b)) c
mulAssoc_S k b c = rewrite distributiveAddMult b (mult k b) c in Refl
  -- the rewrite below allows the distributive property to complete the proof
  -- x = b, y = (mult k b), z = c

mulAssoc : (a : Nat) -> (b : Nat) -> (c : Nat) -> mult a (mult b c) = mult (mult a b) c
mulAssoc Z b c = mulAssoc_Z
  -- invoke base-case proof
mulAssoc (S k) b c = rewrite mulAssoc k b c in mulAssoc_S k b c
  -- invoke inductive-case proof, rewriting mult (plus b (mult k b)) c = plus (mult b c) (mult (mult k b) c)

-- mulAssoc Tests
mulAssocTest1 : mult 2 (mult 3 4) = mult (mult 2 3) 4
mulAssocTest1 = mulAssoc 2 3 4

mulAssocTest2 : mult 5 (mult 0 5) = mult (mult 5 0) 5
mulAssocTest2 = mulAssoc 5 0 5

main : IO ()
main = putStrLn "compiled successfully"
