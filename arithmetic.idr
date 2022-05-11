module Main

--- some examples from the docs
fiveIsFive: 5 = 5
fiveIsFive = Refl

plusReducesS : (n:Nat) -> (m:Nat) -> S (plus n m) = plus n (S m)
plusReducesS Z m = Refl
plusReducesS (S k) m = cong (plusReducesS k m)

--- addComm
--- addAssoc

--- mulComm
--- mulAssoc
--- mulDist

main : IO ()
main = putStrLn "compiled successfully"