module calculator where

-- Nat
data Nat : Set where
  zero : Nat
  suc : Nat → Nat

--Bool
data Bool : Set where
  true  : Bool
  false : Bool


-- Equality type
data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x


-- Maybe
data Maybe (A : Set) : Set where
  nothing : Maybe A
  just : A → Maybe A


-- Dependent type: proof that a Nat is zero
data IsZero : Nat → Set where
  isZero : IsZero zero

checkIsZero : (n : Nat) → Maybe (IsZero n)
checkIsZero zero = just isZero
checkIsZero (suc n) = nothing

-- Int
data Int : Set where
  pos : Nat → Int
  neg : Nat → Int

-- Add
_+_ : Nat → Nat → Nat
zero + m = m
suc n + m = suc (n + m)

-- Mul
_*_ : Nat → Nat → Nat
zero * m = zero
suc n * m = (n * m) + m

-- Sub
_-_ : Nat → Nat → Nat
zero - m = zero
n - zero = n
suc n - suc m = n - m

--negate 
negate : Int → Int
negate (pos n) = neg n
negate (neg n) = pos n

--zero
zeroInt : Int
zeroInt = pos zero



-- Expr
data Expr : Set where
  Lit : Int → Expr
  Add : Expr → Expr → Expr
  Mul : Expr → Expr → Expr
  Sub : Expr → Expr → Expr

eval : Expr → Nat
eval (Lit (pos n)) = n
eval (Lit (neg n)) = zero - n
eval (Add e1 e2) = eval e1 + eval e2
eval (Mul e1 e2) = eval e1 * eval e2
eval (Sub e1 e2) = eval e1 - eval e2

--Literal Help
evalLiteral : Int → Nat
evalLiteral (pos n) = n
evalLiteral (neg n) = zero - n

-- Mul by zero(zero)
multiplyByZero : Expr → Nat
multiplyByZero e = eval (Mul e (Lit zeroInt)) -- Should always be zero


--Dependent type implementattion
expand : Expr → Expr
expand (Lit i) = Lit i
expand (Add e1 e2) = Add (expand e1) (expand e2)
expand (Sub e1 e2) = Sub (expand e1) (expand e2)
expand (Mul e1 (Add e2 e3)) = Add (expand (Mul e1 e2)) (expand (Mul e1 e3))
expand (Mul e1 e2) = Mul (expand e1) (expand e2)

--Breaks down add
simplifyAdd : Expr → Expr
simplifyAdd (Add (Lit (pos zero)) n) = n
simplifyAdd (Add n (Lit (pos zero))) = n
simplifyAdd e = e


-- Tests for operations
Addtest : Expr
Addtest = Add (Lit (pos (suc (suc zero)))) (Lit (pos (suc zero)))

Addanswer : Nat
Addanswer = eval Addtest

Multest : Expr
Multest = Mul (Lit (pos (suc (suc zero)))) (Lit (pos (suc zero)))

Mulanswer : Nat
Mulanswer = eval Multest

Subtest : Expr
Subtest = Sub (Lit (pos (suc (suc zero)))) (Lit (pos (suc zero)))

Subanswer : Nat
Subanswer = eval Subtest

-- eval (......) ≡ 10

-- eval (Add m n) ≡ eval (Add n m)



-- Tests for IsZero
TestIsZero1 : Maybe (IsZero zero)
TestIsZero1 = checkIsZero zero

TestIsZero2 : Maybe (IsZero (suc zero))
TestIsZero2 = checkIsZero (suc zero)


-- Proof that zero is a Nat (simple dependent type)
-- Proof that zero is a Nat (simple dependent type)
data ZeroIsNat : Nat → Set where
  reflZero : zero ≡ zero  -- We prove that zero is equal to zero

-- Function to use the proof
zeroIsNatProof : zero ≡ zero
zeroIsNatProof = refl



