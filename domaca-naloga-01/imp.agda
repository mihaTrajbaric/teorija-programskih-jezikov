module imp where


-- Logične vrednosti

data Bool : Set where
    true : Bool
    false : Bool

if_then_else_ : {A : Set} → Bool → A → A → A
if true then x else y = x
if false then x else y = y

agdaAnd : Bool → Bool → Bool
agdaAnd false _ = false
agdaAnd true q = q

agdaOr : Bool → Bool → Bool
agdaOr true  _ = true
agdaOr false q = q

agdaNot : Bool → Bool
agdaNot false = true
agdaNot true = false


-- Naravna števila

data Nat : Set where
    zero : Nat
    suc : Nat → Nat 

-- Namesto suc (suc zero) lahko napišemo kar 2
{-# BUILTIN NATURAL Nat #-}

plus : Nat → Nat → Nat
plus zero n = n
plus (suc m) n = suc (plus m n)

times : Nat → Nat → Nat
times zero n = zero
times (suc m) n = plus (times m  n) n

pow : Nat → Nat → Nat
pow a zero = suc zero
pow a (suc n) = times a (pow a n) 

equal : Nat → Nat → Bool
equal zero zero = true
equal zero (suc x) = false
equal (suc x) zero = false
equal (suc m) (suc n) = equal m n

greater : Nat → Nat → Bool
greater zero zero = false
greater zero (suc n) = false
greater (suc m) zero = true
greater (suc m) (suc n) = greater m n

smaller : Nat → Nat → Bool
smaller zero zero = false
smaller zero (suc n) = true
smaller (suc m) zero = false
smaller (suc m) (suc n) = smaller m n
-- Seznami

data List : Set → Set where
    [] : {A : Set} → List A
    _::_ : {A : Set} → A → List A → List A


-- Končne množice

data Fin : Nat → Set where
    zero : {n : Nat} → Fin (suc n)
    suc : {n : Nat} → Fin n → Fin (suc n)

infixl 25 _/_

_/_ : (m n : Nat) → Fin (suc (plus m n))
zero / n = zero
suc m / n = suc (m / n)


-- Vektorji

data Vec : Set → Nat → Set where
    [] : {A : Set} → Vec A zero
    _::_ : {A : Set} {n : Nat} → A → Vec A n → Vec A (suc n)

_[_] : {A : Set} {n : Nat} → Vec A n → Fin n → A
[] [ () ]
(x :: v) [ zero ] = x
(x :: v) [ suc ind ] = v [ ind ]

_[_]←_ : {A : Set} {n : Nat} → Vec A n → Fin n → A → Vec A n
_[_]←_ [] ()
_[_]←_ (x :: xs) zero v = v :: xs
_[_]←_ (x :: xs) (suc i) v = x :: (xs [ i ]← v)


-- Sintaksa jezika

infixr 3 _；_ 
infix 4 _:=_
infix 5 IF_THEN_ELSE_END
infix 6 WHILE_DO_DONE
infix 6 FOR_:=_TO_DO_DONE
infix 6 SKIP
infix 6 PRINT

infixl 7 _OR_
infixl 8 _AND_
infixl 9 NOT
infix 10 _≡_
infix 10 _>_
infix 10 _<_

infixl 11 _+_
infixl 12 _*_
infixl 13 _**_

infix 14 !_
infix 15 `_

-- Artimetične in logične izraze ter ukaze parametriziramo z naravnim številom `n`,
-- ki pove, da izraz uporablja spremenljivke indeksirane med `0` in `n - 1`.

data Exp (n : Nat) : Set where
    `_ : Nat → Exp n
    !_ : Fin n → Exp n -- Spremenljivke nazivamo z naravnimi števili manjšimi od `n`
    _+_ : Exp n → Exp n → Exp n
    _*_ : Exp n → Exp n → Exp n
    _**_ : Exp n → Exp n → Exp n

data BExp (n : Nat) : Set where
    _≡_ : Exp n → Exp n → BExp n
    _<_ : Exp n → Exp n → BExp n
    _>_ : Exp n → Exp n → BExp n
    _AND_ : BExp n → BExp n → BExp n
    _OR_ : BExp n → BExp n → BExp n
    NOT : BExp n → BExp n


data Cmd : (n : Nat) → Set where
    IF_THEN_ELSE_END : {n : Nat} → BExp n → Cmd n → Cmd n → Cmd n
    WHILE_DO_DONE : {n : Nat} → BExp n → Cmd n → Cmd n
    FOR_:=_TO_DO_DONE : {n : Nat} → Fin n → Exp n → Exp n → Cmd n → Cmd n
    _；_ : {n : Nat} → Cmd n → Cmd n → Cmd n
    _:=_ : {n : Nat} → (Fin n) → Exp n → Cmd n
    SKIP : {n : Nat} → Cmd n
    PRINT : {n : Nat} → Exp n → Cmd n

-- Primer aritmetičnega izraza, ki sešteje vrednosti spremenljivk na mestu 1 in 0 v stanju s tremi spremenljivkami.
primer : Exp 3
primer = ! 1 / 1 + ! 0 / 2 -- Da lahko uporabimo vrednost na mestu 0 in 1 v izrazu velikosti do 3.

-- Program, ki sešteje prvih n naravnih števil
vsota1 : Nat → Cmd 3
vsota1 n = 
    0 / 2 := ` n ； -- Indeksiramo prvo spremenljivo, in tip vseh možnih spremenljivk povečamo za 2, saj bomo v celotnem programo potrebovali tri spremenljivke
    1 / 1 := ` 0 ；
    2 / 0 :=  ! (0 / 2) ；
    WHILE ! (1 / 1) < ! (0 / 2) DO
        2 / 0 := ! 2 / 0 + ! 1 / 1 ；
        1 / 1 := ! 1 / 1 + ` 1
    DONE

-- Program, ki sešteje prvih n naravnih števil s pomočjo for zanke
vsota : Nat → Cmd 3
vsota n = 
    0 / 2 := ` n ； -- Indeksiramo prvo spremenljivo, in tip vseh možnih spremenljivk povečamo za 2, saj bomo v celotnem programo potrebovali tri spremenljivke
    1 / 1 := ` 0 ；
    2 / 0 := ` 0 ；
    FOR ( (1 / 1) ) := ` 1 TO ! (0 / 2) DO
        2 / 0 := ! 2 / 0 + ! 1 / 1 ；
        1 / 1 := ! 1 / 1 + ` 1 ； PRINT (! (2 / 0))
    DONE


-- Stanje

State : Nat → Set
State n = Vec Nat n

-- Result : Nat → Set
-- Result n = State n

-- Če želite, lahko za nadgradnjo rezultatov uporabite spodnje tipe

record Pair (A B : Set) : Set where
    constructor _,_
    field
        fst : A
        snd : B

-- Result : Nat → Set
-- Result n = Pair (State n) (List Nat)

data Maybe (A : Set) : Set where
    nothing : Maybe A
    just : A → Maybe A

Result : Nat → Set
Result n = Pair (Maybe (State n)) (List Nat)

evalExp : {n : Nat} → State n → Exp n → Nat
evalExp st (` x) = x
evalExp st (! i) = st [ i ]
evalExp st (exp₁ + exp₂) = plus (evalExp st exp₁) (evalExp st exp₂)
evalExp st (exp₁ * exp₂) = times (evalExp st exp₁) (evalExp st exp₂)
evalExp st (exp₁ ** exp₂) = pow (evalExp st exp₁) (evalExp st exp₂)

evalBExp : {n : Nat} → State n → BExp n → Bool
evalBExp st (bexp₁ ≡ bexp₂) = equal (evalExp st bexp₁) (evalExp st bexp₂)
evalBExp st (bexp₁ < bexp₂) = smaller (evalExp st bexp₁) (evalExp st bexp₂)
evalBExp st (bexp₁ > bexp₂) = greater (evalExp st bexp₁) (evalExp st bexp₂)
evalBExp st (bexp₁ AND bexp₂) = agdaAnd (evalBExp st bexp₁) (evalBExp st bexp₂)
evalBExp st (bexp₁ OR bexp₂) = agdaOr (evalBExp st bexp₁) (evalBExp st bexp₂)
evalBExp st (NOT bexp) = agdaNot (evalBExp st bexp)

evalCmd : {n : Nat} → Nat → Result n → Cmd n → Result n
evalCmd _ (nothing , printList) _ = (nothing , printList)
evalCmd n (just st , printList) IF bexp THEN cmd₁ ELSE cmd₂ END =
    if evalBExp st bexp then
        evalCmd n (just st , printList) cmd₁
    else
        evalCmd n (just st , printList) cmd₂
evalCmd (suc n) (just st , printList) WHILE bexp DO cmd DONE =
    if evalBExp st bexp then
        evalCmd n (evalCmd n (just st , printList) cmd) (WHILE bexp DO cmd DONE)
    else
        (just st , printList)
evalCmd n res (cmd₁ ； cmd₂) = evalCmd n (evalCmd n res cmd₁) cmd₂
evalCmd _ (just st , printList) (ℓ := exp) = (just (st [ ℓ ]← (evalExp st exp)) , printList)
evalCmd _ st SKIP = st
evalCmd zero st (WHILE bexp DO cmd DONE) = st
evalCmd zero st (FOR i := exp₁ TO exp₂ DO cmd DONE) = st
evalCmd (suc n) (just st , printList) FOR i := exp₁ TO exp₂ DO cmd DONE = 
    if equal (evalExp st exp₁) (evalExp st exp₂) then
        (just st , printList)
    else
        evalCmd n (evalCmd n (evalCmd n (just st , printList) (i := exp₁)) cmd) (FOR i := exp₁ + ` (suc zero) TO exp₂ DO cmd DONE)
evalCmd n (just st , printList) (PRINT exp) = (just st , ((evalExp st exp) :: printList))

-- Pozor: tip funkcije ima smisel zgolj za osnovni tip rezultata
vsotaPrvihN : Nat → Maybe Nat
-- vsotaPrvihN : Nat → Maybe (State 3)
-- vsotaPrvihN n = (evalCmd 125 ( 0 :: (0 :: (0 :: []))) (vsota n)) [ 0 / 2 ]
-- vsotaPrvihN n = (Pair.fst (evalCmd 125 (just ( 0 :: (0 :: (0 :: []))) , (0 :: [])) (vsota n)))
vsotaPrvihN n = maybeVal (Pair.fst (evalCmd 125 (just ( 0 :: (0 :: (0 :: []))) , (0 :: [])) (vsota n)))
                where 
                maybeVal : (Maybe (State 3)) → Maybe Nat
                maybeVal nothing = nothing
                maybeVal (just st) = just (st [ 0 / 2 ])

