{-# OPTIONS --without-K --safe #-}

module Untyped where

open import Data.Fin.Properties using (suc-injective)
open import Data.Fin using (Fin) renaming (zero to x0 ; suc to _+1)
open import Data.Fin.Patterns
open import Data.Nat.Base renaming (ℕ to N ; suc to S)
open import Data.List.Base using (List; []; _∷_)
open import Data.Empty
open import Data.Product
open import Data.Sum renaming ([_,_] to ⊎-elim)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Negation
open import Function.Base using (_$_)

data Context (A : N → Set) : N → Set where
 ϵ : Context A 0
 _∙_ : {n : N} → Context A n → A n → Context A (S n)

infixl 30 _∙_


data GenTs (A : N → Set) : N → List N → Set where
  []  : {n : N} → GenTs A n []
  _∷_ : {n b : N} {bs : List N}
      → (t : A (b + n))
      → (ts : GenTs A n bs)
      → GenTs A n (b ∷ bs)

 
data Kind : (ns : List N) → Set where
  Ukind : Kind []

  Pikind  : Kind (0 ∷ 1 ∷ [])
  Lamkind : Kind (1 ∷ [])
  Appkind : Kind (0 ∷ 0 ∷ [])

  Sigmakind : Kind (0 ∷ 1 ∷ [])
  Prodkind  : Kind (0 ∷ 0 ∷ [])
  Fstkind   : Kind (0 ∷ [])
  Sndkind   : Kind (0 ∷ [])

  Natkind    : Kind []
  Zerokind   : Kind []
  Suckind    : Kind (0 ∷ [])
  Natreckind : Kind (1 ∷ 0 ∷ 0 ∷ 0 ∷ [])

  Unitkind : Kind []
  Starkind : Kind []

  Emptykind    : Kind []
  Emptyreckind : Kind (0 ∷ 0 ∷ [])


data Term (n : N) : Set where
 var : Fin n → Term n
 gen : {bs : List N} (k : Kind bs) (t : GenTs Term n bs) → Term n

private
  variable
    n m : N

private
  variable
    A F H t u v : Term n
    B E G       : Term (S n)

-- Определим примитивные термы и типы нашей MLTT --

U : Term n
U = gen Ukind []

Π_▹_ : Term n → Term (S n) → Term n
Π A ▹ B = gen Pikind (A ∷ B ∷ [])

λ▹ : Term (S n) → Term n
λ▹ A = gen Lamkind (A ∷ [])

_∘_    : (t u : Term n) → Term n    
t ∘ u = gen Appkind (t ∷ u ∷ [])

Σ_▹_ : (A : Term n) (B : Term (S n)) → Term n 
Σ A ▹ B = gen Sigmakind (A ∷ B ∷ [])

prod : (t u : Term n) → Term n      
prod t u = gen Prodkind (t ∷ u ∷ [])

fst : (t : Term n) → Term n       
fst t = gen Fstkind (t ∷ [])

snd : (t : Term n) → Term n
snd t = gen Sndkind (t ∷ [])

ℕ : Term n                   
ℕ = gen Natkind []

o : Term n                     
o = gen Zerokind []

suc : (t : Term n) → Term n
suc t = gen Suckind (t ∷ [])

natrec : (A : Term (S n)) (t u v : Term n) → Term n  
natrec A t u v = gen Natreckind (A ∷ t ∷ u ∷ v ∷ [])

Unit : Term n                       
Unit = gen Unitkind []

star : Term n                       
star = gen Starkind []

Empty : Term n                      
Empty = gen Emptykind []

Emptyrec : (A e : Term n) → Term n 
Emptyrec A e = gen Emptyreckind (A ∷ e ∷ [])

_ : Term n
_ = Π ℕ ▹ Unit

_ : Term n
_ = Σ U ▹ Empty

_ : Term 0
_ =  λ▹ (λ▹ (var 0F)) -- λ x y → y

_ : Term 0
_ =  λ▹ (λ▹ (var 1F)) -- λ x y → x

_ : Term 1
_ = λ▹ (λ▹ (var 2F)) -- λ x y → z (z - единственная свободная переменная из контекста)

data BindingType : Set where
  BΠ : BindingType
  BΣ : BindingType

[_]_▹_ : BindingType → Term n → Term (S n) → Term n   -- Это определение помогает единообразно обрабатывать   
[ BΠ ] F ▹ G = Π F ▹ G                                --  сигма- и пи-типы для некоторых лемм
[ BΣ ] F ▹ G = Σ F ▹ G

B-PE-injectivity : ∀ W → [ W ] F ▹ G ≡ [ W ] H ▹ E → F ≡ H × G ≡ E
B-PE-injectivity BΠ refl = refl , refl
B-PE-injectivity BΣ refl = refl , refl
                                                  -- Полезная лемма об инъективности для технических лемм
suc-PE-injectivity : suc t ≡ suc u → t ≡ u
suc-PE-injectivity refl = refl

data Neutral : Term n → Set where
  varⁿ       : (x : Fin n) → Neutral (var x)
  ∘ⁿ        : Neutral t   → Neutral (t ∘ u)
  fstⁿ      : Neutral t   → Neutral (fst t)  -- Терм нейтрален, если в головной позиции переменная, то есть вычисление застревает
  sndⁿ      : Neutral t   → Neutral (snd t)
  natrecⁿ   : Neutral v   → Neutral (natrec G t u v)
  Emptyrecⁿ : Neutral t   → Neutral (Emptyrec A t)


data Whnf {n : N} : Term n → Set where   
  Uⁿ     : Whnf U                         -- Определение того, какой терм находится в слабой головной нормальной форме
  Πⁿ     : Whnf (Π A ▹ B)
  Σⁿ    : Whnf (Σ A ▹ B)
  ℕⁿ     : Whnf ℕ
  Unitⁿ  : Whnf Unit
  Emptyⁿ : Whnf Empty

  λ▹ⁿ  : Whnf (λ▹ t)
  zeroⁿ : Whnf o
  sucⁿ  : Whnf (suc t)
  starⁿ : Whnf star
  prodⁿ : Whnf (prod t u)

  ne    : Neutral t → Whnf t


U≢ne : Neutral A → U ≢ A         -- Сейчас будет ряд технических лемм о нейтральности и конструкторах Whnf
U≢ne () refl

ℕ≢ne : Neutral A → ℕ ≢ A
ℕ≢ne () refl

Empty≢ne : Neutral A → Empty ≢ A
Empty≢ne () refl

Unit≢ne : Neutral A → Unit ≢ A
Unit≢ne () refl

B≢ne : ∀ W → Neutral A → [ W ] F ▹ G ≢ A
B≢ne BΠ () refl
B≢ne BΣ () refl

U≢B : ∀ W → U ≢ [ W ] F ▹ G
U≢B BΠ ()
U≢B BΣ ()

ℕ≢B : ∀ W → ℕ ≢ [ W ] F ▹ G
ℕ≢B BΠ ()
ℕ≢B BΣ ()

Empty≢B : ∀ W → Empty ≢ [ W ] F ▹ G
Empty≢B BΠ ()
Empty≢B BΣ ()

Unit≢B : ∀ W → Unit ≢ [ W ] F ▹ G
Unit≢B BΠ ()
Unit≢B BΣ ()

zero≢ne : Neutral t → o ≢ t
zero≢ne () refl

suc≢ne : Neutral t → suc u ≢ t
suc≢ne () refl


data Natural {n : N} : Term n → Set where
  oⁿ :             Natural o              -- Техническое нерекурсивное определение для более простых доказательств про ℕ и Whnf
  sucⁿ  :             Natural (suc t)
  ne    : Neutral t → Natural t

