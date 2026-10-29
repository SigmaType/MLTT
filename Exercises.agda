{-# OPTIONS --without-K --safe #-}

module Exercises where

open import Data.Fin.Properties using (suc-injective)
open import Data.Fin using (Fin) renaming (zero to x0 ; suc to _+1)
open import Data.Fin.Patterns
open import Data.Nat.Base renaming (ℕ to N ; suc to S ; pred to pred)
open import Data.List.Base using (List; []; _∷_)
open import Data.Empty
open import Data.Product
open import Data.Sum renaming ([_,_] to ⊎-elim)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Negation
open import Function.Base using (_$_)

open import Untyped

data Bool : Set where
  true : Bool
  false : Bool
  


{-
**Задача 1.** Постройте значения:

```agda
c1 : Context (λ _ → Bool) 3
c2 : Context (λ n → Fin (S n)) 3
```
Во втором случае тип нового элемента зависит от `n`, поэтому не любое число подойдёт на любую позицию.
Подберите допустимые значения и объясните, почему на первой позиции (при `n = 0`) выбор единственный.
-}

c1 : Context (λ _ → Bool) 3
c1 = ((ϵ ∙ true) ∙ false) ∙ true

c2 : Context (λ n → Fin (S n)) 3
c2 = ((ϵ ∙ 0F) ∙ 1F) ∙ 2F

{-
**Задача 2.** Определите функции:

```agda
head : Context A (S n) → A n
tail : Context A (S n) → Context A n
```

Обратите внимание, что для них не нужен случай `ϵ`.
Объясните, почему Agda не требует его разбирать (подсказка: индекс `S n` и `0` не унифицируются).
-}

head : ∀ {n : N} → {A : N → Set} → Context A (S n) → A n
head {n} {A} (ctx ∙ elem) = elem

tail : ∀ {n : N} → {A : N → Set} → Context A (S n) → Context A n
tail {n} {A} (ctx ∙ elem) = ctx

first : ∀ {n : N} {A : N → Set} → Context A (S n) → A zero
first (ϵ ∙ elem) = elem
first ((ctx ∙ elem₁) ∙ elem₂) = first (ctx ∙ elem₁)

-- **Задача 3.** Докажите, что единственный контекст длины 0 это `ϵ`:

ϵ-unique : ∀ {n : N} → {A : N → Set} → (Γ : Context A 0) → Γ ≡ ϵ
ϵ-unique ϵ = refl

{-
**Задача 4.** Определите `map`:

```agda
map : (∀ {n} → A n → B n) → Context A n → Context B n
```

Докажите, что `map id ≡ id` и `map (f ∘ g) ≡ map f ∘ map g`.
-}
mapC : ∀ {n : N} → (A B : N → Set) → (∀ {n} → A n → B n) → Context A n → Context B n
mapC A B f ϵ = ϵ
mapC A B f (ctx ∙ elem) = (mapC A B f ctx) ∙ (f elem)

-- Докажите, что `map id ≡ id`

id1 : {A : Set} → A → A
id1 {A} = λ (a : A) → a

mapC-id : ∀ {n} (A : N → Set) (ctx : Context A n) → mapC {n} A A id1 ctx ≡ ctx
mapC-id A ϵ = refl
mapC-id A (ctx ∙ x) = cong (λ ctx1 → ctx1 ∙ x) (mapC-id A ctx)

-- map (f ∘ g) ≡ map f ∘ map g
compose : ∀ {A B C : Set} → (A → B) → (B → C) → (A → C)
compose {A} {B} {C} f g = λ (x : A) → g (f x)

mapC-compose : ∀ {n} (A B C : N → Set) (ctx : Context A n) 
               (f : ∀ {n} → A n → B n) (g : ∀ {n} → B n → C n) →
               mapC A C (compose f g) ctx ≡ mapC B C g (mapC A B f ctx)
               
mapC-compose A B C ϵ f g = refl
mapC-compose A B C (ctx ∙ a) f g = cong (λ ctx1 → ctx1 ∙ (g (f a))) (mapC-compose A B C ctx f g)

private
  variable
    n m : N

private
  variable
    A F H t u v : Term n
    B E G       : Term (S n)


{- Примеры термов -}

_ : Term n
_ = Π ℕ ▹ Unit

_ : Term n
_ = Σ U ▹ Empty

_ : Term 0
_ =  λ▹ (λ▹ (var 0F)) -- λ x → λ y → y

_ : Term 0
_ =  λ▹ (λ▹ (var 1F)) -- λ x → λ y → x

{-
После добавления
-- количество внешних переменных, которые могут упоминаться в терме
-- [z] - 1 переменная в контексте

-- [y, x, z]
Можно понимать список переменных как стек, где на вершине находится значене последннй переменной
var 2F -
каждый связыватель добавляет переменную в стек, а при обращении мы обращаемся к n-ой переменной слева
-}
_ : Term 1
_ = λ▹ (λ▹ (var 2F)) -- λ x y → z (z - единственная свободная переменная из контекста)


