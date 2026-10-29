{-# OPTIONS --without-K --safe #-}

module Untyped where

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

data Context (A : N → Set) : N → Set where         
 ϵ : Context A 0
 _∙_ : {n : N} → Context A n → A n → Context A (S n)

{-
  A : N → Set --- это терм, который может ссылаться на N переменных
  термы --- это базовые языковы сущности

  ϵ : Context A 0 --- пустой контекст --- это контекст для любого семейства типов
  _∙_ --- добавление элемента в контекст:

    * {n : N} --- количество переменных в контексте, выводится из следующего аргумента
    * Context A n --- контекст с n элементами
    * A n --- терм, который может упоминать n переменных
    * Context A (S n) - контекст с n + 1 переменной

  Термы задаются специальными типами, и контекст может содежать не только термы
-}

infixl 30 _∙_



{-
  A : N → Set - произвольное семейство типов, где могут упоминаться N свободных переменных
  N --- количество внешних переменных в контексте
  список связываний для терма
  List N - список чисел, N-ое число соответствует количеству дополнительных переменных в N-ом терме

  Репрезентирует списки подтермов какого-то терма
-}
data GenTs (A : N → Set) : N → List N → Set where   
  []  : {n : N} → GenTs A n []                 -- Список термов (вместо A будем подставлять Term) в контексте внешних переменных n,
  _∷_ : {n b : N} {bs : List N}                -- тип которого для каждого терма хранит число дополнительных переменных, на которые
      → (t : A (b + n))                        -- он может ссылаться вдобавок к внешним
      → (ts : GenTs A n bs)
      → GenTs A n (b ∷ bs)

{-
  Примитивные синтаксические формы MLTT
  
  
-}
data Kind : (ns : List N) → Set where
  Ukind : Kind []                              -- Universum - вселенная, без дополнительных переменных

{-
Тип 
Π A (λ x : A → B(x))

Аналог записи сигма типа из Agda:
Σ Nat (\n -> Vec Bool n)

Пример 
Π_▹_ : Term n → Term (S n) → Term n
Π A ▹ B = gen Pikind (A ∷ B ∷ [])
-}

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
  -- bs - список упоминаний: сколько дополнительных переменных может упоминать каждый подтерм терма
 -- k - синтаксическая форма
 -- t - список подтермов для k

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


data Neutral : Term n → Set where           -- Терм нейтрален, если в головной позиции переменная, то есть вычисление застревает
  varⁿ      :(x : Fin n) → Neutral (var x)
  ∘ⁿ        : Neutral t   → Neutral (t ∘ u)
  fstⁿ      : Neutral t   → Neutral (fst t) 
  sndⁿ      : Neutral t   → Neutral (snd t)
  natrecⁿ   : Neutral v   → Neutral (natrec G t u v)
  Emptyrecⁿ : Neutral t   → Neutral (Emptyrec A t)


data Whnf {n : N} : Term n → Set where   
  Uⁿ     : Whnf U                         -- Определение того, какой терм находится в слабой головной нормальной форме
  Πⁿ     : Whnf (Π A ▹ B)
  Σⁿ     : Whnf (Σ A ▹ B)
  ℕⁿ     : Whnf ℕ
  Unitⁿ  : Whnf Unit
  Emptyⁿ : Whnf Empty

  λ▹ⁿ   : Whnf (λ▹ t)
  zeroⁿ : Whnf o
  sucⁿ  : Whnf (suc t)
  starⁿ : Whnf star
  prodⁿ : Whnf (prod t u)

  ne    : Neutral t → Whnf t

data BindingType : Set where
  BΠ : BindingType
  BΣ : BindingType

[_]_▹_ : BindingType → Term n → Term (S n) → Term n   -- Эти два определения помогают единообразно обрабатывать   
[ BΠ ] F ▹ G = Π F ▹ G                                --  сигма- и пи-типы для некоторых лемм
[ BΣ ] F ▹ G = Σ F ▹ G

B-PE-injectivity : ∀ W → [ W ] F ▹ G ≡ [ W ] H ▹ E → F ≡ H × G ≡ E
B-PE-injectivity BΠ refl = refl , refl
B-PE-injectivity BΣ refl = refl , refl
                                                  -- Полезная лемма об инъективности для технических лемм
suc-PE-injectivity : suc t ≡ suc u → t ≡ u
suc-PE-injectivity refl = refl


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
  oⁿ :    Natural o                          -- Техническое нерекурсивное определение для более простых доказательств про ℕ и Whnf
  sucⁿ  : Natural (suc t)
  ne    : Neutral t → Natural t


data Type {n : N} : Term n → Set where     -- Определение того, что является типом (обрати внимание, что U - не тип)
  Πⁿ    :             Type (Π A ▹ B)
  Σⁿ    :             Type (Σ A ▹ B)
  ℕⁿ     :             Type ℕ
  Emptyⁿ :             Type Empty
  Unitⁿ  :             Type Unit
  ne     : Neutral t → Type t

data Function {n : N} : Term n → Set where  -- Определение того, что является функцией
  λ▹ⁿ : Function (λ▹ t)
  ne : Neutral t → Function t

data Product {n : N} : Term n → Set where
  prodⁿ : Product (prod t u)
  ne    : Neutral t → Product t


-- Сейчас пойдут определения функций, которые обитателей индуктивных типов выше "превращают" в Whnf (что неудивительно)

naturalWhnf : Natural t → Whnf t
naturalWhnf sucⁿ   = sucⁿ
naturalWhnf oⁿ  = zeroⁿ
naturalWhnf (ne x) = ne x

typeWhnf : Type A → Whnf A
typeWhnf Πⁿ     = Πⁿ
typeWhnf Σⁿ    = Σⁿ
typeWhnf ℕⁿ     = ℕⁿ
typeWhnf Emptyⁿ = Emptyⁿ
typeWhnf Unitⁿ  = Unitⁿ
typeWhnf (ne x) = ne x

functionWhnf : Function t → Whnf t
functionWhnf λ▹ⁿ   =  λ▹ⁿ
functionWhnf (ne x) = ne x

productWhnf : Product t → Whnf t
productWhnf prodⁿ  = prodⁿ
productWhnf (ne x) = ne x

[]ⁿ : (W : BindingType) → Whnf ([ W ] F ▹ G)
[]ⁿ BΠ = Πⁿ
[]ⁿ BΣ = Σⁿ

data Wk : N → N → Set where                     -- Операция ослабления контекста(из n переменных в m такой, что n ≤ m)
  id    : {n : N} → Wk n n                      -- Тривиальное ослабление
  step  : {n m : N} → Wk m n → Wk (S m) n       -- Из n в m + 1
  lift  : {n m : N} → Wk m n → Wk (S m) (S n)   -- Используется для связывателей типа λ▹ или Π (детально пока не разобрался)
