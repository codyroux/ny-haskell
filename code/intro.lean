-- We can import all the theorems from various places from the std lib
import logic logic.connectives

-- remember to use open to not have to prefix them!

help commands

section intro

parameters a b c : Prop

print notation ↔

-- This is probably the most useful command in Lean
print prefix iff

lemma and_left_distrib : a ∧ (b ∨ c) ↔ (a ∧ b) ∨ (a ∧ c) := sorry

reveal and_left_distrib

print and_left_distrib

lemma or_imp : (a → c) → (b → d) →  (a ∨ b) → (c ∨ d) := sorry

check and_of_and_of_imp_of_imp

lemma and_imp {a b c d} : (a → c) → (b → d) →  (a ∧ b) → (c ∧ d) := sorry


print prefix or

lemma or_not_not_and {a b : Prop} : (¬ a) ∨ (¬ b) → ¬ (a ∧ b) := sorry

lemma and_not_not_or {a b : Prop} : (¬ a) ∧ (¬ b) → ¬ (a ∨ b) := sorry

-- This requires the excluded middle

axiom em {a : Prop} : decidable a
attribute em [instance]

print prefix decidable

lemma not_and_or_not {a b : Prop} : ¬ (a ∧ b) → ¬ a ∨ ¬ b := _


