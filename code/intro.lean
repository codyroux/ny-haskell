-- We can import all the theorems from various places from the std lib
import logic logic.connectives

-- remember to use open to not have to prefix them!

help commands

section intro

parameters a b c d : Prop

print notation ↔

-- This is probably the most useful command in Lean
print prefix iff

-- Let's try a "isar-style" proof here
lemma and_left_distrib : a ∧ (b ∨ c) ↔ (a ∧ b) ∨ (a ∧ c) := sorry

reveal and_left_distrib

print and_left_distrib

-- Let's try a tactic proof here

lemma or_imp : (a → c) → (b → d) →  (a ∨ b) → (c ∨ d) := sorry

check and_of_and_of_imp_of_imp

lemma and_imp : (a → c) → (b → d) →  (a ∧ b) → (c ∧ d) := sorry


print prefix or

lemma or_not_not_and : (¬ a) ∨ (¬ b) → ¬ (a ∧ b) := sorry

lemma and_not_not_or : (¬ a) ∧ (¬ b) → ¬ (a ∨ b) := sorry

-- This requires the excluded middle

-- hypothesis em [instance] {a : Prop} : decidable a
-- small hack:
definition em [instance] {a : Prop} : decidable a := sorry

print prefix decidable

-- What kind of proof do you want here?
lemma not_and_or_not : ¬ (a ∧ b) → ¬ a ∨ ¬ b := sorry

end intro

