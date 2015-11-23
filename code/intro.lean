import logic logic.connectives

lemma and_left_distrib {a b c} : a ∧ (b ∨ c) ↔ (a ∧ b) ∨ (a ∧ c) := sorry
lemma or_imp {a b c d} : (a → c) → (b → d) →  (a ∨ b) → (c ∨ d) := sorry

check and_of_and_of_imp_of_imp

lemma and_imp {a b c d} : (a → c) → (b → d) →  (a ∧ b) → (c ∧ d) := begin intros H1 H2 H3, apply and_of_and_of_imp_of_imp; assumption; assumption; assumption end

print prefix or

check or.by_cases

lemma or_not_not_and {a b : Prop} : (¬ a) ∨ (¬ b) → ¬ (a ∧ b) :=
proof
  assume (H1 : ¬ a ∨ ¬ b)(H2 : a ∧ b),
  show false, from
    or.cases_on H1
    (begin intros H3; apply H3; cases H2; assumption end)
    (begin intros H3; apply H3; cases H2; assumption end)
qed

lemma and_not_not_or {a b : Prop} : (¬ a) ∧ (¬ b) → ¬ (a ∨ b) :=
begin
  intros H1 H2,
  cases H1 with L R,
  cases H2 with H2' H2',
  {apply L, assumption},
  {apply R, assumption}
end

reveal or_not_not_and

print or_not_not_and
