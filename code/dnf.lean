import data.bool logic logic.connectives

section dnf

-- The type of syntactic formulae with "A"s at the leaves
inductive Formula (A : Type) : Type :=
| Var     : A → Formula A
| Not     : Formula A → Formula A
| And     : Formula A → Formula A → Formula A
| Or      : Formula A → Formula A → Formula A
-- | Implies : Formula A → Formula A → Formula A

print bool

open Formula bool

-- This function distributes a (simple) formula over disjunctions on the right
definition right_conj {A : Type} : Formula A → Formula A → Formula A
| right_conj a (Or b c) := Or (right_conj a b) (right_conj a c)
| right_conj a d        := And a d

-- This function distributes a formula over disjunctions on the left
definition conjunct {A : Type} : Formula A → Formula A → Formula A
| conjunct (Or a b) c := Or (conjunct a c) (conjunct b c)
| conjunct d        c := right_conj d c

-- This function simultaneously computes the Disjunctive Normal Form (DNF) of a formula
-- and the DNF of its negation depending on the flag.

-- Both are required simultaneously in order for the function to work.
definition dnf_aux {A : Type} : bool → Formula A → Formula A
| dnf_aux tt (Var v)   := Var v
| dnf_aux ff (Var v)   := Not (Var v)
| dnf_aux tt (Not a)   := dnf_aux ff a
| dnf_aux ff (Not a)   := dnf_aux tt a
| dnf_aux tt (And a b) := conjunct (dnf_aux tt a) (dnf_aux tt b)
| dnf_aux ff (And a b) := Or (dnf_aux ff a) (dnf_aux ff b)
| dnf_aux tt (Or a b)  := Or (dnf_aux tt a) (dnf_aux tt b)
| dnf_aux ff (Or a b)  := conjunct (dnf_aux ff a) (dnf_aux ff b)

definition dnf {A : Type} := @dnf_aux A tt

-- Let's test our function, to see if it works as expected
section test_eval

variable A : Type

variables f g h i : A


eval dnf (Or (And (Var f) (Or (Var g) (Var h))) (Var i))


theorem test : dnf (Or (And (Var f) (Or (Var g) (Var h))) (Var i)) = Or (Or (And (Var f) (Var g)) (And (Var f) (Var h))) (Var i)
 
:= by apply eq.refl

end test_eval


definition interp : Formula Prop → Prop
| interp (Var p)   := p
| interp (Not a)   := ¬ (interp a)
| interp (And a b) := (interp a) ∧ (interp b)
| interp (Or a b)  := (interp a) ∨ (interp b)

notation `⟦` φ `⟧` := interp φ

print prefix Formula

open eq.ops

check and.left_distrib


lemma right_conj_correct1 {P Q} : ⟦right_conj P Q⟧ → ⟦P⟧ ∧ ⟦Q⟧ :=
  Formula.induction_on Q
    (assume a H, H)
    (assume a H1 H2, H2)
    (assume a b H1 H2 H3, H3)
    proof
      assume a b H1 H2 H3, show ⟦P⟧ ∧ (⟦a⟧ ∨ ⟦b⟧), from
        iff.elim_right (and.left_distrib _ _ _)
        begin
          apply (or.imp H1 H2),
          apply H3
        end
    qed


-- more of the above
lemma conjunct_correct1 {P Q} : ⟦conjunct P Q⟧ → ⟦P⟧ ∧ ⟦Q⟧ := 
  Formula.induction_on P
    (assume a, right_conj_correct1)
    (assume a H, right_conj_correct1)
    (assume a b H1 H2, right_conj_correct1)
    proof
      assume a b H1 H2 H3,
        iff.elim_right (and.right_distrib _ _ _)
        begin
          apply (or.imp H1 H2),
          apply H3
        end
    qed

check non_contradictory_intro
check and_of_and_of_imp_of_imp


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

-- This lemma is tougher! We need to prove the positive and negative cases for dnf_aux simultaneously
lemma dnf_aux_correct1 {P} : (⟦dnf_aux tt P⟧ → ⟦P⟧) ∧ (⟦dnf_aux ff P⟧ → ¬ ⟦P⟧) :=
proof
  Formula.induction_on P
    (begin intros a, constructor, all_goals (intro H; exact H) end)
    (proof
      assume a H,
        obtain (H1 : ⟦dnf_aux tt a⟧ → ⟦a⟧)
               (H2 : ⟦dnf_aux ff a⟧ → ¬⟦a⟧),
               from H,
        and.intro
         (show ⟦dnf_aux tt (Not a)⟧ → ⟦Not a⟧, from H2)
         (assume H3 : ⟦dnf_aux ff (Not a)⟧,
           assert H4 : ⟦a⟧, from H1 H3,
           show ¬(¬⟦a⟧), from
             non_contradictory_intro H4)
     qed)
    (proof
      assume a b H1 H2,
        assert L : ⟦dnf_aux tt (And a b)⟧ → ⟦And a b⟧, from
          (proof
            assume H3 : ⟦dnf_aux tt (And a b)⟧,
            assert H3' : ⟦dnf_aux tt a⟧ ∧ ⟦dnf_aux tt b⟧, from
              conjunct_correct1 H3,
            show ⟦a⟧ ∧ ⟦b⟧, from
             assert H1' : ⟦dnf_aux tt a⟧ → ⟦a⟧, from and.left H1,
             assert H2' : ⟦dnf_aux tt b⟧ → ⟦b⟧, from and.left H2,
              and_of_and_of_imp_of_imp H3' H1' H2'
            qed),
          assert R : ⟦dnf_aux ff (And a b)⟧ → ¬⟦And a b⟧, from 
            proof
              assume H3 : ⟦dnf_aux ff (And a b)⟧,

              show ¬ (⟦a⟧ ∧ ⟦b⟧), from
              assert D : ¬⟦a⟧ ∨ ¬⟦b⟧, from
                proof
                  show ¬⟦a⟧ ∨ ¬⟦b⟧, from
                  assert H1' : ⟦dnf_aux ff a⟧ → ¬⟦a⟧, from and.right H1,
                  assert H2' : ⟦dnf_aux ff b⟧ → ¬⟦b⟧, from and.right H2,
                    or.imp H1' H2' H3
                qed,
                  or_not_not_and D
            
            qed,
        and.intro L R
      qed)
      begin
        intros a b H1 H2,
        split,
        intro H,
        esimp [interp],
        esimp [interp, dnf_aux] at H,
        cases H with H' H',
          {
            clear H2,
            left,
            cases H1 with L R,
            apply L,
            assumption
          },

          {
            clear H1,
            right,
            cases H2 with L R,
            apply L,
            assumption
          },
        intro H,
        esimp [interp],
        apply (@and_not_not_or ⟦a⟧ ⟦b⟧),
        split,
          {
            cases H1 with L R,
            apply R,
            esimp [dnf_aux] at H,
            apply and.left,
            apply conjunct_correct1,
            exact H
          },
          {
            cases H2 with L R,
            apply R,
            esimp [dnf_aux] at H,
            apply and.right,
            apply conjunct_correct1,
            exact H
          }
        end
qed

lemma dnf_correct1 {P} : ⟦dnf P⟧ → ⟦P⟧ := by exact (and.left dnf_aux_correct1)

-- this actually needs EM
lemma dnf_correct2 {P} : ⟦P⟧ → ⟦dnf P⟧ := sorry

print prefix iff
theorem dnf_correct {P} : ⟦dnf P⟧ ↔ ⟦P⟧ :=
proof
   have H1 : ⟦dnf P⟧ → ⟦P⟧, from dnf_correct1,
   have H2 : ⟦P⟧ → ⟦dnf P⟧, from dnf_correct2,
     iff.intro H1 H2
qed

-- The reifiable class captures the propositions which have a
-- representation in syntax, which is witnessed by the "is_reification"
-- field.
structure reifiable [class] (P : Prop) := (phi : Formula Prop)(is_reification : P = ⟦phi⟧)

-- we could have chosen P ↔ ⟦phi⟧ alternatively


open reifiable

-- We define class instances for reifiable for all the formulae that
-- we want to be able to reify
definition atom_reifiable [instance] {A : Type} {x y : A} : reifiable (x = y) :=
 reifiable.mk (Var (x = y)) (eq.refl _)


definition neg_reifiable [instance] {P : Prop} [h : reifiable P] : reifiable (¬ P) :=
  reifiable.mk (Not (phi P))
  (
    calc
      (¬ P) = (¬ ⟦phi P⟧) : {is_reification P}
      ...   = ⟦Not (phi P)⟧ : eq.refl
  )

definition neg_atom_reifiable [instance] {A : Type} {x y : A} : reifiable (x ≠ y) :=
  neg_reifiable

definition conjunct_reifiable [instance] {P Q : Prop} [h : reifiable P] [i : reifiable Q] :
  reifiable (P ∧ Q) :=
  reifiable.mk (And (phi P) (phi Q))
  (
    calc
      (P ∧ Q) = (⟦phi P⟧ ∧ Q)         : {is_reification P}
      ...     = (⟦phi P⟧ ∧ ⟦phi Q⟧)    : {is_reification Q}
      ...     = ⟦And (phi P) (phi Q)⟧ : eq.refl
     
  )

definition disjunct_reifiable [instance] {P Q : Prop} [h : reifiable P] [i : reifiable Q] :
  reifiable (P ∨ Q) :=
  reifiable.mk (Or (phi P) (phi Q))
  (
    calc
      (P ∨ Q) = (⟦phi P⟧ ∨ Q)        : {is_reification P}
      ...     = (⟦phi P⟧ ∨ ⟦phi Q⟧)   : {is_reification Q}
      ...     = ⟦Or (phi P) (phi Q)⟧ : eq.refl
     
  )


print prefix iff

lemma normalize {P : Prop} [h : reifiable P] : ⟦dnf (phi P)⟧ ↔ P :=
  calc
    ⟦dnf (phi P)⟧ ↔ ⟦phi P⟧ : dnf_correct
    ...          ↔ P       : by rewrite- is_reification



variable A : Type
variables x y z : A


definition pdnf (P : Prop) [h : reifiable P] : Prop := ⟦dnf (phi P)⟧

lemma test' : reifiable (¬ (x = y ∧ y = z) ∨ x = z) := _

lemma test'' : reifiable ((¬ (x = y) ∨ ¬ (y = z)) ∨ x = z) := _

eval (pdnf (¬ (x = y ∧ y = z)))
lemma compute_dnf : pdnf (¬ (x = y ∧ y = z)) = ((x = y → false) ∨ (y = z → false)) := eq.refl _
help options

set_option pp.implicit true

lemma test_normalize : ((x ≠ y ∨ y ≠ z) ∨ x = z) ↔ (¬ (x = y ∧ y = z) ∨ x = z) :=
  proof
    normalize
  qed

end dnf
