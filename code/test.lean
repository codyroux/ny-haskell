import data.nat.div

print prefix dvd
print notation ∣
print notation +
check (3 ∣ 6)
-- print prefix ∣
print prefix num

print definition nat.add

definition pred : ℕ → ℕ
| pred 0 := 0
| pred (nat.succ n') := n'

definition add_nat : ℕ → ℕ → ℕ
| add_nat 0 m := m
| add_nat (nat.succ n') m := nat.succ (add_nat n' m)

definition mul_nat : ℕ → ℕ → ℕ
| mul_nat 0 m := m
| mul_nat (nat.succ n') m := add_nat m (mul_nat n' m)

definition prime = 2 ≤ p ∧ (d ∣ p → d = 1 ∨ d = p)

