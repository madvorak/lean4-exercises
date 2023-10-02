import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.Simps.Basic

-- FLT imported from a suspicious source:
theorem FLT {a b c n : Nat} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hn : 2 < n) :
  a ^ n + b ^ n ≠ c ^ n := sorry


-- From now only trusted code follows:

inductive MyNat
| zer : MyNat
| suc : MyNat → MyNat

def MyAdd (n : MyNat) : MyNat → MyNat
| MyNat.zer   => n
| MyNat.suc m => MyNat.suc (MyAdd n m)

def MyMul (n : MyNat) : MyNat → MyNat
| MyNat.zer   => MyNat.zer
| MyNat.suc m => MyAdd n (MyMul n m)

def MyPow (n : MyNat) : MyNat → MyNat
| MyNat.zer   => MyNat.suc MyNat.zer
| MyNat.suc m => MyMul n (MyPow n m)


def MyNat.toNat : MyNat → Nat
| MyNat.zer   => Nat.zero
| MyNat.suc n => Nat.succ n.toNat

lemma myAdd_left_suc (x y : MyNat) :
  MyAdd (MyNat.suc x) y = MyNat.suc (MyAdd x y) :=
by
  induction y with
  | zer => simp [MyAdd]
  | suc m ih => simp [MyAdd, ih]

lemma myAdd_toNat {a b c : MyNat} (hyp : MyAdd a b = c) :
  a.toNat + b.toNat = c.toNat :=
by
  revert a c
  induction b with
  | zer =>
    intro a c hyp
    rw [show a = c by assumption]
    rfl
  | suc m ih =>
    intro a c hyp
    specialize @ih a.suc c
    simp_all [Nat.add_succ, Nat.succ_add, MyAdd, MyNat.toNat, myAdd_left_suc]

lemma myMul_toNat {a b c : MyNat} (hyp : MyMul a b = c) :
  a.toNat * b.toNat = c.toNat :=
by
  revert a c
  induction b with
  | zer =>
    intro a c hyp
    rw [← (show MyNat.zer = c by assumption)]
    rfl
  | suc m ih =>
    sorry

lemma myPow_toNat {a b c : MyNat} (hyp : MyPow a b = c) :
  a.toNat ^ b.toNat = c.toNat :=
by
  sorry

theorem MyFLT (a b c n : MyNat) :
  MyAdd
    (MyPow a.suc n.suc.suc.suc)
    (MyPow b.suc n.suc.suc.suc)
  ≠ (MyPow c.suc n.suc.suc.suc) :=
by
  have ha : 0 < a.suc.toNat
  · simp [MyNat.toNat]
  have hb : 0 < b.suc.toNat
  · simp [MyNat.toNat]
  have hc : 0 < c.suc.toNat
  · simp [MyNat.toNat]
  have hn : 2 < n.suc.suc.suc.toNat
  · simp only [MyNat.toNat]
    exact Nat.lt_of_sub_eq_succ rfl
  by_contra hyp
  apply FLT ha hb hc hn
  convert myAdd_toNat hyp <;> apply myPow_toNat <;> rfl
