import HRS.MC.CepH5C1

/-!
# Packet C, L2 (`h5_class_constancy`), part a: the rotation/re-reading lemma

If a configuration `x₀` has strictly ordered lifts `Z0` along `π` and `y` along `σ` (`σ 0 = 0`), and a configuration `xt`
has a strictly ordered lift `Zt` along the same `π`, then `xt` has a strictly ordered lift along `σ`.
The lift is `Zt i + [rank_π i < rank_π 0]`; `σ` is recovered as the sorting permutation of the offsets.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.CepH5Pf

open HRS

section Rotation

variable {N : ℕ} [NeZero N]

lemma h5c_plus_lt_core (f : Fin N → ℝ) (hf : StrictMono f) (hf2 : ∀ a b, f a < f b + 1) (a b c : Fin N) :
    (f a + (if a < c then 1 else 0) < f b + (if b < c then 1 else 0)) ↔
      ((c ≤ a ∧ c ≤ b ∧ a < b) ∨ (a < c ∧ b < c ∧ a < b) ∨ (c ≤ a ∧ b < c)) := by
  by_cases h1 : a < c <;> by_cases h2 : b < c
  · rw [if_pos h1, if_pos h2]
    constructor
    · intro h; exact Or.inr (Or.inl ⟨h1, h2, hf.lt_iff_lt.1 (by linarith)⟩)
    · rintro (⟨h, _⟩ | ⟨_, _, h⟩ | ⟨h, _⟩)
      · exact absurd h (not_le.2 h1)
      · linarith [hf h]
      · exact absurd h (not_le.2 h1)
  · rw [if_pos h1, if_neg h2]
    constructor
    · intro h; linarith [hf2 b a]
    · rintro (⟨h, _⟩ | ⟨_, h, _⟩ | ⟨h, _⟩)
      · exact absurd h (not_le.2 h1)
      · exact absurd h h2
      · exact absurd h (not_le.2 h1)
  · rw [if_neg h1, if_pos h2]
    constructor
    · intro _; exact Or.inr (Or.inr ⟨not_lt.1 h1, h2⟩)
    · intro _; linarith [hf2 a b]
  · rw [if_neg h1, if_neg h2, add_zero, add_zero]
    constructor
    · intro h; exact Or.inl ⟨not_lt.1 h1, not_lt.1 h2, hf.lt_iff_lt.1 h⟩
    · rintro (⟨_, _, h⟩ | ⟨h, _⟩ | ⟨_, h⟩)
      · exact hf h
      · exact absurd h h1
      · exact absurd h h2

lemma h5c_plus_range (f : Fin N → ℝ) (hf : StrictMono f) (hf2 : ∀ a b, f a < f b + 1) (a c : Fin N) :
    0 ≤ f a + (if a < c then 1 else 0) - f c ∧ f a + (if a < c then 1 else 0) - f c < 1 := by
  by_cases h : a < c
  · rw [if_pos h]
    have := hf h; have := hf2 c a; constructor <;> linarith
  · rw [if_neg h, add_zero]
    have := hf.monotone (not_lt.1 h); have := hf2 a c; constructor <;> linarith

lemma h5c_coe_of_int {a b : ℝ} {n : ℤ} (h : a - b = n) : ((a : ℝ) : UnitAddCircle) = (b : UnitAddCircle) := by
  rw [← sub_eq_zero, ← AddCircle.coe_sub, AddCircle.coe_eq_zero_iff]
  exact ⟨n, by simpa using h.symm⟩

lemma h5c_sort_eq {σ : Equiv.Perm (Fin N)} {y : Fin N → Euc 1} (hy : cep_StrictlyOrdered σ y) :
    σ = Tuple.sort (fun i => y i 0) := by
  rw [Tuple.eq_sort_iff]
  refine ⟨fun a b hab => ?_, fun i j hij hEq => ?_⟩
  · rcases eq_or_lt_of_le hab with h | h
    · subst h; exact le_rfl
    · exact (hy.1 a b h).le
  · exact absurd hEq (ne_of_lt (hy.1 i j hij))

lemma h5c_sort_congr (f g : Fin N → ℝ) (h : ∀ i j, f i < f j ↔ g i < g j) :
    Tuple.sort f = Tuple.sort g := by
  have hf := Tuple.monotone_sort f
  have hties := (Tuple.eq_sort_iff (f := f) (σ := Tuple.sort f)).1 rfl
  rw [Tuple.eq_sort_iff]
  refine ⟨fun a b hab => ?_, fun i j hij hEq => ?_⟩
  · simp only [Function.comp]
    by_contra hlt
    rw [not_le] at hlt
    have := (h _ _).2 hlt
    have := hf hab
    simp only [Function.comp] at this
    exact absurd this (not_le.2 (by assumption))
  · apply hties.2 i j hij
    by_contra hne
    rcases lt_or_gt_of_ne hne with h1 | h1
    · exact absurd hEq (ne_of_lt ((h _ _).1 h1))
    · exact absurd hEq (ne_of_gt ((h _ _).1 h1))

lemma h5c_core {π σ : Equiv.Perm (Fin N)} (h0 : σ 0 = 0) {y Z0 Zt : Fin N → Euc 1}
    (hy : cep_StrictlyOrdered σ y) (hZ0 : cep_StrictlyOrdered π Z0) (hZt : cep_StrictlyOrdered π Zt)
    (hmk : (fun i => Torus.mk (y i)) = fun i => Torus.mk (Z0 i)) :
    ∃ y' : Fin N → Euc 1, (fun i => Torus.mk (y' i)) = (fun i => Torus.mk (Zt i)) ∧
      cep_StrictlyOrdered σ y' := by
  let plus : (Fin N → Euc 1) → Fin N → ℝ := fun Z i => Z i 0 + (if π.symm i < π.symm 0 then 1 else 0)
  have hplus_eq : ∀ Z i, plus Z i =
      (fun k => Z (π k) 0) (π.symm i) + (if π.symm i < π.symm 0 then 1 else 0) := by
    intro Z i; simp [plus]
  have hplus0 : ∀ Z, plus Z 0 = Z 0 0 := by intro Z; simp [plus]
  have hf : ∀ Z, cep_StrictlyOrdered π Z → StrictMono fun k => Z (π k) 0 :=
    fun Z hZ a b h => hZ.1 a b h
  have hf2 : ∀ Z, cep_StrictlyOrdered π Z → ∀ a b, Z (π a) 0 < Z (π b) 0 + 1 :=
    fun Z hZ a b => hZ.2 b a
  have F1 : ∀ i j, plus Z0 i < plus Z0 j ↔ plus Zt i < plus Zt j := by
    intro i j
    rw [hplus_eq Z0 i, hplus_eq Z0 j, hplus_eq Zt i, hplus_eq Zt j,
      h5c_plus_lt_core _ (hf _ hZ0) (hf2 _ hZ0), h5c_plus_lt_core _ (hf _ hZt) (hf2 _ hZt)]
  have F2 : ∀ Z, cep_StrictlyOrdered π Z → ∀ i, 0 ≤ plus Z i - Z 0 0 ∧ plus Z i - Z 0 0 < 1 := by
    intro Z hZ i
    have := h5c_plus_range (fun k => Z (π k) 0) (hf Z hZ) (hf2 Z hZ) (π.symm i) (π.symm 0)
    simpa [plus] using this
  have hint : ∀ Z i, ∃ m : ℤ, plus Z i - Z i 0 = m := by
    intro Z i
    by_cases h : π.symm i < π.symm 0
    · exact ⟨1, by simp [plus, h]⟩
    · exact ⟨0, by simp [plus, h]⟩
  have F3 : ∀ i, y i 0 - y 0 0 = plus Z0 i - Z0 0 0 := by
    intro i
    obtain ⟨n, hn⟩ := h5c_mk_eq (congrFun hmk i)
    obtain ⟨n0, hn0⟩ := h5c_mk_eq (congrFun hmk 0)
    obtain ⟨m, hm⟩ := hint Z0 i
    obtain ⟨a, a'⟩ := h5c_offset h0 hy i
    obtain ⟨b, b'⟩ := F2 Z0 hZ0 i
    refine h5c_int_eq a a' b b' (n - n0 - m) ?_
    push_cast; linarith
  have F4 : ∀ i j, y i 0 < y j 0 ↔ plus Z0 i < plus Z0 j := by
    intro i j
    have h1 := F3 i; have h2 := F3 j
    constructor <;> intro h <;> linarith
  have hσ : σ = Tuple.sort (plus Zt) := by
    rw [h5c_sort_eq hy, h5c_sort_congr _ (plus Z0) F4, h5c_sort_congr _ _ F1]
  have hinjA : Function.Injective (plus Z0) := by
    intro i j h
    apply h5c_lift_inj hy
    have h1 := F3 i; have h2 := F3 j
    show y i 0 = y j 0
    rw [h] at h1; linarith
  have hinjB : Function.Injective (plus Zt) := by
    intro i j h
    apply hinjA
    refine le_antisymm (not_lt.1 fun hh => ?_) (not_lt.1 fun hh => ?_)
    · exact absurd h (ne_of_gt ((F1 _ _).1 hh))
    · exact absurd h (ne_of_lt ((F1 _ _).1 hh))
  have hmono : Monotone (plus Zt ∘ σ) := by rw [hσ]; exact Tuple.monotone_sort _
  refine ⟨fun i => (WithLp.toLp 2 fun _ => plus Zt i : Euc 1), ?_, ?_, ?_⟩
  · funext i l
    have : l = 0 := Subsingleton.elim _ _
    subst this
    obtain ⟨m, hm⟩ := hint Zt i
    exact h5c_coe_of_int hm
  · intro k k' hkk'
    show plus Zt (σ k) < plus Zt (σ k')
    exact lt_of_le_of_ne (hmono hkk'.le) (fun h => (ne_of_lt hkk') (σ.injective (hinjB h)))
  · intro k k'
    show plus Zt (σ k') < plus Zt (σ k) + 1
    have h1 := (F2 Zt hZt (σ k')).2
    have h2 : plus Zt 0 ≤ plus Zt (σ k) := by
      have := hmono (Fin.zero_le k)
      simpa [h0] using this
    rw [hplus0] at h2
    linarith

end Rotation

end HRS.MC.CepH5Pf
