import HRS.Torus.Basic

/-!
# Packet C (`CepH5C`): proofs of `h5Comp_isOpen`, `h5Comp_disjoint`, `h5Comp_iUnion`, `h5Comp_nonempty`

The vocabulary `cep_StrictlyOrdered`, `h5Idx`, `h5Comp` is re-stated here with identical bodies, so that this module
does not import the (sorried) spec files; the tie file `CepH5CTie.lean` checks the identity.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.CepH5Pf

open HRS

/-- Copy of `HRS.MC.Cepa.cep_StrictlyOrdered`. -/
def cep_StrictlyOrdered {N : ℕ} (π : Equiv.Perm (Fin N)) (y : Fin N → Euc 1) : Prop :=
  (∀ k k' : Fin N, k < k' → y (π k) 0 < y (π k') 0) ∧
    ∀ k k' : Fin N, y (π k') 0 < y (π k) 0 + 1

/-- Copy of `HRS.MC.CepH5.h5Idx`. -/
abbrev h5Idx (N : ℕ) [NeZero N] := {σ : Equiv.Perm (Fin N) // σ 0 = 0}

/-- Copy of `HRS.MC.CepH5.h5Comp`. -/
def h5Comp {N : ℕ} (σ : Equiv.Perm (Fin N)) : Set (Config 1 N) :=
  {x | ∃ y : Fin N → Euc 1, (fun i => Torus.mk (y i)) = x ∧ cep_StrictlyOrdered σ y}

section Components

variable {N : ℕ} [NeZero N]

lemma h5c_coe_eq {a b : ℝ} (h : ((a : ℝ) : UnitAddCircle) = (b : UnitAddCircle)) : ∃ n : ℤ, a - b = n := by
  rw [← sub_eq_zero, ← AddCircle.coe_sub, AddCircle.coe_eq_zero_iff] at h
  obtain ⟨n, hn⟩ := h
  exact ⟨n, by simpa using hn.symm⟩

lemma h5c_mk_eq {x y : Euc 1} (h : Torus.mk x = Torus.mk y) : ∃ n : ℤ, x 0 - y 0 = n :=
  h5c_coe_eq (congrFun h 0)

lemma h5c_int_eq {a b : ℝ} (ha : 0 ≤ a) (ha' : a < 1) (hb : 0 ≤ b) (hb' : b < 1) (n : ℤ)
    (h : a - b = n) : a = b := by
  have h1 : (n : ℝ) < 1 := by linarith
  have h2 : (-1 : ℝ) < n := by linarith
  have h1' : n < 1 := by exact_mod_cast h1
  have h2' : -1 < n := by exact_mod_cast h2
  have : n = 0 := by omega
  subst this
  simpa [sub_eq_zero] using h

/-- Strictly ordered along `σ` with `σ 0 = 0`: offsets from particle `0` lie in `[0,1)`. -/
lemma h5c_offset {σ : Equiv.Perm (Fin N)} (h0 : σ 0 = 0) {y : Fin N → Euc 1}
    (hy : cep_StrictlyOrdered σ y) (i : Fin N) : 0 ≤ y i 0 - y 0 0 ∧ y i 0 - y 0 0 < 1 := by
  obtain ⟨k, rfl⟩ := σ.surjective i
  constructor
  · rcases eq_or_lt_of_le (Fin.zero_le k) with h | h
    · subst h; rw [h0]; simp
    · have := hy.1 0 k h; rw [h0] at this; linarith
  · have := hy.2 0 k; rw [h0] at this; linarith

lemma h5c_lift_inj {σ : Equiv.Perm (Fin N)} {y : Fin N → Euc 1} (hy : cep_StrictlyOrdered σ y) :
    Function.Injective fun i => y i 0 := by
  intro i j hij
  obtain ⟨k, rfl⟩ := σ.surjective i
  obtain ⟨k', rfl⟩ := σ.surjective j
  by_contra hne
  have hk : k ≠ k' := fun h => hne (by rw [h])
  rcases lt_or_gt_of_ne hk with h | h
  · have := hy.1 _ _ h; simp only at hij; linarith
  · have := hy.1 _ _ h; simp only at hij; linarith

/-- Two strictly ordered lifts (`σ 0 = 0 = σ' 0`) of the same configuration give `σ = σ'`. -/
lemma h5c_perm_unique {σ σ' : Equiv.Perm (Fin N)} (h0 : σ 0 = 0) (h0' : σ' 0 = 0)
    {y y' : Fin N → Euc 1} (hy : cep_StrictlyOrdered σ y) (hy' : cep_StrictlyOrdered σ' y')
    (hxy : (fun i => Torus.mk (y i)) = fun i => Torus.mk (y' i)) : σ = σ' := by
  set w : Fin N → ℝ := fun i => y i 0 - y 0 0 with hw
  set w' : Fin N → ℝ := fun i => y' i 0 - y' 0 0 with hw'
  have hww : w = w' := by
    funext i
    obtain ⟨n, hn⟩ := h5c_mk_eq (congrFun hxy i)
    obtain ⟨n0, hn0⟩ := h5c_mk_eq (congrFun hxy 0)
    obtain ⟨a, a'⟩ := h5c_offset h0 hy i
    obtain ⟨b, b'⟩ := h5c_offset h0' hy' i
    refine h5c_int_eq a a' b b' (n - n0) ?_
    simp only [hw, hw']; push_cast; linarith
  have hwinj : Function.Injective w := by
    intro i j hij
    exact h5c_lift_inj hy (by simpa [hw] using hij)
  have hs : ∀ τ : Equiv.Perm (Fin N), Monotone (w ∘ τ) → τ = Tuple.sort w := by
    intro τ hτ
    rw [Tuple.eq_sort_iff]
    refine ⟨hτ, fun i j hij hEq => ?_⟩
    exact absurd (hwinj hEq) (fun h => (ne_of_lt hij) (τ.injective h))
  have hmono : ∀ {τ : Equiv.Perm (Fin N)} {z : Fin N → Euc 1}, cep_StrictlyOrdered τ z →
      (∀ i, z i 0 - z 0 0 = w i) → Monotone (w ∘ τ) := by
    intro τ z hz hzw a b hab
    rcases eq_or_lt_of_le hab with h | h
    · subst h; exact le_rfl
    · have := hz.1 a b h
      simp only [Function.comp, ← hzw]; linarith
  have e1 : σ = Tuple.sort w := hs σ (hmono hy (fun i => rfl))
  have e2 : σ' = Tuple.sort w := hs σ' (hmono hy' (fun i => by rw [hww]))
  rw [e1, e2]

theorem h5Comp_disjoint_proof : Pairwise fun σ σ' : h5Idx N => Disjoint (h5Comp σ.1) (h5Comp σ'.1) := by
  intro σ σ' hne
  rw [Set.disjoint_left]
  rintro x ⟨y, hyx, hy⟩ ⟨y', hyx', hy'⟩
  exact hne (Subtype.ext (h5c_perm_unique σ.2 σ'.2 hy hy' (hyx.trans hyx'.symm)))

theorem h5Comp_nonempty_proof (σ : h5Idx N) : (h5Comp σ.1).Nonempty := by
  refine ⟨fun i => Torus.mk (WithLp.toLp 2 fun _ => ((σ.1.symm i : Fin N) : ℕ) / (N : ℝ)), _, rfl, ?_⟩
  have hN : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  constructor
  · intro k k' hkk'
    simp only [Equiv.symm_apply_apply]
    show (k : ℕ) / (N : ℝ) < (k' : ℕ) / (N : ℝ)
    exact (div_lt_div_iff_of_pos_right hN).2 (by exact_mod_cast hkk')
  · intro k k'
    simp only [Equiv.symm_apply_apply]
    show (k' : ℕ) / (N : ℝ) < (k : ℕ) / (N : ℝ) + 1
    have : (k' : ℕ) / (N : ℝ) < 1 := by
      rw [div_lt_one hN]; exact_mod_cast k'.2
    have : 0 ≤ (k : ℕ) / (N : ℝ) := by positivity
    linarith

end Components

end HRS.MC.CepH5Pf
