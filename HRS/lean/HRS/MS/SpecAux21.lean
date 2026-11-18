import HRS.MS.SpecAux20

/-!
# S8P: growth of the eigenvalue sequence from a Rayleigh bound (S8.7, packet E6)

Namespace `HRS.MS.Spec`, helper prefix `s8p_`.  See `SpecAux20`.
-/

noncomputable section

open Filter Topology Module
open scoped RealInnerProductSpace

namespace HRS.MS.Spec

open HRS HRS.Whole

variable {d : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

theorem s8p_growth_count (b : HilbertBasis (MultiIndex d) ℝ H) (u : ℕ → H) (hu : LinearIndependent ℝ u)
    (l : ℕ) {Cr Ω : ℝ} (hCr : 0 < Cr) (hΩ : 0 ≤ Ω)
    (hray : ∀ v ∈ Submodule.span ℝ (Set.range fun i : Fin (l + 1) => u i),
      Summable (fun α => oscEigenvalue d α * ⟪b α, v⟫ ^ 2) ∧
        ∑' α, oscEigenvalue d α * ⟪b α, v⟫ ^ 2 ≤ Cr * (Ω + 1) * ‖v‖ ^ 2) :
    ((l : ℝ) + 1) ≤ (Cr * (Ω + 1) + 2) ^ d := by
  classical
  set M : ℝ := Cr * (Ω + 1) with hM
  have hM0 : 0 ≤ M := by positivity
  set W : Submodule ℝ H := Submodule.span ℝ (Set.range fun i : Fin (l + 1) => u i) with hW
  haveI : FiniteDimensional ℝ W := FiniteDimensional.span_of_finite ℝ (Set.finite_range _)
  have hli : LinearIndependent ℝ (fun i : Fin (l + 1) => u i) :=
    hu.comp _ Fin.val_injective
  have hrank : finrank ℝ W = l + 1 := by
    rw [hW, finrank_span_eq_card hli]; simp
  have hfin : {α : MultiIndex d | oscEigenvalue d α ≤ M + 1}.Finite := by
    refine (multiIndex_sublevel_finite d ⌊M + 1⌋₊).subset fun α hα => ?_
    simp only [Set.mem_setOf_eq] at hα ⊢
    have h1 : (α.degree : ℝ) ≤ M + 1 := by
      unfold oscEigenvalue at hα
      have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
      linarith
    exact Nat.le_floor h1
  have hdim := s8p_dim_count b (fun α => oscEigenvalue d α) hfin.toFinset W
    (M := M) (M' := M + 1) (by linarith) (fun k hk => by
      simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_le] at hk
      exact hk.le) hray
  rw [hrank] at hdim
  have hc := s8p_hermite_count d (Λ := M + 1) (by linarith)
  have h2 : (hfin.toFinset.card : ℝ) ≤ (M + 1 + 1) ^ d := by
    rw [Set.ncard_eq_toFinset_card _ hfin] at hc
    exact hc
  have h3 : ((l + 1 : ℕ) : ℝ) ≤ hfin.toFinset.card := by exact_mod_cast hdim
  push_cast at h3
  calc (l : ℝ) + 1 ≤ _ := h3
    _ ≤ (M + 1 + 1) ^ d := h2
    _ = (M + 2) ^ d := by ring_nf

theorem s8p_growth_lin (hd : 1 ≤ d) {Cr ω0 : ℝ} (hCr : 0 < Cr) (hω0 : 0 < ω0) :
    ∃ c : ℝ, 0 < c ∧ ∀ (l : ℕ) (ω : ℝ), ω0 ≤ ω → ((l : ℝ) + 1) ≤ (Cr * (ω + 1) + 2) ^ d →
      c * ((l : ℝ) + 1) ^ (1 / (d : ℝ)) ≤ ω := by
  set C3 : ℝ := Cr * (1 + 1 / ω0) + 2 / ω0 with hC3
  have hC3pos : 0 < C3 := by positivity
  refine ⟨1 / C3, by positivity, fun l ω hω h => ?_⟩
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have hbase : 0 ≤ (l : ℝ) + 1 := by positivity
  have hle : Cr * (ω + 1) + 2 ≤ C3 * ω := by
    have h1 : 1 ≤ ω / ω0 := by rw [le_div_iff₀ hω0]; linarith
    calc Cr * (ω + 1) + 2 = Cr * ω + Cr + 2 := by ring
      _ ≤ Cr * ω + Cr * (ω / ω0) + 2 * (ω / ω0) := by
          have : 0 ≤ Cr * (ω / ω0 - 1) := mul_nonneg hCr.le (by linarith)
          nlinarith [h1]
      _ = C3 * ω := by rw [hC3]; field_simp
  have hpow : (((l : ℝ) + 1) ^ (1 / (d : ℝ))) ≤ Cr * (ω + 1) + 2 := by
    calc ((l : ℝ) + 1) ^ (1 / (d : ℝ)) ≤ ((Cr * (ω + 1) + 2) ^ d) ^ (1 / (d : ℝ)) :=
          Real.rpow_le_rpow hbase h (le_of_lt (one_div_pos.2 hdpos))
      _ = Cr * (ω + 1) + 2 := by
          have hnn : (0 : ℝ) ≤ Cr * (ω + 1) + 2 := by
            have := mul_pos hCr (by linarith : 0 < ω + 1); linarith
          rw [← Real.rpow_natCast, ← Real.rpow_mul hnn, mul_one_div_cancel hdpos.ne',
            Real.rpow_one]
  calc 1 / C3 * ((l : ℝ) + 1) ^ (1 / (d : ℝ)) ≤ 1 / C3 * (C3 * ω) :=
        mul_le_mul_of_nonneg_left (hpow.trans hle) (by positivity)
    _ = ω := by field_simp

end HRS.MS.Spec
