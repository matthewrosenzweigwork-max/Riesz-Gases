import Mathlib
import HRS.Main.A33Aux11

/-!
# Packet A33, helper 12: the transport propagator `U^{0,t}` on smooth test functions
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Finset
open scoped ENNReal NNReal BigOperators ComplexConjugate RealInnerProductSpace

namespace HRS.A33

open HRS HRS.PDE HRS.PDE.ET

variable {d : ℕ}

namespace A33Setup

variable (S : A33Setup d)

/-- `U^{0,t} ψ`. -/
abbrev U (t : ℝ) (ψ : Torus d → ℝ) : Torus d → ℝ := propagator S.D S.ρ 0 t ψ

theorem U_zero {ψ : Torus d → ℝ} (hψ : Torus.IsSmooth ψ) : S.U 0 ψ = ψ :=
  prop_self_zero S.hd S.D.s S.D.hs0 S.D.hsd S.J S.R S.MB S.Λ S.VB S.D S.ν₀ S.T S.ρ S.hA hψ

theorem U_cont {t : ℝ} (ht : t ∈ Set.Icc 0 S.T) {ψ : Torus d → ℝ} (hψ : Torus.IsSmooth ψ) :
    Continuous (S.U t ψ) := by
  rcases ht.1.eq_or_lt with h0 | h0
  · rw [← h0, S.U_zero hψ]; exact a33_cont hψ
  · exact (prop_facts S.hd S.D.s S.D.hs0 S.D.hsd S.J S.hJ S.R S.MB S.Λ S.VB S.D S.ν₀ S.T S.ρ S.hA
      ⟨h0, ht.2⟩ (dom_smooth hψ) (⟨le_rfl, h0.le⟩ : (0 : ℝ) ∈ Set.Icc 0 t)).2

theorem U_bound : ∃ K : ℝ, 0 ≤ K ∧ ∀ {t : ℝ}, t ∈ Set.Icc 0 S.T → ∀ {ψ : Torus d → ℝ},
    Torus.IsSmooth ψ → MemSobolev (S.J : ℝ) (S.U t ψ) ∧
      sobolevNorm (S.J : ℝ) (S.U t ψ) ≤ K * sobolevNorm (S.J : ℝ) ψ := by
  obtain ⟨K₁, K₂, hK₁, hK₂, hK⟩ := S.bounds
  refine ⟨max K₁ 1, le_trans zero_le_one (le_max_right _ _), fun {t} ht {ψ} hψ => ?_⟩
  rcases ht.1.eq_or_lt with h0 | h0
  · rw [← h0, S.U_zero hψ]
    refine ⟨a33_memSob _ hψ, ?_⟩
    calc sobolevNorm (S.J : ℝ) ψ = 1 * sobolevNorm (S.J : ℝ) ψ := (one_mul _).symm
      _ ≤ max K₁ 1 * sobolevNorm (S.J : ℝ) ψ :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.sqrt_nonneg _)
  · obtain ⟨hm, hb, -⟩ := hK t ⟨h0, ht.2⟩ ψ hψ 0 ⟨le_rfl, h0.le⟩
    exact ⟨hm, hb.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.sqrt_nonneg _))⟩

theorem U_lin {t : ℝ} (ht : t ∈ Set.Icc 0 S.T) {φ ψ : Torus d → ℝ} (hφ : Torus.IsSmooth φ)
    (hψ : Torus.IsSmooth ψ) (α β : ℝ) :
    S.U t (fun x => α * φ x + β * ψ x) = fun x => α * S.U t φ x + β * S.U t ψ x := by
  rcases ht.1.eq_or_lt with h0 | h0
  · have hs : Torus.IsSmooth (fun x => α * φ x + β * ψ x) := by
      unfold Torus.IsSmooth Torus.IsCk at *
      exact (contDiff_const.mul hφ).add (contDiff_const.mul hψ)
    rw [← h0, S.U_zero hs, S.U_zero hφ, S.U_zero hψ]
  · exact prop_lin S.hd S.D.s S.D.hs0 S.D.hsd S.J S.hJ S.R S.MB S.Λ S.VB S.D S.ν₀ S.T S.ρ S.hA
      ⟨h0, ht.2⟩ (dom_smooth hφ) (dom_smooth hψ) α β (⟨le_rfl, h0.le⟩ : (0 : ℝ) ∈ Set.Icc 0 t)

theorem U_const {t : ℝ} (ht : t ∈ Set.Icc 0 S.T) (c : ℝ) :
    S.U t (fun _ => c) = fun _ => c := by
  rcases ht.1.eq_or_lt with h0 | h0
  · rw [← h0, S.U_zero (a33_isSmooth_const c)]
  · exact prop_const S.hd S.D.s S.D.hs0 S.D.hsd S.J S.hJ S.R S.MB S.Λ S.VB S.D S.ν₀ S.T S.ρ S.hA
      ⟨h0, ht.2⟩ c (⟨le_rfl, h0.le⟩ : (0 : ℝ) ∈ Set.Icc 0 t)

/-- The functional `ψ ↦ F(U^{0,t}ψ)`. -/
def ell {m : ℝ} (t : ℝ) (F : NegSobolev d m) (ψ : Torus d → ℝ) : ℝ := NegSobolev.eval F (S.U t ψ)

theorem ell_lin {t : ℝ} (ht : t ∈ Set.Icc 0 S.T) (F : NegSobolev d (S.J : ℝ))
    {φ ψ : Torus d → ℝ} (hφ : Torus.IsSmooth φ) (hψ : Torus.IsSmooth ψ) (α β : ℝ) :
    S.ell t F (fun x => α * φ x + β * ψ x) = α * S.ell t F φ + β * S.ell t F ψ := by
  obtain ⟨K, -, hK⟩ := S.U_bound
  unfold ell
  rw [S.U_lin ht hφ hψ α β]
  exact a33_eval_lin F (S.U_cont ht hφ) (S.U_cont ht hψ) (a33_ws_of_memSobolev (hK ht hφ).1)
    (a33_ws_of_memSobolev (hK ht hψ).1) α β

theorem ell_const {t : ℝ} (ht : t ∈ Set.Icc 0 S.T) (F : NegSobolev d (S.J : ℝ)) (c : ℝ) :
    S.ell t F (fun _ => c) = 0 := by
  unfold ell
  rw [S.U_const ht c]
  exact a33_eval_const F c

theorem ell_trigPoly {t : ℝ} (ht : t ∈ Set.Icc 0 S.T) (F : NegSobolev d (S.J : ℝ))
    (s : Finset (NonzeroLattice d)) (c : NonzeroLattice d → ℝ) :
    S.ell t F (HRS.FieldSingAux.trigPoly s c) =
      ∑ k ∈ s, c k * S.ell t F (Torus.realMode k) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have : HRS.FieldSingAux.trigPoly (∅ : Finset (NonzeroLattice d)) c = fun _ => (0 : ℝ) := by
      funext x; simp [HRS.FieldSingAux.trigPoly]
    rw [this, S.ell_const ht F 0]; simp
  | insert a s ha ih =>
    have : HRS.FieldSingAux.trigPoly (insert a s) c = fun x =>
        1 * HRS.FieldSingAux.trigPoly s c x + c a * Torus.realMode a x := by
      funext x; simp [HRS.FieldSingAux.trigPoly, Finset.sum_insert ha]; ring
    rw [this, S.ell_lin ht F (HRS.FieldSingAux.isSmooth_trigPoly s c)
      (HRS.FieldSingAux.isSmooth_realMode a) 1 (c a), ih, Finset.sum_insert ha]
    ring

end A33Setup

end HRS.A33
