import HRS.Sections.Q41Aux15

/-!
# Packet Q41, helper 16: the frozen semigroup acts linearly and boundedly on smooth functions

Linearity on finite sums, invariance under adding constants, and the sup bound
`|S(τ)h| ≤ M ‖h‖_{C^{m*+4}}` for the centered frozen semigroup.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace HRS.Q41

open HRS HRS.PDE HRS.PDE.MFAdjoint HRS.PDE.MFLinear HRS.PDE.MFPair

variable {d : ℕ}

section SemiProps

variable {s β c₀ Λ₀ : ℝ} {V ρβ : Torus d → ℝ}
  (H : FrozenHyp d s (2 * mStar d + 4) β⁻¹ β⁻¹ c₀ Λ₀ β V ρβ)

/-- Linearity of the frozen semigroup on finite sums of `C^{m*+4}` functions. -/
theorem q41_S_sum (hd : 1 ≤ d) {ι : Type*} (t : Finset ι) (c : ι → ℝ) (g : ι → Torus d → ℝ)
    (hg : ∀ i, Torus.IsCk ((mStar d + 4 : ℕ) : WithTop ℕ∞) (g i)) {τ : ℝ} (hτ : 0 ≤ τ) :
    Sg H τ (fun y => ∑ i ∈ t, c i * g i y) = fun y => ∑ i ∈ t, c i * Sg H τ (g i) y := by
  classical
  have hck : ∀ i, Torus.IsCk ((mStar d + 4 : ℕ) : WithTop ℕ∞) (fun y => c i * g i y) := fun i =>
    contDiff_const.mul (hg i)
  have h1 := S_sum_ps hd H (fun i y => c i * g i y) hck hτ t
  refine h1.trans ?_
  funext y
  refine Finset.sum_congr rfl fun i _ => ?_
  have := congrFun (S_smul_ps hd H (hg i) (c i) hτ) y
  exact this

/-- The frozen semigroup does not see additive constants. -/
theorem q41_S_add_const (hd : 1 ≤ d) {ψ : Torus d → ℝ}
    (hψ : Torus.IsCk ((mStar d + 4 : ℕ) : WithTop ℕ∞) ψ) (c : ℝ) {τ : ℝ} (hτ : 0 ≤ τ) :
    Sg H τ (fun y => ψ y + c) = Sg H τ ψ := by
  have hψ' : Torus.IsCk ((mStar d + 4 : ℕ) : WithTop ℕ∞) (fun y => ψ y + c) :=
    hψ.add contDiff_const
  obtain ⟨hc1, hm1⟩ := sob_of_isCk_ps hψ'
  obtain ⟨hc0, hm0⟩ := sob_of_isCk_ps hψ
  haveI : IsProbabilityMeasure (withDensityReal ρβ) := (KS_of_frozen hd H).isProb
  have e1 := equilibriumSemigroup_projMean hd s β⁻¹ β⁻¹ c₀ Λ₀ β V ρβ H _ hc1 hm1 τ hτ
  have e0 := equilibriumSemigroup_projMean hd s β⁻¹ β⁻¹ c₀ Λ₀ β V ρβ H _ hc0 hm0 τ hτ
  have hpm : projMean (withDensityReal ρβ) (fun y => ψ y + c) = projMean (withDensityReal ρβ) ψ := by
    funext x
    simp only [projMean]
    rw [q41_pair_add_const hc0]
    ring
  show equilibriumSemigroup _ _ _ _ = equilibriumSemigroup _ _ _ _
  rw [← e1, hpm, e0]

/-- Continuity and the sup bound for the frozen semigroup. -/
theorem q41_S_bound (hd : 1 ≤ d) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (h : Torus d → ℝ) (_ : Torus.IsCk ((mStar d + 4 : ℕ) : WithTop ℕ∞) h)
      (τ : ℝ), 0 ≤ τ → Continuous (Sg H τ h) ∧
        ∀ x, |Sg H τ h x| ≤ M * Torus.cbNorm (mStar d + 4) h := by
  have h3 := ClassicalPart.three_le_mStar d
  have hjL : (d : ℝ) / 2 + ((0 : ℕ) : ℝ) < ((mStar d + 4 : ℕ) : ℝ) := by
    have := mStar_gt d
    push_cast
    linarith
  obtain ⟨M, c, hM, hc, hbd⟩ := S_cb_bound hd s 0 (mStar d + 4) le_rfl hjL β⁻¹ β⁻¹ c₀ Λ₀
  refine ⟨M, hM.le, fun h hh τ hτ => ?_⟩
  have H' : FrozenHyp d s (mStar d + 4 + mStar d) β⁻¹ β⁻¹ c₀ Λ₀ β V ρβ := H.mono (by omega)
  obtain ⟨hck, hnorm⟩ := hbd β V ρβ H' h hh τ hτ
  refine ⟨Torus.continuous_of_continuous_lift hck.continuous, fun x => ?_⟩
  refine (abs_le_cb_ps hck x).trans ?_
  refine hnorm.trans ?_
  have hexp : Real.exp (-c * τ) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
  have h0 := cbNorm_nonneg_ps (d := d) (mStar d + 4) h
  calc M * Real.exp (-c * τ) * Torus.cbNorm (mStar d + 4) h ≤ M * 1 * Torus.cbNorm (mStar d + 4) h := by
        gcongr
    _ = M * Torus.cbNorm (mStar d + 4) h := by ring

end SemiProps

end HRS.Q41
