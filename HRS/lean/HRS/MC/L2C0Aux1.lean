import HRS.MC.RegSet
import HRS.PDE.WellPosed
import HRS.PDE.MeanFieldSemigroup
import HRS.PDE.MeanFieldLinearLoss

/-!
# Packet L2C-0, part 1: smoothness of the adjoint propagator from the hypotheses of Proposition 3.9

For dynamics `D` and a density path `μ`, if the hypotheses of Proposition 3.9 (`AdjointData`) hold at every
Sobolev level `m ≥ 1` on every horizon `[0,T]`, then for smooth `φ` the propagator `U^{r,t}φ` is smooth.
Route: `ClassicalPart.propagator_eq_toFun` (the propagator is `toFun` of the level-`m` forward solution, which lies in
`H^m`) and the Sobolev embedding `toFun_isCk_le` at every level.
-/

noncomputable section

open MeasureTheory Filter Topology
open HRS HRS.PDE

namespace HRS.MC.L2C0

variable {d : ℕ}

/-- The propagator at `r = t = 0` is smooth for smooth `φ` (it is `φ` or the junk value `0`). -/
theorem l2c0_smooth_zero (D : DynData d) (μ : ℝ → Torus d → ℝ) (φ : Torus d → ℝ)
    (hφ : Torus.IsSmooth φ) : Torus.IsSmooth (propagator D μ 0 0 φ) := by
  unfold propagator
  split_ifs with h
  · have := h.choose_spec.terminal
    rw [this]
    exact hφ
  · have h0 : Torus.lift (0 : Torus d → ℝ) = fun _ => 0 := rfl
    unfold Torus.IsSmooth Torus.IsCk
    rw [h0]
    exact contDiff_const

/-- The level-`n` smoothness of the propagator, from `AdjointData` at a large level. -/
theorem l2c0_isCk_of_adjointData (hd : 1 ≤ d) (D : DynData d) (μ : ℝ → Torus d → ℝ)
    (φ : Torus d → ℝ) (hφ : Torus.IsSmooth φ) (n : ℕ) (r t : ℝ) (hr : 0 ≤ r) (hrt : r ≤ t)
    (ht : 0 < t)
    (hA : ∀ m : ℕ, 1 ≤ m → ∃ (R : PDE.Regime) (MB Λ VB ν₀ : ℝ),
      AdjointData D.s m R MB Λ VB D ν₀ t μ) :
    Torus.IsCk n (propagator D μ r t φ) := by
  set m : ℕ := mStar d + n with hm
  have hmS : mStar d ≤ m := Nat.le_add_right _ _
  have hm3 := ClassicalPart.one_le_of_mStar hmS
  have hm1 : 1 ≤ m := by omega
  obtain ⟨R, MB, Λ, VB, ν₀, hAD⟩ := hA m hm1
  have hφc : Continuous φ := MFLinear.continuous_of_isSmooth hφ
  have hφS : MemSobolev (m : ℝ) φ := MFSemigroup.memSobolev_of_isSmooth hφ _
  have hpe := ClassicalPart.propagator_eq_toFun hd D.s D.hs0 D.hsd m hmS R MB Λ VB D ν₀ t μ hAD
    t ⟨ht, le_rfl⟩ φ hφc hφS r ⟨hr, hrt⟩
  have hmd : (d : ℝ) / 2 < m := by
    obtain ⟨m'', h1, h2⟩ := ClassicalPart.exists_mid (d := d) hmS
    have : (0 : ℝ) ≤ (d : ℝ) / 2 := by positivity
    linarith
  obtain ⟨hcm, -⟩ := hsNormSq_coeffOf (m : ℝ) φ hφS
  have hre : IsRealCoeff (coeffOf φ) :=
    isRealCoeff_coeffOf φ (ClassicalAux.integrable_of_continuous hφc)
  have hreal := ClassicalPart.propagatorCoeff_real hd D.s D.hs0 D.hsd m hm1 R MB Λ VB D ν₀ t μ
    hAD t ⟨ht, le_rfl⟩ (coeffOf φ) hcm hre
  obtain ⟨C, hC, hspec⟩ := propagatorCoeff_spec hd D.s D.hs0 D.hsd m hm1 R MB Λ VB
  obtain ⟨-, hw, -⟩ := hspec D ν₀ t μ hAD t ⟨ht, le_rfl⟩ (coeffOf φ) hcm
  have hτ := ClassicalAux.mem_Icc_sub t (show r ∈ Set.Icc (0 : ℝ) t from ⟨hr, hrt⟩)
  have hnm : (d : ℝ) / 2 + n < m := by
    have h3 : (d : ℝ) / 2 < mStar d := by
      unfold mStar; push_cast
      have := Nat.lt_floor_add_one ((d : ℝ) / 2)
      linarith
    rw [hm]; push_cast; linarith
  obtain ⟨C2, hC2⟩ := toFun_isCk_le (d := d) n (m : ℝ) hnm
  rw [hpe]
  exact (hC2 _ (hw.1 _ hτ) (hreal _ hτ)).1

/-- Smoothness of the propagator from `AdjointData` at every level on the horizon `[0,t]`. -/
theorem l2c0_smooth_of_adjointData (hd : 1 ≤ d) (D : DynData d) (μ : ℝ → Torus d → ℝ)
    (hA : ∀ m : ℕ, 1 ≤ m → ∀ T : ℝ, 0 < T → ∃ (R : PDE.Regime) (MB Λ VB ν₀ : ℝ),
      AdjointData D.s m R MB Λ VB D ν₀ T μ)
    (φ : Torus d → ℝ) (hφ : Torus.IsSmooth φ) (r t : ℝ) (hr : 0 ≤ r) (hrt : r ≤ t) :
    Torus.IsSmooth (propagator D μ r t φ) := by
  rcases (hr.trans hrt).eq_or_lt with h0 | ht
  · have hr0 : r = 0 := le_antisymm (h0 ▸ hrt) hr
    subst h0
    rw [hr0]
    exact l2c0_smooth_zero D μ φ hφ
  · have : ∀ n : ℕ, ContDiff ℝ n (Torus.lift (propagator D μ r t φ)) := fun n =>
      l2c0_isCk_of_adjointData hd D μ φ hφ n r t hr hrt ht (fun m hm => hA m hm t ht)
    exact contDiff_infty.2 this

end HRS.MC.L2C0

end
