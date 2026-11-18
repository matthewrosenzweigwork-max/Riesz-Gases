import HRS.PDE.MeanFieldOneLe
import HRS.PDE.MeanFieldLinearResponse
import HRS.PDE.MeanFieldLinearLoss
import HRS.PDE.MeanFieldAdjointSmoothing
import HRS.PDE.MeanFieldPairSeries
import HRS.Sections.Q41Aux14

/-!
# EQ-GAUSS (a), deterministic part: the Lyapunov identity

For the frozen coefficient `ρ_β` (smooth, positive thermal density) and smooth tests `φ, ψ`, `0 ≤ a ≤ b`:

`𝒞_β(U^{0,a}φ, U^{0,b}ψ) + 2β⁻¹ ∫_0^a ∫ ∇U^{r,a}φ·∇U^{r,b}ψ ρ_β dr = 𝒞_β(φ, S_β(b-a)ψ)`.

Route: time homogeneity of the frozen propagator (`U^{r,t} = U^{0,t-r}`), the integral formula
`susceptibilityCov_eq_integral` applied twice (to `(φ, S_δψ)` and `(S_aφ, S_bψ)`), the semigroup property of
`S_β`, and a translation/reflection of the `v`-integral.  Everything is exact (no limit).
-/

noncomputable section

open MeasureTheory Filter Topology
open HRS HRS.PDE

namespace HRS.MD.EQGaussLyapDet

variable {d : ℕ}

/-! ### Smoothness of the frozen propagator (copy of `HRS.MC.L2C0.l2c0_smooth_of_adjointData`) -/

theorem eqgld_zero_smooth (D : DynData d) (μ : ℝ → Torus d → ℝ) (φ : Torus d → ℝ)
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

theorem eqgld_isCk_of_adjointData (hd : 1 ≤ d) (D : DynData d) (μ : ℝ → Torus d → ℝ)
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

theorem eqgld_smooth_of_adjointData (hd : 1 ≤ d) (D : DynData d) (μ : ℝ → Torus d → ℝ)
    (hA : ∀ m : ℕ, 1 ≤ m → ∀ T : ℝ, 0 < T → ∃ (R : PDE.Regime) (MB Λ VB ν₀ : ℝ),
      AdjointData D.s m R MB Λ VB D ν₀ T μ)
    (φ : Torus d → ℝ) (hφ : Torus.IsSmooth φ) (r t : ℝ) (hr : 0 ≤ r) (hrt : r ≤ t) :
    Torus.IsSmooth (propagator D μ r t φ) := by
  rcases (hr.trans hrt).eq_or_lt with h0 | ht
  · have hr0 : r = 0 := le_antisymm (h0 ▸ hrt) hr
    subst h0
    rw [hr0]
    exact eqgld_zero_smooth D μ φ hφ
  · have : ∀ n : ℕ, ContDiff ℝ n (Torus.lift (propagator D μ r t φ)) := fun n =>
      eqgld_isCk_of_adjointData hd D μ φ hφ n r t hr hrt ht (fun m hm => hA m hm t ht)
    exact contDiff_infty.2 this

/-! ### The frozen data -/

/-- Smoothness and positivity of the thermal density, and the frozen hypothesis bundle. -/
theorem eqgld_frozen (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (V : Torus d → ℝ)
    (hV : Torus.IsSmooth V) {β : ℝ} (hβ : 0 < β) (ρβ : Torus d → ℝ)
    (hρβ : IsThermalDensity (periodicRiesz d s) V β ρβ) :
    (∀ x, 0 < ρβ x) ∧ Torus.IsSmooth ρβ ∧ ∃ c₀ Λ₀ : ℝ,
      Nonempty (MFAdjoint.FrozenHyp d s (2 * mStar d + 4) β⁻¹ β⁻¹ c₀ Λ₀ β V ρβ) := by
  obtain ⟨hpos, hsm⟩ := HRS.Q41.q41_thermal_regular hd hs0 hsd hβ hV hρβ
  obtain ⟨c₀, Λ₀, H⟩ := MFPair.frozenHyp_of_smooth s hs0 hsd β hβ V hV ρβ hρβ hsm hpos
    (2 * mStar d + 4)
  exact ⟨hpos, hsm, c₀, Λ₀, ⟨H⟩⟩

/-- The frozen propagator is smooth for smooth data. -/
theorem eqgld_prop_smooth (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (V : Torus d → ℝ)
    (hV : Torus.IsSmooth V) {β : ℝ} (hβ : 0 < β) (ρβ : Torus d → ℝ) (hprob : IsProbDensity ρβ)
    (hρC : Torus.IsSmooth ρβ) (hpos : ∀ x, 0 < ρβ x) (φ : Torus d → ℝ) (hφ : Torus.IsSmooth φ)
    (r t : ℝ) (hr : 0 ≤ r) (hrt : r ≤ t) :
    Torus.IsSmooth (propagator (mfData d s hs0 hsd V β hβ) (fun _ => ρβ) r t φ) := by
  refine eqgld_smooth_of_adjointData hd _ _ (fun m hm T hT => ?_) φ hφ r t hr hrt
  obtain ⟨R, MB, Λ, VB, h⟩ :=
    MFSemigroup.adjointData_frozen s hs0 hsd β hβ V hV ρβ hprob hρC hpos m
  exact ⟨R, MB, Λ, VB, 0, h 0 T hT⟩

/-- Time homogeneity of the frozen propagator. -/
theorem eqgld_homog (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (V : Torus d → ℝ)
    (hV : Torus.IsSmooth V) {β : ℝ} (hβ : 0 < β) (ρβ : Torus d → ℝ) (hprob : IsProbDensity ρβ)
    (hρC : Torus.IsSmooth ρβ) (hpos : ∀ x, 0 < ρβ x) (ψ : Torus d → ℝ) (hψ : Torus.IsSmooth ψ)
    {r t : ℝ} (hr : 0 ≤ r) (hrt : r < t) :
    propagator (mfData d s hs0 hsd V β hβ) (fun _ => ρβ) r t ψ =
      propagator (mfData d s hs0 hsd V β hβ) (fun _ => ρβ) 0 (t - r) ψ := by
  have ht : 0 < t := lt_of_le_of_lt hr hrt
  obtain ⟨R, MB, Λ, VB, hA, F, hF⟩ :=
    MFOneLe.frozen_classical_of_one_le hd s hs0 hsd β hβ V hV ρβ hprob hρC hpos ψ hψ t ht
  have hm : 1 ≤ mStar d := by have := ClassicalPart.three_le_mStar d; omega
  have h1 := MFOneLe.propagator_frozen_eq_of_one_le hd s hs0 hsd (mStar d) hm R MB Λ VB
    (mfData d s hs0 hsd V β hβ) 0 t ρβ hA (T' := t) ⟨ht, le_rfl⟩ hF (τ := t - r)
    ⟨by linarith, by linarith⟩
  have hex : ∃ f, IsClassicalAdjointSolution (mfData d s hs0 hsd V β hβ) (fun _ => ρβ) t ψ f :=
    ⟨F, hF⟩
  have h2 : propagator (mfData d s hs0 hsd V β hβ) (fun _ => ρβ) r t ψ = F r := by
    simp only [propagator, hex, dite_true]
    exact classical_adjoint_unique hd s hs0 hsd (mStar d) hm R MB Λ VB (mfData d s hs0 hsd V β hβ)
      0 t _ hA t ⟨ht, le_rfl⟩ ψ _ _ hex.choose_spec hF r ⟨hr, hrt.le⟩
  rw [h2, h1]
  congr 1
  ring

end HRS.MD.EQGaussLyapDet

end
