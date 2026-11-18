import HRS.MS.R2GenInitNL1
import HRS.MS.R2WinErrNL1
import HRS.MS.R2GenInitAux10

/-!
# S10.5, nonlinear branch, part 2: the second-moment bound along a resulting solution

`s105n_hmom`: for a resulting solution `ρ` (class constants `ε_*, c₁, C₁`), if the entropy bound `H(f^t|Q^t) ≤ C_ent(H_{N,0} + Nδ_N)` holds
(`s105n_hent`), then `E N⁻¹∑|x_i(t)|² ≤ C_m(1 + B_N/N)`.  Donsker--Varadhan against `(ρ^t)^{⊗N}` (`s105_second_moment_of_kl`) with the product-entropy
bound `s105_kl_product` (density, log-moment bounds of `s104n_hcls`) and the uniform Gaussian exponential moment `ρ^t ≤ C₁ρ_β`.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R2GenInit

open HRS.Whole HRS.Whole.AppendixA HRS.MS.R2WinErr

variable {d : ℕ}

set_option maxHeartbeats 1600000 in
theorem s105n_hmom (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {a β : ℝ} (ha : 0 < a) (hβ : 0 < β)
    (εstar c₁ C₁ Cent : ℝ) (hCent : 0 ≤ Cent) :
    ∃ Cm : ℝ, 0 ≤ Cm ∧ ∀ ρβ : Euc d → ℝ, IsThermalEquilibrium d s a β ρβ →
      ∀ (ε : ℝ) (ψ : Euc d → ℝ) (ρ : ℝ → Euc d → ℝ),
      IsAdmissiblePerturbation ρβ εstar ε ψ → IsResultingSolution d s a β ρβ εstar ε ψ c₁ C₁ ρ →
      ∀ N : ℕ, 2 ≤ N →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (X₀ : Ω → EucConfig d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → EucConfig d N),
      IsR2Realization d s a β P X₀ W X →
      HRS.relEntropy (HRS.law P X₀) (HRS.Whole.modulatedGibbs (HRS.Whole.rieszKernel d s) N β
        (HRS.Whole.withDensityReal (ρ 0))) < ⊤ →
      (∀ t : ℝ, 0 ≤ t → HRS.relEntropy (P.map (X t.toNNReal))
        (HRS.Whole.modulatedGibbs (HRS.Whole.rieszKernel d s) N β (HRS.Whole.withDensityReal (ρ t))) ≤
        ENNReal.ofReal (Cent * ((HRS.relEntropy (HRS.law P X₀)
          (HRS.Whole.modulatedGibbs (HRS.Whole.rieszKernel d s) N β
            (HRS.Whole.withDensityReal (ρ 0)))).toReal + N * deltaN d s N))) →
      ∀ t : ℝ, 0 ≤ t → ∫⁻ ζ, ENNReal.ofReal (movSecondMoment (X t.toNNReal ζ)) ∂P ≤
        ENNReal.ofReal (Cm * (1 + (1 + (HRS.relEntropy (HRS.law P X₀)
          (HRS.Whole.modulatedGibbs (HRS.Whole.rieszKernel d s) N β
            (HRS.Whole.withDensityReal (ρ 0)))).toReal + N * deltaN d s N) / N)) := by
  by_cases hex : ∃ ρ0 : Euc d → ℝ, IsThermalEquilibrium d s a β ρ0
  swap
  · exact ⟨0, le_rfl, fun ρβ h => absurd ⟨ρβ, h⟩ hex⟩
  obtain ⟨ρ0, hρ0⟩ := hex
  obtain ⟨Λ, hΛ⟩ := HRS.MS.S21.s21_thermal_bounded hd hs0 hsd ha hβ
  obtain ⟨hp0, hb0, hl0⟩ := hΛ ρ0 hρ0
  have hρeq : ρ0 = thermalDensity d s a β := HRS.MS.Mov0.mv0_rho_eq hd hs0 hsd ha hβ hρ0
  obtain ⟨C, c, BU, hT⟩ := S45.s45_thermal_data hd hs0 hsd ha hβ
  obtain ⟨M, L, Mom, C₀c, -, hcl⟩ := s104n_hcls hd hs0 hsd ha hβ εstar c₁ C₁
  obtain ⟨Ck, hCk0, hkl⟩ := s105_kl_product hd s hs0 hsd M L β hβ
  have hc2 : 0 < c / 2 := by have := hT.hc; positivity
  set Cr : ℝ := max C₁ 1 with hCr
  have hCr1 : 1 ≤ Cr := le_max_right _ _
  have hCr0 : 0 ≤ Cr := by linarith
  have hbd : ∀ x, ρ0 x ≤ C * Real.exp (-(c * ‖x‖ ^ 2)) := fun x => by
    rw [hρeq]
    have := (le_abs_self _).trans (hT.h0 x)
    simpa [neg_mul] using this
  set Z : ℝ := max 1 (Cr * (C * ∫ x : Euc d, Real.exp (-((c / 2) * ‖x‖ ^ 2)))) with hZ
  have hZ1 : 1 ≤ Z := le_max_left _ _
  set K : ℝ := Ck * (Cent + 1) with hK
  have hK0 : 0 ≤ K := by positivity
  refine ⟨(c / 2)⁻¹ * max K Z, by positivity, ?_⟩
  intro ρβ hρβ ε ψ ρ hadm hres N hN Ω _ P _ X₀ W X hreal hfin hentb t ht
  have hρβeq : ρβ = ρ0 := by
    rw [HRS.MS.Mov0.mv0_rho_eq hd hs0 hsd ha hβ hρβ, hρeq]
  subst hρβeq
  have htraj : IsR2WindowTrajectory d s a β ρβ εstar c₁ C₁ ρ := Or.inr ⟨ε, ψ, hadm, hres⟩
  obtain ⟨hρt, hρM, -, -, hρlog⟩ := (hcl ρβ hρβ ρ htraj).1 t ht
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hδ : 0 ≤ deltaN d s N := HRS.MS.S53.s53_deltaN_nonneg s (by omega)
  have hNδ : 0 ≤ (N : ℝ) * deltaN d s N := mul_nonneg hN0.le hδ
  have hXm : Measurable (X t.toNNReal) := (hreal.solution t).adapted _
  haveI : IsProbabilityMeasure (P.map (X t.toNNReal)) :=
    ⟨by rw [Measure.map_apply hXm MeasurableSet.univ]; simp⟩
  haveI : IsProbabilityMeasure (HRS.Whole.withDensityReal (ρ t)) := Q34.isProbabilityMeasure_nu hρt
  -- Gaussian exponential moment of ρ^t
  have hbdt : ∀ x, ρ t x ≤ (Cr * C) * Real.exp (-(c * ‖x‖ ^ 2)) := fun x => by
    have h1 := (hres.ratio t ht x).2
    have h2 : ρβ x ≤ C * Real.exp (-(c * ‖x‖ ^ 2)) := hbd x
    calc ρ t x ≤ C₁ * ρβ x := h1
      _ ≤ Cr * ρβ x := mul_le_mul_of_nonneg_right (le_max_left _ _) (hp0.nonneg x)
      _ ≤ Cr * (C * Real.exp (-(c * ‖x‖ ^ 2))) := mul_le_mul_of_nonneg_left h2 hCr0
      _ = _ := by ring
  have hexp := s105_exp_moment_gauss hρt (mul_nonneg hCr0 hT.C0) hT.hc hbdt
  have hexpZ : ∫⁻ x, ENNReal.ofReal (Real.exp ((c / 2) * ‖x‖ ^ 2)) ∂(HRS.Whole.withDensityReal (ρ t)) ≤
      ENNReal.ofReal Z := by
    refine hexp.trans (ENNReal.ofReal_le_ofReal (le_of_eq ?_))
    rw [hZ, mul_assoc]
  set h0 : ℝ := (HRS.relEntropy (HRS.law P X₀) (HRS.Whole.modulatedGibbs (HRS.Whole.rieszKernel d s) N β
    (HRS.Whole.withDensityReal (ρ 0)))).toReal with hh0
  have hh00 : 0 ≤ h0 := ENNReal.toReal_nonneg
  have hent := hentb t ht
  obtain ⟨hπne, hπ⟩ := hkl (ρ t) hρt hρM hρlog N hN (P.map (X t.toNNReal)) inferInstance
    (Cent * (h0 + N * deltaN d s N)) (by positivity) hent
  have hsm := s105_second_moment_of_kl (μ := HRS.Whole.withDensityReal (ρ t)) (by omega : 0 < N) hc2 hZ1 hexpZ P
    (X t.toNNReal) hXm hπne
  refine hsm.trans (ENNReal.ofReal_le_ofReal ?_)
  set q : ℝ := (1 + h0 + N * deltaN d s N) / N with hq
  have hq0 : 0 ≤ q := by positivity
  have hkq : (InformationTheory.klDiv (P.map (X t.toNNReal))
      (Measure.pi fun _ : Fin N => HRS.Whole.withDensityReal (ρ t))).toReal / N ≤ K * q := by
    rw [div_le_iff₀ hN0, hq]
    have : K * ((1 + h0 + N * deltaN d s N) / N) * N = K * (1 + h0 + N * deltaN d s N) := by field_simp
    rw [this, hK]
    have h1 : Cent * (h0 + N * deltaN d s N) + N * deltaN d s N ≤ (Cent + 1) * (1 + h0 + N * deltaN d s N) := by
      nlinarith [mul_nonneg hCent hh00, mul_nonneg hCent hNδ]
    calc _ ≤ Ck * (Cent * (h0 + N * deltaN d s N) + N * deltaN d s N) := hπ
      _ ≤ Ck * ((Cent + 1) * (1 + h0 + N * deltaN d s N)) := mul_le_mul_of_nonneg_left h1 hCk0
      _ = _ := by ring
  have hmz : Z ≤ max K Z := le_max_right _ _
  have hmx : K ≤ max K Z := le_max_left _ _
  have hm0 : 0 ≤ max K Z := hK0.trans hmx
  have : K * q + Z ≤ max K Z * (1 + q) := by nlinarith
  have hpos : 0 ≤ (c / 2)⁻¹ := by positivity
  calc (c / 2)⁻¹ * ((InformationTheory.klDiv (P.map (X t.toNNReal))
        (Measure.pi fun _ : Fin N => HRS.Whole.withDensityReal (ρ t))).toReal / N + Z)
      ≤ (c / 2)⁻¹ * (K * q + Z) := mul_le_mul_of_nonneg_left (by linarith) hpos
    _ ≤ (c / 2)⁻¹ * (max K Z * (1 + q)) := mul_le_mul_of_nonneg_left this hpos
    _ = (c / 2)⁻¹ * max K Z * (1 + q) := by ring

end HRS.MS.R2GenInit
