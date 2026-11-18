import HRS.MS.MovEntAux3

/-!
# S6.6, packet P3 (part 3): the particle bounds at one time from the entropy bound

`s66_bounds_at`: for a density `ρ` of the S3.1 class with exponential moment `E` at rate `c₁`, `N ≥ 2` and a probability law `f`
with `H(f|Q_{N,β}(ρ)) ≤ ofReal(C₁ N δ_N)`: the bounds `H(f|Q) ≤ C N δ`, `E_f|F_N| ≤ C δ`, `H(f|ρ^{⊗N}) ≤ C N δ`,
`E_f (F_N + o_N) ≤ C o_N` (any `C₀ ≥ 1`), `E_f N⁻¹∑|x_i|² ≤ C`, with `C` independent of `ρ, N, f, C₀`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory InformationTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.MovEnt

open HRS.Whole

local notation "wd" => Whole.withDensityReal

variable {d N : ℕ}

set_option maxHeartbeats 1000000 in
theorem s66_bounds_at (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (M L E c₁ β C₁ : ℝ)
    (hβ : 0 < β) (hc₁ : 0 < c₁) (hC₁ : 0 ≤ C₁) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ρ : Euc d → ℝ, Whole.IsProbDensity ρ → (∀ x, ρ x ≤ M) →
      (s = 0 → HasLogMoment (wd ρ) L) →
      ∫⁻ x, ENNReal.ofReal (Real.exp (c₁ * ‖x‖ ^ 2)) ∂(wd ρ) ≤ ENNReal.ofReal E →
      ∀ N : ℕ, 2 ≤ N → ∀ f : Measure (EucConfig d N), IsProbabilityMeasure f →
      relEntropy f (Whole.modulatedGibbs (rieszKernel d s) N β (wd ρ)) ≤
        ENNReal.ofReal (C₁ * N * deltaN d s N) →
      relEntropy f (Whole.modulatedGibbs (rieszKernel d s) N β (wd ρ)) ≤ ENNReal.ofReal (C * N * deltaN d s N) ∧
      ∫⁻ Z, ENNReal.ofReal |rieszModulatedEnergy d s Z (wd ρ)| ∂f ≤ ENNReal.ofReal (C * deltaN d s N) ∧
      relEntropy f (Measure.pi fun _ : Fin N => wd ρ) ≤ ENNReal.ofReal (C * N * deltaN d s N) ∧
      (∀ C₀ : ℝ, 1 ≤ C₀ →
        ∫⁻ Z, ENNReal.ofReal (rieszModulatedEnergy d s Z (wd ρ) + oN d s C₀ N) ∂f ≤
          ENNReal.ofReal (C * oN d s C₀ N)) ∧
      ∫⁻ Z, ENNReal.ofReal (movSecondMoment Z) ∂f ≤ ENNReal.ofReal C := by
  have hd1 : 1 ≤ d := by omega
  obtain ⟨Cp, hCp⟩ := s66_gibbs_data hd hs0 hsd M L (β / 2) (2 * β) (by positivity) (by linarith)
  obtain ⟨c, hc, C2, hent⟩ := HRS.MS.Wr.euclidean_pair_entropy_self_proof hd hs0 hsd M L (β / 2) (2 * β)
    (by positivity) (by linarith)
  set Cp' : ℝ := max Cp 0 with hCp'
  set C2' : ℝ := max C2 0 with hC2'
  have hCp'0 : 0 ≤ Cp' := le_max_right _ _
  have hC2'0 : 0 ≤ C2' := le_max_right _ _
  set A : ℝ := C₁ with hA
  set CF : ℝ := C2' * (A + 1) with hCF
  have hCF0 : 0 ≤ CF := by positivity
  set C3 : ℝ := A + β * CF + Cp' with hC3
  have hC30 : 0 ≤ C3 := by positivity
  set Ce : ℝ := 2 * CF + 1 with hCe
  set E' : ℝ := max E 1 with hE'
  have hlogE : 0 ≤ Real.log E' := Real.log_nonneg (le_max_right _ _)
  set Cm : ℝ := c₁⁻¹ * (C3 + Real.log E') with hCm
  have hCm0 : 0 ≤ Cm := by positivity
  set C : ℝ := A + CF + C3 + Ce + Cm with hC
  have hC0 : 0 ≤ C := by positivity
  refine ⟨C, hC0, ?_⟩
  intro ρ hρ hM hL hE N hN f hf hH
  haveI := hf
  haveI : IsProbabilityMeasure (wd ρ) := HRS.MS.Thm.cb_withDensityReal_isProb hρ
  have hmem : β ∈ Set.Icc (β / 2) (2 * β) := ⟨by linarith, by linarith⟩
  obtain ⟨hW, hlogK⟩ := hCp ρ hρ hM hL N hN β hmem
  obtain ⟨hδ0, hδ1, ho0, hδo⟩ := s66_delta_facts hd1 hs0 hsd (C₀ := 1) le_rfl hN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hNδ : 0 ≤ (N : ℝ) * deltaN d s N := by positivity
  have hHne : relEntropy f (Whole.modulatedGibbs (rieszKernel d s) N β (wd ρ)) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hH
  obtain ⟨hiff, hid⟩ := s66_split hd hs0 hsd M L β hβ hρ hM hL hN f
  have hfin := hiff.1 hHne
  have hid' := hid hfin
  have hHr : (relEntropy f (Whole.modulatedGibbs (rieszKernel d s) N β (wd ρ))).toReal ≤
      A * N * deltaN d s N :=
    ENNReal.toReal_le_of_le_ofReal (by positivity) hH
  have hHlt : relEntropy f (Whole.modulatedGibbs (rieszKernel d s) N β (wd ρ)) < ⊤ := lt_top_iff_ne_top.2 hHne
  obtain ⟨hi, hint⟩ := (hent ρ hρ hM hL N hN β hmem).2 f hf hHlt
  have hne : (N : ℝ) ≠ 0 := hN0.ne'
  have habsInt : Integrable (fun Z : EucConfig d N => |rieszModulatedEnergy d s Z (wd ρ)|) f :=
    (integrable_const_mul_iff (isUnit_iff_ne_zero.2 hne) _).1 hi
  have hFint : ∫ Z, |rieszModulatedEnergy d s Z (wd ρ)| ∂f ≤ CF * deltaN d s N := by
    have h1 : (N : ℝ) * ∫ Z, |rieszModulatedEnergy d s Z (wd ρ)| ∂f ≤ CF * deltaN d s N * N := by
      rw [← integral_const_mul]
      refine hint.trans ?_
      have h2 : C2 ≤ C2' := le_max_left _ _
      have h3 : (relEntropy f (Whole.modulatedGibbs (rieszKernel d s) N β (wd ρ))).toReal + N * deltaN d s N ≤
          (A + 1) * (N * deltaN d s N) := by nlinarith
      calc C2 * ((relEntropy f (Whole.modulatedGibbs (rieszKernel d s) N β (wd ρ))).toReal + N * deltaN d s N)
          ≤ C2' * ((relEntropy f (Whole.modulatedGibbs (rieszKernel d s) N β (wd ρ))).toReal +
            N * deltaN d s N) := by
            have : 0 ≤ (relEntropy f (Whole.modulatedGibbs (rieszKernel d s) N β (wd ρ))).toReal + N * deltaN d s N :=
              by positivity
            exact mul_le_mul_of_nonneg_right h2 this
        _ ≤ C2' * ((A + 1) * (N * deltaN d s N)) := mul_le_mul_of_nonneg_left h3 hC2'0
        _ = CF * deltaN d s N * N := by rw [hCF]; ring
    exact le_of_mul_le_mul_left (by linarith) hN0
  have hFlin : ∫⁻ Z, ENNReal.ofReal |rieszModulatedEnergy d s Z (wd ρ)| ∂f =
      ENNReal.ofReal (∫ Z, |rieszModulatedEnergy d s Z (wd ρ)| ∂f) :=
    (ofReal_integral_eq_lintegral_ofReal habsInt (ae_of_all _ fun Z => abs_nonneg _)).symm
  have hCF_le : CF ≤ C := by rw [hC]; linarith
  have hC3_le : C3 ≤ C := by rw [hC]; linarith
  have hA_le : A ≤ C := by rw [hC]; linarith
  have hCe_le : Ce ≤ C := by rw [hC]; linarith
  have hCm_le : Cm ≤ C := by rw [hC]; linarith
  -- the product entropy
  have hpi_real : (relEntropy f (Measure.pi fun _ : Fin N => wd ρ)).toReal ≤ C3 * N * deltaN d s N := by
    have hFi : Integrable (fun Z : EucConfig d N => rieszModulatedEnergy d s Z (wd ρ)) f := hfin.2
    have h1 : |∫ Z, rieszModulatedEnergy d s Z (wd ρ) ∂f| ≤ ∫ Z, |rieszModulatedEnergy d s Z (wd ρ)| ∂f :=
      abs_integral_le_integral_abs
    have hlk : -(Cp' * N * deltaN d s N) ≤ Real.log (Whole.gibbsNormalizer (rieszKernel d s) N β (wd ρ)) := by
      have := hlogK
      have h2 : Cp * N * deltaN d s N ≤ Cp' * N * deltaN d s N :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) hN0.le) hδ0.le
      have h3 := neg_abs_le (Real.log (pairNormalizer (fun x y => rieszKernel d s (x - y)) N β (wd ρ)))
      show -(Cp' * N * deltaN d s N) ≤ Real.log (pairNormalizer (fun x y => rieszKernel d s (x - y)) N β (wd ρ))
      linarith
    have h4 : β * N * ∫ Z, rieszModulatedEnergy d s Z (wd ρ) ∂f ≥ -(β * N * (CF * deltaN d s N)) := by
      have h5 := neg_abs_le (∫ Z, rieszModulatedEnergy d s Z (wd ρ) ∂f)
      have h6 : 0 ≤ β * N := by positivity
      nlinarith
    have : (relEntropy f (Measure.pi fun _ : Fin N => wd ρ)).toReal =
        (relEntropy f (Whole.modulatedGibbs (rieszKernel d s) N β (wd ρ))).toReal -
          β * N * ∫ Z, rieszModulatedEnergy d s Z (wd ρ) ∂f -
          Real.log (Whole.gibbsNormalizer (rieszKernel d s) N β (wd ρ)) := by linarith
    rw [this, hC3]
    linarith
  have hpi_ne : relEntropy f (Measure.pi fun _ : Fin N => wd ρ) ≠ ⊤ := hfin.1
  refine ⟨hH.trans (ENNReal.ofReal_le_ofReal (by nlinarith)), ?_, ?_, ?_, ?_⟩
  · rw [hFlin]
    exact ENNReal.ofReal_le_ofReal (hFint.trans (mul_le_mul_of_nonneg_right hCF_le hδ0.le))
  · rw [← ENNReal.ofReal_toReal hpi_ne]
    exact ENNReal.ofReal_le_ofReal (hpi_real.trans (by nlinarith))
  · intro C₀ hC₀
    obtain ⟨-, -, ho0', hδo'⟩ := s66_delta_facts hd1 hs0 hsd hC₀ hN
    set o := oN d s C₀ N with ho
    have hpt : ∀ Z : EucConfig d N, ENNReal.ofReal (rieszModulatedEnergy d s Z (wd ρ) + o) ≤
        ENNReal.ofReal |rieszModulatedEnergy d s Z (wd ρ)| + ENNReal.ofReal o := by
      intro Z
      refine (ENNReal.ofReal_le_ofReal ?_).trans ENNReal.ofReal_add_le
      linarith [le_abs_self (rieszModulatedEnergy d s Z (wd ρ))]
    calc ∫⁻ Z, ENNReal.ofReal (rieszModulatedEnergy d s Z (wd ρ) + o) ∂f
        ≤ ∫⁻ Z, (ENNReal.ofReal |rieszModulatedEnergy d s Z (wd ρ)| + ENNReal.ofReal o) ∂f :=
          lintegral_mono hpt
      _ = ∫⁻ Z, ENNReal.ofReal |rieszModulatedEnergy d s Z (wd ρ)| ∂f + ENNReal.ofReal o := by
          rw [lintegral_add_right _ measurable_const, lintegral_const, measure_univ, mul_one]
      _ ≤ ENNReal.ofReal (CF * deltaN d s N) + ENNReal.ofReal o := by
          rw [hFlin]; exact add_le_add (ENNReal.ofReal_le_ofReal hFint) le_rfl
      _ = ENNReal.ofReal (CF * deltaN d s N + o) :=
          (ENNReal.ofReal_add (by positivity) ho0'.le).symm
      _ ≤ ENNReal.ofReal (C * o) := by
          refine ENNReal.ofReal_le_ofReal ?_
          have h1 : CF * deltaN d s N ≤ CF * (2 * o) := mul_le_mul_of_nonneg_left hδo' hCF0
          have h2 : Ce * o ≤ C * o := mul_le_mul_of_nonneg_right hCe_le ho0'.le
          rw [hCe] at h2
          nlinarith
  · have hmom := s66_second_moment hd1 hc₁ hE (by omega : 1 ≤ N) f hpi_ne
    refine hmom.trans (ENNReal.ofReal_le_ofReal ?_)
    have h1 : (relEntropy f (Measure.pi fun _ : Fin N => wd ρ)).toReal / N ≤ C3 := by
      rw [div_le_iff₀ hN0]
      have := mul_le_mul_of_nonneg_left hδ1 (by positivity : 0 ≤ C3 * N)
      linarith
    have h2 : c₁⁻¹ * ((relEntropy f (Measure.pi fun _ : Fin N => wd ρ)).toReal / N + Real.log E') ≤ Cm := by
      rw [hCm]
      exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    linarith

end HRS.MS.MovEnt

end
