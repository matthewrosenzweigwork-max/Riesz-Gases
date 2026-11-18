import HRS.MS.Fp81S21InitialFR4
import HRS.MS.Fp81S21InitialMoments3

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators RealInnerProductSpace ContDiff

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000
noncomputable section

namespace HRS.Fp81.S21

open S45 S99
open HRS.Whole
open HRS (Euc MemCb cbNorm)
open HRS.MS.R26T3

/-!
## SOL31 packet 24b: the actual-initial-law singular-kernel limit

Thermal `s99_Bkernel` (`R2SeAux31:45`) first fixes one finite-rank approximant
using the uniform actual-law tail and kernel-approximation bounds.  It then
uses the finite-rank constant for that fixed approximant to choose the particle
cutoff.  The constant in `fp81s21_initial_FR` may depend on the approximant;
this order of choices is exactly what the qualitative limit needs.

Dictionary: thermal `Bh`, `Bterm`, and `Qk` become
`fp81s21_initial_Bh`, `fp81s21_initial_Bterm`, and
`fp81s21_initial_Qk`; thermal `s99_tail` is supplied by
`fp81s21_initial_F_tail_exists` / `fp81s21_initial_F_tail`; thermal
`s99_FR` is `fp81s21_initial_FR`; the approximation and coefficient-difference
steps use `IsRound2Approx.converges`, `S99.s99_tsum2_sub`, and the actual-law
response bounds in `InitialFamData`.

Closure already ported: finite-rank quadratic estimate (wR42, `InitialFR`),
actual-law tails (wR25, `InitialMoments3`), the mixed `Mab` bounds (wR40),
and the bias and linear/quadratic moment bounds (wR22-wR25).  The proof here
does not use a thermal law or a thermal equilibrium identity.
-/

/-- The centered quadratic statistic under the actual initial law. -/
def fp81s21_initial_Bh {p : Parameters} {δ : ℝ} (R : Trajectory p δ)
    (N : ℕ) (h : Euc p.d → Euc p.d → ℝ) (X : EucConfig p.d N) : ℝ :=
  (N : ℝ) * (pairEnergy h X (r26t3_mu R 0) -
    ∫ Y, pairEnergy h Y (r26t3_mu R 0) ∂(r26t3_Q R N))

/-- Bounded kernels have integrable rows and product under the actual initial
reference, by its Round2 density and kernel envelope. -/
theorem fp81s21_initial_kernel_wr8
    {p : Parameters} {δ : ℝ} (hδ : 0 < δ) (hδh : δ ≤ 1 / 2)
    (R : Trajectory p δ) {B : ℝ} {h : Euc p.d → Euc p.d → ℝ}
    (hh : IsBoundedPairKernel p.s B h) :
    HRS.MS.Wr.Wr8Ok (r26t3_mu R 0) h := by
  have hsd : p.s < p.d := by
    have hsd' := p.hs
    have hdpos : (0 : ℝ) ≤ (p.d : ℝ) / 2 := by positivity
    linarith
  obtain ⟨M, L, hρ⟩ := s21f_round2Density_init hδ hδh R
  haveI hμ : IsProbabilityMeasure (r26t3_mu R 0) :=
    HRS.Whole.Q34.isProbabilityMeasure_nu hρ.prob
  obtain ⟨hrows, hprod, -⟩ := HRS.MS.R2Mt.s92_kernel_integrable
    (by have := p.hd; omega) p.hs0 hsd M hρ.prob hρ.bdd hh
  exact ⟨hh.measurable, hrows, hprod⟩

/-- Pair energies of bounded kernels are integrable under the actual initial
particle law. -/
theorem fp81s21_initial_pairEnergy_int
    {p : Parameters} {δ : ℝ} (hδ : 0 < δ) (hδh : δ ≤ 1 / 2)
    (R : Trajectory p δ) (E : InitialSteinEnv R) (hγ : 0 < p.γ)
    {B : ℝ} {h : Euc p.d → Euc p.d → ℝ}
    (hh : IsBoundedPairKernel p.s B h) {N : ℕ} (hN : 2 ≤ N) :
    Integrable (fun X : EucConfig p.d N => pairEnergy h X (r26t3_mu R 0))
      (r26t3_Q R N) := by
  haveI hP : IsProbabilityMeasure (r26t3_Q R N) := by
    rw [← E.law_eq N]
    exact (E.static N hN).prob
  haveI hμ : IsProbabilityMeasure (r26t3_mu R 0) :=
    HRS.Whole.Q34.isProbabilityMeasure_nu E.reference.prob
  have hk := fp81s21_initial_kernel_wr8 hδ hδh R hh
  have hmeas : Measurable (fun X : EucConfig p.d N => pairEnergy h X (r26t3_mu R 0)) :=
    HRS.MS.Wr.wr9_measurable_pairEnergy hk.meas
  obtain ⟨C, hC, hF, -, -⟩ :=
    r26t3_static_moments hδ hδh R hγ 1 le_rfl
  have hbound := (hF B h hh) () N hN
  have hscaled : Integrable
      (fun X : EucConfig p.d N => (N : ℝ) * pairEnergy h X (r26t3_mu R 0))
      (r26t3_Q R N) := by
    have hmeas' : AEStronglyMeasurable
        (fun X : EucConfig p.d N => (N : ℝ) * pairEnergy h X (r26t3_mu R 0))
        (r26t3_Q R N) := (measurable_const.mul hmeas).aestronglyMeasurable
    have hBnonneg : 0 ≤ B := HRS.MS.Wr.wr14a_nonneg_of_bound
      (by have := p.hd; omega) hh.bound
    have hL1 := S99.s99_l1_bound (mul_nonneg hC hBnonneg) hmeas' (by simpa using hbound.1)
    exact hL1.1
  have hscaled' := hscaled.const_mul (N : ℝ)⁻¹
  refine hscaled'.congr (Filter.Eventually.of_forall fun X => ?_)
  simp only
  field_simp

/-- The actual-law centered quadratic statistic is integrable. -/
theorem fp81s21_initial_Bh_int
    {p : Parameters} {δ : ℝ} (hδ : 0 < δ) (hδh : δ ≤ 1 / 2)
    (R : Trajectory p δ) (E : InitialSteinEnv R) (hγ : 0 < p.γ)
    {B : ℝ} {h : Euc p.d → Euc p.d → ℝ}
    (hh : IsBoundedPairKernel p.s B h) {N : ℕ} (hN : 2 ≤ N) :
    Integrable (fun X : EucConfig p.d N => fp81s21_initial_Bh R N h X)
      (r26t3_Q R N) := by
  haveI hP : IsProbabilityMeasure (r26t3_Q R N) := by
    rw [← E.law_eq N]
    exact (E.static N hN).prob
  haveI hμ : IsProbabilityMeasure (r26t3_mu R 0) :=
    HRS.Whole.Q34.isProbabilityMeasure_nu E.reference.prob
  have hk := fp81s21_initial_kernel_wr8 hδ hδh R hh
  have hmeas : Measurable (fun X : EucConfig p.d N => pairEnergy h X (r26t3_mu R 0)) :=
    HRS.MS.Wr.wr9_measurable_pairEnergy hk.meas
  have hBh_meas : Measurable (fun X : EucConfig p.d N => fp81s21_initial_Bh R N h X) := by
    exact measurable_const.mul (hmeas.sub measurable_const)
  obtain ⟨C, hC, hF, -, -⟩ :=
    r26t3_static_moments hδ hδh R hγ 1 le_rfl
  have hbound := (hF B h hh) () N hN
  have hBnonneg : 0 ≤ B := HRS.MS.Wr.wr14a_nonneg_of_bound
    (by have := p.hd; omega) hh.bound
  have hCbound : 0 ≤ C * B := mul_nonneg hC hBnonneg
  have hL1 := S99.s99_l1_bound hCbound hBh_meas.aestronglyMeasurable (by
    simpa [fp81s21_initial_Bh] using hbound.2)
  exact hL1.1

/-- Linearity of the centered actual-law statistic in its kernel. -/
theorem fp81s21_initial_Bh_sub
    {p : Parameters} {δ : ℝ} (hδ : 0 < δ) (hδh : δ ≤ 1 / 2)
    (R : Trajectory p δ) (E : InitialSteinEnv R) (hγ : 0 < p.γ)
    {B₁ B₂ : ℝ} {h₁ h₂ : Euc p.d → Euc p.d → ℝ}
    (hh₁ : IsBoundedPairKernel p.s B₁ h₁)
    (hh₂ : IsBoundedPairKernel p.s B₂ h₂) {N : ℕ} (hN : 2 ≤ N)
    (X : EucConfig p.d N) :
    fp81s21_initial_Bh R N h₁ X - fp81s21_initial_Bh R N h₂ X =
      fp81s21_initial_Bh R N (fun x y => h₁ x y - h₂ x y) X := by
  haveI hP : IsProbabilityMeasure (r26t3_Q R N) := by
    rw [← E.law_eq N]
    exact (E.static N hN).prob
  haveI hμ : IsProbabilityMeasure (r26t3_mu R 0) :=
    HRS.Whole.Q34.isProbabilityMeasure_nu E.reference.prob
  have w₁ := fp81s21_initial_kernel_wr8 hδ hδh R hh₁
  have w₂ := fp81s21_initial_kernel_wr8 hδ hδh R hh₂
  have hsub : ∀ Y : EucConfig p.d N,
      pairEnergy (fun x y => h₁ x y - h₂ x y) Y (r26t3_mu R 0) =
        pairEnergy h₁ Y (r26t3_mu R 0) - pairEnergy h₂ Y (r26t3_mu R 0) := by
    intro Y
    have h := HRS.MS.Wr.wr9_pairEnergy_sub (N := N) w₁ w₂ 1 Y
    simpa using h
  have hi₁ := fp81s21_initial_pairEnergy_int hδ hδh R E hγ hh₁ hN
  have hi₂ := fp81s21_initial_pairEnergy_int hδ hδh R E hγ hh₂ hN
  unfold fp81s21_initial_Bh
  simp_rw [hsub]
  rw [integral_sub hi₁ hi₂]
  ring

/-- Each member of an actual-law Round2 approximation is a bounded pair
kernel with the uniform envelope supplied by the approximation. -/
theorem fp81s21_initial_approx_bounded
    {p : Parameters} {δ : ℝ}
    (R : Trajectory p δ) {B C₂ : ℝ} {h : Euc p.d → Euc p.d → ℝ}
    {hj : ℕ → Euc p.d → Euc p.d → ℝ}
    (ha : IsRound2Approx p.s C₂ B (r26t3_mu R 0) h hj) (n : ℕ) :
    IsBoundedPairKernel p.s (C₂ * B) (hj n) := by
  obtain ⟨m, cc, u, hu, e⟩ := ha.finiteRank n
  refine ⟨?_, ?_, fun x y hxy => ha.envelope n x y hxy⟩
  · have hm := HRS.MS.R2Mt.s92_finiteRank_meas hu
    rw [e]
    exact hm
  · intro x y
    rw [e]
    exact HRS.MS.R2Mt.s92_finiteRank_symm hu x y

#print axioms fp81s21_initial_kernel_wr8
#print axioms fp81s21_initial_pairEnergy_int
#print axioms fp81s21_initial_Bh_int
#print axioms fp81s21_initial_Bh_sub
#print axioms fp81s21_initial_approx_bounded

end HRS.Fp81.S21

end
