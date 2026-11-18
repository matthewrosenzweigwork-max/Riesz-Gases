import HRS.MS.S111X2Aux16
import HRS.MS.S111X2Aux5

/-!
# S11.1 X2, packet E03: the classical fluctuation-dissipation theorem
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S111X2

open HRS (Euc)
open HRS.Whole HRS.Whole.Q34
open HRS.MS.S111X1 (EnData KData Nnl)
open HRS.MS.TcR (tc2_integrable_nu tc2_integral_nu)

variable {d : ℕ}

/-- **E03 (derivative part).** -/
theorem s111x2_classical_fd_deriv (hd : 2 ≤ d) {s a β H : ℝ} (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2)
    (ha : 0 < a) (hβ : 0 < β) (hH : 0 < H) {ρ : Euc d → ℝ} (hρ : IsThermalEquilibrium d s a β ρ)
    {φ ψ : Euc d → ℝ} {f h : ℝ → Euc d → ℝ}
    (hf : IsClassicalAdjointW ((quadraticGradientDyn d s a β).coeff (fun _ => ρ)) H φ f)
    (hh : IsClassicalAdjointW ((quadraticGradientDyn d s a β).coeff (fun _ => ρ)) H ψ h) :
    (∀ r ∈ Ioo 0 H, HasDerivAt (fun q => HRS.Whole.susceptibilityCov (HRS.Whole.rieszKernel d s)
        (HRS.Whole.withDensityReal ρ) β (f q) (h q))
        (2 * β⁻¹ * s111x2_dirichlet (HRS.Whole.withDensityReal ρ) (f r) (h r)) r) ∧
      ContinuousOn (fun q => HRS.Whole.susceptibilityCov (HRS.Whole.rieszKernel d s)
        (HRS.Whole.withDensityReal ρ) β (f q) (h q)) (Icc 0 H) := by
  have hdr : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hsd : s < d := by linarith
  obtain ⟨M, T⟩ := s111x2_td_of_thermal hd hs0 hs ha hβ hρ
  haveI := isProbabilityMeasure_nu T.prob
  obtain ⟨M₀, c, S, hc, hTc⟩ := HRS.MS.TransOp.s611_tcref_of_thermal hd hs0 hsd ha hβ hρ
  obtain ⟨Mg, K, hK⟩ := s111x2_krep_of_tcref (by omega) hs0 hsd hc hTc
  have hθ : (0 : ℝ) ≤ β := hβ.le
  set μ := HRS.Whole.withDensityReal ρ with hμ
  set C := (quadraticGradientDyn d s a β).coeff (fun _ => ρ) with hC
  have hRF := s111x2_responseForm hK hθ (le_refl β)
  obtain ⟨Bf0, Bf1, Bf2, hBf0, hBf1, hBf2, hfB⟩ := HRS.MS.S111X1.classical_bounds hf
  obtain ⟨Bh0, Bh1, Bh2, hBh0, hBh1, hBh2, hhB⟩ := HRS.MS.S111X1.classical_bounds hh
  have hfC : ∀ r ∈ Icc (0 : ℝ) H, CbD (f r) Bf1 Bf2 := fun r hr =>
    ⟨hf.c2 r hr, fun x => (hfB r hr x).2.1, fun x => (hfB r hr x).2.2⟩
  have hhC : ∀ r ∈ Icc (0 : ℝ) H, CbD (h r) Bh1 Bh2 := fun r hr =>
    ⟨hh.c2 r hr, fun x => (hhB r hr x).2.1, fun x => (hhB r hr x).2.2⟩
  have hfL : ∀ r ∈ Icc (0 : ℝ) H, MemLp (f r) 2 μ := fun r hr =>
    MemLp.of_bound (hf.c2 r hr).continuous.aestronglyMeasurable Bf0
      (Filter.Eventually.of_forall fun x => (hfB r hr x).1) |>.mono_exponent le_top
  have hhL : ∀ r ∈ Icc (0 : ℝ) H, MemLp (h r) 2 μ := fun r hr =>
    MemLp.of_bound (hh.c2 r hr).continuous.aestronglyMeasurable Bh0
      (Filter.Eventually.of_forall fun x => (hhB r hr x).1) |>.mono_exponent le_top
  have hfcl : ∀ r ∈ Icc (0 : ℝ) H, ∀ x, ‖f r x‖ ≤ Bf0 := fun r hr x => (hfB r hr x).1
  obtain ⟨Af, hAf⟩ := hf.bdd_time_deriv
  obtain ⟨Ah, hAh⟩ := hh.bdd_time_deriv
  -- the susceptibility form as a Hilbert space inner product
  have hE : ∀ r ∈ Icc (0 : ℝ) H, HRS.Whole.susceptibilityCov (HRS.Whole.rieszKernel d s) μ β (f r) (h r) =
      inner ℝ (Pc μ (s111x2_toLp μ (f r))) (s111x2_Rm hK.posOp hθ (Pc μ (s111x2_toLp μ (h r)))) :=
    fun r hr => s111x2_susc_eq_inner hK hθ (hfL r hr) (hhL r hr)
  constructor
  · intro r hr
    have hrI : r ∈ Icc (0 : ℝ) H := ⟨hr.1.le, hr.2.le⟩
    -- derivative data
    have hdf : ∀ x, ∀ r' ∈ Ioo (0 : ℝ) H, HasDerivAt (fun q => f q x)
        ((fun x => -generatorW C 0 (f r') x) x) r' := by
      intro x r' hr'
      have := hf.time_deriv x r' hr'
      rwa [s111x2_gen_auto T (hfC r' ⟨hr'.1.le, hr'.2.le⟩) r'] at this
    have hdh : ∀ x, ∀ r' ∈ Ioo (0 : ℝ) H, HasDerivAt (fun q => h q x)
        ((fun x => -generatorW C 0 (h r') x) x) r' := by
      intro x r' hr'
      have := hh.time_deriv x r' hr'
      rwa [s111x2_gen_auto T (hhC r' ⟨hr'.1.le, hr'.2.le⟩) r'] at this
    have hGf := s111x2_gen_memLp T (hfC r hrI)
    have hGh := s111x2_gen_memLp T (hhC r hrI)
    have hFl := s111x2_lp_hasDerivAt (μ := μ) (w := f) (w' := fun r' x => -generatorW C 0 (f r') x)
      (a := 0) (b := H) (A := Af) hr (fun r' hr' => hfL r' ⟨hr'.1.le, hr'.2.le⟩) hGf.neg hdf
      (fun r' hr' x => by
        have := hAf r' ⟨hr'.1.le, hr'.2.le⟩ x
        rwa [s111x2_gen_auto T (hfC r' ⟨hr'.1.le, hr'.2.le⟩) r', abs_neg] at *)
      (s111x2_lin_memLp T Af)
    have hHl := s111x2_lp_hasDerivAt (μ := μ) (w := h) (w' := fun r' x => -generatorW C 0 (h r') x)
      (a := 0) (b := H) (A := Ah) hr (fun r' hr' => hhL r' ⟨hr'.1.le, hr'.2.le⟩) hGh.neg hdh
      (fun r' hr' x => by
        have := hAh r' ⟨hr'.1.le, hr'.2.le⟩ x
        rwa [s111x2_gen_auto T (hhC r' ⟨hr'.1.le, hr'.2.le⟩) r', abs_neg] at *)
      (s111x2_lin_memLp T Ah)
    have hA : HasDerivAt (fun q => Pc μ (s111x2_toLp μ (f q)))
        (Pc μ (s111x2_toLp μ (fun x => -generatorW C 0 (f r) x))) r :=
      (Pc μ).hasFDerivAt.comp_hasDerivAt r hFl
    have hB : HasDerivAt (fun q => s111x2_Rm hK.posOp hθ (Pc μ (s111x2_toLp μ (h q))))
        (s111x2_Rm hK.posOp hθ (Pc μ (s111x2_toLp μ (fun x => -generatorW C 0 (h r) x)))) r :=
      (s111x2_Rm hK.posOp hθ).hasFDerivAt.comp_hasDerivAt r ((Pc μ).hasFDerivAt.comp_hasDerivAt r hHl)
    have hAB := hA.inner ℝ hB
    have hev : (fun q => HRS.Whole.susceptibilityCov (HRS.Whole.rieszKernel d s) μ β (f q) (h q)) =ᶠ[nhds r]
        fun q => inner ℝ (Pc μ (s111x2_toLp μ (f q))) (s111x2_Rm hK.posOp hθ (Pc μ (s111x2_toLp μ (h q)))) := by
      filter_upwards [Ioo_mem_nhds hr.1 hr.2] with q hq
      exact hE q ⟨hq.1.le, hq.2.le⟩
    refine (hAB.congr_of_eventuallyEq hev).congr_deriv ?_
    -- value of the derivative
    rw [s111x2_toLp_neg hGf, s111x2_toLp_neg hGh]
    simp only [map_neg, inner_neg_left, inner_neg_right]
    have e1 := s111x2_susc_eq_inner hK hθ (hfL r hrI) hGh
    have e3 := s111x2_susc_eq_inner hK hθ hGf (hhL r hrI)
    have i1 := s111x2_susc_gen T (hhC r hrI) ((hfC r hrI).smooth.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2))
      (fun x => hfcl r hrI x) (fun x => (hfC r hrI).d1 x)
    have i2 := s111x2_susc_gen T (hfC r hrI) ((hhC r hrI).smooth.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2))
      (fun x => (hhB r hrI x).1) (fun x => (hhC r hrI).d1 x)
    have sym := hRF.symmetry _ _ hGf (hhL r hrI)
    rw [← e1, ← e3, sym, i1, i2, s111x2_dirichlet_symm μ (h r) (f r)]
    ring
  · have hcont0 : ∀ (φ' : Euc d → ℝ) (u : ℝ → Euc d → ℝ), IsClassicalAdjointW C H φ' u → ∀ x, ContinuousOn (fun q => u q x) (Icc 0 H) := by
      intro φ' u hu x
      have h0 := hu.cont_c2 0 (by norm_num)
      have h1 : Continuous fun r : Icc (0 : ℝ) H => iteratedFDeriv ℝ 0 (u r) x :=
        h0.comp (continuous_id.prodMk continuous_const)
      have h2 : Continuous fun r : Icc (0 : ℝ) H => u r x := by
        have := (continuousMultilinearCurryFin0 ℝ (Euc d) ℝ).continuous.comp h1
        refine this.congr fun r => ?_
        simp [iteratedFDeriv_zero_eq_comp]
      exact continuousOn_iff_continuous_restrict.2 h2
    have hFc : ∀ r ∈ Icc (0 : ℝ) H, ContinuousWithinAt (fun q => s111x2_toLp μ (f q)) (Icc 0 H) r :=
      fun r hr => s111x2_lp_continuousWithinAt (μ := μ) (G := fun _ => Bf0) hr hfL (hcont0 φ f hf)
        (fun r' hr' x => by simpa using hfcl r' hr' x) (memLp_const _)
    have hHc : ∀ r ∈ Icc (0 : ℝ) H, ContinuousWithinAt (fun q => s111x2_toLp μ (h q)) (Icc 0 H) r :=
      fun r hr => s111x2_lp_continuousWithinAt (μ := μ) (G := fun _ => Bh0) hr hhL (hcont0 ψ h hh)
        (fun r' hr' x => by simpa using (hhB r' hr' x).1) (memLp_const _)
    have hcc : ContinuousOn (fun q => inner ℝ (Pc μ (s111x2_toLp μ (f q)))
        (s111x2_Rm hK.posOp hθ (Pc μ (s111x2_toLp μ (h q))))) (Icc 0 H) := fun r hr =>
      ((Pc μ).continuous.continuousAt.comp_continuousWithinAt (hFc r hr)).inner
        ((s111x2_Rm hK.posOp hθ).continuous.continuousAt.comp_continuousWithinAt
          ((Pc μ).continuous.continuousAt.comp_continuousWithinAt (hHc r hr)))
    exact hcc.congr hE

end HRS.MS.S111X2
