import HRS.Commutator.Torus.TSAMPAux7
import HRS.Commutator.Torus.TKRAux13
import HRS.PDE.EnergyR2Fn

/-!
# T-SAMP helpers, part 8: Fourier side of `∇g_≤ * σ` (trigonometric polynomials)
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators FourierTransform

namespace HRS.Commutator.TorusNote

open HRS

variable {d : ℕ} {s : ℝ}

lemma tsamp_fcoef_eq_coeffOf (φ : Torus d → ℝ) (k : Lattice d) :
    Torus.fcoef φ k = HRS.PDE.coeffOf φ k := by
  unfold Torus.fcoef HRS.PDE.coeffOf
  rw [HRS.PDE.funFourierCoeff_eq_int]
  rfl

/-- A real function with prescribed real-symmetric trigonometric coefficients. -/
lemma tsamp_real_trig {n : ℕ} {c : Lattice d → ℂ} (hr : HRS.PDE.IsRealCoeff c)
    (hc : HRS.PDE.IsTrigPoly n c) :
    ∃ f : Torus d → ℝ, Continuous f ∧ (∀ x, ((f x : ℝ) : ℂ) = HRS.PDE.Kern.trig c x) ∧
      ∀ k, Torus.fcoef f k = c k := by
  refine ⟨HRS.PDE.toFun c, HRS.PDE.R2Aux.continuous_toFun_trig hr hc, fun x => ?_, fun k => ?_⟩
  · exact HRS.PDE.ofReal_toFun c hr (HRS.PDE.R2Aux.summable_norm_of_trig hc) x
  · rw [tsamp_fcoef_eq_coeffOf, HRS.PDE.R2Aux.coeffOf_toFun_trig hr hc]

/-- The coefficients of a real continuous function that is a trigonometric polynomial. -/
lemma tsamp_trig_fcoef {n : ℕ} {c : Lattice d → ℂ} (hc : HRS.PDE.IsTrigPoly n c)
    {h : Torus d → ℝ} (hh : ∀ x, ((h x : ℝ) : ℂ) = HRS.PDE.Kern.trig c x) (k : Lattice d) :
    Torus.fcoef h k = c k := by
  have h1 : HRS.PDE.coeffOf h = c := by
    funext k
    have e : (fun x => ((h x : ℝ) : ℂ)) = HRS.PDE.series c := funext hh
    unfold HRS.PDE.coeffOf
    rw [e]
    exact congrFun (HRS.PDE.coeffOfC_series c (HRS.PDE.R2Aux.summable_norm_of_trig hc)) k
  rw [tsamp_fcoef_eq_coeffOf, h1]


lemma tsamp_int_mode (μ : Measure (Torus d)) (k : Lattice d) (x : Torus d) :
    ∫ y, Torus.mode k (x - y) ∂μ = Torus.mode k x * ∫ y, Torus.mode (-k) y ∂μ := by
  simp_rw [tkr_mode_sub]
  rw [integral_const_mul]

lemma tsamp_integrable_mode (μ : Measure (Torus d)) [IsFiniteMeasure μ] (k : Lattice d) :
    Integrable (fun y => Torus.mode k y) μ :=
  (Torus.continuous_mode k).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

lemma tsamp_gloForce_continuous (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) {η : ℝ}
    (hη : 0 < η) : Continuous (gloForceT s η : Torus d → Euc d) := by
  have hd2 : 2 ≤ d := by omega
  have hsd1 : s + 1 < (d : ℝ) := by
    have : (3 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hFc : ∀ i : Fin d, Continuous fun z : Torus d => gloForceT s η z i := fun i =>
    tkr_glo_continuous hd2 hs0 hsd1 hη i
  have := (PiLp.continuous_toLp 2 (fun _ : Fin d => ℝ)).comp (continuous_pi hFc)
  have e : (gloForceT s η : Torus d → Euc d) =
      WithLp.toLp 2 ∘ fun a => (gloForceT s η a).ofLp := by funext a; simp
  rw [e]; exact this

lemma tsamp_convForce_trig (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) {η : ℝ} (hη : 0 < η)
    (σ : SMT d) (hσ : σ.IsFinite) (x : Torus d) (j : Fin d) :
    ((σ.convForce (gloForceT s η) x j : ℝ) : ℂ) =
      HRS.PDE.Kern.trig
        (fun k : Lattice d => ((tkrChi η k : ℝ) : ℂ) * tkrCI d s j k * σ.coef k) x := by
  have hd2 : 2 ≤ d := by omega
  have hsd1 : s + 1 < (d : ℝ) := by
    have : (3 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  obtain ⟨hp, hn⟩ := hσ
  have hFvec := tsamp_gloForce_continuous hd hs0 hsd hη
  set n : ℕ := ⌈2 / η⌉₊ with hn0
  have hT2 : HRS.PDE.IsTrigPoly n
      (fun k : Lattice d => ((tkrChi η k : ℝ) : ℂ) * tkrCI d s j k) :=
    tkr_isTrigPoly hη (fun k hk => by
      intro h0; apply hk; simp [h0])
  have hT3 : HRS.PDE.IsTrigPoly n
      (fun k : Lattice d => ((tkrChi η k : ℝ) : ℂ) * tkrCI d s j k * σ.coef k) :=
    tkr_isTrigPoly hη (fun k hk => by
      intro h0; apply hk; simp [h0])
  have hFj : ∀ z : Torus d, ((gloForceT s η z j : ℝ) : ℂ) =
      ∑ k ∈ HRS.PDE.Kern.boxF d n, ((tkrChi η k : ℝ) : ℂ) * tkrCI d s j k * Torus.mode k z := by
    intro z
    have := tkr_glo hd2 hs0 hsd1 hη z j
    rw [HRS.PDE.Kern.trig_eq_sum hT2] at this
    exact this
  have hcomp : ∀ (μ : Measure (Torus d)) [IsFiniteMeasure μ],
      ((∫ y, gloForceT s η (x - y) ∂μ) j : ℝ) = ∫ y, gloForceT s η (x - y) j ∂μ := by
    intro μ _
    have hint : Integrable (fun y => gloForceT s η (x - y)) μ :=
      (hFvec.comp (continuous_const.sub continuous_id)).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    have := (EuclideanSpace.proj j : Euc d →L[ℝ] ℝ).integral_comp_comm hint
    simpa using this.symm
  have hmode : ∀ (μ : Measure (Torus d)) [IsFiniteMeasure μ],
      (((∫ y, gloForceT s η (x - y) j ∂μ : ℝ)) : ℂ) =
        ∑ k ∈ HRS.PDE.Kern.boxF d n, ((tkrChi η k : ℝ) : ℂ) * tkrCI d s j k *
          (Torus.mode k x * ∫ y, Torus.mode (-k) y ∂μ) := by
    intro μ _
    rw [← integral_complex_ofReal]
    simp_rw [hFj]
    rw [integral_finsetSum _ (fun k _ => ?_)]
    · refine Finset.sum_congr rfl fun k _ => ?_
      rw [integral_const_mul, tsamp_int_mode]
    · exact ((Torus.continuous_mode k).comp (continuous_const.sub continuous_id)).const_mul _
        |>.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  rw [HRS.PDE.Kern.trig_eq_sum hT3]
  unfold SMT.convForce SMT.intV
  rw [PiLp.sub_apply, hcomp σ.pos, hcomp σ.neg, Complex.ofReal_sub, hmode σ.pos, hmode σ.neg,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  unfold SMT.coef
  ring

end HRS.Commutator.TorusNote
