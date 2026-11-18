import HRS.Commutator.Torus.TINHOMAux6

/-!
# T-INHOM helpers, part 7: Cauchy–Schwarz for Fourier series, the Sobolev pairing, `u = ∇g_≤ * b`
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators FourierTransform ComplexConjugate

namespace HRS.Commutator.TorusNote

open HRS

variable {d : ℕ} {s : ℝ}

lemma tinhom_tsum_cs {ι : Type*} [Countable ι] (f g : ι → ℝ≥0∞) :
    ∑' i, f i * g i ≤ (∑' i, f i ^ 2) ^ ((1 : ℝ) / 2) * (∑' i, g i ^ 2) ^ ((1 : ℝ) / 2) := by
  letI : MeasurableSpace ι := ⊤
  haveI : MeasurableSingletonClass ι := ⟨fun _ => trivial⟩
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq (Measure.count : Measure ι)
    Real.HolderConjugate.two_two (f := f) (g := g) measurable_from_top.aemeasurable
    measurable_from_top.aemeasurable
  simp only [lintegral_count, Pi.mul_apply] at h
  simpa [ENNReal.rpow_two] using h

/-- The Sobolev pairing `|∫ b h| ≤ ‖b‖_{H^{-α}} ‖h‖_{H^{α}}` (without the factors `η^d`). -/
lemma tinhom_pairing_le {b h : Torus d → ℝ} (hb : MemLp b 2 volume) (hh : MemLp h 2 volume) (η α : ℝ) :
    ENNReal.ofReal |∫ x, b x * h x| ≤
      (tinhomS η (-α) (fun k => Torus.fcoef b k)) ^ ((1 : ℝ) / 2) *
        (tinhomS η α (fun k => Torus.fcoef h k)) ^ ((1 : ℝ) / 2) := by
  have hP := HRS.PDE.hasSum_parseval (fun x => ((b x : ℝ) : ℂ)) (fun x => ((h x : ℝ) : ℂ)) hb.ofReal hh.ofReal
  have hcb : ∀ k, Torus.funFourierCoeff (fun x => ((b x : ℝ) : ℂ)) k = Torus.fcoef b k := by
    intro k; rw [HRS.PDE.funFourierCoeff_eq_int]; rfl
  have hch : ∀ k, Torus.funFourierCoeff (fun x => ((h x : ℝ) : ℂ)) k = Torus.fcoef h k := by
    intro k; rw [HRS.PDE.funFourierCoeff_eq_int]; rfl
  have hint : (∫ t : Torus d, conj (((b t : ℝ) : ℂ)) * ((h t : ℝ) : ℂ)) = (((∫ x, b x * h x : ℝ)) : ℂ) := by
    rw [← integral_complex_ofReal]
    refine integral_congr_ae (ae_of_all _ fun t => ?_)
    show conj ((b t : ℝ) : ℂ) * ((h t : ℝ) : ℂ) = ((b t * h t : ℝ) : ℂ)
    rw [Complex.conj_ofReal]; push_cast; ring
  simp_rw [hcb, hch, hint] at hP
  have h1 : ENNReal.ofReal |∫ x, b x * h x| = ‖(((∫ x, b x * h x : ℝ)) : ℂ)‖ₑ := by
    rw [← ofReal_norm, Complex.norm_real, Real.norm_eq_abs]
  rw [h1, ← hP.tsum_eq]
  refine enorm_tsum_le_tsum_enorm.trans ?_
  set w : Lattice d → ℝ := fun k => 1 + 4 * Real.pi ^ 2 * η ^ 2 * Lattice.enorm k ^ 2 with hw
  have hw0 : ∀ k, 0 < w k := fun k => by simp only [hw]; positivity
  set fB : Lattice d → ℝ≥0∞ := fun k => ENNReal.ofReal (w k ^ (-α / 2)) * ‖Torus.fcoef b k‖ₑ with hfB
  set gH : Lattice d → ℝ≥0∞ := fun k => ENNReal.ofReal (w k ^ (α / 2)) * ‖Torus.fcoef h k‖ₑ with hgH
  have hterm : ∀ k, ‖conj (Torus.fcoef b k) * Torus.fcoef h k‖ₑ = fB k * gH k := by
    intro k
    have e : ENNReal.ofReal (w k ^ (-α / 2)) * ENNReal.ofReal (w k ^ (α / 2)) = 1 := by
      rw [← ENNReal.ofReal_mul (Real.rpow_nonneg (hw0 k).le _), ← Real.rpow_add (hw0 k)]
      have : -α / 2 + α / 2 = 0 := by ring
      rw [this, Real.rpow_zero]
      simp
    rw [enorm_mul, RCLike.enorm_conj]
    simp only [hfB, hgH]
    calc ‖Torus.fcoef b k‖ₑ * ‖Torus.fcoef h k‖ₑ =
        (ENNReal.ofReal (w k ^ (-α / 2)) * ENNReal.ofReal (w k ^ (α / 2))) *
          (‖Torus.fcoef b k‖ₑ * ‖Torus.fcoef h k‖ₑ) := by rw [e, one_mul]
      _ = _ := by ring
  simp_rw [hterm]
  refine (tinhom_tsum_cs fB gH).trans ?_
  have e1 : ∀ k, fB k ^ 2 = ENNReal.ofReal (w k ^ (-α)) * ‖Torus.fcoef b k‖ₑ ^ 2 := by
    intro k
    simp only [hfB]
    rw [mul_pow, ← ENNReal.ofReal_pow (Real.rpow_nonneg (hw0 k).le _)]
    congr 2
    rw [← Real.rpow_natCast, ← Real.rpow_mul (hw0 k).le]
    congr 1; push_cast; ring
  have e2 : ∀ k, gH k ^ 2 = ENNReal.ofReal (w k ^ α) * ‖Torus.fcoef h k‖ₑ ^ 2 := by
    intro k
    simp only [hgH]
    rw [mul_pow, ← ENNReal.ofReal_pow (Real.rpow_nonneg (hw0 k).le _)]
    congr 2
    rw [← Real.rpow_natCast, ← Real.rpow_mul (hw0 k).le]
    congr 1; push_cast; ring
  simp_rw [e1, e2]
  exact le_rfl

/-- Components of `u = σ * ∇g_≤` for a density. -/
lemma tinhom_convForce_eq (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) {η : ℝ} (hη : 0 < η)
    {b : Torus d → ℝ} (hb : Continuous b) (x : Torus d) (i : Fin d) :
    (SMT.ofDensity b).convForce (gloForceT s η) x i =
      textConv (fun z => gloForceT s η z i) b x := by
  obtain ⟨Bb, hBb⟩ := ten_bound_of_continuous hb
  have hBb' : ∀ y, |b y| ≤ Bb := fun y => by simpa using hBb y
  have hfin := tlowv_ofDensity_finite b hb.measurable hBb'
  obtain ⟨hp, hn⟩ := hfin
  have hFc := tsamp_gloForce_continuous hd hs0 hsd hη
  have hint : ∀ (μ : Measure (Torus d)) [IsFiniteMeasure μ],
      Integrable (fun y => gloForceT s η (x - y)) μ := fun μ _ =>
    (hFc.comp (continuous_const.sub continuous_id)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hcomp : ∀ (μ : Measure (Torus d)) [IsFiniteMeasure μ],
      (∫ y, gloForceT s η (x - y) ∂μ) i = ∫ y, gloForceT s η (x - y) i ∂μ := by
    intro μ _
    have := (EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).integral_comp_comm (hint μ)
    simpa using this.symm
  have hgi : Integrable (fun y => b y * gloForceT s η (x - y) i) :=
    (hb.mul ((EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).continuous.comp
      (hFc.comp (continuous_const.sub continuous_id)))).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have h2 := ten_int_ofDensity b (fun y => gloForceT s η (x - y) i) hb.measurable hgi
  unfold SMT.convForce SMT.intV
  rw [PiLp.sub_apply, hcomp (SMT.ofDensity b).pos, hcomp (SMT.ofDensity b).neg]
  unfold SMT.int at h2
  rw [h2]
  unfold textConv
  refine integral_congr_ae (ae_of_all _ fun y => ?_)
  ring

end HRS.Commutator.TorusNote
