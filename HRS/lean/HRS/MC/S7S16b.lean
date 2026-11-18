import HRS.MC.Sec7Vocab
import HRS.Main.HaarAux1
import HRS.Energy.StaticLimitBasic
import HRS.Equilibrium.FieldSingAux

/-!
# Packet `s7_S16b_tilt_invariance`: translation invariance and Haar marginal of the radial tilt
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.S16b

open HRS HRS.Sec7 HRS.MC.SEdge HRS.MC.Sec7

variable {d : ℕ}

theorem s7b_mode_add (k : Lattice d) (x y : Torus d) :
    Torus.mode k (x + y) = Torus.mode k x * Torus.mode k y := by
  simp [Torus.mode, UnitAddTorus.mFourier, fourier_apply, zsmul_add, AddCircle.toCircle_add,
    Finset.prod_mul_distrib]

theorem s7b_normSq_mode (k : Lattice d) (x : Torus d) : Complex.normSq (Torus.mode k x) = 1 := by
  rw [Complex.normSq_eq_norm_sq, Torus.norm_mode]; norm_num

/-- the complex mode sum -/
def s7b_Z (k : NonzeroLattice d) {N : ℕ} (X : Config d N) : ℂ := ∑ i, Torus.mode k.1 (X i)

theorem s7b_Z_shift (k : NonzeroLattice d) {N : ℕ} (X : Config d N) (b : Torus d) :
    Complex.normSq (s7b_Z k fun i => X i + b) = Complex.normSq (s7b_Z k X) := by
  have : s7b_Z k (fun i => X i + b) = Torus.mode k.1 b * s7b_Z k X := by
    unfold s7b_Z
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [s7b_mode_add]; ring
  rw [this, map_mul, s7b_normSq_mode, one_mul]

theorem s7b_continuous_Z (k : NonzeroLattice d) {N : ℕ} :
    Continuous fun X : Config d N => s7b_Z k X := by
  unfold s7b_Z
  exact continuous_finset_sum _ fun i _ => (Torus.continuous_mode k.1).comp (continuous_apply i)

/-- pair of real mode sums -/
theorem s7b_pair_sq (k : NonzeroLattice d) {N : ℕ} (X : Config d N) :
    (∑ i, Torus.realMode k (X i)) ^ 2 + (∑ i, Torus.realMode (s7_neg k) (X i)) ^ 2 =
      2 * Complex.normSq (s7b_Z k X) := by
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hre : (s7b_Z k X).re = ∑ i, (Torus.mode k.1 (X i)).re := by simp [s7b_Z, Complex.re_sum]
  have him : (s7b_Z k X).im = ∑ i, (Torus.mode k.1 (X i)).im := by simp [s7b_Z, Complex.im_sum]
  rw [Complex.normSq_apply]
  by_cases h : Lattice.IsPosHalf k.1
  · have h1 : ∀ x, Torus.realMode k x = Real.sqrt 2 * (Torus.mode k.1 x).re := fun x => by
      simp [Torus.realMode, h, Torus.cosMode]
    have h3 : ∀ x, Torus.realMode (s7_neg k) x = -(Real.sqrt 2 * (Torus.mode k.1 x).im) :=
      fun x => by
        have hn : ¬ Lattice.IsPosHalf (-k.1) := by
          rw [Torus.isPosHalf_neg _ k.2]; exact not_not.2 h
        simp [Torus.realMode, s7_neg, hn, Torus.sinMode, Torus.mode_neg]
    simp only [h1, h3, ← Finset.mul_sum, Finset.sum_neg_distrib, ← hre, ← him]
    nlinarith [h2]
  · have h1 : ∀ x, Torus.realMode k x = Real.sqrt 2 * (Torus.mode k.1 x).im := fun x => by
      simp [Torus.realMode, h, Torus.sinMode]
    have h3 : ∀ x, Torus.realMode (s7_neg k) x = Real.sqrt 2 * (Torus.mode k.1 x).re :=
      fun x => by
        have hn : Lattice.IsPosHalf (-k.1) := by
          rw [Torus.isPosHalf_neg _ k.2]; exact h
        simp [Torus.realMode, s7_neg, hn, Torus.cosMode, Torus.mode_neg]
    simp only [h1, h3, ← Finset.mul_sum, ← hre, ← him]
    nlinarith [h2]

theorem s7b_fourierCoeff_eta {m : ℝ} (hm : (d : ℝ) < 2 * m) {N : ℕ} (X : Config d N)
    (j : NonzeroLattice d) :
    NegSobolev.fourierCoeff (etaE m X volume) j =
      Real.sqrt N * ((N : ℝ)⁻¹ * ∑ i, Torus.realMode j (X i)) := by
  have : IsFiniteMeasure (empirical X) := by
    unfold empirical
    rcases Nat.eq_zero_or_pos N with h | h
    · subst h; simp; infer_instance
    · have : (N : ℝ≥0∞)⁻¹ ≠ ⊤ := by simp [h.ne']
      exact Measure.smul_finite _ this
  unfold etaE flucE
  rw [HRS.FieldSingAux.fourierCoeff_smul, NegSobolev.fourierCoeff_ofMeasureDiff hm]
  unfold Torus.measureRealCoeff
  rw [HRS.integral_empirical X (HRS.continuous_realMode' j), Torus.integral_realMode, sub_zero]

theorem s7b_W_eq {m : ℝ} (hm : (d : ℝ) < 2 * m) (k : NonzeroLattice d) {N : ℕ} (X : Config d N) :
    ‖s7_modePair m k (etaE m X volume)‖ ^ 2 =
      (Real.sqrt N * (N : ℝ)⁻¹) ^ 2 * (2 * Complex.normSq (s7b_Z k X)) := by
  rw [← s7b_pair_sq, EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity), Fin.sum_univ_two]
  simp only [s7_modePair, ite_true, Fin.one_eq_zero_iff, Nat.succ_ne_self, ite_false,
    Real.norm_eq_abs, sq_abs, s7b_fourierCoeff_eta hm]
  ring

theorem s7b_W_shift {m : ℝ} (hm : (d : ℝ) < 2 * m) (k : NonzeroLattice d) {N : ℕ}
    (X : Config d N) (b : Torus d) :
    ‖s7_modePair m k (etaE m (fun i => X i + b) volume)‖ ^ 2 =
      ‖s7_modePair m k (etaE m X volume)‖ ^ 2 := by
  rw [s7b_W_eq hm, s7b_W_eq hm, s7b_Z_shift]

theorem s7b_W_meas {m : ℝ} (hm : (d : ℝ) < 2 * m) (k : NonzeroLattice d) {N : ℕ} :
    Measurable fun X : Config d N => ‖s7_modePair m k (etaE m X volume)‖ ^ 2 := by
  have : (fun X : Config d N => ‖s7_modePair m k (etaE m X volume)‖ ^ 2) =
      fun X => (Real.sqrt N * (N : ℝ)⁻¹) ^ 2 * (2 * Complex.normSq (s7b_Z k X)) :=
    funext fun X => s7b_W_eq hm k X
  rw [this]
  exact (continuous_const.mul (continuous_const.mul
    (Complex.continuous_normSq.comp (s7b_continuous_Z k)))).measurable

theorem s7_S16b_tilt_invariance_proof (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) {β : ℝ}
    (hβ : 0 < β) (m : ℝ) (hm : (d : ℝ) / 2 < m) (k : NonzeroLattice d) (θ : ℝ → ℝ)
    (hθm : Measurable θ) (hθ : ∀ x, 1 ≤ θ x) (hθb : ∃ M, ∀ x, θ x ≤ M) (N : ℕ) :
    IsProbabilityMeasure (s7_tiltedLaw d s β N m k θ) ∧
      (∀ b : Torus d, (s7_tiltedLaw d s β N m k θ).map (fun X i => X i + b) =
        s7_tiltedLaw d s β N m k θ) ∧
      (1 ≤ N → firstMarginal (s7_tiltedLaw d s β N m k θ) = volume) := by
  have hd1 : 1 ≤ d := by omega
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hsd : s < d := by linarith
  have hmd : (d : ℝ) < 2 * m := by linarith
  have hg : Measurable (periodicRiesz d s) := CoercAux.measurable_periodicRiesz_one hd1 hs0 hsd
  have hint : Integrable (fun X : Config d N =>
      Real.exp (-β * N * modulatedEnergyKernel (periodicRiesz d s) X volume))
      (Measure.pi fun _ : Fin N => (volume : Measure (Torus d))) := by
    rcases Nat.eq_zero_or_pos N with h0 | h0
    · subst h0; simp
    · obtain ⟨B, hB⟩ := periodicRiesz_ge hd hs0 hsd
      exact haar_boltz_integrable hg (le_max_right B 0)
        (fun x => (neg_le_neg (le_max_left B 0)).trans (hB x)) β hβ h0
  have hK : 0 < gibbsNormalizer (periodicRiesz d s) N β (volume : Measure (Torus d)) := by
    unfold gibbsNormalizer
    exact integral_exp_pos hint
  have hQprob : IsProbabilityMeasure (modulatedGibbs (periodicRiesz d s) N β
      (volume : Measure (Torus d))) :=
    modulatedGibbs_isProbabilityMeasure _ β _ hK hint
  set Q := modulatedGibbs (periodicRiesz d s) N β (volume : Measure (Torus d)) with hQdef
  have hτ : ∀ b : Torus d, Measurable fun X : Config d N => fun i => X i + b :=
    fun b => haar_shift_measurable b
  have hQinv : ∀ b : Torus d, Q.map (fun X : Config d N => fun i => X i + b) = Q := by
    intro b
    rcases Nat.eq_zero_or_pos N with h0 | h0
    · subst h0
      have : (fun X : Config d 0 => fun i => X i + b) = id := by
        funext X i; exact i.elim0
      rw [this, Measure.map_id]
    · exact haar_gibbs_shift_invariant hg h0 β b
  obtain ⟨M, hM⟩ := hθb
  have hWm := s7b_W_meas (N := N) hmd k
  set w : Config d N → ℝ≥0∞ := fun X =>
    ENNReal.ofReal (θ (‖s7_modePair m k (etaE m X volume)‖ ^ 2)) with hwdef
  have hwm : Measurable w := ENNReal.measurable_ofReal.comp (hθm.comp hWm)
  have hwsh : ∀ (b : Torus d) X, w (fun i => X i + b) = w X := fun b X => by
    simp only [hwdef, s7b_W_shift hmd]
  have hw1 : ∀ X, 1 ≤ w X := fun X => by
    simp only [hwdef]
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (hθ _)
  have hwM : ∀ X, w X ≤ ENNReal.ofReal M := fun X =>
    ENNReal.ofReal_le_ofReal (hM _)
  set Zn := ∫⁻ X, w X ∂Q with hZn
  have hZ1 : 1 ≤ Zn := by
    calc (1 : ℝ≥0∞) = ∫⁻ _, 1 ∂Q := by simp
      _ ≤ Zn := lintegral_mono hw1
  have hZtop : Zn ≠ ⊤ := by
    refine ne_top_of_le_ne_top (b := ENNReal.ofReal M) ENNReal.ofReal_ne_top ?_
    calc Zn ≤ ∫⁻ _, ENNReal.ofReal M ∂Q := lintegral_mono hwM
      _ = ENNReal.ofReal M := by simp
  have hT : s7_tiltedLaw d s β N m k θ = Zn⁻¹ • Q.withDensity w := rfl
  have hZ0 : Zn ≠ 0 := (lt_of_lt_of_le one_pos hZ1).ne'
  have hprob : IsProbabilityMeasure (s7_tiltedLaw d s β N m k θ) := by
    refine ⟨?_⟩
    rw [hT, Measure.smul_apply, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      smul_eq_mul]
    exact ENNReal.inv_mul_cancel hZ0 hZtop
  have hinv : ∀ b : Torus d, (s7_tiltedLaw d s β N m k θ).map
      (fun X i => X i + b) = s7_tiltedLaw d s β N m k θ := by
    intro b
    have hmp : MeasurePreserving (fun X : Config d N => fun i => X i + b) Q Q := ⟨hτ b, hQinv b⟩
    have key : (Q.withDensity w).map (fun X : Config d N => fun i => X i + b) =
        Q.withDensity w := by
      ext A hA
      rw [Measure.map_apply (hτ b) hA, withDensity_apply _ ((hτ b) hA), withDensity_apply _ hA]
      calc ∫⁻ X in (fun X : Config d N => fun i => X i + b) ⁻¹' A, w X ∂Q
          = ∫⁻ X in (fun X : Config d N => fun i => X i + b) ⁻¹' A,
              w ((fun X : Config d N => fun i => X i + b) X) ∂Q := by
            simp only [hwsh]
        _ = ∫⁻ X in A, w X ∂Q := hmp.setLIntegral_comp_preimage hA hwm
    rw [hT, Measure.map_smul, key]
    exact (hτ b).aemeasurable
  refine ⟨hprob, hinv, fun hN => ?_⟩
  exact haar_firstMarginal_of_invariant hN hinv

end HRS.MC.Sec7.S16b
