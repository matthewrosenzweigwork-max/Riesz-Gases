import HRS.MC.Sec7Vocab
import HRS.MC.S7S16b
import HRS.MC.S7S16d
import HRS.MC.SEdgeS16aAux2
import HRS.MC.S7S16fAux1
import HRS.MC.S7S16fAux4

/-!
# Packet `slow_correction` (S16f), part 5: the tilted initial laws `f_N`

`f_N = s7_tiltedLaw` with the weight `theta_a(x) = 1 + (1 + a) exp(-max(x,0))`, i.e. `1 + (1 + a) v(pi eta_N)` on
the support.  Density bound relative to `Q_{N,beta}`, and the integral formula for `E_{f_N} F(eta_N)`.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.S16f

open HRS HRS.Sec7 HRS.MC.SEdge HRS.MC.Sec7 HRS.MC.SEdge.S16a HRS.MC.Sec7.S16b

variable {d : ℕ}

/-- the tilt weight -/
def s16f_θ (a : ℝ) : ℝ → ℝ := fun x => 1 + (1 + a) * Real.exp (-(max x 0))

theorem s16f_θ_meas (a : ℝ) : Measurable (s16f_θ a) := by
  unfold s16f_θ; fun_prop

theorem s16f_θ_ge {a : ℝ} (ha : 0 ≤ a) (x : ℝ) : 1 ≤ s16f_θ a x := by
  unfold s16f_θ
  have := mul_nonneg (by linarith : (0 : ℝ) ≤ 1 + a) (Real.exp_pos (-(max x 0))).le
  linarith

theorem s16f_θ_le {a : ℝ} (ha : 0 ≤ a) (x : ℝ) : s16f_θ a x ≤ 2 + a := by
  unfold s16f_θ
  have h1 : Real.exp (-(max x 0)) ≤ 1 := by
    rw [Real.exp_le_one_iff]; simpa using le_max_right x 0
  have := mul_le_mul_of_nonneg_left h1 (by linarith : (0 : ℝ) ≤ 1 + a)
  linarith

theorem s16f_θ_sq (a : ℝ) (z : EuclideanSpace ℝ (Fin 2)) :
    s16f_θ a (‖z‖ ^ 2) = 1 + (1 + a) * s16f_v z := by
  unfold s16f_θ s16f_v
  rw [max_eq_left (sq_nonneg _)]

/-- `Phi_0 = v o pi` on `E_m` -/
def s16f_Φ (m : ℝ) (k : NonzeroLattice d) : NegSobolev d m → ℝ :=
  fun y => s16f_v (s7_modePair m k y)

theorem s16f_Φ_cont (m : ℝ) (k : NonzeroLattice d) : Continuous (s16f_Φ m k) := by
  obtain ⟨π, hπ, -⟩ := HRS.MC.Sec7.S16d.s7_S16d_modePair_clm_proof d m k
  have : s16f_Φ m k = fun y => s16f_v (π y) := by
    funext y; simp [s16f_Φ, hπ]
  rw [this]
  exact s16f_memCb_v.1.continuous.comp π.continuous

theorem s16f_Φ_pos (m : ℝ) (k : NonzeroLattice d) (y : NegSobolev d m) : 0 < s16f_Φ m k y :=
  s16f_v_pos _

theorem s16f_Φ_le_one (m : ℝ) (k : NonzeroLattice d) (y : NegSobolev d m) : s16f_Φ m k y ≤ 1 :=
  s16f_v_le_one _

theorem s16f_memCb_Φ (m : ℝ) (k : NonzeroLattice d) : MemCb 5 (s16f_Φ m k) := by
  obtain ⟨π, hπ, -⟩ := HRS.MC.Sec7.S16d.s7_S16d_modePair_clm_proof d m k
  have : s16f_Φ m k = fun y => s16f_v (π y) := by
    funext y; simp [s16f_Φ, hπ]
  rw [this]
  exact Tilt715Aux.memCb_comp_clm π s16f_memCb_v

section Gibbs

variable {s : ℝ} (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) {β : ℝ} (hβ : 0 < β)
include hd hs0 hs hβ

theorem s16f_Q_prob (N : ℕ) :
    IsProbabilityMeasure (modulatedGibbs (periodicRiesz d s) N β (volume : Measure (Torus d))) := by
  have hd1 : 1 ≤ d := by omega
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hsd : s < d := by linarith
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
  exact modulatedGibbs_isProbabilityMeasure _ β _ hK hint

theorem s16f_meas_eta (m : ℝ) (hm : (d : ℝ) / 2 < m) {N : ℕ} (hN : 1 ≤ N) :
    Measurable (fun X : Config d N => etaE m X (volume : Measure (Torus d))) := by
  have hm' : (d : ℝ) < 2 * m := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have := measurable_ofMeasureDiff_empirical (N := N) hm' (volume : Measure (Torus d)) hN
  unfold etaE flucE
  exact this.const_smul (Real.sqrt (N : ℝ))

theorem s16f_meas_W (m : ℝ) (hm : (d : ℝ) / 2 < m) (k : NonzeroLattice d) {N : ℕ} (hN : 1 ≤ N) :
    Measurable (fun X : Config d N => s7_modePair m k (etaE m X (volume : Measure (Torus d)))) := by
  obtain ⟨π, hπ, -⟩ := HRS.MC.Sec7.S16d.s7_S16d_modePair_clm_proof d m k
  have : (fun X : Config d N => s7_modePair m k (etaE m X (volume : Measure (Torus d)))) =
      fun X => π (etaE m X (volume : Measure (Torus d))) := by
    funext X; rw [hπ]
  rw [this]
  exact π.continuous.measurable.comp (s16f_meas_eta hd hs0 hs hβ m hm hN)

/-- density bound of `f_N` w.r.t. `Q_N` (all `N`) -/
theorem s16f_rn (m : ℝ) (hm : (d : ℝ) / 2 < m) (k : NonzeroLattice d) {a : ℝ} (ha : 0 ≤ a) (N : ℕ) :
    s7_tiltedLaw d s β N m k (s16f_θ a) ≪
        modulatedGibbs (periodicRiesz d s) N β (volume : Measure (Torus d)) ∧
      ∀ᵐ X ∂(modulatedGibbs (periodicRiesz d s) N β (volume : Measure (Torus d))),
        (s7_tiltedLaw d s β N m k (s16f_θ a)).rnDeriv
          (modulatedGibbs (periodicRiesz d s) N β (volume : Measure (Torus d))) X ≤
          ENNReal.ofReal (2 + a) := by
  haveI := s16f_Q_prob hd hs0 hs hβ N
  have hmd : (d : ℝ) < 2 * m := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hWm := HRS.MC.Sec7.S16b.s7b_W_meas (N := N) hmd k
  exact s16f_tilt_rn (modulatedGibbs (periodicRiesz d s) N β (volume : Measure (Torus d)))
    (g := fun X : Config d N => s16f_θ a (‖s7_modePair m k (etaE m X volume)‖ ^ 2))
    ((s16f_θ_meas a).comp hWm) (fun X => s16f_θ_ge ha _) (M := 2 + a) (fun X => s16f_θ_le ha _)

/-- the integral formula for `E_{f_N} F(eta_N)` -/
theorem s16f_int_f (m : ℝ) (hm : (d : ℝ) / 2 < m) (k : NonzeroLattice d) {a : ℝ} (ha : 0 ≤ a)
    {N : ℕ} (hN : 1 ≤ N) {F : NegSobolev d m → ℝ} (hFc : Continuous F) {K : ℝ}
    (hK : ∀ y, |F y| ≤ K) :
    ∫ X, F (etaE m X volume) ∂(s7_tiltedLaw d s β N m k (s16f_θ a)) =
      ((∫ X, F (etaE m X volume) ∂(modulatedGibbs (periodicRiesz d s) N β (volume : Measure (Torus d)))) +
        (1 + a) * ∫ X, (s16f_Φ m k (etaE m X volume) * F (etaE m X volume))
          ∂(modulatedGibbs (periodicRiesz d s) N β (volume : Measure (Torus d)))) /
      (1 + (1 + a) * ∫ X, s16f_Φ m k (etaE m X volume)
          ∂(modulatedGibbs (periodicRiesz d s) N β (volume : Measure (Torus d)))) := by
  haveI := s16f_Q_prob hd hs0 hs hβ N
  set Q := modulatedGibbs (periodicRiesz d s) N β (volume : Measure (Torus d)) with hQ
  have hmd : (d : ℝ) < 2 * m := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hWm := HRS.MC.Sec7.S16b.s7b_W_meas (N := N) hmd k
  have hηm := s16f_meas_eta hd hs0 hs hβ m hm hN
  have hΦ : Continuous (s16f_Φ m k) := s16f_Φ_cont m k
  have hg : ∀ X : Config d N, s16f_θ a (‖s7_modePair m k (etaE m X volume)‖ ^ 2) =
      1 + (1 + a) * s16f_Φ m k (etaE m X volume) := fun X => s16f_θ_sq a _
  have hFi : Integrable (fun X : Config d N => F (etaE m X volume)) Q :=
    Integrable.of_bound (hFc.measurable.comp hηm).aestronglyMeasurable K
      (ae_of_all _ fun X => by rw [Real.norm_eq_abs]; exact hK _)
  have hΦi : Integrable (fun X : Config d N => s16f_Φ m k (etaE m X volume)) Q :=
    Integrable.of_bound (hΦ.measurable.comp hηm).aestronglyMeasurable 1
      (ae_of_all _ fun X => by
        rw [Real.norm_eq_abs, abs_of_pos (s16f_Φ_pos m k _)]; exact s16f_Φ_le_one m k _)
  have hΦFi : Integrable (fun X : Config d N => s16f_Φ m k (etaE m X volume) * F (etaE m X volume)) Q := by
    refine Integrable.of_bound ((hΦ.measurable.comp hηm).mul (hFc.measurable.comp hηm)).aestronglyMeasurable K
      (ae_of_all _ fun X => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (s16f_Φ_pos m k _)]
    calc s16f_Φ m k (etaE m X volume) * |F (etaE m X volume)| ≤ 1 * K :=
          mul_le_mul (s16f_Φ_le_one m k _) (hK _) (abs_nonneg _) zero_le_one
      _ = K := one_mul K
  have key := s16f_tilt_integral Q
    (g := fun X : Config d N => s16f_θ a (‖s7_modePair m k (etaE m X volume)‖ ^ 2))
    ((s16f_θ_meas a).comp hWm) (fun X => s16f_θ_ge ha _) (M := 2 + a) (fun X => s16f_θ_le ha _)
    (F := fun X => F (etaE m X volume)) hFi
  have e : s7_tiltedLaw d s β N m k (s16f_θ a) = s16f_tilt Q
      (fun X : Config d N => s16f_θ a (‖s7_modePair m k (etaE m X volume)‖ ^ 2)) := rfl
  rw [e, key]
  simp_rw [hg]
  have e1 : ∫ X, (1 + (1 + a) * s16f_Φ m k (etaE m X volume)) * F (etaE m X volume) ∂Q =
      (∫ X, F (etaE m X volume) ∂Q) +
        (1 + a) * ∫ X, s16f_Φ m k (etaE m X volume) * F (etaE m X volume) ∂Q := by
    have : ∀ X : Config d N, (1 + (1 + a) * s16f_Φ m k (etaE m X volume)) * F (etaE m X volume) =
        F (etaE m X volume) + (1 + a) * (s16f_Φ m k (etaE m X volume) * F (etaE m X volume)) :=
      fun X => by ring
    simp_rw [this]
    rw [integral_add hFi (hΦFi.const_mul _), integral_const_mul]
  have e2 : ∫ X, (1 + (1 + a) * s16f_Φ m k (etaE m X volume)) ∂Q =
      1 + (1 + a) * ∫ X, s16f_Φ m k (etaE m X volume) ∂Q := by
    rw [integral_add (integrable_const _) (hΦi.const_mul _), integral_const_mul]
    simp
  rw [e1, e2]

end Gibbs

end HRS.MC.Sec7.S16f

end
