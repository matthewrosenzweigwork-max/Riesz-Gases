import HRS.MS.S81pReturn
import HRS.MS.S81pSeriesGauss
import HRS.MS.SpecAux66
import HRS.Sections.Q41Aux8

/-!
# S8.1 (worker S81P): the initial Gaussian block of the burn-in coupling

Namespace `HRS.Whole.S81P`, prefix `s81p_`.

On `Ω₀ = ℕ → ℝ` with the product measure `∏_l N(0, β⁻¹)` (`Measure.infinitePi`), put `z_l = e^{-(u-b+τ/2)ω_l} γ_l` (an `ℓ²` vector a.s.) and
`G₀(t) = R(z)(t)` with `R` the return map of S8.8 (`s81p_return_clm`).  Then `G₀` has the Gaussian finite-dimensional laws with covariance
profile `Q_{αα'}(2u + t + t')` (the initial susceptibility covariance transported by the orbit, `s81w2_susc_orbit`), positive semidefinite
covariance matrices, and `‖G₀‖_{L²(𝒳_T)} ≤ K e^{-ω₀ u}` (`ω₀ = ω_0 > 0` the first eigenvalue).
-/

set_option autoImplicit false
set_option maxRecDepth 4000

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators RealInnerProductSpace
open HRS HRS.Whole HRS.MS.SuppU11 HRS.Whole.S81W2

namespace HRS.Whole.S81P

/-- The weighted `ℓ²` vector `z_l = w_l γ_l` (junk `0` off the null set where the series diverges). -/
def s81p_zinit (w : ℕ → ℝ) (γ : ℕ → ℝ) : SeqL2 := SeqL2.ofSeq fun l => w l * γ l

theorem s81p_zinit_coord {w γ : ℕ → ℝ} (h : Summable fun l => (w l * γ l) ^ 2) (l : ℕ) :
    SeqL2.coord (s81p_zinit w γ) l = w l * γ l :=
  u11_coord_ofSeq (memℓp_two_iff.2 h) l

theorem s81p_zinit_measurable (w : ℕ → ℝ) : Measurable (s81p_zinit w) := by
  classical
  have hf : ∀ l : ℕ, Measurable (fun γ : ℕ → ℝ => (w l * γ l) ^ 2) := fun l =>
    (measurable_const.mul (measurable_pi_apply l)).pow_const 2
  have hSm : MeasurableSet {γ : ℕ → ℝ | Summable fun l => (w l * γ l) ^ 2} :=
    HRS.Q41.q41_measurableSet_summable (fun (l : ℕ) (γ : ℕ → ℝ) => (w l * γ l) ^ 2) hf
      (fun l γ => sq_nonneg _)
  refine HRS.measurable_of_inner_basis S45.s45_seqBasis fun i => ?_
  have e : (fun γ : ℕ → ℝ => inner ℝ (S45.s45_seqBasis i) (s81p_zinit w γ)) =
      fun γ => if Summable (fun l => (w l * γ l) ^ 2) then w i * γ i else 0 := by
    funext γ
    have hb := S45.s45_inner_seqBasis i (s81p_zinit w γ)
    refine hb.trans ?_
    by_cases hs : Summable fun l => (w l * γ l) ^ 2
    · rw [if_pos hs, s81p_zinit_coord hs]
    · rw [if_neg hs]
      have : ¬ Memℓp (fun l => w l * γ l) 2 := fun h => hs (memℓp_two_iff.1 h)
      have h0 : s81p_zinit w γ = 0 := by unfold s81p_zinit SeqL2.ofSeq; exact dif_neg this
      rw [h0]
      rfl
  rw [e]
  exact Measurable.ite hSm (measurable_const.mul (measurable_pi_apply i)) measurable_const

/-- The product Gaussian measure `∏_l N(0, ν)` on `ℕ → ℝ`. -/
def s81p_gamma (ν : ℝ≥0) : Measure (ℕ → ℝ) := Measure.infinitePi fun _ : ℕ => gaussianReal 0 ν

instance (ν : ℝ≥0) : IsProbabilityMeasure (s81p_gamma ν) := by
  unfold s81p_gamma; infer_instance

theorem s81p_gamma_sq_lintegral (ν : ℝ≥0) (c : ℝ) (l : ℕ) :
    ∫⁻ γ, ENNReal.ofReal ((c * γ l) ^ 2) ∂(s81p_gamma ν) = ENNReal.ofReal (c ^ 2 * ν) := by
  have hm : Measurable fun γ : ℕ → ℝ => γ l := measurable_pi_apply l
  have h1 : ∫⁻ γ, ENNReal.ofReal ((c * γ l) ^ 2) ∂(s81p_gamma ν) =
      ∫⁻ x, ENNReal.ofReal ((c * x) ^ 2) ∂(gaussianReal 0 ν) := by
    have := lintegral_map (μ := s81p_gamma ν) (f := fun x : ℝ => ENNReal.ofReal ((c * x) ^ 2))
      (by fun_prop) hm
    rw [← this]
    unfold s81p_gamma
    rw [Measure.infinitePi_map_eval]
  rw [h1]
  have hint : Integrable (fun x : ℝ => (c * x) ^ 2) (gaussianReal 0 ν) := by
    have := (IsGaussian.memLp_two_id (μ := gaussianReal 0 ν)).integrable_sq
    simpa [mul_pow] using this.const_mul (c ^ 2)
  rw [← ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun x => sq_nonneg _)]
  congr 1
  simp only [mul_pow]
  rw [integral_const_mul]
  have := HRS.integral_sq_gaussianReal_zero ν
  rw [this]

theorem s81p_summable_of_tsum_ne_top {f : ℕ → ℝ} (hnn : ∀ l, 0 ≤ f l)
    (h : ∑' l, ENNReal.ofReal (f l) ≠ ⊤) : Summable f := by
  have e : ∀ l, ENNReal.ofReal (f l) = (((f l).toNNReal : ℝ≥0) : ℝ≥0∞) := fun l => rfl
  simp_rw [e] at h
  rw [ENNReal.tsum_coe_ne_top_iff_summable, ← NNReal.summable_coe] at h
  simpa [Real.coe_toNNReal _ (hnn _)] using h

theorem s81p_zinit_ae {w : ℕ → ℝ} (ν : ℝ≥0) (hw : Summable fun l => w l ^ 2) :
    ∀ᵐ γ ∂(s81p_gamma ν), Summable fun l => (w l * γ l) ^ 2 := by
  have hmf : ∀ l, Measurable (fun γ : ℕ → ℝ => ENNReal.ofReal ((w l * γ l) ^ 2)) := fun l =>
    ENNReal.measurable_ofReal.comp ((measurable_const.mul (measurable_pi_apply l)).pow_const 2)
  have hfin : ∫⁻ γ, ∑' l, ENNReal.ofReal ((w l * γ l) ^ 2) ∂(s81p_gamma ν) ≠ ⊤ := by
    rw [lintegral_tsum fun l => (hmf l).aemeasurable]
    simp_rw [s81p_gamma_sq_lintegral]
    rw [← ENNReal.ofReal_tsum_of_nonneg (f := fun l => w l ^ 2 * (ν : ℝ))
      (fun l => mul_nonneg (sq_nonneg _) ν.2) (hw.mul_right _)]
    exact ENNReal.ofReal_ne_top
  have hae := ae_lt_top' (Measurable.ennreal_tsum hmf).aemeasurable hfin
  filter_upwards [hae] with γ hγ
  exact s81p_summable_of_tsum_ne_top (fun l => sq_nonneg _) hγ.ne

/-- `E ‖z‖² = ν ∑ w_l²`. -/
theorem s81p_zinit_L2 {w : ℕ → ℝ} (ν : ℝ≥0) (hw : Summable fun l => w l ^ 2) :
    ∫⁻ γ, ENNReal.ofReal (‖s81p_zinit w γ‖ ^ 2) ∂(s81p_gamma ν) = ENNReal.ofReal (ν * ∑' l, w l ^ 2) := by
  have hmf : ∀ l, Measurable (fun γ : ℕ → ℝ => ENNReal.ofReal ((w l * γ l) ^ 2)) := fun l =>
    ENNReal.measurable_ofReal.comp ((measurable_const.mul (measurable_pi_apply l)).pow_const 2)
  have h1 : ∫⁻ γ, ENNReal.ofReal (‖s81p_zinit w γ‖ ^ 2) ∂(s81p_gamma ν) =
      ∫⁻ γ, ∑' l, ENNReal.ofReal ((w l * γ l) ^ 2) ∂(s81p_gamma ν) := by
    refine lintegral_congr_ae ?_
    filter_upwards [s81p_zinit_ae ν hw] with γ hγ
    have hz : ‖s81p_zinit w γ‖ ^ 2 = ∑' l, (w l * γ l) ^ 2 := by
      rw [← u11_norm_sq]
      exact tsum_congr fun l => by rw [s81p_zinit_coord hγ]
    rw [hz, ENNReal.ofReal_tsum_of_nonneg (fun l => sq_nonneg _) hγ]
  rw [h1, lintegral_tsum fun l => (hmf l).aemeasurable]
  simp_rw [s81p_gamma_sq_lintegral]
  rw [← ENNReal.ofReal_tsum_of_nonneg (f := fun l => w l ^ 2 * (ν : ℝ))
    (fun l => mul_nonneg (sq_nonneg _) ν.2) (hw.mul_right _), tsum_mul_right, mul_comm]

/-- The path process of an element of `𝒳_T`, extended by `0` outside `[0,T]`. -/
def s81p_pathProc {d : ℕ} {m T : ℝ} (w : OscPath d m T) (t : ℝ) : OscDual d m :=
  if h : t ∈ Icc (0 : ℝ) T then OscPath.at' w ⟨t, h⟩ else 0

theorem s81p_pathProc_cont {d : ℕ} {m T : ℝ} (w : OscPath d m T) :
    ContinuousOn (fun t => s81p_pathProc w t) (Icc 0 T) := by
  rw [continuousOn_iff_continuous_restrict]
  have hcw : Continuous fun t : Icc (0 : ℝ) T => OscPath.at' w t :=
    (show C(Icc (0 : ℝ) T, OscDual d m) from w).continuous
  refine hcw.congr fun t => ?_
  simp only [Set.restrict_apply, s81p_pathProc, dif_pos t.2]

theorem s81p_pathProc_win {d : ℕ} {m T : ℝ} (w : OscPath d m T) :
    processWindow m T 0 (fun t (_ : Unit) => s81p_pathProc w t) () = w := by
  unfold processWindow
  refine s81p_win_ext fun t => ?_
  rw [s81p_win_apply (s81p_pathProc_cont w)]
  simp only [s81p_pathProc, dif_pos t.2]

theorem s81p_pathProc_measurable {d : ℕ} {m T : ℝ} {Ω : Type*} [MeasurableSpace Ω] {w : Ω → OscPath d m T}
    (hw : Measurable w) (t : ℝ) : Measurable fun ω => s81p_pathProc (w ω) t := by
  unfold s81p_pathProc
  by_cases h : t ∈ Icc (0 : ℝ) T
  · simp only [h, dite_true]
    have hev : Measurable fun x : OscPath d m T => OscPath.at' x ⟨t, h⟩ :=
      (ContinuousMap.measurable_eval (⟨t, h⟩ : Icc (0 : ℝ) T) :
        Measurable fun f : C(Icc (0 : ℝ) T, OscDual d m) => f ⟨t, h⟩)
    exact hev.comp hw
  · simp only [h, dite_false]
    exact measurable_const

section Block

variable {d : ℕ}

/-- **The initial Gaussian block.** -/
theorem s81p_initial_block (hd : 2 ≤ d) (a β : ℝ) (ha : 0 < a) (hβ : 0 < β) (ρβ : Euc d → ℝ)
    (hρ : IsThermalEquilibrium d ((d : ℝ) / 2) a β ρβ) (e : ℕ → Euc d → ℝ) (om : ℕ → ℝ)
    (hdata : IsSpectralData d β ρβ e om) (t₀ : ℝ) (ht₀ : 0 < t₀) (C4 : ℝ)
    (hL4 : ∀ l, eLpNorm (fun x => ‖gradient (e l) x‖) 4 (withDensityReal ρβ) ≤
      ENNReal.ofReal (C4 * Real.exp (t₀ * om l)))
    (τ : ℝ) (hτ : 4 * t₀ < τ) (b : ℝ) (hb : τ / 2 + 1 < b) (m : ℝ)
    (hm : (wholeSpaceIndex d : ℝ) ≤ m) (T : ℝ) (hT : 0 < T) :
    ∃ K ω₀ : ℝ, 0 < ω₀ ∧ ∀ u : ℝ, b ≤ u →
      ∃ G₀ : ℝ → (ℕ → ℝ) → OscDual d m, S81PProc (s81p_gamma (β⁻¹).toNNReal) T G₀ ∧
        (∀ (p : ℕ) (ts : Fin p → ℝ) (αs : Fin p → MultiIndex d), (∀ c, ts c ∈ Icc (0 : ℝ) T) →
          (s81p_gamma (β⁻¹).toNNReal).map (s81p_vec G₀ ts αs) = multivariateGaussian 0
            (Matrix.of fun i j => s81w2_Q d β ρβ e om m (αs i) (αs j) (2 * u + ts i + ts j))) ∧
        (∀ (p : ℕ) (ts : Fin p → ℝ) (αs : Fin p → MultiIndex d), (∀ c, ts c ∈ Icc (0 : ℝ) T) →
          (Matrix.of fun i j => s81w2_Q d β ρβ e om m (αs i) (αs j) (2 * u + ts i + ts j)).PosSemidef) ∧
        s81p_L2 (s81p_gamma (β⁻¹).toNNReal) (processWindow m T 0 G₀) ≤
          ENNReal.ofReal (K * Real.exp (-ω₀ * u)) := by
  classical
  obtain ⟨R, hR⟩ := s81p_return_clm hd a β ha hβ ρβ hρ e om hdata t₀ ht₀ C4 hL4 τ hτ b hb m hm T hT
  obtain ⟨c0, hc0, hgrowth⟩ := hdata.growth
  have hd1 : 1 ≤ d := by omega
  have hom : ∀ l, 0 < om l := hdata.pos
  have hmono : Monotone om := hdata.mono
  have hτ0 : 0 < τ := by linarith
  set ν : ℝ≥0 := (β⁻¹).toNNReal with hν
  have hνr : (ν : ℝ) = β⁻¹ := Real.coe_toNNReal _ (inv_nonneg.2 hβ.le)
  set Sτ : ℝ := ∑' l, Real.exp (-τ * om l) with hSτ
  have hsτ : Summable fun l => Real.exp (-τ * om l) := HRS.MS.Spec.s8p_summable_exp_growth hd1 hc0 hgrowth hτ0
  refine ⟨‖R‖ * Real.sqrt (ν * Sτ) * Real.exp (b * om 0), om 0, hom 0, fun u hu => ?_⟩
  set w : ℕ → ℝ := fun l => Real.exp (-(u - b + τ / 2) * om l) with hw
  have hκ : 0 < 2 * (u - b) + τ := by linarith
  have hwsq : ∀ l, w l ^ 2 = Real.exp (-(2 * (u - b) + τ) * om l) := fun l => by
    simp only [hw]
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hwsum : Summable fun l => w l ^ 2 := by
    simp_rw [hwsq]
    exact HRS.MS.Spec.s8p_summable_exp_growth hd1 hc0 hgrowth hκ
  set z : (ℕ → ℝ) → SeqL2 := s81p_zinit w with hz
  have hzm : Measurable z := s81p_zinit_measurable w
  set G₀ : ℝ → (ℕ → ℝ) → OscDual d m := fun t γ => s81p_pathProc (R (z γ)) t with hG₀
  have hRz : Measurable fun γ => R (z γ) := R.continuous.measurable.comp hzm
  have hmeasG : ∀ t, Measurable (G₀ t) := fun t => s81p_pathProc_measurable hRz t
  have hwin : ∀ γ, processWindow m T 0 G₀ γ = R (z γ) := fun γ => s81p_pathProc_win (R (z γ))
  -- coefficient data
  obtain ⟨Cb, hCb⟩ := return_map_bounded_proof hd a β ha hβ ρβ hρ e om hdata t₀ ht₀ C4 hL4 τ hτ b hb m
    hm T hT
  obtain ⟨B, hB, hB0, hbes⟩ := u11_coef_bessel hd ha hβ hρ hdata.centered hdata.orth hm
  have hcsum : ∀ α : MultiIndex d, Summable fun l => u11Coef d β ρβ e m α l ^ 2 := fun α =>
    summable_of_sum_le (fun l => sq_nonneg _) (hbes α)
  have hb0 : 0 < b := by linarith
  have hfdd_aux : ∀ (p : ℕ) (ts : Fin p → ℝ) (αs : Fin p → MultiIndex d), (∀ c, ts c ∈ Icc (0 : ℝ) T) →
      (∀ a, 0 ≤ u + ts a) ∧
      (∀ a, Summable fun l => (u11Coef d β ρβ e m (αs a) l * Real.exp (-(u + ts a) * om l)) ^ 2 * (ν : ℝ)) := by
    intro p ts αs hts
    have hnn : ∀ a, 0 ≤ u + ts a := fun a => by linarith [(hts a).1]
    refine ⟨fun a => hnn a, fun a => ?_⟩
    refine Summable.of_nonneg_of_le (fun l => mul_nonneg (sq_nonneg _) ν.2) (fun l => ?_)
      ((hcsum (αs a)).mul_right (ν : ℝ))
    refine mul_le_mul_of_nonneg_right ?_ ν.2
    rw [mul_pow]
    have h1 : Real.exp (-(u + ts a) * om l) ^ 2 ≤ 1 := by
      have : Real.exp (-(u + ts a) * om l) ≤ 1 := by
        rw [Real.exp_le_one_iff]; nlinarith [hom l, hnn a]
      nlinarith [Real.exp_pos (-(u + ts a) * om l)]
    nlinarith [sq_nonneg (u11Coef d β ρβ e m (αs a) l)]
  have hmat : ∀ (p : ℕ) (ts : Fin p → ℝ) (αs : Fin p → MultiIndex d), (∀ c, ts c ∈ Icc (0 : ℝ) T) →
      s81p_seriesCov (fun a l => u11Coef d β ρβ e m (αs a) l * Real.exp (-(u + ts a) * om l))
        (fun _ => ν) = Matrix.of fun i j =>
          s81w2_Q d β ρβ e om m (αs i) (αs j) (2 * u + ts i + ts j) := by
    intro p ts αs hts
    ext i j
    simp only [s81p_seriesCov, Matrix.of_apply, s81w2_Q, hνr]
    rw [← tsum_mul_left]
    refine tsum_congr fun l => ?_
    have : Real.exp (-(2 * u + ts i + ts j) * om l) =
        Real.exp (-(u + ts i) * om l) * Real.exp (-(u + ts j) * om l) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [this]; ring
  have hpsd : ∀ (p : ℕ) (ts : Fin p → ℝ) (αs : Fin p → MultiIndex d), (∀ c, ts c ∈ Icc (0 : ℝ) T) →
      (Matrix.of fun i j => s81w2_Q d β ρβ e om m (αs i) (αs j) (2 * u + ts i + ts j)).PosSemidef := by
    intro p ts αs hts
    rw [← hmat p ts αs hts]
    exact s81p_seriesCov_psd (hfdd_aux p ts αs hts).2
  refine ⟨G₀, ⟨hmeasG, Eventually.of_forall fun γ => s81p_pathProc_cont (R (z γ))⟩, ?_, hpsd, ?_⟩
  · intro p ts αs hts
    rw [← hmat p ts αs hts]
    have hind : iIndepFun (fun (l : ℕ) (γ : ℕ → ℝ) => γ l) (s81p_gamma ν) := by
      unfold s81p_gamma
      exact iIndepFun_infinitePi (P := fun _ : ℕ => gaussianReal 0 ν) (X := fun _ (x : ℝ) => x)
        (fun _ => measurable_id)
    have hlaw : ∀ l, HasLaw (fun γ : ℕ → ℝ => γ l) (gaussianReal 0 ν) (s81p_gamma ν) := fun l =>
      ⟨(measurable_pi_apply l).aemeasurable, by unfold s81p_gamma; exact Measure.infinitePi_map_eval _ l⟩
    refine s81p_series_gaussian (s81p_gamma ν) (fun l γ => γ l) (fun l => measurable_pi_apply l)
      (fun _ => ν) hind hlaw _ (hfdd_aux p ts αs hts).2 _ (s81p_vec_meas hmeasG ts αs) ?_
    filter_upwards [s81p_zinit_ae ν hwsum] with γ hγ a
    have hta := hts a
    have hG : G₀ (ts a) γ = returnMapW d β ρβ e om m τ b (z γ) (ts a) := by
      simp only [hG₀, s81p_pathProc, dif_pos hta]
      exact hR (z γ) ⟨ts a, hta⟩
    obtain ⟨hs, hmem⟩ := (hCb (z γ)).1 (ts a) hta
    have hco : OscDual.coord (G₀ (ts a) γ) (αs a) =
        ∑' l, u11Coef d β ρβ e m (αs a) l * Real.exp (-(b + ts a - τ / 2) * om l) *
          SeqL2.coord (z γ) l := by
      rw [hG]
      unfold returnMapW
      exact HRS.MS.CovMeas.s101_ellVec_coord hmem (αs a)
    show HasSum _ (OscDual.coord (G₀ (ts a) γ) (αs a))
    rw [hco]
    have hs' := hs (αs a)
    have heq : (fun l => u11Coef d β ρβ e m (αs a) l * Real.exp (-(u + ts a) * om l) * γ l) =
        fun l => u11Coef d β ρβ e m (αs a) l * Real.exp (-(b + ts a - τ / 2) * om l) *
          SeqL2.coord (z γ) l := by
      funext l
      rw [hz, s81p_zinit_coord hγ l, hw]
      simp only
      have : Real.exp (-(u + ts a) * om l) = Real.exp (-(b + ts a - τ / 2) * om l) *
          Real.exp (-(u - b + τ / 2) * om l) := by
        rw [← Real.exp_add]; congr 1; ring
      rw [this]; ring
    rw [heq]
    exact hs'.hasSum
  · -- the `L²` bound
    have hL2 : s81p_L2 (s81p_gamma ν) (processWindow m T 0 G₀) ≤
        ENNReal.ofReal (‖R‖ * Real.sqrt (ν * ∑' l, w l ^ 2)) := by
      unfold s81p_L2
      have hX : 0 ≤ (ν : ℝ) * ∑' l, w l ^ 2 := mul_nonneg ν.2 (tsum_nonneg fun l => sq_nonneg _)
      calc (∫⁻ γ, ENNReal.ofReal (‖processWindow m T 0 G₀ γ‖ ^ (2 : ℝ)) ∂(s81p_gamma ν)) ^ (1 / (2 : ℝ))
          ≤ (∫⁻ γ, ENNReal.ofReal (‖R‖ ^ 2 * ‖z γ‖ ^ 2) ∂(s81p_gamma ν)) ^ (1 / (2 : ℝ)) := by
            refine ENNReal.rpow_le_rpow (lintegral_mono fun γ => ENNReal.ofReal_le_ofReal ?_)
              (by norm_num)
            rw [hwin, Real.rpow_two, ← mul_pow]
            exact pow_le_pow_left₀ (norm_nonneg _) (R.le_opNorm _) 2
        _ = (ENNReal.ofReal (‖R‖ ^ 2) * ∫⁻ γ, ENNReal.ofReal (‖z γ‖ ^ 2) ∂(s81p_gamma ν)) ^ (1 / (2 : ℝ)) := by
            congr 1
            simp_rw [ENNReal.ofReal_mul (sq_nonneg ‖R‖)]
            rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        _ = ENNReal.ofReal (‖R‖ * Real.sqrt (ν * ∑' l, w l ^ 2)) := by
            rw [s81p_zinit_L2 ν hwsum, ← ENNReal.ofReal_mul (sq_nonneg _),
              ENNReal.ofReal_rpow_of_nonneg (mul_nonneg (sq_nonneg _) hX) (by norm_num),
              ← Real.sqrt_eq_rpow, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (norm_nonneg _)]
    refine hL2.trans (ENNReal.ofReal_le_ofReal ?_)
    -- `∑ w² ≤ e^{-2(u-b)ω₀} Sτ`
    have hle : ∑' l, w l ^ 2 ≤ Real.exp (-(2 * (u - b)) * om 0) * Sτ := by
      rw [hSτ, ← tsum_mul_left]
      refine hwsum.tsum_le_tsum (fun l => ?_) (hsτ.mul_left _)
      rw [hwsq, show -(2 * (u - b) + τ) * om l = -(2 * (u - b)) * om l + -τ * om l by ring,
        Real.exp_add]
      refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
      rw [Real.exp_le_exp]
      have := hmono (Nat.zero_le l)
      nlinarith [hu]
    have hS0 : 0 ≤ Sτ := tsum_nonneg fun l => (Real.exp_pos _).le
    have hsq : Real.sqrt (ν * ∑' l, w l ^ 2) ≤ Real.sqrt (ν * Sτ) * Real.exp (-(u - b) * om 0) := by
      calc Real.sqrt (ν * ∑' l, w l ^ 2) ≤ Real.sqrt (ν * (Real.exp (-(2 * (u - b)) * om 0) * Sτ)) :=
            Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hle ν.2)
        _ = Real.sqrt (ν * Sτ) * Real.exp (-(u - b) * om 0) := by
            rw [show (ν : ℝ) * (Real.exp (-(2 * (u - b)) * om 0) * Sτ) =
              (ν * Sτ) * (Real.exp (-(u - b) * om 0)) ^ 2 by
                rw [← Real.exp_nat_mul]; push_cast
                rw [show (-(2 * (u - b)) * om 0 : ℝ) = 2 * (-(u - b) * om 0) by ring]; ring,
              Real.sqrt_mul (mul_nonneg (NNReal.coe_nonneg ν) hS0), Real.sqrt_sq (Real.exp_pos _).le]
    calc ‖R‖ * Real.sqrt (ν * ∑' l, w l ^ 2)
        ≤ ‖R‖ * (Real.sqrt (ν * Sτ) * Real.exp (-(u - b) * om 0)) :=
          mul_le_mul_of_nonneg_left hsq (norm_nonneg _)
      _ = ‖R‖ * Real.sqrt (ν * Sτ) * Real.exp (b * om 0) * Real.exp (-om 0 * u) := by
          have hex : Real.exp (-(u - b) * om 0) = Real.exp (b * om 0) * Real.exp (-om 0 * u) := by
            rw [← Real.exp_add]; congr 1; ring
          rw [hex]; ring

end Block

end HRS.Whole.S81P
