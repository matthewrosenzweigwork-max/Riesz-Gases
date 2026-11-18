/-
# HRS.Equilibrium.RepulsiveL2 — package REP-05: `L²` smallness of a band and the norm fields (M3)

`∫_{𝕋^d} heatBand d a b ² dx = ∑_k bandCoeff d a b k ²` (Parseval), and for `0 < a ≤ b ≤ 1/2`
the weighted Cauchy-Schwarz inequality in heat time

  `c_k² ≤ A² (∫_0^b t^{d/4-1} dt) (∫_0^b t^{3d/4-1} e^{-2t|k|²} dt)`,  `k ≠ 0`,

summed with Tonelli and the heat-trace bound `∑_{k≠0} e^{-2t|k|²} ≤ (π/2t)^{d/2} Θ_d`, gives
`∫ heatBand² ≤ l2Const d · b^{d/2}` uniformly in `a`.  Against `μ = ρ dx`, `ρ ≤ Λ`, the row
integrals of `W(x,y) = 2β heatBand(x - y)` are `≤ 4β² Λ l2Const d b^{d/2}`, and the generic
`DGRHS.Gaussian.ae_row_sq_hoeffdingCentered_le` / `integral_sq_hoeffdingCentered_le` /
`DGRHS.Kernel.norm_integralOperator_le` turn this into the three norm fields of
`MasterCutoffData` (DGR `lem:logBandL2`, Euclidean Lean `gaussianLogMasterBand_norm_fields`).

`sorry`-ed specifications; see `docs/REPULSIVE_PLAN.md` (REP-05).
-/
import HRS.Equilibrium.RepulsiveBridge
import HRS.Equilibrium.RepulsiveBand

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS

namespace Repulsive

variable {d : ℕ}

/-! ### Parseval -/

/-- A continuous real function on a compact space is in `L²` of every finite measure. -/
theorem memLp_two_of_continuous_repulsive {X : Type*} [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] [OpensMeasurableSpace X] [SecondCountableTopology X]
    {ν : Measure X} [IsFiniteMeasure ν] {f : X → ℝ}
    (hf : Continuous f) : MemLp f 2 ν := by
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hf.continuousOn
  exact MemLp.of_bound hf.aestronglyMeasurable C (ae_of_all _ fun x => hC x (Set.mem_univ _))

theorem memLp_two_heatBand (hd : 2 ≤ d) {a b : ℝ} (ha : 0 < a) :
    MemLp (heatBand d a b) 2 (volume : Measure (Torus d)) :=
  memLp_two_of_continuous_repulsive (continuous_heatBand hd ha)

/-- `∫ heatBand² = ∑_k c_k²` (`Torus.parseval_realCoeff`; the coefficient of `√2 cos` on the
positive half-lattice is `√2 c_k`, that of `√2 sin` on the negative half is `0`, and `c_k = c_{-k}`). -/
theorem integral_sq_heatBand_eq (hd : 2 ≤ d) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∫ x, heatBand d a b x ^ 2 = ∑' k : Lattice d, bandCoeff d a b k ^ 2 := by
  have hφ : MemLp (heatBand d a b) 2 (volume : Measure (Torus d)) := memLp_two_heatBand hd ha
  have hφ1 : Integrable (heatBand d a b) (volume : Measure (Torus d)) := hφ.integrable one_le_two
  have hc0 : ∀ j, 0 ≤ bandCoeff d a b j := fun j => bandCoeff_nonneg hd ha.le hab j
  have hcos : ∀ j (x : Torus d), ((Torus.cosMode j x : ℝ) : ℂ) =
      (Torus.mode j x + Torus.mode (-j) x) / 2 := by
    intro j x
    rw [Torus.mode_neg]
    exact Complex.re_eq_add_conj _
  -- the Fourier coefficient `∫ e_{-n} φ` of the band is its lattice coefficient `c_n`
  have hcoef : ∀ n : Lattice d, ∫ x, Torus.mode (-n) x * ((heatBand d a b x : ℝ) : ℂ) =
      ((bandCoeff d a b n : ℝ) : ℂ) := by
    intro n
    have hint : ∀ j : Lattice d, Integrable (fun x : Torus d =>
        Torus.mode (-n) x * ((bandCoeff d a b j * Torus.cosMode j x : ℝ) : ℂ)) := fun j =>
      ((Torus.continuous_mode (-n)).mul (Complex.continuous_ofReal.comp
        (continuous_const.mul (Torus.continuous_cosMode j)))).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    have hbd : ∀ j : Lattice d, ∫ x, ‖Torus.mode (-n) x * ((bandCoeff d a b j * Torus.cosMode j x : ℝ) : ℂ)‖
        ≤ bandCoeff d a b j := fun j => by
      calc ∫ x, ‖Torus.mode (-n) x * ((bandCoeff d a b j * Torus.cosMode j x : ℝ) : ℂ)‖
          ≤ ∫ _x : Torus d, bandCoeff d a b j := by
            refine integral_mono (hint j).norm (integrable_const _) fun x => ?_
            rw [norm_mul, Torus.norm_mode, one_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul,
              abs_of_nonneg (hc0 j)]
            exact mul_le_of_le_one_right (hc0 j) (HRS.abs_cosMode_le j x)
        _ = bandCoeff d a b j := by simp
    have hFsum : Summable (fun j : Lattice d =>
        ∫ x, ‖Torus.mode (-n) x * ((bandCoeff d a b j * Torus.cosMode j x : ℝ) : ℂ)‖) :=
      Summable.of_nonneg_of_le (fun j => integral_nonneg fun x => norm_nonneg _) hbd
        (summable_bandCoeff hd ha hab)
    have hexp : (fun x : Torus d => Torus.mode (-n) x * ((heatBand d a b x : ℝ) : ℂ)) =
        fun x => ∑' j : Lattice d,
          Torus.mode (-n) x * ((bandCoeff d a b j * Torus.cosMode j x : ℝ) : ℂ) := by
      funext x
      rw [heatBand_eq_tsum hd ha hab x, Complex.ofReal_tsum, ← tsum_mul_left]
    -- termwise integrals
    have hI : ∀ j : Lattice d, ∫ x, Torus.mode (-n) x * ((bandCoeff d a b j * Torus.cosMode j x : ℝ) : ℂ)
        = ((bandCoeff d a b j : ℝ) : ℂ) / 2 * (if -n + j = 0 then 1 else 0) +
          ((bandCoeff d a b j : ℝ) : ℂ) / 2 * (if -n + -j = 0 then 1 else 0) := by
      intro j
      have hF : (fun x : Torus d => Torus.mode (-n) x * ((bandCoeff d a b j * Torus.cosMode j x : ℝ) : ℂ))
          = fun x => ((bandCoeff d a b j : ℝ) : ℂ) / 2 * (Torus.mode (-n) x * Torus.mode j x) +
              ((bandCoeff d a b j : ℝ) : ℂ) / 2 * (Torus.mode (-n) x * Torus.mode (-j) x) := by
        funext x
        rw [Complex.ofReal_mul, hcos j x]
        ring
      rw [hF, integral_add ((Torus.integrable_mode_mul _ _).const_mul _)
        ((Torus.integrable_mode_mul _ _).const_mul _), integral_const_mul, integral_const_mul,
        Torus.integral_mode_mul, Torus.integral_mode_mul]
    have hneg : bandCoeff d a b (-n) = bandCoeff d a b n := by
      unfold bandCoeff
      by_cases hn : n = 0
      · simp [hn]
      · simp [hn, HRS.enorm_neg]
    have h1 : HasSum (fun j : Lattice d => ((bandCoeff d a b j : ℝ) : ℂ) / 2 *
        (if -n + j = 0 then 1 else 0)) (((bandCoeff d a b n : ℝ) : ℂ) / 2) := by
      have := hasSum_single (f := fun j : Lattice d => ((bandCoeff d a b j : ℝ) : ℂ) / 2 *
        (if -n + j = 0 then 1 else 0)) n (fun j hj => by
          rw [if_neg (fun h => hj (neg_add_eq_zero.mp h).symm)]
          ring)
      convert this using 1
      simp
    have h2 : HasSum (fun j : Lattice d => ((bandCoeff d a b j : ℝ) : ℂ) / 2 *
        (if -n + -j = 0 then 1 else 0)) (((bandCoeff d a b (-n) : ℝ) : ℂ) / 2) := by
      have := hasSum_single (f := fun j : Lattice d => ((bandCoeff d a b j : ℝ) : ℂ) / 2 *
        (if -n + -j = 0 then 1 else 0)) (-n) (fun j hj => by
          rw [if_neg (fun h => hj (by
            have h' := eq_neg_of_add_eq_zero_left h
            rw [neg_neg] at h'
            exact h'.symm))]
          ring)
      convert this using 1
      simp
    rw [hexp, ← integral_tsum_of_summable_integral_norm (F := fun j x =>
      Torus.mode (-n) x * ((bandCoeff d a b j * Torus.cosMode j x : ℝ) : ℂ)) hint hFsum]
    calc ∑' j : Lattice d, ∫ x, Torus.mode (-n) x * ((bandCoeff d a b j * Torus.cosMode j x : ℝ) : ℂ)
        = ∑' j : Lattice d, (((bandCoeff d a b j : ℝ) : ℂ) / 2 * (if -n + j = 0 then 1 else 0) +
            ((bandCoeff d a b j : ℝ) : ℂ) / 2 * (if -n + -j = 0 then 1 else 0)) := tsum_congr hI
      _ = ((bandCoeff d a b n : ℝ) : ℂ) / 2 + ((bandCoeff d a b (-n) : ℝ) : ℂ) / 2 :=
          ((h1.add h2).tsum_eq)
      _ = ((bandCoeff d a b n : ℝ) : ℂ) := by rw [hneg]; ring
  -- Parseval in the complex Fourier form
  have hS := Torus.hasSum_sq_coeff hφ
  have hnorm : ∀ n : Lattice d, Torus.cosCoeff (heatBand d a b) n ^ 2 +
      Torus.sinCoeff (heatBand d a b) n ^ 2 = bandCoeff d a b n ^ 2 := fun n => by
    rw [← Torus.norm_sq_coeff hφ1 n, hcoef n, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have hS2 : HasSum (fun n : Lattice d => bandCoeff d a b n ^ 2) (∫ x, heatBand d a b x ^ 2) := by
    convert hS using 1
    funext n
    exact (hnorm n).symm
  exact hS2.tsum_eq.symm

/-! ### Cauchy-Schwarz in heat time -/

/-- The heat weight `t^{d/2-1}` is integrable on `(0, b]`. -/
theorem integrableOn_heatWeight_Ioc (hd : 2 ≤ d) (b : ℝ) (hb : 0 ≤ b) :
    IntegrableOn (heatWeight d) (Ioc (0 : ℝ) b) := by
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hp : -1 < (d : ℝ) / 2 - 1 := by linarith
  have h : IntervalIntegrable (fun t : ℝ => t ^ ((d : ℝ) / 2 - 1)) volume 0 b :=
    intervalIntegral.intervalIntegrable_rpow' hp
  exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hb).mp h

/-- The integrand `t^{d/2-1} e^{-t|k|²}` is integrable on `(0, b]`. -/
theorem integrableOn_heatWeight_exp_Ioc (hd : 2 ≤ d) (b : ℝ) (hb : 0 ≤ b) (k : Lattice d) :
    IntegrableOn (fun t => heatWeight d t * Real.exp (-t * Lattice.enorm k ^ 2)) (Ioc (0 : ℝ) b) := by
  have hm : Measurable (fun t : ℝ => heatWeight d t * Real.exp (-t * Lattice.enorm k ^ 2)) := by
    unfold heatWeight; fun_prop
  refine Integrable.mono' (integrableOn_heatWeight_Ioc hd b hb) hm.aestronglyMeasurable ?_
  refine ae_restrict_of_forall_mem measurableSet_Ioc fun t ht => ?_
  have h0 : 0 ≤ t * Lattice.enorm k ^ 2 := mul_nonneg ht.1.le (sq_nonneg _)
  have he : Real.exp (-t * Lattice.enorm k ^ 2) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by nlinarith)
  rw [Real.norm_of_nonneg (mul_nonneg (rb_heatWeight_nonneg ht.1) (Real.exp_pos _).le)]
  calc heatWeight d t * Real.exp (-t * Lattice.enorm k ^ 2)
      ≤ heatWeight d t * 1 := mul_le_mul_of_nonneg_left he (rb_heatWeight_nonneg ht.1)
    _ = heatWeight d t := mul_one _

/-- Monotonicity in the lower endpoint: `bandCoeff d a b k ≤ bandCoeff d 0 b k`. -/
theorem bandCoeff_le (hd : 2 ≤ d) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (k : Lattice d) :
    bandCoeff d a b k ≤ bandCoeff d 0 b k := by
  unfold bandCoeff
  split_ifs with hk
  · exact le_rfl
  · refine mul_le_mul_of_nonneg_left ?_ (rb_subA_nonneg hd)
    refine setIntegral_mono_set (integrableOn_heatWeight_exp_Ioc hd b (ha.trans hab) k)
      (ae_restrict_of_forall_mem measurableSet_Ioc fun t ht =>
        mul_nonneg (rb_heatWeight_nonneg ht.1) (Real.exp_pos _).le)
      (Set.Ioc_subset_Ioc_left ha).eventuallyLE

/-- A power `t^p` with `p > -1` is integrable on `(0, b]`. -/
theorem integrableOn_rpow_Ioc {p : ℝ} (hp : -1 < p) {b : ℝ} (hb : 0 ≤ b) :
    IntegrableOn (fun t : ℝ => t ^ p) (Ioc (0 : ℝ) b) :=
  (intervalIntegrable_iff_integrableOn_Ioc_of_le hb).mp (intervalIntegral.intervalIntegrable_rpow' hp)

/-- `t^p E(t)` with `p > -1` and `0 ≤ E ≤ 1` on `(0, b]` is integrable on `(0, b]`. -/
theorem integrableOn_rpow_mul_Ioc {p : ℝ} (hp : -1 < p) {b : ℝ} (hb : 0 ≤ b) {E : ℝ → ℝ}
    (hEm : Measurable E) (hE : ∀ t ∈ Ioc (0 : ℝ) b, 0 ≤ E t ∧ E t ≤ 1) :
    IntegrableOn (fun t => t ^ p * E t) (Ioc (0 : ℝ) b) := by
  have hm : Measurable (fun t : ℝ => t ^ p) := Measurable.pow_const measurable_id p
  refine Integrable.mono' (integrableOn_rpow_Ioc hp hb) (hm.mul hEm).aestronglyMeasurable ?_
  refine ae_restrict_of_forall_mem measurableSet_Ioc fun t ht => ?_
  obtain ⟨h0, h1⟩ := hE t ht
  have hpos : 0 ≤ t ^ p := Real.rpow_nonneg ht.1.le _
  rw [Real.norm_of_nonneg (mul_nonneg hpos h0)]
  calc t ^ p * E t ≤ t ^ p * 1 := mul_le_mul_of_nonneg_left h1 hpos
    _ = t ^ p := mul_one _

/-- `∫_{(0,b]} t^{d/4-1} dt = (4/d) b^{d/4}`. -/
theorem integral_rpow_quarter (hd : 1 ≤ d) {b : ℝ} (hb : 0 ≤ b) :
    ∫ t in Ioc (0 : ℝ) b, t ^ ((d : ℝ) / 4 - 1) = (4 / (d : ℝ)) * b ^ ((d : ℝ) / 4) := by
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hdpos : (0 : ℝ) < (d : ℝ) / 4 := by linarith
  have hr : -1 < (d : ℝ) / 4 - 1 := by linarith
  have hd0 : (d : ℝ) ≠ 0 := ne_of_gt (by linarith)
  rw [← intervalIntegral.integral_of_le hb, integral_rpow (Or.inl hr),
    show (d : ℝ) / 4 - 1 + 1 = (d : ℝ) / 4 by ring, Real.zero_rpow hdpos.ne', sub_zero]
  field_simp

/-- Two-term AM-GM with the Cauchy-Schwarz identity `q w = h²`: `2h ≤ λ w + q/λ`. -/
theorem amgm_aux {w q h lam : ℝ} (hw : 0 < w) (hlam : 0 < lam) (hqw : q * w = h ^ 2) :
    2 * h ≤ lam * w + q / lam := by
  have h1 : w * (lam ^ 2 * w + q - 2 * lam * h) = (lam * w - h) ^ 2 := by
    linear_combination hqw
  have h2 : 0 ≤ lam ^ 2 * w + q - 2 * lam * h := by
    have h3 : 0 ≤ w * (lam ^ 2 * w + q - 2 * lam * h) := by
      rw [h1]; exact sq_nonneg _
    exact (mul_nonneg_iff_of_pos_left hw).mp h3
  have h4 : lam * w + q / lam - 2 * h = (lam ^ 2 * w + q - 2 * lam * h) / lam := by
    field_simp
  have h5 : 0 ≤ (lam ^ 2 * w + q - 2 * lam * h) / lam := div_nonneg h2 hlam.le
  linarith

/-- The pointwise identity `q(t) w(t) = h(t)²` of the Cauchy-Schwarz weights. -/
theorem heat_cs_identity {t : ℝ} (ht : 0 < t) (n : ℝ) :
    (t ^ (3 * (d : ℝ) / 4 - 1) * Real.exp (-(2 * t) * n)) * t ^ ((d : ℝ) / 4 - 1) =
      (heatWeight d t * Real.exp (-t * n)) ^ 2 := by
  unfold heatWeight
  have e1 : Real.exp (-(2 * t) * n) = Real.exp (-t * n) * Real.exp (-t * n) := by
    rw [← Real.exp_add]; congr 1; ring
  have e2 : t ^ (3 * (d : ℝ) / 4 - 1) * t ^ ((d : ℝ) / 4 - 1) =
      t ^ ((d : ℝ) / 2 - 1) * t ^ ((d : ℝ) / 2 - 1) := by
    rw [← Real.rpow_add ht, ← Real.rpow_add ht]; congr 1; ring
  rw [e1]
  linear_combination (Real.exp (-t * n) * Real.exp (-t * n)) * e2

/-- Core Cauchy-Schwarz step: `(∫h)² ≤ (∫w)(∫q)` from the family of AM-GM inequalities. -/
theorem cs_core {s W Q : ℝ} (hs : 0 ≤ s) (hW : 0 < W) (hQ : 0 ≤ Q)
    (hK : ∀ lam : ℝ, 0 < lam → 2 * s ≤ lam * W + Q / lam) : s ^ 2 ≤ W * Q := by
  rcases hs.eq_or_lt with h0 | hpos
  · rw [← h0]
    simpa using mul_nonneg hW.le hQ
  · have key := hK (s / W) (div_pos hpos hW)
    have e1 : s / W * W = s := div_mul_cancel₀ s hW.ne'
    have e2 : Q / (s / W) * s = Q * W := by
      field_simp
    have hle : s ≤ Q / (s / W) := by linarith
    have h3 := mul_le_mul_of_nonneg_right hle hpos.le
    nlinarith

/-- Weighted Cauchy-Schwarz: for `k ≠ 0`,
`c_k² ≤ A² ((4/d) b^{d/4}) ∫_0^b t^{3d/4-1} e^{-2t|k|²} dt`. -/
theorem bandCoeff_sq_le (hd : 2 ≤ d) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (k : Lattice d)
    (hk : k ≠ 0) :
    bandCoeff d a b k ^ 2 ≤
      KernelAux.subA d 0 ^ 2 * ((4 / (d : ℝ)) * b ^ ((d : ℝ) / 4)) *
        ∫ t in Ioc (0 : ℝ) b, t ^ (3 * (d : ℝ) / 4 - 1) * Real.exp (-(2 * t) * Lattice.enorm k ^ 2) := by
  have hb0 : 0 ≤ b := ha.trans hab
  have hd1 : 1 ≤ d := by omega
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hdR : (0 : ℝ) < d := by linarith
  have hpw : -1 < (d : ℝ) / 4 - 1 := by linarith
  have hpq : -1 < 3 * (d : ℝ) / 4 - 1 := by linarith
  have hbc : bandCoeff d a b k = KernelAux.subA d 0 *
      ∫ t in Ioc a b, heatWeight d t * Real.exp (-t * Lattice.enorm k ^ 2) := by
    unfold bandCoeff; rw [if_neg hk]
  have hEnn : ∀ t : ℝ, 0 < t → 0 ≤ Real.exp (-(2 * t) * Lattice.enorm k ^ 2) :=
    fun t _ => (Real.exp_pos _).le
  have hE1 : ∀ t ∈ Ioc (0 : ℝ) b, 0 ≤ Real.exp (-(2 * t) * Lattice.enorm k ^ 2) ∧
      Real.exp (-(2 * t) * Lattice.enorm k ^ 2) ≤ 1 := by
    intro t ht
    refine ⟨(Real.exp_pos _).le, Real.exp_le_one_iff.mpr ?_⟩
    have : 0 ≤ t * Lattice.enorm k ^ 2 := mul_nonneg ht.1.le (sq_nonneg _)
    nlinarith
  have hQ0 : IntegrableOn (fun t : ℝ => t ^ (3 * (d : ℝ) / 4 - 1) *
      Real.exp (-(2 * t) * Lattice.enorm k ^ 2)) (Ioc (0 : ℝ) b) :=
    integrableOn_rpow_mul_Ioc hpq hb0 (E := fun t => Real.exp (-(2 * t) * Lattice.enorm k ^ 2))
      (by fun_prop) hE1
  have hWI : IntegrableOn (fun t : ℝ => t ^ ((d : ℝ) / 4 - 1)) (Ioc (0 : ℝ) b) :=
    integrableOn_rpow_Ioc hpw hb0
  have hHI : IntegrableOn (fun t => heatWeight d t * Real.exp (-t * Lattice.enorm k ^ 2))
      (Ioc (0 : ℝ) b) :=
    integrableOn_heatWeight_exp_Ioc hd b hb0 k
  have hsub : Ioc a b ⊆ Ioc (0 : ℝ) b := Set.Ioc_subset_Ioc_left ha
  have hR0 : 0 ≤ KernelAux.subA d 0 ^ 2 * ((4 / (d : ℝ)) * b ^ ((d : ℝ) / 4)) *
      ∫ t in Ioc (0 : ℝ) b, t ^ (3 * (d : ℝ) / 4 - 1) * Real.exp (-(2 * t) * Lattice.enorm k ^ 2) := by
    refine mul_nonneg (mul_nonneg (sq_nonneg _) (mul_nonneg (by positivity)
      (Real.rpow_nonneg hb0 _))) (setIntegral_nonneg measurableSet_Ioc fun t ht => ?_)
    exact mul_nonneg (Real.rpow_nonneg ht.1.le _) (hEnn t ht.1)
  rcases hab.eq_or_lt with hab' | hab'
  · rw [hbc, hab', Set.Ioc_self, Measure.restrict_empty, integral_zero_measure, mul_zero]
    calc (0 : ℝ) ^ 2 = 0 := by norm_num
      _ ≤ _ := hR0
  · -- the three integrals over `(a, b]`
    have hsI : IntegrableOn (fun t => heatWeight d t * Real.exp (-t * Lattice.enorm k ^ 2))
        (Ioc a b) := hHI.mono_set hsub
    have hWa : IntegrableOn (fun t : ℝ => t ^ ((d : ℝ) / 4 - 1)) (Ioc a b) := hWI.mono_set hsub
    have hQa : IntegrableOn (fun t : ℝ => t ^ (3 * (d : ℝ) / 4 - 1) *
        Real.exp (-(2 * t) * Lattice.enorm k ^ 2)) (Ioc a b) := hQ0.mono_set hsub
    have hWpos : 0 < ∫ t in Ioc a b, t ^ ((d : ℝ) / 4 - 1) := by
      rw [← intervalIntegral.integral_of_le hab'.le]
      exact intervalIntegral.intervalIntegral_pos_of_pos_on
        (intervalIntegral.intervalIntegrable_rpow' hpw)
        (fun x hx => Real.rpow_pos_of_pos (lt_of_le_of_lt ha hx.1) _) hab'
    have hK : ∀ lam : ℝ, 0 < lam →
        2 * (∫ t in Ioc a b, heatWeight d t * Real.exp (-t * Lattice.enorm k ^ 2)) ≤
          lam * (∫ t in Ioc a b, t ^ ((d : ℝ) / 4 - 1)) +
            (∫ t in Ioc a b, t ^ (3 * (d : ℝ) / 4 - 1) * Real.exp (-(2 * t) * Lattice.enorm k ^ 2)) / lam := by
      intro lam hlam
      have hpt : ∀ t ∈ Ioc a b, 2 * (heatWeight d t * Real.exp (-t * Lattice.enorm k ^ 2)) ≤
          lam * t ^ ((d : ℝ) / 4 - 1) +
            t ^ (3 * (d : ℝ) / 4 - 1) * Real.exp (-(2 * t) * Lattice.enorm k ^ 2) / lam := by
        intro t ht
        have htpos : 0 < t := lt_of_le_of_lt ha ht.1
        exact amgm_aux (Real.rpow_pos_of_pos htpos _) hlam (heat_cs_identity htpos _)
      have hI1 : IntegrableOn (fun t => 2 * (heatWeight d t * Real.exp (-t * Lattice.enorm k ^ 2)))
          (Ioc a b) := hsI.const_mul 2
      have hI2 : IntegrableOn (fun t => lam * t ^ ((d : ℝ) / 4 - 1) +
          t ^ (3 * (d : ℝ) / 4 - 1) * Real.exp (-(2 * t) * Lattice.enorm k ^ 2) / lam) (Ioc a b) :=
        (hWa.const_mul lam).add (hQa.div_const lam)
      have hmono := setIntegral_mono_on hI1 hI2 measurableSet_Ioc hpt
      rw [integral_const_mul, integral_add (hWa.const_mul lam) (hQa.div_const lam),
        integral_const_mul, integral_div] at hmono
      exact hmono
    have hs0 : 0 ≤ ∫ t in Ioc a b, heatWeight d t * Real.exp (-t * Lattice.enorm k ^ 2) :=
      setIntegral_nonneg measurableSet_Ioc fun t ht =>
        mul_nonneg (rb_heatWeight_nonneg (lt_of_le_of_lt ha ht.1)) (Real.exp_pos _).le
    have hQ0' : 0 ≤ ∫ t in Ioc a b, t ^ (3 * (d : ℝ) / 4 - 1) *
        Real.exp (-(2 * t) * Lattice.enorm k ^ 2) :=
      setIntegral_nonneg measurableSet_Ioc fun t ht =>
        mul_nonneg (Real.rpow_nonneg (lt_of_le_of_lt ha ht.1).le _) (hEnn t (lt_of_le_of_lt ha ht.1))
    have hcs := cs_core hs0 hWpos hQ0' hK
    have hW : ∫ t in Ioc a b, t ^ ((d : ℝ) / 4 - 1) ≤ (4 / (d : ℝ)) * b ^ ((d : ℝ) / 4) := by
      rw [← integral_rpow_quarter hd1 hb0]
      exact setIntegral_mono_set hWI
        (ae_restrict_of_forall_mem measurableSet_Ioc fun t ht =>
          Real.rpow_nonneg ht.1.le _)
        hsub.eventuallyLE
    have hQ : ∫ t in Ioc a b, t ^ (3 * (d : ℝ) / 4 - 1) * Real.exp (-(2 * t) * Lattice.enorm k ^ 2) ≤
        ∫ t in Ioc (0 : ℝ) b, t ^ (3 * (d : ℝ) / 4 - 1) * Real.exp (-(2 * t) * Lattice.enorm k ^ 2) :=
      setIntegral_mono_set hQ0
        (ae_restrict_of_forall_mem measurableSet_Ioc fun t ht =>
          mul_nonneg (Real.rpow_nonneg ht.1.le _) (hEnn t ht.1))
        hsub.eventuallyLE
    rw [hbc, mul_pow]
    have hW0 : 0 ≤ (4 / (d : ℝ)) * b ^ ((d : ℝ) / 4) :=
      mul_nonneg (by positivity) (Real.rpow_nonneg hb0 _)
    calc KernelAux.subA d 0 ^ 2 * (∫ t in Ioc a b, heatWeight d t * Real.exp (-t * Lattice.enorm k ^ 2)) ^ 2
        ≤ KernelAux.subA d 0 ^ 2 * ((∫ t in Ioc a b, t ^ ((d : ℝ) / 4 - 1)) *
            ∫ t in Ioc a b, t ^ (3 * (d : ℝ) / 4 - 1) * Real.exp (-(2 * t) * Lattice.enorm k ^ 2)) :=
          mul_le_mul_of_nonneg_left hcs (sq_nonneg _)
      _ ≤ KernelAux.subA d 0 ^ 2 * ((4 / (d : ℝ)) * b ^ ((d : ℝ) / 4) *
            ∫ t in Ioc (0 : ℝ) b, t ^ (3 * (d : ℝ) / 4 - 1) * Real.exp (-(2 * t) * Lattice.enorm k ^ 2)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul hW hQ hQ0' hW0) (sq_nonneg _)
      _ = KernelAux.subA d 0 ^ 2 * ((4 / (d : ℝ)) * b ^ ((d : ℝ) / 4)) *
            ∫ t in Ioc (0 : ℝ) b, t ^ (3 * (d : ℝ) / 4 - 1) * Real.exp (-(2 * t) * Lattice.enorm k ^ 2) := by
          ring

/-- Tonelli for a nonnegative lattice family of heat-time integrals, dominated pointwise by an
integrable `H`: the integrals are summable and `∑_k ∫_S F_k ≤ ∫_S H`. -/
theorem summable_integral_of_tsum_le {S : Set ℝ} (hS : MeasurableSet S) {F : Lattice d → ℝ → ℝ}
    (hF0 : ∀ k, ∀ t ∈ S, 0 ≤ F k t) (hFm : ∀ k, Measurable (F k)) {H : ℝ → ℝ}
    (hH : IntegrableOn H S) (hsum : ∀ t ∈ S, Summable fun k => F k t)
    (hHbd : ∀ t ∈ S, ∑' k, F k t ≤ H t) :
    Summable (fun k => ∫ t in S, F k t) ∧ ∑' k, (∫ t in S, F k t) ≤ ∫ t in S, H t := by
  have hH0 : ∀ t ∈ S, 0 ≤ H t := fun t ht => (tsum_nonneg fun k => hF0 k t ht).trans (hHbd t ht)
  have hL : ∫⁻ t in S, ENNReal.ofReal (H t) ≠ ⊤ := hH.lintegral_lt_top.ne
  have hle : ∑' k, ∫⁻ t in S, ENNReal.ofReal (F k t) ≤ ∫⁻ t in S, ENNReal.ofReal (H t) := by
    rw [← lintegral_tsum fun k => (hFm k).ennreal_ofReal.aemeasurable]
    refine lintegral_mono_ae (ae_restrict_of_forall_mem hS fun t ht => ?_)
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => hF0 k t ht) (hsum t ht)]
    exact ENNReal.ofReal_le_ofReal (hHbd t ht)
  have hT : ∑' k, ∫⁻ t in S, ENNReal.ofReal (F k t) ≠ ⊤ := ne_top_of_le_ne_top hL hle
  have hint : ∀ k, ∫ t in S, F k t = (∫⁻ t in S, ENNReal.ofReal (F k t)).toReal := fun k =>
    integral_eq_lintegral_of_nonneg_ae (ae_restrict_of_forall_mem hS fun t ht => hF0 k t ht)
      (hFm k).aestronglyMeasurable
  refine ⟨?_, ?_⟩
  · have e : (fun k => ∫ t in S, F k t) = fun k => (∫⁻ t in S, ENNReal.ofReal (F k t)).toReal :=
      funext hint
    rw [e]
    exact ENNReal.summable_toReal hT
  · calc ∑' k, (∫ t in S, F k t)
        = ∑' k, (∫⁻ t in S, ENNReal.ofReal (F k t)).toReal := tsum_congr hint
      _ = (∑' k, ∫⁻ t in S, ENNReal.ofReal (F k t)).toReal :=
          (ENNReal.tsum_toReal_eq fun k => ENNReal.ne_top_of_tsum_ne_top hT k).symm
      _ ≤ (∫⁻ t in S, ENNReal.ofReal (H t)).toReal := ENNReal.toReal_mono hL hle
      _ = ∫ t in S, H t :=
          (integral_eq_lintegral_of_nonneg_ae (ae_restrict_of_forall_mem hS hH0)
            hH.aestronglyMeasurable).symm

/-- The lattice integrand `k ↦ 1_{k≠0} t^{3d/4-1} e^{-2t|k|²}`, nonnegative. -/
theorem heatF_nonneg {t : ℝ} (ht : 0 < t) (k : Lattice d) :
    0 ≤ (if k = 0 then (0 : ℝ) else t ^ (3 * (d : ℝ) / 4 - 1) *
      Real.exp (-(2 * t) * Lattice.enorm k ^ 2)) := by
  split_ifs
  · exact le_rfl
  · exact mul_nonneg (Real.rpow_nonneg ht.le _) (Real.exp_pos _).le

theorem heatF_measurable (k : Lattice d) :
    Measurable (fun t : ℝ => if k = 0 then (0 : ℝ) else t ^ (3 * (d : ℝ) / 4 - 1) *
      Real.exp (-(2 * t) * Lattice.enorm k ^ 2)) := by
  by_cases hk : k = 0 <;> simp only [hk, ↓reduceIte] <;> fun_prop

theorem heatF_summable {t : ℝ} (ht : 0 < t) :
    Summable fun k : Lattice d => (if k = 0 then (0 : ℝ) else t ^ (3 * (d : ℝ) / 4 - 1) *
      Real.exp (-(2 * t) * Lattice.enorm k ^ 2)) := by
  refine Summable.of_nonneg_of_le (fun k => heatF_nonneg ht k) (fun k => ?_)
    ((summable_gauss_lattice d (2 * t) (by positivity)).mul_left (t ^ (3 * (d : ℝ) / 4 - 1)))
  by_cases hk : k = 0
  · rw [if_pos hk]; positivity
  · rw [if_neg hk]

/-- Heat-trace bound at small times: `∑_k 1_{k≠0} t^{3d/4-1} e^{-2t|k|²} ≤ (π/2)^{d/2} Θ_d t^{d/4-1}`
for `0 < t ≤ 1/2` (`1 + Ψ(0,2t) ≤ (π/2t)^{d/2} Θ_d`). -/
theorem tsum_heatF_le_small {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1 / 2) :
    ∑' k : Lattice d, (if k = 0 then (0 : ℝ) else t ^ (3 * (d : ℝ) / 4 - 1) *
      Real.exp (-(2 * t) * Lattice.enorm k ^ 2)) ≤
      (Real.pi / 2) ^ ((d : ℝ) / 2) * thetaConst d * t ^ ((d : ℝ) / 4 - 1) := by
  have hfac : ∀ k : Lattice d, (if k = 0 then (0 : ℝ) else t ^ (3 * (d : ℝ) / 4 - 1) *
      Real.exp (-(2 * t) * Lattice.enorm k ^ 2)) =
      t ^ (3 * (d : ℝ) / 4 - 1) * (if k = 0 then 0 else Real.exp (-(2 * t) * Lattice.enorm k ^ 2)) := by
    intro k; split_ifs <;> ring
  have hpsi : ∑' k : Lattice d, (if k = 0 then (0 : ℝ) else Real.exp (-(2 * t) * Lattice.enorm k ^ 2))
      = psiFn (0 : Torus d) (2 * t) := by
    unfold psiFn
    refine tsum_congr fun k => ?_
    by_cases hk : k = 0
    · simp [hk]
    · simp [hk, cosMode_zero_pt]
  have h1 := one_add_psiFn_zero_le (d := d) (u := 2 * t) (by positivity) (by linarith)
  have hp0 : 0 ≤ t ^ (3 * (d : ℝ) / 4 - 1) := Real.rpow_nonneg ht.le _
  have e1 : t ^ ((d : ℝ) / 4 - 1) * t ^ ((d : ℝ) / 2) = t ^ (3 * (d : ℝ) / 4 - 1) := by
    rw [← Real.rpow_add ht]; congr 1; ring
  have hX : 0 < t ^ ((d : ℝ) / 2) := Real.rpow_pos_of_pos ht _
  have hid : t ^ (3 * (d : ℝ) / 4 - 1) * ((Real.pi / (2 * t)) ^ ((d : ℝ) / 2) * thetaConst d) =
      (Real.pi / 2) ^ ((d : ℝ) / 2) * thetaConst d * t ^ ((d : ℝ) / 4 - 1) := by
    rw [← div_div, Real.div_rpow (by positivity) ht.le, ← e1]
    field_simp
  calc ∑' k : Lattice d, (if k = 0 then (0 : ℝ) else t ^ (3 * (d : ℝ) / 4 - 1) *
        Real.exp (-(2 * t) * Lattice.enorm k ^ 2))
      = t ^ (3 * (d : ℝ) / 4 - 1) * psiFn (0 : Torus d) (2 * t) := by
        simp_rw [hfac]
        rw [tsum_mul_left, hpsi]
    _ ≤ t ^ (3 * (d : ℝ) / 4 - 1) * ((Real.pi / (2 * t)) ^ ((d : ℝ) / 2) * thetaConst d) :=
        mul_le_mul_of_nonneg_left (by linarith) hp0
    _ = _ := hid

/-- Heat-trace bound at large times `1/2 ≤ t ≤ b`: the lattice sum is at most `T_0 b^{d/2} t^{d/4-1}`
with `T_0 = ∑_k e^{-|k|²}` (`e^{-2t|k|²} ≤ e^{-|k|²}` for `2t ≥ 1`). -/
theorem tsum_heatF_le_large (hd : 2 ≤ d) {t b : ℝ} (ht : 1 / 2 ≤ t) (htb : t ≤ b) :
    ∑' k : Lattice d, (if k = 0 then (0 : ℝ) else t ^ (3 * (d : ℝ) / 4 - 1) *
      Real.exp (-(2 * t) * Lattice.enorm k ^ 2)) ≤
      (∑' k : Lattice d, Real.exp (-1 * Lattice.enorm k ^ 2)) * b ^ ((d : ℝ) / 2) *
        t ^ ((d : ℝ) / 4 - 1) := by
  have ht0 : 0 < t := by linarith
  have hsT : Summable fun k : Lattice d => Real.exp (-1 * Lattice.enorm k ^ 2) :=
    summable_gauss_lattice d 1 one_pos
  have hterm : ∀ k : Lattice d, (if k = 0 then (0 : ℝ) else Real.exp (-(2 * t) * Lattice.enorm k ^ 2))
      ≤ Real.exp (-1 * Lattice.enorm k ^ 2) := by
    intro k
    by_cases hk : k = 0
    · rw [if_pos hk]; positivity
    · rw [if_neg hk]
      apply Real.exp_le_exp.mpr
      have hn : 0 ≤ Lattice.enorm k ^ 2 := sq_nonneg _
      nlinarith [mul_nonneg (sub_nonneg.mpr (show (1 : ℝ) ≤ 2 * t by linarith)) hn]
  have hX : Summable fun k : Lattice d =>
      (if k = 0 then (0 : ℝ) else Real.exp (-(2 * t) * Lattice.enorm k ^ 2)) :=
    Summable.of_nonneg_of_le (fun k => by split_ifs <;> positivity) hterm hsT
  have hXle := Summable.tsum_le_tsum hterm hX hsT
  have hfac : ∀ k : Lattice d, (if k = 0 then (0 : ℝ) else t ^ (3 * (d : ℝ) / 4 - 1) *
      Real.exp (-(2 * t) * Lattice.enorm k ^ 2)) =
      t ^ (3 * (d : ℝ) / 4 - 1) * (if k = 0 then 0 else Real.exp (-(2 * t) * Lattice.enorm k ^ 2)) := by
    intro k; split_ifs <;> ring
  have hpt : t ^ (3 * (d : ℝ) / 4 - 1) = t ^ ((d : ℝ) / 2) * t ^ ((d : ℝ) / 4 - 1) := by
    rw [← Real.rpow_add ht0]; congr 1; ring
  have hpb : t ^ ((d : ℝ) / 2) ≤ b ^ ((d : ℝ) / 2) :=
    Real.rpow_le_rpow ht0.le htb (by positivity)
  have hT0 : 0 ≤ ∑' k : Lattice d, Real.exp (-1 * Lattice.enorm k ^ 2) :=
    tsum_nonneg fun k => (Real.exp_pos _).le
  calc ∑' k : Lattice d, (if k = 0 then (0 : ℝ) else t ^ (3 * (d : ℝ) / 4 - 1) *
        Real.exp (-(2 * t) * Lattice.enorm k ^ 2))
      = t ^ (3 * (d : ℝ) / 4 - 1) * ∑' k : Lattice d,
          (if k = 0 then (0 : ℝ) else Real.exp (-(2 * t) * Lattice.enorm k ^ 2)) := by
        simp_rw [hfac]
        rw [tsum_mul_left]
    _ ≤ t ^ (3 * (d : ℝ) / 4 - 1) * ∑' k : Lattice d, Real.exp (-1 * Lattice.enorm k ^ 2) :=
        mul_le_mul_of_nonneg_left hXle (Real.rpow_nonneg ht0.le _)
    _ = (t ^ ((d : ℝ) / 2) * t ^ ((d : ℝ) / 4 - 1)) * ∑' k : Lattice d,
          Real.exp (-1 * Lattice.enorm k ^ 2) := by rw [hpt]
    _ ≤ (b ^ ((d : ℝ) / 2) * t ^ ((d : ℝ) / 4 - 1)) * ∑' k : Lattice d,
          Real.exp (-1 * Lattice.enorm k ^ 2) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hpb
          (Real.rpow_nonneg ht0.le _)) hT0
    _ = _ := by ring

/-- Tonelli and the heat-trace bound: for `0 < b ≤ 1/2`,
`∑_{k≠0} ∫_0^b t^{3d/4-1} e^{-2t|k|²} dt = ∫_0^b t^{3d/4-1} Ψ(0, 2t) dt
  ≤ (π/2)^{d/2} Θ_d ∫_0^b t^{d/4-1} dt = (π/2)^{d/2} Θ_d (4/d) b^{d/4}`. -/
theorem tsum_integral_exp_le (hd : 2 ≤ d) {b : ℝ} (hb : 0 < b) (hb1 : b ≤ 1 / 2) :
    ∑' k : Lattice d, (if k = 0 then 0 else
        ∫ t in Ioc (0 : ℝ) b, t ^ (3 * (d : ℝ) / 4 - 1) * Real.exp (-(2 * t) * Lattice.enorm k ^ 2)) ≤
      (Real.pi / 2) ^ ((d : ℝ) / 2) * thetaConst d * ((4 / (d : ℝ)) * b ^ ((d : ℝ) / 4)) := by
  have hd1 : 1 ≤ d := by omega
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hpw : -1 < (d : ℝ) / 4 - 1 := by linarith
  have key := summable_integral_of_tsum_le (d := d) (S := Ioc (0 : ℝ) b) measurableSet_Ioc
    (F := fun k t => if k = 0 then (0 : ℝ) else t ^ (3 * (d : ℝ) / 4 - 1) *
      Real.exp (-(2 * t) * Lattice.enorm k ^ 2))
    (fun k t ht => heatF_nonneg ht.1 k) (fun k => heatF_measurable k)
    ((integrableOn_rpow_Ioc hpw hb.le).const_mul ((Real.pi / 2) ^ ((d : ℝ) / 2) * thetaConst d))
    (fun t ht => heatF_summable ht.1)
    (H := fun t => (Real.pi / 2) ^ ((d : ℝ) / 2) * thetaConst d * t ^ ((d : ℝ) / 4 - 1))
    (fun t ht => tsum_heatF_le_small ht.1 (ht.2.trans hb1))
  have e : ∀ k : Lattice d, (if k = 0 then (0 : ℝ) else
      ∫ t in Ioc (0 : ℝ) b, t ^ (3 * (d : ℝ) / 4 - 1) * Real.exp (-(2 * t) * Lattice.enorm k ^ 2)) =
      ∫ t in Ioc (0 : ℝ) b, (if k = 0 then (0 : ℝ) else
        t ^ (3 * (d : ℝ) / 4 - 1) * Real.exp (-(2 * t) * Lattice.enorm k ^ 2)) := by
    intro k
    by_cases hk : k = 0 <;> simp [hk]
  simp_rw [e]
  refine key.2.trans_eq ?_
  rw [integral_const_mul, integral_rpow_quarter hd1 hb.le]

theorem summable_integral_exp (hd : 2 ≤ d) {b : ℝ} (hb : 0 < b) :
    Summable fun k : Lattice d => (if k = 0 then 0 else
      ∫ t in Ioc (0 : ℝ) b, t ^ (3 * (d : ℝ) / 4 - 1) * Real.exp (-(2 * t) * Lattice.enorm k ^ 2)) := by
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hpw : -1 < (d : ℝ) / 4 - 1 := by linarith
  have hT0 : 0 ≤ ∑' k : Lattice d, Real.exp (-1 * Lattice.enorm k ^ 2) :=
    tsum_nonneg fun k => (Real.exp_pos _).le
  have hA0 : 0 ≤ (Real.pi / 2) ^ ((d : ℝ) / 2) * thetaConst d :=
    mul_nonneg (Real.rpow_nonneg (by positivity) _) (thetaConst_pos d).le
  obtain ⟨C, hC⟩ : ∃ C : ℝ, C = (Real.pi / 2) ^ ((d : ℝ) / 2) * thetaConst d +
      (∑' k : Lattice d, Real.exp (-1 * Lattice.enorm k ^ 2)) * b ^ ((d : ℝ) / 2) := ⟨_, rfl⟩
  have hbd : ∀ t ∈ Ioc (0 : ℝ) b, ∑' k : Lattice d, (if k = 0 then (0 : ℝ) else
      t ^ (3 * (d : ℝ) / 4 - 1) * Real.exp (-(2 * t) * Lattice.enorm k ^ 2)) ≤ C * t ^ ((d : ℝ) / 4 - 1) := by
    intro t ht
    have htp : 0 ≤ t ^ ((d : ℝ) / 4 - 1) := Real.rpow_nonneg ht.1.le _
    by_cases h2 : t ≤ 1 / 2
    · calc _ ≤ (Real.pi / 2) ^ ((d : ℝ) / 2) * thetaConst d * t ^ ((d : ℝ) / 4 - 1) :=
          tsum_heatF_le_small ht.1 h2
        _ ≤ C * t ^ ((d : ℝ) / 4 - 1) := by
          rw [hC]
          exact mul_le_mul_of_nonneg_right
            (le_add_of_nonneg_right (mul_nonneg hT0 (Real.rpow_nonneg hb.le _))) htp
    · push_neg at h2
      calc _ ≤ (∑' k : Lattice d, Real.exp (-1 * Lattice.enorm k ^ 2)) * b ^ ((d : ℝ) / 2) *
            t ^ ((d : ℝ) / 4 - 1) := tsum_heatF_le_large hd h2.le ht.2
        _ ≤ C * t ^ ((d : ℝ) / 4 - 1) := by
          rw [hC]
          exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hA0) htp
  obtain ⟨hsumm, -⟩ := summable_integral_of_tsum_le (d := d) (S := Ioc (0 : ℝ) b) measurableSet_Ioc
    (F := fun k t => if k = 0 then (0 : ℝ) else t ^ (3 * (d : ℝ) / 4 - 1) *
      Real.exp (-(2 * t) * Lattice.enorm k ^ 2))
    (fun k t ht => heatF_nonneg ht.1 k) (fun k => heatF_measurable k)
    ((integrableOn_rpow_Ioc hpw hb.le).const_mul C)
    (fun t ht => heatF_summable ht.1) (H := fun t => C * t ^ ((d : ℝ) / 4 - 1)) hbd
  convert hsumm using 1
  funext k
  by_cases hk : k = 0 <;> simp [hk]

/-- The `L²` bound of a band, uniform in the lower endpoint: `∫ heatBand d a b ² ≤ l2Const d · b^{d/2}`
for `0 < a ≤ b ≤ 1/2`. -/
theorem integral_sq_heatBand_le (hd : 2 ≤ d) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hb : b ≤ 1 / 2) :
    ∫ x, heatBand d a b x ^ 2 ≤ l2Const d * b ^ ((d : ℝ) / 2) := by
  rw [integral_sq_heatBand_eq hd ha hab]
  have hb0 : 0 < b := ha.trans_le hab
  have hA0 : 0 ≤ KernelAux.subA d 0 ^ 2 * ((4 / (d : ℝ)) * b ^ ((d : ℝ) / 4)) :=
    mul_nonneg (sq_nonneg _) (mul_nonneg (by positivity) (Real.rpow_nonneg hb0.le _))
  have hsumG := (summable_integral_exp hd hb0).mul_left
    (KernelAux.subA d 0 ^ 2 * ((4 / (d : ℝ)) * b ^ ((d : ℝ) / 4)))
  have hle : ∀ k : Lattice d, bandCoeff d a b k ^ 2 ≤
      KernelAux.subA d 0 ^ 2 * ((4 / (d : ℝ)) * b ^ ((d : ℝ) / 4)) *
        (if k = 0 then 0 else ∫ t in Ioc (0 : ℝ) b,
          t ^ (3 * (d : ℝ) / 4 - 1) * Real.exp (-(2 * t) * Lattice.enorm k ^ 2)) := by
    intro k
    by_cases hk : k = 0
    · subst hk
      simp [bandCoeff_zero]
    · rw [if_neg hk]
      exact bandCoeff_sq_le hd ha.le hab k hk
  have hsumB : Summable (fun k : Lattice d => bandCoeff d a b k ^ 2) :=
    Summable.of_nonneg_of_le (fun k => sq_nonneg _) hle hsumG
  have hcomp := Summable.tsum_le_tsum hle hsumB hsumG
  rw [tsum_mul_left] at hcomp
  have hT := tsum_integral_exp_le hd hb0 hb
  have hfin := hcomp.trans (mul_le_mul_of_nonneg_left hT hA0)
  refine hfin.trans (le_of_eq ?_)
  have hbb : b ^ ((d : ℝ) / 4) * b ^ ((d : ℝ) / 4) = b ^ ((d : ℝ) / 2) := by
    rw [← Real.rpow_add hb0]; congr 1; ring
  unfold l2Const
  rw [← hbb]
  ring

theorem l2Const_nonneg (hd : 2 ≤ d) : 0 ≤ l2Const d := by
  unfold l2Const
  exact mul_nonneg (mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))
    (Real.rpow_nonneg (by positivity) _)) (thetaConst_pos d).le

/-! ### Row and joint second moments against a bounded density -/

variable {ρ : Torus d → ℝ} {Λ : ℝ} {μ : Measure (Torus d)}

/-- `∫ heatBand(x - y)² dμ(y) ≤ Λ ∫ heatBand² dx ≤ Λ l2Const d b^{d/2}`. -/
theorem row_sq_heatBand_le (hd : 2 ≤ d) (hμ : μ = withDensityReal ρ) (hρ : IsProbDensity ρ)
    (hΛ : ∀ x, ρ x ≤ Λ) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : b ≤ 1 / 2) (x : Torus d) :
    ∫ y, heatBand d a b (x - y) ^ 2 ∂μ ≤ Λ * l2Const d * b ^ ((d : ℝ) / 2) := by
  subst hμ
  have hΛ0 : 0 ≤ Λ := (hρ.nonneg x).trans (hΛ x)
  have hg2 : Integrable (fun y => heatBand d a b y ^ 2) (volume : Measure (Torus d)) :=
    (memLp_two_heatBand hd ha).integrable_sq
  have hsq0 : ∀ y, 0 ≤ heatBand d a b y ^ 2 := fun y => sq_nonneg _
  have hmeas : Measurable (fun y : Torus d => heatBand d a b (x - y) ^ 2) :=
    ((measurable_heatBand hd a b).comp (measurable_const.sub measurable_id)).pow_const 2
  have hLHS : ∫ y, heatBand d a b (x - y) ^ 2 ∂(withDensityReal ρ) =
      (∫⁻ y, ENNReal.ofReal (heatBand d a b (x - y) ^ 2) ∂(withDensityReal ρ)).toReal :=
    integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun y => sq_nonneg _)
      hmeas.aestronglyMeasurable
  have hlin := KernelAux2.lintegral_conv_le ρ Λ hΛ (fun z => ENNReal.ofReal (heatBand d a b z ^ 2)) x
  have hR : ∫⁻ y, ENNReal.ofReal (heatBand d a b y ^ 2) =
      ENNReal.ofReal (∫ y, heatBand d a b y ^ 2) :=
    (ofReal_integral_eq_lintegral_ofReal hg2 (ae_of_all _ hsq0)).symm
  have hfin : ENNReal.ofReal Λ * ∫⁻ y, ENNReal.ofReal (heatBand d a b y ^ 2) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (by rw [hR]; exact ENNReal.ofReal_ne_top)
  have hval : (ENNReal.ofReal Λ * ∫⁻ y, ENNReal.ofReal (heatBand d a b y ^ 2)).toReal =
      Λ * ∫ y, heatBand d a b y ^ 2 := by
    rw [hR, ← ENNReal.ofReal_mul hΛ0,
      ENNReal.toReal_ofReal (mul_nonneg hΛ0 (integral_nonneg fun y => sq_nonneg _))]
  calc ∫ y, heatBand d a b (x - y) ^ 2 ∂(withDensityReal ρ)
      = (∫⁻ y, ENNReal.ofReal (heatBand d a b (x - y) ^ 2) ∂(withDensityReal ρ)).toReal := hLHS
    _ ≤ (ENNReal.ofReal Λ * ∫⁻ y, ENNReal.ofReal (heatBand d a b y ^ 2)).toReal :=
        ENNReal.toReal_mono hfin hlin
    _ = Λ * ∫ y, heatBand d a b y ^ 2 := hval
    _ ≤ Λ * (l2Const d * b ^ ((d : ℝ) / 2)) :=
        mul_le_mul_of_nonneg_left (integral_sq_heatBand_le hd ha hab hb) hΛ0
    _ = Λ * l2Const d * b ^ ((d : ℝ) / 2) := by ring

theorem memLp_two_heatBand_pair (hd : 2 ≤ d) (hμ : μ = withDensityReal ρ) (hρ : IsProbDensity ρ)
    (hΛ : ∀ x, ρ x ≤ Λ) [IsProbabilityMeasure μ] {a b : ℝ} (ha : 0 < a) (c : ℝ) :
    MemLp (fun p : Torus d × Torus d => c * heatBand d a b (p.1 - p.2)) 2 (μ.prod μ) :=
  memLp_two_of_continuous_repulsive (continuous_const.mul
    ((continuous_heatBand hd ha).comp (continuous_fst.sub continuous_snd)))

theorem memLp_two_masterKernel (hd : 2 ≤ d) (hμ : μ = withDensityReal ρ) (hρ : IsProbDensity ρ)
    (hΛ : ∀ x, ρ x ≤ Λ) [IsProbabilityMeasure μ] {α δ β : ℝ} (hα : 0 < α) :
    MemLp (masterKernel d α δ β μ) 2 (μ.prod μ) := by
  have hc : Continuous (pairKernel (heatBand d (α ^ 2) (δ ^ 2)) μ) :=
    continuous_pairKernel (continuous_heatBand hd (pow_pos hα 2)) μ
  exact memLp_two_of_continuous_repulsive (hc.const_mul (2 * β))

/-- The norm fields (M3) of the master kernel `q = 2β (heatBand d α² δ²)~`, `0 < α ≤ δ`,
`δ² ≤ 1/2`: with `W = 2β heatBand(x - y)` the row integrals are `≤ 4β² bandRowControl d Λ δ`,
so by `ae_row_sq_hoeffdingCentered_le`, `integral_sq_hoeffdingCentered_le` and
`norm_integralOperator_le` the row and joint second moments of `q` are `≤ 64 β² bandRowControl`
and the operator norm is `≤ 8β √bandRowControl`.  `L` stands for `glzUniversalTailConstant`. -/
theorem masterKernel_norm_fields (hd : 2 ≤ d) (hμ : μ = withDensityReal ρ) (hρ : IsProbDensity ρ)
    (hΛ : ∀ x, ρ x ≤ Λ) [IsProbabilityMeasure μ] {α δ β : ℝ} (hα : 0 < α) (hαδ : α ≤ δ)
    (hδ : δ ^ 2 ≤ 1 / 2) (hβ : 0 ≤ β) {L : ℝ} (hL : 0 < L)
    (hrow : 64 * β ^ 2 * bandRowControl d Λ δ ≤ 1 / L)
    (hop : 8 * β * Real.sqrt (bandRowControl d Λ δ) ≤ 1 / L) :
    (∀ᵐ x ∂μ, ∫ y, masterKernel d α δ β μ (x, y) ^ 2 ∂μ ≤ 1 / L) ∧
    (∫ p, masterKernel d α δ β μ p ^ 2 ∂(μ.prod μ)) ≤ 1 / L ∧
    ∀ h2 : MemLp (masterKernel d α δ β μ) 2 (μ.prod μ),
      ‖DGRHS.Kernel.integralOperator (masterKernel d α δ β μ) h2‖ ≤ 1 / L := by
  have hα2 : 0 < α ^ 2 := pow_pos hα 2
  have hab : α ^ 2 ≤ δ ^ 2 := pow_le_pow_left₀ hα.le hαδ 2
  have hΛ0 : 0 ≤ Λ := (hρ.nonneg 0).trans (hΛ 0)
  have hR0 : 0 ≤ bandRowControl d Λ δ := by
    unfold bandRowControl
    exact mul_nonneg (mul_nonneg hΛ0 (l2Const_nonneg hd)) (Real.rpow_nonneg (sq_nonneg _) _)
  have hβ2 : 0 ≤ (2 * β) ^ 2 := sq_nonneg _
  set f : Torus d → ℝ := heatBand d (α ^ 2) (δ ^ 2) with hf
  set W : Torus d × Torus d → ℝ := fun p => f (p.1 - p.2) with hW
  have hWc : Continuous W := (continuous_heatBand hd hα2).comp (continuous_fst.sub continuous_snd)
  have hWm : StronglyMeasurable W := hWc.stronglyMeasurable
  have hW2 : MemLp W 2 (μ.prod μ) := memLp_two_of_continuous_repulsive hWc
  have hfeven : ∀ z, f (-z) = f z := fun z => heatBand_neg _ _ z
  have hI : Integrable (fun p : Torus d × Torus d => f (p.1 - p.2)) (μ.prod μ) :=
    hW2.integrable one_le_two
  -- the master kernel is `2β` times the Hoeffding centring of `W`
  have hkey : ∀ p : Torus d × Torus d,
      masterKernel d α δ β μ p = 2 * β * DGRHS.Gaussian.hoeffdingCentered μ W p := by
    intro p
    have h := pairKernel_eq_hoeffdingCentered hfeven hI
    show 2 * β * pairKernel f μ p = 2 * β * DGRHS.Gaussian.hoeffdingCentered μ W p
    rw [h]
  -- row integrals of `W` against `μ` (uniform in `x`)
  have hrowae : ∀ᵐ x ∂μ, ∫ y, W (x, y) ^ 2 ∂μ ≤ bandRowControl d Λ δ :=
    ae_of_all _ fun x => row_sq_heatBand_le hd hμ hρ hΛ hα2 hab hδ x
  have hK := DGRHS.Gaussian.ae_row_sq_hoeffdingCentered_le μ W hWm hW2 (bandRowControl d Λ δ) hrowae
  have hJ := DGRHS.Gaussian.integral_sq_hoeffdingCentered_le μ W hWm hW2
  have hJW : ∫ p, W p ^ 2 ∂(μ.prod μ) ≤ bandRowControl d Λ δ := by
    rw [integral_prod _ hW2.integrable_sq]
    calc ∫ x, ∫ y, W (x, y) ^ 2 ∂μ ∂μ ≤ ∫ _x, bandRowControl d Λ δ ∂μ :=
          integral_mono_ae hW2.integrable_sq.integral_prod_left (integrable_const _) hrowae
      _ = bandRowControl d Λ δ := by simp
  -- joint second moment
  have hsecond : ∫ p, masterKernel d α δ β μ p ^ 2 ∂(μ.prod μ) ≤
      64 * β ^ 2 * bandRowControl d Λ δ := by
    calc ∫ p, masterKernel d α δ β μ p ^ 2 ∂(μ.prod μ)
        = ∫ p, (2 * β) ^ 2 * DGRHS.Gaussian.hoeffdingCentered μ W p ^ 2 ∂(μ.prod μ) := by
          refine integral_congr_ae (ae_of_all _ fun p => ?_)
          dsimp only
          rw [hkey p]
          ring
      _ = (2 * β) ^ 2 * ∫ p, DGRHS.Gaussian.hoeffdingCentered μ W p ^ 2 ∂(μ.prod μ) :=
          integral_const_mul _ _
      _ ≤ (2 * β) ^ 2 * (16 * ∫ p, W p ^ 2 ∂(μ.prod μ)) := mul_le_mul_of_nonneg_left hJ hβ2
      _ ≤ (2 * β) ^ 2 * (16 * bandRowControl d Λ δ) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hJW (by norm_num)) hβ2
      _ = 64 * β ^ 2 * bandRowControl d Λ δ := by ring
  -- row second moments
  have hrow1 : ∀ᵐ x ∂μ, ∫ y, masterKernel d α δ β μ (x, y) ^ 2 ∂μ ≤ 1 / L := by
    filter_upwards [hK] with x hx
    calc ∫ y, masterKernel d α δ β μ (x, y) ^ 2 ∂μ
        = (2 * β) ^ 2 * ∫ y, DGRHS.Gaussian.hoeffdingCentered μ W (x, y) ^ 2 ∂μ := by
          rw [← integral_const_mul]
          refine integral_congr_ae (ae_of_all _ fun y => ?_)
          dsimp only
          rw [hkey (x, y)]
          ring
      _ ≤ (2 * β) ^ 2 * (16 * bandRowControl d Λ δ) := mul_le_mul_of_nonneg_left hx hβ2
      _ = 64 * β ^ 2 * bandRowControl d Λ δ := by ring
      _ ≤ 1 / L := hrow
  refine ⟨hrow1, hsecond.trans hrow, fun h2 => ?_⟩
  -- operator norm
  have hn := DGRHS.Kernel.norm_integralOperator_le (masterKernel d α δ β μ) h2
  have hsq := DGRHS.Kernel.norm_toLp_sq h2
  have hs0 : 0 ≤ Real.sqrt (bandRowControl d Λ δ) := Real.sqrt_nonneg _
  have hss : Real.sqrt (bandRowControl d Λ δ) ^ 2 = bandRowControl d Λ δ := Real.sq_sqrt hR0
  have hnorm2 : ‖h2.toLp (masterKernel d α δ β μ)‖ ^ 2 ≤
      (8 * β * Real.sqrt (bandRowControl d Λ δ)) ^ 2 := by
    rw [hsq]
    calc ∫ p, masterKernel d α δ β μ p ^ 2 ∂(μ.prod μ) ≤ 64 * β ^ 2 * bandRowControl d Λ δ := hsecond
      _ = (8 * β * Real.sqrt (bandRowControl d Λ δ)) ^ 2 := by
          rw [mul_pow, mul_pow, hss]; ring
  have h8 : 0 ≤ 8 * β * Real.sqrt (bandRowControl d Λ δ) :=
    mul_nonneg (mul_nonneg (by norm_num) hβ) hs0
  have hnorm : ‖h2.toLp (masterKernel d α δ β μ)‖ ≤ 8 * β * Real.sqrt (bandRowControl d Λ δ) := by
    nlinarith [norm_nonneg (h2.toLp (masterKernel d α δ β μ))]
  exact hn.trans (hnorm.trans hop)

end Repulsive

end HRS

end
