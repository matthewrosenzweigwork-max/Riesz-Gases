/-
# HRS.Equilibrium.RepulsiveBand — package REP-02: heat-time bands of the periodic logarithm

Real analysis of the subordination formula `KernelAux.periodicRiesz_eq_integral` (`s = 0`):

  `g(x) = subA d 0 ∫_0^∞ t^{d/2-1} Ψ(x,t) dt`,  `Ψ(x,t) = psiFn x t = ∑_{k≠0} e^{-t|k|²} cos(2πk·x)`.

Contents: pointwise bounds on `Ψ` (positivity of `1 + Ψ` by Poisson summation `theta_images`,
the heat-trace bound `1 + Ψ(0,t) ≤ (π/t)^{d/2} Θ_d` for `t ≤ 1`, `|Ψ(x,t)| ≤ Ψ(0,t)`), the
three-piece decomposition `g = near + band + tail`, the sup bound of a band
`|heatBand d a b x| ≤ bandSupConst d · log(b/a)`, regularity, and the Fourier series of a band
and of the tail with nonnegative coefficients `bandCoeff`, `tailCoeff`.

Torus analogue of the Euclidean files `DGRHS/Gaussian/GaussianLogBand*.lean` (Gaussian heat
bands of the Euclidean logarithm).  `sorry`-ed specifications; see `docs/REPULSIVE_PLAN.md`.
-/
import HRS.Equilibrium.RepulsiveDefs

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS

namespace Repulsive

variable {d : ℕ}

/-! ### The constants -/

/-- `subA d 0 > 0` for `d ≥ 2` (`rieszConst d 0 > 0`, `Γ(d/2) > 0`). -/
theorem subA_zero_pos (hd : 2 ≤ d) : 0 < KernelAux.subA d 0 := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  unfold KernelAux.subA
  exact div_pos (mul_pos (HRS.rieszConst_pos (s := 0) hd le_rfl hd')
    (Real.rpow_pos_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi) _))
    (Real.Gamma_pos_of_pos (by linarith))

theorem summable_theta_aux (d : ℕ) :
    Summable fun m : Lattice d => Real.exp (-(Real.pi ^ 2 * Lattice.enorm m ^ 2)) := by
  refine (HRS.summable_gauss_lattice d (Real.pi ^ 2) (by positivity)).congr fun m => ?_
  rw [neg_mul]

theorem thetaConst_pos (d : ℕ) : 0 < thetaConst d := by
  unfold thetaConst
  exact Summable.tsum_pos (summable_theta_aux d) (fun m => (Real.exp_pos _).le) 0 (Real.exp_pos _)

theorem summable_thetaConst (d : ℕ) :
    Summable fun m : Lattice d => Real.exp (-(Real.pi ^ 2 * Lattice.enorm m ^ 2)) := by
  exact summable_theta_aux d

theorem bandSupConst_pos (hd : 2 ≤ d) : 0 < bandSupConst d := by
  unfold bandSupConst
  exact mul_pos (mul_pos (subA_zero_pos hd) (Real.rpow_pos_of_pos Real.pi_pos _)) (thetaConst_pos d)

/-- `heatWeight d t = t^{(d-0)/2-1}`: the weight of `periodicRiesz_eq_integral` at `s = 0`. -/
theorem heatWeight_eq (t : ℝ) : heatWeight d t = t ^ (((d : ℝ) - 0) / 2 - 1) := by
  simp [heatWeight]

theorem heatWeight_nonneg (t : ℝ) (ht : 0 ≤ t) : 0 ≤ heatWeight d t := by
  unfold heatWeight
  exact Real.rpow_nonneg ht _

/-- `∫_0^a t^{d/2-1} dt = (2/d) a^{d/2}` for `d ≥ 1`, `0 ≤ a`. -/
theorem integral_heatWeight (hd : 1 ≤ d) {a : ℝ} (ha : 0 ≤ a) :
    ∫ t in Ioc (0 : ℝ) a, heatWeight d t = (2 / (d : ℝ)) * a ^ ((d : ℝ) / 2) := by
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hdpos : (0 : ℝ) < (d : ℝ) / 2 := by linarith
  have hr : -1 < (d : ℝ) / 2 - 1 := by linarith
  have hd0 : (d : ℝ) ≠ 0 := ne_of_gt (by linarith)
  rw [← intervalIntegral.integral_of_le ha]
  unfold heatWeight
  rw [integral_rpow (Or.inl hr), show (d : ℝ) / 2 - 1 + 1 = (d : ℝ) / 2 by ring,
    Real.zero_rpow hdpos.ne', sub_zero]
  field_simp

/-! ### Pointwise bounds on `Ψ` -/

/-- `cos(2πk·0) = 1`. -/
theorem cosMode_zero_pt (k : Lattice d) : Torus.cosMode k (0 : Torus d) = 1 := by
  have h0 : (0 : Torus d) = Torus.mk (0 : Euc d) := by
    funext i
    simp [Torus.mk]
  rw [h0, Torus.cosMode_mk]
  simp [Lattice.dot]

/-- Every point of the torus is `boxPt y` for some `y ∈ ℝ^d` (`y = rep x`). -/
theorem exists_boxPt_eq (x : Torus d) : ∃ y : Fin d → ℝ, KernelAux.boxPt y = x :=
  ⟨fun i => Torus.rep x i, Torus.mk_rep x⟩

theorem psiFn_neg (x : Torus d) (u : ℝ) : psiFn (-x) u = psiFn x u := by
  unfold psiFn
  simp only [HRS.cosMode_neg]

/-- `1 + Ψ(x,t) = ∑_k e^{-t|k|²} cos(2πk·x) ≥ 0` (Poisson summation, `theta_images`). -/
theorem one_add_psiFn_nonneg (x : Torus d) {u : ℝ} (hu : 0 < u) : 0 ≤ 1 + psiFn x u := by
  obtain ⟨y, rfl⟩ := exists_boxPt_eq x
  rw [← HRS.psi_eq _ hu, KernelAux.theta_images y hu]
  exact mul_nonneg (by positivity) (tsum_nonneg fun _ => (Real.exp_pos _).le)

/-- `|Ψ(x,t)| ≤ Ψ(0,t) = ∑_{k≠0} e^{-t|k|²}`. -/
theorem abs_psiFn_le_psiFn_zero (x : Torus d) {u : ℝ} (hu : 0 < u) :
    |psiFn x u| ≤ psiFn (0 : Torus d) u := by
  have hsx := HRS.psi_summable x hu
  have hs0 := HRS.psi_summable (0 : Torus d) hu
  have hup : psiFn x u ≤ psiFn (0 : Torus d) u := by
    unfold psiFn
    refine Summable.tsum_le_tsum (fun k => ?_) hsx hs0
    by_cases hk : k = 0
    · simp [hk]
    · simp only [hk, ↓reduceIte, cosMode_zero_pt, mul_one]
      exact mul_le_of_le_one_right (Real.exp_pos _).le (le_trans (le_abs_self _) (HRS.abs_cosMode_le k x))
  have hlow : 0 ≤ psiFn x u + psiFn (0 : Torus d) u := by
    unfold psiFn
    rw [← (hsx.hasSum.add hs0.hasSum).tsum_eq]
    refine tsum_nonneg fun k => ?_
    by_cases hk : k = 0
    · simp [hk]
    · simp only [hk, ↓reduceIte, cosMode_zero_pt, mul_one]
      have hc := abs_le.mp (HRS.abs_cosMode_le k x)
      have he := Real.exp_pos (-u * Lattice.enorm k ^ 2)
      have := mul_nonneg he.le (by linarith [hc.1] : (0 : ℝ) ≤ Torus.cosMode k x + 1)
      linarith
  rw [abs_le]
  constructor <;> linarith

theorem psiFn_zero_nonneg {u : ℝ} (hu : 0 < u) : 0 ≤ psiFn (0 : Torus d) u := by
  unfold psiFn
  refine tsum_nonneg fun k => ?_
  by_cases hk : k = 0
  · simp [hk]
  · simp only [hk, ↓reduceIte, cosMode_zero_pt, mul_one]
    exact (Real.exp_pos _).le

/-- Heat-trace bound: `1 + Ψ(0,t) = ∑_k e^{-t|k|²} ≤ (π/t)^{d/2} Θ_d` for `0 < t ≤ 1`
(`theta_images` at `y = 0` and `e^{-π²|m|²/t} ≤ e^{-π²|m|²}`). -/
theorem one_add_psiFn_zero_le {u : ℝ} (hu : 0 < u) (hu1 : u ≤ 1) :
    1 + psiFn (0 : Torus d) u ≤ (Real.pi / u) ^ ((d : ℝ) / 2) * thetaConst d := by
  have hb : KernelAux.boxPt (0 : Fin d → ℝ) = (0 : Torus d) := by
    funext i
    simp [KernelAux.boxPt]
  have h := KernelAux.theta_images (0 : Fin d → ℝ) hu
  rw [hb] at h
  simp only [cosMode_zero_pt, mul_one, Pi.zero_apply, sub_zero] at h
  have h1 : 1 + psiFn (0 : Torus d) u = ∑' k : Lattice d, Real.exp (-u * Lattice.enorm k ^ 2) := by
    rw [← HRS.psi_eq (0 : Torus d) hu]
    simp only [cosMode_zero_pt, mul_one]
  have hsq : Real.sqrt (Real.pi / u) ^ d = (Real.pi / u) ^ ((d : ℝ) / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    congr 1
    ring
  have hle : ∀ m : Lattice d, Real.exp (-(Real.pi ^ 2 * ∑ i, (((m i : ℤ) : ℝ)) ^ 2 / u))
      ≤ Real.exp (-(Real.pi ^ 2 * Lattice.enorm m ^ 2)) := by
    intro m
    apply Real.exp_le_exp.mpr
    rw [enorm_sq]
    have hterm : ∑ i, (((m i : ℤ) : ℝ)) ^ 2 ≤ ∑ i, (((m i : ℤ) : ℝ)) ^ 2 / u :=
      Finset.sum_le_sum fun i _ => by
        rw [le_div_iff₀ hu]
        nlinarith [mul_nonneg (sq_nonneg (((m i : ℤ) : ℝ))) (sub_nonneg.mpr hu1)]
    exact neg_le_neg (mul_le_mul_of_nonneg_left hterm (sq_nonneg Real.pi))
  have hsumL : Summable fun m : Lattice d =>
      Real.exp (-(Real.pi ^ 2 * ∑ i, (((m i : ℤ) : ℝ)) ^ 2 / u)) :=
    Summable.of_nonneg_of_le (fun m => (Real.exp_pos _).le) hle (summable_theta_aux d)
  have htl : ∑' m : Lattice d, Real.exp (-(Real.pi ^ 2 * ∑ i, (((m i : ℤ) : ℝ)) ^ 2 / u))
      ≤ thetaConst d :=
    Summable.tsum_le_tsum hle hsumL (summable_theta_aux d)
  rw [h1, h, hsq]
  exact mul_le_mul_of_nonneg_left htl (by positivity)

/-- `Ψ(·,t)` is continuous for `t > 0` (uniformly convergent series). -/
theorem continuous_psiFn {u : ℝ} (hu : 0 < u) : Continuous fun x : Torus d => psiFn x u := by
  unfold psiFn
  refine continuous_tsum (fun k => ?_) (HRS.summable_gauss_lattice d u hu) (fun k x => ?_)
  · by_cases hk : k = 0
    · simp only [hk, ↓reduceIte]
      exact continuous_const
    · simp only [hk, ↓reduceIte]
      exact continuous_const.mul (Torus.continuous_cosMode k)
  · by_cases hk : k = 0
    · simp only [hk, ↓reduceIte, norm_zero]
      exact (Real.exp_pos _).le
    · simp only [hk, ↓reduceIte]
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
      exact mul_le_of_le_one_right (Real.exp_pos _).le (HRS.abs_cosMode_le k x)

/-- Joint measurability of `(x, t) ↦ Ψ(x, t)`. -/
theorem measurable_psiFn_uncurry :
    Measurable fun p : Torus d × ℝ => psiFn p.1 p.2 := by
  unfold psiFn
  refine Measurable.tsum fun k => ?_
  by_cases hk : k = 0
  · simp only [hk, ↓reduceIte]
    exact measurable_const
  · simp only [hk, ↓reduceIte]
    have hc : Continuous fun p : Torus d × ℝ => Real.exp (-p.2 * Lattice.enorm k ^ 2) :=
      Real.continuous_exp.comp (continuous_snd.neg.mul continuous_const)
    exact (hc.mul ((Torus.continuous_cosMode k).comp continuous_fst)).measurable

/-! ### Integrability in the heat time -/

/-- Away from the origin the full Mellin integrand is integrable on `(0, ∞)`
(`KernelAux.integrableOn_psi` with `s = 0`). -/
theorem integrableOn_heatWeight_psiFn (hd : 2 ≤ d) (x : Torus d) (hx : x ≠ 0) :
    IntegrableOn (fun t => heatWeight d t * psiFn x t) (Ioi 0) := by
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hsd : (0 : ℝ) < (d : ℝ) := by linarith
  have h := KernelAux.integrableOn_psi (d := d) (s := 0) hsd x hx
  simpa [heatWeight] using h

/-- For every `x` (including the origin) the Mellin integrand is integrable on `(a, ∞)`, `a > 0`
(`|Ψ(x,t)| ≤ Ψ(0,t)`, which is `O(e^{-t})` for `t ≥ 1` by `psi_large` and bounded on `[a, 1]`). -/
theorem integrableOn_heatWeight_psiFn_Ioi (hd : 2 ≤ d) (x : Torus d) {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun t => heatWeight d t * psiFn x t) (Ioi a) := by
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hdpos : (0 : ℝ) < (d : ℝ) / 2 := by linarith
  unfold heatWeight
  set S : ℝ := ∑' k : Lattice d, Real.exp (-a * Lattice.enorm k ^ 2) with hS
  -- uniform bound of `Ψ` on `[a, ∞)`, for every `x`
  have hbound : ∀ t : ℝ, a ≤ t → |psiFn x t| ≤ S := by
    intro t ht
    unfold psiFn
    rw [← Real.norm_eq_abs]
    refine tsum_of_norm_bounded (summable_gauss_lattice d a ha).hasSum (fun k => ?_)
    by_cases hk : k = 0
    · simp only [hk, ite_true, norm_zero]; positivity
    · simp only [hk, ite_false, Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
      have hexp : Real.exp (-t * Lattice.enorm k ^ 2) ≤ Real.exp (-a * Lattice.enorm k ^ 2) :=
        Real.exp_le_exp.mpr (by nlinarith [mul_nonneg (sub_nonneg.mpr ht) (sq_nonneg (Lattice.enorm k))])
      calc Real.exp (-t * Lattice.enorm k ^ 2) * |Torus.cosMode k x|
          ≤ Real.exp (-t * Lattice.enorm k ^ 2) * 1 := by gcongr; exact abs_cosMode_le k x
        _ = Real.exp (-t * Lattice.enorm k ^ 2) := mul_one _
        _ ≤ Real.exp (-a * Lattice.enorm k ^ 2) := hexp
  have hcont := psi_continuousOn x
  have hmeas0 : AEStronglyMeasurable (fun t : ℝ => t ^ ((d : ℝ) / 2 - 1) * psiFn x t)
      (volume.restrict (Ioi 0)) := by
    refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    exact ContinuousOn.mul (continuousOn_id.rpow_const fun t ht => Or.inl (ne_of_gt ht)) hcont
  have hp : -1 < (d : ℝ) / 2 - 1 := by linarith
  -- large times: exponential decay (`psi_large`)
  have hpart2 : ∀ b : ℝ, 1 ≤ b →
      IntegrableOn (fun t : ℝ => t ^ ((d : ℝ) / 2 - 1) * psiFn x t) (Ioi b) := by
    intro b hb
    obtain ⟨C, hC⟩ : ∃ C : ℝ, ∀ u : ℝ, 1 ≤ u → |psiFn x u| ≤ C * Real.exp (-u) :=
      ⟨_, fun u hu => KernelAux.psi_large x hu⟩
    have hg : IntegrableOn (fun t : ℝ => C * (Real.exp (-t) * t ^ ((d : ℝ) / 2 - 1))) (Ioi b) :=
      ((Real.GammaIntegral_convergent hdpos).mono_set (Ioi_subset_Ioi (zero_le_one.trans hb))).const_mul C
    refine Integrable.mono' hg (AEStronglyMeasurable.mono_set (Ioi_subset_Ioi (zero_le_one.trans hb)) hmeas0) ?_
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun t ht => ?_)
    have ht' : b < t := ht
    have ht1 : 1 ≤ t := le_trans hb ht'.le
    have ht0 : 0 < t := lt_of_lt_of_le one_pos ht1
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.rpow_pos_of_pos ht0 _)]
    calc t ^ ((d : ℝ) / 2 - 1) * |psiFn x t|
        ≤ t ^ ((d : ℝ) / 2 - 1) * (C * Real.exp (-t)) :=
          mul_le_mul_of_nonneg_left (hC t ht1) (Real.rpow_pos_of_pos ht0 _).le
      _ = C * (Real.exp (-t) * t ^ ((d : ℝ) / 2 - 1)) := by ring
  -- the initial piece `(a, max a 1]`: bounded integrand against an integrable power
  have hpart1 : IntegrableOn (fun t : ℝ => t ^ ((d : ℝ) / 2 - 1) * psiFn x t)
      (Ioc a (max a 1)) := by
    have hb0 : (0 : ℝ) ≤ max a 1 := le_trans zero_le_one (le_max_right a 1)
    have hint0 : IntegrableOn (fun t : ℝ => t ^ ((d : ℝ) / 2 - 1)) (Ioc a (max a 1)) :=
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le hb0).mp
        (intervalIntegral.intervalIntegrable_rpow' hp)).mono_set (Ioc_subset_Ioc_left ha.le)
    have hg : IntegrableOn (fun t : ℝ => S * t ^ ((d : ℝ) / 2 - 1)) (Ioc a (max a 1)) :=
      hint0.const_mul S
    refine Integrable.mono' hg
      (AEStronglyMeasurable.mono_set (Ioc_subset_Ioi_self.trans (Ioi_subset_Ioi ha.le)) hmeas0) ?_
    refine (ae_restrict_iff' measurableSet_Ioc).mpr (Filter.Eventually.of_forall fun t ht => ?_)
    have ht' : a < t := ht.1
    have ht0 : 0 < t := lt_trans ha ht'
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.rpow_pos_of_pos ht0 _)]
    calc t ^ ((d : ℝ) / 2 - 1) * |psiFn x t|
        ≤ t ^ ((d : ℝ) / 2 - 1) * S :=
          mul_le_mul_of_nonneg_left (hbound t ht'.le) (Real.rpow_pos_of_pos ht0 _).le
      _ = S * t ^ ((d : ℝ) / 2 - 1) := mul_comm _ _
  have hsplit : Ioi a = Ioc a (max a 1) ∪ Ioi (max a 1) :=
    (Ioc_union_Ioi_eq_Ioi (le_max_left a 1)).symm
  rw [hsplit]
  exact integrableOn_union.mpr ⟨hpart1, hpart2 (max a 1) (le_max_right a 1)⟩

theorem integrableOn_heatWeight_one_add_psiFn (hd : 2 ≤ d) (x : Torus d) (hx : x ≠ 0)
    {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun t => heatWeight d t * (1 + psiFn x t)) (Ioc 0 a) := by
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hp : -1 < (d : ℝ) / 2 - 1 := by linarith
  have h1 : IntegrableOn (fun t => heatWeight d t) (Ioc 0 a) := by
    unfold heatWeight
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le ha.le).mp
      (intervalIntegral.intervalIntegrable_rpow' hp)
  have h2 : IntegrableOn (fun t => heatWeight d t * psiFn x t) (Ioc 0 a) :=
    (integrableOn_heatWeight_psiFn hd x hx).mono_set Ioc_subset_Ioi_self
  have h3 : (fun t => heatWeight d t * (1 + psiFn x t))
      = fun t => heatWeight d t + heatWeight d t * psiFn x t := by
    funext t; ring
  rw [h3]
  exact h1.add h2

/-! ### The decomposition `g = near + band + tail` -/

/-- Three-piece decomposition of the periodic logarithm in heat time, `x ≠ 0`:
`g(x) = heatBand d 0 a x + heatBand d a b x + heatTail d b x` for `0 < a ≤ b`. -/
theorem heatBand_decomp (hd : 2 ≤ d) (x : Torus d) (hx : x ≠ 0) {a b : ℝ} (ha : 0 < a)
    (hab : a ≤ b) :
    periodicRiesz d 0 x = heatBand d 0 a x + heatBand d a b x + heatTail d b x := by
  have hsd : (0 : ℝ) < (d : ℝ) := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hP : periodicRiesz d 0 x
      = KernelAux.subA d 0 * ∫ t in Ioi (0 : ℝ), heatWeight d t * psiFn x t := by
    rw [KernelAux.periodicRiesz_eq_integral hd le_rfl hsd x hx]
    simp only [heatWeight, sub_zero]
  have hint := integrableOn_heatWeight_psiFn hd x hx
  have h0 : (0 : ℝ) ≤ a := ha.le
  have hI1 : IntegrableOn (fun t => heatWeight d t * psiFn x t) (Ioc 0 a) :=
    hint.mono_set Ioc_subset_Ioi_self
  have hI2 : IntegrableOn (fun t => heatWeight d t * psiFn x t) (Ioc a b) :=
    hint.mono_set (Ioc_subset_Ioi_self.trans (Ioi_subset_Ioi ha.le))
  have hI3 : IntegrableOn (fun t => heatWeight d t * psiFn x t) (Ioi b) :=
    hint.mono_set (Ioi_subset_Ioi (ha.le.trans hab))
  have e1 : Ioi (0 : ℝ) = (Ioc 0 a ∪ Ioc a b) ∪ Ioi b := by
    rw [Ioc_union_Ioc_eq_Ioc h0 hab, Ioc_union_Ioi_eq_Ioi (h0.trans hab)]
  have hsplit : ∫ t in Ioi (0 : ℝ), heatWeight d t * psiFn x t
      = (∫ t in Ioc 0 a, heatWeight d t * psiFn x t)
        + (∫ t in Ioc a b, heatWeight d t * psiFn x t)
        + ∫ t in Ioi b, heatWeight d t * psiFn x t := by
    rw [e1, setIntegral_union (Disjoint.union_left (Ioc_disjoint_Ioi hab) (Ioc_disjoint_Ioi le_rfl))
        measurableSet_Ioi (integrableOn_union.mpr ⟨hI1, hI2⟩) hI3,
      setIntegral_union (Ioc_disjoint_Ioc_of_le le_rfl) measurableSet_Ioc hI1 hI2]
  rw [hP]
  unfold heatBand heatTail
  rw [hsplit]
  ring

/-- The near field with the zero mode added back: `heatBand d 0 a = heatPos d a - heatPosMass d a`
off the origin. -/
theorem heatBand_zero_eq (hd : 2 ≤ d) (x : Torus d) (hx : x ≠ 0) {a : ℝ} (ha : 0 < a) :
    heatBand d 0 a x = heatPos d a x - heatPosMass d a := by
  have hd1 : 1 ≤ d := by omega
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hp : -1 < (d : ℝ) / 2 - 1 := by linarith
  have hw : IntegrableOn (fun t => heatWeight d t) (Ioc 0 a) := by
    unfold heatWeight
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le ha.le).mp
      (intervalIntegral.intervalIntegrable_rpow' hp)
  have hws : IntegrableOn (fun t => heatWeight d t * psiFn x t) (Ioc 0 a) :=
    (integrableOn_heatWeight_psiFn hd x hx).mono_set Ioc_subset_Ioi_self
  have hsplit : ∫ t in Ioc (0 : ℝ) a, heatWeight d t * (1 + psiFn x t)
      = (2 / (d : ℝ)) * a ^ ((d : ℝ) / 2)
        + ∫ t in Ioc (0 : ℝ) a, heatWeight d t * psiFn x t := by
    have h3 : (fun t => heatWeight d t * (1 + psiFn x t))
        = fun t => heatWeight d t + heatWeight d t * psiFn x t := by
      funext t; ring
    rw [h3, integral_add hw hws, integral_heatWeight hd1 ha.le]
  unfold heatBand heatPos heatPosMass
  rw [hsplit]
  ring

/-- Positivity of the near field with the zero mode (`1 + Ψ ≥ 0`, `subA d 0 > 0`). -/
theorem heatPos_nonneg (hd : 2 ≤ d) {a : ℝ} (ha : 0 ≤ a) (x : Torus d) : 0 ≤ heatPos d a x := by
  unfold heatPos
  refine mul_nonneg (subA_zero_pos hd).le (setIntegral_nonneg measurableSet_Ioc fun t ht => ?_)
  exact mul_nonneg (heatWeight_nonneg t ht.1.le) (one_add_psiFn_nonneg x ht.1)

theorem heatPosMass_nonneg (hd : 2 ≤ d) {a : ℝ} (ha : 0 ≤ a) : 0 ≤ heatPosMass d a := by
  unfold heatPosMass
  exact mul_nonneg (mul_nonneg (subA_zero_pos hd).le (by positivity)) (Real.rpow_nonneg ha _)

/-- `Λ · heatPosMass d (α²) = nearConst d Λ · α^d` for `0 ≤ α`. -/
theorem heatPosMass_sq (hd : 2 ≤ d) (Λ : ℝ) {α : ℝ} (hα : 0 ≤ α) :
    Λ * heatPosMass d (α ^ 2) = nearConst d Λ * α ^ (d : ℝ) := by
  unfold heatPosMass nearConst
  have h : ((α ^ 2 : ℝ)) ^ ((d : ℝ) / 2) = α ^ (d : ℝ) := by
    rw [← Real.rpow_two α, ← Real.rpow_mul hα, show (2 : ℝ) * ((d : ℝ) / 2) = d by ring]
  rw [h]
  ring

/-! ### Regularity and symmetry -/

theorem heatBand_neg (a b : ℝ) (x : Torus d) : heatBand d a b (-x) = heatBand d a b x := by
  unfold heatBand
  simp only [psiFn_neg]

theorem heatTail_neg (b : ℝ) (x : Torus d) : heatTail d b (-x) = heatTail d b x := by
  unfold heatTail
  simp only [psiFn_neg]

theorem heatPos_neg (a : ℝ) (x : Torus d) : heatPos d a (-x) = heatPos d a x := by
  unfold heatPos
  simp only [psiFn_neg]

/-- Continuity in `x` of `∫_S heatWeight · Ψ(x,t) dt` on a set `S` of positive times, by dominated
convergence with the bound `|Ψ(x,t)| ≤ Ψ(0,t)` (`abs_psiFn_le_psiFn_zero`). -/
theorem rb_continuous_integral {S : Set ℝ} (hS : MeasurableSet S) (hpos : ∀ t ∈ S, 0 < t)
    (hint : IntegrableOn (fun t => heatWeight d t * psiFn (0 : Torus d) t) S) :
    Continuous fun x : Torus d => ∫ t in S, heatWeight d t * psiFn x t := by
  have hw : Measurable (heatWeight d) := by
    unfold heatWeight
    fun_prop
  refine continuous_of_dominated (bound := fun t => heatWeight d t * psiFn (0 : Torus d) t)
    (fun x => ?_) (fun x => ?_) hint (ae_restrict_of_forall_mem hS fun t ht => ?_)
  · exact (hw.mul (measurable_psiFn_uncurry.comp (measurable_const.prodMk measurable_id))).aestronglyMeasurable
  · refine ae_restrict_of_forall_mem hS fun t ht => ?_
    have ht0 := hpos t ht
    have hw0 : 0 ≤ heatWeight d t := by
      unfold heatWeight
      exact Real.rpow_nonneg ht0.le _
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hw0]
    exact mul_le_mul_of_nonneg_left (abs_psiFn_le_psiFn_zero x ht0) hw0
  · exact continuous_const.mul (continuous_psiFn (hpos t ht))

/-- A band with `0 < a` is continuous (dominated convergence with the bound
`|heatWeight d t · Ψ(x,t)| ≤ heatWeight d t · Ψ(0,t)` on `(a, b]`). -/
theorem continuous_heatBand (hd : 2 ≤ d) {a b : ℝ} (ha : 0 < a) : Continuous (heatBand d a b) := by
  have e : heatBand d a b = fun x => KernelAux.subA d 0 *
      ∫ t in Set.Ioc a b, heatWeight d t * psiFn x t := rfl
  rw [e]
  exact continuous_const.mul (rb_continuous_integral measurableSet_Ioc (fun t ht => ha.trans ht.1)
    ((integrableOn_heatWeight_psiFn_Ioi hd (0 : Torus d) ha).mono_set Set.Ioc_subset_Ioi_self))

theorem continuous_heatTail (hd : 2 ≤ d) {b : ℝ} (hb : 0 < b) : Continuous (heatTail d b) := by
  have e : heatTail d b = fun x => KernelAux.subA d 0 *
      ∫ t in Set.Ioi b, heatWeight d t * psiFn x t := rfl
  rw [e]
  exact continuous_const.mul (rb_continuous_integral measurableSet_Ioi
    (fun t ht => hb.trans (Set.mem_Ioi.mp ht)) (integrableOn_heatWeight_psiFn_Ioi hd (0 : Torus d) hb))

/-- Measurability of `x ↦ ∫_S F(x, t) dt` for a jointly measurable `F`. -/
theorem rb_measurable_integral {S : Set ℝ} {F : Torus d × ℝ → ℝ} (hF : Measurable F) :
    Measurable fun x : Torus d => ∫ t in S, F (x, t) :=
  (hF.stronglyMeasurable.integral_prod_right').measurable

theorem measurable_heatPos (hd : 2 ≤ d) (a : ℝ) : Measurable (heatPos d a) := by
  have hw : Measurable (heatWeight d) := by
    unfold heatWeight
    fun_prop
  have hF : Measurable fun p : Torus d × ℝ => heatWeight d p.2 * (1 + psiFn p.1 p.2) :=
    (hw.comp measurable_snd).mul (measurable_const.add measurable_psiFn_uncurry)
  unfold heatPos
  exact (rb_measurable_integral hF).const_mul _

theorem measurable_heatBand (hd : 2 ≤ d) (a b : ℝ) : Measurable (heatBand d a b) := by
  have hw : Measurable (heatWeight d) := by
    unfold heatWeight
    fun_prop
  have hF : Measurable fun p : Torus d × ℝ => heatWeight d p.2 * psiFn p.1 p.2 :=
    (hw.comp measurable_snd).mul measurable_psiFn_uncurry
  unfold heatBand
  exact (rb_measurable_integral hF).const_mul _

/-! ### Sup bound of a band -/

/-- `|heatBand d a b x| ≤ bandSupConst d · log(b/a)` for `0 < a ≤ b ≤ 1`: from
`|Ψ(x,t)| ≤ 1 + Ψ(0,t) ≤ (π/t)^{d/2} Θ_d` and `t^{d/2-1} · t^{-d/2} = t^{-1}`. -/
theorem abs_heatBand_le (hd : 2 ≤ d) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : b ≤ 1)
    (x : Torus d) : |heatBand d a b x| ≤ bandSupConst d * Real.log (b / a) := by
  have hpt : ∀ t ∈ Set.Ioc a b,
      ‖heatWeight d t * psiFn x t‖ ≤ Real.pi ^ ((d : ℝ) / 2) * thetaConst d * t⁻¹ := by
    intro t ht
    have ht0 : 0 < t := ha.trans ht.1
    have ht1 : t ≤ 1 := ht.2.trans hb
    have hw0 : 0 ≤ heatWeight d t := by
      unfold heatWeight
      exact Real.rpow_nonneg ht0.le _
    have hpsi : |psiFn x t| ≤ (Real.pi / t) ^ ((d : ℝ) / 2) * thetaConst d := by
      have h1 := abs_psiFn_le_psiFn_zero x ht0
      have h2 := one_add_psiFn_zero_le (d := d) ht0 ht1
      linarith
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hw0]
    refine (mul_le_mul_of_nonneg_left hpsi hw0).trans (le_of_eq ?_)
    have htp : t ^ ((d : ℝ) / 2) ≠ 0 := (Real.rpow_pos_of_pos ht0 _).ne'
    unfold heatWeight
    rw [Real.rpow_sub_one ht0.ne', Real.div_rpow Real.pi_pos.le ht0.le]
    field_simp
  have hcont : ContinuousOn (fun t : ℝ => t⁻¹) (Set.Icc a b) := fun t ht =>
    (continuousAt_inv₀ (ne_of_gt (lt_of_lt_of_le ha ht.1))).continuousWithinAt
  have hint : IntegrableOn (fun t : ℝ => Real.pi ^ ((d : ℝ) / 2) * thetaConst d * t⁻¹) (Set.Ioc a b) :=
    ((hcont.integrableOn_compact isCompact_Icc).mono_set Set.Ioc_subset_Icc_self).const_mul _
  have key : |∫ t in Set.Ioc a b, heatWeight d t * psiFn x t|
      ≤ Real.pi ^ ((d : ℝ) / 2) * thetaConst d * Real.log (b / a) := by
    rw [← Real.norm_eq_abs]
    refine (norm_integral_le_of_norm_le hint (ae_restrict_of_forall_mem measurableSet_Ioc hpt)).trans
      (le_of_eq ?_)
    rw [integral_const_mul, ← intervalIntegral.integral_of_le hab,
      integral_inv_of_pos ha (ha.trans_le hab)]
  unfold heatBand bandSupConst
  rw [abs_mul, abs_of_pos (subA_zero_pos hd)]
  refine (mul_le_mul_of_nonneg_left key (subA_zero_pos hd).le).trans (le_of_eq ?_)
  ring

/-! ### Fourier series of band and tail -/

theorem rb_heatWeight_nonneg {t : ℝ} (ht : 0 < t) : 0 ≤ heatWeight d t := by
  unfold heatWeight
  exact Real.rpow_nonneg ht.le _

theorem rb_subA_nonneg (hd : 2 ≤ d) : 0 ≤ KernelAux.subA d 0 :=
  KernelAux.subA_nonneg hd le_rfl (Nat.cast_pos.mpr (by omega))

theorem bandCoeff_nonneg (hd : 2 ≤ d) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (k : Lattice d) :
    0 ≤ bandCoeff d a b k := by
  unfold bandCoeff
  split_ifs with hk
  · exact le_rfl
  · refine mul_nonneg (rb_subA_nonneg hd) (setIntegral_nonneg measurableSet_Ioc fun t ht => ?_)
    have ht0 : 0 < t := lt_of_le_of_lt ha ht.1
    exact mul_nonneg (rb_heatWeight_nonneg ht0) (Real.exp_pos _).le

theorem tailCoeff_nonneg (hd : 2 ≤ d) {b : ℝ} (hb : 0 ≤ b) (k : Lattice d) :
    0 ≤ tailCoeff d b k := by
  unfold tailCoeff
  split_ifs with hk
  · exact le_rfl
  · refine mul_nonneg (rb_subA_nonneg hd) (setIntegral_nonneg measurableSet_Ioi fun t ht => ?_)
    have ht0 : 0 < t := lt_of_le_of_lt hb (Set.mem_Ioi.mp ht)
    exact mul_nonneg (rb_heatWeight_nonneg ht0) (Real.exp_pos _).le

theorem bandCoeff_zero (a b : ℝ) : bandCoeff d a b 0 = 0 := by
  simp [bandCoeff]

theorem tailCoeff_zero (b : ℝ) : tailCoeff d b 0 = 0 := by
  simp [tailCoeff]

theorem rb_heatWeight_le (hd : 2 ≤ d) {t b : ℝ} (ht : 0 < t) (htb : t ≤ b) :
    heatWeight d t ≤ b ^ ((d : ℝ) / 2 - 1) := by
  unfold heatWeight
  have h2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  exact Real.rpow_le_rpow ht.le htb (by linarith)

theorem rb_band_pointwise (hd : 2 ≤ d) {a b : ℝ} (ha : 0 < a) (k : Lattice d) {t : ℝ}
    (ht : t ∈ Set.Ioc a b) :
    heatWeight d t * Real.exp (-t * Lattice.enorm k ^ 2) ≤
      b ^ ((d : ℝ) / 2 - 1) * Real.exp (-a * Lattice.enorm k ^ 2) := by
  have ht0 : 0 < t := ha.trans ht.1
  have hw := rb_heatWeight_le hd ht0 ht.2
  have hE : Real.exp (-t * Lattice.enorm k ^ 2) ≤ Real.exp (-a * Lattice.enorm k ^ 2) :=
    Real.exp_le_exp.mpr (by nlinarith [mul_nonneg (sub_nonneg.2 ht.1.le) (sq_nonneg (Lattice.enorm k))])
  have hB : 0 ≤ b ^ ((d : ℝ) / 2 - 1) := Real.rpow_nonneg (ht0.le.trans ht.2) _
  exact mul_le_mul hw hE (Real.exp_pos _).le hB

theorem rb_band_bound (hd : 2 ≤ d) {a b : ℝ} (ha : 0 < a) (x : Torus d) (k : Lattice d)
    {t : ℝ} (ht : t ∈ Set.Ioc a b) :
    ‖heatWeight d t * (if k = 0 then 0 else Real.exp (-t * Lattice.enorm k ^ 2) * Torus.cosMode k x)‖ ≤
      b ^ ((d : ℝ) / 2 - 1) * Real.exp (-a * Lattice.enorm k ^ 2) := by
  have ht0 : 0 < t := ha.trans ht.1
  have hB : 0 ≤ b ^ ((d : ℝ) / 2 - 1) := Real.rpow_nonneg (ht0.le.trans ht.2) _
  have hM : 0 ≤ b ^ ((d : ℝ) / 2 - 1) * Real.exp (-a * Lattice.enorm k ^ 2) :=
    mul_nonneg hB (Real.exp_pos _).le
  by_cases hk : k = 0
  · rw [if_pos hk, mul_zero, norm_zero]
    exact hM
  · rw [if_neg hk, Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (rb_heatWeight_nonneg ht0),
      abs_of_pos (Real.exp_pos _)]
    calc heatWeight d t * (Real.exp (-t * Lattice.enorm k ^ 2) * |Torus.cosMode k x|)
        ≤ heatWeight d t * (Real.exp (-t * Lattice.enorm k ^ 2) * 1) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (abs_cosMode_le k x) (Real.exp_pos _).le)
            (rb_heatWeight_nonneg ht0)
      _ = heatWeight d t * Real.exp (-t * Lattice.enorm k ^ 2) := by rw [mul_one]
      _ ≤ _ := rb_band_pointwise hd ha k ht

theorem rb_tail_pointwise {b : ℝ} (hb : 0 < b) (k : Lattice d) (hk : k ≠ 0) {t : ℝ} (ht : b < t) :
    heatWeight d t * Real.exp (-t * Lattice.enorm k ^ 2) ≤
      Real.exp b * Real.exp (-b * Lattice.enorm k ^ 2) * (Real.exp (-t) * t ^ ((d : ℝ) / 2 - 1)) := by
  have hw0 : 0 ≤ heatWeight d t := rb_heatWeight_nonneg (hb.trans ht)
  have he1 : 1 ≤ Lattice.enorm k ^ 2 := by nlinarith [one_le_enorm k hk]
  have hE : Real.exp (-t * Lattice.enorm k ^ 2) ≤
      Real.exp b * Real.exp (-b * Lattice.enorm k ^ 2) * Real.exp (-t) := by
    rw [← Real.exp_add, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith [mul_nonneg (sub_nonneg.2 ht.le) (sub_nonneg.2 he1)]
  calc heatWeight d t * Real.exp (-t * Lattice.enorm k ^ 2)
      ≤ heatWeight d t * (Real.exp b * Real.exp (-b * Lattice.enorm k ^ 2) * Real.exp (-t)) :=
        mul_le_mul_of_nonneg_left hE hw0
    _ = Real.exp b * Real.exp (-b * Lattice.enorm k ^ 2) * (Real.exp (-t) * t ^ ((d : ℝ) / 2 - 1)) := by
        unfold heatWeight; ring

theorem rb_tail_bound {b : ℝ} (hb : 0 < b) (x : Torus d) (k : Lattice d) {t : ℝ} (ht : b < t) :
    ‖heatWeight d t * (if k = 0 then 0 else Real.exp (-t * Lattice.enorm k ^ 2) * Torus.cosMode k x)‖ ≤
      Real.exp b * Real.exp (-b * Lattice.enorm k ^ 2) * (Real.exp (-t) * t ^ ((d : ℝ) / 2 - 1)) := by
  have ht0 : 0 < t := hb.trans ht
  have hw0 : 0 ≤ heatWeight d t := rb_heatWeight_nonneg ht0
  have hM : 0 ≤ Real.exp b * Real.exp (-b * Lattice.enorm k ^ 2) *
      (Real.exp (-t) * t ^ ((d : ℝ) / 2 - 1)) :=
    mul_nonneg (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)
      (mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg ht0.le _))
  by_cases hk : k = 0
  · rw [if_pos hk, mul_zero, norm_zero]
    exact hM
  · rw [if_neg hk, Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hw0, abs_of_pos (Real.exp_pos _)]
    calc heatWeight d t * (Real.exp (-t * Lattice.enorm k ^ 2) * |Torus.cosMode k x|)
        ≤ heatWeight d t * (Real.exp (-t * Lattice.enorm k ^ 2) * 1) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (abs_cosMode_le k x) (Real.exp_pos _).le) hw0
      _ = heatWeight d t * Real.exp (-t * Lattice.enorm k ^ 2) := by rw [mul_one]
      _ ≤ _ := rb_tail_pointwise hb k hk ht

/-- `∑_{k≠0} ∫_a^b t^{d/2-1} e^{-t|k|²} dt < ∞` for `a > 0` (`∑_{k≠0} e^{-a|k|²} < ∞`). -/
theorem summable_bandCoeff (hd : 2 ≤ d) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    Summable (bandCoeff d a b) := by
  have hbd : ∀ k : Lattice d, bandCoeff d a b k ≤
      KernelAux.subA d 0 * ((b - a) * (b ^ ((d : ℝ) / 2 - 1) * Real.exp (-a * Lattice.enorm k ^ 2))) := by
    intro k
    by_cases hk : k = 0
    · rw [show bandCoeff d a b k = 0 by simp [bandCoeff, hk]]
      exact mul_nonneg (rb_subA_nonneg hd) (mul_nonneg (sub_nonneg.2 hab)
        (mul_nonneg (Real.rpow_nonneg (lt_of_lt_of_le ha hab).le _) (Real.exp_pos _).le))
    · unfold bandCoeff
      rw [if_neg hk]
      refine mul_le_mul_of_nonneg_left ?_ (rb_subA_nonneg hd)
      calc ∫ t in Set.Ioc a b, heatWeight d t * Real.exp (-t * Lattice.enorm k ^ 2)
          ≤ ∫ t in Set.Ioc a b, b ^ ((d : ℝ) / 2 - 1) * Real.exp (-a * Lattice.enorm k ^ 2) :=
            integral_mono_of_nonneg
              (ae_restrict_of_forall_mem measurableSet_Ioc fun t ht =>
                mul_nonneg (rb_heatWeight_nonneg (ha.trans ht.1)) (Real.exp_pos _).le)
              (integrableOn_const measure_Ioc_lt_top.ne)
              (ae_restrict_of_forall_mem measurableSet_Ioc fun t ht => rb_band_pointwise hd ha k ht)
        _ = (b - a) * (b ^ ((d : ℝ) / 2 - 1) * Real.exp (-a * Lattice.enorm k ^ 2)) := by
            rw [setIntegral_const, Real.volume_real_Ioc_of_le hab, smul_eq_mul]
  refine Summable.of_nonneg_of_le (fun k => bandCoeff_nonneg hd ha.le hab k) hbd ?_
  exact (((summable_gauss_lattice d a ha).mul_left (b ^ ((d : ℝ) / 2 - 1))).mul_left (b - a)).mul_left
    (KernelAux.subA d 0)

/-- `∑_k ∫_{(b,∞)} t^{d/2-1} e^{-t|k|²} dt < ∞` for `b > 0` (`e^{-t|k|²} ≤ e^{-t} e^{b} e^{-b|k|²}`
for `t ≥ b`, `|k| ≥ 1`, and `∫_b^∞ t^{d/2-1} e^{-t} dt < ∞`). -/
theorem summable_tailCoeff (hd : 2 ≤ d) {b : ℝ} (hb : 0 < b) : Summable (tailCoeff d b) := by
  have hpos : (0 : ℝ) < (d : ℝ) / 2 := by
    have h2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hG : IntegrableOn (fun t : ℝ => Real.exp (-t) * t ^ ((d : ℝ) / 2 - 1)) (Set.Ioi b) :=
    (Real.GammaIntegral_convergent hpos).mono_set (Set.Ioi_subset_Ioi hb.le)
  obtain ⟨C0, hC0⟩ : ∃ C0 : ℝ, C0 = ∫ t in Set.Ioi b, Real.exp (-t) * t ^ ((d : ℝ) / 2 - 1) :=
    ⟨_, rfl⟩
  have hC0nn : 0 ≤ C0 := by
    rw [hC0]
    exact setIntegral_nonneg measurableSet_Ioi fun t ht =>
      mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg (hb.le.trans (Set.mem_Ioi.mp ht).le) _)
  have hbd : ∀ k : Lattice d, tailCoeff d b k ≤
      KernelAux.subA d 0 * ((Real.exp b * C0) * Real.exp (-b * Lattice.enorm k ^ 2)) := by
    intro k
    by_cases hk : k = 0
    · rw [show tailCoeff d b k = 0 by simp [tailCoeff, hk]]
      exact mul_nonneg (rb_subA_nonneg hd)
        (mul_nonneg (mul_nonneg (Real.exp_pos _).le hC0nn) (Real.exp_pos _).le)
    · unfold tailCoeff
      rw [if_neg hk]
      refine mul_le_mul_of_nonneg_left ?_ (rb_subA_nonneg hd)
      calc ∫ t in Set.Ioi b, heatWeight d t * Real.exp (-t * Lattice.enorm k ^ 2)
          ≤ ∫ t in Set.Ioi b, Real.exp b * Real.exp (-b * Lattice.enorm k ^ 2) *
              (Real.exp (-t) * t ^ ((d : ℝ) / 2 - 1)) :=
            integral_mono_of_nonneg
              (ae_restrict_of_forall_mem measurableSet_Ioi fun t ht =>
                mul_nonneg (rb_heatWeight_nonneg (hb.trans (Set.mem_Ioi.mp ht))) (Real.exp_pos _).le)
              (Integrable.const_mul hG _)
              (ae_restrict_of_forall_mem measurableSet_Ioi fun t ht =>
                rb_tail_pointwise hb k hk (Set.mem_Ioi.mp ht))
        _ = Real.exp b * Real.exp (-b * Lattice.enorm k ^ 2) * C0 := by
            rw [integral_const_mul, hC0]
        _ = (Real.exp b * C0) * Real.exp (-b * Lattice.enorm k ^ 2) := by ring
  refine Summable.of_nonneg_of_le (fun k => tailCoeff_nonneg hd hb.le k) hbd ?_
  exact ((summable_gauss_lattice d b hb).mul_left (Real.exp b * C0)).mul_left (KernelAux.subA d 0)

/-- Exchange of the lattice sum with a heat-time integral against a fixed weight `w`, by dominated
convergence (`integral_tsum_of_summable_integral_norm`) with a summable family of bounds `M k`. -/
theorem rb_integral_psi_eq_tsum {S : Set ℝ} (hS : MeasurableSet S) (x : Torus d) {w : ℝ → ℝ}
    (hw : Measurable w) (M : Lattice d → ℝ → ℝ) (hMint : ∀ k, IntegrableOn (M k) S)
    (hMsum : Summable fun k => ∫ t in S, M k t)
    (hMbd : ∀ k, ∀ t ∈ S,
      ‖w t * (if k = 0 then 0 else Real.exp (-t * Lattice.enorm k ^ 2) * Torus.cosMode k x)‖ ≤ M k t) :
    ∫ t in S, w t * psiFn x t =
      ∑' k : Lattice d, ∫ t in S, w t * (if k = 0 then 0 else
        Real.exp (-t * Lattice.enorm k ^ 2) * Torus.cosMode k x) := by
  have hFm : ∀ k : Lattice d, Measurable fun t =>
      w t * (if k = 0 then 0 else Real.exp (-t * Lattice.enorm k ^ 2) * Torus.cosMode k x) := by
    intro k
    by_cases hk : k = 0
    · simp only [if_pos hk, mul_zero]
      exact measurable_const
    · simp only [if_neg hk]
      exact hw.mul (by fun_prop)
  have hFint : ∀ k : Lattice d, Integrable (fun t =>
      w t * (if k = 0 then 0 else Real.exp (-t * Lattice.enorm k ^ 2) * Torus.cosMode k x))
      (volume.restrict S) :=
    fun k => Integrable.mono' (hMint k) (hFm k).aestronglyMeasurable
      (ae_restrict_of_forall_mem hS fun t ht => hMbd k t ht)
  have hFsum : Summable fun k : Lattice d => ∫ t in S,
      ‖w t * (if k = 0 then 0 else Real.exp (-t * Lattice.enorm k ^ 2) * Torus.cosMode k x)‖ :=
    Summable.of_nonneg_of_le (fun k => integral_nonneg fun t => norm_nonneg _)
      (fun k => integral_mono_of_nonneg (ae_restrict_of_forall_mem hS fun t _ => norm_nonneg _)
        (hMint k) (ae_restrict_of_forall_mem hS fun t ht => hMbd k t ht)) hMsum
  have hpt : ∀ t, w t * psiFn x t = ∑' k : Lattice d,
      w t * (if k = 0 then 0 else Real.exp (-t * Lattice.enorm k ^ 2) * Torus.cosMode k x) := by
    intro t
    unfold psiFn
    rw [tsum_mul_left]
  calc ∫ t in S, w t * psiFn x t = ∫ t in S, ∑' k : Lattice d,
        w t * (if k = 0 then 0 else Real.exp (-t * Lattice.enorm k ^ 2) * Torus.cosMode k x) := by
        congr 1
        funext t
        exact hpt t
    _ = _ := (integral_tsum_of_summable_integral_norm hFint hFsum).symm

/-- Fourier series of a band (`0 < a`), valid at every `x` (Tonelli/Fubini in `(k, t)`). -/
theorem heatBand_eq_tsum (hd : 2 ≤ d) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (x : Torus d) :
    heatBand d a b x = ∑' k : Lattice d, bandCoeff d a b k * Torus.cosMode k x := by
  have hw : Measurable (heatWeight d) := by
    unfold heatWeight
    fun_prop
  have hMint : ∀ k : Lattice d, IntegrableOn
      (fun _ : ℝ => b ^ ((d : ℝ) / 2 - 1) * Real.exp (-a * Lattice.enorm k ^ 2)) (Set.Ioc a b) :=
    fun k => integrableOn_const measure_Ioc_lt_top.ne
  have hMsum : Summable fun k : Lattice d => ∫ t in Set.Ioc a b,
      b ^ ((d : ℝ) / 2 - 1) * Real.exp (-a * Lattice.enorm k ^ 2) := by
    have e : (fun k : Lattice d => ∫ t in Set.Ioc a b,
        b ^ ((d : ℝ) / 2 - 1) * Real.exp (-a * Lattice.enorm k ^ 2)) =
        fun k => (b - a) * (b ^ ((d : ℝ) / 2 - 1) * Real.exp (-a * Lattice.enorm k ^ 2)) := by
      funext k
      rw [setIntegral_const, Real.volume_real_Ioc_of_le hab, smul_eq_mul]
    rw [e]
    exact ((summable_gauss_lattice d a ha).mul_left (b ^ ((d : ℝ) / 2 - 1))).mul_left (b - a)
  have key := rb_integral_psi_eq_tsum (d := d) (M := fun k _ =>
      b ^ ((d : ℝ) / 2 - 1) * Real.exp (-a * Lattice.enorm k ^ 2))
    measurableSet_Ioc x hw hMint hMsum (fun k t ht => rb_band_bound hd ha x k ht)
  unfold heatBand
  rw [key, ← tsum_mul_left]
  refine tsum_congr fun k => ?_
  by_cases hk : k = 0
  · simp [hk, bandCoeff]
  · simp only [bandCoeff, if_neg hk]
    have e2 : ∀ t : ℝ, heatWeight d t * (Real.exp (-t * Lattice.enorm k ^ 2) * Torus.cosMode k x) =
        heatWeight d t * Real.exp (-t * Lattice.enorm k ^ 2) * Torus.cosMode k x :=
      fun t => by ring
    simp only [e2]
    rw [integral_mul_const]
    ring

/-- Fourier series of the tail (`0 < b`), valid at every `x`. -/
theorem heatTail_eq_tsum (hd : 2 ≤ d) {b : ℝ} (hb : 0 < b) (x : Torus d) :
    heatTail d b x = ∑' k : Lattice d, tailCoeff d b k * Torus.cosMode k x := by
  have hpos : (0 : ℝ) < (d : ℝ) / 2 := by
    have h2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hw : Measurable (heatWeight d) := by
    unfold heatWeight
    fun_prop
  have hG : IntegrableOn (fun t : ℝ => Real.exp (-t) * t ^ ((d : ℝ) / 2 - 1)) (Set.Ioi b) :=
    (Real.GammaIntegral_convergent hpos).mono_set (Set.Ioi_subset_Ioi hb.le)
  obtain ⟨C0, hC0⟩ : ∃ C0 : ℝ, C0 = ∫ t in Set.Ioi b, Real.exp (-t) * t ^ ((d : ℝ) / 2 - 1) :=
    ⟨_, rfl⟩
  have hMint : ∀ k : Lattice d, IntegrableOn (fun t : ℝ => Real.exp b *
      Real.exp (-b * Lattice.enorm k ^ 2) * (Real.exp (-t) * t ^ ((d : ℝ) / 2 - 1))) (Set.Ioi b) :=
    fun k => Integrable.const_mul hG _
  have hMsum : Summable fun k : Lattice d => ∫ t in Set.Ioi b, Real.exp b *
      Real.exp (-b * Lattice.enorm k ^ 2) * (Real.exp (-t) * t ^ ((d : ℝ) / 2 - 1)) := by
    have e : (fun k : Lattice d => ∫ t in Set.Ioi b, Real.exp b *
        Real.exp (-b * Lattice.enorm k ^ 2) * (Real.exp (-t) * t ^ ((d : ℝ) / 2 - 1))) =
        fun k => (Real.exp b * C0) * Real.exp (-b * Lattice.enorm k ^ 2) := by
      funext k
      rw [integral_const_mul, ← hC0]
      ring
    rw [e]
    exact (summable_gauss_lattice d b hb).mul_left (Real.exp b * C0)
  have key := rb_integral_psi_eq_tsum (d := d) (M := fun k t => Real.exp b *
      Real.exp (-b * Lattice.enorm k ^ 2) * (Real.exp (-t) * t ^ ((d : ℝ) / 2 - 1)))
    measurableSet_Ioi x hw hMint hMsum (fun k t ht => rb_tail_bound hb x k ht)
  unfold heatTail
  rw [key, ← tsum_mul_left]
  refine tsum_congr fun k => ?_
  by_cases hk : k = 0
  · simp [hk, tailCoeff]
  · simp only [tailCoeff, if_neg hk]
    have e2 : ∀ t : ℝ, heatWeight d t * (Real.exp (-t * Lattice.enorm k ^ 2) * Torus.cosMode k x) =
        heatWeight d t * Real.exp (-t * Lattice.enorm k ^ 2) * Torus.cosMode k x :=
      fun t => by ring
    simp only [e2]
    rw [integral_mul_const]
    ring

theorem rb_cosMode_zero (k : Lattice d) : Torus.cosMode k (0 : Torus d) = 1 := by
  simp [Torus.cosMode, Torus.mode, UnitAddTorus.mFourier]

/-- The value at the origin is the sum of the coefficients. -/
theorem heatBand_zero_eq_tsum (hd : 2 ≤ d) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    heatBand d a b 0 = ∑' k : Lattice d, bandCoeff d a b k := by
  rw [heatBand_eq_tsum hd ha hab 0]
  refine tsum_congr fun k => ?_
  rw [rb_cosMode_zero, mul_one]

theorem heatTail_zero_eq_tsum (hd : 2 ≤ d) {b : ℝ} (hb : 0 < b) :
    heatTail d b 0 = ∑' k : Lattice d, tailCoeff d b k := by
  rw [heatTail_eq_tsum hd hb 0]
  refine tsum_congr fun k => ?_
  rw [rb_cosMode_zero, mul_one]

/-- The tail is bounded by its value at the origin (nonnegative coefficients). -/
theorem abs_heatTail_le (hd : 2 ≤ d) {b : ℝ} (hb : 0 < b) (x : Torus d) :
    |heatTail d b x| ≤ heatTail d b 0 := by
  have hle : |∫ t in Set.Ioi b, heatWeight d t * psiFn x t|
      ≤ ∫ t in Set.Ioi b, heatWeight d t * psiFn (0 : Torus d) t := by
    rw [← Real.norm_eq_abs]
    refine norm_integral_le_of_norm_le (integrableOn_heatWeight_psiFn_Ioi hd (0 : Torus d) hb)
      (ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => ?_)
    have ht0 : 0 < t := hb.trans (Set.mem_Ioi.mp ht)
    have hw0 : 0 ≤ heatWeight d t := by
      unfold heatWeight
      exact Real.rpow_nonneg ht0.le _
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hw0]
    exact mul_le_mul_of_nonneg_left (abs_psiFn_le_psiFn_zero x ht0) hw0
  unfold heatTail
  rw [abs_mul, abs_of_pos (subA_zero_pos hd)]
  exact mul_le_mul_of_nonneg_left hle (subA_zero_pos hd).le

end Repulsive

end HRS

end
