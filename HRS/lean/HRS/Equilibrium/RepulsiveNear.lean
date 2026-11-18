/-
# HRS.Equilibrium.RepulsiveNear — package REP-03: the near field against a bounded density

The near field `heatPos d a ≥ 0` has Haar mass `heatPosMass d a = subA d 0 (2/d) a^{d/2}`.
Against `μ = ρ dx` with `0 ≤ ρ ≤ Λ`, its one-body potential is `0 ≤ heatPos*μ ≤ Λ heatPosMass`,
and the negative statistic of its centred kernel is at most `N Λ heatPosMass d a`
(DGR Lemma `lem:logShortRange`, Euclidean Lean `DGRHS.Gaussian.gaussianLogShort*`).

`sorry`-ed specifications; see `docs/REPULSIVE_PLAN.md` (REP-03).
-/
import HRS.Equilibrium.RepulsiveBridge
import HRS.Equilibrium.RepulsiveBand

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS

namespace Repulsive

variable {d : ℕ} {ρ : Torus d → ℝ} {Λ : ℝ} {μ : Measure (Torus d)}

/-- Joint measurability of the heat-time integrand `(x, t) ↦ t^{d/2-1} (1 + Ψ(x, t))`. -/
theorem measurable_heatInt_aux :
    Measurable fun p : Torus d × ℝ => heatWeight d p.2 * (1 + psiFn p.1 p.2) := by
  unfold heatWeight
  exact (measurable_snd.pow_const _).mul (measurable_const.add measurable_psiFn_uncurry)

/-- The near field is nonnegative at every point (the integrand is nonnegative on `(0, a]`). -/
theorem heatPos_nonneg_aux (hd : 2 ≤ d) {a : ℝ} (ha : 0 ≤ a) (x : Torus d) : 0 ≤ heatPos d a x :=
  mul_nonneg (subA_zero_pos hd).le
    (setIntegral_nonneg measurableSet_Ioc fun t ht =>
      mul_nonneg (rb_heatWeight_nonneg ht.1) (one_add_psiFn_nonneg x ht.1))

theorem heatPosMass_nonneg_aux (hd : 2 ≤ d) {a : ℝ} (ha : 0 ≤ a) : 0 ≤ heatPosMass d a := by
  unfold heatPosMass
  exact mul_nonneg (mul_nonneg (subA_zero_pos hd).le (by positivity)) (Real.rpow_nonneg ha _)

/-- Measurability of the near field. -/
theorem heatPos_measurable_aux (a : ℝ) : Measurable (heatPos d a) := by
  have h : heatPos d a = fun x : Torus d => KernelAux.subA d 0 *
      ∫ t, heatWeight d t * (1 + psiFn x t) ∂(volume.restrict (Ioc (0 : ℝ) a)) := rfl
  rw [h]
  exact ((measurable_heatInt_aux (d := d)).stronglyMeasurable.integral_prod_right'
    (ν := volume.restrict (Ioc (0 : ℝ) a))).measurable.const_mul _

theorem integrable_one_add_psiFn_aux {t : ℝ} (ht : 0 < t) :
    Integrable (fun x : Torus d => 1 + psiFn x t) :=
  (integrable_const (1 : ℝ)).add
    ((continuous_psiFn (d := d) ht).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))

/-- Mean zero of a nonzero cosine mode on the torus. -/
theorem integral_cosMode_aux {k : Lattice d} (hk : k ≠ 0) :
    ∫ x : Torus d, Torus.cosMode k x = 0 := by
  have h1 : ∫ x : Torus d, Torus.cosMode k x = RCLike.re (∫ x : Torus d, Torus.mode k x) := by
    rw [← integral_re (Torus.integrable_mode k)]
    rfl
  rw [h1, Torus.integral_mode, if_neg hk]
  simp

/-- `∫_𝕋 Ψ(x, t) dx = 0` for `t > 0` (each nonzero mode has mean zero). -/
theorem integral_psiFn_aux {t : ℝ} (ht : 0 < t) : ∫ x : Torus d, psiFn x t = 0 := by
  set c : Lattice d → ℝ := fun k => if k = 0 then 0 else Real.exp (-t * Lattice.enorm k ^ 2) with hc
  set F : Lattice d → Torus d → ℝ := fun k x => c k * Torus.cosMode k x with hF
  have hpt : ∀ x : Torus d, psiFn x t = ∑' k, F k x := by
    intro x
    unfold psiFn
    refine tsum_congr fun k => ?_
    by_cases hk : k = 0 <;> simp [hF, hc, hk]
  have hFint : ∀ k, Integrable (F k) := fun k =>
    (continuous_const.mul (Torus.continuous_cosMode k)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hbd : ∀ k (x : Torus d), ‖F k x‖ ≤ c k := by
    intro k x
    have hc0 : 0 ≤ c k := by
      by_cases hk : k = 0 <;> simp [hc, hk, (Real.exp_pos _).le]
    show ‖c k * Torus.cosMode k x‖ ≤ c k
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hc0]
    exact mul_le_of_le_one_right hc0 (HRS.abs_cosMode_le k x)
  have hcle : ∀ k, c k ≤ Real.exp (-t * Lattice.enorm k ^ 2) := by
    intro k
    by_cases hk : k = 0 <;> simp [hc, hk, (Real.exp_pos _).le]
  have hcsum : Summable fun k : Lattice d => ∫ x : Torus d, ‖F k x‖ := by
    refine Summable.of_nonneg_of_le (fun k => integral_nonneg fun x => norm_nonneg _)
      (fun k => ?_) (summable_gauss_lattice d t ht)
    calc ∫ x : Torus d, ‖F k x‖ ≤ ∫ _x : Torus d, c k :=
          integral_mono (hFint k).norm (integrable_const _) (fun x => hbd k x)
      _ = c k := by simp
      _ ≤ _ := by exact hcle k
  have hint : ∫ x : Torus d, psiFn x t = ∑' k : Lattice d, ∫ x : Torus d, F k x := by
    simp_rw [hpt]
    exact (integral_tsum_of_summable_integral_norm hFint hcsum).symm
  have hz : ∀ k : Lattice d, ∫ x : Torus d, F k x = 0 := by
    intro k
    by_cases hk : k = 0
    · simp [hF, hc, hk]
    · show ∫ x : Torus d, c k * Torus.cosMode k x = 0
      rw [integral_const_mul, integral_cosMode_aux hk, mul_zero]
  rw [hint]
  simp [hz]

/-- `∫_𝕋 (1 + Ψ(x, t)) dx = 1` for `t > 0`. -/
theorem integral_one_add_psiFn_aux {t : ℝ} (ht : 0 < t) :
    ∫ x : Torus d, (1 + psiFn x t) = 1 := by
  have hpsi : Integrable (fun x : Torus d => psiFn x t) :=
    (continuous_psiFn (d := d) ht).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  rw [integral_add (integrable_const _) hpsi, integral_const, integral_psiFn_aux ht]
  simp

/-- Tonelli in `(x, t)`: `∫_𝕋 heatPos d a dx = heatPosMass d a` (as a lower integral). -/
theorem lintegral_heatPos_aux (hd : 2 ≤ d) {a : ℝ} (ha : 0 < a) :
    ∫⁻ x, ENNReal.ofReal (heatPos d a x) = ENNReal.ofReal (heatPosMass d a) := by
  have hd1 : 1 ≤ d := by omega
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hp : (-1 : ℝ) < (d : ℝ) / 2 - 1 := by linarith
  have hae : ∀ᵐ x : Torus d, x ≠ 0 := KernelAux.torus_ae_ne (by omega)
  have hpt : ∀ᵐ x : Torus d, ENNReal.ofReal (heatPos d a x) =
      ENNReal.ofReal (KernelAux.subA d 0) *
        ∫⁻ t in Ioc (0 : ℝ) a, ENNReal.ofReal (heatWeight d t * (1 + psiFn x t)) := by
    filter_upwards [hae] with x hx
    have hnn : ∀ᵐ t ∂(volume.restrict (Ioc (0 : ℝ) a)), 0 ≤ heatWeight d t * (1 + psiFn x t) :=
      ae_restrict_of_forall_mem measurableSet_Ioc fun t ht =>
        mul_nonneg (rb_heatWeight_nonneg ht.1) (one_add_psiFn_nonneg x ht.1)
    have hI := ofReal_integral_eq_lintegral_ofReal
      (integrableOn_heatWeight_one_add_psiFn hd x hx ha) hnn
    show ENNReal.ofReal (KernelAux.subA d 0 * ∫ t in Ioc (0 : ℝ) a, heatWeight d t * (1 + psiFn x t)) = _
    rw [ENNReal.ofReal_mul (subA_zero_pos hd).le, hI]
  have hmeasG : Measurable fun p : Torus d × ℝ =>
      ENNReal.ofReal (heatWeight d p.2 * (1 + psiFn p.1 p.2)) :=
    ENNReal.measurable_ofReal.comp (measurable_heatInt_aux (d := d))
  have hint0 : IntegrableOn (fun t : ℝ => heatWeight d t) (Ioc (0 : ℝ) a) := by
    unfold heatWeight
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le ha.le).mp
      (intervalIntegral.intervalIntegrable_rpow' hp)
  have hnn0 : ∀ᵐ t ∂(volume.restrict (Ioc (0 : ℝ) a)), 0 ≤ heatWeight d t :=
    by exact ae_restrict_of_forall_mem measurableSet_Ioc fun t ht => rb_heatWeight_nonneg ht.1
  have hinner : ∀ t ∈ Ioc (0 : ℝ) a,
      (∫⁻ x : Torus d, ENNReal.ofReal (heatWeight d t * (1 + psiFn x t))) = ENNReal.ofReal (heatWeight d t) := by
    intro t ht
    have ht0 : 0 < t := ht.1
    have hfun : ∀ x : Torus d, ENNReal.ofReal (heatWeight d t * (1 + psiFn x t)) =
        ENNReal.ofReal (heatWeight d t) * ENNReal.ofReal (1 + psiFn x t) :=
      fun x => ENNReal.ofReal_mul (rb_heatWeight_nonneg ht0)
    have hone : ∫⁻ x : Torus d, ENNReal.ofReal (1 + psiFn x t) = 1 := by
      rw [← ofReal_integral_eq_lintegral_ofReal (integrable_one_add_psiFn_aux ht0)
        (Eventually.of_forall fun x => one_add_psiFn_nonneg x ht0),
        integral_one_add_psiFn_aux ht0, ENNReal.ofReal_one]
    simp_rw [hfun]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, hone, mul_one]
  have hswap : ∫⁻ t in Ioc (0 : ℝ) a, (∫⁻ x : Torus d, ENNReal.ofReal (heatWeight d t * (1 + psiFn x t)))
      = ∫⁻ t in Ioc (0 : ℝ) a, ENNReal.ofReal (heatWeight d t) :=
    setLIntegral_congr_fun measurableSet_Ioc (by intro t ht; exact hinner t ht)
  rw [lintegral_congr_ae hpt, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    lintegral_lintegral_swap (f := fun x t => ENNReal.ofReal (heatWeight d t * (1 + psiFn x t)))
      hmeasG.aemeasurable, hswap, ← ofReal_integral_eq_lintegral_ofReal hint0 hnn0,
    integral_heatWeight hd1 ha.le, ← ENNReal.ofReal_mul (subA_zero_pos hd).le]
  congr 1
  unfold heatPosMass
  ring

/-- `heatPos d a` is Haar-integrable (nonnegative with finite Haar mass, Tonelli in `(x, t)`). -/
theorem integrable_heatPos (hd : 2 ≤ d) {a : ℝ} (ha : 0 < a) : Integrable (heatPos d a) := by
  refine ⟨(heatPos_measurable_aux a).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun x => heatPos_nonneg_aux hd ha.le x),
    lintegral_heatPos_aux hd ha]
  exact ENNReal.ofReal_lt_top

/-- `∫_{𝕋^d} heatPos d a dx = heatPosMass d a` (`∫ (1 + Ψ(x,t)) dx = 1`, then
`integral_heatWeight`). -/
theorem integral_heatPos (hd : 2 ≤ d) {a : ℝ} (ha : 0 < a) :
    ∫ x, heatPos d a x = heatPosMass d a := by
  rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun x => heatPos_nonneg_aux hd ha.le x)
    (heatPos_measurable_aux a).aestronglyMeasurable, lintegral_heatPos_aux hd ha,
    ENNReal.toReal_ofReal (heatPosMass_nonneg_aux hd ha.le)]

/-- The near field is Haar-integrable in the sense needed for the centred kernel: every
translate is `μ`-integrable for `μ = ρ dx`, `ρ ≤ Λ`. -/
theorem integrable_heatPos_shift (hd : 2 ≤ d) (hμ : μ = withDensityReal ρ) (hρ : IsProbDensity ρ)
    (hΛ : ∀ x, ρ x ≤ Λ) {a : ℝ} (ha : 0 < a) (x : Torus d) :
    Integrable (fun y => heatPos d a (x - y)) μ :=
  integrable_shift_withDensity hμ hρ hΛ (integrable_heatPos hd ha) x

/-- The one-body integral of the near field against `μ = ρ dx` is at most `Λ heatPosMass`
(lower Lebesgue form). -/
theorem lintegral_heatPos_conv_aux (hd : 2 ≤ d) (hΛ : ∀ x, ρ x ≤ Λ) {a : ℝ} (ha : 0 < a)
    (x : Torus d) :
    ∫⁻ y, ENNReal.ofReal (heatPos d a (x - y)) ∂(withDensityReal ρ) ≤
      ENNReal.ofReal Λ * ENNReal.ofReal (heatPosMass d a) := by
  have h : ∫⁻ y, ENNReal.ofReal (heatPos d a (x - y)) ∂(withDensityReal ρ) ≤
      ENNReal.ofReal Λ * ∫⁻ y, ENNReal.ofReal (heatPos d a y) :=
    KernelAux2.lintegral_conv_le ρ Λ hΛ (fun z => ENNReal.ofReal (heatPos d a z)) x
  rw [lintegral_heatPos_aux hd ha] at h
  exact h

theorem integrable_heatPos_pair (hd : 2 ≤ d) (hμ : μ = withDensityReal ρ) (hρ : IsProbDensity ρ)
    (hΛ : ∀ x, ρ x ≤ Λ) [IsProbabilityMeasure μ] {a : ℝ} (ha : 0 < a) :
    Integrable (fun p : Torus d × Torus d => heatPos d a (p.1 - p.2)) (μ.prod μ) := by
  have hm : Measurable (fun p : Torus d × Torus d => heatPos d a (p.1 - p.2)) :=
    (heatPos_measurable_aux a).comp (measurable_fst.sub measurable_snd)
  refine ⟨hm.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun p => heatPos_nonneg_aux hd ha.le _),
    lintegral_prod _ hm.ennreal_ofReal.aemeasurable]
  calc ∫⁻ x, ∫⁻ y, ENNReal.ofReal (heatPos d a ((x, y).1 - (x, y).2)) ∂μ ∂μ
      ≤ ∫⁻ _x, ENNReal.ofReal Λ * ENNReal.ofReal (heatPosMass d a) ∂μ := by
        refine lintegral_mono fun x => ?_
        show ∫⁻ y, ENNReal.ofReal (heatPos d a (x - y)) ∂μ ≤ _
        rw [hμ]
        exact lintegral_heatPos_conv_aux hd hΛ ha x
    _ = ENNReal.ofReal Λ * ENNReal.ofReal (heatPosMass d a) := by simp
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top

theorem convMeasure_heatPos_nonneg (hd : 2 ≤ d) (hμ : μ = withDensityReal ρ)
    (hρ : IsProbDensity ρ) {a : ℝ} (ha : 0 ≤ a) (x : Torus d) :
    0 ≤ convMeasure (heatPos d a) μ x := by
  unfold convMeasure
  exact integral_nonneg fun y => heatPos_nonneg_aux hd ha (x - y)

/-- `heatPos*μ ≤ Λ ∫ heatPos dx = Λ heatPosMass d a`. -/
theorem convMeasure_heatPos_le (hd : 2 ≤ d) (hμ : μ = withDensityReal ρ) (hρ : IsProbDensity ρ)
    (hΛ : ∀ x, ρ x ≤ Λ) {a : ℝ} (ha : 0 < a) (x : Torus d) :
    convMeasure (heatPos d a) μ x ≤ Λ * heatPosMass d a := by
  have hΛ0 : 0 ≤ Λ := (hρ.nonneg x).trans (hΛ x)
  have hmass : 0 ≤ heatPosMass d a := heatPosMass_nonneg_aux hd ha.le
  have h2 := lintegral_heatPos_conv_aux (ρ := ρ) hd hΛ ha x
  have h3 : (∫⁻ y, ENNReal.ofReal (heatPos d a (x - y)) ∂(withDensityReal ρ)).toReal ≤
      (ENNReal.ofReal Λ * ENNReal.ofReal (heatPosMass d a)).toReal :=
    ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top) h2
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hΛ0, ENNReal.toReal_ofReal hmass] at h3
  unfold convMeasure
  rw [hμ, integral_eq_lintegral_of_nonneg_ae
    (Eventually.of_forall fun y => heatPos_nonneg_aux hd ha.le (x - y))
    (heatPos_measurable_aux a |>.comp (measurable_const.sub measurable_id)).aestronglyMeasurable]
  exact h3

theorem integrable_convMeasure_heatPos (hd : 2 ≤ d) (hμ : μ = withDensityReal ρ)
    (hρ : IsProbDensity ρ) (hΛ : ∀ x, ρ x ≤ Λ) {a : ℝ} (ha : 0 < a) :
    Integrable (convMeasure (heatPos d a) μ) μ :=
  integrable_convMeasure_withDensity hμ hρ hΛ (heatPos_measurable_aux a) (integrable_heatPos hd ha)

theorem energyPairing_heatPos_nonneg (hd : 2 ≤ d) (hμ : μ = withDensityReal ρ)
    (hρ : IsProbDensity ρ) {a : ℝ} (ha : 0 ≤ a) : 0 ≤ energyPairing (heatPos d a) μ μ := by
  show 0 ≤ ∫ x, convMeasure (heatPos d a) μ x ∂μ
  exact integral_nonneg fun x => convMeasure_heatPos_nonneg hd hμ hρ ha x

theorem energyPairing_heatPos_le (hd : 2 ≤ d) (hμ : μ = withDensityReal ρ) (hρ : IsProbDensity ρ)
    (hΛ : ∀ x, ρ x ≤ Λ) [IsProbabilityMeasure μ] {a : ℝ} (ha : 0 < a) :
    energyPairing (heatPos d a) μ μ ≤ Λ * heatPosMass d a := by
  show ∫ x, convMeasure (heatPos d a) μ x ∂μ ≤ Λ * heatPosMass d a
  calc ∫ x, convMeasure (heatPos d a) μ x ∂μ ≤ ∫ _x, Λ * heatPosMass d a ∂μ :=
        integral_mono (integrable_convMeasure_heatPos hd hμ hρ hΛ ha) (integrable_const _)
          (fun x => convMeasure_heatPos_le hd hμ hρ hΛ ha x)
    _ = Λ * heatPosMass d a := by simp

/-- Off-diagonal lower bound `-M` for every pair (no collision hypothesis needed). -/
theorem iidNegativeStatistic_le_of_le_all {N : ℕ} (h : Torus d × Torus d → ℝ) (X : Config d N)
    {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ x y : Torus d, -M ≤ h (x, y)) :
    DGRHS.Concentration.iidNegativeStatistic N h X ≤ (N : ℝ) * M / 2 := by
  have hsum : ∑ _i : Fin N, ∑ _j : Fin N, (-M) ≤
      ∑ i, ∑ j, (if i ≠ j then h (X i, X j) else 0) := by
    refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
    split_ifs with hij
    · exact hM _ _
    · linarith
  have h0 : ∑ _i : Fin N, ∑ _j : Fin N, (-M) = -((N : ℝ) * N * M) := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  unfold DGRHS.Concentration.iidNegativeStatistic DGRHS.Concentration.iidCoupledSum
    DGRHS.Decoupling.offDiagonalSum
  simp only []
  rcases Nat.eq_zero_or_pos N with rfl | hNpos
  · simp
  · have hNr : (0 : ℝ) < N := by exact_mod_cast hNpos
    rw [div_le_iff₀ (mul_pos two_pos hNr)]
    nlinarith

/-- Near-field bound (torus form of DGR `lem:logShortRange`): since `heatPos ≥ 0`,
`-∑_{i≠j} (heatPos)~(x_i, x_j) ≤ ∑_{i≠j} (H(x_i) + H(x_j)) ≤ 2N(N-1) Λ heatPosMass`, so the
negative statistic is at most `(N-1) Λ heatPosMass ≤ N Λ heatPosMass d a`. -/
theorem iidNegativeStatistic_heatPos_le (hd : 2 ≤ d) (hμ : μ = withDensityReal ρ)
    (hρ : IsProbDensity ρ) (hΛ : ∀ x, ρ x ≤ Λ) [IsProbabilityMeasure μ] {a : ℝ} (ha : 0 < a)
    {N : ℕ} (X : Config d N) :
    DGRHS.Concentration.iidNegativeStatistic N (pairKernel (heatPos d a) μ) X ≤
      (N : ℝ) * (Λ * heatPosMass d a) := by
  have hΛ0 : 0 ≤ Λ := (hρ.nonneg 0).trans (hΛ 0)
  have hm0 : 0 ≤ heatPosMass d a := heatPosMass_nonneg_aux hd ha.le
  have hM0 : 0 ≤ 2 * (Λ * heatPosMass d a) := mul_nonneg two_pos.le (mul_nonneg hΛ0 hm0)
  have hbd : ∀ x y : Torus d, -(2 * (Λ * heatPosMass d a)) ≤ pairKernel (heatPos d a) μ (x, y) := by
    intro x y
    have h1 := heatPos_nonneg_aux hd ha.le (x - y)
    have h2 := convMeasure_heatPos_le hd hμ hρ hΛ ha x
    have h3 := convMeasure_heatPos_le hd hμ hρ hΛ ha y
    have h4 := energyPairing_heatPos_nonneg hd hμ hρ ha.le
    show -(2 * (Λ * heatPosMass d a)) ≤ centeredKernel (heatPos d a) μ x y
    unfold centeredKernel
    linarith
  have key := iidNegativeStatistic_le_of_le_all (pairKernel (heatPos d a) μ) X hM0 hbd
  calc _ ≤ (N : ℝ) * (2 * (Λ * heatPosMass d a)) / 2 := key
    _ = (N : ℝ) * (Λ * heatPosMass d a) := by ring

end Repulsive

end HRS

end
