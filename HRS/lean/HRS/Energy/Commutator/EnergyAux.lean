import HRS.Energy.Commutator.Smear

/-!
# Auxiliary lemmas for the energy identities of `Stress.lean` (packet CM-S3)

Positivity, measurability, integrability of the slice kernel `𝒢_l^{full}`, geometry of `tdist`, and
the measure-theoretic bookkeeping (lintegrals) for `energy_identity_slice` / `energy_identity_coulomb`.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators
open HRS HRS.KernelAux

namespace HRS.Commutator.EnergyAux

variable {d : ℕ}

/-! ### Measurability -/

theorem measurable_psiFn_uncurry : Measurable fun p : Torus d × ℝ => psiFn p.1 p.2 := by
  unfold psiFn
  refine Measurable.tsum fun k => ?_
  by_cases hk : k = 0
  · simp [hk]
  · simp only [hk, ite_false]
    have h1 : Continuous fun p : Torus d × ℝ => Real.exp (-p.2 * Lattice.enorm k ^ 2) :=
      Real.continuous_exp.comp ((continuous_snd.neg).mul continuous_const)
    have h2 : Continuous fun p : Torus d × ℝ => Torus.cosMode k p.1 :=
      (Torus.continuous_cosMode k).comp continuous_fst
    exact (h1.mul h2).measurable

theorem measurable_sliceG (l : ℝ) : Measurable (sliceG d l) := by
  unfold sliceG
  have hm : Measurable fun q : Torus d × ℝ =>
      Real.exp (-l * q.2) * psiFn q.1 (4 * Real.pi ^ 2 * q.2) := by
    refine Measurable.mul (by fun_prop) ?_
    exact measurable_psiFn_uncurry.comp (measurable_fst.prodMk (measurable_const.mul measurable_snd))
  exact (hm.stronglyMeasurable.integral_prod_right' (ν := volume.restrict (Ioi (0 : ℝ)))).measurable

theorem measurable_sliceGfull (l : ℝ) : Measurable (sliceGfull d l) :=
  (measurable_sliceG l).add measurable_const

theorem measurable_yukawa (d : ℕ) (l : ℝ) : Measurable (yukawa d l) := by
  unfold yukawa
  have hm : Measurable fun q : ℝ × ℝ => Real.exp (-l * q.2) *
      ((4 * Real.pi * q.2) ^ (-(d : ℝ) / 2) * Real.exp (-q.1 ^ 2 / (4 * q.2))) := by
    refine Measurable.mul (by fun_prop) (Measurable.mul ?_ ?_)
    · exact (measurable_const.mul measurable_snd).pow_const _
    · exact Real.measurable_exp.comp ((measurable_fst.pow_const 2).neg.div (measurable_const.mul measurable_snd))
  exact (hm.stronglyMeasurable.integral_prod_right' (ν := volume.restrict (Ioi (0 : ℝ)))).measurable

theorem measurable_tdist_zero : Measurable fun z : Torus d => KernelGrad.tdist z 0 :=
  CoercAux.continuous_tdist_zero.measurable

theorem measurable_fTrunc (l η : ℝ) : Measurable (fTrunc d l η) := by
  unfold fTrunc
  have : (fun z : Torus d => max (yukawa d l ‖KernelGrad.centeredRep z‖ - yukawa d l η) 0) =
      fun z => max (yukawa d l (KernelGrad.tdist z 0) - yukawa d l η) 0 := by
    funext z; simp [KernelGrad.tdist]
  rw [this]
  exact (((measurable_yukawa d l).comp measurable_tdist_zero).sub measurable_const).max measurable_const


/-! ### Positivity of the slice kernel -/

theorem centeredRep_mem_box (x : Torus d) : (fun i => KernelGrad.centeredRep x i) ∈ Box d := by
  intro i
  obtain ⟨h0, h1⟩ := KernelGrad.rep_mem x i
  show KernelGrad.centeredRep x i ∈ Ioc (-1 / 2 : ℝ) (-1 / 2 + 1)
  rw [KernelGrad.centeredRep_apply]
  simp only [mem_Ioc]
  split_ifs with h
  · constructor <;> linarith
  · push Not at h
    constructor <;> linarith

theorem boxPt_centeredRep (x : Torus d) : boxPt (fun i => KernelGrad.centeredRep x i) = x :=
  KernelGrad.mk_centeredRep x

section Positivity

variable {l : ℝ}

/-- Representation of the full slice kernel as a nonnegative heat integral (`x ≠ 0`). -/
theorem sliceGfull_eq_integral (hl : 0 < l) {x : Torus d} (hx : x ≠ 0) :
    IntegrableOn (fun t : ℝ => Real.exp (-l * t) * (1 + psiFn x (4 * Real.pi ^ 2 * t))) (Ioi 0) ∧
    sliceGfull d l x =
      ∫ t in Ioi (0 : ℝ), Real.exp (-l * t) * (1 + psiFn x (4 * Real.pi ^ 2 * t)) := by
  have hI := SliceAux.integrableOn_slice_psi hl.le hx
  have hE : IntegrableOn (fun t : ℝ => Real.exp (-l * t)) (Ioi 0) :=
    integrableOn_exp_mul_Ioi (a := -l) (by linarith) (0 : ℝ)
  have hE' : ∫ t in Ioi (0 : ℝ), Real.exp (-l * t) = 1 / l := by
    rw [integral_exp_mul_Ioi (by linarith : -l < 0)]
    simp
  have hg : IntegrableOn (fun t : ℝ => Real.exp (-l * t) * (1 + psiFn x (4 * Real.pi ^ 2 * t)))
      (Ioi 0) := by
    have := hE.add hI
    refine this.congr_fun (fun t _ => ?_) measurableSet_Ioi
    simp only [Pi.add_apply]; ring
  refine ⟨hg, ?_⟩
  have hsplit : ∫ t in Ioi (0 : ℝ), Real.exp (-l * t) * (1 + psiFn x (4 * Real.pi ^ 2 * t)) =
      1 / l + ∫ t in Ioi (0 : ℝ), Real.exp (-l * t) * psiFn x (4 * Real.pi ^ 2 * t) := by
    rw [← hE', ← integral_add hE hI]
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    ring
  rw [hsplit]
  unfold sliceGfull sliceG
  ring

/-- The integrand of the heat representation is nonnegative, and dominates the term `m = 0`. -/
theorem heat_integrand_ge (y : Fin d → ℝ) (l : ℝ) {t : ℝ} (ht : 0 < t) :
    SliceAux.heatTerm d y 0 l t ≤
      Real.exp (-l * t) * (1 + psiFn (boxPt y) (4 * Real.pi ^ 2 * t)) := by
  rw [SliceAux.heat_pointwise y l ht]
  exact (SliceAux.summable_heatTerm y l ht).le_tsum 0 fun m _ => SliceAux.heatTerm_nonneg y m l ht

theorem one_add_psi_nonneg_exp (y : Fin d → ℝ) (l : ℝ) {t : ℝ} (ht : 0 < t) :
    0 ≤ Real.exp (-l * t) * (1 + psiFn (boxPt y) (4 * Real.pi ^ 2 * t)) :=
  (SliceAux.heatTerm_nonneg y 0 l ht).trans (heat_integrand_ge y l ht)

theorem sliceGfull_nonneg (hl : 0 < l) (x : Torus d) : 0 ≤ sliceGfull d l x := by
  by_cases hx : x = 0
  · subst hx
    unfold sliceGfull sliceG
    have h1 : 0 ≤ ∫ t in Ioi (0 : ℝ), Real.exp (-l * t) * psiFn (0 : Torus d) (4 * Real.pi ^ 2 * t) :=
      setIntegral_nonneg measurableSet_Ioi fun t ht =>
        mul_nonneg (Real.exp_pos _).le (CoercAux.psi_zero_nonneg (by have : (0 : ℝ) < t := ht; positivity))
    have h2 : 0 ≤ 1 / l := by positivity
    linarith
  · obtain ⟨-, h⟩ := sliceGfull_eq_integral hl hx
    rw [h]
    refine setIntegral_nonneg measurableSet_Ioi fun t ht => ?_
    have := one_add_psi_nonneg_exp (fun i => KernelGrad.centeredRep x i) l (by exact ht)
    rwa [boxPt_centeredRep] at this

/-- Comparison with the Yukawa profile: `Γ_l(|x|) ≤ 𝒢_l^{full}(x)`. -/
theorem yukawa_le_sliceGfull (hd : 1 ≤ d) (hl : 0 < l) {x : Torus d} (hx : x ≠ 0) :
    yukawa d l ‖KernelGrad.centeredRep x‖ ≤ sliceGfull d l x := by
  obtain ⟨hint, h⟩ := sliceGfull_eq_integral hl hx
  rw [h]
  set y : Fin d → ℝ := fun i => KernelGrad.centeredRep x i with hy
  have hyn : ‖KernelGrad.centeredRep x‖ ≠ 0 := by
    intro h0
    apply hx
    rw [← KernelGrad.mk_centeredRep x, norm_eq_zero.mp h0]
    funext i; simp [Torus.mk]
  have hrpos : 0 < ‖KernelGrad.centeredRep x‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hyn)
  have hyk := SliceAux.integrableOn_yk hl hd hrpos
  unfold yukawa
  refine setIntegral_mono_on hyk hint measurableSet_Ioi
    fun t ht => ?_
  have := heat_integrand_ge y l (by exact ht)
  rw [boxPt_centeredRep] at this
  refine le_trans (le_of_eq ?_) this
  unfold SliceAux.heatTerm
  congr 3
  simp [hy]

theorem sliceGfull_pos (hd : 1 ≤ d) (hl : 0 < l) (x : Torus d) : 0 < sliceGfull d l x := by
  by_cases hx : x = 0
  · subst hx
    unfold sliceGfull sliceG
    have h1 : 0 ≤ ∫ t in Ioi (0 : ℝ), Real.exp (-l * t) * psiFn (0 : Torus d) (4 * Real.pi ^ 2 * t) :=
      setIntegral_nonneg measurableSet_Ioi fun t ht =>
        mul_nonneg (Real.exp_pos _).le (CoercAux.psi_zero_nonneg (by have : (0 : ℝ) < t := ht; positivity))
    have h2 : 0 < 1 / l := by positivity
    linarith
  · refine lt_of_lt_of_le ?_ (yukawa_le_sliceGfull hd hl hx)
    have hrpos : 0 < ‖KernelGrad.centeredRep x‖ := by
      refine lt_of_le_of_ne (norm_nonneg _) fun h0 => hx ?_
      have h00 : KernelGrad.centeredRep x = 0 := norm_eq_zero.mp h0.symm
      rw [← KernelGrad.mk_centeredRep x, h00]
      funext i; simp [Torus.mk]
    exact SliceAux.yk_pos hd hl hrpos

end Positivity


/-! ### Geometry of `tdist` -/

theorem circ_norm_le (x : ℝ) : ‖(x : UnitAddCircle)‖ ≤ |x| := by
  rw [UnitAddCircle.norm_eq]
  have := round_le x 0
  simpa using this

theorem tdist_zero_eq (z : Torus d) : KernelGrad.tdist z 0 = Real.sqrt (∑ i, ‖z i‖ ^ 2) := by
  have := CoercAux.tdist_eq_sqrt z 0
  simpa using this

theorem tdist_add_le (a b : Torus d) :
    KernelGrad.tdist (a + b) 0 ≤ KernelGrad.tdist a 0 + KernelGrad.tdist b 0 := by
  set P : Euc d := WithLp.toLp 2 fun i => ‖a i‖
  set Q : Euc d := WithLp.toLp 2 fun i => ‖b i‖
  have hP : ‖P‖ = KernelGrad.tdist a 0 := by
    rw [tdist_zero_eq, EuclideanSpace.norm_eq]; simp [P]
  have hQ : ‖Q‖ = KernelGrad.tdist b 0 := by
    rw [tdist_zero_eq, EuclideanSpace.norm_eq]; simp [Q]
  rw [← hP, ← hQ]
  refine le_trans ?_ (norm_add_le P Q)
  rw [tdist_zero_eq, EuclideanSpace.norm_eq]
  refine Real.sqrt_le_sqrt (Finset.sum_le_sum fun i _ => ?_)
  simp only [Real.norm_eq_abs, sq_abs, PiLp.add_apply, P, Q]
  have h1 : ‖(a + b) i‖ ≤ ‖a i‖ + ‖b i‖ := norm_add_le _ _
  have h0 : 0 ≤ ‖(a + b) i‖ := norm_nonneg _
  nlinarith

theorem tdist_mk_le (w : Euc d) : KernelGrad.tdist (Torus.mk w) 0 ≤ ‖w‖ := by
  rw [tdist_zero_eq, EuclideanSpace.norm_eq]
  refine Real.sqrt_le_sqrt (Finset.sum_le_sum fun i _ => ?_)
  have h := circ_norm_le (w i)
  have h0 : 0 ≤ ‖(Torus.mk w) i‖ := norm_nonneg _
  have : ‖(Torus.mk w) i‖ ≤ |w i| := h
  simp only [Real.norm_eq_abs, sq_abs]
  have h2 := pow_le_pow_left₀ h0 this 2
  rwa [sq_abs] at h2

theorem tdist_neg_zero (z : Torus d) : KernelGrad.tdist (-z) 0 = KernelGrad.tdist z 0 :=
  KernelGrad.tdist_neg z

/-- A point at distance `> ε` from `0` stays at distance `> ε - δ` after moving by `x'` with
`|x'| ≤ δ`. -/
theorem tdist_add_ge (z x' : Torus d) :
    KernelGrad.tdist z 0 - KernelGrad.tdist x' 0 ≤ KernelGrad.tdist (x' + z) 0 := by
  have h := tdist_add_le (x' + z) (-x')
  rw [KernelGrad.tdist_neg, show x' + z + -x' = z by abel] at h
  linarith

theorem tdist_eq_zero_iff (z : Torus d) : KernelGrad.tdist z 0 = 0 ↔ z = 0 := by
  constructor
  · intro h
    by_contra hz
    exact absurd h (KernelGrad.tdist_pos hz).ne'
  · rintro rfl
    exact CoercAux.tdist_self 0

theorem ne_zero_of_tdist_pos {z : Torus d} (h : 0 < KernelGrad.tdist z 0) : z ≠ 0 := by
  rintro rfl
  rw [CoercAux.tdist_self] at h
  exact lt_irrefl _ h

/-- `tdist (x - y) 0 = tdist x y` (definition). -/
theorem tdist_def (x y : Torus d) : KernelGrad.tdist x y = KernelGrad.tdist (x - y) 0 := by
  unfold KernelGrad.tdist; rw [sub_zero]

/-- `‖centeredRep z‖ = tdist z 0`. -/
theorem norm_centeredRep_eq (z : Torus d) : ‖KernelGrad.centeredRep z‖ = KernelGrad.tdist z 0 := by
  simp [KernelGrad.tdist]

/-! ### The heat integral of the slice kernel over the torus -/

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

theorem integral_cosMode_aux {k : Lattice d} (hk : k ≠ 0) :
    ∫ x : Torus d, Torus.cosMode k x = 0 := by
  have h1 : ∫ x : Torus d, Torus.cosMode k x = RCLike.re (∫ x : Torus d, Torus.mode k x) := by
    rw [← integral_re (Torus.integrable_mode k)]
    rfl
  rw [h1, Torus.integral_mode, if_neg hk]
  simp

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
      (fun k => ?_) (HRS.summable_gauss_lattice d t ht)
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

theorem integral_one_add_psiFn_aux {t : ℝ} (ht : 0 < t) :
    ∫ x : Torus d, (1 + psiFn x t) = 1 := by
  have hpsi : Integrable (fun x : Torus d => psiFn x t) :=
    (continuous_psiFn (d := d) ht).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  rw [integral_add (integrable_const _) hpsi, integral_const, integral_psiFn_aux ht]
  simp

theorem one_add_psiFn_nonneg' (x : Torus d) {u : ℝ} (hu : 0 < u) : 0 ≤ 1 + psiFn x u := by
  obtain ⟨y, rfl⟩ : ∃ y : Fin d → ℝ, boxPt y = x := ⟨fun i => Torus.rep x i, Torus.mk_rep x⟩
  rw [← HRS.psi_eq _ hu, KernelAux.theta_images y hu]
  exact mul_nonneg (by positivity) (tsum_nonneg fun _ => (Real.exp_pos _).le)

section L1

variable {l : ℝ}

/-- `𝒢_l^{full} ∈ L¹(𝕋^d)` with `∫ 𝒢_l^{full} = 1/l` (Tonelli on the heat representation). -/
theorem lintegral_sliceGfull (hd : 1 ≤ d) (hl : 0 < l) :
    ∫⁻ x : Torus d, ENNReal.ofReal (sliceGfull d l x) = ENNReal.ofReal (1 / l) := by
  have hae : ∀ᵐ x : Torus d, x ≠ 0 := KernelAux.torus_ae_ne (by omega)
  set F : Torus d → ℝ → ℝ := fun x t => Real.exp (-l * t) * (1 + psiFn x (4 * Real.pi ^ 2 * t)) with hF
  have h1 : ∀ᵐ x : Torus d, ENNReal.ofReal (sliceGfull d l x) =
      ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (F x t) := by
    filter_upwards [hae] with x hx
    obtain ⟨hint, h⟩ := sliceGfull_eq_integral hl hx
    rw [h]
    refine ofReal_integral_eq_lintegral_ofReal hint ?_
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun t ht => ?_)
    have ht' : (0 : ℝ) < t := ht
    exact mul_nonneg (Real.exp_pos _).le (one_add_psiFn_nonneg' x (by positivity))
  rw [lintegral_congr_ae h1]
  have hmeas : Measurable (Function.uncurry fun (x : Torus d) (t : ℝ) => ENNReal.ofReal (F x t)) := by
    refine ENNReal.measurable_ofReal.comp ?_
    refine Measurable.mul (by fun_prop) ?_
    exact measurable_const.add (measurable_psiFn_uncurry.comp
      (measurable_fst.prodMk (measurable_const.mul measurable_snd)))
  rw [lintegral_lintegral_swap hmeas.aemeasurable]
  have h2 : ∀ t ∈ Ioi (0 : ℝ), ∫⁻ x : Torus d, ENNReal.ofReal (F x t) =
      ENNReal.ofReal (Real.exp (-l * t)) := by
    intro t ht
    have ht' : (0 : ℝ) < t := ht
    have hu : 0 < 4 * Real.pi ^ 2 * t := by positivity
    have hint : Integrable (fun x : Torus d => F x t) :=
      (((integrable_const (1 : ℝ)).add ((continuous_psiFn hu).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _))).const_mul (Real.exp (-l * t)))
    rw [← ofReal_integral_eq_lintegral_ofReal hint
      (Filter.Eventually.of_forall fun x => mul_nonneg (Real.exp_pos _).le (one_add_psiFn_nonneg' x hu))]
    simp only [hF]
    rw [integral_const_mul, integral_one_add_psiFn_aux hu, mul_one]
  rw [setLIntegral_congr_fun measurableSet_Ioi h2]
  have hE : IntegrableOn (fun t : ℝ => Real.exp (-l * t)) (Ioi 0) :=
    integrableOn_exp_mul_Ioi (a := -l) (by linarith) (0 : ℝ)
  rw [← ofReal_integral_eq_lintegral_ofReal hE
    (Filter.Eventually.of_forall fun t => (Real.exp_pos _).le)]
  rw [integral_exp_mul_Ioi (by linarith : -l < 0)]
  simp

end L1

/-! ### Structure of the smeared charges -/

theorem measurable_sphere_smul (η : ℝ) :
    Measurable (fun ω : Metric.sphere (0 : Euc d) 1 => η • (ω : Euc d)) :=
  (by fun_prop : Continuous fun ω : Metric.sphere (0 : Euc d) 1 => η • (ω : Euc d)).measurable

theorem lintegral_smearT (l η : ℝ) {F : Torus d → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ x, F x ∂(smearT d l η) =
      ENNReal.ofReal (l * yukawa d l η) * (∫⁻ w in Metric.closedBall (0 : Euc d) η, F (Torus.mk w)) +
      ENNReal.ofReal (-(deriv (yukawa d l) η) * η ^ (d - 1)) *
        ∫⁻ ω : Metric.sphere (0 : Euc d) 1, F (Torus.mk (η • (ω : Euc d)))
          ∂((volume : Measure (Euc d)).toSphere) := by
  unfold smearT smearEuc
  rw [lintegral_map hF HRS.Torus.continuous_mk.measurable, lintegral_add_measure,
    lintegral_smul_measure, lintegral_smul_measure]
  have := lintegral_map (μ := (volume : Measure (Euc d)).toSphere)
    (hF.comp HRS.Torus.continuous_mk.measurable) (measurable_sphere_smul η)
  simp only [smul_eq_mul]
  rw [show (∫⁻ a : Euc d, F (Torus.mk a) ∂Measure.map (fun ω : Metric.sphere (0 : Euc d) 1 => η • (ω : Euc d)) (volume : Measure (Euc d)).toSphere) = _ from this]
  rfl


/-- The cube `(-1/2, 1/2]^d` in `ℝ^d` (a fundamental domain). -/
def cube (d : ℕ) : Set (Euc d) := {w | ∀ i, w i ∈ Ioc (-1/2 : ℝ) (-1/2 + 1)}

theorem measurableSet_cube : MeasurableSet (cube d) := by
  have : cube d = (fun w : Euc d => w.ofLp) ⁻¹' (Set.pi univ fun _ : Fin d => Ioc (-1/2 : ℝ) (-1/2 + 1)) := by
    ext w; simp [cube]
  rw [this]
  exact (MeasurableSet.pi countable_univ fun _ _ => measurableSet_Ioc).preimage
    (PiLp.volume_preserving_ofLp (Fin d)).measurable

theorem mk_measurePreserving :
    MeasurePreserving (Torus.mk : Euc d → Torus d) (volume.restrict (cube d)) volume := by
  have h1 := measurePreserving_pi (fun _ : Fin d => (volume : Measure ℝ).restrict (Ioc (-1/2 : ℝ) (-1/2 + 1)))
    (fun _ : Fin d => (volume : Measure UnitAddCircle))
    (f := fun _ => ((↑) : ℝ → UnitAddCircle)) (fun _ => UnitAddCircle.measurePreserving_mk (-1/2))
  rw [← Measure.restrict_pi_pi] at h1
  have h2 := (PiLp.volume_preserving_ofLp (Fin d)).restrict_preimage
    (s := Set.pi univ fun _ : Fin d => Ioc (-1/2 : ℝ) (-1/2 + 1))
    (MeasurableSet.pi countable_univ fun _ _ => measurableSet_Ioc)
  have hc : (fun w : Euc d => w.ofLp) ⁻¹' (Set.pi univ fun _ : Fin d => Ioc (-1/2 : ℝ) (-1/2 + 1)) = cube d := by
    ext w; simp [cube]
  rw [hc] at h2
  exact h1.comp h2

theorem abs_apply_le_norm (w : Euc d) (i : Fin d) : |w i| ≤ ‖w‖ := by
  have := PiLp.norm_apply_le w i
  simpa [Real.norm_eq_abs] using this

theorem closedBall_subset_cube {δ : ℝ} (hδ : δ < 1 / 2) : Metric.closedBall (0 : Euc d) δ ⊆ cube d := by
  intro w hw i
  have h1 := abs_apply_le_norm w i
  have h2 : ‖w‖ ≤ δ := by simpa using hw
  have := abs_lt.1 (lt_of_le_of_lt (h1.trans h2) hδ)
  constructor <;> linarith [this.1, this.2]

theorem mk_eq_zero_of_norm_lt_one {w : Euc d} (hw : Torus.mk w = 0) (h : ‖w‖ < 1) : w = 0 := by
  obtain ⟨m, hm⟩ := SliceAux.exists_lattice_of_mk_eq (x := w) (y := 0) (by
    rw [hw]; funext i; simp [Torus.mk])
  ext i
  have h1 := abs_apply_le_norm w i
  have h2 : w i = (m i : ℝ) := by rw [hm]; simp [Lattice.toEuc]
  have h3 : |(m i : ℝ)| < 1 := by rw [← h2]; exact lt_of_le_of_lt h1 h
  have h4 : m i = 0 := by
    have h5 : |m i| < 1 := by exact_mod_cast h3
    have := abs_lt.mp h5
    omega
  simp [h2, h4]

theorem smearT_singleton_zero (hd : 1 ≤ d) {l η : ℝ} (hη : 0 < η) (hη2 : η < 1 / 2) :
    smearT d l η {0} = 0 := by
  have : Nontrivial (Euc d) := by
    have : Nonempty (Fin d) := ⟨⟨0, by omega⟩⟩
    infer_instance
  have hms : MeasurableSet ({0} : Set (Torus d)) := measurableSet_singleton _
  have hF : Measurable (({0} : Set (Torus d)).indicator (fun _ => (1 : ℝ≥0∞))) :=
    measurable_const.indicator hms
  have h := lintegral_smearT (d := d) l η hF
  have h0 : ∫⁻ x, ({0} : Set (Torus d)).indicator (fun _ => (1 : ℝ≥0∞)) x ∂(smearT d l η) =
      smearT d l η {0} := by
    rw [lintegral_indicator hms]; simp
  rw [← h0, h]
  have h1 : (∫⁻ w in Metric.closedBall (0 : Euc d) η,
      ({0} : Set (Torus d)).indicator (fun _ => (1 : ℝ≥0∞)) (Torus.mk w)) = 0 := by
    refine le_antisymm ?_ bot_le
    calc _ ≤ ∫⁻ w in Metric.closedBall (0 : Euc d) η, ({0} : Set (Euc d)).indicator (fun _ => (1 : ℝ≥0∞)) w := by
          refine setLIntegral_mono' Metric.isClosed_closedBall.measurableSet fun w hwb => ?_
          by_cases hw : Torus.mk w = 0
          · have hwn : ‖w‖ ≤ η := by simpa using hwb
            have := mk_eq_zero_of_norm_lt_one hw (by linarith)
            subst this
            show ({0} : Set (Torus d)).indicator (fun _ => (1 : ℝ≥0∞)) (Torus.mk 0) ≤
              ({0} : Set (Euc d)).indicator (fun _ => (1 : ℝ≥0∞)) 0
            rw [hw, Set.indicator_of_mem (Set.mem_singleton _), Set.indicator_of_mem (Set.mem_singleton _)]
          · simp [hw]
      _ ≤ ∫⁻ w, ({0} : Set (Euc d)).indicator (fun _ => (1 : ℝ≥0∞)) w := setLIntegral_le_lintegral _ _
      _ = 0 := by
          rw [lintegral_indicator (measurableSet_singleton _)]
          simp
  have h2 : (∫⁻ ω : Metric.sphere (0 : Euc d) 1,
      ({0} : Set (Torus d)).indicator (fun _ => (1 : ℝ≥0∞)) (Torus.mk (η • (ω : Euc d)))
        ∂((volume : Measure (Euc d)).toSphere)) = 0 := by
    have : ∀ ω : Metric.sphere (0 : Euc d) 1,
        ({0} : Set (Torus d)).indicator (fun _ => (1 : ℝ≥0∞)) (Torus.mk (η • (ω : Euc d))) = 0 := by
      intro ω
      have hn : ‖η • (ω : Euc d)‖ = η := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos hη]
        have : ‖(ω : Euc d)‖ = 1 := by simpa using ω.2
        rw [this, mul_one]
      by_cases hz : Torus.mk (η • (ω : Euc d)) = 0
      · exfalso
        have := mk_eq_zero_of_norm_lt_one hz (by rw [hn]; linarith)
        rw [this] at hn
        simp at hn
        linarith
      · simp [hz]
    simp [this]
  rw [h1, h2]; simp

section SliceFinite

variable {l : ℝ}

theorem sliceG_continuousAt_lift (hl : 0 ≤ l) {w : Euc d} (hw : Torus.mk w ≠ 0) :
    ContinuousAt (fun y : Euc d => sliceG d l (Torus.mk y)) w :=
  (SliceAux.hasFDerivAt_slice hl hw).continuousAt

theorem sliceG_bdd_sphere (hl : 0 ≤ l) {η : ℝ} (hη : 0 < η) (hη2 : η < 1 / 2) :
    ∃ B : ℝ, ∀ w : Euc d, ‖w‖ = η → sliceG d l (Torus.mk w) ≤ B := by
  have hc : ContinuousOn (fun y : Euc d => sliceG d l (Torus.mk y)) (Metric.sphere (0 : Euc d) η) := by
    intro w hw
    refine (sliceG_continuousAt_lift hl ?_).continuousWithinAt
    intro hz
    have hn : ‖w‖ = η := by simpa using hw
    have := mk_eq_zero_of_norm_lt_one hz (by rw [hn]; linarith)
    rw [this] at hn; simp at hn; linarith
  obtain ⟨C, hC⟩ := (isCompact_sphere (0 : Euc d) η).exists_bound_of_continuousOn hc
  refine ⟨C, fun w hw => ?_⟩
  have := hC w (by simpa using hw)
  exact (le_abs_self _).trans (by simpa using this)

theorem lintegral_smearT_g_lt_top (hd : 1 ≤ d) (hl : 0 < l) {η : ℝ} (hη : 0 < η) (hη2 : η < 1 / 2) :
    ∫⁻ x, ENNReal.ofReal (sliceGfull d l x) ∂(smearT d l η) < ⊤ := by
  have hm : Measurable fun x : Torus d => ENNReal.ofReal (sliceGfull d l x) :=
    ENNReal.measurable_ofReal.comp (measurable_sliceGfull l)
  rw [lintegral_smearT l η hm]
  refine ENNReal.add_lt_top.mpr ⟨ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_, ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_⟩
  · calc _ ≤ ∫⁻ w in cube d, ENNReal.ofReal (sliceGfull d l (Torus.mk w)) :=
          lintegral_mono_set (closedBall_subset_cube hη2)
      _ = ∫⁻ x, ENNReal.ofReal (sliceGfull d l x) := by
          have hmp := mk_measurePreserving (d := d)
          have := hmp.lintegral_comp hm
          exact this
      _ < ⊤ := by rw [lintegral_sliceGfull hd hl]; exact ENNReal.ofReal_lt_top
  · obtain ⟨B, hB⟩ := sliceG_bdd_sphere hl.le hη hη2
    have hbd : ∀ ω : Metric.sphere (0 : Euc d) 1,
        ENNReal.ofReal (sliceGfull d l (Torus.mk (η • (ω : Euc d)))) ≤ ENNReal.ofReal (B + 1 / l) := by
      intro ω
      have hn : ‖η • (ω : Euc d)‖ = η := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos hη]
        have : ‖(ω : Euc d)‖ = 1 := by simpa using ω.2
        rw [this, mul_one]
      refine ENNReal.ofReal_le_ofReal ?_
      have := hB _ hn
      unfold sliceGfull
      linarith
    calc _ ≤ ∫⁻ _ω : Metric.sphere (0 : Euc d) 1, ENNReal.ofReal (B + 1 / l)
          ∂((volume : Measure (Euc d)).toSphere) := lintegral_mono hbd
      _ < ⊤ := by
          rw [lintegral_const]
          exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _)

end SliceFinite

section Newton

variable {l η : ℝ}

theorem g_sub_f_pos (hd : 1 ≤ d) (hl : 0 < l) (hη : 0 < η) {x : Torus d} (hx : x ≠ 0) :
    0 < sliceGfull d l x - fTrunc d l η x := by
  have h1 := yukawa_le_sliceGfull hd hl hx
  have hpos := sliceGfull_pos hd hl x
  have hη' : 0 < yukawa d l η := SliceAux.yk_pos hd hl hη
  unfold fTrunc
  rcases le_total (yukawa d l ‖KernelGrad.centeredRep x‖ - yukawa d l η) 0 with h | h
  · rw [max_eq_right h]; linarith
  · rw [max_eq_left h]; linarith

theorem integrable_G_smear (hd : 1 ≤ d) (hl : 0 < l) (hη : 0 < η) (hη2 : η < 1 / 2) {x : Torus d}
    (hx : x ≠ 0) : Integrable (fun y => sliceGfull d l (x - y)) (smearT d l η) := by
  by_contra h
  have h0 := integral_undef h
  rw [sliceGfull_conv_smear hd hl hη hη2 x hx] at h0
  linarith [g_sub_f_pos hd hl hη hx]

theorem lintegral_G_smear (hd : 1 ≤ d) (hl : 0 < l) (hη : 0 < η) (hη2 : η < 1 / 2) {x : Torus d}
    (hx : x ≠ 0) :
    ∫⁻ y, ENNReal.ofReal (sliceGfull d l (x - y)) ∂(smearT d l η) =
      ENNReal.ofReal (sliceGfull d l x - fTrunc d l η x) := by
  rw [← sliceGfull_conv_smear hd hl hη hη2 x hx]
  exact (ofReal_integral_eq_lintegral_ofReal (integrable_G_smear hd hl hη hη2 hx)
    (Filter.Eventually.of_forall fun y => sliceGfull_nonneg hl _)).symm

theorem lintegral_even {σ : Measure (Torus d)} (hσ : σ.map (fun x => -x) = σ) {F : Torus d → ℝ≥0∞}
    (hF : Measurable F) : ∫⁻ x, F x ∂σ = ∫⁻ x, F (-x) ∂σ := by
  conv_lhs => rw [← hσ]
  rw [lintegral_map hF measurable_neg]

theorem lintegral_G_smear' (hd : 1 ≤ d) (hl : 0 < l) (hη : 0 < η) (hη2 : η < 1 / 2) {z : Torus d}
    (hz : z ≠ 0) :
    ∫⁻ y, ENNReal.ofReal (sliceGfull d l (z + y)) ∂(smearT d l η) =
      ENNReal.ofReal (sliceGfull d l z - fTrunc d l η z) := by
  obtain ⟨-, hev, -, -⟩ := smearT_structure hd hl hη hη2
  have hF : Measurable fun y : Torus d => ENNReal.ofReal (sliceGfull d l (z + y)) :=
    ENNReal.measurable_ofReal.comp ((measurable_sliceGfull l).comp (measurable_const.add measurable_id))
  rw [lintegral_even hev hF]
  simp only [← sub_eq_add_neg]
  exact lintegral_G_smear hd hl hη hη2 hz

end Newton

section Pair

theorem lintegral_map_add (σ : Measure (Torus d)) (a : Torus d) (F : Torus d → ℝ≥0∞) :
    ∫⁻ x, F x ∂(σ.map (fun y => y + a)) = ∫⁻ x, F (x + a) ∂σ :=
  (MeasurableEquiv.addRight a).measurableEmbedding.lintegral_map F

variable {l : ℝ}

/-- Support of the smeared charge: `tdist ≤ η` almost everywhere. -/
theorem ae_tdist_le (hd : 1 ≤ d) (hl : 0 < l) {η : ℝ} (hη : 0 < η) (hη2 : η < 1 / 2) :
    ∀ᵐ x ∂(smearT d l η), KernelGrad.tdist x 0 ≤ η := by
  obtain ⟨-, -, hsupp, -⟩ := smearT_structure hd hl hη hη2
  have : ∀ᵐ x ∂(smearT d l η), x ∈ Torus.mk '' Metric.closedBall (0 : Euc d) η := by
    exact mem_ae_iff.mpr hsupp
  filter_upwards [this] with x hx
  obtain ⟨w, hw, rfl⟩ := hx
  exact (tdist_mk_le w).trans (by simpa using hw)

theorem lintegral_pair (hd : 1 ≤ d) (hl : 0 < l) {ηa ηb : ℝ} (ha : 0 < ηa) (ha2 : ηa < 1 / 2)
    (hb : 0 < ηb) (hb2 : ηb < 1 / 2) (X Y : Torus d) (hsep : ηa + ηb < KernelGrad.tdist X Y) :
    ∫⁻ x, ∫⁻ y, ENNReal.ofReal (sliceGfull d l (x - y)) ∂((smearT d l ηb).map (fun y => y + Y))
      ∂((smearT d l ηa).map (fun x => x + X)) = ENNReal.ofReal (sliceGfull d l (X - Y)) := by
  have hz : 0 < KernelGrad.tdist (X - Y) 0 := by rw [← tdist_def]; linarith
  have hzne : X - Y ≠ 0 := ne_zero_of_tdist_pos hz
  rw [lintegral_map_add]
  have hae := ae_tdist_le hd hl ha ha2
  have hcongr : ∀ᵐ x' ∂(smearT d l ηa),
      (∫⁻ y, ENNReal.ofReal (sliceGfull d l (x' + X - y)) ∂((smearT d l ηb).map (fun y => y + Y))) =
        ENNReal.ofReal (sliceGfull d l ((X - Y) + x')) := by
    filter_upwards [hae] with x' hx'
    have e := (tdist_def X Y).symm
    have h1 : KernelGrad.tdist ((X - Y) + x') 0 > ηb := by
      have := tdist_add_ge (X - Y) x'
      rw [add_comm x' (X - Y)] at this
      linarith
    have hne : (X - Y) + x' ≠ 0 := ne_zero_of_tdist_pos (by linarith)
    rw [lintegral_map_add]
    have e : ∀ y : Torus d, x' + X - (y + Y) = ((X - Y) + x') - y := fun y => by abel
    simp only [e]
    rw [lintegral_G_smear hd hl hb hb2 hne]
    have hf : fTrunc d l ηb ((X - Y) + x') = 0 := by
      refine (fTrunc_support hd hl hb hb2).2.1 _ ?_
      rw [norm_centeredRep_eq]; exact h1.le
    rw [hf, sub_zero]
  rw [lintegral_congr_ae hcongr]
  have e2 : ∀ x' : Torus d, X - Y + x' = (X - Y) + x' := fun _ => rfl
  rw [lintegral_G_smear' hd hl ha ha2 hzne]
  have hf : fTrunc d l ηa (X - Y) = 0 := by
    refine (fTrunc_support hd hl ha ha2).2.1 _ ?_
    rw [norm_centeredRep_eq, ← tdist_def]; linarith
  rw [hf, sub_zero]

end Pair


/-! ### From lintegrals to Bochner integrals -/

theorem integral_integral_eq_toReal {ν₁ ν₂ : Measure (Torus d)} [SFinite ν₁] [SFinite ν₂]
    {K : Torus d → Torus d → ℝ} (hK : Measurable (Function.uncurry K)) (hK0 : ∀ x y, 0 ≤ K x y)
    (hfin : ∫⁻ x, ∫⁻ y, ENNReal.ofReal (K x y) ∂ν₂ ∂ν₁ ≠ ⊤) :
    ∫ x, ∫ y, K x y ∂ν₂ ∂ν₁ = (∫⁻ x, ∫⁻ y, ENNReal.ofReal (K x y) ∂ν₂ ∂ν₁).toReal := by
  have hKx : ∀ x, Measurable fun y => K x y := fun x => hK.comp measurable_prodMk_left
  have hinner : ∀ x, ∫ y, K x y ∂ν₂ = (∫⁻ y, ENNReal.ofReal (K x y) ∂ν₂).toReal := fun x =>
    integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun y => hK0 x y)
      (hKx x).aestronglyMeasurable
  have hA : Measurable fun x => ∫⁻ y, ENNReal.ofReal (K x y) ∂ν₂ := by
    have : Measurable (Function.uncurry fun x y => ENNReal.ofReal (K x y)) :=
      ENNReal.measurable_ofReal.comp hK
    exact this.lintegral_prod_right'
  simp_rw [hinner]
  have hae : ∀ᵐ x ∂ν₁, (∫⁻ y, ENNReal.ofReal (K x y) ∂ν₂) ≠ ⊤ :=
    (ae_lt_top hA hfin).mono fun x hx => hx.ne
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun x => ENNReal.toReal_nonneg)
    (hA.ennreal_toReal.aestronglyMeasurable)]
  congr 1
  refine lintegral_congr_ae (hae.mono fun x hx => ?_)
  exact ENNReal.ofReal_toReal hx

section Main
variable {l : ℝ}

theorem lintegral_self_le (hd : 1 ≤ d) (hl : 0 < l) {η : ℝ} (hη : 0 < η) (hη2 : η < 1 / 2) :
    ∫⁻ x, ∫⁻ y, ENNReal.ofReal (sliceGfull d l (x - y)) ∂(smearT d l η) ∂(smearT d l η) ≤
      ∫⁻ x, ENNReal.ofReal (sliceGfull d l x) ∂(smearT d l η) := by
  have h0 : ∀ᵐ x ∂(smearT d l η), x ≠ 0 := by
    rw [ae_iff]; simpa using smearT_singleton_zero hd hη hη2
  refine lintegral_mono_ae (h0.mono fun x hx => ?_)
  rw [lintegral_G_smear hd hl hη hη2 hx]
  exact ENNReal.ofReal_le_ofReal (by have := (fTrunc_support hd hl hη hη2).1 x; linarith)

theorem lintegral_self_shift (σ : Measure (Torus d)) (a : Torus d) :
    ∫⁻ x, ∫⁻ y, ENNReal.ofReal (sliceGfull d l (x - y)) ∂(σ.map (fun y => y + a))
      ∂(σ.map (fun y => y + a)) =
    ∫⁻ x, ∫⁻ y, ENNReal.ofReal (sliceGfull d l (x - y)) ∂σ ∂σ := by
  rw [lintegral_map_add]
  simp_rw [lintegral_map_add]
  simp only [add_sub_add_right_eq_sub]

theorem lintegral_cross (hd : 1 ≤ d) (hl : 0 < l) {η : ℝ} (hη : 0 < η) (hη2 : η < 1 / 2)
    (X : Torus d) (μ : Measure (Torus d)) [IsFiniteMeasure μ] (hμ0 : ∀ x, μ {x} = 0) :
    ∫⁻ x, ∫⁻ y, ENNReal.ofReal (sliceGfull d l (x - y)) ∂μ ∂((smearT d l η).map (fun y => y + X)) =
      ∫⁻ y, ENNReal.ofReal (sliceGfull d l (X - y) - fTrunc d l η (X - y)) ∂μ := by
  obtain ⟨hfin, -, -, -⟩ := smearT_structure hd hl hη hη2
  rw [lintegral_map_add]
  have hmeas : Measurable (Function.uncurry fun (x : Torus d) (y : Torus d) =>
      ENNReal.ofReal (sliceGfull d l (x + X - y))) :=
    ENNReal.measurable_ofReal.comp ((measurable_sliceGfull l).comp
      ((measurable_fst.add measurable_const).sub measurable_snd))
  rw [lintegral_lintegral_swap hmeas.aemeasurable]
  have hae : ∀ᵐ y ∂μ, y ≠ X := by
    rw [ae_iff]; simpa using hμ0 X
  refine lintegral_congr_ae (hae.mono fun y hy => ?_)
  have hz : X - y ≠ 0 := sub_ne_zero.mpr (Ne.symm hy)
  have e : ∀ x' : Torus d, x' + X - y = (X - y) + x' := fun x' => by abel
  simp only [e]
  exact lintegral_G_smear' hd hl hη hη2 hz


theorem energy_identity_slice_aux {N : ℕ} (hd : 1 ≤ d) (hl : 0 < l) (μ : Measure (Torus d))
    [IsFiniteMeasure μ] (hμ0 : ∀ x, μ {x} = 0)
    (hμ1 : ∀ x, Integrable (fun y => sliceGfull d l (x - y)) μ)
    (X : Fin N → Torus d) (η : Fin N → ℝ) (hη : ∀ i, 0 < η i ∧ η i < 1 / 2)
    (hdisj : ∀ i j, i ≠ j → η i + η j < KernelGrad.tdist (X i) (X j))
    (ν : Measure (Torus d))
    (hν : ν = (N : ℝ≥0∞)⁻¹ • ∑ i, (smearT d l (η i)).map (fun y => y + X i)) :
    ∫ x, ∫ y, sliceGfull d l (x - y) ∂ν ∂ν - 2 * ∫ x, ∫ y, sliceGfull d l (x - y) ∂μ ∂ν
        + ∫ x, ∫ y, sliceGfull d l (x - y) ∂μ ∂μ =
      (1 / (N : ℝ) ^ 2) * ∑ i, ∑ j ∈ Finset.univ.erase i, sliceGfull d l (X i - X j)
      + (1 / (N : ℝ) ^ 2) * ∑ i, ∫ x, ∫ y, sliceGfull d l (x - y) ∂(smearT d l (η i)) ∂(smearT d l (η i))
      - (2 / (N : ℝ)) * ∑ i, ∫ y, (sliceGfull d l (X i - y) - fTrunc d l (η i) (X i - y)) ∂μ
      + ∫ x, ∫ y, sliceGfull d l (x - y) ∂μ ∂μ := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · subst hν
    simp

  set c : ℝ≥0∞ := (N : ℝ≥0∞)⁻¹ with hcdef
  have hc : c ≠ ⊤ := by
    rw [hcdef]; exact ENNReal.inv_ne_top.mpr (by simpa using hN.ne')
  have hcr : c.toReal = 1 / (N : ℝ) := by
    rw [hcdef, ENNReal.toReal_inv]; simp
  set σ : Fin N → Measure (Torus d) := fun i => smearT d l (η i) with hσ
  have hσfin : ∀ i, IsFiniteMeasure (σ i) := fun i =>
    (smearT_structure hd hl (hη i).1 (hη i).2).1
  set ν' : Fin N → Measure (Torus d) := fun i => (σ i).map (fun y => y + X i) with hν'
  have hν'fin : ∀ i, IsFiniteMeasure (ν' i) := fun i => by rw [hν']; infer_instance
  have hν2 : ν = c • ∑ i, ν' i := hν
  have : IsFiniteMeasure ν := by
    refine ⟨?_⟩
    rw [hν2]
    simp only [Measure.smul_apply, Measure.coe_finset_sum, Finset.sum_apply, smul_eq_mul]
    exact ENNReal.mul_lt_top hc.lt_top (ENNReal.sum_lt_top.mpr fun i _ => measure_lt_top _ _)
  set g : Torus d → ℝ := sliceGfull d l with hg
  have hgm : Measurable g := measurable_sliceGfull l
  have hg0 : ∀ z, 0 ≤ g z := sliceGfull_nonneg hl
  have hK : Measurable (Function.uncurry fun x y : Torus d => g (x - y)) :=
    hgm.comp (measurable_fst.sub measurable_snd)
  have hKA : Measurable (Function.uncurry fun x y : Torus d => ENNReal.ofReal (g (x - y))) :=
    ENNReal.measurable_ofReal.comp hK
  -- self energies
  set S : Fin N → ℝ≥0∞ := fun i => ∫⁻ x, ∫⁻ y, ENNReal.ofReal (g (x - y)) ∂(σ i) ∂(σ i) with hS
  have hSfin : ∀ i, S i ≠ ⊤ := fun i =>
    ((lintegral_self_le hd hl (hη i).1 (hη i).2).trans_lt
      (lintegral_smearT_g_lt_top hd hl (hη i).1 (hη i).2)).ne
  -- pair energies
  have hE : ∀ i j, ∫⁻ x, ∫⁻ y, ENNReal.ofReal (g (x - y)) ∂(ν' j) ∂(ν' i) =
      if i = j then S i else ENNReal.ofReal (g (X i - X j)) := by
    intro i j
    by_cases hij : i = j
    · subst hij
      rw [if_pos rfl]
      exact lintegral_self_shift (σ i) (X i)
    · rw [if_neg hij]
      exact lintegral_pair hd hl (hη i).1 (hη i).2 (hη j).1 (hη j).2 (X i) (X j) (hdisj i j hij)
  have hAm : ∀ j, Measurable fun x => ∫⁻ y, ENNReal.ofReal (g (x - y)) ∂(ν' j) := fun j =>
    hKA.lintegral_prod_right'
  have hEtot : ∫⁻ x, ∫⁻ y, ENNReal.ofReal (g (x - y)) ∂ν ∂ν =
      c * ∑ i, (c * ∑ j, if i = j then S i else ENNReal.ofReal (g (X i - X j))) := by
    rw [hν2]
    simp only [lintegral_smul_measure, lintegral_finset_sum_measure, smul_eq_mul]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [lintegral_const_mul' _ _ hc, lintegral_finset_sum _ fun j _ => hAm j]
    congr 1
    exact Finset.sum_congr rfl fun j _ => hE i j

  -- cross energies
  set Cc : Fin N → ℝ≥0∞ := fun i => ∫⁻ y, ENNReal.ofReal (g (X i - y) - fTrunc d l (η i) (X i - y)) ∂μ
    with hCc
  have hCfin : ∀ i, Cc i ≠ ⊤ := by
    intro i
    have h1 : Cc i ≤ ∫⁻ y, ENNReal.ofReal (g (X i - y)) ∂μ := by
      refine lintegral_mono fun y => ENNReal.ofReal_le_ofReal ?_
      have := (fTrunc_support hd hl (hη i).1 (hη i).2).1 (X i - y)
      linarith
    have h2 : ∫⁻ y, ENNReal.ofReal (g (X i - y)) ∂μ < ⊤ := by
      rw [← ofReal_integral_eq_lintegral_ofReal (hμ1 (X i))
        (Filter.Eventually.of_forall fun y => hg0 _)]
      exact ENNReal.ofReal_lt_top
    exact (h1.trans_lt h2).ne
  have hEcross : ∫⁻ x, ∫⁻ y, ENNReal.ofReal (g (x - y)) ∂μ ∂ν = c * ∑ i, Cc i := by
    rw [hν2]
    simp only [lintegral_smul_measure, lintegral_finset_sum_measure, smul_eq_mul]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    exact lintegral_cross hd hl (hη i).1 (hη i).2 (X i) μ hμ0
  -- real values
  have hEtotfin : (∫⁻ x, ∫⁻ y, ENNReal.ofReal (g (x - y)) ∂ν ∂ν) ≠ ⊤ := by
    rw [hEtot]
    refine ENNReal.mul_ne_top hc (ENNReal.sum_ne_top.mpr fun i _ => ENNReal.mul_ne_top hc
      (ENNReal.sum_ne_top.mpr fun j _ => ?_))
    split_ifs
    · exact hSfin i
    · exact ENNReal.ofReal_ne_top
  have hEcrossfin : (∫⁻ x, ∫⁻ y, ENNReal.ofReal (g (x - y)) ∂μ ∂ν) ≠ ⊤ := by
    rw [hEcross]
    exact ENNReal.mul_ne_top hc (ENNReal.sum_ne_top.mpr fun i _ => hCfin i)
  have hT1 := integral_integral_eq_toReal (ν₁ := ν) (ν₂ := ν) hK (fun x y => hg0 _) hEtotfin
  have hT2 := integral_integral_eq_toReal (ν₁ := ν) (ν₂ := μ) hK (fun x y => hg0 _) hEcrossfin
  have hTS : ∀ i, ∫ x, ∫ y, g (x - y) ∂(smearT d l (η i)) ∂(smearT d l (η i)) = (S i).toReal := fun i =>
    integral_integral_eq_toReal hK (fun x y => hg0 _) (hSfin i)
  have hTC : ∀ i, ∫ y, (g (X i - y) - fTrunc d l (η i) (X i - y)) ∂μ = (Cc i).toReal := by
    intro i
    have hae : ∀ᵐ y ∂μ, y ≠ X i := by
      rw [ae_iff]; simpa using hμ0 (X i)
    have hmeasU : Measurable fun y => g (X i - y) - fTrunc d l (η i) (X i - y) :=
      (hgm.comp (measurable_const.sub measurable_id)).sub
        ((measurable_fTrunc l (η i)).comp (measurable_const.sub measurable_id))
    exact integral_eq_lintegral_of_nonneg_ae
      (hae.mono fun y hy => (g_sub_f_pos hd hl (hη i).1 (sub_ne_zero.mpr (Ne.symm hy))).le)
      hmeasU.aestronglyMeasurable
  rw [hT1, hT2, hEtot, hEcross]
  simp only [hTC, hTS]
  have hsplit : ∀ i, (∑ j, if i = j then S i else ENNReal.ofReal (g (X i - X j))) =
      S i + ∑ j ∈ Finset.univ.erase i, ENNReal.ofReal (g (X i - X j)) := by
    intro i
    rw [← Finset.add_sum_erase (Finset.univ : Finset (Fin N))
      (fun j : Fin N => if i = j then S i else ENNReal.ofReal (g (X i - X j))) (Finset.mem_univ i)]
    simp only [if_true]
    congr 1
    exact Finset.sum_congr rfl fun j hj => by rw [if_neg (Ne.symm (Finset.ne_of_mem_erase hj))]
  have hE1 : (c * ∑ i, c * ∑ j, if i = j then S i else ENNReal.ofReal (g (X i - X j))).toReal =
      (1 / (N : ℝ)) ^ 2 * ∑ i, ((S i).toReal + ∑ j ∈ Finset.univ.erase i, g (X i - X j)) := by
    simp only [hsplit]
    have hfin : ∀ i, (S i + ∑ j ∈ Finset.univ.erase i, ENNReal.ofReal (g (X i - X j))) ≠ ⊤ := fun i =>
      ENNReal.add_ne_top.mpr ⟨hSfin i, ENNReal.sum_ne_top.mpr fun j _ => ENNReal.ofReal_ne_top⟩
    rw [ENNReal.toReal_mul, ENNReal.toReal_sum (fun i _ => ENNReal.mul_ne_top hc (hfin i)), hcr]
    have hterm : ∀ i, (c * (S i + ∑ j ∈ Finset.univ.erase i, ENNReal.ofReal (g (X i - X j)))).toReal =
        1 / (N : ℝ) * ((S i).toReal + ∑ j ∈ Finset.univ.erase i, g (X i - X j)) := by
      intro i
      have hsf : (∑ j ∈ Finset.univ.erase i, ENNReal.ofReal (g (X i - X j))) ≠ ⊤ :=
        ENNReal.sum_ne_top.mpr fun j _ => ENNReal.ofReal_ne_top
      rw [ENNReal.toReal_mul, hcr, ENNReal.toReal_add (hSfin i) hsf,
        ENNReal.toReal_sum (s := Finset.univ.erase i) (fun j _ => ENNReal.ofReal_ne_top)]
      congr 2
      exact Finset.sum_congr rfl fun j _ => ENNReal.toReal_ofReal (hg0 _)
    simp only [hterm]
    rw [← Finset.mul_sum, sq, mul_assoc]
  have hE2 : (c * ∑ i, Cc i).toReal = (1 / (N : ℝ)) * ∑ i, (Cc i).toReal := by
    rw [ENNReal.toReal_mul, ENNReal.toReal_sum (fun i _ => hCfin i), hcr]
  rw [hE1, hE2]
  have hNn : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  simp only [Finset.sum_add_distrib, mul_add]
  field_simp
  ring

end Main


end HRS.Commutator.EnergyAux
