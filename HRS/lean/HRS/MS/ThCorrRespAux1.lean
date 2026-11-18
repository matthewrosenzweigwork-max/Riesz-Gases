import HRS.Whole.Q34Aux18

/-!
# TC-2 (response operator), part 1: the integral operator of a nonnegative symmetric kernel on `L²(ν)`

Namespace `HRS.MS.TcR`; helper lemmas carry the prefix `tc2_`.  No existing file is edited.

For a probability measure `ν` and a nonnegative symmetric measurable kernel `k` the structure `TcKer ν k Mg` records
the lintegral Schur bound `∫⁻ (∫⁻ k(x,y) |u(y)| dν(y))² dν(x) ≤ Mg² ∫ u² dν`; separately `TcPos ν k` is the conditional positivity
`0 ≤ ∫ (∫ k(x,y) u(y) dν(y)) u(x) dν(x)` for centered `u ∈ L²(ν)`.  From these we build, exactly as in
`HRS/Whole/Q34Aux10..17` (which treats the Riesz kernel with `s > 0`), the Bochner potential `tc2_T ν k u`,
its `L²` bound, a.e. integrability of `y ↦ k x y u y`, the symmetry `⟨Tu,v⟩ = ⟨u,Tv⟩`, the bounded operator
`tc2_TopL hk` on `Lp ℝ 2 ν`, and the centered operator `tc2_Kc hk = P T P`
(`P = Q34.Pc`), which is symmetric, nonnegative and `‖Kc U‖ ≤ Mg ‖U‖`.
-/

noncomputable section

open MeasureTheory Filter Topology Set Metric InnerProductSpace
open scoped ENNReal NNReal

namespace HRS.MS.TcR

open HRS.Whole HRS.Whole.Q34

variable {d : ℕ}

/-- The potential `T u (x) = ∫ k(x,y) u(y) dν(y)`. -/
def tc2_T (ν : Measure (Euc d)) (k : Euc d → Euc d → ℝ) (u : Euc d → ℝ) (x : Euc d) : ℝ :=
  ∫ y, k x y * u y ∂ν

/-- The `lintegral` majorant `N_u(x) = ∫ k(x,y) |u(y)| dν(y)`. -/
def tc2_Nu (ν : Measure (Euc d)) (k : Euc d → Euc d → ℝ) (u : Euc d → ℝ) (x : Euc d) : ℝ≥0∞ :=
  ∫⁻ y, ENNReal.ofReal (k x y) * ENNReal.ofReal |u y| ∂ν

/-- Hypotheses on a kernel `k` and a measure `ν`: measurable, nonnegative, symmetric, a Schur bound with constant
`Mg`, and positivity on centered `L²(ν)`-functions. -/
structure TcKer (ν : Measure (Euc d)) (k : Euc d → Euc d → ℝ) (Mg : ℝ) : Prop where
  meas : Measurable (fun p : Euc d × Euc d => k p.1 p.2)
  nonneg : ∀ x y, 0 ≤ k x y
  symm : ∀ x y, k x y = k y x
  mg_nonneg : 0 ≤ Mg
  bound : ∀ u : Euc d → ℝ, Measurable u → MemLp u 2 ν →
    ∫⁻ x, tc2_Nu ν k u x ^ 2 ∂ν ≤ ENNReal.ofReal (Mg ^ 2 * ∫ x, u x ^ 2 ∂ν)

/-- Conditional positivity of the potential: `0 ≤ ∫ (T u) u dν` for centered `u ∈ L²(ν)`.  Kept separate from `TcKer`
because the pair integrability needed to prove it is a consequence of `TcKer`. -/
def TcPos (ν : Measure (Euc d)) (k : Euc d → Euc d → ℝ) : Prop :=
  ∀ u : Euc d → ℝ, Measurable u → MemLp u 2 ν → ∫ x, u x ∂ν = 0 →
    0 ≤ ∫ x, tc2_T ν k u x * u x ∂ν

section Pot

variable {ν : Measure (Euc d)} [IsProbabilityMeasure ν] {k : Euc d → Euc d → ℝ} {Mg : ℝ}

theorem tc2_T_measurable (hk : TcKer ν k Mg) {u : Euc d → ℝ} (hu : Measurable u) :
    Measurable (tc2_T ν k u) := by
  have hsm : StronglyMeasurable (fun p : Euc d × Euc d => k p.1 p.2 * u p.2) :=
    (hk.meas.mul (hu.comp measurable_snd)).stronglyMeasurable
  exact (hsm.integral_prod_right' (ν := ν)).measurable

theorem tc2_Nu_measurable (hk : TcKer ν k Mg) {u : Euc d → ℝ} (hu : Measurable u) :
    Measurable (tc2_Nu ν k u) := by
  unfold tc2_Nu
  exact Measurable.lintegral_prod_right' (f := fun p : Euc d × Euc d =>
    ENNReal.ofReal (k p.1 p.2) * ENNReal.ofReal |u p.2|)
    (hk.meas.ennreal_ofReal.mul (hu.comp measurable_snd).abs.ennreal_ofReal)

theorem tc2_ofReal_abs_T_le (hk : TcKer ν k Mg) (u : Euc d → ℝ) (x : Euc d) :
    ENNReal.ofReal |tc2_T ν k u x| ≤ tc2_Nu ν k u x := by
  have := enorm_integral_le_lintegral_enorm (μ := ν) (fun y => k x y * u y)
  rw [Real.enorm_eq_ofReal_abs] at this
  refine this.trans (le_of_eq ?_)
  refine lintegral_congr fun y => ?_
  rw [Real.enorm_eq_ofReal_abs, abs_mul, abs_of_nonneg (hk.nonneg x y),
    ENNReal.ofReal_mul (hk.nonneg x y)]

theorem tc2_T_memLp (hk : TcKer ν k Mg) {u : Euc d → ℝ} (hu : Measurable u) (hu2 : MemLp u 2 ν) :
    MemLp (tc2_T ν k u) 2 ν ∧ ∫ x, tc2_T ν k u x ^ 2 ∂ν ≤ Mg ^ 2 * ∫ x, u x ^ 2 ∂ν := by
  have hTm := tc2_T_measurable hk hu
  have hc : 0 ≤ Mg ^ 2 * ∫ x, u x ^ 2 ∂ν :=
    mul_nonneg (sq_nonneg _) (integral_nonneg fun x => sq_nonneg _)
  have hN := hk.bound u hu hu2
  obtain ⟨hI, hV⟩ := integrable_of_lintegral_le (μ := ν)
    (f := fun x => tc2_T ν k u x ^ 2) (hTm.pow_const 2) (fun x => sq_nonneg _) hc
    ((lintegral_mono fun x => by
      calc ENNReal.ofReal (tc2_T ν k u x ^ 2)
          = ENNReal.ofReal |tc2_T ν k u x| ^ 2 := by
            rw [← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]
        _ ≤ tc2_Nu ν k u x ^ 2 := pow_le_pow_left' (tc2_ofReal_abs_T_le hk u x) 2).trans hN)
  exact ⟨(memLp_two_iff_integrable_sq hTm.aestronglyMeasurable).2 hI, hV⟩

/-- For `ν`-a.e. `x` the integrand `y ↦ k x y u y` is integrable (no junk value in `tc2_T`). -/
theorem tc2_T_ae_integrable (hk : TcKer ν k Mg) {u : Euc d → ℝ} (hu : Measurable u)
    (hu2 : MemLp u 2 ν) : ∀ᵐ x ∂ν, Integrable (fun y => k x y * u y) ν := by
  have hN := hk.bound u hu hu2
  have hfin : ∀ᵐ x ∂ν, tc2_Nu ν k u x ^ 2 < ∞ :=
    ae_lt_top ((tc2_Nu_measurable hk hu).pow_const 2)
      (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hN)
  filter_upwards [hfin] with x hx
  have hx' : tc2_Nu ν k u x < ∞ := by
    by_contra h
    rw [not_lt, top_le_iff] at h
    rw [h] at hx
    simp at hx
  refine ⟨?_, ?_⟩
  · exact ((hk.meas.comp (measurable_const.prodMk measurable_id)).mul hu).aestronglyMeasurable
  · have : ∫⁻ y, ‖k x y * u y‖ₑ ∂ν = tc2_Nu ν k u x := by
      refine lintegral_congr fun y => ?_
      rw [Real.enorm_eq_ofReal_abs, abs_mul, abs_of_nonneg (hk.nonneg x y),
        ENNReal.ofReal_mul (hk.nonneg x y)]
    simp only [HasFiniteIntegral, this]
    exact hx'

theorem tc2_T_congr_ae {u u' : Euc d → ℝ} (h : u =ᵐ[ν] u') : tc2_T ν k u = tc2_T ν k u' := by
  funext x
  unfold tc2_T
  refine integral_congr_ae ?_
  filter_upwards [h] with y hy
  rw [hy]

theorem tc2_T_smul (c : ℝ) (u : Euc d → ℝ) : tc2_T ν k (c • u) = c • tc2_T ν k u := by
  funext x
  unfold tc2_T
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  ring

theorem tc2_T_add_ae (hk : TcKer ν k Mg) {u v : Euc d → ℝ} (hu : Measurable u) (hv : Measurable v)
    (hu2 : MemLp u 2 ν) (hv2 : MemLp v 2 ν) :
    tc2_T ν k (u + v) =ᵐ[ν] tc2_T ν k u + tc2_T ν k v := by
  filter_upwards [tc2_T_ae_integrable hk hu hu2, tc2_T_ae_integrable hk hv hv2] with x h1 h2
  unfold tc2_T
  simp only [Pi.add_apply, mul_add]
  exact integral_add h1 h2

/-- Integrability of the pair integrand. -/
theorem tc2_pair_integrable (hk : TcKer ν k Mg) {u v : Euc d → ℝ} (hu : Measurable u)
    (hv : Measurable v) (hu2 : MemLp u 2 ν) (hv2 : MemLp v 2 ν) :
    Integrable (fun p : Euc d × Euc d => k p.1 p.2 * u p.2 * v p.1) (ν.prod ν) := by
  have hmeas : Measurable (fun p : Euc d × Euc d => k p.1 p.2 * u p.2 * v p.1) :=
    (hk.meas.mul (hu.comp measurable_snd)).mul (hv.comp measurable_fst)
  refine ⟨hmeas.aestronglyMeasurable, ?_⟩
  have hN := hk.bound u hu hu2
  have hv_int : ∫⁻ x, ENNReal.ofReal |v x| ^ 2 ∂ν < ∞ := by
    have : ∫⁻ x, ENNReal.ofReal |v x| ^ 2 ∂ν = ENNReal.ofReal (∫ x, v x ^ 2 ∂ν) := by
      rw [ofReal_integral_eq_lintegral_ofReal (hv2.integrable_sq)
        (Filter.Eventually.of_forall fun x => sq_nonneg _)]
      refine lintegral_congr fun y => ?_
      rw [← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]
    rw [this]; exact ENNReal.ofReal_lt_top
  have hrw : ∫⁻ p, ‖k p.1 p.2 * u p.2 * v p.1‖ₑ ∂(ν.prod ν) =
      ∫⁻ x, ENNReal.ofReal |v x| * tc2_Nu ν k u x ∂ν := by
    rw [lintegral_prod _ (hmeas.enorm.aemeasurable)]
    refine lintegral_congr fun x => ?_
    have : ∀ y : Euc d, ‖k (x, y).1 (x, y).2 * u (x, y).2 * v (x, y).1‖ₑ =
        ENNReal.ofReal |v x| * (ENNReal.ofReal (k x y) * ENNReal.ofReal |u y|) := by
      intro y
      simp only
      rw [Real.enorm_eq_ofReal_abs, abs_mul, abs_mul, abs_of_nonneg (hk.nonneg x y),
        ENNReal.ofReal_mul (mul_nonneg (hk.nonneg x y) (abs_nonneg _)),
        ENNReal.ofReal_mul (hk.nonneg x y)]
      ring
    simp_rw [this]
    have hm : Measurable (fun y : Euc d => ENNReal.ofReal (k x y) * ENNReal.ofReal |u y|) :=
      (hk.meas.comp (measurable_const.prodMk measurable_id)).ennreal_ofReal.mul
        hu.abs.ennreal_ofReal
    rw [lintegral_const_mul _ hm]
    rfl
  simp only [HasFiniteIntegral, hrw]
  calc ∫⁻ x, ENNReal.ofReal |v x| * tc2_Nu ν k u x ∂ν
      ≤ ∫⁻ x, (ENNReal.ofReal |v x| ^ 2 + tc2_Nu ν k u x ^ 2) ∂ν :=
        lintegral_mono fun x => mul_le_sq_add_sq _ _
    _ = ∫⁻ x, ENNReal.ofReal |v x| ^ 2 ∂ν + ∫⁻ x, tc2_Nu ν k u x ^ 2 ∂ν :=
        lintegral_add_left (hv.abs.ennreal_ofReal.pow_const 2) _
    _ < ∞ := ENNReal.add_lt_top.2 ⟨hv_int, hN.trans_lt ENNReal.ofReal_lt_top⟩

/-- Symmetry of the potential: `⟨T u, v⟩ = ⟨u, T v⟩`. -/
theorem tc2_T_symm (hk : TcKer ν k Mg) {u v : Euc d → ℝ} (hu : Measurable u) (hv : Measurable v)
    (hu2 : MemLp u 2 ν) (hv2 : MemLp v 2 ν) :
    ∫ x, tc2_T ν k u x * v x ∂ν = ∫ x, u x * tc2_T ν k v x ∂ν := by
  have hI := tc2_pair_integrable hk hu hv hu2 hv2
  have h1 : ∫ x, tc2_T ν k u x * v x ∂ν = ∫ x, ∫ y, k x y * u y * v x ∂ν ∂ν := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [tc2_T]
    rw [← integral_mul_const]
  have h2 : ∫ x, u x * tc2_T ν k v x ∂ν = ∫ y, ∫ x, k x y * u y * v x ∂ν ∂ν := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [tc2_T]
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    show u y * (k y x * v x) = k x y * u y * v x
    rw [hk.symm y x]
    ring
  rw [h1, h2]
  exact integral_integral_swap (f := fun x y => k x y * u y * v x) hI

end Pot

section Op

variable {ν : Measure (Euc d)} [IsProbabilityMeasure ν] {k : Euc d → Euc d → ℝ} {Mg : ℝ}

/-- The integral operator on classes of `L²(ν)`. -/
def tc2_Top (hk : TcKer ν k Mg) (U : Lp ℝ 2 ν) : Lp ℝ 2 ν :=
  (tc2_T_memLp hk (mrep_measurable U) (mrep_memLp U)).1.toLp (tc2_T ν k (mrep U))

theorem tc2_top_ae (hk : TcKer ν k Mg) (U : Lp ℝ 2 ν) :
    (tc2_Top hk U : Euc d → ℝ) =ᵐ[ν] tc2_T ν k (U : Euc d → ℝ) := by
  have h1 := MemLp.coeFn_toLp (tc2_T_memLp hk (mrep_measurable U) (mrep_memLp U)).1
  rw [tc2_T_congr_ae (mrep_ae U)]
  exact h1

theorem tc2_top_add (hk : TcKer ν k Mg) (U V : Lp ℝ 2 ν) :
    tc2_Top hk (U + V) = tc2_Top hk U + tc2_Top hk V := by
  refine Lp.ext ?_
  have hUV : ((U + V : Lp ℝ 2 ν) : Euc d → ℝ) =ᵐ[ν] mrep U + mrep V := by
    filter_upwards [Lp.coeFn_add U V, mrep_ae U, mrep_ae V] with x h1 h2 h3
    rw [h1, Pi.add_apply, Pi.add_apply, h2, h3]
  have hadd := tc2_T_add_ae hk (mrep_measurable U) (mrep_measurable V) (mrep_memLp U)
    (mrep_memLp V)
  have e1 := tc2_T_congr_ae (k := k) hUV
  have e2 := tc2_T_congr_ae (k := k) (mrep_ae U)
  have e3 := tc2_T_congr_ae (k := k) (mrep_ae V)
  filter_upwards [tc2_top_ae hk (U + V), Lp.coeFn_add (tc2_Top hk U) (tc2_Top hk V),
    tc2_top_ae hk U, tc2_top_ae hk V, hadd] with x h1 h2 h3 h4 h5
  rw [h2, Pi.add_apply, h1, e1, h5, Pi.add_apply, h3, h4, e2, e3]

theorem tc2_top_smul (hk : TcKer ν k Mg) (c : ℝ) (U : Lp ℝ 2 ν) :
    tc2_Top hk (c • U) = c • tc2_Top hk U := by
  refine Lp.ext ?_
  have hU : ((c • U : Lp ℝ 2 ν) : Euc d → ℝ) =ᵐ[ν] c • mrep U := by
    filter_upwards [Lp.coeFn_smul c U, mrep_ae U] with x h1 h2
    rw [h1, Pi.smul_apply, Pi.smul_apply, h2]
  have e1 := tc2_T_congr_ae (k := k) hU
  have e2 := tc2_T_congr_ae (k := k) (mrep_ae U)
  filter_upwards [tc2_top_ae hk (c • U), Lp.coeFn_smul c (tc2_Top hk U), tc2_top_ae hk U]
    with x h1 h2 h3
  rw [h2, Pi.smul_apply, h1, e1, tc2_T_smul, Pi.smul_apply, h3, e2]

theorem tc2_top_norm_le (hk : TcKer ν k Mg) (U : Lp ℝ 2 ν) : ‖tc2_Top hk U‖ ≤ Mg * ‖U‖ := by
  have hMg0 := hk.mg_nonneg
  have hb := (tc2_T_memLp hk (mrep_measurable U) (mrep_memLp U)).2
  have e1 : ‖tc2_Top hk U‖ ^ 2 = ∫ x, tc2_T ν k (mrep U) x ^ 2 ∂ν := by
    rw [lp_norm_sq]
    refine integral_congr_ae ?_
    filter_upwards [tc2_top_ae hk U] with x hx
    rw [hx, tc2_T_congr_ae (mrep_ae U)]
  have e2 : ‖U‖ ^ 2 = ∫ x, mrep U x ^ 2 ∂ν := by
    rw [lp_norm_sq]
    refine integral_congr_ae ?_
    filter_upwards [mrep_ae U] with x hx
    rw [hx]
  have : ‖tc2_Top hk U‖ ^ 2 ≤ (Mg * ‖U‖) ^ 2 := by
    rw [e1, mul_pow, e2]; exact hb
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hMg0 (norm_nonneg _))).1 this

theorem tc2_top_inner_ae (hk : TcKer ν k Mg) (U V : Lp ℝ 2 ν) :
    inner ℝ (tc2_Top hk U) V = ∫ x, tc2_T ν k (mrep U) x * mrep V x ∂ν := by
  rw [lp_inner]
  refine integral_congr_ae ?_
  filter_upwards [tc2_top_ae hk U, mrep_ae V] with x h1 h2
  rw [h1, h2, tc2_T_congr_ae (mrep_ae U)]

theorem tc2_top_symm (hk : TcKer ν k Mg) (U V : Lp ℝ 2 ν) :
    inner ℝ (tc2_Top hk U) V = inner ℝ U (tc2_Top hk V) := by
  rw [tc2_top_inner_ae hk U V, real_inner_comm, tc2_top_inner_ae hk V U,
    tc2_T_symm hk (mrep_measurable U) (mrep_measurable V) (mrep_memLp U) (mrep_memLp V)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  ring

/-- Nonnegativity on centered classes. -/
theorem tc2_top_pos (hk : TcKer ν k Mg) (hp : TcPos ν k) (U : Lp ℝ 2 ν) (hU : inner ℝ (one2 ν) U = 0) :
    0 ≤ inner ℝ (tc2_Top hk U) U := by
  rw [tc2_top_inner_ae hk U U]
  have hmean : ∫ x, mrep U x ∂ν = 0 :=
    (integral_congr_ae (mrep_ae U)).symm.trans ((inner_one2 U).symm.trans hU)
  exact hp (mrep U) (mrep_measurable U) (mrep_memLp U) hmean

/-- The integral operator as a continuous linear map on `L²(ν)`. -/
def tc2_TopL (hk : TcKer ν k Mg) : Lp ℝ 2 ν →L[ℝ] Lp ℝ 2 ν :=
  LinearMap.mkContinuous
    { toFun := tc2_Top hk
      map_add' := tc2_top_add hk
      map_smul' := fun c U => tc2_top_smul hk c U } Mg (tc2_top_norm_le hk)

theorem tc2_topL_apply (hk : TcKer ν k Mg) (U : Lp ℝ 2 ν) : tc2_TopL hk U = tc2_Top hk U := rfl

/-- The centered operator `K' = P T P` on `L²(ν)`. -/
def tc2_Kc (hk : TcKer ν k Mg) : Lp ℝ 2 ν →L[ℝ] Lp ℝ 2 ν :=
  (Pc ν).comp ((tc2_TopL hk).comp (Pc ν))

theorem tc2_Kc_apply (hk : TcKer ν k Mg) (U : Lp ℝ 2 ν) :
    tc2_Kc hk U = Pc ν (tc2_Top hk (Pc ν U)) := rfl

theorem tc2_Kc_symm (hk : TcKer ν k Mg) (U V : Lp ℝ 2 ν) :
    inner ℝ (tc2_Kc hk U) V = inner ℝ U (tc2_Kc hk V) := by
  rw [tc2_Kc_apply, tc2_Kc_apply, Pc_symm, tc2_top_symm, ← Pc_symm]

theorem tc2_Kc_pos (hk : TcKer ν k Mg) (hp : TcPos ν k) (U : Lp ℝ 2 ν) : 0 ≤ inner ℝ (tc2_Kc hk U) U := by
  rw [tc2_Kc_apply, Pc_symm]
  exact tc2_top_pos hk hp _ (inner_one2_Pc U)

theorem tc2_Kc_norm_le (hk : TcKer ν k Mg) (U : Lp ℝ 2 ν) : ‖tc2_Kc hk U‖ ≤ Mg * ‖U‖ := by
  have hMg0 := hk.mg_nonneg
  calc ‖tc2_Kc hk U‖ ≤ ‖tc2_Top hk (Pc ν U)‖ := Pc_norm_le _
    _ ≤ Mg * ‖Pc ν U‖ := tc2_top_norm_le hk _
    _ ≤ Mg * ‖U‖ := mul_le_mul_of_nonneg_left (Pc_norm_le U) hMg0

theorem tc2_Pc_Kc (hk : TcKer ν k Mg) (U : Lp ℝ 2 ν) : Pc ν (tc2_Kc hk U) = tc2_Kc hk U := by
  rw [tc2_Kc_apply, Pc_idem]

/-- On a centered class `U`, `K' U` is the centered potential of `U`. -/
theorem tc2_Kc_ae (hk : TcKer ν k Mg) (U : Lp ℝ 2 ν) (hU : Pc ν U = U) :
    (tc2_Kc hk U : Euc d → ℝ) =ᵐ[ν]
      fun x => tc2_T ν k (U : Euc d → ℝ) x - ∫ y, tc2_T ν k (U : Euc d → ℝ) y ∂ν := by
  rw [tc2_Kc_apply, hU, Pc_apply]
  have hmean : inner ℝ (one2 ν) (tc2_Top hk U) = ∫ y, tc2_T ν k (U : Euc d → ℝ) y ∂ν := by
    rw [inner_one2]
    exact integral_congr_ae (tc2_top_ae hk U)
  filter_upwards [Lp.coeFn_sub (tc2_Top hk U) (inner ℝ (one2 ν) (tc2_Top hk U) • one2 ν),
    Lp.coeFn_smul (inner ℝ (one2 ν) (tc2_Top hk U)) (one2 ν), one2_ae (ν := ν),
    tc2_top_ae hk U] with x h1 h2 h3 h4
  rw [h1, Pi.sub_apply, h2, Pi.smul_apply, h3, h4, hmean]
  simp

end Op

end HRS.MS.TcR

end
