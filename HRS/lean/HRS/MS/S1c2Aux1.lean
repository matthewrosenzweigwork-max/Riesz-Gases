import HRS.MS.SuppU8Aux16
import HRS.MS.SuppU8Aux19

/-!
# S1C2 aux 1: `L^p` calculus of iterated differences

Infrastructure for the `L^p` fractional derivative by central differences (S.A.1, claim 2).
Contents (all helper statements, none is a frozen row):

* `s1c2_jensen`, `s1c2_mink`: Jensen and a weighted Minkowski (integral) inequality for `ℝ≥0∞`-valued
  integrands, with exponent `1 < p < ∞`.
* `s1c2_fd_lp_crude`: `‖Δ_{h_1}⋯Δ_{h_k} u‖_p ≤ 2^k ‖u‖_p`.
* `s1c2_fd_lp_taylor`: `‖Δ_y^k u‖_p ≤ ‖y‖^k ‖D^k u‖_p` (for `u ∈ C^k`, values in any real Banach space).
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace HRS.S1C2

open HRS.U8

/-! ### Jensen and Minkowski for `ℝ≥0∞`-valued integrands -/

theorem s1c2_jensen {Y : Type*} [MeasurableSpace Y] (ν : Measure Y) {p : ℝ} (hp : 1 < p)
    {f : Y → ℝ≥0∞} (hf : AEMeasurable f ν) :
    (∫⁻ y, f y ∂ν) ^ p ≤ (ν univ) ^ (p - 1) * ∫⁻ y, f y ^ p ∂ν := by
  have hpq := Real.HolderConjugate.conjExponent hp
  set q := Real.conjExponent p with hq
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq ν hpq hf (aemeasurable_const (b := (1 : ℝ≥0∞)))
  simp only [Pi.mul_apply, mul_one, ENNReal.one_rpow, lintegral_const, one_mul] at h
  have hp0 : 0 ≤ p := by linarith
  have h2 := ENNReal.rpow_le_rpow h hp0
  rw [ENNReal.mul_rpow_of_nonneg _ _ hp0, ← ENNReal.rpow_mul, ← ENNReal.rpow_mul] at h2
  have e1 : 1 / p * p = 1 := by field_simp
  have e2 : 1 / q * p = p - 1 := by
    have := hpq.div_conj_eq_sub_one
    rw [← this]; field_simp
  rw [e1, e2, ENNReal.rpow_one] at h2
  rw [mul_comm]
  exact h2

/-- Weighted Minkowski inequality (Jensen form): for `θ ψ = 1` a.e., `1 < p`,
`∫ (∫ K G dν)^p dμ ≤ (∫ K θ dν)^{p-1} ∫ K θ ψ^p (∫ G^p dμ) dν`. -/
theorem s1c2_mink {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] (μ : Measure X)
    (ν : Measure Y) [SFinite μ] [SFinite ν] {p : ℝ} (hp : 1 < p)
    (K θ ψ : Y → ℝ≥0∞) (hK : Measurable K) (hθ : Measurable θ) (hψ : Measurable ψ)
    (hθψ : ∀ᵐ y ∂ν, θ y * ψ y = 1)
    (G : X → Y → ℝ≥0∞) (hG : Measurable (Function.uncurry G)) :
    ∫⁻ x, (∫⁻ y, K y * G x y ∂ν) ^ p ∂μ ≤
      (∫⁻ y, K y * θ y ∂ν) ^ (p - 1) *
        ∫⁻ y, K y * θ y * ψ y ^ p * ∫⁻ x, G x y ^ p ∂μ ∂ν := by
  set ν' : Measure Y := ν.withDensity (fun y => K y * θ y) with hν'
  have hKθ : Measurable (fun y => K y * θ y) := hK.mul hθ
  have hGx : ∀ x, Measurable (G x) := fun x => hG.comp measurable_prodMk_left
  have hGy : ∀ y, Measurable (fun x => G x y) := fun y => hG.comp measurable_prodMk_right
  have hpt : ∀ x, ∫⁻ y, K y * G x y ∂ν = ∫⁻ y, ψ y * G x y ∂ν' := by
    intro x
    have h1 := lintegral_withDensity_eq_lintegral_mul ν hKθ
      (g := fun y => ψ y * G x y) (hψ.mul (hGx x))
    try simp only [Pi.mul_apply] at h1
    rw [hν', h1]
    refine lintegral_congr_ae ?_
    filter_upwards [hθψ] with y hy
    calc K y * G x y = K y * (θ y * ψ y) * G x y := by rw [hy, mul_one]
      _ = K y * θ y * (ψ y * G x y) := by ring
  have hν'univ : ν' univ = ∫⁻ y, K y * θ y ∂ν := by
    rw [hν', withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  calc ∫⁻ x, (∫⁻ y, K y * G x y ∂ν) ^ p ∂μ
      = ∫⁻ x, (∫⁻ y, ψ y * G x y ∂ν') ^ p ∂μ := by simp_rw [hpt]
    _ ≤ ∫⁻ x, (ν' univ) ^ (p - 1) * ∫⁻ y, (ψ y * G x y) ^ p ∂ν' ∂μ := by
        refine lintegral_mono (fun x => ?_)
        exact s1c2_jensen ν' hp (hψ.mul (hGx x)).aemeasurable
    _ = (ν' univ) ^ (p - 1) * ∫⁻ x, ∫⁻ y, (ψ y * G x y) ^ p ∂ν' ∂μ := by
        have hm : Measurable (fun x => ∫⁻ y, (ψ y * G x y) ^ p ∂ν') := by
          have : Measurable (Function.uncurry fun x y => (ψ y * G x y) ^ p) :=
            ((hψ.comp measurable_snd).mul hG).pow_const _
          exact this.lintegral_prod_right'
        rw [lintegral_const_mul'' _ hm.aemeasurable]
    _ = (ν' univ) ^ (p - 1) * ∫⁻ x, ∫⁻ y, K y * θ y * (ψ y * G x y) ^ p ∂ν ∂μ := by
        congr 1
        refine lintegral_congr (fun x => ?_)
        have h1 := lintegral_withDensity_eq_lintegral_mul ν hKθ
          (g := fun y => (ψ y * G x y) ^ p) ((hψ.mul (hGx x)).pow_const _)
        try simp only [Pi.mul_apply] at h1
        rw [hν', h1]
    _ = (ν' univ) ^ (p - 1) * ∫⁻ y, ∫⁻ x, K y * θ y * (ψ y * G x y) ^ p ∂μ ∂ν := by
        congr 1
        refine lintegral_lintegral_swap ?_
        have : Measurable (Function.uncurry fun x y => K y * θ y * (ψ y * G x y) ^ p) :=
          (hKθ.comp measurable_snd).mul (((hψ.comp measurable_snd).mul hG).pow_const _)
        exact this.aemeasurable
    _ = _ := by
        rw [hν'univ]
        congr 1
        refine lintegral_congr (fun y => ?_)
        have hm : Measurable (fun x => G x y ^ p) := (hGy y).pow_const _
        rw [← lintegral_const_mul'' _ hm.aemeasurable]
        refine lintegral_congr (fun x => ?_)
        have hp0 : 0 ≤ p := by linarith
        rw [ENNReal.mul_rpow_of_nonneg _ _ hp0]
        ring

/-! ### Algebra of `u8_fd` -/

theorem s1c2_fd_append {V E : Type*} [AddCommGroup V] [AddCommGroup E] (L1 L2 : List V)
    (u : V → E) : u8_fd (L1 ++ L2) u = u8_fd L2 (u8_fd L1 u) := by
  induction L1 generalizing u with
  | nil => rfl
  | cons h hs ih =>
    rw [List.cons_append, u8_fd_cons, u8_fd_cons, ih]

theorem s1c2_fd_cont {V E : Type*} [NormedAddCommGroup V] [NormedAddCommGroup E]
    (L : List V) {u : V → E} (hu : Continuous u) : Continuous (u8_fd L u) := by
  induction L generalizing u with
  | nil => exact hu
  | cons h hs ih =>
    rw [u8_fd_cons]
    exact ih ((hu.comp (continuous_id.add continuous_const)).sub hu)

theorem s1c2_fd_clm {V E E' : Type*} [AddCommGroup V] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup E'] [NormedSpace ℝ E'] (T : E →L[ℝ] E') (L : List V) (u : V → E) :
    u8_fd L (fun x => T (u x)) = fun x => T (u8_fd L u x) := by
  induction L generalizing u with
  | nil => rfl
  | cons h hs ih =>
    rw [u8_fd_cons, u8_fd_cons]
    have : (fun x => T (u (x + h)) - T (u x)) = fun x => T (u (x + h) - u x) := by
      funext x; rw [map_sub]
    rw [this, ih]

/-! ### `L^p` norms -/

/-- `∫⁻ ‖u‖ₑ^p`. -/
def Ip {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E] (μ : Measure α) (p : ℝ)
    (u : α → E) : ℝ≥0∞ := ∫⁻ x, ‖u x‖ₑ ^ p ∂μ

theorem s1c2_Ip_eq {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E] (μ : Measure α)
    {p : ℝ} (hp : 0 < p) (u : α → E) (hu : AEStronglyMeasurable u μ) :
    Ip μ p u = eLpNorm u (ENNReal.ofReal p) μ ^ p := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by simpa using hp) ENNReal.ofReal_ne_top hu,
    ENNReal.toReal_ofReal hp.le, ← ENNReal.rpow_mul]
  have : 1 / p * p = 1 := by field_simp
  rw [this, ENNReal.rpow_one]
  rfl

theorem s1c2_Ip_shift {d : ℕ} (p : ℝ) {E : Type*} [NormedAddCommGroup E]
    (u : EuclideanSpace ℝ (Fin d) → E) (a : EuclideanSpace ℝ (Fin d)) :
    Ip volume p (fun x => u (x + a)) = Ip volume p u := by
  unfold Ip
  exact lintegral_add_right_eq_self (fun x => ‖u x‖ₑ ^ p) a

theorem s1c2_eLpNorm_shift {d : ℕ} (q : ℝ≥0∞) {E : Type*} [NormedAddCommGroup E]
    (u : EuclideanSpace ℝ (Fin d) → E) (hu : Continuous u) (a : EuclideanSpace ℝ (Fin d)) :
    eLpNorm (fun x => u (x + a)) q volume = eLpNorm u q volume := by
  have := eLpNorm_comp_measurePreserving (p := q) hu.aestronglyMeasurable
    (measurePreserving_add_right (volume : Measure (EuclideanSpace ℝ (Fin d))) a)
  exact this

theorem s1c2_fd_lp_crude {d : ℕ} {p : ℝ} (hp : 1 ≤ p) {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (L : List (EuclideanSpace ℝ (Fin d))) :
    ∀ u : EuclideanSpace ℝ (Fin d) → E, Continuous u →
      eLpNorm (u8_fd L u) (ENNReal.ofReal p) volume ≤
        2 ^ L.length * eLpNorm u (ENNReal.ofReal p) volume := by
  induction L with
  | nil => intro u _; simp [u8_fd_nil]
  | cons h hs ih =>
    intro u hu
    rw [u8_fd_cons]
    have hc : Continuous (fun x => u (x + h) - u x) :=
      (hu.comp (continuous_id.add continuous_const)).sub hu
    refine (ih _ hc).trans ?_
    have hq : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by simpa using hp
    have h1 : eLpNorm (fun x => u (x + h) - u x) (ENNReal.ofReal p) volume ≤
        2 * eLpNorm u (ENNReal.ofReal p) volume := by
      have h2 := eLpNorm_sub_le (μ := volume) (p := ENNReal.ofReal p)
        (f := fun x => u (x + h)) (g := u) hq
      rw [s1c2_eLpNorm_shift _ u hu] at h2
      calc _ ≤ _ := h2
        _ = 2 * eLpNorm u (ENNReal.ofReal p) volume := by rw [two_mul]
    calc (2 : ℝ≥0∞) ^ hs.length * eLpNorm (fun x => u (x + h) - u x) (ENNReal.ofReal p) volume
        ≤ 2 ^ hs.length * (2 * eLpNorm u (ENNReal.ofReal p) volume) :=
          mul_le_mul_right (by exact h1) _
      _ = 2 ^ (h :: hs).length * eLpNorm u (ENNReal.ofReal p) volume := by
          rw [List.length_cons, pow_succ]; ring

theorem s1c2_fd_Ip_crude {d : ℕ} {p : ℝ} (hp : 1 ≤ p) {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (L : List (EuclideanSpace ℝ (Fin d)))
    (u : EuclideanSpace ℝ (Fin d) → E) (hu : Continuous u) :
    Ip volume p (u8_fd L u) ≤ (2 ^ L.length) ^ p * Ip volume p u := by
  have hp0 : 0 < p := by linarith
  rw [s1c2_Ip_eq _ hp0 _ (s1c2_fd_cont L hu).aestronglyMeasurable,
    s1c2_Ip_eq _ hp0 _ hu.aestronglyMeasurable, ← ENNReal.mul_rpow_of_nonneg _ _ hp0.le]
  exact ENNReal.rpow_le_rpow (s1c2_fd_lp_crude hp L u hu) hp0.le

/-- The `L^p` Taylor bound for iterated differences along a fixed direction:
`‖Δ_y^k u‖_p^p ≤ (‖y‖^k)^p ‖D^k u‖_p^p` for `u ∈ C^k` with values in a real Banach space. -/
theorem s1c2_fd_Ip_taylor {d : ℕ} {p : ℝ} (hp : 1 < p) :
    ∀ (k : ℕ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
      (u : EuclideanSpace ℝ (Fin d) → E), ContDiff ℝ k u → ∀ y : EuclideanSpace ℝ (Fin d),
      Ip volume p (u8_fd (List.replicate k y) u) ≤
        ENNReal.ofReal (‖y‖ ^ k) ^ p * Ip volume p (iteratedFDeriv ℝ k u) := by
  intro k
  induction k with
  | zero =>
    intro E _ _ _ u hu y
    simp only [List.replicate_zero, u8_fd_nil, pow_zero, ENNReal.ofReal_one, ENNReal.one_rpow,
      one_mul]
    refine le_of_eq (lintegral_congr (fun x => ?_))
    rw [← ofReal_norm, ← ofReal_norm, norm_iteratedFDeriv_zero]
  | succ k ih =>
    intro E _ _ _ u hu y
    have hp0 : 0 ≤ p := by linarith
    have hU : ContDiff ℝ k (fderiv ℝ u) := hu.fderiv_right (by exact_mod_cast le_refl (k + 1))
    have hu1 : Differentiable ℝ u := hu.differentiable (by exact_mod_cast Nat.succ_ne_zero k)
    set U := fderiv ℝ u with hUdef
    have hUc : Continuous U := hU.continuous
    have hftc : ∀ x, u (x + y) - u x = ∫ t in Set.Ioc (0 : ℝ) 1, U (x + t • y) y := by
      intro x
      rw [← intervalIntegral.integral_of_le zero_le_one]
      have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun t : ℝ => u (x + t • y))
        (f' := fun t => U (x + t • y) y) (a := 0) (b := 1) (fun t _ => by
          have h1 : HasDerivAt (fun t : ℝ => x + t • y) y t := by
            simpa using ((hasDerivAt_id t).smul_const y).const_add x
          have h2 : HasFDerivAt u (U (x + t • y)) (x + t • y) :=
            (hu1 (x + t • y)).hasFDerivAt
          exact h2.comp_hasDerivAt t h1)
        (((hUc.comp (by fun_prop : Continuous fun t : ℝ => x + t • y)).clm_apply
          continuous_const).intervalIntegrable 0 1)
      simpa using h.symm
    have hfd : u8_fd (List.replicate (k + 1) y) u =
        fun x => ∫ t in Set.Ioc (0 : ℝ) 1, (u8_fd (List.replicate k y) U) (x + t • y) y := by
      rw [List.replicate_succ, u8_fd_cons]
      have : (fun x => u (x + y) - u x) = fun x => ∫ t in Set.Ioc (0 : ℝ) 1, U (x + t • y) y :=
        funext hftc
      rw [this]
      rw [u8_fd_integral (volume.restrict (Set.Ioc (0 : ℝ) 1)) (List.replicate k y)
        (fun t x => U (x + t • y) y) (fun x => ?_)]
      · funext x
        congr 1; funext t
        have e1 : u8_fd (List.replicate k y) (fun x => U (x + t • y) y) =
            fun x => (u8_fd (List.replicate k y) (fun x => U (x + t • y)) x) y := by
          have := s1c2_fd_clm (ContinuousLinearMap.apply ℝ E y) (List.replicate k y)
            (fun x => U (x + t • y))
          simpa using this
        rw [e1, u8_fd_shift (List.replicate k y) U (t • y)]
      · exact ((hUc.comp (by fun_prop : Continuous fun t : ℝ => x + t • y)).clm_apply
          continuous_const).integrableOn_Ioc
    set F := u8_fd (List.replicate k y) U with hF
    have hFc : Continuous F := s1c2_fd_cont _ hUc
    have hpt : ∀ x, ‖u8_fd (List.replicate (k + 1) y) u x‖ₑ ≤
        ∫⁻ t in Set.Ioc (0 : ℝ) 1, ‖y‖ₑ * ‖F (x + t • y)‖ₑ := by
      intro x
      rw [hfd]
      refine (enorm_integral_le_lintegral_enorm _).trans (lintegral_mono (fun t => ?_))
      rw [mul_comm]
      exact ContinuousLinearMap.le_opENorm _ _
    have hmeasG : Measurable (Function.uncurry fun (x : EuclideanSpace ℝ (Fin d)) (t : ℝ) =>
        ‖F (x + t • y)‖ₑ) := by
      have hc : Continuous (fun q : EuclideanSpace ℝ (Fin d) × ℝ => F (q.1 + q.2 • y)) :=
        hFc.comp (by fun_prop)
      exact hc.enorm.measurable
    have hmk := s1c2_mink (volume : Measure (EuclideanSpace ℝ (Fin d)))
      (volume.restrict (Set.Ioc (0 : ℝ) 1)) hp (fun _ => ‖y‖ₑ) (fun _ => 1) (fun _ => 1)
      measurable_const measurable_const measurable_const
      (Filter.Eventually.of_forall (fun _ => by simp))
      (fun x t => ‖F (x + t • y)‖ₑ) hmeasG
    have hshift : ∀ t : ℝ, ∫⁻ x, ‖F (x + t • y)‖ₑ ^ p = Ip volume p F := fun t =>
      s1c2_Ip_shift p F (t • y)
    simp only [hshift, mul_one, ENNReal.one_rpow, lintegral_const,
      Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, Real.volume_Ioc] at hmk
    have hvol : (ENNReal.ofReal (1 - 0)) = 1 := by simp
    rw [hvol] at hmk
    simp only [mul_one] at hmk
    have hy : ‖y‖ₑ ^ p = ‖y‖ₑ ^ (p - 1) * ‖y‖ₑ := by
      conv_lhs => rw [show p = (p - 1) + 1 by ring]
      rw [ENNReal.rpow_add_of_nonneg _ _ (by linarith) zero_le_one, ENNReal.rpow_one]
    have hIter : Ip volume p (iteratedFDeriv ℝ k U) = Ip volume p (iteratedFDeriv ℝ (k + 1) u) := by
      unfold Ip
      refine lintegral_congr (fun x => ?_)
      rw [← ofReal_norm, ← ofReal_norm, norm_iteratedFDeriv_fderiv]
    calc Ip volume p (u8_fd (List.replicate (k + 1) y) u) ≤ _ :=
          (lintegral_mono (fun x => ENNReal.rpow_le_rpow (hpt x) hp0)).trans hmk
      _ = ‖y‖ₑ ^ p * Ip volume p F := by rw [hy, mul_assoc]
      _ ≤ ‖y‖ₑ ^ p * (ENNReal.ofReal (‖y‖ ^ k) ^ p * Ip volume p (iteratedFDeriv ℝ k U)) :=
          mul_le_mul_right (ih (EuclideanSpace ℝ (Fin d) →L[ℝ] E) U hU y) _
      _ = _ := by
          rw [hIter, ← mul_assoc, pow_succ', ENNReal.ofReal_mul (norm_nonneg y),
            ENNReal.mul_rpow_of_nonneg _ _ hp0, ofReal_norm]

theorem s1c2_uL_split {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] (ℓ : ℕ) (y : V) :
    u8_L ℓ y = List.replicate ℓ y ++ List.replicate ℓ (-y) := by
  simp [u8_L, List.map_append, List.map_replicate]

/-- Far bound: `‖Δ^{2ℓ}_y u‖_p^p ≤ (2^{2ℓ})^p ‖u‖_p^p`. -/
theorem s1c2_uL_Ip_far {d : ℕ} {p : ℝ} (hp : 1 < p) {E : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (ℓ : ℕ) (u : EuclideanSpace ℝ (Fin d) → E) (hu : Continuous u)
    (y : EuclideanSpace ℝ (Fin d)) :
    Ip volume p (u8_fd (u8_L ℓ y) u) ≤ ((2 : ℝ≥0∞) ^ (2 * ℓ)) ^ p * Ip volume p u := by
  have := s1c2_fd_Ip_crude hp.le (u8_L ℓ y) u hu
  rwa [u8_L_length] at this

/-- Near bound: `‖Δ^{2ℓ}_y u‖_p^p ≤ (2^ℓ ‖y‖^ℓ)^p ‖D^ℓ u‖_p^p` for `u ∈ C^ℓ`. -/
theorem s1c2_uL_Ip_near {d : ℕ} {p : ℝ} (hp : 1 < p) {E : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (ℓ : ℕ) (u : EuclideanSpace ℝ (Fin d) → E)
    (hu : ContDiff ℝ ℓ u) (y : EuclideanSpace ℝ (Fin d)) :
    Ip volume p (u8_fd (u8_L ℓ y) u) ≤
      ((2 : ℝ≥0∞) ^ ℓ * ENNReal.ofReal (‖y‖ ^ ℓ)) ^ p * Ip volume p (iteratedFDeriv ℝ ℓ u) := by
  have hp0 : 0 ≤ p := by linarith
  rw [s1c2_uL_split, s1c2_fd_append]
  have hc : Continuous (u8_fd (List.replicate ℓ y) u) := s1c2_fd_cont _ hu.continuous
  have h1 := s1c2_fd_Ip_crude hp.le (List.replicate ℓ (-y)) _ hc
  rw [List.length_replicate] at h1
  refine h1.trans ?_
  rw [ENNReal.mul_rpow_of_nonneg _ _ hp0, mul_assoc]
  exact mul_le_mul_right (s1c2_fd_Ip_taylor hp ℓ E u hu y) _

end HRS.S1C2
