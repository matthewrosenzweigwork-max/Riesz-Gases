import HRS.MS.WlInsAux2
import HRS.MS.WrRefMargAux3
import HRS.MS.ThmLogAux2

/-!
# HRS.MS.WlMargAux1 -- `K` on `L²(μ)`: Minkowski bound for `Kη`, positivity on mean-zero functions (WL-8, part 1)

Packet WL-8 of `docs/WR_LOG_PLAN.md` (Step 10 of the proof of `r2_log_static`).  Infrastructure lemmas, not
manuscript rows.  Namespace `HRS.MS.Wl`, helper prefix `wl8_`.  Notation: `μ = HRS.Whole.withDensityReal ρ`,
`K = sphericalLogKernel`, `ℓ = logWeight`.

* `wl8_minkowski_lintegral`: Schur/Minkowski in `ℝ≥0∞` form: for a symmetric measurable kernel `h` with
  `∫⁻ h(x,y)² dμ(y) ≤ C` and `G ≥ 0`, `∫⁻ (∫⁻ h(x,y) G(y) dμ(y))² dμ(x) ≤ C (∫⁻ G dμ)²`
  (weighted Cauchy-Schwarz, then Tonelli and the symmetry of `h`).
* `wl8_conv_L2` (**TeX `eq:r2-log-TV-convolution`, form `w ∈ L¹(μ)`**): for `d ≥ 2`, `A` there is `C ≥ 0`
  (before `ρ`) with `‖K w‖_{L²(μ)} ≤ C ‖w‖_{L¹(μ)}`, `(K w)(x) = ∫ K(x,y) w(y) dμ(y)`, for every measurable
  `w ∈ L¹(μ)` (`wl_row_pow 2`; no junk value: all integrals are of integrable functions).
* `wl8_cv_L2` (**TeX `eq:r2-log-TV-convolution` for measures**): for probability measures `P, Q ≤ Cb μ` with
  `tvDist P Q ≤ ε`, `x ↦ ∫ K(x,y) dP(y) - ∫ K(x,y) dQ(y)` is measurable with `L²(μ)` norm `≤ 2 C ε`
  (densities by Radon-Nikodym, `RefMarg.integral_abs_sub_le`).
* `wl8_K_psd` (**`K` is positive on `L²_0(μ)`, bounded functions**): `0 ≤ ∫ (Kz) z dμ` for measurable bounded
  `z` with `∫ z dμ = 0` (`t67_k2` for `K̃ = K + (1/2) log 2`, which differs from `K` by a constant, harmless on
  mean-zero functions; absolute integrability from `wl_schur` and the density `ρ ⊗ ρ`).

Adjustments with respect to the plan (documented, harmless): positivity is stated for bounded measurable mean-zero
`z` (this is all that the absorption step needs, since `-1 < z_N ≤ C - 1`); the Minkowski bound is stated for
`L¹(μ)` densities `w` (the signed measure `η = w μ`), and `wl8_cv_L2` for two probability measures dominated by
`Cb μ` in terms of `tvDist` (the constant does not depend on `Cb`).
-/

set_option linter.unusedSectionVars false

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

noncomputable section

namespace HRS.MS.Wl

open HRS.Whole HRS.External HRS.MS.Wr

/-! ### Generic Schur/Minkowski bound -/

section Generic

variable {E : Type*} [MeasurableSpace E] {μ : Measure E} [SFinite μ]

/-- **Schur/Minkowski in `ℝ≥0∞` form.** -/
theorem wl8_minkowski_lintegral {h : E → E → ℝ≥0∞} (hm : Measurable (fun p : E × E => h p.1 p.2))
    (hsymm : ∀ x y, h x y = h y x) {C : ℝ≥0∞} (hrow : ∀ x, ∫⁻ y, h x y ^ 2 ∂μ ≤ C)
    {G : E → ℝ≥0∞} (hG : Measurable G) :
    ∫⁻ x, (∫⁻ y, h x y * G y ∂μ) ^ 2 ∂μ ≤ C * (∫⁻ y, G y ∂μ) ^ 2 := by
  have hx : ∀ x, Measurable (h x) := fun x => Measurable.of_uncurry_left hm
  have hpt : ∀ x, (∫⁻ y, h x y * G y ∂μ) ^ 2 ≤ (∫⁻ y, G y ∂μ) * ∫⁻ y, G y * h x y ^ 2 ∂μ := by
    intro x
    have := HRS.PoleCavityAux.weighted_cs μ G (h x) hG (hx x)
    calc (∫⁻ y, h x y * G y ∂μ) ^ 2 = (∫⁻ y, G y * h x y ∂μ) ^ 2 := by
          congr 1; exact lintegral_congr fun y => mul_comm _ _
      _ ≤ _ := this
  have hjoint : Measurable (fun p : E × E => G p.2 * h p.1 p.2 ^ 2) :=
    (hG.comp measurable_snd).mul (hm.pow_const 2)
  calc ∫⁻ x, (∫⁻ y, h x y * G y ∂μ) ^ 2 ∂μ
      ≤ ∫⁻ x, (∫⁻ y, G y ∂μ) * ∫⁻ y, G y * h x y ^ 2 ∂μ ∂μ := lintegral_mono hpt
    _ = (∫⁻ y, G y ∂μ) * ∫⁻ x, ∫⁻ y, G y * h x y ^ 2 ∂μ ∂μ := by
        rw [lintegral_const_mul]
        exact Measurable.lintegral_prod_right' (f := fun p : E × E => G p.2 * h p.1 p.2 ^ 2) hjoint
    _ = (∫⁻ y, G y ∂μ) * ∫⁻ y, ∫⁻ x, G y * h x y ^ 2 ∂μ ∂μ := by
        congr 1
        exact lintegral_lintegral_swap hjoint.aemeasurable
    _ ≤ (∫⁻ y, G y ∂μ) * ∫⁻ y, G y * C ∂μ := by
        refine mul_le_mul' le_rfl (lintegral_mono fun y => ?_)
        have hm' : Measurable (fun x : E => h x y ^ 2) :=
          (Measurable.of_uncurry_right (f := h) hm (y := y)).pow_const 2
        rw [lintegral_const_mul _ hm']
        refine mul_le_mul' le_rfl ?_
        calc ∫⁻ x, h x y ^ 2 ∂μ = ∫⁻ x, h y x ^ 2 ∂μ := lintegral_congr fun x => by rw [hsymm x y]
          _ ≤ C := hrow y
    _ = C * (∫⁻ y, G y ∂μ) ^ 2 := by
        rw [lintegral_mul_const _ hG]
        ring

/-- From a `lintegral` bound on `‖f‖ₑ²` to the `L²` seminorm. -/
lemma wl8_eLpNorm_two_le {f : E → ℝ} (hf : AEStronglyMeasurable f μ) {s : ℝ} (h : ∫⁻ x, ‖f x‖ₑ ^ 2 ∂μ ≤ ENNReal.ofReal s ^ 2) :
    eLpNorm f 2 μ ≤ ENNReal.ofReal s := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top hf]
  simp only [ENNReal.toReal_ofNat]
  have h1 : ∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) ∂μ ≤ ENNReal.ofReal s ^ (2 : ℝ) := by
    simpa [ENNReal.rpow_two] using h
  calc (∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) ≤ (ENNReal.ofReal s ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) :=
        ENNReal.rpow_le_rpow h1 (by norm_num)
    _ = ENNReal.ofReal s := by
        rw [← ENNReal.rpow_mul]
        norm_num

end Generic

/-! ### The Minkowski bound for `K w` -/

section Conv

variable {d : ℕ}

/-- **`wl8_conv_L2`**: `‖K w‖_{L²(μ)} ≤ C ‖w‖_{L¹(μ)}` for every measurable `w ∈ L¹(μ)`, `C` depending on
`d, A` only. -/
theorem wl8_conv_L2 (hd : 2 ≤ d) (A : ℝ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ ρ : Euc d → ℝ,
    HRS.Whole.IsProbDensity ρ → HasSphericalBound A ρ → ∀ w : Euc d → ℝ, Measurable w →
      Integrable w (HRS.Whole.withDensityReal ρ) →
      Measurable (fun x => ∫ y, sphericalLogKernel x y * w y ∂(HRS.Whole.withDensityReal ρ)) ∧
      eLpNorm (fun x => ∫ y, sphericalLogKernel x y * w y ∂(HRS.Whole.withDensityReal ρ)) 2 (HRS.Whole.withDensityReal ρ) ≤
        ENNReal.ofReal (C * ∫ y, |w y| ∂(HRS.Whole.withDensityReal ρ)) := by
  obtain ⟨C2, hC20, hC2⟩ := wl_row_pow hd A 2
  refine ⟨Real.sqrt C2, Real.sqrt_nonneg _, fun ρ hρ hA w hwm hwi => ?_⟩
  have := wl_isProb hρ
  set μ := HRS.Whole.withDensityReal ρ with hμ
  have hKm : Measurable (fun p : Euc d × Euc d => sphericalLogKernel p.1 p.2) := wl_K_measurable
  have hFm : Measurable fun x : Euc d => ∫ y, sphericalLogKernel x y * w y ∂μ :=
    RefMarg.measurable_integral_kernel
      (F := fun p : Euc d × Euc d => sphericalLogKernel p.1 p.2 * w p.2) (hKm.mul (hwm.comp measurable_snd))
  refine ⟨hFm, ?_⟩
  set m : ℝ := ∫ y, |w y| ∂μ with hm
  have hm0 : 0 ≤ m := integral_nonneg fun _ => abs_nonneg _
  set G : Euc d → ℝ≥0∞ := fun y => ENNReal.ofReal |w y| with hGdef
  have hG : Measurable G := hwm.abs.ennreal_ofReal
  have hGint : ∫⁻ y, G y ∂μ = ENNReal.ofReal m :=
    (ofReal_integral_eq_lintegral_ofReal hwi.abs (Filter.Eventually.of_forall fun _ => abs_nonneg _)).symm
  set h : Euc d → Euc d → ℝ≥0∞ := fun x y => ENNReal.ofReal (sphericalLogKernel x y) with hh
  have hhm : Measurable (fun p : Euc d × Euc d => h p.1 p.2) := hKm.ennreal_ofReal
  have hrow : ∀ x, ∫⁻ y, h x y ^ 2 ∂μ ≤ ENNReal.ofReal C2 := by
    intro x
    obtain ⟨hi, hle⟩ := hC2 ρ hρ hA x
    calc ∫⁻ y, h x y ^ 2 ∂μ = ∫⁻ y, ENNReal.ofReal (sphericalLogKernel x y ^ 2) ∂μ :=
          lintegral_congr fun y => by
            simp only [hh]; rw [ENNReal.ofReal_pow (HRS.MS.Comm.comm_log_nonneg x y)]
      _ = ENNReal.ofReal (∫ y, sphericalLogKernel x y ^ 2 ∂μ) :=
          (ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall fun _ => sq_nonneg _)).symm
      _ ≤ _ := ENNReal.ofReal_le_ofReal hle
  have hmk := wl8_minkowski_lintegral (μ := μ) hhm (fun x y => by simp only [hh]; rw [wl_K_symm]) hrow hG
  have hpt : ∀ x, ‖∫ y, sphericalLogKernel x y * w y ∂μ‖ₑ ≤ ∫⁻ y, h x y * G y ∂μ := by
    intro x
    refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq (lintegral_congr fun y => ?_))
    simp only [hh, hGdef]
    rw [Real.enorm_eq_ofReal_abs, abs_mul, abs_of_nonneg (HRS.MS.Comm.comm_log_nonneg x y),
      ENNReal.ofReal_mul (HRS.MS.Comm.comm_log_nonneg x y)]
  have hs0 : 0 ≤ Real.sqrt C2 * m := mul_nonneg (Real.sqrt_nonneg _) hm0
  refine wl8_eLpNorm_two_le hFm.aestronglyMeasurable ?_
  calc ∫⁻ x, ‖∫ y, sphericalLogKernel x y * w y ∂μ‖ₑ ^ 2 ∂μ ≤ ∫⁻ x, (∫⁻ y, h x y * G y ∂μ) ^ 2 ∂μ :=
        lintegral_mono fun x => pow_le_pow_left' (hpt x) 2
    _ ≤ ENNReal.ofReal C2 * (∫⁻ y, G y ∂μ) ^ 2 := hmk
    _ = ENNReal.ofReal (Real.sqrt C2 * m) ^ 2 := by
        rw [hGint, ← ENNReal.ofReal_pow hm0, ← ENNReal.ofReal_pow hs0, ← ENNReal.ofReal_mul hC20,
          mul_pow, Real.sq_sqrt hC20]

end Conv

/-! ### The Minkowski bound for `K(P - Q)` -/

section CV

variable {d : ℕ}

lemma wl8_K_row_integrable (hd : 2 ≤ d) (A : ℝ) : ∃ C1 : ℝ, 0 ≤ C1 ∧ ∀ ρ : Euc d → ℝ,
    HRS.Whole.IsProbDensity ρ → HasSphericalBound A ρ → ∀ x : Euc d,
      Integrable (fun y => sphericalLogKernel x y) (HRS.Whole.withDensityReal ρ) ∧
        ∫ y, sphericalLogKernel x y ∂(HRS.Whole.withDensityReal ρ) ≤ C1 := by
  obtain ⟨C1, hC10, hC1⟩ := wl_row_pow hd A 1
  refine ⟨C1, hC10, fun ρ hρ hA x => ?_⟩
  obtain ⟨hi, hle⟩ := hC1 ρ hρ hA x
  simp only [pow_one] at hi hle
  exact ⟨hi, hle⟩

/-- A finite measure dominated by `Cb μ`: density `p = dP/dμ`, `P = μ.withDensity p`, and `K(x,·)` is `P`-integrable
with `∫ K(x,·) dP = ∫ K(x,y) p(y) dμ(y)` (with integrability). -/
lemma wl8_density_of_le {μ : Measure (Euc d)} [IsFiniteMeasure μ] {Cb : ℝ} {P : Measure (Euc d)}
    [IsFiniteMeasure P] (hP : P ≤ ENNReal.ofReal Cb • μ) :
    Measurable (fun y => (P.rnDeriv μ y).toReal) ∧ (∀ y, 0 ≤ (P.rnDeriv μ y).toReal) ∧
      Integrable (fun y => (P.rnDeriv μ y).toReal) μ ∧
      P = μ.withDensity (fun y => ENNReal.ofReal ((P.rnDeriv μ y).toReal)) ∧
      ∀ {g : Euc d → ℝ}, Integrable g μ → Integrable (fun y => (P.rnDeriv μ y).toReal * g y) μ ∧
        ∫ y, g y ∂P = ∫ y, (P.rnDeriv μ y).toReal * g y ∂μ := by
  have hPac : P ≪ μ := Measure.absolutelyContinuous_of_le_smul hP
  have : P.HaveLebesgueDecomposition μ := Measure.haveLebesgueDecomposition_of_sigmaFinite _ _
  have hm : Measurable (fun y => (P.rnDeriv μ y).toReal) := (Measure.measurable_rnDeriv P μ).ennreal_toReal
  have hfin : ∀ᵐ y ∂μ, P.rnDeriv μ y < ∞ := Measure.rnDeriv_lt_top P μ
  have hPeq : P = μ.withDensity (P.rnDeriv μ) := (Measure.withDensity_rnDeriv_eq P μ hPac).symm
  have hPeq' : P = μ.withDensity (fun y => ENNReal.ofReal ((P.rnDeriv μ y).toReal)) := by
    refine hPeq.trans (withDensity_congr_ae ?_)
    filter_upwards [hfin] with y hy
    rw [ENNReal.ofReal_toReal hy.ne]
  refine ⟨hm, fun y => ENNReal.toReal_nonneg, Measure.integrable_toReal_rnDeriv, hPeq', fun {g} hg => ?_⟩
  have hint : Integrable g P := by
    refine (hg.smul_measure (c := ENNReal.ofReal Cb) ENNReal.ofReal_ne_top).mono_measure hP
  have h1 : Integrable (fun y => (P.rnDeriv μ y).toReal • g y) μ := by
    have := (integrable_withDensity_iff_integrable_smul' (Measure.measurable_rnDeriv P μ) hfin).1
      (hPeq ▸ hint)
    exact this
  refine ⟨by simpa using h1, ?_⟩
  conv_lhs => rw [hPeq]
  rw [integral_withDensity_eq_integral_toReal_smul (Measure.measurable_rnDeriv P μ) hfin]
  rfl

/-- **`wl8_cv_L2`** (TeX `eq:r2-log-TV-convolution` for measures): for probability measures `P, Q ≤ Cb μ` with
`tvDist P Q ≤ ε`, the function `x ↦ ∫ K(x,y) dP(y) - ∫ K(x,y) dQ(y)` is measurable with `L²(μ)` norm `≤ C (2 ε)`,
`C` depending on `d, A` only (not on `Cb`). -/
theorem wl8_cv_L2 (hd : 2 ≤ d) (A : ℝ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ ρ : Euc d → ℝ,
    HRS.Whole.IsProbDensity ρ → HasSphericalBound A ρ → ∀ Cb : ℝ, 0 ≤ Cb →
      ∀ P Q : Measure (Euc d), IsProbabilityMeasure P → IsProbabilityMeasure Q →
        P ≤ ENNReal.ofReal Cb • HRS.Whole.withDensityReal ρ →
        Q ≤ ENNReal.ofReal Cb • HRS.Whole.withDensityReal ρ → ∀ ε : ℝ, tvDist P Q ≤ ε →
          Measurable (fun x => ∫ y, sphericalLogKernel x y ∂P - ∫ y, sphericalLogKernel x y ∂Q) ∧
          eLpNorm (fun x => ∫ y, sphericalLogKernel x y ∂P - ∫ y, sphericalLogKernel x y ∂Q) 2
            (HRS.Whole.withDensityReal ρ) ≤ ENNReal.ofReal (C * (2 * ε)) := by
  obtain ⟨C, hC0, hC⟩ := wl8_conv_L2 hd A
  obtain ⟨C1, hC10, hC1⟩ := wl8_K_row_integrable hd A
  refine ⟨C, hC0, fun ρ hρ hA Cb hCb P Q hP hQ hPle hQle ε hε => ?_⟩
  have := wl_isProb hρ
  set μ := HRS.Whole.withDensityReal ρ with hμ
  obtain ⟨hpm, hp0, hpi, hPeq, hPint⟩ := wl8_density_of_le hPle
  obtain ⟨hqm, hq0, hqi, hQeq, hQint⟩ := wl8_density_of_le hQle
  set p : Euc d → ℝ := fun y => (P.rnDeriv μ y).toReal with hp
  set q : Euc d → ℝ := fun y => (Q.rnDeriv μ y).toReal with hq
  set w : Euc d → ℝ := fun y => p y - q y with hw
  have hwm : Measurable w := hpm.sub hqm
  have hwi : Integrable w μ := hpi.sub hqi
  have hid : ∀ x, ∫ y, sphericalLogKernel x y ∂P - ∫ y, sphericalLogKernel x y ∂Q =
      ∫ y, sphericalLogKernel x y * w y ∂μ := by
    intro x
    have hKi := (hC1 ρ hρ hA x).1
    obtain ⟨h1, e1⟩ := hPint hKi
    obtain ⟨h2, e2⟩ := hQint hKi
    rw [e1, e2, ← integral_sub h1 h2]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [hw, hp, hq]
    ring
  have hfun : (fun x => ∫ y, sphericalLogKernel x y ∂P - ∫ y, sphericalLogKernel x y ∂Q) =
      fun x => ∫ y, sphericalLogKernel x y * w y ∂μ := funext hid
  obtain ⟨hmeas, hnorm⟩ := hC ρ hρ hA w hwm hwi
  rw [hfun]
  refine ⟨hmeas, hnorm.trans (ENNReal.ofReal_le_ofReal ?_)⟩
  -- the total variation bound
  have hbdd : BddAbove (Set.range fun E : {E : Set (Euc d) // MeasurableSet E} =>
      |(P E.1).toReal - (Q E.1).toReal|) := by
    refine ⟨1, ?_⟩
    rintro _ ⟨E, rfl⟩
    have h1 : (P E.1).toReal ≤ 1 := by
      have := prob_le_one (μ := P) (s := E.1)
      exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using this)
    have h2 : (Q E.1).toReal ≤ 1 := by
      have := prob_le_one (μ := Q) (s := E.1)
      exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using this)
    rw [abs_le]
    constructor <;> linarith [ENNReal.toReal_nonneg (a := P E.1), ENNReal.toReal_nonneg (a := Q E.1)]
  have hset : ∀ A' : Set (Euc d), MeasurableSet A' → |P.real A' - Q.real A'| ≤ ε := by
    intro A' hA'
    refine le_trans ?_ hε
    unfold tvDist
    exact le_ciSup hbdd (⟨A', hA'⟩ : {E : Set (Euc d) // MeasurableSet E})
  have hε0 : 0 ≤ ε := le_trans (Real.iSup_nonneg fun _ => abs_nonneg _) hε
  have hint : ∫ y, |p y - q y| ∂μ ≤ 2 * ε := by
    refine RefMarg.integral_abs_sub_le hpm hqm hp0 hq0 hpi hqi (fun A' hA' => ?_)
    rw [← hPeq, ← hQeq]
    exact hset A' hA'
  have : ∫ y, |w y| ∂μ ≤ 2 * ε := hint
  exact mul_le_mul_of_nonneg_left this hC0

end CV

/-! ### Positivity of `K` on mean-zero functions -/

section Psd

variable {d : ℕ}

lemma wl8_t67K_eq (x y : Euc d) : HRS.MS.Thm.t67K d x y = sphericalLogKernel x y + (1 / 2) * Real.log 2 := by
  unfold HRS.MS.Thm.t67K sphericalLogKernel logWeight HRS.MS.Thm.t67l
  rw [HRS.MS.Thm.t67_g]

/-- `L¹(μ)` versus `L¹(dx)` for `μ = ρ dx`. -/
lemma wl8_integrable_nu {ρ : Euc d → ℝ} (hρ : HRS.Whole.IsProbDensity ρ) {g : Euc d → ℝ} :
    Integrable g (HRS.Whole.withDensityReal ρ) ↔ Integrable (fun y => ρ y * g y) := by
  have hfm : Measurable (fun x => ENNReal.ofReal (ρ x)) := ENNReal.measurable_ofReal.comp hρ.measurable
  unfold HRS.Whole.withDensityReal
  rw [integrable_withDensity_iff_integrable_smul' hfm
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  refine integrable_congr (Filter.Eventually.of_forall fun y => ?_)
  simp [ENNReal.toReal_ofReal (hρ.nonneg y)]

/-- **`K` is positive on bounded mean-zero functions** (`L²_0(μ)`): `0 ≤ ∫ (K z) z dμ`.  Proof: `t67_k2` for
`K̃ = K + (1/2) log 2` against `f = ρ z`, `∫ f = 0`; absolute integrability of `K̃ f ⊗ f` from `wl_schur`
(`K ∈ L¹(μ ⊗ μ)`) and `ρ ⊗ ρ ∈ L¹`. -/
theorem wl8_K_psd (hd : 2 ≤ d) (A : ℝ) {ρ : Euc d → ℝ} (hρ : HRS.Whole.IsProbDensity ρ)
    (hA : HasSphericalBound A ρ) {z : Euc d → ℝ} (hzm : Measurable z) {b : ℝ} (hb : ∀ x, |z x| ≤ b)
    (hz0 : ∫ x, z x ∂(HRS.Whole.withDensityReal ρ) = 0) :
    0 ≤ ∫ x, (∫ y, sphericalLogKernel x y * z y ∂(HRS.Whole.withDensityReal ρ)) * z x
      ∂(HRS.Whole.withDensityReal ρ) := by
  obtain ⟨C1, hC10, hC1⟩ := wl8_K_row_integrable hd A
  obtain ⟨Cs, hCs0, hCs⟩ := wl_schur hd A
  have := wl_isProb hρ
  set μ := HRS.Whole.withDensityReal ρ with hμ
  have hb0 : 0 ≤ b := le_trans (abs_nonneg _) (hb 0)
  set c : ℝ := (1 / 2) * Real.log 2 with hc
  have hc0 : 0 ≤ c := by
    have : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    positivity
  have hρi : Integrable ρ := HRS.Whole.Q34.integrable_of_isProbDensity hρ
  set f : Euc d → ℝ := fun x => ρ x * z x with hf
  have hfm : Measurable f := hρ.measurable.mul hzm
  have hfbd : ∀ x, |f x| ≤ b * ρ x := fun x => by
    simp only [hf]
    rw [abs_mul, abs_of_nonneg (hρ.nonneg x)]
    nlinarith [hb x, hρ.nonneg x]
  have hfi : Integrable f := by
    refine Integrable.mono' (hρi.const_mul b) hfm.aestronglyMeasurable (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs]; exact hfbd x
  have hmass : ∫ x, f x = 0 := by
    rw [← wr13e_integral_nu hρ z]; exact hz0
  -- `K ∈ L¹(μ ⊗ μ)` and the weighted version on `dx ⊗ dx`
  have hKμμ : Integrable (fun p : Euc d × Euc d => sphericalLogKernel p.1 p.2) (μ.prod μ) := by
    have := (hCs ρ hρ hA 1 (fun x y => sphericalLogKernel x y) wl_K_measurable (fun x y _ => by
      rw [abs_of_nonneg (HRS.MS.Comm.comm_log_nonneg x y)]; linarith [HRS.MS.Comm.comm_log_nonneg x y])).2.2
    exact this
  have hρρ : Integrable (fun p : Euc d × Euc d => ρ p.1 * ρ p.2) (volume.prod volume) := hρi.mul_prod hρi
  have hKρρ : Integrable (fun p : Euc d × Euc d => ρ p.1 * ρ p.2 * sphericalLogKernel p.1 p.2)
      (volume.prod volume) := by
    have hfm1 : Measurable (fun x : Euc d => ENNReal.ofReal (ρ x)) := ENNReal.measurable_ofReal.comp hρ.measurable
    have hprod : μ.prod μ = (volume.prod volume).withDensity
        (fun p : Euc d × Euc d => ENNReal.ofReal (ρ p.1) * ENNReal.ofReal (ρ p.2)) := by
      rw [hμ]
      unfold HRS.Whole.withDensityReal
      exact prod_withDensity hfm1 hfm1
    have hfp : Measurable (fun p : Euc d × Euc d => ENNReal.ofReal (ρ p.1) * ENNReal.ofReal (ρ p.2)) :=
      (hfm1.comp measurable_fst).mul (hfm1.comp measurable_snd)
    rw [hprod, integrable_withDensity_iff_integrable_smul' hfp
      (Filter.Eventually.of_forall fun _ => ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top)] at hKμμ
    refine hKμμ.congr (Filter.Eventually.of_forall fun p => ?_)
    simp [ENNReal.toReal_mul, ENNReal.toReal_ofReal (hρ.nonneg p.1), ENNReal.toReal_ofReal (hρ.nonneg p.2)]
  have habs : Integrable (fun p : Euc d × Euc d => |HRS.MS.Thm.t67K d p.1 p.2 * f p.1 * f p.2|)
      (volume.prod volume) := by
    have hMj : Integrable (fun p : Euc d × Euc d => b ^ 2 * (ρ p.1 * ρ p.2 * sphericalLogKernel p.1 p.2 +
        c * (ρ p.1 * ρ p.2))) (volume.prod volume) :=
      (hKρρ.add (hρρ.const_mul c)).const_mul _
    have hmeas : Measurable (fun p : Euc d × Euc d => HRS.MS.Thm.t67K d p.1 p.2 * f p.1 * f p.2) :=
      (HRS.MS.Thm.t67K_measurable.mul (hfm.comp measurable_fst)).mul (hfm.comp measurable_snd)
    refine Integrable.mono' hMj hmeas.abs.aestronglyMeasurable (Filter.Eventually.of_forall fun p => ?_)
    rw [Real.norm_eq_abs, abs_abs, abs_mul, abs_mul, abs_of_nonneg (HRS.MS.Thm.t67K_nonneg p.1 p.2)]
    have h1 := hfbd p.1
    have h2 := hfbd p.2
    have hK0 := HRS.MS.Comm.comm_log_nonneg p.1 p.2
    have hr1 := hρ.nonneg p.1
    have hr2 := hρ.nonneg p.2
    rw [wl8_t67K_eq]
    have h12 : |f p.1| * |f p.2| ≤ b ^ 2 * (ρ p.1 * ρ p.2) := by
      calc |f p.1| * |f p.2| ≤ (b * ρ p.1) * (b * ρ p.2) :=
            mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
        _ = b ^ 2 * (ρ p.1 * ρ p.2) := by ring
    have hKc : 0 ≤ sphericalLogKernel p.1 p.2 + (1 / 2) * Real.log 2 := by
      have : 0 ≤ (1 / 2) * Real.log 2 := hc0
      linarith
    calc (sphericalLogKernel p.1 p.2 + (1 / 2) * Real.log 2) * |f p.1| * |f p.2|
        = (sphericalLogKernel p.1 p.2 + c) * (|f p.1| * |f p.2|) := by rw [hc]; ring
      _ ≤ (sphericalLogKernel p.1 p.2 + c) * (b ^ 2 * (ρ p.1 * ρ p.2)) :=
          mul_le_mul_of_nonneg_left h12 (by linarith)
      _ = _ := by ring
  have hk2 := HRS.MS.Thm.t67_k2 (by omega) hfi habs hmass
  -- identify `pairE`
  have hrow : ∀ x, Integrable (fun y => sphericalLogKernel x y * z y) μ := by
    intro x
    have hKi := (hC1 ρ hρ hA x).1
    refine Integrable.mono' (hKi.mul_const b) ((wl_K_measurable.comp (measurable_const.prodMk measurable_id)).mul hzm).aestronglyMeasurable
      (Filter.Eventually.of_forall fun y => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (HRS.MS.Comm.comm_log_nonneg x y)]
    exact mul_le_mul_of_nonneg_left (hb y) (HRS.MS.Comm.comm_log_nonneg x y)
  have hrowf : ∀ x, Integrable (fun y => sphericalLogKernel x y * f x * f y) := by
    intro x
    have h1 := (wl8_integrable_nu hρ).1 (hrow x)
    refine (h1.const_mul (f x)).congr (Filter.Eventually.of_forall fun y => ?_)
    simp only [hf]; ring
  have hinner : ∀ x, ∫ y, HRS.MS.Thm.t67K d x y * f x * f y =
      f x * ∫ y, sphericalLogKernel x y * z y ∂μ := by
    intro x
    have e1 : ∀ y, HRS.MS.Thm.t67K d x y * f x * f y =
        sphericalLogKernel x y * f x * f y + (c * f x) * f y := fun y => by
      rw [wl8_t67K_eq, hc]; ring
    simp_rw [e1]
    rw [integral_add (hrowf x) (hfi.const_mul (c * f x)), integral_const_mul, hmass, mul_zero, add_zero]
    have e2 : ∫ y, sphericalLogKernel x y * z y ∂μ = ∫ y, ρ y * (sphericalLogKernel x y * z y) :=
      wr13e_integral_nu hρ _
    rw [e2, ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [hf]; ring
  have hpair : HRS.MS.Thm.pairE (HRS.MS.Thm.t67K d) f f =
      ∫ x, (∫ y, sphericalLogKernel x y * z y ∂μ) * z x ∂μ := by
    unfold HRS.MS.Thm.pairE
    simp_rw [hinner]
    rw [wr13e_integral_nu hρ]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [hf]; ring
  rw [← hpair]
  exact hk2

end Psd

end HRS.MS.Wl
