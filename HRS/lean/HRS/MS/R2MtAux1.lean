import HRS.Whole.Round2
import HRS.MS.WrPress
import HRS.MS.WrEnt
import HRS.MS.WrQuadAux3

/-!
# HRS.MS.R2MtAux1 -- Step A of `round2_moment_transfer` (S9.2): density and moments of `Q_{N,b}`

Packet S92 (`docs/NEXT_WAVE_PLAN.md`, Brief 1), namespace `HRS.MS.R2Mt`, helper prefix `s92_`.

Infrastructure statements (not manuscript rows), all for `d ≥ 2`, `0 ≤ s < d/2` (so `N δ_N = 1`), `μ = ρ dx` with
`IsRound2Density d s M L ρ`, `Q = Q_{N,b}(μ) = HRS.Whole.modulatedGibbs (rieszKernel d s) N b μ`:

* `s92_normalizer_bounds`: uniform two-sided pressure bound `e^{-C} ≤ K_{N,b} ≤ e^{C}` for `b ∈ [b₋, b₊]`,
  `N ≥ 2` (the pressure bound of `euclidean_pressure_proof` at `θ = 0`, `h = 0`), with `GibbsWellDefined`.
* `s92_Q_eq_withDensity`: `Q = μ^{⊗N}.withDensity ψ_b` with `ψ_b = K_b⁻¹ e^{-bNF^g}`.
* `s92_psi_sq_le`: `∫ ψ_b² dμ^{⊗N} = K_{2b}/K_b² ≤ e^{3C}` (so `dQ/dμ^N ∈ L²(μ^N)` uniformly in `N`).
* `s92_moment_Q`: for every kernel of the class `IsBoundedPairKernel s B` and every `n : ℕ`,
  `∫ |N F^h|^n dQ ≤ C_n` uniformly in `N ≥ 2` and `ρ` (consequence of `euclidean_pair_entropy_proof`).
* generic measure-theoretic lemmas: Hölder transfer along a density (`s92_eLpNorm_withDensity_le`) and the
  splitting of an `L^m` moment into smallness in probability plus a higher moment (`s92_tail_split`).
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

open MeasureTheory ProbabilityTheory Function Set Filter
open scoped ENNReal NNReal

noncomputable section

namespace HRS.MS.R2Mt

open HRS.Whole HRS.MS.Wr

variable {d N : ℕ}

/-! ### Preliminaries on `μ`, `N δ_N` -/

theorem s92_isProb_mu {ρ : Euc d → ℝ} (hρ : HRS.Whole.IsProbDensity ρ) :
    IsProbabilityMeasure (HRS.Whole.withDensityReal ρ) :=
  HRS.Whole.Q34.isProbabilityMeasure_nu hρ

theorem s92_mul_deltaN {s : ℝ} (hs : s < (d : ℝ) / 2) (hN : 2 ≤ N) :
    (N : ℝ) * HRS.deltaN d s N = 1 := by
  have hN0 : (N : ℝ) ≠ 0 := by
    have : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
    exact this.ne'
  have e : HRS.deltaN d s N = (N : ℝ)⁻¹ := by rw [HRS.Whole.deltaN_eq]; simp [hs]
  rw [e, mul_inv_cancel₀ hN0]

/-- The kernel `0` is an admissible pair kernel. -/
theorem s92_zero_kernel (s : ℝ) : IsBoundedPairKernel (d := d) s 0 (fun _ _ => 0) where
  measurable := measurable_const
  symm := fun _ _ => rfl
  bound := fun x y _ => by simp

/-! ### Two-sided pressure bound at `θ = 0` -/

theorem s92_normalizer_bounds (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) (M L bm bp : ℝ)
    (hbm : 0 < bm) (hb : bm < bp) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ρ : Euc d → ℝ, IsRound2Density d s M L ρ → ∀ N : ℕ, 2 ≤ N → ∀ b ∈ Set.Icc bm bp,
      GibbsWellDefined (fun x y => rieszKernel d s (x - y)) N b (HRS.Whole.withDensityReal ρ) ∧
      |Real.log (pairNormalizer (fun x y => rieszKernel d s (x - y)) N b (HRS.Whole.withDensityReal ρ))| ≤ C := by
  have hsd : s < d := by
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  obtain ⟨θ₀, hθ₀, C, hC⟩ := euclidean_pressure_proof hd hs0 hsd M L bm bp 0 hbm hb
  refine ⟨max C 0, le_max_right _ _, fun ρ hρ N hN b hb' => ?_⟩
  have h := hC ρ hρ.prob hρ.bdd hρ.logMoment (fun _ _ => 0) (s92_zero_kernel s) N hN b hb' 0
    (by rw [abs_zero]; exact hθ₀.le)
  have e : (fun x y : Euc d => rieszKernel d s (x - y) - (0 : ℝ) * (fun _ _ => (0 : ℝ)) x y) =
      fun x y => rieszKernel d s (x - y) := by
    funext x y; simp
  rw [e] at h
  refine ⟨h.1, h.2.trans ?_⟩
  rw [mul_assoc, s92_mul_deltaN hs hN, mul_one]
  exact le_max_left _ _

/-! ### The density of `Q_{N,b}` against `μ^{⊗N}` -/

/-- The density `ψ_b = K_b⁻¹ e^{-bNF^G}` of `pairGibbs G N b μ` with respect to `μ^{⊗N}`. -/
def s92_dens (G : Euc d → Euc d → ℝ) (N : ℕ) (b : ℝ) (μ : Measure (Euc d)) (X : EucConfig d N) : ℝ≥0∞ :=
  ENNReal.ofReal ((pairNormalizer G N b μ)⁻¹ * Real.exp (-b * N * pairEnergy G X μ))

theorem s92_dens_meas {μ : Measure (Euc d)} [SFinite μ] {G : Euc d → Euc d → ℝ}
    (hGm : Measurable (Function.uncurry G)) (b : ℝ) :
    Measurable (s92_dens G N b μ) :=
  ENNReal.measurable_ofReal.comp
    (measurable_const.mul (Real.measurable_exp.comp (measurable_const.mul (wr9_measurable_pairEnergy hGm))))

theorem s92_pairGibbs_eq {μ : Measure (Euc d)} [IsProbabilityMeasure μ] {G : Euc d → Euc d → ℝ}
    (hGm : Measurable (Function.uncurry G)) {b : ℝ} (hW : GibbsWellDefined G N b μ) :
    pairGibbs G N b μ = (Measure.pi fun _ : Fin N => μ).withDensity (s92_dens G N b μ) := by
  have hK := hW.normalizer_pos
  have hf : Measurable (fun X : EucConfig d N => ENNReal.ofReal (Real.exp (-b * N * pairEnergy G X μ))) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
      (measurable_const.mul (wr9_measurable_pairEnergy hGm)))
  have e : s92_dens G N b μ = (ENNReal.ofReal (pairNormalizer G N b μ))⁻¹ •
      (fun X : EucConfig d N => ENNReal.ofReal (Real.exp (-b * N * pairEnergy G X μ))) := by
    funext X
    simp only [s92_dens, Pi.smul_apply, smul_eq_mul]
    rw [ENNReal.ofReal_mul (inv_nonneg.2 hK.le), ENNReal.ofReal_inv_of_pos hK]
  rw [e, withDensity_smul _ hf]
  rfl

theorem s92_isProb_gibbs {μ : Measure (Euc d)} [IsProbabilityMeasure μ] {G : Euc d → Euc d → ℝ} {b : ℝ}
    (hW : GibbsWellDefined G N b μ) : IsProbabilityMeasure (pairGibbs G N b μ) :=
  wr9_gibbs_prob hW

/-- `∫ ψ_b² dμ^{⊗N} = K_{2b} / K_b²`. -/
theorem s92_dens_sq_lintegral {μ : Measure (Euc d)} [IsProbabilityMeasure μ] {G : Euc d → Euc d → ℝ}
    {b : ℝ} (hW : GibbsWellDefined G N b μ) (hW2 : GibbsWellDefined G N (2 * b) μ) :
    ∫⁻ X, (s92_dens G N b μ X) ^ 2 ∂(Measure.pi fun _ : Fin N => μ) =
      ENNReal.ofReal ((pairNormalizer G N b μ)⁻¹ ^ 2) * ENNReal.ofReal (pairNormalizer G N (2 * b) μ) := by
  have hK := hW.normalizer_pos
  have e : ∀ X : EucConfig d N, (s92_dens G N b μ X) ^ 2 =
      ENNReal.ofReal ((pairNormalizer G N b μ)⁻¹ ^ 2) *
        ENNReal.ofReal (Real.exp (-(2 * b) * N * pairEnergy G X μ)) := by
    intro X
    simp only [s92_dens]
    rw [← ENNReal.ofReal_pow (mul_nonneg (inv_nonneg.2 hK.le) (Real.exp_pos _).le),
      ← ENNReal.ofReal_mul (pow_nonneg (inv_nonneg.2 hK.le) 2)]
    congr 1
    rw [mul_pow, ← Real.exp_nat_mul]
    congr 2
    push_cast
    ring
  simp_rw [e]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, wr9_partition hW2]

/-- Uniform `L²(μ^{⊗N})` bound for the density of `Q_{N,b}`: `∫ ψ_b² ≤ e^{3 C}`. -/
theorem s92_psi_sq_le {A K K2 : ℝ} (hK : 0 < K) (hK2 : 0 < K2) (h1 : |Real.log K| ≤ A) (h2 : |Real.log K2| ≤ A) :
    ENNReal.ofReal (K⁻¹ ^ 2) * ENNReal.ofReal K2 ≤ ENNReal.ofReal (Real.exp (3 * A)) := by
  rw [← ENNReal.ofReal_mul (pow_nonneg (inv_nonneg.2 hK.le) 2)]
  refine ENNReal.ofReal_le_ofReal ?_
  have hl : Real.log (K⁻¹ ^ 2 * K2) ≤ 3 * A := by
    rw [Real.log_mul (pow_pos (inv_pos.2 hK) 2).ne' hK2.ne', Real.log_pow, Real.log_inv]
    have := (abs_le.1 h1).1
    have := (abs_le.1 h1).2
    have := (abs_le.1 h2).2
    push_cast
    linarith
  calc K⁻¹ ^ 2 * K2 = Real.exp (Real.log (K⁻¹ ^ 2 * K2)) :=
        (Real.exp_log (mul_pos (pow_pos (inv_pos.2 hK) 2) hK2)).symm
    _ ≤ Real.exp (3 * A) := Real.exp_le_exp.2 hl

/-! ### Step A: moments of `N F^h` under `Q_{N,b}` -/

/-- Polynomial moments from an exponential moment. -/
theorem s92_moment_of_exp {α : Type*} [MeasurableSpace α] (Q : Measure α) {G : α → ℝ} {c E : ℝ} (hc : 0 < c)
    (hint : Integrable (fun x => Real.exp (c * |G x|)) Q)
    (hle : ∫ x, Real.exp (c * |G x|) ∂Q ≤ E) (n : ℕ) :
    ∫⁻ x, ‖G x‖ₑ ^ n ∂Q ≤ ENNReal.ofReal ((n.factorial : ℝ) / c ^ n * E) := by
  have hpt : ∀ x, ‖G x‖ₑ ^ n ≤ ENNReal.ofReal ((n.factorial : ℝ) / c ^ n) *
        ENNReal.ofReal (Real.exp (c * |G x|)) := by
    intro x
    have h1 : ‖G x‖ₑ ^ n = ENNReal.ofReal (|G x| ^ n) := by
      rw [← ofReal_norm, Real.norm_eq_abs, ENNReal.ofReal_pow (abs_nonneg _)]
    rw [h1, ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have hx := Real.pow_div_factorial_le_exp (c * |G x|) (by positivity) n
    have hfac : (0 : ℝ) < n.factorial := by exact_mod_cast n.factorial_pos
    have hcn : 0 < c ^ n := pow_pos hc n
    rw [div_mul_eq_mul_div, le_div_iff₀ hcn]
    rw [div_le_iff₀ hfac] at hx
    calc |G x| ^ n * c ^ n = (c * |G x|) ^ n := by rw [← mul_pow]; ring
      _ ≤ Real.exp (c * |G x|) * n.factorial := hx
      _ = (n.factorial : ℝ) * Real.exp (c * |G x|) := by ring
  calc ∫⁻ x, ‖G x‖ₑ ^ n ∂Q
      ≤ ∫⁻ x, ENNReal.ofReal ((n.factorial : ℝ) / c ^ n) * ENNReal.ofReal (Real.exp (c * |G x|)) ∂Q :=
        lintegral_mono hpt
    _ = ENNReal.ofReal ((n.factorial : ℝ) / c ^ n) * ENNReal.ofReal (∫ x, Real.exp (c * |G x|) ∂Q) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall fun X => (Real.exp_pos _).le)]
    _ ≤ ENNReal.ofReal ((n.factorial : ℝ) / c ^ n * E) := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hle (by positivity))

theorem s92_moment_Q (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) (M L b B : ℝ) (hb : 0 < b)
    (n : ℕ) :
    ∃ Cn : ℝ, 0 ≤ Cn ∧ ∀ ρ : Euc d → ℝ, IsRound2Density d s M L ρ → ∀ h : Euc d → Euc d → ℝ,
      IsBoundedPairKernel s B h → ∀ N : ℕ, 2 ≤ N →
        ∫⁻ X : EucConfig d N, ‖(N : ℝ) * pairEnergy h X (HRS.Whole.withDensityReal ρ)‖ₑ ^ n
          ∂(HRS.Whole.modulatedGibbs (rieszKernel d s) N b (HRS.Whole.withDensityReal ρ)) ≤ ENNReal.ofReal Cn := by
  have hsd : s < d := by
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  obtain ⟨c, hc, C, hent⟩ := euclidean_pair_entropy_proof hd hs0 hsd M L b (2 * b) B hb (by linarith)
  obtain ⟨C0, hC0, hnorm⟩ := s92_normalizer_bounds hd hs0 hs M L b (2 * b) hb (by linarith)
  refine ⟨(n.factorial : ℝ) / c ^ n * Real.exp C, by positivity, fun ρ hρ h hh N hN => ?_⟩
  have hμ := s92_isProb_mu hρ.prob
  have hb' : b ∈ Set.Icc b (2 * b) := ⟨le_rfl, by linarith⟩
  have hW := (hnorm ρ hρ N hN b hb').1
  have hQ : IsProbabilityMeasure (HRS.Whole.modulatedGibbs (rieszKernel d s) N b (HRS.Whole.withDensityReal ρ)) :=
    by rw [← pairGibbs_diff]; exact wr9_gibbs_prob hW
  obtain ⟨⟨hint, hlog⟩, -⟩ := hent ρ hρ.prob hρ.bdd hρ.logMoment h hh N hN b hb'
  rw [mul_assoc, s92_mul_deltaN hs hN, mul_one] at hlog
  have hcongr : ∀ X : EucConfig d N, c * (N : ℝ) * |pairEnergy h X (HRS.Whole.withDensityReal ρ)| =
      c * |(N : ℝ) * pairEnergy h X (HRS.Whole.withDensityReal ρ)| := by
    intro X
    rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg N : (0 : ℝ) ≤ N), mul_assoc]
  simp_rw [hcongr] at hint hlog
  have hIpos := integral_exp_pos hint
  have hIle := (Real.log_le_iff_le_exp hIpos).1 hlog
  exact s92_moment_of_exp _ hc hint hIle n

/-- Polynomial moments from an exponential moment, `lintegral` form. -/
theorem s92_moment_of_lexp {α : Type*} [MeasurableSpace α] (Q : Measure α) {G : α → ℝ} {c E : ℝ} (hc : 0 < c)
    (hle : ∫⁻ x, ENNReal.ofReal (Real.exp (c * |G x|)) ∂Q ≤ ENNReal.ofReal E) (n : ℕ) :
    ∫⁻ x, ‖G x‖ₑ ^ n ∂Q ≤ ENNReal.ofReal ((n.factorial : ℝ) / c ^ n * E) := by
  have hpt : ∀ x, ‖G x‖ₑ ^ n ≤ ENNReal.ofReal ((n.factorial : ℝ) / c ^ n) *
        ENNReal.ofReal (Real.exp (c * |G x|)) := by
    intro x
    have h1 : ‖G x‖ₑ ^ n = ENNReal.ofReal (|G x| ^ n) := by
      rw [← ofReal_norm, Real.norm_eq_abs, ENNReal.ofReal_pow (abs_nonneg _)]
    rw [h1, ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have hx := Real.pow_div_factorial_le_exp (c * |G x|) (by positivity) n
    have hfac : (0 : ℝ) < n.factorial := by exact_mod_cast n.factorial_pos
    have hcn : 0 < c ^ n := pow_pos hc n
    rw [div_mul_eq_mul_div, le_div_iff₀ hcn]
    rw [div_le_iff₀ hfac] at hx
    calc |G x| ^ n * c ^ n = (c * |G x|) ^ n := by rw [← mul_pow]; ring
      _ ≤ Real.exp (c * |G x|) * n.factorial := hx
      _ = (n.factorial : ℝ) * Real.exp (c * |G x|) := by ring
  calc ∫⁻ x, ‖G x‖ₑ ^ n ∂Q
      ≤ ∫⁻ x, ENNReal.ofReal ((n.factorial : ℝ) / c ^ n) * ENNReal.ofReal (Real.exp (c * |G x|)) ∂Q :=
        lintegral_mono hpt
    _ = ENNReal.ofReal ((n.factorial : ℝ) / c ^ n) * ∫⁻ x, ENNReal.ofReal (Real.exp (c * |G x|)) ∂Q := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ ≤ ENNReal.ofReal ((n.factorial : ℝ) / c ^ n) * ENNReal.ofReal E := mul_le_mul' le_rfl hle
    _ = ENNReal.ofReal ((n.factorial : ℝ) / c ^ n * E) := by
        rw [← ENNReal.ofReal_mul (by positivity)]

/-! ### Hölder transfer along a density -/

/-- **Change of measure.**  If `λ = ν.withDensity ψ`, then
`‖X‖_{L^r(λ)} ≤ ‖ψ‖_{L^a(ν)}^{1/r} ‖X‖_{L^{r a'}(ν)}` with `a' = a/(a-1)`. -/
theorem s92_eLpNorm_withDensity_le {α : Type*} [MeasurableSpace α] (ν : Measure α) {ψ : α → ℝ≥0∞}
    (hψ : Measurable ψ) {X : α → ℝ} (hX : Measurable X) {r a : ℝ} (hr : 0 < r) (ha : 1 < a) :
    eLpNorm X (ENNReal.ofReal r) (ν.withDensity ψ) ≤
      ((∫⁻ x, ψ x ^ a ∂ν) ^ (1 / a)) ^ (1 / r) *
        eLpNorm X (ENNReal.ofReal (r * Real.conjExponent a)) ν := by
  have hpq : a.HolderConjugate (Real.conjExponent a) := Real.HolderConjugate.conjExponent ha
  set q : ℝ := Real.conjExponent a with hqdef
  have hq : 0 < q := hpq.symm.pos
  have hrq : 0 < r * q := mul_pos hr hq
  have hp0 : ENNReal.ofReal r ≠ 0 := (ENNReal.ofReal_pos.2 hr).ne'
  have hp1 : ENNReal.ofReal (r * q) ≠ 0 := (ENNReal.ofReal_pos.2 hrq).ne'
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 ENNReal.ofReal_ne_top hX.aestronglyMeasurable,
    eLpNorm_eq_lintegral_rpow_enorm_toReal hp1 ENNReal.ofReal_ne_top hX.aestronglyMeasurable]
  simp only [ENNReal.toReal_ofReal hr.le, ENNReal.toReal_ofReal hrq.le]
  have hXm : Measurable (fun x => ‖X x‖ₑ ^ r) := (measurable_enorm.comp hX).pow_const r
  have h1 : ∫⁻ x, ‖X x‖ₑ ^ r ∂(ν.withDensity ψ) = ∫⁻ x, (ψ * fun x => ‖X x‖ₑ ^ r) x ∂ν :=
    lintegral_withDensity_eq_lintegral_mul ν hψ hXm
  have h2 := ENNReal.lintegral_mul_le_Lp_mul_Lq ν hpq hψ.aemeasurable hXm.aemeasurable
  have h3 : ∫⁻ x, (‖X x‖ₑ ^ r) ^ q ∂ν = ∫⁻ x, ‖X x‖ₑ ^ (r * q) ∂ν := by
    refine lintegral_congr fun x => ?_
    rw [← ENNReal.rpow_mul]
  rw [h1]
  refine (ENNReal.rpow_le_rpow h2 (by positivity)).trans ?_
  have e : (1 / q) * (1 / r) = 1 / (r * q) := by field_simp
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity), h3, ← ENNReal.rpow_mul (∫⁻ x, ‖X x‖ₑ ^ (r * q) ∂ν) (1 / q) (1 / r), e]

/-- Real form of the change of measure. -/
theorem s92_eLpNorm_withDensity_le_real {α : Type*} [MeasurableSpace α] (ν : Measure α) {ψ : α → ℝ≥0∞}
    (hψ : Measurable ψ) {X : α → ℝ} (hX : Measurable X) {r a : ℝ} (hr : 0 < r) (ha : 1 < a)
    {A Bq : ℝ} (hA : 0 ≤ A) (hψA : (∫⁻ x, ψ x ^ a ∂ν) ^ (1 / a) ≤ ENNReal.ofReal A)
    (hX' : eLpNorm X (ENNReal.ofReal (r * Real.conjExponent a)) ν ≤ ENNReal.ofReal Bq) :
    eLpNorm X (ENNReal.ofReal r) (ν.withDensity ψ) ≤ ENNReal.ofReal (A ^ (1 / r) * Bq) := by
  refine (s92_eLpNorm_withDensity_le ν hψ hX hr ha).trans ?_
  have h1 : ((∫⁻ x, ψ x ^ a ∂ν) ^ (1 / a)) ^ (1 / r) ≤ ENNReal.ofReal (A ^ (1 / r)) := by
    calc ((∫⁻ x, ψ x ^ a ∂ν) ^ (1 / a)) ^ (1 / r) ≤ (ENNReal.ofReal A) ^ (1 / r) :=
          ENNReal.rpow_le_rpow hψA (by positivity)
      _ = ENNReal.ofReal (A ^ (1 / r)) := ENNReal.ofReal_rpow_of_nonneg hA (by positivity)
  calc _ ≤ ENNReal.ofReal (A ^ (1 / r)) * ENNReal.ofReal Bq := mul_le_mul' h1 hX'
    _ = ENNReal.ofReal (A ^ (1 / r) * Bq) := (ENNReal.ofReal_mul (by positivity)).symm

/-! ### Splitting an `L^m` moment into smallness in probability and a higher moment -/

theorem s92_tail_split {α : Type*} [MeasurableSpace α] (Q : Measure α) [IsProbabilityMeasure Q] {X : α → ℝ}
    (hX : Measurable X) (m : ℕ) {ε : ℝ} :
    ∫⁻ x, ‖X x‖ₑ ^ m ∂Q ≤ ENNReal.ofReal ε ^ m +
      (∫⁻ x, ‖X x‖ₑ ^ (2 * m) ∂Q) ^ (1 / 2 : ℝ) * (Q {x | ε < |X x|}) ^ (1 / 2 : ℝ) := by
  set A : Set α := {x | ε < |X x|} with hA
  have hAm : MeasurableSet A := measurableSet_lt measurable_const hX.abs
  have hpt : ∀ x, ‖X x‖ₑ ^ m ≤ ENNReal.ofReal ε ^ m + A.indicator (fun _ => (1 : ℝ≥0∞)) x * ‖X x‖ₑ ^ m := by
    intro x
    by_cases hx : x ∈ A
    · simp only [Set.indicator_of_mem hx, one_mul]
      exact le_add_self
    · have : |X x| ≤ ε := not_lt.1 hx
      have h2 : ‖X x‖ₑ ≤ ENNReal.ofReal ε := by
        rw [← ofReal_norm, Real.norm_eq_abs]
        exact ENNReal.ofReal_le_ofReal this
      exact le_add_right (pow_le_pow_left' h2 m)
  have hind : Measurable (A.indicator (fun _ => (1 : ℝ≥0∞))) := measurable_const.indicator hAm
  have hXm : Measurable (fun x => ‖X x‖ₑ ^ m) := (measurable_enorm.comp hX).pow_const m
  calc ∫⁻ x, ‖X x‖ₑ ^ m ∂Q
      ≤ ∫⁻ x, (ENNReal.ofReal ε ^ m + A.indicator (fun _ => (1 : ℝ≥0∞)) x * ‖X x‖ₑ ^ m) ∂Q :=
        lintegral_mono hpt
    _ = ENNReal.ofReal ε ^ m + ∫⁻ x, (A.indicator (fun _ => (1 : ℝ≥0∞)) * fun x => ‖X x‖ₑ ^ m) x ∂Q := by
        rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one]
        rfl
    _ ≤ ENNReal.ofReal ε ^ m + (∫⁻ x, (A.indicator (fun _ => (1 : ℝ≥0∞)) x) ^ (2 : ℝ) ∂Q) ^ (1 / 2 : ℝ) *
          (∫⁻ x, (‖X x‖ₑ ^ m) ^ (2 : ℝ) ∂Q) ^ (1 / 2 : ℝ) := by
        gcongr
        exact ENNReal.lintegral_mul_le_Lp_mul_Lq Q Real.HolderConjugate.two_two hind.aemeasurable
          hXm.aemeasurable
    _ = ENNReal.ofReal ε ^ m + (∫⁻ x, ‖X x‖ₑ ^ (2 * m) ∂Q) ^ (1 / 2 : ℝ) * (Q A) ^ (1 / 2 : ℝ) := by
        rw [mul_comm]
        congr 2
        · congr 1
          refine lintegral_congr fun x => ?_
          rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul, ← ENNReal.rpow_natCast]
          congr 1
          push_cast
          ring
        · have : ∀ x, (A.indicator (fun _ => (1 : ℝ≥0∞)) x) ^ (2 : ℝ) = A.indicator (fun _ => (1 : ℝ≥0∞)) x := by
            intro x
            by_cases hx : x ∈ A <;> simp [hx]
          simp_rw [this]
          rw [lintegral_indicator_const hAm, one_mul]

end HRS.MS.R2Mt
