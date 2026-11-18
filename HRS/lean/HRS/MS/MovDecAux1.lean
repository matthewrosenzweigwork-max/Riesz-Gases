import HRS.MS.MovForceTie
import HRS.MS.WrKernAux1
import HRS.MS.PsdAux2

/-!
# MOV-2e (1): the interaction form `⟨f, K f⟩`, the sandwich `ν I ≤ A ≤ C I`  (S6.2, TeX L4278-4343)

Namespace `HRS.MS.MovDec`, helper prefix `mov2e_`.  Infrastructure for S6.2 (`W:lem:r2mov-linear`, the exponential-decay
paragraph); not a manuscript row.

Setting.  `ρ = ψ²` is a smooth positive probability density with a Gaussian `ψ` (`Mov2eRho`; instantiated for a thermal
equilibrium in `MovDecAux3`), `g = rieszKernel d s`, `0 ≤ s < d`, `ν = β⁻¹`, `v` a Schwartz function and `f = v/ψ`.
For Gaussian bounded `h` put `U_h = g * h` (`HRS.Whole.convFun`).  The quadratic form of `A = ν I + K` on `f ∈ L²(ρ)` is, in the
variable `v = ψ f ∈ L²`,
`E(v) = ν ∫ v² + ∬ g(x-y) (ψ v)(x) (ψ v)(y) dx dy`  (`mov2eE`),
and the constant projection of `K` disappears since the form is evaluated on `⟨v, ψ⟩ = 0`.

Results (all for Schwartz `v`, `w`):
* `mov2e_pair_integrable`: absolute integrability of `g(x-y) h₁(x) h₂(y)` for Gaussian bounded continuous `h₁, h₂`
  (kernel majorant `|g| ≤ 2|z|^{-σ} + |z| + 1`; for `s = 0` the same for `g²`).
* `mov2e_kernel_L2`: `‖K_μ f‖_{L²(μ)} ≤ M ‖f‖_{L²(μ)}` for `f ∈ L²(μ)`, `μ = ρ dx`: Schur test for `s > 0`
  (`wr13c_schur_W_real`), Hilbert-Schmidt for `s = 0` (`∬ log²|x-y| ρ(x) ρ(y) < ∞`, local integrability of `log²`
  via the majorant `|z|^{-1/2}` of `|log|`).
* `mov2e_E_lower`, `mov2e_E_upper`: `ν ‖v‖² ≤ E(v) ≤ (ν + M) ‖v‖²` for `⟨v, ψ⟩ = 0`; positivity of the form:
  `wr13c_Kmu_nonneg` (`s > 0`, all of `L²(μ)`), `Psd.log_energy_nonneg` (`s = 0`, zero mass).
* `mov2e_E_expand`: `E(v + δ) = E(v) + 2 ⟨W_v, δ⟩ + E(δ)`, `W_v = ν v + ψ U_{ψ v}`.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.MovDec

open HRS.Whole

variable {d : ℕ}

/-! ### Gaussian bounded functions -/

/-- `∫ e^{-c‖y‖²} dy < ∞`. -/
lemma mov2e_gauss_int (hd : 1 ≤ d) {c : ℝ} (hc : 0 < c) :
    Integrable (fun y : Euc d => Real.exp (-c * ‖y‖ ^ 2)) := by
  have := movtr_integrable_rpow_gauss (d := d) hd (α := 0) (c := c)
    (by have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
        have : (1 : ℝ) ≤ d := by exact_mod_cast hd
        linarith) hc
  simpa using this

lemma mov2e_exp_mono {c c' : ℝ} (h : c' ≤ c) (r : ℝ) :
    Real.exp (-c * r ^ 2) ≤ Real.exp (-c' * r ^ 2) :=
  Real.exp_le_exp.mpr (by nlinarith [sq_nonneg r])

/-- A continuous function with a Gaussian bound. -/
def Mov2eGB (h : Euc d → ℝ) : Prop :=
  Continuous h ∧ ∃ C c : ℝ, 0 ≤ C ∧ 0 < c ∧ ∀ x, |h x| ≤ C * Real.exp (-c * ‖x‖ ^ 2)

lemma Mov2eGB.common {h₁ h₂ : Euc d → ℝ} (a : Mov2eGB h₁) (b : Mov2eGB h₂) :
    ∃ C c : ℝ, 0 ≤ C ∧ 0 < c ∧ (∀ x, |h₁ x| ≤ C * Real.exp (-c * ‖x‖ ^ 2)) ∧
      ∀ x, |h₂ x| ≤ C * Real.exp (-c * ‖x‖ ^ 2) := by
  obtain ⟨-, C₁, c₁, hC₁, hc₁, h₁b⟩ := a
  obtain ⟨-, C₂, c₂, hC₂, hc₂, h₂b⟩ := b
  refine ⟨max C₁ C₂, min c₁ c₂, le_max_of_le_left hC₁, lt_min hc₁ hc₂, fun x => ?_, fun x => ?_⟩
  · exact (h₁b x).trans (mul_le_mul (le_max_left _ _) (mov2e_exp_mono (min_le_left _ _) _)
      (Real.exp_pos _).le (le_max_of_le_left hC₁))
  · exact (h₂b x).trans (mul_le_mul (le_max_right _ _) (mov2e_exp_mono (min_le_right _ _) _)
      (Real.exp_pos _).le (le_max_of_le_left hC₁))

lemma Mov2eGB.add {h₁ h₂ : Euc d → ℝ} (a : Mov2eGB h₁) (b : Mov2eGB h₂) :
    Mov2eGB (fun x => h₁ x + h₂ x) := by
  obtain ⟨C, c, hC, hc, h1, h2⟩ := Mov2eGB.common a b
  refine ⟨a.1.add b.1, 2 * C, c, by positivity, hc, fun x => ?_⟩
  calc |h₁ x + h₂ x| ≤ |h₁ x| + |h₂ x| := abs_add_le _ _
    _ ≤ C * Real.exp (-c * ‖x‖ ^ 2) + C * Real.exp (-c * ‖x‖ ^ 2) := add_le_add (h1 x) (h2 x)
    _ = 2 * C * Real.exp (-c * ‖x‖ ^ 2) := by ring

lemma Mov2eGB.smul {h : Euc d → ℝ} (a : Mov2eGB h) (t : ℝ) : Mov2eGB (fun x => t * h x) := by
  obtain ⟨hc0, C, c, hC, hc, hb⟩ := a
  refine ⟨continuous_const.mul hc0, |t| * C, c, by positivity, hc, fun x => ?_⟩
  rw [abs_mul]
  calc |t| * |h x| ≤ |t| * (C * Real.exp (-c * ‖x‖ ^ 2)) := mul_le_mul_of_nonneg_left (hb x) (abs_nonneg _)
    _ = _ := by ring

lemma Mov2eGB.sub {h₁ h₂ : Euc d → ℝ} (a : Mov2eGB h₁) (b : Mov2eGB h₂) :
    Mov2eGB (fun x => h₁ x - h₂ x) := by
  have := a.add (b.smul (-1))
  simpa [sub_eq_add_neg] using this

/-! ### Integrability of the pair integrand -/

/-- **Pair integrability**: `(x, y) ↦ k(x-y) h₁(x) h₂(y)` is integrable on `ℝ^d × ℝ^d` whenever `h₁, h₂` have a
common Gaussian bound with rate `c` and `|k| e^{-(c/4)|z|²}` is integrable. -/
theorem mov2e_pair_integrable (hd : 1 ≤ d) {k : Euc d → ℝ} (hk : Measurable k) {C c : ℝ} (hC : 0 ≤ C)
    (hc : 0 < c) (hkint : Integrable (fun z : Euc d => |k z| * Real.exp (-(c / 4) * ‖z‖ ^ 2)))
    {h₁ h₂ : Euc d → ℝ} (hh₁ : Continuous h₁) (hh₂ : Continuous h₂)
    (hb₁ : ∀ x, |h₁ x| ≤ C * Real.exp (-c * ‖x‖ ^ 2)) (hb₂ : ∀ x, |h₂ x| ≤ C * Real.exp (-c * ‖x‖ ^ 2)) :
    Integrable (fun p : Euc d × Euc d => k (p.1 - p.2) * (h₁ p.1 * h₂ p.2))
      ((volume : Measure (Euc d)).prod volume) := by
  have hT : MeasurePreserving (fun p : Euc d × Euc d => (p.1 - p.2, p.2))
      ((volume : Measure (Euc d)).prod volume) ((volume : Measure (Euc d)).prod volume) :=
    measurePreserving_sub_prod volume volume
  set Ft : Euc d × Euc d → ℝ := fun q => k q.1 * (h₁ (q.1 + q.2) * h₂ q.2) with hFt
  have hmaj : Integrable (fun q : Euc d × Euc d =>
      (C ^ 2 * (|k q.1| * Real.exp (-(c / 4) * ‖q.1‖ ^ 2))) * Real.exp (-(c / 2) * ‖q.2‖ ^ 2))
      ((volume : Measure (Euc d)).prod volume) :=
    (hkint.const_mul (C ^ 2)).mul_prod (mov2e_gauss_int hd (by positivity : 0 < c / 2))
  have hmeas : AEStronglyMeasurable Ft ((volume : Measure (Euc d)).prod volume) := by
    have h1 : Measurable (fun q : Euc d × Euc d => k q.1) := hk.comp measurable_fst
    have h2 : Continuous (fun q : Euc d × Euc d => h₁ (q.1 + q.2)) :=
      hh₁.comp (continuous_fst.add continuous_snd)
    have h3 : Continuous (fun q : Euc d × Euc d => h₂ q.2) := hh₂.comp continuous_snd
    exact (h1.aestronglyMeasurable.mul (h2.mul h3).aestronglyMeasurable)
  have hFtint : Integrable Ft ((volume : Measure (Euc d)).prod volume) := by
    refine Integrable.mono' hmaj hmeas (Filter.Eventually.of_forall fun q => ?_)
    obtain ⟨z, y⟩ := q
    simp only [hFt, norm_mul, Real.norm_eq_abs]
    have e1 := hb₁ (z + y)
    have e2 := hb₂ y
    have hsq : ‖z‖ ^ 2 ≤ 2 * (‖z + y‖ ^ 2 + ‖y‖ ^ 2) := by
      have : ‖z‖ ≤ ‖z + y‖ + ‖y‖ := by
        calc ‖z‖ = ‖(z + y) - y‖ := by simp
          _ ≤ ‖z + y‖ + ‖y‖ := norm_sub_le _ _
      nlinarith [norm_nonneg z, norm_nonneg y, norm_nonneg (z + y), sq_nonneg (‖z + y‖ - ‖y‖)]
    have hexp : Real.exp (-c * ‖z + y‖ ^ 2) * Real.exp (-c * ‖y‖ ^ 2) ≤
        Real.exp (-(c / 4) * ‖z‖ ^ 2) * Real.exp (-(c / 2) * ‖y‖ ^ 2) := by
      rw [← Real.exp_add, ← Real.exp_add]
      apply Real.exp_le_exp.mpr
      nlinarith [sq_nonneg ‖y‖, sq_nonneg ‖z + y‖]
    have hkk : 0 ≤ |k z| := abs_nonneg _
    calc |k z| * (|h₁ (z + y)| * |h₂ y|)
        ≤ |k z| * ((C * Real.exp (-c * ‖z + y‖ ^ 2)) * (C * Real.exp (-c * ‖y‖ ^ 2))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul e1 e2 (abs_nonneg _) (by positivity)) hkk
      _ = C ^ 2 * |k z| * (Real.exp (-c * ‖z + y‖ ^ 2) * Real.exp (-c * ‖y‖ ^ 2)) := by ring
      _ ≤ C ^ 2 * |k z| * (Real.exp (-(c / 4) * ‖z‖ ^ 2) * Real.exp (-(c / 2) * ‖y‖ ^ 2)) :=
          mul_le_mul_of_nonneg_left hexp (by positivity)
      _ = _ := by ring
  have := hT.integrable_comp_of_integrable hFtint
  refine this.congr (Filter.Eventually.of_forall fun p => ?_)
  simp [hFt]


/-! ### The kernel -/

lemma mov2e_g_meas (d : ℕ) (s : ℝ) : Measurable (rieszKernel d s : Euc d → ℝ) := by
  unfold rieszKernel
  by_cases hs : s = 0
  · simp only [hs, ite_true]
    exact (Real.measurable_log.comp measurable_norm).neg
  · simp only [hs, ite_false]
    exact measurable_norm.pow_const _

lemma mov2e_g_even (d : ℕ) (s : ℝ) (z : Euc d) : rieszKernel d s (-z) = rieszKernel d s z := by
  simp [rieszKernel]

/-- `|g| e^{-(c/4)|z|²}` is integrable. -/
lemma mov2e_g_gauss_int (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {c : ℝ} (hc : 0 < c) :
    Integrable (fun z : Euc d => |rieszKernel d s z| * Real.exp (-(c / 4) * ‖z‖ ^ 2)) := by
  obtain ⟨-, hB, hBint⟩ := HRS.MS.MovForce.mv1_g_data (d := d) hd hs0 hsd (c := c / 2) (by positivity)
  have e : -(c / 2 / 2) = -(c / 4) := by ring
  rw [e] at hBint
  refine Integrable.mono' hBint
    (((mov2e_g_meas d s).abs.mul
      (Real.measurable_exp.comp ((measurable_norm.pow_const 2).const_mul _))).aestronglyMeasurable) ?_
  filter_upwards [hB] with z hz
  rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_abs, abs_of_pos (Real.exp_pos _)]
  exact mul_le_mul_of_nonneg_right hz (Real.exp_pos _).le

/-- The pair integrand of the kernel `g` against two Gaussian bounded profiles. -/
theorem mov2e_g_pair_integrable (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {h₁ h₂ : Euc d → ℝ}
    (a : Mov2eGB h₁) (b : Mov2eGB h₂) :
    Integrable (fun p : Euc d × Euc d => rieszKernel d s (p.1 - p.2) * (h₁ p.1 * h₂ p.2))
      ((volume : Measure (Euc d)).prod volume) := by
  obtain ⟨C, c, hC, hc, h1, h2⟩ := Mov2eGB.common a b
  exact mov2e_pair_integrable hd (mov2e_g_meas d s) hC hc (mov2e_g_gauss_int hd hs0 hsd hc) a.1 b.1 h1 h2

/-- `g² e^{-c|z|²}` is integrable for `s = 0`, `d ≥ 2`. -/
lemma mov2e_g0_sq_gauss_int (hd : 2 ≤ d) {c : ℝ} (hc : 0 < c) :
    Integrable (fun z : Euc d => (rieszKernel d 0 z) ^ 2 * Real.exp (-c * ‖z‖ ^ 2)) := by
  have hd1 : 1 ≤ d := by omega
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have i1 := movtr_integrable_rpow_gauss (d := d) hd1 (α := -1) (c := c) (by linarith) hc
  have i2 := movtr_integrable_rpow_gauss (d := d) hd1 (α := 2) (c := c) (by linarith) hc
  have i3 := movtr_integrable_rpow_gauss (d := d) hd1 (α := 0) (c := c) (by linarith) hc
  have hmaj := ((i1.const_mul 12).add (i2.const_mul 3)).add (i3.const_mul 3)
  obtain ⟨-, hB, -⟩ := HRS.MS.MovForce.mv1_g_data (d := d) hd1 (s := 0) le_rfl (by linarith) hc
  refine Integrable.mono' hmaj
    ((((mov2e_g_meas d 0).pow_const 2).mul
      (Real.measurable_exp.comp ((measurable_norm.pow_const 2).const_mul _))).aestronglyMeasurable) ?_
  filter_upwards [hB, movtr_ae_ne_zero (d := d) hd1] with z hz hz0
  have hr : 0 < ‖z‖ := norm_pos_iff.2 hz0
  have hsp : movtr_sp (0 : ℝ) = 1 / 2 := by simp [movtr_sp]
  rw [hsp] at hz
  have hpow : (‖z‖ ^ (-(1 / 2 : ℝ))) ^ 2 = ‖z‖ ^ (-1 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hr.le]; norm_num
  have hnn : 0 ≤ ‖z‖ ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hr.le _
  have hsq : (rieszKernel d 0 z) ^ 2 ≤ 12 * ‖z‖ ^ (-1 : ℝ) + 3 * ‖z‖ ^ (2 : ℝ) + 3 := by
    have h1 : (rieszKernel d 0 z) ^ 2 ≤ (2 * ‖z‖ ^ (-(1 / 2 : ℝ)) + ‖z‖ + 1) ^ 2 :=
      sq_le_sq' (by linarith [abs_le.1 hz, norm_nonneg z]) (abs_le.1 hz).2
    have h2 : (2 * ‖z‖ ^ (-(1 / 2 : ℝ)) + ‖z‖ + 1) ^ 2 ≤
        3 * (4 * (‖z‖ ^ (-(1 / 2 : ℝ))) ^ 2 + ‖z‖ ^ 2 + 1) := by
      nlinarith [sq_nonneg (2 * ‖z‖ ^ (-(1 / 2 : ℝ)) - ‖z‖), sq_nonneg (‖z‖ - 1),
        sq_nonneg (2 * ‖z‖ ^ (-(1 / 2 : ℝ)) - 1)]
    rw [hpow] at h2
    have h3 : ‖z‖ ^ (2 : ℝ) = ‖z‖ ^ 2 := by rw [← Real.rpow_natCast]; norm_num
    rw [h3]
    linarith
  rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), abs_of_nonneg (sq_nonneg _)]
  have h3 : ‖z‖ ^ (0 : ℝ) = 1 := Real.rpow_zero _
  simp only [Pi.add_apply, h3]
  calc (rieszKernel d 0 z) ^ 2 * Real.exp (-c * ‖z‖ ^ 2)
      ≤ (12 * ‖z‖ ^ (-1 : ℝ) + 3 * ‖z‖ ^ (2 : ℝ) + 3) * Real.exp (-c * ‖z‖ ^ 2) :=
        mul_le_mul_of_nonneg_right hsq (Real.exp_pos _).le
    _ = _ := by ring


/-! ### The thermal data and the measure `μ = ρ dx` -/

/-- The thermal data used here: `ρ > 0` smooth with Gaussian `√ρ` (`MovRhoData`), and a probability density. -/
structure Mov2eRho (d : ℕ) (ρ : Euc d → ℝ) : Prop where
  data : HRS.MS.MovForce.MovRhoData d ρ
  prob : HRS.Whole.IsProbDensity ρ

namespace Mov2eRho

variable {ρ : Euc d → ℝ}

lemma pos (h : Mov2eRho d ρ) (x : Euc d) : 0 < ρ x := h.data.pos x

lemma psi_sq (h : Mov2eRho d ρ) (x : Euc d) : Real.sqrt (ρ x) * Real.sqrt (ρ x) = ρ x :=
  Real.mul_self_sqrt (h.pos x).le

lemma psi_pos (h : Mov2eRho d ρ) (x : Euc d) : 0 < Real.sqrt (ρ x) := Real.sqrt_pos.2 (h.pos x)

lemma psi_GB (h : Mov2eRho d ρ) : Mov2eGB (fun x => Real.sqrt (ρ x)) := by
  refine ⟨h.data.sqrt_smooth.continuous, ?_⟩
  obtain ⟨C, c, hc, hb⟩ := h.data.sqrt_gauss 0
  have hC : 0 ≤ C := by
    have := hb 0
    simp only [norm_zero, mul_zero, zero_pow two_ne_zero, Real.exp_zero, mul_one] at this
    exact (norm_nonneg _).trans this
  refine ⟨C, c, hC, hc, fun x => ?_⟩
  have := hb x
  rwa [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at this

lemma rho_GB (h : Mov2eRho d ρ) : Mov2eGB ρ := by
  obtain ⟨hc0, C, c, hC, hc, hb⟩ := h.psi_GB
  refine ⟨h.data.smooth.continuous, C ^ 2, c, by positivity, hc, fun x => ?_⟩
  have h1 := hb x
  have h2 : ρ x = Real.sqrt (ρ x) * Real.sqrt (ρ x) := (h.psi_sq x).symm
  have hn : |ρ x| = |Real.sqrt (ρ x)| * |Real.sqrt (ρ x)| := by rw [← abs_mul, ← h2]
  rw [hn]
  calc |Real.sqrt (ρ x)| * |Real.sqrt (ρ x)| ≤ (C * Real.exp (-c * ‖x‖ ^ 2)) * (C * Real.exp (-c * ‖x‖ ^ 2)) :=
        mul_le_mul h1 h1 (abs_nonneg _) (by positivity)
    _ = C ^ 2 * (Real.exp (-c * ‖x‖ ^ 2) * Real.exp (-c * ‖x‖ ^ 2)) := by ring
    _ = C ^ 2 * Real.exp (-(2 * c) * ‖x‖ ^ 2) := by
        rw [← Real.exp_add]; congr 2; ring
    _ ≤ C ^ 2 * Real.exp (-c * ‖x‖ ^ 2) :=
        mul_le_mul_of_nonneg_left (mov2e_exp_mono (by linarith) _) (by positivity)

lemma rho_bdd (h : Mov2eRho d ρ) : ∃ M : ℝ, 0 ≤ M ∧ ∀ x, ρ x ≤ M := by
  obtain ⟨-, C, c, hC, hc, hb⟩ := h.rho_GB
  refine ⟨C, hC, fun x => ?_⟩
  refine (le_abs_self _).trans ((hb x).trans ?_)
  have : Real.exp (-c * ‖x‖ ^ 2) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith [sq_nonneg ‖x‖])
  nlinarith

/-- `ψ a` is Gaussian bounded for continuous bounded `a`. -/
lemma mul_GB (h : Mov2eRho d ρ) {a : Euc d → ℝ} (ha : Continuous a) {M : ℝ} (hM : ∀ x, |a x| ≤ M) :
    Mov2eGB (fun x => Real.sqrt (ρ x) * a x) := by
  obtain ⟨hc0, C, c, hC, hc, hb⟩ := h.psi_GB
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  refine ⟨hc0.mul ha, C * M, c, by positivity, hc, fun x => ?_⟩
  rw [abs_mul]
  calc |Real.sqrt (ρ x)| * |a x| ≤ (C * Real.exp (-c * ‖x‖ ^ 2)) * M :=
        mul_le_mul (hb x) (hM x) (abs_nonneg _) (by positivity)
    _ = _ := by ring

lemma schwartz_GB (h : Mov2eRho d ρ) (a : SchwartzMap (Euc d) ℝ) :
    Mov2eGB (fun x => Real.sqrt (ρ x) * a x) := by
  obtain ⟨M, hM⟩ := HRS.MS.MovForce.mv1_schwartz_bdd a 0
  exact h.mul_GB a.continuous (M := M) fun x => by
    have := hM x
    rwa [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at this

end Mov2eRho

lemma mov2e_isProb {ρ : Euc d → ℝ} (hρ : Mov2eRho d ρ) : IsProbabilityMeasure (HRS.Whole.withDensityReal ρ) :=
  HRS.Whole.Q34.isProbabilityMeasure_nu hρ.prob

lemma mov2e_integral_mu {ρ : Euc d → ℝ} (hρ : Mov2eRho d ρ) (F : Euc d → ℝ) :
    ∫ x, F x ∂(HRS.Whole.withDensityReal ρ) = ∫ x, ρ x * F x := by
  unfold HRS.Whole.withDensityReal
  rw [integral_withDensity_eq_integral_toReal_smul hρ.prob.measurable.ennreal_ofReal
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp [ENNReal.toReal_ofReal (hρ.prob.nonneg x)]

lemma mov2e_integrable_mu {ρ : Euc d → ℝ} (hρ : Mov2eRho d ρ) {F : Euc d → ℝ} :
    Integrable F (HRS.Whole.withDensityReal ρ) ↔ Integrable (fun x => ρ x * F x) := by
  unfold HRS.Whole.withDensityReal
  rw [integrable_withDensity_iff_integrable_smul' hρ.prob.measurable.ennreal_ofReal
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp [ENNReal.toReal_ofReal (hρ.prob.nonneg _)]

lemma mov2e_ae_mu {ρ : Euc d → ℝ} {P : Euc d → Prop} (h : ∀ᵐ x, P x) : ∀ᵐ x ∂(HRS.Whole.withDensityReal ρ), P x :=
  (withDensity_absolutelyContinuous _ _).ae_le h

/-- The kernel operator `K̃ f (x) = ∫ g(x-y) f(y) dμ(y)` (without the constant projection). -/
def mov2eKt (d : ℕ) (s : ℝ) (ρ f : Euc d → ℝ) (x : Euc d) : ℝ :=
  ∫ y, rieszKernel d s (x - y) * f y ∂(HRS.Whole.withDensityReal ρ)

lemma mov2eKt_eq {ρ : Euc d → ℝ} (hρ : Mov2eRho d ρ) (s : ℝ) (f : Euc d → ℝ) (x : Euc d) :
    mov2eKt d s ρ f x = HRS.Whole.convFun (rieszKernel d s) (fun y => ρ y * f y) x := by
  unfold mov2eKt HRS.Whole.convFun
  rw [mov2e_integral_mu hρ]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  ring

lemma mov2e_rho_div {ρ : Euc d → ℝ} (hρ : Mov2eRho d ρ) (a : Euc d → ℝ) (y : Euc d) :
    ρ y * (a y / Real.sqrt (ρ y)) = Real.sqrt (ρ y) * a y := by
  have hs := hρ.psi_pos y
  have hss := hρ.psi_sq y
  generalize Real.sqrt (ρ y) = p at hs hss ⊢
  rw [← hss]
  field_simp

/-! ### Cauchy-Schwarz -/

lemma mov2e_cs {α : Type*} [MeasurableSpace α] {μ : Measure α} {a b : α → ℝ} (ha : MemLp a 2 μ)
    (hb : MemLp b 2 μ) :
    (∫ x, a x * b x ∂μ) ^ 2 ≤ (∫ x, a x ^ 2 ∂μ) * (∫ x, b x ^ 2 ∂μ) := by
  have hab : Integrable (fun x => a x * b x) μ := ha.integrable_mul hb
  have ha2 := ha.integrable_sq
  have hb2 := hb.integrable_sq
  have key : ∀ t : ℝ, 0 ≤ (∫ x, a x ^ 2 ∂μ) * (t * t) + (2 * ∫ x, a x * b x ∂μ) * t +
      ∫ x, b x ^ 2 ∂μ := by
    intro t
    have h0 : 0 ≤ ∫ x, (t * a x + b x) ^ 2 ∂μ := integral_nonneg fun x => sq_nonneg _
    have h1 : ∫ x, (t * a x + b x) ^ 2 ∂μ =
        t ^ 2 * ∫ x, a x ^ 2 ∂μ + 2 * t * ∫ x, a x * b x ∂μ + ∫ x, b x ^ 2 ∂μ := by
      have e : (fun x => (t * a x + b x) ^ 2) =
          fun x => t ^ 2 * a x ^ 2 + 2 * t * (a x * b x) + b x ^ 2 := by funext x; ring
      have i1 : Integrable (fun x => t ^ 2 * a x ^ 2) μ := ha2.const_mul _
      have i2 : Integrable (fun x => 2 * t * (a x * b x)) μ := hab.const_mul _
      have i3 : Integrable (fun x => t ^ 2 * a x ^ 2 + 2 * t * (a x * b x)) μ := i1.add i2
      rw [e, integral_add i3 hb2, integral_add i1 i2, integral_const_mul, integral_const_mul]
    rw [h1] at h0
    nlinarith [h0]
  have := discrim_le_zero key
  unfold discrim at this
  nlinarith [this]

/-! ### Hilbert-Schmidt bound for `s = 0` -/

theorem mov2e_kernel_L2_zero (hd : 2 ≤ d) {ρ : Euc d → ℝ} (hρ : Mov2eRho d ρ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ f : Euc d → ℝ, Measurable f → MemLp f 2 (HRS.Whole.withDensityReal ρ) →
      MemLp (mov2eKt d 0 ρ f) 2 (HRS.Whole.withDensityReal ρ) ∧
      ∫ x, (mov2eKt d 0 ρ f x) ^ 2 ∂(HRS.Whole.withDensityReal ρ) ≤
        M ^ 2 * ∫ x, f x ^ 2 ∂(HRS.Whole.withDensityReal ρ) := by
  have hd1 : 1 ≤ d := by omega
  have := mov2e_isProb hρ
  set μ := HRS.Whole.withDensityReal ρ with hμ
  set g : Euc d → ℝ := rieszKernel d 0 with hg
  have hgm : Measurable g := mov2e_g_meas d 0
  obtain ⟨hcr, C, c, hC, hc, hb⟩ := hρ.rho_GB
  have hint2 : Integrable (fun p : Euc d × Euc d => g (p.1 - p.2) ^ 2 * (ρ p.1 * ρ p.2))
      ((volume : Measure (Euc d)).prod volume) := by
    refine mov2e_pair_integrable hd1 (k := fun z => g z ^ 2) (hgm.pow_const 2) hC hc ?_ hcr hcr hb hb
    refine (mov2e_g0_sq_gauss_int hd (c := c / 4) (by positivity)).congr
      (Filter.Eventually.of_forall fun z => ?_)
    show _ = |g z ^ 2| * _
    rw [abs_sq]
  -- the slices
  have hslice : ∀ᵐ x : Euc d, Integrable (fun y => g (x - y) ^ 2) μ := by
    filter_upwards [hint2.prod_right_ae] with x hx
    rw [mov2e_integrable_mu hρ]
    have := hx.const_mul (ρ x)⁻¹
    refine this.congr (Filter.Eventually.of_forall fun y => ?_)
    have hx0 := hρ.pos x
    simp only
    field_simp
  have hGint : Integrable (fun x => ρ x * ∫ y, g (x - y) ^ 2 ∂μ) := by
    have := hint2.integral_prod_left
    refine this.congr (Filter.Eventually.of_forall fun x => ?_)
    simp only
    rw [mov2e_integral_mu hρ, ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    ring
  have hGμ : Integrable (fun x => ∫ y, g (x - y) ^ 2 ∂μ) μ := (mov2e_integrable_mu hρ).2 hGint
  set H : ℝ := ∫ x, ∫ y, g (x - y) ^ 2 ∂μ ∂μ with hH
  have hH0 : 0 ≤ H := integral_nonneg fun x => integral_nonneg fun y => sq_nonneg _
  refine ⟨Real.sqrt H, Real.sqrt_nonneg _, fun f hf hf2 => ?_⟩
  set F2 : ℝ := ∫ x, f x ^ 2 ∂μ with hF2
  have hF20 : 0 ≤ F2 := integral_nonneg fun x => sq_nonneg _
  have hmeasK : AEStronglyMeasurable (mov2eKt d 0 ρ f) μ := by
    have : Measurable (fun p : Euc d × Euc d => g (p.1 - p.2) * f p.2) :=
      (hgm.comp (measurable_fst.sub measurable_snd)).mul (hf.comp measurable_snd)
    exact (this.stronglyMeasurable.integral_prod_right').aestronglyMeasurable
  have hpt : ∀ᵐ x ∂μ, (mov2eKt d 0 ρ f x) ^ 2 ≤ (∫ y, g (x - y) ^ 2 ∂μ) * F2 := by
    filter_upwards [mov2e_ae_mu (ρ := ρ) hslice] with x hx
    have hA : MemLp (fun y => g (x - y)) 2 μ :=
      (memLp_two_iff_integrable_sq ((hgm.comp (measurable_const.sub measurable_id)).aestronglyMeasurable)).2 hx
    have := mov2e_cs hA hf2
    simpa [mov2eKt] using this
  have hbound : Integrable (fun x => (∫ y, g (x - y) ^ 2 ∂μ) * F2) μ := hGμ.mul_const _
  have hsqint : Integrable (fun x => (mov2eKt d 0 ρ f x) ^ 2) μ :=
    Integrable.mono' hbound (hmeasK.pow 2) (hpt.mono fun x hx => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; exact hx)
  refine ⟨(memLp_two_iff_integrable_sq hmeasK).2 hsqint, ?_⟩
  calc ∫ x, (mov2eKt d 0 ρ f x) ^ 2 ∂μ ≤ ∫ x, (∫ y, g (x - y) ^ 2 ∂μ) * F2 ∂μ :=
        integral_mono_ae hsqint hbound hpt
    _ = H * F2 := by rw [integral_mul_const]
    _ = Real.sqrt H ^ 2 * F2 := by rw [Real.sq_sqrt hH0]


/-! ### The `L²(μ)` bound for all `0 ≤ s < d` -/

/-- **`K_μ` is bounded on `L²(μ)`** (`A ≤ C I`): Schur test for `s > 0`, Hilbert-Schmidt for `s = 0`. -/
theorem mov2e_kernel_L2 (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {ρ : Euc d → ℝ}
    (hρ : Mov2eRho d ρ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ f : Euc d → ℝ, Measurable f → MemLp f 2 (HRS.Whole.withDensityReal ρ) →
      MemLp (mov2eKt d s ρ f) 2 (HRS.Whole.withDensityReal ρ) ∧
      ∫ x, (mov2eKt d s ρ f x) ^ 2 ∂(HRS.Whole.withDensityReal ρ) ≤
        M ^ 2 * ∫ x, f x ^ 2 ∂(HRS.Whole.withDensityReal ρ) := by
  rcases hs0.eq_or_lt with h0 | h0
  · subst h0
    exact mov2e_kernel_L2_zero hd hρ
  · obtain ⟨M, -, hM⟩ := hρ.rho_bdd
    obtain ⟨C, hC0, hC⟩ := HRS.MS.Wr.wr13c_schur_W_real (d := d) (by omega) h0.le hsd M
    refine ⟨C * 1, by positivity, fun f hf hf2 => ?_⟩
    exact hC ρ hρ.prob hM 1 zero_le_one (fun x y => rieszKernel d s (x - y))
      ((mov2e_g_meas d s).comp (measurable_fst.sub measurable_snd))
      (fun x y _ => by
        have : rieszKernel d s (x - y) = HRS.Whole.rieszWeight s (x - y) := by
          simp [rieszKernel, HRS.Whole.rieszWeight, h0.ne']
        rw [this, abs_of_nonneg (by simp [HRS.Whole.rieszWeight, h0.ne', Real.rpow_nonneg (norm_nonneg _)])]
        linarith)
      f hf hf2

/-! ### The pair form -/

/-- `∬ g(x-y) h₁(x) h₂(y) dx dy`. -/
def mov2ePairF (d : ℕ) (s : ℝ) (h₁ h₂ : Euc d → ℝ) : ℝ :=
  ∫ p : Euc d × Euc d, rieszKernel d s (p.1 - p.2) * (h₁ p.1 * h₂ p.2)
    ∂((volume : Measure (Euc d)).prod volume)

section Pair

variable {s : ℝ}

lemma mov2ePairF_add_left (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {h₁ h₂ h₃ : Euc d → ℝ}
    (a : Mov2eGB h₁) (b : Mov2eGB h₂) (c : Mov2eGB h₃) :
    mov2ePairF d s (fun x => h₁ x + h₂ x) h₃ = mov2ePairF d s h₁ h₃ + mov2ePairF d s h₂ h₃ := by
  unfold mov2ePairF
  rw [← integral_add (mov2e_g_pair_integrable hd hs0 hsd a c) (mov2e_g_pair_integrable hd hs0 hsd b c)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
  simp only
  ring

lemma mov2ePairF_smul_left {h₁ h₃ : Euc d → ℝ} (t : ℝ) :
    mov2ePairF d s (fun x => t * h₁ x) h₃ = t * mov2ePairF d s h₁ h₃ := by
  unfold mov2ePairF
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
  simp only
  ring

lemma mov2ePairF_symm (h₁ h₂ : Euc d → ℝ) : mov2ePairF d s h₁ h₂ = mov2ePairF d s h₂ h₁ := by
  unfold mov2ePairF
  rw [← integral_prod_swap (μ := (volume : Measure (Euc d))) (ν := (volume : Measure (Euc d)))]
  refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
  simp only [Prod.fst_swap, Prod.snd_swap]
  have : rieszKernel d s (p.2 - p.1) = rieszKernel d s (p.1 - p.2) := by
    rw [← neg_sub p.1 p.2, mov2e_g_even]
  rw [this]
  ring

lemma mov2ePairF_add_right (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {h₁ h₂ h₃ : Euc d → ℝ}
    (a : Mov2eGB h₁) (b : Mov2eGB h₂) (c : Mov2eGB h₃) :
    mov2ePairF d s h₁ (fun x => h₂ x + h₃ x) = mov2ePairF d s h₁ h₂ + mov2ePairF d s h₁ h₃ := by
  calc mov2ePairF d s h₁ (fun x => h₂ x + h₃ x) = mov2ePairF d s (fun x => h₂ x + h₃ x) h₁ :=
        mov2ePairF_symm _ _
    _ = mov2ePairF d s h₂ h₁ + mov2ePairF d s h₃ h₁ := mov2ePairF_add_left hd hs0 hsd b c a
    _ = _ := by rw [mov2ePairF_symm (h₁ := h₂), mov2ePairF_symm (h₁ := h₃)]

lemma mov2ePairF_smul_right {h₁ h₃ : Euc d → ℝ} (t : ℝ) :
    mov2ePairF d s h₃ (fun x => t * h₁ x) = t * mov2ePairF d s h₃ h₁ := by
  rw [mov2ePairF_symm, mov2ePairF_smul_left (s := s) t, mov2ePairF_symm]

/-- The iterated form `∫ h₁ (g * h₂)`. -/
lemma mov2ePairF_eq_iter (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {h₁ h₂ : Euc d → ℝ}
    (a : Mov2eGB h₁) (b : Mov2eGB h₂) :
    mov2ePairF d s h₁ h₂ = ∫ x, h₁ x * HRS.Whole.convFun (rieszKernel d s) h₂ x := by
  unfold mov2ePairF
  rw [integral_prod _ (mov2e_g_pair_integrable hd hs0 hsd a b)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [HRS.Whole.convFun]
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  ring

/-- `h₁ · (g * h₂)` is integrable. -/
lemma mov2e_conv_mul_integrable (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {h₁ h₂ : Euc d → ℝ}
    (a : Mov2eGB h₁) (b : Mov2eGB h₂) :
    Integrable (fun x => h₁ x * HRS.Whole.convFun (rieszKernel d s) h₂ x) := by
  have := (mov2e_g_pair_integrable hd hs0 hsd a b).integral_prod_left
  refine this.congr (Filter.Eventually.of_forall fun x => ?_)
  simp only [HRS.Whole.convFun]
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  ring

end Pair


/-! ### The energy form -/

lemma Mov2eGB.integrable {h : Euc d → ℝ} (hd : 1 ≤ d) (a : Mov2eGB h) : Integrable h := by
  obtain ⟨hc0, C, c, hC, hc, hb⟩ := a
  refine Integrable.mono' ((mov2e_gauss_int hd hc).const_mul C) hc0.aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs]; exact hb x

lemma mov2e_schw_int (a b : SchwartzMap (Euc d) ℝ) : Integrable (fun x => a x * b x) :=
  (a.memLp 2 volume).integrable_mul (b.memLp 2 volume)

/-- `E(v) = ν ∫ v² + ∬ g(x-y) (ψ v)(x) (ψ v)(y)`: the quadratic form `⟨f, A f⟩_{L²(ρ)}` of `A = ν I + K`
in the variable `v = ψ f`, `ν = β⁻¹`. -/
def mov2eE (d : ℕ) (s β : ℝ) (ρ v : Euc d → ℝ) : ℝ :=
  β⁻¹ * (∫ x, v x ^ 2) + mov2ePairF d s (fun x => Real.sqrt (ρ x) * v x) (fun x => Real.sqrt (ρ x) * v x)

/-- `W_u = ν u + ψ (g * (ψ u)) = ψ · A f`: the gradient of the energy is `2 W_u`. -/
def mov2eW (d : ℕ) (s β : ℝ) (ρ u : Euc d → ℝ) (x : Euc d) : ℝ :=
  β⁻¹ * u x + Real.sqrt (ρ x) * HRS.Whole.convFun (rieszKernel d s) (fun y => Real.sqrt (ρ y) * u y) x

section Energy

variable {s : ℝ} {ρ : Euc d → ℝ}

lemma mov2e_f_data (hρ : Mov2eRho d ρ) (v : SchwartzMap (Euc d) ℝ) :
    Measurable (fun x => v x / Real.sqrt (ρ x)) ∧
      MemLp (fun x => v x / Real.sqrt (ρ x)) 2 (HRS.Whole.withDensityReal ρ) ∧
      ∫ x, (v x / Real.sqrt (ρ x)) ^ 2 ∂(HRS.Whole.withDensityReal ρ) = ∫ x, v x ^ 2 := by
  have hcont : Continuous (fun x => v x / Real.sqrt (ρ x)) :=
    v.continuous.div hρ.data.sqrt_smooth.continuous (fun x => (hρ.psi_pos x).ne')
  have hpt : ∀ x, ρ x * (v x / Real.sqrt (ρ x)) ^ 2 = v x ^ 2 := fun x => by
    have hs := hρ.psi_pos x
    have hss := hρ.psi_sq x
    generalize Real.sqrt (ρ x) = p at hs hss ⊢
    rw [← hss]; field_simp
  refine ⟨hcont.measurable, ?_, ?_⟩
  · refine (memLp_two_iff_integrable_sq hcont.aestronglyMeasurable).2 ?_
    rw [mov2e_integrable_mu hρ]
    exact ((v.memLp 2 volume).integrable_sq).congr (Filter.Eventually.of_forall fun x => (hpt x).symm)
  · rw [mov2e_integral_mu hρ]
    exact integral_congr_ae (Filter.Eventually.of_forall hpt)

/-- The pair form as an `L²(μ)` pairing: `∬ g (ψ v)(ψ v) = ⟨K̃ f, f⟩_{L²(μ)}`, `f = v/ψ`. -/
lemma mov2e_pair_eq_mu (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (hρ : Mov2eRho d ρ)
    (v : SchwartzMap (Euc d) ℝ) :
    mov2ePairF d s (fun x => Real.sqrt (ρ x) * v x) (fun x => Real.sqrt (ρ x) * v x) =
      ∫ x, mov2eKt d s ρ (fun y => v y / Real.sqrt (ρ y)) x * (v x / Real.sqrt (ρ x))
        ∂(HRS.Whole.withDensityReal ρ) := by
  have hGB := hρ.schwartz_GB v
  rw [mov2ePairF_eq_iter hd hs0 hsd hGB hGB, mov2e_integral_mu hρ]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  have hK : mov2eKt d s ρ (fun y => v y / Real.sqrt (ρ y)) x =
      HRS.Whole.convFun (rieszKernel d s) (fun y => Real.sqrt (ρ y) * v y) x := by
    rw [mov2eKt_eq hρ]
    congr 1
    funext y
    exact mov2e_rho_div hρ v y
  dsimp only
  rw [hK]
  have := mov2e_rho_div hρ v x
  calc Real.sqrt (ρ x) * v x * HRS.Whole.convFun (rieszKernel d s) (fun y => Real.sqrt (ρ y) * v y) x
      = ρ x * (v x / Real.sqrt (ρ x)) *
          HRS.Whole.convFun (rieszKernel d s) (fun y => Real.sqrt (ρ y) * v y) x := by rw [this]
    _ = _ := by ring

/-- **Positivity of the interaction form** (`⟨f, K f⟩ ≥ 0`): `wr13c_Kmu_nonneg` for `s > 0` (all of `L²(μ)`),
`Psd.log_energy_nonneg` for `s = 0` (zero mass `⟨v, ψ⟩ = 0`). -/
theorem mov2e_pair_nonneg (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (hρ : Mov2eRho d ρ)
    (v : SchwartzMap (Euc d) ℝ) (hmean : ∫ x, Real.sqrt (ρ x) * v x = 0) :
    0 ≤ mov2ePairF d s (fun x => Real.sqrt (ρ x) * v x) (fun x => Real.sqrt (ρ x) * v x) := by
  have hd1 : 1 ≤ d := by omega
  rcases hs0.eq_or_lt with h0 | h0
  · subst h0
    have hGB := hρ.schwartz_GB v
    have key := HRS.MS.Psd.log_energy_nonneg hd1 (hGB.integrable hd1) hmean
      (mov2e_g_pair_integrable hd1 le_rfl hsd hGB hGB)
    have e : mov2ePairF d 0 (fun x => Real.sqrt (ρ x) * v x) (fun x => Real.sqrt (ρ x) * v x) =
        ∫ x, ∫ y, rieszKernel d 0 (x - y) * (Real.sqrt (ρ x) * v x) * (Real.sqrt (ρ y) * v y) := by
      unfold mov2ePairF
      rw [integral_prod _ (mov2e_g_pair_integrable hd1 le_rfl hsd hGB hGB)]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
      simp only
      ring
    rw [e]; exact key
  · obtain ⟨M, -, hM⟩ := hρ.rho_bdd
    obtain ⟨hfm, hf2, -⟩ := mov2e_f_data hρ v
    have := (HRS.MS.Wr.wr13c_Kmu_nonneg hd1 h0 hsd hρ.prob hM hfm hf2).2
    rw [mov2e_pair_eq_mu hd1 hs0 hsd hρ v]
    exact this

/-- `|⟨K̃ f, f⟩| ≤ M ‖f‖²`. -/
theorem mov2e_pair_abs_le (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (hρ : Mov2eRho d ρ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ v : SchwartzMap (Euc d) ℝ,
      |mov2ePairF d s (fun x => Real.sqrt (ρ x) * v x) (fun x => Real.sqrt (ρ x) * v x)| ≤
        M * ∫ x, v x ^ 2 := by
  have hd1 : 1 ≤ d := by omega
  have := mov2e_isProb hρ
  obtain ⟨M, hM0, hM⟩ := mov2e_kernel_L2 hd hs0 hsd hρ
  refine ⟨M, hM0, fun v => ?_⟩
  obtain ⟨hfm, hf2, hfn⟩ := mov2e_f_data hρ v
  obtain ⟨hK2, hKb⟩ := hM _ hfm hf2
  rw [mov2e_pair_eq_mu hd1 hs0 hsd hρ v]
  set f : Euc d → ℝ := fun y => v y / Real.sqrt (ρ y) with hf
  have hcs := mov2e_cs hK2 hf2
  rw [hfn] at hKb hcs
  have h1 : (∫ x, mov2eKt d s ρ f x * f x ∂(HRS.Whole.withDensityReal ρ)) ^ 2 ≤
      (M * ∫ x, v x ^ 2) ^ 2 := by
    calc _ ≤ (∫ x, (mov2eKt d s ρ f x) ^ 2 ∂(HRS.Whole.withDensityReal ρ)) * (∫ x, v x ^ 2) := hcs
      _ ≤ (M ^ 2 * ∫ x, v x ^ 2) * ∫ x, v x ^ 2 :=
          mul_le_mul_of_nonneg_right hKb (integral_nonneg fun x => sq_nonneg _)
      _ = _ := by ring
  exact abs_le_of_sq_le_sq h1 (mul_nonneg hM0 (integral_nonneg fun x => sq_nonneg _))

/-- **The sandwich `ν ‖v‖² ≤ E(v) ≤ (ν + M) ‖v‖²`** (`ν I ≤ A ≤ C I`) for `⟨v, ψ⟩ = 0`. -/
theorem mov2e_E_bounds (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (hρ : Mov2eRho d ρ) (β : ℝ)
    (hβ : 0 < β) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ v : SchwartzMap (Euc d) ℝ, ∫ x, Real.sqrt (ρ x) * v x = 0 →
      β⁻¹ * ∫ x, v x ^ 2 ≤ mov2eE d s β ρ v ∧
        mov2eE d s β ρ v ≤ (β⁻¹ + M) * ∫ x, v x ^ 2 := by
  obtain ⟨M, hM0, hM⟩ := mov2e_pair_abs_le hd hs0 hsd hρ
  refine ⟨M, hM0, fun v hmean => ⟨?_, ?_⟩⟩
  · unfold mov2eE
    linarith [mov2e_pair_nonneg hd hs0 hsd hρ v hmean]
  · unfold mov2eE
    linarith [(le_abs_self _).trans (hM v)]

/-- `E(v) ≥ 0`-type bound for the abstract reading: `E(v) ≤ (ν+M) ‖v‖²` without the mean-zero condition. -/
theorem mov2e_E_le (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (hρ : Mov2eRho d ρ) (β : ℝ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ v : SchwartzMap (Euc d) ℝ,
      |mov2eE d s β ρ v| ≤ (|β⁻¹| + M) * ∫ x, v x ^ 2 := by
  obtain ⟨M, hM0, hM⟩ := mov2e_pair_abs_le hd hs0 hsd hρ
  refine ⟨M, hM0, fun v => ?_⟩
  have hI : 0 ≤ ∫ x, v x ^ 2 := integral_nonneg fun x => sq_nonneg _
  unfold mov2eE
  calc |β⁻¹ * (∫ x, v x ^ 2) + mov2ePairF d s (fun x => Real.sqrt (ρ x) * v x) (fun x => Real.sqrt (ρ x) * v x)|
      ≤ |β⁻¹ * (∫ x, v x ^ 2)| + |mov2ePairF d s (fun x => Real.sqrt (ρ x) * v x) (fun x => Real.sqrt (ρ x) * v x)| :=
        abs_add_le _ _
    _ ≤ |β⁻¹| * (∫ x, v x ^ 2) + M * (∫ x, v x ^ 2) := by
        refine add_le_add ?_ (hM v)
        rw [abs_mul, abs_of_nonneg hI]
    _ = _ := by ring

/-- **Polarisation of the energy**: `E(u + δ) = E(u) + 2 ⟨δ, W_u⟩ + E(δ)` for Schwartz `u, δ`, with
`W_u = ν u + ψ (g * (ψ u))` (`mov2eW`). -/
theorem mov2e_E_expand (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (hρ : Mov2eRho d ρ) (β : ℝ)
    (u δ : SchwartzMap (Euc d) ℝ) :
    mov2eE d s β ρ (fun x => u x + δ x) =
      mov2eE d s β ρ u + 2 * (∫ x, δ x * mov2eW d s β ρ u x) + mov2eE d s β ρ δ := by
  have hu := hρ.schwartz_GB u
  have hδ := hρ.schwartz_GB δ
  have hsum : (fun x => Real.sqrt (ρ x) * (u x + δ x)) =
      fun x => Real.sqrt (ρ x) * u x + Real.sqrt (ρ x) * δ x := by
    funext x; ring
  have i1 : Integrable (fun x => u x * u x) := mov2e_schw_int u u
  have i2 : Integrable (fun x => u x * δ x) := mov2e_schw_int u δ
  have i3 : Integrable (fun x => δ x * δ x) := mov2e_schw_int δ δ
  have hsq : ∫ x, (u x + δ x) ^ 2 =
      (∫ x, u x ^ 2) + 2 * (∫ x, u x * δ x) + ∫ x, δ x ^ 2 := by
    have e : (fun x => (u x + δ x) ^ 2) = fun x => u x ^ 2 + 2 * (u x * δ x) + δ x ^ 2 := by
      funext x; ring
    have j1 : Integrable (fun x => u x ^ 2) := i1.congr (Filter.Eventually.of_forall fun x => by ring)
    have j3 : Integrable (fun x => δ x ^ 2) := i3.congr (Filter.Eventually.of_forall fun x => by ring)
    have j2 : Integrable (fun x => 2 * (u x * δ x)) := i2.const_mul 2
    have j12 : Integrable (fun x => u x ^ 2 + 2 * (u x * δ x)) := j1.add j2
    rw [e, integral_add j12 j3, integral_add j1 j2, integral_const_mul]
  have hpair : mov2ePairF d s (fun x => Real.sqrt (ρ x) * (u x + δ x))
      (fun x => Real.sqrt (ρ x) * (u x + δ x)) =
      mov2ePairF d s (fun x => Real.sqrt (ρ x) * u x) (fun x => Real.sqrt (ρ x) * u x) +
      2 * mov2ePairF d s (fun x => Real.sqrt (ρ x) * δ x) (fun x => Real.sqrt (ρ x) * u x) +
      mov2ePairF d s (fun x => Real.sqrt (ρ x) * δ x) (fun x => Real.sqrt (ρ x) * δ x) := by
    rw [hsum, mov2ePairF_add_left hd hs0 hsd hu hδ (hu.add hδ),
      mov2ePairF_add_right hd hs0 hsd hu hu hδ, mov2ePairF_add_right hd hs0 hsd hδ hu hδ,
      mov2ePairF_symm (h₁ := fun x => Real.sqrt (ρ x) * u x) (h₂ := fun x => Real.sqrt (ρ x) * δ x)]
    ring
  have hW : ∫ x, δ x * mov2eW d s β ρ u x =
      β⁻¹ * (∫ x, u x * δ x) +
        mov2ePairF d s (fun x => Real.sqrt (ρ x) * δ x) (fun x => Real.sqrt (ρ x) * u x) := by
    rw [mov2ePairF_eq_iter hd hs0 hsd hδ hu]
    have k1 : Integrable (fun x => β⁻¹ * (u x * δ x)) := i2.const_mul _
    have k2 := mov2e_conv_mul_integrable hd hs0 hsd hδ hu
    have e : (fun x => δ x * mov2eW d s β ρ u x) = fun x =>
        β⁻¹ * (u x * δ x) + Real.sqrt (ρ x) * δ x *
          HRS.Whole.convFun (rieszKernel d s) (fun y => Real.sqrt (ρ y) * u y) x := by
      funext x; unfold mov2eW; ring
    rw [e, integral_add k1 k2, integral_const_mul]
  unfold mov2eE
  rw [hpair, hsq, hW]
  ring

end Energy

end HRS.MS.MovDec

end
