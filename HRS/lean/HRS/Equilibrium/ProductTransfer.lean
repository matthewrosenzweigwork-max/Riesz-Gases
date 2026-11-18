/-
# HRS.Equilibrium.ProductTransfer — Lemma 4.4 (`M:R:lem:product-transfer`)

`product_moment_transfer_proof` restates `HRS.product_moment_transfer` verbatim (the statement lives
in `PoleCavity.lean`, whose inputs, Proposition 5.5 and the exchangeability of the cavity, are
downstream of that file).  Proof route (TeX lines 4201-4208): Hölder interpolation
`J_{pb} ≤ J_b^{2-p} J_{2b}^{p-1}` (log-convexity of `b ↦ log K_{N,b}`), the two-sided pressure bound
of Proposition 5.5 (`perturbed_pressure`), `Q_{n,b}` versus the cavity (bounded one-body tilt) and the
pole tilt (Jensen and the one-particle density bound of Lemma 4.1).
-/
import HRS.Energy.PressureProof
import HRS.Equilibrium.MarginalPole

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

noncomputable section

namespace HRS

namespace ProdTransfer

variable {d : ℕ} {s : ℝ}

open HRS.External HRS.PoleCavityAux HRS.MarginalAux

/-! ### Constant shifts do not change a tilted law -/

theorem tiltMeasure_add_const {α : Type*} [MeasurableSpace α] (P : Measure α) [IsProbabilityMeasure P]
    (w : α → ℝ) (hw : Measurable w) (k : ℝ) :
    tiltMeasure P (fun a => w a + k) = tiltMeasure P w := by
  rw [Glue.tiltMeasure_eq_tilted_of_measurable P (fun a => w a + k) (hw.add_const k),
    Glue.tiltMeasure_eq_tilted_of_measurable P _ hw]
  exact Calib.tilted_add_const P w k

theorem pairSum_add_const (g : Torus d → ℝ) (c : ℝ) {n : ℕ} (Y : Config d n) :
    pairSum (fun z => g z + c) Y = pairSum g Y +
      c * ∑ i : Fin n, ((Finset.univ.filter (fun j : Fin n => i < j)).card : ℝ) := by
  unfold pairSum
  simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ => by ring

theorem critCavity_eq (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (c β : ℝ) {ρ : Torus d → ℝ}
    (hρ : SmoothPosDensity ρ) (N : ℕ) :
    critCavity d s c β ρ N =
      cavityLaw (periodicRiesz d s) (withDensityReal ρ) (N - 1) (β / N) β := by
  have hμ := isProbabilityMeasure_mu hρ
  obtain ⟨B, Cc, hB, hK⟩ := kerData_periodicRiesz hd hs0 hsd hρ
  unfold critCavity cavityLaw
  have hg := hK.meas
  have hconv : ∀ y, convMeasure (gPlus d s c) (withDensityReal ρ) y =
      convMeasure (periodicRiesz d s) (withDensityReal ρ) y + c := by
    intro y
    unfold convMeasure gPlus
    rw [integral_add (hK.int y) (integrable_const _)]
    simp
  rw [← tiltMeasure_add_const _ _ (measurable_cavityW hg (withDensityReal ρ) (N - 1) (β / N) β)
    (-(β / N) * (c * ∑ i : Fin (N - 1), ((Finset.univ.filter (fun j : Fin (N - 1) => i < j)).card : ℝ))
      + β * ((N - 1 : ℕ) * c))]
  congr 1
  funext Y
  have : pairSum (gPlus d s c) Y = pairSum (fun z => periodicRiesz d s z + c) Y := rfl
  rw [this, pairSum_add_const]
  simp only [hconv, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  ring

/-! ### Hölder step -/

theorem holder3 {α : Type*} [MeasurableSpace α] (ν : Measure α) (Yf w : α → ℝ≥0∞)
    (hY : Measurable Yf) (hw : Measurable w) (q : ℝ) (hq : 2 ≤ q) :
    ∫⁻ a, Yf a ^ 2 * w a ∂ν ≤ (∫⁻ a, Yf a ^ (2 * q) ∂ν) ^ (1 / q) *
      (∫⁻ a, w a ∂ν) ^ ((q - 2) / q) * (∫⁻ a, w a ^ 2 ∂ν) ^ (1 / q) := by
  have hq0 : 0 < q := by linarith
  have hpt : ∀ a, Yf a ^ 2 * w a = (Yf a ^ (2 * q)) ^ (1 / q) * w a ^ ((q - 2) / q) *
      (w a ^ 2) ^ (1 / q) := by
    intro a
    have h1 : (Yf a ^ (2 * q)) ^ (1 / q) = Yf a ^ 2 := by
      rw [← ENNReal.rpow_mul]
      have : 2 * q * (1 / q) = ((2 : ℕ) : ℝ) := by field_simp; norm_num
      rw [this, ENNReal.rpow_natCast]
    have h2 : (w a ^ 2) ^ (1 / q) = w a ^ (2 / q) := by
      rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
      congr 1; push_cast; ring
    rw [h1, h2, mul_assoc, ← ENNReal.rpow_add_of_nonneg _ _ (by
      apply div_nonneg <;> linarith) (by positivity)]
    have : (q - 2) / q + 2 / q = 1 := by field_simp; ring
    rw [this, ENNReal.rpow_one]
  have key := ENNReal.lintegral_prod_norm_pow_le (μ := ν) (Finset.univ : Finset (Fin 3))
    (f := ![fun a => Yf a ^ (2 * q), w, fun a => w a ^ 2])
    (p := ![1 / q, (q - 2) / q, 1 / q]) (by
      intro i _
      fin_cases i
      · exact (hY.pow_const _).aemeasurable
      · exact hw.aemeasurable
      · exact (hw.pow_const _).aemeasurable) (by
      simp [Fin.sum_univ_three]
      field_simp; ring) (by
      intro i _
      fin_cases i
      · simp; positivity
      · simp; apply div_nonneg <;> linarith
      · simp; positivity)
  simp only [Fin.prod_univ_three] at key
  simp at key
  calc ∫⁻ a, Yf a ^ 2 * w a ∂ν = ∫⁻ a, (Yf a ^ (2 * q)) ^ (1 / q) * w a ^ ((q - 2) / q) *
      (w a ^ 2) ^ (1 / q) ∂ν := lintegral_congr hpt
    _ ≤ _ := by simpa only [one_div] using key

theorem AL {α : Type*} [MeasurableSpace α] (ν : Measure α) (φ : α → ℝ) (hφ : Measurable φ)
    (A : ℝ) (hZlo : ENNReal.ofReal (Real.exp (-A)) ≤ ∫⁻ a, ENNReal.ofReal (Real.exp (φ a)) ∂ν)
    (hZhi : ∫⁻ a, ENNReal.ofReal (Real.exp (φ a)) ∂ν ≤ ENNReal.ofReal (Real.exp A))
    (hZ2 : ∫⁻ a, ENNReal.ofReal (Real.exp (2 * φ a)) ∂ν ≤ ENNReal.ofReal (Real.exp A))
    (q : ℝ) (hq : 2 ≤ q) (Y : α → ℝ) (hY : Measurable Y) :
    eLpNorm Y 2 ((∫⁻ a, ENNReal.ofReal (Real.exp (φ a)) ∂ν)⁻¹ •
        ν.withDensity fun a => ENNReal.ofReal (Real.exp (φ a))) ≤
      ENNReal.ofReal (Real.exp (3 * A / (2 * q))) * eLpNorm Y (ENNReal.ofReal (2 * q)) ν := by
  have hq0 : 0 < q := by linarith
  set w : α → ℝ≥0∞ := fun a => ENNReal.ofReal (Real.exp (φ a)) with hw
  have hwm : Measurable w := ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp hφ)
  set Z : ℝ≥0∞ := ∫⁻ a, w a ∂ν with hZ
  have hZ0 : Z ≠ 0 := by
    intro h; rw [h] at hZlo
    exact absurd (le_antisymm hZlo bot_le ▸ (ENNReal.ofReal_pos.2 (Real.exp_pos _))) (lt_irrefl _)
  have hZt : Z ≠ ∞ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hZhi
  have hYm : Measurable fun a => ‖Y a‖ₑ := hY.enorm
  have h1 : ∫⁻ a, ‖Y a‖ₑ ^ (2 : ℝ≥0∞).toReal ∂((Z)⁻¹ • ν.withDensity w) =
      Z⁻¹ * ∫⁻ a, ‖Y a‖ₑ ^ 2 * w a ∂ν := by
    rw [lintegral_smul_measure, lintegral_withDensity_eq_lintegral_mul _ hwm
      ((hYm.pow_const _))]
    simp [mul_comm]
  have hw2 : ∀ a, w a ^ 2 = ENNReal.ofReal (Real.exp (2 * φ a)) := by
    intro a
    simp only [hw]
    rw [← ENNReal.ofReal_pow (Real.exp_pos _).le, ← Real.exp_nat_mul]
    norm_num
  have hH := holder3 ν (fun a => ‖Y a‖ₑ) w hYm hwm q hq
  simp_rw [hw2] at hH
  set M := ∫⁻ a, ‖Y a‖ₑ ^ (2 * q) ∂ν with hM
  set Z2 := ∫⁻ a, ENNReal.ofReal (Real.exp (2 * φ a)) ∂ν with hZ2def
  have hcancel : Z⁻¹ * Z ^ ((q - 2) / q) = (Z⁻¹) ^ (2 / q) := by
    have : Z⁻¹ = Z ^ (-1 : ℝ) := (ENNReal.rpow_neg_one Z).symm
    rw [this, ← ENNReal.rpow_add _ _ hZ0 hZt, ← ENNReal.rpow_mul]
    congr 1
    field_simp; ring
  have hZinv : Z⁻¹ ≤ ENNReal.ofReal (Real.exp A) := by
    calc Z⁻¹ ≤ (ENNReal.ofReal (Real.exp (-A)))⁻¹ := ENNReal.inv_le_inv.2 hZlo
      _ = ENNReal.ofReal (Real.exp A) := by
        rw [← ENNReal.ofReal_inv_of_pos (Real.exp_pos _), ← Real.exp_neg]; simp
  have h2 : Z⁻¹ * ∫⁻ a, ‖Y a‖ₑ ^ 2 * w a ∂ν ≤
      ENNReal.ofReal (Real.exp (3 * A / q)) * M ^ (1 / q) := by
    calc Z⁻¹ * ∫⁻ a, ‖Y a‖ₑ ^ 2 * w a ∂ν ≤ Z⁻¹ * (M ^ (1 / q) * Z ^ ((q - 2) / q) * Z2 ^ (1 / q)) :=
          mul_le_mul' le_rfl hH
      _ = (Z⁻¹ * Z ^ ((q - 2) / q)) * M ^ (1 / q) * Z2 ^ (1 / q) := by ring
      _ = (Z⁻¹) ^ (2 / q) * Z2 ^ (1 / q) * M ^ (1 / q) := by rw [hcancel]; ring
      _ ≤ (ENNReal.ofReal (Real.exp A)) ^ (2 / q) * (ENNReal.ofReal (Real.exp A)) ^ (1 / q) *
            M ^ (1 / q) := by
          gcongr
      _ = ENNReal.ofReal (Real.exp (3 * A / q)) * M ^ (1 / q) := by
          congr 1
          rw [← ENNReal.rpow_add_of_nonneg _ _ (by positivity) (by positivity),
            ENNReal.ofReal_rpow_of_pos (Real.exp_pos _), ← Real.exp_mul]
          congr 2
          field_simp; ring
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hY.aestronglyMeasurable, h1]
  have hMe : M ^ (1 / q) = (eLpNorm Y (ENNReal.ofReal (2 * q)) ν) ^ 2 := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by simp; positivity) ENNReal.ofReal_ne_top
      hY.aestronglyMeasurable,
      ENNReal.toReal_ofReal (by positivity), ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    congr 1
    push_cast
    field_simp
  have h3 : (Z⁻¹ * ∫⁻ a, ‖Y a‖ₑ ^ 2 * w a ∂ν) ^ (1 / (2 : ℝ≥0∞).toReal) ≤
      (ENNReal.ofReal (Real.exp (3 * A / q)) * (eLpNorm Y (ENNReal.ofReal (2 * q)) ν) ^ 2) ^
        (1 / (2 : ℝ≥0∞).toReal) := by
    refine ENNReal.rpow_le_rpow ?_ (by positivity)
    rw [← hMe]; exact h2
  refine h3.trans ?_
  have h2t : (2 : ℝ≥0∞).toReal = 2 := by simp
  rw [h2t, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ENNReal.ofReal_rpow_of_pos (Real.exp_pos _),
    ← Real.exp_mul]
  refine mul_le_mul' (le_of_eq ?_) (le_of_eq ?_)
  · congr 2; field_simp
  · rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]; norm_num

/-! ### Comparison of tilted laws -/

theorem tilt_le_bdd {α : Type*} [MeasurableSpace α] (P : Measure α) (w w' : α → ℝ)
    (hw : Measurable w) (hw' : Measurable w') (U : ℝ) (hU : ∀ a, |w a - w' a| ≤ U)
    (hZ0 : ∫⁻ a, ENNReal.ofReal (Real.exp (w' a)) ∂P ≠ 0)
    (hZt : ∫⁻ a, ENNReal.ofReal (Real.exp (w' a)) ∂P ≠ ∞) :
    tiltMeasure P w ≤ ENNReal.ofReal (Real.exp (2 * U)) • tiltMeasure P w' := by
  set Z' := ∫⁻ a, ENNReal.ofReal (Real.exp (w' a)) ∂P with hZ'
  set Z := ∫⁻ a, ENNReal.ofReal (Real.exp (w a)) ∂P with hZ
  have hpt1 : ∀ a, ENNReal.ofReal (Real.exp (w a)) ≤
      ENNReal.ofReal (Real.exp U) * ENNReal.ofReal (Real.exp (w' a)) := by
    intro a
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [← Real.exp_add]
    refine Real.exp_le_exp.2 ?_
    have := (abs_le.1 (hU a)).2; linarith
  have hpt2 : ∀ a, ENNReal.ofReal (Real.exp (-U)) * ENNReal.ofReal (Real.exp (w' a)) ≤
      ENNReal.ofReal (Real.exp (w a)) := by
    intro a
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [← Real.exp_add]
    refine Real.exp_le_exp.2 ?_
    have := (abs_le.1 (hU a)).1; linarith
  have hZlo : ENNReal.ofReal (Real.exp (-U)) * Z' ≤ Z := by
    rw [hZ', ← lintegral_const_mul (f := fun a => ENNReal.ofReal (Real.exp (w' a))) _
      (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp hw'))]
    exact lintegral_mono hpt2
  have hZinv : Z⁻¹ ≤ ENNReal.ofReal (Real.exp U) * Z'⁻¹ := by
    calc Z⁻¹ ≤ (ENNReal.ofReal (Real.exp (-U)) * Z')⁻¹ := ENNReal.inv_le_inv.2 hZlo
      _ = ENNReal.ofReal (Real.exp U) * Z'⁻¹ := by
        rw [ENNReal.mul_inv (Or.inr hZt) (Or.inr hZ0)]
        rw [← ENNReal.ofReal_inv_of_pos (Real.exp_pos _), ← Real.exp_neg]; simp
  refine Measure.le_iff.2 fun A hA => ?_
  simp only [tiltMeasure, Measure.smul_apply, withDensity_apply _ hA, smul_eq_mul]
  have hint : ∫⁻ a in A, ENNReal.ofReal (Real.exp (w a)) ∂P ≤
      ENNReal.ofReal (Real.exp U) * ∫⁻ a in A, ENNReal.ofReal (Real.exp (w' a)) ∂P := by
    rw [← lintegral_const_mul (f := fun a => ENNReal.ofReal (Real.exp (w' a))) _
      (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp hw'))]
    exact setLIntegral_mono' hA fun a _ => hpt1 a
  calc Z⁻¹ * ∫⁻ a in A, ENNReal.ofReal (Real.exp (w a)) ∂P
      ≤ (ENNReal.ofReal (Real.exp U) * Z'⁻¹) *
          (ENNReal.ofReal (Real.exp U) * ∫⁻ a in A, ENNReal.ofReal (Real.exp (w' a)) ∂P) :=
        mul_le_mul' hZinv hint
    _ = ENNReal.ofReal (Real.exp (2 * U)) * (Z'⁻¹ * ∫⁻ a in A, ENNReal.ofReal (Real.exp (w' a)) ∂P) := by
        have : ENNReal.ofReal (Real.exp U) * ENNReal.ofReal (Real.exp U) =
            ENNReal.ofReal (Real.exp (2 * U)) := by
          rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]; congr 2; ring
        rw [← this]; ring

theorem tilt_le_of_nonpos {α : Type*} [MeasurableSpace α] (P : Measure α) (v : α → ℝ)
    (hv : Measurable v) (hv0 : ∀ a, v a ≤ 0) (A : ℝ)
    (hZ : ENNReal.ofReal (Real.exp (-A)) ≤ ∫⁻ a, ENNReal.ofReal (Real.exp (v a)) ∂P) :
    tiltMeasure P v ≤ ENNReal.ofReal (Real.exp A) • P := by
  refine Measure.le_iff.2 fun S hS => ?_
  simp only [tiltMeasure, Measure.smul_apply, withDensity_apply _ hS, smul_eq_mul]
  have hinv : (∫⁻ a, ENNReal.ofReal (Real.exp (v a)) ∂P)⁻¹ ≤ ENNReal.ofReal (Real.exp A) := by
    calc _ ≤ (ENNReal.ofReal (Real.exp (-A)))⁻¹ := ENNReal.inv_le_inv.2 hZ
      _ = ENNReal.ofReal (Real.exp A) := by
        rw [← ENNReal.ofReal_inv_of_pos (Real.exp_pos _), ← Real.exp_neg]; simp
  have : ∫⁻ a in S, ENNReal.ofReal (Real.exp (v a)) ∂P ≤ P S := by
    calc _ ≤ ∫⁻ a in S, 1 ∂P := lintegral_mono fun a => by
          simpa using Real.exp_le_one_iff.2 (hv0 a)
      _ = P S := by simp
  exact mul_le_mul' hinv this

/-! ### Pressure bounds (Proposition 5.5 at `θ = 0`) -/

theorem rowOK_kernel (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {ρ : Torus d → ℝ}
    (hρ : SmoothPosDensity ρ) :
    RowOK (withDensityReal ρ) (fun x y => periodicRiesz d s (x - y)) := by
  obtain ⟨B, hB⟩ := periodicRiesz_ge (d := d) hd hs0 hsd
  obtain ⟨Λ, hΛ0, hΛ⟩ := exists_density_bound hρ
  have hw : ∀ z : Torus d, z ≠ 0 → 1 ≤ periodicRiesz d s z + (B + 1) :=
    fun z _ => by linarith [hB z]
  exact (rowOK_g_h (by omega) s hs0 hsd (B + 1) hw 0 hΛ0.le hΛ (h := fun _ _ => 0)
    measurable_const (fun x y => by simp)).1

theorem measurable_energy (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {ρ : Torus d → ℝ}
    (hρ : SmoothPosDensity ρ) {N : ℕ} :
    Measurable (fun X : Config d N =>
      modulatedEnergyKernel (periodicRiesz d s) X (withDensityReal ρ)) := by
  haveI := isProbabilityMeasure_mu hρ
  exact measurable_modulatedEnergy (rowOK_kernel hd hs0 hsd hρ)

/-- The normaliser `∫⁻ e^{-b N F_N}` at `N ≥ 2` is `e^{± C N δ_N}`, uniformly for `b ∈ [β/2, 2β]`. -/
theorem pressure_N2 (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (β : ℝ) (hβ : 0 < β)
    {ρ : Torus d → ℝ} (hρ : SmoothPosDensity ρ) :
    ∃ C : ℝ, ∀ N : ℕ, 2 ≤ N → ∀ b ∈ Set.Icc (β / 2) (2 * β),
      ENNReal.ofReal (Real.exp (-(C * N * deltaN d s N))) ≤
          ∫⁻ X : Config d N, ENNReal.ofReal (Real.exp (-b * N *
            modulatedEnergyKernel (periodicRiesz d s) X (withDensityReal ρ)))
            ∂(Measure.pi fun _ => withDensityReal ρ) ∧
        ∫⁻ X : Config d N, ENNReal.ofReal (Real.exp (-b * N *
            modulatedEnergyKernel (periodicRiesz d s) X (withDensityReal ρ)))
            ∂(Measure.pi fun _ => withDensityReal ρ) ≤
          ENNReal.ofReal (Real.exp (C * N * deltaN d s N)) := by
  obtain ⟨B, hB⟩ := periodicRiesz_ge (d := d) hd hs0 hsd
  have hw : ∀ z : Torus d, z ≠ 0 → 1 ≤ periodicRiesz d s z + (B + 1) :=
    fun z _ => by linarith [hB z]
  obtain ⟨x0, -, hx0⟩ := isCompact_univ.exists_isMinOn Set.univ_nonempty
    (continuous_of_smoothPos hρ).continuousOn
  have hc₀ : 0 < ρ x0 := hρ.pos x0
  have hlow : ∀ x, ρ x0 ≤ ρ x := fun x => isMinOn_iff.1 hx0 x (Set.mem_univ x)
  obtain ⟨θ₀, θ₁, C, hθ₀, hθ₁, H⟩ := perturbed_pressure (by omega) s hs0 hsd (B + 1) hw (β / 2)
    (2 * β) (by positivity) (ρ x0) hc₀ (fun k => Torus.cbNorm k ρ) 0
  refine ⟨C, fun N hN b hb => ?_⟩
  have := (H ρ hρ.density hρ.smooth hlow (fun k => le_rfl) (fun _ _ => 0) measurable_const
    (fun _ _ => rfl) (fun x y => by simp) N hN b hb).1 0 (by simp [hθ₀.le])
  simpa [modulatedEnergyKernel] using this

/-- For `N = 1` the energy is bounded, so the normaliser is `e^{O(1)}`. -/
theorem pressure_N1 (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (β : ℝ) (hβ : 0 < β)
    {ρ : Torus d → ℝ} (hρ : SmoothPosDensity ρ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ b ∈ Set.Icc (β / 2) (2 * β),
      ENNReal.ofReal (Real.exp (-C)) ≤
          ∫⁻ X : Config d 1, ENNReal.ofReal (Real.exp (-b * (1 : ℕ) *
            modulatedEnergyKernel (periodicRiesz d s) X (withDensityReal ρ)))
            ∂(Measure.pi fun _ => withDensityReal ρ) ∧
        ∫⁻ X : Config d 1, ENNReal.ofReal (Real.exp (-b * (1 : ℕ) *
            modulatedEnergyKernel (periodicRiesz d s) X (withDensityReal ρ)))
            ∂(Measure.pi fun _ => withDensityReal ρ) ≤
          ENNReal.ofReal (Real.exp C) := by
  haveI := isProbabilityMeasure_mu hρ
  obtain ⟨B, Cc, hB, hK⟩ := kerData_periodicRiesz hd hs0 hsd hρ
  have hCc := hK.Cc_nonneg
  have hE : ∀ X : Config d 1, |modulatedEnergyKernel (periodicRiesz d s) X (withDensityReal ρ)| ≤
      3 * Cc := by
    intro X
    unfold modulatedEnergyKernel modulatedEnergy
    have h0 : Finset.univ.erase (0 : Fin 1) = ∅ := by
      ext j; simp [Subsingleton.elim j 0]
    have hsum : ∀ i : Fin 1, Finset.univ.erase i = ∅ := fun i => by
      rw [Subsingleton.elim i 0]; exact h0
    simp only [hsum, Finset.sum_empty, mul_zero, zero_sub, Nat.cast_one, div_one, one_div, inv_one,
      one_mul, Finset.univ_unique, Finset.sum_singleton, Finset.erase_singleton]
    have h1 : |∫ y, periodicRiesz d s (X default - y) ∂(withDensityReal ρ)| ≤ Cc := hK.conv _
    have h2 : |∫ x, ∫ y, periodicRiesz d s (x - y) ∂(withDensityReal ρ) ∂(withDensityReal ρ)| ≤ Cc := by
      have := norm_integral_le_of_norm_le_const (μ := withDensityReal ρ)
        (f := fun x => ∫ y, periodicRiesz d s (x - y) ∂(withDensityReal ρ)) (C := Cc)
        (Filter.Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hK.conv x)
      simpa using this
    rw [abs_le] at h1 h2 ⊢
    constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
  refine ⟨6 * β * Cc, by positivity, fun b hb => ?_⟩
  have hb0 : 0 ≤ b := by linarith [hb.1]
  have hbd : ∀ X : Config d 1, |-b * ((1 : ℕ) : ℝ) *
      modulatedEnergyKernel (periodicRiesz d s) X (withDensityReal ρ)| ≤ 6 * β * Cc := by
    intro X
    have := hE X
    calc |-b * ((1 : ℕ) : ℝ) * modulatedEnergyKernel (periodicRiesz d s) X (withDensityReal ρ)|
        = b * |modulatedEnergyKernel (periodicRiesz d s) X (withDensityReal ρ)| := by
          simp [abs_mul, abs_of_nonneg hb0]
      _ ≤ (2 * β) * (3 * Cc) := mul_le_mul hb.2 this (abs_nonneg _) (by positivity)
      _ = 6 * β * Cc := by ring
  constructor
  · calc ENNReal.ofReal (Real.exp (-(6 * β * Cc)))
        = ∫⁻ _ : Config d 1, ENNReal.ofReal (Real.exp (-(6 * β * Cc)))
            ∂(Measure.pi fun _ => withDensityReal ρ) := by simp
      _ ≤ _ := lintegral_mono fun X => ENNReal.ofReal_le_ofReal
          (Real.exp_le_exp.2 (by linarith [abs_le.1 (hbd X)]))
  · calc _ ≤ ∫⁻ _ : Config d 1, ENNReal.ofReal (Real.exp (6 * β * Cc))
            ∂(Measure.pi fun _ => withDensityReal ρ) :=
          lintegral_mono fun X => ENNReal.ofReal_le_ofReal
            (Real.exp_le_exp.2 (by linarith [abs_le.1 (hbd X)]))
      _ = _ := by simp

/-- The normaliser `J_{N,b} = ∫⁻ e^{-b N F_N} dμ^{⊗N}`. -/
def Jint (d : ℕ) (s : ℝ) (N : ℕ) (b : ℝ) (μ : Measure (Torus d)) : ℝ≥0∞ :=
  ∫⁻ X : Config d N, ENNReal.ofReal (Real.exp (-b * N *
    modulatedEnergyKernel (periodicRiesz d s) X μ)) ∂(Measure.pi fun _ => μ)

theorem pressure_all (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (β : ℝ) (hβ : 0 < β)
    {ρ : Torus d → ℝ} (hρ : SmoothPosDensity ρ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 1 ≤ N → ∀ b ∈ Set.Icc (β / 2) (2 * β),
      ENNReal.ofReal (Real.exp (-(C * N * deltaN d s N))) ≤ Jint d s N b (withDensityReal ρ) ∧
        Jint d s N b (withDensityReal ρ) ≤ ENNReal.ofReal (Real.exp (C * N * deltaN d s N)) := by
  obtain ⟨C2, h2⟩ := pressure_N2 hd hs0 hsd β hβ hρ
  obtain ⟨C1, hC1, h1⟩ := pressure_N1 hd hs0 hsd β hβ hρ
  refine ⟨max (max C2 0) C1, (le_max_left _ _).trans' (le_max_right _ _), fun N hN b hb => ?_⟩
  have hNd := one_le_mul_deltaN (d := d) hs0 N hN
  have hCnn : 0 ≤ max (max C2 0) C1 := (le_max_right C2 0).trans ((le_max_left _ _))
  have hCNd : max (max C2 0) C1 * N * deltaN d s N = max (max C2 0) C1 * ((N : ℝ) * deltaN d s N) := by ring
  rcases Nat.lt_or_ge N 2 with h | h
  · have hN1 : N = 1 := by omega
    subst hN1
    obtain ⟨hl, hu⟩ := h1 b hb
    have hCle : C1 ≤ max (max C2 0) C1 * (((1 : ℕ) : ℝ) * deltaN d s 1) :=
      (le_max_right _ _).trans (by nlinarith [le_max_right (max C2 0) C1])
    unfold Jint
    refine ⟨hl.trans' (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)),
      hu.trans (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_))⟩
    · rw [hCNd]; linarith
    · rw [hCNd]; linarith
  · obtain ⟨hl, hu⟩ := h2 N h b hb
    have hC2le : C2 ≤ max (max C2 0) C1 := (le_max_left _ _).trans (le_max_left _ _)
    have hmono : C2 * N * deltaN d s N ≤ max (max C2 0) C1 * N * deltaN d s N := by
      have : 0 ≤ (N : ℝ) * deltaN d s N := by linarith
      nlinarith
    unfold Jint
    exact ⟨hl.trans' (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 (by linarith))),
      hu.trans (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 hmono))⟩

theorem eLp_gibbs_le (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (β : ℝ) (hβ : 0 < β)
    {ρ : Torus d → ℝ} (hρ : SmoothPosDensity ρ) {C : ℝ}
    (hC : ∀ N : ℕ, 1 ≤ N → ∀ b ∈ Set.Icc (β / 2) (2 * β),
      ENNReal.ofReal (Real.exp (-(C * N * deltaN d s N))) ≤ Jint d s N b (withDensityReal ρ) ∧
        Jint d s N b (withDensityReal ρ) ≤ ENNReal.ofReal (Real.exp (C * N * deltaN d s N)))
    (N : ℕ) (hN : 1 ≤ N) (b : ℝ) (hb : b ∈ Set.Icc (β / 2) β) (q : ℝ) (hq : 2 ≤ q)
    (Y : Config d N → ℝ) (hY : Measurable Y) :
    eLpNorm Y 2 (modulatedGibbs (periodicRiesz d s) N b (withDensityReal ρ)) ≤
      ENNReal.ofReal (Real.exp (3 * (C * N * deltaN d s N) / (2 * q))) *
        eLpNorm Y (ENNReal.ofReal (2 * q)) (Measure.pi fun _ : Fin N => withDensityReal ρ) := by
  haveI := isProbabilityMeasure_mu hρ
  set μ := withDensityReal ρ with hμ
  set E : Config d N → ℝ := fun X => modulatedEnergyKernel (periodicRiesz d s) X μ with hE
  have hEm : Measurable E := measurable_energy hd hs0 hsd hρ
  have hφ : Measurable fun X : Config d N => -b * N * E X := measurable_const.mul hEm
  have hb1 : b ∈ Set.Icc (β / 2) (2 * β) := ⟨hb.1, by linarith [hb.2]⟩
  have hb2 : 2 * b ∈ Set.Icc (β / 2) (2 * β) := ⟨by linarith [hb.1], by linarith [hb.2]⟩
  obtain ⟨hlo, hhi⟩ := hC N hN b hb1
  obtain ⟨-, hhi2⟩ := hC N hN (2 * b) hb2
  have hZ2 : ∫⁻ X : Config d N, ENNReal.ofReal (Real.exp (2 * (-b * N * E X)))
      ∂(Measure.pi fun _ => μ) ≤ ENNReal.ofReal (Real.exp (C * N * deltaN d s N)) := by
    refine le_trans (le_of_eq ?_) hhi2
    unfold Jint
    refine lintegral_congr fun X => ?_
    have : 2 * (-b * N * E X) = -(2 * b) * N *
        modulatedEnergyKernel (periodicRiesz d s) X μ := by simp only [hE]; ring
    rw [this]
  have hfin : ∫⁻ X : Config d N, ENNReal.ofReal (Real.exp (-b * N * E X))
      ∂(Measure.pi fun _ => μ) ≠ ∞ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hhi
  have hint : Integrable (fun X : Config d N => Real.exp (-b * N * E X)) (Measure.pi fun _ => μ) :=
    ⟨(Real.measurable_exp.comp hφ).aestronglyMeasurable,
      (hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun X => (Real.exp_pos _).le)).2
        (lt_top_iff_ne_top.2 hfin)⟩
  have hmod : modulatedGibbs (periodicRiesz d s) N b μ =
      (∫⁻ X : Config d N, ENNReal.ofReal (Real.exp (-b * N * E X)) ∂(Measure.pi fun _ => μ))⁻¹ •
        (Measure.pi fun _ : Fin N => μ).withDensity fun X =>
          ENNReal.ofReal (Real.exp (-b * N * E X)) := by
    unfold modulatedGibbs gibbsNormalizer
    rw [ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall fun X => (Real.exp_pos _).le)]
  rw [hmod]
  exact AL (Measure.pi fun _ : Fin N => μ) (fun X => -b * N * E X) hφ (C * N * deltaN d s N)
    hlo hhi hZ2 q hq Y hY


/-! ### Pole law versus Gibbs law -/

theorem measure_smul_le' {α : Type*} [MeasurableSpace α] {μ ν : Measure α} (c : ℝ≥0∞) (h : μ ≤ ν) :
    c • μ ≤ c • ν :=
  Measure.le_iff'.2 fun S => by
    simp only [Measure.smul_apply, smul_eq_mul]
    exact mul_le_mul' le_rfl (h S)

theorem coord_mean_le (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (c β : ℝ) (hβ : 0 < β)
    {ρ : Torus d → ℝ} (hρ : SmoothPosDensity ρ) (hc : ∀ z, 0 ≤ periodicRiesz d s z + c) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ N : ℕ, 2 ≤ N → ∀ x : Torus d, ∀ i : Fin (N - 1),
      Integrable (fun Y : Config d (N - 1) => gPlus d s c (x - Y i)) (critCavity d s c β ρ N) ∧
        ∫ Y, gPlus d s c (x - Y i) ∂(critCavity d s c β ρ N) ≤ A := by
  have hμ := isProbabilityMeasure_mu hρ
  obtain ⟨C1, hC1, hmarg⟩ := cavity_marginal_le hd hs0 hsd hβ hρ
  obtain ⟨B, Cc, hB0, hK⟩ := kerData_periodicRiesz hd hs0 hsd hρ
  refine ⟨max 0 (C1 * (Cc + c)), le_max_left _ _, fun N hN x i => ?_⟩
  rw [critCavity_eq hd hs0 hsd c β hρ N]
  have hint0 : Integrable (fun y => gPlus d s c (x - y)) (withDensityReal ρ) :=
    (hK.int x).add (integrable_const c)
  have hint : Integrable (fun y => gPlus d s c (x - y))
      ((cavityLaw (periodicRiesz d s) (withDensityReal ρ) (N - 1) (β / N) β).map
        (fun Y : Config d (N - 1) => Y i)) :=
    (hint0.smul_measure (c := ENNReal.ofReal C1) ENNReal.ofReal_ne_top).mono_measure (hmarg N hN i)
  refine ⟨(integrable_map_measure hint.1 (measurable_pi_apply i).aemeasurable).1 hint, ?_⟩
  calc ∫ Y, gPlus d s c (x - Y i) ∂(cavityLaw (periodicRiesz d s) (withDensityReal ρ) (N - 1)
          (β / N) β)
      = ∫ y, gPlus d s c (x - y) ∂((cavityLaw (periodicRiesz d s) (withDensityReal ρ) (N - 1)
          (β / N) β).map (fun Y : Config d (N - 1) => Y i)) :=
        (integral_map (φ := fun Y : Config d (N - 1) => Y i)
          (μ := cavityLaw (periodicRiesz d s) (withDensityReal ρ) (N - 1) (β / N) β)
          (f := fun y => gPlus d s c (x - y)) (measurable_pi_apply i).aemeasurable hint.1).symm
    _ ≤ ∫ y, gPlus d s c (x - y) ∂(ENNReal.ofReal C1 • withDensityReal ρ) :=
        integral_mono_measure (hmarg N hN i) (Filter.Eventually.of_forall fun y => hc _)
          (hint0.smul_measure ENNReal.ofReal_ne_top)
    _ = C1 * (convMeasure (periodicRiesz d s) (withDensityReal ρ) x + c) := by
        rw [integral_smul_measure, ENNReal.toReal_ofReal hC1.le, smul_eq_mul]
        congr 1
        unfold gPlus convMeasure
        rw [integral_add (hK.int x) (integrable_const _)]
        simp
    _ ≤ max 0 (C1 * (Cc + c)) := le_max_of_le_right
        (mul_le_mul_of_nonneg_left (by linarith [(abs_le.1 (hK.conv x)).2]) hC1.le)

theorem pole_normalizer_lb (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (c β : ℝ) (hβ : 0 < β)
    {ρ : Torus d → ℝ} (hρ : SmoothPosDensity ρ) (hc : ∀ z, 0 ≤ periodicRiesz d s z + c) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ N : ℕ, 2 ≤ N → ∀ x : Torus d, ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ENNReal.ofReal (Real.exp (-A)) ≤ ∫⁻ Y : Config d (N - 1),
        ENNReal.ofReal (Real.exp (-(t * (β / N)) * ∑ i, gPlus d s c (x - Y i)))
          ∂(critCavity d s c β ρ N) := by
  obtain ⟨A0, hA0, hA⟩ := coord_mean_le hd hs0 hsd c β hβ hρ hc
  have hgp : Measurable (gPlus d s c) := measurable_gPlus hd hs0 hsd c
  refine ⟨β * A0, by positivity, fun N hN x t ht => ?_⟩
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hlam : 0 ≤ β / N := by positivity
  have hP : IsProbabilityMeasure (critCavity d s c β ρ N) := by
    rw [critCavity_eq hd hs0 hsd c β hρ N]
    exact cavity_isProb hd hs0 hsd β hρ _ _ hlam
  set P := critCavity d s c β ρ N with hPdef
  set u : Config d (N - 1) → ℝ := fun Y => ∑ i, gPlus d s c (x - Y i) with hu
  have hui : Integrable u P := integrable_finset_sum _ fun i _ => (hA N hN x i).1
  have hum : Measurable u :=
    Finset.measurable_sum _ fun i _ => hgp.comp (measurable_const.sub (measurable_pi_apply i))
  have hu0 : ∀ Y, 0 ≤ u Y := fun Y => Finset.sum_nonneg fun i _ => hc _
  have hmean : ∫ Y, u Y ∂P ≤ ((N - 1 : ℕ) : ℝ) * A0 := by
    simp only [hu]
    rw [integral_finset_sum _ (fun i _ => (hA N hN x i).1)]
    calc _ ≤ ∑ _i : Fin (N - 1), A0 := Finset.sum_le_sum fun i _ => (hA N hN x i).2
      _ = _ := by simp
  have htl : 0 ≤ t * (β / N) := mul_nonneg ht.1 hlam
  set f : Config d (N - 1) → ℝ := fun Y => -(t * (β / N)) * u Y with hf
  have hfi : Integrable f P := hui.const_mul _
  have hfm : Measurable f := hum.const_mul _
  have hf0 : ∀ Y, f Y ≤ 0 := fun Y => by
    simp only [hf]; nlinarith [hu0 Y]
  have hexpint : Integrable (fun Y => Real.exp (f Y)) P :=
    Integrable.of_bound (C := 1) (Real.measurable_exp.comp hfm).aestronglyMeasurable
      (Filter.Eventually.of_forall fun Y => by
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        exact Real.exp_le_one_iff.2 (hf0 Y))
  have hjensen : Real.exp (∫ Y, f Y ∂P) ≤ ∫ Y, Real.exp (f Y) ∂P :=
    convexOn_exp.map_integral_le Real.continuous_exp.continuousOn isClosed_univ
      (Filter.Eventually.of_forall fun _ => Set.mem_univ _) hfi hexpint
  have hlb : -(β * A0) ≤ ∫ Y, f Y ∂P := by
    simp only [hf]
    rw [integral_const_mul]
    have h1 : t * (β / N) * ∫ Y, u Y ∂P ≤ β * A0 := by
      have hint0 : 0 ≤ ∫ Y, u Y ∂P := integral_nonneg hu0
      have h2 : t * (β / N) ≤ β / N := by
        have : t ≤ 1 := ht.2
        nlinarith [div_nonneg hβ.le hN0.le]
      have h3 : β / N * ((N - 1 : ℕ) : ℝ) ≤ β := by
        rw [Nat.cast_sub (by omega : 1 ≤ N), Nat.cast_one]
        have : β / N * ((N : ℝ) - 1) = β - β / N := by field_simp
        rw [this]; linarith [div_nonneg hβ.le hN0.le]
      calc t * (β / N) * ∫ Y, u Y ∂P ≤ (β / N) * ∫ Y, u Y ∂P :=
            mul_le_mul_of_nonneg_right h2 hint0
        _ ≤ (β / N) * (((N - 1 : ℕ) : ℝ) * A0) := mul_le_mul_of_nonneg_left hmean (div_nonneg hβ.le hN0.le)
        _ = (β / N * ((N - 1 : ℕ) : ℝ)) * A0 := by ring
        _ ≤ β * A0 := mul_le_mul_of_nonneg_right h3 hA0
    linarith
  rw [← ofReal_integral_eq_lintegral_ofReal hexpint
    (Filter.Eventually.of_forall fun Y => (Real.exp_pos _).le)]
  exact ENNReal.ofReal_le_ofReal ((Real.exp_le_exp.2 hlb).trans hjensen)

theorem cavity_le_gibbs (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (β : ℝ) (hβ : 0 < β)
    {ρ : Torus d → ℝ} (hρ : SmoothPosDensity ρ) :
    ∃ D : ℝ, ∀ N : ℕ, 2 ≤ N →
      cavityLaw (periodicRiesz d s) (withDensityReal ρ) (N - 1) (β / N) β ≤
        ENNReal.ofReal D • modulatedGibbs (periodicRiesz d s) (N - 1)
          (((N - 1 : ℕ) : ℝ) * β / N) (withDensityReal ρ) := by
  have hμ := isProbabilityMeasure_mu hρ
  obtain ⟨B, Cc, hB0, hK⟩ := kerData_periodicRiesz hd hs0 hsd hρ
  have hCc := hK.Cc_nonneg
  refine ⟨Real.exp (2 * (β * Cc)), fun N hN => ?_⟩
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hn : 0 < N - 1 := by omega
  have hn0 : (0 : ℝ) < ((N - 1 : ℕ) : ℝ) := by exact_mod_cast hn
  have hbpos : 0 < ((N - 1 : ℕ) : ℝ) * β / N := by positivity
  have hlam : 0 ≤ β / N := by positivity
  rw [modulatedGibbs_eq_cavity hd hs0 hsd hbpos hρ (N - 1) hn]
  have hdiv : ((N - 1 : ℕ) : ℝ) * β / N / ((N - 1 : ℕ) : ℝ) = β / N := by
    field_simp
  rw [hdiv]
  have hdiff : β - ((N - 1 : ℕ) : ℝ) * β / N = β / N := by
    rw [Nat.cast_sub (by omega : 1 ≤ N), Nat.cast_one]; field_simp; ring
  have hg := hK.meas
  obtain ⟨W, hW⟩ := cavity_weight_le hd hs0 hsd (((N - 1 : ℕ) : ℝ) * β / N) hρ (N - 1) (β / N) hlam
  have hz := tilt_normalizer_ne (Measure.pi fun _ : Fin (N - 1) => withDensityReal ρ) _
    (measurable_cavityW hg (withDensityReal ρ) (N - 1) (β / N) (((N - 1 : ℕ) : ℝ) * β / N)) W hW
  unfold cavityLaw
  refine tilt_le_bdd _ _ _ (measurable_cavityW hg (withDensityReal ρ) (N - 1) (β / N) β)
    (measurable_cavityW hg (withDensityReal ρ) (N - 1) (β / N) _) (β * Cc) ?_ hz.1 hz.2
  intro Y
  have : -(β / N) * pairSum (periodicRiesz d s) Y +
        β * ∑ i, convMeasure (periodicRiesz d s) (withDensityReal ρ) (Y i) -
      (-(β / N) * pairSum (periodicRiesz d s) Y +
        ((N - 1 : ℕ) : ℝ) * β / N * ∑ i, convMeasure (periodicRiesz d s) (withDensityReal ρ) (Y i)) =
      (β / N) * ∑ i, convMeasure (periodicRiesz d s) (withDensityReal ρ) (Y i) := by
    rw [← hdiff]; ring
  rw [this, abs_mul, abs_of_nonneg hlam]
  have h4 : |∑ i, convMeasure (periodicRiesz d s) (withDensityReal ρ) (Y i)| ≤
      ((N - 1 : ℕ) : ℝ) * Cc := by
    calc _ ≤ ∑ i, |convMeasure (periodicRiesz d s) (withDensityReal ρ) (Y i)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin (N - 1), Cc := Finset.sum_le_sum fun i _ => hK.conv _
      _ = _ := by simp
  calc β / N * |∑ i, convMeasure (periodicRiesz d s) (withDensityReal ρ) (Y i)|
      ≤ β / N * (((N - 1 : ℕ) : ℝ) * Cc) := mul_le_mul_of_nonneg_left h4 hlam
    _ = (β * Cc) * (((N - 1 : ℕ) : ℝ) / N) := by field_simp
    _ ≤ (β * Cc) * 1 := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        rw [div_le_one hN0]
        have : ((N - 1 : ℕ) : ℝ) ≤ N := by exact_mod_cast Nat.sub_le N 1
        exact this
    _ = β * Cc := mul_one _

theorem pole_le_gibbs (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (β : ℝ) (hβ : 0 < β)
    {ρ : Torus d → ℝ} (hρ : SmoothPosDensity ρ) (c : ℝ)
    (hc : ∀ z, 0 ≤ periodicRiesz d s z + c) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ N : ℕ, 2 ≤ N → ∀ x : Torus d, ∀ t ∈ Set.Icc (0 : ℝ) 1,
      critPole d s c β ρ N x t ≤ ENNReal.ofReal D • modulatedGibbs (periodicRiesz d s) (N - 1)
          (((N - 1 : ℕ) : ℝ) * β / N) (withDensityReal ρ) := by
  obtain ⟨A, hA0, hA⟩ := pole_normalizer_lb hd hs0 hsd c β hβ hρ hc
  obtain ⟨D1, hD1⟩ := cavity_le_gibbs hd hs0 hsd β hβ hρ
  have hgp : Measurable (gPlus d s c) := measurable_gPlus hd hs0 hsd c
  refine ⟨Real.exp A * |D1|, by positivity, fun N hN x t ht => ?_⟩
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hlam : 0 ≤ β / N := by positivity
  have hP : IsProbabilityMeasure (critCavity d s c β ρ N) := by
    rw [critCavity_eq hd hs0 hsd c β hρ N]
    exact cavity_isProb hd hs0 hsd β hρ _ _ hlam
  have h1 : critPole d s c β ρ N x t ≤
      ENNReal.ofReal (Real.exp A) • critCavity d s c β ρ N := by
    have := tilt_le_of_nonpos (critCavity d s c β ρ N)
      (fun Y : Config d (N - 1) => -(t * (β / N)) * ∑ i, gPlus d s c (x - Y i))
      ((Finset.measurable_sum _ fun i _ =>
        hgp.comp (measurable_const.sub (measurable_pi_apply i))).const_mul _)
      (fun Y => by
        have h0 : 0 ≤ ∑ i, gPlus d s c (x - Y i) := Finset.sum_nonneg fun i _ => hc _
        have : 0 ≤ t * (β / N) := mul_nonneg ht.1 hlam
        nlinarith) A (hA N hN x t ht)
    exact this
  have h2 : critCavity d s c β ρ N ≤ ENNReal.ofReal D1 • modulatedGibbs (periodicRiesz d s) (N - 1)
      (((N - 1 : ℕ) : ℝ) * β / N) (withDensityReal ρ) := by
    rw [critCavity_eq hd hs0 hsd c β hρ N]; exact hD1 N hN
  have h3 : ENNReal.ofReal D1 ≤ ENNReal.ofReal |D1| := ENNReal.ofReal_le_ofReal (le_abs_self _)
  calc critPole d s c β ρ N x t ≤ ENNReal.ofReal (Real.exp A) • critCavity d s c β ρ N := h1
    _ ≤ ENNReal.ofReal (Real.exp A) • (ENNReal.ofReal D1 • modulatedGibbs (periodicRiesz d s) (N - 1)
        (((N - 1 : ℕ) : ℝ) * β / N) (withDensityReal ρ)) := measure_smul_le' _ h2
    _ = ENNReal.ofReal (Real.exp A * D1) • modulatedGibbs (periodicRiesz d s) (N - 1)
        (((N - 1 : ℕ) : ℝ) * β / N) (withDensityReal ρ) := by
        rw [smul_smul, ← ENNReal.ofReal_mul (Real.exp_pos _).le]
    _ ≤ _ := by
        refine Measure.le_iff'.2 fun S => ?_
        simp only [Measure.smul_apply, smul_eq_mul]
        refine mul_le_mul' ?_ le_rfl
        exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (le_abs_self _) (Real.exp_pos _).le)

/-! ### Assembly -/

theorem N_mul_deltaN_crit (hcrit : s = (d : ℝ) / 2) {N : ℕ} (hN : 1 ≤ N) :
    (N : ℝ) * deltaN d s N = 1 + Real.log N := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  unfold deltaN
  rw [if_neg (by rw [hcrit]; exact lt_irrefl _), if_pos hcrit, ← mul_assoc, mul_inv_cancel₀ hN0.ne',
    one_mul, Real.log_mul (Real.exp_pos _).ne' hN0.ne', Real.log_exp]

theorem growth_bound {C ε : ℝ} (hC : 0 ≤ C) (hε : 0 < ε) {q : ℝ} (hq : 0 < q)
    (hqe : 3 * C / (2 * q) ≤ ε) {N' N : ℕ} (h1 : 1 ≤ N') (h2 : N' ≤ N) :
    Real.exp (3 * (C * (1 + Real.log N')) / (2 * q)) ≤ Real.exp ε * (N : ℝ) ^ ε := by
  have hN'0 : (0 : ℝ) < N' := by exact_mod_cast h1
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast h1.trans h2
  set κ : ℝ := 3 * C / (2 * q) with hκ
  have hκ0 : 0 ≤ κ := by positivity
  have e1 : 3 * (C * (1 + Real.log N')) / (2 * q) = κ + Real.log N' * κ := by
    simp only [hκ]; field_simp
  rw [e1, Real.exp_add, ← Real.rpow_def_of_pos hN'0]
  refine mul_le_mul (Real.exp_le_exp.2 hqe) ?_ (by positivity) (Real.exp_pos _).le
  calc (N' : ℝ) ^ κ ≤ (N : ℝ) ^ κ :=
        Real.rpow_le_rpow hN'0.le (by exact_mod_cast h2) hκ0
    _ ≤ (N : ℝ) ^ ε := Real.rpow_le_rpow_of_exponent_le hN1 hqe

end ProdTransfer

open ProdTransfer in
/-- Lemma 4.4 `M:R:lem:product-transfer` with a real exponent `ε > 0` (the intended statement). -/
theorem product_moment_transfer_real {d : ℕ} {s : ℝ} (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2)
    (β : ℝ) (hβ : 0 < β)
    (ρ : Torus d → ℝ) (hρ : SmoothPosDensity ρ) (c : ℝ)
    (hc : ∀ z, 0 ≤ periodicRiesz d s z + c) :
    ∀ ε : ℝ, 0 < ε → ∃ q : ℕ, 2 ≤ q ∧ ∃ C : ℝ, ∀ N : ℕ, 2 ≤ N →
      (∀ Y : Config d N → ℝ, Measurable Y →
        eLpNorm Y 2 (modulatedGibbs (periodicRiesz d s) N β (withDensityReal ρ)) ≤
          ENNReal.ofReal (C * (N : ℝ) ^ ε) *
            eLpNorm Y ((2 * q : ℕ) : ℝ≥0∞) (Measure.pi fun _ : Fin N => withDensityReal ρ)) ∧
      (∀ x : Torus d, ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ Y : Config d (N - 1) → ℝ, Measurable Y →
        eLpNorm Y 2 (critPole d s c β ρ N x t) ≤
          ENNReal.ofReal (C * (N : ℝ) ^ ε) *
            eLpNorm Y ((2 * q : ℕ) : ℝ≥0∞)
              (Measure.pi fun _ : Fin (N - 1) => withDensityReal ρ)) := by
  intro ε hε
  obtain ⟨hs0, hsd⟩ := PoleCavityAux.hs_aux hd hcrit
  obtain ⟨C, hCnn, hC⟩ := pressure_all hd hs0 hsd β hβ hρ
  obtain ⟨D, hD0, hD⟩ := pole_le_gibbs hd hs0 hsd β hβ hρ c hc
  obtain ⟨q, hq2, hqe⟩ : ∃ q : ℕ, 2 ≤ q ∧ 3 * C / (2 * (q : ℝ)) ≤ ε := by
    refine ⟨max 2 ⌈3 * C / (2 * ε)⌉₊, le_max_left _ _, ?_⟩
    have hqpos : (0 : ℝ) < ((max 2 ⌈3 * C / (2 * ε)⌉₊ : ℕ) : ℝ) := by
      have : (2 : ℝ) ≤ ((max 2 ⌈3 * C / (2 * ε)⌉₊ : ℕ) : ℝ) := by exact_mod_cast le_max_left _ _
      linarith
    rw [div_le_iff₀ (by positivity)]
    have h1 : 3 * C / (2 * ε) ≤ ((max 2 ⌈3 * C / (2 * ε)⌉₊ : ℕ) : ℝ) :=
      (Nat.le_ceil _).trans (by exact_mod_cast le_max_right _ _)
    rw [div_le_iff₀ (by positivity)] at h1
    linarith
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have hq2R : (2 : ℝ) ≤ q := by exact_mod_cast hq2
  have hexp : ((2 * q : ℕ) : ℝ≥0∞) = ENNReal.ofReal (2 * (q : ℝ)) := by
    rw [show (2 * (q : ℝ)) = ((2 * q : ℕ) : ℝ) by push_cast; ring, ENNReal.ofReal_natCast]
  refine ⟨q, hq2, Real.exp ε * (1 + D), fun N hN => ⟨?_, ?_⟩⟩
  · intro Y hY
    rw [hexp]
    have hb : β ∈ Set.Icc (β / 2) β := ⟨by linarith, le_rfl⟩
    refine (eLp_gibbs_le hd hs0 hsd β hβ hρ hC N (by omega) β hb (q : ℝ) hq2R Y hY).trans ?_
    refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
    have e : C * N * deltaN d s N = C * (1 + Real.log N) := by
      rw [mul_assoc, N_mul_deltaN_crit hcrit (by omega)]
    rw [e]
    refine (growth_bound hCnn hε hq0 hqe (le_refl _ |>.trans' (by omega) : 1 ≤ N) le_rfl).trans ?_
    exact mul_le_mul_of_nonneg_right (by nlinarith [Real.exp_pos ε]) (by positivity)
  · intro x t ht Y hY
    rw [hexp]
    have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
    have hN1 : 1 ≤ N - 1 := by omega
    have hb : ((N - 1 : ℕ) : ℝ) * β / N ∈ Set.Icc (β / 2) β := by
      have h1 : ((N - 1 : ℕ) : ℝ) = N - 1 := by rw [Nat.cast_sub (by omega), Nat.cast_one]
      have h2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
      constructor
      · rw [h1, le_div_iff₀ hN0]; nlinarith
      · rw [h1, div_le_iff₀ hN0]; nlinarith
    have hpole := eLpNorm_mono_measure Y (p := 2) (hD N hN x t ht)
    rw [eLpNorm_smul_measure_of_ne_top (by norm_num) Y _ hY.aestronglyMeasurable] at hpole
    have hg := eLp_gibbs_le hd hs0 hsd β hβ hρ hC (N - 1) hN1 _ hb (q : ℝ) hq2R Y hY
    refine hpole.trans ?_
    have hsq : ENNReal.ofReal D ^ (1 / (2 : ℝ≥0∞)).toReal ≤ ENNReal.ofReal (1 + D) := by
      have : (1 / (2 : ℝ≥0∞)).toReal = 1 / 2 := by simp
      rw [this, ENNReal.ofReal_rpow_of_nonneg hD0 (by norm_num)]
      refine ENNReal.ofReal_le_ofReal ?_
      rw [← Real.sqrt_eq_rpow]
      nlinarith [Real.sq_sqrt hD0, Real.sqrt_nonneg D]
    have hfac : Real.exp (3 * (C * ((N - 1 : ℕ) : ℝ) * deltaN d s (N - 1)) / (2 * (q : ℝ))) ≤
        Real.exp ε * (N : ℝ) ^ ε := by
      have e : C * ((N - 1 : ℕ) : ℝ) * deltaN d s (N - 1) = C * (1 + Real.log ((N - 1 : ℕ) : ℝ)) := by
        rw [mul_assoc, N_mul_deltaN_crit hcrit hN1]
      rw [e]
      exact growth_bound hCnn hε hq0 hqe hN1 (Nat.sub_le N 1)
    calc ENNReal.ofReal D ^ (1 / (2 : ℝ≥0∞)).toReal • eLpNorm Y 2
          (modulatedGibbs (periodicRiesz d s) (N - 1) (((N - 1 : ℕ) : ℝ) * β / N) (withDensityReal ρ))
        ≤ ENNReal.ofReal (1 + D) * (ENNReal.ofReal (Real.exp ε * (N : ℝ) ^ ε) *
            eLpNorm Y (ENNReal.ofReal (2 * (q : ℝ)))
              (Measure.pi fun _ : Fin (N - 1) => withDensityReal ρ)) := by
          rw [smul_eq_mul]
          exact mul_le_mul' hsq (hg.trans (mul_le_mul' (ENNReal.ofReal_le_ofReal hfac) le_rfl))
      _ = ENNReal.ofReal (Real.exp ε * (1 + D) * (N : ℝ) ^ ε) *
            eLpNorm Y (ENNReal.ofReal (2 * (q : ℝ)))
              (Measure.pi fun _ : Fin (N - 1) => withDensityReal ρ) := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
          congr 2; ring

/-- Lemma 4.4 `M:R:lem:product-transfer` (restatement of `HRS.product_moment_transfer`, proved here
because Proposition 5.5 and the cavity marginal bounds are downstream of `PoleCavity.lean`).
In the statement of `HRS.product_moment_transfer` the exponent `ε` in `N ^ ε` is elaborated as a
natural number (`Monoid.npow`), which makes it weaker than the source; the real-exponent form
is `product_moment_transfer_real`, from which this follows. -/
theorem product_moment_transfer_proof {d : ℕ} {s : ℝ} (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2)
    (β : ℝ) (hβ : 0 < β)
    (ρ : Torus d → ℝ) (hρ : SmoothPosDensity ρ) (c : ℝ)
    (hc : ∀ z, 0 ≤ periodicRiesz d s z + c) :
    ∀ ε : ℝ, 0 < ε → ∃ q : ℕ, 2 ≤ q ∧ ∃ C : ℝ, ∀ N : ℕ, 2 ≤ N →
      (∀ Y : Config d N → ℝ, Measurable Y →
        eLpNorm Y 2 (modulatedGibbs (periodicRiesz d s) N β (withDensityReal ρ)) ≤
          ENNReal.ofReal (C * (N : ℝ) ^ ε) *
            eLpNorm Y ((2 * q : ℕ) : ℝ≥0∞) (Measure.pi fun _ : Fin N => withDensityReal ρ)) ∧
      (∀ x : Torus d, ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ Y : Config d (N - 1) → ℝ, Measurable Y →
        eLpNorm Y 2 (critPole d s c β ρ N x t) ≤
          ENNReal.ofReal (C * (N : ℝ) ^ ε) *
            eLpNorm Y ((2 * q : ℕ) : ℝ≥0∞)
              (Measure.pi fun _ : Fin (N - 1) => withDensityReal ρ)) := by
  exact product_moment_transfer_real hd hcrit β hβ ρ hρ c hc

example := (@product_moment_transfer_proof : type_of% @product_moment_transfer)

end HRS

end
