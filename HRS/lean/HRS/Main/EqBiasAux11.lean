import HRS.Main.EqBiasAux10

/-!
# EQ-BIAS, S9b: moments of the singular core `f·1{f > H}` under the pole law
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

noncomputable section

namespace HRS

namespace Main

variable {d : ℕ} {s c : ℝ}

open HRS.External HRS.PoleCavityAux HRS.MarginalAux HRS.ProdTransfer HRS.CavResp

/-- The singular core `g_+(x - y) 1{g_+(x - y) > H}`. -/
def eqbias_core (d : ℕ) (s c : ℝ) (x : Torus d) (H : ℝ) (y : Torus d) : ℝ :=
  if H < gPlus d s c (x - y) then gPlus d s c (x - y) else 0

theorem eqbias_lint_dens_le {α : Type*} [MeasurableSpace α] {μ ν : Measure α} [SigmaFinite μ]
    [SigmaFinite ν] (hac : ν ≪ μ) {b : α → ℝ≥0∞} (hb : ∀ᵐ y ∂μ, ν.rnDeriv μ y ≤ b y)
    {φ : α → ℝ≥0∞} (hφ : Measurable φ) : ∫⁻ y, φ y ∂ν ≤ ∫⁻ y, b y * φ y ∂μ := by
  rw [← lintegral_rnDeriv_mul hac hφ.aemeasurable]
  refine lintegral_mono_ae ?_
  filter_upwards [hb] with y hy
  exact mul_le_mul_left hy _

theorem eqbias_exp_le {β B N t g : ℝ} (hβ : 0 < β) (hB : 0 ≤ B) (hNpos : 0 < N) (hN1 : 1 ≤ N)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hg : -B ≤ g) :
    Real.exp (-(t * (β / N)) * g) ≤ Real.exp (β * B) := by
  refine Real.exp_le_exp.2 ?_
  have hl : t * (β / N) ≤ β := by
    have : β / N ≤ β := by rw [div_le_iff₀ hNpos]; nlinarith
    nlinarith
  have h0 : 0 ≤ t * (β / N) := by positivity
  nlinarith

theorem eqbias_core_measurable (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (x : Torus d) (H : ℝ) :
    Measurable (eqbias_core d s c x H) := by
  have hgm := measurable_gPlus hd hs0 hsd c
  have hfm : Measurable fun y : Torus d => gPlus d s c (x - y) :=
    hgm.comp (measurable_const.sub measurable_id)
  exact Measurable.ite (measurableSet_lt measurable_const hfm) hfm measurable_const

theorem eqbias_core_le (hc : ∀ z, 0 ≤ periodicRiesz d s z + c) (x : Torus d) (H : ℝ) (y : Torus d) :
    0 ≤ eqbias_core d s c x H y ∧ eqbias_core d s c x H y ≤ gPlus d s c (x - y) := by
  unfold eqbias_core
  split_ifs
  · exact ⟨hc _, le_rfl⟩
  · exact ⟨le_rfl, hc _⟩

theorem eqbias_core_int (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {β : ℝ} (hβ : 0 < β) {ρ : Torus d → ℝ}
    (hρ : SmoothPosDensity ρ) (hc : ∀ z, 0 ≤ periodicRiesz d s z + c) (x : Torus d) (H : ℝ) :
    Integrable (eqbias_core d s c x H) (withDensityReal ρ) := by
  have := isProbabilityMeasure_mu hρ
  refine Integrable.mono' (eqbias_gPlus_int hd hs0 hsd hβ hρ hc x)
    (eqbias_core_measurable hd hs0 hsd x H).aestronglyMeasurable
    (Eventually.of_forall fun y => ?_)
  have := eqbias_core_le hc x H y
  rw [Real.norm_eq_abs, abs_of_nonneg this.1]
  exact this.2

theorem eqbias_core_moments (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {β : ℝ} (hβ : 0 < β)
    {ρ : Torus d → ℝ} (hρ : SmoothPosDensity ρ) (hc : ∀ z, 0 ≤ periodicRiesz d s z + c)
    (hc0 : 0 ≤ c) :
    ∃ M C₀ : ℝ, 0 ≤ M ∧ 0 ≤ C₀ ∧ ∀ N : ℕ, 2 ≤ N → ∀ x : Torus d, ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ∀ H : ℝ,
      (∀ i : Fin (N - 1),
        ∫ Y, eqbias_core d s c x H (Y i)
          ∂(poleLaw (periodicRiesz d s) (withDensityReal ρ) (N - 1) (β / N) β x t) ≤
          M * ∫ y, eqbias_core d s c x H y ∂(withDensityReal ρ)) ∧
      (∀ i j : Fin (N - 1), i ≠ j →
        ∫ Y, eqbias_core d s c x H (Y i) * eqbias_core d s c x H (Y j)
          ∂(poleLaw (periodicRiesz d s) (withDensityReal ρ) (N - 1) (β / N) β x t) ≤
          C₀ * (∫ y, eqbias_core d s c x H y ∂(withDensityReal ρ)) ^ 2) := by
  have hμ := isProbabilityMeasure_mu hρ
  obtain ⟨M1, hM1, hM1'⟩ := pole_marg_le hd hs0 hsd hβ hρ
  obtain ⟨C, hCpos, hC⟩ := PoleCavityAux.pole_density_clauses hd hs0 hsd β hβ ρ hρ
  refine ⟨M1, C * Real.exp (2 * (β * c)), hM1.le, by positivity, fun N hN x t ht H => ?_⟩
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hlam : 0 ≤ β / N := by positivity
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
  have hlb : t * (β / N) ≤ β := by
    have : β / N ≤ β := by rw [div_le_iff₀ hN0]; nlinarith
    nlinarith [ht.2, ht.1]
  have hl0 : 0 ≤ t * (β / N) := mul_nonneg ht.1 hlam
  have := (isProbabilityMeasure_poleLaw hd hs0 hsd β hβ ρ hρ N hN x t ht).2
  set P := poleLaw (periodicRiesz d s) (withDensityReal ρ) (N - 1) (β / N) β x t with hP
  have hfm := eqbias_core_measurable hd hs0 hsd (c := c) x H
  have hf0 := fun y => (eqbias_core_le hc x H y).1
  have hfi := eqbias_core_int hd hs0 hsd hβ hρ hc x H
  set m := ∫ y, eqbias_core d s c x H y ∂(withDensityReal ρ) with hm
  have hm0 : 0 ≤ m := integral_nonneg hf0
  have hlm : ∫⁻ y, ENNReal.ofReal (eqbias_core d s c x H y) ∂(withDensityReal ρ) =
      ENNReal.ofReal m :=
    (ofReal_integral_eq_lintegral_ofReal hfi (Eventually.of_forall hf0)).symm
  constructor
  · intro i
    obtain ⟨-, hle⟩ := hM1' N hN x t ht
    have hmeas : Measurable fun Y : Config d (N - 1) => Y i := measurable_pi_apply i
    have := (integ_of_lint (μ := P) (f := fun Y => eqbias_core d s c x H (Y i))
      (hfm.comp hmeas) (fun Y => hf0 _) (C := M1 * m) (by positivity) ?_).2
    · exact this
    have e0 : ∫⁻ Y, ENNReal.ofReal (eqbias_core d s c x H (Y i)) ∂P =
        ∫⁻ y, ENNReal.ofReal (eqbias_core d s c x H y) ∂(P.map fun Y : Config d (N - 1) => Y i) :=
      (lintegral_map (ENNReal.measurable_ofReal.comp hfm) hmeas).symm
    rw [e0]
    calc ∫⁻ y, ENNReal.ofReal (eqbias_core d s c x H y) ∂(P.map fun Y : Config d (N - 1) => Y i)
        ≤ ∫⁻ y, ENNReal.ofReal (eqbias_core d s c x H y) ∂(ENNReal.ofReal M1 • withDensityReal ρ) :=
          lintegral_mono' (hle i) le_rfl
      _ = ENNReal.ofReal M1 * ENNReal.ofReal m := by rw [lintegral_smul_measure, hlm, smul_eq_mul]
      _ = ENNReal.ofReal (M1 * m) := (ENNReal.ofReal_mul hM1.le).symm
  · intro i j hij
    obtain ⟨hac, hle⟩ := (hC N hN x t ht).2 i j hij
    have hbd : ∀ᵐ p ∂((withDensityReal ρ).prod (withDensityReal ρ)),
        (twoMarginal P i j).rnDeriv ((withDensityReal ρ).prod (withDensityReal ρ)) p ≤
          ENNReal.ofReal (C * Real.exp (2 * (β * c))) := by
      filter_upwards [hle] with p hp
      refine hp.trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hCpos.le))
      have h1 := hc (x - p.1)
      have h2 := hc (x - p.2)
      have a1 : -(t * (β / N)) * (periodicRiesz d s (x - p.1) + periodicRiesz d s (x - p.2)) ≤
          (t * (β / N)) * (2 * c) := by
        have := mul_nonneg hl0 (add_nonneg h1 h2)
        nlinarith
      have a2 : (t * (β / N)) * (2 * c) ≤ β * (2 * c) :=
        mul_le_mul_of_nonneg_right hlb (by positivity)
      linarith
    have hmeas : Measurable fun Y : Config d (N - 1) => (Y i, Y j) :=
      (measurable_pi_apply i).prodMk (measurable_pi_apply j)
    have hφ : Measurable fun p : Torus d × Torus d =>
        ENNReal.ofReal (eqbias_core d s c x H p.1 * eqbias_core d s c x H p.2) :=
      ENNReal.measurable_ofReal.comp ((hfm.comp measurable_fst).mul (hfm.comp measurable_snd))
    have key := (integ_of_lint (μ := P)
      (f := fun Y => eqbias_core d s c x H (Y i) * eqbias_core d s c x H (Y j))
      ((hfm.comp (measurable_pi_apply i)).mul (hfm.comp (measurable_pi_apply j)))
      (fun Y => mul_nonneg (hf0 _) (hf0 _)) (C := C * Real.exp (2 * (β * c)) * m ^ 2)
      (by positivity) ?_).2
    · calc _ ≤ C * Real.exp (2 * (β * c)) * m ^ 2 := key
        _ = _ := by ring
    have e1 : ∫⁻ Y, ENNReal.ofReal (eqbias_core d s c x H (Y i) * eqbias_core d s c x H (Y j)) ∂P =
        ∫⁻ p, ENNReal.ofReal (eqbias_core d s c x H p.1 * eqbias_core d s c x H p.2)
          ∂(twoMarginal P i j) := by
      unfold twoMarginal
      rw [lintegral_map hφ hmeas]
    rw [e1]
    have hTP : IsProbabilityMeasure (twoMarginal P i j) := by
      unfold twoMarginal
      exact ⟨by rw [Measure.map_apply hmeas MeasurableSet.univ]; simp⟩
    have haux := eqbias_lint_dens_le hac hbd hφ
    refine haux.trans ?_
    have e2 : ∫⁻ p, ENNReal.ofReal (C * Real.exp (2 * (β * c))) *
        ENNReal.ofReal (eqbias_core d s c x H p.1 * eqbias_core d s c x H p.2)
          ∂((withDensityReal ρ).prod (withDensityReal ρ)) =
        ENNReal.ofReal (C * Real.exp (2 * (β * c))) * (ENNReal.ofReal m * ENNReal.ofReal m) := by
      rw [lintegral_const_mul _ hφ]
      congr 1
      have : ∀ p : Torus d × Torus d,
          ENNReal.ofReal (eqbias_core d s c x H p.1 * eqbias_core d s c x H p.2) =
            ENNReal.ofReal (eqbias_core d s c x H p.1) * ENNReal.ofReal (eqbias_core d s c x H p.2) :=
        fun p => ENNReal.ofReal_mul (hf0 _)
      simp_rw [this]
      rw [lintegral_prod_mul (f := fun y => ENNReal.ofReal (eqbias_core d s c x H y))
        (g := fun y => ENNReal.ofReal (eqbias_core d s c x H y))
        (ENNReal.measurable_ofReal.comp hfm).aemeasurable
        (ENNReal.measurable_ofReal.comp hfm).aemeasurable, hlm]
    rw [e2, ← ENNReal.ofReal_mul hm0, ← ENNReal.ofReal_mul (by positivity)]
    refine le_of_eq (congrArg _ ?_)
    ring

theorem eqbias_sqexp_bdd {u g : ℝ} (hu : 0 < u) (hg : 0 ≤ g) :
    g ^ 2 * Real.exp (-(u * g)) ≤ 2 / u ^ 2 := by
  have h0 : 0 ≤ u * g := mul_nonneg hu.le hg
  have h1 : (u * g) ^ 2 / 2 ≤ Real.exp (u * g) := by
    have := Real.quadratic_le_exp_of_nonneg h0
    nlinarith [sq_nonneg (u * g)]
  have h2 : (u * g) ^ 2 * Real.exp (-(u * g)) ≤ 2 := by
    rw [Real.exp_neg, ← div_eq_mul_inv, div_le_iff₀ (Real.exp_pos _)]
    linarith
  rw [le_div_iff₀ (by positivity)]
  calc g ^ 2 * Real.exp (-(u * g)) * u ^ 2 = (u * g) ^ 2 * Real.exp (-(u * g)) := by ring
    _ ≤ 2 := h2

theorem eqbias_diag (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {β : ℝ} (hβ : 0 < β)
    {ρ : Torus d → ℝ} (hρ : SmoothPosDensity ρ) (hc : ∀ z, 0 ≤ periodicRiesz d s z + c) :
    ∃ Cψ : ℝ, 0 ≤ Cψ ∧ ∀ N : ℕ, ∀ hN : 2 ≤ N, ∀ x : Torus d, ∀ t ∈ Set.Icc (0 : ℝ) 1, 0 < t →
      ∀ ε : ℝ, 0 ≤ ε →
      (∀ y' : Torus d,
        Integrable (fun Y => |cavityField d s c β ρ N (⟨0, by omega⟩ : Fin (N - 1)) Y y'|)
          (poleLaw (periodicRiesz d s) (withDensityReal ρ) (N - 1) (β / N) β x t) ∧
        ∫ Y, |cavityField d s c β ρ N (⟨0, by omega⟩ : Fin (N - 1)) Y y'|
          ∂(poleLaw (periodicRiesz d s) (withDensityReal ρ) (N - 1) (β / N) β x t) ≤ ε) →
      ∀ H : ℝ,
      (∀ i : Fin (N - 1), Integrable (fun Y => eqbias_core d s c x H (Y i) ^ 2)
          (poleLaw (periodicRiesz d s) (withDensityReal ρ) (N - 1) (β / N) β x t)) ∧
      |∫ Y, eqbias_core d s c x H (Y ⟨0, by omega⟩) ^ 2
          ∂(poleLaw (periodicRiesz d s) (withDensityReal ρ) (N - 1) (β / N) β x t) -
        ∫ y, eqbias_core d s c x H y ^ 2 * Real.exp (-(t * (β / N)) * gPlus d s c (x - y))
          ∂(withDensityReal ρ)| ≤
        Cψ * (ε + 1 / (N : ℝ)) *
          ∫ y, eqbias_core d s c x H y ^ 2 * Real.exp (-(t * (β / N)) * gPlus d s c (x - y))
            ∂(withDensityReal ρ) := by
  have hμ := isProbabilityMeasure_mu hρ
  obtain ⟨Cψ, hCψ0, hCψ⟩ := eqbias_psi_bound hd hs0 hsd hβ hρ hc
  refine ⟨Cψ, hCψ0, fun N hN x t ht ht0 ε hε0 hε H => ?_⟩
  have hfm := eqbias_core_measurable hd hs0 hsd (c := c) x H
  have hf0 := fun y => (eqbias_core_le hc x H y).1
  have hfg := fun y => (eqbias_core_le hc x H y).2
  have hc' : ∀ y, 0 ≤ gPlus d s c (x - y) := fun y => hc _
  have hgm := measurable_gPlus hd hs0 hsd c
  have hgxm : Measurable fun y : Torus d => gPlus d s c (x - y) :=
    hgm.comp (measurable_const.sub measurable_id)
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hu : 0 < t * (β / N) := by positivity
  have := (isProbabilityMeasure_poleLaw hd hs0 hsd β hβ ρ hρ N hN x t ht).2
  have hPpsi := hCψ N hN x t ht ε hε0 hε
  obtain ⟨m, rfl⟩ : ∃ m, N = m + 2 := ⟨N - 2, by omega⟩
  have hcrit := critPole_formula hd hs0 hsd β hβ hρ hc m x ht.1
  rw [critPole_eq_poleLaw hd hs0 hsd β hβ hρ hN x t] at hcrit
  obtain ⟨hac, hform⟩ := hcrit
  set P := poleLaw (periodicRiesz d s) (withDensityReal ρ) (m + 2 - 1) (β / ((m + 2 : ℕ) : ℝ)) β x t
    with hP
  set u : ℝ := t * (β / ((m + 2 : ℕ) : ℝ)) with hudef
  set εA : ℝ := Cψ * (ε + 1 / ((m + 2 : ℕ) : ℝ)) with hεA
  have hεA0 : 0 ≤ εA := by positivity
  set e : Torus d → ℝ := fun y => Real.exp (-u * gPlus d s c (x - y)) with he
  have he0 : ∀ y, 0 ≤ e y := fun y => (Real.exp_pos _).le
  have hem : Measurable e := Real.measurable_exp.comp (hgxm.const_mul _)
  set ν := firstMarginal P with hν
  have hn : 0 < m + 2 - 1 := by omega
  have hνp : IsProbabilityMeasure ν := isProb_firstMarginal hn P
  set Afun : Torus d → ℝ := fun y =>
      ∫ X, Real.exp (-(cavityField d s c β ρ (m + 2) (⟨0, by omega⟩ : Fin (m + 2 - 1)) X y)) /
        (∫ y', Real.exp (-(t * (β / ((m + 2 : ℕ) : ℝ))) * gPlus d s c (x - y') -
          cavityField d s c β ρ (m + 2) (⟨0, by omega⟩ : Fin (m + 2 - 1)) X y')
          ∂(withDensityReal ρ)) ∂P with hAfun
  have hA1 : ∀ y, |Afun y - 1| ≤ εA := hPpsi
  have hdens : ∀ᵐ y ∂(withDensityReal ρ), (ν.rnDeriv (withDensityReal ρ) y).toReal = e y * Afun y :=
    hform
  have hq0 : ∀ y, eqbias_core d s c x H y ^ 2 * e y ≤ 2 / u ^ 2 := by
    intro y
    have h1 := eqbias_sqexp_bdd hu (hc' y)
    have h2 : eqbias_core d s c x H y ^ 2 ≤ gPlus d s c (x - y) ^ 2 :=
      pow_le_pow_left₀ (hf0 y) (hfg y) 2
    calc eqbias_core d s c x H y ^ 2 * e y ≤ gPlus d s c (x - y) ^ 2 * e y :=
          mul_le_mul_of_nonneg_right h2 (he0 y)
      _ = gPlus d s c (x - y) ^ 2 * Real.exp (-(u * gPlus d s c (x - y))) := by
          simp only [he, neg_mul]
      _ ≤ 2 / u ^ 2 := h1
  have hqm : Measurable fun y => eqbias_core d s c x H y ^ 2 * e y := (hfm.pow_const 2).mul hem
  have hqi : Integrable (fun y => eqbias_core d s c x H y ^ 2 * e y) (withDensityReal ρ) :=
    Integrable.mono' (integrable_const (2 / u ^ 2)) hqm.aestronglyMeasurable
      (Eventually.of_forall fun y => by
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (he0 y))]; exact hq0 y)
  have hrm : Measurable fun y => (ν.rnDeriv (withDensityReal ρ) y).toReal :=
    (Measure.measurable_rnDeriv _ _).ennreal_toReal
  have hsmi : Integrable (fun y => (ν.rnDeriv (withDensityReal ρ) y).toReal •
      eqbias_core d s c x H y ^ 2) (withDensityReal ρ) := by
    refine Integrable.mono' (integrable_const ((1 + εA) * (2 / u ^ 2)))
      ((hrm.mul (hfm.pow_const 2)).aestronglyMeasurable) ?_
    filter_upwards [hdens] with y hy
    rw [smul_eq_mul, Real.norm_eq_abs, hy]
    have hA2 : Afun y ≤ 1 + εA := by have := hA1 y; rw [abs_le] at this; linarith
    have hA0 : 0 ≤ Afun y :=
      integral_nonneg fun X => div_nonneg (Real.exp_pos _).le
        (integral_nonneg fun _ => (Real.exp_pos _).le)
    rw [abs_of_nonneg (mul_nonneg (mul_nonneg (he0 y) hA0) (sq_nonneg _))]
    calc e y * Afun y * eqbias_core d s c x H y ^ 2
        = (eqbias_core d s c x H y ^ 2 * e y) * Afun y := by ring
      _ ≤ (2 / u ^ 2) * (1 + εA) :=
          mul_le_mul (hq0 y) hA2 hA0 (by positivity)
      _ = _ := by ring
  have hνi : Integrable (fun y => eqbias_core d s c x H y ^ 2) ν :=
    (integrable_rnDeriv_smul_iff hac).1 hsmi
  have hY0 : Measurable fun Y : Config d (m + 2 - 1) => Y ⟨0, hn⟩ := measurable_pi_apply _
  have hνmap : ν = P.map fun Y : Config d (m + 2 - 1) => Y ⟨0, hn⟩ := by
    rw [hν]; unfold firstMarginal; rw [dif_pos hn]
  have hexch := MarginalAux.poleLaw_exchangeable hd hs0 hsd β hρ (m + 2 - 1)
    (β / ((m + 2 : ℕ) : ℝ)) (by positivity) x t
  refine ⟨fun i => ?_, ?_⟩
  · have hi : P.map (fun Y : Config d (m + 2 - 1) => Y i) = ν := by
      rw [hνmap]; exact hexch.marginal_eq i ⟨0, hn⟩
    have := hνi
    rw [← hi] at this
    exact (integrable_map_measure (hfm.pow_const 2).aestronglyMeasurable
      (measurable_pi_apply i).aemeasurable).1 this
  · have e1 : ∫ Y, eqbias_core d s c x H (Y ⟨0, hn⟩) ^ 2 ∂P =
        ∫ y, eqbias_core d s c x H y ^ 2 ∂ν := by
      rw [hνmap]
      exact (integral_map hY0.aemeasurable (hfm.pow_const 2).aestronglyMeasurable).symm
    have e2 : ∫ y, eqbias_core d s c x H y ^ 2 ∂ν =
        ∫ y, (ν.rnDeriv (withDensityReal ρ) y).toReal • eqbias_core d s c x H y ^ 2
          ∂(withDensityReal ρ) := (integral_rnDeriv_smul hac).symm
    have e3 : ∫ y, (ν.rnDeriv (withDensityReal ρ) y).toReal • eqbias_core d s c x H y ^ 2
          ∂(withDensityReal ρ) =
        ∫ y, (eqbias_core d s c x H y ^ 2 * e y) * Afun y ∂(withDensityReal ρ) := by
      refine integral_congr_ae ?_
      filter_upwards [hdens] with y hy
      rw [smul_eq_mul, hy]; ring
    show |∫ Y, eqbias_core d s c x H (Y ⟨0, hn⟩) ^ 2 ∂P - ∫ y, (eqbias_core d s c x H y ^ 2 * e y)
      ∂(withDensityReal ρ)| ≤ εA * ∫ y, (eqbias_core d s c x H y ^ 2 * e y) ∂(withDensityReal ρ)
    rw [e1, e2, e3]
    have hprodi : Integrable (fun y => (eqbias_core d s c x H y ^ 2 * e y) * Afun y)
        (withDensityReal ρ) := by
      refine hsmi.congr ?_
      filter_upwards [hdens] with y hy
      rw [smul_eq_mul, hy]; ring
    rw [← integral_sub hprodi hqi]
    have hdi : Integrable (fun y => (eqbias_core d s c x H y ^ 2 * e y) * εA) (withDensityReal ρ) :=
      hqi.mul_const _
    calc _ ≤ ∫ y, |(eqbias_core d s c x H y ^ 2 * e y) * Afun y - eqbias_core d s c x H y ^ 2 * e y|
          ∂(withDensityReal ρ) := abs_integral_le_integral_abs
      _ ≤ ∫ y, (eqbias_core d s c x H y ^ 2 * e y) * εA ∂(withDensityReal ρ) := by
          refine integral_mono_of_nonneg (Eventually.of_forall fun y => abs_nonneg _) hdi
            (Eventually.of_forall fun y => ?_)
          beta_reduce
          have h0 : 0 ≤ eqbias_core d s c x H y ^ 2 * e y := mul_nonneg (sq_nonneg _) (he0 y)
          have : (eqbias_core d s c x H y ^ 2 * e y) * Afun y - eqbias_core d s c x H y ^ 2 * e y =
              (eqbias_core d s c x H y ^ 2 * e y) * (Afun y - 1) := by ring
          rw [this, abs_mul, abs_of_nonneg h0]
          exact mul_le_mul_of_nonneg_left (hA1 y) h0
      _ = _ := by rw [integral_mul_const]; ring


end Main

end HRS

end
