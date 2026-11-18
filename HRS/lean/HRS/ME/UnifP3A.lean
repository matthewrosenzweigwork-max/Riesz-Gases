import HRS.ME.UnifP1B
import HRS.ME.NfUPU1aA
import HRS.Equilibrium.ProductTransfer

/-!
# Uniform product-moment transfer, part A (packet P3)

Uniform versions (constants chosen before `β ∈ [βm, βp]` and before `ρ`) of the pieces of
`HRS.product_moment_transfer_real` (`HRS/Equilibrium/ProductTransfer.lean`) whose constants depended on
`ρ`: `pressure_N1`, `pressure_N2`/`pressure_all`, `cavity_marginal_le`, `coord_mean_le`,
`pole_normalizer_lb`, `cavity_le_gibbs`, `pole_le_gibbs`.  The density enters only through
`c₀ ≤ ρ ≤ Λ` (and `SmoothPosDensity ρ`); the kernel constants come from `kerData_periodicRiesz_unif`.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

noncomputable section

namespace HRS.ME.Unif

open HRS HRS.External HRS.PoleCavityAux HRS.MarginalAux HRS.ProdTransfer

variable {d : ℕ} {s : ℝ}

theorem Kbound_mono {g : Torus d → ℝ} {B Cc β β' : ℝ} (hB : 0 ≤ B) (hCc : 0 ≤ Cc) (h : β ≤ β') :
    Kbound g B Cc β 1 ≤ Kbound g B Cc β' 1 := by
  unfold Kbound
  have h0 := abs_nonneg (g 0)
  nlinarith [mul_nonneg (sub_nonneg.2 h) hB, mul_nonneg (sub_nonneg.2 h) hCc,
    mul_nonneg (sub_nonneg.2 h) h0]

theorem smul_mono_const {α : Type*} [MeasurableSpace α] (μ : Measure α) {a b : ℝ≥0∞} (h : a ≤ b) :
    a • μ ≤ b • μ :=
  Measure.le_iff'.2 fun S => by
    simp only [Measure.smul_apply, smul_eq_mul]
    exact mul_le_mul' h le_rfl

/-! ### Pressure -/

theorem pressure_N1_kd (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {ρ : Torus d → ℝ}
    (hρ : SmoothPosDensity ρ) {B Cc : ℝ}
    (hK : KerData (periodicRiesz d s) (withDensityReal ρ) B Cc) {βp : ℝ} (hβp : 0 ≤ βp)
    {b : ℝ} (hb0 : 0 ≤ b) (hb : b ≤ 2 * βp) :
    ENNReal.ofReal (Real.exp (-(6 * βp * |Cc|))) ≤
          ∫⁻ X : Config d 1, ENNReal.ofReal (Real.exp (-b * (1 : ℕ) *
            modulatedEnergyKernel (periodicRiesz d s) X (withDensityReal ρ)))
            ∂(Measure.pi fun _ => withDensityReal ρ) ∧
        ∫⁻ X : Config d 1, ENNReal.ofReal (Real.exp (-b * (1 : ℕ) *
            modulatedEnergyKernel (periodicRiesz d s) X (withDensityReal ρ)))
            ∂(Measure.pi fun _ => withDensityReal ρ) ≤
          ENNReal.ofReal (Real.exp (6 * βp * |Cc|)) := by
  haveI := isProbabilityMeasure_mu hρ
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
  have hbd : ∀ X : Config d 1, |-b * ((1 : ℕ) : ℝ) *
      modulatedEnergyKernel (periodicRiesz d s) X (withDensityReal ρ)| ≤ 6 * βp * |Cc| := by
    intro X
    have := hE X
    calc |-b * ((1 : ℕ) : ℝ) * modulatedEnergyKernel (periodicRiesz d s) X (withDensityReal ρ)|
        = b * |modulatedEnergyKernel (periodicRiesz d s) X (withDensityReal ρ)| := by
          simp [abs_mul, abs_of_nonneg hb0]
      _ ≤ (2 * βp) * (3 * Cc) := mul_le_mul hb this (abs_nonneg _) (by positivity)
      _ = 6 * βp * Cc := by ring
      _ ≤ 6 * βp * |Cc| := mul_le_mul_of_nonneg_left (le_abs_self Cc) (by positivity)
  constructor
  · calc ENNReal.ofReal (Real.exp (-(6 * βp * |Cc|)))
        = ∫⁻ _ : Config d 1, ENNReal.ofReal (Real.exp (-(6 * βp * |Cc|)))
            ∂(Measure.pi fun _ => withDensityReal ρ) := by simp
      _ ≤ _ := lintegral_mono fun X => ENNReal.ofReal_le_ofReal
          (Real.exp_le_exp.2 (by linarith [abs_le.1 (hbd X)]))
  · calc _ ≤ ∫⁻ _ : Config d 1, ENNReal.ofReal (Real.exp (6 * βp * |Cc|))
            ∂(Measure.pi fun _ => withDensityReal ρ) :=
          lintegral_mono fun X => ENNReal.ofReal_le_ofReal
            (Real.exp_le_exp.2 (by linarith [abs_le.1 (hbd X)]))
      _ = _ := by simp

theorem pressure_all_unif (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (βm βp : ℝ) (hβm : 0 < βm)
    (hβ : βm ≤ βp) (c₀ : ℝ) (hc₀ : 0 < c₀) (Λ : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ρ : Torus d → ℝ, SmoothPosDensity ρ → (∀ x, c₀ ≤ ρ x) → (∀ x, ρ x ≤ Λ) →
      ∀ N : ℕ, 1 ≤ N → ∀ b ∈ Set.Icc (βm / 2) (2 * βp),
      ENNReal.ofReal (Real.exp (-(C * N * deltaN d s N))) ≤ Jint d s N b (withDensityReal ρ) ∧
        Jint d s N b (withDensityReal ρ) ≤ ENNReal.ofReal (Real.exp (C * N * deltaN d s N)) := by
  obtain ⟨B, hB⟩ := periodicRiesz_ge (d := d) hd hs0 hsd
  have hw : ∀ z : Torus d, z ≠ 0 → 1 ≤ periodicRiesz d s z + (B + 1) :=
    fun z _ => by linarith [hB z]
  obtain ⟨θ₀, θ₁, C2, hθ₀, hθ₁, H⟩ := perturbed_pressure_sup (by omega) s hs0 hsd (B + 1) hw
    (βm / 2) (2 * βp) (by positivity) c₀ hc₀ Λ 0
  obtain ⟨B', Cc, hB'0, hKall⟩ := NfU.kerData_periodicRiesz_unif hd hs0 hsd Λ
  have hβp : 0 ≤ βp := by linarith
  refine ⟨max (max C2 0) (6 * βp * |Cc|), (le_max_left _ _).trans' (le_max_right _ _),
    fun ρ hρ hlow hup N hN b hb => ?_⟩
  have hNd := one_le_mul_deltaN (d := d) hs0 N hN
  have hCnn : 0 ≤ max (max C2 0) (6 * βp * |Cc|) := (le_max_right C2 0).trans ((le_max_left _ _))
  have hCNd : max (max C2 0) (6 * βp * |Cc|) * N * deltaN d s N =
      max (max C2 0) (6 * βp * |Cc|) * ((N : ℝ) * deltaN d s N) := by ring
  rcases Nat.lt_or_ge N 2 with h | h
  · have hN1 : N = 1 := by omega
    subst hN1
    have hb0 : 0 ≤ b := by linarith [hb.1]
    obtain ⟨hl, hu⟩ := pressure_N1_kd hd hs0 hsd hρ (hKall ρ hρ hup) hβp hb0 hb.2
    have hCle : 6 * βp * |Cc| ≤ max (max C2 0) (6 * βp * |Cc|) *
        (((1 : ℕ) : ℝ) * deltaN d s 1) :=
      (le_max_right _ _).trans (by nlinarith [le_max_right (max C2 0) (6 * βp * |Cc|)])
    unfold Jint
    refine ⟨hl.trans' (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)),
      hu.trans (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_))⟩
    · rw [hCNd]; linarith
    · rw [hCNd]; linarith
  · have h2 : ENNReal.ofReal (Real.exp (-(C2 * N * deltaN d s N))) ≤ Jint d s N b (withDensityReal ρ) ∧
        Jint d s N b (withDensityReal ρ) ≤ ENNReal.ofReal (Real.exp (C2 * N * deltaN d s N)) := by
      have := (H ρ hρ.density hρ.smooth hlow hup (fun _ _ => 0) measurable_const
        (fun _ _ => rfl) (fun x y => by simp) N h b hb).1 0 (by simp [hθ₀.le])
      unfold Jint
      simpa [modulatedEnergyKernel] using this
    obtain ⟨hl, hu⟩ := h2
    have hC2le : C2 ≤ max (max C2 0) (6 * βp * |Cc|) := (le_max_left _ _).trans (le_max_left _ _)
    have hmono : C2 * N * deltaN d s N ≤ max (max C2 0) (6 * βp * |Cc|) * N * deltaN d s N := by
      have : 0 ≤ (N : ℝ) * deltaN d s N := by linarith
      nlinarith
    exact ⟨hl.trans' (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 (by linarith))),
      hu.trans (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 hmono))⟩

/-! ### Cavity marginals and pole versus Gibbs -/

theorem cavity_marginal_kd (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {β βp : ℝ} (hβ : 0 < β)
    (hββ : β ≤ βp) {ρ : Torus d → ℝ} (hρ : SmoothPosDensity ρ) {B Cc : ℝ} (hB0 : 0 ≤ B)
    (hK : KerData (periodicRiesz d s) (withDensityReal ρ) B Cc) :
    ∀ N : ℕ, 2 ≤ N → ∀ i : Fin (N - 1),
      (cavityLaw (periodicRiesz d s) (withDensityReal ρ) (N - 1) (β / N) β).map
          (fun Y : Config d (N - 1) => Y i) ≤
        ENNReal.ofReal (Real.exp (Kbound (periodicRiesz d s) B Cc βp 1)) • withDensityReal ρ := by
  have hμ := isProbabilityMeasure_mu hρ
  have hCc := hK.Cc_nonneg
  intro N hN i
  have h1 : (cavityLaw (periodicRiesz d s) (withDensityReal ρ) (N - 1) (β / N) β).map
          (fun Y : Config d (N - 1) => Y i) ≤
        ENNReal.ofReal (Real.exp (Kbound (periodicRiesz d s) B Cc β 1)) • withDensityReal ρ := by
    have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
    have hlam : 0 ≤ β / N := by positivity
    have hlb : β / N ≤ β := by
      rw [div_le_iff₀ hN0]
      have : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
      nlinarith
    have hln : β / N * ((N - 1 : ℕ) : ℝ) ≤ β := by
      rw [Nat.cast_sub (by omega : 1 ≤ N), Nat.cast_one]
      have : β / N * ((N : ℝ) - 1) = β - β / N := by field_simp
      rw [this]
      linarith
    haveI hP := pole_isProb hd hs0 hsd β hρ (N - 1) (β / N) hlam 0 0 le_rfl
    have h := pole_one_le hK hB0 i hβ.le le_rfl zero_le_one hlam hlb hln 0 (hP := hP)
    rw [poleLaw_zero_eq hd hs0 hsd β hρ _ _ hlam] at h
    refine h.trans (le_of_eq ?_)
    rw [← withDensity_const]
    congr 1
    funext y
    simp
  exact h1.trans (smul_mono_const _ (ENNReal.ofReal_le_ofReal
    (Real.exp_le_exp.2 (Kbound_mono hB0 hCc hββ))))

theorem coord_mean_kd (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (c β : ℝ)
    {ρ : Torus d → ℝ} (hρ : SmoothPosDensity ρ) (hc : ∀ z, 0 ≤ periodicRiesz d s z + c)
    {B Cc C1 : ℝ} (hK : KerData (periodicRiesz d s) (withDensityReal ρ) B Cc) (hC1 : 0 ≤ C1)
    (hmarg : ∀ N : ℕ, 2 ≤ N → ∀ i : Fin (N - 1),
      (cavityLaw (periodicRiesz d s) (withDensityReal ρ) (N - 1) (β / N) β).map
          (fun Y : Config d (N - 1) => Y i) ≤ ENNReal.ofReal C1 • withDensityReal ρ) :
    ∀ N : ℕ, 2 ≤ N → ∀ x : Torus d, ∀ i : Fin (N - 1),
      Integrable (fun Y : Config d (N - 1) => gPlus d s c (x - Y i)) (critCavity d s c β ρ N) ∧
        ∫ Y, gPlus d s c (x - Y i) ∂(critCavity d s c β ρ N) ≤ max 0 (C1 * (Cc + c)) := by
  have hμ := isProbabilityMeasure_mu hρ
  intro N hN x i
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
        rw [integral_smul_measure, ENNReal.toReal_ofReal hC1, smul_eq_mul]
        congr 1
        unfold gPlus convMeasure
        rw [integral_add (hK.int x) (integrable_const _)]
        simp
    _ ≤ max 0 (C1 * (Cc + c)) := le_max_of_le_right
        (mul_le_mul_of_nonneg_left (by linarith [(abs_le.1 (hK.conv x)).2]) hC1)

theorem pole_normalizer_kd (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (c β : ℝ) (hβ : 0 < β)
    {ρ : Torus d → ℝ} (hρ : SmoothPosDensity ρ) (hc : ∀ z, 0 ≤ periodicRiesz d s z + c)
    {A0 : ℝ} (hA0 : 0 ≤ A0)
    (hA : ∀ N : ℕ, 2 ≤ N → ∀ x : Torus d, ∀ i : Fin (N - 1),
      Integrable (fun Y : Config d (N - 1) => gPlus d s c (x - Y i)) (critCavity d s c β ρ N) ∧
        ∫ Y, gPlus d s c (x - Y i) ∂(critCavity d s c β ρ N) ≤ A0) :
    ∀ N : ℕ, 2 ≤ N → ∀ x : Torus d, ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ENNReal.ofReal (Real.exp (-(β * A0))) ≤ ∫⁻ Y : Config d (N - 1),
        ENNReal.ofReal (Real.exp (-(t * (β / N)) * ∑ i, gPlus d s c (x - Y i)))
          ∂(critCavity d s c β ρ N) := by
  have hgp : Measurable (gPlus d s c) := measurable_gPlus hd hs0 hsd c
  intro N hN x t ht
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

theorem cavity_le_gibbs_kd (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (β : ℝ) (hβ : 0 < β)
    {ρ : Torus d → ℝ} (hρ : SmoothPosDensity ρ) {B Cc : ℝ}
    (hK : KerData (periodicRiesz d s) (withDensityReal ρ) B Cc) :
    ∀ N : ℕ, 2 ≤ N →
      cavityLaw (periodicRiesz d s) (withDensityReal ρ) (N - 1) (β / N) β ≤
        ENNReal.ofReal (Real.exp (2 * (β * Cc))) • modulatedGibbs (periodicRiesz d s) (N - 1)
          (((N - 1 : ℕ) : ℝ) * β / N) (withDensityReal ρ) := by
  have hμ := isProbabilityMeasure_mu hρ
  have hCc := hK.Cc_nonneg
  intro N hN
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

/-- The pole law is bounded by a multiple of the Gibbs law; the multiple depends on `βp`, `c`, `Λ` only. -/
theorem pole_le_gibbs_unif (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (βm βp : ℝ) (hβm : 0 < βm)
    (hβ : βm ≤ βp) (Λ c : ℝ) (hc : ∀ z, 0 ≤ periodicRiesz d s z + c) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ β ∈ Set.Icc βm βp, ∀ ρ : Torus d → ℝ, SmoothPosDensity ρ →
      (∀ x, ρ x ≤ Λ) → ∀ N : ℕ, 2 ≤ N → ∀ x : Torus d, ∀ t ∈ Set.Icc (0 : ℝ) 1,
      critPole d s c β ρ N x t ≤ ENNReal.ofReal D • modulatedGibbs (periodicRiesz d s) (N - 1)
          (((N - 1 : ℕ) : ℝ) * β / N) (withDensityReal ρ) := by
  obtain ⟨B, Cc, hB0, hKall⟩ := NfU.kerData_periodicRiesz_unif hd hs0 hsd Λ
  have hgp : Measurable (gPlus d s c) := measurable_gPlus hd hs0 hsd c
  set C1 : ℝ := Real.exp (Kbound (periodicRiesz d s) B Cc βp 1) with hC1def
  have hC1 : 0 < C1 := Real.exp_pos _
  set A0 : ℝ := max 0 (C1 * (Cc + c)) with hA0def
  have hA0 : 0 ≤ A0 := le_max_left _ _
  refine ⟨Real.exp (βp * A0) * Real.exp (2 * (βp * Cc)), by positivity, ?_⟩
  intro β hβb ρ hρ hup N hN x t ht
  have hβ0 : 0 < β := lt_of_lt_of_le hβm hβb.1
  have hK := hKall ρ hρ hup
  have hμ := isProbabilityMeasure_mu hρ
  have hCc := hK.Cc_nonneg
  have hmarg := cavity_marginal_kd hd hs0 hsd hβ0 hβb.2 hρ hB0 hK
  have hcoord := coord_mean_kd hd hs0 hsd c β hρ hc hK hC1.le hmarg
  have hA := pole_normalizer_kd hd hs0 hsd c β hβ0 hρ hc hA0 hcoord
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hlam : 0 ≤ β / N := by positivity
  have h1 : critPole d s c β ρ N x t ≤
      ENNReal.ofReal (Real.exp (β * A0)) • critCavity d s c β ρ N := by
    have := tilt_le_of_nonpos (critCavity d s c β ρ N)
      (fun Y : Config d (N - 1) => -(t * (β / N)) * ∑ i, gPlus d s c (x - Y i))
      ((Finset.measurable_sum _ fun i _ =>
        hgp.comp (measurable_const.sub (measurable_pi_apply i))).const_mul _)
      (fun Y => by
        have h0 : 0 ≤ ∑ i, gPlus d s c (x - Y i) := Finset.sum_nonneg fun i _ => hc _
        have : 0 ≤ t * (β / N) := mul_nonneg ht.1 hlam
        nlinarith) (β * A0) (hA N hN x t ht)
    exact this
  have h2 : critCavity d s c β ρ N ≤ ENNReal.ofReal (Real.exp (2 * (β * Cc))) •
      modulatedGibbs (periodicRiesz d s) (N - 1)
      (((N - 1 : ℕ) : ℝ) * β / N) (withDensityReal ρ) := by
    rw [critCavity_eq hd hs0 hsd c β hρ N]; exact cavity_le_gibbs_kd hd hs0 hsd β hβ0 hρ hK N hN
  have h3 : ENNReal.ofReal (Real.exp (β * A0) * Real.exp (2 * (β * Cc))) ≤
      ENNReal.ofReal (Real.exp (βp * A0) * Real.exp (2 * (βp * Cc))) := by
    refine ENNReal.ofReal_le_ofReal (mul_le_mul (Real.exp_le_exp.2 ?_) (Real.exp_le_exp.2 ?_)
      (Real.exp_pos _).le (Real.exp_pos _).le)
    · exact mul_le_mul_of_nonneg_right hβb.2 hA0
    · have := mul_le_mul_of_nonneg_right hβb.2 hCc
      linarith
  calc critPole d s c β ρ N x t ≤ ENNReal.ofReal (Real.exp (β * A0)) • critCavity d s c β ρ N := h1
    _ ≤ ENNReal.ofReal (Real.exp (β * A0)) • (ENNReal.ofReal (Real.exp (2 * (β * Cc))) •
        modulatedGibbs (periodicRiesz d s) (N - 1)
        (((N - 1 : ℕ) : ℝ) * β / N) (withDensityReal ρ)) := measure_smul_le' _ h2
    _ = ENNReal.ofReal (Real.exp (β * A0) * Real.exp (2 * (β * Cc))) • modulatedGibbs (periodicRiesz d s) (N - 1)
        (((N - 1 : ℕ) : ℝ) * β / N) (withDensityReal ρ) := by
        rw [smul_smul, ← ENNReal.ofReal_mul (Real.exp_pos _).le]
    _ ≤ _ := smul_mono_const _ h3

end HRS.ME.Unif

end
