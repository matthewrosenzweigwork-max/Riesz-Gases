import HRS.Energy.Commutator.RoughHeat
import HRS.PDE.MeanFieldSchauder

/-!
# The slice kernel as a time integral: Fubini and integration by parts (packet CM-S3 helpers)

`𝒢_l = ∫_0^∞ e^{-lt} Ψ_t dt`, `∇𝒢_l = ∫_0^∞ e^{-lt} ∇Ψ_t dt`; the `u`-integrals of `Ψ_t`, `∇Ψ_t`
are `O(e^{-4π²t})`, `O(t^{-1/2} e^{-2π²t})`, so Fubini in `(u,t)` applies against bounded test
functions: `∫ 𝒢_l φ = ∫_t e^{-lt} ∫ Ψ_t φ`, and likewise for `∇𝒢_l`.  Consequences: `𝒢_l, ∇𝒢_l ∈ L¹`
and `∫ 𝒢_l ∂_iφ = -∫ ∂_i𝒢_l φ` for `φ ∈ C¹`.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators
open HRS HRS.KernelAux HRS.Commutator.FourierAux HRS.Commutator.RoughAux HRS.Commutator.RoughHeat

namespace HRS.Commutator.RoughKernel

variable {d : ℕ}

/-- Integrability on the product `𝕋^d × (0,∞)`. -/
theorem prod_integrable_time {F : Torus d → ℝ → ℝ} (hm : Measurable fun p : Torus d × ℝ => F p.1 p.2)
    {g : ℝ → ℝ} (hg : IntegrableOn g (Ioi 0)) (hint : ∀ t, 0 < t → Integrable (fun u => F u t))
    (hbd : ∀ t, 0 < t → ∫ u, |F u t| ≤ g t) :
    Integrable (fun p : Torus d × ℝ => F p.1 p.2)
      ((volume : Measure (Torus d)).prod (volume.restrict (Ioi (0 : ℝ)))) := by
  rw [integrable_prod_iff' hm.aestronglyMeasurable]
  refine ⟨?_, ?_⟩
  · rw [ae_restrict_iff' measurableSet_Ioi]
    exact Filter.Eventually.of_forall fun t ht => hint t ht
  · refine Integrable.mono' hg ?_ ?_
    · have : Measurable fun p : Torus d × ℝ => ‖F p.1 p.2‖ := hm.norm
      exact (this.stronglyMeasurable.integral_prod_left' (μ := (volume : Measure (Torus d)))).aestronglyMeasurable
    · rw [ae_restrict_iff' measurableSet_Ioi]
      refine Filter.Eventually.of_forall fun t ht => ?_
      rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun u => norm_nonneg _)]
      simpa using hbd t ht

/-- Fubini between a torus variable and a time variable. -/
theorem swap_time {F : Torus d → ℝ → ℝ} (hm : Measurable fun p : Torus d × ℝ => F p.1 p.2)
    {g : ℝ → ℝ} (hg : IntegrableOn g (Ioi 0)) (hint : ∀ t, 0 < t → Integrable (fun u => F u t))
    (hbd : ∀ t, 0 < t → ∫ u, |F u t| ≤ g t) :
    ∫ u, ∫ t in Ioi (0 : ℝ), F u t = ∫ t in Ioi (0 : ℝ), ∫ u, F u t :=
  integral_integral_swap (prod_integrable_time hm hg hint hbd)

theorem measurable_psiG_uncurry' (j : Fin d) :
    Measurable fun p : Torus d × ℝ => psiG j p.1 (4 * Real.pi ^ 2 * p.2) :=
  (SliceAux.measurable_psiG_uncurry j).comp (measurable_fst.prodMk (measurable_const.mul measurable_snd))

theorem continuous_psiG (j : Fin d) {a : ℝ} (ha : 0 < a) : Continuous fun x : Torus d => psiG j x a := by
  unfold psiG
  refine continuous_tsum (u := fun k : Lattice d => 2 * Real.pi * (Lattice.enorm k ^ 1 *
      Real.exp (-a * Lattice.enorm k ^ 2))) (fun k => ?_) ((summable_pow_gauss_lattice d ha 1).mul_left (2 * Real.pi))
    (fun k x => ?_)
  · exact (continuous_const.mul (Torus.continuous_sinMode k)).neg
  · refine (psiG_term_bound j x k a).trans ?_
    rw [pow_one, ← mul_assoc]

/-- `∫ |Ψ_t| ≤ C e^{-4π²t}`. -/
theorem int_abs_psi_le (d : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 0 < t →
    ∫ u : Torus d, |psiFn u (4 * Real.pi ^ 2 * t)| ≤ C * Real.exp (-(4 * Real.pi ^ 2 * t)) := by
  obtain ⟨K, hK0, hK⟩ := HeatAux.abs_psiFn_le_exp d
  refine ⟨max (2 * Real.exp 1) K, by positivity, fun t ht => ?_⟩
  have hu : 0 < 4 * Real.pi ^ 2 * t := by positivity
  set a := 4 * Real.pi ^ 2 * t with ha
  have hcont0 : Continuous fun u : Torus d => psiFn u a := EnergyAux.continuous_psiFn hu
  have hint : Integrable (fun u : Torus d => |psiFn u a|) :=
    hcont0.abs.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  rcases le_total 1 a with h1 | h1
  · calc ∫ u : Torus d, |psiFn u a| ≤ ∫ _u : Torus d, K * Real.exp (-a) :=
          integral_mono hint (integrable_const _) fun u => hK u a h1
      _ = K * Real.exp (-a) := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.exp_pos _).le
  · have hθ : ∀ u : Torus d, |psiFn u a| ≤ (1 + psiFn u a) + 1 := fun u => by
      have := EnergyAux.one_add_psiFn_nonneg' u hu
      rw [abs_le]; constructor <;> linarith [abs_nonneg (psiFn u a)]
    have hint2 : Integrable (fun u : Torus d => (1 + psiFn u a) + 1) :=
      ((integrable_const _).add (hcont0.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))).add
        (integrable_const _)
    calc ∫ u : Torus d, |psiFn u a| ≤ ∫ u : Torus d, ((1 + psiFn u a) + 1) := integral_mono hint hint2 hθ
      _ = 2 := by
          have hi1 : Integrable (fun u : Torus d => 1 + psiFn u a) :=
            (integrable_const (1 : ℝ)).add (hcont0.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
          rw [integral_add hi1 (integrable_const _), EnergyAux.integral_one_add_psiFn_aux hu]
          simp; norm_num
      _ ≤ 2 * Real.exp 1 * Real.exp (-a) := by
          have : 1 ≤ Real.exp 1 * Real.exp (-a) := by
            rw [← Real.exp_add]; exact Real.one_le_exp (by linarith)
          nlinarith
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le

/-- `∫ |∂_jΨ_t| ≤ C₁ t^{-1/2} e^{-2π²t} + C₂ e^{-4π²t}`. -/
theorem int_abs_psiG_le (d : ℕ) (j : Fin d) : ∃ C₁ C₂ : ℝ, 0 ≤ C₁ ∧ 0 ≤ C₂ ∧ ∀ t : ℝ, 0 < t →
    ∫ u : Torus d, |psiG j u (4 * Real.pi ^ 2 * t)| ≤
      C₁ * (t ^ (-(1 / 2 : ℝ)) * Real.exp (-(t * (2 * Real.pi ^ 2)))) + C₂ * Real.exp (-(4 * Real.pi ^ 2 * t)) := by
  obtain ⟨M, hM0, hM⟩ := psiG_large_bound (d := d) j
  refine ⟨Real.sqrt 2 ^ d * Real.exp 1, M, by positivity, hM0, fun t ht => ?_⟩
  have hu : 0 < 4 * Real.pi ^ 2 * t := by positivity
  set a := 4 * Real.pi ^ 2 * t with ha
  have hcont : Continuous fun u : Torus d => psiG j u a := continuous_psiG j hu
  have hint : Integrable (fun u : Torus d => |psiG j u a|) :=
    hcont.abs.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hpos : 0 ≤ Real.sqrt 2 ^ d * Real.exp 1 * (t ^ (-(1 / 2 : ℝ)) * Real.exp (-(t * (2 * Real.pi ^ 2)))) := by
    positivity
  have hpos2 : 0 ≤ M * Real.exp (-(4 * Real.pi ^ 2 * t)) := by positivity
  rcases le_total 1 a with h1 | h1
  · calc ∫ u : Torus d, |psiG j u a| ≤ ∫ _u : Torus d, M * Real.exp (-a) :=
          integral_mono hint (integrable_const _) fun u => hM u a h1
      _ = M * Real.exp (-a) := by simp
      _ ≤ _ := by linarith
  · have hb : ∀ u : Torus d, |psiG j u a| ≤
        2 * Real.pi / Real.sqrt a * Real.sqrt 2 ^ d * (1 + psiFn u (2 * a)) := fun u =>
      HeatAux.abs_psiG_theta j u hu
    have hint2 : Integrable (fun u : Torus d => 2 * Real.pi / Real.sqrt a * Real.sqrt 2 ^ d * (1 + psiFn u (2 * a))) :=
      (((integrable_const (1 : ℝ)).add ((EnergyAux.continuous_psiFn (by positivity : 0 < 2 * a)).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _))).const_mul _)
    have hsq : Real.sqrt a = 2 * Real.pi * Real.sqrt t := by
      rw [ha, show 4 * Real.pi ^ 2 * t = (2 * Real.pi) ^ 2 * t by ring, Real.sqrt_mul (by positivity),
        Real.sqrt_sq (by positivity)]
    have hsqt : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
    calc ∫ u : Torus d, |psiG j u a| ≤ ∫ u : Torus d, 2 * Real.pi / Real.sqrt a * Real.sqrt 2 ^ d * (1 + psiFn u (2 * a)) :=
          integral_mono hint hint2 hb
      _ = 2 * Real.pi / Real.sqrt a * Real.sqrt 2 ^ d := by
          rw [integral_const_mul, EnergyAux.integral_one_add_psiFn_aux (by positivity), mul_one]
      _ = Real.sqrt 2 ^ d * t ^ (-(1 / 2 : ℝ)) := by
          rw [hsq, Real.rpow_neg ht.le, ← Real.sqrt_eq_rpow]
          field_simp
      _ ≤ Real.sqrt 2 ^ d * Real.exp 1 * (t ^ (-(1 / 2 : ℝ)) * Real.exp (-(t * (2 * Real.pi ^ 2)))) := by
          have h2 : 1 ≤ Real.exp 1 * Real.exp (-(t * (2 * Real.pi ^ 2))) := by
            rw [← Real.exp_add]; apply Real.one_le_exp
            have : t * (4 * Real.pi ^ 2) ≤ 1 := by rw [ha] at h1; linarith
            nlinarith [Real.pi_pos]
          have h3 : 0 ≤ Real.sqrt 2 ^ d * t ^ (-(1 / 2 : ℝ)) := by positivity
          calc Real.sqrt 2 ^ d * t ^ (-(1 / 2 : ℝ)) ≤ Real.sqrt 2 ^ d * t ^ (-(1 / 2 : ℝ)) *
                (Real.exp 1 * Real.exp (-(t * (2 * Real.pi ^ 2)))) := le_mul_of_one_le_right h3 h2
            _ = _ := by ring
      _ ≤ _ := by linarith


/-- Fubini for `∫ u (∫_t e^{-lt} Φ(u,t)) φ(u)`. -/
theorem tf_gen {Φ : Torus d → ℝ → ℝ} (hΦ : Measurable fun p : Torus d × ℝ => Φ p.1 p.2)
    (hΦc : ∀ t, 0 < t → Continuous fun u => Φ u t) {g : ℝ → ℝ} (hg : IntegrableOn g (Ioi 0))
    (hbd : ∀ t, 0 < t → ∫ u, |Φ u t| ≤ g t) {l : ℝ} (hl : 0 ≤ l) {φ : Torus d → ℝ}
    (hφm : Measurable φ) {B : ℝ} (hB : ∀ u, |φ u| ≤ B) :
    ∫ u, (∫ t in Ioi (0 : ℝ), Real.exp (-l * t) * Φ u t) * φ u =
      ∫ t in Ioi (0 : ℝ), Real.exp (-l * t) * ∫ u, Φ u t * φ u := by
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  have h1 : ∀ u, (∫ t in Ioi (0 : ℝ), Real.exp (-l * t) * Φ u t) * φ u =
      ∫ t in Ioi (0 : ℝ), Real.exp (-l * t) * Φ u t * φ u := fun u => by
    rw [integral_mul_const]
  simp_rw [h1]
  have hint : ∀ t, 0 < t → Integrable (fun u => Real.exp (-l * t) * Φ u t * φ u) := by
    intro t ht
    have hc := hΦc t ht
    have : Integrable (fun u => Real.exp (-l * t) * Φ u t) :=
      (continuous_const.mul hc).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    exact this.mul_bdd (c := B) hφm.aestronglyMeasurable (Filter.Eventually.of_forall fun u => by
      simpa using hB u)
  have hgt : ∀ t, 0 < t → 0 ≤ g t := fun t ht =>
    (integral_nonneg fun u => abs_nonneg _).trans (hbd t ht)
  have hgi : IntegrableOn (fun t => B * (Real.exp (-l * t) * g t)) (Ioi 0) := by
    refine Integrable.const_mul ?_ _
    refine Integrable.mono' hg ?_ ?_
    · exact ((by fun_prop : Continuous fun t : ℝ => Real.exp (-l * t)).aestronglyMeasurable).mul hg.aestronglyMeasurable
    · rw [ae_restrict_iff' measurableSet_Ioi]
      refine Filter.Eventually.of_forall fun t ht => ?_
      have ht' : (0 : ℝ) < t := ht
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _), abs_of_nonneg (hgt t ht')]
      have : Real.exp (-l * t) ≤ 1 := by rw [Real.exp_le_one_iff]; nlinarith
      calc Real.exp (-l * t) * g t ≤ 1 * g t := mul_le_mul_of_nonneg_right this (hgt t ht')
        _ = g t := one_mul _
  have hm : Measurable fun p : Torus d × ℝ => Real.exp (-l * p.2) * Φ p.1 p.2 * φ p.1 :=
    ((Real.measurable_exp.comp (measurable_const.mul measurable_snd)).mul hΦ).mul (hφm.comp measurable_fst)
  rw [swap_time (F := fun u t => Real.exp (-l * t) * Φ u t * φ u) hm hgi hint ?_]
  · refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    rw [← integral_const_mul]
    exact integral_congr_ae (Filter.Eventually.of_forall fun u => by ring)
  · intro t ht
    calc ∫ u, |Real.exp (-l * t) * Φ u t * φ u| ≤ ∫ u, Real.exp (-l * t) * |Φ u t| * B := by
          refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun u => abs_nonneg _) ?_
            (Filter.Eventually.of_forall fun u => ?_)
          · have : Integrable fun u => |Φ u t| :=
              (hΦc t ht).abs.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
            exact (this.const_mul _).mul_const _
          · show |Real.exp (-l * t) * Φ u t * φ u| ≤ Real.exp (-l * t) * |Φ u t| * B
            rw [abs_mul, abs_mul, abs_of_pos (Real.exp_pos _)]
            exact mul_le_mul_of_nonneg_left (hB u) (by positivity)
      _ = B * (Real.exp (-l * t) * ∫ u, |Φ u t|) := by
          rw [integral_mul_const, integral_const_mul]; ring
      _ ≤ B * (Real.exp (-l * t) * g t) := by
          gcongr
          exact hbd t ht

theorem integrableOn_Ioi_exp_neg (c : ℝ) (hc : 0 < c) :
    IntegrableOn (fun t : ℝ => Real.exp (-(c * t))) (Ioi 0) := by
  have := integrableOn_exp_mul_Ioi (a := -c) (by linarith) (0 : ℝ)
  refine this.congr_fun (fun t _ => ?_) measurableSet_Ioi
  simp [neg_mul]

/-- `∫ 𝒢_l φ = ∫_t e^{-lt} ∫ Ψ_t φ`. -/
theorem tf_sliceG {l : ℝ} (hl : 0 ≤ l) {φ : Torus d → ℝ} (hφm : Measurable φ) {B : ℝ}
    (hB : ∀ u, |φ u| ≤ B) :
    ∫ u, sliceG d l u * φ u =
      ∫ t in Ioi (0 : ℝ), Real.exp (-l * t) * ∫ u, psiFn u (4 * Real.pi ^ 2 * t) * φ u := by
  obtain ⟨C, hC0, hC⟩ := int_abs_psi_le d
  have hm : Measurable fun p : Torus d × ℝ => psiFn p.1 (4 * Real.pi ^ 2 * p.2) :=
    EnergyAux.measurable_psiFn_uncurry.comp (measurable_fst.prodMk (measurable_const.mul measurable_snd))
  have hc : ∀ t : ℝ, 0 < t → Continuous fun u : Torus d => psiFn u (4 * Real.pi ^ 2 * t) :=
    fun t ht => EnergyAux.continuous_psiFn (by positivity)
  have hg : IntegrableOn (fun t : ℝ => C * Real.exp (-(4 * Real.pi ^ 2 * t))) (Ioi 0) :=
    (integrableOn_Ioi_exp_neg _ (by positivity)).const_mul C
  exact tf_gen (Φ := fun u t => psiFn u (4 * Real.pi ^ 2 * t)) hm hc hg (fun t ht => hC t ht) hl hφm hB

/-- `∫ ∂_j𝒢_l φ = ∫_t e^{-lt} ∫ ∂_jΨ_t φ`. -/
theorem tf_sgc (j : Fin d) {l : ℝ} (hl : 0 ≤ l) {φ : Torus d → ℝ} (hφm : Measurable φ) {B : ℝ}
    (hB : ∀ u, |φ u| ≤ B) :
    ∫ u, SliceAux.sgc j l u * φ u =
      ∫ t in Ioi (0 : ℝ), Real.exp (-l * t) * ∫ u, psiG j u (4 * Real.pi ^ 2 * t) * φ u := by
  obtain ⟨C₁, C₂, hC1, hC2, hC⟩ := int_abs_psiG_le d j
  have hI : IntegrableOn (fun t : ℝ => C₁ * (t ^ (-(1 / 2 : ℝ)) * Real.exp (-(t * (2 * Real.pi ^ 2)))) +
      C₂ * Real.exp (-(4 * Real.pi ^ 2 * t))) (Ioi 0) :=
    ((SliceAux.integrableOn_laplace (β := 1 / 2) (t := 2 * Real.pi ^ 2) (by norm_num) (by positivity)).const_mul C₁).add
      ((integrableOn_Ioi_exp_neg _ (by positivity)).const_mul C₂)
  have hc : ∀ t : ℝ, 0 < t → Continuous fun u : Torus d => psiG j u (4 * Real.pi ^ 2 * t) :=
    fun t ht => continuous_psiG j (by positivity)
  exact tf_gen (Φ := fun u t => psiG j u (4 * Real.pi ^ 2 * t)) (measurable_psiG_uncurry' j) hc hI
    (fun t ht => hC t ht) hl hφm hB

/-! ### The regularised Green function as a time integral -/

theorem integral_exp_Ioi {a : ℝ} (ha : 0 < a) (ε : ℝ) :
    ∫ t in Ioi ε, Real.exp (-(a * t)) = Real.exp (-(a * ε)) / a := by
  have := integral_exp_mul_Ioi (a := -a) (by linarith) ε
  simp only [neg_mul] at this
  rw [this, neg_div, ← div_neg, neg_neg]

theorem integrableOn_exp_Ioi {a : ℝ} (ha : 0 < a) (ε : ℝ) :
    IntegrableOn (fun t : ℝ => Real.exp (-(a * t))) (Ioi ε) := by
  have := integrableOn_exp_mul_Ioi (a := -a) (by linarith) ε
  refine this.congr_fun (fun t _ => ?_) measurableSet_Ioi
  simp [neg_mul]

theorem cW_zero_mode (l ε : ℝ) : cW l ε (0 : Lattice d) = Real.exp (-(l * ε)) / l := by
  unfold cW
  by_cases hl : l = 0
  · simp [hl]
  · simp [hl, enorm_zero', mul_comm]

theorem ser_cW_eq {l : ℝ} (hl : 0 ≤ l) {ε : ℝ} (hε : 0 < ε) (w : Torus d) :
    ser (cW l ε) w = (∫ t in Ioi ε, Real.exp (-l * t) * psiFn w (4 * Real.pi ^ 2 * t)) +
      Real.exp (-(l * ε)) / l := by
  have hc0 : 0 < 4 * Real.pi ^ 2 * ε := by positivity
  set μ : Measure ℝ := volume.restrict (Ioi ε) with hμ
  set Fk : Lattice d → ℝ → ℝ := fun k t => Real.exp (-l * t) *
    (if k = 0 then 0 else Real.exp (-(4 * Real.pi ^ 2 * t) * Lattice.enorm k ^ 2) * Torus.cosMode k w) with hFk
  have hden : ∀ k : Lattice d, k ≠ 0 → 0 < l + 4 * Real.pi ^ 2 * Lattice.enorm k ^ 2 :=
    fun k hk => denom_pos hl (fun h => hk h.2)
  -- exact integrals
  have hnorm : ∀ k : Lattice d, k ≠ 0 → ∀ t : ℝ, ‖Fk k t‖ ≤ Real.exp (-((l + 4 * Real.pi ^ 2 * Lattice.enorm k ^ 2) * t)) := by
    intro k hk t
    simp only [hFk, hk, ite_false, Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    calc Real.exp (-l * t) * (Real.exp (-(4 * Real.pi ^ 2 * t) * Lattice.enorm k ^ 2) * |Torus.cosMode k w|)
        ≤ Real.exp (-l * t) * (Real.exp (-(4 * Real.pi ^ 2 * t) * Lattice.enorm k ^ 2) * 1) := by
          gcongr; exact HRS.abs_cosMode_le k w
      _ = _ := by rw [mul_one, ← Real.exp_add]; congr 1; ring
  have hint : ∀ k : Lattice d, Integrable (Fk k) μ := by
    intro k
    by_cases hk : k = 0
    · simp [hFk, hk]
    · have hI := integrableOn_exp_Ioi (hden k hk) ε
      refine Integrable.mono' hI ?_ ?_
      · refine (Continuous.aestronglyMeasurable ?_)
        simp only [hFk, hk, ite_false]
        fun_prop
      · rw [hμ, ae_restrict_iff' measurableSet_Ioi]
        exact Filter.Eventually.of_forall fun t _ => hnorm k hk t
  have hexact : ∀ k : Lattice d, ∫ t, Fk k t ∂μ = if k = 0 then 0 else cW l ε k * Torus.cosMode k w := by
    intro k
    by_cases hk : k = 0
    · simp [hFk, hk]
    · simp only [hk, ite_false]
      have hD := hden k hk
      have h1 : ∀ t : ℝ, Fk k t = Torus.cosMode k w *
          Real.exp (-((l + 4 * Real.pi ^ 2 * Lattice.enorm k ^ 2) * t)) := by
        intro t
        simp only [hFk, hk, ite_false]
        rw [mul_comm (Real.exp _) (Torus.cosMode k w), ← mul_assoc, mul_comm (Real.exp (-l * t)), mul_assoc,
          ← Real.exp_add]
        congr 2; ring
      simp_rw [h1]
      rw [hμ, integral_const_mul, integral_exp_Ioi hD, cW, if_neg (fun h => hk h.2),
        show -((l + 4 * Real.pi ^ 2 * Lattice.enorm k ^ 2) * ε) =
          -ε * (l + 4 * Real.pi ^ 2 * Lattice.enorm k ^ 2) by ring]
      ring
  have hsumN : Summable fun k : Lattice d => ∫ t, ‖Fk k t‖ ∂μ := by
    have hcs : Summable fun k : Lattice d => |cW l ε k| := by
      refine Summable.of_nonneg_of_le (fun k => abs_nonneg _) (fun k => cW_bound hl hε.le k)
        ((summable_gauss_lattice d _ hc0).mul_left _)
    refine Summable.of_nonneg_of_le (fun k => integral_nonneg fun t => norm_nonneg _) (fun k => ?_) hcs
    by_cases hk : k = 0
    · simp [hFk, hk]
    · have hD := hden k hk
      calc ∫ t, ‖Fk k t‖ ∂μ ≤ ∫ t, Real.exp (-((l + 4 * Real.pi ^ 2 * Lattice.enorm k ^ 2) * t)) ∂μ := by
            refine integral_mono (hint k).norm (by rw [hμ]; exact integrableOn_exp_Ioi hD ε) fun t => hnorm k hk t
        _ = cW l ε k := by
            rw [hμ, integral_exp_Ioi hD, cW, if_neg (fun h => hk h.2),
              show -((l + 4 * Real.pi ^ 2 * Lattice.enorm k ^ 2) * ε) =
                -ε * (l + 4 * Real.pi ^ 2 * Lattice.enorm k ^ 2) by ring]
        _ = |cW l ε k| := (abs_of_nonneg (cW_nonneg hl ε k)).symm
  have h1 := integral_tsum_of_summable_integral_norm hint hsumN
  simp_rw [hexact] at h1
  -- the pointwise identification of the sum
  have hpt : ∀ t : ℝ, 0 < t → ∑' k, Fk k t = Real.exp (-l * t) * psiFn w (4 * Real.pi ^ 2 * t) := by
    intro t ht
    simp only [hFk]
    rw [tsum_mul_left]
    rfl
  have h2 : ∫ t, (∑' k, Fk k t) ∂μ = ∫ t in Ioi ε, Real.exp (-l * t) * psiFn w (4 * Real.pi ^ 2 * t) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => hpt t (lt_trans hε ht)
  rw [h2] at h1
  -- the series
  have hcs : Summable fun k : Lattice d => cW l ε k * Torus.cosMode k w := by
    refine Summable.of_norm_bounded (g := fun k => |cW l ε k|) ?_ fun k => ?_
    · refine Summable.of_nonneg_of_le (fun k => abs_nonneg _) (fun k => cW_bound hl hε.le k)
        ((summable_gauss_lattice d _ hc0).mul_left _)
    · rw [Real.norm_eq_abs, abs_mul]
      calc |cW l ε k| * |Torus.cosMode k w| ≤ |cW l ε k| * 1 := by gcongr; exact HRS.abs_cosMode_le k w
        _ = _ := mul_one _
  have hind : Summable fun k : Lattice d => if k = 0 then cW l ε k * Torus.cosMode k w else 0 :=
    summable_of_ne_finset_zero (s := {0}) (fun k hk => by simp at hk; simp [hk])
  have hsplit : ∀ k : Lattice d, cW l ε k * Torus.cosMode k w =
      (if k = 0 then cW l ε k * Torus.cosMode k w else 0) +
        (if k = 0 then 0 else cW l ε k * Torus.cosMode k w) := by
    intro k; by_cases hk : k = 0 <;> simp [hk]
  have hrest : Summable fun k : Lattice d => (if k = 0 then 0 else cW l ε k * Torus.cosMode k w) := by
    have := hcs.sub hind
    refine this.congr fun k => ?_
    by_cases hk : k = 0 <;> simp [hk]
  have hser : ser (cW l ε) w = ∑' k : Lattice d, ((if k = 0 then cW l ε k * Torus.cosMode k w else 0) +
      (if k = 0 then 0 else cW l ε k * Torus.cosMode k w)) := tsum_congr hsplit
  rw [hser, (hind.hasSum.add hrest.hasSum).tsum_eq, tsum_ite_eq]
  have hrest_eq : ∑' k : Lattice d, (if k = 0 then 0 else cW l ε k * Torus.cosMode k w) =
      ∫ t in Ioi ε, Real.exp (-l * t) * psiFn w (4 * Real.pi ^ 2 * t) := by
    exact h1
  rw [hrest_eq, cW_zero_mode]
  have hc : Torus.cosMode (0 : Lattice d) w = 1 := by simp [Torus.cosMode, Torus.mode_zero]
  rw [hc, mul_one, add_comm]


/-- `u ↦ ∫_t e^{-lt} Φ(u,t) dt` is integrable. -/
theorem integrable_gen {Φ : Torus d → ℝ → ℝ} (hΦ : Measurable fun p : Torus d × ℝ => Φ p.1 p.2)
    (hΦc : ∀ t, 0 < t → Continuous fun u => Φ u t) {g : ℝ → ℝ} (hg : IntegrableOn g (Ioi 0))
    (hbd : ∀ t, 0 < t → ∫ u, |Φ u t| ≤ g t) {l : ℝ} (hl : 0 ≤ l) :
    Integrable fun u => ∫ t in Ioi (0 : ℝ), Real.exp (-l * t) * Φ u t := by
  have hgt : ∀ t, 0 < t → 0 ≤ g t := fun t ht =>
    (integral_nonneg fun u => abs_nonneg _).trans (hbd t ht)
  have hm : Measurable fun p : Torus d × ℝ => Real.exp (-l * p.2) * Φ p.1 p.2 :=
    (Real.measurable_exp.comp (measurable_const.mul measurable_snd)).mul hΦ
  have hI := prod_integrable_time (F := fun u t => Real.exp (-l * t) * Φ u t) hm hg
    (fun t ht => (continuous_const.mul (hΦc t ht)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)) (fun t ht => by
      calc ∫ u, |Real.exp (-l * t) * Φ u t| = Real.exp (-l * t) * ∫ u, |Φ u t| := by
            rw [← integral_const_mul]
            exact integral_congr_ae (Filter.Eventually.of_forall fun u => by
              simp only [abs_mul, abs_of_pos (Real.exp_pos _)])
        _ ≤ 1 * g t := by
            have : Real.exp (-l * t) ≤ 1 := by rw [Real.exp_le_one_iff]; nlinarith
            exact mul_le_mul this (hbd t ht) (integral_nonneg fun u => abs_nonneg _) zero_le_one
        _ = g t := one_mul _)
  exact hI.integral_prod_left

theorem integrable_sliceG {l : ℝ} (hl : 0 ≤ l) : Integrable (sliceG d l : Torus d → ℝ) := by
  obtain ⟨C, hC0, hC⟩ := int_abs_psi_le d
  have hm : Measurable fun p : Torus d × ℝ => psiFn p.1 (4 * Real.pi ^ 2 * p.2) :=
    EnergyAux.measurable_psiFn_uncurry.comp (measurable_fst.prodMk (measurable_const.mul measurable_snd))
  have hc : ∀ t : ℝ, 0 < t → Continuous fun u : Torus d => psiFn u (4 * Real.pi ^ 2 * t) :=
    fun t ht => EnergyAux.continuous_psiFn (by positivity)
  have hg : IntegrableOn (fun t : ℝ => C * Real.exp (-(4 * Real.pi ^ 2 * t))) (Ioi 0) :=
    (integrableOn_Ioi_exp_neg _ (by positivity)).const_mul C
  exact integrable_gen (Φ := fun u t => psiFn u (4 * Real.pi ^ 2 * t)) hm hc hg (fun t ht => hC t ht) hl

theorem integrable_sliceGfull {l : ℝ} (hl : 0 ≤ l) : Integrable (sliceGfull d l : Torus d → ℝ) :=
  (integrable_sliceG hl).add (integrable_const _)

theorem integrable_sgc (j : Fin d) {l : ℝ} (hl : 0 ≤ l) : Integrable (SliceAux.sgc j l : Torus d → ℝ) := by
  obtain ⟨C₁, C₂, hC1, hC2, hC⟩ := int_abs_psiG_le d j
  have hI : IntegrableOn (fun t : ℝ => C₁ * (t ^ (-(1 / 2 : ℝ)) * Real.exp (-(t * (2 * Real.pi ^ 2)))) +
      C₂ * Real.exp (-(4 * Real.pi ^ 2 * t))) (Ioi 0) :=
    ((SliceAux.integrableOn_laplace (β := 1 / 2) (t := 2 * Real.pi ^ 2) (by norm_num) (by positivity)).const_mul C₁).add
      ((integrableOn_Ioi_exp_neg _ (by positivity)).const_mul C₂)
  have hc : ∀ t : ℝ, 0 < t → Continuous fun u : Torus d => psiG j u (4 * Real.pi ^ 2 * t) :=
    fun t ht => continuous_psiG j (by positivity)
  exact integrable_gen (Φ := fun u t => psiG j u (4 * Real.pi ^ 2 * t)) (measurable_psiG_uncurry' j) hc hI
    (fun t ht => hC t ht) hl

/-! ### Calculus of `Ψ_t` -/

theorem integral_Ioi_shift (f : ℝ → ℝ) (ε : ℝ) :
    ∫ t in Ioi (0 : ℝ), f (t + ε) = ∫ s in Ioi ε, f s := by
  rw [← integral_indicator measurableSet_Ioi, ← integral_indicator measurableSet_Ioi,
    ← integral_add_right_eq_self (fun s => (Ioi ε).indicator f s) ε]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  simp only [indicator, mem_Ioi]
  by_cases ht : 0 < t
  · simp [ht]
  · have : ¬ ε < t + ε := by intro h; exact ht (by linarith)
    simp [ht, this]

theorem psiFn_eq_hk {a : ℝ} (ha : 0 < a) (x : Torus d) :
    psiFn x a = hk (a / (4 * Real.pi ^ 2)) x - 1 := by
  have hε : 0 < a / (4 * Real.pi ^ 2) := by positivity
  rw [hk_eq hε, show 4 * Real.pi ^ 2 * (a / (4 * Real.pi ^ 2)) = a by field_simp]
  ring

theorem isCk_hk {ε : ℝ} (hε : 0 < ε) : Torus.IsCk 1 (hk (d := d) ε) := by
  have := isCk_ser' (d := d) 1 (aW_gauss hε) (aW_even ε)
  show Torus.IsCk 1 (ser (aW ε))
  simpa using this

theorem isCk_psiFn {a : ℝ} (ha : 0 < a) : Torus.IsCk 1 (fun x : Torus d => psiFn x a) := by
  have hε : 0 < a / (4 * Real.pi ^ 2) := by positivity
  have h1 := isCk_hk (d := d) hε
  have e : (fun x : Torus d => psiFn x a) = fun x => hk (a / (4 * Real.pi ^ 2)) x - 1 :=
    funext fun x => psiFn_eq_hk ha x
  rw [e]
  unfold Torus.IsCk Torus.lift at h1 ⊢
  exact h1.sub contDiff_const

theorem partialDeriv_psiFn {a : ℝ} (ha : 0 < a) (i : Fin d) (x : Torus d) :
    Torus.partialDeriv i (fun x : Torus d => psiFn x a) x = psiG i x a := by
  have h := SliceAux.hasFDerivAt_psiFn ha (Torus.rep x)
  unfold Torus.partialDeriv
  have e : Torus.lift (fun x : Torus d => psiFn x a) = fun y : Euc d => psiFn (Torus.mk y) a := rfl
  rw [e, h.fderiv, SliceAux.psiGrad_apply]
  simp [Torus.mk_rep, PiLp.single_apply]


/-! ### Convolution of the slice kernel with the heat kernel -/

theorem integral_hk_sub (ε : ℝ) (hε : 0 < ε) (w : Torus d) : ∫ u, hk ε (w - u) = 1 := by
  rw [integral_sub_left_eq_self (fun u => hk ε u) volume w, integral_hk hε]

theorem integral_psi_mul_hk {t : ℝ} (ht : 0 < t) {ε : ℝ} (hε : 0 < ε) (w : Torus d) :
    ∫ u, psiFn u (4 * Real.pi ^ 2 * t) * hk ε (w - u) = psiFn w (4 * Real.pi ^ 2 * (ε + t)) := by
  have hpsi : ∀ u : Torus d, psiFn u (4 * Real.pi ^ 2 * t) = hk t u - 1 := fun u => by
    rw [hk_eq ht]; ring
  simp_rw [hpsi, sub_mul, one_mul]
  have hi1 : Integrable (fun u : Torus d => hk t u * hk ε (w - u)) :=
    ((continuous_hk ht).mul ((continuous_hk hε).comp (continuous_const.sub continuous_id))).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hi2 : Integrable (fun u : Torus d => hk ε (w - u)) :=
    ((continuous_hk hε).comp (continuous_const.sub continuous_id)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  rw [integral_sub hi1 hi2, integral_hk_sub ε hε w]
  have : ∫ u, hk t u * hk ε (w - u) = hk (ε + t) w := by
    rw [← hk_semigroup hε ht w]
    exact integral_congr_ae (Filter.Eventually.of_forall fun u => mul_comm _ _)
  rw [this, hk_eq (by positivity : 0 < ε + t)]
  ring

/-- `𝒢_l ⋆ hk_ε = e^{-lε}`-shifted: `∫ 𝒢_l(u) hk_ε(w-u) du + 1/l = e^{lε} ser(cW l ε)(w)`. -/
theorem conv_sliceG_hk {l : ℝ} (hl : 0 ≤ l) {ε : ℝ} (hε : 0 < ε) (w : Torus d) :
    (∫ u, sliceG d l u * hk ε (w - u)) + 1 / l = Real.exp (l * ε) * ser (cW l ε) w := by
  have hφc : Continuous fun u : Torus d => hk ε (w - u) :=
    (continuous_hk hε).comp (continuous_const.sub continuous_id)
  obtain ⟨M, hM⟩ := hk_bdd hε
  have hB : ∀ u : Torus d, |hk ε (w - u)| ≤ M := fun u => by
    rw [abs_of_nonneg (hk_nonneg hε _)]; exact hM _
  rw [tf_sliceG hl hφc.measurable hB]
  have h1 : ∀ t ∈ Ioi (0 : ℝ), Real.exp (-l * t) * ∫ u, psiFn u (4 * Real.pi ^ 2 * t) * hk ε (w - u) =
      Real.exp (l * ε) * (fun s => Real.exp (-l * s) * psiFn w (4 * Real.pi ^ 2 * s)) (t + ε) := by
    intro t ht
    have ht' : (0 : ℝ) < t := ht
    rw [integral_psi_mul_hk ht' hε w]
    simp only []
    rw [show ε + t = t + ε by ring, ← mul_assoc, ← Real.exp_add]
    congr 2; ring
  rw [setIntegral_congr_fun measurableSet_Ioi h1, integral_const_mul,
    integral_Ioi_shift (fun s => Real.exp (-l * s) * psiFn w (4 * Real.pi ^ 2 * s)) ε,
    ser_cW_eq hl hε w, mul_add]
  have : Real.exp (l * ε) * (Real.exp (-(l * ε)) / l) = 1 / l := by
    by_cases hl0 : l = 0
    · simp [hl0]
    · rw [mul_div_assoc', ← Real.exp_add]; simp
  rw [this]

/-- Integration by parts for the slice kernel against a translated `C¹` test function. -/
theorem ibp_conv {l : ℝ} (hl : 0 ≤ l) {φ : Torus d → ℝ} (hφ : Torus.IsCk 1 φ) (i : Fin d) (w : Torus d) :
    ∫ u, sliceG d l u * Torus.partialDeriv i φ (w - u) = ∫ u, SliceAux.sgc i l u * φ (w - u) := by
  have hφc : Continuous φ := HRS.Torus.continuous_of_continuous_lift hφ.continuous
  have hdφc : Continuous (Torus.partialDeriv i φ) := PDE.continuous_partialDeriv i φ hφ
  obtain ⟨B1, hB1⟩ := PDE.MFSchauder.exists_bound_of_cont hdφc
  obtain ⟨B2, hB2⟩ := PDE.MFSchauder.exists_bound_of_cont hφc
  have m1 : Measurable fun u : Torus d => Torus.partialDeriv i φ (w - u) :=
    (hdφc.comp (continuous_const.sub continuous_id)).measurable
  have m2 : Measurable fun u : Torus d => φ (w - u) :=
    (hφc.comp (continuous_const.sub continuous_id)).measurable
  rw [tf_sliceG (φ := fun u => Torus.partialDeriv i φ (w - u)) hl m1 (fun u => hB1 _),
    tf_sgc (φ := fun u => φ (w - u)) i hl m2 (fun u => hB2 _)]
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  have ht' : (0 : ℝ) < t := ht
  have hu : 0 < 4 * Real.pi ^ 2 * t := by positivity
  congr 1
  -- the identity  Ψ_t ⋆ ∂φ = ∂Ψ_t ⋆ φ
  set Ψ : Torus d → ℝ := fun x => psiFn x (4 * Real.pi ^ 2 * t) with hΨ
  have hΨc : Continuous Ψ := EnergyAux.continuous_psiFn hu
  have hΨ1 : Torus.IsCk 1 Ψ := isCk_psiFn hu
  have hΨi : Integrable Ψ := hΨc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hφi : Integrable φ := hφc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hcomm : ∀ (g h : Torus d → ℝ) (x : Torus d), convFun g h x = convFun h g x := by
    intro g h x
    rw [PDE.MFSchauder.convFun_eq', PDE.MFSchauder.convFun_eq']
    rw [← integral_sub_left_eq_self (fun z => g z * h (x - z)) volume x]
    exact integral_congr_ae (Filter.Eventually.of_forall fun z => by simp [mul_comm])
  have e1 : Torus.partialDeriv i (convFun Ψ φ) w = convFun Ψ (Torus.partialDeriv i φ) w :=
    PDE.MFSchauder.convFun_partialDeriv hΨi hφ i w
  have e2 : Torus.partialDeriv i (convFun φ Ψ) w = convFun φ (Torus.partialDeriv i Ψ) w :=
    PDE.MFSchauder.convFun_partialDeriv hφi hΨ1 i w
  have e3 : convFun Ψ φ = convFun φ Ψ := funext fun x => hcomm _ _ x
  have e4 : Torus.partialDeriv i Ψ = fun x => psiG i x (4 * Real.pi ^ 2 * t) :=
    funext fun x => partialDeriv_psiFn hu i x
  rw [e3] at e1
  have e5 : convFun Ψ (Torus.partialDeriv i φ) w = convFun φ (Torus.partialDeriv i Ψ) w := by
    rw [← e1, e2]
  rw [e4, hcomm φ _ w] at e5
  have f1 := PDE.MFSchauder.convFun_eq' Ψ (Torus.partialDeriv i φ) w
  have f2 := PDE.MFSchauder.convFun_eq' (fun x => psiG i x (4 * Real.pi ^ 2 * t)) φ w
  rw [f1, f2] at e5
  exact e5


/-- `∂_i ser(cW l ε) = e^{-lε} ∂_i𝒢_l ⋆ hk_ε`. -/
theorem ser_cW_partialDeriv {l : ℝ} (hl : 0 ≤ l) {ε : ℝ} (hε : 0 < ε) (i : Fin d) (w : Torus d) :
    Torus.partialDeriv i (ser (cW l ε)) w =
      Real.exp (-(l * ε)) * ∫ u, SliceAux.sgc i l u * hk ε (w - u) := by
  have hGi := integrable_sliceG (d := d) hl
  have hC1 : Torus.IsCk 1 (convFun (sliceG d l) (hk ε)) := PDE.MFSchauder.convFun_isCk_one hGi (isCk_hk hε)
  have hf1 : Torus.IsCk 1 (fun x => convFun (sliceG d l) (hk ε) x + 1 / l) :=
    hC1.add contDiff_const
  have hfun : ser (cW l ε) = fun x => Real.exp (-(l * ε)) * (convFun (sliceG d l) (hk ε) x + 1 / l) := by
    funext x
    have := conv_sliceG_hk hl hε x
    rw [PDE.MFSchauder.convFun_eq']
    rw [this, ← mul_assoc, ← Real.exp_add]
    simp
  rw [hfun, PDE.MFHolder.partialDeriv_const_mul i hf1,
    PDE.MFHolder.partialDeriv_add i hC1 (PDE.MFHolder.isCk_one_const _),
    PDE.MFAux.partialDeriv_const, add_zero, PDE.MFSchauder.convFun_partialDeriv hGi (isCk_hk hε) i w,
    PDE.MFSchauder.convFun_eq']
  congr 1
  exact ibp_conv hl (isCk_hk hε) i w

end HRS.Commutator.RoughKernel
