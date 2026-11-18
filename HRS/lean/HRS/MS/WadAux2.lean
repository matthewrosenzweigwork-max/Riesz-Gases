import HRS.MS.WadAux1
import HRS.Whole.CriticalNoise

/-!
# S8.3, packet D1 (part 2): the Gaussian average preserves `C_M`; the semigroup law

For `E`-valued `f` (`E` a real Banach space) we use `CMs M f := Continuous f ∧ ‖f x‖/⟨x⟩^M → 0` at infinity
(`MemCM M f` is the real case, `s83_memCM_iff`).  Results:

* `s83_G_continuous`, `s83_G_cm`: for `f ∈ C_M` (`M ≥ 0`), `0 < c ≤ 1`, `|σ| ≤ σ₀`, `G_{c,σ} f ∈ C_M`.
* `s83_P_cm`: the Mehler operator `P_t = s83_P a ν t` maps `C_M` into `C_M`, `t ≥ 0`.
* `s83_G_comp`: `G_{c,σ} (G_{c',σ'} f) = G_{cc',√(c'²σ²+σ'²)} f` for `f ∈ C_M`, and `s83_P_add`: the
  semigroup law `P_{t+s} f = P_t (P_s f)`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace HRS.MS.Wad

open HRS HRS.Whole

variable {d : ℕ}

/-- `f` is continuous and `‖f x‖ ⟨x⟩^{-M} → 0` at infinity. -/
def CMs {E : Type*} [NormedAddCommGroup E] (M : ℝ) (f : Euc d → E) : Prop :=
  Continuous f ∧ Tendsto (fun x => ‖f x‖ / jbracket x ^ M) (cocompact (Euc d)) (𝓝 0)

theorem s83_memCM_iff (M : ℝ) (f : Euc d → ℝ) : MemCM M f ↔ CMs M f := by
  unfold MemCM CMs
  refine and_congr Iff.rfl ?_
  have e : ∀ x : Euc d, ‖f x / jbracket x ^ M‖ = ‖f x‖ / jbracket x ^ M := fun x => by
    rw [norm_div, Real.norm_of_nonneg (Real.rpow_nonneg (s83_jb_pos _).le _)]
  rw [tendsto_zero_iff_norm_tendsto_zero]
  simp only [e]

/-- A `C_M` function is bounded by a multiple of the weight. -/
theorem s83_cm_wt {E : Type*} [NormedAddCommGroup E] {M : ℝ} {f : Euc d → E} (hf : CMs M f) :
    ∃ C, Wt M C f := by
  obtain ⟨hc, ht⟩ := hf
  have h1 : {x | ‖f x‖ / jbracket x ^ M < 1} ∈ cocompact (Euc d) :=
    ht.eventually (gt_mem_nhds one_pos)
  obtain ⟨K, hK, hKs⟩ := Filter.mem_cocompact.1 h1
  have hcont : Continuous fun x => ‖f x‖ / jbracket x ^ M := by
    refine hc.norm.div ?_ fun x => (Real.rpow_pos_of_pos (s83_jb_pos x) _).ne'
    unfold jbracket
    exact Continuous.rpow_const (by fun_prop) fun x => Or.inl (by
      have := (s83_jb_pos x).ne'; unfold jbracket at this; exact this)
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn hcont.continuousOn
  refine ⟨max B 1, fun x => ?_⟩
  have hp : 0 < jbracket x ^ M := Real.rpow_pos_of_pos (s83_jb_pos x) _
  have : ‖f x‖ / jbracket x ^ M ≤ max B 1 := by
    by_cases hx : x ∈ K
    · have := hB x hx
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)] at this
      exact this.trans (le_max_left _ _)
    · have := hKs hx
      exact (le_of_lt this).trans (le_max_right _ _)
  rwa [div_le_iff₀ hp] at this

theorem s83_jb_le_three {x x₀ : Euc d} (h : ‖x - x₀‖ < 1) : jbracket x ≤ 3 * jbracket x₀ := by
  have h1 : ‖x‖ ≤ ‖x₀‖ + 1 := by
    have := norm_le_insert' x x₀
    linarith
  have h2 := s83_norm_le_jb x₀
  have h3 := s83_one_le_jb x₀
  have := s83_jb_le_one_add x
  linarith

section Cont

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] {M : ℝ}

/-- Continuity of the Gaussian average of a continuous function of weighted growth. -/
theorem s83_G_continuous {f : Euc d → E} (hf : Continuous f) {M C : ℝ} (hM : 0 ≤ M) (hw : Wt M C f)
    {c σ σ₀ : ℝ} (hc : |c| ≤ 1) (hσ : |σ| ≤ σ₀) : Continuous (s83_G c σ f) := by
  rw [continuous_iff_continuousAt]
  intro x₀
  have hC := hw.nonneg
  refine continuousAt_of_dominated
    (bound := fun z : Euc d => C * 2 ^ M * (3 * jbracket x₀) ^ M * jbracket (σ • z) ^ M) ?_ ?_ ?_ ?_
  · exact Eventually.of_forall fun x => (s83_cont_shift hf c σ x).aestronglyMeasurable
  · have hball : Metric.ball x₀ 1 ∈ 𝓝 x₀ := Metric.ball_mem_nhds _ one_pos
    filter_upwards [hball] with x hx
    refine Eventually.of_forall fun z => ?_
    rw [mem_ball_iff_norm] at hx
    refine (hw _).trans ?_
    have h1 := s83_jb_add_rpow hM (c • x) (σ • z)
    have h2 : jbracket (c • x) ^ M ≤ (3 * jbracket x₀) ^ M :=
      (s83_jb_smul_le_rpow hM hc x).trans
        (Real.rpow_le_rpow (s83_jb_pos _).le (s83_jb_le_three hx) hM)
    have h3 : 0 ≤ jbracket (σ • z) ^ M := Real.rpow_nonneg (s83_jb_pos _).le _
    calc C * jbracket (c • x + σ • z) ^ M
        ≤ C * (2 ^ M * (jbracket (c • x) ^ M * jbracket (σ • z) ^ M)) :=
          mul_le_mul_of_nonneg_left h1 hC
      _ = C * 2 ^ M * jbracket (c • x) ^ M * jbracket (σ • z) ^ M := by ring
      _ ≤ C * 2 ^ M * (3 * jbracket x₀) ^ M * jbracket (σ • z) ^ M := by
          refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h2 (by positivity)) h3
  · exact (s83_int_jb_smul (M := M) hM hσ).const_mul _
  · exact Eventually.of_forall fun z => (hf.comp ((continuous_const_smul c).add continuous_const)).continuousAt

theorem s83_cocompact_cg (d : ℕ) : (cocompact (Euc d)).IsCountablyGenerated := by
  rw [← Metric.cobounded_eq_cocompact, ← comap_norm_atTop]; infer_instance

/-- `f(cx+σz)/⟨x⟩^M → 0` as `x → ∞` for fixed `z` (`c > 0`). -/
theorem s83_shift_tendsto {f : Euc d → E} (hf : CMs M f) (hM : 0 ≤ M) {c σ : ℝ} (hc0 : 0 < c)
    (hc : c ≤ 1) (z : Euc d) :
    Tendsto (fun x : Euc d => ‖f (c • x + σ • z)‖ / jbracket x ^ M) (cocompact (Euc d)) (𝓝 0) := by
  have hy : Tendsto (fun x : Euc d => c • x + σ • z) (cocompact (Euc d)) (cocompact (Euc d)) := by
    refine Filter.tendsto_cocompact_cocompact_of_norm fun ε => ⟨(ε + |σ| * ‖z‖) / c, fun x hx => ?_⟩
    have h1 : ‖c • x‖ - ‖σ • z‖ ≤ ‖c • x + σ • z‖ := by
      have := norm_sub_norm_le (c • x) (-(σ • z))
      simpa [sub_neg_eq_add] using this
    rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hc0] at h1
    rw [div_lt_iff₀ hc0] at hx
    nlinarith
  have h1 := hf.2.comp hy
  have h2 : Tendsto (fun x : Euc d => ‖f (c • x + σ • z)‖ / jbracket (c • x + σ • z) ^ M *
      (2 ^ M * jbracket (σ • z) ^ M)) (cocompact (Euc d)) (𝓝 0) := by
    simpa using h1.mul_const (2 ^ M * jbracket (σ • z) ^ M)
  refine squeeze_zero (fun x => div_nonneg (norm_nonneg _) (Real.rpow_nonneg (s83_jb_pos x).le _)) (fun x => ?_) h2
  have hp : 0 < jbracket x ^ M := Real.rpow_pos_of_pos (s83_jb_pos x) _
  have hpy : 0 < jbracket (c • x + σ • z) ^ M := Real.rpow_pos_of_pos (s83_jb_pos _) _
  have hb : jbracket (c • x + σ • z) ^ M ≤ 2 ^ M * jbracket (σ • z) ^ M * jbracket x ^ M := by
    have h1 := s83_jb_add_rpow hM (c • x) (σ • z)
    have h2 : jbracket (c • x) ^ M ≤ jbracket x ^ M :=
      s83_jb_smul_le_rpow hM (by rw [abs_of_pos hc0]; exact hc) x
    have h3 : 0 ≤ jbracket (σ • z) ^ M := Real.rpow_nonneg (s83_jb_pos _).le _
    calc jbracket (c • x + σ • z) ^ M ≤ 2 ^ M * (jbracket (c • x) ^ M * jbracket (σ • z) ^ M) := h1
      _ ≤ 2 ^ M * (jbracket x ^ M * jbracket (σ • z) ^ M) := by
          gcongr
      _ = 2 ^ M * jbracket (σ • z) ^ M * jbracket x ^ M := by ring
  rw [div_mul_eq_mul_div, div_le_div_iff₀ hp hpy]
  have hn := norm_nonneg (f (c • x + σ • z))
  calc ‖f (c • x + σ • z)‖ * jbracket (c • x + σ • z) ^ M
      ≤ ‖f (c • x + σ • z)‖ * (2 ^ M * jbracket (σ • z) ^ M * jbracket x ^ M) :=
        mul_le_mul_of_nonneg_left hb hn
    _ = ‖f (c • x + σ • z)‖ * (2 ^ M * jbracket (σ • z) ^ M) * jbracket x ^ M := by ring

/-- **Decay at infinity** of the Gaussian average of a `C_M` function. -/
theorem s83_G_tendsto {f : Euc d → E} (hf : CMs M f) {C : ℝ} (hw : Wt M C f) (hM : 0 ≤ M) {c σ σ₀ : ℝ}
    (hc0 : 0 < c) (hc : c ≤ 1) (hσ : |σ| ≤ σ₀) :
    Tendsto (fun x => ‖s83_G c σ f x‖ / jbracket x ^ M) (cocompact (Euc d)) (𝓝 0) := by
  have hC := hw.nonneg
  haveI := s83_cocompact_cg d
  have hmain : Tendsto (fun x : Euc d => ∫ z, (jbracket x ^ M)⁻¹ • f (c • x + σ • z)
      ∂(stdGaussian (Euc d))) (cocompact (Euc d)) (𝓝 (∫ z : Euc d, (0 : E) ∂(stdGaussian (Euc d)))) := by
    refine tendsto_integral_filter_of_dominated_convergence
      (bound := fun z : Euc d => C * 2 ^ M * jbracket (σ • z) ^ M) ?_ ?_ ?_ ?_
    · refine Eventually.of_forall fun x => ?_
      exact (continuous_const.smul (s83_cont_shift hf.1 c σ x)).aestronglyMeasurable
    · refine Eventually.of_forall fun x => Eventually.of_forall fun z => ?_
      have hp : 0 < jbracket x ^ M := Real.rpow_pos_of_pos (s83_jb_pos x) _
      rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hp.le), inv_mul_le_iff₀ hp]
      refine (hw _).trans ?_
      have h1 := s83_jb_add_rpow hM (c • x) (σ • z)
      have h2 : jbracket (c • x) ^ M ≤ jbracket x ^ M :=
        s83_jb_smul_le_rpow hM (by rw [abs_of_pos hc0]; exact hc) x
      have h3 : 0 ≤ jbracket (σ • z) ^ M := Real.rpow_nonneg (s83_jb_pos _).le _
      calc C * jbracket (c • x + σ • z) ^ M ≤ C * (2 ^ M * (jbracket (c • x) ^ M * jbracket (σ • z) ^ M)) :=
            mul_le_mul_of_nonneg_left h1 hC
        _ ≤ C * (2 ^ M * (jbracket x ^ M * jbracket (σ • z) ^ M)) := by gcongr
        _ = jbracket x ^ M * (C * 2 ^ M * jbracket (σ • z) ^ M) := by ring
    · exact (s83_int_jb_smul (M := M) hM hσ).const_mul _
    · refine Eventually.of_forall fun z => ?_
      have := s83_shift_tendsto hf hM (σ := σ) hc0 hc z
      rw [tendsto_zero_iff_norm_tendsto_zero]
      refine this.congr fun x => ?_
      have hp : 0 < jbracket x ^ M := Real.rpow_pos_of_pos (s83_jb_pos x) _
      rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hp.le), inv_mul_eq_div]
  rw [s83_int_const] at hmain
  rw [tendsto_zero_iff_norm_tendsto_zero] at hmain
  refine hmain.congr fun x => ?_
  have hint := s83_int_shift hf.1 hM hw (c := c) hσ x
  rw [integral_smul, norm_smul]
  have hp : 0 < jbracket x ^ M := Real.rpow_pos_of_pos (s83_jb_pos x) _
  rw [Real.norm_of_nonneg (inv_nonneg.2 hp.le), inv_mul_eq_div]
  rfl

theorem s83_G_cm {f : Euc d → E} (hf : CMs M f) (hM : 0 ≤ M) {c σ σ₀ : ℝ} (hc0 : 0 < c) (hc : c ≤ 1)
    (hσ : |σ| ≤ σ₀) : CMs M (s83_G c σ f) := by
  obtain ⟨C, hw⟩ := s83_cm_wt hf
  exact ⟨s83_G_continuous hf.1 hM hw (by rw [abs_of_pos hc0]; exact hc) hσ,
    s83_G_tendsto hf hw hM hc0 hc hσ⟩

theorem s83_P_cm {f : Euc d → E} (hf : CMs M f) (hM : 0 ≤ M) {a ν t : ℝ} (ha : 0 < a) (hν : 0 ≤ ν)
    (ht : 0 ≤ t) : CMs M (s83_P a ν t f) :=
  s83_G_cm hf hM (s83_mc_pos a t) (s83_mc_le_one ha.le ht) (s83_abs_ms_le ha hν ht)

end Cont

/-! ### The semigroup law -/

/-- The law of `α z + β z'` under `γ ⊗ γ` is `N(0, α²+β²)`. -/
theorem s83_gauss_comb (d : ℕ) (α β : ℝ) :
    (((stdGaussian (Euc d)).prod (stdGaussian (Euc d))).map
      (fun p : Euc d × Euc d => α • p.1 + β • p.2)) =
    (stdGaussian (Euc d)).map (fun w => Real.sqrt (α ^ 2 + β ^ 2) • w) := by
  have hm1 : Measurable fun w : Euc d => α • w := by fun_prop
  have hm2 : Measurable fun w : Euc d => β • w := by fun_prop
  have e1 : ((stdGaussian (Euc d)).prod (stdGaussian (Euc d))).map
      (fun p : Euc d × Euc d => α • p.1 + β • p.2) =
      (((stdGaussian (Euc d)).map (fun w => α • w)).prod ((stdGaussian (Euc d)).map (fun w => β • w))).map
        (fun p : Euc d × Euc d => p.1 + p.2) := by
    rw [Measure.map_prod_map _ _ hm1 hm2, Measure.map_map (by fun_prop) (by fun_prop)]
    rfl
  rw [e1]
  refine Measure.ext_of_charFun ?_
  ext t
  rw [charFun_map_add_prod_eq_mul, Pi.mul_apply, charFun_map_smul, charFun_map_smul,
    charFun_map_smul, charFun_stdGaussian, charFun_stdGaussian, charFun_stdGaussian,
    ← Complex.exp_add]
  congr 1
  simp only [norm_smul, Real.norm_eq_abs]
  have key : (|α| * ‖t‖) ^ 2 + (|β| * ‖t‖) ^ 2 = (|Real.sqrt (α ^ 2 + β ^ 2)| * ‖t‖) ^ 2 := by
    rw [abs_of_nonneg (Real.sqrt_nonneg _), mul_pow, mul_pow, mul_pow, sq_abs, sq_abs,
      Real.sq_sqrt (by positivity)]
    ring
  have key' : ((|α| * ‖t‖ : ℝ) : ℂ) ^ 2 + ((|β| * ‖t‖ : ℝ) : ℂ) ^ 2 =
      ((|Real.sqrt (α ^ 2 + β ^ 2)| * ‖t‖ : ℝ) : ℂ) ^ 2 := by exact_mod_cast key
  linear_combination (-1 / 2 : ℂ) * key'

theorem s83_wt_poly {E : Type*} [NormedAddCommGroup E] {f : Euc d → E} {M C : ℝ} (hM : 0 ≤ M)
    (hw : Wt M C f) (v u : Euc d) :
    ‖f (v + u)‖ ≤ (C * 2 ^ M * jbracket v ^ M) * (1 + ‖u‖) ^ ⌈M⌉₊ := by
  have hC := hw.nonneg
  refine (hw _).trans ?_
  have h1 := s83_jb_add_rpow hM v u
  have h2 := s83_jb_smul_poly (M := M) (σ := 1) (σ₀ := 1) hM (by simp) u
  simp only [one_smul, one_mul] at h2
  calc C * jbracket (v + u) ^ M ≤ C * (2 ^ M * (jbracket v ^ M * jbracket u ^ M)) :=
        mul_le_mul_of_nonneg_left h1 hC
    _ = (C * 2 ^ M * jbracket v ^ M) * jbracket u ^ M := by ring
    _ ≤ (C * 2 ^ M * jbracket v ^ M) * (1 + ‖u‖) ^ ⌈M⌉₊ := by
        refine mul_le_mul_of_nonneg_left h2
          (mul_nonneg (mul_nonneg hC (by positivity)) (Real.rpow_nonneg (s83_jb_pos v).le _))

section Comp

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] {M : ℝ}

/-- Fubini form of the composition of two Gaussian averages. -/
theorem s83_gauss_comb_integral {F : Euc d → E} (hF : Continuous F) {K : ℝ} {p : ℕ}
    (hb : ∀ u, ‖F u‖ ≤ K * (1 + ‖u‖) ^ p) (α β : ℝ) :
    ∫ z, (∫ z', F (α • z + β • z') ∂(stdGaussian (Euc d))) ∂(stdGaussian (Euc d)) =
      ∫ w, F (Real.sqrt (α ^ 2 + β ^ 2) • w) ∂(stdGaussian (Euc d)) := by
  set τ := Real.sqrt (α ^ 2 + β ^ 2) with hτ
  have hcomb : Measurable fun q : Euc d × Euc d => α • q.1 + β • q.2 := by fun_prop
  have hτm : Measurable fun w : Euc d => τ • w := by fun_prop
  have hIntτ : Integrable (fun w : Euc d => F (τ • w)) (stdGaussian (Euc d)) := by
    refine s83_int_of_poly (C := K * (1 + |τ|) ^ p) (p := p)
      (hF.comp (continuous_const_smul τ)).aestronglyMeasurable fun w => ?_
    refine (hb _).trans ?_
    have hK : 0 ≤ K := by
      have := (norm_nonneg (F 0)).trans (by simpa using hb 0)
      exact this
    rw [mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ hK
    rw [← mul_pow]
    refine pow_le_pow_left₀ (by positivity) ?_ p
    rw [norm_smul, Real.norm_eq_abs]
    nlinarith [norm_nonneg w, abs_nonneg τ]
  have hmap := s83_gauss_comb d α β
  have hInt : Integrable F (((stdGaussian (Euc d)).prod (stdGaussian (Euc d))).map
      (fun q : Euc d × Euc d => α • q.1 + β • q.2)) := by
    rw [hmap]
    exact (integrable_map_measure hF.aestronglyMeasurable hτm.aemeasurable).2 hIntτ
  have hInt2 := (integrable_map_measure hF.aestronglyMeasurable hcomb.aemeasurable).1 hInt
  rw [← integral_map hτm.aemeasurable hF.aestronglyMeasurable, ← hmap,
    integral_map hcomb.aemeasurable hF.aestronglyMeasurable]
  exact (integral_prod _ hInt2).symm

/-- Composition of Gaussian averages: `G_{c,σ} G_{c',σ'} = G_{cc', √(c'²σ²+σ'²)}`. -/
theorem s83_G_comp {f : Euc d → E} (hf : Continuous f) (hM : 0 ≤ M) {C : ℝ} (hw : Wt M C f)
    (c σ c' σ' : ℝ) :
    s83_G c σ (s83_G c' σ' f) = s83_G (c * c') (Real.sqrt ((c' * σ) ^ 2 + σ' ^ 2)) f := by
  funext x
  have hF : Continuous fun u : Euc d => f (((c * c') • x) + u) := hf.comp (continuous_const.add continuous_id)
  have hb : ∀ u : Euc d, ‖f (((c * c') • x) + u)‖ ≤
      (C * 2 ^ M * jbracket ((c * c') • x) ^ M) * (1 + ‖u‖) ^ ⌈M⌉₊ :=
    fun u => s83_wt_poly hM hw _ u
  have := s83_gauss_comb_integral hF hb (c' * σ) σ'
  have e1 : ∀ z z' : Euc d, c' • (c • x + σ • z) + σ' • z' =
      (c * c') • x + ((c' * σ) • z + σ' • z') := by
    intro z z'
    rw [smul_add, smul_smul, smul_smul, mul_comm c' c, add_assoc]
  calc s83_G c σ (s83_G c' σ' f) x
      = ∫ z, (∫ z', f ((c * c') • x + ((c' * σ) • z + σ' • z')) ∂(stdGaussian (Euc d)))
          ∂(stdGaussian (Euc d)) := by simp only [s83_G, e1]
    _ = _ := this
    _ = s83_G (c * c') (Real.sqrt ((c' * σ) ^ 2 + σ' ^ 2)) f x := rfl

/-- `σ_{t+s}² = (e^{-as} σ_t)² + σ_s²`. -/
theorem s83_ms_add {a ν t s : ℝ} (ha : 0 < a) (hν : 0 ≤ ν) (ht : 0 ≤ t) (hs : 0 ≤ s) :
    s83_ms a ν (t + s) = Real.sqrt ((s83_mc a s * s83_ms a ν t) ^ 2 + s83_ms a ν s ^ 2) := by
  have h1 := s83_ms_sq ha hν ht
  have h2 := s83_ms_sq ha hν hs
  have h3 := s83_ms_sq ha hν (add_nonneg ht hs)
  have h : Real.exp (-2 * a * (t + s)) = Real.exp (-2 * a * t) * Real.exp (-2 * a * s) := by
    rw [← Real.exp_add]; congr 1; ring
  have h4 : s83_mc a s ^ 2 = Real.exp (-2 * a * s) := by
    unfold s83_mc; rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  have : (s83_mc a s * s83_ms a ν t) ^ 2 + s83_ms a ν s ^ 2 = s83_ms a ν (t + s) ^ 2 := by
    rw [mul_pow, h1, h2, h3, h4, h]
    field_simp
    ring
  rw [this]
  exact (Real.sqrt_sq (s83_ms_nonneg _ _ _)).symm

/-- **The semigroup law** `P_{t+s} f = P_t (P_s f)` on continuous functions of weighted growth. -/
theorem s83_P_add {f : Euc d → E} (hf : Continuous f) (hM : 0 ≤ M) {C : ℝ} (hw : Wt M C f)
    {a ν t s : ℝ} (ha : 0 < a) (hν : 0 ≤ ν) (ht : 0 ≤ t) (hs : 0 ≤ s) :
    s83_P a ν (t + s) f = s83_P a ν t (s83_P a ν s f) := by
  unfold s83_P
  rw [s83_G_comp hf hM hw, s83_mc_add, s83_ms_add ha hν ht hs]

end Comp

end HRS.MS.Wad
