import HRS.PDE.ToolboxRd.Defs
import HRS.PDE.ToolboxRd.Levy

/-!
# Lemma C.3 (ii) on `ℝ^d`: the principal-value formula

Package PV.  For an even measurable kernel `𝔨` with `|𝔨(z)| ≤ C|z|^{-d-θ}` (`0 < θ < 2`) and symbol
`m = ∫ 𝔨 (1 - cos 2π⟨ξ,·⟩)`, and `u ∈ C^{1,1}_b`, we prove the `pv` field of `IsLevyKernel`
(`pv_core`).  Route (shorter than truncating the test function): with the symmetric second
difference `sd f x z = 2f(x) - f(x-z) - f(x+z)` set `Ku(x) = ½ ∫ 𝔨(z) sd u x z dz`
(absolutely convergent, `|sd u x z| ≤ M min(|z|²,1)`); evenness of `𝔨` identifies the truncated
integrals `∫_{|z|>ε} 𝔨 (u(x) - u(x-z))` with `½ ∫_{|z|>ε} 𝔨 sd u x z`.  Duality `∫ Ku φ = ∫ u Kφ`
is a pair of Fubini's with the translation-invariance of Lebesgue measure (no `ε`), `Kφ = ½∫𝔨 sd φ`
is in `L¹` since `∫_x |sd φ x z| ≤ M min(|z|²,1)` (Schwartz decay of `D²φ`), and `Kφ = 𝓕⁻(m 𝓕φ)` by
Fourier inversion plus Fubini in `(z,ξ)`.
-/

noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ComplexConjugate ContDiff FourierTransform

namespace HRS.PDE.ToolboxRd.PVAux

variable {d : ℕ}

/-- the symmetric second difference `2 f x - f (x - z) - f (x + z)` -/
def sd {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (f : Euc d → F) (x z : Euc d) : F :=
  (2 : ℝ) • f x - f (x - z) - f (x + z)

theorem sd_ofReal (u : Euc d → ℝ) (x z : Euc d) :
    ((sd u x z : ℝ) : ℂ) = sd (fun y => ((u y : ℝ) : ℂ)) x z := by
  simp [sd]

theorem norm_sd_le_of_lip {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {f : Euc d → F}
    (hf : Differentiable ℝ f) {x z : Euc d} {Λ : ℝ} (hΛ : 0 ≤ Λ)
    (hL : ∀ y ∈ Metric.closedBall x ‖z‖, ∀ y' ∈ Metric.closedBall x ‖z‖,
      ‖fderiv ℝ f y - fderiv ℝ f y'‖ ≤ Λ * ‖y - y'‖) :
    ‖sd f x z‖ ≤ 2 * Λ * ‖z‖ ^ 2 := by
  set g : ℝ → F := fun t => f (x + t • z) + f (x - t • z) - (2 : ℝ) • f x with hg
  have hder : ∀ t : ℝ, HasDerivAt g (fderiv ℝ f (x + t • z) z - fderiv ℝ f (x - t • z) z) t := by
    intro t
    have h1 : HasDerivAt (fun t : ℝ => x + t • z) z t := by
      simpa using ((hasDerivAt_id t).smul_const z).const_add x
    have h2 : HasDerivAt (fun t : ℝ => x - t • z) (-z) t := by
      simpa using ((hasDerivAt_id t).smul_const z).const_sub x
    have a1 := (hf (x + t • z)).hasFDerivAt.comp_hasDerivAt t h1
    have a2 := (hf (x - t • z)).hasFDerivAt.comp_hasDerivAt t h2
    have a3 := (a1.add a2).sub_const ((2 : ℝ) • f x)
    exact a3.congr_deriv (by rw [map_neg]; abel)
  have hmem : ∀ t ∈ Set.Icc (0 : ℝ) 1, x + t • z ∈ Metric.closedBall x ‖z‖ ∧
      x - t • z ∈ Metric.closedBall x ‖z‖ := by
    intro t ht
    have : ‖t • z‖ ≤ ‖z‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
      exact mul_le_of_le_one_left (norm_nonneg _) ht.2
    constructor <;> simpa [Metric.mem_closedBall, dist_eq_norm] using this
  have hb : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖deriv g t‖ ≤ 2 * Λ * ‖z‖ ^ 2 := by
    intro t ht
    rw [(hder t).deriv]
    obtain ⟨h1, h2⟩ := hmem t ht
    have := hL _ h1 _ h2
    have e : (x + t • z) - (x - t • z) = (2 * t) • z := by
      rw [two_mul, add_smul]; abel
    rw [e, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith [ht.1])] at this
    calc ‖fderiv ℝ f (x + t • z) z - fderiv ℝ f (x - t • z) z‖
        = ‖(fderiv ℝ f (x + t • z) - fderiv ℝ f (x - t • z)) z‖ := by simp
      _ ≤ ‖fderiv ℝ f (x + t • z) - fderiv ℝ f (x - t • z)‖ * ‖z‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ (Λ * (2 * t * ‖z‖)) * ‖z‖ := mul_le_mul_of_nonneg_right this (norm_nonneg _)
      _ ≤ (Λ * (2 * 1 * ‖z‖)) * ‖z‖ := by
          have := ht.2
          gcongr
      _ = 2 * Λ * ‖z‖ ^ 2 := by ring
  have key := (convex_Icc (0 : ℝ) 1).norm_image_sub_le_of_norm_deriv_le
    (fun t _ => (hder t).differentiableAt) hb (Set.left_mem_Icc.2 zero_le_one)
    (Set.right_mem_Icc.2 zero_le_one)
  have g0 : g 0 = 0 := by simp [hg, two_smul]
  have g1 : g 1 = -sd f x z := by simp [hg, sd]; abel
  rw [g0, g1] at key
  simpa using key


theorem schwartz_fderiv_fderiv_decay (φ : SchwartzMap (Euc d) ℂ) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y : Euc d, (1 + ‖y‖) ^ N * ‖fderiv ℝ (fderiv ℝ φ) y‖ ≤ C := by
  set Ψ := SchwartzMap.fderivCLM ℝ (Euc d) (Euc d →L[ℝ] ℂ) (SchwartzMap.fderivCLM ℝ (Euc d) ℂ φ) with hΨ
  have hf : ⇑(SchwartzMap.fderivCLM ℝ (Euc d) ℂ φ) = fderiv ℝ φ :=
    funext fun w => SchwartzMap.fderivCLM_apply ℝ φ w
  have hΨy : ∀ y, Ψ y = fderiv ℝ (fderiv ℝ φ) y := by
    intro y
    rw [hΨ, SchwartzMap.fderivCLM_apply, hf]
  refine ⟨2 ^ N * (Finset.Iic (N, 0)).sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2) Ψ, by positivity, fun y => ?_⟩
  have := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (N, 0)) (k := N) (n := 0) le_rfl le_rfl Ψ y
  rw [norm_iteratedFDeriv_zero, hΨy] at this
  exact this

theorem schwartz_sd_bound (φ : SchwartzMap (Euc d) ℂ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ x z : Euc d, ‖z‖ ≤ 1 →
      ‖sd (⇑φ) x z‖ * (1 + ‖x‖) ^ (d + 1) ≤ A * ‖z‖ ^ 2 := by
  obtain ⟨C, hC0, hC⟩ := schwartz_fderiv_fderiv_decay φ (d + 1)
  refine ⟨2 * (C * 2 ^ (d + 1)), by positivity, fun x z hz => ?_⟩
  set Λ : ℝ := C * 2 ^ (d + 1) / (1 + ‖x‖) ^ (d + 1) with hΛ
  have hxpos : 0 < (1 + ‖x‖) ^ (d + 1) := by positivity
  have hΛ0 : 0 ≤ Λ := by positivity
  have hbd : ∀ y ∈ Metric.closedBall x ‖z‖, ‖fderiv ℝ (fderiv ℝ φ) y‖ ≤ Λ := by
    intro y hy
    rw [Metric.mem_closedBall, dist_eq_norm] at hy
    have h1 : (1 + ‖x‖) / 2 ≤ 1 + ‖y‖ := by
      have := norm_sub_norm_le x y
      rw [norm_sub_rev] at this
      have h2 : ‖x‖ - ‖y‖ ≤ 1 := by linarith [norm_sub_norm_le x y, norm_sub_rev x y]
      nlinarith [norm_nonneg x, norm_nonneg y]
    have h2 := hC y
    have hypos : 0 < (1 + ‖y‖) ^ (d + 1) := by positivity
    have h3 : ((1 + ‖x‖) / 2) ^ (d + 1) ≤ (1 + ‖y‖) ^ (d + 1) :=
      pow_le_pow_left₀ (by positivity) h1 _
    rw [hΛ, le_div_iff₀ hxpos]
    have : ‖fderiv ℝ (fderiv ℝ φ) y‖ * ((1 + ‖x‖) / 2) ^ (d + 1) ≤ C := by
      calc _ ≤ ‖fderiv ℝ (fderiv ℝ φ) y‖ * (1 + ‖y‖) ^ (d + 1) :=
            mul_le_mul_of_nonneg_left h3 (by positivity)
        _ = _ := by ring
        _ ≤ C := h2
    rw [div_pow] at this
    have h4 : ‖fderiv ℝ (fderiv ℝ φ) y‖ * (1 + ‖x‖) ^ (d + 1) ≤ C * 2 ^ (d + 1) := by
      have h5 : (0 : ℝ) < 2 ^ (d + 1) := by positivity
      rw [← mul_div_assoc] at this
      exact (div_le_iff₀ h5).1 this
    exact h4
  have hf : ⇑(SchwartzMap.fderivCLM ℝ (Euc d) ℂ φ) = fderiv ℝ φ :=
    funext fun w => SchwartzMap.fderivCLM_apply ℝ φ w
  have hdiff : ∀ y, DifferentiableAt ℝ (fderiv ℝ φ) y := fun y => by
    rw [← hf]; exact (SchwartzMap.fderivCLM ℝ (Euc d) ℂ φ).differentiableAt
  have hlip : ∀ y ∈ Metric.closedBall x ‖z‖, ∀ y' ∈ Metric.closedBall x ‖z‖,
      ‖fderiv ℝ φ y - fderiv ℝ φ y'‖ ≤ Λ * ‖y - y'‖ := fun y hy y' hy' =>
    (convex_closedBall x ‖z‖).norm_image_sub_le_of_norm_fderiv_le (fun w _ => hdiff w) hbd hy' hy
  have := norm_sd_le_of_lip (f := ⇑φ) ((φ.smooth 1).differentiable (by norm_num)) hΛ0 hlip
  calc ‖sd (⇑φ) x z‖ * (1 + ‖x‖) ^ (d + 1) ≤ (2 * Λ * ‖z‖ ^ 2) * (1 + ‖x‖) ^ (d + 1) :=
        mul_le_mul_of_nonneg_right this hxpos.le
    _ = 2 * (C * 2 ^ (d + 1)) * ‖z‖ ^ 2 := by
        rw [hΛ]; field_simp


theorem setIntegral_neg_symm {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (S : Set (Euc d))
    (hS : MeasurableSet S) (hsym : ∀ z, -z ∈ S ↔ z ∈ S) (f : Euc d → F) :
    ∫ z in S, f (-z) = ∫ z in S, f z := by
  rw [← integral_indicator hS, ← integral_indicator hS,
    ← integral_neg_eq_self (S.indicator f) volume]
  congr 1
  funext z
  by_cases hz : z ∈ S
  · simp [Set.indicator, hz, (hsym z).2 hz]
  · have : -z ∉ S := fun h => hz ((hsym z).1 h)
    simp [Set.indicator, hz, this]

/-- hypotheses on the kernel -/
structure KH (d : ℕ) (θ : ℝ) (𝔨 : Euc d → ℝ) : Prop where
  hd : 1 ≤ d
  hθ0 : 0 < θ
  hθ2 : θ < 2
  ev : ∀ z, 𝔨 (-z) = 𝔨 z
  meas : Measurable 𝔨
  bd : ∃ C : ℝ, ∀ z : Euc d, z ≠ 0 → |𝔨 z| ≤ C * ‖z‖ ^ (-(d : ℝ) - θ)

namespace KH

variable {θ : ℝ} {𝔨 : Euc d → ℝ}

theorem wint (h : KH d θ 𝔨) : Integrable (fun z => |𝔨 z| * min (‖z‖ ^ 2) 1) :=
  LevyAux.kernel_min_integrable h.hd h.hθ0 h.hθ2 h.bd h.meas

theorem int_smul_of_le (h : KH d θ 𝔨) {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {g : Euc d → F} {M : ℝ}     (hm : AEStronglyMeasurable (fun z => 𝔨 z • g z) volume)
    (hg : ∀ z, ‖g z‖ ≤ M * min (‖z‖ ^ 2) 1) : Integrable (fun z => 𝔨 z • g z) := by
  refine (h.wint.const_mul M).mono' hm (ae_of_all _ fun z => ?_)
  rw [norm_smul, Real.norm_eq_abs]
  calc |𝔨 z| * ‖g z‖ ≤ |𝔨 z| * (M * min (‖z‖ ^ 2) 1) :=
        mul_le_mul_of_nonneg_left (hg z) (abs_nonneg _)
    _ = M * (|𝔨 z| * min (‖z‖ ^ 2) 1) := by ring

theorem tail_int (h : KH d θ 𝔨) {ε : ℝ} (hε : 0 < ε) : IntegrableOn 𝔨 {z : Euc d | ε < ‖z‖} := by
  have hc : 0 < min (ε ^ 2) 1 := lt_min (by positivity) one_pos
  refine (h.wint.integrableOn.const_mul (min (ε ^ 2) 1)⁻¹).mono' h.meas.aestronglyMeasurable ?_
  refine ae_restrict_of_forall_mem (measurableSet_lt measurable_const measurable_norm) fun z hz => ?_
  have hz' : ε < ‖z‖ := hz
  have h1 : min (ε ^ 2) 1 ≤ min (‖z‖ ^ 2) 1 :=
    min_le_min (pow_le_pow_left₀ hε.le hz'.le 2) le_rfl
  rw [Real.norm_eq_abs, inv_mul_eq_div, le_div_iff₀ hc]
  calc |𝔨 z| * min (ε ^ 2) 1 ≤ |𝔨 z| * min (‖z‖ ^ 2) 1 :=
        mul_le_mul_of_nonneg_left h1 (abs_nonneg _)

theorem tail_int_mul (h : KH d θ 𝔨) {ε : ℝ} (hε : 0 < ε) {g : Euc d → ℝ} {c : ℝ}
    (hg : AEStronglyMeasurable g volume) (hb : ∀ z, ‖g z‖ ≤ c) :
    IntegrableOn (fun z => 𝔨 z * g z) {z : Euc d | ε < ‖z‖} :=
  (h.tail_int hε).mul_bdd hg.restrict (ae_of_all _ hb)

end KH


theorem tendsto_tail_integral {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {f : Euc d → F}
    (hd : 1 ≤ d) (hf : Integrable f) :
    Tendsto (fun ε : ℝ => ∫ z in {z : Euc d | ε < ‖z‖}, f z) (𝓝[>] 0) (𝓝 (∫ z, f z)) := by
  have hmeas : ∀ ε : ℝ, MeasurableSet {z : Euc d | ε < ‖z‖} := fun ε =>
    measurableSet_lt measurable_const measurable_norm
  simp_rw [← integral_indicator (hmeas _)]
  refine tendsto_integral_filter_of_dominated_convergence (fun z => ‖f z‖) ?_ ?_ hf.norm ?_
  · exact Filter.Eventually.of_forall fun ε => hf.1.indicator (hmeas ε)
  · exact Filter.Eventually.of_forall fun ε => ae_of_all _ fun z => by
      by_cases hz : z ∈ {z : Euc d | ε < ‖z‖}
      · simp [Set.indicator, hz]
      · simp [Set.indicator, hz]
  · have hae : ∀ᵐ z : Euc d ∂volume, z ≠ 0 := by
      have : Nontrivial (Euc d) := by
        have : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
        infer_instance
      have : (volume : Measure (Euc d)) {0} = 0 := measure_singleton 0
      exact compl_mem_ae_iff.2 this
    filter_upwards [hae] with z hz
    have hpos : 0 < ‖z‖ := norm_pos_iff.2 hz
    refine tendsto_const_nhds.congr' ?_
    have : ∀ᶠ ε : ℝ in 𝓝[>] 0, ε < ‖z‖ := nhdsWithin_le_nhds (Iio_mem_nhds hpos)
    filter_upwards [this] with ε hε
    simp [Set.indicator, hε]

theorem C11_sd_bound {L : ℝ} {u : Euc d → ℝ} (hu : IsC11 L u) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x z : Euc d, |sd u x z| ≤ M * min (‖z‖ ^ 2) 1 := by
  obtain ⟨hC1, ⟨B, hB⟩, -, hlip⟩ := hu
  have hdiff : Differentiable ℝ u := hC1.differentiable one_ne_zero
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  set Λ : ℝ := (Real.toNNReal L : ℝ) with hΛ
  have hΛ0 : 0 ≤ Λ := NNReal.coe_nonneg _
  refine ⟨max (2 * Λ) (4 * B), le_max_of_le_right (by positivity), fun x z => ?_⟩
  have h1 : |sd u x z| ≤ 2 * Λ * ‖z‖ ^ 2 := by
    have := norm_sd_le_of_lip hdiff hΛ0 (x := x) (z := z) (fun y _ y' _ => by
      have := hlip.dist_le_mul y y'
      rwa [dist_eq_norm, dist_eq_norm] at this)
    simpa using this
  have h2 : |sd u x z| ≤ 4 * B := by
    simp only [sd, smul_eq_mul]
    have a := hB x
    have b := hB (x - z)
    have c := hB (x + z)
    rw [abs_le] at a b c ⊢
    constructor <;> linarith [a.1, a.2, b.1, b.2, c.1, c.2]
  rcases le_total (‖z‖ ^ 2) 1 with hz | hz
  · rw [min_eq_left hz]
    exact h1.trans (by nlinarith [le_max_left (2 * Λ) (4 * B), sq_nonneg ‖z‖])
  · rw [min_eq_right hz]
    exact h2.trans (by linarith [le_max_right (2 * Λ) (4 * B)])


theorem continuous_sd {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {f : Euc d → F}
    (hf : Continuous f) : Continuous (fun p : Euc d × Euc d => sd f p.1 p.2) := by
  unfold sd; fun_prop

theorem continuous_sd_snd {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {f : Euc d → F}
    (hf : Continuous f) (x : Euc d) : Continuous (fun z : Euc d => sd f x z) := by
  unfold sd; fun_prop

/-- the principal-value operator, symmetrised -/
def Kop (𝔨 : Euc d → ℝ) (u : Euc d → ℝ) (x : Euc d) : ℝ := (1 / 2) * ∫ z, 𝔨 z * sd u x z

theorem KH.int_sd {θ : ℝ} {𝔨 : Euc d → ℝ} (h : KH d θ 𝔨) {L : ℝ} {u : Euc d → ℝ} (hu : IsC11 L u)
    (x : Euc d) : Integrable (fun z => 𝔨 z * sd u x z) := by
  obtain ⟨M, -, hM⟩ := C11_sd_bound hu
  have := h.int_smul_of_le (g := fun z => sd u x z) (M := M)
    (h.meas.aestronglyMeasurable.smul (continuous_sd_snd hu.1.continuous x).aestronglyMeasurable)
    (fun z => by simpa using hM x z)
  simpa using this

theorem KH.pv_trunc {θ : ℝ} {𝔨 : Euc d → ℝ} (h : KH d θ 𝔨) {u : Euc d → ℝ} (hu : Continuous u)
    {B : ℝ} (hB : ∀ x, |u x| ≤ B) (x : Euc d) {ε : ℝ} (hε : 0 < ε) :
    ∫ z in {z : Euc d | ε < ‖z‖}, 𝔨 z * (u x - u (x - z)) =
      (1 / 2) * ∫ z in {z : Euc d | ε < ‖z‖}, 𝔨 z * sd u x z := by
  set S : Set (Euc d) := {z : Euc d | ε < ‖z‖} with hSdef
  have hS : MeasurableSet S := measurableSet_lt measurable_const measurable_norm
  have hsym : ∀ z, -z ∈ S ↔ z ∈ S := fun z => by simp [hSdef, norm_neg]
  have i0 : IntegrableOn (fun z => 𝔨 z * u x) S :=
    h.tail_int_mul hε (g := fun _ => u x) (c := B) aestronglyMeasurable_const (fun _ => by simpa using hB x)
  have i1 : IntegrableOn (fun z => 𝔨 z * u (x - z)) S :=
    h.tail_int_mul hε (g := fun z => u (x - z)) (c := B)
      (hu.comp (continuous_const.sub continuous_id)).aestronglyMeasurable (fun z => by simpa using hB _)
  have i2 : IntegrableOn (fun z => 𝔨 z * u (x + z)) S :=
    h.tail_int_mul hε (g := fun z => u (x + z)) (c := B)
      (hu.comp (continuous_const.add continuous_id)).aestronglyMeasurable (fun z => by simpa using hB _)
  have e12 : ∫ z in S, 𝔨 z * u (x + z) = ∫ z in S, 𝔨 z * u (x - z) := by
    rw [← setIntegral_neg_symm S hS hsym (fun z => 𝔨 z * u (x - z))]
    refine setIntegral_congr_fun hS fun z _ => ?_
    simp [h.ev]
  have lhs : ∫ z in S, 𝔨 z * (u x - u (x - z)) =
      (∫ z in S, 𝔨 z * u x) - ∫ z in S, 𝔨 z * u (x - z) := by
    rw [← integral_sub i0 i1]
    refine setIntegral_congr_fun hS fun z _ => ?_
    ring
  have rhs : ∫ z in S, 𝔨 z * sd u x z =
      2 * (∫ z in S, 𝔨 z * u x) - (∫ z in S, 𝔨 z * u (x - z)) - ∫ z in S, 𝔨 z * u (x + z) := by
    have : ∫ z in S, 𝔨 z * sd u x z =
        ∫ z in S, ((2 * (𝔨 z * u x) - 𝔨 z * u (x - z)) - 𝔨 z * u (x + z)) := by
      refine setIntegral_congr_fun hS fun z _ => ?_
      simp only [sd, smul_eq_mul]; ring
    have j0 : IntegrableOn (fun z => 2 * (𝔨 z * u x)) S := i0.const_mul 2
    have j1 : IntegrableOn (fun z => 2 * (𝔨 z * u x) - 𝔨 z * u (x - z)) S := j0.sub i1
    rw [this, integral_sub j1 i2, integral_sub j0 i1, integral_const_mul]
  rw [lhs, rhs, e12]; ring

theorem KH.pv_tendsto {θ : ℝ} {𝔨 : Euc d → ℝ} (h : KH d θ 𝔨) {L : ℝ} {u : Euc d → ℝ}
    (hu : IsC11 L u) (x : Euc d) :
    Tendsto (fun ε : ℝ => ∫ z in {z : Euc d | ε < ‖z‖}, 𝔨 z * (u x - u (x - z)))
      (𝓝[>] 0) (𝓝 (Kop 𝔨 u x)) := by
  obtain ⟨-, ⟨B, hB⟩, -, -⟩ := id hu
  have hlim := (tendsto_tail_integral h.hd (h.int_sd hu x)).const_mul (1 / 2)
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact (h.pv_trunc hu.1.continuous hB x hε).symm


theorem integrable_sd_x (φ : SchwartzMap (Euc d) ℂ) (z : Euc d) :
    Integrable (fun x => sd (⇑φ) x z) := by
  have h1 : Integrable (fun x => (2 : ℝ) • φ x) := φ.integrable.smul (2 : ℝ)
  have h2 : Integrable (fun x => φ (x - z)) := φ.integrable.comp_sub_right z
  have h3 : Integrable (fun x => φ (x + z)) := φ.integrable.comp_add_right z
  exact (h1.sub h2).sub h3

theorem schwartz_sd_L1 (φ : SchwartzMap (Euc d) ℂ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ z : Euc d, ∫ x, ‖sd (⇑φ) x z‖ ≤ M * min (‖z‖ ^ 2) 1 := by
  obtain ⟨A, hA0, hA⟩ := schwartz_sd_bound φ
  have hJ : Integrable (fun x : Euc d => (1 + ‖x‖) ^ (-((d + 1 : ℕ) : ℝ))) := by
    refine integrable_one_add_norm ?_
    rw [finrank_euclideanSpace_fin]; push_cast; linarith
  set J := ∫ x : Euc d, (1 + ‖x‖) ^ (-((d + 1 : ℕ) : ℝ)) with hJdef
  have hI : Integrable (fun x : Euc d => ‖φ x‖) := φ.integrable.norm
  set I := ∫ x : Euc d, ‖φ x‖ with hIdef
  have hJ0 : 0 ≤ J := integral_nonneg fun x => by positivity
  have hI0 : 0 ≤ I := integral_nonneg fun x => norm_nonneg _
  refine ⟨max (A * J) (4 * I), le_max_of_le_left (by positivity), fun z => ?_⟩
  have hint : Integrable (fun x => ‖sd (⇑φ) x z‖) := (integrable_sd_x φ z).norm
  rcases le_total ‖z‖ 1 with hz | hz
  · rw [min_eq_left (pow_le_one₀ (norm_nonneg _) hz)]
    calc ∫ x, ‖sd (⇑φ) x z‖ ≤ ∫ x : Euc d, (A * ‖z‖ ^ 2) * (1 + ‖x‖) ^ (-((d + 1 : ℕ) : ℝ)) := by
          refine integral_mono hint (hJ.const_mul _) fun x => ?_
          have h1 := hA x z hz
          have hx : 0 < (1 + ‖x‖) ^ (d + 1) := by positivity
          simp only
          rw [Real.rpow_neg (by positivity), Real.rpow_natCast, ← div_eq_mul_inv, le_div_iff₀ hx]
          exact h1
      _ = (A * J) * ‖z‖ ^ 2 := by rw [integral_const_mul]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
  · rw [min_eq_right (one_le_pow₀ hz), mul_one]
    have h2 : Integrable (fun x : Euc d => ‖φ (x - z)‖) := hI.comp_sub_right z
    have h3 : Integrable (fun x : Euc d => ‖φ (x + z)‖) := hI.comp_add_right z
    have j0 : Integrable (fun x : Euc d => 2 * ‖φ x‖) := hI.const_mul 2
    have j1 : Integrable (fun x : Euc d => 2 * ‖φ x‖ + ‖φ (x - z)‖) := j0.add h2
    have j2 : Integrable (fun x : Euc d => 2 * ‖φ x‖ + ‖φ (x - z)‖ + ‖φ (x + z)‖) := j1.add h3
    calc ∫ x, ‖sd (⇑φ) x z‖ ≤ ∫ x : Euc d, (2 * ‖φ x‖ + ‖φ (x - z)‖ + ‖φ (x + z)‖) := by
          refine integral_mono hint j2 fun x => ?_
          simp only [sd]
          calc ‖(2 : ℝ) • φ x - φ (x - z) - φ (x + z)‖
              ≤ ‖(2 : ℝ) • φ x - φ (x - z)‖ + ‖φ (x + z)‖ := norm_sub_le _ _
            _ ≤ ‖(2 : ℝ) • φ x‖ + ‖φ (x - z)‖ + ‖φ (x + z)‖ := by
                gcongr; exact norm_sub_le _ _
            _ = _ := by rw [norm_smul]; norm_num
      _ = 2 * I + I + I := by
          rw [integral_add j1 h3, integral_add j0 h2,
            integral_const_mul, integral_sub_right_eq_self (fun x : Euc d => ‖φ x‖) z,
            integral_add_right_eq_self (fun x : Euc d => ‖φ x‖) z]
      _ ≤ _ := by linarith [le_max_right (A * J) (4 * I)]


theorem KH.int_prod_sd {θ : ℝ} {𝔨 : Euc d → ℝ} (h : KH d θ 𝔨) (φ : SchwartzMap (Euc d) ℂ) :
    Integrable (fun p : Euc d × Euc d => (𝔨 p.2 : ℂ) * sd (⇑φ) p.1 p.2) (volume.prod volume) := by
  obtain ⟨M, hM0, hM⟩ := schwartz_sd_L1 φ
  have hmeas : AEStronglyMeasurable (fun p : Euc d × Euc d => (𝔨 p.2 : ℂ) * sd (⇑φ) p.1 p.2)
      (volume.prod volume) :=
    ((Complex.measurable_ofReal.comp (h.meas.comp measurable_snd)).mul
      (continuous_sd φ.continuous).measurable).aestronglyMeasurable
  rw [integrable_prod_iff' hmeas]
  refine ⟨ae_of_all _ fun z => (integrable_sd_x φ z).const_mul (𝔨 z : ℂ), ?_⟩
  refine (h.wint.const_mul M).mono' ?_ (ae_of_all _ fun z => ?_)
  · have := (hmeas.norm.prod_swap).integral_prod_right'
    exact this
  · have hnn : 0 ≤ ∫ x : Euc d, ‖(𝔨 z : ℂ) * sd (⇑φ) x z‖ := integral_nonneg fun x => norm_nonneg _
    rw [Real.norm_of_nonneg hnn]
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    rw [integral_const_mul]
    calc |𝔨 z| * ∫ x : Euc d, ‖sd (⇑φ) x z‖ ≤ |𝔨 z| * (M * min (‖z‖ ^ 2) 1) :=
          mul_le_mul_of_nonneg_left (hM z) (abs_nonneg _)
      _ = M * (|𝔨 z| * min (‖z‖ ^ 2) 1) := by ring


theorem sd_complex (f : Euc d → ℂ) (x z : Euc d) : sd f x z = 2 * f x - f (x - z) - f (x + z) := by
  simp [sd, Complex.real_smul]

theorem swap_sd (U : Euc d → ℂ) (hU : Continuous U) {B : ℝ} (hB : ∀ x, ‖U x‖ ≤ B)
    (φ : SchwartzMap (Euc d) ℂ) (z : Euc d) :
    ∫ x, sd U x z * φ x = ∫ x, U x * sd (⇑φ) x z := by
  have hφ : Integrable (⇑φ) := φ.integrable
  have a1 : Integrable (fun x => U x * φ x) :=
    hφ.bdd_mul hU.aestronglyMeasurable (ae_of_all _ hB)
  have a2 : Integrable (fun x => U (x - z) * φ x) :=
    hφ.bdd_mul (hU.comp (continuous_id.sub continuous_const)).aestronglyMeasurable
      (ae_of_all _ fun x => hB _)
  have a3 : Integrable (fun x => U (x + z) * φ x) :=
    hφ.bdd_mul (hU.comp (continuous_id.add continuous_const)).aestronglyMeasurable
      (ae_of_all _ fun x => hB _)
  have b2 : Integrable (fun x => U x * φ (x - z)) :=
    (hφ.comp_sub_right z).bdd_mul hU.aestronglyMeasurable (ae_of_all _ hB)
  have b3 : Integrable (fun x => U x * φ (x + z)) :=
    (hφ.comp_add_right z).bdd_mul hU.aestronglyMeasurable (ae_of_all _ hB)
  have e1 : ∫ x, sd U x z * φ x = ∫ x, ((2 * (U x * φ x) - U (x - z) * φ x) - U (x + z) * φ x) := by
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    simp only [sd_complex]; ring
  have e2 : ∫ x, U x * sd (⇑φ) x z = ∫ x, ((2 * (U x * φ x) - U x * φ (x - z)) - U x * φ (x + z)) := by
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    simp only [sd_complex]; ring
  have j0 : Integrable (fun x => 2 * (U x * φ x)) := a1.const_mul 2
  have k1 : Integrable (fun x => 2 * (U x * φ x) - U (x - z) * φ x) := j0.sub a2
  have k2 : Integrable (fun x => 2 * (U x * φ x) - U x * φ (x - z)) := j0.sub b2
  rw [e1, e2, integral_sub k1 a3, integral_sub j0 a2, integral_sub k2 b3, integral_sub j0 b2]
  have c1 : ∫ x, U x * φ (x + z) = ∫ x, U (x - z) * φ x := by
    have := integral_add_right_eq_self (μ := volume) (fun x => U (x - z) * φ x) z
    simpa using this
  have c2 : ∫ x, U x * φ (x - z) = ∫ x, U (x + z) * φ x := by
    have := integral_sub_right_eq_self (μ := volume) (fun x => U (x + z) * φ x) z
    simpa using this
  rw [c1, c2]; ring


theorem KH.duality {θ : ℝ} {𝔨 : Euc d → ℝ} (h : KH d θ 𝔨) (U : Euc d → ℂ) (hU : Continuous U)
    {B M : ℝ} (hB : ∀ x, ‖U x‖ ≤ B) (hsd : ∀ x z, ‖sd U x z‖ ≤ M * min (‖z‖ ^ 2) 1)
    (φ : SchwartzMap (Euc d) ℂ) :
    ∫ x, ((1 / 2 : ℂ) * ∫ z, (𝔨 z : ℂ) * sd U x z) * φ x =
      ∫ x, U x * ((1 / 2 : ℂ) * ∫ z, (𝔨 z : ℂ) * sd (⇑φ) x z) := by
  have hF1 : Integrable (fun p : Euc d × Euc d => (𝔨 p.2 : ℂ) * sd U p.1 p.2 * φ p.1)
      (volume.prod volume) := by
    have hG : Integrable (fun p : Euc d × Euc d => ‖φ p.1‖ * (M * (|𝔨 p.2| * min (‖p.2‖ ^ 2) 1)))
        (volume.prod volume) :=
      (φ.integrable.norm).mul_prod (h.wint.const_mul M)
    refine hG.mono' ?_ (ae_of_all _ fun p => ?_)
    · exact (((Complex.measurable_ofReal.comp (h.meas.comp measurable_snd)).mul
        (continuous_sd hU).measurable).mul (φ.continuous.measurable.comp measurable_fst)).aestronglyMeasurable
    · simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      have := hsd p.1 p.2
      have h0 : 0 ≤ |𝔨 p.2| := abs_nonneg _
      calc |𝔨 p.2| * ‖sd U p.1 p.2‖ * ‖φ p.1‖ ≤ |𝔨 p.2| * (M * min (‖p.2‖ ^ 2) 1) * ‖φ p.1‖ := by gcongr
        _ = _ := by ring
  have hF2 : Integrable (fun p : Euc d × Euc d => U p.1 * ((𝔨 p.2 : ℂ) * sd (⇑φ) p.1 p.2))
      (volume.prod volume) :=
    (h.int_prod_sd φ).bdd_mul (hU.comp continuous_fst).aestronglyMeasurable (ae_of_all _ fun p => hB _)
  have lhs : ∫ x, ((1 / 2 : ℂ) * ∫ z, (𝔨 z : ℂ) * sd U x z) * φ x =
      ∫ z, ∫ x, (1 / 2 : ℂ) * ((𝔨 z : ℂ) * sd U x z * φ x) := by
    have : ∀ x, ((1 / 2 : ℂ) * ∫ z, (𝔨 z : ℂ) * sd U x z) * φ x =
        ∫ z, (1 / 2 : ℂ) * ((𝔨 z : ℂ) * sd U x z * φ x) := by
      intro x
      rw [integral_const_mul, integral_mul_const]; ring
    simp_rw [this]
    exact integral_integral_swap (f := fun x z => (1 / 2 : ℂ) * ((𝔨 z : ℂ) * sd U x z * φ x))
      (hF1.const_mul (1 / 2 : ℂ))
  have rhs : ∫ x, U x * ((1 / 2 : ℂ) * ∫ z, (𝔨 z : ℂ) * sd (⇑φ) x z) =
      ∫ z, ∫ x, (1 / 2 : ℂ) * (U x * ((𝔨 z : ℂ) * sd (⇑φ) x z)) := by
    have : ∀ x, U x * ((1 / 2 : ℂ) * ∫ z, (𝔨 z : ℂ) * sd (⇑φ) x z) =
        ∫ z, (1 / 2 : ℂ) * (U x * ((𝔨 z : ℂ) * sd (⇑φ) x z)) := by
      intro x
      rw [integral_const_mul, integral_const_mul]; ring
    simp_rw [this]
    exact integral_integral_swap (f := fun x z => (1 / 2 : ℂ) * (U x * ((𝔨 z : ℂ) * sd (⇑φ) x z)))
      (hF2.const_mul (1 / 2 : ℂ))
  rw [lhs, rhs]
  refine integral_congr_ae (ae_of_all _ fun z => ?_)
  simp only
  have e1 : ∫ x, (1 / 2 : ℂ) * ((𝔨 z : ℂ) * sd U x z * φ x) =
      (1 / 2 : ℂ) * ((𝔨 z : ℂ) * ∫ x, sd U x z * φ x) := by
    rw [← integral_const_mul, ← integral_const_mul]
    congr 1; funext x; ring
  have e2 : ∫ x, (1 / 2 : ℂ) * (U x * ((𝔨 z : ℂ) * sd (⇑φ) x z)) =
      (1 / 2 : ℂ) * ((𝔨 z : ℂ) * ∫ x, U x * sd (⇑φ) x z) := by
    rw [← integral_const_mul, ← integral_const_mul]
    congr 1; funext x; ring
  rw [e1, e2, swap_sd U hU hB φ z]


/-- the plane wave `e^{2πi⟨ξ,x⟩}` -/
def ph (ξ x : Euc d) : ℂ := Complex.exp (((2 * Real.pi * inner ℝ ξ x : ℝ) : ℂ) * Complex.I)

theorem ph_sd (ξ x z : Euc d) :
    2 * ph ξ x - ph ξ (x - z) - ph ξ (x + z) = 2 * ((LevyAux.phase ξ z : ℝ) : ℂ) * ph ξ x := by
  unfold ph LevyAux.phase
  set a : ℝ := 2 * Real.pi * inner ℝ ξ x with ha
  set t : ℝ := 2 * Real.pi * inner ℝ ξ z with ht
  have e1 : 2 * Real.pi * inner ℝ ξ (x - z) = a - t := by
    rw [inner_sub_right]; ring
  have e2 : 2 * Real.pi * inner ℝ ξ (x + z) = a + t := by
    rw [inner_add_right]; ring
  rw [e1, e2]
  have hc : Complex.cos (t : ℂ) = (Complex.exp ((t : ℂ) * Complex.I) + Complex.exp (-(t : ℂ) * Complex.I)) / 2 := by
    rw [Complex.cos]
  push_cast
  have h1 : Complex.exp (((a : ℂ) - t) * Complex.I) = Complex.exp ((a : ℂ) * Complex.I) * Complex.exp (-(t : ℂ) * Complex.I) := by
    rw [← Complex.exp_add]; congr 1; ring
  have h2 : Complex.exp (((a : ℂ) + t) * Complex.I) = Complex.exp ((a : ℂ) * Complex.I) * Complex.exp ((t : ℂ) * Complex.I) := by
    rw [← Complex.exp_add]; congr 1; ring
  rw [h1, h2]
  have : (1 : ℂ) - Complex.cos (t : ℂ) = 1 - (Complex.exp ((t : ℂ) * Complex.I) + Complex.exp (-(t : ℂ) * Complex.I)) / 2 := by
    rw [hc]
  rw [this]; ring


theorem norm_ph (ξ x : Euc d) : ‖ph ξ x‖ = 1 := Complex.norm_exp_ofReal_mul_I _

theorem continuous_ph_left (x : Euc d) : Continuous (fun ξ : Euc d => ph ξ x) := by
  unfold ph; fun_prop

theorem integrable_FT (φ : SchwartzMap (Euc d) ℂ) : Integrable (𝓕 (⇑φ)) := by
  have := (𝓕 φ : SchwartzMap (Euc d) ℂ).integrable (μ := volume)
  simpa [SchwartzMap.fourier_coe] using this

theorem integrable_ph_FT (φ : SchwartzMap (Euc d) ℂ) (x : Euc d) :
    Integrable (fun ξ => ph ξ x * 𝓕 (⇑φ) ξ) :=
  (integrable_FT φ).bdd_mul (continuous_ph_left x).aestronglyMeasurable
    (ae_of_all _ fun ξ => (norm_ph ξ x).le)

theorem inv_formula' (φ : SchwartzMap (Euc d) ℂ) (x : Euc d) :
    φ x = ∫ ξ, ph ξ x * 𝓕 (⇑φ) ξ := by
  have := LevyAux.inv_formula φ x
  simpa [ph, SchwartzMap.fourier_coe, smul_eq_mul] using this

theorem sd_fourier (φ : SchwartzMap (Euc d) ℂ) (x z : Euc d) :
    sd (⇑φ) x z = ∫ ξ, 2 * ((LevyAux.phase ξ z : ℝ) : ℂ) * (ph ξ x * 𝓕 (⇑φ) ξ) := by
  have i0 := integrable_ph_FT φ x
  have i1 := integrable_ph_FT φ (x - z)
  have i2 := integrable_ph_FT φ (x + z)
  have j0 : Integrable (fun ξ => 2 * (ph ξ x * 𝓕 (⇑φ) ξ)) := i0.const_mul 2
  have j1 : Integrable (fun ξ => 2 * (ph ξ x * 𝓕 (⇑φ) ξ) - ph ξ (x - z) * 𝓕 (⇑φ) ξ) := j0.sub i1
  rw [sd_complex, inv_formula' φ x, inv_formula' φ (x - z), inv_formula' φ (x + z),
    ← integral_const_mul, ← integral_sub j0 i1, ← integral_sub j1 i2]
  refine integral_congr_ae (ae_of_all _ fun ξ => ?_)
  have := ph_sd ξ x z
  calc 2 * (ph ξ x * 𝓕 (⇑φ) ξ) - ph ξ (x - z) * 𝓕 (⇑φ) ξ - ph ξ (x + z) * 𝓕 (⇑φ) ξ
      = (2 * ph ξ x - ph ξ (x - z) - ph ξ (x + z)) * 𝓕 (⇑φ) ξ := by ring
    _ = _ := by rw [this]; ring

theorem phase_le_min (ξ z : Euc d) :
    LevyAux.phase ξ z ≤ (2 + 2 * Real.pi ^ 2 * ‖ξ‖ ^ 2) * min (‖z‖ ^ 2) 1 := by
  have h0 := LevyAux.phase_le_two ξ z
  have h1 := LevyAux.phase_le_sq ξ z
  have hp : 0 ≤ 2 * Real.pi ^ 2 * ‖ξ‖ ^ 2 := by positivity
  rcases le_total (‖z‖ ^ 2) 1 with hz | hz
  · rw [min_eq_left hz]
    nlinarith [sq_nonneg ‖z‖, mul_nonneg hp (sq_nonneg ‖z‖)]
  · rw [min_eq_right hz]
    nlinarith


theorem KH.fourier_id {θ : ℝ} {𝔨 : Euc d → ℝ} (h : KH d θ 𝔨) {m : Euc d → ℝ}
    (hs : ∀ ξ : Euc d, Integrable (fun z => 𝔨 z * (1 - Real.cos (2 * Real.pi * inner ℝ ξ z))) ∧
      ∫ z, 𝔨 z * (1 - Real.cos (2 * Real.pi * inner ℝ ξ z)) = m ξ)
    (φ : SchwartzMap (Euc d) ℂ) (x : Euc d) :
    (1 / 2 : ℂ) * ∫ z, (𝔨 z : ℂ) * sd (⇑φ) x z =
      𝓕⁻ (fun ξ : Euc d => ((m ξ : ℝ) : ℂ) * 𝓕 (⇑φ) ξ) x := by
  set Fh : Euc d → ℂ := 𝓕 (⇑φ) with hFh
  -- the function on the product
  set f : Euc d → Euc d → ℂ := fun z ξ =>
    (((𝔨 z * LevyAux.phase ξ z : ℝ)) : ℂ) * (ph ξ x * Fh ξ) with hf
  have hFhS : Integrable (fun ξ : Euc d => ‖ξ‖ ^ 2 * ‖Fh ξ‖) := by
    have := (𝓕 φ : SchwartzMap (Euc d) ℂ).integrable_pow_mul volume 2
    simpa [hFh, SchwartzMap.fourier_coe] using this
  have hG : Integrable (fun ξ : Euc d => (2 + 2 * Real.pi ^ 2 * ‖ξ‖ ^ 2) * ‖Fh ξ‖) := by
    have := ((integrable_FT φ).norm.const_mul 2).add (hFhS.const_mul (2 * Real.pi ^ 2))
    refine this.congr (ae_of_all _ fun ξ => ?_)
    simp only [Pi.add_apply, hFh]; ring
  have hint : Integrable (Function.uncurry f) (volume.prod volume) := by
    have hH : Integrable (fun p : Euc d × Euc d => (|𝔨 p.1| * min (‖p.1‖ ^ 2) 1) *
        ((2 + 2 * Real.pi ^ 2 * ‖p.2‖ ^ 2) * ‖Fh p.2‖)) (volume.prod volume) :=
      h.wint.mul_prod hG
    refine hH.mono' ?_ (ae_of_all _ fun p => ?_)
    · have hph : Continuous (fun p : Euc d × Euc d => LevyAux.phase p.2 p.1) := by
        unfold LevyAux.phase; fun_prop
      have hphc : Continuous (fun p : Euc d × Euc d => ph p.2 x) :=
        (continuous_ph_left x).comp continuous_snd
      have hFc : Continuous (fun p : Euc d × Euc d => Fh p.2) :=
        (by simpa [hFh, SchwartzMap.fourier_coe] using (𝓕 φ : SchwartzMap (Euc d) ℂ).continuous :
          Continuous Fh).comp continuous_snd
      refine (Measurable.aestronglyMeasurable ?_)
      refine (Complex.measurable_ofReal.comp ((h.meas.comp measurable_fst).mul hph.measurable)).mul
        (hphc.measurable.mul hFc.measurable)
    · simp only [Function.uncurry, hf, norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_ph, one_mul]
      have hp0 := LevyAux.phase_nonneg p.2 p.1
      have hp1 := phase_le_min p.2 p.1
      rw [abs_of_nonneg hp0]
      calc |𝔨 p.1| * LevyAux.phase p.2 p.1 * ‖Fh p.2‖
          ≤ |𝔨 p.1| * ((2 + 2 * Real.pi ^ 2 * ‖p.2‖ ^ 2) * min (‖p.1‖ ^ 2) 1) * ‖Fh p.2‖ := by gcongr
        _ = _ := by ring
  have step1 : (1 / 2 : ℂ) * ∫ z, (𝔨 z : ℂ) * sd (⇑φ) x z = ∫ z, ∫ ξ, f z ξ := by
    rw [← integral_const_mul]
    refine integral_congr_ae (ae_of_all _ fun z => ?_)
    simp only
    rw [sd_fourier φ x z, ← integral_const_mul, ← integral_const_mul]
    refine integral_congr_ae (ae_of_all _ fun ξ => ?_)
    simp only [hf]
    push_cast; ring
  have step2 : ∫ z, ∫ ξ, f z ξ = ∫ ξ, ∫ z, f z ξ := integral_integral_swap hint
  have step3 : ∀ ξ, ∫ z, f z ξ = ((m ξ : ℝ) : ℂ) * (ph ξ x * Fh ξ) := by
    intro ξ
    simp only [hf]
    rw [integral_mul_const]
    congr 1
    rw [integral_complex_ofReal]
    congr 1
    exact (hs ξ).2
  rw [step1, step2]
  simp_rw [step3]
  rw [Real.fourierInv_eq']
  refine integral_congr_ae (ae_of_all _ fun ξ => ?_)
  simp only [ph, smul_eq_mul]
  ring


theorem Kop_bound {θ : ℝ} {𝔨 : Euc d → ℝ} (h : KH d θ 𝔨) {L : ℝ} {u : Euc d → ℝ} (hu : IsC11 L u) :
    ∃ C : ℝ, ∀ x, |Kop 𝔨 u x| ≤ C := by
  obtain ⟨M, -, hM⟩ := C11_sd_bound hu
  refine ⟨(1 / 2) * (M * ∫ z, |𝔨 z| * min (‖z‖ ^ 2) 1), fun x => ?_⟩
  unfold Kop
  rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
  have := norm_integral_le_of_norm_le (h.wint.const_mul M) (f := fun z => 𝔨 z * sd u x z)
    (ae_of_all _ fun z => by
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
      calc |𝔨 z| * |sd u x z| ≤ |𝔨 z| * (M * min (‖z‖ ^ 2) 1) :=
            mul_le_mul_of_nonneg_left (hM x z) (abs_nonneg _)
        _ = M * (|𝔨 z| * min (‖z‖ ^ 2) 1) := by ring)
  rw [integral_const_mul] at this
  simpa using this

theorem measurable_Kop {θ : ℝ} {𝔨 : Euc d → ℝ} (h : KH d θ 𝔨) {u : Euc d → ℝ} (hu : Continuous u) :
    Measurable (Kop 𝔨 u) := by
  unfold Kop
  have : StronglyMeasurable (fun x : Euc d => ∫ z, 𝔨 z * sd u x z) := by
    refine StronglyMeasurable.integral_prod_right (f := fun x z => 𝔨 z * sd u x z) ?_
    exact ((h.meas.comp measurable_snd).mul (continuous_sd hu).measurable).stronglyMeasurable
  exact (this.measurable.const_mul (1 / 2))

set_option linter.unusedVariables false in
theorem pv_core (hd : 1 ≤ d) {θ : ℝ} (hθ0 : 0 < θ) (hθ2 : θ < 2) {m : Euc d → ℝ}
    (hm : IsHomogSymbol θ m) (𝔨 : Euc d → ℝ) (hev : ∀ z, 𝔨 (-z) = 𝔨 z) (hmeas : Measurable 𝔨)
    (hb : ∃ C : ℝ, ∀ z : Euc d, z ≠ 0 → |𝔨 z| ≤ C * ‖z‖ ^ (-(d : ℝ) - θ))
    (hs : ∀ ξ : Euc d, Integrable (fun z => 𝔨 z * (1 - Real.cos (2 * Real.pi * inner ℝ ξ z))) ∧
      ∫ z, 𝔨 z * (1 - Real.cos (2 * Real.pi * inner ℝ ξ z)) = m ξ) :
    ∀ (L : ℝ) (u : Euc d → ℝ), IsC11 L u → ∃ Ku : Euc d → ℝ,
      (∀ x, Tendsto (fun ε : ℝ => ∫ z in {z : Euc d | ε < ‖z‖}, 𝔨 z * (u x - u (x - z)))
        (𝓝[>] 0) (𝓝 (Ku x))) ∧
      ∀ φ : SchwartzMap (Euc d) ℂ,
        Integrable (fun x => ((Ku x : ℝ) : ℂ) * φ x) ∧
        Integrable (fun x => ((u x : ℝ) : ℂ) *
          (𝓕⁻ (fun ξ : Euc d => ((m ξ : ℝ) : ℂ) * 𝓕 (⇑φ) ξ)) x) ∧
        ∫ x, ((Ku x : ℝ) : ℂ) * φ x =
          ∫ x, ((u x : ℝ) : ℂ) * (𝓕⁻ (fun ξ : Euc d => ((m ξ : ℝ) : ℂ) * 𝓕 (⇑φ) ξ)) x := by
  have h : KH d θ 𝔨 := ⟨hd, hθ0, hθ2, hev, hmeas, hb⟩
  intro L u hu
  refine ⟨Kop 𝔨 u, fun x => h.pv_tendsto hu x, fun φ => ?_⟩
  obtain ⟨M, hM0, hM⟩ := C11_sd_bound hu
  obtain ⟨-, ⟨B, hB⟩, -, -⟩ := id hu
  obtain ⟨CK, hCK⟩ := Kop_bound h hu
  set U : Euc d → ℂ := fun x => ((u x : ℝ) : ℂ) with hU
  have hUc : Continuous U := Complex.continuous_ofReal.comp hu.1.continuous
  have hUB : ∀ x, ‖U x‖ ≤ B := fun x => by simpa [hU] using hB x
  have hsdU : ∀ x z, ‖sd U x z‖ ≤ M * min (‖z‖ ^ 2) 1 := fun x z => by
    have := hM x z
    rw [← sd_ofReal] at *
    simpa [hU, ← sd_ofReal] using this
  have hK : ∀ x, ((Kop 𝔨 u x : ℝ) : ℂ) = (1 / 2 : ℂ) * ∫ z, (𝔨 z : ℂ) * sd U x z := by
    intro x
    unfold Kop
    push_cast
    congr 1
    rw [← integral_complex_ofReal]
    refine integral_congr_ae (ae_of_all _ fun z => ?_)
    simp only [hU]
    push_cast
    rw [sd_ofReal]
  have hF : ∀ x, 𝓕⁻ (fun ξ : Euc d => ((m ξ : ℝ) : ℂ) * 𝓕 (⇑φ) ξ) x =
      (1 / 2 : ℂ) * ∫ z, (𝔨 z : ℂ) * sd (⇑φ) x z := fun x => (h.fourier_id hs φ x).symm
  refine ⟨?_, ?_, ?_⟩
  · refine φ.integrable.bdd_mul (c := CK) ?_ (ae_of_all _ fun x => ?_)
    · exact (Complex.measurable_ofReal.comp (measurable_Kop h hu.1.continuous)).aestronglyMeasurable
    · simpa using hCK x
  · simp_rw [hF]
    have := ((h.int_prod_sd φ).integral_prod_left.const_mul (1 / 2 : ℂ))
    exact this.bdd_mul (c := B) hUc.aestronglyMeasurable (ae_of_all _ hUB)
  · simp_rw [hF, hK]
    exact h.duality U hUc hUB hsdU φ

end HRS.PDE.ToolboxRd.PVAux
