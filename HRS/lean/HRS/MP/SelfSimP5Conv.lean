import HRS.MP.SelfSimP5Trunc
import HRS.MP.SelfSimP1CepaUniq

/-!
# MPP5A (6): pathwise convergence of the regularised flows `ss5_pathwise_conv`

`HRS.MP.SelfSimP5Impl.ss5_pathwise_conv_proof` has the statement of `HRS.MP.SelfSimP5.ss5_pathwise_conv`.
Route: the noise cancels, `e_n = z_n - y` is an integral of `D_n = -∇U_n(z_n) - G_y`, the energy identity
(`ssp1c_sq_integral`, coordinatewise) and the monotonicity of `∇Φ_{ε_n}` give
`|e_n(t)|² ≤ 2 ∫_0^t a_n |e_n|` with `a_n = |∇Φ_{ε_n}(y) - ∇Φ(y)|`, hence `sup |e_n| ≤ 2 ∫_0^S a_n → 0`
by dominated convergence (`|φ_ε'(g) + 1/g| ≤ 3/g`, integrable inverse gaps).
-/

open MeasureTheory Filter Topology ProbabilityTheory Set
open HRS HRS.MP.SelfSimP5
open scoped ENNReal NNReal BigOperators ContDiff

noncomputable section

namespace HRS.MP.SelfSimP5Impl

/-! ### Energy identity for an `ℝ^N`-valued integral -/

theorem ss5c_integrableOn_coord {N : ℕ} {f : ℝ → Ch5 N} {S : Set ℝ} (hf : IntegrableOn f S) (i : Fin N) :
    IntegrableOn (fun r => f r i) S := by
  have := (EuclideanSpace.proj i : Ch5 N →L[ℝ] ℝ).integrable_comp hf
  simpa [IntegrableOn] using this

theorem ss5c_intervalIntegral_coord {N : ℕ} {f : ℝ → Ch5 N} {a b : ℝ}
    (hf : IntervalIntegrable f volume a b) (i : Fin N) :
    (∫ r in a..b, f r) i = ∫ r in a..b, f r i := by
  have := (EuclideanSpace.proj i : Ch5 N →L[ℝ] ℝ).intervalIntegral_comp_comm hf
  simpa using this.symm

theorem ss5c_energy {N : ℕ} {t : ℝ} (ht : 0 ≤ t) {D : ℝ → Ch5 N} (hD : IntegrableOn D (Icc 0 t)) :
    ‖∫ r in (0 : ℝ)..t, D r‖ ^ 2 =
      2 * ∫ r in (0 : ℝ)..t, inner ℝ (D r) (∫ s in (0 : ℝ)..r, D s) := by
  have hDi : ∀ r ∈ Icc (0 : ℝ) t, IntervalIntegrable D volume 0 r := fun r hr =>
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hr.1).2
      ((hD.mono_set (fun s hs => ⟨hs.1.le, hs.2.trans hr.2⟩)))
  have hDt := hDi t ⟨ht, le_rfl⟩
  have hgi : ∀ i : Fin N, IntervalIntegrable (fun r => D r i) volume 0 t := fun i =>
    (intervalIntegrable_iff_integrableOn_Ioc_of_le ht).2
      ((ss5c_integrableOn_coord hD i).mono_set Ioc_subset_Icc_self)
  have hZc : ∀ i : Fin N, ContinuousOn (fun x => ∫ s in (0 : ℝ)..x, D s i) (uIcc 0 t) := fun i =>
    ((hgi i).absolutelyContinuousOnInterval_intervalIntegral (c := 0) (by simp)).continuousOn
  have hprod : ∀ i : Fin N, IntervalIntegrable (fun r => D r i * ∫ s in (0 : ℝ)..r, D s i) volume 0 t :=
    fun i => (hgi i).mul_continuousOn (hZc i)
  have h1 : ∀ i : Fin N, (∫ r in (0 : ℝ)..t, D r i) ^ 2 =
      2 * ∫ r in (0 : ℝ)..t, D r i * ∫ s in (0 : ℝ)..r, D s i := fun i => HRS.MP.SelfSimP1.ssp1c_sq_integral (hgi i)
  rw [EuclideanSpace.norm_sq_eq]
  simp only [Real.norm_eq_abs, sq_abs]
  have hL : ∀ i : Fin N, (∫ r in (0 : ℝ)..t, D r) i ^ 2 =
      2 * ∫ r in (0 : ℝ)..t, D r i * ∫ s in (0 : ℝ)..r, D s i := by
    intro i; rw [ss5c_intervalIntegral_coord hDt i]; exact h1 i
  simp only [hL]
  rw [← Finset.mul_sum, ← intervalIntegral.integral_finsetSum (fun i _ => hprod i)]
  congr 1
  refine intervalIntegral.integral_congr fun r hr => ?_
  have hr' : r ∈ Icc (0 : ℝ) t := by
    rw [uIcc_of_le ht] at hr; exact hr
  simp only [PiLp.inner_apply, ss5c_intervalIntegral_coord (hDi r hr')]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [mul_comm]

/-! ### A Bihari-type bound -/

theorem ss5c_bihari {S : ℝ} (hS : 0 ≤ S) {m a : ℝ → ℝ} (hm : ContinuousOn m (Icc 0 S))
    (hm0 : ∀ t ∈ Icc (0 : ℝ) S, 0 ≤ m t) (ha : IntegrableOn a (Icc 0 S))
    (ha0 : ∀ r ∈ Icc (0 : ℝ) S, 0 ≤ a r)
    (h : ∀ t ∈ Icc (0 : ℝ) S, m t ^ 2 ≤ 2 * ∫ r in (0 : ℝ)..t, a r * m r) :
    ∀ t ∈ Icc (0 : ℝ) S, m t ≤ 2 * ∫ r in (0 : ℝ)..S, a r := by
  obtain ⟨t0, ht0, hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.2 hS) hm
  have hmax' : ∀ t ∈ Icc (0 : ℝ) S, m t ≤ m t0 := fun t ht => hmax ht
  have haI : IntervalIntegrable a volume 0 S :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hS).2 (ha.mono_set Ioc_subset_Icc_self)
  have haI' : ∀ t ∈ Icc (0 : ℝ) S, IntervalIntegrable a volume 0 t := fun t ht =>
    haI.mono_set (by rw [uIcc_of_le ht.1, uIcc_of_le hS]; exact Icc_subset_Icc le_rfl ht.2)
  have hA : 0 ≤ ∫ r in (0 : ℝ)..S, a r :=
    intervalIntegral.integral_nonneg hS (fun r hr => ha0 r hr)
  have key : m t0 ^ 2 ≤ 2 * (m t0 * ∫ r in (0 : ℝ)..S, a r) := by
    refine (h t0 ht0).trans ?_
    have hmI : IntervalIntegrable (fun r => a r * m r) volume 0 t0 :=
      (haI' t0 ht0).mul_continuousOn (hm.mono (by rw [uIcc_of_le ht0.1]; exact Icc_subset_Icc le_rfl ht0.2))
    have hcI : IntervalIntegrable (fun r => a r * m t0) volume 0 t0 := (haI' t0 ht0).mul_const _
    have h1 : ∫ r in (0 : ℝ)..t0, a r * m r ≤ ∫ r in (0 : ℝ)..t0, a r * m t0 :=
      intervalIntegral.integral_mono_on ht0.1 hmI hcI fun r hr =>
        mul_le_mul_of_nonneg_left (hmax' r ⟨hr.1, hr.2.trans ht0.2⟩) (ha0 r ⟨hr.1, hr.2.trans ht0.2⟩)
    have h2 : ∫ r in (0 : ℝ)..t0, a r ≤ ∫ r in (0 : ℝ)..S, a r :=
      intervalIntegral.integral_mono_interval le_rfl ht0.1 ht0.2
        (by rw [EventuallyLE, ae_restrict_iff' measurableSet_Ioc]
            exact Eventually.of_forall fun r hr => ha0 r ⟨hr.1.le, hr.2⟩) haI
    rw [intervalIntegral.integral_mul_const] at h1
    have := mul_le_mul_of_nonneg_right h2 (hm0 t0 ht0)
    nlinarith
  have hM : m t0 ≤ 2 * ∫ r in (0 : ℝ)..S, a r := by
    rcases (hm0 t0 ht0).eq_or_lt with h0 | h0
    · rw [← h0]; linarith
    · nlinarith
  exact fun t ht => (hmax' t ht).trans hM

/-! ### The truncation error -/

theorem ss5c_d1_err {ε : ℝ} (hε : 0 < ε) {g : ℝ} (hg : 0 < g) :
    |ss5t_d1 ε g - (-(g⁻¹))| ≤ 3 * g⁻¹ := by
  unfold ss5t_d1
  split_ifs with h
  · simp; positivity
  · have hlt : g < ε := not_le.1 h
    have h1 : ε⁻¹ < g⁻¹ := inv_strictAnti₀ hg hlt
    have h2 : 0 < ε⁻¹ := inv_pos.2 hε
    have h3 : (g - ε) / ε ^ 2 ≥ -ε⁻¹ := by
      rw [ge_iff_le, le_div_iff₀ (by positivity)]
      have : ε⁻¹ * ε ^ 2 = ε := by field_simp
      nlinarith
    have h4 : (g - ε) / ε ^ 2 ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)
    rw [abs_le]
    constructor <;> nlinarith

/-! ### Pair-gradient estimates -/

theorem ss5c_continuous_gap (N : ℕ) (k l : Fin N) : Continuous fun z : Ch5 N => z l - z k := by
  have := (innerSL ℝ (ss5t_v k l)).continuous
  convert this using 1
  funext w
  simp [ss5t_inner_v]

theorem ss5c_measurable_pairGrad (N : ℕ) {f' : ℝ → ℝ} (hf' : Measurable f') :
    Measurable (ss5t_pairGrad N f') := by
  unfold ss5t_pairGrad
  have h : Measurable fun z : Ch5 N => ∑ k : Fin N, ∑ l : Fin N,
      if k < l then f' (z l - z k) • ss5t_v k l else 0 := by
    refine Finset.measurable_sum _ fun k _ => Finset.measurable_sum _ fun l _ => ?_
    by_cases hkl : k < l
    · simp only [hkl, if_true]
      exact (hf'.comp (ss5c_continuous_gap N k l).measurable).smul_const _
    · simp only [hkl, if_false]
      exact measurable_const
  exact h.const_smul (1 / (N : ℝ))

/-- The inverse-gap functional `(1/N) ∑_{k<l} (z_l - z_k)⁻¹`. -/
def ss5c_B (N : ℕ) (z : Ch5 N) : ℝ :=
  (1 / (N : ℝ)) * ∑ k : Fin N, ∑ l : Fin N, if k < l then (z l - z k)⁻¹ else 0

theorem ss5c_norm_sum2 {E : Type*} [NormedAddCommGroup E] {N : ℕ} (F : Fin N → Fin N → E)
    (b : Fin N → Fin N → ℝ) (h : ∀ k l, ‖F k l‖ ≤ b k l) :
    ‖∑ k, ∑ l, F k l‖ ≤ ∑ k, ∑ l, b k l :=
  (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ =>
    (norm_sum_le _ _).trans (Finset.sum_le_sum fun l _ => h k l))

theorem ss5c_pairGrad_sub_le {N : ℕ} (f' f'' : ℝ → ℝ) {c : ℝ} (hc : 0 ≤ c) (z : Ch5 N)
    (hz : z ∈ ss5_chamber N) (h : ∀ g, 0 < g → |f' g - f'' g| ≤ c * g⁻¹) :
    ‖ss5t_pairGrad N f' z - ss5t_pairGrad N f'' z‖ ≤ 2 * c * ss5c_B N z := by
  unfold ss5t_pairGrad ss5c_B
  rw [← smul_sub, ← Finset.sum_sub_distrib]
  simp only [← Finset.sum_sub_distrib]
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hterm : ∀ k l : Fin N, ‖(if k < l then f' (z l - z k) • ss5t_v k l else 0) -
      (if k < l then f'' (z l - z k) • ss5t_v k l else 0)‖ ≤
      2 * c * (if k < l then (z l - z k)⁻¹ else 0) := by
    intro k l
    by_cases hkl : k < l
    · simp only [hkl, if_true]
      rw [← sub_smul, norm_smul, Real.norm_eq_abs]
      have hg : 0 < z l - z k := sub_pos.2 (hz k l hkl)
      calc |f' (z l - z k) - f'' (z l - z k)| * ‖ss5t_v k l‖
          ≤ (c * (z l - z k)⁻¹) * 2 := by
            gcongr
            · exact h _ hg
            · exact ss5t_norm_v k l
        _ = 2 * c * (z l - z k)⁻¹ := by ring
    · simp [hkl]
  have := ss5c_norm_sum2 _ _ hterm
  calc 1 / (N : ℝ) * ‖∑ k : Fin N, ∑ l : Fin N, ((if k < l then f' (z l - z k) • ss5t_v k l else 0) -
        (if k < l then f'' (z l - z k) • ss5t_v k l else 0))‖
      ≤ 1 / (N : ℝ) * ∑ k : Fin N, ∑ l : Fin N, 2 * c * (if k < l then (z l - z k)⁻¹ else 0) := by
        gcongr
    _ = 2 * c * (1 / (N : ℝ) * ∑ k : Fin N, ∑ l : Fin N, if k < l then (z l - z k)⁻¹ else 0) := by
        simp only [← Finset.mul_sum]; ring

theorem ss5c_B_integrable {N : ℕ} {S : ℝ} {y : ℝ → Ch5 N}
    (hgap : ∀ k l : Fin N, k < l → IntegrableOn (fun r : ℝ => (y r l - y r k)⁻¹) (Icc (0 : ℝ) S)) :
    IntegrableOn (fun r => ss5c_B N (y r)) (Icc (0 : ℝ) S) := by
  unfold ss5c_B
  refine Integrable.const_mul ?_ _
  refine integrable_finsetSum _ fun k _ => integrable_finsetSum _ fun l _ => ?_
  by_cases hkl : k < l
  · simp only [hkl, if_true]; exact hgap k l hkl
  · simp only [hkl, if_false]; exact integrable_zero _ _ _

/-! ### The pointwise energy inequality -/

theorem ss5c_pointwise {N : ℕ} {ε : ℝ} (hε : 0 < ε) (z y : Ch5 N) :
    inner ℝ (-(gradient (ss5_U N ε) z) -
        (-(ss5t_pairGrad N (fun g => -(g⁻¹)) y) - (1 / 2 : ℝ) • y)) (z - y) ≤
      ‖ss5t_pairGrad N (ss5t_d1 ε) y - ss5t_pairGrad N (fun g => -(g⁻¹)) y‖ * ‖z - y‖ := by
  have hmono := ss5t_monotone hε z y
  rw [ss5t_gradient_PhiTr hε, ss5t_gradient_PhiTr hε] at hmono
  rw [ss5t_gradient_U hε]
  have hD : -(ss5t_pairGrad N (ss5t_d1 ε) z + (1 / 2 : ℝ) • z) -
        (-(ss5t_pairGrad N (fun g => -(g⁻¹)) y) - (1 / 2 : ℝ) • y) =
      -(ss5t_pairGrad N (ss5t_d1 ε) z - ss5t_pairGrad N (ss5t_d1 ε) y) -
        (ss5t_pairGrad N (ss5t_d1 ε) y - ss5t_pairGrad N (fun g => -(g⁻¹)) y) -
        (1 / 2 : ℝ) • (z - y) := by module
  rw [hD]
  generalize ss5t_pairGrad N (ss5t_d1 ε) z - ss5t_pairGrad N (ss5t_d1 ε) y = A at hmono ⊢
  generalize ss5t_pairGrad N (ss5t_d1 ε) y - ss5t_pairGrad N (fun g => -(g⁻¹)) y = Bv
  generalize z - y = e at hmono ⊢
  rw [inner_sub_left, inner_sub_left, inner_neg_left, inner_smul_left, real_inner_self_eq_norm_sq]
  have h1 := (abs_le.1 (abs_real_inner_le_norm Bv e)).1
  simp only [conj_trivial]
  nlinarith [sq_nonneg ‖e‖]

theorem ss5c_pairGrad_zero (N : ℕ) (z : Ch5 N) : ss5t_pairGrad N (fun _ => 0) z = 0 := by
  simp [ss5t_pairGrad]

theorem ss5c_interval_of_integrableOn {E : Type*} [NormedAddCommGroup E] {f : ℝ → E} {S t : ℝ}
    (hf : IntegrableOn f (Icc 0 S)) (ht0 : 0 ≤ t) (htS : t ≤ S) : IntervalIntegrable f volume 0 t :=
  (intervalIntegrable_iff_integrableOn_Ioc_of_le ht0).2
    (hf.mono_set (fun r hr => ⟨hr.1.le, hr.2.trans htS⟩))

/-- Dominated-convergence step: the truncation error of the gradients tends to zero in `L¹[0,S]`. -/
theorem ss5c_error_tendsto {N : ℕ} {S : ℝ} (hS : 0 ≤ S) {y : ℝ → Ch5 N} (hyc : Continuous y)
    (hyC : ∀ᵐ r ∂volume, r ∈ Icc (0 : ℝ) S → y r ∈ ss5_chamber N)
    (hgap : ∀ k l : Fin N, k < l → IntegrableOn (fun r : ℝ => (y r l - y r k)⁻¹) (Icc (0 : ℝ) S)) :
    Tendsto (fun n : ℕ => ∫ r in (0 : ℝ)..S,
      ‖ss5t_pairGrad N (ss5t_d1 (ss5_eps n)) (y r) - ss5t_pairGrad N (fun g => -(g⁻¹)) (y r)‖)
      atTop (𝓝 0) := by
  have hBint := ss5c_B_integrable hgap
  have hmeas : ∀ n : ℕ, Measurable fun r => ‖ss5t_pairGrad N (ss5t_d1 (ss5_eps n)) (y r) -
      ss5t_pairGrad N (fun g => -(g⁻¹)) (y r)‖ := by
    intro n
    have h1 : Measurable (ss5t_pairGrad N (ss5t_d1 (ss5_eps n))) :=
      ss5c_measurable_pairGrad N (ss5t_contDiff_d1 (ss5_eps_pos n)).continuous.measurable
    have h2 : Measurable (ss5t_pairGrad N (fun g : ℝ => -(g⁻¹))) :=
      ss5c_measurable_pairGrad N (measurable_inv.neg)
    exact ((h1.comp hyc.measurable).sub (h2.comp hyc.measurable)).norm
  simp only [intervalIntegral.integral_of_le hS]
  have := tendsto_integral_of_dominated_convergence (μ := volume.restrict (Ioc (0 : ℝ) S))
    (F := fun (n : ℕ) r => ‖ss5t_pairGrad N (ss5t_d1 (ss5_eps n)) (y r) -
      ss5t_pairGrad N (fun g => -(g⁻¹)) (y r)‖) (f := fun _ => (0 : ℝ))
    (fun r => 6 * ss5c_B N (y r)) (fun n => (hmeas n).aestronglyMeasurable)
    (IntegrableOn.mono_set (hBint.const_mul 6) Ioc_subset_Icc_self) ?_ ?_
  · simpa using this
  · intro n
    rw [ae_restrict_iff' measurableSet_Ioc]
    filter_upwards [hyC] with r hr hrI
    have hch := hr ⟨hrI.1.le, hrI.2⟩
    rw [norm_norm]
    have := ss5c_pairGrad_sub_le (ss5t_d1 (ss5_eps n)) (fun g => -(g⁻¹)) (c := 3) (by norm_num) (y r) hch
      (fun g hg => ss5c_d1_err (ss5_eps_pos n) hg)
    linarith
  · rw [ae_restrict_iff' measurableSet_Ioc]
    filter_upwards [hyC] with r hr hrI
    have hch := hr ⟨hrI.1.le, hrI.2⟩
    have hev : ∀ᶠ n : ℕ in atTop, ∀ k l : Fin N, k < l → ss5_eps n ≤ y r l - y r k := by
      rw [Filter.eventually_all]
      intro k
      rw [Filter.eventually_all]
      intro l
      by_cases hkl : k < l
      · have hg : 0 < y r l - y r k := sub_pos.2 (hch k l hkl)
        have : ∀ᶠ n : ℕ in atTop, ss5_eps n < y r l - y r k :=
          (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).eventually (gt_mem_nhds hg)
        filter_upwards [this] with n hn _ using hn.le
      · exact Eventually.of_forall fun n h => absurd h hkl
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hev] with n hn
    symm
    have : ss5t_pairGrad N (ss5t_d1 (ss5_eps n)) (y r) = ss5t_pairGrad N (fun g => -(g⁻¹)) (y r) := by
      unfold ss5t_pairGrad
      congr 2
      funext k
      congr 1
      funext l
      by_cases hkl : k < l
      · simp only [hkl, if_true]
        unfold ss5t_d1
        rw [if_pos (hn k l hkl)]
      · simp [hkl]
    rw [this, sub_self, norm_zero]

theorem ss5_pathwise_conv_proof {N : ℕ} {S : ℝ} (hS : 0 ≤ S) {y w : ℝ → Ch5 N} {y0 : Ch5 N}
    (hyc : Continuous y)
    (hyC : ∀ᵐ r ∂volume, r ∈ Icc (0 : ℝ) S → y r ∈ ss5_chamber N)
    (hgap : ∀ k l : Fin N, k < l → IntegrableOn (fun r : ℝ => (y r l - y r k)⁻¹) (Icc (0 : ℝ) S))
    (hy : ∀ t ∈ Icc (0 : ℝ) S,
      y t = y0 + (∫ r in (0 : ℝ)..t, (-(gradient (ss5_Phi N) (y r)) - (1 / 2 : ℝ) • y r)) + w t)
    {z : ℕ → ℝ → Ch5 N} (hzc : ∀ n, Continuous (z n))
    (hz : ∀ n, ∀ t ∈ Icc (0 : ℝ) S,
      z n t = y0 + (∫ r in (0 : ℝ)..t, -(gradient (ss5_U N (ss5_eps n)) (z n r))) + w t) :
    ∀ t ∈ Icc (0 : ℝ) S, Tendsto (fun n => z n t) atTop (𝓝 (y t)) := by
  classical
  have hBint := ss5c_B_integrable hgap
  -- the explicit drift of `y`
  set Gy : ℝ → Ch5 N := fun r => -(ss5t_pairGrad N (fun g => -(g⁻¹)) (y r)) - (1 / 2 : ℝ) • y r with hGy
  have hGy_meas : Measurable Gy := by
    have h2 : Measurable (ss5t_pairGrad N (fun g : ℝ => -(g⁻¹))) :=
      ss5c_measurable_pairGrad N (measurable_inv.neg)
    exact (h2.comp hyc.measurable).neg.sub (hyc.measurable.const_smul (1 / 2 : ℝ))
  have hGy_int : IntegrableOn Gy (Icc 0 S) := by
    have hb : IntegrableOn (fun r => 2 * ss5c_B N (y r) + 1 / 2 * ‖y r‖) (Icc 0 S) :=
      (hBint.const_mul 2).add ((hyc.norm.const_mul (1 / 2)).integrableOn_Icc)
    refine Integrable.mono' hb hGy_meas.aestronglyMeasurable ?_
    rw [ae_restrict_iff' measurableSet_Icc]
    filter_upwards [hyC] with r hr hrI
    have hch := hr hrI
    have := ss5c_pairGrad_sub_le (fun g : ℝ => -(g⁻¹)) (fun _ => 0) (c := 1) (by norm_num) (y r) hch
      (fun g hg => by simp [abs_of_pos (inv_pos.2 hg)])
    rw [ss5c_pairGrad_zero, sub_zero] at this
    calc ‖Gy r‖ ≤ ‖-(ss5t_pairGrad N (fun g => -(g⁻¹)) (y r))‖ + ‖(1 / 2 : ℝ) • y r‖ := norm_sub_le _ _
      _ ≤ 2 * ss5c_B N (y r) + 1 / 2 * ‖y r‖ := by
        rw [norm_neg, norm_smul]; norm_num; linarith
  have hy' : ∀ t ∈ Icc (0 : ℝ) S, y t = y0 + (∫ r in (0 : ℝ)..t, Gy r) + w t := by
    intro t ht
    rw [hy t ht]
    congr 2
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [hyC] with r hr hrI
    rw [uIoc_of_le ht.1] at hrI
    rw [ss5t_gradient_Phi (hr ⟨hrI.1.le, hrI.2.trans ht.2⟩)]
  have hA_tend := ss5c_error_tendsto hS hyc hyC hgap
  have hbound : ∀ n : ℕ, ∀ t ∈ Icc (0 : ℝ) S, ‖z n t - y t‖ ≤
      2 * ∫ r in (0 : ℝ)..S, ‖ss5t_pairGrad N (ss5t_d1 (ss5_eps n)) (y r) -
        ss5t_pairGrad N (fun g => -(g⁻¹)) (y r)‖ := by
    intro n
    obtain ⟨-, ⟨K, hK⟩, -, -⟩ := ss5_trunc_props_proof N (ss5_eps_pos n) (ss5_eps_le_one n)
    have hε := ss5_eps_pos n
    set an : ℝ → ℝ := fun r => ‖ss5t_pairGrad N (ss5t_d1 (ss5_eps n)) (y r) -
      ss5t_pairGrad N (fun g => -(g⁻¹)) (y r)‖ with han
    set Dn : ℝ → Ch5 N := fun r => -(gradient (ss5_U N (ss5_eps n)) (z n r)) - Gy r with hDn
    have hgc : Continuous fun r => gradient (ss5_U N (ss5_eps n)) (z n r) := hK.continuous.comp (hzc n)
    have hDn_meas : Measurable Dn := hgc.measurable.neg.sub hGy_meas
    have hDn_int : IntegrableOn Dn (Icc 0 S) := (hgc.neg.integrableOn_Icc).sub hGy_int
    have han_meas : Measurable an := by
      have h1 : Measurable (ss5t_pairGrad N (ss5t_d1 (ss5_eps n))) :=
        ss5c_measurable_pairGrad N (ss5t_contDiff_d1 hε).continuous.measurable
      have h2 : Measurable (ss5t_pairGrad N (fun g : ℝ => -(g⁻¹))) :=
        ss5c_measurable_pairGrad N (measurable_inv.neg)
      exact ((h1.comp hyc.measurable).sub (h2.comp hyc.measurable)).norm
    have han_int : IntegrableOn an (Icc 0 S) := by
      refine Integrable.mono' (hBint.const_mul 6) han_meas.aestronglyMeasurable ?_
      rw [ae_restrict_iff' measurableSet_Icc]
      filter_upwards [hyC] with r hr hrI
      have := ss5c_pairGrad_sub_le (ss5t_d1 (ss5_eps n)) (fun g => -(g⁻¹)) (c := 3) (by norm_num) (y r)
        (hr hrI) (fun g hg => ss5c_d1_err hε hg)
      rw [han]; simp only [norm_norm]
      linarith
    set m : ℝ → ℝ := fun r => ‖z n r - y r‖ with hm
    have hmc : Continuous m := ((hzc n).sub hyc).norm
    have hE : ∀ t ∈ Icc (0 : ℝ) S, z n t - y t = ∫ r in (0 : ℝ)..t, Dn r := by
      intro t ht
      have hI1 : IntervalIntegrable (fun r => -(gradient (ss5_U N (ss5_eps n)) (z n r))) volume 0 t :=
        hgc.neg.intervalIntegrable 0 t
      have hI2 : IntervalIntegrable Gy volume 0 t := ss5c_interval_of_integrableOn hGy_int ht.1 ht.2
      have : ∫ r in (0 : ℝ)..t, Dn r =
          (∫ r in (0 : ℝ)..t, -(gradient (ss5_U N (ss5_eps n)) (z n r))) - ∫ r in (0 : ℝ)..t, Gy r :=
        intervalIntegral.integral_sub hI1 hI2
      rw [this, hz n t ht, hy' t ht]
      abel
    obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn
      (f := fun r => z n r - y r) ((hzc n).sub hyc).continuousOn (s := Icc (0 : ℝ) S)
    have hI_in : IntegrableOn (fun r => inner ℝ (Dn r) (z n r - y r)) (Icc 0 S) := by
      refine Integrable.mono' (hDn_int.norm.mul_const M)
        (hDn_meas.inner ((hzc n).sub hyc).measurable).aestronglyMeasurable ?_
      rw [ae_restrict_iff' measurableSet_Icc]
      refine Eventually.of_forall fun r hr => ?_
      calc ‖inner ℝ (Dn r) (z n r - y r)‖ ≤ ‖Dn r‖ * ‖z n r - y r‖ := norm_inner_le_norm _ _
        _ ≤ ‖Dn r‖ * M := by gcongr; exact hM r hr
    have hI_a : IntegrableOn (fun r => an r * m r) (Icc 0 S) :=
      han_int.mul_continuousOn hmc.continuousOn isCompact_Icc
    have hineq : ∀ t ∈ Icc (0 : ℝ) S, m t ^ 2 ≤ 2 * ∫ r in (0 : ℝ)..t, an r * m r := by
      intro t ht
      have hsub : Icc (0 : ℝ) t ⊆ Icc 0 S := Icc_subset_Icc le_rfl ht.2
      have h1 := ss5c_energy ht.1 (hDn_int.mono_set hsub)
      rw [← hE t ht] at h1
      have h2 : ∫ r in (0 : ℝ)..t, inner ℝ (Dn r) (∫ s in (0 : ℝ)..r, Dn s) =
          ∫ r in (0 : ℝ)..t, inner ℝ (Dn r) (z n r - y r) := by
        refine intervalIntegral.integral_congr fun r hr => ?_
        rw [uIcc_of_le ht.1] at hr
        rw [← hE r ⟨hr.1, hr.2.trans ht.2⟩]
      have h3 : ∫ r in (0 : ℝ)..t, inner ℝ (Dn r) (z n r - y r) ≤ ∫ r in (0 : ℝ)..t, an r * m r := by
        refine intervalIntegral.integral_mono_ae_restrict ht.1
          (ss5c_interval_of_integrableOn hI_in ht.1 ht.2) (ss5c_interval_of_integrableOn hI_a ht.1 ht.2) ?_
        exact Eventually.of_forall fun r => ss5c_pointwise hε (z n r) (y r)
      rw [h2] at h1
      show ‖z n t - y t‖ ^ 2 ≤ _
      linarith
    exact ss5c_bihari hS hmc.continuousOn (fun _ _ => norm_nonneg _) han_int
      (fun r _ => norm_nonneg _) hineq
  intro t ht
  have hsq := hA_tend.const_mul 2
  rw [mul_zero] at hsq
  exact tendsto_iff_norm_sub_tendsto_zero.2
    (squeeze_zero (fun n => norm_nonneg _) (fun n => hbound n t ht) hsq)

example := (@ss5_pathwise_conv_proof : type_of% @HRS.MP.SelfSimP5.ss5_pathwise_conv)

end HRS.MP.SelfSimP5Impl
