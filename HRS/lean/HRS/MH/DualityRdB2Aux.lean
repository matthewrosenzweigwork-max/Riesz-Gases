import HRS.MH.DualityRdB1

/-!
# DualityRd packet B2 (auxiliary): continuity of the mean-field path on `ℝ^d`

Helpers for `mf_continuity` (`DualityRdB2.lean`): the weighted decay `ρ_t(x) ≤ Λ ⟨x⟩^{-(d+3)}`, uniform
Lipschitz bounds in `x`, the approximate identity with a quantitative error, continuity of `t ↦ ⟨ρ_t, φ⟩`,
joint continuity of `(u,t) ↦ ⟨ρ_t, φ_u⟩`, and joint continuity of the test functions `(t,x) ↦ ∇f_t(x), Δf_t(x)`.
Helper names carry the prefix `db2_`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MH.DualityRd

open HRS.Whole HRS.Whole.AppendixA

variable {d : ℕ}

/-! ### The Japanese bracket -/

theorem db2_jb_pos (x : Euc d) : 0 < jbracket x := Real.sqrt_pos.2 (by positivity)

theorem db2_jb_sq (x : Euc d) : jbracket x ^ 2 = 1 + ‖x‖ ^ 2 := by
  unfold jbracket
  rw [Real.sq_sqrt (by positivity)]

theorem db2_jb_one_le (x : Euc d) : 1 ≤ jbracket x := by
  have h := db2_jb_sq x
  have := db2_jb_pos x
  nlinarith [norm_nonneg x]

theorem db2_one_add_le (x : Euc d) : 1 + ‖x‖ ≤ 2 * jbracket x := by
  have h := db2_jb_sq x
  have := db2_jb_pos x
  nlinarith [norm_nonneg x, sq_nonneg (‖x‖ - 1), sq_nonneg (jbracket x - 1)]

theorem db2_jb_rpow (x : Euc d) (r : ℝ) : jbracket x ^ (-r) = (1 + ‖x‖ ^ 2) ^ (-r / 2) := by
  unfold jbracket
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (by positivity)]
  congr 1
  ring

theorem db2_m_meas : Measurable (fun x : Euc d => jbracket x ^ (-((d : ℝ) + 3))) := by
  unfold jbracket
  fun_prop

theorem db2_m_integrable : Integrable (fun x : Euc d => jbracket x ^ (-((d : ℝ) + 3)) * (1 + ‖x‖)) := by
  have hnr : (Module.finrank ℝ (Euc d) : ℝ) < (d : ℝ) + 2 := by
    rw [finrank_euclideanSpace_fin]; linarith
  have hg := (integrable_rpow_neg_one_add_norm_sq (μ := (volume : Measure (Euc d))) hnr).const_mul 2
  refine hg.mono' ((db2_m_meas).mul (by fun_prop)).aestronglyMeasurable (Filter.Eventually.of_forall fun x => ?_)
  have hm : 0 ≤ jbracket x ^ (-((d : ℝ) + 3)) := Real.rpow_nonneg (db2_jb_pos x).le _
  have hpow : jbracket x ^ (-((d : ℝ) + 2)) = jbracket x ^ (-((d : ℝ) + 3)) * jbracket x := by
    rw [show -((d : ℝ) + 2) = -((d : ℝ) + 3) + 1 by ring, Real.rpow_add (db2_jb_pos x), Real.rpow_one]
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hm (by positivity))]
  have e2 : jbracket x ^ (-((d : ℝ) + 2)) = (1 + ‖x‖ ^ 2) ^ (-(((d : ℝ) + 2)) / 2) :=
    db2_jb_rpow x _
  calc jbracket x ^ (-((d : ℝ) + 3)) * (1 + ‖x‖)
      ≤ jbracket x ^ (-((d : ℝ) + 3)) * (2 * jbracket x) := mul_le_mul_of_nonneg_left (db2_one_add_le x) hm
    _ = 2 * jbracket x ^ (-((d : ℝ) + 2)) := by rw [hpow]; ring
    _ = 2 * (1 + ‖x‖ ^ 2) ^ (-(((d : ℝ) + 2)) / 2) := by rw [e2]

theorem db2_m_integrable' : Integrable (fun x : Euc d => jbracket x ^ (-((d : ℝ) + 3))) := by
  refine db2_m_integrable.mono' db2_m_meas.aestronglyMeasurable (Filter.Eventually.of_forall fun x => ?_)
  have hm : 0 ≤ jbracket x ^ (-((d : ℝ) + 3)) := Real.rpow_nonneg (db2_jb_pos x).le _
  rw [Real.norm_eq_abs, abs_of_nonneg hm]
  exact le_mul_of_one_le_right hm (by linarith [norm_nonneg x])

/-! ### Decay and Lipschitz bounds of the densities -/

theorem db2_deriv_le_cbNorm {k : ℕ} {f : Euc d → ℝ} (hf : MemCb k f) {j : ℕ} (hj : j ≤ k) (x : Euc d) :
    ‖iteratedFDeriv ℝ j f x‖ ≤ HRS.cbNorm k f := by
  have h0 : ‖iteratedFDeriv ℝ j f x‖ ≤ ⨆ z : Euc d, ‖iteratedFDeriv ℝ j f z‖ := le_ciSup (hf.2 j hj) x
  refine h0.trans ?_
  unfold HRS.cbNorm
  exact Finset.single_le_sum (f := fun i => ⨆ z : Euc d, ‖iteratedFDeriv ℝ i f z‖)
    (fun i _ => Real.iSup_nonneg fun z => norm_nonneg _) (Finset.mem_range.2 (Nat.lt_succ_of_le hj))

/-- A `C¹` function with `‖Df‖ ≤ C` is `C`-Lipschitz. -/
theorem db2_lip_of {F : Euc d → ℝ} (hF : ContDiff ℝ 1 F) {C : ℝ} (hC : ∀ z, ‖fderiv ℝ F z‖ ≤ C)
    (x y : Euc d) : |F x - F y| ≤ C * ‖x - y‖ := by
  have h := Convex.norm_image_sub_le_of_norm_fderiv_le (f := F) (s := Set.univ) (C := C)
    (fun z _ => hF.differentiable (by norm_num) z) (fun z _ => hC z) convex_univ
    (Set.mem_univ y) (Set.mem_univ x)
  rw [← Real.norm_eq_abs]
  exact h

theorem db2_rho_lip {s Λ T ΛV G₀ : ℝ} {D : WholeDyn d} {ρ : ℝ → Euc d → ℝ} (h : MFData s Λ T ΛV G₀ D ρ)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) (x y : Euc d) : |ρ t x - ρ t y| ≤ Λ * ‖x - y‖ := by
  obtain ⟨hmem, -, hcb⟩ := h.hreg.1 t ht
  have hc0 : 0 ≤ HRS.cbNorm 3 (ρ t) := (abs_nonneg _).trans (db1_abs_le_cbNorm hmem 0)
  have hW : 0 ≤ (weightedSupE 3 ((d : ℝ) + 3) (ρ t)).toReal := ENNReal.toReal_nonneg
  refine db2_lip_of (hmem.1.of_le (by norm_num)) (fun z => ?_) x y
  rw [← norm_iteratedFDeriv_one]
  have := db2_deriv_le_cbNorm hmem (j := 1) (by norm_num) z
  linarith

theorem db2_rho_bound {s Λ T ΛV G₀ : ℝ} {D : WholeDyn d} {ρ : ℝ → Euc d → ℝ} (h : MFData s Λ T ΛV G₀ D ρ)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) (x : Euc d) : ρ t x ≤ Λ * jbracket x ^ (-((d : ℝ) + 3)) := by
  obtain ⟨hmem, hfin, hcb⟩ := h.hreg.1 t ht
  have hc0 : 0 ≤ HRS.cbNorm 3 (ρ t) := (abs_nonneg _).trans (db1_abs_le_cbNorm hmem 0)
  have hW : (weightedSupE 3 ((d : ℝ) + 3) (ρ t)).toReal ≤ Λ := by linarith
  have h1 := Q09B.q09b_jbracket_bound (r := 3) (L := (d : ℝ) + 3) hfin x
  have hJ : 0 < jbracket x ^ ((d : ℝ) + 3) := Real.rpow_pos_of_pos (db2_jb_pos x) _
  rw [Real.rpow_neg (db2_jb_pos x).le, ← div_eq_mul_inv, le_div_iff₀ hJ]
  have := mul_le_mul_of_nonneg_left (le_abs_self (ρ t x)) hJ.le
  nlinarith

/-! ### The approximate identity with a quantitative error -/

/-- The normalized `n`-th bump as a function. -/
def db2_eta (n : ℕ) : Euc d → ℝ := (db1_bump d n).normed volume

theorem db2_eta_nonneg (n : ℕ) (z : Euc d) : 0 ≤ db2_eta (d := d) n z :=
  ContDiffBump.nonneg_normed (f := db1_bump d n) (μ := volume) z

theorem db2_eta_integral (n : ℕ) : ∫ z, db2_eta (d := d) n z = 1 :=
  ContDiffBump.integral_normed (f := db1_bump d n) (μ := volume)

theorem db2_eta_zero (n : ℕ) {z : Euc d} (hz : (db1_bump d n).rOut ≤ ‖z‖) : db2_eta (d := d) n z = 0 := by
  by_contra hne
  have hmem : z ∈ Function.support (db2_eta (d := d) n) := hne
  unfold db2_eta at hmem
  rw [ContDiffBump.support_normed_eq] at hmem
  rw [Metric.mem_ball, dist_zero_right] at hmem
  linarith

theorem db2_eta_cont (n : ℕ) : Continuous (db2_eta (d := d) n) := by
  have hc : ContDiff ℝ 2 (db2_eta (d := d) n) := ContDiffBump.contDiff_normed (f := db1_bump d n) (μ := volume)
  exact hc.continuous

theorem db2_eta_shift_int (n : ℕ) (x : Euc d) : Integrable (fun y => db2_eta (d := d) n (x - y)) := by
  refine Continuous.integrable_of_hasCompactSupport ((db2_eta_cont n).comp (continuous_const.sub continuous_id)) ?_
  exact (ContDiffBump.hasCompactSupport_normed (f := db1_bump d n) (μ := volume)).comp_homeomorph
    (Homeomorph.subLeft x)

/-- The quantitative approximate identity: `|⟨ρ_t, η_n(x - ·)⟩ - ρ_t(x)| ≤ Λ r_n`. -/
theorem db2_pair_approx {s Λ T ΛV G₀ : ℝ} {D : WholeDyn d} {ρ : ℝ → Euc d → ℝ} (h : MFData s Λ T ΛV G₀ D ρ)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) (x : Euc d) (n : ℕ) :
    |Whole.pair (Whole.withDensityReal (ρ t)) (fun y => db2_eta (d := d) n (x - y)) - ρ t x|
      ≤ Λ * (db1_bump d n).rOut := by
  have hρ := h.hρ.density t ht
  have hρc : Continuous (ρ t) := db1_cont h ht
  have hρb := db1_sup h ht
  have hΛ := db1_Lambda_nonneg h (le_trans ht.1 ht.2)
  have hr0 : 0 ≤ (db1_bump d n).rOut := by
    show 0 ≤ 1 / ((n : ℝ) + 1)
    positivity
  have hint : ∫ y, ρ t x * db2_eta (d := d) n (x - y) = ρ t x := by
    rw [integral_const_mul, integral_sub_left_eq_self (fun z => db2_eta (d := d) n z) volume x,
      db2_eta_integral, mul_one]
  have hi1 : Integrable (fun y => ρ t y * db2_eta (d := d) n (x - y)) := by
    refine ((db2_eta_shift_int n x).const_mul Λ).mono'
      (hρc.measurable.mul ((db2_eta_cont n).measurable.comp (measurable_const.sub measurable_id))).aestronglyMeasurable
      (Filter.Eventually.of_forall fun y => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hρ.nonneg y) (db2_eta_nonneg n _))]
    exact mul_le_mul_of_nonneg_right (hρb y) (db2_eta_nonneg n _)
  have hi2 : Integrable (fun y => ρ t x * db2_eta (d := d) n (x - y)) :=
    (db2_eta_shift_int n x).const_mul _
  have hsub : ∫ y, (ρ t y * db2_eta (d := d) n (x - y) - ρ t x * db2_eta (d := d) n (x - y))
      = (∫ y, ρ t y * db2_eta (d := d) n (x - y)) - ∫ y, ρ t x * db2_eta (d := d) n (x - y) :=
    integral_sub hi1 hi2
  have hpt : (fun y => ρ t y * db2_eta (d := d) n (x - y) - ρ t x * db2_eta (d := d) n (x - y))
      = fun y => (ρ t y - ρ t x) * db2_eta (d := d) n (x - y) := funext fun y => by ring
  rw [hpt, hint] at hsub
  have key : Whole.pair (Whole.withDensityReal (ρ t)) (fun y => db2_eta (d := d) n (x - y)) - ρ t x
      = ∫ y, (ρ t y - ρ t x) * db2_eta (d := d) n (x - y) := by
    rw [Q09A.pair_withDensityReal hρ]
    linarith
  rw [key, ← Real.norm_eq_abs]
  have hgi : Integrable (fun y => Λ * (db1_bump d n).rOut * db2_eta (d := d) n (x - y)) :=
    (db2_eta_shift_int n x).const_mul _
  calc ‖∫ y, (ρ t y - ρ t x) * db2_eta (d := d) n (x - y)‖
      ≤ ∫ y, Λ * (db1_bump d n).rOut * db2_eta (d := d) n (x - y) := by
        refine norm_integral_le_of_norm_le hgi (Filter.Eventually.of_forall fun y => ?_)
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (db2_eta_nonneg n _)]
        by_cases hlt : ‖x - y‖ < (db1_bump d n).rOut
        · have hl := db2_rho_lip h ht y x
          rw [norm_sub_rev] at hl
          have h1 : |ρ t y - ρ t x| ≤ Λ * (db1_bump d n).rOut :=
            hl.trans (mul_le_mul_of_nonneg_left hlt.le hΛ)
          exact mul_le_mul_of_nonneg_right h1 (db2_eta_nonneg n _)
        · rw [db2_eta_zero n (not_lt.1 hlt)]
          simp
    _ = Λ * (db1_bump d n).rOut := by
        rw [integral_const_mul, integral_sub_left_eq_self (fun z => db2_eta (d := d) n z) volume x,
          db2_eta_integral, mul_one]

/-! ### Continuity in time of `⟨ρ_t, ψ⟩` and joint continuity -/

theorem db2_contOn_of_lip {f : ℝ → ℝ} {s : Set ℝ} {K : ℝ}
    (hL : ∀ a ∈ s, ∀ b ∈ s, |f b - f a| ≤ K * |b - a|) : ContinuousOn f s := by
  intro a ha
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  have hpos : 0 < |K| + 1 := by positivity
  refine ⟨ε / (|K| + 1), div_pos hε hpos, fun {b} hb hd => ?_⟩
  have h1 : |b - a| < ε / (|K| + 1) := by rw [Real.dist_eq] at hd; exact hd
  have h2 : |b - a| * (|K| + 1) < ε := (lt_div_iff₀ hpos).1 h1
  rw [Real.dist_eq]
  calc |f b - f a| ≤ K * |b - a| := hL a ha b hb
    _ ≤ |K| * |b - a| := mul_le_mul_of_nonneg_right (le_abs_self K) (abs_nonneg _)
    _ ≤ (|K| + 1) * |b - a| := mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg _)
    _ < ε := by linarith

theorem db2_pair_lip_le {s Λ T ΛV G₀ : ℝ} {D : WholeDyn d} {ρ : ℝ → Euc d → ℝ} (h : MFData s Λ T ΛV G₀ D ρ)
    {ψ : Euc d → ℝ} {K : ℝ} (hK : ∀ r ∈ Set.Icc (0 : ℝ) T, |mfGen D ψ (ρ r)| ≤ K)
    (hw : ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ T →
      Whole.pair (Whole.withDensityReal (ρ b)) ψ - Whole.pair (Whole.withDensityReal (ρ a)) ψ
        = ∫ r in a..b, mfGen D ψ (ρ r))
    {a b : ℝ} (ha : a ∈ Set.Icc (0 : ℝ) T) (hb : b ∈ Set.Icc (0 : ℝ) T) (hab : a ≤ b) :
    |Whole.pair (Whole.withDensityReal (ρ b)) ψ - Whole.pair (Whole.withDensityReal (ρ a)) ψ|
      ≤ K * |b - a| := by
  rw [hw a b ha.1 hab hb.2, ← Real.norm_eq_abs]
  refine intervalIntegral.norm_integral_le_of_norm_le_const (fun r hr => ?_)
  rw [Set.uIoc_of_le hab] at hr
  rw [Real.norm_eq_abs]
  exact hK r ⟨ha.1.trans hr.1.le, hr.2.trans hb.2⟩

theorem db2_pair_lip {s Λ T ΛV G₀ : ℝ} {D : WholeDyn d} {ρ : ℝ → Euc d → ℝ} (h : MFData s Λ T ΛV G₀ D ρ)
    {ψ : Euc d → ℝ} (hψ : MemCb 2 ψ) :
    ∃ K : ℝ, ∀ a ∈ Set.Icc (0 : ℝ) T, ∀ b ∈ Set.Icc (0 : ℝ) T,
      |Whole.pair (Whole.withDensityReal (ρ b)) ψ - Whole.pair (Whole.withDensityReal (ρ a)) ψ|
        ≤ K * |b - a| := by
  obtain ⟨-, ⟨K, hK⟩, hw⟩ := mf_weak_integrable_proof h hψ
  refine ⟨K, fun a ha b hb => ?_⟩
  rcases le_total a b with hab | hab
  · exact db2_pair_lip_le h hK hw ha hb hab
  · have := db2_pair_lip_le h hK hw hb ha hab
    rw [abs_sub_comm, abs_sub_comm b a]
    exact this

theorem db2_pair_contOn {s Λ T ΛV G₀ : ℝ} {D : WholeDyn d} {ρ : ℝ → Euc d → ℝ} (h : MFData s Λ T ΛV G₀ D ρ)
    {ψ : Euc d → ℝ} (hψ : MemCb 2 ψ) :
    ContinuousOn (fun r => Whole.pair (Whole.withDensityReal (ρ r)) ψ) (Set.Icc (0 : ℝ) T) := by
  obtain ⟨K, hK⟩ := db2_pair_lip h hψ
  exact db2_contOn_of_lip (fun a ha b hb => hK a ha b hb)

/-- Uniform approximation of `r ↦ ρ_r(x)` on `[0,T]` by the continuous functions `r ↦ ⟨ρ_r, η_n(x-·)⟩`. -/
theorem db2_pair_unif {s Λ T ΛV G₀ : ℝ} {D : WholeDyn d} {ρ : ℝ → Euc d → ℝ} (h : MFData s Λ T ΛV G₀ D ρ)
    (x : Euc d) :
    TendstoUniformlyOn (fun (n : ℕ) (t : ℝ) => Whole.pair (Whole.withDensityReal (ρ t))
      (fun y => db2_eta (d := d) n (x - y))) (fun t => ρ t x) atTop (Set.Icc (0 : ℝ) T) := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hlim : Tendsto (fun n : ℕ => Λ * (db1_bump d n).rOut) atTop (𝓝 0) := by
    simpa using (db1_bump_tendsto (d := d)).const_mul Λ
  filter_upwards [(tendsto_order.1 hlim).2 ε hε] with n hn t ht
  rw [dist_comm, Real.dist_eq]
  exact (db2_pair_approx h ht x n).trans_lt hn

/-- Part (i) of `mf_continuity`: `r ↦ ρ_r(x)` is continuous on `[0,T]`. -/
theorem db2_rho_contOn {s Λ T ΛV G₀ : ℝ} {D : WholeDyn d} {ρ : ℝ → Euc d → ℝ} (h : MFData s Λ T ΛV G₀ D ρ)
    (x : Euc d) : ContinuousOn (fun r => ρ r x) (Set.Icc (0 : ℝ) T) := by
  refine (db2_pair_unif h x).continuousOn (Filter.Eventually.frequently (Filter.Eventually.of_forall fun n => ?_))
  exact db2_pair_contOn h (db1_test_memCb n x)

theorem db2_slice_cont {φ : ℝ → Euc d → ℝ} {t : ℝ}
    (hφc : ContinuousOn (Function.uncurry φ) (Set.Icc (0 : ℝ) t ×ˢ Set.univ))
    {u : ℝ} (hu : u ∈ Set.Icc (0 : ℝ) t) : Continuous (φ u) := by
  have h2 : ContinuousOn (fun x : Euc d => Function.uncurry φ (u, x)) Set.univ :=
    hφc.comp (continuousOn_const.prodMk continuousOn_id) (fun x _ => ⟨hu, Set.mem_univ _⟩)
  exact continuousOn_univ.1 h2

/-- Part (ii) of `mf_continuity`: `(u,r) ↦ ⟨ρ_r, φ_u⟩` is jointly continuous on `[0,t]²`. -/
theorem db2_pair_joint {s Λ T ΛV G₀ : ℝ} {D : WholeDyn d} {ρ : ℝ → Euc d → ℝ} (h : MFData s Λ T ΛV G₀ D ρ)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) (φ : ℝ → Euc d → ℝ)
    (hφc : ContinuousOn (Function.uncurry φ) (Set.Icc (0 : ℝ) t ×ˢ Set.univ))
    (hφg : ∃ K : ℝ, ∀ u ∈ Set.Icc (0 : ℝ) t, ∀ x, |φ u x| ≤ K * (1 + ‖x‖)) :
    ContinuousOn (fun p : ℝ × ℝ => Whole.pair (Whole.withDensityReal (ρ p.2)) (φ p.1))
      (Set.Icc (0 : ℝ) t ×ˢ Set.Icc (0 : ℝ) t) := by
  obtain ⟨K, hK⟩ := hφg
  have hsub : Set.Icc (0 : ℝ) t ⊆ Set.Icc (0 : ℝ) T := fun r hr => ⟨hr.1, hr.2.trans ht.2⟩
  have hΛ := db1_Lambda_nonneg h (le_trans ht.1 ht.2)
  intro p0 hp0
  have hmain : ContinuousWithinAt (fun p : ℝ × ℝ => ∫ x, ρ p.2 x * φ p.1 x)
      (Set.Icc (0 : ℝ) t ×ˢ Set.Icc (0 : ℝ) t) p0 := by
    refine tendsto_integral_filter_of_dominated_convergence
      (fun x : Euc d => (Λ * K) * (jbracket x ^ (-((d : ℝ) + 3)) * (1 + ‖x‖))) ?_ ?_
      (db2_m_integrable.const_mul _) ?_
    · refine Filter.eventually_of_mem self_mem_nhdsWithin fun p hp => ?_
      exact ((db1_cont h (hsub hp.2)).measurable.mul
        (db2_slice_cont hφc hp.1).measurable).aestronglyMeasurable
    · refine Filter.eventually_of_mem self_mem_nhdsWithin fun p hp => ?_
      refine Filter.Eventually.of_forall fun x => ?_
      have hr := db2_rho_bound h (hsub hp.2) x
      have hρ0 : 0 ≤ ρ p.2 x := (h.hρ.density p.2 (hsub hp.2)).nonneg x
      have hm0 : 0 ≤ jbracket x ^ (-((d : ℝ) + 3)) := Real.rpow_nonneg (db2_jb_pos x).le _
      have hφb := hK p.1 hp.1 x
      rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg hρ0]
      calc ρ p.2 x * |φ p.1 x| ≤ (Λ * jbracket x ^ (-((d : ℝ) + 3))) * (K * (1 + ‖x‖)) :=
            mul_le_mul hr hφb (abs_nonneg _) (mul_nonneg hΛ hm0)
        _ = (Λ * K) * (jbracket x ^ (-((d : ℝ) + 3)) * (1 + ‖x‖)) := by ring
    · refine Filter.Eventually.of_forall fun x => ?_
      have h1 : ContinuousWithinAt (fun p : ℝ × ℝ => ρ p.2 x)
          (Set.Icc (0 : ℝ) t ×ˢ Set.Icc (0 : ℝ) t) p0 :=
        (db2_rho_contOn h x p0.2 (hsub hp0.2)).comp continuousWithinAt_snd
          (fun p hp => hsub hp.2)
      have hc : Continuous (fun p : ℝ × ℝ => (p.1, x)) := continuous_fst.prodMk continuous_const
      have hg : ContinuousWithinAt (Function.uncurry φ) (Set.Icc (0 : ℝ) t ×ˢ Set.univ) (p0.1, x) :=
        hφc _ ⟨hp0.1, Set.mem_univ _⟩
      have h2 : ContinuousWithinAt (fun p : ℝ × ℝ => φ p.1 x)
          (Set.Icc (0 : ℝ) t ×ˢ Set.Icc (0 : ℝ) t) p0 :=
        hg.comp (f := fun p : ℝ × ℝ => (p.1, x)) (x := p0) hc.continuousWithinAt
          (fun p (hp : p ∈ Set.Icc (0 : ℝ) t ×ˢ Set.Icc (0 : ℝ) t) => ⟨hp.1, Set.mem_univ _⟩)
      exact h1.mul h2
  refine ContinuousWithinAt.congr hmain (fun p hp => ?_) ?_
  · rw [Q09A.pair_withDensityReal (h.hρ.density p.2 (hsub hp.2))]
  · rw [Q09A.pair_withDensityReal (h.hρ.density p0.2 (hsub hp0.2))]

/-! ### Uniform bounds for the test functions `f_r`, `r ∈ [0,t]` -/

theorem db2_hs0 {s Λ T ΛV G₀ : ℝ} {D : WholeDyn d} {ρ : ℝ → Euc d → ℝ} (h : MFData s Λ T ΛV G₀ D ρ) :
    0 ≤ D.s := by
  rw [h.hs]; exact h.hs0

theorem db2_hsd {s Λ T ΛV G₀ : ℝ} {D : WholeDyn d} {ρ : ℝ → Euc d → ℝ} (h : MFData s Λ T ΛV G₀ D ρ) :
    D.s < d := by
  rw [h.hs]; exact h.hsd

theorem db2_matVec_le (M : Matrix (Fin d) (Fin d) ℝ) (v : Euc d) :
    ‖Torus.matVec M v‖ ≤ ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin M)‖ * ‖v‖ :=
  (LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin M)).le_opNorm v

theorem db2_grad_le {F : Euc d → ℝ} {A : ℝ} (hA : ∀ z, ‖iteratedFDeriv ℝ 1 F z‖ ≤ A) (z : Euc d) :
    ‖gradient F z‖ ≤ A := by
  rw [db1_grad_norm_eq, ← norm_iteratedFDeriv_one]
  exact hA z

theorem db2_grad_lip_of {F : Euc d → ℝ} (hF : ContDiff ℝ 2 F) {L : ℝ}
    (hL : ∀ z, ‖iteratedFDeriv ℝ 2 F z‖ ≤ L) (x y : Euc d) :
    ‖gradient F x - gradient F y‖ ≤ L * ‖x - y‖ := by
  have hb : ∀ z ∈ (Set.univ : Set (Euc d)), ‖fderiv ℝ (gradient F) z‖ ≤ L := by
    intro z _
    refine (db1_fderiv_gradient_le hF z).trans ?_
    have h1 := norm_iteratedFDeriv_fderiv (𝕜 := ℝ) (f := F) (x := z) (n := 1)
    have h2 := norm_iteratedFDeriv_one (𝕜 := ℝ) (x := z) (fderiv ℝ F)
    rw [← h2, h1]
    exact hL z
  have h := Convex.norm_image_sub_le_of_norm_fderiv_le
    (fun z _ => db1_gradient_differentiable hF z) hb convex_univ (Set.mem_univ x) (Set.mem_univ y)
  rw [norm_sub_rev (gradient F x), norm_sub_rev x y]
  exact h

theorem db2_lap_le {F : Euc d → ℝ} {B : ℝ} (hB : ∀ z, ‖iteratedFDeriv ℝ 2 F z‖ ≤ B) (z : Euc d) :
    |Laplacian.laplacian F z| ≤ (Module.finrank ℝ (Euc d) : ℝ) * B := by
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_stdOrthonormalBasis]
  have key : ∀ i, ‖iteratedFDeriv ℝ 2 F z
      ![(stdOrthonormalBasis ℝ (Euc d)) i, (stdOrthonormalBasis ℝ (Euc d)) i]‖ ≤ B := by
    intro i
    refine (ContinuousMultilinearMap.le_opNorm _ _).trans ?_
    have hb : ∏ j : Fin 2, ‖(![(stdOrthonormalBasis ℝ (Euc d)) i,
        (stdOrthonormalBasis ℝ (Euc d)) i] : Fin 2 → Euc d) j‖ = 1 := by
      simp [Fin.prod_univ_two, OrthonormalBasis.norm_eq_one]
    rw [hb, mul_one]
    exact hB z
  calc |∑ i, iteratedFDeriv ℝ 2 F z
        ![(stdOrthonormalBasis ℝ (Euc d)) i, (stdOrthonormalBasis ℝ (Euc d)) i]|
      = ‖∑ i, iteratedFDeriv ℝ 2 F z
        ![(stdOrthonormalBasis ℝ (Euc d)) i, (stdOrthonormalBasis ℝ (Euc d)) i]‖ :=
        (Real.norm_eq_abs _).symm
    _ ≤ ∑ i, ‖iteratedFDeriv ℝ 2 F z
        ![(stdOrthonormalBasis ℝ (Euc d)) i, (stdOrthonormalBasis ℝ (Euc d)) i]‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin (Module.finrank ℝ (Euc d)), B := Finset.sum_le_sum fun i _ => key i
    _ = (Module.finrank ℝ (Euc d) : ℝ) * B := by
        simp [Finset.sum_const, nsmul_eq_mul]

/-- The kernel bound with explicit constants: `|pairKernelRd D F x y| ≤ CM |σ| (L + 2A) (|x-y|^{-s} 1_{|x-y|<1} + 1)`. -/
theorem db2_pK_core {D : WholeDyn d} (hs0 : 0 ≤ D.s) {F : Euc d → ℝ} {A L CM : ℝ}
    (hCM0 : 0 ≤ CM) (hCM : ∀ v : Euc d, ‖Torus.matVec D.M v‖ ≤ CM * ‖v‖)
    (hA0 : 0 ≤ A) (hL0 : 0 ≤ L) (hA : ∀ z, ‖gradient F z‖ ≤ A)
    (hL : ∀ x y : Euc d, ‖gradient F x - gradient F y‖ ≤ L * ‖x - y‖) (x y : Euc d) :
    |pairKernelRd D F x y| ≤ (CM * |movtr_sigma D.s| * (L + 2 * A)) * (db1G D.s (x - y) + 1) := by
  unfold pairKernelRd
  split_ifs with hxy
  · rw [abs_zero]
    have : 0 ≤ db1G D.s (x - y) + 1 := by linarith [db1G_nonneg D.s (x - y)]
    exact mul_nonneg (by positivity) this
  · have hz : x - y ≠ 0 := sub_ne_zero.mpr hxy
    have hzpos : 0 < ‖x - y‖ := norm_pos_iff.mpr hz
    have hk : ‖rieszKernelGrad d D.s (x - y)‖ = |movtr_sigma D.s| * ‖x - y‖ ^ (-D.s - 1) := by
      rw [movtr_rieszKernelGrad_norm D.s hs0 hz]
      have hr : 0 ≤ ‖x - y‖ ^ (-D.s - 1) := Real.rpow_nonneg (norm_nonneg _) _
      have h1 : |movtr_sigma D.s * ‖x - y‖ ^ (-D.s - 1)| = movtr_sigma D.s * ‖x - y‖ ^ (-D.s - 1) := by
        rw [← movtr_rieszKernelGrad_norm D.s hs0 hz]
        exact abs_of_nonneg (norm_nonneg _)
      rw [abs_mul, abs_of_nonneg hr] at h1
      exact h1.symm
    have hinner : |inner ℝ (gradient F x - gradient F y) (Torus.matVec D.M (rieszKernelGrad d D.s (x - y)))|
        ≤ ‖gradient F x - gradient F y‖ * (CM * (|movtr_sigma D.s| * ‖x - y‖ ^ (-D.s - 1))) := by
      refine (abs_real_inner_le_norm _ _).trans ?_
      refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
      rw [← hk]
      exact hCM _
    have hdiff : ‖gradient F x - gradient F y‖ ≤ L * ‖x - y‖ := hL x y
    have hdiff2 : ‖gradient F x - gradient F y‖ ≤ 2 * A := by
      refine (norm_sub_le _ _).trans ?_
      linarith [hA x, hA y]
    have hC0 : 0 ≤ CM * |movtr_sigma D.s| := by positivity
    by_cases h1 : ‖x - y‖ < 1
    · have hind : db1G D.s (x - y) = ‖x - y‖ ^ (-D.s) := by
        unfold db1G
        rw [Set.indicator_of_mem (by simpa using h1)]
      have hpow : ‖x - y‖ * ‖x - y‖ ^ (-D.s - 1) = ‖x - y‖ ^ (-D.s) := by
        rw [mul_comm, ← Real.rpow_add_one hzpos.ne']
        congr 1
        ring
      have hg : 0 ≤ ‖x - y‖ ^ (-D.s) := Real.rpow_nonneg (norm_nonneg _) _
      calc |inner ℝ (gradient F x - gradient F y) (Torus.matVec D.M (rieszKernelGrad d D.s (x - y)))|
          ≤ ‖gradient F x - gradient F y‖ * (CM * (|movtr_sigma D.s| * ‖x - y‖ ^ (-D.s - 1))) := hinner
        _ ≤ (L * ‖x - y‖) * (CM * (|movtr_sigma D.s| * ‖x - y‖ ^ (-D.s - 1))) :=
            mul_le_mul_of_nonneg_right hdiff (by positivity)
        _ = (CM * |movtr_sigma D.s| * L) * (‖x - y‖ ^ (-D.s)) := by rw [← hpow]; ring
        _ ≤ (CM * |movtr_sigma D.s| * (L + 2 * A)) * (db1G D.s (x - y) + 1) := by
            rw [hind]
            have hLA : L ≤ L + 2 * A := by linarith
            have hX : 0 ≤ CM * |movtr_sigma D.s| * ‖x - y‖ ^ (-D.s) := by positivity
            nlinarith [mul_le_mul_of_nonneg_right hLA hg, mul_nonneg hC0 hg]
    · have hind : db1G D.s (x - y) = 0 := by
        unfold db1G
        rw [Set.indicator_of_notMem (by simpa using h1)]
      have hr1 : ‖x - y‖ ^ (-D.s - 1) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos (not_lt.1 h1) (by linarith)
      calc |inner ℝ (gradient F x - gradient F y) (Torus.matVec D.M (rieszKernelGrad d D.s (x - y)))|
          ≤ ‖gradient F x - gradient F y‖ * (CM * (|movtr_sigma D.s| * ‖x - y‖ ^ (-D.s - 1))) := hinner
        _ ≤ (2 * A) * (CM * (|movtr_sigma D.s| * ‖x - y‖ ^ (-D.s - 1))) :=
            mul_le_mul_of_nonneg_right hdiff2 (by positivity)
        _ ≤ (2 * A) * (CM * (|movtr_sigma D.s| * 1)) := by
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hr1 (abs_nonneg _)) (by positivity)
        _ = (CM * |movtr_sigma D.s| * (2 * A)) * (db1G D.s (x - y) + 1) := by rw [hind]; ring
        _ ≤ (CM * |movtr_sigma D.s| * (L + 2 * A)) * (db1G D.s (x - y) + 1) := by
            rw [hind]
            have : CM * |movtr_sigma D.s| * (2 * A) ≤ CM * |movtr_sigma D.s| * (L + 2 * A) :=
              mul_le_mul_of_nonneg_left (by linarith) hC0
            linarith

/-- Uniform kernel bound over the family `r ↦ f_r`, `r ∈ [0,t]`. -/
theorem db2_pK_unif {s Λ T ΛV G₀ : ℝ} {D : WholeDyn d} {ρ : ℝ → Euc d → ℝ} (h : MFData s Λ T ΛV G₀ D ρ)
    {t : ℝ} {f ft : ℝ → Euc d → ℝ} (hf : IsC12TestRd t f ft) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r ∈ Set.Icc (0 : ℝ) t, ∀ x y : Euc d,
      |pairKernelRd D (f r) x y| ≤ C * (db1G D.s (x - y) + 1) := by
  obtain ⟨B1, hB1⟩ := hf.bdd 1 (by norm_num)
  obtain ⟨B2, hB2⟩ := hf.bdd 2 le_rfl
  refine ⟨(‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin D.M)‖ * |movtr_sigma D.s|
      * (max B2 0 + 2 * max B1 0)), by positivity, fun r hr x y => ?_⟩
  exact db2_pK_core (db2_hs0 h) (norm_nonneg _) (db2_matVec_le D.M) (le_max_right _ _) (le_max_right _ _)
    (fun z => db2_grad_le (fun z => (hB1 r hr z).trans (le_max_left _ _)) z)
    (fun x y => db2_grad_lip_of (hf.c2 r hr) (fun z => (hB2 r hr z).trans (le_max_left _ _)) x y) x y

theorem db2_lap_unif {t : ℝ} {f ft : ℝ → Euc d → ℝ} (hf : IsC12TestRd t f ft) :
    ∃ C : ℝ, ∀ r ∈ Set.Icc (0 : ℝ) t, ∀ z : Euc d, |Laplacian.laplacian (f r) z| ≤ C := by
  obtain ⟨B2, hB2⟩ := hf.bdd 2 le_rfl
  exact ⟨(Module.finrank ℝ (Euc d) : ℝ) * B2, fun r hr z => db2_lap_le (fun z => hB2 r hr z) z⟩

theorem db2_grad_unif {t : ℝ} {f ft : ℝ → Euc d → ℝ} (hf : IsC12TestRd t f ft) :
    ∃ A : ℝ, ∀ r ∈ Set.Icc (0 : ℝ) t, ∀ z : Euc d, ‖gradient (f r) z‖ ≤ A := by
  obtain ⟨B1, hB1⟩ := hf.bdd 1 (by norm_num)
  exact ⟨B1, fun r hr z => db2_grad_le (fun z => hB1 r hr z) z⟩

/-! ### Joint continuity of `∇f`, `Δf` in `(r,x)` -/

theorem db2_contOn_subtype {t : ℝ} {X : Type*} [TopologicalSpace X] {G : ℝ → Euc d → X}
    (hG : Continuous fun q : Set.Icc (0 : ℝ) t × Euc d => G q.1.1 q.2) :
    ContinuousOn (fun p : ℝ × Euc d => G p.1 p.2) (Set.Icc (0 : ℝ) t ×ˢ Set.univ) := by
  rw [continuousOn_iff_continuous_restrict]
  have c1 : Continuous (fun q : ↥(Set.Icc (0 : ℝ) t ×ˢ (Set.univ : Set (Euc d))) => q.1.1) :=
    continuous_fst.comp continuous_subtype_val
  have c2 : Continuous (fun q : ↥(Set.Icc (0 : ℝ) t ×ˢ (Set.univ : Set (Euc d))) => q.1.2) :=
    continuous_snd.comp continuous_subtype_val
  have hmap : Continuous (fun q : ↥(Set.Icc (0 : ℝ) t ×ˢ (Set.univ : Set (Euc d))) =>
      ((⟨q.1.1, q.2.1⟩ : Set.Icc (0 : ℝ) t), q.1.2)) :=
    (Continuous.subtype_mk c1 (fun q => q.2.1)).prodMk c2
  exact hG.comp hmap

theorem db2_fderiv_eq (g : Euc d → ℝ) (z : Euc d) :
    fderiv ℝ g z = continuousMultilinearCurryFin1 ℝ (Euc d) ℝ (iteratedFDeriv ℝ 1 g z) := by
  ext v
  rw [continuousMultilinearCurryFin1_apply, iteratedFDeriv_one_apply]
  congr 1

theorem db2_grad_eq (g : Euc d → ℝ) (z : Euc d) :
    gradient g z = (InnerProductSpace.toDual ℝ (Euc d)).symm
      (continuousMultilinearCurryFin1 ℝ (Euc d) ℝ (iteratedFDeriv ℝ 1 g z)) := by
  unfold gradient
  rw [db2_fderiv_eq]

theorem db2_grad_joint {t : ℝ} {f ft : ℝ → Euc d → ℝ} (hf : IsC12TestRd t f ft) :
    ContinuousOn (fun p : ℝ × Euc d => gradient (f p.1) p.2) (Set.Icc (0 : ℝ) t ×ˢ Set.univ) := by
  apply db2_contOn_subtype (G := fun r x => gradient (f r) x)
  have hΨ : Continuous (fun T : ContinuousMultilinearMap ℝ (fun _ : Fin 1 => Euc d) ℝ =>
      (InnerProductSpace.toDual ℝ (Euc d)).symm (continuousMultilinearCurryFin1 ℝ (Euc d) ℝ T)) :=
    (InnerProductSpace.toDual ℝ (Euc d)).symm.continuous.comp
      (continuousMultilinearCurryFin1 ℝ (Euc d) ℝ).continuous
  exact (hΨ.comp (hf.cont_c2 1 (by norm_num))).congr (fun q => (db2_grad_eq (f q.1.1) q.2).symm)

theorem db2_lap_joint {t : ℝ} {f ft : ℝ → Euc d → ℝ} (hf : IsC12TestRd t f ft) :
    ContinuousOn (fun p : ℝ × Euc d => Laplacian.laplacian (f p.1) p.2) (Set.Icc (0 : ℝ) t ×ˢ Set.univ) := by
  apply db2_contOn_subtype (G := fun r x => Laplacian.laplacian (f r) x)
  have e : ∀ (g : Euc d → ℝ) (z : Euc d), Laplacian.laplacian g z = ∑ i, iteratedFDeriv ℝ 2 g z
      ![(stdOrthonormalBasis ℝ (Euc d)) i, (stdOrthonormalBasis ℝ (Euc d)) i] := fun g z => by
    rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_stdOrthonormalBasis]
  show Continuous (fun q : Set.Icc (0 : ℝ) t × Euc d => Laplacian.laplacian (f q.1.1) q.2)
  simp only [e]
  exact continuous_finsetSum _ fun i _ =>
    ((ContinuousMultilinearMap.apply ℝ (fun _ : Fin 2 => Euc d) ℝ
      ![(stdOrthonormalBasis ℝ (Euc d)) i, (stdOrthonormalBasis ℝ (Euc d)) i]).continuous).comp
      (hf.cont_c2 2 le_rfl)

/-- The kernel `pairKernelRd D (f_r) x y` is continuous in `(r,r')` on `[0,t]²` for fixed `x,y`. -/
theorem db2_pK_contOn {D : WholeDyn d} {t : ℝ} {f ft : ℝ → Euc d → ℝ} (hf : IsC12TestRd t f ft) (x y : Euc d) :
    ContinuousOn (fun p : ℝ × ℝ => pairKernelRd D (f p.1) x y)
      (Set.Icc (0 : ℝ) t ×ˢ Set.Icc (0 : ℝ) t) := by
  by_cases hxy : x = y
  · have e : (fun p : ℝ × ℝ => pairKernelRd D (f p.1) x y) = fun _ => 0 := by
      funext p
      simp [pairKernelRd, hxy]
    rw [e]
    exact continuousOn_const
  · have e : (fun p : ℝ × ℝ => pairKernelRd D (f p.1) x y) = fun p =>
        inner ℝ (gradient (f p.1) x - gradient (f p.1) y)
          (Torus.matVec D.M (rieszKernelGrad d D.s (x - y))) := by
      funext p
      unfold pairKernelRd
      rw [if_neg hxy]
    rw [e]
    have hg : ∀ z : Euc d, ContinuousOn (fun p : ℝ × ℝ => gradient (f p.1) z)
        (Set.Icc (0 : ℝ) t ×ˢ Set.Icc (0 : ℝ) t) := by
      intro z
      have hc : ContinuousOn (fun p : ℝ × ℝ => (p.1, z)) (Set.Icc (0 : ℝ) t ×ˢ Set.Icc (0 : ℝ) t) :=
        (continuous_fst.prodMk continuous_const).continuousOn
      exact (db2_grad_joint hf).comp hc (fun p hp => ⟨hp.1, Set.mem_univ _⟩)
    exact ((hg x).sub (hg y)).inner continuousOn_const

/-! ### The interaction term `B_{f_r}(ρ_σ, ρ_σ)` -/

/-- The integrand bound: `|ρ_σ(y) pairKernelRd D f_r x y| ≤ C Λ (|x-y|^{-s} 1_{|x-y|<1} + ⟨y⟩^{-(d+3)})`. -/
theorem db2_integrand_le {s Λ T ΛV G₀ : ℝ} {D : WholeDyn d} {ρ : ℝ → Euc d → ℝ} (h : MFData s Λ T ΛV G₀ D ρ)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) {f ft : ℝ → Euc d → ℝ} (hf : IsC12TestRd t f ft)
    {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ r ∈ Set.Icc (0 : ℝ) t, ∀ x y : Euc d, |pairKernelRd D (f r) x y| ≤ C * (db1G D.s (x - y) + 1))
    {r σ' : ℝ} (hr : r ∈ Set.Icc (0 : ℝ) t) (hσ : σ' ∈ Set.Icc (0 : ℝ) t) (x y : Euc d) :
    ‖ρ σ' y * pairKernelRd D (f r) x y‖
      ≤ C * Λ * (db1G (d := d) D.s (x - y) + jbracket y ^ (-((d : ℝ) + 3))) := by
  have hsub : Set.Icc (0 : ℝ) t ⊆ Set.Icc (0 : ℝ) T := fun u hu => ⟨hu.1, hu.2.trans ht.2⟩
  have hr0 : 0 ≤ ρ σ' y := (h.hρ.density σ' (hsub hσ)).nonneg y
  have hrΛ := db1_sup h (hsub hσ) y
  have hrm := db2_rho_bound h (hsub hσ) y
  have hK := hC r hr x y
  have hGy : 0 ≤ db1G (d := d) D.s (x - y) := db1G_nonneg _ _
  rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg hr0]
  calc ρ σ' y * |pairKernelRd D (f r) x y| ≤ ρ σ' y * (C * (db1G (d := d) D.s (x - y) + 1)) :=
        mul_le_mul_of_nonneg_left hK hr0
    _ = C * (ρ σ' y * db1G (d := d) D.s (x - y)) + C * ρ σ' y := by ring
    _ ≤ C * (Λ * db1G (d := d) D.s (x - y)) + C * (Λ * jbracket y ^ (-((d : ℝ) + 3))) :=
        add_le_add (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hrΛ hGy) hC0)
          (mul_le_mul_of_nonneg_left hrm hC0)
    _ = C * Λ * (db1G (d := d) D.s (x - y) + jbracket y ^ (-((d : ℝ) + 3))) := by ring

theorem db2_J_bound {s Λ T ΛV G₀ : ℝ} {D : WholeDyn d} {ρ : ℝ → Euc d → ℝ} (h : MFData s Λ T ΛV G₀ D ρ)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) {f ft : ℝ → Euc d → ℝ} (hf : IsC12TestRd t f ft)
    {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ r ∈ Set.Icc (0 : ℝ) t, ∀ x y : Euc d, |pairKernelRd D (f r) x y| ≤ C * (db1G D.s (x - y) + 1))
    {r σ' : ℝ} (hr : r ∈ Set.Icc (0 : ℝ) t) (hσ : σ' ∈ Set.Icc (0 : ℝ) t) (x : Euc d) :
    |∫ y, ρ σ' y * pairKernelRd D (f r) x y|
      ≤ C * Λ * ((∫ z, db1G (d := d) D.s z) + ∫ y : Euc d, jbracket y ^ (-((d : ℝ) + 3))) := by
  have hd : 1 ≤ d := h.one_le_d
  have hsd : D.s < d := db2_hsd h
  have hGi := db1G_integrable (d := d) hd hsd
  have hmaj : Integrable (fun y => C * Λ * (db1G (d := d) D.s (x - y) + jbracket y ^ (-((d : ℝ) + 3)))) :=
    ((hGi.comp_sub_left x).add db2_m_integrable').const_mul _
  have hbound := norm_integral_le_of_norm_le hmaj
    (Filter.Eventually.of_forall fun y => db2_integrand_le h ht hf hC0 hC hr hσ x y)
  rw [← Real.norm_eq_abs]
  refine hbound.trans (le_of_eq ?_)
  rw [integral_const_mul, integral_add (hGi.comp_sub_left x) db2_m_integrable',
    integral_sub_left_eq_self (db1G (d := d) D.s) volume x]

/-- Stage A: for fixed `x`, `(r,σ) ↦ ∫ ρ_σ(y) k_{f_r}(x,y) dy` is continuous on `[0,t]²` (dominated convergence in `y`). -/
theorem db2_J_contOn {s Λ T ΛV G₀ : ℝ} {D : WholeDyn d} {ρ : ℝ → Euc d → ℝ} (h : MFData s Λ T ΛV G₀ D ρ)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) {f ft : ℝ → Euc d → ℝ} (hf : IsC12TestRd t f ft) (x : Euc d) :
    ContinuousOn (fun p : ℝ × ℝ => ∫ y, ρ p.2 y * pairKernelRd D (f p.1) x y)
      (Set.Icc (0 : ℝ) t ×ˢ Set.Icc (0 : ℝ) t) := by
  obtain ⟨C, hC0, hC⟩ := db2_pK_unif h hf
  have hsub : Set.Icc (0 : ℝ) t ⊆ Set.Icc (0 : ℝ) T := fun r hr => ⟨hr.1, hr.2.trans ht.2⟩
  have hd : 1 ≤ d := h.one_le_d
  have hsd : D.s < d := db2_hsd h
  have hGi := db1G_integrable (d := d) hd hsd
  have hmaj : Integrable (fun y : Euc d =>
      C * Λ * (db1G (d := d) D.s (x - y) + jbracket y ^ (-((d : ℝ) + 3)))) :=
    ((hGi.comp_sub_left x).add db2_m_integrable').const_mul _
  intro p0 hp0
  have key : Filter.Tendsto (fun p : ℝ × ℝ => ∫ y, ρ p.2 y * pairKernelRd D (f p.1) x y)
      (𝓝[Set.Icc (0 : ℝ) t ×ˢ Set.Icc (0 : ℝ) t] p0)
      (𝓝 (∫ y, ρ p0.2 y * pairKernelRd D (f p0.1) x y)) := by
    refine tendsto_integral_filter_of_dominated_convergence
      (fun y : Euc d => C * Λ * (db1G (d := d) D.s (x - y) + jbracket y ^ (-((d : ℝ) + 3)))) ?_ ?_ hmaj ?_
    · refine Filter.eventually_of_mem self_mem_nhdsWithin fun p hp => ?_
      have hpk : Measurable (fun y : Euc d => pairKernelRd D (f p.1) x y) :=
        (db1_pK_measurable (hf.c2 p.1 hp.1)).comp (measurable_const.prodMk measurable_id)
      exact ((db1_cont h (hsub hp.2)).measurable.mul hpk).aestronglyMeasurable
    · refine Filter.eventually_of_mem self_mem_nhdsWithin fun p hp => Filter.Eventually.of_forall fun y => ?_
      exact db2_integrand_le h ht hf hC0 hC hp.1 hp.2 x y
    · refine Filter.Eventually.of_forall fun y => ?_
      have hρy : ContinuousWithinAt (fun p : ℝ × ℝ => ρ p.2 y)
          (Set.Icc (0 : ℝ) t ×ˢ Set.Icc (0 : ℝ) t) p0 :=
        (db2_rho_contOn h y p0.2 (hsub hp0.2)).comp continuousWithinAt_snd (fun p hp => hsub hp.2)
      exact hρy.mul (db2_pK_contOn hf x y p0 hp0)
  exact key

/-- Part (iii) core: the interaction term `(t,r) ↦ ∬ ρ_r(x) ρ_r(y) k_{f_t}(x,y)` is continuous on `[0,t]²`. -/
theorem db2_H_contOn {s Λ T ΛV G₀ : ℝ} {D : WholeDyn d} {ρ : ℝ → Euc d → ℝ} (h : MFData s Λ T ΛV G₀ D ρ)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) {f ft : ℝ → Euc d → ℝ} (hf : IsC12TestRd t f ft) :
    ContinuousOn (fun p : ℝ × ℝ => ∫ x, ρ p.2 x * ∫ y, ρ p.2 y * pairKernelRd D (f p.1) x y)
      (Set.Icc (0 : ℝ) t ×ˢ Set.Icc (0 : ℝ) t) := by
  obtain ⟨C, hC0, hC⟩ := db2_pK_unif h hf
  have hsub : Set.Icc (0 : ℝ) t ⊆ Set.Icc (0 : ℝ) T := fun r hr => ⟨hr.1, hr.2.trans ht.2⟩
  have hΛ := db1_Lambda_nonneg h (le_trans ht.1 ht.2)
  have hI1 : 0 ≤ ∫ z, db1G (d := d) D.s z := integral_nonneg fun z => db1G_nonneg _ _
  have hI2 : 0 ≤ ∫ y : Euc d, jbracket y ^ (-((d : ℝ) + 3)) :=
    integral_nonneg fun y => Real.rpow_nonneg (db2_jb_pos y).le _
  obtain ⟨CJ, hCJ0, hJb⟩ : ∃ CJ : ℝ, 0 ≤ CJ ∧ ∀ p ∈ Set.Icc (0 : ℝ) t ×ˢ Set.Icc (0 : ℝ) t, ∀ x : Euc d,
      |∫ y, ρ p.2 y * pairKernelRd D (f p.1) x y| ≤ CJ :=
    ⟨C * Λ * ((∫ z, db1G (d := d) D.s z) + ∫ y : Euc d, jbracket y ^ (-((d : ℝ) + 3))),
      mul_nonneg (mul_nonneg hC0 hΛ) (add_nonneg hI1 hI2),
      fun p hp x => db2_J_bound h ht hf hC0 hC hp.1 hp.2 x⟩
  intro p0 hp0
  have hρx : ∀ x : Euc d, ContinuousWithinAt (fun p : ℝ × ℝ => ρ p.2 x)
      (Set.Icc (0 : ℝ) t ×ˢ Set.Icc (0 : ℝ) t) p0 := fun x =>
    (db2_rho_contOn h x p0.2 (hsub hp0.2)).comp continuousWithinAt_snd (fun p hp => hsub hp.2)
  have key : Filter.Tendsto (fun p : ℝ × ℝ => ∫ x, ρ p.2 x * ∫ y, ρ p.2 y * pairKernelRd D (f p.1) x y)
      (𝓝[Set.Icc (0 : ℝ) t ×ˢ Set.Icc (0 : ℝ) t] p0)
      (𝓝 (∫ x, ρ p0.2 x * ∫ y, ρ p0.2 y * pairKernelRd D (f p0.1) x y)) := by
    refine tendsto_integral_filter_of_dominated_convergence
      (fun x : Euc d => Λ * CJ * jbracket x ^ (-((d : ℝ) + 3))) ?_ ?_ (db2_m_integrable'.const_mul _) ?_
    · refine Filter.eventually_of_mem self_mem_nhdsWithin fun p hp => ?_
      have hjm : Measurable (fun q : Euc d × Euc d => ρ p.2 q.2 * pairKernelRd D (f p.1) q.1 q.2) :=
        ((db1_cont h (hsub hp.2)).measurable.comp measurable_snd).mul (db1_pK_measurable (hf.c2 p.1 hp.1))
      have hJm : StronglyMeasurable (fun x : Euc d => ∫ y, ρ p.2 y * pairKernelRd D (f p.1) x y) :=
        hjm.stronglyMeasurable.integral_prod_right'
      exact ((db1_cont h (hsub hp.2)).measurable.mul hJm.measurable).aestronglyMeasurable
    · refine Filter.eventually_of_mem self_mem_nhdsWithin fun p hp => ?_
      refine Filter.Eventually.of_forall fun x => ?_
      have hr := db2_rho_bound h (hsub hp.2) x
      have hρ0 : 0 ≤ ρ p.2 x := (h.hρ.density p.2 (hsub hp.2)).nonneg x
      have hJb' := hJb p hp x
      have hm0 : 0 ≤ jbracket x ^ (-((d : ℝ) + 3)) := Real.rpow_nonneg (db2_jb_pos x).le _
      rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg hρ0]
      calc ρ p.2 x * |∫ y, ρ p.2 y * pairKernelRd D (f p.1) x y|
          ≤ (Λ * jbracket x ^ (-((d : ℝ) + 3))) * CJ :=
            mul_le_mul hr hJb' (abs_nonneg _) (mul_nonneg hΛ hm0)
        _ = Λ * CJ * jbracket x ^ (-((d : ℝ) + 3)) := by ring
    · refine Filter.Eventually.of_forall fun x => ?_
      exact (hρx x).mul ((db2_J_contOn h ht hf x) p0 hp0)
  exact key

end HRS.MH.DualityRd
