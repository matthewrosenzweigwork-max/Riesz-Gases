import HRS.MS.S21F_D00
import HRS.MS.Fp81S21WickMomRep6

/-! Extension of compact chart agreement to weighted tests. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 400000
noncomputable section

open Classical MeasureTheory Filter Topology
open scoped ENNReal RealInnerProductSpace
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R26T6 HRS.MS.ProClosureS111

variable {Ω : Type*} [MeasurableSpace Ω]
variable (p : Parameters) {δ : ℝ} (R : Trajectory p δ)
variable (E : r26t6_WeightedChart p.d (2 * p.d + 8) ((p.d : ℝ) + 2))
variable (P : Measure Ω) [IsProbabilityMeasure P]
local notation "μ" => HRS.Whole.withDensityReal R.ρβ
local notation "μK" => ((HRS.Whole.withDensityReal R.ρβ).prod (HRS.Whole.withDensityReal R.ρβ))
local notation "Wt" => (IsR2WeightedTest (2 * p.d + 8) ((p.d : ℝ) + 2))
local notation "k" => (fun (f : Euc p.d → ℝ) (xy : Euc p.d × Euc p.d) =>
  HRS.Whole.commutatorKernel p.d p.s (gradient f) xy.1 xy.2)

theorem fp81s21_wick_weighted_agreement
    (A : Lp ℝ 2 μK →L[ℝ] Lp ℝ 2 P)
    (q : Ω → r26t6_Coeff) (hq : MemLp q 2 P)
    (hcompact : ∀ g : Euc p.d → ℝ, IsR2Test g →
      ∀ hg : MemLp (k g) 2 μK,
        (fun ω => fp81s21_chartAction E (q ω) g) =ᵐ[P]
          (A (hg.toLp (k g)) : Ω → ℝ)) :
    ∀ f : Euc p.d → ℝ, Wt f →
      ∃ hf : MemLp (k f) 2 μK,
        (fun ω => fp81s21_chartAction E (q ω) f) =ᵐ[P]
          (A (hf.toLp (k f)) : Ω → ℝ) := by
  letI : IsProbabilityMeasure μ := HRS.Whole.Q34.isProbabilityMeasure_nu R.thermal.1.1
  have hr : (2 : ℝ) + (p.d : ℝ) / 2 < ((2 * p.d + 8 : ℕ) : ℝ) := by
    have hd : (0 : ℝ) ≤ p.d := Nat.cast_nonneg _
    push_cast
    linarith
  have hP : (p.d : ℝ) < 2 * ((p.d : ℝ) + 2) := by
    have hd : (0 : ℝ) ≤ p.d := Nat.cast_nonneg _
    linarith
  obtain ⟨B, hB, hOp⟩ := physical_weighted_L2_operators p.hd p.s p.a p.β
    ((p.d : ℝ) + 2) (2 * p.d + 8) p.hs0 p.hs p.ha p.hβ hr hP R.ρβ R.thermal
  let hk : ∀ g : Euc p.d → ℝ, Wt g → MemLp (k g) 2 μK :=
    fun g hg => (hOp g hg).2.2.1
  intro f hfW
  refine ⟨hk f hfW, ?_⟩
  let c := E.encode f
  let fn : ℕ → compactSmoothSubmodule p.d := chartSection E c
  let hnW : ∀ n, Wt (fn n) := fun n =>
    weightedTestSubmodule_iff.1 (weighted_test_of_compact_smooth hP
      (show IsR2Test (fn n : Euc p.d → ℝ) from (fn n).property))
  let kf : Lp ℝ 2 μK := (hk f hfW).toLp (k f)
  let kn : ℕ → Lp ℝ 2 μK := fun n => (hk (fn n) (hnW n)).toLp (k (fn n))
  have hkconv : Tendsto kn atTop (𝓝 kf) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    have hr0 : 0 < 2 * p.d + 8 := by omega
    have hb : ∀ n, ‖kn n - kf‖ ^ 2 ≤ B *
        (weightedSobolevE (2 * p.d + 8) ((p.d : ℝ) + 2)
          ((fn n : Euc p.d → ℝ) - f)).toReal ^ 2 := by
      intro n
      have hsub := commutator_gradient_sub p.s (fn n) f
        ((fn n).property.1.differentiable (by norm_num))
        (hfW.1.differentiable (by exact_mod_cast (Nat.ne_of_gt hr0)))
      have heq : ‖kn n - kf‖ ^ 2 = ∫ xy : Euc p.d × Euc p.d,
          (k (fn n) xy - k f xy) ^ 2 ∂μK := by
        rw [← real_inner_self_eq_norm_sq, L2.inner_def]
        apply integral_congr_ae
        filter_upwards [Lp.coeFn_sub (kn n) kf, (hk (fn n) (hnW n)).coeFn_toLp,
          (hk f hfW).coeFn_toLp] with xy h1 h2 h3
        change (kn n - kf) xy * (kn n - kf) xy = _
        rw [h1]
        simp only [Pi.sub_apply]
        change (kn n) xy = _ at h2
        change kf xy = _ at h3
        rw [h2, h3]
        ring
      rw [heq]
      have he := (hOp _ (chartSection_error_weighted E hP f hfW n)).2.2.2
      change (∫ xy : Euc p.d × Euc p.d, commutatorKernel p.d p.s
        (gradient ((fn n : Euc p.d → ℝ) - f)) xy.1 xy.2 ^ 2 ∂μK) ≤
          B * (weightedSobolevE (2 * p.d + 8) ((p.d : ℝ) + 2)
            ((fn n : Euc p.d → ℝ) - f)).toReal ^ 2 at he
      simpa only [hsub] using he
    have he := chartSection_error_tendsto E hP f hfW
    have hlim : Tendsto (fun n : ℕ => B *
        (weightedSobolevE (2 * p.d + 8) ((p.d : ℝ) + 2)
          ((fn n : Euc p.d → ℝ) - f)).toReal ^ 2) atTop (𝓝 0) := by
      simpa [fn, c] using (he.pow 2).const_mul B
    have hsq : Tendsto (fun n => ‖kn n - kf‖ ^ 2) atTop (𝓝 0) :=
      squeeze_zero (fun _ => sq_nonneg _) hb hlim
    have hsqrt := (Real.continuous_sqrt.tendsto 0).comp hsq
    simpa only [Function.comp_def, Real.sqrt_zero, Real.sqrt_sq (norm_nonneg _)] using hsqrt
  let Y : Ω → ℝ := fun ω => inner ℝ (q ω) c
  let Yn : ℕ → Ω → ℝ := fun n ω => inner ℝ (q ω) (coeffSection c n)
  have hY : MemLp Y 2 P := hq.inner_const c
  have hYn : ∀ n, MemLp (Yn n) 2 P := fun n => hq.inner_const (coeffSection c n)
  let Yp : Lp ℝ 2 P := hY.toLp Y
  let Ynp : ℕ → Lp ℝ 2 P := fun n => (hYn n).toLp (Yn n)
  have hfinite : ∀ n, Ynp n = A (kn n) := by
    intro n
    apply Lp.ext
    filter_upwards [(hYn n).coeFn_toLp,
      hcompact (fn n) (fn n).property (hk (fn n) (hnW n))] with ω h1 h2
    change Ynp n ω = Yn n ω at h1
    apply h1.trans
    simpa only [Yn, fp81s21_chartAction, fn, encode_chartSection E hP c n, kn] using h2
  have hYconv : Tendsto Ynp atTop (𝓝 Yp) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    have hsquare := inner_pairing_square_tendsto P q hq c (coeffSection c) (coeffSection_tendsto c)
    have heq : ∀ n, ‖Ynp n - Yp‖ ^ 2 = ∫ ω, (Yn n ω - Y ω) ^ 2 ∂P := by
      intro n
      rw [← real_inner_self_eq_norm_sq, L2.inner_def]
      apply integral_congr_ae
      filter_upwards [Lp.coeFn_sub (Ynp n) Yp,
        (hYn n).coeFn_toLp, hY.coeFn_toLp] with ω h1 h2 h3
      change (Ynp n - Yp) ω * (Ynp n - Yp) ω = _
      rw [h1]
      simp only [Pi.sub_apply]
      change Ynp n ω = _ at h2
      change Yp ω = _ at h3
      rw [h2, h3]
      ring
    have hsq : Tendsto (fun n => ‖Ynp n - Yp‖ ^ 2) atTop (𝓝 0) := by
      simpa only [heq, Yn, Y] using hsquare
    have hsqrt := (Real.continuous_sqrt.tendsto 0).comp hsq
    simpa only [Function.comp_def, Real.sqrt_zero, Real.sqrt_sq (norm_nonneg _)] using hsqrt
  have hYeq : Yp = A kf := by
    apply tendsto_nhds_unique hYconv
    have hAconv := A.continuous.tendsto kf |>.comp hkconv
    simpa only [Function.comp_def, ← hfinite] using hAconv
  have hae : Y =ᵐ[P] (A kf : Ω → ℝ) := by
    filter_upwards [hY.coeFn_toLp] with ω hω
    change Yp ω = Y ω at hω
    rw [hYeq] at hω
    exact hω.symm
  simpa only [Y, c, kf, fp81s21_chartAction] using hae

theorem fp81s21_linear_weighted_agreement
    (L : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 P)
    (q : Ω → r26t6_Coeff) (hq : MemLp q 2 P)
    (hcompact : ∀ g : Euc p.d → ℝ, IsR2Test g →
      ∀ hg : MemLp g 2 μ,
        (fun ω => fp81s21_chartAction E (q ω) g) =ᵐ[P]
          (L (hg.toLp g) : Ω → ℝ)) :
    ∀ f : Euc p.d → ℝ, Wt f →
      ∃ hf : MemLp f 2 μ,
        (fun ω => fp81s21_chartAction E (q ω) f) =ᵐ[P]
          (L (hf.toLp f) : Ω → ℝ) := by
  letI : IsProbabilityMeasure μ := HRS.Whole.Q34.isProbabilityMeasure_nu R.thermal.1.1
  have hr : (2 : ℝ) + (p.d : ℝ) / 2 < ((2 * p.d + 8 : ℕ) : ℝ) := by
    have hd : (0 : ℝ) ≤ p.d := Nat.cast_nonneg _
    push_cast
    linarith
  have hP : (p.d : ℝ) < 2 * ((p.d : ℝ) + 2) := by
    have hd : (0 : ℝ) ≤ p.d := Nat.cast_nonneg _
    linarith
  obtain ⟨B, hB, hOp⟩ := physical_weighted_L2_operators p.hd p.s p.a p.β
    ((p.d : ℝ) + 2) (2 * p.d + 8) p.hs0 p.hs p.ha p.hβ hr hP R.ρβ R.thermal
  let hk : ∀ g : Euc p.d → ℝ, Wt g → MemLp g 2 μ := fun g hg => (hOp g hg).1
  intro f hfW
  refine ⟨hk f hfW, ?_⟩
  let c := E.encode f
  let fn : ℕ → compactSmoothSubmodule p.d := chartSection E c
  let hnW : ∀ n, Wt (fn n) := fun n =>
    weightedTestSubmodule_iff.1 (weighted_test_of_compact_smooth hP
      (show IsR2Test (fn n : Euc p.d → ℝ) from (fn n).property))
  let kf : Lp ℝ 2 μ := (hk f hfW).toLp f
  let kn : ℕ → Lp ℝ 2 μ := fun n => (hk (fn n) (hnW n)).toLp (fn n)
  have hkconv : Tendsto kn atTop (𝓝 kf) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    have hb : ∀ n, ‖kn n - kf‖ ^ 2 ≤ B *
        (weightedSobolevE (2 * p.d + 8) ((p.d : ℝ) + 2)
          ((fn n : Euc p.d → ℝ) - f)).toReal ^ 2 := by
      intro n
      have heq : ‖kn n - kf‖ ^ 2 = ∫ x : Euc p.d,
          ((fn n : Euc p.d → ℝ) x - f x) ^ 2 ∂μ := by
        rw [← real_inner_self_eq_norm_sq, L2.inner_def]
        apply integral_congr_ae
        filter_upwards [Lp.coeFn_sub (kn n) kf, (hk (fn n) (hnW n)).coeFn_toLp,
          (hk f hfW).coeFn_toLp] with x h1 h2 h3
        change (kn n - kf) x * (kn n - kf) x = _
        rw [h1]
        simp only [Pi.sub_apply]
        change (kn n) x = _ at h2
        change kf x = _ at h3
        rw [h2, h3]
        ring
      rw [heq]
      simpa only [Pi.sub_apply] using (hOp _ (chartSection_error_weighted E hP f hfW n)).2.1
    have he := chartSection_error_tendsto E hP f hfW
    have hlim : Tendsto (fun n : ℕ => B *
        (weightedSobolevE (2 * p.d + 8) ((p.d : ℝ) + 2)
          ((fn n : Euc p.d → ℝ) - f)).toReal ^ 2) atTop (𝓝 0) := by
      simpa [fn, c] using (he.pow 2).const_mul B
    have hsq : Tendsto (fun n => ‖kn n - kf‖ ^ 2) atTop (𝓝 0) :=
      squeeze_zero (fun _ => sq_nonneg _) hb hlim
    have hsqrt := (Real.continuous_sqrt.tendsto 0).comp hsq
    simpa only [Function.comp_def, Real.sqrt_zero, Real.sqrt_sq (norm_nonneg _)] using hsqrt
  let Y : Ω → ℝ := fun ω => inner ℝ (q ω) c
  let Yn : ℕ → Ω → ℝ := fun n ω => inner ℝ (q ω) (coeffSection c n)
  have hY : MemLp Y 2 P := hq.inner_const c
  have hYn : ∀ n, MemLp (Yn n) 2 P := fun n => hq.inner_const (coeffSection c n)
  let Yp : Lp ℝ 2 P := hY.toLp Y
  let Ynp : ℕ → Lp ℝ 2 P := fun n => (hYn n).toLp (Yn n)
  have hfinite : ∀ n, Ynp n = L (kn n) := by
    intro n
    apply Lp.ext
    filter_upwards [(hYn n).coeFn_toLp,
      hcompact (fn n) (fn n).property (hk (fn n) (hnW n))] with ω h1 h2
    change Ynp n ω = Yn n ω at h1
    apply h1.trans
    simpa only [Yn, fp81s21_chartAction, fn, encode_chartSection E hP c n, kn] using h2
  have hYconv : Tendsto Ynp atTop (𝓝 Yp) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    have hsquare := inner_pairing_square_tendsto P q hq c (coeffSection c) (coeffSection_tendsto c)
    have heq : ∀ n, ‖Ynp n - Yp‖ ^ 2 = ∫ ω, (Yn n ω - Y ω) ^ 2 ∂P := by
      intro n
      rw [← real_inner_self_eq_norm_sq, L2.inner_def]
      apply integral_congr_ae
      filter_upwards [Lp.coeFn_sub (Ynp n) Yp,
        (hYn n).coeFn_toLp, hY.coeFn_toLp] with ω h1 h2 h3
      change (Ynp n - Yp) ω * (Ynp n - Yp) ω = _
      rw [h1]
      simp only [Pi.sub_apply]
      change Ynp n ω = _ at h2
      change Yp ω = _ at h3
      rw [h2, h3]
      ring
    have hsq : Tendsto (fun n => ‖Ynp n - Yp‖ ^ 2) atTop (𝓝 0) := by
      simpa only [heq, Yn, Y] using hsquare
    have hsqrt := (Real.continuous_sqrt.tendsto 0).comp hsq
    simpa only [Function.comp_def, Real.sqrt_zero, Real.sqrt_sq (norm_nonneg _)] using hsqrt
  have hYeq : Yp = L kf := by
    apply tendsto_nhds_unique hYconv
    have hLconv := L.continuous.tendsto kf |>.comp hkconv
    simpa only [Function.comp_def, ← hfinite] using hLconv
  have hae : Y =ᵐ[P] (L kf : Ω → ℝ) := by
    filter_upwards [hY.coeFn_toLp] with ω hω
    change Yp ω = Y ω at hω
    rw [hYeq] at hω
    exact hω.symm
  simpa only [Y, c, kf, fp81s21_chartAction] using hae

theorem fp81s21_wick_weighted_agreement_time
    (A : ℝ → Lp ℝ 2 μK →L[ℝ] Lp ℝ 2 P)
    (q : ℝ → Ω → r26t6_Coeff) (hq : ∀ u, 0 ≤ u → MemLp (q u) 2 P)
    (hcompact : ∀ u, 0 ≤ u → ∀ g : Euc p.d → ℝ, IsR2Test g →
      ∀ hg : MemLp (k g) 2 μK,
        (fun ω => fp81s21_chartAction E (q u ω) g) =ᵐ[P]
          (A u (hg.toLp (k g)) : Ω → ℝ)) :
    ∀ u, 0 ≤ u → ∀ f : Euc p.d → ℝ, Wt f →
      ∃ hf : MemLp (k f) 2 μK,
        (fun ω => fp81s21_chartAction E (q u ω) f) =ᵐ[P]
          (A u (hf.toLp (k f)) : Ω → ℝ) := by
  intro u hu
  exact fp81s21_wick_weighted_agreement p R E P (A u) (q u) (hq u hu) (hcompact u hu)

theorem fp81s21_linear_weighted_agreement_time
    (L : ℝ → Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 P)
    (q : ℝ → Ω → r26t6_Coeff) (hq : ∀ u, 0 ≤ u → MemLp (q u) 2 P)
    (hcompact : ∀ u, 0 ≤ u → ∀ g : Euc p.d → ℝ, IsR2Test g →
      ∀ hg : MemLp g 2 μ,
        (fun ω => fp81s21_chartAction E (q u ω) g) =ᵐ[P]
          (L u (hg.toLp g) : Ω → ℝ)) :
    ∀ u, 0 ≤ u → ∀ f : Euc p.d → ℝ, Wt f →
      ∃ hf : MemLp f 2 μ,
        (fun ω => fp81s21_chartAction E (q u ω) f) =ᵐ[P]
          (L u (hf.toLp f) : Ω → ℝ) := by
  intro u hu
  exact fp81s21_linear_weighted_agreement p R E P (L u) (q u) (hq u hu) (hcompact u hu)

theorem fp81s21_wick_constant_agreement_time
    (A : ℝ → Lp ℝ 2 μK →L[ℝ] Lp ℝ 2 P)
    (q : ℝ → Ω → r26t6_Coeff) (hq : ∀ u, 0 ≤ u → MemLp (q u) 2 P)
    (hcompact : ∀ u, 0 ≤ u → ∀ g : Euc p.d → ℝ, IsR2Test g →
      ∀ hg : MemLp (k g) 2 μK,
        (fun ω => fp81s21_chartAction E (q u ω) g) =ᵐ[P]
          (A u (hg.toLp (k g)) : Ω → ℝ)) :
    ∀ u, 0 ≤ u →
      (fun ω => fp81s21_chartAction E (q u ω) (fun _ => 1)) =ᵐ[P] 0 := by
  intro u hu
  have hP : (p.d : ℝ) < 2 * ((p.d : ℝ) + 2) := by
    have hd : (0 : ℝ) ≤ p.d := Nat.cast_nonneg _
    linarith
  obtain ⟨hf, hae⟩ := fp81s21_wick_weighted_agreement p R E P (A u) (q u)
    (hq u hu) (hcompact u hu) (fun _ => 1) (constant_isWeightedTest hP 1)
  have hzero : k (fun _ => 1) = 0 := by
    funext xy
    simp [gradient, commutatorKernel]
  have hLp : hf.toLp (k (fun _ => 1)) = 0 := by
    apply Lp.ext
    filter_upwards [hf.coeFn_toLp, Lp.coeFn_zero ℝ 2 μK] with xy hxy hz
    change (hf.toLp (k (fun _ => 1))) xy = k (fun _ => 1) xy at hxy
    have hzxy : k (fun _ => 1) xy = 0 := congrFun hzero xy
    exact hxy.trans (hzxy.trans hz.symm)
  rw [hLp, map_zero] at hae
  exact hae.trans (Lp.coeFn_zero ℝ 2 P)

#print axioms fp81s21_wick_weighted_agreement
#print axioms fp81s21_linear_weighted_agreement
#print axioms fp81s21_wick_weighted_agreement_time
#print axioms fp81s21_linear_weighted_agreement_time
#print axioms fp81s21_wick_constant_agreement_time
end HRS.Fp81.S21
end
