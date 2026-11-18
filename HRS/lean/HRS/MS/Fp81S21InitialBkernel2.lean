import HRS.MS.Fp81S21InitialBkernel
import HRS.MS.R2SeAux30

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators RealInnerProductSpace ContDiff

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000
noncomputable section

namespace HRS.Fp81.S21

open S45 S99
open HRS.Whole
open HRS (Euc MemCb cbNorm)
open HRS.MS.R26T3

/-- The actual-law `Bterm` integrand is integrable for every bounded test in
the finite-rank limit class. -/
theorem fp81s21_initial_Bterm_int
    {p : Parameters} {δ : ℝ} (hδ : 0 < δ) (hδh : δ ≤ 1 / 2)
    (R : Trajectory p δ) (E : InitialSteinEnv R) (hγ : 0 < p.γ)
    {φ : ℕ → Euc p.d → ℝ}
    (hφ : IsSummableFeatureFamily (fp81s21_J1 p.d) φ)
    {B : ℝ} {h : Euc p.d → Euc p.d → ℝ}
    (hh : IsBoundedPairKernel p.s B h) {N : ℕ} (hN : 2 ≤ N)
    {ψ : SeqL2 → ℝ} (hψ : S99.Bd 4 ψ) :
    Integrable (fun X : EucConfig p.d N =>
      fp81s21_initial_Bh R N h X * ψ (featureVec φ (r26t3_marg R N) X))
      (r26t3_Q R N) := by
  have hN1 : 1 ≤ N := by omega
  haveI hP : IsProbabilityMeasure (r26t3_Q R N) := by
    rw [← E.law_eq N]
    exact (E.static N hN).prob
  haveI hν : IsProbabilityMeasure (r26t3_marg R N) := S99.s99_nu_prob hN1
  have hWc : Continuous (fun X : EucConfig p.d N => featureVec φ (r26t3_marg R N) X) :=
    (S99.s99_W_contDiff hN1 (by unfold fp81s21_J1; omega) hφ).continuous
  let ψW : EucConfig p.d N → ℝ := fun X => ψ (featureVec φ (r26t3_marg R N) X)
  have hψBM : S99.BM ψW :=
    ⟨(hψ.1.continuous.comp hWc).measurable, 1, fun X => hψ.abs_le _⟩
  have hψWb : ∀ X, |ψW X| ≤ 1 := fun X => hψ.abs_le _
  have hBh := fp81s21_initial_Bh_int hδ hδh R E hγ hh hN
  have hmul := hBh.mul_bdd hψBM.meas.aestronglyMeasurable
    (Filter.Eventually.of_forall fun X => by
      rw [Real.norm_eq_abs]
      exact hψWb X)
  exact hmul.congr (Filter.Eventually.of_forall fun X => by rfl)

/-- Difference of actual-law response coefficients, controlled by the
product-law `L¹` distance of the kernels. -/
theorem fp81s21_initial_Qk_diff
    {p : Parameters} {δ : ℝ} {R : Trajectory p δ}
    (E : InitialSteinEnv R) {φ : ℕ → Euc p.d → ℝ}
    (hφ : IsSummableFeatureFamily (fp81s21_J1 p.d) φ)
    (F : InitialFamData R φ) {k₁ k₂ : Euc p.d → Euc p.d → ℝ}
    (h₁ : Integrable (Function.uncurry k₁)
      ((r26t3_mu R 0).prod (r26t3_mu R 0)))
    (h₂ : Integrable (Function.uncurry k₂)
      ((r26t3_mu R 0).prod (r26t3_mu R 0))) (l q : ℕ) :
    |fp81s21_initial_Qk R φ k₁ l q - fp81s21_initial_Qk R φ k₂ l q| ≤
      (F.K * cbNorm (fp81s21_J1 p.d) (φ l)) *
        (F.K * cbNorm (fp81s21_J1 p.d) (φ q)) *
        ∫ z : Euc p.d × Euc p.d, |k₁ z.1 z.2 - k₂ z.1 z.2|
          ∂((r26t3_mu R 0).prod (r26t3_mu R 0)) := by
  haveI hμ : IsProbabilityMeasure (r26t3_mu R 0) :=
    HRS.Whole.Q34.isProbabilityMeasure_nu E.reference.prob
  let μ : Measure (Euc p.d) := r26t3_mu R 0
  let b : ℕ → ℝ := fun j => cbNorm (fp81s21_J1 p.d) (φ j)
  have hb0 : ∀ j, 0 ≤ b j := fun j => HRS.MS.Tc5.tc5_cb_nonneg _ _
  have hal : ∀ j, Continuous (r26t3_a R (φ j)) := fun j => (F.amem j).1.continuous
  have hab : ∀ j x, |r26t3_a R (φ j) x| ≤ F.K * b j := by
    intro j x
    have h := S99.s99_norm_iter_le_cb (F.amem j) (Nat.zero_le _) x
    rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at h
    exact h.trans (F.anorm j)
  let w : Euc p.d × Euc p.d → ℝ := fun z =>
    r26t3_a R (φ l) z.1 * r26t3_a R (φ q) z.2
  have hwc : Continuous w := ((hal l).comp continuous_fst).mul ((hal q).comp continuous_snd)
  have hwb : ∀ z, |w z| ≤ (F.K * b l) * (F.K * b q) := by
    intro z
    simp only [w]
    rw [abs_mul]
    exact mul_le_mul (hab l _) (hab q _) (abs_nonneg _)
      ((abs_nonneg _).trans (hab l 0))
  have hint : ∀ {k : Euc p.d → Euc p.d → ℝ},
      Integrable (Function.uncurry k) (μ.prod μ) →
      Integrable (fun z : Euc p.d × Euc p.d => k z.1 z.2 * w z) (μ.prod μ) := by
    intro k hk
    have hbound : 0 ≤ (F.K * b l) * (F.K * b q) :=
      (abs_nonneg _).trans (hwb 0)
    have hm := hk.bdd_mul (f := w) (c := (F.K * b l) * (F.K * b q))
      hwc.aestronglyMeasurable (Filter.Eventually.of_forall fun z => by
        rw [Real.norm_eq_abs]
        exact hwb z)
    exact hm.congr (Filter.Eventually.of_forall fun z => by
      simp [Function.uncurry]
      ring)
  have hQ : ∀ k : Euc p.d → Euc p.d → ℝ,
      fp81s21_initial_Qk R φ k l q =
        ∫ z : Euc p.d × Euc p.d, k z.1 z.2 * w z ∂(μ.prod μ) := by
    intro k
    unfold fp81s21_initial_Qk
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    simp only [w, μ]
    ring
  rw [hQ k₁, hQ k₂, ← integral_sub (hint h₁) (hint h₂)]
  have hdiff : Integrable
      (fun z : Euc p.d × Euc p.d => |k₁ z.1 z.2 - k₂ z.1 z.2|) (μ.prod μ) :=
    (h₁.sub h₂).abs
  rw [← Real.norm_eq_abs]
  refine (norm_integral_le_integral_norm _).trans ?_
  rw [← integral_const_mul]
  have hA0 : 0 ≤ (F.K * b l) * (F.K * b q) :=
    (abs_nonneg _).trans (hwb 0)
  refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun z => norm_nonneg _)
    (hdiff.const_mul _) (Filter.Eventually.of_forall fun z => ?_)
  beta_reduce
  rw [← sub_mul, Real.norm_eq_abs, abs_mul]
  calc |k₁ z.1 z.2 - k₂ z.1 z.2| * |w z|
      ≤ |k₁ z.1 z.2 - k₂ z.1 z.2| * ((F.K * b l) * (F.K * b q)) :=
        mul_le_mul_of_nonneg_left (hwb z) (abs_nonneg _)
    _ = _ := by ring

/-- Qualitative singular-kernel limit under the actual initial law.  The
finite-rank approximant is fixed before its FR constant and the resulting
particle cutoff are chosen. -/
theorem fp81s21_initial_Bkernel
    {p : Parameters} {δ : ℝ} (hδ : 0 < δ) (hδh : δ ≤ 1 / 2)
    (R : Trajectory p δ) (E : InitialSteinEnv R) (hγ : 0 < p.γ)
    {φ : ℕ → Euc p.d → ℝ}
    (hφ : IsSummableFeatureFamily (fp81s21_J1 p.d) φ)
    (F : InitialFamData R φ)
    {G : Measure SeqL2} [IsProbabilityMeasure G]
    (hG : IsCenteredGaussianSeq G (fun i j =>
      HRS.Whole.susceptibilityCov (HRS.Whole.rieszKernel p.d p.s)
        (r26t3_mu R 0) p.γ (φ i) (φ j)) )
    {B : ℝ} {h : Euc p.d → Euc p.d → ℝ}
    (hh : IsBoundedPairKernel p.s B h) :
    ∀ ε : ℝ, 0 < ε → ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N → 2 ≤ N →
      ∀ ψ : SeqL2 → ℝ, S99.Bd 4 ψ →
        |fp81s21_initial_Bterm R φ N h ψ - (1 / 2) * ∑' l, ∑' q,
          fp81s21_initial_Qk R φ h l q *
            ∫ z, S99.pd (S99.pd ψ l) q z ∂G| ≤ ε := by
  intro ε hε
  have hsd : p.s < p.d := by
    have hsd' := p.hs
    have hdpos : (0 : ℝ) ≤ (p.d : ℝ) / 2 := by positivity
    linarith
  haveI hμ : IsProbabilityMeasure (r26t3_mu R 0) :=
    HRS.Whole.Q34.isProbabilityMeasure_nu E.reference.prob
  obtain ⟨C₂, hj, ha, htail⟩ :=
    fp81s21_initial_F_tail_exists hδ hδh R hγ 1 le_rfl hh
  let b : ℕ → ℝ := fun j => cbNorm (fp81s21_J1 p.d) (φ j)
  have hb0 : ∀ j, 0 ≤ b j := fun j => HRS.MS.Tc5.tc5_cb_nonneg _ _
  have hbs : Summable b := hφ.2
  let Sb : ℝ := ∑' j, b j
  have hQc0 : 0 < F.K ^ 2 * Sb ^ 2 + 1 := by positivity
  let Qc : ℝ := F.K ^ 2 * Sb ^ 2 + 1
  have hconv := ha.converges 1 le_rfl (by simpa using hsd)
  obtain ⟨n₁, hn₁⟩ := eventually_atTop.1
    (hconv.eventually (gt_mem_nhds (ENNReal.ofReal_pos.2
      (show 0 < ε / (3 * Qc) by positivity))))
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.1
    (htail.2.eventually (gt_mem_nhds (ENNReal.ofReal_pos.2
      (show 0 < ε / 3 by positivity))))
  let n : ℕ := max n₀ n₁
  obtain ⟨m, cc, u, hu, hjn⟩ := ha.finiteRank n
  obtain ⟨K, hK0, hFR⟩ :=
    fp81s21_initial_FR hδ hδh R E hγ hφ F hG hu
  refine ⟨max 2 (⌈(3 * K / ε) ^ 2⌉₊ + 1), fun N hN hN2 ψ hψ => ?_⟩
  have hN2' : 2 ≤ N := hN2
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hsqN : 0 < Real.sqrt N := Real.sqrt_pos.2 hN0
  have hN1 : 1 ≤ N := by omega
  haveI hP : IsProbabilityMeasure (r26t3_Q R N) := by
    rw [← E.law_eq N]
    exact (E.static N hN2').prob
  haveI hν : IsProbabilityMeasure (r26t3_marg R N) := S99.s99_nu_prob hN1
  have hhj : IsBoundedPairKernel p.s (C₂ * B) (hj n) :=
    fp81s21_initial_approx_bounded R ha n
  have hkd : IsBoundedPairKernel p.s (C₂ * B + B)
      (fun x y => hj n x y - h x y) :=
    HRS.MS.R2Mt.s92_diff_kernel hh ha n
  have hWc : Continuous (fun X : EucConfig p.d N => featureVec φ (r26t3_marg R N) X) :=
    (S99.s99_W_contDiff hN1 (by unfold fp81s21_J1; omega) hφ).continuous
  let ψW : EucConfig p.d N → ℝ := fun X => ψ (featureVec φ (r26t3_marg R N) X)
  have hψBM : S99.BM ψW :=
    ⟨(hψ.1.continuous.comp hWc).measurable, 1, fun X => hψ.abs_le _⟩
  have hψWb : ∀ X, |ψW X| ≤ 1 := fun X => hψ.abs_le _
  have hIh := fp81s21_initial_Bterm_int hδ hδh R E hγ hφ hh hN2' hψ
  have hIhj := fp81s21_initial_Bterm_int hδ hδh R E hγ hφ hhj hN2' hψ
  have hBhD := fp81s21_initial_Bh_int hδ hδh R E hγ hkd hN2'
  have htailLp : ∀ N : ℕ, 2 ≤ N →
      eLpNorm (fun X : EucConfig p.d N =>
        fp81s21_initial_Bh R N (fun x y => hj n x y - h x y) X) 1
        (r26t3_Q R N) ≤ ENNReal.ofReal (ε / 3) := by
    intro N hN'
    have ht := (le_iSup₂_of_le () ⟨N, hN'⟩ le_rfl).trans (hn₀ n (le_max_left _ _)).le
    simpa [fp81s21_initial_Bh] using ht
  have htailL1 : ∫ X,
      |fp81s21_initial_Bh R N (fun x y => hj n x y - h x y) X|
      ∂(r26t3_Q R N) ≤ ε / 3 := by
    have ht := S99.s99_l1_bound (by positivity) hBhD.aestronglyMeasurable (htailLp N hN2')
    exact ht.2
  -- Term A: the uniform actual-law tail.
  have hBhDiff : ∀ X,
      fp81s21_initial_Bh R N h X - fp81s21_initial_Bh R N (hj n) X =
        -fp81s21_initial_Bh R N (fun x y => hj n x y - h x y) X := by
    intro X
    have ht := fp81s21_initial_Bh_sub hδ hδh R E hγ hhj hh hN2' X
    linarith
  have hA :
      |fp81s21_initial_Bterm R φ N h ψ -
        fp81s21_initial_Bterm R φ N (hj n) ψ| ≤ ε / 3 := by
    have e : (fun X : EucConfig p.d N =>
        fp81s21_initial_Bh R N h X * ψW X -
          fp81s21_initial_Bh R N (hj n) X * ψW X) =
        fun X => -fp81s21_initial_Bh R N
          (fun x y => hj n x y - h x y) X * ψW X := by
      funext X
      rw [← sub_mul, hBhDiff X]
    change |(∫ X, fp81s21_initial_Bh R N h X *
        ψ (featureVec φ (r26t3_marg R N) X) ∂(r26t3_Q R N)) -
      (∫ X, fp81s21_initial_Bh R N (hj n) X *
        ψ (featureVec φ (r26t3_marg R N) X) ∂(r26t3_Q R N))| ≤ ε / 3
    rw [← integral_sub hIh hIhj]
    simp only [ψW] at e ⊢
    rw [e, ← Real.norm_eq_abs]
    refine (norm_integral_le_integral_norm _).trans ?_
    have hBi : Integrable
        (fun X : EucConfig p.d N =>
          |fp81s21_initial_Bh R N (fun x y => hj n x y - h x y) X|)
        (r26t3_Q R N) := hBhD.abs
    refine le_trans ?_ htailL1
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun X => norm_nonneg _) hBi
      (Filter.Eventually.of_forall fun X => ?_)
    beta_reduce
    rw [Real.norm_eq_abs, abs_mul, abs_neg]
    calc |fp81s21_initial_Bh R N (fun x y => hj n x y - h x y) X| * |ψW X|
        ≤ |fp81s21_initial_Bh R N (fun x y => hj n x y - h x y) X| * 1 :=
          mul_le_mul_of_nonneg_left (hψWb X) (abs_nonneg _)
      _ = _ := by rw [mul_one]
  -- Term B: the fixed finite-rank kernel.
  have hB :
      |fp81s21_initial_Bterm R φ N (hj n) ψ - (1 / 2) * ∑' l, ∑' q,
        fp81s21_initial_Qk R φ (hj n) l q *
          ∫ z, S99.pd (S99.pd ψ l) q z ∂G| ≤ ε / 3 := by
    have h1 := hFR N hN2' hψ
    rw [← hjn] at h1
    refine h1.trans ?_
    rw [div_le_iff₀ hsqN]
    have hx : (3 * K / ε) ^ 2 ≤ (N : ℝ) := by
      have h2 : (3 * K / ε) ^ 2 ≤ (⌈(3 * K / ε) ^ 2⌉₊ : ℝ) := Nat.le_ceil _
      have h3 : ((⌈(3 * K / ε) ^ 2⌉₊ + 1 : ℕ) : ℝ) ≤ (N : ℝ) := by
        exact_mod_cast (le_max_right 2 (⌈(3 * K / ε) ^ 2⌉₊ + 1)).trans hN
      push_cast at h3
      linarith
    have h4 : 3 * K / ε ≤ Real.sqrt N := Real.le_sqrt_of_sq_le hx
    rw [div_le_iff₀ hε] at h4
    nlinarith
  -- Term C: convergence of the singular-kernel coefficients.
  have hwj : Integrable (Function.uncurry (hj n))
      ((r26t3_mu R 0).prod (r26t3_mu R 0)) :=
    (fp81s21_initial_kernel_wr8 hδ hδh R hhj).prod
  have hwh : Integrable (Function.uncurry h)
      ((r26t3_mu R 0).prod (r26t3_mu R 0)) :=
    (fp81s21_initial_kernel_wr8 hδ hδh R hh).prod
  have hzero : Integrable (Function.uncurry (fun _ _ : Euc p.d => (0 : ℝ)))
      ((r26t3_mu R 0).prod (r26t3_mu R 0)) := integrable_const 0
  have hQ0 : ∀ l q,
      fp81s21_initial_Qk R φ (fun _ _ => (0 : ℝ)) l q = 0 := by
    intro l q
    unfold fp81s21_initial_Qk
    simp
  have hQb : ∀ (k : Euc p.d → Euc p.d → ℝ),
      Integrable (Function.uncurry k) ((r26t3_mu R 0).prod (r26t3_mu R 0)) →
      ∀ l q, |fp81s21_initial_Qk R φ k l q| ≤
        F.K ^ 2 * (∫ z : Euc p.d × Euc p.d, |k z.1 z.2|
          ∂((r26t3_mu R 0).prod (r26t3_mu R 0))) * (b l * b q) := by
    intro k hk l q
    have ht := fp81s21_initial_Qk_diff E hφ F hk hzero l q
    rw [hQ0, sub_zero] at ht
    refine ht.trans (le_of_eq ?_)
    simp [b]
    ring
  let Gm : ℕ → ℕ → ℝ := fun l q =>
    ∫ z, S99.pd (S99.pd ψ l) q z ∂G
  have hGb : ∀ l q, |Gm l q| ≤ 1 := by
    intro l q
    have h := norm_integral_le_of_norm_le_const (μ := G)
      (f := S99.pd (S99.pd ψ l) q) (C := 1)
      (Filter.Eventually.of_forall fun z => by
        rw [Real.norm_eq_abs]
        exact ((hψ.pd l).pd q).abs_le z)
    simpa [Real.norm_eq_abs, Gm] using h
  have hdm : Measurable (fun z : Euc p.d × Euc p.d => hj n z.1 z.2 - h z.1 z.2) :=
    hhj.measurable.sub hh.measurable
  have hlt := hn₁ n (le_max_right _ _)
  have hle : eLpNorm (fun z : Euc p.d × Euc p.d => hj n z.1 z.2 - h z.1 z.2)
      1 ((r26t3_mu R 0).prod (r26t3_mu R 0)) ≤
        ENNReal.ofReal (ε / (3 * Qc)) := by
    simpa using hlt.le
  obtain ⟨-, hδbound⟩ := S99.s99_l1_bound (by positivity) hdm.aestronglyMeasurable hle
  let δ₁ : ℝ := ∫ z : Euc p.d × Euc p.d,
    |hj n z.1 z.2 - h z.1 z.2| ∂((r26t3_mu R 0).prod (r26t3_mu R 0))
  have hδ₁0 : 0 ≤ δ₁ := by
    dsimp [δ₁]
    exact integral_nonneg fun z => abs_nonneg _
  have hδ₁le : δ₁ ≤ ε / (3 * Qc) := by
    dsimp [δ₁]
    exact hδbound
  have hQdiff := fun l q =>
    fp81s21_initial_Qk_diff E hφ F hwj hwh l q
  have hsumDiff := S99.s99_tsum2_sub hb0 hbs
    (A1 := F.K ^ 2 *
      (∫ z : Euc p.d × Euc p.d, |hj n z.1 z.2|
        ∂((r26t3_mu R 0).prod (r26t3_mu R 0))))
    (A2 := F.K ^ 2 *
      (∫ z : Euc p.d × Euc p.d, |h z.1 z.2|
        ∂((r26t3_mu R 0).prod (r26t3_mu R 0))))
    (D := F.K ^ 2 * δ₁)
    (f := fun l q => fp81s21_initial_Qk R φ (hj n) l q * Gm l q)
    (g := fun l q => fp81s21_initial_Qk R φ h l q * Gm l q)
    (fun l q => by
      rw [abs_mul]
      calc |fp81s21_initial_Qk R φ (hj n) l q| * |Gm l q|
          ≤ |fp81s21_initial_Qk R φ (hj n) l q| * 1 :=
            mul_le_mul_of_nonneg_left (hGb l q) (abs_nonneg _)
        _ ≤ _ := by
          rw [mul_one]
          exact hQb (hj n) hwj l q)
    (fun l q => by
      rw [abs_mul]
      calc |fp81s21_initial_Qk R φ h l q| * |Gm l q|
          ≤ |fp81s21_initial_Qk R φ h l q| * 1 :=
            mul_le_mul_of_nonneg_left (hGb l q) (abs_nonneg _)
        _ ≤ _ := by
          rw [mul_one]
          exact hQb h hwh l q)
    (fun l q => by
      rw [← sub_mul, abs_mul]
      calc |fp81s21_initial_Qk R φ (hj n) l q -
            fp81s21_initial_Qk R φ h l q| * |Gm l q|
          ≤ |fp81s21_initial_Qk R φ (hj n) l q -
              fp81s21_initial_Qk R φ h l q| * 1 :=
            mul_le_mul_of_nonneg_left (hGb l q) (abs_nonneg _)
        _ ≤ _ := by
          rw [mul_one]
          refine (hQdiff l q).trans (le_of_eq ?_)
          simp [δ₁, b]
          ring)
  have hC :
      |(1 / 2) * ∑' l, ∑' q,
          fp81s21_initial_Qk R φ (hj n) l q *
            ∫ z, S99.pd (S99.pd ψ l) q z ∂G -
        (1 / 2) * ∑' l, ∑' q,
          fp81s21_initial_Qk R φ h l q *
            ∫ z, S99.pd (S99.pd ψ l) q z ∂G| ≤ ε / 3 := by
    rw [← mul_sub, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    have hS0 : 0 ≤ Sb := tsum_nonneg hb0
    calc
      (1 / 2) *
          |(∑' l, ∑' q, fp81s21_initial_Qk R φ (hj n) l q * Gm l q) -
            ∑' l, ∑' q, fp81s21_initial_Qk R φ h l q * Gm l q|
          ≤ (1 / 2) * (F.K ^ 2 * δ₁ * Sb ^ 2) :=
        mul_le_mul_of_nonneg_left hsumDiff (by norm_num)
      _ ≤ (1 / 2) * (Qc * (ε / (3 * Qc))) := by
        refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
        have he : F.K ^ 2 * δ₁ * Sb ^ 2 = (F.K ^ 2 * Sb ^ 2) * δ₁ := by ring
        rw [he]
        exact mul_le_mul (by dsimp [Qc]; linarith) hδ₁le hδ₁0 hQc0.le
      _ ≤ ε / 3 := by
        have he : Qc * (ε / (3 * Qc)) = ε / 3 := by
          dsimp [Qc]
          field_simp
        rw [he]
        linarith
  -- Assemble the tail, finite-rank, and coefficient estimates.
  calc
    |fp81s21_initial_Bterm R φ N h ψ -
        (1 / 2) * ∑' l, ∑' q, fp81s21_initial_Qk R φ h l q *
          ∫ z, S99.pd (S99.pd ψ l) q z ∂G|
      = |(fp81s21_initial_Bterm R φ N h ψ -
            fp81s21_initial_Bterm R φ N (hj n) ψ) +
          (fp81s21_initial_Bterm R φ N (hj n) ψ -
            (1 / 2) * ∑' l, ∑' q,
              fp81s21_initial_Qk R φ (hj n) l q *
                ∫ z, S99.pd (S99.pd ψ l) q z ∂G) +
          ((1 / 2) * ∑' l, ∑' q,
              fp81s21_initial_Qk R φ (hj n) l q *
                ∫ z, S99.pd (S99.pd ψ l) q z ∂G -
            (1 / 2) * ∑' l, ∑' q,
              fp81s21_initial_Qk R φ h l q *
                ∫ z, S99.pd (S99.pd ψ l) q z ∂G)| := by
          congr 1
          ring
    _ ≤ ε / 3 + ε / 3 + ε / 3 := by
      exact ((abs_add_le _ _).trans
        (add_le_add (abs_add_le _ _) le_rfl)).trans
          (add_le_add (add_le_add hA hB) hC)
    _ = ε := by ring

#print axioms fp81s21_initial_Bkernel
#print axioms fp81s21_initial_Bterm_int
#print axioms fp81s21_initial_Qk_diff

end HRS.Fp81.S21

end
