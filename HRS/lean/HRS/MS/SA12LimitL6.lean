import HRS.MS.SA12LimitL3
import HRS.MS.SA12LimitL4
import HRS.MS.SA12LimitL5
import HRS.MS.SA12DualL2
import HRS.MS.ToriCoefAAux1

/-!
# S.A.12 L6: weak compactness of uniformly bounded `H⁰_uloc` paths
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MH.AdjointRd.Phase2SA12Limit

open HRS HRS.Whole HRS.Whole.AppendixA HRS.MH.AdjointRd HRS.MS.UniqM1

variable {d : ℕ}

theorem sa12x_vol_ac_mu : (volume : Measure (Euc d)) ≪ compactMeasure d :=
  withDensity_absolutelyContinuous' sa12l3_measurable_weight.aemeasurable
    (Filter.Eventually.of_forall fun x => (ENNReal.ofReal_pos.2 (sa12x_weight_pos x)).ne')

theorem sa12x_ae_vol {f g : Euc d → ℝ} (h : f =ᵐ[compactMeasure d] g) : f =ᵐ[volume] g :=
  sa12x_vol_ac_mu.ae_le h

theorem sa12x_test_memLp {ψ : Euc d → ℝ} (hc : Continuous ψ) (hs : HasCompactSupport ψ) :
    MemLp (fun x => ψ x / compactWeight d x) 2 (compactMeasure d) := by
  have hw : Continuous (compactWeight d) := sa12x_weight_contDiff.continuous
  have hcont : Continuous fun x => ψ x / compactWeight d x :=
    hc.div hw fun x => (sa12x_weight_pos x).ne'
  have hsupp : HasCompactSupport fun x => ψ x / compactWeight d x := by
    have : (fun x => ψ x / compactWeight d x) = fun x => ψ x * (compactWeight d x)⁻¹ := by
      funext x; simp [div_eq_mul_inv]
    rw [this]
    exact hs.mul_right
  exact hcont.memLp_of_hasCompactSupport hsupp

theorem sa12x_inner_test (f : CompactL2 d) {ψ : Euc d → ℝ} (hc : Continuous ψ) (hs : HasCompactSupport ψ) :
    inner ℝ f ((sa12x_test_memLp hc hs).toLp _) = ∫ x, f x * ψ x := by
  rw [MeasureTheory.L2.inner_def]
  have h1 : (fun a => inner ℝ (f a) (((sa12x_test_memLp hc hs).toLp _ : CompactL2 d) a)) =ᵐ[compactMeasure d]
      fun a => (ψ a / compactWeight d a) * f a := by
    filter_upwards [(sa12x_test_memLp hc hs).coeFn_toLp] with a ha
    rw [ha]; simp [mul_comm]
  rw [integral_congr_ae h1]
  unfold compactMeasure
  rw [integral_withDensity_eq_integral_toReal_smul sa12l3_measurable_weight
    (Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  have hx := sa12x_weight_pos x
  simp only [smul_eq_mul, ENNReal.toReal_ofReal hx.le]
  field_simp

theorem sa12x_weighted_loc (f : CompactL2 d) (c : Euc d) (R : ℝ) :
    MemLp (fun x => (f : Euc d → ℝ) x) 2 (volume.restrict (Metric.ball c R)) := by
  have hg : Measurable (f : Euc d → ℝ) := (Lp.stronglyMeasurable f).measurable
  have hfin : ∫⁻ x, ‖(f : Euc d → ℝ) x‖ₑ ^ 2 ∂(compactMeasure d) < ⊤ := by
    rw [← sq_eLpNorm_two (Lp.aestronglyMeasurable f)]
    exact ENNReal.pow_lt_top (Lp.memLp f).eLpNorm_lt_top
  have hdens : ∀ g : Euc d → ℝ≥0∞, Measurable g → ∫⁻ x, g x ∂(compactMeasure d) =
      ∫⁻ x, ENNReal.ofReal (compactWeight d x) * g x := fun g hg =>
    lintegral_withDensity_eq_lintegral_mul _ sa12l3_measurable_weight hg
  rw [hdens _ (hg.enorm.pow_const 2)] at hfin
  set ω0 : ℝ := (1 + ‖c‖ + |R|) ^ (-((d : ℝ) + 3)) with hω0
  have hbase : 0 < 1 + ‖c‖ + |R| := by positivity
  have hω0pos : 0 < ω0 := Real.rpow_pos_of_pos hbase _
  have hlow : ∀ x ∈ Metric.ball c R, ω0 ≤ compactWeight d x := by
    intro x hx
    have hxn : ‖x‖ ≤ ‖c‖ + |R| := by
      have h1 : ‖x - c‖ < R := by rwa [Metric.mem_ball, dist_eq_norm] at hx
      have h2 : ‖x‖ ≤ ‖c‖ + ‖x - c‖ := by
        calc ‖x‖ = ‖c + (x - c)‖ := by congr 1; abel
          _ ≤ _ := norm_add_le _ _
      linarith [le_abs_self R]
    have hjb : jbracket x ≤ 1 + ‖c‖ + |R| := by
      unfold jbracket
      rw [Real.sqrt_le_left (by positivity)]
      nlinarith [norm_nonneg x, norm_nonneg c, abs_nonneg R]
    unfold compactWeight
    exact Real.rpow_le_rpow_of_nonpos (HRS.MS.ToriCoefA.tca_jbracket_pos x) hjb
      (by have : (0 : ℝ) ≤ d := Nat.cast_nonneg d; linarith)
  have h1 : ENNReal.ofReal ω0 * ∫⁻ x in Metric.ball c R, ‖(f : Euc d → ℝ) x‖ₑ ^ 2 < ⊤ := by
    rw [← lintegral_const_mul _ (hg.enorm.pow_const 2)]
    refine lt_of_le_of_lt ?_ hfin
    refine le_trans (setLIntegral_mono' Metric.isOpen_ball.measurableSet fun x hx => ?_)
      (setLIntegral_le_lintegral _ _)
    exact mul_le_mul_left (ENNReal.ofReal_le_ofReal (hlow x hx)) _
  have h2 : ∫⁻ x in Metric.ball c R, ‖(f : Euc d → ℝ) x‖ₑ ^ 2 < ⊤ := by
    by_contra hcon
    rw [not_lt, top_le_iff] at hcon
    rw [hcon, ENNReal.mul_top (ENNReal.ofReal_pos.2 hω0pos).ne'] at h1
    exact lt_irrefl _ h1
  rw [memLp_iff, eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (by norm_num) (by simp)
    hg.aestronglyMeasurable.restrict]
  simpa using h2

theorem sa12x_cut_memLp (f : CompactL2 d) {χ : Euc d → ℝ} (hχ : IsUlocCutoff χ) (z : Euc d) :
    MemLp (fun x => χ (x - z) * (f : Euc d → ℝ) x) 2 volume := by
  have hloc := sa12x_weighted_loc f z 2
  have hχc : Continuous fun x : Euc d => χ (x - z) :=
    hχ.1.continuous.comp (continuous_id.sub continuous_const)
  have hm : AEStronglyMeasurable (fun x => χ (x - z) * (f : Euc d → ℝ) x) volume :=
    hχc.aestronglyMeasurable.mul (Lp.stronglyMeasurable f).aestronglyMeasurable
  have hle : eLpNorm (fun x => χ (x - z) * (f : Euc d → ℝ) x) 2 volume ≤
      eLpNorm ((Metric.ball z 2).indicator (fun x => (f : Euc d → ℝ) x)) 2 volume := by
    refine eLpNorm_mono hm fun x => ?_
    by_cases hx : x ∈ Metric.ball z 2
    · rw [Set.indicator_of_mem hx, norm_mul, Real.norm_of_nonneg (hχ.2.2.2.1 _).1]
      exact mul_le_of_le_one_left (norm_nonneg _) (hχ.2.2.2.1 _).2
    · rw [Set.indicator_of_notMem hx]
      have : χ (x - z) = 0 := by
        by_contra hne
        have h1 : x - z ∈ tsupport χ := subset_tsupport _ (Function.mem_support.2 hne)
        have := hχ.2.2.1 h1
        rw [Metric.mem_ball, dist_zero_right] at this
        exact hx (by rw [Metric.mem_ball, dist_eq_norm]; exact this)
      simp [this]
  rw [memLp_iff]
  refine hle.trans_lt ?_
  rw [eLpNorm_indicator_eq_eLpNorm_restrict Metric.isOpen_ball.measurableSet]
  exact hloc.eLpNorm_lt_top

-- BEGIN SA12.L6
theorem uloc_weak_compact (hd : 1 ≤ d) (χ : Euc d → ℝ) (hχ : IsUlocCutoff χ)
    (B t : ℝ) (hB0 : 0 ≤ B) (ht : 0 < t) (Fn : ℕ → ℝ → Euc d → ℝ)
    (hB : ∀ n, ∀ τ ∈ Icc (0 : ℝ) t, ulocNormE 0 χ (Fn n τ) ≤ ENNReal.ofReal B)
    (hequi : ∀ ψ : Euc d → ℝ, IsCcInfty ψ → ∃ K : ℝ, ∀ n,
      ∀ τ ∈ Icc (0 : ℝ) t, ∀ σ ∈ Icc (0 : ℝ) t,
      |(∫ x, Fn n τ x * ψ x) - ∫ x, Fn n σ x * ψ x| ≤ K * |τ - σ|) :
    ∃ (n : ℕ → ℕ) (G : ℝ → Euc d → ℝ), StrictMono n ∧
      (∀ τ ∈ Icc (0 : ℝ) t, AEStronglyMeasurable (G τ) volume ∧
        ulocNormE 0 χ (G τ) ≤ ENNReal.ofReal B) ∧
      ∀ ψ : Euc d → ℝ, IsCcInfty ψ → ∀ ε : ℝ, 0 < ε →
        ∀ᶠ k in atTop, ∀ τ ∈ Icc (0 : ℝ) t,
          |(∫ x, Fn (n k) τ x * ψ x) - ∫ x, G τ x * ψ x| ≤ ε := by
  classical
  obtain ⟨C, hC0, hC⟩ := weighted_l2_from_uloc hd χ hχ
  obtain ⟨e, he, hej⟩ := weighted_compact_tests_dense hd
  have hmem : ∀ n, ∀ τ ∈ Icc (0 : ℝ) t, MemLp (Fn n τ) 2 (compactMeasure d) :=
    fun n τ hτ => (hC _ B hB0 (hB n τ hτ)).1
  let U : ℕ → ℝ → CompactL2 d := fun n τ =>
    if h : τ ∈ Icc (0 : ℝ) t then (hmem n τ h).toLp (Fn n τ) else 0
  have hUb : ∀ n, ∀ τ ∈ Icc (0 : ℝ) t, ‖U n τ‖ ≤ C * B := by
    intro n τ hτ
    simp only [U, dif_pos hτ]
    rw [Lp.norm_toLp]
    exact ENNReal.toReal_le_of_le_ofReal (mul_nonneg hC0 hB0) (hC _ B hB0 (hB n τ hτ)).2
  have hUae : ∀ n, ∀ τ ∈ Icc (0 : ℝ) t, (U n τ : Euc d → ℝ) =ᵐ[volume] Fn n τ := by
    intro n τ hτ
    simp only [U, dif_pos hτ]
    exact sa12x_ae_vol (hmem n τ hτ).coeFn_toLp
  choose ψ hψ hψe using hej
  have hepsi : ∀ j, e j = (sa12x_test_memLp (hψ j).1.continuous (hψ j).2).toLp _ := by
    intro j
    exact Lp.ext ((hψe j).trans (MemLp.coeFn_toLp _).symm)
  have hpair : ∀ f : CompactL2 d, ∀ j, inner ℝ f (e j) = ∫ x, f x * ψ j x := by
    intro f j
    rw [hepsi j]
    exact sa12x_inner_test f (ψ := ψ j) (hψ j).1.continuous (hψ j).2
  have hUint : ∀ n, ∀ τ ∈ Icc (0 : ℝ) t, ∀ j, inner ℝ (U n τ) (e j) = ∫ x, Fn n τ x * ψ j x := by
    intro n τ hτ j
    rw [hpair]
    exact integral_congr_ae ((hUae n τ hτ).mono fun x hx => by simp only [hx])
  have hequi' : ∀ j, ∃ K : ℝ, ∀ n, ∀ τ ∈ Icc (0 : ℝ) t, ∀ σ ∈ Icc (0 : ℝ) t,
      |inner ℝ (U n τ - U n σ) (e j)| ≤ K * |τ - σ| := by
    intro j
    obtain ⟨K, hK⟩ := hequi (ψ j) (hψ j)
    refine ⟨K, fun n τ hτ σ hσ => ?_⟩
    rw [inner_sub_left, hUint n τ hτ j, hUint n σ hσ j]
    exact hK n τ hτ σ hσ
  obtain ⟨n, v, hn, hvb, hvc, hconv⟩ := hilbert_path_compact e he (C * B) t (mul_nonneg hC0 hB0) ht
    U hUb hequi'
  -- convergence of all compact tests
  have hlim : ∀ ψ' : Euc d → ℝ, IsCcInfty ψ' → ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, ∀ τ ∈ Icc (0 : ℝ) t,
      |(∫ x, Fn (n k) τ x * ψ' x) - ∫ x, (v τ : Euc d → ℝ) x * ψ' x| ≤ ε := by
    intro ψ' hψ' ε hε
    filter_upwards [hconv ((sa12x_test_memLp hψ'.1.continuous hψ'.2).toLp _) ε hε] with k hk τ hτ
    have h1 := hk τ hτ
    rw [inner_sub_left, sa12x_inner_test _ hψ'.1.continuous hψ'.2,
      sa12x_inner_test _ hψ'.1.continuous hψ'.2] at h1
    have h2 : ∫ x, U (n k) τ x * ψ' x = ∫ x, Fn (n k) τ x * ψ' x :=
      integral_congr_ae ((hUae (n k) τ hτ).mono fun x hx => by simp only [hx])
    rwa [h2] at h1
  refine ⟨n, fun τ => (v τ : Euc d → ℝ), hn, fun τ hτ => ⟨(Lp.stronglyMeasurable (v τ)).aestronglyMeasurable, ?_⟩, hlim⟩
  -- the uloc bound by lower semicontinuity
  refine iSup_le fun z => ?_
  have hmemG := sa12x_cut_memLp (v τ) hχ z
  rw [Nat.cast_zero, sobolevNormE_zero_eq hmemG]
  have hcz : Continuous fun x : Euc d => χ (x - z) :=
    hχ.1.continuous.comp (continuous_id.sub continuous_const)
  refine le_trans (sa12x_dual hmemG hB0 fun ψ' hψ' => ?_) le_rfl
  have hψ'' : IsCcInfty (fun x => χ (x - z) * ψ' x) :=
    ⟨(hχ.1.comp (contDiff_id.sub contDiff_const)).mul hψ'.1, hψ'.2.mul_left⟩
  have hT : Tendsto (fun k => ∫ x, Fn (n k) τ x * (χ (x - z) * ψ' x)) atTop
      (𝓝 (∫ x, (v τ : Euc d → ℝ) x * (χ (x - z) * ψ' x))) := by
    refine Metric.tendsto_nhds.2 fun ε hε => ?_
    filter_upwards [hlim _ hψ'' (ε / 2) (half_pos hε)] with k hk
    have := hk τ hτ
    rw [Real.dist_eq]; linarith
  have hbound : ∀ k, |∫ x, Fn (n k) τ x * (χ (x - z) * ψ' x)| ≤
      B * (eLpNorm ψ' 2 volume).toReal := by
    intro k
    have h0' : sobolevNormE ((0 : ℕ) : ℝ) (fun x => χ (x - z) * Fn (n k) τ x) ≤ ENNReal.ofReal B :=
      (le_iSup (fun z : Euc d => sobolevNormE ((0 : ℕ) : ℝ) fun x => χ (x - z) * Fn (n k) τ x) z).trans
        (hB (n k) τ hτ)
    rw [Nat.cast_zero] at h0'
    have h0 := h0'
    have hm : MemLp (fun x => χ (x - z) * Fn (n k) τ x) 2 volume :=
      sobolevNormE_zero_lt_top_iff.1 (h0.trans_lt ENNReal.ofReal_lt_top)
    rw [sobolevNormE_zero_eq hm] at h0
    have hψm : MemLp ψ' 2 volume := hψ'.1.continuous.memLp_of_hasCompactSupport hψ'.2
    have := sa12x_cs hm hψm
    have e1 : (fun x => Fn (n k) τ x * (χ (x - z) * ψ' x)) =
        fun x => (χ (x - z) * Fn (n k) τ x) * ψ' x := funext fun x => by ring
    rw [e1]
    refine this.trans (mul_le_mul_of_nonneg_right ?_ ENNReal.toReal_nonneg)
    exact ENNReal.toReal_le_of_le_ofReal hB0 h0
  have e2 : (fun x => (χ (x - z) * (v τ : Euc d → ℝ) x) * ψ' x) =
      fun x => (v τ : Euc d → ℝ) x * (χ (x - z) * ψ' x) := funext fun x => by ring
  rw [e2]
  exact le_of_tendsto hT.abs (Filter.Eventually.of_forall hbound)

end HRS.MH.AdjointRd.Phase2SA12Limit
