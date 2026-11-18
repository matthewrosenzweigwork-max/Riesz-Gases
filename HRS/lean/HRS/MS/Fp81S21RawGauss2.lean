import HRS.MS.Fp81S21GaussFeature3

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Classical
open scoped ENNReal NNReal BigOperators RealInnerProductSpace

namespace HRS.Fp81.S21

open HRS.Whole
open HRS.MS.R26T3 HRS.MS.ProClosureS111

private theorem fp81s21_series_lp_tendsto
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (e : ℕ → GaussianFeatureHilbert) (ξ : ℕ → Ω → ℝ)
    (W : GaussianFeatureHilbert → Ω → ℝ)
    (hstd : HRS.IsStdGaussianSeq P ξ)
    (hW2 : ∀ h, MemLp (W h) 2 P)
    (hWlim : ∀ h, Tendsto (fun m : ℕ =>
      ∫ ω, (s21g2_s11a_S ξ (fun n => inner ℝ (e n) h) m ω - W h ω) ^ 2 ∂P)
        atTop (𝓝 0))
    (h : GaussianFeatureHilbert) :
    Tendsto (fun n => (s21g2_s11a_memLp
      (fun i => ⟨hstd.aemeasurable i,
        by simpa [HRS.IsStdGaussianSeq, law] using hstd.2 i⟩)
      (fun j => inner ℝ (e j) h) n).toLp
        (s21g2_s11a_S ξ (fun j => inner ℝ (e j) h) n)) atTop
      (𝓝 ((hW2 h).toLp (W h))) := by
  have hξlaw : ∀ i, HasLaw (ξ i) (gaussianReal 0 1) P := by
    intro i
    exact ⟨hstd.aemeasurable i,
      by simpa [HRS.IsStdGaussianSeq, law] using hstd.2 i⟩
  have hmem : ∀ n, MemLp (s21g2_s11a_S ξ
      (fun j => inner ℝ (e j) h) n) 2 P :=
    s21g2_s11a_memLp hξlaw _
  have hT : HRS.TendstoL2 P
      (s21g2_s11a_S ξ (fun j => inner ℝ (e j) h)) (W h) :=
    HRS.tendstoL2_of_memLp (hW2 h) hmem (hWlim h)
  have hnorm := hT.tendsto_eLpNorm (fun n => (hmem n).aestronglyMeasurable)
  exact (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' (fi := atTop)
    (s21g2_s11a_S ξ (fun j => inner ℝ (e j) h)) hmem (W h) (hW2 h)).2 hnorm

theorem fp81s21_series_linear
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (e : ℕ → GaussianFeatureHilbert) (ξ : ℕ → Ω → ℝ)
    (W : GaussianFeatureHilbert → Ω → ℝ)
    (hstd : HRS.IsStdGaussianSeq P ξ)
    (hW2 : ∀ h, MemLp (W h) 2 P)
    (hWlim : ∀ h, Tendsto (fun m : ℕ =>
      ∫ ω, (s21g2_s11a_S ξ (fun n => inner ℝ (e n) h) m ω - W h ω) ^ 2 ∂P)
        atTop (𝓝 0))
    (h k : GaussianFeatureHilbert) (c : ℝ) :
    W (h + c • k) =ᵐ[P] fun ω => W h ω + c * W k ω := by
  have hξlaw : ∀ i, HasLaw (ξ i) (gaussianReal 0 1) P := by
    intro i
    exact ⟨hstd.aemeasurable i,
      by simpa [HRS.IsStdGaussianSeq, law] using hstd.2 i⟩
  let a : ℕ → ℝ := fun j => inner ℝ (e j) h
  let b : ℕ → ℝ := fun j => inner ℝ (e j) k
  let d : ℕ → ℝ := fun j => inner ℝ (e j) (h + c • k)
  have hmemA : ∀ n, MemLp (s21g2_s11a_S ξ a n) 2 P :=
    s21g2_s11a_memLp hξlaw a
  have hmemB : ∀ n, MemLp (s21g2_s11a_S ξ b n) 2 P :=
    s21g2_s11a_memLp hξlaw b
  have hmemD : ∀ n, MemLp (s21g2_s11a_S ξ d n) 2 P :=
    s21g2_s11a_memLp hξlaw d
  have hseq : ∀ n,
      (hmemD n).toLp (s21g2_s11a_S ξ d n) =
        (hmemA n).toLp (s21g2_s11a_S ξ a n) +
          c • (hmemB n).toLp (s21g2_s11a_S ξ b n) := by
    intro n
    apply Lp.ext
    have hp : ∀ ω, s21g2_s11a_S ξ d n ω =
        s21g2_s11a_S ξ a n ω + c * s21g2_s11a_S ξ b n ω := by
      intro ω
      simp [s21g2_s11a_S, a, b, d, inner_add_right, real_inner_smul_right,
        Finset.sum_add_distrib, add_mul, Finset.mul_sum, mul_assoc]
    filter_upwards [(hmemD n).coeFn_toLp, (hmemA n).coeFn_toLp,
      (hmemB n).coeFn_toLp,
      Lp.coeFn_add ((hmemA n).toLp _) (c • (hmemB n).toLp _),
      Lp.coeFn_smul c ((hmemB n).toLp _)] with ω hd ha hb hadd hsmul
    calc
      ((hmemD n).toLp (s21g2_s11a_S ξ d n) : Ω → ℝ) ω =
          s21g2_s11a_S ξ d n ω := hd
      _ = s21g2_s11a_S ξ a n ω + c * s21g2_s11a_S ξ b n ω := hp ω
      _ = ((hmemA n).toLp (s21g2_s11a_S ξ a n) +
          c • (hmemB n).toLp (s21g2_s11a_S ξ b n) : Lp ℝ 2 P) ω := by
        rw [← ha, ← hb, hadd, Pi.add_apply, hsmul, Pi.smul_apply, smul_eq_mul]
  have hlimD := fp81s21_series_lp_tendsto e ξ W hstd hW2 hWlim (h + c • k)
  have hlimA := fp81s21_series_lp_tendsto e ξ W hstd hW2 hWlim h
  have hlimB := fp81s21_series_lp_tendsto e ξ W hstd hW2 hWlim k
  have hlimAB : Tendsto
      (fun n => (hmemA n).toLp (s21g2_s11a_S ξ a n) +
        c • (hmemB n).toLp (s21g2_s11a_S ξ b n)) atTop
      (𝓝 ((hW2 h).toLp (W h) + c • (hW2 k).toLp (W k))) :=
    hlimA.add (hlimB.const_smul c)
  have hlimD' : Tendsto (fun n => (hmemD n).toLp (s21g2_s11a_S ξ d n)) atTop
      (𝓝 ((hW2 h).toLp (W h) + c • (hW2 k).toLp (W k))) := by
    refine Tendsto.congr' ?_ hlimAB
    exact Filter.Eventually.of_forall fun n => (hseq n).symm
  have hEq := tendsto_nhds_unique hlimD hlimD'
  have hAE : W (h + c • k) =ᵐ[P] fun ω => W h ω + c * W k ω := by
    filter_upwards [Lp.ext_iff.mp hEq,
      (hW2 (h + c • k)).coeFn_toLp, (hW2 h).coeFn_toLp,
      (hW2 k).coeFn_toLp,
      Lp.coeFn_add ((hW2 h).toLp (W h)) (c • (hW2 k).toLp (W k)),
      Lp.coeFn_smul c ((hW2 k).toLp (W k))] with ω hEq hD hA hB hadd hsmul
    calc
      W (h + c • k) ω = ((hW2 (h + c • k)).toLp (W (h + c • k)) : Ω → ℝ) ω := hD.symm
      _ = ((hW2 h).toLp (W h) + c • (hW2 k).toLp (W k) : Lp ℝ 2 P) ω := hEq
      _ = W h ω + c * W k ω := by
        rw [hadd, Pi.add_apply, hsmul, Pi.smul_apply, smul_eq_mul, hA, hB]
  filter_upwards [hAE] with ω hω
  exact hω

theorem fp81s21_series_distance
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (e : ℕ → GaussianFeatureHilbert) (ξ : ℕ → Ω → ℝ)
    (W : GaussianFeatureHilbert → Ω → ℝ)
    (hParseval : ∀ h h' : GaussianFeatureHilbert,
      HasSum (fun n => inner ℝ (e n) h * inner ℝ (e n) h') (inner ℝ h h'))
    (hstd : HRS.IsStdGaussianSeq P ξ)
    (hW2 : ∀ h, MemLp (W h) 2 P)
    (hWlim : ∀ h, Tendsto (fun m : ℕ =>
      ∫ ω, (s21g2_s11a_S ξ (fun n => inner ℝ (e n) h) m ω - W h ω) ^ 2 ∂P)
        atTop (𝓝 0))
    (h k : GaussianFeatureHilbert) :
    (∫ ω, (W h ω - W k ω) ^ 2 ∂P) = ‖h - k‖ ^ 2 := by
  have hξlaw : ∀ i, HasLaw (ξ i) (gaussianReal 0 1) P := by
    intro i
    exact ⟨hstd.aemeasurable i,
      by simpa [HRS.IsStdGaussianSeq, law] using hstd.2 i⟩
  let a : ℕ → ℝ := fun j => inner ℝ (e j) (h - k)
  have hasum : Summable (fun j => a j ^ 2) := by
    simpa [a, sq] using (hParseval (h - k) (h - k)).summable
  have hvar : (∑' j, a j ^ 2) = ‖h - k‖ ^ 2 := by
    have ht := (hParseval (h - k) (h - k)).tsum_eq
    simpa [a, sq, real_inner_self_eq_norm_sq] using ht
  have hlaw := s21g2_s11a_law hξlaw hstd.1 a hasum
    (hW2 (h - k)) (hWlim (h - k))
  have hsecond := s21g2_s11a_second (hW2 (h - k)).aemeasurable hlaw
  have hsum0 : 0 ≤ ∑' j, a j ^ 2 := tsum_nonneg fun _ => sq_nonneg _
  have hae := fp81s21_series_linear e ξ W hstd hW2 hWlim h k (-1)
  have hlin : W (h - k) =ᵐ[P] fun ω => W h ω - W k ω := by
    simpa [sub_eq_add_neg, neg_smul, smul_eq_mul] using hae
  calc
    _ = ∫ ω, W (h - k) ω ^ 2 ∂P := by
      refine integral_congr_ae ?_
      filter_upwards [hlin] with ω hω
      rw [hω]
    _ = ‖h - k‖ ^ 2 := by
      rw [hsecond, Real.coe_toNNReal _ hsum0, hvar]

#print axioms fp81s21_series_linear
#print axioms fp81s21_series_distance

end HRS.Fp81.S21

end
