import HRS.MS.R2GenInitAux17
import HRS.MS.R2WinErrAux12
import HRS.MS.SuppU11Aux1

/-!
# S10.5 window comparison, packet B4: the window feature is a genuine element of `𝒦_T` (no junk values)

`s105_winK`: from the orbit bounds of S10.3 (the hypotheses of `s104_window_feature`) the coordinate arrays of the three slots of the window feature
`r2WindowFeature` are in `ℓ²` and the middle slot is in `L²([0,T];ℓ²)`, so that `r2WindowFeature = KSpace.mk (ellVec A₀) (toLp f) (ellVec B)`
(the window analogue of `IsOrbitFeatureK`).
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R2GenInit

open HRS HRS.Whole HRS.MS.Go HRS.MS.R2WinErr

variable {d : ℕ}

theorem s105_b_le_one (α : MultiIndex d) : s104_b d α ≤ 1 := by
  unfold s104_b
  refine Real.rpow_le_one_of_one_le_of_nonpos (oscEv_one_le α) ?_
  have h1 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  push_cast
  nlinarith

theorem s105_memℓp_of_bound {c : MultiIndex d → ℝ} {K : ℝ} (hbd : ∀ α, |c α| ≤ K * s104_b d α)
    (hbS : Summable (s104_b d)) : Memℓp c 2 := by
  have hsq : Summable fun α => c α ^ 2 := by
    refine Summable.of_nonneg_of_le (fun α => sq_nonneg _) (fun α => ?_) (hbS.mul_left (K ^ 2))
    calc c α ^ 2 = |c α| ^ 2 := (sq_abs _).symm
      _ ≤ (K * s104_b d α) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (hbd α) 2
      _ = K ^ 2 * (s104_b d α) ^ 2 := by ring
      _ ≤ K ^ 2 * s104_b d α := by
          refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
          have := s104_b_nonneg (d := d) α
          have := s105_b_le_one (d := d) α
          nlinarith
  exact (memℓp_gen_iff (p := (2 : ENNReal)) (by norm_num)).2 (by simpa using hsq)

theorem s105_sq_sum_le {c : MultiIndex d → ℝ} {K : ℝ} (hK : 0 ≤ K) (hbd : ∀ α, |c α| ≤ K * s104_b d α)
    (hbS : Summable (s104_b d)) :
    ∑' α, c α ^ 2 ≤ (K * Real.sqrt (∑' α, s104_b d α)) ^ 2 := by
  have hsq : Summable fun α => c α ^ 2 := by
    have := s105_memℓp_of_bound hbd hbS
    simpa using (memℓp_gen_iff (p := (2 : ENNReal)) (by norm_num)).1 this
  rw [mul_pow, Real.sq_sqrt (tsum_nonneg fun α => s104_b_nonneg α)]
  calc ∑' α, c α ^ 2 ≤ ∑' α, K ^ 2 * s104_b d α := by
        refine hsq.tsum_le_tsum (fun α => ?_) (hbS.mul_left _)
        calc c α ^ 2 = |c α| ^ 2 := (sq_abs _).symm
          _ ≤ (K * s104_b d α) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (hbd α) 2
          _ = K ^ 2 * (s104_b d α) ^ 2 := by ring
          _ ≤ K ^ 2 * s104_b d α := by
              refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
              have := s104_b_nonneg (d := d) α
              have := s105_b_le_one (d := d) α
              nlinarith
    _ = K ^ 2 * ∑' α, s104_b d α := tsum_mul_left

theorem s105_winK (C : WholeCoeff d) (k : ℕ) (m T cdec Cs : ℝ) (hcd : 0 ≤ cdec) (hCs : 0 ≤ Cs)
    (hbS : Summable (s104_b d))
    (hG : ∀ α, ∀ t : ℝ, 0 ≤ t → R2OrbitGrad C k t (oscTestFun m α) (Cs * s104_b d α) cdec)
    (hG' : ∀ α, ∀ t : ℝ, 0 ≤ t → R2OrbitGrad C k t (generatorW C t (oscTestFun m α)) (Cs * s104_b d α) cdec)
    (hφ : ∀ α a, ContDiff ℝ k (fun x => gradComp a (oscTestFun m α) x) ∧ ∀ j ≤ k, ∀ x,
      ‖iteratedFDeriv ℝ j (fun x => gradComp a (oscTestFun m α) x) x‖ ≤ Cs * s104_b d α)
    {b r : ℝ} (hb : 0 ≤ b) (hr0 : 0 ≤ r) (a : Fin d)
    (hmeasU : ∀ α x, AEStronglyMeasurable (fun u => if r < b + u then gradComp a (propagatorW C r (b + u)
      (generatorW C (b + u) (oscTestFun m α))) x else 0) (volume.restrict (Set.Icc (0 : ℝ) T))) (x : Euc d) :
    Memℓp (fun α => gradComp a (propagatorW C r (max b r) (oscTestFun m α)) x) 2 ∧
    Memℓp (fun α => if b ≤ r then gradComp a (oscTestFun m α) x else 0) 2 ∧
    (∀ u ∈ Set.Icc (0 : ℝ) T, r < b + u → Memℓp (fun α => gradComp a (propagatorW C r (b + u)
      (generatorW C (b + u) (oscTestFun m α))) x) 2) ∧
    MemLp (fun u : ℝ => if r < b + u then ellVec (d := d) m (fun α => gradComp a (propagatorW C r (b + u)
      (generatorW C (b + u) (oscTestFun m α))) x) else 0) 2 (volume.restrict (Set.Icc (0 : ℝ) T)) := by
  have hCsb : ∀ α, 0 ≤ Cs * s104_b d α := fun α => mul_nonneg hCs (s104_b_nonneg α)
  have hexp : ∀ t r' : ℝ, r' ≤ t → Real.exp (-cdec * (t - r')) ≤ 1 := fun t r' h => by
    rw [Real.exp_le_one_iff]; nlinarith
  -- coordinate bounds
  have hA0 : ∀ α, |gradComp a (propagatorW C r (max b r) (oscTestFun m α)) x| ≤ Cs * s104_b d α := by
    intro α
    obtain ⟨-, h2⟩ := s104_gradComp_bound C (hCsb α) (hG α (max b r) (by positivity)) (r := r)
      ⟨hr0, le_max_right _ _⟩ a
    have := h2 0 (Nat.zero_le _) x
    rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at this
    exact this.trans (mul_le_of_le_one_right (hCsb α) (hexp _ _ (le_max_right _ _)))
  have hB0 : ∀ α, |if b ≤ r then gradComp a (oscTestFun m α) x else 0| ≤ Cs * s104_b d α := by
    intro α
    split_ifs
    · have := (hφ α a).2 0 (Nat.zero_le _) x
      rwa [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at this
    · simpa using hCsb α
  have hV0 : ∀ u : ℝ, 0 ≤ u → ∀ α, |if r < b + u then gradComp a (propagatorW C r (b + u)
      (generatorW C (b + u) (oscTestFun m α))) x else 0| ≤ Cs * s104_b d α := by
    intro u hu α
    split_ifs with h
    · obtain ⟨-, h2⟩ := s104_gradComp_bound C (hCsb α) (hG' α (b + u) (by linarith)) (r := r)
        ⟨hr0, h.le⟩ a
      have := h2 0 (Nat.zero_le _) x
      rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at this
      exact this.trans (mul_le_of_le_one_right (hCsb α) (hexp _ _ h.le))
    · simpa using hCsb α
  refine ⟨s105_memℓp_of_bound hA0 hbS, s105_memℓp_of_bound hB0 hbS, ?_, ?_⟩
  · intro u hu hru
    refine s105_memℓp_of_bound (K := Cs) (fun α => ?_) hbS
    have := hV0 u hu.1 α
    rwa [if_pos hru] at this
  · set μ : Measure ℝ := volume.restrict (Set.Icc (0 : ℝ) T) with hμ
    set Bs : ℝ := Cs * Real.sqrt (∑' α, s104_b d α) with hBs
    have hBs0 : 0 ≤ Bs := by positivity
    set v : MultiIndex d → ℝ → ℝ := fun α u => if u ∈ Set.Icc (0 : ℝ) T then
      (if r < b + u then gradComp a (propagatorW C r (b + u)
        (generatorW C (b + u) (oscTestFun m α))) x else 0) else 0 with hv
    have hvb : ∀ u α, |v α u| ≤ Cs * s104_b d α := by
      intro u α
      by_cases hu : u ∈ Set.Icc (0 : ℝ) T
      · simp only [hv, if_pos hu]; exact hV0 u hu.1 α
      · simp only [hv, if_neg hu]; simpa using hCsb α
    have hvsum : ∀ u, Summable fun α => |v α u| := fun u =>
      Summable.of_nonneg_of_le (fun α => abs_nonneg _) (fun α => hvb u α) (hbS.mul_left Cs)
    have hvmeas : ∀ α, AEStronglyMeasurable (v α) μ := by
      intro α
      have e : v α = (Set.Icc (0 : ℝ) T).indicator (fun u => if r < b + u then
          gradComp a (propagatorW C r (b + u) (generatorW C (b + u) (oscTestFun m α))) x else 0) := by
        funext u
        by_cases h : u ∈ Set.Icc (0 : ℝ) T
        · simp only [hv]; rw [if_pos h, Set.indicator_of_mem h]
        · simp only [hv]; rw [if_neg h, Set.indicator_of_notMem h]
      rw [e, aestronglyMeasurable_indicator_iff measurableSet_Icc]
      exact (hmeasU α x).mono_measure (Measure.restrict_le_self)
    have hFm : AEStronglyMeasurable (fun u => ellVec (d := d) m (fun α => v α u)) μ :=
      s55f_aesm_ellVec (m := m) v hvmeas hvsum
    have hFb : ∀ u, ‖ellVec (d := d) m (fun α => v α u)‖ ≤ Bs := fun u =>
      u11_norm_ellVec_le m _ (s105_memℓp_of_bound (K := Cs) (hvb u) hbS) hBs0
        (s105_sq_sum_le hCs (hvb u) hbS)
    have hF : MemLp (fun u => ellVec (d := d) m (fun α => v α u)) 2 μ := s55f_memLp_of_bound μ hFm (B := Bs) hFb
    refine hF.ae_eq ?_
    refine (ae_restrict_iff' measurableSet_Icc).2 (Filter.Eventually.of_forall fun u hu => ?_)
    by_cases hru : r < b + u
    · simp only [hv, hu, if_true, hru]
    · simp only [hv, hu, if_true, hru, if_false]
      exact s55f_ellVec_zero m

end HRS.MS.R2GenInit
