import HRS.Sections.AdjKEAux8

/-!
# ADJKE part 9: continuity in time of the statistic coordinates and of the forcing

* `adjke_continuousOn_of_lip`: a locally Lipschitz function is continuous on `[0,T]`.
* `adjke_lhs_continuousOn`: along a continuous path, `t ↦ η_N^t(e_k)` is continuous on `[0,T]`.
-/

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.AdjK

open HRS HRS.Uniform HRS.GF HRS.Uniform.Q54c

variable {d : ℕ} {s β : ℝ} {V ρ₀ : Torus d → ℝ} {ρ : ℝ → Torus d → ℝ}

theorem adjke_Icc_subset_closure_rat {T : ℝ} (hT : 0 ≤ T) : Set.Icc (0 : ℝ) T ⊆ closure (ratIcc 0 T) := by
  rcases hT.eq_or_lt with h0 | hpos
  · intro x hx
    have : x = 0 := by rw [← h0] at hx; exact le_antisymm hx.2 hx.1
    subst this
    exact subset_closure ⟨⟨le_rfl, hT⟩, ⟨0, by simp⟩⟩
  · rw [← closure_Ioo hpos.ne]
    refine closure_minimal ?_ isClosed_closure
    intro x hx
    have h1 := (Rat.denseRange_cast (𝕜 := ℝ)).open_subset_closure_inter isOpen_Ioo hx
    refine closure_mono ?_ h1
    rintro y ⟨hy1, ⟨q, hq'⟩⟩
    exact ⟨⟨hy1.1.le, hy1.2.le⟩, ⟨q, hq'⟩⟩

theorem adjke_continuousOn_of_lip (f : ℝ → ℝ) (T Lc : ℝ)
    (h : ∀ t' t : ℝ, 0 ≤ t' → t' ≤ t → t ≤ T → t - t' ≤ 1 → |f t - f t'| ≤ Lc * (t - t')) :
    ContinuousOn f (Set.Icc 0 T) := by
  intro t0 ht0
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  have hL : 0 < |Lc| + 1 := by positivity
  refine ⟨min 1 (ε / (|Lc| + 1)), lt_min one_pos (div_pos hε hL), fun t ht hd => ?_⟩
  rw [Real.dist_eq] at hd ⊢
  have hd1 : |t - t0| < 1 := hd.trans_le (min_le_left _ _)
  have hd2 : |t - t0| < ε / (|Lc| + 1) := hd.trans_le (min_le_right _ _)
  have hbound : |f t - f t0| ≤ Lc * |t - t0| := by
    rcases le_total t0 t with hle | hle
    · have := h t0 t ht0.1 hle ht.2 (by rw [abs_of_nonneg (sub_nonneg.2 hle)] at hd1; linarith)
      rwa [abs_of_nonneg (sub_nonneg.2 hle)]
    · have := h t t0 ht.1 hle ht0.2 (by rw [abs_of_nonpos (sub_nonpos.2 hle)] at hd1; linarith)
      rw [abs_of_nonpos (sub_nonpos.2 hle), abs_sub_comm]
      calc |f t0 - f t| ≤ Lc * (t0 - t) := this
        _ = Lc * -(t - t0) := by ring
  calc |f t - f t0| ≤ Lc * |t - t0| := hbound
    _ ≤ |Lc| * |t - t0| := mul_le_mul_of_nonneg_right (le_abs_self Lc) (abs_nonneg _)
    _ ≤ (|Lc| + 1) * |t - t0| := mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg _)
    _ < (|Lc| + 1) * (ε / (|Lc| + 1)) := mul_lt_mul_of_pos_left hd2 hL
    _ = ε := by field_simp

theorem adjke_lhs_continuousOn (hd : 2 ≤ d) (htr : IsSmoothPositiveTrajectory d s β V ρ₀ ρ)
    {m : ℝ} (hm : (d : ℝ) / 2 + 2 < m) (T : ℝ) {N : ℕ} (hN : 0 < N) (Xp : ℝ≥0 → Config d N)
    (hXc : ∀ i, Continuous fun u : ℝ≥0 => Xp u i) (k : NonzeroLattice d) :
    ContinuousOn (fun t : ℝ => NegSobolev.fourierCoeff
      (etaE m (Xp t.toNNReal) (withDensityReal (ρ t))) k) (Set.Icc 0 T) := by
  classical
  have hd1 : 1 ≤ d := by omega
  have hm2 : (d : ℝ) < 2 * m := by
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  set φ : Torus d → ℝ := Torus.realMode k with hφdef
  have hφ : Torus.IsSmooth φ := HRS.FieldSingAux.isSmooth_realMode k
  obtain ⟨hφ2, hφm⟩ := gf_smooth_mem_proof hφ m
  have hφc : Continuous φ := Q54c.isCk_continuous hφ2
  have hφs := gfb2_summable_of_memSobolev hm2 hφm
  obtain ⟨c₀, hc₀, Λρ, hρbd⟩ := Q40b.q40b_rho_bounds hd1 htr
  have hjc := Q40b.q40b_jointCont hd1 htr T
  obtain ⟨Λ, hΛ⟩ := (isCompact_Icc.prod isCompact_univ).exists_bound_of_continuousOn hjc
  obtain ⟨Bφ, hBφ⟩ := Q40b.q40b_bdd hφc
  -- the pairing with the density is continuous in time
  have hpair : ContinuousOn (fun t : ℝ => pair (withDensityReal (ρ t)) φ) (Set.Icc 0 T) := by
    have hcongr : ∀ t ∈ Set.Icc (0 : ℝ) T, pair (withDensityReal (ρ t)) φ = ∫ x, ρ t x * φ x := by
      intro t ht
      unfold pair
      exact PDE.MFPairing.integral_withDensityReal (hρbd t ht.1).1.measurable (hρbd t ht.1).1.nonneg φ
    refine ContinuousOn.congr ?_ hcongr
    have hρt : ∀ t ∈ Set.Icc (0 : ℝ) T, Continuous (ρ t) := by
      intro t ht
      exact ContinuousOn.comp_continuous (f := fun x : Torus d => (t, x)) hjc (by fun_prop)
        (fun x => ⟨ht, Set.mem_univ x⟩)
    refine continuousOn_of_dominated (bound := fun _ => Λ * Bφ) ?_ ?_ (integrable_const _) ?_
    · intro t ht
      exact ((hρt t ht).mul hφc).aestronglyMeasurable
    · intro t ht
      refine Eventually.of_forall fun x => ?_
      rw [Real.norm_eq_abs, abs_mul]
      have h1 : |ρ t x| ≤ Λ := by
        have := hΛ (t, x) ⟨ht, Set.mem_univ _⟩
        simpa using this
      exact mul_le_mul h1 (hBφ x) (abs_nonneg _) ((abs_nonneg _).trans h1)
    · refine Eventually.of_forall fun x => ?_
      have : ContinuousOn (fun t : ℝ => ρ t x) (Set.Icc 0 T) :=
        ContinuousOn.comp (f := fun t : ℝ => (t, x)) hjc (by fun_prop) (fun t ht => ⟨ht, Set.mem_univ x⟩)
      exact this.mul continuousOn_const
  -- the statistic
  have hXi : ∀ i, Continuous fun t : ℝ => Xp t.toNNReal i := fun i =>
    (hXc i).comp continuous_real_toNNReal
  have hstat : Continuous fun t : ℝ => (1 / (N : ℝ)) * ∑ i, φ (Xp t.toNNReal i) :=
    continuous_const.mul (continuous_finset_sum _ fun i _ => hφc.comp (hXi i))
  have hcont : ContinuousOn (fun t : ℝ => linCoord (withDensityReal (ρ t)) φ (Xp t.toNNReal))
      (Set.Icc 0 T) := by
    unfold linCoord
    exact continuousOn_const.mul (hstat.continuousOn.sub hpair)
  refine hcont.congr fun t ht => ?_
  haveI : IsProbabilityMeasure (withDensityReal (ρ t)) := isProb_withDensityReal (hρbd t ht.1).1
  rw [← adjke_eval_realMode]
  exact adjke_eval_etaE hm2 hN _ _ φ hφc hφs

end HRS.AdjK
