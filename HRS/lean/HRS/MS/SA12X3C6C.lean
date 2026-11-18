import HRS.MS.SA12X3C6B

/-!
# S.A.12 C6 (SA12X3), part C: localizing a bounded density

For `R ≥ 1` there is a smooth cutoff `ζ ≥ 0` with `ζ = 1` on `B̄(0,R)` and a constant `Λ''` such that for every
`μ ∈ C_b^{m+3}` with `cbNorm ≤ Λ` and every shift `q`, `ζ · μ(· + q)` is an `(m+3, Λ'')`-regular density
(weighted decay holds because of the compact support).
-/

set_option autoImplicit false
set_option maxHeartbeats 3200000

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped BigOperators ContDiff ENNReal

namespace HRS.MH.AdjointRd.Phase2SA12Construction

open HRS HRS.Whole HRS.MH.AdjointRd HRS.MH.AdjointRd.Phase2SA12

variable {d : ℕ}

theorem sa12x3_jets_bounded {f : Euc d → ℝ} (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) (k : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ j ≤ k, ∀ x, ‖iteratedFDeriv ℝ j f x‖ ≤ B := by
  have h : ∀ j : ℕ, ∃ Bj : ℝ, 0 ≤ Bj ∧ ∀ x, ‖iteratedFDeriv ℝ j f x‖ ≤ Bj := by
    intro j
    obtain ⟨C, hC⟩ := (hc.iteratedFDeriv (𝕜 := ℝ) j).exists_bound_of_continuous
      (hf.continuous_iteratedFDeriv (m := j) (sa12x2_le_top j))
    exact ⟨max C 0, le_max_right _ _, fun x => (hC x).trans (le_max_left _ _)⟩
  choose Bj hB0 hBj using h
  refine ⟨∑ j ∈ Finset.range (k + 1), Bj j, Finset.sum_nonneg fun j _ => hB0 j, fun j hj x => ?_⟩
  exact (hBj j x).trans (Finset.single_le_sum (f := Bj) (fun j _ => hB0 j)
    (Finset.mem_range.2 (Nat.lt_succ_of_le hj)))

theorem sa12x3_cutoff_density (m : ℕ) {R : ℝ} (hR : 1 ≤ R) (Λ : ℝ) :
    ∃ (ζ : Euc d → ℝ) (Λ'' : ℝ), 0 ≤ Λ'' ∧ ContDiff ℝ ∞ ζ ∧ (∀ x, 0 ≤ ζ x) ∧
      (∀ x ∈ closedBall (0 : Euc d) R, ζ x = 1) ∧
      ∀ (μ : Euc d → ℝ) (q : Euc d), MemCb (m + 3) μ → cbNorm (m + 3) μ ≤ Λ →
        IsRegularDensityW (m + 3) Λ'' (fun y => ζ y * μ (y + q)) := by
  let f : ContDiffBump (0 : Euc d) := ⟨R, R + 1, by linarith, by linarith⟩
  have hζ : ContDiff ℝ ∞ (⇑f) := f.contDiff
  have hζc : HasCompactSupport (⇑f) := f.hasCompactSupport
  obtain ⟨Bz, hBz0, hBz⟩ := sa12x3_jets_bounded hζ hζc (m + 3)
  set Λ0 : ℝ := max Λ 0 with hΛ0
  have hΛ00 : 0 ≤ Λ0 := le_max_right _ _
  set K : ℝ := 2 ^ (m + 3) * Bz * Λ0 with hK
  have hK0 : 0 ≤ K := by positivity
  set J : ℝ := Real.sqrt (1 + (R + 1) ^ 2) with hJ
  have hJ0 : 0 ≤ J := Real.sqrt_nonneg _
  refine ⟨⇑f, ((m + 3 : ℕ) + 1) * K + J ^ ((d : ℝ) + 3) * K, by positivity, hζ, fun x => f.nonneg,
    fun x hx => f.one_of_mem_closedBall (by simpa [f] using hx), ?_⟩
  intro μ q hμ hcb
  have hμB : ∀ j ≤ m + 3, ∀ x, ‖iteratedFDeriv ℝ j μ x‖ ≤ Λ0 := fun j hj x =>
    (sa12r35_single_le_cb hμ hj x).trans (hcb.trans (le_max_left _ _))
  have hg : ContDiff ℝ ((m + 3 : ℕ) : WithTop ℕ∞) (fun y => μ (y + q)) :=
    hμ.1.comp (contDiff_id.add contDiff_const)
  have hgB : ∀ j ≤ m + 3, ∀ x, ‖iteratedFDeriv ℝ j (fun y => μ (y + q)) x‖ ≤ Λ0 := by
    intro j hj x
    rw [iteratedFDeriv_comp_add_right]
    exact hμB j hj _
  have hρ : ContDiff ℝ ((m + 3 : ℕ) : WithTop ℕ∞) (fun y => f y * μ (y + q)) :=
    (hζ.of_le (sa12x2_le_top _)).mul hg
  have hρB : ∀ j ≤ m + 3, ∀ x, ‖iteratedFDeriv ℝ j (fun y => f y * μ (y + q)) x‖ ≤ K := by
    intro j hj x
    have h := sa12x2_jet_mul_bound (k := m + 3) (f := ⇑f) (g := fun y => μ (y + q)) (B := Bz) (C := Λ0)
      hBz0 hΛ00 (hζ.of_le (sa12x2_le_top _)) hg (fun j hj x => hBz j hj x) hgB j hj x
    refine h.trans ?_
    have : (2 : ℝ) ^ j ≤ 2 ^ (m + 3) := pow_le_pow_right₀ (by norm_num) hj
    rw [hK]
    gcongr
  have hsupp : tsupport (fun y => f y * μ (y + q)) ⊆ closedBall (0 : Euc d) (R + 1) := by
    have h1 : tsupport (fun y => f y * μ (y + q)) ⊆ tsupport (⇑f) := tsupport_mul_subset_left
    refine h1.trans ?_
    rw [f.tsupport_eq]
  refine ⟨hρ, ⟨hρ, fun j hj => ⟨K, ?_⟩⟩, ?_⟩
  · rintro _ ⟨x, rfl⟩
    exact hρB j hj x
  · -- the weighted bound
    have hcb' : cbNorm (m + 3) (fun y => f y * μ (y + q)) ≤ ((m + 3 : ℕ) + 1) * K := by
      unfold cbNorm
      have : ∀ j ∈ Finset.range (m + 3 + 1), (⨆ z : Euc d, ‖iteratedFDeriv ℝ j (fun y => f y * μ (y + q)) z‖) ≤ K := by
        intro j hj
        exact ciSup_le fun z => hρB j (by simpa [Nat.lt_succ_iff] using hj) z
      calc _ ≤ ∑ j ∈ Finset.range (m + 3 + 1), K := Finset.sum_le_sum this
        _ = ((m + 3 : ℕ) + 1) * K := by simp
    have hws : weightedSupE (m + 3) ((d : ℝ) + 3) (fun y => f y * μ (y + q)) ≤
        ENNReal.ofReal (J ^ ((d : ℝ) + 3) * K) := by
      unfold weightedSupE derivSupE
      refine iSup_le fun j => iSup_le fun idx => iSup_le fun x => ?_
      apply ENNReal.ofReal_le_ofReal
      by_cases hx : x ∈ closedBall (0 : Euc d) (R + 1)
      · have hjb : jbracket x ≤ J := by
          unfold jbracket
          apply Real.sqrt_le_sqrt
          have : ‖x‖ ≤ R + 1 := by simpa using hx
          have h0 : 0 ≤ ‖x‖ := norm_nonneg _
          nlinarith
        have hjb0 : 0 ≤ jbracket x := Real.sqrt_nonneg _
        have hp : |partialDeriv idx (fun y => f y * μ (y + q)) x| ≤ K :=
          (sa12x2_pd_le_norm _ idx x).trans (hρB j (Nat.lt_succ_iff.mp j.isLt) x)
        show jbracket x ^ ((d : ℝ) + 3) * _ ≤ _
        exact mul_le_mul (Real.rpow_le_rpow hjb0 hjb (by positivity)) hp (abs_nonneg _)
          (Real.rpow_nonneg hJ0 _)
      · have h0 : partialDeriv idx (fun y => f y * μ (y + q)) x = 0 :=
          sa12x2_pd_zero_gen hsupp idx hx
        show jbracket x ^ ((d : ℝ) + 3) * |partialDeriv idx (fun y => f y * μ (y + q)) x| ≤ _
        rw [h0]
        simp only [abs_zero, mul_zero]
        positivity
    calc ENNReal.ofReal (cbNorm (m + 3) (fun y => f y * μ (y + q))) +
          weightedSupE (m + 3) ((d : ℝ) + 3) (fun y => f y * μ (y + q))
        ≤ ENNReal.ofReal (((m + 3 : ℕ) + 1) * K) + ENNReal.ofReal (J ^ ((d : ℝ) + 3) * K) :=
          add_le_add (ENNReal.ofReal_le_ofReal hcb') hws
      _ = ENNReal.ofReal (((m + 3 : ℕ) + 1) * K + J ^ ((d : ℝ) + 3) * K) := by
          rw [ENNReal.ofReal_add (by positivity) (by positivity)]

end HRS.MH.AdjointRd.Phase2SA12Construction
