import HRS.MS.Ker1Aux6
import HRS.MH.AdjointRdDefs

/-!
# S.A.12 C19: derivative bounds of the periodic Riesz kernel on the whole cube `[-L/2, L/2]^d`
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MH.AdjointRd.Phase2SA12Construction

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas

variable {d : ℕ}

/-- The corner region of the unit-scale cube is compact and avoids the lattice. -/
theorem sa12c19_corner_compact :
    IsCompact {y : Euc d | (∀ i, |y i| ≤ 1 / 2) ∧ 1 / 2 ≤ ‖y‖} := by
  have hsub : {y : Euc d | (∀ i, |y i| ≤ 1 / 2) ∧ 1 / 2 ≤ ‖y‖} ⊆
      Metric.closedBall (0 : Euc d) (Real.sqrt (d * (1 / 2) ^ 2)) := by
    intro y hy
    rw [Metric.mem_closedBall, dist_zero_right, EuclideanSpace.norm_eq]
    refine Real.sqrt_le_sqrt ?_
    calc ∑ i, ‖y i‖ ^ 2 ≤ ∑ _i : Fin d, (1 / 2 : ℝ) ^ 2 := by
          refine Finset.sum_le_sum fun i _ => ?_
          rw [Real.norm_eq_abs]
          exact pow_le_pow_left₀ (abs_nonneg _) (hy.1 i) 2
      _ = d * (1 / 2) ^ 2 := by simp
  refine (isCompact_closedBall (0 : Euc d) _).of_isClosed_subset ?_ hsub
  have hproj : ∀ i : Fin d, Continuous fun y : Euc d => y i := fun i =>
    (EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).continuous
  have : {y : Euc d | (∀ i, |y i| ≤ 1 / 2) ∧ 1 / 2 ≤ ‖y‖} =
      (⋂ i, {y : Euc d | |y i| ≤ 1 / 2}) ∩ {y : Euc d | 1 / 2 ≤ ‖y‖} := by
    ext y; simp
  rw [this]
  exact (isClosed_iInter fun i => isClosed_le ((hproj i).abs) continuous_const).inter
    (isClosed_le continuous_const continuous_norm)

theorem sa12c19_corner_offLattice {y : Euc d} (hy : ∀ i, |y i| ≤ 1 / 2) (hn : 1 / 2 ≤ ‖y‖) :
    Torus.mk y ≠ 0 := by
  intro h
  obtain ⟨n, hn'⟩ := HRS.MS.Ker1.ker1_mk_eq_zero h
  have hzero : ∀ i, n i = 0 := by
    intro i
    have h1 := hy i
    rw [hn'] at h1
    simp only [Lattice.toEuc, abs_le] at h1
    have h2 : (n i : ℝ) < 1 := by linarith [h1.2]
    have h3 : (-1 : ℝ) < n i := by linarith [h1.1]
    have h4 : n i < 1 := by exact_mod_cast h2
    have h5 : -1 < n i := by exact_mod_cast h3
    omega
  have : y = 0 := by
    rw [hn']
    ext i
    simp [Lattice.toEuc, hzero i]
  rw [this] at hn
  simp at hn
  linarith

-- BEGIN SA12.C19
theorem periodic_kernel_cube (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ L : ℝ, 1 ≤ L → ∀ γ : Euc d → ℝ,
      HRS.Whole.AppendixALemmas.IsPeriodicRieszKernel d s L γ →
      ∀ n : ℕ, n ≤ m + 2 → 0 < (n : ℝ) + s → ∀ u : Euc d, u ≠ 0 → (∀ i, |u i| ≤ L / 2) →
        ‖iteratedFDeriv ℝ n γ u‖ ≤ C * (‖u‖ ^ (-s - n) + (if 0 < s then L ^ (-s - n) else 0) +
          (if s = 0 then L ^ (-(n : ℝ)) else 0)) := by
  -- constants for each order
  have hex : ∀ n : ℕ, ∃ C : ℝ, 0 ≤ C ∧ (0 < (n : ℝ) + s →
      (∀ L : ℝ, 0 < L → ∀ x : Euc d, x ≠ 0 → ‖x‖ ≤ L / 2 →
        ‖iteratedFDeriv ℝ n (HRS.MS.Ker1.ker1_gam d s L) x‖ ≤ C * ‖x‖ ^ (-s - n)) ∧
      (∀ y : Euc d, (∀ i, |y i| ≤ 1 / 2) → 1 / 2 ≤ ‖y‖ →
        ‖iteratedFDeriv ℝ n (HRS.MS.Ker1.ker1_g1 d s) y‖ ≤ C)) := by
    intro n
    by_cases hn : 0 < (n : ℝ) + s
    · obtain ⟨C1, hC10, hC1⟩ := HRS.MS.Ker1.ker1_gam_bound_a hd hs0 hsd n hn
      have hK := sa12c19_corner_compact (d := d)
      have hsub : {y : Euc d | (∀ i, |y i| ≤ 1 / 2) ∧ 1 / 2 ≤ ‖y‖} ⊆ {y : Euc d | Torus.mk y ≠ 0} :=
        fun y hy => sa12c19_corner_offLattice hy.1 hy.2
      have hcont : ContinuousOn (iteratedFDeriv ℝ n (HRS.MS.Ker1.ker1_g1 d s))
          {y : Euc d | (∀ i, |y i| ≤ 1 / 2) ∧ 1 / 2 ≤ ‖y‖} :=
        (HRS.MS.Ker1.ker1_continuousOn_iteratedFDeriv (HRS.MS.Ker1.ker1_g1_contDiffOn hd hs0 hsd) n).mono hsub
      obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn hcont
      refine ⟨max (max C1 M) 0, le_max_right _ _, fun _ => ⟨fun L hL x hx0 hx => ?_, fun y hy1 hy2 => ?_⟩⟩
      · exact (hC1 L hL x hx0 hx).trans
          (mul_le_mul_of_nonneg_right ((le_max_left _ _).trans (le_max_left _ _)) (by positivity))
      · exact (hM y ⟨hy1, hy2⟩).trans ((le_max_right _ _).trans (le_max_left _ _))
    · exact ⟨0, le_rfl, fun h => absurd h hn⟩
  choose Cn hCn0 hCn using hex
  refine ⟨∑ n ∈ Finset.range (m + 3), Cn n, Finset.sum_nonneg fun n _ => hCn0 n, ?_⟩
  intro L hL γ hγ n hnm hn u hu0 hcube
  have hL0 : 0 < L := lt_of_lt_of_le one_pos hL
  have hCle : Cn n ≤ ∑ n ∈ Finset.range (m + 3), Cn n :=
    Finset.single_le_sum (f := Cn) (fun n _ => hCn0 n) (Finset.mem_range.2 (by omega))
  obtain ⟨hA, hB⟩ := hCn n hn
  have hE0 : 0 ≤ ‖u‖ ^ (-s - n) + (if 0 < s then L ^ (-s - n) else 0) +
      (if s = 0 then L ^ (-(n : ℝ)) else 0) := by
    have h1 : 0 ≤ ‖u‖ ^ (-s - (n : ℝ)) := Real.rpow_nonneg (norm_nonneg _) _
    have h2 : 0 ≤ (if 0 < s then L ^ (-s - (n : ℝ)) else 0) := by
      split_ifs
      · exact Real.rpow_nonneg hL0.le _
      · exact le_rfl
    have h3 : 0 ≤ (if s = 0 then L ^ (-(n : ℝ)) else 0) := by
      split_ifs
      · exact Real.rpow_nonneg hL0.le _
      · exact le_rfl
    linarith
  by_cases hnear : ‖u‖ ≤ L / 2
  · have hoff := HRS.MS.Ker1.ker1_offLattice_of_half hL0 hu0 hnear
    have heq := HRS.MS.Ker1.ker1_eventually_eq_gam hd hs0 hsd hL0 hγ hoff
    rw [((heq.iteratedFDeriv ℝ n).self_of_nhds)]
    refine (hA L hL0 u hu0 hnear).trans ?_
    have h1 : 0 ≤ ‖u‖ ^ (-s - (n : ℝ)) := Real.rpow_nonneg (norm_nonneg _) _
    have h2 : 0 ≤ (if 0 < s then L ^ (-s - (n : ℝ)) else 0) := by
      split_ifs
      · exact Real.rpow_nonneg hL0.le _
      · exact le_rfl
    have h3 : 0 ≤ (if s = 0 then L ^ (-(n : ℝ)) else 0) := by
      split_ifs
      · exact Real.rpow_nonneg hL0.le _
      · exact le_rfl
    calc Cn n * ‖u‖ ^ (-s - (n : ℝ)) ≤ (∑ n ∈ Finset.range (m + 3), Cn n) * ‖u‖ ^ (-s - (n : ℝ)) :=
          mul_le_mul_of_nonneg_right hCle h1
      _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) (hCle.trans' (hCn0 n))
  · push Not at hnear
    have hy : ∀ i, |(L⁻¹ • u) i| ≤ 1 / 2 := by
      intro i
      simp only [PiLp.smul_apply, smul_eq_mul, abs_mul, abs_inv, abs_of_pos hL0]
      rw [inv_mul_le_iff₀ hL0]
      linarith [hcube i]
    have hyn : 1 / 2 ≤ ‖L⁻¹ • u‖ := by
      rw [norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hL0, inv_mul_eq_div, le_div_iff₀ hL0]
      linarith
    have hmk : Torus.mk (L⁻¹ • u) ≠ 0 := sa12c19_corner_offLattice hy hyn
    have hoff := (HRS.MS.Ker1.ker1_offLattice_iff hL0 u).2 hmk
    have heq := HRS.MS.Ker1.ker1_eventually_eq_gam hd hs0 hsd hL0 hγ hoff
    rw [((heq.iteratedFDeriv ℝ n).self_of_nhds),
      HRS.MS.Ker1.ker1_gam_iter hd hs0 hsd hL0 hmk, norm_smul, HRS.MS.Ker1.ker1_gam_scale_pow hL0,
      Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hL0.le _)]
    have h1 := hB _ hy hyn
    have hLp : 0 ≤ L ^ (-(s + (n : ℝ))) := Real.rpow_nonneg hL0.le _
    have hmain : L ^ (-(s + (n : ℝ))) * ‖iteratedFDeriv ℝ n (HRS.MS.Ker1.ker1_g1 d s) (L⁻¹ • u)‖ ≤
        Cn n * L ^ (-(s + (n : ℝ))) := by
      calc _ ≤ L ^ (-(s + (n : ℝ))) * Cn n := mul_le_mul_of_nonneg_left h1 hLp
        _ = _ := mul_comm _ _
    refine hmain.trans ?_
    have hterm : L ^ (-(s + (n : ℝ))) ≤ ‖u‖ ^ (-s - (n : ℝ)) + (if 0 < s then L ^ (-s - (n : ℝ)) else 0) +
        (if s = 0 then L ^ (-(n : ℝ)) else 0) := by
      have h1 : 0 ≤ ‖u‖ ^ (-s - (n : ℝ)) := Real.rpow_nonneg (norm_nonneg _) _
      rcases hs0.lt_or_eq with hs | hs
      · have e : -(s + (n : ℝ)) = -s - n := by ring
        have h3 : (if s = 0 then L ^ (-(n : ℝ)) else 0) = 0 := by simp [hs.ne']
        rw [if_pos hs, h3, e]
        linarith
      · subst hs
        have h2 : (if (0 : ℝ) < 0 then L ^ (-0 - (n : ℝ)) else 0) = 0 := by simp
        have e : -((0 : ℝ) + (n : ℝ)) = -(n : ℝ) := by ring
        rw [h2, if_pos rfl, e]
        linarith
    calc Cn n * L ^ (-(s + (n : ℝ))) ≤ Cn n * (‖u‖ ^ (-s - (n : ℝ)) + (if 0 < s then L ^ (-s - (n : ℝ)) else 0) +
          (if s = 0 then L ^ (-(n : ℝ)) else 0)) := mul_le_mul_of_nonneg_left hterm (hCn0 n)
      _ ≤ _ := mul_le_mul_of_nonneg_right hCle hE0
-- END SA12.C19

end HRS.MH.AdjointRd.Phase2SA12Construction
