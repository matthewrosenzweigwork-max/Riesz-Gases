import HRS.MS.SA12X3C10A

/-!
# S.A.12 C10 (SA12X3), part B: a moving cell energy is bounded by the uloc norm squared
-/

set_option autoImplicit false
set_option maxHeartbeats 12800000

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MH.AdjointRd.Phase2SA12Near

open HRS HRS.Whole HRS.Whole.AppendixA HRS.MH.AdjointRd HRS.MH.AdjointRd.Phase2SA12 HRS.MH.AdjointRd.Phase2SA12Construction

variable {d : ℕ}

theorem sa12x3_cellEnergy_le_uloc (hd : 1 ≤ d) (m : ℕ) (Cb T : ℝ) (χ χh : Euc d → ℝ) (hχ : IsCutoffPair χ χh) :
    ∃ K2 : ℝ, 0 < K2 ∧ ∀ (b : ℝ → Euc d → Euc d) (Ψ : ℝ → Euc d → Euc d), IsAdvectingDrift m Cb T b →
      IsNegDriftFlow T b Ψ → ∀ τ ∈ Icc (0 : ℝ) T, ∀ u : Euc d → ℝ, ContDiff ℝ ∞ u → ∀ c : Euc d,
        ENNReal.ofReal (cellEnergy m χ Ψ τ c u) ≤ ENNReal.ofReal K2 * ulocNormE m χ u ^ 2 := by
  obtain ⟨B, R, hB, hR1, hf⟩ := advected_cutoff_jets d hd m Cb T χ χh hχ
  obtain ⟨S, -, hSfin, hScov⟩ := (isCompact_closedBall (0 : Euc d) R).finite_cover_balls (e := 1) one_pos
  set Sf : Finset (Euc d) := hSfin.toFinset with hSf
  refine ⟨(Sf.card : ℝ) * 2 ^ m * ((m : ℝ) + 1) + 1, by positivity, ?_⟩
  intro b Ψ hb hΨ τ hτ u hu c
  set q : Euc d := Ψ τ c with hq
  have hcut := hf b Ψ hb hΨ τ hτ c
  set w : Euc d → ℝ := advCutoff χ Ψ τ c with hw
  have hwc : Continuous w := hcut.1.1.continuous
  have hwb : ∀ x, |w x| ≤ 1 := by
    intro x
    have h : w x ∈ Icc (0 : ℝ) 1 := hχ.1.2.2.2.1 _
    exact abs_le.2 ⟨by linarith [h.1], h.2⟩
  have hwcs : HasCompactSupport w := sa12x2_advCutoff_hasCompactSupport (hτ.1.trans hτ.2) hb hΨ hτ hχ.1.2.1 c
  -- the shifted cutoffs
  set fs : Euc d → Euc d → ℝ := fun p y => χ (y - p) * u y with hfs
  have hfsC : ∀ p, ContDiff ℝ ∞ (fs p) := fun p => (hχ.1.1.comp (contDiff_id.sub contDiff_const)).mul hu
  have hfsc : ∀ p, HasCompactSupport (fs p) := fun p => by
    have : HasCompactSupport (fun y => χ (y - p)) := by
      have := hχ.1.2.1.comp_homeomorph (Homeomorph.subRight p)
      exact this
    exact this.mul_right
  have hsupp : Function.support w ⊆ closedBall q R := (sa12z3_adv_support_le hχ Ψ τ c).trans hcut.2.2
  have hcs : ∀ p : Euc d, ∀ {j : ℕ} (idx : Fin j → Fin d), Continuous (partialDeriv idx (fs p)) ∧
      HasCompactSupport (partialDeriv idx (fs p)) := fun p j idx =>
    ⟨(sa12z3_pd_contDiff_inf (hfsC p) idx).continuous, sa12z3_pd_compact (hfsc p) idx⟩
  have hsqi : ∀ p : Euc d, ∀ {j : ℕ} (idx : Fin j → Fin d), Integrable (fun x => (partialDeriv idx (fs p) x) ^ 2) :=
    fun p j idx => Continuous.integrable_of_hasCompactSupport (f := fun x => (partialDeriv idx (fs p) x) ^ 2)
      ((hcs p idx).1.pow 2) ((hcs p idx).2.comp_left (g := fun t : ℝ => t ^ 2) (by simp))
  have hkey : ∀ {j : ℕ} (idx : Fin j → Fin d) (x : Euc d), (w x * partialDeriv idx u x) ^ 2 ≤
      ∑ s ∈ Sf, (partialDeriv idx (fs (q + s)) x) ^ 2 := by
    intro j idx x
    by_cases hx : w x = 0
    · rw [hx, zero_mul]; simpa using Finset.sum_nonneg fun s _ => sq_nonneg (partialDeriv idx (fs (q + s)) x)
    · have hxq : x ∈ closedBall q R := hsupp (Function.mem_support.2 hx)
      have h0 : x - q ∈ closedBall (0 : Euc d) R := by
        rw [mem_closedBall_zero_iff]; rw [mem_closedBall, dist_eq_norm] at hxq; exact hxq
      obtain ⟨s, hs, hxs⟩ := Set.mem_iUnion₂.1 (hScov h0)
      have hsSf : s ∈ Sf := by rw [hSf]; simpa using hs
      have hxb : x ∈ ball (q + s) 1 := by
        rw [mem_ball_iff_norm] at hxs ⊢
        have : x - (q + s) = (x - q) - s := by abel
        rw [this]; simpa [mem_ball_iff_norm] using hxs
      have hEq : EqOn (fs (q + s)) u (ball (q + s) 1) := by
        intro y hy
        have h1 : χ (y - (q + s)) = 1 := hχ.1.2.2.2.2 _ (by
          simpa [mem_closedBall_iff_norm] using (mem_ball_iff_norm.1 hy).le)
        simp [hfs, h1]
      have hpd := sa12x3_pd_congr_open (isOpen_ball (x := q + s) (ε := 1)) hEq idx hxb
      calc (w x * partialDeriv idx u x) ^ 2 ≤ (partialDeriv idx u x) ^ 2 := by
            rw [mul_pow]
            exact mul_le_of_le_one_left (sq_nonneg _) (by nlinarith [hwb x, abs_nonneg (w x), sq_abs (w x)])
        _ = (partialDeriv idx (fs (q + s)) x) ^ 2 := by rw [hpd]
        _ ≤ _ := Finset.single_le_sum (f := fun s => (partialDeriv idx (fs (q + s)) x) ^ 2)
              (fun s _ => sq_nonneg _) hsSf
  have hidx : ∀ {j : ℕ} (idx : Fin j → Fin d), ∫ x, (w x * partialDeriv idx u x) ^ 2 ≤
      ∑ s ∈ Sf, ∫ x, (partialDeriv idx (fs (q + s)) x) ^ 2 := by
    intro j idx
    have hl : Integrable (fun x => (w x * partialDeriv idx u x) ^ 2) :=
      Continuous.integrable_of_hasCompactSupport (f := fun x => (w x * partialDeriv idx u x) ^ 2)
        ((hwc.mul (sa12z3_pd_contDiff_inf hu idx).continuous).pow 2)
        ((hwcs.mul_right (f' := partialDeriv idx u)).comp_left (g := fun t : ℝ => t ^ 2) (by simp))
    rw [← integral_finsetSum _ fun s _ => hsqi (q + s) idx]
    exact integral_mono hl (integrable_finsetSum _ fun s _ => hsqi (q + s) idx) (hkey idx)
  -- sum up over the jets
  have hE1 : cellEnergy m χ Ψ τ c u ≤ ∑ s ∈ Sf, 2 ^ m * sa12x3_Jraw m (fs (q + s)) := by
    unfold cellEnergy jetSq
    have hX : ∀ (s : Euc d) (j : ℕ), 0 ≤ ∑ idx : Fin j → Fin d, ∫ x, (partialDeriv idx (fs (q + s)) x) ^ 2 :=
      fun s j => Finset.sum_nonneg fun idx _ => integral_nonneg fun x => sq_nonneg _
    calc ∑ j ∈ Finset.range (m + 1), (Nat.choose m j : ℝ) * ∑ idx : Fin j → Fin d,
          ∫ x, (advCutoff χ Ψ τ c x * partialDeriv idx u x) ^ 2
        ≤ ∑ j ∈ Finset.range (m + 1), (Nat.choose m j : ℝ) * ∑ s ∈ Sf, ∑ idx : Fin j → Fin d,
          ∫ x, (partialDeriv idx (fs (q + s)) x) ^ 2 := by
          refine Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
          rw [Finset.sum_comm]
          exact Finset.sum_le_sum fun idx _ => hidx idx
      _ = ∑ s ∈ Sf, ∑ j ∈ Finset.range (m + 1), (Nat.choose m j : ℝ) * ∑ idx : Fin j → Fin d,
          ∫ x, (partialDeriv idx (fs (q + s)) x) ^ 2 := by
          simp_rw [Finset.mul_sum]
          exact Finset.sum_comm
      _ ≤ ∑ s ∈ Sf, 2 ^ m * sa12x3_Jraw m (fs (q + s)) := by
          refine Finset.sum_le_sum fun s _ => ?_
          unfold sa12x3_Jraw
          rw [Finset.mul_sum]
          refine Finset.sum_le_sum fun j hj => ?_
          have hc : (Nat.choose m j : ℝ) ≤ 2 ^ m := by exact_mod_cast Nat.choose_le_two_pow m j
          exact mul_le_mul_of_nonneg_right hc (hX s j)
  -- the Sobolev norms
  have hsob : ∀ s ∈ Sf, ENNReal.ofReal (2 ^ m * sa12x3_Jraw m (fs (q + s))) ≤
      ENNReal.ofReal (2 ^ m * ((m : ℝ) + 1)) * ulocNormE m χ u ^ 2 := by
    intro s _
    have hfm : ContDiff ℝ m (fs (q + s)) := (hfsC (q + s)).of_le (sa12x2_le_top _)
    obtain ⟨-, h2⟩ := sa12x3_sob_jet m hfm (hfsc (q + s))
    have hU : HRS.Whole.sobolevNormE (m : ℝ) (fs (q + s)) ≤ ulocNormE m χ u :=
      le_iSup (fun z : Euc d => HRS.Whole.sobolevNormE (m : ℝ) fun x => χ (x - z) * u x) (q + s)
    rw [ENNReal.ofReal_mul (by positivity)]
    calc ENNReal.ofReal (2 ^ m) * ENNReal.ofReal (sa12x3_Jraw m (fs (q + s)))
        ≤ ENNReal.ofReal (2 ^ m) * (ENNReal.ofReal ((m : ℝ) + 1) * HRS.Whole.sobolevNormE (m : ℝ) (fs (q + s)) ^ 2) := by
          gcongr
      _ ≤ ENNReal.ofReal (2 ^ m) * (ENNReal.ofReal ((m : ℝ) + 1) * ulocNormE m χ u ^ 2) := by gcongr
      _ = _ := by rw [← mul_assoc, ENNReal.ofReal_mul (by positivity)]
  have hfin : ENNReal.ofReal (cellEnergy m χ Ψ τ c u) ≤
      (Sf.card : ℝ≥0∞) * (ENNReal.ofReal (2 ^ m * ((m : ℝ) + 1)) * ulocNormE m χ u ^ 2) := by
    calc ENNReal.ofReal (cellEnergy m χ Ψ τ c u) ≤ ENNReal.ofReal (∑ s ∈ Sf, 2 ^ m * sa12x3_Jraw m (fs (q + s))) :=
          ENNReal.ofReal_le_ofReal hE1
      _ = ∑ s ∈ Sf, ENNReal.ofReal (2 ^ m * sa12x3_Jraw m (fs (q + s))) :=
          ENNReal.ofReal_sum_of_nonneg fun s _ => mul_nonneg (by positivity)
            (Finset.sum_nonneg fun n _ => Finset.sum_nonneg fun i _ => integral_nonneg fun x => sq_nonneg _)
      _ ≤ ∑ _s ∈ Sf, ENNReal.ofReal (2 ^ m * ((m : ℝ) + 1)) * ulocNormE m χ u ^ 2 := Finset.sum_le_sum hsob
      _ = _ := by simp
  refine hfin.trans ?_
  have e : (Sf.card : ℝ≥0∞) * ENNReal.ofReal (2 ^ m * ((m : ℝ) + 1)) =
      ENNReal.ofReal ((Sf.card : ℝ) * (2 ^ m * ((m : ℝ) + 1))) := by
    rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
  rw [← mul_assoc, e]
  gcongr
  nlinarith

end HRS.MH.AdjointRd.Phase2SA12Near
