import HRS.MS.SA16Y8Sc1
import HRS.MS.SA16Y7K1
import HRS.MS.SA16QMorrey4

/-!
# S.A.16 (SA16Y8) Hd1: Hölder modulus of `D²u` for `u ∈ C_c^∞` by the jet norm (classical clause, K2c)

`sa16y8_norm_iter_iter`: `‖D^k (D^j u) y‖ = ‖D^{k+j} u y‖`.
`sa16y8_holder_cc`: for `m > 2 + d/p`: `‖D²u(x+h) - D²u(x)‖ ≤ C ‖h‖^α ‖wJet m u‖_{L^p}` for `‖h‖ ≤ 1`, `u ∈ C_c^∞`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16Q
open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixA.Phase2SA16

section Hd1
variable {d : ℕ}

/-- the second derivative as a nested continuous linear map -/
noncomputable def sa16y8_D2 (u : Euc d → ℝ) : Euc d → (Euc d →L[ℝ] (Euc d →L[ℝ] ℝ)) := fderiv ℝ (fderiv ℝ u)

lemma sa16y8_norm_D2_iter {u : Euc d → ℝ} (k : ℕ) (y : Euc d) :
    ‖iteratedFDeriv ℝ k (sa16y8_D2 u) y‖ = ‖iteratedFDeriv ℝ (k + 2) u y‖ := by
  unfold sa16y8_D2
  rw [norm_iteratedFDeriv_fderiv, norm_iteratedFDeriv_fderiv]

lemma sa16y8_D2_smooth {u : Euc d → ℝ} (hu : ContDiff ℝ ∞ u) : ContDiff ℝ ∞ (sa16y8_D2 u) := by
  unfold sa16y8_D2
  exact (hu.fderiv_right (m := ∞) (by simp)).fderiv_right (m := ∞) (by simp)

set_option maxHeartbeats 1600000 in
theorem sa16y8_holder_cc (d m : ℕ) (hd : 1 ≤ d) (p : ℝ) [Fact (2 ≤ p)] (hmp : 2 + (d : ℝ) / p < m) :
    ∃ C α : ℝ, 0 < C ∧ 0 < α ∧ ∀ u : Euc d → ℝ, IsCcInfty u → ∀ (x h : Euc d), ‖h‖ ≤ 1 →
      ‖sa16y8_D2 u (x + h) - sa16y8_D2 u x‖ ≤ C * ‖h‖ ^ α * (wNormE m p u).toReal := by
  have hp2 : 2 ≤ p := Fact.out
  have hp : 1 < p := by linarith
  have hp0 : 0 < p := by linarith
  have hdp : (0 : ℝ) ≤ (d : ℝ) / p := by positivity
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 2 := by
    have : 2 < m := by
      have : (2 : ℝ) < m := by linarith
      exact_mod_cast this
    exact ⟨m - 2, by omega⟩
  have hm' : (d : ℝ) / p < m' := by
    have : (2 : ℝ) + d / p < (m' : ℝ) + 2 := by exact_mod_cast hmp
    linarith
  have hm'1 : 1 ≤ m' := by
    have : (0 : ℝ) < m' := lt_of_le_of_lt hdp hm'
    exact_mod_cast this
  obtain ⟨C0, hC0, hM⟩ := sa16y7_morrey_scaled d hd p hp m' hm'1 hm'
  obtain ⟨α, hα, hsc⟩ := sa16y8_scale d hd p hp m' hm'
  refine ⟨C0 * ((m' : ℝ) + 1) * (2 * (d : ℝ) ^ (m' + 2)), α, by positivity, hα, fun u hu x h hh => ?_⟩
  obtain ⟨hus, huc⟩ := hu
  have hS : MemLp (sa16j_S d (m' + 2) u) (ENNReal.ofReal p) volume := by
    unfold sa16j_S
    refine memLp_finsetSum _ fun j _ => ?_
    exact (((hus.continuous_iteratedFDeriv (m := j) (by exact_mod_cast le_top)).norm).memLp_of_hasCompactSupport
      (huc.iteratedFDeriv j).norm)
  have hW : wNormE (m' + 2) p u = eLpNorm (wJet (m' + 2) u) (ENNReal.ofReal p) volume :=
    sa16j_wNormE_eq d (m' + 2) p hus hS
  set W : ℝ≥0∞ := eLpNorm (wJet (m' + 2) u) (ENNReal.ofReal p) volume with hWdef
  have hWt : W ≠ ⊤ := (sa16j_jet_memLp d (m' + 2) p hus hS).eLpNorm_lt_top.ne
  rw [hW]
  have hW' : W = ENNReal.ofReal W.toReal := (ENNReal.ofReal_toReal hWt).symm
  by_cases hh0 : h = 0
  · subst hh0
    rw [add_zero, show sa16y8_D2 u x - sa16y8_D2 u x = 0 from @sub_self (Euc d →L[ℝ] Euc d →L[ℝ] ℝ) _ _]
    have h0 : ‖(0 : Euc d →L[ℝ] Euc d →L[ℝ] ℝ)‖ = 0 := ContinuousLinearMap.opNorm_zero
    rw [h0]
    simp [Real.zero_rpow hα.ne']
  have hρ : 0 < ‖h‖ := norm_pos_iff.2 hh0
  obtain ⟨r, hr0, hk, htop⟩ := hsc ‖h‖ hρ hh
  set w := sa16y8_D2 u with hwdef
  have hw : ContDiff ℝ ∞ w := sa16y8_D2_smooth hus
  have hv : ContDiff ℝ ∞ (fun z => w (z + h) - w z) :=
    (hw.comp (contDiff_id.add contDiff_const)).sub hw
  have hm0 := hM _ (fun z => w (z + h) - w z) hv x r hr0
  set X : ℝ≥0∞ := ENNReal.ofReal ((d : ℝ) ^ (m' + 2)) * W with hX
  have hnormk : ∀ k, k ≤ m' → eLpNorm (fun y => ‖iteratedFDeriv ℝ (k + 2) u y‖) (ENNReal.ofReal p) volume ≤ X :=
    fun k hk' => sa16q_iter_lp hus hd p (by omega)
  have hEk : ∀ k, k < m' →
      eLpNorm (fun y => ‖iteratedFDeriv ℝ k (fun z => w (z + h) - w z) y‖) (ENNReal.ofReal p) volume ≤
        ENNReal.ofReal ‖h‖ * X := by
    intro k hk'
    refine (sa16y7_Dk_diff_le hw hp h k).trans (mul_le_mul_right ?_ _)
    have e : (fun y => ‖iteratedFDeriv ℝ (k + 1) w y‖) = fun y => ‖iteratedFDeriv ℝ (k + 1 + 2) u y‖ :=
      funext fun y => sa16y8_norm_D2_iter (k + 1) y
    rw [e]
    exact sa16q_iter_lp hus hd p (l := k + 1 + 2) (m := m' + 2) (by omega)
  have hEtop : eLpNorm (fun y => ‖iteratedFDeriv ℝ m' (fun z => w (z + h) - w z) y‖) (ENNReal.ofReal p) volume ≤
      2 * X := by
    refine (sa16y7_Dk_diff_two hw hp h m').trans (mul_le_mul_right ?_ _)
    have e : (fun y => ‖iteratedFDeriv ℝ m' w y‖) = fun y => ‖iteratedFDeriv ℝ (m' + 2) u y‖ :=
      funext fun y => sa16y8_norm_D2_iter m' y
    rw [e]
    exact sa16q_iter_lp hus hd p (l := m' + 2) (m := m' + 2) le_rfl
  set c : ℕ → ℝ≥0∞ := fun k => ENNReal.ofReal (r ^ k * ((r ^ d)⁻¹) ^ (1 / p)) with hc
  have hsum : ∑ k ∈ Finset.range (m' + 1), c k *
      eLpNorm (fun y => ‖iteratedFDeriv ℝ k (fun z => w (z + h) - w z) y‖) (ENNReal.ofReal p) volume ≤
      (((m' : ℝ≥0∞) + 2) * ENNReal.ofReal (‖h‖ ^ α)) * X := by
    rw [Finset.sum_range_succ]
    have h1 : ∑ k ∈ Finset.range m', c k *
        eLpNorm (fun y => ‖iteratedFDeriv ℝ k (fun z => w (z + h) - w z) y‖) (ENNReal.ofReal p) volume ≤
        ∑ k ∈ Finset.range m', ENNReal.ofReal (‖h‖ ^ α) * X := by
      refine Finset.sum_le_sum fun k hk' => ?_
      have hk'' : k < m' := Finset.mem_range.1 hk'
      calc c k * eLpNorm (fun y => ‖iteratedFDeriv ℝ k (fun z => w (z + h) - w z) y‖) (ENNReal.ofReal p) volume
          ≤ c k * (ENNReal.ofReal ‖h‖ * X) := mul_le_mul_right (hEk k hk'') _
        _ = ENNReal.ofReal (r ^ k * ((r ^ d)⁻¹) ^ (1 / p) * ‖h‖) * X := by
            rw [hc]; simp only
            rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
        _ ≤ ENNReal.ofReal (‖h‖ ^ α) * X := mul_le_mul_left (ENNReal.ofReal_le_ofReal (hk k hk'')) _
    have h2 : c m' * eLpNorm (fun y => ‖iteratedFDeriv ℝ m' (fun z => w (z + h) - w z) y‖) (ENNReal.ofReal p) volume ≤
        ENNReal.ofReal (‖h‖ ^ α) * (2 * X) :=
      (mul_le_mul_right hEtop _).trans (mul_le_mul_left (ENNReal.ofReal_le_ofReal htop) _)
    refine (add_le_add h1 h2).trans (le_of_eq ?_)
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    ring
  have hfin : ‖w (x + h) - w x‖ₑ ≤ ENNReal.ofReal C0 * ((((m' : ℝ≥0∞) + 2) * ENNReal.ofReal (‖h‖ ^ α)) * X) :=
    hm0.trans (mul_le_mul_right hsum _)
  have hXr : X = ENNReal.ofReal ((d : ℝ) ^ (m' + 2) * W.toReal) := by
    rw [hX, hW', ENNReal.ofReal_mul (by positivity)]
    simp [ENNReal.ofReal_toReal hWt]
  have hm2 : ((m' : ℝ≥0∞) + 2) = ENNReal.ofReal ((m' : ℝ) + 2) := by
    rw [ENNReal.ofReal_add (by positivity) (by norm_num)]; simp
  rw [hXr, hm2, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul (by positivity), ← ofReal_norm_eq_enorm] at hfin
  have hfin' := (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 hfin
  refine hfin'.trans ?_
  have hρα : 0 ≤ ‖h‖ ^ α := Real.rpow_nonneg (norm_nonneg _) _
  have hWr : 0 ≤ W.toReal := ENNReal.toReal_nonneg
  have hdm : 0 ≤ (d : ℝ) ^ (m' + 2) := by positivity
  have hm'0 : (0 : ℝ) ≤ m' := Nat.cast_nonneg _
  have : C0 * (((m' : ℝ) + 2) * ‖h‖ ^ α * ((d : ℝ) ^ (m' + 2) * W.toReal)) ≤
      C0 * ((m' : ℝ) + 1) * (2 * (d : ℝ) ^ (m' + 2)) * ‖h‖ ^ α * W.toReal := by
    have e : C0 * ((m' : ℝ) + 1) * (2 * (d : ℝ) ^ (m' + 2)) * ‖h‖ ^ α * W.toReal =
        C0 * ((2 * m' + 2) * ‖h‖ ^ α * ((d : ℝ) ^ (m' + 2) * W.toReal)) := by ring
    rw [e]
    refine mul_le_mul_of_nonneg_left ?_ hC0.le
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    exact mul_le_mul_of_nonneg_right (by linarith) hρα
  exact this

end Hd1

end HRS.Whole.AppendixA.Phase2SA16Q
