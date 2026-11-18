import HRS.MS.FixEqP3Aux34
import HRS.MS.UniqFTie

/-!
# S5.7 `fixed_equation` (worker S57P), part 47: from the hypotheses of `fixed_equation` to the data of the packets
-/

noncomputable section

set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace HRS.MS.FixEq

open HRS HRS.Whole HRS.MP.RdGen HRS.MS.Go HRS.MS.Fcau

variable {d : ℕ}

/-- the decay constant of the densities -/
def s57pA0 (b : WholeBounds d) : ℝ :=
  (d : ℝ) ^ ((b.k + 1 + ⌈(d : ℝ) / 2⌉₊ + 3) + 1 + ⌈(d : ℝ) / 2⌉₊ + 2) * max b.Λ 0 * 2 ^ ((d : ℝ) + 3)

theorem s57pA0_nonneg (b : WholeBounds d) : 0 ≤ s57pA0 b := by unfold s57pA0; positivity

theorem s57p_decay_top (b : WholeBounds d) (hb : b.Valid) {ρ : ℝ → Euc d → ℝ}
    (hdens : ∀ t ∈ Set.Icc (0 : ℝ) b.T, ContDiff ℝ (b.k + 6 + ⌈(d : ℝ) / 2⌉₊ + 4 + ⌈(d : ℝ) / 2⌉₊) (ρ t) ∧
      weightedSupE (b.k + 6 + ⌈(d : ℝ) / 2⌉₊ + 4 + ⌈(d : ℝ) / 2⌉₊) b.L (ρ t) ≤ ENNReal.ofReal b.Λ)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) b.T) :
    RgDecay ((b.k + 1 + ⌈(d : ℝ) / 2⌉₊ + 3) + 1 + ⌈(d : ℝ) / 2⌉₊ + 2) (fun _ => s57pA0 b) (ρ t) := by
  have hd1 : 1 ≤ d := by have := hb.hd; omega
  have hL : (d : ℝ) + 3 ≤ b.L := by
    have := hb.hL; have := hb.hs0; have : (0 : ℝ) ≤ b.k := Nat.cast_nonneg _
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg _
    linarith
  have hle : (b.k + 1 + ⌈(d : ℝ) / 2⌉₊ + 3) + 1 + ⌈(d : ℝ) / 2⌉₊ + 2 ≤
      b.k + 6 + ⌈(d : ℝ) / 2⌉₊ + 4 + ⌈(d : ℝ) / 2⌉₊ := by omega
  exact s57p_rgdecay_of_wsup hd1 hL ((hdens t ht).1.of_le (by exact_mod_cast hle))
    (((s57p_wsup_mono_r hle b.L (ρ t))).trans (hdens t ht).2)

theorem s57p_c_top (b : WholeBounds d) {c : ℝ → Euc d → Euc d}
    (hcd : ∀ t ∈ Set.Icc (0 : ℝ) b.T, ContDiff ℝ (b.k + 6 + ⌈(d : ℝ) / 2⌉₊ + 4 + ⌈(d : ℝ) / 2⌉₊) (c t) ∧
      cbNormVecE (b.k + 6 + ⌈(d : ℝ) / 2⌉₊ + 4 + ⌈(d : ℝ) / 2⌉₊) (c t) ≤ ENNReal.ofReal b.Λ)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) b.T) :
    ContDiff ℝ ((b.k + 1 + ⌈(d : ℝ) / 2⌉₊ + 3) + 1 + ⌈(d : ℝ) / 2⌉₊ : ℕ) (c t) ∧
      ∀ i ≤ (b.k + 1 + ⌈(d : ℝ) / 2⌉₊ + 3) + 1 + ⌈(d : ℝ) / 2⌉₊, ∀ x, ‖iteratedFDeriv ℝ i (c t) x‖ ≤ max b.Λ 0 :=
  ⟨(hcd t ht).1.of_le (by exact_mod_cast (by omega : (b.k + 1 + ⌈(d : ℝ) / 2⌉₊ + 3) + 1 + ⌈(d : ℝ) / 2⌉₊ ≤
    b.k + 6 + ⌈(d : ℝ) / 2⌉₊ + 4 + ⌈(d : ℝ) / 2⌉₊)),
    fun i hi x => s57p_cbVec_bound (hcd t ht).2 (by omega) x⟩

/-- the family hypotheses at level `b.k`, from those of `fixed_equation` -/
theorem s57p_mkFx (b : WholeBounds d) (hb : b.Valid) {ν : ℝ} {c : ℝ → Euc d → Euc d} {ρ : ℝ → Euc d → ℝ}
    (hν0 : 0 ≤ ν) (hνs : ν ≤ b.νstar) (hF : FixedEqFcauHyp b ν c ρ)
    (hprob : ∀ t ∈ Set.Icc (0 : ℝ) b.T, HRS.Whole.IsProbDensity (ρ t))
    (hdens : ∀ t ∈ Set.Icc (0 : ℝ) b.T, ContDiff ℝ (b.k + 6 + ⌈(d : ℝ) / 2⌉₊ + 4 + ⌈(d : ℝ) / 2⌉₊) (ρ t) ∧
      weightedSupE (b.k + 6 + ⌈(d : ℝ) / 2⌉₊ + 4 + ⌈(d : ℝ) / 2⌉₊) b.L (ρ t) ≤ ENNReal.ofReal b.Λ)
    (hcd : ∀ t ∈ Set.Icc (0 : ℝ) b.T, ContDiff ℝ (b.k + 6 + ⌈(d : ℝ) / 2⌉₊ + 4 + ⌈(d : ℝ) / 2⌉₊) (c t) ∧
      cbNormVecE (b.k + 6 + ⌈(d : ℝ) / 2⌉₊ + 4 + ⌈(d : ℝ) / 2⌉₊) (c t) ≤ ENNReal.ofReal b.Λ)
    (hadj : UlAdjointInput b.θ (fixedEqCoeff b.s b.M b.Q ν c ρ) b.T (b.k + 1) b.K)
    (huniq : HRS.MS.S52B.S52bUniq (fixedEqCoeff b.s b.M b.Q ν c ρ) b.T) :
    S57pFx b.θ b.T b.k b.K b.s b.M b.Q ν c ρ (s57pA0 b) (max b.Λ 0) b.νstar := by
  have hk : (d : ℝ) / 2 + 8 < b.k := hb.hk
  have hk8 : 8 ≤ b.k := by
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    have : (8 : ℝ) < b.k := by linarith
    exact_mod_cast this.le
  have fe := s57p_feData b hb (n := b.k + 6 + ⌈(d : ℝ) / 2⌉₊ + 4 + ⌈(d : ℝ) / 2⌉₊) (by omega) hν0
    (fun t ht => hdens t ht) (fun t ht => hcd t ht) hF
  refine ⟨⟨by omega, huniq, s57p_lin_inst b.M b.Q fe, s57p_gen_inst b.M b.Q fe, hadj⟩, fe, by omega, hb.hT.le, hprob,
    fun t ht => rg_decay_mono (by omega) (s57p_decay_top b hb hdens ht), fun t ht => ?_, ?_⟩
  · obtain ⟨h1, h2⟩ := s57p_c_top b hcd ht
    exact ⟨h1.of_le (by exact_mod_cast (by omega : b.k + 1 + 1 + ⌈(d : ℝ) / 2⌉₊ ≤
      (b.k + 1 + ⌈(d : ℝ) / 2⌉₊ + 3) + 1 + ⌈(d : ℝ) / 2⌉₊)), fun i hi x => h2 i (by omega) x⟩
  · rw [abs_of_nonneg hν0]; exact hνs

theorem s57p_cbVec_delta {K' K : ℕ} (hK : K' ≤ K) (c cN : Euc d → Euc d) :
    cbNormVecE K' (fun x => c x - cN x) ≤ cbNormVecE K (fun x => cN x - c x) := by
  unfold cbNormVecE
  have e : ∀ j : ℕ, (⨆ x : Euc d, ENNReal.ofReal ‖iteratedFDeriv ℝ j (fun x => c x - cN x) x‖) =
      ⨆ x : Euc d, ENNReal.ofReal ‖iteratedFDeriv ℝ j (fun x => cN x - c x) x‖ := by
    intro j
    refine iSup_congr fun x => ?_
    have : (fun x => c x - cN x) = -(fun x => cN x - c x) := by funext y; simp
    rw [this, iteratedFDeriv_neg_apply, norm_neg]
  simp_rw [e]
  exact Finset.sum_le_sum_of_subset (Finset.range_mono (by omega))

theorem s57p_tau_le {ρ ρN : ℝ → Euc d → ℝ} {T : ℝ} (hprob : ∀ t ∈ Set.Icc (0 : ℝ) T, HRS.Whole.IsProbDensity (ρ t))
    (hprobN : ∀ t ∈ Set.Icc (0 : ℝ) T, HRS.Whole.IsProbDensity (ρN t)) {r : ℝ} (hr : r ∈ Set.Icc (0 : ℝ) T) :
    ∫⁻ x : Euc d, ENNReal.ofReal |ρN r x - ρ r x| ≤ ENNReal.ofReal 2 := by
  have hP := hprob r hr
  have hPN := hprobN r hr
  have hint : Integrable (ρ r) := Integrable.of_integral_ne_zero (by rw [hP.integral_one]; norm_num)
  have hintN : Integrable (ρN r) := Integrable.of_integral_ne_zero (by rw [hPN.integral_one]; norm_num)
  calc ∫⁻ x : Euc d, ENNReal.ofReal |ρN r x - ρ r x| ≤ ∫⁻ x : Euc d, (ENNReal.ofReal (ρN r x) + ENNReal.ofReal (ρ r x)) :=
        lintegral_mono fun x => by
          rw [← ENNReal.ofReal_add (hPN.nonneg x) (hP.nonneg x)]
          refine ENNReal.ofReal_le_ofReal ?_
          rw [abs_le]; constructor <;> linarith [hPN.nonneg x, hP.nonneg x]
    _ = ENNReal.ofReal 2 := by
        rw [lintegral_add_left (hPN.measurable.ennreal_ofReal), ← ofReal_integral_eq_lintegral_ofReal hintN
          (Eventually.of_forall hPN.nonneg), ← ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall hP.nonneg),
          hP.integral_one, hPN.integral_one, ← ENNReal.ofReal_add (by norm_num) (by norm_num)]
        norm_num

end HRS.MS.FixEq
