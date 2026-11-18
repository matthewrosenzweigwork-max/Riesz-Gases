import HRS.MS.ZeroTempAux2
import HRS.MS.SobEmbTie

/-!
# SA11, packet A3: the Sobolev embedding in the jet norm

`sa11_embed`: for `m ≥ m_* + ⌊d/p⌋ + 1`, `p ≥ 2`, `d ≥ 1` there is `C` with
`‖D^iφ(x)‖ ≤ C ‖J φ‖_{W^{m,p}}` for all `φ ∈ C_c^∞`, `i ≤ m_*`, `x ∈ ℝ^d`.
It is the S.A.1 machinery `sa1_glue_inf` (Morrey with the Sobolev ladder of `sa1_reach_all`, `d ≥ 2`; `sa1_reach_self`,
`d = 1`) combined with the comparison `‖D^iφ‖ ≤ d^i ‖jet φ‖` of `ZeroTempAux1`.
-/

noncomputable section

open MeasureTheory
open HRS HRS.Whole HRS.Whole.AppendixA
open scoped ENNReal ContDiff

namespace HRS.MS.ZeroTemp

variable {d : ℕ}

/-- The reach hypothesis of Morrey's inequality for every `p ≥ 2`, `d ≥ 1`, with `j = ⌊d/p⌋ + 1`. -/
theorem sa11_reachInf (hd : 1 ≤ d) {p : ℝ} (hp : 2 ≤ p) :
    HRS.SA1.sa1_ReachInf d p (⌊(d : ℝ) / p⌋₊ + 1) := by
  have hp0 : 0 < p := by linarith
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  by_cases hd2 : 2 ≤ d
  · set j : ℕ := ⌊(d : ℝ) / p⌋₊ with hj
    have hj1 : (j : ℝ) ≤ d / p := Nat.floor_le (by positivity)
    have hj2 : (d : ℝ) / p < j + 1 := Nat.lt_floor_add_one _
    set c0 : ℝ := 1 / p - (j : ℝ) / d with hc0
    have hc0' : c0 = ((d : ℝ) / p - j) / d := by rw [hc0]; field_simp
    have hc00 : 0 ≤ c0 := by rw [hc0']; exact div_nonneg (by linarith) hdpos.le
    have hc01 : c0 < 1 / d := by
      rw [hc0']; exact div_lt_div_of_pos_right (by linarith) hdpos
    set z : ℝ := min (1 / p) ((c0 + 1 / d) / 2) with hz
    have hz0 : 0 < z := lt_min (by positivity) (by
      have : 0 < 1 / (d : ℝ) := by positivity
      linarith)
    have hzd : z < 1 / d := lt_of_le_of_lt (min_le_right _ _) (by linarith)
    have hzx : z ≤ 1 / p := min_le_left _ _
    have hzc : c0 ≤ z := le_min (by
      rw [hc0]
      have : (0 : ℝ) ≤ (j : ℝ) / d := by positivity
      linarith) (by linarith)
    set q : ℝ := 1 / z with hq
    have hq1 : 1 / q = z := by rw [hq, one_div_one_div]
    have hqd : (d : ℝ) < q := by
      rw [hq, lt_one_div hdpos hz0]; exact hzd
    have hpq : p ≤ q := by
      have : 1 / q ≤ 1 / p := by rw [hq1]; exact hzx
      exact (one_div_le_one_div (by linarith) hp0).1 this
    have hR : HRS.SA1.sa1_Reach d p j q :=
      HRS.SA1.sa1_reach_all hd2 (by linarith) j q hpq (by rw [hq1]; exact hzc)
    exact HRS.SA1.sa1_reachInf_of_reach hd hqd hR
  · have hd1 : d = 1 := by omega
    subst hd1
    have hfl : ⌊((1 : ℕ) : ℝ) / p⌋₊ = 0 := by
      rw [Nat.floor_eq_zero]
      push_cast
      rw [div_lt_one hp0]; linarith
    rw [hfl]
    exact HRS.SA1.sa1_reachInf_of_reach (j := 0) hd (by push_cast; linarith) (HRS.SA1.sa1_reach_self p 0)

variable {m : ℕ} {p : ℝ} [Fact (2 ≤ p)]

omit [Fact (2 ≤ p)] in
theorem sa11_iter_eLp_le {φ : Euc d → ℝ} (hφ : IsCcInfty φ) {i : ℕ} (hi : i ≤ m) :
    eLpNorm (iteratedFDeriv ℝ i φ) (ENNReal.ofReal p) volume ≤
      ENNReal.ofReal ((d : ℝ) ^ i) * eLpNorm (wJet m φ) (ENNReal.ofReal p) volume := by
  have hc : Continuous (iteratedFDeriv ℝ i φ) :=
    hφ.1.continuous_iteratedFDeriv (by exact_mod_cast le_top)
  calc eLpNorm (iteratedFDeriv ℝ i φ) (ENNReal.ofReal p) volume
      ≤ eLpNorm (((d : ℝ) ^ i) • wJet m φ) (ENNReal.ofReal p) volume := by
        refine eLpNorm_mono_ae hc.aestronglyMeasurable (Filter.Eventually.of_forall fun x => ?_)
        rw [Pi.smul_apply, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        exact sa11_iter_le_jet hi x
    _ = ENNReal.ofReal ((d : ℝ) ^ i) * eLpNorm (wJet m φ) (ENNReal.ofReal p) volume := by
        rw [eLpNorm_const_smul, Real.enorm_eq_ofReal (by positivity)]

/-- The jet-norm Sobolev embedding `W^{m,p} ↪ C_b^{m_*}` on `C_c^∞`. -/
theorem sa11_embed (hd : 1 ≤ d) (hm : mStar d + ⌊(d : ℝ) / p⌋₊ + 1 ≤ m) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ φ : sa11_V d, ∀ i ≤ mStar d, ∀ x : Euc d,
      ‖iteratedFDeriv ℝ i φ.1 x‖ ≤ C * ‖sa11_J (m := m) (p := p) φ‖ := by
  have hp2 : 2 ≤ p := Fact.out
  have hp0 : 0 < p := by linarith
  obtain ⟨C0, hC0, hC⟩ := HRS.SA1.sa1_glue_inf (d := d) (a0 := p) hp0 (sa11_reachInf hd hp2) (mStar d)
  set M₀ : ℕ := mStar d + (⌊(d : ℝ) / p⌋₊ + 1) with hM₀
  have hM₀m : M₀ ≤ m := by omega
  refine ⟨C0 * ∑ i ∈ Finset.range (M₀ + 1), (d : ℝ) ^ i, mul_nonneg hC0 (Finset.sum_nonneg fun _ _ => by positivity),
    fun φ i hi x => ?_⟩
  have hφ := φ.2
  -- integrability of the `p`-th powers of the derivatives
  have hint : ∀ i ≤ M₀, Integrable (fun x => ‖iteratedFDeriv ℝ i φ.1 x‖ ^ p) := by
    intro i hiM
    have hc : Continuous (iteratedFDeriv ℝ i φ.1) :=
      hφ.1.continuous_iteratedFDeriv (by exact_mod_cast le_top)
    refine Continuous.integrable_of_hasCompactSupport ?_ ?_
    · exact hc.norm.rpow_const (fun _ => Or.inr hp0.le)
    · have hs := HasCompactSupport.iteratedFDeriv hφ.2 (𝕜 := ℝ) i
      refine hs.norm.comp_left (g := fun r : ℝ => r ^ p) ?_
      exact Real.zero_rpow hp0.ne'
  have hglue := hC φ.1 hφ.1 hint
  -- pointwise bound by `cbNorm`
  have hcb : ‖iteratedFDeriv ℝ i φ.1 x‖ ≤ HRS.cbNorm (mStar d) φ.1 := by
    have hbdd : BddAbove (Set.range fun x : Euc d => ‖iteratedFDeriv ℝ i φ.1 x‖) := by
      have hc : Continuous (iteratedFDeriv ℝ i φ.1) :=
        hφ.1.continuous_iteratedFDeriv (by exact_mod_cast le_top)
      obtain ⟨B, hB⟩ := hc.norm.bounded_above_of_compact_support (hφ.2.iteratedFDeriv i).norm
      exact ⟨B, by rintro _ ⟨y, rfl⟩; simpa using hB y⟩
    have h1 : ‖iteratedFDeriv ℝ i φ.1 x‖ ≤ ⨆ y : Euc d, ‖iteratedFDeriv ℝ i φ.1 y‖ := le_ciSup hbdd x
    refine h1.trans ?_
    unfold HRS.cbNorm
    exact Finset.single_le_sum (f := fun j => ⨆ z : Euc d, ‖iteratedFDeriv ℝ j φ.1 z‖)
      (fun j _ => Real.iSup_nonneg fun z => norm_nonneg _) (Finset.mem_range.2 (by omega))
  -- the Sobolev norm by the jet norm
  have hsob : HRS.Whole.sobolevWNorm M₀ p φ.1 ≤ (∑ i ∈ Finset.range (M₀ + 1), (d : ℝ) ^ i) * ‖sa11_J (m := m) (p := p) φ‖ := by
    rw [HRS.SA1.sa1_sob_eq, Finset.sum_mul]
    refine Finset.sum_le_sum fun j hj => ?_
    have hjM : j ≤ M₀ := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
    have hfin : HRS.SA1.sa1_nrm j p φ.1 ≠ ⊤ ∧ (HRS.SA1.sa1_nrm j p φ.1).toReal = HRS.SA1.sa1_T j p φ.1 :=
      HRS.SA1.sa1_nrm_of_integrable hφ.1 hp0 (hint j hjM)
    rw [← hfin.2, sa11_norm_J]
    have hle := sa11_iter_eLp_le (m := m) (p := p) hφ (i := j) (hjM.trans hM₀m)
    have hjfin : eLpNorm (wJet m φ.1) (ENNReal.ofReal p) volume ≠ ⊤ :=
      (sa11_wJet_memLp (m := m) (p := p) hφ).eLpNorm_lt_top.ne
    have := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hjfin) hle
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)] at this
    exact this
  calc ‖iteratedFDeriv ℝ i φ.1 x‖ ≤ HRS.cbNorm (mStar d) φ.1 := hcb
    _ ≤ C0 * HRS.Whole.sobolevWNorm M₀ p φ.1 := hglue
    _ ≤ C0 * ((∑ i ∈ Finset.range (M₀ + 1), (d : ℝ) ^ i) * ‖sa11_J (m := m) (p := p) φ‖) :=
        mul_le_mul_of_nonneg_left hsob hC0
    _ = _ := by ring

end HRS.MS.ZeroTemp
