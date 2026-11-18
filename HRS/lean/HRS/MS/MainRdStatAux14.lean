import HRS.MS.MainRdStatAux13
import HRS.Main.A8PAux28
import HRS.Main.A8PAux29

/-!
# SA2, packet 8a: the `ℝ^q`-valued Hilbert Itô integral of the particle martingale (copy of A8P 25-27 for `ℝ^d`)
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open HRS.Whole HRS.Whole.AppendixA HRS.Uniform HRS.GF HRS.Whole.AppendixALemmas
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.MainRdStat

variable {d : ℕ}

/-- The `ℝ^q`-valued integrand: coordinates are the killed scaled noise integrands. -/
def sa2PhiH (S : WholeMainData d) (R : ∀ N, RealizationRd d N) (N : ℕ) {q : ℕ} (ts : Fin q → ℝ)
    (φ : Fin q → Euc d → ℝ) : ℝ → (R N).Ω → (Fin N × Fin d) → EuclideanSpace ℝ (Fin q) :=
  fun r ζ k => WithLp.toLp 2 fun a =>
    killAfter (sa2Phi S (ts a) (φ a) (R N).X) (ts a) r ζ k

section Glue

variable {S : WholeMainData d} {R : ∀ N, RealizationRd d N} {MB Λ ΛV G₀ m20 C₀ : ℝ} {r mV : ℕ}
  {𝔈 : ℕ → ℝ}

theorem sa2_phiH_bound {N : ℕ} {q : ℕ} (ts : Fin q → ℝ) (φ : Fin q → Euc d → ℝ) {B : Fin q → ℝ}
    (hB0 : ∀ a, 0 ≤ B a)
    (hB : ∀ a, ∀ rr ∈ Set.Icc (0 : ℝ) (ts a), MemCb 2 (propagatorW (S.coeff N) rr (ts a) (φ a)) ∧
      cbNorm 2 (propagatorW (S.coeff N) rr (ts a) (φ a)) ≤ B a) :
    ∃ Bc : ℝ, ∀ rr ζ k, ‖sa2PhiH S R N ts φ rr ζ k‖ ≤ Bc := by
  set c : ℝ := |S.sigma N * (Real.sqrt (2 * S.invβ N) / N)| with hc
  refine ⟨∑ a, c * B a, fun rr ζ k => ?_⟩
  refine (HRS.Main.A8P.a8p_norm_le_sum_abs _).trans (Finset.sum_le_sum fun a _ => ?_)
  show |killAfter (sa2Phi S (ts a) (φ a) (R N).X) (ts a) rr ζ k| ≤ c * B a
  have hcB : 0 ≤ c * B a := mul_nonneg (abs_nonneg _) (hB0 a)
  unfold killAfter
  by_cases h1 : rr < ts a
  · rw [Set.indicator_of_mem (show rr ∈ Set.Iio (ts a) from h1)]
    simp only [sa2Phi, Pi.smul_apply, smul_eq_mul]
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (sa2_trunc_bound (hB a) (hB0 a) (R N).X rr ζ k) (abs_nonneg _)
  · rw [Set.indicator_of_notMem (show rr ∉ Set.Iio (ts a) from h1)]
    simpa using hcB

theorem sa2_phiH_isHS {N : ℕ} {ℱ : Filtration ℝ (R N).mΩ} (hprog : IsProgressive ℱ (ofNNRealTime (R N).X))
    {q : ℕ} (ts : Fin q → ℝ) (φ : Fin q → Euc d → ℝ) {B : Fin q → ℝ} (hB0 : ∀ a, 0 ≤ B a)
    (hB : ∀ a, ∀ rr ∈ Set.Icc (0 : ℝ) (ts a), MemCb 2 (propagatorW (S.coeff N) rr (ts a) (φ a)) ∧
      cbNorm 2 (propagatorW (S.coeff N) rr (ts a) (φ a)) ≤ B a) (T : ℝ) :
    IsHSIntegrand (R N).P ℱ T (sa2PhiH S R N ts φ) := by
  obtain ⟨Bc, hBc⟩ := sa2_phiH_bound (S := S) (R := R) (N := N) ts φ hB0 hB
  have hΦ : ∀ a, IsProgressiveL2 (R N).P ℱ (killAfter (sa2Phi S (ts a) (φ a) (R N).X) (ts a)) := fun a =>
    isProgressiveL2_indicator_set (R N).P (S := Set.Iio (ts a)) measurableSet_Iio
      (sa2_phi_L2 S (hB a) (hB0 a) hprog rfl)
  refine ⟨?_, fun rr ζ => Summable.of_finite, ?_⟩
  · intro k i
    letI : MeasurableSpace (Set.Iic i × (R N).Ω) := Subtype.instMeasurableSpace.prod (ℱ i)
    exact (WithLp.measurable_toLp 2 _).comp (measurable_pi_iff.2 fun a => (isProgressive_coord (hΦ a).prog k) i)
  · have hpt : ∀ rr ζ, ∑' k : Fin N × Fin d, ‖sa2PhiH S R N ts φ rr ζ k‖ₑ ^ 2 ≤
        ((N * d : ℕ) : ℝ≥0∞) * ENNReal.ofReal Bc ^ 2 := by
      intro rr ζ
      rw [tsum_fintype]
      calc ∑ k : Fin N × Fin d, ‖sa2PhiH S R N ts φ rr ζ k‖ₑ ^ 2
          ≤ ∑ _k : Fin N × Fin d, ENNReal.ofReal Bc ^ 2 := by
            refine Finset.sum_le_sum fun k _ => ?_
            refine pow_le_pow_left' ?_ 2
            rw [← ofReal_norm]
            exact ENNReal.ofReal_le_ofReal (hBc rr ζ k)
        _ = ((N * d : ℕ) : ℝ≥0∞) * ENNReal.ofReal Bc ^ 2 := by
            simp [Finset.sum_const, Finset.card_univ]
    unfold hsSqIntegralOn
    refine lt_of_le_of_lt (lintegral_mono fun ζ => lintegral_mono fun rr => hpt rr ζ) ?_
    simp only [lintegral_const, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
      Real.volume_Icc, measure_univ, mul_one]
    refine ENNReal.mul_lt_top ?_ ?_
    · exact ENNReal.mul_lt_top (ENNReal.natCast_lt_top _) (ENNReal.pow_lt_top ENNReal.ofReal_lt_top)
    · exact ENNReal.ofReal_lt_top

theorem sa2_hilbert_mart {N : ℕ} {ℱ : Filtration ℝ (R N).mΩ}
    {W' : ℝ≥0 → (R N).Ω → (Fin N × Fin d) → ℝ}
    (hF : IsWholeFilteredSolution (R N).P ℱ W' (R N).W (R N).X)
    {q : ℕ} (ts : Fin q → ℝ) (hts : ∀ a, ts a ∈ Set.Icc (0 : ℝ) S.T) (φ : Fin q → Euc d → ℝ)
    {B : Fin q → ℝ} (hB0 : ∀ a, 0 ≤ B a)
    (hB : ∀ a, ∀ rr ∈ Set.Icc (0 : ℝ) (ts a), MemCb 2 (propagatorW (S.coeff N) rr (ts a) (φ a)) ∧
      cbNorm 2 (propagatorW (S.coeff N) rr (ts a) (φ a)) ≤ B a) :
    ∃ M : ℝ → (R N).Ω → EuclideanSpace ℝ (Fin q),
      IsHilbertItoIntegral (R N).P ℱ W' (sa2PhiH S R N ts φ) M ∧
      ∀ᵐ ζ ∂(R N).P, M S.T ζ = vectorItoIntegral (R N).P ℱ W'
        (fun a => killAfter (sa2Phi S (ts a) (φ a) (R N).X) (ts a)) S.T ζ := by
  classical
  have hW : IsCylindricalBrownian (R N).P ℱ W' := gfb3_isCylindricalBrownian_of_filtration hF.brownian
  have hZ := fun T => sa2_phiH_isHS (S := S) hF.progressive ts φ hB0 hB T
  obtain ⟨Mart, hc, had, hz, hJ⟩ := gfb3_exists_hilbert_version hW hZ
  have hMart : IsHilbertItoIntegral (R N).P ℱ W' (sa2PhiH S R N ts φ) Mart := by
    refine ⟨hc, had, hz, ?_⟩
    intro τ hτ x
    obtain ⟨J, hIJ, hae⟩ := hJ x
    refine (hIJ.approx τ hτ).congr fun s => ?_
    refine lintegral_congr_ae ?_
    filter_upwards [hae τ hτ] with ζ h
    rw [h]
    rfl
  refine ⟨Mart, hMart, ?_⟩
  have hkill : ∀ a, IsProgressiveL2 (R N).P ℱ
      (killAfter (sa2Phi S (ts a) (φ a) (R N).X) (ts a)) := fun a =>
    isProgressiveL2_indicator_set (R N).P (S := Set.Iio (ts a)) measurableSet_Iio
      (sa2_phi_L2 S (hB a) (hB0 a) hF.progressive rfl)
  have hT0 : 0 ≤ S.T := S.hT.le
  have hcoord : ∀ a, ∀ᵐ ζ ∂(R N).P, (Mart S.T ζ) a = itoIntegral (R N).P ℱ W'
      (killAfter (sa2Phi S (ts a) (φ a) (R N).X) (ts a)) S.T ζ := by
    intro a
    have hfun : (fun rr ζ k => inner ℝ (sa2PhiH S R N ts φ rr ζ k)
        (EuclideanSpace.single a (1 : ℝ))) =
        killAfter (sa2Phi S (ts a) (φ a) (R N).X) (ts a) := by
      funext rr ζ k
      simp [sa2PhiH, EuclideanSpace.inner_single_right]
    have hξ' : IsProgressiveL2 (R N).P ℱ
        (fun rr ζ (k : (Finset.univ : Finset (Fin N × Fin d))) =>
          inner ℝ (sa2PhiH S R N ts φ rr ζ k) (EuclideanSpace.single a (1 : ℝ))) := by
      have h0 := gfb3_isProgressiveL2_restrict_univ (hkill a)
      rw [← hfun] at h0
      exact h0
    have := gfb3_pair_ito hF.brownian hMart (EuclideanSpace.single a (1 : ℝ)) hξ' hT0
    rw [hfun] at this
    filter_upwards [this] with ζ h
    simpa [EuclideanSpace.inner_single_right] using h
  filter_upwards [ae_all_iff.2 hcoord] with ζ h
  ext a
  exact h a

theorem sa2_hsCov_eq {N : ℕ} {q : ℕ} (ts : Fin q → ℝ) (φ : Fin q → Euc d → ℝ) (rr : ℝ)
    (ζ : (R N).Ω) :
    hsCovForm (sa2PhiH S R N ts φ rr ζ) = HRS.Main.A8P.a8pForm (sa2Sg S R N ts φ rr ζ) := by
  ext x y
  unfold hsCovForm
  rw [tsum_fintype, HRS.Main.A8P.a8pForm_apply]
  simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.smul_apply, innerSL_apply_apply, smul_eq_mul]
  have hk : ∀ k, inner ℝ (sa2PhiH S R N ts φ rr ζ k) x = ∑ a, killAfter
      (sa2Phi S (ts a) (φ a) (R N).X) (ts a) rr ζ k * x a := by
    intro k
    simp [sa2PhiH, PiLp.inner_apply, mul_comm]
  have hk' : ∀ k, inner ℝ (sa2PhiH S R N ts φ rr ζ k) y = ∑ b, killAfter
      (sa2Phi S (ts b) (φ b) (R N).X) (ts b) rr ζ k * y b := by
    intro k
    simp [sa2PhiH, PiLp.inner_apply, mul_comm]
  simp only [hk, hk', Finset.sum_mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  have := HRS.Main.A8P.a8p_killed_prod (sa2Phi S (ts a) (φ a) (R N).X)
    (sa2Phi S (ts b) (φ b) (R N).X) (ts a) (ts b) rr ζ
  have e : sa2Sg S R N ts φ rr ζ a b = ∑ k, killAfter
      (sa2Phi S (ts a) (φ a) (R N).X) (ts a) rr ζ k *
      killAfter (sa2Phi S (ts b) (φ b) (R N).X) (ts b) rr ζ k := by
    rw [this]; simp [sa2Sg, killedCovMatrix]
  rw [e, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

end Glue

end HRS.MS.MainRdStat
