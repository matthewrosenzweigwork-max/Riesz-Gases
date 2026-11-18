import HRS.Main.A8PAux24
import HRS.Main.GFB3Aux9
import HRS.Main.GFB3Aux6

/-!
# Packet A8P, part 25: the Hilbert-valued version of the vector martingale (`ℝ^q`-valued Itô integral)
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators MeasureTheory

namespace HRS.Main.A8P

open HRS.GF HRS.Uniform

variable {d : ℕ}

/-- The `ℝ^q`-valued integrand: coordinates are the killed scaled noise integrands. -/
def a8pPhiH (S : MainData d) (R : ∀ N, Realization d N) (N : ℕ) {q : ℕ} (ts : Fin q → ℝ)
    (φ : Fin q → Torus d → ℝ) : ℝ → (R N).Ω → (Fin N × Fin d) → EuclideanSpace ℝ (Fin q) :=
  fun r ω k => WithLp.toLp 2 fun a =>
    killAfter (a8pPhi (S.dyn N) (S.sigma N) (ts a) (a8pF S N ts φ a) (R N).X) (ts a) r ω k

section Glue

variable {S : MainData d} {R : ∀ N, Realization d N} {Rg : PDE.Regime} {ν₀ MB Λ VB C₀ Cc : ℝ}
  {𝔈 : ℕ → ℝ} {Ca Λ₁ : ℝ}

theorem a8p_phiH_bound (hspec : A8AdjSpec d S.s Rg MB Λ VB ν₀ Ca Λ₁) (hCa : 0 ≤ Ca)
    (hS : TorusStanding S R Rg ν₀ MB Λ VB (PDE.mStar d) C₀ Cc 𝔈) {N : ℕ} (hN : 1 ≤ N)
    {q : ℕ} (ts : Fin q → ℝ) (hts : ∀ a, ts a ∈ Set.Icc (0 : ℝ) S.T) (φ : Fin q → Torus d → ℝ)
    (hφc : ∀ a, Continuous (φ a)) (hφ : ∀ a, MemSobolev (PDE.mStar d : ℝ) (φ a)) :
    ∃ B : ℝ, ∀ r ω k, ‖a8pPhiH S R N ts φ r ω k‖ ≤ B := by
  have hpk := fun a => a8p_adj_pkg hspec hCa hS hN (hts a) (hφc a) (hφ a)
  set Bc : Fin q → ℝ := fun a => |S.sigma N| * (Real.sqrt (2 * S.invβ N) / N) *
    (Ca * a8pK Λ₁ (ts a) (φ a)) with hBc
  refine ⟨∑ a, Bc a, fun r ω k => ?_⟩
  refine (a8p_norm_le_sum_abs _).trans (Finset.sum_le_sum fun a _ => ?_)
  show |killAfter (a8pPhi (S.dyn N) (S.sigma N) (ts a) (a8pF S N ts φ a) (R N).X) (ts a) r ω k| ≤ Bc a
  have hBc0 : 0 ≤ Bc a := by
    have := a8pK_nonneg Λ₁ (ts a) (φ a)
    simp only [hBc]; positivity
  unfold killAfter
  by_cases h1 : r < ts a
  · rw [Set.indicator_of_mem (show r ∈ Set.Iio (ts a) from h1)]
    simp only [a8pPhi, empiricalNoiseIntegrand]
    by_cases h2 : r ∈ Set.Icc 0 (ts a)
    · rw [if_pos h2]
      obtain ⟨-, hcl, hb⟩ := hpk a
      obtain ⟨-, -, hcb⟩ := hb r h2
      rw [abs_mul, abs_mul, abs_div, abs_of_nonneg (Real.sqrt_nonneg _),
        abs_of_nonneg (Nat.cast_nonneg N : (0 : ℝ) ≤ N), a8p_grad_apply]
      have h3 := HRS.PDE.MFPair.abs_partialDeriv_le (L := 2) (by norm_num) (hcl.c2 r h2) k.2
        ((R N).X (Real.toNNReal r) ω k.1)
      have h4 : |Torus.partialDeriv k.2 (a8pF S N ts φ a r) ((R N).X (Real.toNNReal r) ω k.1)| ≤
          Ca * a8pK Λ₁ (ts a) (φ a) := h3.trans hcb
      simp only [hBc]
      have hc0 : 0 ≤ |S.sigma N| * (Real.sqrt (2 * S.invβ N) / N) := by positivity
      calc |S.sigma N| * (Real.sqrt (2 * S.invβ N) / N *
            |Torus.partialDeriv k.2 (a8pF S N ts φ a r) ((R N).X (Real.toNNReal r) ω k.1)|)
          = |S.sigma N| * (Real.sqrt (2 * S.invβ N) / N) *
            |Torus.partialDeriv k.2 (a8pF S N ts φ a r) ((R N).X (Real.toNNReal r) ω k.1)| := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left h4 hc0
    · rw [if_neg h2]; simpa using hBc0
  · rw [Set.indicator_of_notMem (show r ∉ Set.Iio (ts a) from h1)]
    simpa using hBc0

theorem a8p_phiH_isHS (hspec : A8AdjSpec d S.s Rg MB Λ VB ν₀ Ca Λ₁) (hCa : 0 ≤ Ca)
    (hS : TorusStanding S R Rg ν₀ MB Λ VB (PDE.mStar d) C₀ Cc 𝔈) {N : ℕ} (hN : 1 ≤ N)
    {ℱ : Filtration ℝ (R N).mΩ} (hprog : IsProgressive ℱ (ofNNRealTime (R N).X))
    {q : ℕ} (ts : Fin q → ℝ) (hts : ∀ a, ts a ∈ Set.Icc (0 : ℝ) S.T) (φ : Fin q → Torus d → ℝ)
    (hφc : ∀ a, Continuous (φ a)) (hφ : ∀ a, MemSobolev (PDE.mStar d : ℝ) (φ a)) (T : ℝ) :
    IsHSIntegrand (R N).P ℱ T (a8pPhiH S R N ts φ) := by
  obtain ⟨B, hB⟩ := a8p_phiH_bound hspec hCa hS hN ts hts φ hφc hφ
  have hΦ : ∀ a, IsProgressiveL2 (R N).P ℱ
      (killAfter (a8pPhi (S.dyn N) (S.sigma N) (ts a) (a8pF S N ts φ a) (R N).X) (ts a)) := fun a =>
    isProgressiveL2_indicator_set (R N).P (S := Set.Iio (ts a)) measurableSet_Iio
      (a8p_phi_progressive hspec hCa hS hN hprog (hts a) (hφc a) (hφ a))
  refine ⟨?_, fun r ω => Summable.of_finite, ?_⟩
  · intro k i
    letI : MeasurableSpace (Set.Iic i × (R N).Ω) := Subtype.instMeasurableSpace.prod (ℱ i)
    exact (WithLp.measurable_toLp 2 _).comp (measurable_pi_iff.2 fun a => (isProgressive_coord (hΦ a).prog k) i)
  · have hpt : ∀ r ω, ∑' k : Fin N × Fin d, ‖a8pPhiH S R N ts φ r ω k‖ₑ ^ 2 ≤
        ((N * d : ℕ) : ℝ≥0∞) * ENNReal.ofReal B ^ 2 := by
      intro r ω
      rw [tsum_fintype]
      calc ∑ k : Fin N × Fin d, ‖a8pPhiH S R N ts φ r ω k‖ₑ ^ 2
          ≤ ∑ _k : Fin N × Fin d, ENNReal.ofReal B ^ 2 := by
            refine Finset.sum_le_sum fun k _ => ?_
            refine pow_le_pow_left' ?_ 2
            rw [← ofReal_norm]
            exact ENNReal.ofReal_le_ofReal (hB r ω k)
        _ = ((N * d : ℕ) : ℝ≥0∞) * ENNReal.ofReal B ^ 2 := by
            simp [Finset.sum_const, Finset.card_univ]
    unfold hsSqIntegralOn
    refine lt_of_le_of_lt (lintegral_mono fun ω => lintegral_mono fun r => hpt r ω) ?_
    simp only [lintegral_const, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
      Real.volume_Icc, measure_univ, mul_one]
    refine ENNReal.mul_lt_top ?_ ?_
    · exact ENNReal.mul_lt_top (ENNReal.natCast_lt_top _) (ENNReal.pow_lt_top ENNReal.ofReal_lt_top)
    · exact ENNReal.ofReal_lt_top

end Glue

end HRS.Main.A8P
