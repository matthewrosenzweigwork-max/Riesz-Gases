import HRS.MS.WsInitHAux5
import HRS.MS.QsfAsm10

/-!
# S21H packet H, part 6: the `W_1` rate for a feature law on `ℓ²` (static conclusion + coordinate second moments)

`s21h_w1_of_coords` (`ℓ²`-level): a probability measure `μ` and a Gaussian `γ` on `ℓ²`, the derivative-only comparison `S21hDerivComp`
and coordinate second moments `∫⁻ v_k² ≤ s_k` of both laws with summable `s`, whose tails over the boxes `I_Q` (`|I_Q| ≤ K Q²`) are
`∑_{k ∉ I_Q} s_k ≤ τ² Q^{-3/2}`; then `W_1^X(ι_*μ, ι_*γ) ≤ ‖ι‖ (2τ + 4√K + A₁ + A₂) δ^{3/20}` (`δ ∈ (0,1]`).

`s21h_derivComp_of_static`: `StaticFieldConclusion` (4th conjunct) gives `S21hDerivComp` for `μ = law P (featureVec φ ν)` with `η = √δ_N`,
`A₁ = C S`, `A₂ = C S²`.

`s21h_init_w1_feat`: the packaged statement for the stationary Gibbs feature law (what the S21 assembly needs from H once G supplies
`ι`, `φ`, the Gaussian `γ`, and the coordinate second-moment bounds).
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal Real

namespace HRS.MS.S21

open HRS.Whole

section Coords

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [MeasurableSpace X] [BorelSpace X]
  [SecondCountableTopology X] [CompleteSpace X]

/-- The real form of the tail bound: `(∑ s)^{1/2} ≤ τ Q^{-3/4}` from `∑ s ≤ τ² Q^{-3/2}`. -/
theorem s21h_sqrt_tail {τ Q S : ℝ} (hτ : 0 ≤ τ) (hQ : 0 < Q) (hS : S ≤ τ ^ 2 / Q ^ ((3 : ℝ) / 2)) :
    Real.sqrt S ≤ τ / Q ^ ((3 : ℝ) / 4) := by
  have hq : 0 < Q ^ ((3 : ℝ) / 4) := Real.rpow_pos_of_pos hQ _
  have e : (τ / Q ^ ((3 : ℝ) / 4)) ^ 2 = τ ^ 2 / Q ^ ((3 : ℝ) / 2) := by
    have h2 : (Q ^ ((3 : ℝ) / 4)) ^ 2 = Q ^ ((3 : ℝ) / 2) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hQ.le]; norm_num
    rw [div_pow, h2]
  refine Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
  rw [e]; exact hS

theorem s21h_w1_of_coords (ι : SeqL2 →L[ℝ] X) (μ γ : Measure SeqL2) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure γ] (hμ2 : MemLp id 2 μ) (hγ2 : MemLp id 2 γ) {δ A₁ A₂ K τ : ℝ} (hδ0 : 0 < δ)
    (hδ1 : δ ≤ 1) (hA₁ : 0 ≤ A₁) (hA₂ : 0 ≤ A₂) (hK : 0 ≤ K) (hτ : 0 ≤ τ)
    (hcomp : S21hDerivComp μ γ (Real.sqrt δ) A₁ A₂) (s : ℕ → ℝ) (hs0 : ∀ k, 0 ≤ s k) (hs : Summable s)
    (hsμ : ∀ k, ∫⁻ v, ENNReal.ofReal (SeqL2.coord v k ^ 2) ∂μ ≤ ENNReal.ofReal (s k))
    (hsγ : ∀ k, ∫⁻ v, ENNReal.ofReal (SeqL2.coord v k ^ 2) ∂γ ≤ ENNReal.ofReal (s k))
    (hbox : ∀ Q : ℕ, 1 ≤ Q → ∃ I : Finset ℕ, (I.card : ℝ) ≤ K * (Q : ℝ) ^ 2 ∧
      ∑' k : ℕ, (if k ∈ I then 0 else s k) ≤ τ ^ 2 / (Q : ℝ) ^ ((3 : ℝ) / 2)) :
    wassersteinE 1 (μ.map ι) (γ.map ι) ≤
      ENNReal.ofReal (‖ι‖ * ((2 * τ + 4 * Real.sqrt K + A₁ + A₂) * δ ^ ((3 : ℝ) / 20))) := by
  classical
  refine s21h_w1_of_subspaces ι μ γ hμ2 hγ2 hδ0 hδ1 hA₁ hA₂ hK hτ hcomp fun Q hQ => ?_
  obtain ⟨I, hI, hT⟩ := hbox Q hQ
  have hQ0 : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hsum : Summable fun k : ℕ => if k ∈ I then 0 else s k :=
    Summable.of_nonneg_of_le (fun k => by split_ifs <;> simp [hs0 k]) (fun k => by split_ifs <;> simp [hs0 k]) hs
  have hT0 : 0 ≤ ∑' k : ℕ, (if k ∈ I then 0 else s k) := tsum_nonneg fun k => by split_ifs <;> simp [hs0 k]
  have hconv : (∑' k : ℕ, if k ∈ I then (0 : ℝ≥0∞) else ENNReal.ofReal (s k)) =
      ENNReal.ofReal (∑' k : ℕ, if k ∈ I then 0 else s k) := by
    rw [ENNReal.ofReal_tsum_of_nonneg (fun k => by split_ifs <;> simp [hs0 k]) hsum]
    refine tsum_congr fun k => ?_
    split_ifs <;> simp
  have key : ∀ (ν : Measure SeqL2) [IsProbabilityMeasure ν],
      (∀ k, ∫⁻ v, ENNReal.ofReal (SeqL2.coord v k ^ 2) ∂ν ≤ ENNReal.ofReal (s k)) →
      ∫⁻ v, ‖v - (s21hSpan I).starProjection v‖ₑ ∂ν ≤ ENNReal.ofReal (τ / (Q : ℝ) ^ ((3 : ℝ) / 4)) := by
    intro ν _ hν
    refine (s21h_tail_of_coords ν I (fun k => ENNReal.ofReal (s k)) hν).trans ?_
    rw [hconv, ENNReal.ofReal_rpow_of_nonneg hT0 (by norm_num)]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [← Real.sqrt_eq_rpow]
    exact s21h_sqrt_tail hτ hQ0 hT
  exact ⟨s21hSpan I, inferInstance, by rw [s21h_finrank_span]; exact hI, key μ hsμ, key γ hsγ⟩

end Coords


section Static

variable {d N : ℕ}

/-- The fourth conjunct of `StaticFieldConclusion` is the derivative-only comparison for the feature law
(any larger nonnegative constant `C'` is allowed). -/
theorem s21h_derivComp_of_static {s : ℝ} {P : Measure (EucConfig d N)} {ν : Measure (Euc d)} {J : ℕ}
    {φ : ℕ → Euc d → ℝ} {γ : Measure SeqL2} {C C' : ℝ} (hφ : IsSummableFeatureFamily J φ)
    (hCC : C ≤ C') (hC' : 0 ≤ C') (h : StaticFieldConclusion d s N P ν J φ γ C) :
    S21hDerivComp (P.map (featureVec φ ν)) γ (Real.sqrt (HRS.deltaN d s N)) (C' * featureSum J φ)
      (C' * featureSum J φ ^ 2) := by
  obtain ⟨-, hm, -, hF⟩ := h
  have hS0 : 0 ≤ featureSum J φ := tsum_nonneg fun j => by
    unfold cbNorm
    exact Finset.sum_nonneg fun i _ => Real.iSup_nonneg fun z => norm_nonneg _
  intro F hF2 D₁ D₂ h1 h2
  obtain ⟨i1, i2, hb⟩ := hF F hF2 D₁ D₂ h1 h2
  have hFc : Continuous F := hF2.continuous
  have hD1 : 0 ≤ D₁ := (norm_nonneg (fderiv ℝ F 0)).trans (h1 0)
  have hD2 : 0 ≤ D₂ := (norm_nonneg (iteratedFDeriv ℝ 2 F 0)).trans (h2 0)
  refine ⟨?_, i2, ?_⟩
  · exact (integrable_map_measure hFc.aestronglyMeasurable hm.aemeasurable).2 i1
  · rw [integral_map hm.aemeasurable hFc.aestronglyMeasurable]
    refine hb.trans ?_
    have hbr : 0 ≤ featureSum J φ * D₁ + featureSum J φ ^ 2 * D₂ := by positivity
    have hsq := Real.sqrt_nonneg (HRS.deltaN d s N)
    calc C * Real.sqrt (HRS.deltaN d s N) * (featureSum J φ * D₁ + featureSum J φ ^ 2 * D₂)
        = Real.sqrt (HRS.deltaN d s N) * (C * (featureSum J φ * D₁ + featureSum J φ ^ 2 * D₂)) := by ring
      _ ≤ Real.sqrt (HRS.deltaN d s N) * (C' * (featureSum J φ * D₁ + featureSum J φ ^ 2 * D₂)) := by
          gcongr
      _ = _ := by ring

/-- The packaged `W_1` rate for the stationary feature law (`μ = law P (featureVec φ ν)`) and the Gaussian `γ`. -/
theorem s21h_init_w1_feat {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [MeasurableSpace X] [BorelSpace X]
    [SecondCountableTopology X] [CompleteSpace X] (ι : SeqL2 →L[ℝ] X) {s : ℝ} (hN : 1 ≤ N)
    (P : Measure (EucConfig d N)) [IsProbabilityMeasure P] (ν : Measure (Euc d)) [IsProbabilityMeasure ν]
    {J : ℕ} {φ : ℕ → Euc d → ℝ} (hφ : IsSummableFeatureFamily J φ) {γ : Measure SeqL2}
    (hγ : IsCenteredGaussian γ) {C C' : ℝ} (hCC : C ≤ C') (hC : 0 ≤ C') (hstat : StaticFieldConclusion d s N P ν J φ γ C)
    (hδ0 : 0 < HRS.deltaN d s N) (hδ1 : HRS.deltaN d s N ≤ 1) {K τ : ℝ} (hK : 0 ≤ K) (hτ : 0 ≤ τ)
    (sc : ℕ → ℝ) (hs0 : ∀ k, 0 ≤ sc k) (hs : Summable sc)
    (hsμ : ∀ k, ∫⁻ v, ENNReal.ofReal (SeqL2.coord v k ^ 2) ∂(P.map (featureVec φ ν)) ≤ ENNReal.ofReal (sc k))
    (hsγ : ∀ k, ∫⁻ v, ENNReal.ofReal (SeqL2.coord v k ^ 2) ∂γ ≤ ENNReal.ofReal (sc k))
    (hbox : ∀ Q : ℕ, 1 ≤ Q → ∃ I : Finset ℕ, (I.card : ℝ) ≤ K * (Q : ℝ) ^ 2 ∧
      ∑' k : ℕ, (if k ∈ I then 0 else sc k) ≤ τ ^ 2 / (Q : ℝ) ^ ((3 : ℝ) / 2)) :
    wassersteinE 1 ((P.map (featureVec φ ν)).map ι) (γ.map ι) ≤
      ENNReal.ofReal (‖ι‖ * ((2 * τ + 4 * Real.sqrt K + C' * featureSum J φ + C' * featureSum J φ ^ 2) *
        HRS.deltaN d s N ^ ((3 : ℝ) / 20))) := by
  haveI : IsGaussian γ := hγ.1
  have hfm : Measurable (featureVec φ ν : EucConfig d N → SeqL2) := hstat.2.1
  haveI : IsProbabilityMeasure (P.map (featureVec φ ν)) :=
    (Measure.isProbabilityMeasure_map_iff hfm.aemeasurable).2 inferInstance
  have hγ2 : MemLp id 2 γ := IsGaussian.memLp_two_id
  have hμ2 : MemLp id 2 (P.map (featureVec φ ν)) := by
    refine MemLp.of_bound aestronglyMeasurable_id (2 * Real.sqrt N * featureSum J φ) ?_
    have hae := (ae_map_iff (μ := P) hfm.aemeasurable
      (p := fun v : SeqL2 => ‖v‖ ≤ 2 * Real.sqrt N * featureSum J φ)
      (isClosed_le continuous_norm continuous_const).measurableSet).2
      (ae_of_all _ fun X => S45.s45_featureVec_norm_le hN hφ X)
    exact hae
  have hS0 : 0 ≤ featureSum J φ := tsum_nonneg fun j => by
    unfold cbNorm
    exact Finset.sum_nonneg fun i _ => Real.iSup_nonneg fun z => norm_nonneg _
  exact s21h_w1_of_coords ι _ γ hμ2 hγ2 hδ0 hδ1 (mul_nonneg hC hS0) (mul_nonneg hC (sq_nonneg _)) hK hτ
    (s21h_derivComp_of_static hφ hCC hC hstat) sc hs0 hs hsμ hsγ hbox

end Static

end HRS.MS.S21
