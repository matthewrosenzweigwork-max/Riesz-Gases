import HRS.MS.MfeConfAux151

/-!
# S.B.1 (SB5), packet R3c (part 2): the a priori bound along one conditioned flow

For a probability measure `P` for which `SbMovEnt` holds, the coarse commutator bound and the logarithmic normaliser identity
give the Gronwall bound `u(t) + 1 ≤ (u(0) + 1) exp(α ∫ K)` for
`u(t) = H(P∘X_t⁻¹|Q_t) - log K_t + βN C_E` (`sb1_pj_gronwall`).
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory InformationTheory
open HRS HRS.Whole
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.MfeConf

variable {d N : ℕ}

/-- the constant `C_E` with `En ≥ -C_E` -/
def sb1CE (d : ℕ) (s Cρ M1 : ℝ) : ℝ := sb1CG d s Cρ M1 + sb1kap s * M1

theorem sb1CE_nonneg {s : ℝ} {ρ0 : Euc d → ℝ} {Cρ M1 : ℝ} (R : Sb1Rho ρ0 Cρ M1) : 0 ≤ sb1CE d s Cρ M1 := by
  unfold sb1CE
  have := sb1CG_nonneg (s := s) R
  have := sb1kap_nonneg s
  have := R.M1_nonneg
  positivity

theorem sb1_En_lower (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (hN : 1 ≤ N) {ρ0 : Euc d → ℝ} {Cρ M1 : ℝ}
    (R : Sb1Rho ρ0 Cρ M1) (X : Whole.EucConfig d N) :
    -sb1CE d s Cρ M1 ≤ sb1En (Whole.rieszKernel d s) ρ0 X := by
  have h := sb1_E_le hd hs0 hsd hN (β := 1) zero_le_one (sb1KerU_riesz d s hs0) R X
  have h2 := Real.exp_le_exp.1 h
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  unfold sb1CE
  nlinarith

section One

variable {D : Whole.WholeDyn d} {T C B C3 : ℝ} {ρ : ℝ → Euc d → ℝ} (H : Sb1Tr3 D T C B C3 ρ)

include H

/-- entropy against `Q_t` controls the modulated energy: `βN ∫ En ≤ H(ν|Q_t) - log K_t` -/
theorem sb1_pj_ent (hN : 1 ≤ N) (hβ : 0 < D.invβ) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T)
    {ν : Measure (Whole.EucConfig d N)} [IsProbabilityMeasure ν] (hν : relEntropy ν (sb1Q D N ρ t) ≠ ⊤) :
    Integrable (sb1En (Whole.rieszKernel d D.s) (ρ t) : Whole.EucConfig d N → ℝ) ν ∧
      D.invβ⁻¹ * N * ∫ X, sb1En (Whole.rieszKernel d D.s) (ρ t) X ∂ν ≤
        (relEntropy ν (sb1Q D N ρ t)).toReal -
          Real.log (Whole.gibbsNormalizer (Whole.rieszKernel d D.s) N D.invβ⁻¹ (Whole.withDensityReal (ρ t))) := by
  have hd := H.tr.hd
  have hs0 := H.tr.hs0
  have hsd := H.tr.hsd
  have hβ0 : 0 < D.invβ⁻¹ := inv_pos.2 hβ
  have R := H.rho hd ht
  have hk := sb1KerU_riesz d D.s hs0
  obtain ⟨h1, h2⟩ := sb1_Q_conv hd hs0 hsd hN hβ0 hk R hν
  refine ⟨h2, ?_⟩
  obtain ⟨-, h3⟩ := sb1_kl_Q hd hs0 hsd hN hβ0.le hk R h1 h2
  have h4 : 0 ≤ (relEntropy ν (Measure.pi fun _ : Fin N => Whole.withDensityReal (ρ t))).toReal := ENNReal.toReal_nonneg
  unfold sb1Q
  linarith

/-- the coarse commutator bound `|C_N| ≤ K (a En + b)` on collision-free configurations -/
def Sb1Coarse (D : Whole.WholeDyn d) (N : ℕ) (T : ℝ) (ρ : ℝ → Euc d → ℝ) (a b : ℝ) : Prop :=
  0 < a ∧ 0 ≤ b ∧
    ∀ r ∈ Set.Icc (0 : ℝ) T, ∀ Kr : ℝ, 0 ≤ Kr →
      (∀ x y, ‖Whole.mfeTransportW D (ρ r) x - Whole.mfeTransportW D (ρ r) y‖ ≤ Kr * ‖x - y‖) →
      ∀ Z : Whole.EucConfig d N, (∀ i j, i ≠ j → Z i ≠ Z j) →
        |sb1CN D N ρ r Z| ≤ Kr * (a * sb1En (Whole.rieszKernel d D.s) (ρ r) Z + b)

end One

theorem sb1_coll_ae {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : ℝ≥0 → Ω → Whole.EucConfig d N}
    (hXm : ∀ t, Measurable (X t)) {T : ℝ}
    (hnc : ∀ᵐ ζ ∂P, ∀ t : ℝ≥0, (t : ℝ) ≤ T → X t ζ ∉ eucCollisionSet d N) {r : ℝ} (hr : r ∈ Set.Icc (0 : ℝ) T) :
    ∀ᵐ Z ∂(P.map (X r.toNNReal)), ∀ i j, i ≠ j → Z i ≠ Z j := by
  have hm : MeasurableSet {Z : Whole.EucConfig d N | ∀ i j, i ≠ j → Z i ≠ Z j} := by
    have : {Z : Whole.EucConfig d N | ∀ i j, i ≠ j → Z i ≠ Z j} = (eucCollisionSet d N)ᶜ := by
      ext Z; simp [eucCollisionSet]
    rw [this]
    refine MeasurableSet.compl ?_
    have h2 : eucCollisionSet d N = ⋃ i : Fin N, ⋃ j : Fin N, ⋃ _ : i ≠ j, {X : Whole.EucConfig d N | X i = X j} := by
      ext X; simp [eucCollisionSet]
    rw [h2]
    refine MeasurableSet.iUnion fun i => MeasurableSet.iUnion fun j => MeasurableSet.iUnion fun _ => ?_
    exact measurableSet_eq_fun (measurable_pi_apply i) (measurable_pi_apply j)
  rw [ae_map_iff (hXm _).aemeasurable hm]
  filter_upwards [hnc] with ζ hζ i j hij heq
  exact hζ r.toNNReal (by rw [Real.coe_toNNReal r hr.1]; exact hr.2) ⟨i, j, hij, heq⟩


end HRS.MS.MfeConf
