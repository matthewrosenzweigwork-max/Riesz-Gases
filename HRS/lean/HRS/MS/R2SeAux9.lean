import HRS.MS.R2SeAux8

/-!
# S9.9 `r2_static_edgeworth`, packet 9: the CLT wrapper and the plain Stein identity

Worker S99, namespace `S99`.

* `s99_clt`: for `F ∈ Bd 2` (`C²`, `‖D^i F‖ ≤ 1`), `|E F(W_N) - E F(G)| ≤ K/√N` (S4.6, `δ_N = 1/N`);
* `s99_E1_plain`: the identity (E1) for a test function of `W` alone, `ψ ∈ Bd 1`:
  `E[Y_w ψ(W)] = E[√N R_w ψ(W)] + ∑_l E[T_{wl} ∂_lψ(W)]`.
-/

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators RealInnerProductSpace ContDiff

noncomputable section

namespace S99

open S45
open HRS.Whole
open HRS (Euc cbNorm MemCb)

variable {d N : ℕ}

section Clt

variable (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) {a β γ : ℝ} (ha : 0 < a)
  (hβ : 0 < β) (hγ : 0 < γ)

include hd hs0 hs ha hβ hγ

theorem s99_clt {J : ℕ} (hJ : (d : ℝ) / 2 + 2 < J) {φ : ℕ → Euc d → ℝ}
    (hφ : IsSummableFeatureFamily J φ) {G : Measure SeqL2}
    (hG : IsCenteredGaussianSeq G (fun i j =>
      susceptibilityCov (rieszKernel d s) (thermalMeasure d s a β) γ (φ i) (φ j))) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ N : ℕ, 2 ≤ N → ∀ {F : SeqL2 → ℝ}, Bd 2 F →
      Integrable (fun X : EucConfig d N => F (featureVec φ (S46.s46_nu d s a β γ N) X))
        (S46.s46_P d s a β γ N) ∧ Integrable F G ∧
      |∫ X, F (featureVec φ (S46.s46_nu d s a β γ N) X) ∂(S46.s46_P d s a β γ N) - ∫ z, F z ∂G| ≤
        K / Real.sqrt N := by
  have hsd : s < d := by
    have : (0 : ℝ) ≤ (d : ℝ) / 2 := by positivity
    linarith
  obtain ⟨C, hC⟩ := S46.quadratic_preparation_static_proof hd hs0 hsd J hJ a a β β γ γ ha hβ hγ
  set S := featureSum J φ with hSdef
  have hS0 : 0 ≤ S := tsum_nonneg fun i => HRS.MS.Tc5.tc5_cb_nonneg J _
  refine ⟨|C| * (S + S ^ 2), by positivity, fun N hN F hF => ?_⟩
  have hSF := hC a ⟨le_rfl, le_rfl⟩ β ⟨le_rfl, le_rfl⟩ γ ⟨le_rfl, le_rfl⟩ φ hφ N hN G hG
  rw [← s99_P_eq hd hs0 hs ha hβ hγ N] at hSF
  obtain ⟨-, -, -, h4⟩ := hSF
  have hF2 : ContDiff ℝ 2 F := hF.1
  obtain ⟨i1, i2, i3⟩ := h4 F hF2 1 1 (fun z => hF.fderiv_le z) (fun z => hF.2 2 le_rfl z)
  refine ⟨i1, i2, ?_⟩
  refine i3.trans ?_
  have hδ : HRS.deltaN d s N = 1 / N := by
    have := HRS.MS.R2Mt.s92_mul_deltaN (d := d) (N := N) hs hN
    have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
    field_simp
    linarith
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hsq : Real.sqrt (HRS.deltaN d s N) = 1 / Real.sqrt N := by
    rw [hδ, Real.sqrt_div (by norm_num), Real.sqrt_one]
  rw [hsq]
  have : C * (1 / Real.sqrt N) * (S * 1 + S ^ 2 * 1) ≤ |C| * (S + S ^ 2) / Real.sqrt N := by
    have hsqN : 0 < Real.sqrt N := Real.sqrt_pos.2 hN0
    rw [show C * (1 / Real.sqrt N) * (S * 1 + S ^ 2 * 1) = C * (S + S ^ 2) / Real.sqrt N by ring]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)) hsqN.le
  exact this

end Clt

section E1p

variable (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) {a β γ C c BU Cs : ℝ} (hsd : s < d)
  (ha : 0 < a) (hβ : 0 < β) (hγ : 0 < γ) (hT : ThermalData d s a β C c BU)
  (hN : 2 ≤ N) (hS : S46.S46Static d s a β γ Cs N)

include hd hs0 hsd ha hβ hγ hT hN hS

theorem s99_E1_plain {J : ℕ} (hJ : 1 ≤ J) {φ : ℕ → Euc d → ℝ}
    (hφ : IsSummableFeatureFamily J φ) {w χ : Euc d → ℝ} {Bw : ℝ} (hw : MemCb J w)
    (hwf : S46.S46Feat d s a β γ w χ Bw) {ψ : SeqL2 → ℝ} (hψ : Bd 1 ψ) :
    ∫ X, s45_Yi N w (pair (S46.s46_nu d s a β γ N) w) X *
        ψ (featureVec φ (S46.s46_nu d s a β γ N) X) ∂(S46.s46_P d s a β γ N) =
      ∫ X, (Real.sqrt N * s45_Rp (thermalMeasure d s a β) (S46.s46_nu d s a β γ N)
          (S46.s46_P d s a β γ N) (commutatorKernel d s (gradient χ)) X) *
          ψ (featureVec φ (S46.s46_nu d s a β γ N) X) ∂(S46.s46_P d s a β γ N) +
      ∑' l, ∫ X, (γ⁻¹ * pair (empirical X) (fun x => ⟪gradient χ x, gradient (φ l) x⟫)) *
          pd ψ l (featureVec φ (S46.s46_nu d s a β γ N) X) ∂(S46.s46_P d s a β γ N) := by
  have hb : MemCb J (fun _ : Euc d => (0 : ℝ)) := (HRS.MS.Tc5.tc5_cb_const (d := d) J 0).1
  have hΨ : ContDiff ℝ 1 (fun p : SeqL2 × ℝ => ψ p.1) := hψ.1.comp contDiff_fst
  have hfd : ∀ p : SeqL2 × ℝ, fderiv ℝ (fun p : SeqL2 × ℝ => ψ p.1) p =
      (fderiv ℝ ψ p.1).comp (ContinuousLinearMap.fst ℝ SeqL2 ℝ) := by
    intro p
    have h1 : HasFDerivAt (fun p : SeqL2 × ℝ => ψ p.1) ((fderiv ℝ ψ p.1).comp
        (ContinuousLinearMap.fst ℝ SeqL2 ℝ)) p :=
      (hψ.1.differentiable one_ne_zero p.1).hasFDerivAt.comp p (hasFDerivAt_fst)
    exact h1.fderiv
  have hE := s99_E1 hd hs0 hsd ha hβ hγ hT hN hS hJ hφ hb hw hwf (Ψ := fun p : SeqL2 × ℝ => ψ p.1)
    hΨ (CΨ := 1) (DΨ := 1) (fun p => hψ.abs_le p.1) (fun p => by
      rw [hfd]
      refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
      have h1 := hψ.fderiv_le p.1
      have h2 : ‖ContinuousLinearMap.fst ℝ SeqL2 ℝ‖ ≤ 1 := ContinuousLinearMap.norm_fst_le ℝ SeqL2 ℝ
      nlinarith [norm_nonneg (fderiv ℝ ψ p.1), norm_nonneg (ContinuousLinearMap.fst ℝ SeqL2 ℝ)])
  refine hE.trans ?_
  simp only [hfd, ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_fst', map_zero, mul_zero,
    integral_zero, add_zero]
  rfl

end E1p

end S99

end
