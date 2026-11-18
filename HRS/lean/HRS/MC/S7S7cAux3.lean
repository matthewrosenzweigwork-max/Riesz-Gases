import HRS.MC.S7S7cAux2

/-!
# Packet `s7_S7c_hilbert_stein`, helper 3: the finite-rank Stein identity

For any family `kappa : Fin p -> NonzeroLattice d`, summing `sed_B5b_stein_centred` over `b : Fin p` with
`w = phi_{kappa b}`, `psi_b(y) = DF(iota y)[eps_{kappa b}]` gives the identity of `S7c` for the truncation
`W^kappa_N = iota (centeredStat Q (phi o kappa))`.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.S7c

open HRS HRS.Sec7 HRS.MC.SEdge HRS.StaticLimitAux

variable {d : ℕ}

/-- The finite Fourier truncation `Pi_kappa W_N = sum_a W_{N, kappa a} eps_{kappa a}`. -/
def s7c_Wtr (r : ℝ) {N p : ℕ} (Q : Measure (Config d N)) (κ : Fin p → NonzeroLattice d)
    (X : Config d N) : NegSobolev d r :=
  s7c_iota r κ (centeredStat Q (fun a => s7_phi r (κ a)) X)

theorem s7c_cs_meas {N p : ℕ} (hN : 1 ≤ N) (Q : Measure (Config d N)) (φ : Fin p → Torus d → ℝ)
    (hφ : ∀ a, Continuous (φ a)) : Measurable (centeredStat Q φ) := by
  unfold centeredStat
  refine (PiLp.continuous_toLp 2 (fun _ : Fin p => ℝ)).measurable.comp ?_
  refine measurable_pi_iff.2 fun a => ?_
  refine measurable_const.mul (Measurable.sub ?_ measurable_const)
  exact HRS.MC.SEdge.B5b.b5b_pair_meas hN (hφ a).measurable

theorem s7c_Wtr_meas {r : ℝ} {N p : ℕ} (hN : 1 ≤ N) (Q : Measure (Config d N))
    (κ : Fin p → NonzeroLattice d) : Measurable (s7c_Wtr r Q κ) := by
  unfold s7c_Wtr
  exact (s7c_iota r κ).continuous.measurable.comp
    (s7c_cs_meas hN Q _ fun a => HRS.Q66.q66_cont_of_smooth (HRS.MC.Sec7.S7a.s7a_phi_smooth r (κ a)))

theorem s7c_Wtr_eq {r : ℝ} {N p : ℕ} (Q : Measure (Config d N)) (κ : Fin p → NonzeroLattice d)
    (X : Config d N) :
    s7c_Wtr r Q κ X = ∑ a, sed_Y Q (s7_phi r (κ a)) X • s7_eps r (κ a) := by
  unfold s7c_Wtr
  rw [s7c_iota_apply]
  rfl

section Main

variable {s : ℝ} (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) {γ : ℝ} (hγ : 0 ≤ γ)
  {ρ : Torus d → ℝ} (hρ : SmoothPosDensity ρ)
include hd hs0 hs hγ hρ

theorem s7c_finite_identity {r : ℝ} {a : NonzeroLattice d → Torus d → ℝ}
    {v : NonzeroLattice d → Fin d → Torus d → ℝ} {C₀ : ℝ} (hmode : s7_ModeData d s γ ρ r a v C₀)
    {N : ℕ} (hN : 1 ≤ N) {F : NegSobolev d r → ℝ} (hF : s7_C2b F) {p : ℕ}
    (κ : Fin p → NonzeroLattice d) :
    ∫ X, fderiv ℝ F (s7c_Wtr r (sed_Q d s N γ ρ) κ X) (s7c_Wtr r (sed_Q d s N γ ρ) κ X)
        ∂(sed_Q d s N γ ρ) =
      ∑ b : Fin p, ∑ c : Fin p, ∫ X, sed_A (v (κ b)) (s7_phi r (κ c)) X *
          fderiv ℝ (fderiv ℝ F) (s7c_Wtr r (sed_Q d s N γ ρ) κ X) (s7_eps r (κ b)) (s7_eps r (κ c))
          ∂(sed_Q d s N γ ρ) -
        γ / Real.sqrt N * ∑ b : Fin p, ∫ X, sed_B d s ρ γ (v (κ b)) X *
          fderiv ℝ F (s7c_Wtr r (sed_Q d s N γ ρ) κ X) (s7_eps r (κ b)) ∂(sed_Q d s N γ ρ) := by
  obtain ⟨hF2, M1, M2, hM1, hM2, h1, h2⟩ := s7c_C2b_facts hF
  haveI hQ : IsProbabilityMeasure (sed_Q d s N γ ρ) :=
    HRS.MC.SEdge.B4b.b4b_isProb hd hs0 hs hγ hρ N hN
  have hφs : ∀ a, Torus.IsSmooth (s7_phi r (κ a)) := fun a =>
    HRS.MC.Sec7.S7a.s7a_phi_smooth r (κ a)
  have hφc : ∀ a, Continuous (s7_phi r (κ a)) := fun a => HRS.Q66.q66_cont_of_smooth (hφs a)
  set Q := sed_Q d s N γ ρ with hQdef
  set y : Config d N → EuclideanSpace ℝ (Fin p) :=
    centeredStat Q (fun a => s7_phi r (κ a)) with hy
  have hym : Measurable y := s7c_cs_meas hN Q _ hφc
  -- Step 1: B5b for each `b`
  have key : ∀ b : Fin p, ∫ X, sed_Y Q (s7_phi r (κ b)) X * s7c_psi F κ b (y X) ∂Q =
      ∑ c : Fin p, ∫ X, sed_A (v (κ b)) (s7_phi r (κ c)) X *
          fderiv ℝ (fderiv ℝ F) (s7c_Wtr r Q κ X) (s7_eps r (κ b)) (s7_eps r (κ c)) ∂Q -
        γ / Real.sqrt N * ∫ X, sed_B d s ρ γ (v (κ b)) X *
          fderiv ℝ F (s7c_Wtr r Q κ X) (s7_eps r (κ b)) ∂Q := by
    intro b
    have hint := (HRS.MC.SEdge.B4b.sed_B4b_energy_proof hd hs0 hs hγ hρ
      (hmode.smooth_v (κ b))).1 N hN
    have h := HRS.MC.SEdge.B5b.sed_B5b_stein_centred_proof hd hs0 hs hγ hρ hN
      (hmode.smooth_a (κ b)) (hmode.smooth_v (κ b)) (hmode.div (κ b)) (hmode.resp (κ b)) hint
      hφs (s7c_psi_memCb hF κ b)
    rw [h]
    congr 1
    · refine Finset.sum_congr rfl fun c _ => ?_
      refine integral_congr_ae (Filter.Eventually.of_forall fun X => ?_)
      simp only
      rw [s7c_psi_fderiv hF2 κ b c]
      have hsym : IsSymmSndFDerivAt ℝ F (s7c_iota r κ (y X)) :=
        hF2.contDiffAt.isSymmSndFDerivAt (by simp)
      rw [hsym (s7_eps r (κ c)) (s7_eps r (κ b))]
      rfl
  -- Step 2: the left-hand sides add up
  have hint_b : ∀ b : Fin p, Integrable (fun X => sed_Y Q (s7_phi r (κ b)) X *
      s7c_psi F κ b (y X)) Q := by
    intro b
    obtain ⟨c0, -, hc0⟩ := s7c_Wk_L1 (r := r) hd hs0 hs hγ hρ
    refine (hc0 N hN (κ b)).1.mul_bdd (c := M1) ?_ ?_
    · exact ((s7c_psi_memCb hF κ b).1.continuous.measurable.comp hym).aestronglyMeasurable
    · refine Filter.Eventually.of_forall fun X => ?_
      rw [Real.norm_eq_abs]
      have : ‖s7c_psi F κ b (y X)‖ ≤ M1 := by
        unfold s7c_psi
        calc ‖fderiv ℝ F (s7c_iota r κ (y X)) (s7_eps r (κ b))‖
            ≤ ‖fderiv ℝ F (s7c_iota r κ (y X))‖ * ‖s7_eps r (κ b)‖ :=
              ContinuousLinearMap.le_opNorm _ _
          _ ≤ M1 := by rw [s7c_norm_eps]; linarith [h1 (s7c_iota r κ (y X))]
      simpa [Real.norm_eq_abs] using this
  have hsum : ∑ b : Fin p, ∫ X, sed_Y Q (s7_phi r (κ b)) X * s7c_psi F κ b (y X) ∂Q =
      ∫ X, fderiv ℝ F (s7c_Wtr r Q κ X) (s7c_Wtr r Q κ X) ∂Q := by
    rw [← integral_finsetSum _ fun b _ => hint_b b]
    refine integral_congr_ae (Filter.Eventually.of_forall fun X => ?_)
    simp only
    have hW := s7c_Wtr_eq (r := r) Q κ X
    calc ∑ b : Fin p, sed_Y Q (s7_phi r (κ b)) X * s7c_psi F κ b (y X)
        = ∑ b : Fin p, sed_Y Q (s7_phi r (κ b)) X *
            fderiv ℝ F (s7c_Wtr r Q κ X) (s7_eps r (κ b)) := rfl
      _ = fderiv ℝ F (s7c_Wtr r Q κ X) (∑ b : Fin p, sed_Y Q (s7_phi r (κ b)) X • s7_eps r (κ b)) := by
          simp [map_sum, map_smul, smul_eq_mul]
      _ = _ := by rw [← hW]
  rw [← hsum]
  simp_rw [key]
  rw [Finset.sum_sub_distrib, Finset.mul_sum]

end Main

end HRS.MC.Sec7.S7c

end
