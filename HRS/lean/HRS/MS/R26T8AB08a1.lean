import HRS.MS.R26T8AB06
import HRS.MS.R26T8AB07b
import HRS.MS.R26T8AB07c

/-!
# S8.2 T8A B08 (part 1): the block identity at one fixed terminal horizon
For `0 ≤ l ≤ h ≤ b` almost surely
`∫_{[l,h]} scalarForcing (U^{r,b}φ)(X_r) dr = -Q(h) + Q(l) + ∫_{[l,h]} V + (∫_l^h noise dW)`, in age form.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators ContDiff
namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82

set_option maxHeartbeats 12800000 in
theorem r26t8a_b08_fixed (d N : ℕ) (hd : 2 ≤ d) (hN : 2 ≤ N) (a beta m M C Cf c : ℝ)
    (ha : 0 < a) (hbeta : 0 < beta) (hM : 0 ≤ M) (hC : 0 ≤ C)
    (rho : Euc d → ℝ) (hrho : IsThermalEquilibrium d (criticalS d) a beta rho)
    (Psi : (Euc d → ℝ) → Euc d → Euc d → ℝ)
    (hPsi : r26t8a_NormalFormFamily d a beta M C rho Psi)
    (horb : r26t8a_FeatureOrbits d a beta m Cf c rho) {Omega : Type} [mOmega : MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X0 : Omega → EucConfig d N) (W : ℝ≥0 → Omega → Fin N → Euc d)
    (X : ℝ≥0 → Omega → EucConfig d N)
    (hX : IsCanonicalRealization d (criticalS d) a beta N P X0 W X)
    (F : Filtration ℝ mOmega) (W' : ℝ≥0 → Omega → Fin N × Fin d → ℝ)
    (hfilt : IsWholeFilteredSolution P F W' W X) (alpha : MultiIndex d) (b l h : ℝ)
    (hb : 0 ≤ b) (hl : 0 ≤ l) (hlh : l ≤ h) (hhb : h ≤ b) :
    ∀ᵐ w ∂P,
      (∫ r in Set.Icc l h, scalarForcing a beta rho
          (propagatorW (critCoeff d a beta rho) r b (oscTestFun m alpha)) (X r.toNNReal w)) =
        -r26t8a_QAge a beta m rho Psi alpha 0 (b - h) (X h.toNNReal w) +
          r26t8a_QAge a beta m rho Psi alpha 0 (b - l) (X l.toNNReal w) +
          (∫ r in Set.Icc l h, r26t8a_VAge a beta m rho Psi alpha 0 (b - r) (X r.toNNReal w)) +
          itoIntegral P F W' (r26t8a_clipIntegrand l h (r26t8a_noiseAge a beta m rho Psi alpha X 0 b)) h w := by
  classical
  obtain ⟨hΦ, Mrt, hMrt, hid⟩ := r26t8a_normal_form_path d N hd hN a beta m M C Cf c ha hbeta hM hC rho hrho Psi
    hPsi horb P X0 W X hX F W' hfilt alpha b hb
  have hW : IsBrownianFiltration P F W' := hfilt.brownian
  have hce := r26t8a_o06_corrNoise_eq d N hd a beta m M C Cf c rho Psi hPsi horb alpha b X
  -- the noise integrand is the clipped `noiseAge`
  have hsub : r26t8a_clipIntegrand l h (r26t8a_noiseAge a beta m rho Psi alpha X 0 b) =
      r26t8a_clipIntegrand l h (r26t8a_correctorNoise a beta m b rho Psi alpha X) := by
    rw [hce]
    funext r w i
    unfold r26t8a_clipIntegrand
    by_cases hr : r ∈ Set.Icc l h
    · rw [if_pos hr, if_pos hr, if_pos ⟨hl.trans hr.1, hr.2.trans hhb⟩]
    · rw [if_neg hr, if_neg hr]
  have hcl : IsProgressiveL2 P F (r26t8a_clipIntegrand l h (r26t8a_correctorNoise a beta m b rho Psi alpha X)) :=
    r26t8a_b03_clip_L2 hΦ l h
  have hloc := r26t8a_s07b_local P F W' hW _ hΦ l h hl hlh hcl
  have huniq := (isItoIntegral_itoIntegral hW hΦ).ae_eq_forall hW (isItoIntegral_itoIntegral hW hΦ) hΦ
  have huniq2 := (isItoIntegral_itoIntegral hW hΦ).ae_eq_forall hW hMrt hΦ
  filter_upwards [hid, hloc, huniq2] with w hw1 hw2 hw3
  obtain ⟨-, -, hw⟩ := hw1
  have h1 := hw l h hl hlh hhb
  rw [hsub, hw2 h, min_self, min_eq_right hlh, hw3 h, hw3 l]
  -- convert the integrands
  have hS : ∀ r ∈ Set.Icc l h, scalarForcing a beta rho (propagatorW (critCoeff d a beta rho) r b (oscTestFun m alpha))
      (X r.toNNReal w) = scalarForcing a beta rho (r26t8a_ageTest a beta m rho alpha 0 (b - r)) (X r.toNNReal w) :=
    fun r hr => congrFun (r26t8a_o06_prop_conv d N a beta m M C Cf c rho Psi hPsi horb alpha r b
      (hl.trans hr.1) (hr.2.trans hhb)).2.1 _
  have hV : ∀ r ∈ Set.Icc l h, r26t8a_correctedD a beta rho Psi (propagatorW (critCoeff d a beta rho) r b (oscTestFun m alpha))
      (X r.toNNReal w) - r26t8a_correctedQ a beta Psi (HRS.Whole.projGeneratorW (critCoeff d a beta rho)
        (HRS.Whole.withDensityReal rho) 0 (propagatorW (critCoeff d a beta rho) r b (oscTestFun m alpha)))
        (X r.toNNReal w) = r26t8a_VAge a beta m rho Psi alpha 0 (b - r) (X r.toNNReal w) := by
    intro r hr
    have hc := r26t8a_o06_prop_conv d N a beta m M C Cf c rho Psi hPsi horb alpha r b (hl.trans hr.1) (hr.2.trans hhb)
    rw [congrFun hc.2.2.1 (X r.toNNReal w), congrFun hc.2.2.2 (X r.toNNReal w)]
    rfl
  have hQh := congrFun (r26t8a_o06_prop_conv d N a beta m M C Cf c rho Psi hPsi horb alpha h b
    (hl.trans hlh) hhb).1 (X h.toNNReal w)
  have hQl := congrFun (r26t8a_o06_prop_conv d N a beta m M C Cf c rho Psi hPsi horb alpha l b hl
    (hlh.trans hhb)).1 (X l.toNNReal w)
  have hVint : ∫ r in Set.Icc l h, (r26t8a_correctedD a beta rho Psi
      (propagatorW (critCoeff d a beta rho) r b (oscTestFun m alpha)) (X r.toNNReal w) -
      r26t8a_correctedQ a beta Psi (HRS.Whole.projGeneratorW (critCoeff d a beta rho)
        (HRS.Whole.withDensityReal rho) 0 (propagatorW (critCoeff d a beta rho) r b (oscTestFun m alpha)))
        (X r.toNNReal w)) = ∫ r in Set.Icc l h, r26t8a_VAge a beta m rho Psi alpha 0 (b - r) (X r.toNNReal w) :=
    setIntegral_congr_fun measurableSet_Icc fun r hr => hV r hr
  beta_reduce at h1
  rw [h1, hQh, hQl, hVint]
  ring

end HRS.MS.R26T8A

end
