import HRS.MS.R26T8AO06l
import HRS.MS.R26T8AO05a

/-!
# S8.2 T8A O06 (part m): the pathwise Itô identity of the backward corrector, in age form
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators ContDiff
namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.PDE.ToolboxRd HRS.MP.SelfSimP4Impl HRS.MH.DualityRd

set_option maxHeartbeats 12800000 in
theorem r26t8a_o06_age_identity (d N : ℕ) (hd : 2 ≤ d) (hN : 2 ≤ N) (a beta m M C Cf c : ℝ)
    (ha : 0 < a) (hbeta : 0 < beta) (hM : 0 ≤ M) (hC : 0 ≤ C)
    (rho : Euc d → ℝ) (hrho : IsThermalEquilibrium d (criticalS d) a beta rho)
    (Psi : (Euc d → ℝ) → Euc d → Euc d → ℝ)
    (hPsi : r26t8a_NormalFormFamily d a beta M C rho Psi)
    (horb : r26t8a_FeatureOrbits d a beta m Cf c rho)
    {Omega : Type} [mOmega : MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X0 : Omega → EucConfig d N) (W : ℝ≥0 → Omega → Fin N → Euc d)
    (X : ℝ≥0 → Omega → EucConfig d N)
    (hX : IsCanonicalRealization d (criticalS d) a beta N P X0 W X)
    (F : Filtration ℝ mOmega) (W' : ℝ≥0 → Omega → Fin N × Fin d → ℝ)
    (hfilt : IsWholeFilteredSolution P F W' W X)
    (alpha : MultiIndex d) (b : ℝ) (hbpos : 0 < b) :
    ∀ᵐ w ∂P,
      IntegrableOn (fun s : ℝ => -r26t8a_QAge a beta m rho Psi alpha 1 (b - s) (X s.toNNReal w) +
        r26t8a_DAge a beta m rho Psi alpha 0 (b - s) (X s.toNNReal w) -
        scalarForcing a beta rho (r26t8a_ageTest a beta m rho alpha 0 (b - s)) (X s.toNNReal w))
        (Set.Icc 0 b) ∧
      ∀ t ∈ Set.Icc (0 : ℝ) b,
        r26t8a_QAge a beta m rho Psi alpha 0 (b - t) (X t.toNNReal w) =
          r26t8a_QAge a beta m rho Psi alpha 0 b (X 0 w) +
          (∫ s in Set.Icc 0 t, (-r26t8a_QAge a beta m rho Psi alpha 1 (b - s) (X s.toNNReal w) +
            r26t8a_DAge a beta m rho Psi alpha 0 (b - s) (X s.toNNReal w) -
            scalarForcing a beta rho (r26t8a_ageTest a beta m rho alpha 0 (b - s)) (X s.toNNReal w))) +
          itoIntegral P (p4r_shiftFil F) W' (r26t8a_correctorNoise a beta m b rho Psi alpha X) t w := by
  classical
  set D := quadraticGradientDyn d (criticalS d) a beta with hD
  have hnu : 0 ≤ D.invβ := by show 0 ≤ beta⁻¹; positivity
  have hDsol : IsWholeStrongSolution P D b X0 W X := hX.solution b
  have hDrift : Measurable (fun Y : EucConfig d N => particleDriftW D Y) := r26t8a_o06_drift_meas d N a beta
  have hT : 0 ≤ b := hbpos.le
  set ℱ' := p4r_shiftFil F with hℱ'
  have hW : IsBrownianFiltration P ℱ' W' := p4r_shiftFil_brownian hfilt.brownian
  have had0 : Measurable[F 0] (X 0) := hfilt.adapted 0
  have hprog : IsProgressive ℱ' (ofNNRealTime X) := r26t8a_o05a3_prog_shift hfilt.progressive had0
  have hX₀ : ∀ t : ℝ, Measurable[ℱ' t] (X 0) := fun t =>
    had0.mono (F.mono (le_max_right t 0)) le_rfl
  have hb : IsProgressive ℱ' (ofNNRealTime (fun (s : ℝ≥0) (ξ : Omega) => particleDriftW D (X s ξ))) :=
    fun i => hDrift.comp (hprog i)
  have hZint : ∀ᵐ ζ ∂P, ∀ τ : ℝ≥0, (τ : ℝ) ≤ b →
      X τ ζ = X 0 ζ + (∫ s in Set.Icc (0 : ℝ) τ, particleDriftW D (X (Real.toNNReal s) ζ))
        + ∑ k, (W' τ ζ k - W' 0 ζ k) • noiseDir D k := by
    filter_upwards [hDsol.eqn, hfilt.coords] with ζ h1 h2 τ hτ
    obtain ⟨hI, h1⟩ := h1 τ hτ
    have e : ∀ k : Fin N × Fin d, W' τ ζ k - W' 0 ζ k
        = (fun l => W τ ζ l - W 0 ζ l) k.1 k.2 := by
      intro k
      have h3 := h2 τ k.1 k.2
      have h4 := h2 0 k.1 k.2
      rw [Prod.mk.eta] at h3 h4
      rw [h3, h4]
      simp
    funext i
    have hsum : (∑ k : Fin N × Fin d, (W' τ ζ k - W' 0 ζ k) • noiseDir D k) i
        = Real.sqrt (2 * D.invβ) • (W τ ζ i - W 0 ζ i) := by
      simp only [e]
      exact da4_sum_noiseDir_apply D (fun l => W τ ζ l - W 0 ζ l) i
    have hIi : Integrable (fun s : ℝ => particleDriftW D (X (Real.toNNReal s) ζ))
        (volume.restrict (Set.Icc 0 (τ : ℝ))) := integrable_pi_iff.2 hI
    simp only [Pi.add_apply]
    rw [hsum, da4_integral_apply _ i hIi, ← h1 i]
  have hbint : ∀ᵐ ζ ∂P, IntegrableOn (fun s : ℝ => particleDriftW D (X (Real.toNNReal s) ζ))
      (Set.Icc 0 b) := by
    filter_upwards [hDsol.eqn] with ζ h1
    have htt : ((Real.toNNReal b : ℝ≥0) : ℝ) = b := Real.coe_toNNReal b hT
    obtain ⟨hI, -⟩ := h1 (Real.toNNReal b) (le_of_eq htt)
    rw [htt] at hI
    exact integrable_pi_iff.2 hI
  set f : ℝ → EucConfig d N → ℝ := fun r => r26t8a_QAge (N := N) a beta m rho Psi alpha 0 (b - r) with hfdef
  obtain ⟨hf, -⟩ := r26t8a_backward_corrector_c12 d N hd hN a beta m M C Cf c ha hbeta hM hC rho hrho Psi hPsi horb
    alpha b hbpos
  have hfilt' : IsWholeFilteredSolution P ℱ' W' W X :=
    ⟨hW, hfilt.coords, fun t => by
      have := hfilt.adapted t
      rwa [← p4r_shiftFil_nnreal] at this, hprog⟩
  obtain ⟨-, hL2', -⟩ := r26t8a_noise_regular d N hd hN a beta m M C Cf c ha hbeta hM hC rho hrho Psi hPsi horb
    P X0 W X hX ℱ' W' hfilt' alpha 0 (by norm_num)
  have hΦe : itoIntegrand b (eucCollisionSet d N)ᶜ f (ofNNRealTime X) (fun _ _ => noiseDir D) =
      r26t8a_correctorNoise a beta m b rho Psi alpha X :=
    (r26t8a_o06_Phi_eq d N hd a beta m M C Cf c hC rho Psi hPsi horb alpha b X).trans
      (r26t8a_o06_corrNoise_eq d N hd a beta m M C Cf c rho Psi hPsi horb alpha b X).symm
  have hΦcore : IsProgressiveL2 P ℱ' (itoIntegrand b (eucCollisionSet d N)ᶜ f (ofNNRealTime X)
      (fun _ _ => noiseDir D)) := by
    rw [hΦe, r26t8a_o06_corrNoise_eq d N hd a beta m M C Cf c rho Psi hPsi horb alpha b X]
    exact hL2' b hT
  have hcore := r26t8a_o06_ito_coll P hW hT f hf (noiseDir D) X hDsol.adapted hX₀
    (fun (s : ℝ≥0) (ξ : Omega) => particleDriftW D (X s ξ)) hb hbint hZint hDsol.no_collision hΦcore
  obtain ⟨-, -, hDc, -⟩ := r26t8a_normal_age_FTC d N hd hN a beta m M C Cf c ha hbeta hM hC rho hrho Psi hPsi horb
    alpha 0 (by norm_num)
  have hQ1 := r26t8a_o06_QAge_cont d N hd hN a beta m M C Cf c ha hbeta hM hC rho hrho Psi hPsi horb alpha 1
    (by norm_num)
  filter_upwards [hcore, hDsol.cont, hDsol.no_collision] with w hc hcont hnc
  have hXc : Continuous fun s : ℝ => X s.toNNReal w := (continuous_pi hcont).comp continuous_real_toNNReal
  have hUw : ∀ s ∈ Set.Icc (0 : ℝ) b, X s.toNNReal w ∉ eucCollisionSet d N := fun s hs =>
    hnc s.toNNReal (by rw [Real.coe_toNNReal _ hs.1]; exact hs.2)
  have hpath : ContinuousOn (fun s : ℝ => (b - s, X s.toNNReal w)) (Set.Icc 0 b) :=
    ((continuous_const.sub continuous_id).prodMk hXc).continuousOn
  have hmaps : Set.MapsTo (fun s : ℝ => (b - s, X s.toNNReal w)) (Set.Icc 0 b)
      (Set.Ici 0 ×ˢ (eucCollisionSet d N)ᶜ) := fun s hs => ⟨sub_nonneg.2 hs.2, hUw s hs⟩
  have hdrift : ∀ s ∈ Set.Icc (0 : ℝ) b,
      itoDrift b f (ofNNRealTime X) (ofNNRealTime (fun (s : ℝ≥0) (ξ : Omega) => particleDriftW D (X s ξ)))
        (fun _ _ => noiseDir D) s w =
      -r26t8a_QAge a beta m rho Psi alpha 1 (b - s) (X s.toNNReal w) +
        r26t8a_DAge a beta m rho Psi alpha 0 (b - s) (X s.toNNReal w) -
        scalarForcing a beta rho (r26t8a_ageTest a beta m rho alpha 0 (b - s)) (X s.toNNReal w) :=
    fun s hs => r26t8a_o06_drift_eq d N hd hN a beta m M C Cf c ha hbeta hM hC rho hrho Psi hPsi horb alpha b hbpos
      X w s hs (hUw s hs)
  refine ⟨?_, fun t ht => ?_⟩
  · have := (hc b ⟨hT, le_rfl⟩).1
    exact this.congr_fun hdrift measurableSet_Icc
  · obtain ⟨-, hE⟩ := hc t ht
    rw [hΦe] at hE
    have hint : ∫ s in Set.Icc 0 t, itoDrift b f (ofNNRealTime X)
        (ofNNRealTime (fun (s : ℝ≥0) (ξ : Omega) => particleDriftW D (X s ξ))) (fun _ _ => noiseDir D) s w =
        ∫ s in Set.Icc 0 t, (-r26t8a_QAge a beta m rho Psi alpha 1 (b - s) (X s.toNNReal w) +
          r26t8a_DAge a beta m rho Psi alpha 0 (b - s) (X s.toNNReal w) -
          scalarForcing a beta rho (r26t8a_ageTest a beta m rho alpha 0 (b - s)) (X s.toNNReal w)) :=
      setIntegral_congr_fun measurableSet_Icc fun s hs => hdrift s ⟨hs.1, hs.2.trans ht.2⟩
    rw [hint] at hE
    have e0 : f 0 (X 0 w) = r26t8a_QAge a beta m rho Psi alpha 0 b (X 0 w) := by
      simp only [hfdef, sub_zero]
    rw [e0] at hE
    exact hE

end HRS.MS.R26T8A

end
