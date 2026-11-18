import HRS.MS.R26T8AO05a3

/-!
# S8.2 observed-time layer, packet T8A.O05a: Itô's formula for a whole-space strong solution (additive noise)

Packet statement `r26t8a_whole_ito_additive`.  The coordinate strong equation is assembled into the vector equation (as in
`empirical_ito_rd_proof`), native `ito_formula_additive` is applied on the negative-time shifted filtration `p4r_shiftFil`, and the
drift/Hessian terms are identified with `particleGenerator` through the helpers `O05a1`, `O05a2`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators
namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.PDE.ToolboxRd HRS.MP.SelfSimP4Impl HRS.MH.DualityRd

theorem r26t8a_whole_ito_additive (d N : ℕ) (D : WholeDyn d) (hnu : 0≤D.invβ)
    (hDrift : Measurable (fun Y : EucConfig d N => particleDriftW D Y)) (T : ℝ) (hT : 0≤T)
    {Omega : Type} [mOmega : MeasurableSpace Omega] (P : Measure Omega) [IsProbabilityMeasure P]
    (X0 : Omega → EucConfig d N) (W : ℝ≥0 → Omega → Fin N → Euc d)
    (X : ℝ≥0 → Omega → EucConfig d N) (hX : IsWholeStrongSolution P D T X0 W X)
    (F : Filtration ℝ mOmega) (W' : ℝ≥0 → Omega → (Fin N×Fin d) → ℝ)
    (hfilt : IsWholeFilteredSolution P F W' W X)
    (f : ℝ → EucConfig d N → ℝ) (hf : IsC12On T Set.univ f) :
    ∃ Mrt : ℝ → Omega → ℝ,
      IsLocalItoIntegral P (HRS.MP.SelfSimP4Impl.p4r_shiftFil F) W'
        (r26t8a_clipIntegrand 0 T
          (fun r w i => Real.sqrt (2*D.invβ)*HRS.MS.Phase2S82.configGrad (f r) (X r.toNNReal w) i.1 i.2)) Mrt ∧
      ∀ᵐ w ∂P, ∀ t∈Set.Icc 0 T,
        f t (X t.toNNReal w)=f 0 (X 0 w)+
          (∫ r in Set.Icc 0 t, derivWithin (fun u => f u (X r.toNNReal w)) (Set.Icc 0 T) r+
            particleGenerator D (f r) (X r.toNNReal w))+Mrt t w := by
  set ℱ' := p4r_shiftFil F with hℱ'
  have hW : IsBrownianFiltration P ℱ' W' := p4r_shiftFil_brownian hfilt.brownian
  have had0 : Measurable[F 0] (X 0) := hfilt.adapted 0
  have hprog : IsProgressive ℱ' (ofNNRealTime X) := r26t8a_o05a3_prog_shift hfilt.progressive had0
  have hX₀ : ∀ t : ℝ, Measurable[ℱ' t] (X 0) := fun t =>
    had0.mono (F.mono (le_max_right t 0)) le_rfl
  have hb : IsProgressive ℱ' (ofNNRealTime (fun (s : ℝ≥0) (ξ : Omega) => particleDriftW D (X s ξ))) :=
    fun i => hDrift.comp (hprog i)
  have hZint : ∀ᵐ ζ ∂P, ∀ τ : ℝ≥0, (τ : ℝ) ≤ T →
      X τ ζ = X 0 ζ + (∫ s in Set.Icc (0 : ℝ) τ, particleDriftW D (X (Real.toNNReal s) ζ))
        + ∑ k, (W' τ ζ k - W' 0 ζ k) • noiseDir D k := by
    filter_upwards [hX.eqn, hfilt.coords] with ζ h1 h2 τ hτ
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
      (Set.Icc 0 T) := by
    filter_upwards [hX.eqn] with ζ h1
    have htt : ((Real.toNNReal T : ℝ≥0) : ℝ) = T := Real.coe_toNNReal T hT
    obtain ⟨hI, -⟩ := h1 (Real.toNNReal T) (le_of_eq htt)
    rw [htt] at hI
    exact integrable_pi_iff.2 hI
  have hito := ito_formula_additive (P := P) (ℱ := ℱ') hW hT f hf (noiseDir D) X hX.adapted hX₀
    (fun (s : ℝ≥0) (ξ : Omega) => particleDriftW D (X s ξ)) hb hbint hZint
  have hΦeq : itoIntegrand T Set.univ f (ofNNRealTime X) (fun _ _ => noiseDir D) =
      r26t8a_clipIntegrand 0 T
        (fun r w i => Real.sqrt (2*D.invβ)*HRS.MS.Phase2S82.configGrad (f r) (X r.toNNReal w) i.1 i.2) := by
    funext s ξ k
    simp only [itoIntegrand, r26t8a_clipIntegrand, ofNNRealTime_apply, Set.mem_univ, Set.setOf_true,
      Set.indicator_univ]
    by_cases hs : s ∈ Set.Icc (0 : ℝ) T
    · rw [Set.indicator_of_mem hs, if_pos hs]
      exact r26t8a_o05a2_noise D (f s) (fun y => hf.hasFDerivAt s hs y (Set.mem_univ _))
        (X (Real.toNNReal s) ξ) k.1 k.2
    · rw [Set.indicator_of_notMem hs, if_neg hs]
  have hXc : ∀ᵐ ζ ∂P, Continuous fun t => ofNNRealTime X t ζ := by
    filter_upwards [hX.cont] with ζ hc
    exact continuous_ofNNRealTime _ ζ (continuous_pi hc)
  have hΦ0 : IsProgressiveLocL2E P ℱ' (fun (_ : ℝ) (_ : Omega) => noiseDir (N := N) D) := by
    refine ⟨isProgressive_const ℱ' _, fun T => ae_of_all _ fun ω => ?_⟩
    rw [lintegral_const]
    exact ENNReal.mul_lt_top (by simp) (by simp)
  have hΦ := isProgressiveLocL2_itoIntegrand (P := P) Set.univ isClosed_univ Set.univ
    (Set.Subset.refl _) f hf (ofNNRealTime X) hprog hXc _ hΦ0
  refine ⟨localItoIntegral P ℱ' W' (itoIntegrand T Set.univ f (ofNNRealTime X) (fun _ _ => noiseDir D)),
    ?_, ?_⟩
  · rw [← hΦeq]
    exact isLocalItoIntegral_localItoIntegral hW hΦ
  · filter_upwards [hito] with w hw t ht
    obtain ⟨-, hEq⟩ := hw
    have h := hEq t.toNNReal (by rw [Real.coe_toNNReal _ ht.1]; exact ht.2)
    rw [Real.coe_toNNReal _ ht.1] at h
    rw [h]
    congr 2
    refine setIntegral_congr_fun measurableSet_Icc fun r hr => ?_
    have hr' : r ∈ Set.Icc (0 : ℝ) T := ⟨hr.1, hr.2.trans ht.2⟩
    have hF1 : ∀ y, HasFDerivAt (f r) (fderiv ℝ (f r) y) y := fun y =>
      hf.hasFDerivAt r hr' y (Set.mem_univ _)
    have hF2 := hf.hasFDerivAt_fderiv r hr' (X r.toNNReal w) (Set.mem_univ _)
    simp only [itoDrift, ofNNRealTime_apply]
    rw [r26t8a_o05a2_drift D (f r) hF1, r26t8a_o05a2_hess D hnu (f r) hF1 _ hF2]
    unfold particleGenerator
    ring

end HRS.MS.R26T8A

end
