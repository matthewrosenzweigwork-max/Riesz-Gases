import HRS.MS.TiltAux12

/-!
# S4.7 packet P8: `tilt_static_osc` (oscillator field)

Copy of `QprepAux14` (itself a copy of `QsfOsc7`, `QsfOsc8`) for the tilted preparation: the Hermite family of `B_m` is summable in
`C_b^J` (`m > J + 2d`), its sum `S` is independent of `(a, β, γ₀, ε)`, so the constant `max C₁ 0 (S + S²)` is uniform.
-/

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators RealInnerProductSpace ContDiff

noncomputable section

namespace S47

open S45
open HRS.Whole
open HRS (Euc cbNorm MemCb)

variable {d : ℕ}

theorem s47_cov_smul (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {ρ : Euc d → ℝ} {q γ C c BU BB : ℝ}
    {Bd : Euc d → Euc d} (hγ : 0 < γ) (hT : TRef d s ρ q C c BU BB Bd) {φ ψ : Euc d → ℝ}
    (hφ : MemLp φ 2 (withDensityReal ρ)) (hψ : MemLp ψ 2 (withDensityReal ρ))
    (c₁ c₂ : ℝ) :
    susceptibilityCov (rieszKernel d s) (withDensityReal ρ) γ (fun x => c₁ * φ x)
        (fun x => c₂ * ψ x) =
      c₁ * c₂ * susceptibilityCov (rieszKernel d s) (withDensityReal ρ) γ φ ψ := by
  have hd1 : 1 ≤ d := by omega
  haveI : IsProbabilityMeasure (withDensityReal ρ) :=
    HRS.Whole.Q34.isProbabilityMeasure_nu hT.prob
  obtain ⟨L, hL⟩ := s47_logmoment2 hT
  have hM : ∀ x, ρ x ≤ C := fun x => (le_abs_self _).trans
    ((hT.h0 x).trans (by
      have : Real.exp (-c * ‖x‖ ^ 2) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith [sq_nonneg ‖x‖, hT.hc])
      nlinarith [hT.C0]))
  obtain ⟨K, hK⟩ : ∃ K : Lp ℝ 2 (withDensityReal ρ) →L[ℝ] Lp ℝ 2 (withDensityReal ρ),
      IsKData (withDensityReal ρ) (rieszKernel d s) K :=
    s45_kdata hd1 hs0 hsd hT.prob hM (L := L) (fun _ => hL)
  rw [s45_susceptibilityCov_eq hK hγ (hφ.const_mul c₁) (hψ.const_mul c₂),
    s45_susceptibilityCov_eq hK hγ hφ hψ, s45_U_smul hφ c₁, s45_U_smul hψ c₂, map_smul,
    inner_smul_left, inner_smul_right]
  simp only [conj_trivial]
  ring


theorem tilt_static_osc_proof : type_of% @HRS.Whole.tilt_static_osc := by
  intro d s hd hs0 hsd J hJ m hm am ap βm βp γm γp ham hβm hγm ψ
  by_cases hr : am ≤ ap ∧ βm ≤ βp ∧ γm ≤ γp
  swap
  · exact ⟨0, fun a ha β hβ γ hγ => absurd ⟨ha.1.trans ha.2, hβ.1.trans hβ.2, hγ.1.trans hγ.2⟩ hr⟩
  obtain ⟨hap, hβp, hγp⟩ := hr
  have hd1 : 1 ≤ d := by omega
  obtain ⟨C1, Cs', hCs', hC1⟩ := s47_conclusion hd hs0 hsd J hJ am ap βm βp γm γp ham hβm hγm ψ
  obtain ⟨Cs, Ct, ct, BU, BB, KR, KT, hCs0, hKR, hKT, hsuAll⟩ :=
    s47_setup hd hs0 hsd ham hβm hγm hap hβp hγp ψ
  obtain ⟨e⟩ := s45_exists_enum hd1
  have hJ1 : 1 ≤ J := by
    have : (0 : ℝ) ≤ (d : ℝ) / 2 := by positivity
    have h1 : (1 : ℝ) ≤ J := by linarith
    exact_mod_cast h1
  have hmd : (d : ℝ) < m := by
    have : (0 : ℝ) ≤ J := Nat.cast_nonneg _
    have : (0 : ℝ) < d := by exact_mod_cast hd1
    linarith
  have hφ : HRS.Whole.IsSummableFeatureFamily J (fun j : ℕ => oscTestFun m (e j)) :=
    s45_summable_oscTest hd1 J hm e
  set S := featureSum J (fun j : ℕ => oscTestFun m (e j)) with hSdef
  have hS0 : 0 ≤ S := tsum_nonneg fun i => HRS.MS.Tc5.tc5_cb_nonneg J _
  refine ⟨max C1 0 * (S + S ^ 2), ?_⟩
  intro a ha β hβ γ hγ ε hε N hN Zg hZg
  have ha0 : 0 < a := ham.trans_le ha.1
  have hβ0 : 0 < β := hβm.trans_le hβ.1
  have hγ0 : 0 < γ := hγm.trans_le hγ.1
  have hN1 : 1 ≤ N := by omega
  obtain ⟨Bd, hsu⟩ := hsuAll a ha β hβ γ hγ ε hε
  set ρ : Euc d → ℝ := perturbedDensity (thermalDensity d s a β) ε ψ with hρdef
  have hSN := hsu.hS N hN
  haveI hP : IsProbabilityMeasure (s47_P d s ρ γ N) := hSN.prob
  have hPeq := s47_P_eq hd1 hs0 hsd hsu.hT.hc hsu.hT.C0 hsu.hT.prob hsu.hT.smooth.continuous hsu.hT.pos
    hsu.hT.h0 hγ0 N
  have hPeq' : s47_P d s ρ γ N =
      modulatedGibbs (rieszKernel d s) N γ (tiltedMeasure d s a β ε ψ) := hPeq
  rw [← hPeq']
  set P := s47_P d s ρ γ N with hPdef
  haveI : IsProbabilityMeasure (withDensityReal ρ) :=
    HRS.Whole.Q34.isProbabilityMeasure_nu hsu.hT.prob
  -- the Gaussian on `ℓ²`
  have hmem : ∀ α : MultiIndex d, MemLp (hermiteFunD α) 2 (withDensityReal ρ) := by
    intro α
    obtain ⟨C0, hC0⟩ := hermiteFunD_uniform_bound (d := d)
    exact MemLp.of_bound (contDiff_hermiteFunD α).continuous.aestronglyMeasurable C0
      (Filter.Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hC0 α x)
  have hZg' : IsCenteredGaussianSeq (Zg.map (s45_Psi m e)) fun i j => susceptibilityCov
      (rieszKernel d s) (withDensityReal ρ) γ (oscTestFun m (e i)) (oscTestFun m (e j)) := by
    have h := s45_gauss_transport e hZg
    convert h using 3 with i j
    have := s47_cov_smul hd hs0 hsd hγ0 hsu.hT (hmem (e i)) (hmem (e j))
      (oscEigenvalue d (e i) ^ (-(m / 2))) (oscEigenvalue d (e j) ^ (-(m / 2)))
    exact this
  have hC1' := (hC1 a ha β hβ γ hγ ε hε (fun j : ℕ => oscTestFun m (e j)) hφ N hN
    (Zg.map (s45_Psi m e)) hZg').1
  obtain ⟨hk1, hk2, hk3, hk4⟩ := hC1'
  have hzeta : ∀ X : EucConfig d N, zetaB m P X =
      (s45_Psi m e).symm (featureVec (fun j : ℕ => oscTestFun m (e j)) (firstMarginal P) X) := by
    intro X
    rw [← s45_Psi_zetaB hmd e hφ P hSN.exch hN1 X]
    simp
  have hmeas : Measurable (zetaB m P : EucConfig d N → OscDual d m) := by
    have : (zetaB m P : EucConfig d N → OscDual d m) = fun X => (s45_Psi m e).symm
        (featureVec (fun j : ℕ => oscTestFun m (e j)) (firstMarginal P) X) := funext hzeta
    rw [this]
    exact (s45_Psi m e).symm.continuous.measurable.comp hk2
  refine ⟨hmeas, ?_⟩
  unfold HRS.smoothDist
  refine Real.iSup_le (fun Φ => ?_) (by positivity)
  obtain ⟨hΦ1, hΦ2⟩ := s45_unit_ball_bounds' Φ.2
  have hΦc : ContDiff ℝ 2 Φ.1 := Φ.2.1
  set F : SeqL2 → ℝ := fun z => Φ.1 ((s45_Psi m e).symm z) with hF
  have hFc : ContDiff ℝ 2 F := hΦc.comp (s45_Psi m e).symm.contDiff
  have hD1 : ∀ z, ‖fderiv ℝ F z‖ ≤ 1 := fun z => by
    rw [← norm_iteratedFDeriv_one]
    have := LinearIsometryEquiv.norm_iteratedFDeriv_comp_right (s45_Psi m e).symm Φ.1 z (i := 1)
    rw [show F = Φ.1 ∘ (s45_Psi m e).symm from rfl, this, norm_iteratedFDeriv_one]
    exact hΦ1 _
  have hD2 : ∀ z, ‖iteratedFDeriv ℝ 2 F z‖ ≤ 1 := fun z => by
    have := LinearIsometryEquiv.norm_iteratedFDeriv_comp_right (s45_Psi m e).symm Φ.1 z (i := 2)
    rw [show F = Φ.1 ∘ (s45_Psi m e).symm from rfl, this]
    exact hΦ2 _
  obtain ⟨-, -, hbound⟩ := hk4 F hFc 1 1 hD1 hD2
  have e1 : ∫ z, Φ.1 z ∂(HRS.law P (zetaB m P)) = ∫ X, F (featureVec (fun j : ℕ => oscTestFun m (e j))
      (firstMarginal P) X) ∂P := by
    unfold HRS.law
    rw [integral_map hmeas.aemeasurable Φ.2.1.continuous.aestronglyMeasurable]
    refine integral_congr_ae (Filter.Eventually.of_forall fun X => ?_)
    simp only [hzeta, hF]
  have e2 : ∫ z, F z ∂(Zg.map (s45_Psi m e)) = ∫ u, Φ.1 u ∂Zg := by
    rw [integral_map (s45_Psi m e).continuous.measurable.aemeasurable hFc.continuous.aestronglyMeasurable]
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    simp [hF]
  rw [e1, ← e2]
  refine hbound.trans ?_
  have hδ0 : 0 ≤ Real.sqrt (HRS.deltaN d s N) := Real.sqrt_nonneg _
  have h1 : C1 ≤ max C1 0 := le_max_left _ _
  have h2 : 0 ≤ Real.sqrt (HRS.deltaN d s N) * (S * 1 + S ^ 2 * 1) := by positivity
  nlinarith [mul_le_mul_of_nonneg_right h1 h2]


end S47

end
