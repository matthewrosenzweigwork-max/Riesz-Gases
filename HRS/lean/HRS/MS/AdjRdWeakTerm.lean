import HRS.Whole.AppendixAAdjoint
import HRS.MS.UniqN1cA
import HRS.MS.UniqE1b
import HRS.MS.UniqM1Fin

/-!
# S.A.12 U1: the weak integrand of `IsForwardSolutionRd` equals the S.A.33 `forwardPairing`

The nonlocal term of `forwardWeakTerm` is the integral of `F σ` against the finite sum `nonlocalTestRd`;
the term of `forwardPairing` is the finite sum of the integrals.  The two agree because each
summand `F σ · ∂_j(ρ' · H_i)` is integrable (local `L²` mass of `F σ` and the decay of `ρ'`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.SA12BD

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas

variable {d : ℕ}

/-- Each summand of the nonlocal pairing is integrable against a function of bounded local mass. -/
theorem sa12_nl_integrable {D : WholeDyn d} (hs0 : 0 ≤ D.s) (hsd : D.s < d)
    {ρ' : Euc d → ℝ} (hρ : ContDiff ℝ 1 ρ') {Cρ : ℝ}
    (hρ0 : ∀ y, |ρ' y| ≤ Cρ * (1 + ‖y‖) ^ (-((d : ℝ) + 3)))
    (hρ1 : ∀ y, ‖fderiv ℝ ρ' y‖ ≤ Cρ * (1 + ‖y‖) ^ (-((d : ℝ) + 3)))
    {A : ℝ} {f : Euc d → ℝ} (hf : HRS.MS.UniqM1.LocMass A f)
    {ψ : Euc d → ℝ} (hψ : ContDiff ℝ 2 ψ) (hψc : HasCompactSupport ψ) (i j : Fin d) :
    Integrable (fun x => f x * fderiv ℝ (fun y => ρ' y * kernelConvDeriv d D.s i ψ y) x
      (EuclideanSpace.single j (1 : ℝ))) volume := by
  have hρc : Continuous ρ' := hρ.continuous
  have hDρ : ∀ j, Continuous (HRS.MS.UniqT3.D1 j ρ') := fun j =>
    (hρ.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hHc : ∀ i, Continuous (kernelConvDeriv d D.s i ψ) := fun i =>
    HRS.MS.UniqT3.K_cont hs0 hsd (HRS.MS.UniqT3.D1_contDiff hψ i).continuous
      (HRS.MS.UniqT3.D1_supp hψc i)
  have I1 : Integrable (fun y => f y * (HRS.MS.UniqT3.D1 j ρ' y * kernelConvDeriv d D.s i ψ y)) volume := by
    obtain ⟨C1, hC1⟩ := HRS.MS.UniqT3.conv_bound hs0 hsd (HRS.MS.UniqT3.D1_contDiff hψ i).continuous
      (HRS.MS.UniqT3.D1_supp hψc i)
    exact HRS.MS.UniqT3.key_int hf.1 (A ^ 2) hf.2 ((hDρ j).mul (hHc i)).aestronglyMeasurable (Cρ * C1)
      (HRS.MS.UniqN2b.n2b_wt_dom
        (fun y => (HRS.MS.UniqN2b.n2b_D1_le j ρ' y).trans (hρ1 y)) (fun y => hC1 y))
  have I2 : Integrable (fun y => f y * (ρ' y *
      HRS.MS.UniqT3.D1 j (kernelConvDeriv d D.s i ψ) y)) volume := by
    obtain ⟨C1, hC1⟩ := HRS.MS.UniqT3.conv_bound hs0 hsd (HRS.MS.UniqN2b.n2b_D1D1_cont hψ i j)
      (HRS.MS.UniqT3.D1_supp (HRS.MS.UniqT3.D1_supp hψc i) j)
    refine HRS.MS.UniqT3.key_int hf.1 (A ^ 2) hf.2
      (hρc.mul (HRS.MS.UniqN1c.n1c_D1_kcd_cont hs0 hsd hψ hψc i j)).aestronglyMeasurable
      (Cρ * C1) (HRS.MS.UniqN2b.n2b_wt_dom hρ0 (fun y => ?_))
    rw [HRS.MS.UniqN1c.n1c_D1_kcd hs0 hsd hψ hψc]
    exact hC1 y
  have e : (fun x => f x * fderiv ℝ (fun y => ρ' y * kernelConvDeriv d D.s i ψ y) x
      (EuclideanSpace.single j (1 : ℝ))) =
      fun y => f y * (HRS.MS.UniqT3.D1 j ρ' y * kernelConvDeriv d D.s i ψ y) +
        f y * (ρ' y * HRS.MS.UniqT3.D1 j (kernelConvDeriv d D.s i ψ) y) := by
    funext y
    rw [HRS.MS.UniqN2b.n2b_fderiv_prod hs0 hsd hρ hψ hψc i j y,
      ← HRS.MS.UniqN1c.n1c_D1_kcd hs0 hsd hψ hψc i j y]
    ring
  rw [e]
  exact I1.add I2

theorem sa12_weak_term_bridge (d : ℕ) (hd : 1 ≤ d) (s : ℝ)
    (hs0 : 0 ≤ s) (hsd : s < d) (m : ℕ) (hm : 1 ≤ m)
    (MB Λ ΛV G₀ νbar T : ℝ) (χ : Euc d → ℝ) (hχ : IsUlocCutoff χ)
    (D : WholeDyn d) (μ : ℝ → Euc d → ℝ)
    (hD : AdjointRdData s m MB Λ ΛV G₀ νbar D T μ)
    (t : ℝ) (ht : t ∈ Set.Ioc (0 : ℝ) T)
    (ψ : Euc d → ℝ) (hψ : IsCcInfty ψ)
    (F : ℝ → Euc d → ℝ) (σ : ℝ) (hσ : σ ∈ Set.Icc (0 : ℝ) t)
    (hF : ulocNormE 0 χ (F σ) < ⊤) :
    forwardWeakTerm (D.coeff μ) t F ψ σ =
      forwardPairing D μ t σ (F σ) ψ := by
  obtain ⟨hDs, -, -⟩ := hD.hs
  have hr : t - σ ∈ Set.Icc (0 : ℝ) T := ⟨by linarith [hσ.2], by linarith [hσ.1, ht.2]⟩
  have hs0' : 0 ≤ D.s := by rw [hDs]; exact hs0
  have hsd' : D.s < d := by rw [hDs]; exact hsd
  have hμ : CoeffHypRd D.s m Λ T μ := by rw [hDs]; exact hD.hμ
  obtain ⟨hb1, -, -, hρ1, hρ0, hρ1'⟩ :=
    HRS.MS.UniqE1.e1_coeff hd hs0' hsd' m MB Λ ΛV G₀ hD.hM hD.hV hμ hr
  have hψ2 : ContDiff ℝ 2 ψ := hψ.1.of_le (by simp)
  have hψ1 : ContDiff ℝ 1 ψ := hψ.1.of_le (by simp)
  have hl := rieszKernel_locallyIntegrable (d := d) hs0' hsd'
  -- local mass of `F σ`
  set B : ℝ := (ulocNormE 0 χ (F σ)).toReal with hB
  have hle : ulocNormE 0 χ (F σ) ≤ ENNReal.ofReal B := by
    rw [hB, ENNReal.ofReal_toReal hF.ne]
  have hfm := HRS.MS.UniqM1.locMass_of_ulocNormE hχ ENNReal.toReal_nonneg hle
  -- the nonlocal test function, pointwise
  have hnlpt : ∀ x, nonlocalTestRd (D.coeff μ) (t - σ) ψ x =
      ∑ i : Fin d, ∑ j : Fin d, D.M j i *
        fderiv ℝ (fun y => μ (t - σ) y * kernelConvDeriv d D.s i ψ y) x
          (EuclideanSpace.single j (1 : ℝ)) := by
    intro x
    unfold nonlocalTestRd
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    have hg : ∀ y, gradient (HRS.Whole.convFun (rieszKernel d D.s) ψ) y i =
        kernelConvDeriv d D.s i ψ y := by
      intro y
      rw [q09_gradient_apply]
      exact HRS.MS.UniqT3.convFun_D1 hl hψ1 hψ.2 i y
    show D.M j i * partialDeriv (fun _ : Fin 1 => j)
      (fun y => μ (t - σ) y * gradient (HRS.Whole.convFun (rieszKernel d D.s) ψ) y i) x = _
    congr 1
    simp only [hg]
    unfold partialDeriv
    rw [iteratedFDeriv_one_apply]
  -- the integrated nonlocal term
  have hI : ∀ i j : Fin d, Integrable (fun x => F σ x *
      fderiv ℝ (fun y => μ (t - σ) y * kernelConvDeriv d D.s i ψ y) x
        (EuclideanSpace.single j (1 : ℝ))) volume := fun i j =>
    sa12_nl_integrable hs0' hsd' hρ1 hρ0 hρ1' hfm hψ2 hψ.2 i j
  have hnl : ∫ x, F σ x * nonlocalTestRd (D.coeff μ) (t - σ) ψ x =
      HRS.MS.UniqNDefs.nMain D (μ (t - σ)) (F σ) ψ := by
    unfold HRS.MS.UniqNDefs.nMain
    have e : ∀ x, F σ x * nonlocalTestRd (D.coeff μ) (t - σ) ψ x =
        ∑ i : Fin d, ∑ j : Fin d, D.M j i * (F σ x *
          fderiv ℝ (fun y => μ (t - σ) y * kernelConvDeriv d D.s i ψ y) x
            (EuclideanSpace.single j (1 : ℝ))) := by
      intro x
      rw [hnlpt, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    have e' : (fun x => F σ x * nonlocalTestRd (D.coeff μ) (t - σ) ψ x) =
        fun x => ∑ i : Fin d, ∑ j : Fin d, D.M j i * (F σ x *
          fderiv ℝ (fun y => μ (t - σ) y * kernelConvDeriv d D.s i ψ y) x
            (EuclideanSpace.single j (1 : ℝ))) := funext e
    rw [e', integral_finsetSum _ (fun i _ => integrable_finsetSum _
      (fun j _ => (hI i j).const_mul _))]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_finsetSum _ (fun j _ => (hI i j).const_mul _)]
    exact Finset.sum_congr rfl fun j _ => integral_const_mul _ _
  -- the transport term, pointwise
  have hmov : ∀ x, movDiv (fun y => ψ y • meanFieldDriftW D (μ (t - σ)) y) x =
      ∑ i : Fin d, fderiv ℝ (fun y => meanFieldDriftW D (μ (t - σ)) y i * ψ y) x
        (EuclideanSpace.single i (1 : ℝ)) := by
    intro x
    unfold movDiv
    refine Finset.sum_congr rfl fun i _ => ?_
    have hdiff : DifferentiableAt ℝ (fun y => ψ y • meanFieldDriftW D (μ (t - σ)) y) x := by
      refine DifferentiableAt.smul (hψ1.differentiable (by norm_num) x) ?_
      exact differentiableAt_euclidean.2 fun k => ((hb1 k).differentiable (by norm_num)) x
    have h1 := (EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).hasFDerivAt.comp x hdiff.hasFDerivAt
    have h2 : fderiv ℝ (fun y => meanFieldDriftW D (μ (t - σ)) y i * ψ y) x =
        (EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).comp
          (fderiv ℝ (fun y => ψ y • meanFieldDriftW D (μ (t - σ)) y) x) := by
      have : (fun y => meanFieldDriftW D (μ (t - σ)) y i * ψ y) =
          fun y => (EuclideanSpace.proj i : Euc d →L[ℝ] ℝ)
            (ψ y • meanFieldDriftW D (μ (t - σ)) y) := by
        funext y; simp [mul_comm]
      rw [this]; exact h1.fderiv
    rw [h2]; rfl
  rw [HRS.MS.UniqNDefs.forwardPairing_eq]
  unfold forwardWeakTerm
  have hν : (D.coeff μ).ν = D.invβ := rfl
  have hdr : (D.coeff μ).drift (t - σ) = meanFieldDriftW D (μ (t - σ)) := rfl
  rw [hν, hdr]
  simp only [hmov]
  rw [hnl]

end HRS.MS.SA12BD
