import HRS.MS.AdjRdWeakTerm
import HRS.MH.AdjointRdDefs

/-!
# S.A.12 L10: the four pairings of a weak solution are separately integrable
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MH.AdjointRd.Phase2SA12Limit

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MH.AdjointRd

variable {d : ℕ}

-- BEGIN SA12.L10
theorem weak_components (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d)
    (m : ℕ) (hm : 1 ≤ m) (MB Λ ΛV G₀ νbar T : ℝ)
    (χ : Euc d → ℝ) (hχ : IsUlocCutoff χ) (D : WholeDyn d) (μ : ℝ → Euc d → ℝ)
    (hD : AdjointRdData s m MB Λ ΛV G₀ νbar D T μ)
    (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) T) (φ : Euc d → ℝ)
    (G : ℝ → Euc d → ℝ) (B : ℝ)
    (hGB : ∀ τ ∈ Icc (0 : ℝ) t, ulocNormE 0 χ (G τ) ≤ ENNReal.ofReal B)
    (hw : IsWeakSol (weakOp (D.coeff μ) t) t φ G) :
    IsForwardSolutionRd (D.coeff μ) t φ G := by
  obtain ⟨hDs, -, -⟩ := hD.hs
  have hs0' : 0 ≤ D.s := by rw [hDs]; exact hs0
  have hsd' : D.s < d := by rw [hDs]; exact hsd
  have hμ : CoeffHypRd D.s m Λ T μ := by rw [hDs]; exact hD.hμ
  have hl := rieszKernel_locallyIntegrable (d := d) hs0' hsd'
  -- the three integrabilities and the identification, at each time
  have key : ∀ ψ : Euc d → ℝ, IsCcInfty ψ → ∀ σ ∈ Icc (0 : ℝ) t,
      Integrable (fun x => G σ x * Laplacian.laplacian ψ x) ∧
      Integrable (fun x => G σ x * movDiv (fun y => ψ y • (D.coeff μ).drift (t - σ) y) x) ∧
      Integrable (fun x => G σ x * nonlocalTestRd (D.coeff μ) (t - σ) ψ x) := by
    intro ψ hψ σ hσ
    have hr : t - σ ∈ Icc (0 : ℝ) T := ⟨by linarith [hσ.2], by linarith [hσ.1, ht.2]⟩
    obtain ⟨hb1, -, -, hρ1, hρ0, hρ1'⟩ :=
      HRS.MS.UniqE1.e1_coeff hd hs0' hsd' m MB Λ ΛV G₀ hD.hM hD.hV hμ hr
    have hψ2 : ContDiff ℝ 2 ψ := hψ.1.of_le (by simp)
    have hψ1 : ContDiff ℝ 1 ψ := hψ.1.of_le (by simp)
    have hB0 : ulocNormE 0 χ (G σ) ≤ ENNReal.ofReal (max B 0) :=
      (hGB σ hσ).trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))
    have hfm := HRS.MS.UniqM1.locMass_of_ulocNormE hχ (le_max_right B 0) hB0
    have hli := hfm.locallyIntegrable
    refine ⟨?_, ?_, ?_⟩
    · -- Laplacian
      have hlap : Laplacian.laplacian ψ = fun y => ∑ i, HRS.MS.UniqT3.D1 i (HRS.MS.UniqT3.D1 i ψ) y :=
        funext fun y => HRS.MS.UniqT3.lap_eq hψ2 y
      have hc : Continuous (Laplacian.laplacian ψ) := by
        rw [hlap]
        exact continuous_finsetSum _ fun i _ => HRS.MS.UniqN2b.n2b_D1D1_cont hψ2 i i
      have hcs : HasCompactSupport (Laplacian.laplacian ψ) := by
        rw [hlap]
        have := HasCompactSupport.finset_sum (s := Finset.univ)
          (f := fun i => HRS.MS.UniqT3.D1 i (HRS.MS.UniqT3.D1 i ψ)) fun i _ =>
            HRS.MS.UniqT3.D1_supp (HRS.MS.UniqT3.D1_supp hψ.2 i) i
        convert this using 1
        funext x
        simp [Finset.sum_apply]
      exact hli.integrable_smul_right_of_hasCompactSupport hc hcs
    · -- transport
      have hdr : (D.coeff μ).drift (t - σ) = meanFieldDriftW D (μ (t - σ)) := rfl
      rw [hdr]
      set v : Euc d → Euc d := meanFieldDriftW D (μ (t - σ)) with hv
      have hvc : ContDiff ℝ 1 v := contDiff_euclidean.2 hb1
      have hF1 : ContDiff ℝ 1 (fun y => ψ y • v y) := hψ1.smul hvc
      have hFc : HasCompactSupport (fun y => ψ y • v y) := hψ.2.smul_right
      have hc : Continuous (movDiv (fun y => ψ y • v y)) := by
        unfold movDiv
        refine continuous_finsetSum _ fun i _ => ?_
        have := (hF1.continuous_fderiv one_ne_zero).clm_apply
          (continuous_const (y := (EuclideanSpace.single i (1 : ℝ) : Euc d)))
        exact (EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).continuous.comp this
      have hcs : HasCompactSupport (movDiv (fun y => ψ y • v y)) := by
        have h1 := hFc.fderiv (𝕜 := ℝ)
        have := h1.comp_left (g := fun L : Euc d →L[ℝ] Euc d =>
          ∑ i, L (EuclideanSpace.single i (1 : ℝ)) i) (by simp)
        exact this
      exact hli.integrable_smul_right_of_hasCompactSupport hc hcs
    · -- nonlocal
      have hψ2' := hψ2
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
      have hI : ∀ i j : Fin d, Integrable (fun x => G σ x *
          fderiv ℝ (fun y => μ (t - σ) y * kernelConvDeriv d D.s i ψ y) x
            (EuclideanSpace.single j (1 : ℝ))) volume := fun i j =>
        HRS.MS.SA12BD.sa12_nl_integrable hs0' hsd' hρ1 hρ0 hρ1' hfm hψ2 hψ.2 i j
      have e : (fun x => G σ x * nonlocalTestRd (D.coeff μ) (t - σ) ψ x) =
          fun x => ∑ i : Fin d, ∑ j : Fin d, D.M j i * (G σ x *
            fderiv ℝ (fun y => μ (t - σ) y * kernelConvDeriv d D.s i ψ y) x
              (EuclideanSpace.single j (1 : ℝ))) := by
        funext x
        rw [hnlpt, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ => by ring
      rw [e]
      exact integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => (hI i j).const_mul _
  -- the weak term as the integral of `G σ · weakOp`
  have hterm : ∀ ψ : Euc d → ℝ, IsCcInfty ψ → ∀ σ ∈ Icc (0 : ℝ) t,
      ∫ x, G σ x * weakOp (D.coeff μ) t σ ψ x = forwardWeakTerm (D.coeff μ) t G ψ σ := by
    intro ψ hψ σ hσ
    obtain ⟨k1, k2, k3⟩ := key ψ hψ σ hσ
    unfold forwardWeakTerm weakOp
    have e : (fun x => G σ x * ((D.coeff μ).ν * Laplacian.laplacian ψ x -
        movDiv (fun y => ψ y • (D.coeff μ).drift (t - σ) y) x -
          nonlocalTestRd (D.coeff μ) (t - σ) ψ x)) =
        fun x => (D.coeff μ).ν * (G σ x * Laplacian.laplacian ψ x) -
          G σ x * movDiv (fun y => ψ y • (D.coeff μ).drift (t - σ) y) x -
            G σ x * nonlocalTestRd (D.coeff μ) (t - σ) ψ x := by
      funext x; ring
    have i1 : Integrable (fun x => (D.coeff μ).ν * (G σ x * Laplacian.laplacian ψ x)) volume :=
      k1.const_mul _
    have i12 : Integrable (fun x => (D.coeff μ).ν * (G σ x * Laplacian.laplacian ψ x) -
        G σ x * movDiv (fun y => ψ y • (D.coeff μ).drift (t - σ) y) x) volume := i1.sub k2
    rw [e, integral_sub i12 k3, integral_sub i1 k2, integral_const_mul]
  refine ⟨fun ψ hψ σ hσ => ?_, fun ψ hψ => ?_, fun ψ hψ τ hτ => ?_⟩
  · obtain ⟨k1, k2, k3⟩ := key ψ hψ σ hσ
    exact ⟨(hw.integrable_x ψ hψ σ hσ).1, k1, k2, k3⟩
  · exact (hw.integrable_σ ψ hψ).congr_fun (fun σ hσ => hterm ψ hψ σ hσ) measurableSet_Icc
  · have hsub : Icc (0 : ℝ) τ ⊆ Icc (0 : ℝ) t := Icc_subset_Icc_right hτ.2
    rw [hw.eq ψ hψ τ hτ]
    congr 1
    exact setIntegral_congr_fun measurableSet_Icc fun σ hσ => hterm ψ hψ σ (hsub hσ)
-- END SA12.L10

end HRS.MH.AdjointRd.Phase2SA12Limit
