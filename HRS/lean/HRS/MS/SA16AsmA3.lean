import HRS.MS.SA16TransferT8

/-!
# S.A.16 A3: `classical_initial_membership`

At `τ = 0` the integrated weak equation gives equal compact-test pairings of `F 0` and `φ`.  `F 0` lies in
`W^{m,p}` (hence is locally integrable) and the `C²` datum is locally integrable; distributional
identification gives `F 0 = φ` almost everywhere, and `wNormE` is invariant under a.e. changes.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16Assembly
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16Transfer

theorem classical_initial_membership (d m : ℕ) (p t : ℝ) [Fact (2 ≤ p)]
    (ht : 0 ≤ t) (coeff : WholeCoeff d) (φ : Euc d → ℝ) (hφ : ContDiff ℝ 2 φ)
    (F : ℝ → Euc d → ℝ) (hF : IsForwardSolutionRd coeff t φ F)
    (hF₀ : wNormE m p (F 0)<⊤) : wNormE m p φ<⊤ := by
  -- a lift of `F 0`
  obtain ⟨G, hGrep, -⟩ := (Phase2SA16Transfer.jet_restriction_and_finite_lift d m m le_rfl p).2
    (F 0) hF₀
  have hGrep' : ∀ᵐ x ∂(volume : Measure (Euc d)),
      ((G : WLp d m p) : Euc d → (WIndex d m → ℝ)) x (wZero d m) = F 0 x := hGrep
  -- local integrability of `F 0`
  have hP : MemLp (fun x => ((G : WLp d m p) : Euc d → (WIndex d m → ℝ)) x (wZero d m))
      (ENNReal.ofReal p) (volume : Measure (Euc d)) := by
    have hG' := Lp.memLp (G : WLp d m p)
    exact (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : WIndex d m => ℝ) (wZero d m)).comp_memLp' hG'
  have hloc : LocallyIntegrable (fun x => ((G : WLp d m p) : Euc d → (WIndex d m → ℝ)) x (wZero d m))
      (volume : Measure (Euc d)) :=
    hP.locallyIntegrable (by
      have : (1 : ℝ) ≤ p := by linarith [Fact.out (p := 2 ≤ p)]
      simpa using ENNReal.ofReal_le_ofReal this)
  have hlocF : LocallyIntegrable (F 0) (volume : Measure (Euc d)) :=
    hloc.congr hGrep'
  have hlocφ : LocallyIntegrable φ (volume : Measure (Euc d)) :=
    (hφ.continuous).locallyIntegrable
  -- equal pairings against compactly supported smooth tests
  have hae : ∀ᵐ x ∂(volume : Measure (Euc d)), F 0 x = φ x := by
    refine ae_eq_of_integral_contDiff_smul_eq hlocF hlocφ fun ψ hψ hψs => ?_
    have h := hF.eq ψ ⟨hψ, hψs⟩ 0 ⟨le_rfl, ht⟩
    have h0 : ∫ σ in Icc (0 : ℝ) 0, forwardWeakTerm coeff t F ψ σ = 0 := by
      simp
    rw [h0, add_zero] at h
    simpa [smul_eq_mul, mul_comm] using h
  -- finiteness of `wNormE` is invariant under a.e. changes
  have hle : wNormE m p φ ≤ wNormE m p (F 0) := by
    unfold wNormE
    refine le_iInf₂ fun G' hG' => ?_
    refine iInf₂_le_of_le G' ?_ le_rfl
    filter_upwards [hG', hae] with x hx1 hx2
    rw [hx1, hx2]
  exact lt_of_le_of_lt hle hF₀

end HRS.Whole.AppendixA.Phase2SA16Assembly
