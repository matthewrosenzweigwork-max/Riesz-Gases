import HRS.MS.SA12X3W5D

/-!
# S.A.12 C5-T06 (SA12X3): `periodic_smooth_solution`

`F τ x = lift (toFun (P τ)) (L⁻¹ x)` with `P` the torus path of `sa12w2_torus_path` for the dilated data of `sa12w2_torus_data`;
`G = -perNonlocal(F)` is the dilation of the smooth torus path `-n` of `sa12x3w_nonlocal_JC`, and the time derivative of the jets
is the dilated generator identity (`sa12w2_torus_generator`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 25600000

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ComplexConjugate ContDiff

namespace HRS.MH.AdjointRd.Phase2SA12Construction

variable {d : ℕ}

open HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MH.AdjointRd HRS.PDE.SA12W2

theorem periodic_smooth_solution (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (Rg : PDE.Regime) (N : ℕ)
    (T : ℝ) (L : ℝ) (γ : Euc d → ℝ) (M : Matrix (Fin d) (Fin d) ℝ) (ν ν₀ : ℝ) (μ : ℝ → Euc d → ℝ) (V : Euc d → ℝ)
    (b : ℝ → Euc d → Euc d) (hP : PerSmooth s T L γ M ν μ V b) (hTime : PeriodicTimeSmooth T μ) (hR : RdRegimeHolds Rg d s M ν ν₀)
    (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) T) (φ : Euc d → ℝ) (hφ : ContDiff ℝ ∞ φ)
    (hφp : ∀ (x : Euc d) (k : Fin d → ℤ), φ (x + L • latticePt k) = φ x) :
    ∃ F : ℝ → Euc d → ℝ, IsPerSol N L γ M ν μ b (fun _ _ => 0) t F ∧ F 0 = φ := by
  have hL0 : 0 < L := lt_of_lt_of_le one_pos hP.hL
  obtain ⟨D₁, ρ, φ₁, hDs, hDM, hDν, hDV, hρ, hφ₁, hA, hMem, hReal⟩ :=
    sa12w2_torus_data hd s hs0 hsd T L γ M ν μ V b hP hTime t ht Rg ν₀ hR φ hφ hφp
  obtain ⟨P, hP0, hPrm, hPsm, hPjc, hPder, hPgjc, hPbg⟩ :=
    sa12w2_torus_path hd s hs0 hsd Rg D₁ (ν₀ / L ^ 2) T ρ hA t ht (PDE.coeffOf φ₁) hMem hReal
  have hu : sa12w2_JC t (fun τ => PDE.toFun (P τ)) := ⟨hPsm, hPjc⟩
  obtain ⟨n, hnJC, hnid⟩ := sa12x3w_nonlocal_JC hd hs0 hsd hL0 ht.2 hP.hγ M hTime hP.μ_smooth hP.μ_periodic hu
  set nG : ℝ → Torus d → ℝ := fun τ y => (-1 : ℝ) * n τ y with hnGdef
  have hnG : sa12w2_JC t nG := sa12w2_CC_to_JC (sa12w2_CC_const_mul (-1) (sa12w2_JC_to_CC hnJC))
  set F : ℝ → Euc d → ℝ := fun τ x => Torus.lift (PDE.toFun (P τ)) (L⁻¹ • x) with hF
  have hGeq : ∀ τ ∈ Icc (0 : ℝ) t,
      (fun y => -perNonlocal L γ M (μ τ) (F τ) y + (fun (_ : ℝ) (_ : Euc d) => (0 : ℝ)) τ y) =
        fun x => Torus.lift (nG τ) (L⁻¹ • x) := by
    intro τ hτ
    funext x
    have e : perNonlocal L γ M (μ τ) (F τ) x = Torus.lift (n τ) (L⁻¹ • x) := hnid τ hτ x
    show -perNonlocal L γ M (μ τ) (F τ) x + 0 = (-1 : ℝ) * n τ (Torus.mk (L⁻¹ • x))
    rw [e]
    show -(n τ (Torus.mk (L⁻¹ • x))) + 0 = _
    ring
  refine ⟨F, ⟨⟨fun τ hτ => ⟨sa12w2_scaled_contDiff hL0 (hPsm τ hτ), ?_⟩, fun j idx => ?_, fun j idx => ?_,
    fun j hj idx x τ hτ => ?_⟩, ?_, ?_⟩, ?_⟩
  · rw [hGeq τ hτ]; exact sa12w2_scaled_contDiff hL0 (hnG.1 τ hτ)
  · exact sa12x3w_contF_scaled hL0 hu idx
  · refine (sa12x3w_contF_scaled hL0 hnG idx).congr (fun p hp => ?_)
    show partialDeriv idx (fun y => -perNonlocal L γ M (μ p.1) (F p.1) y + (fun (_ : ℝ) (_ : Euc d) => (0 : ℝ)) p.1 y) p.2 = _
    rw [hGeq p.1 hp.1]
  · -- time derivative of the jets
    have hgen : ∀ τ ∈ Icc (0 : ℝ) t, ∀ x : Euc d,
        Torus.lift (PDE.toFun (PDE.forwardGen D₁ (ρ (t - τ)) (P τ))) (L⁻¹ • x) =
          ν * Laplacian.laplacian (F τ) x + inner ℝ (b τ x) (gradient (F τ) x) +
            (-perNonlocal L γ M (μ τ) (F τ) x + (fun (_ : ℝ) (_ : Euc d) => (0 : ℝ)) τ x) := by
      intro τ hτ x
      have h1 := sa12w2_torus_generator hd s hs0 hsd T L γ M ν μ V b hP hTime t ht D₁ ρ hDs hDM hDν hDV hρ
        (PDE.toFun (P τ)) (hPsm τ hτ) τ hτ x
      have h2 := congrFun (hPbg τ hτ) (Torus.mk (L⁻¹ • x))
      have h3 : Torus.lift (PDE.toFun (PDE.forwardGen D₁ (ρ (t - τ)) (P τ))) (L⁻¹ • x) =
          PDE.toFun (PDE.forwardGen D₁ (ρ (t - τ)) (P τ)) (Torus.mk (L⁻¹ • x)) := rfl
      rw [h3, ← h2, h1]
      show _ = _ + _ + (-perNonlocal L γ M (μ τ) (F τ) x + 0)
      simp only [hF]
      ring
    exact sa12x3w_deriv_scaled hL0 (w := fun σ => PDE.toFun (P σ))
      (W := fun τ => PDE.toFun (PDE.forwardGen D₁ (ρ (t - τ)) (P τ)))
      (Φ := fun τ y => ν * Laplacian.laplacian (F τ) y + inner ℝ (b τ y) (gradient (F τ) y) +
        (-perNonlocal L γ M (μ τ) (F τ) y + (fun (_ : ℝ) (_ : Euc d) => (0 : ℝ)) τ y))
      (fun j y τ hτ => hPder j y τ hτ) hgen idx x τ hτ
  · intro τ hτ x k
    exact sa12w2_scaled_per hL0 _ x k
  · intro τ hτ
    exact sa12w2_scaled_bddJets hL0 (hPsm τ hτ) N
  · have hcont : Continuous φ₁ :=
      Torus.continuous_of_continuous_lift (by rw [hφ₁]; exact hφ.continuous.comp (continuous_const_smul L))
    have hsum : Summable fun k => ‖PDE.coeffOf φ₁ k‖ :=
      PDE.summable_norm_of_memHs ((⌊(d : ℝ) / 2⌋₊ + 1 : ℕ) : ℝ)
        (by push_cast; linarith [Nat.lt_floor_add_one ((d : ℝ) / 2)]) _ (hMem _)
    have h0 : PDE.toFun (P 0) = φ₁ := by rw [hP0, PDE.toFun_coeffOf φ₁ hcont hsum]
    exact sa12w2_scaled_init hL0 (u := PDE.toFun (P 0)) (by rw [h0, hφ₁])

end HRS.MH.AdjointRd.Phase2SA12Construction
