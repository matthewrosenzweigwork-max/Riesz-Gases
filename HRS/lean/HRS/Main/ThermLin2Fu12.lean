import HRS.Main.ThermLin2Fu11

/-!
# THERMLIN2 Fu12: a.e.-measurability in `r` of the coordinates of `ψ_r = (𝓛_r - 𝓛_β) U^{r,t} φ`
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.ThermLin.Plan2

open HRS HRS.Uniform HRS.GF HRS.AdjK HRS.T25P HRS.Uniform.Q54c

variable {d : ℕ}

open HRS.PDE HRS.PDE.MFAdjoint in
theorem tl2fu_psi_coord_ae (S : HRS.Main.PreparedData d) {ρβ : Torus d → ℝ}
    (h : IsThermalDensity (periodicRiesz d S.s) S.V S.β ρβ) (m : ℝ)
    {φ : Torus d → ℝ} (hφ : Torus.IsSmooth φ) {t : ℝ} (ht : 0 < t) (k : NonzeroLattice d) :
    AEMeasurable (fun r => NegSobolev.coord
      (lpFun m (tl2Delta S ρβ r (propagator S.dyn S.ρ r t φ))) k) (volume.restrict (Set.Icc (0 : ℝ) t)) := by
  obtain ⟨hsm, hpos⟩ := HRS.ThermLin.thermlin_thermal_smooth_pos S h
  have hd1 : 1 ≤ d := by have := S.hd; omega
  have hprob : IsProbDensity ρβ := h.1
  obtain ⟨B, -, hreg⟩ := tl2fu_psi_regular S h m hφ ht
  -- levels
  obtain ⟨q, hqdef⟩ : ∃ q : ℕ, q = PDE.mStar d + d + 3 := ⟨_, rfl⟩
  set j' : ℕ := q + 1 with hj'def
  set j : ℕ := j' + 2 with hjdef
  have hj'ms : PDE.mStar d ≤ j' := by omega
  have hjd : (d : ℝ) / 2 + 2 < (j' : ℝ) := by
    have : d + 4 ≤ j' := by omega
    have h2 : ((d + 4 : ℕ) : ℝ) ≤ j' := by exact_mod_cast this
    push_cast at h2
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  have hj : (d : ℝ) / 2 + 4 < (j : ℝ) := by rw [hjdef]; push_cast; linarith
  have hj1' : 1 ≤ j := by omega
  have h3 : 3 ≤ PDE.mStar d := PDE.ClassicalPart.three_le_mStar d
  have hjms : PDE.mStar d ≤ j := by omega
  -- moving data
  obtain ⟨R, Λ, hAtAll⟩ := tl2dy_moving S h j hj
  have hAt := hAtAll t ht
  obtain ⟨C1, hC1, hspec⟩ := propagatorCoeff_spec hd1 S.s S.hs0 S.hsd j hj1' R 1 Λ (Torus.cbNorm (j + 3) S.V)
  have hφS : MemSobolev (j : ℝ) φ := PDE.MFSemigroup.memSobolev_of_isSmooth hφ _
  have hcm : MemHs (j : ℝ) (coeffOf φ) := (PDE.hsNormSq_coeffOf _ φ hφS).1
  obtain ⟨hF, hw, -⟩ := hspec S.dyn S.β⁻¹ t S.ρ hAt t ⟨ht, le_rfl⟩ (coeffOf φ) hcm
  -- frozen data
  obtain ⟨R', MB', Λ', VB', hAfAll⟩ :=
    PDE.MFSemigroup.adjointData_frozen S.s S.hs0 S.hsd S.β S.hβ S.V S.hV ρβ hprob hsm hpos j'
  have hAf := hAfAll 0 t ht
  have hAq := StabAux.adjointData_mono (by omega : q ≤ j') hAf
  have hFc : ContinuousInHs ((q + 2 : ℕ) : ℝ) (propagatorCoeff S.dyn S.ρ (j : ℝ) t (coeffOf φ)) t :=
    forward_strong_continuity _ t _ hw _ (by rw [hjdef, hj'def]; push_cast; linarith)
  have hT1 := tl2fu_forwardGen_ae ht.le hF k.1
  have hT2 : AEMeasurable (fun r => forwardGen S.dyn ρβ
      (propagatorCoeff S.dyn S.ρ (j : ℝ) t (coeffOf φ) (t - r)) k.1) (volume.restrict (Set.Icc (0 : ℝ) t)) :=
    (tl2fu_frozen_gen_cont hd1 S.hs0 S.hsd q hAq hFc k.1).aemeasurable measurableSet_Icc
  have hg : AEMeasurable (fun r => Lattice.jp k.1 ^ m * GF.gfevRc k
      (forwardGen S.dyn (S.ρ r) (propagatorCoeff S.dyn S.ρ (j : ℝ) t (coeffOf φ) (t - r)) k.1 -
        forwardGen S.dyn ρβ (propagatorCoeff S.dyn S.ρ (j : ℝ) t (coeffOf φ) (t - r)) k.1))
      (volume.restrict (Set.Icc (0 : ℝ) t)) :=
    ((GF.gfevRc k).continuous.measurable.comp_aemeasurable (hT1.sub hT2)).const_mul _
  refine hg.congr ?_
  refine (ae_restrict_iff' measurableSet_Icc).2 (Eventually.of_forall fun r hr => ?_)
  obtain ⟨hsmr, hmemr, -⟩ := hreg r hr
  obtain ⟨-, -, -, hcont, he2, -, -⟩ := (tl2dy_moving_facts S h j' hj'ms hjd hφ ht).choose_spec.2 r hr
  have hint := PDE.ClassicalAux.integrable_of_continuous hcont
  beta_reduce
  symm
  rw [coord_lpFun hmemr, gfev_funRealCoeff_eq_rc _ hint, he2]
  rfl

end HRS.ThermLin.Plan2
