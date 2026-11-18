import HRS.ME.FamUF1
import HRS.ME.Fourier417B

/-!
# Chunk E, packet F9a (namespace `HRS.ME.FamU`): V-uniform generator Sobolev bound

Original (copied with the convention of `docs/MAIN_E_FAMU_PLAN.md`):
* `HRS.ME.Crit.equilibriumGen_sobolev_unif` (`HRS/ME/CritUnifDecayA.lean:23`) becomes
  `HRS.ME.FamU.equilibriumGen_sobolev_unifV`. The fixed data are those of the original except `V, hV`, plus
  `Bf : ℕ → ℝ`; the constant `Cg` is chosen before `V`, and the bound holds for every smooth `V` with
  `cbNorm j V ≤ Bf j` for all `j`.

The only V-dependence of the original is the Sobolev norm `hsNorm (d/2 + (n+2) + 1) (coeffOf V)` in the constant.
It is bounded by `Cv * cbNorm ⌈m⌉₊ V ≤ Cv * max (Bf ⌈m⌉₊) 0` (lemma `hsNorm_coeffOf_le_cbNorm`, F1b), and the
constant of the statement is built from this bound `W := Cv * max (Bf ⌈m⌉₊) 0`.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

namespace HRS.ME.FamU

open HRS

variable {d : ℕ}

/-- **F9a (V-uniform copy of `equilibriumGen_sobolev_unif`).** The fixed data are `d s hs0 hsd n Lam Hr Binv`
and the bound sequence `Bf`; the constant `Cg` is chosen before `V`. -/
theorem equilibriumGen_sobolev_unifV (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d)
    (n : ℕ) (Lam Hr Binv : ℝ)
    (hLam0 : 0 ≤ Lam) (hHr : 0 ≤ Hr) (hBinv : 0 ≤ Binv) (Bf : ℕ → ℝ) :
    ∃ Cg : ℝ, 0 ≤ Cg ∧ ∀ V : Torus d → ℝ, Torus.IsSmooth V → (∀ j : ℕ, Torus.cbNorm j V ≤ Bf j) →
      ∀ (β : ℝ) (hβ : 0 < β) (ρβ : Torus d → ℝ),
      IsThermalDensity (periodicRiesz d s) V β ρβ → Torus.IsSmooth ρβ → (∀ x, 0 < ρβ x) →
      (∀ x, ρβ x ≤ Lam) →
      HRS.PDE.hsNorm ((d : ℝ) / 2 + ((n : ℝ) + 2) + 1) (HRS.PDE.coeffOf ρβ) ≤ Hr →
      |β⁻¹| ≤ Binv →
      ∀ f : Torus d → ℝ, Torus.IsSmooth f →
        sobolevNorm (n : ℝ) (HRS.PDE.equilibriumGen d s ρβ β⁻¹ f) ≤ Cg * sobolevNorm ((n : ℝ) + 2) f := by
  have hiN : (1 : ℝ) ≤ (n : ℝ) + 2 := by
    have := (Nat.cast_nonneg n : (0 : ℝ) ≤ n); linarith
  obtain ⟨Cl, hCl, hloss⟩ := HRS.PDE.MFAdjoint.exists_forwardGen_loss hd s hs0 hsd ((n : ℝ) + 2)
    ((d : ℝ) / 2 + ((n : ℝ) + 2) + 1) hiN (by linarith)
  -- the Sobolev norm of `coeffOf V` at the index `m`, uniformly in `V` (F1b)
  obtain ⟨Cv, hCv, hVbd⟩ := hsNorm_coeffOf_le_cbNorm (d := d) ((d : ℝ) / 2 + ((n : ℝ) + 2) + 1)
  obtain ⟨W, hWdef⟩ : ∃ W : ℝ, W = Cv * max (Bf ⌈(d : ℝ) / 2 + ((n : ℝ) + 2) + 1⌉₊) 0 := ⟨_, rfl⟩
  have hW0 : 0 ≤ W := by rw [hWdef]; exact mul_nonneg hCv (le_max_right _ _)
  refine ⟨(1 + Lam) * (Cl * (Hr + W) + Binv),
    mul_nonneg (by linarith) (add_nonneg (mul_nonneg hCl (add_nonneg hHr hW0)) hBinv), ?_⟩
  intro V hV hb β hβ ρβ hρβ hρS hpos hM hHρ hβi f hf
  have hVW : HRS.PDE.hsNorm ((d : ℝ) / 2 + ((n : ℝ) + 2) + 1) (HRS.PDE.coeffOf V) ≤ W := by
    have hcb : Torus.cbNorm ⌈(d : ℝ) / 2 + ((n : ℝ) + 2) + 1⌉₊ V ≤
        max (Bf ⌈(d : ℝ) / 2 + ((n : ℝ) + 2) + 1⌉₊) 0 :=
      (hb _).trans (le_max_left _ _)
    rw [hWdef]
    exact (hVbd V hV).trans (mul_le_mul_of_nonneg_left hcb hCv)
  have hM0 : 0 ≤ Lam := hLam0
  obtain ⟨D, hD⟩ : ∃ D : DynData d, D = PDE.mfData d s hs0 hsd V β hβ := ⟨_, rfl⟩
  have hDs : D.s = s := by rw [hD]; rfl
  have hDM : D.M = -1 := by rw [hD]; rfl
  have hDV : D.V = V := by rw [hD]; rfl
  have hDinv : D.invβ = β⁻¹ := by rw [hD]; rfl
  have hK : PDE.ClassicalAux.ConvKernelFacts d D.s := PDE.ClassicalAux.convKernelFacts hd D
  have hV1 : Torus.IsCk 1 V := PDE.ClassicalAux.isCk_of_le (by norm_num) hV
  have hV2 : Torus.IsCk 2 V := PDE.ClassicalAux.isCk_of_le (by norm_num) hV
  have hρ1 : Torus.IsCk 1 ρβ := PDE.ClassicalAux.isCk_of_le (by norm_num) hρS
  have hρ2 : Torus.IsCk 2 ρβ := PDE.ClassicalAux.isCk_of_le (by norm_num) hρS
  have hρC : Continuous ρβ := Torus.continuous_of_continuous_lift (ContDiff.continuous hρ1)
  have hprob : IsProbDensity ρβ := hρβ.1
  have hVH : PDE.MemHs ((d : ℝ) / 2 + ((n : ℝ) + 2) + 1) (PDE.coeffOf V) :=
    PDE.MFSemigroup.memHs_of_isSmooth hV _
  have hρH : PDE.MemHs ((d : ℝ) / 2 + ((n : ℝ) + 2) + 1) (PDE.coeffOf ρβ) :=
    PDE.MFSemigroup.memHs_of_isSmooth hρS _
  have ha := PDE.MFAdjoint.aExp_spec s hsd
  have hfC0 : Torus.IsCk 2 f := PDE.ClassicalAux.isCk_of_le (by norm_num) hf
  have hfC : Continuous f := Torus.continuous_of_continuous_lift (ContDiff.continuous hfC0)
  have hFH : PDE.MemHs ((n : ℝ) + 2) (PDE.coeffOf f) := PDE.MFSemigroup.memHs_of_isSmooth hf _
  -- the backward generator and its coefficients
  have hbgC := PDE.ClassicalPart.continuous_backwardGenerator D hK (by rw [hDV]; exact hV1) hρ1 hfC0
  have hbgc := PDE.ClassicalAux.coeffOf_backwardGenerator D hK (by rw [hDV]; exact hV1) hρ1 hfC0
  obtain ⟨φ, hφ⟩ : ∃ φ : Torus d → ℝ, φ = backwardGenerator D ρβ f := ⟨_, rfl⟩
  rw [← hφ] at hbgC hbgc
  -- the loss bound for `forwardGen F`
  have hlossF := hloss D hDs hDM ρβ hρC hρH (by rw [hDV]; exact hVH) (PDE.coeffOf f) hFH
  rw [hDinv, hDV] at hlossF
  obtain ⟨RF, hRF⟩ : ∃ R : PDE.Coeff d, R = PDE.forwardGen D ρβ (PDE.coeffOf f) -
      fun k => ((β⁻¹ : ℝ) : ℂ) * PDE.laplaceCoeff (PDE.coeffOf f) k := ⟨_, rfl⟩
  rw [← hRF] at hlossF
  obtain ⟨L, hL⟩ : ∃ L : PDE.Coeff d,
      L = fun k => ((β⁻¹ : ℝ) : ℂ) * PDE.laplaceCoeff (PDE.coeffOf f) k := ⟨_, rfl⟩
  have hLapH : PDE.MemHs (n : ℝ) L := by rw [hL]; exact (fourierTailA_lap (β⁻¹) (n : ℝ) hFH).1
  have hLapN : PDE.hsNorm (n : ℝ) L ≤ |β⁻¹| * PDE.hsNorm ((n : ℝ) + 2) (PDE.coeffOf f) := by
    rw [hL]; exact (fourierTailA_lap (β⁻¹) (n : ℝ) hFH).2
  have hRFn0 := fourierTailA_hs_mono (m := (n : ℝ)) (m' := (n : ℝ) + 2 - PDE.MFAdjoint.aExp d s)
    (by linarith [ha.2.1]) hlossF.1
  have hRFN : PDE.hsNorm (n : ℝ) RF ≤ Cl * (PDE.hsNorm ((d : ℝ) / 2 + ((n : ℝ) + 2) + 1) (PDE.coeffOf ρβ) +
      PDE.hsNorm ((d : ℝ) / 2 + ((n : ℝ) + 2) + 1) (PDE.coeffOf V)) * PDE.hsNorm ((n : ℝ) + 2) (PDE.coeffOf f) :=
    hRFn0.2.trans hlossF.2
  have hRF0 := fourierTailA_hs_mono (m := 0) (m' := (n : ℝ)) (Nat.cast_nonneg n) hRFn0.1
  have hL0 := fourierTailA_hs_mono (m := 0) (m' := (n : ℝ)) (Nat.cast_nonneg n) hLapH
  -- decomposition `forwardGen F = RF + L` (pointwise)
  have hGRL : PDE.forwardGen D ρβ (PDE.coeffOf f) = fun k => RF k + L k := by
    funext k
    rw [hRF, hL]
    simp only [Pi.sub_apply]
    ring
  have hGRLk : ∀ k, PDE.forwardGen D ρβ (PDE.coeffOf f) k = RF k + L k := fun k => congrFun hGRL k
  -- the centering constant `c = μ_β(backward generator)`
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = pair (withDensityReal ρβ) φ := ⟨_, rfl⟩
  have hEq0 := PDE.equilibrium_operator_order hd s hs0 hsd β hβ V hV2 ρβ hρβ hρ2 hpos f hfC0
  rw [← hD, ← hφ] at hEq0
  have hAF : PDE.equilibriumGen d s ρβ β⁻¹ f = fun x => φ x - c := by
    rw [← hEq0, hc]; rfl
  obtain ⟨e', he'⟩ : ∃ e' : PDE.Coeff d, ∀ k, e' k = ((-c : ℝ) : ℂ) * PDE.deltaCoeff (0 : Lattice d) k :=
    ⟨fun k => ((-c : ℝ) : ℂ) * PDE.deltaCoeff (0 : Lattice d) k, fun k => rfl⟩
  have hcdelta := fourierTailA_const_delta (d := d) (-c) (n : ℝ)
  have he'fun : e' = fun k => ((-c : ℝ) : ℂ) * PDE.deltaCoeff (0 : Lattice d) k := funext he'
  rw [← he'fun] at hcdelta
  -- coefficients of `A f`
  have hAcoef : PDE.coeffOf (PDE.equilibriumGen d s ρβ β⁻¹ f) =
      fun k => RF k + (L k + e' k) := by
    funext k
    rw [hAF]
    have hsub : PDE.coeffOf (fun x => φ x - c) k = PDE.coeffOf φ k - PDE.coeffOf (fun _ : Torus d => c) k :=
      PDE.MFApriori.coeffOf_sub φ (fun _ => c) hbgC continuous_const k
    rw [hsub, PDE.coeffOf_const, hbgc, hGRLk, he' k]
    push_cast
    ring
  have hAFMem : PDE.MemHs (n : ℝ) (PDE.coeffOf (PDE.equilibriumGen d s ρβ β⁻¹ f)) := by
    rw [hAcoef]
    exact (PDE.MFAdjoint.hs_add_le (n : ℝ) hRFn0.1 (PDE.MFAdjoint.hs_add_le (n : ℝ) hLapH hcdelta.1).1).1
  have hAFL2 : MeasureTheory.MemLp (PDE.equilibriumGen d s ρβ β⁻¹ f) 2 volume := by
    rw [hAF]; exact PDE.ClassicalAux.memLp_two_of_continuous (hbgC.sub continuous_const)
  have hAFS : MemSobolev (n : ℝ) (PDE.equilibriumGen d s ρβ β⁻¹ f) :=
    PDE.memSobolev_of_memHs _ _ hAFL2 hAFMem
  -- the centering constant `c = μ_β(backward generator)` is controlled by `‖bg f‖_{L²}`
  have hφL2 : MeasureTheory.MemLp φ 2 volume := PDE.ClassicalAux.memLp_two_of_continuous hbgC
  have hφ0 : PDE.MemHs 0 (PDE.coeffOf φ) := by
    rw [hbgc, hGRL]
    exact (PDE.MFAdjoint.hs_add_le 0 hRF0.1 hL0.1).1
  have hGN : PDE.hsNorm 0 (PDE.coeffOf φ) ≤ PDE.hsNorm 0 RF + PDE.hsNorm 0 L := by
    rw [hbgc, hGRL]
    exact (PDE.MFAdjoint.hs_add_le 0 hRF0.1 hL0.1).2
  have hsqφ := fourierTailA_integral_sq φ hφL2 hφ0
  have hL1 : ∫ y, |φ y| ≤ PDE.hsNorm 0 (PDE.coeffOf φ) := by
    have hfm : MeasureTheory.MemLp (fun y => |φ y|) (ENNReal.ofReal 2) volume := by
      rw [ENNReal.ofReal_ofNat]; exact PDE.ClassicalAux.memLp_two_of_continuous hbgC.abs
    have hgm : MeasureTheory.MemLp (fun _ : Torus d => (1 : ℝ)) (ENNReal.ofReal 2) volume := by
      rw [ENNReal.ofReal_ofNat]; exact MeasureTheory.memLp_const 1
    have H := MeasureTheory.integral_mul_le_Lp_mul_Lq_of_nonneg (μ := volume)
      Real.HolderConjugate.two_two (f := fun y => |φ y|) (g := fun _ : Torus d => (1 : ℝ))
      (Filter.Eventually.of_forall fun y => abs_nonneg _)
      (Filter.Eventually.of_forall fun _ => zero_le_one) hfm hgm
    have e1 : ∀ y, |φ y| ^ (2 : ℝ) = φ y ^ 2 := fun y => by rw [Real.rpow_two, sq_abs]
    have e2 : ∫ _ : Torus d, (1 : ℝ) = 1 := by simp
    simp only [mul_one, e1, Real.one_rpow, e2] at H
    have e3 : PDE.hsNorm 0 (PDE.coeffOf φ) = (∫ y, φ y ^ 2) ^ (1 / 2 : ℝ) := by
      unfold PDE.hsNorm
      rw [← hsqφ, Real.sqrt_eq_rpow]
    rw [e3]
    exact H
  have hcint : c = ∫ y, ρβ y * φ y := by
    rw [hc]; exact PDE.MFSemigroup.pair_withDensityReal hprob φ
  have hc0 : |c| ≤ Lam * PDE.hsNorm 0 (PDE.coeffOf φ) := by
    rw [hcint]
    calc |∫ y, ρβ y * φ y| ≤ ∫ y, |ρβ y * φ y| := MeasureTheory.abs_integral_le_integral_abs
      _ ≤ ∫ y, Lam * |φ y| := MeasureTheory.integral_mono
          (fourierTailA_integrable _ (hρC.mul hbgC).abs)
          (fourierTailA_integrable _ (continuous_const.mul hbgC.abs))
          (fun y => by
            rw [abs_mul, abs_of_pos (hpos y)]
            exact mul_le_mul_of_nonneg_right (hM y) (abs_nonneg _))
      _ = Lam * ∫ y, |φ y| := MeasureTheory.integral_const_mul _ _
      _ ≤ Lam * PDE.hsNorm 0 (PDE.coeffOf φ) := mul_le_mul_of_nonneg_left hL1 hM0
  -- assembly
  have hI := PDE.MFAdjoint.hs_add_le (n : ℝ) hLapH hcdelta.1
  have hA2 := (PDE.MFAdjoint.hs_add_le (n : ℝ) hRFn0.1 hI.1).2
  have hA3 : PDE.hsNorm (n : ℝ) e' ≤ |c| := hcdelta.2.trans (le_of_eq (abs_neg c))
  have hP1 := mul_le_mul_of_nonneg_left hGN hM0
  have hP2 := mul_le_mul_of_nonneg_left (add_le_add hRF0.2 hL0.2) hM0
  have hP3 := mul_le_mul_of_nonneg_left (add_le_add hRFN hLapN) hM0
  have hbound : PDE.hsNorm (n : ℝ) (PDE.coeffOf (PDE.equilibriumGen d s ρβ β⁻¹ f)) ≤
      (1 + Lam) * (Cl * (PDE.hsNorm ((d : ℝ) / 2 + ((n : ℝ) + 2) + 1) (PDE.coeffOf ρβ) +
        PDE.hsNorm ((d : ℝ) / 2 + ((n : ℝ) + 2) + 1) (PDE.coeffOf V)) + |β⁻¹|) *
        PDE.hsNorm ((n : ℝ) + 2) (PDE.coeffOf f) := by
    have eq : (1 + Lam) * (Cl * (PDE.hsNorm ((d : ℝ) / 2 + ((n : ℝ) + 2) + 1) (PDE.coeffOf ρβ) +
        PDE.hsNorm ((d : ℝ) / 2 + ((n : ℝ) + 2) + 1) (PDE.coeffOf V)) + |β⁻¹|) *
        PDE.hsNorm ((n : ℝ) + 2) (PDE.coeffOf f) =
        (Cl * (PDE.hsNorm ((d : ℝ) / 2 + ((n : ℝ) + 2) + 1) (PDE.coeffOf ρβ) +
          PDE.hsNorm ((d : ℝ) / 2 + ((n : ℝ) + 2) + 1) (PDE.coeffOf V)) *
          PDE.hsNorm ((n : ℝ) + 2) (PDE.coeffOf f) + |β⁻¹| * PDE.hsNorm ((n : ℝ) + 2) (PDE.coeffOf f)) +
        Lam * (Cl * (PDE.hsNorm ((d : ℝ) / 2 + ((n : ℝ) + 2) + 1) (PDE.coeffOf ρβ) +
          PDE.hsNorm ((d : ℝ) / 2 + ((n : ℝ) + 2) + 1) (PDE.coeffOf V)) *
          PDE.hsNorm ((n : ℝ) + 2) (PDE.coeffOf f) + |β⁻¹| * PDE.hsNorm ((n : ℝ) + 2) (PDE.coeffOf f)) := by
      ring
    rw [hAcoef, eq]
    linarith [hA2, hI.2, hA3, hc0, hP1, hP2, hP3, hRFN, hLapN, hRF0.2, hL0.2]
  -- replace the thermal and inverse-temperature parameters, and the norm of `V`, by their uniform bounds
  have hX0 : 0 ≤ PDE.hsNorm ((n : ℝ) + 2) (PDE.coeffOf f) := PDE.MFAdjoint.hsNorm_nonneg' _ _
  have hCl1 : Cl * (PDE.hsNorm ((d : ℝ) / 2 + ((n : ℝ) + 2) + 1) (PDE.coeffOf ρβ) +
      PDE.hsNorm ((d : ℝ) / 2 + ((n : ℝ) + 2) + 1) (PDE.coeffOf V)) ≤ Cl * (Hr + W) :=
    mul_le_mul_of_nonneg_left (by linarith) hCl
  have hfac : (1 + Lam) * (Cl * (PDE.hsNorm ((d : ℝ) / 2 + ((n : ℝ) + 2) + 1) (PDE.coeffOf ρβ) +
        PDE.hsNorm ((d : ℝ) / 2 + ((n : ℝ) + 2) + 1) (PDE.coeffOf V)) + |β⁻¹|) ≤
      (1 + Lam) * (Cl * (Hr + W) + Binv) :=
    mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  have e1 : sobolevNorm (n : ℝ) (HRS.PDE.equilibriumGen d s ρβ β⁻¹ f) =
      PDE.hsNorm (n : ℝ) (PDE.coeffOf (PDE.equilibriumGen d s ρβ β⁻¹ f)) := by
    unfold PDE.hsNorm
    rw [(PDE.hsNormSq_coeffOf (n : ℝ) _ hAFS).2,
      Real.sqrt_sq (by unfold sobolevNorm; exact Real.sqrt_nonneg _)]
  have e2 : sobolevNorm ((n : ℝ) + 2) f = PDE.hsNorm ((n : ℝ) + 2) (PDE.coeffOf f) := by
    have hfS : MemSobolev ((n : ℝ) + 2) f := PDE.MFSemigroup.memSobolev_of_isSmooth hf _
    unfold PDE.hsNorm
    rw [(PDE.hsNormSq_coeffOf ((n : ℝ) + 2) f hfS).2,
      Real.sqrt_sq (by unfold sobolevNorm; exact Real.sqrt_nonneg _)]
  rw [e1, e2]
  calc _ ≤ (1 + Lam) * (Cl * (PDE.hsNorm ((d : ℝ) / 2 + ((n : ℝ) + 2) + 1) (PDE.coeffOf ρβ) +
        PDE.hsNorm ((d : ℝ) / 2 + ((n : ℝ) + 2) + 1) (PDE.coeffOf V)) + |β⁻¹|) *
        PDE.hsNorm ((n : ℝ) + 2) (PDE.coeffOf f) := hbound
    _ ≤ (1 + Lam) * (Cl * (Hr + W) + Binv) * PDE.hsNorm ((n : ℝ) + 2) (PDE.coeffOf f) :=
      mul_le_mul_of_nonneg_right hfac hX0

end HRS.ME.FamU
