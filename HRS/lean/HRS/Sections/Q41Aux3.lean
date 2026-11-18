import HRS.PDE.MeanField
import HRS.PDE.MeanFieldPairSeries
import HRS.PDE.MeanFieldLinearLoss
import HRS.Equilibrium.StaticLimits
import HRS.Equilibrium.FieldSingAux
import HRS.Sections.Q41Aux2

/-!
# Packet Q41, helper 3: the stationary kernel of the linearized field is nondegenerate and mixing

For the frozen (equilibrium) data `(V, ρ_β)` of the torus (`d ≥ 2`, smooth positive thermal density)
and a fixed smooth test function `φ` (a real Fourier mode), the stationary covariance
`ρ(u) = C_β(φ, S_β(u)φ)` (`PDE.stationaryLagCov` entries with equal tests) satisfies
`ρ(0) > 0` and `ρ(u) → 0` (`q41_kernel_data`).  Inputs: Prop 5.1 / 5.2 machinery
(`exists_frozen_l2_decay`, `exists_inverse`, `susceptibilityCov_eq_inner`, `cov_symm`).
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace HRS.Q41

open HRS HRS.PDE HRS.PDE.MFAdjoint HRS.PDE.MFLinear

variable {d : ℕ}

/-- Positivity and mixing of the stationary kernel `u ↦ C_β(φ, S_β(u)φ)` for a nondegenerate test. -/
theorem q41_kernel_data_aux (hd : 1 ≤ d) {s β c₀ Λ₀ : ℝ} {V ρβ : Torus d → ℝ}
    (H : FrozenHyp d s (2 * mStar d + 4) β⁻¹ β⁻¹ c₀ Λ₀ β V ρβ)
    {φ : Torus d → ℝ} (hφc : Continuous φ) (hφm : MemSobolev ((mStar d : ℝ) + 4) φ)
    (hnd : ¬ (projMean (withDensityReal ρβ) φ =ᵐ[withDensityReal ρβ] 0)) :
    ∃ ρ : ℝ → ℝ, 0 < ρ 0 ∧ Tendsto ρ atTop (𝓝 0) ∧ ∀ u : ℝ, 0 ≤ u →
      susceptibilityCov (periodicRiesz d s) (withDensityReal ρβ) β φ (Sg H u φ) = ρ u ∧
      susceptibilityCov (periodicRiesz d s) (withDensityReal ρβ) β (Sg H u φ) φ = ρ u := by
  have h3 := ClassicalPart.three_le_mStar d
  have hKS := KS_of_frozen hd H
  have hρc : Continuous ρβ := H.cont (by omega)
  haveI : IsProbabilityMeasure (withDensityReal ρβ) := hKS.isProb
  obtain ⟨R, hRA, hAR, hRs, hRpos⟩ := exists_inverse hd s H.hs0 H.hsd hKS hρc β H.hβ.le
  have hco := ALp_coercive hd s H.hs0 H.hsd hKS hρc β H.hβ.le
  have cont1 : ∀ {f : Torus d → ℝ}, Torus.IsCk 2 f → Continuous f := fun hf =>
    MFAux.continuous_of_isCk (hf.of_le (by norm_num))
  have hSdata : ∀ u : ℝ, 0 ≤ u → Continuous (Sg H u φ) ∧ pair (withDensityReal ρβ) (Sg H u φ) = 0 := by
    intro u hu
    obtain ⟨c2, pz, -⟩ := frozen_path_data hd H hφc hφm (T' := u + 1) (by linarith)
    exact ⟨cont1 (c2 u ⟨hu, by linarith⟩), pz u ⟨hu, by linarith⟩⟩
  have hy : ∀ u : ℝ, 0 ≤ u →
      ⇑(pL (withDensityReal ρβ) (fun v => Sg H v φ) u) =ᵐ[withDensityReal ρβ]
        projMean (withDensityReal ρβ) (Sg H u φ) := by
    intro u hu
    rw [projMean_of_pair_zero (hSdata u hu).2]
    exact pL_ae (hSdata u hu).1
  have hy0 : ⇑(pL (withDensityReal ρβ) (fun v => Sg H v φ) 0) =ᵐ[withDensityReal ρβ]
      projMean (withDensityReal ρβ) φ := by
    have := pL_ae (μ := withDensityReal ρβ) (G := fun v => Sg H v φ) (v := 0) (hSdata 0 le_rfl).1
    rw [frozen_zero hd H hφc hφm] at this
    exact this
  set ρ : ℝ → ℝ := fun u => inner ℝ (pL (withDensityReal ρβ) (fun v => Sg H v φ) 0)
    (R (pL (withDensityReal ρβ) (fun v => Sg H v φ) u)) with hρdef
  have hcov1 : ∀ u : ℝ, 0 ≤ u →
      susceptibilityCov (periodicRiesz d s) (withDensityReal ρβ) β φ (Sg H u φ) = ρ u := by
    intro u hu
    exact susceptibilityCov_eq_inner hd s H.hs0 H.hsd hKS hρc β H.hβ R hAR φ (Sg H u φ)
      (hSdata u hu).1 _ _ hy0 (hy u hu)
  have hSm : ∀ u : ℝ, 0 ≤ u → MemSobolev ((mStar d : ℝ) + 4) (Sg H u φ) := by
    intro u hu
    obtain ⟨C1, c1, -, -, hC1⟩ := exists_frozen_hj_decay hd s (mStar d + 4) le_rfl β⁻¹ β⁻¹ c₀ Λ₀
    have H' : FrozenHyp d s (mStar d + 4 + mStar d) β⁻¹ β⁻¹ c₀ Λ₀ β V ρβ := H.mono (by omega)
    have := (hC1 β V ρβ H' φ hφc (by exact_mod_cast hφm) u hu).1
    exact_mod_cast this
  have hcov2 : ∀ u : ℝ, 0 ≤ u →
      susceptibilityCov (periodicRiesz d s) (withDensityReal ρβ) β (Sg H u φ) φ = ρ u := by
    intro u hu
    rw [← hcov1 u hu]
    exact cov_symm hd H (hSdata u hu).1 (hSm u hu) hφc hφm
  -- positivity at `u = 0`
  have hy0ne : pL (withDensityReal ρβ) (fun v => Sg H v φ) 0 ≠ 0 := by
    intro h0
    apply hnd
    refine hy0.symm.trans ?_
    rw [h0]
    exact Lp.coeFn_zero _ _ _
  have hRy0 : R (pL (withDensityReal ρβ) (fun v => Sg H v φ) 0) ≠ 0 := by
    intro h0
    apply hy0ne
    have := hAR (pL (withDensityReal ρβ) (fun v => Sg H v φ) 0)
    rw [h0, map_zero] at this
    exact this.symm
  have hρ0 : 0 < ρ 0 := by
    have h1 := hco (R (pL (withDensityReal ρβ) (fun v => Sg H v φ) 0))
    rw [hAR] at h1
    have h2 : 0 < ‖R (pL (withDensityReal ρβ) (fun v => Sg H v φ) 0)‖ * 
        ‖R (pL (withDensityReal ρβ) (fun v => Sg H v φ) 0)‖ := by
      have := norm_pos_iff.2 hRy0
      positivity
    exact lt_of_lt_of_le h2 h1
  -- decay
  obtain ⟨C, c, hC, hc, hdec⟩ := exists_frozen_l2_decay hd s β⁻¹ β⁻¹ c₀ Λ₀
  have hH5 : FrozenHyp d s (mStar d + 5) β⁻¹ β⁻¹ c₀ Λ₀ β V ρβ := H.mono (by omega)
  have hm2 : MemSobolev ((mStar d : ℝ) + 2) φ := memSobolev_mono_idx hφm (by linarith)
  have hdecφ : ∀ τ : ℝ, 0 ≤ τ → ‖pL (withDensityReal ρβ) (fun v => Sg H v φ) τ‖ ≤
      Real.sqrt Λ₀ * (C * Real.exp (-c * τ) * sobolevNorm 2 (projMean (withDensityReal ρβ) φ)) := by
    intro τ hτ
    refine (norm_pL_le H.thermal.1 hρc H.le_Lam (hSdata τ hτ).1).trans ?_
    refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
    exact hdec β V ρβ hH5 φ hφc hm2 τ hτ
  refine ⟨ρ, hρ0, ?_, fun u hu => ⟨hcov1 u hu, hcov2 u hu⟩⟩
  set A := sobolevNorm 2 (projMean (withDensityReal ρβ) φ)
  set K := ‖pL (withDensityReal ρβ) (fun v => Sg H v φ) 0‖ * (‖R‖ * (Real.sqrt Λ₀ * C * A))
  have hE : Tendsto (fun T : ℝ => Real.exp (-c * T)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg (by linarith))
  refine squeeze_zero_norm' (a := fun T : ℝ => K * Real.exp (-c * T)) ?_
    (by have := hE.const_mul K; rwa [mul_zero] at this)
  filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with T hT
  have hw : ‖R (pL (withDensityReal ρβ) (fun v => Sg H v φ) T)‖ ≤
      ‖R‖ * (Real.sqrt Λ₀ * C * A) * Real.exp (-c * T) := by
    refine (R.le_opNorm _).trans ?_
    have := hdecφ T hT
    calc ‖R‖ * ‖pL (withDensityReal ρβ) (fun v => Sg H v φ) T‖
        ≤ ‖R‖ * (Real.sqrt Λ₀ * (C * Real.exp (-c * T) * A)) :=
          mul_le_mul_of_nonneg_left this (norm_nonneg _)
      _ = _ := by ring
  calc ‖ρ T‖ ≤ ‖pL (withDensityReal ρβ) (fun v => Sg H v φ) 0‖ *
        ‖R (pL (withDensityReal ρβ) (fun v => Sg H v φ) T)‖ := norm_inner_le_norm _ _
    _ ≤ ‖pL (withDensityReal ρβ) (fun v => Sg H v φ) 0‖ *
        (‖R‖ * (Real.sqrt Λ₀ * C * A) * Real.exp (-c * T)) :=
        mul_le_mul_of_nonneg_left hw (norm_nonneg _)
    _ = K * Real.exp (-c * T) := by simp only [K]; ring

/-- A real Fourier mode is not `μ`-a.e. constant. -/
lemma q41_realMode_nd {ρβ : Torus d → ℝ} (hρ : IsProbDensity ρβ) (hpos : ∀ x, 0 < ρβ x)
    (k : NonzeroLattice d) :
    ¬ (projMean (withDensityReal ρβ) (Torus.realMode k) =ᵐ[withDensityReal ρβ] 0) := by
  intro h
  have h1 := HRS.ResponseAux.ae_vol_of_ae_dens hρ h
  set c := pair (withDensityReal ρβ) (Torus.realMode k) with hc
  have h2 : ∀ᵐ x : Torus d, Torus.realMode k x = c := by
    filter_upwards [h1] with x hx
    have hp := hpos x
    simp only [Pi.zero_apply, mul_zero] at hx
    have hx' : projMean (withDensityReal ρβ) (Torus.realMode k) x = 0 := by
      rcases mul_eq_zero.1 hx with h0 | h0
      · exact absurd h0 hp.ne'
      · exact h0
    simpa [projMean, sub_eq_zero] using hx'
  have e1 : ∫ x, Torus.realMode k x = c := by
    rw [integral_congr_ae h2]; simp
  have e2 : ∫ x, Torus.realMode k x * Torus.realMode k x = c * c := by
    rw [integral_congr_ae (h2.mono fun x hx => by rw [hx])]; simp
  have c0 : c = 0 := by rw [← e1, Torus.integral_realMode]
  have h3 := Torus.realMode_orthonormal k k
  simp only [if_true] at h3
  rw [e2, c0] at h3
  norm_num at h3

/-- Nondegenerate mixing kernel for the stationary field of the smooth positive thermal data. -/
theorem q41_kernel_data (hd : 2 ≤ d) {s β : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (hβ : 0 < β)
    (V : Torus d → ℝ) (hV : Torus.IsSmooth V) (ρβ : Torus d → ℝ)
    (hρβ : IsThermalDensity (periodicRiesz d s) V β ρβ) (hρS : Torus.IsSmooth ρβ)
    (hρpos : ∀ x, 0 < ρβ x) :
    ∃ φ : Torus d → ℝ, Torus.IsSmooth φ ∧ ∃ ρ : ℝ → ℝ, 0 < ρ 0 ∧ Tendsto ρ atTop (𝓝 0) ∧
      ∀ u : ℝ, 0 ≤ u →
        susceptibilityCov (periodicRiesz d s) (withDensityReal ρβ) β φ
          (equilibriumSemigroup (mfData d s hs0 hsd V β hβ) ρβ u φ) = ρ u ∧
        susceptibilityCov (periodicRiesz d s) (withDensityReal ρβ) β
          (equilibriumSemigroup (mfData d s hs0 hsd V β hβ) ρβ u φ) φ = ρ u := by
  obtain ⟨c₀, Λ₀, H⟩ := MFPair.frozenHyp_of_smooth s hs0 hsd β hβ V hV ρβ hρβ hρS hρpos
    (2 * mStar d + 4)
  have hd0 : 0 < d := by omega
  let k0 : NonzeroLattice d := ⟨Pi.single ⟨0, hd0⟩ 1, by
    intro h
    have := congrFun h ⟨0, hd0⟩
    simp at this⟩
  have hφS : Torus.IsSmooth (Torus.realMode k0) := HRS.FieldSingAux.isSmooth_realMode k0
  obtain ⟨ρ, h0, hdec, hker⟩ := q41_kernel_data_aux (by omega) H (Torus.continuous_realMode k0)
    (MFSemigroup.memSobolev_of_isSmooth hφS _) (q41_realMode_nd hρβ.1 hρpos k0)
  exact ⟨_, hφS, ρ, h0, hdec, hker⟩

end HRS.Q41
