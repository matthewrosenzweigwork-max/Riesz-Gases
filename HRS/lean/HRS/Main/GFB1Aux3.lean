import HRS.Main.GFSpec3
import HRS.Uniform.Q54cAux36
import HRS.Uniform.Q54cAux56
import HRS.Uniform.Q14Aux2

/-!
# Packet GFB1, part 3: relocated proofs of `gf_bures2_le_traceNorm` and `gf_detCovDensity`

Statements copied verbatim from `HRS/Main/GFSpec3.lean` (not edited).  Each proof is `<name>_proof`, tied to
its spec by an `example` (`type_of%`).  Helpers carry the prefix `gfb1_`.

* `gf_bures2_le_traceNorm`: with the square roots `R = √C`, `S = √D` and a Hilbert basis `e`, the Bures
  cost `bures2 C D` is at most `Tr C + Tr D - 2∑⟨R e_j, S e_j⟩ = ∑‖(R-S)e_j‖²`, which is at most
  `‖C-D‖₁` by Powers–Størmer (`HRS.powers_stormer`).
* `gf_detCovDensity`: the density `σ ↦ covForm γ q ρ_N^σ` (zero off `[0,T]`) is a deterministic covariance
  density by `Q54c.isDetCovDensity_covDens`; its hypotheses come from the mean-field solution and regularity.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.GF

open HRS.Uniform

variable {d : ℕ}

theorem gf_bures2_le_traceNorm_proof {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
    (C D : H →L[ℝ] H →L[ℝ] ℝ) (hC : IsTraceClassCov C) (hD : IsTraceClassCov D) :
    bures2 C D ≤ traceNormForm (C - D) := by
  classical
  obtain ⟨ι, -, e, -⟩ := HilbertCLTAux.exists_hilbertBasis_type (H := H)
  set R := Uniform.formSqrt C with hRdef
  set Sq := Uniform.formSqrt D with hSdef
  have hR : IsSqrtOfForm R C := Uniform.RelCov.formSqrt_spec hC
  have hS : IsSqrtOfForm Sq D := Uniform.RelCov.formSqrt_spec hD
  have hRs := Uniform.RelCov.summable_sqrt_diag e hR hC
  have hSs := Uniform.RelCov.summable_sqrt_diag e hS hD
  obtain ⟨tC, hCt, -⟩ := hC.hasSum_basis e
  obtain ⟨tD, hDt, -⟩ := hD.hasSum_basis e
  have hnC : traceNormForm C = tC :=
    le_antisymm ((traceNormForm_le_basis_trace hC e).trans hCt.tsum_eq.le)
      (hCt.tsum_eq ▸ hC.tsum_basis_le e)
  have hnD : traceNormForm D = tD :=
    le_antisymm ((traceNormForm_le_basis_trace hD e).trans hDt.tsum_eq.le)
      (hDt.tsum_eq ▸ hD.tsum_basis_le e)
  -- the Bures bound in terms of the cross term (`q14_bures2_le` with the square roots)
  have hbures := HRS.Uniform.Q14.q14_bures2_le e hC hD R Sq hR.sq hS.sq
  -- summability of the cross term
  have hsumI : Summable (fun j => inner ℝ (R (e j)) (Sq (e j))) := by
    refine Summable.of_norm_bounded ((hRs.add hSs).mul_left (1 / 2)) fun j => ?_
    have h1 := abs_real_inner_le_norm (R (e j)) (Sq (e j))
    have h2 : ‖R (e j)‖ * ‖Sq (e j)‖ ≤ (‖R (e j)‖ ^ 2 + ‖Sq (e j)‖ ^ 2) / 2 := by
      nlinarith [sq_nonneg (‖R (e j)‖ - ‖Sq (e j)‖)]
    rw [Real.norm_eq_abs]
    linarith
  -- the Powers–Størmer bound for the difference of the square roots
  obtain ⟨hPs, hPle⟩ := HRS.powers_stormer e hR hS hC hD hCt.summable hDt.summable
  -- expansion of the squared difference
  have hR2 : ∀ j, ‖R (e j)‖ ^ 2 = C (e j) (e j) := fun j => by
    rw [← real_inner_self_eq_norm_sq, hR.sq]
  have hS2 : ∀ j, ‖Sq (e j)‖ ^ 2 = D (e j) (e j) := fun j => by
    rw [← real_inner_self_eq_norm_sq, hS.sq]
  have hterm : ∀ j, ‖(R - Sq) (e j)‖ ^ 2 =
      ‖R (e j)‖ ^ 2 + ‖Sq (e j)‖ ^ 2 - 2 * inner ℝ (R (e j)) (Sq (e j)) := fun j => by
    rw [ContinuousLinearMap.sub_apply, norm_sub_sq_real]
    ring
  have hP : ∑' j, ‖(R - Sq) (e j)‖ ^ 2 = tC + tD - 2 * ∑' j, inner ℝ (R (e j)) (Sq (e j)) := by
    rw [tsum_congr hterm, Summable.tsum_sub (hRs.add hSs) (hsumI.mul_left 2),
      Summable.tsum_add hRs hSs, tsum_mul_left, tsum_congr hR2, tsum_congr hS2,
      hCt.tsum_eq, hDt.tsum_eq]
  have hb := hbures
  rw [hnC, hnD] at hb
  linarith [hPle, hP, hb]

example := (@gf_bures2_le_traceNorm_proof : type_of% @HRS.GF.gf_bures2_le_traceNorm)

theorem gf_detCovDensity_proof (S : GeneralSetup d) (M : Matrix (Fin d) (Fin d) ℝ) (hMF : S.MFHypM M)
    (N : ℕ) (q : ℝ) (hq : 0 ≤ q) :
    IsDetCovDensity S.T (covDensT (S.γ : ℝ) q S.T (S.ρ N)) := by
  have hn : (d : ℝ) / 2 + 2 < (S.γ : ℝ) := by
    have h' : ((2 * d + 10 : ℕ) : ℝ) < (S.γ : ℝ) := by exact_mod_cast S.hγ
    push_cast at h'
    have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  obtain ⟨hMFN, hReg⟩ := hMF N
  have hK : d + 1 ≤ S.γ + 2 * d + 12 := by omega
  have hprob : ∀ σ ∈ Set.Icc (0 : ℝ) S.T, IsProbDensity (S.ρ N σ) := fun σ hσ => hMFN.density σ hσ
  have hV : Torus.IsCk 1 (S.dynM M N).V := by
    have h1 : (1 : WithTop ℕ∞) ≤ ((S.γ + 2 * d + 12 : ℕ) : WithTop ℕ∞) := by
      exact_mod_cast (show 1 ≤ S.γ + 2 * d + 12 by omega)
    exact ContDiff.of_le S.V_reg h1
  have hd1 : 1 ≤ d := by have := S.hd; omega
  have hweak := Q54c.weak_continuity (S.dynM M N) hd1 S.T S.Λ S.hT.le
    (S.γ + 2 * d + 12) hK (S.ρ N) hMFN hReg hV
  have hcts : ∀ σ ∈ Set.Icc (0 : ℝ) S.T, Continuous (S.ρ N σ) := by
    intro σ hσ
    have h1 : (1 : WithTop ℕ∞) ≤ ((S.γ + 2 * d + 12 : ℕ) : WithTop ℕ∞) := by
      exact_mod_cast (show 1 ≤ S.γ + 2 * d + 12 by omega)
    have hC1 : ContDiff ℝ 1 (Torus.lift (S.ρ N σ)) := ContDiff.of_le (hReg σ hσ).1 h1
    exact Torus.continuous_of_continuous_lift hC1.continuous
  exact Q54c.isDetCovDensity_covDens hn hq hprob hweak hcts

example := (@gf_detCovDensity_proof : type_of% @HRS.GF.gf_detCovDensity)

end HRS.GF
