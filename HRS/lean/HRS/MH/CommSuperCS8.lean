import HRS.MH.CommSuperDefs
import HRS.Commutator.Whole.ApproxAux
import HRS.Commutator.Whole.Bridge

/-!
# CS8: integrability for bounded densities (packet `bdd_integrable` of `CommSuperSpec.lean`)

Reuses `HRS.Commutator.Whole.cmxSA_core_m`, `cmxSA_conv_bound`, `cmxSA_kern_bound`, `cmxSA_comm_bound`
(`HRS/Commutator/Whole/ApproxAux.lean`) with `p = ⊤`, `qr = 1`, `σ = (s+d)/2`, and the transfer
`commIntegrableW_iff` (`HRS/Commutator/Whole/Bridge.lean`).
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace HRS.MH.CommSuper

variable {d N : ℕ} {s : ℝ}

/-- A probability density is integrable (its integral is `1 ≠ 0`). -/
theorem cs8_integrable {ρ : Euc d → ℝ} (hρ : Whole.IsProbDensity ρ) : Integrable ρ := by
  by_contra h
  have h1 := hρ.integral_one
  rw [integral_undef h] at h1
  norm_num at h1

/-- A bounded measurable function is in `L^∞`. -/
theorem cs8_memLp_top {ρ : Euc d → ℝ} (hρ : Whole.IsProbDensity ρ) {Λ : ℝ}
    (hρΛ : ∀ x, ρ x ≤ Λ) : MemLp ρ ⊤ volume := by
  refine memLp_top_of_bound hρ.measurable.aestronglyMeasurable |Λ|
    (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_of_nonneg (hρ.nonneg x)]
  exact (hρΛ x).trans (le_abs_self Λ)

/-- **CS8** (size S).  For a bounded probability density (and, if `s = 0`, a log moment) all integrals
defining `𝖥_N` and `Comm_N` converge absolutely, so none of the Bochner integrals is junk, and
`CommIntegrableW` holds (no log moment is needed for the commutator kernel: `|h_v| ≤ Lip·(|z|^{-s}...)`).
Reuses `cmxSA_core_m` (`ApproxAux.lean:365`) with `p = ⊤`, `qr = 1`, `σ = (s+d)/2`
(`cmxSA_conv_bound`, `:193`), `cmxSA_kern_bound` (`:295`), `cmxSA_comm_bound` (`:324`), `cmxSA_W`
(`:237`), the log term from `HasLogMoment` via `integrable_withDensity_iff`, and
`Bridge.commIntegrableW_iff` (`Bridge.lean:82`). -/
theorem bdd_integrable_proof (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {Λ : ℝ} {ρ : Euc d → ℝ}
    (hρ : Whole.IsProbDensity ρ) (hρΛ : ∀ x, ρ x ≤ Λ) {L : ℝ}
    (hlog : s = 0 → Whole.HasLogMoment (Whole.withDensityReal ρ) L)
    {N : ℕ} (X : Whole.EucConfig d N) (hX : Function.Injective X)
    (v : Euc d → Euc d) (K : ℝ) (hv : Whole.HasLipBoundW v K) :
    HRS.Commutator.Whole.EnergyIntegrable s X ρ ∧ HRS.Commutator.Whole.CommIntegrable s X ρ v ∧
      Whole.CommIntegrableW d s v X (Whole.withDensityReal ρ) := by
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hρ1 : Integrable ρ := cs8_integrable hρ
  obtain ⟨σ, hσdef⟩ : ∃ σ : ℝ, σ = (s + d) / 2 := ⟨_, rfl⟩
  have hσ0 : 0 < σ := by linarith
  have hsσ : s ≤ σ := by linarith
  have hσd : σ * 1 < d := by linarith
  obtain ⟨B, hB, hconv⟩ := HRS.Commutator.Whole.cmxSA_conv_bound hd hσ0.le le_rfl hσd ⊤
    (by simp) ρ (cs8_memLp_top hρ hρΛ)
  have hW : Integrable (fun x => HRS.Commutator.Whole.cmxSA_W s x * ρ x) := by
    by_cases h0 : s = 0
    · obtain ⟨hI, -⟩ := hlog h0
      have hI' := (HRS.Commutator.Whole.cmxFB_integrable_wd hρ _).1 hI
      refine hI'.congr (Filter.Eventually.of_forall fun x => ?_)
      simp [HRS.Commutator.Whole.cmxSA_W, h0, mul_comm]
    · refine (integrable_zero _ _ _).congr (Filter.Eventually.of_forall fun x => ?_)
      simp [HRS.Commutator.Whole.cmxSA_W, h0]
  have hE : HRS.Commutator.Whole.EnergyIntegrable s X ρ := by
    have key := HRS.Commutator.Whole.cmxSA_core_m
      (k := fun x y => HRS.Commutator.Whole.kern s (x - y))
      ((HRS.Commutator.Whole.cmxSA_kern_measurable s).comp (measurable_fst.sub measurable_snd)) ρ
      hρ.measurable hρ1 (HRS.Commutator.Whole.cmxSA_W s) (HRS.Commutator.Whole.cmxSA_W_measurable s)
      (HRS.Commutator.Whole.cmxSA_W_nonneg s) hW (s⁻¹) (s⁻¹ + σ⁻¹) σ (inv_nonneg.2 hs0)
      (add_nonneg (inv_nonneg.2 hs0) (inv_nonneg.2 hσ0.le)) B hB hconv
      (fun x y => HRS.Commutator.Whole.cmxSA_kern_bound hs0 hσ0 hsσ x y)
    exact ⟨fun i => key.1 (X i), key.2⟩
  obtain ⟨L', hLv, -⟩ := hv
  have hC : HRS.Commutator.Whole.CommIntegrable s X ρ v := by
    have key := HRS.Commutator.Whole.cmxSA_core_m
      (k := HRS.Commutator.Whole.commKer (HRS.Commutator.Whole.kernGrad s) v)
      (HRS.Commutator.Whole.cmxSA_commKer_measurable s hLv.continuous.measurable) ρ hρ.measurable hρ1
      (fun _ => 0) measurable_const (fun _ => le_rfl) (by simpa using integrable_zero _ _ _)
      L' L' σ L'.coe_nonneg L'.coe_nonneg B hB hconv
      (fun x y => by simpa using HRS.Commutator.Whole.cmxSA_comm_bound hs0 hσ0 hsσ hLv x y)
    exact ⟨fun i => key.1 (X i), key.2⟩
  exact ⟨hE, hC, (HRS.Commutator.Whole.commIntegrableW_iff hs0 ρ hρ X hX v).2 hC⟩

end HRS.MH.CommSuper
