import HRS.ME.UIPath

/-!
# Packet Q4 of `HRS.ui_path_shifted`: the limit-side finite-dimensional vector of `windowPath`

Statement copied verbatim from `HRS/ME/UIPathShiftedSpec.lean` (sorried there, independently reviewed).
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal

noncomputable section

namespace HRS.ME.UIPathShifted

open HRS HRS.Main

variable {d : ℕ}

/-- Evaluation of the window `windowPath m T 0 Z` at `t ∈ [0,T]`, on an `ω` where `Z(·,ω)` is continuous on
`[0,∞)`: it is the value `Z (0 + t) ω`. -/
theorem p_sq4_windowPath_at {m T : ℝ} {Ω' : Type} (Z : ℝ → Ω' → NegSobolev d m) (ω : Ω')
    (hω : ContinuousOn (fun t => Z t ω) (Set.Ici 0)) (t : Set.Icc (0 : ℝ) T) :
    (windowPath m T 0 Z ω).at' t = Z (0 + (t : ℝ)) ω := by
  have hc : ContinuousOn (fun t : ℝ => Z (0 + t) ω) (Set.Icc 0 T) := by
    have h1 : ContinuousOn (fun t : ℝ => 0 + t) (Set.Icc 0 T) := by fun_prop
    exact hω.comp h1 (fun t ht => by simp only [Set.mem_Ici, zero_add]; exact ht.1)
  have h : Continuous fun t : Set.Icc (0 : ℝ) T => Z (0 + (t : ℝ)) ω := hc.restrict
  have e : windowPath m T 0 Z ω =
      (⟨fun t : Set.Icc (0 : ℝ) T => Z (0 + (t : ℝ)) ω, h⟩ : C(Set.Icc (0 : ℝ) T, NegSobolev d m)) := by
    unfold windowPath toPath
    exact dif_pos h
  rw [e]
  rfl

/-- **Q4** (limit side: the finite-dimensional vector of the window of `Z_β`; scope note Q4).  For a stationary
Gaussian field `Z` (`IsStationaryGaussianField`, a.s. continuous on `[0,∞)`) the test vector of the window
`windowPath m T 0 Z` at times `ts a ∈ [0,T]` agrees `P'`-a.e. with `(⟨Z^{ts a}, φ_a⟩)_a`, and its law is the
centred Gaussian `multivariateGaussian 0 (PDE.stationaryLagCov …)`.  Route: a.s. continuity on `[0,T] ⊂ [0,∞)`
unfolds `windowPath`/`toPath`; `IsStationaryGaussianField.gaussian` at `τ = ts` (`0 ≤ ts a`);
`Measure.map_congr`. -/
theorem windowPath_fidi_law {s β : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (hβ : 0 < β)
    (V ρβ : Torus d → ℝ) {m : ℝ} (T : ℝ)
    {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (Z : ℝ → Ω' → NegSobolev d m) (hZ : IsStationaryGaussianField P' s β hs0 hsd hβ V ρβ m Z)
    (p : ℕ) (ts : Fin p → ℝ) (hts : ∀ a, ts a ∈ Set.Icc (0 : ℝ) T)
    (φ : Fin p → Torus d → ℝ) (hφ : ∀ a, Torus.IsSmooth (φ a)) :
    ((fun ω => (WithLp.toLp 2 fun a =>
        NegSobolev.eval ((windowPath m T 0 Z ω).at' ⟨ts a, hts a⟩) (φ a) :
        EuclideanSpace ℝ (Fin p))) =ᵐ[P']
      (fun ω => (WithLp.toLp 2 fun a => NegSobolev.eval (Z (ts a) ω) (φ a) :
        EuclideanSpace ℝ (Fin p)))) ∧
    law P' (fun ω => (WithLp.toLp 2 fun a =>
        NegSobolev.eval ((windowPath m T 0 Z ω).at' ⟨ts a, hts a⟩) (φ a) :
        EuclideanSpace ℝ (Fin p))) =
      ProbabilityTheory.multivariateGaussian 0
        (PDE.stationaryLagCov d s β (PDE.mfData d s hs0 hsd V β hβ) ρβ ts φ) := by
  have hae : (fun ω => (WithLp.toLp 2 fun a =>
        NegSobolev.eval ((windowPath m T 0 Z ω).at' ⟨ts a, hts a⟩) (φ a) :
        EuclideanSpace ℝ (Fin p))) =ᵐ[P']
      (fun ω => (WithLp.toLp 2 fun a => NegSobolev.eval (Z (ts a) ω) (φ a) :
        EuclideanSpace ℝ (Fin p))) := by
    filter_upwards [hZ.cont] with ω hω
    congr 1
    funext a
    rw [p_sq4_windowPath_at Z ω hω ⟨ts a, hts a⟩]
    simp only [zero_add]
  refine ⟨hae, ?_⟩
  have hlaw := hZ.gaussian p ts φ (fun a => (hts a).1) hφ
  rw [← hlaw]
  exact Measure.map_congr hae

end HRS.ME.UIPathShifted
