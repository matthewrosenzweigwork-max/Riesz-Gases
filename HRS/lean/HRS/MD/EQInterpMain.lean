import HRS.MD.EQInterpStmt
import HRS.MD.EQInterpWass
import HRS.MD.EQInterpD2
import HRS.MD.EQInterpMom
import HRS.MD.EQInterpArith

/-!
# EQ-INTERP packet: assembly of `equilibrium_paths_interpolation` (TeX L4134-4163)

`eq_interp_assembly_proof`: the interpolation clause of Theorem 2.9 from the direct clause at the weaker index `m₁`
(`equilibrium_paths_direct`), the stationary strong moment (`eq_strong_moment`), the lift of the Gaussian field along `E_m ↪ E_{m₁}`
(`eq_gauss_lift`) and the existence of flows (`eq_flow_exists`; only for the edge case `T = 0`).

Route: the windows of `ζ_N` and of `Z` at index `m₁` are the images under `epath : 𝒳_{m,T} ↪ 𝒳_{m₁,T}` of those at index `m`
(`windowZeta_embed_ae`, `windowPath_embed_ae`).  `W_2`: `wass_interp` (almost optimal coupling at `m₁`, pulled back along the
measurable embedding, Hölder in probability against the `𝒳_{q,T}` second moments of `eq_strong_moment`).  `d₂`: `d2_interp`
(frequency cut-off `P_R`, `C_b²` composition estimate) and `d2_optimize` (the choice `R = ε^{-1/(2m₁-m-q)}`).
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS

namespace MD

namespace EQInterp

open HRS.LZ HRS.Uniform HRS.Main

theorem deltaN_pos' {d : ℕ} {s : ℝ} (hs0 : 0 ≤ s) {N : ℕ} (hN : 1 ≤ N) : 0 < deltaN d s N := by
  have h := HRS.MD.EQ29.one_le_mul_deltaN' (d := d) hs0 hN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  by_contra hcon
  push Not at hcon
  nlinarith

theorem eq_interp_assembly_proof {d : ℕ} (hd : 2 ≤ d)
    (hdirect : type_of% (@HRS.Main.equilibrium_paths_direct d))
    (hstrong : StrongMomentStmt d) (hlift : GaussLiftStmt d) (hflow : FlowExistsStmt d) :
    type_of% (@HRS.Main.equilibrium_paths_interpolation d) := by
  intro hd' s hs0 hsd V hV βm βp hβm hββ m hm q m₁ hq hqm hmm₁ hm₁ T hT
  have hd2 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hmq : (0 : ℝ) < m - q := by linarith
  have hm₁q : (0 : ℝ) < m₁ - q := by linarith
  set α : ℝ := (m - q) / (m₁ - q) with hα
  have hα0 : 0 < α := div_pos hmq hm₁q
  have hα1 : α < 1 := by rw [hα, div_lt_one hm₁q]; linarith
  have hαeq : α * (m₁ - q) = m - q := by rw [hα]; field_simp
  have hmmle : m ≤ m₁ := hmm₁.le
  have hm2 : (d : ℝ) < 2 * m := by linarith
  obtain ⟨C₁, hC₁, hdir⟩ := hdirect hd hs0 hsd V hV βm βp hβm hββ m₁ hm₁ T hT
  obtain ⟨Cs, hCs, hmom⟩ := hstrong hd hs0 hsd V hV βm βp hβm hββ m q hq hqm T hT
  set γ : ℝ := (m - q) / (2 * m₁ - m - q) with hγ
  have hD : 0 < 2 * m₁ - m - q := by linarith
  have hγ0 : 0 < γ := div_pos hmq hD
  set KW : ℝ := (4 * Cs) ^ ((1 - α) / 2) * (2 * C₁) ^ α with hKW
  set KD : ℝ := (2 * (1 + Cs) + 1) * C₁ ^ γ with hKD
  have hKW0 : 0 < KW := by positivity
  have hKD0 : 0 < KD := by positivity
  refine ⟨max KW KD, lt_max_of_lt_left hKW0, ?_⟩
  intro β hβ ρβ hρ u hu N hN Ω _ P _ X₀ W X hX Ω' _ P' _ Z hZ
  have hβ0 : 0 < β := hβm.trans_le hβ.1
  have hZ₁ := hlift hd hs0 hsd V hβ0 ρβ m m₁ (by linarith) hmmle P' Z hZ
  obtain ⟨hD_smooth, hD_W⟩ := hdir β hβ ρβ hρ u hu N hN P X₀ W X hX P'
    (fun t ω => NegSobolev.embed m₁ (Z t ω)) hZ₁
  obtain ⟨hmomF, hmomG⟩ := hmom β hβ ρβ hρ
  -- the `𝒳_{q,T}` second moments of the two windows
  have hμ : ∫⁻ w, qSq q w ∂(law P (Main.windowZeta m T u P X)) ≤ ENNReal.ofReal Cs := by
    rcases hT.eq_or_lt with h0 | hpos
    · subst h0
      exact flow_moment_zero hd hs0 hsd V hV hβ0 hN hu P hX hm2 Cs
        (fun Ω' _ P' _ X₀' W' X' hX' => hmomF 0 le_rfl N hN P' X₀' W' X' hX')
        (hflow hd hs0 hsd V hV hβ0 hN (0 + 0) (by norm_num))
    · exact flow_moment_pos hd hs0 hsd V hV hβ0 hN hu hpos P hX hm2 Cs
        (hmomF u hu N hN P X₀ W X hX)
  have hν : ∫⁻ w, qSq q w ∂(law P' (Main.windowPath m T 0 Z)) ≤ ENNReal.ofReal Cs :=
    gauss_moment hd hs0 hsd V hβ0 ρβ hT P' Z hZ Cs (hmomG P' Z hZ)
  -- the windows at index `m₁` are the images of those at index `m`
  have hAEF := windowZeta_aemeasurable hd hs0 hsd V hV hβ0 hN hu hT P hX hm2
  have hAEG := (EQGaussWindow.eqgw_fidi hd hs0 hsd V hβ0 ρβ m T P' Z hZ 0 le_rfl).1
  have hem : Measurable (epath hmmle T : PathSpace d m T → PathSpace d m₁ T) :=
    (epath hmmle T).continuous.measurable
  have hlawF : law P (Main.windowZeta m₁ T u P X) =
      (law P (Main.windowZeta m T u P X)).map (epath hmmle T) := by
    exact (Measure.map_congr (windowZeta_embed_ae hd hs0 hsd V hV hβ0 hN hu hT P hX hm2 hmmle)).trans
      (AEMeasurable.map_map_of_aemeasurable hem.aemeasurable hAEF).symm
  have hlawG : law P' (Main.windowPath m₁ T 0 (fun t ω => NegSobolev.embed m₁ (Z t ω))) =
      (law P' (Main.windowPath m T 0 Z)).map (epath hmmle T) := by
    exact (Measure.map_congr (windowPath_embed_ae hs0 hsd hβ0 V ρβ hmmle T P' Z hZ.cont)).trans
      (AEMeasurable.map_map_of_aemeasurable hem.aemeasurable hAEG).symm
  haveI hμP : IsProbabilityMeasure (law P (Main.windowZeta m T u P X)) :=
    (Measure.isProbabilityMeasure_map_iff hAEF).2 inferInstance
  haveI hνP : IsProbabilityMeasure (law P' (Main.windowPath m T 0 Z)) :=
    (Measure.isProbabilityMeasure_map_iff hAEG).2 inferInstance
  rw [hlawF, hlawG] at hD_smooth hD_W
  have hδ : 0 < deltaN d s N := deltaN_pos' hs0 (by omega)
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  set x : ℝ := (N : ℝ) ^ (-(1 : ℝ) / 4) + Real.sqrt (deltaN d s N) with hx
  have hx0 : 0 < x :=
    add_pos_of_pos_of_nonneg (Real.rpow_pos_of_pos hN0 _) (Real.sqrt_nonneg _)
  constructor
  · -- `W_2`
    have hW1 : wassersteinE 2 ((law P (Main.windowZeta m T u P X)).map (epath hmmle T))
        ((law P' (Main.windowPath m T 0 Z)).map (epath hmmle T)) < ENNReal.ofReal (2 * C₁ * x) := by
      refine lt_of_le_of_lt hD_W ?_
      exact (ENNReal.ofReal_lt_ofReal_iff (by positivity)).2 (by nlinarith [mul_pos hC₁ hx0])
    have hW := wass_interp hmmle hT hα0 hα1 hαeq _ _ (ENNReal.ofReal Cs) hμ hν _ hW1
    rw [wass_const hCs hC₁ hα0 hα1 hx0] at hW
    refine hW.trans (ENNReal.ofReal_le_ofReal ?_)
    have : KW * x ^ α ≤ max KW KD * x ^ α :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hx0.le _)
    rw [hKW] at this
    exact this
  · -- `d₂`
    set ε₀ : ℝ := C₁ * Real.sqrt (deltaN d s N) with hε₀
    have hε0 : 0 < ε₀ := mul_pos hC₁ (Real.sqrt_pos.2 hδ)
    have hS := d2_optimize (S := smoothDist 2 (law P (Main.windowZeta m T u P X))
        (law P' (Main.windowPath m T 0 Z))) (ε := ε₀) (A := Cs) hqm hmm₁ hCs.le hε0
      (fun R hR => d2_interp hmmle hT hqm.le hR hCs.le _ _ hμ hν hD_smooth)
      (smoothDist_le_two _ _)
    refine hS.trans ?_
    have e1 : ε₀ ^ γ = C₁ ^ γ * deltaN d s N ^ ((m - q) / (2 * (2 * m₁ - m - q))) := by
      rw [hε₀, Real.mul_rpow hC₁.le (Real.sqrt_nonneg _), Real.sqrt_eq_rpow, ← Real.rpow_mul hδ.le]
      congr 2
      rw [hγ]; field_simp
    rw [e1]
    have hpow : 0 ≤ deltaN d s N ^ ((m - q) / (2 * (2 * m₁ - m - q))) := Real.rpow_nonneg hδ.le _
    calc (2 * (1 + Cs) + 1) * (C₁ ^ γ * deltaN d s N ^ ((m - q) / (2 * (2 * m₁ - m - q))))
        = KD * deltaN d s N ^ ((m - q) / (2 * (2 * m₁ - m - q))) := by rw [hKD]; ring
      _ ≤ max KW KD * deltaN d s N ^ ((m - q) / (2 * (2 * m₁ - m - q))) :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) hpow

end EQInterp

end MD

end HRS
