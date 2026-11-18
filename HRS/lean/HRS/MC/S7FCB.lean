import HRS.MC.S7FCBBnd2
import HRS.MC.Sec7Vocab

/-!
# FC-B: smooth finite-rank approximation of an enveloped pair kernel (relocated proof)

`s7_FC_B_tail_kernels_proof` has the statement of `HRS.MC.Sec7.s7_FC_B_tail_kernels` verbatim.  Route: the Landau
kernel averaging `fcbT n h = ∫ K_n(x - q₁) K_n(y - q₂) h(q) dq` is smooth finite rank and symmetric
(`fcbT_finite_rank`), keeps the envelope up to a constant (`fcb_envelope`, `fcbT_pointwise_bound`), and converges
to `h` in `L^{2+ε}` for Lebesgue measure (`fcb_Lp_conv`), hence for the bounded-density product measure.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.FCB

open HRS HRS.Sec7 HRS.MC.SEdge

variable {d : ℕ}

local instance fcb_borel_prod2m : BorelSpace (Torus d × Torus d) := Prod.borelSpace
local instance fcb_open_prod4m : OpensMeasurableSpace ((Torus d × Torus d) × Torus d × Torus d) :=
  Prod.opensMeasurableSpace

theorem s7_FC_B_tail_kernels_proof (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) (ρ : Torus d → ℝ)
    (hρ : SmoothPosDensity ρ) (c : ℝ) (hc : EnvelopeConst (d := d) s c) :
    ∃ C : ℝ, ∀ (B : ℝ), 0 ≤ B → ∀ (h : Torus d → Torus d → ℝ), Measurable (Function.uncurry h) →
      (∀ x y, h x y = h y x) → (∀ x y, x ≠ y → |h x y| ≤ B * (periodicRiesz d s (x - y) + c)) →
      ∀ ε : ℝ, 0 < ε → (2 + ε) * s < d →
      ∃ hL : ℕ → Torus d → Torus d → ℝ, (∀ L, s7_IsFiniteRankSmooth (hL L)) ∧
        (∀ L x y, x ≠ y → |hL L x y| ≤ C * B * (periodicRiesz d s (x - y) + c)) ∧
        Tendsto (fun L => eLpNorm (fun p : Torus d × Torus d => hL L p.1 p.2 - h p.1 p.2)
          (ENNReal.ofReal (2 + ε)) ((withDensityReal ρ).prod (withDensityReal ρ))) atTop (𝓝 0) := by
  have hd0 : 0 < d := by omega
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd0
  have hsd : s < (d : ℝ) := by linarith
  obtain ⟨c1, c2, hc1, hc2, hw⟩ := fcb_w_comp_sup hd hs0 hsd hc
  obtain ⟨Cenv, hCenv, hT⟩ := fcbT_pointwise_bound hd0 hs0 hsd
  obtain ⟨K, hK, hKle⟩ := fcb_withDensity_prod_le (fcb_smooth_continuous hρ.smooth)
  refine ⟨c2 * Cenv / c1, fun B hB h hmeas hsym hbd ε hε hεs => ?_⟩
  have hp1 : (1 : ℝ) < 2 + ε := by linarith
  have hp0 : (0 : ℝ) < 2 + ε := by linarith
  have hae : ∀ᵐ q ∂(volume.prod volume : Measure (Torus d × Torus d)),
      |Function.uncurry h q| ≤ (B * c2) * fcbPhi s ‖q.1 - q.2‖ := by
    filter_upwards [fcb_ae_ne hd0] with q hq
    have hz : q.1 - q.2 ≠ 0 := sub_ne_zero.2 hq
    calc |Function.uncurry h q| ≤ B * (periodicRiesz d s (q.1 - q.2) + c) := hbd q.1 q.2 hq
      _ ≤ B * (c2 * fcbPhi s ‖q.1 - q.2‖) := mul_le_mul_of_nonneg_left (hw _ hz).2 hB
      _ = _ := by ring
  have hmem : MemLp (Function.uncurry h) (ENNReal.ofReal (2 + ε)) (volume.prod volume) := by
    have hΦ := (fcb_memLp_Phi hd0 hs0 hp0 hεs).const_mul (B * c2)
    refine hΦ.mono' hmeas.aestronglyMeasurable ?_
    filter_upwards [hae] with q hq
    rw [Real.norm_eq_abs]; exact hq
  have hint : Integrable (Function.uncurry h) (volume.prod volume) :=
    hmem.integrable (by rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hp1.le)
  have hsym' : ∀ q : Torus d × Torus d, Function.uncurry h q.swap = Function.uncurry h q :=
    fun q => hsym q.2 q.1
  have hfr : ∀ L : ℕ, ∃ (m : ℕ) (p : Fin m → Torus d → ℝ) (cc : Fin m → Fin m → ℝ),
      (∀ i, Torus.IsSmooth (p i)) ∧ (∀ i j, cc i j = cc j i) ∧
      ∀ x y, fcbT d (L + 1) (Function.uncurry h) (x, y) = ∑ i, ∑ j, cc i j * p i x * p j y :=
    fun L => fcbT_finite_rank hd0 (Nat.le_add_left 1 L) hint hsym'
  choose m pp cc hpp hcc hTe using hfr
  refine ⟨fun L x y => fcbT d (L + 1) (Function.uncurry h) (x, y),
    fun L => ⟨m L, pp L, cc L, hpp L, hcc L, hTe L⟩, ?_, ?_⟩
  · intro L x y hxy
    have h1 := hT (L + 1) (Nat.le_add_left 1 L) (B * c2) (mul_nonneg hB hc2.le) (Function.uncurry h) hae x y hxy
    have hz : x - y ≠ 0 := sub_ne_zero.2 hxy
    have hlow := (hw (x - y) hz).1
    have hΦ0 : 0 ≤ fcbPhi s ‖x - y‖ := fcb_Phi_nonneg hs0 (norm_nonneg _)
    have hq : 0 ≤ c2 * Cenv / c1 := by positivity
    calc |fcbT d (L + 1) (Function.uncurry h) (x, y)| ≤ (B * c2) * (Cenv * fcbPhi s ‖x - y‖) := h1
      _ = (c2 * Cenv / c1) * B * (c1 * fcbPhi s ‖x - y‖) := by field_simp
      _ ≤ (c2 * Cenv / c1) * B * (periodicRiesz d s (x - y) + c) := by gcongr
  · have h1 := fcb_Lp_conv hd0 hp1 hmeas hmem
    have hum : ∀ L : ℕ, AEStronglyMeasurable
        (fun p : Torus d × Torus d => fcbT d (L + 1) (Function.uncurry h) p - Function.uncurry h p)
        (volume.prod volume) := fun L =>
      ((fcbT_stronglyMeasurable (L + 1) hmeas).sub hmeas.stronglyMeasurable).aestronglyMeasurable
    exact fcb_tendsto_transfer hK hKle ENNReal.ofReal_ne_top
      (fun L p => fcbT d (L + 1) (Function.uncurry h) p - Function.uncurry h p) hum h1

end HRS.MC.Sec7.FCB
