import HRS.MS.R26T8AP11b3
import HRS.MS.R26T8APot2

/-!
# S8.2 nonlocal layer: measurability in `v` of the `p`-jets of the truncated integrand (P11e, part 3b, piece B4a)
`v ↦ D^i (G v) p` is a pointwise limit of continuous functions: `G v` agrees, for `|v| >= 2/(m+1)`, with the parameter-smooth
`Gm m` (the extra factor `1 - chi((m+1) v)` kills the singularity at `v = 0`), and `r26t8a_partialY_continuous` gives joint continuity.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Metric
open scoped ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82

/-- The regularised integrand, jointly in `(q, w)` with `v = w.1`. -/
def r26t8a_Gm {d : ℕ} (alpha : ℝ) (chi : Euc d → ℝ) (δ : ℝ) (F : Euc d → Euc d → ℝ) (m : ℕ)
    (q w : Euc d × Euc d) : ℝ :=
  r26t8a_Kc alpha chi δ (q.1 - q.2 - w.1) *
    (chi w.1 * chi (δ⁻¹ • w.1) * (1 - chi (((m : ℝ) + 1) • w.1)) * F (q.2 + w.1) q.2)

theorem r26t8a_Gm_contDiff (d : ℕ) (alpha : ℝ) (halpha : 0 < alpha) (had : alpha < d) (hd : 2 ≤ d)
    (chi : Euc d → ℝ) (hchi : NewtonCutoff chi) (F : Euc d → Euc d → ℝ) {k : ℕ}
    (hF : ContDiffOn ℝ k (Function.uncurry F) {p | p.1 ≠ p.2}) {δ : ℝ} (hδ : 0 < δ) (m : ℕ) :
    ContDiff ℝ (k : WithTop ℕ∞) (fun x : (Euc d × Euc d) × (Euc d × Euc d) => r26t8a_Gm alpha chi δ F m x.1 x.2) := by
  have hchic : ContDiff ℝ (k : WithTop ℕ∞) chi := hchi.1.of_le (by exact_mod_cast le_top)
  have hK : ContDiff ℝ (k : WithTop ℕ∞) (r26t8a_Kc alpha chi δ) :=
    (r26t8a_Kc_contDiff d hd alpha halpha had chi hchi hδ).of_le (by exact_mod_cast le_top)
  have h1 : ContDiff ℝ (k : WithTop ℕ∞)
      (fun x : (Euc d × Euc d) × (Euc d × Euc d) => r26t8a_Kc alpha chi δ (x.1.1 - x.1.2 - x.2.1)) :=
    hK.comp (((contDiff_fst.comp contDiff_fst).sub (contDiff_snd.comp contDiff_fst)).sub
      (contDiff_fst.comp contDiff_snd))
  have hw : ContDiff ℝ (k : WithTop ℕ∞) (fun x : (Euc d × Euc d) × (Euc d × Euc d) => x.2.1) :=
    contDiff_fst.comp contDiff_snd
  have h2 : ContDiff ℝ (k : WithTop ℕ∞) (fun x : (Euc d × Euc d) × (Euc d × Euc d) =>
      chi x.2.1 * chi (δ⁻¹ • x.2.1) * (1 - chi (((m : ℝ) + 1) • x.2.1))) :=
    ((hchic.comp hw).mul (hchic.comp (hw.const_smul δ⁻¹))).mul
      (contDiff_const.sub (hchic.comp (hw.const_smul ((m : ℝ) + 1))))
  have h3 : ContDiff ℝ (k : WithTop ℕ∞) (fun x : (Euc d × Euc d) × (Euc d × Euc d) =>
      (chi x.2.1 * chi (δ⁻¹ • x.2.1) * (1 - chi (((m : ℝ) + 1) • x.2.1))) * F (x.1.2 + x.2.1) x.1.2) := by
    rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hs : ‖x.2.1‖ < 1 / ((m : ℝ) + 1)
    · have hm : (0 : ℝ) < (m : ℝ) + 1 := by positivity
      have hev : (fun x : (Euc d × Euc d) × (Euc d × Euc d) =>
          (chi x.2.1 * chi (δ⁻¹ • x.2.1) * (1 - chi (((m : ℝ) + 1) • x.2.1))) * F (x.1.2 + x.2.1) x.1.2) =ᶠ[𝓝 x]
          fun _ => 0 := by
        have hopen : IsOpen {y : (Euc d × Euc d) × (Euc d × Euc d) | ‖y.2.1‖ < 1 / ((m : ℝ) + 1)} :=
          isOpen_lt (continuous_norm.comp (continuous_fst.comp continuous_snd)) continuous_const
        filter_upwards [hopen.mem_nhds hs] with y hy
        have hy' : ‖y.2.1‖ < 1 / ((m : ℝ) + 1) := hy
        have h1' : ‖((m : ℝ) + 1) • y.2.1‖ ≤ 1 := by
          rw [norm_smul, Real.norm_of_nonneg hm.le]
          rw [lt_div_iff₀ hm] at hy'
          nlinarith
        rw [hchi.2.2.2.1 _ h1']
        ring
      exact contDiffAt_const.congr_of_eventuallyEq hev
    · push Not at hs
      have hne : x.2.1 ≠ 0 := by
        intro h; rw [h, norm_zero] at hs
        have : (0 : ℝ) < 1 / ((m : ℝ) + 1) := by positivity
        linarith
      have hopen : IsOpen {p : Euc d × Euc d | p.1 ≠ p.2} := isOpen_ne_fun continuous_fst continuous_snd
      have hmem : (x.1.2 + x.2.1, x.1.2) ∈ {p : Euc d × Euc d | p.1 ≠ p.2} := by
        show x.1.2 + x.2.1 ≠ x.1.2
        intro h; apply hne; simpa using h
      have hlin : ContDiff ℝ (k : WithTop ℕ∞) (fun x : (Euc d × Euc d) × (Euc d × Euc d) => (x.1.2 + x.2.1, x.1.2)) :=
        ((contDiff_snd.comp contDiff_fst).add hw).prodMk (contDiff_snd.comp contDiff_fst)
      have h4 : ContDiffAt ℝ (k : WithTop ℕ∞)
          (fun x : (Euc d × Euc d) × (Euc d × Euc d) => F (x.1.2 + x.2.1) x.1.2) x :=
        ContDiffAt.comp (g := Function.uncurry F) x (hF.contDiffAt (hopen.mem_nhds hmem)) hlin.contDiffAt
      exact h2.contDiffAt.mul h4
  have := h1.mul h3
  simpa only [r26t8a_Gm, mul_assoc] using this

theorem r26t8a_Gm_eq {d : ℕ} (alpha : ℝ) (chi : Euc d → ℝ) (hchi : NewtonCutoff chi) (δ : ℝ)
    (F : Euc d → Euc d → ℝ) (m : ℕ) {v : Euc d} (hv : 2 ≤ ((m : ℝ) + 1) * ‖v‖) :
    (fun Y : Euc d × Euc d => r26t8a_Gm alpha chi δ F m Y (v, 0)) = r26t8a_G alpha chi δ F v := by
  funext Y
  have h : ‖((m : ℝ) + 1) • v‖ ≥ 2 := by
    rw [norm_smul, Real.norm_of_nonneg (by positivity)]; exact hv
  simp only [r26t8a_Gm, r26t8a_G, hchi.2.2.2.2 _ h, sub_zero, mul_one]

theorem r26t8a_G_meas (d : ℕ) (alpha : ℝ) (halpha : 0 < alpha) (had : alpha < d) (hd : 2 ≤ d)
    (chi : Euc d → ℝ) (hchi : NewtonCutoff chi) (F : Euc d → Euc d → ℝ) {k : ℕ}
    (hF : ContDiffOn ℝ k (Function.uncurry F) {p | p.1 ≠ p.2}) {δ : ℝ} (hδ : 0 < δ) {i : ℕ} (hi : i ≤ k)
    (p : Euc d × Euc d) :
    AEStronglyMeasurable (fun v : Euc d => iteratedFDeriv ℝ i (r26t8a_G alpha chi δ F v) p) volume := by
  haveI : Nontrivial (Euc d) := ⟨⟨0, EuclideanSpace.single ⟨0, by omega⟩ (1 : ℝ), by
    intro h; have := congrArg (fun v : Euc d => v ⟨0, by omega⟩) h; simp at this⟩⟩
  have hcont : ∀ m : ℕ, Continuous (fun v : Euc d =>
      iteratedFDeriv ℝ i (fun Y : Euc d × Euc d => r26t8a_Gm alpha chi δ F m Y (v, 0)) p) := by
    intro m
    have h := r26t8a_partialY_continuous i (E := Euc d × Euc d) (V := ℝ)
      (fun x => r26t8a_Gm alpha chi δ F m x.1 x.2)
      ((r26t8a_Gm_contDiff d alpha halpha had hd chi hchi F hF hδ m).of_le (by exact_mod_cast hi))
    exact h.comp (f := fun v : Euc d => (p, ((v, 0) : Euc d × Euc d))) (by fun_prop)
  refine aestronglyMeasurable_of_tendsto_ae (u := Filter.atTop)
    (f := fun (m : ℕ) (v : Euc d) => iteratedFDeriv ℝ i (fun Y : Euc d × Euc d => r26t8a_Gm alpha chi δ F m Y (v, 0)) p)
    (fun m => (hcont m).aestronglyMeasurable) ?_
  have hae : ∀ᵐ v : Euc d, v ≠ 0 := compl_mem_ae_iff.2 (measure_singleton (0 : Euc d))
  filter_upwards [hae] with v hv
  have hvpos : 0 < ‖v‖ := norm_pos_iff.2 hv
  refine tendsto_const_nhds.congr' ?_
  obtain ⟨m0, hm0⟩ := exists_nat_gt (2 / ‖v‖)
  filter_upwards [eventually_ge_atTop m0] with m hm
  have h1 : 2 ≤ ((m : ℝ) + 1) * ‖v‖ := by
    have h2 : (m0 : ℝ) ≤ m := by exact_mod_cast hm
    rw [div_lt_iff₀ hvpos] at hm0
    nlinarith
  rw [r26t8a_Gm_eq alpha chi hchi δ F m h1]

end HRS.MS.R26T8A
