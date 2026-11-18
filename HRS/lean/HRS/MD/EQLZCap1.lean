import HRS.PDE.TorusFPExistAux13

/-!
# EQ-LZ packet CAP, helper 1: C¹ mollification and the energy density `capG`

Plan of the proof of `eqlz_cap` (spec `HRS/MD/EQLZSpec.lean`, route (i)-(iv)):

* (i) truncation `Φ_K = K p(Φ/K)` (`p(x) = x` on `[-1,1]`, bounded, `p'` bounded): `Φ_K → Φ` in `L²(ν)`, energies
  converge by dominated convergence (`EQLZCap3`).
* (ii) cut-off `χ_m = ∏_{i<j} Θ_m(s(x_i - x_j))` (`s(u) = ∑ (1 - cos 2πu_k)`, `Θ_m(τ) = ρ(log τ/m + 2)`),
  with `∫ ‖∇χ_m‖² → 0` (dyadic shells and `vol{s ≤ τ} ≤ τ/2`, `d ≥ 2`; `EQLZCap4`).
* (iii) `χ_m Φ_K` is `C¹` on the whole covering space (it vanishes near the collision set); a `C¹` mollification
  (this file) gives smooth `G` with `G → χ_m Φ_K` and `∇G → ∇(χ_m Φ_K)` uniformly (`EQLZCap2`).
* (iv) diagonal sequence (`CapGood`, `EQLZCap2`/`EQLZCap3`), and the transfer to `Config d N` through
  `d1_configEquiv`, the density bound `μ ≤ C dx`, and the collision-set null set (`EQLZCap5`).

This file: generic `C¹` approximation of a `C¹` function on the torus `𝕋^n` by smooth functions, uniformly together
with the gradient (copy of `d1_exists_C2_approx` without the second derivative).
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped Convolution

namespace HRS.MD.EQLZ.Cap

variable {n : ℕ}

/-- The energy density `‖∇φ‖²` of a function on the torus, through the periodic lift. -/
def capG (φ : Torus n → ℝ) (x : Torus n) : ℝ := ‖fderiv ℝ (Torus.lift φ) (Torus.rep x)‖ ^ 2

theorem capG_eq_grad (φ : Torus n → ℝ) (x : Torus n) : ‖Torus.grad φ x‖ ^ 2 = capG φ x := by
  unfold capG Torus.grad gradient
  rw [LinearIsometryEquiv.norm_map]

set_option maxHeartbeats 1600000 in
/-- `C¹`-approximation: a `C¹` function on the torus is approximated, together with its gradient,
uniformly by smooth functions. -/
theorem exists_C1_approx {φ : Torus n → ℝ} (hφ : ContDiff ℝ 1 (Torus.lift φ)) {ε : ℝ} (hε : 0 < ε) :
    ∃ ψ : Torus n → ℝ, Torus.IsSmooth ψ ∧ ∀ x, |φ x - ψ x| ≤ ε ∧
      ‖fderiv ℝ (Torus.lift φ) (Torus.rep x) - fderiv ℝ (Torus.lift ψ) (Torus.rep x)‖ ≤ ε := by
  set F := Torus.lift φ with hFdef
  have hF0 : ContDiff ℝ 1 F := hφ
  have hF1c : Continuous (fderiv ℝ F) := hF0.continuous_fderiv one_ne_zero
  have p0 : ∀ (y : Euc n) (k : Lattice n), F (y + Lattice.toEuc k) = F y :=
    fun y k => Torus.lift_periodic φ y k
  have p1 := d1_fderiv_periodic p0
  obtain ⟨B0, hB0⟩ := d1_periodic_bounded hF0.continuous p0
  obtain ⟨B1, hB1⟩ := d1_periodic_bounded hF1c p1
  have u0 := d1_periodic_uniformContinuous hF0.continuous p0
  have u1 := d1_periodic_uniformContinuous hF1c p1
  obtain ⟨r0, hr0, h0⟩ := Metric.uniformContinuous_iff.1 u0 ε hε
  obtain ⟨r1, hr1, h1⟩ := Metric.uniformContinuous_iff.1 u1 ε hε
  set r : ℝ := min r0 r1 with hr
  have hrpos : 0 < r := lt_min hr0 hr1
  let φb : ContDiffBump (0 : Euc n) := ⟨r / 2, r, half_pos hrpos, half_lt_self hrpos⟩
  set ρ : Euc n → ℝ := φb.normed volume with hρ
  have hρi : Integrable ρ := φb.integrable_normed (μ := volume)
  have hρ0 : ∀ t, 0 ≤ ρ t := fun t => φb.nonneg_normed (μ := volume) t
  set ψr : Euc n → ℝ := d1_mol ρ F with hψr
  have hψsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψr := by
    have := (φb.hasCompactSupport_normed (μ := volume)).contDiff_convolution_left
      (ContinuousLinearMap.lsmul ℝ ℝ)
      (φb.contDiff_normed (μ := volume) (n := ⊤)) (hF0.continuous.locallyIntegrable (μ := volume))
    exact this
  have hψp : ∀ (y : Euc n) (k : Lattice n), ψr (y + Lattice.toEuc k) = ψr y := by
    intro y k
    simp only [hψr, d1_mol]
    refine integral_congr_ae (ae_of_all _ fun t => ?_)
    have : y + Lattice.toEuc k - t = (y - t) + Lattice.toEuc k := by abel
    simp only [this, p0]
  have hder1 : ∀ y, fderiv ℝ ψr y = d1_mol ρ (fderiv ℝ F) y := fun y =>
    (d1_mol_hasFDerivAt hρi hρ0 hF0 hB0 hB1 y).fderiv
  have hmg0 : AEStronglyMeasurable F volume := hF0.continuous.aestronglyMeasurable
  have e0 : ∀ y, dist (ψr y) (F y) ≤ ε := fun y =>
    φb.dist_normed_convolution_le (μ := volume) hmg0 (fun x hx => by
      have : dist x y < r0 := lt_of_lt_of_le hx (by
        show r ≤ r0
        exact min_le_left _ _)
      exact (h0 this).le)
  have e1 : ∀ y, ‖d1_mol ρ (fderiv ℝ F) y - fderiv ℝ F y‖ ≤ ε := fun y => by
    have := φb.dist_normed_convolution_le (μ := volume) hF1c.aestronglyMeasurable
      (x₀ := y) (ε := ε) (fun x hx => by
      have : dist x y < r1 := lt_of_lt_of_le hx (by
        show r ≤ r1
        exact min_le_right _ _)
      exact (h1 this).le)
    rw [dist_eq_norm] at this
    exact this
  let ψ : Torus n → ℝ := fun x => ψr (Torus.rep x)
  have hlift : Torus.lift ψ = ψr := by
    funext y
    exact periodic_rep_mk ψr hψp y
  refine ⟨ψ, ?_, fun x => ?_⟩
  · unfold Torus.IsSmooth Torus.IsCk
    rw [hlift]; exact hψsm
  have hφx : φ x = F (Torus.rep x) := by simp [hFdef, Torus.lift, Torus.mk_rep]
  refine ⟨?_, ?_⟩
  · rw [hφx, abs_sub_comm]
    have := e0 (Torus.rep x)
    rw [Real.dist_eq] at this
    exact this
  · rw [hlift, hder1, norm_sub_rev]
    exact e1 (Torus.rep x)

end HRS.MD.EQLZ.Cap
