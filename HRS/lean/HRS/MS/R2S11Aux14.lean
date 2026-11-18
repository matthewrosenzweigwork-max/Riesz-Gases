import HRS.MS.R2S11Aux13
import HRS.MS.Mov63Aux1
import HRS.MS.MovLinAux7

/-!
# S11.4 item (5): joint continuity (hence measurability) of `(t, x) ↦ ρ t x` on the small class

For `ρ₀` continuous and positive, `ρ t = ρ₀ + √ρ₀ v_t` with `t ↦ v_t` continuous into `Σ^m` (`MovInSmallClass.cont`) and `Σ^m ↪ C_b⁰`
for `m > d/2` (`mn_sobolev_emb_gen`).  Hence `(t,x) ↦ ρ t x` is continuous on `ℝ≥0 × ℝ^d`.
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R2S11

open HRS.Whole
open HRS (Euc)

variable {d : ℕ}

theorem s11_class_continuous {s q β : ℝ} {ρ₀ : Euc d → ℝ} {m : ℕ} {r c₀ : ℝ} {f0 : Euc d → ℝ}
    {ρ : ℝ → Euc d → ℝ} (hρc : Continuous ρ₀) (hρp : ∀ x, 0 < ρ₀ x) (hmd : (d : ℝ) / 2 < m)
    (hρ : MovInSmallClass d s q β ρ₀ m r c₀ f0 ρ) :
    Continuous fun p : ℝ≥0 × Euc d => ρ p.1 p.2 := by
  obtain ⟨C, hC0, hC⟩ := HRS.MS.Mov63.mn_sobolev_emb_gen 0 m (by simpa using hmd)
  have hv : ∀ t : ℝ, 0 ≤ t → Continuous (movV ρ₀ ρ t) := fun t ht => by
    unfold movV
    exact ((hρ.regular t ht).sub hρc).div (hρc.sqrt) (fun x => (Real.sqrt_pos.2 (hρp x)).ne')
  have hF : Continuous fun t : ℝ≥0 => OscSpace.ofFun (d := d) (m : ℝ) (movV ρ₀ ρ (t : ℝ)) :=
    hρ.cont.comp_continuous NNReal.continuous_coe (fun t => t.2)
  -- the sup-norm Lipschitz bound
  have hsup : ∀ t t' : ℝ≥0, ∀ x, |movV ρ₀ ρ t x - movV ρ₀ ρ t' x| ≤
      C * ‖OscSpace.ofFun (d := d) (m : ℝ) (movV ρ₀ ρ t) - OscSpace.ofFun (d := d) (m : ℝ) (movV ρ₀ ρ t')‖ := by
    intro t t' x
    have h1 := (hρ.weighted t t.2).1
    have h2 := (hρ.weighted t' t'.2).1
    have hsub := HRS.MS.MovLin.mov2d_memOsc_sub h1 h2
    obtain ⟨g, hgd, hfg, hbd⟩ := hC _ hsub
    have hcont : Continuous fun z => movV ρ₀ ρ t z - movV ρ₀ ρ t' z := (hv t t.2).sub (hv t' t'.2)
    have hgc : Continuous g := hgd.continuous
    have heq := HRS.MS.Mov63.mn_ae_eq_cont hcont hgc hfg
    have := hbd 0 le_rfl x
    rw [norm_iteratedFDeriv_zero, ← heq] at this
    rw [HRS.MS.MovLin.mov2d_ofFun_sub h1 h2 |>.symm, OscSpace.norm_ofFun _ hsub]
    simpa [Real.norm_eq_abs] using this
  have hVcont : Continuous fun p : ℝ≥0 × Euc d => movV ρ₀ ρ p.1 p.2 := by
    rw [continuous_iff_continuousAt]
    rintro ⟨t0, x0⟩
    rw [ContinuousAt, tendsto_iff_dist_tendsto_zero]
    have hb : Tendsto (fun p : ℝ≥0 × Euc d => C * ‖OscSpace.ofFun (d := d) (m : ℝ) (movV ρ₀ ρ p.1) -
        OscSpace.ofFun (d := d) (m : ℝ) (movV ρ₀ ρ t0)‖ + dist (movV ρ₀ ρ t0 p.2) (movV ρ₀ ρ t0 x0))
        (𝓝 (t0, x0)) (𝓝 0) := by
      have e1 : Tendsto (fun p : ℝ≥0 × Euc d => C * ‖OscSpace.ofFun (d := d) (m : ℝ) (movV ρ₀ ρ p.1) -
          OscSpace.ofFun (d := d) (m : ℝ) (movV ρ₀ ρ t0)‖) (𝓝 (t0, x0)) (𝓝 (C * ‖(0 : OscSpace d (m : ℝ))‖)) := by
        refine Tendsto.const_mul _ ?_
        have : Continuous fun p : ℝ≥0 × Euc d => OscSpace.ofFun (d := d) (m : ℝ) (movV ρ₀ ρ p.1) -
            OscSpace.ofFun (d := d) (m : ℝ) (movV ρ₀ ρ t0) := (hF.comp continuous_fst).sub continuous_const
        have h0 := (this.norm.tendsto (t0, x0))
        simpa using h0
      have e2 : Tendsto (fun p : ℝ≥0 × Euc d => dist (movV ρ₀ ρ t0 p.2) (movV ρ₀ ρ t0 x0)) (𝓝 (t0, x0)) (𝓝 0) := by
        have : Continuous fun p : ℝ≥0 × Euc d => dist (movV ρ₀ ρ t0 p.2) (movV ρ₀ ρ t0 x0) :=
          ((hv t0 t0.2).comp continuous_snd).dist continuous_const
        simpa using this.tendsto (t0, x0)
      simpa using e1.add e2
    refine squeeze_zero (fun p => dist_nonneg) (fun p => ?_) hb
    calc dist (movV ρ₀ ρ p.1 p.2) (movV ρ₀ ρ t0 x0)
        ≤ dist (movV ρ₀ ρ p.1 p.2) (movV ρ₀ ρ t0 p.2) + dist (movV ρ₀ ρ t0 p.2) (movV ρ₀ ρ t0 x0) :=
          dist_triangle _ _ _
      _ ≤ _ := by
          refine add_le_add ?_ le_rfl
          rw [Real.dist_eq]
          exact hsup p.1 t0 p.2
  -- ρ t x = ρ₀ x + √ρ₀ x · v_t x
  have e : (fun p : ℝ≥0 × Euc d => ρ p.1 p.2) =
      fun p => ρ₀ p.2 + Real.sqrt (ρ₀ p.2) * movV ρ₀ ρ p.1 p.2 := by
    funext p
    unfold movV
    have := (Real.sqrt_pos.2 (hρp p.2)).ne'
    field_simp
    ring
  rw [e]
  exact (hρc.comp continuous_snd).add ((hρc.sqrt.comp continuous_snd).mul hVcont)

end HRS.MS.R2S11
