import HRS.MC.S7FCB
import HRS.MC.S7FCDefs
import HRS.MC.S7FCW3F2

/-!
# S7FCHA1: existence of the FC-B/FC-G kernel data (`FCKernelData`) for a regime

For every regime `R` there are `ε c` and smooth finite-rank symmetric kernels `K k L` (`k` a nonzero lattice point,
`L ∈ ℕ`) with `FCKernelData R ε c K`.  Route: the envelope constant `c` and the bound
`|h_{∇e_k}| ≤ A ⟨k⟩² (g + c)` (`s7b_envelope`, `s7fcw3_hT_env`), the exponent `ε` with `(2 + ε) s < d`, and the proved
`s7_FC_B_tail_kernels_proof` applied for every mode `k` to the kernel `h_{∇e_k}` (symmetric, measurable) with the density
`ρ^0 = ρ₀`; the finite-rank decomposition is then chosen with `choose`.  This is the input of the assembly
`s7_FC_H_every_B_proof` (the hypothesis `hK` of H2 and H3).
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.S7FCH

open HRS HRS.Sec7 HRS.MC.Sec7 HRS.MC.SEdge HRS.MC.QRSpec HRS.MC.Sec7.FCPlan

variable {d : ℕ}

/-- A positive `ε` with `(2 + ε) s < d` when `s < d/2`. -/
theorem S7FCHA_exists_eps {s : ℝ} (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) :
    ∃ ε : ℝ, 0 < ε ∧ (2 + ε) * s < d := by
  have hd0 : 0 < (d : ℝ) - 2 * s := by linarith
  refine ⟨((d : ℝ) - 2 * s) / (2 * (s + 1)), by positivity, ?_⟩
  have h1 : 0 < 2 * (s + 1) := by positivity
  have key : ((d : ℝ) - 2 * s) / (2 * (s + 1)) * s < (d : ℝ) - 2 * s := by
    rw [div_mul_eq_mul_div, div_lt_iff₀ h1]
    nlinarith
  linarith

/-- A `FRKernel` with prescribed `toFun` from `s7_IsFiniteRankSmooth`. -/
theorem S7FCHA_exists_frkernel {h : Torus d → Torus d → ℝ} (hh : s7_IsFiniteRankSmooth h) :
    ∃ K : FRKernel d, K.toFun = h := by
  obtain ⟨n, f, c, hf, hc, he⟩ := hh
  refine ⟨⟨n, f, c, hf, hc⟩, ?_⟩
  funext x y
  exact (he x y).symm

/-- **Kernel data**: for every regime there is `FCKernelData`. -/
theorem S7FCHA_kernelData (R : Regime d) :
    ∃ (ε c : ℝ) (K : NonzeroLattice d → ℕ → FRKernel d), FCKernelData R ε c K := by
  obtain ⟨K0, c, hK0, hgc0, hwc, henv⟩ := HRS.MC.Sec7.S7b.s7b_envelope R.hd R.D.hs0 R.hs
  have hsd : R.D.s < (d : ℝ) := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast R.hd
    have := R.hs
    linarith
  obtain ⟨ε, hε, hεs⟩ := S7FCHA_exists_eps R.D.hs0 R.hs
  have hρ : SmoothPosDensity (R.ρ 0) := by rw [R.init]; exact R.hρ₀
  obtain ⟨C, hC⟩ := HRS.MC.Sec7.FCB.s7_FC_B_tail_kernels_proof R.hd R.D.hs0 R.hs (R.ρ 0) hρ c hwc
  set A : ℝ := K0 * d * (3 * Real.sqrt 2) + 1 with hA
  have hA0 : 0 ≤ A := by
    have : 0 ≤ K0 * d * (3 * Real.sqrt 2) := by positivity
    linarith
  have hex : ∀ k : NonzeroLattice d, ∃ hL : ℕ → Torus d → Torus d → ℝ,
      (∀ L, s7_IsFiniteRankSmooth (hL L)) ∧
      (∀ L x y, x ≠ y → |hL L x y| ≤ C * (A * Lattice.jp k.1 ^ 2) * (periodicRiesz d R.D.s (x - y) + c)) ∧
      Tendsto (fun L => eLpNorm (fun p : Torus d × Torus d =>
          hL L p.1 p.2 - hTransport d R.D.s (Torus.realMode k) p.1 p.2) (ENNReal.ofReal (2 + ε))
        ((withDensityReal (R.ρ 0)).prod (withDensityReal (R.ρ 0)))) atTop (𝓝 0) := by
    intro k
    have hms := HRS.MC.Sec7.S7FCW3.s7fcw3_hT_meas_symm hsd (HRS.FieldSingAux.isSmooth_realMode (d := d) k)
    refine hC (A * Lattice.jp k.1 ^ 2) (by positivity) _ hms.1 hms.2 (fun x y hxy => ?_) ε hε hεs
    exact HRS.MC.Sec7.S7FCW3.s7fcw3_hT_env hK0 k henv x y (by linarith [hwc (x - y) (sub_ne_zero.2 hxy)])
  choose hL hLd hLB hLT using hex
  have hfr : ∀ k L, ∃ K : FRKernel d, K.toFun = hL k L := fun k L => S7FCHA_exists_frkernel (hLd k L)
  choose K hK using hfr
  refine ⟨ε, c, K, hwc, hε, hεs, fun k => ⟨C * (A * Lattice.jp k.1 ^ 2), fun L x y hxy => ?_⟩, fun k => ?_⟩
  · rw [hK]; exact hLB k L x y hxy
  · simp only [hK]; exact hLT k

end HRS.MC.Sec7.S7FCH

end
