import HRS.MS.R26T8AP11f6
import HRS.MS.R26T8AP11lb
import HRS.MS.R26T8AP06b

/-!
# S8.2 T8A P11f (part 7): the `x`-derivative of a conormal pair is conormal of order `σ+1`
`r26t8a_f7_dx_conormal`: `Conormal (k+1) b M σ A F → Conormal k b M (σ+1) (2A) (dx_i F)`, `dx_i F x y = ∂_{x_i} F(x,y)`.
In centre/relative coordinates `midPair (dx_i F) = (½∂_{Y_i} + ∂_{w_i}) midPair F`; use `nest_dY_le`, `nest_succ` on the cutoff `psiCut * midPair F`.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.Wad

variable {d : ℕ}

/-- `∂_{x_i}` of a pair function (partial derivative in the first slot). -/
def r26t8a_dx (i : Fin d) (F : Euc d → Euc d → ℝ) (x y : Euc d) : ℝ :=
  fderiv ℝ (fun x' => F x' y) x (EuclideanSpace.single i 1)

theorem r26t8a_f7_dx_eq {k : ℕ} {F : Euc d → Euc d → ℝ}
    (hF : ContDiffOn ℝ ((k + 1 : ℕ) : WithTop ℕ∞) (Function.uncurry F) {p | p.1 ≠ p.2}) (i : Fin d)
    (p : Euc d × Euc d) (hp : p.1 ≠ p.2) :
    r26t8a_dx i F p.1 p.2 = fderiv ℝ (Function.uncurry F) p (EuclideanSpace.single i 1, 0) := by
  have hopen : IsOpen {p : Euc d × Euc d | p.1 ≠ p.2} := isOpen_ne_fun continuous_fst continuous_snd
  have hdiff : DifferentiableAt ℝ (Function.uncurry F) p :=
    (hF.contDiffAt (hopen.mem_nhds hp)).differentiableAt (by simp)
  have := hdiff.hasFDerivAt.comp p.1 (hasFDerivAt_prodMk_left (𝕜 := ℝ) p.1 p.2)
  unfold r26t8a_dx
  have e : (fun x' => F x' p.2) = Function.uncurry F ∘ fun x' => (x', p.2) := rfl
  rw [e, this.fderiv]
  simp

theorem r26t8a_f7_dx_contDiffOn {k : ℕ} {F : Euc d → Euc d → ℝ}
    (hF : ContDiffOn ℝ ((k + 1 : ℕ) : WithTop ℕ∞) (Function.uncurry F) {p | p.1 ≠ p.2}) (i : Fin d) :
    ContDiffOn ℝ (k : WithTop ℕ∞) (Function.uncurry (r26t8a_dx i F)) {p | p.1 ≠ p.2} := by
  have hopen : IsOpen {p : Euc d × Euc d | p.1 ≠ p.2} := isOpen_ne_fun continuous_fst continuous_snd
  have h1 : ContDiffOn ℝ (k : WithTop ℕ∞) (fderiv ℝ (Function.uncurry F)) {p | p.1 ≠ p.2} :=
    hF.fderiv_of_isOpen hopen (by push_cast; exact le_rfl)
  have h2 := h1.clm_apply (contDiffOn_const (c := ((EuclideanSpace.single i 1, 0) : Euc d × Euc d)))
  refine h2.congr fun p hp => ?_
  exact r26t8a_f7_dx_eq hF i p hp

end HRS.MS.R26T8A
