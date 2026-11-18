import HRS.MS.R26T8AP29i

/-!
# S8.2 T8A P29 (part j): kernels agreeing off the diagonal have equal jets off the diagonal
Used to transfer the P23 bounds from `r26t8a_parametrix` to `r26t8a_parametrixZero`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology
namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82

variable {d : ℕ}

theorem r26t8a_p29_offdiag_eventually {F G : Euc d → Euc d → ℝ} (h : ∀ x y, x ≠ y → F x y = G x y)
    (x y : Euc d) (hxy : x ≠ y) :
    Function.uncurry F =ᶠ[𝓝 (x, y)] Function.uncurry G := by
  have hU : IsOpen {p : Euc d × Euc d | p.1 ≠ p.2} := isOpen_ne_fun continuous_fst continuous_snd
  filter_upwards [hU.mem_nhds (show (x, y) ∈ {p : Euc d × Euc d | p.1 ≠ p.2} from hxy)] with p hp
  exact h p.1 p.2 hp

theorem r26t8a_p29_offdiag_iterated {F G : Euc d → Euc d → ℝ} (h : ∀ x y, x ≠ y → F x y = G x y)
    (n : ℕ) (x y : Euc d) (hxy : x ≠ y) :
    iteratedFDeriv ℝ n (Function.uncurry F) (x, y) = iteratedFDeriv ℝ n (Function.uncurry G) (x, y) :=
  (Filter.EventuallyEq.iteratedFDeriv ℝ (r26t8a_p29_offdiag_eventually h x y hxy) n).eq_of_nhds

theorem r26t8a_p29_offdiag_grad {F G : Euc d → Euc d → ℝ} (h : ∀ x y, x ≠ y → F x y = G x y)
    (x y : Euc d) (hxy : x ≠ y) :
    pairGradX F x y = pairGradX G x y ∧ pairGradY F x y = pairGradY G x y := by
  have hx : (fun x' => F x' y) =ᶠ[𝓝 x] (fun x' => G x' y) := by
    have hU : IsOpen {w : Euc d | w ≠ y} := isOpen_ne
    filter_upwards [hU.mem_nhds (show x ∈ {w : Euc d | w ≠ y} from hxy)] with w hw
    exact h w y hw
  have hy : F x =ᶠ[𝓝 y] G x := by
    have hU : IsOpen {w : Euc d | w ≠ x} := isOpen_ne
    filter_upwards [hU.mem_nhds (show y ∈ {w : Euc d | w ≠ x} from hxy.symm)] with w hw
    exact h x w hw.symm
  exact ⟨by unfold pairGradX gradient; rw [hx.fderiv_eq], by unfold pairGradY gradient; rw [hy.fderiv_eq]⟩

end HRS.MS.R26T8A

end
