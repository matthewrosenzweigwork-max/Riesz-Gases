import HRS.MS.S81w2Weak
import HRS.MS.S81w2Synth
import HRS.MS.S81w2Cov
import HRS.MS.S81w2Orth

/-!
# S8.1 (worker S81W2): the closed gradient expansion of the classical orbits

For the critical thermal reference `μ = ρ dx`, retained spectral data `(e_l, ω_l)` with orbit coefficients
`β⟨P_μ U_tφ_α, R e_l⟩ = e^{-tω_l} a_{αl}` and `t > 0`, put `c_l = e^{-tω_l} a_{αl}`.  Then
`Σ ω_l c_l² < ∞`, the classical gradient `∇U_tφ_α` is the `L²(μ;ℝ^d)`-limit of `Σ_{l<L} c_l ∇e_l`, and

`∫ ‖∇U_tφ_α - Σ_{l<L} c_l ∇e_l‖² dμ = Σ_{l ≥ L} ω_l c_l²`   (`s81w2_grad_closure`)

(Lemma 2.1 of the Pro paper, equation `eq:gradtail`; synthesis + `grad_orth` + the weak identification
`s81w2_weak_ident`).
-/

set_option autoImplicit false
set_option maxRecDepth 4000

noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal BigOperators ContDiff InnerProductSpace

namespace HRS.Whole.S81W2

open HRS HRS.Whole HRS.MS.S88Breakdown

variable {d : ℕ}

theorem s81w2_gradient_continuous {u : Euc d → ℝ} (hu : ContDiff ℝ ∞ u) :
    Continuous fun x => gradient u x :=
  (InnerProductSpace.toDual ℝ (Euc d)).symm.continuous.comp (hu.continuous_fderiv (by simp))

theorem s81w2_inner_gradient (u : Euc d → ℝ) (x v : Euc d) :
    inner ℝ v (gradient u x) = fderiv ℝ u x v := by
  rw [real_inner_comm]
  exact InnerProductSpace.toDual_symm_apply

theorem s81w2_grad_memLp {μ : Measure (Euc d)} {u : Euc d → ℝ} (hu : ContDiff ℝ ∞ u)
    (hint : Integrable (fun x => inner ℝ (gradient u x) (gradient u x)) μ) :
    MemLp (fun x => gradient u x) 2 μ := by
  refine (memLp_two_iff_integrable_sq_norm (s81w2_gradient_continuous hu).aestronglyMeasurable).2 ?_
  refine hint.congr (Filter.Eventually.of_forall fun x => ?_)
  simp [real_inner_self_eq_norm_sq]

/-- Finite sums commute with the passage to `Lp` classes. -/
theorem s81w2_partial {α E : Type*} [MeasurableSpace α] {μ : Measure α} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (u : ℕ → α → E) (hu : ∀ l, MemLp (u l) 2 μ) (c : ℕ → ℝ) (L : ℕ) :
    ∃ hF : MemLp (fun x => ∑ l ∈ Finset.range L, c l • u l x) 2 μ,
      hF.toLp (fun x => ∑ l ∈ Finset.range L, c l • u l x) =
        ∑ l ∈ Finset.range L, c l • (hu l).toLp (u l) := by
  induction L with
  | zero =>
    refine ⟨by simpa using (memLp_zero : MemLp (fun _ : α => (0 : E)) 2 μ), ?_⟩
    simp only [Finset.range_zero, Finset.sum_empty]
    exact (MemLp.toLp_zero _)
  | succ L ih =>
    obtain ⟨hF, hFe⟩ := ih
    have hfun : (fun x => ∑ l ∈ Finset.range (L + 1), c l • u l x) =
        fun x => (∑ l ∈ Finset.range L, c l • u l x) + c L • u L x := by
      funext x; rw [Finset.sum_range_succ]
    have hmem : MemLp (fun x => ∑ l ∈ Finset.range (L + 1), c l • u l x) 2 μ := by
      rw [hfun]; exact hF.add ((hu L).const_smul (c L))
    refine ⟨hmem, ?_⟩
    rw [Finset.sum_range_succ, ← hFe]
    refine Lp.ext ?_
    filter_upwards [hmem.coeFn_toLp, hF.coeFn_toLp, ((hu L).const_smul (c L)).coeFn_toLp,
      Lp.coeFn_add (hF.toLp (fun x => ∑ l ∈ Finset.range L, c l • u l x))
        (c L • (hu L).toLp (u L)),
      Lp.coeFn_smul (c L) ((hu L).toLp (u L)), (hu L).coeFn_toLp] with x h1 h2 h3 h4 h5 h6
    rw [h4, Pi.add_apply, h2, h5, Pi.smul_apply, h6, h1, Finset.sum_range_succ]

end HRS.Whole.S81W2
