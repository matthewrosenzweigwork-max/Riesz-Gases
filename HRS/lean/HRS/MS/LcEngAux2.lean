import HRS.MS.LcEngAux1

/-!
# LC-4, part 2: differentiation under `E` with an integrable (not uniform) bound

`PoisSg.sg_iteratedFDeriv_integral` asks for derivative bounds that are uniform in `ω`.  For the
engine the derivatives of `g ∘ X_v(ω)` are only bounded by `C (1+κ(ω))^N ‖g‖_{k,b}` with `κ` a
noise-dependent quantity, which is integrable but not bounded.  This file proves the same
differentiation theorem with an integrable majorant `Φ ω` of all `‖D^i G ω x‖`, `i ≤ k`, uniform in `x`
(`lc4_iteratedFDeriv_integral`), and the passage from operator-norm decay to `decayNormE`
(`lc4_decayNormE_le`).

Helper lemmas carry the prefix `lc4_`.
-/

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open HRS HRS.Whole

noncomputable section

namespace HRS.MS.Lc

variable {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]

theorem lc4_hasFDerivAt_integral {μ : Measure Ω} {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    (H : Ω → Euc d → V) (hdiff : ∀ ω, Differentiable ℝ (H ω)) {Φ0 Φ1 : Ω → ℝ}
    (hΦ1 : Integrable Φ1 μ)
    (h0 : ∀ ω x, ‖H ω x‖ ≤ Φ0 ω) (hΦ0 : Integrable Φ0 μ)
    (h1 : ∀ ω x, ‖fderiv ℝ (H ω) x‖ ≤ Φ1 ω)
    (hm0 : ∀ x, AEStronglyMeasurable (fun ω => H ω x) μ)
    (hm1 : ∀ x, AEStronglyMeasurable (fun ω => fderiv ℝ (H ω) x) μ) (x : Euc d) :
    HasFDerivAt (fun x => ∫ ω, H ω x ∂μ) (∫ ω, fderiv ℝ (H ω) x ∂μ) x :=
  hasFDerivAt_integral_of_dominated_of_fderiv_le (F := fun x ω => H ω x)
    (F' := fun x ω => fderiv ℝ (H ω) x) (s := Set.univ) (bound := Φ1)
    Filter.univ_mem (Eventually.of_forall hm0)
    (hΦ0.mono' (hm0 x) (Eventually.of_forall fun ω => h0 ω x)) (hm1 x)
    (Eventually.of_forall fun ω y _ => h1 ω y) hΦ1
    (Eventually.of_forall fun ω y _ => (hdiff ω y).hasFDerivAt)

/-- **Differentiation under `E` with an integrable majorant.**  If every `G ω` is `C^k`, all
`‖D^i (G ω) x‖`, `i ≤ k`, are bounded by `Φ ω` with `Φ` integrable (uniformly in `x`), and the
derivatives are measurable in `ω` for fixed `x`, then `x ↦ ∫ G ω x dμ` is `C^k` and
`D^i ∫ G = ∫ D^i G`. -/
theorem lc4_iteratedFDeriv_integral {μ : Measure Ω} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (G : Ω → Euc d → F) (k : ℕ) (hG : ∀ ω, ContDiff ℝ (k : WithTop ℕ∞) (G ω))
    {Φ : Ω → ℝ} (hΦ : Integrable Φ μ)
    (hbd : ∀ i ≤ k, ∀ ω x, ‖iteratedFDeriv ℝ i (G ω) x‖ ≤ Φ ω)
    (hmeas : ∀ i ≤ k, ∀ x, AEStronglyMeasurable (fun ω => iteratedFDeriv ℝ i (G ω) x) μ) :
    ContDiff ℝ (k : WithTop ℕ∞) (fun x => ∫ ω, G ω x ∂μ) ∧
      ∀ i ≤ k, ∀ x, iteratedFDeriv ℝ i (fun x => ∫ ω, G ω x ∂μ) x =
        ∫ ω, iteratedFDeriv ℝ i (G ω) x ∂μ := by
  -- one differentiation step
  have step : ∀ i < k, ∀ x, HasFDerivAt (fun x => ∫ ω, iteratedFDeriv ℝ i (G ω) x ∂μ)
      (∫ ω, fderiv ℝ (iteratedFDeriv ℝ i (G ω)) x ∂μ) x := by
    intro i hi x
    refine lc4_hasFDerivAt_integral (fun ω => iteratedFDeriv ℝ i (G ω))
      (fun ω => (hG ω).differentiable_iteratedFDeriv (by exact_mod_cast hi)) (Φ1 := Φ) hΦ
      (fun ω y => hbd i hi.le ω y) hΦ (fun ω y => ?_)
      (fun y => hmeas i hi.le y) (fun y => ?_) x
    · have e : fderiv ℝ (iteratedFDeriv ℝ i (G ω)) y =
          continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (i + 1) => Euc d) F
            (iteratedFDeriv ℝ (i + 1) (G ω) y) := by
        rw [iteratedFDeriv_succ_eq_comp_left]; simp
      rw [e, LinearIsometryEquiv.norm_map]; exact hbd (i + 1) hi ω y
    · have e : (fun ω => fderiv ℝ (iteratedFDeriv ℝ i (G ω)) y) = fun ω =>
          continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (i + 1) => Euc d) F
            (iteratedFDeriv ℝ (i + 1) (G ω) y) := by
        funext ω; rw [iteratedFDeriv_succ_eq_comp_left]; simp
      rw [e]
      exact (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (i + 1) => Euc d) F).continuous.comp_aestronglyMeasurable (hmeas (i + 1) hi y)
  have hS : ∀ i ≤ k, iteratedFDeriv ℝ i (fun x => ∫ ω, G ω x ∂μ) =
      fun x => ∫ ω, iteratedFDeriv ℝ i (G ω) x ∂μ := by
    intro i
    induction i with
    | zero =>
      intro _
      funext x
      rw [iteratedFDeriv_zero_eq_comp]
      simp only [Function.comp]
      have : ∀ ω, iteratedFDeriv ℝ 0 (G ω) x =
          (continuousMultilinearCurryFin0 ℝ (Euc d) F).symm (G ω x) := fun ω => by
        rw [iteratedFDeriv_zero_eq_comp]; rfl
      simp_rw [this]
      exact ((continuousMultilinearCurryFin0 ℝ (Euc d) F).symm.toContinuousLinearEquiv.integral_comp_comm _).symm
    | succ i ih =>
      intro hi
      funext x
      rw [iteratedFDeriv_succ_eq_comp_left, Function.comp, ih (Nat.le_of_succ_le hi),
        (step i hi x).fderiv]
      have : ∀ ω, iteratedFDeriv ℝ (i + 1) (G ω) x =
          (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (i + 1) => Euc d) F).symm
            (fderiv ℝ (iteratedFDeriv ℝ i (G ω)) x) := fun ω => by
        rw [iteratedFDeriv_succ_eq_comp_left]; rfl
      simp_rw [this]
      exact (PoisSg.sg_integral_curryLeft i _).symm
  refine ⟨?_, fun i hi x => by rw [hS i hi]⟩
  have hk : ∀ i ≤ k, Continuous fun x => ∫ ω, iteratedFDeriv ℝ i (G ω) x ∂μ := by
    intro i hi
    exact continuous_of_dominated (bound := Φ) (fun y => hmeas i hi y)
      (fun y => Eventually.of_forall fun ω => hbd i hi ω y) hΦ
      (Eventually.of_forall fun ω => (hG ω).continuous_iteratedFDeriv (by exact_mod_cast hi))
  have key : ContDiff ℝ ((k : ℕ∞) : WithTop ℕ∞) (fun x => ∫ ω, G ω x ∂μ) := by
    refine contDiff_iff_continuous_differentiable.2 ⟨fun i hi => ?_, fun i hi => ?_⟩
    · have hi' : i ≤ k := by exact_mod_cast hi
      rw [hS i hi']; exact hk i hi'
    · have hi' : i < k := by exact_mod_cast hi
      rw [hS i hi'.le]
      exact fun x => (step i hi' x).differentiableAt
  exact_mod_cast key

/-- The coordinate derivative is bounded by the operator norm. -/
theorem lc4_partial_le {f : Euc d → ℝ} (j : ℕ) (I : Fin j → Fin d) (x : Euc d) :
    |partialDeriv I f x| ≤ ‖iteratedFDeriv ℝ j f x‖ := by
  unfold partialDeriv
  have := (iteratedFDeriv ℝ j f x).le_opNorm (fun l => EuclideanSpace.single (I l) (1 : ℝ))
  simpa [EuclideanSpace.norm_single] using this

/-- From weighted operator-norm bounds to `decayNormE`. -/
theorem lc4_decayNormE_le {k : ℕ} {b : ℝ} {F : Euc d → ℝ} {M : ℝ}
    (hF : ∀ j ≤ k, ∀ x : Euc d, jbracket x ^ (b + (j : ℝ)) * ‖iteratedFDeriv ℝ j F x‖ ≤ M) :
    decayNormE k b F ≤ ENNReal.ofReal M := by
  unfold decayNormE derivSupE
  refine iSup_le fun j => iSup_le fun I => iSup_le fun x => ?_
  refine ENNReal.ofReal_le_ofReal ?_
  have hj : (j : ℕ) ≤ k := Nat.lt_succ_iff.mp j.2
  have hpos : 0 ≤ jbracket x ^ (b + ((j : ℕ) : ℝ)) :=
    Real.rpow_nonneg (Real.sqrt_nonneg _) _
  exact (mul_le_mul_of_nonneg_left (lc4_partial_le (j : ℕ) I x) hpos).trans (hF j hj x)

end HRS.MS.Lc
