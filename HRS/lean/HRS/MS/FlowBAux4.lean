import HRS.MS.FlowBAux3

/-!
# MS-FLOW-B, `C^{m+1}` regularity of the Nemytskii-integral operator

`𝒩 α = (t ↦ ∫_0^{clampT T t} b (clampT T s) (α s) ds)` on `X = ℝ →ᵇ E`, with the explicit Taylor series
`p α j = Vop T j (s ↦ D^j b̃ s (α s))`.
-/

open MeasureTheory Filter Topology Set Metric
open scoped BoundedContinuousFunction

namespace HRS.MS.FlowB

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- Drift bounds (same fields as `IsDriftBounds`), generic space. -/
structure DB (T : ℝ) (m : ℕ) (Λ : ℝ) (b : ℝ → E → E) : Prop where
  cont : ContinuousOn (fun p : ℝ × E => b p.1 p.2) (Icc (0 : ℝ) T ×ˢ univ)
  smooth : ∀ τ ∈ Icc (0 : ℝ) T, ContDiff ℝ ((m + 1 : ℕ) : WithTop ℕ∞) (b τ)
  deriv_bound : ∀ τ ∈ Icc (0 : ℝ) T, ∀ j : ℕ, 1 ≤ j → j ≤ m + 1 → ∀ x : E,
    ‖iteratedFDeriv ℝ j (b τ) x‖ ≤ Λ
  growth : ∀ τ ∈ Icc (0 : ℝ) T, ∀ x : E, ‖b τ x‖ ≤ Λ * (1 + ‖x‖)

/-- The clamped drift. -/
def bt (T : ℝ) (b : ℝ → E → E) (s : ℝ) : E → E := b (clampT T s)

theorem DB.Λ_nonneg {T : ℝ} (hT : 0 ≤ T) {m : ℕ} {Λ : ℝ} {b : ℝ → E → E} (hb : DB T m Λ b) :
    0 ≤ Λ :=
  (norm_nonneg _).trans (hb.deriv_bound 0 ⟨le_rfl, hT⟩ 1 le_rfl (by omega) 0)

theorem DB.good {T : ℝ} (hT : 0 ≤ T) {m : ℕ} {Λ : ℝ} {b : ℝ → E → E} (hb : DB T m Λ b)
    {j : ℕ} (hj : j ≤ m + 1) : Good (fun s y => iteratedFDeriv ℝ j (bt T b s) y) where
  cont s := (hb.smooth _ (clampT_mem hT s)).continuous_iteratedFDeriv
    (by exact_mod_cast hj)
  meas y := by
    refine sm_iteratedFDeriv (bt T b) (n := ((m + 1 : ℕ) : WithTop ℕ∞))
      (fun s => hb.smooth _ (clampT_mem hT s)) (fun y => ?_) j (by exact_mod_cast hj) y
    refine Continuous.stronglyMeasurable ?_
    have := hb.cont.comp (f := fun s : ℝ => (clampT T s, y)) (s := univ)
      (t := Icc (0 : ℝ) T ×ˢ univ)
      ((continuous_clampT T).prodMk continuous_const).continuousOn
      (fun s _ => ⟨clampT_mem hT s, trivial⟩)
    exact continuousOn_univ.1 this
  bdd R := by
    have hΛ := hb.Λ_nonneg hT
    by_cases hj0 : j = 0
    · subst hj0
      refine ⟨Λ * (1 + max R 0), fun s y hy => ?_⟩
      rw [norm_iteratedFDeriv_zero]
      refine (hb.growth _ (clampT_mem hT s) y).trans ?_
      gcongr
      exact hy.trans (le_max_left _ _)
    · exact ⟨Λ, fun s y _ => hb.deriv_bound _ (clampT_mem hT s) j (Nat.one_le_iff_ne_zero.2 hj0)
        hj y⟩

/-- The Taylor series of the Nemytskii-integral operator. -/
noncomputable def tay (T : ℝ) (b : ℝ → E → E) (α : ℝ →ᵇ E) :
    FormalMultilinearSeries ℝ (ℝ →ᵇ E) (ℝ →ᵇ E) :=
  fun j => Vop T j (fun s => iteratedFDeriv ℝ j (bt T b s) (α s))

/-- The Nemytskii-integral operator. -/
noncomputable def nem (T : ℝ) (b : ℝ → E → E) (α : ℝ →ᵇ E) : ℝ →ᵇ E := (tay T b α 0).curry0

theorem hasFTaylor {T : ℝ} (hT : 0 ≤ T) {m : ℕ} {Λ : ℝ} {b : ℝ → E → E} (hb : DB T m Λ b) :
    HasFTaylorSeriesUpTo ((m + 1 : ℕ) : ℕ∞) (nem T b) (tay T b) where
  zero_eq _ := rfl
  fderiv j hj α := by
    have hj' : j < m + 1 := by exact_mod_cast hj
    refine Good.hasFDerivAt_Vop hT (hb.good hT (by omega)) (hb.good hT (by omega)) (fun s y => ?_) α
    have hf := hb.smooth _ (clampT_mem hT s)
    have hd : Differentiable ℝ (iteratedFDeriv ℝ j (bt T b s)) :=
      hf.differentiable_iteratedFDeriv (by exact_mod_cast hj')
    have := (hd y).hasFDerivAt
    rw [show fderiv ℝ (iteratedFDeriv ℝ j (bt T b s)) y =
      (iteratedFDeriv ℝ (j + 1) (bt T b s) y).curryLeft from rfl] at this
    exact this
  cont j hj := by
    have hj' : j ≤ m + 1 := by exact_mod_cast hj
    exact (hb.good hT hj').continuous_Vop hT

theorem contDiff_nem {T : ℝ} (hT : 0 ≤ T) {m : ℕ} {Λ : ℝ} {b : ℝ → E → E} (hb : DB T m Λ b) :
    ContDiff ℝ ((m + 1 : ℕ) : WithTop ℕ∞) (nem T b) := by
  have := (hasFTaylor hT hb).contDiff
  exact_mod_cast this

theorem nem_apply {T : ℝ} (hT : 0 ≤ T) {m : ℕ} {Λ : ℝ} {b : ℝ → E → E} (hb : DB T m Λ b)
    (α : ℝ →ᵇ E) (t : ℝ) :
    nem T b α t = ∫ s in (0 : ℝ)..clampT T t, b (clampT T s) (α s) := by
  have hB : HasB (fun s => iteratedFDeriv ℝ 0 (bt T b s) (α s)) := (hb.good hT (Nat.zero_le _)).hasB α
  unfold nem tay
  rw [ContinuousMultilinearMap.curry0, Vop_apply hB]
  simp [iteratedFDeriv_zero_apply, bt]

theorem hasFDerivAt_nem {T : ℝ} (hT : 0 ≤ T) {m : ℕ} {Λ : ℝ} {b : ℝ → E → E}
    (hb : DB T m Λ b) (α : ℝ →ᵇ E) :
    HasFDerivAt (nem T b) (continuousMultilinearCurryFin1 ℝ (ℝ →ᵇ E) (ℝ →ᵇ E) (tay T b α 1)) α :=
  (hasFTaylor hT hb).hasFDerivAt (by simp) α

theorem dnem_apply {T : ℝ} (hT : 0 ≤ T) {m : ℕ} {Λ : ℝ} {b : ℝ → E → E}
    (hb : DB T m Λ b) (α γ : ℝ →ᵇ E) (t : ℝ) :
    continuousMultilinearCurryFin1 ℝ (ℝ →ᵇ E) (ℝ →ᵇ E) (tay T b α 1) γ t =
      ∫ s in (0 : ℝ)..clampT T t, fderiv ℝ (b (clampT T s)) (α s) (γ s) := by
  have hB : HasB (fun s => iteratedFDeriv ℝ 1 (bt T b s) (α s)) :=
    (hb.good hT (by omega)).hasB α
  rw [continuousMultilinearCurryFin1_apply]
  unfold tay
  rw [Vop_apply hB]
  simp [iteratedFDeriv_one_apply, bt]

end HRS.MS.FlowB
