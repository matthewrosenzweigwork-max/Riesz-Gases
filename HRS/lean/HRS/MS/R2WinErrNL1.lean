import HRS.MS.R2WinErrAux18
import HRS.MS.Mov63Aux3
import HRS.MS.MovLinAux7
import HRS.MS.SuppU4
import HRS.MS.WsStatAux5

/-!
# S10.4, nonlinear branch, part 1: joint measurability of the density along a resulting solution (`hjmNL`)

`s104n_hjm`: for `ρ` with `IsResultingSolution` the map `(t,x) ↦ ρ (max 0 (min t T')) x` is Borel measurable on `ℝ × Euc d`.  Proof: with
`V_t = (ρ^t - ρ_β)/√ρ_β` one has `ρ^t = ρ_β + √ρ_β V_t`; `V_t` is continuous with `V_t ∈ Σ^m`, the map `t ↦ ofFun V_t` is continuous into `Σ^m`
(`IsResultingSolution.cont`) and the sup norm is bounded by the `Σ^m` norm (`mn_force_bound`), so `(t,x) ↦ V_{clamp t}(x)` is jointly continuous.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R2WinErr

open HRS HRS.Whole HRS.MS.Mov63 HRS.MS.MovLin HRS.MS.MovOsc

variable {d : ℕ}

theorem s104n_hjm (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {a β : ℝ} (ha : 0 < a) (hβ : 0 < β)
    {ρβ : Euc d → ℝ} (hρβ : IsThermalEquilibrium d s a β ρβ) {εstar ε c₁ C₁ : ℝ} {ψ : Euc d → ℝ}
    {ρ : ℝ → Euc d → ℝ} (hres : IsResultingSolution d s a β ρβ εstar ε ψ c₁ C₁ ρ) (T' : ℝ) (hT' : 0 ≤ T') :
    Measurable fun p : ℝ × Euc d => ρ (max 0 (min p.1 T')) p.2 := by
  obtain ⟨m, hm⟩ : ∃ m : ℕ, m = 102 * d + 1020 := ⟨_, rfl⟩
  have hmR : (m : ℝ) = 102 * (d : ℝ) + 1020 := by rw [hm]; push_cast; ring
  have hm0 : (d : ℝ) / 2 + ((0 : ℕ) : ℝ) + 2 < m := by
    rw [hmR]; push_cast; have : (0 : ℝ) ≤ d := Nat.cast_nonneg d; linarith
  obtain ⟨C, hC0, hC⟩ := mn_force_bound hd hs0 hsd β a hβ ha ρβ hρβ 0 m hm0
  have hpos : ∀ x, 0 < ρβ x := fun x => HRS.Whole.u4_thermal_pos hρβ x
  have hρβc : Continuous ρβ := by
    have hρeq := HRS.MS.Mov0.mv0_rho_eq hd hs0 hsd ha hβ hρβ
    obtain ⟨-, ψ', hψ'⟩ := HRS.MS.S21.s21_schwartz_thermal hd hs0 hsd ha hβ
    rw [hρeq, ← hψ']; exact ψ'.continuous
  obtain ⟨V, hVdef⟩ : ∃ V : ℝ → Euc d → ℝ, ∀ t x, V t x = (ρ t x - ρβ x) / Real.sqrt (ρβ x) :=
    ⟨fun t x => (ρ t x - ρβ x) / Real.sqrt (ρβ x), fun _ _ => rfl⟩
  have hVfun : ∀ t, V t = fun x => (ρ t x - ρβ x) / Real.sqrt (ρβ x) := fun t => funext (hVdef t)
  have hVc : ∀ t, 0 ≤ t → Continuous (V t) := fun t ht => by
    rw [hVfun t]
    exact ((hres.regular t ht).sub hρβc).div hρβc.sqrt (fun x => (Real.sqrt_pos.2 (hpos x)).ne')
  have hVm : ∀ t, 0 ≤ t → MemOsc (m : ℝ) (V t) := fun t ht => by
    rw [hVfun t, hmR]; exact (hres.weighted t ht).1
  have hu : ContinuousOn (fun t => OscSpace.ofFun (d := d) (m : ℝ) (V t)) (Ici 0) := by
    have : (fun t => OscSpace.ofFun (d := d) (m : ℝ) (V t)) = fun t => OscSpace.ofFun (d := d) (102 * (d : ℝ) + 1020)
        (fun x => (ρ t x - ρβ x) / Real.sqrt (ρβ x)) := by
      funext t; rw [hmR, hVfun t]
    rw [this]; exact hres.cont
  have hκ : Continuous fun t : ℝ => max 0 (min t T') := by fun_prop
  have hκ0 : ∀ t : ℝ, max 0 (min t T') ∈ Ici (0 : ℝ) := fun t => mem_Ici.2 (le_max_left _ _)
  have huκ : Continuous fun t : ℝ => OscSpace.ofFun (d := d) (m : ℝ) (V (max 0 (min t T'))) :=
    hu.comp_continuous hκ hκ0
  have hbd : ∀ t t' : ℝ, 0 ≤ t → 0 ≤ t' → ∀ x, ‖V t' x - V t x‖ ≤
      C * dist (OscSpace.ofFun (d := d) (m : ℝ) (V t')) (OscSpace.ofFun (d := d) (m : ℝ) (V t)) := by
    intro t t' ht ht' x
    have hmem := mov2d_memOsc_sub (hVm t' ht') (hVm t ht)
    obtain ⟨-, h2, -⟩ := hC (fun z => V t' z - V t z) ((hVc t' ht').sub (hVc t ht)) hmem
    have := h2 0 (by norm_num) x
    rw [norm_iteratedFDeriv_zero] at this
    rw [dist_eq_norm, ← mov2d_ofFun_sub (hVm t' ht') (hVm t ht), OscSpace.norm_ofFun _ hmem]
    exact this
  -- bounded continuous representatives
  have hbdd : ∀ t, 0 ≤ t → ∀ x, ‖V t x‖ ≤ C * oscNorm (m : ℝ) (V t) := fun t ht x => by
    obtain ⟨-, h2, -⟩ := hC (V t) (hVc t ht) (hVm t ht)
    have := h2 0 (by norm_num) x
    rwa [norm_iteratedFDeriv_zero] at this
  let Φ : ℝ → (BoundedContinuousFunction (Euc d) ℝ) := fun t => BoundedContinuousFunction.ofNormedAddCommGroup (V (max 0 (min t T')))
    (hVc _ (hκ0 t)) _ (hbdd _ (hκ0 t))
  have hΦc : Continuous Φ := by
    rw [Metric.continuous_iff]
    intro t ε' hε'
    obtain ⟨δ, hδ, h⟩ := Metric.continuous_iff.1 huκ t (ε' / (C + 1)) (by positivity)
    refine ⟨δ, hδ, fun t' ht' => ?_⟩
    have hd' := h t' ht'
    have hle : dist (Φ t') (Φ t) ≤ C * dist (OscSpace.ofFun (d := d) (m : ℝ) (V (max 0 (min t' T'))))
        (OscSpace.ofFun (d := d) (m : ℝ) (V (max 0 (min t T')))) := by
      rw [BoundedContinuousFunction.dist_le (mul_nonneg hC0 dist_nonneg)]
      intro x
      rw [Real.dist_eq, ← Real.norm_eq_abs]
      exact hbd _ _ (hκ0 t) (hκ0 t') x
    calc dist (Φ t') (Φ t) ≤ _ := hle
      _ ≤ C * (ε' / (C + 1)) := mul_le_mul_of_nonneg_left hd'.le hC0
      _ < ε' := by
        rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
        nlinarith
  have hjc : Continuous fun p : ℝ × Euc d => V (max 0 (min p.1 T')) p.2 :=
    (continuous_eval (F := BoundedContinuousFunction (Euc d) ℝ) (X := Euc d)).comp ((hΦc.comp continuous_fst).prodMk continuous_snd)
  have heq : (fun p : ℝ × Euc d => ρ (max 0 (min p.1 T')) p.2) =
      fun p => ρβ p.2 + Real.sqrt (ρβ p.2) * V (max 0 (min p.1 T')) p.2 := by
    funext p
    rw [hVdef]
    have := (Real.sqrt_pos.2 (hpos p.2)).ne'
    field_simp
    ring
  rw [heq]
  exact ((hρβc.comp continuous_snd).add ((hρβc.sqrt.comp continuous_snd).mul hjc)).measurable

/-- `hcls` for the whole class (stationary and nonlinear), unconditionally. -/
theorem s104n_hcls (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {a β : ℝ} (ha : 0 < a) (hβ : 0 < β)
    (εstar c₁ C₁ : ℝ) : S104ClassInput d s a β εstar c₁ C₁ :=
  s104_hcls hd hs0 hsd ha hβ εstar c₁ C₁ fun _ hρβ _ _ _ hres T' hT' =>
    s104n_hjm hd hs0 hsd ha hβ hρβ hres T' hT'

end HRS.MS.R2WinErr
