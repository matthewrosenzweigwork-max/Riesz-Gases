import HRS.MS.CovMeasAux8

/-!
# S10.1 (worker S101B), part 9: `F_{u⊗v} = ∇g_u · ∇g_v` and the explicit values of `D_τ` on the basic vectors

`s101_Fm_Rk_eq_inner`: if `⟨Γ(x),u⟩ = f(x)` and `⟨Γ(x),v⟩ = f'(x)` for all `x` then `F_{u⊗v} = ∇f·∇f'` (for `Γ` differentiable).
`s101_D_W`: for `W_{s,α} = (0, 1_{[0,s]} e_α, e_α)` the form `D_τ(W_{s,α}, W_{s',β})` is `2ν z^τ(∇Wf·∇Wf')` with
`Wf τ s α = U^{τ,s}φ_α` if `τ < s` and `U^{τ,τ}φ_α` otherwise.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.CovMeas

open HRS HRS.Whole HRS.MS.Go HRS.MS.FixEq

variable {d : ℕ}

section E2

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

lemma s101_fderiv_inner {Γ : Euc d → H} (hΓ : Differentiable ℝ Γ) (u : H) (x h : Euc d) :
    fderiv ℝ (fun y => inner ℝ (Γ y) u) x h = inner ℝ (fderiv ℝ Γ x h) u := by
  have e : (fun y => inner ℝ (Γ y) u) = fun y => (innerSL ℝ u) (Γ y) := by
    funext y; rw [real_inner_comm]; rfl
  have h1 : HasFDerivAt (fun y => (innerSL ℝ u) (Γ y)) ((innerSL ℝ u).comp (fderiv ℝ Γ x)) x :=
    (innerSL ℝ u).hasFDerivAt.comp x (hΓ x).hasFDerivAt
  rw [e, h1.fderiv]
  simp [real_inner_comm]

theorem s101_Fm_Rk_eq_inner {Γ : Euc d → H} (hΓ : Differentiable ℝ Γ) {u v : H} {f f' : Euc d → ℝ}
    (hu : ∀ x, inner ℝ (Γ x) u = f x) (hv : ∀ x, inner ℝ (Γ x) v = f' x) :
    s101Fm Γ (s101Rk u v) = fun x => inner ℝ (gradient f x) (gradient f' x) := by
  have hfu : f = fun y => inner ℝ (Γ y) u := (funext hu).symm
  have hfv : f' = fun y => inner ℝ (Γ y) v := (funext hv).symm
  funext x
  simp only [s101Fm, s101Rk_apply, s101Gk]
  rw [PiLp.inner_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [movtr_gradient_apply, movtr_gradient_apply, hfu, hfv, s101_fderiv_inner hΓ, s101_fderiv_inner hΓ,
    real_inner_comm u, real_inner_comm v]
  simp [mul_comm]

end E2

/-- The basic vectors `W_{s,α} = (0, 1_{[0,s]} e_α, e_α)`. -/
def s101W (m T s : ℝ) (α : MultiIndex d) : KSpace d m T :=
  KSpace.mk 0 (s101Ind m T s (s101e m α)) (s101e m α)

/-- `g^τ_{W_{s,α}}`. -/
def s101Wf (C : WholeCoeff d) (m τ s : ℝ) (α : MultiIndex d) : Euc d → ℝ :=
  if τ < s then propagatorW C τ s (oscTestFun m α) else propagatorW C τ τ (oscTestFun m α)

lemma s101_Wf_contDiff {C : WholeCoeff d} {m T : ℝ} {r : ℕ} {c : MultiIndex d → ℝ}
    (hD : S101Data C m T r c) {τ : ℝ} (hτ : τ ∈ Icc (0 : ℝ) T) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) T)
    (α : MultiIndex d) : ContDiff ℝ ((r + 1 : ℕ) : WithTop ℕ∞) (s101Wf C m τ s α) := by
  unfold s101Wf
  split_ifs with h
  · exact hD.smoothU α τ hτ s ⟨h.le, hs.2⟩
  · exact hD.smoothU α τ hτ τ ⟨le_rfl, hτ.2⟩

lemma s101g_W_fun {C : WholeCoeff d} {m T : ℝ} {r : ℕ} {c : MultiIndex d → ℝ}
    (hD : S101Data C m T r c) {τ : ℝ} (hτ : τ ∈ Icc (0 : ℝ) T) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) T)
    (α : MultiIndex d) : ∀ x, inner ℝ (s101Gamma C m T τ x) (s101W m T s α) = s101Wf C m τ s α x := by
  intro x
  have := s101g_W hD hτ hs α x
  unfold s101g at this
  unfold s101W
  rw [this]
  unfold s101Wf
  by_cases h : τ < s <;> simp [h]

theorem s101_D_W (hd : 1 ≤ d) {C : WholeCoeff d} {m T : ℝ} {r : ℕ} {Pw : ℝ}
    (hP : (d : ℝ) < 2 * Pw) (horb : R2OrbitSummable C m T r)
    {z : ℝ → (Euc d → ℝ) → ℝ} (hz : S101Lin r Pw T z) {τ : ℝ} (hτ : τ ∈ Icc (0 : ℝ) T)
    {s s' : ℝ} (hs : s ∈ Icc (0 : ℝ) T) (hs' : s' ∈ Icc (0 : ℝ) T) (α β : MultiIndex d) :
    s101D C m T z τ (s101W m T s α) (s101W m T s' β) =
      2 * C.ν * z τ (fun x => inner ℝ (gradient (s101Wf C m τ s α) x) (gradient (s101Wf C m τ s' β) x)) := by
  obtain ⟨K0, -, hK⟩ := s101_D_data hd hP horb
  obtain ⟨c, hD⟩ := s101_data_of_horb hd horb
  obtain ⟨B, hB0, hB⟩ := s101_gamma_smooth hd hD
  obtain ⟨hΓ, -⟩ := hB τ hτ
  have hΓd : Differentiable ℝ (fun x => s101Gamma C m T τ x) :=
    hΓ.differentiable (by exact_mod_cast Nat.succ_ne_zero r)
  rw [(hK z hz τ hτ).1, s101_Fm_Rk_eq_inner hΓd (s101g_W_fun hD hτ hs α) (s101g_W_fun hD hτ hs' β)]

end HRS.MS.CovMeas
