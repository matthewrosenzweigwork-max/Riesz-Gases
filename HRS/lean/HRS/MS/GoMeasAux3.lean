import HRS.MS.GoMeasAux2
import HRS.MS.GoMax

/-!
# S55M, part 3: continuity in the terminal time of the adjoint orbit; `S55fMeas` for the `Rd` regime

Helper names carry the prefix `s55m_`; namespace `HRS.MS.Go`.

Route (a): the family `t ↦ f_t := U(·,t)ψ_t`, `ψ_t = 𝓛_t φ_α`, of classical adjoint solutions is bounded in `C_b^{k+1}`
uniformly in `t` (`UlAdjointInput` and `s55f_gen_ul`), and `∂_r f_t = -𝓛_r f_t` has the uniform linear growth bound of
`rg_gen_core`.  If `t_n → t`, a subsequence of the (time-clipped) `f_{t_n}` converges pointwise (`s55m_ex`, diagonal
argument) to a function `g` with `g(r) ∈ C^4`, `D^j f_{t_n}(r) → D^j g(r)` (`s55m_dl`); the integral identity
`f_{t_n}(r_1) - f_{t_n}(r_2) = ∫ 𝓛_τ f_{t_n}(τ) dτ` passes to the limit (dominated convergence, `s55m_gen_tendsto`), so
`g` is a classical adjoint solution on `[0,t]` with terminal datum `ψ_t` and `g = f_t` by uniqueness
(`s55f_propagatorW_eq`, which needs the `Rd` disjunct of `S.regime N`).  Hence
`t ↦ ∂_a f_t(r)(x)` is continuous on `(r,T]`, in particular strongly measurable.

Statement actually proved: `s55fMeasRd_holds`: `S55fMeasRd b S` (the slice of `S55fMeas` for the `N` whose regime is the
`Rd` disjunct) for every `S : WholeSetup b`, `b.Valid`; `s55fMeas_of_rd`: `S55fMeas b S` whenever the `Rd` disjunct holds for
every `N`; consumers `s55m_features_rd`, `s55m_maximal_rd` (`s55f_features_of_meas`, `s55f_maximal_of_meas` for such `S`).
Not covered: an `N` whose regime is only the `Lp` disjunct (uniqueness of classical adjoint solutions is not available there).
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators ContDiff

set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000

namespace HRS.MS.Go
open HRS HRS.Whole HRS.Whole.AppendixA HRS.MH.DualityRd HRS.MP.RdGen

variable {d : ℕ}

/-! ### The family `t ↦ U(·,t)ψ_t` -/

theorem s55m_osc_bound (b : WholeBounds d) (hb : b.Valid) (α : MultiIndex d) :
    ∃ Bφ : ℝ, 0 ≤ Bφ ∧ ContDiff ℝ 4 (oscTestFun b.m α) ∧
      ∀ n ≤ 4, ∀ x, ‖iteratedFDeriv ℝ n (oscTestFun b.m α) x‖ ≤ Bφ := by
  have hd1 : 1 ≤ d := by have := hb.hd; omega
  have hceil := s55f_ceil_half_le d
  have hJ : b.J = 4 * b.k + 4 * d + 40 := rfl
  have hk9 : (9 : ℝ) < b.k := by
    have := hb.hk; have : (2 : ℝ) ≤ d := by exact_mod_cast hb.hd
    linarith
  have hk9' : 9 < b.k := by exact_mod_cast hk9
  have hc2 : ⌈(1 + (((b.k + 1 : ℕ) : ℝ))) / 2⌉₊ ≤ b.k + 1 := by
    rw [Nat.ceil_le]; push_cast
    have : (0 : ℝ) ≤ b.k := Nat.cast_nonneg _
    linarith
  obtain ⟨C0, hC0, hosc⟩ := s55_osc_bounds hb.hθ b.m 0 (b.k + 1) 1 (by norm_num) b.J (by omega) (by omega)
  obtain ⟨hsm, -, hdec⟩ := hosc α
  have hφ : ContDiff ℝ ((b.k + 1 : ℕ) : WithTop ℕ∞) (oscTestFun b.m α) := s55_cd_of_inf _ hsm
  have hΛ0 : 0 ≤ C0 * oscEigenvalue d α ^ (((b.J : ℝ) - b.m) / 2) :=
    mul_nonneg hC0 (Real.rpow_nonneg (oscEigenvalue_pos α).le _)
  have hnorm := s55f_decay_to_norm hφ hdec
  rw [max_eq_left hΛ0] at hnorm
  refine ⟨(d : ℝ) ^ 4 * (C0 * oscEigenvalue d α ^ (((b.J : ℝ) - b.m) / 2)) + 0, by positivity,
    hφ.of_le (by exact_mod_cast (by omega : 4 ≤ b.k + 1)), fun n hn x => ?_⟩
  have h1 := (hnorm n (by omega) x).1
  have hd1' : (1 : ℝ) ≤ d := by exact_mod_cast hd1
  have h2 : (d : ℝ) ^ n ≤ (d : ℝ) ^ 4 := pow_le_pow_right₀ hd1' hn
  calc _ ≤ (d : ℝ) ^ n * (C0 * oscEigenvalue d α ^ (((b.J : ℝ) - b.m) / 2)) := h1
    _ ≤ (d : ℝ) ^ 4 * (C0 * oscEigenvalue d α ^ (((b.J : ℝ) - b.m) / 2)) :=
        mul_le_mul_of_nonneg_right h2 hΛ0
    _ = _ := by ring

theorem s55m_family (b : WholeBounds d) (hb : b.Valid) (S : WholeSetup b) (N : ℕ) (α : MultiIndex d) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t ∈ Set.Icc (0 : ℝ) b.T,
      IsClassicalAdjointW (S.coeff N) t (generatorW (S.coeff N) t (oscTestFun b.m α))
        (fun r => propagatorW (S.coeff N) r t (generatorW (S.coeff N) t (oscTestFun b.m α))) ∧
      ∀ r ∈ Set.Icc (0 : ℝ) t,
        ContDiff ℝ ((b.k + 1 : ℕ) : WithTop ℕ∞) (propagatorW (S.coeff N) r t (generatorW (S.coeff N) t (oscTestFun b.m α))) ∧
        ∀ j ≤ b.k + 1, ∀ x, ‖iteratedFDeriv ℝ j
          (propagatorW (S.coeff N) r t (generatorW (S.coeff N) t (oscTestFun b.m α))) x‖ ≤ B := by
  obtain ⟨Cg, hCg0, hCg⟩ := s55f_gen_ul b hb
  have hΛ0 : 0 ≤ Cg * oscEigenvalue d α ^ (((b.J : ℝ) - b.m) / 2) :=
    mul_nonneg hCg0 (Real.rpow_nonneg (oscEigenvalue_pos α).le _)
  refine ⟨|b.K| * (Cg * oscEigenvalue d α ^ (((b.J : ℝ) - b.m) / 2)), by positivity, fun t ht => ?_⟩
  obtain ⟨hψ, hul⟩ := hCg S N t ht α
  have hulfin : ulNormE (b.k + 1 + 1 + ⌈(d : ℝ) / 2⌉₊) b.θ
      (generatorW (S.coeff N) t (oscTestFun b.m α)) < ⊤ :=
    lt_of_le_of_lt hul ENNReal.ofReal_lt_top
  have hulr : (ulNormE (b.k + 1 + 1 + ⌈(d : ℝ) / 2⌉₊) b.θ
      (generatorW (S.coeff N) t (oscTestFun b.m α))).toReal ≤
      Cg * oscEigenvalue d α ^ (((b.J : ℝ) - b.m) / 2) := by
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hul
    rwa [ENNReal.toReal_ofReal hΛ0] at this
  obtain ⟨hex, -, -⟩ := S.adjoint N 0 t le_rfl ht.1 ht.2 _ hψ hulfin
  refine ⟨HRS.MS.Fcau.propagatorW_isClassical hex, fun r hr => ?_⟩
  obtain ⟨-, hmem, hcb⟩ := S.adjoint N r t hr.1 hr.2 ht.2 _ hψ hulfin
  refine ⟨hmem.1, fun j hj x => ?_⟩
  have hbdd := hmem.2 j hj
  have h1 : ‖iteratedFDeriv ℝ j (propagatorW (S.coeff N) r t
      (generatorW (S.coeff N) t (oscTestFun b.m α))) x‖ ≤
      ⨆ z, ‖iteratedFDeriv ℝ j (propagatorW (S.coeff N) r t
      (generatorW (S.coeff N) t (oscTestFun b.m α))) z‖ := le_ciSup hbdd x
  have hsup : ‖iteratedFDeriv ℝ j (propagatorW (S.coeff N) r t
      (generatorW (S.coeff N) t (oscTestFun b.m α))) x‖ ≤
      cbNorm (b.k + 1) (propagatorW (S.coeff N) r t (generatorW (S.coeff N) t (oscTestFun b.m α))) := by
    unfold cbNorm
    refine h1.trans ?_
    exact Finset.single_le_sum (f := fun i => ⨆ z, ‖iteratedFDeriv ℝ i (propagatorW (S.coeff N) r t
      (generatorW (S.coeff N) t (oscTestFun b.m α))) z‖)
      (fun i _ => Real.iSup_nonneg fun _ => norm_nonneg _) (Finset.mem_range.2 (by omega))
  refine hsup.trans (hcb.trans ?_)
  calc b.K * (ulNormE (b.k + 1 + 1 + ⌈(d : ℝ) / 2⌉₊) b.θ
        (generatorW (S.coeff N) t (oscTestFun b.m α))).toReal
      ≤ |b.K| * (ulNormE (b.k + 1 + 1 + ⌈(d : ℝ) / 2⌉₊) b.θ
        (generatorW (S.coeff N) t (oscTestFun b.m α))).toReal :=
          mul_le_mul_of_nonneg_right (le_abs_self _) ENNReal.toReal_nonneg
    _ ≤ |b.K| * (Cg * oscEigenvalue d α ^ (((b.J : ℝ) - b.m) / 2)) :=
          mul_le_mul_of_nonneg_left hulr (abs_nonneg _)

/-! ### Calculus for classical adjoint solutions -/

theorem s55m_cont0 {C : WholeCoeff d} {t : ℝ} {φ : Euc d → ℝ} {f : ℝ → Euc d → ℝ}
    (hf : IsClassicalAdjointW C t φ f) (x : Euc d) : ContinuousOn (fun r => f r x) (Set.Icc 0 t) := by
  have h := hf.cont_c2 0 (Nat.zero_le _)
  have e : (fun r : Set.Icc (0 : ℝ) t => f r x) = fun r : Set.Icc (0 : ℝ) t =>
      continuousMultilinearCurryFin0 ℝ (Euc d) ℝ (iteratedFDeriv ℝ 0 (f r) x) := by
    funext r; simp [iteratedFDeriv_zero_eq_comp]
  rw [continuousOn_iff_continuous_domRestrict]
  show Continuous fun r : Set.Icc (0 : ℝ) t => f r x
  rw [e]
  have hp : Continuous fun r : Set.Icc (0 : ℝ) t => ((r, x) : Set.Icc (0 : ℝ) t × Euc d) :=
    continuous_id.prodMk continuous_const
  exact (continuousMultilinearCurryFin0 ℝ (Euc d) ℝ).continuous.comp (h.comp hp)

theorem s55m_contL {C : WholeCoeff d} {t : ℝ} {φ : Euc d → ℝ} {f : ℝ → Euc d → ℝ}
    (hf : IsClassicalAdjointW C t φ f) (x : Euc d) :
    ContinuousOn (fun r => generatorW C r (f r) x) (Set.Icc 0 t) := by
  rw [continuousOn_iff_continuous_domRestrict]
  have hp : Continuous fun r : Set.Icc (0 : ℝ) t => ((r, x) : Set.Icc (0 : ℝ) t × Euc d) :=
    continuous_id.prodMk continuous_const
  refine Continuous.congr (hf.cont_time_deriv.comp hp) (fun r => ?_)
  rfl

theorem s55m_ftc {C : WholeCoeff d} {t : ℝ} {φ : Euc d → ℝ} {f : ℝ → Euc d → ℝ}
    (hf : IsClassicalAdjointW C t φ f) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hbt : b ≤ t) (x : Euc d) :
    f a x - f b x = ∫ τ in a..b, generatorW C τ (f τ) x := by
  have hsub : Set.Icc a b ⊆ Set.Icc 0 t := Set.Icc_subset_Icc ha hbt
  have hc := (s55m_cont0 hf x).mono hsub
  have hgi : IntervalIntegrable (fun r => -generatorW C r (f r) x) MeasureTheory.volume a b :=
    ((s55m_contL hf x).mono hsub).neg.intervalIntegrable_of_Icc hab
  have := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hab hc
    (fun y hy => (hf.time_deriv x y ⟨ha.trans_lt hy.1, hy.2.trans_le hbt⟩).hasDerivWithinAt) hgi
  rw [intervalIntegral.integral_neg] at this
  linarith

theorem s55m_lip_r {C : WholeCoeff d} {t : ℝ} {φ : Euc d → ℝ} {f : ℝ → Euc d → ℝ}
    (hf : IsClassicalAdjointW C t φ f) {BL : ℝ}
    (hBL : ∀ τ ∈ Set.Icc (0 : ℝ) t, ∀ x, |generatorW C τ (f τ) x| ≤ BL * (1 + ‖x‖))
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hbt : b ≤ t) (x : Euc d) :
    |f a x - f b x| ≤ BL * (1 + ‖x‖) * (b - a) := by
  rw [s55m_ftc hf ha hab hbt x]
  have := intervalIntegral.norm_integral_le_of_norm_le_const (a := a) (b := b)
    (f := fun τ => generatorW C τ (f τ) x) (C := BL * (1 + ‖x‖)) (fun τ hτ => by
      rw [Set.uIoc_of_le hab] at hτ
      simpa using hBL τ ⟨ha.trans hτ.1.le, hτ.2.trans hbt⟩ x)
  rwa [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.2 hab)] at this

theorem s55m_lip_x {u : Euc d → ℝ} {B : ℝ} (hu : Differentiable ℝ u) (hb : ∀ y, ‖fderiv ℝ u y‖ ≤ B)
    (x x' : Euc d) : |u x - u x'| ≤ B * ‖x - x'‖ := by
  have := Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ) (f := u) (C := B) (s := Set.univ)
    (x := x') (y := x) (fun z _ => hu z) (fun z _ => hb z) convex_univ (Set.mem_univ _) (Set.mem_univ _)
  simpa [Real.norm_eq_abs] using this

/-! ### The limit of a converging family of slices -/

theorem s55m_limit_G {B : ℝ} (hB : 0 ≤ B) {F : ℕ → ℝ → Euc d → ℝ} {g : ℝ → Euc d → ℝ}
    (hF : ∀ n r', ContDiff ℝ 5 (F n r') ∧ ∀ j ≤ 5, ∀ x, ‖iteratedFDeriv ℝ j (F n r') x‖ ≤ B)
    (hFg : ∀ r' x, Tendsto (fun n => F n r' x) atTop (𝓝 (g r' x))) (r' : ℝ) :
    ContDiff ℝ 4 (g r') ∧ (∀ j ≤ 4, ∀ x, ‖iteratedFDeriv ℝ j (g r') x‖ ≤ B) ∧
      ∀ j ≤ 4, ∀ x, Tendsto (fun n => iteratedFDeriv ℝ j (F n r') x) atTop
        (𝓝 (iteratedFDeriv ℝ j (g r') x)) := by
  obtain ⟨h1, h2⟩ := s55m_dl 4 hB (F := ℝ) (h := fun n => F n r') (h₀ := g r')
    (fun n => by simpa using (hF n r').1) (fun n j hj x => (hF n r').2 j (by omega) x) (fun x => hFg r' x)
  exact ⟨by simpa using h1, fun j hj x => s55m_dl_bound (fun n => (hF n r').2 j (by omega) x) (h2 j hj x), h2⟩

theorem s55m_conv_tau {B L : ℝ} (hB : 0 ≤ B) {g : ℝ → Euc d → ℝ}
    (hG : ∀ r', ContDiff ℝ 4 (g r') ∧ ∀ j ≤ 4, ∀ x, ‖iteratedFDeriv ℝ j (g r') x‖ ≤ B)
    (hgr : ∀ r r' x, |g r x - g r' x| ≤ L * (1 + ‖x‖) * |r - r'|)
    {τs : ℕ → ℝ} {τ : ℝ} (hτ : Tendsto τs atTop (𝓝 τ)) :
    ∀ j ≤ 2, ∀ y, Tendsto (fun m => iteratedFDeriv ℝ j (g (τs m)) y) atTop
      (𝓝 (iteratedFDeriv ℝ j (g τ) y)) := by
  have hpt : ∀ x, Tendsto (fun m => g (τs m) x) atTop (𝓝 (g τ x)) := by
    intro x
    have h0 : Tendsto (fun m => L * (1 + ‖x‖) * |τs m - τ|) atTop (𝓝 0) := by
      have := ((hτ.sub_const τ).abs).const_mul (L * (1 + ‖x‖))
      simpa using this
    refine tendsto_iff_dist_tendsto_zero.2 (squeeze_zero (fun _ => dist_nonneg) (fun m => ?_) h0)
    rw [Real.dist_eq]; exact hgr _ _ x
  exact (s55m_dl 2 hB (F := ℝ) (h := fun m => g (τs m)) (h₀ := g τ)
    (fun m => by simpa using ((hG _).1.of_le (by norm_num : ((3 : ℕ) : WithTop ℕ∞) ≤ 4)))
    (fun m j hj x => (hG _).2 j (by omega) x) hpt).2

theorem s55m_cont_jet {B L : ℝ} (hB : 0 ≤ B) {g : ℝ → Euc d → ℝ}
    (hG : ∀ r', ContDiff ℝ 4 (g r') ∧ ∀ j ≤ 4, ∀ x, ‖iteratedFDeriv ℝ j (g r') x‖ ≤ B)
    (hgr : ∀ r r' x, |g r x - g r' x| ≤ L * (1 + ‖x‖) * |r - r'|) {j : ℕ} (hj : j ≤ 2) :
    Continuous fun p : ℝ × Euc d => iteratedFDeriv ℝ j (g p.1) p.2 := by
  refine continuous_iff_seqContinuous.2 fun pm p₀ hp => ?_
  have hτ : Tendsto (fun m => (pm m).1) atTop (𝓝 p₀.1) := (continuous_fst.tendsto _).comp hp
  have hx : Tendsto (fun m => (pm m).2) atTop (𝓝 p₀.2) := (continuous_snd.tendsto _).comp hp
  have h1 := s55m_conv_tau hB hG hgr hτ j hj p₀.2
  have h2 : ∀ m, ‖iteratedFDeriv ℝ j (g (pm m).1) (pm m).2 - iteratedFDeriv ℝ j (g (pm m).1) p₀.2‖ ≤
      B * ‖(pm m).2 - p₀.2‖ := by
    intro m
    have hd : Differentiable ℝ (iteratedFDeriv ℝ j (g (pm m).1)) :=
      ((hG _).1.differentiable_iteratedFDeriv (by exact_mod_cast (by omega : j < 4)))
    have := Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ) (f := iteratedFDeriv ℝ j (g (pm m).1))
      (C := B) (s := Set.univ) (x := p₀.2) (y := (pm m).2) (fun z _ => hd z) (fun z _ => by
        rw [norm_fderiv_iteratedFDeriv]; exact (hG _).2 (j + 1) (by omega) z) convex_univ (Set.mem_univ _)
        (Set.mem_univ _)
    exact this
  have h3 : Tendsto (fun m => B * ‖(pm m).2 - p₀.2‖) atTop (𝓝 0) := by
    have := ((hx.sub_const p₀.2).norm).const_mul B
    simpa using this
  refine tendsto_iff_norm_sub_tendsto_zero.2 ?_
  have h4 : Tendsto (fun m => ‖iteratedFDeriv ℝ j (g (pm m).1) p₀.2 - iteratedFDeriv ℝ j (g p₀.1) p₀.2‖)
      atTop (𝓝 0) := tendsto_iff_norm_sub_tendsto_zero.1 h1
  refine squeeze_zero (fun _ => norm_nonneg _) (fun m => ?_) (by simpa using h3.add h4)
  calc _ = ‖(iteratedFDeriv ℝ j (g (pm m).1) (pm m).2 - iteratedFDeriv ℝ j (g (pm m).1) p₀.2) +
        (iteratedFDeriv ℝ j (g (pm m).1) p₀.2 - iteratedFDeriv ℝ j (g p₀.1) p₀.2)‖ := by
          congr 1; simp
    _ ≤ _ := (norm_add_le _ _).trans (add_le_add (h2 m) le_rfl)

theorem s55m_gen_tendsto_S (b : WholeBounds d) (hb : b.Valid) (S : WholeSetup b) (N : ℕ) {B : ℝ}
    (hB : 0 ≤ B) {τ : ℕ → ℝ} {τ₀ : ℝ} (hτ : ∀ m, τ m ∈ Set.Icc (0 : ℝ) b.T)
    (hτ₀ : τ₀ ∈ Set.Icc (0 : ℝ) b.T) (hτt : Tendsto τ atTop (𝓝 τ₀)) {u : ℕ → Euc d → ℝ}
    {u₀ : Euc d → ℝ}
    (hu : ∀ m, ContDiff ℝ 3 (u m) ∧ ∀ n ≤ 3, ∀ x, ‖iteratedFDeriv ℝ n (u m) x‖ ≤ B)
    (hu₀ : ContDiff ℝ 3 u₀ ∧ ∀ n ≤ 3, ∀ x, ‖iteratedFDeriv ℝ n u₀ x‖ ≤ B)
    (h1 : ∀ y, Tendsto (fun m => iteratedFDeriv ℝ 1 (u m) y) atTop (𝓝 (iteratedFDeriv ℝ 1 u₀ y)))
    (x : Euc d)
    (h2 : Tendsto (fun m => iteratedFDeriv ℝ 2 (u m) x) atTop (𝓝 (iteratedFDeriv ℝ 2 u₀ x))) :
    Tendsto (fun m => generatorW (S.coeff N) (τ m) (u m) x) atTop
      (𝓝 (generatorW (S.coeff N) τ₀ u₀ x)) := by
  have hd1 : 1 ≤ d := by have := hb.hd; omega
  obtain ⟨A, hA0, hdec, hpt⟩ := s55m_rho_data b hb S N
  exact s55m_gen_tendsto hd1 (S.dyn N) hb.hs0 hb.hsd (s55f_matBound _)
    (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) hA0 hB hdec hpt hτ hτ₀ hτt
    hu hu₀ h1 x h2

theorem s55m_cont_gen (b : WholeBounds d) (hb : b.Valid) (S : WholeSetup b) (N : ℕ) {B K L : ℝ}
    (hB : 0 ≤ B) (hK : 0 ≤ K)
    (hgen : ∀ τ ∈ Set.Icc (0 : ℝ) b.T, ∀ u : Euc d → ℝ, ContDiff ℝ 4 u →
      (∀ n ≤ 4, ∀ x, ‖iteratedFDeriv ℝ n u x‖ ≤ B) →
      RgW (fun x => 1 + ‖x‖) 1 (B * K) (generatorW (S.coeff N) τ u))
    {g : ℝ → Euc d → ℝ}
    (hG : ∀ r', ContDiff ℝ 4 (g r') ∧ ∀ j ≤ 4, ∀ x, ‖iteratedFDeriv ℝ j (g r') x‖ ≤ B)
    (hgr : ∀ r r' x, |g r x - g r' x| ≤ L * (1 + ‖x‖) * |r - r'|) :
    Continuous fun p : Set.Icc (0 : ℝ) b.T × Euc d => generatorW (S.coeff N) p.1 (g p.1) p.2 := by
  refine continuous_iff_seqContinuous.2 fun pm p₀ hp => ?_
  have hτ : Tendsto (fun m => ((pm m).1 : ℝ)) atTop (𝓝 (p₀.1 : ℝ)) :=
    ((continuous_subtype_val.comp continuous_fst).tendsto _).comp hp
  have hx : Tendsto (fun m => (pm m).2) atTop (𝓝 p₀.2) := (continuous_snd.tendsto _).comp hp
  have hcv := s55m_conv_tau hB hG hgr hτ
  have h1 : Tendsto (fun m => generatorW (S.coeff N) ((pm m).1 : ℝ) (g (pm m).1) p₀.2) atTop
      (𝓝 (generatorW (S.coeff N) (p₀.1 : ℝ) (g p₀.1) p₀.2)) :=
    s55m_gen_tendsto_S b hb S N hB (fun m => (pm m).1.2) p₀.1.2 hτ
      (u := fun m => g (pm m).1) (u₀ := g p₀.1)
      (fun m => ⟨(hG _).1.of_le (by norm_num), fun n hn x => (hG _).2 n (by omega) x⟩)
      ⟨(hG _).1.of_le (by norm_num), fun n hn x => (hG _).2 n (by omega) x⟩
      (fun y => hcv 1 (by norm_num) y) p₀.2 (hcv 2 le_rfl p₀.2)
  have hδ : Tendsto (fun m => ‖(pm m).2 - p₀.2‖) atTop (𝓝 0) := by
    simpa using (hx.sub_const p₀.2).norm
  have h2 : ∀ m, |generatorW (S.coeff N) ((pm m).1 : ℝ) (g (pm m).1) (pm m).2 -
      generatorW (S.coeff N) ((pm m).1 : ℝ) (g (pm m).1) p₀.2| ≤
      B * K * (1 + ‖p₀.2‖ + ‖(pm m).2 - p₀.2‖) * ‖(pm m).2 - p₀.2‖ := by
    intro m
    have hr := hgen _ (pm m).1.2 (g (pm m).1) (hG _).1 (hG _).2
    set R : ℝ := max ‖(pm m).2‖ ‖p₀.2‖ with hR
    have hRle : 1 + R ≤ 1 + ‖p₀.2‖ + ‖(pm m).2 - p₀.2‖ := by
      have : ‖(pm m).2‖ ≤ ‖p₀.2‖ + ‖(pm m).2 - p₀.2‖ := by
        calc ‖(pm m).2‖ = ‖p₀.2 + ((pm m).2 - p₀.2)‖ := by congr 1; abel
          _ ≤ _ := norm_add_le _ _
      have h0 := norm_nonneg ((pm m).2 - p₀.2)
      rw [hR]
      rcases le_total ‖(pm m).2‖ ‖p₀.2‖ with h | h
      · rw [max_eq_right h]; linarith
      · rw [max_eq_left h]; linarith
    have hdiff : Differentiable ℝ (generatorW (S.coeff N) ((pm m).1 : ℝ) (g (pm m).1)) :=
      hr.1.differentiable (by norm_num)
    have := Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ)
      (f := generatorW (S.coeff N) ((pm m).1 : ℝ) (g (pm m).1)) (C := B * K * (1 + R))
      (s := Metric.closedBall (0 : Euc d) R) (x := p₀.2) (y := (pm m).2) (fun z _ => hdiff z) (fun z hz => by
        have h1' := hr.2 1 le_rfl z
        rw [norm_iteratedFDeriv_one] at h1'
        have hz' : ‖z‖ ≤ R := by simpa using hz
        refine h1'.trans ?_
        have : 0 ≤ B * K := mul_nonneg hB hK
        exact mul_le_mul_of_nonneg_left (by linarith) this) (convex_closedBall _ _)
        (by simp [hR]) (by simp [hR])
    rw [Real.norm_eq_abs] at this
    refine this.trans ?_
    have : 0 ≤ B * K := mul_nonneg hB hK
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hRle this) (norm_nonneg _)
  have h3 : Tendsto (fun m => B * K * (1 + ‖p₀.2‖ + ‖(pm m).2 - p₀.2‖) * ‖(pm m).2 - p₀.2‖) atTop (𝓝 0) := by
    simpa using (((tendsto_const_nhds (x := 1 + ‖p₀.2‖)).add hδ).const_mul (B * K)).mul hδ
  have h4 := tendsto_iff_norm_sub_tendsto_zero.1 h1
  refine tendsto_iff_norm_sub_tendsto_zero.2 ?_
  refine squeeze_zero (fun _ => norm_nonneg _) (fun m => ?_) (by simpa using h3.add h4)
  calc _ ≤ |generatorW (S.coeff N) ((pm m).1 : ℝ) (g (pm m).1) (pm m).2 -
        generatorW (S.coeff N) ((pm m).1 : ℝ) (g (pm m).1) p₀.2| +
      |generatorW (S.coeff N) ((pm m).1 : ℝ) (g (pm m).1) p₀.2 -
        generatorW (S.coeff N) (p₀.1 : ℝ) (g p₀.1) p₀.2| := by
          rw [Function.comp_apply, Real.norm_eq_abs]
          exact abs_sub_le _ _ _
    _ ≤ _ := add_le_add (h2 m) le_rfl

theorem s55m_limit_ftc (b : WholeBounds d) (hb : b.Valid) (S : WholeSetup b) (N : ℕ) {B K t₀ : ℝ}
    (hB : 0 ≤ B) (hK : 0 ≤ K) (ht₀ : t₀ ∈ Set.Icc (0 : ℝ) b.T)
    (hgen : ∀ τ ∈ Set.Icc (0 : ℝ) b.T, ∀ u : Euc d → ℝ, ContDiff ℝ 4 u →
      (∀ n ≤ 4, ∀ x, ‖iteratedFDeriv ℝ n u x‖ ≤ B) →
      RgW (fun x => 1 + ‖x‖) 1 (B * K) (generatorW (S.coeff N) τ u))
    {F : ℕ → ℝ → Euc d → ℝ} {g : ℝ → Euc d → ℝ}
    (hF : ∀ n r', ContDiff ℝ 5 (F n r') ∧ ∀ j ≤ 5, ∀ x, ‖iteratedFDeriv ℝ j (F n r') x‖ ≤ B)
    (hFg : ∀ r' x, Tendsto (fun n => F n r' x) atTop (𝓝 (g r' x)))
    (hG' : ∀ r', ContDiff ℝ 4 (g r') ∧ (∀ j ≤ 4, ∀ x, ‖iteratedFDeriv ℝ j (g r') x‖ ≤ B) ∧
      ∀ j ≤ 4, ∀ x, Tendsto (fun n => iteratedFDeriv ℝ j (F n r') x) atTop
        (𝓝 (iteratedFDeriv ℝ j (g r') x)))
    (hftc : ∀ r₁ r₂ x, 0 ≤ r₁ → r₁ ≤ r₂ → r₂ < t₀ → ∀ᶠ n in atTop,
      F n r₁ x - F n r₂ x = ∫ τ in r₁..r₂, generatorW (S.coeff N) τ (F n τ) x ∧
        ContinuousOn (fun τ => generatorW (S.coeff N) τ (F n τ) x) (Set.Icc r₁ r₂))
    {r₁ r₂ : ℝ} (h1 : 0 ≤ r₁) (h12 : r₁ ≤ r₂) (h2 : r₂ < t₀) (x : Euc d) :
    g r₁ x - g r₂ x = ∫ τ in r₁..r₂, generatorW (S.coeff N) τ (g τ) x := by
  have hmemT : ∀ τ ∈ Set.Ioc r₁ r₂, τ ∈ Set.Icc (0 : ℝ) b.T := fun τ hτ =>
    ⟨h1.trans hτ.1.le, hτ.2.trans (h2.le.trans ht₀.2)⟩
  have hlim : Tendsto (fun n => ∫ τ in r₁..r₂, generatorW (S.coeff N) τ (F n τ) x) atTop
      (𝓝 (∫ τ in r₁..r₂, generatorW (S.coeff N) τ (g τ) x)) := by
    refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      (fun _ => B * K * (1 + ‖x‖)) ?_ ?_ intervalIntegrable_const ?_
    · filter_upwards [hftc r₁ r₂ x h1 h12 h2] with n hn
      rw [Set.uIoc_of_le h12]
      exact (hn.2.mono Set.Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc
    · refine Eventually.of_forall fun n => Eventually.of_forall fun τ hτ => ?_
      rw [Set.uIoc_of_le h12] at hτ
      have hr := hgen τ (hmemT τ hτ) (F n τ) ((hF n τ).1.of_le (by norm_num))
        (fun j hj x => (hF n τ).2 j (by omega) x)
      have := hr.2 0 (by norm_num) x
      rwa [norm_iteratedFDeriv_zero] at this
    · refine Eventually.of_forall fun τ hτ => ?_
      rw [Set.uIoc_of_le h12] at hτ
      refine s55m_gen_tendsto_S b hb S N hB (τ := fun _ => τ) (fun _ => hmemT τ hτ) (hmemT τ hτ)
        tendsto_const_nhds (u := fun n => F n τ) (u₀ := g τ)
        (fun n => ⟨(hF n τ).1.of_le (by norm_num), fun j hj x => (hF n τ).2 j (by omega) x⟩)
        ⟨(hG' τ).1.of_le (by norm_num), fun j hj x => (hG' τ).2.1 j (by omega) x⟩
        (fun y => (hG' τ).2.2 1 (by norm_num) y) x ((hG' τ).2.2 2 (by norm_num) x)
  have h3 : Tendsto (fun n => F n r₁ x - F n r₂ x) atTop (𝓝 (g r₁ x - g r₂ x)) :=
    (hFg _ _).sub (hFg _ _)
  have h4 := hlim.congr' ((hftc r₁ r₂ x h1 h12 h2).mono fun n hn => hn.1.symm)
  exact tendsto_nhds_unique h3 h4

theorem s55m_limit (b : WholeBounds d) (hb : b.Valid) (S : WholeSetup b) (N : ℕ) {B K L t₀ : ℝ}
    (hB : 0 ≤ B) (hK : 0 ≤ K) (ht₀ : t₀ ∈ Set.Icc (0 : ℝ) b.T)
    (hgen : ∀ τ ∈ Set.Icc (0 : ℝ) b.T, ∀ u : Euc d → ℝ, ContDiff ℝ 4 u →
      (∀ n ≤ 4, ∀ x, ‖iteratedFDeriv ℝ n u x‖ ≤ B) →
      RgW (fun x => 1 + ‖x‖) 1 (B * K) (generatorW (S.coeff N) τ u))
    {F : ℕ → ℝ → Euc d → ℝ} {g : ℝ → Euc d → ℝ} {ψ₀ : Euc d → ℝ}
    (hF : ∀ n r', ContDiff ℝ 5 (F n r') ∧ ∀ j ≤ 5, ∀ x, ‖iteratedFDeriv ℝ j (F n r') x‖ ≤ B)
    (hFg : ∀ r' x, Tendsto (fun n => F n r' x) atTop (𝓝 (g r' x)))
    (hgr : ∀ r r' x, |g r x - g r' x| ≤ L * (1 + ‖x‖) * |r - r'|)
    (hftc : ∀ r₁ r₂ x, 0 ≤ r₁ → r₁ ≤ r₂ → r₂ < t₀ → ∀ᶠ n in atTop,
      F n r₁ x - F n r₂ x = ∫ τ in r₁..r₂, generatorW (S.coeff N) τ (F n τ) x ∧
        ContinuousOn (fun τ => generatorW (S.coeff N) τ (F n τ) x) (Set.Icc r₁ r₂))
    (hterm : g t₀ = ψ₀) : IsClassicalAdjointW (S.coeff N) t₀ ψ₀ g := by
  have hG' := fun r' => s55m_limit_G hB hF hFg r'
  have hG : ∀ r', ContDiff ℝ 4 (g r') ∧ ∀ j ≤ 4, ∀ x, ‖iteratedFDeriv ℝ j (g r') x‖ ≤ B :=
    fun r' => ⟨(hG' r').1, (hG' r').2.1⟩
  have hcg := s55m_cont_gen b hb S N hB hK hgen hG hgr
  have hincl : Continuous fun p : Set.Icc (0 : ℝ) t₀ × Euc d =>
      ((⟨p.1.1, p.1.2.1, p.1.2.2.trans ht₀.2⟩ : Set.Icc (0 : ℝ) b.T), p.2) :=
    ((continuous_subtype_val.comp continuous_fst).subtype_mk _).prodMk continuous_snd
  have hcL : ∀ x, ContinuousOn (fun τ => generatorW (S.coeff N) τ (g τ) x) (Set.Icc (0 : ℝ) b.T) := by
    intro x
    rw [continuousOn_iff_continuous_domRestrict]
    have hp : Continuous fun r : Set.Icc (0 : ℝ) b.T => ((r, x) : Set.Icc (0 : ℝ) b.T × Euc d) :=
      continuous_id.prodMk continuous_const
    exact Continuous.congr (hcg.comp hp) (fun r => rfl)
  refine ⟨fun r hr => (hG r).1.of_le (by norm_num), fun j hj => ⟨B, fun r hr x => (hG r).2 j (by omega) x⟩,
    fun j hj => ?_, hterm, ?_, ?_, ?_⟩
  · exact (s55m_cont_jet hB hG hgr (by omega)).comp
      ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
  · intro x r hr
    set r₂ : ℝ := (r + t₀) / 2 with hr₂
    have hr2 : r < r₂ ∧ r₂ < t₀ := ⟨by rw [hr₂]; linarith [hr.2], by rw [hr₂]; linarith [hr.2]⟩
    have hT : t₀ ≤ b.T := ht₀.2
    have hI : ∀ r'' ∈ Set.Icc (0 : ℝ) r₂, g r'' x = g r₂ x - ∫ τ in r₂..r'', generatorW (S.coeff N) τ (g τ) x := by
      intro r'' hr''
      have := s55m_limit_ftc b hb S N hB hK ht₀ hgen hF hFg hG' hftc hr''.1 hr''.2 hr2.2 x
      rw [intervalIntegral.integral_symm]; linarith
    have hcont : ContinuousOn (fun τ => generatorW (S.coeff N) τ (g τ) x) (Set.Icc (0 : ℝ) b.T) := hcL x
    have hrT : r ∈ Set.Ioo (0 : ℝ) b.T := ⟨hr.1, hr.2.trans_le hT⟩
    have hd : HasDerivAt (fun r'' => ∫ τ in r₂..r'', generatorW (S.coeff N) τ (g τ) x)
        (generatorW (S.coeff N) r (g r) x) r := by
      refine intervalIntegral.integral_hasDerivAt_right ?_ ?_ ?_
      · refine (hcont.mono ?_).intervalIntegrable
        rw [Set.uIcc_of_ge hr2.1.le]
        exact Set.Icc_subset_Icc hr.1.le (hr2.2.le.trans hT)
      · exact (hcont.mono Set.Ioo_subset_Icc_self).stronglyMeasurableAtFilter isOpen_Ioo r hrT
      · exact hcont.continuousAt (Icc_mem_nhds hrT.1 hrT.2)
    have hd2 := (hasDerivAt_const r (g r₂ x)).sub hd
    refine (hd2.congr_deriv (by ring)).congr_of_eventuallyEq ?_
    filter_upwards [Icc_mem_nhds hr.1 hr2.1] with r'' hr''
    exact hI r'' hr''
  · exact Continuous.congr (hcg.comp hincl) (fun p => rfl)
  · refine ⟨B * K, fun r hr x => ?_⟩
    have hrT : r ∈ Set.Icc (0 : ℝ) b.T := ⟨hr.1, hr.2.trans ht₀.2⟩
    have := (hgen r hrT (g r) (hG r).1 (hG r).2).2 0 (by norm_num) x
    rwa [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at this

/-! ### Convergence of a subsequence of the clipped family -/

theorem s55m_clip_le (t r r' : ℝ) (h : r ≤ r') :
    max 0 (min r' t) - max 0 (min r t) ≤ r' - r := by
  simp only [max_def, min_def]
  split_ifs <;> linarith

theorem s55m_clip_abs (t a b : ℝ) : |max 0 (min a t) - max 0 (min b t)| ≤ |a - b| := by
  rcases le_total a b with h | h
  · have h1 : max 0 (min a t) ≤ max 0 (min b t) := max_le_max le_rfl (min_le_min_right _ h)
    have h2 := s55m_clip_le t a b h
    rw [abs_of_nonpos (sub_nonpos.2 h1), abs_of_nonpos (sub_nonpos.2 h)]
    linarith
  · have h1 : max 0 (min b t) ≤ max 0 (min a t) := max_le_max le_rfl (min_le_min_right _ h)
    have h2 := s55m_clip_le t b a h
    rw [abs_of_nonneg (sub_nonneg.2 h1), abs_of_nonneg (sub_nonneg.2 h)]
    linarith

theorem s55m_lip_r_abs {C : WholeCoeff d} {t : ℝ} {φ : Euc d → ℝ} {f : ℝ → Euc d → ℝ}
    (hf : IsClassicalAdjointW C t φ f) {BL : ℝ}
    (hBL : ∀ τ ∈ Set.Icc (0 : ℝ) t, ∀ x, |generatorW C τ (f τ) x| ≤ BL * (1 + ‖x‖)) (hBL0 : 0 ≤ BL)
    {a b : ℝ} (ha : a ∈ Set.Icc (0 : ℝ) t) (hb : b ∈ Set.Icc (0 : ℝ) t) (x : Euc d) :
    |f a x - f b x| ≤ BL * (1 + ‖x‖) * |a - b| := by
  rcases le_total a b with h | h
  · rw [abs_of_nonpos (sub_nonpos.2 h), neg_sub]
    exact s55m_lip_r hf hBL ha.1 h hb.2 x
  · rw [abs_sub_comm (f a x), abs_of_nonneg (sub_nonneg.2 h)]
    exact s55m_lip_r hf hBL hb.1 h ha.2 x

theorem s55m_seq (b : WholeBounds d) (hb : b.Valid) (S : WholeSetup b) (N : ℕ)
    (hRd : ∃ (Rg : PDE.Regime) (ν₀ : ℝ), RdRegimeHolds Rg d b.s b.M (S.invβ N) ν₀)
    (α : MultiIndex d) {r t₀ : ℝ} (hr0 : 0 ≤ r) (ht₀ : t₀ ∈ Set.Ioc r b.T) {tn : ℕ → ℝ}
    (htn : ∀ n, tn n ∈ Set.Ioc r b.T) (hlim : Tendsto tn atTop (𝓝 t₀)) (a : Fin d) (x : Euc d) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧ Tendsto (fun i => gradComp a (propagatorW (S.coeff N) r (tn (ns i))
        (generatorW (S.coeff N) (tn (ns i)) (oscTestFun b.m α))) x) atTop
      (𝓝 (gradComp a (propagatorW (S.coeff N) r t₀ (generatorW (S.coeff N) t₀ (oscTestFun b.m α))) x)) := by
  obtain ⟨B, hB0, hfam⟩ := s55m_family b hb S N α
  obtain ⟨K, hK0, hgen⟩ := s55m_gen_rgW b hb S N
  obtain ⟨Bφ, hBφ0, hφ4, hφb⟩ := s55m_osc_bound b hb α
  have hk9 : (9 : ℝ) < b.k := by
    have := hb.hk; have : (2 : ℝ) ≤ d := by exact_mod_cast hb.hd
    linarith
  have hk9' : 9 < b.k := by exact_mod_cast hk9
  set C := S.coeff N with hC
  set φ := oscTestFun b.m α with hφ
  set ψ : ℝ → Euc d → ℝ := fun t => generatorW C t φ with hψ
  set fam : ℝ → ℝ → Euc d → ℝ := fun t r' => propagatorW C r' t (ψ t) with hfamdef
  have hmemT : ∀ n, tn n ∈ Set.Icc (0 : ℝ) b.T := fun n => ⟨hr0.trans (htn n).1.le, (htn n).2⟩
  have ht₀T : t₀ ∈ Set.Icc (0 : ℝ) b.T := ⟨hr0.trans ht₀.1.le, ht₀.2⟩
  have hcl : ∀ n, IsClassicalAdjointW C (tn n) (ψ (tn n)) (fam (tn n)) := fun n => (hfam _ (hmemT n)).1
  have hsl : ∀ n, ∀ r' ∈ Set.Icc (0 : ℝ) (tn n), ContDiff ℝ 5 (fam (tn n) r') ∧
      ∀ j ≤ 5, ∀ y, ‖iteratedFDeriv ℝ j (fam (tn n) r') y‖ ≤ B := by
    intro n r' hr'
    obtain ⟨h1, h2⟩ := (hfam _ (hmemT n)).2 r' hr'
    exact ⟨h1.of_le (by exact_mod_cast (by omega : 5 ≤ b.k + 1)), fun j hj y => h2 j (by omega) y⟩
  have hgl : ∀ n, ∀ τ ∈ Set.Icc (0 : ℝ) (tn n), ∀ y, |generatorW C τ (fam (tn n) τ) y| ≤ B * K * (1 + ‖y‖) := by
    intro n τ hτ y
    have hτT : τ ∈ Set.Icc (0 : ℝ) b.T := ⟨hτ.1, hτ.2.trans (hmemT n).2⟩
    obtain ⟨h1, h2⟩ := hsl n τ hτ
    have := (hgen τ hτT B (fam (tn n) τ) hB0 (h1.of_le (by norm_num)) (fun j hj => h2 j (by omega))).2 0
      (by norm_num) y
    rwa [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at this
  -- the clipped family
  set cl : ℕ → ℝ → ℝ := fun n r' => max 0 (min r' (tn n)) with hcl_def
  have hclmem : ∀ n r', cl n r' ∈ Set.Icc (0 : ℝ) (tn n) := fun n r' =>
    ⟨le_max_left _ _, max_le (hmemT n).1 (min_le_right _ _)⟩
  set F : ℕ → ℝ → Euc d → ℝ := fun n r' => fam (tn n) (cl n r') with hFdef
  set L : ℝ := max B (B * K) with hL
  have hL0 : 0 ≤ L := le_max_of_le_left hB0
  have hFb : ∀ n r' y, |F n r' y| ≤ B := by
    intro n r' y
    have := (hsl n _ (hclmem n r')).2 0 (by norm_num) y
    rwa [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at this
  have hFr : ∀ n r' r'' y, |F n r' y - F n r'' y| ≤ L * (1 + ‖y‖) * |r' - r''| := by
    have key : ∀ n r' r'' y, r' ≤ r'' → |F n r' y - F n r'' y| ≤ L * (1 + ‖y‖) * |r' - r''| := by
      intro n r' r'' y hle
      have hcle : cl n r' ≤ cl n r'' := max_le_max le_rfl (min_le_min_right _ hle)
      have h1 := s55m_lip_r (hcl n) (BL := B * K) (hgl n) (hclmem n r').1 hcle (hclmem n r'').2 y
      have h2 := s55m_clip_le (tn n) r' r'' hle
      rw [abs_of_nonpos (sub_nonpos.2 hle), neg_sub]
      refine h1.trans ?_
      have : 0 ≤ B * K * (1 + ‖y‖) := by positivity
      calc B * K * (1 + ‖y‖) * (cl n r'' - cl n r') ≤ B * K * (1 + ‖y‖) * (r'' - r') :=
            mul_le_mul_of_nonneg_left h2 this
        _ ≤ L * (1 + ‖y‖) * (r'' - r') := by
            have h3 : B * K ≤ L := le_max_right _ _
            have h4 : 0 ≤ r'' - r' := sub_nonneg.2 hle
            gcongr
    intro n r' r'' y
    rcases le_total r' r'' with h | h
    · exact key n r' r'' y h
    · rw [abs_sub_comm (F n r' y), abs_sub_comm r' r'']; exact key n r'' r' y h
  have hFx : ∀ n r' y y', |F n r' y - F n r' y'| ≤ L * ‖y - y'‖ := by
    intro n r' y y'
    have hs := hsl n _ (hclmem n r')
    refine (s55m_lip_x (u := F n r') (B := B) (hs.1.differentiable (by norm_num)) (fun z => ?_) y y').trans ?_
    · have := hs.2 1 (by norm_num) z
      rwa [norm_iteratedFDeriv_one] at this
    · exact mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)
  obtain ⟨ns, hns, g, hpt, hgr, -, -⟩ := s55m_ex F hL0 hFb hFr hFx
  set F' : ℕ → ℝ → Euc d → ℝ := fun i => F (ns i) with hF'
  have hF'b : ∀ i r', ContDiff ℝ 5 (F' i r') ∧ ∀ j ≤ 5, ∀ y, ‖iteratedFDeriv ℝ j (F' i r') y‖ ≤ B :=
    fun i r' => hsl (ns i) _ (hclmem (ns i) r')
  have htns : Tendsto (fun i => tn (ns i)) atTop (𝓝 t₀) := hlim.comp hns.tendsto_atTop
  have hftc : ∀ r₁ r₂ y, 0 ≤ r₁ → r₁ ≤ r₂ → r₂ < t₀ → ∀ᶠ i in atTop,
      F' i r₁ y - F' i r₂ y = ∫ τ in r₁..r₂, generatorW C τ (F' i τ) y ∧
        ContinuousOn (fun τ => generatorW C τ (F' i τ) y) (Set.Icc r₁ r₂) := by
    intro r₁ r₂ y h1 h12 h2
    filter_upwards [htns.eventually (Ioi_mem_nhds h2)] with i hi
    have hi' : r₂ ≤ tn (ns i) := le_of_lt hi
    have hcl_id : ∀ τ ∈ Set.Icc r₁ r₂, cl (ns i) τ = τ := by
      intro τ hτ
      show max 0 (min τ (tn (ns i))) = τ
      rw [min_eq_left (hτ.2.trans hi'), max_eq_right (h1.trans hτ.1)]
    have hFeq : ∀ τ ∈ Set.Icc r₁ r₂, F' i τ = fam (tn (ns i)) τ := fun τ hτ => by
      show fam (tn (ns i)) (cl (ns i) τ) = _
      rw [hcl_id τ hτ]
    refine ⟨?_, ?_⟩
    · rw [hFeq r₁ ⟨le_rfl, h12⟩, hFeq r₂ ⟨h12, le_rfl⟩, s55m_ftc (hcl (ns i)) h1 h12 hi' y]
      refine intervalIntegral.integral_congr fun τ hτ => ?_
      rw [Set.uIcc_of_le h12] at hτ
      simp only [hFeq τ hτ]
    · refine ((s55m_contL (hcl (ns i)) y).mono (Set.Icc_subset_Icc h1 hi')).congr fun τ hτ => ?_
      simp only [hFeq τ hτ]
  have hterm : g t₀ = ψ t₀ := by
    funext y
    have hψt : Tendsto (fun i => ψ (tn (ns i)) y) atTop (𝓝 (ψ t₀ y)) :=
      s55m_gen_tendsto_S b hb S N hBφ0 (τ := fun i => tn (ns i)) (fun i => hmemT _) ht₀T htns
        (u := fun _ => φ) (u₀ := φ)
        (fun _ => ⟨hφ4.of_le (by norm_num), fun n hn z => hφb n (by omega) z⟩)
        ⟨hφ4.of_le (by norm_num), fun n hn z => hφb n (by omega) z⟩ (fun _ => tendsto_const_nhds) y
        tendsto_const_nhds
    have h1 : Tendsto (fun i => F' i t₀ y - ψ (tn (ns i)) y) atTop (𝓝 (g t₀ y - ψ t₀ y)) :=
      (hpt (t₀) y).sub hψt
    have h2 : Tendsto (fun i => F' i t₀ y - ψ (tn (ns i)) y) atTop (𝓝 0) := by
      have h0 : Tendsto (fun i => B * K * (1 + ‖y‖) * |t₀ - tn (ns i)|) atTop (𝓝 0) := by
        have := ((htns.const_sub t₀).abs).const_mul (B * K * (1 + ‖y‖))
        simpa using this
      refine squeeze_zero_norm (fun i => ?_) h0
      have hterm_i : ψ (tn (ns i)) = fam (tn (ns i)) (tn (ns i)) := ((hcl (ns i)).terminal).symm
      rw [hterm_i, Real.norm_eq_abs]
      have := s55m_lip_r_abs (hcl (ns i)) (BL := B * K) (hgl (ns i)) (by positivity) (hclmem (ns i) t₀)
        ⟨(hmemT (ns i)).1, le_rfl⟩ y
      refine this.trans ?_
      have h3 := s55m_clip_abs (tn (ns i)) t₀ (tn (ns i))
      have h4 : max 0 (min (tn (ns i)) (tn (ns i))) = tn (ns i) := by
        rw [min_self, max_eq_right (hmemT _).1]
      rw [h4] at h3
      exact mul_le_mul_of_nonneg_left h3 (by positivity)
    have := tendsto_nhds_unique h1 h2
    linarith
  have hcl' : IsClassicalAdjointW C t₀ (ψ t₀) g :=
    s55m_limit b hb S N hB0 hK0 ht₀T (fun τ hτ u hu hub => hgen τ hτ B u hB0 hu hub) (F := F') hF'b hpt hgr hftc hterm
  have hfg : ∀ r' ∈ Set.Icc (0 : ℝ) t₀, propagatorW C r' t₀ (ψ t₀) = g r' :=
    s55f_propagatorW_eq b hb S N hRd ht₀T hcl'
  have hG1 := s55m_limit_G hB0 hF'b hpt r
  refine ⟨ns, hns, ?_⟩
  have hrle : ∀ i, F' i r = fam (tn (ns i)) r := fun i => by
    show fam (tn (ns i)) (cl (ns i) r) = _
    have : cl (ns i) r = r := by
      show max 0 (min r (tn (ns i))) = r
      rw [min_eq_left (htn _).1.le, max_eq_right hr0]
    rw [this]
  have hgrad := s55m_grad_tendsto (hG1.2.2 1 (by norm_num) x)
  have hcomp : Tendsto (fun i => gradient (F' i r) x a) atTop (𝓝 (gradient (g r) x a)) :=
    ((EuclideanSpace.proj a : Euc d →L[ℝ] ℝ).continuous.tendsto _).comp hgrad
  have e : gradComp a (propagatorW C r t₀ (ψ t₀)) x = gradient (g r) x a := by
    rw [hfg r ⟨hr0, ht₀.1.le⟩]; rfl
  rw [e]
  refine hcomp.congr fun i => ?_
  rw [hrle i]; rfl

/-! ### Continuity in the terminal time and `S55fMeas` -/

theorem s55m_continuousOn (b : WholeBounds d) (hb : b.Valid) (S : WholeSetup b) (N : ℕ)
    (hRd : ∃ (Rg : PDE.Regime) (ν₀ : ℝ), RdRegimeHolds Rg d b.s b.M (S.invβ N) ν₀)
    (α : MultiIndex d) (a : Fin d) {r : ℝ} (hr0 : 0 ≤ r) (x : Euc d) :
    ContinuousOn (fun t => gradComp a (propagatorW (S.coeff N) r t
      (generatorW (S.coeff N) t (oscTestFun b.m α))) x) (Set.Ioc r b.T) := by
  intro t₀ ht₀
  rw [ContinuousWithinAt, tendsto_iff_seq_tendsto]
  intro tn htn
  obtain ⟨hlim, hev⟩ := tendsto_nhdsWithin_iff.1 htn
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.1 hev
  set tn' : ℕ → ℝ := fun n => tn (n + n₀) with htn'
  have hlim' : Tendsto tn' atTop (𝓝 t₀) := hlim.comp (tendsto_add_atTop_nat n₀)
  have hmem : ∀ n, tn' n ∈ Set.Ioc r b.T := fun n => hn₀ _ (by omega)
  rw [← tendsto_add_atTop_iff_nat n₀]
  refine tendsto_of_subseq_tendsto fun ns₁ hns₁ => ?_
  obtain ⟨ns, hns, h⟩ := s55m_seq b hb S N hRd α hr0 ht₀ (tn := fun i => tn' (ns₁ i)) (fun i => hmem _)
    (hlim'.comp hns₁) a x
  exact ⟨ns, h⟩

/-- The `Rd`-regime slice of `S55fMeas`: for every `N` whose regime is the `Rd` disjunct, the `t`-measurability
of the orbit coordinates. -/
def S55fMeasRd (b : WholeBounds d) (S : WholeSetup b) : Prop :=
  ∀ N : ℕ, (∃ (Rg : PDE.Regime) (ν₀ : ℝ), RdRegimeHolds Rg d b.s b.M (S.invβ N) ν₀) →
    ∀ (a : Fin d), ∀ r ∈ Set.Icc (0 : ℝ) b.T, ∀ (α : MultiIndex d) (x : Euc d),
      AEStronglyMeasurable (fun t => gradComp a (propagatorW (S.coeff N) r t
        (generatorW (S.coeff N) t (oscTestFun b.m α))) x) (volume.restrict (Set.Ioc r b.T))

theorem s55fMeasRd_holds (b : WholeBounds d) (hb : b.Valid) (S : WholeSetup b) : S55fMeasRd b S :=
  fun N hRd a r hr α x =>
    (s55m_continuousOn b hb S N hRd α a hr.1 x).aestronglyMeasurable measurableSet_Ioc

theorem s55fMeas_of_rd (b : WholeBounds d) (hb : b.Valid) (S : WholeSetup b)
    (h : ∀ N : ℕ, ∃ (Rg : PDE.Regime) (ν₀ : ℝ), RdRegimeHolds Rg d b.s b.M (S.invβ N) ν₀) :
    S55fMeas b S :=
  fun N a r hr α x => s55fMeasRd_holds b hb S N (h N) a r hr α x


/-! ### Consumers: features and maximal estimate when every `N` is in the `Rd` regime -/

/-- `s55f_features_of_meas` for the setups all of whose regimes are the `Rd` disjunct (R1, R2a, R2c, R3). -/
theorem s55m_features_rd (b : WholeBounds d) (hb : b.Valid) :
    ∃ C : ℝ, ∀ S : WholeSetup b,
      (∀ N : ℕ, ∃ (Rg : PDE.Regime) (ν₀ : ℝ), RdRegimeHolds Rg d b.s b.M (S.invβ N) ν₀) →
      ∀ (N : ℕ) (a : Fin d), ∀ r ∈ Set.Icc (0 : ℝ) b.T,
        ContDiff ℝ (b.k : WithTop ℕ∞) (fun x => gradFeature (S.coeff N) b.m b.T a r x) ∧
        ∀ j ≤ b.k, ∀ x, ‖iteratedFDeriv ℝ j (fun y => gradFeature (S.coeff N) b.m b.T a r y) x‖ ≤ C := by
  obtain ⟨C, hC⟩ := s55f_features_of_meas b hb
  exact ⟨C, fun S hS => hC S (s55fMeas_of_rd b hb S hS)⟩

/-- `s55f_maximal_of_meas` for the setups all of whose regimes are the `Rd` disjunct. -/
theorem s55m_maximal_rd (b : WholeBounds d) (hb : b.Valid) :
    ∃ Ctr Cmax : ℝ, ∀ S : WholeSetup b,
      (∀ N : ℕ, ∃ (Rg : PDE.Regime) (ν₀ : ℝ), RdRegimeHolds Rg d b.s b.M (S.invβ N) ν₀) →
      ∀ N : ℕ, OrbitMaximalConclusion b.m b.T
        (fun (a : Fin d) (r : ℝ) (x : Euc d) => gradFeature (S.coeff N) b.m b.T a r x) Ctr Cmax := by
  obtain ⟨Ctr, Cmax, h⟩ := s55f_maximal_of_meas b hb
  exact ⟨Ctr, Cmax, fun S hS => h S (s55fMeas_of_rd b hb S hS)⟩

end HRS.MS.Go
