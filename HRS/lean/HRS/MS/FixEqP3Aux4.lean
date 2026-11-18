import HRS.MS.FixEqP3Aux3

/-!
# S5.7 `fixed_equation` (worker S57P), part 16: the propagator on the Hermite expansion

`s57p_prop_partial`: `U^{r,t}(∑_{α ∈ F} b_α φ_α) = ∑_{α ∈ F} b_α U^{r,t}φ_α`.
`s57p_prop_expand`: for `φ ∈ Σ^m` (`m > J + d`, `J ≥ 3(j+1+⌈d/2⌉)+9`) and every `ε > 0` there is a finite `F₀` with
`‖D^i (U^{r,t}φ - ∑_{α ∈ F} b_α U^{r,t}φ_α)‖_∞ ≤ ε` for all `F ⊇ F₀`, `i ≤ j`, `0 ≤ r ≤ t ≤ T`.
-/

noncomputable section

set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000

open MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace HRS.MS.FixEq

open HRS HRS.Whole HRS.MP.RdGen HRS.MS.Go HRS.MS.Fcau

variable {d : ℕ}

theorem s57p_partial_jets {m : ℝ} {φ : Euc d → ℝ} {R : ℕ} {Cα : MultiIndex d → ℝ}
    (hj : ∀ α : MultiIndex d, ContDiff ℝ ∞ (oscTestFun m α) ∧ ∀ n ≤ R, ∀ x,
      ‖iteratedFDeriv ℝ n (oscTestFun m α) x‖ ≤ Cα α) (F : Finset (MultiIndex d)) :
    ContDiff ℝ (R : ℕ) (s57pP d m φ F) ∧ ∀ l ≤ R, ∀ x,
      ‖iteratedFDeriv ℝ l (s57pP d m φ F) x‖ ≤ ∑ α ∈ F, |s57pb d m φ α| * Cα α := by
  induction F using Finset.induction_on with
  | empty =>
    have e : s57pP d m φ ∅ = fun _ => (0 : ℝ) := by funext y; simp [s57pP]
    rw [e]
    refine ⟨contDiff_const, fun l hl x => ?_⟩
    simp only [Finset.sum_empty]
    rcases l with _ | l
    · simp
    · rw [iteratedFDeriv_const_of_ne (by omega)]; simp
  | insert β F hβ ih =>
    obtain ⟨ih1, ih2⟩ := ih
    have e : s57pP d m φ (insert β F) = fun y => 1 * s57pP d m φ F y + s57pb d m φ β * oscTestFun m β y := by
      funext y; simp [s57pP, Finset.sum_insert hβ]; ring
    have hc : ContDiff ℝ (R : ℕ) (oscTestFun m β) := (hj β).1.of_le (by exact_mod_cast le_top)
    rw [e, Finset.sum_insert hβ]
    refine ⟨(contDiff_const.mul ih1).add (contDiff_const.mul hc), fun l hl x => ?_⟩
    rw [s57p_iter_lin2 (ih1.of_le (by exact_mod_cast hl)) (hc.of_le (by exact_mod_cast hl))]
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_one, one_mul]
    have := mul_le_mul_of_nonneg_left ((hj β).2 l hl x) (abs_nonneg (s57pb d m φ β))
    linarith [ih2 l hl x]

theorem s57p_prop_zero {C : WholeCoeff d} {θ : Euc d → ℝ} {T : ℝ} {j : ℕ} {K : ℝ} (hθ : IsUlCutoff θ)
    (F : S57pFam C θ T j K) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) :
    ∀ r ∈ Set.Icc (0 : ℝ) t, propagatorW C r t (fun _ => (0 : ℝ)) = fun _ => (0 : ℝ) := by
  have hc : ContDiff ℝ ((j + 1 + ⌈(d : ℝ) / 2⌉₊ : ℕ) : WithTop ℕ∞) (fun _ : Euc d => (0 : ℝ)) := contDiff_const
  have hb : ∀ l ≤ j + 1 + ⌈(d : ℝ) / 2⌉₊, ∀ x : Euc d, ‖iteratedFDeriv ℝ l (fun _ : Euc d => (0 : ℝ)) x‖ ≤ 0 := by
    intro l hl x
    rcases l with _ | l
    · simp
    · rw [iteratedFDeriv_const_of_ne (by omega)]; simp
  intro r hr
  have := s57p_prop_lin2 hθ F le_rfl le_rfl hc hb hc hb 0 0 ht r hr
  have e : (fun _ : Euc d => 0 * (0 : ℝ) + 0 * 0) = fun _ => 0 := by funext; simp
  rw [e] at this
  rw [this]
  funext x; simp

theorem s57p_prop_partial {C : WholeCoeff d} {θ : Euc d → ℝ} {T : ℝ} {j : ℕ} {K : ℝ} (hθ : IsUlCutoff θ)
    (Fm : S57pFam C θ T j K) {m : ℝ} {φ : Euc d → ℝ} {Cα : MultiIndex d → ℝ} (hCα : ∀ α, 0 ≤ Cα α)
    (hj : ∀ α : MultiIndex d, ContDiff ℝ ∞ (oscTestFun m α) ∧ ∀ n ≤ j + 1 + ⌈(d : ℝ) / 2⌉₊, ∀ x,
      ‖iteratedFDeriv ℝ n (oscTestFun m α) x‖ ≤ Cα α) (F : Finset (MultiIndex d)) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) T) :
    ∀ r ∈ Set.Icc (0 : ℝ) t, propagatorW C r t (s57pP d m φ F) =
      fun x => ∑ α ∈ F, s57pb d m φ α * propagatorW C r t (oscTestFun m α) x := by
  induction F using Finset.induction_on with
  | empty =>
    intro r hr
    have e : s57pP d m φ ∅ = fun _ => (0 : ℝ) := by funext y; simp [s57pP]
    rw [e, s57p_prop_zero hθ Fm ht r hr]
    funext x; simp
  | insert β F hβ ih =>
    intro r hr
    obtain ⟨ih1, ih2⟩ := s57p_partial_jets (φ := φ) hj F
    have e : s57pP d m φ (insert β F) = fun y => 1 * s57pP d m φ F y + s57pb d m φ β * oscTestFun m β y := by
      funext y; simp [s57pP, Finset.sum_insert hβ]; ring
    have hB1 : 0 ≤ ∑ α ∈ F, |s57pb d m φ α| * Cα α :=
      Finset.sum_nonneg fun α _ => mul_nonneg (abs_nonneg _) (hCα α)
    have hc : ContDiff ℝ ((j + 1 + ⌈(d : ℝ) / 2⌉₊ : ℕ) : WithTop ℕ∞) (oscTestFun m β) :=
      (hj β).1.of_le (by exact_mod_cast le_top)
    rw [e, s57p_prop_lin2 hθ Fm hB1 (hCα β) ih1 ih2 hc (hj β).2 1 (s57pb d m φ β) ht r hr]
    funext x
    have ihr := congrFun (ih r hr) x
    rw [ihr, Finset.sum_insert hβ]
    ring

theorem s57p_prop_expand {C : WholeCoeff d} {θ : Euc d → ℝ} {T : ℝ} {j : ℕ} {K : ℝ} (hθ : IsUlCutoff θ)
    (hd : 1 ≤ d) (Fm : S57pFam C θ T j K) {m : ℝ} {J : ℕ} (hJ : 3 * (j + 1 + ⌈(d : ℝ) / 2⌉₊) + 9 ≤ J)
    (hm : (J : ℝ) + d < m) {φ : Euc d → ℝ} (hφ : IsOscTest m φ) {ε : ℝ} (hε : 0 < ε) :
    ∃ F₀ : Finset (MultiIndex d), ∀ F : Finset (MultiIndex d), F₀ ⊆ F → ∀ t ∈ Set.Icc (0 : ℝ) T,
      ∀ r ∈ Set.Icc (0 : ℝ) t, ∀ i ≤ j, ∀ x,
        ‖iteratedFDeriv ℝ i (fun y => propagatorW C r t φ y -
          ∑ α ∈ F, s57pb d m φ α * propagatorW C r t (oscTestFun m α) y) x‖ ≤ ε := by
  set R : ℕ := j + 1 + ⌈(d : ℝ) / 2⌉₊ with hR
  obtain ⟨Cj, hCj0, hjets⟩ := s57p_osc_jets hθ hd m J R hJ
  obtain ⟨hsum, hexp, htail⟩ := s57p_hermite_series hd hm hCj0 hjets hφ
  obtain ⟨Cu, hCu0, hCu⟩ := s57p_orb hθ j
  set g : MultiIndex d → ℝ := fun α => |s57pb d m φ α| * (Cj * oscEigenvalue d α ^ (((J : ℝ) - m) / 2)) with hg
  have hg0 : ∀ α, 0 ≤ g α := fun α => mul_nonneg (abs_nonneg _) (mul_nonneg hCj0
    (Real.rpow_nonneg (oscEv_pos α).le _))
  have htl : ∀ F : Finset (MultiIndex d), ∑' α, (if α ∈ F then 0 else g α) = ∑' α, g α - ∑ α ∈ F, g α := by
    intro F
    have h1 : ∑' α, (if α ∈ F then 0 else g α) = ∑' α, (g α - if α ∈ F then g α else 0) := by
      refine tsum_congr fun α => ?_
      by_cases hα : α ∈ F <;> simp [hα]
    have hsF : Summable fun α : MultiIndex d => (if α ∈ F then g α else 0) :=
      summable_of_ne_finset_zero (s := F) (fun α hα => by simp [hα])
    have hsF' : ∑' α, (if α ∈ F then g α else 0) = ∑ α ∈ F, g α := by
      rw [tsum_eq_sum (s := F) (fun α hα => by simp [hα])]
      exact Finset.sum_congr rfl fun α hα => by simp [hα]
    rw [h1, hsum.tsum_sub hsF, hsF']
  have hε' : 0 < ε / (|K| * Cu + 1) := by positivity
  have hten : Tendsto (fun F : Finset (MultiIndex d) => ∑ α ∈ F, g α) atTop (𝓝 (∑' α, g α)) := hsum.hasSum
  obtain ⟨F₀, hF₀⟩ := (eventually_atTop.1 ((Metric.tendsto_nhds.1 hten) _ hε'))
  refine ⟨F₀, fun F hF t ht r hr i hi x => ?_⟩
  have hdist := hF₀ F hF
  rw [Real.dist_eq] at hdist
  have htailF : ∑' α, (if α ∈ F then 0 else g α) ≤ ε / (|K| * Cu + 1) := by
    rw [htl]
    have := (abs_lt.1 hdist).1
    linarith
  have htail0 : 0 ≤ ∑' α, (if α ∈ F then 0 else g α) := tsum_nonneg fun α => by
    by_cases hα : α ∈ F <;> simp [hα, hg0]
  -- jets of φ and of φ - P_F
  have hφ1 : ContDiff ℝ (R : ℕ) φ := hφ.1.of_le (by exact_mod_cast le_top)
  have hBφ0 : ∀ n ≤ R, ∀ x, ‖iteratedFDeriv ℝ n φ x‖ ≤ ∑' α, g α := by
    intro n hn x
    have := htail ∅ n hn x
    have e : (fun y => φ y - s57pP d m φ ∅ y) = φ := by funext y; simp [s57pP]
    rw [e] at this
    refine this.trans (le_of_eq ?_)
    refine tsum_congr fun α => ?_
    simp [hg]
  have hPF := s57p_partial_jets (φ := φ) (Cα := fun α => Cj * oscEigenvalue d α ^ (((J : ℝ) - m) / 2))
    (fun α => ⟨(hjets α).1, (hjets α).2⟩) F
  have hPF2 : ∀ l ≤ R, ∀ x, ‖iteratedFDeriv ℝ l (s57pP d m φ F) x‖ ≤ ∑ α ∈ F, g α := hPF.2
  have hPF' := s57p_prop_partial hθ Fm (φ := φ) (Cα := fun α => Cj * oscEigenvalue d α ^ (((J : ℝ) - m) / 2))
    (fun α => mul_nonneg hCj0 (Real.rpow_nonneg (oscEv_pos α).le _)) (fun α => ⟨(hjets α).1,
      fun n hn x => (hjets α).2 n (by omega) x⟩) F ht
  have hlin := s57p_prop_lin2 hθ Fm (tsum_nonneg hg0) (Finset.sum_nonneg fun α _ => hg0 α) hφ1 hBφ0
    hPF.1 hPF2 1 (-1) ht r hr
  have hψ : ContDiff ℝ (R : ℕ) (fun y => φ y - s57pP d m φ F y) := hφ1.sub hPF.1
  have hψb : ∀ l ≤ R, ∀ x, ‖iteratedFDeriv ℝ l (fun y => φ y - s57pP d m φ F y) x‖ ≤
      ∑' α, (if α ∈ F then 0 else g α) := fun l hl x => htail F l hl x
  obtain ⟨-, hO⟩ := hCu Fm.adj htail0 hψ hψb t ht
  have key : (fun y => propagatorW C r t φ y - ∑ α ∈ F, s57pb d m φ α * propagatorW C r t (oscTestFun m α) y) =
      propagatorW C r t (fun y => φ y - s57pP d m φ F y) := by
    rw [show (fun y => φ y - s57pP d m φ F y) = fun y => 1 * φ y + (-1) * s57pP d m φ F y from by
      funext y; ring, hlin, hPF' r hr]
    funext x; ring
  rw [key]
  refine ((hO r hr).2 i hi x).trans ?_
  have hKC : 0 ≤ |K| * Cu := mul_nonneg (abs_nonneg _) hCu0
  have hpos : 0 < |K| * Cu + 1 := by linarith
  calc |K| * (Cu * ∑' α, (if α ∈ F then 0 else g α)) ≤ |K| * (Cu * (ε / (|K| * Cu + 1))) := by
        gcongr
    _ = (|K| * Cu) * ε / (|K| * Cu + 1) := by ring
    _ ≤ ε := by rw [div_le_iff₀ hpos]; nlinarith

end HRS.MS.FixEq
