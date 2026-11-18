import HRS.MS.WadAux100

/-!
# S8.3, packet S8F-1, part 2: difference quotients converge to partial derivatives

`s8f_dpF k m g`: the iterated difference along a tuple `m : Fin k → ℝ^d` (the last entry is the outermost `Δ`);
`s8f_dp_ofFn`: it agrees with `s8f_dp` along `(List.ofFn m).reverse`.
`s8f_dpF_taylor`: `‖Δ_m g (y) - D^k g (y) m‖ ≤ 2^k ε ∏‖m_l‖` if the oscillation of `D^k g` on the ball of radius `R ≥ Σ‖m_l‖` is at most `ε`.
`s8f_partial_le_of_dp`: if `|Δ_{h e_{i_1}} ⋯ Δ_{h e_{i_k}} g (x)| ≤ B h^k` for small `h` and `g ∈ C^k`, then `|∂_{i_1}⋯∂_{i_k} g (x)| ≤ B`.
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal ContDiff

namespace HRS.MS.Wad

open HRS HRS.Whole

variable {d : ℕ}

def s8f_dpF {F : Type} [AddCommGroup F] : (k : ℕ) → (Fin k → Euc d) → (Euc d → F) → Euc d → F
  | 0, _, g => g
  | k + 1, m, g => fun y => s8f_dpF k (Fin.init m) g (y + m (Fin.last k)) - s8f_dpF k (Fin.init m) g y

theorem s8f_dp_ofFn {F : Type} [AddCommGroup F] : ∀ (k : ℕ) (m : Fin k → Euc d) (g : Euc d → F),
    s8f_dp (List.ofFn m).reverse g = s8f_dpF k m g := by
  intro k
  induction k with
  | zero => intro m g; simp [s8f_dp, s8f_dpF]
  | succ k ih =>
    intro m g
    rw [List.ofFn_succ', List.concat_eq_append, List.reverse_append]
    funext y
    show s8f_dp (List.ofFn fun i : Fin k => m i.castSucc).reverse g (y + m (Fin.last k)) -
      s8f_dp (List.ofFn fun i : Fin k => m i.castSucc).reverse g y = _
    rw [ih (fun i => m i.castSucc) g]
    rfl

theorem s8f_dpF_fderiv {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] (k : ℕ) (m : Fin k → Euc d)
    {g : Euc d → F} (hg : Differentiable ℝ g) : fderiv ℝ (s8f_dpF k m g) = s8f_dpF k m (fderiv ℝ g) := by
  rw [← s8f_dp_ofFn, ← s8f_dp_ofFn]
  exact s8f_dp_fderiv _ hg

theorem s8f_dpF_differentiable {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] (k : ℕ) (m : Fin k → Euc d)
    {g : Euc d → F} (hg : Differentiable ℝ g) : Differentiable ℝ (s8f_dpF k m g) := by
  rw [← s8f_dp_ofFn]
  exact s8f_dp_differentiable _ hg

theorem s8f_norm_iter_sub {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] (k : ℕ) (g : Euc d → F)
    (y1 y2 : Euc d) :
    ‖iteratedFDeriv ℝ k (fderiv ℝ g) y1 - iteratedFDeriv ℝ k (fderiv ℝ g) y2‖ =
      ‖iteratedFDeriv ℝ (k + 1) g y1 - iteratedFDeriv ℝ (k + 1) g y2‖ := by
  rw [iteratedFDeriv_succ_eq_comp_right, iteratedFDeriv_succ_eq_comp_right]
  simp only [Function.comp_apply]
  rw [← dist_eq_norm, ← dist_eq_norm, LinearIsometryEquiv.dist_map]

theorem s8f_dpF_taylor : ∀ (k : ℕ) {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] (g : Euc d → F),
    ContDiff ℝ k g → ∀ (m : Fin k → Euc d) (y : Euc d) (R ε : ℝ), (∑ l, ‖m l‖) ≤ R → 0 ≤ ε →
    (∀ y1 y2, ‖y1 - y‖ ≤ R → ‖y2 - y‖ ≤ R →
      ‖iteratedFDeriv ℝ k g y1 - iteratedFDeriv ℝ k g y2‖ ≤ ε) →
    ‖s8f_dpF k m g y - iteratedFDeriv ℝ k g y m‖ ≤ 2 ^ k * ε * ∏ l, ‖m l‖ := by
  intro k
  induction k with
  | zero =>
    intro F _ _ g hg m y R ε hR hε hmod
    simp [s8f_dpF, iteratedFDeriv_zero_apply, hε]
  | succ k ih =>
    intro F _ _ g hg m y R ε hR hε hmod
    set e : Euc d := m (Fin.last k) with he
    set m' : Fin k → Euc d := Fin.init m with hm'
    have hdg : Differentiable ℝ g := hg.differentiable (by simp)
    have hDg : ContDiff ℝ k (fderiv ℝ g) := hg.fderiv_right (by norm_cast)
    set A : Euc d →L[ℝ] F := iteratedFDeriv ℝ k (fderiv ℝ g) y m' with hA
    have hsum : (∑ l, ‖m l‖) = (∑ l : Fin k, ‖m' l‖) + ‖e‖ := by
      rw [Fin.sum_univ_castSucc]; rfl
    have hprod : (∏ l, ‖m l‖) = (∏ l : Fin k, ‖m' l‖) * ‖e‖ := by
      rw [Fin.prod_univ_castSucc]; rfl
    have hP : 0 ≤ ∏ l : Fin k, ‖m' l‖ := Finset.prod_nonneg fun l _ => norm_nonneg _
    have hS0 : 0 ≤ ∑ l : Fin k, ‖m' l‖ := Finset.sum_nonneg fun l _ => norm_nonneg _
    set G : Euc d → F := s8f_dpF k m' g with hG
    have hGd : Differentiable ℝ G := s8f_dpF_differentiable k m' hdg
    set C : ℝ := (2 ^ k * ε * ∏ l : Fin k, ‖m' l‖) + ε * ∏ l : Fin k, ‖m' l‖ with hC
    have hmv := (convex_closedBall y ‖e‖).norm_image_sub_le_of_norm_fderiv_le
      (f := fun y' => G y' - A y') (C := C)
      (fun y' _ => (hGd y').sub (A.differentiableAt)) (fun y' hy' => ?_)
      (mem_closedBall_self (norm_nonneg e)) (show y + e ∈ closedBall y ‖e‖ by
        rw [mem_closedBall_iff_norm]; simp)
    · have e1 : s8f_dpF (k + 1) m g y = G (y + e) - G y := rfl
      have e2 : iteratedFDeriv ℝ (k + 1) g y m = A e := by
        rw [iteratedFDeriv_succ_apply_right]
      rw [e1, e2]
      have e3 : (G (y + e) - A (y + e)) - (G y - A y) = G (y + e) - G y - A e := by
        rw [map_add]; abel
      simp only [add_sub_cancel_left] at hmv
      rw [e3] at hmv
      refine hmv.trans ?_
      rw [hprod, hC]
      have h2 : (2 : ℝ) ^ k ≤ 2 ^ (k + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
      have hε2 : (2 ^ k * ε * ∏ l : Fin k, ‖m' l‖) + ε * ∏ l : Fin k, ‖m' l‖ ≤
          2 ^ (k + 1) * ε * ∏ l : Fin k, ‖m' l‖ := by
        have : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
        have h3 : 0 ≤ ε * ∏ l : Fin k, ‖m' l‖ := mul_nonneg hε hP
        nlinarith [pow_succ (2 : ℝ) k]
      calc ((2 ^ k * ε * ∏ l : Fin k, ‖m' l‖) + ε * ∏ l : Fin k, ‖m' l‖) * ‖e‖
          ≤ (2 ^ (k + 1) * ε * ∏ l : Fin k, ‖m' l‖) * ‖e‖ :=
            mul_le_mul_of_nonneg_right hε2 (norm_nonneg e)
        _ = _ := by ring
    · -- the derivative bound on the segment
      rw [mem_closedBall_iff_norm] at hy'
      have hfd : fderiv ℝ (fun y' => G y' - A y') y' = fderiv ℝ G y' - A := by
        exact ((hGd y').hasFDerivAt.sub A.hasFDerivAt).fderiv
      rw [hfd, hG, s8f_dpF_fderiv k m' hdg]
      have hT := ih (fderiv ℝ g) hDg m' y' (∑ l : Fin k, ‖m' l‖) ε le_rfl hε (fun y1 y2 h1 h2 => by
        rw [s8f_norm_iter_sub]
        refine hmod y1 y2 ?_ ?_
        · calc ‖y1 - y‖ = ‖(y1 - y') + (y' - y)‖ := by congr 1; abel
            _ ≤ ‖y1 - y'‖ + ‖y' - y‖ := norm_add_le _ _
            _ ≤ R := by rw [hsum] at hR; linarith
        · calc ‖y2 - y‖ = ‖(y2 - y') + (y' - y)‖ := by congr 1; abel
            _ ≤ ‖y2 - y'‖ + ‖y' - y‖ := norm_add_le _ _
            _ ≤ R := by rw [hsum] at hR; linarith)
      have hT2 : ‖(iteratedFDeriv ℝ k (fderiv ℝ g) y' m' - A)‖ ≤ ε * ∏ l : Fin k, ‖m' l‖ := by
        have hcm : iteratedFDeriv ℝ k (fderiv ℝ g) y' m' - A =
            (iteratedFDeriv ℝ k (fderiv ℝ g) y' - iteratedFDeriv ℝ k (fderiv ℝ g) y) m' := by
          rw [hA]; rfl
        rw [hcm]
        refine ((iteratedFDeriv ℝ k (fderiv ℝ g) y' - iteratedFDeriv ℝ k (fderiv ℝ g) y).le_opNorm m').trans ?_
        refine mul_le_mul_of_nonneg_right ?_ hP
        rw [s8f_norm_iter_sub]
        refine hmod y' y ?_ (by simp [hR.trans' (le_refl _)] ; exact (by
          rw [hsum] at hR; linarith [hS0, norm_nonneg e] : (0 : ℝ) ≤ R))
        rw [hsum] at hR; linarith
      calc ‖s8f_dpF k m' (fderiv ℝ g) y' - A‖
          = ‖(s8f_dpF k m' (fderiv ℝ g) y' - iteratedFDeriv ℝ k (fderiv ℝ g) y' m') +
              (iteratedFDeriv ℝ k (fderiv ℝ g) y' m' - A)‖ := by congr 1; abel
        _ ≤ _ := (norm_add_le _ _).trans (add_le_add hT hT2)

theorem s8f_partial_le_of_dp {k : ℕ} {g : Euc d → ℝ} (hg : ContDiff ℝ k g) (idx : Fin k → Fin d) (x : Euc d)
    {B h0 : ℝ} (hh0 : 0 < h0)
    (hB : ∀ h : ℝ, 0 < h → h ≤ h0 →
      |s8f_dpF k (fun l => h • (EuclideanSpace.single (idx l) (1 : ℝ) : Euc d)) g x| ≤ B * h ^ k) :
    |partialDeriv idx g x| ≤ B := by
  by_contra hcon
  push Not at hcon
  set ε : ℝ := (|partialDeriv idx g x| - B) / 2 ^ (k + 1) with hε
  have hε0 : 0 < ε := div_pos (sub_pos.2 hcon) (by positivity)
  have hcont : ContinuousAt (iteratedFDeriv ℝ k g) x :=
    (hg.continuous_iteratedFDeriv (le_refl _)).continuousAt
  obtain ⟨δ, hδ, hδ'⟩ := Metric.continuousAt_iff.1 hcont (ε / 2) (by positivity)
  set h : ℝ := min h0 (δ / (2 * ((k : ℝ) + 1))) with hh
  have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hhpos : 0 < h := lt_min hh0 (by positivity)
  have hh1 : h ≤ h0 := min_le_left _ _
  have hh2 : h ≤ δ / (2 * ((k : ℝ) + 1)) := min_le_right _ _
  have hhk : (k : ℝ) * h ≤ δ / 2 := by
    have h3 : ((k : ℝ) + 1) * h ≤ δ / 2 := by
      calc ((k : ℝ) + 1) * h ≤ ((k : ℝ) + 1) * (δ / (2 * ((k : ℝ) + 1))) :=
            mul_le_mul_of_nonneg_left hh2 hk1.le
        _ = δ / 2 := by field_simp
    nlinarith
  set m : Fin k → Euc d := fun l => h • (EuclideanSpace.single (idx l) (1 : ℝ) : Euc d) with hm
  have hnorm : ∀ l, ‖m l‖ = h := fun l => by
    simp [hm, norm_smul, abs_of_pos hhpos]
  have hsum : ∑ l, ‖m l‖ = k * h := by simp [hnorm]
  have hprod : ∏ l, ‖m l‖ = h ^ k := by simp [hnorm]
  have htay := s8f_dpF_taylor k g hg m x (δ / 2) ε (by rw [hsum]; exact hhk) hε0.le (fun y1 y2 h1 h2 => by
    have a1 := hδ' (x := y1) (by rw [dist_eq_norm]; linarith)
    have a2 := hδ' (x := y2) (by rw [dist_eq_norm]; linarith)
    rw [dist_eq_norm] at a1 a2
    calc ‖iteratedFDeriv ℝ k g y1 - iteratedFDeriv ℝ k g y2‖
        = ‖(iteratedFDeriv ℝ k g y1 - iteratedFDeriv ℝ k g x) -
            (iteratedFDeriv ℝ k g y2 - iteratedFDeriv ℝ k g x)‖ := by congr 1; abel
      _ ≤ ‖iteratedFDeriv ℝ k g y1 - iteratedFDeriv ℝ k g x‖ +
            ‖iteratedFDeriv ℝ k g y2 - iteratedFDeriv ℝ k g x‖ := norm_sub_le _ _
      _ ≤ ε := by linarith)
  have hev : iteratedFDeriv ℝ k g x m = h ^ k * partialDeriv idx g x := by
    unfold partialDeriv
    have := (iteratedFDeriv ℝ k g x).map_smul_univ (fun _ => h)
      (fun l => (EuclideanSpace.single (idx l) (1 : ℝ) : Euc d))
    simpa [Finset.prod_const, hm] using this
  have hdp := hB h hhpos hh1
  rw [hprod] at htay
  have hhk0 : 0 < h ^ k := pow_pos hhpos k
  have key : h ^ k * |partialDeriv idx g x| ≤ B * h ^ k + 2 ^ k * ε * h ^ k := by
    have e1 : h ^ k * |partialDeriv idx g x| = |iteratedFDeriv ℝ k g x m| := by
      rw [hev, abs_mul, abs_of_pos hhk0]
    rw [e1]
    have e2 : |iteratedFDeriv ℝ k g x m| ≤ |s8f_dpF k m g x| +
        |s8f_dpF k m g x - iteratedFDeriv ℝ k g x m| := by
      have := abs_sub (s8f_dpF k m g x) (s8f_dpF k m g x - iteratedFDeriv ℝ k g x m)
      have e3 : s8f_dpF k m g x - (s8f_dpF k m g x - iteratedFDeriv ℝ k g x m) =
          iteratedFDeriv ℝ k g x m := by ring
      rw [e3] at this
      exact this
    rw [Real.norm_eq_abs] at htay
    linarith
  have key2 : |partialDeriv idx g x| ≤ B + 2 ^ k * ε := by
    have : h ^ k * |partialDeriv idx g x| ≤ h ^ k * (B + 2 ^ k * ε) := by nlinarith
    exact le_of_mul_le_mul_left this hhk0
  have h2k : (2 : ℝ) ^ (k + 1) = 2 * 2 ^ k := by ring
  have : 2 ^ k * ε = (|partialDeriv idx g x| - B) / 2 := by
    rw [hε, h2k]; field_simp
  linarith

end HRS.MS.Wad
