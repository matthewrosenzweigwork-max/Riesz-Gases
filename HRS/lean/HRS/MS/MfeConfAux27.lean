import HRS.MS.MfeConfAux26

/-!
# S.B.1, packet F3 (part 8): calculus on the configuration space

* `sb1dEn`, `sb1_hasFDerivAt_En`: the Fréchet derivative of the energy `En(X) = sb1En k ρ X` of a regular kernel;
  `sb1_dEn_single`: its value on `Pi.single i e` is `sb1dE k G N X i e = N⁻² ∑_{j≠i} ∇k(x_i-x_j)·e - N⁻¹ ∇G(x_i)·e`.
* `sb1_cfg_int_of_bound`: a measurable function bounded by `K ∏_l (1+|x_l|)^{-(d+2)}` is integrable on `(ℝ^d)^N`.
* `sb1_ibp_cfg`: the integration by parts in the variable `x_i`, component `kk`
  `∫ E ∏_{l≠i}ρ(x_l) ∂_kk J_kk(x_i) = βN ∫ E ∏_{l≠i}ρ(x_l) J_kk(x_i) ∂_{(i,kk)}En`, `E = e^{-βN En}`.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.MfeConf

variable {d N : ℕ}

/-- the coordinate projection `(ℝ^d)^N → ℝ^d` -/
def sb1pr (d N : ℕ) (i : Fin N) : Whole.EucConfig d N →L[ℝ] Euc d := ContinuousLinearMap.proj i

/-- `∂_{(i,e)} En` -/
def sb1dE (k G : Euc d → ℝ) (N : ℕ) (X : Whole.EucConfig d N) (i : Fin N) (e : Euc d) : ℝ :=
  (1 / (N : ℝ) ^ 2) * ∑ j ∈ Finset.univ.erase i, fderiv ℝ k (X i - X j) e - (1 / (N : ℝ)) * fderiv ℝ G (X i) e

/-- the Fréchet derivative of the energy on the configuration space -/
def sb1dEn (k G : Euc d → ℝ) (N : ℕ) (X : Whole.EucConfig d N) : Whole.EucConfig d N →L[ℝ] ℝ :=
  (1 / (2 * (N : ℝ) ^ 2)) • ∑ i, ∑ j ∈ Finset.univ.erase i,
      (fderiv ℝ k (X i - X j)).comp (sb1pr d N i - sb1pr d N j)
    - (1 / (N : ℝ)) • ∑ i, (fderiv ℝ G (X i)).comp (sb1pr d N i)

section Cfg

variable {k : Euc d → ℝ} {Lg : ℝ} {ρ : Euc d → ℝ} {Cρ M1 s : ℝ}

theorem sb1_hasFDerivAt_En (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (hk : Sb1KerU d s k) (hR : Sb1KerR d k Lg)
    (R : Sb1Rho ρ Cρ M1) (X : Whole.EucConfig d N) :
    HasFDerivAt (sb1En k ρ : Whole.EucConfig d N → ℝ) (sb1dEn k (sb1G k ρ) N X) X := by
  have hp : ∀ i j : Fin N, HasFDerivAt (fun X : Whole.EucConfig d N => k (X i - X j))
      ((fderiv ℝ k (X i - X j)).comp (sb1pr d N i - sb1pr d N j)) X := fun i j =>
    (hR.diff (X i - X j)).hasFDerivAt.comp X
      ((sb1pr d N i).hasFDerivAt.sub
        (sb1pr d N j).hasFDerivAt)
  have hg : ∀ i : Fin N, HasFDerivAt (fun X : Whole.EucConfig d N => sb1G k ρ (X i))
      ((fderiv ℝ (sb1G k ρ) (X i)).comp (sb1pr d N i)) X := fun i => by
    have h1 : HasFDerivAt (sb1G k ρ) (fderiv ℝ (sb1G k ρ) (X i)) (sb1pr d N i X) :=
      (sb1_hasFDerivAt_G hd hs0 hsd hk hR R (X i)).differentiableAt.hasFDerivAt
    exact h1.comp X (sb1pr d N i).hasFDerivAt
  have hS := HasFDerivAt.fun_sum (u := (Finset.univ : Finset (Fin N))) (fun i _ =>
    HasFDerivAt.fun_sum (u := Finset.univ.erase i) (fun j _ => hp i j))
  have hG := HasFDerivAt.fun_sum (u := (Finset.univ : Finset (Fin N))) (fun i _ => hg i)
  exact ((hS.const_mul (1 / (2 * (N : ℝ) ^ 2))).fun_sub (hG.const_mul (1 / (N : ℝ)))).add_const ((1 / 2) * sb1c k ρ)

theorem sb1_dEn_single (hR : Sb1KerR d k Lg) (G : Euc d → ℝ) (X : Whole.EucConfig d N) (i : Fin N) (e : Euc d) :
    sb1dEn k G N X (Pi.single i e) = sb1dE k G N X i e := by
  have hproj : ∀ a : Fin N, (sb1pr d N a)
      (Pi.single i e : Whole.EucConfig d N) = if a = i then e else 0 := by
    intro a
    by_cases h : a = i
    · subst h; simp [sb1pr]
    · simp [sb1pr, h, Pi.single_eq_of_ne h]
  set Fk : Fin N → Fin N → ℝ := fun a b => fderiv ℝ k (X a - X b) e with hFk
  have h1 : ∀ a b : Fin N, fderiv ℝ k (X a - X b) ((if a = i then e else 0) - (if b = i then e else 0)) =
      (if a = i then Fk a b else 0) - (if b = i then Fk a b else 0) := by
    intro a b
    by_cases ha : a = i <;> by_cases hb : b = i <;> simp [ha, hb, hFk, map_sub]
  have hA : ∑ a : Fin N, ∑ b ∈ Finset.univ.erase a, (if a = i then Fk a b else 0) =
      ∑ b ∈ Finset.univ.erase i, Fk i b := by
    rw [Finset.sum_eq_single i]
    · simp
    · intro a _ ha
      simp [ha]
    · simp
  have hB : ∑ a : Fin N, ∑ b ∈ Finset.univ.erase a, (if b = i then Fk a b else 0) =
      ∑ a ∈ Finset.univ.erase i, Fk a i := by
    rw [MP.SelfSimP4Impl.p4k_sum_swap (fun a b => if b = i then Fk a b else 0)]
    rw [Finset.sum_eq_single i]
    · simp
    · intro b _ hb
      simp [hb]
    · simp
  have hodd : ∑ a ∈ Finset.univ.erase i, Fk a i = -∑ b ∈ Finset.univ.erase i, Fk i b := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp only [hFk]
    rw [← neg_sub (X i) (X a)]
    exact sb1_fderiv_odd hR.diff hR.even _ _
  have hG1 : ∑ a : Fin N, fderiv ℝ G (X a) (if a = i then e else 0) = fderiv ℝ G (X i) e := by
    rw [Finset.sum_eq_single i]
    · simp
    · intro a _ ha
      simp [ha]
    · simp
  unfold sb1dEn sb1dE
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.comp_apply, hproj, smul_eq_mul]
  simp_rw [h1]
  simp only [Finset.sum_sub_distrib]
  rw [hA, hB, hodd, hG1]
  simp only [hFk]
  ring

end Cfg

/-! ### Product bounds on the configuration space -/

/-- a measurable function bounded by `K ∏_l (1+|x_l|)^{-(d+2)}` is integrable -/
theorem sb1_cfg_int_of_bound (hd : 1 ≤ d) {F : Whole.EucConfig d N → ℝ} (hF : AEStronglyMeasurable F volume) {K : ℝ}
    (hb : ∀ X, |F X| ≤ K * ∏ l, sb1w ((d : ℝ) + 2) (X l)) : Integrable F := by
  have h : Integrable (fun X : Whole.EucConfig d N => ∏ l, sb1w ((d : ℝ) + 2) (X l)) volume :=
    Integrable.fintype_prod (fun _ => sb1w_int hd (p := (d : ℝ) + 2) (by linarith))
  exact (h.const_mul K).mono' hF (Eventually.of_forall fun X => by rw [Real.norm_eq_abs]; exact hb X)

section Bound

variable {D : Whole.WholeDyn d} {T C B C3 : ℝ} {ρ : ℝ → Euc d → ℝ}

theorem sb1_prod_erase_le (H : Sb1Tr3 D T C B C3 ρ) {r : ℝ} (hr : r ∈ Set.Icc (0 : ℝ) T) (i : Fin N)
    (X : Whole.EucConfig d N) :
    ∏ l ∈ Finset.univ.erase i, ρ r (X l) ≤ C3 ^ (N - 1) * ∏ l ∈ Finset.univ.erase i, sb1w ((d : ℝ) + 2) (X l) := by
  calc ∏ l ∈ Finset.univ.erase i, ρ r (X l) ≤ ∏ l ∈ Finset.univ.erase i, (C3 * sb1w ((d : ℝ) + 2) (X l)) :=
        Finset.prod_le_prod₀ (fun l _ => (H.pos r hr _).le) (fun l _ =>
          (le_abs_self _).trans (sb1_rho_absw H hr (X l)))
    _ = C3 ^ (N - 1) * ∏ l ∈ Finset.univ.erase i, sb1w ((d : ℝ) + 2) (X l) := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ i)]
        simp

theorem sb1_prod_le (H : Sb1Tr3 D T C B C3 ρ) {r : ℝ} (hr : r ∈ Set.Icc (0 : ℝ) T) (X : Whole.EucConfig d N) :
    ∏ l, ρ r (X l) ≤ C3 ^ N * ∏ l, sb1w ((d : ℝ) + 2) (X l) := by
  calc ∏ l, ρ r (X l) ≤ ∏ l, (C3 * sb1w ((d : ℝ) + 2) (X l)) :=
        Finset.prod_le_prod₀ (fun l _ => (H.pos r hr _).le) (fun l _ =>
          (le_abs_self _).trans (sb1_rho_absw H hr (X l)))
    _ = C3 ^ N * ∏ l, sb1w ((d : ℝ) + 2) (X l) := by
        rw [Finset.prod_mul_distrib, Finset.prod_const]
        simp

/-- `|φ(x_i)| ∏_{l≠i} ρ(x_l) ≤ a C3^{N-1} ∏_l w₂(x_l)` -/
theorem sb1_cfg_bound (H : Sb1Tr3 D T C B C3 ρ) {r : ℝ} (hr : r ∈ Set.Icc (0 : ℝ) T) (i : Fin N) {φ : Euc d → ℝ}
    {a : ℝ} (ha : 0 ≤ a) (hφ : ∀ y, |φ y| ≤ a * sb1w ((d : ℝ) + 2) y) (X : Whole.EucConfig d N) :
    |φ (X i)| * ∏ l ∈ Finset.univ.erase i, ρ r (X l) ≤ a * C3 ^ (N - 1) * ∏ l, sb1w ((d : ℝ) + 2) (X l) := by
  have h1 := sb1_prod_erase_le H hr i X
  have h2 := hφ (X i)
  have h3 : 0 ≤ ∏ l ∈ Finset.univ.erase i, ρ r (X l) := Finset.prod_nonneg fun l _ => (H.pos r hr _).le
  calc |φ (X i)| * ∏ l ∈ Finset.univ.erase i, ρ r (X l)
      ≤ (a * sb1w ((d : ℝ) + 2) (X i)) * (C3 ^ (N - 1) * ∏ l ∈ Finset.univ.erase i, sb1w ((d : ℝ) + 2) (X l)) :=
        mul_le_mul h2 h1 h3 (mul_nonneg ha (sb1w_pos _ _).le)
    _ = a * C3 ^ (N - 1) * (sb1w ((d : ℝ) + 2) (X i) * ∏ l ∈ Finset.univ.erase i, sb1w ((d : ℝ) + 2) (X l)) := by
        ring
    _ = a * C3 ^ (N - 1) * ∏ l, sb1w ((d : ℝ) + 2) (X l) := by
        rw [Finset.mul_prod_erase Finset.univ (fun l => sb1w ((d : ℝ) + 2) (X l)) (Finset.mem_univ i)]

end Bound

end HRS.MS.MfeConf
