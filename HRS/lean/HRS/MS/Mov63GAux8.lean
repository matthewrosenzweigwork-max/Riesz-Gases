import HRS.MS.Mov63GAux7

/-!
# S6.3, packet N8 (part 8): interpolation for the a priori growth of the derivatives of `Q`

Namespace `HRS.MS.Mov63`, prefix `mng_`.  The borderline Gaussian growth `exp((βq/4)‖x‖²)` of the crude bound for `D^kQ` is improved,
order by order, to `exp(κ_k ‖x‖²)` with `κ_k < βq/4`, using `Q` bounded and the local interpolation inequality

`‖D^{n+1} g (x)‖ ≤ 2 sup_{B(x,r)} ‖D^n g‖ / r + r sup_{B(x,r)} ‖D^{n+2} g‖`   (`mng_interp_norm`),

with `r = exp(-γ‖x‖²)` (`mng_interp_exp`).
-/

noncomputable section

open Filter Topology Set MeasureTheory
open scoped RealInnerProductSpace

namespace HRS.MS.Mov63

open HRS

variable {d : ℕ}

/-- One-dimensional interpolation: `|φ'(0)| ≤ 2A/r + B r`. -/
lemma mng_taylor1 {φ φ' φ'' : ℝ → ℝ} {r A B : ℝ} (hr : 0 < r)
    (h1 : ∀ s ∈ Icc 0 r, HasDerivAt φ (φ' s) s) (h2 : ∀ s ∈ Icc 0 r, HasDerivAt φ' (φ'' s) s)
    (hA : ∀ s ∈ Icc 0 r, |φ s| ≤ A) (hB : ∀ s ∈ Icc 0 r, |φ'' s| ≤ B) :
    |φ' 0| ≤ 2 * A / r + B * r := by
  have h0 : (0 : ℝ) ∈ Icc 0 r := ⟨le_rfl, hr.le⟩
  have hrI : r ∈ Icc 0 r := ⟨hr.le, le_rfl⟩
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0 h0)
  -- |φ' s - φ' 0| ≤ B r
  have hd1 : ∀ s ∈ Icc 0 r, |φ' s - φ' 0| ≤ B * r := by
    intro s hs
    have := (convex_Icc (0 : ℝ) r).norm_image_sub_le_of_norm_hasDerivWithin_le (f := φ') (f' := φ'') (C := B)
      (fun y hy => (h2 y hy).hasDerivWithinAt) (fun y hy => by rw [Real.norm_eq_abs]; exact hB y hy) h0 hs
    rw [Real.norm_eq_abs, Real.norm_eq_abs, sub_zero] at this
    calc |φ' s - φ' 0| ≤ B * |s| := this
      _ ≤ B * r := mul_le_mul_of_nonneg_left (by rw [abs_of_nonneg hs.1]; exact hs.2) hB0
  -- ψ(s) = φ s - s φ' 0
  have hd2 : ∀ s ∈ Icc 0 r, HasDerivAt (fun s => φ s - s * φ' 0) (φ' s - φ' 0) s := by
    intro s hs
    have := (h1 s hs).sub ((hasDerivAt_id s).mul_const (φ' 0))
    exact this.congr_deriv (by simp)
  have hm := (convex_Icc (0 : ℝ) r).norm_image_sub_le_of_norm_hasDerivWithin_le (f := fun s => φ s - s * φ' 0)
    (f' := fun s => φ' s - φ' 0) (C := B * r) (fun y hy => (hd2 y hy).hasDerivWithinAt)
    (fun y hy => by rw [Real.norm_eq_abs]; exact hd1 y hy) h0 hrI
  simp only [Real.norm_eq_abs, sub_zero, abs_of_pos hr, zero_mul] at hm
  have hA0 := hA 0 h0
  have hAr := hA r hrI
  have e1 : -(r * φ' 0) = (φ 0 - φ r) + (φ r - r * φ' 0 - φ 0) := by ring
  have h3 : |r * φ' 0| ≤ 2 * A + B * r * r := by
    have := abs_add_le (φ 0 - φ r) (φ r - r * φ' 0 - φ 0)
    rw [← e1, abs_neg] at this
    have h4 : |φ 0 - φ r| ≤ |φ 0| + |φ r| := abs_sub _ _
    linarith
  rw [abs_mul, abs_of_pos hr] at h3
  rw [div_add' _ _ _ hr.ne', le_div_iff₀ hr]
  nlinarith

lemma mng_line_iter {g : Euc d → ℝ} {N : ℕ} (hg : ContDiff ℝ N g) {n : ℕ} (hn : n < N) (x e : Euc d)
    (m : Fin n → Euc d) (s : ℝ) :
    HasDerivAt (fun s : ℝ => iteratedFDeriv ℝ n g (x + s • e) m)
      (iteratedFDeriv ℝ (n + 1) g (x + s • e) (Fin.cons e m)) s := by
  have hd : DifferentiableAt ℝ (iteratedFDeriv ℝ n g) (x + s • e) :=
    hg.differentiable_iteratedFDeriv (by exact_mod_cast hn) _
  have h1 : HasFDerivAt (fun y => iteratedFDeriv ℝ n g y m)
      ((ContinuousMultilinearMap.apply ℝ (fun _ : Fin n => Euc d) ℝ m).comp
        (fderiv ℝ (iteratedFDeriv ℝ n g) (x + s • e))) (x + s • e) :=
    (ContinuousMultilinearMap.apply ℝ (fun _ : Fin n => Euc d) ℝ m).hasFDerivAt.comp _ hd.hasFDerivAt
  have h2 : HasDerivAt (fun s : ℝ => x + s • e) e s := by
    simpa using ((hasDerivAt_id s).smul_const e).const_add x
  have := h1.comp_hasDerivAt s h2
  rw [iteratedFDeriv_succ_apply_left]
  exact this.congr_deriv (by simp [Fin.tail_cons])

/-- **Local interpolation inequality** for the operator norms of iterated derivatives. -/
lemma mng_interp_norm {g : Euc d → ℝ} {n : ℕ} (hg : ContDiff ℝ (n + 2 : ℕ) g) (x : Euc d) {r A B : ℝ}
    (hr : 0 < r) (hA : ∀ y, ‖y - x‖ ≤ r → ‖iteratedFDeriv ℝ n g y‖ ≤ A)
    (hB : ∀ y, ‖y - x‖ ≤ r → ‖iteratedFDeriv ℝ (n + 2) g y‖ ≤ B) :
    ‖iteratedFDeriv ℝ (n + 1) g x‖ ≤ 2 * A / r + B * r := by
  have hA0 : 0 ≤ A := (norm_nonneg _).trans (hA x (by simp [hr.le]))
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB x (by simp [hr.le]))
  refine (iteratedFDeriv ℝ (n + 1) g x).opNorm_le_bound (by positivity) fun h => ?_
  by_cases h0 : h 0 = 0
  · have : iteratedFDeriv ℝ (n + 1) g x h = 0 := by
      apply (iteratedFDeriv ℝ (n + 1) g x).map_coord_zero 0 h0
    rw [this, norm_zero]
    exact mul_nonneg (by positivity) (Finset.prod_nonneg fun _ _ => norm_nonneg _)
  · set ρ : ℝ := ‖h 0‖ with hρ
    have hρpos : 0 < ρ := norm_pos_iff.2 h0
    set m : Fin n → Euc d := Fin.tail h with hm
    have hh : h = Fin.cons (h 0) m := (Fin.cons_self_tail h).symm
    set r' : ℝ := r / ρ with hr'
    have hr'pos : 0 < r' := by positivity
    have hline : ∀ s ∈ Icc 0 r', ‖x + s • h 0 - x‖ ≤ r := by
      intro s hs
      rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg hs.1, ← hρ]
      calc s * ρ ≤ r' * ρ := mul_le_mul_of_nonneg_right hs.2 hρpos.le
        _ = r := by rw [hr']; field_simp
    set P : ℝ := ∏ a : Fin n, ‖m a‖ with hP
    have hP0 : 0 ≤ P := Finset.prod_nonneg fun _ _ => norm_nonneg _
    have hφ1 : ∀ s ∈ Icc 0 r', HasDerivAt (fun s : ℝ => iteratedFDeriv ℝ n g (x + s • h 0) m)
        (iteratedFDeriv ℝ (n + 1) g (x + s • h 0) (Fin.cons (h 0) m)) s := fun s _ =>
      mng_line_iter hg (by omega) x (h 0) m s
    have hφ2 : ∀ s ∈ Icc 0 r', HasDerivAt (fun s : ℝ => iteratedFDeriv ℝ (n + 1) g (x + s • h 0) (Fin.cons (h 0) m))
        (iteratedFDeriv ℝ (n + 2) g (x + s • h 0) (Fin.cons (h 0) (Fin.cons (h 0) m))) s := fun s _ =>
      mng_line_iter hg (by omega) x (h 0) (Fin.cons (h 0) m) s
    have hbA : ∀ s ∈ Icc 0 r', |iteratedFDeriv ℝ n g (x + s • h 0) m| ≤ A * P := by
      intro s hs
      rw [← Real.norm_eq_abs]
      refine ((iteratedFDeriv ℝ n g (x + s • h 0)).le_opNorm m).trans ?_
      exact mul_le_mul_of_nonneg_right (hA _ (hline s hs)) hP0
    have hbB : ∀ s ∈ Icc 0 r', |iteratedFDeriv ℝ (n + 2) g (x + s • h 0) (Fin.cons (h 0) (Fin.cons (h 0) m))| ≤
        B * ρ ^ 2 * P := by
      intro s hs
      rw [← Real.norm_eq_abs]
      refine ((iteratedFDeriv ℝ (n + 2) g (x + s • h 0)).le_opNorm _).trans ?_
      have : ∏ a : Fin (n + 2), ‖(Fin.cons (h 0) (Fin.cons (h 0) m) : Fin (n + 2) → Euc d) a‖ = ρ ^ 2 * P := by
        rw [Fin.prod_univ_succ, Fin.prod_univ_succ]
        simp only [Fin.cons_zero, Fin.cons_succ, hρ, hP]
        ring
      rw [this, ← mul_assoc]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hB _ (hline s hs)) (sq_nonneg ρ)) hP0
    have key := mng_taylor1 hr'pos hφ1 hφ2 hbA hbB
    simp only [zero_smul, add_zero] at key
    rw [← hh] at key
    have e1 : ∏ a : Fin (n + 1), ‖h a‖ = ρ * P := by
      rw [Fin.prod_univ_succ]; simp [hρ, hP, hm, Fin.tail]
    rw [e1, ← Real.norm_eq_abs] at *
    calc ‖iteratedFDeriv ℝ (n + 1) g x h‖ ≤ 2 * (A * P) / r' + B * ρ ^ 2 * P * r' := key
      _ = (2 * A / r + B * r) * (ρ * P) := by rw [hr']; field_simp
lemma mng_exp_shift {k δ : ℝ} (hk : 0 ≤ k) (hδ : 0 < δ) (x y : Euc d) (hy : ‖y - x‖ ≤ 1) :
    Real.exp (k * ‖y‖ ^ 2) ≤ Real.exp (k ^ 2 / δ + k) * Real.exp ((k + δ) * ‖x‖ ^ 2) := by
  rw [← Real.exp_add]
  refine Real.exp_le_exp.2 ?_
  have h1 : ‖y‖ ≤ ‖x‖ + 1 := by
    have := norm_le_norm_add_norm_sub' y x
    linarith
  have h2 : ‖y‖ ^ 2 ≤ (‖x‖ + 1) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
  have h3 : 2 * k * ‖x‖ ≤ δ * ‖x‖ ^ 2 + k ^ 2 / δ := by
    have : 0 ≤ (δ * ‖x‖ - k) ^ 2 / δ := by positivity
    have e : (δ * ‖x‖ - k) ^ 2 / δ = δ * ‖x‖ ^ 2 - 2 * k * ‖x‖ + k ^ 2 / δ := by field_simp; ring
    linarith
  nlinarith [mul_le_mul_of_nonneg_left h2 hk]

lemma mng_interp_exp (n : ℕ) {C1 C2 k0 k1 δ : ℝ} (hC1 : 0 ≤ C1) (hC2 : 0 ≤ C2) (hk0 : 0 ≤ k0) (hk01 : k0 ≤ k1)
    (hδ : 0 < δ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ g : Euc d → ℝ, ContDiff ℝ (n + 2 : ℕ) g →
      (∀ y, ‖iteratedFDeriv ℝ n g y‖ ≤ C1 * Real.exp (k0 * ‖y‖ ^ 2)) →
      (∀ y, ‖iteratedFDeriv ℝ (n + 2) g y‖ ≤ C2 * Real.exp (k1 * ‖y‖ ^ 2)) →
      ∀ x, ‖iteratedFDeriv ℝ (n + 1) g x‖ ≤ C * Real.exp (((k0 + k1) / 2 + δ) * ‖x‖ ^ 2) := by
  have hk1 : 0 ≤ k1 := hk0.trans hk01
  set c0 : ℝ := Real.exp (k0 ^ 2 / δ + k0) with hc0
  set c1 : ℝ := Real.exp (k1 ^ 2 / δ + k1) with hc1
  refine ⟨2 * C1 * c0 + C2 * c1, by positivity, fun g hg h1 h2 x => ?_⟩
  set γ : ℝ := (k1 - k0) / 2 with hγ
  have hγ0 : 0 ≤ γ := by rw [hγ]; linarith
  set r : ℝ := Real.exp (-γ * ‖x‖ ^ 2) with hr
  have hrpos : 0 < r := Real.exp_pos _
  have hr1 : r ≤ 1 := by
    rw [hr, ← Real.exp_zero]
    exact Real.exp_le_exp.2 (by nlinarith [sq_nonneg ‖x‖])
  have hA : ∀ y, ‖y - x‖ ≤ r → ‖iteratedFDeriv ℝ n g y‖ ≤ C1 * c0 * Real.exp ((k0 + δ) * ‖x‖ ^ 2) := by
    intro y hy
    calc ‖iteratedFDeriv ℝ n g y‖ ≤ C1 * Real.exp (k0 * ‖y‖ ^ 2) := h1 y
      _ ≤ C1 * (c0 * Real.exp ((k0 + δ) * ‖x‖ ^ 2)) :=
          mul_le_mul_of_nonneg_left (mng_exp_shift hk0 hδ x y (hy.trans hr1)) hC1
      _ = _ := by ring
  have hB : ∀ y, ‖y - x‖ ≤ r → ‖iteratedFDeriv ℝ (n + 2) g y‖ ≤ C2 * c1 * Real.exp ((k1 + δ) * ‖x‖ ^ 2) := by
    intro y hy
    calc ‖iteratedFDeriv ℝ (n + 2) g y‖ ≤ C2 * Real.exp (k1 * ‖y‖ ^ 2) := h2 y
      _ ≤ C2 * (c1 * Real.exp ((k1 + δ) * ‖x‖ ^ 2)) :=
          mul_le_mul_of_nonneg_left (mng_exp_shift hk1 hδ x y (hy.trans hr1)) hC2
      _ = _ := by ring
  have key := mng_interp_norm hg x hrpos hA hB
  refine key.trans ?_
  have e1 : 2 * (C1 * c0 * Real.exp ((k0 + δ) * ‖x‖ ^ 2)) / r =
      2 * C1 * c0 * Real.exp (((k0 + k1) / 2 + δ) * ‖x‖ ^ 2) := by
    rw [hr, div_eq_mul_inv, ← Real.exp_neg]
    have : Real.exp ((k0 + δ) * ‖x‖ ^ 2) * Real.exp (-(-γ * ‖x‖ ^ 2)) =
        Real.exp (((k0 + k1) / 2 + δ) * ‖x‖ ^ 2) := by
      rw [← Real.exp_add]; congr 1; rw [hγ]; ring
    calc 2 * (C1 * c0 * Real.exp ((k0 + δ) * ‖x‖ ^ 2)) * Real.exp (-(-γ * ‖x‖ ^ 2))
        = 2 * C1 * c0 * (Real.exp ((k0 + δ) * ‖x‖ ^ 2) * Real.exp (-(-γ * ‖x‖ ^ 2))) := by ring
      _ = _ := by rw [this]
  have e2 : C2 * c1 * Real.exp ((k1 + δ) * ‖x‖ ^ 2) * r = C2 * c1 * Real.exp (((k0 + k1) / 2 + δ) * ‖x‖ ^ 2) := by
    rw [hr]
    have : Real.exp ((k1 + δ) * ‖x‖ ^ 2) * Real.exp (-γ * ‖x‖ ^ 2) = Real.exp (((k0 + k1) / 2 + δ) * ‖x‖ ^ 2) := by
      rw [← Real.exp_add]; congr 1; rw [hγ]; ring
    calc C2 * c1 * Real.exp ((k1 + δ) * ‖x‖ ^ 2) * Real.exp (-γ * ‖x‖ ^ 2)
        = C2 * c1 * (Real.exp ((k1 + δ) * ‖x‖ ^ 2) * Real.exp (-γ * ‖x‖ ^ 2)) := by ring
      _ = _ := by rw [this]
  rw [e1, e2]
  linarith [Real.exp_pos (((k0 + k1) / 2 + δ) * ‖x‖ ^ 2)]

lemma mng_growth_iter {Qf : ℝ → Euc d → ℝ} {N : ℕ} (hQ : ∀ t, ContDiff ℝ (N + 1 : ℕ) (Qf t)) {MQ K1 δ : ℝ}
    (hK1 : 0 < K1) (hδ0 : 0 < δ) (hδ : 2 * δ ≤ K1 * (1 / 2 : ℝ) ^ N)
    (hbd0 : ∀ t, 0 ≤ t → ∀ y, ‖iteratedFDeriv ℝ 0 (Qf t) y‖ ≤ MQ)
    (hcrude : ∀ i, 1 ≤ i → i ≤ N + 1 → ∃ Cc : ℝ, 0 ≤ Cc ∧ ∀ t, 0 ≤ t → ∀ y,
      ‖iteratedFDeriv ℝ i (Qf t) y‖ ≤ Cc * Real.exp (K1 * ‖y‖ ^ 2)) :
    ∀ i ≤ N, ∃ C : ℝ, 0 ≤ C ∧ ∀ t, 0 ≤ t → ∀ y,
      ‖iteratedFDeriv ℝ i (Qf t) y‖ ≤ C * Real.exp ((K1 + 2 * δ) * (1 - (1 / 2 : ℝ) ^ i) * ‖y‖ ^ 2) := by
  intro i
  induction i with
  | zero =>
    intro _
    have hMQ : 0 ≤ MQ := (norm_nonneg _).trans (hbd0 0 le_rfl 0)
    exact ⟨MQ, hMQ, fun t ht y => by simpa using hbd0 t ht y⟩
  | succ i ih =>
    intro hi
    obtain ⟨C1, hC1, h1⟩ := ih (by omega)
    obtain ⟨C2, hC2, h2⟩ := hcrude (i + 2) (by omega) (by omega)
    set k0 : ℝ := (K1 + 2 * δ) * (1 - (1 / 2 : ℝ) ^ i) with hk0
    have hp : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ i := by positivity
    have hp1 : (1 / 2 : ℝ) ^ i ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    have hk0nn : 0 ≤ k0 := by rw [hk0]; apply mul_nonneg (by linarith) (by linarith)
    have hpN : (1 / 2 : ℝ) ^ N ≤ (1 / 2 : ℝ) ^ i := pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    have hk01 : k0 ≤ K1 := by
      rw [hk0]
      nlinarith [mul_le_mul_of_nonneg_left hpN hK1.le]
    obtain ⟨C, hC0, hC⟩ := mng_interp_exp (d := d) i hC1 hC2 hk0nn hk01 hδ0
    refine ⟨C, hC0, fun t ht y => ?_⟩
    have := hC (Qf t) ((hQ t).of_le (by exact_mod_cast (by omega : i + 2 ≤ N + 1)))
      (fun z => by rw [hk0] at *; exact h1 t ht z) (fun z => h2 t ht z) y
    have e : (K1 + 2 * δ) * (1 - (1 / 2 : ℝ) ^ (i + 1)) = (k0 + K1) / 2 + δ := by
      rw [hk0, pow_succ]; ring
    rw [e]
    exact this


end HRS.MS.Mov63

end
