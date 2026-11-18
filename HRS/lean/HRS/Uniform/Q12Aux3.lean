import HRS.Uniform.Q12Aux2

/-!
# Q12, part 3: regularity of the iterated generator, continuity at `t = 0`, sup-norm bound
-/

noncomputable section

open MeasureTheory Filter Topology Set
open HRS HRS.CoercAux

namespace HRS.Uniform.Q12

variable {d : ℕ}

lemma q12_isCk_heatGen {n : ℕ} {ψ : Torus d → ℝ} (h : Torus.IsCk ((n + 2 : ℕ) : WithTop ℕ∞) ψ) :
    Torus.IsCk (n : WithTop ℕ∞) (heatGen ψ) := by
  have h2 : Torus.IsCk 2 ψ := h.of_le (by exact_mod_cast (by omega : 2 ≤ n + 2))
  have hlift : Torus.lift (heatGen ψ) = fun y => (4 * Real.pi ^ 2)⁻¹ *
      ∑ j : Fin d, iteratedFDeriv ℝ 2 (Torus.lift ψ) y
        ![EuclideanSpace.single j (1 : ℝ), EuclideanSpace.single j (1 : ℝ)] := by
    funext y
    have e : Torus.lift (heatGen ψ) y = heatGen ψ (Torus.mk y) := rfl
    rw [e]
    simp only [heatGen]
    rw [PDE.ClassicalAux.laplacian_mk ψ h2 y]
  unfold Torus.IsCk
  rw [hlift]
  refine contDiff_const.mul (ContDiff.sum fun j _ => ?_)
  have hf : ContDiff ℝ ((n + 2 : ℕ) : WithTop ℕ∞) (Torus.lift ψ) := h
  have h3 : ContDiff ℝ (n : WithTop ℕ∞) (iteratedFDeriv ℝ 2 (Torus.lift ψ)) :=
    hf.iteratedFDeriv_right (by push_cast; exact le_of_eq (by ring))
  exact (ContinuousMultilinearMap.apply ℝ (fun _ : Fin 2 => Euc d) ℝ
    ![EuclideanSpace.single j (1 : ℝ), EuclideanSpace.single j (1 : ℝ)]).contDiff.comp h3

lemma q12_isCk_iter {n : ℕ} : ∀ (m : ℕ) {ψ : Torus d → ℝ},
    Torus.IsCk ((n + 2 * m : ℕ) : WithTop ℕ∞) ψ → Torus.IsCk (n : WithTop ℕ∞) ((heatGen)^[m] ψ) := by
  intro m
  induction m with
  | zero => intro ψ h; simpa using h
  | succ m ih =>
    intro ψ h
    rw [Function.iterate_succ_apply]
    apply ih
    have := q12_isCk_heatGen (n := n + 2 * m) (ψ := ψ) (by
      have e : n + 2 * m + 2 = n + 2 * (m + 1) := by ring
      rw [e]; exact h)
    exact this

lemma q12_exists_lip {ψ : Torus d → ℝ} (h : Torus.IsCk 1 ψ) :
    ∃ L : ℝ, 0 ≤ L ∧ KernelGrad.IsLipschitz L ψ :=
  ⟨Torus.cbNorm 1 ψ, PDE.R2Aux.cbNorm_nonneg' 1 ψ, fun x y => (PDE.R2Aux.isLipschitz_of_cbNorm h) x y⟩

lemma q12_tendsto_heatP {ψ : Torus d → ℝ} (hd : 1 ≤ d) (h : Torus.IsCk 1 ψ) (x : Torus d) :
    Tendsto (fun τ => heatP d τ ψ x) (𝓝[>] 0) (𝓝 (ψ x)) := by
  obtain ⟨L, hL, hLip⟩ := q12_exists_lip h
  obtain ⟨M, hM0, hM⟩ := heatP_approx hd
  rw [tendsto_iff_dist_tendsto_zero]
  refine squeeze_zero' (Filter.Eventually.of_forall fun _ => dist_nonneg) ?_ ?_
    (g := fun τ => L * (M * Real.sqrt τ))
  · filter_upwards [Ioo_mem_nhdsGT (show (0:ℝ) < 1 by norm_num)] with τ hτ
    rw [Real.dist_eq, abs_sub_comm]
    exact hM τ hτ.1 hτ.2.le L ψ hL hLip x
  · have : Tendsto (fun τ : ℝ => L * (M * Real.sqrt τ)) (𝓝 0) (𝓝 (L * (M * Real.sqrt 0))) :=
      (continuous_const.mul (continuous_const.mul Real.continuous_sqrt)).tendsto 0
    simp only [Real.sqrt_zero, mul_zero] at this
    exact this.mono_left nhdsWithin_le_nhds

lemma q12_abs_heatP_le {ψ : Torus d → ℝ} (hc : Continuous ψ) {B : ℝ} (hB : ∀ x, |ψ x| ≤ B)
    {t : ℝ} (ht : 0 < t) (x : Torus d) : |heatP d t ψ x| ≤ B := by
  have hK := continuous_heatK (d := d) ht
  have hint1 : Integrable (fun y => heatK d t y * ψ (x - y)) :=
    (hK.mul (hc.comp (continuous_const.sub continuous_id))).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hint0 : Integrable (fun y : Torus d => heatK d t y * B) :=
    (hK.mul continuous_const).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  unfold heatP
  rw [← Real.norm_eq_abs]
  calc ‖∫ y, heatK d t y * ψ (x - y)‖ ≤ ∫ y, heatK d t y * B :=
        norm_integral_le_of_norm_le hint0 (Filter.Eventually.of_forall fun y => by
          rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (heatK_nonneg ht y)]
          exact mul_le_mul_of_nonneg_left (hB _) (heatK_nonneg ht y))
    _ = B := by rw [integral_mul_const, integral_heatK ht, one_mul]

end HRS.Uniform.Q12

namespace HRS.Uniform.Q12

variable {d : ℕ}

/-- The heat-filter `S_{ε,L} φ = φ - (I - P_ε)^L φ = ∑_{j=1}^L (-1)^{j+1} C(L,j) P_{jε} φ`. -/
def heatS (L : ℕ) (ε : ℝ) (φ : Torus d → ℝ) (x : Torus d) : ℝ :=
  ∑ j ∈ Finset.range L, (-1 : ℝ) ^ j * (L.choose (j + 1) : ℝ) * heatP d (((j + 1 : ℕ) : ℝ) * ε) φ x

/-- `‖(I - P_ε)^L φ‖_∞ ≤ ε^L ‖(Δ/4π²)^L φ‖_∞` for `φ ∈ C^{2L}`. -/
theorem q12_sup_bound (hd : 1 ≤ d) (n : ℕ) {φ : Torus d → ℝ}
    (hφ : Torus.IsCk ((2 * (n + 1) : ℕ) : WithTop ℕ∞) φ) {B : ℝ}
    (hB : ∀ x, |((heatGen)^[n + 1] φ) x| ≤ B) {ε : ℝ} (hε : 0 < ε) (x : Torus d) :
    |φ x - heatS (n + 1) ε φ x| ≤ ε ^ (n + 1) * B := by
  classical
  set u : ℕ → ℝ → ℝ := fun m t =>
    if t = 0 then ((heatGen)^[m] φ) x else heatP d t ((heatGen)^[m] φ) x with hu
  have hCk : ∀ k m : ℕ, m ≤ n + 1 → 2 * (n + 1 - m) = k → Torus.IsCk (k : WithTop ℕ∞) ((heatGen)^[m] φ) := by
    intro k m hm hk
    apply q12_isCk_iter (n := k) m
    have : k + 2 * m = 2 * (n + 1) := by omega
    rw [this]; exact hφ
  have hψ2 : ∀ m, m < n + 1 → Torus.IsCk 2 ((heatGen)^[m] φ) := fun m hm => by
    have := hCk (2 * (n + 1 - m)) m hm.le rfl
    exact this.of_le (by exact_mod_cast (by omega : 2 ≤ 2 * (n + 1 - m)))
  have hψ1 : ∀ m, m < n + 1 → Torus.IsCk 1 ((heatGen)^[m] φ) := fun m hm =>
    (hψ2 m hm).of_le (by norm_num)
  have hψ0 : Continuous ((heatGen)^[n + 1] φ) := by
    have := hCk 0 (n + 1) le_rfl (by omega)
    exact Torus.continuous_of_continuous_lift
      (show ContDiff ℝ ((0 : ℕ) : WithTop ℕ∞) _ from this).continuous
  have hD : ∀ m, m < n + 1 → ∀ t, 0 < t → HasDerivAt (u m) (u (m + 1) t) t := by
    intro m hm t ht
    have h1 := q12_hasDerivAt_heatP (hψ2 m hm) x ht
    have h2 : u (m + 1) t = heatP d t (heatGen ((heatGen)^[m] φ)) x := by
      simp only [hu, if_neg ht.ne']
      rw [Function.iterate_succ_apply']
    rw [h2]
    refine h1.congr_of_eventuallyEq ?_
    filter_upwards [Ioi_mem_nhds ht] with τ hτ
    simp only [hu, if_neg (ne_of_gt (show (0:ℝ) < τ from hτ))]
  have hC : ∀ m, m < n + 1 → ContinuousOn (u m) (Ici 0) := by
    intro m hm t ht
    rcases (show (0:ℝ) ≤ t from ht).eq_or_lt with h0 | hpos
    · subst h0
      rw [← continuousWithinAt_Ioi_iff_Ici]
      have h1 := q12_tendsto_heatP hd (hψ1 m hm) x
      have h2 : u m 0 = ((heatGen)^[m] φ) x := by simp [hu]
      rw [ContinuousWithinAt, h2]
      refine h1.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with τ hτ
      simp only [hu, if_neg (ne_of_gt (show (0:ℝ) < τ from hτ))]
    · exact (hD m hm t hpos).continuousAt.continuousWithinAt
  have hbd : ∀ t, 0 < t → |u (n + 1) t| ≤ B := by
    intro t ht
    simp only [hu, if_neg ht.ne']
    exact q12_abs_heatP_le hψ0 hB ht x
  have key := q12_fd_bound hε n B u hC hD hbd
  rw [fwdDiff_iter_eq_sum_shift, Finset.sum_range_succ'] at key
  have e : ∑ j ∈ Finset.range (n + 1), (((-1 : ℤ) ^ (n + 1 - (j + 1)) * ((n + 1).choose (j + 1) : ℤ)) • u 0 (0 + (j + 1) • ε))
        + ((-1 : ℤ) ^ (n + 1 - 0) * ((n + 1).choose 0 : ℤ)) • u 0 (0 + 0 • ε)
      = (-1 : ℝ) ^ (n + 1) * (φ x - heatS (n + 1) ε φ x) := by
    have hterm : ∀ j ∈ Finset.range (n + 1),
        (((-1 : ℤ) ^ (n + 1 - (j + 1)) * ((n + 1).choose (j + 1) : ℤ)) • u 0 (0 + (j + 1) • ε)) =
        -((-1 : ℝ) ^ (n + 1)) * ((-1 : ℝ) ^ j * ((n + 1).choose (j + 1) : ℝ) *
          heatP d (((j + 1 : ℕ) : ℝ) * ε) φ x) := by
      intro j hj
      have hj' : j ≤ n := by simpa [Nat.lt_succ_iff] using Finset.mem_range.1 hj
      have hpos : (0 : ℝ) < ((j + 1 : ℕ) : ℝ) * ε := by positivity
      have hu0 : u 0 (0 + (j + 1) • ε) = heatP d (((j + 1 : ℕ) : ℝ) * ε) φ x := by
        rw [zero_add, nsmul_eq_mul]
        simp only [hu, if_neg hpos.ne', Function.iterate_zero, id]
      rw [hu0, zsmul_eq_mul]
      obtain ⟨r, rfl⟩ : ∃ r, n = j + r := ⟨n - j, by omega⟩
      have hs : (-1 : ℝ) ^ (j + r + 1 - (j + 1)) = -((-1 : ℝ) ^ (j + r + 1)) * (-1 : ℝ) ^ j := by
        have e1 : j + r + 1 - (j + 1) = r := by omega
        have e2 : (-1 : ℝ) ^ (j + r + 1) = (-1) ^ j * (-1) ^ r * (-1) := by rw [pow_succ, pow_add]
        have h2 : ((-1 : ℝ) ^ j) * ((-1 : ℝ) ^ j) = 1 := by
          rw [← pow_add, ← two_mul, pow_mul]; simp
        rw [e1, e2]
        linear_combination (-((-1 : ℝ) ^ r)) * h2
      rw [Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one, Int.cast_natCast, hs]
      ring
    have h0 : ((-1 : ℤ) ^ (n + 1 - 0) * ((n + 1).choose 0 : ℤ)) • u 0 (0 + 0 • ε) =
        (-1 : ℝ) ^ (n + 1) * φ x := by
      rw [zsmul_eq_mul]
      simp [hu]
    rw [Finset.sum_congr rfl hterm, h0, ← Finset.mul_sum]
    unfold heatS
    ring
  rw [e, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul] at key
  exact key

end HRS.Uniform.Q12
