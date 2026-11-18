import HRS.Uniform.Spec

/-!
# Lemma 3.17 (`maximal_estimate`): downstream helpers (packet Q01)

`Spec.lean` cannot import this file (the definitions `EvolData`, `IsStochConv`, ... live there), so the
helpers are downstream.  Proved here: the quasi-contractivity `‖V(t,r)‖ ≤ e^{K(t-r)/2}` of the
dissipative alternative (finite-dimensional energy estimate for the Galerkin evolutions, then strong
limit), and the deterministic clause (2) of Lemma 3.17.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace HRS
namespace Uniform

variable {H E : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Energy estimate for a finite-dimensional Galerkin trajectory: if `u(t) ∈ W` (finite-dimensional),
`d/dt ⟨y, u(t)⟩ = ⟨j y, g(t)⟩` for `y ∈ W` and `2⟨j u, g⟩ ≤ K‖u‖²`, then `‖u(t)‖² ≤ e^{K(t-a)}‖u(a)‖²`. -/
theorem galerkin_energy (W : Submodule ℝ H) [FiniteDimensional ℝ W] (j : H →L[ℝ] E)
    (u : ℝ → H) (g : ℝ → E) (a b K : ℝ)
    (hu : ∀ t ∈ Set.Icc a b, u t ∈ W)
    (hd : ∀ t ∈ Set.Icc a b, ∀ y ∈ W,
      HasDerivWithinAt (fun t' => inner ℝ y (u t')) (inner ℝ (j y) (g t)) (Set.Icc a b) t)
    (hdis : ∀ t ∈ Set.Icc a b, 2 * inner ℝ (j (u t)) (g t) ≤ K * ‖u t‖ ^ 2) :
    ∀ t ∈ Set.Icc a b, ‖u t‖ ^ 2 ≤ Real.exp (K * (t - a)) * ‖u a‖ ^ 2 := by
  classical
  by_cases hab : a ≤ b
  swap
  · intro t ht; exact absurd (ht.1.trans ht.2) hab
  set B := stdOrthonormalBasis ℝ W with hB
  have hnorm : ∀ t ∈ Set.Icc a b, ‖u t‖ ^ 2 = ∑ i, (inner ℝ (B i : H) (u t)) ^ 2 := by
    intro t ht
    have := B.sum_sq_norm_inner_right ⟨u t, hu t ht⟩
    simpa [Submodule.coe_norm, Submodule.coe_inner, Real.norm_eq_abs, sq_abs] using this.symm
  have hrepr : ∀ t ∈ Set.Icc a b, u t = ∑ i, inner ℝ (B i : H) (u t) • (B i : H) := by
    intro t ht
    have := B.sum_repr' ⟨u t, hu t ht⟩
    have h2 := congrArg (fun z : W => (z : H)) this
    simpa [Submodule.coe_inner] using h2.symm
  set φ : ℝ → ℝ := fun t => ∑ i, (inner ℝ (B i : H) (u t)) ^ 2 with hφ
  set φ' : ℝ → ℝ := fun t => ∑ i, 2 * inner ℝ (B i : H) (u t) * inner ℝ (j (B i : H)) (g t) with hφ'
  have hφd : ∀ t ∈ Set.Icc a b, HasDerivWithinAt φ (φ' t) (Set.Icc a b) t := by
    intro t ht
    have := HasDerivWithinAt.sum (u := Finset.univ) (fun i _ =>
      ((hd t ht (B i : H) (B i).2).pow 2))
    convert this using 1
    · ext s; simp [hφ]
    · simp [hφ']
  have hφ'eq : ∀ t ∈ Set.Icc a b, φ' t = 2 * inner ℝ (j (u t)) (g t) := by
    intro t ht
    have h1 : inner ℝ (j (u t)) (g t) = ∑ i, inner ℝ (B i : H) (u t) * inner ℝ (j (B i : H)) (g t) := by
      conv_lhs => rw [hrepr t ht]
      rw [map_sum, sum_inner]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_smul, inner_smul_left]
      simp
    rw [h1, hφ', Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  have hφle : ∀ t ∈ Set.Icc a b, φ' t ≤ K * φ t := by
    intro t ht
    rw [hφ'eq t ht]
    have := hdis t ht
    have e : φ t = ‖u t‖ ^ 2 := (hnorm t ht).symm
    rw [e]; exact this
  set ψ : ℝ → ℝ := fun t => Real.exp (-K * t) * φ t with hψ
  have hcont : ContinuousOn φ (Set.Icc a b) := fun t ht => (hφd t ht).continuousWithinAt
  have hanti : AntitoneOn ψ (Set.Icc a b) := by
    refine antitoneOn_of_hasDerivWithinAt_nonpos (f' := fun t => Real.exp (-K * t) * (φ' t - K * φ t))
      (convex_Icc a b) ?_ ?_ ?_
    · exact (Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn.mul hcont
    · intro t ht
      rw [interior_Icc] at ht ⊢
      have h1 : HasDerivAt (fun t => Real.exp (-K * t)) (Real.exp (-K * t) * (-K)) t := by
        have := ((hasDerivAt_id t).const_mul (-K)).exp
        simpa using this
      have h2 : HasDerivAt φ (φ' t) t :=
        (hφd t (Set.Ioo_subset_Icc_self ht)).hasDerivAt (Icc_mem_nhds ht.1 ht.2)
      have := (h1.mul h2).hasDerivWithinAt (s := Set.Ioo a b)
      convert this using 1
      ring
    · intro t ht
      rw [interior_Icc] at ht
      have := hφle t (Set.Ioo_subset_Icc_self ht)
      have h0 : 0 < Real.exp (-K * t) := Real.exp_pos _
      exact mul_nonpos_of_nonneg_of_nonpos h0.le (by linarith)
  intro t ht
  have h1 := hanti (Set.left_mem_Icc.2 hab) ht ht.1
  simp only [hψ] at h1
  have e1 : φ t = ‖u t‖ ^ 2 := (hnorm t ht).symm
  have e2 : φ a = ‖u a‖ ^ 2 := (hnorm a (Set.left_mem_Icc.2 hab)).symm
  rw [e1, e2] at h1
  have h3 : 0 < Real.exp (K * t) := Real.exp_pos _
  have h5 := mul_le_mul_of_nonneg_left h1 h3.le
  have h6 : Real.exp (K * t) * (Real.exp (-K * t) * ‖u t‖ ^ 2) = ‖u t‖ ^ 2 := by
    rw [← mul_assoc, ← Real.exp_add]; simp
  have h7 : Real.exp (K * t) * (Real.exp (-K * a) * ‖u a‖ ^ 2) = Real.exp (K * (t - a)) * ‖u a‖ ^ 2 := by
    rw [← mul_assoc, ← Real.exp_add]; ring_nf
  rw [h6, h7] at h5
  exact h5

theorem norm_proj_le (P : H →L[ℝ] H) (h2 : P.comp P = P)
    (hs : ∀ x y, inner ℝ (P x) y = inner ℝ x (P y)) (x : H) : ‖P x‖ ≤ ‖x‖ := by
  have h1 : ‖P x‖ ^ 2 = inner ℝ x (P x) := by
    rw [← real_inner_self_eq_norm_sq, hs, ← ContinuousLinearMap.comp_apply, h2]
  have h3 : inner ℝ x (P x) ≤ ‖x‖ * ‖P x‖ := real_inner_le_norm _ _
  by_contra hlt
  push_neg at hlt
  have : ‖P x‖ ^ 2 ≤ ‖x‖ * ‖P x‖ := h1 ▸ h3
  nlinarith [norm_nonneg x, norm_nonneg (P x)]

/-- Quasi-contractivity of the dissipative alternative: `‖V(t,r)x‖ ≤ e^{K(t-r)/2}‖x‖`. -/
theorem EvolData.Dissipative.norm_VH_le (S : EvolData H E) {T K : ℝ} (hD : S.Dissipative T K)
    {r t : ℝ} (hr : r ∈ Set.Icc (0 : ℝ) T) (ht : t ∈ Set.Icc r T) (x : H) :
    ‖S.VH t r x‖ ≤ Real.exp (K * (t - r) / 2) * ‖x‖ := by
  obtain ⟨hj, hsurj, hdis, hgen, P, Vn, hP2, hPs, hPfin, hPD, hPconv, hVr, hVrange, hVder, hVlim⟩ := hD
  have key : ∀ n, ‖Vn n t r x‖ ≤ Real.exp (K * (t - r) / 2) * ‖x‖ := by
    intro n
    classical
    haveI : FiniteDimensional ℝ (LinearMap.range (P n : H →ₗ[ℝ] H)) := hPfin n
    have hrange : ∀ s ∈ Set.Icc r T, Vn n s r x ∈ LinearMap.range (P n : H →ₗ[ℝ] H) := by
      intro s _
      obtain ⟨y, hy⟩ := hVrange n s r x
      exact ⟨y, hy⟩
    have hmemD : ∀ s ∈ Set.Icc r T, Vn n s r x ∈ S.D := by
      intro s hs
      obtain ⟨y, hy⟩ := hVrange n s r x
      rw [← hy]; exact hPD n y
    let g : ℝ → E := fun s => if h : Vn n s r x ∈ S.D then S.A s ⟨Vn n s r x, h⟩ else 0
    have hge : ∀ s (hs : s ∈ Set.Icc r T), g s = S.A s ⟨Vn n s r x, hmemD s hs⟩ := by
      intro s hs; simp [g, hmemD s hs]
    have hmain := galerkin_energy (LinearMap.range (P n : H →ₗ[ℝ] H)) S.j (fun s => Vn n s r x) g r T K
      hrange
      (by
        intro s hs y hy
        have := hVder n r s x y (hmemD s hs) hr hs (by simpa using hy)
        rw [hge s hs]; exact this)
      (by
        intro s hs
        rw [hge s hs]
        exact hdis s ⟨hr.1.trans hs.1, hs.2⟩ ⟨Vn n s r x, hmemD s hs⟩)
      t ht
    have hr0 : Vn n r r x = P n x := hVr n r x hr
    have hPn : ‖P n x‖ ≤ ‖x‖ := norm_proj_le (P n) (hP2 n) (hPs n) x
    simp only [hr0] at hmain
    have h1 : ‖Vn n t r x‖ ^ 2 ≤ (Real.exp (K * (t - r) / 2) * ‖x‖) ^ 2 := by
      calc ‖Vn n t r x‖ ^ 2 ≤ Real.exp (K * (t - r)) * ‖P n x‖ ^ 2 := hmain
        _ ≤ Real.exp (K * (t - r)) * ‖x‖ ^ 2 := by
          gcongr
        _ = (Real.exp (K * (t - r) / 2) * ‖x‖) ^ 2 := by
          rw [mul_pow, ← Real.exp_nat_mul]; congr 2; push_cast; ring
    exact le_of_sq_le_sq h1 (by positivity)
  exact le_of_tendsto' ((hVlim r hr t ht x).norm) key

/-- The constant of the deterministic clause (2) of Lemma 3.17 (depends only on `(T, K)`). -/
def detConst (T K : ℝ) : ℝ := K ^ 2 + Real.exp (|K| * T / 2) + 1

theorem detConst_pos (T K : ℝ) : 0 < detConst T K := by
  unfold detConst; positivity

/-- Pointwise bound `‖V(t,r) j b‖ ≤ C‖b‖` for `0 ≤ r ≤ t ≤ T` under either alternative. -/
theorem EvolData.MaxHyp.norm_le {T K : ℝ} (hT : 0 ≤ T) {S : EvolData H E} (hS : S.MaxHyp T K)
    {r t : ℝ} (hr : 0 ≤ r) (hrt : r ≤ t) (htT : t ≤ T) (b : H) :
    ‖S.VE t r (S.j b)‖ ≤ detConst T K * ‖b‖ := by
  obtain ⟨hev, h | h⟩ := hS
  · obtain ⟨-, hj, hV, -⟩ := h
    have hK : 0 ≤ K := (norm_nonneg _).trans (hV 0 0 le_rfl le_rfl hT).2
    have h1 : ‖S.VE t r (S.j b)‖ ≤ K * (K * ‖b‖) := by
      calc ‖S.VE t r (S.j b)‖ ≤ ‖S.VE t r‖ * ‖S.j b‖ := (S.VE t r).le_opNorm _
        _ ≤ K * (K * ‖b‖) := by
          have h2 : ‖S.j b‖ ≤ K * ‖b‖ := (S.j.le_opNorm b).trans (by gcongr)
          exact mul_le_mul ((hV r t hr hrt htT).2) h2 (norm_nonneg _) hK
    calc ‖S.VE t r (S.j b)‖ ≤ K * (K * ‖b‖) := h1
      _ = K ^ 2 * ‖b‖ := by ring
      _ ≤ detConst T K * ‖b‖ := by
        unfold detConst
        have : 0 ≤ Real.exp (|K| * T / 2) + 1 := by positivity
        nlinarith [norm_nonneg b]
  · have hint := hev.intertwine r t hr hrt htT
    have hcomm : S.VE t r (S.j b) = S.j (S.VH t r b) := by
      have := congrArg (fun F : H →L[ℝ] E => F b) hint
      simpa using this
    rw [hcomm, h.1 (S.VH t r b)]
    have hb := EvolData.Dissipative.norm_VH_le S h ⟨hr, hrt.trans htT⟩ ⟨hrt, htT⟩ b
    refine hb.trans ?_
    have : Real.exp (K * (t - r) / 2) ≤ Real.exp (|K| * T / 2) := by
      apply Real.exp_le_exp.2
      have h1 : K * (t - r) ≤ |K| * (t - r) := mul_le_mul_of_nonneg_right (le_abs_self K) (by linarith)
      have h2 : |K| * (t - r) ≤ |K| * T := mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg K)
      linarith
    unfold detConst
    have h3 : Real.exp (|K| * T / 2) * ‖b‖ ≤ (K ^ 2 + Real.exp (|K| * T / 2) + 1) * ‖b‖ := by
      gcongr; nlinarith [sq_nonneg K]
    exact (mul_le_mul_of_nonneg_right this (norm_nonneg b)).trans h3

/-- Clause (2) of Lemma 3.17: the deterministic convolution. -/
theorem maximal_deterministic (T K : ℝ) (hT : 0 ≤ T) (S : EvolData H E) (hS : S.MaxHyp T K)
    [CompleteSpace E] (b : ℝ → H) :
    ⨆ t ∈ Set.Icc (0 : ℝ) T, ‖∫ r in Set.Icc (0 : ℝ) t, S.VE t r (S.j (b r))‖ₑ ≤
      ENNReal.ofReal (detConst T K) * ∫⁻ r in Set.Icc (0 : ℝ) T, ‖b r‖ₑ := by
  refine iSup₂_le fun t ht => ?_
  calc ‖∫ r in Set.Icc (0 : ℝ) t, S.VE t r (S.j (b r))‖ₑ
      ≤ ∫⁻ r in Set.Icc (0 : ℝ) t, ‖S.VE t r (S.j (b r))‖ₑ := enorm_integral_le_lintegral_enorm _
    _ ≤ ∫⁻ r in Set.Icc (0 : ℝ) t, ENNReal.ofReal (detConst T K) * ‖b r‖ₑ := by
        refine setLIntegral_mono' measurableSet_Icc fun r hr => ?_
        have := hS.norm_le hT hr.1 hr.2 ht.2 (b r)
        rw [← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm, ← ENNReal.ofReal_mul (detConst_pos T K).le]
        exact ENNReal.ofReal_le_ofReal this
    _ ≤ ∫⁻ r in Set.Icc (0 : ℝ) T, ENNReal.ofReal (detConst T K) * ‖b r‖ₑ :=
        lintegral_mono_set (Set.Icc_subset_Icc_right ht.2)
    _ = _ := by
        exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

end Uniform
end HRS
