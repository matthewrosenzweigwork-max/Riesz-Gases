import HRS.Equilibrium.Parametrix.PX1AuxChart

/-!
# Prop 4.13 parametrix, packet PX1: extension of functions across the diagonal

For `d ≥ 2` the diagonal `{x = y}` of `𝕋^d × 𝕋^d` has codimension `≥ 2`.  A `C^{n+1}` function on the
off-diagonal set whose derivatives of orders `≤ n+1` are bounded extends to a `C^n` function on
`ℝ^d × ℝ^d` (`ext_theorem`).  The proof: bounded gradient gives a Lipschitz function on the
(quasi-convex) complement of the diagonal (`lip_offDiag`, using perturbation of segments off the
lattice points, `seg_perturb`), hence a continuous extension (`ext_cont`); a continuous function
that is `C^1` off a closed set and whose gradient extends continuously is `C^1` (`hasFDerivAt_ext`,
via two half-spaces); induct on `n`.
-/

open MeasureTheory Filter Topology
noncomputable section

namespace HRS.Parx

variable {d : ℕ}

/-- The difference map `ζ(x, y) = x - y`. -/
def zeta (d : ℕ) : Euc d × Euc d →L[ℝ] Euc d :=
  ContinuousLinearMap.fst ℝ (Euc d) (Euc d) - ContinuousLinearMap.snd ℝ (Euc d) (Euc d)

theorem zeta_apply (p : Euc d × Euc d) : zeta d p = p.1 - p.2 := rfl

theorem norm_zeta_le (p : Euc d × Euc d) : ‖zeta d p‖ ≤ 2 * ‖p‖ := by
  rw [zeta_apply]
  calc ‖p.1 - p.2‖ ≤ ‖p.1‖ + ‖p.2‖ := norm_sub_le _ _
    _ ≤ _ := by linarith [norm_fst_le p, norm_snd_le p]

theorem mk_sub' (x y : Euc d) : Torus.mk (x - y) = Torus.mk x - Torus.mk y := by
  funext i; simp [Torus.mk]

theorem mk_eq_iff (x y : Euc d) : Torus.mk x = Torus.mk y ↔ Torus.mk (x - y) = 0 := by
  rw [mk_sub', sub_eq_zero]

theorem mem_offDiag_iff (p : Euc d × Euc d) : p ∈ offDiag d ↔ Torus.mk (zeta d p) ≠ 0 := by
  show Torus.mk p.1 ≠ Torus.mk p.2 ↔ _
  rw [Ne, Ne, mk_eq_iff]; rfl

/-- Nonzero lattice vectors have norm `≥ 1`. -/
theorem one_le_norm_of_mk_eq_zero {v : Euc d} (hv : Torus.mk v = 0) (hne : v ≠ 0) : 1 ≤ ‖v‖ := by
  have h := mk_eq_zero_imp hv
  obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hne (by ext i; simpa using hcon i)
  obtain ⟨n, hn⟩ := h i
  have hn0 : n ≠ 0 := by
    intro h0; apply hi; rw [hn, h0]; simp
  have h1 : (1 : ℝ) ≤ |(n : ℝ)| := by
    have : (1 : ℤ) ≤ |n| := Int.one_le_abs hn0
    exact_mod_cast this
  calc (1 : ℝ) ≤ |(n : ℝ)| := h1
    _ = |v i| := by rw [hn]
    _ ≤ ‖v‖ := by simpa using PiLp.norm_apply_le v i

theorem lat_sub {v w : Euc d} (hv : Torus.mk v = 0) (hw : Torus.mk w = 0) : Torus.mk (v - w) = 0 := by
  rw [mk_sub', hv, hw, sub_zero]

theorem lat_eq_of_close {v w : Euc d} (hv : Torus.mk v = 0) (hw : Torus.mk w = 0)
    (h : ‖v - w‖ < 1) : v = w := by
  by_contra hne
  have := one_le_norm_of_mk_eq_zero (lat_sub hv hw) (sub_ne_zero.mpr hne)
  linarith

theorem dense_offDiag (hd : 0 < d) : Dense (offDiag d) := by
  rw [Metric.dense_iff]
  intro x r hr
  set e : Euc d := EuclideanSpace.single ⟨0, hd⟩ (1 : ℝ) with he
  have hne : ‖e‖ = 1 := by simp [he]
  have he0 : e ≠ 0 := by intro h; rw [h] at hne; simp at hne
  set r' := min r (1 / 2) with hr'
  have hr'0 : 0 < r' := lt_min hr (by norm_num)
  have hr'r : r' ≤ r := min_le_left _ _
  have hr'h : r' ≤ 1 / 2 := min_le_right _ _
  let pt : ℝ → Euc d × Euc d := fun η => (x.1 + η • e, x.2)
  have hzp : ∀ η, zeta d (pt η) = zeta d x + η • e := by
    intro η; simp only [pt, zeta_apply]; rw [add_sub_right_comm]
  have hdist : ∀ η, 0 < η → η < r' → pt η ∈ Metric.ball x r := by
    intro η h0 h1
    rw [Metric.mem_ball, dist_eq_norm]
    have : pt η - x = (η • e, 0) := by ext <;> simp [pt]
    rw [this, Prod.norm_def]
    simp only [norm_zero, norm_smul, hne, Real.norm_eq_abs, abs_of_pos h0, mul_one]
    exact lt_of_lt_of_le (max_lt (lt_of_lt_of_le h1 hr'r) hr) le_rfl
  by_contra hcon
  rw [Set.not_nonempty_iff_eq_empty] at hcon
  have hmem : ∀ η, 0 < η → η < r' → Torus.mk (zeta d x + η • e) = 0 := by
    intro η h0 h1
    by_contra hnot
    have : pt η ∈ Metric.ball x r ∩ offDiag d :=
      ⟨hdist η h0 h1, (mem_offDiag_iff _).2 (by rw [hzp]; exact hnot)⟩
    rw [hcon] at this; exact this
  have a1 := hmem (r' / 2) (by linarith) (by linarith)
  have a2 := hmem (r' / 4) (by linarith) (by linarith)
  have := lat_eq_of_close a1 a2 (by
    have : zeta d x + (r' / 2) • e - (zeta d x + (r' / 4) • e) = (r' / 4) • e := by
      rw [add_sub_add_left_eq_sub, ← sub_smul]; congr 1; ring
    rw [this, norm_smul, hne, Real.norm_eq_abs, abs_of_pos (by linarith)]
    linarith)
  have h3 : (r' / 2) • e = (r' / 4) • e := add_left_cancel this
  have h4 : ((r' / 2) - (r' / 4)) • e = 0 := by rw [sub_smul, h3, sub_self]
  rcases smul_eq_zero.mp h4 with h | h
  · linarith
  · exact he0 h

section Lipschitz
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem mvt_offDiag {f : Euc d × Euc d → V} {K : ℝ}
    (hdiff : DifferentiableOn ℝ f (offDiag d)) (hfd : ∀ p ∈ offDiag d, ‖fderiv ℝ f p‖ ≤ K)
    {p q : Euc d × Euc d} (hseg : segment ℝ p q ⊆ offDiag d) :
    ‖f q - f p‖ ≤ K * ‖q - p‖ := by
  refine Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le (f' := fderiv ℝ f)
    (fun x hx => ?_) (fun x hx => hfd x (hseg hx)) (convex_segment p q) (left_mem_segment ℝ p q)
    (right_mem_segment ℝ p q)
  exact ((hdiff.differentiableAt (isOpen_offDiag.mem_nhds (hseg hx))).hasFDerivAt).hasFDerivWithinAt

theorem exists_not_span (hd : 2 ≤ d) (a : Euc d) :
    ∃ w : Euc d, ‖w‖ = 1 ∧ ∀ c : ℝ, w ≠ c • a := by
  let i0 : Fin d := ⟨0, by omega⟩
  let i1 : Fin d := ⟨1, by omega⟩
  have h01 : i0 ≠ i1 := by intro h; have := congrArg Fin.val h; simp [i0, i1] at this
  by_contra hcon
  push Not at hcon
  obtain ⟨c0, h0⟩ := hcon (EuclideanSpace.single i0 (1 : ℝ)) (by simp)
  obtain ⟨c1, h1⟩ := hcon (EuclideanSpace.single i1 (1 : ℝ)) (by simp)
  have e00 := congrArg (fun v : Euc d => v i0) h0
  have e10 := congrArg (fun v : Euc d => v i0) h1
  have e11 := congrArg (fun v : Euc d => v i1) h1
  simp [h01] at e00 e10 e11
  have hc1 : c1 = 0 := by
    rcases e10 with h | h
    · exact h.symm ▸ rfl
    · rw [h] at e00; simp at e00
  rw [hc1] at e11
  simp at e11

theorem seg_perturb (hd : 2 ≤ d) {p q : Euc d × Euc d} (hp : p ∈ offDiag d)
    (hpq : ‖q - p‖ < 1 / 8) (hB : ¬ segment ℝ p q ⊆ offDiag d) :
    ∃ w : Euc d, ‖w‖ = 1 ∧ ∀ η : ℝ, 0 < η → η < 1 / 2 →
      segment ℝ p (q + (η • w, (0 : Euc d))) ⊆ offDiag d := by
  obtain ⟨x, hx, hxU⟩ := Set.not_subset.mp hB
  obtain ⟨a, t, ha, ht, hat, rfl⟩ := hx
  have hxS : Torus.mk (zeta d (a • p + t • q)) = 0 := by
    by_contra h; exact hxU ((mem_offDiag_iff _).2 h)
  have hpS : Torus.mk (zeta d p) ≠ 0 := (mem_offDiag_iff _).1 hp
  set bv : Euc d := zeta d q - zeta d p with hbv
  have hbn : ‖bv‖ < 1 / 4 := by
    have : bv = zeta d (q - p) := by simp [hbv]
    rw [this]
    have := norm_zeta_le (q - p)
    linarith
  have hax : zeta d (a • p + t • q) = zeta d p + t • bv := by
    have : a = 1 - t := by linarith
    subst this
    simp only [map_add, map_smul, hbv]
    module
  set av : Euc d := t • bv with hav
  have hav0 : av ≠ 0 := by
    intro h
    apply hpS
    rw [hax, h, add_zero] at hxS
    exact hxS
  obtain ⟨w, hw1, hw⟩ := exists_not_span hd av
  refine ⟨w, hw1, fun η h0 h1 y hy => ?_⟩
  by_contra hyU
  obtain ⟨a', s', ha', hs', has', rfl⟩ := hy
  have hyS : Torus.mk (zeta d (a' • p + s' • (q + (η • w, (0 : Euc d))))) = 0 := by
    by_contra h; exact hyU ((mem_offDiag_iff _).2 h)
  have hay : zeta d (a' • p + s' • (q + (η • w, (0 : Euc d)))) = zeta d p + s' • (bv + η • w) := by
    have : a' = 1 - s' := by linarith
    subst this
    simp only [map_add, map_smul, hbv, zeta_apply]
    simp
    module
  have ht1 : t ≤ 1 := by linarith
  have hs1 : s' ≤ 1 := by linarith
  have hclose : ‖(zeta d p + s' • (bv + η • w)) - (zeta d p + t • bv)‖ < 1 := by
    have e : (zeta d p + s' • (bv + η • w)) - (zeta d p + t • bv) = s' • (bv + η • w) - t • bv := by
      abel
    rw [e]
    calc ‖s' • (bv + η • w) - t • bv‖ ≤ ‖s' • (bv + η • w)‖ + ‖t • bv‖ := norm_sub_le _ _
      _ = s' * ‖bv + η • w‖ + t * ‖bv‖ := by
          rw [norm_smul, norm_smul, Real.norm_of_nonneg hs', Real.norm_of_nonneg ht]
      _ ≤ s' * (‖bv‖ + η) + t * ‖bv‖ := by
          have : ‖bv + η • w‖ ≤ ‖bv‖ + η := by
            calc ‖bv + η • w‖ ≤ ‖bv‖ + ‖η • w‖ := norm_add_le _ _
              _ = _ := by rw [norm_smul, hw1, Real.norm_of_nonneg h0.le, mul_one]
          exact add_le_add (mul_le_mul_of_nonneg_left this hs') le_rfl
      _ < 1 := by
          have : s' * (‖bv‖ + η) ≤ ‖bv‖ + η := by
            nlinarith [norm_nonneg bv]
          have : t * ‖bv‖ ≤ ‖bv‖ := by nlinarith [norm_nonneg bv]
          linarith
  rw [hay] at hyS
  rw [hax] at hxS
  have hm := lat_eq_of_close hyS hxS hclose
  have hs0 : s' ≠ 0 := by
    intro h
    apply hpS
    have := hyS
    rw [h, zero_smul, add_zero] at this
    exact this
  have ht0 : t ≠ 0 := by
    intro h; apply hav0; rw [hav, h, zero_smul]
  have h2 : s' • (bv + η • w) = t • bv := add_left_cancel hm
  apply hw ((t - s') / (s' * η * t))
  have h3 : (s' * η) • w = (t - s') • bv := by
    have : s' • bv + (s' * η) • w = t • bv := by
      rw [mul_smul, ← smul_add] ; exact h2
    rw [sub_smul]
    exact eq_sub_of_add_eq' this
  have hsη : s' * η ≠ 0 := mul_ne_zero hs0 h0.ne'
  calc w = (s' * η)⁻¹ • ((s' * η) • w) := by rw [inv_smul_smul₀ hsη]
    _ = (s' * η)⁻¹ • ((t - s') • bv) := by rw [h3]
    _ = ((t - s') / (s' * η * t)) • (t • bv) := by
        rw [smul_smul, smul_smul]
        congr 1
        field_simp
    
theorem lip_short (hd : 2 ≤ d) {f : Euc d × Euc d → V} {K : ℝ}
    (hdiff : DifferentiableOn ℝ f (offDiag d)) (hfd : ∀ p ∈ offDiag d, ‖fderiv ℝ f p‖ ≤ K)
    {p q : Euc d × Euc d} (hp : p ∈ offDiag d) (hq : q ∈ offDiag d) (hpq : ‖q - p‖ < 1 / 8) :
    ‖f q - f p‖ ≤ K * ‖q - p‖ := by
  by_cases hseg : segment ℝ p q ⊆ offDiag d
  · exact mvt_offDiag hdiff hfd hseg
  obtain ⟨w, hw1, hseg'⟩ := seg_perturb hd hp hpq hseg
  let qη : ℝ → Euc d × Euc d := fun η => q + (η • w, (0 : Euc d))
  have hqη : Continuous qη := by
    have : Continuous fun η : ℝ => ((η • w, (0 : Euc d)) : Euc d × Euc d) :=
      (continuous_id.smul continuous_const).prodMk continuous_const
    exact continuous_const.add this
  have hq0 : qη 0 = q := by simp [qη]
  have hfc : ContinuousAt f q := (hdiff.differentiableAt (isOpen_offDiag.mem_nhds hq)).continuousAt
  have h1 : Tendsto (fun η => ‖f (qη η) - f p‖) (𝓝[>] (0 : ℝ)) (𝓝 ‖f q - f p‖) := by
    have : Tendsto (fun η => f (qη η)) (𝓝 (0 : ℝ)) (𝓝 (f q)) := by
      have h0 : Tendsto qη (𝓝 (0 : ℝ)) (𝓝 q) := by
        have := hqη.tendsto 0
        rwa [hq0] at this
      exact hfc.tendsto.comp h0
    exact (((this.sub tendsto_const_nhds).norm)).mono_left nhdsWithin_le_nhds
  have h2 : Tendsto (fun η => K * ‖qη η - p‖) (𝓝[>] (0 : ℝ)) (𝓝 (K * ‖q - p‖)) := by
    have : Tendsto (fun η => K * ‖qη η - p‖) (𝓝 (0 : ℝ)) (𝓝 (K * ‖qη 0 - p‖)) :=
      (((hqη.sub continuous_const).norm).const_mul K).tendsto 0
    rw [hq0] at this
    exact this.mono_left nhdsWithin_le_nhds
  refine le_of_tendsto_of_tendsto h1 h2 ?_
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 / 2 by norm_num)] with η hη
  exact mvt_offDiag hdiff hfd (hseg' η hη.1 hη.2)

theorem lip_offDiag (hd : 2 ≤ d) {f : Euc d × Euc d → V} {K : ℝ}
    (hdiff : DifferentiableOn ℝ f (offDiag d)) (hf : ∀ p ∈ offDiag d, ‖f p‖ ≤ K)
    (hfd : ∀ p ∈ offDiag d, ‖fderiv ℝ f p‖ ≤ K) {p q : Euc d × Euc d}
    (hp : p ∈ offDiag d) (hq : q ∈ offDiag d) : ‖f q - f p‖ ≤ 16 * K * ‖q - p‖ := by
  have hK : 0 ≤ K := (norm_nonneg _).trans (hf p hp)
  by_cases h : ‖q - p‖ < 1 / 8
  · refine (lip_short hd hdiff hfd hp hq h).trans ?_
    nlinarith [norm_nonneg (q - p)]
  · push Not at h
    calc ‖f q - f p‖ ≤ ‖f q‖ + ‖f p‖ := norm_sub_le _ _
      _ ≤ K + K := add_le_add (hf q hq) (hf p hp)
      _ ≤ 16 * K * ‖q - p‖ := by nlinarith

theorem ext_cont [CompleteSpace V] (hd : 2 ≤ d) {f : Euc d × Euc d → V} {K : ℝ}
    (hdiff : DifferentiableOn ℝ f (offDiag d)) (hf : ∀ p ∈ offDiag d, ‖f p‖ ≤ K)
    (hfd : ∀ p ∈ offDiag d, ‖fderiv ℝ f p‖ ≤ K) :
    ∃ g : Euc d × Euc d → V, Continuous g ∧ ∀ p ∈ offDiag d, g p = f p := by
  have hK : 0 ≤ K := by
    have hne : (offDiag d).Nonempty := (dense_offDiag (by omega)).nonempty
    obtain ⟨p, hp⟩ := hne
    exact (norm_nonneg _).trans (hf p hp)
  have hL : LipschitzOnWith (Real.toNNReal (16 * K)) f (offDiag d) := by
    refine LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_
    rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ (by positivity)]
    have := lip_offDiag hd hdiff hf hfd hy hx
    exact this
  let e : offDiag d → Euc d × Euc d := Subtype.val
  have he : IsUniformInducing e := isUniformInducing_val _
  have hdense : DenseRange e := (dense_offDiag (by omega)).denseRange_val
  have hfu : UniformContinuous (fun u : offDiag d => f u.1) := hL.to_restrict.uniformContinuous
  refine ⟨(he.isDenseInducing hdense).extend (fun u : offDiag d => f u.1),
    (uniformContinuous_uniformly_extend he hdense hfu).continuous, fun p hp => ?_⟩
  exact uniformly_extend_of_ind he hdense hfu ⟨p, hp⟩

end Lipschitz

section C1ext

theorem halfspace_closure_mem {x y h₀ : Euc d × Euc d} {δ : ℝ} (ℓ : Euc d × Euc d →L[ℝ] ℝ)
    (hh₀ : 0 < ℓ h₀) (hy : ‖y - x‖ < δ) (hℓ : ℓ x ≤ ℓ y) :
    y ∈ closure {z | ‖z - x‖ < δ ∧ ℓ x < ℓ z} := by
  rw [Metric.mem_closure_iff]
  intro ε hε
  have hn : 0 < ‖h₀‖ := by
    rcases eq_or_ne h₀ 0 with h | h
    · rw [h] at hh₀; simp at hh₀
    · exact norm_pos_iff.mpr h
  set t := min ε (δ - ‖y - x‖) / (2 * ‖h₀‖) with ht
  have hm : 0 < min ε (δ - ‖y - x‖) := lt_min hε (by linarith)
  have ht0 : 0 < t := by positivity
  have htn : t * ‖h₀‖ = min ε (δ - ‖y - x‖) / 2 := by
    rw [ht]; field_simp
  refine ⟨y + t • h₀, ⟨?_, ?_⟩, ?_⟩
  · calc ‖y + t • h₀ - x‖ = ‖(y - x) + t • h₀‖ := by rw [add_sub_right_comm]
      _ ≤ ‖y - x‖ + ‖t • h₀‖ := norm_add_le _ _
      _ = ‖y - x‖ + t * ‖h₀‖ := by rw [norm_smul, Real.norm_of_nonneg ht0.le]
      _ < δ := by
          rw [htn]
          have := min_le_right ε (δ - ‖y - x‖)
          linarith
  · rw [map_add, map_smul]
    have : 0 < t * ℓ h₀ := mul_pos ht0 hh₀
    simp only [smul_eq_mul]
    linarith
  · rw [dist_eq_norm, norm_sub_rev, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg ht0.le, htn]
    have := min_le_left ε (δ - ‖y - x‖)
    linarith

theorem hasFDerivWithinAt_side {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {g : Euc d × Euc d → V} {γ : Euc d × Euc d → (Euc d × Euc d →L[ℝ] V)}
    (hg : Continuous g) (hdiff : DifferentiableOn ℝ g (offDiag d)) (hγ : Continuous γ)
    (heq : ∀ p ∈ offDiag d, fderiv ℝ g p = γ p) (x : Euc d × Euc d) {δ : ℝ}
    (ℓ : Euc d × Euc d →L[ℝ] ℝ)
    (hU : ∀ y, ‖y - x‖ < δ → ℓ x < ℓ y → y ∈ offDiag d) :
    HasFDerivWithinAt g (γ x) (closure {z | ‖z - x‖ < δ ∧ ℓ x < ℓ z}) x := by
  set s : Set (Euc d × Euc d) := {z | ‖z - x‖ < δ ∧ ℓ x < ℓ z} with hs
  have hs_eq : s = Metric.ball x δ ∩ {y | ℓ x < ℓ y} := by
    ext z; simp [hs, dist_eq_norm]
  have hsU : s ⊆ offDiag d := fun y hy => hU y hy.1 hy.2
  have hs_open : IsOpen s := by
    rw [hs_eq]; exact Metric.isOpen_ball.inter (isOpen_lt continuous_const ℓ.continuous)
  have hs_conv : Convex ℝ s := by
    rw [hs_eq]; exact (convex_ball x δ).inter (convex_halfSpace_gt ℓ.toLinearMap.isLinear _)
  refine hasFDerivWithinAt_closure_of_tendsto_fderiv (hdiff.mono hsU) hs_conv hs_open
    (fun y _ => hg.continuousWithinAt) ?_
  have h1 : Tendsto γ (𝓝[s] x) (𝓝 (γ x)) := hγ.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  refine h1.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with y hy
  exact (heq y (hsU hy)).symm

theorem hasFDerivAt_ext (hd : 0 < d) {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {g : Euc d × Euc d → V} {γ : Euc d × Euc d → (Euc d × Euc d →L[ℝ] V)}
    (hg : Continuous g) (hdiff : DifferentiableOn ℝ g (offDiag d)) (hγ : Continuous γ)
    (heq : ∀ p ∈ offDiag d, fderiv ℝ g p = γ p) (x : Euc d × Euc d) :
    HasFDerivAt g (γ x) x := by
  by_cases hx : x ∈ offDiag d
  · have := (hdiff.differentiableAt (isOpen_offDiag.mem_nhds hx)).hasFDerivAt
    rwa [heq x hx] at this
  have hxS : Torus.mk (zeta d x) = 0 := by
    by_contra h; exact hx ((mem_offDiag_iff _).2 h)
  set i0 : Fin d := ⟨0, hd⟩ with hi0
  set ℓ₀ : Euc d × Euc d →L[ℝ] ℝ :=
    (EuclideanSpace.proj i0 : Euc d →L[ℝ] ℝ).comp (zeta d) with hℓ₀
  set h₀ : Euc d × Euc d := (EuclideanSpace.single i0 (1 : ℝ), 0) with hh₀
  have hℓh : ℓ₀ h₀ = 1 := by simp [hℓ₀, hh₀, zeta_apply]
  have hU : ∀ (ℓ : Euc d × Euc d →L[ℝ] ℝ), (∀ y, ℓ y = ℓ x → zeta d y = zeta d x →  True) →
      (∃ c : ℝ, c ≠ 0 ∧ ℓ = c • ℓ₀) →
      ∀ y, ‖y - x‖ < 1 / 8 → ℓ x < ℓ y → y ∈ offDiag d := by
    intro ℓ _ ⟨c, hc, hℓ⟩ y hy hlt
    by_contra hyU
    have hyS : Torus.mk (zeta d y) = 0 := by
      by_contra h; exact hyU ((mem_offDiag_iff _).2 h)
    have hclose : ‖zeta d y - zeta d x‖ < 1 := by
      have : zeta d y - zeta d x = zeta d (y - x) := by simp
      rw [this]
      have := norm_zeta_le (y - x)
      linarith
    have := lat_eq_of_close hyS hxS hclose
    rw [hℓ] at hlt
    simp [hℓ₀, this] at hlt
  have hplus := hasFDerivWithinAt_side hg hdiff hγ heq x (δ := 1 / 8) ℓ₀
    (hU ℓ₀ (fun _ _ _ => trivial) ⟨1, one_ne_zero, by simp⟩)
  have hminus := hasFDerivWithinAt_side hg hdiff hγ heq x (δ := 1 / 8) (-ℓ₀)
    (hU (-ℓ₀) (fun _ _ _ => trivial) ⟨-1, by norm_num, (neg_one_smul ℝ ℓ₀).symm⟩)
  have hunion := hplus.union hminus
  refine hunion.hasFDerivAt ?_
  refine Filter.mem_of_superset (Metric.ball_mem_nhds x (by norm_num : (0 : ℝ) < 1 / 8)) ?_
  intro y hy
  have hy' : ‖y - x‖ < 1 / 8 := by simpa [dist_eq_norm] using hy
  rcases le_total (ℓ₀ x) (ℓ₀ y) with h | h
  · exact Or.inl (halfspace_closure_mem ℓ₀ (by rw [hℓh]; norm_num) hy' h)
  · refine Or.inr (halfspace_closure_mem (-ℓ₀) (h₀ := -h₀) ?_ hy' ?_)
    · simp [hℓh]
    · simpa using h

end C1ext

universe u

theorem ext_theorem (hd : 2 ≤ d) : ∀ (n : ℕ) {V : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [CompleteSpace V] (f : Euc d × Euc d → V) (K : ℝ),
    ContDiffOn ℝ ((n + 1 : ℕ) : WithTop ℕ∞) f (offDiag d) →
    (∀ j ≤ n + 1, ∀ p ∈ offDiag d, ‖iteratedFDeriv ℝ j f p‖ ≤ K) →
    ∃ g : Euc d × Euc d → V, ContDiff ℝ (n : WithTop ℕ∞) g ∧ ∀ p ∈ offDiag d, g p = f p := by
  intro n
  induction n with
  | zero =>
    intro V _ _ _ f K hf hK
    have hdiff : DifferentiableOn ℝ f (offDiag d) := hf.differentiableOn (by simp)
    obtain ⟨g, hg, hgf⟩ := ext_cont hd hdiff
      (fun p hp => by simpa using hK 0 (by omega) p hp)
      (fun p hp => by simpa using hK 1 (by omega) p hp)
    exact ⟨g, contDiff_zero.2 hg, hgf⟩
  | succ n ih =>
    intro V _ _ _ f K hf hK
    have hdiff : DifferentiableOn ℝ f (offDiag d) := hf.differentiableOn (by simp)
    obtain ⟨g₀, hg₀, hg₀f⟩ := ext_cont hd hdiff
      (fun p hp => by simpa using hK 0 (by omega) p hp)
      (fun p hp => by simpa using hK 1 (by omega) p hp)
    have hφ : ContDiffOn ℝ ((n + 1 : ℕ) : WithTop ℕ∞) (fderiv ℝ f) (offDiag d) :=
      hf.fderiv_of_isOpen isOpen_offDiag (m := ((n + 1 : ℕ) : WithTop ℕ∞)) (by norm_cast)
    obtain ⟨γ, hγ, hγφ⟩ := ih (fderiv ℝ f) K hφ (fun j hj p hp => by
      rw [norm_iteratedFDeriv_fderiv]; exact hK (j + 1) (by omega) p hp)
    -- `g₀` agrees with `f` near points of the open set
    have hev : ∀ p ∈ offDiag d, g₀ =ᶠ[𝓝 p] f := fun p hp => by
      filter_upwards [isOpen_offDiag.mem_nhds hp] with y hy using hg₀f y hy
    have hg₀d : DifferentiableOn ℝ g₀ (offDiag d) := hdiff.congr hg₀f
    have heq : ∀ p ∈ offDiag d, fderiv ℝ g₀ p = γ p := fun p hp => by
      rw [(hev p hp).fderiv_eq, ← hγφ p hp]
    have hder := hasFDerivAt_ext (by omega) hg₀ hg₀d hγ.continuous heq
    have hfd : fderiv ℝ g₀ = γ := funext fun x => (hder x).fderiv
    refine ⟨g₀, ?_, hg₀f⟩
    rw [Nat.cast_add_one, contDiff_succ_iff_fderiv]
    exact ⟨fun x => (hder x).differentiableAt, by simp, by rw [hfd]; exact hγ⟩

end HRS.Parx

end
