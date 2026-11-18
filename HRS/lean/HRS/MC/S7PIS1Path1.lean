import HRS.MC.S7PIS1Sum

/-!
# Packet S1 (path facts), part 1: joint strong continuity of `(u,t,F) ↦ V^{t,u}F` on `0 ≤ u ≤ t ≤ T`, including the diagonal

* entries: `pieT t t = 1`, `|pieT u t - 1| ≤ L (t - u) ⟨k⟩^J`, and the entries `pieT u t j k` converge along any filter on which
  `(u,t) → (u₀,t₀)` inside `0 ≤ u ≤ t ≤ T`;
* `S7PIS1_V_tendsto`: the version of `pie_V_tendsto` that allows `t₀ = 0` (finite-section bounds from `S7PIDV_finBd_unif`);
* `S7PIS1_V_joint`: joint convergence with a varying vector; `S7PIS1_Vdiag`: `V^{t,t} = id`.
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.S7PIS1

open HRS HRS.PDE HRS.A33 HRS.Sec7 HRS.MC.Sec7.PIE HRS.MC.Sec7.S7PIDV

variable {d : ℕ}

/-- `U^{t,t} = id` on the modes: the diagonal matrix is the identity -/
lemma S7PIS1_pieT_diag {J : ℕ} {D : DynData d} {μ : ℝ → Torus d → ℝ} {T : ℝ} (H : PIEHyp J D μ T)
    {t : ℝ} (ht0 : 0 ≤ t) (htT : t ≤ T) (j k : NonzeroLattice d) :
    pieT D μ t t j k = if j = k then 1 else 0 := by
  classical
  rcases ht0.eq_or_lt with h | hpos
  · subst h
    exact S7PIDV_pieT_zero H j k
  · obtain ⟨hd, hJ, Rg, MB, Λ, VB, ν₀, hA⟩ := H
    unfold pieT
    rw [prop_self_pos hd D.s D.hs0 D.hsd J hJ Rg MB Λ VB D ν₀ T μ hA ⟨hpos, htT⟩
      (pieDom_realMode J k)]
    unfold Torus.funRealCoeff
    exact Torus.realMode_orthonormal j k

/-- distance of the entries to the identity -/
lemma S7PIS1_diag_dist {J : ℕ} {D : DynData d} {μ : ℝ → Torus d → ℝ} {T : ℝ} (H : PIEHyp J D μ T) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ u t : ℝ, 0 ≤ u → u ≤ t → t ≤ T → ∀ j k : NonzeroLattice d,
      |pieT D μ u t j k - (if j = k then 1 else 0)| ≤ L * (t - u) * Lattice.jp k.1 ^ (J : ℝ) := by
  classical
  obtain ⟨L, hL, hlip⟩ := pie_T_lip_u H
  refine ⟨L, hL, fun u t hu hut htT j k => ?_⟩
  rcases (hu.trans hut).eq_or_lt with h | hpos
  · have ht0 : t = 0 := h.symm
    subst ht0
    have hu0 : u = 0 := le_antisymm hut hu
    subst hu0
    rw [S7PIDV_pieT_zero H j k]
    simp only [sub_self, abs_zero]
    have := Real.rpow_nonneg (Torus.jp_pos k.1).le (J : ℝ)
    simpa using this
  · rw [← S7PIS1_pieT_diag H hpos.le htT j k]
    exact hlip u t t hu hut le_rfl hpos htT j k

/-- the entries of the propagator matrix converge along `(u,t) → (u₀,t₀)` inside `0 ≤ u ≤ t ≤ T` -/
lemma S7PIS1_entries_tendsto {J : ℕ} {D : DynData d} {μ : ℝ → Torus d → ℝ} {T : ℝ} (H : PIEHyp J D μ T)
    {X : Type*} (l : Filter X) (tt uu : X → ℝ) {t₀ u₀ : ℝ}
    (hmem : ∀ᶠ x in l, 0 ≤ uu x ∧ uu x ≤ tt x ∧ tt x ≤ T) (h₀ : 0 ≤ u₀ ∧ u₀ ≤ t₀ ∧ t₀ ≤ T)
    (hu : Tendsto uu l (𝓝 u₀)) (ht : Tendsto tt l (𝓝 t₀)) (j k : NonzeroLattice d) :
    Tendsto (fun x => pieT D μ (uu x) (tt x) j k) l (𝓝 (pieT D μ u₀ t₀ j k)) := by
  classical
  obtain ⟨L0, hL0, hdist⟩ := S7PIS1_diag_dist H
  obtain ⟨L1, hL1, hlt⟩ := pie_T_lip_t' H
  obtain ⟨L2, hL2, hlu⟩ := pie_T_lip_u' H
  have hjp : 0 ≤ Lattice.jp k.1 ^ (J : ℝ) := Real.rpow_nonneg (Torus.jp_pos k.1).le _
  rw [tendsto_iff_dist_tendsto_zero]
  rcases h₀.2.1.eq_or_lt with heq | hlt₀
  · -- diagonal limit
    have hlim : pieT D μ u₀ t₀ j k = if j = k then 1 else 0 := by
      rw [← heq]; exact S7PIS1_pieT_diag H h₀.1 (heq ▸ h₀.2.2) j k
    have hb : Tendsto (fun x => L0 * (tt x - uu x) * Lattice.jp k.1 ^ (J : ℝ)) l (𝓝 0) := by
      have := ((ht.sub hu).const_mul L0).mul_const (Lattice.jp k.1 ^ (J : ℝ))
      simpa [heq] using this
    refine squeeze_zero' (Eventually.of_forall fun x => dist_nonneg) ?_ hb
    filter_upwards [hmem] with x hx
    rw [Real.dist_eq, hlim]
    exact hdist _ _ hx.1 hx.2.1 hx.2.2 j k
  · -- off the diagonal
    have hbd : Tendsto (fun x => (L1 * |tt x - t₀| + L2 * |uu x - u₀|) * Lattice.jp k.1 ^ (J : ℝ)) l
        (𝓝 0) := by
      have h1 : Tendsto (fun x => |tt x - t₀|) l (𝓝 0) := by simpa using (ht.sub_const t₀).abs
      have h2 : Tendsto (fun x => |uu x - u₀|) l (𝓝 0) := by simpa using (hu.sub_const u₀).abs
      have := ((h1.const_mul L1).add (h2.const_mul L2)).mul_const (Lattice.jp k.1 ^ (J : ℝ))
      simpa using this
    refine squeeze_zero' (Eventually.of_forall fun x => dist_nonneg) ?_ hbd
    have hev1 : ∀ᶠ x in l, uu x < t₀ := hu.eventually (gt_mem_nhds (lt_of_le_of_lt le_rfl hlt₀))
    have hev2 : ∀ᶠ x in l, uu x < tt x := by
      have hmid : u₀ < (u₀ + t₀) / 2 := by linarith
      have hmid' : (u₀ + t₀) / 2 < t₀ := by linarith
      filter_upwards [hu.eventually (gt_mem_nhds hmid), ht.eventually (lt_mem_nhds hmid')] with x hx1 hx2
      linarith
    have ht0 : 0 < t₀ := lt_of_le_of_lt h₀.1 hlt₀
    filter_upwards [hmem, hev1, hev2] with x hx hx1 hx2
    rw [Real.dist_eq]
    have e1 := hlt (uu x) (tt x) t₀ hx.1 hx2 hx1 hx.2.2 h₀.2.2 j k
    have e2 := hlu (uu x) u₀ t₀ hx.1 h₀.1 hx1.le hlt₀.le ht0 h₀.2.2 j k
    calc |pieT D μ (uu x) (tt x) j k - pieT D μ u₀ t₀ j k|
        = |(pieT D μ (uu x) (tt x) j k - pieT D μ (uu x) t₀ j k) +
            (pieT D μ (uu x) t₀ j k - pieT D μ u₀ t₀ j k)| := by ring_nf
      _ ≤ |pieT D μ (uu x) (tt x) j k - pieT D μ (uu x) t₀ j k| +
            |pieT D μ (uu x) t₀ j k - pieT D μ u₀ t₀ j k| := abs_add_le _ _
      _ ≤ L1 * |tt x - t₀| * Lattice.jp k.1 ^ (J : ℝ) + L2 * |uu x - u₀| * Lattice.jp k.1 ^ (J : ℝ) :=
          add_le_add e1 e2
      _ = _ := by ring

/-- strong continuity of `V` along matrix-entry convergence, also at `t₀ = 0` -/
lemma S7PIS1_V_tendsto {J : ℕ} {D : DynData d} {μ : ℝ → Torus d → ℝ} {T : ℝ} (H : PIEHyp J D μ T)
    (m : ℝ) (k : ℕ) (hk : 1 ≤ k) (hJ : k + 2 ≤ J) (hm0 : (k : ℝ) + 1 < m) (hm1 : m ≤ (k : ℝ) + 2)
    {X : Type*} (l : Filter X) (tt uu : X → ℝ) (t₀ u₀ : ℝ)
    (hmem : ∀ᶠ x in l, 0 ≤ uu x ∧ uu x ≤ tt x ∧ tt x ≤ T) (h₀ : 0 ≤ u₀ ∧ u₀ ≤ t₀ ∧ t₀ ≤ T)
    (hc : ∀ j k', Tendsto (fun x => pieT D μ (uu x) (tt x) j k') l (𝓝 (pieT D μ u₀ t₀ j k')))
    (F : NegSobolev d m) :
    Tendsto (fun x => Vprop D μ m (tt x) (uu x) F) l (𝓝 (Vprop D μ m t₀ u₀ F)) := by
  obtain ⟨A, hA1, hAb⟩ := S7PIDV_finBd_unif H m (k + 1) (by omega) (by omega)
    (by push_cast; linarith) (by push_cast; linarith)
  obtain ⟨A', hA'1, hA'b⟩ := S7PIDV_finBd_unif H ((k : ℝ) + 1) k hk (by omega) (by linarith) le_rfl
  have hA : 0 ≤ A := by linarith
  have hA' : 0 ≤ A' := by linarith
  have hw : ∀ k : NonzeroLattice d, 1 ≤ Lattice.jp k.1 := fun k => Torus.jp_ge_one k.1
  have hwpos : ∀ k : NonzeroLattice d, 0 < Lattice.jp k.1 := fun k => Torus.jp_pos k.1
  have hcoord : ∀ j, Lattice.jp j.1 ^ (-m) * NegSobolev.fourierCoeff F j = NegSobolev.coord F j := by
    intro j
    unfold NegSobolev.fourierCoeff
    rw [← mul_assoc, ← Real.rpow_add (hwpos j)]; simp
  obtain ⟨hF2, -⟩ := NegSobolev.coord_sq F
  have ha : Summable fun j : NonzeroLattice d =>
      (Lattice.jp j.1 ^ (-m) * NegSobolev.fourierCoeff F j) ^ 2 :=
    hF2.congr fun j => by rw [hcoord]
  have key := pie_strong_abs l (fun k : NonzeroLattice d => Lattice.jp k.1) hw pie_jp_sublevel_finite
    (fun x => pieT D μ (uu x) (tt x)) (pieT D μ u₀ t₀) (m := m) (n := (k : ℝ) + 1) hm0 hA hA'
    (hmem.mono fun x hx => hAb _ _ hx.1 hx.2.1 hx.2.2) (hAb _ _ h₀.1 h₀.2.1 h₀.2.2)
    (hmem.mono fun x hx => hA'b _ _ hx.1 hx.2.1 hx.2.2) (hA'b _ _ h₀.1 h₀.2.1 h₀.2.2) hc
    (fun j => NegSobolev.fourierCoeff F j) ha
  have hsq := (Real.continuous_sqrt.tendsto 0).comp key
  rw [Real.sqrt_zero] at hsq
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine hsq.congr' ?_
  filter_upwards [hmem] with x hx
  simp only [Function.comp]
  obtain ⟨-, hnorm⟩ := NegSobolev.coord_sq (Vprop D μ m (tt x) (uu x) F - Vprop D μ m t₀ u₀ F)
  rw [← Real.sqrt_sq (norm_nonneg _), hnorm]
  congr 1
  refine tsum_congr fun k => ?_
  have e1 := pie_Vprop_coord D μ m (tt x) (uu x) hA (hAb _ _ hx.1 hx.2.1 hx.2.2) F k
  have e2 := pie_Vprop_coord D μ m t₀ u₀ hA (hAb _ _ h₀.1 h₀.2.1 h₀.2.2) F k
  have e3 : NegSobolev.coord (Vprop D μ m (tt x) (uu x) F - Vprop D μ m t₀ u₀ F) k =
      NegSobolev.coord (Vprop D μ m (tt x) (uu x) F) k - NegSobolev.coord (Vprop D μ m t₀ u₀ F) k := rfl
  rw [e3, e1, e2]
  ring_nf

/-- joint convergence `V^{t,u}F_x → V^{t₀,u₀}F₀` -/
lemma S7PIS1_V_joint {J : ℕ} {D : DynData d} {μ : ℝ → Torus d → ℝ} {T : ℝ} (H : PIEHyp J D μ T)
    (m : ℝ) (k : ℕ) (hk : 1 ≤ k) (hJ : k + 2 ≤ J) (hm0 : (k : ℝ) + 1 < m) (hm1 : m ≤ (k : ℝ) + 2)
    {X : Type*} (l : Filter X) (tt uu : X → ℝ) {t₀ u₀ : ℝ}
    (hmem : ∀ᶠ x in l, 0 ≤ uu x ∧ uu x ≤ tt x ∧ tt x ≤ T) (h₀ : 0 ≤ u₀ ∧ u₀ ≤ t₀ ∧ t₀ ≤ T)
    (hu : Tendsto uu l (𝓝 u₀)) (ht : Tendsto tt l (𝓝 t₀))
    (F : X → NegSobolev d m) {F₀ : NegSobolev d m} (hF : Tendsto F l (𝓝 F₀)) :
    Tendsto (fun x => Vprop D μ m (tt x) (uu x) (F x)) l (𝓝 (Vprop D μ m t₀ u₀ F₀)) := by
  obtain ⟨A, hA1, hAb⟩ := S7PIDV_finBd_unif H m (k + 1) (by omega) (by omega)
    (by push_cast; linarith) (by push_cast; linarith)
  have hA : 0 ≤ A := by linarith
  have h1 := S7PIS1_V_tendsto H m k hk hJ hm0 hm1 l tt uu t₀ u₀ hmem h₀
    (S7PIS1_entries_tendsto H l tt uu hmem h₀ hu ht) F₀
  have h2 : Tendsto (fun x => Vprop D μ m (tt x) (uu x) (F x) - Vprop D μ m (tt x) (uu x) F₀) l (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hq : Tendsto (fun x => A * ‖F x - F₀‖) l (𝓝 0) := by
      have := (tendsto_iff_norm_sub_tendsto_zero.1 hF).const_mul A
      simpa using this
    refine squeeze_zero' (Eventually.of_forall fun x => norm_nonneg _) ?_ hq
    filter_upwards [hmem] with x hx
    exact pie_V_lip_F D μ m (tt x) (uu x) hA (hAb _ _ hx.1 hx.2.1 hx.2.2) (F x) F₀
  have h3 := h2.add h1
  rw [zero_add] at h3
  refine h3.congr fun x => ?_
  abel

/-- `V^{t,t} = id` -/
lemma S7PIS1_Vdiag {J : ℕ} {D : DynData d} {μ : ℝ → Torus d → ℝ} {T : ℝ} (H : PIEHyp J D μ T)
    (m : ℝ) (k : ℕ) (hk : 1 ≤ k) (hJ : k + 2 ≤ J) (hm0 : (k : ℝ) + 1 < m) (hm1 : m ≤ (k : ℝ) + 2)
    {t : ℝ} (ht0 : 0 ≤ t) (htT : t ≤ T) (F : NegSobolev d m) : Vprop D μ m t t F = F := by
  classical
  obtain ⟨A, hA1, hAb⟩ := S7PIDV_finBd_unif H m (k + 1) (by omega) (by omega)
    (by push_cast; linarith) (by push_cast; linarith)
  apply pie_ext
  intro i
  have hwpos : 0 < Lattice.jp i.1 := Torus.jp_pos i.1
  have h1 := S7PIDV_fc_V D μ m t t (by linarith) (hAb t t ht0 le_rfl htT) F i
  have h2 : ∑' j, NegSobolev.fourierCoeff F j * pieT D μ t t j i = NegSobolev.fourierCoeff F i := by
    rw [tsum_eq_single i]
    · rw [S7PIS1_pieT_diag H ht0 htT i i]; simp
    · intro j hj
      rw [S7PIS1_pieT_diag H ht0 htT j i, if_neg hj]; simp
  have h3 : NegSobolev.fourierCoeff (Vprop D μ m t t F) i = NegSobolev.fourierCoeff F i := by
    rw [h1, h2]
  unfold NegSobolev.fourierCoeff at h3
  exact mul_left_cancel₀ (Real.rpow_pos_of_pos hwpos m).ne' h3

end HRS.MC.Sec7.S7PIS1

end
