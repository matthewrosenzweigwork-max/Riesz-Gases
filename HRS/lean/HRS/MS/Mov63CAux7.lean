import HRS.MS.Mov63CAux6

/-!
# S6.3, uniqueness chain (N3b, part 2): the defect functional `Ψ` and its `L¹` bound

Namespace `HRS.MS.Mov63`, helper prefix `mnc_`.  See `Mov63CAux1` for the plan.

For a test function `g` set `Ψ(g) = (⟨g,u_t⟩ - ⟨g,u_0⟩) - ∫_{[0,t]} F_g`, `F_g(x) = -⟨S_0g,u_x⟩ - ⟨g,R u_x⟩ + ⟨g,B(u_x,u_x)⟩`.
`mnc_weak_linear` says `Ψ(φ) = 0` for `φ ∈ C_c^∞`.  `Ψ` is linear on "good" functions and
`|Ψ(g)| ≤ C (‖g‖_{L¹} + ‖S_0 g‖_{L¹})`.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.Mov63

open HRS HRS.Whole HRS.MS.MovOsc HRS.MS.MovC1 HRS.MS.MovForce HRS.MS.MovLin HRS.MH.DualityRd

variable {d : ℕ} {s β q : ℝ} {ρ : Euc d → ℝ}

/-- Test functions for which all pairings are defined. -/
structure mnc_Good (d : ℕ) (β q : ℝ) (g : Euc d → ℝ) : Prop where
  smooth : ContDiff ℝ ∞ g
  l2 : MemLp g 2 (volume : Measure (Euc d))
  l1 : Integrable g
  s2 : MemLp (mov_S0 d β q g) 2 (volume : Measure (Euc d))
  s1 : Integrable (mov_S0 d β q g)

lemma mnc_S0_sub {g1 g2 : Euc d → ℝ} (h1 : ContDiff ℝ ∞ g1) (h2 : ContDiff ℝ ∞ g2) (x : Euc d) :
    mov_S0 d β q (fun y => g1 y - g2 y) x = mov_S0 d β q g1 x - mov_S0 d β q g2 x := by
  have h := ContDiffAt.laplacian_sub (x := x) (f₁ := g1) (f₂ := g2) (h1.contDiffAt.of_le (by simp))
    (h2.contDiffAt.of_le (by simp))
  have e : Laplacian.laplacian (fun y => g1 y - g2 y) x = Laplacian.laplacian g1 x - Laplacian.laplacian g2 x := h
  unfold mov_S0
  rw [e]
  ring

lemma mnc_S0_sub_fun {g1 g2 : Euc d → ℝ} (h1 : ContDiff ℝ ∞ g1) (h2 : ContDiff ℝ ∞ g2) :
    mov_S0 d β q (fun y => g1 y - g2 y) = fun x => mov_S0 d β q g1 x - mov_S0 d β q g2 x :=
  funext fun x => mnc_S0_sub h1 h2 x

lemma mnc_Good.sub {g1 g2 : Euc d → ℝ} (h1 : mnc_Good d β q g1) (h2 : mnc_Good d β q g2) :
    mnc_Good d β q (fun y => g1 y - g2 y) := by
  refine ⟨h1.smooth.sub h2.smooth, h1.l2.sub h2.l2, h1.l1.sub h2.l1, ?_, ?_⟩
  · rw [mnc_S0_sub_fun h1.smooth h2.smooth]; exact h1.s2.sub h2.s2
  · rw [mnc_S0_sub_fun h1.smooth h2.smooth]; exact h1.s1.sub h2.s1

section Psi

variable (H : Mov2dTh d s β q ρ) {m : ℕ} (hm : (d : ℝ) / 2 + 3 < m) (P : ℝ → Euc d → ℝ)

/-- The integrand `F_g(x)`. -/
def mnc_F (g : Euc d → ℝ) (x : ℝ) : ℝ :=
  -(mnc_ipL (mov_S0 d β q g) (Nat.cast_nonneg m) (mnc_u ρ P m x)) -
    mnc_ipL g (mnb_sub_a_nonneg H hm) (mov2d_R d s β q ρ (m : ℝ) (mnc_u ρ P m x)) +
    mnc_ipL g (mnb_sub_a_nonneg H hm) (mov_B_ext H hm (mnc_u ρ P m x) (mnc_u ρ P m x))

/-- The defect functional `Ψ_t(g)`. -/
def mnc_Psi (t : ℝ) (g : Euc d → ℝ) : ℝ :=
  (mnc_ipL g (Nat.cast_nonneg m) (mnc_u ρ P m t) - mnc_ipL g (Nat.cast_nonneg m) (mnc_u ρ P m 0)) -
    ∫ x in Set.Icc (0 : ℝ) t, mnc_F (β := β) H hm P g x

variable {P}

lemma mnc_hk (hm : (d : ℝ) / 2 + 3 < m) : (d : ℝ) / 2 < ((m - 2 : ℕ) : ℝ) ∧ ((m - 2 : ℕ) : ℝ) = (m : ℝ) - 2 := by
  have h3 : 3 ≤ m := by
    have : (3 : ℝ) < m := by have := Nat.cast_nonneg (α := ℝ) d; linarith
    exact_mod_cast this.le
  have hc : ((m - 2 : ℕ) : ℝ) = (m : ℝ) - 2 := by
    rw [Nat.cast_sub (by omega)]; norm_num
  exact ⟨by rw [hc]; linarith, hc⟩

lemma mnc_F_cont {r c₀ : ℝ} {f0 : Euc d → ℝ} (hcls : MovInSmallClass d s q β ρ m r c₀ f0 P) (g : Euc d → ℝ)
    (t : ℝ) (ht : 0 ≤ t) : ContinuousOn (mnc_F (β := β) H hm P g) (Set.Icc 0 t) := by
  have hu : ContinuousOn (mnc_u ρ P m) (Set.Icc 0 t) := hcls.cont.mono Set.Icc_subset_Ici_self
  unfold mnc_F
  refine ContinuousOn.add (ContinuousOn.sub ?_ ?_) ?_
  · exact ((mnc_ipL _ _).continuous.comp_continuousOn hu).neg
  · exact (mnc_ipL _ _).continuous.comp_continuousOn ((mov2d_R d s β q ρ (m : ℝ)).continuous.comp_continuousOn hu)
  · have hB : ContinuousOn (fun x => mov_B_ext H hm (mnc_u ρ P m x)) (Set.Icc 0 t) :=
      (mov_B_ext H hm).continuous.comp_continuousOn hu
    exact (mnc_ipL _ _).continuous.comp_continuousOn (hB.clm_apply hu)

lemma mnc_ipL_sub (hm : (d : ℝ) / 2 + 3 < m) {g1 g2 : Euc d → ℝ} (h1 : MemLp g1 2 (volume : Measure (Euc d)))
    (h2 : MemLp g2 2 (volume : Measure (Euc d))) {r : ℝ} (hr : (((m - 2 : ℕ) : ℝ)) ≤ r) (h0 : 0 ≤ r)
    (x : OscSpace d r) :
    mnc_ipL (fun y => g1 y - g2 y) h0 x = mnc_ipL g1 h0 x - mnc_ipL g2 h0 x := by
  obtain ⟨C, -, h⟩ := mnc_ipL_repr (d := d) (mnc_hk hm).1
  obtain ⟨f, hf, -, hrep⟩ := h hr h0 x
  have i1 : Integrable (fun y => g1 y * f y) := h1.integrable_mul hf
  have i2 : Integrable (fun y => g2 y * f y) := h2.integrable_mul hf
  rw [hrep _ (show MemLp (fun y => g1 y - g2 y) 2 (volume : Measure (Euc d)) from h1.sub h2), hrep g1 h1, hrep g2 h2,
    ← integral_sub i1 i2]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp only
  ring

lemma mnc_a_le (H : Mov2dTh d s β q ρ) (hm : (d : ℝ) / 2 + 3 < m) : ((m - 2 : ℕ) : ℝ) ≤ (m : ℝ) - movA d s := by
  rw [(mnc_hk hm).2]
  have := (mov2d_a_bounds d H.hd H.hsd).2
  linarith

lemma mnc_F_sub {g1 g2 : Euc d → ℝ} (h1 : mnc_Good d β q g1) (h2 : mnc_Good d β q g2) (x : ℝ) :
    mnc_F (β := β) H hm P (fun y => g1 y - g2 y) x = mnc_F (β := β) H hm P g1 x - mnc_F (β := β) H hm P g2 x := by
  have hk0 : (((m - 2 : ℕ) : ℝ)) ≤ (m : ℝ) := by rw [(mnc_hk hm).2]; linarith
  unfold mnc_F
  rw [mnc_S0_sub_fun h1.smooth h2.smooth, mnc_ipL_sub hm h1.s2 h2.s2 hk0,
    mnc_ipL_sub hm h1.l2 h2.l2 (mnc_a_le H hm), mnc_ipL_sub hm h1.l2 h2.l2 (mnc_a_le H hm)]
  ring


lemma mnc_Psi_sub {r c₀ : ℝ} {f0 : Euc d → ℝ} (hcls : MovInSmallClass d s q β ρ m r c₀ f0 P) {t : ℝ} (ht : 0 ≤ t)
    {g1 g2 : Euc d → ℝ} (h1 : mnc_Good d β q g1) (h2 : mnc_Good d β q g2) :
    mnc_Psi (β := β) H hm P t (fun y => g1 y - g2 y) = mnc_Psi (β := β) H hm P t g1 - mnc_Psi (β := β) H hm P t g2 := by
  have hk0 : (((m - 2 : ℕ) : ℝ)) ≤ (m : ℝ) := by rw [(mnc_hk hm).2]; linarith
  unfold mnc_Psi
  have i1 := (mnc_F_cont H hm hcls g1 t ht).integrableOn_Icc (μ := (volume : Measure ℝ))
  have i2 := (mnc_F_cont H hm hcls g2 t ht).integrableOn_Icc (μ := (volume : Measure ℝ))
  rw [mnc_ipL_sub hm h1.l2 h2.l2 hk0, mnc_ipL_sub hm h1.l2 h2.l2 hk0]
  have : ∫ x in Set.Icc (0 : ℝ) t, mnc_F (β := β) H hm P (fun y => g1 y - g2 y) x =
      (∫ x in Set.Icc (0 : ℝ) t, mnc_F (β := β) H hm P g1 x) - ∫ x in Set.Icc (0 : ℝ) t, mnc_F (β := β) H hm P g2 x := by
    rw [← integral_sub i1 i2]
    exact setIntegral_congr_fun measurableSet_Icc (fun x _ => mnc_F_sub H hm h1 h2 x)
  rw [this]
  ring

/-- The `L¹` bound of the defect functional. -/
lemma mnc_Psi_bound {r c₀ : ℝ} {f0 : Euc d → ℝ} (hcls : MovInSmallClass d s q β ρ m r c₀ f0 P) {t : ℝ} (ht : 0 ≤ t) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ g : Euc d → ℝ, mnc_Good d β q g →
      |mnc_Psi (β := β) H hm P t g| ≤ C * ((∫ y, |g y|) + ∫ y, |mov_S0 d β q g y|) := by
  have hk := mnc_hk hm
  obtain ⟨Ck, hCk, hL⟩ := mnc_ipL_L1 (d := d) hk.1
  have hu : ContinuousOn (mnc_u ρ P m) (Set.Icc 0 t) := hcls.cont.mono Set.Icc_subset_Ici_self
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := t)).exists_bound_of_continuousOn hu
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 ⟨le_rfl, ht⟩)
  obtain ⟨KB, hKB0, hKB⟩ := mov_B_ext_bound H hm
  set Rn : ℝ := ‖mov2d_R d s β q ρ (m : ℝ)‖ with hRn
  have hk0 : (((m - 2 : ℕ) : ℝ)) ≤ (m : ℝ) := by rw [hk.2]; linarith
  have hka := mnc_a_le H hm
  refine ⟨2 * Ck * M + t * (Ck * M + Ck * Rn * M + Ck * KB * M * M), by positivity, fun g hg => ?_⟩
  set A : ℝ := ∫ y, |g y| with hA
  set S : ℝ := ∫ y, |mov_S0 d β q g y| with hS
  have hA0 : 0 ≤ A := integral_nonneg fun _ => abs_nonneg _
  have hS0 : 0 ≤ S := integral_nonneg fun _ => abs_nonneg _
  have bL : ∀ x ∈ Set.Icc (0 : ℝ) t, |mnc_ipL g (Nat.cast_nonneg m) (mnc_u ρ P m x)| ≤ Ck * M * A := by
    intro x hx
    refine (hL hk0 _ _ g hg.l2 hg.l1).trans ?_
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hM x hx) hCk) hA0
  have bF : ∀ x ∈ Set.Icc (0 : ℝ) t, ‖mnc_F (β := β) H hm P g x‖ ≤
      Ck * M * S + Ck * Rn * M * A + Ck * KB * M * M * A := by
    intro x hx
    have b1 : |mnc_ipL (mov_S0 d β q g) (Nat.cast_nonneg m) (mnc_u ρ P m x)| ≤ Ck * M * S := by
      refine (hL hk0 _ _ _ hg.s2 hg.s1).trans ?_
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hM x hx) hCk) hS0
    have b2 : |mnc_ipL g (mnb_sub_a_nonneg H hm) (mov2d_R d s β q ρ (m : ℝ) (mnc_u ρ P m x))| ≤
        Ck * Rn * M * A := by
      refine (hL hka _ _ g hg.l2 hg.l1).trans ?_
      have : ‖mov2d_R d s β q ρ (m : ℝ) (mnc_u ρ P m x)‖ ≤ Rn * M :=
        ((mov2d_R d s β q ρ (m : ℝ)).le_opNorm _).trans
          (mul_le_mul_of_nonneg_left (hM x hx) (norm_nonneg _))
      calc Ck * ‖mov2d_R d s β q ρ (m : ℝ) (mnc_u ρ P m x)‖ * A ≤ Ck * (Rn * M) * A :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left this hCk) hA0
        _ = _ := by ring
    have b3 : |mnc_ipL g (mnb_sub_a_nonneg H hm) (mov_B_ext H hm (mnc_u ρ P m x) (mnc_u ρ P m x))| ≤
        Ck * KB * M * M * A := by
      refine (hL hka _ _ g hg.l2 hg.l1).trans ?_
      have h1 : ‖mov_B_ext H hm (mnc_u ρ P m x) (mnc_u ρ P m x)‖ ≤ KB * M * M := by
        refine (hKB _ _).trans ?_
        have := hM x hx
        have h0 := norm_nonneg (mnc_u ρ P m x)
        exact mul_le_mul (mul_le_mul_of_nonneg_left this hKB0) this h0 (mul_nonneg hKB0 hM0)
      calc Ck * ‖mov_B_ext H hm (mnc_u ρ P m x) (mnc_u ρ P m x)‖ * A ≤ Ck * (KB * M * M) * A :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 hCk) hA0
        _ = _ := by ring
    unfold mnc_F
    rw [Real.norm_eq_abs]
    set a1 := mnc_ipL (mov_S0 d β q g) (Nat.cast_nonneg m) (mnc_u ρ P m x)
    set a2 := mnc_ipL g (mnb_sub_a_nonneg H hm) (mov2d_R d s β q ρ (m : ℝ) (mnc_u ρ P m x))
    set a3 := mnc_ipL g (mnb_sub_a_nonneg H hm) (mov_B_ext H hm (mnc_u ρ P m x) (mnc_u ρ P m x))
    have e : -a1 - a2 + a3 = (-a1) + (-a2) + a3 := by ring
    rw [e]
    refine (abs_add_three _ _ _).trans ?_
    simp only [abs_neg]
    linarith
  have hI : ‖∫ x in Set.Icc (0 : ℝ) t, mnc_F (β := β) H hm P g x‖ ≤
      (Ck * M * S + Ck * Rn * M * A + Ck * KB * M * M * A) * t := by
    have := norm_setIntegral_le_of_norm_le_const (μ := (volume : Measure ℝ)) (s := Set.Icc (0 : ℝ) t)
      (f := mnc_F (β := β) H hm P g) (C := Ck * M * S + Ck * Rn * M * A + Ck * KB * M * M * A)
      (by simp) bF
    simpa [Real.volume_real_Icc, ht] using this
  have b0 := bL t ⟨ht, le_rfl⟩
  have bz := bL 0 ⟨le_rfl, ht⟩
  rw [mnc_Psi]
  have hsplit : |(mnc_ipL g (Nat.cast_nonneg m) (mnc_u ρ P m t) - mnc_ipL g (Nat.cast_nonneg m) (mnc_u ρ P m 0)) -
      (∫ x in Set.Icc (0 : ℝ) t, mnc_F (β := β) H hm P g x)| ≤
      |mnc_ipL g (Nat.cast_nonneg m) (mnc_u ρ P m t)| + |mnc_ipL g (Nat.cast_nonneg m) (mnc_u ρ P m 0)| +
        ‖∫ x in Set.Icc (0 : ℝ) t, mnc_F (β := β) H hm P g x‖ := by
    refine (abs_sub _ _).trans ?_
    gcongr
    · exact abs_sub _ _
    · rfl
  refine hsplit.trans ?_
  have hRn0 : 0 ≤ Rn := norm_nonneg _
  have p1 : 0 ≤ Ck * M * S := by positivity
  have p2 : 0 ≤ t * (Ck * M * A) := by positivity
  have p3 : 0 ≤ t * (Ck * Rn * M * S) := by positivity
  have p4 : 0 ≤ t * (Ck * KB * M * M * S) := by positivity
  nlinarith [p1, p2, p3, p4, b0, bz, hI]

end Psi

end HRS.MS.Mov63
