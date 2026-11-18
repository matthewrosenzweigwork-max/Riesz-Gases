import HRS.Whole.Q09AAux6
open MeasureTheory Filter Topology
open scoped ENNReal NNReal ComplexConjugate ContDiff

/-!
# Packet Q09-A, part 7: supports of the Leibniz coefficients, overlap and `L²` bounds

Translation covariance of `coef`, closed supports of the pieces `Th`, the bounded overlap `3^d`, and the
`L²` estimates `l2_sum_overlap`, `l2_coef_sum` used to bound `‖plat · h‖_{H^m}`.
-/

noncomputable section

namespace HRS.Whole.Q09A
open HRS.PDE.ToolboxRd LineDeriv

variable {d : ℕ}

theorem tsupport_dirv_subset (i : Fin d) (f : Euc d → ℂ) : tsupport (dirv i f) ⊆ tsupport f := by
  refine closure_minimal (fun x hx => ?_) (isClosed_tsupport f)
  have h1 : x ∈ Function.support (fderiv ℝ f) := by
    intro h0
    apply hx
    simp [dirv, h0]
  exact support_fderiv_subset ℝ h1

theorem tsupport_coef_subset (i : Fin d) (a : Euc d → ℂ) :
    ∀ j l, tsupport (coef i a j l) ⊆ tsupport a
  | 0, 0 => subset_rfl
  | 0, _ + 1 => by simp [coef]
  | j + 1, 0 => (tsupport_dirv_subset i _).trans (tsupport_coef_subset i a j 0)
  | j + 1, l + 1 => by
    refine (tsupport_add _ _).trans (Set.union_subset ?_ (tsupport_coef_subset i a j l))
    exact (tsupport_dirv_subset i _).trans (tsupport_coef_subset i a j (l + 1))

theorem dirv_translate (i : Fin d) (f : Euc d → ℂ) (c : Euc d) :
    dirv i (fun x => f (x - c)) = fun x => dirv i f (x - c) := by
  ext x
  simp only [dirv]
  rw [fderiv_comp_sub]

theorem coef_translate (i : Fin d) (f : Euc d → ℂ) (c : Euc d) :
    ∀ j l, coef i (fun x => f (x - c)) j l = fun x => coef i f j l (x - c)
  | 0, 0 => rfl
  | 0, _ + 1 => rfl
  | j + 1, 0 => by
    simp only [coef]
    rw [coef_translate i f c j 0, dirv_translate]
  | j + 1, l + 1 => by
    simp only [coef]
    rw [coef_translate i f c j (l + 1), coef_translate i f c j l, dirv_translate]

theorem IsCc.translate {f : Euc d → ℂ} (hf : IsCc f) (c : Euc d) : IsCc (fun x => f (x - c)) :=
  ⟨hf.smooth.comp (contDiff_id.sub contDiff_const),
    hf.supp.comp_homeomorph (Homeomorph.subRight c)⟩


/-- `x` lies in the closed cube carrying the piece `Th d N k` -/
def InBox (d N : ℕ) (k : Fin d → ℕ) (x : Euc d) : Prop :=
  ∀ i, 0 ≤ (d : ℝ) * x i + N - k i ∧ (d : ℝ) * x i + N - k i ≤ 2

theorem Th_ne_zero_inBox {d N : ℕ} {k : Fin d → ℕ} {x : Euc d} (hx : Th d N k x ≠ 0) :
    InBox d N k x := fun i => ⟨(Th_coord hx i).1.le, (Th_coord hx i).2.le⟩

theorem isClosed_inBox (d N : ℕ) (k : Fin d → ℕ) : IsClosed {x : Euc d | InBox d N k x} := by
  have : {x : Euc d | InBox d N k x} = ⋂ i : Fin d, {x : Euc d | 0 ≤ (d : ℝ) * x i + N - k i} ∩
      {x : Euc d | (d : ℝ) * x i + N - k i ≤ 2} := by
    ext x; simp [InBox]
  rw [this]
  refine isClosed_iInter fun i => ?_
  have hc : Continuous fun x : Euc d => (d : ℝ) * x i + N - k i := by fun_prop
  exact (isClosed_le continuous_const hc).inter (isClosed_le hc continuous_const)

theorem inBox_dist {d : ℕ} (hd : 1 ≤ d) {N : ℕ} {k : Fin d → ℕ} {x : Euc d} (hx : InBox d N k x) :
    ‖x - zc d N k‖ ≤ 1 := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hb : ∀ i, |(x - zc d N k) i| ≤ 1 / d := by
    intro i
    obtain ⟨h1, h2⟩ := hx i
    simp only [zc, PiLp.sub_apply]
    have e : (x i - ((k i : ℝ) - N + 1) / d) * d = d * x i - ((k i : ℝ) - N + 1) := by
      field_simp
    rw [abs_le]
    constructor
    · rw [← neg_div, div_le_iff₀ hd0]; linarith
    · rw [le_div_iff₀ hd0]; linarith
  have h2 : ‖x - zc d N k‖ ^ 2 ≤ 1 := by
    rw [EuclideanSpace.norm_sq_eq]
    calc ∑ i, ‖(x - zc d N k) i‖ ^ 2 ≤ ∑ _i : Fin d, (1 / (d : ℝ)) ^ 2 :=
          Finset.sum_le_sum fun i _ => by
            rw [Real.norm_eq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hb i) 2
      _ = 1 / (d : ℝ) := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          field_simp
      _ ≤ 1 := by
          rw [div_le_one hd0]; exact_mod_cast hd
  exact (sq_le_sq₀ (norm_nonneg _) zero_le_one).mp (by simpa using h2)

open Classical in
theorem inBox_overlap (d N : ℕ) (x : Euc d) (B : Finset (Fin d → ℕ)) :
    (B.filter fun k => InBox d N k x).card ≤ 3 ^ d := by
  classical
  set a : Fin d → ℕ := fun i => ⌈(d : ℝ) * x i + N⌉₊ - 2 with ha
  have hsub : B.filter (fun k => InBox d N k x) ⊆
      Fintype.piFinset (fun i => ({a i, a i + 1, a i + 2} : Finset ℕ)) := by
    intro k hk
    rw [Finset.mem_filter] at hk
    rw [Fintype.mem_piFinset]
    intro i
    obtain ⟨h1, h2⟩ := hk.2 i
    have hai : a i = ⌈(d : ℝ) * x i + N⌉₊ - 2 := rfl
    obtain ⟨cn, hcn⟩ : ∃ cn : ℕ, cn = ⌈(d : ℝ) * x i + N⌉₊ := ⟨_, rfl⟩
    rw [← hcn] at hai
    have hc1 : (d : ℝ) * x i + N ≤ cn := by rw [hcn]; exact Nat.le_ceil _
    have hc2 : ∀ n : ℕ, n < cn ↔ (n : ℝ) < (d : ℝ) * x i + N := fun n => by
      rw [hcn]; exact Nat.lt_ceil
    have hlow : a i ≤ k i := by
      by_contra hlt
      push Not at hlt
      have h3 : k i + 2 < cn := by omega
      have h4 := (hc2 _).mp h3
      push_cast at h4
      linarith
    have hup : k i ≤ a i + 2 := by
      have hkc : k i ≤ cn := by exact_mod_cast (by linarith : (k i : ℝ) ≤ cn)
      omega
    simp only [Finset.mem_insert, Finset.mem_singleton]
    omega
  calc (B.filter fun k => InBox d N k x).card
      ≤ (Fintype.piFinset (fun i : Fin d => ({a i, a i + 1, a i + 2} : Finset ℕ))).card :=
        Finset.card_le_card hsub
    _ ≤ 3 ^ d := by
        rw [Fintype.card_piFinset]
        calc ∏ i : Fin d, ({a i, a i + 1, a i + 2} : Finset ℕ).card ≤ ∏ _i : Fin d, 3 :=
              Finset.prod_le_prod' fun i _ => Finset.card_le_three
          _ = 3 ^ d := by simp


open Classical in
theorem l2_sum_overlap {ι : Type*} (B : Finset ι) (F : ι → Euc d → ℂ) (T : ι → Set (Euc d)) (M : ℕ)
    (hF : ∀ k ∈ B, MemLp (F k) 2 volume) (hsupp : ∀ k x, x ∉ T k → F k x = 0)
    (hM : ∀ x, (B.filter fun k => x ∈ T k).card ≤ M) :
    ∫ x, ‖∑ k ∈ B, F k x‖ ^ 2 ≤ (M : ℝ) * ∑ k ∈ B, ∫ x, ‖F k x‖ ^ 2 := by
  have hint : ∀ k ∈ B, Integrable (fun x => ‖F k x‖ ^ 2) volume :=
    fun k hk => (hF k hk).norm.integrable_sq
  have hpt : ∀ x, ‖∑ k ∈ B, F k x‖ ^ 2 ≤ (M : ℝ) * ∑ k ∈ B, ‖F k x‖ ^ 2 := by
    intro x
    set Tx := B.filter fun k => x ∈ T k with hTx
    have e1 : ∑ k ∈ Tx, F k x = ∑ k ∈ B, F k x :=
      Finset.sum_filter_of_ne fun k _ hk => by
        by_contra h; exact hk (hsupp k x h)
    have e2 : ∑ k ∈ Tx, ‖F k x‖ ^ 2 = ∑ k ∈ B, ‖F k x‖ ^ 2 :=
      Finset.sum_filter_of_ne fun k _ hk => by
        by_contra h; exact hk (by simp [hsupp k x h])
    rw [← e1, ← e2]
    calc ‖∑ k ∈ Tx, F k x‖ ^ 2 ≤ (∑ k ∈ Tx, ‖F k x‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2
      _ ≤ (Tx.card : ℝ) * ∑ k ∈ Tx, ‖F k x‖ ^ 2 := sq_sum_le_card_mul_sum_sq
      _ ≤ (M : ℝ) * ∑ k ∈ Tx, ‖F k x‖ ^ 2 := by
          gcongr
          exact_mod_cast hM x
  calc ∫ x, ‖∑ k ∈ B, F k x‖ ^ 2 ≤ ∫ x, (M : ℝ) * ∑ k ∈ B, ‖F k x‖ ^ 2 :=
        integral_mono_of_nonneg (Eventually.of_forall fun x => sq_nonneg _)
          ((integrable_finsetSum _ fun k hk => hint k hk).const_mul _) (Eventually.of_forall hpt)
    _ = (M : ℝ) * ∑ k ∈ B, ∫ x, ‖F k x‖ ^ 2 := by
        rw [integral_const_mul, integral_finsetSum _ fun k hk => hint k hk]


theorem l2_coef_sum {a : Euc d → ℂ} (ha : IsCc a) (i : Fin d) (j : ℕ) (Bc V : ℝ) (hBc : 0 ≤ Bc)
    (G : ℕ → Euc d → ℂ) (hG : ∀ l ≤ j, MemLp (G l) 2 volume)
    (hGV : ∀ l ≤ j, ∫ x, ‖G l x‖ ^ 2 ≤ V)
    (hB : ∀ l ≤ j, ∀ x, ‖coef i a j l x‖ ≤ Bc) :
    MemLp (fun x => ∑ l ∈ Finset.range (j + 1), coef i a j l x * G l x) 2 volume ∧
      ∫ x, ‖∑ l ∈ Finset.range (j + 1), coef i a j l x * G l x‖ ^ 2 ≤ ((j : ℝ) + 1) ^ 2 * Bc ^ 2 * V := by
  have hmem : ∀ l ∈ Finset.range (j + 1), MemLp (fun x => coef i a j l x * G l x) 2 volume :=
    fun l hl => (coef_isCc ha j l).memLp_mul (hG l (by have := Finset.mem_range.mp hl; omega))
  refine ⟨?_, ?_⟩
  · have := memLp_finsetSum' (Finset.range (j + 1)) hmem
    refine this.ae_eq (Eventually.of_forall fun x => ?_)
    simp
  · have hint : ∀ l ≤ j, Integrable (fun x => ‖G l x‖ ^ 2) volume :=
      fun l hl => (hG l hl).norm.integrable_sq
    have hpt : ∀ x, ‖∑ l ∈ Finset.range (j + 1), coef i a j l x * G l x‖ ^ 2 ≤
        ((j : ℝ) + 1) * Bc ^ 2 * ∑ l ∈ Finset.range (j + 1), ‖G l x‖ ^ 2 := by
      intro x
      calc ‖∑ l ∈ Finset.range (j + 1), coef i a j l x * G l x‖ ^ 2
          ≤ (∑ l ∈ Finset.range (j + 1), ‖coef i a j l x * G l x‖) ^ 2 :=
            pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2
        _ ≤ ((Finset.range (j + 1)).card : ℝ) *
              ∑ l ∈ Finset.range (j + 1), ‖coef i a j l x * G l x‖ ^ 2 := sq_sum_le_card_mul_sum_sq
        _ ≤ ((j : ℝ) + 1) * ∑ l ∈ Finset.range (j + 1), Bc ^ 2 * ‖G l x‖ ^ 2 := by
            rw [Finset.card_range]
            push_cast
            gcongr with l hl
            rw [norm_mul, mul_pow]
            have := hB l (by have := Finset.mem_range.mp hl; omega) x
            gcongr
        _ = _ := by rw [← Finset.mul_sum]; ring
    calc ∫ x, ‖∑ l ∈ Finset.range (j + 1), coef i a j l x * G l x‖ ^ 2
        ≤ ∫ x, ((j : ℝ) + 1) * Bc ^ 2 * ∑ l ∈ Finset.range (j + 1), ‖G l x‖ ^ 2 :=
          integral_mono_of_nonneg (Eventually.of_forall fun x => sq_nonneg _)
            ((integrable_finsetSum _ fun l hl => hint l (by have := Finset.mem_range.mp hl; omega)).const_mul _)
            (Eventually.of_forall hpt)
      _ = ((j : ℝ) + 1) * Bc ^ 2 * ∑ l ∈ Finset.range (j + 1), ∫ x, ‖G l x‖ ^ 2 := by
          rw [integral_const_mul, integral_finsetSum _ fun l hl =>
            hint l (by have := Finset.mem_range.mp hl; omega)]
      _ ≤ ((j : ℝ) + 1) * Bc ^ 2 * ∑ _l ∈ Finset.range (j + 1), V := by
          gcongr with l hl
          exact hGV l (by have := Finset.mem_range.mp hl; omega)
      _ = ((j : ℝ) + 1) ^ 2 * Bc ^ 2 * V := by
          simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          push_cast
          ring

end HRS.Whole.Q09A
