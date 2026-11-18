import HRS.Equilibrium.Parametrix.PX1AuxChart

/-!
# Prop 4.13 parametrix, packet PX1: multiplication of conormal kernels by smooth kernels

A Leibniz rule for the bounds `|D^{a+c} f (u_1, 0, ..., 0, v_c)|` on mixed patterns (`TB`), proved
by peeling one derivative at a time, and `conormal_mul_smooth` as its consequence.
-/

open MeasureTheory Filter Topology
noncomputable section

namespace HRS.Parx

variable {d : ℕ}

/-- `|D^{a+c} f(q)|` is bounded by `W` on the patterns of type `(a, c)` (`a` slots in the first factor,
`c` slots in the second factor), with the norms of the entries as weights. -/
def TB (f : Euc d × Euc d → ℝ) (q : Euc d × Euc d) (a c : ℕ) (W : ℝ) : Prop :=
  ∀ (u : Fin a → Euc d) (v : Fin c → Euc d),
    |iteratedFDeriv ℝ (a + c) f q (pat u v)| ≤ W * (∏ i, ‖u i‖) * ∏ j, ‖v j‖

theorem pat_eq_snoc_right {a c : ℕ} (u : Fin a → Euc d) (v : Fin (c + 1) → Euc d) :
    pat u v = (Fin.snoc (pat u (Fin.init v)) ((0 : Euc d), v (Fin.last c)) :
      Fin (a + c + 1) → Euc d × Euc d) := by
  have := pat_snoc_right u (Fin.init v) (v (Fin.last c))
  rw [Fin.snoc_init_self] at this
  exact this

theorem prod_norm_snoc {c : ℕ} (v : Fin c → Euc d) (h : Euc d) :
    ∏ j, ‖(Fin.snoc v h : Fin (c + 1) → Euc d) j‖ = (∏ j, ‖v j‖) * ‖h‖ := by
  rw [Fin.prod_univ_castSucc]
  simp

theorem prod_norm_init {c : ℕ} (v : Fin (c + 1) → Euc d) :
    ∏ j, ‖v j‖ = (∏ j, ‖Fin.init v j‖) * ‖v (Fin.last c)‖ := by
  rw [Fin.prod_univ_castSucc]
  rfl

theorem contDiffOn_dirD {U : Set (Euc d × Euc d)} (hU : IsOpen U) {k : ℕ} {A : Euc d × Euc d → ℝ}
    (hA : ContDiffOn ℝ ((k + 1 : ℕ) : WithTop ℕ∞) A U) (η : Euc d × Euc d) :
    ContDiffOn ℝ (k : WithTop ℕ∞) (dirD η A) U :=
  (hA.fderiv_of_isOpen hU (m := k) (by norm_cast)).clm_apply contDiffOn_const

theorem norm_iteratedFDeriv_dirD_le {k : ℕ} {A : Euc d × Euc d → ℝ} {q : Euc d × Euc d}
    (hA : ContDiffAt ℝ ((k + 1 : ℕ) : WithTop ℕ∞) A q) (η : Euc d × Euc d) :
    ‖iteratedFDeriv ℝ k (dirD η A) q‖ ≤ ‖iteratedFDeriv ℝ (k + 1) A q‖ * ‖η‖ := by
  refine ContinuousMultilinearMap.opNorm_le_bound (by positivity) fun w => ?_
  rw [iteratedFDeriv_dirD hA η w]
  have h1 := (iteratedFDeriv ℝ (k + 1) A q).le_opNorm (Fin.snoc w η : Fin (k + 1) → Euc d × Euc d)
  rw [Fin.prod_univ_castSucc] at h1
  simp only [Fin.snoc_castSucc, Fin.snoc_last] at h1
  calc ‖(iteratedFDeriv ℝ (k + 1) A q) (Fin.snoc w η)‖
      ≤ ‖iteratedFDeriv ℝ (k + 1) A q‖ * ((∏ i : Fin k, ‖w i‖) * ‖η‖) := h1
    _ = _ := by ring

theorem peel_mul {U : Set (Euc d × Euc d)} (hU : IsOpen U) {q : Euc d × Euc d} (hq : q ∈ U) {k : ℕ}
    {A F : Euc d × Euc d → ℝ} (hA : ContDiffOn ℝ ((k + 1 : ℕ) : WithTop ℕ∞) A U)
    (hF : ContDiffOn ℝ ((k + 1 : ℕ) : WithTop ℕ∞) F U) (η : Euc d × Euc d) (w : Fin k → Euc d × Euc d) :
    iteratedFDeriv ℝ (k + 1) (fun p => A p * F p) q (Fin.snoc w η) =
      iteratedFDeriv ℝ k (fun p => dirD η A p * F p) q w +
        iteratedFDeriv ℝ k (fun p => A p * dirD η F p) q w := by
  have hAF : ContDiffAt ℝ ((k + 1 : ℕ) : WithTop ℕ∞) (fun p => A p * F p) q :=
    (hA.mul hF).contDiffAt (hU.mem_nhds hq)
  rw [← iteratedFDeriv_dirD hAF η w]
  have hev : dirD η (fun p => A p * F p) =ᶠ[𝓝 q]
      (fun p => dirD η A p * F p) + (fun p => A p * dirD η F p) := by
    filter_upwards [hU.mem_nhds hq] with p hp
    have hAd : DifferentiableAt ℝ A p :=
      (hA.differentiableOn (by exact_mod_cast Nat.succ_ne_zero k)).differentiableAt (hU.mem_nhds hp)
    have hFd : DifferentiableAt ℝ F p :=
      (hF.differentiableOn (by exact_mod_cast Nat.succ_ne_zero k)).differentiableAt (hU.mem_nhds hp)
    simp only [dirD, Pi.add_apply]
    have hm : HasFDerivAt (fun p => A p * F p) (A p • fderiv ℝ F p + F p • fderiv ℝ A p) p :=
      hAd.hasFDerivAt.mul hFd.hasFDerivAt
    rw [hm.fderiv]
    simp
    ring
  rw [(hev.iteratedFDeriv ℝ k).eq_of_nhds]
  have h1 : ContDiffAt ℝ (k : WithTop ℕ∞) (fun p => dirD η A p * F p) q :=
    ((contDiffOn_dirD hU hA η).mul (hF.of_le (by exact_mod_cast Nat.le_succ k))).contDiffAt
      (hU.mem_nhds hq)
  have h2 : ContDiffAt ℝ (k : WithTop ℕ∞) (fun p => A p * dirD η F p) q :=
    ((hA.of_le (by exact_mod_cast Nat.le_succ k)).mul (contDiffOn_dirD hU hF η)).contDiffAt
      (hU.mem_nhds hq)
  rw [iteratedFDeriv_add_apply h1 h2]
  rfl

theorem tb_dirD_snd {F : Euc d × Euc d → ℝ} {q : Euc d × Euc d} {i j : ℕ} {W : ℝ} (h : Euc d)
    (hF : ContDiffAt ℝ ((i + j + 1 : ℕ) : WithTop ℕ∞) F q) (hT : TB F q i (j + 1) W) :
    TB (dirD ((0 : Euc d), h) F) q i j (W * ‖h‖) := by
  intro u v
  rw [iteratedFDeriv_dirD hF, ← pat_snoc_right] 
  have := hT u (Fin.snoc v h)
  rw [prod_norm_snoc] at this
  calc _ ≤ _ := this
    _ = _ := by ring

theorem tb_dirD_fst {F : Euc d × Euc d → ℝ} {q : Euc d × Euc d} {i : ℕ} {W : ℝ} (h : Euc d)
    (hF : ContDiffAt ℝ ((i + 0 + 1 : ℕ) : WithTop ℕ∞) F q) (hT : TB F q (i + 1) 0 W) :
    TB (dirD (h, (0 : Euc d)) F) q i 0 (W * ‖h‖) := by
  intro u v
  have hv : v = Fin.elim0 := Subsingleton.elim _ _
  subst hv
  rw [iteratedFDeriv_dirD (n := i + 0) hF, ← pat_snoc_left]
  have := hT (Fin.snoc u h) Fin.elim0
  have e : ∏ k : Fin (i + 1), ‖(Fin.snoc u h : Fin (i + 1) → Euc d) k‖ = (∏ k, ‖u k‖) * ‖h‖ :=
    prod_norm_snoc u h
  rw [e] at this
  calc _ ≤ _ := this
    _ = _ := by ring

theorem sum_aux (f : ℕ → ℝ) (hf : ∀ j, 0 ≤ f j) (m : ℕ) :
    ∑ j ∈ Finset.range (m + 1), f j + ∑ j ∈ Finset.range (m + 1), f (j + 1) ≤
      2 * ∑ j ∈ Finset.range (m + 2), f j := by
  have h1 : ∑ j ∈ Finset.range (m + 1), f j ≤ ∑ j ∈ Finset.range (m + 2), f j := by
    rw [Finset.sum_range_succ f (m + 1)]; linarith [hf (m + 1)]
  have h2 : ∑ j ∈ Finset.range (m + 1), f (j + 1) ≤ ∑ j ∈ Finset.range (m + 2), f j := by
    rw [Finset.sum_range_succ' f (m + 1)]; linarith [hf 0]
  linarith

set_option maxHeartbeats 1000000 in
/-- Leibniz for typed derivative bounds. -/
theorem leibniz_TB {U : Set (Euc d × Euc d)} (hU : IsOpen U) {q : Euc d × Euc d} (hq : q ∈ U) :
    ∀ (n a c : ℕ), a + c = n → ∀ (A F : Euc d × Euc d → ℝ) (α : ℝ) (W : ℕ → ℕ → ℝ),
      0 ≤ α → (∀ i j, 0 ≤ W i j) →
      ContDiffOn ℝ (n : WithTop ℕ∞) A U → ContDiffOn ℝ (n : WithTop ℕ∞) F U →
      (∀ k ≤ n, ‖iteratedFDeriv ℝ k A q‖ ≤ α) →
      (∀ i ≤ a, ∀ j ≤ c, TB F q i j (W i j)) →
      TB (fun p => A p * F p) q a c
        (2 ^ n * α * ∑ j ∈ Finset.range (c + 1), ∑ i ∈ Finset.range (a + 1), W i j) := by
  intro n
  induction n with
  | zero =>
    intro a c hac A F α W hα hW hA hF hAk hFt
    obtain ⟨rfl, rfl⟩ : a = 0 ∧ c = 0 := by omega
    intro u v
    have h1 := hFt 0 le_rfl 0 le_rfl u v
    have h2 := hAk 0 le_rfl
    simp only [norm_iteratedFDeriv_zero] at h1 h2 ⊢
    simp at h1 ⊢
    have : 0 ≤ W 0 0 := hW 0 0
    calc |A q| * |F q| ≤ α * W 0 0 :=
          mul_le_mul (by simpa using h2) h1 (abs_nonneg _) hα
      _ = _ := by simp
  | succ n ih =>
    intro a c hac A F α W hα hW hA hF hAk hFt
    have hAn : ContDiffOn ℝ (n : WithTop ℕ∞) A U := hA.of_le (by exact_mod_cast Nat.le_succ n)
    have hFn : ContDiffOn ℝ (n : WithTop ℕ∞) F U := hF.of_le (by exact_mod_cast Nat.le_succ n)
    have hAat : ContDiffAt ℝ ((n + 1 : ℕ) : WithTop ℕ∞) A q := hA.contDiffAt (hU.mem_nhds hq)
    have hFat : ContDiffAt ℝ ((n + 1 : ℕ) : WithTop ℕ∞) F q := hF.contDiffAt (hU.mem_nhds hq)
    -- bounds for the derivative of `A` in the direction `η`
    have hAk' : ∀ η : Euc d × Euc d, ∀ k ≤ n,
        ‖iteratedFDeriv ℝ k (dirD η A) q‖ ≤ α * ‖η‖ := by
      intro η k hk
      have hAk1 : ContDiffAt ℝ ((k + 1 : ℕ) : WithTop ℕ∞) A q :=
        hAat.of_le (by exact_mod_cast Nat.succ_le_succ hk)
      refine (norm_iteratedFDeriv_dirD_le hAk1 η).trans ?_
      exact mul_le_mul_of_nonneg_right (hAk (k + 1) (Nat.succ_le_succ hk)) (norm_nonneg _)
    cases c with
    | zero =>
      obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨n, by omega⟩
      obtain rfl : a' = n := by omega
      intro u v
      have hv : v = Fin.elim0 := Subsingleton.elim _ _
      subst hv
      set h := u (Fin.last a') with hh
      set u' := Fin.init u with hu'
      set η : Euc d × Euc d := (h, 0) with hη
      have hpat : pat u (Fin.elim0 : Fin 0 → Euc d) =
          (Fin.snoc (pat u' (Fin.elim0 : Fin 0 → Euc d)) η : Fin (a' + 0 + 1) → Euc d × Euc d) := by
        have := pat_snoc_left u' h
        rw [hu', hh, Fin.snoc_init_self] at this
        exact this
      have hnη : ‖η‖ = ‖h‖ := by simp [hη]
      rw [hpat, peel_mul hU hq hA hF η (pat u' (Fin.elim0 : Fin 0 → Euc d))]
      have hα' : 0 ≤ α * ‖h‖ := mul_nonneg hα (norm_nonneg _)
      have I1 := ih a' 0 (by omega) (dirD η A) F (α * ‖h‖) W hα' hW (contDiffOn_dirD hU hA η) hFn
        (fun k hk => by rw [← hnη]; exact hAk' η k hk)
        (fun i hi j hj => hFt i (by omega) j hj) u' (Fin.elim0 : Fin 0 → Euc d)
      have I2 := ih a' 0 (by omega) A (dirD η F) α (fun i j => ‖h‖ * W (i + 1) j) hα
        (fun i j => mul_nonneg (norm_nonneg _) (hW _ _)) hAn (contDiffOn_dirD hU hF η)
        (fun k hk => hAk k (by omega))
        (fun i hi j hj => by
          obtain rfl : j = 0 := Nat.le_zero.mp hj
          have := tb_dirD_fst (F := F) (q := q) (i := i) h (hFat.of_le (by exact_mod_cast (by omega : i + 0 + 1 ≤ a' + 1)))
            (hFt (i + 1) (by omega) 0 le_rfl)
          rw [mul_comm] at this
          exact this) u' (Fin.elim0 : Fin 0 → Euc d)
      refine (abs_add_le _ _).trans ?_
      have e0 : ∏ j : Fin 0, ‖(Fin.elim0 j : Euc d)‖ = 1 := by simp
      have hprod : ∏ i, ‖u i‖ = (∏ i, ‖u' i‖) * ‖h‖ := prod_norm_init u
      rw [e0] at I1 I2 ⊢
      simp only [zero_add, Finset.sum_range_one, ← Finset.mul_sum] at I1 I2 ⊢
      have key := sum_aux (fun i => W i 0) (fun i => hW i 0) a'
      have hP : 0 ≤ ∏ i, ‖u' i‖ := Finset.prod_nonneg fun i _ => norm_nonneg _
      have hpos : 0 ≤ 2 ^ a' * α * ‖h‖ * ∏ i, ‖u' i‖ :=
        mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg (by norm_num) _) hα) (norm_nonneg _)) hP
      calc _ ≤ ((2 ^ a' * (α * ‖h‖) * ∑ i ∈ Finset.range (a' + 1), W i 0) * ∏ i, ‖u' i‖) * 1 +
            ((2 ^ a' * α * (‖h‖ * ∑ i ∈ Finset.range (a' + 1), W (i + 1) 0)) * ∏ i, ‖u' i‖) * 1 :=
            add_le_add I1 I2
        _ = (2 ^ a' * α * ‖h‖ * ∏ i, ‖u' i‖) *
            (∑ i ∈ Finset.range (a' + 1), W i 0 + ∑ i ∈ Finset.range (a' + 1), W (i + 1) 0) := by ring
        _ ≤ (2 ^ a' * α * ‖h‖ * ∏ i, ‖u' i‖) * (2 * ∑ i ∈ Finset.range (a' + 1 + 1), W i 0) :=
            mul_le_mul_of_nonneg_left key hpos
        _ = _ := by rw [hprod]; ring
    | succ c' =>
      obtain rfl : n = a + c' := by omega
      intro u v
      set h := v (Fin.last c') with hh
      set v' := Fin.init v with hv'
      set η : Euc d × Euc d := ((0 : Euc d), h) with hη
      have hnη : ‖η‖ = ‖h‖ := by simp [hη]
      have hpat := pat_eq_snoc_right u v
      show |iteratedFDeriv ℝ (a + c' + 1) (fun p => A p * F p) q (pat (a := a) (c := c' + 1) u v)| ≤ _
      rw [hpat]
      rw [peel_mul hU hq hA hF η (pat u v')]
      have hα' : 0 ≤ α * ‖h‖ := mul_nonneg hα (norm_nonneg _)
      have I1 := ih a c' rfl (dirD η A) F (α * ‖h‖) W hα' hW (contDiffOn_dirD hU hA η) hFn
        (fun k hk => by rw [← hnη]; exact hAk' η k hk)
        (fun i hi j hj => hFt i hi j (by omega)) u v'
      have I2 := ih a c' rfl A (dirD η F) α (fun i j => ‖h‖ * W i (j + 1)) hα
        (fun i j => mul_nonneg (norm_nonneg _) (hW _ _)) hAn (contDiffOn_dirD hU hF η)
        (fun k hk => hAk k (by omega))
        (fun i hi j hj => by
          have := tb_dirD_snd (F := F) (q := q) (i := i) (j := j) h
            (hFat.of_le (by exact_mod_cast (by omega : i + j + 1 ≤ a + c' + 1)))
            (hFt i hi (j + 1) (by omega))
          rw [mul_comm] at this
          exact this) u v'
      refine (abs_add_le _ _).trans ?_
      have hprod : ∏ j, ‖v j‖ = (∏ j, ‖v' j‖) * ‖h‖ := prod_norm_init v
      let S : ℕ → ℝ := fun j => ∑ i ∈ Finset.range (a + 1), W i j
      have key := sum_aux S (fun j => Finset.sum_nonneg fun i _ => hW i j) c'
      have hP1 : 0 ≤ ∏ i, ‖u i‖ := Finset.prod_nonneg fun i _ => norm_nonneg _
      have hP2 : 0 ≤ ∏ j, ‖v' j‖ := Finset.prod_nonneg fun i _ => norm_nonneg _
      have hpos : 0 ≤ 2 ^ (a + c') * α * ‖h‖ * ((∏ i, ‖u i‖) * ∏ j, ‖v' j‖) :=
        mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg (by norm_num) _) hα) (norm_nonneg _))
          (mul_nonneg hP1 hP2)
      have e2 : ∑ j ∈ Finset.range (c' + 1), ∑ i ∈ Finset.range (a + 1), ‖h‖ * W i (j + 1) =
          ‖h‖ * ∑ j ∈ Finset.range (c' + 1), S (j + 1) := by
        simp only [S, Finset.mul_sum]
      rw [e2] at I2
      calc _ ≤ ((2 ^ (a + c') * (α * ‖h‖) * ∑ j ∈ Finset.range (c' + 1), S j) * ∏ i, ‖u i‖) *
            ∏ j, ‖v' j‖ +
            ((2 ^ (a + c') * α * (‖h‖ * ∑ j ∈ Finset.range (c' + 1), S (j + 1))) * ∏ i, ‖u i‖) *
            ∏ j, ‖v' j‖ := add_le_add I1 I2
        _ = (2 ^ (a + c') * α * ‖h‖ * ((∏ i, ‖u i‖) * ∏ j, ‖v' j‖)) *
            (∑ j ∈ Finset.range (c' + 1), S j + ∑ j ∈ Finset.range (c' + 1), S (j + 1)) := by ring
        _ ≤ (2 ^ (a + c') * α * ‖h‖ * ((∏ i, ‖u i‖) * ∏ j, ‖v' j‖)) *
            (2 * ∑ j ∈ Finset.range (c' + 1 + 1), S j) := mul_le_mul_of_nonneg_left key hpos
        _ = _ := by rw [hprod]; simp only [S]; ring

theorem norm_chartT_le : ‖chartT d‖ ≤ 2 := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by norm_num) fun p => ?_
  rw [chartT_apply, Prod.norm_def]
  have h1 : ‖p.1‖ ≤ ‖p‖ := norm_fst_le p
  have h2 : ‖p.2‖ ≤ ‖p‖ := norm_snd_le p
  refine max_le ?_ ?_
  · calc ‖p.1 + (1 / 2 : ℝ) • p.2‖ ≤ ‖p.1‖ + ‖(1 / 2 : ℝ) • p.2‖ := norm_add_le _ _
      _ ≤ _ := by rw [norm_smul, Real.norm_of_nonneg (by norm_num)]; linarith [norm_nonneg p]
  · calc ‖p.1 - (1 / 2 : ℝ) • p.2‖ ≤ ‖p.1‖ + ‖(1 / 2 : ℝ) • p.2‖ := norm_sub_le _ _
      _ ≤ _ := by rw [norm_smul, Real.norm_of_nonneg (by norm_num)]; linarith [norm_nonneg p]

theorem norm_iteratedFDeriv_toChart_le {m : ℕ} {a : Torus d → Torus d → ℝ} (ha : PDE.IsCk2 m a)
    {k : ℕ} (hk : k ≤ m) (q : Euc d × Euc d) :
    ‖iteratedFDeriv ℝ k (toChart a) q‖ ≤ 2 ^ k * PDE.cbNorm2 m a := by
  rw [toChart_eq]
  have h := (chartT d).iteratedFDeriv_comp_right (f := lift2 a) ha (q) (i := k)
    (by exact_mod_cast hk)
  rw [h]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  have h1 : ‖iteratedFDeriv ℝ k (lift2 a) (chartT d q)‖ ≤ PDE.cbNorm2 m a :=
    PDE.MFPair.norm_iteratedFDeriv_le_cbNorm2 ha hk _
  have h2 : ∏ _i : Fin k, ‖chartT d‖ ≤ 2 ^ k := by
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    exact pow_le_pow_left₀ (norm_nonneg _) norm_chartT_le k
  calc _ ≤ PDE.cbNorm2 m a * 2 ^ k :=
        mul_le_mul h1 h2 (Finset.prod_nonneg fun _ _ => norm_nonneg _)
          (PDE.MFPair.cbNorm2_nonneg m a)
    _ = _ := by ring

theorem tb_of_norm_le {G : Euc d × Euc d → ℝ} {U : Set (Euc d × Euc d)} (hU : IsOpen U)
    {i j : ℕ} (hG : ContDiffOn ℝ ((i + j : ℕ) : WithTop ℕ∞) G U) {X z : Euc d} (hz : (X, z) ∈ U)
    {W : ℝ} (h : ‖mixedDeriv i j G X z‖ ≤ W) : TB G (X, z) i j W := by
  intro u v
  rw [← mixedDeriv_apply hU hG hz]
  calc _ ≤ ‖mixedDeriv i j G X z‖ * (∏ k, ‖u k‖) * ∏ k, ‖v k‖ := le_norm_nested _ u v
    _ ≤ _ := by
      have hp1 : 0 ≤ ∏ k, ‖u k‖ := Finset.prod_nonneg fun k _ => norm_nonneg _
      have hp2 : 0 ≤ ∏ k, ‖v k‖ := Finset.prod_nonneg fun k _ => norm_nonneg _
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h hp1) hp2

theorem norm_le_of_tb {G : Euc d × Euc d → ℝ} {U : Set (Euc d × Euc d)} (hU : IsOpen U)
    {i j : ℕ} (hG : ContDiffOn ℝ ((i + j : ℕ) : WithTop ℕ∞) G U) {X z : Euc d} (hz : (X, z) ∈ U)
    {W : ℝ} (hW : 0 ≤ W) (h : TB G (X, z) i j W) : ‖mixedDeriv i j G X z‖ ≤ W := by
  refine norm_nested_le_of hW fun u v => ?_
  rw [mixedDeriv_apply hU hG hz]
  exact h u v

theorem near_mul_aux {m : ℕ} {σ : ℝ} {b : ℕ → ℕ} {B : ℝ} {F a : Torus d → Torus d → ℝ}
    (hF : ConormalL σ b m B F) (ha : PDE.IsCk2 m a) {i c : ℕ} (hic : i + c ≤ m) {X z : Euc d}
    (hz : z ≠ 0) (hzr : ‖z‖ < r0) :
    ‖mixedDeriv i c (toChart (fun x y => a x y * F x y)) X z‖ ≤
      (4 ^ m * ((m : ℝ) + 1) ^ 2) * PDE.cbNorm2 m a * B *
        (1 + ‖z‖ ^ (-(σ + c)) * (1 + |Real.log ‖z‖|) ^ ((Finset.range (c + 1)).sup b)) := by
  have hq : (X, z) ∈ Uc d := mem_Uc hz hzr
  have hcb := PDE.MFPair.cbNorm2_nonneg m a
  set r := ‖z‖ with hr
  set L := 1 + |Real.log r| with hL
  have hr0 : 0 < r := norm_pos_iff.mpr hz
  have hr1 : r ≤ 1 := by unfold r0 at hzr; linarith
  have hL1 : 1 ≤ L := by linarith [abs_nonneg (Real.log r)]
  have hL0 : 0 < L := by linarith
  have hB : 0 ≤ B := by
    have h00 := hF.near 0 0 (Nat.zero_le _) X z hz hzr
    have h0 : 0 ≤ ‖mixedDeriv 0 0 (toChart F) X z‖ := ContinuousMultilinearMap.opNorm_nonneg _
    have hw : 0 < 1 + r ^ (-(σ + ((0 : ℕ) : ℝ))) * L ^ (b 0) := by positivity
    by_contra hneg
    rw [not_le] at hneg
    have := mul_neg_of_neg_of_pos hneg hw
    linarith
  -- the data
  have hG : ContDiffOn ℝ ((i + c : ℕ) : WithTop ℕ∞) (toChart F) (Uc d) :=
    (toChart_contDiffOn hF.smooth).of_le (by exact_mod_cast hic)
  have hA : ContDiffOn ℝ ((i + c : ℕ) : WithTop ℕ∞) (toChart a) (Uc d) := by
    rw [toChart_eq]
    exact ((ha.comp (chartT d).contDiff).contDiffOn).of_le (by exact_mod_cast hic)
  set W : ℕ → ℕ → ℝ := fun i' j => B * (1 + r ^ (-(σ + (j : ℝ))) * L ^ (b j)) with hW
  have hW0 : ∀ i' j, 0 ≤ W i' j := fun i' j => by simp only [hW]; positivity
  have hFt : ∀ i' ≤ i, ∀ j ≤ c, TB (toChart F) (X, z) i' j (W i' j) := by
    intro i' hi' j hj
    have hmj : i' + j ≤ m := by omega
    refine tb_of_norm_le isOpen_Uc ?_ hq (hF.near i' j hmj X z hz hzr)
    exact (toChart_contDiffOn hF.smooth).of_le (by exact_mod_cast hmj)
  have hαk : ∀ k ≤ i + c, ‖iteratedFDeriv ℝ k (toChart a) (X, z)‖ ≤ 2 ^ m * PDE.cbNorm2 m a := by
    intro k hk
    refine (norm_iteratedFDeriv_toChart_le ha (hk.trans hic) _).trans ?_
    exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) (hk.trans hic)) hcb
  have hα0 : 0 ≤ 2 ^ m * PDE.cbNorm2 m a := by positivity
  have hLeib := leibniz_TB isOpen_Uc hq (i + c) i c rfl (toChart a) (toChart F)
    (2 ^ m * PDE.cbNorm2 m a) W hα0 hW0 hA hG hαk hFt
  have hAG : ContDiffOn ℝ ((i + c : ℕ) : WithTop ℕ∞)
      (toChart (fun x y => a x y * F x y)) (Uc d) := hA.mul hG
  -- the sum is bounded
  set w' := 1 + r ^ (-(σ + (c : ℝ))) * L ^ ((Finset.range (c + 1)).sup b) with hw'
  have hw'0 : 0 ≤ w' := by simp only [hw']; positivity
  have hWle : ∀ i' j, j ≤ c → W i' j ≤ B * w' := by
    intro i' j hj
    simp only [hW, hw']
    refine mul_le_mul_of_nonneg_left ?_ hB
    have h1 : r ^ (-(σ + (j : ℝ))) ≤ r ^ (-(σ + (c : ℝ))) :=
      Real.rpow_le_rpow_of_exponent_ge hr0 hr1 (by
        have : (j : ℝ) ≤ c := by exact_mod_cast hj
        linarith)
    have h2 : L ^ (b j) ≤ L ^ ((Finset.range (c + 1)).sup b) :=
      pow_le_pow_right₀ hL1 (Finset.le_sup (f := b) (Finset.mem_range.mpr (Nat.lt_succ_of_le hj)))
    have := mul_le_mul h1 h2 (by positivity) (by positivity)
    linarith
  have hS : ∑ j ∈ Finset.range (c + 1), ∑ i' ∈ Finset.range (i + 1), W i' j ≤
      ((c : ℝ) + 1) * (((i : ℝ) + 1) * (B * w')) := by
    calc _ ≤ ∑ j ∈ Finset.range (c + 1), ((i : ℝ) + 1) * (B * w') := by
          refine Finset.sum_le_sum fun j hj => ?_
          have hj' : j ≤ c := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
          calc ∑ i' ∈ Finset.range (i + 1), W i' j ≤ ∑ i' ∈ Finset.range (i + 1), (B * w') :=
                Finset.sum_le_sum fun i' _ => hWle i' j hj'
            _ = _ := by simp
      _ = _ := by simp
  have hbound := norm_le_of_tb isOpen_Uc hAG hq
    (by
      have : 0 ≤ ∑ j ∈ Finset.range (c + 1), ∑ i' ∈ Finset.range (i + 1), W i' j :=
        Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun i' _ => hW0 i' j
      positivity) hLeib
  refine hbound.trans ?_
  have hpow : (2 : ℝ) ^ (i + c) ≤ 2 ^ m := pow_le_pow_right₀ (by norm_num) hic
  have hi1 : ((i : ℝ) + 1) ≤ (m : ℝ) + 1 := by
    have : (i : ℝ) ≤ m := by exact_mod_cast (by omega : i ≤ m)
    linarith
  have hc1 : ((c : ℝ) + 1) ≤ (m : ℝ) + 1 := by
    have : (c : ℝ) ≤ m := by exact_mod_cast (by omega : c ≤ m)
    linarith
  have hBw : 0 ≤ B * w' := mul_nonneg hB hw'0
  calc 2 ^ (i + c) * (2 ^ m * PDE.cbNorm2 m a) *
        ∑ j ∈ Finset.range (c + 1), ∑ i' ∈ Finset.range (i + 1), W i' j
      ≤ 2 ^ m * (2 ^ m * PDE.cbNorm2 m a) * (((m : ℝ) + 1) * (((m : ℝ) + 1) * (B * w'))) := by
        refine mul_le_mul (mul_le_mul_of_nonneg_right hpow hα0) (hS.trans ?_)
          (Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun i' _ => hW0 i' j) (by positivity)
        exact mul_le_mul hc1 (mul_le_mul_of_nonneg_right hi1 hBw) (by positivity) (by positivity)
    _ = _ := by
        have : (4 : ℝ) ^ m = 2 ^ m * 2 ^ m := by
          rw [← mul_pow]; norm_num
        rw [this]; ring

theorem far_mul_aux {m : ℕ} {σ : ℝ} {b : ℕ → ℕ} {B : ℝ} {F a : Torus d → Torus d → ℝ}
    (hF : ConormalL σ b m B F) (ha : PDE.IsCk2 m a) {k : ℕ} (hk : k ≤ m) {p : Euc d × Euc d}
    (hp : p ∈ offDiag d) (hr : r0 ≤ Torus.eucDist (Torus.mk p.1) (Torus.mk p.2)) :
    ‖iteratedFDeriv ℝ k (lift2 (fun x y => a x y * F x y)) p‖ ≤
      (4 ^ m * ((m : ℝ) + 1) ^ 2) * PDE.cbNorm2 m a * B := by
  have hcb := PDE.MFPair.cbNorm2_nonneg m a
  have hB : 0 ≤ B := (norm_nonneg _).trans (hF.far 0 (Nat.zero_le _) p hp hr)
  have hso : UniqueDiffOn ℝ (offDiag d) := isOpen_offDiag.uniqueDiffOn
  have hfa : ContDiffOn ℝ (m : WithTop ℕ∞) (lift2 a) (offDiag d) := ha.contDiffOn
  have e : iteratedFDeriv ℝ k (lift2 (fun x y => a x y * F x y)) p =
      iteratedFDerivWithin ℝ k (fun y => lift2 a y * lift2 F y) (offDiag d) p :=
    (iteratedFDerivWithin_of_isOpen k isOpen_offDiag hp).symm
  rw [e]
  refine (norm_iteratedFDerivWithin_mul_le hfa hF.smooth hso hp (by exact_mod_cast hk)).trans ?_
  have hterm : ∀ i ∈ Finset.range (k + 1),
      (k.choose i : ℝ) * ‖iteratedFDerivWithin ℝ i (lift2 a) (offDiag d) p‖ *
        ‖iteratedFDerivWithin ℝ (k - i) (lift2 F) (offDiag d) p‖ ≤
      (k.choose i : ℝ) * (PDE.cbNorm2 m a * B) := by
    intro i hi
    have hi' : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    rw [iteratedFDerivWithin_of_isOpen i isOpen_offDiag hp,
      iteratedFDerivWithin_of_isOpen (k - i) isOpen_offDiag hp]
    have h1 := PDE.MFPair.norm_iteratedFDeriv_le_cbNorm2 ha (hi'.trans hk) p
    have h2 := hF.far (k - i) ((Nat.sub_le _ _).trans hk) p hp hr
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left (mul_le_mul h1 h2 (norm_nonneg _) hcb) (by positivity)
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [← Finset.sum_mul]
  have hsum : ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) = 2 ^ k := by
    exact_mod_cast Nat.sum_range_choose k
  rw [hsum]
  have hk2 : (2 : ℝ) ^ k ≤ 4 ^ m * ((m : ℝ) + 1) ^ 2 := by
    have h1 : (2 : ℝ) ^ k ≤ 2 ^ m := pow_le_pow_right₀ (by norm_num) hk
    have h2 : (2 : ℝ) ^ m ≤ 4 ^ m := pow_le_pow_left₀ (by norm_num) (by norm_num) m
    have h3 : (1 : ℝ) ≤ ((m : ℝ) + 1) ^ 2 := by
      have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      nlinarith
    calc (2 : ℝ) ^ k ≤ 4 ^ m := h1.trans h2
      _ = 4 ^ m * 1 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left h3 (by positivity)
  have hcbB : 0 ≤ PDE.cbNorm2 m a * B := mul_nonneg hcb hB
  calc 2 ^ k * (PDE.cbNorm2 m a * B) ≤ (4 ^ m * ((m : ℝ) + 1) ^ 2) * (PDE.cbNorm2 m a * B) :=
        mul_le_mul_of_nonneg_right hk2 hcbB
    _ = _ := by ring

/-- Multiplication by a smooth kernel (`conormal_mul_smooth`). -/
theorem conormal_mul_smooth_aux (m : ℕ) (σ : ℝ) (b : ℕ → ℕ) :
    ∃ Cm : ℝ, 0 ≤ Cm ∧ ∀ (B : ℝ) (F a : Torus d → Torus d → ℝ),
      ConormalL σ b m B F → PDE.IsCk2 m a →
        ConormalL σ (fun c => (Finset.range (c + 1)).sup b) m (Cm * PDE.cbNorm2 m a * B)
          (fun x y => a x y * F x y) := by
  refine ⟨4 ^ m * ((m : ℝ) + 1) ^ 2, by positivity, ?_⟩
  intro B F a hF ha
  refine ⟨?_, ?_, ?_⟩
  · exact (ha.contDiffOn (s := offDiag d)).mul hF.smooth
  · intro i c hic X z hz hzr
    exact near_mul_aux hF ha hic hz hzr
  · intro k hk p hp hr
    exact far_mul_aux hF ha hk hp hr

end HRS.Parx

end
