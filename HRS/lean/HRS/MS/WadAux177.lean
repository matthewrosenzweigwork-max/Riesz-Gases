import HRS.MS.WadAux176

/-!
# S8.3, packet S8H2-3: `tensorU` of separated data and its jet bound

For `G = ∑_l a_l ⊗ b_l` (`a_l, b_l ∈ C_c^∞`) one has `tensorU U t G = ∑_l U_t a_l ⊗ U_t b_l` (`s8h2_tensor_sep`), and
for `t ∈ [0,T]` the pair jets of `tensorU U t G` of order `≤ j` are bounded by `(2^j K)² N w` whenever those of `G` are bounded by
`N w` (`s8h2_sepZ_jets`, from `s8h2_sep_bound` applied once in each variable).
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal ContDiff Convolution

namespace HRS.MS.Wad

open HRS HRS.Whole

variable {d : ℕ}

theorem s8h2_memCM_sum {M : ℝ} {ι : Type} (s : Finset ι) {lam : ι → ℝ} {f : ι → Euc d → ℝ}
    (hf : ∀ l, MemCM M (f l)) : MemCM M (fun x => ∑ l ∈ s, lam l * f l x) := by
  refine ⟨continuous_finsetSum _ fun l _ => continuous_const.mul (hf l).1, ?_⟩
  have h : Tendsto (fun x => ∑ l ∈ s, lam l * (f l x / jbracket x ^ M)) (cocompact (Euc d))
      (𝓝 (∑ l ∈ s, lam l * 0)) :=
    tendsto_finsetSum _ fun l _ => ((hf l).2.const_mul (lam l))
  simp only [mul_zero, Finset.sum_const_zero] at h
  refine h.congr fun x => ?_
  rw [Finset.sum_div]
  exact Finset.sum_congr rfl fun l _ => by ring

theorem s8h2_cc_memCM (M : ℝ) {φ : Euc d → ℝ} (hφ : S85Cc φ) : MemCM M φ := by
  refine ⟨hφ.1.continuous, ?_⟩
  have hev : ∀ᶠ x in cocompact (Euc d), φ x / jbracket x ^ M = 0 := by
    filter_upwards [hφ.2.compl_mem_cocompact] with x hx
    rw [image_eq_zero_of_notMem_tsupport hx]
    simp
  exact tendsto_const_nhds.congr' (hev.mono fun x hx => hx.symm)

theorem s8h2_cc_lincomb {ι : Type} (s : Finset ι) (lam : ι → ℝ) {b : ι → Euc d → ℝ} (hb : ∀ l, S85Cc (b l)) :
    S85Cc (fun y => ∑ l ∈ s, lam l * b l y) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact ⟨contDiff_const, HasCompactSupport.zero⟩
  | insert l s hl ih =>
    simp only [Finset.sum_insert hl]
    refine ⟨((hb l).1.const_smul (lam l)).add ih.1, ?_⟩
    have h1 : HasCompactSupport (fun y => lam l * b l y) := (hb l).2.mul_left (f := fun _ => lam l)
    exact h1.add ih.2

theorem s8h2_cc_bound {M : ℝ} (hM : 0 ≤ M) {φ : Euc d → ℝ} (hφ : S85Cc φ) (j : ℕ) :
    ∃ N : ℝ, 0 ≤ N ∧ ∀ i ≤ j, ∀ y, ‖iteratedFDeriv ℝ i φ y‖ ≤ N * jbracket y ^ M := by
  have hC : ∀ i : ℕ, ∃ C : ℝ, ∀ y, ‖iteratedFDeriv ℝ i φ y‖ ≤ C := fun i =>
    (hφ.1.continuous_iteratedFDeriv (by exact_mod_cast le_top)).bounded_above_of_compact_support
      (hφ.2.iteratedFDeriv i)
  choose C hC using hC
  refine ⟨∑ i ∈ Finset.range (j + 1), max (C i) 0, Finset.sum_nonneg fun i _ => le_max_right _ _,
    fun i hi y => ?_⟩
  have h1 : C i ≤ ∑ i ∈ Finset.range (j + 1), max (C i) 0 :=
    (le_max_left _ _).trans (Finset.single_le_sum (f := fun i => max (C i) 0)
      (fun i _ => le_max_right _ _) (Finset.mem_range.2 (by omega)))
  have h2 : 1 ≤ jbracket y ^ M := Real.one_le_rpow (s83_one_le_jb y) hM
  have h3 : 0 ≤ ∑ i ∈ Finset.range (j + 1), max (C i) 0 := Finset.sum_nonneg fun i _ => le_max_right _ _
  calc ‖iteratedFDeriv ℝ i φ y‖ ≤ C i := hC i y
    _ ≤ ∑ i ∈ Finset.range (j + 1), max (C i) 0 := h1
    _ = (∑ i ∈ Finset.range (j + 1), max (C i) 0) * 1 := (mul_one _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left h2 h3

section Interface

variable {a β : ℝ} {ρβ : Euc d → ℝ} {M : ℝ} {U : ℝ → (Euc d → ℝ) → Euc d → ℝ}

theorem s8h2_U_sum (hU : IsWeightedSemigroup (critCoeff d a β ρβ) (HRS.Whole.withDensityReal ρβ) M U)
    {t : ℝ} (ht : 0 ≤ t) {ι : Type} (lam : ι → ℝ) {f : ι → Euc d → ℝ} (hf : ∀ l, MemCM M (f l))
    (s : Finset ι) :
    U t (fun x => ∑ l ∈ s, lam l * f l x) = fun x => ∑ l ∈ s, lam l * U t (f l) x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    have h0 : MemCM M (fun _ : Euc d => (0 : ℝ)) := by
      refine ⟨continuous_const, ?_⟩
      simpa using tendsto_const_nhds
    have := hU.smul t ht 0 (fun _ => (0 : ℝ)) h0
    simp only [zero_smul] at this
    exact this
  | insert l s hl ih =>
    simp only [Finset.sum_insert hl]
    have e1 : (fun x => lam l * f l x + ∑ k ∈ s, lam k * f k x) =
        (lam l • f l) + (fun x => ∑ k ∈ s, lam k * f k x) := by
      funext x; simp
    have hm1 : MemCM M (lam l • f l) := by
      have := s8h2_memCM_sum (M := M) ({l} : Finset ι) (lam := lam) hf
      simp only [Finset.sum_singleton] at this
      exact this
    rw [e1, hU.add t ht _ _ hm1 (s8h2_memCM_sum s hf), hU.smul t ht _ _ (hf l), ih]
    funext x
    simp

theorem s8h2_tensor_sep (hU : IsWeightedSemigroup (critCoeff d a β ρβ) (HRS.Whole.withDensityReal ρβ) M U)
    {t : ℝ} (ht : 0 ≤ t) {ι : Type} [Fintype ι] {a' b' : ι → Euc d → ℝ} (ha : ∀ l, S85Cc (a' l))
    (hb : ∀ l, S85Cc (b' l)) (x y : Euc d) :
    tensorU U t (fun x' y' => ∑ l, a' l x' * b' l y') x y = ∑ l, U t (a' l) x * U t (b' l) y := by
  unfold tensorU
  have hbm : ∀ l, MemCM M (b' l) := fun l => s8h2_cc_memCM M (hb l)
  have ham : ∀ l, MemCM M (a' l) := fun l => s8h2_cc_memCM M (ha l)
  have h1 : (fun x' => U t (fun y' => ∑ l, a' l x' * b' l y') y) =
      fun x' => ∑ l, U t (b' l) y * a' l x' := by
    funext x'
    rw [s8h2_U_sum hU ht (fun l => a' l x') hbm Finset.univ]
    exact Finset.sum_congr rfl fun l _ => mul_comm _ _
  rw [h1, s8h2_U_sum hU ht (fun l => U t (b' l) y) ham Finset.univ]
  exact Finset.sum_congr rfl fun l _ => mul_comm _ _

theorem s8h2_P (hU : IsWeightedSemigroup (critCoeff d a β ρβ) (HRS.Whole.withDensityReal ρβ) M U)
    (h3 : S8eC3 M U) (hM : 0 ≤ M) (j : ℕ) {T : ℝ} (hT : 0 ≤ T) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ t ∈ Set.Icc 0 T, ∀ {ι : Type} [Fintype ι] (b : ι → Euc d → ℝ), (∀ l, S85Cc (b l)) →
      ∀ r ≤ j, ∀ lam : ι → ℝ, ∀ {N' : ℝ}, 0 ≤ N' →
        (∀ i ≤ r, ∀ y, ‖iteratedFDeriv ℝ i (fun y => ∑ l, lam l * b l y) y‖ ≤ N' * jbracket y ^ M) →
        ∀ i ≤ r, ∀ y, ‖iteratedFDeriv ℝ i (fun y => ∑ l, lam l * U t (b l) y) y‖ ≤
          K * N' * jbracket y ^ M := by
  have hr : ∀ r : ℕ, ∃ K : ℝ, 0 ≤ K ∧ ∀ t ∈ Set.Icc 0 T, ∀ f, MemCMj M r f → ∀ {N : ℝ}, 0 ≤ N →
      (∀ i ≤ r, ∀ y, ‖iteratedFDeriv ℝ i f y‖ ≤ N * jbracket y ^ M) →
      MemCMj M r (U t f) ∧ ∀ i ≤ r, ∀ y, ‖iteratedFDeriv ℝ i (U t f) y‖ ≤ K * N * jbracket y ^ M :=
    fun r => s8h_Ujet h3 hM r hT
  choose Kr hKr0 hKr using hr
  refine ⟨∑ r ∈ Finset.range (j + 1), Kr r, Finset.sum_nonneg fun r _ => hKr0 r, ?_⟩
  intro t ht ι _ b hb r hr' lam N' hN' hjet i hi y
  have hKle : Kr r ≤ ∑ r ∈ Finset.range (j + 1), Kr r :=
    Finset.single_le_sum (f := Kr) (fun r _ => hKr0 r) (Finset.mem_range.2 (by omega))
  have hf : S85Cc (fun y => ∑ l, lam l * b l y) := s8h2_cc_lincomb Finset.univ lam hb
  have := (hKr r t ht _ (s8h_cc_memCMj M hf r) hN' hjet).2 i hi y
  rw [s8h2_U_sum hU ht.1 lam (fun l => s8h2_cc_memCM M (hb l)) Finset.univ] at this
  refine this.trans ?_
  have : 0 ≤ N' * jbracket y ^ M := mul_nonneg hN' (Real.rpow_nonneg (s83_jb_pos y).le _)
  nlinarith

theorem s8h2_U_cc_smooth (h3 : S8eC3 M U) (hM : 0 ≤ M) (j : ℕ) {T : ℝ} (hT : 0 ≤ T) {t : ℝ}
    (ht : t ∈ Set.Icc 0 T) {φ : Euc d → ℝ} (hφ : S85Cc φ) : ContDiff ℝ j (U t φ) := by
  obtain ⟨K, -, hK⟩ := s8h_Ujet h3 hM j hT
  obtain ⟨N, hN, hb⟩ := s8h2_cc_bound hM hφ j
  exact (hK t ht φ (s8h_cc_memCMj M hφ j) hN hb).1.1

theorem s8h2_sepZ_jets (hU : IsWeightedSemigroup (critCoeff d a β ρβ) (HRS.Whole.withDensityReal ρβ) M U)
    (h3 : S8eC3 M U) (hM : 0 ≤ M) (j : ℕ) {T : ℝ} (hT : 0 ≤ T) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Set.Icc 0 T, ∀ {G : Euc d × Euc d → ℝ}, S8hSepZ G → ∀ {N : ℝ}, 0 ≤ N →
      (∀ i ≤ j, ∀ z, ‖iteratedFDeriv ℝ i G z‖ ≤ N * s8h_w M z) →
      ContDiff ℝ j (Function.uncurry (tensorU U t (fun x y => G (x, y)))) ∧
      ∀ i ≤ j, ∀ z, ‖iteratedFDeriv ℝ i (Function.uncurry (tensorU U t (fun x y => G (x, y)))) z‖ ≤
        C * N * s8h_w M z := by
  obtain ⟨K, hK0, hKP⟩ := s8h2_P hU h3 hM j hT
  refine ⟨(2 ^ j * K) ^ 2, by positivity, fun t ht G hG N hN hjet => ?_⟩
  obtain ⟨ι, _, a', b', hab, rfl⟩ := hG
  have hwt : ∀ x : Euc d, 0 ≤ jbracket x ^ M := fun x => Real.rpow_nonneg (s83_jb_pos x).le _
  have hbC : ∀ l, ContDiff ℝ j (b' l) := fun l => (hab l).2.1.of_le (by exact_mod_cast le_top)
  have haC : ∀ l, ContDiff ℝ j (a' l) := fun l => (hab l).1.1.of_le (by exact_mod_cast le_top)
  have hcC : ∀ l, ContDiff ℝ j (U t (b' l)) := fun l => s8h2_U_cc_smooth h3 hM j hT ht (hab l).2
  have hdC : ∀ l, ContDiff ℝ j (U t (a' l)) := fun l => s8h2_U_cc_smooth h3 hM j hT ht (hab l).1
  have hPb := fun r (hr : r ≤ j) lam {N'} (hN' : 0 ≤ N') hb =>
    hKP t ht b' (fun l => (hab l).2) r hr lam hN' hb
  have hPa := fun r (hr : r ≤ j) lam {N'} (hN' : 0 ≤ N') hb =>
    hKP t ht a' (fun l => (hab l).1) r hr lam hN' hb
  have e : Function.uncurry (tensorU U t (fun x y => ∑ l, a' l x * b' l y)) =
      s8h2_G (fun l => U t (a' l)) (fun l => U t (b' l)) := by
    funext z
    rcases z with ⟨x, y⟩
    exact s8h2_tensor_sep hU ht.1 (fun l => (hab l).1) (fun l => (hab l).2) x y
  have hG0 : ∀ i ≤ j, ∀ z : Euc d × Euc d, ‖iteratedFDeriv ℝ i (s8h2_G a' b') z‖ ≤
      N * (jbracket z.1 ^ M * jbracket z.2 ^ M) := fun i hi z => hjet i hi z
  have h1 := s8h2_sep_bound (wt := fun x : Euc d => jbracket x ^ M) hwt hK0 hbC hcC hPb haC hN hG0
  have hN2 : 0 ≤ 2 ^ j * K * N := by positivity
  have hG2 : ∀ i ≤ j, ∀ z : Euc d × Euc d, ‖iteratedFDeriv ℝ i (s8h2_G (fun l => U t (b' l)) a') z‖ ≤
      2 ^ j * K * N * (jbracket z.1 ^ M * jbracket z.2 ^ M) := by
    intro i hi z
    have es : s8h2_G (fun l => U t (b' l)) a' = (s8h2_G a' (fun l => U t (b' l))) ∘ Prod.swap := by
      funext z'; simp [s8h2_G, mul_comm]
    rw [es, s8h2_swap_jet]
    refine (h1 i hi z.swap).trans ?_
    have h2i : (2 : ℝ) ^ i ≤ 2 ^ j := pow_le_pow_right₀ (by norm_num) hi
    have hp : 0 ≤ jbracket z.1 ^ M * jbracket z.2 ^ M := mul_nonneg (hwt _) (hwt _)
    have : 2 ^ i * K * N ≤ 2 ^ j * K * N := by gcongr
    calc _ = 2 ^ i * K * N * (jbracket z.1 ^ M * jbracket z.2 ^ M) := by
          simp only [Prod.fst_swap, Prod.snd_swap]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right this hp
  have h2 := s8h2_sep_bound (wt := fun x : Euc d => jbracket x ^ M) hwt hK0 haC hdC hPa hcC hN2 hG2
  rw [e]
  refine ⟨s8h2_G_contDiff hdC hcC, fun i hi z => ?_⟩
  have es : s8h2_G (fun l => U t (a' l)) (fun l => U t (b' l)) =
      (s8h2_G (fun l => U t (b' l)) (fun l => U t (a' l))) ∘ Prod.swap := by
    funext z'; simp [s8h2_G, mul_comm]
  rw [es, s8h2_swap_jet]
  refine (h2 i hi z.swap).trans ?_
  have h2i : (2 : ℝ) ^ i ≤ 2 ^ j := pow_le_pow_right₀ (by norm_num) hi
  have hp : 0 ≤ jbracket z.1 ^ M * jbracket z.2 ^ M := mul_nonneg (hwt _) (hwt _)
  have : 2 ^ i * K * (2 ^ j * K * N) ≤ (2 ^ j * K) ^ 2 * N := by
    have : 2 ^ i * K ≤ 2 ^ j * K := by gcongr
    nlinarith [mul_le_mul_of_nonneg_right this (mul_nonneg (by positivity : (0:ℝ) ≤ 2 ^ j * K) hN)]
  calc _ = 2 ^ i * K * (2 ^ j * K * N) * (jbracket z.1 ^ M * jbracket z.2 ^ M) := by
        simp only [Prod.fst_swap, Prod.snd_swap]; ring
    _ ≤ (2 ^ j * K) ^ 2 * N * (jbracket z.1 ^ M * jbracket z.2 ^ M) :=
        mul_le_mul_of_nonneg_right this hp

end Interface

end HRS.MS.Wad
