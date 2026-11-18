import HRS.MS.WadAux184

/-!
# S8.3, packet S8H2-11: the projected generator commutes with time integrals

`s8h2_comm`: for a family `g_s ∈ C²` (`s ∈ [0,T]`) with jets `D^i g_s(x)` (`i ≤ 2`) bounded and jointly continuous, a continuous scalar weight `lam` and
`t ↦ 𝒜 g_t(x)` continuous, the function `Θ = ∫_{(0,T]} lam(s) g_s ds` is `C²`, lies in the weighted class (weight `⟨x⟩`) and
`𝒜Θ(x) = ∫_{(0,T]} lam(s) 𝒜g_s(x) ds`.  Proof: Riemann sums `Θ_n`; weighted uniform continuity in `s` of the jets (`s8h2_wmod`);
linearity (`s8h2_proj_sub`, `s8h2_proj_sum`) and the bound `s8g_gen_bound`.
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal ContDiff RealInnerProductSpace

namespace HRS.MS.Wad

open HRS HRS.Whole

variable {d : ℕ}

theorem s8h2_riemann {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W] {h : ℝ → W}
    {T : ℝ} (hT : 0 < T) (hcont : ContinuousOn h (Set.Icc 0 T)) {δ η : ℝ}
    (hmod : ∀ s ∈ Set.Icc 0 T, ∀ s' ∈ Set.Icc 0 T, |s - s'| ≤ δ → ‖h s - h s'‖ ≤ η) {n : ℕ} (hn : 0 < n)
    (hδ : T / n ≤ δ) :
    ‖(∫ s in Set.Ioc 0 T, h s) - ∑ k ∈ Finset.range n, (T / n) • h (T * ((k : ℝ) + 1) / n)‖ ≤ T * η := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  set a : ℕ → ℝ := fun k => T * k / n with ha
  have ha0 : a 0 = 0 := by simp [ha]
  have hn0 : (n : ℝ) ≠ 0 := hnR.ne'
  have han : a n = T := by simp only [ha]; exact mul_div_cancel_right₀ T hn0
  have hstep : ∀ k, a (k + 1) - a k = T / n := fun k => by simp only [ha]; push_cast; ring
  have hmem : ∀ k ≤ n, a k ∈ Set.Icc 0 T := fun k hk => by
    simp only [ha, Set.mem_Icc]
    have hk' : (k : ℝ) ≤ n := by exact_mod_cast hk
    refine ⟨by positivity, ?_⟩
    rw [div_le_iff₀ hnR]; nlinarith
  have hint : ∀ k < n, IntervalIntegrable h volume (a k) (a (k + 1)) := fun k hk => by
    refine (hcont.mono ?_).intervalIntegrable
    rw [Set.uIcc_of_le]
    · exact Set.Icc_subset_Icc (hmem k hk.le).1 (hmem (k + 1) hk).2
    · have := hstep k; have : 0 < T / n := by positivity
      linarith [hstep k]
  have hsum := intervalIntegral.sum_integral_adjacent_intervals (μ := volume) (f := h) (a := a) (n := n) hint
  rw [ha0, han] at hsum
  have hI : (∫ s in Set.Ioc 0 T, h s) = ∫ s in (0 : ℝ)..T, h s := (intervalIntegral.integral_of_le hT.le).symm
  rw [hI, ← hsum, ← Finset.sum_sub_distrib]
  have hk : ∀ k ∈ Finset.range n, ‖(∫ s in a k..a (k + 1), h s) - (T / n) • h (T * ((k : ℝ) + 1) / n)‖ ≤ η * (T / n) := by
    intro k hk
    have hk' : k < n := Finset.mem_range.1 hk
    have e : (T / n) • h (T * ((k : ℝ) + 1) / n) = ∫ s in a k..a (k + 1), h (a (k + 1)) := by
      rw [intervalIntegral.integral_const, hstep k]
      simp only [ha]; push_cast; try rfl
    rw [e, ← intervalIntegral.integral_sub (hint k hk') intervalIntegrable_const]
    have hle : a k ≤ a (k + 1) := by linarith [hstep k, show 0 < T / n by positivity]
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := a k) (b := a (k + 1))
      (f := fun s => h s - h (a (k + 1))) (C := η) (fun s hs => by
        rw [Set.uIoc_of_le hle] at hs
        refine hmod s ⟨?_, ?_⟩ (a (k + 1)) (hmem (k + 1) hk') ?_
        · exact (hmem k hk'.le).1.trans hs.1.le
        · exact hs.2.trans (hmem (k + 1) hk').2
        · rw [abs_of_nonpos (by linarith [hs.2])]
          have := hstep k
          linarith [hs.1, hs.2])
    rw [abs_of_nonneg (by linarith [hstep k, show 0 < T / n by positivity])] at this
    rw [hstep k] at this
    exact this
  refine (norm_sum_le _ _).trans ((Finset.sum_le_sum hk).trans ?_)
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have : (n : ℝ) * (η * (T / n)) = T * η := by
    calc (n : ℝ) * (η * (T / n)) = T * η * ((n : ℝ) / n) := by ring
      _ = T * η := by rw [div_self hn0, mul_one]
  exact le_of_eq this

theorem s8h2_wmod {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] {H : ℝ × Euc d → W} {T : ℝ}
    (hc : ContinuousOn H (Set.Icc 0 T ×ˢ Set.univ)) {B : ℝ} (hB : ∀ s ∈ Set.Icc 0 T, ∀ x, ‖H (s, x)‖ ≤ B)
    {η : ℝ} (hη : 0 < η) :
    ∃ δ > 0, ∀ s ∈ Set.Icc 0 T, ∀ s' ∈ Set.Icc 0 T, |s - s'| ≤ δ → ∀ x : Euc d,
      ‖H (s, x) - H (s', x)‖ ≤ η * jbracket x := by
  set ρ : ℝ := 2 * |B| / η with hρ
  have hK : IsCompact (Set.Icc 0 T ×ˢ Metric.closedBall (0 : Euc d) ρ) :=
    isCompact_Icc.prod (isCompact_closedBall _ _)
  have hcK : ContinuousOn H (Set.Icc 0 T ×ˢ Metric.closedBall (0 : Euc d) ρ) :=
    hc.mono (Set.prod_mono le_rfl (Set.subset_univ _))
  obtain ⟨δ, hδ, hδ'⟩ := Metric.uniformContinuousOn_iff.1 (hK.uniformContinuousOn_of_continuous hcK) η hη
  refine ⟨δ / 2, half_pos hδ, fun s hs s' hs' hss x => ?_⟩
  have hjx := s83_one_le_jb x
  by_cases hx : ‖x‖ ≤ ρ
  · have := hδ' (s, x) ⟨hs, Metric.mem_closedBall.2 (by simpa using hx)⟩ (s', x)
      ⟨hs', Metric.mem_closedBall.2 (by simpa using hx)⟩ (by
        rw [Prod.dist_eq]
        simp only [dist_self, Real.dist_eq]
        refine max_lt ?_ hδ
        linarith [hss, half_pos hδ])
    rw [dist_eq_norm] at this
    calc ‖H (s, x) - H (s', x)‖ ≤ η := this.le
      _ = η * 1 := (mul_one _).symm
      _ ≤ η * jbracket x := mul_le_mul_of_nonneg_left hjx hη.le
  · push Not at hx
    have h1 := norm_sub_le (H (s, x)) (H (s', x))
    have h2 := hB s hs x
    have h3 := hB s' hs' x
    have hxj := s83_norm_le_jb x
    have : 2 * |B| < η * jbracket x := by
      have : 2 * |B| < η * ‖x‖ := by
        have := (div_lt_iff₀ hη).1 (show 2 * |B| / η < ‖x‖ from hx)
        linarith
      nlinarith [norm_nonneg x]
    calc ‖H (s, x) - H (s', x)‖ ≤ ‖H (s, x)‖ + ‖H (s', x)‖ := h1
      _ ≤ |B| + |B| := add_le_add (h2.trans (le_abs_self _)) (h3.trans (le_abs_self _))
      _ ≤ η * jbracket x := by linarith

theorem s8h2_cls_of_jets {M V W : ℝ} {g : Euc d → ℝ} (hg : ContDiff ℝ 2 g)
    (h1 : ∀ y, ‖iteratedFDeriv ℝ 1 g y‖ ≤ V * jbracket y ^ M)
    (h2 : ∀ y, ‖iteratedFDeriv ℝ 2 g y‖ ≤ W * jbracket y ^ M) : S8hCls M V W g := by
  refine ⟨hg, fun y => ?_, fun y => ?_⟩
  · have := h1 y
    rwa [norm_iteratedFDeriv_one] at this
  · have := h2 y
    rwa [← norm_iteratedFDeriv_fderiv, norm_iteratedFDeriv_one] at this

section Comm

variable {a β : ℝ} {ρβ : Euc d → ℝ}

theorem s8h2_comm (hd : 2 ≤ d) (ha : 0 < a) (hβ : 0 < β)
    (hρ : IsThermalEquilibrium d ((d : ℝ) / 2) a β ρβ) {T : ℝ} (hT : 0 < T) {g : ℝ → Euc d → ℝ}
    {lam : ℝ → ℝ} (hc2 : ∀ s ∈ Set.Icc 0 T, ContDiff ℝ 2 (g s)) {B : ℝ}
    (hB : ∀ s ∈ Set.Icc 0 T, ∀ x, ∀ i ≤ 2, ‖iteratedFDeriv ℝ i (g s) x‖ ≤ B)
    (hcont : ∀ i ≤ 2, ContinuousOn (fun p : ℝ × Euc d => iteratedFDeriv ℝ i (g p.1) p.2)
      (Set.Icc 0 T ×ˢ Set.univ))
    (hlam : ContinuousOn lam (Set.Icc 0 T))
    (hA : ∀ x, ContinuousOn (fun s => projGeneratorW (critCoeff d a β ρβ)
      (HRS.Whole.withDensityReal ρβ) 0 (g s) x) (Set.Icc 0 T)) :
    ContDiff ℝ 2 (fun x => ∫ s in Set.Ioc 0 T, lam s * g s x) ∧
    (∃ V W : ℝ, 0 ≤ V ∧ 0 ≤ W ∧ S8hCls 1 V W (fun x => ∫ s in Set.Ioc 0 T, lam s * g s x)) ∧
    ∀ x, projGeneratorW (critCoeff d a β ρβ) (HRS.Whole.withDensityReal ρβ) 0
        (fun x => ∫ s in Set.Ioc 0 T, lam s * g s x) x =
      ∫ s in Set.Ioc 0 T, lam s * projGeneratorW (critCoeff d a β ρβ) (HRS.Whole.withDensityReal ρβ) 0 (g s) x := by
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0 ⟨le_rfl, hT.le⟩ 0 0 (by norm_num))
  obtain ⟨Bl0, hBl0⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := T)).exists_bound_of_continuousOn hlam
  set Bl : ℝ := |Bl0| with hBl
  have hBl0' : ∀ s ∈ Set.Icc (0 : ℝ) T, |lam s| ≤ Bl := fun s hs => by
    have := hBl0 s hs
    rw [Real.norm_eq_abs] at this
    exact this.trans (le_abs_self _)
  have hBlp : 0 ≤ Bl := abs_nonneg _
  have hIcc : ∀ s ∈ Set.Ioc (0 : ℝ) T, s ∈ Set.Icc (0 : ℝ) T := fun s hs => ⟨hs.1.le, hs.2⟩
  have hg0 : ∀ z, ContinuousOn (fun s => g s z) (Set.Icc 0 T) := fun z => by
    have h := (hcont 0 (by norm_num)).comp (continuous_id.prodMk continuous_const).continuousOn
      (fun s hs => ⟨hs, Set.mem_univ z⟩)
    exact ((ContinuousMultilinearMap.apply ℝ (fun _ : Fin 0 => Euc d) ℝ (fun i => i.elim0)).continuous.comp_continuousOn
      h).congr (fun s _ => by simp [iteratedFDeriv_zero_apply])
  have hjet : ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ k ≤ 2, ∀ z,
      iteratedFDeriv ℝ k (fun x => lam s * g s x) z = lam s • iteratedFDeriv ℝ k (g s) z := fun s hs k hk z =>
    iteratedFDeriv_const_smul_apply' (a := lam s) (f := g s) (x := z) (i := k)
      ((hc2 s hs).contDiffAt.of_le (by exact_mod_cast hk))
  have hbd : ∀ s ∈ Set.Ioc (0 : ℝ) T, ∀ k ≤ 2, ∀ z,
      ‖iteratedFDeriv ℝ k (fun x => lam s * g s x) z‖ ≤ (Bl * B) * (fun _ : Euc d => (1 : ℝ)) z := by
    intro s hs k hk z
    rw [hjet s (hIcc s hs) k hk z, norm_smul]
    simp only [Real.norm_eq_abs, mul_one]
    exact mul_le_mul (hBl0' s (hIcc s hs)) (hB s (hIcc s hs) z k hk) (norm_nonneg _) hBlp
  obtain ⟨hΘ, hform, hnorm⟩ := s8h2_param_set (V := Euc d) 2 (w := fun _ => (1 : ℝ)) continuous_const
    (fun _ => zero_le_one) measurableSet_Ioc (F := fun s x => lam s * g s x)
    (fun s hs => contDiff_const.mul (hc2 s (hIcc s hs)))
    (fun z => (hlam.mono Set.Ioc_subset_Icc_self).mul ((hg0 z).mono Set.Ioc_subset_Icc_self))
    (b := fun _ => Bl * B) continuous_const.integrableOn_Ioc (fun _ _ => mul_nonneg hBlp hB0) hbd
  have hint : (∫ _ in Set.Ioc (0 : ℝ) T, Bl * B) = T * (Bl * B) := by
    simp [setIntegral_const, hT.le]
  have hVT : 0 ≤ T * (Bl * B) := by positivity
  have hcls : S8hCls 1 (T * (Bl * B)) (T * (Bl * B)) (fun x => ∫ s in Set.Ioc 0 T, lam s * g s x) := by
    refine s8h2_cls_of_jets hΘ (fun y => ?_) (fun y => ?_)
    · have := hnorm 1 (by norm_num) y
      rw [hint, mul_one] at this
      rw [Real.rpow_one]
      have h1 := s83_one_le_jb y
      nlinarith
    · have := hnorm 2 le_rfl y
      rw [hint, mul_one] at this
      rw [Real.rpow_one]
      have h1 := s83_one_le_jb y
      nlinarith
  refine ⟨hΘ, ⟨_, _, hVT, hVT, hcls⟩, fun x => ?_⟩
  obtain ⟨Cg, hCg0, hCg⟩ := s8g_gen_bound hd ha hβ hρ (M := 1) zero_le_one
  set Θ : Euc d → ℝ := fun x => ∫ s in Set.Ioc 0 T, lam s * g s x with hΘdef
  set A : (Euc d → ℝ) → Euc d → ℝ := fun f => projGeneratorW (critCoeff d a β ρβ)
    (HRS.Whole.withDensityReal ρβ) 0 f with hAdef
  -- the weighted jets of the integrand
  set Hi : (i : ℕ) → ℝ × Euc d → (Euc d [×i]→L[ℝ] ℝ) := fun i p => lam p.1 • iteratedFDeriv ℝ i (g p.1) p.2 with hHi
  have hHc : ∀ i ≤ 2, ContinuousOn (Hi i) (Set.Icc 0 T ×ˢ Set.univ) := fun i hi =>
    (hlam.comp continuous_fst.continuousOn (fun p hp => hp.1)).smul (hcont i hi)
  have hHb : ∀ i ≤ 2, ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ x, ‖Hi i (s, x)‖ ≤ Bl * B := fun i hi s hs x => by
    simp only [hHi]
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul (hBl0' s hs) (hB s hs x i hi) (norm_nonneg _) hBlp
  have hmod : ∀ η' > 0, ∃ δ > 0, ∀ i ≤ 2, ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ s' ∈ Set.Icc (0 : ℝ) T, |s - s'| ≤ δ →
      ∀ y : Euc d, ‖Hi i (s, y) - Hi i (s', y)‖ ≤ η' * jbracket y := by
    intro η' hη'
    obtain ⟨δ0, h0, m0⟩ := s8h2_wmod (hHc 0 (by norm_num)) (hHb 0 (by norm_num)) hη'
    obtain ⟨δ1, h1, m1⟩ := s8h2_wmod (hHc 1 (by norm_num)) (hHb 1 (by norm_num)) hη'
    obtain ⟨δ2, h2, m2⟩ := s8h2_wmod (hHc 2 le_rfl) (hHb 2 le_rfl) hη'
    refine ⟨min δ0 (min δ1 δ2), lt_min h0 (lt_min h1 h2), fun i hi s hs s' hs' hss y => ?_⟩
    interval_cases i
    · exact m0 s hs s' hs' (hss.trans (min_le_left _ _)) y
    · exact m1 s hs s' hs' (hss.trans ((min_le_right _ _).trans (min_le_left _ _))) y
    · exact m2 s hs s' hs' (hss.trans ((min_le_right _ _).trans (min_le_right _ _))) y
  -- the main estimate
  have hmain : ∀ ε > 0, |A Θ x - ∫ s in Set.Ioc 0 T, lam s * A (g s) x| ≤ ε := by
    intro ε hε
    set Kx : ℝ := Cg * 2 * (jbracket x ^ (1 : ℝ) * (1 + ‖x‖)) with hKx
    have hKx0 : 0 ≤ Kx := by
      have := Real.rpow_nonneg (s83_jb_pos x).le (1 : ℝ)
      exact mul_nonneg (mul_nonneg hCg0 (by norm_num)) (mul_nonneg this (by positivity))
    set η' : ℝ := ε / (2 * T * (Kx + 1)) with hη'
    have hη'0 : 0 < η' := by positivity
    set η'' : ℝ := ε / (2 * T) with hη''
    have hη''0 : 0 < η'' := by positivity
    obtain ⟨δ1, hδ1, hm1⟩ := hmod η' hη'0
    have hhc : ContinuousOn (fun s => lam s * A (g s) x) (Set.Icc 0 T) := hlam.mul (hA x)
    obtain ⟨δ2, hδ2, hm2⟩ := Metric.uniformContinuousOn_iff.1
      (isCompact_Icc.uniformContinuousOn_of_continuous hhc) η'' hη''0
    set δ : ℝ := min δ1 (δ2 / 2) with hδ
    have hδ0 : 0 < δ := lt_min hδ1 (half_pos hδ2)
    set n : ℕ := ⌈T / δ⌉₊ + 1 with hn
    have hnpos : 0 < n := Nat.succ_pos _
    have hnR : (0 : ℝ) < n := by exact_mod_cast hnpos
    have hTn : T / n ≤ δ := by
      rw [div_le_iff₀ hnR]
      have h1 : T / δ ≤ n := by
        have := Nat.le_ceil (T / δ)
        simp only [hn]; push_cast; linarith
      have := (div_le_iff₀ hδ0).1 h1
      linarith
    set t : ℕ → ℝ := fun k => T * ((k : ℝ) + 1) / n with ht
    have htmem : ∀ k ∈ Finset.range n, t k ∈ Set.Icc (0 : ℝ) T := fun k hk => by
      have hk' : (k : ℝ) + 1 ≤ n := by exact_mod_cast Finset.mem_range.1 hk
      simp only [ht, Set.mem_Icc]
      refine ⟨by positivity, ?_⟩
      rw [div_le_iff₀ hnR]; nlinarith
    set c : ℕ → ℝ := fun k => (T / n) * lam (t k) with hc
    set Θn : Euc d → ℝ := fun y => ∑ k ∈ Finset.range n, c k * g (t k) y with hΘn
    have hgcls : ∀ k ∈ Finset.range n, S8hCls 1 B B (g (t k)) := fun k hk =>
      s8h2_cls_of_jets (hc2 _ (htmem k hk)) (fun y => by
        rw [Real.rpow_one]
        have := hB _ (htmem k hk) y 1 (by norm_num)
        have h1 := s83_one_le_jb y
        nlinarith) (fun y => by
        rw [Real.rpow_one]
        have := hB _ (htmem k hk) y 2 le_rfl
        have h1 := s83_one_le_jb y
        nlinarith)
    have hΘncls := S8hCls.sum (M := 1) c (fun k => g (t k)) (V := fun _ => B) (W := fun _ => B)
      (Finset.range n) hgcls
    have hAΘn : A Θn x = ∑ k ∈ Finset.range n, c k * A (g (t k)) x :=
      s8h2_proj_sum hd ha hβ hρ zero_le_one c (fun k => g (t k)) (fun _ => B) (fun _ => B) x
        (Finset.range n) (fun _ _ => hB0) (fun _ _ => hB0) hgcls
    have hjetΘ : ∀ i ≤ 2, ∀ y, iteratedFDeriv ℝ i Θ y = ∫ s in Set.Ioc 0 T, Hi i (s, y) := by
      intro i hi y
      rw [hform i hi y]
      refine setIntegral_congr_fun measurableSet_Ioc (fun s hs => ?_)
      simp only [hHi]
      exact hjet s (hIcc s hs) i hi y
    have hjetΘn : ∀ i ≤ 2, ∀ y, iteratedFDeriv ℝ i Θn y = ∑ k ∈ Finset.range n, (T / n) • Hi i (t k, y) := by
      intro i hi y
      have hcd : ∀ k ∈ Finset.range n, ContDiffAt ℝ i (fun y => c k * g (t k) y) y := fun k hk =>
        (contDiff_const.mul ((hc2 _ (htmem k hk)).of_le (by exact_mod_cast hi))).contDiffAt
      rw [hΘn]
      rw [iteratedFDeriv_fun_sum_apply (f := fun k y => c k * g (t k) y) hcd]
      refine Finset.sum_congr rfl fun k hk => ?_
      have := iteratedFDeriv_const_smul_apply' (a := c k) (f := g (t k)) (x := y) (i := i)
        ((hc2 _ (htmem k hk)).contDiffAt.of_le (by exact_mod_cast hi))
      simp only [smul_eq_mul] at this
      rw [this]
      simp only [hHi, hc, smul_smul]
    have hRi : ∀ i ≤ 2, ∀ y, ‖(∫ s in Set.Ioc 0 T, Hi i (s, y)) -
        ∑ k ∈ Finset.range n, (T / n) • Hi i (t k, y)‖ ≤ T * (η' * jbracket y) := by
      intro i hi y
      exact s8h2_riemann (W := Euc d [×i]→L[ℝ] ℝ) hT (h := fun s => Hi i (s, y))
        ((hHc i hi).comp (continuous_id.prodMk continuous_const).continuousOn
          (fun s hs => ⟨hs, Set.mem_univ y⟩)) (δ := δ1) (η := η' * jbracket y)
        (fun s hs s' hs' hss => hm1 i hi s hs s' hs' hss y) hnpos (hTn.trans (min_le_left _ _))
    have hΘ2 : ContDiff ℝ 2 Θn := hΘncls.1
    have hdiff : ∀ i ≤ 2, ∀ y, ‖iteratedFDeriv ℝ i (fun y => Θ y - Θn y) y‖ ≤ (T * η') * jbracket y := by
      intro i hi y
      have hi' : (i : WithTop ℕ∞) ≤ 2 := by exact_mod_cast hi
      rw [s8h2_iter_sub (hΘ.of_le hi') (hΘ2.of_le hi') y, hjetΘ i hi y, hjetΘn i hi y]
      refine (hRi i hi y).trans (le_of_eq (by ring))
    have hdcls : S8hCls 1 (T * η') (T * η') (fun y => Θ y - Θn y) :=
      s8h2_cls_of_jets (hΘ.sub hΘ2) (fun y => by rw [Real.rpow_one]; exact hdiff 1 (by norm_num) y)
        (fun y => by rw [Real.rpow_one]; exact hdiff 2 le_rfl y)
    have hTη : 0 ≤ T * η' := by positivity
    have hAd := hCg hTη hTη hdcls.1 hdcls.2.1 hdcls.2.2 x
    have hsub := s8h2_proj_sub hd ha hβ hρ zero_le_one (g₁ := Θ) (g₂ := Θn) hVT hVT
      (Finset.sum_nonneg fun k _ => mul_nonneg (abs_nonneg _) hB0)
      (Finset.sum_nonneg fun k _ => mul_nonneg (abs_nonneg _) hB0) hcls hΘncls x
    have hAd' : |A Θ x - A Θn x| ≤ T * η' * Kx := by
      have e : A (fun y => Θ y - Θn y) x = A Θ x - A Θn x := hsub
      rw [← e]
      refine hAd.trans (le_of_eq ?_)
      simp only [hKx]; ring
    -- the scalar Riemann sum
    have hRs := s8h2_riemann (W := ℝ) hT (h := fun s => lam s * A (g s) x) hhc (δ := δ) (η := η'')
      (fun s hs s' hs' hss => by
        have := hm2 s hs s' hs' (by
          rw [Real.dist_eq]
          have : δ ≤ δ2 / 2 := min_le_right _ _
          linarith)
        rw [Real.dist_eq] at this
        rw [← Real.norm_eq_abs] at this
        exact this.le) hnpos hTn
    have hsum : ∑ k ∈ Finset.range n, c k * A (g (t k)) x =
        ∑ k ∈ Finset.range n, (T / n) • (lam (T * ((k : ℝ) + 1) / n) * A (g (T * ((k : ℝ) + 1) / n)) x) := by
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [hc, ht, smul_eq_mul]; ring
    have h1 : T * η' * Kx ≤ ε / 2 := by
      rw [hη']
      have e : T * (ε / (2 * T * (Kx + 1))) * Kx = ε / 2 * (Kx / (Kx + 1)) := by field_simp
      rw [e]
      have : Kx / (Kx + 1) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
      nlinarith [hε]
    have h2 : T * η'' = ε / 2 := by rw [hη'']; field_simp
    have hRs' : ‖(∫ s in Set.Ioc 0 T, lam s * A (g s) x) -
        ∑ k ∈ Finset.range n, (T / n) • (lam (T * ((k : ℝ) + 1) / n) * A (g (T * ((k : ℝ) + 1) / n)) x)‖ ≤
        T * η'' := hRs
    have h3 : |A Θn x - ∫ s in Set.Ioc 0 T, lam s * A (g s) x| ≤ ε / 2 := by
      rw [hAΘn, hsum, abs_sub_comm, ← Real.norm_eq_abs]
      exact hRs'.trans (le_of_eq h2)
    calc |A Θ x - ∫ s in Set.Ioc 0 T, lam s * A (g s) x|
        ≤ |A Θ x - A Θn x| + |A Θn x - ∫ s in Set.Ioc 0 T, lam s * A (g s) x| := abs_sub_le _ _ _
      _ ≤ ε / 2 + ε / 2 := add_le_add (hAd'.trans h1) h3
      _ = ε := by ring
  have hfin : A Θ x = ∫ s in Set.Ioc 0 T, lam s * A (g s) x :=
    sub_eq_zero.1 (abs_nonpos_iff.1 (le_of_forall_pos_le_add fun ε hε => by simpa using hmain ε hε))
  exact hfin

end Comm

end HRS.MS.Wad
