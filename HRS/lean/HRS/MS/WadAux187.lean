import HRS.MS.WadAux186

/-!
# S8.3, packet S8H2-13: the equation on a finite horizon for general kernels

`s8h2_eq_T`: for `F` with `S8hPair M 2 F` and `T > 0`, with `Φ_T = ∫_{(0,T]} S_tF dt`:
`𝒜_xΦ_T(·,y)(x) + 𝒜_yΦ_T(x,·)(y) = S_TF(x,y) - F(x,y)`.  The separated case (`s8h2_sep_eq`) passes to the limit along the approximants of `s8h2_P1`
(linearity `s8h2_proj_sub` and the bound `s8g_gen_bound` on the difference of the `Φ`'s).
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal ContDiff RealInnerProductSpace

namespace HRS.MS.Wad

open HRS HRS.Whole

variable {d : ℕ}

theorem s8h2_slice_jet_fst {G : Euc d × Euc d → ℝ} {m : ℕ} (hG : ContDiff ℝ m G) (y : Euc d) {i : ℕ}
    (hi : i ≤ m) (x : Euc d) :
    ‖iteratedFDeriv ℝ i (fun x' => G (x', y)) x‖ ≤ ‖iteratedFDeriv ℝ i G (x, y)‖ := by
  have hG' : ContDiff ℝ m (G ∘ Prod.swap) := hG.comp (contDiff_snd.prodMk contDiff_fst)
  have := s8h2_slice_jet hG' y hi x
  rw [s8h2_swap_jet] at this
  exact this

theorem s8h2_slice_cls {M c : ℝ} (hc : 0 ≤ c) {Φ : Euc d × Euc d → ℝ} (hΦ : ContDiff ℝ 2 Φ)
    (hb : ∀ k ≤ 2, ∀ z, ‖iteratedFDeriv ℝ k Φ z‖ ≤ c * s8h_w M z) (y x0 : Euc d) :
    S8hCls M (c * jbracket y ^ M) (c * jbracket y ^ M) (fun x' => Φ (x', y)) ∧
    S8hCls M (c * jbracket x0 ^ M) (c * jbracket x0 ^ M) (fun y' => Φ (x0, y')) := by
  have h1 : ContDiff ℝ 2 (fun x' : Euc d => Φ (x', y)) := hΦ.comp (contDiff_id.prodMk contDiff_const)
  have h2 : ContDiff ℝ 2 (fun y' : Euc d => Φ (x0, y')) := hΦ.comp (contDiff_const.prodMk contDiff_id)
  refine ⟨s8h2_cls_of_jets h1 (fun x' => ?_) (fun x' => ?_), s8h2_cls_of_jets h2 (fun y' => ?_) (fun y' => ?_)⟩
  · refine (s8h2_slice_jet_fst hΦ y (by norm_num) x').trans ((hb 1 (by norm_num) (x', y)).trans (le_of_eq ?_))
    unfold s8h_w; ring
  · refine (s8h2_slice_jet_fst hΦ y le_rfl x').trans ((hb 2 le_rfl (x', y)).trans (le_of_eq ?_))
    unfold s8h_w; ring
  · refine (s8h2_slice_jet hΦ x0 (by norm_num) y').trans ((hb 1 (by norm_num) (x0, y')).trans (le_of_eq ?_))
    unfold s8h_w; ring
  · refine (s8h2_slice_jet hΦ x0 le_rfl y').trans ((hb 2 le_rfl (x0, y')).trans (le_of_eq ?_))
    unfold s8h_w; ring

section Interface

variable {a β : ℝ} {ρβ : Euc d → ℝ} {M : ℝ} {U : ℝ → (Euc d → ℝ) → Euc d → ℝ}

theorem s8h2_phi_reg {T : ℝ} (hT : 0 < T) {H : ℝ → Euc d × Euc d → ℝ} {c : ℝ} (hc : 0 ≤ c)
    (hcd : ∀ t ∈ Set.Ioc (0 : ℝ) T, ContDiff ℝ 2 (H t))
    (hcont : ∀ z, ContinuousOn (fun t => H t z) (Set.Ioc 0 T))
    (hb : ∀ t ∈ Set.Ioc (0 : ℝ) T, ∀ k ≤ 2, ∀ z, ‖iteratedFDeriv ℝ k (H t) z‖ ≤ c * s8h_w M z) :
    ContDiff ℝ 2 (fun z => ∫ t in Set.Ioc 0 T, H t z) ∧
      ∀ k ≤ 2, ∀ z, ‖iteratedFDeriv ℝ k (fun z => ∫ t in Set.Ioc 0 T, H t z) z‖ ≤ (T * c) * s8h_w M z := by
  obtain ⟨h1, -, h3⟩ := s8h2_param_set 2 (w := s8h_w (d := d) M) (s8h_w_cont M) (fun z => (s8h_w_pos M z).le)
    measurableSet_Ioc (F := H) hcd hcont (b := fun _ => c) continuous_const.integrableOn_Ioc
    (fun _ _ => hc) hb
  refine ⟨h1, fun k hk z => ?_⟩
  have := h3 k hk z
  have e : (∫ _t in Set.Ioc (0 : ℝ) T, c) = T * c := by simp [setIntegral_const, hT.le]
  rwa [e] at this

theorem s8h2_eq_limit (hd : 2 ≤ d) (ha : 0 < a) (hβ : 0 < β)
    (hρ : IsThermalEquilibrium d ((d : ℝ) / 2) a β ρβ) (hM : 0 ≤ M) {ΦF : Euc d × Euc d → ℝ}
    {ΦG : ℕ → Euc d × Euc d → ℝ} {cF cG : ℝ} (hcF : 0 ≤ cF) (hcG : 0 ≤ cG) (hΦF : ContDiff ℝ 2 ΦF)
    (hbF : ∀ k ≤ 2, ∀ z, ‖iteratedFDeriv ℝ k ΦF z‖ ≤ cF * s8h_w M z)
    (hΦG : ∀ n, ContDiff ℝ 2 (ΦG n))
    (hbG : ∀ n, ∀ k ≤ 2, ∀ z, ‖iteratedFDeriv ℝ k (ΦG n) z‖ ≤ cG * s8h_w M z)
    {cD : ℕ → ℝ} (hcD : ∀ n, 0 ≤ cD n) (hcDt : Tendsto cD atTop (𝓝 0))
    (hbD : ∀ n, ∀ k ≤ 2, ∀ z, ‖iteratedFDeriv ℝ k (fun z => ΦF z - ΦG n z) z‖ ≤ cD n * s8h_w M z)
    {Rn : ℕ → ℝ} {R0 : ℝ} (hRt : Tendsto Rn atTop (𝓝 R0)) (x y : Euc d)
    (hE : ∀ n, projGeneratorW (critCoeff d a β ρβ) (HRS.Whole.withDensityReal ρβ) 0
        (fun x' => ΦG n (x', y)) x +
      projGeneratorW (critCoeff d a β ρβ) (HRS.Whole.withDensityReal ρβ) 0 (fun y' => ΦG n (x, y')) y = Rn n) :
    projGeneratorW (critCoeff d a β ρβ) (HRS.Whole.withDensityReal ρβ) 0 (fun x' => ΦF (x', y)) x +
      projGeneratorW (critCoeff d a β ρβ) (HRS.Whole.withDensityReal ρβ) 0 (fun y' => ΦF (x, y')) y = R0 := by
  obtain ⟨Cg, hCg0, hCg⟩ := s8g_gen_bound hd ha hβ hρ hM
  set A : (Euc d → ℝ) → Euc d → ℝ := fun f => projGeneratorW (critCoeff d a β ρβ)
    (HRS.Whole.withDensityReal ρβ) 0 f with hAdef
  set Kc : ℝ := Cg * 2 * (jbracket y ^ M * (jbracket x ^ M * (1 + ‖x‖)) +
    jbracket x ^ M * (jbracket y ^ M * (1 + ‖y‖))) with hKc
  have hjx := Real.rpow_nonneg (s83_jb_pos x).le M
  have hjy := Real.rpow_nonneg (s83_jb_pos y).le M
  have hKc0 : 0 ≤ Kc :=
    mul_nonneg (mul_nonneg hCg0 (by norm_num)) (add_nonneg (mul_nonneg hjy (mul_nonneg hjx (by positivity)))
      (mul_nonneg hjx (mul_nonneg hjy (by positivity))))
  have hbd : ∀ n, |(A (fun x' => ΦF (x', y)) x + A (fun y' => ΦF (x, y')) y) - Rn n| ≤ cD n * Kc := by
    intro n
    obtain ⟨hxF, hyF⟩ := s8h2_slice_cls hcF hΦF hbF y x
    obtain ⟨hxG, hyG⟩ := s8h2_slice_cls hcG (hΦG n) (hbG n) y x
    have hΦD : ContDiff ℝ 2 (fun z => ΦF z - ΦG n z) := hΦF.sub (hΦG n)
    obtain ⟨hxD, hyD⟩ := s8h2_slice_cls (hcD n) hΦD (hbD n) y x
    have hVx : 0 ≤ cD n * jbracket y ^ M := mul_nonneg (hcD n) hjy
    have hVy : 0 ≤ cD n * jbracket x ^ M := mul_nonneg (hcD n) hjx
    have h1 := hCg hVx hVx hxD.1 hxD.2.1 hxD.2.2 x
    have h2 := hCg hVy hVy hyD.1 hyD.2.1 hyD.2.2 y
    have e1 : A (fun x' => ΦF (x', y) - ΦG n (x', y)) x =
        A (fun x' => ΦF (x', y)) x - A (fun x' => ΦG n (x', y)) x :=
      s8h2_proj_sub hd ha hβ hρ hM (g₁ := fun x' => ΦF (x', y)) (g₂ := fun x' => ΦG n (x', y))
        (mul_nonneg hcF hjy) (mul_nonneg hcF hjy) (mul_nonneg hcG hjy) (mul_nonneg hcG hjy) hxF hxG x
    have e2 : A (fun y' => ΦF (x, y') - ΦG n (x, y')) y =
        A (fun y' => ΦF (x, y')) y - A (fun y' => ΦG n (x, y')) y :=
      s8h2_proj_sub hd ha hβ hρ hM (g₁ := fun y' => ΦF (x, y')) (g₂ := fun y' => ΦG n (x, y'))
        (mul_nonneg hcF hjx) (mul_nonneg hcF hjx) (mul_nonneg hcG hjx) (mul_nonneg hcG hjx) hyF hyG y
    have h1' : |A (fun x' => ΦF (x', y)) x - A (fun x' => ΦG n (x', y)) x| ≤
        Cg * (cD n * jbracket y ^ M + cD n * jbracket y ^ M) * (jbracket x ^ M * (1 + ‖x‖)) := by
      rw [← e1]; exact h1
    have h2' : |A (fun y' => ΦF (x, y')) y - A (fun y' => ΦG n (x, y')) y| ≤
        Cg * (cD n * jbracket x ^ M + cD n * jbracket x ^ M) * (jbracket y ^ M * (1 + ‖y‖)) := by
      rw [← e2]; exact h2
    have hsplit : (A (fun x' => ΦF (x', y)) x + A (fun y' => ΦF (x, y')) y) - Rn n =
        (A (fun x' => ΦF (x', y)) x - A (fun x' => ΦG n (x', y)) x) +
          (A (fun y' => ΦF (x, y')) y - A (fun y' => ΦG n (x, y')) y) := by
      have hE' : A (fun x' => ΦG n (x', y)) x + A (fun y' => ΦG n (x, y')) y = Rn n := hE n
      rw [← hE']; ring
    rw [hsplit]
    refine (abs_add_le _ _).trans ?_
    calc _ ≤ Cg * (cD n * jbracket y ^ M + cD n * jbracket y ^ M) * (jbracket x ^ M * (1 + ‖x‖)) +
          Cg * (cD n * jbracket x ^ M + cD n * jbracket x ^ M) * (jbracket y ^ M * (1 + ‖y‖)) :=
          add_le_add h1' h2'
      _ = cD n * Kc := by simp only [hKc]; ring
  have hlim : Tendsto Rn atTop (𝓝 (A (fun x' => ΦF (x', y)) x + A (fun y' => ΦF (x, y')) y)) := by
    refine tendsto_iff_norm_sub_tendsto_zero.2 (squeeze_zero (fun n => norm_nonneg _) (fun n => ?_)
      (g := fun n => cD n * Kc) ?_)
    · rw [Real.norm_eq_abs, abs_sub_comm]; exact hbd n
    · simpa using hcDt.mul_const Kc
  exact tendsto_nhds_unique hlim hRt

theorem s8h2_eq_T (hd : 2 ≤ d) (ha : 0 < a) (hβ : 0 < β)
    (hρ : IsThermalEquilibrium d ((d : ℝ) / 2) a β ρβ)
    (hU : IsWeightedSemigroup (critCoeff d a β ρβ) (HRS.Whole.withDensityReal ρβ) M U)
    (h3 : S8eC3 M U) (hM : 0 ≤ M) {T : ℝ} (hT : 0 < T) {F : Euc d × Euc d → ℝ} (hF : S8hPair M 2 F)
    (x y : Euc d) :
    projGeneratorW (critCoeff d a β ρβ) (HRS.Whole.withDensityReal ρβ) 0
        (fun x' => ∫ t in Set.Ioc 0 T, s8h2_S U t F (x', y)) x +
      projGeneratorW (critCoeff d a β ρβ) (HRS.Whole.withDensityReal ρβ) 0
        (fun y' => ∫ t in Set.Ioc 0 T, s8h2_S U t F (x, y')) y =
      s8h2_S U T F (x, y) - F (x, y) := by
  obtain ⟨C, hC0, hP⟩ := s8h2_P1 hU h3 hM 2 hT.le
  obtain ⟨N0, hN0, G, hGs, hGF, hG⟩ := hP hF
  set ε : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1) with hε
  have hε0 : ∀ n, 0 ≤ ε n := fun n => by simp only [hε]; positivity
  have hε1 : ∀ n, ε n ≤ 1 := fun n => by
    simp only [hε]
    rw [div_le_one (by positivity)]
    linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hεt : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hIcc : ∀ t ∈ Set.Ioc (0 : ℝ) T, t ∈ Set.Icc (0 : ℝ) T := fun t ht => ⟨ht.1.le, ht.2⟩
  have hGp : ∀ n, S8hPair M 2 (G n) := fun n => s8h2_sepZ_pair M (hGs n) 2
  have hF0 : ∀ z, ContinuousOn (fun t => s8h2_S U t F z) (Set.Ioc 0 T) := fun z =>
    ((s8h2_S_cont hd ha hβ hρ hU h3 hM hF z).mono (fun t ht => Set.mem_Ici.2 ht.1.le))
  have hG0 : ∀ n z, ContinuousOn (fun t => s8h2_S U t (G n) z) (Set.Ioc 0 T) := fun n z =>
    ((s8h2_S_sep_cont hd ha hβ hρ hU (hGs n) z).mono (fun t ht => Set.mem_Ici.2 ht.1.le))
  have hGcd : ∀ n, ∀ t ∈ Set.Icc (0 : ℝ) T, ContDiff ℝ 2 (s8h2_S U t (G n)) := fun n t ht => by
    obtain ⟨N', -, G', -, -, hG'⟩ := hP (hGp n)
    exact (hG' t ht).1
  have hint : ∀ (H : ℝ → Euc d × Euc d → ℝ), (∀ z, ContinuousOn (fun t => H t z) (Set.Ioc 0 T)) →
      (∀ z, ContinuousOn (fun t => H t z) (Set.Icc 0 T)) → ∀ z, IntegrableOn (fun t => H t z) (Set.Ioc 0 T) :=
    fun H _ h2 z => ((h2 z).integrableOn_Icc).mono_set Set.Ioc_subset_Icc_self
  have hF0' : ∀ z, ContinuousOn (fun t => s8h2_S U t F z) (Set.Icc 0 T) := fun z =>
    ((s8h2_S_cont hd ha hβ hρ hU h3 hM hF z).mono Set.Icc_subset_Ici_self)
  have hG0' : ∀ n z, ContinuousOn (fun t => s8h2_S U t (G n) z) (Set.Icc 0 T) := fun n z =>
    ((s8h2_S_sep_cont hd ha hβ hρ hU (hGs n) z).mono Set.Icc_subset_Ici_self)
  -- regularity of `Φ^F`
  obtain ⟨hΦF, hΦFb⟩ := s8h2_phi_reg (M := M) hT (H := fun t z => s8h2_S U t F z) (c := C * N0)
    (mul_nonneg hC0 hN0) (fun t ht => (hG t (hIcc t ht)).1) hF0
    (fun t ht k hk z => (hG t (hIcc t ht)).2.1 k hk z)
  -- regularity of `Φ^{G_n}`
  have hΦG : ∀ n, ContDiff ℝ 2 (fun z => ∫ t in Set.Ioc 0 T, s8h2_S U t (G n) z) ∧
      ∀ k ≤ 2, ∀ z, ‖iteratedFDeriv ℝ k (fun z => ∫ t in Set.Ioc 0 T, s8h2_S U t (G n) z) z‖ ≤
        (T * (C * N0 + C)) * s8h_w M z := by
    intro n
    refine s8h2_phi_reg (M := M) hT (H := fun t z => s8h2_S U t (G n) z) (c := C * N0 + C)
      (by positivity) (fun t ht => hGcd n t (hIcc t ht)) (hG0 n) (fun t ht k hk z => ?_)
    have hcdF : ContDiff ℝ k (s8h2_S U t F) :=
      ((hG t (hIcc t ht)).1).of_le (by exact_mod_cast hk)
    have hcdG : ContDiff ℝ k (s8h2_S U t (G n)) :=
      ((hGcd n t (hIcc t ht))).of_le (by exact_mod_cast hk)
    have e : iteratedFDeriv ℝ k (s8h2_S U t (G n)) z =
        iteratedFDeriv ℝ k (s8h2_S U t F) z -
          (iteratedFDeriv ℝ k (s8h2_S U t F) z - iteratedFDeriv ℝ k (s8h2_S U t (G n)) z) := by abel
    rw [e]
    refine (norm_sub_le _ _).trans ?_
    have h1 := (hG t (hIcc t ht)).2.1 k hk z
    have h2 : ‖iteratedFDeriv ℝ k (s8h2_S U t F) z - iteratedFDeriv ℝ k (s8h2_S U t (G n)) z‖ ≤
        ε n * C * s8h_w M z := (hG t (hIcc t ht)).2.2 n k hk z
    have hw := (s8h_w_pos M z).le
    calc _ ≤ C * N0 * s8h_w M z + ε n * C * s8h_w M z := add_le_add h1 h2
      _ ≤ C * N0 * s8h_w M z + 1 * C * s8h_w M z := by
          refine add_le_add le_rfl (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hε1 n) hC0) hw)
      _ = (C * N0 + C) * s8h_w M z := by ring
  -- regularity of the difference
  have hΦD : ∀ n, ContDiff ℝ 2 (fun z => ∫ t in Set.Ioc 0 T, (s8h2_S U t F z - s8h2_S U t (G n) z)) ∧
      ∀ k ≤ 2, ∀ z, ‖iteratedFDeriv ℝ k (fun z => ∫ t in Set.Ioc 0 T,
        (s8h2_S U t F z - s8h2_S U t (G n) z)) z‖ ≤ (T * (ε n * C)) * s8h_w M z := by
    intro n
    refine s8h2_phi_reg (M := M) hT (H := fun t z => s8h2_S U t F z - s8h2_S U t (G n) z)
      (c := ε n * C) (mul_nonneg (hε0 n) hC0)
      (fun t ht => ((hG t (hIcc t ht)).1).sub (hGcd n t (hIcc t ht)))
      (fun z => (hF0 z).sub (hG0 n z)) (fun t ht k hk z => ?_)
    have hcdF : ContDiff ℝ k (s8h2_S U t F) :=
      ((hG t (hIcc t ht)).1).of_le (by exact_mod_cast hk)
    have hcdG : ContDiff ℝ k (s8h2_S U t (G n)) :=
      ((hGcd n t (hIcc t ht))).of_le (by exact_mod_cast hk)
    rw [s8h2_iter_sub hcdF hcdG z]
    have := (hG t (hIcc t ht)).2.2 n k hk z
    calc _ ≤ 1 / ((n : ℝ) + 1) * C * s8h_w M z := this
      _ = ε n * C * s8h_w M z := rfl
  have hΦeq : ∀ n, (fun z => ∫ t in Set.Ioc 0 T, (s8h2_S U t F z - s8h2_S U t (G n) z)) =
      fun z => (∫ t in Set.Ioc 0 T, s8h2_S U t F z) - ∫ t in Set.Ioc 0 T, s8h2_S U t (G n) z := fun n => by
    funext z
    exact integral_sub (hint _ hF0 hF0' z) (hint _ (hG0 n) (hG0' n) z)
  have hΦD' : ∀ n, ContDiff ℝ 2 (fun z => (∫ t in Set.Ioc 0 T, s8h2_S U t F z) -
      ∫ t in Set.Ioc 0 T, s8h2_S U t (G n) z) ∧
      ∀ k ≤ 2, ∀ z, ‖iteratedFDeriv ℝ k (fun z => (∫ t in Set.Ioc 0 T, s8h2_S U t F z) -
        ∫ t in Set.Ioc 0 T, s8h2_S U t (G n) z) z‖ ≤ (T * (ε n * C)) * s8h_w M z := fun n => by
    have := hΦD n
    rwa [hΦeq n] at this
  have hRn : Tendsto (fun n => s8h2_S U T (G n) (x, y) - G n (x, y)) atTop
      (𝓝 (s8h2_S U T F (x, y) - F (x, y))) := by
    have hw := (s8h_w_pos M (x, y)).le
    refine tendsto_iff_norm_sub_tendsto_zero.2 (squeeze_zero (fun n => norm_nonneg _) (fun n => ?_)
      (g := fun n => ε n * ((C + 1) * s8h_w M (x, y))) ?_)
    · have h1 := (hG T ⟨hT.le, le_rfl⟩).2.2 n 0 (Nat.zero_le 2) (x, y)
      rw [s8h_norm_iter0_sub] at h1
      have h2 := hGF n (x, y)
      have e : s8h2_S U T (G n) (x, y) - G n (x, y) - (s8h2_S U T F (x, y) - F (x, y)) =
          -((s8h2_S U T F (x, y) - s8h2_S U T (G n) (x, y)) - (F (x, y) - G n (x, y))) := by ring
      rw [e, norm_neg]
      refine (norm_sub_le _ _).trans ?_
      calc _ ≤ 1 / ((n : ℝ) + 1) * C * s8h_w M (x, y) + 1 / ((n : ℝ) + 1) * s8h_w M (x, y) := add_le_add h1 h2
        _ = ε n * ((C + 1) * s8h_w M (x, y)) := by simp only [hε]; ring
    · simpa using hεt.mul_const ((C + 1) * s8h_w M (x, y))
  refine s8h2_eq_limit hd ha hβ hρ hM (ΦF := fun z => ∫ t in Set.Ioc 0 T, s8h2_S U t F z)
    (ΦG := fun n z => ∫ t in Set.Ioc 0 T, s8h2_S U t (G n) z) (cF := T * (C * N0)) (cG := T * (C * N0 + C))
    (by positivity) (by positivity) hΦF hΦFb (fun n => (hΦG n).1) (fun n => (hΦG n).2)
    (cD := fun n => T * (ε n * C)) (fun n => by have := hε0 n; positivity) ?_
    (fun n => (hΦD' n).2) hRn x y (fun n => s8h2_sep_eq hd ha hβ hρ hU hT (hGs n) x y)
  simpa using (hεt.mul_const C).const_mul T

end Interface

end HRS.MS.Wad
