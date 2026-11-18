import HRS.MS.WadAux187

/-!
# S8.3, packet S8H2-14: clause (5) `S8eC5` and the tie of `weighted_adjoint_decay`

`s8h2_c5`: for every weighted semigroup `U` the pair-inverse clause `S8eC5` holds.  Integrability, `C^j` regularity and the weighted bounds of `Ψ = ∫_0^∞ S_tR dt`
come from `s8h2_psi_reg`; the equation `-(𝒜_x+𝒜_y)Ψ = R` from `s8h2_eq_T` on the horizons `T_n = n+2` and `s8h2_eq_limit` (the tails
`∫_{T_n}^∞ S_tR dt` have jets bounded by `(∫_{T_n}^∞ b) w → 0`).  `s8h2_weighted_adjoint_decay` is the frozen statement `weighted_adjoint_decay`.
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal ContDiff RealInnerProductSpace

namespace HRS.MS.Wad

open HRS HRS.Whole

variable {d : ℕ}

theorem s8h2_decay_prod {κ : ℝ} (hκ : 0 < κ) :
    Tendsto (fun z : Euc d × Euc d => jbracket z.1 ^ (-κ) * jbracket z.2 ^ (-κ)) (cocompact (Euc d × Euc d)) (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro η hη
  obtain ⟨ρ, hρ⟩ := Filter.eventually_atTop.1 ((tendsto_rpow_neg_atTop hκ).eventually (gt_mem_nhds hη))
  set R : ℝ := max ρ 1 with hR
  have hev : (Metric.closedBall (0 : Euc d × Euc d) R)ᶜ ∈ cocompact (Euc d × Euc d) :=
    (isCompact_closedBall _ _).compl_mem_cocompact
  filter_upwards [hev] with z hz
  have hz' : R < ‖z‖ := by simpa [mem_closedBall_zero_iff] using hz
  have hone : ∀ w : Euc d, jbracket w ^ (-κ) ≤ 1 := fun w =>
    Real.rpow_le_one_of_one_le_of_nonpos (s83_one_le_jb w) (by linarith)
  have hpos : ∀ w : Euc d, 0 ≤ jbracket w ^ (-κ) := fun w => Real.rpow_nonneg (s83_jb_pos w).le _
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (mul_nonneg (hpos _) (hpos _))]
  rw [Prod.norm_def] at hz'
  have hmax : R < ‖z.1‖ ∨ R < ‖z.2‖ := by
    rcases lt_max_iff.1 hz' with h | h
    · exact Or.inl h
    · exact Or.inr h
  rcases hmax with h | h
  · have := hρ (jbracket z.1) ((le_max_left ρ 1).trans (h.le.trans (s83_norm_le_jb _)))
    calc jbracket z.1 ^ (-κ) * jbracket z.2 ^ (-κ) ≤ jbracket z.1 ^ (-κ) * 1 :=
          mul_le_mul_of_nonneg_left (hone _) (hpos _)
      _ < η := by rwa [mul_one]
  · have := hρ (jbracket z.2) ((le_max_left ρ 1).trans (h.le.trans (s83_norm_le_jb _)))
    calc jbracket z.1 ^ (-κ) * jbracket z.2 ^ (-κ) ≤ 1 * jbracket z.2 ^ (-κ) :=
          mul_le_mul_of_nonneg_right (hone _) (hpos _)
      _ < η := by rwa [one_mul]

theorem s8h2_pair_of_growth {M K : ℝ} (hKM : K < M) {j : ℕ} {F : Euc d × Euc d → ℝ} (hF : ContDiff ℝ j F)
    (hg : ∀ k : ℕ, k ≤ j → ∃ CR : ℝ, ∀ x y : Euc d,
      ‖iteratedFDeriv ℝ k F (x, y)‖ ≤ CR * jbracket x ^ K * jbracket y ^ K) : S8hPair M j F := by
  refine ⟨hF, fun i hi => ?_⟩
  obtain ⟨CR, hCR⟩ := hg i hi
  have hκ : 0 < M - K := by linarith
  have h0 := (s8h2_decay_prod (d := d) hκ).const_mul |CR|
  rw [mul_zero] at h0
  refine squeeze_zero (fun z => by have := s8h_w_pos M z; positivity) (fun z => ?_) h0
  have hx := Real.rpow_pos_of_pos (s83_jb_pos z.1) M
  have hy := Real.rpow_pos_of_pos (s83_jb_pos z.2) M
  have h1 := hCR z.1 z.2
  have e1 : jbracket z.1 ^ (-(M - K)) = jbracket z.1 ^ K / jbracket z.1 ^ M := by
    rw [show -(M - K) = K - M by ring, Real.rpow_sub (s83_jb_pos _)]
  have e2 : jbracket z.2 ^ (-(M - K)) = jbracket z.2 ^ K / jbracket z.2 ^ M := by
    rw [show -(M - K) = K - M by ring, Real.rpow_sub (s83_jb_pos _)]
  show ‖iteratedFDeriv ℝ i F z‖ / s8h_w M z ≤ |CR| * (jbracket z.1 ^ (-(M - K)) * jbracket z.2 ^ (-(M - K)))
  rw [e1, e2]
  unfold s8h_w
  rw [div_le_iff₀ (mul_pos hx hy)]
  have hKx := Real.rpow_nonneg (s83_jb_pos z.1).le K
  have hKy := Real.rpow_nonneg (s83_jb_pos z.2).le K
  calc ‖iteratedFDeriv ℝ i F z‖ ≤ CR * jbracket z.1 ^ K * jbracket z.2 ^ K := h1
    _ ≤ |CR| * jbracket z.1 ^ K * jbracket z.2 ^ K := by
        refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self _) hKx) hKy
    _ = |CR| * (jbracket z.1 ^ K / jbracket z.1 ^ M * (jbracket z.2 ^ K / jbracket z.2 ^ M)) *
          (jbracket z.1 ^ M * jbracket z.2 ^ M) := by field_simp

section Interface

variable {a β : ℝ} {ρβ : Euc d → ℝ} {M : ℝ} {U : ℝ → (Euc d → ℝ) → Euc d → ℝ}

theorem s8h2_c5 (hd : 2 ≤ d) (ha : 0 < a) (hβ : 0 < β)
    (hρ : IsThermalEquilibrium d ((d : ℝ) / 2) a β ρβ) (hM : 0 < M)
    (hU : IsWeightedSemigroup (critCoeff d a β ρβ) (HRS.Whole.withDensityReal ρβ) M U) :
    S8eC5 a β ρβ M U := by
  have h3 := s8f_clause3 hd ha hβ hρ hM hU
  have h4b := s8g_clause4b hd ha hβ hρ hM hU
  intro j hj R hR hdc hgr
  obtain ⟨K, hKM, hgrowth⟩ := hgr
  set F : Euc d × Euc d → ℝ := Function.uncurry R with hFdef
  have hF : S8hPair M j F := s8h2_pair_of_growth hKM hR hgrowth
  have hF2 : S8hPair M 2 F := s8h2_pair_mono hj hF
  have hdc' : IsDoublyCentered (HRS.Whole.withDensityReal ρβ) (fun x y => F (x, y)) := hdc
  obtain ⟨b, hbi, hb0, ⟨C, c, hc, hbe⟩, hbd, hS⟩ := s8h2_psi_reg hd ha hβ hρ hU h3 h4b hM.le j hF hdc'
  have hΨ : Function.uncurry (pairInverseW U R) = fun z => ∫ t in Set.Ioi (0 : ℝ), s8h2_S U t F z := rfl
  have hintOn : ∀ z, IntegrableOn (fun t => s8h2_S U t F z) (Set.Ioi 0) := fun z => by
    refine Integrable.mono' (hbi.integrableOn.mul_const (s8h_w M z))
      (((s8h2_S_cont hd ha hβ hρ hU h3 hM.le hF z).mono Set.Ioi_subset_Ici_self).aestronglyMeasurable
        measurableSet_Ioi) ?_
    refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun t ht => ?_)
    have := (hbd t ht).2 0 (Nat.zero_le j) z
    rwa [norm_iteratedFDeriv_zero] at this
  obtain ⟨hΨ2, hΨform, hΨb⟩ := hS (Set.Ioi 0) measurableSet_Ioi subset_rfl
  refine ⟨fun x y => hintOn (x, y), ?_, fun k hk => ⟨∫ t in Set.Ioi (0 : ℝ), b t, fun x y => ?_⟩, fun x y => ?_⟩
  · rw [hΨ]; exact hΨ2
  · rw [hΨ]
    have := hΨb k hk (x, y)
    unfold s8h_w at this
    dsimp only at this
    calc _ ≤ _ := this
      _ = _ := by ring
  · -- the equation, by the horizons `T_n = n + 2`
    set Tn : ℕ → ℝ := fun n => (n : ℝ) + 2 with hTn
    have hTpos : ∀ n, 0 < Tn n := fun n => by simp only [hTn]; positivity
    have hT1 : ∀ n, 1 < Tn n := fun n => by simp only [hTn]; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    have hIoc : ∀ n, Set.Ioc (0 : ℝ) (Tn n) ⊆ Set.Ioi 0 := fun n t ht => ht.1
    have hIoiT : ∀ n, Set.Ioi (Tn n) ⊆ Set.Ioi (0 : ℝ) := fun n t ht => (hTpos n).trans ht
    have hunion : ∀ n z, (∫ t in Set.Ioi (0 : ℝ), s8h2_S U t F z) -
        (∫ t in Set.Ioc 0 (Tn n), s8h2_S U t F z) = ∫ t in Set.Ioi (Tn n), s8h2_S U t F z := by
      intro n z
      have e : Set.Ioc (0 : ℝ) (Tn n) ∪ Set.Ioi (Tn n) = Set.Ioi 0 := Set.Ioc_union_Ioi_eq_Ioi (hTpos n).le
      have hdisj : Disjoint (Set.Ioc (0 : ℝ) (Tn n)) (Set.Ioi (Tn n)) :=
        Set.disjoint_left.2 (fun t h1 h2 => absurd h1.2 (not_le.2 h2))
      rw [← e, setIntegral_union hdisj measurableSet_Ioi ((hintOn z).mono_set (hIoc n))
        ((hintOn z).mono_set (hIoiT n))]
      ring
    have hcD0 : ∀ n, 0 ≤ ∫ t in Set.Ioi (Tn n), b t := fun n => setIntegral_nonneg measurableSet_Ioi (fun t _ => hb0 t)
    have hcDt : Tendsto (fun n => ∫ t in Set.Ioi (Tn n), b t) atTop (𝓝 0) := by
      have h := tendsto_setIntegral_of_antitone (μ := volume) (f := b) (s := fun n : ℕ => Set.Ioi (Tn n))
        (fun n => measurableSet_Ioi) (fun m n hmn => Set.Ioi_subset_Ioi (by
          simp only [hTn]
          have : (m : ℝ) ≤ n := by exact_mod_cast hmn
          linarith)) ⟨0, hbi.integrableOn⟩
      have hempty : (⋂ n : ℕ, Set.Ioi (Tn n)) = ∅ := by
        refine Set.eq_empty_iff_forall_notMem.2 fun t ht => ?_
        obtain ⟨n, hn⟩ := exists_nat_gt t
        have := Set.mem_iInter.1 ht n
        simp only [Set.mem_Ioi, hTn] at this
        linarith
      rw [hempty] at h
      simpa using h
    have hmono : ∀ n, (∫ t in Set.Ioc 0 (Tn n), b t) ≤ ∫ t in Set.Ioi (0 : ℝ), b t := fun n =>
      setIntegral_mono_set hbi.integrableOn (Eventually.of_forall fun t => hb0 t)
        (Eventually.of_forall (hIoc n))
    have hRt : Tendsto (fun n => s8h2_S U (Tn n) F (x, y) - F (x, y)) atTop (𝓝 (-F (x, y))) := by
      have hw := (s8h_w_pos M (x, y)).le
      have h0 : Tendsto (fun n => s8h2_S U (Tn n) F (x, y)) atTop (𝓝 0) := by
        refine squeeze_zero_norm' (Eventually.of_forall fun n => ?_)
          (a := fun n => C * Real.exp (-c * Tn n) * s8h_w M (x, y)) ?_
        · have h1 := (hbd (Tn n) (hTpos n)).2 0 (Nat.zero_le j) (x, y)
          rw [norm_iteratedFDeriv_zero] at h1
          exact h1.trans (mul_le_mul_of_nonneg_right (hbe _ (hT1 n)) hw)
        · have h2 : Tendsto (fun n : ℕ => Tn n) atTop atTop := by
            simp only [hTn]
            exact tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
          have h3' : Tendsto (fun n : ℕ => Real.exp (-c * Tn n)) atTop (𝓝 0) := by
            exact Real.tendsto_exp_atBot.comp (h2.const_mul_atTop_of_neg (by linarith : -c < 0))
          simpa using (h3'.const_mul C).mul_const (s8h_w M (x, y))
      simpa using h0.sub_const (F (x, y))
    have key := s8h2_eq_limit hd ha hβ hρ hM.le (ΦF := fun z => ∫ t in Set.Ioi (0 : ℝ), s8h2_S U t F z)
      (ΦG := fun n z => ∫ t in Set.Ioc 0 (Tn n), s8h2_S U t F z)
      (cF := ∫ t in Set.Ioi (0 : ℝ), b t) (cG := ∫ t in Set.Ioi (0 : ℝ), b t)
      (setIntegral_nonneg measurableSet_Ioi (fun t _ => hb0 t))
      (setIntegral_nonneg measurableSet_Ioi (fun t _ => hb0 t))
      (hΨ2.of_le (by exact_mod_cast hj)) (fun k hk z => hΨb k (hk.trans hj) z)
      (fun n => ((hS (Set.Ioc 0 (Tn n)) measurableSet_Ioc (hIoc n)).1).of_le (by exact_mod_cast hj))
      (fun n k hk z => ((hS (Set.Ioc 0 (Tn n)) measurableSet_Ioc (hIoc n)).2.2 k (hk.trans hj) z).trans
        (mul_le_mul_of_nonneg_right (hmono n) (s8h_w_pos M z).le))
      (cD := fun n => ∫ t in Set.Ioi (Tn n), b t) hcD0 hcDt
      (fun n k hk z => by
        have e : (fun z => (∫ t in Set.Ioi (0 : ℝ), s8h2_S U t F z) - ∫ t in Set.Ioc 0 (Tn n), s8h2_S U t F z) =
            fun z => ∫ t in Set.Ioi (Tn n), s8h2_S U t F z := funext fun z => hunion n z
        rw [e]
        exact (hS (Set.Ioi (Tn n)) measurableSet_Ioi (hIoiT n)).2.2 k (hk.trans hj) z)
      (Rn := fun n => s8h2_S U (Tn n) F (x, y) - F (x, y)) (R0 := -F (x, y)) hRt x y
      (fun n => s8h2_eq_T hd ha hβ hρ hU h3 hM.le (hTpos n) hF2 x y)
    have hkey : projGeneratorW (critCoeff d a β ρβ) (HRS.Whole.withDensityReal ρβ) 0
        (fun x' => pairInverseW U R x' y) x +
        projGeneratorW (critCoeff d a β ρβ) (HRS.Whole.withDensityReal ρβ) 0 (pairInverseW U R x) y =
        -F (x, y) := key
    rw [hkey]
    simp [hFdef, Function.uncurry]

end Interface

/-- The frozen statement of `weighted_adjoint_decay` (S8.3). -/
theorem weighted_adjoint_decay_proof (hd : 2 ≤ d) (a β : ℝ) (ha : 0 < a) (hβ : 0 < β) (ρβ : Euc d → ℝ)
    (hρ : IsThermalEquilibrium d ((d : ℝ) / 2) a β ρβ) (M : ℝ) (hM : 0 < M) :
    type_of% (@HRS.Whole.weighted_adjoint_decay d hd a β ha hβ ρβ hρ M hM) :=
  s8g_wad_of_c5 hd ha hβ hρ hM (fun _ hU => s8h2_c5 hd ha hβ hρ hM hU)

example := (@weighted_adjoint_decay_proof : type_of% (@HRS.Whole.weighted_adjoint_decay))

end HRS.MS.Wad
