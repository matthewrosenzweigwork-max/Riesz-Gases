import HRS.Energy.Commutator.RoughLimit
import HRS.PDE.MeanFieldThermalExist

/-!
# The regularised stress inequality and its limit (packet CM-S3, helpers for `stress_rough`)

For a finite measure `m` and a bounded density `s` (with `∫ s dm = 0` when `l = 0`) put
`ρ_ε = hk_ε ⋆ (s m)` and `H_ε = (cW l ε) ⋆ (s m)`.  Then `(l - Δ) H_ε = e^{-lε} ρ_ε`, the energy is
`∫ H_ε ρ_ε = e^{-lε} ∬ s s Ê_ε` and the commutator pairing is `e^{-lε}/2 ∬ s s k_ε`, with
`k_ε = (hk_ε ⊗ hk_ε) ⋆ k`.  `StressAux.stress_bound` gives the inequality at level `ε`.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators
open HRS HRS.KernelAux HRS.Commutator.FourierAux HRS.Commutator.RoughAux HRS.Commutator.RoughHeat
  HRS.Commutator.RoughKernel HRS.Commutator.RoughLimit

namespace HRS.Commutator.RoughMain

variable {d : ℕ}

theorem cW_gauss {l : ℝ} (hl : 0 ≤ l) {ε : ℝ} (hε : 0 < ε) : GaussDecay (cW (d := d) l ε) :=
  ⟨4 * Real.pi ^ 2 * ε, 1 / l + 1 / (4 * Real.pi ^ 2), by positivity, fun k => cW_bound hl hε.le k⟩

theorem cW_mul_aW {l : ℝ} (ε : ℝ) (hl : 0 ≤ l) (k : Lattice d) :
    cW l ε k * aW ε k = Real.exp (l * ε) * cW l (2 * ε) k := by
  rw [cW_two hl ε k, ← mul_assoc, ← mul_assoc, ← Real.exp_add]
  simp

theorem ser_cW_mul_aW {l : ℝ} (hl : 0 ≤ l) (ε : ℝ) (w : Torus d) :
    ser (fun k => cW l ε k * aW ε k) w = Real.exp (l * ε) * ser (cW l (2 * ε)) w := by
  unfold ser
  rw [← tsum_mul_left]
  refine tsum_congr fun k => ?_
  dsimp only
  rw [cW_mul_aW ε hl k]; ring

/-- The energy identity at level `ε`. -/
theorem energy_side {l : ℝ} (hl : 0 ≤ l) {ε : ℝ} (hε : 0 < ε) (m : Measure (Torus d)) [IsFiniteMeasure m]
    {s : Torus d → ℝ} (hsm : Measurable s) (hs : ∀ y, |s y| ≤ 1) :
    ∫ x, convS (ser (cW l ε)) m s x * convS (ser (aW ε)) m s x =
      Real.exp (-(l * ε)) * ∫ p, s p.1 * s p.2 * Ehat l ε (p.1 - p.2) ∂(m.prod m) := by
  have hcG := cW_gauss (d := d) hl hε
  have haG := aW_gauss (d := d) hε
  have hbc : ∀ x : Torus d, |ser (cW l ε) x| ≤ ∑' k, |cW l ε k| := hcG.bound
  have hba : ∀ x : Torus d, |ser (aW ε) x| ≤ ∑' k, |aW ε k| := haG.bound
  have hcm : Measurable (Function.uncurry fun x y : Torus d => ser (cW l ε) (x - y)) :=
    ((continuous_ser hcG.summable).measurable.comp (measurable_fst.sub measurable_snd))
  have ham : Measurable (Function.uncurry fun x y : Torus d => ser (aW ε) (x - y)) :=
    ((continuous_ser haG.summable).measurable.comp (measurable_fst.sub measurable_snd))
  have key := fubini_pair m hsm hs (f := fun x y => ser (cW l ε) (x - y)) (g := fun x y => ser (aW ε) (x - y))
    hcm ham (M := (∑' k, |cW l ε k|) + ∑' k, |aW ε k|)
    (fun x y => (hbc _).trans (le_add_of_nonneg_right (tsum_nonneg fun _ => abs_nonneg _)))
    (fun x y => (hba _).trans (le_add_of_nonneg_left (tsum_nonneg fun _ => abs_nonneg _)))
  have e1 : ∀ x : Torus d, convS (ser (cW l ε)) m s x * convS (ser (aW ε)) m s x =
      (∫ y, ser (cW l ε) (x - y) * s y ∂m) * (∫ z, ser (aW ε) (x - z) * s z ∂m) := fun x => rfl
  simp_rw [e1]
  rw [key]
  have e2 : ∀ p : Torus d × Torus d, ∫ x, ser (cW l ε) (x - p.1) * ser (aW ε) (x - p.2) =
      Real.exp (l * ε) * ser (cW l (2 * ε)) (p.1 - p.2) := by
    intro p
    rw [integral_kernel_pair (fun x => ser_neg _ x) p.1 p.2,
      convS_ser_ser hcG haG (cW_even l ε) (aW_even ε), ser_cW_mul_aW hl]
  simp_rw [e2]
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
  simp only [Ehat]
  have : Real.exp (-(l * ε)) * Real.exp (2 * l * ε) = Real.exp (l * ε) := by
    rw [← Real.exp_add]; congr 1; ring
  calc s p.1 * s p.2 * (Real.exp (l * ε) * ser (cW l (2 * ε)) (p.1 - p.2))
      = s p.1 * s p.2 * ((Real.exp (-(l * ε)) * Real.exp (2 * l * ε)) * ser (cW l (2 * ε)) (p.1 - p.2)) := by
        rw [this]
    _ = _ := by ring


/-- The stress inequality at level `ε`. -/
theorem level_stress {l : ℝ} (hl : 0 ≤ l) {ε : ℝ} (hε : 0 < ε) (m : Measure (Torus d)) [IsFiniteMeasure m]
    {s : Torus d → ℝ} (hsm : Measurable s) (hs : ∀ y, |s y| ≤ 1) (hneut : l = 0 → ∫ y, s y ∂m = 0)
    {L : ℝ} (hL : 0 ≤ L) {v : Torus d → Euc d} (hv : IsLipschitzVF L v) :
    |∫ x, convS (ser (aW ε)) m s x * inner ℝ (v x) (Torus.grad (convS (ser (cW l ε)) m s) x)| ≤
      (2 * d + 1) * L * ∫ x, convS (ser (cW l ε)) m s x * convS (ser (aW ε)) m s x := by
  set H := convS (ser (cW l ε)) m s with hH
  set ρ := convS (ser (aW ε)) m s with hρ
  have hcG := cW_gauss (d := d) hl hε
  have hH2 : Torus.IsCk 2 H := by
    obtain ⟨ε', C, hε', hC⟩ := hcG
    exact isCk_convS 2 hε' hC (cW_even l ε) m hsm hs
  have hgreen : ∀ x, l * H x - Torus.laplacian H x = Real.exp (-l * ε) * ρ x := fun x =>
    green_identity hl hε m hsm hs hneut x
  have h1 := StressAux.stress_bound d hl hL hv hH2
  have e1 : ∫ x, (l * H x - Torus.laplacian H x) * inner ℝ (v x) (Torus.grad H x) =
      Real.exp (-l * ε) * ∫ x, ρ x * inner ℝ (v x) (Torus.grad H x) := by
    rw [← integral_const_mul]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => by simp only [hgreen x]; ring)
  have e2 : ∫ x, (l * H x ^ 2 + ‖Torus.grad H x‖ ^ 2) = Real.exp (-l * ε) * ∫ x, H x * ρ x := by
    rw [energy_by_parts hH2 l, ← integral_const_mul]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => by simp only [hgreen x]; ring)
  rw [e1, e2, abs_mul, abs_of_pos (Real.exp_pos _)] at h1
  have hpos := Real.exp_pos (-l * ε)
  have : Real.exp (-l * ε) * |∫ x, ρ x * inner ℝ (v x) (Torus.grad H x)| ≤
      Real.exp (-l * ε) * ((2 * d + 1) * L * ∫ x, H x * ρ x) := by
    calc _ ≤ _ := h1
      _ = _ := by ring
  exact le_of_mul_le_mul_left this hpos


/-- `∂_j H_ε = e^{-lε} ∂_j𝒢_l ⋆ ρ_ε`. -/
theorem grad_formula {l : ℝ} (hl : 0 ≤ l) {ε : ℝ} (hε : 0 < ε) (m : Measure (Torus d)) [IsFiniteMeasure m]
    {s : Torus d → ℝ} (hsm : Measurable s) (hs : ∀ y, |s y| ≤ 1) (j : Fin d) (x : Torus d) :
    Torus.partialDeriv j (convS (ser (cW l ε)) m s) x =
      Real.exp (-(l * ε)) * ∫ u, SliceAux.sgc j l u * convS (ser (aW ε)) m s (x - u) := by
  have hcG := cW_gauss (d := d) hl hε
  obtain ⟨ε', C, hε', hC⟩ := hcG
  rw [partialDeriv_convS j hε' hC (cW_even l ε) m hsm hs]
  unfold convS
  have e1 : ∀ y : Torus d, Torus.partialDeriv j (ser (cW l ε)) (x - y) * s y =
      Real.exp (-(l * ε)) * (s y * ∫ u, SliceAux.sgc j l u * hk ε (x - y - u)) := fun y => by
    rw [ser_cW_partialDeriv hl hε j (x - y)]; ring
  simp_rw [e1]
  rw [integral_const_mul]
  congr 1
  obtain ⟨M, hM⟩ := hk_bdd hε
  have hsg := integrable_sgc (d := d) j hl
  have hint : Integrable (Function.uncurry fun (y u : Torus d) => s y * (SliceAux.sgc j l u * hk ε (x - y - u)))
      (m.prod (volume : Measure (Torus d))) := by
    have hmeas : Measurable (Function.uncurry fun (y u : Torus d) => s y * (SliceAux.sgc j l u * hk ε (x - y - u))) :=
      (hsm.comp measurable_fst).mul (((SliceAux.measurable_sgc j).comp
        (measurable_const.prodMk measurable_snd)).mul
        ((continuous_hk hε).measurable.comp ((measurable_const.sub measurable_fst).sub measurable_snd)))
    refine Integrable.mono' (g := fun p : Torus d × Torus d => M * |SliceAux.sgc j l p.2|)
      ((hsg.abs.comp_snd m).const_mul M) hmeas.aestronglyMeasurable (Filter.Eventually.of_forall fun p => ?_)
    simp only [Function.uncurry, Real.norm_eq_abs, abs_mul]
    have h1 := hs p.1
    have h2 : |hk ε (x - p.1 - p.2)| ≤ M := by rw [abs_of_nonneg (hk_nonneg hε _)]; exact hM _
    calc |s p.1| * (|SliceAux.sgc j l p.2| * |hk ε (x - p.1 - p.2)|) ≤ 1 * (|SliceAux.sgc j l p.2| * M) := by
          gcongr
      _ = M * |SliceAux.sgc j l p.2| := by ring
  have e2 : (∫ y, s y * (∫ u, SliceAux.sgc j l u * hk ε (x - y - u)) ∂m) =
      ∫ y, (∫ u, s y * (SliceAux.sgc j l u * hk ε (x - y - u)) ∂(volume : Measure (Torus d))) ∂m := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only []
    rw [← integral_const_mul]
  rw [e2, integral_integral_swap hint]
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  simp only []
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp only []
  rw [show x - y - u = (x - u) - y by abel]
  simp only [hk]
  ring


theorem continuous_rho {ε : ℝ} (hε : 0 < ε) (m : Measure (Torus d)) [IsFiniteMeasure m]
    {s : Torus d → ℝ} (hsm : Measurable s) (hs : ∀ y, |s y| ≤ 1) :
    Continuous (convS (ser (aW ε)) m s) :=
  continuous_convS (continuous_ser (aW_gauss (d := d) hε).summable) m hsm hs

/-- The commutator pairing in terms of `ρ_ε`. -/
theorem comm_side {l : ℝ} (hl : 0 ≤ l) {ε : ℝ} (hε : 0 < ε) (m : Measure (Torus d)) [IsFiniteMeasure m]
    {s : Torus d → ℝ} (hsm : Measurable s) (hs : ∀ y, |s y| ≤ 1) (v : Torus d → Euc d) :
    ∫ x, convS (ser (aW ε)) m s x * inner ℝ (v x) (Torus.grad (convS (ser (cW l ε)) m s) x) =
      Real.exp (-(l * ε)) * ∫ x, ∫ y, convS (ser (aW ε)) m s x * convS (ser (aW ε)) m s y *
        inner ℝ (v x) (SliceAux.sgv l (x - y)) := by
  set ρ := convS (ser (aW ε)) m s with hρ
  have hρc : Continuous ρ := continuous_rho hε m hsm hs
  obtain ⟨Mρ, hMρ⟩ := PDE.MFSchauder.exists_bound_of_cont hρc
  have hin : ∀ a w : Euc d, inner ℝ a w = ∑ j, a j * w j := fun a w => by
    simp [PiLp.inner_apply, mul_comm]
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only []
  -- Step A
  have hA : ρ x * inner ℝ (v x) (Torus.grad (convS (ser (cW l ε)) m s) x) =
      Real.exp (-(l * ε)) * ∫ u, ρ x * ρ (x - u) * inner ℝ (v x) (SliceAux.sgv l u) := by
    rw [StressAux.inner_grad]
    simp_rw [grad_formula hl hε m hsm hs]
    have hint : ∀ j : Fin d, Integrable (fun u : Torus d => ρ x * (v x j * (SliceAux.sgc j l u * ρ (x - u)))) := by
      intro j
      have h1 : Integrable (fun u : Torus d => SliceAux.sgc j l u * ρ (x - u)) :=
        (integrable_sgc j hl).mul_bdd (c := Mρ)
          (hρc.measurable.comp (measurable_const.sub measurable_id)).aestronglyMeasurable
          (Filter.Eventually.of_forall fun u => by simpa using hMρ (x - u))
      exact (h1.const_mul _).const_mul _
    have e1 : ∀ u : Torus d, ρ x * ρ (x - u) * inner ℝ (v x) (SliceAux.sgv l u) =
        ∑ j, ρ x * (v x j * (SliceAux.sgc j l u * ρ (x - u))) := by
      intro u
      rw [hin, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [SliceAux.sgv, PiLp.toLp_apply]
      ring
    simp_rw [e1]
    rw [integral_finset_sum _ fun j _ => hint j, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_const_mul, integral_const_mul]
    ring
  rw [hA]
  congr 1
  -- Step B: change of variables `u = x - y`
  have := integral_sub_left_eq_self (fun u : Torus d => ρ x * ρ (x - u) * inner ℝ (v x) (SliceAux.sgv l u))
    (volume : Measure (Torus d)) x
  rw [← this]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp only [sub_sub_cancel]


theorem sgv_zero (l : ℝ) : SliceAux.sgv l (0 : Torus d) = 0 := by
  have h := sgv_neg l (0 : Torus d)
  rw [neg_zero] at h
  have : SliceAux.sgv l (0 : Torus d) + SliceAux.sgv l 0 = 0 := by
    nth_rewrite 2 [h]; simp
  have h2 : (2 : ℝ) • SliceAux.sgv l (0 : Torus d) = 0 := by rw [two_smul]; exact this
  exact (smul_eq_zero.mp h2).resolve_left (by norm_num)

theorem norm_sgv_le' (l : ℝ) (z : Torus d) : ‖SliceAux.sgv l z‖ ≤ ∑ j, |SliceAux.sgc j l z| :=
  SliceAux.norm_sgv_le l z

/-- Symmetrisation of the commutator pairing. -/
theorem double_sym {l : ℝ} (hl : 0 ≤ l) {ρ : Torus d → ℝ} (hρc : Continuous ρ) {v : Torus d → Euc d}
    (hvc : Continuous v) :
    2 * ∫ x, ∫ y, ρ x * ρ y * inner ℝ (v x) (SliceAux.sgv l (x - y)) =
      ∫ p : Torus d × Torus d, ρ p.1 * ρ p.2 * kk l v p.1 p.2 ∂((volume : Measure (Torus d)).prod volume) := by
  obtain ⟨Mρ, hMρ⟩ := PDE.MFSchauder.exists_bound_of_cont hρc
  obtain ⟨Mv, hMv⟩ := isCompact_univ.exists_bound_of_continuousOn hvc.continuousOn
  set a : Torus d → Torus d → ℝ := fun x y => ρ x * ρ y * inner ℝ (v x) (SliceAux.sgv l (x - y)) with ha
  have hmeas : Measurable (Function.uncurry a) := by
    simp only [Function.uncurry, ha]
    refine (((hρc.measurable.comp measurable_fst).mul (hρc.measurable.comp measurable_snd))).mul ?_
    refine Measurable.inner (hvc.measurable.comp measurable_fst) ?_
    exact (SliceAux.measurable_sgv (d := d)).comp (measurable_const.prodMk (measurable_fst.sub measurable_snd) :
      Measurable fun p : Torus d × Torus d => (l, p.1 - p.2))
  have hmaj : Integrable (fun p : Torus d × Torus d => Mρ * Mρ * Mv * ∑ j, |SliceAux.sgc j l (p.1 - p.2)|)
      ((volume : Measure (Torus d)).prod (volume : Measure (Torus d))) := by
    have h1 : Integrable (fun w : Torus d => Mρ * Mρ * Mv * ∑ j, |SliceAux.sgc j l w|) :=
      (integrable_finset_sum _ fun j _ => (integrable_sgc j hl).abs).const_mul _
    have hm1 : Measurable (fun w : Torus d => Mρ * Mρ * Mv * ∑ j, |SliceAux.sgc j l w|) :=
      measurable_const.mul (Finset.measurable_sum _ fun j _ => ((SliceAux.measurable_sgc j).comp
        (measurable_const.prodMk measurable_id)).abs)
    exact integrable_sub_prod hm1 h1
  have hI : Integrable (Function.uncurry a) ((volume : Measure (Torus d)).prod (volume : Measure (Torus d))) := by
    refine Integrable.mono' hmaj hmeas.aestronglyMeasurable (Filter.Eventually.of_forall fun p => ?_)
    simp only [Function.uncurry, ha, Real.norm_eq_abs, abs_mul]
    have h1 : |ρ p.1| ≤ Mρ := by simpa using hMρ p.1
    have h2 : |ρ p.2| ≤ Mρ := by simpa using hMρ p.2
    have h3 : ‖v p.1‖ ≤ Mv := by simpa using hMv p.1 (mem_univ _)
    have h4 : |inner ℝ (v p.1) (SliceAux.sgv l (p.1 - p.2))| ≤ Mv * ∑ j, |SliceAux.sgc j l (p.1 - p.2)| :=
      (abs_real_inner_le_norm _ _).trans (mul_le_mul h3 (norm_sgv_le' l _) (norm_nonneg _)
        ((norm_nonneg _).trans h3))
    have hMρ0 : 0 ≤ Mρ := (abs_nonneg _).trans h1
    have hMv0 : 0 ≤ Mv := (norm_nonneg _).trans h3
    calc |ρ p.1| * |ρ p.2| * |inner ℝ (v p.1) (SliceAux.sgv l (p.1 - p.2))|
        ≤ Mρ * Mρ * (Mv * ∑ j, |SliceAux.sgc j l (p.1 - p.2)|) := by
          refine mul_le_mul (mul_le_mul h1 h2 (abs_nonneg _) hMρ0) h4 (abs_nonneg _) (by positivity)
      _ = _ := by ring
  have hI2 : Integrable (fun p : Torus d × Torus d => a p.2 p.1)
      ((volume : Measure (Torus d)).prod (volume : Measure (Torus d))) := by
    exact hI.swap
  have h1 : ∫ x, ∫ y, a x y = ∫ p, a p.1 p.2 ∂((volume : Measure (Torus d)).prod volume) :=
    (integral_prod (fun p : Torus d × Torus d => a p.1 p.2) hI).symm
  have h2 : ∫ p : Torus d × Torus d, a p.2 p.1 ∂((volume : Measure (Torus d)).prod volume) =
      ∫ p : Torus d × Torus d, a p.1 p.2 ∂((volume : Measure (Torus d)).prod volume) :=
    integral_prod_swap (fun p : Torus d × Torus d => a p.1 p.2)
  have h4 : ∀ p : Torus d × Torus d, a p.1 p.2 + a p.2 p.1 = ρ p.1 * ρ p.2 * kk l v p.1 p.2 := by
    intro p
    obtain ⟨x, y⟩ := p
    simp only [ha, kk, commKernel]
    by_cases hxy : x = y
    · subst hxy
      simp [sgv_zero]
    · rw [if_neg hxy]
      have : y - x = -(x - y) := by abel
      rw [this, sgv_neg, inner_neg_right, inner_sub_left]
      ring
  rw [h1, two_mul]
  nth_rewrite 2 [← h2]
  rw [← integral_add (f := fun p : Torus d × Torus d => a p.1 p.2) hI hI2]
  exact integral_congr_ae (Filter.Eventually.of_forall fun p => h4 p)


/-- The mollified commutator kernel `k_ε = (hk_ε ⊗ hk_ε) ⋆ k`. -/
def kmol (l : ℝ) (v : Torus d → Euc d) (ε : ℝ) (y z : Torus d) : ℝ :=
  ∫ q : Torus d × Torus d, kk l v q.1 q.2 * hk ε (q.1 - y) * hk ε (q.2 - z)
    ∂((volume : Measure (Torus d)).prod volume)

/-- `∬ k ρ ρ = ∬ s s k_ε`. -/
theorem mollify_pair {l : ℝ} {ε : ℝ} (hε : 0 < ε) (m : Measure (Torus d)) [IsFiniteMeasure m]
    {s : Torus d → ℝ} (hsm : Measurable s) (hs : ∀ y, |s y| ≤ 1) {v : Torus d → Euc d}
    (hvc : Continuous v)
    (hkk : Integrable (fun p : Torus d × Torus d => kk l v p.1 p.2)
      ((volume : Measure (Torus d)).prod (volume : Measure (Torus d)))) :
    ∫ p : Torus d × Torus d, convS (ser (aW ε)) m s p.1 * convS (ser (aW ε)) m s p.2 * kk l v p.1 p.2
        ∂((volume : Measure (Torus d)).prod volume) =
      ∫ r : Torus d × Torus d, s r.1 * s r.2 * kmol l v ε r.1 r.2 ∂(m.prod m) := by
  obtain ⟨M, hM⟩ := hk_bdd hε
  have hM0 : 0 ≤ M := (hk_nonneg hε 0).trans (hM 0)
  have hkm := measurable_kk (l := l) hvc
  set G : (Torus d × Torus d) → (Torus d × Torus d) → ℝ := fun q r =>
    kk l v q.1 q.2 * (hk ε (q.1 - r.1) * s r.1 * (hk ε (q.2 - r.2) * s r.2)) with hG
  have hGm : Measurable (Function.uncurry G) := by
    simp only [Function.uncurry, hG]
    have h1 : Measurable fun z : (Torus d × Torus d) × (Torus d × Torus d) => kk l v z.1.1 z.1.2 :=
      hkm.comp (measurable_fst)
    have h2 : Measurable fun z : (Torus d × Torus d) × (Torus d × Torus d) => hk ε (z.1.1 - z.2.1) :=
      (continuous_hk hε).measurable.comp (measurable_fst.fst.sub measurable_snd.fst)
    have h3 : Measurable fun z : (Torus d × Torus d) × (Torus d × Torus d) => hk ε (z.1.2 - z.2.2) :=
      (continuous_hk hε).measurable.comp (measurable_fst.snd.sub measurable_snd.snd)
    exact h1.mul (((h2.mul (hsm.comp measurable_snd.fst))).mul (h3.mul (hsm.comp measurable_snd.snd)))
  have hGi : Integrable (Function.uncurry G)
      (((volume : Measure (Torus d)).prod volume).prod (m.prod m)) := by
    refine Integrable.mono' (g := fun z => M * M * |kk l v z.1.1 z.1.2|)
      ((hkk.abs.comp_fst (m.prod m)).const_mul (M * M)) hGm.aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => ?_)
    simp only [Function.uncurry, hG, Real.norm_eq_abs, abs_mul]
    have h1 : |hk ε (z.1.1 - z.2.1)| ≤ M := by rw [abs_of_nonneg (hk_nonneg hε _)]; exact hM _
    have h2 : |hk ε (z.1.2 - z.2.2)| ≤ M := by rw [abs_of_nonneg (hk_nonneg hε _)]; exact hM _
    have h3 := hs z.2.1
    have h4 := hs z.2.2
    calc |kk l v z.1.1 z.1.2| * (|hk ε (z.1.1 - z.2.1)| * |s z.2.1| * (|hk ε (z.1.2 - z.2.2)| * |s z.2.2|))
        ≤ |kk l v z.1.1 z.1.2| * (M * 1 * (M * 1)) := by gcongr
      _ = _ := by ring
  have e1 : ∀ q : Torus d × Torus d,
      convS (ser (aW ε)) m s q.1 * convS (ser (aW ε)) m s q.2 * kk l v q.1 q.2 =
        ∫ r, G q r ∂(m.prod m) := by
    intro q
    have := integral_prod_mul (μ := m) (ν := m) (fun y => hk ε (q.1 - y) * s y) (fun z => hk ε (q.2 - z) * s z)
    simp only [hG]
    rw [integral_const_mul, this]
    simp only [convS, hk]
    ring
  simp_rw [e1]
  rw [integral_integral_swap hGi]
  refine integral_congr_ae (Filter.Eventually.of_forall fun r => ?_)
  simp only [hG, kmol]
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun q => ?_)
  ring


/-- The inequality at level `ε`. -/
theorem level_ineq (hd : 1 ≤ d) {l : ℝ} (hl : 0 ≤ l) {ε : ℝ} (hε : 0 < ε) (m : Measure (Torus d))
    [IsFiniteMeasure m] {s : Torus d → ℝ} (hsm : Measurable s) (hs : ∀ y, |s y| ≤ 1)
    (hneut : l = 0 → ∫ y, s y ∂m = 0) {L : ℝ} (hL : 0 ≤ L) {v : Torus d → Euc d}
    (hv : IsLipschitzVF L v) :
    |∫ r : Torus d × Torus d, s r.1 * s r.2 * kmol l v ε r.1 r.2 ∂(m.prod m)| ≤
      2 * ((2 * d + 1) * L) * ∫ r : Torus d × Torus d, s r.1 * s r.2 * Ehat l ε (r.1 - r.2) ∂(m.prod m) := by
  have hvc : Continuous v := lipschitzVF_continuous hL hv
  have hkk := integrable_kk hd hl hL hv
  have h1 := level_stress hl hε m hsm hs hneut hL hv
  rw [comm_side hl hε m hsm hs v, energy_side hl hε m hsm hs, abs_mul, abs_of_pos (Real.exp_pos _)] at h1
  have hρc := continuous_rho hε m hsm hs
  have h2 := double_sym hl hρc hvc
  rw [mollify_pair hε m hsm hs hvc hkk] at h2
  rw [← h2, abs_mul, abs_two]
  have hpos := Real.exp_pos (-(l * ε))
  have : Real.exp (-(l * ε)) * |∫ x, ∫ y, convS (ser (aW ε)) m s x * convS (ser (aW ε)) m s y *
      inner ℝ (v x) (SliceAux.sgv l (x - y))| ≤ Real.exp (-(l * ε)) * (
        (2 * d + 1) * L * ∫ r : Torus d × Torus d, s r.1 * s r.2 * Ehat l ε (r.1 - r.2) ∂(m.prod m)) := by
    calc _ ≤ _ := h1
      _ = _ := by ring
  have h3 := le_of_mul_le_mul_left this hpos
  linarith


/-- `∬ φ(q₁-q₂) hk_ε(q₁-y) hk_ε(q₂-z) = (φ ⋆ hk_{2ε})(y-z)`. -/
theorem J_eq {φ : Torus d → ℝ} (hφm : Measurable φ) (hφ : Integrable φ) {ε : ℝ} (hε : 0 < ε) (y z : Torus d) :
    ∫ q : Torus d × Torus d, φ (q.1 - q.2) * hk ε (q.1 - y) * hk ε (q.2 - z)
      ∂((volume : Measure (Torus d)).prod volume) = ∫ u, φ u * hk (2 * ε) (y - z - u) := by
  obtain ⟨M, hM⟩ := hk_bdd hε
  have hM0 : 0 ≤ M := (hk_nonneg hε 0).trans (hM 0)
  have hPc := continuous_hk (d := d) hε
  have hmeas : Measurable fun q : Torus d × Torus d => φ (q.1 - q.2) * hk ε (q.1 - y) * hk ε (q.2 - z) :=
    ((hφm.comp (measurable_fst.sub measurable_snd)).mul
      (hPc.measurable.comp (measurable_fst.sub measurable_const))).mul
      (hPc.measurable.comp (measurable_snd.sub measurable_const))
  have hI : Integrable (fun q : Torus d × Torus d => φ (q.1 - q.2) * hk ε (q.1 - y) * hk ε (q.2 - z))
      ((volume : Measure (Torus d)).prod (volume : Measure (Torus d))) := by
    refine Integrable.mono' (g := fun q : Torus d × Torus d => M * M * |φ (q.1 - q.2)|)
      ((integrable_sub_prod hφm.abs hφ.abs).const_mul (M * M)) hmeas.aestronglyMeasurable
      (Filter.Eventually.of_forall fun q => ?_)
    simp only [Real.norm_eq_abs, abs_mul]
    have h1 : |hk ε (q.1 - y)| ≤ M := by rw [abs_of_nonneg (hk_nonneg hε _)]; exact hM _
    have h2 : |hk ε (q.2 - z)| ≤ M := by rw [abs_of_nonneg (hk_nonneg hε _)]; exact hM _
    calc |φ (q.1 - q.2)| * |hk ε (q.1 - y)| * |hk ε (q.2 - z)| ≤ |φ (q.1 - q.2)| * M * M := by gcongr
      _ = _ := by ring
  rw [integral_prod _ hI]
  set P := hk (d := d) ε with hP
  set ψ := convFun φ P with hψ
  have step1 : ∀ q1 : Torus d, ∫ q2, φ (q1 - q2) * P (q1 - y) * P (q2 - z) = P (q1 - y) * ψ (q1 - z) := by
    intro q1
    have e : ∀ q2 : Torus d, φ (q1 - q2) * P (q1 - y) * P (q2 - z) = P (q1 - y) * (φ (q1 - q2) * P (q2 - z)) :=
      fun q2 => by ring
    simp_rw [e]
    rw [integral_const_mul]
    congr 1
    rw [← integral_add_right_eq_self (fun q2 : Torus d => φ (q1 - q2) * P (q2 - z)) z]
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    simp only [hψ, convFun]
    rw [add_sub_cancel_right, show q1 - (t + z) = q1 - z - t by abel]
  simp_rw [step1]
  have step2 : ∫ q1 : Torus d, P (q1 - y) * ψ (q1 - z) = convFun P ψ (y - z) := by
    rw [← integral_add_right_eq_self (fun q1 : Torus d => P (q1 - y) * ψ (q1 - z)) z]
    simp only [convFun]
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    show P (t + z - y) * ψ (t + z - z) = P (y - z - t) * ψ t
    rw [add_sub_cancel_right, show t + z - y = -(y - z - t) by abel]
    exact congrArg (· * ψ t) (hk_neg ε _)
  rw [step2]
  have step3 : convFun P ψ (y - z) = convFun φ (hk (2 * ε)) (y - z) := by
    have hφc : Integrable φ := hφ
    have e1 : convFun P (convFun φ P) = convFun (convFun P φ) P := by
      funext x
      have hc : convFun φ P = convFun P φ := funext (PDE.MFThermalExist.convFun_comm φ P)
      rw [PDE.MFThermalExist.convFun_comm P (convFun φ P) x, hc]
    have e2 := PDE.MFThermalExist.convFun_assoc hφc hPc hPc
    have e3 : convFun P P = hk (2 * ε) := by
      funext x
      have := hk_semigroup hε hε x
      rw [two_mul]
      exact this
    show convFun P (convFun φ P) (y - z) = _
    rw [e1, e2, e3]
  rw [step3]
  simp only [convFun]
  rw [← integral_sub_left_eq_self (fun u : Torus d => φ u * hk (2 * ε) (y - z - u)) volume (y - z)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  simp only [sub_sub_cancel]


theorem conv_Ehat {l : ℝ} (hl : 0 ≤ l) {ε : ℝ} (hε : 0 < ε) (w : Torus d) :
    (∫ u, sliceG d l u * hk (2 * ε) (w - u)) + 1 / l = Ehat l ε w := by
  rw [conv_sliceG_hk hl (by positivity : 0 < 2 * ε) w]
  unfold Ehat
  congr 2; ring

theorem kmol_bound (hd : 1 ≤ d) {l : ℝ} (hl : 0 ≤ l) :
    ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ ∀ (L : ℝ) (v : Torus d → Euc d), 0 ≤ L → IsLipschitzVF L v →
      ∀ ε : ℝ, 0 < ε → ∀ y z : Torus d, |kmol l v ε y z| ≤ L * (A * Ehat l ε (y - z) + B) := by
  obtain ⟨A, B, hA, hB, hmaj⟩ := kk_majorant hd hl (d := d)
  refine ⟨A, B, hA, hB, fun L v hL hv ε hε y z => ?_⟩
  have hvc : Continuous v := lipschitzVF_continuous hL hv
  have hkm := measurable_kk (l := l) hvc
  obtain ⟨M, hM⟩ := hk_bdd hε
  have hM0 : 0 ≤ M := (hk_nonneg hε 0).trans (hM 0)
  have hPc := continuous_hk (d := d) hε
  have hPm1 : Measurable fun q : Torus d × Torus d => hk ε (q.1 - y) :=
    hPc.measurable.comp (measurable_fst.sub measurable_const)
  have hPm2 : Measurable fun q : Torus d × Torus d => hk ε (q.2 - z) :=
    hPc.measurable.comp (measurable_snd.sub measurable_const)
  have hkk := integrable_kk hd hl hL hv
  -- integrability of the weights
  have hw : ∀ φ : Torus d → ℝ, Measurable φ → Integrable φ →
      Integrable (fun q : Torus d × Torus d => φ (q.1 - q.2) * hk ε (q.1 - y) * hk ε (q.2 - z))
        ((volume : Measure (Torus d)).prod (volume : Measure (Torus d))) := by
    intro φ hφm hφ
    have hmeas : Measurable fun q : Torus d × Torus d => φ (q.1 - q.2) * hk ε (q.1 - y) * hk ε (q.2 - z) :=
      ((hφm.comp (measurable_fst.sub measurable_snd)).mul hPm1).mul hPm2
    refine Integrable.mono' (g := fun q : Torus d × Torus d => M * M * |φ (q.1 - q.2)|)
      ((integrable_sub_prod hφm.abs hφ.abs).const_mul (M * M)) hmeas.aestronglyMeasurable
      (Filter.Eventually.of_forall fun q => ?_)
    simp only [Real.norm_eq_abs, abs_mul]
    have h1 : |hk ε (q.1 - y)| ≤ M := by rw [abs_of_nonneg (hk_nonneg hε _)]; exact hM _
    have h2 : |hk ε (q.2 - z)| ≤ M := by rw [abs_of_nonneg (hk_nonneg hε _)]; exact hM _
    calc |φ (q.1 - q.2)| * |hk ε (q.1 - y)| * |hk ε (q.2 - z)| ≤ |φ (q.1 - q.2)| * M * M := by gcongr
      _ = _ := by ring
  have hG1 := integrable_sliceG (d := d) hl
  have hGm := EnergyAux.measurable_sliceG (d := d) l
  have hw1 := hw (sliceG d l) hGm hG1
  have hw0 := hw (fun _ => (1 : ℝ)) measurable_const (integrable_const _)
  have hint : Integrable (fun q : Torus d × Torus d => kk l v q.1 q.2 * hk ε (q.1 - y) * hk ε (q.2 - z))
      ((volume : Measure (Torus d)).prod (volume : Measure (Torus d))) := by
    refine Integrable.mono' (g := fun q : Torus d × Torus d => M * M * |kk l v q.1 q.2|)
      (hkk.abs.const_mul (M * M)) ((hkm.comp measurable_id).mul hPm1 |>.mul hPm2).aestronglyMeasurable
      (Filter.Eventually.of_forall fun q => ?_)
    simp only [Real.norm_eq_abs, abs_mul]
    have h1 : |hk ε (q.1 - y)| ≤ M := by rw [abs_of_nonneg (hk_nonneg hε _)]; exact hM _
    have h2 : |hk ε (q.2 - z)| ≤ M := by rw [abs_of_nonneg (hk_nonneg hε _)]; exact hM _
    calc |kk l v q.1 q.2| * |hk ε (q.1 - y)| * |hk ε (q.2 - z)| ≤ |kk l v q.1 q.2| * M * M := by gcongr
      _ = _ := by ring
  unfold kmol
  rw [← Real.norm_eq_abs]
  refine (norm_integral_le_integral_norm _).trans ?_
  have hJ1 := J_eq hGm hG1 hε y z
  have hone : ∫ u : Torus d, hk (2 * ε) (y - z - u) = 1 := by
    rw [integral_sub_left_eq_self (fun u => hk (2 * ε) u) volume (y - z), integral_hk (by positivity)]
  have hJ0 : ∫ q : Torus d × Torus d, 1 * hk ε (q.1 - y) * hk ε (q.2 - z)
      ∂((volume : Measure (Torus d)).prod volume) = 1 :=
    (J_eq (φ := fun _ => (1 : ℝ)) measurable_const (integrable_const 1) hε y z).trans
      (by simp only [one_mul]; exact hone)
  have hmajint : Integrable (fun q : Torus d × Torus d => L * (A * (sliceG d l (q.1 - q.2) * hk ε (q.1 - y) * hk ε (q.2 - z)) +
      B * (1 * hk ε (q.1 - y) * hk ε (q.2 - z)))) ((volume : Measure (Torus d)).prod (volume : Measure (Torus d))) :=
    (((hw1.const_mul A).add (hw0.const_mul B))).const_mul L
  calc ∫ q : Torus d × Torus d, ‖kk l v q.1 q.2 * hk ε (q.1 - y) * hk ε (q.2 - z)‖
        ∂((volume : Measure (Torus d)).prod volume)
      ≤ ∫ q : Torus d × Torus d, L * (A * (sliceG d l (q.1 - q.2) * hk ε (q.1 - y) * hk ε (q.2 - z)) +
          B * (1 * hk ε (q.1 - y) * hk ε (q.2 - z))) ∂((volume : Measure (Torus d)).prod volume) := by
        refine integral_mono hint.norm hmajint fun q => ?_
        simp only [Real.norm_eq_abs, abs_mul]
        have h1 : |hk ε (q.1 - y)| = hk ε (q.1 - y) := abs_of_nonneg (hk_nonneg hε _)
        have h2 : |hk ε (q.2 - z)| = hk ε (q.2 - z) := abs_of_nonneg (hk_nonneg hε _)
        rw [h1, h2]
        have h3 := hmaj L v hL hv q.1 q.2
        have hp : 0 ≤ hk ε (q.1 - y) * hk ε (q.2 - z) := mul_nonneg (hk_nonneg hε _) (hk_nonneg hε _)
        calc |kk l v q.1 q.2| * hk ε (q.1 - y) * hk ε (q.2 - z)
            = |kk l v q.1 q.2| * (hk ε (q.1 - y) * hk ε (q.2 - z)) := by ring
          _ ≤ (L * (A * sliceG d l (q.1 - q.2) + B)) * (hk ε (q.1 - y) * hk ε (q.2 - z)) :=
              mul_le_mul_of_nonneg_right h3 hp
          _ = _ := by ring
    _ = L * (A * (∫ u, sliceG d l u * hk (2 * ε) (y - z - u)) + B * 1) := by
        rw [integral_const_mul, integral_add (hw1.const_mul A) (hw0.const_mul B), integral_const_mul,
          integral_const_mul, hJ1, hJ0]
    _ ≤ L * (A * Ehat l ε (y - z) + B) := by
        have h := conv_Ehat hl hε (y - z)
        have hl' : 0 ≤ 1 / l := by positivity
        refine mul_le_mul_of_nonneg_left ?_ hL
        have : (∫ u, sliceG d l u * hk (2 * ε) (y - z - u)) = Ehat l ε (y - z) - 1 / l := by linarith
        rw [this, mul_one]
        nlinarith [mul_nonneg hA hl']


theorem dist_le_tdist (x y : Torus d) : dist x y ≤ KernelGrad.tdist x y := by
  rw [dist_eq_norm, (pi_norm_le_iff_of_nonneg (KernelGrad.tdist_nonneg x y))]
  intro i
  rw [CoercAux.tdist_eq_sqrt]
  refine Real.le_sqrt_of_sq_le ?_
  exact Finset.single_le_sum (f := fun j => ‖(x - y) j‖ ^ 2) (fun j _ => sq_nonneg _) (Finset.mem_univ i)

theorem kmol_tendsto_of_cont (hd : 1 ≤ d) {l : ℝ} (hl : 0 ≤ l) {L : ℝ} (hL : 0 ≤ L) {v : Torus d → Euc d}
    (hv : IsLipschitzVF L v) {y z : Torus d}
    (hcont : ContinuousAt (fun p : Torus d × Torus d => kk l v p.1 p.2) (y, z)) :
    Tendsto (fun ε : ℝ => kmol l v ε y z) (𝓝[>] (0 : ℝ)) (𝓝 (kk l v y z)) := by
  have hvc : Continuous v := lipschitzVF_continuous hL hv
  have hkk := integrable_kk hd hl hL hv
  set n : ℕ := 2 * d + 1 with hn
  have hsup := hk_sup d
  have key := approx_identity (X := Torus d × Torus d) ((volume : Measure (Torus d)).prod volume) hkk
    (x₀ := (y, z)) hcont (𝓝[>] (0 : ℝ))
    (fun q => max (KernelGrad.tdist q.1 y) (KernelGrad.tdist q.2 z))
    (fun q => by
      rw [Prod.dist_eq]
      exact max_le_max (dist_le_tdist _ _) (dist_le_tdist _ _))
    (fun ε q => hk ε (q.1 - y) * hk ε (q.2 - z)) ?_ ?_ ?_ ?_ ?_
  · refine key.congr' (Filter.Eventually.of_forall fun ε => ?_)
    unfold kmol
    exact integral_congr_ae (Filter.Eventually.of_forall fun q => by ring)
  · filter_upwards [self_mem_nhdsWithin] with ε hε q
    exact mul_nonneg (hk_nonneg hε _) (hk_nonneg hε _)
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    exact ((continuous_hk hε).measurable.comp (measurable_fst.sub measurable_const)).mul
      ((continuous_hk hε).measurable.comp (measurable_snd.sub measurable_const))
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    have hε' : 0 < ε := hε
    have := integral_prod_mul (μ := (volume : Measure (Torus d))) (ν := (volume : Measure (Torus d)))
      (fun x => hk ε (x - y)) (fun u => hk ε (u - z))
    rw [this, integral_sub_right_eq_self (fun x => hk ε x) y, integral_sub_right_eq_self (fun x => hk ε x) z,
      integral_hk hε', one_mul]
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    have hε' : 0 < ε := hε
    obtain ⟨M, hM⟩ := hk_bdd hε'
    exact ⟨M * M, fun q => mul_le_mul (hM _) (hM _) (hk_nonneg hε' _) ((hk_nonneg hε' 0).trans (hM 0))⟩
  · intro r hr
    obtain ⟨C1, hC10, hC1⟩ := hk_tail d n hr
    obtain ⟨C2, hC20, hC2⟩ := hsup
    refine ⟨fun ε => C1 * C2 * ε ^ (1 / 2 : ℝ), ?_, ?_⟩
    · have := (tendsto_rpow_nhdsGT_zero (p := 1 / 2) (by norm_num)).const_mul (C1 * C2)
      simpa using this
    · have hδ : (0 : ℝ) < 1 / (2 ^ n * (4 * Real.pi ^ 2) + 4 * Real.pi ^ 2) := by positivity
      filter_upwards [Ioo_mem_nhdsGT hδ] with ε hε q hq
      have hε0 : 0 < ε := hε.1
      have hεl : ε < 1 / (2 ^ n * (4 * Real.pi ^ 2) + 4 * Real.pi ^ 2) := hε.2
      have hsmall : 2 ^ n * (4 * Real.pi ^ 2 * ε) ≤ 1 := by
        rw [lt_div_iff₀ (by positivity)] at hεl
        nlinarith [Real.pi_pos]
      have hsmall' : 4 * Real.pi ^ 2 * ε ≤ 1 := by
        have : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
        nlinarith [mul_pos (by positivity : (0 : ℝ) < 4 * Real.pi ^ 2) hε0]
      have hrpow : ε ^ (((n : ℝ) - d) / 2) * ε ^ (-((d : ℝ) / 2)) = ε ^ (1 / 2 : ℝ) := by
        rw [← Real.rpow_add hε0]
        congr 1
        rw [hn]; push_cast; ring
      have hp1 : 0 ≤ ε ^ (((n : ℝ) - d) / 2) := Real.rpow_nonneg hε0.le _
      have hp2 : 0 ≤ ε ^ (-((d : ℝ) / 2)) := Real.rpow_nonneg hε0.le _
      rcases le_max_iff.mp hq with h | h
      · have h1 := hC1 ε hε0 hsmall (q.1 - y) (by rwa [← EnergyAux.tdist_def] )
        have h2 := hC2 ε hε0 hsmall' (q.2 - z)
        calc hk ε (q.1 - y) * hk ε (q.2 - z) ≤ (C1 * ε ^ (((n : ℝ) - d) / 2)) * (C2 * ε ^ (-((d : ℝ) / 2))) :=
              mul_le_mul h1 h2 (hk_nonneg hε0 _) (by positivity)
          _ = C1 * C2 * (ε ^ (((n : ℝ) - d) / 2) * ε ^ (-((d : ℝ) / 2))) := by ring
          _ = _ := by rw [hrpow]
      · have h1 := hC1 ε hε0 hsmall (q.2 - z) (by rwa [← EnergyAux.tdist_def] )
        have h2 := hC2 ε hε0 hsmall' (q.1 - y)
        calc hk ε (q.1 - y) * hk ε (q.2 - z) ≤ (C2 * ε ^ (-((d : ℝ) / 2))) * (C1 * ε ^ (((n : ℝ) - d) / 2)) :=
              mul_le_mul h2 h1 (hk_nonneg hε0 _) (by positivity)
          _ = C1 * C2 * (ε ^ (((n : ℝ) - d) / 2) * ε ^ (-((d : ℝ) / 2))) := by ring
          _ = _ := by rw [hrpow]


theorem kmol_tendsto (hd : 1 ≤ d) {l : ℝ} (hl : 0 ≤ l) {L : ℝ} (hL : 0 ≤ L) {v : Torus d → Euc d}
    (hv : IsLipschitzVF L v) {y z : Torus d} (hyz : y ≠ z) :
    Tendsto (fun ε : ℝ => kmol l v ε y z) (𝓝[>] (0 : ℝ)) (𝓝 (kk l v y z)) :=
  kmol_tendsto_of_cont hd hl hL hv (kk_continuousAt hl (lipschitzVF_continuous hL hv) hyz)

theorem measurable_kmol {l : ℝ} {v : Torus d → Euc d} (hvc : Continuous v) {ε : ℝ} (hε : 0 < ε) :
    Measurable fun p : Torus d × Torus d => kmol l v ε p.1 p.2 := by
  have hkm := measurable_kk (l := l) hvc
  have hP := (continuous_hk (d := d) hε).measurable
  have hm : Measurable fun z : (Torus d × Torus d) × (Torus d × Torus d) =>
      kk l v z.1.1 z.1.2 * hk ε (z.1.1 - z.2.1) * hk ε (z.1.2 - z.2.2) :=
    ((hkm.comp measurable_fst).mul (hP.comp (measurable_fst.fst.sub measurable_snd.fst))).mul
      (hP.comp (measurable_fst.snd.sub measurable_snd.snd))
  exact (hm.stronglyMeasurable.integral_prod_left' (μ := (volume : Measure (Torus d)).prod volume)).measurable

theorem measurable_Ehat {l : ℝ} (hl : 0 ≤ l) {ε : ℝ} (hε : 0 < ε) : Measurable (Ehat (d := d) l ε) := by
  unfold Ehat
  exact (measurable_const.mul
    (continuous_ser (cW_gauss (d := d) hl (by positivity : 0 < 2 * ε)).summable).measurable)

/-- The limit `ε → 0` of the level-`ε` inequality. -/
theorem main_limit (hd : 1 ≤ d) {l : ℝ} (hl : 0 ≤ l) (m : Measure (Torus d)) [IsFiniteMeasure m]
    {s : Torus d → ℝ} (hsm : Measurable s) (hs : ∀ y, |s y| ≤ 1) (hneut : l = 0 → ∫ y, s y ∂m = 0)
    {L : ℝ} (hL : 0 ≤ L) {v : Torus d → Euc d} (hv : IsLipschitzVF L v)
    (hint : Integrable (fun p : Torus d × Torus d => sliceGfull d l (p.1 - p.2)) (m.prod m))
    (hgood : ∀ᵐ p ∂(m.prod m), IntW l (p.1 - p.2) ∧
      Tendsto (fun ε : ℝ => kmol l v ε p.1 p.2) (𝓝[>] (0 : ℝ)) (𝓝 (kk l v p.1 p.2))) :
    |∫ p : Torus d × Torus d, s p.1 * s p.2 * kk l v p.1 p.2 ∂(m.prod m)| ≤
      2 * ((2 * d + 1) * L) * ∫ p : Torus d × Torus d, s p.1 * s p.2 * sliceGfull d l (p.1 - p.2) ∂(m.prod m) := by
  have hvc : Continuous v := lipschitzVF_continuous hL hv
  obtain ⟨A, B, hA, hB, hkmol⟩ := kmol_bound hd hl (d := d)
  obtain ⟨Kc, hKc, hlow⟩ := Ehat_lower d
  set Gf : Torus d × Torus d → ℝ := fun p => sliceGfull d l (p.1 - p.2) with hGf
  have hGfm : Measurable Gf := (EnergyAux.measurable_sliceGfull l).comp (measurable_fst.sub measurable_snd)
  have hint' : Integrable Gf (m.prod m) := hint
  have hss : ∀ p : Torus d × Torus d, |s p.1 * s p.2| ≤ 1 := fun p => by
    rw [abs_mul]; exact mul_le_one₀ (hs _) (abs_nonneg _) (hs _)
  have hssm : Measurable fun p : Torus d × Torus d => s p.1 * s p.2 :=
    (hsm.comp measurable_fst).mul (hsm.comp measurable_snd)
  -- the two limits
  have hKlim : Tendsto (fun ε : ℝ => ∫ p : Torus d × Torus d, s p.1 * s p.2 * kmol l v ε p.1 p.2 ∂(m.prod m))
      (𝓝[>] (0 : ℝ)) (𝓝 (∫ p : Torus d × Torus d, s p.1 * s p.2 * kk l v p.1 p.2 ∂(m.prod m))) := by
    refine tendsto_integral_filter_of_dominated_convergence
      (fun p => L * (A * (Real.exp (2 * l) * |Gf p| + 2) + B)) ?_ ?_ ?_ ?_
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      exact (hssm.mul (measurable_kmol hvc hε)).aestronglyMeasurable
    · filter_upwards [Ioo_mem_nhdsGT (zero_lt_one : (0 : ℝ) < 1)] with ε hε
      filter_upwards [hgood] with p hp
      have hε0 : 0 < ε := hε.1
      rw [Real.norm_eq_abs, abs_mul]
      have h1 := hkmol L v hL hv ε hε0 p.1 p.2
      have h2 := Ehat_upper hl hp.1 hε0
      have h3 : Real.exp (2 * l * ε) * sliceGfull d l (p.1 - p.2) ≤ Real.exp (2 * l) * |Gf p| := by
        calc Real.exp (2 * l * ε) * sliceGfull d l (p.1 - p.2) ≤ Real.exp (2 * l * ε) * |Gf p| :=
              mul_le_mul_of_nonneg_left (le_abs_self _) (Real.exp_pos _).le
          _ ≤ Real.exp (2 * l) * |Gf p| :=
              mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by nlinarith [mul_nonneg hl (sub_nonneg.mpr hε.2.le)]))
                (abs_nonneg _)
      calc |s p.1 * s p.2| * |kmol l v ε p.1 p.2| ≤ 1 * (L * (A * Ehat l ε (p.1 - p.2) + B)) :=
            mul_le_mul (hss p) h1 (abs_nonneg _) zero_le_one
        _ ≤ L * (A * (Real.exp (2 * l) * |Gf p| + 2) + B) := by
            rw [one_mul]
            refine mul_le_mul_of_nonneg_left ?_ hL
            have : Ehat l ε (p.1 - p.2) ≤ Real.exp (2 * l) * |Gf p| + 2 := by
              have : 2 * ε ≤ 2 := by linarith [hε.2]
              linarith
            nlinarith [mul_le_mul_of_nonneg_left this hA]
    · exact ((((hint'.abs.const_mul _).add (integrable_const (2 : ℝ))).const_mul A).add (integrable_const B)).const_mul L
    · filter_upwards [hgood] with p hp
      exact (hp.2.const_mul (s p.1 * s p.2))
  have hElim : Tendsto (fun ε : ℝ => ∫ p : Torus d × Torus d, s p.1 * s p.2 * Ehat l ε (p.1 - p.2) ∂(m.prod m))
      (𝓝[>] (0 : ℝ)) (𝓝 (∫ p : Torus d × Torus d, s p.1 * s p.2 * Gf p ∂(m.prod m))) := by
    refine tendsto_integral_filter_of_dominated_convergence
      (fun p => Real.exp (2 * l) * |Gf p| + 2 + Kc) ?_ ?_ ?_ ?_
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      exact (hssm.mul ((measurable_Ehat hl hε).comp (measurable_fst.sub measurable_snd))).aestronglyMeasurable
    · filter_upwards [Ioo_mem_nhdsGT (zero_lt_one : (0 : ℝ) < 1)] with ε hε
      filter_upwards [hgood] with p hp
      have hε0 : 0 < ε := hε.1
      rw [Real.norm_eq_abs, abs_mul]
      have h2 := Ehat_upper hl hp.1 hε0
      have h4 := hlow l hl (p.1 - p.2) hp.1 ε hε0
      have h3 : Real.exp (2 * l * ε) * sliceGfull d l (p.1 - p.2) ≤ Real.exp (2 * l) * |Gf p| := by
        calc Real.exp (2 * l * ε) * sliceGfull d l (p.1 - p.2) ≤ Real.exp (2 * l * ε) * |Gf p| :=
              mul_le_mul_of_nonneg_left (le_abs_self _) (Real.exp_pos _).le
          _ ≤ Real.exp (2 * l) * |Gf p| :=
              mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by nlinarith [mul_nonneg hl (sub_nonneg.mpr hε.2.le)]))
                (abs_nonneg _)
      have hE : |Ehat l ε (p.1 - p.2)| ≤ Real.exp (2 * l) * |Gf p| + 2 + Kc := by
        rw [abs_le]
        constructor
        · have : 0 ≤ Real.exp (2 * l) * |Gf p| := by positivity
          linarith
        · have : 2 * ε ≤ 2 := by linarith [hε.2]
          linarith
      calc |s p.1 * s p.2| * |Ehat l ε (p.1 - p.2)| ≤ 1 * (Real.exp (2 * l) * |Gf p| + 2 + Kc) :=
            mul_le_mul (hss p) hE (abs_nonneg _) zero_le_one
        _ = _ := one_mul _
    · exact ((hint'.abs.const_mul _).add (integrable_const (2 : ℝ))).add (integrable_const Kc)
    · filter_upwards [hgood] with p hp
      exact (Ehat_tendsto hl hp.1).const_mul (s p.1 * s p.2)
  have hle : ∀ᶠ ε in 𝓝[>] (0 : ℝ), |∫ p : Torus d × Torus d, s p.1 * s p.2 * kmol l v ε p.1 p.2 ∂(m.prod m)| ≤
      2 * ((2 * d + 1) * L) * ∫ p : Torus d × Torus d, s p.1 * s p.2 * Ehat l ε (p.1 - p.2) ∂(m.prod m) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact level_ineq hd hl hε m hsm hs hneut hL hv
  exact le_of_tendsto_of_tendsto hKlim.abs (hElim.const_mul _) hle

end HRS.Commutator.RoughMain
