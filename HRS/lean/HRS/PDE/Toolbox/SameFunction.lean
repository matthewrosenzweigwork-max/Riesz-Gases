import HRS.PDE.Toolbox.LocalInt

/-!
# Appendix C helper lemmas: same-function symmetrization on the torus (Lemma C.4)

Auxiliary results for `HRS/PDE/Toolbox.lean`.

`SameFn.main` is the full statement of Lemma C.4 (`periodic_same_function`): the symmetrized
pairing `½ ∬ κ(x-y) w(x) w(y) (a(y) - a(x))` is absolutely convergent (Schur test with the
majorant `K₀ [a]_{C^{0,1}} (t + t^{-s})`, `t = tdist x y`), is the limit of the symmetric
truncations (oddness of `κ` + swap of `(x,y)`; dominated convergence), and obeys the bound.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ComplexConjugate

namespace HRS.PDE.SameFn

variable {d : ℕ}

/-- The kernel majorant `ρ₀(z) = t + t^{-s}`, `t = tdist z 0`. -/
def rho0 (s : ℝ) (z : Torus d) : ℝ :=
  Torus.tdist z 0 ^ (-(-1 : ℝ)) + Torus.tdist z 0 ^ (-s)

theorem rho0_nonneg (s : ℝ) (z : Torus d) : 0 ≤ rho0 s z := by
  unfold rho0
  have := LocInt.tdist_nonneg z 0
  positivity

theorem integrable_rho0 {s : ℝ} (hs : s < d) : Integrable (rho0 (d := d) s) :=
  (LocInt.integrable_tdist_rpow (by have : (0:ℝ) ≤ d := Nat.cast_nonneg d; linarith)).add
    (LocInt.integrable_tdist_rpow hs)

/-- the pointwise majorant -/
theorem pointwise_bound {s K₀ H : ℝ} (hK : 0 ≤ K₀) (hH : 0 ≤ H) {κ : Torus d → ℝ}
    (hκ : ∀ z : Torus d, z ≠ 0 → |κ z| ≤ K₀ * (1 + Torus.tdist z 0 ^ (-s - 1)))
    (x y : Torus d) {Δ : ℝ} (hΔ : |Δ| ≤ H * Torus.tdist x y) (h0 : x = y → Δ = 0) :
    |κ (x - y)| * |Δ| ≤ K₀ * H * rho0 s (x - y) := by
  by_cases hxy : x = y
  · rw [h0 hxy]
    simp only [abs_zero, mul_zero]
    exact mul_nonneg (mul_nonneg hK hH) (rho0_nonneg _ _)
  have hz : x - y ≠ 0 := sub_ne_zero.2 hxy
  have ht0 : Torus.tdist (x - y) 0 = Torus.tdist x y := (LocInt.tdist_zero_right x y).symm
  have ht : 0 < Torus.tdist x y :=
    lt_of_le_of_ne (LocInt.tdist_nonneg x y) (fun h => hxy ((LocInt.tdist_eq_zero_iff _ _).1 h.symm))
  have hk := hκ _ hz
  rw [ht0] at hk
  calc |κ (x - y)| * |Δ| ≤ (K₀ * (1 + Torus.tdist x y ^ (-s - 1))) * (H * Torus.tdist x y) :=
        mul_le_mul hk hΔ (abs_nonneg _) (mul_nonneg hK (by positivity))
    _ = K₀ * H * rho0 s (x - y) := by
        unfold rho0
        rw [ht0]
        have : Torus.tdist x y ^ (-s - 1) * Torus.tdist x y = Torus.tdist x y ^ (-s) := by
          rw [← Real.rpow_add_one ht.ne']; congr 1; ring
        simp only [neg_neg, Real.rpow_one]
        calc K₀ * (1 + Torus.tdist x y ^ (-s - 1)) * (H * Torus.tdist x y)
            = K₀ * H * (Torus.tdist x y + Torus.tdist x y ^ (-s - 1) * Torus.tdist x y) := by ring
          _ = _ := by rw [this]

theorem main (hd : 1 ≤ d) (s : ℝ) (hsd : s < d) :
    ∃ C : ℝ, ∀ (κ : Torus d → ℝ) (K₀ : ℝ), (∀ z, κ (-z) = -κ z) → Torus.IsSmoothOffZero κ →
      (∀ z : Torus d, z ≠ 0 → |κ z| ≤ K₀ * (1 + Torus.tdist z 0 ^ (-s - 1))) →
      ∀ (La : ℝ) (a w : Torus d → ℝ), Torus.IsLipschitz La a → MemLp w 2 volume →
      Integrable (fun p : Torus d × Torus d => κ (p.1 - p.2) * w p.1 * w p.2 * (a p.2 - a p.1)) ∧
      (∀ ε : ℝ, 0 < ε →
        Integrable (fun p : Torus d × Torus d =>
          if ε < Torus.tdist p.1 p.2 then κ (p.1 - p.2) * a p.2 * w p.2 * w p.1 else 0)) ∧
      Tendsto (fun ε : ℝ => ∫ p : Torus d × Torus d,
          if ε < Torus.tdist p.1 p.2 then κ (p.1 - p.2) * a p.2 * w p.2 * w p.1 else 0)
        (𝓝[>] 0)
        (𝓝 ((1 / 2) * ∫ p : Torus d × Torus d, κ (p.1 - p.2) * w p.1 * w p.2 * (a p.2 - a p.1))) ∧
      |(1 / 2) * ∫ p : Torus d × Torus d, κ (p.1 - p.2) * w p.1 * w p.2 * (a p.2 - a p.1)| ≤
        C * K₀ * Torus.c01Norm a * ∫ x, w x ^ 2 := by
  refine ⟨∫ z : Torus d, rho0 s z, ?_⟩
  intro κ K₀ hodd hsm hbd La a w ha hw
  set H := Torus.holderSeminorm 1 a with hHdef
  have hH0 : 0 ≤ H := LocInt.holderSeminorm_nonneg a
  have hK₀ : 0 ≤ K₀ := by
    obtain ⟨z, hz⟩ := LocInt.exists_torus_ne_zero (d := d) (by omega)
    have h1 := hbd z hz
    by_contra hneg
    push Not at hneg
    have : K₀ * (1 + Torus.tdist z 0 ^ (-s - 1)) < 0 :=
      mul_neg_of_neg_of_pos hneg (by have := Real.rpow_nonneg (LocInt.tdist_nonneg z 0) (-s - 1); linarith)
    linarith [abs_nonneg (κ z)]
  have hκm : Measurable κ := LocInt.measurable_of_smoothOffZero hsm
  have hacont : Continuous a := LocInt.continuous_of_isLipschitz ha
  have hwm : AEStronglyMeasurable w volume := hw.aestronglyMeasurable
  have hw1 : AEStronglyMeasurable (fun p : Torus d × Torus d => w p.1) (volume : Measure (Torus d × Torus d)) :=
    hwm.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_fst
  have hw2 : AEStronglyMeasurable (fun p : Torus d × Torus d => w p.2) (volume : Measure (Torus d × Torus d)) :=
    hwm.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd
  have hk : AEStronglyMeasurable (fun p : Torus d × Torus d => κ (p.1 - p.2)) (volume : Measure (Torus d × Torus d)) :=
    (hκm.comp (measurable_fst.sub measurable_snd)).aestronglyMeasurable
  have ha1 : AEStronglyMeasurable (fun p : Torus d × Torus d => a p.1) (volume : Measure (Torus d × Torus d)) :=
    (hacont.measurable.comp measurable_fst).aestronglyMeasurable
  have ha2 : AEStronglyMeasurable (fun p : Torus d × Torus d => a p.2) (volume : Measure (Torus d × Torus d)) :=
    (hacont.measurable.comp measurable_snd).aestronglyMeasurable
  set F : Torus d × Torus d → ℝ := fun p => κ (p.1 - p.2) * w p.1 * w p.2 * (a p.2 - a p.1) with hFdef
  have hFm : AEStronglyMeasurable F (volume : Measure (Torus d × Torus d)) :=
    ((hk.mul hw1).mul hw2).mul (ha2.sub ha1)
  -- the majorant
  have hρint : Integrable (fun z : Torus d => K₀ * H * rho0 s z) := (integrable_rho0 hsd).const_mul _
  have hρ0 : ∀ z : Torus d, 0 ≤ K₀ * H * rho0 s z := fun z =>
    mul_nonneg (mul_nonneg hK₀ hH0) (rho0_nonneg _ _)
  have hFbd : ∀ p : Torus d × Torus d, |F p| ≤ (K₀ * H * rho0 s (p.1 - p.2)) * (|w p.1| * |w p.2|) := by
    intro p
    have hb := pointwise_bound (s := s) hK₀ hH0 (κ := κ) hbd p.1 p.2 (Δ := a p.2 - a p.1)
      (by rw [LocInt.tdist_comm]; exact LocInt.abs_sub_le_holder ha p.2 p.1)
      (fun h => by rw [h]; ring)
    have : |F p| = |κ (p.1 - p.2)| * |a p.2 - a p.1| * (|w p.1| * |w p.2|) := by
      simp only [hFdef, abs_mul]; ring
    rw [this]
    exact mul_le_mul_of_nonneg_right hb (by positivity)
  obtain ⟨hFint, hFbound⟩ := LocInt.schur_bound hρint hρ0 hw hFm hFbd
  have hw2int : 0 ≤ ∫ x, w x ^ 2 := integral_nonneg fun x => sq_nonneg _
  -- truncations
  set T : ℝ → Torus d × Torus d → ℝ := fun ε p =>
    if ε < Torus.tdist p.1 p.2 then κ (p.1 - p.2) * a p.2 * w p.2 * w p.1 else 0 with hTdef
  have hTm : ∀ ε : ℝ, AEStronglyMeasurable (T ε) (volume : Measure (Torus d × Torus d)) := by
    intro ε
    have hset : MeasurableSet {p : Torus d × Torus d | ε < Torus.tdist p.1 p.2} :=
      measurableSet_lt measurable_const LocInt.measurable_tdist_pair
    have : T ε = Set.indicator {p : Torus d × Torus d | ε < Torus.tdist p.1 p.2}
        (fun p => κ (p.1 - p.2) * a p.2 * w p.2 * w p.1) := by
      funext p; simp only [hTdef, Set.indicator, Set.mem_ofPred_eq]
    rw [this]
    exact (((hk.mul ha2).mul hw2).mul hw1).indicator hset
  have hTint : ∀ ε : ℝ, 0 < ε → Integrable (T ε) := by
    intro ε hε
    set e : ℝ := -s - 1 with he
    set M : ℝ := ε ^ e + (d : ℝ) ^ e with hM
    have hM0 : 0 ≤ M := by positivity
    have htM : ∀ t : ℝ, ε < t → t ≤ d → t ^ e ≤ M := by
      intro t h1 h2
      have ht0 : 0 < t := lt_trans hε h1
      by_cases he0 : 0 ≤ e
      · have : t ^ e ≤ (d : ℝ) ^ e := Real.rpow_le_rpow ht0.le h2 he0
        have : 0 ≤ ε ^ e := by positivity
        linarith
      · push Not at he0
        have : t ^ e ≤ ε ^ e := Real.rpow_le_rpow_of_nonpos hε h1.le he0.le
        have : 0 ≤ (d : ℝ) ^ e := by positivity
        linarith
    set A := Torus.supNorm a with hA
    have hA0 : 0 ≤ A := supNorm_nonneg a
    have hρc : Integrable (fun _ : Torus d => K₀ * (1 + M) * A) := integrable_const _
    have hc0 : ∀ _ : Torus d, 0 ≤ K₀ * (1 + M) * A := fun _ => by positivity
    refine (LocInt.schur_bound hρc hc0 hw (hTm ε) ?_).1
    intro p
    simp only [hTdef]
    split_ifs with hlt
    · have hne : p.1 - p.2 ≠ 0 := by
        intro h
        have : p.1 = p.2 := sub_eq_zero.1 h
        rw [this, LocInt.tdist_self] at hlt
        linarith
      have ht0 : Torus.tdist (p.1 - p.2) 0 = Torus.tdist p.1 p.2 := (LocInt.tdist_zero_right _ _).symm
      have hk1 := hbd _ hne
      rw [ht0] at hk1
      have hle := LocInt.tdist_le_dim (p.1 - p.2)
      rw [ht0] at hle
      have hpow := htM _ hlt hle
      have hka : |κ (p.1 - p.2)| ≤ K₀ * (1 + M) := by
        refine hk1.trans (mul_le_mul_of_nonneg_left ?_ hK₀)
        linarith
      have haa : |a p.2| ≤ A := LocInt.abs_le_supNorm_of_isLipschitz ha p.2
      calc |κ (p.1 - p.2) * a p.2 * w p.2 * w p.1|
          = |κ (p.1 - p.2)| * |a p.2| * (|w p.1| * |w p.2|) := by
            simp only [abs_mul]; ring
        _ ≤ (K₀ * (1 + M)) * A * (|w p.1| * |w p.2|) :=
            mul_le_mul_of_nonneg_right (mul_le_mul hka haa (abs_nonneg _) (by positivity)) (by positivity)
    · simp only [abs_zero]; positivity
  -- symmetrization of the truncations
  set G : ℝ → Torus d × Torus d → ℝ := fun ε p =>
    if ε < Torus.tdist p.1 p.2 then F p else 0 with hGdef
  have hGint : ∀ ε : ℝ, Integrable (G ε) := by
    intro ε
    refine hFint.norm.mono' ?_ (Eventually.of_forall fun p => ?_)
    · have hset : MeasurableSet {p : Torus d × Torus d | ε < Torus.tdist p.1 p.2} :=
        measurableSet_lt measurable_const LocInt.measurable_tdist_pair
      have : G ε = Set.indicator {p : Torus d × Torus d | ε < Torus.tdist p.1 p.2} F := by
        funext p; simp only [hGdef, Set.indicator, Set.mem_ofPred_eq]
      rw [this]
      exact hFm.indicator hset
    · simp only [hGdef]
      split_ifs
      · exact le_rfl
      · simp
  have hsym : ∀ ε : ℝ, 0 < ε → ∫ p, T ε p = (1 / 2) * ∫ p, G ε p := by
    intro ε hε
    set T' : Torus d × Torus d → ℝ := fun p =>
      if ε < Torus.tdist p.1 p.2 then κ (p.1 - p.2) * a p.1 * w p.2 * w p.1 else 0 with hT'def
    have hswap : ∀ p : Torus d × Torus d, T' p = -(T ε (Prod.swap p)) := by
      intro p
      simp only [hT'def, hTdef, Prod.fst_swap, Prod.snd_swap]
      rw [LocInt.tdist_comm p.2 p.1]
      split_ifs
      · have : κ (p.2 - p.1) = -κ (p.1 - p.2) := by
          rw [← neg_sub, hodd]
        rw [this]; ring
      · simp
    have hT'int : Integrable T' := by
      have := (hTint ε hε).swap
      have h2 := this.neg
      refine h2.congr (Eventually.of_forall fun p => ?_)
      simp [hswap p]
    have hGsplit : ∀ p, G ε p = T ε p - T' p := by
      intro p
      simp only [hGdef, hTdef, hT'def, hFdef]
      split_ifs
      · ring
      · simp
    have h1 : ∫ p, G ε p = (∫ p, T ε p) - ∫ p, T' p := by
      rw [show (fun p => G ε p) = fun p => T ε p - T' p from funext hGsplit]
      exact integral_sub (hTint ε hε) hT'int
    have h2 : ∫ p, T' p = -∫ p, T ε p := by
      rw [show (fun p => T' p) = fun p => -(T ε (Prod.swap p)) from funext hswap, integral_neg]
      congr 1
      exact integral_prod_swap (μ := (volume : Measure (Torus d))) (ν := (volume : Measure (Torus d))) (T ε)
    rw [h1, h2]; ring
  refine ⟨hFint, hTint, ?_, ?_⟩
  · -- the limit
    have hlim : Tendsto (fun ε : ℝ => ∫ p, G ε p) (𝓝[>] 0) (𝓝 (∫ p, F p)) := by
      refine tendsto_integral_filter_of_dominated_convergence (fun p => ‖F p‖) ?_ ?_ hFint.norm ?_
      · exact Eventually.of_forall fun ε => (hGint ε).aestronglyMeasurable
      · refine Eventually.of_forall fun ε => Eventually.of_forall fun p => ?_
        simp only [hGdef]
        split_ifs
        · exact le_rfl
        · simp
      · refine Eventually.of_forall fun p => ?_
        by_cases hpt : Torus.tdist p.1 p.2 = 0
        · have hxy : p.1 = p.2 := (LocInt.tdist_eq_zero_iff _ _).1 hpt
          have hF0 : F p = 0 := by simp [hFdef, hxy]
          have : ∀ ε : ℝ, 0 < ε → G ε p = 0 := by
            intro ε hε
            simp only [hGdef]
            have hn : ¬ ε < Torus.tdist p.1 p.2 := by rw [hpt]; exact not_lt.2 hε.le
            simp [hn]
          rw [hF0]
          refine tendsto_const_nhds.congr' ?_
          filter_upwards [self_mem_nhdsWithin] with ε hε
          exact (this ε hε).symm
        · have hpos : 0 < Torus.tdist p.1 p.2 := lt_of_le_of_ne (LocInt.tdist_nonneg _ _) (Ne.symm hpt)
          refine tendsto_const_nhds.congr' ?_
          filter_upwards [Ioo_mem_nhdsGT hpos] with ε hε
          simp only [hGdef]
          simp [hε.2]
    refine (hlim.const_mul (1 / 2)).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact (hsym ε hε).symm
  · -- the bound
    have hρ : ∫ z : Torus d, K₀ * H * rho0 s z = K₀ * H * ∫ z : Torus d, rho0 s z := integral_const_mul _ _
    rw [hρ] at hFbound
    have hC0 : 0 ≤ ∫ z : Torus d, rho0 s z := integral_nonneg fun z => rho0_nonneg _ _
    have hHc : H ≤ Torus.c01Norm a := LocInt.holderSeminorm_le_c01Norm a
    rw [abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 1 / 2)]
    calc 1 / 2 * |∫ p, F p| ≤ 1 / 2 * (K₀ * H * (∫ z : Torus d, rho0 s z) * ∫ x, w x ^ 2) :=
          mul_le_mul_of_nonneg_left hFbound (by norm_num)
      _ ≤ (∫ z : Torus d, rho0 s z) * K₀ * Torus.c01Norm a * ∫ x, w x ^ 2 := by
          have h1 : K₀ * H * (∫ z : Torus d, rho0 s z) * ∫ x, w x ^ 2 ≤
              (∫ z : Torus d, rho0 s z) * K₀ * Torus.c01Norm a * ∫ x, w x ^ 2 := by
            apply mul_le_mul_of_nonneg_right _ hw2int
            have : K₀ * H ≤ K₀ * Torus.c01Norm a := mul_le_mul_of_nonneg_left hHc hK₀
            nlinarith
          have h2 : 0 ≤ (∫ z : Torus d, rho0 s z) * K₀ * Torus.c01Norm a * ∫ x, w x ^ 2 := by
            have := (hH0.trans hHc)
            positivity
          linarith

end HRS.PDE.SameFn
