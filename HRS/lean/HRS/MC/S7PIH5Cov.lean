import HRS.MC.S7PIH4Key

/-!
# Packet piH, part 5: the covariance increments `S s - S s' = ∫_{(s,s']} A`
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators MatrixOrder

noncomputable section

namespace HRS.MC.Sec7.S7PIH

variable {q : ℕ} {a b : ℝ} {A S : ℝ → Matrix (Fin q) (Fin q) ℝ}

theorem S7PIH_cov_sub (hA : ∀ i j, ContinuousOn (fun v => A v i j) (Set.Icc a b))
    (hS : ∀ u ∈ Set.Icc a b, ∀ i j, S u i j = S b i j + ∫ v in Set.Ioc u b, A v i j)
    {s s' : ℝ} (hs : s ∈ Set.Icc a b) (hs' : s' ∈ Set.Icc a b) (hss : s ≤ s') (i j : Fin q) :
    S s i j - S s' i j = ∫ v in Set.Ioc s s', A v i j := by
  have hint : ∀ x y, x ∈ Set.Icc a b → y ∈ Set.Icc a b →
      IntervalIntegrable (fun v => A v i j) volume x y :=
    fun x y hx hy => ((hA i j).mono (Set.uIcc_subset_Icc hx hy)).intervalIntegrable
  have hbm : b ∈ Set.Icc a b := ⟨hs'.1.trans hs'.2, le_rfl⟩
  rw [hS s hs, hS s' hs', ← intervalIntegral.integral_of_le hs.2, ← intervalIntegral.integral_of_le hs'.2,
    ← intervalIntegral.integral_of_le hss,
    ← intervalIntegral.integral_add_adjacent_intervals (hint s s' hs hs') (hint s' b hs' hbm)]
  ring

theorem S7PIH_cov_psd (hA : ∀ i j, ContinuousOn (fun v => A v i j) (Set.Icc a b))
    (hApsd : ∀ v ∈ Set.Icc a b, (A v).PosSemidef)
    (hS : ∀ u ∈ Set.Icc a b, ∀ i j, S u i j = S b i j + ∫ v in Set.Ioc u b, A v i j)
    {s s' : ℝ} (hs : s ∈ Set.Icc a b) (hs' : s' ∈ Set.Icc a b) (hss : s ≤ s') :
    (S s - S s').PosSemidef := by
  have hE : S s - S s' = Matrix.of fun i j => ∫ v in Set.Ioc s s', A v i j := by
    ext i j
    simp [S7PIH_cov_sub hA hS hs hs' hss]
  have hsub : Set.Ioc s s' ⊆ Set.Icc a b := fun v hv => ⟨hs.1.trans hv.1.le, hv.2.trans hs'.2⟩
  rw [hE, Matrix.posSemidef_iff_dotProduct_mulVec]
  constructor
  · refine Matrix.IsHermitian.ext fun i j => ?_
    simp only [Matrix.of_apply, star_trivial]
    refine setIntegral_congr_fun measurableSet_Ioc fun v hv => ?_
    have := (hApsd v (hsub hv)).isHermitian
    exact (Matrix.IsHermitian.apply this i j)
  · intro x
    have hI : ∀ i j, IntegrableOn (fun v => x i * (A v i j * x j)) (Set.Ioc s s') := fun i j =>
      (((hA i j).integrableOn_Icc.mono_set hsub).mul_const (x j)).const_mul (x i)
    have hq : star x ⬝ᵥ (Matrix.of fun i j => ∫ v in Set.Ioc s s', A v i j).mulVec x =
        ∫ v in Set.Ioc s s', ∑ i, ∑ j, x i * (A v i j * x j) := by
      rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hI i j]
      simp only [dotProduct, Matrix.mulVec, Matrix.of_apply, star_trivial, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [integral_finsetSum _ fun j _ => hI i j]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [integral_const_mul, integral_mul_const]
    rw [hq]
    refine setIntegral_nonneg measurableSet_Ioc fun v hv => ?_
    have := ((Matrix.posSemidef_iff_dotProduct_mulVec.1 (hApsd v (hsub hv)))).2 x
    simpa [dotProduct, Matrix.mulVec, Finset.mul_sum, star_trivial] using this

theorem S7PIH_S_psd (hA : ∀ i j, ContinuousOn (fun v => A v i j) (Set.Icc a b))
    (hApsd : ∀ v ∈ Set.Icc a b, (A v).PosSemidef) (hSb : (S b).PosSemidef)
    (hS : ∀ u ∈ Set.Icc a b, ∀ i j, S u i j = S b i j + ∫ v in Set.Ioc u b, A v i j)
    {s : ℝ} (hs : s ∈ Set.Icc a b) : (S s).PosSemidef := by
  have hbm : b ∈ Set.Icc a b := ⟨hs.1.trans hs.2, le_rfl⟩
  have := (S7PIH_cov_psd hA hApsd hS hs hbm hs.2).add hSb
  simpa using this

theorem S7PIH_A_bound (hA : ∀ i j, ContinuousOn (fun v => A v i j) (Set.Icc a b)) :
    ∃ K : ℝ, 0 < K ∧ ∀ v ∈ Set.Icc a b, ∀ i j, |A v i j| ≤ K := by
  have h : ∀ i j : Fin q, ∃ C : ℝ, ∀ v ∈ Set.Icc a b, ‖A v i j‖ ≤ C := fun i j =>
    isCompact_Icc.exists_bound_of_continuousOn (hA i j)
  choose C hC using h
  refine ⟨∑ i, ∑ j, max (C i j) 0 + 1, ?_, fun v hv i j => ?_⟩
  · have : 0 ≤ ∑ i : Fin q, ∑ j : Fin q, max (C i j) 0 :=
      Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => le_max_right _ _
    linarith
  · have h1 : max (C i j) 0 ≤ ∑ j' : Fin q, max (C i j') 0 :=
      Finset.single_le_sum (f := fun j' => max (C i j') 0) (fun j' _ => le_max_right _ _)
        (Finset.mem_univ j)
    have h2 : ∑ j' : Fin q, max (C i j') 0 ≤ ∑ i' : Fin q, ∑ j' : Fin q, max (C i' j') 0 :=
      Finset.single_le_sum (f := fun i' => ∑ j' : Fin q, max (C i' j') 0)
        (fun i' _ => Finset.sum_nonneg fun j' _ => le_max_right _ _) (Finset.mem_univ i)
    have h3 := hC i j v hv
    rw [Real.norm_eq_abs] at h3
    linarith [le_max_left (C i j) 0]

theorem S7PIH_cov_entry_bound (hA : ∀ i j, ContinuousOn (fun v => A v i j) (Set.Icc a b)) {K : ℝ}
    (hK : ∀ v ∈ Set.Icc a b, ∀ i j, |A v i j| ≤ K)
    (hS : ∀ u ∈ Set.Icc a b, ∀ i j, S u i j = S b i j + ∫ v in Set.Ioc u b, A v i j)
    {s s' : ℝ} (hs : s ∈ Set.Icc a b) (hs' : s' ∈ Set.Icc a b) (hss : s ≤ s') (i j : Fin q) :
    |S s i j - S s' i j| ≤ K * (s' - s) := by
  rw [S7PIH_cov_sub hA hS hs hs' hss]
  have hsub : Set.Ioc s s' ⊆ Set.Icc a b := fun v hv => ⟨hs.1.trans hv.1.le, hv.2.trans hs'.2⟩
  have := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Set.Ioc s s')
    (f := fun v => A v i j) (C := K) (by simp) (fun v hv => by
      rw [Real.norm_eq_abs]; exact hK v (hsub hv) i j)
  rw [Real.norm_eq_abs] at this
  simpa [Real.volume_Ioc, hss, mul_comm] using this

theorem S7PIH_S_cont (hA : ∀ i j, ContinuousOn (fun v => A v i j) (Set.Icc a b)) (hab : a ≤ b)
    (hS : ∀ u ∈ Set.Icc a b, ∀ i j, S u i j = S b i j + ∫ v in Set.Ioc u b, A v i j)
    (i j : Fin q) : ContinuousOn (fun u => S u i j) (Set.Icc a b) := by
  have hint : ∀ x y, x ∈ Set.Icc a b → y ∈ Set.Icc a b →
      IntervalIntegrable (fun v => A v i j) volume x y :=
    fun x y hx hy => ((hA i j).mono (Set.uIcc_subset_Icc hx hy)).intervalIntegrable
  have ha : a ∈ Set.Icc a b := ⟨le_rfl, hab⟩
  have hbm : b ∈ Set.Icc a b := ⟨hab, le_rfl⟩
  have hprim : ContinuousOn (fun x => ∫ t in a..x, A t i j) (Set.Icc a b) := by
    have := intervalIntegral.continuousOn_primitive_interval (a := a) (b := b) (μ := volume)
      (f := fun t => A t i j) (((hA i j).mono (Set.uIcc_subset_Icc ha hbm)).integrableOn_uIcc)
    simpa [Set.uIcc_of_le hab] using this
  have : ContinuousOn (fun u => S b i j + ((∫ t in a..b, A t i j) - ∫ t in a..u, A t i j))
      (Set.Icc a b) := continuousOn_const.add (continuousOn_const.sub hprim)
  refine this.congr fun u hu => ?_
  dsimp only
  rw [hS u hu, ← intervalIntegral.integral_of_le hu.2,
    intervalIntegral.integral_interval_sub_left (hint a b ha hbm) (hint a u ha hu)]

end HRS.MC.Sec7.S7PIH

end
