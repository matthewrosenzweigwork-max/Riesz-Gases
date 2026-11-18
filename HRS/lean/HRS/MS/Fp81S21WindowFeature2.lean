import HRS.MS.Fp81S21WindowFeature
import HRS.MS.OrbIdAux2

/-!
# HRS S2.1(iii), SOL40 packet 15c: shifted reconstruction integrals

The physical time in the observation window is `a + t`; this lemma records
the translation of an interval integral before applying the existing S101 FTC.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Fp81.S21

open HRS (Euc)
open HRS.Whole HRS.MS.CovMeas

theorem fp81s21_window_shift_integral_Icc {a t : ℝ} (ht : 0 ≤ t) (f : ℝ → ℝ) :
    ∫ u in Icc (0 : ℝ) t, f (a + u) = ∫ s in Icc a (a + t), f s := by
  have h := intervalIntegral.integral_comp_add_left (a := 0) (b := t) f a
  simp only [add_zero] at h
  rw [intervalIntegral.integral_of_le ht,
    intervalIntegral.integral_of_le (show a ≤ a + t by linarith)] at h
  rw [← integral_Icc_eq_integral_Ioc, ← integral_Icc_eq_integral_Ioc] at h
  simpa using h

/-- Pairing the window feature with the usual path evaluation test exposes the
initial coordinate and the shifted physical derivative integral.  The
pointwise `Memℓp` premise is only used to identify the coordinate of the
`L²` representative almost everywhere on the observed subinterval. -/
theorem fp81s21_window_feature_pair_y1_formula
    {d : ℕ} {C : WholeCoeff d} {m H a v : ℝ} {x : Euc d}
    (hA : Memℓp (fun β : MultiIndex d => if v ≤ a then
      propagatorW C v a (oscTestFun m β) x else oscTestFun m β x) 2)
    (hLp : MemLp (fun t : ℝ => fp81s21_window_feature_Aprime C m H a v t x) 2
      (volume.restrict (Icc (0 : ℝ) H)))
    (hcoord : ∀ t ∈ Icc (0 : ℝ) H,
      Memℓp (fun β : MultiIndex d => if v < a + t then
        s101Dt C m (a + H) v (a + t) β x else 0) 2)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) H) (α : MultiIndex d) :
    inner ℝ (fp81s21_window_feature C m H a v x)
        (HRS.MS.S52.s52y1 m H t α) =
      (if v ≤ a then propagatorW C v a (oscTestFun m α) x else oscTestFun m α x) +
        ∫ u in Icc (0 : ℝ) t,
          (if v < a + u then s101Dt C m (a + H) v (a + u) α x else 0) := by
  classical
  rw [HRS.MS.S52.s52_inner_y1 ht.2]
  have hfeature : fp81s21_window_feature C m H a v x =
      KSpace.mk (fp81s21_window_feature_A0 C m a v x) (hLp.toLp _) 
        (fp81s21_window_feature_B m a v x) := by
    unfold fp81s21_window_feature
    rw [dif_pos hLp]
  rw [hfeature, HRS.MS.S52.s52_mk_A₀, HRS.MS.S52.s52_mk_A']
  unfold fp81s21_window_feature_A0
  rw [s101_ellVec_coord hA α]
  have hae : ∀ᵐ u ∂(volume.restrict (Icc (0 : ℝ) t)),
      ((hLp.toLp _ : L2Path d m H) u) =
        (fun u : ℝ => fp81s21_window_feature_Aprime C m H a v u x) u :=
    ae_restrict_of_ae_restrict_of_subset (Icc_subset_Icc_right ht.2) hLp.coeFn_toLp
  have hint :
      ∫ u in Icc (0 : ℝ) t,
        OscDual.coord ((hLp.toLp _ : L2Path d m H) u) α =
      ∫ u in Icc (0 : ℝ) t,
        (if v < a + u then s101Dt C m (a + H) v (a + u) α x else 0) := by
    refine integral_congr_ae ?_
    filter_upwards [hae, ae_restrict_mem (measurableSet_Icc (a := (0 : ℝ)) (b := t))]
      with u huLp hu
    rw [huLp]
    by_cases hv : v < a + u
    · simp only [fp81s21_window_feature_Aprime, hv, if_pos]
      have hcoord' : Memℓp
          (fun β : MultiIndex d => s101Dt C m (a + H) v (a + u) β x) 2 := by
        simpa [hv] using hcoord u ⟨hu.1, hu.2.trans ht.2⟩
      exact s101_ellVec_coord hcoord' α
    · rw [fp81s21_window_feature_Aprime]
      rw [if_neg hv]
      rw [s101_ellVec_coord (hcoord u ⟨hu.1, hu.2.trans ht.2⟩) α]
      simp [hv]
  rw [hint]

/-- The shifted window derivative integral is the difference of the two
full-history S101 integrals at physical times `a+t` and `a`. -/
theorem fp81s21_window_shifted_th_integral
    {d : ℕ} {C : WholeCoeff d} {m H a v : ℝ} {r : ℕ}
    {c : MultiIndex d → ℝ} {α : MultiIndex d} {x : Euc d}
    (hD : S101Data C m (a + H) r c) (ha : 0 ≤ a) (hH : 0 ≤ H)
    (hv : v ∈ Icc (0 : ℝ) (a + H)) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) H) :
    ∫ u in Icc (0 : ℝ) t,
      (if v < a + u then s101Dt C m (a + H) v (a + u) α x else 0) =
      (if v < a + t then propagatorW C v (a + t) (oscTestFun m α) x -
        propagatorW C v v (oscTestFun m α) x else 0) -
      (if v < a then propagatorW C v a (oscTestFun m α) x -
        propagatorW C v v (oscTestFun m α) x else 0) := by
  let F : ℝ → ℝ := fun s => s101Th C m (a + H) v s α x
  have haT : a ∈ Icc (0 : ℝ) (a + H) := by constructor <;> linarith
  have hatT : a + t ∈ Icc (0 : ℝ) (a + H) := by
    constructor
    · linarith [ht.1]
    · linarith [ht.2]
  have hpoint : ∀ u ∈ Icc (0 : ℝ) t,
      (if v < a + u then s101Dt C m (a + H) v (a + u) α x else 0) = F (a + u) := by
    intro u hu
    have huT : a + u ≤ a + H := by linarith [hu.2, ht.2]
    by_cases hvu : v < a + u
    · simp [F, s101Th, hvu, huT]
    · simp [F, s101Th, hvu]
  have hshift :
      ∫ u in Icc (0 : ℝ) t,
        (if v < a + u then s101Dt C m (a + H) v (a + u) α x else 0) =
      ∫ s in Icc a (a + t), F s := by
    calc
      ∫ u in Icc (0 : ℝ) t,
          (if v < a + u then s101Dt C m (a + H) v (a + u) α x else 0) =
        ∫ u in Icc (0 : ℝ) t, F (a + u) :=
          setIntegral_congr_fun measurableSet_Icc fun u hu => hpoint u hu
      _ = ∫ s in Icc a (a + t), F s := fp81s21_window_shift_integral_Icc ht.1 F
  have hI1 : IntervalIntegrable F volume 0 a := by
    exact s101_th_intervalIntegrable hD hv α x 0 a
  have hI2 : IntervalIntegrable F volume a (a + t) := by
    exact s101_th_intervalIntegrable hD hv α x a (a + t)
  have hsplit :
      ∫ s in Icc (0 : ℝ) (a + t), F s =
        (∫ s in Icc (0 : ℝ) a, F s) + ∫ s in Icc a (a + t), F s := by
    have hsplit' := intervalIntegral.integral_add_adjacent_intervals hI1 hI2
    rw [intervalIntegral.integral_of_le ha,
      intervalIntegral.integral_of_le (show a ≤ a + t by linarith [ht.1]),
      intervalIntegral.integral_of_le (show 0 ≤ a + t by linarith [ha, ht.1]),
      ← integral_Icc_eq_integral_Ioc, ← integral_Icc_eq_integral_Ioc,
      ← integral_Icc_eq_integral_Ioc] at hsplit'
    exact hsplit'.symm
  have hfull := s101_int_th hD hv (t := a + t) hatT α x
  have hlower := s101_int_th hD hv (t := a) haT α x
  have hfull' : ∫ s in Icc (0 : ℝ) (a + t), F s =
      (if v < a + t then propagatorW C v (a + t) (oscTestFun m α) x -
        propagatorW C v v (oscTestFun m α) x else 0) := by simpa [F] using hfull
  have hlower' : ∫ s in Icc (0 : ℝ) a, F s =
      (if v < a then propagatorW C v a (oscTestFun m α) x -
        propagatorW C v v (oscTestFun m α) x else 0) := by simpa [F] using hlower
  rw [hfull', hlower'] at hsplit
  rw [hshift]
  linarith

/-- Reconstruction against a path evaluation test.  The terminal-value
identity is explicit because `S101Data` alone does not assert existence of a
classical adjoint at the diagonal. -/
theorem fp81s21_window_feature_reconstruct_y1
    {d : ℕ} {C : WholeCoeff d} {m H a v : ℝ} {x : Euc d} {α : MultiIndex d}
    {c : MultiIndex d → ℝ} {r : ℕ}
    (hD : S101Data C m (a + H) r c) (ha : 0 ≤ a) (hH : 0 ≤ H)
    (hv : v ∈ Icc (0 : ℝ) (a + H))
    (hterminal : propagatorW C v v (oscTestFun m α) x = oscTestFun m α x)
    (hA : Memℓp (fun β : MultiIndex d => if v ≤ a then
      propagatorW C v a (oscTestFun m β) x else oscTestFun m β x) 2)
    (hLp : MemLp (fun t : ℝ => fp81s21_window_feature_Aprime C m H a v t x) 2
      (volume.restrict (Icc (0 : ℝ) H)))
    (hcoord : ∀ t ∈ Icc (0 : ℝ) H,
      Memℓp (fun β : MultiIndex d => if v < a + t then
        s101Dt C m (a + H) v (a + t) β x else 0) 2)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) H) :
    inner ℝ (fp81s21_window_feature C m H a v x)
        (HRS.MS.S52.s52y1 m H t α) =
      if v ≤ a + t then propagatorW C v (a + t) (oscTestFun m α) x
      else oscTestFun m α x := by
  rw [fp81s21_window_feature_pair_y1_formula hA hLp hcoord ht α,
    fp81s21_window_shifted_th_integral hD ha hH hv ht]
  by_cases hva : v ≤ a
  · by_cases hva' : v < a
    · have hend : v < a + t := by linarith [ht.1]
      have hend_le : v ≤ a + t := hend.le
      simp only [if_pos hva, if_pos hend, if_pos hva', if_pos hend_le]
      rw [hterminal]
      ring
    · have hv_eq : v = a := le_antisymm hva (le_of_not_gt hva')
      by_cases ht_zero : t = 0
      · subst v
        subst t
        simp
      · have ht_pos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm ht_zero)
        have hend : v < a + t := by rw [hv_eq]; linarith
        have hend_le : v ≤ a + t := hend.le
        simp only [if_pos hva, if_pos hend, if_neg hva', if_pos hend_le]
        rw [hv_eq] at hterminal ⊢
        ring
  · have hva' : a < v := lt_of_not_ge hva
    have hnotstart : ¬ v < a := not_lt_of_ge hva'.le
    by_cases hend : v < a + t
    · have hend_le : v ≤ a + t := hend.le
      simp only [if_neg hva, if_pos hend, if_neg hnotstart, if_pos hend_le]
      rw [hterminal]
      ring
    · by_cases hend_le : v ≤ a + t
      · have hv_eq : v = a + t := le_antisymm hend_le (le_of_not_gt hend)
        have hdiag : propagatorW C v (a + t) (oscTestFun m α) x = oscTestFun m α x := by
          simpa [hv_eq] using hterminal
        simp only [if_neg hva, if_neg hend, if_neg hnotstart, if_pos hend_le]
        rw [hdiag]
        ring
      · simp only [if_neg hva, if_neg hend, if_neg hnotstart, if_neg hend_le]
        ring

/-- The uniform `S101Data` envelope supplies the initial and time-slice
`ℓ²` coordinates of the window feature. -/
theorem fp81s21_window_feature_coordinate_memLp
    {d : ℕ} {C : WholeCoeff d} {m H a v : ℝ}
    {c : MultiIndex d → ℝ} {r : ℕ} {x : Euc d}
    (hD : S101Data C m (a + H) r c) (ha : 0 ≤ a) (hH : 0 ≤ H)
    (hv : v ∈ Icc (0 : ℝ) (a + H))
    (hterminal : ∀ β : MultiIndex d, ∀ y : Euc d,
      propagatorW C v v (oscTestFun m β) y = oscTestFun m β y) :
    Memℓp (fun β : MultiIndex d => if v ≤ a then
      propagatorW C v a (oscTestFun m β) x else oscTestFun m β x) 2 ∧
    ∀ t ∈ Icc (0 : ℝ) H,
      Memℓp (fun β : MultiIndex d => if v < a + t then
        s101Dt C m (a + H) v (a + t) β x else 0) 2 := by
  refine ⟨?_, ?_⟩
  · apply s101_memℓp_of_bound hD.summable
    intro β
    by_cases hva : v ≤ a
    · have haT : a ≤ a + H := by linarith
      have hb := hD.bddU β v hv a ⟨hva, haT⟩ 0 (Nat.zero_le _) x
      have habs : |propagatorW C v a (oscTestFun m β) x| ≤ c β := by
        simpa only [norm_iteratedFDeriv_zero, Real.norm_eq_abs] using hb
      simpa [hva] using habs
    · have hvv := hD.bddU β v hv v ⟨le_rfl, hv.2⟩ 0 (Nat.zero_le _) x
      have hφ : |oscTestFun m β x| ≤ c β := by
        simpa only [norm_iteratedFDeriv_zero, Real.norm_eq_abs, hterminal β x] using hvv
      simpa [hva] using hφ
  · intro t ht
    apply s101_memℓp_of_bound hD.summable
    intro β
    by_cases hvt : v < a + t
    · have htT : a + t ≤ a + H := by linarith [ht.2]
      have hb := hD.bddD β v hv (a + t) ⟨hvt.le, htT⟩ 0 (Nat.zero_le _) x
      have habs : |s101Dt C m (a + H) v (a + t) β x| ≤ c β := by
        simpa only [norm_iteratedFDeriv_zero, Real.norm_eq_abs, s101Dt] using hb
      simpa [hvt] using habs
    · simpa [hvt] using hD.nonneg β

private lemma fp81s21_window_shifted_dt_measurable_repr
    {d : ℕ} {C : WholeCoeff d} {m H a v : ℝ}
    {c : MultiIndex d → ℝ} {r : ℕ} {x : Euc d}
    (hD : S101Data C m (a + H) r c)
    (hv : v ∈ Icc (0 : ℝ) (a + H)) (β : MultiIndex d) :
    ∃ g : ℝ → ℝ, Measurable g ∧ ∀ t ∈ Icc (0 : ℝ) H,
      g (a + t) = if v < a + t then s101Dt C m (a + H) v (a + t) β x else 0 := by
  let f : ℝ → ℝ := fun s => propagatorW C v s (oscTestFun m β) x
  let q : ℝ := s101Dt C m (a + H) v (a + H) β x
  let g : ℝ → ℝ := fun s =>
    if s = a + H then (if v < s then q else 0)
    else if v < s ∧ s < a + H then derivWithin f (Ici s) s else 0
  have hderiv : Measurable (fun s : ℝ => derivWithin f (Ici s) s) :=
    measurable_derivWithin_Ici f
  have hg0 : Measurable (fun s : ℝ =>
      if v < s ∧ s < a + H then derivWithin f (Ici s) s else 0) :=
    Measurable.ite (measurableSet_Ioi.inter measurableSet_Iio) hderiv measurable_const
  have hg1 : Measurable (fun s : ℝ => if v < s then q else 0) :=
    Measurable.ite measurableSet_Ioi measurable_const measurable_const
  have hgm : Measurable g := by
    exact Measurable.ite (measurableSet_singleton (a + H)) hg1 hg0
  refine ⟨g, hgm, ?_⟩
  intro t ht
  have hsT : a + t ≤ a + H := by linarith [ht.2]
  by_cases hsEq : a + t = a + H
  · simp [g, q, hsEq]
  · have hsLt : a + t < a + H := lt_of_le_of_ne hsT hsEq
    by_cases hvs : v < a + t
    · have hsIoo : a + t ∈ Ioo v (a + H) := ⟨hvs, hsLt⟩
      have hdiff := hD.diffT β v hv x (a + t) ⟨hvs.le, hsLt.le⟩
      have heq : s101Dt C m (a + H) v (a + t) β x =
          derivWithin f (Ici (a + t)) (a + t) := by
        exact s101_derivWithin_Icc_eq hsIoo hdiff
      simp only [g, if_neg hsEq, if_pos (And.intro hvs hsLt)]
      rw [if_pos hvs]
      exact heq.symm
    · simp [g, q, hsEq, hvs]

/-- The shifted derivative slice is a genuine `L²([0,H];ℓ²)` vector.  Its
bound is the `S101Data` square-sum envelope and does not depend on `a` or `v`.-/
theorem fp81s21_window_feature_Aprime_memLp
    {d : ℕ} {C : WholeCoeff d} {m H a v : ℝ}
    {c : MultiIndex d → ℝ} {r : ℕ} {x : Euc d}
    (hD : S101Data C m (a + H) r c) (ha : 0 ≤ a) (hH : 0 ≤ H)
    (hv : v ∈ Icc (0 : ℝ) (a + H))
    (hterminal : ∀ β : MultiIndex d, ∀ y : Euc d,
      propagatorW C v v (oscTestFun m β) y = oscTestFun m β y) :
    MemLp (fun t : ℝ => fp81s21_window_feature_Aprime C m H a v t x) 2
      (volume.restrict (Icc (0 : ℝ) H)) := by
  let μ : Measure ℝ := volume.restrict (Icc (0 : ℝ) H)
  let coord : MultiIndex d → ℝ → ℝ := fun β t =>
    if t ∈ Icc (0 : ℝ) H then
      if v < a + t then s101Dt C m (a + H) v (a + t) β x else 0
    else 0
  let F : ℝ → OscDual d m := fun t => ellVec m (fun β => coord β t)
  have hcoordMem : ∀ t, Memℓp (fun β : MultiIndex d => coord β t) 2 := by
    intro t
    by_cases ht : t ∈ Icc (0 : ℝ) H
    · have h := (fp81s21_window_feature_coordinate_memLp (x := x) hD ha hH hv hterminal).2 t ht
      simpa only [coord, Set.mem_Icc, ht.1, ht.2, and_self, if_true] using h
    · have hz : Memℓp (fun _ : MultiIndex d => (0 : ℝ)) 2 := by
        apply s101_memℓp_of_bound hD.summable
        intro β
        simpa using hD.nonneg β
      have ht' : ¬ (0 ≤ t ∧ t ≤ H) := by simpa only [Set.mem_Icc] using ht
      simpa only [coord, Set.mem_Icc, ht', if_false] using hz
  have hcoordAesm : ∀ β : MultiIndex d, AEStronglyMeasurable (coord β) μ := by
    intro β
    obtain ⟨g, hg, hrepr⟩ := fp81s21_window_shifted_dt_measurable_repr hD hv β
    let g' : ℝ → ℝ := fun t => if t ∈ Icc (0 : ℝ) H then g (a + t) else 0
    have hg' : Measurable g' :=
      Measurable.ite measurableSet_Icc (hg.comp (measurable_const_add a)) measurable_const
    have hEq : g' =ᵐ[μ] coord β := by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
      simp only [g', coord, if_pos ht]
      exact hrepr t ht
    exact hg'.aestronglyMeasurable.congr hEq
  have hFmeas : AEStronglyMeasurable F μ := by
    exact s101_aesm_ellVec (m := m) coord hcoordAesm hcoordMem
  have hF_eq : (fun t => fp81s21_window_feature_Aprime C m H a v t x) =ᵐ[μ] F := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    change ellVec m (fun β : MultiIndex d =>
        if v < a + t then s101Dt C m (a + H) v (a + t) β x else 0) =
      ellVec m (fun β => coord β t)
    congr 1
    funext β
    change (if v < a + t then s101Dt C m (a + H) v (a + t) β x else 0) =
      (if t ∈ Icc (0 : ℝ) H then
        if v < a + t then s101Dt C m (a + H) v (a + t) β x else 0 else 0)
    rw [if_pos ht]
  have hmeas : AEStronglyMeasurable
      (fun t => fp81s21_window_feature_Aprime C m H a v t x) μ :=
    hFmeas.congr hF_eq.symm
  let B : ℝ := Real.sqrt (∑' β : MultiIndex d, c β ^ 2)
  have hbound : ∀ t ∈ Icc (0 : ℝ) H,
      ‖fp81s21_window_feature_Aprime C m H a v t x‖ ≤ B := by
    intro t ht
    apply s101_norm_ellVec_le hD.summable
    intro β
    by_cases hvt : v < a + t
    · have htT : a + t ≤ a + H := by linarith [ht.2]
      have hb := hD.bddD β v hv (a + t) ⟨hvt.le, htT⟩ 0 (Nat.zero_le _) x
      have habs : |s101Dt C m (a + H) v (a + t) β x| ≤ c β := by
        simpa only [norm_iteratedFDeriv_zero, Real.norm_eq_abs, s101Dt] using hb
      simpa [fp81s21_window_feature_Aprime, hvt, B] using habs
    · simpa [fp81s21_window_feature_Aprime, hvt, B] using hD.nonneg β
  refine MemLp.of_bound hmeas B ?_
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  exact hbound t ht

/-- Reconstruction using only `S101Data`, the terminal diagonal values, and
the observation-window bounds. -/
theorem fp81s21_window_feature_reconstruct_y1_of_data
    {d : ℕ} {C : WholeCoeff d} {m H a v : ℝ} {x : Euc d} {α : MultiIndex d}
    {c : MultiIndex d → ℝ} {r : ℕ}
    (hD : S101Data C m (a + H) r c) (ha : 0 ≤ a) (hH : 0 ≤ H)
    (hv : v ∈ Icc (0 : ℝ) (a + H))
    (hterminal : ∀ β : MultiIndex d, ∀ y : Euc d,
      propagatorW C v v (oscTestFun m β) y = oscTestFun m β y)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) H) :
    inner ℝ (fp81s21_window_feature C m H a v x)
        (HRS.MS.S52.s52y1 m H t α) =
      if v ≤ a + t then propagatorW C v (a + t) (oscTestFun m α) x
      else oscTestFun m α x := by
  obtain ⟨hA, hcoord⟩ :=
    fp81s21_window_feature_coordinate_memLp (x := x) hD ha hH hv hterminal
  exact fp81s21_window_feature_reconstruct_y1 hD ha hH hv (hterminal α x)
    hA (fp81s21_window_feature_Aprime_memLp hD ha hH hv hterminal) hcoord ht

#print axioms fp81s21_window_feature_pair_y1_formula
#print axioms fp81s21_window_shifted_th_integral
#print axioms fp81s21_window_feature_reconstruct_y1
#print axioms fp81s21_window_feature_coordinate_memLp
#print axioms fp81s21_window_feature_Aprime_memLp
#print axioms fp81s21_window_feature_reconstruct_y1_of_data

#print axioms fp81s21_window_shift_integral_Icc

end HRS.Fp81.S21

end
