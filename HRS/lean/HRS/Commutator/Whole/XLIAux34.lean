import HRS.Commutator.Whole.XLIAux33

/-!
# X-LI part 34: layer-cake (Marcinkiewicz-type) integration
-/

open MeasureTheory Metric Set Filter
open scoped ENNReal NNReal FourierTransform ContDiff Convolution Topology SchwartzMap

noncomputable section

namespace HRS.Commutator.Whole.XLI

open HRS.Commutator.Whole

variable {d : ℕ}

local notation "𝔼" => EuclideanSpace ℝ (Fin d)

lemma inner_J4 {u : ℝ} (hu4 : u < 4) (hu1 : 1 < u) {a : ℝ≥0∞} (ha : a ≠ ⊤) :
    ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (t ^ (u - 5)) *
        (if a ≤ ENNReal.ofReal t then a ^ 4 else 0) =
      ENNReal.ofReal (1 / (4 - u)) * a ^ u := by
  by_cases ha0 : a = 0
  · subst ha0
    simp [ENNReal.zero_rpow_of_pos (by linarith : 0 < u)]
  set α : ℝ := a.toReal with hα
  have hαpos : 0 < α := ENNReal.toReal_pos ha0 ha
  have haα : a = ENNReal.ofReal α := (ENNReal.ofReal_toReal ha).symm
  have h1 : ∀ t : ℝ, ENNReal.ofReal (t ^ (u - 5)) * (if a ≤ ENNReal.ofReal t then a ^ 4 else 0) =
      (Ici α).indicator (fun t => a ^ 4 * ENNReal.ofReal (t ^ (u - 5))) t := by
    intro t
    by_cases ht : 0 < t
    · by_cases h : α ≤ t
      · have h' : a ≤ ENNReal.ofReal t := by
          rw [haα]; exact ENNReal.ofReal_le_ofReal h
        rw [Set.indicator_of_mem (show t ∈ Ici α from h), if_pos h', mul_comm]
      · have h' : ¬ a ≤ ENNReal.ofReal t := by
          rw [haα]; intro hh; exact h ((ENNReal.ofReal_le_ofReal_iff ht.le).1 hh)
        rw [Set.indicator_of_notMem (show t ∉ Ici α from h), if_neg h']
        simp
    · have h : ¬ α ≤ t := by intro hh; linarith
      rw [Set.indicator_of_notMem (show t ∉ Ici α from h)]
      have h' : ¬ a ≤ ENNReal.ofReal t := by
        rw [ENNReal.ofReal_of_nonpos (not_lt.1 ht)]; simpa using ha0
      rw [if_neg h']; simp
  simp_rw [h1]
  rw [setLIntegral_indicator measurableSet_Ici]
  have hIci : Ici α ∩ Ioi (0 : ℝ) = Ici α :=
    Set.inter_eq_left.2 fun t ht => lt_of_lt_of_le hαpos ht
  rw [hIci, setLIntegral_congr Ioi_ae_eq_Ici.symm,
    lintegral_const_mul' _ _ (ENNReal.pow_ne_top ha)]
  have hint : IntegrableOn (fun t : ℝ => t ^ (u - 5)) (Ioi α) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) hαpos
  rw [← ofReal_integral_eq_lintegral_ofReal hint
    ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun t ht =>
      Real.rpow_nonneg (hαpos.le.trans (le_of_lt ht)) _)),
    integral_Ioi_rpow_of_lt (by linarith) hαpos]
  have h4pos : 0 < 4 - u := by linarith
  rw [haα, ← ENNReal.ofReal_pow hαpos.le, ← ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_rpow_of_pos hαpos, ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  have e : α ^ (u - 5 + 1) = α ^ (u - 4) := by congr 1; ring
  have e2 : α ^ u = α ^ 4 * α ^ (u - 4) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hαpos]; congr 1; push_cast; ring
  have h4 : (u - 5 + 1) = u - 4 := by ring
  rw [e, e2, h4]
  have hne : u - 4 ≠ 0 := by linarith
  field_simp
  ring

lemma inner_J1 {u : ℝ} (hu1 : 1 < u) {a : ℝ≥0∞} (ha : a ≠ ⊤) :
    ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (t ^ (u - 2)) *
        (if ENNReal.ofReal t < a then a else 0) =
      ENNReal.ofReal (1 / (u - 1)) * a ^ u := by
  by_cases ha0 : a = 0
  · subst ha0
    simp [ENNReal.zero_rpow_of_pos (by linarith : 0 < u)]
  set α : ℝ := a.toReal with hα
  have hαpos : 0 < α := ENNReal.toReal_pos ha0 ha
  have haα : a = ENNReal.ofReal α := (ENNReal.ofReal_toReal ha).symm
  have h1 : ∀ t : ℝ, ENNReal.ofReal (t ^ (u - 2)) * (if ENNReal.ofReal t < a then a else 0) =
      (Iio α).indicator (fun t => a * ENNReal.ofReal (t ^ (u - 2))) t := by
    intro t
    by_cases h : t < α
    · have h' : ENNReal.ofReal t < a := by
        rw [haα]; exact (ENNReal.ofReal_lt_ofReal_iff hαpos).2 h
      rw [Set.indicator_of_mem (show t ∈ Iio α from h), if_pos h', mul_comm]
    · have h' : ¬ ENNReal.ofReal t < a := by
        rw [haα]
        intro hh
        exact h ((ENNReal.ofReal_lt_ofReal_iff hαpos).1 hh)
      rw [Set.indicator_of_notMem (show t ∉ Iio α from h), if_neg h']
      simp
  simp_rw [h1]
  rw [setLIntegral_indicator measurableSet_Iio, Iio_inter_Ioi,
    lintegral_const_mul' _ _ ha, cmxHLS_int_rpow hαpos.le (by linarith)]
  have h4pos : 0 < u - 1 := by linarith
  rw [haα, ← ENNReal.ofReal_mul hαpos.le, ENNReal.ofReal_rpow_of_pos hαpos,
    ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  have e : α ^ (u - 2 + 1) = α ^ (u - 1) := by congr 1; ring
  have e2 : α ^ u = α * α ^ (u - 1) := by
    rw [← Real.rpow_one_add' hαpos.le (by linarith)]; congr 1; ring
  have h4 : (u - 2 + 1) = u - 1 := by ring
  rw [e, e2, h4]
  field_simp

/-- the layer-cake integration of a distribution inequality of Marcinkiewicz type -/
lemma layer_bound {W f : 𝔼 → ℝ≥0∞} (hW : Measurable W) (hf : Measurable f) (hfT : ∀ x, f x ≠ ⊤)
    {u : ℝ} (hu1 : 1 < u) (hu4 : u < 4) {A4 A1 : ℝ≥0∞}
    (hdist : ∀ t : ℝ, 0 < t → volume {x | ENNReal.ofReal t < W x} ≤
      A4 * (ENNReal.ofReal (t ^ (-4 : ℝ)) *
        ∫⁻ x, (if f x ≤ ENNReal.ofReal t then f x ^ 4 else 0)) +
      A1 * (ENNReal.ofReal (t ^ (-1 : ℝ)) *
        ∫⁻ x, (if ENNReal.ofReal t < f x then f x else 0))) :
    ∫⁻ x, W x ^ u ≤ ENNReal.ofReal u * (A4 * (ENNReal.ofReal (1 / (4 - u)) * ∫⁻ x, f x ^ u) +
      A1 * (ENNReal.ofReal (1 / (u - 1)) * ∫⁻ x, f x ^ u)) := by
  have hu0 : 0 < u := by linarith
  have hP4m : Measurable (fun q : ℝ × 𝔼 => if f q.2 ≤ ENNReal.ofReal q.1 then f q.2 ^ 4 else 0) :=
    Measurable.ite (measurableSet_le (hf.comp measurable_snd) measurable_fst.ennreal_ofReal)
      ((hf.comp measurable_snd).pow_const 4) measurable_const
  have hP1m : Measurable (fun q : ℝ × 𝔼 => if ENNReal.ofReal q.1 < f q.2 then f q.2 else 0) :=
    Measurable.ite (measurableSet_lt measurable_fst.ennreal_ofReal (hf.comp measurable_snd))
      (hf.comp measurable_snd) measurable_const
  have key : ∀ N : ℕ, ∫⁻ x, (min (W x) (N : ℝ≥0∞)) ^ u ≤
      ENNReal.ofReal u * (A4 * (ENNReal.ofReal (1 / (4 - u)) * ∫⁻ x, f x ^ u) +
        A1 * (ENNReal.ofReal (1 / (u - 1)) * ∫⁻ x, f x ^ u)) := by
    intro N
    set gN : 𝔼 → ℝ := fun x => (min (W x) (N : ℝ≥0∞)).toReal with hgN
    have hmeas : Measurable gN := (hW.min measurable_const).ennreal_toReal
    have hlc := lintegral_rpow_eq_lintegral_meas_lt_mul volume (f := gN)
      (Eventually.of_forall fun x => ENNReal.toReal_nonneg) hmeas.aemeasurable hu0
    have hfin : ∀ x, min (W x) (N : ℝ≥0∞) ≠ ⊤ := fun x =>
      ne_top_of_le_ne_top (ENNReal.natCast_ne_top N) (min_le_right _ _)
    have hL : ∫⁻ x, (min (W x) (N : ℝ≥0∞)) ^ u = ∫⁻ z, ENNReal.ofReal (gN z ^ u) := by
      refine lintegral_congr fun x => ?_
      rw [hgN]
      simp only
      rw [← ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg hu0.le,
        ENNReal.ofReal_toReal (hfin x)]
    rw [hL, hlc]
    have hpt : ∀ t ∈ Ioi (0 : ℝ), volume {a | t < gN a} * ENNReal.ofReal (t ^ (u - 1)) ≤
        A4 * (∫⁻ x, ENNReal.ofReal (t ^ (u - 5)) *
            (if f x ≤ ENNReal.ofReal t then f x ^ 4 else 0)) +
          A1 * (∫⁻ x, ENNReal.ofReal (t ^ (u - 2)) *
            (if ENNReal.ofReal t < f x then f x else 0)) := by
      intro t ht
      have ht' : 0 < t := ht
      have hsub : {a | t < gN a} ⊆ {a | ENNReal.ofReal t < W a} := by
        intro a ha
        have ha' : t < gN a := ha
        have : ENNReal.ofReal t < min (W a) (N : ℝ≥0∞) :=
          (ENNReal.ofReal_lt_iff_lt_toReal ht'.le (hfin a)).2 ha'
        exact lt_of_lt_of_le this (min_le_left _ _)
      have e4 : ENNReal.ofReal (t ^ (-4 : ℝ)) * ENNReal.ofReal (t ^ (u - 1)) =
          ENNReal.ofReal (t ^ (u - 5)) := by
        rw [← ENNReal.ofReal_mul (Real.rpow_nonneg ht'.le _), ← Real.rpow_add ht']
        congr 2; ring
      have e1 : ENNReal.ofReal (t ^ (-1 : ℝ)) * ENNReal.ofReal (t ^ (u - 1)) =
          ENNReal.ofReal (t ^ (u - 2)) := by
        rw [← ENNReal.ofReal_mul (Real.rpow_nonneg ht'.le _), ← Real.rpow_add ht']
        congr 2; ring
      have hm4 : Measurable fun x => (if f x ≤ ENNReal.ofReal t then f x ^ 4 else 0) :=
        Measurable.ite (measurableSet_le hf measurable_const) (hf.pow_const 4) measurable_const
      have hm1 : Measurable fun x => (if ENNReal.ofReal t < f x then f x else 0) :=
        Measurable.ite (measurableSet_lt measurable_const hf) hf measurable_const
      rw [lintegral_const_mul _ hm4, lintegral_const_mul _ hm1]
      calc volume {a | t < gN a} * ENNReal.ofReal (t ^ (u - 1))
          ≤ volume {a | ENNReal.ofReal t < W a} * ENNReal.ofReal (t ^ (u - 1)) :=
            mul_le_mul_left (measure_mono (μ := volume) hsub) _
        _ ≤ (A4 * (ENNReal.ofReal (t ^ (-4 : ℝ)) *
              ∫⁻ x, (if f x ≤ ENNReal.ofReal t then f x ^ 4 else 0)) +
            A1 * (ENNReal.ofReal (t ^ (-1 : ℝ)) *
              ∫⁻ x, (if ENNReal.ofReal t < f x then f x else 0))) *
              ENNReal.ofReal (t ^ (u - 1)) := mul_le_mul_left (hdist t ht') _
        _ = A4 * (ENNReal.ofReal (t ^ (u - 5)) *
              ∫⁻ x, (if f x ≤ ENNReal.ofReal t then f x ^ 4 else 0)) +
            A1 * (ENNReal.ofReal (t ^ (u - 2)) *
              ∫⁻ x, (if ENNReal.ofReal t < f x then f x else 0)) := by
            rw [← e4, ← e1]; ring
    calc ENNReal.ofReal u * ∫⁻ t in Ioi (0 : ℝ), volume {a | t < gN a} * ENNReal.ofReal (t ^ (u - 1))
        ≤ ENNReal.ofReal u * ∫⁻ t in Ioi (0 : ℝ),
            (A4 * (∫⁻ x, ENNReal.ofReal (t ^ (u - 5)) *
                (if f x ≤ ENNReal.ofReal t then f x ^ 4 else 0)) +
              A1 * (∫⁻ x, ENNReal.ofReal (t ^ (u - 2)) *
                (if ENNReal.ofReal t < f x then f x else 0))) :=
          mul_le_mul_right (setLIntegral_mono' measurableSet_Ioi hpt) _
      _ = ENNReal.ofReal u * (A4 * (∫⁻ x, ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (t ^ (u - 5)) *
                (if f x ≤ ENNReal.ofReal t then f x ^ 4 else 0)) +
            A1 * (∫⁻ x, ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (t ^ (u - 2)) *
                (if ENNReal.ofReal t < f x then f x else 0))) := by
          congr 1
          have hφ4 : Measurable (fun q : ℝ × 𝔼 => ENNReal.ofReal (q.1 ^ (u - 5)) *
              (if f q.2 ≤ ENNReal.ofReal q.1 then f q.2 ^ 4 else 0)) :=
            (measurable_fst.pow_const _).ennreal_ofReal.mul hP4m
          have hφ1 : Measurable (fun q : ℝ × 𝔼 => ENNReal.ofReal (q.1 ^ (u - 2)) *
              (if ENNReal.ofReal q.1 < f q.2 then f q.2 else 0)) :=
            (measurable_fst.pow_const _).ennreal_ofReal.mul hP1m
          have hm4 : Measurable (fun t : ℝ => A4 * (∫⁻ x, ENNReal.ofReal (t ^ (u - 5)) *
              (if f x ≤ ENNReal.ofReal t then f x ^ 4 else 0))) :=
            (hφ4.lintegral_prod_right').const_mul _
          rw [lintegral_add_left hm4, lintegral_const_mul _ (hφ4.lintegral_prod_right'),
            lintegral_const_mul _ (hφ1.lintegral_prod_right')]
          have s4 := lintegral_lintegral_swap (μ := volume.restrict (Ioi (0 : ℝ))) (ν := (volume : Measure 𝔼))
            (f := fun (t : ℝ) (x : 𝔼) => ENNReal.ofReal (t ^ (u - 5)) *
              (if f x ≤ ENNReal.ofReal t then f x ^ 4 else 0)) hφ4.aemeasurable
          have s1 := lintegral_lintegral_swap (μ := volume.restrict (Ioi (0 : ℝ))) (ν := (volume : Measure 𝔼))
            (f := fun (t : ℝ) (x : 𝔼) => ENNReal.ofReal (t ^ (u - 2)) *
              (if ENNReal.ofReal t < f x then f x else 0)) hφ1.aemeasurable
          rw [s4, s1]
      _ = _ := by
          have h4 : ∫⁻ x, ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (t ^ (u - 5)) *
              (if f x ≤ ENNReal.ofReal t then f x ^ 4 else 0) =
              ENNReal.ofReal (1 / (4 - u)) * ∫⁻ x, f x ^ u := by
            rw [← lintegral_const_mul _ (hf.pow_const u)]
            exact lintegral_congr fun x => inner_J4 hu4 hu1 (hfT x)
          have h1 : ∫⁻ x, ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (t ^ (u - 2)) *
              (if ENNReal.ofReal t < f x then f x else 0) =
              ENNReal.ofReal (1 / (u - 1)) * ∫⁻ x, f x ^ u := by
            rw [← lintegral_const_mul _ (hf.pow_const u)]
            exact lintegral_congr fun x => inner_J1 hu1 (hfT x)
          rw [h4, h1]
  -- monotone convergence
  have hu0' : 0 ≤ u := hu0.le
  have hsup : ∀ x, W x ^ u = ⨆ N : ℕ, (min (W x) (N : ℝ≥0∞)) ^ u := by
    intro x
    have h1 : (⨆ N : ℕ, min (W x) (N : ℝ≥0∞)) = W x := by
      have := inf_iSup_eq (W x) (fun N : ℕ => (N : ℝ≥0∞))
      rw [ENNReal.iSup_natCast, inf_top_eq] at this
      exact this.symm
    conv_lhs => rw [← h1]
    refine Monotone.map_iSup_of_continuousAt (f := fun z : ℝ≥0∞ => z ^ u)
      ENNReal.continuous_rpow_const.continuousAt (ENNReal.monotone_rpow_of_nonneg hu0') ?_
    simp [ENNReal.zero_rpow_of_pos hu0]
  calc ∫⁻ x, W x ^ u = ∫⁻ x, ⨆ N : ℕ, (min (W x) (N : ℝ≥0∞)) ^ u := lintegral_congr hsup
    _ = ⨆ N : ℕ, ∫⁻ x, (min (W x) (N : ℝ≥0∞)) ^ u := by
        refine lintegral_iSup (fun N => ?_) (fun N M hNM x => ?_)
        · exact (hW.min measurable_const).pow_const _
        · exact ENNReal.monotone_rpow_of_nonneg hu0' (min_le_min le_rfl (by exact_mod_cast hNM))
    _ ≤ _ := iSup_le key

end HRS.Commutator.Whole.XLI
