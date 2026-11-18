import HRS.Commutator.Torus.TEXTAux8

/-!
# T-EXT-A helpers, part 9: the transference lemma
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators FourierTransform

namespace HRS.Commutator.TorusNote

open HRS

variable {d : ℕ}

lemma text_transfer (hd : 1 ≤ d) {σ pr qr : ℝ} (hσ : 0 < σ) (hp : 1 < pr) (hpq : pr < qr)
    (hrel : 1 / qr = 1 / pr - σ / d) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ g : Torus d → ℝ≥0, Measurable g →
      ∫⁻ x : Torus d, (∫⁻ y, ENNReal.ofReal (KernelGrad.tdist x y ^ (σ - d)) *
          (g y : ℝ≥0∞)) ^ qr ≤
        C * (∫⁻ y, (g y : ℝ≥0∞) ^ pr) ^ (qr / pr) := by
  classical
  obtain ⟨Ch, hChpos, hCh⟩ := Whole.cmxHLS_kernel hd hσ hp hpq hrel
  set N : Finset (Lattice d) := Fintype.piFinset fun _ : Fin d => Finset.Icc (-1 : ℤ) 1 with hN
  have hq1 : 1 ≤ qr := by linarith
  refine ⟨(N.card : ℝ≥0∞) ^ (qr - 1) * (N.card : ℝ≥0∞) * ENNReal.ofReal Ch, ?_, fun g hg => ?_⟩
  · exact ENNReal.mul_ne_top (ENNReal.mul_ne_top
      (ENNReal.rpow_ne_top_of_nonneg (by linarith) (ENNReal.natCast_ne_top _))
      (ENNReal.natCast_ne_top _)) ENNReal.ofReal_ne_top
  set G : Euc d → ℝ≥0 := fun y => if y ∈ tposCell0 d then g (Torus.mk y) else 0 with hG
  have hGm : Measurable G :=
    Measurable.ite tpos_measurableSet_cell0 (hg.comp Torus.continuous_mk.measurable) measurable_const
  have hFm : Measurable (fun y : Euc d => (G y : ℝ≥0∞)) := hGm.coe_nnreal_ennreal
  set I : Euc d → ℝ≥0∞ := Whole.cmxHLS_I σ (fun y : Euc d => (G y : ℝ≥0∞)) with hI
  have hIm : Measurable I := Whole.cmxHLS_I_measurable σ hFm
  have hH := hCh G hGm
  have hGp : ∫⁻ y, (G y : ℝ≥0∞) ^ pr = ∫⁻ y, (g y : ℝ≥0∞) ^ pr := by
    rw [tpos_torus_lintegral (fun y => (g y : ℝ≥0∞) ^ pr), ← lintegral_indicator
      tpos_measurableSet_cell0]
    refine lintegral_congr fun y => ?_
    by_cases hy : y ∈ tposCell0 d
    · simp [G, hy, Set.indicator]
    · simp [G, hy, Set.indicator, ENNReal.zero_rpow_of_pos (by linarith : 0 < pr)]
  -- the potential of `g` at `mk u`
  set Φ : Torus d → ℝ≥0∞ := fun x =>
    ∫⁻ y, ENNReal.ofReal (KernelGrad.tdist x y ^ (σ - d)) * (g y : ℝ≥0∞) with hΦ
  have hkey : ∀ u ∈ tposCell0 d, Φ (Torus.mk u) ≤ ∑ n ∈ N, I (u - Lattice.toEuc n) := by
    intro u hu
    have e1 : Φ (Torus.mk u) = ∫⁻ v in tposCell0 d,
        ENNReal.ofReal (KernelGrad.tdist (Torus.mk u) (Torus.mk v) ^ (σ - d)) *
          (g (Torus.mk v) : ℝ≥0∞) := by
      simp only [hΦ]
      rw [tpos_torus_lintegral (fun y => ENNReal.ofReal (KernelGrad.tdist (Torus.mk u) y ^ (σ - d)) *
          (g y : ℝ≥0∞))]
    rw [e1]
    calc ∫⁻ v in tposCell0 d, ENNReal.ofReal (KernelGrad.tdist (Torus.mk u) (Torus.mk v) ^ (σ - d)) *
            (g (Torus.mk v) : ℝ≥0∞)
        ≤ ∫⁻ v in tposCell0 d, ∑ n ∈ N, ENNReal.ofReal (‖u - Lattice.toEuc n - v‖ ^ (σ - d)) *
            (g (Torus.mk v) : ℝ≥0∞) := by
          refine setLIntegral_mono' tpos_measurableSet_cell0 fun v hv => ?_
          rw [← Finset.sum_mul]
          exact mul_le_mul' (text_tdist_le_sum u v hu hv) le_rfl
      _ = ∑ n ∈ N, ∫⁻ v in tposCell0 d, ENNReal.ofReal (‖u - Lattice.toEuc n - v‖ ^ (σ - d)) *
            (g (Torus.mk v) : ℝ≥0∞) := by
          rw [lintegral_finsetSum]
          intro n _
          refine Measurable.mul ?_ (hg.coe_nnreal_ennreal.comp Torus.continuous_mk.measurable)
          exact ((measurable_norm.comp (measurable_const.sub measurable_id)).pow_const _).ennreal_ofReal
      _ = ∑ n ∈ N, I (u - Lattice.toEuc n) := by
          refine Finset.sum_congr rfl fun n _ => ?_
          simp only [hI, Whole.cmxHLS_I, Whole.cmxHLS_k]
          rw [← lintegral_indicator tpos_measurableSet_cell0]
          refine lintegral_congr fun v => ?_
          by_cases hv : v ∈ tposCell0 d
          · simp [G, hv, Set.indicator]
          · simp [G, hv, Set.indicator]
  have hpt : ∀ u ∈ tposCell0 d, Φ (Torus.mk u) ^ qr ≤
      (N.card : ℝ≥0∞) ^ (qr - 1) * ∑ n ∈ N, I (u - Lattice.toEuc n) ^ qr := by
    intro u hu
    calc Φ (Torus.mk u) ^ qr ≤ (∑ n ∈ N, I (u - Lattice.toEuc n)) ^ qr :=
          ENNReal.rpow_le_rpow (hkey u hu) (by linarith)
      _ ≤ _ := ENNReal.rpow_sum_le_const_mul_sum_rpow N (fun n => I (u - Lattice.toEuc n)) hq1
  calc ∫⁻ x : Torus d, Φ x ^ qr = ∫⁻ u in tposCell0 d, Φ (Torus.mk u) ^ qr :=
        tpos_torus_lintegral (fun x => Φ x ^ qr)
    _ ≤ ∫⁻ u in tposCell0 d, (N.card : ℝ≥0∞) ^ (qr - 1) * ∑ n ∈ N, I (u - Lattice.toEuc n) ^ qr :=
        setLIntegral_mono' tpos_measurableSet_cell0 hpt
    _ = (N.card : ℝ≥0∞) ^ (qr - 1) * ∑ n ∈ N, ∫⁻ u in tposCell0 d, I (u - Lattice.toEuc n) ^ qr := by
        rw [lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg (by linarith)
          (ENNReal.natCast_ne_top _)), lintegral_finsetSum]
        intro n _
        exact (hIm.comp (measurable_id.sub_const _)).pow_const _
    _ ≤ (N.card : ℝ≥0∞) ^ (qr - 1) * ∑ n ∈ N, ∫⁻ u, I (u - Lattice.toEuc n) ^ qr := by
        refine mul_le_mul' le_rfl (Finset.sum_le_sum fun n _ => ?_)
        exact setLIntegral_le_lintegral _ _
    _ = (N.card : ℝ≥0∞) ^ (qr - 1) * ((N.card : ℝ≥0∞) * ∫⁻ u, I u ^ qr) := by
        congr 1
        rw [Finset.sum_congr rfl fun n _ => lintegral_sub_right_eq_self (fun u => I u ^ qr)
          (Lattice.toEuc n)]
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (N.card : ℝ≥0∞) ^ (qr - 1) * ((N.card : ℝ≥0∞) *
          (ENNReal.ofReal Ch * (∫⁻ y, (G y : ℝ≥0∞) ^ pr) ^ (qr / pr))) := by
        exact mul_le_mul' le_rfl (mul_le_mul' le_rfl hH)
    _ = (N.card : ℝ≥0∞) ^ (qr - 1) * (N.card : ℝ≥0∞) * ENNReal.ofReal Ch *
          (∫⁻ y, (g y : ℝ≥0∞) ^ pr) ^ (qr / pr) := by
        rw [hGp]; ring

end HRS.Commutator.TorusNote
