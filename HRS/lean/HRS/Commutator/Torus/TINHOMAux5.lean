import HRS.Commutator.Torus.TINHOMAux4

/-!
# T-INHOM helpers, part 5: Hölder tools; the low part of the cross term vanishes
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators FourierTransform ComplexConjugate

namespace HRS.Commutator.TorusNote

open HRS

variable {d : ℕ} {s : ℝ}

lemma tinhom_holder12 {f g : Torus d → ℝ} (hf : AEStronglyMeasurable f volume)
    (hg : AEStronglyMeasurable g volume) :
    ENNReal.ofReal |∫ x, f x * g x| ≤ eLpNorm f 2 volume * eLpNorm g 2 volume := by
  have h1 : ENNReal.ofReal |∫ x, f x * g x| ≤ ∫⁻ x, ‖f x * g x‖ₑ := by
    rw [← Real.enorm_eq_ofReal_abs]
    exact enorm_integral_le_lintegral_enorm _
  refine h1.trans ?_
  have h2 := eLpNorm_smul_le_mul_eLpNorm (p := 2) (q := 2) (r := 1) hf hg
  have hm : AEStronglyMeasurable (f • g) volume := hf.smul hg
  rw [eLpNorm_one_eq_lintegral_enorm hm] at h2
  exact h2

lemma tinhom_holder_triple {P Q : ℝ≥0∞} [ENNReal.HolderTriple P Q 2] {f g : Torus d → ℝ}
    (hf : AEStronglyMeasurable f volume) (hg : AEStronglyMeasurable g volume) :
    eLpNorm (fun x => f x * g x) 2 volume ≤ eLpNorm f P volume * eLpNorm g Q volume :=
  eLpNorm_smul_le_mul_eLpNorm (p := P) (q := Q) (r := 2) hf hg

lemma tinhom_bdd_mul {f q : Torus d → ℝ} (hf : AEStronglyMeasurable f volume)
    (hq : AEStronglyMeasurable q volume) {M : ℝ} (hM : ∀ x, |q x| ≤ M) :
    eLpNorm (fun x => f x * q x) 2 volume ≤ ENNReal.ofReal M * eLpNorm f 2 volume := by
  have hm : AEStronglyMeasurable (fun x => f x * q x) volume := hf.mul hq
  refine eLpNorm_le_mul_eLpNorm_of_ae_le_mul hm (Eventually.of_forall fun x => ?_) 2
  show ‖f x * q x‖ ≤ M * ‖f x‖
  rw [norm_mul, Real.norm_eq_abs, mul_comm]
  gcongr
  exact hM x

lemma tinhom_sqrt_of_sq {N X : ℝ≥0∞} (h : N ^ 2 ≤ X) : N ≤ X ^ ((1 : ℝ) / 2) := by
  calc N = (N ^ 2) ^ ((1 : ℝ) / 2) := by
        rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
        norm_num
    _ ≤ X ^ ((1 : ℝ) / 2) := ENNReal.rpow_le_rpow h (by norm_num)

lemma tinhom_rpow_half_le {X Y : ℝ≥0∞} (c : ℝ) (hc : 0 ≤ c) (h : X ≤ ENNReal.ofReal c * Y) :
    X ^ ((1 : ℝ) / 2) ≤ ENNReal.ofReal (c ^ ((1 : ℝ) / 2)) * Y ^ ((1 : ℝ) / 2) := by
  calc X ^ ((1 : ℝ) / 2) ≤ (ENNReal.ofReal c * Y) ^ ((1 : ℝ) / 2) :=
        ENNReal.rpow_le_rpow h (by norm_num)
    _ = _ := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num),
          ENNReal.ofReal_rpow_of_nonneg hc (by norm_num)]

lemma tinhom_sqrt_mul_sqrt (X : ℝ≥0∞) : X ^ ((1 : ℝ) / 2) * X ^ ((1 : ℝ) / 2) = X := by
  rw [← ENNReal.rpow_add_of_nonneg _ _ (by norm_num) (by norm_num)]
  norm_num

/-- The low part of the cross term vanishes: `∫ a₀ v_lo,i (K_i * b) = 0`. -/
lemma tinhom_cross_lo (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) {η : ℝ} (hη : 0 < η)
    {a₀ b : Torus d → ℝ} (ha₀ : Continuous a₀) (hb : Continuous b)
    (hsupp : ∀ k : Lattice d, 1 / 8 < η * Lattice.enorm k → Torus.fcoef a₀ k = 0)
    {vlo : Torus d → Euc d} (B : Finset (Lattice d)) (c : Fin d → Lattice d → ℂ)
    (hvlo : ∀ i z, ((vlo z i : ℝ) : ℂ) = ∑ k ∈ B, c i k * Torus.mode k z)
    (hc : ∀ i k, c i k ≠ 0 → η * Lattice.enorm k < 1 / 2) (i : Fin d) :
    ∫ x, a₀ x * (vlo x i * textConv (fun z => ghiForceT s η z i) b x) = 0 := by
  have hK := tinhom_ghi_int hd hs0 hsd hη i
  have hKm := tinhom_ghi_meas hd hs0 hsd hη i
  obtain ⟨Bb, hBb⟩ := ten_bound_of_continuous hb
  have hBb' : ∀ x, |b x| ≤ Bb := fun x => by simpa using hBb x
  have hbi : Integrable b := (HRS.PDE.R2Aux.memLp_of_continuous_real hb).integrable (by norm_num)
  set φ : Torus d → ℝ := textConv (fun z => ghiForceT s η z i) b with hφ
  have hφm : Measurable φ := tinhom_conv_meas hKm hb.measurable
  have hφb : ∀ x, |φ x| ≤ (∫ z, |ghiForceT s η z i|) * Bb := fun x => tinhom_conv_bdd hK hBb' x
  have hφc : ∀ k, Torus.fcoef φ k = Torus.fcoef (fun z => ghiForceT s η z i) k * Torus.fcoef b k :=
    fun k => text_fcoef_conv hK hbi k
  -- expansion of `a₀`
  have hT : HRS.PDE.IsTrigPoly ⌈(1 / 8) / η + 1⌉₊ (fun k => Torus.fcoef a₀ k) :=
    HRS.HDB.isTrigPoly_of_enorm_lt (R := (1 / 8) / η + 1) (fun k hk => by
      have : η * Lattice.enorm k ≤ 1 / 8 := by
        by_contra hcon
        exact hk (hsupp k (not_le.1 hcon))
      have h2 : Lattice.enorm k ≤ (1 / 8) / η := by rw [le_div_iff₀ hη]; linarith
      linarith)
  have hexp := fun z => tlowv_trig_of_fcoef ha₀ hT (fun k => rfl) z
  set M := HRS.PDE.Kern.boxF d ⌈(1 / 8) / η + 1⌉₊ with hM
  -- the integrand as a finite double sum
  have hpt : ∀ x : Torus d, ((a₀ x * (vlo x i * φ x) : ℝ) : ℂ) =
      ∑ m ∈ M, ∑ k ∈ B, (Torus.fcoef a₀ m * c i k) * (Torus.mode (m + k) x * ((φ x : ℝ) : ℂ)) := by
    intro x
    push_cast
    rw [hexp x, hvlo i x, Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Torus.mode_add]
    ring
  have hint : ∀ m k : Lattice d, Integrable (fun x : Torus d => Torus.mode (m + k) x * ((φ x : ℝ) : ℂ)) := by
    intro m k
    refine Integrable.of_bound ((Torus.continuous_mode _).aestronglyMeasurable.mul
      (Complex.continuous_ofReal.measurable.comp hφm).aestronglyMeasurable)
      ((∫ z, |ghiForceT s η z i|) * Bb) (ae_of_all _ fun x => ?_)
    rw [norm_mul, Torus.norm_mode, one_mul, Complex.norm_real, Real.norm_eq_abs]
    exact hφb x
  have hzero : ∀ m ∈ M, ∀ k ∈ B, (Torus.fcoef a₀ m * c i k) *
      ∫ x, Torus.mode (m + k) x * ((φ x : ℝ) : ℂ) = 0 := by
    intro m _ k _
    by_cases h1 : Torus.fcoef a₀ m = 0
    · rw [h1, zero_mul, zero_mul]
    by_cases h2 : c i k = 0
    · rw [h2, mul_zero, zero_mul]
    have hm1 : η * Lattice.enorm m ≤ 1 / 8 := by
      by_contra hcon
      exact h1 (hsupp m (not_le.1 hcon))
    have hk1 := hc i k h2
    have hcoef : ∫ x, Torus.mode (m + k) x * ((φ x : ℝ) : ℂ) = Torus.fcoef φ (-(m + k)) := by
      unfold Torus.fcoef
      rw [neg_neg]
    rw [hcoef, hφc]
    have hlow : η * Lattice.enorm (-(m + k)) ≤ 1 := by
      rw [tlowv_enorm_neg]
      have := tlowv_enorm_add m k
      nlinarith
    rw [tinhom_ghi_fcoef_zero hd hs0 hsd hη i hlow]
    simp
  have hcomplex : (((∫ x, a₀ x * (vlo x i * φ x) : ℝ)) : ℂ) = 0 := by
    rw [← integral_complex_ofReal]
    simp_rw [hpt]
    rw [integral_finset_sum _ (fun m _ => integrable_finset_sum _ fun k _ => (hint m k).const_mul _)]
    refine Finset.sum_eq_zero fun m hm => ?_
    rw [integral_finset_sum _ (fun k _ => (hint m k).const_mul _)]
    refine Finset.sum_eq_zero fun k hk => ?_
    rw [integral_const_mul]
    exact hzero m hm k hk
  exact_mod_cast hcomplex

end HRS.Commutator.TorusNote
