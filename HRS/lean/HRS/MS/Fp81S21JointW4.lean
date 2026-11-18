import HRS.MS.Fp81S21JointW3
import HRS.MS.S111BDAux4

/-! Finite-coordinate Gaussian centering in time sections. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open Classical MeasureTheory Filter ProbabilityTheory
open scoped BigOperators
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R26T6

local instance fp81s21_jointW4_measurable (H : ℝ) : MeasurableSpace
    (Lp r26t6_Coeff 2 (volume.restrict (Set.Icc (0 : ℝ) H))) := borel _
local instance fp81s21_jointW4_borel (H : ℝ) : BorelSpace
    (Lp r26t6_Coeff 2 (volume.restrict (Set.Icc (0 : ℝ) H))) := ⟨rfl⟩

/-- Centering a finite sum of integrable scalar coordinates commutes with
forming the coefficient-basis sum. -/
theorem fp81s21_center_finite_basis
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (m : ℕ) (f : Fin m → Ω → ℝ) (hf : ∀ j, Integrable (f j) P) (ω : Ω) :
    fp81s21_center P (fun ω => ∑ j : Fin m, f j ω • fp81s21_coeffBasis j) ω =
      ∑ j : Fin m, fp81s21_center P (f j) ω • fp81s21_coeffBasis j := by
  unfold fp81s21_center
  rw [integral_finset_sum _ (fun j _ => (hf j).smul_const _)]
  simp_rw [integral_smul_const, sub_smul, Finset.sum_sub_distrib]

/-- Each raw Gaussian polynomial is integrable, by the physical fixed-time
Wick identity. -/
theorem fp81s21_physical31_rawPolynomial_integrable
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ)
    (Es : r26t6_WeightedChart p.d (2 * p.d + 6) ((p.d : ℝ) + 4))
    (E : r26t6_WeightedChart p.d (2 * p.d + 8) ((p.d : ℝ) + 2))
    (ε : ℕ → ℝ) (S : fp81s21_QuadraticPhysical31 p R Es E ε)
    (G : GaussianRealization R) (u : ℝ) (hu : 0 ≤ u)
    (D : fp81s21_RankKernel p.d) :
    Integrable (fun ω => fp81s21_polyAt D (G.Z u ω)) G.P := by
  have hw := fp81s21_physical31_rank_center p R Es E ε S G u hu D
  have he : (fun ω => (S.W G u (fp81s21_rankKernelLp R D) : G.Ω → ℝ) ω +
      ∫ ω', fp81s21_polyAt D (G.Z u ω') ∂G.P) =ᵐ[G.P]
      (fun ω => fp81s21_polyAt D (G.Z u ω)) := by
    filter_upwards [hw] with ω hω
    simp only [fp81s21_center] at hω
    linarith
  exact (((Lp.memLp (S.W G u (fp81s21_rankKernelLp R D))).integrable (by norm_num)).add
    (integrable_const _)).congr he

/-- If the raw and selected-rank fields have genuine time sections, their time
classes satisfy the Gaussian centering identity. -/
theorem fp81s21_GaussianRankTime31_of_representatives
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ)
    (Es : r26t6_WeightedChart p.d (2 * p.d + 6) ((p.d : ℝ) + 4))
    (E : r26t6_WeightedChart p.d (2 * p.d + 8) ((p.d : ℝ) + 2))
    (ε : ℕ → ℝ) (S : fp81s21_QuadraticPhysical31 p R Es E ε)
    (G : GaussianRealization R) (m : ℕ) (D : Fin m → fp81s21_RankKernel p.d)
    (q r : ℝ → G.Ω → r26t6_Coeff) (Mq Mr a H : ℝ)
    (U V : G.Ω → Lp r26t6_Coeff 2 (volume.restrict (Set.Icc (0 : ℝ) H)))
    (hq : Measurable (Function.uncurry q)) (hr : Measurable (Function.uncurry r))
    (ha : 0 ≤ a)
    (hqsec : ∀ u, 0 ≤ u → ∀ᵐ ω ∂G.P,
      q u ω = ∑ j : Fin m,
        (S.W G u (fp81s21_rankKernelLp R (D j)) : G.Ω → ℝ) ω • fp81s21_coeffBasis j)
    (hrsec : ∀ᵐ ω ∂G.P, ∀ u, 0 ≤ u →
      r u ω = ∑ j : Fin m, fp81s21_polyAt (D j) (G.Z u ω) • fp81s21_coeffBasis j)
    (hU : fp81s21_TimeL2Rep G.P q Mq a H U)
    (hV : fp81s21_TimeL2Rep G.P r Mr a H V) :
    U =ᵐ[G.P] fp81s21_center G.P V := by
  apply fp81s21_time_center_of_sections G.P q r Mq Mr a H U V hq hr ha _ hU hV
  intro u hu
  let f : Fin m → G.Ω → ℝ := fun j ω => fp81s21_polyAt (D j) (G.Z u ω)
  have hf : ∀ j, Integrable (f j) G.P := fun j =>
    fp81s21_physical31_rawPolynomial_integrable p R Es E ε S G u hu (D j)
  have hraw : (r u) =ᵐ[G.P] (fun ω => ∑ j : Fin m, f j ω • fp81s21_coeffBasis j) :=
    hrsec.mono (fun ω hω => hω u hu)
  have hmean := integral_congr_ae hraw
  have hall : ∀ᵐ ω ∂G.P, ∀ j : Fin m,
      (S.W G u (fp81s21_rankKernelLp R (D j)) : G.Ω → ℝ) ω =
        fp81s21_center G.P (f j) ω :=
    ae_all_iff.mpr (fun j => fp81s21_physical31_rank_center p R Es E ε S G u hu (D j))
  filter_upwards [hqsec u hu, hraw, hall] with ω hqω hrω hω
  calc
    q u ω = ∑ j : Fin m, fp81s21_center G.P (f j) ω • fp81s21_coeffBasis j := by
      rw [hqω]
      exact Finset.sum_congr rfl (fun j _ => by rw [hω j])
    _ = fp81s21_center G.P (fun ω => ∑ j : Fin m, f j ω • fp81s21_coeffBasis j) ω :=
      (fp81s21_center_finite_basis G.P m f hf ω).symm
    _ = fp81s21_center G.P (r u) ω := by
      simp only [fp81s21_center, hrω, hmean]

/-- The Gaussian window law provides a genuine L² time section for the
measurable raw polynomial field. -/
theorem fp81s21_rawPolynomial_time_section_of_fourth
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ) (G : GaussianRealization R)
    (m : ℕ) (D : Fin m → fp81s21_RankKernel p.d)
    (r : ℝ → G.Ω → r26t6_Coeff) (a H : ℝ) (ha : 0 ≤ a) (hH : 0 < H)
    (hr : Measurable (Function.uncurry r))
    (hrsec : ∀ᵐ ω ∂G.P, ∀ u, 0 ≤ u →
      r u ω = ∑ j : Fin m, fp81s21_polyAt (D j) (G.Z u ω) • fp81s21_coeffBasis j) :
    ∃ M : ℝ, ∃ V : G.Ω → Lp r26t6_Coeff 2
      (volume.restrict (Set.Icc (0 : ℝ) H)), fp81s21_TimeL2Rep G.P r M a H V := by
  obtain ⟨hWmeas, hWgauss, _⟩ := HRS.MS.S111BD.s111_shifted_window_gaussian
    p.d G.P (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ) p.β⁻¹ H a (a + H)
    (HRS.Whole.susceptibilityCov (rieszKernel p.d p.s) (r26t3_mu R 0) p.γ)
    G.Z (G.evolution (a + H)) hH ha le_rfl
  have hWlaw : HasGaussianLaw (processWindow (wholeSpaceIndex p.d : ℝ) H a G.Z) G.P :=
    ⟨hWmeas, hWgauss.1⟩
  have hWmem : MemLp (processWindow (wholeSpaceIndex p.d : ℝ) H a G.Z) 4 G.P :=
    hWlaw.memLp (by norm_num)
  have hfour := hWmem.integrable_norm_pow (by norm_num : (4 : ℕ) ≠ 0)
  let dt : Measure ℝ := volume.restrict (Set.Icc (0 : ℝ) H)
  let g : ℝ × G.Ω → r26t6_Coeff := fun z => r (a + z.1) z.2
  let X : G.Ω → OscPath p.d (wholeSpaceIndex p.d : ℝ) H :=
    processWindow (wholeSpaceIndex p.d : ℝ) H a G.Z
  let K : ℝ := ∑ j : Fin m, fp81s21_quadK (D j).c (D j).u
  have hK : 0 ≤ K := Finset.sum_nonneg fun j _ => fp81s21_quadK_nonneg _ _
  have hgm : Measurable g :=
    hr.comp ((measurable_const.add measurable_fst).prodMk measurable_snd)
  have hwindow : ∀ᵐ ω ∂G.P, ∀ j : Fin m, ∀ t : Set.Icc (0 : ℝ) H,
      fp81s21_polyAt (D j) (G.Z (a + t) ω) =
        fp81s21_quadPoly (D j).c (D j).u (X ω) t :=
    ae_all_iff.mpr (fun j => fp81s21_polyAt_gaussian_window p R G a H ha hH.le (D j))
  have hsample : ∀ᵐ z ∂(dt.prod G.P),
      (∀ u, 0 ≤ u → r u z.2 = ∑ j : Fin m,
        fp81s21_polyAt (D j) (G.Z u z.2) • fp81s21_coeffBasis j) ∧
      (∀ j : Fin m, ∀ t : Set.Icc (0 : ℝ) H,
        fp81s21_polyAt (D j) (G.Z (a + t) z.2) =
          fp81s21_quadPoly (D j).c (D j).u (X z.2) t) :=
    (Measure.quasiMeasurePreserving_snd (μ := dt) (ν := G.P)).ae (hrsec.and hwindow)
  have htimes : ∀ᵐ z ∂(dt.prod G.P), z.1 ∈ Set.Icc (0 : ℝ) H :=
    (Measure.quasiMeasurePreserving_fst (μ := dt) (ν := G.P)).ae
      (ae_restrict_mem measurableSet_Icc)
  have hbound : ∀ᵐ z ∂(dt.prod G.P), ‖g z‖ ^ 2 ≤ K ^ 2 * ‖X z.2‖ ^ 4 := by
    filter_upwards [hsample, htimes] with z hz ht
    let t : Set.Icc (0 : ℝ) H := ⟨z.1, ht⟩
    have ht0 : 0 ≤ a + z.1 := add_nonneg ha ht.1
    have hb : ∀ j : Fin m,
        ‖fp81s21_polyAt (D j) (G.Z (a + z.1) z.2) • fp81s21_coeffBasis j‖ ≤
          fp81s21_quadK (D j).c (D j).u * ‖X z.2‖ ^ 2 := by
      intro j
      have hp := fp81s21_quadPoly_bound (D j).valid (X z.2) t
      rw [← hz.2 j t] at hp
      simpa [t, norm_smul, fp81s21_coeffBasis.orthonormal.norm_eq_one,
        Real.norm_eq_abs] using hp
    have hg : ‖g z‖ ≤ K * ‖X z.2‖ ^ 2 := by
      rw [show g z = ∑ j : Fin m,
        fp81s21_polyAt (D j) (G.Z (a + z.1) z.2) • fp81s21_coeffBasis j from hz.1 _ ht0]
      calc
        _ ≤ ∑ j : Fin m, ‖fp81s21_polyAt (D j) (G.Z (a + z.1) z.2) • fp81s21_coeffBasis j‖ := norm_sum_le _ _
        _ ≤ ∑ j : Fin m, fp81s21_quadK (D j).c (D j).u * ‖X z.2‖ ^ 2 := Finset.sum_le_sum fun j _ => hb j
        _ = K * ‖X z.2‖ ^ 2 := by simp [K, Finset.sum_mul]
    have hs := pow_le_pow_left₀ (norm_nonneg (g z)) hg 2
    nlinarith [sq_nonneg ‖X z.2‖, sq_nonneg K]
  have hmajor : Integrable (fun z : ℝ × G.Ω => K ^ 2 * ‖X z.2‖ ^ 4) (dt.prod G.P) :=
    (hfour.const_mul (K ^ 2)).comp_snd dt
  have hint : Integrable (fun z => ‖g z‖ ^ 2) (dt.prod G.P) := by
    apply hmajor.mono' (hgm.norm.pow_const 2).aestronglyMeasurable
    filter_upwards [hbound] with z hz
    simpa [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ‖g z‖)] using hz
  have hg : MemLp g 2 (dt.prod G.P) :=
    (memLp_two_iff_integrable_sq_norm hgm.aestronglyMeasurable).2 hint
  have hs : ∀ᵐ ω ∂G.P, MemLp (fun t => g (t, ω)) 2 dt := by
    filter_upwards [hint.prod_left_ae] with ω hω
    exact (memLp_two_iff_integrable_sq_norm
      (hgm.comp (measurable_prodMk_right (y := ω))).aestronglyMeasurable).2 hω
  obtain ⟨V, hVm, hVL, hVeq, hVin⟩ := fp81s21_time_section_exists G.P H g hgm hg
  refine ⟨(∫ ω, ‖V ω‖ ^ 2 ∂G.P) / H, V, hVm, hVL, ?_, ?_⟩
  · field_simp
    exact le_rfl
  · filter_upwards [hs, hVeq] with ω hω heq
    exact ⟨hω, heq⟩

/-- A vector with the stated first coordinates and zero tail is the
corresponding finite basis sum. -/
theorem fp81s21_finite_basis_of_coordinates (m : ℕ) (c : Fin m → ℝ)
    (z : r26t6_Coeff)
    (hz : ∀ j : ℕ, z j = if hj : j < m then c ⟨j, hj⟩ else 0) :
    z = ∑ j : Fin m, c j • fp81s21_coeffBasis j := by
  have hsupport : fp81s21_projectField m (∑ j : Fin m, c j • fp81s21_coeffBasis j) =
      ∑ j : Fin m, c j • fp81s21_coeffBasis j := by
    simpa using fp81s21_finite_basis_sub_project_supported2 m c (0 : r26t6_Coeff)
  ext j
  by_cases hj : j < m
  · rw [hz j, dif_pos hj]
    exact (fp81s21_finite_basis_coordinate2 m c ⟨j, hj⟩).symm
  · rw [hz j, dif_neg hj, ← hsupport, fp81s21_projectField_coordinate2]
    simp [hj]

/-- The selected Gaussian rank time class is the actual-law-centered raw
projected polynomial time class. The raw field is jointly measurable and
agrees with the original Gaussian process on one common nonnegative-time event. -/
theorem fp81s21_GaussianRankTime31_physical
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ)
    (Es : r26t6_WeightedChart p.d (2 * p.d + 6) ((p.d : ℝ) + 4))
    (E : r26t6_WeightedChart p.d (2 * p.d + 8) ((p.d : ℝ) + 2))
    (ε : ℕ → ℝ) (S : fp81s21_QuadraticPhysical31 p R Es E ε)
    (G : GaussianRealization R) (m : ℕ) (D : Fin m → fp81s21_RankKernel p.d)
    (q : ℝ → G.Ω → r26t6_Coeff) (Mq a H : ℝ)
    (U : G.Ω → Lp r26t6_Coeff 2 (volume.restrict (Set.Icc (0 : ℝ) H)))
    (hq : Measurable (Function.uncurry q)) (ha : 0 ≤ a) (hH : 0 < H)
    (hqcoord : ∀ u, 0 ≤ u → ∀ᵐ ω ∂G.P, ∀ j : ℕ,
      q u ω j = if hj : j < m then
        (S.W G u (fp81s21_rankKernelLp R (D ⟨j, hj⟩)) : G.Ω → ℝ) ω else 0)
    (hU : fp81s21_TimeL2Rep G.P q Mq a H U) :
    ∃ r : ℝ → G.Ω → r26t6_Coeff, Measurable (Function.uncurry r) ∧
      (∀ᵐ ω ∂G.P, ∀ u, 0 ≤ u →
        r u ω = ∑ j : Fin m, fp81s21_polyAt (D j) (G.Z u ω) • fp81s21_coeffBasis j) ∧
      ∃ Mr : ℝ, ∃ V : G.Ω → Lp r26t6_Coeff 2 (volume.restrict (Set.Icc (0 : ℝ) H)),
        fp81s21_TimeL2Rep G.P r Mr a H V ∧ U =ᵐ[G.P] fp81s21_center G.P V := by
  obtain ⟨r, hr, hrsec⟩ := fp81s21_rawPolynomial_joint_field p R G m D
  obtain ⟨Mr, V, hV⟩ := fp81s21_rawPolynomial_time_section_of_fourth p R G m D r a H ha hH hr hrsec
  have hqsec : ∀ u, 0 ≤ u → ∀ᵐ ω ∂G.P,
      q u ω = ∑ j : Fin m,
        (S.W G u (fp81s21_rankKernelLp R (D j)) : G.Ω → ℝ) ω • fp81s21_coeffBasis j := by
    intro u hu
    filter_upwards [hqcoord u hu] with ω hω
    exact fp81s21_finite_basis_of_coordinates m
      (fun j => (S.W G u (fp81s21_rankKernelLp R (D j)) : G.Ω → ℝ) ω) (q u ω) hω
  exact ⟨r, hr, hrsec, Mr, V, hV,
    fp81s21_GaussianRankTime31_of_representatives p R Es E ε S G m D q r Mq Mr a H
      U V hq hr ha hqsec hrsec hU hV⟩

#print axioms fp81s21_GaussianRankTime31_physical
#print axioms fp81s21_finite_basis_of_coordinates
#print axioms fp81s21_rawPolynomial_time_section_of_fourth
#print axioms fp81s21_center_finite_basis
#print axioms fp81s21_physical31_rawPolynomial_integrable
#print axioms fp81s21_GaussianRankTime31_of_representatives
end HRS.Fp81.S21
end
