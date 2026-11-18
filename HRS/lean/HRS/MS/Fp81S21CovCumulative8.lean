import HRS.MS.Fp81S21CovCumulative7

/-!
# HRS S2.1(iii), packet 19c-i: measurable covariance evaluation integrals

For fixed path evaluations, the moving empirical eta covariance integrand has
a jointly measurable sample-time representative.  This supplies scalar
coordinates for the projective tensor reconstruction lemma.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

namespace HRS.Fp81.S21

open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R2Interp

/-- Every fixed evaluation-pair covariance integral of the moving raw eta
field is a.e. measurable in the particle outcome. -/
theorem fp81s21_moving_raw_eta_pairing_integral_aemeasurable
    (p : Parameters) {δ H : ℝ} (R : Trajectory p δ)
    (hδ : 0 < δ) (hδh : δ ≤ 1 / 2) (hH : 0 < H)
    {N : ℕ} (hN : 2 ≤ N) (A : Particle R N)
    (ta tb q r : ℝ) (α β : MultiIndex p.d)
    (hta : ta ∈ Icc (0 : ℝ) H) (htb : tb ∈ Icc (0 : ℝ) H)
    (hq : 0 ≤ q) (hqr : q ≤ r) (hr : r ≤ H)
    (hφa : IsR2DualCombo (wholeSpaceIndex p.d : ℝ)
      (oscTestFun (wholeSpaceIndex p.d : ℝ) α))
    (hφb : IsR2DualCombo (wholeSpaceIndex p.d : ℝ)
      (oscTestFun (wholeSpaceIndex p.d : ℝ) β)) :
    AEMeasurable
      (fun ω => ∫ u in Ioc q r ∩ Icc (0 : ℝ) (min ta tb),
        fp81s21_movingRawEtaField p R A ω u (fun x =>
          inner ℝ
            (gradient (propagatorW (r26t3_coeff R) u ta
              (oscTestFun (wholeSpaceIndex p.d : ℝ) α)) x)
            (gradient (propagatorW (r26t3_coeff R) u tb
              (oscTestFun (wholeSpaceIndex p.d : ℝ) β)) x))) A.P := by
  classical
  have hN0 : 0 < N := by omega
  have hXcont : ∀ᵐ ω ∂A.P, ∀ k : Fin N,
      Continuous fun t : ℝ≥0 => A.X t ω k := (A.strong H).cont
  obtain ⟨Xjoint, hXjoint, hXae⟩ :=
    HRS.MS.R2S11.s11_X_joint (fun t => (A.strong H).adapted t) hXcont
  let clamp : ℝ → ℝ := fun u => max 0 (min u H)
  have hclamp : Continuous clamp := by
    dsimp [clamp]
    fun_prop
  have hclampMem : ∀ u, clamp u ∈ Icc (0 : ℝ) H := by
    intro u
    dsimp [clamp]
    exact ⟨le_max_left _ _, max_le hH.le (min_le_right _ _)⟩
  let ci : ℝ → Icc (0 : ℝ) H := fun u => ⟨clamp u, hclampMem u⟩
  have hci : Continuous ci := hclamp.subtype_mk _
  let ctime : ℝ → ℝ≥0 := fun u => ⟨clamp u, le_max_left _ _⟩
  have hρ := fp81s21_moving_density_joint_meas (H := H) p R hδ hδh
  have hρclip : Measurable
      (fun z : ℝ × Euc p.d => R.ρ (ctime z.1) z.2) := by
    have hm : Measurable fun z : ℝ × Euc p.d => (ci z.1, z.2) :=
      ((hci.comp continuous_fst).prodMk continuous_snd).measurable
    exact hρ.comp hm
  have hρ0 : ∀ u x, 0 ≤ R.ρ (ctime u) x := by
    intro u x
    exact ((R.resulting.global H).density (ctime u)
      (hclampMem u)).nonneg x
  obtain ⟨fa, hfa⟩ := fp81s21_adjoint_of_hermite_combo p R hφa hta.1
  obtain ⟨fb, hfb⟩ := fp81s21_adjoint_of_hermite_combo p R hφb htb.1
  have hFa : IsClassicalAdjointW (r26t3_coeff R) ta
      (oscTestFun (wholeSpaceIndex p.d : ℝ) α)
      (fun u => propagatorW (r26t3_coeff R) u ta
        (oscTestFun (wholeSpaceIndex p.d : ℝ) α)) := by
    exact s102_propagator_classical ⟨fa, hfa⟩
  have hFb : IsClassicalAdjointW (r26t3_coeff R) tb
      (oscTestFun (wholeSpaceIndex p.d : ℝ) β)
      (fun u => propagatorW (r26t3_coeff R) u tb
        (oscTestFun (wholeSpaceIndex p.d : ℝ) β)) := by
    exact s102_propagator_classical ⟨fb, hfb⟩
  let Va : ℝ × Euc p.d → Euc p.d := fun z =>
    if z.1 ∈ Icc (0 : ℝ) ta then
      gradient (propagatorW (r26t3_coeff R) z.1 ta
        (oscTestFun (wholeSpaceIndex p.d : ℝ) α)) z.2 else 0
  let Vb : ℝ × Euc p.d → Euc p.d := fun z =>
    if z.1 ∈ Icc (0 : ℝ) tb then
      gradient (propagatorW (r26t3_coeff R) z.1 tb
        (oscTestFun (wholeSpaceIndex p.d : ℝ) β)) z.2 else 0
  have hVam : Measurable Va := s102_gradJoint_meas hFa
  have hVbm : Measurable Vb := s102_gradJoint_meas hFb
  let G : ℝ × Euc p.d → ℝ := fun z => inner ℝ (Va z) (Vb z)
  have hGm : Measurable G := hVam.inner hVbm
  have hXjointEval : Measurable fun z : ℝ × A.Ω => Xjoint (z.1, z.2) := hXjoint
  have hsum : Measurable fun z : ℝ × A.Ω =>
      ∑ k : Fin N, G (z.1, Xjoint (z.1, z.2) k) := by
    refine Finset.measurable_sum _ fun k _ => ?_
    exact hGm.comp (measurable_fst.prodMk
      ((measurable_pi_apply k).comp hXjointEval))
  let center : ℝ → ℝ := fun u =>
    ∫ x, G (u, x) ∂(HRS.Whole.withDensityReal (R.ρ (ctime u)))
  have hcenterm : Measurable center :=
    fp81s21_moving_spatial_integral_meas hρclip hρ0 hGm
  let F : ℝ × A.Ω → ℝ := fun z =>
    Real.sqrt N * ((N : ℝ)⁻¹ * (∑ k : Fin N, G (z.1, Xjoint (z.1, z.2) k)) -
      center z.1)
  have hFm : Measurable F := by
    exact measurable_const.mul
      ((measurable_const.mul hsum).sub (hcenterm.comp measurable_fst))
  let D : Set ℝ := Ioc q r ∩ Icc (0 : ℝ) (min ta tb)
  have hD : MeasurableSet D := measurableSet_Ioc.inter measurableSet_Icc
  have hFint : Measurable fun ω => ∫ u in D, F (u, ω) := by
    have hswap : Measurable fun z : A.Ω × ℝ => F (z.2, z.1) :=
      hFm.comp measurable_swap
    exact (hswap.stronglyMeasurable.integral_prod_right'
      (ν := volume.restrict D)).measurable
  apply hFint.aemeasurable.congr
  filter_upwards [hXae] with ω hω
  apply setIntegral_congr_fun hD
  intro u hu
  have huD : u ∈ D := hu
  have hu0 : 0 ≤ u := le_trans hq huD.1.1.le
  have huH : u ≤ H := huD.1.2.trans hr
  have huTa : u ∈ Icc (0 : ℝ) ta :=
    ⟨hu0, huD.2.2.trans (min_le_left _ _)⟩
  have huTb : u ∈ Icc (0 : ℝ) tb :=
    ⟨hu0, huD.2.2.trans (min_le_right _ _)⟩
  have hclip : clamp u = u := by
    dsimp [clamp]
    rw [min_eq_left huH, max_eq_right hu0]
  have hρeq : (fun x : Euc p.d => R.ρ (ctime u) x) = R.ρ u := by
    funext x
    change R.ρ (clamp u) x = R.ρ u x
    rw [hclip]
  have hμ : HRS.Whole.withDensityReal (fun x : Euc p.d => R.ρ (ctime u) x) =
      r26t3_mu R u := by
    rw [hρeq]
    rfl
  have hGslice : (fun x => inner ℝ
      (gradient (propagatorW (r26t3_coeff R) u ta
        (oscTestFun (wholeSpaceIndex p.d : ℝ) α)) x)
      (gradient (propagatorW (r26t3_coeff R) u tb
        (oscTestFun (wholeSpaceIndex p.d : ℝ) β)) x)) =
      fun x => G (u, x) := by
    funext x
    simp only [G, Va, Vb, if_pos huTa, if_pos huTb]
  have hpair :
      HRS.Whole.pair (r26t3_mu R u) (fun x => G (u, x)) = center u := by
    rw [← hμ]
    rfl
  simp only [F, fp81s21_movingRawEtaField, s102_etaf]
  rw [hGslice, HRS.Whole.pair_empirical hN0, hω u]
  rw [hpair]

#print axioms HRS.Fp81.S21.fp81s21_moving_raw_eta_pairing_integral_aemeasurable

end HRS.Fp81.S21

end
