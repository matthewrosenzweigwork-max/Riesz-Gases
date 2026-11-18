import HRS.MS.CritForceLead3

/-!
# S8.2 NormalForm packet P05, part 4: the `d = 2` gradient bound `|∇ L| ≤ C ‖B‖`
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set

namespace HRS.MS.S82N

open HRS

/-- In dimension two the leading inverse is `(h0/(3ν)) |w| - (B w w)/(12ν |w|)`. -/
lemma s82n_rep_two (nu : ℝ) (hnu : 0 < nu) (B : Euc 2 →L[ℝ] Euc 2 →L[ℝ] ℝ) (w : Euc 2) (hw : w ≠ 0) :
    s82n_leadingInverse nu B w =
      ((∑ i, B (EuclideanSpace.basisFun (Fin 2) ℝ i) (EuclideanSpace.basisFun (Fin 2) ℝ i)) / 2 /
          (3 * nu)) * (‖w‖ ^ 2) ^ ((1 : ℝ) / 2) -
        (1 / (12 * nu)) * (B w w * (‖w‖ ^ 2) ^ (-(1 : ℝ) / 2)) := by
  have hr : 0 < ‖w‖ := norm_pos_iff.2 hw
  have hwt : 0 < ‖w‖ ^ 2 := by positivity
  have hs : s82n_critS 2 = 1 := by unfold s82n_critS; norm_num
  have hQw := s82n_omega_quad B w hw
  have e1 : (‖w‖ ^ 2) ^ ((1 : ℝ) / 2) = ‖w‖ := by
    rw [← Real.sqrt_eq_rpow, Real.sqrt_sq hr.le]
  have e2 : (‖w‖ ^ 2) ^ (-(1 : ℝ) / 2) = ‖w‖⁻¹ := by
    rw [show (-(1 : ℝ) / 2) = -((1 : ℝ) / 2) by norm_num, Real.rpow_neg hwt.le, e1]
  have e3 : ‖w‖ ^ (2 - s82n_critS 2) = ‖w‖ := by rw [hs]; norm_num
  simp only [s82n_leadingInverse, show (2 = 4) = False by norm_num, ite_false, hQw, e3, hs,
    s82n_trace_eq B, e1, e2]
  push_cast
  field_simp
  norm_num
  ring

lemma s82n_trace_two_le (B : Euc 2 →L[ℝ] Euc 2 →L[ℝ] ℝ) :
    |(∑ i, B (EuclideanSpace.basisFun (Fin 2) ℝ i) (EuclideanSpace.basisFun (Fin 2) ℝ i)) / 2| ≤
      ‖B‖ := by
  have h : ∀ i, |B (EuclideanSpace.basisFun (Fin 2) ℝ i) (EuclideanSpace.basisFun (Fin 2) ℝ i)| ≤
      ‖B‖ := fun i => by
    have := B.le_opNorm₂ (EuclideanSpace.basisFun (Fin 2) ℝ i) (EuclideanSpace.basisFun (Fin 2) ℝ i)
    simpa [Real.norm_eq_abs] using this
  rw [Fin.sum_univ_two, abs_div]
  have := abs_add_le (B (EuclideanSpace.basisFun (Fin 2) ℝ 0) (EuclideanSpace.basisFun (Fin 2) ℝ 0))
    (B (EuclideanSpace.basisFun (Fin 2) ℝ 1) (EuclideanSpace.basisFun (Fin 2) ℝ 1))
  have h0 := h 0
  have h1 := h 1
  rw [abs_two]
  linarith

theorem s82n_leading_grad (nu : ℝ) (hnu : 0 < nu) (B : Euc 2 →L[ℝ] Euc 2 →L[ℝ] ℝ)
    (hB : ∀ x y, B x y = B y x) (z : Euc 2) (hz : z ≠ 0) :
    ‖gradient (s82n_leadingInverse nu B) z‖ ≤ (7 / (12 * nu)) * ‖B‖ := by
  have hr : 0 < ‖z‖ := norm_pos_iff.2 hz
  have ht : 0 < ‖z‖ ^ 2 := by positivity
  set c : ℝ := ((∑ i, B (EuclideanSpace.basisFun (Fin 2) ℝ i) (EuclideanSpace.basisFun (Fin 2) ℝ i)) / 2 /
          (3 * nu)) with hc
  set k : ℝ := 1 / (12 * nu) with hk
  let F : Euc 2 → ℝ := fun w => c * (‖w‖ ^ 2) ^ ((1 : ℝ) / 2) -
    k * (B w w * (‖w‖ ^ 2) ^ (-(1 : ℝ) / 2))
  have hnear : ∀ᶠ w in 𝓝 z, w ≠ 0 := isOpen_ne.mem_nhds hz
  have hcongr : s82n_leadingInverse nu B =ᶠ[𝓝 z] F :=
    hnear.mono fun w hw => s82n_rep_two nu hnu B w hw
  have hn : HasFDerivAt (fun x : Euc 2 => ‖x‖ ^ 2) ((2 : ℕ) • innerSL ℝ z) z :=
    (hasStrictFDerivAt_norm_sq z).hasFDerivAt
  have hg1 : HasFDerivAt (fun x : Euc 2 => (‖x‖ ^ 2) ^ ((1 : ℝ) / 2))
      (((1 : ℝ) / 2 * (‖z‖ ^ 2) ^ ((1 : ℝ) / 2 - 1)) • ((2 : ℕ) • innerSL ℝ z)) z := by
    have h0 := Real.hasDerivAt_rpow_const (x := ‖z‖ ^ 2) (p := (1 : ℝ) / 2) (Or.inl ht.ne')
    exact h0.comp_hasFDerivAt (f := fun x : Euc 2 => ‖x‖ ^ 2) z hn
  have hg2 : HasFDerivAt (fun x : Euc 2 => (‖x‖ ^ 2) ^ (-(1 : ℝ) / 2))
      (((-(1 : ℝ) / 2) * (‖z‖ ^ 2) ^ (-(1 : ℝ) / 2 - 1)) • ((2 : ℕ) • innerSL ℝ z)) z := by
    have h0 := Real.hasDerivAt_rpow_const (x := ‖z‖ ^ 2) (p := -(1 : ℝ) / 2) (Or.inl ht.ne')
    exact h0.comp_hasFDerivAt (f := fun x : Euc 2 => ‖x‖ ^ 2) z hn
  have hF := (hg1.const_mul c).sub (((s82n_hasFDerivAt_quad B hB z).mul hg2).const_mul k)
  have hF' : HasFDerivAt F _ z := hF
  have hgrad : ‖gradient (s82n_leadingInverse nu B) z‖ =
      ‖fderiv ℝ (s82n_leadingInverse nu B) z‖ := by
    unfold gradient; exact (InnerProductSpace.toDual ℝ (Euc 2)).symm.norm_map _
  rw [hgrad, hcongr.fderiv_eq, hF'.fderiv]
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
  have e1 : (‖z‖ ^ 2) ^ ((1 : ℝ) / 2) = ‖z‖ := by
    rw [← Real.sqrt_eq_rpow, Real.sqrt_sq hr.le]
  have e2 : (‖z‖ ^ 2) ^ (-(1 : ℝ) / 2) = ‖z‖⁻¹ := by
    rw [show (-(1 : ℝ) / 2) = -((1 : ℝ) / 2) by norm_num, Real.rpow_neg ht.le, e1]
  have e3 : (‖z‖ ^ 2) ^ ((1 : ℝ) / 2 - 1) = ‖z‖⁻¹ := by
    rw [Real.rpow_sub_one ht.ne', e1]; field_simp
  have e4 : (‖z‖ ^ 2) ^ (-(1 : ℝ) / 2 - 1) = (‖z‖ ^ 3)⁻¹ := by
    rw [Real.rpow_sub_one ht.ne', e2]; field_simp
  set a : ℝ := inner ℝ z v with ha
  set bB : ℝ := B z v with hbB
  set Q : ℝ := B z z with hQ
  have hE : (c • (1 / 2 * (‖z‖ ^ 2) ^ ((1 : ℝ) / 2 - 1)) • (2 : ℕ) • innerSL ℝ z -
          k • (Q • (-1 / 2 * (‖z‖ ^ 2) ^ (-(1 : ℝ) / 2 - 1)) • (2 : ℕ) • innerSL ℝ z +
            (‖z‖ ^ 2) ^ (-(1 : ℝ) / 2) • (2 : ℝ) • B z)) v =
      c * (a / ‖z‖) + k * ((Q / ‖z‖ ^ 2) * (a / ‖z‖)) - 2 * k * (bB / ‖z‖) := by
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply, smul_apply,
      innerSL_apply_apply, smul_eq_mul, nsmul_eq_mul, e2, e3, e4, ← ha, ← hbB, ← hQ]
    have : inner ℝ z v = a := rfl
    rw [real_inner_comm] at this
    push_cast
    field_simp
    ring
  rw [hE, Real.norm_eq_abs]
  have hz0 : ‖z‖ ≠ 0 := hr.ne'
  have hA : |a / ‖z‖| ≤ ‖v‖ := by
    rw [abs_div, abs_of_pos hr, div_le_iff₀ hr]
    have := abs_real_inner_le_norm z v
    linarith [mul_comm ‖z‖ ‖v‖]
  have hQb : |Q / ‖z‖ ^ 2| ≤ ‖B‖ := by
    rw [abs_div, abs_of_pos ht, div_le_iff₀ ht]
    have := B.le_opNorm₂ z z
    rw [Real.norm_eq_abs] at this
    nlinarith [this]
  have hBb : |bB / ‖z‖| ≤ ‖B‖ * ‖v‖ := by
    rw [abs_div, abs_of_pos hr, div_le_iff₀ hr]
    have := B.le_opNorm₂ z v
    rw [Real.norm_eq_abs] at this
    nlinarith [this]
  have hcb : |c| ≤ ‖B‖ / (3 * nu) := by
    rw [hc, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 3 * nu), div_le_div_iff_of_pos_right (by positivity)]
    exact s82n_trace_two_le B
  have hkpos : 0 < k := by positivity
  have hB0 : 0 ≤ ‖B‖ := ContinuousLinearMap.opNorm_nonneg B
  have hv0 : 0 ≤ ‖v‖ := norm_nonneg _
  have h1 : |c * (a / ‖z‖)| ≤ ‖B‖ / (3 * nu) * ‖v‖ := by
    rw [abs_mul]; exact mul_le_mul hcb hA (abs_nonneg _) (by positivity)
  have h2 : |k * ((Q / ‖z‖ ^ 2) * (a / ‖z‖))| ≤ k * (‖B‖ * ‖v‖) := by
    rw [abs_mul, abs_of_pos hkpos, abs_mul]
    exact mul_le_mul_of_nonneg_left (mul_le_mul hQb hA (abs_nonneg _) hB0) hkpos.le
  have h3 : |2 * k * (bB / ‖z‖)| ≤ 2 * k * (‖B‖ * ‖v‖) := by
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * k)]
    exact mul_le_mul_of_nonneg_left hBb (by positivity)
  calc |c * (a / ‖z‖) + k * ((Q / ‖z‖ ^ 2) * (a / ‖z‖)) - 2 * k * (bB / ‖z‖)|
      ≤ |c * (a / ‖z‖)| + |k * ((Q / ‖z‖ ^ 2) * (a / ‖z‖))| + |2 * k * (bB / ‖z‖)| := by
        refine (abs_sub _ _).trans ?_
        gcongr
        exact abs_add_le _ _
    _ ≤ ‖B‖ / (3 * nu) * ‖v‖ + k * (‖B‖ * ‖v‖) + 2 * k * (‖B‖ * ‖v‖) := by gcongr
    _ = 7 / (12 * nu) * ‖B‖ * ‖v‖ := by
        rw [hk]; field_simp; ring

/-- Packet S82.P05 (`leading_harmonics`), with `criticalS d = d/2`: the exact degree-zero/two leading
inverse, its Laplacian identity away from the origin, and the `d = 2` gradient bound. -/
theorem s82n_leading_harmonics (d : ℕ) (hd : 2 ≤ d) (nu : ℝ) (hnu : 0 < nu) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ B : Euc d →L[ℝ] Euc d →L[ℝ] ℝ,
      (∀ x y, B x y = B y x) →
      (∀ z : Euc d, z ≠ 0 →
        -2 * nu * Laplacian.laplacian (s82n_leadingInverse nu B) z =
          -(s82n_critS d / 2) * ‖z‖ ^ (-s82n_critS d) *
            B (‖z‖⁻¹ • z) (‖z‖⁻¹ • z)) ∧
      (d = 2 → ∀ z : Euc d, z ≠ 0 →
        ‖gradient (s82n_leadingInverse nu B) z‖ ≤ C * ‖B‖) := by
  refine ⟨7 / (12 * nu), by positivity, fun B hB => ⟨fun z hz =>
    s82n_leading_laplacian hd nu hnu B hB z hz, fun hd2 z hz => ?_⟩⟩
  subst hd2
  exact s82n_leading_grad nu hnu B hB z hz

end HRS.MS.S82N
