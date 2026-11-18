import HRS.MS.SA12NN2B

/-!
# S.A.12 N2 (SA12N), part C: local `L²` bound for an operator dominated by a power kernel

If `|T x| ≤ ∫ A ‖x-y‖^{-t} |ψ(y)| dy` on `B̄(c', r')` (`r' ≤ ρ`, `ρ ≥ 1`, `supp ψ ⊆ B̄(c, ρ)`, `0 ≤ t < d`)
then `‖1_{B̄(c',r')} T‖_{L²} ≤ A C₁ ρ^d ‖ψ‖_{L²}`.  Near/far split as in `UniqN1a.n1a_hess_local`:
Young `L¹ * L²` for the kernel cut at `5ρ` when `|c - c'| ≤ 3ρ`, and the bound `A` otherwise.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal ContDiff

namespace HRS.MH.AdjointRd.Phase2SA12Near

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MS.UniqT3 HRS.MS.UniqN0
  HRS.MH.Screened HRS.MS.UniqN1a

variable {d : ℕ}

theorem sa12n_young_pow (hd : 1 ≤ d) {t : ℝ} (ht0 : 0 ≤ t) (htd : t < d) :
    ∃ C1 : ℝ, 0 ≤ C1 ∧ ∀ (A : ℝ), 0 ≤ A → ∀ (ρ : ℝ), 1 ≤ ρ → ∀ (c : Euc d) (ψ : Euc d → ℝ),
      Measurable ψ → Function.support ψ ⊆ closedBall c ρ →
      ∀ (c' : Euc d) (r' : ℝ), r' ≤ ρ → ∀ T : Euc d → ℝ, AEStronglyMeasurable T volume →
      (∀ x ∈ closedBall c' r', ‖T x‖ₑ ≤
        ∫⁻ y, ENNReal.ofReal (A * ‖x - y‖ ^ (-t)) * ‖ψ y‖ₑ) →
        eLpNorm ((closedBall c' r').indicator T) 2 volume ≤
          ENNReal.ofReal (A * C1 * ρ ^ (d : ℝ)) * eLpNorm ψ 2 volume := by
  obtain ⟨CK, hCK0, hCK⟩ := lintegral_ball_rpow_le_proof (d := d) hd htd
  set V1r : ℝ := (volume (closedBall (0 : Euc d) 1)).toReal with hV1r
  have hV1r0 : 0 ≤ V1r := ENNReal.toReal_nonneg
  have h5d : (0 : ℝ) ≤ (5 : ℝ) ^ (d : ℝ) := Real.rpow_nonneg (by norm_num) _
  refine ⟨CK * (5 : ℝ) ^ (d : ℝ) + V1r, by positivity, fun A hA ρ hρ c ψ hψm hsupp c' r' hr' T hTm hT => ?_⟩
  have hρ0 : 0 ≤ ρ := by linarith
  set Nv := eLpNorm ψ 2 volume with hNv
  have hNv2 : Nv ^ 2 = ∫⁻ x, ‖ψ x‖ₑ ^ 2 := l1_sq_eLpNorm_ae ψ hψm.aestronglyMeasurable
  have hρd : 0 ≤ ρ ^ (d : ℝ) := Real.rpow_nonneg hρ0 _
  have hind : AEStronglyMeasurable ((closedBall c' r').indicator T) volume :=
    hTm.indicator measurableSet_closedBall
  suffices hsq : (eLpNorm ((closedBall c' r').indicator T) 2 volume) ^ 2 ≤
      (ENNReal.ofReal (A * (CK * (5 : ℝ) ^ (d : ℝ) + V1r) * ρ ^ (d : ℝ)) * Nv) ^ 2 by
    exact (ENNReal.pow_le_pow_left_iff two_ne_zero).1 hsq
  rw [l1_sq_eLpNorm_ae _ hind]
  by_cases hnear : dist c' c ≤ 3 * ρ
  · set k : Euc d → ℝ≥0∞ := (closedBall (0 : Euc d) (5 * ρ)).indicator
      (fun u => ENNReal.ofReal (A * ‖u‖ ^ (-t))) with hk
    have hkm : Measurable k := by
      refine Measurable.indicator ?_ measurableSet_closedBall
      fun_prop
    have hkI : ∫⁻ u, k u ≤ ENNReal.ofReal (A * CK * (5 : ℝ) ^ (d : ℝ) * ρ ^ (d : ℝ)) := by
      have h5 : (0 : ℝ) < 5 * ρ := by linarith
      calc ∫⁻ u, k u = ∫⁻ u in closedBall (0 : Euc d) (5 * ρ), ENNReal.ofReal (A * ‖u‖ ^ (-t)) :=
            lintegral_indicator measurableSet_closedBall _
        _ = ENNReal.ofReal A * ∫⁻ u in closedBall (0 : Euc d) (5 * ρ),
              ENNReal.ofReal (‖u‖ ^ (-t)) := by
            rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
            refine lintegral_congr fun u => ?_
            rw [ENNReal.ofReal_mul hA]
        _ ≤ ENNReal.ofReal A * ENNReal.ofReal (CK * (5 * ρ) ^ ((d : ℝ) - t)) :=
            mul_le_mul_of_nonneg_left (hCK _ h5) (by positivity)
        _ = ENNReal.ofReal (A * (CK * (5 * ρ) ^ ((d : ℝ) - t))) := by
            rw [ENNReal.ofReal_mul hA]
        _ ≤ ENNReal.ofReal (A * CK * (5 : ℝ) ^ (d : ℝ) * ρ ^ (d : ℝ)) := by
            apply ENNReal.ofReal_le_ofReal
            have he : (d : ℝ) - t ≤ (d : ℝ) := by linarith
            have h5e : (5 : ℝ) ^ ((d : ℝ) - t) ≤ (5 : ℝ) ^ (d : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le (by norm_num) he
            have hre : ρ ^ ((d : ℝ) - t) ≤ ρ ^ (d : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le hρ he
            have : A * (CK * (5 * ρ) ^ ((d : ℝ) - t)) =
                (A * CK) * ((5 : ℝ) ^ ((d : ℝ) - t) * ρ ^ ((d : ℝ) - t)) := by
              rw [Real.mul_rpow (by norm_num) hρ0]; ring
            rw [this]
            calc (A * CK) * ((5 : ℝ) ^ ((d : ℝ) - t) * ρ ^ ((d : ℝ) - t))
                ≤ (A * CK) * ((5 : ℝ) ^ (d : ℝ) * ρ ^ (d : ℝ)) :=
                  mul_le_mul_of_nonneg_left (mul_le_mul h5e hre (by positivity) (by positivity))
                    (mul_nonneg hA hCK0)
              _ = _ := by ring
    have hk1 : ∫⁻ u, k u ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hkI
    set G : Euc d → ℝ≥0∞ := fun x => ∫⁻ y, k (x - y) * ‖ψ y‖ₑ with hG
    have hpt : ∀ x, ‖(closedBall c' r').indicator T x‖ₑ ≤ G x := by
      intro x
      by_cases hx : x ∈ closedBall c' r'
      · rw [Set.indicator_of_mem hx]
        refine (hT x hx).trans (lintegral_mono fun y => ?_)
        by_cases hv0 : ψ y = 0
        · simp [hv0]
        · have hyB : y ∈ closedBall c ρ := hsupp (Function.mem_support.2 hv0)
          have hxd : dist x c' ≤ ρ := le_trans (mem_closedBall.1 hx) hr'
          have hcy : dist c y ≤ ρ := by rw [dist_comm]; exact mem_closedBall.1 hyB
          have hxy : ‖x - y‖ ≤ 5 * ρ := by
            rw [← dist_eq_norm]; linarith [dist_triangle4 x c' c y]
          have hmem5 : x - y ∈ closedBall (0 : Euc d) (5 * ρ) := mem_closedBall_zero_iff.2 hxy
          simp only [hk]
          rw [Set.indicator_of_mem hmem5]
      · rw [Set.indicator_of_notMem hx]; simp
    have hYoung := young_l1_l2_proof k (fun y => ‖ψ y‖ₑ) hkm hψm.enorm hk1
    have hsq1 : ∫⁻ x, ‖(closedBall c' r').indicator T x‖ₑ ^ 2 ≤ ∫⁻ x, G x ^ 2 :=
      lintegral_mono fun x => pow_le_pow_left₀ (by positivity) (hpt x) 2
    have hYle : ENNReal.ofReal (A * CK * (5 : ℝ) ^ (d : ℝ) * ρ ^ (d : ℝ)) ≤
        ENNReal.ofReal (A * (CK * (5 : ℝ) ^ (d : ℝ) + V1r) * ρ ^ (d : ℝ)) := by
      apply ENNReal.ofReal_le_ofReal
      have : A * CK * (5 : ℝ) ^ (d : ℝ) ≤ A * (CK * (5 : ℝ) ^ (d : ℝ) + V1r) := by
        nlinarith [mul_nonneg hA hV1r0]
      exact mul_le_mul_of_nonneg_right this hρd
    calc ∫⁻ x, ‖(closedBall c' r').indicator T x‖ₑ ^ 2
        ≤ ∫⁻ x, G x ^ 2 := hsq1
      _ ≤ (∫⁻ y, k y) ^ 2 * ∫⁻ y, ‖ψ y‖ₑ ^ 2 := hYoung
      _ = (∫⁻ y, k y) ^ 2 * Nv ^ 2 := by rw [hNv2]
      _ ≤ (ENNReal.ofReal (A * CK * (5 : ℝ) ^ (d : ℝ) * ρ ^ (d : ℝ)) * Nv) ^ 2 := by
          rw [mul_pow]
          exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hkI 2) (by positivity)
      _ ≤ (ENNReal.ofReal (A * (CK * (5 : ℝ) ^ (d : ℝ) + V1r) * ρ ^ (d : ℝ)) * Nv) ^ 2 :=
          pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_right hYle (by positivity)) 2
  · have hnear' : 3 * ρ < dist c' c := not_le.mp hnear
    set X : ℝ≥0∞ := ENNReal.ofReal (ρ ^ (d : ℝ) * V1r) with hX
    have hvolB : volume (closedBall c ρ) ≤ X := l1_vol_closedBall_le c le_rfl hρ0
    have hvolB' : volume (closedBall c' r') ≤ X := l1_vol_closedBall_le c' hr' hρ0
    have hm_pt : ∀ x ∈ closedBall c' r', ∀ y,
        ENNReal.ofReal (A * ‖x - y‖ ^ (-t)) * ‖ψ y‖ₑ ≤ ENNReal.ofReal A * ‖ψ y‖ₑ := by
      intro x hx y
      by_cases hv0 : ψ y = 0
      · simp [hv0]
      · have hyB : y ∈ closedBall c ρ := hsupp (Function.mem_support.2 hv0)
        have hxd : dist x c' ≤ ρ := le_trans (mem_closedBall.1 hx) hr'
        have hyd : dist y c ≤ ρ := mem_closedBall.1 hyB
        have h1 : ρ < ‖x - y‖ := by
          rw [← dist_eq_norm]
          have h3 := dist_triangle4 c' x y c
          rw [dist_comm c' x] at h3
          linarith
        have hge : 1 ≤ ‖x - y‖ := by linarith
        have hpow : ‖x - y‖ ^ (-t) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hge (by linarith)
        refine mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal ?_) (by positivity)
        calc A * ‖x - y‖ ^ (-t) ≤ A * 1 := mul_le_mul_of_nonneg_left hpow hA
          _ = A := mul_one A
    have hwb : ∀ x ∈ closedBall c' r', ‖T x‖ₑ ≤ ENNReal.ofReal A * ∫⁻ y, ‖ψ y‖ₑ := by
      intro x hx
      calc ‖T x‖ₑ ≤ ∫⁻ y, ENNReal.ofReal (A * ‖x - y‖ ^ (-t)) * ‖ψ y‖ₑ := hT x hx
        _ ≤ ∫⁻ y, ENNReal.ofReal A * ‖ψ y‖ₑ := lintegral_mono fun y => hm_pt x hx y
        _ = ENNReal.ofReal A * ∫⁻ y, ‖ψ y‖ₑ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    have hsq2 : ∫⁻ x, ‖(closedBall c' r').indicator T x‖ₑ ^ 2 ≤
        ∫⁻ x, (closedBall c' r').indicator
          (fun _ : Euc d => (ENNReal.ofReal A * ∫⁻ y, ‖ψ y‖ₑ) ^ 2) x := by
      refine lintegral_mono fun x => ?_
      by_cases hx : x ∈ closedBall c' r'
      · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]
        exact pow_le_pow_left₀ (by positivity) (hwb x hx) 2
      · simp [Set.indicator_of_notMem hx]
    rw [lintegral_indicator_const measurableSet_closedBall] at hsq2
    have hL1 : (∫⁻ y, ‖ψ y‖ₑ) ^ 2 ≤ volume (closedBall c ρ) * Nv ^ 2 := by
      rw [hNv2]
      exact l1_holder hψm.aestronglyMeasurable measurableSet_closedBall hsupp
    have hYle : ENNReal.ofReal A * X ≤
        ENNReal.ofReal (A * (CK * (5 : ℝ) ^ (d : ℝ) + V1r) * ρ ^ (d : ℝ)) := by
      rw [hX, ← ENNReal.ofReal_mul hA]
      apply ENNReal.ofReal_le_ofReal
      have e1 : A * (CK * (5 : ℝ) ^ (d : ℝ) + V1r) * ρ ^ (d : ℝ) =
          A * (CK * (5 : ℝ) ^ (d : ℝ)) * ρ ^ (d : ℝ) + A * (ρ ^ (d : ℝ) * V1r) := by ring
      rw [e1]
      have : 0 ≤ A * (CK * (5 : ℝ) ^ (d : ℝ)) * ρ ^ (d : ℝ) := by positivity
      linarith
    calc ∫⁻ x, ‖(closedBall c' r').indicator T x‖ₑ ^ 2
        ≤ (ENNReal.ofReal A * ∫⁻ y, ‖ψ y‖ₑ) ^ 2 * volume (closedBall c' r') := hsq2
      _ = ENNReal.ofReal A ^ 2 * (∫⁻ y, ‖ψ y‖ₑ) ^ 2 * volume (closedBall c' r') := by ring
      _ ≤ ENNReal.ofReal A ^ 2 * (volume (closedBall c ρ) * Nv ^ 2) * X := by gcongr
      _ ≤ ENNReal.ofReal A ^ 2 * (X * Nv ^ 2) * X := by gcongr
      _ = (ENNReal.ofReal A * X) ^ 2 * Nv ^ 2 := by ring
      _ ≤ (ENNReal.ofReal (A * (CK * (5 : ℝ) ^ (d : ℝ) + V1r) * ρ ^ (d : ℝ)) * Nv) ^ 2 := by
          rw [mul_pow (ENNReal.ofReal (A * (CK * (5 : ℝ) ^ (d : ℝ) + V1r) * ρ ^ (d : ℝ))) Nv]
          exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hYle 2) (by positivity)

end HRS.MH.AdjointRd.Phase2SA12Near
