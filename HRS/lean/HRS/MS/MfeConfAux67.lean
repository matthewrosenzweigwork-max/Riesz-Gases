import HRS.MS.MfeConfAux66

/-!
# S.B.1, packet F6 (part 28): the tilt data of a one-body tilt

`sb1_tilt_onebody`: reduces the fields of `Sb1Tilt` for `Ψ_s(Z) = ∑_i ψ_s(Z_i) + κ_s`, `w_s = sb1wOne u_s`,
`Wψ_s(Z) = ∑_i ∂_sψ_s(Z_i) + κ'_s` to one-body hypotheses on `ψ, u, ∂_sψ, κ, κ'` (continuity, `∇ψ_s = -u_s`, `u_s ∈ C¹`,
continuity of `div u`, the `s`-derivatives, one-body growth bounds with time-integrable constants) and the growth bound of
the source.
-/

open MeasureTheory Filter Topology InformationTheory
open HRS HRS.Whole HRS.MP.SelfSimP4 HRS.MP.SelfSimP4Mol HRS.MP.SelfSimP4Impl
open scoped ENNReal NNReal BigOperators ContDiff

noncomputable section

namespace HRS.MS.MfeConf

variable {d N : ℕ}

theorem sb1_tilt_onebody {θ T : ℝ} {b : ℝ → EucConfig d N → EucConfig d N} (hN : 1 ≤ N)
    {ψ wψ1 : ℝ → Euc d → ℝ} {u : ℝ → Euc d → Euc d} {κ κ' : ℝ → ℝ}
    (hψc : Continuous (Function.uncurry ψ)) (hκc : Continuous κ)
    (hψg : ∀ s x, HasFDerivAt (ψ s) (innerSL ℝ (-(u s x))) x)
    (huc : Continuous (Function.uncurry u)) (hu1 : ∀ s, ContDiff ℝ 1 (u s))
    (hdivc : Continuous (Function.uncurry fun s x => sb1divE (u s) x))
    (hwc : Continuous (Function.uncurry wψ1)) (hκ'c : Continuous κ')
    (hψd : ∀ s ∈ Set.Ioo (0 : ℝ) T, ∀ x, HasDerivAt (fun r => ψ r x) (wψ1 s x) s)
    (hκd : ∀ s ∈ Set.Ioo (0 : ℝ) T, HasDerivAt κ (κ' s) s)
    {Cψ Ck B1 K1 CS : ℝ → ℝ} (hCψ : ∀ s, 0 ≤ Cψ s) (hCk : ∀ s, 0 ≤ Ck s) (hB1 : ∀ s, 0 ≤ B1 s)
    (hK1 : ∀ s, 0 ≤ K1 s) (hCS : ∀ s, 0 ≤ CS s)
    (hψb : ∀ s x, |ψ s x| ≤ Cψ s * (1 + ‖x‖ ^ 2)) (hκb : ∀ s, |κ s| ≤ Ck s)
    (hub : ∀ s x, ‖u s x‖ ≤ B1 s + K1 s * ‖x‖)
    (hSg : ∀ r (x : EucConfig d N), |sb1S θ b (fun r => sb1wOne (u r))
      (fun s Z => ∑ i, wψ1 s (Z i) + κ' s) r x| ≤ CS r * (1 + p4m_q x))
    (iCψ : IntegrableOn Cψ (Set.Icc 0 T)) (iCk : IntegrableOn Ck (Set.Icc 0 T))
    (iB1 : IntegrableOn B1 (Set.Icc 0 T)) (iK1 : IntegrableOn K1 (Set.Icc 0 T))
    (iCS : IntegrableOn CS (Set.Icc 0 T)) :
    Sb1Tilt θ T b (fun r => sb1wOne (u r)) (fun s Z => ∑ i, ψ s (Z i) + κ s)
      (fun s Z => ∑ i, wψ1 s (Z i) + κ' s) (fun s => N * Cψ s + Ck s) B1 K1 CS where
  Ψc := by
    show Continuous fun p : ℝ × EucConfig d N => ∑ i, ψ p.1 (p.2 i) + κ p.1
    exact (continuous_finset_sum _ fun i _ => hψc.comp (continuous_fst.prodMk
      ((continuous_apply i).comp continuous_snd))).add (hκc.comp continuous_fst)
  Ψgrad := fun r x => sb1_hasFDerivAt_onebody (hψg r) (κ r) x
  wc := by
    show Continuous fun p : ℝ × EucConfig d N => sb1wOne (u p.1) p.2
    exact continuous_pi fun i => (huc.comp (continuous_fst.prodMk
      ((continuous_apply i).comp continuous_snd))).neg
  w1 := fun r => contDiff_pi.2 fun i => ((hu1 r).comp (contDiff_apply ℝ _ i)).neg
  dwc := by
    show Continuous fun p : ℝ × EucConfig d N => sb1div (sb1wOne (u p.1)) p.2
    have : (fun p : ℝ × EucConfig d N => sb1div (sb1wOne (u p.1)) p.2) =
        fun p => -∑ i, sb1divE (u p.1) (p.2 i) := funext fun p => sb1_div_one (hu1 p.1) p.2
    rw [this]
    exact (continuous_finset_sum _ fun i _ => hdivc.comp (continuous_fst.prodMk
      ((continuous_apply i).comp continuous_snd))).neg
  Wc := by
    show Continuous fun p : ℝ × EucConfig d N => ∑ i, wψ1 p.1 (p.2 i) + κ' p.1
    exact (continuous_finset_sum _ fun i _ => hwc.comp (continuous_fst.prodMk
      ((continuous_apply i).comp continuous_snd))).add (hκ'c.comp continuous_fst)
  Wd := fun r hr Z => (HasDerivAt.fun_sum fun i _ => hψd r hr (Z i)).add (hκd r hr)
  nn := fun r => ⟨by have := hCψ r; have := hCk r; positivity, hB1 r, hK1 r, hCS r⟩
  Ψg := fun r Z => by
    have hq : ∑ i, ‖Z i‖ ^ 2 = p4m_q Z := rfl
    calc |∑ i, ψ r (Z i) + κ r| ≤ |∑ i, ψ r (Z i)| + |κ r| := abs_add_le _ _
      _ ≤ ∑ i, |ψ r (Z i)| + Ck r := add_le_add (Finset.abs_sum_le_sum_abs _ _) (hκb r)
      _ ≤ ∑ i, Cψ r * (1 + ‖Z i‖ ^ 2) + Ck r := add_le_add (Finset.sum_le_sum fun i _ => hψb r (Z i)) le_rfl
      _ = N * Cψ r + Cψ r * p4m_q Z + Ck r := by
          rw [← hq]
          simp only [mul_add, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
            nsmul_eq_mul, mul_one, ← Finset.mul_sum]
      _ ≤ (N * Cψ r + Ck r) * (1 + p4m_q Z) := by
          have h1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
          have h2 := hCψ r
          have h3 := hCk r
          have h4 := p4m_q_nonneg Z
          nlinarith [mul_nonneg h2 h4, mul_nonneg h3 h4, mul_le_mul_of_nonneg_left h1 (mul_nonneg h2 h4)]
  wg := fun r Z => by
    have hK := hK1 r
    have hB := hB1 r
    refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
    simp only [sb1wOne, norm_neg]
    calc ‖u r (Z i)‖ ≤ B1 r + K1 r * ‖Z i‖ := hub r (Z i)
      _ ≤ B1 r + K1 r * ‖Z‖ := by gcongr; exact norm_le_pi_norm Z i
  Sg := hSg
  intΨ := (iCψ.const_mul (N : ℝ)).add iCk
  intB := iB1
  intK := iK1
  intS := iCS

end HRS.MS.MfeConf
