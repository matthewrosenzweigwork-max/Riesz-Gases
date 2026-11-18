import HRS.MS.S82WR4
import HRS.MS.S82WP4
import HRS.MS.S82WA04
import HRS.MS.S82P2R05
import HRS.MS.S82TFinal
import HRS.MS.S82QR07
import HRS.MS.S82UA01
import HRS.MS.S82VA2

/-!
# S8.2 A05 (S82W), part 12: `normal_form_bound` (frozen statement)
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S82W
open HRS HRS.Whole HRS.MS.Phase2S82

lemma w_mu_prob {d : ℕ} (hd : 2 ≤ d) {a beta : ℝ} (ha : 0 < a) (hbeta : 0 < beta) {rho : Euc d → ℝ}
    (hrho : IsThermalEquilibrium d (criticalS d) a beta rho) :
    IsProbabilityMeasure (HRS.Whole.withDensityReal rho) := by
  have hrho_eq := critical_thermal_eq d hd a beta ha hbeta hrho
  have hs0 : 0 ≤ criticalS d := by unfold criticalS; positivity
  have hsd : criticalS d < d := by
    unfold criticalS
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  obtain ⟨Cth, cth, BU, hT⟩ := _root_.S45.s45_thermal_data hd hs0 hsd ha hbeta
  rw [hrho_eq]
  exact HRS.Whole.Q09A.measure_isProb hT.prob

end HRS.MS.S82W

namespace HRS.MS.Phase2S82
open HRS HRS.Whole

theorem normal_form_bound (d : ℕ) (hd : 2 ≤ d)
    (a beta M C0 C1 : ℝ) (ha : 0 < a) (hbeta : 0 < beta) (hM : 0 ≤ M)
    (q : Euc d → ℝ) (hq : ShortRangePole d q) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ rho : Euc d → ℝ,
      IsThermalEquilibrium d (criticalS d) a beta rho →
      ∀ h : ℕ → Euc d → ℝ,
      WeakReferenceSetup d a beta rho q h C0 → PinComparison beta rho q h C1 →
      ∀ Psi : (Euc d → ℝ) → Euc d → Euc d → ℝ,
      ∀ f : Euc d → ℝ, ∀ A B : ℝ, 0 ≤ A → 0 ≤ B →
      TestBound (testOrder d) A f →
      PairCorrector a beta rho M B f (Psi f) →
      MemLp (aSource (HRS.Whole.withDensityReal rho) f) 2 (HRS.Whole.withDensityReal rho) →
      eLpNorm (aSource (HRS.Whole.withDensityReal rho) f) 2 (HRS.Whole.withDensityReal rho) ≤ ENNReal.ofReal B →
      ∀ N : ℕ, 2 ≤ N →
        GeneratorClosure a beta (correctedQ (N := N) a beta Psi f)
          (fun X => -scalarForcing a beta rho f X + correctedD a beta rho Psi f X) ∧
        MemLp (correctedD (N := N) a beta rho Psi f) 2 (canonicalP d N a beta) ∧
        (∀ X : EucConfig d N, X ∉ eucCollisionSet d N →
          scalarForcing a beta rho f X =
            -particleGenerator (quadraticGradientDyn d (criticalS d) a beta)
              (correctedQ a beta Psi f) X + correctedD a beta rho Psi f X) ∧
        eLpNorm (correctedQ (N := N) a beta Psi f) 2 (canonicalP d N a beta) +
          (∫⁻ X, ∑ i, ‖configGrad (correctedQ a beta Psi f) X i‖ₑ ^ 2
            ∂canonicalP d N a beta) ^ (1 / 2 : ℝ) +
          eLpNorm (correctedD (N := N) a beta rho Psi f) 2 (canonicalP d N a beta) ≤
            ENNReal.ofReal (C * (A + B) * (N : ℝ) ^ (-(1 / 2 : ℝ))) := by
  obtain ⟨C5, hC5, H5⟩ := weighted_pair_moments d hd a beta M C0 C1 ha hbeta hM q hq
  obtain ⟨C6, hC6, H6⟩ := weighted_repeated_pair_moments d hd a beta M C0 C1 ha hbeta hM q hq
  obtain ⟨CA, M', hCA, hM', H1⟩ := canonical_triple_and_bounds d hd a beta M ha hbeta hM
  obtain ⟨C7, hC7, H7⟩ := weighted_triple_moments d hd a beta M' C0 C1 ha hbeta hM' q hq
  refine ⟨2 * Real.sqrt C5 + 3 * Real.sqrt C6 + 2 * Real.sqrt C7 * CA + 2 * Real.sqrt (C0 * C0),
    by positivity, ?_⟩
  intro rho hrho h hW hP Psi f A B hA hB hTB hQ hLm hLb N hN
  haveI hμ : IsProbabilityMeasure (HRS.Whole.withDensityReal rho) := HRS.MS.S82W.w_mu_prob hd ha hbeta hrho
  haveI hPp : IsProbabilityMeasure (canonicalP d N a beta) := HRS.MS.S82U.u4_prob (N := N) hd ha hbeta
  have hN0 : 0 < N := by omega
  obtain ⟨hps, hgr, hv5⟩ := H5 rho hrho h hW hP f B hB (Psi f) hQ N hN
  obtain ⟨hJ, hBm, hvJ, hvB⟩ := H6 rho hrho h hW hP f B hB (Psi f) hQ N hN
  obtain ⟨G, hGm, hGc, hGb, hBb⟩ := H1 rho hrho f B hB (Psi f) hQ
  obtain ⟨hT, hvT⟩ := H7 rho hrho h hW hP G (CA * B) (mul_nonneg hCA hB) hGm hGc
    (fun x y z hxy hxz hyz => hGb x y z hxy hxz hyz |>.2) N hN
  set P := canonicalP d N a beta with hPdef
  set μ := HRS.Whole.withDensityReal rho with hμdef
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN0
  have hsq : 0 < Real.sqrt N := Real.sqrt_pos.2 hNpos
  have hss : Real.sqrt N * Real.sqrt N = N := Real.mul_self_sqrt hNpos.le
  -- marginal domination
  have hmarg : ∀ i : Fin N, P.map (fun X => X i) ≤ ENNReal.ofReal (C0 * C0) • μ := by
    intro i
    have := HRS.MS.S82W.w_marg_dom hW hbeta hN i
    rwa [smul_smul, ← ENNReal.ofReal_mul hW.positive.le] at this
  -- the triple model agrees off collisions
  have hGeq : ∀ X : EucConfig d N, X ∉ eucCollisionSet d N →
      tripleSum G X = tripleSum (tripleG (critCoeff d a beta rho) rho (Psi f)) X := by
    intro X hX
    unfold Phase2S82.tripleSum
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j hj => Finset.sum_congr rfl fun k hk => ?_
    have hij : i ≠ j := (Finset.ne_of_mem_erase hj).symm
    have hkj : k ≠ j := Finset.ne_of_mem_erase hk
    have hki : k ≠ i := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hk)
    exact (hGb (X i) (X j) (X k) (fun h => hX ⟨i, j, hij, h⟩) (fun h => hX ⟨i, k, hki.symm, h⟩)
      (fun h => hX ⟨j, k, hkj.symm, h⟩)).1
  -- error statistic
  obtain ⟨hErrM, hErrC⟩ := HRS.MS.S82W.w_err_center (N := N) hN (G := G) hd hJ hBm hT hGeq hC6 hC7 hCA hB hvJ hvB hvT
  -- the linear correction
  set aS := aSource μ f with haS
  set K : ℝ := C0 * C0 with hK
  have hK0 : 0 ≤ K := mul_self_nonneg C0
  have hz1 := HRS.MS.S82W.w_zeta_L2 (a := a) (beta := beta) (N := N) hN0 hK0 hmarg hLm
  have hz2 : eLpNorm (fun X : EucConfig d N => (1 / (N : ℝ)) * ∑ i, aS (X i)) 2 P ≤
      ENNReal.ofReal (Real.sqrt K * B) := by
    refine hz1.trans ?_
    rw [ENNReal.ofReal_mul (Real.sqrt_nonneg _)]
    exact mul_le_mul' le_rfl hLb
  set Gz : EucConfig d N → ℝ := fun X => (1 / (N : ℝ)) * ∑ i, aS (X i) with hGz
  have hGzm : MemLp Gz 2 P := lt_of_le_of_lt hz2 ENNReal.ofReal_lt_top
  have hζ : eLpNorm (zetaActual (N := N) a beta aS) 2 P ≤ ENNReal.ofReal (Real.sqrt N * (Real.sqrt K * B)) := by
    have e : zetaActual (N := N) a beta aS = (Real.sqrt N) • centerUnder P Gz := by
      funext X; rfl
    rw [e, eLpNorm_const_smul, Real.enorm_eq_ofReal (Real.sqrt_nonneg _), ENNReal.ofReal_mul (Real.sqrt_nonneg _)]
    exact mul_le_mul' le_rfl ((HRS.MS.S82W.w_center_L2 hGzm.aestronglyMeasurable).trans hz2)
  have hζm : MemLp (zetaActual (N := N) a beta aS) 2 P := lt_of_le_of_lt hζ ENNReal.ofReal_lt_top
  have hSint : Integrable (fun Y : EucConfig d N => ∑ i, aS (Y i)) P := by
    have := (hGzm.integrable (by norm_num)).const_mul (N : ℝ)
    refine this.congr (Eventually.of_forall fun Y => ?_)
    simp only [hGz]
    field_simp
  -- the corrected error D
  have hDe : correctedD (N := N) a beta rho Psi f = fun X =>
      centerUnder P (errorStatistic (critCoeff d a beta rho) rho (Psi f)) X +
        (-(2 / (N : ℝ))) * zetaActual (N := N) a beta aS X := by
    funext X; unfold correctedD; ring
  have hDn : eLpNorm (correctedD (N := N) a beta rho Psi f) 2 P ≤
      ENNReal.ofReal (((3 * Real.sqrt C6 + 2 * Real.sqrt C7 * CA) * B) / Real.sqrt N) +
        ENNReal.ofReal (2 * Real.sqrt K * B / Real.sqrt N) := by
    have e : correctedD (N := N) a beta rho Psi f =
        (centerUnder P (errorStatistic (critCoeff d a beta rho) rho (Psi f))) +
          (-(2 / (N : ℝ))) • zetaActual (N := N) a beta aS := by
      rw [hDe]; funext X; simp
    rw [e]
    refine (eLpNorm_add_le (by norm_num)).trans (add_le_add hErrC ?_)
    rw [eLpNorm_const_smul, Real.enorm_eq_ofReal_abs, abs_neg, abs_of_nonneg (by positivity)]
    refine (mul_le_mul' le_rfl hζ).trans (le_of_eq ?_)
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    generalize Real.sqrt N = r at hss hsq ⊢
    rw [← hss]; field_simp
  have hDm : MemLp (correctedD (N := N) a beta rho Psi f) 2 P :=
    lt_of_le_of_lt hDn (ENNReal.add_lt_top.2 ⟨ENNReal.ofReal_lt_top, ENNReal.ofReal_lt_top⟩)
  -- the envelope of the corrected pair statistic and graph closure (A04)
  set c1 : ℝ := ∫ Y, pairStatistic (Psi f) Y ∂P with hc1
  obtain ⟨hFcd, A', M'', hA', hM'', hbF⟩ := HRS.MS.S82W.w_pairstat_env (N := N) hd hM hQ hB c1
  have hcQ : correctedQ (N := N) a beta Psi f = fun X => pairStatistic (Psi f) X - c1 := rfl
  have hFcd0 : ContDiffOn ℝ 2 (fun X : EucConfig d N => pairStatistic (Psi f) X) (eucCollisionSet d N)ᶜ := by
    have := hFcd.add (contDiffOn_const (c := c1))
    simpa using this
  obtain ⟨hclos, hmean⟩ := gibbs_graph_closure d N hd hN a beta ha hbeta (correctedQ (N := N) a beta Psi f)
    (by rw [hcQ]; exact hFcd) M'' A' hM'' hA' (fun X hX => hbF X hX)
  have hLmem := hclos.2.1
  have hA02 := HRS.MS.S82V.s82v_lifted_pair_generator d N hd hN a beta M B ha hbeta rho hrho f (Psi f) hQ
  have hident := HRS.MS.S82W.w_forcing_identity hd hN hFcd0 hA02 (hErrM.integrable (by norm_num)) hLmem hmean hSint
  have hae0 : ∀ᵐ X ∂P, X ∉ eucCollisionSet d N := by
    rw [ae_iff]; simpa using HRS.MS.S82U.u4_P_coll hd N a beta
  have hclos' : GeneratorClosure a beta (correctedQ (N := N) a beta Psi f)
      (fun X => -scalarForcing a beta rho f X + correctedD a beta rho Psi f X) := by
    refine HRS.MS.S82W.w_closure_congr hclos ?_
    filter_upwards [hae0] with X hX
    rw [hident X hX]; ring
  -- norm bounds of the pair part
  have hV5 : 0 ≤ C5 * B ^ 2 / N := by positivity
  have hv5a : evariance (pairStatistic (N := N) (Psi f)) P ≤ ENNReal.ofReal (C5 * B ^ 2 / N) :=
    le_self_add.trans hv5
  have hv5b : (∫⁻ X, ∑ i, ‖configGrad (pairStatistic (Psi f)) X i‖ₑ ^ 2 ∂P) ≤ ENNReal.ofReal (C5 * B ^ 2 / N) :=
    le_add_self.trans hv5
  have hsq5 : Real.sqrt (C5 * B ^ 2 / N) = Real.sqrt C5 * B / Real.sqrt N := by
    rw [Real.sqrt_div' _ hNpos.le, Real.sqrt_mul hC5, Real.sqrt_sq hB]
  have hq1 : eLpNorm (correctedQ (N := N) a beta Psi f) 2 P ≤ ENNReal.ofReal (Real.sqrt C5 * B / Real.sqrt N) := by
    have := HRS.MS.S82W.w_center_sqrt hps.aestronglyMeasurable hV5 hv5a
    rwa [hsq5] at this
  have hq2 : (∫⁻ X, ∑ i, ‖configGrad (correctedQ (N := N) a beta Psi f) X i‖ₑ ^ 2 ∂P) ^ (1 / 2 : ℝ) ≤
      ENNReal.ofReal (Real.sqrt C5 * B / Real.sqrt N) := by
    have e : (fun X : EucConfig d N => ∑ i, ‖configGrad (correctedQ (N := N) a beta Psi f) X i‖ₑ ^ 2) =
        fun X => ∑ i, ‖configGrad (pairStatistic (Psi f)) X i‖ₑ ^ 2 := by
      funext X
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hcQ]
      exact congrArg (fun v => ‖v‖ₑ ^ 2) (HRS.MS.S82W.w_configGrad_shift _ c1 X i)
    rw [e]
    refine (ENNReal.rpow_le_rpow hv5b (by norm_num)).trans ?_
    rw [ENNReal.ofReal_rpow_of_nonneg hV5 (by norm_num), ← Real.sqrt_eq_rpow, hsq5]
  refine ⟨hclos', hDm, hident, ?_⟩
  refine (add_le_add (add_le_add hq1 hq2) hDn).trans ?_
  rw [← ENNReal.ofReal_add (by positivity) (by positivity), ← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  have hnn : (N : ℝ) ^ (-(1 / 2 : ℝ)) = 1 / Real.sqrt N := by
    rw [Real.rpow_neg hNpos.le, Real.sqrt_eq_rpow]; simp
  rw [hnn]
  have hKs : Real.sqrt (C0 * C0) = Real.sqrt K := rfl
  have hc0 : 0 ≤ 2 * Real.sqrt C5 + 3 * Real.sqrt C6 + 2 * Real.sqrt C7 * CA + 2 * Real.sqrt (C0 * C0) := by positivity
  have hid : Real.sqrt C5 * B / Real.sqrt N + Real.sqrt C5 * B / Real.sqrt N +
      ((3 * Real.sqrt C6 + 2 * Real.sqrt C7 * CA) * B / Real.sqrt N + 2 * Real.sqrt K * B / Real.sqrt N) =
      (2 * Real.sqrt C5 + 3 * Real.sqrt C6 + 2 * Real.sqrt C7 * CA + 2 * Real.sqrt K) * B / Real.sqrt N := by ring
  rw [hid, ← hKs]
  rw [mul_one_div]
  refine div_le_div_of_nonneg_right ?_ hsq.le
  exact mul_le_mul_of_nonneg_left (by linarith) hc0

end HRS.MS.Phase2S82
