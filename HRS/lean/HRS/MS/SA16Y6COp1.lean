import HRS.MS.SA16Y4Io10
import HRS.MS.SA16Y6C1
import HRS.MS.SA16Y6Tc7
import HRS.MS.SA16Y5Op1

/-!
# S.A.16 (SA16Y6) COp1: the order-one operator at the critical exponent `s = d-1` (replaces SA16Y5Op1 `sa16y5_G_smooth`)

For smooth `a` and `φ ∈ C_c^∞`: `eucNonlocal s M a φ = ∑ M_ji (-c_s) R_i(a ∂_jφ)` (`R_i` the Riesz transform) and
`∂^idx R_i f = R_i ∂^idx f`; with the Calderón-Zygmund bound this gives `W^{m+1,p} → W^{m,p}` boundedness.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff SchwartzMap

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16Evolution Phase2SA16Transfer
open HRS.Whole.AppendixA.Phase2SA16Q HRS.MS.ToriCoefA

section COp1
variable {d : ℕ}

/-- the `(i,j)` piece `-c_s R_i(a ∂_jφ)` -/
def sa16y6c_G (d : ℕ) (i j : Fin d) (a φ : Euc d → ℝ) : Euc d → ℝ := fun x =>
  -(sa16y6_cs d) * sa16y6_R d i (fun y => a y * fderiv ℝ φ y (sa16z_e j)) x

lemma sa16y6c_cc_aD {a φ : Euc d → ℝ} (ha : ContDiff ℝ ∞ a) (hφ : IsCcInfty φ) (j : Fin d) :
    IsCcInfty (fun y => a y * fderiv ℝ φ y (sa16z_e j)) :=
  sa16y5_cc_mul ha (sa16s_cc_fderiv hφ (sa16z_e j))

lemma sa16y6c_euc_eq (hd : 1 ≤ d) {s : ℝ} (hs : s = (d : ℝ) - 1) (M : Matrix (Fin d) (Fin d) ℝ) {a φ : Euc d → ℝ}
    (ha : ContDiff ℝ ∞ a) (hφ : IsCcInfty φ) :
    HRS.MH.AdjointRd.eucNonlocal s M a φ = fun x => ∑ i, ∑ j, M j i * sa16y6c_G d i j a φ x := by
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hs0 : 0 ≤ s := by rw [hs]; linarith
  have hsd : s < d := by rw [hs]; linarith
  have hk := rieszKernel_locallyIntegrable (d := d) hs0 hsd
  have hc := HRS.CZ.Hls.hlsg_c_pos hs0
  rw [sa16y5_euc_eq]
  funext x
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  congr 1
  have hw := sa16y6c_cc_aD ha hφ j
  unfold sa16y5_S sa16y6c_G
  rw [sa16y5_cv_fderiv hk hw x, sa16y6_R_eq hd hs hw i x]
  have hcs : sa16y6_cs d = HRS.CZ.Hls.hlsg_c s := by unfold sa16y6_cs; rw [hs]
  rw [hcs]
  field_simp

lemma sa16y6c_Gij_smooth (hd : 1 ≤ d) {s : ℝ} (hs : s = (d : ℝ) - 1) {a φ : Euc d → ℝ} (ha : ContDiff ℝ ∞ a)
    (hφ : IsCcInfty φ) (i j : Fin d) : ContDiff ℝ ∞ (sa16y6c_G d i j a φ) :=
  contDiff_const.mul (sa16y6_R_contDiff hd hs (sa16y6c_cc_aD ha hφ j) i)

lemma sa16y6c_euc_smooth (hd : 1 ≤ d) {s : ℝ} (hs : s = (d : ℝ) - 1) (M : Matrix (Fin d) (Fin d) ℝ)
    {a φ : Euc d → ℝ} (ha : ContDiff ℝ ∞ a) (hφ : IsCcInfty φ) :
    ContDiff ℝ ∞ (HRS.MH.AdjointRd.eucNonlocal s M a φ) := by
  rw [sa16y6c_euc_eq hd hs M ha hφ]
  exact ContDiff.sum fun i _ => ContDiff.sum fun j _ => contDiff_const.mul (sa16y6c_Gij_smooth hd hs ha hφ i j)

lemma sa16y6c_euc_add_phi (hd : 1 ≤ d) {s : ℝ} (hs : s = (d : ℝ) - 1) (M : Matrix (Fin d) (Fin d) ℝ)
    {a : Euc d → ℝ} (ha : ContDiff ℝ ∞ a) {φ ψ : Euc d → ℝ} (hφ : IsCcInfty φ) (hψ : IsCcInfty ψ) :
    HRS.MH.AdjointRd.eucNonlocal s M a (fun y => φ y + ψ y) =
      fun x => HRS.MH.AdjointRd.eucNonlocal s M a φ x + HRS.MH.AdjointRd.eucNonlocal s M a ψ x := by
  have hφψ : IsCcInfty (fun y => φ y + ψ y) := ⟨hφ.1.add hψ.1, hφ.2.add hψ.2⟩
  rw [sa16y6c_euc_eq hd hs M ha hφψ, sa16y6c_euc_eq hd hs M ha hφ, sa16y6c_euc_eq hd hs M ha hψ]
  funext x
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← mul_add]
  congr 1
  unfold sa16y6c_G
  have e : (fun y => a y * fderiv ℝ (fun z => φ z + ψ z) y (sa16z_e j)) =
      fun y => a y * fderiv ℝ φ y (sa16z_e j) + a y * fderiv ℝ ψ y (sa16z_e j) := by
    funext y
    have h := congrFun (sa16y6_D_add hφ hψ (sa16z_e j)) y
    rw [h]; ring
  rw [e, sa16y6_R_add hd hs (sa16y6c_cc_aD ha hφ j) (sa16y6c_cc_aD ha hψ j) i x]
  ring

lemma sa16y6c_euc_smul_phi (hd : 1 ≤ d) {s : ℝ} (hs : s = (d : ℝ) - 1) (M : Matrix (Fin d) (Fin d) ℝ)
    {a : Euc d → ℝ} (ha : ContDiff ℝ ∞ a) {φ : Euc d → ℝ} (hφ : IsCcInfty φ) (c : ℝ) :
    HRS.MH.AdjointRd.eucNonlocal s M a (fun y => c * φ y) =
      fun x => c * HRS.MH.AdjointRd.eucNonlocal s M a φ x := by
  have hcφ : IsCcInfty (fun y => c * φ y) := ⟨contDiff_const.mul hφ.1, hφ.2.mul_left⟩
  rw [sa16y6c_euc_eq hd hs M ha hcφ, sa16y6c_euc_eq hd hs M ha hφ]
  funext x
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  unfold sa16y6c_G
  have e : (fun y => a y * fderiv ℝ (fun z => c * φ z) y (sa16z_e j)) =
      fun y => c * (a y * fderiv ℝ φ y (sa16z_e j)) := by
    funext y
    have hfd : DifferentiableAt ℝ φ y := (hφ.1.differentiable (by simp)) y
    have h : HasFDerivAt (fun w => c * φ w) (c • fderiv ℝ φ y) y := hfd.hasFDerivAt.const_mul c
    rw [h.fderiv]; simp; ring
  rw [e, sa16y6_R_smul hd hs (sa16y6c_cc_aD ha hφ j) c i x]
  ring

theorem sa16y6c_euc_jet (hd : 1 ≤ d) {s : ℝ} (hs : s = (d : ℝ) - 1) (k : ℕ) {p : ℝ} (hp : 2 ≤ p) (MB W : ℝ)
    (hMB : 0 ≤ MB) (hW : 0 ≤ W) :
    ∃ c0 : ℝ, 0 ≤ c0 ∧ ∀ (M : Matrix (Fin d) (Fin d) ℝ), (∀ i j, |M i j| ≤ MB) → ∀ {a : Euc d → ℝ},
      ContDiff ℝ ∞ a → (∀ κ ≤ k, ∀ x, ‖iteratedFDeriv ℝ κ a x‖ ≤ W) → ∀ (φ : ccSub d) {l : ℕ}, l + 1 ≤ k →
      ∀ idx : Fin l → Fin d,
        eLpNorm (partialDeriv idx (HRS.MH.AdjointRd.eucNonlocal s M a φ.1)) (ENNReal.ofReal p) volume ≤
          ENNReal.ofReal c0 * eLpNorm (wJet k φ.1) (ENNReal.ofReal p) volume := by
  have hp1 : (1 : ℝ) ≤ p := by linarith
  have hp' : 1 ≤ ENNReal.ofReal p := ENNReal.one_le_ofReal.2 hp1
  choose CR hCR0 hCR using fun i : Fin d => sa16y6_R_Lp hd hp i
  set CRm : ℝ := ∑ i, CR i with hCRm
  have hCRm0 : 0 ≤ CRm := Finset.sum_nonneg fun i _ => hCR0 i
  have hCRle : ∀ i, CR i ≤ CRm := fun i => Finset.single_le_sum (f := CR) (fun i _ => hCR0 i) (Finset.mem_univ i)
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hs0 : 0 ≤ s := by rw [hs]; linarith
  have hcs : 0 ≤ sa16y6_cs d := by
    unfold sa16y6_cs; exact (HRS.CZ.Hls.hlsg_c_pos (by linarith)).le
  set A0 : ℝ := 2 * (2 ^ k * (W * (d : ℝ) ^ k)) with hA0
  have hA00 : 0 ≤ A0 := by positivity
  refine ⟨(d : ℝ) * d * (MB * (sa16y6_cs d * (CRm * A0))), by positivity, ?_⟩
  intro M hM a ha hbd φ l hl idx
  set E := eLpNorm (wJet k φ.1) (ENNReal.ofReal p) volume with hE
  have hdm : ∀ j : Fin d, ContDiff ℝ ∞ (fun y => fderiv ℝ a y (sa16z_e j)) := fun j =>
    (ha.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  have hP : IsCcInfty (fun y => a y * φ.1 y) := sa16y5_cc_mul ha φ.2
  have hQ : ∀ j : Fin d, IsCcInfty (fun y => fderiv ℝ a y (sa16z_e j) * φ.1 y) := fun j =>
    sa16y5_cc_mul (hdm j) φ.2
  have hGs : ∀ i j, ContDiff ℝ ∞ (sa16y6c_G d i j a φ.1) := fun i j => sa16y6c_Gij_smooth hd hs ha φ.2 i j
  rw [sa16y6c_euc_eq hd hs M ha φ.2, sa16y5_pd_dsum hGs (fun i j => M j i) idx]
  refine (sa16q_eLpNorm_dsum_le _ hp').trans ?_
  have hb : ∀ i j : Fin d, eLpNorm (fun x => M j i * partialDeriv idx (sa16y6c_G d i j a φ.1) x)
      (ENNReal.ofReal p) volume ≤ ENNReal.ofReal (MB * (sa16y6_cs d * (CRm * A0))) * E := by
    intro i j
    have hf := sa16y6c_cc_aD ha φ.2 j
    have hGe : partialDeriv idx (sa16y6c_G d i j a φ.1) =
        (-(sa16y6_cs d)) • sa16y6_R d i (partialDeriv idx (fun y => a y * fderiv ℝ φ.1 y (sa16z_e j))) := by
      funext x
      have e : sa16y6c_G d i j a φ.1 = fun x => (-(sa16y6_cs d)) *
          sa16y6_R d i (fun y => a y * fderiv ℝ φ.1 y (sa16z_e j)) x := rfl
      rw [e, sa16q_pd_smul (sa16y6_R_contDiff hd hs hf i) _ idx x,
        congrFun (sa16y6_R_pd hd hs hf i l idx) x]
      simp
    have e1 : (fun x => M j i * partialDeriv idx (sa16y6c_G d i j a φ.1) x) =
        (M j i * (-(sa16y6_cs d))) • sa16y6_R d i (partialDeriv idx (fun y => a y * fderiv ℝ φ.1 y (sa16z_e j))) := by
      funext x; rw [hGe]; simp; ring
    rw [e1, eLpNorm_const_smul]
    have hn : ‖M j i * (-(sa16y6_cs d))‖ₑ ≤ ENNReal.ofReal (MB * sa16y6_cs d) := by
      rw [Real.enorm_eq_ofReal_abs, abs_mul, abs_neg, abs_of_nonneg hcs]
      exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (hM j i) hcs)
    have hRC := hCR i _ (sa16s_cc_partialDeriv hf idx)
    -- ∂^idx (a ∂_jφ) = ∂_j ∂^idx (aφ) - ∂^idx ((∂_j a) φ)
    have hf_eq : (fun y => a y * fderiv ℝ φ.1 y (sa16z_e j)) = fun y =>
        fderiv ℝ (fun z => a z * φ.1 z) y (sa16z_e j) + (-1) * (fderiv ℝ a y (sa16z_e j) * φ.1 y) := by
      funext y
      rw [sa16y6_D_mul ha φ.2.1 y (sa16z_e j)]
      ring
    have hDP : ContDiff ℝ ∞ (fun y => fderiv ℝ (fun z => a z * φ.1 z) y (sa16z_e j)) :=
      (hP.1.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
    have hQs : ContDiff ℝ ∞ (fun y => (-1 : ℝ) * (fderiv ℝ a y (sa16z_e j) * φ.1 y)) :=
      contDiff_const.mul (hQ j).1
    have hpd : partialDeriv idx (fun y => a y * fderiv ℝ φ.1 y (sa16z_e j)) = fun y =>
        partialDeriv (Fin.cons j idx : Fin (l + 1) → Fin d) (fun z => a z * φ.1 z) y +
          (-1) * partialDeriv idx (fun y => fderiv ℝ a y (sa16z_e j) * φ.1 y) y := by
      funext y
      rw [hf_eq, sa16sy_pd_add hDP hQs idx y, sa16q_pd_smul (hQ j).1 (-1) idx y]
      congr 1
      have := congrFun (sa16y6_pd_D hP.1 j l idx) y
      rw [this, sa16s_pd_cons hP.1 j idx y]
    have hbd1 : ∀ κ ≤ l + 1, ∀ x, ‖iteratedFDeriv ℝ κ a x‖ ≤ W := fun κ hκ x => hbd κ (by omega) x
    have hbd2 : ∀ κ ≤ l, ∀ x, ‖iteratedFDeriv ℝ κ (fun y => fderiv ℝ a y (sa16z_e j)) x‖ ≤ W :=
      fun κ hκ x => (sa16q_norm_iter_pd_le ha j κ x).trans (hbd (κ + 1) (by omega) x)
    have h3 := sa16y5_leib_lp hd ha hW hl hbd1 φ (Fin.cons j idx : Fin (l + 1) → Fin d) hp1
    have h4 := sa16y5_leib_lp hd (hdm j) hW (by omega : l ≤ k) hbd2 φ idx hp1
    have hpow : ∀ n, n ≤ k → (2 : ℝ) ^ n * (W * (d : ℝ) ^ k) ≤ 2 ^ k * (W * (d : ℝ) ^ k) := fun n hn =>
      mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hn) (by positivity)
    have h5 : eLpNorm (partialDeriv idx (fun y => a y * fderiv ℝ φ.1 y (sa16z_e j)))
        (ENNReal.ofReal p) volume ≤ ENNReal.ofReal A0 * E := by
      rw [hpd]
      have h6 := eLpNorm_add_le (μ := (volume : Measure (Euc d))) (p := ENNReal.ofReal p)
        (f := fun y => partialDeriv (Fin.cons j idx : Fin (l + 1) → Fin d) (fun z => a z * φ.1 z) y)
        (g := fun y => (-1 : ℝ) * partialDeriv idx (fun y => fderiv ℝ a y (sa16z_e j) * φ.1 y) y)
        hp'
      refine h6.trans ?_
      have h7 : eLpNorm (fun y => (-1 : ℝ) * partialDeriv idx (fun y => fderiv ℝ a y (sa16z_e j) * φ.1 y) y)
          (ENNReal.ofReal p) volume = eLpNorm (partialDeriv idx (fun y => fderiv ℝ a y (sa16z_e j) * φ.1 y))
          (ENNReal.ofReal p) volume := by
        have : (fun y => (-1 : ℝ) * partialDeriv idx (fun y => fderiv ℝ a y (sa16z_e j) * φ.1 y) y) =
            (-1 : ℝ) • partialDeriv idx (fun y => fderiv ℝ a y (sa16z_e j) * φ.1 y) := by funext y; simp
        rw [this, eLpNorm_const_smul]; simp
      rw [h7]
      have h3' := h3.trans (mul_le_mul' (ENNReal.ofReal_le_ofReal (hpow (l + 1) hl)) le_rfl)
      have h4' := h4.trans (mul_le_mul' (ENNReal.ofReal_le_ofReal (hpow l (by omega))) le_rfl)
      calc _ ≤ ENNReal.ofReal (2 ^ k * (W * (d : ℝ) ^ k)) * E + ENNReal.ofReal (2 ^ k * (W * (d : ℝ) ^ k)) * E :=
            add_le_add h3' h4'
        _ = _ := by
          rw [← two_mul, hA0, ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat, mul_assoc]
    calc ‖M j i * (-(sa16y6_cs d))‖ₑ * eLpNorm (sa16y6_R d i (partialDeriv idx
          (fun y => a y * fderiv ℝ φ.1 y (sa16z_e j)))) (ENNReal.ofReal p) volume
        ≤ ENNReal.ofReal (MB * sa16y6_cs d) * (ENNReal.ofReal CRm *
            (ENNReal.ofReal A0 * E)) :=
          mul_le_mul' hn (hRC.trans (mul_le_mul' (ENNReal.ofReal_le_ofReal (hCRle i)) h5))
      _ = ENNReal.ofReal (MB * (sa16y6_cs d * (CRm * A0))) * E := by
          have e5 : ENNReal.ofReal (MB * (sa16y6_cs d * (CRm * A0))) =
              ENNReal.ofReal (MB * sa16y6_cs d) * (ENNReal.ofReal CRm * ENNReal.ofReal A0) := by
            rw [show MB * (sa16y6_cs d * (CRm * A0)) = (MB * sa16y6_cs d) * (CRm * A0) by ring,
              ENNReal.ofReal_mul (mul_nonneg hMB hcs), ENNReal.ofReal_mul hCRm0]
          rw [e5]; ring
  calc ∑ i : Fin d, ∑ j : Fin d, eLpNorm (fun x => M j i * partialDeriv idx (sa16y6c_G d i j a φ.1) x)
        (ENNReal.ofReal p) volume
      ≤ ∑ i : Fin d, ∑ j : Fin d, ENNReal.ofReal (MB * (sa16y6_cs d * (CRm * A0))) * E :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hb i j
    _ = (d : ℝ≥0∞) * ((d : ℝ≥0∞) * (ENNReal.ofReal (MB * (sa16y6_cs d * (CRm * A0))) * E)) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        congr 1
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    _ = ENNReal.ofReal ((d : ℝ) * d * (MB * (sa16y6_cs d * (CRm * A0)))) * E := by
        have hB0 : 0 ≤ MB * (sa16y6_cs d * (CRm * A0)) := by positivity
        rw [ENNReal.ofReal_mul (show (0 : ℝ) ≤ (d : ℝ) * d by positivity), ENNReal.ofReal_mul (Nat.cast_nonneg _),
          ENNReal.ofReal_natCast]
        ring

theorem sa16y6c_G_smooth (d m : ℕ) (hd : 1 ≤ d) (s p MB W : ℝ) [Fact (2 ≤ p)] (hs0 : 0 ≤ s)
    (hs1 : s = (d : ℝ) - 1) (hfar : (d : ℝ) < p * (s + 1)) (hW : 0 ≤ W) :
    ∃ C : ℝ, 0 < C ∧ ∀ M : Matrix (Fin d) (Fin d) ℝ, (∀ i j, |M i j| ≤ MB) → ∀ a : Euc d → ℝ, sa16q_SB a →
      (∀ κ ≤ m + 2, ∀ x, ‖iteratedFDeriv ℝ κ a x‖ ≤ W * (1 + ‖x‖) ^ (-((d + 3 : ℕ) : ℝ))) →
        ∃ T : WmpSpace d (m + 1) p →L[ℝ] WmpSpace d m p, ‖T‖ ≤ C ∧ ∀ φ : ccSub d,
          wrep d m p (T (sa16r_Jcc d (m + 1) p φ)) =ᵐ[volume]
            HRS.MH.AdjointRd.eucNonlocal s M a φ.1 := by
  have hp2 : 2 ≤ p := Fact.out
  obtain ⟨c0, hc0, hc⟩ := sa16y6c_euc_jet hd hs1 (m + 1) hp2 (max MB 0) W (le_max_right _ _) hW
  refine ⟨(Fintype.card (WIndex d m) : ℝ) * c0 + 1, by positivity, fun M hM a ha hdec => ?_⟩
  have haS : ContDiff ℝ ∞ a := ha.1
  have hM' : ∀ i j, |M i j| ≤ max MB 0 := fun i j => (hM i j).trans (le_max_left _ _)
  have hbd : ∀ κ ≤ m + 1, ∀ x, ‖iteratedFDeriv ℝ κ a x‖ ≤ W := by
    intro κ hκ x
    refine (hdec κ (by omega) x).trans ?_
    have h1 : (1 + ‖x‖) ^ (-((d + 3 : ℕ) : ℝ)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by linarith [norm_nonneg x]) (neg_nonpos.2 (Nat.cast_nonneg _))
    nlinarith
  obtain ⟨T, hT, hTφ⟩ := sa16y5_ext_of_fun d (m + 1) m p (fun φ => HRS.MH.AdjointRd.eucNonlocal s M a φ.1)
    (fun φ ψ => sa16y6c_euc_add_phi hd hs1 M haS φ.2 ψ.2)
    (fun c φ => sa16y6c_euc_smul_phi hd hs1 M haS φ.2 c)
    (fun φ => sa16y6c_euc_smooth hd hs1 M haS φ.2) (c0 := c0) hc0
    (fun φ {j} hj idx => hc M hM' haS hbd φ (by omega) idx)
  exact ⟨T, hT.trans (by linarith), hTφ⟩

end COp1

end HRS.Whole.AppendixA.Phase2SA16R
