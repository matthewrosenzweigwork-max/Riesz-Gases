import HRS.Commutator.Whole.ExternalAuxMult3
import HRS.Commutator.Whole.LocalAuxKR2

/-!
# CMX-KR auxiliary (3): decay of `∇g_{>1}`

`cmxMY_ghi_ae`: componentwise, `(∇g_{>1})_i = c K_i` almost everywhere, where `K_i` is the kernel of the
homogeneous symbol `(1-χ) ξ_i |ξ|^{-(d-s)}` (`cmxMY_LP_homog`); `cmxMY_ghi_far`: `|∇g_{>1}(x)| ≤ C_m |x|^{-m}`
for `|x| ≥ 1` (a.e. bound upgraded by continuity).  Names prefixed `cmxMY_`.
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators FourierTransform ContDiff

namespace HRS.Commutator.Whole

open HRS HRS.Whole

variable {d : ℕ}

/-- the homogeneous symbol `ξ_i |ξ|^{-(d-s)}` -/
def cmxMY_hi (d : ℕ) (s : ℝ) (i : Fin d) (η : Euc d) : ℂ := (((η i) * ‖η‖ ^ (-((d : ℝ) - s)) : ℝ) : ℂ)

lemma cmxMY_hi_smooth (s : ℝ) (i : Fin d) (η : Euc d) (hη : η ≠ 0) :
    ContDiffAt ℝ ∞ (cmxMY_hi d s i) η := by
  unfold cmxMY_hi
  refine Complex.ofRealCLM.contDiff.contDiffAt.comp η ?_
  exact ((EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).contDiff.contDiffAt).mul
    ((contDiffAt_norm ℝ hη).rpow_const_of_ne (norm_ne_zero_iff.2 hη))

lemma cmxMY_hi_hom (s : ℝ) (i : Fin d) (t : ℝ) (η : Euc d) (ht : 0 < t) :
    cmxMY_hi d s i (t • η) = ((t ^ (-(((d : ℝ) - s) - 1)) : ℝ)) • cmxMY_hi d s i η := by
  unfold cmxMY_hi
  rw [Complex.real_smul, ← Complex.ofReal_mul]
  congr 1
  rw [norm_smul, Real.norm_of_nonneg ht.le, Real.mul_rpow ht.le (norm_nonneg _)]
  have : t ^ (-(((d : ℝ) - s) - 1)) = t * t ^ (-((d : ℝ) - s)) := by
    have h1 : t ^ (-(((d : ℝ) - s) - 1)) = t ^ (1 : ℝ) * t ^ (-((d : ℝ) - s)) := by
      rw [← Real.rpow_add ht]; congr 1; ring
    rw [h1, Real.rpow_one]
  rw [this]
  simp only [PiLp.smul_apply, smul_eq_mul]
  ring

lemma cmxMY_locInt_comp (K : Euc d → Euc d) (hK : cmxFB_KerOK K) (i : Fin d) :
    LocallyIntegrable (fun x : Euc d => ((K x i : ℝ) : ℂ)) := by
  obtain ⟨M, hM⟩ := hK.far
  have hKi : AEStronglyMeasurable (fun y : Euc d => ((K y i : ℝ) : ℂ)) volume :=
    Complex.continuous_ofReal.comp_aestronglyMeasurable
      ((EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).continuous.comp_aestronglyMeasurable hK.meas)
  have hsplit : (fun x : Euc d => ((K x i : ℝ) : ℂ)) =
      (ball (0 : Euc d) 1).indicator (fun x : Euc d => ((K x i : ℝ) : ℂ)) +
        (ball (0 : Euc d) 1)ᶜ.indicator (fun x : Euc d => ((K x i : ℝ) : ℂ)) := by
    exact (Set.indicator_self_add_compl _ _).symm
  rw [hsplit]
  refine LocallyIntegrable.add ?_ ?_
  · refine Integrable.locallyIntegrable ?_
    rw [integrable_indicator_iff measurableSet_ball]
    refine hK.loc.norm.mono' hKi.restrict (Eventually.of_forall fun y => ?_)
    rw [Complex.norm_real, Real.norm_eq_abs]
    simpa using PiLp.norm_apply_le (K y) i
  · refine MemLp.locallyIntegrable (p := ⊤) ?_ le_top
    refine memLp_top_of_bound (C := |M|) ?_ ?_
    · exact hKi.indicator measurableSet_ball.compl
    · refine Eventually.of_forall fun x => ?_
      by_cases hx : x ∈ (ball (0 : Euc d) 1)ᶜ
      · rw [Set.indicator_of_mem hx]
        have hx1 : 1 ≤ ‖x‖ := by simpa [mem_ball_zero_iff] using hx
        rw [Complex.norm_real, Real.norm_eq_abs]
        have := PiLp.norm_apply_le (K x) i
        have h2 := hM x hx1
        simp only [Real.norm_eq_abs] at this
        exact this.trans (h2.trans (le_abs_self M))
      · rw [Set.indicator_of_notMem hx]; simp

lemma cmxMY_gloForce_continuous (hd : 3 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) :
    Continuous (gloForce s : Euc d → Euc d) := by
  have hK := cmxFB_kerOK hd hs0 hsd
  have : ContDiff ℝ ∞ (gloForce s : Euc d → Euc d) := by
    rw [cmxFB_gloForce_eq, contDiff_infty]
    exact fun n => cmxFB_Phi_contDiff hK n _ _
  exact this.continuous

theorem cmxMY_ghi_ae (hd : 3 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) (i : Fin d) :
    ∃ (c : ℂ) (K : Euc d → ℂ), Integrable K ∧
      (∀ m : ℕ, ∃ C : ℝ, ∀ x : Euc d, 1 ≤ ‖x‖ → ‖K x‖ ≤ C * ‖x‖ ^ (-(m : ℝ))) ∧
      ∀ᵐ x : Euc d, ((ghiForce s x i : ℝ) : ℂ) = c * K x := by
  have hd1 : 1 ≤ d := by omega
  obtain ⟨c, hc⟩ := cmxMY_kernGrad_fourier hd hs0 hsd (s := s)
  have hγ : 0 < ((d : ℝ) - s) - 1 := by linarith
  obtain ⟨K, hK, hF, hfar, -⟩ := cmxMY_LP_homog hd1 hγ (cmxMY_hi d s i)
    (fun η hη => cmxMY_hi_smooth s i η hη) (fun t η ht => cmxMY_hi_hom s i t η ht)
  refine ⟨c, K, hK, hfar, ?_⟩
  have hKer := cmxFB_kerOK hd hs0 hsd
  have hloc1 : LocallyIntegrable (fun x : Euc d => ((ghiForce s x i : ℝ) : ℂ)) := by
    have h1 := cmxMY_locInt_comp _ hKer i
    have h2 : LocallyIntegrable (fun x : Euc d => ((gloForce s x i : ℝ) : ℂ)) :=
      (Complex.continuous_ofReal.comp ((EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).continuous.comp
        (cmxMY_gloForce_continuous hd hs0 hsd))).locallyIntegrable
    have e : (fun x : Euc d => ((ghiForce s x i : ℝ) : ℂ)) =
        (fun x : Euc d => ((kernGrad s x i : ℝ) : ℂ)) - fun x : Euc d => ((gloForce s x i : ℝ) : ℂ) := by
      funext x
      simp only [ghiForce, PiLp.sub_apply, Pi.sub_apply]
      push_cast; ring
    rw [e]
    exact h1.sub h2
  have hloc2 : LocallyIntegrable (fun x : Euc d => c * K x) := (hK.const_mul c).locallyIntegrable
  refine ae_eq_of_integral_contDiff_smul_eq hloc1 hloc2 (fun g hg hgc => ?_)
  -- the test function
  have hgc' : HasCompactSupport (fun x : Euc d => ((g x : ℝ) : ℂ)) :=
    hgc.comp_left (g := fun t : ℝ => (t : ℂ)) (by simp)
  have hgs' : ContDiff ℝ ∞ (fun x : Euc d => ((g x : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp hg
  set S : SchwartzMap (Euc d) ℂ := hgc'.toSchwartzMap hgs' with hS
  have hSg : ∀ x, S x = ((g x : ℝ) : ℂ) := fun x => rfl
  set Φ : SchwartzMap (Euc d) ℂ := 𝓕⁻ S with hΦ
  have hΦS : ∀ x, 𝓕 (⇑Φ) x = ((g x : ℝ) : ℂ) := by
    intro x
    have h : (𝓕 Φ : SchwartzMap (Euc d) ℂ) = S := FourierTransform.fourier_fourierInv_eq S
    have h2 := congrArg (fun T : SchwartzMap (Euc d) ℂ => T x) h
    rw [← hSg x, ← h2]
    rfl
  set Φ' : SchwartzMap (Euc d) ℂ := Φ - cmxMY_chiPhi Φ with hΦ'
  have hΦ'0 : ∀ ξ : Euc d, ‖ξ‖ ≤ 1 → Φ' ξ = 0 := by
    intro ξ hξ
    show Φ ξ - ((chi ξ : ℝ) : ℂ) * Φ ξ = 0
    rw [cmxFB_chi_one hξ]; simp
  have hL : ∫ x : Euc d, g x • ((ghiForce s x i : ℝ) : ℂ) =
      c * ∫ ξ : Euc d, cmxMY_hi d s i ξ * Φ' ξ := by
    have e1 : ∀ x : Euc d, g x • ((ghiForce s x i : ℝ) : ℂ) =
        ((ghiForce s x i : ℝ) : ℂ) * 𝓕 (⇑Φ) x := by
      intro x; rw [hΦS, Complex.real_smul]; ring
    simp_rw [e1]
    rw [cmxMY_ghi_pairing hd hs0 hsd i Φ]
    exact hc i Φ' hΦ'0
  have hR : ∫ x : Euc d, g x • (c * K x) =
      c * ∫ ξ : Euc d, cmxMY_hi d s i ξ * Φ' ξ := by
    have e1 : ∀ x : Euc d, g x • (c * K x) = c * (K x * 𝓕 (⇑Φ) x) := by
      intro x; rw [hΦS, Complex.real_smul]; ring
    simp_rw [e1]
    rw [integral_const_mul, integral_mul_fourier_eq K Φ hK Φ.integrable]
    congr 1
    refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
    beta_reduce
    rw [hF ξ]
    show _ = cmxMY_hi d s i ξ * (Φ ξ - ((chi ξ : ℝ) : ℂ) * Φ ξ)
    rw [Complex.real_smul]
    push_cast; ring
  rw [hL, hR]

lemma cmxMY_norm_le_card {d : ℕ} (v : EuclideanSpace ℝ (Fin d)) {b : ℝ} (hb : 0 ≤ b)
    (h : ∀ i, |v i| ≤ b) : ‖v‖ ≤ d * b := by
  rw [EuclideanSpace.norm_eq, Real.sqrt_le_iff]
  refine ⟨by positivity, ?_⟩
  calc ∑ i, ‖v i‖ ^ 2 ≤ ∑ _i : Fin d, b ^ 2 := by
        apply Finset.sum_le_sum
        intro i _
        rw [Real.norm_eq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) (h i) 2
    _ = d * b ^ 2 := by simp
    _ ≤ (d * b) ^ 2 := by
        rw [mul_pow]
        have : (d : ℝ) ≤ (d : ℝ) ^ 2 := by
          rcases Nat.eq_zero_or_pos d with h0 | h0
          · simp [h0]
          · have : (1 : ℝ) ≤ d := by exact_mod_cast h0
            nlinarith
        nlinarith [sq_nonneg b]

lemma cmxMY_kernGrad_continuousAt {s : ℝ} {x : Euc d} (hx : x ≠ 0) :
    ContinuousAt (kernGrad s : Euc d → Euc d) x := by
  unfold kernGrad
  have hc : ContinuousAt (fun y : Euc d => ‖y‖) x := continuous_norm.continuousAt
  have h2 : ContinuousAt (fun y : Euc d => -(‖y‖ ^ (-(s + 2)))) x :=
    (hc.rpow_const (Or.inl (norm_ne_zero_iff.2 hx))).neg
  exact h2.smul (continuousAt_id (x := x))

/-- an open-set a.e. inequality upgrades to a pointwise one for functions continuous on the set -/
lemma cmxMY_ae_to_all {U : Set (Euc d)} (hU : IsOpen U) {φ : Euc d → ℝ} (hφ : ContinuousOn φ U)
    (h : ∀ᵐ x : Euc d, x ∈ U → φ x ≤ 0) : ∀ x ∈ U, φ x ≤ 0 := by
  by_contra hcon
  push Not at hcon
  obtain ⟨x, hxU, hx⟩ := hcon
  have hV : IsOpen (U ∩ φ ⁻¹' Set.Ioi 0) := hφ.isOpen_inter_preimage hU isOpen_Ioi
  have hpos : 0 < volume (U ∩ φ ⁻¹' Set.Ioi 0) := hV.measure_pos volume ⟨x, hxU, hx⟩
  have hz : volume (U ∩ φ ⁻¹' Set.Ioi 0) = 0 := by
    rw [measure_eq_zero_iff_ae_notMem]
    filter_upwards [h] with y hy hyV
    exact absurd (hy hyV.1) (not_le.2 hyV.2)
  exact hpos.ne' hz

theorem cmxMY_ghi_far (hd : 3 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) (m : ℕ) :
    ∃ C : ℝ, ∀ x : Euc d, 1 ≤ ‖x‖ → ‖ghiForce s x‖ ≤ C * ‖x‖ ^ (-(m : ℝ)) := by
  have hKer := cmxFB_kerOK hd hs0 hsd
  choose c K hKint hKfar hae using fun i : Fin d => cmxMY_ghi_ae hd hs0 hsd (s := s) i
  choose C hC using fun i : Fin d => hKfar i m
  obtain ⟨B, hB⟩ := cmxFB_Phi_bdd hKer (cmxFB_B0 d) (cmxFB_Om (d := d) 1 one_pos)
  have hglo : ∀ x : Euc d, ‖gloForce s x‖ ≤ |B| := fun x => by
    rw [cmxFB_gloForce_eq]; exact (hB x).trans (le_abs_self B)
  set A : ℝ := ∑ i : Fin d, ‖c i‖ * |C i| + (1 + |B|) with hA
  have hA0 : 0 ≤ A := by
    rw [hA]; have : 0 ≤ ∑ i : Fin d, ‖c i‖ * |C i| := Finset.sum_nonneg fun i _ => by positivity
    positivity
  refine ⟨d * A, fun x hx => ?_⟩
  have hx0 : 0 < ‖x‖ := by linarith
  have hxp : 0 < ‖x‖ ^ (-(m : ℝ)) := Real.rpow_pos_of_pos hx0 _
  -- componentwise bound
  have hcomp : ∀ i : Fin d, |ghiForce s x i| ≤ A * ‖x‖ ^ (-(m : ℝ)) := by
    intro i
    by_cases hx1 : 1 < ‖x‖
    · -- a.e. bound, upgraded
      have hae' : ∀ᵐ y : Euc d, y ∈ {y : Euc d | 1 < ‖y‖} →
          |ghiForce s y i| - ‖c i‖ * |C i| * ‖y‖ ^ (-(m : ℝ)) ≤ 0 := by
        filter_upwards [hae i] with y hy hyU
        have hy1 : 1 ≤ ‖y‖ := le_of_lt hyU
        have h1 : |ghiForce s y i| = ‖c i‖ * ‖K i y‖ := by
          have := congrArg norm hy
          rw [Complex.norm_real, Real.norm_eq_abs, norm_mul] at this
          exact this
        have h2 := hC i y hy1
        have hp : 0 < ‖y‖ ^ (-(m : ℝ)) := Real.rpow_pos_of_pos (by linarith) _
        rw [h1, sub_nonpos]
        calc ‖c i‖ * ‖K i y‖ ≤ ‖c i‖ * (C i * ‖y‖ ^ (-(m : ℝ))) :=
              mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
          _ ≤ ‖c i‖ * (|C i| * ‖y‖ ^ (-(m : ℝ))) := by
              gcongr; exact le_abs_self _
          _ = _ := by ring
      have hcont : ContinuousOn (fun y : Euc d => |ghiForce s y i| - ‖c i‖ * |C i| * ‖y‖ ^ (-(m : ℝ)))
          {y : Euc d | 1 < ‖y‖} := by
        intro y hy
        have hy0 : y ≠ 0 := norm_ne_zero_iff.1 (by have : 1 < ‖y‖ := hy; linarith)
        refine ContinuousAt.continuousWithinAt ?_
        have h1 : ContinuousAt (ghiForce s : Euc d → Euc d) y :=
          (cmxMY_kernGrad_continuousAt hy0).sub (cmxMY_gloForce_continuous hd hs0 hsd).continuousAt
        refine ContinuousAt.sub ?_ ?_
        · exact (continuous_abs.continuousAt.comp
            ((EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).continuous.continuousAt.comp h1))
        · exact continuousAt_const.mul (continuous_norm.continuousAt.rpow_const
            (Or.inl (norm_ne_zero_iff.2 hy0)))
      have := cmxMY_ae_to_all (isOpen_lt continuous_const continuous_norm) hcont hae' x hx1
      have h3 : ‖c i‖ * |C i| ≤ A := by
        rw [hA]
        have : ‖c i‖ * |C i| ≤ ∑ j : Fin d, ‖c j‖ * |C j| :=
          Finset.single_le_sum (f := fun j : Fin d => ‖c j‖ * |C j|)
            (fun j _ => by positivity) (Finset.mem_univ i)
        linarith [abs_nonneg B]
      calc |ghiForce s x i| ≤ ‖c i‖ * |C i| * ‖x‖ ^ (-(m : ℝ)) := by linarith
        _ ≤ A * ‖x‖ ^ (-(m : ℝ)) := by gcongr
    · have hx1' : ‖x‖ = 1 := le_antisymm (not_lt.1 hx1) hx
      have hn : ‖ghiForce s x‖ ≤ 1 + |B| := by
        have h1 : ‖kernGrad s x‖ ≤ 1 := by
          refine (cmxFB_kernGrad_norm_le hs0 x).trans ?_
          exact Real.rpow_le_one_of_one_le_of_nonpos hx (by linarith)
        calc ‖ghiForce s x‖ = ‖kernGrad s x - gloForce s x‖ := rfl
          _ ≤ ‖kernGrad s x‖ + ‖gloForce s x‖ := norm_sub_le _ _
          _ ≤ 1 + |B| := add_le_add h1 (hglo x)
      have h2 : |ghiForce s x i| ≤ ‖ghiForce s x‖ := by simpa using PiLp.norm_apply_le (ghiForce s x) i
      have h3 : (1 + |B|) ≤ A := by
        rw [hA]; have : 0 ≤ ∑ i : Fin d, ‖c i‖ * |C i| := Finset.sum_nonneg fun i _ => by positivity
        linarith
      rw [hx1', Real.one_rpow]
      linarith
  have := cmxMY_norm_le_card (ghiForce s x) (by positivity : 0 ≤ A * ‖x‖ ^ (-(m : ℝ))) hcomp
  calc ‖ghiForce s x‖ ≤ d * (A * ‖x‖ ^ (-(m : ℝ))) := this
    _ = d * A * ‖x‖ ^ (-(m : ℝ)) := by ring

end HRS.Commutator.Whole
