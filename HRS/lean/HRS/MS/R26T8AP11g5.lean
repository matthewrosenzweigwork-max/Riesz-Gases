import HRS.MS.R26T8AP11g4
import HRS.MS.R26T8AP11g2
import HRS.MS.R26T8AP08c
import HRS.MS.R26T8AP10a

/-!
# S8.2 T8A P11g (part 5): the row identity
For `Q` conormal and `ρ` thermal: `x ↦ oneJ(Q(·,y))(x)` is `ρ dx`-integrable with
`∫ oneJ(Q(·,y)) dμ = -∫ ⟨forceMean ρ, ∇_x Q(·,y)⟩ dμ`.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82

variable {d : ℕ}

set_option maxHeartbeats 3200000 in
theorem r26t8a_g5_row (d : ℕ) (hd : 2 ≤ d) (k b : ℕ) (a beta M sigma : ℝ) (ha : 0 < a)
    (hbeta : 0 < beta) (hM : 0 ≤ M) (hsd : sigma < d) (rho : Euc d → ℝ)
    (hrho : IsThermalEquilibrium d (criticalS d) a beta rho) (Q : Euc d → Euc d → ℝ) (A : ℝ)
    (hA : 0 ≤ A) (hQ : Conormal (k + 2) b M (sigma - 2) A Q) (y : Euc d) :
    Integrable (fun x => oneJ (critCoeff d a beta rho) (fun u => Q u y) x)
      (HRS.Whole.withDensityReal rho) ∧
    ∫ x, oneJ (critCoeff d a beta rho) (fun u => Q u y) x ∂(HRS.Whole.withDensityReal rho) =
      -∫ u, inner ℝ (forceMean rho u) (pairGradX Q u y) ∂(HRS.Whole.withDensityReal rho) := by
  have hdd : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hs0 : 0 < criticalS d := by unfold criticalS; linarith
  have hsd' : criticalS d < d := by unfold criticalS; linarith
  haveI : Nontrivial (Euc d) := by
    apply Module.nontrivial_of_finrank_pos (R := ℝ)
    simp; omega
  obtain ⟨hdiff, C, c, hC, hc, hb⟩ := HRS.MS.Wad.s84_thermal_gaussReg hd ha hbeta hrho
  have hρs : ContDiff ℝ ∞ rho :=
    (HRS.MS.Mov0.mv0_hgauss hd (by unfold criticalS; linarith) (by unfold criticalS; linarith) ha hbeta
      hrho).1
  have hprob : HRS.Whole.IsProbDensity rho := hrho.1.1
  obtain ⟨τ, H⟩ := r26t8a_p10a_hyp hd hM hsd hA hQ hρs hC hc (fun x => (hb x).1) (fun x => (hb x).2) y
  obtain ⟨hHC1, ⟨B0, hB0⟩, ⟨B1, hB1⟩, hHd, hHv⟩ := r26t8a_g4_potential hd ha hbeta hrho
  set Hf : Euc d → ℝ := HRS.Whole.convFun (rieszKernel d (criticalS d)) rho with hHf
  set hh : Euc d → Euc d := fun w => rho w • gradient (fun v => Q v y) w with hhh
  have hdivI : Integrable (r26t8a_divh hh) := r26t8a_p10a_divh_int H
  have hrho0 : ∀ x, 0 ≤ rho x := hprob.nonneg
  have hρc : Continuous rho := hρs.continuous
  have hρi : Integrable rho := Integrable.of_integral_ne_zero (by rw [hprob.integral_one]; norm_num)
  have hρK : ∀ x, rho x ≤ C := fun x => by
    refine (le_abs_self _).trans ((hb x).1.trans ?_)
    have : Real.exp (-c * ‖x‖ ^ 2) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith [sq_nonneg ‖x‖])
    nlinarith
  have hker : ∀ w : Euc d, rieszKernel d (criticalS d) w = ‖w‖ ^ (-criticalS d) := fun w => by
    rw [rieszKernel, if_neg hs0.ne']
  -- the product function
  set F : Euc d × Euc d → ℝ := fun p => rho p.1 * (‖p.1 - p.2‖ ^ (-criticalS d) * r26t8a_divh hh p.2) with hF
  have hFi : Integrable F (volume.prod volume) := by
    have hdom := (r26t8a_g3_prod_int hd hs0 hsd' hrho0 hρK hρc hρi hdivI).2
    refine Integrable.mono' hdom ?_ (Filter.Eventually.of_forall fun p => ?_)
    · have h1 : AEStronglyMeasurable (fun p : Euc d × Euc d => rho p.1) (volume.prod volume) :=
        (hρc.comp continuous_fst).aestronglyMeasurable
      have h2 : Measurable (fun p : Euc d × Euc d => ‖p.1 - p.2‖ ^ (-criticalS d)) :=
        ((measurable_fst.sub measurable_snd).norm).pow_const _
      have h3 : AEStronglyMeasurable (fun p : Euc d × Euc d => r26t8a_divh hh p.2) (volume.prod volume) :=
        hdivI.aestronglyMeasurable.comp_snd
      exact h1.mul (h2.aestronglyMeasurable.mul h3)
    · have hn : 0 ≤ ‖p.1 - p.2‖ ^ (-criticalS d) := Real.rpow_nonneg (norm_nonneg _) _
      rw [hF]
      simp only [norm_mul, Real.norm_eq_abs, abs_of_nonneg (hrho0 p.1), abs_of_nonneg hn]
      have : ‖p.1 - p.2‖ ^ (-criticalS d) ≤ 1 + ‖p.1 - p.2‖ ^ (-criticalS d) := by linarith
      calc rho p.1 * (‖p.1 - p.2‖ ^ (-criticalS d) * |r26t8a_divh hh p.2|)
          ≤ rho p.1 * ((1 + ‖p.1 - p.2‖ ^ (-criticalS d)) * |r26t8a_divh hh p.2|) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right this (abs_nonneg _)) (hrho0 _)
        _ = _ := by ring
  -- swap
  have hswap : ∫ x, ∫ u, F (x, u) = ∫ u, ∫ x, F (x, u) := integral_integral_swap hFi
  have hinner : ∀ u, ∫ x, F (x, u) = Hf u * r26t8a_divh hh u := by
    intro u
    have : ∀ x, F (x, u) = (rho x * ‖x - u‖ ^ (-criticalS d)) * r26t8a_divh hh u := fun x => by
      simp only [hF]; ring
    simp only [this]
    rw [integral_mul_const, hHv u]
  have hFx : Integrable (fun x => ∫ u, F (x, u)) := hFi.integral_prod_left
  -- the row of oneJ
  have hae : ∀ᵐ u : Euc d ∂volume, u ≠ y := compl_mem_ae_iff.mpr (measure_singleton y)
  have hopen : IsOpen ({y}ᶜ : Set (Euc d)) := isClosed_singleton.isOpen_compl
  have hf2 : ContDiffOn ℝ 2 (fun v => Q v y) {y}ᶜ := by
    have hg : ContDiff ℝ ((k + 2 : ℕ) : WithTop ℕ∞) (fun v : Euc d => (v, y)) :=
      contDiff_id.prodMk contDiff_const
    have hmaps : Set.MapsTo (fun v : Euc d => (v, y)) {y}ᶜ {p : Euc d × Euc d | p.1 ≠ p.2} :=
      fun v hv => by simpa using hv
    have := hQ.1.comp hg.contDiffOn hmaps
    exact this.of_le (by exact_mod_cast (by omega : 2 ≤ k + 2))
  have hdiv : ∀ᵐ u : Euc d ∂volume, r26t8a_divSource rho Q u y = r26t8a_divh hh u := by
    filter_upwards [hae] with u hu
    exact (r26t8a_p10a_divh_eq hdiff
      (hf2.contDiffAt (hopen.mem_nhds (by simpa using hu)))).symm
  have hJrow : ∀ x : Euc d, x ≠ y → oneJ (critCoeff d a beta rho) (fun u => Q u y) x =
      ∫ u, ‖x - u‖ ^ (-criticalS d) * r26t8a_divh hh u := by
    intro x hxy
    obtain ⟨-, hid⟩ := r26t8a_conormal_potential_ibp d hd k b a beta M sigma ha hbeta hM hsd rho hrho Q A hA
      hQ x y hxy
    rw [hid]
    refine integral_congr_ae ?_
    filter_upwards [hdiv] with u hu
    rw [hker, hu]
  have hFrow : ∀ x : Euc d, ∫ u, F (x, u) = rho x * ∫ u, ‖x - u‖ ^ (-criticalS d) * r26t8a_divh hh u := by
    intro x
    simp only [hF]
    rw [integral_const_mul]
  have hae_x : ∀ᵐ x : Euc d ∂volume, x ≠ y := compl_mem_ae_iff.mpr (measure_singleton y)
  have hrowae : (fun x => rho x * oneJ (critCoeff d a beta rho) (fun u => Q u y) x) =ᵐ[volume]
      fun x => ∫ u, F (x, u) := by
    filter_upwards [hae_x] with x hx
    rw [hFrow, hJrow x hx]
  have hInt : Integrable (fun x => rho x * oneJ (critCoeff d a beta rho) (fun u => Q u y) x) :=
    hFx.congr hrowae.symm
  have hrowI : Integrable (fun x => oneJ (critCoeff d a beta rho) (fun u => Q u y) x)
      (HRS.Whole.withDensityReal rho) := (r26t8a_f25_wd_integrable hprob _).2 hInt
  refine ⟨hrowI, ?_⟩
  rw [r26t8a_f25_wd_integral hprob, r26t8a_f25_wd_integral hprob, integral_congr_ae hrowae, hswap]
  simp only [hinner]
  -- integration by parts against the potential
  obtain ⟨-, -, hibp⟩ := r26t8a_g2_ibp H hHC1 (B0 := B0) (B1 := B1) hB0 hB1
  have hsum : ∀ u, ∑ j : Fin d, fderiv ℝ Hf u (EuclideanSpace.single j 1) * hh u j =
      rho u * inner ℝ (forceMean rho u) (pairGradX Q u y) := by
    intro u
    simp only [hhh, hHd, PiLp.smul_apply, smul_eq_mul, pairGradX, PiLp.inner_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [RCLike.inner_apply, conj_trivial]
    ring
  rw [show (fun u => Hf u * r26t8a_divh hh u) = fun u => Hf u * r26t8a_divh hh u from rfl, hibp]
  congr 2
  funext u
  exact hsum u

end HRS.MS.R26T8A
