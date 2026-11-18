import HRS.MC.SEdgeVocab
import HRS.MC.SEdgeB1
import HRS.MC.SEdgeB4b
import HRS.MC.SEdgeB7
import HRS.MC.SEdgeB9sym
import HRS.MC.SEdgeB11a
import HRS.MC.SEdgeB11b
import HRS.MC.SEdgeB12

/-!
# Packet B10a: first-order bound for the leading CLT (relocated proof of `sed_B10a_rate`)

From the master identity B12 with the Stein solution `f` of B11b:
`E F(W_N) - E F(Z) = sum_ab E[(C_ab - A_ab) d_ba f(W_N)] + beta N^{-1/2} sum_a E[B_a d_a f(W_N)]`.
Here `C_ab = mu(v_a . grad phi_b)` exactly (B9sym), so `E|C_ab - A_ab| <= K/sqrt N` by the LLN B7
(`m = 1`); and `E|B_a| <= K` (Holder transfer of the `L^2` energy bound, as in B4b); all derivatives of
`f` are bounded.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.SEdge.B10a

open HRS.Sec7

/-- `E |h G| <= M E |h|` for `|G| <= M`. -/
theorem b10_wbound {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {h G : Ω → ℝ} {M : ℝ}
    (hh : Integrable h μ) (hG : ∀ x, |G x| ≤ M) :
    |∫ x, h x * G x ∂μ| ≤ M * ∫ x, |h x| ∂μ := by
  have hi : Integrable (fun x => M * |h x|) μ := hh.abs.const_mul M
  have := norm_integral_le_of_norm_le hi (Filter.Eventually.of_forall fun x => by
    rw [Real.norm_eq_abs, abs_mul]
    calc |h x| * |G x| ≤ |h x| * M := mul_le_mul_of_nonneg_left (hG x) (abs_nonneg _)
      _ = M * |h x| := mul_comm _ _)
  rw [Real.norm_eq_abs] at this
  rwa [integral_const_mul] at this

theorem b10_abs_le {z t : ℝ} (ht : 0 < t) : |z| ≤ (t * z ^ 2 + 1 / t) / 2 := by
  have h : 0 ≤ (t * |z| - 1) ^ 2 / t := by positivity
  have e : (t * |z| - 1) ^ 2 / t = t * z ^ 2 + 1 / t - 2 * |z| := by
    have : z ^ 2 = |z| ^ 2 := (sq_abs z).symm
    rw [this]
    field_simp
    ring
  linarith

section Main

variable {d : ℕ} {s : ℝ} (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) {β : ℝ} (hβ : 0 ≤ β)
  {ρ : Torus d → ℝ} (hρ : SmoothPosDensity ρ)
include hd hs0 hs hβ hρ

/-- `L^1` bound for `A_N - mu(A)`: LLN B7 with `m = 1`. -/
theorem b10_A_l1 {v : Fin d → Torus d → ℝ} (hv : ∀ j, Torus.IsSmooth (v j))
    {φ : Torus d → ℝ} (hφ : Torus.IsSmooth φ) :
    ∃ K : ℝ, ∀ N : ℕ, 1 ≤ N →
      ∫ X, |(∫ x, sed_drift v φ x ∂(withDensityReal ρ)) - sed_A v φ X| ∂(sed_Q d s N β ρ) ≤
        K / Real.sqrt N := by
  have hpdc : ∀ k, Continuous (Torus.partialDeriv k φ) := fun k =>
    HRS.Q66.q66_cont_of_smooth (HRS.Q66.q66_isSmooth_partialDeriv hφ k)
  have hdriftc : Continuous (sed_drift v φ) := by
    unfold sed_drift
    exact continuous_finsetSum _ fun k _ => (HRS.Q66.q66_cont_of_smooth (hv k)).mul (hpdc k)
  obtain ⟨M, hM⟩ := (isCompact_univ (X := Torus d)).exists_bound_of_continuousOn hdriftc.continuousOn
  have hM' : ∀ x, |sed_drift v φ x| ≤ M := fun x => by
    simpa [Real.norm_eq_abs] using hM x (Set.mem_univ _)
  obtain ⟨C7, hC7⟩ := HRS.MC.SEdge.B7.sed_B7_lln_proof hd hs0 hs hβ hρ M 1
  refine ⟨(C7 + 1) / 2, fun N hN => ?_⟩
  have hG : IsProbabilityMeasure (sed_Q d s N β ρ) :=
    HRS.MC.SEdge.B4b.b4b_isProb hd hs0 hs hβ hρ N hN
  set c : ℝ := ∫ x, sed_drift v φ x ∂(withDensityReal ρ) with hc
  set Z : Config d N → ℝ := fun X => sed_A v φ X - c with hZ
  obtain ⟨hAm, MA, hMA⟩ := HRS.MC.SEdge.B12.b12_A_facts (N := N) hN hv hφ
  have hZm : Measurable Z := hAm.sub_const c
  have hZb : ∀ X, |Z X| ≤ MA + |c| := fun X => by
    show |sed_A v φ X - c| ≤ MA + |c|
    linarith [abs_sub (sed_A v φ X) c, hMA X]
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  set t : ℝ := Real.sqrt N with ht
  have htpos : 0 < t := Real.sqrt_pos.2 hNpos
  have htt : t ^ 2 = N := Real.sq_sqrt hNpos.le
  have hZ2 : Integrable (fun X => Z X ^ 2) (sed_Q d s N β ρ) := by
    refine Integrable.of_bound (hZm.pow_const 2).aestronglyMeasurable ((MA + |c|) ^ 2)
      (Filter.Eventually.of_forall fun X => ?_)
    rw [Real.norm_eq_abs, abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (hZb X) 2
  have hZ1 : Integrable (fun X => |Z X|) (sed_Q d s N β ρ) :=
    Integrable.of_bound hZm.abs.aestronglyMeasurable (MA + |c|)
      (Filter.Eventually.of_forall fun X => by simpa [Real.norm_eq_abs] using hZb X)
  have hmom : ∫ X, Z X ^ 2 ∂(sed_Q d s N β ρ) ≤ C7 / (N : ℝ) := by
    have := hC7 (sed_drift v φ) hdriftc.measurable hM' N hN
    simp only [mul_one, pow_one] at this
    exact this
  have step1 : ∫ X, |Z X| ∂(sed_Q d s N β ρ) ≤
      ∫ X, (t * Z X ^ 2 + 1 / t) / 2 ∂(sed_Q d s N β ρ) :=
    integral_mono hZ1 (((hZ2.const_mul t).add (integrable_const _)).div_const 2)
      (fun X => b10_abs_le htpos)
  have step2 : ∫ X, (t * Z X ^ 2 + 1 / t) / 2 ∂(sed_Q d s N β ρ) =
      (t * ∫ X, Z X ^ 2 ∂(sed_Q d s N β ρ) + 1 / t) / 2 := by
    rw [integral_div, integral_add (hZ2.const_mul t) (integrable_const _), integral_const_mul]
    simp
  have step3 : (t * ∫ X, Z X ^ 2 ∂(sed_Q d s N β ρ) + 1 / t) / 2 ≤ (C7 + 1) / 2 / t := by
    have h1 : t * ∫ X, Z X ^ 2 ∂(sed_Q d s N β ρ) ≤ t * (C7 / (N : ℝ)) :=
      mul_le_mul_of_nonneg_left hmom htpos.le
    have h2 : t * (C7 / (N : ℝ)) = C7 / t := by
      rw [← htt]; field_simp
    have h3 : (C7 + 1) / 2 / t = (C7 / t + 1 / t) / 2 := by ring
    rw [h3]
    linarith
  have : ∫ X, |(∫ x, sed_drift v φ x ∂(withDensityReal ρ)) - sed_A v φ X| ∂(sed_Q d s N β ρ) =
      ∫ X, |Z X| ∂(sed_Q d s N β ρ) := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun X => ?_)
    simp only [hZ, hc]
    exact abs_sub_comm _ _
  rw [this]
  exact step1.trans (step2.le.trans step3)

/-- `L^1` bound for `B_N`: Holder transfer (B4a, `r = 2`) of the `L^2` energy bound. -/
theorem b10_B_l1 {v : Fin d → Torus d → ℝ} (hv : ∀ j, Torus.IsSmooth (v j)) :
    ∃ K : ℝ, ∀ N : ℕ, 1 ≤ N →
      ∫ X, |sed_B d s ρ β v X| ∂(sed_Q d s N β ρ) ≤ K := by
  have hP : IsProbabilityMeasure (withDensityReal ρ) := HRS.MC.SEdge.B3.b3_prob hρ
  set J : ℝ := ∫ x, ∫ y, Q66.q66_hv d s v x y ∂(withDensityReal ρ) ∂(withDensityReal ρ) with hJ
  set K : ℝ := 3 * ∫ x, ∫ y, Q66.q66_hv d s v x y ^ 2 ∂(withDensityReal ρ) ∂(withDensityReal ρ)
    with hK
  have hK0 : 0 ≤ K := by
    rw [hK]
    exact mul_nonneg (by norm_num) (integral_nonneg fun x => integral_nonneg fun y => sq_nonneg _)
  obtain ⟨C2, hC2, T2⟩ := HRS.MC.SEdge.B4a.sed_B4a_transfer_proof hd hs0 hs hβ hρ (r := 2)
    (by norm_num)
  set A : ℝ := C2 * K ^ (1 / 2 : ℝ) with hAdef
  have hA0 : 0 ≤ A := mul_nonneg hC2 (Real.rpow_nonneg hK0 _)
  refine ⟨A + A, fun N hN => ?_⟩
  have hG : IsProbabilityMeasure (sed_Q d s N β ρ) :=
    HRS.MC.SEdge.B4b.b4b_isProb hd hs0 hs hβ hρ N hN
  have hPP : IsProbabilityMeasure (Measure.pi fun _ : Fin N => withDensityReal ρ) := by
    infer_instance
  obtain ⟨hYm, hYL, hYint⟩ := HRS.MC.SEdge.B4b.b4b_L2 hd hs0 hs hρ hv N hN
  set Y : Config d N → ℝ := HRS.MC.SEdge.B4b.b4b_Y d s ρ v N with hYdef
  have hYsq : ∫⁻ X, ENNReal.ofReal (Y X ^ 2) ∂(Measure.pi fun _ : Fin N => withDensityReal ρ) ≤
      ENNReal.ofReal K := by
    rw [← ofReal_integral_eq_lintegral_ofReal hYL.integrable_sq
      (Filter.Eventually.of_forall fun _ => sq_nonneg _)]
    exact ENNReal.ofReal_le_ofReal hYint
  have hA : ∫⁻ X, ENNReal.ofReal |Y X| ∂(sed_Q d s N β ρ) ≤ ENNReal.ofReal A := by
    have h1 := T2 N hN (fun X => ENNReal.ofReal |Y X|) hYm.abs.ennreal_ofReal
    have h2 : ∫⁻ X, (ENNReal.ofReal |Y X|) ^ (2 : ℝ) ∂(Measure.pi fun _ : Fin N => withDensityReal ρ)
        = ∫⁻ X, ENNReal.ofReal (Y X ^ 2) ∂(Measure.pi fun _ : Fin N => withDensityReal ρ) := by
      refine lintegral_congr fun X => ?_
      rw [ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) (by norm_num), Real.rpow_two, sq_abs]
    rw [h2] at h1
    refine h1.trans ?_
    calc ENNReal.ofReal C2 * (∫⁻ X, ENNReal.ofReal (Y X ^ 2)
          ∂(Measure.pi fun _ : Fin N => withDensityReal ρ)) ^ (1 / (2 : ℝ))
        ≤ ENNReal.ofReal C2 * (ENNReal.ofReal K) ^ (1 / (2 : ℝ)) := by gcongr
      _ = ENNReal.ofReal A := by
        rw [hAdef, ENNReal.ofReal_mul hC2, ENNReal.ofReal_rpow_of_nonneg hK0 (by norm_num)]
  have hGY : Integrable Y (sed_Q d s N β ρ) := by
    refine ⟨hYm.aestronglyMeasurable, ?_⟩
    unfold HasFiniteIntegral
    simp_rw [Real.enorm_eq_ofReal_abs]
    exact lt_of_le_of_lt hA ENNReal.ofReal_lt_top
  have hYabs : ∫ X, |Y X| ∂(sed_Q d s N β ρ) ≤ A := by
    have := ofReal_integral_eq_lintegral_ofReal hGY.abs
      (Filter.Eventually.of_forall fun _ => abs_nonneg _)
    rw [← this] at hA
    exact (ENNReal.ofReal_le_ofReal_iff hA0).1 hA
  set c : ℝ := ∫ X, Y X ∂(sed_Q d s N β ρ) with hc
  have hcA : |c| ≤ A := (abs_integral_le_integral_abs).trans hYabs
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hmE : ∀ X, modulatedEnergy (Q66.q66_hv d s v) X (withDensityReal ρ) =
      (N : ℝ)⁻¹ * (Y X - J / 2) := by
    intro X
    simp only [hYdef, HRS.MC.SEdge.B4b.b4b_Y, hJ]
    field_simp
    ring
  have h3 : ∫ Z, modulatedEnergy (Q66.q66_hv d s v) Z (withDensityReal ρ)
      ∂(sed_Q d s N β ρ) = (N : ℝ)⁻¹ * (c - J / 2) := by
    simp_rw [hmE]
    rw [integral_const_mul, integral_sub hGY (integrable_const _)]
    simp [hc]
  have hB : ∀ X, sed_B d s ρ β v X = Y X - c := by
    intro X
    unfold sed_B
    rw [h3, hmE X]
    field_simp
    ring
  simp_rw [hB]
  calc ∫ X, |Y X - c| ∂(sed_Q d s N β ρ) ≤ ∫ X, (|Y X| + |c|) ∂(sed_Q d s N β ρ) :=
        integral_mono (hGY.sub (integrable_const c)).abs (hGY.abs.add (integrable_const _))
          (fun X => abs_sub _ _)
    _ = ∫ X, |Y X| ∂(sed_Q d s N β ρ) + |c| := by
        rw [integral_add hGY.abs (integrable_const _)]
        simp
    _ ≤ A + A := add_le_add hYabs hcA

theorem sed_B10a_rate_proof {p : ℕ} {φ : Fin p → Torus d → ℝ} (hφ : ∀ a, Torus.IsSmooth (φ a))
    {F : EuclideanSpace ℝ (Fin p) → ℝ} (hF : MemCb 5 F) :
    ∃ K : ℝ, ∀ N : ℕ, 1 ≤ N →
      |∫ X, F (centeredStat (sed_Q d s N β ρ) φ X) ∂(sed_Q d s N β ρ) -
          ∫ z, F z ∂(multivariateGaussian 0 (sed_Cmat d s β ρ φ))| ≤ K / Real.sqrt N := by
  have hP : IsProbabilityMeasure (withDensityReal ρ) := HRS.MC.SEdge.B3.b3_prob hρ
  have hCpsd := HRS.MC.SEdge.B11a.sed_B11a_cov_psd_proof hd hs0 hs hβ hρ hφ
  obtain ⟨f, -, hf5, hfb, hstein, -⟩ := HRS.MC.SEdge.B11b.sed_B11b_ou_proof _ hCpsd hF
  have hf : sed_StBdd f 3 := by
    refine ⟨hf5.of_le (by norm_num), fun j hj1 hj3 => ?_⟩
    obtain ⟨M, hM⟩ := hF.2 j (by omega)
    refine ⟨(j : ℝ)⁻¹ * ⨆ y, ‖iteratedFDeriv ℝ j F y‖, fun x => hfb j hj1 (by omega) x⟩
  have hFc : Continuous F := hF.1.continuous
  have hFb : ∃ M, ∀ z, |F z| ≤ M := by
    obtain ⟨M, hM⟩ := hF.2 0 (Nat.zero_le _)
    refine ⟨M, fun z => ?_⟩
    have := hM ⟨z, rfl⟩
    simpa [norm_iteratedFDeriv_zero, Real.norm_eq_abs] using this
  choose r v hrs hvs hrae hresp hmean hdiv using
    fun a => HRS.MC.SEdge.B1.sed_B1_regular_proof hd hs0 hs hβ hρ (hφ a)
  have hint : ∀ a, ∀ N : ℕ, 1 ≤ N → Integrable
      (fun X : Config d N => modulatedEnergy (Q66.q66_hv d s (v a)) X (withDensityReal ρ))
      (sed_Q d s N β ρ) := fun a =>
    (HRS.MC.SEdge.B4b.sed_B4b_energy_proof hd hs0 hs hβ hρ (hvs a)).1
  -- `C_ab = mu(v_a . grad phi_b)`
  have hC : ∀ a b, sed_Cmat d s β ρ φ a b = ∫ x, sed_drift (v a) (φ b) x ∂(withDensityReal ρ) := by
    intro a b
    obtain ⟨h1, h2⟩ := HRS.MC.SEdge.B9sym.sed_B9sym_response_proof hd hs0 hs hβ hρ (hφ a) (hφ b)
      (hrs a) (hrs b) (hvs a) (hdiv a) (hresp a) (hresp b)
    rw [h1]
    have h3 : ∫ x, r a x * φ b x ∂(withDensityReal ρ) = ∫ x, φ b x * r a x ∂(withDensityReal ρ) :=
      integral_congr_ae (Filter.Eventually.of_forall fun x => mul_comm _ _)
    rw [h3, h2]
    unfold sed_Cmat
    simp only [Matrix.of_apply]
    refine integral_congr_ae ?_
    filter_upwards [hrae b] with x hx
    rw [hx]
  choose KA hKA using fun a b => b10_A_l1 hd hs0 hs hβ hρ (hvs a) (hφ b)
  choose KB hKB using fun a => b10_B_l1 hd hs0 hs hβ hρ (hvs a)
  choose M2 hM2 using fun a b => (HRS.MC.SEdge.B12.b12_second_facts hf a b).2
  have hψb : ∀ a, ∃ M, ∀ x, |fderiv ℝ f x (stdVec a)| ≤ M := by
    intro a
    obtain ⟨M0, hM0⟩ := (HRS.MC.SEdge.B12.b12_psi_memCb hf a).2 0 (Nat.zero_le _)
    refine ⟨M0, fun x => ?_⟩
    have := hM0 ⟨x, rfl⟩
    simpa [norm_iteratedFDeriv_zero, Real.norm_eq_abs] using this
  choose M1 hM1 using hψb
  refine ⟨∑ a, ∑ b, max (M2 a b) 0 * KA a b + β * ∑ a, max (M1 a) 0 * KB a, fun N hN => ?_⟩
  have hQ : IsProbabilityMeasure (sed_Q d s N β ρ) :=
    HRS.MC.SEdge.B4b.b4b_isProb hd hs0 hs hβ hρ N hN
  have hmaster := HRS.MC.SEdge.B12.sed_B12_master_proof hd hs0 hs hβ hρ hN hφ hrs hvs hdiv hresp
    (fun a => hint a N hN) hFc hFb hf hstein
  rw [hmaster]
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hsN : 0 < Real.sqrt N := Real.sqrt_pos.2 hNpos
  have hT1 : ∀ a b, |∫ X, (sed_Cmat d s β ρ φ a b - sed_A (v a) (φ b) X) *
        iteratedFDeriv ℝ 2 f (centeredStat (sed_Q d s N β ρ) φ X) ![stdVec b, stdVec a]
        ∂(sed_Q d s N β ρ)| ≤ max (M2 a b) 0 * (KA a b / Real.sqrt N) := by
    intro a b
    obtain ⟨hAm, MA, hMA⟩ := HRS.MC.SEdge.B12.b12_A_facts (N := N) hN (hvs a) (hφ b)
    have hhi : Integrable (fun X => sed_Cmat d s β ρ φ a b - sed_A (v a) (φ b) X)
        (sed_Q d s N β ρ) := by
      refine Integrable.of_bound ((measurable_const.sub hAm)).aestronglyMeasurable
        (|sed_Cmat d s β ρ φ a b| + MA) (Filter.Eventually.of_forall fun X => ?_)
      rw [Real.norm_eq_abs]
      linarith [abs_sub (sed_Cmat d s β ρ φ a b) (sed_A (v a) (φ b) X), hMA X]
    refine (b10_wbound (G := fun X => iteratedFDeriv ℝ 2 f (centeredStat (sed_Q d s N β ρ) φ X)
      ![stdVec b, stdVec a]) (M := max (M2 a b) 0) hhi
      (fun X => (hM2 a b _).trans (le_max_left _ _))).trans ?_
    refine mul_le_mul_of_nonneg_left ?_ (le_max_right _ _)
    have := hKA a b N hN
    simp_rw [hC a b]
    exact this
  have hT2 : ∀ a, |∫ X, sed_B d s ρ β (v a) X *
        fderiv ℝ f (centeredStat (sed_Q d s N β ρ) φ X) (stdVec a) ∂(sed_Q d s N β ρ)| ≤
      max (M1 a) 0 * KB a := by
    intro a
    have hBi : Integrable (fun X : Config d N => sed_B d s ρ β (v a) X) (sed_Q d s N β ρ) := by
      unfold sed_B
      exact ((hint a N hN).sub (integrable_const _)).const_mul _
    refine (b10_wbound (G := fun X => fderiv ℝ f (centeredStat (sed_Q d s N β ρ) φ X) (stdVec a))
      (M := max (M1 a) 0) hBi (fun X => (hM1 a _).trans (le_max_left _ _))).trans ?_
    exact mul_le_mul_of_nonneg_left (hKB a N hN) (le_max_right _ _)
  calc _ ≤ |∑ a, ∑ b, ∫ X, (sed_Cmat d s β ρ φ a b - sed_A (v a) (φ b) X) *
          iteratedFDeriv ℝ 2 f (centeredStat (sed_Q d s N β ρ) φ X) ![stdVec b, stdVec a]
          ∂(sed_Q d s N β ρ)| + |β / Real.sqrt N * ∑ a, ∫ X, sed_B d s ρ β (v a) X *
          fderiv ℝ f (centeredStat (sed_Q d s N β ρ) φ X) (stdVec a) ∂(sed_Q d s N β ρ)| :=
        abs_add_le _ _
    _ ≤ ∑ a, ∑ b, max (M2 a b) 0 * (KA a b / Real.sqrt N) +
          β / Real.sqrt N * ∑ a, max (M1 a) 0 * KB a := by
        refine add_le_add ?_ ?_
        · refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun a _ => ?_)
          refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun b _ => hT1 a b)
        · rw [abs_mul, abs_of_nonneg (div_nonneg hβ hsN.le)]
          refine mul_le_mul_of_nonneg_left ?_ (div_nonneg hβ hsN.le)
          exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun a _ => hT2 a)
    _ = _ := by
        have e1 : ∑ a, ∑ b, max (M2 a b) 0 * (KA a b / Real.sqrt N) =
            (∑ a, ∑ b, max (M2 a b) 0 * KA a b) / Real.sqrt N := by
          rw [Finset.sum_div]
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [Finset.sum_div]
          exact Finset.sum_congr rfl fun b _ => by ring
        rw [e1]
        ring

end Main


end HRS.MC.SEdge.B10a
