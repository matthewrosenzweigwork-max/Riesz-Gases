import HRS.Commutator.Whole.XNRSAux37
import HRS.Commutator.Whole.XLIAux44

/-!
# Packet XBB, part 1: the `L^p` bound for the Riesz transform on Fourier-localised Schwartz functions

By Littlewood–Paley theory from the X-LI development: `R_a u = ∑_k U_k` with `U_k` the dyadic pieces,
`U_k = (K_k ⋆ Δ̃_k u)`, the reverse square function inequality (`SYN`), the vector-valued
Fefferman–Stein inequality (`E3`) and the forward square function inequality (`E1At_rhoT`).
-/

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal FourierTransform ContDiff SchwartzMap LineDeriv Convolution

noncomputable section
namespace HRS.Commutator.Whole.XBB
open HRS.Commutator.Whole HRS.Commutator.Whole.XLI HRS.Commutator.Whole.XNRS
variable {d : ℕ}
local notation "𝔼" => EuclideanSpace ℝ (Fin d)

/-- the Riesz symbol `i ξ_a / |ξ|` -/
def xbbRm (a : Fin d) (η : 𝔼) : ℂ := Complex.I * (((η a) / ‖η‖ : ℝ) : ℂ)

lemma xbbRm_smul (a : Fin d) {c : ℝ} (hc : 0 < c) (η : 𝔼) : xbbRm a (c • η) = xbbRm a η := by
  unfold xbbRm
  rw [norm_smul, Real.norm_of_nonneg hc.le]
  simp only [PiLp.smul_apply, smul_eq_mul]
  rw [mul_div_mul_left _ _ hc.ne']

/-- the symbol `m(η) ρ(η)` -/
def xbbTh (a : Fin d) (η : 𝔼) : ℂ := xbbRm a η * rho η

lemma xbbTh_contDiff (a : Fin d) : ContDiff ℝ ∞ (xbbTh a : 𝔼 → ℂ) := by
  refine cmxMY_contDiff_of_away_real (r := 1 / 2) (by norm_num) (fun η hη => ?_) (fun η hη => ?_)
  · have hn : 0 < ‖η‖ := norm_pos_iff.2 hη
    have h1 : ContDiffAt ℝ ∞ (fun η : 𝔼 => (η a : ℝ)) η :=
      ((EuclideanSpace.proj a : 𝔼 →L[ℝ] ℝ).contDiff).contDiffAt
    have h2 : ContDiffAt ℝ ∞ (fun η : 𝔼 => ‖η‖) η := contDiffAt_norm ℝ hη
    have h3 : ContDiffAt ℝ ∞ (fun η : 𝔼 => xbbRm a η) η := by
      unfold xbbRm
      exact contDiffAt_const.mul
        ((Complex.ofRealCLM.contDiff.contDiffAt).comp η (h1.div h2 hn.ne'))
    exact h3.mul rho_contDiff.contDiffAt
  · simp [xbbTh, rho_eq_zero_of_le hη.le]

lemma xbbTh_cs (a : Fin d) : HasCompactSupport (xbbTh a : 𝔼 → ℂ) := rho_cs.mul_left


/-- telescoping of the Littlewood–Paley partition of unity -/
lemma xbb_rho_telescope (ξ : 𝔼) (K0 : ℤ) (n : ℕ)
    (h1 : cut (((2 : ℝ) ^ (K0 + (n : ℤ)))⁻¹ • ξ) = 1) (h0 : cut (((2 : ℝ) ^ (K0 - 1))⁻¹ • ξ) = 0) :
    ∑ i ∈ Finset.range (n + 1), rho (((2 : ℝ) ^ (K0 + (i : ℤ)))⁻¹ • ξ) = 1 := by
  set f : ℕ → ℝ := fun j => cut (((2 : ℝ) ^ (K0 + (j : ℤ) - 1))⁻¹ • ξ) with hf
  have key : ∀ i : ℕ, rho (((2 : ℝ) ^ (K0 + (i : ℤ)))⁻¹ • ξ) = ((f (i + 1) - f i : ℝ) : ℂ) := by
    intro i
    unfold rho
    have e : (2 : ℝ) • (((2 : ℝ) ^ (K0 + (i : ℤ)))⁻¹ • ξ) = ((2 : ℝ) ^ (K0 + (i : ℤ) - 1))⁻¹ • ξ := by
      rw [smul_smul, zpow_sub₀ (by norm_num), zpow_one]
      congr 1
      field_simp
    rw [e]
    have e2 : f (i + 1) = cut (((2 : ℝ) ^ (K0 + (i : ℤ)))⁻¹ • ξ) := by
      simp only [hf]; congr 3; push_cast; ring
    rw [e2]
  have hsum : ∑ i ∈ Finset.range (n + 1), rho (((2 : ℝ) ^ (K0 + (i : ℤ)))⁻¹ • ξ)
      = ((f (n + 1) - f 0 : ℝ) : ℂ) := by
    simp_rw [key]
    rw [← Complex.ofReal_sum, Finset.sum_range_sub (fun i => f i) (n + 1)]
  rw [hsum]
  have e1 : f (n + 1) = 1 := by
    simp only [hf]; rw [← h1]; congr 3; push_cast; ring
  have e0 : f 0 = 0 := by
    simp only [hf]; rw [← h0]; congr 3; simp
  rw [e1, e0]; simp


/-- the `k`-th dyadic piece of the Riesz transform of `u` -/
def xbbU (a : Fin d) (u : 𝓢(𝔼, ℂ)) (k : ℤ) : 𝓢(𝔼, ℂ) :=
  mulS (fun ξ => xbbTh a (((2 : ℝ) ^ k)⁻¹ • ξ))
    (temperate_symbol (xbbTh_contDiff a) (xbbTh_cs a) k) u

lemma xbbU_eq_cv (a : Fin d) (u : 𝓢(𝔼, ℂ)) (k : ℤ) (x : 𝔼) :
    xbbU a u k x = cv (symK (xbbTh a) k) (cv (symK (rhoT : 𝔼 → ℂ) k) ⇑u) x := by
  rw [cv_symK_eq_mulS rhoT_contDiff rhoT_cs u k]
  rw [cv_symK_eq_mulS (xbbTh_contDiff a) (xbbTh_cs a) _ k]
  rw [mulS_mulS _ _ (temperate_symbol (xbbTh_contDiff a) (xbbTh_cs a) k)
    (temperate_symbol rhoT_contDiff rhoT_cs k)
    ((temperate_symbol (xbbTh_contDiff a) (xbbTh_cs a) k).mul
      (temperate_symbol rhoT_contDiff rhoT_cs k))]
  unfold xbbU
  have hsym : (fun ξ : 𝔼 => xbbTh a (((2 : ℝ) ^ k)⁻¹ • ξ) * rhoT (((2 : ℝ) ^ k)⁻¹ • ξ)) =
      fun ξ => xbbTh a (((2 : ℝ) ^ k)⁻¹ • ξ) := by
    funext ξ
    unfold xbbTh
    rw [mul_assoc, mul_comm (rho _) (rhoT _), rhoT_mul_rho]
  rw [mulS_congr hsym ((temperate_symbol (xbbTh_contDiff a) (xbbTh_cs a) k).mul
      (temperate_symbol rhoT_contDiff rhoT_cs k)) (temperate_symbol (xbbTh_contDiff a) (xbbTh_cs a) k)]

lemma xbbU_rep (a : Fin d) (u : 𝓢(𝔼, ℂ)) (k : ℤ) (x : 𝔼) :
    xbbU a u k x = cv (symK (rhoT : 𝔼 → ℂ) k) (⇑(xbbU a u k)) x := by
  rw [cv_symK_eq_mulS rhoT_contDiff rhoT_cs _ k]
  unfold xbbU
  rw [mulS_mulS _ _ (temperate_symbol rhoT_contDiff rhoT_cs k)
    (temperate_symbol (xbbTh_contDiff a) (xbbTh_cs a) k)
    ((temperate_symbol rhoT_contDiff rhoT_cs k).mul
      (temperate_symbol (xbbTh_contDiff a) (xbbTh_cs a) k))]
  have hsym : (fun ξ : 𝔼 => rhoT (((2 : ℝ) ^ k)⁻¹ • ξ) * xbbTh a (((2 : ℝ) ^ k)⁻¹ • ξ)) =
      fun ξ => xbbTh a (((2 : ℝ) ^ k)⁻¹ • ξ) := by
    funext ξ
    unfold xbbTh
    rw [mul_left_comm, rhoT_mul_rho]
  rw [mulS_congr hsym ((temperate_symbol rhoT_contDiff rhoT_cs k).mul
      (temperate_symbol (xbbTh_contDiff a) (xbbTh_cs a) k)) (temperate_symbol (xbbTh_contDiff a) (xbbTh_cs a) k)]


lemma xbb_fourier_sum (S : Finset ℤ) (U : ℤ → 𝓢(𝔼, ℂ)) (ξ : 𝔼) :
    𝓕 (⇑(∑ k ∈ S, U k)) ξ = ∑ k ∈ S, 𝓕 (⇑(U k)) ξ := by
  have h := map_sum (SchwartzMap.fourierTransformCLM ℂ (E := ℂ) (V := 𝔼)) U S
  have h2 := congrArg (fun f : 𝓢(𝔼, ℂ) => f ξ) h
  simp only [SchwartzMap.fourierTransformCLM_apply, SchwartzMap.fourier_coe,
    SchwartzMap.sum_apply] at h2
  exact h2

lemma xbb_exists_K (ε Rr : ℝ) (hε : 0 < ε) (hεR : ε ≤ Rr) :
    ∃ (K0 : ℤ) (n : ℕ), (2 : ℝ) ^ K0 ≤ ε ∧ Rr ≤ (2 : ℝ) ^ (K0 + (n : ℤ)) := by
  obtain ⟨K0, hK0, -⟩ := _root_.exists_mem_Ico_zpow hε (one_lt_two : (1 : ℝ) < 2)
  obtain ⟨J, -, hJ⟩ := _root_.exists_mem_Ico_zpow (lt_of_lt_of_le hε hεR) (one_lt_two : (1 : ℝ) < 2)
  have hlt : (2 : ℝ) ^ K0 < (2 : ℝ) ^ (J + 1) := by linarith
  have hK : K0 < J + 1 := by
    by_contra h
    push Not at h
    have := zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2) h
    linarith
  refine ⟨K0, (J + 1 - K0).toNat, hK0, ?_⟩
  have : K0 + ((J + 1 - K0).toNat : ℤ) = J + 1 := by omega
  rw [this]; exact hJ.le

lemma xbb_sum_U (a : Fin d) (u R : 𝓢(𝔼, ℂ)) (ε Rr : ℝ) (hε : 0 < ε)
    (hu : ∀ ξ : 𝔼, (‖ξ‖ < ε ∨ Rr < ‖ξ‖) → 𝓕 (⇑u) ξ = 0)
    (hR : ∀ ξ : 𝔼, 𝓕 (⇑R) ξ = xbbRm a ξ * 𝓕 (⇑u) ξ) :
    ∃ S : Finset ℤ, R = ∑ k ∈ S, xbbU a u k := by
  obtain ⟨K0, n, hK0, hK1⟩ := xbb_exists_K ε (max Rr ε) hε (le_max_right _ _)
  refine ⟨(Finset.range (n + 1)).image (fun i : ℕ => K0 + (i : ℤ)), ?_⟩
  refine xschwartz_ext_fourier fun ξ => ?_
  have e1 : 𝓕 (R : 𝓢(𝔼, ℂ)) ξ = 𝓕 (⇑R) ξ := by rw [SchwartzMap.fourier_coe]
  have e2 : 𝓕 ((∑ k ∈ (Finset.range (n + 1)).image (fun i : ℕ => K0 + (i : ℤ)), xbbU a u k : 𝓢(𝔼, ℂ))) ξ
      = 𝓕 (⇑(∑ k ∈ (Finset.range (n + 1)).image (fun i : ℕ => K0 + (i : ℤ)), xbbU a u k)) ξ := by
    rw [SchwartzMap.fourier_coe]
  rw [e1, e2, xbb_fourier_sum, hR ξ, Finset.sum_image (fun i _ j _ h => by simpa using h)]
  have hU : ∀ k : ℤ, 𝓕 (⇑(xbbU a u k)) ξ = xbbTh a (((2 : ℝ) ^ k)⁻¹ • ξ) * 𝓕 (⇑u) ξ := fun k => by
    unfold xbbU; rw [fourier_mulS]
  simp_rw [hU]
  by_cases h0 : 𝓕 (⇑u) ξ = 0
  · simp [h0]
  · have hξ : ε ≤ ‖ξ‖ ∧ ‖ξ‖ ≤ Rr := by
      by_contra hcon
      apply h0
      refine hu ξ ?_
      by_cases h1 : ε ≤ ‖ξ‖
      · right; by_contra h2; exact hcon ⟨h1, not_lt.1 h2⟩
      · left; exact not_le.1 h1
    have hξ' : ‖ξ‖ ≤ (2 : ℝ) ^ (K0 + (n : ℤ)) := hξ.2.trans ((le_max_left _ _).trans hK1)
    have hp : ∑ i ∈ Finset.range (n + 1), rho (((2 : ℝ) ^ (K0 + (i : ℤ)))⁻¹ • ξ) = 1 := by
      refine xbb_rho_telescope ξ K0 n ?_ ?_
      · refine cut_one ?_
        have hs0 : 0 < (2 : ℝ) ^ (K0 + (n : ℤ)) := zpow_pos (by norm_num) _
        rw [norm_smul, norm_inv, Real.norm_of_nonneg hs0.le, inv_mul_le_iff₀ hs0, mul_one]
        exact hξ'
      · refine cut_zero ?_
        have hs0 : 0 < (2 : ℝ) ^ (K0 - 1) := zpow_pos (by norm_num) _
        rw [norm_smul, norm_inv, Real.norm_of_nonneg hs0.le, le_inv_mul_iff₀ hs0]
        have : (2 : ℝ) ^ (K0 - 1) * 2 = (2 : ℝ) ^ K0 := by
          rw [zpow_sub₀ (by norm_num), zpow_one]; field_simp
        rw [this]
        exact hK0.trans hξ.1
    calc xbbRm a ξ * 𝓕 (⇑u) ξ
        = (xbbRm a ξ * ∑ i ∈ Finset.range (n + 1), rho (((2 : ℝ) ^ (K0 + (i : ℤ)))⁻¹ • ξ)) *
            𝓕 (⇑u) ξ := by rw [hp, mul_one]
      _ = _ := by
        rw [Finset.mul_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun i _ => ?_
        unfold xbbTh
        rw [xbbRm_smul a (inv_pos.2 (zpow_pos (by norm_num) _))]


/-- **`L^p` bound for the Riesz transform** on Fourier-localised Schwartz functions, uniformly in the
localisation: `∫ |R_a u|^p ≲ ∫ |u|^p`, `p > 1`. -/
theorem xbb_riesz_lintegral (hd : 1 ≤ d) {p : ℝ} (hp : 1 < p) (a : Fin d) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ (u R : 𝓢(𝔼, ℂ)) (ε Rr : ℝ), 0 < ε →
      (∀ ξ : 𝔼, (‖ξ‖ < ε ∨ Rr < ‖ξ‖) → 𝓕 (⇑u) ξ = 0) →
      (∀ ξ : 𝔼, 𝓕 (⇑R) ξ = xbbRm a ξ * 𝓕 (⇑u) ξ) →
      ∫⁻ x, ‖R x‖ₑ ^ p ≤ C * ∫⁻ x, ‖u x‖ₑ ^ p := by
  have hconj : p.HolderConjugate p.conjExponent := Real.HolderConjugate.conjExponent hp
  have hconj1 : 1 < p.conjExponent := (Real.holderConjugate_iff.1 hconj.symm).1
  have hp0 : 0 < p := by linarith
  have hs : 1 / 2 < p / 2 := by linarith
  have hs0 : 0 ≤ p / 2 := by linarith
  obtain ⟨CS, hSYN⟩ := SYN hd hp (E1At_rhoT hd (by linarith : 1 / 2 < p.conjExponent / 2))
  obtain ⟨CE, hE3⟩ := E3 hd hs
  obtain ⟨CF, hCF⟩ := E1At_rhoT hd hs
  obtain ⟨A, hA, hdec⟩ := symK_dec (xbbTh_contDiff a) (xbbTh_cs a)
  refine ⟨(CS : ℝ≥0∞) * (((A * A) ^ (p / 2) * CE) * CF), ?_, ?_⟩
  · exact ENNReal.mul_ne_top ENNReal.coe_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top
      (ENNReal.rpow_ne_top_of_nonneg hs0 (ENNReal.mul_ne_top hA hA)) ENNReal.coe_ne_top)
      ENNReal.coe_ne_top)
  · intro u R ε Rr hε hu hR
    obtain ⟨S, hS⟩ := xbb_sum_U a u R ε Rr hε hu hR
    subst hS
    have h1 := hSYN S (xbbU a u) (fun k x => xbbU_rep a u k x)
    set h : ℤ → 𝔼 → ℂ := fun j => cv (symK (rhoT : 𝔼 → ℂ) j) ⇑u with hh
    have hhm : ∀ j, Measurable (h j) := fun j => by
      simp only [hh]
      rw [cv_symK_eq_mulS rhoT_contDiff rhoT_cs u j]
      exact (SchwartzMap.continuous _).measurable
    have h2 : ∫⁻ x, (∑ k ∈ S, ‖xbbU a u k x‖ₑ ^ 2) ^ (p / 2) ≤
        ∫⁻ x, sqS (fun j => cv (symK (xbbTh a) j) (h j)) x ^ (p / 2) := by
      refine lintegral_mono fun x => ENNReal.rpow_le_rpow ?_ hs0
      calc ∑ k ∈ S, ‖xbbU a u k x‖ₑ ^ 2 ≤ ∑' k, ‖xbbU a u k x‖ₑ ^ 2 := ENNReal.sum_le_tsum S
        _ = sqS (fun j => cv (symK (xbbTh a) j) (h j)) x := by
          unfold sqS
          refine tsum_congr fun k => ?_
          show ‖xbbU a u k x‖ₑ ^ 2 = ‖cv (symK (xbbTh a) k) (cv (symK (rhoT : 𝔼 → ℂ) k) ⇑u) x‖ₑ ^ 2
          rw [← xbbU_eq_cv a u k x]
    have h3 := hE3 A hA (fun j => symK (xbbTh a) j) h hdec hhm
    obtain ⟨C0, hC00, hC0⟩ := sch_bdd u
    have hB : ∀ x, ‖u x‖ₑ ≤ ENNReal.ofReal C0 := fun x => by
      rw [← ofReal_norm]; exact ENNReal.ofReal_le_ofReal (hC0 x)
    have h4 := hCF (⇑u) (SchwartzMap.continuous _).measurable u.integrable (ENNReal.ofReal C0)
      ENNReal.ofReal_ne_top hB
    rw [show 2 * (p / 2) = p by ring] at h4
    calc ∫⁻ x, ‖(∑ k ∈ S, xbbU a u k) x‖ₑ ^ p
        ≤ (CS : ℝ≥0∞) * ∫⁻ x, (∑ k ∈ S, ‖xbbU a u k x‖ₑ ^ 2) ^ (p / 2) := h1
      _ ≤ (CS : ℝ≥0∞) * ∫⁻ x, sqS (fun j => cv (symK (xbbTh a) j) (h j)) x ^ (p / 2) := by
          gcongr
      _ ≤ (CS : ℝ≥0∞) * (((A * A) ^ (p / 2) * CE) * ∫⁻ x, sqS h x ^ (p / 2)) := by gcongr
      _ ≤ (CS : ℝ≥0∞) * (((A * A) ^ (p / 2) * CE) * (CF * ∫⁻ x, ‖u x‖ₑ ^ p)) := by gcongr
      _ = _ := by ring

end HRS.Commutator.Whole.XBB
