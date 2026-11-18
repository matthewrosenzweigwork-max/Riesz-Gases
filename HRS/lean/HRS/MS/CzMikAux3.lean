import HRS.MS.CzMikAux2

/-!
# MIK-1, part 3: the localised Mikhlin multiplier theorem

**Statement** (`mikhlin_localised`, new infrastructure lemma, not a manuscript row).  For `d ≥ 1` and `1 < p`
there is a constant `C < ∞` (depending on `d, p` only) such that for every Mikhlin symbol `m` of order
`d + 1` with constant `A ≥ 0` (`mik1_IsMikhlin d A m`), every Schwartz `u` whose Fourier transform vanishes
off the annulus `{ε ≤ |ξ| ≤ Rr}` (`ε > 0`), and every Schwartz `R` with `𝓕 R = m 𝓕 u`,
`∫ |R|^p ≤ C A^p ∫ |u|^p` (lintegral over `ℝ^d`, in `ℝ≥0∞`).

Proof: generalisation of `HRS.Commutator.Whole.XBB.xbb_riesz_lintegral`: the pieces `U_k = Δ_k^m u` are
`dK (mik1_Th m) k ⋆ (symK ρ̃ k ⋆ u)`, `R = ∑_{k ∈ S} U_k` for a finite `S`, `SYN` (reverse square function),
`E3` (Fefferman–Stein, decay constant `C₀ c₀ A` of `dK` from `mik1_dK_dec_unif`), `E1At_rhoT` (forward square
function); the constant is linear in `A^p` because the decay constant of `dK (mik1_Th m)` is linear in `A`.

Adjustments relative to the plan sketch: smoothness in `mik1_IsMikhlin` is `ContDiffAt ℝ ∞` (ordinary
smoothness) instead of `⊤`; `mik1_IsMikhlin` is defined in `CzMikAux1` since `HRS/CZ/Defs.lean` is not present
on this branch; `m` is complex valued on `EuclideanSpace ℝ (Fin d)`, `u`, `R` are complex Schwartz functions.
No case distinction `A = 0` is needed.
-/

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal FourierTransform ContDiff SchwartzMap LineDeriv Convolution

noncomputable section
namespace HRS.CZ.Mik
open HRS.Commutator.Whole HRS.Commutator.Whole.XLI HRS.Commutator.Whole.XNRS HRS.Commutator.Whole.XBB
variable {d : ℕ}
local notation "𝔼" => EuclideanSpace ℝ (Fin d)

lemma mik1_rpow_sq {p : ℝ} (hp : 0 ≤ p) (x y : ℝ≥0∞) :
    ((x * y) * (x * y)) ^ (p / 2) = x ^ p * y ^ p := by
  have hp2 : 0 ≤ p / 2 := by linarith
  rw [ENNReal.mul_rpow_of_nonneg _ _ hp2, ENNReal.mul_rpow_of_nonneg _ _ hp2]
  have e1 : ∀ z : ℝ≥0∞, z ^ (p / 2) * z ^ (p / 2) = z ^ p := fun z => by
    rw [← ENNReal.rpow_add_of_nonneg _ _ hp2 hp2]; congr 1; ring
  calc x ^ (p / 2) * y ^ (p / 2) * (x ^ (p / 2) * y ^ (p / 2))
      = (x ^ (p / 2) * x ^ (p / 2)) * (y ^ (p / 2) * y ^ (p / 2)) := by ring
    _ = x ^ p * y ^ p := by rw [e1, e1]

theorem mikhlin_localised (hd : 1 ≤ d) {p : ℝ} (hp : 1 < p) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ (A : ℝ) (m : 𝔼 → ℂ), 0 ≤ A → mik1_IsMikhlin d A m →
      ∀ (u R : 𝓢(𝔼, ℂ)) (ε Rr : ℝ), 0 < ε →
        (∀ ξ : 𝔼, (‖ξ‖ < ε ∨ Rr < ‖ξ‖) → 𝓕 (⇑u) ξ = 0) →
        (∀ ξ : 𝔼, 𝓕 (⇑R) ξ = m ξ * 𝓕 (⇑u) ξ) →
        ∫⁻ x, ‖R x‖ₑ ^ p ≤ C * ENNReal.ofReal A ^ p * ∫⁻ x, ‖u x‖ₑ ^ p := by
  have hconj : p.HolderConjugate p.conjExponent := Real.HolderConjugate.conjExponent hp
  have hconj1 : 1 < p.conjExponent := (Real.holderConjugate_iff.1 hconj.symm).1
  have hp0 : 0 < p := by linarith
  have hs : 1 / 2 < p / 2 := by linarith
  have hs0 : 0 ≤ p / 2 := by linarith
  obtain ⟨CS, hSYN⟩ := SYN hd hp (E1At_rhoT hd (by linarith : 1 / 2 < p.conjExponent / 2))
  obtain ⟨CE, hE3⟩ := E3 hd hs
  obtain ⟨CF, hCF⟩ := E1At_rhoT hd hs
  obtain ⟨c0, hc0, hbound⟩ := mik1_Th_bound (d := d)
  obtain ⟨Cd, hCd0, hCd⟩ := mik1_dK_dec_unif (d := d) 2
  set x0 : ℝ≥0∞ := ENNReal.ofReal (Cd * c0) with hx0
  refine ⟨(CS : ℝ≥0∞) * ((x0 ^ p * CE) * CF), ?_, ?_⟩
  · exact ENNReal.mul_ne_top ENNReal.coe_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top
      (ENNReal.rpow_ne_top_of_nonneg hp0.le ENNReal.ofReal_ne_top) ENNReal.coe_ne_top)
      ENNReal.coe_ne_top)
  · intro A m hA hm u R ε Rr hε hu hR
    obtain ⟨S, hS⟩ := mik1_sum_U m hm.1 u R ε Rr hε hu hR
    subst hS
    have hb : ∀ (k : ℤ) (i : ℕ), i ≤ d + 1 → ∀ η : 𝔼,
        ‖iteratedFDeriv ℝ i (mik1_Th m k) η‖ ≤ c0 * A := fun k i hi η => hbound A m hA hm k i hi η
    have hfam := mik1_symFam hm hA hc0 hb
    have hdec : ∀ j, DecK (ENNReal.ofReal (Cd * (c0 * A))) j (dK (mik1_Th m) j) :=
      hCd (mik1_Th m) hfam.smooth hfam.supp (c0 * A) (mul_nonneg hc0 hA)
        (fun j i hi η => hb j i hi η)
    set Ad : ℝ≥0∞ := ENNReal.ofReal (Cd * (c0 * A)) with hAd
    have hAdne : Ad ≠ ⊤ := ENNReal.ofReal_ne_top
    have hAd' : Ad = x0 * ENNReal.ofReal A := by
      rw [hAd, hx0, ← ENNReal.ofReal_mul (mul_nonneg hCd0 hc0), mul_assoc]
    have h1 := hSYN S (mik1_U m hm.1 u) (fun k x => mik1_U_rep m hm.1 u k x)
    set h : ℤ → 𝔼 → ℂ := fun j => cv (symK (rhoT : 𝔼 → ℂ) j) ⇑u with hh
    have hhm : ∀ j, Measurable (h j) := fun j => by
      simp only [hh]
      rw [cv_symK_eq_mulS rhoT_contDiff rhoT_cs u j]
      exact (SchwartzMap.continuous _).measurable
    have h2 : ∫⁻ x, (∑ k ∈ S, ‖mik1_U m hm.1 u k x‖ₑ ^ 2) ^ (p / 2) ≤
        ∫⁻ x, sqS (fun j => cv (dK (mik1_Th m) j) (h j)) x ^ (p / 2) := by
      refine lintegral_mono fun x => ENNReal.rpow_le_rpow ?_ hs0
      calc ∑ k ∈ S, ‖mik1_U m hm.1 u k x‖ₑ ^ 2 ≤ ∑' k, ‖mik1_U m hm.1 u k x‖ₑ ^ 2 :=
            ENNReal.sum_le_tsum S
        _ = sqS (fun j => cv (dK (mik1_Th m) j) (h j)) x := by
          unfold sqS
          refine tsum_congr fun k => ?_
          show ‖mik1_U m hm.1 u k x‖ₑ ^ 2 =
            ‖cv (dK (mik1_Th m) k) (cv (symK (rhoT : 𝔼 → ℂ) k) ⇑u) x‖ₑ ^ 2
          rw [← mik1_U_eq_cv m hm.1 u k x]
    have h3 := hE3 Ad hAdne (fun j => dK (mik1_Th m) j) h hdec hhm
    obtain ⟨C0, hC00, hC0⟩ := sch_bdd u
    have hB : ∀ x, ‖u x‖ₑ ≤ ENNReal.ofReal C0 := fun x => by
      rw [← ofReal_norm]; exact ENNReal.ofReal_le_ofReal (hC0 x)
    have h4 := hCF (⇑u) (SchwartzMap.continuous _).measurable u.integrable (ENNReal.ofReal C0)
      ENNReal.ofReal_ne_top hB
    rw [show 2 * (p / 2) = p by ring] at h4
    calc ∫⁻ x, ‖(∑ k ∈ S, mik1_U m hm.1 u k) x‖ₑ ^ p
        ≤ (CS : ℝ≥0∞) * ∫⁻ x, (∑ k ∈ S, ‖mik1_U m hm.1 u k x‖ₑ ^ 2) ^ (p / 2) := h1
      _ ≤ (CS : ℝ≥0∞) * ∫⁻ x, sqS (fun j => cv (dK (mik1_Th m) j) (h j)) x ^ (p / 2) := by
          gcongr
      _ ≤ (CS : ℝ≥0∞) * (((Ad * Ad) ^ (p / 2) * CE) * ∫⁻ x, sqS h x ^ (p / 2)) := by gcongr
      _ ≤ (CS : ℝ≥0∞) * (((Ad * Ad) ^ (p / 2) * CE) * (CF * ∫⁻ x, ‖u x‖ₑ ^ p)) := by gcongr
      _ = _ := by
          rw [hAd', mik1_rpow_sq hp0.le]
          ring

end HRS.CZ.Mik
