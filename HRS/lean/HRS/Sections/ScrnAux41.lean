import HRS.Sections.ScrnAux40

/-!
# Packet SCRN, part 41: the covariation discrepancy bound for the transported mesoscopic tests

`scrn_cov_final`: `covDiscrepancy ≤ p² · (2 Cq/(b₋ c₁)) (K_L N^{-1/d} ℓ^{-d-3+min(q,2)} + K_H √o_N ℓ^{-(d+q)/2-2+min(q,2)})`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators ComplexConjugate

namespace HRS

open HRS.Main.A8P PDE

variable {d : ℕ}

local notation "ℝ^" p => EuclideanSpace ℝ (Fin p)

theorem scrn_cov_final (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (β : ℝ) (hβ : 0 < β)
    {N : ℕ} (hN : 2 ≤ N) {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {X₀ : Ω → Config d N} {W : ℝ≥0 → Ω → (Fin N → Euc d)}
    {X : ℝ≥0 → Ω → Config d N} (hfl : ScrnFlow d hs0 hsd β hβ N P X₀ W X)
    {C₀ Cq : ℝ} (hC₀ : 0 ≤ C₀) (hcom : A8CommSpec d s C₀ Cq) (hCq : 0 ≤ Cq) {bm bp ℓ CG : ℝ}
    (hbm : 0 < bm) (hbp : 0 < bp) (hℓ : 0 < ℓ) (hCG : 0 ≤ CG) (hbN : bm ≤ β * ℓ ^ ((d : ℝ) - s))
    {Tm : ℝ} (hTm0 : 0 < Tm) {p : ℕ} {ts : Fin p → ℝ} {ψ : Fin p → Torus d → ℝ}
    {f : Fin p → ℝ → Torus d → ℝ}
    (htr : ScrnTr d hs0 hsd hβ ℓ (scrnLamS d s bp ℓ) CG ts ψ f)
    (htsT : ∀ a, ts a ∈ Set.Icc 0 Tm) :
    covDiscrepancyMatrix P Tm
        (killedCovMatrix (fun a => scrnPhi (PDE.mfData d s hs0 hsd (fun _ => 0) β hβ) (Real.sqrt N)
          (ts a) (f a) X) ts)
        (scrnSig ts (scrnGc ts f) (2 * (PDE.mfData d s hs0 hsd (fun _ => 0) β hβ).invβ)) ≤
      (p : ℝ) ^ 2 * (2 * Cq / (bm * min (rieszConst d s) bp⁻¹)) *
        ((2 * d * CG ^ 2) * ((N : ℝ) ^ (-(1 : ℝ) / d) * ℓ ^ (-(d : ℝ) - 3 + min ((d : ℝ) - s) 2)) +
          (2 * d * 2 ^ (3 * (((d : ℝ) - s) / 2) / 2) * CG ^ 2) * (Real.sqrt (oN d s C₀ N) *
            ℓ ^ (-((d : ℝ) + ((d : ℝ) - s)) / 2 - 2 + min ((d : ℝ) - s) 2))) := by
  set D := PDE.mfData d s hs0 hsd (fun _ => 0) β hβ with hD
  set lamS := scrnLamS d s bp ℓ with hlamS
  have hlam := scrnLamS_pos hd hs0 hsd hbp hℓ
  have hc1 : 0 < min (rieszConst d s) bp⁻¹ :=
    lt_min (rieszConst_pos hd hs0 hsd) (inv_pos.2 hbp)
  set CL : ℝ := 2 * d * CG ^ 2 * ℓ ^ (-(d : ℝ) - 3) with hCL
  set eH : ℝ := -((d : ℝ) + ((d : ℝ) - s)) / 2 - 2 with heH
  set CH : ℝ := 2 * d * 2 ^ (3 * (((d : ℝ) - s) / 2) / 2) * CG ^ 2 * ℓ ^ eH with hCH
  have hpl : 0 ≤ ℓ ^ (-(d : ℝ) - 3) := Real.rpow_nonneg hℓ.le _
  have hph : 0 ≤ ℓ ^ eH := Real.rpow_nonneg hℓ.le _
  have hCL0 : 0 ≤ CL := by positivity
  have hCH0 : 0 ≤ CH := by positivity
  set Lf : Fin p → Fin p → ℝ → ℝ := fun a b r => CL * (scrnTheta lamS (ts a) r * scrnTheta lamS (ts b) r)
    with hLf
  set Hf : Fin p → Fin p → ℝ → ℝ := fun a b r => CH * (scrnTheta lamS (ts a) r * scrnTheta lamS (ts b) r)
    with hHf
  have hLc : ∀ a b, Continuous (Lf a b) := fun a b => by
    have := scrnTheta_cont lamS (ts a)
    have := scrnTheta_cont lamS (ts b)
    simp only [hLf]; fun_prop
  have hHc : ∀ a b, Continuous (Hf a b) := fun a b => by
    have := scrnTheta_cont lamS (ts a)
    have := scrnTheta_cont lamS (ts b)
    simp only [hHf]; fun_prop
  have hnn : ∀ a b r, 0 ≤ scrnTheta lamS (ts a) r * scrnTheta lamS (ts b) r := fun a b r =>
    mul_nonneg (scrnTheta_pos _ _ _).le (scrnTheta_pos _ _ _).le
  have hb := scrn_cov_bound hd hs0 hsd β hβ hN hfl (hfl.filt.choose_spec.choose_spec) hcom hCq hTm0
    ts htsT f Lf Hf (fun a b => (hLc a b).measurable) (fun a b => (hHc a b).measurable)
    (fun a b r _ => mul_nonneg hCL0 (hnn a b r)) (fun a b r _ => mul_nonneg hCH0 (hnn a b r))
    (fun a b => (hLc a b).integrableOn_Icc.mono_set Ico_subset_Icc_self)
    (fun a b => (hHc a b).integrableOn_Icc.mono_set Ico_subset_Icc_self)
    (fun a b r hr => by
      have hra : r ∈ Set.Icc 0 (ts a) := ⟨hr.1, (lt_min_iff.1 hr.2).1.le⟩
      have hrb : r ∈ Set.Icc 0 (ts b) := ⟨hr.1, (lt_min_iff.1 hr.2).2.le⟩
      obtain ⟨h1, h2, h3⟩ := scrn_GB_pair hsd hℓ (scrnTheta_pos lamS (ts a) r).le
        (scrnTheta_pos lamS (ts b) r).le (htr.gb a r hra) (htr.gb b r hrb)
      exact ⟨h1, h2, h3⟩)
  refine hb.trans ?_
  have hts0 := htr.ts0
  have hiL : ∀ j i, ∫ r in Set.Ico 0 (min (ts j) (ts i)), Lf j i r ≤ CL / lamS := fun j i =>
    scrn_LH_int hlam (hts0 j) (hts0 i) hCL0
  have hiH : ∀ j i, ∫ r in Set.Ico 0 (min (ts j) (ts i)), Hf j i r ≤ CH / lamS := fun j i =>
    scrn_LH_int hlam (hts0 j) (hts0 i) hCH0
  set Nn : ℝ := (N : ℝ) ^ (-(1 : ℝ) / d) with hNn
  set so : ℝ := Real.sqrt (oN d s C₀ N) with hso
  have hNn0 : 0 ≤ Nn := Real.rpow_nonneg (Nat.cast_nonneg N) _
  have hso0 : 0 ≤ so := Real.sqrt_nonneg _
  have hinv : D.invβ = β⁻¹ := rfl
  have hq0 : 0 < ℓ ^ ((d : ℝ) - s) := Real.rpow_pos_of_pos hℓ _
  have hbeta : β⁻¹ ≤ ℓ ^ ((d : ℝ) - s) / bm := by
    rw [inv_eq_one_div, div_le_div_iff₀ hβ hbm]
    nlinarith
  have hbeta0 : 0 ≤ β⁻¹ := inv_nonneg.2 hβ.le
  have hterm : ∀ i j : Fin p, 2 * D.invβ * Cq * ((∫ r in Set.Ico 0 (min (ts j) (ts i)), Lf j i r) * Nn +
      (∫ r in Set.Ico 0 (min (ts j) (ts i)), Hf j i r) * so) ≤
      2 * (ℓ ^ ((d : ℝ) - s) / bm) * Cq * ((CL / lamS) * Nn + (CH / lamS) * so) := by
    intro i j
    rw [hinv]
    have h1 := hiL j i
    have h2 := hiH j i
    have hI : (∫ r in Set.Ico 0 (min (ts j) (ts i)), Lf j i r) * Nn +
        (∫ r in Set.Ico 0 (min (ts j) (ts i)), Hf j i r) * so ≤ (CL / lamS) * Nn + (CH / lamS) * so := by
      gcongr
    have hR0 : 0 ≤ (CL / lamS) * Nn + (CH / lamS) * so := by positivity
    calc 2 * β⁻¹ * Cq * _ ≤ 2 * β⁻¹ * Cq * ((CL / lamS) * Nn + (CH / lamS) * so) :=
          mul_le_mul_of_nonneg_left hI (by positivity)
      _ ≤ _ := by gcongr
  calc _ ≤ ∑ _i : Fin p, ∑ _j : Fin p, 2 * (ℓ ^ ((d : ℝ) - s) / bm) * Cq *
        ((CL / lamS) * Nn + (CH / lamS) * so) := by
        refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hterm i j
    _ = (p : ℝ) ^ 2 * (2 * (ℓ ^ ((d : ℝ) - s) / bm) * Cq *
        ((CL / lamS) * Nn + (CH / lamS) * so)) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring
    _ = _ := by
        have hL := scrnLamS_inv hd hs0 hsd hbp hℓ (-(d : ℝ) - 3)
        have hH := scrnLamS_inv hd hs0 hsd hbp hℓ eH
        rw [← hlamS] at hL hH
        have hCL' : CL / lamS = 2 * d * CG ^ 2 * (ℓ ^ (-(d : ℝ) - 3) / lamS) := by
          simp only [hCL]; ring
        have hCH' : CH / lamS = 2 * d * 2 ^ (3 * (((d : ℝ) - s) / 2) / 2) * CG ^ 2 * (ℓ ^ eH / lamS) := by
          simp only [hCH]; ring
        rw [hCL', hCH', hL, hH]
        have hqL : ℓ ^ ((d : ℝ) - s) * ℓ ^ (-(d : ℝ) - 3 - max ((d : ℝ) - s - 2) 0) =
            ℓ ^ (-(d : ℝ) - 3 + min ((d : ℝ) - s) 2) := by
          rw [← Real.rpow_add hℓ]; congr 1
          have := scrn_min_q ((d : ℝ) - s); linarith
        have hqH : ℓ ^ ((d : ℝ) - s) * ℓ ^ (eH - max ((d : ℝ) - s - 2) 0) =
            ℓ ^ (eH + min ((d : ℝ) - s) 2) := by
          rw [← Real.rpow_add hℓ]; congr 1
          have := scrn_min_q ((d : ℝ) - s); linarith
        have hqL' := hqL
        have hqH' := hqH
        field_simp
        rw [← hqL, ← hqH]
        ring

end HRS
