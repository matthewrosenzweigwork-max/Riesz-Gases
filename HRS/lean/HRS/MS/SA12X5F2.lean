import HRS.MS.SA12X5N9
import HRS.MS.SA12X5L0
import HRS.MS.SA12X5L1
import HRS.MS.SA12X5L2
import HRS.MS.SA12X5L3
import HRS.MS.SA12X5F1
import HRS.MS.SA12X5D5
import HRS.MS.SA12X3C10B
import HRS.MS.SA12X3C15J
import HRS.MS.SA12X3C15L

/-!
# S.A.12 X5 F2: the cell energy of the difference source in terms of the uloc norm of `F`
-/

set_option autoImplicit false
set_option maxHeartbeats 6400000

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MH.AdjointRd.Phase2SA12X5

open HRS HRS.Whole HRS.Whole.AppendixA HRS.MH.AdjointRd HRS.MH.AdjointRd.Phase2SA12
  HRS.MH.AdjointRd.Phase2SA12Near HRS.MH.AdjointRd.Phase2SA12Construction

variable {d : ℕ}

theorem sa12x5_source_cell_bound (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (m : ℕ) (hm : 1 ≤ m)
    (MB Cb T : ℝ) (χ χh : Euc d → ℝ) (hχ : IsCutoffPair χ χh) (E : Finset (Fin d → ℤ))
    (hE : CoversBall8 E) :
    ∃ C L₁ : ℝ, 0 ≤ C ∧ ∀ (b : ℝ → Euc d → Euc d) (Ψ : ℝ → Euc d → Euc d),
      IsAdvectingDrift (m + 2) Cb T b → IsNegDriftFlow T b Ψ → ∀ τ ∈ Icc (0 : ℝ) T,
      ∀ (L : ℝ) (γ : Euc d → ℝ), L₁ ≤ L → HRS.Whole.AppendixALemmas.IsPeriodicRieszKernel d s L γ →
      ∀ M : Matrix (Fin d) (Fin d) ℝ, PDE.MatBound MB M → ∀ (ν₁ ν₂ : ℝ) (a F : Euc d → ℝ)
      (db : Euc d → Euc d), ContDiff ℝ ∞ a → ContDiff ℝ ∞ F → ContDiff ℝ ∞ db →
      (∀ (x : Euc d) (k : Fin d → ℤ), a (x + L • latticePt k) = a x) →
      (∀ (x : Euc d) (k : Fin d → ℤ), F (x + L • latticePt k) = F x) → BddJets m F →
      ∀ A : ℝ, 0 ≤ A → (∀ j ≤ m + 2, ∀ y, ‖iteratedFDeriv ℝ j a y‖ ≤ A) →
      (∀ j ≤ m + 2, ∀ x : Euc d, ∃ k : Fin d → ℤ,
        jbracket (x - L • latticePt k) ^ ((d : ℝ) + 3) * ‖iteratedFDeriv ℝ j a x‖ ≤ A) →
      (∀ j ≤ m, ∀ y, ‖iteratedFDeriv ℝ j db y‖ ≤ A) → ulocNormE (m + 2) χ F < ⊤ →
      ∀ z : Fin d → ℤ, cellEnergy m χ Ψ τ (cellPt d z)
          (fun x => (ν₁ - ν₂) * Laplacian.laplacian F x + inner ℝ (db x) (gradient F x) -
            perNonlocal L γ M a F x) ≤
        C * (|ν₁ - ν₂| + A) ^ 2 * (ulocNormE (m + 2) χ F).toReal ^ 2 := by
  obtain ⟨C9, L9, hC90, h9⟩ := sa12x5_nonlocal_diff_bound hd hs0 hsd m hm MB Cb T χ χh hχ E hE
  obtain ⟨K2, hK2, hK2c⟩ := sa12x3_cellEnergy_le_uloc hd (m + 2) Cb T χ χh hχ
  obtain ⟨Nm, hNm, hmass⟩ := sa12x3_cellMass_le hd m χ hχ.1
  set G0 : ℝ := sa12x5_C0 d m with hG0
  have hG00 : 0 ≤ G0 := sa12x5_C0_nonneg d m
  set Cf : ℝ := 3 * (d + G0 + C9 * (E.card + C9 * Nm)) * K2 with hCf
  refine ⟨Cf, max L9 1, by positivity, ?_⟩
  intro b Ψ hb hΨ τ hτ L γ hL hγ M hM ν₁ ν₂ a F db ha hF hdb hap hFp hFB A hA0 haj had hdbj hU z
  have hb0 : IsAdvectingDrift m Cb T b := sa12x5_advDrift_mono (sa12x5_advDrift_mono hb)
  have hL9 : L9 ≤ L := (le_max_left _ _).trans hL
  have hL0 : 0 < L := lt_of_lt_of_le one_pos ((le_max_right _ _).trans hL)
  have hT : 0 ≤ T := hτ.1.trans hτ.2
  set U : ℝ := (ulocNormE (m + 2) χ F).toReal with hUdef
  have hUfin : ulocNormE (m + 2) χ F = ENNReal.ofReal U := (ENNReal.ofReal_toReal hU.ne).symm
  set Q : ℝ := K2 * U ^ 2 with hQ
  have hQ0 : 0 ≤ Q := by positivity
  have hcell : ∀ c : Euc d, cellEnergy (m + 2) χ Ψ τ c F ≤ Q := by
    intro c
    have h := hK2c b Ψ hb hΨ τ hτ F hF c
    rw [hUfin] at h
    have e : ENNReal.ofReal K2 * ENNReal.ofReal U ^ 2 = ENNReal.ofReal Q := by
      rw [hQ, ← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_mul hK2.le]
    rw [e] at h
    exact (ENNReal.ofReal_le_ofReal_iff hQ0).1 h
  set w : Euc d → ℝ := advCutoff χ Ψ τ (cellPt d z) with hw
  obtain ⟨Bc, Rc, -, -, hfc⟩ := advected_cutoff_jets d hd m Cb T χ χh hχ
  have hcut := hfc b Ψ hb0 hΨ τ hτ (cellPt d z)
  have hwc : Continuous w := hcut.1.1.continuous
  have hwcs : HasCompactSupport w :=
    sa12x2_advCutoff_hasCompactSupport hT hb0 hΨ hτ hχ.1.2.1 (cellPt d z)
  -- the three pieces
  have hS1 : ContDiff ℝ ∞ (fun x => (ν₁ - ν₂) * Laplacian.laplacian F x) :=
    contDiff_const.mul (sa12x5_lap_smooth hF)
  have hS2 : ContDiff ℝ ∞ (fun x => inner ℝ (db x) (gradient F x)) :=
    hdb.inner ℝ (sa12y_grad_contDiff hF)
  have hS3 : ContDiff ℝ ∞ (fun x => perNonlocal L γ M a F x) :=
    sa12x5_perNonlocal_smooth hL0 hγ.locInt hγ.periodic M ha hF hap hFp
  have hsum := sa12x5_jetSq_sum_le m hwc hwcs hS1 hS2 hS3
  have p1 : jetSq m w (fun x => (ν₁ - ν₂) * Laplacian.laplacian F x) ≤ (ν₁ - ν₂) ^ 2 * (d * Q) := by
    rw [sa12x5_jetSq_const_mul' m w (sa12x5_lap_smooth hF)]
    refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
    refine (sa12x5_jetSq_lap_le m hwc hwcs hF).trans ?_
    exact mul_le_mul_of_nonneg_left (hcell (cellPt d z)) (Nat.cast_nonneg _)
  have p2 : jetSq m w (fun x => inner ℝ (db x) (gradient F x)) ≤ G0 * A ^ 2 * Q := by
    refine (sa12x5_jetSq_drift_le m hwc hwcs hF hdb hA0 hdbj).trans ?_
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    exact (sa12x5_jetSq_mono (Nat.le_succ (m + 1)) w F).trans (hcell (cellPt d z))
  -- the nonlocal term
  obtain ⟨Kc, hrow, hcol, hKc⟩ := h9 b Ψ hb0 hΨ τ hτ L γ hL9 hγ M hM a F ha hF hap hFp hFB A hA0 haj had
  have hfl := HRS.MS.UniqC3.uc3_flowFacts hT hb0 hΨ
  have hΨc : Continuous (Ψ τ) := (hfl.contDiff τ hτ).continuous
  have hΨi : Continuous (Function.invFun (Ψ τ)) := (hfl.contDiff_inv τ hτ).continuous
  have hbij := hΨ.bij τ hτ
  have hQm : ∀ z'' : Fin d → ℤ, cellEnergy m χ Ψ τ (cellPt d z'') F ≤ Q := fun z'' =>
    (sa12x5_jetSq_mono (Nat.le_add_right m 2) _ F).trans (hcell _)
  have hmz : ∀ z', cellMass m Ψ τ z' F ≤ Nm * Q := fun z' =>
    hmass Ψ τ hbij hΨc hΨi F hF
      (fun z'' j idx => sa12x3_adv_cut_integrable hχ.1.1 hχ.1.2.1 hb0 hΨ hτ (cellPt d z'') hF idx)
      Q hQm z'
  have hmassterm : (∑' z', (Kc z z' : ℝ≥0∞) * ENNReal.ofReal (cellMass m Ψ τ z' F)).toReal ≤
      C9 * (Nm * Q) := by
    have h1 : ∑' z', (Kc z z' : ℝ≥0∞) * ENNReal.ofReal (cellMass m Ψ τ z' F) ≤
        ENNReal.ofReal C9 * ENNReal.ofReal (Nm * Q) := by
      calc _ ≤ ∑' z', (Kc z z' : ℝ≥0∞) * ENNReal.ofReal (Nm * Q) :=
            ENNReal.tsum_le_tsum fun z' => by gcongr; exact hmz z'
        _ = (∑' z', (Kc z z' : ℝ≥0∞)) * ENNReal.ofReal (Nm * Q) := ENNReal.tsum_mul_right
        _ ≤ ENNReal.ofReal C9 * ENNReal.ofReal (Nm * Q) := by
            gcongr
            exact le_trans (le_iSup (fun z => ∑' z', (Kc z z' : ℝ≥0∞)) z) hrow
    have h2 := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top) h1
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hC90, ENNReal.toReal_ofReal (by positivity)] at h2
  have hEsum : ∑ k ∈ E, cellEnergy (m + 2) χ Ψ τ (cellPt d (z + k)) F ≤ E.card * Q := by
    calc _ ≤ ∑ _k ∈ E, Q := Finset.sum_le_sum fun k _ => hcell _
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
  have p3 : jetSq m w (fun x => perNonlocal L γ M a F x) ≤ C9 * A ^ 2 * (E.card * Q + C9 * (Nm * Q)) := by
    refine (hKc z).trans ?_
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    linarith
  -- assembly
  set X : ℝ := (|ν₁ - ν₂| + A) ^ 2 with hX
  have h1 : (ν₁ - ν₂) ^ 2 ≤ X := by
    rw [hX]; nlinarith [sq_abs (ν₁ - ν₂), abs_nonneg (ν₁ - ν₂)]
  have h2 : A ^ 2 ≤ X := by
    rw [hX]; nlinarith [abs_nonneg (ν₁ - ν₂)]
  have hX0 : 0 ≤ X := sq_nonneg _
  have e1 : (ν₁ - ν₂) ^ 2 * (d * Q) ≤ X * (d * Q) := mul_le_mul_of_nonneg_right h1 (by positivity)
  have e2 : G0 * A ^ 2 * Q ≤ G0 * X * Q := by
    have := mul_le_mul_of_nonneg_left h2 hG00
    exact mul_le_mul_of_nonneg_right this hQ0
  have e3 : C9 * A ^ 2 * (E.card * Q + C9 * (Nm * Q)) ≤ C9 * X * (E.card * Q + C9 * (Nm * Q)) := by
    have := mul_le_mul_of_nonneg_left h2 hC90
    exact mul_le_mul_of_nonneg_right this
      (add_nonneg (mul_nonneg (Nat.cast_nonneg _) hQ0) (mul_nonneg hC90 (mul_nonneg hNm hQ0)))
  show jetSq m w (fun x => (ν₁ - ν₂) * Laplacian.laplacian F x + inner ℝ (db x) (gradient F x) -
    perNonlocal L γ M a F x) ≤ _
  calc _ ≤ 3 * (jetSq m w (fun x => (ν₁ - ν₂) * Laplacian.laplacian F x) +
        jetSq m w (fun x => inner ℝ (db x) (gradient F x)) +
        jetSq m w (fun x => perNonlocal L γ M a F x)) := hsum
    _ ≤ 3 * (X * (d * Q) + G0 * X * Q + C9 * X * (E.card * Q + C9 * (Nm * Q))) := by linarith
    _ = Cf * X * U ^ 2 := by rw [hCf, hQ]; ring

end HRS.MH.AdjointRd.Phase2SA12X5
