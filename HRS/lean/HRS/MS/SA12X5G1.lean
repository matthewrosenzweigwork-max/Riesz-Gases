import HRS.MS.SA12X5N9
import HRS.MS.SA12X5L3
import HRS.MS.SA12X5L2
import HRS.MS.SA12X5L1
import HRS.MS.SA12X4W5
import HRS.MS.SA12X4W4
import HRS.MS.SA12X3C15L

/-!
# S.A.12 X5 G1: the weighted source bound

The cell energies of the source `S = (ν₁-ν₂)ΔF + ⟨db,∇F⟩ - 𝒢_a[F]` are bounded in the weighted `ℓ¹` sum by
`C (|ν₁-ν₂| + A)² * cellWeighted (m+2) F`: per cell from N9 and the LOC lemmas, then summed with the shifted-weight
comparison (W2) and the weighted Schur column bound / weighted cell mass (W4, W5).
-/

set_option autoImplicit false
set_option maxHeartbeats 6400000

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MH.AdjointRd.Phase2SA12X5

open HRS HRS.Whole HRS.Whole.AppendixA HRS.MH.AdjointRd HRS.MH.AdjointRd.Phase2SA12Near
  HRS.MH.AdjointRd.Phase2SA12Construction HRS.MH.AdjointRd.Phase2SA12X4 HRS.MS.UniqT3
  HRS.MH.AdjointRd.Phase2SA12

variable {d : ℕ}

theorem sa12x5_g1_lap_smooth {F : Euc d → ℝ} (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ (fun x => Laplacian.laplacian F x) := by
  have hfun : (fun x => Laplacian.laplacian F x) = fun y => ∑ i ∈ Finset.univ, (1 : ℝ) * D1 i (D1 i F) y := by
    funext y; rw [lap_eq (sa12z3_cd_of_inf hF 2) y]; simp
  rw [hfun]
  exact ContDiff.sum fun i _ => contDiff_const.mul (sa12x5_loc_D1_smooth i (sa12x5_loc_D1_smooth i hF))

theorem sa12x5_g1_source_smooth {F : Euc d → ℝ} (hF : ContDiff ℝ ∞ F) {db : Euc d → Euc d}
    (hdb : ContDiff ℝ ∞ db) (c : ℝ) :
    ContDiff ℝ ∞ (fun x => c * Laplacian.laplacian F x) ∧
      ContDiff ℝ ∞ (fun x => inner ℝ (db x) (gradient F x)) := by
  constructor
  · exact contDiff_const.mul (sa12x5_g1_lap_smooth hF)
  · have hfun : (fun x => inner ℝ (db x) (gradient F x)) = fun y => ∑ i : Fin d, db y i * D1 i F y := by
      funext y; exact sa12x5_loc_inner_expand db y
    rw [hfun]
    exact ContDiff.sum fun i _ => (sa12x5_loc_coord_smooth i hdb).mul (sa12x5_loc_D1_smooth i hF)

theorem sa12x5_source_weighted_bound (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (m : ℕ) (hm : 1 ≤ m)
    (MB Cb T : ℝ) (χ χh : Euc d → ℝ) (hχu : IsUlocCutoff χ) (hχ : IsCutoffPair χ χh)
    (E : Finset (Fin d → ℤ)) (hE : CoversBall8 E) :
    ∃ C L₁ : ℝ, 0 ≤ C ∧ ∀ (b : ℝ → Euc d → Euc d) (Ψ : ℝ → Euc d → Euc d),
      IsAdvectingDrift m Cb T b → IsNegDriftFlow T b Ψ → ∀ τ ∈ Icc (0 : ℝ) T,
      ∀ (L : ℝ) (γ : Euc d → ℝ), L₁ ≤ L → HRS.Whole.AppendixALemmas.IsPeriodicRieszKernel d s L γ →
      ∀ M : Matrix (Fin d) (Fin d) ℝ, PDE.MatBound MB M → ∀ (ν₁ ν₂ : ℝ) (a db F : _),
      ContDiff ℝ ∞ a → ContDiff ℝ ∞ F → (∀ (x : Euc d) (k : Fin d → ℤ), a (x + L • latticePt k) = a x) →
      (∀ (x : Euc d) (k : Fin d → ℤ), F (x + L • latticePt k) = F x) → BddJets m F →
      ContDiff ℝ ∞ (db : Euc d → Euc d) → ContDiff ℝ ∞ (fun x => perNonlocal L γ M a F x) →
      ∀ A : ℝ, 0 ≤ A → (∀ j ≤ m + 2, ∀ y, ‖iteratedFDeriv ℝ j a y‖ ≤ A) →
      (∀ j ≤ m + 2, ∀ x : Euc d, ∃ k : Fin d → ℤ,
        jbracket (x - L • latticePt k) ^ ((d : ℝ) + 3) * ‖iteratedFDeriv ℝ j a x‖ ≤ A) →
      (∀ j ≤ m, ∀ y, ‖iteratedFDeriv ℝ j db y‖ ≤ A) →
      ∑' z, ENNReal.ofReal (jbracket (cellPt d z) ^ (-((d : ℝ) + 3))) *
          ENNReal.ofReal (cellEnergy m χ Ψ τ (cellPt d z)
            (fun x => (ν₁ - ν₂) * Laplacian.laplacian F x + inner ℝ (db x) (gradient F x) -
              perNonlocal L γ M a F x)) ≤
        ENNReal.ofReal (C * (|ν₁ - ν₂| + A) ^ 2) * cellWeighted (m + 2) χ Ψ τ F := by
  classical
  set E' : Finset (Fin d → ℤ) := insert 0 E with hE'
  have hE'c : CoversBall8 E' := fun x hx => by
    obtain ⟨k, hk, h⟩ := Set.mem_iUnion₂.1 (hE hx)
    exact Set.mem_iUnion₂.2 ⟨k, Finset.mem_insert_of_mem hk, h⟩
  obtain ⟨C9, L9, hC90, h9⟩ := sa12x5_nonlocal_diff_bound hd hs0 hsd m hm MB Cb T χ χh hχ E' hE'c
  obtain ⟨cE, hcE0, hcE⟩ := sa12x4_shift_weight (d := d) E'
  obtain ⟨C12, hC120, hC12⟩ := sa12x4_cellMass_weighted hd m χ hχu
  set Kw : ℝ := (⌈Real.sqrt d⌉ : ℝ) ^ ((d : ℝ) + 3) with hKw
  have hKw0 : 0 ≤ Kw := Real.rpow_nonneg (by
    have := HRS.MH.AdjointRd.Phase2SA12Construction.sa12c12_kappa_ge hd; linarith) _
  set K : ℝ := 3 * ((d : ℝ) + sa12x5_C0 d m + 2 * C9) with hK
  have hK0 : 0 ≤ K := by
    have := sa12x5_C0_nonneg d m
    positivity
  refine ⟨K * (cE + Kw * C9 * C12), L9, by positivity, ?_⟩
  intro b Ψ hb hΨ τ hτ L γ hL hγ M hM ν₁ ν₂ a db F ha hF hap hFp hFB hdb hNL A hA0 hAs hAd hAb
  have hT : 0 ≤ T := hτ.1.trans hτ.2
  have hfl := HRS.MS.UniqC3.uc3_flowFacts hT hb hΨ
  obtain ⟨Kc, hrow, hcol, hKc⟩ := h9 b Ψ hb hΨ τ hτ L γ hL hγ M hM a F ha hF hap hFp hFB A hA0 hAs hAd
  set Δ : ℝ := |ν₁ - ν₂| + A with hΔ
  have hΔ0 : 0 ≤ Δ := by positivity
  have hν2 : (ν₁ - ν₂) ^ 2 ≤ Δ ^ 2 := by
    have : |ν₁ - ν₂| ≤ Δ := by rw [hΔ]; linarith
    calc (ν₁ - ν₂) ^ 2 = |ν₁ - ν₂| ^ 2 := (sq_abs _).symm
      _ ≤ Δ ^ 2 := pow_le_pow_left₀ (abs_nonneg _) this 2
  have hA2 : A ^ 2 ≤ Δ ^ 2 := pow_le_pow_left₀ hA0 (by rw [hΔ]; linarith [abs_nonneg (ν₁ - ν₂)]) 2
  set fz : (Fin d → ℤ) → ℝ := fun z => cellEnergy (m + 2) χ Ψ τ (cellPt d z) F with hfz
  have hfz0 : ∀ z, 0 ≤ fz z := fun z => sa12x5_jetSq_nonneg _ _ _
  set massT : (Fin d → ℤ) → ℝ≥0∞ := fun z => ∑' z', (Kc z z' : ℝ≥0∞) * ENNReal.ofReal (cellMass m Ψ τ z' F)
    with hmassT
  -- per cell
  have hcell : ∀ z, cellEnergy m χ Ψ τ (cellPt d z)
      (fun x => (ν₁ - ν₂) * Laplacian.laplacian F x + inner ℝ (db x) (gradient F x) -
        perNonlocal L γ M a F x) ≤
      K * Δ ^ 2 * (∑ k ∈ E', fz (z + k) + (massT z).toReal) := by
    intro z
    set w : Euc d → ℝ := advCutoff χ Ψ τ (cellPt d z) with hw
    have hwc : Continuous w :=
      hχ.1.1.continuous.comp ((hfl.contDiff_inv τ hτ).continuous.sub continuous_const)
    have hwk : HasCompactSupport w :=
      sa12x2_advCutoff_hasCompactSupport hT hb hΨ hτ hχ.1.2.1 (cellPt d z)
    obtain ⟨hs1, hs2⟩ := sa12x5_g1_source_smooth hF hdb (ν₁ - ν₂)
    have h3 := sa12x5_jetSq_sum_le m hwc hwk hs1 hs2 hNL
    have h1 : jetSq m w (fun x => (ν₁ - ν₂) * Laplacian.laplacian F x) ≤ (ν₁ - ν₂) ^ 2 * ((d : ℝ) * fz z) := by
      rw [sa12x5_jetSq_const_mul' m w (sa12x5_g1_lap_smooth hF) (ν₁ - ν₂)]
      exact mul_le_mul_of_nonneg_left (sa12x5_jetSq_lap_le m hwc hwk hF) (sq_nonneg _)
    have h2 : jetSq m w (fun x => inner ℝ (db x) (gradient F x)) ≤ sa12x5_C0 d m * A ^ 2 * fz z :=
      (sa12x5_jetSq_drift_le m hwc hwk hF hdb hA0 hAb).trans
        (mul_le_mul_of_nonneg_left (sa12x5_jetSq_mono (by omega) w F)
          (mul_nonneg (sa12x5_C0_nonneg d m) (sq_nonneg _)))
    have h4 := hKc z
    have hf0 : fz z ≤ ∑ k ∈ E', fz (z + k) := by
      have := Finset.single_le_sum (f := fun k => fz (z + k)) (fun k _ => hfz0 _)
        (Finset.mem_insert_self (0 : Fin d → ℤ) E)
      simpa using this
    have hSum0 : 0 ≤ ∑ k ∈ E', fz (z + k) := Finset.sum_nonneg fun k _ => hfz0 _
    have hm0 : 0 ≤ (massT z).toReal := ENNReal.toReal_nonneg
    have hC0 := sa12x5_C0_nonneg d m
    have e1 : jetSq m w (fun x => (ν₁ - ν₂) * Laplacian.laplacian F x + inner ℝ (db x) (gradient F x) -
        perNonlocal L γ M a F x) = cellEnergy m χ Ψ τ (cellPt d z) _ := rfl
    show jetSq m w _ ≤ _
    refine h3.trans ?_
    have hmain : jetSq m w (fun x => perNonlocal L γ M a F x) ≤ C9 * Δ ^ 2 * (∑ k ∈ E', fz (z + k) + (massT z).toReal) :=
      h4.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hA2 hC90) (add_nonneg hSum0 hm0))
    have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    have hX : fz z ≤ ∑ k ∈ E', fz (z + k) + (massT z).toReal := by linarith
    have t1 : (ν₁ - ν₂) ^ 2 * ((d : ℝ) * fz z) ≤ Δ ^ 2 * ((d : ℝ) * (∑ k ∈ E', fz (z + k) + (massT z).toReal)) :=
      mul_le_mul hν2 (mul_le_mul_of_nonneg_left hX hd0) (mul_nonneg hd0 (hfz0 z)) (sq_nonneg _)
    have t2' : sa12x5_C0 d m * fz z ≤ sa12x5_C0 d m * (∑ k ∈ E', fz (z + k) + (massT z).toReal) :=
      mul_le_mul_of_nonneg_left hX hC0
    have t2 : sa12x5_C0 d m * A ^ 2 * fz z ≤ Δ ^ 2 * (sa12x5_C0 d m * (∑ k ∈ E', fz (z + k) + (massT z).toReal)) := by
      have := mul_le_mul hA2 t2' (mul_nonneg hC0 (hfz0 z)) (sq_nonneg _)
      linarith
    nlinarith [h1, h2, hmain, t1, t2, hSum0, hm0, mul_nonneg (sq_nonneg Δ) hSum0, mul_nonneg (sq_nonneg Δ) hm0,
      mul_nonneg hC90 (mul_nonneg (sq_nonneg Δ) (add_nonneg hSum0 hm0))]
  -- weights
  have hbij := hΨ.bij τ hτ
  have hmassW := hC12 Ψ τ hbij (hfl.contDiff τ hτ).continuous (hfl.contDiff_inv τ hτ).continuous F hF
    (fun z j idx => sa12x3_adv_cut_integrable hχ.1.1 hχ.1.2.1 hb hΨ hτ (cellPt d z) hF idx)
  have hmass : ∑' z', ENNReal.ofReal (cellWeight d z') * ENNReal.ofReal (cellMass m Ψ τ z' F) ≤
      ENNReal.ofReal C12 * ∑' z, ENNReal.ofReal (jbracket (cellPt d z) ^ (-((d : ℝ) + 3))) *
        ENNReal.ofReal (fz z) := by
    refine hmassW.trans (mul_le_mul_of_nonneg_left (ENNReal.tsum_le_tsum fun z => ?_) bot_le)
    exact mul_le_mul_of_nonneg_left (ENNReal.ofReal_le_ofReal (sa12x5_jetSq_mono (by omega) _ _)) bot_le
  have hrate := sa12x4_weighted_rate_dom (d := d) E' ∅ (c7 := cE) (c9 := 0) hcE
    (fun u => by simp) 0 0 1 Kw C9 C12 hC120 le_rfl le_rfl zero_le_one hKw0 hC90 hcE0 le_rfl
    (fun z => sa12x4_wt_le_cellWeight hd z) fz (fun _ => 0) hfz0 (fun _ => le_rfl)
    (fun z' => ENNReal.ofReal (cellMass m Ψ τ z' F)) Kc hcol hmass
  have hpt : ∀ z, ENNReal.ofReal (cellEnergy m χ Ψ τ (cellPt d z)
      (fun x => (ν₁ - ν₂) * Laplacian.laplacian F x + inner ℝ (db x) (gradient F x) -
        perNonlocal L γ M a F x)) ≤
      ENNReal.ofReal (K * Δ ^ 2) * (ENNReal.ofReal (0 * ∑ k ∈ (∅ : Finset (Fin d → ℤ)), fz (z + k)) +
        ENNReal.ofReal (0 * ∑ k ∈ E', (fun _ : Fin d → ℤ => (0 : ℝ)) (z + k)) +
        ENNReal.ofReal (1 * ∑ k ∈ E', fz (z + k)) +
        ENNReal.ofReal 1 * ∑' z', (Kc z z' : ℝ≥0∞) * ENNReal.ofReal (cellMass m Ψ τ z' F)) := by
    intro z
    have e1 : (ENNReal.ofReal (0 * ∑ k ∈ (∅ : Finset (Fin d → ℤ)), fz (z + k)) +
        ENNReal.ofReal (0 * ∑ k ∈ E', (fun _ : Fin d → ℤ => (0 : ℝ)) (z + k)) +
        ENNReal.ofReal (1 * ∑ k ∈ E', fz (z + k)) +
        ENNReal.ofReal 1 * ∑' z', (Kc z z' : ℝ≥0∞) * ENNReal.ofReal (cellMass m Ψ τ z' F)) =
        ENNReal.ofReal (∑ k ∈ E', fz (z + k)) + massT z := by simp [hmassT]
    rw [e1]
    refine (ENNReal.ofReal_le_ofReal (hcell z)).trans ?_
    rw [ENNReal.ofReal_mul (by positivity)]
    refine mul_le_mul_of_nonneg_left ?_ bot_le
    rw [ENNReal.ofReal_add (Finset.sum_nonneg fun k _ => hfz0 _) ENNReal.toReal_nonneg]
    exact add_le_add le_rfl ENNReal.ofReal_toReal_le
  calc ∑' z, ENNReal.ofReal (jbracket (cellPt d z) ^ (-((d : ℝ) + 3))) *
        ENNReal.ofReal (cellEnergy m χ Ψ τ (cellPt d z)
          (fun x => (ν₁ - ν₂) * Laplacian.laplacian F x + inner ℝ (db x) (gradient F x) -
            perNonlocal L γ M a F x))
      ≤ ∑' z, ENNReal.ofReal (K * Δ ^ 2) * (ENNReal.ofReal (jbracket (cellPt d z) ^ (-((d : ℝ) + 3))) *
        (ENNReal.ofReal (0 * ∑ k ∈ (∅ : Finset (Fin d → ℤ)), fz (z + k)) +
        ENNReal.ofReal (0 * ∑ k ∈ E', (fun _ : Fin d → ℤ => (0 : ℝ)) (z + k)) +
        ENNReal.ofReal (1 * ∑ k ∈ E', fz (z + k)) +
        ENNReal.ofReal 1 * ∑' z', (Kc z z' : ℝ≥0∞) * ENNReal.ofReal (cellMass m Ψ τ z' F))) :=
        ENNReal.tsum_le_tsum fun z => by
          calc _ ≤ ENNReal.ofReal (jbracket (cellPt d z) ^ (-((d : ℝ) + 3))) * (ENNReal.ofReal (K * Δ ^ 2) * _) :=
                mul_le_mul_of_nonneg_left (hpt z) bot_le
            _ = _ := by ring
    _ = ENNReal.ofReal (K * Δ ^ 2) * ∑' z, ENNReal.ofReal (jbracket (cellPt d z) ^ (-((d : ℝ) + 3))) *
        (ENNReal.ofReal (0 * ∑ k ∈ (∅ : Finset (Fin d → ℤ)), fz (z + k)) +
        ENNReal.ofReal (0 * ∑ k ∈ E', (fun _ : Fin d → ℤ => (0 : ℝ)) (z + k)) +
        ENNReal.ofReal (1 * ∑ k ∈ E', fz (z + k)) +
        ENNReal.ofReal 1 * ∑' z', (Kc z z' : ℝ≥0∞) * ENNReal.ofReal (cellMass m Ψ τ z' F)) := by
        rw [← ENNReal.tsum_mul_left]
    _ ≤ ENNReal.ofReal (K * Δ ^ 2) * (ENNReal.ofReal (0 * cE) * ∑' z, ENNReal.ofReal (jbracket (cellPt d z) ^ (-((d : ℝ) + 3))) *
        ENNReal.ofReal ((fun _ : Fin d → ℤ => (0 : ℝ)) z) +
        ENNReal.ofReal (0 * 0 + 1 * (cE + Kw * C9 * C12)) * ∑' z, ENNReal.ofReal (jbracket (cellPt d z) ^ (-((d : ℝ) + 3))) *
          ENNReal.ofReal (fz z)) := mul_le_mul_of_nonneg_left hrate bot_le
    _ = ENNReal.ofReal (K * (cE + Kw * C9 * C12) * Δ ^ 2) * cellWeighted (m + 2) χ Ψ τ F := by
        have e2 : ENNReal.ofReal (K * (cE + Kw * C9 * C12) * Δ ^ 2) =
            ENNReal.ofReal (K * Δ ^ 2) * ENNReal.ofReal (cE + Kw * C9 * C12) := by
          rw [← ENNReal.ofReal_mul (by positivity)]; congr 1; ring
        rw [e2, mul_assoc]
        simp [cellWeighted, hfz]
        ring

end HRS.MH.AdjointRd.Phase2SA12X5
