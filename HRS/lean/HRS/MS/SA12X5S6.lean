import HRS.MS.SA12StabS8
import HRS.MS.SA12X5S1
import HRS.MS.SA12X5D4
import HRS.MS.SA12X5F1
import HRS.MS.SA12X5F3
import HRS.MS.SA12X5G2

/-!
# S.A.12 X5 S6: the paired approximation sequence (producer of `PairedApproxSeqStatement`)

Same `(L_n, ε_n, datum)` for both coefficient sets; `F_n^i` the smooth periodic solutions; `sa12x5_one_seq` builds the two
`ApproximationSequence`s with `a_i.F = F^i`; the difference bounds are `sa12x5_periodic_diff_uloc`/`_varpi` (with `A = Kd δ`
from `sa12x5_paired_coeff`).
-/

set_option autoImplicit false
set_option maxHeartbeats 12800000

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MH.AdjointRd.Phase2SA12X5

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MH.AdjointRd
  HRS.MH.AdjointRd.Phase2SA12Construction HRS.MH.AdjointRd.Phase2SA12Limit
  HRS.MH.AdjointRd.Phase2SA12Assembly HRS.MH.AdjointRd.Phase2SA12Stability

variable {d : ℕ}

theorem sa12x5_comp_ineq {Cx C2 K1 Kd δ Δ τ l1 l2 : ℝ} (hτ : 0 ≤ τ) (hΔ : 0 ≤ Δ) (hδ : 0 ≤ δ)
    (hCx : 0 ≤ Cx) (hC2 : 0 ≤ C2) (hKd0 : 0 ≤ Kd) (hK1 : 1 ≤ K1) (hKd : Kd ≤ K1) (hl : l1 ≤ l2) :
    Cx * τ * Real.exp (l1 * τ) * (Δ + Kd * δ) * C2 ≤ (Cx * (C2 * K1)) * τ * Real.exp (l2 * τ) * (Δ + δ) := by
  have h1 : Δ + Kd * δ ≤ K1 * (Δ + δ) := by nlinarith [mul_nonneg hδ (sub_nonneg.2 hKd), mul_nonneg hΔ (sub_nonneg.2 hK1)]
  have h2 : Real.exp (l1 * τ) ≤ Real.exp (l2 * τ) := Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right hl hτ)
  have h3 : 0 ≤ Cx * τ := mul_nonneg hCx hτ
  have h4 : Cx * τ * Real.exp (l1 * τ) * (Δ + Kd * δ) ≤ Cx * τ * Real.exp (l2 * τ) * (K1 * (Δ + δ)) := by
    exact mul_le_mul (mul_le_mul_of_nonneg_left h2 h3) h1 (by nlinarith [mul_nonneg hKd0 hδ]) (mul_nonneg h3 (Real.exp_pos _).le)
  calc Cx * τ * Real.exp (l1 * τ) * (Δ + Kd * δ) * C2 ≤ Cx * τ * Real.exp (l2 * τ) * (K1 * (Δ + δ)) * C2 :=
        mul_le_mul_of_nonneg_right h4 hC2
    _ = _ := by ring

theorem sa12x5_paired_approx_seq : PairedApproxSeqStatement := by
  classical
  intro d hd s hs0 hsd m hm Rg MB Λ ΛV G₀ νbar T χ hχ
  have hm2 : 1 ≤ m + 2 := by omega
  obtain ⟨ζ, hζ⟩ := sa12x3p_zeta (d := d)
  obtain ⟨η, hη⟩ := sa12x3p_eta (d := d)
  obtain ⟨γ, hγ⟩ := sa12x3p_gamma hd hs0 hsd
  obtain ⟨Λ', ΛV', Cb, L₀, Kd, hKd0, hPC⟩ := sa12x5_paired_coeff hd s hs0 hsd m hm MB Λ ΛV G₀ νbar T ζ hζ
  obtain ⟨C2, hC2, hinit⟩ := HRS.MH.AdjointRd.Phase2SA12V3.sa12v3_periodic_initial_bounds hd (m + 2) χ ζ η hχ hζ hη
  obtain ⟨C15, L15, hC15, h15⟩ := periodic_uloc_bound hd s hs0 hsd (m + 2) hm2 Rg MB Λ' ΛV' νbar Cb T χ hχ
  obtain ⟨Cd, Ld, hCd, hD6⟩ := sa12x5_periodic_diff_uloc hd s hs0 hsd m hm Rg MB Λ' ΛV' νbar Cb T χ hχ
  obtain ⟨Cw, Lw, hCw, hD6w⟩ := sa12x5_periodic_diff_varpi hd s hs0 hsd m hm Rg MB Λ' ΛV' νbar Cb T χ hχ
  set K1 : ℝ := max 1 Kd with hK1
  have hK1ge : 1 ≤ K1 := le_max_left _ _
  have hKdK : Kd ≤ K1 := le_max_right _ _
  set C' : ℝ := max (max (C15 * C2) C15) (max Cd Cw) + 1 with hC'def
  have hC'a : C15 * C2 ≤ C' := by
    have : C15 * C2 ≤ max (max (C15 * C2) C15) (max Cd Cw) := (le_max_left _ _).trans (le_max_left _ _)
    linarith
  have hC'b : C15 ≤ C' := by
    have : C15 ≤ max (max (C15 * C2) C15) (max Cd Cw) := (le_max_right _ _).trans (le_max_left _ _)
    linarith
  have hC'c : Cd ≤ C' := by
    have : Cd ≤ max (max (C15 * C2) C15) (max Cd Cw) := (le_max_left _ _).trans (le_max_right _ _)
    linarith
  have hC'd : Cw ≤ C' := by
    have : Cw ≤ max (max (C15 * C2) C15) (max Cd Cw) := (le_max_right _ _).trans (le_max_right _ _)
    linarith
  have hC'pos : 0 < C' := by linarith
  set C : ℝ := max (Cd * (C2 * K1)) (Cw * (C2 * K1)) + 1 with hCdef
  have hCa : Cd * (C2 * K1) ≤ C := by
    have := le_max_left (Cd * (C2 * K1)) (Cw * (C2 * K1)); linarith
  have hCb : Cw * (C2 * K1) ≤ C := by
    have := le_max_right (Cd * (C2 * K1)) (Cw * (C2 * K1)); linarith
  have hCpos : 0 < C := by
    have : 0 ≤ Cd * (C2 * K1) := by positivity
    have := le_max_left (Cd * (C2 * K1)) (Cw * (C2 * K1)); linarith
  refine ⟨C, C', hCpos, hC'pos, ?_⟩
  intro D₁ D₂ ν₀ μ₁ μ₂ hD₁ hD₂ hR₁ hR₂ hM hV δ hδ hdist t ht φ hφ
  obtain ⟨μL₁, μL₂, VL, hA₁, hA₂, hT₁, hT₂, hj⟩ :=
    hPC D₁ D₂ μ₁ μ₂ hD₁ hD₂ hM hV δ hδ hdist γ hγ t ht
  have hT0 : 0 ≤ T := ht.1.le.trans ht.2
  set Lb : ℝ := max (max 1 L₀) (max L15 (max Ld Lw)) with hLb
  set Ln : ℕ → ℝ := fun n => Lb + n + 1 with hLn
  set εn : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1) with hεn
  have hLbge : ∀ x, x ≤ Lb → ∀ n : ℕ, x ≤ Ln n := fun x hx n => by
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    simp only [hLn]; linarith
  have hLn1 : ∀ n, max 1 L₀ ≤ Ln n := fun n => hLbge _ (le_max_left _ _) n
  have hLn15 : ∀ n, L15 ≤ Ln n := fun n => hLbge _ ((le_max_left _ _).trans (le_max_right _ _)) n
  have hLnd : ∀ n, Ld ≤ Ln n := fun n =>
    hLbge _ (((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)) n
  have hLnw : ∀ n, Lw ≤ Ln n := fun n =>
    hLbge _ (((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _)) n
  have hLnge1 : ∀ n, 1 ≤ Ln n := fun n => (le_max_left 1 L₀).trans (hLn1 n)
  have hεnI : ∀ n, εn n ∈ Ioc (0 : ℝ) 1 := fun n => by
    have : (1 : ℝ) ≤ n + 1 := by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    refine ⟨by simp only [hεn]; positivity, ?_⟩
    simp only [hεn]
    rw [div_le_one (by linarith)]; exact this
  have hLN : ∀ n : ℕ, (n : ℝ) ≤ Ln n := fun n => by
    simp only [hLn]
    have h3 : (1 : ℝ) ≤ Lb := (le_max_left 1 L₀).trans (le_max_left _ _)
    linarith
  have hLge : ∀ (a : ℝ), ∃ N : ℕ, ∀ n ≥ N, a ≤ Ln n := fun a => by
    refine ⟨⌈a⌉₊, fun n hn => ?_⟩
    have h1 : a ≤ (⌈a⌉₊ : ℝ) := Nat.le_ceil a
    have h2 : (⌈a⌉₊ : ℝ) ≤ n := by exact_mod_cast hn
    have h3 : (1 : ℝ) ≤ Lb := (le_max_left 1 L₀).trans (le_max_left _ _)
    simp only [hLn]; linarith
  have hεge : ∀ (e : ℝ), 0 < e → ∃ N : ℕ, ∀ n ≥ N, εn n ≤ e := fun e he => by
    refine ⟨⌈1 / e⌉₊, fun n hn => ?_⟩
    have h1 : 1 / e ≤ (⌈1 / e⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : (⌈1 / e⌉₊ : ℝ) ≤ n := by exact_mod_cast hn
    simp only [hεn]
    rw [div_le_iff₀ (by positivity)]
    have : 1 ≤ e * (n + 1) := by
      have := (div_le_iff₀ he).1 (h1.trans h2 |>.trans (by linarith : (n : ℝ) ≤ n + 1))
      linarith
    linarith
  -- the periodic data
  have hi := hinit φ hφ
  have hdat_reg : ∀ n, BddJets (m + 2) (periodicDatum ζ η (Ln n) (εn n) φ) ∧
      (∀ (x : Euc d) (k : Fin d → ℤ), periodicDatum ζ η (Ln n) (εn n) φ (x + Ln n • latticePt k) =
        periodicDatum ζ η (Ln n) (εn n) φ x) ∧
      ulocNormE (m + 2) χ (periodicDatum ζ η (Ln n) (εn n) φ) ≤ ENNReal.ofReal C2 * ulocNormE (m + 2) χ φ ∧
      varpiNormE (m + 2) χ (periodicDatum ζ η (Ln n) (εn n) φ) ≤ ENNReal.ofReal C2 * varpiNormE (m + 2) χ φ :=
    fun n => hi.1 (Ln n) (εn n) (hLnge1 n) (hεnI n).1
  have hPD₁ : ∀ n, PerData s (m + 2) MB Λ' ΛV' νbar Cb T (Ln n) (γ (Ln n)) D₁.M D₁.invβ
      (μL₁ (Ln n) (εn n)) (VL (Ln n) (εn n))
      (fun τ => torusDriftL D₁.M (Ln n) (γ (Ln n)) (μL₁ (Ln n) (εn n) τ) (VL (Ln n) (εn n))) :=
    fun n => hA₁.1 (Ln n) (hLn1 n) (εn n) (hεnI n)
  have hPD₂ : ∀ n, PerData s (m + 2) MB Λ' ΛV' νbar Cb T (Ln n) (γ (Ln n)) D₂.M D₂.invβ
      (μL₂ (Ln n) (εn n)) (VL (Ln n) (εn n))
      (fun τ => torusDriftL D₂.M (Ln n) (γ (Ln n)) (μL₂ (Ln n) (εn n) τ) (VL (Ln n) (εn n))) :=
    fun n => hA₂.1 (Ln n) (hLn1 n) (εn n) (hεnI n)
  have hex₁ : ∀ n, ∃ F : ℝ → Euc d → ℝ, IsPerSol (max (m + 2) 2) (Ln n) (γ (Ln n)) D₁.M D₁.invβ
      (μL₁ (Ln n) (εn n))
      (fun τ => torusDriftL D₁.M (Ln n) (γ (Ln n)) (μL₁ (Ln n) (εn n) τ) (VL (Ln n) (εn n)))
      (fun _ _ => 0) t F ∧ F 0 = periodicDatum ζ η (Ln n) (εn n) φ := fun n =>
    periodic_smooth_solution hd s hs0 hsd Rg (max (m + 2) 2) T (Ln n) (γ (Ln n)) D₁.M D₁.invβ ν₀
      (μL₁ (Ln n) (εn n)) (VL (Ln n) (εn n)) _ (hPD₁ n).toPerSmooth
      (hT₁ (Ln n) (hLn1 n) (εn n) (hεnI n)) hR₁ t ht _ (hdat_reg n).1.1 (hdat_reg n).2.1
  have hex₂ : ∀ n, ∃ F : ℝ → Euc d → ℝ, IsPerSol (max (m + 2) 2) (Ln n) (γ (Ln n)) D₂.M D₂.invβ
      (μL₂ (Ln n) (εn n))
      (fun τ => torusDriftL D₂.M (Ln n) (γ (Ln n)) (μL₂ (Ln n) (εn n) τ) (VL (Ln n) (εn n)))
      (fun _ _ => 0) t F ∧ F 0 = periodicDatum ζ η (Ln n) (εn n) φ := fun n =>
    periodic_smooth_solution hd s hs0 hsd Rg (max (m + 2) 2) T (Ln n) (γ (Ln n)) D₂.M D₂.invβ ν₀
      (μL₂ (Ln n) (εn n)) (VL (Ln n) (εn n)) _ (hPD₂ n).toPerSmooth
      (hT₂ (Ln n) (hLn1 n) (εn n) (hεnI n)) hR₂ t ht _ (hdat_reg n).1.1 (hdat_reg n).2.1
  choose Fs₁ hFs₁ using hex₁
  choose Fs₂ hFs₂ using hex₂
  obtain ⟨a₁, ha₁⟩ := sa12x5_one_seq d hd s hs0 hsd (m + 2) hm2 Rg MB Λ ΛV G₀ νbar T χ hχ ζ η γ hγ Λ' ΛV' Cb L₀
    C2 hC2 hinit C15 L15 hC15 h15 C' hC'pos hC'a hC'b D₁ ν₀ μ₁ hD₁ hR₁ t ht φ hφ μL₁ VL hA₁ hT₁ Ln εn hLn1 hLn15
    hLnge1 hεnI hLN hLge hεge Fs₁ hFs₁
  obtain ⟨a₂, ha₂⟩ := sa12x5_one_seq d hd s hs0 hsd (m + 2) hm2 Rg MB Λ ΛV G₀ νbar T χ hχ ζ η γ hγ Λ' ΛV' Cb L₀
    C2 hC2 hinit C15 L15 hC15 h15 C' hC'pos hC'a hC'b D₂ ν₀ μ₂ hD₂ hR₂ t ht φ hφ μL₂ VL hA₂ hT₂ Ln εn hLn1 hLn15
    hLnge1 hεnI hLN hLge hεge Fs₂ hFs₂
  refine ⟨a₁, a₂, fun n τ hτ => ?_⟩
  have e1 : ∀ x, a₁.F n τ x - a₂.F n τ x = Fs₁ n τ x - Fs₂ n τ x := fun x => by rw [ha₁, ha₂]
  simp only [e1]
  -- common-M versions of the second coefficient set
  have hPD₂' : PerData s (m + 2) MB Λ' ΛV' νbar Cb T (Ln n) (γ (Ln n)) D₁.M D₂.invβ
      (μL₂ (Ln n) (εn n)) (VL (Ln n) (εn n))
      (fun τ => torusDriftL D₁.M (Ln n) (γ (Ln n)) (μL₂ (Ln n) (εn n) τ) (VL (Ln n) (εn n))) := by
    rw [hM]; exact hPD₂ n
  have hR₂' : RdRegimeHolds Rg d s D₁.M D₂.invβ ν₀ := by rw [hM]; exact hR₂
  have hsol₁ : IsPerSol (m + 2) (Ln n) (γ (Ln n)) D₁.M D₁.invβ (μL₁ (Ln n) (εn n))
      (fun τ => torusDriftL D₁.M (Ln n) (γ (Ln n)) (μL₁ (Ln n) (εn n) τ) (VL (Ln n) (εn n)))
      (fun _ _ => 0) t (Fs₁ n) := sa12x3p_isPerSol_mono (le_max_left (m + 2) 2) (hFs₁ n).1
  have hsol₂ : IsPerSol (m + 2) (Ln n) (γ (Ln n)) D₁.M D₂.invβ (μL₂ (Ln n) (εn n))
      (fun τ => torusDriftL D₁.M (Ln n) (γ (Ln n)) (μL₂ (Ln n) (εn n) τ) (VL (Ln n) (εn n)))
      (fun _ _ => 0) t (Fs₂ n) := by
    rw [hM]; exact sa12x3p_isPerSol_mono (le_max_left (m + 2) 2) (hFs₂ n).1
  have hF0 : Fs₁ n 0 = Fs₂ n 0 := (hFs₁ n).2.trans (hFs₂ n).2.symm
  have hdiff : ∀ τ' ∈ Icc (0 : ℝ) T,
      (∀ j ≤ m + 2, ∀ y, ‖iteratedFDeriv ℝ j (fun x => μL₁ (Ln n) (εn n) τ' x - μL₂ (Ln n) (εn n) τ' x) y‖ ≤ Kd * δ) ∧
      (∀ j ≤ m + 2, ∀ x : Euc d, ∃ k : Fin d → ℤ,
        jbracket (x - Ln n • latticePt k) ^ ((d : ℝ) + 3) *
          ‖iteratedFDeriv ℝ j (fun x => μL₁ (Ln n) (εn n) τ' x - μL₂ (Ln n) (εn n) τ' x) x‖ ≤ Kd * δ) ∧
      (∀ j ≤ m, ∀ y, ‖iteratedFDeriv ℝ j (fun x =>
        torusDriftL D₁.M (Ln n) (γ (Ln n)) (μL₁ (Ln n) (εn n) τ') (VL (Ln n) (εn n)) x -
          torusDriftL D₁.M (Ln n) (γ (Ln n)) (μL₂ (Ln n) (εn n) τ') (VL (Ln n) (εn n)) x) y‖ ≤ Kd * δ) :=
    fun τ' hτ' => hj (Ln n) (hLn1 n) (εn n) (hεnI n) τ' hτ'
  have hKδ : 0 ≤ Kd * δ := mul_nonneg hKd0 hδ
  have hτ0 : 0 ≤ τ := hτ.1
  have hlam1 : Rg.lambdaM Cd ν₀ (PDE.thetaOrder d s) ≤ Rg.lambdaM C' ν₀ (PDE.thetaOrder d s) := by
    have := sa12x3_lam_ge hR₁ hC'c (PDE.thetaOrder d s); linarith
  have hlam2 : Rg.lambdaM Cw ν₀ (PDE.thetaOrder d s) ≤ Rg.lambdaM C' ν₀ (PDE.thetaOrder d s) := by
    have := sa12x3_lam_ge hR₁ hC'd (PDE.thetaOrder d s); linarith
  have hU0 : ulocNormE (m + 2) χ (Fs₁ n 0) ≤ ENNReal.ofReal C2 * ulocNormE (m + 2) χ φ := by
    rw [(hFs₁ n).2]; exact (hdat_reg n).2.2.1
  have hV0 : varpiNormE (m + 2) χ (Fs₁ n 0) ≤ ENNReal.ofReal C2 * varpiNormE (m + 2) χ φ := by
    rw [(hFs₁ n).2]; exact (hdat_reg n).2.2.2
  have hUfin : ulocNormE (m + 2) χ (Fs₁ n 0) < ⊤ :=
    lt_of_le_of_lt hU0 (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hφ)
  have hL0 : 0 < Ln n := lt_of_lt_of_le one_pos (hLnge1 n)
  have hτt : τ ∈ Icc (0 : ℝ) t := hτ
  constructor
  · have h1 := hD6 ν₀ (Ln n) (γ (Ln n)) D₁.M D₁.invβ D₂.invβ (μL₁ (Ln n) (εn n)) (μL₂ (Ln n) (εn n))
      (VL (Ln n) (εn n)) _ _ (Kd * δ) hKδ (hLnd n) (hPD₁ n) hPD₂' hR₁ hR₂' (hT₁ _ (hLn1 n) _ (hεnI n))
      (hT₂ _ (hLn1 n) _ (hεnI n)) hdiff t ht (Fs₁ n) (Fs₂ n) hsol₁ hsol₂ hF0 hUfin τ hτ
    have hX0 : 0 ≤ Cd * τ * Real.exp (Rg.lambdaM Cd ν₀ (PDE.thetaOrder d s) * τ) * (|D₁.invβ - D₂.invβ| + Kd * δ) := by
      positivity
    calc _ ≤ _ := h1
      _ ≤ ENNReal.ofReal (Cd * τ * Real.exp (Rg.lambdaM Cd ν₀ (PDE.thetaOrder d s) * τ) *
            (|D₁.invβ - D₂.invβ| + Kd * δ)) * (ENNReal.ofReal C2 * ulocNormE (m + 2) χ φ) := by gcongr
      _ = ENNReal.ofReal (Cd * τ * Real.exp (Rg.lambdaM Cd ν₀ (PDE.thetaOrder d s) * τ) *
            (|D₁.invβ - D₂.invβ| + Kd * δ) * C2) * ulocNormE (m + 2) χ φ := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul hX0]
      _ ≤ _ := by
          refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
          have := sa12x5_comp_ineq (Cx := Cd) (C2 := C2) (K1 := K1) (Kd := Kd) (δ := δ)
            (Δ := |D₁.invβ - D₂.invβ|) (τ := τ) (l1 := Rg.lambdaM Cd ν₀ (PDE.thetaOrder d s))
            (l2 := Rg.lambdaM C' ν₀ (PDE.thetaOrder d s)) hτ0 (abs_nonneg _) hδ hCd.le hC2.le hKd0 hK1ge hKdK hlam1
          refine this.trans ?_
          have hq : 0 ≤ τ * Real.exp (Rg.lambdaM C' ν₀ (PDE.thetaOrder d s) * τ) * (|D₁.invβ - D₂.invβ| + δ) := by
            positivity
          nlinarith [mul_le_mul_of_nonneg_right hCa hq]
  · have h1 := hD6w ν₀ (Ln n) (γ (Ln n)) D₁.M D₁.invβ D₂.invβ (μL₁ (Ln n) (εn n)) (μL₂ (Ln n) (εn n))
      (VL (Ln n) (εn n)) _ _ (Kd * δ) hKδ (hLnw n) (hPD₁ n) hPD₂' hR₁ hR₂' (hT₁ _ (hLn1 n) _ (hεnI n))
      (hT₂ _ (hLn1 n) _ (hεnI n)) t ht hdiff (Fs₁ n) (Fs₂ n) hsol₁ hsol₂ hF0 τ hτ
    have hX0 : 0 ≤ Cw * τ * Real.exp (Rg.lambdaM Cw ν₀ (PDE.thetaOrder d s) * τ) * (|D₁.invβ - D₂.invβ| + Kd * δ) := by
      positivity
    calc _ ≤ _ := h1
      _ ≤ ENNReal.ofReal (Cw * τ * Real.exp (Rg.lambdaM Cw ν₀ (PDE.thetaOrder d s) * τ) *
            (|D₁.invβ - D₂.invβ| + Kd * δ)) * (ENNReal.ofReal C2 * varpiNormE (m + 2) χ φ) := by gcongr
      _ = ENNReal.ofReal (Cw * τ * Real.exp (Rg.lambdaM Cw ν₀ (PDE.thetaOrder d s) * τ) *
            (|D₁.invβ - D₂.invβ| + Kd * δ) * C2) * varpiNormE (m + 2) χ φ := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul hX0]
      _ ≤ _ := by
          refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
          have := sa12x5_comp_ineq (Cx := Cw) (C2 := C2) (K1 := K1) (Kd := Kd) (δ := δ)
            (Δ := |D₁.invβ - D₂.invβ|) (τ := τ) (l1 := Rg.lambdaM Cw ν₀ (PDE.thetaOrder d s))
            (l2 := Rg.lambdaM C' ν₀ (PDE.thetaOrder d s)) hτ0 (abs_nonneg _) hδ hCw.le hC2.le hKd0 hK1ge hKdK hlam2
          refine this.trans ?_
          have hq : 0 ≤ τ * Real.exp (Rg.lambdaM C' ν₀ (PDE.thetaOrder d s) * τ) * (|D₁.invβ - D₂.invβ| + δ) := by
            positivity
          nlinarith [mul_le_mul_of_nonneg_right hCb hq]

end HRS.MH.AdjointRd.Phase2SA12X5
