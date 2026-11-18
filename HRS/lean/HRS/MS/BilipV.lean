import HRS.MS.BilipVAux3
import HRS.MS.FlowE

/-!
# MS-BILIP-V: clause (v) of Lemma S.A.32 and the final assembly `uloc_bilip_proof`

`bilip_v_const` (Milestone 1): clause (v) from the content of (i), (ii) with an arbitrary constant `E`;
`uloc_bilip_proof` (Milestone 2): the frozen statement `uloc_bilip` verbatim.  Route: `BilipVPlan.md`.
-/

open Set MeasureTheory
open scoped ENNReal ContDiff
open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas

namespace HRS.MS.BilipV

variable {d : ℕ}

/-- the content of conjunct (i) of `uloc_bilip` with the constant `E` at one time `τ` -/
def BvI (m : ℕ) (E : ℝ) (Ψ Ψinv : ℝ → Euc d → Euc d) (τ : ℝ) : Prop :=
  (∀ x, Ψinv τ (Ψ τ x) = x) ∧ (∀ y, Ψ τ (Ψinv τ y) = y) ∧
    ContDiff ℝ ((m + 1 : ℕ) : WithTop ℕ∞) (Ψ τ) ∧
    ContDiff ℝ ((m + 1 : ℕ) : WithTop ℕ∞) (Ψinv τ) ∧
    (∀ x, ‖fderiv ℝ (Ψ τ) x‖ ≤ Real.exp (E * τ)) ∧
    (∀ y, ‖fderiv ℝ (Ψinv τ) y‖ ≤ Real.exp (E * τ)) ∧
    ∀ j : ℕ, 2 ≤ j → j ≤ m + 1 → ∀ x : Euc d,
      ‖iteratedFDeriv ℝ j (Ψ τ) x‖ ≤ E * Real.exp (E * m * τ) ∧
      ‖iteratedFDeriv ℝ j (Ψinv τ) x‖ ≤ E * Real.exp (E * m * τ)

/-- the `C_b` content of conjunct (ii) of `uloc_bilip` with the constant `E` at one time `τ` -/
def BvII (m : ℕ) (E : ℝ) (χ : Euc d → ℝ) (Ψinv : ℝ → Euc d → Euc d) (τ : ℝ) : Prop :=
  ∀ z : Euc d, MemCb (m + 1) (fun x => χ (Ψinv τ x - z)) ∧
    cbNorm (m + 1) (fun x => χ (Ψinv τ x - z)) ≤ E * Real.exp (E * m * τ)

theorem bv_lip_of_fderiv {f : Euc d → Euc d} {m : ℕ}
    (hf : ContDiff ℝ ((m + 1 : ℕ) : WithTop ℕ∞) f) {L : ℝ} (h : ∀ x, ‖fderiv ℝ f x‖ ≤ L) :
    ∀ x x', ‖f x - f x'‖ ≤ L * ‖x - x'‖ := by
  intro x x'
  have hd : Differentiable ℝ f := hf.differentiable (by exact_mod_cast Nat.succ_ne_zero m)
  exact (convex_univ (𝕜 := ℝ) (E := Euc d)).norm_image_sub_le_of_norm_fderiv_le (f := f) (C := L)
    (fun y _ => hd y) (fun y _ => h y) (mem_univ x') (mem_univ x)

/-- Milestone 1: clause (v) of S.A.32, from the content of (i), (ii) with an arbitrary constant `E`. -/
theorem bilip_v_const (m : ℕ) (T : ℝ) (hT : 0 < T) (χ : Euc d → ℝ) (hχ : IsUlocCutoff χ)
    (E : ℝ) (hE : 0 < E) :
    ∃ K0 c : ℝ, 0 < K0 ∧ 0 < c ∧ ∀ C : ℝ, K0 ≤ C → ∀ Ψ Ψinv : ℝ → Euc d → Euc d,
      ∀ τ ∈ Set.Icc (0 : ℝ) T, BvI m E Ψ Ψinv τ → BvII m E χ Ψinv τ →
        ∀ F : Euc d → ℝ,
          ENNReal.ofReal (c * Real.exp (-(C * (m + d) * τ))) * ulocNormE m χ F ≤
            ⨆ z : Euc d, sobolevNormE (m : ℝ) (fun x => χ (Ψinv τ x - z) * F x) ∧
          (⨆ z : Euc d, sobolevNormE (m : ℝ) (fun x => χ (Ψinv τ x - z) * F x)) ≤
            ENNReal.ofReal (C * Real.exp (C * (m + d) * τ)) * ulocNormE m χ F := by
  set L : ℝ := Real.exp (E * T) with hL
  have hL1 : 1 ≤ L := Real.one_le_exp (by positivity)
  set B : ℝ := E * Real.exp (E * m * T) with hB
  have hB0 : 0 ≤ B := by positivity
  set D : ℝ := max 1 (max L B) with hD
  have hD1 : 1 ≤ D := le_max_left _ _
  have hDL : L ≤ D := (le_max_left _ _).trans (le_max_right _ _)
  have hDB : B ≤ D := (le_max_right _ _).trans (le_max_right _ _)
  obtain ⟨K, hK, hcore⟩ := bv_core m χ hχ L D B hL1 hD1 hB0
  refine ⟨K, 1 / K, hK, by positivity, fun C hC Ψ Ψinv τ hτ hI hII F => ?_⟩
  obtain ⟨hinv1, hinv2, hcd1, hcd2, hfd1, hfd2, hiter⟩ := hI
  have hτ0 : 0 ≤ τ := hτ.1
  have hτT : τ ≤ T := hτ.2
  have hexpL : Real.exp (E * τ) ≤ L := Real.exp_le_exp.2 (by nlinarith)
  have hdat : BvData m χ L D B (Ψ τ) (Ψinv τ) := by
    refine ⟨hinv2, bv_lip_of_fderiv hcd1 fun x => (hfd1 x).trans hexpL,
      bv_lip_of_fderiv hcd2 fun x => (hfd2 x).trans hexpL, hcd2, ?_, ?_⟩
    · intro x i h1 h2
      by_cases hi : i = 1
      · subst hi
        rw [norm_iteratedFDeriv_one (𝕜 := ℝ)]
        exact (hfd2 x).trans (hexpL.trans hDL)
      · refine ((hiter i (by omega) h2 x).2).trans ?_
        refine le_trans ?_ hDB
        have : E * m * τ ≤ E * m * T := by
          have : (0 : ℝ) ≤ E * m := by positivity
          exact mul_le_mul_of_nonneg_left hτT this
        exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 this) hE.le
    · intro z
      refine ⟨(hII z).1, (hII z).2.trans ?_⟩
      have : E * m * τ ≤ E * m * T := by
        have : (0 : ℝ) ≤ E * m := by positivity
        exact mul_le_mul_of_nonneg_left hτT this
      exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 this) hE.le
  obtain ⟨hup, hlow⟩ := hcore (Ψ τ) (Ψinv τ) hdat F
  have hC0 : 0 < C := lt_of_lt_of_le hK hC
  have hmd : (0 : ℝ) ≤ C * (m + d) * τ := by positivity
  constructor
  · -- lower bound
    have h1 : 1 / K * Real.exp (-(C * (m + d) * τ)) ≤ 1 / K :=
      mul_le_of_le_one_right (by positivity) (Real.exp_le_one_iff.2 (by linarith))
    calc ENNReal.ofReal (1 / K * Real.exp (-(C * (m + d) * τ))) * ulocNormE m χ F
        ≤ ENNReal.ofReal (1 / K) * ulocNormE m χ F := by gcongr
      _ ≤ ENNReal.ofReal (1 / K) * (ENNReal.ofReal K *
            ⨆ z : Euc d, sobolevNormE (m : ℝ) (fun x => χ (Ψinv τ x - z) * F x)) := by gcongr
      _ = ⨆ z : Euc d, sobolevNormE (m : ℝ) (fun x => χ (Ψinv τ x - z) * F x) := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity), one_div, inv_mul_cancel₀ hK.ne',
            ENNReal.ofReal_one, one_mul]
  · refine hup.trans ?_
    gcongr
    calc K ≤ C := hC
      _ = C * 1 := (mul_one C).symm
      _ ≤ C * Real.exp (C * (m + d) * τ) :=
          mul_le_mul_of_nonneg_left (Real.one_le_exp hmd) hC0.le

/-- Milestone 2: Lemma S.A.32 (`uloc_bilip`), statement verbatim. -/
theorem uloc_bilip_proof (m : ℕ) (T Λ : ℝ) (hT : 0 < T) (χ χh : Euc d → ℝ) (hχ : IsUlocCutoff χ)
    (hχh : IsCutoffRad 6 8 χh) :
    ∃ C c : ℝ, 0 < c ∧ ∀ b : ℝ → Euc d → Euc d, IsDriftBounds T m Λ b →
      (∃ Ψ, IsNegDriftFlow T b Ψ) ∧
      ∀ Ψ : ℝ → Euc d → Euc d, IsNegDriftFlow T b Ψ →
        ∃ Ψinv : ℝ → Euc d → Euc d, ∀ τ ∈ Set.Icc (0 : ℝ) T,
          -- (i)
          ((∀ x, Ψinv τ (Ψ τ x) = x) ∧ (∀ y, Ψ τ (Ψinv τ y) = y) ∧
            ContDiff ℝ ((m + 1 : ℕ) : WithTop ℕ∞) (Ψ τ) ∧
            ContDiff ℝ ((m + 1 : ℕ) : WithTop ℕ∞) (Ψinv τ) ∧
            (∀ x, ‖fderiv ℝ (Ψ τ) x‖ ≤ Real.exp (C * τ)) ∧
            (∀ y, ‖fderiv ℝ (Ψinv τ) y‖ ≤ Real.exp (C * τ)) ∧
            ∀ j : ℕ, 2 ≤ j → j ≤ m + 1 → ∀ x : Euc d,
              ‖iteratedFDeriv ℝ j (Ψ τ) x‖ ≤ C * Real.exp (C * m * τ) ∧
              ‖iteratedFDeriv ℝ j (Ψinv τ) x‖ ≤ C * Real.exp (C * m * τ)) ∧
          -- (ii)
          (∀ z : Euc d, (∀ x, HasDerivWithinAt (fun τ' => χ (Ψinv τ' x - z))
              (inner ℝ (b τ x) (gradient (fun y => χ (Ψinv τ y - z)) x)) (Set.Icc (0 : ℝ) T) τ) ∧
            MemCb (m + 1) (fun x => χ (Ψinv τ x - z)) ∧
            cbNorm (m + 1) (fun x => χ (Ψinv τ x - z)) ≤ C * Real.exp (C * m * τ)) ∧
          -- (iii)
          (∀ z : Euc d, ∀ x y : Euc d, x ∈ tsupport (fun x => χ (Ψinv τ x - z)) →
            y ∈ tsupport (fun y => 1 - χh (Ψinv τ y - z)) →
            4 * Real.exp (-(C * τ)) ≤ ‖x - y‖) ∧
          -- (iv)
          ((⋃ z : Fin d → ℤ, Ψ τ '' latticeCell z) = Set.univ ∧
            (∀ y : Euc d, {z : Fin d → ℤ | y ∈ Ψ τ '' latticeCell z}.encard ≤
              ((⌊C * Real.exp (C * d * τ)⌋₊ : ℕ) : ℕ∞)) ∧
            (∀ G : Euc d → ℝ≥0∞, Measurable G →
              ∫⁻ x, G x ≤ ∑' z : Fin d → ℤ, ∫⁻ x in Ψ τ '' latticeCell z, G x ∧
              (∑' z : Fin d → ℤ, ∫⁻ x in Ψ τ '' latticeCell z, G x) ≤
                ENNReal.ofReal (C * Real.exp (C * d * τ)) * ∫⁻ x, G x) ∧
            ∀ (A : Set (Euc d)) (ρ : ℝ), 0 ≤ ρ → Metric.ediam A ≤ ENNReal.ofReal ρ →
              {z : Fin d → ℤ | (A ∩ tsupport (fun x => χ (Ψinv τ x - latticePt z))).Nonempty}.encard ≤
                ((⌊C * (1 + ρ) ^ d * Real.exp (C * d * τ)⌋₊ : ℕ) : ℕ∞)) ∧
          -- (v)
          (∀ F : Euc d → ℝ,
            ENNReal.ofReal (c * Real.exp (-(C * (m + d) * τ))) * ulocNormE m χ F ≤
              ⨆ z : Euc d, sobolevNormE (m : ℝ) (fun x => χ (Ψinv τ x - z) * F x) ∧
            (⨆ z : Euc d, sobolevNormE (m : ℝ) (fun x => χ (Ψinv τ x - z) * F x)) ≤
              ENNReal.ofReal (C * Real.exp (C * (m + d) * τ)) * ulocNormE m χ F) := by
  by_cases hΛ : 0 ≤ Λ
  swap
  · exact ⟨1, 1, one_pos, fun b hb => absurd (FlowD.Λ_nonneg' hT.le hb) hΛ⟩
  obtain ⟨E, hE, hEprop⟩ := FlowE.uloc_bilip_i_ii m T Λ hT χ χh hχ hχh
  obtain ⟨CD, hCD, hDprop⟩ := FlowD.flow_covering_separation d Λ hΛ χ χh hχ hχh
  obtain ⟨K0, c, hK0, hc, hVprop⟩ := bilip_v_const m T hT χ hχ E hE
  set C : ℝ := max (max E CD) K0 with hCdef
  have hEC : E ≤ C := (le_max_left _ _).trans (le_max_left _ _)
  have hCDC : CD ≤ C := (le_max_right _ _).trans (le_max_left _ _)
  have hKC : K0 ≤ C := le_max_right _ _
  have hC0 : 0 < C := lt_of_lt_of_le hE hEC
  refine ⟨C, c, hc, fun b hb => ?_⟩
  obtain ⟨hex, hrest⟩ := hEprop b hb
  refine ⟨hex, fun Ψ hΨ => ?_⟩
  obtain ⟨Ψinv, hΨinv⟩ := hrest Ψ hΨ
  refine ⟨Ψinv, fun τ hτ => ?_⟩
  obtain ⟨hi, hii⟩ := hΨinv τ hτ
  have hτ0 : 0 ≤ τ := hτ.1
  have hinvall : ∀ τ ∈ Set.Icc (0 : ℝ) T,
      (∀ x, Ψinv τ (Ψ τ x) = x) ∧ (∀ y, Ψ τ (Ψinv τ y) = y) :=
    fun τ' hτ' => ⟨((hΨinv τ' hτ').1).1, ((hΨinv τ' hτ').1).2.1⟩
  have hlipI := FlowD.inv_lip hT.le hb hΨ Ψinv hinvall τ hτ
  have hlipΨ := FlowA.flow_lipschitz hT.le hb hΨ τ hτ
  obtain ⟨hiii, hiv⟩ := hDprop Ψ Ψinv τ hτ0 (hinvall τ hτ).1 (hinvall τ hτ).2 hlipI hlipΨ
  have hmτ : (0 : ℝ) ≤ m * τ := by positivity
  have hdτ : (0 : ℝ) ≤ d * τ := by positivity
  have hexp1 : Real.exp (E * τ) ≤ Real.exp (C * τ) := Real.exp_le_exp.2 (by nlinarith)
  have hexp2 : E * Real.exp (E * m * τ) ≤ C * Real.exp (C * m * τ) :=
    mul_le_mul hEC (Real.exp_le_exp.2 (by nlinarith)) (Real.exp_pos _).le hC0.le
  have mono1 : CD * Real.exp (CD * d * τ) ≤ C * Real.exp (C * d * τ) :=
    mul_le_mul hCDC (Real.exp_le_exp.2 (by nlinarith)) (Real.exp_pos _).le hC0.le
  have hiBv : BvI m E Ψ Ψinv τ := hi
  have hiiBv : BvII m E χ Ψinv τ := fun z => ⟨(hii z).2.1, (hii z).2.2⟩
  obtain ⟨a1, a2, a3, a4, a5, a6, a7⟩ := hi
  refine ⟨⟨a1, a2, a3, a4, fun x => (a5 x).trans hexp1, fun y => (a6 y).trans hexp1,
    fun j hj hjm x => ⟨(a7 j hj hjm x).1.trans hexp2, (a7 j hj hjm x).2.trans hexp2⟩⟩,
    fun z => ⟨(hii z).1, (hii z).2.1, (hii z).2.2.trans hexp2⟩,
    fun z x y hx hy => ?_, ?_, hVprop C hKC Ψ Ψinv τ hτ hiBv hiiBv⟩
  · refine le_trans ?_ (hiii z x y hx hy)
    have : Real.exp (-(C * τ)) ≤ Real.exp (-(CD * τ)) := Real.exp_le_exp.2 (by nlinarith)
    linarith
  · obtain ⟨iv1, iv2, iv3, iv4⟩ := hiv
    refine ⟨iv1, fun y => (iv2 y).trans ?_, fun G hG => ⟨(iv3 G hG).1, (iv3 G hG).2.trans ?_⟩,
      fun A ρ hρ hA => (iv4 A ρ hρ hA).trans ?_⟩
    · exact_mod_cast Nat.floor_le_floor mono1
    · gcongr
    · have : CD * (1 + ρ) ^ d * Real.exp (CD * d * τ) ≤ C * (1 + ρ) ^ d * Real.exp (C * d * τ) := by
        have h1p : 0 ≤ (1 + ρ) ^ d := by positivity
        calc CD * (1 + ρ) ^ d * Real.exp (CD * d * τ) = (CD * Real.exp (CD * d * τ)) * (1 + ρ) ^ d := by
              ring
          _ ≤ (C * Real.exp (C * d * τ)) * (1 + ρ) ^ d := mul_le_mul_of_nonneg_right mono1 h1p
          _ = _ := by ring
      exact_mod_cast Nat.floor_le_floor this

example := (@uloc_bilip_proof : type_of% @HRS.Whole.AppendixALemmas.uloc_bilip)

end HRS.MS.BilipV
