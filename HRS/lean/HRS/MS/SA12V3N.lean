import HRS.MS.SA12V3M
import HRS.MS.AdjRdNorms

/-!
# S.A.12 C2 (SA12V3 worker), part N: finite sums, lattice counting and the local structure of a periodization

* `sobolevNormE` of finite sums; the cell norm `sa12v3_cell m χ c u = ‖χ(·-c) u‖_{H^m}`;
* `sa12v3_box_card`: lattice points of spacing `s` in a ball lie in a finite box with at most `(2ρ/s+2)^d` points;
* `sa12v3_perL_cell`: if `g` vanishes for `‖y‖ ≥ L/3`, then `χ(·-c) perL L g` is the finite sum over `‖Lz - c‖ < 2 + L/3`
  of the translated pieces, and `‖χ(·-c) perL L g‖ ≤ ∑_z ‖χ(·-(c-Lz)) g‖`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff Pointwise

namespace HRS.MH.AdjointRd.Phase2SA12V3

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MH.AdjointRd
  HRS.MH.AdjointRd.Phase2SA12Construction

variable {d : ℕ}

/-- The cell norm `‖χ(·-c) u‖_{H^m}`. -/
def sa12v3_cell (m : ℕ) (χ : Euc d → ℝ) (c : Euc d) (u : Euc d → ℝ) : ℝ≥0∞ :=
  sobolevNormE (m : ℝ) (fun x => χ (x - c) * u x)

theorem sa12v3_sobolevNormE_neg_le (r : ℝ) (u : Euc d → ℝ) :
    sobolevNormE r (fun x => -u x) ≤ sobolevNormE r u := by
  by_cases hu : HRS.PDE.ToolboxRd.MemSobolev r u
  swap
  · simp [sobolevNormE, hu]
  have hF := HRS.PDE.ToolboxRd.FourierAux.fourierL2_smul hu.1 (-1)
  have e : (fun x => (-1 : ℝ) * u x) = fun x => -u x := by funext x; ring
  rw [e] at hF
  have hmL : MemLp (fun x => -u x) 2 volume := hu.1.neg
  have hpt : ∀ᵐ ξ ∂(volume : Measure (Euc d)),
      (1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ r * ‖HRS.PDE.ToolboxRd.fourierL2 (fun x => -u x) ξ‖ ^ 2 =
        (1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ r * ‖HRS.PDE.ToolboxRd.fourierL2 u ξ‖ ^ 2 := by
    filter_upwards [hF] with ξ hξ
    rw [hξ]
    simp
  have hmem : HRS.PDE.ToolboxRd.MemSobolev r (fun x => -u x) := ⟨hmL, hu.2.congr (hpt.mono fun ξ h => h.symm)⟩
  have hn : HRS.PDE.ToolboxRd.sobolevNormSq r (fun x => -u x) = HRS.PDE.ToolboxRd.sobolevNormSq r u :=
    integral_congr_ae hpt
  simp only [sobolevNormE, hu, hmem, ite_true, hn, le_refl]

theorem sa12v3_sobolevNormE_add_le (r : ℝ) (u v : Euc d → ℝ) :
    sobolevNormE r (fun x => u x + v x) ≤ sobolevNormE r u + sobolevNormE r v := by
  have e : (fun x => u x + v x) = fun x => u x - (-v x) := by funext x; ring
  rw [e]
  exact (HRS.MS.SA12BD.sa12_sobolevNormE_sub r u (fun x => -v x)).trans
    (add_le_add le_rfl (sa12v3_sobolevNormE_neg_le r v))

theorem sa12v3_sobolevNormE_zero (r : ℝ) : sobolevNormE r (fun _ : Euc d => (0 : ℝ)) = 0 := by
  have h0 : MemLp (fun _ : Euc d => (0 : ℝ)) 2 volume := MemLp.zero
  have hF := HRS.PDE.ToolboxRd.FourierAux.fourierL2_smul h0 0
  simp only [zero_mul, Complex.ofReal_zero] at hF
  have hpt : ∀ᵐ ξ ∂(volume : Measure (Euc d)),
      (1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ r * ‖HRS.PDE.ToolboxRd.fourierL2 (fun _ : Euc d => (0 : ℝ)) ξ‖ ^ 2 = 0 := by
    filter_upwards [hF] with ξ hξ
    rw [hξ]; simp
  have hmem : HRS.PDE.ToolboxRd.MemSobolev r (fun _ : Euc d => (0 : ℝ)) :=
    ⟨h0, (integrable_zero _ _ _).congr (hpt.mono fun ξ h => h.symm)⟩
  have hn : HRS.PDE.ToolboxRd.sobolevNormSq r (fun _ : Euc d => (0 : ℝ)) = 0 := by
    unfold HRS.PDE.ToolboxRd.sobolevNormSq
    rw [integral_congr_ae hpt]; simp
  simp [sobolevNormE, hmem, hn]

theorem sa12v3_sobolevNormE_sum_le {ι : Type*} (s : Finset ι) (r : ℝ) (f : ι → Euc d → ℝ) :
    sobolevNormE r (fun x => ∑ i ∈ s, f i x) ≤ ∑ i ∈ s, sobolevNormE r (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [sa12v3_sobolevNormE_zero]
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (sa12v3_sobolevNormE_add_le r (f a) (fun x => ∑ i ∈ s, f i x)).trans (add_le_add le_rfl ih)

theorem sa12v3_box_card (s : ℝ) (hs : 0 < s) (X : Euc d) (ρ : ℝ) (hρ : 0 ≤ ρ) :
    ∃ B : Finset (Fin d → ℤ), (∀ z : Fin d → ℤ, (∀ i, |s * (z i : ℝ) - X i| ≤ ρ) → z ∈ B) ∧
      (B.card : ℝ) ≤ (2 * ρ / s + 2) ^ d := by
  refine ⟨Finset.Icc (fun i => ⌈(X i - ρ) / s⌉) (fun i => ⌊(X i + ρ) / s⌋), ?_, ?_⟩
  · intro z hz
    rw [Finset.mem_Icc]
    constructor <;> intro i
    · apply Int.ceil_le.2
      have := (abs_le.1 (hz i)).1
      rw [div_le_iff₀ hs]; linarith
    · apply Int.le_floor.2
      have := (abs_le.1 (hz i)).2
      rw [le_div_iff₀ hs]; linarith
  · rw [Pi.card_Icc]
    push_cast
    have hR : 0 ≤ 2 * ρ / s + 2 := by positivity
    calc ∏ i : Fin d, ((Finset.Icc (⌈(X i - ρ) / s⌉) (⌊(X i + ρ) / s⌋)).card : ℝ)
        ≤ ∏ _i : Fin d, (2 * ρ / s + 2) := by
          gcongr with i _
          rw [Int.card_Icc]
          have hb : (⌊(X i + ρ) / s⌋ : ℝ) ≤ (X i + ρ) / s := Int.floor_le _
          have ha : (X i - ρ) / s ≤ (⌈(X i - ρ) / s⌉ : ℝ) := Int.le_ceil _
          have hdiff : ((X i + ρ) / s) - ((X i - ρ) / s) = 2 * ρ / s := by field_simp; ring
          by_cases h : 0 ≤ ⌊(X i + ρ) / s⌋ + 1 - ⌈(X i - ρ) / s⌉
          · have : (((⌊(X i + ρ) / s⌋ + 1 - ⌈(X i - ρ) / s⌉).toNat : ℕ) : ℝ) =
                ((⌊(X i + ρ) / s⌋ + 1 - ⌈(X i - ρ) / s⌉ : ℤ) : ℝ) := by
              rw [← Int.cast_natCast, Int.toNat_of_nonneg h]
            rw [this]
            push_cast
            linarith
          · have : (⌊(X i + ρ) / s⌋ + 1 - ⌈(X i - ρ) / s⌉).toNat = 0 := Int.toNat_of_nonpos (by omega)
            rw [this]; simpa using hR
      _ = _ := by simp

theorem sa12v3_perL_cell_fun {χ : Euc d → ℝ} (hχ : IsUlocCutoff χ) {L : ℝ} (hL : 0 < L) {g : Euc d → ℝ}
    (hg : ∀ y : Euc d, L / 3 ≤ ‖y‖ → g y = 0) (c : Euc d) (K : Finset (Fin d → ℤ))
    (hK : ∀ z : Fin d → ℤ, ‖L • latticePt z - c‖ < 2 + L / 3 → z ∈ K) :
    (fun x => χ (x - c) * perL L g x) = fun x => ∑ z ∈ K, χ (x - c) * g (x - L • latticePt z) := by
  funext x
  by_cases hx : χ (x - c) = 0
  · simp [hx]
  · have hxn : ‖x - c‖ < 2 := by
      have := hχ.2.2.1 (subset_tsupport _ (Function.mem_support.2 hx))
      simpa using this
    unfold perL
    rw [tsum_eq_sum (s := K), Finset.mul_sum]
    intro z hz
    apply hg
    by_contra hlt
    rw [not_le] at hlt
    apply hz
    apply hK
    calc ‖L • latticePt z - c‖ = ‖(x - c) - (x - L • latticePt z)‖ := by congr 1; abel
      _ ≤ ‖x - c‖ + ‖x - L • latticePt z‖ := norm_sub_le _ _
      _ < 2 + L / 3 := by linarith

theorem sa12v3_perL_cell_le {χ : Euc d → ℝ} (hχ : IsUlocCutoff χ) (m : ℕ) {L : ℝ} (hL : 0 < L) {g : Euc d → ℝ}
    (hg : ∀ y : Euc d, L / 3 ≤ ‖y‖ → g y = 0) (c : Euc d) (K : Finset (Fin d → ℤ))
    (hK : ∀ z : Fin d → ℤ, ‖L • latticePt z - c‖ < 2 + L / 3 → z ∈ K) :
    sa12v3_cell m χ c (perL L g) ≤ ∑ z ∈ K, sa12v3_cell m χ (c - L • latticePt z) g := by
  unfold sa12v3_cell
  rw [sa12v3_perL_cell_fun hχ hL hg c K hK]
  refine (sa12v3_sobolevNormE_sum_le K (m : ℝ) (fun z x => χ (x - c) * g (x - L • latticePt z))).trans
    (le_of_eq (Finset.sum_congr rfl fun z _ => ?_))
  have e : (fun x => χ (x - c) * g (x - L • latticePt z)) =
      fun x => (fun y => χ (y - (c - L • latticePt z)) * g y) (x - L • latticePt z) := by
    funext x
    show _ = χ ((x - L • latticePt z) - (c - L • latticePt z)) * g (x - L • latticePt z)
    congr 2; abel
  rw [e]
  exact HRS.MS.SobMul.sobolevNormE_translate (m : ℝ) (fun y => χ (y - (c - L • latticePt z)) * g y) (L • latticePt z)

end HRS.MH.AdjointRd.Phase2SA12V3
