import HRS.MP.RdGenConv
import HRS.MP.RdGenSob
import HRS.Whole.Q09BAux2

/-!
# Packet MPRGEN, stage 3a: derivative bookkeeping for the generator bound

`weightedSupE` and operator norms of iterated derivatives (`rg_partial_weight_bound`,
`rg_norm_le_of_partial`), the decay class of the mean-field density `rg_rho_decay`, and the uniform
Sobolev-embedding constant `rg_phi_bounds`.
-/

noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MP.RdGen
open HRS HRS.Whole

variable {d : ℕ}

lemma rg_partial_weight_bound {r : ℕ} {L : ℝ} {f : Euc d → ℝ} (hfin : weightedSupE r L f < ⊤)
    {j : ℕ} (hj : j ≤ r) (i : Fin j → Fin d) (x : Euc d) :
    jbracket x ^ L * |partialDeriv i f x| ≤ (weightedSupE r L f).toReal := by
  have h : ENNReal.ofReal (jbracket x ^ L * |partialDeriv i f x|) ≤ weightedSupE r L f := by
    unfold weightedSupE derivSupE
    refine le_trans ?_ (le_iSup _ (⟨j, by omega⟩ : Fin (r + 1)))
    refine le_trans ?_ (le_iSup _ i)
    exact le_iSup (fun x => ENNReal.ofReal (jbracket x ^ (fun _ => L) j * |partialDeriv i f x|)) x
  exact (ENNReal.ofReal_le_iff_le_toReal hfin.ne).1 h

lemma rg_norm_le_of_partial (hd : 1 ≤ d) {j : ℕ} (A : (Euc d) [×j]→L[ℝ] ℝ) {c : ℝ}
    (hc : ∀ i : Fin j → Fin d, |A (fun p => EuclideanSpace.single (i p) 1)| ≤ c) :
    ‖A‖ ≤ (d : ℝ) ^ j * c := by
  have hc0 : 0 ≤ c := by
    have : NeZero d := ⟨by omega⟩
    exact (abs_nonneg _).trans (hc (fun _ => ⟨0, by omega⟩))
  refine ContinuousMultilinearMap.opNorm_le_bound (by positivity) fun m => ?_
  have hm : ∀ p, m p = ∑ i : Fin d, m p i • (EuclideanSpace.single i (1 : ℝ) : Euc d) := by
    intro p; ext k; simp [Finset.sum_apply, Pi.single_apply]
  have hA : A m = ∑ r : Fin j → Fin d, (∏ p, m p (r p)) • A (fun p => EuclideanSpace.single (r p) 1) := by
    conv_lhs => rw [show m = fun p => ∑ i : Fin d, m p i • (EuclideanSpace.single i (1 : ℝ) : Euc d) from funext hm]
    rw [ContinuousMultilinearMap.map_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [ContinuousMultilinearMap.map_smul_univ]
  rw [hA]
  have hterm : ∀ r : Fin j → Fin d, ‖(∏ p, m p (r p)) • A (fun p => EuclideanSpace.single (r p) 1)‖ ≤
      (∏ p, ‖m p‖) * c := by
    intro r
    rw [norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, Finset.abs_prod]
    apply mul_le_mul _ (hc r) (abs_nonneg _) (by positivity)
    gcongr with p _
    have := PiLp.norm_apply_le (m p) (r p)
    simpa [Real.norm_eq_abs] using this
  calc ‖∑ r : Fin j → Fin d, (∏ p, m p (r p)) • A (fun p => EuclideanSpace.single (r p) 1)‖
      ≤ ∑ r : Fin j → Fin d, ‖(∏ p, m p (r p)) • A (fun p => EuclideanSpace.single (r p) 1)‖ :=
        norm_sum_le _ _
    _ ≤ ∑ r : Fin j → Fin d, (∏ p, ‖m p‖) * c := Finset.sum_le_sum fun r _ => hterm r
    _ = (d : ℝ) ^ j * c * ∏ p, ‖m p‖ := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        simp
        ring


lemma rg_jb_ge (y : Euc d) : (1 + ‖y‖) / 2 ≤ jbracket y := by
  unfold jbracket
  have h1 : 1 ≤ Real.sqrt (1 + ‖y‖ ^ 2) := Real.one_le_sqrt.2 (by nlinarith [sq_nonneg ‖y‖])
  have h2 : ‖y‖ ≤ Real.sqrt (1 + ‖y‖ ^ 2) := Real.le_sqrt_of_sq_le (by nlinarith [sq_nonneg ‖y‖])
  linarith

lemma rg_jb_rpow_le (y : Euc d) {p : ℝ} (hp : 0 ≤ p) :
    jbracket y ^ (-p) ≤ 2 ^ p * (1 + ‖y‖) ^ (-p) := by
  have hB : 0 < 1 + ‖y‖ := by positivity
  have hle := rg_jb_ge y
  calc jbracket y ^ (-p) ≤ ((1 + ‖y‖) / 2) ^ (-p) :=
        Real.rpow_le_rpow_of_nonpos (by positivity) hle (by linarith)
    _ = 2 ^ p * (1 + ‖y‖) ^ (-p) := by
        have h6 : ((2 : ℝ)⁻¹) ^ (-p) = 2 ^ p := by
          rw [Real.inv_rpow (by norm_num), Real.rpow_neg (by norm_num), inv_inv]
        rw [div_eq_mul_inv, Real.mul_rpow hB.le (by norm_num), h6, mul_comm]

lemma rg_rho_decay (hd : 1 ≤ d) {r : ℕ} {Λ : ℝ} {ρ : Euc d → ℝ} (hcb : MemCb r ρ)
    (hfin : weightedSupE r ((d : ℝ) + 3) ρ < ⊤)
    (hΛ : (weightedSupE r ((d : ℝ) + 3) ρ).toReal ≤ Λ) :
    RgDecay r (fun _ => (d : ℝ) ^ r * Λ * 2 ^ ((d : ℝ) + 3)) ρ := by
  have hΛ0 : 0 ≤ Λ := (ENNReal.toReal_nonneg).trans hΛ
  refine ⟨hcb.1, fun l hl y => ?_⟩
  have hjpos : 0 < jbracket y := by unfold jbracket; positivity
  have hpt : ∀ i : Fin l → Fin d,
      |iteratedFDeriv ℝ l ρ y (fun p => EuclideanSpace.single (i p) 1)| ≤
        Λ * jbracket y ^ (-((d : ℝ) + 3)) := by
    intro i
    have h := (rg_partial_weight_bound hfin hl i y).trans hΛ
    have e : |iteratedFDeriv ℝ l ρ y (fun p => EuclideanSpace.single (i p) 1)| =
        (jbracket y ^ ((d : ℝ) + 3) * |partialDeriv i ρ y|) * jbracket y ^ (-((d : ℝ) + 3)) := by
      have : jbracket y ^ ((d : ℝ) + 3) * jbracket y ^ (-((d : ℝ) + 3)) = 1 := by
        rw [← Real.rpow_add hjpos]; simp
      unfold partialDeriv
      calc _ = |iteratedFDeriv ℝ l ρ y (fun p => EuclideanSpace.single (i p) 1)| * 1 := by ring
        _ = _ := by rw [← this]; ring
    rw [e]
    exact mul_le_mul_of_nonneg_right h (Real.rpow_nonneg hjpos.le _)
  have hn := rg_norm_le_of_partial hd (iteratedFDeriv ℝ l ρ y) hpt
  have h1 := rg_jb_rpow_le y (p := (d : ℝ) + 3) (by positivity)
  have h2 : (1 + ‖y‖) ^ (-((d : ℝ) + 3)) ≤ (1 + ‖y‖) ^ (-((d : ℝ) + 1)) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith [norm_nonneg y]) (by linarith)
  have hdr : (d : ℝ) ^ l ≤ (d : ℝ) ^ r :=
    pow_le_pow_right₀ (by exact_mod_cast hd) hl
  have hw0 : 0 ≤ (1 + ‖y‖) ^ (-((d : ℝ) + 1)) := Real.rpow_nonneg (by positivity) _
  calc ‖iteratedFDeriv ℝ l ρ y‖ ≤ (d : ℝ) ^ l * (Λ * jbracket y ^ (-((d : ℝ) + 3))) := hn
    _ ≤ (d : ℝ) ^ r * (Λ * (2 ^ ((d : ℝ) + 3) * (1 + ‖y‖) ^ (-((d : ℝ) + 1)))) := by
        apply mul_le_mul hdr _ (by positivity) (by positivity)
        apply mul_le_mul_of_nonneg_left _ hΛ0
        exact h1.trans (mul_le_mul_of_nonneg_left h2 (by positivity))
    _ = _ := by ring


open HRS.PDE in
lemma rg_phi_bounds (N : ℕ) {q : ℝ} (hq : (N : ℝ) + d / 2 < q) :
    ∃ Cs : ℝ, 0 ≤ Cs ∧ ∀ φ : Euc d → ℝ, ContDiff ℝ ∞ φ → ToolboxRd.MemSobolev q φ →
      ∀ n, n ≤ N → ∀ x : Euc d, ‖iteratedFDeriv ℝ n φ x‖ ≤ Cs * HRS.Whole.sobolevNorm q φ := by
  have h : ∀ n : ℕ, ∃ C : ℝ, 0 ≤ C ∧ (n ≤ N → ∀ φ : Euc d → ℝ, ContDiff ℝ ∞ φ →
      ToolboxRd.MemSobolev q φ → ∀ x : Euc d, ‖iteratedFDeriv ℝ n φ x‖ ≤ C * HRS.Whole.sobolevNorm q φ) := by
    intro n
    by_cases hn : n ≤ N
    · have hnq : (n : ℝ) + d / 2 < q := by
        have : (n : ℝ) ≤ N := by exact_mod_cast hn
        linarith
      obtain ⟨C, hC0, hC⟩ := rg_sobolev_embedding (d := d) n hnq
      exact ⟨C, hC0, fun _ => hC⟩
    · exact ⟨0, le_rfl, fun h' => absurd h' hn⟩
  choose C hC0 hC using h
  refine ⟨∑ n ∈ Finset.range (N + 1), C n, Finset.sum_nonneg fun n _ => hC0 n, fun φ hφ hmem n hn x => ?_⟩
  have h1 : C n ≤ ∑ n ∈ Finset.range (N + 1), C n :=
    Finset.single_le_sum (fun m _ => hC0 m) (Finset.mem_range.2 (by omega))
  have h2 : 0 ≤ HRS.Whole.sobolevNorm q φ := Real.sqrt_nonneg _
  exact (hC n hn φ hφ hmem x).trans (mul_le_mul_of_nonneg_right h1 h2)

end HRS.MP.RdGen
