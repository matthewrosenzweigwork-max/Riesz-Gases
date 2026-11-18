import HRS.MS.UlNlAux2
import HRS.MS.UlocWeighted
import HRS.MP.RdInit

/-!
# UL-1 (S5.1 nonlocal term), part 3: global Sobolev norms from pointwise envelopes, weights

* `ul1_fourier_partial`, `ul1_sobolev_deriv`: the Plancherel identities of `HRS.MP.RdInit` without compact
  support (integrability hypotheses instead);
* `ul1_sobolev_env`: if `‖D^j h‖ ≤ w` for `j ≤ k`, `w ∈ L¹ ∩ L²`, then `h ∈ H^k` with norm
  `≤ C(d,k) ‖w‖_{L²}`;
* weights, Schwartz decay and the pointwise Leibniz envelope of `D^k (ρ ∂_w u)`;
* the weighted mass `∫ ϖ ∑_{b ≤ m} |D^b u|² ≤ C ‖u‖²_{H^m_uloc}` (from `uloc_embedding_weighted_proof`).
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal ContDiff FourierTransform

namespace HRS.MS.Ul

open HRS HRS.Whole HRS.MP.RdInit HRS.PDE.ToolboxRd HRS.PDE.ToolboxRd.FourierAux

variable {d : ℕ}

theorem ul1_fourier_partial {k : ℕ} {u : Euc d → ℝ} (hu : ContDiff ℝ k u) 
    (hint : ∀ n : ℕ, (n : ℕ∞) ≤ (k : ℕ∞) →
      Integrable (iteratedFDeriv ℝ n (fun x => ((u x : ℝ) : ℂ))) volume)
    {j : ℕ} (hj : j ≤ k) (idx : Fin j → Fin d) (ξ : Euc d) :
    ‖𝓕 (fun x => ((partialDeriv idx u x : ℝ) : ℂ)) ξ‖ =
      (2 * Real.pi) ^ j * (∏ i, |ξ (idx i)|) * ‖𝓕 (fun x => ((u x : ℝ) : ℂ)) ξ‖ := by
  set f : Euc d → ℂ := fun x => ((u x : ℝ) : ℂ) with hf
  have hfC : ContDiff ℝ (k : ℕ∞) f := by
    have := Complex.ofRealCLM.contDiff.comp hu
    exact this
  have hjk : (j : ℕ∞) ≤ (k : ℕ∞) := by exact_mod_cast hj
  have h1 := Real.fourier_iteratedFDeriv hfC hint hjk
  have hcomp : ∀ x, iteratedFDeriv ℝ j f x (mri_e idx) = ((partialDeriv idx u x : ℝ) : ℂ) := by
    intro x
    have : iteratedFDeriv ℝ j f x = Complex.ofRealCLM.compContinuousMultilinearMap (iteratedFDeriv ℝ j u x) := by
      have := Complex.ofRealCLM.iteratedFDeriv_comp_left (x := x) (f := u) (n := (k : WithTop ℕ∞))
        hu.contDiffAt (i := j) (by exact_mod_cast hj)
      exact this
    rw [this]
    rfl
  have h2 : 𝓕 (fun x => ((partialDeriv idx u x : ℝ) : ℂ)) ξ = 𝓕 (iteratedFDeriv ℝ j f) ξ (mri_e idx) := by
    have h3 := Real.fourierIntegral_continuousMultilinearMap_apply' (L := innerSL ℝ) (μ := volume)
      (hf := hint j hjk) (m := mri_e idx) (w := ξ)
    have h4 : (fun x => ((partialDeriv idx u x : ℝ) : ℂ)) = fun x => iteratedFDeriv ℝ j f x (mri_e idx) := by
      funext x; exact (hcomp x).symm
    rw [h4]
    exact h3.symm
  rw [h2, h1]
  simp only [VectorFourier.fourierPowSMulRight_apply]
  have hin : ∀ a : Fin d, innerSL ℝ ξ (EuclideanSpace.single a (1 : ℝ)) = ξ a := by
    intro a
    rw [innerSL_apply_apply, EuclideanSpace.inner_single_right]
    simp
  simp [mri_e, hin]
  ring




/-- Version of `mri_sobolev_deriv` without compact support: integrability hypotheses instead. -/
theorem ul1_sobolev_deriv {k : ℕ} {u : Euc d → ℝ} (hu : ContDiff ℝ k u)
    (hL1 : Integrable u volume) (hL2 : MemLp u 2 volume)
    (hint : ∀ n : ℕ, (n : ℕ∞) ≤ (k : ℕ∞) →
      Integrable (iteratedFDeriv ℝ n (fun x => ((u x : ℝ) : ℂ))) volume)
    (hv : ∀ j ≤ k, ∀ idx : Fin j → Fin d, MemLp (partialDeriv idx u) 2 volume ∧
      Integrable (partialDeriv idx u) volume) :
    HRS.PDE.ToolboxRd.MemSobolev (k : ℝ) u ∧ HRS.PDE.ToolboxRd.sobolevNormSq (k : ℝ) u =
      ∑ j ∈ Finset.range (k + 1), (k.choose j : ℝ) *
        ∑ idx : Fin j → Fin d, ∫ x, (partialDeriv idx u x) ^ 2 := by
  have hFu : fourierL2 u =ᵐ[volume] 𝓕 (fun x : Euc d => ((u x : ℝ) : ℂ)) :=
    HRS.Commutator.Whole.energyAux_fourierL2_eq u hL1 hL2
  have hFv : ∀ j ≤ k, ∀ idx : Fin j → Fin d, ∀ᵐ ξ ∂(volume : Measure (Euc d)),
      ‖fourierL2 (partialDeriv idx u) ξ‖ = (2 * Real.pi) ^ j * (∏ i, |ξ (idx i)|) * ‖fourierL2 u ξ‖ := by
    intro j hj idx
    have h := HRS.Commutator.Whole.energyAux_fourierL2_eq (partialDeriv idx u) (hv j hj idx).2
      (hv j hj idx).1
    filter_upwards [h, hFu] with ξ h1 h2
    rw [h1, h2, ul1_fourier_partial hu hint hj idx ξ]
  -- the integrand identities
  have hterm : ∀ j ≤ k, (∀ᵐ ξ ∂(volume : Measure (Euc d)),
      (4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ j * ‖fourierL2 u ξ‖ ^ 2 =
        ∑ idx : Fin j → Fin d, ‖fourierL2 (partialDeriv idx u) ξ‖ ^ 2) := by
    intro j hj
    have hall : ∀ᵐ ξ ∂(volume : Measure (Euc d)), ∀ idx : Fin j → Fin d,
        ‖fourierL2 (partialDeriv idx u) ξ‖ = (2 * Real.pi) ^ j * (∏ i, |ξ (idx i)|) * ‖fourierL2 u ξ‖ :=
      ae_all_iff.2 fun idx => hFv j hj idx
    filter_upwards [hall] with ξ h
    simp_rw [h]
    have : ∀ idx : Fin j → Fin d, ((2 * Real.pi) ^ j * (∏ i, |ξ (idx i)|) * ‖fourierL2 u ξ‖) ^ 2 =
        (2 * Real.pi) ^ (2 * j) * ‖fourierL2 u ξ‖ ^ 2 * (∏ i, |ξ (idx i)|) ^ 2 := by
      intro idx
      rw [show (2 * Real.pi) ^ (2 * j) = ((2 * Real.pi) ^ j) ^ 2 by ring]; ring
    simp_rw [this]
    rw [← Finset.mul_sum, mri_sum_idx_sq]
    have h4 : (4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ j = (2 * Real.pi) ^ (2 * j) * ‖ξ‖ ^ (2 * j) := by
      rw [show 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2 = (2 * Real.pi) ^ 2 * ‖ξ‖ ^ 2 by ring, mul_pow, ← pow_mul, ← pow_mul]
    rw [h4]; ring
  have hint_term : ∀ j ≤ k, Integrable (fun ξ : Euc d => (4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ j * ‖fourierL2 u ξ‖ ^ 2) volume := by
    intro j hj
    have : Integrable (fun ξ : Euc d => ∑ idx : Fin j → Fin d, ‖fourierL2 (partialDeriv idx u) ξ‖ ^ 2) volume :=
      integrable_finsetSum _ fun idx _ => integrable_norm_sq_fourierL2 (hv j hj idx).1
    exact this.congr (by filter_upwards [hterm j hj] with ξ h using h.symm)
  have hbin : ∀ ξ : Euc d, (1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ (k : ℝ) * ‖fourierL2 u ξ‖ ^ 2 =
      ∑ j ∈ Finset.range (k + 1), (k.choose j : ℝ) * ((4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ j * ‖fourierL2 u ξ‖ ^ 2) := by
    intro ξ
    rw [Real.rpow_natCast, add_comm, add_pow, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [one_pow, mul_one]
    ring
  have hint : Integrable (fun ξ : Euc d => (1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ (k : ℝ) * ‖fourierL2 u ξ‖ ^ 2) volume := by
    simp_rw [hbin]
    exact integrable_finsetSum _ fun j hj =>
      (hint_term j (by simpa [Nat.lt_succ_iff] using hj)).const_mul _
  refine ⟨⟨hL2, hint⟩, ?_⟩
  unfold sobolevNormSq
  simp_rw [hbin]
  rw [integral_finsetSum _ fun j hj =>
    (hint_term j (by simpa [Nat.lt_succ_iff] using hj)).const_mul _]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hjk : j ≤ k := by simpa [Nat.lt_succ_iff] using hj
  rw [integral_const_mul]
  congr 1
  rw [integral_congr_ae (hterm j hjk), integral_finsetSum _ fun idx _ =>
    integrable_norm_sq_fourierL2 (hv j hjk idx).1]
  refine Finset.sum_congr rfl fun idx _ => ?_
  rw [integral_norm_sq_fourierL2 (hv j hjk idx).1]




theorem ul1_partial_cont {k : ℕ} {h : Euc d → ℝ} (hh : ContDiff ℝ k h) {j : ℕ} (hj : j ≤ k)
    (idx : Fin j → Fin d) : Continuous (partialDeriv idx h) := by
  have h1 : Continuous (iteratedFDeriv ℝ j h) := hh.continuous_iteratedFDeriv (by exact_mod_cast hj)
  exact (continuous_eval_const (mri_e idx)).comp h1

/-- Global Sobolev norm from a pointwise envelope `‖D^j h‖ ≤ w`, `w ∈ L¹ ∩ L²`. -/
theorem ul1_sobolev_env {k : ℕ} {h : Euc d → ℝ} (hh : ContDiff ℝ k h) {w : Euc d → ℝ}
    (hw1 : Integrable w) (hw2 : Integrable (fun y => w y ^ 2))
    (hb : ∀ j ≤ k, ∀ y, ‖iteratedFDeriv ℝ j h y‖ ≤ w y) :
    HRS.PDE.ToolboxRd.MemSobolev (k : ℝ) h ∧ HRS.PDE.ToolboxRd.sobolevNormSq (k : ℝ) h ≤
      (∑ j ∈ Finset.range (k + 1), (k.choose j : ℝ) * (d : ℝ) ^ j) * ∫ y, w y ^ 2 := by
  have hh0 : ContDiff ℝ (0 : ℕ) h := hh.of_le (by exact_mod_cast Nat.zero_le k)
  have hcont : Continuous h := hh0.continuous
  have hb0 : ∀ y, |h y| ≤ w y := fun y => by simpa using hb 0 (Nat.zero_le _) y
  have hL1 : Integrable h volume :=
    hw1.mono' hcont.aestronglyMeasurable (Filter.Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs]; exact hb0 y)
  have hL2 : MemLp h 2 volume := by
    refine (memLp_two_iff_integrable_sq hcont.aestronglyMeasurable).2 ?_
    refine hw2.mono' (hcont.pow 2).aestronglyMeasurable (Filter.Eventually.of_forall fun y => ?_)
    rw [Real.norm_eq_abs, abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (hb0 y) 2
  set f : Euc d → ℂ := fun x => ((h x : ℝ) : ℂ) with hf
  have hfC : ContDiff ℝ (k : ℕ∞) f := Complex.ofRealCLM.contDiff.comp hh
  have hint : ∀ n : ℕ, (n : ℕ∞) ≤ (k : ℕ∞) → Integrable (iteratedFDeriv ℝ n f) volume := by
    intro n hn
    have hnk : n ≤ k := by exact_mod_cast hn
    have hc : Continuous (iteratedFDeriv ℝ n f) := hfC.continuous_iteratedFDeriv (by exact_mod_cast hn)
    refine hw1.mono' hc.aestronglyMeasurable (Filter.Eventually.of_forall fun y => ?_)
    have := Complex.ofRealLI.norm_iteratedFDeriv_comp_left (f := h) (x := y) (i := n)
      (n := (k : WithTop ℕ∞)) hh.contDiffAt (by exact_mod_cast hnk)
    have e : (⇑Complex.ofRealLI ∘ h) = f := rfl
    rw [e] at this
    rw [this]
    exact hb n hnk y
  have hv : ∀ j ≤ k, ∀ idx : Fin j → Fin d, MemLp (partialDeriv idx h) 2 volume ∧
      Integrable (partialDeriv idx h) volume := by
    intro j hj idx
    have hc := ul1_partial_cont hh hj idx
    have hbd : ∀ y, |partialDeriv idx h y| ≤ w y := fun y =>
      (mri_abs_partialDeriv_le idx h y).trans (hb j hj y)
    refine ⟨?_, hw1.mono' hc.aestronglyMeasurable (Filter.Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs]; exact hbd y)⟩
    refine (memLp_two_iff_integrable_sq hc.aestronglyMeasurable).2 ?_
    refine hw2.mono' (hc.pow 2).aestronglyMeasurable (Filter.Eventually.of_forall fun y => ?_)
    rw [Real.norm_eq_abs, abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (hbd y) 2
  obtain ⟨hmem, hsq⟩ := ul1_sobolev_deriv hh hL1 hL2 hint hv
  refine ⟨hmem, ?_⟩
  rw [hsq, Finset.sum_mul]
  refine Finset.sum_le_sum fun j hj => ?_
  have hjk : j ≤ k := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
  have hterm : ∀ idx : Fin j → Fin d, ∫ x, (partialDeriv idx h x) ^ 2 ≤ ∫ y, w y ^ 2 := by
    intro idx
    obtain ⟨h2, -⟩ := hv j hjk idx
    refine integral_mono h2.integrable_sq hw2 fun y => ?_
    have hbd : |partialDeriv idx h y| ≤ w y :=
      (mri_abs_partialDeriv_le idx h y).trans (hb j hjk y)
    calc partialDeriv idx h y ^ 2 = |partialDeriv idx h y| ^ 2 := (sq_abs _).symm
      _ ≤ w y ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hbd 2
  calc (k.choose j : ℝ) * ∑ idx : Fin j → Fin d, ∫ x, (partialDeriv idx h x) ^ 2
      ≤ (k.choose j : ℝ) * ∑ _idx : Fin j → Fin d, ∫ y, w y ^ 2 :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun idx _ => hterm idx) (by positivity)
    _ = (k.choose j : ℝ) * (d : ℝ) ^ j * ∫ y, w y ^ 2 := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin,
          nsmul_eq_mul]
        push_cast; ring

/-! ### Weights and Schwartz decay -/

theorem ul1_jb_ge_one (y : Euc d) : 1 ≤ jbracket y := by
  unfold jbracket
  exact Real.one_le_sqrt.2 (by nlinarith [sq_nonneg ‖y‖])

theorem ul1_jb_pos (y : Euc d) : 0 < jbracket y := lt_of_lt_of_le one_pos (ul1_jb_ge_one y)

theorem ul1_jb_le (y : Euc d) : jbracket y ≤ 1 + ‖y‖ := by
  unfold jbracket
  exact Real.sqrt_le_iff.2 ⟨by positivity, by nlinarith [norm_nonneg y]⟩

theorem ul1_jb_cont : Continuous (jbracket : Euc d → ℝ) := by
  unfold jbracket; fun_prop

theorem ul1_jb_rpow_cont (c : ℝ) : Continuous (fun y : Euc d => jbracket y ^ c) :=
  ul1_jb_cont.rpow_const fun y => Or.inl (ul1_jb_pos y).ne'

theorem ul1_pow_le (t : ℝ) (ht : 0 ≤ t) (N : ℕ) : (1 + t) ^ N ≤ 2 ^ N * (1 + t ^ N) := by
  rcases le_total t 1 with h | h
  · calc (1 + t) ^ N ≤ 2 ^ N := pow_le_pow_left₀ (by linarith) (by linarith) N
      _ ≤ 2 ^ N * (1 + t ^ N) := le_mul_of_one_le_right (by positivity) (by
          have : 0 ≤ t ^ N := by positivity
          linarith)
  · calc (1 + t) ^ N ≤ (2 * t) ^ N := pow_le_pow_left₀ (by linarith) (by linarith) N
      _ = 2 ^ N * t ^ N := by rw [mul_pow]
      _ ≤ 2 ^ N * (1 + t ^ N) := mul_le_mul_of_nonneg_left (by linarith) (by positivity)

/-- the decay exponent `(3d+5)/2 = (d+3)/2 + (d+1)` -/
def ul1p (d : ℕ) : ℝ := (3 * (d : ℝ) + 5) / 2

theorem ul1_schwartz_decay (ψ : SchwartzMap (Euc d) ℝ) (a : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ y, ‖iteratedFDeriv ℝ a ψ y‖ ≤ B * jbracket y ^ (-(ul1p d)) := by
  set N : ℕ := ⌈ul1p d⌉₊ with hN
  obtain ⟨C0, hC0, h0⟩ := ψ.decay 0 a
  obtain ⟨CN, hCN, hN'⟩ := ψ.decay N a
  refine ⟨2 ^ N * (C0 + CN), by positivity, fun y => ?_⟩
  have hjb := ul1_jb_pos y
  have h1 : jbracket y ^ (ul1p d) ≤ (1 + ‖y‖) ^ N := by
    calc jbracket y ^ (ul1p d) ≤ jbracket y ^ (N : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (ul1_jb_ge_one y) (Nat.le_ceil _)
      _ = jbracket y ^ N := Real.rpow_natCast _ _
      _ ≤ (1 + ‖y‖) ^ N := pow_le_pow_left₀ hjb.le (ul1_jb_le y) N
  have h2 : ‖iteratedFDeriv ℝ a ψ y‖ * jbracket y ^ (ul1p d) ≤ 2 ^ N * (C0 + CN) := by
    have e0 := h0 y
    have eN := hN' y
    simp only [pow_zero, one_mul] at e0
    calc ‖iteratedFDeriv ℝ a ψ y‖ * jbracket y ^ (ul1p d)
        ≤ ‖iteratedFDeriv ℝ a ψ y‖ * (2 ^ N * (1 + ‖y‖ ^ N)) :=
          mul_le_mul_of_nonneg_left (h1.trans (ul1_pow_le _ (norm_nonneg _) N)) (norm_nonneg _)
      _ = 2 ^ N * (‖iteratedFDeriv ℝ a ψ y‖ + ‖y‖ ^ N * ‖iteratedFDeriv ℝ a ψ y‖) := by ring
      _ ≤ 2 ^ N * (C0 + CN) := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have hneg : jbracket y ^ (-(ul1p d)) = (jbracket y ^ (ul1p d))⁻¹ := Real.rpow_neg hjb.le _
  rw [hneg, ← div_eq_mul_inv, le_div_iff₀ (Real.rpow_pos_of_pos hjb _)]
  exact h2

theorem ul1_q_sq_integrable : Integrable (fun y : Euc d => (jbracket y ^ (-((d : ℝ) + 1))) ^ 2) := by
  have h := integrable_rpow_neg_one_add_norm_sq (E := Euc d) (μ := volume) (r := 2 * (d : ℝ) + 2)
    (by simp; linarith)
  refine h.congr (Filter.Eventually.of_forall fun y => ?_)
  have hjb := ul1_jb_pos y
  have : jbracket y = (1 + ‖y‖ ^ 2) ^ ((1 : ℝ) / 2) := by
    unfold jbracket; rw [Real.sqrt_eq_rpow]
  beta_reduce
  have hb : (0 : ℝ) ≤ 1 + ‖y‖ ^ 2 := by positivity
  have e : ((1 + ‖y‖ ^ 2) ^ (1 / 2 * -((d : ℝ) + 1))) ^ 2 =
      ((1 + ‖y‖ ^ 2) ^ (1 / 2 * -((d : ℝ) + 1))) ^ (2 : ℝ) := (Real.rpow_two _).symm
  rw [this, ← Real.rpow_mul hb, e, ← Real.rpow_mul hb]
  congr 1; ring

/-- `jb^{-(3d+5)/2} = ϖ^{1/2} q` -/
theorem ul1_jb_split (y : Euc d) : jbracket y ^ (-(ul1p d)) =
    jbracket y ^ (-(((d : ℝ) + 3) / 2)) * jbracket y ^ (-((d : ℝ) + 1)) := by
  rw [← Real.rpow_add (ul1_jb_pos y)]
  congr 1; unfold ul1p; ring

theorem ul1_jb_sq (y : Euc d) :
    (jbracket y ^ (-(((d : ℝ) + 3) / 2))) ^ 2 = jbracket y ^ (-((d : ℝ) + 3)) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (ul1_jb_pos y).le]
  congr 1; push_cast; ring

theorem ul1_q_le_one (y : Euc d) : jbracket y ^ (-((d : ℝ) + 1)) ≤ 1 :=
  Real.rpow_le_one_of_one_le_of_nonpos (ul1_jb_ge_one y) (by have : (0 : ℝ) ≤ d := Nat.cast_nonneg _; linarith)

/-! ### The weighted mass -/

open HRS.Whole.AppendixA HRS.Whole.AppendixALemmas in
theorem ul1_weighted_mass {χ : Euc d → ℝ} (hχ : IsUlocCutoff χ) (m : ℕ) (hd : 0 < d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : Euc d → ℝ, ContDiff ℝ m u → ulocNormE m χ u < ⊤ →
      Integrable (fun y => jbracket y ^ (-((d : ℝ) + 3)) * mriG m u y) ∧
      ∫ y, jbracket y ^ (-((d : ℝ) + 3)) * mriG m u y ≤ C * (ulocNormE m χ u).toReal ^ 2 := by
  obtain ⟨⟨C1, hC1⟩, hT, -⟩ := HRS.MS.UlocWeighted.uloc_embedding_weighted_proof m χ hχ
  set ϖ : Euc d → ℝ := fun y => jbracket y ^ (-((d : ℝ) + 3)) with hϖ
  have hϖ0 : ∀ y, 0 ≤ ϖ y := fun y => (Real.rpow_pos_of_pos (ul1_jb_pos y) _).le
  have hϖc : Continuous ϖ := ul1_jb_rpow_cont _
  set T : ℝ≥0∞ := cellSupSum ϖ with hTdef
  have hTfin : T ≠ ⊤ := hT.ne
  refine ⟨(d : ℝ) ^ m * |C1| ^ 2 * T.toReal, by positivity, fun u hu hU => ?_⟩
  set U := ulocNormE m χ u with hUdef
  have hUfin : U ≠ ⊤ := hU.ne
  have hW : weightedHE m ϖ u ≤ ENNReal.ofReal |C1| * T ^ (1 / 2 : ℝ) * U := by
    refine (hC1 ϖ hϖ0 u hu).trans ?_
    gcongr
    exact le_abs_self _
  set S : ℝ≥0∞ := ∑ j ∈ Finset.range (m + 1), ∑ idx : Fin j → Fin d,
    ∫⁻ x, ENNReal.ofReal (ϖ x * (partialDeriv idx u x) ^ 2) with hS
  have hSeq : weightedHE m ϖ u ^ 2 = S := by
    unfold weightedHE
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    norm_num
    rfl
  have hSle : S ≤ ENNReal.ofReal (|C1| ^ 2) * T * U ^ 2 := by
    rw [← hSeq]
    calc weightedHE m ϖ u ^ 2 ≤ (ENNReal.ofReal |C1| * T ^ (1 / 2 : ℝ) * U) ^ 2 := by gcongr
      _ = ENNReal.ofReal (|C1| ^ 2) * T * U ^ 2 := by
          have h1 : (T ^ (1 / 2 : ℝ)) ^ 2 = T := by
            rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]; norm_num
          rw [mul_pow, mul_pow, h1, ENNReal.ofReal_pow (abs_nonneg _)]
  -- the pointwise comparison
  have hmeas : ∀ j (idx : Fin j → Fin d) (hj : j ≤ m), Measurable
      (fun x => ENNReal.ofReal (ϖ x * (partialDeriv idx u x) ^ 2)) := by
    intro j idx hj
    exact ENNReal.measurable_ofReal.comp (hϖc.mul ((ul1_partial_cont hu hj idx).pow 2)).measurable
  have hpt : ∀ y, ϖ y * mriG m u y ≤ (d : ℝ) ^ m * ∑ j ∈ Finset.range (m + 1),
      ∑ idx : Fin j → Fin d, ϖ y * (partialDeriv idx u y) ^ 2 := by
    intro y
    have h1 : mriG m u y ≤ (d : ℝ) ^ m * ∑ b ∈ Finset.range (m + 1),
        ∑ idx : Fin b → Fin d, (partialDeriv idx u y) ^ 2 := by
      rw [Finset.mul_sum]
      unfold mriG
      refine Finset.sum_le_sum fun b hb => ?_
      have hbm : b ≤ m := Nat.lt_succ_iff.1 (Finset.mem_range.1 hb)
      calc ‖iteratedFDeriv ℝ b u y‖ ^ 2 ≤ (d : ℝ) ^ b * ∑ idx : Fin b → Fin d, (partialDeriv idx u y) ^ 2 :=
            mri_norm_iter_sq b u y
        _ ≤ (d : ℝ) ^ m * ∑ idx : Fin b → Fin d, (partialDeriv idx u y) ^ 2 := by
            refine mul_le_mul_of_nonneg_right ?_ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
            exact pow_le_pow_right₀ (by exact_mod_cast hd) hbm
    calc ϖ y * mriG m u y ≤ ϖ y * ((d : ℝ) ^ m * ∑ b ∈ Finset.range (m + 1),
          ∑ idx : Fin b → Fin d, (partialDeriv idx u y) ^ 2) :=
          mul_le_mul_of_nonneg_left h1 (hϖ0 y)
      _ = _ := by
          simp only [Finset.mul_sum]
          exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun idx _ => by ring
  have hlint : ∫⁻ y, ENNReal.ofReal (ϖ y * mriG m u y) ≤ ENNReal.ofReal ((d : ℝ) ^ m) * S := by
    calc ∫⁻ y, ENNReal.ofReal (ϖ y * mriG m u y)
        ≤ ∫⁻ y, ENNReal.ofReal ((d : ℝ) ^ m) * ∑ j ∈ Finset.range (m + 1), ∑ idx : Fin j → Fin d,
            ENNReal.ofReal (ϖ y * (partialDeriv idx u y) ^ 2) := by
          refine lintegral_mono fun y => ?_
          have hnn : ∀ (j : ℕ) (idx : Fin j → Fin d), 0 ≤ ϖ y * (partialDeriv idx u y) ^ 2 :=
            fun j idx => mul_nonneg (hϖ0 y) (sq_nonneg _)
          calc ENNReal.ofReal (ϖ y * mriG m u y)
              ≤ ENNReal.ofReal ((d : ℝ) ^ m * ∑ j ∈ Finset.range (m + 1),
                  ∑ idx : Fin j → Fin d, ϖ y * (partialDeriv idx u y) ^ 2) :=
                ENNReal.ofReal_le_ofReal (hpt y)
            _ = ENNReal.ofReal ((d : ℝ) ^ m) * ∑ j ∈ Finset.range (m + 1), ∑ idx : Fin j → Fin d,
                  ENNReal.ofReal (ϖ y * (partialDeriv idx u y) ^ 2) := by
                rw [ENNReal.ofReal_mul (by positivity),
                  ENNReal.ofReal_sum_of_nonneg (fun j _ => Finset.sum_nonneg fun idx _ => hnn j idx)]
                congr 1
                refine Finset.sum_congr rfl fun j _ => ?_
                rw [ENNReal.ofReal_sum_of_nonneg (fun idx _ => hnn j idx)]
      _ = ENNReal.ofReal ((d : ℝ) ^ m) * S := by
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, hS, lintegral_finsetSum]
          · congr 1
            refine Finset.sum_congr rfl fun j hj => ?_
            rw [lintegral_finsetSum]
            intro idx _
            exact hmeas j idx (Nat.lt_succ_iff.1 (Finset.mem_range.1 hj))
          · intro j hj
            exact Finset.measurable_sum _ fun idx _ => hmeas j idx (Nat.lt_succ_iff.1 (Finset.mem_range.1 hj))
  set Kc : ℝ := (d : ℝ) ^ m * |C1| ^ 2 * T.toReal with hKc
  have hI : ∫⁻ y, ENNReal.ofReal (ϖ y * mriG m u y) ≤ ENNReal.ofReal Kc * U ^ 2 := by
    refine hlint.trans ?_
    calc ENNReal.ofReal ((d : ℝ) ^ m) * S ≤ ENNReal.ofReal ((d : ℝ) ^ m) *
          (ENNReal.ofReal (|C1| ^ 2) * T * U ^ 2) := by gcongr
      _ = ENNReal.ofReal Kc * U ^ 2 := by
          rw [hKc, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
            ENNReal.ofReal_toReal hTfin]
          ring
  have hfin : ∫⁻ y, ENNReal.ofReal (ϖ y * mriG m u y) < ⊤ :=
    lt_of_le_of_lt hI (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.pow_lt_top hU))
  have hcont : Continuous (fun y => ϖ y * mriG m u y) := hϖc.mul (mriG_continuous hu)
  have hnn : ∀ y, 0 ≤ ϖ y * mriG m u y := fun y => mul_nonneg (hϖ0 y) (mriG_nonneg _ _ _)
  have hint : Integrable (fun y => ϖ y * mriG m u y) := by
    refine ⟨hcont.aestronglyMeasurable, ?_⟩
    unfold HasFiniteIntegral
    have : ∀ y, ‖ϖ y * mriG m u y‖ₑ = ENNReal.ofReal (ϖ y * mriG m u y) := fun y =>
      Real.enorm_eq_ofReal (hnn y)
    simp_rw [this]
    exact hfin
  refine ⟨hint, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hnn) hcont.aestronglyMeasurable]
  have h2 : (ENNReal.ofReal Kc * U ^ 2).toReal = Kc * U.toReal ^ 2 := by
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity), ENNReal.toReal_pow]
  rw [← h2]
  exact ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.pow_ne_top hUfin)) hI

/-! ### The Leibniz envelope of `ρ ∂_w u` -/

/-- `w_j = ∑_i M_{ij} e_i`, so that `(Mᵀ∇u)_j = ∂_{w_j} u` -/
def ul1w (M : Matrix (Fin d) (Fin d) ℝ) (j : Fin d) : Euc d :=
  ∑ i, M i j • EuclideanSpace.single i (1 : ℝ)

theorem ul1_matVec (M : Matrix (Fin d) (Fin d) ℝ) (u : Euc d → ℝ) (y : Euc d) (j : Fin d) :
    (Torus.matVec M.transpose (gradient u y)) j = fderiv ℝ u y (ul1w M j) := by
  unfold ul1w
  simp [Torus.matVec, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct,
    HRS.Whole.AppendixA.q09_gradient_apply, map_sum, map_smul]

/-- `ϖ^{1/2}` and `q` -/
def ul1wt (d : ℕ) (y : Euc d) : ℝ := jbracket y ^ (-(((d : ℝ) + 3) / 2))

def ul1q (d : ℕ) (y : Euc d) : ℝ := jbracket y ^ (-((d : ℝ) + 1))

theorem ul1_wt_nonneg (y : Euc d) : 0 ≤ ul1wt d y := (Real.rpow_pos_of_pos (ul1_jb_pos y) _).le
theorem ul1_q_nonneg (y : Euc d) : 0 ≤ ul1q d y := (Real.rpow_pos_of_pos (ul1_jb_pos y) _).le

theorem ul1_norm_le_sqrt {m : ℕ} {u : Euc d → ℝ} {b : ℕ} (hb : b ≤ m) (y : Euc d) :
    ‖iteratedFDeriv ℝ b u y‖ ≤ Real.sqrt (mriG m u y) := by
  refine Real.le_sqrt_of_sq_le ?_
  unfold mriG
  exact Finset.single_le_sum (f := fun i => ‖iteratedFDeriv ℝ i u y‖ ^ 2) (fun i _ => sq_nonneg _)
    (Finset.mem_range.2 (Nat.lt_succ_of_le hb))

theorem ul1_env_F (ψ : SchwartzMap (Euc d) ℝ) (M : Matrix (Fin d) (Fin d) ℝ) (m : ℕ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ u : Euc d → ℝ, ContDiff ℝ m u → ∀ (j : Fin d) (k : ℕ), k + 1 ≤ m →
      ∀ y, ‖iteratedFDeriv ℝ k (fun y => ψ y * fderiv ℝ u y (ul1w M j)) y‖ ≤
        A * (ul1wt d y * ul1q d y) * Real.sqrt (mriG m u y) := by
  choose B hB0 hB using fun a => ul1_schwartz_decay ψ a
  set Bs : ℝ := ∑ a ∈ Finset.range (m + 1), B a with hBs
  have hBs0 : 0 ≤ Bs := Finset.sum_nonneg fun a _ => hB0 a
  set Ws : ℝ := ∑ j, ‖ul1w M j‖ with hWs
  have hWs0 : 0 ≤ Ws := Finset.sum_nonneg fun j _ => norm_nonneg _
  refine ⟨2 ^ m * Bs * Ws, by positivity, fun u hu j k hk y => ?_⟩
  have hψk : ContDiff ℝ k ψ := ψ.smooth k
  have hhk : ContDiff ℝ k (fun y => fderiv ℝ u y (ul1w M j)) :=
    (hu.fderiv_right (m := (k : WithTop ℕ∞)) (by exact_mod_cast hk)).clm_apply contDiff_const
  have h1 := norm_iteratedFDeriv_mul_le (𝕜 := ℝ) (f := ψ) (g := fun y => fderiv ℝ u y (ul1w M j))
    (N := (k : WithTop ℕ∞)) hψk hhk y le_rfl
  have hP : 0 ≤ Real.sqrt (mriG m u y) := Real.sqrt_nonneg _
  have hjb : jbracket y ^ (-(ul1p d)) = ul1wt d y * ul1q d y := ul1_jb_split y
  have hterm : ∀ a ∈ Finset.range (k + 1), (k.choose a : ℝ) * ‖iteratedFDeriv ℝ a ψ y‖ *
      ‖iteratedFDeriv ℝ (k - a) (fun y => fderiv ℝ u y (ul1w M j)) y‖ ≤
      (k.choose a : ℝ) * (Bs * (ul1wt d y * ul1q d y)) * (‖ul1w M j‖ * Real.sqrt (mriG m u y)) := by
    intro a ha
    have hak : a ≤ k := Nat.lt_succ_iff.1 (Finset.mem_range.1 ha)
    have hda : ‖iteratedFDeriv ℝ a ψ y‖ ≤ Bs * (ul1wt d y * ul1q d y) := by
      refine (hB a y).trans ?_
      rw [hjb]
      refine mul_le_mul_of_nonneg_right ?_ (mul_nonneg (ul1_wt_nonneg y) (ul1_q_nonneg y))
      exact Finset.single_le_sum (f := B) (fun i _ => hB0 i) (Finset.mem_range.2 (by omega))
    have hdh : ‖iteratedFDeriv ℝ (k - a) (fun y => fderiv ℝ u y (ul1w M j)) y‖ ≤
        ‖ul1w M j‖ * Real.sqrt (mriG m u y) := by
      have hd : ContDiff ℝ (m - 1 : ℕ) (fderiv ℝ u) := by
        have := hu.fderiv_right (m := ((m - 1 : ℕ) : WithTop ℕ∞)) (by
          have : m - 1 + 1 ≤ m := by omega
          exact_mod_cast this)
        exact this
      refine (norm_iteratedFDeriv_clm_apply_const (N := ((m - 1 : ℕ) : WithTop ℕ∞)) (c := ul1w M j)
        (n := k - a) hd.contDiffAt (by exact_mod_cast (by omega : k - a ≤ m - 1))).trans ?_
      rw [norm_iteratedFDeriv_fderiv]
      exact mul_le_mul_of_nonneg_left (ul1_norm_le_sqrt (by omega) y) (norm_nonneg _)
    exact mul_le_mul (mul_le_mul_of_nonneg_left hda (by positivity)) hdh (norm_nonneg _)
      (mul_nonneg (by positivity) (mul_nonneg hBs0 (mul_nonneg (ul1_wt_nonneg y) (ul1_q_nonneg y))))
  calc ‖iteratedFDeriv ℝ k (fun y => ψ y * fderiv ℝ u y (ul1w M j)) y‖
      ≤ ∑ a ∈ Finset.range (k + 1), (k.choose a : ℝ) * (Bs * (ul1wt d y * ul1q d y)) *
          (‖ul1w M j‖ * Real.sqrt (mriG m u y)) := h1.trans (Finset.sum_le_sum hterm)
    _ = (2 ^ k : ℝ) * (Bs * (ul1wt d y * ul1q d y)) * (‖ul1w M j‖ * Real.sqrt (mriG m u y)) := by
        rw [← Finset.sum_mul, ← Finset.sum_mul]
        congr 2
        have := Nat.sum_range_choose k
        exact_mod_cast this
    _ ≤ 2 ^ m * Bs * Ws * (ul1wt d y * ul1q d y) * Real.sqrt (mriG m u y) := by
        have hwj : ‖ul1w M j‖ ≤ Ws :=
          Finset.single_le_sum (f := fun j => ‖ul1w M j‖) (fun i _ => norm_nonneg _) (Finset.mem_univ j)
        have h2k : (2 : ℝ) ^ k ≤ 2 ^ m := pow_le_pow_right₀ (by norm_num) (by omega)
        have hq : 0 ≤ ul1wt d y * ul1q d y := mul_nonneg (ul1_wt_nonneg y) (ul1_q_nonneg y)
        calc (2 ^ k : ℝ) * (Bs * (ul1wt d y * ul1q d y)) * (‖ul1w M j‖ * Real.sqrt (mriG m u y))
            ≤ (2 ^ m : ℝ) * (Bs * (ul1wt d y * ul1q d y)) * (Ws * Real.sqrt (mriG m u y)) := by
              gcongr
          _ = _ := by ring

end HRS.MS.Ul
