import HRS.MS.Fp81S21WeightedRellich13

/-!
The localized weighted Rellich argument is stated in the actual chart norm:
`weightedSobolevE` is the L² norm of the weighted ordered jets, not its
square.  Thus the multiplier estimate and scalar normalization below use
linear norm scaling.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

noncomputable section

open MeasureTheory
open scoped ENNReal BigOperators

namespace HRS.Fp81.S21

open HRS HRS.Whole HRS.MS.FixEq

/-- Multiplication by a nonnegative scalar scales the weighted Sobolev
L² norm by that scalar. -/
theorem fp81s21_weightedRellich_weightedSobolevE_nonneg_smul
    {d r : ℕ} {P c : ℝ} {f : Euc d → ℝ}
    (hc : 0 ≤ c) (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f) :
    weightedSobolevE r P (c • f) = ENNReal.ofReal c * weightedSobolevE r P f := by
  have hf' : ContDiff ℝ (r : WithTop ℕ∞) f := hf.of_le (by exact_mod_cast le_top)
  have hfc : ContDiff ℝ (r : WithTop ℕ∞) (c • f) := hf'.const_smul c
  calc
    weightedSobolevE r P (c • f) =
        eLpNorm (HRS.MS.ProClosureS111.weightedJets r P (c • f)) 2 volume :=
      (HRS.MS.ProClosureS111.weightedJets_eLpNorm (Pw := P) (r := r) (f := c • f) hfc).symm
    _ = eLpNorm (c • HRS.MS.ProClosureS111.weightedJets r P f) 2 volume := by
      rw [HRS.MS.ProClosureS111.weightedJets_smul (Pw := P) (r := r) c hf']
    _ = ENNReal.ofReal c * eLpNorm
        (HRS.MS.ProClosureS111.weightedJets r P f) 2 volume := by
      rw [eLpNorm_const_smul, Real.enorm_eq_ofReal hc]
    _ = ENNReal.ofReal c * weightedSobolevE r P f := by
      rw [HRS.MS.ProClosureS111.weightedJets_eLpNorm (Pw := P) (r := r) hf']

/-- For every fixed radius, a single smooth cutoff localizes any sequence
from the strong unit ball; the resulting cutoff sequence has a subsequence
Cauchy in the weak weighted jet space. -/
theorem fp81s21_weightedRellich_fixedCutoffFamily_cauchy
    {d q : ℕ} {P ρ C : ℝ} (hρ : 1 ≤ ρ) (hC0 : 0 ≤ C)
    {χ : Euc d → ℝ} (hχs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ)
    (hχc : HasCompactSupport χ)
    (hχone : ∀ x, ‖x‖ ≤ ρ → χ x = 1)
    (hχzero : ∀ x, 2 * ρ ≤ ‖x‖ → χ x = 0)
    (hχB : ∀ k ≤ q + 2, ∀ x, ‖iteratedFDeriv ℝ k χ x‖ ≤ C)
    (f : ℕ → Euc d → ℝ) (hf : ∀ n, IsR2Test (f n))
    (hE : ∀ n, weightedSobolevE (q + 2) P (f n) ≤ 1) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧
      CauchySeq (fun n => HRS.MS.R26T3.r26t3_jet q (P + 2)
        (fun x => χ x * f (σ n) x)) := by
  let L : ℝ := ∑ j ∈ Finset.range (q + 3),
    ∑ k ∈ Finset.range (j + 1),
      (j.choose k : ℝ) * C * (d : ℝ) ^ (j - k)
  let N : ℝ := (Fintype.card
    (HRS.MS.ProClosureS111.WeightedJetIndex d (q + 2)) : ℝ) + 1
  let K : ℝ := N * L
  let B : ℝ := K + 1
  let a : ℝ := B⁻¹
  have hcoeff : ∀ j, ∀ k ∈ Finset.range (j + 1),
      0 ≤ (j.choose k : ℝ) * C * (d : ℝ) ^ (j - k) := by
    intro j k hk
    positivity
  have hL : 0 ≤ L := by
    dsimp [L]
    refine Finset.sum_nonneg fun j hj => ?_
    exact Finset.sum_nonneg fun k hk => hcoeff j k hk
  have hK : 0 ≤ K := by
    dsimp [K, N]
    positivity
  have hB : 0 < B := by dsimp [B]; linarith
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hratio : a * K ≤ 1 := by
    have hdiv : K / (K + 1) ≤ 1 := by
      apply (div_le_iff₀ (by linarith : 0 < K + 1)).2
      linarith
    calc
      a * K = K / (K + 1) := by
        dsimp [a, B]
        rw [div_eq_mul_inv]
        ring
      _ ≤ 1 := hdiv
  let u : ℕ → Euc d → ℝ := fun n x => χ x * f n x
  let g : ℕ → Euc d → ℝ := fun n => a • u n
  have hu : ∀ n, IsR2Test (u n) := by
    intro n
    exact ⟨hχs.mul (hf n).1, hχc.mul_right⟩
  have hsupp : ∀ n, tsupport (g n) ⊆ Metric.closedBall 0 (2 * ρ) := by
    intro n
    refine closure_minimal ?_ (Metric.isClosed_closedBall)
    intro x hx
    by_contra hxball
    apply Function.mem_support.1 hx
    have hxnot : ¬ ‖x‖ ≤ 2 * ρ := by
      simpa [Metric.mem_closedBall, dist_zero_right] using hxball
    have hxnorm : 2 * ρ ≤ ‖x‖ := le_of_not_ge hxnot
    simp [g, u, hχzero x hxnorm]
  have hg : ∀ n, IsR2Test (g n) := by
    intro n
    refine ⟨(hu n).1.const_smul a, ?_⟩
    exact HasCompactSupport.of_support_subset_isCompact
      (isCompact_closedBall (0 : Euc d) (2 * ρ))
      ((subset_tsupport (g n)).trans (hsupp n))
  have hprodE : ∀ n, weightedSobolevE (q + 2) P (u n) ≤ ENNReal.ofReal K := by
    intro n
    have hmul := fp81s21_weightedRellich_cutoff_product_energy_le
      (d := d) (q := q) (P := P) (C := C) hC0 hχs (hf n).1 hχB
    calc
      weightedSobolevE (q + 2) P (u n) ≤ ENNReal.ofReal K * weightedSobolevE (q + 2) P (f n) := by
        simpa [u, K, N, L] using hmul
      _ ≤ ENNReal.ofReal K * 1 := by
        simpa [mul_comm] using
          (mul_le_mul_left (hE n) (ENNReal.ofReal K))
      _ = ENNReal.ofReal K := by rw [mul_one]
  have hscaledE : ∀ n, weightedSobolevE (q + 2) P (g n) ≤ 1 := by
    intro n
    rw [show g n = a • u n by rfl,
      fp81s21_weightedRellich_weightedSobolevE_nonneg_smul ha (hu n).1]
    calc
      ENNReal.ofReal a * weightedSobolevE (q + 2) P (u n)
          ≤ ENNReal.ofReal a * ENNReal.ofReal K := by
              simpa [mul_comm] using
                (mul_le_mul_left (hprodE n) (ENNReal.ofReal a))
      _ = ENNReal.ofReal (a * K) := by rw [← ENNReal.ofReal_mul ha]
      _ ≤ 1 := by
        calc
          ENNReal.ofReal (a * K) ≤ ENNReal.ofReal 1 :=
            ENNReal.ofReal_le_ofReal hratio
          _ = 1 := by norm_num
  obtain ⟨σ, hσ, hc⟩ := fp81s21_weightedRellich_localSupport_cauchy
    d q P (2 * ρ) (by linarith) g hg hsupp hscaledE
  have hW_g : ∀ n, IsR2WeightedTest q (P + 2) (g n) := by
    intro n
    exact ⟨(hg n).1.of_le (by exact_mod_cast le_top),
      HRS.MS.R26T3.s21k2_w09_wE_fin (hg n).1 (hsupp n) q (P + 2)⟩
  have hW_zero : IsR2WeightedTest q (P + 2) (0 : Euc d → ℝ) := by
    refine ⟨contDiff_const, ?_⟩
    have hs0 : tsupport (0 : Euc d → ℝ) ⊆ Metric.closedBall (0 : Euc d) (2 * ρ) := by
      intro x hx
      simp at hx
    exact HRS.MS.R26T3.s21k2_w09_wE_fin contDiff_const hs0 q (P + 2)
  have hjetZero : HRS.MS.R26T3.r26t3_jet q (P + 2) (0 : Euc d → ℝ) = 0 := by
    have hfun : HRS.MS.R26T3.r26t3_jetfun q (0 : Euc d → ℝ) = 0 := by
      funext x
      ext i
      simp [HRS.MS.R26T3.r26t3_jetfun, HRS.Whole.partialDeriv]
    have hmem : MemLp (HRS.MS.R26T3.r26t3_jetfun q (0 : Euc d → ℝ)) 2
        (HRS.MS.R26T3.r26t3_weightMeasure d (P + 2)) := by
      rw [hfun]
      exact MemLp.zero
    rw [HRS.MS.R26T3.r26t3_jet, dif_pos hmem]
    rw [MemLp.toLp_congr hmem MemLp.zero
      (Filter.Eventually.of_forall fun x => congrFun hfun x), MemLp.toLp_zero]
  have hrecover : ∀ n,
      HRS.MS.R26T3.r26t3_jet q (P + 2) (u n) =
        B • HRS.MS.R26T3.r26t3_jet q (P + 2) (g n) := by
    intro n
    have hlin := HRS.MS.R26T3.r26t3_jet_linear (P + 2)
      (0 : Euc d → ℝ) (g n) hW_zero (hW_g n) B
    have hfun : (0 : Euc d → ℝ) + B • g n = u n := by
      funext x
      change 0 + B * (a * (χ x * f n x)) = χ x * f n x
      have hBa : B * a = 1 := by
        dsimp [a]
        exact mul_inv_cancel₀ hB.ne'
      rw [zero_add, ← mul_assoc, hBa, one_mul]
    rw [hfun] at hlin
    simpa only [hjetZero, zero_add] using hlin
  refine ⟨σ, hσ, ?_⟩
  rw [Metric.cauchySeq_iff] at hc ⊢
  intro ε hε
  obtain ⟨N, hN⟩ := hc (ε / B) (div_pos hε hB)
  refine ⟨N, ?_⟩
  intro m hm n hn
  have hd := hN m hm n hn
  have hdist : dist
      (HRS.MS.R26T3.r26t3_jet q (P + 2) (u (σ m)))
      (HRS.MS.R26T3.r26t3_jet q (P + 2) (u (σ n))) =
        B * dist (HRS.MS.R26T3.r26t3_jet q (P + 2) (g (σ m)))
          (HRS.MS.R26T3.r26t3_jet q (P + 2) (g (σ n))) := by
    rw [hrecover, hrecover, dist_eq_norm, dist_eq_norm, ← smul_sub,
      norm_smul, Real.norm_eq_abs, abs_of_pos hB]
  rw [hdist]
  calc
    B * dist (HRS.MS.R26T3.r26t3_jet q (P + 2) (g (σ m)))
        (HRS.MS.R26T3.r26t3_jet q (P + 2) (g (σ n)))
      < B * (ε / B) := mul_lt_mul_of_pos_left hd hB
    _ = ε := by field_simp

/-- The fixed-cutoff sequence result applies to the scaled bump supplied by
the uniform cutoff theorem. -/
theorem fp81s21_weightedRellich_cutoffFamily_cauchy
    {d q : ℕ} {P ρ : ℝ} (hρ : 1 ≤ ρ)
    (f : ℕ → Euc d → ℝ) (hf : ∀ n, IsR2Test (f n))
    (hE : ∀ n, weightedSobolevE (q + 2) P (f n) ≤ 1) :
    ∃ χ : Euc d → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ ∧ HasCompactSupport χ ∧
      (∀ x, ‖x‖ ≤ ρ → χ x = 1) ∧
      (∀ x, 2 * ρ ≤ ‖x‖ → χ x = 0) ∧
      ∃ σ : ℕ → ℕ, StrictMono σ ∧
        CauchySeq (fun n => HRS.MS.R26T3.r26t3_jet q (P + 2)
          (fun x => χ x * f (σ n) x)) := by
  obtain ⟨C, hC0, hCut⟩ :=
    fp81s21_weightedRellich_scaledCutoff_uniform (d := d) (q := q)
  obtain ⟨χ, hχs, hχc, hχone, hχzero, hχB⟩ := hCut ρ hρ
  refine ⟨χ, hχs, hχc, hχone, hχzero, ?_⟩
  exact fp81s21_weightedRellich_fixedCutoffFamily_cauchy
    hρ hC0 hχs hχc hχone hχzero hχB f hf hE

#print axioms HRS.Fp81.S21.fp81s21_weightedRellich_weightedSobolevE_nonneg_smul
#print axioms HRS.Fp81.S21.fp81s21_weightedRellich_fixedCutoffFamily_cauchy
#print axioms HRS.Fp81.S21.fp81s21_weightedRellich_cutoffFamily_cauchy

end HRS.Fp81.S21
