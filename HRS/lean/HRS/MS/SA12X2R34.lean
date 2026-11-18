import HRS.MS.SA12X2R34B
import HRS.MS.SA12CellR33

/-!
# S.A.12 R34 (SA12X2), part C: `localized_product_jets`

`jetSq (m+1) 1 (a F) ≤ C ∑_k (jetSq m (χ_k) F + dissipSq m (χ_k) F)` for a `C^(m+1)` coefficient `a` with
bounded jets, and cutoffs `χ_k` with `∑_k χ_k² ≥ 1` on `tsupport a`. Pointwise Leibniz (part B), the
multilinear norm bound (part A), the cutoff, and the top-order reindexing `sa12_sum_snoc` (R33).
-/

set_option autoImplicit false
set_option maxHeartbeats 3200000

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped BigOperators ContDiff

namespace HRS.MH.AdjointRd.Phase2SA12

open HRS HRS.Whole HRS.MH.AdjointRd

variable {d : ℕ}

theorem sa12x2_jet_nonneg (m : ℕ) (w F : Euc d → ℝ) : 0 ≤ jetSq m w F := by
  unfold jetSq
  exact Finset.sum_nonneg fun j _ => mul_nonneg (Nat.cast_nonneg _)
    (Finset.sum_nonneg fun idx _ => integral_nonneg fun x => sq_nonneg _)

theorem sa12x2_dissip_nonneg (m : ℕ) (w F : Euc d → ℝ) : 0 ≤ dissipSq m w F := by
  unfold dissipSq
  exact Finset.sum_nonneg fun j _ => mul_nonneg (Nat.cast_nonneg _)
    (Finset.sum_nonneg fun idx _ => Finset.sum_nonneg fun i _ => integral_nonneg fun x => sq_nonneg _)

/-- Continuity of tuple partials of a `C^(m+1)` function. -/
theorem sa12x2_pd_cont {m : ℕ} {G : Euc d → ℝ} (hG : ContDiff ℝ (m + 1) G) {j : ℕ} (hj : j ≤ m + 1)
    (idx : Fin j → Fin d) : Continuous (fun x => partialDeriv idx G x) := by
  unfold partialDeriv
  exact (continuous_eval_const (fun l => EuclideanSpace.single (idx l) (1 : ℝ))).comp
    (hG.continuous_iteratedFDeriv (m := j) (by exact_mod_cast hj))

/-- Tuple partials of `a * F` vanish off `tsupport a`. -/
theorem sa12x2_pd_zero {a F : Euc d → ℝ} {j : ℕ} {x : Euc d} (hx : x ∉ tsupport a) (idx : Fin j → Fin d) :
    partialDeriv idx (fun y => a y * F y) x = 0 := by
  unfold partialDeriv
  have hsub : tsupport (iteratedFDeriv ℝ j (fun y => a y * F y)) ⊆ tsupport a :=
    (tsupport_iteratedFDeriv_subset (𝕜 := ℝ) (f := fun y => a y * F y) j).trans tsupport_mul_subset_left
  have hx' : x ∉ tsupport (iteratedFDeriv ℝ j (fun y => a y * F y)) := fun h => hx (hsub h)
  rw [image_eq_zero_of_notMem_tsupport hx']
  simp

/-- Algebraic identity: `χ² ∑_l d^l ∑_idx (∂^idx F)² = ∑_l ∑_idx d^l (χ ∂^idx F)²`. -/
theorem sa12x2_weight_pt (m : ℕ) (χ : Euc d → ℝ) (F : Euc d → ℝ) (x : Euc d) :
    χ x ^ 2 * (∑ l ∈ Finset.range (m + 2), (d : ℝ) ^ l * ∑ idx' : Fin l → Fin d, (partialDeriv idx' F x) ^ 2) =
      ∑ l ∈ Finset.range (m + 2), ∑ idx' : Fin l → Fin d, (d : ℝ) ^ l * (χ x * partialDeriv idx' F x) ^ 2 := by
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun idx _ => ?_
  ring

/-- Integrability and integral of the weighted tuple sum. -/
theorem sa12x2_weight_int (m : ℕ) (χ : Euc d → ℝ) (hχc : Continuous χ) (hχs : HasCompactSupport χ)
    {F : Euc d → ℝ} (hF : ContDiff ℝ (m + 1) F) :
    Integrable (fun x => χ x ^ 2 * (∑ l ∈ Finset.range (m + 2), (d : ℝ) ^ l *
        ∑ idx' : Fin l → Fin d, (partialDeriv idx' F x) ^ 2)) ∧
    ∫ x, χ x ^ 2 * (∑ l ∈ Finset.range (m + 2), (d : ℝ) ^ l *
        ∑ idx' : Fin l → Fin d, (partialDeriv idx' F x) ^ 2) =
      ∑ l ∈ Finset.range (m + 2), (d : ℝ) ^ l * ∑ idx' : Fin l → Fin d,
        ∫ x, (χ x * partialDeriv idx' F x) ^ 2 := by
  have hterm : ∀ l ∈ Finset.range (m + 2), ∀ idx' : Fin l → Fin d,
      Integrable (fun x => (d : ℝ) ^ l * (χ x * partialDeriv idx' F x) ^ 2) := by
    intro l hl idx'
    have hl' : l ≤ m + 1 := by have := Finset.mem_range.mp hl; omega
    have hc : Continuous (fun x => (χ x * partialDeriv idx' F x) ^ 2) :=
      ((hχc.mul (sa12x2_pd_cont hF hl' idx')).pow 2)
    have hcs0 : HasCompactSupport (fun x => χ x * partialDeriv idx' F x) := hχs.mul_right
    have hcs : HasCompactSupport (fun x => (χ x * partialDeriv idx' F x) ^ 2) :=
      hcs0.comp_left (g := fun t : ℝ => t ^ 2) (by simp)
    exact (hc.integrable_of_hasCompactSupport hcs).const_mul ((d : ℝ) ^ l)
  have hEq : (fun x => χ x ^ 2 * (∑ l ∈ Finset.range (m + 2), (d : ℝ) ^ l *
        ∑ idx' : Fin l → Fin d, (partialDeriv idx' F x) ^ 2)) =
      fun x => ∑ l ∈ Finset.range (m + 2), ∑ idx' : Fin l → Fin d,
        (d : ℝ) ^ l * (χ x * partialDeriv idx' F x) ^ 2 := funext fun x => sa12x2_weight_pt m χ F x
  rw [hEq]
  refine ⟨?_, ?_⟩
  · exact integrable_finset_sum _ fun l hl => integrable_finset_sum _ fun idx' _ => hterm l hl idx'
  · have key0 : ∫ x, ∑ l ∈ Finset.range (m + 2), ∑ idx' : Fin l → Fin d,
        (d : ℝ) ^ l * (χ x * partialDeriv idx' F x) ^ 2 =
        ∑ l ∈ Finset.range (m + 2), ∫ x, ∑ idx' : Fin l → Fin d,
          (d : ℝ) ^ l * (χ x * partialDeriv idx' F x) ^ 2 :=
      integral_finset_sum _ (fun l hl => integrable_finset_sum _ (fun idx' _ => hterm l hl idx'))
    rw [key0]
    refine Finset.sum_congr rfl fun l hl => ?_
    have key1 : ∫ x, ∑ idx' : Fin l → Fin d, (d : ℝ) ^ l * (χ x * partialDeriv idx' F x) ^ 2 =
        ∑ idx' : Fin l → Fin d, ∫ x, (d : ℝ) ^ l * (χ x * partialDeriv idx' F x) ^ 2 :=
      integral_finset_sum _ (fun idx' _ => hterm l hl idx')
    rw [key1, Finset.mul_sum]
    refine Finset.sum_congr rfl fun idx' _ => ?_
    rw [integral_const_mul]

theorem localized_product_jets (d m q : ℕ) (B : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ a F : Euc d → ℝ,
      ContDiff ℝ (m + 1) a → HasCompactSupport a → ContDiff ℝ ∞ F →
      (∀ j ≤ m + 1, ∀ x, ‖iteratedFDeriv ℝ j a x‖ ≤ B) →
      ∀ χ : Fin q → Euc d → ℝ,
      (∀ k, ContDiff ℝ (m + 1) (χ k) ∧ HasCompactSupport (χ k)) →
      (∀ x ∈ tsupport a, 1 ≤ ∑ k : Fin q, (χ k x) ^ 2) →
      jetSq (m + 1) (fun _ => 1) (fun x => a x * F x) ≤
        C * ∑ k : Fin q, (jetSq m (χ k) F + dissipSq m (χ k) F) := by
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = B ^ 2 * ((2 : ℝ) ^ (m + 1)) ^ 2 * ((m : ℝ) + 2) := ⟨_, rfl⟩
  obtain ⟨A0, hA0⟩ : ∃ A0 : ℝ, A0 = ∑ j ∈ Finset.range (m + 2), ((m + 1).choose j : ℝ) * (d : ℝ) ^ j :=
    ⟨_, rfl⟩
  obtain ⟨D, hD⟩ : ∃ D : ℝ, D = ∑ l ∈ Finset.range (m + 2), (d : ℝ) ^ l := ⟨_, rfl⟩
  have hA00 : 0 ≤ A0 := by
    rw [hA0]; exact Finset.sum_nonneg fun j _ => mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (Nat.cast_nonneg _) _)
  have hD0 : 0 ≤ D := by
    rw [hD]; exact Finset.sum_nonneg fun l _ => pow_nonneg (Nat.cast_nonneg _) _
  have hK0 : 0 ≤ K := by rw [hK]; positivity
  refine ⟨A0 * K * D + 1, ?_, ?_⟩
  · have := mul_nonneg (mul_nonneg hA00 hK0) hD0
    linarith
  intro a F ha hac hF hB χ hχ hcut
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0 (by omega) 0)
  have hle : ((m + 1 : ℕ) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by exact_mod_cast le_top
  have hFm : ContDiff ℝ (m + 1) F := hF.of_le hle
  have hχc : ∀ k, Continuous (χ k) := fun k => (hχ k).1.continuous
  -- tuple sums of the jet of `χ_k F`
  obtain ⟨Tk, hTk⟩ : ∃ T : Fin q → ℕ → ℝ,
      ∀ k l, T k l = ∑ idx' : Fin l → Fin d, ∫ x, (χ k x * partialDeriv idx' F x) ^ 2 :=
    ⟨fun k l => ∑ idx' : Fin l → Fin d, ∫ x, (χ k x * partialDeriv idx' F x) ^ 2, fun _ _ => rfl⟩
  have hTnn : ∀ k l, 0 ≤ Tk k l := fun k l => by
    rw [hTk]; exact Finset.sum_nonneg fun _ _ => integral_nonneg fun _ => sq_nonneg _
  -- the weight `W(x) = ∑_{l ≤ m+1} d^l ∑_idx (∂^idx F x)²`
  have hWnn : ∀ x : Euc d, 0 ≤ ∑ l ∈ Finset.range (m + 2), (d : ℝ) ^ l *
      ∑ idx' : Fin l → Fin d, (partialDeriv idx' F x) ^ 2 := fun x =>
    Finset.sum_nonneg fun l _ => mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _)
      (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  -- step 1: pointwise bound on the tuple partials of `a F`
  have hpt : ∀ j ≤ m + 1, ∀ (idx : Fin j → Fin d) (x : Euc d),
      (partialDeriv idx (fun y => a y * F y) x) ^ 2 ≤
        K * ∑ k : Fin q, (χ k x) ^ 2 * (∑ l ∈ Finset.range (m + 2), (d : ℝ) ^ l *
          ∑ idx' : Fin l → Fin d, (partialDeriv idx' F x) ^ 2) := by
    intro j hj idx x
    by_cases hx : x ∈ tsupport a
    · have hT : (partialDeriv idx (fun y => a y * F y) x) ^ 2 ≤
          ‖iteratedFDeriv ℝ j (fun y => a y * F y) x‖ ^ 2 := by
        have h1 := (iteratedFDeriv ℝ j (fun y => a y * F y) x).le_opNorm
          (fun l => EuclideanSpace.single (idx l) (1 : ℝ))
        have h2 : ∏ l, ‖(EuclideanSpace.single (idx l) (1 : ℝ) : Euc d)‖ = 1 := by
          simp [EuclideanSpace.norm_single]
        rw [h2, mul_one] at h1
        have h3 : |partialDeriv idx (fun y => a y * F y) x| ≤
            ‖iteratedFDeriv ℝ j (fun y => a y * F y) x‖ := by
          rw [← Real.norm_eq_abs]; exact h1
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h3 2
      have hleib := sa12x2_leib_pt hB0 ha hFm hB hj x
      have hsumF : ∑ i ∈ Finset.range (j + 1), ‖iteratedFDeriv ℝ (j - i) F x‖ ^ 2 ≤
          ∑ l ∈ Finset.range (m + 2), (d : ℝ) ^ l * ∑ idx' : Fin l → Fin d, (partialDeriv idx' F x) ^ 2 := by
        have e1 : ∑ i ∈ Finset.range (j + 1), ‖iteratedFDeriv ℝ (j - i) F x‖ ^ 2 ≤
            ∑ i ∈ Finset.range (j + 1), (d : ℝ) ^ (j - i) *
              ∑ idx' : Fin (j - i) → Fin d, (partialDeriv idx' F x) ^ 2 :=
          Finset.sum_le_sum fun i _ => sa12x2_multi_sq_le (d := d) (iteratedFDeriv ℝ (j - i) F x)
        have e2 : ∑ i ∈ Finset.range (j + 1), (d : ℝ) ^ (j - i) *
              ∑ idx' : Fin (j - i) → Fin d, (partialDeriv idx' F x) ^ 2 =
            ∑ l ∈ Finset.range (j + 1), (d : ℝ) ^ l * ∑ idx' : Fin l → Fin d, (partialDeriv idx' F x) ^ 2 := by
          have := Finset.sum_range_reflect
            (fun l => (d : ℝ) ^ l * ∑ idx' : Fin l → Fin d, (partialDeriv idx' F x) ^ 2) (j + 1)
          simpa using this
        have e3 : ∑ l ∈ Finset.range (j + 1), (d : ℝ) ^ l * ∑ idx' : Fin l → Fin d, (partialDeriv idx' F x) ^ 2 ≤
            ∑ l ∈ Finset.range (m + 2), (d : ℝ) ^ l * ∑ idx' : Fin l → Fin d, (partialDeriv idx' F x) ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 (by omega))
            fun l _ _ => mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _)
              (Finset.sum_nonneg fun _ _ => sq_nonneg _)
        linarith
      have hC : B ^ 2 * ((2 : ℝ) ^ j) ^ 2 * ((j : ℝ) + 1) ≤ K := by
        have h2j : (2 : ℝ) ^ j ≤ 2 ^ (m + 1) := pow_le_pow_right₀ (by norm_num) hj
        have hsq : ((2 : ℝ) ^ j) ^ 2 ≤ ((2 : ℝ) ^ (m + 1)) ^ 2 := pow_le_pow_left₀ (by positivity) h2j 2
        have hjm : (j : ℝ) + 1 ≤ (m : ℝ) + 2 := by
          have : (j : ℝ) ≤ m + 1 := by exact_mod_cast hj
          linarith
        rw [hK]
        gcongr
      have hKW : K * ∑ k : Fin q, (χ k x) ^ 2 * (∑ l ∈ Finset.range (m + 2), (d : ℝ) ^ l *
            ∑ idx' : Fin l → Fin d, (partialDeriv idx' F x) ^ 2) ≥ 0 := by
        exact mul_nonneg hK0 (Finset.sum_nonneg fun k _ => mul_nonneg (sq_nonneg _) (hWnn x))
      have hW : (partialDeriv idx (fun y => a y * F y) x) ^ 2 ≤ K * ∑ l ∈ Finset.range (m + 2),
          (d : ℝ) ^ l * ∑ idx' : Fin l → Fin d, (partialDeriv idx' F x) ^ 2 := by
        calc (partialDeriv idx (fun y => a y * F y) x) ^ 2
            ≤ ‖iteratedFDeriv ℝ j (fun y => a y * F y) x‖ ^ 2 := hT
          _ ≤ B ^ 2 * ((2 : ℝ) ^ j) ^ 2 * ((j : ℝ) + 1) *
                ∑ i ∈ Finset.range (j + 1), ‖iteratedFDeriv ℝ (j - i) F x‖ ^ 2 := hleib
          _ ≤ K * ∑ l ∈ Finset.range (m + 2), (d : ℝ) ^ l *
                ∑ idx' : Fin l → Fin d, (partialDeriv idx' F x) ^ 2 :=
              mul_le_mul hC hsumF (Finset.sum_nonneg fun _ _ => sq_nonneg _) hK0
      have hcut' := hcut x hx
      have hWx := hWnn x
      have hWs : (∑ l ∈ Finset.range (m + 2), (d : ℝ) ^ l *
          ∑ idx' : Fin l → Fin d, (partialDeriv idx' F x) ^ 2) ≤
          (∑ l ∈ Finset.range (m + 2), (d : ℝ) ^ l *
          ∑ idx' : Fin l → Fin d, (partialDeriv idx' F x) ^ 2) * ∑ k : Fin q, (χ k x) ^ 2 :=
        le_mul_of_one_le_right hWx hcut'
      have hsplit : (∑ l ∈ Finset.range (m + 2), (d : ℝ) ^ l *
          ∑ idx' : Fin l → Fin d, (partialDeriv idx' F x) ^ 2) * ∑ k : Fin q, (χ k x) ^ 2 =
          ∑ k : Fin q, (χ k x) ^ 2 * (∑ l ∈ Finset.range (m + 2), (d : ℝ) ^ l *
          ∑ idx' : Fin l → Fin d, (partialDeriv idx' F x) ^ 2) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun k _ => mul_comm _ _
      calc (partialDeriv idx (fun y => a y * F y) x) ^ 2
          ≤ K * (∑ l ∈ Finset.range (m + 2), (d : ℝ) ^ l *
                ∑ idx' : Fin l → Fin d, (partialDeriv idx' F x) ^ 2) := hW
        _ ≤ K * ((∑ l ∈ Finset.range (m + 2), (d : ℝ) ^ l *
                ∑ idx' : Fin l → Fin d, (partialDeriv idx' F x) ^ 2) * ∑ k : Fin q, (χ k x) ^ 2) :=
            mul_le_mul_of_nonneg_left hWs hK0
        _ = K * ∑ k : Fin q, (χ k x) ^ 2 * (∑ l ∈ Finset.range (m + 2), (d : ℝ) ^ l *
                ∑ idx' : Fin l → Fin d, (partialDeriv idx' F x) ^ 2) := by rw [hsplit]
    · rw [sa12x2_pd_zero hx idx]
      have : 0 ≤ K * ∑ k : Fin q, (χ k x) ^ 2 * (∑ l ∈ Finset.range (m + 2), (d : ℝ) ^ l *
          ∑ idx' : Fin l → Fin d, (partialDeriv idx' F x) ^ 2) :=
        mul_nonneg hK0 (Finset.sum_nonneg fun k _ => mul_nonneg (sq_nonneg _) (hWnn x))
      simpa using this
  -- the total `X = ∑_k ∑_l d^l T_{k,l}`
  obtain ⟨X, hX⟩ : ∃ X : ℝ, X = ∑ k : Fin q, ∑ l ∈ Finset.range (m + 2), (d : ℝ) ^ l * Tk k l := ⟨_, rfl⟩
  have hX0 : 0 ≤ X := by
    rw [hX]; exact Finset.sum_nonneg fun k _ => Finset.sum_nonneg fun l _ =>
      mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _) (hTnn k l)
  -- step 2: integrate, per tuple
  have hint_idx : ∀ j ≤ m + 1, ∀ idx : Fin j → Fin d,
      ∫ x, (partialDeriv idx (fun y => a y * F y) x) ^ 2 ≤ K * X := by
    intro j hj idx
    have hG : Integrable (fun x => K * ∑ k : Fin q, (χ k x) ^ 2 * (∑ l ∈ Finset.range (m + 2),
        (d : ℝ) ^ l * ∑ idx' : Fin l → Fin d, (partialDeriv idx' F x) ^ 2)) := by
      refine Integrable.const_mul ?_ K
      exact integrable_finset_sum _ fun k _ => (sa12x2_weight_int m (χ k) (hχc k) (hχ k).2 hFm).1
    calc ∫ x, (partialDeriv idx (fun y => a y * F y) x) ^ 2
        ≤ ∫ x, K * ∑ k : Fin q, (χ k x) ^ 2 * (∑ l ∈ Finset.range (m + 2), (d : ℝ) ^ l *
            ∑ idx' : Fin l → Fin d, (partialDeriv idx' F x) ^ 2) :=
          integral_mono_of_nonneg (Eventually.of_forall fun x => sq_nonneg _) hG
            (Eventually.of_forall fun x => hpt j hj idx x)
      _ = K * ∑ k : Fin q, ∫ x, (χ k x) ^ 2 * (∑ l ∈ Finset.range (m + 2), (d : ℝ) ^ l *
            ∑ idx' : Fin l → Fin d, (partialDeriv idx' F x) ^ 2) := by
          rw [integral_const_mul, integral_finset_sum _ fun k _ =>
            (sa12x2_weight_int m (χ k) (hχc k) (hχ k).2 hFm).1]
      _ = K * X := by
          congr 1
          rw [hX]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [(sa12x2_weight_int m (χ k) (hχc k) (hχ k).2 hFm).2]
          refine Finset.sum_congr rfl fun l _ => ?_
          rw [hTk]
  -- step 3: sum over the tuples of length j, then over j
  have hLsum : ∀ j ∈ Finset.range (m + 2), ((m + 1).choose j : ℝ) *
      ∑ idx : Fin j → Fin d, ∫ x, (partialDeriv idx (fun y => a y * F y) x) ^ 2 ≤
        ((m + 1).choose j : ℝ) * ((d : ℝ) ^ j * (K * X)) := by
    intro j hj
    have hj' : j ≤ m + 1 := by have := Finset.mem_range.mp hj; omega
    refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
    calc ∑ idx : Fin j → Fin d, ∫ x, (partialDeriv idx (fun y => a y * F y) x) ^ 2
        ≤ ∑ idx : Fin j → Fin d, K * X := Finset.sum_le_sum fun idx _ => hint_idx j hj' idx
      _ = (d : ℝ) ^ j * (K * X) := by
          simp [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin]
  have hLHS : jetSq (m + 1) (fun _ => (1 : ℝ)) (fun x => a x * F x) =
      ∑ j ∈ Finset.range (m + 2), ((m + 1).choose j : ℝ) *
        ∑ idx : Fin j → Fin d, ∫ x, (partialDeriv idx (fun y => a y * F y) x) ^ 2 := by
    unfold jetSq; simp only [one_mul]
  -- step 4: the top order and the lower orders are controlled by the cutoff jets
  have hTle : ∀ k : Fin q, ∀ l ∈ Finset.range (m + 2), Tk k l ≤
      jetSq m (χ k) F + dissipSq m (χ k) F := by
    intro k l hl
    have hl' := Finset.mem_range.mp hl
    have hjn := sa12x2_jet_nonneg m (χ k) F
    have hdn := sa12x2_dissip_nonneg m (χ k) F
    rcases Nat.lt_or_ge l (m + 1) with h | h
    · have hlm : l ≤ m := by omega
      have hc1 : (1 : ℝ) ≤ (m.choose l : ℝ) := by exact_mod_cast Nat.choose_pos hlm
      have h1 : Tk k l ≤ (m.choose l : ℝ) * Tk k l :=
        le_mul_of_one_le_left (hTnn k l) hc1
      have h2 : (m.choose l : ℝ) * Tk k l ≤ jetSq m (χ k) F := by
        rw [hTk]
        unfold jetSq
        exact Finset.single_le_sum (f := fun j => (m.choose j : ℝ) *
          ∑ idx' : Fin j → Fin d, ∫ x, (χ k x * partialDeriv idx' F x) ^ 2)
          (fun j _ => mul_nonneg (Nat.cast_nonneg _) (Finset.sum_nonneg fun _ _ =>
            integral_nonneg fun _ => sq_nonneg _))
          (Finset.mem_range.mpr (by omega))
      linarith
    · have hlm : l = m + 1 := by omega
      rw [hlm, hTk]
      have h3 := sa12_sum_snoc d m (fun idx => ∫ x, (χ k x * partialDeriv idx F x) ^ 2)
      have h5 : (m.choose m : ℝ) * ∑ idx : Fin m → Fin d, ∑ i : Fin d,
          ∫ x, (χ k x * partialDeriv (Fin.snoc idx i : Fin (m + 1) → Fin d) F x) ^ 2 ≤
          dissipSq m (χ k) F := by
        unfold dissipSq
        exact Finset.single_le_sum (f := fun j => (m.choose j : ℝ) * ∑ idx : Fin j → Fin d,
            ∑ i : Fin d, ∫ x, (χ k x * partialDeriv (Fin.snoc idx i : Fin (j + 1) → Fin d) F x) ^ 2)
          (fun j _ => mul_nonneg (Nat.cast_nonneg _) (Finset.sum_nonneg fun _ _ =>
            Finset.sum_nonneg fun _ _ => integral_nonneg fun _ => sq_nonneg _))
          (Finset.mem_range.mpr (by omega))
      rw [Nat.choose_self, Nat.cast_one, one_mul] at h5
      rw [h3]
      linarith
  -- step 5: `X ≤ D ∑_k S_k`
  have hsw : D * ∑ k : Fin q, (jetSq m (χ k) F + dissipSq m (χ k) F) =
      ∑ k : Fin q, ∑ l ∈ Finset.range (m + 2), (d : ℝ) ^ l * (jetSq m (χ k) F + dissipSq m (χ k) F) := by
    rw [hD, Finset.sum_mul]
    simp only [Finset.mul_sum]
    exact Finset.sum_comm
  have hXle : X ≤ D * ∑ k : Fin q, (jetSq m (χ k) F + dissipSq m (χ k) F) := by
    rw [hsw, hX]
    exact Finset.sum_le_sum fun k _ => Finset.sum_le_sum fun l hl =>
      mul_le_mul_of_nonneg_left (hTle k l hl) (pow_nonneg (Nat.cast_nonneg _) _)
  -- assemble
  have hsumS : 0 ≤ ∑ k : Fin q, (jetSq m (χ k) F + dissipSq m (χ k) F) :=
    Finset.sum_nonneg fun k _ => add_nonneg (sa12x2_jet_nonneg m (χ k) F) (sa12x2_dissip_nonneg m (χ k) F)
  rw [hLHS]
  calc ∑ j ∈ Finset.range (m + 2), ((m + 1).choose j : ℝ) *
        ∑ idx : Fin j → Fin d, ∫ x, (partialDeriv idx (fun y => a y * F y) x) ^ 2
      ≤ ∑ j ∈ Finset.range (m + 2), ((m + 1).choose j : ℝ) * ((d : ℝ) ^ j * (K * X)) :=
        Finset.sum_le_sum hLsum
    _ = A0 * K * X := by
        rw [hA0, Finset.sum_mul, Finset.sum_mul]
        refine Finset.sum_congr rfl fun j _ => ?_
        ring
    _ ≤ A0 * K * (D * ∑ k : Fin q, (jetSq m (χ k) F + dissipSq m (χ k) F)) :=
        mul_le_mul_of_nonneg_left hXle (mul_nonneg hA00 hK0)
    _ = (A0 * K * D) * ∑ k : Fin q, (jetSq m (χ k) F + dissipSq m (χ k) F) := by ring
    _ ≤ (A0 * K * D + 1) * ∑ k : Fin q, (jetSq m (χ k) F + dissipSq m (χ k) F) := by
        nlinarith

end HRS.MH.AdjointRd.Phase2SA12
