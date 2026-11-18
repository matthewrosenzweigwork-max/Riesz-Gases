import HRS.MS.SA12DE7M

/-!
# S.A.12(c), packet E7.07 (worker S82Z2), part N: weak limits of zero-extended jets are weak jets

`sa12de7_weak_limit_jets`: let `F n ∈ C^∞`, sets `S n` exhausting `ℝ^d` (every ball is eventually inside `S n`), whose
zero-extended jets `1_{S n} ∂^idx F n` (`j ≤ m`) lie in `L²` with weighted energy `∑_j C(m,j) ∑_idx ‖·‖² ≤ B²`, and suppose
`∫ F n ψ → ∫ u ψ` for every real `C_c^∞` test `ψ`.  Then there is an ordered family `G j idx ∈ L²` with
weighted energy `≤ B²`, `G 0 = u` against tests, and `G (j+1) (cons i idx) = ∂_i (G j idx)` against tests.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.SA12DE7

open HRS HRS.Whole HRS.MH.AdjointRd HRS.Whole.AppendixA HRS.Whole.Q09A

variable {d : ℕ}

theorem sa12de7_weak_limit_jets {m : ℕ} (F : ℕ → Euc d → ℝ) (u : Euc d → ℝ) (S : ℕ → Set (Euc d)) {B : ℝ}
    (hB0 : 0 ≤ B) (hF : ∀ n, ContDiff ℝ ∞ (F n))
    (hS : ∀ R : ℝ, ∀ᶠ n in atTop, Metric.closedBall (0 : Euc d) R ⊆ S n)
    (hmem : ∀ n j, j ≤ m → ∀ idx : Fin j → Fin d, MemLp ((S n).indicator (partialDeriv idx (F n))) 2 volume)
    (hbound : ∀ n, ∑ j ∈ Finset.range (m + 1), (m.choose j : ℝ) *
      ∑ idx : Fin j → Fin d, ∫ x, ((S n).indicator (partialDeriv idx (F n)) x) ^ 2 ≤ B ^ 2)
    (hconv : ∀ ψ : Euc d → ℝ, IsCcInfty ψ →
      Tendsto (fun n => ∫ x, F n x * ψ x) atTop (𝓝 (∫ x, u x * ψ x))) :
    ∃ G : (j : ℕ) → (Fin j → Fin d) → Euc d → ℝ,
      (∀ j, j ≤ m → ∀ idx : Fin j → Fin d, MemLp (G j idx) 2 volume) ∧
      (∑ j ∈ Finset.range (m + 1), (m.choose j : ℝ) * ∑ idx : Fin j → Fin d, ∫ x, (G j idx x) ^ 2 ≤ B ^ 2) ∧
      (∀ (idx : Fin 0 → Fin d) (ψ : Euc d → ℝ), IsCcInfty ψ → ∫ x, G 0 idx x * ψ x = ∫ x, u x * ψ x) ∧
      (∀ j, j < m → ∀ (i : Fin d) (idx : Fin j → Fin d) (ψ : Euc d → ℝ), IsCcInfty ψ →
        ∫ x, G (j + 1) (Fin.cons i idx : Fin (j + 1) → Fin d) x * ψ x =
          -∫ x, G j idx x * fderiv ℝ ψ x (EuclideanSpace.single i (1 : ℝ))) := by
  classical
  let Jf : ℕ → SA12Idx d m → Euc d → ℝ := fun n ι => (S n).indicator (partialDeriv ι.2 (F n))
  have hJm : ∀ n (ι : SA12Idx d m), MemLp (Jf n ι) 2 volume := fun n ι =>
    hmem n (ι.1 : ℕ) (Nat.lt_succ_iff.mp ι.1.2) ι.2
  let J : SA12Idx d m → ℕ → Lp ℝ 2 (volume : Measure (Euc d)) := fun ι n => (hJm n ι).toLp (Jf n ι)
  let w : SA12Idx d m → ℝ := fun ι => (m.choose (ι.1 : ℕ) : ℝ)
  have hw1 : ∀ ι, 1 ≤ w ι := fun ι => by
    have : 1 ≤ m.choose (ι.1 : ℕ) := Nat.choose_pos (Nat.lt_succ_iff.mp ι.1.2)
    show (1 : ℝ) ≤ (m.choose (ι.1 : ℕ) : ℝ)
    exact_mod_cast this
  have hnorm : ∀ n, ∑ ι, w ι * ‖J ι n‖ ^ 2 ≤ B ^ 2 := by
    intro n
    have e : ∀ ι : SA12Idx d m, w ι * ‖J ι n‖ ^ 2 =
        (m.choose (ι.1 : ℕ) : ℝ) * ∫ x, ((S n).indicator (partialDeriv ι.2 (F n)) x) ^ 2 := fun ι => by
      simp only [w, J, Jf]; rw [sa12de7_norm_sq_toLp]
    calc ∑ ι, w ι * ‖J ι n‖ ^ 2
        = ∑ ι : SA12Idx d m, (m.choose (ι.1 : ℕ) : ℝ) *
            ∫ x, ((S n).indicator (partialDeriv ι.2 (F n)) x) ^ 2 := Finset.sum_congr rfl fun ι _ => e ι
      _ = _ := sa12de7_sigma_sum m (fun j idx => ∫ x, ((S n).indicator (partialDeriv idx (F n)) x) ^ 2)
      _ ≤ B ^ 2 := hbound n
  have hB : ∀ ι n, ‖J ι n‖ ≤ B := by
    intro ι n
    have h1 : w ι * ‖J ι n‖ ^ 2 ≤ ∑ ι', w ι' * ‖J ι' n‖ ^ 2 :=
      Finset.single_le_sum (f := fun ι' => w ι' * ‖J ι' n‖ ^ 2)
        (fun ι' _ => mul_nonneg (by linarith [hw1 ι']) (sq_nonneg _)) (Finset.mem_univ ι)
    have h2 : ‖J ι n‖ ^ 2 ≤ B ^ 2 := by nlinarith [hw1 ι, sq_nonneg ‖J ι n‖, hnorm n]
    exact (sq_le_sq₀ (norm_nonneg _) hB0).1 h2
  obtain ⟨φ, g, hφ, hlim⟩ := sa12de7_weak_subseq_family J hB
  have hlsc := sa12de7_weighted_lsc w (fun ι => by linarith [hw1 ι]) (fun ι n => J ι (φ n)) g
    (fun n => hnorm (φ n)) (fun ι v => hlim ι v)
  have KC : ∀ (ι : SA12Idx d m) (ψ : Euc d → ℝ), IsCcInfty ψ →
      Tendsto (fun n => ∫ x, partialDeriv ι.2 (F (φ n)) x * ψ x) atTop (𝓝 (∫ x, g ι x * ψ x)) := by
    intro ι ψ hψ
    have h1 := hlim ι ((sa12de7_cc_memLp hψ).toLp ψ)
    rw [sa12de7_inner_lp (g ι) hψ] at h1
    obtain ⟨R, hR⟩ := hψ.2.isCompact.isBounded.subset_closedBall (0 : Euc d)
    have hev : ∀ᶠ n in atTop, Metric.closedBall (0 : Euc d) R ⊆ S (φ n) :=
      hφ.tendsto_atTop.eventually (hS R)
    refine h1.congr' (hev.mono fun n hn => ?_)
    show inner ℝ ((hJm (φ n) ι).toLp (Jf (φ n) ι)) _ = _
    rw [sa12de7_inner_toLp (hJm (φ n) ι) hψ]
    exact integral_congr_ae (Eventually.of_forall fun x => sa12de7_indicator_mul (hR.trans hn) x)
  let G : (j : ℕ) → (Fin j → Fin d) → Euc d → ℝ := fun j idx =>
    if h : j ≤ m then ⇑(g ⟨⟨j, Nat.lt_succ_of_le h⟩, idx⟩) else fun _ => 0
  have hG : ∀ j (h : j ≤ m) (idx : Fin j → Fin d),
      G j idx = ⇑(g ⟨⟨j, Nat.lt_succ_of_le h⟩, idx⟩) := fun j h idx => by simp only [G, dif_pos h]
  refine ⟨G, ?_, ?_, ?_, ?_⟩
  · intro j hj idx
    rw [hG j hj idx]
    exact Lp.memLp _
  · have e : ∀ ι : SA12Idx d m, ∫ x, (G ι.1 ι.2 x) ^ 2 = ‖g ι‖ ^ 2 := fun ι => by
      rw [hG (ι.1 : ℕ) (Nat.lt_succ_iff.mp ι.1.2) ι.2, sa12de7_norm_sq_lp]
    calc ∑ j ∈ Finset.range (m + 1), (m.choose j : ℝ) * ∑ idx : Fin j → Fin d, ∫ x, (G j idx x) ^ 2
        = ∑ ι : SA12Idx d m, (m.choose (ι.1 : ℕ) : ℝ) * ∫ x, (G ι.1 ι.2 x) ^ 2 :=
          (sa12de7_sigma_sum m (fun j idx => ∫ x, (G j idx x) ^ 2)).symm
      _ = ∑ ι, w ι * ‖g ι‖ ^ 2 := Finset.sum_congr rfl fun ι _ => by rw [e ι]
      _ ≤ B ^ 2 := hlsc
  · intro idx ψ hψ
    have h1 := KC ⟨⟨0, Nat.succ_pos m⟩, idx⟩ ψ hψ
    have h2 : Tendsto (fun n => ∫ x, partialDeriv idx (F (φ n)) x * ψ x) atTop (𝓝 (∫ x, u x * ψ x)) :=
      ((hconv ψ hψ).comp hφ.tendsto_atTop).congr fun n =>
        integral_congr_ae (Eventually.of_forall fun x => by
          show F (φ n) x * ψ x = partialDeriv idx (F (φ n)) x * ψ x
          rw [sa12de7_partialDeriv_zero])
    rw [hG 0 (Nat.zero_le _) idx]
    exact tendsto_nhds_unique h1 h2
  · intro j hj i idx ψ hψ
    have hjm : j ≤ m := hj.le
    have hjm1 : j + 1 ≤ m := hj
    have h1 := KC ⟨⟨j + 1, Nat.lt_succ_of_le hjm1⟩, (Fin.cons i idx : Fin (j + 1) → Fin d)⟩ ψ hψ
    have h2 := (KC ⟨⟨j, Nat.lt_succ_of_le hjm⟩, idx⟩ _ (sa12de7_cc_fderiv hψ i)).neg
    have h3 : Tendsto (fun n => -∫ x, partialDeriv idx (F (φ n)) x *
        fderiv ℝ ψ x (EuclideanSpace.single i (1 : ℝ))) atTop
        (𝓝 (∫ x, g ⟨⟨j + 1, Nat.lt_succ_of_le hjm1⟩, (Fin.cons i idx : Fin (j + 1) → Fin d)⟩ x * ψ x)) := by
      refine h1.congr fun n => ?_
      have e1 : ∫ x, partialDeriv (Fin.cons i idx : Fin (j + 1) → Fin d) (F (φ n)) x * ψ x =
          ∫ x, fderiv ℝ (partialDeriv idx (F (φ n))) x (EuclideanSpace.single i (1 : ℝ)) * ψ x :=
        integral_congr_ae (Eventually.of_forall fun x =>
          congrArg (fun t => t * ψ x) (sa12de7_partialDeriv_cons (hF (φ n)) i idx x))
      show _ = -_
      rw [e1, sa12de7_ibp_smooth (sa12de7_partialDeriv_contDiff (hF (φ n)) idx) hψ i]
    rw [hG (j + 1) hjm1 (Fin.cons i idx), hG j hjm idx]
    exact tendsto_nhds_unique h3 h2

end HRS.MS.SA12DE7
