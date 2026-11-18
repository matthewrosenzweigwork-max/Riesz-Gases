import HRS.MS.SA12X5L3

/-!
# S.A.12 X5 LOC1: `jetSq m w (ΔF) ≤ d * jetSq (m+2) w F`
-/

set_option autoImplicit false
set_option maxHeartbeats 3200000

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MH.AdjointRd.Phase2SA12X5

open HRS HRS.Whole HRS.Whole.AppendixA HRS.MH.AdjointRd HRS.MH.AdjointRd.Phase2SA12Near HRS.MS.UniqT3

variable {d : ℕ}

theorem sa12x5_loc_D1_smooth (i : Fin d) {G : Euc d → ℝ} (hG : ContDiff ℝ ∞ G) :
    ContDiff ℝ ∞ (D1 i G) :=
  (hG.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

theorem sa12x5_loc_pd_lap {F : Euc d → ℝ} (hF : ContDiff ℝ ∞ F) {n : ℕ} (idx : Fin n → Fin d) (x : Euc d) :
    partialDeriv idx (fun y => Laplacian.laplacian F y) x =
      ∑ i : Fin d, partialDeriv (Fin.cons i (Fin.cons i idx : Fin (n + 1) → Fin d) : Fin (n + 2) → Fin d) F x := by
  have hfun : (fun y => Laplacian.laplacian F y) = fun y => ∑ i ∈ Finset.univ, (1 : ℝ) * D1 i (D1 i F) y := by
    funext y
    rw [lap_eq (sa12z3_cd_of_inf hF 2) y]; simp
  rw [hfun, sa12z3_pd_sum Finset.univ (fun i => D1 i (D1 i F)) (fun _ => 1)
    (fun i _ => sa12z3_cd_of_inf (sa12x5_loc_D1_smooth i (sa12x5_loc_D1_smooth i hF)) n) idx x]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [one_mul]
  have e1 : partialDeriv idx (D1 i (D1 i F)) x = D1 i (partialDeriv idx (D1 i F)) x :=
    sa12z3_pd_D1_comm i n (D1 i F) (sa12z3_cd_of_inf (sa12x5_loc_D1_smooth i hF) _) idx x
  have e2 : partialDeriv idx (D1 i F) = fun y => D1 i (partialDeriv idx F) y :=
    funext fun y => sa12z3_pd_D1_comm i n F (sa12z3_cd_of_inf hF _) idx y
  have e3 : partialDeriv (Fin.cons i (Fin.cons i idx : Fin (n + 1) → Fin d) : Fin (n + 2) → Fin d) F x =
      D1 i (partialDeriv (Fin.cons i idx : Fin (n + 1) → Fin d) F) x :=
    sa12z3_pd_cons (Fin.cons i idx) i (sa12z3_cd_of_inf hF _) x
  have e4 : partialDeriv (Fin.cons i idx : Fin (n + 1) → Fin d) F = fun y => D1 i (partialDeriv idx F) y :=
    funext fun y => sa12z3_pd_cons idx i (sa12z3_cd_of_inf hF _) y
  rw [e1, e2, e3, e4]

theorem sa12x5_loc_choose (m j : ℕ) : Nat.choose m j ≤ Nat.choose (m + 2) (j + 2) := by
  have h1 : Nat.choose (m + 1) (j + 1) = Nat.choose m j + Nat.choose m (j + 1) := Nat.choose_succ_succ m j
  have h2 : Nat.choose (m + 2) (j + 2) = Nat.choose (m + 1) (j + 1) + Nat.choose (m + 1) (j + 2) :=
    Nat.choose_succ_succ (m + 1) (j + 1)
  omega

theorem sa12x5_jetSq_lap_le (m : ℕ) {w : Euc d → ℝ} (hw : Continuous w) (hwc : HasCompactSupport w)
    {F : Euc d → ℝ} (hF : ContDiff ℝ ∞ F) :
    jetSq m w (fun x => Laplacian.laplacian F x) ≤ (d : ℝ) * jetSq (m + 2) w F := by
  set T : ℕ → ℝ := fun k => ∑ idx : Fin k → Fin d, ∫ x, (w x * partialDeriv idx F x) ^ 2 with hT
  have hT0 : ∀ k, 0 ≤ T k := fun k =>
    Finset.sum_nonneg fun idx _ => sa12x5_loc_integral_nonneg w F idx
  have pt : ∀ {n : ℕ} (idx : Fin n → Fin d),
      ∫ x, (w x * partialDeriv idx (fun y => Laplacian.laplacian F y) x) ^ 2 ≤
        (d : ℝ) * ∑ i : Fin d, ∫ x, (w x * partialDeriv
          (Fin.cons i (Fin.cons i idx : Fin (n + 1) → Fin d) : Fin (n + 2) → Fin d) F x) ^ 2 := by
    intro n idx
    have hi : ∀ i : Fin d, Integrable (fun x => (w x * partialDeriv
        (Fin.cons i (Fin.cons i idx : Fin (n + 1) → Fin d) : Fin (n + 2) → Fin d) F x) ^ 2) :=
      fun i => sa12x5_loc_integrable hw hwc (sa12z3_pd_contDiff_inf hF _).continuous
    rw [← integral_finset_sum _ (fun i _ => hi i), ← integral_const_mul]
    refine integral_mono_of_nonneg (Eventually.of_forall fun x => sq_nonneg _)
      ((integrable_finset_sum _ (fun i _ => hi i)).const_mul _) (Eventually.of_forall fun x => ?_)
    beta_reduce
    rw [sa12x5_loc_pd_lap hF idx x]
    calc (w x * ∑ i : Fin d, partialDeriv
          (Fin.cons i (Fin.cons i idx : Fin (n + 1) → Fin d) : Fin (n + 2) → Fin d) F x) ^ 2
        = (∑ i : Fin d, w x * partialDeriv
          (Fin.cons i (Fin.cons i idx : Fin (n + 1) → Fin d) : Fin (n + 2) → Fin d) F x) ^ 2 := by
          rw [Finset.mul_sum]
      _ ≤ (Finset.univ : Finset (Fin d)).card * ∑ i : Fin d, (w x * partialDeriv
          (Fin.cons i (Fin.cons i idx : Fin (n + 1) → Fin d) : Fin (n + 2) → Fin d) F x) ^ 2 :=
          sq_sum_le_card_mul_sum_sq
      _ = _ := by simp
  have hbound : ∀ j ∈ Finset.range (m + 1), (Nat.choose m j : ℝ) *
      ∑ idx : Fin j → Fin d, ∫ x, (w x * partialDeriv idx (fun y => Laplacian.laplacian F y) x) ^ 2 ≤
        (d : ℝ) * ((Nat.choose (m + 2) (j + 2) : ℝ) * T (j + 2)) := by
    intro j _
    have h1 : ∑ idx : Fin j → Fin d, ∫ x, (w x * partialDeriv idx (fun y => Laplacian.laplacian F y) x) ^ 2 ≤
        (d : ℝ) * T (j + 2) := by
      calc _ ≤ ∑ idx : Fin j → Fin d, (d : ℝ) * ∑ i : Fin d, ∫ x, (w x * partialDeriv
            (Fin.cons i (Fin.cons i idx : Fin (j + 1) → Fin d) : Fin (j + 2) → Fin d) F x) ^ 2 :=
            Finset.sum_le_sum fun idx _ => pt idx
        _ = (d : ℝ) * ∑ p : (Fin j → Fin d) × Fin d, ∫ x, (w x * partialDeriv
            (Fin.cons p.2 (Fin.cons p.2 p.1 : Fin (j + 1) → Fin d) : Fin (j + 2) → Fin d) F x) ^ 2 := by
            rw [← Finset.mul_sum, Fintype.sum_prod_type]
        _ ≤ (d : ℝ) * T (j + 2) := by
            refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
            have hinj : Function.Injective (fun p : (Fin j → Fin d) × Fin d =>
                (Fin.cons p.2 (Fin.cons p.2 p.1 : Fin (j + 1) → Fin d) : Fin (j + 2) → Fin d)) := by
              intro p p' h
              have h' := (Fin.cons_inj.1 h)
              have h'' := Fin.cons_inj.1 h'.2
              exact Prod.ext h''.2 h'.1
            calc ∑ p : (Fin j → Fin d) × Fin d, ∫ x, (w x * partialDeriv
                  (Fin.cons p.2 (Fin.cons p.2 p.1 : Fin (j + 1) → Fin d) : Fin (j + 2) → Fin d) F x) ^ 2
                = ∑ q ∈ (Finset.univ : Finset ((Fin j → Fin d) × Fin d)).image (fun p =>
                  (Fin.cons p.2 (Fin.cons p.2 p.1 : Fin (j + 1) → Fin d) : Fin (j + 2) → Fin d)),
                    ∫ x, (w x * partialDeriv q F x) ^ 2 := by
                  rw [Finset.sum_image (fun a _ b _ h => hinj h)]
              _ ≤ T (j + 2) := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
                  (fun q _ _ => sa12x5_loc_integral_nonneg w F q)
    have hc : (Nat.choose m j : ℝ) ≤ Nat.choose (m + 2) (j + 2) := by
      exact_mod_cast sa12x5_loc_choose m j
    calc (Nat.choose m j : ℝ) * ∑ idx : Fin j → Fin d, ∫ x, (w x * partialDeriv idx
          (fun y => Laplacian.laplacian F y) x) ^ 2
        ≤ (Nat.choose m j : ℝ) * ((d : ℝ) * T (j + 2)) :=
          mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg _)
      _ = (d : ℝ) * ((Nat.choose m j : ℝ) * T (j + 2)) := by ring
      _ ≤ (d : ℝ) * ((Nat.choose (m + 2) (j + 2) : ℝ) * T (j + 2)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hc (hT0 _)) (Nat.cast_nonneg _)
  have hs : ∑ j ∈ Finset.range (m + 1), ((Nat.choose (m + 2) (j + 2) : ℝ) * T (j + 2)) ≤
      jetSq (m + 2) w F := by
    have hJ : jetSq (m + 2) w F = ∑ k ∈ Finset.range (m + 2 + 1), (Nat.choose (m + 2) k : ℝ) * T k := rfl
    rw [hJ, ← Finset.sum_image (f := fun k => (Nat.choose (m + 2) k : ℝ) * T k) (g := fun j => j + 2)
      (fun a _ b _ h => by simpa using h)]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun k _ _ => mul_nonneg (Nat.cast_nonneg _) (hT0 k))
    intro k hk
    simp only [Finset.mem_image, Finset.mem_range] at hk ⊢
    obtain ⟨a, ha, rfl⟩ := hk
    omega
  calc jetSq m w (fun x => Laplacian.laplacian F x)
      ≤ ∑ j ∈ Finset.range (m + 1), (d : ℝ) * ((Nat.choose (m + 2) (j + 2) : ℝ) * T (j + 2)) :=
        Finset.sum_le_sum hbound
    _ = (d : ℝ) * ∑ j ∈ Finset.range (m + 1), ((Nat.choose (m + 2) (j + 2) : ℝ) * T (j + 2)) := by
        rw [Finset.mul_sum]
    _ ≤ (d : ℝ) * jetSq (m + 2) w F := mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg _)

end HRS.MH.AdjointRd.Phase2SA12X5
