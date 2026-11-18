import HRS.MS.FlowBAux6
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.Calculus.ContDiff.FaaDiBruno

/-!
# MS-FLOW-C, generic tools

* `sup_gronwall`: a Gronwall bound for `η + Lη = ζ` with `L` a Volterra-type operator on `ℝ →ᵇ E`.
* `fc_fdb_split`: Faà di Bruno with the top-order term separated.
-/

open MeasureTheory Filter Topology Set Metric
open scoped BoundedContinuousFunction

namespace HRS.MS.FlowC

open HRS.MS.FlowB

section Gronwall

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem sup_gronwall {S Λ : ℝ} (hS : 0 ≤ S) (hΛ : 0 ≤ Λ) (L : (ℝ →ᵇ E) →L[ℝ] (ℝ →ᵇ E))
    (hL : ∀ γ t, ‖L γ t‖ ≤ ∫ s in (0 : ℝ)..clampT S t, Λ * ‖γ s‖)
    (η ζ : ℝ →ᵇ E) (h : η + L η = ζ) : ‖η‖ ≤ Real.exp (Λ * S) * ‖ζ‖ := by
  set A := ‖ζ‖ with hA
  have hA0 : 0 ≤ A := norm_nonneg _
  have hu : Continuous fun s => Λ * ‖η s‖ := (η.continuous.norm).const_mul Λ
  have hpt : ∀ t, ‖η t‖ ≤ A + ∫ s in (0 : ℝ)..clampT S t, Λ * ‖η s‖ := by
    intro t
    have e : η t = ζ t - L η t := by
      have := congrArg (fun F : ℝ →ᵇ E => F t) h
      simp only [BoundedContinuousFunction.coe_add, Pi.add_apply] at this
      rw [← this]; abel
    calc ‖η t‖ = ‖ζ t - L η t‖ := by rw [← e]
      _ ≤ ‖ζ t‖ + ‖L η t‖ := norm_sub_le _ _
      _ ≤ A + ∫ s in (0 : ℝ)..clampT S t, Λ * ‖η s‖ :=
        add_le_add (ζ.norm_coe_le_norm t) (hL η t)
  set w : ℝ → ℝ := fun t => A + ∫ s in (0 : ℝ)..t, Λ * ‖η s‖ with hw
  have hwd : ∀ t, HasDerivAt w (Λ * ‖η t‖) t := fun t =>
    ((hu.integral_hasStrictDerivAt 0 t).hasDerivAt).const_add A
  have hwnn : ∀ t, 0 ≤ t → 0 ≤ w t := fun t ht => by
    have : 0 ≤ ∫ s in (0 : ℝ)..t, Λ * ‖η s‖ :=
      intervalIntegral.integral_nonneg ht fun s _ => mul_nonneg hΛ (norm_nonneg _)
    simp only [hw]; linarith
  have hwb : ∀ t ∈ Icc (0 : ℝ) S, w t ≤ A * Real.exp (Λ * t) := by
    intro t ht
    have hmain := norm_le_gronwallBound_of_norm_deriv_right_le (f := w)
      (f' := fun t => Λ * ‖η t‖) (δ := A) (K := Λ) (ε := 0) (a := 0) (b := S)
      (fun t _ => (hwd t).continuousAt.continuousWithinAt) (fun t _ => (hwd t).hasDerivWithinAt)
      (by simp [hw, abs_of_nonneg hA0]) (fun t ht => by
        have ht' : t ∈ Icc (0 : ℝ) S := ⟨ht.1, ht.2.le⟩
        have h1 : ‖η t‖ ≤ w t := by
          have := hpt t
          rwa [clampT_of_mem ht'] at this
        rw [Real.norm_of_nonneg (mul_nonneg hΛ (norm_nonneg _)),
          Real.norm_of_nonneg (hwnn t ht.1), add_zero]
        exact mul_le_mul_of_nonneg_left h1 hΛ) t ht
    rw [gronwallBound_ε0, sub_zero, Real.norm_of_nonneg (hwnn t ht.1)] at hmain
    exact hmain
  refine (BoundedContinuousFunction.norm_le (by positivity)).2 fun t => ?_
  have hct := clampT_mem hS t
  calc ‖η t‖ ≤ w (clampT S t) := hpt t
    _ ≤ A * Real.exp (Λ * clampT S t) := hwb _ hct
    _ ≤ A * Real.exp (Λ * S) := by
        gcongr
        exact hct.2
    _ = Real.exp (Λ * S) * ‖ζ‖ := by rw [mul_comm]

end Gronwall

section Faa

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- The ordered finpartition of `Fin n` with a single block. -/
def fc_single (n : ℕ) (hn : 0 < n) : OrderedFinpartition n where
  length := 1
  partSize _ := n
  partSize_pos _ := hn
  emb _ := id
  emb_strictMono _ := strictMono_id
  parts_strictMono := Subsingleton.strictMono _
  disjoint := fun i _ j _ h => absurd (Subsingleton.elim i j) h
  cover x := ⟨0, x, rfl⟩

theorem fc_eq_single {n : ℕ} (hn : 0 < n) (c : OrderedFinpartition n) {i : Fin c.length}
    (hi : c.partSize i = n) : c = fc_single n hn := by
  have hbij : ∀ m, c.partSize m = n → Function.Bijective (c.emb m) := fun m hm =>
    (Fintype.bijective_iff_injective_and_card _).2 ⟨(c.emb_strictMono m).injective, by simp [hm]⟩
  have huniq : ∀ i' : Fin c.length, i' = i := by
    intro i'
    by_contra hne
    have hd := c.disjoint (Set.mem_univ i') (Set.mem_univ i) hne
    obtain ⟨a, ha⟩ := (hbij i hi).2 (c.emb i' ⟨0, c.partSize_pos i'⟩)
    exact (Set.disjoint_left.1 hd) (Set.mem_range_self _) ⟨a, ha⟩
  have hlen : c.length = 1 := by
    have : Subsingleton (Fin c.length) := ⟨fun a b => (huniq a).trans (huniq b).symm⟩
    exact le_antisymm (Fin.subsingleton_iff_le_one.1 this) i.pos
  have hps : ∀ m, c.partSize m = n := fun m => by rw [huniq m]; exact hi
  have hemb : ∀ m (a : Fin (c.partSize m)), ((c.emb m a : Fin n) : ℕ) = (a : ℕ) := by
    intro m a
    have hm := hps m
    have hmono : StrictMono (fun a : Fin n => c.emb m (Fin.cast hm.symm a)) :=
      (c.emb_strictMono m).comp (fun x y hxy => by simpa using hxy)
    have hrange : Set.range (fun a : Fin n => c.emb m (Fin.cast hm.symm a)) =
        Set.range (id : Fin n → Fin n) := by
      ext y
      simp only [Set.mem_range, id_eq]
      constructor
      · intro _; exact ⟨y, rfl⟩
      · intro _
        obtain ⟨a, ha⟩ := (hbij m hm).2 y
        exact ⟨Fin.cast hm a, by simpa using ha⟩
    have := (StrictMono.range_inj_of_wellFoundedLT hmono strictMono_id).1 hrange
    have h2 := congrFun this (Fin.cast hm a)
    simpa using congrArg Fin.val h2
  rcases c with ⟨length, partSize, hpos, emb, hmono, hpm, hdisj, hcover⟩
  subst hlen
  obtain rfl : partSize = fun _ => n := funext hps
  obtain rfl : emb = fun _ => id := funext fun m => funext fun a => Fin.ext (hemb m a)
  rfl

theorem fc_partSize_lt {n : ℕ} (hn : 0 < n) (c : OrderedFinpartition n)
    (hc : c ≠ fc_single n hn) (i : Fin c.length) : c.partSize i < n := by
  by_contra hlt
  exact hc (fc_eq_single hn c (le_antisymm (c.partSize_le i) (not_lt.1 hlt)))

theorem fc_fdb_split {n : ℕ} (hn : 1 ≤ n) (q : FormalMultilinearSeries ℝ F G)
    (p : FormalMultilinearSeries ℝ E F) :
    ∃ R : E [×n]→L[ℝ] G,
      q.taylorComp p n =
        (continuousMultilinearCurryFin1 ℝ F G (q 1)).compContinuousMultilinearMap (p n) + R ∧
      ∀ B K : ℝ, 1 ≤ K → (∀ k, 1 ≤ k → k ≤ n → ‖q k‖ ≤ B) → (∀ k, 1 ≤ k → k < n → ‖p k‖ ≤ K) →
        ‖R‖ ≤ Fintype.card (OrderedFinpartition n) * B * K ^ n := by
  classical
  have hn' : 0 < n := hn
  refine ⟨∑ c ∈ Finset.univ.erase (fc_single n hn'), q.compAlongOrderedFinpartition p c, ?_, ?_⟩
  · unfold FormalMultilinearSeries.taylorComp
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (fc_single n hn'))]
    congr 1
  · intro B K hK hq hp
    have hB : 0 ≤ B := (norm_nonneg _).trans (hq 1 le_rfl hn)
    have hK0 : 0 ≤ K := by linarith
    have hterm : ∀ c ∈ Finset.univ.erase (fc_single n hn'),
        ‖q.compAlongOrderedFinpartition p c‖ ≤ B * K ^ n := by
      intro c hc
      have hcne : c ≠ fc_single n hn' := Finset.ne_of_mem_erase hc
      have hlen1 : 1 ≤ c.length := c.length_pos hn'
      have hlenn : c.length ≤ n := c.length_le
      calc ‖q.compAlongOrderedFinpartition p c‖ ≤ ‖q c.length‖ * ∏ i, ‖p (c.partSize i)‖ :=
            c.norm_compAlongOrderedFinpartition_le _ _
        _ ≤ B * K ^ c.length := by
            refine mul_le_mul (hq _ hlen1 hlenn) ?_ (Finset.prod_nonneg fun _ _ => norm_nonneg _) hB
            calc ∏ i, ‖p (c.partSize i)‖ ≤ ∏ _i : Fin c.length, K :=
                  Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
                    (fun i _ => hp _ (c.partSize_pos i) (fc_partSize_lt hn' c hcne i))
              _ = K ^ c.length := by simp
        _ ≤ B * K ^ n := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hK hlenn) hB
    refine (norm_sum_le _ _).trans ?_
    calc ∑ c ∈ Finset.univ.erase (fc_single n hn'), ‖q.compAlongOrderedFinpartition p c‖
        ≤ ∑ _c ∈ Finset.univ.erase (fc_single n hn'), B * K ^ n := Finset.sum_le_sum hterm
      _ = ((Finset.univ.erase (fc_single n hn')).card : ℝ) * (B * K ^ n) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (Fintype.card (OrderedFinpartition n) : ℝ) * (B * K ^ n) := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          exact_mod_cast (Finset.card_erase_le).trans (by simp)
      _ = Fintype.card (OrderedFinpartition n) * B * K ^ n := by ring

end Faa

end HRS.MS.FlowC
