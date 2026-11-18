import Mathlib
import HRS.Torus.Sobolev
import HRS.Energy.StaticLimitGauss

/-!
# Packet Q41, helper 8: `E_m`-valued random elements from random coefficient sequences
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace HRS.Q41

open HRS

variable {d : ℕ} {m : ℝ}

lemma q41_measurableSet_summable {Ω ι : Type*} [MeasurableSpace Ω] [Countable ι]
    (f : ι → Ω → ℝ) (hf : ∀ i, Measurable (f i)) (hnn : ∀ i ω, 0 ≤ f i ω) :
    MeasurableSet {ω | Summable fun i => f i ω} := by
  have hmeas : Measurable fun ω => ∑' i, ENNReal.ofReal (f i ω) :=
    Measurable.ennreal_tsum fun i => ENNReal.measurable_ofReal.comp (hf i)
  have : {ω | Summable fun i => f i ω} = {ω | ∑' i, ENNReal.ofReal (f i ω) ≠ ⊤} := by
    ext ω
    simp only [Set.mem_setOf_eq]
    have e : ∀ i, ENNReal.ofReal (f i ω) = (((f i ω).toNNReal : ℝ≥0) : ℝ≥0∞) := fun i => rfl
    simp_rw [e]
    rw [ENNReal.tsum_coe_ne_top_iff_summable, ← NNReal.summable_coe]
    simp only [Real.coe_toNNReal _ (hnn _ ω)]
  rw [this]
  exact hmeas (measurableSet_singleton (⊤ : ℝ≥0∞)).compl

/-- The basis vector `x e_k` of `E_m = ℓ²`. -/
def q41_single (m : ℝ) (k : NonzeroLattice d) (x : ℝ) : NegSobolev d m :=
  (lp.single 2 k x : lp (fun _ : NonzeroLattice d => ℝ) 2)

lemma q41_continuous_single (m : ℝ) (k : NonzeroLattice d) : Continuous (q41_single (d := d) m k) :=
  (lp.singleContinuousLinearMap ℝ (fun _ : NonzeroLattice d => ℝ) 2 k).continuous

/-- `ofSeq m` of a random coefficient sequence is a measurable `E_m`-valued map. -/
lemma q41_measurable_ofSeq {Ω : Type*} [MeasurableSpace Ω] (e : ℕ → NonzeroLattice d)
    (he : Function.Surjective e) (c : NonzeroLattice d → Ω → ℝ) (hc : ∀ k, Measurable (c k)) :
    Measurable (fun ω => NegSobolev.ofSeq m (fun k => c k ω)) := by
  classical
  set w : NonzeroLattice d → ℝ := fun k => Lattice.jp k.1 ^ (-m) with hw
  have hSm : MeasurableSet {ω | Summable fun k => (w k * c k ω) ^ 2} :=
    q41_measurableSet_summable (fun k ω => (w k * c k ω) ^ 2)
      (fun k => ((hc k).const_mul (w k)).pow_const 2) (fun k ω => sq_nonneg _)
  have hmem : ∀ ω, Memℓp (fun k => w k * c k ω) 2 ↔ Summable fun k => (w k * c k ω) ^ 2 :=
    fun ω => Torus.memℓp_two_iff _
  set F : ℕ → Finset (NonzeroLattice d) := fun N => (Finset.range N).image e with hF
  have hFmono : Monotone F := fun a b hab => Finset.image_subset_image (Finset.range_mono hab)
  have hFtop : Tendsto F atTop atTop :=
    Filter.tendsto_atTop_finset_of_monotone hFmono fun k => by
      obtain ⟨n, hn⟩ := he k
      exact ⟨n + 1, Finset.mem_image.2 ⟨n, Finset.mem_range.2 (by omega), hn⟩⟩
  set a : ℕ → Ω → NegSobolev d m := fun N ω =>
    if Summable (fun k => (w k * c k ω) ^ 2) then
      ∑ k ∈ F N, q41_single m k (w k * c k ω) else 0 with ha
  refine measurable_of_tendsto_metrizable (f := a) (fun N => ?_) ?_
  · refine Measurable.ite hSm ?_ measurable_const
    refine Finset.measurable_sum _ fun k _ => ?_
    exact (q41_continuous_single m k).measurable.comp ((hc k).const_mul (w k))
  · refine tendsto_pi_nhds.2 fun ω => ?_
    by_cases hS : Summable fun k => (w k * c k ω) ^ 2
    · have hm : Memℓp (fun k => w k * c k ω) 2 := (hmem ω).2 hS
      have h1 : NegSobolev.ofSeq m (fun k => c k ω) =
          (⟨fun k => w k * c k ω, hm⟩ : lp (fun _ : NonzeroLattice d => ℝ) 2) :=
        NegSobolev.ofSeq_of_mem _ hm
      have h2 := lp.hasSum_single (E := fun _ : NonzeroLattice d => ℝ) (p := 2) (by simp)
        (⟨fun k => w k * c k ω, hm⟩ : lp (fun _ : NonzeroLattice d => ℝ) 2)
      have h3 := h2.comp hFtop
      simp only [ha, if_pos hS]
      rw [h1]
      exact h3
    · have hnot : ¬ Memℓp (fun k : NonzeroLattice d => Lattice.jp k.1 ^ (-m) * c k ω) 2 :=
        fun h => hS ((hmem ω).1 (by simpa [hw] using h))
      have : NegSobolev.ofSeq m (fun k => c k ω) = 0 := by
        unfold NegSobolev.ofSeq
        exact dif_neg hnot
      simp only [ha, if_neg hS, this]
      exact tendsto_const_nhds

lemma q41_coord_ofSeq {c : NonzeroLattice d → ℝ}
    (h : Memℓp (fun k : NonzeroLattice d => Lattice.jp k.1 ^ (-m) * c k) 2) (k : NonzeroLattice d) :
    NegSobolev.coord (NegSobolev.ofSeq m c) k = Lattice.jp k.1 ^ (-m) * c k :=
  NegSobolev.coord_ofSeq_of_mem c h k

lemma q41_fourierCoeff_ofSeq {c : NonzeroLattice d → ℝ}
    (h : Memℓp (fun k : NonzeroLattice d => Lattice.jp k.1 ^ (-m) * c k) 2) (k : NonzeroLattice d) :
    NegSobolev.fourierCoeff (NegSobolev.ofSeq m c) k = c k := by
  unfold NegSobolev.fourierCoeff
  rw [q41_coord_ofSeq h k, ← mul_assoc, ← Real.rpow_add (Torus.jp_pos k.1)]
  simp

lemma q41_norm_sq_sub {c c' : NonzeroLattice d → ℝ}
    (h : Memℓp (fun k : NonzeroLattice d => Lattice.jp k.1 ^ (-m) * c k) 2)
    (h' : Memℓp (fun k : NonzeroLattice d => Lattice.jp k.1 ^ (-m) * c' k) 2) :
    ‖NegSobolev.ofSeq m c - NegSobolev.ofSeq m c'‖ ^ 2 =
      ∑' k : NonzeroLattice d, (Lattice.jp k.1 ^ (-m) * (c k - c' k)) ^ 2 := by
  have hs := (NegSobolev.coord_sq (NegSobolev.ofSeq m c - NegSobolev.ofSeq m c')).2
  rw [hs]
  refine tsum_congr fun k => ?_
  have : NegSobolev.coord (NegSobolev.ofSeq m c - NegSobolev.ofSeq m c') k =
      NegSobolev.coord (NegSobolev.ofSeq m c) k - NegSobolev.coord (NegSobolev.ofSeq m c') k := rfl
  rw [this, q41_coord_ofSeq h k, q41_coord_ofSeq h' k]
  ring

end HRS.Q41
