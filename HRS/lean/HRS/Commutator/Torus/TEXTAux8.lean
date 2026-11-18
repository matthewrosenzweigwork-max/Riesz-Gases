import HRS.Commutator.Torus.TEXTAux7

/-!
# T-EXT-A helpers, part 8: transference of the `ℝ^d` Riesz potential to the torus

`∫_𝕋 (∫_𝕋 tdist(x,y)^{σ-d} g(y) dy)^q dx ≲ (∫_𝕋 g^p)^{q/p}` from the `ℝ^d` Hardy–Littlewood–Sobolev
inequality in kernel form (`Whole.cmxHLS_kernel`).
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators FourierTransform

namespace HRS.Commutator.TorusNote

open HRS

variable {d : ℕ}

lemma text_nebot_circle : (𝓝[≠] (0 : UnitAddCircle)).NeBot := by
  have h1 : Tendsto (fun x : ℝ => (x : UnitAddCircle)) (𝓝[≠] 0) (𝓝[≠] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have hc : Continuous (fun x : ℝ => (x : UnitAddCircle)) := AddCircle.continuous_mk' (1 : ℝ)
      have := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds : 𝓝[≠] (0 : ℝ) ≤ 𝓝 0)
      simpa using this
    · have hmem : Set.Ioo (-1 : ℝ) 1 ∈ 𝓝[≠] (0 : ℝ) :=
        mem_nhdsWithin_of_mem_nhds (Ioo_mem_nhds (by norm_num) (by norm_num))
      filter_upwards [hmem, self_mem_nhdsWithin] with x hx hx0
      intro h
      have h' : ((x : ℝ) : UnitAddCircle) = 0 := h
      rw [AddCircle.coe_eq_zero_iff] at h'
      obtain ⟨n, hn⟩ := h'
      have hn' : (n : ℝ) = x := by simpa using hn
      have h2 : (-1 : ℝ) < n ∧ (n : ℝ) < 1 := by rw [hn']; exact hx
      have h3 : n = 0 := by
        have a : (-1 : ℤ) < n := by exact_mod_cast h2.1
        have b : n < 1 := by exact_mod_cast h2.2
        omega
      apply hx0
      rw [← hn', h3]; simp
  exact Filter.NeBot.mono (inferInstance :
    (Filter.map (fun x : ℝ => (x : UnitAddCircle)) (𝓝[≠] (0 : ℝ))).NeBot) h1

lemma text_volume_singleton (hd : 1 ≤ d) (x : Torus d) :
    (volume : Measure (Torus d)) {x} = 0 := by
  haveI : (𝓝[≠] (0 : UnitAddCircle)).NeBot := text_nebot_circle
  haveI : NullSingletonClass (volume : Measure UnitAddCircle) :=
    MeasureTheory.Measure.IsAddHaarMeasure.nullSingletonClass _
  haveI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  exact measure_singleton x

lemma text_ae_ne (hd : 1 ≤ d) (x : Torus d) : ∀ᵐ y ∂(volume : Measure (Torus d)), y ≠ x := by
  rw [ae_iff]
  simpa using text_volume_singleton hd x

lemma text_mk_sub (u v : Euc d) : Torus.mk (u - v) = Torus.mk u - Torus.mk v := by
  funext i
  simp [Torus.mk]

lemma text_centeredRep_mk (z : Euc d) (hz : ∀ i, |z i| < 1) :
    ∃ n : Lattice d, (∀ i, |n i| ≤ 1) ∧
      KernelGrad.centeredRep (Torus.mk z) = z + Lattice.toEuc n := by
  obtain ⟨n₀, hn₀⟩ := Torus.rep_mk z
  have hrep : ∀ i, (Torus.rep (Torus.mk z)) i = z i + n₀ i := fun i => by
    rw [hn₀]; simp [Lattice.toEuc]
  let n : Lattice d := fun i =>
    if (Torus.rep (Torus.mk z)) i ≤ 1 / 2 then n₀ i else n₀ i - 1
  have hc : ∀ i, KernelGrad.centeredRep (Torus.mk z) i = z i + (n i : ℝ) := by
    intro i
    rw [KernelGrad.centeredRep_apply]
    by_cases h : (Torus.rep (Torus.mk z)) i ≤ 1 / 2
    · have hni : n i = n₀ i := if_pos h
      rw [if_pos h, hni, hrep]
    · have hni : n i = n₀ i - 1 := if_neg h
      rw [if_neg h, hni, hrep]
      push_cast; ring
  refine ⟨n, fun i => ?_, ?_⟩
  · have h1 := KernelGrad.abs_centeredRep_le (Torus.mk z) i
    rw [hc i] at h1
    have h2 := abs_lt.1 (hz i)
    have h3 := abs_le.1 h1
    have a : (n i : ℝ) < 2 := by linarith
    have b : (-2 : ℝ) < n i := by linarith
    have a' : n i < 2 := by exact_mod_cast a
    have b' : -2 < n i := by exact_mod_cast b
    rw [abs_le]; constructor <;> omega
  · ext i
    rw [hc i]
    simp [Lattice.toEuc]

lemma text_tdist_le_sum {σ : ℝ} (u v : Euc d) (hu : u ∈ tposCell0 d) (hv : v ∈ tposCell0 d) :
    ENNReal.ofReal (KernelGrad.tdist (Torus.mk u) (Torus.mk v) ^ (σ - d)) ≤
      ∑ n ∈ (Fintype.piFinset fun _ : Fin d => Finset.Icc (-1 : ℤ) 1 : Finset (Lattice d)),
        ENNReal.ofReal (‖u - Lattice.toEuc n - v‖ ^ (σ - d)) := by
  have hz : ∀ i, |(u - v) i| < 1 := by
    intro i
    have h1 := hu i
    have h2 := hv i
    simp only [Set.mem_Ioc] at h1 h2
    show |u i - v i| < 1
    rw [abs_lt]; constructor <;> linarith
  obtain ⟨n, hn, hcn⟩ := text_centeredRep_mk (u - v) hz
  have htd : KernelGrad.tdist (Torus.mk u) (Torus.mk v) = ‖u - v + Lattice.toEuc n‖ := by
    unfold KernelGrad.tdist
    rw [← text_mk_sub, hcn]
  have hneg : -n ∈ (Fintype.piFinset fun _ : Fin d => Finset.Icc (-1 : ℤ) 1 : Finset (Lattice d)) := by
    rw [Fintype.mem_piFinset]
    intro i
    rw [Finset.mem_Icc]
    have := abs_le.1 (hn i)
    simp only [Pi.neg_apply]
    constructor <;> linarith [this.1, this.2]
  have : u - v + Lattice.toEuc n = u - Lattice.toEuc (-n) - v := by
    have : Lattice.toEuc (-n) = - Lattice.toEuc n := by ext i; simp [Lattice.toEuc]
    rw [this]; abel
  rw [htd, this]
  exact Finset.single_le_sum (f := fun n : Lattice d =>
    ENNReal.ofReal (‖u - Lattice.toEuc n - v‖ ^ (σ - d))) (fun _ _ => bot_le) hneg

end HRS.Commutator.TorusNote
