import HRS.MS.S81R_Mk
import HRS.MS.GapRefAux2

/-!
# S81R, packet R4: time reversal of the stationary smooth diffusion on finite sets of times

For a Brownian filtration `(P, ℱ, W)`, `q > 0`, `B ∈ C_b²`, a reference density `ρ` (`GapRef m ρ q B`), and an `ℱ₀`-measurable start `z₀`
with law `ρ dx`: for `a₀, T ≥ 0`, times `tₖ ∈ [0,T]` and test functions `fₖ ∈ s81r_S`,
`E ∏ fₖ(flow_{a₀+tₖ}(z₀)) = E ∏ fₖ(flow_{a₀+T-tₖ}(z₀))`.
Ingredients: `Gap.gap_reversible` (symmetry on bounded `C²` tests), the chain formula `s81r_chain`, the abstract reversal `s81r_foldT_refl`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open HRS HRS.Whole HRS.MS.PoisFlow HRS.MS.PoisSg HRS.MS.Gap

namespace HRS.MS.S81R

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {m : ℕ} {P : Measure Ω} {ℱ : Filtration ℝ mΩ}
  {W : ℝ≥0 → Ω → Fin m → ℝ}

theorem s81r_chainOp [IsProbabilityMeasure P] (hW : IsBrownianFiltration P ℱ W) {q Mb : ℝ}
    (hq : 0 < q) {B : Euc m → Euc m} (hB : HasCbBound 2 Mb B) {ρ : Euc m → ℝ} (hR : GapRef m ρ q B) :
    ChainOp (Whole.withDensityReal ρ) (sg P W q B) s81r_S where
  one := s81r_S_one
  mul := fun f g hf hg => s81r_S_mul hf hg
  mem := fun t f ht hf => s81r_S_sg hW hq hB ht hf
  stat := by
    intro t f ht hf
    obtain ⟨Mf, hMf⟩ := hf
    obtain ⟨M1, hM1⟩ := (s81r_S_one : s81r_S (fun _ : Euc m => (1 : ℝ)))
    have h := (gap_reversible hR hq hB hW hMf hM1 ht).2.2
    have h1 : ∀ x, sg P W q B t (fun _ => (1 : ℝ)) x = 1 := fun x => by simp [sg]
    simp only [mul_one, h1] at h
    exact h
  symm := by
    intro t f g ht hf hg
    obtain ⟨Mf, hMf⟩ := hf
    obtain ⟨Mg, hMg⟩ := hg
    exact (gap_reversible hR hq hB hW hMf hMg ht).2.2

/-- time reversal on a finite set of times -/
theorem s81r_core_rev [IsProbabilityMeasure P] (hW : IsBrownianFiltration P ℱ W) {q Mb : ℝ}
    (hq : 0 < q) {B : Euc m → Euc m} (hB : HasCbBound 2 Mb B) {ρ : Euc m → ℝ} (hR : GapRef m ρ q B)
    {z0 : Ω → Euc m} (hz0 : Measurable[ℱ 0] z0) (hlaw : P.map z0 = Whole.withDensityReal ρ)
    {a0 T : ℝ} (ha0 : 0 ≤ a0) (n : ℕ) (t : Fin n → ℝ) (ht : ∀ i, t i ∈ Set.Icc 0 T)
    (f : Fin n → Euc m → ℝ) (hf : ∀ i, s81r_S (f i)) :
    ∫ ω, ∏ k, f k (flowMap q B (fun u => W u ω) (a0 + t k) (z0 ω)) ∂P =
      ∫ ω, ∏ k, f k (flowMap q B (fun u => W u ω) (a0 + T - t k) (z0 ω)) ∂P := by
  have hC := s81r_chainOp hW hq hB hR
  have hz0m : Measurable z0 := hz0.mono (ℱ.le 0) le_rfl
  set σ := Tuple.sort t with hσ
  have hmono : Monotone (t ∘ σ) := Tuple.monotone_sort t
  set g : Fin n → ℝ × (Euc m → ℝ) := fun i => (a0 + t (σ i), f (σ i)) with hg
  set L1 : List (ℝ × (Euc m → ℝ)) := List.ofFn g with hL1
  have hPw1 : s81r_Pw L1 := by
    unfold s81r_Pw
    rw [hL1, List.map_ofFn, List.pairwise_ofFn]
    intro i j hij
    simp only [Function.comp, hg]
    have := hmono hij.le
    simp only [Function.comp] at this
    linarith
  have hmem1 : ∀ p ∈ L1, ∃ i, g i = p := fun p hp => (List.mem_ofFn).1 hp
  have hnn1 : ∀ p ∈ L1, 0 ≤ p.1 := by
    intro p hp
    obtain ⟨i, rfl⟩ := hmem1 p hp
    have := (ht (σ i)).1
    simp only [hg]
    linarith
  have hA1 : s81r_AllS s81r_S L1 := by
    intro p hp
    obtain ⟨i, rfl⟩ := hmem1 p hp
    exact hf (σ i)
  set c : ℝ := 2 * a0 + T with hc
  set L2 := s81r_refl c L1 with hL2
  have hPw2 : s81r_Pw L2 := s81r_Pw_refl c hPw1
  have hnn2 : ∀ p ∈ L2, 0 ≤ p.1 := by
    intro p hp
    simp only [hL2, s81r_refl, List.mem_reverse, List.mem_map] at hp
    obtain ⟨p0, hp0, rfl⟩ := hp
    obtain ⟨i, rfl⟩ := hmem1 p0 hp0
    have := (ht (σ i)).2
    simp only [hg, hc]
    linarith
  have hA2 : s81r_AllS s81r_S L2 := by
    intro p hp
    simp only [hL2, s81r_refl, List.mem_reverse, List.mem_map] at hp
    obtain ⟨p0, hp0, rfl⟩ := hp
    exact hA1 p0 hp0
  -- left side
  have hleft : ∀ ω, ∏ k, f k (flowMap q B (fun u => W u ω) (a0 + t k) (z0 ω)) =
      (L1.map (fun p => p.2 (flowMap q B (fun u => W u ω) p.1 (z0 ω)))).prod := by
    intro ω
    rw [hL1, List.map_ofFn, List.prod_ofFn]
    exact (Equiv.prod_comp σ (fun k => f k (flowMap q B (fun u => W u ω) (a0 + t k) (z0 ω)))).symm
  have hright : ∀ ω, ∏ k, f k (flowMap q B (fun u => W u ω) (a0 + T - t k) (z0 ω)) =
      (L2.map (fun p => p.2 (flowMap q B (fun u => W u ω) p.1 (z0 ω)))).prod := by
    intro ω
    rw [hL2, s81r_refl, List.map_reverse, List.prod_reverse, List.map_map, hL1, List.map_ofFn,
      List.prod_ofFn]
    rw [← Equiv.prod_comp σ (fun k => f k (flowMap q B (fun u => W u ω) (a0 + T - t k) (z0 ω)))]
    refine Finset.prod_congr rfl fun i _ => ?_
    have e : 2 * a0 + T - (a0 + t (σ i)) = a0 + T - t (σ i) := by ring
    simp only [Function.comp, hg, hc, e]
  simp_rw [hleft, hright]
  rw [s81r_chain hW hq hB L1.length L1 rfl hPw1 hnn1 hA1 hz0,
    s81r_chain hW hq hB L2.length L2 rfl hPw2 hnn2 hA2 hz0]
  have hfm : ∀ L : List (ℝ × (Euc m → ℝ)), s81r_Pw L → (∀ p ∈ L, 0 ≤ p.1) → s81r_AllS s81r_S L →
      ∫ ω, s81r_foldT (sg P W q B) 0 L (z0 ω) ∂P =
        ∫ y, s81r_foldT (sg P W q B) 0 L y ∂(Whole.withDensityReal ρ) := by
    intro L hP hG hA
    have hS := s81r_foldT_mem hC.toClosOp L 0 hP hG hA
    have hcont := s81r_S_cont hS
    rw [← hlaw, integral_map hz0m.aemeasurable hcont.aestronglyMeasurable]
  rw [hfm L1 hPw1 hnn1 hA1, hfm L2 hPw2 hnn2 hA2]
  exact (s81r_foldT_refl hC c L1.length L1 rfl hPw1 hA1 0 0 hnn1 hnn2).symm

end HRS.MS.S81R
