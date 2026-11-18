import HRS.Commutator.Whole.PRODAux8

/-!
# CMX-PROD helper file 9: the product estimate for functions with Bessel derivatives
-/

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators FourierTransform ContDiff Convolution

noncomputable section

namespace HRS.Commutator.Whole.PROD

open HRS HRS.Whole HRS.Commutator.Whole
open HRS.PDE.ToolboxRd

variable {d : ℕ}

/-- The product estimate `‖⟨∇⟩^α ∑ f_i a_i‖₂ ≲ ∑ ‖⟨∇⟩^α f_i‖_P ‖a_i‖_Q + ‖⟨∇⟩^α a_i‖_Q ‖f_i‖_P` for
`f_i ∈ L^P`, `a_i ∈ L^Q` with Bessel derivatives in `L^P`, `L^Q` (`1/P + 1/Q = 1/2`). -/
theorem prod_main_limit (hd : 1 ≤ d) {p q : ℝ} (hp : 1 < p) (hq : 1 < q)
    (hpq : (ENNReal.ofReal p)⁻¹ + (ENNReal.ofReal q)⁻¹ = 2⁻¹) {α : ℝ} (hα : 0 < α) :
    ∃ C : ℝ, 0 < C ∧ ∀ (f a : Fin d → Euc d → ℝ) (W A : Fin d → Euc d → ℂ),
      (∀ i, MemLp (fun x => ((f i x : ℝ) : ℂ)) (ENNReal.ofReal p) volume) →
      (∀ i, MemLp (fun x => ((a i x : ℝ) : ℂ)) (ENNReal.ofReal q) volume) →
      (∀ i, MemLp (W i) (ENNReal.ofReal p) volume) →
      (∀ i, MemLp (A i) (ENNReal.ofReal q) volume) →
      (∀ i, ProdBes α (fun x => ((f i x : ℝ) : ℂ)) (W i)) →
      (∀ i, ProdBes α (fun x => ((a i x : ℝ) : ℂ)) (A i)) →
      MemLp (fun x => ∑ i, f i x * a i x) 2 volume ∧
      sobSqE α (fourierL2 (fun x => ∑ i, f i x * a i x)) ^ ((1 : ℝ) / 2) ≤
        ENNReal.ofReal C * ∑ i, (eLpNorm (W i) (ENNReal.ofReal p) volume *
            eLpNorm (fun x => ((a i x : ℝ) : ℂ)) (ENNReal.ofReal q) volume +
          eLpNorm (A i) (ENNReal.ofReal q) volume *
            eLpNorm (fun x => ((f i x : ℝ) : ℂ)) (ENNReal.ofReal p) volume) := by
  set P : ℝ≥0∞ := ENNReal.ofReal p with hP
  set Q : ℝ≥0∞ := ENNReal.ofReal q with hQ
  have hP1 : 1 < P := ENNReal.one_lt_ofReal.2 hp
  have hQ1 : 1 < Q := ENNReal.one_lt_ofReal.2 hq
  have hP1' : 1 ≤ P := hP1.le
  have hpq' : Q⁻¹ + P⁻¹ = 2⁻¹ := by rw [add_comm]; exact hpq
  obtain ⟨C, hC, hLi⟩ := li_leibniz hd α hα 2 P Q Q P (by norm_num) (by simp) hP1 hQ1 hQ1 hP1
    hpq hpq'
  refine ⟨C, hC, fun f a W A hf ha hW hA hbf hba => ?_⟩
  haveI hT : ENNReal.HolderTriple P Q 2 := ⟨hpq⟩
  -- the real function `g`
  set g : Euc d → ℝ := fun x => ∑ i, f i x * a i x with hg
  have hfr : ∀ i, MemLp (f i) P volume := fun i => by
    have := (hf i).re
    simpa using this
  have har : ∀ i, MemLp (a i) Q volume := fun i => by
    have := (ha i).re
    simpa using this
  have hgL2 : MemLp g 2 volume := by
    have : MemLp (fun x => ∑ i ∈ Finset.univ, f i x * a i x) 2 volume :=
      memLp_finsetSum (Finset.univ) (fun i _ => (hfr i).fun_mul (har i) (r := 2))
    simpa [hg] using this
  refine ⟨hgL2, ?_⟩
  -- approximants
  choose φ hφ1 hφ2 using fun i => prod_approx hp (hf i) (hW i) (hbf i)
  choose χ hχ1 hχ2 using fun i => prod_approx hq (ha i) (hA i) (hba i)
  set fC : Fin d → Euc d → ℂ := fun i x => ((f i x : ℝ) : ℂ) with hfC
  set aC : Fin d → Euc d → ℂ := fun i x => ((a i x : ℝ) : ℂ) with haC
  set N1 : Fin d → ℝ≥0∞ := fun i => eLpNorm (W i) P volume with hN1
  set N2 : Fin d → ℝ≥0∞ := fun i => eLpNorm (aC i) Q volume with hN2
  set N3 : Fin d → ℝ≥0∞ := fun i => eLpNorm (A i) Q volume with hN3
  set N4 : Fin d → ℝ≥0∞ := fun i => eLpNorm (fC i) P volume with hN4
  have hN1t : ∀ i, N1 i ≠ ⊤ := fun i => (hW i).eLpNorm_lt_top.ne
  have hN2t : ∀ i, N2 i ≠ ⊤ := fun i => (ha i).eLpNorm_lt_top.ne
  have hN3t : ∀ i, N3 i ≠ ⊤ := fun i => (hA i).eLpNorm_lt_top.ne
  have hN4t : ∀ i, N4 i ≠ ⊤ := fun i => (hf i).eLpNorm_lt_top.ne
  set δ1 : Fin d → ℕ → ℝ≥0∞ := fun i n => eLpNorm (fun x => besselS α (φ i n) x - W i x) P volume
    with hδ1
  set ε4 : Fin d → ℕ → ℝ≥0∞ := fun i n => eLpNorm (fun x => φ i n x - fC i x) P volume with hε4
  set δ3 : Fin d → ℕ → ℝ≥0∞ := fun i n => eLpNorm (fun x => besselS α (χ i n) x - A i x) Q volume
    with hδ3
  set ε2 : Fin d → ℕ → ℝ≥0∞ := fun i n => eLpNorm (fun x => χ i n x - aC i x) Q volume with hε2
  have hQ1' : 1 ≤ Q := hQ1.le
  -- bounds on the Schwartz norms
  have hJφ : ∀ i n, eLpNorm (besselS α (φ i n)) P volume ≤ N1 i + δ1 i n := fun i n =>
    prod_norm_le_add hP1' _ _
  have hχn : ∀ i n, eLpNorm (⇑(χ i n)) Q volume ≤ N2 i + ε2 i n := fun i n =>
    prod_norm_le_add hQ1' _ _
  have hJχ : ∀ i n, eLpNorm (besselS α (χ i n)) Q volume ≤ N3 i + δ3 i n := fun i n =>
    prod_norm_le_add hQ1' _ _
  have hφn : ∀ i n, eLpNorm (⇑(φ i n)) P volume ≤ N4 i + ε4 i n := fun i n =>
    prod_norm_le_add hP1' _ _
  -- the Schwartz products
  set u : ℕ → SchwartzMap (Euc d) ℂ := fun n => ∑ i, XLI.prodS (φ i n) (χ i n) with hu
  set U : ℕ → ℝ≥0∞ := fun n => ENNReal.ofReal C * ∑ i, ((N1 i + δ1 i n) * (N2 i + ε2 i n) +
    (N3 i + δ3 i n) * (N4 i + ε4 i n)) with hU
  have hbes : ∀ n, besselS α (u n) = fun x => ∑ i, besselS α (XLI.prodS (φ i n) (χ i n)) x := by
    intro n
    funext x
    rw [prod_besselS_eq, hu]
    simp only
    rw [prod_J_sum, prod_schwartz_sum_apply]
    simp [prod_besselS_eq]
  have hle : ∀ n, eLpNorm (besselS α (u n)) 2 volume ≤ U n := by
    intro n
    rw [hbes n]
    have h1 : eLpNorm (fun x => ∑ i, besselS α (XLI.prodS (φ i n) (χ i n)) x) 2 volume ≤
        ∑ i, eLpNorm (besselS α (XLI.prodS (φ i n) (χ i n))) 2 volume := by
      have := eLpNorm_sum_le (μ := volume) (p := 2) (s := Finset.univ)
        (f := fun (i : Fin d) (x : Euc d) => besselS α (XLI.prodS (φ i n) (χ i n)) x)
        (by norm_num)
      have e : (fun x => ∑ i, besselS α (XLI.prodS (φ i n) (χ i n)) x) =
          ∑ i, (fun x => besselS α (XLI.prodS (φ i n) (χ i n)) x) := by
        funext x; simp [Finset.sum_apply]
      rw [e]
      exact this
    refine h1.trans ?_
    rw [hU]
    simp only
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    refine (hLi (φ i n) (χ i n) (XLI.prodS (φ i n) (χ i n)) (fun x => XLI.prodS_apply _ _ x)).trans ?_
    gcongr
    · exact hJφ i n
    · exact hχn i n
    · exact hJχ i n
    · exact hφn i n
  -- convergence of the bounds
  have hUlim : Tendsto U atTop (𝓝 (ENNReal.ofReal C * ∑ i, (N1 i * N2 i + N3 i * N4 i))) := by
    refine ENNReal.Tendsto.const_mul ?_ (Or.inr ENNReal.ofReal_ne_top)
    refine tendsto_finsetSum _ fun i _ => ?_
    have t1 : Tendsto (fun n => N1 i + δ1 i n) atTop (𝓝 (N1 i)) := by
      simpa using (tendsto_const_nhds (x := N1 i)).add (hφ2 i)
    have t2 : Tendsto (fun n => N2 i + ε2 i n) atTop (𝓝 (N2 i)) := by
      simpa using (tendsto_const_nhds (x := N2 i)).add (hχ1 i)
    have t3 : Tendsto (fun n => N3 i + δ3 i n) atTop (𝓝 (N3 i)) := by
      simpa using (tendsto_const_nhds (x := N3 i)).add (hχ2 i)
    have t4 : Tendsto (fun n => N4 i + ε4 i n) atTop (𝓝 (N4 i)) := by
      simpa using (tendsto_const_nhds (x := N4 i)).add (hφ1 i)
    exact (ENNReal.Tendsto.mul t1 (Or.inr (hN2t i)) t2 (Or.inr (hN1t i))).add
      (ENNReal.Tendsto.mul t3 (Or.inr (hN4t i)) t4 (Or.inr (hN3t i)))
  -- `L²` convergence of the products
  have hconv : Tendsto (fun n => eLpNorm (fun x => u n x - ((g x : ℝ) : ℂ)) 2 volume) atTop
      (𝓝 0) := by
    set V : ℕ → ℝ≥0∞ := fun n => ∑ i, (ε4 i n * (N2 i + ε2 i n) + N4 i * ε2 i n) with hV
    have hVlim : Tendsto V atTop (𝓝 0) := by
      have : Tendsto V atTop (𝓝 (∑ i : Fin d, (0 : ℝ≥0∞))) := by
        refine tendsto_finsetSum _ fun i _ => ?_
        have t2 : Tendsto (fun n => N2 i + ε2 i n) atTop (𝓝 (N2 i)) := by
          simpa using (tendsto_const_nhds (x := N2 i)).add (hχ1 i)
        have h1 := ENNReal.Tendsto.mul (hφ1 i) (Or.inr (hN2t i)) t2 (Or.inr ENNReal.zero_ne_top)
        have h2 := ENNReal.Tendsto.mul (tendsto_const_nhds (x := N4 i)) (Or.inr ENNReal.zero_ne_top)
          (hχ1 i) (Or.inr (hN4t i))
        simpa using h1.add h2
      simpa using this
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hVlim
      (fun n => bot_le) (fun n => ?_)
    have e : (fun x => u n x - ((g x : ℝ) : ℂ)) = ∑ i, (fun x => φ i n x * χ i n x - fC i x * aC i x) := by
      funext x
      simp only [hu, hg, hfC, haC, Finset.sum_apply]
      rw [prod_schwartz_sum_apply]
      push_cast
      rw [← Finset.sum_sub_distrib]
      rfl
    rw [e]
    refine (eLpNorm_sum_le (μ := volume) (p := 2) (s := Finset.univ)
      (f := fun (i : Fin d) => fun x => φ i n x * χ i n x - fC i x * aC i x) (by norm_num)).trans ?_
    refine Finset.sum_le_sum fun i _ => ?_
    have h1 := prod_holder_diff (P := P) (Q := Q) (φ' := ⇑(φ i n)) (f' := fC i) (χ' := ⇑(χ i n))
      (a' := aC i) (φ i n).continuous.aestronglyMeasurable (hf i).aestronglyMeasurable
      (χ i n).continuous.aestronglyMeasurable (ha i).aestronglyMeasurable
    refine h1.trans ?_
    gcongr
    exact hχn i n
  exact prod_fatou_sobolev α u hgL2 hconv hUlim hle |>.trans (le_of_eq (by
    rw [Finset.mul_sum]))

end HRS.Commutator.Whole.PROD
