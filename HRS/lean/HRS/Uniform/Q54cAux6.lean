import HRS.Uniform.Q54cAux5

/-!
# Q54c, part 6: covariance of Itô sums

For a continuous Hilbert martingale `G` with deterministic covariation density `C`:
`E[isum_a · isum_b] = ∑_i ∫_{(τ_i,τ_{i+1}] ∩ (0,t_a ∧ t_b]} C_σ(y_a(s^a_i), y_b(s^b_i)) dσ`
(orthogonality of martingale increments on disjoint cells), and the limit of this expression
as the grid is refined (dominated convergence).
-/

noncomputable section

open MeasureTheory Filter Topology Finset ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.Uniform.Q54c

open HRS HRS.Uniform.Q07c

/-! ### grid cells -/

theorem Ioc_min_subset {x x' t : ℝ} (h : x ≤ x') : Set.Ioc (min x t) (min x' t) ⊆ Set.Ioc x x' := by
  intro σ hσ
  have h1 : σ ≤ t := hσ.2.trans (min_le_right _ _)
  refine ⟨?_, hσ.2.trans (min_le_left _ _)⟩
  by_contra hc
  rw [not_lt] at hc
  have : min x t < σ := hσ.1
  have h2 : min x t = x := by
    rcases le_total x t with h3 | h3
    · exact min_eq_left h3
    · exfalso
      rw [min_eq_right h3] at this
      exact absurd h1 (not_le.2 this)
  rw [h2] at this
  exact absurd hc (not_le.2 this)

theorem cell_inter {x x' ta tb : ℝ} :
    Set.Ioc (min x ta) (min x' ta) ∩ Set.Ioc (min x tb) (min x' tb) =
      Set.Ioc x x' ∩ Set.Iic (min ta tb) := by
  ext σ
  simp only [Set.mem_inter_iff, Set.mem_Ioc, Set.mem_Iic, le_min_iff, min_lt_iff]
  constructor
  · rintro ⟨⟨h1, h2, h3⟩, ⟨h5, h7, h8⟩⟩
    refine ⟨⟨?_, h2⟩, h3, h8⟩
    rcases h1 with h1 | h1
    · exact h1
    · exact absurd h3 (not_le.2 h1)
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩
    exact ⟨⟨Or.inl h1, h2, h3⟩, ⟨Or.inl h1, h2, h4⟩⟩

theorem grid_cells_disjoint {T : ℝ} (hT : 0 ≤ T) (N : ℕ) {i j : ℕ} (hij : i ≠ j) :
    Disjoint (Set.Ioc (gridPt T N i) (gridPt T N (i + 1))) (Set.Ioc (gridPt T N j) (gridPt T N (j + 1))) := by
  rw [Set.disjoint_left]
  intro σ h1 h2
  rcases lt_or_gt_of_ne hij with h | h
  · have : gridPt T N (i + 1) ≤ gridPt T N j := gridPt_mono hT N (Nat.succ_le_of_lt h)
    exact absurd (h1.2.trans this) (not_le.2 h2.1)
  · have : gridPt T N (j + 1) ≤ gridPt T N i := gridPt_mono hT N (Nat.succ_le_of_lt h)
    exact absurd (h2.2.trans this) (not_le.2 h1.1)


section ItoCov

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {ℱ : Filtration ℝ mΩ}
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
variable {G : ℝ → Ω → H} {C : ℝ → H →L[ℝ] H →L[ℝ] ℝ} {T : ℝ}

theorem memLp_incr (hG : IsHilbertMartingaleWithCovariation P ℱ T G (fun r _ => C r)) (hT : 0 ≤ T)
    {s s' : ℝ} (hs : s ≤ T) (hs' : s' ≤ T) (u : H) :
    MemLp (fun ω => inner ℝ (G s' ω - G s ω) u) 2 P := by
  have e : (fun ω => inner ℝ (G s' ω - G s ω) u) =
      fun ω => inner ℝ (G s' ω) u - inner ℝ (G s ω) u := by
    funext ω; rw [inner_sub_left]
  rw [e]
  exact (memLp_inner_aux hG hT u hs').sub (memLp_inner_aux hG hT u hs)

/-- the `i`-th increment term of an Itô sum -/
def incrTerm (G : ℝ → Ω → H) (y : ℝ → H) (T t : ℝ) (N i : ℕ) (ω : Ω) : ℝ :=
  inner ℝ (G (min (gridPt T N (i + 1)) t) ω - G (min (gridPt T N i) t) ω) (y (min (gridPt T N i) t))

theorem isum_eq_sum (G : ℝ → Ω → H) (y : ℝ → H) (T t : ℝ) (N : ℕ) (ω : Ω) :
    isum (fun σ => G σ ω) y T t N = ∑ i ∈ Finset.range (N + 1), incrTerm G y T t N i ω := rfl

theorem incrTerm_cov (hG : IsHilbertMartingaleWithCovariation P ℱ T G (fun r _ => C r)) (hT : 0 ≤ T)
    {ta tb : ℝ} (hta : ta ∈ Set.Icc 0 T) (htb : tb ∈ Set.Icc 0 T) (ya yb : ℝ → H) (N : ℕ)
    {i j : ℕ} (hi : i ≤ N) (hj : j ≤ N) :
    ∫ ω, incrTerm G ya T ta N i ω * incrTerm G yb T tb N j ω ∂P =
      ∫ σ in Set.Ioc (min (gridPt T N i) ta) (min (gridPt T N (i + 1)) ta) ∩
        Set.Ioc (min (gridPt T N j) tb) (min (gridPt T N (j + 1)) tb),
          C σ (ya (min (gridPt T N i) ta)) (yb (min (gridPt T N j) tb)) := by
  have hmono := gridPt_mono hT N
  have h1 := inc_cov (P := P) hG (s := min (gridPt T N i) ta) (s' := min (gridPt T N (i + 1)) ta)
    (r := min (gridPt T N j) tb) (r' := min (gridPt T N (j + 1)) tb)
    (le_min (gridPt_nonneg hT N i) hta.1) (min_le_min_right _ (hmono (Nat.le_succ i)))
    ((min_le_left _ _).trans (gridPt_le hT N (Nat.succ_le_succ hi)))
    (le_min (gridPt_nonneg hT N j) htb.1) (min_le_min_right _ (hmono (Nat.le_succ j)))
    ((min_le_left _ _).trans (gridPt_le hT N (Nat.succ_le_succ hj)))
    (ya (min (gridPt T N i) ta)) (yb (min (gridPt T N j) tb))
  exact h1

theorem isum_cov (hG : IsHilbertMartingaleWithCovariation P ℱ T G (fun r _ => C r)) (hT : 0 ≤ T)
    {ta tb : ℝ} (hta : ta ∈ Set.Icc 0 T) (htb : tb ∈ Set.Icc 0 T) (ya yb : ℝ → H) (N : ℕ) :
    ∫ ω, isum (fun σ => G σ ω) ya T ta N * isum (fun σ => G σ ω) yb T tb N ∂P =
      ∑ i ∈ Finset.range (N + 1), ∫ σ in Set.Ioc (gridPt T N i) (gridPt T N (i + 1)) ∩
        Set.Iic (min ta tb), C σ (ya (min (gridPt T N i) ta)) (yb (min (gridPt T N i) tb)) := by
  classical
  have hmono := gridPt_mono hT N
  simp_rw [isum_eq_sum, Finset.sum_mul_sum]
  have hint : ∀ i ∈ Finset.range (N + 1), ∀ j ∈ Finset.range (N + 1),
      Integrable (fun ω => incrTerm G ya T ta N i ω * incrTerm G yb T tb N j ω) P := by
    intro i hi j hj
    have hi' : i ≤ N := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
    have hj' : j ≤ N := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
    exact (memLp_incr hG hT ((min_le_left _ _).trans (gridPt_le hT N (hi'.trans (Nat.le_succ N))))
      ((min_le_left _ _).trans (gridPt_le hT N (Nat.succ_le_succ hi'))) _).integrable_mul
      (memLp_incr hG hT ((min_le_left _ _).trans (gridPt_le hT N (hj'.trans (Nat.le_succ N))))
      ((min_le_left _ _).trans (gridPt_le hT N (Nat.succ_le_succ hj'))) _)
  rw [integral_finset_sum _ (fun i hi => integrable_finset_sum _ (fun j hj => hint i hi j hj))]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' : i ≤ N := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
  rw [integral_finset_sum _ (fun j hj => hint i hi j hj)]
  rw [Finset.sum_eq_single i]
  · rw [incrTerm_cov hG hT hta htb ya yb N hi' hi', cell_inter]
  · intro j hj hji
    have hj' : j ≤ N := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
    rw [incrTerm_cov hG hT hta htb ya yb N hi' hj']
    have hdis : Disjoint (Set.Ioc (min (gridPt T N i) ta) (min (gridPt T N (i + 1)) ta))
        (Set.Ioc (min (gridPt T N j) tb) (min (gridPt T N (j + 1)) tb)) :=
      (grid_cells_disjoint hT N (Ne.symm hji)).mono (Ioc_min_subset (hmono (Nat.le_succ i)))
        (Ioc_min_subset (hmono (Nat.le_succ j)))
    rw [Set.disjoint_iff_inter_eq_empty.1 hdis]
    simp
  · intro hi'; exact absurd hi hi'

end ItoCov


/-! ### the cell index of a point -/

/-- the index of the grid cell `(τ_i, τ_{i+1}]` containing `σ` -/
def cellIdx (T : ℝ) (N : ℕ) (σ : ℝ) : ℕ := ⌈σ * ((N : ℝ) + 1) / T⌉₊ - 1

theorem cellIdx_spec {T : ℝ} (hT : 0 < T) (N : ℕ) {σ : ℝ} (hσ : σ ∈ Set.Ioc 0 T) :
    cellIdx T N σ ≤ N ∧
      σ ∈ Set.Ioc (gridPt T N (cellIdx T N σ)) (gridPt T N (cellIdx T N σ + 1)) := by
  have hN : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  set a : ℝ := σ * ((N : ℝ) + 1) / T with ha
  have ha0 : 0 < a := by have := hσ.1; positivity
  have haN : a ≤ (N : ℝ) + 1 := by
    rw [ha, div_le_iff₀ hT]
    have := mul_le_mul_of_nonneg_right hσ.2 hN.le
    linarith
  set k : ℕ := ⌈a⌉₊ with hk
  have hk0 : 0 < k := Nat.ceil_pos.2 ha0
  have hkN : k ≤ N + 1 := Nat.ceil_le.2 (by exact_mod_cast haN)
  have hk1 : a ≤ k := Nat.le_ceil a
  have hk2 : (k : ℝ) < a + 1 := Nat.ceil_lt_add_one ha0.le
  have hidx : cellIdx T N σ = k - 1 := rfl
  have hk' : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
    rw [Nat.cast_sub hk0]; simp
  refine ⟨by omega, ?_, ?_⟩
  · rw [hidx]
    unfold gridPt
    rw [div_lt_iff₀ hN, hk']
    rw [ha] at hk2
    have : ((k : ℝ) - 1) < σ * ((N : ℝ) + 1) / T := by linarith
    rw [lt_div_iff₀ hT] at this
    linarith
  · rw [hidx]
    unfold gridPt
    rw [le_div_iff₀ hN]
    have hkk : k - 1 + 1 = k := by omega
    rw [hkk]
    rw [ha, div_le_iff₀ hT] at hk1
    linarith

theorem cellIdx_eq {T : ℝ} (hT : 0 < T) (N : ℕ) {i : ℕ} {σ : ℝ}
    (hσ : σ ∈ Set.Ioc (gridPt T N i) (gridPt T N (i + 1))) : cellIdx T N σ = i := by
  have hN : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  unfold gridPt at hσ
  have h1 : (i : ℝ) < σ * ((N : ℝ) + 1) / T := by
    rw [lt_div_iff₀ hT]
    have := hσ.1
    rw [div_lt_iff₀ hN] at this
    linarith
  have h2 : σ * ((N : ℝ) + 1) / T ≤ ((i + 1 : ℕ) : ℝ) := by
    rw [div_le_iff₀ hT]
    have := hσ.2
    rw [le_div_iff₀ hN] at this
    exact this
  have : ⌈σ * ((N : ℝ) + 1) / T⌉₊ = i + 1 := by
    rw [Nat.ceil_eq_iff (by omega)]
    refine ⟨by push_cast; linarith, h2⟩
  unfold cellIdx
  rw [this]; rfl

end HRS.Uniform.Q54c
