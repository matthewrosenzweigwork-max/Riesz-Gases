import HRS.MC.S7E1Aux4

/-!
# Packet `s7_E1_variance_sandwich`

Route.  (1) The finite sections `S_L = (1/2) sum_{i,j<L} H_ij (G_i G_j - C_ij)` satisfy, by the Isserlis identity
`s7_W1_isserlis_proof` and the symmetry `H_ij = H_ji`, the exact formula
`E S_L^2 = (1/2) sum H_ij H_kl C_ik C_jl` (the trace identity `tr(HCHC)`).  (2) The covariance matrices satisfy
`c I <= C_n <= I` (file `S7E1Aux1`), hence by the Kronecker square
`(c^2/2) t_L <= E S_L^2 <= (1/2) t_L`, `t_L = sum_{i,j<L} H_ij^2`.  (3) `t_L -> ||h°||^2` (Parseval, files
`S7E1Aux2`, `S7E1Aux3`).  (4) The bounds pass to the `L^2` limit `Q` (`S7E1Aux4`).
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators RealInnerProductSpace Matrix

noncomputable section

namespace HRS.MC.Sec7.E1

open HRS HRS.Sec7

variable {d : ℕ} {ρ : Torus d → ℝ}

/-! ### Symmetry of the coefficients -/

theorem e1_H_prod (hρ : SmoothPosDensity ρ) {e : ℕ → Torus d → ℝ} (he : IsONBL2Zero (withDensityReal ρ) e)
    {h : Torus d → Torus d → ℝ}
    (hL2 : MemLp (Function.uncurry h) 2 ((withDensityReal ρ).prod (withDensityReal ρ))) (i j : ℕ) :
    E0b.e0bH ρ e h i j = ∫ z : Torus d × Torus d, h z.1 z.2 * (e i z.1 * e j z.2)
      ∂((withDensityReal ρ).prod (withDensityReal ρ)) := by
  have := isProb_withDensityReal hρ.density
  have hW : MemLp (fun z : Torus d × Torus d => e i z.1 * e j z.2) 2
      ((withDensityReal ρ).prod (withDensityReal ρ)) :=
    E0b.e0b_tensor_memLp (he.memLp i) (he.memLp j)
  have hint : Integrable (fun z : Torus d × Torus d => h z.1 z.2 * (e i z.1 * e j z.2))
      ((withDensityReal ρ).prod (withDensityReal ρ)) := hL2.integrable_mul hW
  rw [integral_prod _ hint]
  unfold E0b.e0bH
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp only [mul_assoc]

theorem e1_H_symm (hρ : SmoothPosDensity ρ) {e : ℕ → Torus d → ℝ} (he : IsONBL2Zero (withDensityReal ρ) e)
    {h : Torus d → Torus d → ℝ} (hsymm : ∀ x y, h x y = h y x)
    (hL2 : MemLp (Function.uncurry h) 2 ((withDensityReal ρ).prod (withDensityReal ρ))) (i j : ℕ) :
    E0b.e0bH ρ e h i j = E0b.e0bH ρ e h j i := by
  rw [e1_H_prod hρ he hL2, e1_H_prod hρ he hL2]
  rw [← integral_prod_swap (fun z : Torus d × Torus d => h z.1 z.2 * (e i z.1 * e j z.2))]
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  simp only [Prod.fst_swap, Prod.snd_swap]
  rw [hsymm z.2 z.1]; ring

/-! ### Exact second moments of the finite sections -/

section Var

variable {s β : ℝ} {e : ℕ → Torus d → ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {G : ℕ → Ω → ℝ}

theorem e1_mean_pair (hG : s7_GaussData d s β ρ e P G) (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d)
    (hβ : 0 < β) (hρ : SmoothPosDensity ρ) (he : IsONBL2Zero (withDensityReal ρ) e) (i j : ℕ) :
    ∫ ω, G i ω * G j ω ∂P =
      susceptibilityCov (periodicRiesz d s) (withDensityReal ρ) β (e i) (e j) := by
  obtain ⟨hmeas, hlaw⟩ := hG
  set N := max i j + 1 with hN
  have hS := E0a.s7e_cov_psd hd hs0 hsd hβ hρ he N
  have hV : Measurable (fun ω => (WithLp.toLp 2 fun a : Fin N => G a ω : EuclideanSpace ℝ (Fin N))) :=
    (MeasurableEquiv.toLp 2 (Fin N → ℝ)).measurable.comp (Measurable.of_eval fun a => hmeas a)
  have hi : i < N := by omega
  have hj : j < N := by omega
  have key := W1.w1_second hS ⟨i, hi⟩ ⟨j, hj⟩
  rw [← hlaw N] at key
  unfold law at key
  rw [integral_map hV.aemeasurable (by fun_prop)] at key
  simpa using key

theorem e1_var_block_eq (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (hβ : 0 < β)
    (hρ : SmoothPosDensity ρ) (he : IsONBL2Zero (withDensityReal ρ) e)
    (hG : s7_GaussData d s β ρ e P G) (N : ℕ) (a : Fin N → Fin N → ℝ) :
    ∫ ω, (∑ p : Fin N × Fin N, a p.1 p.2 * (G p.1 ω * G p.2 ω -
        susceptibilityCov (periodicRiesz d s) (withDensityReal ρ) β (e p.1) (e p.2))) ^ 2 ∂P =
      ∑ i, ∑ j, ∑ k, ∑ l, a i j * a k l *
        (susceptibilityCov (periodicRiesz d s) (withDensityReal ρ) β (e i) (e k) *
          susceptibilityCov (periodicRiesz d s) (withDensityReal ρ) β (e j) (e l) +
        susceptibilityCov (periodicRiesz d s) (withDensityReal ρ) β (e i) (e l) *
          susceptibilityCov (periodicRiesz d s) (withDensityReal ρ) β (e j) (e k)) := by
  have hG4 := E0b.e0b_memLp4 (e := e) (ρ := ρ) (s := s) (β := β) hG
  set C : ℕ → ℕ → ℝ := fun x y => susceptibilityCov (periodicRiesz d s) (withDensityReal ρ) β (e x) (e y)
    with hCdef
  show ∫ ω, (∑ p : Fin N × Fin N, a p.1 p.2 * (G p.1 ω * G p.2 ω - C p.1 p.2)) ^ 2 ∂P = _
  have hY : ∀ p : Fin N × Fin N, MemLp (fun ω => G p.1 ω * G p.2 ω - C p.1 p.2) 2 P :=
    fun p => E0b.e0b_X_memLp2 hG4 _ _ _
  have hint : ∀ p q : Fin N × Fin N, Integrable (fun ω => (G p.1 ω * G p.2 ω - C p.1 p.2) *
      (G q.1 ω * G q.2 ω - C q.1 q.2)) P := fun p q => (hY p).integrable_mul (hY q)
  have hw : ∀ p q : Fin N × Fin N, ∫ ω, (G p.1 ω * G p.2 ω - C p.1 p.2) *
      (G q.1 ω * G q.2 ω - C q.1 q.2) ∂P = C p.1 q.1 * C p.2 q.2 + C p.1 q.2 * C p.2 q.1 :=
    fun p q => W1.s7_W1_isserlis_proof d s β ρ e P G hd hs0 hsd hβ hρ he hG p.1 p.2 q.1 q.2
  have hexp : ∀ ω, (∑ p : Fin N × Fin N, a p.1 p.2 * (G p.1 ω * G p.2 ω - C p.1 p.2)) ^ 2 =
      ∑ p : Fin N × Fin N, ∑ q : Fin N × Fin N, (a p.1 p.2 * a q.1 q.2) *
        ((G p.1 ω * G p.2 ω - C p.1 p.2) * (G q.1 ω * G q.2 ω - C q.1 q.2)) := by
    intro ω
    rw [sq, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
    ring
  simp_rw [hexp]
  rw [integral_finsetSum _ (fun p _ => integrable_finsetSum _ fun q _ => (hint p q).const_mul _)]
  have : ∀ p ∈ (Finset.univ : Finset (Fin N × Fin N)),
      ∫ ω, ∑ q : Fin N × Fin N, (a p.1 p.2 * a q.1 q.2) *
        ((G p.1 ω * G p.2 ω - C p.1 p.2) * (G q.1 ω * G q.2 ω - C q.1 q.2)) ∂P =
      ∑ q : Fin N × Fin N, (a p.1 p.2 * a q.1 q.2) * (C p.1 q.1 * C p.2 q.2 + C p.1 q.2 * C p.2 q.1) := by
    intro p _
    rw [integral_finsetSum _ (fun q _ => (hint p q).const_mul _)]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [integral_const_mul, hw]
  rw [Finset.sum_congr rfl this]
  simp only [Fintype.sum_prod_type]
  rfl

theorem e1_sec_bounds (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (hβ : 0 < β)
    (hρ : SmoothPosDensity ρ) (he : IsONBL2Zero (withDensityReal ρ) e)
    (hG : s7_GaussData d s β ρ e P G) {c : ℝ} (hc0 : 0 < c)
    (hup : ∀ n : ℕ, (((1 : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ)) - Matrix.of fun i j : Fin n =>
        susceptibilityCov (periodicRiesz d s) (withDensityReal ρ) β (e i) (e j)).PosSemidef)
    (hlow : ∀ n : ℕ, ((Matrix.of fun i j : Fin n =>
        susceptibilityCov (periodicRiesz d s) (withDensityReal ρ) β (e i) (e j)) -
        c • (1 : Matrix (Fin n) (Fin n) ℝ)).PosSemidef)
    (H : ℕ → ℕ → ℝ) (hH : ∀ i j, H i j = H j i) (L : ℕ) :
    c ^ 2 / 2 * ∑ i ∈ Finset.range L, ∑ j ∈ Finset.range L, H i j ^ 2 ≤
      ∫ ω, ((1 / 2 : ℝ) * ∑ i ∈ Finset.range L, ∑ j ∈ Finset.range L, H i j * (G i ω * G j ω -
        susceptibilityCov (periodicRiesz d s) (withDensityReal ρ) β (e i) (e j))) ^ 2 ∂P ∧
    ∫ ω, ((1 / 2 : ℝ) * ∑ i ∈ Finset.range L, ∑ j ∈ Finset.range L, H i j * (G i ω * G j ω -
        susceptibilityCov (periodicRiesz d s) (withDensityReal ρ) β (e i) (e j))) ^ 2 ∂P ≤
      1 / 2 * ∑ i ∈ Finset.range L, ∑ j ∈ Finset.range L, H i j ^ 2 := by
  set C : ℕ → ℕ → ℝ := fun x y => susceptibilityCov (periodicRiesz d s) (withDensityReal ρ) β (e x) (e y)
    with hCdef
  have hpt : ∀ ω, (1 / 2 : ℝ) * ∑ i ∈ Finset.range L, ∑ j ∈ Finset.range L, H i j * (G i ω * G j ω - C i j) =
      ∑ p : Fin L × Fin L, ((1 / 2 : ℝ) * H p.1 p.2) * (G p.1 ω * G p.2 ω - C p.1 p.2) := by
    intro ω
    simp only [Finset.sum_range, Fintype.sum_prod_type, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have hblock := e1_var_block_eq hd hs0 hsd hβ hρ he hG L (fun i j => (1 / 2 : ℝ) * H i j)
  show _ ≤ ∫ ω, ((1 / 2 : ℝ) * ∑ i ∈ Finset.range L, ∑ j ∈ Finset.range L, H i j * (G i ω * G j ω - C i j)) ^ 2 ∂P ∧
    ∫ ω, ((1 / 2 : ℝ) * ∑ i ∈ Finset.range L, ∑ j ∈ Finset.range L, H i j * (G i ω * G j ω - C i j)) ^ 2 ∂P ≤ _
  simp_rw [hpt]
  rw [hblock]
  set CN : Matrix (Fin L) (Fin L) ℝ := Matrix.of fun i j : Fin L => C i j with hCN
  have hPSD : CN.PosSemidef := E0a.s7e_cov_psd hd hs0 hsd hβ hρ he L
  have e1 := E0b.e0b_kron_le hPSD zero_le_one (hup L) (fun i j : Fin L => H i j)
  have e2 := E1Aux1.e1a_kron_ge hPSD hc0.le (hlow L) (fun i j : Fin L => H i j)
  simp only [hCN, Matrix.of_apply, one_pow, one_mul] at e1 e2
  have hsq : ∑ i ∈ Finset.range L, ∑ j ∈ Finset.range L, H i j ^ 2 =
      ∑ i : Fin L, ∑ j : Fin L, H i j ^ 2 := by
    simp only [Finset.sum_range]
  -- the two pairings coincide
  have hB : ∑ i : Fin L, ∑ j : Fin L, ∑ k : Fin L, ∑ l : Fin L, H i j * H k l * (C i l * C j k) =
      ∑ i : Fin L, ∑ j : Fin L, ∑ k : Fin L, ∑ l : Fin L, H i j * H k l * (C i k * C j l) := by
    rw [E0b.e0b_sum_swap_kl]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
      Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    rw [hH (l : ℕ) (k : ℕ)]
  have hexp : ∑ i : Fin L, ∑ j : Fin L, ∑ k : Fin L, ∑ l : Fin L, (1 / 2 : ℝ) * H i j * ((1 / 2 : ℝ) * H k l) *
      (C i k * C j l + C i l * C j k) =
      (1 / 2 : ℝ) * ∑ i : Fin L, ∑ j : Fin L, ∑ k : Fin L, ∑ l : Fin L, H i j * H k l * (C i k * C j l) := by
    have : ∀ i j k l : Fin L, (1 / 2 : ℝ) * H i j * ((1 / 2 : ℝ) * H k l) * (C i k * C j l + C i l * C j k) =
        (1 / 4 : ℝ) * (H i j * H k l * (C i k * C j l)) + (1 / 4 : ℝ) * (H i j * H k l * (C i l * C j k)) := by
      intros; ring
    simp only [this, Finset.sum_add_distrib, ← Finset.mul_sum, hB]
    ring
  rw [hexp, hsq]
  constructor <;> nlinarith [e1, e2]

end Var

/-! ### The packet -/

theorem s7_E1_variance_sandwich_proof (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {β : ℝ} (hβ : 0 < β)
    (ρ : Torus d → ℝ) (hρ : SmoothPosDensity ρ) :
    ∃ c : ℝ, 0 < c ∧ c ≤ 1 ∧ ∀ (e : ℕ → Torus d → ℝ), IsONBL2Zero (withDensityReal ρ) e →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (G : ℕ → Ω → ℝ),
      s7_GaussData d s β ρ e P G →
      ∀ (h : Torus d → Torus d → ℝ), Measurable (Function.uncurry h) → (∀ x y, h x y = h y x) →
      MemLp (Function.uncurry h) 2 ((withDensityReal ρ).prod (withDensityReal ρ)) →
      ∀ Q : Ω → ℝ, AEMeasurable Q P → s7_IsChaosLimit d s β ρ e P G h Q →
        MemLp Q 2 P ∧ ∫ ω, Q ω ∂P = 0 ∧
          c ^ 2 / 2 * s7_hcNorm2 d ρ h ≤ ∫ ω, Q ω ^ 2 ∂P ∧
          ∫ ω, Q ω ^ 2 ∂P ≤ 1 / 2 * s7_hcNorm2 d ρ h := by
  obtain ⟨c, hc0, hc1, hall⟩ := E1Aux1.e1a_cov_bounds hd hs0 hsd hβ hρ
  refine ⟨c, hc0, hc1, fun e he Ω _ P _ G hG h hm hsymm hL2 Q hQ hchaos => ?_⟩
  have hprob := isProb_withDensityReal hρ.density
  have hG4 := E0b.e0b_memLp4 (e := e) (ρ := ρ) (s := s) (β := β) hG
  set H : ℕ → ℕ → ℝ := E0b.e0bH ρ e h with hHdef
  have hHs : ∀ i j, H i j = H j i := e1_H_symm hρ he hsymm hL2
  set S : ℕ → Ω → ℝ := fun L ω => (1 / 2 : ℝ) * ∑ i ∈ Finset.range L, ∑ j ∈ Finset.range L,
    H i j * (G i ω * G j ω -
      susceptibilityCov (periodicRiesz d s) (withDensityReal ρ) β (e i) (e j)) with hSdef
  have hS : ∀ L, MemLp (S L) 2 P := by
    intro L
    refine MemLp.const_mul ?_ _
    refine memLp_finsetSum _ fun i _ => memLp_finsetSum _ fun j _ => ?_
    exact (E0b.e0b_X_memLp2 hG4 _ i j).const_mul _
  have hS0 : ∀ L, ∫ ω, S L ω ∂P = 0 := by
    intro L
    have hX : ∀ i j : ℕ, Integrable (fun ω => H i j * (G i ω * G j ω -
        susceptibilityCov (periodicRiesz d s) (withDensityReal ρ) β (e i) (e j))) P := fun i j =>
      ((E0b.e0b_X_memLp2 hG4 _ i j).integrable one_le_two).const_mul _
    simp only [hSdef]
    rw [integral_const_mul, integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hX i j]
    have : ∀ i ∈ Finset.range L, ∫ ω, ∑ j ∈ Finset.range L, H i j * (G i ω * G j ω -
        susceptibilityCov (periodicRiesz d s) (withDensityReal ρ) β (e i) (e j)) ∂P = 0 := by
      intro i _
      rw [integral_finsetSum _ fun j _ => hX i j]
      refine Finset.sum_eq_zero fun j _ => ?_
      rw [integral_const_mul]
      have hm0 : ∫ ω, (G i ω * G j ω -
          susceptibilityCov (periodicRiesz d s) (withDensityReal ρ) β (e i) (e j)) ∂P = 0 := by
        have hGG : Integrable (fun ω => G i ω * G j ω) P :=
          ((hG4 i).mul (hG4 j) (r := 2)).integrable one_le_two
        rw [integral_sub hGG (integrable_const _), e1_mean_pair hG hd hs0 hsd hβ hρ he i j]
        simp
      rw [hm0, mul_zero]
    rw [Finset.sum_eq_zero this, mul_zero]
  -- the limit of the partial sums of squares
  have hsum := E0b.e0b_bessel hρ he hL2
  have hpars := E1Aux3.e1c_parseval (μ := withDensityReal ρ) he hm hL2
  set T : ℝ := ∫ z : Torus d × Torus d, canonicalCenter (withDensityReal ρ) h z.1 z.2 ^ 2
    ∂((withDensityReal ρ).prod (withDensityReal ρ)) with hT
  have ht : Tendsto (fun L : ℕ => ∑ i ∈ Finset.range L, ∑ j ∈ Finset.range L, H i j ^ 2)
      atTop (𝓝 T) := by
    have h1 : Tendsto (fun N : ℕ => Finset.range N ×ˢ Finset.range N) atTop atTop := by
      refine Filter.tendsto_atTop_finset_of_monotone (fun a b hab => ?_) (fun p => ?_)
      · exact Finset.product_subset_product (Finset.range_mono hab) (Finset.range_mono hab)
      · exact ⟨max p.1 p.2 + 1, by
          simp only [Finset.mem_product, Finset.mem_range]; omega⟩
    have h2 := hpars.comp h1
    refine Tendsto.congr (fun N => ?_) h2
    simp only [Function.comp_apply]
    exact Finset.sum_product' (s := Finset.range N) (t := Finset.range N) (f := fun i j => H i j ^ 2)
  have hQ2 := E1Aux4.e1d_limit S hS hS0 Q hQ hchaos
    (fun L => c ^ 2 / 2 * ∑ i ∈ Finset.range L, ∑ j ∈ Finset.range L, H i j ^ 2)
    (fun L => 1 / 2 * ∑ i ∈ Finset.range L, ∑ j ∈ Finset.range L, H i j ^ 2)
    (ht.const_mul _) (ht.const_mul _) (fun L => by
      obtain ⟨hup, hlow⟩ := hall he L
      exact e1_sec_bounds hd hs0 hsd hβ hρ he hG hc0 (fun n => (hall he n).1)
        (fun n => (hall he n).2) H hHs L)
  exact hQ2

end HRS.MC.Sec7.E1

end
