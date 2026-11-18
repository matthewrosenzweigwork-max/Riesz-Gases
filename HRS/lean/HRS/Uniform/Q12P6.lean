import HRS.Uniform.Q12P5

/-!
# Q12, Peyre part 6: `L²` displacement of the Euler scheme
-/

noncomputable section

open HRS MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

namespace HRS.Uniform.Q12

variable {d : ℕ}

/-- Cauchy-Schwarz for nonneg continuous functions on a finite measure space. -/
lemma q12_cs {μ : Measure (Torus d)} [IsFiniteMeasure μ] {p q : Torus d → ℝ} (hp : Continuous p)
    (hq : Continuous q) :
    (∫ x, p x * q x ∂μ) ^ 2 ≤ (∫ x, p x ^ 2 ∂μ) * (∫ x, q x ^ 2 ∂μ) := by
  have hi : ∀ (f : Torus d → ℝ), Continuous f → Integrable f μ := fun f hf =>
    hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have h1 : Integrable (fun x => p x ^ 2) μ := hi _ (hp.pow 2)
  have h2 : Integrable (fun x => q x ^ 2) μ := hi _ (hq.pow 2)
  have h3 : Integrable (fun x => p x * q x) μ := hi _ (hp.mul hq)
  set A := ∫ x, p x ^ 2 ∂μ
  set Bq := ∫ x, q x ^ 2 ∂μ
  set C := ∫ x, p x * q x ∂μ
  have hq0 : ∀ l : ℝ, 0 ≤ A * l ^ 2 + (-2 * C) * l + Bq := by
    intro l
    have : ∫ x, (l * p x - q x) ^ 2 ∂μ = l ^ 2 * A - 2 * l * C + Bq := by
      have e : ∀ x, (l * p x - q x) ^ 2 = l ^ 2 * p x ^ 2 - 2 * l * (p x * q x) + q x ^ 2 := fun x => by ring
      simp_rw [e]
      have ia : Integrable (fun x => l ^ 2 * p x ^ 2) μ := h1.const_mul _
      have ib : Integrable (fun x => 2 * l * (p x * q x)) μ := h3.const_mul _
      have ic : Integrable (fun x => l ^ 2 * p x ^ 2 - 2 * l * (p x * q x)) μ := ia.sub ib
      rw [integral_add ic h2, integral_sub ia ib, integral_const_mul, integral_const_mul]
    have h0 : 0 ≤ ∫ x, (l * p x - q x) ^ 2 ∂μ := integral_nonneg fun x => sq_nonneg _
    rw [this] at h0
    nlinarith
  have := discrim_le_zero (a := A) (b := -2 * C) (c := Bq) (fun l => by have := hq0 l; nlinarith)
  unfold discrim at this
  nlinarith


lemma q12_integrable_cont {μ : Measure (Torus d)} [IsFiniteMeasure μ] {f : Torus d → ℝ}
    (hf : Continuous f) : Integrable f μ :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

/-- Minkowski in `L²(μ)` for continuous vector-valued functions. -/
lemma q12_l2_add_le {μ : Measure (Torus d)} [IsFiniteMeasure μ] {f g : Torus d → Euc d}
    (hf : Continuous f) (hg : Continuous g) :
    Real.sqrt (∫ x, ‖f x + g x‖ ^ 2 ∂μ) ≤
      Real.sqrt (∫ x, ‖f x‖ ^ 2 ∂μ) + Real.sqrt (∫ x, ‖g x‖ ^ 2 ∂μ) := by
  have hpf : Continuous fun x => ‖f x‖ := hf.norm
  have hpg : Continuous fun x => ‖g x‖ := hg.norm
  have hcs := q12_cs (μ := μ) hpf hpg
  set A := ∫ x, ‖f x‖ ^ 2 ∂μ
  set Bq := ∫ x, ‖g x‖ ^ 2 ∂μ
  set C := ∫ x, ‖f x‖ * ‖g x‖ ∂μ
  have hA : 0 ≤ A := integral_nonneg fun x => sq_nonneg _
  have hB : 0 ≤ Bq := integral_nonneg fun x => sq_nonneg _
  have hC : 0 ≤ C := integral_nonneg fun x => mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have hC' : C ≤ Real.sqrt A * Real.sqrt Bq := by
    rw [← Real.sqrt_mul hA]
    exact Real.le_sqrt_of_sq_le hcs
  have h1 : ∫ x, ‖f x + g x‖ ^ 2 ∂μ ≤ ∫ x, (‖f x‖ ^ 2 + 2 * (‖f x‖ * ‖g x‖) + ‖g x‖ ^ 2) ∂μ := by
    refine integral_mono (q12_integrable_cont ((hf.add hg).norm.pow 2)) ?_ fun x => ?_
    · exact ((q12_integrable_cont (hpf.pow 2)).add ((q12_integrable_cont (hpf.mul hpg)).const_mul 2)).add
        (q12_integrable_cont (hpg.pow 2))
    · have := norm_add_le (f x) (g x)
      nlinarith [norm_nonneg (f x + g x), norm_nonneg (f x), norm_nonneg (g x)]
  have h2 : ∫ x, (‖f x‖ ^ 2 + 2 * (‖f x‖ * ‖g x‖) + ‖g x‖ ^ 2) ∂μ = A + 2 * C + Bq := by
    have ia : Integrable (fun x => ‖f x‖ ^ 2) μ := q12_integrable_cont (hpf.pow 2)
    have ib : Integrable (fun x => 2 * (‖f x‖ * ‖g x‖)) μ :=
      (q12_integrable_cont (hpf.mul hpg)).const_mul 2
    have ic : Integrable (fun x => ‖g x‖ ^ 2) μ := q12_integrable_cont (hpg.pow 2)
    have iab : Integrable (fun x => ‖f x‖ ^ 2 + 2 * (‖f x‖ * ‖g x‖)) μ := ia.add ib
    rw [integral_add iab ic, integral_add ia ib, integral_const_mul]
  rw [h2] at h1
  rw [Real.sqrt_le_left (by positivity)]
  have hsA := Real.sq_sqrt hA
  have hsB := Real.sq_sqrt hB
  nlinarith [Real.sqrt_nonneg A, Real.sqrt_nonneg Bq]


lemma q12_cont_descend {G : Euc d → Euc d} (hp : Torus.Per G) (hc : Continuous G) :
    Continuous fun x : Torus d => G (Torus.rep x) :=
  Torus.continuous_descend hp hc

/-- The `L²(μ 0)` displacement of the Euler scheme. -/
theorem q12_scheme_cost {w : ℝ → Euc d → Euc d} {μ : ℝ → Measure (Torus d)} {V V₁ V₂ δ Θ₂ a : ℝ}
    (hwc : ∀ t, ContDiff ℝ 2 (w t)) (hwp : ∀ t, Torus.Per (w t))
    (hV : ∀ t ∈ Icc (0 : ℝ) 1, ∀ y, ‖w t y‖ ≤ V)
    (hV₁ : ∀ t ∈ Icc (0 : ℝ) 1, ∀ y, ‖fderiv ℝ (w t) y‖ ≤ V₁)
    (hV₂ : ∀ t ∈ Icc (0 : ℝ) 1, ∀ y, ‖fderiv ℝ (fderiv ℝ (w t)) y‖ ≤ V₂)
    (hprob : ∀ t ∈ Icc (0 : ℝ) 1, IsProbabilityMeasure (μ t)) (hδ : 0 ≤ δ)
    (hCE : ∀ t τ : ℝ, t ∈ Icc (0 : ℝ) 1 → 0 < τ → τ ≤ 1 → t + τ ≤ 1 → ∀ (Φ : Euc d → ℝ) (B : ℝ),
      Torus.Per Φ → C2b B Φ →
      |τ * ∫ x, fderiv ℝ Φ (Torus.rep x) (w t (Torus.rep x)) ∂(μ t) + (Iw (μ t) Φ - Iw (μ (t + τ)) Φ)|
        ≤ δ * τ ^ 2 * B)
    (hΘ : ∀ t ∈ Icc (0 : ℝ) 1, C2b Θ₂ (fun y => ‖w t y‖ ^ 2))
    (hkin : ∀ t ∈ Icc (0 : ℝ) 1, ∫ x, ‖w t (Torus.rep x)‖ ^ 2 ∂(μ t) ≤ a)
    {n : ℕ} (hn : 0 < n) :
    ∫ x, ‖schemeMap w (1 / n) n (Torus.rep x) - Torus.rep x‖ ^ 2 ∂(μ 0) ≤
      a + Θ₂ * ((δ + V ^ 2) * (1 / (n : ℝ)) * Real.exp (2 * V₁ + V₁ ^ 2 + V₂)) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  set τ : ℝ := 1 / (n : ℝ) with hτ
  have hτ0 : 0 < τ := by positivity
  have h0mem : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  haveI := hprob 0 h0mem
  have hV0 : 0 ≤ V := le_trans (norm_nonneg _) (hV 0 h0mem 0)
  have hV₁0 : 0 ≤ V₁ := le_trans (norm_nonneg (fderiv ℝ (w 0) 0)) (hV₁ 0 h0mem 0)
  have hV₂0 : 0 ≤ V₂ := le_trans (norm_nonneg (fderiv ℝ (fderiv ℝ (w 0)) 0)) (hV₂ 0 h0mem 0)
  have hΘ0 : 0 ≤ Θ₂ := le_trans (abs_nonneg _) ((hΘ 0 h0mem).2 0).1
  have ha0 : 0 ≤ a := le_trans (integral_nonneg fun x => sq_nonneg _) (hkin 0 h0mem)
  set C₂ : ℝ := 2 * V₁ + V₁ ^ 2 + V₂ with hC₂
  have hC₂0 : 0 ≤ C₂ := by positivity
  set ε : ℝ := (δ + V ^ 2) * τ * Real.exp C₂ with hε
  have hε0 : 0 ≤ ε := by positivity
  have hweak := q12_scheme_weak hwc hwp hV hV₁ hV₂ hprob hδ hCE hn
  -- bound of the weak error
  have hbε : ∀ i : ℕ, i ≤ n → (δ + V ^ 2) * τ ^ 2 * i * (1 + C₂ * τ) ^ i ≤ ε := by
    intro i hi
    have hiτ : (i : ℝ) * τ ≤ 1 := by
      have : (i : ℝ) ≤ n := by exact_mod_cast hi
      calc (i : ℝ) * τ ≤ n * τ := mul_le_mul_of_nonneg_right this hτ0.le
        _ = 1 := by rw [hτ]; field_simp
    have hq : (1 + C₂ * τ) ^ i ≤ Real.exp C₂ := by
      calc (1 + C₂ * τ) ^ i ≤ (Real.exp (C₂ * τ)) ^ i :=
            pow_le_pow_left₀ (by positivity) (by linarith [Real.add_one_le_exp (C₂ * τ)]) i
        _ = Real.exp (C₂ * τ * i) := by rw [← Real.exp_nat_mul]; congr 1; ring
        _ ≤ Real.exp C₂ := by
            apply Real.exp_le_exp.2
            nlinarith
    have hK : 0 ≤ (δ + V ^ 2) := by positivity
    calc (δ + V ^ 2) * τ ^ 2 * i * (1 + C₂ * τ) ^ i = ((δ + V ^ 2) * τ) * ((i * τ) * (1 + C₂ * τ) ^ i) := by
          ring
      _ ≤ ((δ + V ^ 2) * τ) * (1 * Real.exp C₂) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact mul_le_mul hiτ hq (by positivity) zero_le_one
      _ = ε := by rw [hε]; ring
  have hM0 : 0 ≤ a + Θ₂ * ε := by positivity
  set M : ℝ := Real.sqrt (a + Θ₂ * ε) with hM
  have hSe := q12_schemeMap_perEquiv hwp τ
  have hSc := q12_schemeMap_continuous (fun t => (hwc t).continuous) τ
  have hFper : ∀ i, Torus.Per (fun y => schemeMap w τ i y - y) := fun i y n => by
    show schemeMap w τ i (y + Lattice.toEuc n) - (y + Lattice.toEuc n) = schemeMap w τ i y - y
    rw [hSe i y n]; abel
  have hFc : ∀ i, Continuous (fun x : Torus d => schemeMap w τ i (Torus.rep x) - Torus.rep x) :=
    fun i => Torus.continuous_descend (hFper i) ((hSc i).sub continuous_id)
  have hGper : ∀ i : ℕ, Torus.Per (fun y => w ((i : ℝ) * τ) (schemeMap w τ i y)) := fun i y n => by
    show w ((i : ℝ) * τ) (schemeMap w τ i (y + Lattice.toEuc n)) = w ((i : ℝ) * τ) (schemeMap w τ i y)
    rw [hSe i y n]; exact hwp _ _ n
  have hGc : ∀ i : ℕ, Continuous (fun x : Torus d => w ((i : ℝ) * τ) (schemeMap w τ i (Torus.rep x))) :=
    fun i => Torus.continuous_descend (hGper i) ((hwc _).continuous.comp (hSc i))
  have hti : ∀ i : ℕ, i ≤ n → (i : ℝ) * τ ∈ Icc (0 : ℝ) 1 := by
    intro i hi
    refine ⟨by positivity, ?_⟩
    have : (i : ℝ) ≤ n := by exact_mod_cast hi
    calc (i : ℝ) * τ ≤ n * τ := mul_le_mul_of_nonneg_right this hτ0.le
      _ = 1 := by rw [hτ]; field_simp
  -- kinetic bound along the scheme
  have hm : ∀ i : ℕ, i ≤ n → ∫ x, ‖w ((i : ℝ) * τ) (schemeMap w τ i (Torus.rep x))‖ ^ 2 ∂(μ 0) ≤
      a + Θ₂ * ε := by
    intro i hi
    set t : ℝ := (i : ℝ) * τ with ht
    have htm := hti i hi
    set Φ : Euc d → ℝ := fun y => ‖w t y‖ ^ 2 with hΦ
    have hΦp : Torus.Per Φ := fun y n => by
      show ‖w t (y + Lattice.toEuc n)‖ ^ 2 = ‖w t y‖ ^ 2
      rw [hwp t y n]
    have hΦc : Continuous Φ := ((hwc t).continuous.norm).pow 2
    have h1 := q12_Iw_map (hSe i) (hSc i) (μ 0) hΦp hΦc
    have h2 := hweak i hi Φ Θ₂ hΦp (hΘ t htm)
    have h3 : |Iw ((μ 0).map (torusMap (schemeMap w τ i))) Φ - Iw (μ t) Φ| ≤ Θ₂ * ε := by
      refine h2.trans ?_
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_left (hbε i hi) hΘ0
    have h4 : Iw (μ t) Φ ≤ a := hkin t htm
    have h5 : Iw ((μ 0).map (torusMap (schemeMap w τ i))) Φ ≤ a + Θ₂ * ε := by
      have := (abs_le.1 h3).2
      linarith
    rw [h1] at h5
    exact h5
  -- the `L²` recursion
  have hrec : ∀ i : ℕ, i ≤ n →
      Real.sqrt (∫ x, ‖schemeMap w τ i (Torus.rep x) - Torus.rep x‖ ^ 2 ∂(μ 0)) ≤ i * τ * M := by
    intro i
    induction i with
    | zero =>
      intro _
      simp [schemeMap]
    | succ i ih =>
      intro hi
      have hi' : i ≤ n := by omega
      have hpt : ∀ x : Torus d, schemeMap w τ (i + 1) (Torus.rep x) - Torus.rep x =
          (schemeMap w τ i (Torus.rep x) - Torus.rep x) +
            τ • w ((i : ℝ) * τ) (schemeMap w τ i (Torus.rep x)) := fun x => by
        show schemeMap w τ i (Torus.rep x) + τ • w ((i : ℝ) * τ) (schemeMap w τ i (Torus.rep x)) - Torus.rep x = _
        abel
      simp_rw [hpt]
      have htri := q12_l2_add_le (μ := μ 0) (hFc i) ((hGc i).const_smul τ)
      have hsm : Real.sqrt (∫ x, ‖τ • w ((i : ℝ) * τ) (schemeMap w τ i (Torus.rep x))‖ ^ 2 ∂(μ 0)) ≤
          τ * M := by
        have e : ∀ x : Torus d, ‖τ • w ((i : ℝ) * τ) (schemeMap w τ i (Torus.rep x))‖ ^ 2 =
            τ ^ 2 * ‖w ((i : ℝ) * τ) (schemeMap w τ i (Torus.rep x))‖ ^ 2 := fun x => by
          rw [norm_smul, Real.norm_of_nonneg hτ0.le, mul_pow]
        simp_rw [e]
        rw [integral_const_mul, Real.sqrt_mul (sq_nonneg τ), Real.sqrt_sq hτ0.le]
        exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (hm i hi')) hτ0.le
      have := ih hi'
      calc _ ≤ _ := htri
        _ ≤ i * τ * M + τ * M := add_le_add this hsm
        _ = ((i + 1 : ℕ) : ℝ) * τ * M := by push_cast; ring
  have hfin := hrec n le_rfl
  have hnτ : (n : ℝ) * τ = 1 := by rw [hτ]; field_simp
  rw [hnτ, one_mul] at hfin
  have hX : 0 ≤ ∫ x, ‖schemeMap w τ n (Torus.rep x) - Torus.rep x‖ ^ 2 ∂(μ 0) :=
    integral_nonneg fun x => sq_nonneg _
  have := (Real.sqrt_le_iff.1 hfin).2
  rw [hM, Real.sq_sqrt hM0] at this
  exact this

end HRS.Uniform.Q12
