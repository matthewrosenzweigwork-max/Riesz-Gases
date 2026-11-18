import HRS.Uniform.Q12P4

/-!
# Q12, Peyre part 5: the Euler scheme and its weak-norm error
-/

noncomputable section

open HRS MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

namespace HRS.Uniform.Q12

variable {d : ℕ}

/-- The `i`-th Euler map: `S_{i+1} = (id + τ w_{iτ}) ∘ S_i`. -/
def schemeMap (w : ℝ → Euc d → Euc d) (τ : ℝ) : ℕ → Euc d → Euc d
  | 0 => fun y => y
  | (i + 1) => fun y => schemeMap w τ i y + τ • w ((i : ℝ) * τ) (schemeMap w τ i y)

lemma q12_schemeMap_perEquiv {w : ℝ → Euc d → Euc d} (hwp : ∀ t, Torus.Per (w t)) (τ : ℝ) :
    ∀ i, PerEquiv (schemeMap w τ i) := by
  intro i
  induction i with
  | zero => intro y n; rfl
  | succ i ih =>
    intro y n
    show schemeMap w τ i (y + Lattice.toEuc n) + τ • w ((i : ℝ) * τ) (schemeMap w τ i (y + Lattice.toEuc n)) =
      schemeMap w τ i y + τ • w ((i : ℝ) * τ) (schemeMap w τ i y) + Lattice.toEuc n
    rw [ih, hwp]; abel

lemma q12_schemeMap_continuous {w : ℝ → Euc d → Euc d} (hwc : ∀ t, Continuous (w t)) (τ : ℝ) :
    ∀ i, Continuous (schemeMap w τ i) := by
  intro i
  induction i with
  | zero => exact continuous_id
  | succ i ih =>
    exact ih.add (((hwc _).comp ih).const_smul τ)

lemma q12_torusMap_comp {S T : Euc d → Euc d} (hS : PerEquiv S) (hT : PerEquiv T) (x : Torus d) :
    torusMap (fun y => T (S y)) x = torusMap T (torusMap S x) := by
  unfold torusMap
  conv_rhs => rw [show Torus.mk (S (Torus.rep x)) = Torus.mk (S (Torus.rep x)) from rfl]
  have := q12_torusMap_mk hT (S (Torus.rep x))
  unfold torusMap at this
  exact this.symm


lemma q12_weakClose_trans {ν μ μ' : Measure (Torus d)} {b b' : ℝ} (h : WeakClose ν μ b)
    (h' : WeakClose μ μ' b') : WeakClose ν μ' (b + b') := by
  intro Φ B hp hC
  have h1 := h Φ B hp hC
  have h2 := h' Φ B hp hC
  calc |Iw ν Φ - Iw μ' Φ| = |(Iw ν Φ - Iw μ Φ) + (Iw μ Φ - Iw μ' Φ)| := by ring_nf
    _ ≤ |Iw ν Φ - Iw μ Φ| + |Iw μ Φ - Iw μ' Φ| := abs_add_le _ _
    _ ≤ b * B + b' * B := add_le_add h1 h2
    _ = (b + b') * B := by ring

lemma q12_weakClose_mono {ν μ : Measure (Torus d)} {b b' : ℝ} (hbb : b ≤ b')
    (h : WeakClose ν μ b) : WeakClose ν μ b' := by
  intro Φ B hp hC
  have hB0 : 0 ≤ B := le_trans (abs_nonneg _) (hC.2 0).1
  exact (h Φ B hp hC).trans (mul_le_mul_of_nonneg_right hbb hB0)

lemma q12_weakClose_self (μ : Measure (Torus d)) : WeakClose μ μ 0 := by
  intro Φ B _ _
  simp

lemma q12_torusMap_id : torusMap (fun y : Euc d => y) = fun x => x := by
  funext x
  unfold torusMap
  exact Torus.mk_rep x

/-- The weak-norm error of the Euler scheme. -/
theorem q12_scheme_weak {w : ℝ → Euc d → Euc d} {μ : ℝ → Measure (Torus d)} {V V₁ V₂ δ : ℝ}
    (hwc : ∀ t, ContDiff ℝ 2 (w t)) (hwp : ∀ t, Torus.Per (w t))
    (hV : ∀ t ∈ Icc (0 : ℝ) 1, ∀ y, ‖w t y‖ ≤ V)
    (hV₁ : ∀ t ∈ Icc (0 : ℝ) 1, ∀ y, ‖fderiv ℝ (w t) y‖ ≤ V₁)
    (hV₂ : ∀ t ∈ Icc (0 : ℝ) 1, ∀ y, ‖fderiv ℝ (fderiv ℝ (w t)) y‖ ≤ V₂)
    (hprob : ∀ t ∈ Icc (0 : ℝ) 1, IsProbabilityMeasure (μ t)) (hδ : 0 ≤ δ)
    (hCE : ∀ t τ : ℝ, t ∈ Icc (0 : ℝ) 1 → 0 < τ → τ ≤ 1 → t + τ ≤ 1 → ∀ (Φ : Euc d → ℝ) (B : ℝ),
      Torus.Per Φ → C2b B Φ →
      |τ * ∫ x, fderiv ℝ Φ (Torus.rep x) (w t (Torus.rep x)) ∂(μ t) + (Iw (μ t) Φ - Iw (μ (t + τ)) Φ)|
        ≤ δ * τ ^ 2 * B)
    {n : ℕ} (hn : 0 < n) :
    ∀ i : ℕ, i ≤ n → WeakClose ((μ 0).map (torusMap (schemeMap w (1 / n) i)))
      (μ ((i : ℝ) * (1 / n)))
      ((δ + V ^ 2) * (1 / (n : ℝ)) ^ 2 * i * (1 + (2 * V₁ + V₁ ^ 2 + V₂) * (1 / (n : ℝ))) ^ i) := by
  intro i
  induction i with
  | zero =>
    intro _
    simp only [schemeMap, Nat.cast_zero, zero_mul, mul_zero]
    rw [q12_torusMap_id, show (fun x : Torus d => x) = id from rfl, Measure.map_id]
    exact q12_weakClose_self _
  | succ i ih =>
    intro hi
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    set τ : ℝ := 1 / (n : ℝ) with hτ
    have hτ0 : 0 < τ := by positivity
    have hτ1 : τ ≤ 1 := by
      rw [hτ, div_le_one hnR]; exact_mod_cast hn
    have hi' : i ≤ n := by omega
    have hti : (i : ℝ) * τ ∈ Icc (0 : ℝ) 1 := by
      refine ⟨by positivity, ?_⟩
      have : (i : ℝ) ≤ n := by exact_mod_cast hi'
      calc (i : ℝ) * τ ≤ n * τ := mul_le_mul_of_nonneg_right this hτ0.le
        _ = 1 := by rw [hτ]; field_simp
    have hti1 : (i : ℝ) * τ + τ ≤ 1 := by
      have : ((i + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast hi
      calc (i : ℝ) * τ + τ = ((i + 1 : ℕ) : ℝ) * τ := by push_cast; ring
        _ ≤ n * τ := mul_le_mul_of_nonneg_right this hτ0.le
        _ = 1 := by rw [hτ]; field_simp
    have ih' := ih hi'
    set t : ℝ := (i : ℝ) * τ with ht
    haveI := hprob t hti
    have hw2 := hwc t
    set T : Euc d → Euc d := fun y => y + τ • w t y with hT
    have hTe : PerEquiv T := q12_perEquiv_shift (hwp t) τ
    have hSe := q12_schemeMap_perEquiv hwp τ i
    have hSc := q12_schemeMap_continuous (fun t => (hwc t).continuous) τ i
    have hV0 : 0 ≤ V := le_trans (norm_nonneg _) (hV 0 ⟨le_rfl, zero_le_one⟩ 0)
    have hV₁0 : 0 ≤ V₁ := le_trans (norm_nonneg (fderiv ℝ (w 0) 0)) (hV₁ 0 ⟨le_rfl, zero_le_one⟩ 0)
    have hV₂0 : 0 ≤ V₂ := le_trans (norm_nonneg (fderiv ℝ (fderiv ℝ (w 0)) 0))
      (hV₂ 0 ⟨le_rfl, zero_le_one⟩ 0)
    have hν : (μ 0).map (torusMap (schemeMap w τ (i + 1))) =
        ((μ 0).map (torusMap (schemeMap w τ i))).map (torusMap T) := by
      have hcS := q12_continuous_torusMap hSe hSc
      have hcT := q12_continuous_torusMap hTe (continuous_id.add ((hw2.continuous).const_smul τ))
      rw [Measure.map_map hcT.measurable hcS.measurable]
      congr 1
      funext x
      exact q12_torusMap_comp hSe hTe x
    have hstep := q12_weakClose_step hτ0.le hτ1 (hwp t) hw2 (hV₁ t hti) (hV₂ t hti) ih'
    have hcons := q12_consistency (μa := μ t) (μb := μ (t + τ)) (τ := τ) (δ := δ * τ ^ 2) hτ0.le
      (hwp t) hw2.continuous (hV t hti)
      (fun Φ B hp hC => hCE t τ hti hτ0 hτ1 hti1 Φ B hp hC)
    have htr := q12_weakClose_trans hstep hcons
    rw [hν]
    have hT' : ((i + 1 : ℕ) : ℝ) * τ = t + τ := by rw [ht]; push_cast; ring
    rw [hT']
    refine q12_weakClose_mono ?_ htr
    set q : ℝ := 1 + (2 * V₁ + V₁ ^ 2 + V₂) * τ with hq
    have hq1 : 1 ≤ q := by
      have : 0 ≤ (2 * V₁ + V₁ ^ 2 + V₂) * τ := by positivity
      linarith
    set K : ℝ := (δ + V ^ 2) * τ ^ 2 with hK
    have hK0 : 0 ≤ K := by positivity
    have hqp : 1 ≤ q ^ (i + 1) := one_le_pow₀ hq1
    have e1 : K * i * q ^ i * q + (δ * τ ^ 2 + τ ^ 2 * V ^ 2) = K * (i * q ^ (i + 1) + 1) := by
      rw [hK]; ring
    calc K * i * q ^ i * q + (δ * τ ^ 2 + τ ^ 2 * V ^ 2) = K * (i * q ^ (i + 1) + 1) := e1
      _ ≤ K * ((i + 1 : ℕ) * q ^ (i + 1)) := by
          apply mul_le_mul_of_nonneg_left _ hK0
          push_cast; nlinarith
      _ = _ := by push_cast; ring
  
end HRS.Uniform.Q12
