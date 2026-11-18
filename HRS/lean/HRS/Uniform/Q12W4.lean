import HRS.Uniform.Q12W3
import HRS.Uniform.Q12Aux5

/-!
# Q12, part W4: symmetry of `W_2`, and the `Ḣ^{-1}` bound for smeared differences
-/

noncomputable section

open HRS MeasureTheory Filter Topology
open HRS.CoercAux
open scoped ENNReal NNReal BigOperators ComplexConjugate

namespace HRS.Uniform.Q12

variable {d : ℕ}

lemma q12_tdist_symm (x y : Torus d) : Torus.tdist x y = Torus.tdist y x := by
  have h1 : Torus.tdist x y = KernelGrad.tdist x y := rfl
  have h2 : Torus.tdist y x = KernelGrad.tdist y x := rfl
  rw [h1, h2]
  exact HRS.Commutator.Renorm.tdist_symm' x y

theorem q12_W_symm (p : ℝ) (μ ν : Measure (Torus d)) :
    torusWassersteinE p μ ν ≤ torusWassersteinE p ν μ := by
  refine le_iInf fun π => ?_
  have hsw : Measurable (Prod.swap : Torus d × Torus d → Torus d × Torus d) := measurable_swap
  have h1 : (π.1.map Prod.swap).map Prod.fst = μ := by
    rw [Measure.map_map measurable_fst hsw]
    have : (Prod.fst ∘ Prod.swap : Torus d × Torus d → Torus d) = Prod.snd := rfl
    rw [this]; exact π.2.2
  have h2 : (π.1.map Prod.swap).map Prod.snd = ν := by
    rw [Measure.map_map measurable_snd hsw]
    have : (Prod.snd ∘ Prod.swap : Torus d × Torus d → Torus d) = Prod.fst := rfl
    rw [this]; exact π.2.1
  refine (q12_W_le_cost h1 h2).trans (le_of_eq ?_)
  have hF : Measurable fun z : Torus d × Torus d => ENNReal.ofReal (Torus.tdist z.1 z.2 ^ p) :=
    (q12_measurable_tdist.pow_const p).ennreal_ofReal
  rw [lintegral_map hF hsw]
  congr 1
  refine lintegral_congr fun z => ?_
  show ENNReal.ofReal (Torus.tdist z.2 z.1 ^ p) = ENNReal.ofReal (Torus.tdist z.1 z.2 ^ p)
  rw [q12_tdist_symm]

/-- `u^r e^{-u} ≤ 1 + ⌈r⌉!`. -/
lemma q12_rpow_exp_le {r : ℝ} (hr : 0 ≤ r) {u : ℝ} (hu : 0 ≤ u) :
    u ^ r * Real.exp (-u) ≤ 1 + (⌈r⌉₊.factorial : ℝ) := by
  have hn := Real.exp_pos u
  have hexp : Real.exp (-u) * Real.exp u = 1 := by rw [← Real.exp_add]; simp
  have hexp1 : Real.exp (-u) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  have hfac : (0 : ℝ) ≤ (⌈r⌉₊.factorial : ℝ) := by positivity
  rcases le_total u 1 with h | h
  · have : u ^ r ≤ 1 := Real.rpow_le_one hu h hr
    calc u ^ r * Real.exp (-u) ≤ 1 * 1 :=
          mul_le_mul this hexp1 (Real.exp_pos _).le zero_le_one
      _ ≤ _ := by linarith
  · have h1 : u ^ r ≤ u ^ (⌈r⌉₊ : ℝ) := Real.rpow_le_rpow_of_exponent_le h (Nat.le_ceil r)
    rw [Real.rpow_natCast] at h1
    have h2 := Real.pow_div_factorial_le_exp u hu ⌈r⌉₊
    have h3 : u ^ ⌈r⌉₊ * Real.exp (-u) ≤ (⌈r⌉₊.factorial : ℝ) := by
      have hf : (0 : ℝ) < (⌈r⌉₊.factorial : ℝ) := by positivity
      rw [div_le_iff₀ hf] at h2
      calc u ^ ⌈r⌉₊ * Real.exp (-u) ≤ (Real.exp u * (⌈r⌉₊.factorial : ℝ)) * Real.exp (-u) :=
            mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le
        _ = (⌈r⌉₊.factorial : ℝ) * (Real.exp (-u) * Real.exp u) := by ring
        _ = _ := by rw [hexp, mul_one]
    calc u ^ r * Real.exp (-u) ≤ u ^ ⌈r⌉₊ * Real.exp (-u) :=
          mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
      _ ≤ _ := by linarith


lemma q12_cT_neg (s ε : ℝ) (k : Lattice d) : CoercAux.cT d s ε (-k) = CoercAux.cT d s ε k := by
  unfold CoercAux.cT
  by_cases hk : k = 0
  · simp [hk]
  · have hk' : -k ≠ 0 := neg_ne_zero.2 hk
    rw [if_neg hk, if_neg hk', q12_enorm_neg]

lemma q12_Esq_summable (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {e : ℝ} (he : 0 < e)
    {N : ℕ} (hN : 0 < N) (X : Config d N) (μ : Measure (Torus d)) [IsProbabilityMeasure μ] :
    Summable fun k : Lattice d => CoercAux.cT d s e k * ‖deltaF X μ k‖ ^ 2 := by
  refine Summable.of_nonneg_of_le (fun k => mul_nonneg (cT_nonneg hd hs0 hsd he k) (sq_nonneg _))
    (fun k => ?_) ((summable_cT hd hs0 hsd he).mul_right 4)
  refine mul_le_mul_of_nonneg_left ?_ (cT_nonneg hd hs0 hsd he k)
  have h2 : ‖deltaF X μ k‖ ≤ 2 := delta_norm_le hN X μ k
  have h3 := norm_nonneg (deltaF X μ k)
  nlinarith

/-- The weight inequality behind `(U:eq:smear-Hminus1)`. -/
lemma q12_weight (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {ε₀ t : ℝ}, 0 < ε₀ → 2 * ε₀ ≤ t → ∀ k : Lattice d, k ≠ 0 →
      (Lattice.enorm k ^ 2)⁻¹ * Real.exp (-t * Lattice.enorm k ^ 2) ^ 2 ≤
        K * t ^ (-(max (((d : ℝ) - s) - 2) 0) / 2) * CoercAux.cT d s ε₀ k := by
  obtain ⟨c, hc, hcl⟩ := cT_lower hd hs0 hsd
  set q' : ℝ := max (((d : ℝ) - s) - 2) 0 with hq'
  have hq'0 : 0 ≤ q' := le_max_right _ _
  set r : ℝ := q' / 2 with hr
  have hr0 : 0 ≤ r := by positivity
  set C₁ : ℝ := 1 + (⌈r⌉₊.factorial : ℝ) with hC₁
  have hC₁0 : 0 < C₁ := by positivity
  refine ⟨C₁ / c, by positivity, fun {ε₀ t} hε₀ ht k hk => ?_⟩
  have ht0 : 0 < t := by linarith
  set e : ℝ := Lattice.enorm k with he
  have he1 : 1 ≤ e := one_le_enorm k hk
  set w : ℝ := e ^ 2 with hw
  have hw1 : 1 ≤ w := by rw [hw]; nlinarith
  have hw0 : 0 < w := by linarith
  set a : ℝ := ((d : ℝ) - s) / 2 with ha
  have h1 := hcl hε₀ k hk
  -- the key inequality
  have hkey : w⁻¹ * Real.exp (-t * w) ^ 2 ≤
      C₁ * t ^ (-r) * (Real.exp (-(2 * ε₀ * w)) * w ^ (-a)) := by
    have e1 : Real.exp (-t * w) ^ 2 = Real.exp (-(2 * t * w)) := by
      rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
    have e2 : w⁻¹ = w ^ (a - 1) * w ^ (-a) := by
      rw [← Real.rpow_add hw0, show a - 1 + -a = -1 by ring, Real.rpow_neg_one]
    have e3 : Real.exp (-(2 * t * w)) = Real.exp (-(2 * (t - ε₀) * w)) * Real.exp (-(2 * ε₀ * w)) := by
      rw [← Real.exp_add]; congr 1; ring
    have hexp : Real.exp (-(2 * (t - ε₀) * w)) ≤ Real.exp (-t * w) := by
      apply Real.exp_le_exp.2; nlinarith
    have hwr : w ^ (a - 1) ≤ w ^ r := by
      apply Real.rpow_le_rpow_of_exponent_le hw1
      have : a - 1 = (((d : ℝ) - s) - 2) / 2 := by rw [ha]; ring
      rw [this, hr]
      have := le_max_left (((d : ℝ) - s) - 2) 0
      linarith
    have hR := q12_rpow_exp_le hr0 (u := t * w) (by positivity)
    have hmul : w ^ r * Real.exp (-t * w) ≤ C₁ * t ^ (-r) := by
      have h1 : (t * w) ^ r = t ^ r * w ^ r := Real.mul_rpow ht0.le hw0.le
      rw [h1] at hR
      have h2 : Real.exp (-(t * w)) = Real.exp (-t * w) := by congr 1; ring
      rw [h2] at hR
      have htr : 0 < t ^ r := Real.rpow_pos_of_pos ht0 r
      rw [Real.rpow_neg ht0.le, ← div_eq_mul_inv, le_div_iff₀ htr]
      calc w ^ r * Real.exp (-t * w) * t ^ r = t ^ r * w ^ r * Real.exp (-t * w) := by ring
        _ ≤ C₁ := hR
    have hpos1 : 0 ≤ Real.exp (-(2 * ε₀ * w)) * w ^ (-a) :=
      mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg hw0.le _)
    calc w⁻¹ * Real.exp (-t * w) ^ 2
        = (w ^ (a - 1) * Real.exp (-(2 * (t - ε₀) * w))) * (Real.exp (-(2 * ε₀ * w)) * w ^ (-a)) := by
          rw [e1, e2, e3]; ring
      _ ≤ (C₁ * t ^ (-r)) * (Real.exp (-(2 * ε₀ * w)) * w ^ (-a)) := by
          refine mul_le_mul_of_nonneg_right ?_ hpos1
          calc w ^ (a - 1) * Real.exp (-(2 * (t - ε₀) * w)) ≤ w ^ r * Real.exp (-t * w) :=
                mul_le_mul hwr hexp (Real.exp_pos _).le (Real.rpow_nonneg hw0.le _)
            _ ≤ _ := hmul
  have hc0 : 0 < c := hc
  have h1' : c * (Real.exp (-(2 * ε₀ * w)) * w ^ (-a)) ≤ CoercAux.cT d s ε₀ k := by
    have := h1
    simpa [he, hw, ha] using this
  calc (Lattice.enorm k ^ 2)⁻¹ * Real.exp (-t * Lattice.enorm k ^ 2) ^ 2
      = w⁻¹ * Real.exp (-t * w) ^ 2 := rfl
    _ ≤ C₁ * t ^ (-r) * (Real.exp (-(2 * ε₀ * w)) * w ^ (-a)) := hkey
    _ = (C₁ / c * t ^ (-(q') / 2)) * (c * (Real.exp (-(2 * ε₀ * w)) * w ^ (-a))) := by
        rw [hr]; field_simp
    _ ≤ (C₁ / c * t ^ (-(q') / 2)) * CoercAux.cT d s ε₀ k := by
        refine mul_le_mul_of_nonneg_left h1' ?_
        have : 0 ≤ t ^ (-(q') / 2) := Real.rpow_nonneg ht0.le _
        positivity


/-- The `Ḣ^{-1}`-type sum `∑_{k≠0} |k|^{-2} |f̂(k) - ĝ(k)|²` (up to the factor `4π²`). -/
def hmSum (f g : Torus d → ℝ) : ℝ :=
  ∑' k : Lattice d, if k = 0 then 0 else
    (Lattice.enorm k ^ 2)⁻¹ * ‖Torus.fcoef f k - Torus.fcoef g k‖ ^ 2

/-- `(U:eq:smear-Hminus1)`: the `Ḣ^{-1}` norm of the smeared difference is controlled by `Esq`. -/
theorem q12_hmSum_le (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {ε₀ t : ℝ}, 0 < ε₀ → 2 * ε₀ ≤ t → ∀ {N : ℕ}, 0 < N →
      ∀ (X : Config d N) (μ : Measure (Torus d)) [IsProbabilityMeasure μ],
      hmSum (smearDens d t (empirical X)) (smearDens d t μ) ≤
        K * t ^ (-(max (((d : ℝ) - s) - 2) 0) / 2) * Esq d s ε₀ X μ := by
  obtain ⟨K, hK0, hK⟩ := q12_weight hd hs0 hsd
  refine ⟨K, hK0, fun {ε₀ t} hε₀ ht {N} hN X μ _ => ?_⟩
  have ht0 : 0 < t := by linarith
  haveI := empirical_isProbabilityMeasure hN X
  have hterm : ∀ k : Lattice d, (if k = 0 then (0 : ℝ) else
      (Lattice.enorm k ^ 2)⁻¹ * ‖Torus.fcoef (smearDens d t (empirical X)) k -
        Torus.fcoef (smearDens d t μ) k‖ ^ 2) ≤
      K * t ^ (-(max (((d : ℝ) - s) - 2) 0) / 2) *
        (CoercAux.cT d s ε₀ (-k) * ‖deltaF X μ (-k)‖ ^ 2) := by
    intro k
    by_cases hk : k = 0
    · simp only [hk, if_true]
      have : 0 ≤ CoercAux.cT d s ε₀ (-(0 : Lattice d)) * ‖deltaF X μ (-(0 : Lattice d))‖ ^ 2 :=
        mul_nonneg (cT_nonneg hd hs0 hsd hε₀ _) (sq_nonneg _)
      have h2 : 0 ≤ K * t ^ (-(max (((d : ℝ) - s) - 2) 0) / 2) :=
        mul_nonneg hK0 (Real.rpow_nonneg ht0.le _)
      exact mul_nonneg h2 this
    · simp only [hk, if_false]
      have hdiff : Torus.fcoef (smearDens d t (empirical X)) k - Torus.fcoef (smearDens d t μ) k =
          (Real.exp (-t * Lattice.enorm k ^ 2) : ℂ) * deltaF X μ (-k) := by
        rw [q12_fcoef_smearDens ht0 (empirical X) k, q12_fcoef_smearDens ht0 μ k,
          integral_empirical_mode hN X (-k)]
        unfold deltaF
        ring
      rw [hdiff, norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le, mul_pow]
      have hw := hK hε₀ ht k hk
      have hcneg : CoercAux.cT d s ε₀ (-k) = CoercAux.cT d s ε₀ k := q12_cT_neg s ε₀ k
      rw [hcneg]
      have h3 : 0 ≤ ‖deltaF X μ (-k)‖ ^ 2 := sq_nonneg _
      calc (Lattice.enorm k ^ 2)⁻¹ * (Real.exp (-t * Lattice.enorm k ^ 2) ^ 2 * ‖deltaF X μ (-k)‖ ^ 2)
          = ((Lattice.enorm k ^ 2)⁻¹ * Real.exp (-t * Lattice.enorm k ^ 2) ^ 2) * ‖deltaF X μ (-k)‖ ^ 2 := by ring
        _ ≤ (K * t ^ (-(max (((d : ℝ) - s) - 2) 0) / 2) * CoercAux.cT d s ε₀ k) * ‖deltaF X μ (-k)‖ ^ 2 :=
            mul_le_mul_of_nonneg_right hw h3
        _ = _ := by ring
  have hs1 : Summable fun k : Lattice d => CoercAux.cT d s ε₀ (-k) * ‖deltaF X μ (-k)‖ ^ 2 :=
    (Equiv.neg (Lattice d)).summable_iff.2 (q12_Esq_summable hd hs0 hsd hε₀ hN X μ)
  have hs2 : Summable fun k : Lattice d => K * t ^ (-(max (((d : ℝ) - s) - 2) 0) / 2) *
      (CoercAux.cT d s ε₀ (-k) * ‖deltaF X μ (-k)‖ ^ 2) := hs1.mul_left _
  have hnn : ∀ k : Lattice d, 0 ≤ (if k = 0 then (0 : ℝ) else
      (Lattice.enorm k ^ 2)⁻¹ * ‖Torus.fcoef (smearDens d t (empirical X)) k -
        Torus.fcoef (smearDens d t μ) k‖ ^ 2) := fun k => by
    split_ifs
    · exact le_rfl
    · positivity
  unfold hmSum
  calc _ ≤ ∑' k : Lattice d, K * t ^ (-(max (((d : ℝ) - s) - 2) 0) / 2) *
        (CoercAux.cT d s ε₀ (-k) * ‖deltaF X μ (-k)‖ ^ 2) :=
        (Summable.of_nonneg_of_le hnn hterm hs2).tsum_le_tsum hterm hs2
    _ = K * t ^ (-(max (((d : ℝ) - s) - 2) 0) / 2) * Esq d s ε₀ X μ := by
        rw [tsum_mul_left]
        congr 1
        unfold Esq
        exact Equiv.tsum_eq (Equiv.neg (Lattice d))
          (fun k => CoercAux.cT d s ε₀ k * ‖deltaF X μ k‖ ^ 2)

end HRS.Uniform.Q12
