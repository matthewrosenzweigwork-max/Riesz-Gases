import HRS.MC.S7WQAux3

/-!
# Packet `s7_WQ_weak_ui_wasserstein`: weak convergence plus a uniform `(q+δ)`-moment gives `W_q` convergence

Route (a soft version of the cell coupling): a smooth partition of unity `pF` of mesh `s` about a dense sequence
quantises each measure; `W_q(ρ, quant ρ)^q ≤ s^q + ∫ tail_N ‖x‖^q dρ`, the tail term is controlled by
the uniform `(q+δ)`-moment (`wq_tail_moment_le`) and the tail mass, which converges to the tail mass of `ν`
(bounded continuous test function) and is small for `N` large (dominated convergence); the quantised measures are
supported on one finite set and their weights converge (`wq_discrete`).
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.WQ

open HRS

theorem s7_WQ_weak_ui_wasserstein_proof {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
    [CompleteSpace B] [SecondCountableTopology B] [MeasurableSpace B] [BorelSpace B]
    (μ : ℕ → Measure B) [∀ N, IsProbabilityMeasure (μ N)] (ν : Measure B) [IsProbabilityMeasure ν]
    (hweak : ∀ F : B → ℝ, Continuous F → (∃ M, ∀ x, |F x| ≤ M) →
      Tendsto (fun N => ∫ x, F x ∂(μ N)) atTop (𝓝 (∫ x, F x ∂ν)))
    (q δ : ℝ) (hq : 1 ≤ q) (hδ : 0 < δ)
    (hmom : ∃ C : ℝ, ∀ N, Integrable (fun x => ‖x‖ ^ (q + δ)) (μ N) ∧ ∫ x, ‖x‖ ^ (q + δ) ∂(μ N) ≤ C) :
    Tendsto (fun N => wassersteinE q (μ N) ν) atTop (𝓝 0) := by
  obtain ⟨C, hC⟩ := hmom
  have hq0 : 0 < q := by linarith
  have hC0 : 0 ≤ C :=
    (integral_nonneg fun x => Real.rpow_nonneg (norm_nonneg _) _).trans (hC 0).2
  obtain ⟨hνi, hνC⟩ := wq_limit_moment (r := q + δ) (by linarith) μ ν hweak hC
  have hνq : Integrable (fun x : B => ‖x‖ ^ q) ν := wq_integrable_q hq0 hδ ν hνi
  have hμq : ∀ n, Integrable (fun x : B => ‖x‖ ^ q) (μ n) := fun n =>
    wq_integrable_q hq0 hδ (μ n) (hC n).1
  set c : ℕ → B := TopologicalSpace.denseSeq B with hcdef
  have hc : DenseRange c := TopologicalSpace.denseRange_denseSeq B
  have key : ∀ η : ℝ, 0 < η → ∀ᶠ n in atTop, wassersteinE q (μ n) ν ≤ ENNReal.ofReal η := by
    intro η hη
    set θ : ℝ := η / 3 with hθdef
    have hθ : 0 < θ := by positivity
    set K : ℝ := θ ^ q with hKdef
    have hK : 0 < K := Real.rpow_pos_of_pos hθ q
    set κ : ℝ := K / 2 with hκdef
    have hκ : 0 < κ := by positivity
    set s : ℝ := θ / 2 with hsdef
    have hs : 0 < s := by positivity
    have hsq : s ^ q ≤ κ := by
      rw [hsdef, Real.div_rpow hθ.le (by norm_num : (0:ℝ) ≤ 2) q]
      have h2 : (2 : ℝ) ≤ 2 ^ q := by
        calc (2 : ℝ) = 2 ^ (1 : ℝ) := (Real.rpow_one 2).symm
          _ ≤ 2 ^ q := Real.rpow_le_rpow_of_exponent_le (by norm_num) hq
      rw [hκdef, hKdef]
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith [Real.rpow_nonneg hθ.le q]
    -- the radius `R` of the moment split
    set a₀ : ℝ := 2 * C / κ + 1 with ha₀
    have ha₀pos : 0 < a₀ := by positivity
    set R : ℝ := a₀ ^ (1 / δ) with hRdef
    have hR : 0 < R := Real.rpow_pos_of_pos ha₀pos _
    have hRδ : R ^ δ = a₀ := by
      rw [hRdef, ← Real.rpow_mul ha₀pos.le, one_div_mul_cancel hδ.ne', Real.rpow_one]
    have hRC : R ^ (-δ) * C ≤ κ / 2 := by
      rw [Real.rpow_neg hR.le, hRδ, inv_mul_eq_div, div_le_iff₀ ha₀pos]
      have : κ / 2 * a₀ = C + κ / 2 := by
        rw [ha₀]; field_simp
      linarith
    have hRq : 0 < R ^ q := Real.rpow_pos_of_pos hR q
    set τ : ℝ := κ / (2 * R ^ q) with hτdef
    have hτ : 0 < τ := by positivity
    have hτR : R ^ q * τ = κ / 2 := by
      rw [hτdef]; field_simp
    -- choose `N`
    obtain ⟨N, hN⟩ := ((wq_tail_nu hs hc ν).eventually (gt_mem_nhds (half_pos hτ))).exists
    have hN' : ∫ x, tailF s c N x ∂ν < τ / 2 := hN
    have hμt : ∀ᶠ n in atTop, ∫ x, tailF s c N x ∂(μ n) < τ := by
      have := hweak (fun x => tailF s c N x) (continuous_tailF s c N) ⟨1, fun x => by
        rw [abs_of_nonneg (tailF_nonneg s c N x)]; exact tailF_le_one s c N x⟩
      exact this.eventually (gt_mem_nhds (by linarith))
    -- discrete weights
    set a : Fin (N + 1) → B := aF c N with hadef
    set D : ℝ := 2 * ∑ k, ‖a k‖ with hD
    have hD0 : 0 ≤ D := by positivity
    have hDk : ∀ k l, ‖a k - a l‖ ≤ D := by
      intro k l
      have h1 : ‖a k‖ ≤ ∑ j, ‖a j‖ :=
        Finset.single_le_sum (f := fun j => ‖a j‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ k)
      have h2 : ‖a l‖ ≤ ∑ j, ‖a j‖ :=
        Finset.single_le_sum (f := fun j => ‖a j‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ l)
      calc ‖a k - a l‖ ≤ ‖a k‖ + ‖a l‖ := norm_sub_le _ _
        _ ≤ D := by rw [hD]; linarith
    have hw : ∀ k, Tendsto (fun n => ∫ x, pF s c N k x ∂(μ n)) atTop (𝓝 (∫ x, pF s c N k x ∂ν)) :=
      fun k => hweak (pF s c N k) (continuous_pF s c N k) ⟨1, fun x => by
        rw [abs_of_nonneg (pF_nonneg s c N k x)]
        exact f_le_one (pF_nonneg s c N) (sum_pF s c N) k x⟩
    have hS : Tendsto (fun n => ∑ k, |∫ x, pF s c N k x ∂(μ n) - ∫ x, pF s c N k x ∂ν|) atTop (𝓝 0) := by
      have := tendsto_finsetSum Finset.univ (fun k _ => ((hw k).sub_const
        (∫ x, pF s c N k x ∂ν)).abs)
      simpa using this
    have hev2 : ∀ᶠ n in atTop, D ^ q * ∑ k, |∫ x, pF s c N k x ∂(μ n) -
        ∫ x, pF s c N k x ∂ν| < K := by
      have := hS.const_mul (D ^ q)
      rw [mul_zero] at this
      exact this.eventually (gt_mem_nhds hK)
    -- the tail estimate for a measure with the moment bound
    have htail : ∀ (ρ : Measure B) [IsProbabilityMeasure ρ], Integrable (fun x : B => ‖x‖ ^ (q + δ)) ρ →
        ∫ x, ‖x‖ ^ (q + δ) ∂ρ ≤ C → ∫ x, tailF s c N x ∂ρ < τ →
        s ^ q + ∫ x, tailF s c N x * ‖x‖ ^ q ∂ρ ≤ θ ^ q := by
      intro ρ _ hi hCρ ht
      have h1 := wq_tail_moment_le hq0 hδ ρ hi hCρ hR (s := s) c N
      have h2 : R ^ q * ∫ x, tailF s c N x ∂ρ ≤ κ / 2 := by
        rw [← hτR]; exact mul_le_mul_of_nonneg_left ht.le hRq.le
      have : K = 2 * κ := by rw [hκdef]; ring
      rw [← hKdef]
      linarith
    filter_upwards [hμt, hev2] with n h1 h2
    haveI := isProb_quantMeas s c N (μ n)
    haveI := isProb_quantMeas s c N ν
    have e1 := wq_quant_le hq hs c N (μ n) (hμq n) hθ.le
      (htail (μ n) (hC n).1 (hC n).2 h1)
    have e3 := wq_quant_le hq hs c N ν hνq hθ.le
      (htail ν hνi hνC (by linarith))
    have e2 := wq_discrete hq a (fun k => ∫ x, pF s c N k x ∂(μ n)) (fun k => ∫ x, pF s c N k x ∂ν)
      (fun k => integral_nonneg (pF_nonneg s c N k)) (fun k => integral_nonneg (pF_nonneg s c N k))
      (sum_integral_pF s c N _) (sum_integral_pF s c N _) D hD0 hDk hθ.le h2.le
    rw [wq_comm] at e3
    have t1 := wassersteinE_triangle q hq (μ n) (quantMeas s c N (μ n)) ν
    have t2 := wassersteinE_triangle q hq (quantMeas s c N (μ n)) (quantMeas s c N ν) ν
    calc _ ≤ _ := t1
      _ ≤ wassersteinE q (μ n) (quantMeas s c N (μ n)) +
          (wassersteinE q (quantMeas s c N (μ n)) (quantMeas s c N ν) +
            wassersteinE q (quantMeas s c N ν) ν) := add_le_add le_rfl t2
      _ ≤ ENNReal.ofReal θ + (ENNReal.ofReal θ + ENNReal.ofReal θ) :=
          add_le_add e1 (add_le_add e2 e3)
      _ = ENNReal.ofReal η := by
          rw [← ENNReal.ofReal_add hθ.le hθ.le, ← ENNReal.ofReal_add hθ.le (by positivity)]
          congr 1; rw [hθdef]; ring
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  by_cases htop : ε = ⊤
  · exact Filter.Eventually.of_forall fun n => htop ▸ le_top
  · have := key ε.toReal (ENNReal.toReal_pos hε.ne' htop)
    rwa [ENNReal.ofReal_toReal htop] at this

end HRS.MC.Sec7.WQ
