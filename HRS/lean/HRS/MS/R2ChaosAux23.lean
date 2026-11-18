import HRS.MS.R2ChaosAux22

/-!
# HRS.MS.R2ChaosAux23 -- joint convergence in law for finite-rank kernels with time-dependent coefficients

Packet S94, namespace `HRS.MS.R2Chaos`, helper prefix `s94_`.
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false
set_option linter.style.haveILetI false
set_option linter.deprecated false

open MeasureTheory ProbabilityTheory Function Set Filter
open scoped ENNReal NNReal Topology

noncomputable section

namespace HRS.MS.R2Chaos

open HRS.Whole

variable {d : ℕ}

theorem s94_memLp_of_bdd {T : ℝ} {f : ℝ → ℝ} (hf : Measurable f) {K : ℝ}
    (hb : ∀ t ∈ Set.Icc (0 : ℝ) T, |f t| ≤ K) : MemLp f 2 (volume.restrict (Set.Icc (0 : ℝ) T)) := by
  have : IsFiniteMeasure (volume.restrict (Set.Icc (0 : ℝ) T)) := by constructor; simp
  exact MemLp.of_bound hf.aestronglyMeasurable K
    ((ae_restrict_iff' measurableSet_Icc).2 (ae_of_all _ fun t ht => by simpa using hb t ht))

section Flat

variable {s T b p K M L : ℝ} {ρ : Euc d → ℝ} {Ω : ℕ → Type} [∀ N, MeasurableSpace (Ω N)]
  {P : ∀ N, Measure (Ω N)} [∀ N, IsProbabilityMeasure (P N)] {X : ∀ N, ℝ≥0 → Ω N → EucConfig d N}
  {Ω' : Type} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
  {ξ : (Euc d → ℝ) → Ω' → C(Set.Icc (0 : ℝ) T, ℝ)}

/-- The limit integrand `F_C(t, ζ) = ½ ∑ C_ab(t) (ξ^t(ũ_a) ξ^t(ũ_b) - E)`. -/
def s94Flim {n : ℕ} (ξ0 : (Euc d → ℝ) → Ω' → C(Set.Icc (0 : ℝ) T, ℝ)) (P0 : Measure Ω')
    (C : ℝ → Fin n → Fin n → ℝ) (u : Fin n → Euc d → ℝ) (t : ℝ) (ζ : Ω') : ℝ :=
  ∑ p : Fin n × Fin n, ((1 / 2) * C t p.1 p.2) * (r2PathEval T (ξ0 (u p.1) ζ) t * r2PathEval T (ξ0 (u p.2) ζ) t -
    ∫ ζ', r2PathEval T (ξ0 (u p.1) ζ') t * r2PathEval T (ξ0 (u p.2) ζ') t ∂P0)

theorem s94_quad_decomp {μ : Measure (Euc d)} [IsProbabilityMeasure μ] {N : ℕ} (hN : 0 < N) {n : ℕ}
    {C : ℝ → Fin n → Fin n → ℝ} (hCs : ∀ t a b, C t a b = C t b a) {u : Fin n → Euc d → ℝ}
    (hu : ∀ a, IsR2Test (u a)) {Ω0 : Type*} [MeasurableSpace Ω0] (P0 : Measure Ω0) [IsProbabilityMeasure P0]
    (X0 : ℝ≥0 → Ω0 → EucConfig d N) (hX : Measurable fun q : ℝ≥0 × Ω0 => X0 q.1 q.2) (t : ℝ) (ζ : Ω0) :
    r2QuadFluct μ (fun t => r2FiniteRankKernel (C t) u) P0 X0 t ζ =
      ∑ p : Fin n × Fin n, ((1 / 2) * C t p.1 p.2) * (r2EmpFluct μ (u p.1) X0 ζ t * r2EmpFluct μ (u p.2) X0 ζ t) -
        s94mN μ X0 P0 (fun (p : Fin n × Fin n) t => (1 / 2) * C t p.1 p.2) (fun p => u p.1) (fun p => u p.2) t -
        s94Rt X0 P0 C u t ζ := by
  have h := s94_quad_finiteRank (μ := μ) hu (hCs t) hN P0 X0 hX t ζ
  have e : r2QuadFluct μ (fun t => r2FiniteRankKernel (C t) u) P0 X0 t ζ =
      r2QuadFluct μ (fun _ => r2FiniteRankKernel (C t) u) P0 X0 t ζ := rfl
  rw [e, h]
  unfold s94mN s94Rt s94Gt s94gt
  simp only [Fintype.sum_prod_type, mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]
  ring_nf

/-- Coefficients `(1/2) C_ab(t)` indexed by pairs. -/
def s94coef {n : ℕ} (C : ℝ → Fin n → Fin n → ℝ) : Fin n × Fin n → ℝ → ℝ := fun p t => (1 / 2) * C t p.1 p.2

/-- The continuous quadratic path map `Ψ`. -/
def s94Psi {n : ℕ} (C : ℝ → Fin n → Fin n → ℝ) (w : Fin n → C(Set.Icc (0 : ℝ) T, ℝ)) : R2L2 T :=
  r2L2Path T (s94Intg (s94coef C) Prod.fst Prod.snd w)

theorem s94coef_measurable {n : ℕ} {C : ℝ → Fin n → Fin n → ℝ} (hCm : ∀ a b, Measurable fun t => C t a b)
    (p : Fin n × Fin n) : Measurable (s94coef C p) := measurable_const.mul (hCm p.1 p.2)

theorem s94coef_abs_le {n : ℕ} {C : ℝ → Fin n → Fin n → ℝ} {K0 : ℝ} (hK0 : 0 ≤ K0)
    (hCb : ∀ t a b, |C t a b| ≤ K0) (p : Fin n × Fin n) (t : ℝ) : |s94coef C p t| ≤ K0 := by
  unfold s94coef
  rw [abs_mul]
  have h2 : |(1 / 2 : ℝ)| = 1 / 2 := by norm_num
  rw [h2]
  have := hCb t p.1 p.2
  linarith

theorem s94_pathEval_r2ContPath {T : ℝ} {f : ℝ → ℝ} (hf : Continuous f) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) :
    r2PathEval T (r2ContPath T f) t = f t := by
  rw [s94_pathEval_eq ht, s94_r2ContPath_eq (hf.comp continuous_subtype_val)]
  rfl

/-- The pathwise approximation estimate: the continuous functional of the paths approximates the true process. -/
theorem s94_flat_approx (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) (hb : 0 < b) (hp : 1 < p)
    (hρ : IsRound2Density d s M L ρ)
    (hset : IsRound2PathSetting d s T b p K (Whole.withDensityReal ρ) P X P' ξ) (hT : 0 ≤ T) {n : ℕ}
    {u : Fin n → Euc d → ℝ} (hu : ∀ a, IsR2Test (u a)) {C : ℝ → Fin n → Fin n → ℝ}
    (hCm : ∀ a b, Measurable fun t => C t a b) {K0 : ℝ} (hK0 : 0 ≤ K0) (hCb : ∀ t a b, |C t a b| ≤ K0)
    (hCs : ∀ t a b, C t a b = C t b a) :
    ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧ ∀ N : ℕ, 2 ≤ N →
      ∫⁻ ζ, ‖s94Psi C (fun a => r2ContPath T (r2EmpFluct (Whole.withDensityReal ρ) (u a) (X N) ζ)) -
          r2L2Path T (s94mL ξ P' (s94coef C) (fun q => u q.1) (fun q => u q.2)) -
          r2L2Path T (fun t => r2QuadFluct (Whole.withDensityReal ρ) (fun t => r2FiniteRankKernel (C t) u)
            (P N) (X N) t ζ)‖ₑ ^ 2 ∂(P N) ≤ ENNReal.ofReal (ε N) := by
  haveI : IsProbabilityMeasure (Whole.withDensityReal ρ) := HRS.Whole.U1.u1_isProb hρ.prob
  obtain ⟨C1, hLM⟩ := s94_linear_moment hd hs0 hs hb hp hρ hset (r := 2) (by norm_num)
  obtain ⟨Kr, hKr⟩ := s94_R_small hT hset.measX hCm hK0 hCb hu (μ := Whole.withDensityReal ρ) (C1 := C1) hLM
  obtain ⟨Ag, hAg0, hAg⟩ := s94gt_abs_le (C := C) hK0 hCb hu
  obtain ⟨K1, hK1, hbN, hbL⟩ := s94mN_bdd hd hs0 hs hb hp hρ hset (coef := s94coef C) hK0
    (s94coef_abs_le hK0 hCb) (ua := fun q => u q.1) (ub := fun q => u q.2) (fun q => hu q.1) (fun q => hu q.2)
  have hdN := s94_mN_tendsto hd hs0 hs hb hp hρ hset hT (coef := s94coef C) (s94coef_measurable hCm) hK0
    (s94coef_abs_le hK0 hCb) (ua := fun q => u q.1) (ub := fun q => u q.2) (fun q => hu q.1) (fun q => hu q.2)
  refine ⟨fun N => 2 * (dist (r2L2Path T (s94mN (Whole.withDensityReal ρ) (X N) (P N) (s94coef C)
      (fun q => u q.1) (fun q => u q.2)))
      (r2L2Path T (s94mL ξ P' (s94coef C) (fun q => u q.1) (fun q => u q.2)))) ^ 2 + 2 * (|Kr| / N), ?_, ?_⟩
  · have h1 : Tendsto (fun N : ℕ => 2 * (dist (r2L2Path T (s94mN (Whole.withDensityReal ρ) (X N) (P N) (s94coef C)
        (fun q => u q.1) (fun q => u q.2)))
        (r2L2Path T (s94mL ξ P' (s94coef C) (fun q => u q.1) (fun q => u q.2)))) ^ 2) atTop (𝓝 (2 * 0 ^ 2)) :=
      (hdN.pow 2).const_mul 2
    have h2 : Tendsto (fun N : ℕ => 2 * (|Kr| / (N : ℝ))) atTop (𝓝 (2 * 0)) :=
      (tendsto_const_div_atTop_nhds_zero_nat |Kr|).const_mul 2
    simpa using h1.add h2
  · intro N hN
    have hN0 : 0 < N := by omega
    have hμ := Whole.withDensityReal ρ
    -- pointwise estimate
    have hpt : ∀ᵐ ζ ∂(P N), ‖s94Psi C (fun a => r2ContPath T (r2EmpFluct (Whole.withDensityReal ρ) (u a) (X N) ζ)) -
          r2L2Path T (s94mL ξ P' (s94coef C) (fun q => u q.1) (fun q => u q.2)) -
          r2L2Path T (fun t => r2QuadFluct (Whole.withDensityReal ρ) (fun t => r2FiniteRankKernel (C t) u)
            (P N) (X N) t ζ)‖ₑ ^ 2 ≤
        ENNReal.ofReal (2 * (dist (r2L2Path T (s94mN (Whole.withDensityReal ρ) (X N) (P N) (s94coef C)
          (fun q => u q.1) (fun q => u q.2))) (r2L2Path T (s94mL ξ P' (s94coef C) (fun q => u q.1)
          (fun q => u q.2)))) ^ 2) + 2 * ∫⁻ t in Set.Icc (0 : ℝ) T,
            ENNReal.ofReal ((s94Rt (X N) (P N) C u t ζ) ^ 2) ∂volume := by
      filter_upwards [hset.contX N] with ζ hζ
      have hcont : ∀ a, Continuous fun t : ℝ => r2EmpFluct (Whole.withDensityReal ρ) (u a) (X N) ζ t :=
        fun a => s94_empFluct_continuous (Whole.withDensityReal ρ) (X N) (hu a) ζ hζ
      have hQ : ∀ t ∈ Set.Icc (0 : ℝ) T, s94Intg (s94coef C) Prod.fst Prod.snd
          (fun a => r2ContPath T (r2EmpFluct (Whole.withDensityReal ρ) (u a) (X N) ζ)) t =
          ∑ q : Fin n × Fin n, s94coef C q t * (r2EmpFluct (Whole.withDensityReal ρ) (u q.1) (X N) ζ t *
            r2EmpFluct (Whole.withDensityReal ρ) (u q.2) (X N) ζ t) := by
        intro t ht
        unfold s94Intg
        refine Finset.sum_congr rfl fun q _ => ?_
        rw [s94_pathEval_r2ContPath (hcont q.1) ht, s94_pathEval_r2ContPath (hcont q.2) ht]
      have hΨ : s94Psi C (fun a => r2ContPath T (r2EmpFluct (Whole.withDensityReal ρ) (u a) (X N) ζ)) =
          r2L2Path T (fun t => ∑ q : Fin n × Fin n, s94coef C q t * (r2EmpFluct (Whole.withDensityReal ρ) (u q.1) (X N) ζ t *
            r2EmpFluct (Whole.withDensityReal ρ) (u q.2) (X N) ζ t)) := s94_r2L2Path_congr hQ
      have hmemQ : MemLp (fun t => ∑ q : Fin n × Fin n, s94coef C q t * (r2EmpFluct (Whole.withDensityReal ρ) (u q.1) (X N) ζ t *
            r2EmpFluct (Whole.withDensityReal ρ) (u q.2) (X N) ζ t)) 2 (volume.restrict (Set.Icc (0 : ℝ) T)) := by
        have hae : s94Intg (s94coef C) Prod.fst Prod.snd
            (fun a => r2ContPath T (r2EmpFluct (Whole.withDensityReal ρ) (u a) (X N) ζ)) =ᵐ[volume.restrict (Set.Icc (0 : ℝ) T)]
            (fun t => ∑ q : Fin n × Fin n, s94coef C q t * (r2EmpFluct (Whole.withDensityReal ρ) (u q.1) (X N) ζ t *
            r2EmpFluct (Whole.withDensityReal ρ) (u q.2) (X N) ζ t)) :=
          (ae_restrict_iff' measurableSet_Icc).2 (ae_of_all _ hQ)
        exact (memLp_congr_ae hae).1 (s94Intg_memLp hT (s94coef_measurable hCm) (s94coef_abs_le hK0 hCb) Prod.fst Prod.snd _)
      generalize hQd : (fun t => ∑ q : Fin n × Fin n, s94coef C q t * (r2EmpFluct (Whole.withDensityReal ρ) (u q.1) (X N) ζ t *
            r2EmpFluct (Whole.withDensityReal ρ) (u q.2) (X N) ζ t)) = Qt at hΨ hmemQ
      have hQt : ∀ t, Qt t = ∑ q : Fin n × Fin n, s94coef C q t * (r2EmpFluct (Whole.withDensityReal ρ) (u q.1) (X N) ζ t *
            r2EmpFluct (Whole.withDensityReal ρ) (u q.2) (X N) ζ t) := fun t => (congrFun hQd t).symm
      have hmemm : MemLp (s94mN (Whole.withDensityReal ρ) (X N) (P N) (s94coef C) (fun q => u q.1) (fun q => u q.2)) 2
          (volume.restrict (Set.Icc (0 : ℝ) T)) :=
        s94_memLp_of_bdd (s94mN_measurable (μ := Whole.withDensityReal ρ) (X N) (hset.measX N) (P N) (s94coef_measurable hCm)
          (fun q => hu q.1) (fun q => hu q.2)) (fun t ht => hbN N hN t ht)
      have hRmeas : Measurable fun t => s94Rt (X N) (P N) C u t ζ :=
        Measurable.comp (g := fun q : ℝ × Ω N => s94Rt (X N) (P N) C u q.1 q.2) (f := fun t : ℝ => (t, ζ))
          (s94Rt_measurable hN0 (X N) (hset.measX N) (P N) hCm hu) measurable_prodMk_right
      have hmemR : MemLp (fun t => s94Rt (X N) (P N) C u t ζ) 2 (volume.restrict (Set.Icc (0 : ℝ) T)) :=
        s94_memLp_of_bdd hRmeas (K := Ag) (fun t _ => s94Rt_abs_le hN0 (X N) (P N) hAg t ζ)
      have hB : ∀ t, r2QuadFluct (Whole.withDensityReal ρ) (fun t => r2FiniteRankKernel (C t) u) (P N) (X N) t ζ =
          Qt t - s94mN (Whole.withDensityReal ρ) (X N) (P N) (s94coef C) (fun q => u q.1) (fun q => u q.2) t -
            s94Rt (X N) (P N) C u t ζ := fun t => by
        rw [hQt]
        exact s94_quad_decomp hN0 hCs hu (P N) (X N) (hset.measX N) t ζ
      have hBpath : r2L2Path T (fun t => r2QuadFluct (Whole.withDensityReal ρ) (fun t => r2FiniteRankKernel (C t) u)
          (P N) (X N) t ζ) = r2L2Path T Qt - r2L2Path T (s94mN (Whole.withDensityReal ρ) (X N) (P N) (s94coef C)
            (fun q => u q.1) (fun q => u q.2)) - r2L2Path T (fun t => s94Rt (X N) (P N) C u t ζ) := by
        have : (fun t => r2QuadFluct (Whole.withDensityReal ρ) (fun t => r2FiniteRankKernel (C t) u)
            (P N) (X N) t ζ) = fun t => (Qt t - s94mN (Whole.withDensityReal ρ) (X N) (P N) (s94coef C)
              (fun q => u q.1) (fun q => u q.2) t) - s94Rt (X N) (P N) C u t ζ := funext hB
        rw [this, s94_r2L2Path_sub hmemQ hmemm]
        exact (s94_r2L2Path_sub (hmemQ.sub hmemm) hmemR).symm
      have hΔ : s94Psi C (fun a => r2ContPath T (r2EmpFluct (Whole.withDensityReal ρ) (u a) (X N) ζ)) -
          r2L2Path T (s94mL ξ P' (s94coef C) (fun q => u q.1) (fun q => u q.2)) -
          r2L2Path T (fun t => r2QuadFluct (Whole.withDensityReal ρ) (fun t => r2FiniteRankKernel (C t) u)
            (P N) (X N) t ζ) =
          (r2L2Path T (s94mN (Whole.withDensityReal ρ) (X N) (P N) (s94coef C) (fun q => u q.1) (fun q => u q.2)) -
            r2L2Path T (s94mL ξ P' (s94coef C) (fun q => u q.1) (fun q => u q.2))) +
          r2L2Path T (fun t => s94Rt (X N) (P N) C u t ζ) := by
        rw [hΨ, hBpath]; abel
      rw [hΔ]
      set a1 := dist (r2L2Path T (s94mN (Whole.withDensityReal ρ) (X N) (P N) (s94coef C)
          (fun q => u q.1) (fun q => u q.2))) (r2L2Path T (s94mL ξ P' (s94coef C) (fun q => u q.1)
          (fun q => u q.2))) with ha1
      set a2 := ‖r2L2Path T (fun t => s94Rt (X N) (P N) C u t ζ)‖ with ha2
      have hn : ‖(r2L2Path T (s94mN (Whole.withDensityReal ρ) (X N) (P N) (s94coef C) (fun q => u q.1) (fun q => u q.2)) -
            r2L2Path T (s94mL ξ P' (s94coef C) (fun q => u q.1) (fun q => u q.2))) +
          r2L2Path T (fun t => s94Rt (X N) (P N) C u t ζ)‖ ≤ a1 + a2 :=
        (norm_add_le _ _).trans (by rw [ha1, dist_eq_norm])
      have hsq : ‖(r2L2Path T (s94mN (Whole.withDensityReal ρ) (X N) (P N) (s94coef C) (fun q => u q.1) (fun q => u q.2)) -
            r2L2Path T (s94mL ξ P' (s94coef C) (fun q => u q.1) (fun q => u q.2))) +
          r2L2Path T (fun t => s94Rt (X N) (P N) C u t ζ)‖ ^ 2 ≤ 2 * a1 ^ 2 + 2 * a2 ^ 2 := by
        have h0 : 0 ≤ ‖(r2L2Path T (s94mN (Whole.withDensityReal ρ) (X N) (P N) (s94coef C) (fun q => u q.1) (fun q => u q.2)) -
            r2L2Path T (s94mL ξ P' (s94coef C) (fun q => u q.1) (fun q => u q.2))) +
          r2L2Path T (fun t => s94Rt (X N) (P N) C u t ζ)‖ := norm_nonneg _
        nlinarith [sq_nonneg (a1 - a2), pow_le_pow_left₀ h0 hn 2]
      have hR2 : ENNReal.ofReal (a2 ^ 2) = ∫⁻ t in Set.Icc (0 : ℝ) T, ENNReal.ofReal ((s94Rt (X N) (P N) C u t ζ) ^ 2) ∂volume := by
        rw [ha2, s94_norm_r2L2Path_sq hmemR,
          ofReal_integral_eq_lintegral_ofReal hmemR.integrable_sq (ae_of_all _ fun t => sq_nonneg _)]
      rw [← ofReal_norm_eq_enorm, ← ENNReal.ofReal_pow (norm_nonneg _)]
      calc ENNReal.ofReal (‖(r2L2Path T (s94mN (Whole.withDensityReal ρ) (X N) (P N) (s94coef C) (fun q => u q.1) (fun q => u q.2)) -
            r2L2Path T (s94mL ξ P' (s94coef C) (fun q => u q.1) (fun q => u q.2))) +
          r2L2Path T (fun t => s94Rt (X N) (P N) C u t ζ)‖ ^ 2) ≤ ENNReal.ofReal (2 * a1 ^ 2 + 2 * a2 ^ 2) :=
            ENNReal.ofReal_le_ofReal hsq
        _ = ENNReal.ofReal (2 * a1 ^ 2) + 2 * ENNReal.ofReal (a2 ^ 2) := by
            rw [ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
            simp
        _ = _ := by rw [hR2]
    calc ∫⁻ ζ, ‖s94Psi C (fun a => r2ContPath T (r2EmpFluct (Whole.withDensityReal ρ) (u a) (X N) ζ)) -
          r2L2Path T (s94mL ξ P' (s94coef C) (fun q => u q.1) (fun q => u q.2)) -
          r2L2Path T (fun t => r2QuadFluct (Whole.withDensityReal ρ) (fun t => r2FiniteRankKernel (C t) u)
            (P N) (X N) t ζ)‖ₑ ^ 2 ∂(P N)
        ≤ ∫⁻ ζ, (ENNReal.ofReal (2 * (dist (r2L2Path T (s94mN (Whole.withDensityReal ρ) (X N) (P N) (s94coef C)
          (fun q => u q.1) (fun q => u q.2))) (r2L2Path T (s94mL ξ P' (s94coef C) (fun q => u q.1)
          (fun q => u q.2)))) ^ 2) + 2 * ∫⁻ t in Set.Icc (0 : ℝ) T,
            ENNReal.ofReal ((s94Rt (X N) (P N) C u t ζ) ^ 2) ∂volume) ∂(P N) := lintegral_mono_ae hpt
      _ = ENNReal.ofReal (2 * (dist (r2L2Path T (s94mN (Whole.withDensityReal ρ) (X N) (P N) (s94coef C)
          (fun q => u q.1) (fun q => u q.2))) (r2L2Path T (s94mL ξ P' (s94coef C) (fun q => u q.1)
          (fun q => u q.2)))) ^ 2) + 2 * ∫⁻ ζ, ∫⁻ t in Set.Icc (0 : ℝ) T,
            ENNReal.ofReal ((s94Rt (X N) (P N) C u t ζ) ^ 2) ∂volume ∂(P N) := by
          have hmeas : Measurable fun ζ => ∫⁻ t in Set.Icc (0 : ℝ) T,
              ENNReal.ofReal ((s94Rt (X N) (P N) C u t ζ) ^ 2) ∂volume := by
            have hRm := s94Rt_measurable hN0 (X N) (hset.measX N) (P N) hCm hu
            have hF : Measurable fun q : Ω N × ℝ => ENNReal.ofReal ((s94Rt (X N) (P N) C u q.2 q.1) ^ 2) :=
              ENNReal.measurable_ofReal.comp (((hRm.comp measurable_swap).pow_const 2))
            exact hF.lintegral_prod_right'  (ν := volume.restrict (Set.Icc (0 : ℝ) T))
          rw [lintegral_add_left measurable_const, lintegral_const_mul' _ _ (by simp), lintegral_const]
          simp
      _ ≤ _ := by
          have h1 := hKr N hN
          have hNr : (0 : ℝ) < N := by exact_mod_cast hN0
          have h2 : ENNReal.ofReal (Kr / N) ≤ ENNReal.ofReal (|Kr| / N) :=
            ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right (le_abs_self _) hNr.le)
          have h3 : ∫⁻ ζ, ∫⁻ t in Set.Icc (0 : ℝ) T, ENNReal.ofReal ((s94Rt (X N) (P N) C u t ζ) ^ 2) ∂volume ∂(P N)
              ≤ ENNReal.ofReal (|Kr| / N) := h1.trans h2
          rw [ENNReal.ofReal_add (by positivity) (by positivity)]
          refine add_le_add le_rfl ?_
          rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
          have h4 : (2 : ℝ≥0∞) * ∫⁻ ζ, ∫⁻ t in Set.Icc (0 : ℝ) T, ENNReal.ofReal ((s94Rt (X N) (P N) C u t ζ) ^ 2) ∂volume ∂(P N)
              ≤ 2 * ENNReal.ofReal (|Kr| / N) := mul_le_mul_right h3 2
          simpa using h4

theorem s94Flim_measurable {n : ℕ} (hξ : ∀ a, Measurable (ξ a)) (P0 : Measure Ω') [IsProbabilityMeasure P0]
    {C : ℝ → Fin n → Fin n → ℝ} (hCm : ∀ a b, Measurable fun t => C t a b) (u : Fin n → Euc d → ℝ) :
    Measurable fun q : ℝ × Ω' => s94Flim ξ P0 C u q.1 q.2 := by
  unfold s94Flim
  refine Finset.measurable_sum _ fun p _ => ?_
  have hj : ∀ a, Measurable fun q : ℝ × Ω' => r2PathEval T (ξ a q.2) q.1 := fun a =>
    Measurable.comp (g := fun q : C(Set.Icc (0 : ℝ) T, ℝ) × ℝ => r2PathEval T q.1 q.2)
      (f := fun q : ℝ × Ω' => (ξ a q.2, q.1)) s94_pathEval_joint_measurable
      (((hξ a).comp measurable_snd).prodMk measurable_fst)
  have h1 : Measurable fun q : ℝ × Ω' => r2PathEval T (ξ (u p.1) q.2) q.1 * r2PathEval T (ξ (u p.2) q.2) q.1 :=
    (hj _).mul (hj _)
  have h2 : Measurable fun t : ℝ => ∫ ζ', r2PathEval T (ξ (u p.1) ζ') t * r2PathEval T (ξ (u p.2) ζ') t ∂P0 :=
    (h1.stronglyMeasurable.integral_prod_right' (ν := P0)).measurable
  exact (((hCm p.1 p.2).comp measurable_fst).const_mul _).mul (h1.sub (h2.comp measurable_fst))

end Flat

end HRS.MS.R2Chaos
