import HRS.MS.Fp81S21WindowFeature7
import HRS.MS.CovMeasAux1
import HRS.MS.GoFeatAux5

/-!
# S2.1 packet 15c: positive-order bounds for `ℓ²` features

This helper keeps separate square-summable envelopes for values and positive
spatial derivatives.  It is needed because moving-orbit decay controls the
gradient, while the zeroth-order feature uses the ordinary S101 envelope.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Fp81.S21

open HRS (Euc)
open HRS.Whole HRS.MS.CovMeas HRS.MS.Go

variable {d : ℕ}

/-- An `ℓ²`-valued feature is smooth under one envelope and has sharper
positive-order derivatives under another envelope. -/
theorem fp81s21_ell2_contDiff_pos
    {m : ℝ} (k : ℕ)
    (g : MultiIndex d → Euc d → ℝ)
    (c0 cpos : MultiIndex d → ℝ)
    (hc0 : Summable fun α => c0 α ^ 2)
    (hcpos : Summable fun α => cpos α ^ 2)
    (hg : ∀ α, ContDiff ℝ ((k : ℕ) : WithTop ℕ∞) (g α))
    (hfull : ∀ α, ∀ j ≤ k, ∀ x,
      ‖iteratedFDeriv ℝ j (g α) x‖ ≤ c0 α)
    (hpos : ∀ α, ∀ j ≤ k, 1 ≤ j → ∀ x,
      ‖iteratedFDeriv ℝ j (g α) x‖ ≤ cpos α) :
    ContDiff ℝ ((k : ℕ) : WithTop ℕ∞)
      (fun x => ellVec (d := d) m (fun α => g α x)) ∧
    ∀ j ≤ k, 1 ≤ j → ∀ x,
      ‖iteratedFDeriv ℝ j
        (fun x => ellVec (d := d) m (fun α => g α x)) x‖ ≤
          Real.sqrt (∑' α, cpos α ^ 2) := by
  have hregular := s101_ell2_contDiff (d := d) (m := m) k g c0 hc0 hg hfull
  by_cases hk : 1 ≤ k
  · have h0 : ∀ α x, |g α x| ≤ c0 α := by
      intro α x
      have h := hfull α 0 (Nat.zero_le _) x
      simpa [norm_iteratedFDeriv_zero, Real.norm_eq_abs] using h
    have hg1 : ∀ α, ContDiff ℝ 1 (g α) := by
      intro α
      exact (hg α).of_le (by exact_mod_cast hk)
    have hb1full : ∀ α x, ‖fderiv ℝ (g α) x‖ ≤ c0 α := by
      intro α x
      have h := hfull α 1 (by exact_mod_cast hk) x
      rwa [norm_iteratedFDeriv_one] at h
    let Θ : Euc d → (Euc d →L[ℝ] OscDual d m) := fun x =>
      s101EllCLM m (fun α => fderiv ℝ (g α) x) c0 hc0
        (fun α => hb1full α x)
    have hder : ∀ x,
        HasFDerivAt (fun y => ellVec (d := d) m (fun α => g α y)) (Θ x) x := by
      intro x
      exact s101_ell_hasFDerivAt g c0 hc0 hg1 h0 hb1full x
    have hThetaSlice : ∀ h : Euc d,
        ContDiff ℝ ((k - 1 : ℕ) : WithTop ℕ∞) (fun x => Θ x h) ∧
        ∀ j ≤ k - 1, ∀ x,
          ‖iteratedFDeriv ℝ j (fun x => Θ x h) x‖ ≤
            Real.sqrt (∑' α, cpos α ^ 2) * ‖h‖ := by
      intro h
      have hfdg : ∀ α, ContDiff ℝ ((k - 1 : ℕ) : WithTop ℕ∞)
          (fderiv ℝ (g α)) := by
        intro α
        have hfd := (hg α).fderiv_right
          (m := ((k - 1 : ℕ) : WithTop ℕ∞)) (by
            have hnat : k - 1 + 1 ≤ k := by omega
            exact_mod_cast hnat)
        exact hfd
      have hgh : ∀ α, ContDiff ℝ ((k - 1 : ℕ) : WithTop ℕ∞)
          (fun x => fderiv ℝ (g α) x h) := by
        intro α
        exact (hfdg α).clm_apply contDiff_const
      have hbh : ∀ α, ∀ j ≤ k - 1, ∀ x,
          ‖iteratedFDeriv ℝ j (fun x => fderiv ℝ (g α) x h) x‖ ≤
            cpos α * ‖h‖ := by
        intro α j hj x
        have h1 := norm_iteratedFDeriv_clm_apply_const (𝕜 := ℝ)
          (f := fderiv ℝ (g α)) (c := h) (x := x)
          (N := ((k - 1 : ℕ) : WithTop ℕ∞)) (n := j)
          (hfdg α).contDiffAt
          (by exact_mod_cast hj)
        rw [norm_iteratedFDeriv_fderiv] at h1
        have hjk : j + 1 ≤ k := by omega
        calc
          _ ≤ ‖h‖ * ‖iteratedFDeriv ℝ (j + 1) (g α) x‖ := h1
          _ ≤ ‖h‖ * cpos α :=
            mul_le_mul_of_nonneg_left (hpos α (j + 1) hjk (by omega) x)
              (norm_nonneg _)
          _ = cpos α * ‖h‖ := by ring
      have hscaled : Summable fun α => (cpos α * ‖h‖) ^ 2 :=
        s101_summable_mul hcpos ‖h‖
      have hEll := s101_ell2_contDiff (d := d) (m := m) (k - 1)
        (fun α x => fderiv ℝ (g α) x h) (fun α => cpos α * ‖h‖)
        hscaled hgh hbh
      have heq : (fun x => Θ x h) = fun x =>
          ellVec (d := d) m (fun α => fderiv ℝ (g α) x h) := by
        funext x
        rw [s101EllCLM_apply]
      rw [heq]
      refine ⟨hEll.1, fun j hj x => ?_⟩
      have hmul := hEll.2 j hj x
      rw [s101_sqrt_tsum_mul] at hmul
      simpa [abs_of_nonneg (norm_nonneg h)] using hmul
    have hTheta : ContDiff ℝ ((k - 1 : ℕ) : WithTop ℕ∞) Θ :=
      contDiff_clm_apply_iff.2 fun h => (hThetaSlice h).1
    refine ⟨hregular.1, ?_⟩
    intro j hj hj1 x
    obtain ⟨n, rfl⟩ : ∃ n, j = n + 1 := ⟨j - 1, by omega⟩
    have hn : n ≤ k - 1 := by omega
    have hfd : fderiv ℝ
        (fun y => ellVec (d := d) m (fun α => g α y)) = Θ :=
      funext fun y => (hder y).fderiv
    rw [← norm_iteratedFDeriv_fderiv (𝕜 := ℝ)
      (f := fun y => ellVec (d := d) m (fun α => g α y)) (x := x) (n := n), hfd]
    refine ContinuousMultilinearMap.opNorm_le_bound (Real.sqrt_nonneg _) fun mm => ?_
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun h => ?_
    have hcomp := (ContinuousLinearMap.apply ℝ (OscDual d m) h).iteratedFDeriv_comp_left
      (hTheta.contDiffAt (x := x)) (i := n) (by exact_mod_cast hn)
    have heq : (ContinuousLinearMap.apply ℝ (OscDual d m) h ∘ Θ) =
        fun y => Θ y h := rfl
    rw [heq] at hcomp
    have heval : (iteratedFDeriv ℝ n Θ x mm) h =
        iteratedFDeriv ℝ n (fun y => Θ y h) x mm := by
      rw [hcomp]
      rfl
    rw [heval]
    have hmult := (iteratedFDeriv ℝ n (fun y => Θ y h) x).le_opNorm mm
    have hslice := (hThetaSlice h).2 n hn x
    calc
      ‖iteratedFDeriv ℝ n (fun y => Θ y h) x mm‖ ≤
          ‖iteratedFDeriv ℝ n (fun y => Θ y h) x‖ * ∏ i, ‖mm i‖ := hmult
      _ ≤ (Real.sqrt (∑' α, cpos α ^ 2) * ‖h‖) * ∏ i, ‖mm i‖ :=
        mul_le_mul_of_nonneg_right hslice (by positivity)
      _ = (Real.sqrt (∑' α, cpos α ^ 2) * ∏ i, ‖mm i‖) * ‖h‖ := by ring
  · have hk0 : k = 0 := by omega
    subst k
    exact ⟨hregular.1, by intro j hj hj1; omega⟩

/-- The `L²`-valued feature retains its full regularity from the value
envelope, while its positive derivatives use the sharper envelope. -/
theorem fp81s21_L2_contDiff_pos
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
    {μ : Measure ℝ} [IsFiniteMeasure μ]
    (hd : 1 ≤ d) (k : ℕ) (F : ℝ → Euc d → G) (B0 Bpos : ℝ)
    (hB0 : 0 ≤ B0) (hBpos : 0 ≤ Bpos)
    (hF : ∀ t, ContDiff ℝ ((k : ℕ) : WithTop ℕ∞) (F t))
    (hfull : ∀ t x, ‖F t x‖ ≤ B0)
    (hpos : ∀ t, ∀ j ≤ k, 1 ≤ j → ∀ x,
      ‖iteratedFDeriv ℝ j (F t) x‖ ≤ Bpos)
    (hmeas : ∀ x, AEStronglyMeasurable (fun t => F t x) μ)
    (hmem : ∀ x, MemLp (fun t => F t x) 2 μ) :
    ContDiff ℝ ((k : ℕ) : WithTop ℕ∞)
      (fun x => (hmem x).toLp (fun t => F t x)) ∧
    ∀ j ≤ k, 1 ≤ j → ∀ x,
      ‖iteratedFDeriv ℝ j
        (fun x => (hmem x).toLp (fun t => F t x)) x‖ ≤
          (d : ℝ) ^ j * (Bpos * (μ Set.univ).toReal ^ (1 / 2 : ℝ)) := by
  revert F B0 Bpos hB0 hBpos hF hfull hpos hmeas hmem
  induction k with
  | zero =>
      intro F B0 Bpos hB0 hBpos hF hfull hpos hmeas hmem
      have hbase := s55f_L2_contDiff (μ := μ) (d := d) (G := G) hd 0 F B0
        hF (fun t j hj x => by
          have hj0 : j = 0 := by omega
          subst j
          simpa [norm_iteratedFDeriv_zero] using hfull t x) hmeas hmem
      refine ⟨hbase.1, ?_⟩
      intro j hj hj1
      omega
  | succ k ih =>
      intro F B0 Bpos hB0 hBpos hF hfull hpos hmeas hmem
      let B : ℝ := max B0 Bpos
      have hB : 0 ≤ B := le_trans hB0 (le_max_left _ _)
      have hF1 : ∀ t, ContDiff ℝ 1 (F t) := by
        intro t
        exact (hF t).of_le (by exact_mod_cast (show 1 ≤ k + 1 from by omega))
      have hdiff : ∀ t, Differentiable ℝ (F t) :=
        fun t => (hF1 t).differentiable one_ne_zero
      have hfdF : ∀ t, ContDiff ℝ ((k : ℕ) : WithTop ℕ∞)
          (fderiv ℝ (F t)) := by
        intro t
        have hfd := (hF t).fderiv_right
          (m := ((k : ℕ) : WithTop ℕ∞)) (by
            have hnat : k + 1 ≤ k + 1 := le_rfl
            exact_mod_cast hnat)
        exact hfd
      have hb0 : ∀ t x, ‖F t x‖ ≤ B := fun t x =>
        (hfull t x).trans (le_max_left _ _)
      have hb1 : ∀ t x, ‖fderiv ℝ (F t) x‖ ≤ B := by
        intro t x
        have hp := hpos t 1 (by omega) (by omega) x
        rw [norm_iteratedFDeriv_one] at hp
        exact hp.trans (le_max_right _ _)
      have hmD : ∀ x h, AEStronglyMeasurable
          (fun t => fderiv ℝ (F t) x h) μ := fun x h =>
        s55f_aesm_fderiv F hdiff hmeas x h
      have hmemD : ∀ x h, MemLp
          (fun t => fderiv ℝ (F t) x h) 2 μ := by
        intro x h
        exact s55f_memLp_of_bound μ (hmD x h) (B := Bpos * ‖h‖) fun t =>
          (ContinuousLinearMap.le_opNorm _ _).trans
          (mul_le_mul_of_nonneg_right (by
            have hp := hpos t 1 (by omega) (by omega) x
            rwa [norm_iteratedFDeriv_one] at hp) (norm_nonneg _))
      let Θl : Euc d → (Euc d →ₗ[ℝ] Lp G 2 μ) := fun x =>
        { toFun := fun h => (hmemD x h).toLp (fun t => fderiv ℝ (F t) x h)
          map_add' := fun h₁ h₂ => by
            rw [← MemLp.toLp_add]
            exact MemLp.toLp_congr _ _ (Eventually.of_forall fun t => by simp)
          map_smul' := fun c h => by
            rw [RingHom.id_apply, ← MemLp.toLp_const_smul]
            exact MemLp.toLp_congr _ _ (Eventually.of_forall fun t => by simp) }
      let Θ : Euc d → (Euc d →L[ℝ] Lp G 2 μ) := fun x =>
        LinearMap.toContinuousLinearMap (Θl x)
      have hΘ : ∀ x h, Θ x h =
          (hmemD x h).toLp (fun t => fderiv ℝ (F t) x h) := fun x h => rfl
      have hder : ∀ x, HasFDerivAt
          (fun x => (hmem x).toLp (fun t => F t x)) (Θ x) x := by
        intro x
        exact s55f_W_hasFDerivAt (μ := μ) F hF1 hb0 hb1 hmeas hmem
          hmemD x (Θ x) (hΘ x)
      have hslice : ∀ h : Euc d,
          ContDiff ℝ ((k : ℕ) : WithTop ℕ∞) (fun x => Θ x h) ∧
          ∀ j ≤ k, ∀ x,
            ‖iteratedFDeriv ℝ j (fun x => Θ x h) x‖ ≤
              (d : ℝ) ^ j * (Bpos * ‖h‖ * (μ Set.univ).toReal ^ (1 / 2 : ℝ)) := by
        intro h
        let Fh : ℝ → Euc d → G := fun t x => fderiv ℝ (F t) x h
        have hFh : ∀ t, ContDiff ℝ ((k : ℕ) : WithTop ℕ∞) (Fh t) := by
          intro t
          exact (hfdF t).clm_apply contDiff_const
        have hboundh : ∀ t x, ‖Fh t x‖ ≤ Bpos * ‖h‖ := by
          intro t x
          exact (ContinuousLinearMap.le_opNorm _ _).trans
            (mul_le_mul_of_nonneg_right (by
              have hp := hpos t 1 (by omega) (by omega) x
              rwa [norm_iteratedFDeriv_one] at hp) (norm_nonneg _))
        have hposh : ∀ t, ∀ j ≤ k, 1 ≤ j → ∀ x,
            ‖iteratedFDeriv ℝ j (Fh t) x‖ ≤ Bpos * ‖h‖ := by
          intro t j hj hj1 x
          have h1 := norm_iteratedFDeriv_clm_apply_const (𝕜 := ℝ)
            (f := fderiv ℝ (F t)) (c := h) (x := x)
            (N := ((k : ℕ) : WithTop ℕ∞)) (n := j)
            (hfdF t).contDiffAt
            (by exact_mod_cast hj)
          rw [norm_iteratedFDeriv_fderiv] at h1
          calc
            _ ≤ ‖h‖ * ‖iteratedFDeriv ℝ (j + 1) (F t) x‖ := h1
            _ ≤ ‖h‖ * Bpos :=
              mul_le_mul_of_nonneg_left (hpos t (j + 1) (by omega) (by omega) x)
                (norm_nonneg _)
            _ = Bpos * ‖h‖ := by ring
        have hmeash : ∀ x, AEStronglyMeasurable (fun t => Fh t x) μ := by
          intro x
          exact s55f_aesm_fderiv F hdiff hmeas x h
        have hmemh : ∀ x, MemLp (fun t => Fh t x) 2 μ := by
          intro x
          exact s55f_memLp_of_bound μ (hmeash x) (B := Bpos * ‖h‖)
            (fun t => hboundh t x)
        have hInd := ih Fh (Bpos * ‖h‖) (Bpos * ‖h‖)
          (mul_nonneg hBpos (norm_nonneg _)) (mul_nonneg hBpos (norm_nonneg _))
          hFh hboundh hposh hmeash hmemh
        have hzero : ∀ x,
            ‖iteratedFDeriv ℝ 0
              (fun x => (hmemh x).toLp (fun t => Fh t x)) x‖ ≤
                Bpos * ‖h‖ * (μ Set.univ).toReal ^ (1 / 2 : ℝ) := by
          intro x
          simp only [norm_iteratedFDeriv_zero]
          exact s55f_norm_toLp_le μ (hmemh x) (fun t => hboundh t x)
        have hderbounds : ∀ j ≤ k, ∀ x,
            ‖iteratedFDeriv ℝ j
              (fun x => (hmemh x).toLp (fun t => Fh t x)) x‖ ≤
                (d : ℝ) ^ j * (Bpos * ‖h‖ * (μ Set.univ).toReal ^ (1 / 2 : ℝ)) := by
          intro j hj x
          by_cases hj0 : j = 0
          · subst j
            simpa using hzero x
          · have hj1 : 1 ≤ j := by omega
            have hi := hInd.2 j hj hj1 x
            convert hi using 1
        have heq : (fun x => Θ x h) =
            fun x => (hmemh x).toLp (fun t => Fh t x) := by
          funext x
          rw [hΘ]
        rw [heq]
        exact ⟨hInd.1, hderbounds⟩
      have hTheta : ContDiff ℝ ((k : ℕ) : WithTop ℕ∞) Θ :=
        contDiff_clm_apply_iff.2 fun h => (hslice h).1
      have hreg : ContDiff ℝ ((k + 1 : ℕ) : WithTop ℕ∞)
          (fun x => (hmem x).toLp (fun t => F t x)) :=
        contDiff_succ_iff_hasFDerivAt.2 ⟨Θ, hTheta, hder⟩
      refine ⟨hreg, ?_⟩
      intro j hj hj1 x
      obtain ⟨n, rfl⟩ : ∃ n, j = n + 1 := ⟨j - 1, by omega⟩
      have hn : n ≤ k := by omega
      have hfd : fderiv ℝ (fun x => (hmem x).toLp (fun t => F t x)) = Θ :=
        funext fun y => (hder y).fderiv
      rw [← norm_iteratedFDeriv_fderiv (𝕜 := ℝ)
        (f := fun x => (hmem x).toLp (fun t => F t x)) (x := x) (n := n), hfd]
      have hbd : ‖iteratedFDeriv ℝ n Θ x‖ ≤
          (d : ℝ) ^ n * (Bpos * (μ Set.univ).toReal ^ (1 / 2 : ℝ)) := by
        refine ContinuousMultilinearMap.opNorm_le_bound (by positivity) fun m => ?_
        refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun h => ?_
        have hcomp := (ContinuousLinearMap.apply ℝ (Lp G 2 μ) h).iteratedFDeriv_comp_left
          (hTheta.contDiffAt (x := x)) (i := n) (by exact_mod_cast hn)
        have heq : (ContinuousLinearMap.apply ℝ (Lp G 2 μ) h ∘ Θ) = fun y => Θ y h := rfl
        rw [heq] at hcomp
        have heval : (iteratedFDeriv ℝ n Θ x m) h =
            iteratedFDeriv ℝ n (fun y => Θ y h) x m := by rw [hcomp]; rfl
        rw [heval]
        have hmult := (iteratedFDeriv ℝ n (fun y => Θ y h) x).le_opNorm m
        have hslice' := (hslice h).2 n hn x
        calc
          ‖iteratedFDeriv ℝ n (fun y => Θ y h) x m‖ ≤
              ‖iteratedFDeriv ℝ n (fun y => Θ y h) x‖ * ∏ i, ‖m i‖ := hmult
          _ ≤ ((d : ℝ) ^ n *
                (Bpos * ‖h‖ * (μ Set.univ).toReal ^ (1 / 2 : ℝ))) * ∏ i, ‖m i‖ :=
            mul_le_mul_of_nonneg_right hslice' (by positivity)
          _ = (((d : ℝ) ^ n * (Bpos * (μ Set.univ).toReal ^ (1 / 2 : ℝ))) *
                ∏ i, ‖m i‖) * ‖h‖ := by ring
      have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
      have hpow : (d : ℝ) ^ n ≤ (d : ℝ) ^ (n + 1) :=
        pow_le_pow_right₀ hd1 (Nat.le_succ n)
      exact hbd.trans (mul_le_mul_of_nonneg_right hpow (by positivity))

#print axioms fp81s21_ell2_contDiff_pos
#print axioms fp81s21_L2_contDiff_pos

end HRS.Fp81.S21

end
