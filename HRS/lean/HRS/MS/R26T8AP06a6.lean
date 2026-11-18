import HRS.MS.R26T8AP06a5
import HRS.MS.R26T8ASym

/-!
# S8.2 P06a (6): the limit jets `T_j`
`r26t8a_p06_T`: for `j < k`, `j < -sigma`, the jet `D^j h` has a symmetric limit `T` at `0` with
`‖T‖ <= C A` and `‖D^j h(z) - T‖ <= C A |z|^a (1+|log|z||)^b`, `a = min(-(sigma+j), 1)`.
-/

set_option autoImplicit false
noncomputable section
open Real Filter Topology

namespace HRS.MS.R26T8A
open HRS

theorem r26t8a_p06_T (d : ℕ) (hd : 2 ≤ d) (b k : ℕ) (σ : ℝ) (j : ℕ) (hjk : j < k) (hjσ : (j : ℝ) < -σ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ A : ℝ, 0 ≤ A → ∀ h : Euc d → ℝ, ContDiffOn ℝ k h {z | z ≠ 0} →
      (∀ i ≤ k, ∀ z : Euc d, 0 < ‖z‖ → ‖z‖ ≤ 1 →
        ‖iteratedFDeriv ℝ i h z‖ ≤ A * r26t8a_jetEnvelope b (σ + i) ‖z‖) →
      ∃ T : ContinuousMultilinearMap ℝ (fun _ : Fin j => Euc d) ℝ, ‖T‖ ≤ C * A ∧
        (∀ (τ : Equiv.Perm (Fin j)) (v : Fin j → Euc d), T (v ∘ τ) = T v) ∧
        ∀ z : Euc d, 0 < ‖z‖ → ‖z‖ ≤ 1 / 2 →
          ‖iteratedFDeriv ℝ j h z - T‖ ≤
            C * A * (‖z‖ ^ (min (-(σ + j)) 1) * (1 + |Real.log ‖z‖|) ^ b) := by
  set a : ℝ := min (-(σ + j)) 1 with ha_def
  have ha : 0 < a := lt_min (by linarith) one_pos
  set B' : ℝ := 2 + |r26t8a_p06_M (-(σ + j + 1)) b| with hB'
  have hB'0 : 0 ≤ B' := by rw [hB']; positivity
  set K := r26t8a_p06_K a b with hK
  have hK0 : 0 ≤ K := r26t8a_p06_K_nonneg a b
  set C1 : ℝ := 2 ^ (b + 2) * 2 ^ |a - 1| * B' + 2 * B' * K with hC1
  have hC10 : 0 ≤ C1 := by rw [hC1]; positivity
  set L12 : ℝ := (1 + |Real.log ((1:ℝ) / 2)|) ^ b with hL12
  have hL120 : 0 ≤ L12 := by rw [hL12]; positivity
  set C2 : ℝ := 1 + ((1:ℝ) / 2) ^ (-(σ + j)) * L12 + C1 * (((1:ℝ) / 2) ^ a * L12) with hC2
  have hC20 : 0 ≤ C2 := by rw [hC2]; positivity
  refine ⟨C1 + C2, add_nonneg hC10 hC20, ?_⟩
  intro A hA h hcont hjet
  have hcd : ∀ y : Euc d, y ≠ 0 → ContDiffAt ℝ (k : WithTop ℕ∞) h y := fun y hy =>
    hcont.contDiffAt (isOpen_ne.mem_nhds hy)
  set G : Euc d → ContinuousMultilinearMap ℝ (fun _ : Fin j => Euc d) ℝ := iteratedFDeriv ℝ j h with hG
  have hdiff : ∀ y : Euc d, 0 < ‖y‖ → ‖y‖ ≤ 1 / 2 → DifferentiableAt ℝ G y := fun y hy _ =>
    (hcd y (norm_pos_iff.1 hy)).differentiableAt_iteratedFDeriv (by exact_mod_cast hjk)
  have hder : ∀ y : Euc d, 0 < ‖y‖ → ‖y‖ ≤ 1 / 2 →
      ‖fderiv ℝ G y‖ ≤ (B' * A) * ‖y‖ ^ (a - 1) * (1 + |Real.log ‖y‖|) ^ b := by
    intro y hy hy2
    rw [hG, norm_fderiv_iteratedFDeriv]
    have h1 := hjet (j + 1) (by omega) y hy (by linarith)
    have h2 := r26t8a_p06_env_step b σ j hjσ hy (by linarith : ‖y‖ ≤ 1)
    calc ‖iteratedFDeriv ℝ (j + 1) h y‖ ≤ A * r26t8a_jetEnvelope b (σ + ((j + 1 : ℕ) : ℝ)) ‖y‖ := h1
      _ ≤ A * (B' * (‖y‖ ^ (a - 1) * (1 + |Real.log ‖y‖|) ^ b)) := mul_le_mul_of_nonneg_left h2 hA
      _ = _ := by ring
  obtain ⟨T, hT⟩ := r26t8a_p06_limit hd G ha b (B' * A) (by positivity) hdiff hder
  have hrate : ∀ z : Euc d, 0 < ‖z‖ → ‖z‖ ≤ 1 / 2 →
      ‖G z - T‖ ≤ C1 * A * (‖z‖ ^ a * (1 + |Real.log ‖z‖|) ^ b) := by
    intro z hz hz2
    refine (hT z hz hz2).trans (le_of_eq ?_)
    rw [hC1]; ring
  set z0 : Euc d := (1 / 2 : ℝ) • EuclideanSpace.single (⟨0, by omega⟩ : Fin d) (1 : ℝ) with hz0
  have hz0n : ‖z0‖ = 1 / 2 := by rw [hz0, norm_smul]; simp
  refine ⟨T, ?_, ?_, fun z hz hz2 => ?_⟩
  · -- norm bound
    have h1 := hjet j hjk.le z0 (by rw [hz0n]; norm_num) (by rw [hz0n]; norm_num)
    rw [hz0n, r26t8a_p06_env_eq b _ (by norm_num) (by norm_num)] at h1
    have h2 := hrate z0 (by rw [hz0n]; norm_num) hz0n.le
    rw [hz0n] at h2
    have h3 : ‖T‖ ≤ ‖G z0‖ + ‖G z0 - T‖ := by
      calc ‖T‖ = ‖G z0 - (G z0 - T)‖ := by congr 1; abel
        _ ≤ ‖G z0‖ + ‖G z0 - T‖ := norm_sub_le _ _
    have h4 : ‖G z0‖ ≤ A * (1 + ((1:ℝ) / 2) ^ (-(σ + j)) * L12) := h1
    calc ‖T‖ ≤ A * (1 + ((1:ℝ) / 2) ^ (-(σ + j)) * L12) + C1 * A * (((1:ℝ) / 2) ^ a * L12) := by
          linarith
      _ = C2 * A := by rw [hC2]; ring
      _ ≤ (C1 + C2) * A := by nlinarith
  · -- symmetry
    intro τ v
    set P : ℝ := ∏ i, ‖v i‖ with hP
    have hP0 : 0 ≤ P := Finset.prod_nonneg fun i _ => norm_nonneg _
    have hbd : ∀ N : ℕ, |T (v ∘ τ) - T v| ≤
        2 * (C1 * A * (((((1:ℝ) / 2) ^ (N + 1)) ^ a * (1 + |Real.log (((1:ℝ) / 2) ^ (N + 1))|) ^ b))) * P := by
      intro N
      set u : Euc d := (((1:ℝ) / 2) ^ N) • z0 with hu
      have hun : ‖u‖ = ((1:ℝ) / 2) ^ (N + 1) := by
        rw [hu, norm_smul, hz0n, Real.norm_of_nonneg (by positivity)]; rw [pow_succ]
      have hu0 : 0 < ‖u‖ := by rw [hun]; positivity
      have hu2 : ‖u‖ ≤ 1 / 2 := by
        rw [hun]
        calc ((1:ℝ) / 2) ^ (N + 1) ≤ ((1:ℝ) / 2) ^ 1 :=
              pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
          _ = 1 / 2 := by norm_num
      have hsy := r26t8a_iter_symm (Euc d) j h u
        ((hcd u (norm_pos_iff.1 hu0)).of_le (by exact_mod_cast hjk.le)) τ v
      have hr := hrate u hu0 hu2
      rw [hun] at hr
      have e1 : T (v ∘ τ) - T v = (T - G u) (v ∘ τ) - (T - G u) v := by
        have : G u (v ∘ τ) = G u v := hsy
        simp only [ContinuousMultilinearMap.sub_apply]
        rw [this]; ring
      have e2 : ‖T - G u‖ ≤ C1 * A * (((((1:ℝ) / 2) ^ (N + 1)) ^ a *
          (1 + |Real.log (((1:ℝ) / 2) ^ (N + 1))|) ^ b)) := by
        rw [norm_sub_rev]; exact hr
      have e3 : ∀ w : Fin j → Euc d, |(T - G u) w| ≤ ‖T - G u‖ * ∏ i, ‖w i‖ := fun w =>
        (le_of_eq (Real.norm_eq_abs _).symm).trans ((T - G u).le_opNorm w)
      have e4 : ∏ i, ‖(v ∘ τ) i‖ = P := by
        rw [hP]; exact Equiv.prod_comp τ (fun i => ‖v i‖)
      rw [e1]
      calc |(T - G u) (v ∘ τ) - (T - G u) v| ≤ |(T - G u) (v ∘ τ)| + |(T - G u) v| := abs_sub _ _
        _ ≤ ‖T - G u‖ * P + ‖T - G u‖ * P := by
            refine add_le_add ?_ ?_
            · have := e3 (v ∘ τ); rwa [e4] at this
            · exact e3 v
        _ ≤ _ := by
            have : 0 ≤ P := hP0
            nlinarith [mul_le_mul_of_nonneg_right e2 this]
    have hlim : Tendsto (fun N : ℕ => 2 * (C1 * A * (((((1:ℝ) / 2) ^ (N + 1)) ^ a *
        (1 + |Real.log (((1:ℝ) / 2) ^ (N + 1))|) ^ b))) * P) atTop (𝓝 0) := by
      have := ((r26t8a_p06_decay b ha).const_mul (C1 * A)).const_mul 2 |>.mul_const P
      simpa using this
    have : |T (v ∘ τ) - T v| ≤ 0 := ge_of_tendsto' hlim hbd
    have h0 : T (v ∘ τ) - T v = 0 := abs_nonpos_iff.1 this
    linarith
  · -- rate
    have := hrate z hz hz2
    refine this.trans ?_
    have hf : 0 ≤ ‖z‖ ^ a * (1 + |Real.log ‖z‖|) ^ b := by positivity
    have hCA : C1 * A ≤ (C1 + C2) * A := by nlinarith
    exact mul_le_mul_of_nonneg_right hCA hf

end HRS.MS.R26T8A
