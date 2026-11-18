import HRS.MS.R2WinOrbTRD8

/-!
# S10.3 packet [D], part 3: the generator is bounded by `(1+‖x‖)` times the `C²` jets, and uniform `C^k` limits of classical adjoint solutions

Prefix `s103c_`, namespace `HRS.MS.R2WinOrbNL`.

* `s103c_gen_le`: `|L_τ e(x)| ≤ K (1+A_ρ) B (1+‖x‖)` for `e ∈ C²` with first and second derivatives bounded by `B` and `ρ_τ ∈ U2Dec 1 L A_ρ`.
* `s103c_limit_solution`: a sequence of classical adjoint solutions on `[0,t]` that is uniformly Cauchy in all jets up to order `k ≥ 2`, uniformly bounded, has a
  classical adjoint limit `u` (terminal datum `u t = lim w_n t`) and `w_n → u` uniformly in `r ∈ [0,t]` in all jets up to order `k`.
-/

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory Metric
open scoped ENNReal NNReal BigOperators ContDiff RealInnerProductSpace

namespace HRS.MS.R2WinOrbNL

open HRS HRS.Whole HRS.MS.Wad HRS.MS.Ul HRS.MS.Who HRS.MS.BreakdownS67 HRS.MS.MovLin

variable {d : ℕ}

theorem s103c_gen_le {s : ℝ} (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (a β : ℝ) {L : ℝ}
    (hL : (d : ℝ) + ((0 : ℕ) : ℝ) + s + 3 < L) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (ρ : ℝ → Euc d → ℝ) (Ah τ : ℝ), 0 ≤ Ah → U2Dec (0 + 1) L Ah (ρ τ) →
      ∀ (e : Euc d → ℝ) (B : ℝ), ContDiff ℝ ((0 + 2 : ℕ) : WithTop ℕ∞) e →
        (∀ i, 1 ≤ i → i ≤ 2 → ∀ y, ‖iteratedFDeriv ℝ i e y‖ ≤ B) → ∀ x : Euc d,
        |generatorW ((quadraticGradientDyn d s a β).coeff ρ) τ e x| ≤ K * (1 + Ah) * B * (1 + ‖x‖) := by
  obtain ⟨Cq, hCq0, hCq⟩ := s103b_q_sy hd hs0 hsd 0 hL
  refine ⟨|β⁻¹| * d + |a| + Cq, by positivity, ?_⟩
  intro ρ Ah τ hAh hU e B he hb x
  have hB : 0 ≤ B := by
    have := hb 1 le_rfl (by norm_num) 0
    exact (norm_nonneg _).trans this
  have hB1 : ∀ y, ‖fderiv ℝ e y‖ ≤ B := fun y => by
    have := hb 1 le_rfl (by norm_num) y
    rwa [norm_iteratedFDeriv_one] at this
  have hB2 : ∀ y, ‖fderiv ℝ (fderiv ℝ e) y‖ ≤ B := fun y => by
    have := hb 2 (by norm_num) le_rfl y
    rwa [← norm_iteratedFDeriv_fderiv (n := 1), norm_iteratedFDeriv_one] at this
  rw [s103b_gen_split]
  have h1 := s83_L0_bound hB1 hB2 a β⁻¹ x
  have h2 := (hCq Ah (ρ τ) hAh hU B e he hb).2 0 le_rfl x
  rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at h2
  have hw : (1 + ‖x‖)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith [norm_nonneg x])
  have hw1 : 1 ≤ 1 + ‖x‖ := by linarith [norm_nonneg x]
  have h3 : |s103bQ d s (ρ τ) e x| ≤ Cq * Ah * B := by
    refine h2.trans ?_
    have : 0 ≤ Cq * Ah * B := by positivity
    calc Cq * Ah * B * (1 + ‖x‖)⁻¹ ≤ Cq * Ah * B * 1 := mul_le_mul_of_nonneg_left hw this
      _ = _ := mul_one _
  refine (abs_add_le _ _).trans ?_
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hn : 0 ≤ ‖x‖ := norm_nonneg x
  nlinarith [mul_nonneg hd0 (abs_nonneg β⁻¹), mul_nonneg (mul_nonneg hd0 (abs_nonneg β⁻¹)) hB,
    mul_nonneg (abs_nonneg a) hB, mul_nonneg hCq0 (mul_nonneg hAh hB), mul_nonneg hn hB,
    mul_nonneg (mul_nonneg hd0 (abs_nonneg β⁻¹)) (mul_nonneg hB hn), mul_nonneg (abs_nonneg a) (mul_nonneg hB hn),
    mul_nonneg hCq0 (mul_nonneg (mul_nonneg hAh hB) hn)]

theorem s103c_limit_solution {s a β : ℝ} (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {L A : ℝ}
    (hL : (d : ℝ) + ((0 : ℕ) : ℝ) + s + 3 < L) (hA : 0 ≤ A)
    (ρ : ℝ → Euc d → ℝ) {t : ℝ} (ht : 0 ≤ t) (hρ : ∀ τ ∈ Set.Icc (0 : ℝ) t, U2Dec 1 L A (ρ τ))
    {k : ℕ} (hk : 2 ≤ k) (w : ℕ → ℝ → Euc d → ℝ) {θ : ℕ → Euc d → ℝ}
    (hw : ∀ n, IsClassicalAdjointW ((quadraticGradientDyn d s a β).coeff ρ) t (θ n) (w n))
    (hCk : ∀ n, ∀ r ∈ Set.Icc (0 : ℝ) t, ContDiff ℝ (k : WithTop ℕ∞) (w n r)) (B : ℝ)
    (hB : ∀ n, ∀ r ∈ Set.Icc (0 : ℝ) t, ∀ j ≤ k, ∀ x, ‖iteratedFDeriv ℝ j (w n r) x‖ ≤ B)
    (hcau : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, ∀ m ≥ N, ∀ r ∈ Set.Icc (0 : ℝ) t, ∀ j ≤ k, ∀ x,
      ‖iteratedFDeriv ℝ j (w n r) x - iteratedFDeriv ℝ j (w m r) x‖ ≤ ε) :
    ∃ u : ℝ → Euc d → ℝ, IsClassicalAdjointW ((quadraticGradientDyn d s a β).coeff ρ) t (u t) u ∧
      (∀ r ∈ Set.Icc (0 : ℝ) t, ContDiff ℝ (k : WithTop ℕ∞) (u r)) ∧
      ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, ∀ r ∈ Set.Icc (0 : ℝ) t, ∀ j ≤ k, ∀ x,
        ‖iteratedFDeriv ℝ j (w n r) x - iteratedFDeriv ℝ j (u r) x‖ ≤ ε := by
  classical
  set Cf := (quadraticGradientDyn d s a β).coeff ρ with hCf
  have hex : ∀ r ∈ Set.Icc (0 : ℝ) t, ∃ u' : Euc d → ℝ, ContDiff ℝ (k : WithTop ℕ∞) u' ∧
      ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, ∀ j ≤ k, ∀ x,
        ‖iteratedFDeriv ℝ j (w n r) x - iteratedFDeriv ℝ j u' x‖ ≤ ε := by
    intro r hr
    refine s103c_ck_limit k (fun n => w n r) (fun n => hCk n r hr) (fun ε hε => ?_)
    obtain ⟨N, hN⟩ := hcau ε hε
    exact ⟨N, fun n hn m hm j hj x => hN n hn m hm r hr j hj x⟩
  choose! u hu1 hu2 using hex
  have hunif : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, ∀ r ∈ Set.Icc (0 : ℝ) t, ∀ j ≤ k, ∀ x,
      ‖iteratedFDeriv ℝ j (w n r) x - iteratedFDeriv ℝ j (u r) x‖ ≤ ε := by
    intro ε hε
    obtain ⟨N, hN⟩ := hcau ε hε
    refine ⟨N, fun n hn r hr j hj x => ?_⟩
    refine le_of_forall_pos_le_add fun ε' hε' => ?_
    obtain ⟨N', hN'⟩ := hu2 r hr ε' hε'
    have h1 := hN n hn (max N N') (le_trans (le_max_left _ _) le_rfl) r hr j hj x
    have h2 := hN' (max N N') (le_max_right _ _) j hj x
    calc ‖iteratedFDeriv ℝ j (w n r) x - iteratedFDeriv ℝ j (u r) x‖ =
        ‖(iteratedFDeriv ℝ j (w n r) x - iteratedFDeriv ℝ j (w (max N N') r) x) +
          (iteratedFDeriv ℝ j (w (max N N') r) x - iteratedFDeriv ℝ j (u r) x)‖ := by congr 1; abel
      _ ≤ _ := (norm_add_le _ _).trans (add_le_add h1 h2)
  have huB : ∀ r ∈ Set.Icc (0 : ℝ) t, ∀ j ≤ k, ∀ x, ‖iteratedFDeriv ℝ j (u r) x‖ ≤ B := by
    intro r hr j hj x
    refine le_of_forall_pos_le_add fun ε hε => ?_
    obtain ⟨N, hN⟩ := hunif ε hε
    have h1 := hN N le_rfl r hr j hj x
    have h2 := hB N r hr j hj x
    calc ‖iteratedFDeriv ℝ j (u r) x‖ ≤ ‖iteratedFDeriv ℝ j (w N r) x‖ +
        ‖iteratedFDeriv ℝ j (w N r) x - iteratedFDeriv ℝ j (u r) x‖ := by
          have := norm_sub_le (iteratedFDeriv ℝ j (w N r) x) (iteratedFDeriv ℝ j (w N r) x - iteratedFDeriv ℝ j (u r) x)
          simpa using this
      _ ≤ B + ε := add_le_add h2 h1
  have hkle : ∀ i, i ≤ 2 → i ≤ k := fun i hi => hi.trans hk
  have huC2 : ∀ r ∈ Set.Icc (0 : ℝ) t, ContDiff ℝ 2 (u r) := fun r hr => by
    have := (hu1 r hr).of_le (show ((2 : ℕ) : WithTop ℕ∞) ≤ (k : WithTop ℕ∞) by exact_mod_cast hk)
    exact_mod_cast this
  have hwC2 : ∀ n, ∀ r ∈ Set.Icc (0 : ℝ) t, ContDiff ℝ 2 (w n r) := fun n r hr => (hw n).c2 r hr
  have hdL : (d : ℝ) < L := by
    have : (0 : ℝ) ≤ s := hs0
    push_cast at hL
    linarith
  -- the generator estimate
  obtain ⟨Kg, hKg0, hKg⟩ := s103c_gen_le hd hs0 hsd a β hL
  have hLd : ∀ (ε' : ℝ), 0 ≤ ε' → ∀ n, ∀ r ∈ Set.Icc (0 : ℝ) t,
      (∀ i, 1 ≤ i → i ≤ 2 → ∀ y, ‖iteratedFDeriv ℝ i (w n r) y - iteratedFDeriv ℝ i (u r) y‖ ≤ ε') →
      ∀ x, |generatorW Cf r (w n r) x - generatorW Cf r (u r) x| ≤ Kg * (1 + A) * ε' * (1 + ‖x‖) := by
    intro ε' hε' n r hr hdiff x
    have hsub := s103c_gen_sub (a := a) (β := β) hd hs0 hsd hdL ρ r (hρ r hr)
      (hwC2 n r hr) (fun i h1 h2 y => hB n r hr i (hkle i h2) y) (huC2 r hr)
      (fun i h1 h2 y => huB r hr i (hkle i h2) y) x
    rw [← hsub]
    refine hKg ρ A r hA (by simpa using hρ r hr) (fun y => w n r y - u r y) ε' (by exact_mod_cast (huC2 r hr |> fun _ => (hwC2 n r hr).sub (huC2 r hr))) (fun i h1 h2 y => ?_) x
    rw [← s103c_iter_sub ((hwC2 n r hr).of_le (by exact_mod_cast h2)) ((huC2 r hr).of_le (by exact_mod_cast h2))]
    exact hdiff i h1 h2 y
  refine ⟨u, ⟨huC2, fun j hj => ⟨B, fun r hr x => huB r hr j (hkle j hj) x⟩, fun j hj => ?_, rfl, fun x r hr => ?_, ?_, ?_⟩,
    hu1, hunif⟩
  · -- continuity of the jets
    have hF : ∀ n, Continuous (fun p : Set.Icc (0 : ℝ) t × Euc d => iteratedFDeriv ℝ j (w n p.1) p.2) :=
      fun n => (hw n).cont_c2 j hj
    refine TendstoUniformly.continuous (F := fun n (p : Set.Icc (0 : ℝ) t × Euc d) => iteratedFDeriv ℝ j (w n p.1) p.2)
      (p := atTop) ?_ (Filter.Eventually.of_forall hF).frequently
    rw [Metric.tendstoUniformly_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := hunif (ε / 2) (by positivity)
    refine Filter.eventually_atTop.2 ⟨N, fun n hn p => ?_⟩
    rw [dist_comm, dist_eq_norm]
    exact (hN n hn p.1.1 p.1.2 j (hkle j hj) p.2).trans_lt (by linarith)
  · -- the time derivative
    have hmem : ∀ r' ∈ Set.Ioo (0 : ℝ) t, r' ∈ Set.Icc (0 : ℝ) t := fun r' hr' => ⟨hr'.1.le, hr'.2.le⟩
    have hunif' : TendstoUniformlyOn (fun n r' => -(generatorW Cf r' (w n r') x))
        (fun r' => -(generatorW Cf r' (u r') x)) atTop (Set.Ioo 0 t) := by
      rw [Metric.tendstoUniformlyOn_iff]
      intro ε hε
      set Q : ℝ := Kg * (1 + A) * (1 + ‖x‖) + 1 with hQ
      have hQ0 : 0 < Q := by positivity
      obtain ⟨N, hN⟩ := hunif (ε / (2 * Q)) (by positivity)
      refine Filter.eventually_atTop.2 ⟨N, fun n hn r' hr' => ?_⟩
      rw [dist_comm, dist_eq_norm, Real.norm_eq_abs]
      have := hLd (ε / (2 * Q)) (by positivity) n r' (hmem r' hr')
        (fun i h1 h2 y => hN n hn r' (hmem r' hr') i (hkle i h2) y) x
      have e : -(generatorW Cf r' (w n r') x) - -(generatorW Cf r' (u r') x) =
          -(generatorW Cf r' (w n r') x - generatorW Cf r' (u r') x) := by ring
      rw [e, abs_neg]
      refine this.trans_lt ?_
      have h3 : Kg * (1 + A) * (ε / (2 * Q)) * (1 + ‖x‖) = (Kg * (1 + A) * (1 + ‖x‖)) * (ε / (2 * Q)) := by ring
      rw [h3]
      have h4 : Kg * (1 + A) * (1 + ‖x‖) ≤ Q := by rw [hQ]; linarith
      calc (Kg * (1 + A) * (1 + ‖x‖)) * (ε / (2 * Q)) ≤ Q * (ε / (2 * Q)) :=
            mul_le_mul_of_nonneg_right h4 (by positivity)
        _ = ε / 2 := by field_simp
        _ < ε := by linarith
    have hpt : ∀ r' ∈ Set.Ioo (0 : ℝ) t, Tendsto (fun n => w n r' x) atTop (𝓝 (u r' x)) := by
      intro r' hr'
      rw [tendsto_iff_norm_sub_tendsto_zero]
      refine tendsto_order.2 ⟨fun a ha => ?_, fun a ha => ?_⟩
      · exact Filter.Eventually.of_forall fun n => lt_of_lt_of_le ha (norm_nonneg _)
      · obtain ⟨N, hN⟩ := hunif (a / 2) (by linarith)
        refine Filter.eventually_atTop.2 ⟨N, fun n hn => ?_⟩
        have := hN n hn r' (hmem r' hr') 0 (Nat.zero_le _) x
        rw [s103c_iter_sub ((hCk n r' (hmem r' hr')).of_le (by exact_mod_cast Nat.zero_le _))
          ((hu1 r' (hmem r' hr')).of_le (by exact_mod_cast Nat.zero_le _))] at this
        simp only [norm_iteratedFDeriv_zero] at this
        linarith
    exact hasDerivAt_of_tendstoUniformlyOn isOpen_Ioo hunif' (Filter.Eventually.of_forall fun n r' hr' => (hw n).time_deriv x r' hr') hpt hr
  · -- continuity of the generator along the limit
    have hFn : ∀ n, Continuous (fun p : Set.Icc (0 : ℝ) t × Euc d => generatorW Cf p.1 (w n p.1) p.2) :=
      fun n => (hw n).cont_time_deriv
    refine TendstoLocallyUniformly.continuous
      (F := fun n (p : Set.Icc (0 : ℝ) t × Euc d) => generatorW Cf p.1 (w n p.1) p.2) (p := atTop) ?_
      (Filter.Eventually.of_forall hFn).frequently
    rw [tendstoLocallyUniformly_iff_forall_isCompact]
    intro K hK
    obtain ⟨R, hR⟩ := hK.exists_bound_of_continuousOn
      (f := fun p : Set.Icc (0 : ℝ) t × Euc d => ‖p.2‖) (continuous_norm.comp continuous_snd).continuousOn
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    set Q : ℝ := Kg * (1 + A) * (1 + |R|) + 1 with hQ
    have hQ0 : 0 < Q := by positivity
    obtain ⟨N, hN⟩ := hunif (ε / (2 * Q)) (by positivity)
    refine Filter.eventually_atTop.2 ⟨N, fun n hn p hp => ?_⟩
    rw [dist_comm, dist_eq_norm, Real.norm_eq_abs]
    have := hLd (ε / (2 * Q)) (by positivity) n p.1.1 p.1.2
      (fun i h1 h2 y => hN n hn p.1.1 p.1.2 i (hkle i h2) y) p.2
    refine this.trans_lt ?_
    have hpR : ‖p.2‖ ≤ |R| := by
      have := hR p hp
      rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] at this
      exact this.trans (le_abs_self _)
    have h4 : Kg * (1 + A) * (1 + ‖p.2‖) ≤ Q := by
      rw [hQ]
      have : Kg * (1 + A) * (1 + ‖p.2‖) ≤ Kg * (1 + A) * (1 + |R|) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      linarith
    have h3 : Kg * (1 + A) * (ε / (2 * Q)) * (1 + ‖p.2‖) =
        (Kg * (1 + A) * (1 + ‖p.2‖)) * (ε / (2 * Q)) := by ring
    rw [h3]
    calc (Kg * (1 + A) * (1 + ‖p.2‖)) * (ε / (2 * Q)) ≤ Q * (ε / (2 * Q)) :=
          mul_le_mul_of_nonneg_right h4 (by positivity)
      _ = ε / 2 := by field_simp
      _ < ε := by linarith
  · -- linear growth of the time derivative
    refine ⟨Kg * (1 + A) * B, fun r hr x => ?_⟩
    exact hKg ρ A r hA (by simpa using hρ r hr) (u r) B (by exact_mod_cast huC2 r hr)
      (fun i h1 h2 y => huB r hr i (hkle i h2) y) x

end HRS.MS.R2WinOrbNL

end
