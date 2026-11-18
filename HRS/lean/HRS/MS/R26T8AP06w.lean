import HRS.MS.R26T8AP06a
import HRS.MS.R26T8AP06v

/-!
# S8.2 Taylor split (T), step B2b: pure remainder bound for a function of the relative variable
`r26t8a_word_taylor`: for a scalar `h` with conormal jet envelope (order `sigma < 0`, `m < -sigma <= m+1`) and prescribed limits `Λ ℓ` of its
`ℓ`-th derivatives at `0` (`ℓ <= m`), the function `h - Σ_{ℓ<=m} (1/ℓ!) Λ ℓ (w,…,w)` has derivatives of order `q <= N` bounded by `C A' |z|^(-sigma-q) (1+|log|z||)^b`
for `0 < |z| <= 1/2`.  (`r26t8a_negative_taylor` plus identification of its polynomial with the limit-jet polynomial.)
-/

set_option autoImplicit false
noncomputable section
open Filter Topology
open scoped ContDiff

namespace HRS.MS.R26T8A
open HRS

theorem r26t8a_word_taylor {d : ℕ} (hd : 2 ≤ d) (b N m : ℕ) (σ : ℝ) (hσ : σ < 0) (hm : (m : ℝ) < -σ)
    (hm1 : -σ ≤ (m : ℝ) + 1) (hN : m + 1 ≤ N) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ A' : ℝ, 0 ≤ A' → ∀ (h : Euc d → ℝ)
      (Λ : (ℓ : ℕ) → ContinuousMultilinearMap ℝ (fun _ : Fin ℓ => Euc d) ℝ),
      ContDiffOn ℝ N h {z | z ≠ 0} →
      (∀ i ≤ N, ∀ z : Euc d, 0 < ‖z‖ → ‖z‖ ≤ 1 → ‖iteratedFDeriv ℝ i h z‖ ≤ A' * r26t8a_jetEnvelope b (σ + i) ‖z‖) →
      (∀ ℓ ≤ m, Tendsto (fun z : Euc d => iteratedFDeriv ℝ ℓ h z) (𝓝[≠] (0 : Euc d)) (𝓝 (Λ ℓ))) →
      ∀ q ≤ N, ∀ z : Euc d, 0 < ‖z‖ → ‖z‖ ≤ 1 / 2 →
        ‖iteratedFDeriv ℝ q (fun w : Euc d => h w - ∑ ℓ ∈ Finset.range (m + 1), (1 / (ℓ.factorial : ℝ)) * Λ ℓ (fun _ => w)) z‖ ≤
          C * A' * ‖z‖ ^ (-σ - (q : ℝ)) * (1 + |Real.log ‖z‖|) ^ b := by
  haveI : Nontrivial (Euc d) := ⟨⟨0, EuclideanSpace.single ⟨0, by omega⟩ (1 : ℝ), by
    intro h; have := congrArg (fun v : Euc d => v ⟨0, by omega⟩) h; simp at this⟩⟩
  obtain ⟨C0, hC00, hC0⟩ := r26t8a_negative_taylor hd N b (by omega) σ hσ
  refine ⟨C0, hC00, ?_⟩
  intro A' hA' h Λ hcd hjet hlim q hq z hz hz1
  obtain ⟨coeff, -, hcz, hrem⟩ := hC0 A' hA' h hcd hjet
  set Qp : Euc d → ℝ := fun v => ∑ ℓ ∈ Finset.range N, coeff ℓ (fun _ => v) with hQp
  have hvan : ∀ j, m < j → coeff j = 0 := fun j hj => hcz j (by
    have : (m : ℝ) + 1 ≤ j := by exact_mod_cast hj
    exact (min_le_left _ _).trans (by linarith))
  have hmin : min (-σ) (N : ℝ) = -σ := min_eq_left (by
    have : ((m + 1 : ℕ) : ℝ) ≤ N := by exact_mod_cast hN
    push_cast at this; linarith)
  have hQd : ∀ n : ℕ, ContDiff ℝ (n : WithTop ℕ∞) Qp := fun n => by
    refine ContDiff.sum fun ℓ _ => ?_
    exact (coeff ℓ).contDiff.comp (ContinuousLinearMap.pi (fun _ : Fin ℓ => ContinuousLinearMap.id ℝ (Euc d))).contDiff
  have hopen : IsOpen {w : Euc d | w ≠ 0} := isOpen_ne
  -- decay of the remainder jets
  have hdecay : ∀ ℓ ≤ m, Tendsto (fun z : Euc d => iteratedFDeriv ℝ ℓ (fun v => h v - Qp v) z) (𝓝[≠] (0 : Euc d)) (𝓝 0) := by
    intro ℓ hℓ
    have hc : 0 < -σ - (ℓ : ℝ) := by
      have : (ℓ : ℝ) ≤ m := by exact_mod_cast hℓ
      linarith
    have hc2 : 0 < (-σ - (ℓ : ℝ)) / 2 := by positivity
    set M' : ℝ := r26t8a_p06_M ((-σ - (ℓ : ℝ)) / 2) b with hM'
    have hM'0 : 0 ≤ M' := by rw [hM']; unfold r26t8a_p06_M; positivity
    have hg : Tendsto (fun z : Euc d => C0 * A' * M' * ‖z‖ ^ ((-σ - (ℓ : ℝ)) / 2)) (𝓝[≠] (0 : Euc d)) (𝓝 0) := by
      have h1 : Tendsto (fun z : Euc d => ‖z‖) (𝓝[≠] (0 : Euc d)) (𝓝 0) := by
        have := (continuous_norm (E := Euc d)).tendsto (0 : Euc d)
        simp only [norm_zero] at this
        exact this.mono_left nhdsWithin_le_nhds
      have h2 : Tendsto (fun r : ℝ => r ^ ((-σ - (ℓ : ℝ)) / 2)) (𝓝 0) (𝓝 0) := by
        have := (Real.continuousAt_rpow_const 0 ((-σ - (ℓ : ℝ)) / 2) (Or.inr hc2.le)).tendsto
        simpa [Real.zero_rpow hc2.ne'] using this
      simpa using (h2.comp h1).const_mul (C0 * A' * M')
    refine squeeze_zero_norm' ?_ hg
    have h1 : ∀ᶠ z in 𝓝[≠] (0 : Euc d), dist z 0 < 1 / 2 :=
      eventually_nhdsWithin_of_eventually_nhds
        (Metric.eventually_nhds_iff.2 ⟨1 / 2, by norm_num, fun y hy => hy⟩ : ∀ᶠ w in 𝓝 (0 : Euc d), dist w 0 < 1 / 2)
    filter_upwards [(eventually_mem_nhdsWithin : ∀ᶠ w in 𝓝[≠] (0 : Euc d), w ∈ ({0}ᶜ : Set (Euc d))), h1] with z hz hz1
    have hz0 : z ≠ 0 := hz
    have hzpos : 0 < ‖z‖ := norm_pos_iff.2 hz0
    have hzn : ‖z‖ ≤ 1 / 2 := by simpa using hz1.le
    have hb := hrem ℓ (by omega) z hzpos hzn
    rw [hmin] at hb
    refine hb.trans ?_
    have hsl := r26t8a_p06_slog b hc2 hzpos (by linarith)
    have e : ‖z‖ ^ (-σ - (ℓ : ℝ)) = ‖z‖ ^ ((-σ - (ℓ : ℝ)) / 2) * ‖z‖ ^ ((-σ - (ℓ : ℝ)) / 2) := by
      rw [← Real.rpow_add hzpos]; congr 1; ring
    rw [e]
    have hp0 : 0 ≤ ‖z‖ ^ ((-σ - (ℓ : ℝ)) / 2) := Real.rpow_nonneg (norm_nonneg _) _
    calc C0 * A' * (‖z‖ ^ ((-σ - (ℓ : ℝ)) / 2) * ‖z‖ ^ ((-σ - (ℓ : ℝ)) / 2)) * (1 + |Real.log ‖z‖|) ^ b
        = C0 * A' * ‖z‖ ^ ((-σ - (ℓ : ℝ)) / 2) * (‖z‖ ^ ((-σ - (ℓ : ℝ)) / 2) * (1 + |Real.log ‖z‖|) ^ b) := by ring
      _ ≤ C0 * A' * ‖z‖ ^ ((-σ - (ℓ : ℝ)) / 2) * M' := mul_le_mul_of_nonneg_left hsl (by positivity)
      _ = C0 * A' * M' * ‖z‖ ^ ((-σ - (ℓ : ℝ)) / 2) := by ring
  have hjetQ : ∀ ℓ ≤ m, iteratedFDeriv ℝ ℓ Qp 0 = Λ ℓ := by
    intro ℓ hℓ
    have h1 : Tendsto (fun z : Euc d => iteratedFDeriv ℝ ℓ Qp z) (𝓝[≠] (0 : Euc d)) (𝓝 (iteratedFDeriv ℝ ℓ Qp 0)) :=
      (((hQd ℓ).continuous_iteratedFDeriv (m := ℓ) le_rfl).tendsto (0 : Euc d)).mono_left nhdsWithin_le_nhds
    have h2 : Tendsto (fun z : Euc d => iteratedFDeriv ℝ ℓ Qp z) (𝓝[≠] (0 : Euc d)) (𝓝 (Λ ℓ)) := by
      have h3 := (hlim ℓ hℓ).sub (hdecay ℓ hℓ)
      rw [sub_zero] at h3
      refine h3.congr' ?_
      filter_upwards [(eventually_mem_nhdsWithin : ∀ᶠ w in 𝓝[≠] (0 : Euc d), w ∈ ({0}ᶜ : Set (Euc d)))] with z hz
      have hz0 : z ≠ 0 := hz
      have hhd : ContDiffAt ℝ (ℓ : WithTop ℕ∞) h z :=
        ((hcd.contDiffAt (hopen.mem_nhds hz0)).of_le (by exact_mod_cast (by omega : ℓ ≤ N)))
      have := iteratedFDeriv_sub_apply (i := ℓ) hhd (hQd ℓ).contDiffAt
      have this' : iteratedFDeriv ℝ ℓ (fun v => h v - Qp v) z = iteratedFDeriv ℝ ℓ h z - iteratedFDeriv ℝ ℓ Qp z := this
      rw [this']
      abel
    exact tendsto_nhds_unique h1 h2
  have hPfun : ∀ w : Euc d, ∑ ℓ ∈ Finset.range (m + 1), (1 / (ℓ.factorial : ℝ)) * Λ ℓ (fun _ => w) = Qp w := by
    intro w
    rw [hQp]
    simp only
    rw [r26t8a_poly_taylor N m (by omega) coeff hvan w]
    refine Finset.sum_congr rfl fun ℓ hℓ => ?_
    rw [hjetQ ℓ (by rw [Finset.mem_range] at hℓ; omega)]
  have hfe : (fun w : Euc d => h w - ∑ ℓ ∈ Finset.range (m + 1), (1 / (ℓ.factorial : ℝ)) * Λ ℓ (fun _ => w)) =
      fun v => h v - Qp v := by
    funext w; rw [hPfun w]
  rw [hfe]
  have := hrem q hq z hz hz1
  rw [hmin] at this
  exact this

end HRS.MS.R26T8A
