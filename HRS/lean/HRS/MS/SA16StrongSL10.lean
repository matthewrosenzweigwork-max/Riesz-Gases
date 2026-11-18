import HRS.MS.SA16StrongSL10Aux
import HRS.MS.SA16StrongDomLp

/-!
# S.A.16 SL10: `nlCut_difference_bound_cb`

For `μ ∈ C_b^{m+2}` take Schwartz approximants `μ_n` (`sa16y_approx`) with `D^j μ_n → D^j μ` pointwise and
`‖D^j μ_n‖ ≤ K B`.  SL3 bounds `wNormE m (F_n)` uniformly; `sa16y_nlCut_tendsto` gives `F_n → F` pointwise; the core
estimate `sa16y_nl_core` applied to `μ_n - μ_l` together with the Leibniz bound and dominated convergence shows that
`F_n` is Cauchy for `wNormE m`.  `sa16y_wnorm_limit` passes the bound to `F`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff SchwartzMap

namespace HRS.Whole.AppendixA.Phase2SA16
open HRS HRS.Whole HRS.Whole.AppendixA

section SL10
variable {d : ℕ}

lemma sa16y_cb_bound {k : ℕ} {μ : Euc d → ℝ} (hμ : MemCb k μ) {B : ℝ} (hB : cbNorm k μ ≤ B) :
    ∀ j ≤ k, ∀ x, ‖iteratedFDeriv ℝ j μ x‖ ≤ B := by
  intro j hj x
  have hbdd := hμ.2 j hj
  have h1 : ‖iteratedFDeriv ℝ j μ x‖ ≤ ⨆ z, ‖iteratedFDeriv ℝ j μ z‖ := le_ciSup hbdd x
  have h2 : (⨆ z, ‖iteratedFDeriv ℝ j μ z‖) ≤ cbNorm k μ := by
    unfold cbNorm
    exact Finset.single_le_sum (f := fun j => ⨆ z, ‖iteratedFDeriv ℝ j μ z‖)
      (fun i _ => Real.iSup_nonneg fun z => norm_nonneg _) (Finset.mem_range.2 (by omega))
  linarith

/-- the vanishing weight: total deviation of the first `k+1` derivatives -/
def sa16y_dev (d k : ℕ) (μs : ℕ → 𝓢(Euc d, ℝ)) (μ : Euc d → ℝ) (n : ℕ) (x : Euc d) : ℝ :=
  ∑ i ∈ Finset.range (k + 1), ‖iteratedFDeriv ℝ i (⇑(μs n)) x - iteratedFDeriv ℝ i μ x‖

lemma sa16y_dev_nonneg (d k : ℕ) (μs : ℕ → 𝓢(Euc d, ℝ)) (μ : Euc d → ℝ) (n : ℕ) (x : Euc d) :
    0 ≤ sa16y_dev d k μs μ n x := Finset.sum_nonneg fun _ _ => norm_nonneg _

lemma sa16y_dev_cont (k : ℕ) (μs : ℕ → 𝓢(Euc d, ℝ)) {μ : Euc d → ℝ} (hμ : ContDiff ℝ k μ) (n : ℕ) :
    Continuous (sa16y_dev d k μs μ n) := by
  unfold sa16y_dev
  refine continuous_finsetSum _ fun i hi => ?_
  have hi' : i ≤ k := by have := Finset.mem_range.1 hi; omega
  have h1 : Continuous fun x => iteratedFDeriv ℝ i (⇑(μs n)) x :=
    (show ContDiff ℝ ∞ (⇑(μs n)) from (μs n).smooth').continuous_iteratedFDeriv (m := i)
      (by exact_mod_cast le_top)
  have h2 : Continuous fun x => iteratedFDeriv ℝ i μ x :=
    hμ.continuous_iteratedFDeriv (m := i) (by exact_mod_cast hi')
  exact (h1.sub h2).norm

lemma sa16y_dev_diff (k : ℕ) (μs : ℕ → 𝓢(Euc d, ℝ)) (μ : Euc d → ℝ) (n l : ℕ) (x : Euc d) {i : ℕ}
    (hi : i ≤ k) :
    ‖iteratedFDeriv ℝ i (⇑(μs n - μs l)) x‖ ≤ sa16y_dev d k μs μ n x + sa16y_dev d k μs μ l x := by
  have hn : ContDiffAt ℝ i (⇑(μs n)) x :=
    ((μs n).smooth'.of_le (by exact_mod_cast le_top)).contDiffAt
  have hl : ContDiffAt ℝ i (⇑(μs l)) x :=
    ((μs l).smooth'.of_le (by exact_mod_cast le_top)).contDiffAt
  have hsub : (⇑(μs n - μs l) : Euc d → ℝ) = ⇑(μs n) - ⇑(μs l) := by funext y; simp
  rw [hsub, iteratedFDeriv_sub_apply hn hl]
  refine (norm_sub_le_norm_sub_add_norm_sub (iteratedFDeriv ℝ i (⇑(μs n)) x)
    (iteratedFDeriv ℝ i μ x) (iteratedFDeriv ℝ i (⇑(μs l)) x)).trans ?_
  rw [norm_sub_rev (iteratedFDeriv ℝ i μ x)]
  have h1 : ‖iteratedFDeriv ℝ i (⇑(μs n)) x - iteratedFDeriv ℝ i μ x‖ ≤ sa16y_dev d k μs μ n x :=
    Finset.single_le_sum (f := fun i => ‖iteratedFDeriv ℝ i (⇑(μs n)) x - iteratedFDeriv ℝ i μ x‖)
      (fun _ _ => norm_nonneg _) (Finset.mem_range.2 (by omega))
  have h2 : ‖iteratedFDeriv ℝ i (⇑(μs l)) x - iteratedFDeriv ℝ i μ x‖ ≤ sa16y_dev d k μs μ l x :=
    Finset.single_le_sum (f := fun i => ‖iteratedFDeriv ℝ i (⇑(μs l)) x - iteratedFDeriv ℝ i μ x‖)
      (fun _ _ => norm_nonneg _) (Finset.mem_range.2 (by omega))
  linarith

/-- the Cauchy estimate for the approximating differences -/
lemma sa16y_cauchy (hd : 1 ≤ d) (m : ℕ) (θ p lam c gamma MB : ℝ) (hθ0 : 0 < θ) (hθ2 : θ < 2)
    [Fact (2 ≤ p)] (C0 : ℝ) (hC0 : 0 < C0)
    (h0 : ∀ M : Matrix (Fin d) (Fin d) ℝ, (∀ i j, |M i j| ≤ MB) → ∀ f u : 𝓢(Euc d, ℝ),
      ∀ δ η : ℝ, δ ∈ Ioc (0 : ℝ) 1 → η ∈ Ioc (0 : ℝ) 1 →
      wNormE m p (fun x => nlCut d θ δ lam c gamma M f u x - nlCut d θ η lam c gamma M f u x) ≤
        ENNReal.ofReal (C0 * (δ ^ (2 - θ) + η ^ (2 - θ))) *
          (wNormE (m + 2) p (⇑(sa16y_mulS f u)) +
            ∑ j : Fin d, wNormE (m + 1) p (⇑(sa16y_mulS (sa16y_dS f j) u))))
    (M : Matrix (Fin d) (Fin d) ℝ) (hM : ∀ i j, |M i j| ≤ MB)
    (μ : Euc d → ℝ) (hμ : ContDiff ℝ ((m + 2 : ℕ) : WithTop ℕ∞) μ) (μs : ℕ → 𝓢(Euc d, ℝ)) {E0 : ℝ}
    (hE0 : ∀ n x, sa16y_dev d (m + 2) μs μ n x ≤ E0)
    (hconv : ∀ j ≤ m + 2, ∀ x, Tendsto (fun n => ‖iteratedFDeriv ℝ j (⇑(μs n)) x -
      iteratedFDeriv ℝ j μ x‖) atTop (𝓝 0))
    (δ η : ℝ) (hδ : δ ∈ Ioc (0 : ℝ) 1) (hη : η ∈ Ioc (0 : ℝ) 1) (u : 𝓢(Euc d, ℝ)) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, ∀ l ≥ N,
      wNormE m p (fun x => (nlCut d θ δ lam c gamma M (⇑(μs n)) u x -
          nlCut d θ η lam c gamma M (⇑(μs n)) u x) -
        (nlCut d θ δ lam c gamma M (⇑(μs l)) u x - nlCut d θ η lam c gamma M (⇑(μs l)) u x)) ≤
        ENNReal.ofReal ε := by
  intro ε hε
  have hp1 : (1 : ℝ) ≤ p := by have : (2 : ℝ) ≤ p := Fact.out; linarith
  have hu : ContDiff ℝ ∞ (⇑u) := u.smooth'
  have hSu : MemLp (sa16j_S d (m + 2) (⇑u)) (ENNReal.ofReal p) volume := sa16j_S_memLp (m + 2) p u
  set S : ℝ := δ ^ (2 - θ) + η ^ (2 - θ) with hS
  set c1 : ℝ := ((d : ℝ) + 1) ^ (m + 2) with hc1
  have hc10 : 0 ≤ c1 := by positivity
  set J : Euc d → ℝ := fun x => c1 * ‖wJet (m + 2) (⇑u) x‖ with hJ
  have hJc : Continuous J := continuous_const.mul (sa16j_jet_cont hu (m + 2)).norm
  have hJmem : MemLp J (ENNReal.ofReal p) volume :=
    ((sa16j_jet_memLp d (m + 2) p hu hSu).norm).const_mul c1
  set G : ℕ → ℝ≥0∞ := fun n =>
    eLpNorm (fun x => sa16y_dev d (m + 2) μs μ n x * J x) (ENNReal.ofReal p) volume with hG
  have hGlim : Tendsto G atTop (𝓝 0) :=
    sa16y_dom_lp p hp1 (sa16y_dev d (m + 2) μs μ) J (fun n => sa16y_dev_cont (m + 2) μs hμ n)
      (sa16y_dev_nonneg d (m + 2) μs μ) hE0
      (fun x => by
        unfold sa16y_dev
        simpa using tendsto_finsetSum (Finset.range (m + 2 + 1)) fun i hi =>
          hconv i (by have := Finset.mem_range.1 hi; omega) x)
      hJc hJmem
  -- the pointwise Leibniz bounds
  have hdevc : ∀ n, Continuous (sa16y_dev d (m + 2) μs μ n) := fun n => sa16y_dev_cont (m + 2) μs hμ n
  have hmeasJ : ∀ n, AEStronglyMeasurable (fun x => sa16y_dev d (m + 2) μs μ n x * J x) volume :=
    fun n => ((hdevc n).mul hJc).aestronglyMeasurable
  have hsumle : ∀ n l, eLpNorm (fun x => (sa16y_dev d (m + 2) μs μ n x + sa16y_dev d (m + 2) μs μ l x) * J x)
      (ENNReal.ofReal p) volume ≤ G n + G l := by
    intro n l
    have : (fun x => (sa16y_dev d (m + 2) μs μ n x + sa16y_dev d (m + 2) μs μ l x) * J x) =
        (fun x => sa16y_dev d (m + 2) μs μ n x * J x) + (fun x => sa16y_dev d (m + 2) μs μ l x * J x) := by
      funext x; simp [add_mul]
    rw [this]
    exact eLpNorm_add_le (by simpa using hp1)
  have hA : ∀ n l, wNormE (m + 2) p (⇑(sa16y_mulS (μs n - μs l) u)) ≤ G n + G l := by
    intro n l
    rw [sa16y_wnorm_jet]
    refine le_trans ?_ (hsumle n l)
    have hmeas : AEStronglyMeasurable (wJet (m + 2) (⇑(sa16y_mulS (μs n - μs l) u))) volume :=
      (sa16j_jet_cont (sa16y_mulS (μs n - μs l) u).smooth' (m + 2)).aestronglyMeasurable
    refine eLpNorm_mono_ae_real hmeas (Eventually.of_forall fun x => ?_)
    rw [sa16y_mulS_apply]
    have := sa16y_prod_jet_le (f := ⇑(μs n - μs l)) (g := ⇑u) (μs n - μs l).smooth' hu (m + 2) x
      (B := sa16y_dev d (m + 2) μs μ n x + sa16y_dev d (m + 2) μs μ l x)
      (fun i hi => sa16y_dev_diff (m + 2) μs μ n l x hi)
    refine this.trans (le_of_eq ?_)
    simp only [hJ, hc1]
    ring
  have hB' : ∀ n l (j : Fin d), wNormE (m + 1) p (⇑(sa16y_mulS (sa16y_dS (μs n - μs l) j) u)) ≤
      G n + G l := by
    intro n l j
    rw [sa16y_wnorm_jet]
    refine le_trans ?_ (hsumle n l)
    have hmeas : AEStronglyMeasurable (wJet (m + 1) (⇑(sa16y_mulS (sa16y_dS (μs n - μs l) j) u))) volume :=
      (sa16j_jet_cont (sa16y_mulS (sa16y_dS (μs n - μs l) j) u).smooth' (m + 1)).aestronglyMeasurable
    refine eLpNorm_mono_ae_real hmeas (Eventually.of_forall fun x => ?_)
    rw [sa16y_mulS_apply]
    have hbd : ∀ i ≤ m + 1, ‖iteratedFDeriv ℝ i (⇑(sa16y_dS (μs n - μs l) j)) x‖ ≤
        sa16y_dev d (m + 2) μs μ n x + sa16y_dev d (m + 2) μs μ l x := by
      intro i hi
      rw [sa16y_dS_apply]
      exact (sa16y_dpd_norm (μs n - μs l) j i x).trans (sa16y_dev_diff (m + 2) μs μ n l x (by omega))
    have := sa16y_prod_jet_le (f := ⇑(sa16y_dS (μs n - μs l) j)) (g := ⇑u)
      (sa16y_dS (μs n - μs l) j).smooth' hu (m + 1) x
      (B := sa16y_dev d (m + 2) μs μ n x + sa16y_dev d (m + 2) μs μ l x) hbd
    refine this.trans ?_
    have hsum0 : 0 ≤ sa16y_dev d (m + 2) μs μ n x + sa16y_dev d (m + 2) μs μ l x :=
      add_nonneg (sa16y_dev_nonneg _ _ _ _ _ _) (sa16y_dev_nonneg _ _ _ _ _ _)
    have hpow : ((d : ℝ) + 1) ^ (m + 1) ≤ ((d : ℝ) + 1) ^ (m + 2) :=
      pow_le_pow_right₀ (by have : (0 : ℝ) ≤ d := Nat.cast_nonneg _; linarith) (by omega)
    calc (sa16y_dev d (m + 2) μs μ n x + sa16y_dev d (m + 2) μs μ l x) * ((d : ℝ) + 1) ^ (m + 1) *
          ‖wJet (m + 1) (⇑u) x‖
        ≤ (sa16y_dev d (m + 2) μs μ n x + sa16y_dev d (m + 2) μs μ l x) * ((d : ℝ) + 1) ^ (m + 2) *
          ‖wJet (m + 2) (⇑u) x‖ := by
          refine mul_le_mul (mul_le_mul_of_nonneg_left hpow hsum0) (sa16y_jet_mono (by omega) _ x)
            (norm_nonneg _) (by positivity)
      _ = (sa16y_dev d (m + 2) μs μ n x + sa16y_dev d (m + 2) μs μ l x) * J x := by
          simp only [hJ, hc1]; ring
  -- the Cauchy estimate
  set K0 : ℝ≥0∞ := ENNReal.ofReal (C0 * S) * (1 + (d : ℝ≥0∞)) with hK0
  have hK0top : K0 ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top, ENNReal.natCast_ne_top d⟩)
  have hKG : Tendsto (fun n => K0 * G n) atTop (𝓝 0) := by
    have := ENNReal.Tendsto.const_mul hGlim (Or.inr hK0top)
    simpa using this
  have hev := (ENNReal.tendsto_nhds_zero.1 hKG) (ENNReal.ofReal (ε / 2)) (by simpa using (by positivity : 0 < ε / 2))
  obtain ⟨N, hN⟩ := eventually_atTop.1 hev
  refine ⟨N, fun n hn l hl => ?_⟩
  have hfd : (fun x => (nlCut d θ δ lam c gamma M (⇑(μs n)) u x -
          nlCut d θ η lam c gamma M (⇑(μs n)) u x) -
        (nlCut d θ δ lam c gamma M (⇑(μs l)) u x - nlCut d θ η lam c gamma M (⇑(μs l)) u x)) =
      fun x => nlCut d θ δ lam c gamma M (⇑(μs n - μs l)) u x -
        nlCut d θ η lam c gamma M (⇑(μs n - μs l)) u x := by
    funext x
    rw [sa16y_nlCut_sub hd hδ.1 hθ0 lam c gamma M (μs n) (μs l) u x,
      sa16y_nlCut_sub hd hη.1 hθ0 lam c gamma M (μs n) (μs l) u x]
    ring
  rw [hfd]
  refine (h0 M hM (μs n - μs l) u δ η hδ hη).trans ?_
  have hsum : wNormE (m + 2) p (⇑(sa16y_mulS (μs n - μs l) u)) +
      ∑ j : Fin d, wNormE (m + 1) p (⇑(sa16y_mulS (sa16y_dS (μs n - μs l) j) u)) ≤
      (1 + (d : ℝ≥0∞)) * (G n + G l) := by
    calc _ ≤ (G n + G l) + ∑ j : Fin d, (G n + G l) :=
          add_le_add (hA n l) (Finset.sum_le_sum fun j _ => hB' n l j)
      _ = (1 + (d : ℝ≥0∞)) * (G n + G l) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, add_mul, one_mul,
            mul_comm]
  calc ENNReal.ofReal (C0 * S) * (wNormE (m + 2) p (⇑(sa16y_mulS (μs n - μs l) u)) +
        ∑ j : Fin d, wNormE (m + 1) p (⇑(sa16y_mulS (sa16y_dS (μs n - μs l) j) u)))
      ≤ ENNReal.ofReal (C0 * S) * ((1 + (d : ℝ≥0∞)) * (G n + G l)) := mul_le_mul' le_rfl hsum
    _ = K0 * G n + K0 * G l := by rw [hK0, ← mul_assoc, mul_add]
    _ ≤ ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) := add_le_add (hN n hn) (hN l hl)
    _ = ENNReal.ofReal ε := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1; ring

theorem nlCut_difference_bound_cb (d : ℕ) (hd : 1 ≤ d) (m : ℕ)
    (θ p lam c gamma MB B : ℝ) (hθ0 : 0 < θ) (hθ2 : θ < 2)
    [Fact (2 ≤ p)] :
    ∃ C : ℝ, 0 < C ∧ ∀ M : Matrix (Fin d) (Fin d) ℝ,
      (∀ i j, |M i j| ≤ MB) → ∀ μ : Euc d → ℝ,
      MemCb (m+2) μ → cbNorm (m+2) μ ≤ B →
      ∀ δ η : ℝ, δ ∈ Ioc (0 : ℝ) 1 → η ∈ Ioc (0 : ℝ) 1 →
      ∀ u : SchwartzMap (Euc d) ℝ,
      wNormE m p
        (fun x => nlCut d θ δ lam c gamma M μ u x-nlCut d θ η lam c gamma M μ u x) ≤
        ENNReal.ofReal (C*(δ^(2-θ)+η^(2-θ))) * wNormE (m+2) p u := by
  obtain ⟨K, hK0, hap⟩ := sa16y_approx d (m + 2)
  obtain ⟨C0, hC0, h0⟩ := sa16y_nl_core d hd m θ p lam c gamma MB hθ0 hθ2
  obtain ⟨C3, hC3, h3⟩ := nlCut_difference_bound d hd m θ p lam c gamma MB (K * |B|) hθ0 hθ2
  refine ⟨C3, hC3, ?_⟩
  intro M hM μ hμ hcb δ η hδ hη u
  have hB := sa16y_cb_bound hμ hcb
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0 (Nat.zero_le _) 0)
  obtain ⟨μs, hμs_b, hμs_t⟩ := hap μ hμ.1 B hB
  have hKB : K * B ≤ K * |B| := mul_le_mul_of_nonneg_left (le_abs_self B) hK0
  have hu : ContDiff ℝ ∞ (⇑u) := u.smooth'
  have hSu : MemLp (sa16j_S d (m + 2) (⇑u)) (ENNReal.ofReal p) volume := sa16j_S_memLp (m + 2) p u
  have hWfin : wNormE (m + 2) p (⇑u) < ⊤ := by
    rw [sa16j_wNormE_eq d (m + 2) p hu hSu]
    exact (sa16j_jet_memLp d (m + 2) p hu hSu).eLpNorm_lt_top
  set S : ℝ := δ ^ (2 - θ) + η ^ (2 - θ) with hS
  set F : ℕ → Euc d → ℝ := fun n x =>
    nlCut d θ δ lam c gamma M (⇑(μs n)) u x - nlCut d θ η lam c gamma M (⇑(μs n)) u x with hF
  set F' : Euc d → ℝ := fun x =>
    nlCut d θ δ lam c gamma M μ u x - nlCut d θ η lam c gamma M μ u x with hF'
  have hbd : ∀ n, wNormE m p (F n) ≤ ENNReal.ofReal (C3 * S) * wNormE (m + 2) p (⇑u) :=
    fun n => h3 M hM (μs n) (fun j hj x => (hμs_b n j hj x).trans hKB) δ η hδ hη u
  -- pointwise convergence
  have hb0 : ∀ n y, |μs n y| ≤ K * B := by
    intro n y
    have := hμs_b n 0 (Nat.zero_le _) y
    rwa [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at this
  have hb1 : ∀ n (j : Fin d) y, |partialDeriv (fun _ : Fin 1 => j) (⇑(μs n)) y| ≤ K * B :=
    fun n j y => (sa16y_pd_le_iter _ y _).trans (hμs_b n 1 (by omega) y)
  have hl0 : ∀ y, Tendsto (fun n => μs n y) atTop (𝓝 (μ y)) := by
    intro y
    have := sa16y_pd1_tendsto (f := fun n => ⇑(μs n)) (g := μ) (j := 0)
      (fun x => hμs_t 0 (Nat.zero_le _) x) (fun i => Fin.elim0 i) y
    simpa only [sa16j_pd_zero] using this
  have hl1 : ∀ (j : Fin d) y, Tendsto (fun n => partialDeriv (fun _ : Fin 1 => j) (⇑(μs n)) y) atTop
      (𝓝 (partialDeriv (fun _ : Fin 1 => j) μ y)) := fun j y =>
    sa16y_pd1_tendsto (f := fun n => ⇑(μs n)) (g := μ) (j := 1)
      (fun x => hμs_t 1 (by omega) x) (fun _ => j) y
  have hlim : ∀ x, Tendsto (fun n => F n x) atTop (𝓝 (F' x)) := by
    intro x
    exact (sa16y_nlCut_tendsto hd hδ.1 hθ0 lam c gamma M u μ hμ.1.continuous μs hb0 hb1 hl0 hl1 x).sub
      (sa16y_nlCut_tendsto hd hη.1 hθ0 lam c gamma M u μ hμ.1.continuous μs hb0 hb1 hl0 hl1 x)
  -- the Cauchy property
  have hE0 : ∀ n x, sa16y_dev d (m + 2) μs μ n x ≤ ((m : ℝ) + 3) * (K * B + B) := by
    intro n x
    unfold sa16y_dev
    calc ∑ i ∈ Finset.range (m + 2 + 1), ‖iteratedFDeriv ℝ i (⇑(μs n)) x - iteratedFDeriv ℝ i μ x‖
        ≤ ∑ i ∈ Finset.range (m + 2 + 1), (K * B + B) := by
          refine Finset.sum_le_sum fun i hi => ?_
          have hi' : i ≤ m + 2 := by have := Finset.mem_range.1 hi; omega
          exact (norm_sub_le _ _).trans (add_le_add (hμs_b n i hi' x) (hB i hi' x))
      _ = ((m : ℝ) + 3) * (K * B + B) := by
          simp [Finset.sum_const]; ring
  have hC := sa16y_cauchy hd m θ p lam c gamma MB hθ0 hθ2 C0 hC0 h0 M hM μ hμ.1 μs hE0
    (fun j hj x => hμs_t j hj x) δ η hδ hη u
  exact sa16y_wnorm_limit m p F F' (ENNReal.ofReal (C3 * S) * wNormE (m + 2) p (⇑u))
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hWfin) hbd (Eventually.of_forall hlim) hC

end SL10

end HRS.Whole.AppendixA.Phase2SA16
