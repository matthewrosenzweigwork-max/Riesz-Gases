import HRS.MS.SA16TransferT7Aux

/-!
# S.A.16 T7: `compatible_generator_difference`

`compatibleNl δ - compatibleNl η = -γ ∑ M (spliceOdd δ - spliceOdd η)(μ ∂_j φ)`.  For Schwartz `μ` this is bounded by the
odd estimate `sa16y_spliceOdd_diff_bound` (K2 + SL2) and the Leibniz bound.  For `μ ∈ C_b^{m+2}` the Schwartz
approximants of `sa16y_approx` and the limit lemma `sa16y_wnorm_limit` are used, exactly as for SL10.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff SchwartzMap

namespace HRS.Whole.AppendixA.Phase2SA16Transfer
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16Cutoff

section T7
variable {d : ℕ}

/-- the Schwartz core estimate -/
theorem sa16y_T7_core (d : ℕ) (hd : 1 ≤ d) (m : ℕ) (θ p gamma MB : ℝ) (hθ0 : 0 < θ) (hθ2 : θ < 2)
    [Fact (2 ≤ p)] :
    ∃ C0 : ℝ, 0 < C0 ∧ ∀ M : Matrix (Fin d) (Fin d) ℝ, (∀ i j, |M i j| ≤ MB) →
      ∀ f φ : 𝓢(Euc d, ℝ), ∀ δ η : ℝ, δ ∈ Ioc (0 : ℝ) 1 → η ∈ Ioc (0 : ℝ) 1 →
      wNormE m p (fun x => compatibleNl d θ δ gamma M (⇑f) (⇑φ) x -
          compatibleNl d θ η gamma M (⇑f) (⇑φ) x) ≤
        ENNReal.ofReal (C0 * (δ ^ (2 - θ) + η ^ (2 - θ))) *
          ∑ j : Fin d, wNormE (m + 1) p (⇑(sa16y_mulS f (sa16y_dS φ j))) := by
  obtain ⟨C3, hC3, h3⟩ := sa16y_spliceOdd_diff_bound d hd m θ p hθ0 hθ2
  refine ⟨(d : ℝ) * (|gamma| * |MB| * C3) + 1, by positivity, ?_⟩
  intro M hM f φ δ η hδ hη
  set S : ℝ := δ ^ (2 - θ) + η ^ (2 - θ) with hS
  have hS0 : 0 ≤ S := add_nonneg (Real.rpow_nonneg hδ.1.le _) (Real.rpow_nonneg hη.1.le _)
  set a : Fin d → ℝ≥0∞ := fun j => wNormE (m + 1) p (⇑(sa16y_mulS f (sa16y_dS φ j))) with ha
  set v : Fin d → 𝓢(Euc d, ℝ) := fun j => sa16y_mulS f (sa16y_dS φ j) with hvd
  have hv : ∀ j, ⇑(v j) = fun y => f y * partialDeriv (fun _ : Fin 1 => j) (⇑φ) y := by
    intro j; show ⇑(sa16y_mulS f (sa16y_dS φ j)) = _; rw [sa16y_mulS_apply, sa16y_dS_apply]
  set D : Fin d → Fin d → Euc d → ℝ := fun i j x =>
    spliceOdd d θ δ i (⇑(v j)) x - spliceOdd d θ η i (⇑(v j)) x with hD
  have hfun : (fun x => compatibleNl d θ δ gamma M (⇑f) (⇑φ) x -
        compatibleNl d θ η gamma M (⇑f) (⇑φ) x) =
      fun x => ∑ i : Fin d, ∑ j : Fin d, ((-gamma) * M j i) * D i j x := by
    funext x
    simp only [compatibleNl, hD, hv]
    simp only [mul_sub, Finset.sum_sub_distrib, Finset.mul_sum, mul_assoc]
  rw [hfun]
  have T2 : ∀ i j : Fin d, wNormE m p (fun x => ((-gamma) * M j i) * D i j x) ≤
      ENNReal.ofReal (|gamma| * |MB| * C3 * S) * a j := by
    intro i j
    have hgM : |(-gamma) * M j i| ≤ |gamma| * |MB| := by
      rw [abs_mul, abs_neg]
      exact mul_le_mul_of_nonneg_left ((hM j i).trans (le_abs_self _)) (abs_nonneg _)
    calc wNormE m p (fun x => ((-gamma) * M j i) * D i j x)
        ≤ ENNReal.ofReal |(-gamma) * M j i| * wNormE m p (D i j) :=
          sa16y_wNormE_smul_le m p _ _
      _ ≤ ENNReal.ofReal |(-gamma) * M j i| * (ENNReal.ofReal (C3 * S) * a j) :=
          mul_le_mul' le_rfl (h3 δ η hδ hη i (v j))
      _ ≤ ENNReal.ofReal (|gamma| * |MB| * C3 * S) * a j := by
          refine sa16y_ofReal_mul_le (abs_nonneg _) ?_ _
          calc |(-gamma) * M j i| * (C3 * S) ≤ (|gamma| * |MB|) * (C3 * S) :=
                mul_le_mul_of_nonneg_right hgM (by positivity)
            _ = |gamma| * |MB| * C3 * S := by ring
  have T2' : wNormE m p (fun x => ∑ i : Fin d, ∑ j : Fin d, ((-gamma) * M j i) * D i j x) ≤
      ENNReal.ofReal ((d : ℝ) * (|gamma| * |MB| * C3 * S)) * ∑ j : Fin d, a j := by
    refine (sa16y_wNormE_sum_le m p Finset.univ
      (fun i x => ∑ j : Fin d, ((-gamma) * M j i) * D i j x)).trans ?_
    have hin : ∀ i : Fin d, wNormE m p (fun x => ∑ j : Fin d, ((-gamma) * M j i) * D i j x) ≤
        ENNReal.ofReal (|gamma| * |MB| * C3 * S) * ∑ j : Fin d, a j := fun i =>
      (sa16y_wNormE_sum_le m p Finset.univ (fun j x => ((-gamma) * M j i) * D i j x)).trans
        ((Finset.sum_le_sum fun j _ => T2 i j).trans (by rw [Finset.mul_sum]))
    refine (Finset.sum_le_sum fun i _ => hin i).trans (le_of_eq ?_)
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [← mul_assoc, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
  refine T2'.trans (mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl)
  nlinarith [mul_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg d) (abs_nonneg gamma)) (abs_nonneg MB))
    (mul_nonneg hC3.le hS0)]

lemma sa16y_dpd_norm' (φ : 𝓢(Euc d, ℝ)) (j : Fin d) (i : ℕ) (x : Euc d) :
    ‖iteratedFDeriv ℝ i (⇑(sa16y_dS φ j)) x‖ ≤ ‖iteratedFDeriv ℝ (i + 1) (⇑φ) x‖ := by
  rw [sa16y_dS_apply]
  exact sa16y_dpd_norm φ j i x

lemma sa16y_dS_jet (m : ℕ) (φ : 𝓢(Euc d, ℝ)) (j : Fin d) (x : Euc d) :
    ‖wJet (m + 1) (⇑(sa16y_dS φ j)) x‖ ≤ ((d : ℝ) + 1) ^ (m + 2) * ‖wJet (m + 2) (⇑φ) x‖ := by
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun τ => ?_
  rw [Real.norm_eq_abs]
  have hi : (τ.1 : ℕ) ≤ m + 1 := by have := τ.1.2; omega
  refine (sa16y_pd_le_iter _ x τ.2).trans ?_
  refine (sa16y_dpd_norm' φ j _ x).trans ?_
  refine (sa16y_iter_le_jet (⇑φ) x (n := m + 2) (l := (τ.1 : ℕ) + 1) (by omega)).trans ?_
  refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
  calc (d : ℝ) ^ ((τ.1 : ℕ) + 1) ≤ ((d : ℝ) + 1) ^ ((τ.1 : ℕ) + 1) :=
        pow_le_pow_left₀ (Nat.cast_nonneg _) (by linarith) _
    _ ≤ ((d : ℝ) + 1) ^ (m + 2) :=
        pow_le_pow_right₀ (by have : (0 : ℝ) ≤ d := Nat.cast_nonneg _; linarith) (by omega)

lemma sa16y_wnorm_dS_le (m : ℕ) (p : ℝ) [Fact (2 ≤ p)] (φ : 𝓢(Euc d, ℝ)) (j : Fin d) :
    wNormE (m + 1) p (⇑(sa16y_dS φ j)) ≤
      ENNReal.ofReal (((d : ℝ) + 1) ^ (m + 2)) * wNormE (m + 2) p (⇑φ) := by
  rw [sa16y_wnorm_jet, sa16y_wnorm_jet]
  have hφ : ContDiff ℝ ∞ (⇑φ) := φ.smooth'
  have hmeas : AEStronglyMeasurable (wJet (m + 1) (⇑(sa16y_dS φ j))) volume :=
    (sa16j_jet_cont (sa16y_dS φ j).smooth' (m + 1)).aestronglyMeasurable
  refine (eLpNorm_mono_ae_real hmeas (Eventually.of_forall (sa16y_dS_jet m φ j))).trans ?_
  have : (fun x => ((d : ℝ) + 1) ^ (m + 2) * ‖wJet (m + 2) (⇑φ) x‖) =
      ((d : ℝ) + 1) ^ (m + 2) • (fun x => ‖wJet (m + 2) (⇑φ) x‖) := by
    funext x; simp
  rw [this, eLpNorm_const_smul, eLpNorm_norm _ (sa16j_jet_cont hφ (m + 2)).aestronglyMeasurable]
  refine le_of_eq ?_
  rw [Real.enorm_eq_ofReal (by positivity)]

lemma sa16y_compNl_sub {θ δ : ℝ} (hd : 1 ≤ d) (hδ : 0 < δ) (hθ : 0 < θ) (gamma : ℝ)
    (M : Matrix (Fin d) (Fin d) ℝ) (a b φ : 𝓢(Euc d, ℝ)) (x : Euc d) :
    compatibleNl d θ δ gamma M (⇑(a - b)) (⇑φ) x =
      compatibleNl d θ δ gamma M (⇑a) (⇑φ) x - compatibleNl d θ δ gamma M (⇑b) (⇑φ) x := by
  have hos : ∀ i j : Fin d, spliceOdd d θ δ i
      (fun y => (⇑(a - b)) y * partialDeriv (fun _ : Fin 1 => j) (⇑φ) y) x =
      spliceOdd d θ δ i (fun y => a y * partialDeriv (fun _ : Fin 1 => j) (⇑φ) y) x -
        spliceOdd d θ δ i (fun y => b y * partialDeriv (fun _ : Fin 1 => j) (⇑φ) y) x := by
    intro i j
    have := sa16y_spliceOdd_sub hd hδ hθ i (sa16y_mulS a (sa16y_dS φ j)) (sa16y_mulS b (sa16y_dS φ j)) x
    rw [sa16y_mulS_apply, sa16y_mulS_apply, sa16y_dS_apply] at this
    have e : (fun y => (⇑(a - b)) y * partialDeriv (fun _ : Fin 1 => j) (⇑φ) y) =
        fun y => a y * partialDeriv (fun _ : Fin 1 => j) (⇑φ) y -
          b y * partialDeriv (fun _ : Fin 1 => j) (⇑φ) y := by
      funext y; simp [sub_mul]
    rw [e]
    exact this
  unfold compatibleNl
  simp only [hos, mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]

/-- the Cauchy estimate for the approximating differences -/
lemma sa16y_T7_cauchy (hd : 1 ≤ d) (m : ℕ) (θ p gamma MB : ℝ) (hθ0 : 0 < θ) [Fact (2 ≤ p)]
    (C0 : ℝ)
    (h0 : ∀ M : Matrix (Fin d) (Fin d) ℝ, (∀ i j, |M i j| ≤ MB) →
      ∀ f φ : 𝓢(Euc d, ℝ), ∀ δ η : ℝ, δ ∈ Ioc (0 : ℝ) 1 → η ∈ Ioc (0 : ℝ) 1 →
      wNormE m p (fun x => compatibleNl d θ δ gamma M (⇑f) (⇑φ) x -
          compatibleNl d θ η gamma M (⇑f) (⇑φ) x) ≤
        ENNReal.ofReal (C0 * (δ ^ (2 - θ) + η ^ (2 - θ))) *
          ∑ j : Fin d, wNormE (m + 1) p (⇑(sa16y_mulS f (sa16y_dS φ j))))
    (M : Matrix (Fin d) (Fin d) ℝ) (hM : ∀ i j, |M i j| ≤ MB)
    (μ : Euc d → ℝ) (μs : ℕ → 𝓢(Euc d, ℝ)) (hμ : ContDiff ℝ ((m + 1 : ℕ) : WithTop ℕ∞) μ) {E0 : ℝ}
    (hE0 : ∀ n x, sa16y_dev d (m + 1) μs μ n x ≤ E0)
    (hconv : ∀ j ≤ m + 1, ∀ x, Tendsto (fun n => ‖iteratedFDeriv ℝ j (⇑(μs n)) x -
      iteratedFDeriv ℝ j μ x‖) atTop (𝓝 0))
    (δ η : ℝ) (hδ : δ ∈ Ioc (0 : ℝ) 1) (hη : η ∈ Ioc (0 : ℝ) 1) (φ : 𝓢(Euc d, ℝ)) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, ∀ l ≥ N,
      wNormE m p (fun x => (compatibleNl d θ δ gamma M (⇑(μs n)) (⇑φ) x -
          compatibleNl d θ η gamma M (⇑(μs n)) (⇑φ) x) -
        (compatibleNl d θ δ gamma M (⇑(μs l)) (⇑φ) x - compatibleNl d θ η gamma M (⇑(μs l)) (⇑φ) x)) ≤
        ENNReal.ofReal ε := by
  intro ε hε
  have hp1 : (1 : ℝ) ≤ p := by have : (2 : ℝ) ≤ p := Fact.out; linarith
  have hφ : ContDiff ℝ ∞ (⇑φ) := φ.smooth'
  have hSφ : MemLp (sa16j_S d (m + 2) (⇑φ)) (ENNReal.ofReal p) volume := sa16j_S_memLp (m + 2) p φ
  set S : ℝ := δ ^ (2 - θ) + η ^ (2 - θ) with hS
  set c1 : ℝ := ((d : ℝ) + 1) ^ (m + 1) * ((d : ℝ) + 1) ^ (m + 2) with hc1
  have hc10 : 0 ≤ c1 := by positivity
  set J : Euc d → ℝ := fun x => c1 * ‖wJet (m + 2) (⇑φ) x‖ with hJ
  have hJc : Continuous J := continuous_const.mul (sa16j_jet_cont hφ (m + 2)).norm
  have hJmem : MemLp J (ENNReal.ofReal p) volume :=
    ((sa16j_jet_memLp d (m + 2) p hφ hSφ).norm).const_mul c1
  set G : ℕ → ℝ≥0∞ := fun n =>
    eLpNorm (fun x => sa16y_dev d (m + 1) μs μ n x * J x) (ENNReal.ofReal p) volume with hG
  have hGlim : Tendsto G atTop (𝓝 0) :=
    sa16y_dom_lp p hp1 (sa16y_dev d (m + 1) μs μ) J (fun n => sa16y_dev_cont (m + 1) μs hμ n)
      (sa16y_dev_nonneg d (m + 1) μs μ) hE0
      (fun x => by
        unfold sa16y_dev
        simpa using tendsto_finsetSum (Finset.range (m + 1 + 1)) fun i hi =>
          hconv i (by have := Finset.mem_range.1 hi; omega) x)
      hJc hJmem
  have hdevc : ∀ n, Continuous (sa16y_dev d (m + 1) μs μ n) := fun n => sa16y_dev_cont (m + 1) μs hμ n
  have hmeasJ : ∀ n, AEStronglyMeasurable (fun x => sa16y_dev d (m + 1) μs μ n x * J x) volume :=
    fun n => ((hdevc n).mul hJc).aestronglyMeasurable
  have hsumle : ∀ n l, eLpNorm (fun x => (sa16y_dev d (m + 1) μs μ n x + sa16y_dev d (m + 1) μs μ l x) * J x)
      (ENNReal.ofReal p) volume ≤ G n + G l := by
    intro n l
    have : (fun x => (sa16y_dev d (m + 1) μs μ n x + sa16y_dev d (m + 1) μs μ l x) * J x) =
        (fun x => sa16y_dev d (m + 1) μs μ n x * J x) + (fun x => sa16y_dev d (m + 1) μs μ l x * J x) := by
      funext x; simp [add_mul]
    rw [this]
    exact eLpNorm_add_le (by simpa using hp1)
  have hB' : ∀ n l (j : Fin d), wNormE (m + 1) p (⇑(sa16y_mulS (μs n - μs l) (sa16y_dS φ j))) ≤
      G n + G l := by
    intro n l j
    rw [sa16y_wnorm_jet]
    refine le_trans ?_ (hsumle n l)
    have hmeas : AEStronglyMeasurable (wJet (m + 1) (⇑(sa16y_mulS (μs n - μs l) (sa16y_dS φ j)))) volume :=
      (sa16j_jet_cont (sa16y_mulS (μs n - μs l) (sa16y_dS φ j)).smooth' (m + 1)).aestronglyMeasurable
    refine eLpNorm_mono_ae_real hmeas (Eventually.of_forall fun x => ?_)
    rw [sa16y_mulS_apply]
    have := sa16y_prod_jet_le (f := ⇑(μs n - μs l)) (g := ⇑(sa16y_dS φ j)) (μs n - μs l).smooth'
      (sa16y_dS φ j).smooth' (m + 1) x
      (B := sa16y_dev d (m + 1) μs μ n x + sa16y_dev d (m + 1) μs μ l x)
      (fun i hi => sa16y_dev_diff (m + 1) μs μ n l x hi)
    refine this.trans ?_
    have hsum0 : 0 ≤ sa16y_dev d (m + 1) μs μ n x + sa16y_dev d (m + 1) μs μ l x :=
      add_nonneg (sa16y_dev_nonneg _ _ _ _ _ _) (sa16y_dev_nonneg _ _ _ _ _ _)
    calc (sa16y_dev d (m + 1) μs μ n x + sa16y_dev d (m + 1) μs μ l x) * ((d : ℝ) + 1) ^ (m + 1) *
          ‖wJet (m + 1) (⇑(sa16y_dS φ j)) x‖
        ≤ (sa16y_dev d (m + 1) μs μ n x + sa16y_dev d (m + 1) μs μ l x) * ((d : ℝ) + 1) ^ (m + 1) *
          (((d : ℝ) + 1) ^ (m + 2) * ‖wJet (m + 2) (⇑φ) x‖) :=
          mul_le_mul_of_nonneg_left (sa16y_dS_jet m φ j x) (by positivity)
      _ = (sa16y_dev d (m + 1) μs μ n x + sa16y_dev d (m + 1) μs μ l x) * J x := by
          simp only [hJ, hc1]; ring
  set K0 : ℝ≥0∞ := ENNReal.ofReal (C0 * S) * (d : ℝ≥0∞) with hK0
  have hK0top : K0 ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.natCast_ne_top d)
  have hKG : Tendsto (fun n => K0 * G n) atTop (𝓝 0) := by
    have := ENNReal.Tendsto.const_mul hGlim (Or.inr hK0top)
    simpa using this
  have hev := (ENNReal.tendsto_nhds_zero.1 hKG) (ENNReal.ofReal (ε / 2)) (by simpa using (by positivity : 0 < ε / 2))
  obtain ⟨N, hN⟩ := eventually_atTop.1 hev
  refine ⟨N, fun n hn l hl => ?_⟩
  have hfd : (fun x => (compatibleNl d θ δ gamma M (⇑(μs n)) (⇑φ) x -
          compatibleNl d θ η gamma M (⇑(μs n)) (⇑φ) x) -
        (compatibleNl d θ δ gamma M (⇑(μs l)) (⇑φ) x - compatibleNl d θ η gamma M (⇑(μs l)) (⇑φ) x)) =
      fun x => compatibleNl d θ δ gamma M (⇑(μs n - μs l)) (⇑φ) x -
        compatibleNl d θ η gamma M (⇑(μs n - μs l)) (⇑φ) x := by
    funext x
    rw [sa16y_compNl_sub hd hδ.1 hθ0 gamma M (μs n) (μs l) φ x,
      sa16y_compNl_sub hd hη.1 hθ0 gamma M (μs n) (μs l) φ x]
    ring
  rw [hfd]
  refine (h0 M hM (μs n - μs l) φ δ η hδ hη).trans ?_
  have hsum : ∑ j : Fin d, wNormE (m + 1) p (⇑(sa16y_mulS (μs n - μs l) (sa16y_dS φ j))) ≤
      (d : ℝ≥0∞) * (G n + G l) := by
    calc _ ≤ ∑ j : Fin d, (G n + G l) := Finset.sum_le_sum fun j _ => hB' n l j
      _ = (d : ℝ≥0∞) * (G n + G l) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  calc ENNReal.ofReal (C0 * S) * ∑ j : Fin d, wNormE (m + 1) p (⇑(sa16y_mulS (μs n - μs l) (sa16y_dS φ j)))
      ≤ ENNReal.ofReal (C0 * S) * ((d : ℝ≥0∞) * (G n + G l)) := mul_le_mul' le_rfl hsum
    _ = K0 * G n + K0 * G l := by rw [hK0, ← mul_assoc, mul_add]
    _ ≤ ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) := add_le_add (hN n hn) (hN l hl)
    _ = ENNReal.ofReal ε := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1; ring

theorem compatible_generator_difference (d m : ℕ) (hd : 1 ≤ d)
    (θ p gamma MB B : ℝ) (hθ0 : 0 < θ) (hθ2 : θ < 2) [Fact (2 ≤ p)] :
    ∃ C : ℝ, 0 < C ∧ ∀ M : Matrix (Fin d) (Fin d) ℝ,
      (∀ i j, |M i j| ≤ MB) → ∀ μ : Euc d → ℝ, MemCb (m+2) μ → cbNorm (m+2) μ ≤ B →
      ∀ δ η : ℝ, δ ∈ Ioc (0 : ℝ) 1 → η ∈ Ioc (0 : ℝ) 1 →
      ∀ φ : Euc d → ℝ, IsCcInfty φ →
        wNormE m p (fun x => compatibleNl d θ δ gamma M μ φ x-
          compatibleNl d θ η gamma M μ φ x) ≤
          ENNReal.ofReal (C*(δ^(2-θ)+η^(2-θ)))*wNormE (m+2) p φ := by
  obtain ⟨K, hK0, hap⟩ := sa16y_approx d (m + 1)
  obtain ⟨C0, hC0, h0⟩ := sa16y_T7_core d hd m θ p gamma MB hθ0 hθ2
  set Lb : ℝ := K * |B| * ((d : ℝ) + 1) ^ (m + 1) with hLb
  set Ld : ℝ := ((d : ℝ) + 1) ^ (m + 2) with hLd
  have hLb0 : 0 ≤ Lb := by positivity
  have hLd0 : 0 ≤ Ld := by positivity
  refine ⟨C0 * ((d : ℝ) * (Lb * Ld)) + 1, by positivity, ?_⟩
  intro M hM μ hμ hcb δ η hδ hη φ hφ
  set φS : 𝓢(Euc d, ℝ) := hφ.2.toSchwartzMap hφ.1 with hφS
  have hφe : (φ : Euc d → ℝ) = ⇑φS := rfl
  rw [hφe]
  have hB := sa16y_cb_bound hμ hcb
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0 (Nat.zero_le _) 0)
  have hμ1 : ContDiff ℝ ((m + 1 : ℕ) : WithTop ℕ∞) μ := hμ.1.of_le (by exact_mod_cast Nat.le_succ _)
  obtain ⟨μs, hμs_b, hμs_t⟩ := hap μ hμ1 B (fun j hj x => hB j (by omega) x)
  have hKB : K * B ≤ K * |B| := mul_le_mul_of_nonneg_left (le_abs_self B) hK0
  have hu : ContDiff ℝ ∞ (⇑φS) := φS.smooth'
  have hSu : MemLp (sa16j_S d (m + 2) (⇑φS)) (ENNReal.ofReal p) volume := sa16j_S_memLp (m + 2) p φS
  have hWfin : wNormE (m + 2) p (⇑φS) < ⊤ := by
    rw [sa16j_wNormE_eq d (m + 2) p hu hSu]
    exact (sa16j_jet_memLp d (m + 2) p hu hSu).eLpNorm_lt_top
  set S : ℝ := δ ^ (2 - θ) + η ^ (2 - θ) with hS
  have hS0 : 0 ≤ S := add_nonneg (Real.rpow_nonneg hδ.1.le _) (Real.rpow_nonneg hη.1.le _)
  set W : ℝ≥0∞ := wNormE (m + 2) p (⇑φS) with hW
  set F : ℕ → Euc d → ℝ := fun n x =>
    compatibleNl d θ δ gamma M (⇑(μs n)) (⇑φS) x - compatibleNl d θ η gamma M (⇑(μs n)) (⇑φS) x with hF
  set F' : Euc d → ℝ := fun x =>
    compatibleNl d θ δ gamma M μ (⇑φS) x - compatibleNl d θ η gamma M μ (⇑φS) x with hF'
  -- uniform bound
  have hbd : ∀ n, wNormE m p (F n) ≤
      ENNReal.ofReal ((C0 * ((d : ℝ) * (Lb * Ld)) + 1) * S) * W := by
    intro n
    refine (h0 M hM (μs n) φS δ η hδ hη).trans ?_
    have hj : ∀ j : Fin d, wNormE (m + 1) p (⇑(sa16y_mulS (μs n) (sa16y_dS φS j))) ≤
        ENNReal.ofReal Lb * (ENNReal.ofReal Ld * W) := by
      intro j
      refine (sa16y_mulS_wnorm (m + 1) p (μs n) (sa16y_dS φS j)
        (B := K * |B|) (fun i hi x => (hμs_b n i hi x).trans hKB)).trans ?_
      exact mul_le_mul' (le_of_eq (by rw [hLb])) (sa16y_wnorm_dS_le m p φS j)
    have hsum : ∑ j : Fin d, wNormE (m + 1) p (⇑(sa16y_mulS (μs n) (sa16y_dS φS j))) ≤
        ENNReal.ofReal ((d : ℝ) * (Lb * Ld)) * W := by
      calc _ ≤ ∑ j : Fin d, ENNReal.ofReal Lb * (ENNReal.ofReal Ld * W) := Finset.sum_le_sum fun j _ => hj j
        _ = ENNReal.ofReal ((d : ℝ) * (Lb * Ld)) * W := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← mul_assoc,
              ← mul_assoc, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _),
              ← ENNReal.ofReal_mul (by positivity)]
            exact congrArg (fun r => ENNReal.ofReal r * W) (by ring)
    calc ENNReal.ofReal (C0 * S) * ∑ j : Fin d, wNormE (m + 1) p (⇑(sa16y_mulS (μs n) (sa16y_dS φS j)))
        ≤ ENNReal.ofReal (C0 * S) * (ENNReal.ofReal ((d : ℝ) * (Lb * Ld)) * W) := mul_le_mul' le_rfl hsum
      _ ≤ ENNReal.ofReal ((C0 * ((d : ℝ) * (Lb * Ld)) + 1) * S) * W := by
          refine sa16y_ofReal_mul_le (by positivity) ?_ _
          nlinarith [mul_nonneg hC0.le hS0, mul_nonneg (mul_nonneg hC0.le hS0)
            (mul_nonneg (Nat.cast_nonneg d) (mul_nonneg hLb0 hLd0))]
  -- pointwise convergence
  have hb0 : ∀ n y, |μs n y| ≤ K * B := by
    intro n y
    have := hμs_b n 0 (Nat.zero_le _) y
    rwa [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at this
  have hl0 : ∀ y, Tendsto (fun n => μs n y) atTop (𝓝 (μ y)) := by
    intro y
    have := sa16y_pd1_tendsto (f := fun n => ⇑(μs n)) (g := μ) (j := 0)
      (fun x => hμs_t 0 (Nat.zero_le _) x) (fun i => Fin.elim0 i) y
    simpa only [sa16j_pd_zero] using this
  have hsplice : ∀ (δ' : ℝ), 0 < δ' → ∀ x, Tendsto (fun n => compatibleNl d θ δ' gamma M (⇑(μs n)) (⇑φS) x)
      atTop (𝓝 (compatibleNl d θ δ' gamma M μ (⇑φS) x)) := by
    intro δ' hδ' x
    unfold compatibleNl
    refine Tendsto.const_mul _ (tendsto_finsetSum _ fun i _ => tendsto_finsetSum _ fun j _ => ?_)
    refine Tendsto.const_mul _ ?_
    obtain ⟨Bd, hBd⟩ := sa16j_schwartz_bdd (sa16y_dS φS j)
    have hpd : ∀ y, |partialDeriv (fun _ : Fin 1 => j) (⇑φS) y| ≤ Bd := fun y => by
      rw [← sa16y_dS_apply]; exact hBd y
    have hdφ : Integrable (⇑(sa16y_dS φS j)) := (sa16y_dS φS j).integrable
    refine sa16y_spliceOdd_tendsto hd hδ' hθ0 i
      (w := fun n y => μs n y * partialDeriv (fun _ : Fin 1 => j) (⇑φS) y)
      (w' := fun y => μ y * partialDeriv (fun _ : Fin 1 => j) (⇑φS) y)
      (fun n => (μs n).continuous.mul (sa16y_pd1_continuous φS j))
      (hμ.1.continuous.mul (sa16y_pd1_continuous φS j)) (Bw := K * B * Bd)
      (fun n y => by
        rw [abs_mul]; exact mul_le_mul (hb0 n y) (hpd y) (abs_nonneg _) (by positivity))
      (fun n => by
        refine Integrable.mono' (hdφ.norm.const_mul (K * B)) ?_ (Eventually.of_forall fun y => ?_)
        · exact ((μs n).continuous.mul (sa16y_pd1_continuous φS j)).aestronglyMeasurable
        · rw [Real.norm_eq_abs, abs_mul, ← sa16y_dS_apply]
          exact mul_le_mul (hb0 n y) (by simp) (abs_nonneg _) (by positivity))
      (H := fun y => K * B * ‖sa16y_dS φS j y‖) (hdφ.norm.const_mul (K * B))
      (fun n y => by
        rw [abs_mul, ← sa16y_dS_apply]
        exact mul_le_mul (hb0 n y) (by simp) (abs_nonneg _) (by positivity))
      (fun y => (hl0 y).mul_const _) x
  have hlim : ∀ x, Tendsto (fun n => F n x) atTop (𝓝 (F' x)) := fun x =>
    (hsplice δ hδ.1 x).sub (hsplice η hη.1 x)
  -- Cauchy
  have hE0 : ∀ n x, sa16y_dev d (m + 1) μs μ n x ≤ ((m : ℝ) + 2) * (K * B + B) := by
    intro n x
    unfold sa16y_dev
    calc ∑ i ∈ Finset.range (m + 1 + 1), ‖iteratedFDeriv ℝ i (⇑(μs n)) x - iteratedFDeriv ℝ i μ x‖
        ≤ ∑ i ∈ Finset.range (m + 1 + 1), (K * B + B) := by
          refine Finset.sum_le_sum fun i hi => ?_
          have hi' : i ≤ m + 1 := by have := Finset.mem_range.1 hi; omega
          exact (norm_sub_le _ _).trans (add_le_add (hμs_b n i hi' x) (hB i (by omega) x))
      _ = ((m : ℝ) + 2) * (K * B + B) := by
          simp [Finset.sum_const]; ring
  have hC := sa16y_T7_cauchy hd m θ p gamma MB hθ0 C0 h0 M hM μ μs hμ1 hE0
    (fun j hj x => hμs_t j hj x) δ η hδ hη φS
  exact sa16y_wnorm_limit m p F F' (ENNReal.ofReal ((C0 * ((d : ℝ) * (Lb * Ld)) + 1) * S) * W)
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hWfin) hbd (Eventually.of_forall hlim) hC

end T7

end HRS.Whole.AppendixA.Phase2SA16Transfer
