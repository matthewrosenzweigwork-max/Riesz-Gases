import HRS.MS.FixEqP3Aux4
import HRS.MS.FixEqP1Aux3

/-!
# S5.7 `fixed_equation` (worker S57P), part 20: the Wiener integral of a test function is the pairing with the noise field

For an isonormal process `W` and the field `X` of `s57p_noise_exists` (`coord_α (X_t) = W(κ_t α)` a.s.), the pairing `eval (X_t) φ`
of `φ ∈ Σ^m` equals `W(k)` a.s. as soon as `k ∈ H` is the limit of the finite combinations `∑_{α ∈ F} b_α κ_t α`
(`s57p_eval_ae`); hence the finite-dimensional law of `(eval (X_{t_a}) φ_a)_a` is the Gaussian with the Gram covariance of the `k`'s
(`s57p_noise_law`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace HRS.MS.FixEq

open HRS HRS.Whole HRS.MS.U10

variable {d : ℕ}

section Iso

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  {Ω₀ : Type} [MeasurableSpace Ω₀] {Q : Measure Ω₀} [IsProbabilityMeasure Q] {W : H → Ω₀ → ℝ}

theorem s57p_W_finsum (hI : Sb7Iso Q W) {ι : Type*} (F : Finset ι) (c : ι → ℝ) (v : ι → H) :
    W (∑ α ∈ F, c α • v α) =ᵐ[Q] fun w => ∑ α ∈ F, c α * W (v α) w := by
  classical
  induction F using Finset.induction_on with
  | empty =>
    have := hI.lin 0 0 0 0
    simpa using this
  | insert β F hβ ih =>
    have h1 := hI.lin (c β) 1 (v β) (∑ α ∈ F, c α • v α)
    rw [Finset.sum_insert hβ]
    filter_upwards [h1, ih] with w hw hw2
    rw [one_smul] at hw
    rw [hw, hw2, Finset.sum_insert hβ]; ring

theorem s57p_eLpNorm_W (hI : Sb7Iso Q W) (h : H) : eLpNorm (W h) 2 Q = ENNReal.ofReal ‖h‖ := by
  rw [(hI.memLp h).eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)]
  congr 1
  have e : ∫ w, ‖W h w‖ ^ ((2 : ℝ≥0∞).toReal) ∂Q = ‖h‖ ^ 2 := by
    have h1 : ∫ w, W h w * W h w ∂Q = ‖h‖ ^ 2 := by
      rw [hI.inner, real_inner_self_eq_norm_sq]
    rw [← h1]
    refine integral_congr_ae (Eventually.of_forall fun w => ?_)
    simp only [ENNReal.toReal_ofNat, Real.rpow_two, norm_pow, Real.norm_eq_abs, sq_abs]
    ring
  rw [e]
  simp only [ENNReal.toReal_ofNat]
  rw [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _)]
  norm_num

theorem s57p_eval_ae (hI : Sb7Iso Q W) {m : ℝ} {T : ℝ} (κ : ℝ → MultiIndex d → H) {X : ℝ → Ω₀ → OscDual d m}
    (hX : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ α, ∀ᵐ w ∂Q, OscDual.coord (X t w) α = W (κ t α) w) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) T) {φ : Euc d → ℝ} (hφ : IsOscTest m φ) {k : H}
    (hk : ∀ ε > 0, ∃ F₀ : Finset (MultiIndex d), ∀ F : Finset (MultiIndex d), F₀ ⊆ F →
      ‖k - ∑ α ∈ F, s57pb d m φ α • κ t α‖ ≤ ε) :
    (fun w => OscDual.eval (X t w) φ) =ᵐ[Q] W k := by
  classical
  set S : Finset (MultiIndex d) → H := fun F => ∑ α ∈ F, s57pb d m φ α • κ t α with hS
  set f : Finset (MultiIndex d) → Ω₀ → ℝ := fun F => W (S F) with hf
  -- convergence in measure
  have hmeas : TendstoInMeasure Q f atTop (W k) := by
    refine tendstoInMeasure_of_tendsto_eLpNorm (p := 2) (by norm_num) ?_
    have hae : ∀ F, eLpNorm (f F - W k) 2 Q = ENNReal.ofReal ‖S F - k‖ := by
      intro F
      have e : S F - k = (1 : ℝ) • S F + (-1 : ℝ) • k := by simp [sub_eq_add_neg]
      have := hI.lin 1 (-1) (S F) k
      rw [← e] at this
      rw [← s57p_eLpNorm_W hI (S F - k)]
      refine eLpNorm_congr_ae ?_
      filter_upwards [this] with w hw
      simp only [Pi.sub_apply, hf]
      rw [hw]; ring
    simp_rw [hae]
    rw [ENNReal.tendsto_nhds_zero]
    intro ε hε
    by_cases htop : ε = ⊤
    · exact Eventually.of_forall fun _ => by simp [htop]
    obtain ⟨F₀, hF₀⟩ := hk ε.toReal (ENNReal.toReal_pos hε.ne' htop)
    refine eventually_atTop.2 ⟨F₀, fun F hF => ?_⟩
    have := hF₀ F hF
    rw [norm_sub_rev] at this
    calc ENNReal.ofReal ‖S F - k‖ ≤ ENNReal.ofReal ε.toReal := ENNReal.ofReal_le_ofReal this
      _ = ε := ENNReal.ofReal_toReal htop
  obtain ⟨ns, hns, hae⟩ := hmeas.exists_seq_tendsto_ae'
  -- a.e. pointwise convergence of the pairings
  have hcoord : ∀ᵐ w ∂Q, ∀ α, OscDual.coord (X t w) α = W (κ t α) w := ae_all_iff.2 (hX t ht)
  have hfin : ∀ F : Finset (MultiIndex d), ∀ᵐ w ∂Q, f F w = ∑ α ∈ F, s57pb d m φ α * W (κ t α) w := fun F =>
    s57p_W_finsum hI F (s57pb d m φ) (κ t)
  have hfin' : ∀ᵐ w ∂Q, ∀ n, f (ns n) w = ∑ α ∈ ns n, s57pb d m φ α * W (κ t α) w :=
    ae_all_iff.2 fun n => hfin (ns n)
  have hb2 : Summable fun α : MultiIndex d => (s57pb d m φ α) ^ 2 := by
    refine hφ.2.2.congr fun α => ?_
    unfold s57pb
    rw [mul_pow, rpow_half_sq _ _ (oscEv_pos α)]
  filter_upwards [hcoord, hfin', hae] with w hw hfw haw
  have hsum2 : Summable fun α : MultiIndex d => (OscDual.coord (X t w) α) ^ 2 := by
    have := (lp.memℓp (X t w : lp (fun _ : MultiIndex d => ℝ) 2))
    rw [memℓp_two_iff] at this
    simpa [Real.norm_eq_abs, sq_abs, OscDual.coord] using this
  have hs : Summable fun α : MultiIndex d => s57pb d m φ α * OscDual.coord (X t w) α := by
    refine Summable.of_norm_bounded ((hb2.add hsum2).div_const 2) fun α => ?_
    rw [Real.norm_eq_abs, abs_mul]
    have := two_mul_le_add_sq |s57pb d m φ α| |OscDual.coord (X t w) α|
    rw [sq_abs, sq_abs] at this
    linarith
  have hev : OscDual.eval (X t w) φ = ∑' α, s57pb d m φ α * OscDual.coord (X t w) α := by
    unfold OscDual.eval
    refine tsum_congr fun α => ?_
    unfold OscDual.hermiteCoeff s57pb
    ring
  have hT : Tendsto (fun i => f (ns i) w) atTop (𝓝 (OscDual.eval (X t w) φ)) := by
    rw [hev]
    have h2 : Tendsto (fun F : Finset (MultiIndex d) => ∑ α ∈ F, s57pb d m φ α * OscDual.coord (X t w) α) atTop
        (𝓝 (∑' α, s57pb d m φ α * OscDual.coord (X t w) α)) := hs.hasSum
    refine (h2.comp hns).congr fun i => ?_
    simp only [Function.comp_apply]
    rw [hfw i]
    exact Finset.sum_congr rfl fun α _ => by rw [hw α]
  exact tendsto_nhds_unique hT haw

theorem s57p_noise_law (hI : Sb7Iso Q W)
    (hjoint : ∀ (κ : Type) [Fintype κ] [DecidableEq κ] (h : κ → H),
      Q.map (fun w => (WithLp.toLp 2 (fun a => W (h a) w) : EuclideanSpace ℝ κ)) =
        multivariateGaussian 0 (Matrix.of fun a b => inner ℝ (h a) (h b)))
    {m : ℝ} {T : ℝ} (κ : ℝ → MultiIndex d → H) {X : ℝ → Ω₀ → OscDual d m}
    (hX : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ α, ∀ᵐ w ∂Q, OscDual.coord (X t w) α = W (κ t α) w)
    {kφ : ℝ → (Euc d → ℝ) → H}
    (hk : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ φ : Euc d → ℝ, IsOscTest m φ → ∀ ε > 0,
      ∃ F₀ : Finset (MultiIndex d), ∀ F : Finset (MultiIndex d), F₀ ⊆ F →
        ‖kφ t φ - ∑ α ∈ F, s57pb d m φ α • κ t α‖ ≤ ε)
    (p : ℕ) (ts : Fin p → ℝ) (φ : Fin p → Euc d → ℝ) (hts : ∀ a, ts a ∈ Set.Icc (0 : ℝ) T)
    (hφ : ∀ a, IsOscTest m (φ a)) :
    Q.map (fun w => (WithLp.toLp 2 (fun a => OscDual.eval (X (ts a) w) (φ a)) : EuclideanSpace ℝ (Fin p))) =
      multivariateGaussian 0 (Matrix.of fun a b => inner ℝ (kφ (ts a) (φ a)) (kφ (ts b) (φ b))) := by
  rw [← hjoint (Fin p) (fun a => kφ (ts a) (φ a))]
  refine Measure.map_congr ?_
  have h : ∀ᵐ w ∂Q, ∀ a, OscDual.eval (X (ts a) w) (φ a) = W (kφ (ts a) (φ a)) w :=
    ae_all_iff.2 fun a => s57p_eval_ae hI κ hX (hts a) (hφ a) (hk (ts a) (hts a) (φ a) (hφ a))
  filter_upwards [h] with w hw
  congr 1
  funext a
  exact hw a

end Iso

end HRS.MS.FixEq
