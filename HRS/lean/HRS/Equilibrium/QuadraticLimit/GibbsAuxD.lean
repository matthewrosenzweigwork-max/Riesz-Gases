import HRS.Equilibrium.QuadraticLimit.GibbsAuxC

/-!
# Lemma 7.5, `q08_gibbs_approx`: the abstract approximation theorem (prefix `q08gl_`)

Combination of the replacement chain, the limit `N → ∞` and the removal of the truncation of the
limit weight, with the choice of the truncation level `R` and the approximation accuracy `δ`.
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.Q08

/-- The error of the replacement chain of `q08gl_chain` (with `θ = ξ = ρ = δ`). -/
def q08gl_Chain (c₀ K M z₀ A₂ A₃ B β R δ : ℝ) : ℝ :=
  (K / z₀) * (c₀ * B * Real.sqrt (A₃ / R)) + (M / z₀) * (A₂ / R) +
      (K / z₀) * (2 * (c₀ * δ * Real.sqrt A₂)) +
      ((K / z₀) * (c₀ * (B + δ) * (Real.sqrt β * R * δ)) + (M / z₀) * (β * R * δ ^ 2)) +
      (2 * (A₂ / R + β * R * δ ^ 2 + δ) / z₀ ^ 2) *
        (M * Real.sqrt (2 * A₂ + 2) + (2 * K / z₀) * (c₀ * (B + δ) * (2 * A₂ + 2)))

/-- The error of the removal of the truncation of the limit weight. -/
def q08gl_G (c₀ K M z₀ B₂ B₃ Bf R : ℝ) : ℝ :=
  (2 * K / z₀) * ((2 / z₀) * (c₀ * Bf * Real.sqrt (B₃ / R)) * Real.sqrt B₂) + (2 * M / z₀) * (B₂ / R) +
    (4 * B₂ / (R * z₀ ^ 2)) * (M * Real.sqrt B₂ + (2 * K / z₀) * (c₀ * Bf * B₂))

theorem q08gl_select (c₀ K M z₀ A₂ A₃ B β B₂ B₃ Bf : ℝ) (hc₀ : 0 ≤ c₀) (hK : 0 ≤ K) (hM : 0 ≤ M)
    (hz₀ : 0 < z₀) (hA₂ : 0 ≤ A₂) (hA₃ : 0 ≤ A₃) (hB : 0 ≤ B) (hβ : 0 ≤ β) (hB₂ : 0 ≤ B₂)
    (hB₃ : 0 ≤ B₃) (hBf : 0 ≤ Bf) (η : ℝ) (hη : 0 < η) :
    ∃ R : ℝ, 0 < R ∧ ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ A₂ / R + β * R * δ ^ 2 + δ ≤ z₀ / 2 ∧
      β * R ^ 2 * δ ^ 2 ≤ 1 ∧ q08gl_Chain c₀ K M z₀ A₂ A₃ B β R δ + q08gl_G c₀ K M z₀ B₂ B₃ Bf R ≤ η := by
  -- the limit R → ∞ at δ = 0
  have hu : ∀ c : ℝ, Tendsto (fun R : ℝ => c / R) atTop (𝓝 0) := fun c =>
    tendsto_const_nhds.div_atTop tendsto_id
  have hus : ∀ c : ℝ, Tendsto (fun R : ℝ => Real.sqrt (c / R)) atTop (𝓝 0) := fun c => by
    have := (Real.continuous_sqrt.tendsto 0).comp (hu c)
    simpa [Function.comp_def] using this
  set Ab := 2 * A₂ + 2 with hAb
  set a1 := K / z₀ * (c₀ * B) with ha1
  set a2 := M / z₀ + 2 / z₀ ^ 2 * (M * Real.sqrt Ab + (2 * K / z₀) * (c₀ * B * Ab)) with ha2
  set a3 := (2 * K / z₀) * ((2 / z₀) * (c₀ * Bf) * Real.sqrt B₂) with ha3
  set a4 := 2 * M / z₀ + 4 / z₀ ^ 2 * (M * Real.sqrt B₂ + (2 * K / z₀) * (c₀ * Bf * B₂)) with ha4
  have hg : ∀ R : ℝ, q08gl_Chain c₀ K M z₀ A₂ A₃ B β R 0 + q08gl_G c₀ K M z₀ B₂ B₃ Bf R =
      a1 * Real.sqrt (A₃ / R) + a2 * (A₂ / R) + a3 * Real.sqrt (B₃ / R) + a4 * (B₂ / R) := by
    intro R
    unfold q08gl_Chain q08gl_G
    simp only [ha1, ha2, ha3, ha4, hAb]
    ring
  have hlim : Tendsto (fun R : ℝ => q08gl_Chain c₀ K M z₀ A₂ A₃ B β R 0 + q08gl_G c₀ K M z₀ B₂ B₃ Bf R)
      atTop (𝓝 0) := by
    simp_rw [hg]
    have := (((((hus A₃).const_mul a1).add ((hu A₂).const_mul a2)).add ((hus B₃).const_mul a3)).add
      ((hu B₂).const_mul a4))
    simpa using this
  have h1 : ∀ᶠ R : ℝ in atTop, q08gl_Chain c₀ K M z₀ A₂ A₃ B β R 0 + q08gl_G c₀ K M z₀ B₂ B₃ Bf R < η / 2 :=
    hlim.eventually (gt_mem_nhds (by linarith))
  have h2 : ∀ᶠ R : ℝ in atTop, A₂ / R < z₀ / 4 := (hu A₂).eventually (gt_mem_nhds (by linarith))
  have h3 : ∀ᶠ R : ℝ in atTop, 0 < R := eventually_gt_atTop 0
  obtain ⟨R, hR1, hR2, hR3⟩ := (h1.and (h2.and h3)).exists
  -- now δ → 0 at fixed R
  have hcont : Continuous (fun δ : ℝ => q08gl_Chain c₀ K M z₀ A₂ A₃ B β R δ + q08gl_G c₀ K M z₀ B₂ B₃ Bf R) := by
    unfold q08gl_Chain
    fun_prop
  have hev1 : ∀ᶠ δ : ℝ in 𝓝 0, q08gl_Chain c₀ K M z₀ A₂ A₃ B β R δ + q08gl_G c₀ K M z₀ B₂ B₃ Bf R < η / 2 := by
    exact (hcont.tendsto 0).eventually (gt_mem_nhds hR1)
  have hev2 : ∀ᶠ δ : ℝ in 𝓝 0, A₂ / R + β * R * δ ^ 2 + δ < z₀ / 2 := by
    have hc : Continuous (fun δ : ℝ => A₂ / R + β * R * δ ^ 2 + δ) := by fun_prop
    exact (hc.tendsto 0).eventually (gt_mem_nhds (by simp; linarith))
  have hev3 : ∀ᶠ δ : ℝ in 𝓝 0, β * R ^ 2 * δ ^ 2 < 1 := by
    have hc : Continuous (fun δ : ℝ => β * R ^ 2 * δ ^ 2) := by fun_prop
    exact (hc.tendsto 0).eventually (gt_mem_nhds (by simp))
  have hev4 : ∀ᶠ δ : ℝ in 𝓝 0, δ < 1 := gt_mem_nhds (by norm_num)
  have hpos : ∀ᶠ δ : ℝ in 𝓝[>] 0, 0 < δ := self_mem_nhdsWithin
  have hall : ∀ᶠ δ : ℝ in 𝓝[>] 0, 0 < δ ∧ δ < 1 ∧ A₂ / R + β * R * δ ^ 2 + δ < z₀ / 2 ∧
      β * R ^ 2 * δ ^ 2 < 1 ∧
      q08gl_Chain c₀ K M z₀ A₂ A₃ B β R δ + q08gl_G c₀ K M z₀ B₂ B₃ Bf R < η / 2 :=
    hpos.and ((hev4.filter_mono nhdsWithin_le_nhds).and ((hev2.filter_mono nhdsWithin_le_nhds).and
      ((hev3.filter_mono nhdsWithin_le_nhds).and (hev1.filter_mono nhdsWithin_le_nhds))))
  obtain ⟨δ, hδ0, hδ1, hδ2, hδ3, hδ4⟩ := hall.exists
  exact ⟨R, hR3, δ, hδ0, hδ1.le, hδ2.le, hδ3.le, by linarith⟩

section GA

variable {ι : Type*} [Fintype ι]

set_option maxHeartbeats 800000 in
/-- **Abstract approximation theorem.** The tilted functional of the true statistics is within `η` of
the Gaussian tilted functional of the finite-rank limit, provided the finite-rank statistic and weight
approximate the true ones to accuracy `δ`, where `δ` depends only on the listed constants. -/
theorem q08gl_GA (F : (ι → ℝ) → ℝ) (M K : ℝ) (hFc : Continuous F) (hM : ∀ v, |F v| ≤ M) (hK0 : 0 ≤ K)
    (hF : ∀ v v', |F v - F v'| ≤ K * ∑ i, |v i - v' i|)
    (β : ℝ) (hβ : 0 ≤ β) (z₀ A₂ A₃ B B₂ B₃ Bf : ℝ) (hz₀ : 0 < z₀) (hA₂ : 0 ≤ A₂) (hA₃ : 0 ≤ A₃)
    (hB : 0 ≤ B) (hB₂ : 0 ≤ B₂) (hB₃ : 0 ≤ B₃) (hBf : 0 ≤ Bf) (η : ℝ) (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ (m : ℕ) (Ω : ℕ → Type) (_ : ∀ N, MeasurableSpace (Ω N)) (P : ∀ N, Measure (Ω N))
        (_ : ∀ N, IsProbabilityMeasure (P N)) (S : ∀ N, Ω N → EuclideanSpace ℝ (Fin m))
        (_ : ∀ N, Measurable (S N)) (γ : Measure (EuclideanSpace ℝ (Fin m)))
        (_ : IsProbabilityMeasure γ)
        (_ : ∀ Ψ : EuclideanSpace ℝ (Fin m) → ℝ, Continuous Ψ → ∀ C₀ : ℝ,
          (∀ s, |Ψ s| ≤ C₀ * (1 + ‖s‖ ^ 2)) →
            Tendsto (fun N => ∫ ω, Ψ (S N ω) ∂(P N)) atTop (𝓝 (∫ s, Ψ s ∂γ)))
        (ψ : EuclideanSpace ℝ (Fin m) → ℝ) (_ : Continuous ψ)
        (f : ι → EuclideanSpace ℝ (Fin m) → ℝ) (_ : ∀ i, Continuous (f i)) (Cf : ℝ) (_ : 0 ≤ Cf)
        (_ : ∀ i s, |f i s| ≤ Cf * (1 + ‖s‖ ^ 2))
        (_ : MemLp (fun s => Real.exp (-β * ψ s)) 2 γ)
        (_ : Integrable (fun s => Real.exp (-β * ψ s) ^ 3) γ)
        (_ : ∫ s, Real.exp (-β * ψ s) ^ 2 ∂γ ≤ B₂) (_ : ∫ s, Real.exp (-β * ψ s) ^ 3 ∂γ ≤ B₃)
        (_ : ∀ i, MemLp (f i) 2 γ) (_ : ∀ i, Real.sqrt (∫ s, f i s ^ 2 ∂γ) ≤ Bf)
        (a x : ∀ N, Ω N → ℝ) (V : ∀ N, ι → Ω N → ℝ)
        (_ : ∀ N, Measurable (x N)) (_ : ∀ N ω, a N ω = Real.exp (-β * x N ω))
        (_ : ∀ N, MemLp (a N) 2 (P N)) (_ : ∀ N, Integrable (fun ω => a N ω ^ 3) (P N))
        (_ : ∀ N, ∫ ω, a N ω ^ 2 ∂(P N) ≤ A₂) (_ : ∀ N, ∫ ω, a N ω ^ 3 ∂(P N) ≤ A₃)
        (_ : ∀ N, z₀ ≤ ∫ ω, a N ω ∂(P N))
        (_ : ∀ N i, Measurable (V N i)) (_ : ∀ N i, MemLp (V N i) 2 (P N))
        (_ : ∀ N i, Real.sqrt (∫ ω, V N i ω ^ 2 ∂(P N)) ≤ B)
        (_ : ∀ᶠ N in atTop, ∀ i, MemLp (fun ω => V N i ω - f i (S N ω)) 2 (P N) ∧
          Real.sqrt (∫ ω, (V N i ω - f i (S N ω)) ^ 2 ∂(P N)) ≤ δ)
        (_ : ∀ᶠ N in atTop, Integrable (fun ω => |x N ω - ψ (S N ω)|) (P N) ∧
          ∫ ω, |x N ω - ψ (S N ω)| ∂(P N) ≤ δ ^ 2),
        ∀ᶠ N in atTop,
          |q08gl_Phi (P N) F (a N) (V N) (∫ ω, a N ω ∂(P N)) -
            q08gl_Phi γ F (fun s => Real.exp (-β * ψ s)) f (∫ s, Real.exp (-β * ψ s) ∂γ)| ≤ η := by
  obtain ⟨R, hR, δ, hδ0, hδ1, hsm, hR2, hsel⟩ := q08gl_select (Fintype.card ι) K M z₀ A₂ A₃ B β B₂ B₃ Bf
    (Nat.cast_nonneg _) hK0 ((abs_nonneg _).trans (hM (fun _ => 0))) hz₀ hA₂ hA₃ hB hβ hB₂ hB₃ hBf (η / 2)
    (by linarith)
  refine ⟨δ, hδ0, ?_⟩
  intro m Ω hΩ P hP S hS γ hγ hclt ψ hψ f hfc Cf hCf hf hb2 hb3 hB2 hB3 hfγ hBfγ a x V hxm hax ha2 ha3 hA2 hA3
    hz hVm hV hVB hYV hxy
  haveI : ∀ N, IsProbabilityMeasure (P N) := hP
  haveI : IsProbabilityMeasure γ := hγ
  set b : EuclideanSpace ℝ (Fin m) → ℝ := fun s => Real.exp (-β * ψ s) with hb
  have hbc : Continuous b := Real.continuous_exp.comp (continuous_const.mul hψ)
  have hb0 : ∀ s, 0 ≤ b s := fun s => (Real.exp_pos _).le
  set w : EuclideanSpace ℝ (Fin m) → ℝ := fun s => min (b s) R with hw
  have hwc : Continuous w := hbc.min continuous_const
  have hw0 : ∀ s, 0 ≤ w s := fun s => le_min (hb0 s) hR.le
  have hwR : ∀ s, w s ≤ R := fun s => min_le_right _ _
  set z' : ℝ := ∫ s, w s ∂γ with hz'
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM (fun _ => 0))
  -- the mass of the truncated weight converges
  have hρlim : Tendsto (fun N => ∫ ω, w (S N ω) ∂(P N)) atTop (𝓝 z') :=
    hclt w hwc R (fun s => by
      rw [abs_of_nonneg (hw0 s)]
      have : (1 : ℝ) ≤ 1 + ‖s‖ ^ 2 := by nlinarith [sq_nonneg ‖s‖]
      nlinarith [hwR s, hR.le])
  have hρev : ∀ᶠ N in atTop, |∫ ω, min (b (S N ω)) R ∂(P N) - z'| ≤ δ := by
    have := hρlim.eventually (Metric.closedBall_mem_nhds z' hδ0)
    filter_upwards [this] with N hN
    rwa [Real.dist_eq] at hN
  have hmeasb : ∀ N, Measurable (fun ω => b (S N ω)) := fun N => hbc.measurable.comp (hS N)
  have hYm : ∀ N i, Measurable (fun ω => f i (S N ω)) := fun N i => (hfc i).measurable.comp (hS N)
  -- chain at a good `N`
  have hchain : ∀ᶠ N in atTop, z₀ / 2 ≤ z' ∧
      |q08gl_Phi (P N) F (a N) (V N) (∫ ω, a N ω ∂(P N)) -
        q08gl_Phi (P N) F (fun ω => w (S N ω)) (fun i ω => f i (S N ω)) z'| ≤
        q08gl_Chain (Fintype.card ι) K M z₀ A₂ A₃ B β R δ := by
    filter_upwards [hYV, hxy, hρev] with N hYV' hxy' hρ'
    have hY : ∀ i, MemLp (fun ω => f i (S N ω)) 2 (P N) := fun i => by
      have := (hV N i).sub (hYV' i).1
      convert this using 1
      ext ω; simp only [Pi.sub_apply]; ring
    have := q08gl_chain (P N) F M K hFc hM hK0 hF β R hβ hR (a N) (x N) (fun ω => ψ (S N ω))
      (fun ω => b (S N ω)) (hxm N) (hψ.measurable.comp (hS N)) (hax N) (fun ω => rfl) (ha2 N) (ha3 N) A₂ A₃
      (hA2 N) (hA3 N) z₀ hz₀ (hz N) (V N) (fun i ω => f i (S N ω)) (hVm N) (hYm N) (hV N) hY B δ δ hB
      (hVB N) (fun i => (hYV' i).2) hδ0.le hδ0.le hxy'.1 hxy'.2 z' δ hρ' hsm hR2
    refine ⟨this.1, this.2.trans (le_of_eq ?_)⟩
    unfold q08gl_Chain
    ring
  obtain ⟨N₀, hN₀⟩ := hchain.exists
  have hz'half : z₀ / 2 ≤ z' := hN₀.1
  have hz'pos : 0 < z' := lt_of_lt_of_le (by positivity) hz'half
  -- the limit N → ∞
  have hlim := q08gl_lim P S hS γ hclt F M K hFc hM hK0 hF w hwc R hw0 hwR f hfc Cf hCf hf z' hz'pos
  have hlimev : ∀ᶠ N in atTop, |q08gl_Phi (P N) F (fun ω => w (S N ω)) (fun i ω => f i (S N ω)) z' -
      q08gl_Phi γ F w f z'| < η / 4 := by
    have := hlim.eventually (Metric.ball_mem_nhds _ (by linarith : 0 < η / 4))
    filter_upwards [this] with N hN
    rwa [Real.dist_eq] at hN
  -- removal of the truncation of the limit weight
  have hB₂0 : 0 ≤ B₂ := le_trans (integral_nonneg fun s => sq_nonneg (b s)) hB2
  have hgs := q08gl_gstep γ F M K hFc hM hK0 hF b hb0 hbc.measurable hb2 hb3 B₂ B₃ hB2 hB3 R hR z₀ hz₀ hz'half f
    (fun i => (hfc i).measurable) hfγ Bf hBf hBfγ
  filter_upwards [hchain, hlimev] with N hc hl
  have t1 := abs_sub_le (q08gl_Phi (P N) F (a N) (V N) (∫ ω, a N ω ∂(P N)))
    (q08gl_Phi (P N) F (fun ω => w (S N ω)) (fun i ω => f i (S N ω)) z') (q08gl_Phi γ F b f (∫ s, b s ∂γ))
  have t2 := abs_sub_le (q08gl_Phi (P N) F (fun ω => w (S N ω)) (fun i ω => f i (S N ω)) z')
    (q08gl_Phi γ F w f z') (q08gl_Phi γ F b f (∫ s, b s ∂γ))
  have hG : q08gl_G (Fintype.card ι) K M z₀ B₂ B₃ Bf R =
      (2 * K / z₀) * ((2 / z₀) * (Fintype.card ι * Bf * Real.sqrt (B₃ / R)) * Real.sqrt B₂) +
        (2 * M / z₀) * (B₂ / R) +
      (4 * B₂ / (R * z₀ ^ 2)) * (M * Real.sqrt B₂ + (2 * K / z₀) * (Fintype.card ι * Bf * B₂)) := rfl
  rw [← hG] at hgs
  linarith [hc.2]

end GA

end HRS.Q08

end
