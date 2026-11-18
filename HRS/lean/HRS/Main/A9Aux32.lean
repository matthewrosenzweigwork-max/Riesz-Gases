import HRS.Main.A9Aux31

/-!
# Packet A9, part 32: bookkeeping for `main_torus_field_limit`

* `a9_conv_shift`: convergence in law is insensitive to a finite index shift;
* `a9EmbCLM`: the embedding `E_γ ↪ E_γ'` as a contraction, and `a9_smoothDist_map_le`;
* `a9_particle_embed`: the particle field law at level `γ'` is the embedding of the one at level `γ`;
* `a9_fieldRate_tendsto`: the right-hand side of `B:eq:thm-torus-field` tends to `0`;
* `a9_linear_eq`: the linear field law with the coupled initial field `η°` is the one with law `νin`.
-/

noncomputable section

open MeasureTheory Filter Topology Finset ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.Main.A9

open HRS HRS.PDE HRS.A33 HRS.Main HRS.A34 HRS.Main.A8P

section Shift

theorem a9_conv_shift {E : Type*} [TopologicalSpace E] [MeasurableSpace E] {μ : ℕ → Measure E}
    {ν : Measure E} (k : ℕ) :
    ConvergesInLaw μ ν ↔ ConvergesInLaw (fun n => μ (n + k)) ν := by
  constructor
  · intro h f; exact (h f).comp (tendsto_add_atTop_nat k)
  · intro h f; exact (tendsto_add_atTop_iff_nat k).1 (h f)

end Shift

section Embed

variable {d : ℕ}

theorem a9_embed_smul {m m' : ℝ} (hmm' : m ≤ m') (c : ℝ) (F : NegSobolev d m) :
    NegSobolev.embed m' (c • F) = c • NegSobolev.embed m' F := by
  refine a34_ext fun k => ?_
  rw [a34_coord_embed hmm', a34_coord_smul, a34_coord_embed hmm']
  unfold NegSobolev.fourierCoeff
  rw [a34_coord_smul]
  ring

/-- the embedding as a continuous linear map. -/
def a9EmbCLM {m m' : ℝ} (hmm' : m ≤ m') : NegSobolev d m →L[ℝ] NegSobolev d m' :=
  LinearMap.mkContinuous
    { toFun := NegSobolev.embed m'
      map_add' := a34_embed_add hmm'
      map_smul' := fun c F => by simpa using a9_embed_smul hmm' c F } 1
    (fun F => by simpa using NegSobolev.norm_embed_le m' hmm' F)

theorem a9EmbCLM_apply {m m' : ℝ} (hmm' : m ≤ m') (F : NegSobolev d m) :
    a9EmbCLM hmm' F = NegSobolev.embed m' F := rfl

theorem a9EmbCLM_norm_le {m m' : ℝ} (hmm' : m ≤ m') : ‖(a9EmbCLM hmm' : NegSobolev d m →L[ℝ] _)‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

end Embed

section SmoothDist

variable {B B' : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B] [MeasurableSpace B] [BorelSpace B]
  [NormedAddCommGroup B'] [NormedSpace ℝ B'] [MeasurableSpace B'] [BorelSpace B']

theorem a9_smoothDist_map_le (e : B →L[ℝ] B') (he : ‖e‖ ≤ 1) (P Q : Measure B)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] :
    smoothDist 2 (P.map e) (Q.map e) ≤ smoothDist 2 P Q := by
  have hm : Measurable e := e.continuous.measurable
  show (⨆ Φ : CbUnitBall B' 2, |∫ z, Φ.1 z ∂(P.map e) - ∫ z, Φ.1 z ∂(Q.map e)|) ≤ _
  refine Real.iSup_le (fun Φ => ?_) (smoothDist_nonneg 2 P Q)
  rw [integral_map hm.aemeasurable Φ.2.1.continuous.aestronglyMeasurable,
    integral_map hm.aemeasurable Φ.2.1.continuous.aestronglyMeasurable]
  exact abs_integral_sub_le_smoothDist (cbUnitBall_comp_clm e he Φ.2) P Q

end SmoothDist

section Particle

variable {d : ℕ}

theorem a9_embed_ofMeasureDiff {γ γ' : ℝ} (hγ : (d : ℝ) < 2 * γ) (μ ν : Measure (Torus d))
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    NegSobolev.embed γ' (NegSobolev.ofMeasureDiff γ μ ν) = NegSobolev.ofMeasureDiff γ' μ ν := by
  have h := fun k => NegSobolev.fourierCoeff_ofMeasureDiff hγ μ ν k
  unfold NegSobolev.embed
  conv_rhs => unfold NegSobolev.ofMeasureDiff
  congr 1
  funext k
  exact h k

variable {S : MainData d} {R : ∀ N, Realization d N} {Rg : PDE.Regime} {ν₀ MB Λ VB C₀ Cc : ℝ}
  {𝔈 : ℕ → ℝ}

theorem a9_particle_embed (hS : TorusStanding S R Rg ν₀ MB Λ VB (gammaIdx d) C₀ Cc 𝔈) {N : ℕ}
    (hN : 1 ≤ N) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) S.T) {γ' : ℝ}
    (hγ : (gammaIdx d : ℝ) ≤ γ') :
    particleFieldLaw (R N).P (S.sigma N) γ' (R N).X (S.ρ N) t =
      (particleFieldLaw (R N).P (S.sigma N) (gammaIdx d : ℝ) (R N).X (S.ρ N) t).map
        (NegSobolev.embed γ') := by
  obtain ⟨ℱ, W', hF⟩ := hS.filtered N hN
  have hZ := a9_Z_meas hS hN ht hF
  have hρ := (hS.mean_field.solution N hN).density t ht
  haveI : IsProbabilityMeasure (withDensityReal (S.ρ N t)) := HRS.isProb_withDensityReal hρ
  show (R N).P.map _ = ((R N).P.map (a9Z S R N t)).map (NegSobolev.embed γ')
  rw [Measure.map_map (a34_embed_meas hγ) hZ]
  congr 1
  funext ω
  show S.sigma N • NegSobolev.ofMeasureDiff γ' _ _ =
    NegSobolev.embed γ' (S.sigma N • NegSobolev.ofMeasureDiff (gammaIdx d : ℝ) _ _)
  rw [a9_embed_smul hγ, a9_embed_ofMeasureDiff a9_gamma_gt]

end Particle

section FieldRate

variable {d : ℕ}

theorem a9_fieldRate_tendsto (S : MainData d) {𝔈 εf : ℕ → ℝ} (hpos : ∀ N, 1 ≤ N → 0 < 𝔈 N)
    (hsmall : Tendsto (fun N => S.sigma N * 𝔈 N) atTop (𝓝 0)) (hεf : Tendsto εf atTop (𝓝 0)) :
    Tendsto (fun N => fieldRate d (εf N) (S.qN N) (S.sigma N) (𝔈 N) N) atTop (𝓝 0) := by
  obtain ⟨B, hB⟩ := S.invβ_bdd
  set B' : ℝ := max B 0 with hB'
  have hB'0 : 0 ≤ B' := le_max_right _ _
  -- key: `q 𝔈 ≤ √B' (σ 𝔈)`
  have key : ∀ N, 1 ≤ N → S.qN N * 𝔈 N ≤ Real.sqrt B' * (S.sigma N * 𝔈 N) := by
    intro N hN
    have hσ := a8p_sigma_nonneg S N
    have h𝔈 := (hpos N hN).le
    have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
    have hb0 := S.hinvβ N
    have hbB : S.invβ N ≤ B' := (hB N).trans (le_max_left _ _)
    have hq := a8p_q_eq S N
    have hσ𝔈 : 0 ≤ S.sigma N * 𝔈 N := mul_nonneg hσ h𝔈
    rcases hb0.eq_or_lt with h0 | hbpos
    · rw [hq, ← h0]; simp; positivity
    · -- σ² b ≤ N
      have hσle : S.sigma N ≤ Real.sqrt (N / S.invβ N) := by
        unfold MainData.sigma sigmaScale
        rw [if_neg hbpos.ne']
        exact min_le_right _ _
      have hσ2 : S.sigma N ^ 2 * S.invβ N ≤ N := by
        have h1 : S.sigma N ^ 2 ≤ N / S.invβ N := by
          calc S.sigma N ^ 2 ≤ (Real.sqrt (N / S.invβ N)) ^ 2 := by gcongr
            _ = N / S.invβ N := Real.sq_sqrt (by positivity)
        rwa [le_div_iff₀ hbpos] at h1
      -- (σ b / N)² ≤ B'
      have h3 : (S.sigma N * S.invβ N / N) ^ 2 ≤ B' := by
        have e : (S.sigma N * S.invβ N / N) ^ 2 = (S.sigma N ^ 2 * S.invβ N) * S.invβ N / N ^ 2 := by
          field_simp
        rw [e, div_le_iff₀ (by positivity)]
        have h4 : (S.sigma N ^ 2 * S.invβ N) * S.invβ N ≤ N * S.invβ N :=
          mul_le_mul_of_nonneg_right hσ2 hb0
        have h5 : (N : ℝ) * S.invβ N ≤ B' * N ^ 2 := by
          have h1N : (1 : ℝ) ≤ N := by exact_mod_cast hN
          have h7 := mul_le_mul_of_nonneg_left hbB hN0.le
          have h8 := mul_nonneg (mul_nonneg hB'0 hN0.le) (sub_nonneg.2 h1N)
          nlinarith [h7, h8]
        linarith
      have h6 : S.sigma N * S.invβ N / N ≤ Real.sqrt B' :=
        Real.le_sqrt_of_sq_le h3
      have e2 : S.qN N * 𝔈 N = (S.sigma N * S.invβ N / N) * (S.sigma N * 𝔈 N) := by
        rw [hq]; field_simp
      rw [e2]
      exact mul_le_mul_of_nonneg_right h6 hσ𝔈
  -- the four terms
  have hq01 : ∀ N, 1 ≤ N → 0 ≤ S.qN N ∧ S.qN N ≤ 1 := fun N hN => a8p_q_bounds S hN
  have hT3 : Tendsto (fun N => S.qN N * (𝔈 N) ^ ((1 : ℝ) / 2)) atTop (𝓝 0) := by
    have hlim : Tendsto (fun N => Real.sqrt (Real.sqrt B' * (S.sigma N * 𝔈 N))) atTop (𝓝 0) := by
      have h0 : Tendsto (fun N => Real.sqrt B' * (S.sigma N * 𝔈 N)) atTop (𝓝 0) := by
        simpa using hsmall.const_mul (Real.sqrt B')
      have h1 := (Real.continuous_sqrt.tendsto 0).comp h0
      rw [Real.sqrt_zero] at h1
      exact h1
    refine squeeze_zero' ?_ ?_ hlim
    · filter_upwards [eventually_ge_atTop 1] with N hN
      exact mul_nonneg (hq01 N hN).1 (Real.rpow_nonneg (hpos N hN).le _)
    · filter_upwards [eventually_ge_atTop 1] with N hN
      obtain ⟨hq0, hq1⟩ := hq01 N hN
      have h𝔈 := (hpos N hN).le
      rw [← Real.sqrt_eq_rpow]
      calc S.qN N * Real.sqrt (𝔈 N) = Real.sqrt (S.qN N ^ 2 * 𝔈 N) := by
            rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hq0]
        _ ≤ Real.sqrt (Real.sqrt B' * (S.sigma N * 𝔈 N)) := by
            refine Real.sqrt_le_sqrt ?_
            refine le_trans ?_ (key N hN)
            nlinarith [mul_nonneg hq0 h𝔈]
  have hT4 : Tendsto (fun N : ℕ => S.qN N * (N : ℝ) ^ (-(1 : ℝ) / d)) atTop (𝓝 0) := by
    have hd : (0 : ℝ) < d := by exact_mod_cast S.hd
    have h1 : Tendsto (fun N : ℕ => (N : ℝ) ^ (-(1 : ℝ) / d)) atTop (𝓝 0) := by
      have := (tendsto_rpow_neg_atTop (y := 1 / (d : ℝ)) (by positivity)).comp
        tendsto_natCast_atTop_atTop
      refine this.congr fun N => ?_
      simp only [Function.comp]
      congr 1
      ring
    refine squeeze_zero' ?_ ?_ h1
    · filter_upwards [eventually_ge_atTop 1] with N hN
      exact mul_nonneg (hq01 N hN).1 (Real.rpow_nonneg (Nat.cast_nonneg N) _)
    · filter_upwards [eventually_ge_atTop 1] with N hN
      have := (hq01 N hN).2
      have h0 : 0 ≤ (N : ℝ) ^ (-(1 : ℝ) / d) := Real.rpow_nonneg (Nat.cast_nonneg N) _
      nlinarith
  have := (hεf.add hsmall).add (hT3.add hT4)
  simp only [add_zero] at this
  refine this.congr fun N => ?_
  unfold fieldRate
  ring

end FieldRate

section LinearEq

variable {d : ℕ} {S : MainData d} {R : ∀ N, Realization d N} {Cin : ℝ} {εf : ℕ → ℝ}
  {ηF : ∀ N, (R N).Ω → NegSobolev d (gammaIdx d : ℝ)}
  {νin : Measure (NegSobolev d (gammaIdx d : ℝ))}

theorem a9_linear_eq (hfield : InitialFluctuationField S R (gammaIdx d) Cin εf ηF νin) {N : ℕ}
    (hN : 1 ≤ N) {t : ℝ}
    (htm : Measurable fun F : NegSobolev d (gammaIdx d : ℝ) =>
      S.AN N • transportField (S.dyn N) (S.ρ N) t (gammaIdx d : ℝ) F)
    (νG : Measure (NegSobolev d (gammaIdx d : ℝ))) :
    linearFieldLaw (R N).P (S.dyn N) (S.ρ N) (S.AN N) t (gammaIdx d : ℝ) (ηF N) νG =
      linearFieldLaw νin (S.dyn N) (S.ρ N) (S.AN N) t (gammaIdx d : ℝ) id νG := by
  have h : law (R N).P (fun ω => S.AN N • transportField (S.dyn N) (S.ρ N) t (gammaIdx d : ℝ) (ηF N ω)) =
      law νin (fun F : NegSobolev d (gammaIdx d : ℝ) =>
        S.AN N • transportField (S.dyn N) (S.ρ N) t (gammaIdx d : ℝ) (id F)) := by
    rw [← hfield.law_eq N hN]
    unfold law
    simp only [id_eq]
    rw [Measure.map_map htm (hfield.ηF_meas N)]
    rfl
  unfold linearFieldLaw
  rw [h]

end LinearEq

end HRS.Main.A9
