import HRS.MD.EQInterpBase

/-!
# EQ-INTERP packet, part 2: the Hölder interpolation in the Fourier series, the embedding of path spaces

* `ce_holder`: `ce m ≤ (ce q)^{1-α}(ce m₁)^α`, `α = (m-q)/(m₁-q)` (TeX `P:eq:Sobolev-interpolate`, L4136-4141);
* `embedCLM`, `epath`: the inclusion `E_m ↪ E_{m₁}` and its action on `𝒳_{m,T} → 𝒳_{m₁,T}` as continuous linear maps, injective, hence
  (Lusin-Souslin, `PathSpace` is Polish) a measurable embedding `epath_measurableEmbedding`;
* `sq_norm_le_holder`: pathwise `‖z‖²_{𝒳_m} ≤ (sup_t ‖z^t‖²_{E_q})^{1-α} (‖epath z‖²_{𝒳_{m₁}})^α`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MD.EQInterp

variable {d : ℕ}

theorem holder_term (j c α q m m₁ : ℝ) (hj : 0 < j) (hα0 : 0 < α) (hα1 : α < 1)
    (hα : α * (m₁ - q) = m - q) :
    j ^ (-2 * m) * c ^ 2 = (j ^ (-2 * q) * c ^ 2) ^ (1 - α) * (j ^ (-2 * m₁) * c ^ 2) ^ α := by
  by_cases hc : c = 0
  · subst hc
    have h1 : (1 - α) ≠ 0 := by linarith
    simp [Real.zero_rpow h1, Real.zero_rpow hα0.ne']
  · have hc2 : 0 < c ^ 2 := by positivity
    rw [Real.mul_rpow (by positivity) hc2.le, Real.mul_rpow (by positivity) hc2.le,
      ← Real.rpow_mul hj.le, ← Real.rpow_mul hj.le]
    have e1 : (c ^ 2) ^ (1 - α) * (c ^ 2) ^ α = c ^ 2 := by
      rw [← Real.rpow_add hc2]; simp
    have e2 : j ^ (-2 * q * (1 - α)) * j ^ (-2 * m₁ * α) = j ^ (-2 * m) := by
      rw [← Real.rpow_add hj]; congr 1; nlinarith
    calc j ^ (-2 * m) * c ^ 2 = (j ^ (-2 * q * (1 - α)) * j ^ (-2 * m₁ * α)) *
          ((c ^ 2) ^ (1 - α) * (c ^ 2) ^ α) := by rw [e1, e2]
      _ = _ := by ring

theorem ce_holder {m' : ℝ} (q m m₁ α : ℝ) (hα0 : 0 < α) (hα1 : α < 1)
    (hα : α * (m₁ - q) = m - q) (F : NegSobolev d m') :
    ce m F ≤ ce q F ^ (1 - α) * ce m₁ F ^ α := by
  have hp : (1 / (1 - α)).HolderConjugate (1 / α) := by
    rw [Real.holderConjugate_iff]
    refine ⟨?_, ?_⟩
    · rw [lt_div_iff₀ (by linarith)]; linarith
    · field_simp; ring
  set a : NonzeroLattice d → ℝ≥0∞ := fun k =>
    ENNReal.ofReal (Lattice.jp k.1 ^ (-2 * q) * NegSobolev.fourierCoeff F k ^ 2) with ha
  set b : NonzeroLattice d → ℝ≥0∞ := fun k =>
    ENNReal.ofReal (Lattice.jp k.1 ^ (-2 * m₁) * NegSobolev.fourierCoeff F k ^ 2) with hb
  have hterm : ∀ k, ENNReal.ofReal (Lattice.jp k.1 ^ (-2 * m) * NegSobolev.fourierCoeff F k ^ 2) =
      a k ^ (1 - α) * b k ^ α := by
    intro k
    have hj := Torus.jp_pos k.1
    rw [holder_term _ _ α q m m₁ hj hα0 hα1 hα, ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_rpow_of_nonneg (by positivity) (by linarith),
      ENNReal.ofReal_rpow_of_nonneg (by positivity) hα0.le]
  have hce : ∀ r : ℝ, ce r F = ∑' k, ENNReal.ofReal (Lattice.jp k.1 ^ (-2 * r) *
      NegSobolev.fourierCoeff F k ^ 2) := fun r => rfl
  rw [hce m, hce q, hce m₁]
  simp_rw [hterm]
  rw [ENNReal.tsum_eq_iSup_sum]
  refine iSup_le fun s => ?_
  refine (ENNReal.inner_le_Lp_mul_Lq s (fun k => a k ^ (1 - α)) (fun k => b k ^ α) hp).trans ?_
  have e1 : ∀ k, (a k ^ (1 - α)) ^ (1 / (1 - α)) = a k := fun k => by
    rw [← ENNReal.rpow_mul]; rw [mul_one_div_cancel (by linarith), ENNReal.rpow_one]
  have e2 : ∀ k, (b k ^ α) ^ (1 / α) = b k := fun k => by
    rw [← ENNReal.rpow_mul]; rw [mul_one_div_cancel hα0.ne', ENNReal.rpow_one]
  simp_rw [e1, e2]
  have h1 : 1 / (1 / (1 - α)) = 1 - α := by field_simp
  have h2 : 1 / (1 / α) = α := by field_simp
  rw [h1, h2]
  gcongr
  · exact ENNReal.sum_le_tsum s
  · exact ENNReal.sum_le_tsum s

theorem embed_injective {m m₁ : ℝ} (hmm : m ≤ m₁) :
    Function.Injective (NegSobolev.embed m₁ : NegSobolev d m → NegSobolev d m₁) := by
  intro F G h
  refine EQGaussLift.eqgl_ext fun k => ?_
  have h1 := EQGaussLift.eqgl_fourierCoeff_embed hmm F k
  have h2 := EQGaussLift.eqgl_fourierCoeff_embed hmm G k
  have h3 : NegSobolev.fourierCoeff F k = NegSobolev.fourierCoeff G k := by
    rw [← h1, ← h2, h]
  have hj := Torus.jp_pos k.1
  simp only [NegSobolev.fourierCoeff] at h3
  exact mul_left_cancel₀ (Real.rpow_pos_of_pos hj m).ne' h3

theorem ce_embed {m m₁ : ℝ} (hmm : m ≤ m₁) (r : ℝ) (F : NegSobolev d m) :
    ce r (NegSobolev.embed m₁ F) = ce r F := by
  simp only [ce]
  simp_rw [EQGaussLift.eqgl_fourierCoeff_embed hmm]

/-- The inclusion `E_m ↪ E_{m₁}` as a continuous linear map (norm `≤ 1`). -/
def embedCLM {m m₁ : ℝ} (hmm : m ≤ m₁) : NegSobolev d m →L[ℝ] NegSobolev d m₁ :=
  LinearMap.mkContinuous
    { toFun := NegSobolev.embed m₁
      map_add' := fun F G => by
        refine EQGaussLift.eqgl_ext fun k => ?_
        have hs : ∀ (A B : NegSobolev d m₁), NegSobolev.coord (A + B) k =
            NegSobolev.coord A k + NegSobolev.coord B k := fun A B => rfl
        rw [hs, EQGaussLift.eqgl_coord_embed hmm, EQGaussLift.eqgl_coord_embed hmm,
          EQGaussLift.eqgl_coord_embed hmm]
        have : NegSobolev.fourierCoeff (F + G) k = NegSobolev.fourierCoeff F k +
            NegSobolev.fourierCoeff G k := by
          simp only [NegSobolev.fourierCoeff]
          have : NegSobolev.coord (F + G) k = NegSobolev.coord F k + NegSobolev.coord G k := rfl
          rw [this]; ring
        rw [this]; ring
      map_smul' := fun c F => by
        refine EQGaussLift.eqgl_ext fun k => ?_
        have hs : ∀ (A : NegSobolev d m₁), NegSobolev.coord (c • A) k = c * NegSobolev.coord A k :=
          fun A => rfl
        simp only [RingHom.id_apply]
        rw [hs, EQGaussLift.eqgl_coord_embed hmm, EQGaussLift.eqgl_coord_embed hmm]
        have : NegSobolev.fourierCoeff (c • F) k = c * NegSobolev.fourierCoeff F k := by
          simp only [NegSobolev.fourierCoeff]
          have : NegSobolev.coord (c • F) k = c * NegSobolev.coord F k := rfl
          rw [this]; ring
        rw [this]; ring } 1
    (fun F => by simpa using NegSobolev.norm_embed_le m₁ hmm F)

theorem embedCLM_apply {m m₁ : ℝ} (hmm : m ≤ m₁) (F : NegSobolev d m) :
    embedCLM hmm F = NegSobolev.embed m₁ F := rfl

/-- The inclusion `𝒳_{m,T} ↪ 𝒳_{m₁,T}`. -/
def epath {m m₁ : ℝ} (hmm : m ≤ m₁) (T : ℝ) : PathSpace d m T →L[ℝ] PathSpace d m₁ T :=
  ContinuousLinearMap.compLeftContinuous ℝ (Set.Icc (0 : ℝ) T) (embedCLM hmm)

theorem epath_at' {m m₁ : ℝ} (hmm : m ≤ m₁) (T : ℝ) (w : PathSpace d m T) (t : Set.Icc (0 : ℝ) T) :
    (epath hmm T w).at' t = NegSobolev.embed m₁ (w.at' t) := rfl

theorem epath_injective {m m₁ : ℝ} (hmm : m ≤ m₁) (T : ℝ) :
    Function.Injective (epath hmm T : PathSpace d m T → PathSpace d m₁ T) := by
  intro w w' h
  refine ContinuousMap.ext fun t => ?_
  have := congrArg (fun v : PathSpace d m₁ T => v.at' t) h
  exact embed_injective hmm this

instance pathSpace_secondCountable {m T : ℝ} : SecondCountableTopology (PathSpace d m T) :=
  inferInstanceAs (SecondCountableTopology C(Set.Icc (0 : ℝ) T, NegSobolev d m))

instance pathSpace_complete {m T : ℝ} : CompleteSpace (PathSpace d m T) :=
  inferInstanceAs (CompleteSpace C(Set.Icc (0 : ℝ) T, NegSobolev d m))

theorem epath_measurableEmbedding {m m₁ : ℝ} (hmm : m ≤ m₁) (T : ℝ) :
    MeasurableEmbedding (epath hmm T : PathSpace d m T → PathSpace d m₁ T) := by
  have : PolishSpace (PathSpace d m T) :=
    inferInstanceAs (PolishSpace C(Set.Icc (0 : ℝ) T, NegSobolev d m))
  exact (epath hmm T).continuous.measurableEmbedding (epath_injective hmm T)

theorem ce_epath_at' {m m₁ : ℝ} (hmm : m ≤ m₁) (T r : ℝ) (w : PathSpace d m T)
    (t : Set.Icc (0 : ℝ) T) : ce r ((epath hmm T w).at' t) = ce r (w.at' t) :=
  ce_embed hmm r _

/-- Pathwise Hölder interpolation (`P:eq:Sobolev-interpolate`):
`‖z‖²_{𝒳_m} ≤ (sup_t ‖z^t‖²_{E_q})^{1-α} (‖z‖²_{𝒳_{m₁}})^α`, `α = (m-q)/(m₁-q)`. -/
theorem sq_norm_le_holder {m m₁ T : ℝ} (hmm : m ≤ m₁) (hT : 0 ≤ T) (q α : ℝ) (hα0 : 0 < α)
    (hα1 : α < 1) (hα : α * (m₁ - q) = m - q) (z : PathSpace d m T) :
    ENNReal.ofReal (‖z‖ ^ 2) ≤
      qSq q z ^ (1 - α) * ENNReal.ofReal (‖epath hmm T z‖ ^ 2) ^ α := by
  have hne : (Set.Icc (0 : ℝ) T).Nonempty := ⟨0, le_rfl, hT⟩
  have hcont : Continuous fun t : Set.Icc (0 : ℝ) T => ‖z.at' t‖ :=
    (show Continuous fun t : Set.Icc (0 : ℝ) T => z.at' t from
      (show C(Set.Icc (0 : ℝ) T, NegSobolev d m) from z).continuous).norm
  haveI : Nonempty (Set.Icc (0 : ℝ) T) := hne.to_subtype
  obtain ⟨t₀, -, ht₀⟩ := isCompact_univ.exists_isMaxOn (Set.univ_nonempty) hcont.continuousOn
  have hnorm : ‖z‖ ≤ ‖z.at' t₀‖ := by
    refine (ContinuousMap.norm_le _ (norm_nonneg _)).2 fun t => ?_
    exact ht₀ (Set.mem_univ t)
  have hz : ‖z.at' t₀‖ ≤ ‖z‖ := ContinuousMap.norm_coe_le_norm (show C(Set.Icc (0 : ℝ) T, NegSobolev d m) from z) t₀
  calc ENNReal.ofReal (‖z‖ ^ 2) ≤ ENNReal.ofReal (‖z.at' t₀‖ ^ 2) :=
        ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (norm_nonneg _) hnorm 2)
    _ = ce m (z.at' t₀) := ofReal_norm_sq_eq_ce _
    _ ≤ ce q (z.at' t₀) ^ (1 - α) * ce m₁ (z.at' t₀) ^ α := ce_holder q m m₁ α hα0 hα1 hα _
    _ ≤ qSq q z ^ (1 - α) * ENNReal.ofReal (‖epath hmm T z‖ ^ 2) ^ α := by
        have h1 : ce q (z.at' t₀) ≤ qSq q z := le_iSup (fun t => ce q (z.at' t)) t₀
        have h2 : ce m₁ (z.at' t₀) ≤ ENNReal.ofReal (‖epath hmm T z‖ ^ 2) := by
          rw [← ce_epath_at' hmm T m₁ z t₀, ← ofReal_norm_sq_eq_ce]
          exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (norm_nonneg _)
            (ContinuousMap.norm_coe_le_norm (show C(Set.Icc (0 : ℝ) T, NegSobolev d m₁) from epath hmm T z) t₀) 2)
        gcongr

end HRS.MD.EQInterp
