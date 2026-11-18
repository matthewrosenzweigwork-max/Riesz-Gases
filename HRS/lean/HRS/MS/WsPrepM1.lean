import HRS.MS.R2GenInitAux41
import HRS.MS.WsStatAux33

/-!
# S21S packet M1: the moving window data and the covariation density of the window features

`S21mData d s a β T b ρ`: the window data for a MOVING mean-field trajectory `ρ : ℝ → Euc d → ℝ` of the quadratic dynamics
(the moving analogue of `S105Stat`): adjoint-orbit input, window feature regularity, classical adjoints, mean-field regularity data
(`MFData`), measurability and weak continuity of the trajectory.
`s21mDb`: the deterministic covariation density `C̄_r = featureForm (Γ(r)) (ρ_r dx)` (`0` off `[0,τ₀]`), `s21mDb_isDet`, and the positive
semidefiniteness of the matrices of integrals of a deterministic covariation density (`s21m_psd_of_entries`).
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.S21m

open HRS HRS.Whole HRS.Whole.AppendixA HRS.MS.GenPath HRS.MS.S52 HRS.MP.RdRem HRS.MH.DualityRd HRS.MS.R2GenInit
  HRS.Uniform.Q54c

variable {d : ℕ}

/-- The moving window data (see the module docstring). -/
structure S21mData (d : ℕ) (s a β T b : ℝ) (ρ : ℝ → Euc d → ℝ) : Prop where
  hC : OscAdjointInput ((quadraticGradientDyn d s a β).coeff ρ) ((wholeSpaceIndex d : ℕ) : ℝ) (b + T)
  hK : ∀ (a' : Fin d) (r : ℝ), r ∈ Set.Icc (0 : ℝ) (b + T) → ∀ x,
    S105WinK ((quadraticGradientDyn d s a β).coeff ρ) ((wholeSpaceIndex d : ℕ) : ℝ) T b a' r x
  hF : S105Feat d ((wholeSpaceIndex d : ℕ) : ℝ) T (b + T) (fun a' r x => r2WindowFeature
    ((quadraticGradientDyn d s a β).coeff ρ) ((wholeSpaceIndex d : ℕ) : ℝ) T (gradComp a') b r x)
  hcl : ∀ α : MultiIndex d, ∀ t : ℝ, 0 ≤ t → IsClassicalAdjointW
    ((quadraticGradientDyn d s a β).coeff ρ) t (oscTestFun ((wholeSpaceIndex d : ℕ) : ℝ) α)
    (fun r => propagatorW ((quadraticGradientDyn d s a β).coeff ρ) r t
      (oscTestFun ((wholeSpaceIndex d : ℕ) : ℝ) α))
  hM : ∃ Λ ΛV G₀ : ℝ, MFData s Λ (b + T) ΛV G₀ (quadraticGradientDyn d s a β) ρ
  hρ2 : Integrable (fun x : Euc d => ‖x‖ ^ 2 * ρ 0 x)
  hρm : Measurable fun p : ℝ × Euc d => ρ (mrrClamp (b + T) p.1) p.2
  hcont : ∀ ψ : Euc d → ℝ, Continuous ψ → (∃ B, ∀ x, |ψ x| ≤ B) →
    ContinuousOn (fun r => ∫ x, ψ x * ρ r x) (Set.Icc (0 : ℝ) (b + T))

theorem S21mData.regSlice {s a β T b : ℝ} {ρ : ℝ → Euc d → ℝ} (h : S21mData d s a β T b ρ) {r : ℝ}
    (hr : r ∈ Set.Icc (0 : ℝ) (b + T)) : RegSliceRd (ρ r) := by
  obtain ⟨Λ, ΛV, G₀, hM⟩ := h.hM
  exact hM.regSlice hr

theorem S21mData.hprob {s a β T b : ℝ} {ρ : ℝ → Euc d → ℝ} (h : S21mData d s a β T b ρ) {r : ℝ}
    (hr : r ∈ Set.Icc (0 : ℝ) (b + T)) : HRS.Whole.IsProbDensity (ρ r) :=
  (h.regSlice hr).1

theorem s21m_featureForm_meas {m T τ₀ : ℝ} (hτ : 0 ≤ τ₀) {Γ : Fin d → ℝ → Euc d → KSpace d m T}
    (h : S105Feat d m T τ₀ Γ) {ρ : ℝ → Euc d → ℝ}
    (hρ : ∀ r ∈ Set.Icc (0 : ℝ) τ₀, HRS.Whole.IsProbDensity (ρ r))
    (hρm : Measurable fun p : ℝ × Euc d => ρ (mrrClamp τ₀ p.1) p.2) (q : ℝ) (u v : KSpace d m T) :
    Measurable fun r : ℝ => featureForm m T q (fun a => Γ a (mrrClamp τ₀ r))
      (HRS.Whole.withDensityReal (ρ (mrrClamp τ₀ r))) u v := by
  unfold featureForm
  refine (Finset.measurable_sum _ fun a _ => ?_).const_mul _
  have : (fun r : ℝ => ∫ x, inner ℝ (Γ a (mrrClamp τ₀ r) x) u * inner ℝ (Γ a (mrrClamp τ₀ r) x) v
        ∂(HRS.Whole.withDensityReal (ρ (mrrClamp τ₀ r)))) =
      fun r : ℝ => ∫ x, ρ (mrrClamp τ₀ r) x *
        (inner ℝ (Γ a (mrrClamp τ₀ r) x) u * inner ℝ (Γ a (mrrClamp τ₀ r) x) v) := by
    funext r
    have hr := hρ _ (mrrClamp_mem hτ r)
    exact mrr_integral_withDensityReal _ hr.measurable hr.nonneg _
  rw [this]
  have hG : Measurable fun p : ℝ × Euc d => ρ (mrrClamp τ₀ p.1) p.2 *
      (inner ℝ (Γ a (mrrClamp τ₀ p.1) p.2) u * inner ℝ (Γ a (mrrClamp τ₀ p.1) p.2) v) :=
    hρm.mul (((s105_feat_meas hτ h a).inner measurable_const).mul
      ((s105_feat_meas hτ h a).inner measurable_const))
  exact (hG.stronglyMeasurable.integral_prod_right').measurable

theorem s21m_exists_Db {m T τ₀ : ℝ} (Γ : Fin d → ℝ → Euc d → KSpace d m T) (h : S105Feat d m T τ₀ Γ)
    {ρ : ℝ → Euc d → ℝ} (hρ : ∀ r ∈ Set.Icc (0 : ℝ) τ₀, HRS.Whole.IsProbDensity (ρ r)) (q : ℝ) (hq : 0 ≤ q) :
    ∃ (B : ℝ) (Db : ℝ → (KSpace d m T →L[ℝ] KSpace d m T →L[ℝ] ℝ)),
      (∀ r ∈ Set.Icc (0 : ℝ) τ₀,
        (∀ u v, Db r u v = featureForm m T q (fun a => Γ a r) (HRS.Whole.withDensityReal (ρ r)) u v) ∧
          IsTraceClassCov (Db r) ∧ traceNormForm (Db r) ≤ 2 * d * B ^ 2 * q) ∧
      ∀ r, r ∉ Set.Icc (0 : ℝ) τ₀ → Db r = 0 := by
  classical
  obtain ⟨B, hB0, hB⟩ := h.bound
  have : ∀ r : ℝ, ∃ Bf : KSpace d m T →L[ℝ] KSpace d m T →L[ℝ] ℝ,
      (r ∈ Set.Icc (0 : ℝ) τ₀ →
        (∀ u v, Bf u v = featureForm m T q (fun a => Γ a r) (HRS.Whole.withDensityReal (ρ r)) u v) ∧
          IsTraceClassCov Bf ∧ traceNormForm Bf ≤ 2 * d * B ^ 2 * q) ∧
      (r ∉ Set.Icc (0 : ℝ) τ₀ → Bf = 0) := by
    intro r
    by_cases hr : r ∈ Set.Icc (0 : ℝ) τ₀
    · haveI := HRS.MS.Thm.cb_withDensityReal_isProb (hρ r hr)
      obtain ⟨Bf, h1, h2, h3⟩ := HRS.MS.U9.u9_exists_form (ν := HRS.Whole.withDensityReal (ρ r))
        (Γ := fun a => Γ a r) hq (fun a => (h.cont_x a r hr).measurable) (B := B)
        (fun a x => hB a r hr x)
      refine ⟨Bf, fun _ => ⟨h1, h2, ?_⟩, fun h' => absurd hr h'⟩
      simp only [measure_univ, ENNReal.toReal_one, mul_one] at h3
      exact h3
    · exact ⟨0, fun h' => absurd h' hr, fun _ => rfl⟩
  choose Db hDb using this
  exact ⟨B, Db, fun r hr => (hDb r).1 hr, fun r hr => (hDb r).2 hr⟩

open Classical in
/-- The bounded bilinear form `C̄_r = featureForm(Γ(r), ρ_r dx)`, `0` off `[0,τ₀]`. -/
def s21mDb {m T τ₀ : ℝ} (Γ : Fin d → ℝ → Euc d → KSpace d m T) (h : S105Feat d m T τ₀ Γ) {ρ : ℝ → Euc d → ℝ}
    (hρ : ∀ r ∈ Set.Icc (0 : ℝ) τ₀, HRS.Whole.IsProbDensity (ρ r)) (q : ℝ) (hq : 0 ≤ q) :
    ℝ → (KSpace d m T →L[ℝ] KSpace d m T →L[ℝ] ℝ) :=
  Classical.choose (Classical.choose_spec (s21m_exists_Db Γ h hρ q hq))

theorem s21mDb_spec {m T τ₀ : ℝ} (Γ : Fin d → ℝ → Euc d → KSpace d m T) (h : S105Feat d m T τ₀ Γ)
    {ρ : ℝ → Euc d → ℝ} (hρ : ∀ r ∈ Set.Icc (0 : ℝ) τ₀, HRS.Whole.IsProbDensity (ρ r)) (q : ℝ) (hq : 0 ≤ q)
    {r : ℝ} (hr : r ∈ Set.Icc (0 : ℝ) τ₀) :
    (∀ u v, s21mDb Γ h hρ q hq r u v = featureForm m T q (fun a => Γ a r) (HRS.Whole.withDensityReal (ρ r)) u v) ∧
      IsTraceClassCov (s21mDb Γ h hρ q hq r) ∧
      ∃ B : ℝ, traceNormForm (s21mDb Γ h hρ q hq r) ≤ 2 * d * B ^ 2 * q := by
  have := (Classical.choose_spec (Classical.choose_spec (s21m_exists_Db Γ h hρ q hq))).1 r hr
  exact ⟨this.1, this.2.1, _, this.2.2⟩

theorem s21mDb_bound {m T τ₀ : ℝ} (Γ : Fin d → ℝ → Euc d → KSpace d m T) (h : S105Feat d m T τ₀ Γ)
    {ρ : ℝ → Euc d → ℝ} (hρ : ∀ r ∈ Set.Icc (0 : ℝ) τ₀, HRS.Whole.IsProbDensity (ρ r)) (q : ℝ) (hq : 0 ≤ q) :
    ∃ B : ℝ, ∀ r ∈ Set.Icc (0 : ℝ) τ₀, traceNormForm (s21mDb Γ h hρ q hq r) ≤ 2 * d * B ^ 2 * q := by
  refine ⟨Classical.choose (s21m_exists_Db Γ h hρ q hq), fun r hr => ?_⟩
  exact (Classical.choose_spec (Classical.choose_spec (s21m_exists_Db Γ h hρ q hq))).1 r hr |>.2.2

theorem s21mDb_zero {m T τ₀ : ℝ} (Γ : Fin d → ℝ → Euc d → KSpace d m T) (h : S105Feat d m T τ₀ Γ)
    {ρ : ℝ → Euc d → ℝ} (hρ : ∀ r ∈ Set.Icc (0 : ℝ) τ₀, HRS.Whole.IsProbDensity (ρ r)) (q : ℝ) (hq : 0 ≤ q)
    {r : ℝ} (hr : r ∉ Set.Icc (0 : ℝ) τ₀) : s21mDb Γ h hρ q hq r = 0 :=
  (Classical.choose_spec (Classical.choose_spec (s21m_exists_Db Γ h hρ q hq))).2 r hr

theorem s21mDb_isDet {m T τ₀ : ℝ} (hτ : 0 ≤ τ₀) (Γ : Fin d → ℝ → Euc d → KSpace d m T)
    (h : S105Feat d m T τ₀ Γ) {ρ : ℝ → Euc d → ℝ}
    (hρ : ∀ r ∈ Set.Icc (0 : ℝ) τ₀, HRS.Whole.IsProbDensity (ρ r))
    (hρm : Measurable fun p : ℝ × Euc d => ρ (mrrClamp τ₀ p.1) p.2) (q : ℝ) (hq : 0 ≤ q) :
    IsDetCovDensity τ₀ (s21mDb Γ h hρ q hq) := by
  have hm : ∀ u v : KSpace d m T, Measurable fun r => s21mDb Γ h hρ q hq r u v := by
    intro u v
    have h1 := s21m_featureForm_meas hτ h hρ hρm q u v
    have : (fun r => s21mDb Γ h hρ q hq r u v) = fun r =>
        if r ∈ Set.Icc (0 : ℝ) τ₀ then featureForm m T q (fun a => Γ a (mrrClamp τ₀ r))
          (HRS.Whole.withDensityReal (ρ (mrrClamp τ₀ r))) u v else 0 := by
      funext r
      by_cases hr : r ∈ Set.Icc (0 : ℝ) τ₀
      · rw [if_pos hr, (s21mDb_spec Γ h hρ q hq hr).1, mrrClamp_of_mem hr]
      · rw [if_neg hr, s21mDb_zero Γ h hρ q hq hr]; rfl
    rw [this]
    exact Measurable.ite measurableSet_Icc h1 measurable_const
  refine ⟨hm, fun r hr => (s21mDb_spec Γ h hρ q hq hr).2.1, ?_⟩
  have hmeas : Measurable fun r => traceNormForm (s21mDb Γ h hρ q hq r) :=
    HRS.measurable_traceNormForm _ hm
  obtain ⟨B, hB⟩ := s21mDb_bound Γ h hρ q hq
  refine Measure.integrableOn_of_bounded (M := |2 * d * B ^ 2 * q|) (by simp)
    hmeas.aestronglyMeasurable ?_
  refine (ae_restrict_iff' measurableSet_Icc).2 (Filter.Eventually.of_forall fun r hr => ?_)
  rw [Real.norm_of_nonneg (traceNormForm_nonneg _)]
  exact (hB r hr).trans (le_abs_self _)

/-- The matrix of integrals of a deterministic covariation density over the initial segments is positive semidefinite. -/
theorem s21m_psd_of_entries {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]
    [MeasurableSpace K] [BorelSpace K] [SecondCountableTopology K]
    {τ : ℝ} {Db : ℝ → (K →L[ℝ] K →L[ℝ] ℝ)} (hDet : IsDetCovDensity τ Db) {p : ℕ} (ts : Fin p → ℝ)
    (hts : ∀ a, ts a ∈ Set.Icc (0 : ℝ) τ) (y : Fin p → K) (E : Fin p → Fin p → ℝ)
    (hentry : ∀ a c, E a c = ∫ σ in Set.Icc (0 : ℝ) (min (ts a) (ts c)), Db σ (y a) (y c)) :
    (Matrix.of fun a c => E a c).PosSemidef := by
  classical
  have hint : ∀ u v : K, IntegrableOn (fun σ => Db σ u v) (Set.Icc (0 : ℝ) τ) := by
    intro u v
    refine Integrable.mono' (g := fun σ => traceNormForm (Db σ) * (‖u‖ * ‖v‖)) (hDet.int.mul_const _)
      (hDet.meas u v).aestronglyMeasurable ?_
    rw [ae_restrict_iff' measurableSet_Icc]
    exact Filter.Eventually.of_forall fun σ hσ => by
      rw [Real.norm_eq_abs]
      exact abs_apply_le_tn (hDet.traceClass σ hσ) u v
  have hsymm : ∀ a c, ∫ σ in Set.Icc (0 : ℝ) (min (ts a) (ts c)), Db σ (y a) (y c) =
      ∫ σ in Set.Icc (0 : ℝ) (min (ts c) (ts a)), Db σ (y c) (y a) := by
    intro a c
    rw [min_comm]
    refine setIntegral_congr_fun measurableSet_Icc fun σ hσ => ?_
    exact (hDet.traceClass σ ⟨hσ.1, hσ.2.trans ((min_le_left _ _).trans (hts c).2)⟩).symm _ _
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  refine ⟨?_, fun x => ?_⟩
  · ext a c
    simp only [Matrix.conjTranspose_apply, Matrix.of_apply, star_trivial]
    rw [hentry, hentry, hsymm]
  · set ind : Fin p → ℝ → ℝ := fun a σ => if σ ≤ ts a then x a else 0 with hind
    set w : ℝ → K := fun σ => ∑ a, ind a σ • y a with hw
    set g : Fin p → Fin p → ℝ → ℝ := fun a c => Set.indicator (Set.Icc (0 : ℝ) (min (ts a) (ts c)))
      (fun σ => Db σ (y a) (y c)) with hg
    have hgint : ∀ a c, IntegrableOn (g a c) (Set.Icc (0 : ℝ) τ) := fun a c =>
      (hint (y a) (y c)).indicator measurableSet_Icc
    have hgeq : ∀ a c, ∫ σ in Set.Icc (0 : ℝ) τ, g a c σ =
        ∫ σ in Set.Icc (0 : ℝ) (min (ts a) (ts c)), Db σ (y a) (y c) := by
      intro a c
      rw [hg, setIntegral_indicator measurableSet_Icc]
      have hsub : Set.Icc (0 : ℝ) τ ∩ Set.Icc (0 : ℝ) (min (ts a) (ts c)) =
          Set.Icc (0 : ℝ) (min (ts a) (ts c)) :=
        Set.inter_eq_right.2 (Set.Icc_subset_Icc_right ((min_le_left _ _).trans (hts a).2))
      rw [hsub]
    have hexp : ∀ σ, Db σ (w σ) (w σ) = ∑ a, ∑ c, ind a σ * ind c σ * Db σ (y a) (y c) := by
      intro σ
      simp only [hw, map_sum, map_smul, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
        smul_eq_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => ?_
      ring
    have hpt : ∀ σ ∈ Set.Icc (0 : ℝ) τ, Db σ (w σ) (w σ) = ∑ a, ∑ c, x a * x c * g a c σ := by
      intro σ hσ
      rw [hexp σ]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => ?_
      simp only [hind, hg, Set.indicator, Set.mem_Icc]
      by_cases ha : σ ≤ ts a <;> by_cases hc : σ ≤ ts c
      · have : σ ≤ min (ts a) (ts c) := le_min ha hc
        simp [ha, hc, hσ.1, this]
      · have : ¬ σ ≤ min (ts a) (ts c) := fun h => hc (h.trans (min_le_right _ _))
        simp [ha, hc, this]
      · have : ¬ σ ≤ min (ts a) (ts c) := fun h => ha (h.trans (min_le_left _ _))
        simp [ha, hc, this]
      · have : ¬ σ ≤ min (ts a) (ts c) := fun h => ha (h.trans (min_le_left _ _))
        simp [ha, hc, this]
    have hnn : 0 ≤ ∫ σ in Set.Icc (0 : ℝ) τ, Db σ (w σ) (w σ) :=
      setIntegral_nonneg measurableSet_Icc fun σ hσ => (hDet.traceClass σ hσ).nonneg _
    have hform : dotProduct x (Matrix.mulVec (Matrix.of fun a c => E a c) x) =
        ∑ a, ∑ c, x a * x c * ∫ σ in Set.Icc (0 : ℝ) τ, g a c σ := by
      simp only [dotProduct, Matrix.mulVec, Matrix.of_apply, Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => ?_
      rw [hgeq, hentry]
      ring
    have hswap : ∫ σ in Set.Icc (0 : ℝ) τ, ∑ a, ∑ c, x a * x c * g a c σ =
        ∑ a, ∑ c, x a * x c * ∫ σ in Set.Icc (0 : ℝ) τ, g a c σ := by
      rw [integral_finsetSum _ fun a _ => integrable_finsetSum _ fun c _ => (hgint a c).const_mul _]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [integral_finsetSum _ fun c _ => (hgint a c).const_mul _]
      exact Finset.sum_congr rfl fun c _ => integral_const_mul _ _
    have hcongr : ∫ σ in Set.Icc (0 : ℝ) τ, Db σ (w σ) (w σ) =
        ∫ σ in Set.Icc (0 : ℝ) τ, ∑ a, ∑ c, x a * x c * g a c σ :=
      setIntegral_congr_fun measurableSet_Icc hpt
    have hfin : 0 ≤ dotProduct x (Matrix.mulVec (Matrix.of fun a c => E a c) x) := by
      rw [hform, ← hswap, ← hcongr]; exact hnn
    simpa using hfin

end HRS.MS.S21m
