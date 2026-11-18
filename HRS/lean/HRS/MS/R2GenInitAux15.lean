import HRS.MS.R2GenInitAux14
import HRS.MS.GenPathTie
import HRS.Main.GFB3Aux7
import HRS.MP.RdRemainder

/-!
# S10.5 window comparison, packet B1: a generic `𝒦`-valued feature layer

For a family of features `Γ_a(r,x) ∈ 𝒦_T` (`a < d`, `0 ≤ r ≤ τ₀`) which is bounded, continuous in `x` and weakly measurable in `r`
(`S105Feat`; the window features jump at `r = b`): joint measurability of the time-clamped family, the clamped `𝒦`-valued Hilbert-Schmidt integrand `s105Phi` of the empirical
noise (progressive on every horizon), the covariation `hsCovForm = featureForm` of the empirical measure and the existence of the
`𝒦`-valued Itô integral `M` with this covariation on `[0,τ₀]`.  This is the window analogue of `GenPathAux19-21` (written for the
window features `r2WindowFeature`, whose time horizon `τ₀ = b + T` differs from the horizon `T` of `𝒦_T`).
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.R2GenInit

open HRS HRS.Whole HRS.MP.RdRem HRS.MS.GenPath

variable {d : ℕ}

/-- The regularity of a window feature family (see the module docstring). -/
structure S105Feat (d : ℕ) (m T τ₀ : ℝ) (Γ : Fin d → ℝ → Euc d → KSpace d m T) : Prop where
  bound : ∃ B : ℝ, 0 ≤ B ∧ ∀ a, ∀ r ∈ Set.Icc (0 : ℝ) τ₀, ∀ x, ‖Γ a r x‖ ≤ B
  cont_x : ∀ a, ∀ r ∈ Set.Icc (0 : ℝ) τ₀, Continuous (Γ a r)
  weak_r : ∀ a x (e : KSpace d m T), Measurable (fun r => inner ℝ e (Γ a (mrrClamp τ₀ r) x))

theorem s105_feat_meas {m T τ₀ : ℝ} (hτ : 0 ≤ τ₀) {Γ : Fin d → ℝ → Euc d → KSpace d m T}
    (h : S105Feat d m T τ₀ Γ) (a : Fin d) :
    Measurable fun p : ℝ × Euc d => Γ a (mrrClamp τ₀ p.1) p.2 := by
  obtain ⟨ι, hι, e, -⟩ := HilbertCLTAux.exists_hilbertBasis_type (H := KSpace d m T)
  haveI := hι
  refine measurable_of_inner_basis e fun i => ?_
  have hcont : ∀ r : ℝ, Continuous fun x : Euc d => inner ℝ (e i) (Γ a (mrrClamp τ₀ r) x) := fun r =>
    continuous_const.inner (h.cont_x a _ (mrrClamp_mem hτ r))
  exact s56_carath (fun (x : Euc d) (r : ℝ) => inner ℝ (e i) (Γ a (mrrClamp τ₀ r) x)) hcont (fun x =>
    h.weak_r a x (e i))

/-- The clamped `𝒦`-valued noise integrand. -/
def s105Phi {Ω : Type*} {N : ℕ} {m T : ℝ} (Γ : Fin d → ℝ → Euc d → KSpace d m T) (τ₀ q : ℝ)
    (X : ℝ≥0 → Ω → EucConfig d N) : ℝ → Ω → Fin N × Fin d → KSpace d m T :=
  fun r ζ ia => Real.sqrt (2 * q / N) • Γ ia.2 (mrrClamp τ₀ r) (X (Real.toNNReal r) ζ ia.1)

theorem s105_phi_isHS {m T τ₀ : ℝ} (hτ : 0 ≤ τ₀) {Γ : Fin d → ℝ → Euc d → KSpace d m T}
    (h : S105Feat d m T τ₀ Γ) (N : ℕ) (q : ℝ) {Ω : Type} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ℱ : Filtration ℝ mΩ) (X : ℝ≥0 → Ω → EucConfig d N)
    (hprog : IsProgressive ℱ (ofNNRealTime X)) (τ : ℝ) :
    IsHSIntegrand P ℱ τ (s105Phi Γ τ₀ q X) := by
  obtain ⟨Cf, hCf0, hCf⟩ := h.bound
  refine ⟨?_, fun r ζ => Summable.of_finite, ?_⟩
  · intro k i
    have hp : Measurable fun p : ℝ × EucConfig d N => ((p.1, p.2 k.1) : ℝ × Euc d) :=
      measurable_fst.prodMk ((measurable_pi_apply k.1).comp measurable_snd)
    have hf : Measurable fun p : ℝ × EucConfig d N => Γ k.2 (mrrClamp τ₀ p.1) (p.2 k.1) :=
      Measurable.comp (g := fun p : ℝ × Euc d => Γ k.2 (mrrClamp τ₀ p.1) p.2)
        (f := fun p : ℝ × EucConfig d N => ((p.1, p.2 k.1) : ℝ × Euc d))
        (s105_feat_meas hτ h k.2) hp
    have hg : Measurable fun p : ℝ × EucConfig d N => Real.sqrt (2 * q / N) •
        Γ k.2 (mrrClamp τ₀ p.1) (p.2 k.1) := hf.const_smul (Real.sqrt (2 * q / N))
    have hX := hprog i
    have h1 : Measurable[Subtype.instMeasurableSpace.prod (ℱ i)]
        fun p : Set.Iic i × Ω => (p.1 : ℝ) :=
      measurable_subtype_coe.comp measurable_fst
    exact s56_meas_comp (Subtype.instMeasurableSpace.prod (ℱ i)) hg h1 hX
  · set B : ℝ := |Real.sqrt (2 * q / N)| * |Cf| with hB
    have hnorm : ∀ r ζ (k : Fin N × Fin d), ‖s105Phi Γ τ₀ q X r ζ k‖ ≤ B := by
      intro r ζ k
      unfold s105Phi
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left ((hCf k.2 _ (mrrClamp_mem hτ r) _).trans (le_abs_self _)) (abs_nonneg _)
    have hpt : ∀ r ζ, ∑' k : Fin N × Fin d, ‖s105Phi Γ τ₀ q X r ζ k‖ₑ ^ 2 ≤
        ((N * d : ℕ) : ℝ≥0∞) * ENNReal.ofReal B ^ 2 := by
      intro r ζ
      rw [tsum_fintype]
      calc ∑ k : Fin N × Fin d, ‖s105Phi Γ τ₀ q X r ζ k‖ₑ ^ 2
          ≤ ∑ _k : Fin N × Fin d, ENNReal.ofReal B ^ 2 := by
            refine Finset.sum_le_sum fun k _ => ?_
            refine pow_le_pow_left' ?_ 2
            rw [← ofReal_norm]
            exact ENNReal.ofReal_le_ofReal (hnorm r ζ k)
        _ = ((N * d : ℕ) : ℝ≥0∞) * ENNReal.ofReal B ^ 2 := by
            simp [Finset.sum_const, Finset.card_univ]
    unfold hsSqIntegralOn
    refine lt_of_le_of_lt (lintegral_mono fun ζ => lintegral_mono fun r => hpt r ζ) ?_
    simp only [lintegral_const, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
      Real.volume_Icc, measure_univ, mul_one]
    refine ENNReal.mul_lt_top ?_ ?_
    · exact ENNReal.mul_lt_top (ENNReal.natCast_lt_top _) (ENNReal.pow_lt_top ENNReal.ofReal_lt_top)
    · exact ENNReal.ofReal_lt_top

theorem s105_hsCov_eq {m T : ℝ} (Γ : Fin d → ℝ → Euc d → KSpace d m T) (τ₀ q : ℝ) (hq : 0 ≤ q) {N : ℕ}
    (hN : 1 ≤ N) (r : ℝ) (x : EucConfig d N) (u v : KSpace d m T) :
    hsCovForm (fun k : Fin N × Fin d =>
        Real.sqrt (2 * q / N) • Γ k.2 (mrrClamp τ₀ r) (x k.1)) u v =
      featureForm m T q (fun a => Γ a (mrrClamp τ₀ r)) (HRS.Whole.empirical x) u v := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hsum : Summable fun k : Fin N × Fin d =>
      ‖Real.sqrt (2 * q / N) • Γ k.2 (mrrClamp τ₀ r) (x k.1)‖ ^ 2 := Summable.of_finite
  rw [hsCovForm_apply hsum]
  unfold featureForm
  rw [tsum_fintype, Fintype.sum_prod_type, Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  have hint : ∫ y, inner ℝ (Γ a (mrrClamp τ₀ r) y) u * inner ℝ (Γ a (mrrClamp τ₀ r) y) v ∂(HRS.Whole.empirical x) =
      (N : ℝ)⁻¹ * ∑ i, inner ℝ (Γ a (mrrClamp τ₀ r) (x i)) u * inner ℝ (Γ a (mrrClamp τ₀ r) (x i)) v :=
    HRS.Whole.pair_empirical hN (x) (fun y => inner ℝ (Γ a (mrrClamp τ₀ r) y) u *
      inner ℝ (Γ a (mrrClamp τ₀ r) y) v)
  rw [hint, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [inner_smul_left, conj_trivial]
  have h2 : Real.sqrt (2 * q / N) * Real.sqrt (2 * q / N) = 2 * q / N :=
    Real.mul_self_sqrt (by positivity)
  calc Real.sqrt (2 * q / N) * inner ℝ (Γ a (mrrClamp τ₀ r) (x i)) u *
        (Real.sqrt (2 * q / N) * inner ℝ (Γ a (mrrClamp τ₀ r) (x i)) v)
      = (Real.sqrt (2 * q / N) * Real.sqrt (2 * q / N)) *
        (inner ℝ (Γ a (mrrClamp τ₀ r) (x i)) u * inner ℝ (Γ a (mrrClamp τ₀ r) (x i)) v) := by ring
    _ = _ := by rw [h2]; field_simp

theorem s105_particle_martingale {m T τ₀ : ℝ} (hτ : 0 ≤ τ₀) {Γ : Fin d → ℝ → Euc d → KSpace d m T}
    (h : S105Feat d m T τ₀ Γ) (N : ℕ) (hN : 1 ≤ N) (q : ℝ) (hq : 0 ≤ q)
    {Ω : Type} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ℱ : Filtration ℝ mΩ) (W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ) (X : ℝ≥0 → Ω → EucConfig d N)
    (hB : IsBrownianFiltration P ℱ W') (hprog : IsProgressive ℱ (ofNNRealTime X)) :
    ∃ M : ℝ → Ω → KSpace d m T,
      IsHilbertItoIntegral P ℱ W' (s105Phi Γ τ₀ q X) M ∧
      IsHilbertMartingaleWithCovariation P ℱ τ₀ M (fun r ζ => hsCovForm (s105Phi Γ τ₀ q X r ζ)) := by
  have hW : IsCylindricalBrownian P ℱ W' := HRS.GF.gfb3_isCylindricalBrownian_of_filtration hB
  have hZ := fun τ => s105_phi_isHS hτ h N q P ℱ X hprog τ
  obtain ⟨Mart, hc, had, hz, hJ⟩ := HRS.GF.gfb3_exists_hilbert_version hW hZ
  refine ⟨Mart, ⟨hc, had, hz, ?_⟩, ?_⟩
  · intro τ hτ' x
    obtain ⟨J, hIJ, hae⟩ := hJ x
    refine (hIJ.approx τ hτ').congr fun s => ?_
    refine lintegral_congr_ae ?_
    filter_upwards [hae τ hτ'] with ω h
    rw [h]
    rfl
  · have hM := HRS.Uniform.Q07c.isHM_of_ito hW hZ hc had hz hJ τ₀
    exact hM

end HRS.MS.R2GenInit
