import HRS.MS.MfeConfAux1
import HRS.MS.MfeConfAux2
import HRS.PDE.MovSpecAux
import HRS.MS.Canon
import HRS.MS.WrSmlAux1
import HRS.MS.ThmCons
import HRS.MS.AdjConvAux1

/-!
# S.B.1: whole-space `mfe41_ac`, the dissipation interface (DISS), and the conditional assembly

* `sb1_mfe_ac`: finite relative entropy with respect to `μ^{⊗N}` (`μ = ρ dx`) gives `f ≪ volume` and `f`-a.e. no collision
  (whole-space `HRS.mfe41_ac`).
* `MfeDiss`: (DISS), the integrated modulated-free-energy dissipation inequality of the whole-space `mov_mfe_ineq`
  (`𝖤_N(f_t,μ_t) ≤ 𝖤_N(f_0,μ_0) - ½∫_0^t∫ Comm_N(u_V^r;·,μ_r) f_r dr` with the integrability clauses), exactly the torus
  `HRS.mov_mfe_ineq` conclusion (TeX S L11118-11130, the identity `B:eq:mfe-confined-smooth-differential` after passage to the
  selected law).  It is the only unproved ingredient of S.B.1 (plan packets F1-F11, `docs/SB1_PLAN.md`).
* `sb1_core`: Grönwall assembly (the torus `mfe_uniform_proof`): (DISS) + coercivity `F_N + o_N ≥ 0` + the commutator
  bound `|Comm_N(u_V^r)| ≤ A K_r (F_N + o_N)` give `𝖤(t) + o ≤ exp((A/2)∫K)(𝖤(0) + o)`.
* `sb1_super_of_diss`, `sb1_sub_of_diss`: both frozen statements of S.B.1, with the dissipation inequality (for the exact regime
  hypotheses of the statement) as the clean hypothesis `SuperDiss`, `SubDiss`.  Once (DISS) is proved they close the frozen
  statements by `example := (@mfe_confined_rd_gradient_super_proof : type_of% @HRS.Whole.mfe_confined_rd_gradient_super)`.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.MfeConf

variable {d : ℕ}

/-! ### SB1-D: absolute continuity and collision-freeness from finite entropy -/

theorem sb1_mfe_ac (hd : 1 ≤ d) {N : ℕ} {ρ : Euc d → ℝ} (hρ : Whole.IsProbDensity ρ)
    {ν : Measure (Whole.EucConfig d N)}
    (h : relEntropy ν (Measure.pi fun _ : Fin N => Whole.withDensityReal ρ) ≠ ⊤) :
    ν ≪ (volume : Measure (Whole.EucConfig d N)) ∧ ∀ᵐ Z ∂ν, Z ∉ Whole.eucCollisionSet d N := by
  have hac : ν ≪ Measure.pi fun _ : Fin N => Whole.withDensityReal ρ := by
    unfold relEntropy at h
    exact (InformationTheory.klDiv_ne_top_iff.mp h).1
  have hi : Integrable ρ := by
    by_contra hni
    have := hρ.integral_one
    rw [integral_undef hni] at this
    norm_num at this
  have hpv : (Measure.pi fun _ : Fin N => Whole.withDensityReal ρ) ≪
      (volume : Measure (Whole.EucConfig d N)) := by
    rw [HRS.MS.Canon.cn_pi_withDensityReal ρ hρ.nonneg hi]
    exact withDensity_absolutelyContinuous _ _
  haveI : IsProbabilityMeasure (Whole.withDensityReal ρ) :=
    HRS.MS.Thm.cb_withDensityReal_isProb hρ
  have hae := HRS.MS.Wr.ae_injective_pi_Euc (N := N) (HRS.MS.Wr.wr12_atomless hd ρ)
  refine ⟨hac.trans hpv, hac.ae_le ?_⟩
  filter_upwards [hae] with Z hZ hcol
  obtain ⟨i, j, hij, hZij⟩ := hcol
  exact hZ i j hij hZij

/-! ### The dissipation interface (DISS) -/

/-- (DISS): the conclusion of the whole-space `mov_mfe_ineq` (torus `HRS.mov_mfe_ineq`, `MovSpec3.lean`) for the particle
process `X`, the initial law `P.map X₀` and the mean-field trajectory `ρ`: for all `t ∈ [0,T]`, `𝖤_N(f_t, μ_t) < ∞`,
`Comm_N(u_V^r; ·, μ_r)` is `f_r`-integrable, `r ↦ ∫ Comm_N f_r` is integrable on `[0,t]`, and
`𝖤_N(f_t, μ_t) ≤ 𝖤_N(f_0, μ_0) - ½ ∫_0^t ∫ Comm_N(u_V^r; Z, μ_r) f_r(dZ) dr`. -/
def MfeDiss (d : ℕ) (D : Whole.WholeDyn d) (N : ℕ) (T : ℝ) (ρ : ℝ → Euc d → ℝ) {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω) (X₀ : Ω → Whole.EucConfig d N)
    (X : ℝ≥0 → Ω → Whole.EucConfig d N) : Prop :=
  ∀ t ∈ Set.Icc (0 : ℝ) T,
    Whole.MFEFiniteW d D.s (P.map (X t.toNNReal)) (Whole.withDensityReal (ρ t)) ∧
    (∀ r ∈ Set.Icc (0 : ℝ) t, Integrable (fun Z => Whole.commN d D.s (Whole.mfeTransportW D (ρ r)) Z
      (Whole.withDensityReal (ρ r))) (P.map (X r.toNNReal))) ∧
    IntegrableOn (fun r => ∫ Z, Whole.commN d D.s (Whole.mfeTransportW D (ρ r)) Z
      (Whole.withDensityReal (ρ r)) ∂(P.map (X r.toNNReal))) (Set.Icc 0 t) ∧
    Whole.modulatedFreeEnergyW d D.s D.invβ (P.map (X t.toNNReal)) (Whole.withDensityReal (ρ t)) ≤
      Whole.modulatedFreeEnergyW d D.s D.invβ (P.map X₀) (Whole.withDensityReal (ρ 0)) -
        (1 / 2) * ∫ r in Set.Icc 0 t, ∫ Z, Whole.commN d D.s (Whole.mfeTransportW D (ρ r)) Z
          (Whole.withDensityReal (ρ r)) ∂(P.map (X r.toNNReal))

/-- Integration of a pointwise commutator bound against a probability measure (as `HRS.mfe41_int`). -/
theorem sb1_int_bound {α : Type*} [MeasurableSpace α] {ν : Measure α} [IsProbabilityMeasure ν]
    {F c : α → ℝ} {o B : ℝ} (hF : Integrable F ν) (hnn : ∀ᵐ z ∂ν, 0 ≤ F z + o)
    (hc : ∀ᵐ z ∂ν, |c z| ≤ B * (F z + o)) :
    0 ≤ ∫ z, F z ∂ν + o ∧ |∫ z, c z ∂ν| ≤ B * (∫ z, F z ∂ν + o) := by
  have hint : Integrable (fun z => F z + o) ν := hF.add (integrable_const o)
  have hI : ∫ z, (F z + o) ∂ν = ∫ z, F z ∂ν + o := by
    rw [integral_add hF (integrable_const o)]
    simp
  refine ⟨?_, ?_⟩
  · rw [← hI]
    exact integral_nonneg_of_ae hnn
  · have h1 := norm_integral_le_of_norm_le (hint.const_mul B)
      (hc.mono fun z hz => by rw [Real.norm_eq_abs]; exact hz)
    rw [integral_const_mul, hI] at h1
    simpa [Real.norm_eq_abs] using h1

/-! ### The Grönwall assembly -/

/-- **Core of S.B.1**: (DISS), coercivity and the commutator bound give the Grönwall inequality with constant `A/2`. -/
theorem sb1_core (hd : 1 ≤ d) {D : Whole.WholeDyn d} {N : ℕ} (hN : 2 ≤ N) {T Λ : ℝ} {k : ℕ}
    (hT : 0 ≤ T) {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ρ : ℝ → Euc d → ℝ} {X₀ : Ω → Whole.EucConfig d N} {W : ℝ≥0 → Ω → (Fin N → Euc d)}
    {X : ℝ≥0 → Ω → Whole.EucConfig d N}
    (h : Whole.WholeMFEHyp P D N T Λ k ρ X₀ W X) {C₀ A : ℝ} (hA : 0 ≤ A)
    (hCN : Whole.AppendixA.CompletionNonnegRd d D.s C₀)
    {K : ℝ → ℝ} (hKi : IntegrableOn K (Set.Icc 0 T)) (hK0 : ∀ r ∈ Set.Icc (0 : ℝ) T, 0 ≤ K r)
    (hcomm : ∀ r ∈ Set.Icc (0 : ℝ) T, ∀ Z : Whole.EucConfig d N, Function.Injective Z →
      |Whole.commN d D.s (Whole.mfeTransportW D (ρ r)) Z (Whole.withDensityReal (ρ r))| ≤
        A * K r * (Whole.rieszModulatedEnergy d D.s Z (Whole.withDensityReal (ρ r)) +
          oNΛ d D.s C₀ Λ N))
    (hDiss : MfeDiss d D N T ρ P X₀ X) :
    ∀ t ∈ Set.Icc (0 : ℝ) T,
      (P.map (X (Real.toNNReal t))).AbsolutelyContinuous volume ∧
      Whole.MFEFiniteW d D.s (P.map (X (Real.toNNReal t))) (Whole.withDensityReal (ρ t)) ∧
      Whole.modulatedFreeEnergyW d D.s D.invβ (P.map (X (Real.toNNReal t)))
          (Whole.withDensityReal (ρ t)) + oNΛ d D.s C₀ Λ N ≤
        Real.exp (A / 2 * ∫ r in Set.Icc 0 T, K r) *
          (Whole.modulatedFreeEnergyW d D.s D.invβ (P.map X₀) (Whole.withDensityReal (ρ 0)) +
            oNΛ d D.s C₀ Λ N) := by
  have hΛ1 : 1 ≤ Λ := h.Λ_ge
  have hΛ0 : 0 ≤ Λ := by linarith
  have hβ : 0 < D.invβ := h.pos_temp
  set o : ℝ := oNΛ d D.s C₀ Λ N with ho
  obtain ⟨Lm, hLm⟩ := sb1_regular_density_bounds (d := d) k Λ
  have hmax : max Λ 0 = Λ := max_eq_left hΛ0
  have hρprob : ∀ r ∈ Set.Icc (0 : ℝ) T, Whole.IsProbDensity (ρ r) := fun r hr => h.mf.density r hr
  have hρΛ : ∀ r ∈ Set.Icc (0 : ℝ) T, ∀ x, ρ r x ≤ Λ := fun r hr x => by
    have := (hLm (ρ r) (hρprob r hr) (h.mf_reg r hr)).1 x
    rwa [hmax] at this
  have hlog : ∀ r ∈ Set.Icc (0 : ℝ) T, D.s = 0 →
      Integrable (fun x : Euc d => Real.log (2 + ‖x‖)) (Whole.withDensityReal (ρ r)) :=
    fun r hr _ => (hLm (ρ r) (hρprob r hr) (h.mf_reg r hr)).2.2.1
  have hXm : ∀ t : ℝ≥0, Measurable (X t) := h.sol.adapted
  have hX0m : AEMeasurable X₀ P := by
    have h0 : AEMeasurable (X 0) P := (hXm 0).aemeasurable
    exact h0.congr (by filter_upwards [h.sol.init] with ζ hζ using hζ)
  haveI hP0 : IsProbabilityMeasure (P.map X₀) :=
    (Measure.isProbabilityMeasure_map_iff hX0m).2 inferInstance
  haveI hfp : ∀ r : ℝ, IsProbabilityMeasure (P.map (X r.toNNReal)) := fun r =>
    (Measure.isProbabilityMeasure_map_iff (hXm _).aemeasurable).2 inferInstance
  -- general bounds for a probability measure ν of finite modulated free energy at time r
  have hbd : ∀ r ∈ Set.Icc (0 : ℝ) T, ∀ (ν : Measure (Whole.EucConfig d N)) [IsProbabilityMeasure ν],
      Whole.MFEFiniteW d D.s ν (Whole.withDensityReal (ρ r)) →
      0 ≤ ∫ Z, Whole.rieszModulatedEnergy d D.s Z (Whole.withDensityReal (ρ r)) ∂ν + o ∧
      |∫ Z, Whole.commN d D.s (Whole.mfeTransportW D (ρ r)) Z (Whole.withDensityReal (ρ r)) ∂ν| ≤
        A * K r * (∫ Z, Whole.rieszModulatedEnergy d D.s Z (Whole.withDensityReal (ρ r)) ∂ν + o) ∧
      ∫ Z, Whole.rieszModulatedEnergy d D.s Z (Whole.withDensityReal (ρ r)) ∂ν + o ≤
        Whole.modulatedFreeEnergyW d D.s D.invβ ν (Whole.withDensityReal (ρ r)) + o := by
    intro r hr ν _ hfin
    obtain ⟨-, hae⟩ := sb1_mfe_ac hd (hρprob r hr) hfin.1
    have hnn' : ∀ᵐ Z ∂ν, 0 ≤ Whole.rieszModulatedEnergy d D.s Z (Whole.withDensityReal (ρ r)) + o := by
      filter_upwards [hae] with Z hZ
      exact hCN.2 Λ hΛ1 N hN (ρ r) (hρprob r hr) (hρΛ r hr) (hlog r hr) Z hZ
    have hc' : ∀ᵐ Z ∂ν, |Whole.commN d D.s (Whole.mfeTransportW D (ρ r)) Z
        (Whole.withDensityReal (ρ r))| ≤ A * K r *
          (Whole.rieszModulatedEnergy d D.s Z (Whole.withDensityReal (ρ r)) + o) := by
      filter_upwards [hae] with Z hZ
      exact hcomm r hr Z ((HRS.MH.CoercLower.eucCollisionSet_iff).1 hZ)
    obtain ⟨h1, h2⟩ := sb1_int_bound hfin.2 hnn' hc'
    refine ⟨h1, h2, ?_⟩
    unfold Whole.modulatedFreeEnergyW
    have : 0 ≤ D.invβ * (relEntropy ν (Measure.pi fun _ : Fin N => Whole.withDensityReal (ρ r)) /
        (N : ℝ≥0∞)).toReal := mul_nonneg hβ.le ENNReal.toReal_nonneg
    linarith
  -- Grönwall
  have hT' : T ∈ Set.Icc (0 : ℝ) T := ⟨hT, le_rfl⟩
  have hint := (hDiss T hT').2.2.1
  have hgr := movspec_gronwall_var (T := T)
    (u0 := Whole.modulatedFreeEnergyW d D.s D.invβ (P.map X₀) (Whole.withDensityReal (ρ 0)) + o)
    (a := fun r => A / 2 * K r)
    (G := fun r => -(1 / 2) * ∫ Z, Whole.commN d D.s (Whole.mfeTransportW D (ρ r)) Z
        (Whole.withDensityReal (ρ r)) ∂(P.map (X r.toNNReal)))
    (u := fun r => Whole.modulatedFreeEnergyW d D.s D.invβ (P.map (X r.toNNReal))
      (Whole.withDensityReal (ρ r)) + o)
    (fun r hr => mul_nonneg (by positivity) (hK0 r hr)) (hKi.const_mul _) (hint.const_mul _)
    (fun t ht => by
      have := (hDiss t ht).2.2.2
      rw [integral_const_mul]
      linarith)
    (fun r hr => by
      obtain ⟨-, h2, h3⟩ := hbd r hr (P.map (X r.toNNReal)) (hDiss r hr).1
      have h4 := neg_abs_le (∫ Z, Whole.commN d D.s (Whole.mfeTransportW D (ρ r)) Z
        (Whole.withDensityReal (ρ r)) ∂(P.map (X r.toNNReal)))
      have h5 : 0 ≤ A * K r := mul_nonneg hA (hK0 r hr)
      have h6 := mul_le_mul_of_nonneg_left h3 h5
      nlinarith)
  obtain ⟨hu0, -, hu0'⟩ := hbd 0 ⟨le_rfl, hT⟩ (P.map X₀) h.mfe_init
  intro t ht
  refine ⟨?_, (hDiss t ht).1, ?_⟩
  · exact (sb1_mfe_ac hd (hρprob t ht) (hDiss t ht).1.1).1
  · have h1 := hgr t ht
    refine h1.trans ?_
    have hu0n : 0 ≤ Whole.modulatedFreeEnergyW d D.s D.invβ (P.map X₀)
        (Whole.withDensityReal (ρ 0)) + o := by linarith
    rw [mul_comm]
    refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr ?_) hu0n
    rw [integral_const_mul]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    exact setIntegral_mono_set hKi (ae_restrict_of_forall_mem measurableSet_Icc (fun r hr => hK0 r hr))
      (Eventually.of_forall (Set.Icc_subset_Icc le_rfl ht.2))

end HRS.MS.MfeConf

end
