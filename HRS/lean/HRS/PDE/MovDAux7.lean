import HRS.PDE.MovDAux6
import HRS.PDE.MovSXFinal
import HRS.PDE.MovAFinal
import HRS.PDE.MovBAux4
import HRS.PDE.MovRepairAux1

/-!
# MOVD Aux7: `movT_source_limit_cond` for the unregularised system

Clean copies of `movT_Q_isProb` and of the integrability of `C_N` (using the `_proof` packets of MOVSX/MOVA), the joint
measurability of the exact source off collisions (from the regularised sources `movT_srcReg` and the packet
`movT_srcReg_tendsto`), and the assembly from `movd_limit_cond_abstract`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory Set InformationTheory
open scoped ENNReal NNReal BigOperators

namespace HRS

variable {d N : ℕ}

theorem movd_Q_isProb (hN : 2 ≤ N) {D : DynData d} {T : ℝ} {ρ : ℝ → Torus d → ℝ} (h : MovTraj D T ρ)
    {r : ℝ} (hr : r ∈ Set.Icc 0 T) :
    IsProbabilityMeasure (movT_Q (periodicRiesz d D.s) D N ρ r) := by
  have hd : 1 ≤ d := b15_one_le_d D
  have hβ : 0 < D.invβ⁻¹ := inv_pos.2 h.pos_temp
  have hμ : IsProbabilityMeasure (withDensityReal (ρ r)) := isProb_withDensityReal (h.mf.density r hr)
  obtain ⟨Bg, hBg⟩ := b15_periodicRiesz_lower D
  have hw : ∀ z : Torus d, z ≠ 0 → 1 ≤ periodicRiesz d D.s z + (Bg + 1) := fun z _ => by
    have := hBg z; linarith
  have hcont : Continuous (ρ r) := b15_continuous_of_isCk (h.ck r hr)
  obtain ⟨x₀, -, hx₀⟩ := isCompact_univ.exists_isMinOn (Set.univ_nonempty (α := Torus d))
    hcont.continuousOn
  have hc₀ : 0 < ρ r x₀ := h.pos r hr x₀
  obtain ⟨Λ₂, hΛ₂⟩ := h.bounds
  obtain ⟨θ₀, C, hθ₀, hC, hP⟩ := movT_pressure_two_sided_C2_proof hd D.s D.hs0 D.hsd (Bg + 1) hw D.invβ⁻¹
    D.invβ⁻¹ hβ (ρ r x₀) hc₀ Λ₂ 0
  have hP0 := hP (ρ r) (h.mf.density r hr) (h.ck r hr) (fun x => hx₀ (Set.mem_univ x))
    (hΛ₂ r hr) (fun _ _ => 0) measurable_const (fun _ _ => rfl) (fun x y => by simp) N hN
    D.invβ⁻¹ ⟨le_rfl, le_rfl⟩ 0 (by simp [hθ₀.le])
  simp only [zero_mul, sub_zero] at hP0
  obtain ⟨hlow, hup⟩ := hP0
  have hK0 : ∫⁻ X : Config d N, ENNReal.ofReal (Real.exp (-D.invβ⁻¹ * N *
      modulatedEnergy (fun x y => periodicRiesz d D.s (x - y)) X (withDensityReal (ρ r))))
      ∂(Measure.pi fun _ : Fin N => withDensityReal (ρ r)) ≠ 0 := by
    intro h0
    rw [h0] at hlow
    simp at hlow
    exact absurd hlow (not_le.2 (Real.exp_pos _))
  have hKt : ∫⁻ X : Config d N, ENNReal.ofReal (Real.exp (-D.invβ⁻¹ * N *
      modulatedEnergy (fun x y => periodicRiesz d D.s (x - y)) X (withDensityReal (ρ r))))
      ∂(Measure.pi fun _ : Fin N => withDensityReal (ρ r)) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hup
  obtain ⟨Mρ, hMρ0, hMρ⟩ := exists_abs_bound hcont
  have hρΛ : ∀ x, ρ r x ≤ Mρ := fun x => (le_abs_self _).trans (hMρ x)
  obtain ⟨hgR, -⟩ := rowOK_g_h hd D.s D.hs0 D.hsd (Bg + 1) hw 0 hMρ0 hρΛ
    (h := fun _ _ => 0) measurable_const (fun x y => by simp)
  exact (gibbs_facts hgR hK0 hKt).2



theorem movd_comm_integrable (hN : 2 ≤ N) {D : DynData d} {T : ℝ} {ρ : ℝ → Torus d → ℝ}
    (htr : MovTraj D T ρ) :
    ∀ r ∈ Set.Icc 0 T,
      Integrable (movT_comm D N ρ r) (movT_Q (periodicRiesz d D.s) D N ρ r) := by
  obtain ⟨c₀, Lu, hc₀, hLu, hρlow, hLip⟩ := movT_traj_bounds_proof htr
  obtain ⟨Λ₂, hΛ⟩ := htr.bounds
  obtain ⟨l, C₁, hl, hexp⟩ := movT_source_exp_proof (b15_one_le_d D) D.hs0 D.hsd D.invβ⁻¹ D.invβ⁻¹
    (inv_pos.2 htr.pos_temp) c₀ hc₀ Λ₂
  intro r hr
  exact (hexp D rfl ⟨le_rfl, le_rfl⟩ (ρ r) (htr.mf.density r hr) (htr.ck r hr) (hρlow r hr) (hΛ r hr)
    Lu hLu (hLip r hr) N hN).1

theorem movd_source_aemeasurable (hN : 2 ≤ N) {D : DynData d} {T : ℝ} {ρ : ℝ → Torus d → ℝ}
    (htr : MovTraj D T ρ) {r : ℝ} (hr : r ∈ Set.Icc 0 T) :
    AEMeasurable (movT_source D N ρ r) (movT_Q (periodicRiesz d D.s) D N ρ r) := by
  have h1 := (movd_comm_integrable hN htr r hr).aemeasurable
  unfold movT_source movT_sourceAt
  exact (h1.sub aemeasurable_const).const_mul _

/-- The exact source is a measurable function of `(r, Z)` off the collision set (limit of the regularised sources,
which are jointly continuous). -/
theorem movd_source_joint_measurable (hN : 2 ≤ N) {D : DynData d} {T : ℝ} {ρ : ℝ → Torus d → ℝ}
    (htr : MovTraj D T ρ) :
    ∃ Ψ : ℝ × Config d N → ℝ, Measurable Ψ ∧
      ∀ r ∈ Set.Icc 0 T, ∀ Z : Config d N, Z ∉ collisionSet d N → Ψ (r, Z) = movT_source D N ρ r Z := by
  by_cases hT : 0 ≤ T
  swap
  · exact ⟨fun _ => 0, measurable_const, fun r hr => absurd (hr.1.trans hr.2) hT⟩
  classical
  obtain ⟨ρt, hρt, hgood⟩ := movrepair_good_test (N := N) hN htr
  have hcoll : MeasurableSet (collisionSet d N) := (isClosed_collisionSet d N).measurableSet
  let clamp : ℝ → ℝ := fun r => (Set.projIcc 0 T hT r : ℝ)
  have hclamp : ∀ r, clamp r ∈ Set.Icc 0 T := fun r => (Set.projIcc 0 T hT r).2
  let f : ℕ → ℝ × Config d N → ℝ := fun n p =>
    if p.2 ∈ collisionSet d N then 0 else movT_srcReg D N (n : ℝ) ρ ρt (clamp p.1) p.2
  let g : ℝ × Config d N → ℝ := fun p =>
    if p.2 ∈ collisionSet d N then 0 else movT_source D N ρ (clamp p.1) p.2
  have hN' : 0 < N := by omega
  have hf : ∀ n, Measurable (f n) := by
    intro n
    have hc := movb_srcReg_cont hN' D htr.gradient htr.pos_temp htr.V_reg (n : ℝ) hρt
      htr.mf.density htr.pos
    have hpr : Continuous fun p : ℝ × Config d N =>
        ((Set.projIcc 0 T hT p.1, p.2) : Set.Icc (0 : ℝ) T × Config d N) :=
      (continuous_projIcc.comp continuous_fst).prodMk continuous_snd
    have hc' : Continuous fun p : ℝ × Config d N =>
        movT_srcReg D N (n : ℝ) ρ ρt (clamp p.1) p.2 := by
      have h2 := hc.comp' hpr
      dsimp only at h2
      exact h2
    exact Measurable.ite (measurable_snd hcoll) measurable_const hc'.measurable
  have hlim : Tendsto f atTop (𝓝 g) := by
    refine tendsto_pi_nhds.2 fun p => ?_
    by_cases hp : p.2 ∈ collisionSet d N
    · simp only [f, g, hp, if_true]; exact tendsto_const_nhds
    · simp only [f, g, hp, if_false]
      exact hgood (M := fun n : ℕ => (n : ℝ)) tendsto_natCast_atTop_atTop (hclamp p.1) hp
  refine ⟨g, measurable_of_tendsto_metrizable' atTop hf hlim, fun r hr Z hZ => ?_⟩
  have : clamp r = r := by
    simp only [clamp]; rw [Set.projIcc_of_mem _ hr]
  simp only [g, hZ, if_false, this]

theorem movd_source_limit_cond (hN : 2 ≤ N) {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {D : DynData d} {T : ℝ} {ρ : ℝ → Torus d → ℝ} {X₀ : Ω → Config d N}
    {W : ℝ≥0 → Ω → (Fin N → Euc d)} {X : ℝ≥0 → Ω → Config d N}
    (htr : MovTraj D T ρ) (hS : IsStrongSolution P D T X₀ W X) {A : ℕ → Set Ω}
    (hA : ∀ k, MeasurableSet (A k)) (hP : Tendsto (fun k => P (A k)) atTop (𝓝 1))
    (hexp : ∃ l C : ℝ, 0 < l ∧ ∀ r ∈ Set.Icc 0 T,
      ∫⁻ Z : Config d N, ENNReal.ofReal (Real.exp (l * |movT_source D N ρ r Z|))
        ∂(movT_Q (periodicRiesz d D.s) D N ρ r) ≤ ENNReal.ofReal (Real.exp C))
    (hH : ∃ C : ℝ, ∀ k, ∀ r ∈ Set.Icc 0 T,
      relEntropy ((movT_cond P (A k)).map (X r.toNNReal)) (movT_Q (periodicRiesz d D.s) D N ρ r) ≤
        ENNReal.ofReal C) :
    (∀ r ∈ Set.Icc 0 T, Integrable (movT_source D N ρ r) (P.map (X r.toNNReal))) ∧
    IntegrableOn (fun r => ∫ Z, movT_source D N ρ r Z ∂(P.map (X r.toNNReal))) (Set.Icc 0 T) ∧
    ∀ t ∈ Set.Icc 0 T,
      Tendsto (fun k => ∫ r in Set.Icc 0 t, ∫ Z, movT_source D N ρ r Z
        ∂((movT_cond P (A k)).map (X r.toNNReal))) atTop
        (𝓝 (∫ r in Set.Icc 0 t, ∫ Z, movT_source D N ρ r Z ∂(P.map (X r.toNNReal)))) := by
  have : BorelSpace (Torus d) := Pi.borelSpace
  have : BorelSpace (Config d N) := Pi.borelSpace
  have : Inhabited (Config d N) := ⟨fun _ => 0⟩
  have hXm : ∀ t, Measurable (X t) := hS.adapted
  obtain ⟨Xt, hXt, hXtm⟩ := movd_path_modification P X hXm (by
    filter_upwards [hS.cont] with ω h using continuous_pi h)
  obtain ⟨Ψ, hΨm, hΨ⟩ := movd_source_joint_measurable hN htr
  exact movd_limit_cond_abstract (P := P) (T := T) (Z := fun r ω => X r.toNNReal ω) (Zt := Xt)
    (fun r => hXm _) hXt hXtm (Q := fun r => movT_Q (periodicRiesz d D.s) D N ρ r)
    (fun r hr => movd_Q_isProb hN htr hr) (Φ := movT_source D N ρ) hΨm
    (fun r hr => by
      filter_upwards [hS.no_collision] with ω hω
      exact hΨ r hr _ (hω r.toNNReal (by rw [Real.coe_toNNReal _ hr.1]; exact hr.2)))
    (fun r hr => movd_source_aemeasurable hN htr hr) hA hP hexp hH

end HRS

end
