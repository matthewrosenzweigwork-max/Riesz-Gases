/-
HANDOFF STATUS (T25, branch wk/t25).
Compiled, sorry-free, standard axioms only: T25PAux1-21 (checked with tools/wcheck.sh in dependency order).
Changes in the last round: Aux14 `t25p_traceNormForm_le_entries` no longer sums in the operator-norm space (it expands
  `Q x y` as a `tsum` in `ℝ` via `HasSum.prod_fiberwise`); Aux15 gets `{m : ℝ}` in `variable`; Aux17 uses
  `Comp28.continuousOn_V_zero` and rewrites `htr.dyn.s = s`; Aux19 `setLIntegral_congr Ioc_ae_eq_Icc`; Aux20 `t25p_stage2`
  gives `∃ C, 0 ≤ C ∧ ...` (C unused); Aux21 adds `t25p_aemeasurable_path` (a.e.-continuous paths with a.e.-measurable
  sections have an a.e.-measurable path map into `ℝ≥0 → E`; needed because `aemeasurable_pi_iff` needs countable index).
  No helper statement was weakened.
Public lemmas the assembly can use (all in namespace HRS.T25P):
  Aux14 t25p_traceNormForm_le_entries (trace norm <= l1 norm of the matrix entries in a Hilbert basis)
  Aux15 t25p_entry_abs_le, t25p_trace_le_entries
  Aux16 t25p_trace_L1      (E ‖C_N^r - C̄^r‖_{S1} <= C sqrt(B_N/N), uniformly in r in [0,T'] and N >= 2)
  Aux17 t25p_enorm_eq_tsum, t25p_stage1 (mild decomposition at level m, pathwise bound of the remainder by Psi_a)
  Aux18 t25p_Psi_aemeas, t25p_ev_pkg (Cr, cr, one dual evolution Vev, and for every T the Cmax with T25Ev)
  Aux19 t25p_detCov, t25p_covDensT_zero, t25p_trace_int (integrated weighted trace discrepancy <= Ct sqrt(B/N), uniform in a)
  Aux20 t25p_core_gen      (smoothDist-2 and W1/W2 window comparison for flucProc against any Lambda satisfying `hid`)
  Aux21 t25p_aemeasurable_path, t25p_vecBrownian_aemeas, t25p_vecBrownian_cont, t25p_iIndepFun_comp,
        t25p_isParticleSystem_comp (IsParticleSystem pulls back along a measure-preserving map)
DONE (see Aux22-33 and T25PFinal): assembly file(s) Aux22+ (eps-optimal coupling, first enlargement via
  t25p_init_enlargement, hid via t25p_law_ident, constants for smooth/W1/W2, clause 3 via the product argument);
  T25PFinal.lean with the two `_proof` theorems + `example` ties; axiom check; update T25Aux1 plan header.
-/
import HRS.Main.T25PAux20

/-!
# T25P, part 21: pull-back of a particle system along a measure-preserving map
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

namespace HRS.T25P

open HRS HRS.Uniform HRS.GF

variable {d : ℕ}

/-- A process with a.e.-continuous paths and a.e.-measurable time sections has an a.e.-measurable path map into the
product space (the index set `ℝ≥0` is uncountable, so `aemeasurable_pi_iff` does not apply). -/
theorem t25p_aemeasurable_path {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {B : ℝ≥0 → Ω → E} (hm : ∀ t, AEMeasurable (B t) P) (hc : ∀ᵐ ω ∂P, Continuous fun t => B t ω) :
    AEMeasurable (fun ω => fun t => B t ω) P := by
  classical
  have key : ∀ n : ℕ, ∃ Z' : ℝ → Ω → E, (∀ t, Measurable (Z' t)) ∧
      (∀ ω, ContinuousOn (fun t => Z' t ω) (Set.Icc 0 (n : ℝ))) ∧
      ∀ t ∈ Set.Icc (0 : ℝ) n, Z' t =ᵐ[P] fun ω => B t.toNNReal ω := fun n =>
    gf_measurable_modification_proof P (n : ℝ) (fun t ω => B t.toNNReal ω)
      (by
        filter_upwards [hc] with ω hω
        exact (hω.comp continuous_real_toNNReal).continuousOn)
      (fun t _ => hm _)
  choose Z hZm hZc hZae using key
  have hdense : ∀ n : ℕ, ∃ s : Set (Set.Icc (0 : ℝ) n), s.Countable ∧ Dense s := fun n =>
    TopologicalSpace.exists_countable_dense _
  choose s hsc hsd using hdense
  have hae : ∀ᵐ ω ∂P, ∀ n : ℕ, ∀ x ∈ s n, Z n (x : ℝ) ω = B (x : ℝ).toNNReal ω := by
    rw [ae_all_iff]
    intro n
    exact (ae_ball_iff (hsc n)).2 fun x _ => hZae n x x.2
  refine ⟨fun ω t => Z ⌈(t : ℝ)⌉₊ t ω, measurable_pi_iff.2 fun t => hZm _ _, ?_⟩
  filter_upwards [hae, hc] with ω h1 h2
  funext t
  set n := ⌈(t : ℝ)⌉₊ with hn
  have hcf : Continuous fun x : Set.Icc (0 : ℝ) n => Z n x ω := (hZc n ω).restrict
  have hcg : Continuous fun x : Set.Icc (0 : ℝ) n => B (x : ℝ).toNNReal ω :=
    h2.comp (continuous_real_toNNReal.comp continuous_subtype_val)
  have h3 := Continuous.ext_on (hsd n) hcf hcg (fun x hx => h1 n x hx)
  have htn : (t : ℝ) ∈ Set.Icc (0 : ℝ) n := ⟨t.2, Nat.le_ceil _⟩
  have h4 := congrFun h3 ⟨t, htn⟩
  simp only [Real.toNNReal_coe] at h4
  exact h4.symm

/-- The vector map `Fin N → Fin d → ℝ → Fin N → Euc d`. -/
theorem t25p_toEuc_continuous {N : ℕ} :
    Continuous fun f : Fin N → Fin d → ℝ => (fun i => (WithLp.toLp 2 (f i) : Euc d)) :=
  continuous_pi fun i => (PiLp.continuous_toLp 2 (fun _ : Fin d => ℝ)).comp (continuous_apply i)

theorem t25p_vecBrownian_aemeas {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {N : ℕ}
    {W : ℝ≥0 → Ω → (Fin N → Euc d)} (hB : IsVectorBrownian P W) (t : ℝ≥0) :
    AEMeasurable (W t) P := by
  have h1 : AEMeasurable (fun ω => fun i => fun j => W t ω i j) P :=
    aemeasurable_pi_iff.2 fun i => aemeasurable_pi_iff.2 fun j =>
      (hB.1 i j).toIsPreBrownianReal.aemeasurable t
  exact (t25p_toEuc_continuous (d := d)).measurable.comp_aemeasurable h1

theorem t25p_vecBrownian_cont {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {N : ℕ}
    {W : ℝ≥0 → Ω → (Fin N → Euc d)} (hB : IsVectorBrownian P W) :
    ∀ᵐ ω ∂P, Continuous fun t => W t ω := by
  have h1 : ∀ᵐ ω ∂P, ∀ i j, Continuous fun t => W t ω i j := by
    rw [ae_all_iff]; intro i
    rw [ae_all_iff]; intro j
    exact (hB.1 i j).cont
  filter_upwards [h1] with ω hω
  exact (t25p_toEuc_continuous (d := d) (N := N)).comp (continuous_pi fun i => continuous_pi fun j => hω i j)

theorem t25p_iIndepFun_comp {ι Ω Ω' 𝓧 : Type*} [Fintype ι] [MeasurableSpace Ω] [MeasurableSpace Ω']
    [MeasurableSpace 𝓧] {P : Measure Ω} {P' : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    {f : Ω' → Ω} (hf : MeasurePreserving f P' P) {X : ι → Ω → 𝓧} (hX : ∀ i, AEMeasurable (X i) P)
    (h : iIndepFun X P) : iIndepFun (fun i ω' => X i (f ω')) P' := by
  have hXf : ∀ i, AEMeasurable (fun ω' => X i (f ω')) P' := fun i => by
    have : AEMeasurable (X i) (P'.map f) := by rw [hf.map_eq]; exact hX i
    exact this.comp_aemeasurable hf.aemeasurable
  rw [iIndepFun_iff_map_fun_eq_pi_map hXf]
  have h1 := (iIndepFun_iff_map_fun_eq_pi_map hX).1 h
  have hXm : AEMeasurable (fun ω i => X i ω) P := aemeasurable_pi_iff.2 hX
  have e1 : P'.map (fun ω' i => X i (f ω')) = P.map (fun ω i => X i ω) := by
    have : AEMeasurable (fun ω i => X i ω) (P'.map f) := by rw [hf.map_eq]; exact hXm
    rw [← hf.map_eq]
    exact (AEMeasurable.map_map_of_aemeasurable this hf.aemeasurable).symm
  have e2 : ∀ i, P'.map (fun ω' => X i (f ω')) = P.map (X i) := fun i => by
    have : AEMeasurable (X i) (P'.map f) := by rw [hf.map_eq]; exact hX i
    rw [← hf.map_eq]
    exact (AEMeasurable.map_map_of_aemeasurable this hf.aemeasurable).symm
  rw [e1, h1]
  simp_rw [e2]

theorem t25p_isParticleSystem_comp {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] {N : ℕ}
    {P : Measure Ω} {P' : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure P'] {π : Ω' → Ω}
    (hπ : MeasurePreserving π P' P) {D : DynData d} {T : ℝ} {X₀ : Ω → Config d N}
    {W : ℝ≥0 → Ω → (Fin N → Euc d)} {X : ℝ≥0 → Ω → Config d N} (h : IsParticleSystem P D T X₀ W X) :
    IsParticleSystem P' D T (fun ω' => X₀ (π ω')) (fun t ω' => W t (π ω')) (fun t ω' => X t (π ω')) := by
  have hWc : ∀ i j, AEMeasurable (fun ω => (fun t : ℝ≥0 => W t ω i j)) P := fun i j =>
    t25p_aemeasurable_path (fun t => (h.brownian.1 i j).toIsPreBrownianReal.aemeasurable t)
      (h.brownian.1 i j).cont
  refine ⟨⟨fun i j => ?_, ?_⟩, ?_, isStrongSolution_comp hπ h.sol⟩
  · have hB := h.brownian.1 i j
    exact ⟨⟨fun I => (hB.hasLaw I).comp hπ.hasLaw⟩, hπ.quasiMeasurePreserving.ae hB.cont⟩
  · exact t25p_iIndepFun_comp hπ (fun ij : Fin N × Fin d => hWc ij.1 ij.2) h.brownian.2
  · -- independence of the initial configuration and the noise
    have hX₀ : AEMeasurable X₀ P := (h.sol.adapted 0).aemeasurable.congr h.sol.init
    have hWp : AEMeasurable (fun ω => fun t : ℝ≥0 => W t ω) P :=
      t25p_aemeasurable_path (fun t => t25p_vecBrownian_aemeas h.brownian t)
        (t25p_vecBrownian_cont h.brownian)
    have hpair : AEMeasurable (fun ω => (X₀ ω, fun t : ℝ≥0 => W t ω)) P := hX₀.prodMk hWp
    have h1 := (indepFun_iff_map_prod_eq_prod_map_map hX₀ hWp).1 h.indep
    have hf1 : AEMeasurable (fun ω' => X₀ (π ω')) P' := by
      have : AEMeasurable X₀ (P'.map π) := by rw [hπ.map_eq]; exact hX₀
      exact this.comp_aemeasurable hπ.aemeasurable
    have hf2 : AEMeasurable (fun ω' => fun t : ℝ≥0 => W t (π ω')) P' := by
      have : AEMeasurable (fun ω => fun t : ℝ≥0 => W t ω) (P'.map π) := by rw [hπ.map_eq]; exact hWp
      exact this.comp_aemeasurable hπ.aemeasurable
    refine (indepFun_iff_map_prod_eq_prod_map_map hf1 hf2).2 ?_
    have e1 : P'.map (fun ω' => (X₀ (π ω'), fun t : ℝ≥0 => W t (π ω'))) =
        P.map (fun ω => (X₀ ω, fun t : ℝ≥0 => W t ω)) := by
      have : AEMeasurable (fun ω => (X₀ ω, fun t : ℝ≥0 => W t ω)) (P'.map π) := by
        rw [hπ.map_eq]; exact hpair
      rw [← hπ.map_eq]
      exact (AEMeasurable.map_map_of_aemeasurable this hπ.aemeasurable).symm
    have e2 : P'.map (fun ω' => X₀ (π ω')) = P.map X₀ := by
      have : AEMeasurable X₀ (P'.map π) := by rw [hπ.map_eq]; exact hX₀
      rw [← hπ.map_eq]
      exact (AEMeasurable.map_map_of_aemeasurable this hπ.aemeasurable).symm
    have e3 : P'.map (fun ω' => fun t : ℝ≥0 => W t (π ω')) = P.map (fun ω => fun t : ℝ≥0 => W t ω) := by
      have : AEMeasurable (fun ω => fun t : ℝ≥0 => W t ω) (P'.map π) := by rw [hπ.map_eq]; exact hWp
      rw [← hπ.map_eq]
      exact (AEMeasurable.map_map_of_aemeasurable this hπ.aemeasurable).symm
    rw [e1, e2, e3]
    exact h1

end HRS.T25P
