import HRS.Main.GFEVAux16

/-!
# Packet GFEVM, part 1: algebra of the classical adjoint propagator

Uniqueness of classical adjoint solutions (the first conjunct of `AdjointInput`) gives the cocycle identity, the
identity `U^{t,t} = 1`, linearity of `propagator` and `propagator (const) = const`.  Generic in `(D, ρ, T)`.
-/

noncomputable section

open MeasureTheory Filter Topology Finset
open scoped ENNReal NNReal BigOperators ComplexConjugate

namespace HRS.GF

open HRS HRS.PDE HRS.PDE.ET HRS.Uniform HRS.Uniform.Q54 HRS.Uniform.Q48b

variable {d : ℕ}

/-- Uniqueness of classical adjoint solutions on `[0,T]` (first conjunct of `AdjointInput`). -/
def GfmUniq (D : DynData d) (ρ : ℝ → Torus d → ℝ) (T : ℝ) : Prop :=
  ∀ t : ℝ, 0 ≤ t → t ≤ T → ∀ (φ : Torus d → ℝ) (f g : ℝ → Torus d → ℝ),
    IsClassicalAdjointSolution D ρ t φ f → IsClassicalAdjointSolution D ρ t φ g →
      ∀ r ∈ Set.Icc (0 : ℝ) t, f r = g r

/-- The function class `C² ∩ H^m`. -/
def gfmCls (m : ℝ) (φ : Torus d → ℝ) : Prop := Torus.IsCk 2 φ ∧ MemSobolev m φ

theorem gfm_prop_eq {D : DynData d} {ρ : ℝ → Torus d → ℝ} {T : ℝ} (hU : GfmUniq D ρ T) {t : ℝ}
    {φ : Torus d → ℝ} {f : ℝ → Torus d → ℝ} (ht0 : 0 ≤ t) (htT : t ≤ T)
    (hf : IsClassicalAdjointSolution D ρ t φ f) {r : ℝ} (hr : r ∈ Set.Icc (0 : ℝ) t) :
    propagator D ρ r t φ = f r := by
  classical
  have h : ∃ f, IsClassicalAdjointSolution D ρ t φ f := ⟨f, hf⟩
  unfold propagator
  rw [dif_pos h]
  exact hU t ht0 htT φ _ f h.choose_spec hf r hr

theorem gfm_restrict {D : DynData d} {ρ : ℝ → Torus d → ℝ} {t : ℝ} {φ : Torus d → ℝ}
    {f : ℝ → Torus d → ℝ} (hf : IsClassicalAdjointSolution D ρ t φ f) {r : ℝ}
    (hr : r ∈ Set.Icc (0 : ℝ) t) : IsClassicalAdjointSolution D ρ r (f r) f := by
  have hsub : ∀ s : Set.Icc (0 : ℝ) r, s.1 ∈ Set.Icc (0 : ℝ) t := fun s => ⟨s.2.1, s.2.2.trans hr.2⟩
  have hι : Continuous (fun s : Set.Icc (0 : ℝ) r => (⟨s.1, hsub s⟩ : Set.Icc (0 : ℝ) t)) :=
    Continuous.subtype_mk continuous_subtype_val _
  refine ⟨fun s hs => hf.c2 s ⟨hs.1, hs.2.trans hr.2⟩, fun j hj => ?_, rfl,
    fun x s hs => hf.time_deriv x s ⟨hs.1, hs.2.trans_le hr.2⟩, ?_⟩
  · have hc := (hf.cont_c2 j hj).comp (hι.prodMap (continuous_id : Continuous (id : Euc d → Euc d)))
    exact hc
  · have hc := hf.cont_time_deriv.comp (hι.prodMap (continuous_id : Continuous (id : Torus d → Torus d)))
    exact hc

/-- The solution is a solution at every intermediate terminal time, so the cocycle identity holds. -/
theorem gfm_cocycle {D : DynData d} {ρ : ℝ → Torus d → ℝ} {T : ℝ} (hU : GfmUniq D ρ T) {t : ℝ}
    {φ : Torus d → ℝ} {f : ℝ → Torus d → ℝ} (ht0 : 0 ≤ t) (htT : t ≤ T)
    (hf : IsClassicalAdjointSolution D ρ t φ f) {s r : ℝ} (hs : 0 ≤ s) (hsr : s ≤ r) (hrt : r ≤ t) :
    propagator D ρ s r (propagator D ρ r t φ) = propagator D ρ s t φ := by
  have hr0 : 0 ≤ r := hs.trans hsr
  rw [gfm_prop_eq hU ht0 htT hf ⟨hr0, hrt⟩]
  have hres := gfm_restrict hf (⟨hr0, hrt⟩ : r ∈ Set.Icc (0 : ℝ) t)
  rw [gfm_prop_eq hU hr0 (hrt.trans htT) hres ⟨hs, hsr⟩, gfm_prop_eq hU ht0 htT hf ⟨hs, hsr.trans hrt⟩]

theorem gfm_prop_self {D : DynData d} {ρ : ℝ → Torus d → ℝ} {T : ℝ} (hU : GfmUniq D ρ T) {t : ℝ}
    {φ : Torus d → ℝ} {f : ℝ → Torus d → ℝ} (ht0 : 0 ≤ t) (htT : t ≤ T)
    (hf : IsClassicalAdjointSolution D ρ t φ f) : propagator D ρ t t φ = φ := by
  rw [gfm_prop_eq hU ht0 htT hf ⟨ht0, le_rfl⟩, hf.terminal]

theorem gfm_sol_lin {D : DynData d} {ρ : ℝ → Torus d → ℝ} {t : ℝ} {φ ψ : Torus d → ℝ}
    {f g : ℝ → Torus d → ℝ} (α β : ℝ) (hf : IsClassicalAdjointSolution D ρ t φ f)
    (hg : IsClassicalAdjointSolution D ρ t ψ g)
    (hlin : ∀ r ∈ Set.Icc (0 : ℝ) t,
      backwardGenerator D (ρ r) (fun x => α * f r x + β * g r x) =
        fun x => α * backwardGenerator D (ρ r) (f r) x + β * backwardGenerator D (ρ r) (g r) x) :
    IsClassicalAdjointSolution D ρ t (fun x => α * φ x + β * ψ x) (fun r x => α * f r x + β * g r x) := by
  refine ⟨fun r hr => ?_, fun j hj => ?_, ?_, fun x r hr => ?_, ?_⟩
  · have h1 := hf.c2 r hr
    have h2 := hg.c2 r hr
    unfold Torus.IsCk at h1 h2 ⊢
    show ContDiff ℝ 2 (fun y => α * Torus.lift (f r) y + β * Torus.lift (g r) y)
    exact (contDiff_const.mul h1).add (contDiff_const.mul h2)
  · have key : ∀ (p : Set.Icc (0 : ℝ) t × Euc d),
        iteratedFDeriv ℝ j (Torus.lift (fun x => α * f p.1 x + β * g p.1 x)) p.2 =
          α • iteratedFDeriv ℝ j (Torus.lift (f p.1)) p.2 + β • iteratedFDeriv ℝ j (Torus.lift (g p.1)) p.2 := by
      intro p
      have h1 : ContDiff ℝ j (Torus.lift (f p.1)) := (hf.c2 p.1 p.1.2).of_le (by exact_mod_cast hj)
      have h2 : ContDiff ℝ j (Torus.lift (g p.1)) := (hg.c2 p.1 p.1.2).of_le (by exact_mod_cast hj)
      have e : Torus.lift (fun x => α * f p.1 x + β * g p.1 x) =
          (fun y => α • Torus.lift (f p.1) y) + (fun y => β • Torus.lift (g p.1) y) := by
        funext y; simp [Torus.lift, smul_eq_mul]
      rw [e, iteratedFDeriv_add_apply (h1.const_smul α).contDiffAt (h2.const_smul β).contDiffAt,
        iteratedFDeriv_const_smul_apply' h1.contDiffAt, iteratedFDeriv_const_smul_apply' h2.contDiffAt]
    refine Continuous.congr (((hf.cont_c2 j hj).const_smul α).add ((hg.cont_c2 j hj).const_smul β))
      (fun p => (key p).symm)
  · show (fun x => α * f t x + β * g t x) = fun x => α * φ x + β * ψ x
    rw [hf.terminal, hg.terminal]
  · have h := ((hf.time_deriv x r hr).const_mul α).add ((hg.time_deriv x r hr).const_mul β)
    have hr' : r ∈ Set.Icc (0 : ℝ) t := Set.Ioo_subset_Icc_self hr
    have e : backwardGenerator D (ρ r) (fun x => α * f r x + β * g r x) x =
        α * backwardGenerator D (ρ r) (f r) x + β * backwardGenerator D (ρ r) (g r) x :=
      congrFun (hlin r hr') x
    show HasDerivAt (fun r' => α * f r' x + β * g r' x)
      (-(backwardGenerator D (ρ r) (fun x => α * f r x + β * g r x) x)) r
    rw [e]
    convert h using 1
    ring
  · have hc : Continuous (fun p : Set.Icc (0 : ℝ) t × Torus d =>
        α * backwardGenerator D (ρ p.1) (f p.1) p.2 + β * backwardGenerator D (ρ p.1) (g p.1) p.2) :=
      (continuous_const.mul hf.cont_time_deriv).add (continuous_const.mul hg.cont_time_deriv)
    refine hc.congr (fun p => ?_)
    exact (congrFun (hlin p.1 p.1.2) p.2).symm

theorem gfm_sol_const {D : DynData d} {ρ : ℝ → Torus d → ℝ} {t : ℝ} (c : ℝ)
    (hbc : ∀ r ∈ Set.Icc (0 : ℝ) t, backwardGenerator D (ρ r) (fun _ => c) = fun _ => 0) :
    IsClassicalAdjointSolution D ρ t (fun _ => c) (fun _ _ => c) := by
  refine ⟨fun r hr => ?_, fun j hj => ?_, rfl, fun x r hr => ?_, ?_⟩
  · unfold Torus.IsCk
    exact contDiff_const
  · have hcd : ContDiff ℝ 2 (Torus.lift (fun _ : Torus d => c)) := contDiff_const
    exact (hcd.continuous_iteratedFDeriv (by exact_mod_cast hj)).comp continuous_snd
  · have hr' : r ∈ Set.Icc (0 : ℝ) t := Set.Ioo_subset_Icc_self hr
    show HasDerivAt (fun _ : ℝ => c) (-(backwardGenerator D (ρ r) (fun _ => c) x)) r
    rw [congrFun (hbc r hr') x]
    simpa using hasDerivAt_const r c
  · refine (continuous_const : Continuous (fun _ : Set.Icc (0 : ℝ) t × Torus d => (0 : ℝ))).congr (fun p => ?_)
    exact (congrFun (hbc p.1 p.1.2) p.2).symm

theorem gfm_sol_mem1 {D : DynData d} {ρ : ℝ → Torus d → ℝ} {t : ℝ} {φ : Torus d → ℝ}
    {f : ℝ → Torus d → ℝ} (hf : IsClassicalAdjointSolution D ρ t φ f) {r : ℝ}
    (hr : r ∈ Set.Icc (0 : ℝ) t) : MemSobolev 1 (f r) :=
  memSobolev_of_memHs 1 (f r) (ClassicalAux.memLp_two_of_continuous (ClassicalAux.continuous_f_apply hf hr))
    ((ClassicalAux.hs2_f hf hr).1.mono (by norm_num))

theorem gfm_prop_lin {D : DynData d} {ρ : ℝ → Torus d → ℝ} {T : ℝ} (hU : GfmUniq D ρ T)
    (hbl : ∀ r ∈ Set.Icc (0 : ℝ) T, ∀ u v : Torus d → ℝ, Torus.IsCk 2 u → Torus.IsCk 2 v →
      MemSobolev 1 u → MemSobolev 1 v → ∀ α β : ℝ,
      backwardGenerator D (ρ r) (fun x => α * u x + β * v x) =
        fun x => α * backwardGenerator D (ρ r) u x + β * backwardGenerator D (ρ r) v x)
    {t : ℝ} {φ ψ : Torus d → ℝ} {f g : ℝ → Torus d → ℝ} (ht0 : 0 ≤ t) (htT : t ≤ T)
    (hf : IsClassicalAdjointSolution D ρ t φ f) (hg : IsClassicalAdjointSolution D ρ t ψ g) (α β : ℝ)
    {r : ℝ} (hr : r ∈ Set.Icc (0 : ℝ) t) :
    propagator D ρ r t (fun x => α * φ x + β * ψ x) =
      fun x => α * propagator D ρ r t φ x + β * propagator D ρ r t ψ x := by
  have hsol := gfm_sol_lin α β hf hg (fun r' hr' =>
    hbl r' ⟨hr'.1, hr'.2.trans htT⟩ (f r') (g r') (hf.c2 r' hr') (hg.c2 r' hr')
      (gfm_sol_mem1 hf hr') (gfm_sol_mem1 hg hr') α β)
  rw [gfm_prop_eq hU ht0 htT hsol hr, gfm_prop_eq hU ht0 htT hf hr, gfm_prop_eq hU ht0 htT hg hr]

theorem gfm_prop_const {D : DynData d} {ρ : ℝ → Torus d → ℝ} {T : ℝ} (hU : GfmUniq D ρ T)
    (hbc : ∀ r ∈ Set.Icc (0 : ℝ) T, ∀ c : ℝ, backwardGenerator D (ρ r) (fun _ => c) = fun _ => 0)
    {t : ℝ} (ht0 : 0 ≤ t) (htT : t ≤ T) (c : ℝ) {r : ℝ} (hr : r ∈ Set.Icc (0 : ℝ) t) :
    propagator D ρ r t (fun _ => c) = fun _ => c := by
  have hsol := gfm_sol_const (D := D) (ρ := ρ) (t := t) c
    (fun r' hr' => hbc r' ⟨hr'.1, hr'.2.trans htT⟩ c)
  rw [gfm_prop_eq hU ht0 htT hsol hr]

end HRS.GF
