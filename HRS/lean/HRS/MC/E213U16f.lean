import HRS.MC.E213U16e

/-!
# Packet e213u16, file f: Gaussian process of past and future coordinates, and their independence

* `IsSC`: finite combinations of continuous linear functionals of time slices of `η`; closed under linear combinations,
  centred Gaussian, in `L²`;
* `Xs τ`, `Ys τ H`: the past coordinates `η^s(ψ)` (`s ≤ τ`) and the future coordinates `η^t(ψ) - η^τ(U^{τ,t}ψ)` (`t > τ`);
* `u16_indep`: `future_independence`: the past and the future coordinates are independent processes.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace HRS.MC.E213U16

open HRS HRS.Sec7 HRS.Main HRS.Uniform HRS.MC.E213O HRS.MC.E213T HRS.MC.E213Q HRS.MC.E213U13 HRS.MC.E213Plan

variable {d : ℕ}

section SC

variable {S : PreparedData d} {β₀ m : ℝ} {hE : EdgeworthHyp S β₀ m} (gd : GaussData S β₀ hE)

/-- `W` is a finite combination of continuous linear functionals of time slices of `η` at times in `[0,H]`. -/
def IsSC (H : ℝ) (W : gd.Ω₀ → ℝ) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (t : ι → ℝ) (L : ι → StrongDual ℝ (NegSobolev d (rLvl d))),
    (∀ i, t i ∈ Set.Icc (0 : ℝ) H) ∧ ∀ ω, W ω = ∑ i, L i (gd.η (t i) ω)

variable {gd}

theorem IsSC.zero (H : ℝ) : IsSC gd H (fun _ => 0) :=
  ⟨Empty, inferInstance, fun e => e.elim, fun e => e.elim, fun e => e.elim, fun ω => by simp⟩

theorem IsSC.add {H : ℝ} {W₁ W₂ : gd.Ω₀ → ℝ} (h₁ : IsSC gd H W₁) (h₂ : IsSC gd H W₂) :
    IsSC gd H (fun ω => W₁ ω + W₂ ω) := by
  obtain ⟨ι₁, i₁, t₁, L₁, ht₁, e₁⟩ := h₁
  obtain ⟨ι₂, i₂, t₂, L₂, ht₂, e₂⟩ := h₂
  refine ⟨ι₁ ⊕ ι₂, inferInstance, Sum.elim t₁ t₂, Sum.elim L₁ L₂, ?_, fun ω => ?_⟩
  · intro i
    cases i with
    | inl i => exact ht₁ i
    | inr i => exact ht₂ i
  · simp only [Fintype.sum_sum_type, e₁, e₂]
    rfl

theorem IsSC.smul {H : ℝ} {W : gd.Ω₀ → ℝ} (c : ℝ) (h : IsSC gd H W) : IsSC gd H (fun ω => c * W ω) := by
  obtain ⟨ι, i, t, L, ht, e⟩ := h
  refine ⟨ι, i, t, fun j => c • L j, ht, fun ω => ?_⟩
  simp only [e, Finset.mul_sum]
  rfl

theorem IsSC.congr {H : ℝ} {W W' : gd.Ω₀ → ℝ} (h : IsSC gd H W) (e : ∀ ω, W ω = W' ω) : IsSC gd H W' := by
  obtain ⟨ι, i, t, L, ht, e'⟩ := h
  exact ⟨ι, i, t, L, ht, fun ω => (e ω).symm.trans (e' ω)⟩

theorem IsSC.sub {H : ℝ} {W₁ W₂ : gd.Ω₀ → ℝ} (h₁ : IsSC gd H W₁) (h₂ : IsSC gd H W₂) :
    IsSC gd H (fun ω => W₁ ω - W₂ ω) :=
  (h₁.add (h₂.smul (-1))).congr fun ω => by ring

theorem IsSC.sum {α : Type*} {H : ℝ} (I : Finset α) {W : α → gd.Ω₀ → ℝ} (h : ∀ i ∈ I, IsSC gd H (W i)) :
    IsSC gd H (fun ω => ∑ i ∈ I, W i ω) := by
  classical
  induction I using Finset.induction_on with
  | empty => simpa using IsSC.zero (gd := gd) H
  | insert a I ha ih =>
    have h1 := h a (Finset.mem_insert_self _ _)
    have h2 := ih fun i hi => h i (Finset.mem_insert_of_mem hi)
    refine (h1.add h2).congr fun ω => ?_
    rw [Finset.sum_insert ha]

theorem IsSC.measurable {H : ℝ} {W : gd.Ω₀ → ℝ} (h : IsSC gd H W) : Measurable W := by
  obtain ⟨ι, i, t, L, ht, e⟩ := h
  have : W = fun ω => ∑ i, L i (gd.η (t i) ω) := funext e
  rw [this]
  exact Finset.measurable_sum _ fun i _ => (L i).continuous.measurable.comp (u16_eta_meas gd (t i))

theorem IsSC.gaussian {H : ℝ} {W : gd.Ω₀ → ℝ} (h : IsSC gd H W) :
    ∃ v : ℝ≥0, gd.P₀.map W = gaussianReal 0 v := by
  obtain ⟨ι, i, t, L, ht, e⟩ := h
  have : W = fun ω => ∑ i, L i (gd.η (t i) ω) := funext e
  rw [this]
  exact u16_slice_gauss gd H t ht L

theorem IsSC.memLp_mean {H : ℝ} {W : gd.Ω₀ → ℝ} (h : IsSC gd H W) :
    MemLp W 2 gd.P₀ ∧ ∫ ω, W ω ∂gd.P₀ = 0 := by
  obtain ⟨v, hv⟩ := h.gaussian
  have hm : AEMeasurable W gd.P₀ := h.measurable.aemeasurable
  refine ⟨?_, ?_⟩
  · have : MemLp id 2 (gd.P₀.map W) := by rw [hv]; exact memLp_id_gaussianReal 2
    exact (memLp_map_measure_iff aestronglyMeasurable_id hm).1 this
  · have := integral_map (μ := gd.P₀) (φ := W) (f := fun x : ℝ => x) hm aestronglyMeasurable_id
    rw [hv, integral_id_gaussianReal] at this
    exact this.symm

theorem u16_isSC_pair {H s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) H) {ψ : Torus d → ℝ} (hψ : Torus.IsSmooth ψ) :
    IsSC gd H (fun ω => NegSobolev.eval (gd.η s ω) ψ) :=
  ⟨Unit, inferInstance, fun _ => s, fun _ => u16_ev (rLvl d) hψ, fun _ => hs, fun ω => by
    simp [u16_ev_apply]⟩

end SC

section Proc

variable {S : PreparedData d} {β₀ m : ℝ} {hE : EdgeworthHyp S β₀ m} (gd : GaussData S β₀ hE)

theorem u16_isSC_Nrv {H t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) H) {φ : Torus d → ℝ} (hφ : Torus.IsSmooth φ) :
    IsSC gd H (Nrv gd t φ) :=
  (u16_isSC_pair ht hφ).sub (u16_isSC_pair ⟨le_rfl, ht.1.trans ht.2⟩ (u16_prop_smooth hE hφ le_rfl ht.1))

theorem u16_N_pair {H : ℝ} (hH : 0 < H) {t₁ t₂ : ℝ} (h₁ : t₁ ∈ Set.Icc (0 : ℝ) H) (h₂ : t₂ ∈ Set.Icc (0 : ℝ) H)
    {φ₁ φ₂ : Torus d → ℝ} (hφ₁ : Torus.IsSmooth φ₁) (hφ₂ : Torus.IsSmooth φ₂) :
    Integrable (fun ω => Nrv gd t₁ φ₁ ω * Nrv gd t₂ φ₂ ω) gd.P₀ ∧
    ∫ ω, Nrv gd t₁ φ₁ ω * Nrv gd t₂ φ₂ ω ∂gd.P₀ = covK S.dyn S.ρ t₁ t₂ φ₁ φ₂ := by
  refine ⟨((u16_isSC_Nrv gd h₁ hφ₁).memLp_mean.1).integrable_mul ((u16_isSC_Nrv gd h₂ hφ₂).memLp_mean.1), ?_⟩
  have := (u16_N_cov gd hE H hH (p := 2) ![t₁, t₂] ![φ₁, φ₂] (by intro a; fin_cases a <;> simpa) 
    (by intro a; fin_cases a <;> simpa) 0 1).2
  simpa using this

/-- Smooth test functions. -/
abbrev SmoothFn (d : ℕ) := {ψ : Torus d → ℝ // Torus.IsSmooth ψ}

/-- The past coordinates `η^s(ψ)`, `0 ≤ s ≤ τ`. -/
def Xs (τ : ℝ) : (Set.Icc (0 : ℝ) τ × SmoothFn d) → gd.Ω₀ → ℝ :=
  fun p ω => NegSobolev.eval (gd.η p.1.1 ω) p.2.1

/-- The future coordinates `η^t(ψ) - η^τ(U^{τ,t}ψ)`, `τ < t ≤ H`. -/
def Ys (τ H : ℝ) : (Set.Ioc τ H × SmoothFn d) → gd.Ω₀ → ℝ :=
  fun p ω => NegSobolev.eval (gd.η p.1.1 ω) p.2.1 -
    NegSobolev.eval (gd.η τ ω) (propagator S.dyn S.ρ τ p.1.1 p.2.1)

theorem u16_Xs_eq (τ : ℝ) (p : Set.Icc (0 : ℝ) τ × SmoothFn d) (ω : gd.Ω₀) :
    Xs gd τ p ω = Nrv gd p.1.1 p.2.1 ω + NegSobolev.eval (gd.η 0 ω) (propagator S.dyn S.ρ 0 p.1.1 p.2.1) := by
  simp [Xs, Nrv]

theorem u16_Ys_eq {τ H : ℝ} (hτ : 0 ≤ τ) (p : Set.Ioc τ H × SmoothFn d) (ω : gd.Ω₀) :
    Ys gd τ H p ω = Nrv gd p.1.1 p.2.1 ω - Nrv gd τ (propagator S.dyn S.ρ τ p.1.1 p.2.1) ω := by
  have hc := u16_cocycle (HRS.MC.E213A.regimeOfPrepared S β₀ hE) p.2.2 (le_refl (0 : ℝ)) hτ p.1.2.1
  have hc' : propagator S.dyn S.ρ 0 p.1.1 p.2.1 =
      propagator S.dyn S.ρ 0 τ (propagator S.dyn S.ρ τ p.1.1 p.2.1) := hc
  simp only [Ys, Nrv, hc']
  ring

end Proc

theorem u16_covK_cocycle {S : PreparedData d} {β₀ m : ℝ} (hE : EdgeworthHyp S β₀ m) {s τ t : ℝ} (hs0 : 0 ≤ s)
    (hsτ : s ≤ τ) (hτt : τ < t) {ψ₁ ψ₂ : Torus d → ℝ} (hψ₂ : Torus.IsSmooth ψ₂) :
    covK S.dyn S.ρ s t ψ₁ ψ₂ = covK S.dyn S.ρ s τ ψ₁ (propagator S.dyn S.ρ τ t ψ₂) := by
  unfold covK
  have h1 : min s t = s := min_eq_left (hsτ.trans hτt.le)
  have h2 : min s τ = s := min_eq_left hsτ
  rw [h1, h2]
  congr 1
  refine setIntegral_congr_fun measurableSet_Icc fun r hr => ?_
  have hc := u16_cocycle (HRS.MC.E213A.regimeOfPrepared S β₀ hE) hψ₂ hr.1 (hr.2.trans hsτ) hτt
  have hc' : propagator S.dyn S.ρ r t ψ₂ = propagator S.dyn S.ρ r τ (propagator S.dyn S.ρ τ t ψ₂) := hc
  simp only [hc']


section Indep

variable {S : PreparedData d} {β₀ m : ℝ} {hE : EdgeworthHyp S β₀ m} (gd : GaussData S β₀ hE)

theorem u16_isSC_Xs {H τ : ℝ} (hτ : τ ∈ Set.Icc (0 : ℝ) H) (p : Set.Icc (0 : ℝ) τ × SmoothFn d) :
    IsSC gd H (Xs gd τ p) :=
  u16_isSC_pair ⟨p.1.2.1, p.1.2.2.trans hτ.2⟩ p.2.2

theorem u16_isSC_Ys {H τ : ℝ} (hτ : τ ∈ Set.Icc (0 : ℝ) H) (p : Set.Ioc τ H × SmoothFn d) :
    IsSC gd H (Ys gd τ H p) := by
  refine (u16_isSC_pair ⟨hτ.1.trans p.1.2.1.le, p.1.2.2⟩ p.2.2).sub
    (u16_isSC_pair hτ (u16_prop_smooth hE p.2.2 hτ.1 p.1.2.1.le))

theorem u16_gp {H τ : ℝ} (hτ : τ ∈ Set.Icc (0 : ℝ) H) :
    IsGaussianProcess (Sum.elim (Xs gd τ) (Ys gd τ H)) gd.P₀ := by
  have hSC : ∀ i, IsSC gd H (Sum.elim (Xs gd τ) (Ys gd τ H) i) := by
    intro i
    cases i with
    | inl p => exact u16_isSC_Xs gd hτ p
    | inr p => exact u16_isSC_Ys gd hτ p
  refine isGaussianProcess_of_combos _ (fun i => (hSC i).measurable) ?_
  intro I c
  exact IsSC.gaussian (IsSC.sum (Finset.univ : Finset I) (fun i _ => (hSC i).smul (c i)))

theorem u16_cov_zero {H τ : ℝ} (hH : 0 < H) (hτ : τ ∈ Set.Icc (0 : ℝ) H) (p : Set.Icc (0 : ℝ) τ × SmoothFn d)
    (q : Set.Ioc τ H × SmoothFn d) :
    cov[Xs gd τ p, Ys gd τ H q; gd.P₀] = 0 := by
  set s := p.1.1 with hs
  set t := q.1.1 with ht
  have hs0 : 0 ≤ s := p.1.2.1
  have hsτ : s ≤ τ := p.1.2.2
  have hτt : τ < t := q.1.2.1
  have htH : t ≤ H := q.1.2.2
  have hsH : s ∈ Set.Icc (0 : ℝ) H := ⟨hs0, hsτ.trans hτ.2⟩
  have htH' : t ∈ Set.Icc (0 : ℝ) H := ⟨hτ.1.trans hτt.le, htH⟩
  set ψ₁ := p.2.1 with hψ₁
  set ψ₂ := q.2.1 with hψ₂
  have hψ₁s : Torus.IsSmooth ψ₁ := p.2.2
  have hψ₂s : Torus.IsSmooth ψ₂ := q.2.2
  set ψ₃ := propagator S.dyn S.ρ τ t ψ₂ with hψ₃
  have hψ₃s : Torus.IsSmooth ψ₃ := u16_prop_smooth hE hψ₂s hτ.1 hτt.le
  set ψ₀ := propagator S.dyn S.ρ 0 s ψ₁ with hψ₀
  have hψ₀s : Torus.IsSmooth ψ₀ := u16_prop_smooth hE hψ₁s le_rfl hs0
  have hXm := (u16_isSC_Xs gd hτ p).memLp_mean
  have hYm := (u16_isSC_Ys gd hτ q).memLp_mean
  rw [covariance_eq_sub hXm.1 hYm.1]
  have hmean : gd.P₀[Xs gd τ p] * gd.P₀[Ys gd τ H q] = 0 := by
    have := hXm.2; simp only [this, zero_mul]
  rw [hmean, sub_zero]
  -- the decomposition
  set N₁ := Nrv gd s ψ₁ with hN₁
  set N₂ := Nrv gd t ψ₂ with hN₂
  set N₃ := Nrv gd τ ψ₃ with hN₃
  set A : gd.Ω₀ → ℝ := fun ω => NegSobolev.eval (gd.η 0 ω) ψ₀ with hA
  have hX : ∀ ω, Xs gd τ p ω = N₁ ω + A ω := fun ω => u16_Xs_eq gd τ p ω
  have hY : ∀ ω, Ys gd τ H q ω = N₂ ω - N₃ ω := fun ω => u16_Ys_eq gd hτ.1 q ω
  have h0H : (0 : ℝ) ∈ Set.Icc (0 : ℝ) H := ⟨le_rfl, hH.le⟩
  have hSN₁ := u16_isSC_Nrv gd hsH hψ₁s
  have hSN₂ := u16_isSC_Nrv gd htH' hψ₂s
  have hSN₃ := u16_isSC_Nrv gd hτ hψ₃s
  have hSA : IsSC gd H A := u16_isSC_pair h0H hψ₀s
  have hSB : IsSC gd H (fun ω => N₂ ω - N₃ ω) := hSN₂.sub hSN₃
  have i12 : Integrable (fun ω => N₁ ω * N₂ ω) gd.P₀ ∧
      ∫ ω, N₁ ω * N₂ ω ∂gd.P₀ = covK S.dyn S.ρ s t ψ₁ ψ₂ := u16_N_pair gd hH hsH htH' hψ₁s hψ₂s
  have i13 : Integrable (fun ω => N₁ ω * N₃ ω) gd.P₀ ∧
      ∫ ω, N₁ ω * N₃ ω ∂gd.P₀ = covK S.dyn S.ρ s τ ψ₁ ψ₃ := u16_N_pair gd hH hsH hτ hψ₁s hψ₃s
  have iAB : Integrable (fun ω => A ω * (N₂ ω - N₃ ω)) gd.P₀ :=
    hSA.memLp_mean.1.integrable_mul hSB.memLp_mean.1
  have hexp : ∀ ω, Xs gd τ p ω * Ys gd τ H q ω = N₁ ω * N₂ ω - N₁ ω * N₃ ω + A ω * (N₂ ω - N₃ ω) := by
    intro ω; rw [hX, hY]; ring
  have e1 : ∫ ω, (Xs gd τ p * Ys gd τ H q) ω ∂gd.P₀ =
      (∫ ω, N₁ ω * N₂ ω ∂gd.P₀) - (∫ ω, N₁ ω * N₃ ω ∂gd.P₀) + ∫ ω, A ω * (N₂ ω - N₃ ω) ∂gd.P₀ := by
    simp only [Pi.mul_apply, hexp]
    have iS : Integrable (fun ω => N₁ ω * N₂ ω - N₁ ω * N₃ ω) gd.P₀ := i12.1.sub i13.1
    rw [integral_add iS iAB, integral_sub i12.1 i13.1]
  rw [e1]
  -- independence
  have hind : ∫ ω, A ω * (N₂ ω - N₃ ω) ∂gd.P₀ = 0 := by
    obtain ⟨hI, -⟩ := u16_gauss_part gd H hH.le ![t, τ] ![ψ₂, ψ₃] (by intro a; fin_cases a <;> simpa)
      (by intro a; fin_cases a <;> simpa)
    have hA' : IndepFun (fun ω => (WithLp.toLp 2 fun a => Nrv gd (![t, τ] a) (![ψ₂, ψ₃] a) ω :
        EuclideanSpace ℝ (Fin 2))) (gd.η 0) gd.P₀ := hI
    have hg : Measurable (fun x : EuclideanSpace ℝ (Fin 2) => x 0 - x 1) := by fun_prop
    have ha : Measurable (fun F : NegSobolev d (rLvl d) => NegSobolev.eval F ψ₀) := by
      have e : (fun F : NegSobolev d (rLvl d) => NegSobolev.eval F ψ₀) = ⇑(u16_ev (rLvl d) hψ₀s) :=
        funext fun F => (u16_ev_apply _ _ F).symm
      rw [e]
      exact (u16_ev (rLvl d) hψ₀s).continuous.measurable
    have hind2 := hA'.comp hg ha
    have e2 : (fun x : EuclideanSpace ℝ (Fin 2) => x 0 - x 1) ∘ (fun ω => (WithLp.toLp 2 fun a =>
        Nrv gd (![t, τ] a) (![ψ₂, ψ₃] a) ω : EuclideanSpace ℝ (Fin 2))) = fun ω => N₂ ω - N₃ ω := by
      funext ω; simp [hN₂, hN₃]
    rw [e2] at hind2
    have hind3 : IndepFun (fun ω => N₂ ω - N₃ ω) A gd.P₀ := hind2
    have := hind3.integral_fun_mul_eq_mul_integral hSB.measurable.aestronglyMeasurable
      hSA.measurable.aestronglyMeasurable
    have e5 : ∫ ω, A ω * (N₂ ω - N₃ ω) ∂gd.P₀ = ∫ ω, (N₂ ω - N₃ ω) * A ω ∂gd.P₀ :=
      integral_congr_ae (Eventually.of_forall fun ω => by simp [mul_comm])
    rw [e5, this, hSA.memLp_mean.2, mul_zero]
  rw [hind]
  have k12 := i12.2
  have k13 := i13.2
  rw [k12, k13, u16_covK_cocycle hE hs0 hsτ hτt hψ₂s]
  ring

/-- **Future independence.**  The past coordinates `η^s(ψ)`, `s ≤ τ`, are independent of the future coordinates
`η^t(ψ) - η^τ(U^{τ,t}ψ)`, `t > τ`. -/
theorem u16_indep {H τ : ℝ} (hH : 0 < H) (hτ : τ ∈ Set.Icc (0 : ℝ) H) :
    IndepFun (fun ω p => Xs gd τ p ω) (fun ω q => Ys gd τ H q ω) gd.P₀ :=
  IsGaussianProcess.indepFun_of_covariance_eq_zero (u16_gp gd hτ)
    (fun p => (u16_isSC_Xs gd hτ p).measurable.aemeasurable)
    (fun q => (u16_isSC_Ys gd hτ q).measurable.aemeasurable)
    (fun p q => u16_cov_zero gd hH hτ p q)

end Indep

end HRS.MC.E213U16

end
