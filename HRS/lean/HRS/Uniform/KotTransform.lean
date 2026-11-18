import HRS.Uniform.KotTrace
import HRS.Prob.HilbertMartingale
import HRS.Stochastic.Simple
import HRS.Stochastic.QuadraticVariation

/-!
# Step-operator transforms of Hilbert martingales (packet KOTELENEZ)

If `M` is a Hilbert-valued martingale with covariation (`IsHilbertMartingaleWithCovariation`), `s_0 ≤ s_1 ≤ …` a
partition of `[0,T]` and `A_l : H → K` bounded operators, the process
`N_t = ∑_l A_l (M_{c_l(t)} - M_{s_l})` (`c_l(t)` the clamp of `t` to `[s_l, s_{l+1}]`) is again such a martingale,
with covariation density `Σ^N_r = Σ_r ∘ (A_l^*, A_l^*)` for `r ∈ (s_l, s_{l+1}]` (`stepT`, `stepSg`,
`isHMC_stepT`).  Only deterministic operators occur; no stochastic integration is needed.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

namespace HRS
namespace Uniform
namespace Kot

section RealMart

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {ℱ : Filtration ℝ mΩ}

/-- Clamp of `t` to `[a, b]` (for `a ≤ b`). -/
def clampI (a b t : ℝ) : ℝ := max a (min t b)

theorem clampI_of_le_left {a b t : ℝ} (h : t ≤ a) : clampI a b t = a := by
  unfold clampI
  exact max_eq_left ((min_le_left _ _).trans h)

theorem clampI_of_right_le {a b t : ℝ} (hab : a ≤ b) (h : b ≤ t) : clampI a b t = b := by
  unfold clampI
  rw [min_eq_right h, max_eq_right hab]

theorem clampI_of_mem {a b t : ℝ} (h1 : a ≤ t) (h2 : t ≤ b) : clampI a b t = t := by
  unfold clampI
  rw [min_eq_left h2, max_eq_right h1]

theorem clampI_mem {a b : ℝ} (hab : a ≤ b) (t : ℝ) : clampI a b t ∈ Icc a b :=
  ⟨le_max_left _ _, max_le hab (min_le_right _ _)⟩

theorem continuous_clampI (a b : ℝ) : Continuous (clampI a b) :=
  continuous_const.max (continuous_id.min continuous_const)

theorem clampI_le_self {a b t : ℝ} (h : a ≤ t) : clampI a b t ≤ t := by
  unfold clampI
  exact max_le h (min_le_left _ _)

theorem le_clampI_of_le {a b s t : ℝ} (hab : a ≤ b) (hs : s ≤ t) (hsb : s ≤ b) (has : a ≤ s) :
    s ≤ clampI a b t := by
  unfold clampI
  exact le_max_of_le_right (le_min hs hsb)

/-- Gluing: a process vanishing up to time `a`, adapted, integrable and with the martingale property for
times `≥ a` is a martingale. -/
theorem martingale_of_after {f : ℝ → Ω → ℝ} (a : ℝ) (hmeas : ∀ t, StronglyMeasurable[ℱ t] (f t))
    (hint : ∀ t, Integrable (f t) P) (h0 : ∀ t ≤ a, f t = 0)
    (hmart : ∀ s t, a ≤ s → s ≤ t → P[f t | ℱ s] =ᵐ[P] f s) : Martingale f ℱ P := by
  refine ⟨hmeas, fun s t hst => ?_⟩
  by_cases hs : a ≤ s
  · exact hmart s t hs hst
  · rw [not_le] at hs
    have hfs : f s = 0 := h0 s hs.le
    by_cases ht : t ≤ a
    · rw [h0 t ht, hfs]; simp
    · rw [not_le] at ht
      have h1 := hmart a t le_rfl ht.le
      have h2 := condExp_condExp_of_le (μ := P) (f := f t) (ℱ.mono hs.le) (ℱ.le a)
      calc P[f t | ℱ s] =ᵐ[P] P[P[f t | ℱ a] | ℱ s] := h2.symm
        _ =ᵐ[P] P[f a | ℱ s] := condExp_congr_ae h1
        _ = f s := by rw [h0 a le_rfl, hfs]; simp

/-- For `a ≤ s ≤ t`: `E[Y(c(t)) | ℱ_s] = Y(c(s))`. -/
theorem condExp_clamp {Y : ℝ → Ω → ℝ} (hY : Martingale Y ℱ P) {a b s t : ℝ} (hab : a ≤ b) (hs : a ≤ s)
    (hst : s ≤ t) : P[Y (clampI a b t) | ℱ s] =ᵐ[P] Y (clampI a b s) := by
  by_cases hsb : s ≤ b
  · have hcs : clampI a b s = s := clampI_of_mem hs hsb
    rw [hcs]
    exact hY.condExp_ae_eq (le_clampI_of_le hab hst hsb hs)
  · rw [not_le] at hsb
    have hcs : clampI a b s = b := clampI_of_right_le hab hsb.le
    have hct : clampI a b t = b := clampI_of_right_le hab (hsb.le.trans hst)
    rw [hcs, hct]
    exact (condExp_of_stronglyMeasurable (ℱ.le s)
      ((hY.stronglyAdapted b).mono (ℱ.mono hsb.le)) (hY.integrable b)).eventuallyEq

/-- Clamped increments of a martingale: `t ↦ Y(c(t)) - Y(a)` is a martingale. -/
theorem martingale_clampInc {Y : ℝ → Ω → ℝ} (hY : Martingale Y ℱ P) {a b : ℝ} (hab : a ≤ b) :
    Martingale (fun t ω => Y (clampI a b t) ω - Y a ω) ℱ P := by
  refine martingale_of_after a (fun t => ?_) (fun t => ?_) (fun t ht => ?_) (fun s t hs hst => ?_)
  · by_cases ht : a ≤ t
    · exact (((hY.stronglyAdapted (clampI a b t)).mono (ℱ.mono (clampI_le_self ht))).sub
        ((hY.stronglyAdapted a).mono (ℱ.mono ht)))
    · rw [not_le] at ht
      have : (fun ω => Y (clampI a b t) ω - Y a ω) = fun _ => (0 : ℝ) := by
        funext ω; rw [clampI_of_le_left ht.le]; simp
      rw [this]; exact stronglyMeasurable_const
  · exact (hY.integrable _).sub (hY.integrable _)
  · funext ω; simp [clampI_of_le_left ht]
  · have hYa : StronglyMeasurable[ℱ s] (Y a) := (hY.stronglyAdapted a).mono (ℱ.mono hs)
    have e1 : P[fun ω => Y (clampI a b t) ω - Y a ω | ℱ s] =ᵐ[P]
        P[Y (clampI a b t) | ℱ s] - P[Y a | ℱ s] :=
      condExp_sub (hY.integrable _) (hY.integrable _) _
    have e2 : P[Y a | ℱ s] =ᵐ[P] Y a :=
      (condExp_of_stronglyMeasurable (ℱ.le s) hYa (hY.integrable a)).eventuallyEq
    have e3 := condExp_clamp hY hab hs hst
    filter_upwards [e1, e2, e3] with ω h1 h2 h3
    simp only [Pi.sub_apply] at h1
    rw [h1, h2, h3]

/-- Cross terms of disjoint consecutive cells are martingales. -/
theorem cell_cross {X Y : ℝ → Ω → ℝ} (hX : Martingale X ℱ P) (hY : Martingale Y ℱ P) {a b a' b' : ℝ}
    (hab : a ≤ b) (hba' : b ≤ a') (ha'b' : a' ≤ b')
    (hX2 : MemLp (fun ω => X b ω - X a ω) 2 P)
    (hY2 : ∀ τ ∈ Icc a' b', MemLp (Y τ) 2 P) (hYa : MemLp (Y a') 2 P) :
    Martingale (fun t ω => (X (clampI a b t) ω - X a ω) * (Y (clampI a' b' t) ω - Y a' ω)) ℱ P := by
  have hYm := martingale_clampInc hY ha'b'
  set ξ : Ω → ℝ := fun ω => X b ω - X a ω with hξ
  have hξm : StronglyMeasurable[ℱ a'] ξ :=
    (((hX.stronglyAdapted b).mono (ℱ.mono hba')).sub ((hX.stronglyAdapted a).mono (ℱ.mono (hab.trans hba'))))
  have hint : ∀ s, Integrable (fun ω => ξ ω * (Y (clampI a' b' s) ω - Y a' ω)) P := by
    intro s
    have h1 : MemLp (fun ω => Y (clampI a' b' s) ω - Y a' ω) 2 P :=
      (hY2 _ (clampI_mem ha'b' s)).sub hYa
    exact hX2.integrable_mul h1
  have hmul := SimpleIntegrand.martingale_mul_left hYm (a := a') (fun s hs => by
      funext ω; simp [clampI_of_le_left hs]) hξm hint
  convert hmul using 2 with t
  funext ω
  by_cases ht : t ≤ a'
  · simp [clampI_of_le_left ht]
  · rw [not_le] at ht
    rw [clampI_of_right_le hab (hba'.trans ht.le)]

/-- The covariation of a clamped increment: `U_c V_c - (G(c) - G(a))` is a martingale when
`Y^x Y^y - G` is one (`G = Y^x Y^y - Φ`). -/
theorem cell_bracket {Yx Yy Φ G : ℝ → Ω → ℝ} (hx : Martingale Yx ℱ P) (hy : Martingale Yy ℱ P)
    (hΦ : Martingale Φ ℱ P) (hG : ∀ τ ω, G τ ω = Yx τ ω * Yy τ ω - Φ τ ω) {a b : ℝ} (hab : a ≤ b)
    (hxy : ∀ τ ∈ Icc a b, MemLp (Yx τ) 2 P ∧ MemLp (Yy τ) 2 P) :
    Martingale (fun t ω => (Yx (clampI a b t) ω - Yx a ω) * (Yy (clampI a b t) ω - Yy a ω) -
      (G (clampI a b t) ω - G a ω)) ℱ P := by
  have haIcc : a ∈ Icc a b := ⟨le_rfl, hab⟩
  set κ : Ω → ℝ := fun ω => Yx a ω * Yy a ω + G a ω with hκ
  have hGa : ∀ ω, G a ω = Yx a ω * Yy a ω - Φ a ω := fun ω => hG a ω
  have hid : ∀ t ω, (Yx (clampI a b t) ω - Yx a ω) * (Yy (clampI a b t) ω - Yy a ω) -
      (G (clampI a b t) ω - G a ω) = Φ (clampI a b t) ω - Yx a ω * Yy (clampI a b t) ω -
        Yy a ω * Yx (clampI a b t) ω + κ ω := by
    intro t ω
    rw [hG (clampI a b t) ω]
    simp only [hκ]
    ring
  have hint2 : ∀ τ ∈ Icc a b, Integrable (fun ω => Yx a ω * Yy τ ω) P := fun τ hτ =>
    (hxy a haIcc).1.integrable_mul (hxy τ hτ).2
  have hint2' : ∀ τ ∈ Icc a b, Integrable (fun ω => Yy a ω * Yx τ ω) P := fun τ hτ =>
    (hxy a haIcc).2.integrable_mul (hxy τ hτ).1
  have hκint : Integrable κ P := by
    have h1 : Integrable (fun ω => Yx a ω * Yy a ω) P := (hxy a haIcc).1.integrable_mul (hxy a haIcc).2
    have h2 : Integrable (G a) P := by
      have : G a = fun ω => Yx a ω * Yy a ω - Φ a ω := funext hGa
      rw [this]; exact h1.sub (hΦ.integrable a)
    exact h1.add h2
  have hκm : StronglyMeasurable[ℱ a] κ := by
    have h1 : StronglyMeasurable[ℱ a] (fun ω => Yx a ω * Yy a ω) :=
      (hx.stronglyAdapted a).mul (hy.stronglyAdapted a)
    have h2 : StronglyMeasurable[ℱ a] (G a) := by
      have : G a = fun ω => Yx a ω * Yy a ω - Φ a ω := funext hGa
      rw [this]; exact h1.sub (hΦ.stronglyAdapted a)
    exact h1.add h2
  refine martingale_of_after a (fun t => ?_) (fun t => ?_) (fun t ht => ?_) (fun s t hs hst => ?_)
  · by_cases ht : a ≤ t
    · simp_rw [hid t]
      have hc : ℱ (clampI a b t) ≤ ℱ t := ℱ.mono (clampI_le_self ht)
      have hat : ℱ a ≤ ℱ t := ℱ.mono ht
      refine ((((hΦ.stronglyAdapted _).mono hc).sub
        (((hx.stronglyAdapted a).mono hat).mul ((hy.stronglyAdapted _).mono hc))).sub
        (((hy.stronglyAdapted a).mono hat).mul ((hx.stronglyAdapted _).mono hc))).add (hκm.mono hat)
    · rw [not_le] at ht
      have : (fun ω => (Yx (clampI a b t) ω - Yx a ω) * (Yy (clampI a b t) ω - Yy a ω) -
          (G (clampI a b t) ω - G a ω)) = fun _ => (0 : ℝ) := by
        funext ω; rw [clampI_of_le_left ht.le]; simp
      rw [this]; exact stronglyMeasurable_const
  · simp_rw [hid t]
    have hc := clampI_mem hab t
    exact ((((hΦ.integrable _).sub (hint2 _ hc)).sub (hint2' _ hc)).add hκint)
  · funext ω; simp [clampI_of_le_left ht]
  · have hc := clampI_mem hab t
    have hcs := clampI_mem hab s
    have hsm : ℱ a ≤ ℱ s := ℱ.mono hs
    have hf : ∀ u : ℝ, (fun ω => (Yx (clampI a b u) ω - Yx a ω) * (Yy (clampI a b u) ω - Yy a ω) -
        (G (clampI a b u) ω - G a ω)) = Φ (clampI a b u) - (Yx a * Yy (clampI a b u)) -
          (Yy a * Yx (clampI a b u)) + κ := by
      intro u; funext ω; rw [hid u ω]; rfl
    rw [hf t]
    have e1 : P[Φ (clampI a b t) - (Yx a * Yy (clampI a b t)) - (Yy a * Yx (clampI a b t)) + κ | ℱ s]
        =ᵐ[P] P[Φ (clampI a b t) | ℱ s] - P[Yx a * Yy (clampI a b t) | ℱ s] -
          P[Yy a * Yx (clampI a b t) | ℱ s] + P[κ | ℱ s] := by
      refine (condExp_add (((hΦ.integrable _).sub (hint2 _ hc)).sub (hint2' _ hc)) hκint _).trans ?_
      refine EventuallyEq.add ?_ EventuallyEq.rfl
      refine (condExp_sub ((hΦ.integrable _).sub (hint2 _ hc)) (hint2' _ hc) _).trans ?_
      refine EventuallyEq.sub ?_ EventuallyEq.rfl
      exact condExp_sub (hΦ.integrable _) (hint2 _ hc) _
    have e2 : P[Yx a * Yy (clampI a b t) | ℱ s] =ᵐ[P] Yx a * Yy (clampI a b s) := by
      refine (condExp_mul_of_stronglyMeasurable_left ((hx.stronglyAdapted a).mono hsm)
        (hint2 _ hc) (hy.integrable _)).trans ?_
      exact EventuallyEq.mul EventuallyEq.rfl (condExp_clamp hy hab hs hst)
    have e3 : P[Yy a * Yx (clampI a b t) | ℱ s] =ᵐ[P] Yy a * Yx (clampI a b s) := by
      refine (condExp_mul_of_stronglyMeasurable_left ((hy.stronglyAdapted a).mono hsm)
        (hint2' _ hc) (hx.integrable _)).trans ?_
      exact EventuallyEq.mul EventuallyEq.rfl (condExp_clamp hx hab hs hst)
    have e4 : P[κ | ℱ s] =ᵐ[P] κ :=
      (condExp_of_stronglyMeasurable (ℱ.le s) (hκm.mono hsm) hκint).eventuallyEq
    have e5 := condExp_clamp hΦ hab hs hst
    rw [hf s]
    filter_upwards [e1, e2, e3, e4, e5] with ω h1 h2 h3 h4 h5
    rw [h1]
    simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply] at h2 h3 h4 h5 ⊢
    rw [h2, h3, h4, h5]

/-- The integral of an indicator of a cell over `[0,t]`. -/
theorem cell_integral {f : ℝ → ℝ} {T a b t : ℝ} (h0 : 0 ≤ a) (hab : a ≤ b) (hbT : b ≤ T)
    (hf : IntegrableOn f (Icc 0 T)) :
    ∫ σ in Icc 0 t, (Ioc a b).indicator f σ =
      (∫ σ in Icc 0 (clampI a b t), f σ) - ∫ σ in Icc 0 a, f σ := by
  rw [setIntegral_indicator measurableSet_Ioc]
  have hset : Icc 0 t ∩ Ioc a b = Ioc a (clampI a b t) := by
    ext σ
    simp only [mem_inter_iff, mem_Icc, mem_Ioc]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3, h4⟩
      refine ⟨h3, ?_⟩
      unfold clampI
      exact le_max_of_le_right (le_min h2 h4)
    · rintro ⟨h1, h2⟩
      have hc := clampI_mem hab t
      have hct : clampI a b t ≤ t ∨ t < a := by
        by_cases hta : a ≤ t
        · exact Or.inl (clampI_le_self hta)
        · exact Or.inr (not_le.1 hta)
      refine ⟨⟨h0.trans h1.le, ?_⟩, h1, h2.trans hc.2⟩
      rcases hct with h | h
      · exact h2.trans h
      · rw [clampI_of_le_left h.le] at h2
        exact absurd h1 (not_lt.2 h2)
  rw [hset]
  have hc := clampI_mem hab t
  have hsub : ∀ c, c ≤ T → Icc 0 c ⊆ Icc 0 T := fun c hc' => Icc_subset_Icc le_rfl hc'
  have hI1 : IntegrableOn f (Icc 0 a) := hf.mono_set (hsub a (hab.trans hbT))
  have hI2 : IntegrableOn f (Ioc a (clampI a b t)) :=
    hf.mono_set (fun σ hσ => ⟨h0.trans hσ.1.le, hσ.2.trans (hc.2.trans hbT)⟩)
  have hunion : Icc 0 (clampI a b t) = Icc 0 a ∪ Ioc a (clampI a b t) :=
    (Icc_union_Ioc_eq_Icc h0 hc.1).symm
  have hdisj : Disjoint (Icc 0 a) (Ioc a (clampI a b t)) :=
    disjoint_left.2 fun σ h1 h2 => absurd h2.1 (not_lt.2 h1.2)
  rw [hunion, setIntegral_union hdisj measurableSet_Ioc hI1 hI2]
  ring

end RealMart

section StepTransform

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {ℱ : Filtration ℝ mΩ}
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
variable {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]
  [MeasurableSpace K] [BorelSpace K] [SecondCountableTopology K]

/-- The step-operator transform `N_t = ∑_{l<n} A_l (M_{c_l(t)} - M_{s_l})`. -/
def stepT (M : ℝ → Ω → H) (s : ℕ → ℝ) (n : ℕ) (A : ℕ → H →L[ℝ] K) (τ : ℝ) (ω : Ω) : K :=
  ∑ l ∈ Finset.range n, A l (M (clampI (s l) (s (l + 1)) τ) ω - M (s l) ω)

/-- The covariation density of the step transform. -/
def stepSg (Sg : ℝ → Ω → (H →L[ℝ] H →L[ℝ] ℝ)) (s : ℕ → ℝ) (n : ℕ) (A : ℕ → H →L[ℝ] K)
    (r : ℝ) (ω : Ω) : K →L[ℝ] K →L[ℝ] ℝ :=
  ∑ l ∈ Finset.range n, (Ioc (s l) (s (l + 1))).indicator
    (fun r => formComp (ContinuousLinearMap.adjoint (A l)) (Sg r ω)) r

theorem stepSg_apply (Sg : ℝ → Ω → (H →L[ℝ] H →L[ℝ] ℝ)) (s : ℕ → ℝ) (n : ℕ) (A : ℕ → H →L[ℝ] K)
    (r : ℝ) (ω : Ω) (u v : K) :
    stepSg Sg s n A r ω u v = ∑ l ∈ Finset.range n,
      if r ∈ Ioc (s l) (s (l + 1)) then
        Sg r ω (ContinuousLinearMap.adjoint (A l) u) (ContinuousLinearMap.adjoint (A l) v) else 0 := by
  unfold stepSg
  rw [ContinuousLinearMap.sum_apply, ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl fun l _ => ?_
  by_cases h : r ∈ Ioc (s l) (s (l + 1))
  · simp [h]
  · simp [h]

theorem stepSg_of_mem {Sg : ℝ → Ω → (H →L[ℝ] H →L[ℝ] ℝ)} {s : ℕ → ℝ} (hs : Monotone s) {n : ℕ}
    {A : ℕ → H →L[ℝ] K} {l : ℕ} (hl : l < n) {r : ℝ} (hr : r ∈ Ioc (s l) (s (l + 1))) (ω : Ω) :
    stepSg Sg s n A r ω = formComp (ContinuousLinearMap.adjoint (A l)) (Sg r ω) := by
  unfold stepSg
  rw [Finset.sum_eq_single l]
  · simp [hr]
  · intro l' hl' hne
    have : r ∉ Ioc (s l') (s (l' + 1)) := by
      intro hr'
      rcases lt_or_gt_of_ne hne with h | h
      · have h1 : s (l' + 1) ≤ s l := hs (by omega)
        have := hr.1
        have := hr'.2
        linarith
      · have : s (l + 1) ≤ s l' := hs (by omega)
        have := hr.2
        have := hr'.1
        linarith
    simp [this]
  · intro h; exact absurd (Finset.mem_range.2 hl) h

theorem stepSg_of_not_mem {Sg : ℝ → Ω → (H →L[ℝ] H →L[ℝ] ℝ)} {s : ℕ → ℝ} {n : ℕ}
    {A : ℕ → H →L[ℝ] K} {r : ℝ} (hr : ∀ l < n, r ∉ Ioc (s l) (s (l + 1))) (ω : Ω) :
    stepSg Sg s n A r ω = 0 := by
  unfold stepSg
  refine Finset.sum_eq_zero fun l hl => ?_
  simp [hr l (Finset.mem_range.1 hl)]

theorem cell_mem {s : ℕ → ℝ} (hs : Monotone s) {n : ℕ} {T : ℝ} (h0 : 0 ≤ s 0) (hsn : s n ≤ T)
    {l : ℕ} (hl : l < n) : 0 ≤ s l ∧ s l ≤ s (l + 1) ∧ s (l + 1) ≤ T :=
  ⟨h0.trans (hs (Nat.zero_le l)), hs (Nat.le_succ l), (hs (by omega : l + 1 ≤ n)).trans hsn⟩

theorem inner_stepT (M : ℝ → Ω → H) (s : ℕ → ℝ) (n : ℕ) (A : ℕ → H →L[ℝ] K) (τ : ℝ) (ω : Ω)
    (u : K) : inner ℝ (stepT M s n A τ ω) u = ∑ l ∈ Finset.range n,
      (inner ℝ (M (clampI (s l) (s (l + 1)) τ) ω) (ContinuousLinearMap.adjoint (A l) u) -
        inner ℝ (M (s l) ω) (ContinuousLinearMap.adjoint (A l) u)) := by
  unfold stepT
  rw [sum_inner]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [← ContinuousLinearMap.adjoint_inner_right, inner_sub_left]

variable {T : ℝ} {M : ℝ → Ω → H} {Sg : ℝ → Ω → (H →L[ℝ] H →L[ℝ] ℝ)}

theorem stepT_martingale (hM : IsHilbertMartingaleWithCovariation P ℱ T M Sg) {s : ℕ → ℝ}
    (hs : Monotone s) {n : ℕ} (A : ℕ → H →L[ℝ] K) (u : K) :
    Martingale (fun τ ω => inner ℝ (stepT M s n A τ ω) u) ℱ P := by
  have : (fun τ ω => inner ℝ (stepT M s n A τ ω) u) = fun τ ω => ∑ l ∈ Finset.range n,
      (inner ℝ (M (clampI (s l) (s (l + 1)) τ) ω) (ContinuousLinearMap.adjoint (A l) u) -
        inner ℝ (M (s l) ω) (ContinuousLinearMap.adjoint (A l) u)) := by
    funext τ ω; exact inner_stepT M s n A τ ω u
  rw [this]
  exact SimpleIntegrand.martingale_finset_sum _ fun l _ =>
    martingale_clampInc (hM.martingale _) (hs (Nat.le_succ l))

theorem stepT_zero {s : ℕ → ℝ} (hs : Monotone s) (h0 : 0 ≤ s 0) {n : ℕ} (A : ℕ → H →L[ℝ] K) (ω : Ω) :
    stepT M s n A 0 ω = 0 := by
  unfold stepT
  refine Finset.sum_eq_zero fun l _ => ?_
  rw [clampI_of_le_left (h0.trans (hs (Nat.zero_le l)))]
  simp

theorem stepT_cont (hM : IsHilbertMartingaleWithCovariation P ℱ T M Sg) {s : ℕ → ℝ}
    (hs : Monotone s) {n : ℕ} (h0 : 0 ≤ s 0) (hsn : s n ≤ T) (A : ℕ → H →L[ℝ] K) :
    ∀ᵐ ω ∂P, ContinuousOn (fun τ => stepT M s n A τ ω) (Icc 0 T) := by
  filter_upwards [hM.cont] with ω hω
  unfold stepT
  refine continuousOn_finset_sum _ fun l hl => ?_
  have hc := cell_mem hs h0 hsn (Finset.mem_range.1 hl)
  refine (A l).continuous.comp_continuousOn ?_
  refine ContinuousOn.sub ?_ continuousOn_const
  refine hω.comp (continuous_clampI _ _).continuousOn fun τ _ => ?_
  have := clampI_mem hc.2.1 τ
  exact ⟨hc.1.trans this.1, this.2.trans hc.2.2⟩

theorem stepT_memLp (hM : IsHilbertMartingaleWithCovariation P ℱ T M Sg) {s : ℕ → ℝ}
    (hs : Monotone s) {n : ℕ} (h0 : 0 ≤ s 0) (hsn : s n ≤ T) (A : ℕ → H →L[ℝ] K) (τ : ℝ) :
    MemLp (stepT M s n A τ) 2 P := by
  have : stepT M s n A τ = fun ω => ∑ l ∈ Finset.range n,
      A l (M (clampI (s l) (s (l + 1)) τ) ω - M (s l) ω) := rfl
  rw [this]
  refine memLp_finset_sum _ fun l hl => ?_
  have hc := cell_mem hs h0 hsn (Finset.mem_range.1 hl)
  have h1 := clampI_mem hc.2.1 τ
  have h2 : MemLp (M (clampI (s l) (s (l + 1)) τ)) 2 P :=
    hM.sq_int _ ⟨hc.1.trans h1.1, h1.2.trans hc.2.2⟩
  have h3 : MemLp (M (s l)) 2 P := hM.sq_int _ ⟨hc.1, hc.2.1.trans hc.2.2⟩
  exact (A l).comp_memLp' (h2.sub h3)

theorem isTraceClassCov_zero {K' : Type} [NormedAddCommGroup K'] [InnerProductSpace ℝ K']
    [CompleteSpace K'] : IsTraceClassCov (0 : K' →L[ℝ] K' →L[ℝ] ℝ) := by
  refine ⟨fun x y => by simp, fun x => by simp, ?_⟩
  obtain ⟨w, b, -⟩ := exists_hilbertBasis ℝ K'
  exact ⟨w, b, by simp [summable_zero]⟩

theorem traceNormForm_zero {K' : Type} [NormedAddCommGroup K'] [InnerProductSpace ℝ K'] :
    traceNormForm (0 : K' →L[ℝ] K' →L[ℝ] ℝ) = 0 := by
  unfold traceNormForm
  simp

theorem stepSg_isTraceClassCov {s : ℕ → ℝ} (hs : Monotone s) {n : ℕ} {A : ℕ → H →L[ℝ] K} {r : ℝ}
    {ω : Ω} (hr : IsTraceClassCov (Sg r ω)) : IsTraceClassCov (stepSg Sg s n A r ω) := by
  by_cases h : ∃ l < n, r ∈ Ioc (s l) (s (l + 1))
  · obtain ⟨l, hl, hrl⟩ := h
    rw [stepSg_of_mem hs hl hrl]
    exact isTraceClassCov_formComp hr _
  · push_neg at h
    rw [stepSg_of_not_mem h]
    exact isTraceClassCov_zero

theorem traceNormForm_stepSg_le {s : ℕ → ℝ} (hs : Monotone s) {n : ℕ} {A : ℕ → H →L[ℝ] K} {cA : ℝ}
    (hA : ∀ l < n, ‖A l‖ ≤ cA) {r : ℝ} {ω : Ω} (hr : IsTraceClassCov (Sg r ω)) :
    traceNormForm (stepSg Sg s n A r ω) ≤ cA ^ 2 * traceNormForm (Sg r ω) := by
  by_cases h : ∃ l < n, r ∈ Ioc (s l) (s (l + 1))
  · obtain ⟨l, hl, hrl⟩ := h
    rw [stepSg_of_mem hs hl hrl]
    refine (traceNormForm_formComp_le hr _).trans ?_
    rw [LinearIsometryEquiv.norm_map]
    have h1 : ‖A l‖ ^ 2 ≤ cA ^ 2 := by
      have := hA l hl
      nlinarith [norm_nonneg (A l)]
    exact mul_le_mul_of_nonneg_right h1 (traceNormForm_nonneg _)
  · push_neg at h
    rw [stepSg_of_not_mem h, traceNormForm_zero]
    exact mul_nonneg (sq_nonneg _) (traceNormForm_nonneg _)

theorem measurable_stepSg_entry (hM : IsHilbertMartingaleWithCovariation P ℱ T M Sg) (s : ℕ → ℝ)
    (n : ℕ) (A : ℕ → H →L[ℝ] K) (u v : K) :
    Measurable (Function.uncurry fun r ω => stepSg Sg s n A r ω u v) := by
  have : (Function.uncurry fun r ω => stepSg Sg s n A r ω u v) = fun p : ℝ × Ω =>
      ∑ l ∈ Finset.range n, if p.1 ∈ Ioc (s l) (s (l + 1)) then
        Sg p.1 p.2 (ContinuousLinearMap.adjoint (A l) u) (ContinuousLinearMap.adjoint (A l) v) else 0 := by
    funext p; exact stepSg_apply Sg s n A p.1 p.2 u v
  rw [this]
  refine Finset.measurable_sum _ fun l _ => ?_
  exact Measurable.ite (measurableSet_Ioc.preimage measurable_fst)
    (hM.sigma_meas _ _) measurable_const

theorem measurable_traceNormForm_stepSg (hM : IsHilbertMartingaleWithCovariation P ℱ T M Sg)
    (s : ℕ → ℝ) (n : ℕ) (A : ℕ → H →L[ℝ] K) :
    Measurable (Function.uncurry fun r ω => traceNormForm (stepSg Sg s n A r ω)) := by
  have := measurable_traceNormForm (H := K) (α := ℝ × Ω)
    (fun p => stepSg Sg s n A p.1 p.2) (fun u v => measurable_stepSg_entry hM s n A u v)
  exact this

theorem memLp_coord (hM : IsHilbertMartingaleWithCovariation P ℱ T M Sg) {τ : ℝ}
    (hτ : τ ∈ Icc 0 T) (x : H) : MemLp (fun ω => inner ℝ (M τ ω) x) 2 P := by
  have e : (fun ω => inner ℝ (M τ ω) x) = fun ω => innerSL ℝ x (M τ ω) :=
    funext fun ω => real_inner_comm x (M τ ω)
  rw [e]
  exact (innerSL ℝ x).comp_memLp' (hM.sq_int τ hτ)

theorem stepSg_apply' (Sg : ℝ → Ω → (H →L[ℝ] H →L[ℝ] ℝ)) (s : ℕ → ℝ) (n : ℕ) (A : ℕ → H →L[ℝ] K)
    (r : ℝ) (ω : Ω) (u v : K) :
    stepSg Sg s n A r ω u v = ∑ l ∈ Finset.range n, (Ioc (s l) (s (l + 1))).indicator
      (fun σ => Sg σ ω (ContinuousLinearMap.adjoint (A l) u) (ContinuousLinearMap.adjoint (A l) v)) r := by
  rw [stepSg_apply]
  exact Finset.sum_congr rfl fun l _ => by rw [Set.indicator_apply]

/-- The covariation martingale of the step transform. -/
theorem stepT_covariation (hcomp : IsCompleteFiltration P ℱ)
    (hM : IsHilbertMartingaleWithCovariation P ℱ T M Sg) {s : ℕ → ℝ} (hs : Monotone s) {n : ℕ}
    (h0 : 0 ≤ s 0) (hsn : s n ≤ T) (A : ℕ → H →L[ℝ] K) (u v : K) :
    Martingale (fun τ ω => inner ℝ (stepT M s n A τ ω) u * inner ℝ (stepT M s n A τ ω) v -
      ∫ σ in Icc 0 τ, stepSg Sg s n A σ ω u v) ℱ P := by
  classical
  set x : ℕ → H := fun l => ContinuousLinearMap.adjoint (A l) u with hx
  set y : ℕ → H := fun l => ContinuousLinearMap.adjoint (A l) v with hy
  set Gb : H → H → ℝ → Ω → ℝ := fun a b τ ω => ∫ σ in Icc 0 τ, Sg σ ω a b with hGb
  set p : ℕ → ℝ → Ω → ℝ := fun l t ω =>
    inner ℝ (M (clampI (s l) (s (l + 1)) t) ω) (x l) - inner ℝ (M (s l) ω) (x l) with hp
  set q : ℕ → ℝ → Ω → ℝ := fun l t ω =>
    inner ℝ (M (clampI (s l) (s (l + 1)) t) ω) (y l) - inner ℝ (M (s l) ω) (y l) with hq
  set Kl : ℕ → ℝ → Ω → ℝ := fun l t ω =>
    Gb (x l) (y l) (clampI (s l) (s (l + 1)) t) ω - Gb (x l) (y l) (s l) ω with hKl
  set term : ℕ → ℕ → ℝ → Ω → ℝ := fun l l' t ω => p l t ω * q l' t ω - if l = l' then Kl l t ω else 0
    with hterm
  set ψ : ℝ → Ω → ℝ := fun t ω => ∑ l ∈ Finset.range n, ∑ l' ∈ Finset.range n, term l l' t ω with hψ
  -- (1) `ψ` is a martingale
  have hmartTerm : ∀ l ∈ Finset.range n, ∀ l' ∈ Finset.range n, Martingale (term l l') ℱ P := by
    intro l hl l' hl'
    have hc := cell_mem hs h0 hsn (Finset.mem_range.1 hl)
    have hc' := cell_mem hs h0 hsn (Finset.mem_range.1 hl')
    by_cases hll : l = l'
    · subst hll
      have hb := cell_bracket (hM.martingale (x l)) (hM.martingale (y l)) (hM.covariation (x l) (y l))
        (G := Gb (x l) (y l)) (fun τ ω => by simp [hGb]) hc.2.1
        (fun τ hτ => ⟨memLp_coord hM ⟨hc.1.trans hτ.1, hτ.2.trans hc.2.2⟩ _,
          memLp_coord hM ⟨hc.1.trans hτ.1, hτ.2.trans hc.2.2⟩ _⟩)
      convert hb using 2 with t
      funext ω
      simp [hterm, hp, hq, hKl, inner_sub_left]
    · rcases lt_or_gt_of_ne hll with hlt | hgt
      · have hba : s (l + 1) ≤ s l' := hs hlt
        have hX2 : MemLp (fun ω => inner ℝ (M (s (l + 1)) ω) (x l) - inner ℝ (M (s l) ω) (x l)) 2 P :=
          (memLp_coord hM ⟨hc.1.trans hc.2.1, hc.2.2⟩ _).sub (memLp_coord hM ⟨hc.1, hc.2.1.trans hc.2.2⟩ _)
        have hcr := cell_cross (hM.martingale (x l)) (hM.martingale (y l')) hc.2.1 hba hc'.2.1 hX2
          (fun τ hτ => memLp_coord hM ⟨hc'.1.trans hτ.1, hτ.2.trans hc'.2.2⟩ _)
          (memLp_coord hM ⟨hc'.1, hc'.2.1.trans hc'.2.2⟩ _)
        convert hcr using 2 with t
        funext ω
        simp [hterm, hp, hq, hll]
      · have hba : s (l' + 1) ≤ s l := hs hgt
        have hX2 : MemLp (fun ω => inner ℝ (M (s (l' + 1)) ω) (y l') - inner ℝ (M (s l') ω) (y l')) 2 P :=
          (memLp_coord hM ⟨hc'.1.trans hc'.2.1, hc'.2.2⟩ _).sub (memLp_coord hM ⟨hc'.1, hc'.2.1.trans hc'.2.2⟩ _)
        have hcr := cell_cross (hM.martingale (y l')) (hM.martingale (x l)) hc'.2.1 hba hc.2.1 hX2
          (fun τ hτ => memLp_coord hM ⟨hc.1.trans hτ.1, hτ.2.trans hc.2.2⟩ _)
          (memLp_coord hM ⟨hc.1, hc.2.1.trans hc.2.2⟩ _)
        convert hcr using 2 with t
        funext ω
        simp only [hterm, hp, hq, hll, if_false, sub_zero]
        ring
  have hψm : Martingale ψ ℱ P :=
    SimpleIntegrand.martingale_finset_sum _ fun l hl =>
      SimpleIntegrand.martingale_finset_sum _ fun l' hl' => hmartTerm l hl l' hl'
  -- (2) pointwise identification on the good set
  have hid : ∀ ω, (∀ a b : H, IntegrableOn (fun σ => Sg σ ω a b) (Icc 0 T)) → ∀ t,
      inner ℝ (stepT M s n A t ω) u * inner ℝ (stepT M s n A t ω) v -
        ∫ σ in Icc 0 t, stepSg Sg s n A σ ω u v = ψ t ω := by
    intro ω hω t
    have hu : inner ℝ (stepT M s n A t ω) u = ∑ l ∈ Finset.range n, p l t ω :=
      inner_stepT M s n A t ω u
    have hv : inner ℝ (stepT M s n A t ω) v = ∑ l ∈ Finset.range n, q l t ω :=
      inner_stepT M s n A t ω v
    have hint : ∫ σ in Icc 0 t, stepSg Sg s n A σ ω u v = ∑ l ∈ Finset.range n, Kl l t ω := by
      have e : (fun σ => stepSg Sg s n A σ ω u v) = fun σ => ∑ l ∈ Finset.range n,
          (Ioc (s l) (s (l + 1))).indicator (fun σ => Sg σ ω (x l) (y l)) σ := by
        funext σ; exact stepSg_apply' Sg s n A σ ω u v
      rw [e, integral_finset_sum]
      · refine Finset.sum_congr rfl fun l hl => ?_
        have hc := cell_mem hs h0 hsn (Finset.mem_range.1 hl)
        exact cell_integral hc.1 hc.2.1 hc.2.2 (hω (x l) (y l))
      · intro l hl
        have hc := cell_mem hs h0 hsn (Finset.mem_range.1 hl)
        have : Integrable ((Ioc (s l) (s (l + 1))).indicator (fun σ => Sg σ ω (x l) (y l))) volume := by
          rw [integrable_indicator_iff measurableSet_Ioc]
          exact (hω (x l) (y l)).mono_set (fun σ hσ => ⟨hc.1.trans hσ.1.le, hσ.2.trans hc.2.2⟩)
        exact this.integrableOn
    rw [hu, hv, hint, Finset.sum_mul_sum]
    simp only [hψ, hterm, Finset.sum_sub_distrib]
    congr 1
    simp only [Finset.sum_ite_eq, Finset.mem_range]
    exact Finset.sum_congr rfl fun l hl => by simp [Finset.mem_range.1 hl]
  -- (3) measurability
  have hmeasΘ : ∀ t, Measurable (fun ω => inner ℝ (stepT M s n A t ω) u * inner ℝ (stepT M s n A t ω) v -
      ∫ σ in Icc 0 t, stepSg Sg s n A σ ω u v) := by
    intro t
    have hm : ∀ (w : K), Measurable (fun ω => inner ℝ (stepT M s n A t ω) w) := by
      intro w
      have e : (fun ω => inner ℝ (stepT M s n A t ω) w) = fun ω => ∑ l ∈ Finset.range n,
          (inner ℝ (M (clampI (s l) (s (l + 1)) t) ω) (ContinuousLinearMap.adjoint (A l) w) -
            inner ℝ (M (s l) ω) (ContinuousLinearMap.adjoint (A l) w)) := by
        funext ω; exact inner_stepT M s n A t ω w
      rw [e]
      refine Finset.measurable_sum _ fun l _ => ?_
      exact (((hM.martingale _).stronglyAdapted _).measurable.mono (ℱ.le _) le_rfl).sub
        (((hM.martingale _).stronglyAdapted _).measurable.mono (ℱ.le _) le_rfl)
    refine ((hm u).mul (hm v)).sub ?_
    have hmeas := measurable_stepSg_entry hM s n A u v
    have := (hmeas.comp (measurable_swap (α := Ω) (β := ℝ))).stronglyMeasurable
    exact (this.integral_prod_right' (ν := volume.restrict (Icc 0 t))).measurable
  have hae : ∀ t, (fun ω => inner ℝ (stepT M s n A t ω) u * inner ℝ (stepT M s n A t ω) v -
      ∫ σ in Icc 0 t, stepSg Sg s n A σ ω u v) =ᵐ[P] ψ t := by
    intro t
    filter_upwards [hM.sigma_entry_int] with ω hω
    exact hid ω hω t
  have hadapted : Adapted ℱ (fun t ω => inner ℝ (stepT M s n A t ω) u * inner ℝ (stepT M s n A t ω) v -
      ∫ σ in Icc 0 t, stepSg Sg s n A σ ω u v) :=
    hcomp.adapted_of_ae_eq (fun t => (hψm.stronglyAdapted t).measurable) hmeasΘ
      (fun t => (hae t).symm)
  exact martingale_congr_ae hψm hadapted.stronglyAdapted hae

theorem pathint_stepSg (hM : IsHilbertMartingaleWithCovariation P ℱ T M Sg) {s : ℕ → ℝ}
    (hs : Monotone s) {n : ℕ} (A : ℕ → H →L[ℝ] K) {cA : ℝ} (hA : ∀ l < n, ‖A l‖ ≤ cA) :
    ∀ᵐ ω ∂P, IntegrableOn (fun σ => traceNormForm (stepSg Sg s n A σ ω)) (Icc 0 T) ∧
      ∀ σ ∈ Icc 0 T, traceNormForm (stepSg Sg s n A σ ω) ≤ cA ^ 2 * traceNormForm (Sg σ ω) := by
  filter_upwards [hM.sigma_traceClass, hM.sigma_pathint] with ω htc hpath
  have hb : ∀ σ ∈ Icc 0 T, traceNormForm (stepSg Sg s n A σ ω) ≤ cA ^ 2 * traceNormForm (Sg σ ω) :=
    fun σ hσ => traceNormForm_stepSg_le hs hA (htc σ hσ)
  refine ⟨?_, hb⟩
  refine Integrable.mono' (hpath.const_mul (cA ^ 2)) ?_ ?_
  · exact ((measurable_traceNormForm_stepSg hM s n A).comp
      (measurable_id.prodMk measurable_const)).aestronglyMeasurable
  · refine (ae_restrict_iff' measurableSet_Icc).2 (Filter.Eventually.of_forall fun σ hσ => ?_)
    rw [Real.norm_of_nonneg (traceNormForm_nonneg _)]
    exact hb σ hσ

/-- **Step transforms of Hilbert martingales are Hilbert martingales.** -/
theorem isHMC_stepT (hcomp : IsCompleteFiltration P ℱ)
    (hM : IsHilbertMartingaleWithCovariation P ℱ T M Sg) {s : ℕ → ℝ} (hs : Monotone s) {n : ℕ}
    (h0 : 0 ≤ s 0) (hsn : s n ≤ T) (A : ℕ → H →L[ℝ] K) {cA : ℝ} (hA : ∀ l < n, ‖A l‖ ≤ cA) :
    IsHilbertMartingaleWithCovariation P ℱ T (stepT M s n A) (stepSg Sg s n A) where
  martingale := stepT_martingale hM hs A
  zero := Filter.Eventually.of_forall (stepT_zero hs h0 A)
  cont := stepT_cont hM hs h0 hsn A
  sq_int := fun τ _ => stepT_memLp hM hs h0 hsn A τ
  sigma_meas := measurable_stepSg_entry hM s n A
  sigma_adapted := by
    intro σ u v
    have e : (fun ω => stepSg Sg s n A σ ω u v) = fun ω => ∑ l ∈ Finset.range n,
        if σ ∈ Ioc (s l) (s (l + 1)) then
          Sg σ ω (ContinuousLinearMap.adjoint (A l) u) (ContinuousLinearMap.adjoint (A l) v) else 0 :=
      funext fun ω => stepSg_apply Sg s n A σ ω u v
    rw [e]
    refine Finset.measurable_sum _ fun l _ => ?_
    by_cases h : σ ∈ Ioc (s l) (s (l + 1))
    · simp only [h, if_true]
      exact hM.sigma_adapted σ _ _
    · simp only [h, if_false]
      exact measurable_const
  sigma_traceClass := by
    filter_upwards [hM.sigma_traceClass] with ω hω σ hσ
    exact stepSg_isTraceClassCov hs (hω σ hσ)
  sigma_int := by
    have hsm : StronglyMeasurable fun ω => ∫ σ in Icc 0 T, traceNormForm (stepSg Sg s n A σ ω) := by
      have := ((measurable_traceNormForm_stepSg hM s n A).comp
        (measurable_swap (α := Ω) (β := ℝ))).stronglyMeasurable
      exact this.integral_prod_right' (ν := volume.restrict (Icc 0 T))
    refine Integrable.mono' (hM.sigma_int.const_mul (cA ^ 2)) hsm.aestronglyMeasurable ?_
    filter_upwards [pathint_stepSg hM hs A hA, hM.sigma_pathint] with ω hω hpath
    rw [Real.norm_of_nonneg (setIntegral_nonneg measurableSet_Icc fun σ _ => traceNormForm_nonneg _)]
    calc ∫ σ in Icc 0 T, traceNormForm (stepSg Sg s n A σ ω)
        ≤ ∫ σ in Icc 0 T, cA ^ 2 * traceNormForm (Sg σ ω) :=
          setIntegral_mono_on hω.1 (hpath.const_mul _) measurableSet_Icc hω.2
      _ = cA ^ 2 * ∫ σ in Icc 0 T, traceNormForm (Sg σ ω) := integral_const_mul _ _
  sigma_pathint := by
    filter_upwards [pathint_stepSg hM hs A hA] with ω hω using hω.1
  sigma_entry_int := by
    filter_upwards [hM.sigma_entry_int] with ω hω u v
    have e : (fun σ => stepSg Sg s n A σ ω u v) = fun σ => ∑ l ∈ Finset.range n,
        (Ioc (s l) (s (l + 1))).indicator
          (fun σ => Sg σ ω (ContinuousLinearMap.adjoint (A l) u) (ContinuousLinearMap.adjoint (A l) v)) σ :=
      funext fun σ => stepSg_apply' Sg s n A σ ω u v
    rw [e]
    exact integrable_finset_sum _ fun l _ => (hω _ _).indicator measurableSet_Ioc
  covariation := fun u v => stepT_covariation hcomp hM hs h0 hsn A u v

/-- Passing to the null-set augmentation of the filtration preserves `IsHilbertMartingaleWithCovariation`. -/
theorem isHMC_aug (hM : IsHilbertMartingaleWithCovariation P ℱ T M Sg) :
    IsHilbertMartingaleWithCovariation P (augFiltration P ℱ) T M Sg where
  martingale := fun x => martingale_aug (hM.martingale x)
  zero := hM.zero
  cont := hM.cont
  sq_int := hM.sq_int
  sigma_meas := hM.sigma_meas
  sigma_adapted := fun σ x y =>
    (hM.sigma_adapted σ x y).mono (le_sup_left : ℱ σ ≤ ℱ σ ⊔ nullSets P) le_rfl
  sigma_traceClass := hM.sigma_traceClass
  sigma_int := hM.sigma_int
  sigma_pathint := hM.sigma_pathint
  sigma_entry_int := hM.sigma_entry_int
  covariation := fun x y => martingale_aug (hM.covariation x y)

end StepTransform

end Kot
end Uniform
end HRS
