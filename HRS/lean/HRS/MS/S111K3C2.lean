import HRS.MS.S111K3C1

/-!
# S11.1 continuation (S11K3), B03 part C2: measurability of the covariance density of the shifted window

Generators `y1(t,α) = (e_α, 1_{[0,t]}e_α, 0)`, `y2(α) = (0,0,e_α)` span a dense subspace of `𝒦_T` (`k3_span_dense`).
Their pairings with the window feature are `∂_a U^{v,u+t}φ_α` (`v ≤ u+t`), `∂_aφ_α` (`v > u+t`), and `1_{u≤v}∂_aφ_α`.
The functions `v ↦ D_v(h,k)` are a.e. measurable on `[0,u+T]` for generators `h,k` (hypothesis `R2JIntegrandMeas` on the
region where both pairings are propagated, the shifted dyadic approximation elsewhere), hence a Borel set of full measure
on which `D` is entrywise measurable (`k3_exists_good`).
-/

set_option autoImplicit false
noncomputable section

set_option synthInstance.maxHeartbeats 400000
set_option maxSynthPendingDepth 3
set_option maxRecDepth 4000

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S111K3

open HRS HRS.Whole HRS.MS.Go HRS.MS.CovMeas HRS.MS.S111K2 HRS.MS.S111K HRS.MS.S52 HRS.MS.FixEq
open Classical

variable {d : ℕ} {C : WholeCoeff d} {m T u c0 : ℝ} {r : ℕ} {b : MultiIndex d → ℝ} {Pw K1 : ℝ}
  {z z' : ℝ → (Euc d → ℝ) → ℝ}

/-! ### Density of the generators -/

/-- The generators `y1(t,α)`, `y2(α)`. -/
def k3Gen (m T : ℝ) : Set (KSpace d m T) :=
  {w | ∃ t ∈ Icc (0 : ℝ) T, ∃ α : MultiIndex d, w = s52y1 m T t α} ∪
    {w | ∃ α : MultiIndex d, w = s52y2 m T α}

theorem k3_span_dense (hT : 0 ≤ T) :
    (Submodule.span ℝ (k3Gen m T : Set (KSpace d m T))).topologicalClosure = ⊤ := by
  rw [Submodule.topologicalClosure_eq_top_iff, Submodule.eq_bot_iff]
  intro w hw
  rw [Submodule.mem_orthogonal] at hw
  have hw' : ∀ g ∈ k3Gen m T, inner ℝ g w = 0 := fun g hg => hw g (Submodule.subset_span hg)
  have hweq : w = KSpace.mk w.A₀ w.A' w.B := rfl
  have hB : ∀ α, OscDual.coord w.B α = 0 := fun α => by
    have := hw' (s52y2 m T α) (Or.inr ⟨α, rfl⟩)
    rw [real_inner_comm, ← s52_coord_B] at this
    exact this
  have hB0 : w.B = 0 := s101_ellVec_ext fun α => by rw [hB α]; rfl
  have h0 : ∀ α, OscDual.coord w.A₀ α = 0 := fun α => by
    have := hw' (s52y1 m T 0 α) (Or.inl ⟨0, ⟨le_rfl, hT⟩, α, rfl⟩)
    rw [real_inner_comm, s52_inner_y1 hT] at this
    have hz : (∫ τ in Icc (0 : ℝ) 0, OscDual.coord ((w.A' : L2Path d m T) τ) α) = 0 :=
      setIntegral_measure_zero _ (by simp)
    rw [hz, add_zero] at this
    exact this
  have hA0 : w.A₀ = 0 := s101_ellVec_ext fun α => by rw [h0 α]; rfl
  have h4 : ∀ α, ∀ t ∈ Icc (0 : ℝ) T, ∫ τ in Icc (0 : ℝ) t, OscDual.coord ((w.A' : L2Path d m T) τ) α = 0 := by
    intro α t ht
    have := hw' (s52y1 m T t α) (Or.inl ⟨t, ht, α, rfl⟩)
    rw [real_inner_comm, s52_inner_y1 ht.2, h0 α, zero_add] at this
    exact this
  have h5 : ∀ α, ∀ᵐ s ∂(volume.restrict (Icc (0 : ℝ) T)), OscDual.coord ((w.A' : ℝ → OscDual d m) s) α = 0 := by
    intro α
    have hint : IntegrableOn (fun s => OscDual.coord ((w.A' : ℝ → OscDual d m) s) α) (Icc 0 T) volume := by
      have : Integrable (fun s => inner ℝ (s101e m α) ((w.A' : ℝ → OscDual d m) s))
          (volume.restrict (Icc (0 : ℝ) T)) :=
        ((Lp.memLp w.A').integrable one_le_two).const_inner _
      have h' : Integrable (fun s => OscDual.coord ((w.A' : ℝ → OscDual d m) s) α)
          (volume.restrict (Icc (0 : ℝ) T)) := by simpa [s101_inner_e] using this
      exact h'
    exact s101_ae_zero_of_primitive hT hint fun t ht => h4 α t ht
  have h6 : ∀ᵐ s ∂(volume.restrict (Icc (0 : ℝ) T)), (w.A' : ℝ → OscDual d m) s = 0 := by
    filter_upwards [ae_all_iff.2 h5] with s hs
    exact s101_ellVec_ext fun α => by rw [hs α]; rfl
  have hA' : w.A' = 0 := Lp.eq_zero_iff_ae_eq_zero.2 (by filter_upwards [h6] with s hs; simpa using hs)
  rw [hweq, hA0, hA', hB0]
  rfl

theorem k3_span_dense' (hT : 0 ≤ T) :
    Dense (Submodule.span ℝ (k3Gen m T : Set (KSpace d m T)) : Set (KSpace d m T)) := by
  rw [dense_iff_closure_eq, ← Submodule.topologicalClosure_coe, k3_span_dense hT]
  rfl

/-! ### Pairings of the window feature with the generators -/

/-- The pairing function of `y1(t,α)`: `U^{v,u+t}φ_α` if `v ≤ u+t`, `φ_α` otherwise. -/
def k3Wf (C : WholeCoeff d) (m u v t : ℝ) (α : MultiIndex d) : Euc d → ℝ :=
  if v ≤ u + t then propagatorW C v (u + t) (oscTestFun m α) else oscTestFun m α

/-- The pairing function of `y2(α)`: `1_{u ≤ v} φ_α`. -/
def k3W2 (m u v : ℝ) (α : MultiIndex d) : Euc d → ℝ := if u ≤ v then oscTestFun m α else 0

lemma gradComp_zero' (a : Fin d) (x : Euc d) : gradComp a (0 : Euc d → ℝ) x = 0 := by
  simp [gradComp, gradient]

lemma k3_pair1 (A : K3Adm C m T u c0 r b Pw K1 z) {v : ℝ} (hv : v ∈ Icc (0 : ℝ) (u + T)) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) T) (α : MultiIndex d) (i : Fin d) (x : Euc d) :
    inner ℝ (k3G C m T u v i x) (s52y1 m T t α) = gradComp i (k3Wf C m u v t α) x := by
  unfold k3G k3Wf
  rw [k3_pair_y1 A.hW A.hbS A.hc0 A.hu hv.1 hv.2 ht i x α]
  by_cases h : v ≤ u + t <;> simp [h]

lemma k3_pair2 (A : K3Adm C m T u c0 r b Pw K1 z) {v : ℝ} (hv : v ∈ Icc (0 : ℝ) (u + T))
    (α : MultiIndex d) (i : Fin d) (x : Euc d) :
    inner ℝ (k3G C m T u v i x) (s52y2 m T α) = gradComp i (k3W2 m u v α) x := by
  unfold k3G k3W2
  rw [k3_pair_y2 A.hW A.hbS A.hc0 hv.1 i x α]
  by_cases h : u ≤ v
  · simp [h]
  · simp [h, gradComp_zero']

lemma k3_ip_grad (f g : Euc d → ℝ) (x : Euc d) :
    ∑ i : Fin d, gradComp i f x * gradComp i g x = inner ℝ (gradient f x) (gradient g x) := by
  rw [PiLp.inner_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [gradComp, RCLike.inner_apply, conj_trivial]
  ring

lemma k3_D_pairs (A : K3Adm C m T u c0 r b Pw K1 z) {v : ℝ} (hv : v ∈ Icc (0 : ℝ) (u + T))
    {h k : KSpace d m T} {f g : Euc d → ℝ}
    (hh : ∀ i x, inner ℝ (k3G C m T u v i x) h = gradComp i f x)
    (hk : ∀ i x, inner ℝ (k3G C m T u v i x) k = gradComp i g x) :
    k3D C m T u z v h k = 2 * C.ν * z v (fun x => inner ℝ (gradient f x) (gradient g x)) := by
  rw [k3_D_apply A hv, k3_Fg_eq (G := k3G C m T u v) (h := h) (k := k) (f := fun i x => gradComp i f x)
    (f' := fun i x => gradComp i g x) hh hk]
  congr 2
  funext x
  exact k3_ip_grad f g x

lemma k3_D_congr_right (A : K3Adm C m T u c0 r b Pw K1 z) {v : ℝ} (hv : v ∈ Icc (0 : ℝ) (u + T))
    (h : KSpace d m T) {k k' : KSpace d m T}
    (hh : ∀ i x, inner ℝ (k3G C m T u v i x) k = inner ℝ (k3G C m T u v i x) k') :
    k3D C m T u z v h k = k3D C m T u z v h k' := by
  rw [k3_D_symm A hv h k, k3_D_symm A hv h k']
  exact k3_D_congr_left A hv hh h

/-- On `v > u + t` the pairing of `y1(t,α)` equals that of `y1(v-u,α)`. -/
lemma k3_pair1_diag (A : K3Adm C m T u c0 r b Pw K1 z) {v : ℝ} (hv : v ∈ Icc u (u + T)) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) T) (hvt : u + t < v) (α : MultiIndex d) (i : Fin d) (x : Euc d) :
    inner ℝ (k3G C m T u v i x) (s52y1 m T t α) = inner ℝ (k3G C m T u v i x) (s52y1 m T (v - u) α) := by
  have hv' : v ∈ Icc (0 : ℝ) (u + T) := ⟨by linarith [hv.1, A.hu], hv.2⟩
  have hvu : v - u ∈ Icc (0 : ℝ) T := ⟨by linarith [hv.1], by linarith [hv.2]⟩
  rw [k3_pair1 A hv' ht α i x, k3_pair1 A hv' hvu α i x]
  unfold k3Wf
  have h1 : ¬ v ≤ u + t := not_le.2 hvt
  have h2 : v ≤ u + (v - u) := by linarith
  rw [if_neg h1, if_pos h2]
  have : propagatorW C v (u + (v - u)) (oscTestFun m α) = oscTestFun m α := by
    have e : u + (v - u) = v := by ring
    rw [e]
    exact k3_prop_terminal A.hW α (hv'.1)
  rw [this]

/-- On `v ≥ u` the pairing of `y2(α)` equals that of `y1(v-u,α)`. -/
lemma k3_pair2_diag (A : K3Adm C m T u c0 r b Pw K1 z) {v : ℝ} (hv : v ∈ Icc u (u + T))
    (α : MultiIndex d) (i : Fin d) (x : Euc d) :
    inner ℝ (k3G C m T u v i x) (s52y2 m T α) = inner ℝ (k3G C m T u v i x) (s52y1 m T (v - u) α) := by
  have hv' : v ∈ Icc (0 : ℝ) (u + T) := ⟨by linarith [hv.1, A.hu], hv.2⟩
  have hvu : v - u ∈ Icc (0 : ℝ) T := ⟨by linarith [hv.1], by linarith [hv.2]⟩
  rw [k3_pair2 A hv' α i x, k3_pair1 A hv' hvu α i x]
  unfold k3Wf k3W2
  have h2 : v ≤ u + (v - u) := by linarith
  rw [if_pos hv.1, if_pos h2]
  have : propagatorW C v (u + (v - u)) (oscTestFun m α) = oscTestFun m α := by
    have e : u + (v - u) = v := by ring
    rw [e]
    exact k3_prop_terminal A.hW α (hv'.1)
  rw [this]

/-- For `v < u` the pairing of `y2(α)` vanishes. -/
lemma k3_pair2_zero (A : K3Adm C m T u c0 r b Pw K1 z) {v : ℝ} (hv : v ∈ Icc (0 : ℝ) (u + T)) (hvu : v < u)
    (α : MultiIndex d) (i : Fin d) (x : Euc d) :
    inner ℝ (k3G C m T u v i x) (s52y2 m T α) = 0 := by
  rw [k3_pair2 A hv α i x]
  unfold k3W2
  rw [if_neg (not_le.2 hvu), gradComp_zero']

/-! ### Measurability -/

lemma k3_y1_tendsto {τ : ℝ} (hτ : 0 ≤ τ) (hτT : τ < T) (α : MultiIndex d) :
    Tendsto (fun n => s52y1 m T (s101tn T n τ) α) atTop (𝓝 (s52y1 m T τ α)) := by
  have hInd := s101_Ind_tendsto (T := T) (s101e m α) hτ (fun n => (s101tn_lt hτ hτT n).le)
    (s101tn_tendsto hτ hτT)
  have hc : Continuous fun a' : L2Path d m T => (s55fE (d := d) m T).symm (s101e m α, (a', 0)) :=
    (s55fE (d := d) m T).symm.continuous.comp (continuous_const.prodMk (continuous_id.prodMk continuous_const))
  exact (hc.tendsto _).comp hInd

/-- Region where both pairings are propagated: `R2JIntegrandMeas`. -/
theorem k3_aem_direct (A : K3Adm C m T u c0 r b Pw K1 z) {t t' : ℝ} (ht : t ∈ Icc (0 : ℝ) T)
    (ht' : t' ∈ Icc (0 : ℝ) T) (α β : MultiIndex d) {E : Set ℝ} (hE : MeasurableSet E)
    (hsub : ∀ v ∈ E, v ∈ Icc (0 : ℝ) (u + T) ∧ v ≤ u + t ∧ v ≤ u + t') :
    AEMeasurable (fun v => k3D C m T u z v (s52y1 m T t α) (s52y1 m T t' β)) (volume.restrict E) := by
  have hta : u + t ∈ Icc (0 : ℝ) (u + T) := ⟨by linarith [ht.1, A.hu], by linarith [ht.2]⟩
  have htb : u + t' ∈ Icc (0 : ℝ) (u + T) := ⟨by linarith [ht'.1, A.hu], by linarith [ht'.2]⟩
  have h := A.hmeas (u + t) (u + t') (oscTestFun m α) (oscTestFun m β) (s101_isCombo_single m α)
    (s101_isCombo_single m β) hta htb
  have h2 := h.const_mul (2 * C.ν)
  have hE' : E ⊆ Icc 0 (min (u + t) (u + t')) := fun v hv =>
    ⟨(hsub v hv).1.1, le_min (hsub v hv).2.1 (hsub v hv).2.2⟩
  refine (h2.mono_measure (Measure.restrict_mono hE' le_rfl)).congr ?_
  refine (ae_restrict_iff' hE).2 (Eventually.of_forall fun v hv => ?_)
  obtain ⟨hv1, hv2, hv3⟩ := hsub v hv
  symm
  refine k3_D_pairs A hv1 (f := propagatorW C v (u + t) (oscTestFun m α))
    (g := propagatorW C v (u + t') (oscTestFun m β)) (fun i x => ?_) (fun i x => ?_)
  · rw [k3_pair1 A hv1 ht α i x]; unfold k3Wf; rw [if_pos hv2]
  · rw [k3_pair1 A hv1 ht' β i x]; unfold k3Wf; rw [if_pos hv3]

theorem k3_aem_dd (A : K3Adm C m T u c0 r b Pw K1 z) (α β : MultiIndex d) {E : Set ℝ}
    (hE : MeasurableSet E) (hsub : E ⊆ Icc u (u + T)) :
    AEMeasurable (fun v => k3D C m T u z v (s52y1 m T (v - u) α) (s52y1 m T (v - u) β))
      (volume.restrict E) := by
  refine k3_aem_diag A.hT u hE hsub (k3D C m T u z) (fun t => s52y1 m T t α) (fun t => s52y1 m T t β)
    (fun v => s52y1 m T (v - u) α) (fun v => s52y1 m T (v - u) β) ?_ ?_
  · intro t ht
    refine k3_aem_direct A ht ht α β (hE.inter measurableSet_Iio) ?_
    intro v hv
    have hv2 : v < u + t := hv.2
    exact ⟨⟨by linarith [(hsub hv.1).1, A.hu], by linarith [ht.2]⟩, hv2.le, hv2.le⟩
  · intro v hv hvT
    have hv0 : 0 ≤ v - u := by linarith [(hsub hv).1]
    exact ⟨k3_y1_tendsto hv0 hvT α, k3_y1_tendsto hv0 hvT β⟩

theorem k3_aem_sd (A : K3Adm C m T u c0 r b Pw K1 z) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) T) (α β : MultiIndex d)
    {E : Set ℝ} (hE : MeasurableSet E) (hsub : E ⊆ Icc u (u + s)) :
    AEMeasurable (fun v => k3D C m T u z v (s52y1 m T s α) (s52y1 m T (v - u) β)) (volume.restrict E) := by
  have hsub' : E ⊆ Icc u (u + T) := hsub.trans (Icc_subset_Icc_right (by linarith [hs.2]))
  refine k3_aem_diag A.hT u hE hsub' (k3D C m T u z) (fun _ => s52y1 m T s α) (fun t => s52y1 m T t β)
    (fun _ => s52y1 m T s α) (fun v => s52y1 m T (v - u) β) ?_ ?_
  · intro t ht
    refine k3_aem_direct A hs ht α β (hE.inter measurableSet_Iio) ?_
    intro v hv
    have hv2 : v < u + t := hv.2
    exact ⟨⟨by linarith [(hsub hv.1).1, A.hu], by linarith [hs.2, (hsub hv.1).2]⟩, (hsub hv.1).2, hv2.le⟩
  · intro v hv hvT
    have hv0 : 0 ≤ v - u := by linarith [(hsub hv).1]
    exact ⟨tendsto_const_nhds, k3_y1_tendsto hv0 hvT β⟩

lemma k3_mem_of_Icc {v : ℝ} (hu : 0 ≤ u) (hv : v ∈ Icc u (u + T)) : v ∈ Icc (0 : ℝ) (u + T) :=
  ⟨by linarith [hv.1], hv.2⟩

/-- Pair of two `y1` generators, ordered `s ≤ s'`. -/
theorem k3_aem_y1y1_le (A : K3Adm C m T u c0 r b Pw K1 z) {s s' : ℝ} (hs : s ∈ Icc (0 : ℝ) T)
    (hs' : s' ∈ Icc (0 : ℝ) T) (hss : s ≤ s') (α β : MultiIndex d) :
    AEMeasurable (fun v => k3D C m T u z v (s52y1 m T s α) (s52y1 m T s' β))
      (volume.restrict (Icc 0 (u + T))) := by
  have hunion : Icc (0 : ℝ) (u + T) = Icc 0 (u + s) ∪ Ioc (u + s) (u + s') ∪ Ioc (u + s') (u + T) := by
    ext v
    simp only [mem_Icc, mem_union, mem_Ioc]
    constructor
    · rintro ⟨h1, h2⟩
      by_cases a1 : v ≤ u + s
      · exact Or.inl (Or.inl ⟨h1, a1⟩)
      · by_cases a2 : v ≤ u + s'
        · exact Or.inl (Or.inr ⟨not_le.1 a1, a2⟩)
        · exact Or.inr ⟨not_le.1 a2, h2⟩
    · rintro ((h | h) | h)
      · exact ⟨h.1, by linarith [h.2, hs.2]⟩
      · exact ⟨by linarith [h.1, hs.1, A.hu], by linarith [h.2, hs'.2]⟩
      · exact ⟨by linarith [h.1, hs'.1, A.hu], h.2⟩
  rw [hunion, aemeasurable_union_iff, aemeasurable_union_iff]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · refine k3_aem_direct A hs hs' α β measurableSet_Icc fun v hv => ⟨⟨hv.1, by linarith [hv.2, hs.2]⟩, hv.2,
      hv.2.trans (by linarith)⟩
  · -- `u + s < v ≤ u + s'`
    have hsub : Ioc (u + s) (u + s') ⊆ Icc u (u + s') := fun v hv => ⟨by linarith [hv.1, hs.1], hv.2⟩
    have h1 := k3_aem_sd A hs' β α measurableSet_Ioc hsub
    have h2 : AEMeasurable (fun v => k3D C m T u z v (s52y1 m T (v - u) α) (s52y1 m T s' β))
        (volume.restrict (Ioc (u + s) (u + s'))) := by
      refine h1.congr ?_
      refine (ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun v hv => ?_)
      have hv' : v ∈ Icc (0 : ℝ) (u + T) := ⟨by linarith [hv.1, hs.1, A.hu], by linarith [hv.2, hs'.2]⟩
      exact k3_D_symm A hv' _ _
    refine h2.congr ?_
    refine (ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun v hv => ?_)
    have hvI : v ∈ Icc u (u + T) := ⟨by linarith [hv.1, hs.1], by linarith [hv.2, hs'.2]⟩
    have hv' := k3_mem_of_Icc A.hu hvI
    exact (k3_D_congr_left A hv' (fun i x => k3_pair1_diag A hvI hs hv.1 α i x) _).symm
  · -- `v > u + s'`
    have hsub : Ioc (u + s') (u + T) ⊆ Icc u (u + T) := fun v hv => ⟨by linarith [hv.1, hs'.1], hv.2⟩
    refine (k3_aem_dd A α β measurableSet_Ioc hsub).congr ?_
    refine (ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun v hv => ?_)
    have hvI : v ∈ Icc u (u + T) := hsub hv
    have hv' := k3_mem_of_Icc A.hu hvI
    have e1 := k3_D_congr_left A hv' (fun i x => k3_pair1_diag A hvI hs (lt_of_le_of_lt (by linarith) hv.1) α i x)
      (s52y1 m T s' β)
    have e2 := k3_D_congr_right A hv' (s52y1 m T (v - u) α) (fun i x => k3_pair1_diag A hvI hs' hv.1 β i x)
    exact (e1.trans e2).symm

theorem k3_aem_y1y1 (A : K3Adm C m T u c0 r b Pw K1 z) {s s' : ℝ} (hs : s ∈ Icc (0 : ℝ) T)
    (hs' : s' ∈ Icc (0 : ℝ) T) (α β : MultiIndex d) :
    AEMeasurable (fun v => k3D C m T u z v (s52y1 m T s α) (s52y1 m T s' β))
      (volume.restrict (Icc 0 (u + T))) := by
  rcases le_total s s' with h | h
  · exact k3_aem_y1y1_le A hs hs' h α β
  · refine (k3_aem_y1y1_le A hs' hs h β α).congr ?_
    refine (ae_restrict_iff' measurableSet_Icc).2 (Eventually.of_forall fun v hv => ?_)
    exact k3_D_symm A hv _ _

theorem k3_aem_y1y2 (A : K3Adm C m T u c0 r b Pw K1 z) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) T) (α β : MultiIndex d) :
    AEMeasurable (fun v => k3D C m T u z v (s52y1 m T s α) (s52y2 m T β)) (volume.restrict (Icc 0 (u + T))) := by
  have hunion : Icc (0 : ℝ) (u + T) = Ico 0 u ∪ Icc u (u + s) ∪ Ioc (u + s) (u + T) := by
    ext v
    simp only [mem_Icc, mem_union, mem_Ioc, mem_Ico]
    constructor
    · rintro ⟨h1, h2⟩
      by_cases a1 : v < u
      · exact Or.inl (Or.inl ⟨h1, a1⟩)
      · by_cases a2 : v ≤ u + s
        · exact Or.inl (Or.inr ⟨not_lt.1 a1, a2⟩)
        · exact Or.inr ⟨not_le.1 a2, h2⟩
    · rintro ((h | h) | h)
      · exact ⟨h.1, by linarith [h.2, A.hT]⟩
      · exact ⟨by linarith [h.1, A.hu], by linarith [h.2, hs.2]⟩
      · exact ⟨by linarith [h.1, hs.1, A.hu], h.2⟩
  rw [hunion, aemeasurable_union_iff, aemeasurable_union_iff]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · -- `v < u`: zero
    refine (aemeasurable_const (b := (0 : ℝ))).congr ?_
    refine (ae_restrict_iff' measurableSet_Ico).2 (Eventually.of_forall fun v hv => ?_)
    have hv' : v ∈ Icc (0 : ℝ) (u + T) := ⟨hv.1, by linarith [hv.2, A.hT]⟩
    symm
    beta_reduce
    rw [k3_D_symm A hv' _ _]
    exact k3_D_zero_left A hv' (fun i x => k3_pair2_zero A hv' hv.2 β i x) _
  · have hsub : Icc u (u + s) ⊆ Icc u (u + s) := subset_rfl
    refine (k3_aem_sd A hs α β measurableSet_Icc hsub).congr ?_
    refine (ae_restrict_iff' measurableSet_Icc).2 (Eventually.of_forall fun v hv => ?_)
    have hvI : v ∈ Icc u (u + T) := ⟨hv.1, by linarith [hv.2, hs.2]⟩
    have hv' := k3_mem_of_Icc A.hu hvI
    exact (k3_D_congr_right A hv' (s52y1 m T s α) (fun i x => k3_pair2_diag A hvI β i x)).symm
  · have hsub : Ioc (u + s) (u + T) ⊆ Icc u (u + T) := fun v hv => ⟨by linarith [hv.1, hs.1], hv.2⟩
    refine (k3_aem_dd A α β measurableSet_Ioc hsub).congr ?_
    refine (ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun v hv => ?_)
    have hvI : v ∈ Icc u (u + T) := hsub hv
    have hv' := k3_mem_of_Icc A.hu hvI
    have e1 := k3_D_congr_left A hv' (fun i x => k3_pair1_diag A hvI hs hv.1 α i x) (s52y2 m T β)
    have e2 := k3_D_congr_right A hv' (s52y1 m T (v - u) α) (fun i x => k3_pair2_diag A hvI β i x)
    exact (e1.trans e2).symm

theorem k3_aem_y2y2 (A : K3Adm C m T u c0 r b Pw K1 z) (α β : MultiIndex d) :
    AEMeasurable (fun v => k3D C m T u z v (s52y2 m T α) (s52y2 m T β)) (volume.restrict (Icc 0 (u + T))) := by
  have hunion : Icc (0 : ℝ) (u + T) = Ico 0 u ∪ Icc u (u + T) := by
    ext v
    simp only [mem_Icc, mem_union, mem_Ico]
    constructor
    · rintro ⟨h1, h2⟩
      by_cases a1 : v < u
      · exact Or.inl ⟨h1, a1⟩
      · exact Or.inr ⟨not_lt.1 a1, h2⟩
    · rintro (h | h)
      · exact ⟨h.1, by linarith [h.2, A.hT]⟩
      · exact ⟨by linarith [h.1, A.hu], h.2⟩
  rw [hunion, aemeasurable_union_iff]
  refine ⟨?_, ?_⟩
  · refine (aemeasurable_const (b := (0 : ℝ))).congr ?_
    refine (ae_restrict_iff' measurableSet_Ico).2 (Eventually.of_forall fun v hv => ?_)
    have hv' : v ∈ Icc (0 : ℝ) (u + T) := ⟨hv.1, by linarith [hv.2, A.hT]⟩
    symm
    beta_reduce
    exact k3_D_zero_left A hv' (fun i x => k3_pair2_zero A hv' hv.2 α i x) _
  · refine (k3_aem_dd A α β measurableSet_Icc subset_rfl).congr ?_
    refine (ae_restrict_iff' measurableSet_Icc).2 (Eventually.of_forall fun v hv => ?_)
    have hv' := k3_mem_of_Icc A.hu hv
    have e1 := k3_D_congr_left A hv' (fun i x => k3_pair2_diag A hv α i x) (s52y2 m T β)
    have e2 := k3_D_congr_right A hv' (s52y1 m T (v - u) α) (fun i x => k3_pair2_diag A hv β i x)
    exact (e1.trans e2).symm

theorem k3_aem_gen (A : K3Adm C m T u c0 r b Pw K1 z) {h k : KSpace d m T} (hh : h ∈ k3Gen m T)
    (hk : k ∈ k3Gen m T) :
    AEMeasurable (fun v => k3D C m T u z v h k) (volume.restrict (Icc 0 (u + T))) := by
  rcases hh with ⟨s, hs, α, rfl⟩ | ⟨α, rfl⟩ <;> rcases hk with ⟨s', hs', β, rfl⟩ | ⟨β, rfl⟩
  · exact k3_aem_y1y1 A hs hs' α β
  · exact k3_aem_y1y2 A hs α β
  · refine (k3_aem_y1y2 A hs' β α).congr ?_
    refine (ae_restrict_iff' measurableSet_Icc).2 (Eventually.of_forall fun v hv => ?_)
    exact k3_D_symm A hv _ _
  · exact k3_aem_y2y2 A α β

theorem k3_exists_good_D (A : K3Adm C m T u c0 r b Pw K1 z) :
    ∃ G : Set ℝ, MeasurableSet G ∧ G ⊆ Icc 0 (u + T) ∧ volume (Icc 0 (u + T) \ G) = 0 ∧
      ∀ h k : KSpace d m T, Measurable (fun v => if v ∈ G then k3D C m T u z v h k else 0) :=
  k3_exists_good (k3D C m T u z) measurableSet_Icc (k3_span_dense' A.hT) fun h hh k hk => k3_aem_gen A hh hk

end HRS.MS.S111K3
