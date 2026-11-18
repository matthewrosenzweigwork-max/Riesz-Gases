import HRS.MS.S81sTransport
import HRS.MS.S81sGauss
import HRS.MS.S81sFiniteNoise
import HRS.MS.S81sLinear
import HRS.MS.S81sSetup
import HRS.MS.S81sCov
import HRS.MS.GenPathAux43
import HRS.MS.OrbIdAux2
import HRS.MS.S81pAssemble
import HRS.MS.SuppU9
import HRS.Uniform.Comp28W1

/-!
# S8.1 (worker S81S): the RECENT block

Namespace `HRS.Whole.S81S`, prefix `s81s_`.

Let `(Ω₁, Q₁)` carry a canonical realization with a filtration `ℱ₁` for which `W` is cylindrical Brownian and `X` is a filtered solution
(`hF`), let `h ≥ 0` be the split time and `H = b + T`.  The shifted data `(X_h, W_{h+·} - W_h, X_{h+·})` on `ℱ₁(h + ·)` form again a
canonical realization (`s81b_isCanonical_shift`), to which the (re-exported) feature producer `s81s_finite_noise` applies at the FIXED
horizon `H`.  `s81s_recent_block` extracts from it the recent window `Rp(t) = (𝒯 M)(b+t)` (`M` the Hilbert Itô integral of the
shifted feature integrand), the Gaussian window `G2(t) = (𝒯 G)(b+t)`, and proves:
* both are measurable, a.s. continuous processes with values in `B_m`;
* the finite-dimensional laws of `G2` are centered Gaussian with the (positive semidefinite) noise covariance `noiseCovW (critCoeff) β⁻¹`
  at times `b + t`;
* `G2` is independent of `ℱ₁(h)` (pulled back to the extension), as a process;
* `‖Rp - G2‖_{L²(𝒳_T)} ≤ C N^{-1/2}`, with `C` independent of `h`, `N`, the realization (it depends on `H = b+T` only).
-/

set_option autoImplicit false
set_option maxRecDepth 4000

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators
open HRS HRS.Whole HRS.Whole.S81P HRS.MS.GenPath

namespace HRS.Whole.S81S

section Generic

variable {d : ℕ}

/-- Existence of the Hilbert Itô integral of a Hilbert-Schmidt integrand (on every horizon). -/
theorem s81s_exists_hito {Ω : Type} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    {ℱ : Filtration ℝ mΩ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H] {κ : Type*} [Countable κ]
    {W : ℝ≥0 → Ω → κ → ℝ} (hW : IsCylindricalBrownian P ℱ W) {Φ : ℝ → Ω → κ → H}
    (hΦ : ∀ T : ℝ, IsHSIntegrand P ℱ T Φ) : ∃ M, IsHilbertItoIntegral P ℱ W Φ M := by
  obtain ⟨Mart, hc, had, hz, hJ⟩ := HRS.GF.gfb3_exists_hilbert_version hW hΦ
  refine ⟨Mart, ⟨hc, had, hz, ?_⟩⟩
  intro τ hτ x
  obtain ⟨J, hIJ, hae⟩ := hJ x
  refine (hIJ.approx τ hτ).congr fun s => ?_
  refine lintegral_congr_ae ?_
  filter_upwards [hae τ hτ] with ω h
  rw [h]
  rfl

/-- A map into `B_m` with measurable coordinates is measurable. -/
theorem s81s_measurable_of_coord {α : Type*} {mα : MeasurableSpace α} {m : ℝ} (F : α → OscDual d m)
    (hc : ∀ k, Measurable fun a => OscDual.coord (F a) k) : Measurable F := by
  have hlim : ∀ X : α, Tendsto
      (fun s : Finset (MultiIndex d) => (∑ k ∈ s,
        (show OscDual d m from lp.single (E := fun _ : MultiIndex d => ℝ) 2 k (OscDual.coord (F X) k))))
      atTop (𝓝 (F X)) := by
    intro X
    exact lp.hasSum_single (p := 2) (by simp) (show lp (fun _ : MultiIndex d => ℝ) 2 from F X)
  refine measurable_of_tendsto_metrizable' (atTop : Filter (Finset (MultiIndex d)))
    (f := fun (s : Finset (MultiIndex d)) (X : α) =>
      (∑ k ∈ s, (show OscDual d m from lp.single (E := fun _ : MultiIndex d => ℝ) 2 k
        (OscDual.coord (F X) k)))) (fun s => ?_) (tendsto_pi_nhds.2 hlim)
  refine Finset.measurable_sum _ fun k _ => ?_
  have hcont : Continuous (fun a : ℝ => (show OscDual d m from
      lp.single (E := fun _ : MultiIndex d => ℝ) 2 k a)) :=
    (lp.isometry_single (E := fun _ : MultiIndex d => ℝ) (p := 2) k).continuous
  exact hcont.measurable.comp (hc k)

/-- The process-level independence from `𝒢` follows from the independence of the finite families of coordinates. -/
theorem s81s_proc_indep {Ω : Type*} (𝒢 : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω] {Q : Measure Ω}
    [IsProbabilityMeasure Q] (h𝒢 : 𝒢 ≤ mΩ) {m : ℝ} (Y : ℝ → Ω → OscDual d m)
    (hY : ∀ t, Measurable (Y t))
    (hfdd : ∀ F : Finset (ℝ × MultiIndex d), Indep 𝒢
      (⨆ i ∈ F, MeasurableSpace.comap (fun ζ => OscDual.coord (Y i.1 ζ) i.2) inferInstance) Q) :
    Indep 𝒢 (⨆ t : ℝ, MeasurableSpace.comap (Y t) inferInstance) Q := by
  set mm : Finset (ℝ × MultiIndex d) → MeasurableSpace Ω := fun F =>
    ⨆ i ∈ F, MeasurableSpace.comap (fun ζ => OscDual.coord (Y i.1 ζ) i.2) inferInstance with hmm
  have hle : ∀ F, mm F ≤ mΩ := fun F =>
    iSup₂_le fun i _ => (((s56_continuous_coord m i.2).measurable.comp (hY i.1)).comap_le)
  have hdir : Directed (· ≤ ·) mm := by
    refine directed_of_isDirected_le fun F F' hFF' => ?_
    exact iSup₂_le fun i hi => le_iSup₂_of_le i (hFF' hi) le_rfl
  have h1 : Indep (⨆ F, mm F) 𝒢 Q :=
    indep_iSup_of_directed_le (fun F => (hfdd F).symm) hle h𝒢 hdir
  have h2 : (⨆ t : ℝ, MeasurableSpace.comap (Y t) inferInstance) ≤ ⨆ F, mm F := by
    refine iSup_le fun t => ?_
    have hmeas : @Measurable Ω (OscDual d m) (⨆ F, mm F) _ (Y t) := by
      refine @s81s_measurable_of_coord d Ω (⨆ F, mm F) m (Y t) fun k => ?_
      have hh : MeasurableSpace.comap (fun ζ => OscDual.coord (Y t ζ) k) inferInstance ≤ ⨆ F, mm F :=
        le_iSup_of_le ({(t, k)} : Finset (ℝ × MultiIndex d))
          (le_iSup₂_of_le (t, k) (Finset.mem_singleton_self _) le_rfl)
      exact @Measurable.of_comap_le Ω ℝ (⨆ F, mm F) _ _ hh
    exact hmeas.comap_le
  exact (indep_of_indep_of_le_left h1 h2).symm


/-- The reconstruction of a continuous `𝒦`-process, read on the window `[b, b+T]`, is a measurable a.s. continuous process
(clamped outside `[0,T]`). -/
theorem s81s_recon_proc {m H b T : ℝ} (hb : 0 ≤ b) (hT : 0 ≤ T) (hbT : b + T ≤ H) {Ω : Type*}
    [MeasurableSpace Ω] {Q : Measure Ω} (M : ℝ → Ω → KSpace d m H) (hMm : ∀ τ, Measurable (M τ))
    (hMc : ∀ᵐ ζ ∂Q, ContinuousOn (fun τ => M τ ζ) (Set.Icc 0 H)) :
    S81PProc Q T (fun t ζ => reconstructPath m H M ζ (b + max 0 (min t T))) := by
  have hH : 0 ≤ H := by linarith
  refine ⟨fun t => ?_, ?_⟩
  · unfold reconstructPath
    exact (((s56_evalA_cont hH _).measurable.comp (hMm H)).sub
      (HRS.MS.U9.u9_continuous_B.measurable.comp (hMm H))).add
      (HRS.MS.U9.u9_continuous_B.measurable.comp (hMm _))
  · filter_upwards [hMc] with ζ hc
    have h1 := HRS.MS.U9.u9_continuous_recon hH M ζ hc
    have hφ : ∀ t : ℝ, b + max 0 (min t T) ∈ Set.Icc (0 : ℝ) H := fun t =>
      ⟨by have := le_max_left (0 : ℝ) (min t T); linarith,
        by have : max 0 (min t T) ≤ T := max_le hT (min_le_right _ _); linarith⟩
    have hcont : Continuous fun t : ℝ => (⟨b + max 0 (min t T), hφ t⟩ : Set.Icc (0 : ℝ) H) :=
      Continuous.subtype_mk (continuous_const.add (continuous_const.max (continuous_id.min continuous_const))) _
    exact (h1.comp hcont).continuousOn

/-- The sup norm of a continuous window is bounded by the supremum of the pointwise norms. -/
theorem s81s_window_enorm_le {m T : ℝ} {Ω : Type*} (Y : ℝ → Ω → OscDual d m) (ζ : Ω)
    (hc : ContinuousOn (fun t => Y t ζ) (Set.Icc 0 T)) :
    ‖processWindow m T 0 Y ζ‖ₑ ≤ ⨆ t : Set.Icc (0 : ℝ) T, ‖Y t ζ‖ₑ := by
  set R : ℝ≥0∞ := ⨆ t : Set.Icc (0 : ℝ) T, ‖Y t ζ‖ₑ with hR
  rcases eq_or_ne R ⊤ with h | h
  · rw [h]; exact le_top
  have hcw : Continuous fun t : Set.Icc (0 : ℝ) T => Y (0 + (t : ℝ)) ζ := by
    simp only [zero_add]
    exact continuousOn_iff_continuous_restrict.1 hc
  have hw : processWindow m T 0 Y ζ =
      (⟨fun t : Set.Icc (0 : ℝ) T => Y (0 + (t : ℝ)) ζ, hcw⟩ : C(Set.Icc (0 : ℝ) T, OscDual d m)) := by
    unfold processWindow windowPathOf
    exact dif_pos hcw
  have hnorm : ‖processWindow m T 0 Y ζ‖ ≤ R.toReal := by
    rw [hw]
    refine (ContinuousMap.norm_le _ ENNReal.toReal_nonneg).2 fun t => ?_
    have : ‖Y (0 + (t : ℝ)) ζ‖ₑ ≤ R := by
      simpa using le_iSup (fun t : Set.Icc (0 : ℝ) T => ‖Y t ζ‖ₑ) t
    have h2 := ENNReal.toReal_mono h this
    simpa [toReal_enorm] using h2
  calc ‖processWindow m T 0 Y ζ‖ₑ = ENNReal.ofReal ‖processWindow m T 0 Y ζ‖ := (ofReal_norm _).symm
    _ ≤ ENNReal.ofReal R.toReal := ENNReal.ofReal_le_ofReal hnorm
    _ = R := ENNReal.ofReal_toReal h

/-- `L²` cost of the difference of two windows from a pointwise bound of the difference process. -/
theorem s81s_L2_window_le {m T : ℝ} {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω}
    {Rp G2 : ℝ → Ω → OscDual d m} (hR : S81PProc Q T Rp) (hG : S81PProc Q T G2) (A : Ω → ℝ≥0∞)
    (hA : ∀ᵐ ζ ∂Q, ∀ t ∈ Set.Icc (0 : ℝ) T, ‖Rp t ζ - G2 t ζ‖ₑ ≤ A ζ) :
    s81p_L2 Q (fun ζ => processWindow m T 0 Rp ζ - processWindow m T 0 G2 ζ) ≤
      (∫⁻ ζ, A ζ ^ 2 ∂Q) ^ (1 / 2 : ℝ) := by
  rw [s81p_L2_eq]
  refine ENNReal.rpow_le_rpow (lintegral_mono_ae ?_) (by norm_num)
  filter_upwards [hA, hR.2, hG.2] with ζ hA' hRc hGc
  have e : processWindow m T 0 Rp ζ - processWindow m T 0 G2 ζ =
      processWindow m T 0 (fun t ζ => Rp t ζ - G2 t ζ) ζ := by
    unfold processWindow
    exact (s81p_win_sub hRc hGc).symm
  rw [e]
  have h1 := s81s_window_enorm_le (m := m) (T := T) (fun t ζ => Rp t ζ - G2 t ζ) ζ (hRc.sub hGc)
  have h2 : (⨆ t : Set.Icc (0 : ℝ) T, ‖Rp t ζ - G2 t ζ‖ₑ) ≤ A ζ := iSup_le fun t => hA' t t.2
  rw [← ENNReal.rpow_two]
  exact ENNReal.rpow_le_rpow (h1.trans h2) (by norm_num)


end Generic

section Block

variable {d : ℕ}

/-- The (frozen-form) feature integrand of the recent block. -/
def s81s_Phi (d N : ℕ) (a β : ℝ) (ρ : Euc d → ℝ) (m H : ℝ) {Ω : Type*}
    (X : ℝ≥0 → Ω → EucConfig d N) : ℝ → Ω → (Fin N × Fin d) → KSpace d m H :=
  fun r z ia => Real.sqrt (2 / (N * β)) •
    gradFeature (critCoeff d a β ρ) m H ia.2 (max r 0) (X (Real.toNNReal r) z ia.1)

/-- Coordinates of the reconstruction of a Gaussian `𝒦`-martingale (the increment beyond `t` is invisible to the covariation). -/
theorem s81s_recon_coord_ae {Ω : Type*} {mΩ : MeasurableSpace Ω} {Q : Measure Ω} [IsProbabilityMeasure Q]
    {ℱ : Filtration ℝ mΩ} {C : WholeCoeff d} {m H q : ℝ} {ν : Measure (Euc d)}
    (hC : OscAdjointInput C m H) (hH : 0 ≤ H)
    {G : ℝ → Ω → KSpace d m H} {Cg : ℝ → KSpace d m H →L[ℝ] KSpace d m H →L[ℝ] ℝ}
    (hG : IsHilbertMartingaleWithCovariation Q ℱ H G (fun r _ => Cg r))
    (hCg : ∀ σ ∈ Set.Icc (0 : ℝ) H, ∀ u v, Cg σ u v =
      featureForm m H q (fun i => gradFeature C m H i σ) ν u v)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) H) (α : MultiIndex d) :
    ∀ᵐ ζ ∂Q, OscDual.coord (reconstructPath m H G ζ t) α =
      inner ℝ (G t ζ) (HRS.MS.S52.s52y1 m H t α) := by
  have hdir : ∀ σ ∈ Set.Ioc t H, Cg σ (HRS.MS.S52.s52y1 m H t α - HRS.MS.S52.s52y2 m H α)
      (HRS.MS.S52.s52y1 m H t α - HRS.MS.S52.s52y2 m H α) = 0 := by
    intro σ hσ
    have hσ' : σ ∈ Set.Icc (0 : ℝ) H := ⟨ht.1.trans hσ.1.le, hσ.2⟩
    rw [hCg σ hσ']
    unfold featureForm
    have hz : ∀ (a : Fin d) (x : Euc d), inner ℝ (gradFeature C m H a σ x)
        (HRS.MS.S52.s52y1 m H t α - HRS.MS.S52.s52y2 m H α) = 0 := by
      intro a x
      rw [inner_sub_right, HRS.MS.S52.s52_pair_grad_y1 hC ht.2 a hσ' x α, if_neg (not_le.2 hσ.1),
        HRS.MS.S52.s52_pair_grad_y2 hC hH a σ x α, sub_self]
    simp [hz]
  have h := s56_incr_zero hG ht _ hdir
  filter_upwards [h] with ζ hζ
  rw [HRS.MS.S52.s52_coord_recon ht.1 ht.2]
  simp only [inner_sub_right] at hζ
  linarith

/-- Finite families of coordinates of the clamped reconstruction of a Gaussian `𝒦`-martingale are independent of `𝒢 ≤ ℱ 0`. -/
theorem s81s_recon_fdd_indep {Ω : Type*} (𝒢 : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω] {Q : Measure Ω}
    [IsProbabilityMeasure Q] {ℱ : Filtration ℝ mΩ} {m b T : ℝ} (hb : 0 ≤ b) (hT : 0 ≤ T)
    {G : ℝ → Ω → KSpace d m (b + T)} {Cg : ℝ → KSpace d m (b + T) →L[ℝ] KSpace d m (b + T) →L[ℝ] ℝ}
    (hHM : IsHilbertMartingaleWithCovariation Q ℱ (b + T) G (fun r _ => Cg r))
    (hGc : ∀ ω, Continuous fun s => G s ω) (hGz : ∀ ω, G 0 ω = 0) (hGm : ∀ t, Measurable (G t))
    (hH : 0 < b + T) (h𝒢 : 𝒢 ≤ ℱ 0) (F : Finset (ℝ × MultiIndex d)) :
    Indep 𝒢 (⨆ i ∈ F, MeasurableSpace.comap (fun ζ => OscDual.coord
      (reconstructPath m (b + T) G ζ (b + max 0 (min i.1 T))) i.2) inferInstance) Q := by
  classical
  set n := F.card with hn
  set ε : Fin n ≃ F := F.equivFin.symm with hε
  set v : Fin n → ℝ := fun j => b + max 0 (min (ε j).1.1 T) with hv
  set α : Fin n → MultiIndex d := fun j => (ε j).1.2 with hα
  have hvm : ∀ j, v j ∈ Set.Icc (0 : ℝ) (b + T) := fun j =>
    ⟨by have := le_max_left (0 : ℝ) (min (ε j).1.1 T); simp only [hv]; linarith,
     by have : max 0 (min (ε j).1.1 T) ≤ T := max_le hT (min_le_right _ _); simp only [hv]; linarith⟩
  set z : Fin n → KSpace d m (b + T) := fun j =>
    HRS.MS.S52.s52y1 m (b + T) (v j) (α j) - HRS.MS.S52.s52y2 m (b + T) (α j) with hz
  set w : Fin n → KSpace d m (b + T) := fun j => HRS.MS.S52.s52y2 m (b + T) (α j) with hw
  set ts : Fin (n + n) → ℝ := Fin.append (fun _ : Fin n => b + T) v with hts
  set ys : Fin (n + n) → KSpace d m (b + T) := Fin.append z w with hys
  have htsm : ∀ c, ts c ∈ Set.Icc (0 : ℝ) (b + T) := by
    intro c
    refine Fin.addCases (fun j => ?_) (fun j => ?_) c
    · simp only [hts, Fin.append_left]; exact ⟨hH.le, le_rfl⟩
    · simp only [hts, Fin.append_right]; exact hvm j
  have hind := (s81s_vec_gauss_indep 𝒢 hHM hGc hGz hGm hH h𝒢 ts htsm ys).1
  refine indep_of_indep_of_le_right hind (iSup₂_le fun i hi => ?_)
  -- the coordinate is a measurable function of the pairing vector
  set j : Fin n := F.equivFin ⟨i, hi⟩ with hj
  have hεj : ε j = ⟨i, hi⟩ := by simp [hε, hj]
  have hcoord : ∀ ζ, OscDual.coord (reconstructPath m (b + T) G ζ (b + max 0 (min i.1 T))) i.2 =
      (fun x : EuclideanSpace ℝ (Fin (n + n)) => x (Fin.castAdd n j) + x (Fin.natAdd n j))
        (s81s_pairVec G ts ys ζ) := by
    intro ζ
    have e1 := HRS.MS.S52.s52_coord_recon (m := m) (T := b + T) (t := b + max 0 (min i.1 T))
      (by have := le_max_left (0 : ℝ) (min i.1 T); linarith)
      (by have : max 0 (min i.1 T) ≤ T := max_le hT (min_le_right _ _); linarith) G ζ i.2
    rw [e1]
    have hvj : v j = b + max 0 (min i.1 T) := by simp [hv, hεj]
    have hαj : α j = i.2 := by simp [hα, hεj]
    simp only [s81s_pairVec, hts, hys, Fin.append_left, Fin.append_right, hz, hw, hvj, hαj,
      inner_sub_right]
  have hmeas : Measurable (fun x : EuclideanSpace ℝ (Fin (n + n)) =>
      x (Fin.castAdd n j) + x (Fin.natAdd n j)) :=
    ((PiLp.continuous_apply 2 (fun _ : Fin (n + n) => ℝ) _).add
      (PiLp.continuous_apply 2 (fun _ : Fin (n + n) => ℝ) _)).measurable
  have hle : MeasurableSpace.comap (fun ζ => OscDual.coord
      (reconstructPath m (b + T) G ζ (b + max 0 (min i.1 T))) i.2) inferInstance =
      MeasurableSpace.comap ((fun x : EuclideanSpace ℝ (Fin (n + n)) =>
        x (Fin.castAdd n j) + x (Fin.natAdd n j)) ∘ s81s_pairVec G ts ys) inferInstance := by
    congr 1
    funext ζ
    exact hcoord ζ
  rw [hle, ← MeasurableSpace.comap_comp]
  exact MeasurableSpace.comap_mono hmeas.comap_le


/-- **The recent block.** -/
theorem s81s_recent_block (hd : 2 ≤ d) (a β : ℝ) (ha : 0 < a) (hβ : 0 < β) (m : ℝ)
    (hm : (wholeSpaceIndex d : ℝ) ≤ m) (T b : ℝ) (hT : 0 < T) (hb : 0 ≤ b) :
    ∃ CR : ℝ, ∀ ρβ : Euc d → ℝ, IsThermalEquilibrium d ((d : ℝ) / 2) a β ρβ → ∀ N : ℕ, 2 ≤ N →
      ∀ {Ω₁ : Type} [mΩ₁ : MeasurableSpace Ω₁] (Q₁ : Measure Ω₁) [IsProbabilityMeasure Q₁]
        (X₀ : Ω₁ → EucConfig d N) (W : ℝ≥0 → Ω₁ → (Fin N → Euc d)) (X : ℝ≥0 → Ω₁ → EucConfig d N),
        IsCanonicalRealization d ((d : ℝ) / 2) a β N Q₁ X₀ W X →
      ∀ (ℱ₁ : Filtration ℝ mΩ₁) (W'' : ℝ≥0 → Ω₁ → (Fin N × Fin d) → ℝ),
        IsCylindricalBrownian Q₁ ℱ₁ (fun t z (ia : Fin N × Fin d) => W t z ia.1 ia.2) →
        IsWholeFilteredSolution Q₁ ℱ₁ W'' W X → ∀ h : ℝ≥0,
      ∃ M : ℝ → Ω₁ → KSpace d m (b + T),
        IsHilbertItoIntegral Q₁ (HRS.Whole.BreakdownS81.s81b_shiftFil ℱ₁ h)
          (fun t z (ia : Fin N × Fin d) => HRS.Whole.S79.s79p_shiftW h W t z ia.1 ia.2)
          (s81s_Phi d N a β ρβ m (b + T) (HRS.Whole.S79.s79p_shiftX h X)) M ∧
        ∃ (Ω₂ : Type) (mΩ₂ : MeasurableSpace Ω₂) (Q₂ : Measure Ω₂) (_ : IsProbabilityMeasure Q₂)
          (π₂ : Ω₂ → Ω₁) (Rp G2 : ℝ → Ω₂ → OscDual d m),
          MeasurePreserving π₂ Q₂ Q₁ ∧
          (∀ t ζ, Rp t ζ = reconstructPath m (b + T) (fun τ z => M τ (π₂ z)) ζ (b + max 0 (min t T))) ∧
          S81PProc Q₂ T Rp ∧ S81PProc Q₂ T G2 ∧
          Indep ((ℱ₁ (h : ℝ)).comap π₂) (⨆ t : ℝ, MeasurableSpace.comap (G2 t) inferInstance) Q₂ ∧
          (∀ (p : ℕ) (ts : Fin p → ℝ) (αs : Fin p → MultiIndex d), (∀ c, ts c ∈ Set.Icc (0 : ℝ) T) →
            (Matrix.of fun i j => noiseCovW (critCoeff d a β ρβ) β⁻¹ (b + ts i) (b + ts j)
              (oscTestFun m (αs i)) (oscTestFun m (αs j))).PosSemidef ∧
            Q₂.map (s81p_vec G2 ts αs) = multivariateGaussian 0
              (Matrix.of fun i j => noiseCovW (critCoeff d a β ρβ) β⁻¹ (b + ts i) (b + ts j)
                (oscTestFun m (αs i)) (oscTestFun m (αs j)))) ∧
          s81p_L2 Q₂ (fun ζ => processWindow m T 0 Rp ζ - processWindow m T 0 G2 ζ) ≤
            ENNReal.ofReal (CR * (N : ℝ) ^ (-(1 / 2 : ℝ))) := by
  classical
  have hH : 0 < b + T := by linarith
  obtain ⟨Cin, hCin⟩ := s81s_linear_input hd ha hβ
  obtain ⟨Crec, hCrec⟩ := s81s_finite_noise hd a β ha hβ m hm (b + T) hH Cin
  refine ⟨3 * max Crec 0, fun ρβ hρβ N hN Ω₁ _ Q₁ _ X₀ W X hR ℱ₁ W'' hWc hF h => ?_⟩
  -- shifted data
  have hRh := HRS.Whole.BreakdownS81.s81b_isCanonical_shift hR h
  have hWh := s81s_cyl_shift_vec hWc h
  have hFh := HRS.Whole.BreakdownS81.s81b_filtered_shift hF h
  have hprog : ∀ i : Fin N, IsProgressive (HRS.Whole.BreakdownS81.s81b_shiftFil ℱ₁ h)
      (fun r z => HRS.Whole.S79.s79p_shiftX h X (Real.toNNReal r) z i) :=
    fun i => s81s_prog_coord hFh.progressive i
  have hlin : ∀ t ∈ Set.Icc (0 : ℝ) (b + T), LinearInputBounds d ((d : ℝ) / 2) N
      (HRS.Whole.withDensityReal ρβ) Cin Q₁ (HRS.Whole.S79.s79p_shiftX h X (Real.toNNReal t)) :=
    fun t _ => hCin ρβ hρβ N hN Q₁ _ _ _ hRh (Real.toNNReal t)
  obtain ⟨hHS, hrest⟩ := hCrec ρβ hρβ N hN Q₁ (X h) (HRS.Whole.S79.s79p_shiftW h W)
    (HRS.Whole.S79.s79p_shiftX h X) hRh (HRS.Whole.BreakdownS81.s81b_shiftFil ℱ₁ h) hWh hprog hlin
  obtain ⟨M, hM⟩ := s81s_exists_hito hWh hHS
  refine ⟨M, hM, ?_⟩
  obtain ⟨Cdet, hform, Ω₂, mΩ₂, Q₂, π₂, ℱ₂, ι, hι, e, B, Sr, Sb, G, hcoup, hcost, hWb, hHS2⟩ := hrest M hM
  haveI : IsProbabilityMeasure Q₂ := hcoup.prob
  have hG := hcoup.gaussian
  have hGc : ∀ ω, Continuous fun s => G s ω := hG.cont
  have hGz : ∀ ω, G 0 ω = 0 := fun ω => hG.zero 0 le_rfl ω
  have hGm : ∀ τ, Measurable (G τ) := fun τ => (hG.adapted τ).mono (ℱ₂.le τ) le_rfl
  have hMm : ∀ τ, Measurable (M τ) := fun τ =>
    (hM.adapted τ).mono ((HRS.Whole.BreakdownS81.s81b_shiftFil ℱ₁ h).le τ) le_rfl
  have hπ := hcoup.preserving
  -- the Gaussian martingale
  set Cg : ℝ → KSpace d m (b + T) →L[ℝ] KSpace d m (b + T) →L[ℝ] ℝ := fun r =>
    hsCovForm (fun j : ι => if r ≤ b + T then Sb r (e j) else 0) with hCgdef
  have hHM : IsHilbertMartingaleWithCovariation Q₂ ℱ₂ (b + T) G (fun r _ => Cg r) :=
    HRS.Uniform.Comp28.isHM_of_hilbertIto hcoup.brownian hHS2 hG (b + T)
  obtain ⟨ω₀⟩ := MeasureTheory.nonempty_of_isProbabilityMeasure Q₂
  have hCg_eq : ∀ r ∈ Set.Icc (0 : ℝ) (b + T), Cg r = Cdet r := by
    intro r hr
    have hs : Summable fun j : ι => ‖Sb r (e j)‖ ^ 2 := by
      have := (hHS2 0).summable r ω₀
      simpa [hr.2] using this
    have e1 := HRS.Uniform.Q07c.hsCovForm_sqrt_cols e (hcoup.sqrtSb r hr) hs
    simp only [hCgdef, hr.2, ite_true]
    exact e1
  have hCg : ∀ σ ∈ Set.Icc (0 : ℝ) (b + T), ∀ u v, Cg σ u v = featureForm m (b + T) β⁻¹
      (fun i => gradFeature (critCoeff d a β ρβ) m (b + T) i σ) (HRS.Whole.withDensityReal ρβ) u v :=
    fun σ hσ u v => by rw [hCg_eq σ hσ]; exact hform σ hσ u v
  -- the setup
  obtain ⟨θ, Λ, K, C₀, S, hbv, hSρ, hSinv, hSκ, hScoeff, hSdyn, hSadj⟩ :=
    s81s_setup hd ha hβ hρβ hm hH
  have hC : OscAdjointInput (critCoeff d a β ρβ) m (b + T) := by
    rw [← hScoeff N]; exact hSadj N
  -- the processes
  set Rp : ℝ → Ω₂ → OscDual d m := fun t ζ =>
    reconstructPath m (b + T) (fun τ z => M τ (π₂ z)) ζ (b + max 0 (min t T)) with hRp
  set G2 : ℝ → Ω₂ → OscDual d m := fun t ζ =>
    reconstructPath m (b + T) G ζ (b + max 0 (min t T)) with hG2
  have hRproc : S81PProc Q₂ T Rp :=
    s81s_recon_proc hb hT.le le_rfl (fun τ z => M τ (π₂ z)) (fun τ => (hMm τ).comp hπ.measurable)
      (Filter.Eventually.of_forall fun ζ => (hM.cont (π₂ ζ)).continuousOn)
  have hGproc : S81PProc Q₂ T G2 :=
    s81s_recon_proc hb hT.le le_rfl G hGm (Filter.Eventually.of_forall fun ζ => (hGc ζ).continuousOn)
  have hclamp : ∀ t ∈ Set.Icc (0 : ℝ) T, max 0 (min t T) = t := fun t ht => by
    rw [min_eq_left ht.2, max_eq_right ht.1]
  refine ⟨Ω₂, mΩ₂, Q₂, hcoup.prob, π₂, Rp, G2, hπ, fun t ζ => rfl, hRproc, hGproc, ?_, ?_, ?_⟩
  · -- independence
    have hle0 : (ℱ₁ (h : ℝ)).comap π₂ ≤ ℱ₂ 0 := by
      have := hcoup.filtration 0
      simpa [HRS.Whole.BreakdownS81.s81b_shiftFil] using this
    refine s81s_proc_indep _ ((ℱ₂.le 0).trans' ?_ |> fun h => h) G2 (fun t => hGproc.1 t) ?_
    · exact hle0
    · intro F
      exact s81s_recon_fdd_indep _ hb hT.le hHM hGc hGz hGm hH hle0 F
  · -- finite-dimensional laws
    intro p ts αs hts
    set vs : Fin p → ℝ := fun i => b + ts i with hvs
    have hvsm : ∀ i, vs i ∈ Set.Icc (0 : ℝ) (b + T) := fun i =>
      ⟨by linarith [(hts i).1], by linarith [(hts i).2]⟩
    set ys : Fin p → KSpace d m (b + T) := fun i =>
      HRS.MS.S52.s52y1 m (b + T) (vs i) (αs i) with hys
    have hlaw := s81s_vec_law hHM hGc hGz hGm hH vs hvsm ys
    have hpsd := (s81s_vec_gauss_indep ⊥ hHM hGc hGz hGm hH bot_le vs hvsm ys).2.2
    have hform' : ∀ r ∈ Set.Icc (0 : ℝ) (b + T), ∀ u v, Cdet r u v = featureForm m (b + T) β⁻¹
        (fun i => gradFeature (S.coeff N) m (b + T) i r) (HRS.Whole.withDensityReal (S.ρ N r)) u v := by
      intro r hr u v
      rw [hScoeff N, hSρ N r]
      exact hform r hr u v
    have hcov : s81s_covMat Cg vs ys = Matrix.of fun i j => noiseCovW (critCoeff d a β ρβ) β⁻¹
        (b + ts i) (b + ts j) (oscTestFun m (αs i)) (oscTestFun m (αs j)) := by
      ext i j
      simp only [s81s_covMat, Matrix.of_apply]
      have e1 : ∫ σ in Set.Icc (0 : ℝ) (min (vs i) (vs j)), Cg σ (ys i) (ys j) =
          ∫ σ in Set.Icc (0 : ℝ) (min (vs i) (vs j)), Cdet σ (ys i) (ys j) :=
        setIntegral_congr_fun measurableSet_Icc fun σ hσ => by
          rw [hCg_eq σ ⟨hσ.1, hσ.2.trans ((min_le_left _ _).trans (hvsm i).2)⟩]
      rw [e1]
      have := s81s_cdet_noiseCov (s81s_bounds d a β m (b + T) θ Λ K C₀) hbv S N (hSadj N) Cdet β⁻¹
        hform' (hvsm i) (hvsm j) (αs i) (αs j)
      rw [hScoeff N] at this
      exact this
    have hae : s81p_vec G2 ts αs =ᵐ[Q₂] s81s_pairVec G vs ys := by
      have h1 : ∀ᵐ ζ ∂Q₂, ∀ i, OscDual.coord (reconstructPath m (b + T) G ζ (vs i)) (αs i) =
          inner ℝ (G (vs i) ζ) (ys i) := by
        rw [ae_all_iff]; intro i
        exact s81s_recon_coord_ae hC hH.le hHM hCg (hvsm i) (αs i)
      filter_upwards [h1] with ζ hζ
      ext i
      have e2 : G2 (ts i) ζ = reconstructPath m (b + T) G ζ (vs i) := by
        simp only [hG2, hvs]
        rw [hclamp (ts i) (hts i)]
      simp only [s81p_vec, s81s_pairVec, e2]
      exact hζ i
    rw [hcov] at hlaw hpsd
    exact ⟨hpsd, by rw [Measure.map_congr hae]; exact hlaw⟩
  · -- cost
    have hδ := HRS.MS.FinNoise.s86_deltaN_nonneg d N (by omega)
    have hδ2 := s81s_deltaN_le (d := d) (N := N) (by omega)
    have hx : 0 ≤ (N : ℝ) ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg (Nat.cast_nonneg N) _
    set A : Ω₂ → ℝ≥0∞ := fun ζ => ⨆ t : Set.Icc (0 : ℝ) (b + T), ENNReal.ofReal
      ‖reconstructPath m (b + T) (fun τ z => M τ (π₂ z)) ζ t - reconstructPath m (b + T) G ζ t‖ with hA
    have hAle : ∀ᵐ ζ ∂Q₂, ∀ t ∈ Set.Icc (0 : ℝ) T, ‖Rp t ζ - G2 t ζ‖ₑ ≤ A ζ := by
      refine Filter.Eventually.of_forall fun ζ t ht => ?_
      have hbt : b + t ∈ Set.Icc (0 : ℝ) (b + T) := ⟨by linarith [ht.1], by linarith [ht.2]⟩
      have e3 : Rp t ζ - G2 t ζ = reconstructPath m (b + T) (fun τ z => M τ (π₂ z)) ζ (b + t) -
          reconstructPath m (b + T) G ζ (b + t) := by
        simp only [hRp, hG2]
        rw [hclamp t ht]
      rw [e3, ← ofReal_norm]
      exact le_iSup (fun t : Set.Icc (0 : ℝ) (b + T) => ENNReal.ofReal
        ‖reconstructPath m (b + T) (fun τ z => M τ (π₂ z)) ζ t - reconstructPath m (b + T) G ζ t‖)
        ⟨b + t, hbt⟩
    refine (s81s_L2_window_le hRproc hGproc A hAle).trans (hcost.trans (ENNReal.ofReal_le_ofReal ?_))
    calc Crec * ((N : ℝ) ^ (-(1 / 2 : ℝ)) + deltaN d ((d : ℝ) / 2) N)
        ≤ max Crec 0 * ((N : ℝ) ^ (-(1 / 2 : ℝ)) + deltaN d ((d : ℝ) / 2) N) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
      _ ≤ max Crec 0 * (3 * (N : ℝ) ^ (-(1 / 2 : ℝ))) :=
          mul_le_mul_of_nonneg_left (by linarith) (le_max_right _ _)
      _ = 3 * max Crec 0 * (N : ℝ) ^ (-(1 / 2 : ℝ)) := by ring

end Block

end HRS.Whole.S81S
