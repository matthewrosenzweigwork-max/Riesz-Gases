import HRS.Commutator.Torus.TPRODAux2
import HRS.Commutator.Torus.LEIBTAux26

/-!
# T-PROD helper file 3: smoothness of band-limited functions, measurable representatives,
coefficient convergence, and the componentwise Leibniz estimate with Fejér smoothing
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators FourierTransform ComplexConjugate

namespace HRS.Commutator.TorusNote

open HRS

variable {d : ℕ}

lemma tprod_isSmooth_toFun_trig {n : ℕ} {c : Lattice d → ℂ} (hr : HRS.PDE.IsRealCoeff c)
    (ht : HRS.PDE.IsTrigPoly n c) : Torus.IsSmooth (HRS.PDE.toFun c) := by
  unfold Torus.IsSmooth Torus.IsCk
  rw [contDiff_infty]
  intro m
  exact HRS.PDE.R2Aux.isCk_toFun_trig hr ht m

/-- A continuous function whose Fourier coefficients vanish outside a box is smooth. -/
lemma tprod_smooth_of_box {u : Torus d → ℝ} (hu : Continuous u) (n : ℕ)
    (hsupp : ∀ k : Lattice d, ¬ HRS.PDE.InBox n k → Torus.fcoef u k = 0) : Torus.IsSmooth u := by
  have hui : Integrable u := HRS.PDE.MFThermalExist.integrable_of_continuous' hu
  set c : Lattice d → ℂ := fun k => Torus.fcoef u k with hc
  have hr : HRS.PDE.IsRealCoeff c := fun k => tprod_fcoef_conj hui k
  have ht : HRS.PDE.IsTrigPoly n c := by
    intro k hk
    by_contra hbox
    exact hk (hsupp k hbox)
  have hs : Summable fun k => ‖c k‖ := HRS.PDE.R2Aux.summable_norm_of_trig ht
  have heq : u = HRS.PDE.toFun c := by
    funext x
    have h1 := Torus.hasSum_fcoef_series hu hs x
    have h2 : ((u x : ℝ) : ℂ) = HRS.PDE.series c x := h1.tsum_eq.symm
    unfold HRS.PDE.toFun
    rw [← h2]
    simp
  rw [heq]
  exact tprod_isSmooth_toFun_trig hr ht

lemma tprod_meas_rep (W : Torus d → ℝ) (p : ℝ≥0∞) (X : ℝ≥0∞)
    (hX : AEStronglyMeasurable W volume → eLpNorm W p volume ≤ X) :
    ∃ W' : Torus d → ℝ, Measurable W' ∧ (∀ k, Torus.fcoef W' k = Torus.fcoef W k) ∧
      eLpNorm W' p volume ≤ X := by
  by_cases h : AEStronglyMeasurable W volume
  · refine ⟨h.mk W, h.stronglyMeasurable_mk.measurable, fun k => ?_,
      ((eLpNorm_congr_ae h.ae_eq_mk.symm).le).trans (hX h)⟩
    unfold Torus.fcoef
    refine integral_congr_ae ?_
    filter_upwards [h.ae_eq_mk] with x hx
    rw [hx]
  · refine ⟨0, measurable_const, fun k => ?_, by simp⟩
    rw [tsamp_not_aesm_fcoef h k]
    simp [Torus.fcoef]

lemma tprod_fcoef_sum {ι : Type*} (S : Finset ι) {F : ι → Torus d → ℝ}
    (hF : ∀ i, Integrable (F i)) (k : Lattice d) :
    Torus.fcoef (fun x => ∑ i ∈ S, F i x) k = ∑ i ∈ S, Torus.fcoef (F i) k := by
  unfold Torus.fcoef
  have hint : ∀ i ∈ S, Integrable (fun x : Torus d => Torus.mode (-k) x * ((F i x : ℝ) : ℂ)) := by
    intro i _
    exact (hF i).ofReal.bdd_mul (Torus.continuous_mode (-k)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => (Torus.norm_mode (-k) x).le)
  rw [← integral_finsetSum S hint]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  push_cast
  rw [Finset.mul_sum]

lemma tprod_coef_tendsto {f g : Torus d → ℝ} (hf : Continuous f) (hg : Continuous g)
    {φ : ℕ → Torus d → ℝ} (hφc : ∀ N, Continuous (φ N))
    (hφ : ∀ N, φ N =ᵐ[volume] textConv (HRS.PDE.MFThermalExist.fejer (N + 1) : Torus d → ℝ) f)
    (k : Lattice d) :
    Tendsto (fun N => Torus.fcoef (fun x => φ N x * g x) k) atTop
      (𝓝 (Torus.fcoef (fun x => f x * g x) k)) := by
  obtain ⟨B, hB⟩ := (isCompact_univ (X := Torus d)).exists_bound_of_continuousOn hg.continuousOn
  have hB0 : 0 ≤ B := le_trans (norm_nonneg _) (hB 0 (Set.mem_univ _))
  set V : ℝ := (volume : Measure (Torus d)).real Set.univ with hV
  have hV0 : 0 ≤ V := measureReal_nonneg
  rw [Metric.tendsto_nhds]
  intro ε hε
  set δ : ℝ := ε / ((B + 1) * (V + 1)) with hδ
  have hδ0 : 0 < δ := by positivity
  filter_upwards [tprod_fejer_unif hf hδ0] with N hN
  have hint : ∀ (a : Torus d → ℝ), Continuous a →
      Integrable (fun x : Torus d => Torus.mode (-k) x * ((a x : ℝ) : ℂ)) := fun a ha =>
    ((Torus.continuous_mode (-k)).mul (Complex.continuous_ofReal.comp ha)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hdiff : Torus.fcoef (fun x => φ N x * g x) k - Torus.fcoef (fun x => f x * g x) k =
      ∫ x, Torus.mode (-k) x * (((φ N x - f x) * g x : ℝ) : ℂ) := by
    unfold Torus.fcoef
    rw [← integral_sub (hint (fun x => φ N x * g x) ((hφc N).mul hg))
      (hint (fun x => f x * g x) (hf.mul hg))]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    push_cast
    ring
  rw [dist_eq_norm, hdiff]
  have hbd : ∀ᵐ x ∂(volume : Measure (Torus d)),
      ‖Torus.mode (-k) x * (((φ N x - f x) * g x : ℝ) : ℂ)‖ ≤ δ * B := by
    filter_upwards [hφ N] with x hx
    rw [norm_mul, Torus.norm_mode, one_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul]
    have h1 : |φ N x - f x| ≤ δ := by
      rw [hx]; exact (hN x).le
    have h2 : |g x| ≤ B := by simpa using hB x (Set.mem_univ _)
    exact mul_le_mul h1 h2 (abs_nonneg _) hδ0.le
  have := norm_integral_le_of_norm_le_const hbd
  refine lt_of_le_of_lt this ?_
  have hε' : δ * B * V < ε := by
    have e : δ * B * V = ε * (B / (B + 1)) * (V / (V + 1)) := by
      rw [hδ]; field_simp
    rw [e]
    have h1 : B / (B + 1) < 1 := by rw [div_lt_one (by positivity)]; linarith
    have h2 : V / (V + 1) < 1 := by rw [div_lt_one (by positivity)]; linarith
    have h3 : 0 ≤ B / (B + 1) := by positivity
    have h4 : 0 ≤ V / (V + 1) := by positivity
    calc ε * (B / (B + 1)) * (V / (V + 1)) ≤ ε * (B / (B + 1)) * 1 := by gcongr
      _ = ε * (B / (B + 1)) := by ring
      _ < ε * 1 := by gcongr
      _ = ε := by ring
  exact hε'

lemma tprod_bessel_smooth {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) (α : ℝ) {f : Torus d → ℝ}
    (hf : Torus.IsSmooth f) : IsBesselRepT η α f (leibt_F0 α η f) := by
  intro k
  rw [leibt_F0_fcoef hη hη1 α hf, leibt_bc, leibt_m_lam α η hη]

/-- Componentwise Leibniz estimate with Fejér smoothing of the non-smooth factor. -/
theorem tprod_comp {η α CL : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) {P Q : ℝ} (hP : 1 < P) (hQ : 1 < Q)
    (hLeib : ∀ f g h F G H : Torus d → ℝ, Torus.IsSmooth f → Torus.IsSmooth g →
      (∀ x, h x = f x * g x) → Integrable F → Integrable G → Integrable H →
      IsBesselRepT η α f F → IsBesselRepT η α g G → IsBesselRepT η α h H →
        eLpNorm H 2 volume ≤ ENNReal.ofReal CL *
          (eLpNorm F (ENNReal.ofReal P) volume * eLpNorm g (ENNReal.ofReal Q) volume +
            eLpNorm G (ENNReal.ofReal Q) volume * eLpNorm f (ENNReal.ofReal P) volume))
    {f W g U : Torus d → ℝ} (hf : Continuous f) (hg : Torus.IsSmooth g)
    (hW : IsBesselRepT η α f W) (hU : IsBesselRepT η α g U)
    {XW XU : ℝ≥0∞} (hXW : XW ≠ ⊤) (hXU : XU ≠ ⊤)
    (hWX : AEStronglyMeasurable W volume → eLpNorm W (ENNReal.ofReal P) volume ≤ XW)
    (hUX : AEStronglyMeasurable U volume → eLpNorm U (ENNReal.ofReal Q) volume ≤ XU) :
    ∃ ψ H : ℕ → Torus d → ℝ, (∀ N, Continuous (ψ N) ∧ Continuous (H N)) ∧
      (∀ N k, Torus.fcoef (H N) k =
        (((1 + 4 * Real.pi ^ 2 * η ^ 2 * Lattice.enorm k ^ 2) ^ (α / 2) : ℝ) : ℂ) *
          Torus.fcoef (ψ N) k) ∧
      (∀ N, eLpNorm (H N) 2 volume ≤ ENNReal.ofReal CL *
          (XW * eLpNorm g (ENNReal.ofReal Q) volume +
            XU * eLpNorm f (ENNReal.ofReal P) volume)) ∧
      ∀ k, Tendsto (fun N => Torus.fcoef (ψ N) k) atTop
        (𝓝 (Torus.fcoef (fun x => f x * g x) k)) := by
  have hP1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal P := ENNReal.one_le_ofReal.2 hP.le
  have hQ1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal Q := ENNReal.one_le_ofReal.2 hQ.le
  have hgc : Continuous g := leibt_continuous_of_smooth hg
  obtain ⟨W', hW'm, hW'c, hW'n⟩ := tprod_meas_rep W (ENNReal.ofReal P) XW hWX
  obtain ⟨U', hU'm, hU'c, hU'n⟩ := tprod_meas_rep U (ENNReal.ofReal Q) XU hUX
  have hW'i : Integrable W' :=
    (show MemLp W' (ENNReal.ofReal P) volume from lt_of_le_of_lt hW'n hXW.lt_top).integrable hP1
  have hU'i : Integrable U' :=
    (show MemLp U' (ENNReal.ofReal Q) volume from lt_of_le_of_lt hU'n hXU.lt_top).integrable hQ1
  have hfi : Integrable f := HRS.PDE.MFThermalExist.integrable_of_continuous' hf
  have hex : ∀ N : ℕ, ∃ φ : Torus d → ℝ, Torus.IsSmooth φ ∧
      (∀ k, Torus.fcoef φ k = ((tprod_fc (N + 1) k : ℝ) : ℂ) * Torus.fcoef f k) ∧
      φ =ᵐ[volume] textConv (HRS.PDE.MFThermalExist.fejer (N + 1) : Torus d → ℝ) f :=
    fun N => tprod_exists_smooth hfi (Nat.succ_pos N)
  choose φ hφs hφk hφae using hex
  have hφc : ∀ N, Continuous (φ N) := fun N => leibt_continuous_of_smooth (hφs N)
  have hψs : ∀ N, Torus.IsSmooth (fun x => φ N x * g x) := fun N =>
    leibt_smooth_mul (hφs N) hg (fun _ => rfl)
  have hKi : ∀ N : ℕ, Integrable (HRS.PDE.MFThermalExist.fejer (N + 1) : Torus d → ℝ) := fun N =>
    HRS.PDE.MFThermalExist.integrable_of_continuous' (HRS.PDE.MFThermalExist.fejer_continuous _)
  have hbound : ∀ N : ℕ, eLpNorm (leibt_F0 α η (fun x => φ N x * g x)) 2 volume ≤
      ENNReal.ofReal CL *
        (XW * eLpNorm g (ENNReal.ofReal Q) volume +
          XU * eLpNorm f (ENNReal.ofReal P) volume) := by
    intro N
    have hrepF : IsBesselRepT η α (φ N)
        (textConv (HRS.PDE.MFThermalExist.fejer (N + 1) : Torus d → ℝ) W') := by
      intro k
      rw [text_fcoef_conv (hKi N) hW'i, tprod_fejer_fcoef (Nat.succ_pos N), hW'c k, hW k, hφk N k]
      ring
    have hrepU : IsBesselRepT η α g U' := fun k => by rw [hU'c k]; exact hU k
    have h1 := hLeib (φ N) g (fun x => φ N x * g x) _ U' _ (hφs N) hg (fun _ => rfl)
      (text_integrable_conv (hKi N) hW'i) hU'i
      (HRS.PDE.MFThermalExist.integrable_of_continuous'
        (leibt_F0_continuous hη hη1 α (hψs N)))
      hrepF hrepU (tprod_bessel_smooth hη hη1 α (hψs N))
    refine h1.trans ?_
    gcongr
    · exact (tprod_conv_eLpNorm_le hW'm hP (Nat.succ_pos N)).trans hW'n
    · rw [eLpNorm_congr_ae (hφae N)]
      exact tprod_conv_eLpNorm_le hf.measurable hP (Nat.succ_pos N)
  refine ⟨fun N x => φ N x * g x, fun N => leibt_F0 α η (fun x => φ N x * g x), fun N => ⟨?_, ?_⟩, ?_,
    hbound, ?_⟩
  · exact (hφc N).mul hgc
  · exact leibt_F0_continuous hη hη1 α (hψs N)
  · intro N k
    exact tprod_bessel_smooth hη hη1 α (hψs N) k
  · intro k
    exact tprod_coef_tendsto hf hgc hφc hφae k

end HRS.Commutator.TorusNote
