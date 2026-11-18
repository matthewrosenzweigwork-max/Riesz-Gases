import HRS.MS.Fp81S21ChaosLimit
import HRS.MS.Fp81S21GaussFeature
import HRS.MS.Fp81S21GaussUnif3
import HRS.MS.ProClosureS111FeatureEmbedding
import HRS.MS.S111BDAux4
import HRS.MS.R2InterpAux3

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators RealInnerProductSpace

namespace HRS.Fp81.S21

open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.S111X2 HRS.MS.ProClosureS111

/-- The retained shifted window has the centered Gaussian law supplied by its
linear Gaussian evolution. -/
theorem fp81s21_retained_Z_centeredGaussian
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ)
    (G0 : GaussianRealization R) :
    ∀ a : ℝ, 0 ≤ a →
      HRS.IsCenteredGaussian (HRS.law G0.P (r26t3_Zpath G0 a)) := by
  intro a ha
  have hshift := HRS.MS.S111BD.s111_shifted_window_gaussian
    p.d G0.P (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ) p.β⁻¹ p.T a
    (a + p.T)
    (HRS.Whole.susceptibilityCov (rieszKernel p.d p.s) (r26t3_mu R 0) p.γ)
    G0.Z (G0.evolution (a + p.T)) p.hT ha le_rfl
  simpa [r26t3_Zpath, HRS.law] using hshift.2.1

/-- Uniform fourth moments for the retained shifted window, with the moment
constant chosen before the shift and source realization. -/
theorem fp81s21_retained_Z_uniform_fourth (p : Parameters) :
    ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ0 → ∀ R : Trajectory p δ,
        ∃ MZ : ℝ, 0 ≤ MZ ∧
          ∀ G0 : GaussianRealization R, ∀ a : ℝ, 0 ≤ a →
            MemLp (r26t3_Zpath G0 a) 4 G0.P ∧
            Integrable (fun ω => ‖r26t3_Zpath G0 a ω‖ ^ 4) G0.P ∧
            (∫ ω, ‖r26t3_Zpath G0 a ω‖ ^ 4 ∂G0.P) ≤ MZ := by
  obtain ⟨δ0, hδ0, hδ0half, hfour⟩ := fp81s21_gauss_unif_window_fourth p
  refine ⟨δ0, hδ0, hδ0half, ?_⟩
  intro δ hδ hδle R
  obtain ⟨MZ, hMZ, hfourR⟩ := hfour δ hδ hδle R p.T p.hT
  refine ⟨MZ, hMZ, ?_⟩
  intro G0 a ha
  have hshift := HRS.MS.S111BD.s111_shifted_window_gaussian
    p.d G0.P (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ) p.β⁻¹ p.T a
    (a + p.T)
    (HRS.Whole.susceptibilityCov (rieszKernel p.d p.s) (r26t3_mu R 0) p.γ)
    G0.Z (G0.evolution (a + p.T)) p.hT ha le_rfl
  have hhas := HasGaussianLaw.mk hshift.1 hshift.2.1.1
  have hmem : MemLp (r26t3_Zpath G0 a) 4 G0.P := by
    simpa [r26t3_Zpath] using
      hhas.memLp (by norm_num : (ENNReal.ofReal (4 : ℝ)) ≠ ⊤)
  have hmom := hfourR a ha G0
  refine ⟨hmem, ?_, ?_⟩
  · simpa [r26t3_Zpath] using hmom.1
  · simpa [r26t3_Zpath] using hmom.2

private theorem fp81s21_retained_window_at_eq
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ)
    (G0 : GaussianRealization R) (a : ℝ) (ha : 0 ≤ a)
    (t : Set.Icc (0 : ℝ) p.T) :
    (fun ω => OscPath.at' (r26t3_Zpath G0 a ω) t) =ᵐ[G0.P]
      fun ω => G0.Z (a + (t : ℝ)) ω := by
  have hcont : ∀ᵐ ω ∂G0.P,
      ContinuousOn (fun u : ℝ => G0.Z u ω) (Set.Icc (0 : ℝ) (a + p.T)) :=
    (G0.evolution (a + p.T)).cont
  have hshift : ContinuousOn (fun u : ℝ => a + u) (Set.Icc (0 : ℝ) p.T) :=
    (continuous_const.add continuous_id).continuousOn
  have hmaps : Set.MapsTo (fun u : ℝ => a + u) (Set.Icc (0 : ℝ) p.T)
      (Set.Icc (0 : ℝ) (a + p.T)) := by
    intro u hu
    constructor <;> dsimp <;> linarith [ha, hu.1, hu.2]
  have hwindow : ∀ᵐ ω ∂G0.P,
      Continuous (fun u : Set.Icc (0 : ℝ) p.T => G0.Z (a + (u : ℝ)) ω) := by
    filter_upwards [hcont] with ω hω
    exact continuousOn_iff_continuous_restrict.mp (hω.comp hshift hmaps)
  filter_upwards [hwindow] with ω hω
  simp [r26t3_Zpath, HRS.Whole.processWindow, HRS.Whole.windowPathOf,
    OscPath.at', hω]

private theorem fp81s21_retained_window_eval_ae
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ)
    (G0 : GaussianRealization R) (a : ℝ) (ha : 0 ≤ a)
    (t : Set.Icc (0 : ℝ) p.T) (φ : Euc p.d → ℝ)
    (Y : ℝ → (Euc p.d → ℝ) → G0.Ω → ℝ)
    (hsrcEval : ∀ u : ℝ, 0 ≤ u → ∀ ψ : Euc p.d → ℝ,
      IsOscTest (wholeSpaceIndex p.d : ℝ) ψ →
      (fun ω => OscDual.eval (G0.Z u ω) ψ) =ᵐ[G0.P] fun ω => Y u ψ ω)
    (hφ : IsOscTest (wholeSpaceIndex p.d : ℝ) φ) :
    (fun ω => OscDual.eval (OscPath.at' (r26t3_Zpath G0 a ω) t) φ) =ᵐ[G0.P]
      fun ω => Y (a + (t : ℝ)) φ ω := by
  have hu : 0 ≤ a + (t : ℝ) := add_nonneg ha t.2.1
  have hAt := fp81s21_retained_window_at_eq p R G0 a ha t
  have hsrc := hsrcEval (a + (t : ℝ)) hu φ hφ
  filter_upwards [hAt, hsrc] with ω hω hωsrc
  rw [hω]
  exact hωsrc

/-- Conditional retained-source first-chaos theorem. The source hypothesis
records both the compiled evaluation identity and the scalar `L²`-closure
certificate needed for each projected coordinate. The actual compiled feature
is `J (fp81s21_combinedFeature ...)`. -/
theorem fp81s21_retained_Z_firstChaos_conditional
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ)
    [IsProbabilityMeasure (r26t3_mu R 0)]
    (G0 : GaussianRealization R)
    (ξ : ℕ → G0.Ω → ℝ) (hξ : HRS.IsStdGaussianSeq G0.P ξ)
    (hξmeas : ∀ i, Measurable (ξ i))
    {Mg : ℝ} {K : Lp ℝ 2 (r26t3_mu R 0) →L[ℝ] Lp ℝ 2 (r26t3_mu R 0)}
    (hK : KRep (rieszKernel p.d p.s) (r26t3_mu R 0) K Mg)
    (J : Fp81S21GaussFeatureHilbert p R →ₗᵢ[ℝ] GaussianFeatureHilbert)
    (W : GaussianFeatureHilbert → G0.Ω → ℝ)
    (hsrc : ∀ u : ℝ, 0 ≤ u → ∀ φ : Euc p.d → ℝ,
      IsOscTest (wholeSpaceIndex p.d : ℝ) φ →
      (fun ω => OscDual.eval (G0.Z u ω) φ) =ᵐ[G0.P]
        (fun ω => W (J (fp81s21_combinedFeature p R hK u φ)) ω) ∧
      HRS.MC.E213U13.InQ1 hξ hξmeas
        (fun ω => W (J (fp81s21_combinedFeature p R hK u φ)) ω)) :
    ∀ a : ℝ, 0 ≤ a →
      HRS.InFirstChaos G0.P ξ 2 (r26t3_Zpath G0 a) ∧
      HRS.IsCenteredGaussian (HRS.law G0.P (r26t3_Zpath G0 a)) := by
  intro a ha
  let Z : G0.Ω → Window p := r26t3_Zpath G0 a
  have hshift := HRS.MS.S111BD.s111_shifted_window_gaussian
    p.d G0.P (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ) p.β⁻¹ p.T a
    (a + p.T)
    (HRS.Whole.susceptibilityCov (rieszKernel p.d p.s) (r26t3_mu R 0) p.γ)
    G0.Z (G0.evolution (a + p.T)) p.hT ha le_rfl
  have hhas : HasGaussianLaw Z G0.P := by
    have h := HasGaussianLaw.mk hshift.1 hshift.2.1.1
    simpa [Z, r26t3_Zpath] using h
  have hZmeas : AEStronglyMeasurable Z G0.P := by
    simpa [Z, r26t3_Zpath] using hshift.1.aestronglyMeasurable
  have hZ4 : MemLp Z (ENNReal.ofReal 4) G0.P := by
    exact hhas.memLp (by norm_num : (ENNReal.ofReal (4 : ℝ)) ≠ ⊤)
  let Pn : ℕ → Window p →L[ℝ] Window p := fun n =>
    HRS.MS.R2Interp.s102_Pj (d := p.d) (m := wholeSpaceIndex p.d) p.T p.hT n
  have hPn : ∀ n x, ‖Pn n x‖ ≤ ‖x‖ := by
    intro n x
    have hop :=
      (HRS.MS.R2Interp.s102_projection_strong
        (d := p.d) (m := wholeSpaceIndex p.d) p.T p.hT).1 n
    calc
      ‖Pn n x‖ ≤ ‖Pn n‖ * ‖x‖ := (Pn n).le_opNorm x
      _ ≤ 1 * ‖x‖ := mul_le_mul_of_nonneg_right hop (norm_nonneg x)
      _ = ‖x‖ := one_mul _
  have hlim : ∀ x, Tendsto (fun n => Pn n x) atTop (𝓝 x) := by
    intro x
    exact (HRS.MS.R2Interp.s102_projection_strong
      (d := p.d) (m := wholeSpaceIndex p.d) p.T p.hT).2.1 x
  let ι := ℕ × (ℕ × MultiIndex p.d)
  let S : ℕ → Finset ι := fun n =>
    (HRS.MS.R2Interp.s102_idx p.d n).image (fun q => (n, q))
  let ell : ι → Window p →L[ℝ] ℝ := fun q =>
    HRS.MS.R2Interp.s102_ellp p.hT q.1 q.2
  let b : ℕ → ι → Window p := fun n q =>
    HRS.MS.R2Interp.s102_bpath p.T n q.2
  have hfin : ∀ n x, Pn n x = ∑ q ∈ S n, ell q x • b n q := by
    intro n x
    classical
    rw [HRS.MS.R2Interp.s102_Pj_decomp]
    dsimp [S, ell, b]
    rw [Finset.sum_image]
    intro q _ q' _ h
    exact congrArg Prod.snd h
  let Y : ℝ → (Euc p.d → ℝ) → G0.Ω → ℝ := fun u φ ω =>
    W (J (fp81s21_combinedFeature p R hK u φ)) ω
  have hscal : ∀ n, ∀ q ∈ S n,
      HRS.MC.E213U13.InQ1 hξ hξmeas (fun ω => ell q (Z ω)) := by
    intro n q hq
    classical
    rcases Finset.mem_image.mp hq with ⟨v, hv, rfl⟩
    let t := HRS.MS.R2Interp.s102_node p.hT n v.1
    let φ := oscTestFun (wholeSpaceIndex p.d : ℝ) v.2
    have hφ : IsOscTest (wholeSpaceIndex p.d : ℝ) φ :=
      HRS.MS.GenPath.s56_isOscTest (wholeSpaceIndex p.d : ℝ) v.2
    have hu : 0 ≤ a + (t : ℝ) := add_nonneg ha t.2.1
    have hsrcv := hsrc (a + (t : ℝ)) hu φ hφ
    have hpath := fp81s21_retained_window_eval_ae
      p R G0 a ha t φ Y (fun u hu ψ hψ => (hsrc u hu ψ hψ).1) hφ
    have hEval :
        (fun ω => HRS.MS.R2Interp.s102_ellp p.hT n v (Z ω)) =ᵐ[G0.P]
          fun ω => W (J (fp81s21_combinedFeature p R hK
            (a + (t : ℝ)) φ)) ω := by
      filter_upwards [hpath] with ω hω
      simpa [φ, HRS.MS.R2Interp.s102_ellp,
        HRS.MS.R2Interp.s102_ell_apply, OscDual.eval_oscTestFun] using hω
    exact HRS.MC.E213U13.InQ1_congr hEval.symm hsrcv.2
  have hfirst : HRS.InFirstChaos G0.P ξ 2 Z :=
    HRS.MC.E213U13.inFirstChaos_of_approx
      (P := G0.P) (ξ := ξ) hξ hξmeas
      (W := Z) hZmeas (q := 2) (r := 4)
      (by norm_num : (2 : ℝ) ≤ 2) (by norm_num : (2 : ℝ) < 4) hZ4
      Pn hPn hlim S ell b hfin hscal
  exact ⟨by simpa [Z] using hfirst,
    by simpa [Z, r26t3_Zpath, HRS.law] using hshift.2.1⟩

#print axioms fp81s21_retained_Z_centeredGaussian
#print axioms fp81s21_retained_Z_uniform_fourth
#print axioms fp81s21_retained_Z_firstChaos_conditional

end HRS.Fp81.S21
