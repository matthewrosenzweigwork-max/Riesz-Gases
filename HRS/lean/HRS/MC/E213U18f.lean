import HRS.MC.E213U18e
import HRS.Sections.AdjKAAux6
import HRS.MC.S7PIRA
import HRS.MC.S7FCH4D
import HRS.MC.E213U10P
import HRS.MC.E213U5a

/-!
# Packet e213u18 (part f): identification of the Gaussian window with the limit field `η`

For the canonical Gaussian data `gd`: a.s. `pathEval (Zwin T a ω) τ = embed m (η^{a+τ} ω)`, and the linear functionals
`ω ↦ η^v(ψ)` belong to the Gaussian space of `Zwin H 0`.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.E213U18

open HRS HRS.Sec7 HRS.Main HRS.Uniform HRS.MC.E213O HRS.MC.E213T HRS.MC.E213Plan HRS.MC.E213U11
  HRS.MC.E213U10

variable {d : ℕ}

theorem u18_pathEval_eq {m T : ℝ} (w : PathSpace d m T) (τ : ℝ) : pathEval w τ = pathAt w τ := by
  by_cases h : τ ∈ Set.Icc (0 : ℝ) T <;> simp [pathEval, pathAt, h]

/-- The continuous linear functional `w ↦ w^τ(ψ)` on a path space. -/
def u18_pathCLF (m T τ : ℝ) (hτ : τ ∈ Set.Icc (0 : ℝ) T) {ψ : Torus d → ℝ} (hψ : Torus.IsSmooth ψ) :
    StrongDual ℝ (PathSpace d m T) :=
  (HRS.MC.Sec7.S7PIR.S7PIR_evalCLM m hψ).comp (HRS.MC.Sec7.S7FCH4.S7FCH4_evalCLM (d := d) (r := m) ⟨τ, hτ⟩)

theorem u18_pathCLF_apply {m T τ : ℝ} (hτ : τ ∈ Set.Icc (0 : ℝ) T) {ψ : Torus d → ℝ} (hψ : Torus.IsSmooth ψ)
    (w : PathSpace d m T) :
    u18_pathCLF m T τ hτ hψ w = NegSobolev.eval (pathEval w τ) ψ := by
  unfold u18_pathCLF
  rw [u18_pathEval_eq, show pathAt w τ = w.at' ⟨τ, hτ⟩ from u10_pathAt_eq w ⟨τ, hτ⟩]
  rfl

section GD

variable {S : PreparedData d} {β₀ m : ℝ} {hE : EdgeworthHyp S β₀ m} (gd : GaussData S β₀ hE)

theorem u18_Zwin_pathEval (T : ℝ) (hT : 0 < T) (a : ℝ) (ha : 0 ≤ a) :
    ∀ᵐ ω ∂gd.P₀, ∀ τ ∈ Set.Icc (0 : ℝ) T,
      pathEval (gd.Zwin T a ω) τ = NegSobolev.embed m (gd.η (a + τ) ω) := by
  filter_upwards [u11_eta_cont gd (a + T)] with ω hc τ hτ
  have hc' : ContinuousOn (fun t => gd.η t ω) (Set.Icc a (a + T)) :=
    hc.mono fun t ht => ⟨ha.trans ht.1, ht.2⟩
  rw [u18_pathEval_eq]
  unfold GaussData.Zwin
  rw [u10_pathAt_epath hE T _ hτ,
    show pathAt (procWin (rLvl d) T a gd.η ω) τ = (procWin (rLvl d) T a gd.η ω).at' ⟨τ, hτ⟩ from
      u10_pathAt_eq _ ⟨τ, hτ⟩]
  have := u11_procWin_at gd.η T a ω hc' hT.le ⟨τ, hτ⟩
  rw [this]

theorem u18_Zwin_eval (T : ℝ) (hT : 0 < T) (a : ℝ) (ha : 0 ≤ a) {ψ : Torus d → ℝ} :
    ∀ᵐ ω ∂gd.P₀, ∀ τ ∈ Set.Icc (0 : ℝ) T,
      NegSobolev.eval (pathEval (gd.Zwin T a ω) τ) ψ = NegSobolev.eval (gd.η (a + τ) ω) ψ := by
  filter_upwards [u18_Zwin_pathEval gd T hT a ha] with ω h τ hτ
  rw [h τ hτ]
  exact HRS.AdjK.adjka_eval_embed (rLvl_le hE) _ _

end GD

section Gauss

variable {S : PreparedData d} {β₀ m : ℝ} {hE : EdgeworthHyp S β₀ m} (gd : GaussData S β₀ hE)

theorem u18_Zwin_aemeas (T : ℝ) (hT : 0 < T) : AEMeasurable (gd.Zwin T 0) gd.P₀ := by
  obtain ⟨C, hC⟩ := HRS.MC.E213U11.gd_moments_proof gd T hT
  exact (hC 0 le_rfl).2.1.aemeasurable

theorem u18_Zwin_gauss (T : ℝ) (hT : 0 < T) : IsCenteredGaussian (law gd.P₀ (gd.Zwin T 0)) := by
  obtain ⟨ξ, -, h⟩ := HRS.MC.E213U13.chaos_data_proof gd T hT
  exact (h 0 le_rfl).1

/-- The Gaussian space of the window `[0,H]`. -/
theorem u18_G4 (H : ℝ) (hH : 0 < H) : HRS.MC.QRSpec.Wick.QrpwG4 gd.P₀ (u18_gspace gd.P₀ (gd.Zwin H 0)) :=
  u18_gspace_G4 (u18_Zwin_aemeas gd H hH) (u18_Zwin_gauss gd H hH)

theorem u18_eta_mem (H : ℝ) (hH : 0 < H) {v : ℝ} (hv : v ∈ Set.Icc (0 : ℝ) H) {ψ : Torus d → ℝ}
    (hψ : Torus.IsSmooth ψ) :
    (fun ω => NegSobolev.eval (gd.η v ω) ψ) ∈ u18_gspace gd.P₀ (gd.Zwin H 0) := by
  refine ⟨u18_pathCLF m H v hv hψ, ?_⟩
  filter_upwards [u18_Zwin_eval gd H hH 0 le_rfl (ψ := ψ)] with ω h
  rw [u18_pathCLF_apply hv hψ, h v hv, zero_add]

theorem u18_fc_mem (H : ℝ) (hH : 0 < H) {v : ℝ} (hv : v ∈ Set.Icc (0 : ℝ) H) (k : NonzeroLattice d) :
    (fun ω => NegSobolev.fourierCoeff (gd.η v ω) k) ∈ u18_gspace gd.P₀ (gd.Zwin H 0) := by
  have := u18_eta_mem gd H hH hv (HRS.AdjK.adjkd_isSmooth_realMode k)
  simpa only [HRS.AdjK.adjkd_eval_realMode] using this

end Gauss

section Transfer

variable {S : PreparedData d} {β₀ m : ℝ} {hE : EdgeworthHyp S β₀ m} (gd : GaussData S β₀ hE)

/-- Covariances of any prepared linear Gaussian process equal those of the canonical field `η`. -/
theorem u18_cov_transfer (T : ℝ) (hT : 0 < T) (a : ℝ) (ha : 0 ≤ a)
    (ν : Measure (NegSobolev d m)) (hν : IsCenteredGaussianWithCov m ν (preparedCov d S.s β₀ S.μ0))
    {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (Z₀ : Ω' → NegSobolev d m) (Z : ℝ → Ω' → NegSobolev d m) (hZ : IsPreparedLinear S m (a + T) ν P' Z₀ Z)
    {r t : ℝ} (hr : r ∈ Set.Icc (0 : ℝ) (a + T)) (ht : t ∈ Set.Icc (0 : ℝ) (a + T))
    {ψ φ : Torus d → ℝ} (hψ : Torus.IsSmooth ψ) (hφ : Torus.IsSmooth φ) :
    ∫ ω', NegSobolev.eval (Z r ω') ψ * NegSobolev.eval (Z t ω') φ ∂P' =
      ∫ ω, NegSobolev.eval (gd.η r ω) ψ * NegSobolev.eval (gd.η t ω) φ ∂gd.P₀ := by
  have hH : 0 < a + T := by linarith
  have hZ' : IsPreparedLinear S m (0 + (a + T)) ν P' Z₀ Z := by rwa [zero_add]
  obtain ⟨-, -, -, hg⟩ := HRS.MC.E213U5.Z_universal_proof gd (a + T) hH 0 le_rfl ν hν P' Z₀ Z hZ'
  have hcont : Continuous fun w : PathSpace d m (a + T) =>
      u18_pathCLF m (a + T) r hr hψ w * u18_pathCLF m (a + T) t ht hφ w :=
    (u18_pathCLF m (a + T) r hr hψ).continuous.mul (u18_pathCLF m (a + T) t ht hφ).continuous
  have h1 := hg _ hcont
  have hL : ∀ᵐ ω' ∂P', u18_pathCLF m (a + T) r hr hψ (HRS.Main.windowPath m (a + T) 0 Z ω') *
      u18_pathCLF m (a + T) t ht hφ (HRS.Main.windowPath m (a + T) 0 Z ω') =
      NegSobolev.eval (Z r ω') ψ * NegSobolev.eval (Z t ω') φ := by
    filter_upwards [hZ.sol.cont] with ω' hc
    have hc' : Continuous fun s : Set.Icc (0 : ℝ) (a + T) => Z (0 + (s : ℝ)) ω' := by
      have h2 : ContinuousOn (fun s : ℝ => Z (0 + s) ω') (Set.Icc 0 (a + T)) := by
        simpa only [zero_add] using hc
      exact continuousOn_iff_continuous_restrict.1 h2
    rw [u18_pathCLF_apply hr hψ, u18_pathCLF_apply ht hφ, u18_pathEval_eq, u18_pathEval_eq,
      show pathAt (HRS.Main.windowPath m (a + T) 0 Z ω') r =
        (HRS.Main.windowPath m (a + T) 0 Z ω').at' ⟨r, hr⟩ from u10_pathAt_eq _ ⟨r, hr⟩,
      show pathAt (HRS.Main.windowPath m (a + T) 0 Z ω') t =
        (HRS.Main.windowPath m (a + T) 0 Z ω').at' ⟨t, ht⟩ from u10_pathAt_eq _ ⟨t, ht⟩]
    unfold HRS.Main.windowPath
    rw [HRS.MC.E213O.e213o_toPath_at' _ ω' hc' ⟨r, hr⟩, HRS.MC.E213O.e213o_toPath_at' _ ω' hc' ⟨t, ht⟩]
    simp
  have hR : ∀ᵐ ω ∂gd.P₀, u18_pathCLF m (a + T) r hr hψ (gd.Zwin (a + T) 0 ω) *
      u18_pathCLF m (a + T) t ht hφ (gd.Zwin (a + T) 0 ω) =
      NegSobolev.eval (gd.η r ω) ψ * NegSobolev.eval (gd.η t ω) φ := by
    filter_upwards [u18_Zwin_eval gd (a + T) hH 0 le_rfl (ψ := ψ),
      u18_Zwin_eval gd (a + T) hH 0 le_rfl (ψ := φ)] with ω h1 h2
    rw [u18_pathCLF_apply hr hψ, u18_pathCLF_apply ht hφ, h1 r hr, h2 t ht, zero_add, zero_add]
  rw [integral_congr_ae hL, integral_congr_ae hR] at h1
  exact h1

end Transfer

end HRS.MC.E213U18

end
