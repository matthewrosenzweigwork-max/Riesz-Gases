import HRS.MS.Fp81S21VersionG2
import HRS.MS.Fp81S21VersionTime
import HRS.MS.Fp81S21GaussTimeRep3
import HRS.MS.Fp81S21EmbedIdent

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open Classical MeasureTheory Topology Set
open scoped ENNReal

namespace HRS.Fp81.S21

open HRS.Whole HRS.MS.R26T3 HRS.MS.R26T6 HRS.MS.ProClosureS111

local instance fp81s21_versionGTime_UH_measSpace (H : ℝ) : MeasurableSpace
    (fp81s21_SmoothUH H) := borel _
local instance fp81s21_versionGTime_UH_borelSpace (H : ℝ) : BorelSpace
    (fp81s21_SmoothUH H) := ⟨rfl⟩

/-- Packet 30's canonical Gaussian time class agrees with the time-L² class
of a V1-G continuous version, even when packet 30 selected a different
coefficient representative. The simultaneous physical identity is obtained
from the same V1-G representative by continuity on a dense set of times. -/
theorem fp81s21_gaussian_V2_G_selected
    (p : Parameters)
    {δ : ℝ} (R : Trajectory p δ)
    (Es : r26t6_WeightedChart p.d (2 * p.d + 6) ((p.d : ℝ) + 4))
    (E : r26t6_WeightedChart p.d (2 * p.d + 8) ((p.d : ℝ) + 2))
    (G : GaussianRealization R)
    (a H : ℝ) (ha : 0 ≤ a) (hH : 0 < H)
    (MUG : ℝ) (qsUG : ℝ → G.Ω → r26t6_Coeff) (ε : ℕ → ℝ)
    (hcanonical : fp81s21_gaussian_canonical_time_payload p Es E G.P
      (fun u ω f => OscDual.eval (G.Z u ω) f) MUG qsUG
      (fp81s21_gaussian_embedFamily p Es E qsUG) ε)
    (M : ℝ) (qG : ℝ → G.Ω → r26t6_Coeff)
    (hRep : fp81s21_MomentRep E G.P
      (fun u ω f => OscDual.eval (G.Z u ω) f) qG M)
    (XG : G.Ω → fp81s21_SmoothCH H)
    (hXG : Measurable XG)
    (hsec : ∀ t : Icc (0 : ℝ) H,
      (fun ω => XG ω t) =ᵐ[G.P] qG (a + t)) :
    ∃ UG : G.Ω → fp81s21_SmoothUH H,
      fp81s21_TimeL2Rep G.P
        (fp81s21_gaussian_embedFamily p Es E qsUG) MUG a H UG ∧
      UG =ᵐ[G.P] (fun ω => fp81s21_smoothPathToL2 H hH (XG ω)) ∧
      ∀ᵐ ω ∂G.P, ∀ t : Icc (0 : ℝ) H, ∀ f, IsR2Test f →
        fp81s21_chartAction E (XG ω t) f =
          OscDual.eval (G.Z (a + t) ω) f := by
  obtain ⟨UG, hTimeRep, _⟩ := hcanonical.time_representation a ha H hH
  let qUG : ℝ → G.Ω → r26t6_Coeff := fp81s21_gaussian_embedFamily p Es E qsUG
  have hcanonicalRep : fp81s21_MomentRep E G.P
      (fun u ω f => OscDual.eval (G.Z u ω) f) qUG MUG := by
    simpa [qUG] using hcanonical.coefficients.weak_momentRep
  have hP : (p.d : ℝ) < 2 * ((p.d : ℝ) + 2) := by
    nlinarith [p.hd]
  have huniq : ∀ u, 0 ≤ u → (fun ω => qUG u ω) =ᵐ[G.P] qG u := by
    intro u hu
    exact fp81s21_MomentRep_eq_ae hP E G.P
      (fun u ω f => OscDual.eval (G.Z u ω) f) qUG qG MUG M
      hcanonicalRep hRep u hu
  have hsecUG : ∀ t : Icc (0 : ℝ) H,
      (fun ω => XG ω t) =ᵐ[G.P] qUG (a + t) := by
    intro t
    have hu : 0 ≤ a + (t : ℝ) := add_nonneg ha t.property.1
    filter_upwards [hsec t, huniq (a + t) hu] with ω hx hq
    exact hx.trans hq.symm
  have hUGcore : fp81s21_TimeL2Rep G.P qUG MUG a H UG := by
    refine ⟨hTimeRep.1, hTimeRep.2.1, hTimeRep.2.2.1, ?_⟩
    filter_upwards [hTimeRep.2.2.2] with ω hω
    refine ⟨hω.1, ?_⟩
    filter_upwards [hω.2] with t ht
    exact ht.1
  have hUGeq := fp81s21_TimeL2Rep_eq_continuous_version
    G.P H MUG a hH qUG UG XG hcanonicalRep.1 hUGcore hXG hsecUG

  obtain ⟨Zbar, hZbarMeas, hZbarCont, hZbarEq⟩ :=
    fp81s21_gauss_modification p R G
  letI : Nonempty (Icc (0 : ℝ) H) := ⟨⟨0, le_rfl, hH.le⟩⟩
  let s : ℕ → Icc (0 : ℝ) H := TopologicalSpace.denseSeq _
  have hs : DenseRange s := TopologicalSpace.denseRange_denseSeq _
  have hDense : ∀ᵐ ω ∂G.P, ∀ n, ∀ f, IsR2Test f →
      fp81s21_chartAction E (XG ω (s n)) f =
        OscDual.eval (Zbar (a + s n) ω) f := by
    apply ae_all_iff.mpr
    intro n
    let u : ℝ := a + s n
    have hu : 0 ≤ u := by dsimp [u]; exact add_nonneg ha (s n).property.1
    have hfield := (hRep.2 u hu).2.2
    filter_upwards [hsec (s n), hfield, hZbarEq] with ω hx hω hmod
    intro f hf
    calc
      fp81s21_chartAction E (XG ω (s n)) f =
          fp81s21_chartAction E (qG u ω) f := by rw [hx]
      _ = OscDual.eval (G.Z u ω) f := hω.1 f hf
      _ = OscDual.eval (Zbar u ω) f := by rw [← hmod u hu]

  have hAllZbar : ∀ᵐ ω ∂G.P, ∀ t : Icc (0 : ℝ) H, ∀ f, IsR2Test f →
      fp81s21_chartAction E (XG ω t) f =
        OscDual.eval (Zbar (a + t) ω) f := by
    filter_upwards [hDense] with ω hω
    intro t f hf
    have hchart : Continuous (fun x : Icc (0 : ℝ) H =>
        fp81s21_chartAction E (XG ω x) f) := by
      change Continuous (fun x => inner ℝ (XG ω x) (E.encode f))
      exact (continuous_id.inner continuous_const).comp (XG ω).continuous
    let φ : HRS.MS.S111X1.oscSub p.d (wholeSpaceIndex p.d : ℝ) :=
      ⟨f, r2Test_isOscTest (wholeSpaceIndex p.d : ℝ) hf⟩
    have heval : Continuous (fun z : OscDual p.d (wholeSpaceIndex p.d : ℝ) =>
        OscDual.eval z f) := by
      have hEq : (fun z : OscDual p.d (wholeSpaceIndex p.d : ℝ) =>
          OscDual.eval z f) = fun z => gaussianOscEval φ z := by
        funext z
        exact (gaussianOscEval_apply φ z).symm
      rw [hEq]
      exact (gaussianOscEval φ).continuous
    have hshift : Continuous (fun x : Icc (0 : ℝ) H => a + (x : ℝ)) :=
      continuous_const.add continuous_subtype_val
    have hphysical : Continuous (fun x : Icc (0 : ℝ) H =>
        OscDual.eval (Zbar (a + x) ω) f) :=
      heval.comp ((hZbarCont ω).comp hshift)
    have hseq : (fun x : Icc (0 : ℝ) H =>
        fp81s21_chartAction E (XG ω x) f) ∘ s =
        (fun x : Icc (0 : ℝ) H => OscDual.eval (Zbar (a + x) ω) f) ∘ s := by
      funext n
      exact hω n f hf
    have hfun := DenseRange.equalizer hs hchart hphysical hseq
    exact congrFun hfun t

  have hphysical : ∀ᵐ ω ∂G.P, ∀ t : Icc (0 : ℝ) H, ∀ f, IsR2Test f →
      fp81s21_chartAction E (XG ω t) f =
        OscDual.eval (G.Z (a + t) ω) f := by
    filter_upwards [hAllZbar, hZbarEq] with ω hω hmod
    intro t f hf
    have hu : 0 ≤ a + (t : ℝ) := add_nonneg ha t.property.1
    rw [← hmod (a + t) hu]
    exact hω t f hf
  exact ⟨UG, hUGcore, hUGeq, hphysical⟩

#print axioms HRS.Fp81.S21.fp81s21_gaussian_V2_G_selected

end HRS.Fp81.S21

end
