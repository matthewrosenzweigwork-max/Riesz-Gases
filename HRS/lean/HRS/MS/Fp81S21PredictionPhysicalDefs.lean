import HRS.MS.Fp81S21PredMap11
import HRS.MS.Fp81S21CenteredJointComparison
import HRS.MS.Fp81S21SLin

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open Classical MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal RealInnerProductSpace

namespace HRS.Fp81.S21

open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R26T6 HRS.MS.R2Interp HRS.MS.CovMeas

abbrev I (H : ℝ) := Set.Icc (0 : ℝ) H
abbrev F := r26t6_Coeff
abbrev CH (H : ℝ) := fp81s21_SmoothCH H
abbrev UH (H : ℝ) := fp81s21_SmoothUH H
abbrev YH (p : Parameters) (H : ℝ) := ContinuousMap (I H) (Window p)
abbrev m (p : Parameters) := (wholeSpaceIndex p.d : ℝ)
abbrev r (p : Parameters) := 2 * p.d + 8
abbrev Pw (p : Parameters) := (p.d : ℝ) + 2

def cen {Ω B : Type*} [MeasurableSpace Ω] [NormedAddCommGroup B]
    [NormedSpace ℝ B] [CompleteSpace B]
    (μ : Measure Ω) (X : Ω → B) : Ω → B :=
  fun ω => X ω - ∫ ω', X ω' ∂μ

def CD {p : Parameters} {Ω : Type*} [MeasurableSpace Ω]
    (E : r26t6_WeightedChart p.d (r p) (Pw p)) (μ : Measure Ω)
    (Q : ℝ → Ω → (Euc p.d → ℝ) → ℝ) (b H : ℝ) (X : Ω → CH H) : Prop :=
  Measurable X ∧ MemLp X 2 μ ∧
    ∀ᵐ ω ∂μ, ∀ t : I H, ∀ f, IsR2Test f →
      fp81s21_chartAction E (X ω t) f = Q (b + (t : ℝ)) ω f

def Qext {p : Parameters} {Ω : Type*}
    (E : r26t6_WeightedChart p.d (r p) (Pw p)) (b H : ℝ)
    (X : Ω → CH H) (ω : Ω) (u : ℝ) : (Euc p.d → ℝ) → ℝ :=
  if hu : u - b ∈ I H then
    fp81s21_chartAction E (X ω ⟨u - b, hu⟩)
  else 0

local instance fp81s21_prediction_CH_measSpace (H : ℝ) :
    MeasurableSpace (CH H) := borel _
local instance fp81s21_prediction_CH_borelSpace (H : ℝ) :
    BorelSpace (CH H) := ⟨rfl⟩
local instance fp81s21_prediction_UH_measSpace (H : ℝ) :
    MeasurableSpace (UH H) := borel _
local instance fp81s21_prediction_UH_borelSpace (H : ℝ) :
    BorelSpace (UH H) := ⟨rfl⟩
local instance fp81s21_prediction_YH_measSpace (p : Parameters) (H : ℝ) :
    MeasurableSpace (YH p H) := borel _
local instance fp81s21_prediction_YH_borelSpace (p : Parameters) (H : ℝ) :
    BorelSpace (YH p H) := ⟨rfl⟩

def PSpec (p : Parameters) {δ : ℝ} (R : Trajectory p δ)
    (E : r26t6_WeightedChart p.d (r p) (Pw p)) (L a : ℝ)
    (P : CH (L + p.T) →L[ℝ] YH p (L + p.T)) : Prop :=
  let H := L + p.T
  let b := max (a - L) 0
  let θ := a - b
  ∀ x : CH H, ∀ v : I H, ∀ τ : I p.T,
    let s : ℝ := min (v : ℝ) (θ + (τ : ℝ))
    ∀ hs : s ∈ I H,
      OscPath.at' (P x v) τ =
        r2Vprop (r26t3_coeff R) (m p) (a + (τ : ℝ)) (b + s)
          (fp81s21_chartAction E (x ⟨s, hs⟩))

def NId (p : Parameters) {δ : ℝ} (R : Trajectory p δ) {N : ℕ}
    (A : Particle R N) (L a : ℝ) (Y : A.Ω → YH p (L + p.T)) : Prop :=
  let H := L + p.T
  let b := max (a - L) 0
  let θ := a - b
  let h := θ + p.T
  ∀ᵐ ω ∂A.P, ∀ v : I H, ∀ τ : I p.T,
    OscPath.at' (Y ω v) τ =
      r2PathAt (s102_Y (r26t3_coeff R) (m p) (b + H) A.P A.X ω
        (b + min (v : ℝ) h)) (a + (τ : ℝ))

def GId (p : Parameters) {δ : ℝ} (R : Trajectory p δ)
    (E : r26t6_WeightedChart p.d (r p) (Pw p))
    (G : GaussianRealization R) (L a : ℝ)
    (X : G.Ω → CH (L + p.T)) (Y : G.Ω → YH p (L + p.T)) : Prop :=
  let H := L + p.T
  let b := max (a - L) 0
  let θ := a - b
  let h := θ + p.T
  ∀ᵐ ω ∂G.P, ∀ v : I H, ∀ τ : I p.T,
    OscPath.at' (Y ω v) τ =
      r2PathAt (r2Predicted (r26t3_coeff R)
        (windowPathOf (m p) (b + H) 0 (fun u => G.Z u ω))
        (Qext E b H X ω) (b + min (v : ℝ) h)) (a + (τ : ℝ))

def GA (p : Parameters) {δ : ℝ} (R : Trajectory p δ)
    (E : r26t6_WeightedChart p.d (r p) (Pw p))
    (G : GaussianRealization R)
    (T : ℝ → Lp ℝ 2 (HRS.Whole.withDensityReal R.ρβ) →L[ℝ]
      Lp ℝ 2 G.P)
    (b H : ℝ) (X : G.Ω → CH H) : Prop :=
  ∀ s : I H, ∀ f, IsR2WeightedTest (r p) (Pw p) f →
    ∃ hf : MemLp f 2 (HRS.Whole.withDensityReal R.ρβ),
      (fun ω => fp81s21_chartAction E (X ω s) f) =ᵐ[G.P]
        (T (b + (s : ℝ)) (hf.toLp f) : G.Ω → ℝ)

theorem recent_geometry (L a : ℝ) (hL : 0 < L) (ha : 0 ≤ a) :
    let b := max (a - L) 0
    0 ≤ b ∧ 0 ≤ a - b ∧ a - b ≤ L ∧ b + (a - b) = a := by
  dsimp only
  by_cases hle : a ≤ L
  · rw [max_eq_right (sub_nonpos.mpr hle)]
    simpa using (⟨le_rfl, ha, hle, by ring⟩ :
      0 ≤ 0 ∧ 0 ≤ a ∧ a ≤ L ∧ 0 + a = a)
  · have hLa : L ≤ a := le_of_not_ge hle
    rw [max_eq_left (sub_nonneg.mpr hLa)]
    constructor
    · linarith
    constructor
    · nlinarith
    constructor
    · nlinarith
    · ring

theorem recent_operator (p : Parameters) {δ : ℝ} (R : Trajectory p δ)
    (E : r26t6_WeightedChart p.d (r p) (Pw p))
    (c : MultiIndex p.d → ℝ)
    (hD : ∀ T : ℝ, 0 < T →
      S101Data (r26t3_coeff R) (m p) T (r p) c)
    (L : ℝ) (hL : 0 < L) :
    ∃ P : (a : ℝ) → 0 ≤ a → CH (L + p.T) →L[ℝ] YH p (L + p.T),
      ∀ a ha, ‖P a ha‖ ≤ s102_KV p.d (r p) (Pw p) c ∧
        PSpec p R E L a (P a ha) := by
  let H : ℝ := L + p.T
  have hH : 0 < H := by dsimp [H]; linarith [p.hT]
  have hPdim : (p.d : ℝ) < 2 * Pw p := by
    have hd : (2 : ℝ) ≤ (p.d : ℝ) := by exact_mod_cast p.hd
    dsimp [Pw]
    nlinarith
  have hforall : ∀ a : ℝ, ∀ ha : 0 ≤ a,
      ∃ P : CH H →L[ℝ] YH p H,
        ‖P‖ ≤ s102_KV p.d (r p) (Pw p) c ∧ PSpec p R E L a P := by
    intro a ha
    let b : ℝ := max (a - L) 0
    let θ : ℝ := a - b
    have hgeom := recent_geometry L a hL ha
    have hb : 0 ≤ b := hgeom.1
    have hθ : 0 ≤ θ := hgeom.2.1
    have hθL : θ ≤ L := hgeom.2.2.1
    have hsum : b + θ = a := hgeom.2.2.2
    have hgeo : θ + p.T ≤ H := by dsimp [H]; linarith
    have hTpos : 0 < b + H := by linarith [hb, hH]
    obtain ⟨P₀, hNorm, hEval⟩ :=
      fp81s21_recentPred_exists
        (d := p.d) (r := r p) (Pw := Pw p) (m := m p)
        (T := b + H) (b := b) (H := H) (S := p.T) (θ := θ)
        (C := r26t3_coeff R) (c := c)
        hPdim (hD (b + H) hTpos)
        (fp81s21_S102Lin p R (b + H)) E hb hθ p.hT.le hgeo le_rfl
    refine ⟨P₀, hNorm, ?_⟩
    change ∀ x : CH H, ∀ v : I H, ∀ τ : I p.T,
      let s : ℝ := min (v : ℝ) (θ + (τ : ℝ))
      ∀ hs : s ∈ I H,
        OscPath.at' (P₀ x v) τ =
          r2Vprop (r26t3_coeff R) (m p) (a + (τ : ℝ)) (b + s)
            (fp81s21_chartAction E (x ⟨s, hs⟩))
    intro x v τ
    dsimp only
    intro hs
    have h := hEval x v τ
    simpa [fp81s21_predSource, hsum] using h
  refine ⟨fun a ha => Classical.choose (hforall a ha), ?_⟩
  intro a ha
  exact Classical.choose_spec (hforall a ha)

#print axioms HRS.Fp81.S21.recent_geometry
#print axioms HRS.Fp81.S21.recent_operator

end HRS.Fp81.S21
