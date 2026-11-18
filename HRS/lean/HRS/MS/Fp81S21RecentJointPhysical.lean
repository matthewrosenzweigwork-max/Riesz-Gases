import HRS.MS.Fp81S21PredictionPhysical
import HRS.MS.Fp81S21RecentBVPhysical3
import HRS.MS.Fp81S21RecentJointTransport

/-! Whole-packet recent physical law, retaining packet 32's selected witnesses. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open Classical MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal RealInnerProductSpace
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R26T6 HRS.MS.R2Interp HRS.MS.CovMeas

local instance fp81s21_recentJoint_CH_meas (H : ℝ) : MeasurableSpace (CH H) := borel _
local instance fp81s21_recentJoint_CH_borel (H : ℝ) : BorelSpace (CH H) := ⟨rfl⟩
local instance fp81s21_recentJoint_UH_meas (H : ℝ) : MeasurableSpace (UH H) := borel _
local instance fp81s21_recentJoint_UH_borel (H : ℝ) : BorelSpace (UH H) := ⟨rfl⟩
local instance fp81s21_recentJoint_YH_meas (p : Parameters) (H : ℝ) :
    MeasurableSpace (YH p H) := borel _
local instance fp81s21_recentJoint_YH_borel (p : Parameters) (H : ℝ) :
    BorelSpace (YH p H) := ⟨rfl⟩

/-- The radius precedes trajectories; the interval operators and prediction
bound precede every window. The covariance coordinate uses the raw linear path.
The six epsilon certificates are retained for compatible downstream selection.
Proof binders `hc`, `hK`, `hL`, `ha` name the carrier's dependent parameters. -/
def fp81s21_RecentJointPhysicalSpec (p : Parameters) : Prop :=
    ∃ Es : r26t6_WeightedChart p.d (2 * p.d + 6) ((p.d : ℝ) + 4),
    ∃ E : r26t6_WeightedChart p.d (r p) (Pw p),
    ∃ εAvg : ℕ → ℝ, (∀ k, 0 ≤ εAvg k) ∧ Tendsto εAvg atTop (𝓝 0) ∧
    ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ 1 / 2 ∧
    ∀ δ : ℝ, 0 < δ → δ ≤ δ0 → ∀ R : Trajectory p δ,
    ∃ MUG : ℝ, 0 ≤ MUG ∧
    ∃ canon : fp81s21_gaussian_V2_G_canonicalFamily p Es E R MUG εAvg,
    ∃ εN εG εB : ℕ → ℝ,
      (∀ k, 0 ≤ εN k) ∧ Tendsto εN atTop (𝓝 0) ∧
      (∀ k, 0 ≤ εG k) ∧ Tendsto εG atTop (𝓝 0) ∧
      (∀ k, 0 ≤ εB k) ∧ Tendsto εB atTop (𝓝 0) ∧
    ∃ S31 : fp81s21_Physical31 p R Es E εN εG εB,
    ∃ c : ℝ, ∃ hc : 0 < c, ∃ K : ℝ, ∃ hK : 0 ≤ K,
    ∃ Kpred : ℝ, 0 ≤ Kpred ∧
    ∃ O : (a : ℝ) → 0 ≤ a → r26t6_IntervalOperators E (r26t3_coeff R) p.T a c K,
    ∀ L : ℝ, ∀ hL : 0 < L,
      let H := L + p.T
      let T := fp81s21_smoothPathToL2 H (add_pos hL p.hT)
      let dL := K * Real.sqrt H
      let jL := K * |2 * (r26t3_coeff R).ν| * Real.sqrt H
      let CL := max Kpred (max dL (jL * ‖T‖))
      let MBG := S31.gaussian.quadratic.Kstar ^ 4 * S31.gaussian.quadratic.B / 2
      ∃ e e33 : ℕ → ℝ, ∃ M33 : ℝ, 0 ≤ M33 ∧
        (∀ N, 0 ≤ e N) ∧ Tendsto e atTop (𝓝 0) ∧
        e33 = (fun N => 2 * CL * e N) ∧
        (∀ N, 0 ≤ e33 N) ∧ Tendsto e33 atTop (𝓝 0) ∧
      ∃ P : (a : ℝ) → 0 ≤ a → CH H →L[ℝ] YH p H,
        (∀ a ha, ‖P a ha‖ ≤ Kpred ∧ PSpec p R E L a (P a ha)) ∧
      ∀ N : ℕ, ∀ hN : 2 ≤ N, ∀ A : Particle R N,
      ∀ G : GaussianRealization R, ∀ a : ℝ, ∀ ha : 0 ≤ a,
        let b := max (a - L) 0
        let D := fp81s21_VDtransport p a ha L hL c K (O a ha) hK hc.le
        let J := fp81s21_VJtransport p a ha L hL c K (O a ha) hK hc.le
        letI : MeasurableSpace (fp81s21_VD p a ha L hL c K (O a ha) hK hc.le) := borel _
        letI : MeasurableSpace (fp81s21_VJ p a ha L hL c K (O a ha) hK hc.le) := borel _
        ∃ XN : A.Ω → CH H, ∃ XG : G.Ω → CH H,
        ∃ UBN : A.Ω → UH H, ∃ UBG : G.Ω → UH H,
        ∃ YN : A.Ω → YH p H, ∃ YG : G.Ω → YH p H,
          CD E A.P (fp81s21_particleEmpField R N A) b H XN ∧
          CD E G.P (fun u ω f => OscDual.eval (G.Z u ω) f) b H XG ∧
          fp81s21_TimeL2Rep A.P (fun u ω => fp81s21_particle_embedField p Es E
            (S31.qsBN N hN A u ω)) S31.MN b H UBN ∧
          fp81s21_TimeL2Rep G.P (S31.gaussian.quadratic.qe G)
            (S31.gaussian.quadratic.Kstar ^ 4 * S31.gaussian.quadratic.B / 2) b H UBG ∧
          (∫ ω, XG ω ∂G.P) = 0 ∧
          GA p R E G (S31.gaussian.quadratic.T G) b H XG ∧
          YN = (fun ω => P a ha (cen A.P XN ω)) ∧
          YG = (fun ω => P a ha (cen G.P XG ω)) ∧
          Measurable YN ∧ MemLp YN 2 A.P ∧ Measurable YG ∧ MemLp YG 2 G.P ∧
          NId p R A L a YN ∧ GId p R E G L a XG YG ∧
          wassersteinE 2 (law A.P (fun ω => (XN ω, UBN ω)))
            (law G.P (fun ω => (XG ω, UBG ω))) ≤ ENNReal.ofReal (e N) ∧
          wassersteinE 2 (law A.P (fun ω => (cen A.P XN ω, cen A.P UBN ω)))
            (law G.P (fun ω => (cen G.P XG ω, cen G.P UBG ω))) ≤ ENNReal.ofReal (2 * e N) ∧
          wassersteinE 2 (law A.P (fun ω => (YN ω, cen A.P UBN ω)))
            (law G.P (fun ω => (YG ω, cen G.P UBG ω))) ≤ ENNReal.ofReal (max 1 Kpred * (2 * e N)) ∧
          fp81s21_BVLaw p R A.P E (fp81s21_particleEmpField R N A)
            (fp81s21_particleQuadField R N A) S31.MN S31.MN a L c K ha hL
            (O a ha) hK hc.le (fun ω => D (UBN ω)) (fun ω => J (T (XN ω))) ∧
          fp81s21_BVLaw p R G.P E
            (fun u ω f => fp81s21_chartAction E
              (fp81s21_gaussian_embedFamily p Es E (canon.q G) u ω) f)
            (fun u ω f => fp81s21_chartAction E (S31.gaussian.quadratic.qe G u ω) f)
            MUG MBG a L c K ha hL (O a ha) hK hc.le
            (fun ω => D (UBG ω)) (fun ω => J (T (XG ω))) ∧
          (∫ ω, (‖D (UBN ω)‖ ^ 2 + ‖J (T (XN ω))‖ ^ 2) ∂A.P) ≤ M33 ∧
          (∫ ω, (‖D (UBG ω)‖ ^ 2 + ‖J (T (XG ω))‖ ^ 2) ∂G.P) ≤ M33 ∧
          wassersteinE 2
            (law A.P (fun ω => (P a ha (cen A.P XN ω), (D (UBN ω), J (T (XN ω))))))
            (law G.P (fun ω => (P a ha (cen G.P XG ω), (D (UBG ω), J (T (XG ω)))))) ≤
              ENNReal.ofReal (e33 N)

#print axioms fp81s21_RecentJointPhysicalSpec
end HRS.Fp81.S21
