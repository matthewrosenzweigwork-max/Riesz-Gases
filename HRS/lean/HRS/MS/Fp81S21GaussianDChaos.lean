import HRS.MS.Fp81S21GaussianSourceDensity
import HRS.MS.Fp81S21GaussianQuadraticHilbert15
import HRS.MS.Fp81S21GaussianPropagated
import HRS.MS.Fp81S21WickApprox33
import HRS.MS.Fp81S21GaussianDriftPhysical

/-!
# Same-source second chaos for the selected physical drift

The selected field is `S.qe D.G0`, where `S` is the quadratic component of
packet 31's physical selection (`S.gaussian.quadratic` in the full package).
It is the weak embedded field, not the strong field `S.qs D.G0`.
The physical drift consumer is generic in its field; instantiate it with this
same `qe` and the same origin-zero history used below.

The payload retains oscillator agreement for its own `T`, its own supplied
half-Wick operator `W`, compact agreement for `qs`, and the exact embedding
identity for `qe`. Density recovers the retained-source certificate for `T`;
compact chart tests recover the strong coordinates; the recorded continuous
linear embedding then transports the certificate to `qe`.

Binder adjustment: `InQ2` takes `hξ` and the random variable, but does not take
`hm`. Strict coordinate measurability is still supplied to the Wick and history
lifts. All source coordinates below are literally `measurableXi D`.
The horizon proof is supplied as `hH : 0 ≤ a + p.T`, exactly the proof used by
`timeL2L1`; for physical windows it is `add_nonneg ha p.hT.le`.
The history bound `MB` is retained from `hUB`; it need not be reselected.

The final map is the definition of `gaussian_Dcum` at `a + p.T`.
Spatial constant cancellation `hB0` remains an explicit premise of
`gaussian_Dcum_physical`, where the physical identification is proved; it is
not a premise of chaos membership. No interval starting at `a` is substituted
for the full history starting at zero.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open Classical MeasureTheory Filter Topology
open scoped ENNReal BigOperators

namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R26T6 HRS.MC.E213U13

local instance fp81s21_DChaos_measurableSpace (H : ℝ) : MeasurableSpace
    (Lp r26t6_Coeff 2 (volume.restrict (Set.Icc (0 : ℝ) H))) := borel _
local instance fp81s21_DChaos_borelSpace (H : ℝ) : BorelSpace
    (Lp r26t6_Coeff 2 (volume.restrict (Set.Icc (0 : ℝ) H))) := ⟨rfl⟩

variable {p : Parameters} {δ : ℝ} {R : Trajectory p δ}
variable {hμ₀ : IsProbabilityMeasure (r26t3_mu R 0)}
variable (D : fp81s21_gaussian_source_retained_data p R hμ₀)
variable {Es : r26t6_WeightedChart p.d (2 * p.d + 6) ((p.d : ℝ) + 4)}
variable {E : r26t6_WeightedChart p.d (2 * p.d + 8) ((p.d : ℝ) + 2)}
variable {ε : ℕ → ℝ} (S : fp81s21_QuadraticPhysical31 p R Es E ε)

/-- The selected linear operator, rather than a newly chosen operator, is in
first chaos of the retained source on its entire thermal L² domain. -/
private theorem fp81s21_gaussian_D_selected_T_firstChaos
    (u : ℝ) (hu : 0 ≤ u)
    (f : Lp ℝ 2 (HRS.Whole.withDensityReal R.ρβ)) :
    InFirstChaos D.G0.P (fp81s21_gaussian_source_measurableXi D) 2
      (fun ω => S.T D.G0 u f ω) := by
  obtain ⟨hm, hξ, _, heval⟩ :=
    fp81s21_gaussian_source_measurable_eval_firstChaos D
  let T := S.T D.G0 u
  have hclosed : IsClosed (Qc (K1 hξ hm) : Set (Lp ℝ 2 D.G0.P)) :=
    Submodule.isClosed_topologicalClosure _
  have hpre : IsClosed {x : Lp ℝ 2 (HRS.Whole.withDensityReal R.ρβ) |
      T x ∈ Qc (K1 hξ hm)} := hclosed.preimage T.continuous
  have htests : Set.range (fp81s21_gaussianSourceSpace_oscTestLp p R) ⊆
      {x : Lp ℝ 2 (HRS.Whole.withDensityReal R.ρβ) | T x ∈ Qc (K1 hξ hm)} := by
    rintro x ⟨φ, rfl⟩
    have hag := (S.payload D.G0).2.1 u hu φ.1 φ.2
      (fp81s21_gaussianSourceSpace_oscTest_memLp p R φ)
    have hq : InQ1 hξ hm
        (fun ω => T (fp81s21_gaussianSourceSpace_oscTestLp p R φ) ω) :=
      InQ1_congr hag.symm (s21l_inQ1_of_first hξ hm (heval u hu φ))
    obtain ⟨hmem, hmemQ⟩ := hq
    have heq : hmem.toLp
        (fun ω => T (fp81s21_gaussianSourceSpace_oscTestLp p R φ) ω) =
        T (fp81s21_gaussianSourceSpace_oscTestLp p R φ) :=
      Lp.toLp_coeFn _ hmem
    change T (fp81s21_gaussianSourceSpace_oscTestLp p R φ) ∈ Qc (K1 hξ hm)
    rw [← heq]
    exact hmemQ
  have hTf : T f ∈ Qc (K1 hξ hm) :=
    closure_minimal htests hpre (fp81s21_gaussianSourceSpace_oscTest_dense p R f)
  have hmem : MemLp (fun ω => T f ω) 2 D.G0.P := Lp.memLp _
  have hq : InQ1 hξ hm (fun ω => T f ω) := by
    refine ⟨hmem, ?_⟩
    rw [Lp.toLp_coeFn _ hmem]
    exact hTf
  have h3 : MemLp (fun ω => T f ω) (ENNReal.ofReal (3 : ℝ)) D.G0.P :=
    InQ1.memLp hξ hm hq _
  obtain ⟨c, hc⟩ := firstApprox_of_InQ1 hξ hm hq
    (q := 2) (r := 3) (by norm_num) (by norm_num) h3
  exact ⟨hmem.aestronglyMeasurable, id, c, hc⟩

/-- Each value of the payload's supplied half-Wick operator is in second chaos
of the same retained source. No existential operator is reselected. -/
private theorem fp81s21_gaussian_D_selected_W_InQ2
    (u : ℝ) (hu : 0 ≤ u)
    (k : Lp ℝ 2 ((HRS.Whole.withDensityReal R.ρβ).prod
      (HRS.Whole.withDensityReal R.ρβ))) :
    InQ2 (fp81s21_gaussian_source_measurable_coords_std D).2.2
      (fun ω => S.W D.G0 u k ω) := by
  letI : IsProbabilityMeasure (HRS.Whole.withDensityReal R.ρβ) :=
    HRS.Whole.Q34.isProbabilityMeasure_nu R.thermal.1.1
  obtain ⟨hL, hJoint, hW⟩ := (S.payload D.G0).1 u hu
  rw [hW]
  exact fp81s21_wick_operator_InQ2
    (fp81s21_gaussian_source_measurable_coords_std D).2.2
    (fp81s21_gaussian_source_measurable_coords_std D).1
    (S.T D.G0 u) S.Kstar hL hJoint
    (fp81s21_gaussian_D_selected_T_firstChaos D S u hu) k

private theorem fp81s21_gaussian_D_chart_coordinate
    (z : r26t6_Coeff) (j : ℕ) :
    fp81s21_chartAction Es z (Es.test j) = z j := by
  have he : Es.encode (Es.test j) =
      (lp.single 2 j (1 : ℝ) : r26t6_Coeff) := by
    ext i
    change Es.encode (Es.test j) i = _
    rw [Es.test_coord]
    simp [lp.single_apply, Pi.single_apply, eq_comm]
  rw [fp81s21_chartAction, he]
  simp [lp.inner_single_right]

/-- Compact agreement identifies strong-chart coordinates with the supplied
Wick values: `Es.test j` is a compact smooth test and its encoding is the jth
unit vector. This uses the selected strong field itself. -/
private theorem fp81s21_gaussian_D_strong_InQ2
    (u : ℝ) (hu : 0 ≤ u) (j : ℕ) :
    InQ2 (fp81s21_gaussian_source_measurable_coords_std D).2.2
      (fun ω => S.qs D.G0 u ω j) := by
  obtain ⟨hk, hag⟩ := (S.payload D.G0).2.2.2.2.2.1 u hu
    (Es.test j) (Es.test_smooth j)
  have hW := fp81s21_gaussian_D_selected_W_InQ2 D S u hu
    (hk.toLp (fun xy : Euc p.d × Euc p.d =>
      commutatorKernel p.d p.s (gradient (Es.test j)) xy.1 xy.2))
  have heq : (fun ω => S.qs D.G0 u ω j) =ᵐ[D.G0.P]
      (fun ω => S.W D.G0 u (hk.toLp (fun xy : Euc p.d × Euc p.d =>
        commutatorKernel p.d p.s (gradient (Es.test j)) xy.1 xy.2)) ω) := by
    simpa only [fp81s21_wickChartField, fp81s21_gaussian_D_chart_coordinate] using hag
  exact InQ2.congr_ae heq.symm hW

/-- Coordinate certificate for packet 31's actual weak embedded quadratic
field, on the retained source. The time and slice measurability certificates
come from that same field's retained moment representation. -/
theorem fp81s21_gaussian_qB_secondChaos_coords :
    Measurable (Function.uncurry (S.qe D.G0)) ∧
      ∀ u, 0 ≤ u → MemLp (S.qe D.G0 u) 2 D.G0.P ∧
        ∀ j, InQ2 (fp81s21_gaussian_source_measurable_coords_std D).2.2
          (fun ω => S.qe D.G0 u ω j) := by
  have hs := (S.payload D.G0).2.2.2.1
  have he := (S.payload D.G0).2.2.2.2.1
  refine ⟨he.1, ?_⟩
  intro u hu
  refine ⟨(he.2 u hu).1, ?_⟩
  intro j
  have hmap := fp81s21_InQ2_coeff_functional
    (fp81s21_gaussian_source_measurable_coords_std D).2.2
    (S.qs D.G0 u) (hs.2 u hu).1
    (fp81s21_gaussian_D_strong_InQ2 D S u hu)
    ((lp.evalCLM ℝ (fun _ : ℕ => ℝ) 2 j).comp
      (fp81s21_gaussian_chartEmbed p Es E))
  have heq : (fun ω => S.qe D.G0 u ω j) =
      (fun ω => ((lp.evalCLM ℝ (fun _ : ℕ => ℝ) 2 j).comp
        (fp81s21_gaussian_chartEmbed p Es E)) (S.qs D.G0 u ω)) := by
    funext ω
    rw [(S.payload D.G0).2.2.1 u ω]
    rfl
  rw [heq]
  exact hmap

/-- The selected weak field also agrees with the same supplied Wick operator
on every weighted test in the physical core chart. This records the weighted
identification without changing the selected field or the operator. -/
private theorem fp81s21_gaussian_D_weighted_agreement
    (u : ℝ) (hu : 0 ≤ u) (f : Euc p.d → ℝ)
    (hf : IsR2WeightedTest (2 * p.d + 8) ((p.d : ℝ) + 2) f) :
    ∃ hk : MemLp (fun xy : Euc p.d × Euc p.d =>
      commutatorKernel p.d p.s (gradient f) xy.1 xy.2) 2
        ((HRS.Whole.withDensityReal R.ρβ).prod (HRS.Whole.withDensityReal R.ρβ)),
      (fun ω => fp81s21_chartAction E (S.qe D.G0 u ω) f) =ᵐ[D.G0.P]
        (S.W D.G0 u (hk.toLp (fun xy : Euc p.d × Euc p.d =>
          commutatorKernel p.d p.s (gradient f) xy.1 xy.2)) : D.G0.Ω → ℝ) := by
  have he := (S.payload D.G0).2.2.2.2.1
  apply fp81s21_wick_weighted_agreement p R E D.G0.P (S.W D.G0 u)
    (S.qe D.G0 u) (he.2 u hu).1 ?_ f hf
  intro g hg hk
  obtain ⟨hk', hag⟩ := (S.payload D.G0).2.2.2.2.2.1 u hu g hg
  have hchart : (fun ω => fp81s21_chartAction E (S.qe D.G0 u ω) g) =ᵐ[D.G0.P]
      (fun ω => fp81s21_wickChartField Es (S.qs D.G0) u ω g) := by
    filter_upwards [(he.2 u hu).2.2] with ω hω
    exact hω.1 g hg
  exact hchart.trans hag

/-- The total drift of the same origin-zero history is in second chaos in L³
on the retained source. `MB` is the constant in the supplied history certificate;
no extra coordinate-chaos or source-compatibility premise is assumed.

Unfolding `fp81s21_gaussian_Dcum O hH UB (a + p.T)` gives exactly the random
variable displayed here. Its physical interpretation uses the separate
`fp81s21_gaussian_Dcum_physical` theorem with its explicit spatial-cancellation
hypothesis `hB0`, in addition to its deterministic chart/orbit hypotheses. -/
theorem fp81s21_gaussian_D_secondChaos
    {C : WholeCoeff p.d} {a c K MB : ℝ}
    (hH : 0 ≤ a + p.T)
    (O : r26t6_IntervalOperators E C p.T a c K)
    (UB : D.G0.Ω → Lp r26t6_Coeff 2
      (volume.restrict (Set.Icc (0 : ℝ) (a + p.T))))
    (hUB : fp81s21_TimeL2Rep D.G0.P (S.qe D.G0) MB 0 (a + p.T) UB) :
    InSecondChaos D.G0.P (fp81s21_gaussian_source_measurableXi D) 3
      (fun ω => O.drift 0 (a + p.T)
        (fp81s21_timeL2L1 (a + p.T) hH (UB ω))) := by
  obtain ⟨hq, hcoord⟩ := fp81s21_gaussian_qB_secondChaos_coords D S
  exact (fp81s21_TimeL2Rep_secondChaos
    (fp81s21_gaussian_source_measurable_coords_std D).2.2
    (fp81s21_gaussian_source_measurable_coords_std D).1
    (S.qe D.G0) MB 0 (a + p.T) le_rfl hH UB hq hUB hcoord
    ((O.drift 0 (a + p.T)).comp (fp81s21_timeL2L1 (a + p.T) hH))).2

/-- The named cumulative correction at the full horizon has the same second-chaos
certificate. This is the literal `Dcum` definition; the physical identification
still uses the explicit `hB0` premise of `fp81s21_gaussian_Dcum_physical`. -/
theorem fp81s21_gaussian_Dcum_secondChaos
    {C : WholeCoeff p.d} {a c K MB : ℝ}
    (hH : 0 ≤ a + p.T)
    (O : r26t6_IntervalOperators E C p.T a c K)
    (UB : D.G0.Ω → Lp r26t6_Coeff 2
      (volume.restrict (Set.Icc (0 : ℝ) (a + p.T))))
    (hUB : fp81s21_TimeL2Rep D.G0.P (S.qe D.G0) MB 0 (a + p.T) UB) :
    InSecondChaos D.G0.P (fp81s21_gaussian_source_measurableXi D) 3
      (fp81s21_gaussian_Dcum O hH UB (a + p.T)) := by
  exact fp81s21_gaussian_D_secondChaos D S hH O UB hUB

#print axioms fp81s21_gaussian_D_selected_T_firstChaos
#print axioms fp81s21_gaussian_D_selected_W_InQ2
#print axioms fp81s21_gaussian_D_chart_coordinate
#print axioms fp81s21_gaussian_D_strong_InQ2
#print axioms fp81s21_gaussian_qB_secondChaos_coords
#print axioms fp81s21_gaussian_D_weighted_agreement
#print axioms fp81s21_gaussian_D_secondChaos
#print axioms fp81s21_gaussian_Dcum_secondChaos

end HRS.Fp81.S21
end
