import HRS.MS.Fp81S21MovingHeatIto

/-!
# S2.1(iii), packet 18c: partition concatenation for the moving heat Itô formula

Each interval uses the full-horizon prediction and the pulled-back test
`Φ (W_a (P_L^H w))`, with `H = a + p.T`.  The partition condition says every
projection-grid point in the closed interval is a partition vertex.  Strict
ordering then gives the no-grid-interior hypothesis required by the stopped
piece theorem.  At a shared endpoint, both stopped formulas evaluate the same
`r2HeatFn` expression, so the endpoint values match without choosing or
matching separate heat extensions.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators MatrixOrder Matrix

namespace HRS.Fp81.S21

open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R2Interp HRS.MS.CovMeas
open HRS.MC.Sec7.PI HRS.MC.Sec7.S7PIF6

/-- The finite-level moving Itô drift plus covariance rate on the full horizon.
The cylindrical test is `G x = Φ (W_a (s102_Lam H L x))`, the coordinate form of
`Φ (W_a (P_L^H w))` used by the stopped-piece formula. -/
noncomputable def fp81s21_moving_heat_ito_rate
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ)
    {N : ℕ} (A : Particle R N) (F : FilteredParticle A)
    (a : ℝ) (ha : 0 ≤ a) (hH : 0 < a + p.T)
    (L : ℕ) (Φ : Window p → ℝ) (ζ : A.Ω) (u : ℝ) : ℝ := by
  let H : ℝ := a + p.T
  let C : WholeCoeff p.d := r26t3_coeff R
  let m : ℝ := (wholeSpaceIndex p.d : ℝ)
  let τ : Fin (s102_q p.d L) → Icc (0 : ℝ) H := s102_tauk hH L
  let α : Fin (s102_q p.d L) → MultiIndex p.d := s102_alk L
  let W : OscPath p.d (wholeSpaceIndex p.d : ℝ) H →L[ℝ] Window p :=
    HRS.MS.ProClosureS111.physicalWindowRestriction
      (d := p.d) (m := (wholeSpaceIndex p.d : ℝ)) (T := p.T)
      (H := H) ha le_rfl
  let G : EuclideanSpace ℝ (Fin (s102_q p.d L)) → ℝ :=
    fun x => Φ (W (s102_Lam H L x))
  exact
    -(Real.sqrt N)⁻¹ *
        (∑ i, fderiv ℝ (gaussHeat (s102_obsCov C m τ α) G u)
          (s102_obs τ α
            (s102_Y C m H A.P A.X ζ u))
          (EuclideanSpace.single i 1) *
          s102_hh C m τ α
            (fun v => r2QuadField p.s (r26t3_mu R v) A.P F.X v ζ) i u) +
      (1 / (2 * Real.sqrt N)) *
        (∑ i, ∑ j, iteratedFDeriv ℝ 2
          (gaussHeat (s102_obsCov C m τ α) G u)
          (s102_obs τ α
            (s102_Y C m H A.P A.X ζ u))
          ![EuclideanSpace.single i 1, EuclideanSpace.single j 1] *
          (2 * C.ν * s102_hh2 C m τ α
            (fun v => s102_etaf (r26t3_mu R v) F.X ζ v) i j u))

/-- The finite-level endpoint value with the physical-window test pulled back
through the full-horizon projection. -/
noncomputable def fp81s21_moving_heat_ito_endpoint
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ)
    {N : ℕ} (A : Particle R N)
    (a : ℝ) (ha : 0 ≤ a) (hH : 0 < a + p.T)
    (future : (H : ℝ) → ℝ →
      Measure (OscPath p.d (wholeSpaceIndex p.d : ℝ) H))
    (L : ℕ) (Φ : Window p → ℝ) (u : ℝ) (ζ : A.Ω) : ℝ := by
  let H : ℝ := a + p.T
  let C : WholeCoeff p.d := r26t3_coeff R
  let m : ℝ := (wholeSpaceIndex p.d : ℝ)
  let W : OscPath p.d (wholeSpaceIndex p.d : ℝ) H →L[ℝ] Window p :=
    HRS.MS.ProClosureS111.physicalWindowRestriction
      (d := p.d) (m := (wholeSpaceIndex p.d : ℝ)) (T := p.T)
      (H := H) ha le_rfl
  exact r2HeatFn (future H) (fun w => Φ (W (s102_Pj H hH L w))) u
    (s102_Y C m H A.P A.X ζ u)

/-- Concatenation of finitely many adjacent interval Itô formulas.  The local
hypothesis `hpieces` is supplied by applying the moving stopped-piece theorem
on each grid-free interval. -/
private theorem fp81s21_moving_heat_ito_partition_from_pieces
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (V : ℝ → Ω → ℝ) (D : Ω → ℝ → ℝ)
    (q : ℕ → ℝ) (n : ℕ)
    (hmono : ∀ i j, i ≤ j → j ≤ n → q i ≤ q j)
    (hpieces : ∀ i < n, ∃ M : Ω → ℝ,
      Integrable M P ∧ (∫ ω, M ω ∂P = 0) ∧
      ∀ᵐ ω ∂P,
        IntegrableOn (D ω) (Ioc (q i) (q (i + 1))) ∧
        V (q (i + 1)) ω - V (q i) ω =
          (∫ u in Ioc (q i) (q (i + 1)), D ω u) + M ω) :
    ∃ M : Ω → ℝ, Integrable M P ∧ (∫ ω, M ω ∂P = 0) ∧
      ∀ᵐ ω ∂P,
        IntegrableOn (D ω) (Ioc (q 0) (q n)) ∧
        V (q n) ω - V (q 0) ω =
          (∫ u in Ioc (q 0) (q n), D ω u) + M ω := by
  classical
  let Q : ℕ → Prop := fun j =>
    ∃ M : Ω → ℝ, Integrable M P ∧ (∫ ω, M ω ∂P = 0) ∧
      ∀ᵐ ω ∂P,
        IntegrableOn (D ω) (Ioc (q 0) (q j)) ∧
        V (q j) ω - V (q 0) ω =
          (∫ u in Ioc (q 0) (q j), D ω u) + M ω
  have hbase : Q 0 := by
    refine ⟨fun _ => 0, integrable_zero _ _ _, by simp, ?_⟩
    exact Filter.Eventually.of_forall fun ω => by
      constructor <;> simp
  have hstep : ∀ i, i < n → Q i → Q (i + 1) := by
    intro i hi ⟨M₁, hM₁i, hM₁0, hM₁⟩
    obtain ⟨M₂, hM₂i, hM₂0, hM₂⟩ := hpieces i hi
    refine ⟨fun ω => M₁ ω + M₂ ω, hM₁i.add hM₂i, ?_, ?_⟩
    · rw [integral_add hM₁i hM₂i, hM₁0, hM₂0]
      simp
    · filter_upwards [hM₁, hM₂] with ω h₁ h₂
      rcases h₁ with ⟨hI₁, hE₁⟩
      rcases h₂ with ⟨hI₂, hE₂⟩
      have hu : Ioc (q 0) (q i) ∪ Ioc (q i) (q (i + 1)) =
          Ioc (q 0) (q (i + 1)) :=
        Ioc_union_Ioc_eq_Ioc
          (hmono 0 i (Nat.zero_le _) (by omega))
          (hmono i (i + 1) (by omega) (by omega))
      have hI : IntegrableOn (D ω) (Ioc (q 0) (q (i + 1))) := by
        rw [← hu]
        exact hI₁.union hI₂
      refine ⟨hI, ?_⟩
      have hsplit :
          (∫ u in Ioc (q 0) (q (i + 1)), D ω u) =
            (∫ u in Ioc (q 0) (q i), D ω u) +
              ∫ u in Ioc (q i) (q (i + 1)), D ω u := by
        rw [← hu, setIntegral_union
          (Set.disjoint_left.2 fun z hz hz' =>
            absurd hz.2 (not_le.2 hz'.1))
          measurableSet_Ioc hI₁ hI₂]
      calc
        V (q (i + 1)) ω - V (q 0) ω =
            (V (q (i + 1)) ω - V (q i) ω) +
              (V (q i) ω - V (q 0) ω) := by ring
        _ = ((∫ u in Ioc (q i) (q (i + 1)), D ω u) + M₂ ω) +
              ((∫ u in Ioc (q 0) (q i), D ω u) + M₁ ω) := by
            rw [hE₂, hE₁]
        _ = (∫ u in Ioc (q 0) (q (i + 1)), D ω u) +
              (M₁ ω + M₂ ω) := by rw [hsplit]; ring
  have hall : ∀ i ≤ n, Q i := by
    intro i
    induction i with
    | zero =>
        intro _
        exact hbase
    | succ i ih =>
        intro hi
        exact hstep i (by omega) (ih (by omega))
  simpa [Q] using hall n le_rfl

/-- The moving finite-projection heat Itô identity on a finite partition
`q 0 < ... < q n` of `[q 0,q n]`.  Every full-horizon projection-grid point in
that interval is a vertex.  Consequently, no grid point lies in an open piece,
and `fp81s21_moving_heat_ito_piece` applies on each consecutive pair.  The
martingale in the conclusion is the finite sum of the piece martingales; it is
integrable and has expectation zero.  The endpoint test stays
`Φ (W_a (P_L^H w))` at every vertex. -/
theorem fp81s21_moving_heat_ito_partition
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ)
    (hδ : 0 < δ) (hδh : δ ≤ 1 / 2)
    (a : ℝ) (ha : 0 ≤ a) (hH : 0 < a + p.T)
    {N : ℕ} (hN : 2 ≤ N) (A : Particle R N) (F : FilteredParticle A)
    {r0 : ℕ} {c : MultiIndex p.d → ℝ}
    (hstd : Fp81MovingStd (r26t3_coeff R)
      (wholeSpaceIndex p.d : ℝ) (a + p.T) r0 c hH)
    (hlin : S102Lin (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ) (a + p.T))
    (hr0 : (p.d : ℝ) / 2 + 2 < r0)
    (hphys : Fp81MovingPhysicalInputs R hN A (a + p.T))
    (future : (H : ℝ) → ℝ →
      Measure (OscPath p.d (wholeSpaceIndex p.d : ℝ) H))
    (hfuture : fp81s21_moving_heat_full_clause p R future)
    (L : ℕ) {n : ℕ} (hn : 1 ≤ n) (q : ℕ → ℝ)
    (hq0 : 0 ≤ q 0) (hqstep : ∀ i < n, q i < q (i + 1))
    (hqend : q n ≤ a + p.T)
    (hgrid : ∀ k : Fin (s102_q p.d L),
      q 0 ≤ (s102_tk hH L k : ℝ) →
      (s102_tk hH L k : ℝ) ≤ q n →
      ∃ i : ℕ, i ≤ n ∧ (s102_tk hH L k : ℝ) = q i)
    (Φ : Window p → ℝ) (hΦ : MemCb 5 Φ) :
    q 0 < q n ∧
      ∃ Mart : A.Ω → ℝ, Integrable Mart A.P ∧
        (∫ ζ, Mart ζ ∂A.P = 0) ∧
        ∀ᵐ ζ ∂A.P,
          IntegrableOn
            (fp81s21_moving_heat_ito_rate p R A F a ha hH L Φ ζ)
            (Ioc (q 0) (q n)) ∧
          fp81s21_moving_heat_ito_endpoint
              p R A a ha hH future L Φ (q n) ζ -
            fp81s21_moving_heat_ito_endpoint
              p R A a ha hH future L Φ (q 0) ζ =
            (∫ u in Ioc (q 0) (q n),
              fp81s21_moving_heat_ito_rate p R A F a ha hH L Φ ζ u) + Mart ζ := by
  classical
  have hmonoAux : ∀ j, ∀ i, i ≤ j → j ≤ n → q i ≤ q j := by
    intro j
    induction j with
    | zero =>
        intro i hij hjn
        have : i = 0 := by omega
        subst i
        exact le_rfl
    | succ j ih =>
        intro i hij hjn
        by_cases hEq : i = j + 1
        · subst i
          exact le_rfl
        · have hij' : i ≤ j := by omega
          have hprev := ih i hij' (by omega)
          exact hprev.trans (hqstep j (by omega)).le
  have hmono : ∀ i j, i ≤ j → j ≤ n → q i ≤ q j := by
    intro i j hij hjn
    exact hmonoAux j i hij hjn
  have hlt : q 0 < q n := by
    have h01 : q 0 < q 1 := hqstep 0 (by omega)
    have h1n : q 1 ≤ q n := hmono 1 n (by omega) le_rfl
    exact h01.trans_le h1n
  have hno : ∀ i < n, ∀ k : Fin (s102_q p.d L),
      ¬ (q i < (s102_tk hH L k : ℝ) ∧
        (s102_tk hH L k : ℝ) < q (i + 1)) := by
    intro i hi k hbetween
    have h0i : q 0 ≤ q i := hmono 0 i (by omega) (by omega)
    have hin : q i ≤ q n := hmono i n (by omega) le_rfl
    have hin' : q (i + 1) ≤ q n := hmono (i + 1) n (by omega) le_rfl
    obtain ⟨j, hjn, hjk⟩ := hgrid k
      (h0i.trans hbetween.1.le) (hbetween.2.le.trans hin')
    by_cases hji : j ≤ i
    · have hji' : q j ≤ q i := hmono j i hji (by omega)
      rw [hjk] at hbetween
      linarith
    · have hij : i + 1 ≤ j := by omega
      have hij' : q (i + 1) ≤ q j := hmono (i + 1) j hij hjn
      rw [hjk] at hbetween
      linarith
  let V : ℝ → A.Ω → ℝ := fun u ζ =>
    fp81s21_moving_heat_ito_endpoint p R A a ha hH future L Φ u ζ
  let D : A.Ω → ℝ → ℝ := fun ζ u =>
    fp81s21_moving_heat_ito_rate p R A F a ha hH L Φ ζ u
  have hpieces : ∀ i < n, ∃ Mart : A.Ω → ℝ,
      Integrable Mart A.P ∧ (∫ ζ, Mart ζ ∂A.P = 0) ∧
      ∀ᵐ ζ ∂A.P,
        IntegrableOn (D ζ) (Ioc (q i) (q (i + 1))) ∧
        V (q (i + 1)) ζ - V (q i) ζ =
          (∫ u in Ioc (q i) (q (i + 1)), D ζ u) + Mart ζ := by
    intro i hi
    have hqi0 : 0 ≤ q i := hq0.trans (hmono 0 i (by omega) (by omega))
    have hqis : q i ≤ q (i + 1) := (hqstep i hi).le
    have hsiH : q (i + 1) ≤ a + p.T :=
      (hmono (i + 1) n (by omega) le_rfl).trans hqend
    obtain ⟨Mart, hMi, hM0, hMeq⟩ :=
      fp81s21_moving_heat_ito_piece p R hδ hδh a ha hH hN A F
        hstd hlin hr0 hphys future hfuture L hqi0 hqis hsiH (hno i hi) Φ hΦ
    refine ⟨Mart, hMi, hM0, ?_⟩
    filter_upwards [hMeq] with ζ hζ
    refine ⟨?_, ?_⟩
    ·
      convert hζ.1 using 1
      all_goals first | rfl | (funext u; rfl)
    ·
      convert hζ.2 using 1
      all_goals first | rfl | (funext u; rfl)
  obtain ⟨Mart, hMi, hM0, hMeq⟩ :=
    fp81s21_moving_heat_ito_partition_from_pieces
      A.P V D q n (fun i j hij hjn => hmono i j hij hjn) hpieces
  exact ⟨hlt, Mart, hMi, hM0, hMeq⟩

#print axioms fp81s21_moving_heat_ito_rate
#print axioms fp81s21_moving_heat_ito_endpoint
#print axioms fp81s21_moving_heat_ito_partition

end HRS.Fp81.S21

end
