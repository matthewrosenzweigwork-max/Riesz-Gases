import HRS.MS.Fp81S21BlockValue5

/-!
# S2.1(iii), packet 15d-4: actual block observation expansion

This specializes the generic unit-clock four-term identity to the block value
and the finite observation tests. Its arguments are exactly `1`, `θ(ta)`, and
`θ(tb)` from the block reconstruction.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
noncomputable section

open MeasureTheory Filter Topology Set Classical
open scoped ENNReal NNReal BigOperators

namespace HRS.Fp81.S21

open HRS HRS.Whole HRS.Uniform HRS.Uniform.Q45 HRS.MS.CovMeas HRS.MS.GenPath

/-- The actual block value on a pair of finite-combination observation tests
is the four-term unit-clock expansion at `1`, `θ(ta)`, and `θ(tb)`. -/
theorem fp81s21_blockValue_obs_four
    {d : ℕ} {C : WholeCoeff d} {m H a : ℝ} {r : ℕ} {P : ℝ}
    {z : ℝ → (Euc d → ℝ) → ℝ} {Cmix cdec : ℝ}
    (D : fp81s21_WindowLocalInput C m H a r P z Cmix cdec)
    {I : Set ℝ} (hI : MeasurableSet I) (k : ℕ)
    {ta tb : ℝ} (hta : ta ∈ Icc (0 : ℝ) H) (htb : tb ∈ Icc (0 : ℝ) H)
    (Sa Sb : Finset (MultiIndex d)) (ca cb : MultiIndex d → ℝ)
    (l₁ l₂ : StrongDual ℝ (OscPath d m H))
    (h₁ : ∀ w, l₁ w = OscDual.eval (r2PathAt w ta)
      (fun x => ∑ α ∈ Sa, ca α * oscTestFun m α x))
    (h₂ : ∀ w, l₂ w = OscDual.eval (r2PathAt w tb)
      (fun x => ∑ α ∈ Sb, cb α * oscTestFun m α x)) :
    ((fp81s21_blockValue D I k : projTensor (OscPath d m H) 2) :
      TensorDual (OscPath d m H) 2)
        ((ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin 2) ℝ).compContinuousLinearMap ![l₁, l₂]) =
      (∫ s in Icc (0 : ℝ) 1,
        fp81s21_windowLocalD I k C m H a z D.fp81s21_ha
          (le_of_lt D.fp81s21_hH) s
          (s101Pc m H ta Sa ca) (s101Pc m H tb Sb cb)) +
      (∫ s in Icc (0 : ℝ) (fp81s21_blockClock a k ⟨tb, htb⟩ : ℝ),
        fp81s21_windowLocalD I k C m H a z D.fp81s21_ha
          (le_of_lt D.fp81s21_hH) s
          (s101Pc m H ta Sa ca) (s101Qc m H Sb cb)) +
      (∫ s in Icc (0 : ℝ) (fp81s21_blockClock a k ⟨ta, hta⟩ : ℝ),
        fp81s21_windowLocalD I k C m H a z D.fp81s21_ha
          (le_of_lt D.fp81s21_hH) s
          (s101Qc m H Sa ca) (s101Pc m H tb Sb cb)) +
      ∫ s in Icc (0 : ℝ)
          (min (fp81s21_blockClock a k ⟨ta, hta⟩ : ℝ)
            (fp81s21_blockClock a k ⟨tb, htb⟩ : ℝ)),
        fp81s21_windowLocalD I k C m H a z D.fp81s21_ha
          (le_of_lt D.fp81s21_hH) s
          (s101Qc m H Sa ca) (s101Qc m H Sb cb) := by
  let Rc : PathSp 1 (KSpace d m H) →L[ℝ] OscPath d m H := fp81s21_blockRecon (le_of_lt D.fp81s21_hH) a k
  let θa : Icc (0 : ℝ) 1 := fp81s21_blockClock a k ⟨ta, hta⟩
  let θb : Icc (0 : ℝ) 1 := fp81s21_blockClock a k ⟨tb, htb⟩
  let Dloc : ℝ → KSpace d m H →L[ℝ] KSpace d m H →L[ℝ] ℝ :=
    fun s => fp81s21_windowLocalD I k C m H a z D.fp81s21_ha
      (le_of_lt D.fp81s21_hH) s
  have hQ := fp81s21_blockCovariance_props (KSpace d m H)
  have hDloc := fp81s21_windowLocal_isTraceDensityL1 D hI k
  have hmI : MeasurableSet (Icc (0 : ℝ) 1) := measurableSet_Icc
  have h₁' : ∀ y : PathSp 1 (KSpace d m H),
      l₁ (Rc y) = inner ℝ (pcm y fp81s21_unitClockEndpoint)
          (s101Pc m H ta Sa ca) + inner ℝ (pcm y θa) (s101Qc m H Sa ca) := by
    intro y
    rw [h₁ (Rc y)]
    exact fp81s21_blockRecon_eval_combo (le_of_lt D.fp81s21_hH) a k y hta Sa ca
  have h₂' : ∀ y : PathSp 1 (KSpace d m H),
      l₂ (Rc y) = inner ℝ (pcm y fp81s21_unitClockEndpoint)
          (s101Pc m H tb Sb cb) + inner ℝ (pcm y θb) (s101Qc m H Sb cb) := by
    intro y
    rw [h₂ (Rc y)]
    exact fp81s21_blockRecon_eval_combo (le_of_lt D.fp81s21_hH) a k y htb Sb cb
  change fp81s21_blockPsi Rc
      (fp81s21_blockCovariance (KSpace d m H) Dloc (Icc (0 : ℝ) 1))
      ((ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin 2) ℝ).compContinuousLinearMap ![l₁, l₂]) = _
  have hfour := fp81s21_blockPsi_four hQ hDloc hmI Rc
    (s101Pc m H ta Sa ca) (s101Qc m H Sa ca)
    (s101Pc m H tb Sb cb) (s101Qc m H Sb cb) l₁ l₂ h₁' h₂'
  have hseta : Icc (0 : ℝ) 1 ∩ Icc 0 (θa : ℝ) = Icc 0 (θa : ℝ) := by
    ext s
    constructor
    · exact fun h => h.2
    · intro hs
      refine ⟨?_, hs⟩
      exact ⟨hs.1, le_trans hs.2 θa.property.2⟩
  have hsetb : Icc (0 : ℝ) 1 ∩ Icc 0 (θb : ℝ) = Icc 0 (θb : ℝ) := by
    ext s
    constructor
    · exact fun h => h.2
    · intro hs
      refine ⟨?_, hs⟩
      exact ⟨hs.1, le_trans hs.2 θb.property.2⟩
  have hsetmin : Icc (0 : ℝ) 1 ∩ Icc 0 (min (θa : ℝ) (θb : ℝ)) =
      Icc 0 (min (θa : ℝ) (θb : ℝ)) := by
    ext s
    constructor
    · exact fun h => h.2
    · intro hs
      refine ⟨?_, hs⟩
      exact ⟨hs.1, le_trans hs.2 (le_trans (min_le_left _ _) θa.property.2)⟩
  rw [hsetb, hseta, hsetmin] at hfour
  simpa [Dloc, θa, θb, Rc, fp81s21_blockValue] using hfour

#print axioms fp81s21_blockValue_obs_four

end HRS.Fp81.S21

end
