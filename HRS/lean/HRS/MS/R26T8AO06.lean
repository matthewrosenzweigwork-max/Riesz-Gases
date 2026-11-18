import HRS.MS.R26T8AO06m
import HRS.MS.R26T8AS08

/-!
# S8.2 T8A O06: `r26t8a_normal_form_path` (Pro contract, verbatim)
Assembly: O06m (pathwise Itô identity of the backward corrector in age form, from the localised Itô formula O06d on
the collision-free set, the drift identification O06e/j and the noise identification O06i), O06g (literal propagator
= age objects), O04 (progressive `L²` noise), and the unshifting of the filtration (S08).
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators ContDiff FourierTransform ComplexConjugate
namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.PDE.ToolboxRd HRS.MP.SelfSimP4Impl

set_option maxHeartbeats 12800000 in
theorem r26t8a_normal_form_path (d N : ℕ) (hd : 2 ≤ d) (hN : 2 ≤ N)
    (a beta m M C Cf c : ℝ) (ha : 0 < a) (hbeta : 0 < beta) (hM : 0≤M) (hC : 0≤C)
    (rho : Euc d → ℝ) (hrho : IsThermalEquilibrium d (criticalS d) a beta rho)
    (Psi : (Euc d → ℝ) → Euc d → Euc d → ℝ)
    (hPsi : r26t8a_NormalFormFamily d a beta M C rho Psi)
    (horb : r26t8a_FeatureOrbits d a beta m Cf c rho)
    {Omega : Type} [mOmega : MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X0 : Omega → EucConfig d N) (W : ℝ≥0 → Omega → Fin N → Euc d)
    (X : ℝ≥0 → Omega → EucConfig d N)
    (hX : IsCanonicalRealization d (criticalS d) a beta N P X0 W X)
    (F : Filtration ℝ mOmega) (W' : ℝ≥0 → Omega → Fin N × Fin d → ℝ)
    (hfilt : IsWholeFilteredSolution P F W' W X)
    (alpha : MultiIndex d) (b : ℝ) (hb : 0 ≤ b) :
    IsProgressiveL2 P F (r26t8a_correctorNoise a beta m b rho Psi alpha X) ∧
    ∃ Mrt : ℝ → Omega → ℝ,
      IsItoIntegral P F W' (r26t8a_correctorNoise a beta m b rho Psi alpha X) Mrt ∧
      ∀ᵐ w ∂P,
        let f := fun r => propagatorW (critCoeff d a beta rho) r b (oscTestFun m alpha)
        IntegrableOn (fun r => scalarForcing a beta rho (f r) (X r.toNNReal w))
          (Set.Icc 0 b) ∧
        IntegrableOn (fun r =>
          r26t8a_correctedD a beta rho Psi (f r) (X r.toNNReal w) -
          r26t8a_correctedQ a beta Psi
            (HRS.Whole.projGeneratorW (critCoeff d a beta rho) (HRS.Whole.withDensityReal rho) 0 (f r))
            (X r.toNNReal w)) (Set.Icc 0 b) ∧
        ∀ l h : ℝ, 0 ≤ l → l ≤ h → h ≤ b →
        (∫ r in Set.Icc l h, scalarForcing a beta rho (f r) (X r.toNNReal w)) =
          -r26t8a_correctedQ a beta Psi (f h) (X h.toNNReal w) +
            r26t8a_correctedQ a beta Psi (f l) (X l.toNNReal w) +
            (∫ r in Set.Icc l h,
              r26t8a_correctedD a beta rho Psi (f r) (X r.toNNReal w) -
              r26t8a_correctedQ a beta Psi
                (HRS.Whole.projGeneratorW (critCoeff d a beta rho) (HRS.Whole.withDensityReal rho) 0 (f r))
                (X r.toNNReal w)) +
            Mrt h w - Mrt l w := by
  classical
  have hDsol : IsWholeStrongSolution P (quadraticGradientDyn d (criticalS d) a beta) b X0 W X := hX.solution b
  have hW' : IsBrownianFiltration P (p4r_shiftFil F) W' := p4r_shiftFil_brownian hfilt.brownian
  have had0 : Measurable[F 0] (X 0) := hfilt.adapted 0
  have hprog : IsProgressive (p4r_shiftFil F) (ofNNRealTime X) :=
    r26t8a_o05a3_prog_shift hfilt.progressive had0
  have hfilt' : IsWholeFilteredSolution P (p4r_shiftFil F) W' W X :=
    ⟨hW', hfilt.coords, fun t => by
      have := hfilt.adapted t
      rwa [← p4r_shiftFil_nnreal] at this, hprog⟩
  obtain ⟨-, hL2, -⟩ := r26t8a_noise_regular d N hd hN a beta m M C Cf c ha hbeta hM hC rho hrho Psi hPsi horb
    P X0 W X hX F W' hfilt alpha 0 (by norm_num)
  obtain ⟨-, hL2', -⟩ := r26t8a_noise_regular d N hd hN a beta m M C Cf c ha hbeta hM hC rho hrho Psi hPsi horb
    P X0 W X hX (p4r_shiftFil F) W' hfilt' alpha 0 (by norm_num)
  have hce := r26t8a_o06_corrNoise_eq d N hd a beta m M C Cf c rho Psi hPsi horb alpha b X
  have hΦ : IsProgressiveL2 P F (r26t8a_correctorNoise a beta m b rho Psi alpha X) := by
    rw [hce]; exact hL2 b hb
  have hΦ' : IsProgressiveL2 P (p4r_shiftFil F) (r26t8a_correctorNoise a beta m b rho Psi alpha X) := by
    rw [hce]; exact hL2' b hb
  refine ⟨hΦ, itoIntegral P (p4r_shiftFil F) W' (r26t8a_correctorNoise a beta m b rho Psi alpha X),
    r26t8a_ito_unshift P F W' _ _ (isItoIntegral_itoIntegral hW' hΦ'), ?_⟩
  set Mrt := itoIntegral P (p4r_shiftFil F) W' (r26t8a_correctorNoise a beta m b rho Psi alpha X) with hMrt
  rcases eq_or_lt_of_le hb with hb0 | hbpos
  · -- degenerate horizon
    refine Filter.Eventually.of_forall fun w => ?_
    intro f
    have hz : volume (Set.Icc (0 : ℝ) b) = 0 := by rw [← hb0]; simp
    have hint0 : ∀ g : ℝ → ℝ, IntegrableOn g (Set.Icc 0 b) := fun g => by
      unfold IntegrableOn
      rw [Measure.restrict_eq_zero.2 hz]
      exact integrable_zero_measure
    refine ⟨hint0 _, hint0 _, fun l h hl hlh hhb => ?_⟩
    have hl0 : l = 0 := le_antisymm (hlh.trans (hhb.trans hb0.ge)) hl
    have hh0 : h = 0 := le_antisymm (hhb.trans hb0.ge) (hl.trans hlh)
    subst hl0 hh0
    have hz0 : volume (Set.Icc (0 : ℝ) 0) = 0 := by simp
    rw [setIntegral_measure_zero _ hz0, setIntegral_measure_zero _ hz0]
    ring
  · have hage := r26t8a_o06_age_identity d N hd hN a beta m M C Cf c ha hbeta hM hC rho hrho Psi hPsi horb P X0 W X
      hX F W' hfilt alpha b hbpos
    obtain ⟨-, -, hDc, -⟩ := r26t8a_normal_age_FTC d N hd hN a beta m M C Cf c ha hbeta hM hC rho hrho Psi hPsi
      horb alpha 0 (by norm_num)
    have hQ1 := r26t8a_o06_QAge_cont d N hd hN a beta m M C Cf c ha hbeta hM hC rho hrho Psi hPsi horb alpha 1
      (by norm_num)
    filter_upwards [hage, hDsol.cont, hDsol.no_collision] with w hw hcont hnc
    intro f
    obtain ⟨hgint, hgid⟩ := hw
    have hXc : Continuous fun s : ℝ => X s.toNNReal w := (continuous_pi hcont).comp continuous_real_toNNReal
    have hUw : ∀ s ∈ Set.Icc (0 : ℝ) b, X s.toNNReal w ∉ eucCollisionSet d N := fun s hs =>
      hnc s.toNNReal (by rw [Real.coe_toNNReal _ hs.1]; exact hs.2)
    have hpath : ContinuousOn (fun s : ℝ => (b - s, X s.toNNReal w)) (Set.Icc 0 b) :=
      ((continuous_const.sub continuous_id).prodMk hXc).continuousOn
    have hmaps : Set.MapsTo (fun s : ℝ => (b - s, X s.toNNReal w)) (Set.Icc 0 b)
        (Set.Ici 0 ×ˢ (eucCollisionSet d N)ᶜ) := fun s hs => ⟨sub_nonneg.2 hs.2, hUw s hs⟩
    set q1 : ℝ → ℝ := fun s => r26t8a_QAge a beta m rho Psi alpha 1 (b - s) (X s.toNNReal w) with hq1
    set dd : ℝ → ℝ := fun s => r26t8a_DAge a beta m rho Psi alpha 0 (b - s) (X s.toNNReal w) with hdd
    set sf : ℝ → ℝ := fun s => scalarForcing a beta rho (r26t8a_ageTest a beta m rho alpha 0 (b - s))
      (X s.toNNReal w) with hsf
    have hq1c : ContinuousOn q1 (Set.Icc 0 b) :=
      ContinuousOn.comp (g := fun p : ℝ × EucConfig d N => r26t8a_QAge a beta m rho Psi alpha 1 p.1 p.2)
        (f := fun s : ℝ => (b - s, X s.toNNReal w)) hQ1 hpath hmaps
    have hddc : ContinuousOn dd (Set.Icc 0 b) :=
      ContinuousOn.comp (g := fun p : ℝ × EucConfig d N => r26t8a_DAge a beta m rho Psi alpha 0 p.1 p.2)
        (f := fun s : ℝ => (b - s, X s.toNNReal w)) hDc hpath hmaps
    have hq1i : IntegrableOn q1 (Set.Icc 0 b) := hq1c.integrableOn_Icc
    have hddi : IntegrableOn dd (Set.Icc 0 b) := hddc.integrableOn_Icc
    have hsfi : IntegrableOn sf (Set.Icc 0 b) := by
      have := (hq1i.neg.add hddi).sub hgint
      refine this.congr_fun (fun s _ => ?_) measurableSet_Icc
      simp only [Pi.sub_apply, Pi.add_apply, Pi.neg_apply, hq1, hdd, hsf]
      ring
    -- conversion of the literal propagator objects
    have hconv := fun r (hr : r ∈ Set.Icc (0 : ℝ) b) =>
      r26t8a_o06_prop_conv d N a beta m M C Cf c rho Psi hPsi horb alpha r b hr.1 hr.2
    have hSF : ∀ r ∈ Set.Icc (0 : ℝ) b, scalarForcing a beta rho (f r) (X r.toNNReal w) = sf r := fun r hr => by
      have := congrFun (hconv r hr).2.1 (X r.toNNReal w)
      exact this
    have hDD : ∀ r ∈ Set.Icc (0 : ℝ) b, r26t8a_correctedD a beta rho Psi (f r) (X r.toNNReal w) = dd r :=
      fun r hr => congrFun (hconv r hr).2.2.1 (X r.toNNReal w)
    have hQ1' : ∀ r ∈ Set.Icc (0 : ℝ) b, r26t8a_correctedQ a beta Psi
        (HRS.Whole.projGeneratorW (critCoeff d a beta rho) (HRS.Whole.withDensityReal rho) 0 (f r))
        (X r.toNNReal w) = q1 r := fun r hr => congrFun (hconv r hr).2.2.2 (X r.toNNReal w)
    have hQ0 : ∀ r ∈ Set.Icc (0 : ℝ) b, r26t8a_correctedQ a beta Psi (f r) (X r.toNNReal w) =
        r26t8a_QAge a beta m rho Psi alpha 0 (b - r) (X r.toNNReal w) := fun r hr =>
      congrFun (hconv r hr).1 (X r.toNNReal w)
    refine ⟨hsfi.congr_fun (fun r hr => (hSF r hr).symm) measurableSet_Icc, ?_, ?_⟩
    · exact (hddi.sub hq1i).congr_fun (fun r hr => by
        simp only [Pi.sub_apply]; rw [hDD r hr, hQ1' r hr]) measurableSet_Icc
    · intro l h hl hlh hhb
      have hgh : IntegrableOn (fun s : ℝ => -q1 s + dd s - sf s) (Set.Icc 0 h) :=
        hgint.mono_set (Set.Icc_subset_Icc_right hhb)
      have hsplit := r26t8a_o06_icc_split hl hlh hgh
      have hIh := hgid h ⟨hl.trans hlh, hhb⟩
      have hIl := hgid l ⟨hl, hlh.trans hhb⟩
      have hsub : Set.Icc l h ⊆ Set.Icc 0 b := Set.Icc_subset_Icc hl hhb
      have hq1' := hq1i.mono_set hsub
      have hdd' := hddi.mono_set hsub
      have hsf' := hsfi.mono_set hsub
      have hg3 : ∫ s in Set.Icc l h, (-q1 s + dd s - sf s) =
          -(∫ s in Set.Icc l h, q1 s) + (∫ s in Set.Icc l h, dd s) - ∫ s in Set.Icc l h, sf s := by
        have i0 : IntegrableOn (fun s => -q1 s) (Set.Icc l h) := hq1'.neg
        have i1 : IntegrableOn (fun s => -q1 s + dd s) (Set.Icc l h) := i0.add hdd'
        rw [integral_sub i1 hsf', integral_add i0 hdd', integral_neg]
      have hint1 : ∫ r in Set.Icc l h, scalarForcing a beta rho (f r) (X r.toNNReal w) =
          ∫ s in Set.Icc l h, sf s :=
        setIntegral_congr_fun measurableSet_Icc fun r hr => hSF r ⟨hl.trans hr.1, hr.2.trans hhb⟩
      have hint2 : ∫ r in Set.Icc l h, (r26t8a_correctedD a beta rho Psi (f r) (X r.toNNReal w) -
          r26t8a_correctedQ a beta Psi (HRS.Whole.projGeneratorW (critCoeff d a beta rho)
            (HRS.Whole.withDensityReal rho) 0 (f r)) (X r.toNNReal w)) =
          (∫ s in Set.Icc l h, dd s) - ∫ s in Set.Icc l h, q1 s := by
        rw [← integral_sub hdd' hq1']
        exact setIntegral_congr_fun measurableSet_Icc fun r hr => by
          beta_reduce
          rw [hDD r ⟨hl.trans hr.1, hr.2.trans hhb⟩, hQ1' r ⟨hl.trans hr.1, hr.2.trans hhb⟩]
      rw [hint1, hint2, hQ0 h ⟨hl.trans hlh, hhb⟩, hQ0 l ⟨hl, hlh.trans hhb⟩]
      have hE : (r26t8a_QAge a beta m rho Psi alpha 0 (b - h) (X h.toNNReal w)) -
          r26t8a_QAge a beta m rho Psi alpha 0 (b - l) (X l.toNNReal w) =
          (∫ s in Set.Icc l h, (-q1 s + dd s - sf s)) + Mrt h w - Mrt l w := by
        rw [hIh, hIl, hsplit]; ring
      rw [hg3] at hE
      linarith

end HRS.MS.R26T8A

end
