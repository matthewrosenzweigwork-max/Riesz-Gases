import HRS.MS.Fp81S21FinProj

/-!
# HRS S2.1(iii), packet 19d: expectation closure for a covering partition

This stage integrates the finite-level partition identity against the particle
law and identifies the separate drift and covariance terms with the specified
RS values.  The covering partition and the two value-identification clauses
are explicit inputs, supplied by the partition construction and packets 19b/19c.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

noncomputable section

open MeasureTheory Filter Set
open scoped BigOperators

namespace HRS.Fp81.S21

open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R2Interp

/-- Sort the finite set of projection-grid nodes lying in `[q,r]` together
with the two endpoints.  The resulting partition contains every grid node in
the interval, as required by the moving stopped-piece theorem. -/
theorem fp81s21_finproj_covering_partition
    (p : Parameters) (a : ℝ) (hH : 0 < a + p.T) (L : ℕ) (q r : ℝ)
    (hq : 0 ≤ q) (hqr : q < r) (hr : r ≤ a + p.T) :
    ∃ n : ℕ, 1 ≤ n ∧ ∃ π : ℕ → ℝ,
      π 0 = q ∧ π n = r ∧
      (∀ i < n, π i < π (i + 1)) ∧
      ∀ k : Fin (s102_q p.d L),
        q ≤ (s102_tk hH L k : ℝ) → (s102_tk hH L k : ℝ) ≤ r →
        ∃ i : ℕ, i ≤ n ∧ (s102_tk hH L k : ℝ) = π i := by
  classical
  let S : Finset ℝ :=
    (Finset.univ.filter (fun k : Fin (s102_q p.d L) =>
      q ≤ s102_tk hH L k ∧ s102_tk hH L k ≤ r)).image (fun k => s102_tk hH L k)
  let Z : Finset ℝ := insert q (insert r S)
  have hqZ : q ∈ Z := by simp [Z]
  have hrZ : r ∈ Z := by simp [Z]
  have hgridZ : ∀ k : Fin (s102_q p.d L),
      q ≤ s102_tk hH L k → s102_tk hH L k ≤ r → s102_tk hH L k ∈ Z := by
    intro k hqk hkr
    have hmem : k ∈ Finset.univ.filter (fun j : Fin (s102_q p.d L) =>
        q ≤ s102_tk hH L j ∧ s102_tk hH L j ≤ r) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨hqk, hkr⟩⟩
    change s102_tk hH L k ∈ insert q (insert r S)
    apply Finset.mem_insert_of_mem
    apply Finset.mem_insert_of_mem
    exact Finset.mem_image_of_mem (fun j => s102_tk hH L j) hmem
  have hZlower : ∀ z ∈ Z, q ≤ z := by
    intro z hz
    rcases Finset.mem_insert.mp hz with hq' | hz
    · simpa [hq']
    · rcases Finset.mem_insert.mp hz with hr' | hz
      · simpa [hr'] using hqr.le
      · rcases Finset.mem_image.mp hz with ⟨k, hk, rfl⟩
        exact (Finset.mem_filter.mp hk).2.1
  have hZupper : ∀ z ∈ Z, z ≤ r := by
    intro z hz
    rcases Finset.mem_insert.mp hz with hq' | hz
    · simpa [hq'] using hqr.le
    · rcases Finset.mem_insert.mp hz with hr' | hz
      · simpa [hr']
      · rcases Finset.mem_image.mp hz with ⟨k, hk, rfl⟩
        exact (Finset.mem_filter.mp hk).2.2
  let Good : ℕ → Prop := fun m =>
    ∀ y, y ∈ Z → q ≤ y → (Z.filter (fun z => z ≤ y)).card ≤ m →
      ∃ n : ℕ, ∃ π : ℕ → ℝ,
        π 0 = q ∧ π n = y ∧
        (∀ i < n, π i < π (i + 1)) ∧
        ∀ k : Fin (s102_q p.d L),
          q ≤ s102_tk hH L k → (s102_tk hH L k : ℝ) ≤ y →
          ∃ i : ℕ, i ≤ n ∧ (s102_tk hH L k : ℝ) = π i
  have hGood : ∀ m, Good m := by
    intro m
    induction m with
    | zero =>
        intro y hy hqy hcard
        have hpos : 0 < (Z.filter (fun z => z ≤ y)).card :=
          Finset.card_pos.2 ⟨y, Finset.mem_filter.mpr ⟨hy, le_rfl⟩⟩
        omega
    | succ m ih =>
        intro y hy hqy hcard
        by_cases hyq : y = q
        · subst y
          refine ⟨0, fun _ => q, rfl, rfl, ?_, ?_⟩
          · intro i hi
            omega
          · intro k hqk hky
            have heq : s102_tk hH L k = q := le_antisymm hky hqk
            exact ⟨0, Nat.zero_le _, heq⟩
        · have hqyl : q < y := lt_of_le_of_ne hqy (by
            intro heq
            exact hyq heq.symm)
          have hne : (Z.filter (fun z => z < y)).Nonempty :=
            ⟨q, Finset.mem_filter.mpr ⟨hqZ, hqyl⟩⟩
          let x := (Z.filter (fun z => z < y)).max' hne
          have hxmem : x ∈ Z.filter (fun z => z < y) := Finset.max'_mem _ _
          have hxZ : x ∈ Z := (Finset.mem_filter.mp hxmem).1
          have hxy : x < y := (Finset.mem_filter.mp hxmem).2
          have hqx : q ≤ x := hZlower x hxZ
          have hcardx : (Z.filter (fun z => z ≤ x)).card ≤ m := by
            have hsub : (Z.filter (fun z => z ≤ x)) ⊂
                (Z.filter (fun z => z ≤ y)) := by
              refine ⟨?_, ?_⟩
              · intro z hz
                rcases Finset.mem_filter.mp hz with ⟨hzZ, hzx⟩
                exact Finset.mem_filter.mpr ⟨hzZ, hzx.trans hxy.le⟩
              · intro hback
                have hyin : y ∈ Z.filter (fun z => z ≤ y) :=
                  Finset.mem_filter.mpr ⟨hy, le_rfl⟩
                have hyx : y ≤ x := (Finset.mem_filter.mp (hback hyin)).2
                exact (not_le_of_gt hxy) hyx
            have hltcard := Finset.card_lt_card hsub
            omega
          obtain ⟨n, π, hπ0, hπx, hπstep, hπcover⟩ := ih x hxZ hqx hcardx
          let π' : ℕ → ℝ := fun i => if i ≤ n then π i else y
          refine ⟨n + 1, π', ?_, ?_, ?_, ?_⟩
          · simp [π', hπ0]
          · simp [π', hπx, show ¬ n + 1 ≤ n by omega]
          · intro i hi
            by_cases hin : i < n
            · have hin' : i + 1 ≤ n := by omega
              simpa [π', Nat.le_of_lt hin, hin'] using hπstep i hin
            · have hieq : i = n := by omega
              subst i
              simpa [π', hπx, show ¬ n + 1 ≤ n by omega] using hxy
          · intro k hqk hky
            by_cases hty : (s102_tk hH L k : ℝ) = y
            · refine ⟨n + 1, le_rfl, ?_⟩
              simp [π', hty, show ¬ n + 1 ≤ n by omega]
            · have hty' : (s102_tk hH L k : ℝ) < y :=
                lt_of_le_of_ne hky hty
              have htkZ : s102_tk hH L k ∈ Z :=
                hgridZ k hqk (hky.trans (hZupper y hy))
              have htkx : (s102_tk hH L k : ℝ) ≤ x :=
                Finset.le_max' _ _ (Finset.mem_filter.mpr ⟨htkZ, hty'⟩)
              obtain ⟨i, hi, hπi⟩ := hπcover k hqk htkx
              refine ⟨i, hi.trans (Nat.le_succ n), ?_⟩
              simp [π', hi, hπi]
  have hcardr : (Z.filter (fun z => z ≤ r)).card ≤ Z.card :=
    Finset.card_le_card (Finset.filter_subset _ _)
  obtain ⟨n, π, hπ0, hπr, hπstep, hπcover⟩ :=
    hGood Z.card r hrZ hqr.le hcardr
  have hn : 1 ≤ n := by
    by_contra h
    have hn0 : n = 0 := by omega
    subst n
    rw [hπ0] at hπr
    exact (ne_of_lt hqr) hπr
  exact ⟨n, hn, π, hπ0, hπr, hπstep, hπcover⟩

/-- The finite-level drift operator in the moving heat RS contract. -/
noncomputable def fp81s21_finproj_drift_adapter
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ)
    {N : ℕ} (A : Particle R N)
    (a : ℝ) (ha : 0 ≤ a) (hH : 0 < a + p.T)
    (future : (H : ℝ) → ℝ → Measure
      (OscPath p.d (wholeSpaceIndex p.d : ℝ) H))
    (L : ℕ) (Φ : Window p → ℝ)
    (Yh : A.Ω → ℝ → OscPath p.d (wholeSpaceIndex p.d : ℝ) (a + p.T)) :
    A.Ω → ℝ → OscPath p.d (wholeSpaceIndex p.d : ℝ) (a + p.T) →L[ℝ] ℝ :=
  let H : ℝ := a + p.T
  let W : OscPath p.d (wholeSpaceIndex p.d : ℝ) H →L[ℝ] Window p :=
    HRS.MS.ProClosureS111.physicalWindowRestriction
      (d := p.d) (m := (wholeSpaceIndex p.d : ℝ))
      (T := p.T) (H := H) ha le_rfl
  fun ω t => fderiv ℝ
    (r2HeatFn (future H) (fun w => Φ (W (s102_Pj H hH L w))) t)
    (Yh ω t)

/-- The finite-level covariance operator in the moving heat RS contract. -/
noncomputable def fp81s21_finproj_covariance_adapter
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ)
    {N : ℕ} (A : Particle R N)
    (a : ℝ) (ha : 0 ≤ a) (hH : 0 < a + p.T)
    (future : (H : ℝ) → ℝ → Measure
      (OscPath p.d (wholeSpaceIndex p.d : ℝ) H))
    (L : ℕ) (Φ : Window p → ℝ)
    (Yh : A.Ω → ℝ → OscPath p.d (wholeSpaceIndex p.d : ℝ) (a + p.T)) :
    A.Ω → ℝ → (projTensor
      (OscPath p.d (wholeSpaceIndex p.d : ℝ) (a + p.T)) 2 →L[ℝ] ℝ) :=
  let H : ℝ := a + p.T
  let W : OscPath p.d (wholeSpaceIndex p.d : ℝ) H →L[ℝ] Window p :=
    HRS.MS.ProClosureS111.physicalWindowRestriction
      (d := p.d) (m := (wholeSpaceIndex p.d : ℝ))
      (T := p.T) (H := H) ha le_rfl
  fun ω t => fp81s21_covariance_pairingCLM
    (iteratedFDeriv ℝ 2
      (r2HeatFn (future H) (fun w => Φ (W (s102_Pj H hH L w))) t)
      (Yh ω t))

/-- The finite-level moving Itô identity gives the expected signed RS
correction when the drift and covariance RS values are separately identified
with their time integrals. -/
theorem fp81s21_moving_heat_ito_expectation_of_rs_values
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
    (future : (H : ℝ) → ℝ → Measure
      (OscPath p.d (wholeSpaceIndex p.d : ℝ) H))
    (hfuture : fp81s21_moving_heat_full_clause p R future)
    (L : ℕ) (Φ : Window p → ℝ) (hΦ : MemCb 5 Φ)
    (Yh Fd : A.Ω → ℝ → OscPath p.d (wholeSpaceIndex p.d : ℝ) (a + p.T))
    (Fj : A.Ω → ℝ → projTensor
      (OscPath p.d (wholeSpaceIndex p.d : ℝ) (a + p.T)) 2)
    (hYm : ∀ t, Measurable (fun ω => Yh ω t))
    (hYae : ∀ᵐ ω ∂A.P, ∀ t ∈ Icc (0 : ℝ) (a + p.T),
      Yh ω t = s102_Y (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ)
        (a + p.T) A.P A.X ω t)
    (WS : fp81s21_WindowRS A.P (a + p.T)
      (fp81s21_finproj_drift_adapter p R A a ha hH future L Φ Yh) Fd
      (fp81s21_finproj_covariance_adapter p R A a ha hH future L Φ Yh) Fj)
    (q r : ℝ) (hq : 0 ≤ q) (hqr : q ≤ r) (hr : r ≤ a + p.T)
    (hDOn : ∀ᵐ ω ∂A.P,
      IntegrableOn (fp81s21_moving_drift_cyl_sum p R A F a ha hH L Φ ω)
        (Ioc q r))
    (hJOn : ∀ᵐ ω ∂A.P,
      IntegrableOn (fp81s21_moving_covariance_cyl_sum p R A F a ha hH L Φ ω)
        (Ioc q r))
    (hDval : ∀ᵐ ω ∂A.P,
      WS.drift.value q r ω =
        ∫ u in Ioc q r, fp81s21_moving_drift_cyl_sum p R A F a ha hH L Φ ω u)
    (hJval : ∀ᵐ ω ∂A.P,
      WS.covariance.value q r ω =
        ∫ u in Ioc q r, fp81s21_moving_covariance_cyl_sum p R A F a ha hH L Φ ω u) :
    Real.sqrt N *
        ((∫ ω, fp81s21_moving_heat_ito_endpoint
            p R A a ha hH future L Φ r ω ∂A.P) -
          (∫ ω, fp81s21_moving_heat_ito_endpoint
            p R A a ha hH future L Φ q ω ∂A.P)) =
      fp81s21_WindowRS_corr WS q r := by
  classical
  have hIq := fp81s21_moving_heat_ito_endpoint_integrable p R A a ha hH
    future hfuture L Φ hΦ Yh hYm hYae q hq (hqr.trans hr)
  have hIr := fp81s21_moving_heat_ito_endpoint_integrable p R A a ha hH
    future hfuture L Φ hΦ Yh hYm hYae r (hq.trans hqr) hr
  by_cases hlt : q < r
  · obtain ⟨n, hn, π, hπ0, hπn, hπstep, hπgrid⟩ :=
      fp81s21_finproj_covering_partition p a hH L q r hq hlt hr
    have hπ0nonneg : 0 ≤ π 0 := by rw [hπ0]; exact hq
    have hπnH : π n ≤ a + p.T := by rw [hπn]; exact hr
    have hπgrid' : ∀ k : Fin (s102_q p.d L),
        π 0 ≤ (s102_tk hH L k : ℝ) →
        (s102_tk hH L k : ℝ) ≤ π n →
        ∃ i : ℕ, i ≤ n ∧ (s102_tk hH L k : ℝ) = π i := by
      intro k hk0 hkn
      apply hπgrid k
      · simpa [hπ0] using hk0
      · simpa [hπn] using hkn
    obtain ⟨_, Mart, hMi, hM0, hparts⟩ :=
      fp81s21_moving_heat_ito_partition p R hδ hδh a ha hH hN A F
        hstd hlin hr0 hphys future hfuture L hn π hπ0nonneg hπstep hπnH hπgrid' Φ hΦ
    have hparts' : ∀ᵐ ω ∂A.P,
        IntegrableOn (fp81s21_moving_heat_ito_rate p R A F a ha hH L Φ ω)
          (Ioc q r) ∧
        fp81s21_moving_heat_ito_endpoint p R A a ha hH future L Φ r ω -
          fp81s21_moving_heat_ito_endpoint p R A a ha hH future L Φ q ω =
          (∫ u in Ioc q r,
            fp81s21_moving_heat_ito_rate p R A F a ha hH L Φ ω u) + Mart ω := by
      simpa [hπ0, hπn] using hparts
    let K : A.Ω → ℝ := fun ω =>
      ∫ u in Ioc q r, fp81s21_moving_heat_ito_rate p R A F a ha hH L Φ ω u
    have hRate : ∀ ω u,
        fp81s21_moving_heat_ito_rate p R A F a ha hH L Φ ω u =
          -(Real.sqrt N)⁻¹ *
              fp81s21_moving_drift_cyl_sum p R A F a ha hH L Φ ω u +
            (1 / (2 * Real.sqrt N)) *
              fp81s21_moving_covariance_cyl_sum p R A F a ha hH L Φ ω u := by
      intro ω u
      rfl
    have hKae : K =ᵐ[A.P] fun ω =>
        -(Real.sqrt N)⁻¹ * WS.drift.value q r ω +
          (1 / (2 * Real.sqrt N)) * WS.covariance.value q r ω := by
      filter_upwards [hDOn, hJOn, hDval, hJval] with ω hDOnω hJOnω hDvalω hJvalω
      have hDscaled : IntegrableOn
          (fun u => -(Real.sqrt N)⁻¹ *
            fp81s21_moving_drift_cyl_sum p R A F a ha hH L Φ ω u) (Ioc q r) :=
        hDOnω.const_mul _
      have hJscaled : IntegrableOn
          (fun u => (1 / (2 * Real.sqrt N)) *
            fp81s21_moving_covariance_cyl_sum p R A F a ha hH L Φ ω u) (Ioc q r) :=
        hJOnω.const_mul _
      have hsum := integral_add hDscaled hJscaled
      have hdecomp :
          (∫ u in Ioc q r,
            -(Real.sqrt N)⁻¹ * fp81s21_moving_drift_cyl_sum
              p R A F a ha hH L Φ ω u +
            (1 / (2 * Real.sqrt N)) *
              fp81s21_moving_covariance_cyl_sum p R A F a ha hH L Φ ω u) =
          -(Real.sqrt N)⁻¹ *
              (∫ u in Ioc q r,
                fp81s21_moving_drift_cyl_sum p R A F a ha hH L Φ ω u) +
            (1 / (2 * Real.sqrt N)) *
              (∫ u in Ioc q r,
                fp81s21_moving_covariance_cyl_sum p R A F a ha hH L Φ ω u) := by
        simpa only [integral_const_mul] using hsum
      calc
        K ω = ∫ u in Ioc q r,
            fp81s21_moving_heat_ito_rate p R A F a ha hH L Φ ω u := rfl
        _ = ∫ u in Ioc q r,
            -(Real.sqrt N)⁻¹ * fp81s21_moving_drift_cyl_sum
              p R A F a ha hH L Φ ω u +
            (1 / (2 * Real.sqrt N)) *
              fp81s21_moving_covariance_cyl_sum p R A F a ha hH L Φ ω u :=
          integral_congr_ae
            (Filter.Eventually.of_forall fun u => hRate ω u)
        _ = -(Real.sqrt N)⁻¹ * WS.drift.value q r ω +
            (1 / (2 * Real.sqrt N)) * WS.covariance.value q r ω := by
          rw [hdecomp, ← hDvalω, ← hJvalω]
    have hDvalInt : Integrable (WS.drift.value q r) A.P :=
      WS.drift.value_integrable q r hq hqr hr
    have hJvalInt : Integrable (WS.covariance.value q r) A.P :=
      WS.covariance.value_integrable q r hq hqr hr
    have hDscaledInt : Integrable
        (fun ω => -(Real.sqrt N)⁻¹ * WS.drift.value q r ω) A.P :=
      hDvalInt.const_mul _
    have hJscaledInt : Integrable
        (fun ω => (1 / (2 * Real.sqrt N)) * WS.covariance.value q r ω) A.P :=
      hJvalInt.const_mul _
    have hCorrInt : Integrable
        (fun ω => -(Real.sqrt N)⁻¹ * WS.drift.value q r ω +
          (1 / (2 * Real.sqrt N)) * WS.covariance.value q r ω) A.P := by
      exact hDscaledInt.add hJscaledInt
    have hKInt : Integrable K A.P := hCorrInt.congr hKae.symm
    have hEqAE :
        (fun ω => fp81s21_moving_heat_ito_endpoint
          p R A a ha hH future L Φ r ω -
          fp81s21_moving_heat_ito_endpoint p R A a ha hH future L Φ q ω) =ᵐ[A.P]
        (fun ω => K ω + Mart ω) := by
      filter_upwards [hparts'] with ω hω
      exact hω.2
    have hdiffInt : Integrable
        (fun ω => fp81s21_moving_heat_ito_endpoint
          p R A a ha hH future L Φ r ω -
          fp81s21_moving_heat_ito_endpoint p R A a ha hH future L Φ q ω) A.P :=
      hIr.sub hIq
    have hDelta :
        (∫ ω, fp81s21_moving_heat_ito_endpoint
            p R A a ha hH future L Φ r ω ∂A.P) -
          (∫ ω, fp81s21_moving_heat_ito_endpoint
            p R A a ha hH future L Φ q ω ∂A.P) =
        (∫ ω, K ω ∂A.P) + ∫ ω, Mart ω ∂A.P := by
      rw [← integral_sub hIr hIq]
      calc
        (∫ ω,
            fp81s21_moving_heat_ito_endpoint p R A a ha hH future L Φ r ω -
              fp81s21_moving_heat_ito_endpoint p R A a ha hH future L Φ q ω ∂A.P) =
            ∫ ω, K ω + Mart ω ∂A.P := integral_congr_ae hEqAE
        _ = _ := integral_add hKInt hMi
    have hKexpect :
        (∫ ω, K ω ∂A.P) =
          -(Real.sqrt N)⁻¹ * (∫ ω, WS.drift.value q r ω ∂A.P) +
            (1 / (2 * Real.sqrt N)) *
              (∫ ω, WS.covariance.value q r ω ∂A.P) := by
      calc
        (∫ ω, K ω ∂A.P) =
            ∫ ω, -(Real.sqrt N)⁻¹ * WS.drift.value q r ω +
              (1 / (2 * Real.sqrt N)) * WS.covariance.value q r ω ∂A.P :=
          integral_congr_ae hKae
        _ = (∫ ω, -(Real.sqrt N)⁻¹ * WS.drift.value q r ω ∂A.P) +
              ∫ ω, (1 / (2 * Real.sqrt N)) * WS.covariance.value q r ω ∂A.P :=
          integral_add hDscaledInt hJscaledInt
        _ = _ := by rw [integral_const_mul, integral_const_mul]
    rw [hDelta, hM0, add_zero, hKexpect]
    have hsqrt : Real.sqrt (N : ℝ) ≠ 0 := by
      exact ne_of_gt (Real.sqrt_pos.2 (by exact_mod_cast (show 0 < N by omega)))
    change Real.sqrt (N : ℝ) *
        (-(Real.sqrt (N : ℝ))⁻¹ *
            (∫ ω, WS.drift.value q r ω ∂A.P) +
          (1 / (2 * Real.sqrt (N : ℝ))) *
            (∫ ω, WS.covariance.value q r ω ∂A.P)) = _
    rw [fp81s21_WindowRS_corr]
    field_simp [hsqrt] <;> ring
  · have hqr' : q = r := le_antisymm hqr (le_of_not_gt hlt)
    subst r
    have hCorrZero := fp81s21_WindowRS_corr_zero WS hq hr
    rw [hCorrZero]
    simp

/-! The next theorem quantifies the finite-level closure over every level and
admissible interval.  Its separate time-integrability and RS-value clauses are
precisely the conclusions supplied by packets 19b-ii and 19c-ii. -/
theorem fp81s21_moving_heat_ito_finite_projection_expectation_identity
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
    (future : (H : ℝ) → ℝ → Measure
      (OscPath p.d (wholeSpaceIndex p.d : ℝ) H))
    (hfuture : fp81s21_moving_heat_full_clause p R future)
    (Φ : Window p → ℝ) (hΦ : MemCb 5 Φ)
    (Yh Fd : A.Ω → ℝ → OscPath p.d (wholeSpaceIndex p.d : ℝ) (a + p.T))
    (Fj : A.Ω → ℝ → projTensor
      (OscPath p.d (wholeSpaceIndex p.d : ℝ) (a + p.T)) 2)
    (hYm : ∀ t, Measurable (fun ω => Yh ω t))
    (hYae : ∀ᵐ ω ∂A.P, ∀ t ∈ Icc (0 : ℝ) (a + p.T),
      Yh ω t = s102_Y (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ)
        (a + p.T) A.P A.X ω t)
    (WS : ∀ L : ℕ, fp81s21_WindowRS A.P (a + p.T)
      (fp81s21_finproj_drift_adapter p R A a ha hH future L Φ Yh) Fd
      (fp81s21_finproj_covariance_adapter p R A a ha hH future L Φ Yh) Fj)
    (hDOn : ∀ L q r, 0 ≤ q → q ≤ r → r ≤ a + p.T → ∀ᵐ ω ∂A.P,
      IntegrableOn (fp81s21_moving_drift_cyl_sum p R A F a ha hH L Φ ω)
        (Ioc q r))
    (hJOn : ∀ L q r, 0 ≤ q → q ≤ r → r ≤ a + p.T → ∀ᵐ ω ∂A.P,
      IntegrableOn (fp81s21_moving_covariance_cyl_sum p R A F a ha hH L Φ ω)
        (Ioc q r))
    (hDval : ∀ L q r, 0 ≤ q → q ≤ r → r ≤ a + p.T → ∀ᵐ ω ∂A.P,
      (WS L).drift.value q r ω =
        ∫ u in Ioc q r, fp81s21_moving_drift_cyl_sum p R A F a ha hH L Φ ω u)
    (hJval : ∀ L q r, 0 ≤ q → q ≤ r → r ≤ a + p.T → ∀ᵐ ω ∂A.P,
      (WS L).covariance.value q r ω =
        ∫ u in Ioc q r, fp81s21_moving_covariance_cyl_sum p R A F a ha hH L Φ ω u) :
    ∀ L q r, 0 ≤ q → q ≤ r → r ≤ a + p.T →
      Real.sqrt N *
          ((∫ ω, fp81s21_moving_heat_ito_endpoint
              p R A a ha hH future L Φ r ω ∂A.P) -
            (∫ ω, fp81s21_moving_heat_ito_endpoint
              p R A a ha hH future L Φ q ω ∂A.P)) =
        fp81s21_WindowRS_corr (WS L) q r := by
  intro L q r hq hqr hr
  exact fp81s21_moving_heat_ito_expectation_of_rs_values
    p R hδ hδh a ha hH hN A F hstd hlin hr0 hphys future hfuture L Φ hΦ
    Yh Fd Fj hYm hYae (WS L) q r hq hqr hr
    (hDOn L q r hq hqr hr) (hJOn L q r hq hqr hr)
    (hDval L q r hq hqr hr) (hJval L q r hq hqr hr)

#print axioms HRS.Fp81.S21.fp81s21_finproj_drift_adapter
#print axioms HRS.Fp81.S21.fp81s21_finproj_covariance_adapter
#print axioms HRS.Fp81.S21.fp81s21_finproj_covering_partition
#print axioms HRS.Fp81.S21.fp81s21_moving_heat_ito_expectation_of_rs_values
#print axioms HRS.Fp81.S21.fp81s21_moving_heat_ito_finite_projection_expectation_identity

end HRS.Fp81.S21

end
