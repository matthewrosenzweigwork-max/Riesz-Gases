import HRS.MC.E213M5
import HRS.MC.S7PICMain
import HRS.MC.E213TElem

/-!
# Packet E213U3, part A: series-level calculus of the covariance tensor `𝒥`

`Fterm`, `Fser` (the Fourier series of `PID`), `SJ` (the evaluation predicate of `e213m_series`, in series form),
the pointwise `L¹`-type bound of the series (`u3_Fser_bound`), linearity, integrability, additivity of `SJ`
in the coefficient and in the interval, uniqueness, and the conversion `SJ → IsJValue`.
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.E213U3

open HRS HRS.Sec7 HRS.MC.Sec7.PID HRS.MC.Sec7.S7PIDS

set_option maxSynthPendingDepth 3

variable {d : ℕ}

/-- The `p`-th term of the series of `PID`. -/
def Fterm (Rb : Regime d) (r m : ℝ) (zr : ℝ → NegSobolev d r) (ta tb : ℝ) (φa φb : Torus d → ℝ)
    (pr : NonzeroLattice d × NonzeroLattice d) (u : ℝ) : ℝ :=
  NegSobolev.eval (NegSobolev.ofSeq m (fun k => NegSobolev.fourierCoeff (zr u) k) : NegSobolev d m)
      (gradProd pr.1 pr.2) *
    NegSobolev.eval (Vprop Rb.D Rb.ρ m ta u (modeVec m pr.1)) φa *
    NegSobolev.eval (Vprop Rb.D Rb.ρ m tb u (modeVec m pr.2)) φb

/-- The series of `PID`. -/
def Fser (Rb : Regime d) (r m : ℝ) (zr : ℝ → NegSobolev d r) (ta tb : ℝ) (φa φb : Torus d → ℝ) (u : ℝ) : ℝ :=
  ∑' pr : NonzeroLattice d × NonzeroLattice d, Fterm Rb r m zr ta tb φa φb pr u

/-- The evaluation predicate of `E213M.e213m_series` (series form). -/
def SJ (Rb : Regime d) (r m G : ℝ) (zr : ℝ → NegSobolev d r) (I : Set ℝ)
    (J : TensorDual (PathSpace d m G) 2) : Prop :=
  J ∈ projTensor (PathSpace d m G) 2 ∧
  ∀ (ta tb : ℝ) (φa φb : Torus d → ℝ) (l₁ l₂ : StrongDual ℝ (PathSpace d m G)),
    Torus.IsSmooth φa → Torus.IsSmooth φb →
    ta ∈ Set.Icc (0 : ℝ) G → tb ∈ Set.Icc (0 : ℝ) G →
    (∀ w, l₁ w = NegSobolev.eval (pathAt w ta) φa) → (∀ w, l₂ w = NegSobolev.eval (pathAt w tb) φb) →
    J (prodForm l₁ l₂) = 2 * Rb.D.invβ * ∫ u in I ∩ Set.Icc 0 (min ta tb), Fser Rb r m zr ta tb φa φb u

/-- Pointwise bound of the terms: `|F_p(u)| ≤ ‖z(u)‖ H_p` with a summable `H`. -/
theorem u3_term_bound (Rb : Regime d) (r : ℝ) (hr : r = 2 * (d : ℝ) + 6) (m : ℝ)
    (hm : 3 * (d : ℝ) + 8 < m) (G : ℝ) (hG : 0 < G) (ta tb : ℝ) (hta : ta ∈ Set.Icc (0 : ℝ) G)
    (htb : tb ∈ Set.Icc (0 : ℝ) G) (φa φb : Torus d → ℝ) (hφa : Torus.IsSmooth φa)
    (hφb : Torus.IsSmooth φb) :
    ∃ H : NonzeroLattice d × NonzeroLattice d → ℝ, Summable H ∧ (∀ pr, 0 ≤ H pr) ∧
      ∀ (zr : ℝ → NegSobolev d r) (u : ℝ), 0 ≤ u → u ≤ ta → u ≤ tb → ∀ pr,
        |Fterm Rb r m zr ta tb φa φb pr u| ≤ ‖zr u‖ * H pr := by
  classical
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hr0 : 0 ≤ r := by rw [hr]; linarith
  have hrm : r ≤ m := by rw [hr]; linarith
  obtain ⟨Cg, hCg0, hCg⟩ := HRS.MC.Sec7.S7PIDR.s7_PID_gradprod_proof (d := d) r hr0
  obtain ⟨N, hN⟩ : ∃ N : ℕ, r + d + 2 ≤ N := ⟨⌈r + d + 2⌉₊, Nat.le_ceil _⟩
  obtain ⟨Aa, hAa0, hAa⟩ := HRS.MC.Sec7.S7PIDM.s7_PID_mode_decay_proof Rb m hm G hG φa hφa N
  obtain ⟨Ab, hAb0, hAb⟩ := HRS.MC.Sec7.S7PIDM.s7_PID_mode_decay_proof Rb m hm G hG φb hφb N
  obtain ⟨h, hhdef⟩ : ∃ h : NonzeroLattice d → ℝ, ∀ k, h k = Lattice.jp k.1 ^ (-((N : ℝ) - r - 1)) :=
    ⟨fun k => Lattice.jp k.1 ^ (-((N : ℝ) - r - 1)), fun _ => rfl⟩
  have hh0 : ∀ k, 0 ≤ h k := fun k => by rw [hhdef]; exact Real.rpow_nonneg (Torus.jp_pos k.1).le _
  have hhs : Summable h := by
    have hs := summable_jp_rpow (d := d) (((N : ℝ) - r - 1) / 2) (by linarith)
    refine hs.congr fun k => ?_
    rw [hhdef]
    congr 1
    ring
  have hhh : Summable fun pr : NonzeroLattice d × NonzeroLattice d => h pr.1 * h pr.2 :=
    Summable.mul_of_nonneg hhs hhs (fun k => hh0 k) (fun k => hh0 k)
  refine ⟨fun pr => Cg * Aa * Ab * (h pr.1 * h pr.2), hhh.mul_left _, fun pr => ?_, ?_⟩
  · have := hh0 pr.1; have := hh0 pr.2
    positivity
  · intro zr u hu0 hua hub pr
    obtain ⟨hmemS, hnormS⟩ := hCg pr.1 pr.2
    have h1 := S7PIDS_bound_eval (m := m) hrm hmemS hnormS (le_refl ‖zr u‖)
    have h2 := hAa u ta hu0 hua hta.2 pr.1
    have h3 := hAb u tb hu0 hub htb.2 pr.2
    have e1 : Lattice.jp pr.1.1 ^ (r + 1) * Lattice.jp pr.1.1 ^ (-(N : ℝ)) = h pr.1 := by
      rw [← Real.rpow_add (Torus.jp_pos _), hhdef]; congr 1; ring
    have e2 : Lattice.jp pr.2.1 ^ (r + 1) * Lattice.jp pr.2.1 ^ (-(N : ℝ)) = h pr.2 := by
      rw [← Real.rpow_add (Torus.jp_pos _), hhdef]; congr 1; ring
    have hj1 : 0 ≤ Lattice.jp pr.1.1 ^ (-(N : ℝ)) := Real.rpow_nonneg (Torus.jp_pos _).le _
    have hj2 : 0 ≤ Lattice.jp pr.2.1 ^ (-(N : ℝ)) := Real.rpow_nonneg (Torus.jp_pos _).le _
    have hp1 : 0 ≤ Lattice.jp pr.1.1 ^ (r + 1) := Real.rpow_nonneg (Torus.jp_pos _).le _
    have hp2 : 0 ≤ Lattice.jp pr.2.1 ^ (r + 1) := Real.rpow_nonneg (Torus.jp_pos _).le _
    have hM0 : 0 ≤ ‖zr u‖ := norm_nonneg _
    unfold Fterm
    rw [abs_mul, abs_mul]
    calc _ ≤ (‖zr u‖ * (Cg * Lattice.jp pr.1.1 ^ (r + 1) * Lattice.jp pr.2.1 ^ (r + 1))) *
          (Aa * Lattice.jp pr.1.1 ^ (-(N : ℝ))) * (Ab * Lattice.jp pr.2.1 ^ (-(N : ℝ))) :=
          mul_le_mul (mul_le_mul h1 h2 (abs_nonneg _)
            (mul_nonneg hM0 (mul_nonneg (mul_nonneg hCg0 hp1) hp2))) h3 (abs_nonneg _)
            (mul_nonneg (mul_nonneg hM0 (mul_nonneg (mul_nonneg hCg0 hp1) hp2))
              (mul_nonneg hAa0 hj1))
      _ = ‖zr u‖ * (Cg * Aa * Ab * ((Lattice.jp pr.1.1 ^ (r + 1) * Lattice.jp pr.1.1 ^ (-(N : ℝ))) *
          (Lattice.jp pr.2.1 ^ (r + 1) * Lattice.jp pr.2.1 ^ (-(N : ℝ))))) := by ring
      _ = ‖zr u‖ * (Cg * Aa * Ab * (h pr.1 * h pr.2)) := by rw [e1, e2]

/-- Summability of the series and its `L¹`-type bound `|F(u)| ≤ C_φ ‖z(u)‖` (pointwise in `u`). -/
theorem u3_Fser_bound (Rb : Regime d) (r : ℝ) (hr : r = 2 * (d : ℝ) + 6) (m : ℝ)
    (hm : 3 * (d : ℝ) + 8 < m) (G : ℝ) (hG : 0 < G) (ta tb : ℝ) (hta : ta ∈ Set.Icc (0 : ℝ) G)
    (htb : tb ∈ Set.Icc (0 : ℝ) G) (φa φb : Torus d → ℝ) (hφa : Torus.IsSmooth φa)
    (hφb : Torus.IsSmooth φb) :
    ∃ Cφ : ℝ, 0 ≤ Cφ ∧ ∀ (zr : ℝ → NegSobolev d r) (u : ℝ), 0 ≤ u → u ≤ ta → u ≤ tb →
      Summable (fun pr => Fterm Rb r m zr ta tb φa φb pr u) ∧
      |Fser Rb r m zr ta tb φa φb u| ≤ Cφ * ‖zr u‖ := by
  obtain ⟨H, hHs, hH0, hHb⟩ := u3_term_bound Rb r hr m hm G hG ta tb hta htb φa φb hφa hφb
  refine ⟨∑' pr, H pr, tsum_nonneg hH0, fun zr u hu0 hua hub => ?_⟩
  have hs : Summable (fun pr => Fterm Rb r m zr ta tb φa φb pr u) :=
    Summable.of_norm_bounded (hHs.mul_left ‖zr u‖) (fun pr => by
      rw [Real.norm_eq_abs]; exact hHb zr u hu0 hua hub pr)
  refine ⟨hs, ?_⟩
  unfold Fser
  rw [← Real.norm_eq_abs]
  refine (tsum_of_norm_bounded (hHs.mul_left ‖zr u‖).hasSum (fun pr => by
    rw [Real.norm_eq_abs]; exact hHb zr u hu0 hua hub pr)).trans ?_
  rw [tsum_mul_left]
  exact le_of_eq (mul_comm _ _)

/-- Linearity of the evaluation of an embedded vector against a `H^r` test function. -/
theorem u3_eval_embed_sub {r m : ℝ} (hrm : r ≤ m) {ψ : Torus d → ℝ} (hψ : MemSobolev r ψ)
    (x y : NegSobolev d r) :
    NegSobolev.eval (NegSobolev.ofSeq m (fun k => NegSobolev.fourierCoeff (x - y) k) : NegSobolev d m) ψ =
      NegSobolev.eval (NegSobolev.ofSeq m (fun k => NegSobolev.fourierCoeff x k) : NegSobolev d m) ψ -
      NegSobolev.eval (NegSobolev.ofSeq m (fun k => NegSobolev.fourierCoeff y k) : NegSobolev d m) ψ := by
  rw [S7PIDS_eval_embed hrm, S7PIDS_eval_embed hrm, S7PIDS_eval_embed hrm,
    ← HRS.GF.gfb4_ell_apply hψ, ← HRS.GF.gfb4_ell_apply hψ, ← HRS.GF.gfb4_ell_apply hψ, map_sub]

theorem u3_eval_embed_zero {r m : ℝ} (hrm : r ≤ m) {ψ : Torus d → ℝ} (hψ : MemSobolev r ψ) :
    NegSobolev.eval (NegSobolev.ofSeq m (fun k => NegSobolev.fourierCoeff (0 : NegSobolev d r) k) :
      NegSobolev d m) ψ = 0 := by
  rw [S7PIDS_eval_embed hrm, ← HRS.GF.gfb4_ell_apply hψ, map_zero]

/-- Linearity of the terms in the coefficient. -/
theorem u3_Fterm_sub (Rb : Regime d) (r : ℝ) (hr : r = 2 * (d : ℝ) + 6) (m : ℝ)
    (hm : 3 * (d : ℝ) + 8 < m) (z₁ z₂ : ℝ → NegSobolev d r) (ta tb : ℝ) (φa φb : Torus d → ℝ)
    (pr : NonzeroLattice d × NonzeroLattice d) (u : ℝ) :
    Fterm Rb r m (fun v => z₁ v - z₂ v) ta tb φa φb pr u =
      Fterm Rb r m z₁ ta tb φa φb pr u - Fterm Rb r m z₂ ta tb φa φb pr u := by
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hr0 : 0 ≤ r := by rw [hr]; linarith
  have hrm : r ≤ m := by rw [hr]; linarith
  obtain ⟨Cg, -, hCg⟩ := HRS.MC.Sec7.S7PIDR.s7_PID_gradprod_proof (d := d) r hr0
  unfold Fterm
  rw [u3_eval_embed_sub hrm (hCg pr.1 pr.2).1]
  ring

theorem u3_Fterm_zero (Rb : Regime d) (r : ℝ) (hr : r = 2 * (d : ℝ) + 6) (m : ℝ)
    (hm : 3 * (d : ℝ) + 8 < m) (z : ℝ → NegSobolev d r) (ta tb : ℝ) (φa φb : Torus d → ℝ)
    (pr : NonzeroLattice d × NonzeroLattice d) (u : ℝ) (hu : z u = 0) :
    Fterm Rb r m z ta tb φa φb pr u = 0 := by
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hr0 : 0 ≤ r := by rw [hr]; linarith
  have hrm : r ≤ m := by rw [hr]; linarith
  obtain ⟨Cg, -, hCg⟩ := HRS.MC.Sec7.S7PIDR.s7_PID_gradprod_proof (d := d) r hr0
  unfold Fterm
  rw [hu, u3_eval_embed_zero hrm (hCg pr.1 pr.2).1]
  ring

theorem u3_Fser_sub (Rb : Regime d) (r : ℝ) (hr : r = 2 * (d : ℝ) + 6) (m : ℝ)
    (hm : 3 * (d : ℝ) + 8 < m) (G : ℝ) (hG : 0 < G) (ta tb : ℝ) (hta : ta ∈ Set.Icc (0 : ℝ) G)
    (htb : tb ∈ Set.Icc (0 : ℝ) G) (φa φb : Torus d → ℝ) (hφa : Torus.IsSmooth φa)
    (hφb : Torus.IsSmooth φb) (z₁ z₂ : ℝ → NegSobolev d r) (u : ℝ) (hu0 : 0 ≤ u) (hua : u ≤ ta)
    (hub : u ≤ tb) :
    Fser Rb r m (fun v => z₁ v - z₂ v) ta tb φa φb u =
      Fser Rb r m z₁ ta tb φa φb u - Fser Rb r m z₂ ta tb φa φb u := by
  obtain ⟨Cφ, -, hC⟩ := u3_Fser_bound Rb r hr m hm G hG ta tb hta htb φa φb hφa hφb
  have h1 := (hC z₁ u hu0 hua hub).1
  have h2 := (hC z₂ u hu0 hua hub).1
  unfold Fser
  rw [← Summable.tsum_sub h1 h2]
  exact tsum_congr fun pr => u3_Fterm_sub Rb r hr m hm z₁ z₂ ta tb φa φb pr u

theorem u3_Fser_zero (Rb : Regime d) (r : ℝ) (hr : r = 2 * (d : ℝ) + 6) (m : ℝ)
    (hm : 3 * (d : ℝ) + 8 < m) (z : ℝ → NegSobolev d r) (ta tb : ℝ) (φa φb : Torus d → ℝ)
    (u : ℝ) (hu : z u = 0) : Fser Rb r m z ta tb φa φb u = 0 := by
  unfold Fser
  exact (tsum_congr fun pr => u3_Fterm_zero Rb r hr m hm z ta tb φa φb pr u hu).trans tsum_zero

theorem u3_Fser_congr (Rb : Regime d) (r m : ℝ) (z z' : ℝ → NegSobolev d r) (ta tb : ℝ)
    (φa φb : Torus d → ℝ) (u : ℝ) (hu : z u = z' u) :
    Fser Rb r m z ta tb φa φb u = Fser Rb r m z' ta tb φa φb u := by
  unfold Fser Fterm
  simp only [hu]

/-- Integrability of the series on `I ∩ [0, t_a ∧ t_b]` for a measurable coefficient with `‖z‖` integrable on `I`. -/
theorem u3_Fser_integrableOn (Rb : Regime d) (r : ℝ) (hr : r = 2 * (d : ℝ) + 6) (m : ℝ)
    (hm : 3 * (d : ℝ) + 8 < m) (G : ℝ) (hG : 0 < G) (ta tb : ℝ) (hta : ta ∈ Set.Icc (0 : ℝ) G)
    (htb : tb ∈ Set.Icc (0 : ℝ) G) (φa φb : Torus d → ℝ) (hφa : Torus.IsSmooth φa)
    (hφb : Torus.IsSmooth φb) (zr : ℝ → NegSobolev d r) (hzr : Measurable zr) {I : Set ℝ}
    (hI : MeasurableSet I) (hIsub : I ⊆ Set.Ioc 0 G) (hint : IntegrableOn (fun u => ‖zr u‖) I) :
    IntegrableOn (Fser Rb r m zr ta tb φa φb) (I ∩ Set.Icc 0 (min ta tb)) := by
  classical
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hr0 : 0 ≤ r := by rw [hr]; linarith
  have hrm : r ≤ m := by rw [hr]; linarith
  obtain ⟨Cg, -, hCg⟩ := HRS.MC.Sec7.S7PIDR.s7_PID_gradprod_proof (d := d) r hr0
  obtain ⟨Cφ, hCφ0, hC⟩ := u3_Fser_bound Rb r hr m hm G hG ta tb hta htb φa φb hφa hφb
  set S : Set ℝ := I ∩ Set.Icc 0 (min ta tb) with hSdef
  have hSm : MeasurableSet S := hI.inter measurableSet_Icc
  have hSsub : S ⊆ Set.Ioc 0 G := fun u hu => hIsub hu.1
  have hSa : ∀ u ∈ S, u ≤ ta := fun u hu => hu.2.2.trans (min_le_left _ _)
  have hSb : ∀ u ∈ S, u ≤ tb := fun u hu => hu.2.2.trans (min_le_right _ _)
  have hFm : ∀ pr, AEStronglyMeasurable (fun u => Fterm Rb r m zr ta tb φa φb pr u) (volume.restrict S) := by
    intro pr
    obtain ⟨hmemS, -⟩ := hCg pr.1 pr.2
    unfold Fterm
    exact ((S7PIDS_meas_eval hrm hmemS hzr).aestronglyMeasurable.mul
      (S7PIDS_meas_V Rb m hm G hG hφa hta pr.1 hSm hSsub hSa)).mul
      (S7PIDS_meas_V Rb m hm G hG hφb htb pr.2 hSm hSsub hSb)
  have hHas : ∀ u ∈ S, HasSum (fun pr => Fterm Rb r m zr ta tb φa φb pr u) (Fser Rb r m zr ta tb φa φb u) :=
    fun u hu => (hC zr u hu.2.1 (hSa u hu) (hSb u hu)).1.hasSum
  have hfm : AEStronglyMeasurable (Fser Rb r m zr ta tb φa φb) (volume.restrict S) := by
    refine aestronglyMeasurable_of_tendsto_ae
      (Filter.atTop : Filter (Finset (NonzeroLattice d × NonzeroLattice d)))
      (f := fun s u => ∑ pr ∈ s, Fterm Rb r m zr ta tb φa φb pr u)
      (fun s => Finset.aestronglyMeasurable_fun_sum s (fun pr _ => hFm pr)) ?_
    exact (ae_restrict_iff' hSm).2 (Filter.Eventually.of_forall fun u hu => hHas u hu)
  have hint' : IntegrableOn (fun u => Cφ * ‖zr u‖) S :=
    (hint.mono_set Set.inter_subset_left).const_mul Cφ
  refine Integrable.mono' hint' hfm ?_
  refine (ae_restrict_iff' hSm).2 (Filter.Eventually.of_forall fun u hu => ?_)
  rw [Real.norm_eq_abs]
  exact (hC zr u hu.2.1 (hSa u hu) (hSb u hu)).2

/-- Integrability of the series for all admissible tests. -/
def IntOK (Rb : Regime d) (r m G : ℝ) (zr : ℝ → NegSobolev d r) (I : Set ℝ) : Prop :=
  ∀ (ta tb : ℝ) (φa φb : Torus d → ℝ), Torus.IsSmooth φa → Torus.IsSmooth φb →
    ta ∈ Set.Icc (0 : ℝ) G → tb ∈ Set.Icc (0 : ℝ) G →
    IntegrableOn (Fser Rb r m zr ta tb φa φb) (I ∩ Set.Icc 0 (min ta tb))

theorem u3_intOK (Rb : Regime d) (r : ℝ) (hr : r = 2 * (d : ℝ) + 6) (m : ℝ)
    (hm : 3 * (d : ℝ) + 8 < m) (G : ℝ) (hG : 0 < G) (zr : ℝ → NegSobolev d r) (hzr : Measurable zr)
    {I : Set ℝ} (hI : MeasurableSet I) (hIsub : I ⊆ Set.Ioc 0 G)
    (hint : IntegrableOn (fun u => ‖zr u‖) I) : IntOK Rb r m G zr I :=
  fun ta tb φa φb hφa hφb hta htb =>
    u3_Fser_integrableOn Rb r hr m hm G hG ta tb hta htb φa φb hφa hφb zr hzr hI hIsub hint

theorem IntOK.mono {Rb : Regime d} {r m G : ℝ} {zr : ℝ → NegSobolev d r} {I I' : Set ℝ}
    (h : IntOK Rb r m G zr I) (hII : I' ⊆ I) : IntOK Rb r m G zr I' :=
  fun ta tb φa φb hφa hφb hta htb =>
    (h ta tb φa φb hφa hφb hta htb).mono_set (Set.inter_subset_inter_left _ hII)

/-- `SJ` is additive in the coefficient. -/
theorem u3_SJ_sub (Rb : Regime d) (r : ℝ) (hr : r = 2 * (d : ℝ) + 6) (m : ℝ)
    (hm : 3 * (d : ℝ) + 8 < m) (G : ℝ) (hG : 0 < G) {z₁ z₂ : ℝ → NegSobolev d r} {I : Set ℝ}
    (hIm : MeasurableSet I) {J₁ J₂ : TensorDual (PathSpace d m G) 2}
    (h₁ : SJ Rb r m G z₁ I J₁) (h₂ : SJ Rb r m G z₂ I J₂)
    (i₁ : IntOK Rb r m G z₁ I) (i₂ : IntOK Rb r m G z₂ I) :
    SJ Rb r m G (fun v => z₁ v - z₂ v) I (J₁ - J₂) := by
  refine ⟨Submodule.sub_mem _ h₁.1 h₂.1, ?_⟩
  intro ta tb φa φb l₁ l₂ hφa hφb hta htb hl₁ hl₂
  rw [sub_apply, h₁.2 ta tb φa φb l₁ l₂ hφa hφb hta htb hl₁ hl₂,
    h₂.2 ta tb φa φb l₁ l₂ hφa hφb hta htb hl₁ hl₂, ← mul_sub,
    ← integral_sub (i₁ ta tb φa φb hφa hφb hta htb) (i₂ ta tb φa φb hφa hφb hta htb)]
  congr 1
  refine setIntegral_congr_fun (hIm.inter measurableSet_Icc) fun u hu => ?_
  exact (u3_Fser_sub Rb r hr m hm G hG ta tb hta htb φa φb hφa hφb z₁ z₂ u hu.2.1
    (hu.2.2.trans (min_le_left _ _)) (hu.2.2.trans (min_le_right _ _))).symm

/-- `SJ` is additive in the interval. -/
theorem u3_SJ_union (Rb : Regime d) (r m G : ℝ) {z : ℝ → NegSobolev d r} {I₁ I₂ : Set ℝ}
    (hd : Disjoint I₁ I₂) (h₂m : MeasurableSet I₂) {J₁ J₂ : TensorDual (PathSpace d m G) 2}
    (h₁ : SJ Rb r m G z I₁ J₁) (h₂ : SJ Rb r m G z I₂ J₂)
    (i₁ : IntOK Rb r m G z I₁) (i₂ : IntOK Rb r m G z I₂) :
    SJ Rb r m G z (I₁ ∪ I₂) (J₁ + J₂) := by
  refine ⟨Submodule.add_mem (projTensor (PathSpace d m G) 2) h₁.1 h₂.1, ?_⟩
  intro ta tb φa φb l₁ l₂ hφa hφb hta htb hl₁ hl₂
  rw [add_apply, h₁.2 ta tb φa φb l₁ l₂ hφa hφb hta htb hl₁ hl₂,
    h₂.2 ta tb φa φb l₁ l₂ hφa hφb hta htb hl₁ hl₂, ← mul_add, Set.union_inter_distrib_right,
    setIntegral_union (hd.mono Set.inter_subset_left Set.inter_subset_left)
      (h₂m.inter measurableSet_Icc) (i₁ ta tb φa φb hφa hφb hta htb) (i₂ ta tb φa φb hφa hφb hta htb)]

/-- `SJ` only sees the coefficient on `I ∩ [0,∞)`. -/
theorem u3_SJ_congr (Rb : Regime d) (r m G : ℝ) {z z' : ℝ → NegSobolev d r} {I : Set ℝ}
    (hIm : MeasurableSet I) (hzz : ∀ u ∈ I, 0 ≤ u → z u = z' u)
    {J : TensorDual (PathSpace d m G) 2} (h : SJ Rb r m G z I J) : SJ Rb r m G z' I J := by
  refine ⟨h.1, ?_⟩
  intro ta tb φa φb l₁ l₂ hφa hφb hta htb hl₁ hl₂
  rw [h.2 ta tb φa φb l₁ l₂ hφa hφb hta htb hl₁ hl₂]
  congr 1
  refine setIntegral_congr_fun (hIm.inter measurableSet_Icc) fun u hu => ?_
  exact u3_Fser_congr Rb r m z z' ta tb φa φb u (hzz u hu.1 hu.2.1)

theorem u3_IntOK_congr {Rb : Regime d} {r m G : ℝ} {z z' : ℝ → NegSobolev d r} {I : Set ℝ}
    (hIm : MeasurableSet I) (hzz : ∀ u ∈ I, 0 ≤ u → z u = z' u) (h : IntOK Rb r m G z I) :
    IntOK Rb r m G z' I := by
  intro ta tb φa φb hφa hφb hta htb
  refine (h ta tb φa φb hφa hφb hta htb).congr_fun (fun u hu => ?_) (hIm.inter measurableSet_Icc)
  exact u3_Fser_congr Rb r m z z' ta tb φa φb u (hzz u hu.1 hu.2.1)

/-- The empty interval carries the zero tensor. -/
theorem u3_SJ_empty (Rb : Regime d) (r m G : ℝ) (z : ℝ → NegSobolev d r) :
    SJ Rb r m G z ∅ 0 := by
  refine ⟨Submodule.zero_mem _, ?_⟩
  intro ta tb φa φb l₁ l₂ hφa hφb hta htb hl₁ hl₂
  simp

theorem u3_IntOK_empty (Rb : Regime d) (r m G : ℝ) (z : ℝ → NegSobolev d r) :
    IntOK Rb r m G z ∅ := by
  intro ta tb φa φb hφa hφb hta htb
  simp

/-- Uniqueness of tensors in `projTensor` with prescribed evaluations. -/
theorem u3_eq_of_eval (R : Regime d) (m G : ℝ) {J₁ J₂ : TensorDual (PathSpace d m G) 2}
    (h₁ : J₁ ∈ projTensor (PathSpace d m G) 2) (h₂ : J₂ ∈ projTensor (PathSpace d m G) 2)
    (h : ∀ (ta tb : ℝ) (φa φb : Torus d → ℝ) (l₁ l₂ : StrongDual ℝ (PathSpace d m G)),
      Torus.IsSmooth φa → Torus.IsSmooth φb → ta ∈ Set.Icc (0 : ℝ) G → tb ∈ Set.Icc (0 : ℝ) G →
      (∀ w, l₁ w = NegSobolev.eval (pathAt w ta) φa) → (∀ w, l₂ w = NegSobolev.eval (pathAt w tb) φb) →
      J₁ (prodForm l₁ l₂) = J₂ (prodForm l₁ l₂)) : J₁ = J₂ := by
  have hz : IsJValue R.D R.ρ m G (fun _ => (0 : NegSobolev d m)) (∅ : Set ℝ) (J₁ - J₂) := by
    refine ⟨Submodule.sub_mem _ h₁ h₂, ?_⟩
    intro ta tb φa φb l₁ l₂ hφa hφb hta htb hl₁ hl₂
    have := h ta tb φa φb l₁ l₂ hφa hφb hta htb hl₁ hl₂
    simp only [Set.empty_inter, setIntegral_empty, mul_zero]
    rw [sub_apply]
    exact sub_eq_zero.2 this
  have hz0 : IsJValue R.D R.ρ m G (fun _ => (0 : NegSobolev d m)) (∅ : Set ℝ) 0 := by
    refine ⟨Submodule.zero_mem _, ?_⟩
    intro ta tb φa φb l₁ l₂ hφa hφb hta htb hl₁ hl₂
    simp
  have := HRS.MC.Sec7.S7PIC.s7_PI_C_J_unique_proof R m G _ _ _ _ hz hz0
  exact sub_eq_zero.1 this

/-- Uniqueness for `SJ`. -/
theorem u3_SJ_unique (Rb : Regime d) (r m G : ℝ) {z : ℝ → NegSobolev d r} {I : Set ℝ}
    {J₁ J₂ : TensorDual (PathSpace d m G) 2} (h₁ : SJ Rb r m G z I J₁) (h₂ : SJ Rb r m G z I J₂) :
    J₁ = J₂ := by
  refine u3_eq_of_eval Rb m G h₁.1 h₂.1 ?_
  intro ta tb φa φb l₁ l₂ hφa hφb hta htb hl₁ hl₂
  rw [h₁.2 ta tb φa φb l₁ l₂ hφa hφb hta htb hl₁ hl₂, h₂.2 ta tb φa φb l₁ l₂ hφa hφb hta htb hl₁ hl₂]

/-- The series form implies `IsJValue`. -/
theorem u3_SJ_isJValue (Rb : Regime d) (r : ℝ) (hr : r = 2 * (d : ℝ) + 6) (m : ℝ)
    (hm : 3 * (d : ℝ) + 8 < m) (G : ℝ) (hG : 0 < G) {z : ℝ → NegSobolev d r} {I : Set ℝ}
    (hIm : MeasurableSet I) {J : TensorDual (PathSpace d m G) 2} (h : SJ Rb r m G z I J) :
    IsJValue Rb.D Rb.ρ m G (fun u => NegSobolev.ofSeq m (fun k => NegSobolev.fourierCoeff (z u) k)) I J := by
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hrm : r ≤ m := by rw [hr]; linarith
  refine ⟨h.1, ?_⟩
  intro ta tb φa φb l₁ l₂ hφa hφb hta htb hl₁ hl₂
  have e := h.2 ta tb φa φb l₁ l₂ hφa hφb hta htb hl₁ hl₂
  unfold prodForm at e
  rw [e]
  congr 1
  refine setIntegral_congr_fun (hIm.inter measurableSet_Icc) fun u hu => ?_
  have hua : u ≤ ta := hu.2.2.trans (min_le_left _ _)
  have hub : u ≤ tb := hu.2.2.trans (min_le_right _ _)
  have hz : Memℓp (fun k : NonzeroLattice d => Lattice.jp k.1 ^ (-r) *
      NegSobolev.fourierCoeff
        (NegSobolev.ofSeq m (fun k => NegSobolev.fourierCoeff (z u) k) : NegSobolev d m) k) 2 := by
    refine (Torus.memℓp_two_iff _).2 ?_
    refine (HRS.MC.Sec7.PIE.pie_coeff_summable (z u)).congr fun k => ?_
    rw [S7PIDS_fc_embed hrm (z u) k]
  exact (HRS.MC.Sec7.S7PIDE.s7_PID_expansion_proof Rb r hr m hm G hG φa φb hφa hφb
    u ta tb hu.2.1 hua hub hta.2 htb.2 _ hz).tsum_eq

/-- The bounded (`L^∞`) theorem of `E213M`, in the form `SJ`. -/
theorem u3_bounded (R : Regime d) (r : ℝ) (hr : r = 2 * (d : ℝ) + 6) (m : ℝ)
    (hm : 3 * (d : ℝ) + 8 < m) (G : ℝ) (hG : 0 < G) :
    ∃ C : ℝ, ∀ b₀ : ℝ, ∀ hb₀ : 0 ≤ b₀, ∀ (zr : ℝ → NegSobolev d r), Measurable zr → ∀ M : ℝ,
      (∀ u ∈ Set.Icc (0 : ℝ) G, ‖zr u‖ ≤ M) → ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ G →
      ∃ J, SJ (HRS.MC.E213F.shift R b₀ hb₀) r m G zr (Set.Ioc a b) J ∧ ‖J‖ ≤ C * M * (b - a) := by
  obtain ⟨C, hC⟩ := HRS.MC.E213M.e213m_series R r hr m hm G hG
  refine ⟨C, fun b₀ hb₀ zr hzr M hM a b ha hab hbG => ?_⟩
  obtain ⟨J, hJm, hJn, hJe⟩ := hC b₀ hb₀ zr hzr M hM a b ha hab hbG
  exact ⟨J, ⟨hJm, hJe⟩, hJn⟩

end HRS.MC.E213U3

end
