import HRS.MC.E213M3
import HRS.MC.S7PIDSMain

/-!
# Packet E213M4: family-quantified `s7_PID_series_proof` (Theorem 2.13, translation-uniform PI-D)

The constant `C = 2 |invβ| K Cg G` is chosen before the shift `b₀ ≥ 0`; the regimes are `E213F.shift R b₀ hb₀` at the
fixed horizon `T`.  (`invβ` is a property of `D`, which `shift` does not change.)
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.E213M

open HRS HRS.Sec7 HRS.MC.Sec7.PID HRS.MC.Sec7.S7PIDS

variable {d : ℕ}

set_option maxHeartbeats 1000000 in
set_option maxSynthPendingDepth 3 in
theorem e213m_series (R : Regime d) (r : ℝ) (hr : r = 2 * (d : ℝ) + 6) (m : ℝ)
    (hm : 3 * (d : ℝ) + 8 < m) (T : ℝ) (hT : 0 < T) :
    ∃ C : ℝ, ∀ b₀ : ℝ, ∀ hb₀ : 0 ≤ b₀, ∀ (zr : ℝ → NegSobolev d r), Measurable zr → ∀ M : ℝ, (∀ u ∈ Set.Icc (0 : ℝ) T, ‖zr u‖ ≤ M) →
      ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ T →
      ∃ J : TensorDual (PathSpace d m T) 2, J ∈ projTensor (PathSpace d m T) 2 ∧ ‖J‖ ≤ C * M * (b - a) ∧
        ∀ (ta tb : ℝ) (φa φb : Torus d → ℝ) (l₁ l₂ : StrongDual ℝ (PathSpace d m T)),
          Torus.IsSmooth φa → Torus.IsSmooth φb →
          ta ∈ Set.Icc (0 : ℝ) T → tb ∈ Set.Icc (0 : ℝ) T →
          (∀ w, l₁ w = NegSobolev.eval (pathAt w ta) φa) → (∀ w, l₂ w = NegSobolev.eval (pathAt w tb) φb) →
          J (prodForm l₁ l₂) = 2 * R.D.invβ * ∫ u in Set.Ioc a b ∩ Set.Icc 0 (min ta tb),
            ∑' p : NonzeroLattice d × NonzeroLattice d,
              NegSobolev.eval (NegSobolev.ofSeq m (fun k => NegSobolev.fourierCoeff (zr u) k)) (gradProd p.1 p.2) *
                NegSobolev.eval (Vprop (HRS.MC.E213F.shift R b₀ hb₀).D (HRS.MC.E213F.shift R b₀ hb₀).ρ m ta u (modeVec m p.1)) φa *
                NegSobolev.eval (Vprop (HRS.MC.E213F.shift R b₀ hb₀).D (HRS.MC.E213F.shift R b₀ hb₀).ρ m tb u (modeVec m p.2)) φb := by
  classical
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hr0 : 0 ≤ r := by rw [hr]; linarith
  have hrm : r ≤ m := by rw [hr]; linarith
  have hmr : (d : ℝ) < m - r - 2 := by rw [hr]; linarith
  obtain ⟨K, hK0, hcov⟩ := HRS.MC.E213M.e213m_cov R m hm T hT
  obtain ⟨Cg, hCg0, hCg⟩ := HRS.MC.Sec7.S7PIDR.s7_PID_gradprod_proof (d := d) r hr0
  -- the summable weights
  obtain ⟨g, hgdef⟩ : ∃ g : NonzeroLattice d → ℝ, ∀ k, g k = Lattice.jp k.1 ^ (-(m - r - 2)) :=
    ⟨fun k => Lattice.jp k.1 ^ (-(m - r - 2)), fun _ => rfl⟩
  have hg0 : ∀ k, 0 ≤ g k := fun k => by rw [hgdef]; exact Real.rpow_nonneg (Torus.jp_pos k.1).le _
  have hg : Summable g := by
    have h := summable_jp_rpow (d := d) ((m - r - 2) / 2) (by linarith)
    refine h.congr fun k => ?_
    rw [hgdef]
    congr 1
    ring
  have hgg : Summable fun pr : NonzeroLattice d × NonzeroLattice d => g pr.1 * g pr.2 :=
    Summable.mul_of_nonneg hg hg (fun k => hg0 k) (fun k => hg0 k)
  obtain ⟨G, hG⟩ : ∃ G : ℝ, G = ∑' pr : NonzeroLattice d × NonzeroLattice d, g pr.1 * g pr.2 := ⟨_, rfl⟩
  have hG0 : 0 ≤ G := by
    rw [hG]; exact tsum_nonneg fun pr => mul_nonneg (hg0 _) (hg0 _)
  refine ⟨2 * |R.D.invβ| * K * Cg * G, fun b₀ hb₀ => ?_⟩
  have hcov := hcov b₀ hb₀
  set Rb := HRS.MC.E213F.shift R b₀ hb₀ with hRb
  intro zr hzr M hM a b ha hab hbT
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 ⟨le_rfl, hT.le⟩)
  -- the tensors `τ_{kl}`
  have hex : ∀ pr : NonzeroLattice d × NonzeroLattice d, ∃ τ : TensorDual (PathSpace d m T) 2,
      τ ∈ projTensor (PathSpace d m T) 2 ∧ ‖τ‖ ≤ K * Cg * M * (b - a) * (g pr.1 * g pr.2) ∧
      ∀ (ta tb : ℝ) (φa φb : Torus d → ℝ) (l₁ l₂ : StrongDual ℝ (PathSpace d m T)),
        Torus.IsSmooth φa → Torus.IsSmooth φb →
        ta ∈ Set.Icc (0 : ℝ) T → tb ∈ Set.Icc (0 : ℝ) T →
        (∀ w, l₁ w = NegSobolev.eval (pathAt w ta) φa) → (∀ w, l₂ w = NegSobolev.eval (pathAt w tb) φb) →
        τ (prodForm l₁ l₂) = ∫ u in Set.Ioc a b ∩ Set.Icc 0 (min ta tb),
          NegSobolev.eval (NegSobolev.ofSeq m (fun k => NegSobolev.fourierCoeff (zr u) k))
              (gradProd pr.1 pr.2) *
            NegSobolev.eval (Vprop Rb.D Rb.ρ m ta u (modeVec m pr.1)) φa *
            NegSobolev.eval (Vprop Rb.D Rb.ρ m tb u (modeVec m pr.2)) φb := by
    intro pr
    obtain ⟨hmemS, hnormS⟩ := hCg pr.1 pr.2
    obtain ⟨B, hB⟩ : ∃ B : ℝ, B = M * (Cg * Lattice.jp pr.1.1 ^ (r + 1) * Lattice.jp pr.2.1 ^ (r + 1)) :=
      ⟨_, rfl⟩
    have hB0 : 0 ≤ B := by
      rw [hB]
      exact mul_nonneg hM0 (mul_nonneg (mul_nonneg hCg0 (Real.rpow_nonneg (Torus.jp_pos _).le _))
        (Real.rpow_nonneg (Torus.jp_pos _).le _))
    obtain ⟨Ai, hAi⟩ : ∃ Ai : ℝ → ℝ, Ai = (Set.Icc (0 : ℝ) T).indicator (fun u => NegSobolev.eval
        (NegSobolev.ofSeq m (fun k => NegSobolev.fourierCoeff (zr u) k) : NegSobolev d m)
          (gradProd pr.1 pr.2)) := ⟨_, rfl⟩
    have hmeasA : Measurable fun u => NegSobolev.eval
        (NegSobolev.ofSeq m (fun k => NegSobolev.fourierCoeff (zr u) k) : NegSobolev d m)
          (gradProd pr.1 pr.2) := S7PIDS_meas_eval hrm hmemS hzr
    have hAimeas : Measurable Ai := by rw [hAi]; exact hmeasA.indicator measurableSet_Icc
    have hAibd : ∀ u, |Ai u| ≤ B := by
      intro u
      by_cases hu : u ∈ Set.Icc (0 : ℝ) T
      · rw [hAi, Set.indicator_of_mem hu, hB]
        exact S7PIDS_bound_eval hrm hmemS hnormS (hM u hu)
      · rw [hAi, Set.indicator_of_notMem hu, abs_zero]; exact hB0
    obtain ⟨p, q, hp, hq, hpb, hqb, hpq⟩ := S7PIDS_pq hAimeas hAibd
    obtain ⟨τ, hτm, hτn, hτe⟩ := hcov p q (Real.sqrt B) (Real.sqrt B) hp hq hpb hqb a b ha hab hbT
      pr.1 pr.2
    refine ⟨τ, hτm, ?_, ?_⟩
    · have hs : Real.sqrt B * Real.sqrt B = B := Real.mul_self_sqrt hB0
      have e1 : Lattice.jp pr.1.1 ^ (r + 1) * Lattice.jp pr.1.1 ^ (-(m - 1)) = g pr.1 := by
        rw [← Real.rpow_add (Torus.jp_pos _), hgdef]; congr 1; ring
      have e2 : Lattice.jp pr.2.1 ^ (r + 1) * Lattice.jp pr.2.1 ^ (-(m - 1)) = g pr.2 := by
        rw [← Real.rpow_add (Torus.jp_pos _), hgdef]; congr 1; ring
      calc ‖τ‖ ≤ K * Real.sqrt B * Real.sqrt B * Lattice.jp pr.1.1 ^ (-(m - 1)) *
            Lattice.jp pr.2.1 ^ (-(m - 1)) * (b - a) := hτn
        _ = K * (Real.sqrt B * Real.sqrt B) * Lattice.jp pr.1.1 ^ (-(m - 1)) *
            Lattice.jp pr.2.1 ^ (-(m - 1)) * (b - a) := by ring
        _ = K * B * Lattice.jp pr.1.1 ^ (-(m - 1)) * Lattice.jp pr.2.1 ^ (-(m - 1)) * (b - a) := by
            rw [hs]
        _ = K * Cg * M * (b - a) * ((Lattice.jp pr.1.1 ^ (r + 1) * Lattice.jp pr.1.1 ^ (-(m - 1))) *
            (Lattice.jp pr.2.1 ^ (r + 1) * Lattice.jp pr.2.1 ^ (-(m - 1)))) := by rw [hB]; ring
        _ = K * Cg * M * (b - a) * (g pr.1 * g pr.2) := by rw [e1, e2]
    · intro ta tb φa φb l₁ l₂ hφa hφb hta htb hl₁ hl₂
      rw [hτe ta tb φa φb l₁ l₂ hφa hφb hta htb hl₁ hl₂]
      refine setIntegral_congr_fun (measurableSet_Ioc.inter measurableSet_Icc) fun u hu => ?_
      have hu' : u ∈ Set.Icc (0 : ℝ) T := ⟨hu.2.1, hu.1.2.trans hbT⟩
      have hAu : Ai u = NegSobolev.eval
          (NegSobolev.ofSeq m (fun k => NegSobolev.fourierCoeff (zr u) k) : NegSobolev d m)
            (gradProd pr.1 pr.2) := by rw [hAi, Set.indicator_of_mem hu']
      beta_reduce
      rw [hpq u, hAu]
  choose τ hτm hτn hτe using hex
  have hsumN : Summable fun pr => ‖τ pr‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hτn (hgg.mul_left _)
  have hS : HasSum τ (∑' pr, τ pr) := (Summable.of_norm hsumN).hasSum
  have hcl : IsClosed (projTensor (PathSpace d m T) 2 : Set (TensorDual (PathSpace d m T) 2)) := by
    unfold projTensor
    exact Submodule.isClosed_topologicalClosure _
  have hSmem : (∑' pr, τ pr) ∈ projTensor (PathSpace d m T) 2 :=
    hcl.mem_of_tendsto hS
      (Filter.Eventually.of_forall fun s => Submodule.sum_mem _ fun pr _ => hτm pr)
  refine ⟨(2 * R.D.invβ) • ∑' pr, τ pr, Submodule.smul_mem _ _ hSmem, ?_, ?_⟩
  · rw [norm_smul]
    have h1 : ‖∑' pr, τ pr‖ ≤ (K * Cg * M * (b - a)) * G := by
      refine (norm_tsum_le_tsum_norm hsumN).trans ?_
      calc ∑' pr, ‖τ pr‖ ≤ ∑' pr : NonzeroLattice d × NonzeroLattice d,
            (K * Cg * M * (b - a)) * (g pr.1 * g pr.2) :=
            hsumN.tsum_le_tsum hτn (hgg.mul_left _)
        _ = (K * Cg * M * (b - a)) * G := by rw [tsum_mul_left, hG]
    have h2 : ‖2 * R.D.invβ‖ = 2 * |R.D.invβ| := by
      rw [Real.norm_eq_abs, abs_mul, abs_two]
    rw [h2]
    calc 2 * |R.D.invβ| * ‖∑' pr, τ pr‖ ≤ 2 * |R.D.invβ| * ((K * Cg * M * (b - a)) * G) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = 2 * |R.D.invβ| * K * Cg * G * M * (b - a) := by ring
  · intro ta tb φa φb l₁ l₂ hφa hφb hta htb hl₁ hl₂
    have hSm : MeasurableSet (Set.Ioc a b ∩ Set.Icc 0 (min ta tb)) :=
      measurableSet_Ioc.inter measurableSet_Icc
    have hSsub : Set.Ioc a b ∩ Set.Icc 0 (min ta tb) ⊆ Set.Ioc 0 T :=
      fun u hu => ⟨lt_of_le_of_lt ha hu.1.1, hu.1.2.trans hbT⟩
    have hSa : ∀ u ∈ Set.Ioc a b ∩ Set.Icc 0 (min ta tb), u ≤ ta :=
      fun u hu => hu.2.2.trans (min_le_left _ _)
    have hSb : ∀ u ∈ Set.Ioc a b ∩ Set.Icc 0 (min ta tb), u ≤ tb :=
      fun u hu => hu.2.2.trans (min_le_right _ _)
    -- decay of the mode coefficients
    obtain ⟨N, hN⟩ : ∃ N : ℕ, r + d + 2 ≤ N := ⟨⌈r + d + 2⌉₊, Nat.le_ceil _⟩
    obtain ⟨Aa, hAa0, hAa⟩ := HRS.MC.Sec7.S7PIDM.s7_PID_mode_decay_proof Rb m hm T hT φa hφa N
    obtain ⟨Ab, hAb0, hAb⟩ := HRS.MC.Sec7.S7PIDM.s7_PID_mode_decay_proof Rb m hm T hT φb hφb N
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
    obtain ⟨F, hFdef⟩ : ∃ F : NonzeroLattice d × NonzeroLattice d → ℝ → ℝ, ∀ pr u, F pr u =
        NegSobolev.eval (NegSobolev.ofSeq m (fun k => NegSobolev.fourierCoeff (zr u) k))
            (gradProd pr.1 pr.2) *
          NegSobolev.eval (Vprop Rb.D Rb.ρ m ta u (modeVec m pr.1)) φa *
          NegSobolev.eval (Vprop Rb.D Rb.ρ m tb u (modeVec m pr.2)) φb :=
      ⟨fun pr u => NegSobolev.eval (NegSobolev.ofSeq m (fun k => NegSobolev.fourierCoeff (zr u) k))
            (gradProd pr.1 pr.2) *
          NegSobolev.eval (Vprop Rb.D Rb.ρ m ta u (modeVec m pr.1)) φa *
          NegSobolev.eval (Vprop Rb.D Rb.ρ m tb u (modeVec m pr.2)) φb, fun _ _ => rfl⟩
    -- measurability
    have hFm : ∀ pr, AEStronglyMeasurable (F pr)
        (volume.restrict (Set.Ioc a b ∩ Set.Icc 0 (min ta tb))) := by
      intro pr
      obtain ⟨hmemS, -⟩ := hCg pr.1 pr.2
      have e : F pr = fun u => NegSobolev.eval
          (NegSobolev.ofSeq m (fun k => NegSobolev.fourierCoeff (zr u) k)) (gradProd pr.1 pr.2) *
          NegSobolev.eval (Vprop Rb.D Rb.ρ m ta u (modeVec m pr.1)) φa *
          NegSobolev.eval (Vprop Rb.D Rb.ρ m tb u (modeVec m pr.2)) φb := funext (hFdef pr)
      rw [e]
      exact ((S7PIDS_meas_eval hrm hmemS hzr).aestronglyMeasurable.mul
        (S7PIDS_meas_V Rb m hm T hT hφa hta pr.1 hSm hSsub hSa)).mul
        (S7PIDS_meas_V Rb m hm T hT hφb htb pr.2 hSm hSsub hSb)
    -- pointwise bound
    have hFb : ∀ pr, ∀ u ∈ Set.Ioc a b ∩ Set.Icc 0 (min ta tb),
        ‖F pr u‖ ≤ (M * Cg * Aa * Ab) * (h pr.1 * h pr.2) := by
      intro pr u hu
      obtain ⟨hmemS, hnormS⟩ := hCg pr.1 pr.2
      have hu0 : 0 ≤ u := hu.2.1
      have hu' : u ∈ Set.Icc (0 : ℝ) T := ⟨hu0, hu.1.2.trans hbT⟩
      have h1 := S7PIDS_bound_eval hrm hmemS hnormS (hM u hu')
      have h2 := hAa u ta hu0 (hSa u hu) hta.2 pr.1
      have h3 := hAb u tb hu0 (hSb u hu) htb.2 pr.2
      have e1 : Lattice.jp pr.1.1 ^ (r + 1) * Lattice.jp pr.1.1 ^ (-(N : ℝ)) = h pr.1 := by
        rw [← Real.rpow_add (Torus.jp_pos _), hhdef]; congr 1; ring
      have e2 : Lattice.jp pr.2.1 ^ (r + 1) * Lattice.jp pr.2.1 ^ (-(N : ℝ)) = h pr.2 := by
        rw [← Real.rpow_add (Torus.jp_pos _), hhdef]; congr 1; ring
      have hj1 : 0 ≤ Lattice.jp pr.1.1 ^ (-(N : ℝ)) := Real.rpow_nonneg (Torus.jp_pos _).le _
      have hj2 : 0 ≤ Lattice.jp pr.2.1 ^ (-(N : ℝ)) := Real.rpow_nonneg (Torus.jp_pos _).le _
      have hp1 : 0 ≤ Lattice.jp pr.1.1 ^ (r + 1) := Real.rpow_nonneg (Torus.jp_pos _).le _
      have hp2 : 0 ≤ Lattice.jp pr.2.1 ^ (r + 1) := Real.rpow_nonneg (Torus.jp_pos _).le _
      rw [hFdef, norm_mul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs]
      calc _ ≤ (M * (Cg * Lattice.jp pr.1.1 ^ (r + 1) * Lattice.jp pr.2.1 ^ (r + 1))) *
            (Aa * Lattice.jp pr.1.1 ^ (-(N : ℝ))) * (Ab * Lattice.jp pr.2.1 ^ (-(N : ℝ))) :=
            mul_le_mul (mul_le_mul h1 h2 (abs_nonneg _)
              (mul_nonneg hM0 (mul_nonneg (mul_nonneg hCg0 hp1) hp2))) h3 (abs_nonneg _)
              (mul_nonneg (mul_nonneg hM0 (mul_nonneg (mul_nonneg hCg0 hp1) hp2))
                (mul_nonneg hAa0 hj1))
        _ = (M * Cg * Aa * Ab) * ((Lattice.jp pr.1.1 ^ (r + 1) * Lattice.jp pr.1.1 ^ (-(N : ℝ))) *
            (Lattice.jp pr.2.1 ^ (r + 1) * Lattice.jp pr.2.1 ^ (-(N : ℝ)))) := by ring
        _ = (M * Cg * Aa * Ab) * (h pr.1 * h pr.2) := by rw [e1, e2]
    -- integrability and summability of the integrals
    haveI : IsFiniteMeasure (volume.restrict (Set.Ioc a b ∩ Set.Icc 0 (min ta tb))) := by
      refine ⟨?_⟩
      rw [Measure.restrict_apply_univ]
      refine lt_of_le_of_lt (measure_mono Set.inter_subset_left) ?_
      rw [Real.volume_Ioc]
      exact ENNReal.ofReal_lt_top
    have hFae : ∀ pr, ∀ᵐ u ∂(volume.restrict (Set.Ioc a b ∩ Set.Icc 0 (min ta tb))),
        ‖F pr u‖ ≤ (M * Cg * Aa * Ab) * (h pr.1 * h pr.2) := fun pr =>
      (ae_restrict_iff' hSm).2 (Filter.Eventually.of_forall fun u hu => hFb pr u hu)
    have hFint : ∀ pr, Integrable (F pr) (volume.restrict (Set.Ioc a b ∩ Set.Icc 0 (min ta tb))) :=
      fun pr => Integrable.mono' (integrable_const _) (hFm pr) (hFae pr)
    have hFsum : Summable fun pr => ∫ u, ‖F pr u‖ ∂(volume.restrict (Set.Ioc a b ∩ Set.Icc 0 (min ta tb))) := by
      refine Summable.of_nonneg_of_le (fun pr => integral_nonneg fun u => norm_nonneg _) (fun pr => ?_)
        ((hhh.mul_left (M * Cg * Aa * Ab)).mul_right
          ((volume.restrict (Set.Ioc a b ∩ Set.Icc 0 (min ta tb))).real Set.univ))
      refine (le_abs_self _).trans ?_
      rw [← Real.norm_eq_abs]
      exact norm_integral_le_of_norm_le_const (by
        filter_upwards [hFae pr] with u hu
        rw [norm_norm]
        exact hu)
    have key := hasSum_integral_of_summable_integral_norm hFint hFsum
    -- the evaluation of `τ_{kl}`
    have hτF : ∀ pr, τ pr (prodForm l₁ l₂) =
        ∫ u in Set.Ioc a b ∩ Set.Icc 0 (min ta tb), F pr u := by
      intro pr
      rw [hτe pr ta tb φa φb l₁ l₂ hφa hφb hta htb hl₁ hl₂]
      simp only [hFdef]
    have H2 : HasSum (fun pr => τ pr (prodForm l₁ l₂)) ((∑' pr, τ pr) (prodForm l₁ l₂)) :=
      hS.mapL (ContinuousLinearMap.apply ℝ ℝ (prodForm l₁ l₂))
    have H3 : HasSum (fun pr => τ pr (prodForm l₁ l₂))
        (∫ u in Set.Ioc a b ∩ Set.Icc 0 (min ta tb), ∑' pr, F pr u) := by
      have : (fun pr => τ pr (prodForm l₁ l₂)) =
          fun pr => ∫ u in Set.Ioc a b ∩ Set.Icc 0 (min ta tb), F pr u := funext hτF
      rw [this]
      exact key
    have hEq := H2.unique H3
    rw [ContinuousLinearMap.smul_apply, smul_eq_mul, hEq]
    congr 1
    refine setIntegral_congr_fun hSm fun u _ => ?_
    simp only [hFdef]

end HRS.MC.E213M

end
