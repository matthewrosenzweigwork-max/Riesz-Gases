import HRS.MC.CepK0Aux1
import HRS.MC.CepK0Aux2
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Packet CEPK0: relocated proofs of the Cépa–Lépingle kernel/uniqueness externals

Relocation of `cep_K3_gronwall_ac` (`HRS/MC/CepaSpec.lean`) to `cep_K3_gronwall_ac_proof` in this
namespace.  The spec file is not imported here; the ties live in `HRS/MC/CepK0Tie.lean`.
-/

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.CepK0

/-- Complete case of K3.  `G(t) = ∫_0^t ‖F‖` is absolutely continuous and dominates `‖Z‖`; `u = ‖Z‖²` is
absolutely continuous with `u' = 2⟨Z,F⟩` a.e.; then `H = e^{-2Λt} u` is absolutely continuous with `H' ≤ 0`
a.e. and `H(0) = 0`, so `H ≤ 0`, hence `Z = 0`. -/
theorem cep_K3_gronwall_complete {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] {Z F : ℝ → E}
    {T Λ : ℝ} (hT : 0 ≤ T) (hF : IntervalIntegrable F volume 0 T)
    (hZ : ∀ t ∈ Set.Icc 0 T, Z t = Z 0 + ∫ s in (0 : ℝ)..t, F s) (h0 : Z 0 = 0)
    (hdiss : ∀ᵐ s ∂(volume.restrict (Set.Icc 0 T)), inner ℝ (Z s) (F s) ≤ Λ * ‖Z s‖ ^ 2) :
    ∀ t ∈ Set.Icc 0 T, Z t = 0 := by
  have hmem : ∀ x ∈ Icc (0:ℝ) T, x ∈ uIcc (0:ℝ) T := fun x hx => by rw [uIcc_of_le hT]; exact hx
  have hFn : IntervalIntegrable (fun s => ‖F s‖) volume 0 T := hF.norm
  have hGac : AbsolutelyContinuousOnInterval (fun t => ∫ s in (0:ℝ)..t, ‖F s‖) 0 T :=
    hFn.absolutelyContinuousOnInterval_intervalIntegral (c := 0) left_mem_uIcc
  obtain ⟨G, hG⟩ : ∃ G : ℝ → ℝ, ∀ t, G t = ∫ s in (0:ℝ)..t, ‖F s‖ :=
    ⟨fun t => ∫ s in (0:ℝ)..t, ‖F s‖, fun t => rfl⟩
  have hGac' : AbsolutelyContinuousOnInterval G 0 T := by
    have hfun : G = fun t => ∫ s in (0:ℝ)..t, ‖F s‖ := funext hG
    rw [hfun]; exact hGac
  have hG0 : G 0 = 0 := by rw [hG]; simp
  have hFi : ∀ x ∈ Icc (0:ℝ) T, ∀ y ∈ Icc (0:ℝ) T, IntervalIntegrable F volume x y := by
    intro x hx y hy
    exact hF.mono_set (uIcc_subset_uIcc (hmem x hx) (hmem y hy))
  have hGi : ∀ y ∈ Icc (0:ℝ) T, IntervalIntegrable (fun s => ‖F s‖) volume 0 y := fun y hy =>
    hFn.mono_set (uIcc_subset_uIcc left_mem_uIcc (hmem y hy))
  have hGdiff : ∀ x ∈ Icc (0:ℝ) T, ∀ y ∈ Icc (0:ℝ) T, G y - G x = ∫ s in x..y, ‖F s‖ := by
    intro x hx y hy
    rw [hG y, hG x]
    exact intervalIntegral.integral_interval_sub_left (hGi y hy) (hGi x hx)
  have hGnn : ∀ t ∈ Icc (0:ℝ) T, 0 ≤ G t := by
    intro t ht
    rw [hG]
    exact intervalIntegral.integral_nonneg ht.1 (fun s _ => norm_nonneg _)
  have hGT : 0 ≤ G T := hGnn T ⟨hT, le_rfl⟩
  have hGmono : ∀ t ∈ Icc (0:ℝ) T, G t ≤ G T := by
    intro t ht
    have h1 := hGdiff t ht T ⟨hT, le_rfl⟩
    have h2 : 0 ≤ ∫ s in t..T, ‖F s‖ :=
      intervalIntegral.integral_nonneg ht.2 (fun s _ => norm_nonneg _)
    linarith
  have hZeq : ∀ t ∈ Icc (0:ℝ) T, Z t = ∫ s in (0:ℝ)..t, F s := fun t ht => by
    rw [hZ t ht, h0, zero_add]
  have hZd : ∀ x ∈ Icc (0:ℝ) T, ∀ y ∈ Icc (0:ℝ) T, ‖Z y - Z x‖ ≤ |G y - G x| := by
    intro x hx y hy
    rw [hZeq y hy, hZeq x hx, hGdiff x hx y hy,
      intervalIntegral.integral_interval_sub_left (hFi 0 ⟨le_rfl, hT⟩ y hy) (hFi 0 ⟨le_rfl, hT⟩ x hx)]
    exact intervalIntegral.norm_integral_le_abs_integral_norm
  have hZn : ∀ t ∈ Icc (0:ℝ) T, ‖Z t‖ ≤ G T := by
    intro t ht
    have h1 := hZd 0 ⟨le_rfl, hT⟩ t ht
    simp only [h0, hG0, sub_zero] at h1
    rw [abs_of_nonneg (hGnn t ht)] at h1
    exact h1.trans (hGmono t ht)
  -- `u = ‖Z‖²` is absolutely continuous
  have hu : AbsolutelyContinuousOnInterval (fun t => ‖Z t‖ ^ 2) 0 T := by
    apply cep_K3_ac_of_dist_le (C := 2 * G T) hGac'
    intro x hx y hy
    have hx' : x ∈ Icc (0:ℝ) T := by rwa [uIcc_of_le hT] at hx
    have hy' : y ∈ Icc (0:ℝ) T := by rwa [uIcc_of_le hT] at hy
    rw [Real.dist_eq, Real.dist_eq]
    have h1 : |‖Z x‖ - ‖Z y‖| ≤ ‖Z x - Z y‖ := abs_norm_sub_norm_le _ _
    have h2 : ‖Z x - Z y‖ = ‖Z y - Z x‖ := norm_sub_rev _ _
    have h3 : ‖Z y - Z x‖ ≤ |G y - G x| := hZd x hx' y hy'
    have h4 : |G y - G x| = |G x - G y| := abs_sub_comm _ _
    have hxb := hZn x hx'
    have hyb := hZn y hy'
    have hnx : 0 ≤ ‖Z x‖ := norm_nonneg _
    have hny : 0 ≤ ‖Z y‖ := norm_nonneg _
    have hsum : ‖Z x‖ + ‖Z y‖ ≤ 2 * G T := by linarith
    calc |‖Z x‖ ^ 2 - ‖Z y‖ ^ 2|
        = |‖Z x‖ - ‖Z y‖| * (‖Z x‖ + ‖Z y‖) := by
          rw [show ‖Z x‖ ^ 2 - ‖Z y‖ ^ 2 = (‖Z x‖ - ‖Z y‖) * (‖Z x‖ + ‖Z y‖) by ring, abs_mul,
            abs_of_nonneg (add_nonneg hnx hny)]
      _ ≤ ‖Z x - Z y‖ * (2 * G T) := mul_le_mul h1 hsum (add_nonneg hnx hny) (norm_nonneg _)
      _ ≤ |G x - G y| * (2 * G T) :=
          mul_le_mul_of_nonneg_right (by linarith) (by linarith)
      _ = 2 * G T * |G x - G y| := by ring
  -- the exponential weight is smooth
  have hexp : AbsolutelyContinuousOnInterval (fun t : ℝ => Real.exp (-(2 * Λ) * t)) 0 T := by
    have hcd : ContDiff ℝ 1 (fun t : ℝ => Real.exp (-(2 * Λ) * t)) := by fun_prop
    exact (hcd.contDiffOn (s := uIcc (0:ℝ) T)).absolutelyContinuousOnInterval
  have hH : AbsolutelyContinuousOnInterval (fun t => Real.exp (-(2 * Λ) * t) * ‖Z t‖ ^ 2) 0 T :=
    hexp.mul hu
  -- a.e. derivatives
  have hae1 : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Ioo (0:ℝ) T → HasDerivAt Z (F t) t := by
    filter_upwards [hF.ae_hasDerivAt_integral] with t ht htI
    have hd := ht (hmem t (Ioo_subset_Icc_self htI)) 0 left_mem_uIcc
    apply hd.congr_of_eventuallyEq
    filter_upwards [Ioo_mem_nhds htI.1 htI.2] with s hs
    exact hZeq s (Ioo_subset_Icc_self hs)
  have hae2 : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Ioo (0:ℝ) T →
      HasDerivAt (fun s => ‖Z s‖ ^ 2) (2 * inner ℝ (Z t) (F t)) t := by
    filter_upwards [hae1] with t ht htI
    have h := (ht htI).inner ℝ (ht htI)
    simp only [real_inner_self_eq_norm_sq] at h
    convert h using 1
    rw [real_inner_comm (Z t) (F t)]
    ring
  have hae3 : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Ioo (0:ℝ) T →
      HasDerivAt (fun s => Real.exp (-(2 * Λ) * s) * ‖Z s‖ ^ 2)
        (Real.exp (-(2 * Λ) * t) * (-(2 * Λ) * 1) * ‖Z t‖ ^ 2 +
          Real.exp (-(2 * Λ) * t) * (2 * inner ℝ (Z t) (F t))) t := by
    filter_upwards [hae2] with t ht htI
    have he : HasDerivAt (fun s => Real.exp (-(2 * Λ) * s)) (Real.exp (-(2 * Λ) * t) * (-(2 * Λ) * 1)) t :=
      ((hasDerivAt_id' t).const_mul (-(2 * Λ))).exp
    exact he.mul (ht htI)
  have hdissA : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Icc (0:ℝ) T → inner ℝ (Z t) (F t) ≤ Λ * ‖Z t‖ ^ 2 :=
    (ae_restrict_iff' measurableSet_Icc).mp hdiss
  have hsign : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Ioo (0:ℝ) T →
      deriv (fun s => Real.exp (-(2 * Λ) * s) * ‖Z s‖ ^ 2) t ≤ 0 := by
    filter_upwards [hae3, hdissA] with t h3 hd htI
    rw [(h3 htI).deriv]
    have hE := Real.exp_pos (-(2 * Λ) * t)
    have hd' := hd (Ioo_subset_Icc_self htI)
    nlinarith [mul_le_mul_of_nonneg_left hd' hE.le]
  -- conclusion
  intro t ht
  rcases eq_or_lt_of_le ht.1 with h | h
  · rw [← h]; exact h0
  · have hHt : AbsolutelyContinuousOnInterval (fun s => Real.exp (-(2 * Λ) * s) * ‖Z s‖ ^ 2) 0 t :=
      hH.mono (by rw [uIcc_of_le hT, uIcc_of_le ht.1]; exact Icc_subset_Icc le_rfl ht.2)
    have hint := hHt.integral_deriv_eq_sub
    have hnonpos : ∫ x in (0:ℝ)..t,
        deriv (fun s => Real.exp (-(2 * Λ) * s) * ‖Z s‖ ^ 2) x ≤ 0 := by
      rw [intervalIntegral.integral_of_le ht.1, integral_Ioc_eq_integral_Ioo]
      apply setIntegral_nonpos_of_ae_restrict
      filter_upwards [ae_restrict_of_ae hsign, ae_restrict_mem measurableSet_Ioo] with x hx hmem'
      exact hx (Ioo_subset_Ioo_right ht.2 hmem')
    have hH0 : Real.exp (-(2 * Λ) * 0) * ‖Z 0‖ ^ 2 = 0 := by rw [h0]; simp
    have hHle : Real.exp (-(2 * Λ) * t) * ‖Z t‖ ^ 2 ≤ 0 := by
      rw [hH0] at hint
      linarith
    have hE := Real.exp_pos (-(2 * Λ) * t)
    have hsq : ‖Z t‖ ^ 2 ≤ 0 := by
      by_contra hc
      push_neg at hc
      have := mul_pos hE hc
      linarith
    have hn : ‖Z t‖ = 0 := by nlinarith [norm_nonneg (Z t)]
    exact norm_eq_zero.mp hn

/-- **K3 (Gronwall for absolutely continuous differences)**.  If `E` is not complete, the Bochner integral
is `0` (Mathlib convention), so `hZ` gives `Z t = Z 0 = 0`; otherwise `cep_K3_gronwall_complete`. -/
theorem cep_K3_gronwall_ac_proof {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {Z F : ℝ → E}
    {T Λ : ℝ} (hT : 0 ≤ T) (hF : IntervalIntegrable F volume 0 T)
    (hZ : ∀ t ∈ Set.Icc 0 T, Z t = Z 0 + ∫ s in (0 : ℝ)..t, F s) (h0 : Z 0 = 0)
    (hdiss : ∀ᵐ s ∂(volume.restrict (Set.Icc 0 T)), inner ℝ (Z s) (F s) ≤ Λ * ‖Z s‖ ^ 2) :
    ∀ t ∈ Set.Icc 0 T, Z t = 0 := by
  by_cases hC : CompleteSpace E
  · haveI := hC
    exact cep_K3_gronwall_complete hT hF hZ h0 hdiss
  · intro t ht
    rw [hZ t ht, h0, zero_add]
    simp [intervalIntegral, integral_of_not_completeSpace hC]

open HRS

/-- **U1 (continuous lifts differ by a constant lattice vector)**.  Two continuous lifts of the same torus path on
`[0,T]` differ by a time-independent element of `ℤ^{N d}` (a continuous map into a discrete set is constant). -/
theorem cep_U1_lift_const_proof {d N : ℕ} {T : ℝ} (hT : 0 ≤ T) {Y Y' : ℝ≥0 → Fin N → Euc d}
    (hY : Continuous Y) (hY' : Continuous Y')
    (h : ∀ t : ℝ≥0, (t : ℝ) ≤ T → (fun i => Torus.mk (Y t i)) = fun i => Torus.mk (Y' t i)) :
    ∃ v : Fin N → Euc d, IsLatticeVec v ∧ ∀ t : ℝ≥0, (t : ℝ) ≤ T → Y' t = Y t + v := by
  have hint : ∀ t : ℝ≥0, (t : ℝ) ≤ T → ∀ i j, ∃ n : ℤ, (Y' t i - Y t i) j = n := by
    intro t ht i j
    exact cep_U1_torus_int (congrFun (h t ht) i) j
  have hcont : ∀ i j, Continuous (fun t : ℝ≥0 => (Y' t i - Y t i) j) := by
    intro i j
    have h1 : Continuous (fun t : ℝ≥0 => Y' t i - Y t i) :=
      ((continuous_apply i).comp hY').sub ((continuous_apply i).comp hY)
    have h2 : Continuous (fun x : Euc d => x j) := by fun_prop
    exact h2.comp h1
  have hconst : ∀ i j, ∀ t : ℝ≥0, (t : ℝ) ≤ T → (Y' t i - Y t i) j = (Y' 0 i - Y 0 i) j := by
    intro i j t ht
    set g : ℝ → ℝ := fun s => (Y' s.toNNReal i - Y s.toNNReal i) j with hg
    have hgc : Continuous g := (hcont i j).comp continuous_real_toNNReal
    have hgint : ∀ s ∈ Icc (0:ℝ) T, ∃ n : ℤ, g s = n := by
      intro s hs
      have hs' : ((s.toNNReal : ℝ≥0) : ℝ) ≤ T := by
        rw [Real.coe_toNNReal s hs.1]; exact hs.2
      exact hint _ hs' i j
    have key := cep_U1_const_of_int hT hgc.continuousOn hgint (t : ℝ) ⟨t.coe_nonneg, ht⟩
    have e1 : g (t : ℝ) = (Y' t i - Y t i) j := by simp [hg]
    have e2 : g 0 = (Y' 0 i - Y 0 i) j := by simp [hg]
    rw [← e1, ← e2]
    exact key
  have hT0 : ((0 : ℝ≥0) : ℝ) ≤ T := by simpa using hT
  refine ⟨fun i => Y' 0 i - Y 0 i, cep_U1_isLattice_of_int (fun i j => hint 0 hT0 i j), ?_⟩
  intro t ht
  funext i
  ext j
  have := hconst i j t ht
  simp only [Pi.add_apply, PiLp.sub_apply, PiLp.add_apply] at this ⊢
  linarith

/-- **U1b (chambers are identified by one interior point)**.  If `y` is strictly ordered by `π` and `y + v`
strictly ordered by `π'` (`v` a lattice vector), then the closed chamber `{z | CyclicallyOrdered π z}` equals the lattice
translate of the closed chamber of `π'`: `CyclicallyOrdered π' (z + v) → CyclicallyOrdered π z`.  This removes the
ambiguity of the anchor (rotation `π ↦ π ∘ rot`) in `IsCepaLepingleFlow.ordered`. -/
theorem cep_U1b_chamber_unique_proof {N : ℕ} {π π' : Equiv.Perm (Fin N)} {y v : Fin N → Euc 1}
    (hv : IsLatticeVec v) (hy : cep_StrictlyOrdered π y) (hy' : cep_StrictlyOrdered π' (y + v)) :
    ∀ z : Fin N → Euc 1, CyclicallyOrdered π' (z + v) → CyclicallyOrdered π z := by
  intro z hz
  obtain ⟨hy1, hy2⟩ := hy
  obtain ⟨hw1, hw2⟩ := hy'
  obtain ⟨hz1, hz2⟩ := hz 0
  have hadd : ∀ w : Fin N → Euc 1, ∀ a, (w + v) a 0 = w a 0 + v a 0 := fun w a => by simp
  simp only [hadd] at hw1 hw2 hz1 hz2
  have hint : ∀ a b : Fin N, ∃ m : ℤ, v b 0 - v a 0 = m := by
    intro a b
    obtain ⟨n, hn⟩ := hv a
    obtain ⟨n', hn'⟩ := hv b
    refine ⟨n' 0 - n 0, ?_⟩
    rw [hn, hn']
    simp [Lattice.toEuc]
  have key : ∀ a b : Fin N, y a 0 < y b 0 → y b 0 < y a 0 + 1 →
      0 ≤ z b 0 - z a 0 ∧ z b 0 - z a 0 ≤ 1 := by
    intro a b hab hba
    obtain ⟨p, rfl⟩ := π'.surjective a
    obtain ⟨q, rfl⟩ := π'.surjective b
    have hpq : p ≠ q := by
      rintro rfl
      exact lt_irrefl _ hab
    rcases lt_or_gt_of_ne hpq with hlt | hlt
    · exact cep_U1b_pair_real (y (π' p) 0) (y (π' q) 0) (z (π' p) 0) (z (π' q) 0)
        (v (π' p) 0) (v (π' q) 0) (by linarith) (by linarith) (hint _ _)
        (by linarith [hw2 p q]) (by linarith [hw2 q p]) (by linarith [hz2 p q]) (by linarith [hz2 q p])
        (Or.inl ⟨by linarith [hw1 p q hlt], by linarith [hz1 p q hlt.le]⟩)
    · exact cep_U1b_pair_real (y (π' p) 0) (y (π' q) 0) (z (π' p) 0) (z (π' q) 0)
        (v (π' p) 0) (v (π' q) 0) (by linarith) (by linarith) (hint _ _)
        (by linarith [hw2 p q]) (by linarith [hw2 q p]) (by linarith [hz2 p q]) (by linarith [hz2 q p])
        (Or.inr ⟨by linarith [hw1 q p hlt], by linarith [hz1 q p hlt.le]⟩)
  unfold CyclicallyOrdered
  intro j
  obtain rfl : j = 0 := Subsingleton.elim _ _
  refine ⟨fun k k' hkk' => ?_, fun k k' => ?_⟩
  · rcases eq_or_lt_of_le hkk' with h | h
    · subst h; exact le_rfl
    · have := (key (π k) (π k') (hy1 k k' h) (hy2 k k')).1
      linarith
  · rcases lt_trichotomy k k' with h | h | h
    · have := (key (π k) (π k') (hy1 k k' h) (hy2 k k')).2
      linarith
    · subst h; linarith
    · have := (key (π k') (π k) (hy1 k' k h) (hy2 k' k)).1
      linarith

end HRS.MC.CepK0
