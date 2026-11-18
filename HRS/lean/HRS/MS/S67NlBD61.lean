import HRS.MS.MovAdjAux26
import HRS.MS.GradSmTie
import HRS.MS.Mov63Tie
import HRS.MS.MovOpAux5
import HRS.MS.MovLinTie
import HRS.MS.S67NlBD55
import HRS.MS.S67NlBD56
import HRS.MS.S67NlBD57
import HRS.MS.S67NlBD57A
import HRS.MS.S67NlBD57B
import HRS.MS.S67NlBD57C
import HRS.MS.S67NlBD59
import HRS.MS.S67NlBD60
import HRS.MS.S67NlBD66A

/-!
# S6.7 nonlinear breakdown, packet 61: finiteness of the new gradient jet

Namespace `HRS.MS.BreakdownS67`, helper prefix `s67bd_`. TeX S:4844-4851 (finiteness
prerequisite), nonlinear part of `S:W:lem:r2mov-global-adjoint`. No owned definitions.
Route: for fixed nonzero steps and unit directions the mixed difference `u_h` of `u` carries
`s67bd_ParabolicData` with source `commutator` (56), bounded uniformly by 57 and the lower jets; the
initial gradient of `u_h` is bounded by 57B and the finiteness of `cbNormVecE n (∇u 0)`; the common
short slab (59) is applied to the time translates of `u_h` on `N` slabs (`s67bd61_translate`),
giving the recurrence `D (k+1) = Cs * (D k + MJ')` uniformly in the step data; the lower orders
come from 57B/57C and the jet passage from 60.
-/

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff RealInnerProductSpace

namespace HRS.MS.BreakdownS67

open HRS HRS.Whole HRS.MS.MovLin HRS.MS.MovOsc HRS.MS.MovAdj
open HRS.MS.Mov63 HRS.MS.MovForce HRS.MS.MovC2
open HRS.MS.PoisFlow HRS.MS.PoisSg HRS.MS.PoisKolm HRS.MS.PoisHigh

variable {d : ℕ} {s β q : ℝ} {ρ₀ : Euc d → ℝ}

/-- time translation preserves `s67bd_ParabolicData` -/
lemma s67bd61_translate {ν q T : ℝ} {u a : ℝ → Euc d → ℝ} {B : ℝ → Euc d → Euc d}
    {J : ℝ → Euc d → ℝ} (hP : s67bd_ParabolicData ν q T u a B J) {t0 T' : ℝ} (ht0 : 0 ≤ t0)
    (hT' : T' + t0 ≤ T) :
    s67bd_ParabolicData ν q T' (fun t => u (t0 + t)) (fun t => a (t0 + t)) (fun t => B (t0 + t))
      (fun t => J (t0 + t)) := by
  have hmem : ∀ t ∈ Icc (0 : ℝ) T', t0 + t ∈ Icc (0 : ℝ) T := fun t ht =>
    ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hmaps : MapsTo (fun p : ℝ × Euc d => (t0 + p.1, p.2)) (Icc (0 : ℝ) T' ×ˢ (univ : Set (Euc d)))
      (Icc (0 : ℝ) T ×ˢ (univ : Set (Euc d))) := fun p hp => ⟨hmem p.1 hp.1, trivial⟩
  have hcont : ContinuousOn (fun p : ℝ × Euc d => (t0 + p.1, p.2))
      (Icc (0 : ℝ) T' ×ˢ (univ : Set (Euc d))) := by fun_prop
  refine ⟨fun t ht => hP.c2 _ (hmem t ht), ?_, fun k hk => ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨K, hK⟩ := hP.bdd_c2
    exact ⟨K, fun t ht k hk x => hK _ (hmem t ht) k hk x⟩
  · exact (hP.cont_c2 k hk).comp hcont hmaps
  · exact hP.acont.comp hcont hmaps
  · obtain ⟨K, hK⟩ := hP.agrow
    exact ⟨K, fun t ht x => hK _ (hmem t ht) x⟩
  · exact hP.Bcont.comp hcont hmaps
  · exact hP.Jcont.comp hcont hmaps
  · intro t ht t1 ht1 x
    have := hP.hint _ (hmem t ht) _ (hmem t1 ht1) x
    rw [this, intervalIntegral.integral_comp_add_left (fun v => a v x) t0]
  · intro t ht x
    exact hP.equation _ (hmem t ht) x

/-- the lower-order mixed differences of the gradient are bounded by the lower-jet amplitude -/
lemma s67bd61_lower (n' : ℕ) (h : Fin n' → ℝ) (e : Fin n' → Euc d) (hh : ∀ i, h i ≠ 0)
    (he : ∀ i, ‖e i‖ = 1) (w : Euc d → ℝ) (hw : ContDiff ℝ ((n' + 1 : ℕ) : WithTop ℕ∞) w)
    {A : ℝ} (hA : 0 ≤ A) (hjet : ∀ x, ‖iteratedFDeriv ℝ n' (fun y => gradient w y) x‖ ≤ A)
    (x : Euc d) : ‖gradient (s67bd_mixedDiff n' h e w) x‖ ≤ A := by
  rw [(s67bd_mixed_gradient d n' h e hh w hw).1 x]
  have hG : ContDiff ℝ (n' : WithTop ℕ∞) (fun y => gradient w y) := s67_grad_contDiff hw
  have hc : (Finset.univ : Finset (Fin n')).card = n' := by simp
  have := s67bd_subset_mean_value d n' h e hh he Finset.univ (fun y => gradient w y)
    (by rw [hc]; exact hG) A hA (fun y => by rw [hc]; exact hjet y) x
  rwa [s67bd57_sd_univ] at this

theorem s67bd_one_jet_finite (d n : ℕ) (hn : 1 ≤ n) (ν q T Mb MJ A : ℝ)
    (hν : 0 < ν) (hq : 0 < q) (hT : 0 ≤ T)
    (hMb : 0 ≤ Mb) (hMJ : 0 ≤ MJ) (hA : 0 ≤ A)
    (u a : ℝ → Euc d → ℝ) (B : ℝ → Euc d → Euc d) (J : ℝ → Euc d → ℝ)
    (hu : s67bd_ParabolicData ν q T u a B J)
    (hB : ∀ t ∈ Icc (0 : ℝ) T, ContDiff ℝ ((n + 1 : ℕ) : WithTop ℕ∞) (B t) ∧
      ∀ i ≤ n + 1, ∀ x, ‖iteratedFDeriv ℝ i (B t) x‖ ≤ Mb)
    (hJ : ∀ t ∈ Icc (0 : ℝ) T, ContDiff ℝ (n : WithTop ℕ∞) (J t) ∧
      ∀ i ≤ n, ∀ x, ‖iteratedFDeriv ℝ i (J t) x‖ ≤ MJ)
    (hreg : ∀ t ∈ Icc (0 : ℝ) T, ContDiff ℝ ((n + 1 : ℕ) : WithTop ℕ∞) (u t))
    (hlower : ∀ t ∈ Icc (0 : ℝ) T, ∀ i < n, ∀ x,
      ‖iteratedFDeriv ℝ i (fun y => gradient (u t) y) x‖ ≤ A)
    (hinit : cbNormVecE n (fun x => gradient (u 0) x) < ⊤) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Icc (0 : ℝ) T, ∀ x,
      ‖iteratedFDeriv ℝ n (fun y => gradient (u t) y) x‖ ≤ C := by
  have h0T : (0 : ℝ) ∈ Icc (0 : ℝ) T := ⟨le_rfl, hT⟩
  obtain ⟨Cc, hCc, hcomm⟩ := s67bd_commutator_bound d n hn q Mb hMb
  obtain ⟨τ, Cs, hτ, hCs1, hslab⟩ := s67bd_short_slab d ν q Mb hν hq hMb
  -- initial amplitude
  set E : ℝ := (cbNormVecE n (fun x => gradient (u 0) x)).toReal with hE
  have hE0 : 0 ≤ E := ENNReal.toReal_nonneg
  have hjetE : ∀ k ≤ n, ∀ x, ‖iteratedFDeriv ℝ k (fun y => gradient (u 0) y) x‖ ≤ E :=
    s67bd66_jet_le hE0 (by rw [hE, ENNReal.ofReal_toReal hinit.ne])
  set MJ' : ℝ := Cc * (A + MJ) with hMJ'
  have hMJ'0 : 0 ≤ MJ' := mul_nonneg hCc (add_nonneg hA hMJ)
  -- slab count
  obtain ⟨N, hN1, hNT⟩ : ∃ N : ℕ, 1 ≤ N ∧ T ≤ N * τ :=
    ⟨⌈T / τ⌉₊ + 1, by omega, by
      have h1 : T / τ ≤ (⌈T / τ⌉₊ : ℝ) := Nat.le_ceil _
      have h2 : T ≤ (⌈T / τ⌉₊ : ℝ) * τ := by rwa [div_le_iff₀ hτ] at h1
      push_cast
      nlinarith⟩
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
  set τ' : ℝ := T / N with hτ'
  have hτ'0 : 0 ≤ τ' := div_nonneg hT hNpos.le
  have hτ'τ : τ' ≤ τ := by rw [hτ', div_le_iff₀ hNpos]; linarith
  have hNτ' : (N : ℝ) * τ' = T := by rw [hτ']; field_simp
  -- the recurrence
  let D : ℕ → ℝ := fun k => Nat.rec E (fun _ Dk => Cs * (Dk + MJ')) k
  have hD0 : D 0 = E := rfl
  have hDs : ∀ k, D (k + 1) = Cs * (D k + MJ') := fun k => rfl
  have hDnn : ∀ k, 0 ≤ D k := by
    intro k
    induction k with
    | zero => exact hE0
    | succ k ih => rw [hDs]; exact mul_nonneg (by linarith) (by linarith)
  have hDmono : ∀ k, D k ≤ D (k + 1) := by
    intro k
    rw [hDs]
    nlinarith [hDnn k]
  -- uniform bound for the `n`-fold mixed differences
  have main : ∀ k : ℕ, ∀ (h : Fin n → ℝ) (e : Fin n → Euc d), (∀ i, h i ≠ 0) → (∀ i, ‖e i‖ = 1) →
      ∀ t ∈ Icc (0 : ℝ) T, t ≤ k * τ' → ∀ x,
        ‖gradient (s67bd_mixedDiff n h e (u t)) x‖ ≤ D k := by
    intro k
    induction k with
    | zero =>
      intro h e hh he t ht htk x
      have ht0 : t = 0 := le_antisymm (by simpa using htk) ht.1
      subst ht0
      rw [(s67bd_mixed_gradient d n h e hh (u 0) (hreg 0 h0T)).1 x]
      have hG : ContDiff ℝ (n : WithTop ℕ∞) (fun y => gradient (u 0) y) :=
        s67_grad_contDiff (hreg 0 h0T)
      have hc : (Finset.univ : Finset (Fin n)).card = n := by simp
      have := s67bd_subset_mean_value d n h e hh he Finset.univ (fun y => gradient (u 0) y)
        (by rw [hc]; exact hG) E hE0 (fun y => by rw [hc]; exact hjetE n le_rfl y) x
      rw [s67bd57_sd_univ] at this
      exact this
    | succ k ih =>
      intro h e hh he t ht htk x
      by_cases hcase : t ≤ k * τ'
      · exact (ih h e hh he t ht hcase x).trans (hDmono k)
      · push Not at hcase
        have hkτ : (k : ℝ) * τ' ≤ T := by
          have : (k : ℝ) * τ' ≤ t := hcase.le
          linarith [ht.2]
        have hk1 : (k : ℝ) + 1 ≤ N := by
          have : (k : ℝ) * τ' < N * τ' := by
            have : (k : ℝ) * τ' < t := hcase
            linarith [ht.2]
          have hlt : (k : ℝ) < N := lt_of_mul_lt_mul_right this hτ'0
          have : k < N := by exact_mod_cast hlt
          exact_mod_cast this
        set t0 : ℝ := k * τ' with ht0def
        have ht00 : 0 ≤ t0 := mul_nonneg (Nat.cast_nonneg k) hτ'0
        have hend : τ' + t0 ≤ T := by
          have : ((k : ℝ) + 1) * τ' ≤ N * τ' := mul_le_mul_of_nonneg_right hk1 hτ'0
          rw [ht0def]; nlinarith
        -- parabolic data of the mixed difference, translated
        obtain ⟨hPD, -⟩ := s67bd_mixed_difference_pde ν q T u a B J hu n h e hh he
        have hPDt := s67bd61_translate hPD ht00 hend
        have hBb : ∀ t' ∈ Icc (0 : ℝ) τ', ∀ y, ‖B (t0 + t') y‖ ≤ Mb := by
          intro t' ht' y
          have hm : t0 + t' ∈ Icc (0 : ℝ) T := ⟨by linarith [ht'.1], by linarith [ht'.2]⟩
          have := (hB _ hm).2 0 (Nat.zero_le _) y
          rwa [norm_iteratedFDeriv_zero] at this
        have hJb : ∀ t' ∈ Icc (0 : ℝ) τ', ∀ y,
            |s67bd_commutator q n h e (B (t0 + t')) (J (t0 + t')) (u (t0 + t')) y| ≤ MJ' := by
          intro t' ht' y
          have hm : t0 + t' ∈ Icc (0 : ℝ) T := ⟨by linarith [ht'.1], by linarith [ht'.2]⟩
          have hBm := hB _ hm
          have hJm := hJ _ hm
          exact hcomm A MJ hA hMJ (B (t0 + t')) (J (t0 + t')) (u (t0 + t'))
            (hBm.1.of_le (by exact_mod_cast Nat.le_succ n))
            (fun i hi y' => hBm.2 i (by omega) y') hJm.1 hJm.2 (hreg _ hm)
            (hlower _ hm) h e hh he y
        have hinit' : ∀ y, ‖gradient (s67bd_mixedDiff n h e (u (t0 + 0))) y‖ ≤ D k := by
          rw [add_zero]
          exact ih h e hh he t0 ⟨ht00, hkτ⟩ le_rfl
        have hsl := hslab τ' (D k) MJ' hτ'0 hτ'τ (hDnn k) hMJ'0
          (fun t' => s67bd_mixedDiff n h e (u (t0 + t')))
          (fun t' => s67bd_mixedDiff n h e (a (t0 + t'))) (fun t' => B (t0 + t'))
          (fun t' => s67bd_commutator q n h e (B (t0 + t')) (J (t0 + t')) (u (t0 + t')))
          hPDt hBb hJb hinit'
        have ht' : t - t0 ∈ Icc (0 : ℝ) τ' := ⟨by linarith, by
          have : t ≤ ((k : ℝ) + 1) * τ' := by push_cast at htk; exact htk
          rw [ht0def]; linarith⟩
        have := hsl (t - t0) ht' x
        simp only [add_sub_cancel] at this
        rw [hDs]; exact this
  -- assemble with the lower orders and the jet passage
  refine ⟨max A (D N), le_max_of_le_left hA, fun t ht x => ?_⟩
  have hB' : 0 ≤ max A (D N) := le_max_of_le_left hA
  have hbd : ∀ n' ≤ n, ∀ (h : Fin n' → ℝ) (e : Fin n' → Euc d),
      (∀ i, h i ≠ 0) → (∀ i, ‖e i‖ = 1) → ∀ y,
      ‖gradient (s67bd_mixedDiff n' h e (u t)) y‖ ≤ max A (D N) := by
    intro n' hn' h e hh he y
    rcases Nat.lt_or_ge n' n with hlt | hge
    · have hle : n' + 1 ≤ n + 1 := Nat.succ_le_succ hlt.le
      have hreg' : ContDiff ℝ ((n' + 1 : ℕ) : WithTop ℕ∞) (u t) :=
        (hreg t ht).of_le (by exact_mod_cast hle)
      exact (s67bd61_lower n' h e hh he (u t) hreg' hA
        (fun z => hlower t ht n' hlt z) y).trans (le_max_left _ _)
    · have hnn : n' = n := le_antisymm hn' hge
      subst hnn
      exact (main N h e hh he t ht (by rw [hNτ']; exact ht.2) y).trans (le_max_right _ _)
  exact (s67bd_difference_to_jet d n (u t) (hreg t ht) _ hB' hbd).1 n le_rfl x
end HRS.MS.BreakdownS67
