import HRS.PDE.Stability
import HRS.PDE.EnergyTorusDeriv
import HRS.PDE.EnergyTorus
import HRS.PDE.HsAnalysis
import HRS.PDE.Uniqueness
import HRS.PDE.Toolbox

/-!
# Time regularity of the forward solution from weak continuity (Prop 3.9 (c), core)

Helper lemmas in `HRS.PDE.TRB` and `forward_time_regularity_core`: for a forward solution
`F ∈ C_w([0,t];H^m)` (with `F ∈ C([0,t];H^m)` when `ν > 0`), the generator path
`τ ↦ 𝓛^{t-τ}F(τ)` is continuous in `H^{m-2}` and is the `H^{m-2}`-derivative of `F`.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ComplexConjugate

namespace HRS.PDE.TRB

variable {d : ℕ}

/-! ### The Riesz multiplier gains `e = min(1, d - s)` derivatives -/

theorem norm_gradRieszCoeff_gain_le {s : ℝ} {e : ℝ} (he1 : e ≤ 1) (hes : e ≤ (d : ℝ) - s)
    (i : Fin d) (c : Coeff d) (k : Lattice d) :
    ‖gradRieszCoeff d s i c k‖ ^ 2 ≤ |rieszConst d s| ^ 2 * sobWeight (1 - e) k * ‖c k‖ ^ 2 := by
  by_cases hk : k = 0
  · subst hk
    have : ‖gradRieszCoeff d s i c 0‖ = 0 := by
      rw [norm_gradRieszCoeff]; simp
    rw [this, zero_pow two_ne_zero]
    exact mul_nonneg (mul_nonneg (sq_nonneg _) (sobWeight_pos _ _).le) (sq_nonneg _)
  · rw [norm_gradRieszCoeff]
    have he := one_le_enorm_of_ne_zero hk
    have hx : 1 ≤ 2 * Real.pi * Lattice.enorm k := by nlinarith [Real.pi_gt_three]
    have hx0 : 0 < 2 * Real.pi * Lattice.enorm k := by linarith
    have h1 : |rieszCoeff d s k| =
        |rieszConst d s| * (2 * Real.pi * Lattice.enorm k) ^ (s - (d : ℝ)) := by
      simp only [rieszCoeff, hk, ite_false, abs_mul]
      rw [abs_of_nonneg (Real.rpow_nonneg hx0.le _)]
    have h2 : 2 * Real.pi * |((k i : ℤ) : ℝ)| ≤ 2 * Real.pi * Lattice.enorm k :=
      mul_le_mul_of_nonneg_left (abs_coord_le_enorm k i) (by positivity)
    set x := 2 * Real.pi * Lattice.enorm k with hxdef
    have h3 : x ^ (s - (d : ℝ)) * x ≤ x ^ (1 - e) := by
      rw [← Real.rpow_add_one hx0.ne']
      exact Real.rpow_le_rpow_of_exponent_le hx (by linarith)
    have h4 : x ^ (1 - e) ≤ Lattice.jp k ^ (1 - e) :=
      Real.rpow_le_rpow hx0.le (Torus.two_pi_enorm_le_jp k) (by linarith)
    have h5 : 2 * Real.pi * |((k i : ℤ) : ℝ)| * (|rieszCoeff d s k| * ‖c k‖) ≤
        |rieszConst d s| * Lattice.jp k ^ (1 - e) * ‖c k‖ := by
      rw [h1]
      have hc := abs_nonneg (rieszConst d s)
      have hxs : 0 ≤ x ^ (s - (d : ℝ)) := Real.rpow_nonneg hx0.le _
      calc 2 * Real.pi * |((k i : ℤ) : ℝ)| * (|rieszConst d s| * x ^ (s - (d : ℝ)) * ‖c k‖)
          = |rieszConst d s| * (x ^ (s - (d : ℝ)) * (2 * Real.pi * |((k i : ℤ) : ℝ)|)) *
            ‖c k‖ := by ring
        _ ≤ |rieszConst d s| * (x ^ (s - (d : ℝ)) * x) * ‖c k‖ := by
            gcongr
        _ ≤ |rieszConst d s| * Lattice.jp k ^ (1 - e) * ‖c k‖ := by
            gcongr
            exact h3.trans h4
    have h0 : 0 ≤ 2 * Real.pi * |((k i : ℤ) : ℝ)| * (|rieszCoeff d s k| * ‖c k‖) := by positivity
    have h6 := pow_le_pow_left₀ h0 h5 2
    refine h6.trans (le_of_eq ?_)
    rw [mul_pow, mul_pow, Torus.jp_rpow_sq, sobWeight_eq_jp]

theorem gradRiesz_gain {s : ℝ} {e : ℝ} (he1 : e ≤ 1) (hes : e ≤ (d : ℝ) - s) (i : Fin d)
    {r : ℝ} {c : Coeff d} (hc : MemHs (r + 1) c) :
    MemHs (r + e) (gradRieszCoeff d s i c) ∧
      hsNormSq (r + e) (gradRieszCoeff d s i c) ≤ |rieszConst d s| ^ 2 * hsNormSq (r + 1) c := by
  have hle : ∀ k, sobWeight (r + e) k * ‖gradRieszCoeff d s i c k‖ ^ 2 ≤
      |rieszConst d s| ^ 2 * (sobWeight (r + 1) k * ‖c k‖ ^ 2) := by
    intro k
    have h := norm_gradRieszCoeff_gain_le he1 hes i c k
    have hw := (sobWeight_pos (d := d) (r + e) k).le
    have hw1 : sobWeight (r + 1) k = sobWeight (r + e) k * sobWeight (1 - e) k := by
      rw [← sobWeight_add]; congr 1; ring
    calc sobWeight (r + e) k * ‖gradRieszCoeff d s i c k‖ ^ 2
        ≤ sobWeight (r + e) k * (|rieszConst d s| ^ 2 * sobWeight (1 - e) k * ‖c k‖ ^ 2) :=
          mul_le_mul_of_nonneg_left h hw
      _ = _ := by rw [hw1]; ring
  have hs : MemHs (r + e) (gradRieszCoeff d s i c) :=
    Summable.of_nonneg_of_le (fun k => mul_nonneg (sobWeight_pos _ k).le (sq_nonneg _)) hle
      (hc.mul_left _)
  refine ⟨hs, ?_⟩
  unfold hsNormSq
  rw [← tsum_mul_left]
  exact hs.tsum_le_tsum hle (hc.mul_left _)


/-- The smoothing gain `ε = min(1, d - s) > 0` of the nonlocal term. -/
def eps (d : ℕ) (s : ℝ) : ℝ := min 1 ((d : ℝ) - s)

theorem eps_pos {s : ℝ} (hsd : s < d) : 0 < eps d s := lt_min one_pos (by linarith)

theorem eps_le_one (d : ℕ) (s : ℝ) : eps d s ≤ 1 := min_le_left _ _

theorem eps_le_sub (d : ℕ) (s : ℝ) : eps d s ≤ (d : ℝ) - s := min_le_right _ _

theorem finsum_bound {ι : Type*} (S : Finset ι) (x : ι → Coeff d) (r A : ℝ)
    (hx : ∀ i ∈ S, MemHs r (x i) ∧ hsNormSq r (x i) ≤ A) :
    MemHs r (fun k => ∑ i ∈ S, x i k) ∧
      hsNormSq r (fun k => ∑ i ∈ S, x i k) ≤ S.card * (S.card * A) := by
  obtain ⟨h1, h2⟩ := StabAux.hsNormSq_finsum_le S x r (fun i hi => (hx i hi).1)
  refine ⟨h1, h2.trans ?_⟩
  refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
  calc ∑ i ∈ S, hsNormSq r (x i) ≤ ∑ _i ∈ S, A := Finset.sum_le_sum fun i hi => (hx i hi).2
    _ = S.card * A := by simp

/-- **Step B**: the first-order part `b·∇F - 𝒢[F]` of the generator maps `H^m` into
`H^{m-2+ε}` with a uniform bound. -/
theorem firstOrder_bound (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (m : ℕ)
    (hm : 1 ≤ m) (MB Λ VB : ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (D : DynData d), D.s = s → MatBound MB D.M → VHyp m VB D.V →
      ∀ ρ : Torus d → ℝ, IsProbDensity ρ → Torus.IsCk (m + 3) ρ → Torus.cbNorm (m + 3) ρ ≤ Λ →
      ∀ F : Coeff d, MemHs (m : ℝ) F →
        MemHs ((m : ℝ) - 2 + eps d s) (fun k => transportCoeff D ρ F k - nonlocalCoeff D ρ F k) ∧
        hsNormSq ((m : ℝ) - 2 + eps d s)
            (fun k => transportCoeff D ρ F k - nonlocalCoeff D ρ F k) ≤ K * hsNormSq (m : ℝ) F := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  obtain ⟨B, hB⟩ := exists_driftFuns hd s hs0 hsd (n + 1) MB Λ VB
  obtain ⟨C0, hC0, hP⟩ := StabAux.prod_nat hd n
  set c0 : ℝ := |rieszConst d s| with hc0
  set B' : ℝ := max B 0 with hB'
  set Λ' : ℝ := max Λ 0 with hΛ'
  set MB' : ℝ := max MB 0 with hMB'
  have hdd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  refine ⟨2 * ((d : ℝ) * ((d : ℝ) * (C0 * B' ^ 2))) +
      2 * ((d : ℝ) * ((d : ℝ) * ((d : ℝ) * ((d : ℝ) * (MB' ^ 2 * (c0 ^ 2 * (C0 * Λ' ^ 2))))))),
    by positivity, ?_⟩
  intro D hDs hM hV ρ hp hk hb F hF
  have hF' : MemHs ((n : ℝ) + 1) F := by push_cast at hF; exact hF
  set X := hsNormSq ((n : ℝ) + 1) F with hX
  have hX0 : 0 ≤ X := hsNormSq_nonneg _ _
  have hlev : (((n + 1 : ℕ) : ℝ) - 2 + eps d s) = ((n : ℝ) - 1) + eps d s := by push_cast; ring
  have hlev1 : ((n : ℝ) - 1) + 1 = n := by ring
  have hd0 : ∀ j, MemHs (n : ℝ) (derivCoeff j F) ∧ hsNormSq (n : ℝ) (derivCoeff j F) ≤ X :=
    fun j => StabAux.deriv_bound hF' j
  -- transport
  obtain ⟨b, hb1, hb2, hb3⟩ := hB D hDs hM hV ρ hp hk hb
  have hT : ∀ j : Fin d, MemHs (n : ℝ) (mulCoeff (driftCoeff D ρ j) (derivCoeff j F)) ∧
      hsNormSq (n : ℝ) (mulCoeff (driftCoeff D ρ j) (derivCoeff j F)) ≤ C0 * B' ^ 2 * X := by
    intro j
    rw [← hb3 j]
    have hbn : Torus.IsCk (n : WithTop ℕ∞) (b j) :=
      ET.isCk_mono' (a := n) (b := n + 1 + 1) (by omega) (hb1 j)
    obtain ⟨h1, h2⟩ := hP (b j) hbn _ (hd0 j).1
    refine ⟨h1, h2.trans ?_⟩
    have hcb : Torus.cbNorm n (b j) ^ 2 ≤ B' ^ 2 :=
      pow_le_pow_left₀ (cbNorm_nonneg' _ _)
        (((ET.cbNorm_mono' (a := n) (b := n + 1 + 1) (by omega) (b j)).trans (hb2 j)).trans (le_max_left _ _)) 2
    exact mul_le_mul (mul_le_mul_of_nonneg_left hcb hC0) (hd0 j).2 (hsNormSq_nonneg _ _)
      (by positivity)
  obtain ⟨hTm, hTle⟩ := finsum_bound Finset.univ
    (fun j => mulCoeff (driftCoeff D ρ j) (derivCoeff j F)) (n : ℝ) _ (fun j _ => hT j)
  have hTle' : hsNormSq (n : ℝ) (fun k => transportCoeff D ρ F k) ≤
      (d : ℝ) * ((d : ℝ) * (C0 * B' ^ 2 * X)) := by
    simpa [transportCoeff] using hTle
  have hTm' : MemHs (n : ℝ) (fun k => transportCoeff D ρ F k) := by
    simpa [transportCoeff] using hTm
  have hle1 : ((n : ℝ) - 1) + eps d s ≤ n := by
    have := eps_le_one d s; linarith
  have hT1 : MemHs (((n : ℝ) - 1) + eps d s) (fun k => transportCoeff D ρ F k) := hTm'.mono hle1
  have hT2 : hsNormSq (((n : ℝ) - 1) + eps d s) (fun k => transportCoeff D ρ F k) ≤
      (d : ℝ) * ((d : ℝ) * (C0 * B' ^ 2 * X)) :=
    (hsNormSq_mono hle1 hTm').trans hTle'
  -- nonlocal
  have hN : ∀ i j : Fin d, MemHs (((n : ℝ) - 1) + eps d s) (fun k => ((D.M j i : ℝ) : ℂ) *
      gradRieszCoeff d D.s i (mulCoeff (coeffOf ρ) (derivCoeff j F)) k) ∧
      hsNormSq (((n : ℝ) - 1) + eps d s) (fun k => ((D.M j i : ℝ) : ℂ) *
      gradRieszCoeff d D.s i (mulCoeff (coeffOf ρ) (derivCoeff j F)) k) ≤
        MB' ^ 2 * (c0 ^ 2 * (C0 * Λ' ^ 2 * X)) := by
    intro i j
    have hρn : Torus.IsCk (n : WithTop ℕ∞) ρ := by
      have hk' : Torus.IsCk ((n + 1 + 3 : ℕ) : WithTop ℕ∞) ρ := by exact_mod_cast hk
      exact ET.isCk_mono' (a := n) (b := n + 1 + 3) (by omega) hk'
    obtain ⟨h1, h2⟩ := hP ρ hρn _ (hd0 j).1
    have hρΛ : Torus.cbNorm n ρ ^ 2 ≤ Λ' ^ 2 :=
      pow_le_pow_left₀ (cbNorm_nonneg' _ _)
        (((ET.cbNorm_mono' (a := n) (b := n + 1 + 3) (by omega) ρ).trans hb).trans (le_max_left _ _)) 2
    have e1 : hsNormSq (n : ℝ) (mulCoeff (coeffOf ρ) (derivCoeff j F)) ≤ C0 * Λ' ^ 2 * X :=
      h2.trans (mul_le_mul (mul_le_mul_of_nonneg_left hρΛ hC0) (hd0 j).2
        (hsNormSq_nonneg _ _) (by positivity))
    have h1' : MemHs (((n : ℝ) - 1) + 1) (mulCoeff (coeffOf ρ) (derivCoeff j F)) := by
      rw [hlev1]; exact h1
    obtain ⟨h3, h4⟩ := gradRiesz_gain (s := D.s) (eps_le_one d s) (by rw [hDs]; exact eps_le_sub d s) i h1'
    obtain ⟨h5, h6⟩ := StabAux.hsNormSq_const_mul (((n : ℝ) - 1) + eps d s) ((D.M j i : ℝ) : ℂ) _ h3
    refine ⟨h5, ?_⟩
    rw [h6, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    have hMj : D.M j i ^ 2 ≤ MB' ^ 2 := by
      have := pow_le_pow_left₀ (abs_nonneg _) ((hM j i).trans (le_max_left MB 0)) 2
      rwa [sq_abs] at this
    have hrz : hsNormSq (((n : ℝ) - 1) + 1) (mulCoeff (coeffOf ρ) (derivCoeff j F)) ≤
        C0 * Λ' ^ 2 * X := by rw [hlev1]; exact e1
    have e2 : hsNormSq (((n : ℝ) - 1) + eps d s)
        (gradRieszCoeff d D.s i (mulCoeff (coeffOf ρ) (derivCoeff j F))) ≤
        c0 ^ 2 * (C0 * Λ' ^ 2 * X) := by
      have : |rieszConst d D.s| = c0 := by rw [hDs]
      rw [this] at h4
      exact h4.trans (mul_le_mul_of_nonneg_left hrz (sq_nonneg _))
    exact mul_le_mul hMj e2 (hsNormSq_nonneg _ _) (sq_nonneg _)
  have hCi : ∀ i : Fin d, MemHs (((n : ℝ) - 1) + eps d s) (fun k => ∑ j : Fin d,
      ((D.M j i : ℝ) : ℂ) * gradRieszCoeff d D.s i (mulCoeff (coeffOf ρ) (derivCoeff j F)) k) ∧
      hsNormSq (((n : ℝ) - 1) + eps d s) (fun k => ∑ j : Fin d,
      ((D.M j i : ℝ) : ℂ) * gradRieszCoeff d D.s i (mulCoeff (coeffOf ρ) (derivCoeff j F)) k) ≤
      (d : ℝ) * ((d : ℝ) * (MB' ^ 2 * (c0 ^ 2 * (C0 * Λ' ^ 2 * X)))) := fun i =>
    finsum_bound Finset.univ (fun j k => ((D.M j i : ℝ) : ℂ) *
      gradRieszCoeff d D.s i (mulCoeff (coeffOf ρ) (derivCoeff j F)) k) _ _ (fun j _ => hN i j)
      |> fun h => by simpa using h
  obtain ⟨hNm, hNle⟩ := finsum_bound Finset.univ (fun i k => ∑ j : Fin d,
      ((D.M j i : ℝ) : ℂ) * gradRieszCoeff d D.s i (mulCoeff (coeffOf ρ) (derivCoeff j F)) k)
      (((n : ℝ) - 1) + eps d s) _ (fun i _ => hCi i)
  simp only [Finset.card_univ, Fintype.card_fin] at hNle
  have hNm' : MemHs (((n : ℝ) - 1) + eps d s) (fun k => nonlocalCoeff D ρ F k) := hNm
  have hNle' : hsNormSq (((n : ℝ) - 1) + eps d s) (fun k => nonlocalCoeff D ρ F k) ≤
      (d : ℝ) * ((d : ℝ) * ((d : ℝ) * ((d : ℝ) * (MB' ^ 2 * (c0 ^ 2 * (C0 * Λ' ^ 2 * X)))))) := by
    refine hNle.trans (le_of_eq ?_)
    ring
  rw [hlev]
  obtain ⟨h1, h2⟩ := ET.memHs_sub_sq hT1 hNm'
  refine ⟨h1, h2.trans ?_⟩
  have := add_le_add (mul_le_mul_of_nonneg_left hT2 (by norm_num : (0 : ℝ) ≤ 2))
    (mul_le_mul_of_nonneg_left hNle' (by norm_num : (0 : ℝ) ≤ 2))
  refine this.trans (le_of_eq ?_)
  push_cast
  ring


/-! ### Step A: coordinate convergence under bounded + coordinatewise convergence -/

/-- Bounded in `H^m` and coordinatewise convergent implies convergence in `H^{m'}`, `m' < m`
(the tail argument of `continuousInHs_of_weak`, along an arbitrary filter). -/
theorem tendsto_hsNormSq_sub_of_bdd {α : Type*} {l : Filter α} {m m' : ℝ} (hm : m' < m)
    (X : α → Coeff d) (X0 : Coeff d) (B : ℝ)
    (hX : ∀ᶠ x in l, MemHs m (X x) ∧ hsNormSq m (X x) ≤ B)
    (hX0 : MemHs m X0 ∧ hsNormSq m X0 ≤ B)
    (hc : ∀ q, Tendsto (fun x => X x q) l (𝓝 (X0 q))) :
    Tendsto (fun x => hsNormSq m' (X x - X0)) l (𝓝 0) := by
  set x : α → Lattice d → ℝ := fun a k => sobWeight m k * ‖X a k - X0 k‖ ^ 2 with hx
  have hform : ∀ a, hsNormSq m' (X a - X0) = ∑' k, sobWeight (m' - m) k * x a k := by
    intro a
    unfold hsNormSq
    refine tsum_congr fun k => ?_
    simp only [hx, Pi.sub_apply]
    have : sobWeight m' k = sobWeight (m' - m) k * sobWeight m k := by
      rw [← sobWeight_add]; ring_nf
    rw [this, mul_assoc]
  simp_rw [hform]
  refine tendsto_tsum_weight_zero x (sobWeight (m' - m)) (4 * B) 
    (fun τ k => mul_nonneg (sobWeight_pos m k).le (sq_nonneg _))
    (fun k => (sobWeight_pos _ k).le) (tendsto_sobWeight_cofinite (by linarith)) ?_ ?_
  · filter_upwards [hX] with a ha
    have h := memHs_of_sum_le (m := m) (c := X a - X0) (C := 4 * B) (fun S => by
      calc ∑ k ∈ S, sobWeight m k * ‖(X a - X0) k‖ ^ 2
          ≤ ∑ k ∈ S, (2 * (sobWeight m k * ‖X a k‖ ^ 2) +
              2 * (sobWeight m k * ‖X0 k‖ ^ 2)) := by
            refine Finset.sum_le_sum fun k _ => ?_
            have hw := (sobWeight_pos m k).le
            simp only [Pi.sub_apply]
            have h1 : ‖X a k - X0 k‖ ^ 2 ≤ 2 * ‖X a k‖ ^ 2 + 2 * ‖X0 k‖ ^ 2 := by
              have h0 := norm_sub_le (X a k) (X0 k)
              nlinarith [norm_nonneg (X a k - X0 k), norm_nonneg (X a k),
                norm_nonneg (X0 k), sq_nonneg (‖X a k‖ - ‖X0 k‖)]
            nlinarith [mul_le_mul_of_nonneg_left h1 hw]
        _ = 2 * ∑ k ∈ S, sobWeight m k * ‖X a k‖ ^ 2 +
              2 * ∑ k ∈ S, sobWeight m k * ‖X0 k‖ ^ 2 := by
            rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
        _ ≤ 2 * B + 2 * B :=
            add_le_add (mul_le_mul_of_nonneg_left
              ((sum_le_hsNormSq ha.1 S).trans ha.2) (by norm_num))
              (mul_le_mul_of_nonneg_left
              ((sum_le_hsNormSq hX0.1 S).trans hX0.2) (by norm_num))
        _ = 4 * B := by ring)
    exact ⟨h.1, by have := h.2; unfold hsNormSq at this; simpa [hx, Pi.sub_apply] using this⟩
  · intro k
    have hk := hc k
    have : Tendsto (fun a => ‖X a k - X0 k‖) l (𝓝 0) := by
      have := (hk.sub_const (X0 k)).norm
      simpa using this
    have h2 := (this.pow 2).const_mul (sobWeight m k)
    simpa using h2


theorem deriv_zero_level {c : Coeff d} (hc : MemHs 1 c) (j : Fin d) :
    MemHs 0 (derivCoeff j c) ∧ hsNormSq 0 (derivCoeff j c) ≤ hsNormSq 1 c := by
  have h : MemHs ((0 : ℝ) + 1) c := by simpa using hc
  simpa using ET.hsNormSq_deriv_le h j

/-- Weak version of `tendsto_mulCoeff_deriv_strong`: the coefficient `a` and the function `F` are
only assumed bounded in `H^1` and coordinatewise convergent. -/
theorem tendsto_mulCoeff_deriv_weak {α : Type*} {l : Filter α} [l.NeBot] (a : α → Coeff d)
    (a0 : Coeff d) (Ka : ℝ)
    (ha : ∀ᶠ x in l, MemHs 1 (a x) ∧ hsNormSq 1 (a x) ≤ Ka)
    (ha0 : MemHs 1 a0 ∧ hsNormSq 1 a0 ≤ Ka)
    (hac : ∀ q, Tendsto (fun x => a x q) l (𝓝 (a0 q)))
    (Fa : α → Coeff d) (G : Coeff d) (KF : ℝ)
    (hFa : ∀ᶠ x in l, MemHs 1 (Fa x) ∧ hsNormSq 1 (Fa x) ≤ KF)
    (hG : MemHs 1 G ∧ hsNormSq 1 G ≤ KF)
    (hFc : ∀ q, Tendsto (fun x => Fa x q) l (𝓝 (G q))) (j : Fin d) (k : Lattice d) :
    Tendsto (fun x => mulCoeff (a x) (derivCoeff j (Fa x)) k) l
      (𝓝 (mulCoeff a0 (derivCoeff j G) k)) := by
  have hKF : 0 ≤ KF := (hsNormSq_nonneg _ _).trans hG.2
  have ha0' : MemHs 0 a0 := ha0.1.mono (by norm_num)
  -- the part with coefficient difference
  have hA : Tendsto (fun x => mulCoeff (a x - a0) (derivCoeff j (Fa x)) k) l (𝓝 0) := by
    have hdiff : Tendsto (fun x => hsNormSq 0 (a x - a0)) l (𝓝 0) :=
      tendsto_hsNormSq_sub_of_bdd (by norm_num) a a0 Ka ha ha0 hac
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hbd : ∀ᶠ x in l, ‖mulCoeff (a x - a0) (derivCoeff j (Fa x)) k‖ ≤
        Real.sqrt (hsNormSq 0 (a x - a0)) * Real.sqrt KF := by
      filter_upwards [ha, hFa] with x hx hFx
      have hm0 : MemHs 0 (a x - a0) := (ET.memHs_sub_sq (hx.1.mono (by norm_num)) ha0').1
      refine (mulCoeff_deriv_bound hm0 hFx.1 j k).trans ?_
      exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hFx.2) (Real.sqrt_nonneg _)
    refine squeeze_zero' (Filter.Eventually.of_forall fun _ => norm_nonneg _) hbd ?_
    have := ((Real.continuous_sqrt.tendsto 0).comp hdiff).mul_const (Real.sqrt KF)
    simpa using this
  -- the part with the fixed coefficient
  have hB : Tendsto (fun x => mulCoeff a0 (derivCoeff j (Fa x)) k) l
      (𝓝 (mulCoeff a0 (derivCoeff j G) k)) := by
    have hv : Summable fun q => ‖a0 (k - q)‖ ^ 2 := (summable_sq_subLeft ha0' k).1
    have := tendsto_tsum_mul (l := l) (fun x q => derivCoeff j (Fa x) q) (derivCoeff j G)
      (fun q => a0 (k - q)) (Real.sqrt KF) (Real.sqrt_nonneg _) ?_ hv ?_
    · simpa [mulCoeff, mul_comm] using this
    · filter_upwards [hFa] with x hx S
      rw [Real.sq_sqrt hKF]
      refine le_trans (Finset.sum_le_sum fun q _ => norm_derivCoeff_sq_le j (Fa x) q) ?_
      exact (sum_le_hsNormSq hx.1 S).trans hx.2
    · intro q
      simp only [derivCoeff]
      exact (hFc q).const_mul _
  have hsum := hA.add hB
  rw [zero_add] at hsum
  refine hsum.congr' ?_
  filter_upwards [ha, hFa] with x hx hFx
  have h := congrFun (StabAux.mulCoeff_sub_left (hx.1.mono (by norm_num)) ha0'
    (deriv_zero_level hFx.1 j).1) k
  simp only [Pi.sub_apply] at h
  rw [h]
  ring


/-- Coordinates of the forward generator converge under bounded + coordinatewise convergence. -/
theorem tendsto_forwardGen_weak {α : Type*} {l : Filter α} [l.NeBot] (D : DynData d)
    (ρ : α → Torus d → ℝ) (ρ0 : Torus d → ℝ) (K : ℝ)
    (hρ : ∀ᶠ x in l, MemHs 1 (coeffOf (ρ x)) ∧ hsNormSq 1 (coeffOf (ρ x)) ≤ K)
    (hρ0 : MemHs 1 (coeffOf ρ0) ∧ hsNormSq 1 (coeffOf ρ0) ≤ K)
    (hρc : ∀ q, Tendsto (fun x => coeffOf (ρ x) q) l (𝓝 (coeffOf ρ0 q)))
    (hb : ∀ᶠ x in l, ∀ j, MemHs 1 (driftCoeff D (ρ x) j) ∧
      hsNormSq 1 (driftCoeff D (ρ x) j) ≤ K)
    (hb0 : ∀ j, MemHs 1 (driftCoeff D ρ0 j) ∧ hsNormSq 1 (driftCoeff D ρ0 j) ≤ K)
    (hbc : ∀ j q, Tendsto (fun x => driftCoeff D (ρ x) j q) l (𝓝 (driftCoeff D ρ0 j q)))
    (Fa : α → Coeff d) (G : Coeff d) (KF : ℝ)
    (hFa : ∀ᶠ x in l, MemHs 1 (Fa x) ∧ hsNormSq 1 (Fa x) ≤ KF)
    (hG : MemHs 1 G ∧ hsNormSq 1 G ≤ KF)
    (hFc : ∀ q, Tendsto (fun x => Fa x q) l (𝓝 (G q))) (k : Lattice d) :
    Tendsto (fun x => forwardGen D (ρ x) (Fa x) k) l (𝓝 (forwardGen D ρ0 G k)) := by
  unfold forwardGen
  refine Tendsto.sub (Tendsto.add ?_ ?_) ?_
  · simp only [laplaceCoeff]
    exact ((hFc k).const_mul _).const_mul _
  · unfold transportCoeff
    refine tendsto_finsetSum _ fun j _ => ?_
    exact tendsto_mulCoeff_deriv_weak (fun x => driftCoeff D (ρ x) j) (driftCoeff D ρ0 j) K
      (by filter_upwards [hb] with x hx using hx j) (hb0 j) (hbc j) Fa G KF hFa hG hFc j k
  · unfold nonlocalCoeff
    refine tendsto_finsetSum _ fun i _ => tendsto_finsetSum _ fun j _ => ?_
    have := tendsto_mulCoeff_deriv_weak (fun x => coeffOf (ρ x)) (coeffOf ρ0) K hρ hρ0 hρc
      Fa G KF hFa hG hFc j k
    simp only [gradRieszCoeff, derivCoeff, rieszMult]
    exact (this.const_mul _).const_mul _ |>.const_mul _


/-- Uniform `H^1` bounds of the density and the drift under the coefficient hypotheses. -/
theorem coeff_H1_bound (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {m : ℕ}
    {R : Regime} {MB Λ VB : ℝ} {D : DynData d} {ν₀ T : ℝ} {μ : ℝ → Torus d → ℝ}
    (hA : AdjointData s m R MB Λ VB D ν₀ T μ) :
    ∃ K : ℝ, ∀ r ∈ Set.Icc 0 T, (MemHs 1 (coeffOf (μ r)) ∧ hsNormSq 1 (coeffOf (μ r)) ≤ K) ∧
      ∀ j, MemHs 1 (driftCoeff D (μ r) j) ∧ hsNormSq 1 (driftCoeff D (μ r) j) ≤ K := by
  obtain ⟨Bd, hBd⟩ := exists_driftFuns hd s hs0 hsd m MB Λ VB
  refine ⟨(1 + d) * (max Λ 0) ^ 2 + (1 + d) * (max Bd 0) ^ 2, fun r hr => ?_⟩
  have hd0 : (0 : ℝ) ≤ 1 + d := by positivity
  have hρ := memHs_one_coeffOf_cbNorm (m + 3) (by omega) (μ r) (isCk_cast (hA.hμ.smooth r hr))
  have hcb : Torus.cbNorm (m + 3) (μ r) ^ 2 ≤ (max Λ 0) ^ 2 :=
    pow_le_pow_left₀ (cbNorm_nonneg' _ _) ((hA.hμ.bound r hr).trans (le_max_left _ _)) 2
  have hρK : hsNormSq 1 (coeffOf (μ r)) ≤ (1 + d) * (max Λ 0) ^ 2 :=
    hρ.2.trans (mul_le_mul_of_nonneg_left hcb hd0)
  have hpos2 : 0 ≤ (1 + d : ℝ) * (max Bd 0) ^ 2 := by positivity
  have hpos1 : 0 ≤ (1 + d : ℝ) * (max Λ 0) ^ 2 := by positivity
  refine ⟨⟨hρ.1, by linarith⟩, fun j => ?_⟩
  obtain ⟨b, hb1, hb2, hb3⟩ := hBd D hA.hs hA.hM hA.hV (μ r) (hA.hμ.prob r hr)
    (hA.hμ.smooth r hr) (hA.hμ.bound r hr)
  have hb1' : Torus.IsCk (((m + 1 : ℕ)) : WithTop ℕ∞) (b j) := by exact_mod_cast hb1 j
  have h1 := memHs_one_coeffOf_cbNorm (m + 1) (by omega) (b j) hb1'
  rw [hb3 j] at h1
  refine ⟨h1.1, h1.2.trans ?_⟩
  have hcb' : Torus.cbNorm (m + 1) (b j) ^ 2 ≤ (max Bd 0) ^ 2 :=
    pow_le_pow_left₀ (cbNorm_nonneg' _ _) ((hb2 j).trans (le_max_left _ _)) 2
  have := mul_le_mul_of_nonneg_left hcb' hd0
  linarith

theorem gen_coord_continuousOn_weak (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {m : ℕ}
    (hm : 1 ≤ m) {R : Regime} {MB Λ VB : ℝ} {D : DynData d} {ν₀ T : ℝ}
    {μ : ℝ → Torus d → ℝ} (hA : AdjointData s m R MB Λ VB D ν₀ T μ) {t : ℝ}
    (ht : t ∈ Set.Ioc 0 T) {F : ℝ → Coeff d} (hw : WeakContinuousInHs (m : ℝ) F t)
    (k : Lattice d) :
    ContinuousOn (fun σ => forwardGen D (μ (t - σ)) (F σ) k) (Set.Icc 0 t) := by
  obtain ⟨K, hK⟩ := coeff_H1_bound hd hs0 hsd hA
  obtain ⟨B, hB0, hB⟩ := bounded_of_weakContinuous hw
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hF1 : ∀ τ ∈ Set.Icc (0 : ℝ) t, MemHs 1 (F τ) ∧ hsNormSq 1 (F τ) ≤ B ^ 2 := fun τ hτ =>
    ⟨(hw.1 τ hτ).mono hm1, (hsNormSq_mono hm1 (hw.1 τ hτ)).trans (hB τ hτ)⟩
  have hcoef : ∀ q, ContinuousOn (fun σ => coeffOf (μ (t - σ)) q) (Set.Icc 0 t) := by
    intro q
    refine (coeffOf_continuousOn hA.hμ q).comp (continuousOn_const.sub continuousOn_id) ?_
    intro σ hσ
    exact ET.tsub_mem_Icc ht hσ
  have hdrift : ∀ j q, ContinuousOn (fun σ => driftCoeff D (μ (t - σ)) j q) (Set.Icc 0 t) :=
    fun j q => continuousOn_drift D (fun σ => μ (t - σ)) hcoef j q
  intro p hp
  have : (𝓝[Set.Icc 0 t] p).NeBot := nhdsWithin_neBot_of_mem hp
  have hev : ∀ᶠ x in 𝓝[Set.Icc 0 t] p, x ∈ Set.Icc 0 t := self_mem_nhdsWithin
  exact tendsto_forwardGen_weak (l := 𝓝[Set.Icc 0 t] p) D (fun x => μ (t - x)) (μ (t - p)) K
    (by filter_upwards [hev] with x hx using (hK _ (ET.tsub_mem_Icc ht hx)).1)
    (hK _ (ET.tsub_mem_Icc ht hp)).1
    (fun q => (hcoef q p hp).tendsto)
    (by filter_upwards [hev] with x hx using (hK _ (ET.tsub_mem_Icc ht hx)).2)
    (fun j => (hK _ (ET.tsub_mem_Icc ht hp)).2 j)
    (fun j q => (hdrift j q p hp).tendsto)
    F (F p) (B ^ 2) (by filter_upwards [hev] with x hx using hF1 x hx) (hF1 p hp)
    (fun q => (continuousOn_coord_of_weak hw q p hp).tendsto) k


/-! ### Step C: tail lemma and continuity bookkeeping -/

theorem continuousInHs_of_sq {r t : ℝ} {F : ℝ → Coeff d}
    (hmem : ∀ τ ∈ Set.Icc (0 : ℝ) t, MemHs r (F τ))
    (hlim : ∀ τ₀ ∈ Set.Icc (0 : ℝ) t,
      Tendsto (fun τ => hsNormSq r (F τ - F τ₀)) (𝓝[Set.Icc 0 t] τ₀) (𝓝 0)) :
    ContinuousInHs r F t := by
  refine ⟨hmem, fun τ₀ hτ₀ => ?_⟩
  have := (Real.continuous_sqrt.tendsto 0).comp (hlim τ₀ hτ₀)
  simpa [hsNorm, Function.comp_def] using this

theorem continuousInHs_add {r t : ℝ} {X Y : ℝ → Coeff d} (hX : ContinuousInHs r X t)
    (hY : ContinuousInHs r Y t) : ContinuousInHs r (fun τ => X τ + Y τ) t := by
  refine continuousInHs_of_sq (fun τ hτ => (ET.memHs_add_sq (hX.1 τ hτ) (hY.1 τ hτ)).1)
    (fun τ₀ hτ₀ => ?_)
  have h1 := ET.tendsto_hsNormSq_sub hX hτ₀
  have h2 := ET.tendsto_hsNormSq_sub hY hτ₀
  have h3 : Tendsto (fun τ => 2 * hsNormSq r (X τ - X τ₀) + 2 * hsNormSq r (Y τ - Y τ₀))
      (𝓝[Set.Icc 0 t] τ₀) (𝓝 (2 * 0 + 2 * 0)) := (h1.const_mul 2).add (h2.const_mul 2)
  rw [mul_zero, add_zero] at h3
  refine squeeze_zero' (Filter.Eventually.of_forall fun τ => hsNormSq_nonneg _ _) ?_ h3
  filter_upwards [self_mem_nhdsWithin] with τ hτ
  have e' : (X τ + Y τ) - (X τ₀ + Y τ₀) = (X τ - X τ₀) + (Y τ - Y τ₀) := by
    funext k; simp; ring
  rw [e']
  exact (ET.memHs_add_sq (ET.memHs_sub_sq (hX.1 τ hτ) (hX.1 τ₀ hτ₀)).1
    (ET.memHs_sub_sq (hY.1 τ hτ) (hY.1 τ₀ hτ₀)).1).2

/-- **Tail lemma**: a path that is bounded in `H^{σ+δ}` (`δ > 0`) with continuous coordinates is
norm-continuous in `H^σ`. -/
theorem continuousInHs_of_bdd {σ δ t : ℝ} (hδ : 0 < δ) {H : ℝ → Coeff d} (B : ℝ)
    (hmem : ∀ τ ∈ Set.Icc (0 : ℝ) t, MemHs (σ + δ) (H τ))
    (hB : ∀ τ ∈ Set.Icc (0 : ℝ) t, hsNormSq (σ + δ) (H τ) ≤ B)
    (hc : ∀ k, ContinuousOn (fun τ => H τ k) (Set.Icc 0 t)) : ContinuousInHs σ H t := by
  have hB0 : 0 ≤ Real.sqrt (max B 0) := Real.sqrt_nonneg _
  have hw : WeakContinuousInHs (σ + δ) H t :=
    weakContinuous_of_bdd hmem (Real.sqrt (max B 0)) hB0 (fun τ hτ => by
      rw [Real.sq_sqrt (le_max_right _ _)]
      exact (hB τ hτ).trans (le_max_left _ _)) hc
  exact continuousInHs_of_weak hw σ (by linarith)


/-! ### Step D: continuity of the generator path in `H^{m-2}` -/

theorem continuousInHs_laplace {r t : ℝ} {F : ℝ → Coeff d} (hF : ContinuousInHs (r + 2) F t)
    (c : ℝ) : ContinuousInHs r (fun τ k => (c : ℂ) * laplaceCoeff (F τ) k) t := by
  have hmem : ∀ τ ∈ Set.Icc (0 : ℝ) t, MemHs r (fun k => (c : ℂ) * laplaceCoeff (F τ) k) :=
    fun τ hτ => (StabAux.hsNormSq_const_mul r (c : ℂ) _ (StabAux.laplace_bound (hF.1 τ hτ)).1).1
  refine continuousInHs_of_sq hmem (fun τ₀ hτ₀ => ?_)
  have h1 := ET.tendsto_hsNormSq_sub hF hτ₀
  have h3 := h1.const_mul (c ^ 2)
  rw [mul_zero] at h3
  refine squeeze_zero' (Filter.Eventually.of_forall fun τ => hsNormSq_nonneg _ _) ?_ h3
  filter_upwards [self_mem_nhdsWithin] with τ hτ
  have e : (fun k => (c : ℂ) * laplaceCoeff (F τ) k) - (fun k => (c : ℂ) * laplaceCoeff (F τ₀) k) =
      fun k => (c : ℂ) * laplaceCoeff (F τ - F τ₀) k := by
    funext k; simp [laplaceCoeff]; ring
  rw [e]
  obtain ⟨hm1, -⟩ := ET.memHs_sub_sq (hF.1 τ hτ) (hF.1 τ₀ hτ₀)
  obtain ⟨-, h2⟩ := StabAux.hsNormSq_const_mul r (c : ℂ) _ (StabAux.laplace_bound hm1).1
  rw [h2, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  exact mul_le_mul_of_nonneg_left (StabAux.laplace_bound hm1).2 (sq_nonneg _)

theorem gen_continuousInHs (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {m : ℕ}
    (hm : 1 ≤ m) {R : Regime} {MB Λ VB : ℝ} {D : DynData d} {ν₀ T : ℝ}
    {μ : ℝ → Torus d → ℝ} (hA : AdjointData s m R MB Λ VB D ν₀ T μ) {t : ℝ}
    (ht : t ∈ Set.Ioc 0 T) {F : ℝ → Coeff d} (hw : WeakContinuousInHs (m : ℝ) F t)
    (hstrong : 0 < D.invβ → ContinuousInHs (m : ℝ) F t) :
    ContinuousInHs ((m : ℝ) - 2) (fun τ => forwardGen D (μ (t - τ)) (F τ)) t := by
  obtain ⟨K, hK0, hKb⟩ := firstOrder_bound hd s hs0 hsd m hm MB Λ VB
  obtain ⟨B, hB0, hB⟩ := bounded_of_weakContinuous hw
  set P : ℝ → Coeff d := fun τ k => transportCoeff D (μ (t - τ)) (F τ) k -
    nonlocalCoeff D (μ (t - τ)) (F τ) k with hPdef
  set Q : ℝ → Coeff d := fun τ k => ((D.invβ : ℝ) : ℂ) * laplaceCoeff (F τ) k with hQdef
  have hPb : ∀ τ ∈ Set.Icc (0 : ℝ) t, MemHs ((m : ℝ) - 2 + eps d s) (P τ) ∧
      hsNormSq ((m : ℝ) - 2 + eps d s) (P τ) ≤ K * B ^ 2 := by
    intro τ hτ
    have hr := ET.tsub_mem_Icc ht hτ
    obtain ⟨h1, h2⟩ := hKb D hA.hs hA.hM hA.hV (μ (t - τ)) (hA.hμ.prob _ hr)
      (hA.hμ.smooth _ hr) (hA.hμ.bound _ hr) (F τ) (hw.1 τ hτ)
    exact ⟨h1, h2.trans (mul_le_mul_of_nonneg_left (hB τ hτ) hK0)⟩
  have hPc : ∀ k, ContinuousOn (fun τ => P τ k) (Set.Icc 0 t) := by
    intro k
    have h1 := gen_coord_continuousOn_weak hd hs0 hsd hm hA ht hw k
    have h2 : ContinuousOn (fun τ => Q τ k) (Set.Icc 0 t) := by
      simp only [hQdef, laplaceCoeff]
      exact continuousOn_const.mul (continuousOn_const.mul (continuousOn_coord_of_weak hw k))
    refine (h1.sub h2).congr (fun τ _ => ?_)
    simp only [hPdef, hQdef, forwardGen, Pi.sub_apply]
    ring
  have hP : ContinuousInHs ((m : ℝ) - 2) P t :=
    continuousInHs_of_bdd (eps_pos hsd) (K * B ^ 2) (fun τ hτ => (hPb τ hτ).1)
      (fun τ hτ => (hPb τ hτ).2) hPc
  have hQ : ContinuousInHs ((m : ℝ) - 2) Q t := by
    by_cases h0 : D.invβ = 0
    · have hQ0 : Q = fun _ => 0 := by
        funext τ k; simp [hQdef, h0]
      rw [hQ0]
      refine continuousInHs_of_sq (fun τ _ => by simp [MemHs]) (fun τ₀ _ => ?_)
      simp [hsNormSq]
      exact tendsto_const_nhds
    · have hpos : 0 < D.invβ := lt_of_le_of_ne D.hβ (Ne.symm h0)
      have h := hstrong hpos
      have e : (m : ℝ) = ((m : ℝ) - 2) + 2 := by ring
      rw [e] at h
      exact continuousInHs_laplace h D.invβ
  have hG : (fun τ => forwardGen D (μ (t - τ)) (F τ)) = fun τ => Q τ + P τ := by
    funext τ k
    simp only [hPdef, hQdef, Pi.add_apply, forwardGen]
    ring
  rw [hG]
  exact continuousInHs_add hQ hP


/-! ### Step E: difference quotients -/

theorem quotient_sq_bound {r t : ℝ} {F G : ℝ → Coeff d} (hG : ContinuousInHs r G t)
    (hFG : ∀ k, ∀ τ ∈ Set.Icc (0 : ℝ) t, ∀ τ' ∈ Set.Icc (0 : ℝ) t,
      F τ' k - F τ k = ∫ σ in τ..τ', G σ k)
    {τ τ' : ℝ} (hτ : τ ∈ Set.Icc (0 : ℝ) t) (hτ' : τ' ∈ Set.Icc (0 : ℝ) t) (hne : τ' ≠ τ)
    (η : ℝ) (hη : 0 ≤ η) (hsup : ∀ σ ∈ Set.uIcc τ τ', hsNormSq r (G σ - G τ) ≤ η ^ 2) :
    MemHs r (fun k => (F τ' k - F τ k) / ((τ' - τ : ℝ) : ℂ) - G τ k) ∧
      hsNormSq r (fun k => (F τ' k - F τ k) / ((τ' - τ : ℝ) : ℂ) - G τ k) ≤ η ^ 2 := by
  classical
  set h : ℂ := ((τ' - τ : ℝ) : ℂ) with hh
  have hh0 : h ≠ 0 := by
    rw [hh]; exact_mod_cast sub_ne_zero.mpr hne
  set q : Coeff d := fun k => (F τ' k - F τ k) / h - G τ k with hq
  have hsub : Set.uIcc τ τ' ⊆ Set.Icc 0 t := Set.uIcc_subset_Icc hτ hτ'
  have hint : ∀ k, IntervalIntegrable (fun σ => G σ k) MeasureTheory.volume τ τ' := fun k =>
    ((ET.continuousOn_coord_of_continuousInHs hG k).mono hsub).intervalIntegrable
  have hqk : ∀ k, q k = h⁻¹ * ∫ σ in τ..τ', (G σ k - G τ k) := by
    intro k
    rw [intervalIntegral.integral_sub (hint k) intervalIntegrable_const,
      intervalIntegral.integral_const, ← hFG k τ hτ τ' hτ', Complex.real_smul]
    simp only [hq]
    rw [← hh]
    field_simp
  refine memHs_of_sum_le (fun S => ?_)
  set X : ℝ := ∑ k ∈ S, sobWeight r k * ‖q k‖ ^ 2 with hX
  have hX0 : 0 ≤ X := Finset.sum_nonneg fun k _ => mul_nonneg (sobWeight_pos r k).le (sq_nonneg _)
  -- pointwise bound for the integrand
  have hpt : ∀ σ ∈ Set.uIcc τ τ', ‖∑ k ∈ S, (((sobWeight r k : ℝ) : ℂ) * (starRingEnd ℂ) (q k)) *
      (G σ k - G τ k)‖ ≤ Real.sqrt X * η := by
    intro σ hσ
    have hσ' : σ ∈ Set.Icc (0 : ℝ) t := hsub hσ
    obtain ⟨hmem, -⟩ := ET.memHs_sub_sq (hG.1 σ hσ') (hG.1 τ hτ)
    set a : Lattice d → ℝ := fun k => Real.sqrt (sobWeight r k) * ‖q k‖ with ha
    set b : Lattice d → ℝ := fun k => Real.sqrt (sobWeight r k) * ‖G σ k - G τ k‖ with hb
    have hw : ∀ k, Real.sqrt (sobWeight r k) * Real.sqrt (sobWeight r k) = sobWeight r k :=
      fun k => Real.mul_self_sqrt (sobWeight_pos (d := d) r k).le
    calc ‖∑ k ∈ S, (((sobWeight r k : ℝ) : ℂ) * (starRingEnd ℂ) (q k)) * (G σ k - G τ k)‖
        ≤ ∑ k ∈ S, a k * b k := by
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => le_of_eq ?_)
          simp only [ha, hb, norm_mul, Complex.norm_real, Complex.norm_conj, Real.norm_eq_abs,
            abs_of_pos (sobWeight_pos r k)]
          have := hw k
          linear_combination (-(‖q k‖ * ‖G σ k - G τ k‖)) * this
      _ ≤ Real.sqrt (∑ k ∈ S, a k ^ 2) * Real.sqrt (∑ k ∈ S, b k ^ 2) := by
          rw [← Real.sqrt_mul (Finset.sum_nonneg fun k _ => sq_nonneg _)]
          refine Real.le_sqrt_of_sq_le ?_
          exact Finset.sum_mul_sq_le_sq_mul_sq S a b
      _ ≤ Real.sqrt X * η := by
          have h1 : ∑ k ∈ S, a k ^ 2 = X := by
            refine Finset.sum_congr rfl fun k _ => ?_
            simp only [ha, mul_pow, Real.sq_sqrt (sobWeight_pos r k).le]
          have h2 : ∑ k ∈ S, b k ^ 2 ≤ η ^ 2 := by
            calc ∑ k ∈ S, b k ^ 2 = ∑ k ∈ S, sobWeight r k * ‖(G σ - G τ) k‖ ^ 2 := by
                  refine Finset.sum_congr rfl fun k _ => ?_
                  simp only [hb, mul_pow, Real.sq_sqrt (sobWeight_pos r k).le, Pi.sub_apply]
              _ ≤ hsNormSq r (G σ - G τ) := sum_le_hsNormSq hmem S
              _ ≤ η ^ 2 := hsup σ hσ
          rw [h1]
          refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
          exact Real.sqrt_le_iff.mpr ⟨hη, h2⟩ |>.trans (le_of_eq rfl)
  -- duality
  have hcomplex : (X : ℂ) = ∑ k ∈ S, (((sobWeight r k : ℝ) : ℂ) * (starRingEnd ℂ) (q k)) * q k := by
    simp only [hX]
    push_cast
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [mul_assoc, mul_comm ((starRingEnd ℂ) (q k)) (q k), Complex.mul_conj, Complex.normSq_eq_norm_sq]
    push_cast; ring
  have hexch : ∑ k ∈ S, (((sobWeight r k : ℝ) : ℂ) * (starRingEnd ℂ) (q k)) * q k =
      h⁻¹ * ∫ σ in τ..τ', ∑ k ∈ S, (((sobWeight r k : ℝ) : ℂ) * (starRingEnd ℂ) (q k)) *
        (G σ k - G τ k) := by
    rw [intervalIntegral.integral_finsetSum (fun k _ => ?_)]
    · rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [intervalIntegral.integral_const_mul, hqk k]
      ring
    · exact ((hint k).sub intervalIntegrable_const).const_mul _
  have hnorm : ‖(X : ℂ)‖ ≤ Real.sqrt X * η := by
    rw [hcomplex, hexch, norm_mul, norm_inv]
    have hlen : ‖h‖ = |τ' - τ| := by rw [hh, Complex.norm_real, Real.norm_eq_abs]
    have hpos : 0 < |τ' - τ| := abs_pos.mpr (sub_ne_zero.mpr hne)
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := τ) (b := τ')
      (f := fun σ => ∑ k ∈ S, (((sobWeight r k : ℝ) : ℂ) * (starRingEnd ℂ) (q k)) *
        (G σ k - G τ k)) (C := Real.sqrt X * η) (fun σ hσ => hpt σ (Set.uIoc_subset_uIcc hσ))
    rw [hlen]
    calc (|τ' - τ|)⁻¹ * ‖∫ σ in τ..τ', ∑ k ∈ S, (((sobWeight r k : ℝ) : ℂ) *
          (starRingEnd ℂ) (q k)) * (G σ k - G τ k)‖
        ≤ (|τ' - τ|)⁻¹ * (Real.sqrt X * η * |τ' - τ|) :=
          mul_le_mul_of_nonneg_left this (inv_nonneg.mpr hpos.le)
      _ = Real.sqrt X * η := by field_simp
  have hXn : ‖(X : ℂ)‖ = X := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hX0]
  rw [hXn] at hnorm
  -- X ≤ sqrt X * η  ⇒  X ≤ η²
  have hsq : Real.sqrt X * Real.sqrt X = X := Real.mul_self_sqrt hX0
  have : Real.sqrt X ≤ η := by
    by_cases h0 : Real.sqrt X = 0
    · rw [h0]; exact hη
    · have hp : 0 < Real.sqrt X := lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm h0)
      nlinarith
  nlinarith [Real.sqrt_nonneg X]


theorem diffQuotient_tendsto {r t : ℝ} {F G : ℝ → Coeff d} (hG : ContinuousInHs r G t)
    (hFG : ∀ k, ∀ τ ∈ Set.Icc (0 : ℝ) t, ∀ τ' ∈ Set.Icc (0 : ℝ) t,
      F τ' k - F τ k = ∫ σ in τ..τ', G σ k) :
    ∀ τ ∈ Set.Icc (0 : ℝ) t, Tendsto (fun τ' => hsNorm r (fun k =>
        (F τ' k - F τ k) / ((τ' - τ : ℝ) : ℂ) - G τ k))
      (𝓝[Set.Icc 0 t \ {τ}] τ) (𝓝 0) := by
  intro τ hτ
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  have hG' := Metric.tendsto_nhdsWithin_nhds.mp (hG.2 τ hτ) (ε / 2) (by positivity)
  obtain ⟨δ, hδ, hδ'⟩ := hG'
  refine ⟨δ, hδ, fun τ' hτ'S hdist => ?_⟩
  have hτ'S' : τ' ∈ Set.Icc (0 : ℝ) t := hτ'S.1
  have hne : τ' ≠ τ := hτ'S.2
  have hsup : ∀ σ ∈ Set.uIcc τ τ', hsNormSq r (G σ - G τ) ≤ (ε / 2) ^ 2 := by
    intro σ hσ
    have hσ' : σ ∈ Set.Icc (0 : ℝ) t := Set.uIcc_subset_Icc hτ hτ'S' hσ
    have hd : dist σ τ < δ := by
      rw [Real.dist_eq]
      have := Set.abs_sub_left_of_mem_uIcc hσ
      rw [Real.dist_eq] at hdist
      exact lt_of_le_of_lt this hdist
    have h1 := hδ' hσ' hd
    rw [Real.dist_eq, sub_zero, hsNorm, abs_of_nonneg (Real.sqrt_nonneg _)] at h1
    exact ((Real.sqrt_lt' (by positivity)).mp h1).le
  obtain ⟨-, hq⟩ := quotient_sq_bound hG hFG hτ hτ'S' hne (ε / 2) (by positivity) hsup
  rw [Real.dist_eq, sub_zero, hsNorm, abs_of_nonneg (Real.sqrt_nonneg _)]
  have : Real.sqrt (hsNormSq r (fun k => (F τ' k - F τ k) / ((τ' - τ : ℝ) : ℂ) - G τ k)) ≤ ε / 2 :=
    Real.sqrt_le_iff.mpr ⟨by positivity, hq⟩
  show Real.sqrt _ < ε
  linarith

end HRS.PDE.TRB

namespace HRS.PDE

variable {d : ℕ}

set_option linter.unusedVariables false in
/-- **Time regularity core** (Proposition 3.9 (c)): for a forward solution `F ∈ C_w([0,t];H^m)`
(with `F ∈ C([0,t];H^m)` when `ν > 0`), the generator path `τ ↦ 𝓛^{t-τ}F(τ)` is continuous in
`H^{m-2}` and is the `H^{m-2}`-derivative of `F` (one-sided at the endpoints). -/
theorem forward_time_regularity_core (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (m : ℕ)
    (hm : 1 ≤ m) (R : Regime) (MB Λ VB : ℝ) (D : DynData d) (ν₀ T : ℝ) (μ : ℝ → Torus d → ℝ)
    (hA : AdjointData s m R MB Λ VB D ν₀ T μ) (t : ℝ) (ht : t ∈ Set.Ioc 0 T)
    (φc : Coeff d) (hφ : MemHs m φc) (F : ℝ → Coeff d) (hF : IsForwardSolution D μ t φc F)
    (hw : WeakContinuousInHs m F t) (hstrong : 0 < D.invβ → ContinuousInHs m F t) :
    ContinuousInHs ((m : ℝ) - 2) (fun τ => forwardGen D (μ (t - τ)) (F τ)) t ∧
    ∀ τ ∈ Set.Icc 0 t, Tendsto (fun τ' => hsNorm ((m : ℝ) - 2) (fun k =>
        (F τ' k - F τ k) / ((τ' - τ : ℝ) : ℂ) - forwardGen D (μ (t - τ)) (F τ) k))
      (𝓝[Set.Icc 0 t \ {τ}] τ) (𝓝 0) := by
  have hG := TRB.gen_continuousInHs hd hs0 hsd hm hA ht hw hstrong
  refine ⟨hG, TRB.diffQuotient_tendsto hG ?_⟩
  intro k τ hτ τ' hτ'
  have hint : ∀ u ∈ Set.Icc (0 : ℝ) t, IntervalIntegrable
      (fun σ => forwardGen D (μ (t - σ)) (F σ) k) MeasureTheory.volume 0 u := fun u hu =>
    ((TRB.gen_coord_continuousOn_weak hd hs0 hsd hm hA ht hw k).mono
      (Set.uIcc_subset_Icc ⟨le_rfl, ht.1.le⟩ hu)).intervalIntegrable
  rw [hF.eq k τ hτ, hF.eq k τ' hτ']
  rw [add_sub_add_left_eq_sub, intervalIntegral.integral_interval_sub_left (hint τ' hτ') (hint τ hτ)]

end HRS.PDE
