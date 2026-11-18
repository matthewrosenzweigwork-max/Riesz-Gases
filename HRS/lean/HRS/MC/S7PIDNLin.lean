import HRS.MC.S7PIDPPoly

/-!
# Packet PI-D, sub-packet N (part 1): `polyPath` is a Lipschitz function of its finite node family

Route note for `s7_PID_nuc_mem` (D4b):
1. The integrand is `u ↦ elemTensor ![polyPath (w u), polyPath (w' u)]` in `TensorDual 𝒳 2`, a NON-separable Banach space,
   so Pettis on `TensorDual` is useless; instead we factor the integrand through a continuous map out of a separable space.
2. For `c < c'`, `polyPath v` depends only on the finitely many nodes `v 0, …, v (2^n)` (`S7PIDN_polyPath_congr`), and
   `v ↦ polyPath v` is linear (`V^{t,c'}` is linear, `S7PIDN_polyPath_sub`), bounded by `C₁ max ‖v i‖` (`s7_PID_poly_proof`);
   hence `Φ : (Fin (2^n+1) → E_m) → 𝒳` is Lipschitz, in particular continuous (`S7PIDN_Phi_lip`).
3. `(Fin N → E_m)` is second countable (`E_m` is), so `u ↦ (w u i)_i` is strongly measurable (Borel measurable into a second
   countable space); then `u ↦ Φ(w u)` is strongly measurable by continuity of `Φ` (no separability of `𝒳` needed).
4. `elemTensor ![·,·] : 𝒳 × 𝒳 → TensorDual 𝒳 2` is continuous (`S7PIDN_elem_sub_le`), so the integrand is strongly measurable;
   it is bounded by `(C₁ b)²` (`‖elemTensor ![a,b]‖ ≤ ‖a‖‖b‖`), hence integrable on the finite measure `vol|_{(c,c']}`.
5. Membership in the closed submodule `projTensor`: every `elemTensor v` lies in it; the average of an integrable function with
   values in a closed convex set lies in the set (`Convex.average_mem`), and `∫ = vol(I) • ⨍`.
(The degenerate case `c = c'` has `Ioc c c' = ∅`: integral `0`.)
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.S7PIDN

open HRS HRS.Sec7 HRS.MC.Sec7.PID HRS.MC.Sec7.PIE

variable {d : ℕ}

/-- linearity of `V^{t,u}` on `E_m` for `0 < t ≤ T`, `0 ≤ u ≤ t` (the finite-section bounds at the real level `m`) -/
theorem S7PIDN_Vprop_sub {J : ℕ} {D : DynData d} {μ : ℝ → Torus d → ℝ} {T : ℝ} (H : PIEHyp J D μ T)
    (m : ℝ) (n₀ : ℕ) (hn₀ : 1 ≤ n₀) (hJ : n₀ + 1 ≤ J) (hm0 : (n₀ : ℝ) < m) (hm1 : m ≤ n₀ + 1) :
    ∀ t ∈ Set.Ioc 0 T, ∀ u ∈ Set.Icc 0 t, ∀ F G : NegSobolev d m,
      Vprop D μ m t u (F - G) = Vprop D μ m t u F - Vprop D μ m t u G := by
  obtain ⟨C0, hC0, h0⟩ := pie_finBd H n₀ hn₀ (by omega)
  obtain ⟨C1, hC1, h1⟩ := pie_finBd H (n₀ + 1) (by omega) hJ
  set θ : ℝ := m - n₀ with hθ
  have hθ0 : 0 ≤ θ := by linarith
  have hθ1 : θ ≤ 1 := by linarith
  intro t ht u hu F G
  have hw : ∀ k : NonzeroLattice d, 0 < Lattice.jp k.1 := fun k => Torus.jp_pos k.1
  have hint := pie_interp hw (T := pieT D μ u t) hC0 hC1 (h0 t ht u hu)
    (by simpa using h1 t ht u hu) hθ0 hθ1
  have hσ : (1 - θ) * (n₀ : ℝ) + θ * ((n₀ : ℝ) + 1) = m := by
    simp only [hθ]; ring
  rw [hσ] at hint
  exact pie_Vprop_sub D μ m t u (mul_nonneg (Real.rpow_nonneg hC0 _) (Real.rpow_nonneg hC1 _)) hint F G

/-- `polyAt` is additive in the node family -/
theorem S7PIDN_polyAt_sub {m : ℝ} (c c' : ℝ) (n : ℕ) (v v' : ℕ → NegSobolev d m) (t : ℝ) :
    PID.polyAt c c' n (fun i => v i - v' i) t = PID.polyAt c c' n v t - PID.polyAt c c' n v' t := by
  unfold PID.polyAt
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ => smul_sub _ _ _

/-- `polyPath` depends only on the nodes `v 0, …, v (2^n)` -/
theorem S7PIDN_polyPath_congr (D : DynData d) (ρ : ℝ → Torus d → ℝ) (m T c c' : ℝ) (n : ℕ)
    (v v' : ℕ → NegSobolev d m) (h : ∀ i ≤ 2 ^ n, v i = v' i) :
    polyPath D ρ m T c c' n v = polyPath D ρ m T c c' n v' := by
  unfold polyPath
  congr 1
  funext t
  split_ifs with ht
  · unfold PID.polyAt
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [h i (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi))]
  · rw [h (2 ^ n) le_rfl]

/-- the evaluation of `pathAt` at a point of `[0,T]` is the value of the underlying continuous map -/
theorem S7PIDN_pathAt_eq {m T : ℝ} (w : PathSpace d m T) (t : Set.Icc (0 : ℝ) T) :
    pathAt w t.1 = (show C(Set.Icc (0 : ℝ) T, NegSobolev d m) from w) t := by
  unfold pathAt PathSpace.at'
  rw [dif_pos t.2]

/-- `polyPath` is additive in the node family (case `c < c'`): `polyPath v - polyPath v' = polyPath (v - v')`. -/
theorem S7PIDN_polyPath_sub (R : Regime d) (m : ℝ) (hm : 3 * (d : ℝ) + 8 < m) (T : ℝ) (hT : 0 < T)
    (c c' : ℝ) (hc : 0 ≤ c) (hcc : c < c') (hc' : c' ≤ T) (n : ℕ) (v v' : ℕ → NegSobolev d m) :
    polyPath R.D R.ρ m T c c' n v - polyPath R.D R.ρ m T c c' n v' =
      polyPath R.D R.ρ m T c c' n (fun i => v i - v' i) := by
  obtain ⟨J, n₀, H, hn₀, hJ, hm0, hm1⟩ := S7PIDP.S7PIDP_pie R m hm T hT
  have hlin := S7PIDN_Vprop_sub H m n₀ hn₀ hJ hm0 hm1
  have hcont := fun (u : ℕ → NegSobolev d m) => S7PIDP.S7PIDP_cont H hn₀ hJ hm0 hm1 c c' hc hcc hc' n u
  refine ContinuousMap.ext fun x => ?_
  have e1 := S7PIDN_pathAt_eq (polyPath R.D R.ρ m T c c' n v) x
  have e2 := S7PIDN_pathAt_eq (polyPath R.D R.ρ m T c c' n v') x
  have e3 := S7PIDN_pathAt_eq (polyPath R.D R.ρ m T c c' n (fun i => v i - v' i)) x
  have a1 := S7PIDP.S7PIDP_pathAt_cont (g := fun t : ℝ => if t ≤ c' then PID.polyAt c c' n v t else Vprop R.D R.ρ m t c' (v (2 ^ n))) (hcont v) x.1 x.2
  have a2 := S7PIDP.S7PIDP_pathAt_cont (g := fun t : ℝ => if t ≤ c' then PID.polyAt c c' n v' t else Vprop R.D R.ρ m t c' (v' (2 ^ n))) (hcont v') x.1 x.2
  have a3 := S7PIDP.S7PIDP_pathAt_cont (g := fun t : ℝ => if t ≤ c' then PID.polyAt c c' n (fun i => v i - v' i) t else Vprop R.D R.ρ m t c' ((fun i => v i - v' i) (2 ^ n))) (hcont (fun i => v i - v' i)) x.1 x.2
  have ep : ∀ u : ℕ → NegSobolev d m, polyPath R.D R.ρ m T c c' n u =
      pathOf m T fun t => if t ≤ c' then PID.polyAt c c' n u t else Vprop R.D R.ρ m t c' (u (2 ^ n)) :=
    fun u => rfl
  rw [ep] at e1 e2 e3
  show (show C(Set.Icc (0 : ℝ) T, NegSobolev d m) from polyPath R.D R.ρ m T c c' n v) x -
      (show C(Set.Icc (0 : ℝ) T, NegSobolev d m) from polyPath R.D R.ρ m T c c' n v') x =
      (show C(Set.Icc (0 : ℝ) T, NegSobolev d m) from
        polyPath R.D R.ρ m T c c' n (fun i => v i - v' i)) x
  rw [← S7PIDN_pathAt_eq, ← S7PIDN_pathAt_eq, ← S7PIDN_pathAt_eq]
  rw [ep, ep, ep, a1, a2, a3]
  dsimp only
  split_ifs with h
  · exact (S7PIDN_polyAt_sub c c' n v v' x.1).symm
  · have ht : x.1 ∈ Set.Ioc 0 T := ⟨lt_of_le_of_lt (hc.trans hcc.le) (not_le.1 h), x.2.2⟩
    exact (hlin x.1 ht c' ⟨hc.trans hcc.le, (not_le.1 h).le⟩ (v (2 ^ n)) (v' (2 ^ n))).symm

/-- the node-family map `Φ : (Fin (2^n+1) → E_m) → 𝒳` -/
def S7PIDN_Phi (D : DynData d) (ρ : ℝ → Torus d → ℝ) (m T c c' : ℝ) (n : ℕ)
    (x : Fin (2 ^ n + 1) → NegSobolev d m) : PathSpace d m T :=
  polyPath D ρ m T c c' n fun i => if h : i < 2 ^ n + 1 then x ⟨i, h⟩ else 0

theorem S7PIDN_Phi_eq (D : DynData d) (ρ : ℝ → Torus d → ℝ) (m T c c' : ℝ) (n : ℕ)
    (v : ℕ → NegSobolev d m) :
    polyPath D ρ m T c c' n v = S7PIDN_Phi D ρ m T c c' n fun i => v i.1 := by
  unfold S7PIDN_Phi
  refine S7PIDN_polyPath_congr D ρ m T c c' n _ _ fun i hi => ?_
  rw [dif_pos (Nat.lt_succ_of_le hi)]

/-- `Φ` is Lipschitz (constant `C₁` of `s7_PID_poly_proof`), for `c < c'` -/
theorem S7PIDN_Phi_lip (R : Regime d) (m : ℝ) (hm : 3 * (d : ℝ) + 8 < m) (T : ℝ) (hT : 0 < T) :
    ∃ C₁ : ℝ, 1 ≤ C₁ ∧ ∀ c c' : ℝ, 0 ≤ c → c < c' → c' ≤ T → ∀ n : ℕ,
      ∀ x y : Fin (2 ^ n + 1) → NegSobolev d m,
        ‖S7PIDN_Phi R.D R.ρ m T c c' n x - S7PIDN_Phi R.D R.ρ m T c c' n y‖ ≤ C₁ * ‖x - y‖ := by
  obtain ⟨C₁, hC₁, hC⟩ := S7PIDP.s7_PID_poly_proof R m hm T hT
  refine ⟨C₁, hC₁, fun c c' hc hcc hc' n x y => ?_⟩
  unfold S7PIDN_Phi
  rw [S7PIDN_polyPath_sub R m hm T hT c c' hc hcc hc']
  refine (hC c c' hc hcc.le hc' n _).2.1 ‖x - y‖ fun i hi => ?_
  rw [dif_pos (Nat.lt_succ_of_le hi), dif_pos (Nat.lt_succ_of_le hi)]
  exact norm_le_pi_norm (x - y) ⟨i, Nat.lt_succ_of_le hi⟩

end HRS.MC.Sec7.S7PIDN

end
