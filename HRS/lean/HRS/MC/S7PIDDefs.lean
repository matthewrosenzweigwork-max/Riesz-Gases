import HRS.MC.S7PIE

/-!
# Packet PI-D: sorry-free vocabulary for the split of `s7_PI_D_J_exists` (`HRS/MC/S7PIDPlan.lean`)

Nothing here is a statement about the dynamics.  The objects:

* `modeVec m k`: the basis vector `e_k` of `E_m` (`eval (modeVec m k) ψ = ψ̂(k)`);
* `causalVec D ρ m t u e = 1_{u ≤ t} V^{t,u} e`: the DISCONTINUOUS causal kernel (it jumps at `t = u`, so it is NOT a
  path in `𝒳 = C([0,T];E_m)`; this is why `J` cannot be a Bochner integral in `u` of elementary tensors, TeX L8609-8613);
* `polyPath .. c c' n v`: the continuous path of `𝒳` which is the polygonal interpolation of the node values
  `v 0, …, v (2^n)` at the nodes `gridPt c c' n i = c + (c'-c) i / 2^n` of `[c,c']`, constant `= v 0` before `c`, and
  propagated by `V^{t,c'}` after `c'`;
* `nuc .. n w w' = ∫_{(c,c']} (polyPath (w u)) ⊗ (polyPath (w' u)) du`: the time-smoothed nuclear tensor.  It is a
  Bochner integral in `u` of continuous-path elementary tensors, with norm `≤ ∫ ‖w u‖ ‖w' u‖` but NOT uniformly
  Cauchy in the projective norm in `n` for that reason; the Gaussian estimate of `S7PIDPlan` is what gives the Cauchy
  property (`‖nuc_{n+1} - nuc_n‖ ≤ C 2^{-n/4}`).
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.PID

open HRS HRS.Sec7

variable {d : ℕ}

/-- The basis vector `e_k` of `E_m`: `fourierCoeff (modeVec m k) j = δ_{jk}`. -/
def modeVec (m : ℝ) (k : NonzeroLattice d) : NegSobolev d m :=
  NegSobolev.ofSeq m fun j => if j = k then 1 else 0

/-- The `E_s`-norm of the element of `E_m` with the same Fourier coefficients (`0` if they are not in `E_s`). -/
def sobAt (s : ℝ) {m : ℝ} (F : NegSobolev d m) : ℝ :=
  ‖(NegSobolev.ofSeq s fun k => NegSobolev.fourierCoeff F k : NegSobolev d s)‖

/-- The causal kernel `1_{u ≤ t} V^{t,u} e` (a vector of `E_m`; discontinuous in `t` at `t = u`). -/
def causalVec (D : DynData d) (ρ : ℝ → Torus d → ℝ) (m t u : ℝ) (e : NegSobolev d m) : NegSobolev d m :=
  if u ≤ t then Vprop D ρ m t u e else 0

/-- The `i`-th dyadic node of `[c,c']` at level `n`. -/
def gridPt (c c' : ℝ) (n i : ℕ) : ℝ := c + (c' - c) * i / 2 ^ n

/-- Polygonal interpolation of node values `v i` at level `n` of `[c,c']` (clamped outside `[c,c']`). -/
def polyAt {E : Type*} [AddCommGroup E] [Module ℝ E] (c c' : ℝ) (n : ℕ) (v : ℕ → E) (t : ℝ) : E :=
  ∑ i ∈ Finset.range (2 ^ n + 1),
    max 0 (1 - |(max c (min t c') - c) / (c' - c) * 2 ^ n - i|) • v i

/-- The element of `𝒳_{m,T}` given by the polygonal interpolation of the node values `v 0, …, v (2^n)` on `[c,c']`,
`v 0` before `c`, and `V^{t,c'} (v (2^n))` after `c'` (continuous by the strong continuity of `V`, PI-E). -/
def polyPath (D : DynData d) (ρ : ℝ → Torus d → ℝ) (m T c c' : ℝ) (n : ℕ) (v : ℕ → NegSobolev d m) :
    PathSpace d m T :=
  pathOf m T fun t => if t ≤ c' then polyAt c c' n v t else Vprop D ρ m t c' (v (2 ^ n))

/-- The time-smoothed nuclear tensor `∫_{(c,c']} polyPath(w u) ⊗ polyPath(w' u) du` (Bochner integral in
`TensorDual 𝒳 2`; `0` if not integrable, integrability is part of `s7_PID_nuc_mem`). -/
def nuc (D : DynData d) (ρ : ℝ → Torus d → ℝ) (m T c c' : ℝ) (n : ℕ) (w w' : ℝ → ℕ → NegSobolev d m) :
    TensorDual (PathSpace d m T) 2 :=
  ∫ u in Set.Ioc c c', elemTensor ![polyPath D ρ m T c c' n (w u), polyPath D ρ m T c c' n (w' u)]

/-- The node vectors of the causal kernel `p(u) · 1_{u ≤ t_i} V^{t_i,u} e`. -/
def kernelNodes (D : DynData d) (ρ : ℝ → Torus d → ℝ) (m c c' : ℝ) (n : ℕ) (p : ℝ → ℝ) (e : NegSobolev d m)
    (u : ℝ) (i : ℕ) : NegSobolev d m :=
  p u • causalVec D ρ m (gridPt c c' n i) u e

/-- The coordinate truncation `Π_F` of `E_m` to the finite set `F` of modes. -/
def truncF (m : ℝ) (F : Finset (NonzeroLattice d)) (v : NegSobolev d m) : NegSobolev d m :=
  NegSobolev.ofSeq m fun k => if k ∈ F then NegSobolev.fourierCoeff v k else 0

/-- The bilinear form `(w₁, w₂) ↦ l₁ w₁ · l₂ w₂`, i.e. the pairing partner of `ℓ₁ ⊗ ℓ₂` (as in `IsJValue`). -/
def prodForm {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B] (l₁ l₂ : StrongDual ℝ B) : B [×2]→L[ℝ] ℝ :=
  (ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin 2) ℝ).compContinuousLinearMap ![l₁, l₂]

/-- The Fourier product `∇e_k · ∇e_l` of two real modes. -/
def gradProd (k l : NonzeroLattice d) : Torus d → ℝ :=
  fun x => inner ℝ (Torus.grad (Torus.realMode k) x) (Torus.grad (Torus.realMode l) x)

end HRS.MC.Sec7.PID

end
