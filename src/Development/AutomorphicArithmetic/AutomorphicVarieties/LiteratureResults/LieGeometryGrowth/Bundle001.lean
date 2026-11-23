module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PairFactsAlt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.L2Cusps.BrCusp
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.CuspFormsSiegel
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.SummandsAreCuspForms
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

@[expose] public section

section

noncomputable section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.Lit UpperTheory.V.Lit.Dr UpperTheory.V.Lit.Geo
open scoped TensorProduct

section

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

private theorem chart_prod (f h : GA E a → ℂ) (g : GA E a) :
    chart (fun x => f x * h x) g = fun y => chart f g y * chart h g y := by
  funext y
  unfold chart
  split_ifs <;> simp

private def mulOp (u : Sm E a) : Module.End ℂ (Sm E a) where
  toFun φ := ⟨fun x => u.1 x * φ.1 x, fun g => by
    rw [chart_prod]
    exact (u.2 g).mul (φ.2 g)⟩
  map_add' φ ψ := Subtype.ext (funext fun x => mul_add _ _ _)
  map_smul' c φ := Subtype.ext (funext fun x => mul_left_comm _ c _)

private theorem mulOp_apply (u φ : Sm E a) (g : GA E a) : (mulOp u φ).1 g = u.1 g * φ.1 g := rfl

private theorem lie_mulOp (X : Lie E a) (u φ : Sm E a) :
    lie E a X (mulOp u φ) = mulOp u (lie E a X φ) + mulOp (lie E a X u) φ := by
  refine Subtype.ext (funext fun g => ?_)
  have hv : ∀ f : GA E a → ℂ, chart f g (oneL E a) = f g := fun f => by
    simpa using chart_val f g 1
  change fderiv ℝ (chart (fun x => u.1 x * φ.1 x) g) (oneL E a) X =
    u.1 g * fderiv ℝ (chart φ.1 g) (oneL E a) X + fderiv ℝ (chart u.1 g) (oneL E a) X * φ.1 g
  rw [chart_prod, fderiv_fun_mul (differentiableAt_chart u.2 g) (differentiableAt_chart φ.2 g), hv, hv]
  simp [mul_comm]

private theorem ev_mulOp {d : ℕ} (u : Sm E a) (m : Sm E a ⊗[ℂ] (Fin d → ℂ)) (g : GA E a) :
    ev ((mulOp u).rTensor _ m) g = u.1 g • ev m g := by
  induction m using TensorProduct.induction_on with
  | zero => simp
  | tmul φ v => rw [LinearMap.rTensor_tmul, ev_tmul, ev_tmul, mulOp_apply, mul_smul]
  | add x y hx hy => simp only [map_add (f := _), Pi.add_apply, hx, hy, smul_add]

private theorem smLie_mulOp (Ξ : AlgRep E a) (X : Lie E a) (u : Sm E a) (m : Sm E a ⊗[ℂ] (Fin Ξ.d → ℂ)) :
    smLie Ξ X ((mulOp u).rTensor _ m) =
      (mulOp u).rTensor _ (smLie Ξ X m) + (mulOp (lie E a X u)).rTensor _ m := by
  induction m using TensorProduct.induction_on with
  | zero => simp
  | tmul φ v =>
    change lie E a X (mulOp u φ) ⊗ₜ[ℂ] v + mulOp u φ ⊗ₜ[ℂ] (Ξ.dmat X *ᵥ v) =
      (mulOp u).rTensor _ (lie E a X φ ⊗ₜ[ℂ] v + φ ⊗ₜ[ℂ] (Ξ.dmat X *ᵥ v)) + mulOp (lie E a X u) φ ⊗ₜ[ℂ] v
    rw [lie_mulOp, map_add (f := _), LinearMap.rTensor_tmul, LinearMap.rTensor_tmul, TensorProduct.add_tmul]
    abel
  | add x y hx hy => simp only [map_add (f := _), hx, hy]; abel

private theorem smK_mulOp (Ξ : AlgRep E a) (k : Kinf E a) (u : Sm E a) (hu : act (.cpt k) u = u)
    (m : Sm E a ⊗[ℂ] (Fin Ξ.d → ℂ)) :
    smK Ξ k ((mulOp u).rTensor _ m) = (mulOp u).rTensor _ (smK Ξ k m) := by
  induction m using TensorProduct.induction_on with
  | zero => simp
  | tmul φ v =>
    have h : act (.cpt k) (mulOp u φ) = mulOp (act (.cpt k) u) (act (.cpt k) φ) := rfl
    simp only [smK, LinearMap.rTensor_tmul, TensorProduct.map_tmul, h, hu]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

private theorem lie_one_eq_zero (u : Sm E a) (hu : ∀ t g, u.1 (GlobalTheory.UnitaryBC.splitCentre E a t * g) = u.1 g) :
    lie E a (oneL E a) u = 0 := by
  refine Subtype.ext (funext fun g => ?_)
  let c : ℝ → GL (Fin a) (Cinf E) := fun t =>
    Units.map (Matrix.scalar (Fin a)).toMonoidHom (expU fun _ : InfinitePlace E => (t : ℂ))
  have hc : ∀ t, infGL E a (c t) = GlobalTheory.UnitaryBC.splitCentre E a t := fun _ => rfl
  have hval : ∀ t : ℝ, toL (c t).val = Complex.exp t • oneL E a := fun t => by
    ext i j w
    by_cases h : i = j <;> simp [c, expU, toL, oneL, h, Matrix.scalar_apply, Matrix.one_apply, Matrix.diagonal_apply]
  have h0 : c 0 = 1 := Units.ext (by
    have h := hval 0
    rw [Complex.ofReal_zero, Complex.exp_zero, one_smul] at h
    exact h)
  have hd : HasDerivAt (fun t => toL (c t).val) (oneL E a) 0 := by
    simp only [hval]
    simpa using ((Complex.hasDerivAt_exp ((0 : ℝ) : ℂ)).comp_ofReal).smul_const (oneL E a)
  have h1 := GlobalTheory.CuspRep.hasDerivAt_curve u g c _ h0 hd
  simp only [hc, ← CuspidalL2GL.splitCentre_comm, hu] at h1
  exact h1.unique (hasDerivAt_const _ _)

private theorem levelFn_mulOp {U : Subgroup (GL (Fin a) (Af E))} {Ξ : AlgRep E a} {u φ : Sm E a} (hu : IsCut U u)
    (hφ : IsLevelFn U Ξ φ) : IsLevelFn U Ξ (mulOp u φ) := by
  refine ⟨fun γ g => ?_, fun k hk => ?_, fun m hm => ?_⟩
  · rw [mulOp_apply, mulOp_apply, hu.left, hφ.1]
  · have h : act (.fin k) (mulOp u φ) = mulOp (act (.fin k) u) (act (.fin k) φ) := rfl
    rw [h, hu.level k hk, hφ.2.1 k hk]
  · have h : mulOp (0 : Sm E a) φ = 0 := Subtype.ext (funext fun x => zero_mul _)
    rw [lie_mulOp, lie_one_eq_zero u hu.centre, h, add_zero, hφ.2.2 m hm, map_smul]

private theorem ev_dCo (Ξ : AlgRep E a) {q : ℕ} (ω : Co Ξ q) (X : Fin (q + 1) → Herm E a) (g : GA E a) :
    ev (dCo (smLie Ξ) ω X) g =
      ∑ i : Fin (q + 1), (-1 : ℂ) ^ (i : ℕ) • ev (smLie Ξ (toL (X i).1) (ω (i.removeNth X))) g := by

  rw [dCo, AlternatingMap.alternatizeUncurryFin_apply, map_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_zsmul, Pi.smul_apply, ← Int.cast_smul_eq_zsmul ℂ]
  push_cast
  rfl

end

theorem UpperTheory.V.Lit.Geo.mulEx :
    MulEx := by
  intro E _ _ _ a U Ξ q u α hu hα
  refine ⟨(((mulOp u).rTensor (Fin Ξ.d → ℂ)).restrictScalars ℝ).compAlternatingMap α,
    ⟨fun k => ?_, fun X i hi => ?_, fun X => ?_⟩, fun X g => ev_mulOp u (α X) g, fun X g => ?_⟩
  · intro X
    change (mulOp u).rTensor _ (α _) = smK Ξ k ((mulOp u).rTensor _ (α X))
    rw [smK_mulOp Ξ k u (hu.cpt k), hα.equiv k X]
  · change (mulOp u).rTensor _ (α X) = 0
    rw [hα.basic X i hi, map_zero]
  · change (mulOp u).rTensor _ (α X) ∈ _
    refine Submodule.span_induction (p := fun m _ => (mulOp u).rTensor _ m ∈ _) ?_ ?_ ?_ ?_ (hα.val X)
    · rintro _ ⟨φ, v, hφ, rfl⟩
      exact Submodule.subset_span ⟨_, v, levelFn_mulOp hu hφ, LinearMap.rTensor_tmul _ _ _ _⟩
    · rw [map_zero]; exact Submodule.zero_mem _
    · intro x y _ _ hx hy
      rw [map_add (f := _)]; exact Submodule.add_mem _ hx hy
    · intro c x _ hx
      rw [map_smul]; exact Submodule.smul_mem _ c hx
  · rw [ev_dCo, ev_dCo, Finset.smul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    change _ • ev (smLie Ξ _ ((mulOp u).rTensor _ (α _))) g = _
    rw [smLie_mulOp, map_add (f := _), Pi.add_apply, ev_mulOp, ev_mulOp, smul_add, smul_comm, mul_smul]
end
end

section

noncomputable section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af GlobalTheory.UnitaryBC UpperTheory.V.Lit.Dr UpperTheory.V.Lit.Bor

namespace UpperTheory.V.Lit.Geo

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

def BddDer (φ : Sm E a) : Prop :=
  ∀ (X : Lie E a) (l : List (Lie E a)), ∃ C : ℝ, ∀ g, ‖(((X :: l).map (lie E a)).prod φ).1 g‖ ≤ C

structure IsStep (U : Subgroup (GL (Fin a) (Af E))) (f : GA E a → ℝ) (Y : GA E a → Herm E a) (C c f₀ : ℝ) : Prop where
  c_pos : 0 < c
  f_sm : ∃ φ : Sm E a, (∀ g, φ.1 g = f g) ∧ BddDer φ
  f_left : ∀ γ t g, f (ratGL E a γ * splitCentre E a t * g) = f g
  f_cpt : ∀ (k : Kinf E a) g, f (g * infGL E a (Unitary.toUnits k)) = f g
  f_lev : ∀ u ∈ U, ∀ g, f (g * finGL E a u) = f g
  f_nonneg : ∀ g, 0 ≤ f g
  f_le : ∀ g, f g ≤ C * (1 + Real.log (qht g))
  le_f : ∀ g, Real.log (qht g) ≤ C * (1 + f g)
  Y_sm : ∀ i j w, ∃ φ : Sm E a, (∀ g, φ.1 g = (Y g).1 i j w) ∧ BddDer φ
  Y_left : ∀ γ t g, Y (ratGL E a γ * splitCentre E a t * g) = Y g
  Y_cpt : ∀ (k : Kinf E a) g, adHerm k (Y (g * infGL E a (Unitary.toUnits k))) = Y g
  Y_lev : ∀ u ∈ U, ∀ g, Y (g * finGL E a u) = Y g
  root : ∀ g (t : ℝ), |t| ≤ 1 → ∃ h : GL (Fin a) (Cinf E), h.val * star h.val = 1 + t • (Y g).1 ∧
    ‖toL h.val‖ ≤ C ∧ ‖toL (h⁻¹).val‖ ≤ C
  up : ∀ g (h : GL (Fin a) (Cinf E)), f₀ ≤ f g → h.val * star h.val = 1 + (Y g).1 → f g + c ≤ f (g * infGL E a h)
  down : ∀ g (h : GL (Fin a) (Cinf E)), f₀ ≤ f g → h.val * star h.val = 1 - (Y g).1 → f (g * infGL E a h) ≤ f g - c
  near : ∀ g (t : ℝ) (h : GL (Fin a) (Cinf E)), |t| ≤ 1 → h.val * star h.val = 1 + t • (Y g).1 →
    |f (g * infGL E a h) - f g| ≤ C

def StepEx : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ), 1 ≤ a → ∀ U : Subgroup (GL (Fin a) (Af E)),
    IsCompact (U : Set (GL (Fin a) (Af E))) → ∃ f Y C c f₀, IsStep U f Y C c f₀

end UpperTheory.V.Lit.Geo
end
end

section

noncomputable section

open NumberField Matrix MeasureTheory Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af GlobalTheory.UnitaryBC
open UpperTheory.V.Lit.Dr UpperTheory.V.Lit.Bor
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL

namespace UpperTheory.V.Lit.Geo.Pf

section Defs

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

structure CInv (F : GA E a → ℂ) : Prop where
  cont : Continuous F
  left : ∀ γ g, F (ratGL E a γ * g) = F g
  centre : ∀ t g, F (splitCentre E a t * g) = F g

structure SInv (φ : Sm E a) : Prop where
  left : ∀ γ g, φ.1 (ratGL E a γ * g) = φ.1 g
  centre : ∀ t g, φ.1 (splitCentre E a t * g) = φ.1 g
  level : IsOpen {k | act (.fin k) φ = φ}

def Cs {M : Type} [Zero M] (F : GA E a → M) : Prop := ∃ R : ℝ, ∀ g, R < qht g → F g = 0

def QInt (μ : Measure (GA E a)) (F : GA E a → ℂ) : Prop :=
  Integrable (fun x : GlobalTheory.AutomorphicL2Unitary.Quot (latticeGL E a) => F x.out) (GlobalTheory.AutomorphicL2Unitary.quotMeasure (latticeGL E a) μ)

def qint (μ : Measure (GA E a)) (F : GA E a → ℂ) : ℂ :=
  ∫ x : GlobalTheory.AutomorphicL2Unitary.Quot (latticeGL E a), F x.out ∂(GlobalTheory.AutomorphicL2Unitary.quotMeasure (latticeGL E a) μ)

def TwInv (χ : HChar E) {d : ℕ} (m : Sm E a ⊗[ℂ] (Fin d → ℂ)) : Prop := ∀ j, SInv (mulChi a χ (cmp j m))

def pt (χ : HChar E) {d : ℕ} (G : Matrix (Fin d) (Fin d) ℂ) (x y : Sm E a ⊗[ℂ] (Fin d → ℂ)) (g : GA E a) : ℂ :=
  (‖((chiDet a χ g : ℂˣ) : ℂ)‖ ^ 2 : ℝ) * (star (ev x g) ⬝ᵥ G *ᵥ ev y g)

theorem cmp_ev {d : ℕ} (m : Sm E a ⊗[ℂ] (Fin d → ℂ)) (j : Fin d) (g : GA E a) : (cmp j m).1 g = ev m g j := by
  induction m using TensorProduct.inductionOn with
  | tmul φ v => simp [mul_comm]
  | add x y hx hy => simp [hx, hy]

theorem ptIp_eq {Ξ : AlgRep E a} {q : ℕ} (χ : HChar E) (G : Matrix (Fin Ξ.d) (Fin Ξ.d) ℂ) {n : ℕ} (e : Fin n → Herm E a)
    (α β : Co Ξ q) (g : GA E a) :
    ptIp χ G e α β g = ∑ I : Fin q → Fin n, pt χ G (α fun i => e (I i)) (β fun i => e (I i)) g := by
  simp only [ptIp, pt, Finset.mul_sum]

theorem CInv.sum {ι : Type} (s : Finset ι) {F : ι → GA E a → ℂ} (h : ∀ i, CInv (F i)) : CInv fun g => ∑ i ∈ s, F i g :=
  ⟨continuous_finsetSum _ fun i _ => (h i).cont, fun γ g => Finset.sum_congr rfl fun i _ => (h i).left γ g,
    fun t g => Finset.sum_congr rfl fun i _ => (h i).centre t g⟩

theorem cs_pt_left (χ : HChar E) {d : ℕ} (G : Matrix (Fin d) (Fin d) ℂ) {x : Sm E a ⊗[ℂ] (Fin d → ℂ)} (y : Sm E a ⊗[ℂ] (Fin d → ℂ))
    (h : Cs (ev x)) : Cs (pt χ G x y) :=
  h.imp fun _ hR g hg => by simp [pt, hR g hg]

theorem cs_pt_right (χ : HChar E) {d : ℕ} (G : Matrix (Fin d) (Fin d) ℂ) (x : Sm E a ⊗[ℂ] (Fin d → ℂ)) {y : Sm E a ⊗[ℂ] (Fin d → ℂ)}
    (h : Cs (ev y)) : Cs (pt χ G x y) :=
  h.imp fun _ hR g hg => by simp [pt, hR g hg]

end Defs

def InvLie : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (φ : Sm E a), SInv φ →
    CInv φ.1 ∧ ∀ X : Lie E a, SInv (lie E a X φ)

def BddInt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (μ : Measure (GA E a)) [μ.IsHaarMeasure]
    (F : GA E a → ℂ), CInv F → (∃ C : ℝ, ∀ g, ‖F g‖ ≤ C) → QInt μ F ∧ GlobalTheory.AutomorphicL2Unitary.MemL2Quotient (latticeGL E a) μ F

def CsBdd : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (F : GA E a → ℂ), CInv F →
    (Cs F ∨ ∃ C : ℝ, ∀ g : KernelIndexFullLattice.G1 E a, ‖F g.1‖ ≤ C) → ∃ C : ℝ, ∀ g, ‖F g‖ ≤ C

def CsLie : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (φ : Sm E a) (X : Lie E a), Cs φ.1 → Cs (lie E a X φ).1

def ProdEx : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (φ ψ : Sm E a), ∃ θ : Sm E a,
    (∀ g, θ.1 g = starRingEnd ℂ (φ.1 g) * ψ.1 g) ∧
    ∀ (X : Lie E a) g, (lie E a X θ).1 g =
      starRingEnd ℂ ((lie E a X φ).1 g) * ψ.1 g + starRingEnd ℂ (φ.1 g) * (lie E a X ψ).1 g

def StokesFn : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (μ : Measure (GA E a)) [μ.IsHaarMeasure]
    (θ : Sm E a) (X : Lie E a), SInv θ → Cs θ.1 → qint μ (lie E a X θ).1 = 0

def LevInv : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ), 1 ≤ a → ∀ (U : Subgroup (GL (Fin a) (Af E))),
    IsOpen (U : Set (GL (Fin a) (Af E))) → ∀ (Ξ : AlgRep E a) (r : ℝ) (χ : HChar E), HasOne Ξ r → IsTw (a := a) r χ →
    ∀ (q : ℕ) (α : Co Ξ q), IsLev U Ξ α → ∀ X, TwInv χ (α X)

def PtInv : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (χ : HChar E) (d : ℕ) (G : Matrix (Fin d) (Fin d) ℂ)
    (x y : Sm E a ⊗[ℂ] (Fin d → ℂ)),
    (∀ g, pt χ G x y g = ∑ i, ∑ j, G i j *
      (starRingEnd ℂ ((mulChi a χ (cmp i x)).1 g) * (mulChi a χ (cmp j y)).1 g)) ∧
    ((TwInv χ x → TwInv χ y → CInv (pt χ G x y)) ∧
      ∀ θ : Sm E a, (∀ g, θ.1 g = pt χ G x y g) → TwInv χ x → TwInv χ y → SInv θ)

def TwLie : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (Ξ : AlgRep E a) (r : ℝ) (χ : HChar E),
    IsTw (a := a) r χ → ∀ (X : Lie E a) (x : Sm E a ⊗[ℂ] (Fin Ξ.d → ℂ)), TwInv χ x →
      TwInv χ (smLie Ξ X x) ∧ TwInv χ (smAdj Ξ r X x)

def CsTens : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (Ξ : AlgRep E a) (r : ℝ) (X : Lie E a)
    (x : Sm E a ⊗[ℂ] (Fin Ξ.d → ℂ)), Cs (ev x) → Cs (ev (smLie Ξ X x)) ∧ Cs (ev (smAdj Ξ r X x))

def PtDiv : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (Ξ : AlgRep E a) (r : ℝ) (χ : HChar E)
    (G : Matrix (Fin Ξ.d) (Fin Ξ.d) ℂ), IsTw (a := a) r χ → IsAdm Ξ G → ∀ x y : Sm E a ⊗[ℂ] (Fin Ξ.d → ℂ),
    ∃ θ : Sm E a, (∀ g, θ.1 g = pt χ G x y g) ∧ ∀ (X : Herm E a) g,
      (lie E a (toL X.1) θ).1 g = pt χ G x (smLie Ξ (toL X.1) y) g - pt χ G (smAdj Ξ r (toL X.1) x) y g

def AdjInt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (μ : Measure (GA E a)) [μ.IsHaarMeasure]
    (Ξ : AlgRep E a) (r : ℝ) (χ : HChar E) (G : Matrix (Fin Ξ.d) (Fin Ξ.d) ℂ), IsTw (a := a) r χ → IsAdm Ξ G →
    ∀ (X : Herm E a) (x y : Sm E a ⊗[ℂ] (Fin Ξ.d → ℂ)), TwInv χ x → TwInv χ y → Cs (ev x) ∨ Cs (ev y) →
      QInt μ (pt χ G x (smLie Ξ (toL X.1) y)) ∧ QInt μ (pt χ G (smAdj Ξ r (toL X.1) x) y) ∧
        qint μ (pt χ G x (smLie Ξ (toL X.1) y)) = qint μ (pt χ G (smAdj Ξ r (toL X.1) x) y)

def PtD : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (Ξ : AlgRep E a) (χ : HChar E)
    (G : Matrix (Fin Ξ.d) (Fin Ξ.d) ℂ) (n : ℕ) (e : Fin n → Herm E a) (q : ℕ)
    (L : Lie E a →ₗ[ℝ] Module.End ℂ (Sm E a ⊗[ℂ] (Fin Ξ.d → ℂ))) (β : Co Ξ (q + 1)) (η : Co Ξ q) (g : GA E a),
    ptIp χ G e β (dCo L η) g = ((q : ℂ) + 1) * ∑ J : Fin q → Fin n, ∑ j,
        pt χ G (β (Matrix.vecCons (e j) fun i => e (J i))) (L (toL (e j).1) (η fun i => e (J i))) g ∧
      ptIp χ G e (del L e β) η g = ∑ J : Fin q → Fin n, ∑ j,
        pt χ G (L (toL (e j).1) (β (Matrix.vecCons (e j) fun i => e (J i)))) (η fun i => e (J i)) g

def ChiOne : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (χ : HChar E) (s : ℝ), χ.IsAbsPow s →
    ∀ g : KernelIndexFullLattice.G1 E a, ‖((chiDet a χ g.1 : ℂˣ) : ℂ)‖ = 1

def RapidBdd : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (Ξ : AlgRep E a) (χ : HChar E) (s : ℝ), χ.IsAbsPow s →
    ∀ (G : Matrix (Fin Ξ.d) (Fin Ξ.d) ℂ) (n : ℕ) (e : Fin n → Herm E a) (q : ℕ) (α β : Co Ξ q), Rapid α → Moderate β →
      ∃ C : ℝ, ∀ g : KernelIndexFullLattice.G1 E a, ‖ptIp χ G e α β g.1‖ ≤ C

def ZeroInt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (μ : Measure (GA E a)) [μ.IsHaarMeasure]
    (F : GA E a → ℂ), CInv F → (∀ g, ∃ t : ℝ, 0 ≤ t ∧ F g = t) → QInt μ F → qint μ F = 0 → ∀ g, F g = 0

def PtPos : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (Ξ : AlgRep E a) (χ : HChar E)
    (G : Matrix (Fin Ξ.d) (Fin Ξ.d) ℂ), IsAdm Ξ G → ∀ (n : ℕ) (e : Fin n → Herm E a), IsFrame e → ∀ (q : ℕ) (α : Co Ξ q),
    (∀ g, ∃ t : ℝ, 0 ≤ t ∧ ptIp χ G e α α g = t) ∧ ((∀ g, ptIp χ G e α α g = 0) → α = 0)

theorem pairFacts_of_steps (h1 : BddInt) (h2 : CsBdd) (h3 : LevInv) (h4 : PtInv) (h5 : AdjInt) (h6 : PtD) (h7 : RapidBdd)
    (h8 : ZeroInt) (h9 : PtPos) : PairFacts := by
  intro E _ _ _ a ha μ _ U hU Ξ r χ G n e hD q
  have hv := h3 E a ha U hU Ξ r χ hD.one hD.tw
  have hc : ∀ α β : Co Ξ q, IsLev U Ξ α → IsLev U Ξ β → CInv (ptIp χ G e α β) := fun α β hα hβ => by
    rw [show ptIp χ G e α β = _ from funext (ptIp_eq χ G e α β)]
    exact CInv.sum _ fun I => (h4 E a χ _ G _ _).2.1 (hv q α hα _) (hv q β hβ _)
  refine ⟨fun α β hα hβ hr hm => ?_, fun α β hα hβ hs => ⟨?_, ?_⟩, fun α hα hi h0 => ?_, fun β η hβ hη hs => ?_⟩
  · obtain ⟨s, hs⟩ := hD.tw.1
    exact (h1 E a μ _ (hc α β hα hβ) (h2 E a _ (hc α β hα hβ) (.inr (h7 E a Ξ χ s hs G n e q α β hr hm)))).1
  · refine (h1 E a μ _ (hc α β hα hβ) (h2 E a _ (hc α β hα hβ) (.inl ?_))).1
    exact hs.imp fun R hR g hg => by simp [ptIp, hR _ g hg]
  · refine (h1 E a μ _ (hc β α hβ hα) (h2 E a _ (hc β α hβ hα) (.inl ?_))).1
    exact hs.imp fun R hR g hg => by simp [ptIp, hR _ g hg]
  · have hp := h9 E a Ξ χ G hD.adm n e hD.frame q α
    exact hp.2 (h8 E a μ _ (hc α α hα hα) hp.1 hi h0)
  · have hA := fun (J : Fin q → Fin n) (j : Fin n) => h5 E a μ Ξ r χ G hD.tw hD.adm (e j)
      (β (Matrix.vecCons (e j) fun i => e (J i))) (η fun i => e (J i)) (hv _ β hβ _) (hv _ η hη _)
      (hs.imp (fun h => h.imp fun R hR g hg => hR _ g hg) fun h => h.imp fun R hR g hg => hR _ g hg)
    simp only [pair, (h6 E a Ξ χ G n e q (smLie Ξ) β η _).1, (h6 E a Ξ χ G n e q (smAdj Ξ r) β η _).2]
    rw [integral_const_mul, integral_finsetSum _ fun J _ => integrable_finsetSum _ fun j _ => (hA J j).1,
      integral_finsetSum _ fun J _ => integrable_finsetSum _ fun j _ => (hA J j).2.1]
    congr 1
    refine Finset.sum_congr rfl fun J _ => ?_
    rw [integral_finsetSum _ fun j _ => (hA J j).1, integral_finsetSum _ fun j _ => (hA J j).2.1]
    exact Finset.sum_congr rfl fun j _ => (hA J j).2.2

end UpperTheory.V.Lit.Geo.Pf
end
end

section

open UpperTheory.V.Lit.Geo

section
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af GlobalTheory.UnitaryBC UpperTheory.V.Lit.Dr UpperTheory.V.Lit.Bor UpperTheory.V
open GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open scoped TensorProduct

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

private theorem qht_bdd (g : GA E a) :
    BddBelow (Set.range fun γ : GL (Fin a) E => height (K := E) (ratGL E a γ * (retractOne g : KernelIndexFullLattice.G1 E a).1)) :=
  ⟨0, by rintro _ ⟨γ, rfl⟩; exact (height_pos _).le⟩

private theorem qht_nonneg (g : GA E a) : 0 ≤ qht g :=
  le_ciInf fun _ => (height_pos _).le

private theorem decay {φ : Sm E a} (hφ : IsCuspForm φ) (N : ℕ) :
    ∃ C : ℝ, ∀ g : KernelIndexFullLattice.G1 E a, ‖φ.1 g.1‖ * qht (E := E) (a := a) g.1 ^ N ≤ C := by
  have h0 := KernelIndexFullLattice.brCusp_holds E a φ hφ
  obtain ⟨ω, hω, hωB, t, ht, hsieg⟩ := Reduction.exists_siegelSet (K := E) a
  obtain ⟨C, hC⟩ := exists_norm_le_height_pow_neg_siegel h0 hω hωB ht N
  refine ⟨C, fun g => ?_⟩
  obtain ⟨γ, b, hb, _, ⟨ρ, hρ, hs, rfl⟩, kk, hkk, hxe⟩ := hsieg g.1
  have hγx : AdelicGLn.diagonal E a γ * g.1 ∈ Reduction.normOneGL (K := E) (n := a) :=
    mul_mem (Reduction.rationalGL_le_normOneGL ⟨γ, rfl⟩) g.2
  have h := hC b hb ρ hρ hs kk hkk _ hγx hxe
  rw [h0.1.isLeftInvariant γ g.1] at h
  have hp := height_pos (AdelicGLn.diagonal E a γ * g.1)
  have hq : qht (E := E) (a := a) g.1 ≤ height (AdelicGLn.diagonal E a γ * g.1) := by
    have h1 := ciInf_le (qht_bdd (E := E) (a := a) g.1) γ
    rw [retractOne_coe] at h1
    unfold qht
    rw [retractOne_coe]
    exact h1
  rw [le_mul_inv_iff₀ (pow_pos hp N)] at h
  exact (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (qht_nonneg _) hq N) (norm_nonneg _)).trans h

private theorem ev_cmp {d : ℕ} (m : Sm E a ⊗[ℂ] (Fin d → ℂ)) (g : GA E a) (i : Fin d) :
    ev m g i = (cmp i m).1 g := by
  induction m using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add (f := _), Pi.add_apply, hx, hy, Submodule.coe_add]
  | tmul φ v => simp [ev, mul_comm]

private theorem cmp_rTensor {d : ℕ} (T : Module.End ℂ (Sm E a)) (m : Sm E a ⊗[ℂ] (Fin d → ℂ)) (i : Fin d) :
    cmp i (T.rTensor _ m) = T (cmp i m) := by
  induction m using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add (f := _), hx, hy]
  | tmul φ v => simp

private theorem prodA_mem (π : CuspSub E a) (Ξ : AlgRep E a) (l : List (Lie E a)) (m : Sm E a ⊗[ℂ] (Fin Ξ.d → ℂ))
    (hm : m ∈ tens Ξ.d π.V) : (l.map (smA Ξ)).prod m ∈ tens Ξ.d π.V := by
  induction l with
  | nil => exact hm
  | cons X l ih =>
    rw [List.map_cons, List.prod_cons, Module.End.mul_apply, mem_tens]
    intro i
    rw [smA_apply, cmp_rTensor]
    exact π.stable (.lie X) _ (mem_tens.1 ih i)

private theorem decay_tens (π : CuspSub E a) {d : ℕ} (m : Sm E a ⊗[ℂ] (Fin d → ℂ)) (hm : m ∈ tens d π.V) (N : ℕ) :
    ∃ C : ℝ, ∀ g : KernelIndexFullLattice.G1 E a, ‖ev m g.1‖ * qht (E := E) (a := a) g.1 ^ N ≤ C := by
  choose C hC using fun i => decay (π.cusp _ (mem_tens.1 hm i)) N
  refine ⟨∑ i, C i, fun g => ?_⟩
  have hq : 0 ≤ qht (E := E) (a := a) g.1 ^ N := pow_nonneg (qht_nonneg _) N
  have h1 : ‖ev m g.1‖ ≤ ∑ i, ‖(cmp i m).1 g.1‖ := by
    refine (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun i _ => norm_nonneg _)).2 fun i => ?_
    rw [ev_cmp]
    exact Finset.single_le_sum (f := fun i => ‖(cmp i m).1 g.1‖) (fun i _ => norm_nonneg _) (Finset.mem_univ i)
  refine (mul_le_mul_of_nonneg_right h1 hq).trans ?_
  rw [Finset.sum_mul]
  exact Finset.sum_le_sum fun i _ => hC i g

end

theorem UpperTheory.V.Lit.Geo.cuspRapid :
    CuspRapid := by
  intro E _ _ _ a π Ξ q ω hω l X N
  exact decay_tens π _ (prodA_mem π Ξ l (ω X) (hω X)) N
end
