module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

@[expose] public section

section

set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain GlobalTheory.TrueGeo
namespace GlobalTheory.TrueGeoModel
variable {F : Type} [Field F] [NumberField F]

theorem nonempty_ext (v : HeightOneSpectrum (𝓞 F)) : Nonempty (Ext v) := by
  obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot v.ne_bot
  let K := v.adicCompletion F
  have h1 : ‖FinitePlace.embedding v (algebraMap (𝓞 F) F a)‖ < 1 := (FinitePlace.norm_lt_one_iff_mem F v a).2 ha
  have h0 : FinitePlace.embedding v (algebraMap (𝓞 F) F a) ≠ 0 := by
    simpa using ha0
  letI : NontriviallyNormedField K := NontriviallyNormedField.ofNormNeOne ⟨_, h0, h1.ne⟩
  let L := AlgebraicClosure K
  letI : Algebra F L := ((algebraMap K L).comp (FinitePlace.embedding v)).toAlgebra
  let j : AlgebraicClosure F →ₐ[F] L := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  let N := spectralMulAlgNorm K L
  let w : AbsoluteValue (AlgebraicClosure F) ℝ :=
    (MulRingNorm.mulRingNormEquivAbsoluteValue N.toMulRingNorm).comp (f := j.toRingHom) j.injective
  have hw (x) : w x = spectralNorm K L (j x) := rfl
  have hn (x y) : w (x + y) ≤ max (w x) (w y) := by
    rw [hw, hw, hw, map_add (f := _)]; exact isNonarchimedean_spectralNorm _ _
  refine ⟨⟨w, fun x => ?_, ⟨⟨⟨⟨⟨{x | w x ≤ 1}, ?_⟩, by simp⟩, ?_, by simp⟩, ?_⟩, ?_⟩, fun _ => Iff.rfl⟩⟩
  · rw [hw, j.commutes, ← FinitePlace.norm_embedding]
    exact spectralNorm_extends _
  · intro x y hx hy
    simp only [Set.mem_setOf_eq, map_mul] at *
    exact mul_le_one₀ hx (w.nonneg _) hy
  · intro x y hx hy
    exact (hn x y).trans (max_le hx hy)
  · intro x hx
    simpa using hx
  · intro x
    rcases le_total (w x) 1 with h | h
    · exact .inl h
    · refine .inr ?_
      change w x⁻¹ ≤ 1
      rw [map_inv₀]; exact inv_le_one_of_one_le₀ h

end GlobalTheory.TrueGeoModel
end
end

section

set_option autoImplicit false

noncomputable section

open GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar GlobalTheory.ProjVar.Var

namespace GlobalTheory.ProjVar

def cxStage (F : Type) [Field F] [NumberField F] : TrueGeo.CxSt F where
  borel _ _ := inferInstance
  vol := vol
  FnC := FnC
  cx := cx
  cx_smul := cx_smul
  Met := Met
  mAdd Y σ Δ Δ' := mAdd Y σ Δ Δ'
  mPow Y σ Δ := mPow Y σ Δ
  fsMet Y σ Δ := fsMet Y σ Δ
  pn Y σ Δ := pn Y σ Δ
  pnK Y σ Δ := pnK Y σ Δ
  mSmooth Y σ Δ := mSmooth Y σ Δ
  mPsh Y σ Δ := mPsh Y σ Δ
  redZero Y σ Δ := redZero Y σ Δ
  agreeOn Y σ Δ := agreeOn Y σ Δ
  resNorm Y σ Δ := Var.resNorm Y σ Δ
  regOn Y σ Δ := regOn Y σ Δ
  ofWeight Y σ Δ L r := Var.ofWeight Y σ Δ L r
  pn_ofWeight Y σ Δ L r h φ f y i hi _ := by rw [Var.pn_ofWeight h φ (mem_ptsIn.2 hi), fval_cx]
  pn_mAdd Y σ Δ Δ' m m' f f' y h h' := by
    rw [map_mul, Var.pn_mAdd (secReg_cx_iff.2 h) (secReg_cx_iff.2 h')]
  pn_mPow Y σ Δ k m f y h := by rw [map_pow, Var.pn_mPow (secReg_cx_iff.2 h.regularAt)]
  pn_mul Y σ Δ m a f y ha h := by
    rw [map_mul, Var.pn_mul (regC_cx_iff.2 ha) (secReg_cx_iff.2 h), val_cx]
  pn_fs Y σ Δ ι κ _ _ b X f y g hg hb _ _ := by
    have e (k) := hasVal_sum_smul (y := y) hg (fun i => secReg_cx_of_mem (hb i) y) fun i => X i k
    rw [pn_fsMet (fun k => (secReg_iff hg).2 (e k).regC) hg, fval_cx]
    simp only [fval, fun k => (e k).val_eq, ← map_mul, val_cx]

end GlobalTheory.ProjVar
end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter MeasureTheory NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Cartier GlobalTheory.ProjVar Formalism.BasicNotions

namespace GlobalTheory.TrueGeo

variable {F : Type} [Field F] [NumberField F] (Y : Var F) (E : Type) [Field E] [NumberField E] [Algebra F E] {n : ℕ}
  (w : Fin n → Y.Fn) (c : Fin Y.dim → Fin n → 𝓞 E)

def GeomPt : Type :=
  {y : Sp (AlgebraicClosure E) ⟶ Y.X // y ≫ Y.str = spMap ((algebraMap E (AlgebraicClosure E)).comp (algebraMap F E))}

def GenAt (x : Y.X) (k : Fin n) : Prop := w k ≠ 0 ∧ ∀ l, RegAt x (w l / w k)

def coef (i : Fin Y.dim) (l : Fin n) : AlgebraicClosure E := algebraMap E _ (c i l : E)

def cutSet : Set (GeomPt Y E) :=
  {y | ∀ k, GenAt Y w (below y.1) k → ∀ i, ∑ l, coef Y E c i l * valAt y.1 (w l / w k) = 0}

def IsTangent (y : GeomPt Y E) (δ : Y.X.presheaf.stalk (below y.1) →+ AlgebraicClosure E) : Prop :=
  (∀ a b, δ (a * b) = (Scheme.stalkClosedPointTo y.1).hom a * δ b + (Scheme.stalkClosedPointTo y.1).hom b * δ a) ∧
    ∀ (a : Y.X.presheaf.stalk (below y.1)) (t : F), algebraMap _ Y.Fn a = algebraMap F Y.Fn t → δ a = 0

def ReducedAt (y : GeomPt Y E) : Prop :=
  ∀ k, GenAt Y w (below y.1) k → ∀ u : Fin n → Y.X.presheaf.stalk (below y.1),
    (∀ l, algebraMap _ Y.Fn (u l) = w l / w k) → ∀ δ, IsTangent Y E y δ →
      (∀ i, ∑ l, coef Y E c i l * δ (u l) = 0) → δ = 0

def cutGood (bd : Y.Cl) : Prop :=
  (∀ x, ∃ k, GenAt Y w x k) ∧ (cutSet Y E w c).Finite ∧
    ∀ y ∈ cutSet Y E w c, ReducedAt Y E w c y ∧ below y.1 ∉ bd

def cutHt {C : CxSt F} (A : Adl C Y) : ℝ := ∑ᶠ y ∈ cutSet Y E w c, A.ht (below y.1)

def cutOrd (Δ : Y.Dv) (f : Y.Fn) : ℕ :=
  sSup {a : ℕ | ∀ y ∈ cutSet Y E w c, ∃ b ∈ IsLocalRing.maximalIdeal (Y.X.presheaf.stalk (below y.1)) ^ a,
    algebraMap _ Y.Fn b = f * (eqn Δ (below y.1) : Y.Fn)}

def cutSt [StarRing F] (C : CxSt F) : CutSt C where
  cutGood := fun Y bd E _ _ _ _ w c => cutGood Y E w c bd
  cutHt := fun Y A E _ _ _ _ w c => cutHt Y E w c A
  cutOrd := fun Y E _ _ _ _ w c Δ f => cutOrd Y E w c Δ f

end GlobalTheory.TrueGeo
end
end
