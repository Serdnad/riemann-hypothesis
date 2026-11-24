module

public import ReciprocityTheory.AnalyticForms.RegularLocalRings.StalkLoc
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.IsOpenAlt
public import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.SetTheory.ZFC.PSet
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Tactic.TypeStar
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.ExistsMulMemOfAlgebraMapLocRingEqZero
import Std.Tactic.BVDecide.Normalize.Prop
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.ClosureFromSpecMemCompsH

@[expose] public section

namespace ReciprocityTheory.AnForm.R

open AlgebraicGeometry CategoryTheory MvPolynomial TopologicalSpace IrreducibleComponentPreimages

noncomputable section

section Top

variable {α : Type*} [TopologicalSpace α]

def comps (T : Set α) : Set (Set α) :=
  {C | Maximal (fun C => IsIrreducible C ∧ C ⊆ T) C}

private theorem isIrreducible_preimage_coe_of_subset (T D : Set α) (hDT : D ⊆ T) (hD : IsIrreducible D) :
    IsIrreducible ((↑) ⁻¹' D : Set T) := by
  first
    | exact _root_.ReciprocityTheory.AnForm.R.IrreducibleComponentPreimages.compsH_pre_isIrreducible
    | apply _root_.ReciprocityTheory.AnForm.R.IrreducibleComponentPreimages.compsH_pre_isIrreducible <;> first | assumption | rfl | infer_instance

theorem comps_finite [NoetherianSpace α] (T : Set α) : (comps T).Finite := by
  apply _root_.ReciprocityTheory.AnForm.R.IrreducibleComponentPreimages.compsH_finite <;> assumption

theorem isClosed_of_mem_comps {T : Set α} (hT : IsClosed T) {C : Set α} (hC : C ∈ comps T) :
    IsClosed C := by
  have hC' : Maximal (fun C => IsIrreducible C ∧ C ⊆ T) C := hC
  have hcl : closure C ≤ C := hC'.2 ⟨hC'.1.1.closure, closure_minimal hC'.1.2 hT⟩ subset_closure
  exact closure_subset_iff_isClosed.1 hcl

theorem sUnion_comps (T : Set α) : ⋃₀ comps T = T := by
  apply _root_.ReciprocityTheory.AnForm.R.IrreducibleComponentPreimages.sUnion_compsH <;> assumption

end Top

variable {W : Scheme.{0}}

def IsBranch (T : Set W) {U : W.Opens} (f : Γ(W, U)) (y : W) (C : Set W) : Prop :=
  C ∈ comps T ∧ y ∈ C ∧ ∃ h : IsIrreducible C, h.genericPoint ∈ U ∧ h.genericPoint ∈ W.zeroLocus {f}

theorem existsUnique_branch [IsNoetherian W] {Z : W.IdealSheafData} (y : W) (U : W.affineOpens)
    (hy : y ∈ U.1) {n : ℕ} (f : Fin n → Γ(W, U.1)) (J : Finset (Fin n))
    [IsRegularLocalRing (W.presheaf.stalk y)]
    (hrsp : FinalTheorems.Rsp (W.presheaf.stalk y) n (fun i => W.presheaf.germ U.1 y hy (f i)))
    (hZU : Z.ideal U = Ideal.span {∏ i ∈ J, f i}) (i : Fin n) (hi : i ∈ J) :
    ∃! C, IsBranch (Z.support : Set W) (f i) y C := by
  exact existsUnique_branchH y U hy f J hrsp hZU i hi

theorem branch_ne [IsNoetherian W] {Z : W.IdealSheafData} (y : W) (U : W.affineOpens)
    (hy : y ∈ U.1) {n : ℕ} (f : Fin n → Γ(W, U.1)) (J : Finset (Fin n))
    [IsRegularLocalRing (W.presheaf.stalk y)]
    (hrsp : FinalTheorems.Rsp (W.presheaf.stalk y) n (fun i => W.presheaf.germ U.1 y hy (f i)))
    (hZU : Z.ideal U = Ideal.span {∏ i ∈ J, f i}) {i j : Fin n} (hi : i ∈ J) (hj : j ∈ J)
    (hij : i ≠ j) {C C' : Set W} (hC : IsBranch (Z.support : Set W) (f i) y C)
    (hC' : IsBranch (Z.support : Set W) (f j) y C') : C ≠ C' := by
  exact branch_neH y U hy f J hrsp hZU hi hj hij hC hC'

theorem exists_open_comps [IsNoetherian W] {Z : W.IdealSheafData} (y : W) (U : W.affineOpens)
    (hy : y ∈ U.1) {n : ℕ} (f : Fin n → Γ(W, U.1)) (J : Finset (Fin n))
    [IsRegularLocalRing (W.presheaf.stalk y)]
    (hrsp : FinalTheorems.Rsp (W.presheaf.stalk y) n (fun i => W.presheaf.germ U.1 y hy (f i)))
    (hZU : Z.ideal U = Ideal.span {∏ i ∈ J, f i}) :
    ∃ O : W.Opens, y ∈ O ∧ O ≤ U.1 ∧ ∀ C ∈ comps (Z.support : Set W),
      C ∩ O = {z ∈ (O : Set W) | ∃ i ∈ J, IsBranch (Z.support : Set W) (f i) y C ∧
        z ∈ W.zeroLocus {f i}} := by
  exact exists_open_compsH y U hy f J hrsp hZU

section Chart

variable {s : W ⟶ Spec (.of ℂ)}

theorem AffPres.isAffineOpen (P : AffPres s) : IsAffineOpen P.V := by
  first
  | exact IsAffine.of_isIso P.iso.hom

def AffPres.affOpen (P : AffPres s) : W.affineOpens := ⟨P.V, P.isAffineOpen⟩

end Chart

end

end ReciprocityTheory.AnForm.R
