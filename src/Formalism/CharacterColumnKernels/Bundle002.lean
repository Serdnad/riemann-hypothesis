module

public import Formalism.CharacterColumnKernels.Bundle001
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open Finset

noncomputable section

namespace Formalism.NG

section Coh
variable {O : Type*} [CommRing O] {G : Type*} [Group G] {M : Type*} [AddCommGroup M] [Module O M]

def coZ1s (ρ : Representation O G M) : Submodule O (G → M) where
  carrier := {c | ∀ g h, c (g * h) = c g + ρ g (c h)}
  add_mem' {a b} ha hb g h := by
    simp only [Pi.add_apply, ha g h, hb g h, map_add (f := _)]; abel
  zero_mem' g h := by simp
  smul_mem' r c hc g h := by
    simp only [Pi.smul_apply, hc g h, smul_add, map_smul]

def resRep (ρ : Representation O G M) (D : Subgroup G) : Representation O D M :=
  ρ.comp D.subtype

def restrictCocycles1 (ρ : Representation O G M) (D : Subgroup G) : coZ1s ρ →ₗ[O] coZ1s (resRep ρ D) where
  toFun c := ⟨fun g => (c : G → M) g, fun g h => c.2 g h⟩
  map_add' a b := rfl
  map_smul' r a := rfl

abbrev H1z (ρ : Representation O G M) : Type _ := coZ1s ρ ⧸ (coB1 ρ).comap (coZ1s ρ).subtype

def resH1 (ρ : Representation O G M) (D : Subgroup G) : H1z ρ →ₗ[O] H1z (resRep ρ D) :=
  Submodule.mapQ _ _ (restrictCocycles1 ρ D) (by
    rintro x ⟨v, hv⟩
    exact ⟨v, funext fun g => congrFun hv g⟩)

end Coh

def annih {O Cw Cs P : Type*} [CommRing O] [AddCommGroup Cw] [Module O Cw] [AddCommGroup Cs]
    [Module O Cs] [AddCommGroup P] [Module O P] (pr : Cw →ₗ[O] Cs →ₗ[O] P) (U : Submodule O Cs) :
    Submodule O Cw :=
  ⨅ x ∈ U, LinearMap.ker (pr.flip x)

def StatLenChain : Prop :=
  ∀ (O H Zc C : Type*) [CommRing O] [AddCommGroup H] [Module O H] [AddCommGroup Zc] [Module O Zc]
    [AddCommGroup C] [Module O C] (Ψ : H →ₗ[O] Zc) (cl : Zc →ₗ[O] C) (S : Submodule O C),
    LinearMap.range (cl ∘ₗ Ψ) ≤ S →
    Module.length O H ≤ Module.length O (LinearMap.ker Ψ) +
      Module.length O ↥(LinearMap.range Ψ ⊓ LinearMap.ker cl) + Module.length O S

def StatSelRelax : Prop :=
  ∀ (O C ι : Type*) [CommRing O] [AddCommGroup C] [Module O C] (what₂ : Finset ι)
    (Cw : ι → Type*) [∀ w, AddCommGroup (Cw w)] [∀ w, Module O (Cw w)] (res : ∀ w, C →ₗ[O] Cw w)
    (F F' : ∀ w, Submodule O (Cw w)) (Q : Submodule O C), (∀ w, F w ≤ F' w) →
    Module.length O ↥(Q ⊓ ⨅ w ∈ what₂, (F' w).comap (res w)) ≤
      Module.length O ↥(Q ⊓ ⨅ w ∈ what₂, (F w).comap (res w)) +
        ∑ w ∈ what₂, Module.length O (F' w ⧸ (F w).comap (F' w).subtype)

def StatAnnColength : Prop :=
  ∀ (O Cw Cs : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [AddCommGroup Cw]
    [Module O Cw] [AddCommGroup Cs] [Module O Cs] (pr : Cw →ₗ[O] Cs →ₗ[O] KO O),
    ∀ (Fs Im : Submodule O Cs), Im ≤ Fs →
    Module.length O (annih pr Im ⧸ (annih pr Fs).comap (annih pr Im).subtype) ≤
      Module.length O (Fs ⧸ Im.comap Fs.subtype)

def StatTorsLen : Prop :=
  ∀ (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (d : Type) [Fintype d]
    (δ : O),
    Module.length O (LinearMap.ker (DistribSMul.toLinearMap O (d → KO O) (δ * δ))) =
      (Fintype.card d : ℕ∞) * (2 * IsDiscreteValuationRing.addVal O δ)

end Formalism.NG
end
end

section

open Finset Polynomial

noncomputable section

namespace Formalism.NG

def matEnd (O M : Type*) [CommRing O] [AddCommGroup M] [Module O M] (d : Type*) [Fintype d]
    [DecidableEq d] : Matrix d d O →+* Module.End O (d → M) where
  toFun A := relMap O M A
  map_one' := by
    refine LinearMap.ext fun v => funext fun i => ?_
    simp [relMap, Matrix.one_apply, ite_smul, Finset.sum_ite_eq]
  map_mul' A B := by
    refine LinearMap.ext fun v => funext fun i => ?_
    show (∑ j, (A * B) i j • v j) = ∑ k, A i k • ∑ j, B k j • v j
    simp only [Matrix.mul_apply, Finset.sum_smul, Finset.smul_sum, mul_smul]
    exact Finset.sum_comm
  map_zero' := by
    refine LinearMap.ext fun v => funext fun i => ?_
    simp [relMap]
  map_add' A B := by
    refine LinearMap.ext fun v => funext fun i => ?_
    simp [relMap, add_smul, Finset.sum_add_distrib]

def LatQ {R : Type*} [Ring R] (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (d : Type*) [Fintype d] [DecidableEq d] (_ρ : R →+* Matrix d d O) : Type _ := d → KO O

section LatQ
variable {R : Type*} [Ring R] (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  (d : Type*) [Fintype d] [DecidableEq d] (ρ : R →+* Matrix d d O)

instance : AddCommGroup (LatQ O d ρ) := inferInstanceAs (AddCommGroup (d → KO O))
instance : Module O (LatQ O d ρ) := inferInstanceAs (Module O (d → KO O))
instance : Module R (LatQ O d ρ) :=
  Module.compHom (d → KO O) ((matEnd O (KO O) d).comp ρ)

end LatQ

def StatKerHomRect : Prop :=
  ∀ (R O : Type*) [Ring R] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (m g d : Type) [Fintype m] [Fintype g] [DecidableEq g] [Fintype d] [DecidableEq d]
    (ρ : R →+* Matrix d d O) [SMulCommClass R O (LatQ O d ρ)] (P : Matrix m g R),
    Module.length O (LinearMap.ker (relMap O (KO O)
        (fun (p : m × d) (q : g × d) => ρ (P p.1 q.1) p.2 q.2))) =
      Module.length O (Coker P →ₗ[R] LatQ O d ρ)

end Formalism.NG
end
end

section

open Finset

noncomputable section

namespace Formalism.NG

universe u

def epsImg (O : Type*) {OO M : Type*} [CommRing O] [Ring OO] [Algebra O OO] [AddCommGroup M]
    [Module OO M] [Module O M] [IsScalarTower O OO M] (ε : OO) : Submodule O M :=
  LinearMap.range (DistribSMul.toLinearMap O M ε)

def epsIdeal (O : Type*) {OO : Type*} [CommRing O] [Ring OO] [Algebra O OO] (ε : OO) :
    Submodule O OO :=
  LinearMap.range (LinearMap.mulLeft O ε)

abbrev EpsDual (O OO Q : Type*) [CommRing O] [Ring OO] [Algebra O OO] [AddCommGroup Q] [Module O Q]
    (ε : OO) : Type _ :=
  epsIdeal O ε →ₗ[O] Q

section EpsDual
variable (O OO Q : Type*) [CommRing O] [Ring OO] [Algebra O OO] [AddCommGroup Q] [Module O Q]
  (ε : OO)

end EpsDual

def StatMatlis : Prop :=
  ∀ (O N : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [AddCommGroup N]
    [Module O N], IsFiniteLength O N →
    Module.length O (N →ₗ[O] KO O) = Module.length O N

end Formalism.NG
end
end

section

open Finset

noncomputable section

namespace Formalism.NG

def bigRect {R O : Type*} [CommRing O] {m g d : Type*} (ρ : R → Matrix d d O) (P : Matrix m g R) :
    Matrix (m × d) (g × d) O :=
  fun p q => ρ (P p.1 q.1) p.2 q.2

def StatGeneric : Prop :=
  ∀ (R O : Type*) [Ring R] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra O R]
    [Infinite (IsLocalRing.ResidueField O)]
    (m g s : Type) [Fintype m] [Fintype g] [DecidableEq g] [Fintype s]
    (d : s → Type) [∀ w, Fintype (d w)] [∀ w, DecidableEq (d w)]
    (ρ : ∀ w, R →ₐ[O] Matrix (d w) (d w) O), (∀ w, Function.Surjective (ρ w)) →
    ∀ P : Matrix m g R, ∃ C : Matrix g m R, ∀ w,
      Module.length O (LinearMap.ker (matQ O (bigMat (ρ w) (C * P)))) =
        Module.length O (LinearMap.ker (relMap O (KO O) (bigRect (ρ w) P)))

def StatGenericFin : Prop :=
  ∀ (R O : Type*) [Ring R] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra O R]
    (m g s : Type) [Fintype m] [Fintype g] [DecidableEq g] [Fintype s]
    (d : s → Type) [∀ w, Fintype (d w)] [∀ w, DecidableEq (d w)],
    ((Fintype.card g * ∑ w, Fintype.card (d w) : ℕ) : Cardinal) <
      Cardinal.mk (IsLocalRing.ResidueField O) →
    ∀ (ρ : ∀ w, R →ₐ[O] Matrix (d w) (d w) O), (∀ w, Function.Surjective (ρ w)) →
    ∀ P : Matrix m g R, ∃ C : Matrix g m R, ∀ w,
      Module.length O (LinearMap.ker (matQ O (bigMat (ρ w) (C * P)))) =
        Module.length O (LinearMap.ker (relMap O (KO O) (bigRect (ρ w) P)))

end Formalism.NG
end
end
