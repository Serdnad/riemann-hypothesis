module

public import Formalism.LocalToGlobal.HermitianColumns.InLocalDiscriminantKernel
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeComplements

open NumberField Formalism.BasicNotions

section General

variable {E : Type} [Field E] [NumberField E] [StarRing E]

def perp (W : HSpace E) (x : W.V) : Submodule E W.V := LinearMap.ker (W.hT x)

theorem mem_perp (W : HSpace E) (x y : W.V) : y ∈ perp W x ↔ W.hD y x = 0 := Iff.rfl

def IsSelfDualLattice (W : HSpace E) (L : Submodule (𝓞 E) W.V) : Prop :=
  Submodule.IsLattice E L ∧ Formalism.HermitianLatticesTheory.dual W.hT L = L

def OfKind (W : HSpace E) (M P Q : ℕ) : Prop :=
  W.SigOK ∧ W.rank = M ∧ ∀ τ : E →+* ℂ, W.sig τ = (P, Q)

def Step (β : E) (P Q P' Q' : ℕ) : Prop :=
  (β = 1 ∧ 1 ≤ P ∧ P' = P - 1 ∧ Q' = Q) ∨ (β = -1 ∧ 1 ≤ Q ∧ P' = P ∧ Q' = Q - 1)

def HasComplement (W : HSpace E) (x : W.V) (M' P' Q' : ℕ) : Prop :=
  ∃ (L : Submodule (𝓞 E) W.V) (W' : HSpace E) (ι : W'.V →ₗ[E] W.V),
    IsSelfDualLattice W L ∧ x ∈ L ∧
    OfKind W' M' P' Q' ∧
    HSpace.IsIsomEmb W' W ι ∧
    LinearMap.range ι = perp W x ∧
    W'.L0.map (ι.restrictScalars (𝓞 E)) = L ⊓ (perp W x).restrictScalars (𝓞 E) ∧
    L = Submodule.span (𝓞 E) {x} ⊔ (L ⊓ (perp W x).restrictScalars (𝓞 E))

def ExistsPerpOver (E : Type) [Field E] [NumberField E] [StarRing E] : Prop :=
  ∀ (W : HSpace E) (M P Q : ℕ), OfKind W M P Q → 3 ≤ M →
    ∀ (β : E) (P' Q' : ℕ), Step β P Q P' Q' →
      ∃ x : W.V, W.hD x x = β ∧ HasComplement W x (M - 1) P' Q'

theorem injective_of_isIsomEmb {W' W : HSpace E} {ι : W'.V →ₗ[E] W.V}
    (h : HSpace.IsIsomEmb W' W ι) : Function.Injective ι := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro y hy
  refine W'.nondeg.1 y fun z => ?_
  rw [← h y z, hy]
  simp

end General

def UnitVectorPerp (D : D7) : Prop :=
  @ExistsPerpOver D.host.E _ _ D.host.cmStar

end GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeComplements

end
end

section

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.UnitVectorOrthogonal

open NumberField Formalism.BasicNotions

section Generic

variable {E : Type} [Field E] [NumberField E] [StarRing E]

def OfKind (W : HSpace E) (M P Q : ℕ) : Prop :=
  W.rank = M ∧ W.SigOK ∧ ∀ τ : E →+* ℂ, W.sig τ = (P, Q)

def perp (W : HSpace E) (x : W.V) : Submodule E W.V := LinearMap.ker (W.hT x)

def perpLat (W : HSpace E) (L : Submodule (𝓞 E) W.V) (x : W.V) : Submodule (𝓞 E) W.V :=
  L ⊓ (perp W x).restrictScalars (𝓞 E)

def IsSelfDualLat (W : HSpace E) (L : Submodule (𝓞 E) W.V) : Prop :=
  Submodule.IsLattice E L ∧ Formalism.HermitianLatticesTheory.dual W.hT L = L

def HasComplement (W : HSpace E) (x : W.V) (M' P' Q' : ℕ) : Prop :=
  ∃ L : Submodule (𝓞 E) W.V, IsSelfDualLat W L ∧ x ∈ L ∧
    L = Submodule.span (𝓞 E) {x} ⊔ perpLat W L x ∧
    ∃ (W' : HSpace E) (ι : W'.V →ₗ[E] W.V), OfKind W' M' P' Q' ∧
      HSpace.IsIsomEmb W' W ι ∧ LinearMap.range ι = perp W x ∧
      W'.L0.map (ι.restrictScalars (𝓞 E)) = perpLat W L x

def UnitVectorPerpOver (E : Type) [Field E] [NumberField E] [StarRing E] : Prop :=
  ∀ (W : HSpace E) (M P Q : ℕ), OfKind W M P Q → 3 ≤ M →
    (1 ≤ P → ∃ x : W.V, W.hD x x = 1 ∧ HasComplement W x (M - 1) (P - 1) Q) ∧
    (1 ≤ Q → ∃ x : W.V, W.hD x x = -1 ∧ HasComplement W x (M - 1) P (Q - 1))

end Generic

def UnitVectorPerp (D : D7) : Prop :=
  letI := D.host.cmStar
  UnitVectorPerpOver D.host.E

end GlobalTheory.IndefiniteRowSideFullHecke.UnitVectorOrthogonal

end
end

section

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.CosetGroupMembership

open NumberField IsDedekindDomain Matrix Formalism.UG Formalism.BasicNotions Formalism.L2.Herm
open scoped TensorProduct

def cosetGrp {G : Type} [Group G] (Γ K : Subgroup G) (y : G) : Subgroup G :=
  Γ ⊓ K.map (MulAut.conj y).toMonoidHom

def CosetSum {G : Type} [Group G] (Γ K : Subgroup G) (m : ℝ) : Prop :=
  Finite (ClassSet Γ K) ∧
  (∀ y : G, Finite (cosetGrp Γ K y)) ∧
  ∀ (ι : Type) [Fintype ι] (y : ι → G),
    Function.Bijective (fun i => (DoubleCoset.mk Γ K (y i) : ClassSet Γ K)) →
    ∑ i, ((Nat.card (cosetGrp Γ K (y i)) : ℕ) : ℝ)⁻¹ = m

section Obj

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]

def stabHat (hc : CMData F E) (S : HSpace E) (N : Submodule (𝓞 E) S.V) : Subgroup (UAf hc S) :=
  (stabGL (hatL (F := F) (crdLat S N))).subgroupOf (UAf hc S)

def rat0 {R : Ranks} (sp : Spaces R F E) : Subgroup (UPts sp.cm.sig sp.gram0 (Af F)) :=
  (ratPts sp.cm.sig sp.gram0 (Af F)).subgroupOf (UPts sp.cm.sig sp.gram0 (Af F))

def stabHat0 {R : Ranks} (sp : Spaces R F E) (N : Submodule (𝓞 E) (sp.X 0).V) :
    Subgroup (UPts sp.cm.sig sp.gram0 (Af F)) :=
  (stabGL (hatL (F := F) (sp.crdLat0 N))).subgroupOf (UPts sp.cm.sig sp.gram0 (Af F))

end Obj

def GeneralForm : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    (hc : CMData F E) (S : HSpace E), S.SigOK → S.IsPosDef →
    ∀ N : Submodule (𝓞 E) S.V, Submodule.IsLattice E N → Formalism.HermitianLatticesTheory.IsUnimodular S.hT N →
      CosetSum (UFin hc S) (stabHat hc S N) (Formalism.HermitianLatticesTheory.mass S.hT N)

def ColumnForm (D : D7) : Prop :=
  letI := D.host.cmStar
  ∀ N : Submodule (𝓞 D.host.E) (D.sp.X 0).V, Submodule.IsLattice D.host.E N →
    Formalism.HermitianLatticesTheory.IsUnimodular (D.sp.X 0).hT N →
      CosetSum (rat0 D.sp) (stabHat0 D.sp N) (Formalism.HermitianLatticesTheory.mass (D.sp.X 0).hT N)

def MassAsCosetSum : Prop := GeneralForm ∧ ∀ D : D7, ColumnForm D

theorem mem_cosetGrp {G : Type} [Group G] (Γ K : Subgroup G) (y x : G) :
    x ∈ cosetGrp Γ K y ↔ x ∈ Γ ∧ y⁻¹ * x * y ∈ K := by
  simp only [cosetGrp, Subgroup.mem_inf, Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  refine and_congr_right fun _ => ⟨?_, fun h => ⟨_, h, by group⟩⟩
  rintro ⟨k, hk, rfl⟩
  have : y⁻¹ * (y * k * y⁻¹) * y = k := by group
  rwa [this]

theorem stabHat_eq {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E]
    [Algebra F E] (hc : CMData F E) (S : HSpace E) (N : Submodule (𝓞 E) S.V) :
    stabHat hc S N = (levelAfL hc.sig S.gram (crdLat S N)).subgroupOf (UAf hc S) := by
  ext x
  exact ⟨fun h => ⟨x.2, h⟩, fun h => h.2⟩

end GlobalTheory.IndefiniteRowSideFullHecke.CosetGroupMembership

end
end
