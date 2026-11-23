module

public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.RingTheory.Algebraic.Defs
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.Algebra.Module.Lattice.Full
public import Mathlib.Analysis.Complex.Order
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.RingTheory.Length
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.NumberTheory.NumberField.Basic
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Lean.Meta.Basic
public import Mathlib.RingTheory.Algebraic.Basic

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

namespace KAlt

end KAlt

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

namespace RestCutTransportFirst

end RestCutTransportFirst

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace GenericFibreModelTransport

open MvPolynomial

theorem adjoin_transport {k₁ A₁ k₂ A₂ : Type*} [Field k₁] [Field A₁] [Algebra k₁ A₁] [Field k₂] [Field A₂]
    [Algebra k₂ A₂] (i : k₁ ≃+* k₂) (h : A₁ →+* A₂)
    (hc : (algebraMap k₂ A₂).comp i.toRingHom = h.comp (algebraMap k₁ A₁)) (s : Set A₁) (a : A₁) :
    Module.finrank k₁ (Algebra.adjoin k₁ s) = Module.finrank k₂ (Algebra.adjoin k₂ (h '' s)) ∧
      (Transcendental (Algebra.adjoin k₁ s) a ↔ Transcendental (Algebra.adjoin k₂ (h '' s)) (h a)) := by
  have hring : (Algebra.adjoin k₂ (h '' s)).toSubring = (Algebra.adjoin k₁ s).toSubring.map h := by
    rw [Algebra.adjoin_eq_ring_closure, Algebra.adjoin_eq_ring_closure, RingHom.map_closure, Set.image_union]
    congr 2
    ext y
    constructor
    · rintro ⟨c, rfl⟩
      exact ⟨algebraMap k₁ A₁ (i.symm c), ⟨_, rfl⟩, by simpa using (congr($hc (i.symm c))).symm⟩
    · rintro ⟨_, ⟨c, rfl⟩, rfl⟩
      exact ⟨i c, by simpa using congr($hc c)⟩
  have hmem : ∀ y, y ∈ Algebra.adjoin k₂ (h '' s) ↔ ∃ x ∈ Algebra.adjoin k₁ s, h x = y := fun y => by
    rw [← Subalgebra.mem_toSubring, hring, Subring.mem_map]; rfl
  let g : Algebra.adjoin k₁ s →+* Algebra.adjoin k₂ (h '' s) :=
    (h.comp (Algebra.adjoin k₁ s).val.toRingHom).codRestrict (Algebra.adjoin k₂ (h '' s))
      (fun x => (hmem _).2 ⟨x, x.2, rfl⟩)
  have hg : Function.Bijective g := by
    refine ⟨fun x y hxy => Subtype.ext (h.injective (congr_arg Subtype.val hxy)), fun y => ?_⟩
    obtain ⟨x, hx, e⟩ := (hmem y).1 y.2
    exact ⟨⟨x, hx⟩, Subtype.ext e⟩
  let j := RingEquiv.ofBijective g hg
  refine ⟨Algebra.finrank_eq_of_equiv_equiv i j (RingHom.ext fun c => Subtype.ext congr($hc c)),
    (transcendental_ringHom_iff_of_comp_eq j h h.injective (RingHom.ext fun x => rfl)).symm⟩

theorem eval₂_mem_closure {σ F : Type*} [Field F] (c : ℤ →+* F) (y : σ → F) (f : MvPolynomial σ ℤ) :
    eval₂ c y f ∈ Subfield.closure (Set.range y) := by
  induction f using MvPolynomial.induction_on with
  | C a => rw [eval₂_C, eq_intCast]; exact intCast_mem _ a
  | add p q hp hq => rw [eval₂_add]; exact add_mem hp hq
  | mul_X p n hp => rw [eval₂_mul, eval₂_X]; exact mul_mem hp (Subfield.subset_closure ⟨n, rfl⟩)

theorem quotient_lift_injective {A F : Type*} [CommRing A] [Field F] (φ : A →+* F) (P : Ideal A)
    (h : RingHom.ker φ = P) (hP : ∀ a ∈ P, φ a = 0) : Function.Injective (Ideal.Quotient.lift P φ hP) := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro a ha
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  rw [Ideal.Quotient.lift_mk] at ha
  rw [Ideal.Quotient.eq_zero_iff_mem, ← h]
  exact ha

theorem subfield_equiv {L A Φ : Type*} [Field L] [Field A] [Field Φ] (k : Subfield L) (α : L →+* A)
    (ι : Φ →+* A) (hr : ι.fieldRange = k.map α) : ∃ e : k ≃+* Φ, ∀ c, ι (e c) = α c := by
  let g : k →+* ι.fieldRange :=
    (α.comp k.subtype).codRestrict ι.fieldRange (fun c => hr ▸ Subfield.mem_map.2 ⟨c, c.2, rfl⟩)
  have hg : Function.Bijective g := by
    refine ⟨fun x y hxy => Subtype.ext (α.injective (congr_arg Subtype.val hxy)), fun y => ?_⟩
    have hy : (y : A) ∈ k.map α := hr ▸ y.2
    obtain ⟨x, hx, e⟩ := Subfield.mem_map.1 hy
    exact ⟨⟨x, hx⟩, Subtype.ext e⟩
  exact ⟨(RingEquiv.ofBijective g hg).trans ι.rangeRestrictFieldEquiv.symm, fun c =>
    RingHom.rangeRestrictFieldEquiv_apply_symm_apply ι (g c)⟩

end GenericFibreModelTransport

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

theorem LinesLatticeBasis.proof (V : Type) [AddCommGroup V] [Module ℚ V]
    [FiniteDimensional ℚ V] (ι : Type) [Fintype ι]
    (hcard : Fintype.card ι = Module.finrank ℚ V) (M : Submodule ℤ V)
    (hM : Submodule.IsFullLattice ℚ M) :
    ∃ b : Module.Basis ι ℚ V, M = Submodule.span ℤ (Set.range b) := by
  have : Module.Free ℤ M := Submodule.IsLattice.free ℚ M
  have : Module.Finite ℤ M := Submodule.IsLattice.finite ℚ M
  let b0 := Module.finBasis ℤ M
  let B := b0.extendOfIsFullLattice ℚ
  have hc : Fintype.card (Fin (Module.finrank ℤ M)) = Fintype.card ι := by
    rw [hcard, Module.finrank_eq_card_basis B]
  let e := Fintype.equivOfCardEq hc
  refine ⟨B.reindex e, ?_⟩
  rw [Module.Basis.range_reindex]
  have hB : Set.range B = M.subtype '' Set.range b0 := by
    rw [← Set.range_comp']
    exact congrArg Set.range (funext (b0.extendOfIsFullLattice_apply ℚ))
  rw [hB, ← Submodule.map_span, b0.span_eq, Submodule.map_top, Submodule.range_subtype]

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix Finset
open scoped ComplexOrder

noncomputable section

def onePipe {R : Type*} [CommRing R] {j m : ℕ} (Z : Matrix (Fin j) (Fin m) R) :
    Matrix (Fin j) (Fin (j + m)) R :=
  Matrix.of fun a => Fin.append ((1 : Matrix (Fin j) (Fin j) R) a) (Z a)

def colsOf {R : Type*} {j N : ℕ} (A : Matrix (Fin j) (Fin N) R)
    (I : {I : Finset (Fin N) // I.card = j}) : Matrix (Fin j) (Fin j) R :=
  A.submatrix id (I.1.orderEmbOfFin I.2)

def rowsOf {R : Type*} {j N : ℕ} (B : Matrix (Fin N) (Fin j) R)
    (I : {I : Finset (Fin N) // I.card = j}) : Matrix (Fin j) (Fin j) R :=
  B.submatrix (I.1.orderEmbOfFin I.2) id

def CauchyBinet.Statement : Prop :=
  ∀ (R : Type) [CommRing R] (j N : ℕ) (A : Matrix (Fin j) (Fin N) R) (B : Matrix (Fin N) (Fin j) R),
    (A * B).det = ∑ I : {I : Finset (Fin N) // I.card = j}, (colsOf A I).det * (rowsOf B I).det

def PlueckerNormSq.Statement : Prop :=
  ∀ (j m : ℕ) (Z : Matrix (Fin j) (Fin m) ℂ),
    ((∑ I : {I : Finset (Fin (j + m)) // I.card = j}, ‖(colsOf (onePipe Z) I).det‖ ^ 2 : ℝ) : ℂ) =
      (1 + Z * Zᴴ).det

def HadamardPSD.Statement : Prop :=
  ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℂ), A.PosSemidef → ‖A.det‖ ≤ ∏ i, ‖A i i‖

def PlueckerUnitBound.Statement : Prop :=
  ∀ (j m : ℕ) (Z : Matrix (Fin j) (Fin m) ℂ), (∀ a b, ‖Z a b‖ = 1) →
    ‖(1 + Z * Zᴴ).det‖ ≤ (1 + m : ℝ) ^ j

def PlueckerKernel.Statement : Prop :=
  ∀ (j m : ℕ) (Z : Matrix (Fin j) (Fin m) ℂ), (∀ a b, ‖Z a b‖ = 1) →
    ∑ I : {I : Finset (Fin (j + m)) // I.card = j}, ‖(colsOf (onePipe Z) I).det‖ ^ 2 ≤
      (1 + m : ℝ) ^ j

def RootsOfUnityDense.Statement : Prop :=
  ∀ (n : ℕ) (P : MvPolynomial (Fin n) ℂ),
    (∀ z : Fin n → ℂ, (∀ i, ∃ k : ℕ, 0 < k ∧ z i ^ k = 1) → MvPolynomial.eval z P = 0) → P = 0

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix
open scoped ComplexOrder

noncomputable section

def HermFormCompare.Statement : Prop :=
  ∀ (n : ℕ) (M N : Matrix (Fin n) (Fin n) ℂ), M.PosDef → N.PosDef →
    ∃ c : ℝ, 0 < c ∧ ∀ x : Fin n → ℂ, (star x ⬝ᵥ (M *ᵥ x)).re ≤ c * (star x ⬝ᵥ (N *ᵥ x)).re

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

noncomputable section


open Classical in
def locLen {R : Type*} [CommRing R] (m : Ideal R) (N : Type*) [AddCommGroup N] [Module R N] : ℕ :=
  letI : Decidable m.IsPrime := Classical.propDecidable _
  if h : m.IsPrime then
    haveI := h
    (Module.length (Localization.AtPrime m) (LocalizedModule m.primeCompl N)).toNat
  else 0

def LogCardLength.Statement : Prop :=
  ∀ (R : Type) [CommRing R] (N : Type) [AddCommGroup N] [Module R N] [Finite N],
    Real.log (Nat.card N) =
      ∑ᶠ (m : Ideal R) (_ : m.IsMaximal), (locLen m N : ℝ) * Real.log (Nat.card (R ⧸ m))

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open NumberField

noncomputable section

def LocallyPrincipalCoprime.Statement : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] (B : Subring L) (M : AddSubgroup L) (ι : Type) [Fintype ι]
    (a : ι → L),
    Module.Finite ℤ B →
    (∀ b ∈ B, ∀ z ∈ M, b * z ∈ M) →
    (∀ i, a i ∈ M) →
    (∀ i, ∃ c ∈ B, c ≠ 0 ∧ c * a i ∈ B) →
    (∀ m : Ideal B, m.IsMaximal → ∃ i, ∀ z ∈ M, ∃ b c : B, b ∉ m ∧ (b : L) * z = c * a i) →
    M ≠ ⊥ → ∀ s : B, s ≠ 0 →
      ∃ (β δ : B) (I : Ideal B), β ≠ 0 ∧ δ ≠ 0 ∧ I ⊔ Ideal.span {s} = ⊤ ∧
        ∀ x : L, x ∈ M ↔ ∃ y ∈ I, (β : L) * x = δ * y

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open NumberField

noncomputable section

def OrderIdealIndexExtension.Statement : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] (B : Subring L), Module.Finite ℤ B →
    ∃ (r : ℕ) (s : B), s ≠ 0 ∧ Module.finrank ℚ L = r * Module.finrank ℤ B ∧
      (∀ I : Ideal B, I ≠ ⊥ → I.toAddSubgroup.index ≠ 0) ∧
      ∀ I : Ideal B, I ≠ ⊥ → (I.IsPrincipal ∨ I ⊔ Ideal.span {s} = ⊤) →
        (Submodule.span (𝓞 L) ((fun y : B => (y : L)) '' (I : Set B))).toAddSubgroup.relIndex
            (1 : Submodule (𝓞 L) L).toAddSubgroup = I.toAddSubgroup.index ^ r

end

end GroundTheory.Heights₂.Heights
end
