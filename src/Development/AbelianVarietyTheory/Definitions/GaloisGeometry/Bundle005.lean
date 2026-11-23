module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsDPMorphismBot
public import Development.AbelianVarietyTheory.Definitions.Divisors.CrystallineConnectionFormCoboundaryZero
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle002
public import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
public import Formalism.UnipotentAdelicQuotients.Bundle002
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry

namespace GlobalTheory.LogCris

variable {O : Type} [CommRing O]

abbrev PtOver (X : Scheme.{0}) (q : X ⟶ Spec (CommRingCat.of O)) {k : Type} [CommRing k] (κ : O →+* k) (B : Type)
    [CommRing B] : Type :=
  {z : (k →+* B) × (Spec (CommRingCat.of B) ⟶ X) // z.2 ≫ q = Spec.map (CommRingCat.ofHom (z.1.comp κ))}

def IsSSFun (ϖ : O) (X : Scheme.{0}) (q : X ⟶ Spec (CommRingCat.of O)) {k : Type} [CommRing k] (κ : O →+* k)
    (L : LogFun k (κ ϖ)) : Prop :=
  GlobalTheory.Et.IsStrictlySemistable ϖ q ∧
  ∃ (e : ∀ B : CommRingCat.{0}, L.Pt.obj B ≃ PtOver X q κ B) (U : L.A → X.Opens) (F : ∀ α, L.ι → Γ(X, U α))
    (G : ∀ α β, L.ι → Γ(X, U α ⊓ U β)ˣ),
    (∀ α, IsAffineOpen (U α)) ∧ (⨆ α, U α) = ⊤ ∧
    (∀ α, ∏ i, F α i = (q.appLE ⊤ (U α) le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom ϖ)) ∧
    (∀ α β i, X.presheaf.map (homOfLE inf_le_left).op (F α i) =
      (G α β i : Γ(X, U α ⊓ U β)) * X.presheaf.map (homOfLE inf_le_right).op (F β i)) ∧
    (∀ α i, F α i ∈ nonZeroDivisors Γ(X, U α)) ∧
    (∀ α (x : X), x ∈ U α → ∃ (V : X.Opens) (_ : IsAffineOpen V) (_ : x ∈ V) (hV : V ≤ U α) (m r : ℕ) (_ : 1 ≤ r)
      (_ : r ≤ m) (c : Fin r ↪ L.ι)
      (ψ : (MvPolynomial (Fin m) O ⧸ Ideal.span {(((Finset.univ.filter (fun j : Fin m => (j : ℕ) < r)).prod
        (fun j => MvPolynomial.X j)) - MvPolynomial.C ϖ)}) →+* Γ(X, V)),
      ψ.Etale ∧ ψ.comp (algebraMap O _) = ((Scheme.ΓSpecIso (CommRingCat.of O)).inv ≫ q.appLE ⊤ V le_top).hom ∧
      (∀ j : Fin r, ∃ u : Γ(X, V)ˣ, ψ (Ideal.Quotient.mk _ (MvPolynomial.X (Fin.castLE (by omega) j))) =
        u * X.presheaf.map (homOfLE hV).op (F α (c j))) ∧
      ∀ i, i ∉ Set.range c → IsUnit (X.presheaf.map (homOfLE hV).op (F α i))) ∧
    (∀ {B B' : CommRingCat.{0}} (φ : B ⟶ B') (y : L.Pt.obj B),
      (e B' (L.Pt.map φ y)).1 = (φ.hom.comp (e B y).1.1, Spec.map φ ≫ (e B y).1.2)) ∧
    ∀ {B : CommRingCat.{0}} (y : L.Pt.obj B),
      (e B y).1.1 = L.str y ∧
      ∀ α, (L.In α y ↔ ⊤ ≤ (e B y).1.2 ⁻¹ᵁ U α) ∧
        ∀ (h : ⊤ ≤ (e B y).1.2 ⁻¹ᵁ U α),
          (∀ i, L.f α i y = GlobalTheory.Cris.evalAt (e B y).1.2 (U α) h (F α i)) ∧
          ∀ β (h' : ⊤ ≤ (e B y).1.2 ⁻¹ᵁ (U α ⊓ U β)) i,
            (L.g α β i y : B) = GlobalTheory.Cris.evalAt (e B y).1.2 (U α ⊓ U β) h' (G α β i)

end GlobalTheory.LogCris
end
end

section

noncomputable section

namespace GlobalTheory.HeckeSplit

open NumberField IsDedekindDomain HeckeValGen

variable (L : Type) [Field L] [NumberField L]

def IsHeckeChar (χ : Ideles L →* ℂˣ) : Prop := Continuous χ ∧ ∀ k : Lˣ, χ (diagUnits L k) = 1

def infIdele : (InfiniteAdeleRing L)ˣ →* Ideles L :=
  Units.map (MonoidHom.inl (InfiniteAdeleRing L) (FiniteAdeleRing (𝓞 L) L))

def infPart : Ideles L →* (InfiniteAdeleRing L)ˣ :=
  Units.map (MonoidHom.fst (InfiniteAdeleRing L) (FiniteAdeleRing (𝓞 L) L))

def finPart (v : HeightOneSpectrum (𝓞 L)) : Ideles L →* (v.adicCompletion L)ˣ :=
  Units.map
    { toFun := fun x : AdeleRing (𝓞 L) L => (x.2 : FiniteAdeleRing (𝓞 L) L) v
      map_one' := rfl
      map_mul' := fun _ _ => rfl }

variable {L}

def TrivAt (χ : Ideles L →* ℂˣ) (v : HeightOneSpectrum (𝓞 L)) : Prop :=
  ∀ x : (v.adicCompletion L)ˣ, χ (localIdele L v x) = 1

def UnrAt (χ : Ideles L →* ℂˣ) (v : HeightOneSpectrum (𝓞 L)) : Prop :=
  ∀ x : (v.adicCompletion L)ˣ, Valued.v (x : v.adicCompletion L) = 1 → χ (localIdele L v x) = 1

def DegOne (F : Type) [Field F] [NumberField F] [Algebra F L] (w : HeightOneSpectrum (𝓞 L)) : Prop :=
  ∀ y : 𝓞 L, ∃ u : 𝓞 F, y - algebraMap (𝓞 F) (𝓞 L) u ∈ w.asIdeal

variable (L)


open NumberField IsDedekindDomain in
variable (L : Type) [Field L] [NumberField L] in
variable {L} in
variable (L) in
theorem _root_.GlobalTheory.HeckeSplit.unrAt_iff (χ : _root_.Formalism.L2.Host.HChar L) (v : HeightOneSpectrum (𝓞 L)) :
    _root_.GlobalTheory.HeckeSplit.UnrAt χ.1 v ↔ χ.UnrAt v := by
  unfold _root_.GlobalTheory.HeckeSplit.UnrAt _root_.Formalism.L2.Host.HChar.UnrAt _root_.Formalism.L2.Host.IsUnitAt _root_.Formalism.L2.Host.HChar.loc
  rfl


open NumberField IsDedekindDomain in
variable (L : Type) [Field L] [NumberField L] in
variable {L} in
variable (L) in
theorem _root_.GlobalTheory.HeckeSplit.trivAt_iff (χ : _root_.Formalism.L2.Host.HChar L) (v : HeightOneSpectrum (𝓞 L)) :
    _root_.GlobalTheory.HeckeSplit.TrivAt χ.1 v ↔ χ.loc v = 1 := by
  unfold _root_.GlobalTheory.HeckeSplit.TrivAt
  rw [DFunLike.ext_iff]
  unfold _root_.Formalism.L2.Host.HChar.loc
  rfl


open NumberField IsDedekindDomain in
variable (L : Type) [Field L] [NumberField L] in
variable {L} in
variable (L) in
@[simp] theorem _root_.GlobalTheory.HeckeSplit.infPart_infIdele (x : (InfiniteAdeleRing L)ˣ) :
    _root_.GlobalTheory.HeckeSplit.infPart L (_root_.GlobalTheory.HeckeSplit.infIdele L x) = x :=
  Units.ext rfl


open NumberField IsDedekindDomain in
variable (L : Type) [Field L] [NumberField L] in
variable {L} in
variable (L) in
@[simp] theorem _root_.GlobalTheory.HeckeSplit.finPart_infIdele (v : HeightOneSpectrum (𝓞 L))
    (x : (InfiniteAdeleRing L)ˣ) :
    _root_.GlobalTheory.HeckeSplit.finPart L v (_root_.GlobalTheory.HeckeSplit.infIdele L x) = 1 :=
  Units.ext rfl


open NumberField IsDedekindDomain in
variable (L : Type) [Field L] [NumberField L] in
variable {L} in
variable (L) in
@[simp] theorem _root_.GlobalTheory.HeckeSplit.finPart_localIdele (v : HeightOneSpectrum (𝓞 L))
    (x : (v.adicCompletion L)ˣ) :
    _root_.GlobalTheory.HeckeSplit.finPart L v (_root_.HeckeValGen.localIdele L v x) = x :=
  Units.ext (_root_.Neutral.B1.localIdele_snd_self L v x)


open NumberField IsDedekindDomain in
variable (L : Type) [Field L] [NumberField L] in
variable {L} in
variable (L) in
@[simp] theorem _root_.GlobalTheory.HeckeSplit.infPart_localIdele (v : HeightOneSpectrum (𝓞 L))
    (x : (v.adicCompletion L)ˣ) :
    _root_.GlobalTheory.HeckeSplit.infPart L (_root_.HeckeValGen.localIdele L v x) = 1 :=
  Units.ext rfl


open NumberField IsDedekindDomain in
variable (L : Type) [Field L] [NumberField L] in
variable {L} in
variable (L) in
theorem _root_.GlobalTheory.HeckeSplit.finPart_localIdele_ne {v w : HeightOneSpectrum (𝓞 L)} (h : w ≠ v)
    (x : (v.adicCompletion L)ˣ) : _root_.GlobalTheory.HeckeSplit.finPart L w (_root_.HeckeValGen.localIdele L v x) = 1 :=
  Units.ext ((_root_.Neutral.B1.localIdele_isSupportedAt L v x).2 w h)

variable {L}

end GlobalTheory.HeckeSplit
end
end
