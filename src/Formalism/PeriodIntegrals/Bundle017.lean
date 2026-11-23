module

public import Formalism.SharpRestriction.CuspSpanNormBounds.LinQRawRange
public import Formalism.LocalToGlobal.SiegelLatticeTheory.SiegelMassRatios.DensExact
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Mathlib.RingTheory.DedekindDomain.Different
import Mathlib.Algebra.AffineMonoid.Basic
public import Formalism.YangianSpanCharacter.Bundle001
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
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
import Mathlib.Topology.Sheaves.Init
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
import Formalism.HermitianCurvature.StatementW

@[expose] public section

section

open ValuativeRel Classical

noncomputable section

namespace PI.LocDensCorank

open Formalism.MainNotions.S

def LocDensCorank : Prop :=
  ∀ (F E : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E] [Algebra F E]
    [TopologicalSpace E] [MeasurableSpace E] (M : Loc.Model F E),
    IsNonarchimedeanLocalField F → CharZero F →
    ∀ (V : Type) [AddCommGroup V] [Module E V] (H : Loc.HermSp M V) (Λ : Submodule M.L.O V),
      H.IsSelfDual Λ → ∀ ϖ : 𝒪[F], Irreducible ϖ →
      ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (A : Matrix ι ι E) (a : ι → 𝒪[F]),
        (∀ i j, A i j ∈ M.L.O) → (∃ y ∈ M.L.O, A.det * y = 1) →
        Fintype.card ι ≤ Module.finrank E V →
          H.dens ϖ Λ ((A.map M.L.cj).transpose * Matrix.diagonal (fun i => algebraMap F E (a i : F)) * A) =
            Formalism.L2.SG.DensExact.densProd (Nat.card 𝓀[F]) (if ∀ x : E, x ≠ 0 → IsUnit x then -1 else 1)
              (Module.finrank E V) (Fintype.card ι) (Finset.univ.filter fun i => ϖ ∣ a i).card

end PI.LocDensCorank
end
end

section

noncomputable section

namespace PI.SelfDualBridge

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory NumberField IsDedekindDomain
open scoped TensorProduct Classical

section Meas

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F))

def IsStdChar (ψ : AddChar (AF F) ℂ) : Prop :=
  ∀ x : Ainf F, psiInf F ψ x =
    Complex.exp (2 * Real.pi * Complex.I *
      ((∑ w : NumberField.InfinitePlace F, (NumberField.InfinitePlace.Completion.extensionEmbedding w (x w)).re : ℝ) : ℂ))

def StdHyp : Prop := IsCMExt F E σ ∧ IsHermND σ J ∧ IsCharAF F ψ ∧ IsStdChar ψ

def SdExists (a : ℕ) (ι : Type) [Fintype ι] : Prop :=
  StdHyp σ J ψ → (∃ μ, SdW F E σ n J (Fv F v) (psiV F ψ v) a μ) ∧ (∃ ν, SdHerm F E σ (Fv F v) (psiV F ψ v) a ν) ∧
  ∃ μ : Measure (ι → Fv F v ⊗[F] E), SelfDual μ
      (fun x y => psiV F ψ v (∑ i, Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (x i * y i)))

end Meas

end PI.SelfDualBridge
end
end

section

noncomputable section

open MeasureTheory NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

namespace PI.StdCharTR

def Target : Prop :=
  ∀ (F : Type) [Field F] [NumberField F], NumberField.IsTotallyReal F → ∃ ψ : AddChar (AF F) ℂ, IsCharAF F ψ ∧
    ∀ x : Ainf F, psiInf F ψ x =
      Complex.exp (2 * Real.pi * Complex.I *
        ((∑ w : InfinitePlace F, (InfinitePlace.Completion.extensionEmbedding w (x w)).re : ℝ) : ℂ))

end PI.StdCharTR
end
end

section

noncomputable section

namespace PI.LocJacTyp

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory NumberField IsDedekindDomain
open scoped TensorProduct Classical

section Meas

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F))

def sdE (ι : Type) [Fintype ι] : Measure (ι → Fv F v ⊗[F] E) :=
  if h : ∃ μ : Measure (ι → Fv F v ⊗[F] E), SelfDual μ
      (fun x y => psiV F ψ v (∑ i, Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (x i * y i)))
  then h.choose else 0

end Meas

section Frames

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F))

def OEv : Set (Fv F v ⊗[F] E) :=
  SetLike.coe (Submodule.span (v.adicCompletionIntegers F)
    ((fun x : 𝓞 E => inclR (F := F) (Fv F v) (x : E)) '' Set.univ))

def sc (x : Fv F v) : Fv F v ⊗[F] E := x ⊗ₜ[F] (1 : E)

def IsDiffVal (d : Fv F v) : Prop :=
  d ≠ 0 ∧ (∀ x ∈ differentIdeal ℤ (𝓞 F), Valued.v (algebraMap F (Fv F v) (x : F)) ≤ Valued.v d) ∧
    ∃ x ∈ differentIdeal ℤ (𝓞 F), Valued.v (algebraMap F (Fv F v) (x : F)) = Valued.v d

def dV : Fv F v := if h : ∃ d, IsDiffVal v d then h.choose else 1

def alp (r : ℕ) (a : Fin (r + 1)) : Fv F v := if (a : ℕ) < r then (dV v)⁻¹ ^ (r - (a : ℕ)) else 1

end Frames

section Sets

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F)) (Λ : Set (Fin n → E))

def PPTyp (g r T T' : ℕ) (l : Fin (r + 1)) : Set (Fv F v ⊗[F] E) :=
  if (l : ℕ) < r then
    {c | sc (E := E) v (alp v r l ^ 2 * (g : Fv F v)⁻¹) * c ∈ OEv (E := E) v ∧
      sc (E := E) v (alp v r l ^ 2 * ((g : Fv F v)⁻¹) ^ 2) * (c + sigR (Fv F v) σ c) ∈ OEv (E := E) v}
  else
    {c | sc (E := E) v (g : Fv F v)⁻¹ * (c + (T : Fv F v ⊗[F] E)) ∈ OEv (E := E) v ∧
      sc (E := E) v (((g : Fv F v)⁻¹) ^ 2) * (c + sigR (Fv F v) σ c + (T : Fv F v ⊗[F] E) + (T' : Fv F v ⊗[F] E))
        ∈ OEv (E := E) v}

def absV (x : Fv F v) : ℝ :=
  if h : Valued.v x = 0 then 0
  else ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (Multiplicative.toAdd (WithZero.unzero h))

end Sets

section Stmt

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) (ψ : AddChar (AF F) ℂ) (v : HeightOneSpectrum (𝓞 F))

end Stmt

end PI.LocJacTyp
end
end

section

open Matrix Finset

noncomputable section

namespace PI

open Formalism Formalism.FourierDecayAlt

def RTTSandwich : Prop :=
  ∀ (A : Type) [Ring A] [Algebra ℂ A] (QQ : ℂ → Matrix (Fin 2) (Fin 2) A) (p c ci p' c' ci' : A),
    YangianSpanCharacter.T.WeylRel p c ci → YangianSpanCharacter.T.WeylRel p' c' ci' →
    (∀ x ∈ ({p, c, ci} : Set A), ∀ y ∈ ({p', c', ci'} : Set A), x * y = y * x) →
    (∀ x ∈ ({p, c, ci, p', c', ci'} : Set A), ∀ Y a b, x * QQ Y a b = QQ Y a b * x) →
    ∀ Y Y' : ℂ,
      let C : ℂ → A := fun y => (YangianSpanCharacter.T.Tm y p' c' ci' * QQ y * YangianSpanCharacter.T.Tm y p c ci) 0 0
      let X : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) A :=
        ((Y' - Y) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) A) - YangianSpanCharacter.T.Pf A) * YangianSpanCharacter.T.E1 (QQ Y') * YangianSpanCharacter.T.E2 (QQ Y) -
          YangianSpanCharacter.T.E2 (QQ Y) * YangianSpanCharacter.T.E1 (QQ Y') * ((Y' - Y) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) A) - YangianSpanCharacter.T.Pf A)
      algebraMap ℂ A (Y' - Y - 1) * (C Y' * C Y - C Y * C Y') =
        ((YangianSpanCharacter.T.T2 Y p' c' ci' * YangianSpanCharacter.T.T1 Y' p' c' ci') * X * (YangianSpanCharacter.T.T1 Y' p c ci * YangianSpanCharacter.T.T2 Y p c ci)) (0, 0) (0, 0)

def RTTIndependence : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (x : Fin 2 × Fin 2 → Fin 2 × Fin 2 → V) (Y Y' : ℂ), Y' ≠ Y + 1 →
    (∀ (c : ℂ), c ≠ 0 → ∀ (β : ℂ) (n : ℤ),
      ∑ A : Fin 2 × Fin 2, ∑ B : Fin 2 × Fin 2,
        ((if A = (0, 0) then (Y - β) * (Y' - β) else if A = (0, 1) then Y' - β else if A = (1, 0) then Y - β + 1 else 1) *
          (if B = (0, 0) then (Y' + (β + n)) * (Y + (β + n)) else if B = (0, 1) then Y' + (β + n) - 1
            else if B = (1, 0) then Y + (β + n) else 1) *
          (((‖c‖ : ℂ) ^ (2 * β)) * c ^ n * (c ^ ((B.1 : ℕ) + (B.2 : ℕ)))⁻¹ * (star c ^ ((A.1 : ℕ) + (A.2 : ℕ)))⁻¹)) • x A B = 0) →
    ∀ A B, x A B = 0

end PI
end
end
