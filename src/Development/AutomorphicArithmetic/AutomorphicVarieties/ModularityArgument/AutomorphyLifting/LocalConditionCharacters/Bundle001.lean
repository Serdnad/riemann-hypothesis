module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.RatTorsionFree
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.WeakOfAtt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.Bundle001
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.OrdZero
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.SphericalOfHasSat

@[expose] public section

section

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base

namespace UpperTheory.V.Z.Win.RR

def WitUp {Ω : Type} [Field Ω] [CharZero Ω] {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (W : G ℚ Ω →* GL (Fin 2) (Qbar l)) : Prop :=
  IsCycWt l 0 (Matrix.GeneralLinearGroup.det.comp W) ∧
    ∃ (L : Type) (_ : Field L) (_ : NumberField L) (_ : IsCMField L) (_ : IsAbelianGalois ℚ L) (_ : Algebra L Ω),
      IsIrr (W.comp (galEmb ℚ L Ω)) ∧
      (∃ (η : G ℚ Ω →* ℤˣ) (σ : G ℚ Ω), Sd.IsCC σ ∧ η σ = -1 ∧ ∀ s : G L Ω, η (galEmb ℚ L Ω s) = 1) ∧
      ∃ ka : G L Ω →* (Qbar l)ˣ, Sd.IsAlgChar ι ka ∧ WitA ι (tw (W.comp (galEmb ℚ L Ω)) ka)

def AutNewformA : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (e : ℕ), 1 ≤ e →
    ∀ W : G ℚ Ω →* GL (Fin 2) (Qbar l), Continuous W → IsIrr W → IsAutR ι W → WitUp ι W →
    ∀ (B : ValuationSubring Ω), B.valuation (l : Ω) < 1 → ∀ (H : Subgroup (G ℚ Ω)), IsOpen (H : Set (G ℚ Ω)) →
    IsFlagOn W (H ⊓ Ine (F := ℚ) B) (fun i => ((cycBar ℚ Ω l) ^ (![(e : ℤ), -(e : ℤ)] i)).comp (H ⊓ Ine (F := ℚ) B).subtype) →
    ∃ f : Newform (2 * e + 1), f.Att ι (tw W (cycBar ℚ Ω l ^ (-(e : ℤ))))

end UpperTheory.V.Z.Win.RR
end
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Th
open UpperTheory.GalN.V UpperTheory.Zero.LLC UpperTheory.V.Z.Win
open scoped Pointwise
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Z.Win.RR

theorem local_condition_of_flag_of_characters_not_cyclotomic_shift {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime] {n : ℕ}
    {r : _root_.Formalism.ConjugateSelfDual.G F Ω →* GL (Fin n) (Qbar l)} {w : HeightOneSpectrum (𝓞 F)} {A : ValuationSubring Ω} (h : _root_.Formalism.ConjugateSelfDual.IsPlaceOver A w)
    {ψ : Fin n → _root_.ReciprocityTheory.Gal.Dec (F := F) A →* (Qbar l)ˣ} (hf : W.HasFlag (r.comp (_root_.ReciprocityTheory.Gal.Dec (F := F) A).subtype) ψ)
    (hg : ∀ i j, ψ i ≠ ψ j * (cycBar F Ω l).comp (_root_.ReciprocityTheory.Gal.Dec (F := F) A).subtype) : Unl1 r w := by
  intro B hB
  obtain ⟨g, rfl⟩ := exists_smul_eq_of_isPlaceOver (F := F) h hB
  have m1 : ∀ s : ↥(_root_.ReciprocityTheory.Gal.Dec (F := F) (g • A)), g⁻¹ * (s : _root_.Formalism.ConjugateSelfDual.G F Ω) * g ∈ _root_.ReciprocityTheory.Gal.Dec (F := F) A := fun s => by
    have h1 : (s : _root_.Formalism.ConjugateSelfDual.G F Ω) • g • A = g • A := s.2
    show (g⁻¹ * (s : _root_.Formalism.ConjugateSelfDual.G F Ω) * g) • A = A
    rw [mul_smul, mul_smul, h1, inv_smul_smul]
  have m2 : ∀ s : ↥(_root_.ReciprocityTheory.Gal.Dec (F := F) A), g * (s : _root_.Formalism.ConjugateSelfDual.G F Ω) * g⁻¹ ∈ _root_.ReciprocityTheory.Gal.Dec (F := F) (g • A) := fun s => by
    have h1 : (s : _root_.Formalism.ConjugateSelfDual.G F Ω) • A = A := s.2
    show (g * (s : _root_.Formalism.ConjugateSelfDual.G F Ω) * g⁻¹) • g • A = g • A
    rw [mul_smul, mul_smul, inv_smul_smul, h1]
  let c : ↥(_root_.ReciprocityTheory.Gal.Dec (F := F) (g • A)) →* ↥(_root_.ReciprocityTheory.Gal.Dec (F := F) A) :=
    MonoidHom.mk' (fun s => ⟨_, m1 s⟩) fun s t => Subtype.ext (by simp only [Subgroup.coe_mul]; group)
  obtain ⟨p, hp⟩ := hf
  refine ⟨fun i => (ψ i).comp c, ⟨p * (r g)⁻¹, fun s => ?_⟩, fun i j e => hg i j (MonoidHom.ext fun s => ?_)⟩
  · have e1 : p * (r g)⁻¹ * r s * (p * (r g)⁻¹)⁻¹ = p * r (g⁻¹ * (s : _root_.Formalism.ConjugateSelfDual.G F Ω) * g) * p⁻¹ := by
      rw [map_mul, map_mul, map_inv]; group
    rw [e1]
    exact hp (c s)
  · have e2 := DFunLike.congr_fun e ⟨_, m2 s⟩
    have e3 : c ⟨_, m2 s⟩ = s := Subtype.ext (by
      show g⁻¹ * (g * (s : _root_.Formalism.ConjugateSelfDual.G F Ω) * g⁻¹) * g = s
      group)
    change ψ i (c ⟨_, m2 s⟩) = ψ j (c ⟨_, m2 s⟩) * cycBar F Ω l (g * (s : _root_.Formalism.ConjugateSelfDual.G F Ω) * g⁻¹) at e2
    rw [e3, map_mul (cycBar F Ω l), map_mul (cycBar F Ω l), map_inv, mul_inv_cancel_comm] at e2
    exact e2

def AutPA {K Ω : Type} [Field K] [NumberField K] [IsCMField K] [Field Ω] [Algebra K Ω] {l : ℕ} [Fact l.Prime] {n : ℕ}
    (ι : Qbar l ≃+* ℂ) (r : _root_.Formalism.ConjugateSelfDual.G K Ω →* GL (Fin n) (Qbar l)) : Prop :=
  AutP ι r ∧ (Continuous r → WitA ι r)

end UpperTheory.V.Z.Win.RR
end
