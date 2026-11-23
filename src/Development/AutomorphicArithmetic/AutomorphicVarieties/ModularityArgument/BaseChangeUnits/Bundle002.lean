module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle004
import Formalism.SharpRestriction.GrowthBounds.MonomialOrderSegments.BrData
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.SplitDescentOfImagQuadDescent
public import PositivityTheory.AutomorphicForms.PublishedInputs.CyclicBaseChangeLifts.SplitLift
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.SlopeTestRemainingChoices
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.CyclicBaseChangeC
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
import Mathlib.RingTheory.Ideal.Norm.RelNorm
import Mathlib.RingTheory.AdicCompletion.Noetherian
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
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.BcDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.RestrictionMemInvariantH1
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ConstSmall
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.Bundle001
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RedIdeal

@[expose] public section

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal
  GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Published UpperTheory.V.Base

private theorem normV_under {K K' : Type} [Field K] [NumberField K] [Field K'] [NumberField K'] [Algebra K K']
    (w : HeightOneSpectrum (𝓞 K')) : normV w = normV (w.under (𝓞 K)) ^ w.asIdeal.inertiaDeg (𝓞 K) := by
  have : w.asIdeal.LiesOver (w.under (𝓞 K)).asIdeal := ⟨rfl⟩
  have := w.isMaximal
  have := (w.under (𝓞 K)).isMaximal
  simp only [normV, ← Submodule.cardQuot_apply, ← Ideal.absNorm_apply]
  rw [← Ideal.absNorm_relNorm (𝓞 K) (𝓞 K') w.asIdeal,
    Ideal.relNorm_eq_pow_of_isMaximal w.asIdeal (w.under (𝓞 K)).asIdeal, map_pow]

private theorem algSat_pow (n q f : ℕ) (B : Multiset ℂˣ) :
    algSat n (q ^ f) (B.map (· ^ f)) = (algSat n q B).map (· ^ f) := by
  have e : ∀ (q : ℕ) (B : Multiset ℂˣ),
      algSat n q B = B.map fun α : ℂˣ => (((q : ℝ) ^ (((n : ℝ) - 1) / 2) : ℝ) : ℂ) * (α : ℂ) := fun q B => by
    simp only [algSat, Multiset.bind_def, Multiset.pure_def, Multiset.bind_singleton, Multiset.map_map, Function.comp_def]
  simp only [e, Multiset.map_map, Function.comp_def]
  refine Multiset.map_congr rfl fun α _ => ?_
  have h : (((q ^ f : ℕ) : ℝ)) ^ (((n : ℝ) - 1) / 2) = ((q : ℝ) ^ (((n : ℝ) - 1) / 2)) ^ f := by
    rw [Nat.cast_pow, ← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg q),
      ← Real.rpow_mul (Nat.cast_nonneg q), mul_comm]
  rw [h, mul_pow, Units.val_pow_eq_pow_val, Complex.ofReal_pow]

end

section

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.GalOfCusp
open UpperTheory.V.Af UpperTheory.V.Sd UpperTheory.V.Ws UpperTheory.V.Published UpperTheory.V.Base

namespace UpperTheory.V.Z.Bc

section Sys

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def IndSys (sat : HeightOneSpectrum (𝓞 E) → Multiset ℂˣ → Prop) (satP : HeightOneSpectrum (𝓞 F) → Multiset ℂˣ → Prop) : Prop :=
  ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite,
    (∀ w' : HeightOneSpectrum (𝓞 E), w' ≠ w → w'.under (𝓞 F) = w.under (𝓞 F) →
      ∃ B B', sat w B ∧ sat w' B' ∧ satP (w.under (𝓞 F)) (B + B')) ∧
    (normV w = normV (w.under (𝓞 F)) ^ 2 → ∃ B B' : Multiset ℂˣ, sat w (B'.map (· ^ 2)) ∧
      B = B' + B'.map (fun b => -b) ∧ satP (w.under (𝓞 F)) B)

end Sys

def IndCh {Γ Γ' k : Type} [Group Γ] [Group Γ'] [Field k] (e : Γ' →* Γ) (r : Γ' →* GL (Fin 2) k) (R : Γ →* GL (Fin 4) k) : Prop :=
  ∀ t : Γ, t ∉ e.range →
    (∀ g g' : Γ', e g' = t⁻¹ * e g * t → (R (e g) : Matrix (Fin 4) (Fin 4) k).charpoly =
      (r g : Matrix (Fin 2) (Fin 2) k).charpoly * (r g' : Matrix (Fin 2) (Fin 2) k).charpoly) ∧
    ∀ g : Γ', e g = t * t →
      (R t : Matrix (Fin 4) (Fin 4) k).charpoly = (r g : Matrix (Fin 2) (Fin 2) k).charpoly.comp (X ^ 2)

section Defs

variable {E : Type} [Field E] [NumberField E] [IsTotallyReal E]

def MixWt (π : TR.CuspSub E 2) : Prop :=
  ∃ (m m' : Fin 2 → ℤ) (v v' : InfinitePlace E), v ≠ v' ∧ π.HasInfChar v (infOf m) ∧ π.HasInfChar v' (infOf m') ∧
    Function.Injective ![m 0, m 1, m' 0, m' 1]

end Defs

def MixWtC (K : Type) [Field K] {M : Type} [Field M] [NumberField M] [_root_.NumberField.IsTotallyComplex M] [Algebra K M] (π : CuspSub M 2) : Prop :=
  ∀ φ : K →+* ℂ, ∃ (m m' : Fin 2 → ℤ) (τ τ' : M →+* ℂ), τ ≠ τ' ∧ τ.comp (algebraMap K M) = φ ∧ τ'.comp (algebraMap K M) = φ ∧
    π.HasInfChar τ (infOf m) ∧ π.HasInfChar τ' (infOf m') ∧ Function.Injective ![m 0, m 1, m' 0, m' 1]

def IndAutC : Prop :=
  ∀ (K M Ω : Type) [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] [Field M] [NumberField M] [_root_.NumberField.IsTotallyComplex M] [Field Ω]
    [Algebra K M] [Algebra K Ω] [Algebra M Ω] [IsScalarTower K M Ω] [IsAlgClosure M Ω], Module.finrank K M = 2 →
    ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (π : CuspSub M 2) (r : _root_.Formalism.ConjugateSelfDual.G M Ω →* GL (Fin 2) (Qbar l)), AttC ι r π → MixWtC K π →
    ∀ R : _root_.Formalism.ConjugateSelfDual.G K Ω →* GL (Fin 4) (Qbar l), IsSSRep R → IndCh (galEmb K M Ω) r R → IsAutC ι R

def UpQuadI : Prop :=
  ∀ (F E Ω : Type) [Field F] [NumberField F] [IsTotallyReal F] [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] [Field Ω] [Algebra F E]
    [Algebra F Ω] [Algebra E Ω] [IsScalarTower F E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ),
    Module.finrank F E = 2 → ∀ (r : _root_.Formalism.ConjugateSelfDual.G F Ω →* GL (Fin 2) (Qbar l)) (π : TR.CuspSub F 2), Continuous r → π.IsRegAlg → AttR ι r π →
      IsIrr (r.comp (galEmb F E Ω)) → ∃ P : CuspSub E 2, (CG.mk P).IsRegAlg ∧ AttC ι (r.comp (galEmb F E Ω)) P ∧
        ∀ (τ : E →+* ℂ) m, π.HasInfChar (InfinitePlace.mk (τ.comp (algebraMap F E))) m → P.HasInfChar τ m

def UpSolI : Prop :=
  ∀ (F E Ω : Type) [Field F] [NumberField F] [_root_.NumberField.IsTotallyComplex F] [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] [Field Ω] [Algebra F E]
    [Algebra F Ω] [Algebra E Ω] [IsScalarTower F E Ω] [IsAlgClosure E Ω] [IsGalois F E] [Group.IsSolvable (E ≃ₐ[F] E)] (l : ℕ) [Fact l.Prime]
    (ι : Qbar l ≃+* ℂ) (r : _root_.Formalism.ConjugateSelfDual.G F Ω →* GL (Fin 2) (Qbar l)) (π : CuspSub F 2), Continuous r → (CG.mk π).IsRegAlg → AttC ι r π →
      IsIrr (r.comp (galEmb F E Ω)) → ∃ P : CuspSub E 2, (CG.mk P).IsRegAlg ∧ AttC ι (r.comp (galEmb F E Ω)) P ∧
        ∀ (τ : E →+* ℂ) m, π.HasInfChar (τ.comp (algebraMap F E)) m → P.HasInfChar τ m

def AttInd : Prop :=
  ∀ (F E Ω : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Field Ω] [Algebra F E] [Algebra F Ω] [Algebra E Ω]
    [IsScalarTower F E Ω] [IsAlgClosure E Ω], Module.finrank F E = 2 → ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ)
    (r : _root_.Formalism.ConjugateSelfDual.G E Ω →* GL (Fin 2) (Qbar l)) (R : _root_.Formalism.ConjugateSelfDual.G F Ω →* GL (Fin 4) (Qbar l)) sat satP, (∀ w B B', sat w B → sat w B' → B = B') →
    (∀ w B B', satP w B → satP w B' → B = B') → AttachedSys ι r sat → IndSys (F := F) (E := E) sat satP → IsSSRep R →
    IndCh (galEmb F E Ω) r R → AttachedSys ι (tw R (cycBar F Ω l)⁻¹) satP

end UpperTheory.V.Z.Bc

end
end

section

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af

namespace UpperTheory.V.Z.Bc

def Down2 : Prop :=
  ∀ (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [IsAbelianGalois ℚ L] [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω]
    [Algebra L Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (W : G ℚ Ω →* GL (Fin 2) (Qbar l)), Continuous W →
    IsCycWt l 0 (Matrix.GeneralLinearGroup.det.comp W) → IsIrr (W.comp (resG ℚ L Ω)) →
    (∃ (η : G ℚ Ω →* ℤˣ) (σ : G ℚ Ω), IsConjEl σ ∧ η σ = -1 ∧ ∀ s : G L Ω, η (resG ℚ L Ω s) = 1) →
    (∃ π : CuspSub L 2, (CG.mk π).IsRegAlg ∧ AttC ι (W.comp (resG ℚ L Ω)) π) → IsAutR ι W

def Desc2 : Prop := DescS ∨ Down2

end UpperTheory.V.Z.Bc
end
end

section

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published UpperTheory.CBC

namespace UpperTheory.V.Z.Bc

def CBCc : Prop :=
  ∀ (K M : Type) [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M] [IsGalois K M],
    (Module.finrank K M).Prime → IsTotallyComplex K → ∀ n : ℕ, 1 ≤ n →
      (∀ π : Cusp K n, (∃ η : HChar K, IsNormChar M η ∧ (π.twist η).Iso π) ∨
        ∃ P : Cusp M n, WeakBC π.sat P.sat ∧ (∀ τ m, π.inf (τ.comp (algebraMap K M)) m → P.inf τ m) ∧ SplitLift π P) ∧
      (∀ P : Cusp M n, (∀ σ : M ≃ₐ[K] M, P.ConjIso σ.toRingEquiv) →
        ∃ π : Cusp K n, WeakBC π.sat P.sat ∧ (∀ τ m, P.inf τ m → π.inf (τ.comp (algebraMap K M)) m) ∧ SplitLift π P) ∧
      ∀ (π : Cusp K n) (P : Cusp M n), (∀ σ : M ≃ₐ[K] M, P.ConjIso σ.toRingEquiv) → WeakBC π.sat P.sat →
        (∀ η : HChar K, IsNormChar M η → ¬ (π.twist η).Iso π) ∧
        ∀ π₁ : Cusp K n, WeakBC π₁.sat P.sat → ∃ η : HChar K, (η = 1 ∨ IsNormChar M η) ∧ (π.twist η).Iso π₁

def CBCr : Prop :=
  ∀ (K M : Type) [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M] [IsGalois K M],
    (Module.finrank K M).Prime → IsTotallyComplex K → ∀ n : ℕ, 1 ≤ n →
      (∀ π : Cusp K n, RegInf n π.inf → (∃ η : HChar K, IsNormChar M η ∧ (π.twist η).Iso π) ∨
        ∃ P : Cusp M n, WeakBC π.sat P.sat ∧ ∀ τ m, π.inf (τ.comp (algebraMap K M)) m → P.inf τ m) ∧
      (∀ P : Cusp M n, RegInf n P.inf → (∀ σ : M ≃ₐ[K] M, P.ConjIso σ.toRingEquiv) →
        ∃ π : Cusp K n, WeakBC π.sat P.sat ∧ ∀ τ m, P.inf τ m → π.inf (τ.comp (algebraMap K M)) m) ∧
      ∀ (π : Cusp K n) (P : Cusp M n), (∀ σ : M ≃ₐ[K] M, P.ConjIso σ.toRingEquiv) → WeakBC π.sat P.sat →
        ∀ π₁ : Cusp K n, WeakBC π₁.sat P.sat → ∃ η : HChar K, (η = 1 ∨ IsNormChar M η) ∧ (π.twist η).Iso π₁

theorem cbcr_of_cbcc (h : CBCc) : CBCr := by
  intro K M _ _ _ _ _ _ hp hK n hn
  obtain ⟨a, b, c⟩ := h K M hp hK n hn
  refine ⟨fun π _ => (a π).imp_right fun ⟨P, h1, h2, _⟩ => ⟨P, h1, h2⟩, fun P _ hP => ?_, fun π P h1 h2 => (c π P h1 h2).2⟩
  obtain ⟨π, h1, h2, _⟩ := b P hP
  exact ⟨π, h1, h2⟩

end UpperTheory.V.Z.Bc
end
end
