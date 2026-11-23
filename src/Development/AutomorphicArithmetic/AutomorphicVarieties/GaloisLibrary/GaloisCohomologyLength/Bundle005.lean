module

public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle003
public import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.TotallyRealRoots.Bundle001
public import Formalism.GaloisCohomology.LocalTateDualityK
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LengthEqLengthInvariantsOfTorsionLevels
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.GaloisCohomologyLength.LevelInertiaLeLevelDec
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.GaloisCohomologyLength.GalTransport
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.GaloisCohomologyLength.InfUnram
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.GaloisCohomologyLength.NonemptyH0GlobalEquivGaloisImage
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.GaloisCohomologyLength.Bundle003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.GaloisCohomologyLength.Bundle001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.GaloisCohomologyLength.ShaInfl
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
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.GaloisCohomology

noncomputable section

namespace UpperTheory.V.LDataCardLeFinrank

section

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime]

theorem vFormula_of_classicalTheorems (hP : GlobalTheory.Published.PoitouTateDuality) (hF : LocalFinitenessK) (hT : LocalTateDualityK)
    (hc : PTCase F l) (D : LData F Ω l) (e : ℤ) :
    VLen D e + KStar.TotallyRealRoots.nuGal l F e.natAbs = shaLen D e + sumLocalH0TwistLength D e := by
  have hfl := fun r (hr : 0 < r) => GlobalTheory.TateLimit.finite_level D e hP hc r hr
  have hcok := GlobalTheory.TateLimit.ptCokerAt D e hF hT (fun r hr => (hfl r hr).1)
    (fun r hr => (hfl r hr).2.1) (hfl 1 one_pos).2.2
  have hsha := GlobalTheory.TateLimit.ptShaAt D e hF hT (fun r hr => (hfl r hr).1)
    (fun r hr => (hfl r hr).2.1) (hfl 1 one_pos).2.2
  have length_add_coker {R X Y : Type} [CommRing R] [AddCommGroup X] [Module R X]
      [AddCommGroup Y] [Module R Y] (f : X →ₗ[R] Y) :
      Module.length R X + Module.length R (Y ⧸ LinearMap.range f) =
        Module.length R (LinearMap.ker f) + Module.length R Y := by
    have hX := Module.length_eq_add_of_exact (LinearMap.ker f).subtype (LinearMap.ker f).mkQ
      (Submodule.injective_subtype _) (Submodule.mkQ_surjective _) (LinearMap.exact_subtype_mkQ _)
    have hY := Module.length_eq_add_of_exact (LinearMap.range f).subtype (LinearMap.range f).mkQ
      (Submodule.injective_subtype _) (Submodule.mkQ_surjective _) (LinearMap.exact_subtype_mkQ _)
    rw [hX, hY, (f.quotKerEquivRange).length_eq, add_assoc]
  have h : Formalism.GaloisCohomology.VFormula := by
    intro F Ω _ _ _ _ _ l _ D e hcase hcoker hsha hloc
    have hker : LinearMap.ker (localH2 D e) = Sha2Zl D e := by
      unfold localH2
      rw [LinearMap.ker_pi]
      rfl
    have key := length_add_coker (localH2 D e)
    rw [hcoker hcase, hker, hsha hcase, Module.length_pi_of_fintype] at key
    unfold VLen sumLocalH0TwistLength
    rw [key]
    congr 1
    exact Finset.sum_congr rfl (fun v _ => hloc v)
  have h := h F Ω l D e hc hcok hsha (GlobalTheory.TateLimit.local_tate_duality_h2_limit hF hT D e)
  rwa [length_H0_global_eq_nu] at h

theorem ptCase_of_isTotallyComplex (F : Type) [Field F] [NumberField F] [_root_.NumberField.IsTotallyComplex F] (l : ℕ) : PTCase F l :=
  Or.inr (NumberField.nrRealPlaces_eq_zero_iff.2 inferInstance)

theorem VLen_le_shaLen_add (hP : GlobalTheory.Published.PoitouTateDuality) (hF : LocalFinitenessK) (hT : LocalTateDualityK)
    (hc : PTCase F l) (D : LData F Ω l) (e : ℤ) : VLen D e ≤ shaLen D e + sumLocalH0TwistLength D e := by
  rw [← vFormula_of_classicalTheorems hP hF hT hc]
  exact le_self_add

end

end UpperTheory.V.LDataCardLeFinrank

end
end

section

open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.GaloisCohomology

noncomputable section

namespace UpperTheory.V.LDataCardLeFinrank

section

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime]

theorem map_Sha (D : LData F Ω l) (e : ℤ) :
    (Sha D e).map (resH1 (qzTw D e) (toGS Ω _) (continuous_toGS Ω _)) =
      ShaAbs ((qzTw D e).comp (toGS Ω _)) (Above F l) := by
  rw [← D.hS]
  exact shaInfl F Ω D.S D.A D.hA _ _ _ (contTw F Ω l D e).1

theorem injective_infl (D : LData F Ω l) (e : ℤ) :
    Function.Injective (resH1 (qzTw D e) (toGS Ω _) (continuous_toGS Ω _)) :=
  (infUnram F Ω _ _ _ _ (contTw F Ω l D e).1).1

theorem shaLen_eq_abs (D : LData F Ω l) (e : ℤ) :
    shaLen D e = Module.length ℤ_[l] (ShaAbs (qzG F Ω l e) (Above F l)) := by
  rw [← qzTw_comp_toGS D e, ← map_Sha]
  exact (Submodule.equivMapOfInjective _ (injective_infl D e) _).length_eq

variable {F' Ω' : Type} [Field F'] [NumberField F'] [Field Ω'] [Algebra F' Ω'] [IsAlgClosure F' Ω']

theorem length_ShaAbs_le (f : F ≃+* F') (e : ℤ) :
    Module.length ℤ_[l] (ShaAbs (qzG F Ω l e) (Above F l)) ≤
      Module.length ℤ_[l] (ShaAbs (qzG F' Ω' l e) (Above F' l)) := by
  let σ : Ω ≃+* Ω' := IsAlgClosure.equivOfEquiv Ω Ω' f
  have hσ : ∀ x, σ (algebraMap F Ω x) = algebraMap F' Ω' (f.toRingHom x) :=
    fun x => IsAlgClosure.equivOfEquiv_algebraMap Ω Ω' f x
  obtain ⟨φ, h1, h2, h3, -, h5⟩ := galTransport F Ω F' Ω' f.toRingHom σ hσ
  have e1 : (qzG F Ω l e).comp φ = qzG F' Ω' l e := by
    refine MonoidHom.ext fun g => LinearMap.ext fun x => ?_
    rw [MonoidHom.comp_apply, qzG_apply, qzG_apply, h3]
  rw [← e1]
  refine (shaAbsRes F Ω F' Ω' _ _ φ h1 (fun v' A' hA' => ?_) _ _ _).2 (h5 f.surjective)
  obtain ⟨v, A, a, b, -, c, d⟩ := placeTransport F Ω F' Ω' f.toRingHom σ hσ φ h2 v' A' hA'
  exact ⟨v, A, a, b l, fun g hg => (c g).2 hg, fun g hg => (d g).2 hg⟩

theorem shaLen_eq_shaInv (D : LData F Ω l) (e : ℤ) : shaLen D e = shaInv F l e := by
  rw [shaLen_eq_abs]
  exact le_antisymm (length_ShaAbs_le (RingEquiv.refl F) e) (length_ShaAbs_le (RingEquiv.refl F) e)

theorem shaInv_congr (f : F ≃+* F') (e : ℤ) : shaInv F l e = shaInv F' l e :=
  le_antisymm (length_ShaAbs_le f e) (length_ShaAbs_le f.symm e)

end

end UpperTheory.V.LDataCardLeFinrank

end
end
