module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsGtExtOfTorsion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle002
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle089
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle101
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle038
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFacOfClosedPoint
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsLineBundleOfNormOneGenerators
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle123
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle110
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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

@[expose] public section

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory

namespace GlobalTheory.QkDescent

theorem exists_qkExt_of_isAlgClosed : Laws → ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (D : DegPre R), D.TauBimult → ∀ (F F' : Type) [Field F] [IsAlgClosed F] [CharZero F] [Field F'] [IsAlgClosed F'] [Algebra (FractionRing R) F] [Algebra (FractionRing R) F'] (f : F →+* F'), f.comp (algebraMap (FractionRing R) F) = algebraMap (FractionRing R) F' → ∀ k : ℕ, 1 ≤ k → ∀ p' : QkPt D F' k, ∃ p : QkPt D F k, QkExt f p p' := by
  intro hL R _ _ _ D hB F F' _ _ _ _ _ _ _ f hf k hk p'
  have hk' : (k : F) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  letI := GlobalTheory.TorusExt.gtGroup (D := D) (F := F)
  letI := GlobalTheory.TorusExt.gtGroup (D := D) (F := F')
  have hk0 : k ≠ 0 := by omega
  obtain ⟨q, hq⟩ := GlobalTheory.TorusExt.exists_qkPt (F := F) hL.mulN (Or.inr hL.polBaseChange) hB hk0 p'.y
  obtain ⟨h₀, h₁, h₂⟩ := q.eq
  obtain rfl := (GlobalTheory.TorusExt.isNsmul_iff_eq _ _ _).1 h₁
  obtain ⟨h', h₁', h₂'⟩ := p'.eq
  obtain rfl := (GlobalTheory.TorusExt.isNsmul_iff_eq _ _ _).1 h₁'
  have hh₀ : GtPtF.IsIota p'.y (k • q.g) := hq ▸ h₂
  have hext : GtPtF.IsIota p'.y (GlobalTheory.TorusExt.gtExt D f hf (k • q.g)) := by
    obtain ⟨b, -⟩ := (GlobalTheory.TorusExt.isIota_iff_val _ _).1 hh₀
    refine (GlobalTheory.TorusExt.isIota_iff_val _ _).2 ⟨by rw [GlobalTheory.TorusExt.gtExt_b, b, ReciprocityTheory.ChartRestriction.G.DVR.comp_cP], fun χ y J hJ => ?_⟩
    rw [GlobalTheory.TorusExt.gtExt_val f hf _ χ hJ, GlobalTheory.TorusExt.tauVal, ← GlobalTheory.TorusExt.extMap_jFK f hf]
    exact (val_corr hJ (hh₀.2 χ) _).trans (val_pull hJ _ _ _)
  have e₀ : GlobalTheory.TorusExt.gtExt D f hf (k • q.g) = k • p'.g := GlobalTheory.TorusExt.isIota_unique hext h₂'
  have ht' : k • (p'.g - GlobalTheory.TorusExt.gtExt D f hf q.g) = 0 := by
    rw [nsmul_sub, ← map_nsmul, e₀, sub_self]
  obtain ⟨t, ht⟩ := GlobalTheory.ArcExt.exists_gtExt_of_torsion f hf hL hk' _ ht'
  have ht0 : k • t = 0 := GlobalTheory.ArcExt.gtExt_injective f hf (by rw [map_nsmul, ht, ht', map_zero])
  have e : p'.g = GlobalTheory.TorusExt.gtExt D f hf (q.g + t) := by rw [map_add (f := _), ht, add_sub_cancel]
  refine ⟨⟨p'.y, q.g + t, k • q.g, (GlobalTheory.TorusExt.isNsmul_iff_eq _ _ _).2 ?_, hh₀⟩, rfl, (GlobalTheory.TorusExt.eq_gtExt_iff f hf _ _).1 e⟩
  rw [nsmul_add, ht0, add_zero]

end GlobalTheory.QkDescent
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ

namespace GlobalTheory.ZJ

theorem exists_extension_with_section : Semi.extend_existsSt.{0} → Out.MulNSt → (∀ (K : Type) [Field K] [IsAlgClosed K] (B : Over (Sp K)) [GrpObj B], IsAbelianScheme B → ∀ n : ℕ, (n : K) ≠ 0 → Surjective (mulN B n).left) → ∀ (C : Core) (L : C.Law) (T : C.Theta) (n : ℕ), letI := L.grp; letI := L.comm; IsSemiAbelian C.GG → C.HasTests → C.TorsSec n → T.Few n → ∃ M : LB C.G.toScheme, M.IsLB ∧ LBIso (M.pull C.a) T.L.L ∧ ∀ z : C.Z, ∃ (N : C.Z.Opens) (σ : LB.Sec (M.pull (C.GG.hom ⁻¹ᵁ N).ι)), z ∈ N ∧ ∀ z' ∈ N, ∃ x ∈ Out.nonzeroLocus σ, C.GG.hom ((C.GG.hom ⁻¹ᵁ N).ι x) = z' := by
  intro hE hM hS C L T n hG hT hTors hFew
  have hB : T.BTest L := GlobalTheory.T.baseChangeTest_of_surjective_mul_abelianVariety hS C L T
  have hO : IsOpen (T.Om L) := (GlobalTheory.ZJ.etale_mulN_and_isOpen_om_of_isSemiAbelian C L T hG hM).2
  obtain ⟨ν, hν⟩ := GlobalTheory.T.exists_norms_of_tests hE C L T hT hB
  have h6 : L.CompanionTheory (T.Om L) := GlobalTheory.T.companionTheory_om_of_tests_torsionSections hE C L T n hT hB hTors hFew
  have hγ := GlobalTheory.ZJ.Core.exists_gen_normOne C L T (T.Om L) ν hO hν h6
  obtain ⟨-, hlft, -, hint, hflat, -, hop, -⟩ := core_basic C
  have := C.lft
  have hsm : Smooth C.GG.hom := by
    have := L.smooth
    exact SmoothOfRelativeDimension.smooth C.g _
  have hN : Geo.Tor.IsNormalScheme C.G.toScheme := fun x =>
    GlobalTheory.forall_isDomain_and_isIntegrallyClosed_stalk_of_smooth C.GG.hom C.normal x
  have hlft' : LocallyOfFiniteType (C.GG.hom ≫ C.π) := inferInstance
  exact GlobalTheory.T.exists_local_section_ne_zero_on_fibres' C L T (T.Om L) ν hO hν h6
    (@GlobalTheory.exists_lineBundle_of_normOne_generators C.G.toScheme C.A.left hint (C.GG.hom ≫ C.π) hflat hlft' hN C.a hop T.L.L T.L.isLB ν hν.isNrm hγ)

end GlobalTheory.ZJ
end
