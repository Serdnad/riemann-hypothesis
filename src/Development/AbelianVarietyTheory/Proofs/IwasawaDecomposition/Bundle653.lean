module

public import Development.AbelianVarietyTheory.Definitions.Divisors.DetJacMatCoordsEqTransitionJacobianDet
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle001
import Mathlib.Algebra.Module.SpanRankOperations
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.Bundle001
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle624
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsLocalRingTrivSqZeroExt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2119
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.EvaluationLawsGenericFramesAtlasHold
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle043
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIntegerExponentSectionOfChartRegular
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle481
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle011
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2598
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LUnifOfRhoGeoEquivAll
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1472
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.NormConst
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle024
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle042
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle026
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle637
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle638
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle640
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle641
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.KeyFamOne
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle029
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle062
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
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AmpleOnAbelianBase
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FnAlgClosedOfFixedPoints
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle102
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle631
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.HPInvEqForm
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsBlockMetricDiagForm
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomogeneousCompIdeal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle013

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PtDerivSep

open IsLocalRing

theorem exists_der_of_rsp {k R : Type} [Field k] [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [Algebra k R] [Algebra.FormallySmooth k (ResidueField R)] (ψ : R →+* ℂ) [IsLocalHom ψ] (m : ℕ)
    (f : Fin m → R) (hf : ReciprocityTheory.AnForm.R.FinalTheorems.Rsp R m f) (l : Fin m → ℂ) (hl : l ≠ 0) :
    ∃ D : R →+ ℂ, (∀ a : k, D (algebraMap k R a) = 0) ∧
      (∀ x y, D (x * y) = ψ x * D y + ψ y * D x) ∧ ∑ i, l i * D (f i) ≠ 0 := by
  classical
  obtain ⟨hspan, hdim⟩ := hf
  have hfm : ∀ i, f i ∈ maximalIdeal R := fun i => hspan ▸ Ideal.subset_span ⟨i, rfl⟩
  let v : Fin m → CotangentSpace R := fun i => (maximalIdeal R).toCotangent ⟨f i, hfm i⟩
  have hv : Submodule.span (ResidueField R) (Set.range v) = ⊤ := by
    have e : Set.range v = (maximalIdeal R).toCotangent '' Set.range
        (fun i => (⟨f i, hfm i⟩ : maximalIdeal R)) := by
      rw [← Set.range_comp]; rfl
    rw [e, CotangentSpace.span_image_eq_top_iff]
    apply Submodule.map_injective_of_injective (maximalIdeal R).injective_subtype
    rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype, ← Set.range_comp]
    exact hspan
  have hfr : Module.finrank (ResidueField R) (CotangentSpace R) = m := by
    apply le_antisymm
    · rw [← finrank_top (ResidueField R) (CotangentSpace R), ← hv]
      exact (finrank_range_le_card v).trans (by simp)
    · have h1 := ringKrullDim_le_spanFinrank_maximalIdeal R
      rw [spanFinrank_maximalIdeal_eq_finrank_cotangentSpace, ← hdim] at h1
      exact_mod_cast h1
  have hli : LinearIndependent (ResidueField R) v :=
    linearIndependent_of_top_le_span_of_card_eq_finrank hv.ge (by simp [hfr])
  let b := Module.Basis.mk hli hv.ge
  obtain ⟨j, hj⟩ := Function.ne_iff.1 hl

  let emb : ResidueField R →+* ℂ := ResidueField.lift ψ
  have hemb : ∀ r : R, emb (residue R r) = ψ r := fun r => ResidueField.lift_residue_apply ψ r
  let g : R ⧸ maximalIdeal R ^ 2 →ₐ[k] ResidueField R :=
    Ideal.Quotient.liftₐ (maximalIdeal R ^ 2) (IsScalarTower.toAlgHom k R (ResidueField R))
      (fun a ha => (residue_eq_zero_iff a).2 (Ideal.pow_le_self two_ne_zero ha))
  have hgr : ∀ r : R, g (Ideal.Quotient.mk _ r) = residue R r := fun r => rfl
  have hg : Function.Surjective g := by
    intro c
    obtain ⟨r, rfl⟩ := residue_surjective c
    exact ⟨Ideal.Quotient.mk _ r, hgr r⟩
  have hnil : IsNilpotent (RingHom.ker g) := by
    refine ⟨2, le_bot_iff.1 ?_⟩
    rw [pow_two (RingHom.ker g), Ideal.mul_le]
    intro x hx y hy
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective y
    have hr : r ∈ maximalIdeal R := (residue_eq_zero_iff r).1 ((hgr r).symm.trans (RingHom.mem_ker.1 hx))
    have hs : s ∈ maximalIdeal R := (residue_eq_zero_iff s).1 ((hgr s).symm.trans (RingHom.mem_ker.1 hy))
    rw [← map_mul, Ideal.mem_bot, Ideal.Quotient.eq_zero_iff_mem, pow_two]
    exact Ideal.mul_mem_mul hr hs
  let s := Algebra.FormallySmooth.liftOfSurjective (AlgHom.id k (ResidueField R)) g hg hnil
  have hs : ∀ c, g (s c) = c := fun c =>
    congrArg (fun φ : ResidueField R →ₐ[k] ResidueField R => φ c)
      (Algebra.FormallySmooth.comp_liftOfSurjective (AlgHom.id k (ResidueField R)) g hg hnil)
  let t : ResidueField R → R := fun c => Function.surjInv Ideal.Quotient.mk_surjective (s c)
  have ht : ∀ c, Ideal.Quotient.mk (maximalIdeal R ^ 2) (t c) = s c := fun c =>
    Function.surjInv_eq Ideal.Quotient.mk_surjective (s c)
  have hrt : ∀ c, residue R (t c) = c := fun c => by rw [← hgr, ht, hs]
  let e : R → R := fun r => r - t (residue R r)
  have he : ∀ r, e r ∈ maximalIdeal R := fun r =>
    (residue_eq_zero_iff _).1 (by simp only [e, map_sub, hrt, sub_self])
  have hmk : ∀ a : R, Ideal.Quotient.mk (maximalIdeal R ^ 2) a = 0 → a ∈ maximalIdeal R ^ 2 :=
    fun a h => Ideal.Quotient.eq_zero_iff_mem.1 h
  have hcot : ∀ (a a' : R) (ha : a ∈ maximalIdeal R) (ha' : a' ∈ maximalIdeal R),
      a - a' ∈ maximalIdeal R ^ 2 →
      (maximalIdeal R).toCotangent ⟨a, ha⟩ = (maximalIdeal R).toCotangent ⟨a', ha'⟩ :=
    fun a a' ha ha' h => (Ideal.toCotangent_eq _).2 h
  let D0 : R → ℂ := fun r => emb (b.repr ((maximalIdeal R).toCotangent ⟨e r, he r⟩) j)
  have hadd : ∀ x y, D0 (x + y) = D0 x + D0 y := by
    intro x y
    have h1 : (maximalIdeal R).toCotangent ⟨e (x + y), he (x + y)⟩ =
        (maximalIdeal R).toCotangent ⟨e x + e y, add_mem (he x) (he y)⟩ := by
      refine hcot _ _ _ _ (hmk _ ?_)
      simp only [e, map_sub, map_add (f := _), ht]
      ring
    have h2 := map_add (maximalIdeal R).toCotangent ⟨e x, he x⟩ ⟨e y, he y⟩
    simp only [D0, h1]
    rw [show (⟨e x + e y, add_mem (he x) (he y)⟩ : maximalIdeal R) = ⟨e x, he x⟩ + ⟨e y, he y⟩ from rfl,
      h2, map_add, Finsupp.add_apply, map_add]
  have hmul : ∀ x y, D0 (x * y) = ψ x * D0 y + ψ y * D0 x := by
    intro x y
    have hm2 : ∀ a b : R, a ∈ maximalIdeal R → b ∈ maximalIdeal R → a * b ∈ maximalIdeal R ^ 2 :=
      fun a b ha hb => by rw [pow_two]; exact Ideal.mul_mem_mul ha hb
    have h1 : (maximalIdeal R).toCotangent ⟨e (x * y), he (x * y)⟩ =
        (maximalIdeal R).toCotangent (t (residue R x) • (⟨e y, he y⟩ : maximalIdeal R) +
          t (residue R y) • (⟨e x, he x⟩ : maximalIdeal R)) := by
      refine hcot _ _ _ _ ?_
      have q : e (x * y) - (t (residue R x) * e y + t (residue R y) * e x) =
          e x * e y + (t (residue R x) * t (residue R y) - t (residue R (x * y))) := by
        simp only [e]; ring
      change e (x * y) - (t (residue R x) * e y + t (residue R y) * e x) ∈ _
      rw [q]
      refine add_mem (hm2 _ _ (he x) (he y)) (hmk _ ?_)
      rw [map_sub, map_mul, ht, ht, ht, map_mul, map_mul, sub_self]
    simp only [D0, h1, map_add (f := _), map_smul]
    rw [← algebraMap_smul (ResidueField R) (t (residue R x)),
      ← algebraMap_smul (ResidueField R) (t (residue R y)), map_smul, map_smul,
      Finsupp.add_apply, Finsupp.smul_apply, Finsupp.smul_apply, smul_eq_mul, smul_eq_mul,
      map_add, map_mul, map_mul, ResidueField.algebraMap_eq, hrt, hrt, hemb, hemb]
  let D : R →+ ℂ := AddMonoidHom.mk' D0 hadd
  refine ⟨D, fun a => ?_, hmul, ?_⟩
  · change D0 _ = 0
    have h1 : (maximalIdeal R).toCotangent ⟨e (algebraMap k R a), he _⟩ =
        (maximalIdeal R).toCotangent ⟨0, zero_mem _⟩ := by
      refine hcot _ _ _ _ (hmk _ ?_)
      have r1 : residue R (algebraMap k R a) = algebraMap k (ResidueField R) a :=
        (IsScalarTower.algebraMap_apply k R (ResidueField R) a).symm
      show Ideal.Quotient.mk _ (algebraMap k R a - t (residue R (algebraMap k R a)) - 0) = 0
      rw [sub_zero, map_sub, ht, r1, AlgHom.commutes, Ideal.Quotient.mk_algebraMap, sub_self]
    simp only [D0, h1]
    rw [show (⟨0, zero_mem _⟩ : maximalIdeal R) = 0 from rfl, map_zero, map_zero, Finsupp.zero_apply,
      map_zero]
  · have hfi : ∀ i, D0 (f i) = emb (Finsupp.single i 1 j) := by
      intro i
      have h1 : (maximalIdeal R).toCotangent ⟨e (f i), he _⟩ = b i := by
        rw [Module.Basis.mk_apply]
        refine hcot _ _ _ _ (hmk _ ?_)
        have r0 : residue R (f i) = 0 := (residue_eq_zero_iff _).2 (hfm i)
        show Ideal.Quotient.mk _ (f i - t (residue R (f i)) - f i) = 0
        rw [r0, sub_sub_cancel_left, map_neg, ht, map_zero, neg_zero]
      simp only [D0, h1, Module.Basis.repr_self]
    change ∑ i, l i * D0 (f i) ≠ 0
    simp only [hfi]
    rw [Finset.sum_eq_single j (fun i _ hi => by rw [Finsupp.single_apply, if_neg hi, map_zero, mul_zero])
      (fun h => (h (Finset.mem_univ j)).elim), Finsupp.single_eq_same, map_one, _root_.mul_one]
    exact hj

end GlobalTheory.PtDerivSep

namespace GlobalTheory.PtDerivSep

open IsLocalRing

theorem exists_ptDer_sep : ∀ (k : Type) [Field k] [CharZero k] (Y : Scheme.{0}) (p : Y ⟶ Sp k) (n : ℕ) (σ : k →+* ℂ), SmoothOfRelativeDimension n p → ∀ (x₀ : CxPts p σ) (U : Y.affineOpens) (hy : x₀.1 (IsLocalRing.closedPoint ℂ) ∈ U.1) (m : ℕ) (f : Fin m → Γ(Y, U.1)), ReciprocityTheory.AnForm.R.FinalTheorems.Rsp (Y.presheaf.stalk (x₀.1 (IsLocalRing.closedPoint ℂ))) m (fun i => Y.presheaf.germ U.1 _ hy (f i)) → ∀ l : Fin m → ℂ, l ≠ 0 → ∃ δ : Γ(Y, U.1) →+ ℂ, (∀ a : k, δ (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p U.1 a) = 0) ∧ (∀ g h : Γ(Y, U.1), δ (g * h) = CxPts.ev p σ U.1 g x₀ * δ h + CxPts.ev p σ U.1 h x₀ * δ g) ∧ ∑ i, l i * δ (f i) ≠ 0 := by
  intro k _ _ Y p n σ hsm x₀ U hy m f hR l hl
  haveI := hsm
  haveI : Smooth p := SmoothOfRelativeDimension.smooth n p
  let c : k →+* Γ(Y, U.1) := ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p U.1
  have hft : c.FiniteType := (p.finiteType_appLE (isAffineOpen_top _) U.2 le_top).comp
    (RingHom.FiniteType.of_surjective _
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of k)).inv).2)
  let germ : Γ(Y, U.1) →+* Y.presheaf.stalk (x₀.1 (IsLocalRing.closedPoint ℂ)) :=
    (Y.presheaf.germ U.1 _ hy).hom
  have hloc : germ.EssFiniteType := by
    letI := Y.presheaf.algebra_section_stalk (⟨_, hy⟩ : U.1)
    haveI := U.2.isLocalization_stalk ⟨_, hy⟩
    exact Algebra.EssFiniteType.of_isLocalization (Y.presheaf.stalk _)
      (U.2.primeIdealOf ⟨_, hy⟩).asIdeal.primeCompl
  have hnoeth : IsNoetherianRing (Y.presheaf.stalk (x₀.1 (IsLocalRing.closedPoint ℂ))) := by
    letI := c.toAlgebra
    haveI : Algebra.FiniteType k Γ(Y, U.1) := hft
    haveI : IsNoetherianRing Γ(Y, U.1) := Algebra.FiniteType.isNoetherianRing k _
    letI := Y.presheaf.algebra_section_stalk (⟨_, hy⟩ : U.1)
    haveI := U.2.isLocalization_stalk ⟨_, hy⟩
    exact IsLocalization.isNoetherianRing (U.2.primeIdealOf ⟨_, hy⟩).asIdeal.primeCompl _ inferInstance
  letI : Algebra k (Y.presheaf.stalk (x₀.1 (IsLocalRing.closedPoint ℂ))) := (germ.comp c).toAlgebra
  haveI : Algebra.EssFiniteType k (Y.presheaf.stalk (x₀.1 (IsLocalRing.closedPoint ℂ))) :=
    RingHom.essFiniteType_algebraMap.1 (hft.essFiniteType.comp hloc)
  haveI : Algebra.EssFiniteType k (ResidueField (Y.presheaf.stalk (x₀.1 (IsLocalRing.closedPoint ℂ)))) :=
    .of_surjective (IsScalarTower.toAlgHom k _ _) residue_surjective
  let ψ := (Scheme.stalkClosedPointTo (R := CommRingCat.of ℂ) x₀.1).hom
  obtain ⟨D, h1, h2, h3⟩ := exists_der_of_rsp (k := k) ψ m _ hR l hl
  have hx : x₀ ∈ CxPts.ptsIn p σ U.1 := CxPts.mem_ptsIn.2 hy
  have hψ : ∀ g, ψ (germ g) = CxPts.ev p σ U.1 g x₀ := by
    intro g
    rw [CxPts.ev_eq hx, CxPts.evHom, ← GlobalTheory.Points.germ_stalkClosedPointTo_eq_valMap x₀.1 U.1 hx]
    rfl
  refine ⟨D.comp germ.toAddMonoidHom, fun a => h1 a, fun g h => ?_, h3⟩
  simp only [AddMonoidHom.comp_apply, RingHom.toAddMonoidHom_eq_coe, AddMonoidHom.coe_coe, map_mul, h2, hψ]

end GlobalTheory.PtDerivSep
end
end

section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.TrueCx.FlatConst

section Hol

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.ShFam GlobalTheory.LamT
open GlobalTheory.Reg GlobalTheory.KeyFourth GlobalTheory.AllWt GlobalTheory.FlatLine

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l}

theorem exists_generic_units (hpq : 1 ≤ Dw.p + Dw.q) (h : GenFrEx Xo c) :
    ∃ v : ∀ Z : Comp Xo c, (Om Z)ˣ, ∀ C : FChart h,
      ∃ u : (C.R)ˣ, ((u : C.R) : Om C.Z) = ((kch C.t ^ 4 * v C.Z : (Om C.Z)ˣ) : Om C.Z) := by
  obtain ⟨κ, h₁, h₂, -, -, -, h₃, -⟩ := GlobalTheory.KeyFamClosing.keyFam_one
  let e := (Fintype.equivFin (Σ τ : E →+* ℂ, Fin (Dw.mult τ))).symm
  have hc : ∀ Z : Comp Xo c, CharZero (Om Z) := fun Z =>
    charZero_of_injective_algebraMap (algebraMap c.F (Om Z)).injective
  choose Ψ hΨ using fun Z : Comp Xo c => exists_tied E H Dw l Xo c _ e (Om Z) (genFr h Z) hpq
  refine ⟨fun Z => κ (Om Z) (Ψ Z).key, fun C => ?_⟩
  letI : Algebra c.F C.R := Subalgebra.algebra C.R
  haveI := C.sm
  haveI : IsIntegrallyClosed C.R := isIntegrallyClosed_of_smooth c.F C.R
  haveI : IsNoetherianRing C.R := Algebra.FiniteType.isNoetherianRing c.F C.R
  haveI : CharZero C.R := charZero_of_injective_algebraMap (algebraMap c.F C.R).injective
  obtain ⟨Φ, hΦ⟩ := exists_tied E H Dw l Xo c _ e C.R C.y hpq
  obtain ⟨Φ', hΦ'⟩ := exists_tied E H Dw l Xo c _ e (Om C.Z) C.yg hpq
  obtain ⟨u, hu⟩ := h₃ C.R Φ.key
  refine ⟨u, ?_⟩
  rw [← rule_frBor κ h₁ h₂ E H Dw l Xo c _ e (Om C.Z) C.t _ _ (Ψ C.Z) Φ' C.bor (hΨ _) hΦ']
  exact (hu (Om C.Z) _ _ (tied_keyPB E H Dw l Xo c _ e _ _ C.R.val C.y C.yg Φ Φ' C.gen hΦ hΦ')).symm

theorem exists_key_four (hpq : 1 ≤ Dw.p + Dw.q) (σ : c.F →+* ℂ) :
    ∃ ρ ∈ secZ Xo c (fun i => keyEx Dw i * 4), ∀ y : FrPt Xo c (CAt σ), toC (evR Xo c ρ y) ≠ 0 := by
  obtain ⟨-, -, h, hA⟩ := evLaws_genFr_atlas E H Dw l Xo c
  obtain ⟨v, hv⟩ := exists_generic_units hpq h
  have hk : ∀ C : FChart h, (∏ i, C.t i ^ (keyEx Dw i * 4) : (Om C.Z)ˣ) = kch C.t ^ 4 := fun C => by
    rw [kch, ← Finset.prod_pow]
    exact Finset.prod_congr rfl fun i _ => by rw [zpow_mul]; rfl
  obtain ⟨ρ, hρ, hρv⟩ := GlobalTheory.SecGlueInt.exists_secZ_of_regular E H Dw l Xo c h (fun i => keyEx Dw i * 4)
    (fun Z => v Z) fun C => by
      obtain ⟨u, hu⟩ := hv C
      rw [hk, ← Units.val_mul, ← hu]
      exact u.1.2
  refine ⟨ρ, hρ, fun y => ?_⟩
  letI : Field (CAt σ) := inferInstanceAs (Field ℂ)
  obtain ⟨C, ψ, z, t, hz, hb⟩ := hA h (CAt σ) y
  obtain ⟨u, hu⟩ := hv C
  obtain ⟨b, hb₁, hb₂⟩ := GlobalTheory.DegCmp.fChart_exists_val C hρ
  have hbu : b = u := Subtype.ext (by
    rw [hb₁, hu, hk, GlobalTheory.CompHt.genVal_apply h, hρv, Units.val_mul])
  show evR Xo c ρ y ≠ 0
  rw [GlobalTheory.FlagTan.evR_frBor hρ hb, hb₂ _ ψ z hz, hbu]
  exact mul_ne_zero (Units.ne_zero _) (u.isUnit.map ψ).ne_zero

theorem exists_sec_four (hpq : 1 ≤ Dw.p + Dw.q) {σ : c.F →+* ℂ} (y : FrPt Xo c (CAt σ)) :
    ∃ n, Even n ∧ ∃ g ∈ sec Xo c (fun _ => 4) n, toC (evR Xo c g y) ≠ 0 := by
  obtain ⟨ρ, hρ, h0⟩ := exists_key_four (Xo := Xo) hpq σ
  obtain ⟨n, hn, ⟨m, rfl⟩, η, hη, hη0⟩ := exists_even_sec_evR_ne_zero E H Dw l Xo c σ y
  rw [← secZ_nat] at hη
  have h2 := mul_mem_secZ hη hη
  have h3 := mul_mem_secZ (mul_mem_secZ h2 h2) hρ
  refine ⟨2 * (4 * m - 4), even_two_mul _, η * η * (η * η) * ρ, ?_, ?_⟩
  · rw [← secZ_nat]
    convert h3 using 2
    funext i
    cases i with
    | none => simp only [ex, keyEx, Pi.add_apply]; omega
    | some i => simp [ex, keyEx]
  · have h1 : toC (evR Xo c η y) ≠ 0 := hη0
    simp only [CompSplitPfB.cspB_evR_mul]
    exact mul_ne_zero (M₀ := ℂ) (mul_ne_zero (M₀ := ℂ) (mul_ne_zero (M₀ := ℂ) h1 h1) (mul_ne_zero (M₀ := ℂ) h1 h1)) (h0 y)


variable {σ : c.F →+* ℂ} {r : ℕ} {U : Unf Xo c σ r}

end Hol

section Main

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix
open Formalism.DegreeFormula Formalism.MJ Formalism.UG Formalism.L2.Geo Formalism.L2.PjFree
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.PullbackSections
open GlobalTheory GlobalTheory.HodgeDomain GlobalTheory.LieMet GlobalTheory.CxPts GlobalTheory.TrueCx
open GlobalTheory.AllWt (Psi)
attribute [local instance] Over.cartesianMonoidalCategory

end Main

end GlobalTheory.TrueCx.FlatConst
end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Host GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Top.Bl

open Formalism.IndefR.FWT Formalism.L2.Pj Formalism.IndefR.Mult



theorem lUnif_atDat : GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Hk3.HoweUnram →
    GlobalTheory.Mem.Top.Bl.AtDat fun _ B f T w Z hX Wt z => z.R.toRealDat.LUnif := by
  intro _ _ _
  refine StepW.of_all fun K B f T w _ _ _ Z hX Wt z _ _ hEx hIn => ?_
  have hch := z.pins.char
  have hC : GlobalTheory.RealGeo.PreChar z.R.toRealDat :=
    ⟨hch.base.lev, hch.base.grp.red_R, hch.base.grp.red_L, hch.base.grp.record, hch.base.fam, hch.base.models,
      RealDat.chain_of_weak hch.base.chain hEx, RealDat.thP_of_weak hch.base.thP hEx⟩
  have hχ : z.R.toRealDat.grp_chiW := hch.base.grp.chiW
  have ht : TieIn z.core z.R.toRealDat z.geo.κ z.geo.v₀ :=
    ⟨z.geo.fw.laws, z.geo.fw.alg_eq, z.geo.fw.kap, z.geo.fw.hv₀, z.geo.fw.chiR, z.geo.fw.x0⟩
  have hp : z.core.pb = z.R.toRealDat.C.P.pb :=
    GlobalTheory.PinsFixHalf.pb_eq_of_pins z.core z.R.toRealDat z.geo.κ z.geo.v₀ z.geo.O hC.lev z.geo.fw.laws z.geo.pins
  have hx := GlobalTheory.T.exists_equivariant_unit_constants_goodEmbedding z.core z.R.toRealDat z.geo.κ z.geo.v₀ z.geo.O hC.lev ht hp z.geo.pins
  have hU := hIn.jUnif
  intro i σ
  exact ⟨(GlobalTheory.TiedUnif.indep_span_of_tie z.geo.fw hC.models.HW z.geo.bar hU i σ).1,
    (GlobalTheory.TiedUnif.indep_span_of_tie z.geo.fw hC.models.HW z.geo.bar hU i σ).2,
    GlobalTheory.TiedUnif.rhoIs_of_eqAt z.geo.fw hC.models.HW hC.models.gW hχ z.geo.bar z.geo.rhoGeo hU i σ
      (fun h hV => z.geo.equivAll i _ h hV (hx i _ h hV))
      fun h hV => z.geo.equivAll i _ (good_resC z.core h) hV (hx i _ (good_resC z.core h) hV)⟩

end GlobalTheory.Mem.Top.Bl
end

section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.ShFam GlobalTheory.LamT GlobalTheory.KeyFourth GlobalTheory.FrameUnif GlobalTheory.Reg
open scoped Matrix TensorProduct

namespace GlobalTheory.KeyFourth

section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r g : ℕ}
  {e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)}
  {F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => Formalism.L2.PjFree.relab c σ (e j).1)}
  {M : _root_.GlobalTheory.FrameUnif.ModelsOf F r}

theorem exists_isThetaPt_of_adapted {k : Fin F.n} (T : ThetaData e F M k) (x : Fin T.m → ℂ)
    (hx : x ∈ T.co ⁻¹' (M.X k).dom) (y : FrPt Xo c (CAt σ)) (h₁ : y.x = F.u k (T.Pf (T.co x)))
    (h₂ : ∀ τ (i : Fin (Dw.mult τ)), IsDerivAt0 (fun z => (F.ex k (T.Pf (T.co x)) z).left)
      (Pi.single (e.symm ⟨τ, i⟩) 1) (y.u τ i)) :
    ∃ a : ℂ, a ≠ 0 ∧ IsThetaPt T x a y := by
  obtain ⟨hu, hsym, hpos, -⟩ := T.norm x hx
  obtain ⟨-, w, hw⟩ := (GlobalTheory.ThetaHalf.thetaChar_holomorphic_ne_zero g T.c₁ T.c₂ T.half₁ T.half₂).1 _ hsym hpos
  obtain ⟨t, ht⟩ := T.fr_sec x hx
  obtain ⟨a, ha, hv⟩ := GlobalTheory.GenFactor.exists_factor GlobalTheory.abelianSchemeLaws_all.2.secTwist y.x _ h₁ y.s y.gen
    (F.ex k (T.Pf (T.co x))) (fun z => thetaChar (T.ta x) T.c₁ T.c₂ (T.h x *ᵥ z)) (fun j z => T.fr j (x, z))
    ⟨(T.h x)⁻¹ *ᵥ w, by
      show thetaChar _ _ _ (T.h x *ᵥ ((T.h x)⁻¹ *ᵥ w)) ≠ 0
      rwa [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hu, Matrix.one_mulVec]⟩
    (fun j z hz => T.fr_ne j x z hx hz) t ht
  exact ⟨a, ha, h₁, h₂, hv⟩

theorem rootVal_of_isThetaPt {k : Fin F.n} (T : ThetaData e F M k) (un : ∀ k, (M.X k).dom → FrPt Xo c (CAt σ))
    (hun : IsNormUn T (un k)) (x : Fin T.m → ℂ) (hx : x ∈ T.co ⁻¹' (M.X k).dom) (a : ℂ) (ha : a ≠ 0)
    (y : FrPt Xo c (CAt σ)) (hy : IsThetaPt T x a y) :
    RootVal (unfOf e F M un) y
      ((normConst (fun j => Formalism.L2.PjFree.relab c σ (e j).1) (M.X k).ξ0 : ℂ) * (T.h x).det / a ^ 2) := by
  obtain ⟨κ, hκ, hθ⟩ := hun ⟨T.co x, hx⟩
  simp only [ContinuousLinearEquiv.symm_apply_apply] at hκ hθ
  have hC : (normConst (fun j => Formalism.L2.PjFree.relab c σ (e j).1) (M.X k).ξ0 : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero]
    refine (Real.sqrt_pos.2 (div_pos (by positivity) (Finset.prod_pos fun j _ => ?_))).ne'
    have : Formalism.L2.PjFree.relab c σ (e j).1 (M.X k).ξ0 ≠ 0 := (map_ne_zero _).2 (M.X k).ξ0_ne
    positivity
  have k1 : κ ≠ 0 := fun h0 => mul_ne_zero hC (T.norm _ hx).1.ne_zero (by rw [← hκ, h0]; simp)
  let t₀ : ℂˣ := Units.mk0 (a / κ) (div_ne_zero ha k1)
  have hb := GlobalTheory.frBor_of_isThetaPt GlobalTheory.abelianSchemeLaws_all.2.secTwist E H Dw l Xo c σ g e F r M k T x hx κ
    (show (CAt σ)ˣ from t₀) (un k ⟨T.co x, hx⟩) y hθ (by
      have : a / κ * κ = a := div_mul_cancel₀ a k1
      show IsThetaPt T x (a / κ * κ) y
      rwa [this])
  refine ⟨k, ⟨T.co x, hx⟩, _, hb, ?_⟩
  have hk : kch (Dw := Dw) (S := ℂ) (fun i => Option.elim i t₀ (fun _ => 1)) = (t₀ ^ 2)⁻¹ := by
    rw [kch_eq]
    simp
  refine Eq.trans ?_ (congrArg Units.val hk).symm
  rw [← hκ, Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val, Units.val_mk0]
  field_simp

end

theorem continuousOn_rootVal : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => Formalism.L2.PjFree.relab c σ (e j).1)) (r : ℕ) (M : _root_.GlobalTheory.FrameUnif.ModelsOf F r) (T : ∀ k, ThetaData e F M k) (un : ∀ k, (M.X k).dom → FrPt Xo c (CAt σ)), Formalism.L2.PjFree.GoodEmb c σ → ModelBase M → NegXi M → (∀ k, IsNormUn (T k) (un k)) → FramesOK e F M un → ∀ (A : Type) [CommRing A] [Algebra c.F A] (yA : FrPt Xo c A) (m : ℕ) (B : Set (Fin m → ℂ)) (φ : (Fin m → ℂ) → (A →ₐ[c.F] CAt σ)) (y : (Fin m → ℂ) → FrPt Xo c (CAt σ)) (ρ : (Fin m → ℂ) → ℂ), IsOpen B → (∀ a, DifferentiableOn ℂ (fun b => Formalism.L2.PjFree.toC (φ b a)) B) → (∀ b ∈ B, FrMap (φ b) yA (y b)) → (∀ b ∈ B, RootVal (unfOf e F M un) (y b) (ρ b)) → ContinuousOn ρ B := by
  intro E _ _ _ H Dw l Xo c σ g e F r M T un hσ hM hξ hun hok A _ _ yA m B φ y ρ hB hφ hy hρ b₀ hb₀
  obtain ⟨B', k, P, hB', hb', hsub, hP, hd⟩ :=
    GlobalTheory.AdaptedPeriods.exists_holPeriods_adapted E H Dw l Xo c σ g e F A yA m B φ y hB hφ hy b₀ hb₀
  obtain ⟨x, hx, hxc⟩ :=
    GlobalTheory.FrameLiftAt.exists_frame_lift E H Dw l Xo c σ g e F r M k (T k) hσ hM hξ m B' P hB' hP b₀ hb'
  have h₁ : ∀ b ∈ B', ∃ a : ℂ, a ≠ 0 ∧ IsThetaPt (T k) (x b) a (y b) := fun b hb =>
    exists_isThetaPt_of_adapted (T k) (x b) (hx b hb).1 (y b) (by rw [(hx b hb).2]; exact (hd b hb).1)
      (by rw [(hx b hb).2]; exact (hd b hb).2)
  choose! a ha hθ using h₁
  have hac : ContinuousAt a b₀ :=
    GlobalTheory.ThetaScalar.continuousAt_scalar E H Dw l Xo c σ g e F r M k (T k) A yA m B' φ y P x a hB'
      (fun t => (hφ t).mono hsub) (fun b hb => hy b (hsub hb)) hP
      (fun b hb => ⟨(hx b hb).1, (hx b hb).2, hθ b hb⟩) b₀ hb' hxc
  have hO : IsOpen ((T k).co ⁻¹' (M.X k).dom) := (FourierCoefficientDomain.isOpen_dom _).preimage (T k).co.continuous
  have hh : ContinuousAt (T k).h (x b₀) := continuousAt_pi.2 fun i => continuousAt_pi.2 fun j =>
    ((T k).hol i j).1.continuousOn.continuousAt (hO.mem_nhds (hx b₀ hb').1)
  have hdet : ContinuousAt (fun b => ((T k).h (x b)).det) b₀ :=
    (continuous_id.matrix_det.continuousAt).comp (ContinuousAt.comp hh hxc)
  have hq : ContinuousAt (fun b => (normConst (fun j => Formalism.L2.PjFree.relab c σ (e j).1) (M.X k).ξ0 : ℂ) *
      ((T k).h (x b)).det / a b ^ 2) b₀ :=
    (continuousAt_const.mul hdet).div (hac.pow 2) (pow_ne_zero 2 (ha b₀ hb'))
  refine (hq.congr ?_).continuousWithinAt
  filter_upwards [hB'.mem_nhds hb'] with b hb
  exact rootVal_unique E H Dw l Xo c σ g e F r M un hσ hM hξ hok (y b) _ _
    (rootVal_of_isThetaPt (T k) un (hun k) (x b) (hx b hb).1 (a b) (ha b hb) (y b) (hθ b hb)) (hρ b (hsub hb))

end GlobalTheory.KeyFourth
end
