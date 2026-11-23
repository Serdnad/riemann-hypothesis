module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SurjectiveOfIsPullbackSqZero
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle020
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle601
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle972
public import Development.AbelianVarietyTheory.Definitions.Divisors.UnifOfSpaceEq
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsProbabilityMeasureMuPart
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2243
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2215
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2146
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.FinMuUnconditional
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle016
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsProbabilityMeasureAutQuotientNormalized
public import Formalism.LocalToGlobal.ProjectiveLattices.RosatiLatticeNorms.LinkFD
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle016
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
public import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2244
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle025
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2253
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle171
public import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle171
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle568
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.TypeStar
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle026
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle015
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle010
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.OrthonormalFlagTranslateHolds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.SiegelSpaceAlgebraHolds
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle047
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.Bundle002
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IMemSiegel
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsStabForm
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsSystem
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram

@[expose] public section

section

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.LiftSys GlobalTheory.Published
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LiftSys


open TensorProduct in
theorem oneTmul_surjective_ker {R R₀ : Type} [CommRing R] [CommRing R₀] (I : Ideal R) (π : R →+* R₀)
    (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (M : Type*) [AddCommGroup M] [Module R M] :
    letI := π.toAlgebra
    Function.Surjective (TensorProduct.mk R R₀ M 1) ∧
      ∀ m : M, (1 : R₀) ⊗ₜ[R] m = 0 ↔ m ∈ I • (⊤ : Submodule R M) := by
  letI := π.toAlgebra
  subst hk
  let f : (R ⧸ RingHom.ker π) ≃ₐ[R] R₀ := Ideal.quotientKerAlgEquivOfSurjective (f := (Algebra.ofId R R₀)) hπ
  let E : R₀ ⊗[R] M ≃ₗ[R] M ⧸ (RingHom.ker π • (⊤ : Submodule R M)) :=
    (TensorProduct.congr f.toLinearEquiv.symm (LinearEquiv.refl R M)) ≪≫ₗ quotTensorEquivQuotSMul M (RingHom.ker π)
  have hE : ∀ m : M, E (1 ⊗ₜ m) = Submodule.Quotient.mk m := fun m ↦ by
    simp [E, map_one]
  refine ⟨fun t ↦ ?_, fun m ↦ ?_⟩
  · obtain ⟨m, hm⟩ := Submodule.Quotient.mk_surjective _ (E t)
    exact ⟨m, E.injective (by rw [← hm]; exact hE m)⟩
  · rw [← Submodule.Quotient.mk_eq_zero, ← hE, LinearEquiv.map_eq_zero_iff]

theorem mem_smul_top_of_equiv {R : Type} [CommRing R] (I : Ideal R) {M N : Type*} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (L : M ≃ₗ[R] N) (x : M) :
    L x ∈ I • (⊤ : Submodule R N) ↔ x ∈ I • (⊤ : Submodule R M) := by
  have e : (I • ⊤ : Submodule R N) = (I • ⊤ : Submodule R M).map (L : M →ₗ[R] N) := by
    rw [Submodule.map_smul'', Submodule.map_top, LinearMap.range_eq_top.2 L.surjective]
  rw [e, Submodule.mem_map_equiv, LinearEquiv.symm_apply_apply]

theorem rhoBC_of_abelianLift : CrystallineSmoothLift → AbelianHodgeDeRham → ∀ (R R₀ : Type) [CommRing R] [CommRing R₀]
    (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (g : ℕ)
    (A₀ : Over (Sp R₀)) [GrpObj A₀] (A' : Over (Sp R)) [GrpObj A'] (i' : A₀.left ⟶ A'.left)
    (h' : IsGrpPullback A₀ A' (spMap π) i'), IsAbelianScheme A' → SmoothOfRelativeDimension g A'.hom →
    RhoBC hI hk A₀.hom := by
  intro H1 H2 R R₀ _ _ I hI π hπ hk g A₀ _ A' _ i' h' hA hg
  letI := π.toAlgebra
  have := hA.smooth
  have := hA.proper
  haveI : Smooth A₀.hom := MorphismProperty.of_isPullback (P := @Smooth) h'.1 hA.smooth
  haveI : IsProper A₀.hom := MorphismProperty.of_isPullback (P := @IsProper) h'.1 hA.proper
  have w : i' ≫ A'.hom = A₀.hom ≫ spMap π := h'.1.w
  have hm : IsMor (dp0 R) A'.hom (divided₂ hI) (A₀.hom ≫ spMap π) (RingHom.id R) i' :=
    IsMor.of_dividedPowersZeroIdeal _ (by rw [Cris.spMap_id, Category.comp_id]; exact w)
  have hn : IsMor (dp0 R) A'.hom (dp0 R₀) A₀.hom π i' := IsMor.of_dividedPowersZeroIdeal _ w
  have bm : Function.Bijective hm.pull1 :=
    (H1.toCrystallineDeRham R I (divided₂ hI) (isDPNilpotent_squareZero hI) R₀ π hπ hk A'.left A₀.left A'.hom A₀.hom i'
      inferInstance inferInstance inferInstance h'.1 hm).1
  have comp : ∀ c, rho hI hk A₀.hom (hm.pull1 c) = hn.pull1 c := fun c ↦
    IsMor.pullback1_comp hm (redMor hI hk A₀.hom) hn (fun _ ↦ rfl) (Category.id_comp _) c
  have b' := H1.bijective_cechDeRhamComparison_degreeOne A'.hom inferInstance inferInstance inferInstance
  have b₀ := H1.bijective_cechDeRhamComparison_degreeOne A₀.hom inferInstance inferInstance inferInstance
  obtain ⟨⟨e, he⟩, -, -⟩ := (H2 R A' g hA hg).2.2.2.2.2 R₀ A₀.left A₀.hom i' h'.1
  have key : ∀ c, cmp1 A₀.hom (hn.pull1 c) = e (1 ⊗ₜ cmp1 A'.hom c) := fun c ↦
    (pairRes_injective i' A₀.hom).2.2 ((comparison_pullback hn c).symm.trans (he _))
  obtain ⟨hsurj, hker⟩ := oneTmul_surjective_ker I π hπ hk (HH1 A'.hom)
  let L := LinearEquiv.ofBijective hm.pull1 bm
  let C := LinearEquiv.ofBijective (cmp1 A'.hom) b'
  refine ⟨fun y ↦ ?_, fun c ↦ ?_⟩
  · obtain ⟨t, ht⟩ := e.surjective (cmp1 A₀.hom y)
    obtain ⟨m, rfl⟩ := hsurj t
    obtain ⟨c', rfl⟩ := b'.2 m
    exact ⟨hm.pull1 c', by rw [comp]; exact b₀.1 ((key c').trans ht)⟩
  · obtain ⟨c', rfl⟩ := bm.2 c
    rw [comp, show hm.pull1 c' = L c' from rfl, mem_smul_top_of_equiv I L c', ← mem_smul_top_of_equiv I C c',
      ← hker]
    change _ ↔ (1 : R₀) ⊗ₜ cmp1 A'.hom c' = 0
    rw [← LinearEquiv.map_eq_zero_iff e, ← key, ← map_zero (cmp1 A₀.hom)]
    exact ⟨fun h ↦ by rw [h], fun h ↦ b₀.1 h⟩

end GlobalTheory.LiftSys
end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.LiftSys GlobalTheory.Published
open TensorProduct

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LiftSys

theorem exists_isCompl_ker_of_projective {R : Type} {M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [Module.Projective R N] (f : M →ₗ[R] N) (hf : Function.Surjective f) :
    ∃ C : Submodule R M, IsCompl (LinearMap.ker f) C := by
  obtain ⟨g, hg⟩ := Module.projective_lifting_property f LinearMap.id hf
  have hfg : ∀ y, f (g y) = y := fun y ↦ LinearMap.congr_fun hg y
  refine ⟨LinearMap.range g, ?_, ?_⟩
  · rw [Submodule.disjoint_def]
    rintro x hx ⟨y, rfl⟩
    have : y = 0 := (hfg y).symm.trans hx
    rw [this, map_zero]
  · rw [codisjoint_iff, eq_top_iff]
    intro x _
    have e : x = (x - g (f x)) + g (f x) := by abel
    rw [e]
    refine Submodule.add_mem_sup ?_ (LinearMap.mem_range_self g _)
    rw [LinearMap.mem_ker, map_sub, hfg, sub_self]

theorem mem_smul_top_of_tmul_eq_zero {R R₀ M : Type} [CommRing R] [CommRing R₀] [AddCommGroup M] [Module R M]
    (π : R →+* R₀) (hπ : Function.Surjective π) {I : Ideal R} (hk : RingHom.ker π = I) (x : M)
    (h : letI := π.toAlgebra; (1 : R₀) ⊗ₜ[R] x = 0) : x ∈ I • (⊤ : Submodule R M) := by
  letI := π.toAlgebra
  subst hk
  let f : (R ⧸ RingHom.ker π) ≃ₐ[R] R₀ :=
    Ideal.quotientKerAlgEquivOfSurjective (f := Algebra.ofId R R₀) hπ
  let E : R₀ ⊗[R] M ≃ₗ[R] M ⧸ (RingHom.ker π) • (⊤ : Submodule R M) :=
    (TensorProduct.congr f.toLinearEquiv.symm (LinearEquiv.refl R M)).trans
      (TensorProduct.quotTensorEquivQuotSMul M (RingHom.ker π))
  have h1 : E ((1 : R₀) ⊗ₜ[R] x) = Submodule.Quotient.mk x := by
    have : f.symm (1 : R₀) = Ideal.Quotient.mk _ 1 := by rw [map_one, map_one]
    change TensorProduct.quotTensorEquivQuotSMul M (RingHom.ker π) (f.symm 1 ⊗ₜ[R] x) = _
    rw [this, TensorProduct.quotTensorEquivQuotSMul_mk_tmul, one_smul]
  rw [h, map_zero, eq_comm, Submodule.Quotient.mk_eq_zero] at h1
  exact h1

theorem full_and_isCompl : CrystallineSmoothLift → AbelianHodgeDeRham → ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (g : ℕ) (A₀ : Over (Sp R₀)) [GrpObj A₀] (A' : Over (Sp R)) [GrpObj A'] (i' : A₀.left ⟶ A'.left) (h' : IsGrpPullback A₀ A' (spMap π) i'), IsAbelianScheme A' → SmoothOfRelativeDimension g A'.hom → ∀ S : Sys I π A₀.hom, S.Presents A'.hom i' → S.Full hI ∧ ∃ N, IsCompl (S.K hI) N := by
  intro H HD R R₀ _ _ I hI π hπ hk g A₀ _ A' _ i' h' hA hg S hS
  have hpb : IsPullback i' A₀.hom A'.hom (spMap π) := h'.1
  obtain ⟨e, he1, he2⟩ := GlobalTheory.T.hodge_cohomology_iso_presented_crystal R R₀ I hI π hπ hk A₀.left A₀.hom S A'.left A'.hom i' hpb hS
  have hsm : Smooth A'.hom := hA.smooth
  haveI : IsProper A'.hom := hA.proper
  have hsep : IsSeparated A'.hom := inferInstance
  have hqc : QuasiCompact A'.hom := inferInstance
  have hw : i' ≫ A'.hom = (A₀.hom ≫ spMap π) ≫ spMap (RingHom.id R) := by
    rw [Cris.spMap_id, Category.comp_id]; exact hpb.w
  let m : IsMor (dp0 R) A'.hom (divided₂ hI) (A₀.hom ≫ spMap π) (RingHom.id R) i' := IsMor.of_dividedPowersZeroIdeal _ hw
  have hm := (H.toCrystallineDeRham R I (divided₂ hI) (isDPNilpotent_squareZero hI) R₀ π hπ hk A'.left A₀.left A'.hom A₀.hom i'
    hsm hsep hqc hpb m).1
  have hc := H.bijective_cechDeRhamComparison_degreeOne A'.hom hsm hsep hqc
  obtain ⟨-, -, -, ⟨-, hproj, -⟩, ⟨-, -, hto⟩, hbc⟩ := HD R A' g hA hg
  have key : ∀ c, S.r hI (m.pull1 c) = e (toHO1 A'.hom (cmp1 A'.hom c)) := fun c ↦ (he1 m c).symm
  have hr : Function.Surjective (S.r hI) := by
    intro y
    obtain ⟨x, rfl⟩ := e.surjective y
    obtain ⟨w, rfl⟩ := hto x
    obtain ⟨c, rfl⟩ := hc.2 w
    exact ⟨m.pull1 c, key c⟩
  haveI : Module.Projective R (GlobalTheory.CatCoh.H1 S.F) := Module.Projective.of_equiv e
  refine ⟨?_, exists_isCompl_ker_of_projective (S.r hI) hr⟩
  intro z hz
  have hz0 : S.redO.pullbackOneCocycle z = 0 := by
    refine Subtype.ext (funext fun U ↦ funext fun V ↦ funext fun a ↦ ?_)
    exact (S.ker V _).2 (hz U V a)
  have h0 : S.redO.pull1 (H1.mk _ z) = 0 := by
    rw [CoefMap.pullCohomologyOne_class, hz0, map_zero]
  set x := e.symm (H1.mk _ z) with hxdef
  have hx0 : IsPullO hpb.w x 0 := by
    have := he2 x
    rwa [hxdef, LinearEquiv.apply_symm_apply, h0] at this
  letI := π.toAlgebra
  obtain ⟨-, -, e', he'⟩ := hbc R₀ A₀.left A₀.hom i' hpb
  have h1 : e' ((1 : R₀) ⊗ₜ[R] x) = 0 := by
    have a := he' x
    unfold IsPullO at a hx0
    exact (pairRes_injective i' A₀.hom).1 (a.symm.trans (hx0.trans (map_zero _).symm))
  have hxI : x ∈ I • (⊤ : Submodule R (HO1 A'.hom)) :=
    mem_smul_top_of_tmul_eq_zero π hπ hk x ((LinearEquiv.map_eq_zero_iff e').1 h1)
  have hzI : H1.mk _ z ∈ I • (⊤ : Submodule R (GlobalTheory.CatCoh.H1 S.F)) := by
    have : H1.mk _ z = e x := by rw [hxdef, LinearEquiv.apply_symm_apply]
    rw [this]
    have hm' : e.toLinearMap x ∈ Submodule.map e.toLinearMap (I • ⊤) := Submodule.mem_map_of_mem hxI
    rw [Submodule.map_smul''] at hm'
    exact Submodule.smul_mono le_rfl le_top hm'
  have hsurjI : Submodule.map (S.r hI) (I • ⊤) = I • (⊤ : Submodule R (GlobalTheory.CatCoh.H1 S.F)) := by
    rw [Submodule.map_smul'', Submodule.map_top, LinearMap.range_eq_top.2 hr]
  rw [← hsurjI] at hzI
  obtain ⟨c, hc, hcz⟩ := hzI
  exact ⟨c, hc, hcz⟩

end GlobalTheory.LiftSys
end
end

section

open NumberField MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.AllWt GlobalTheory.LevGeo
open scoped ENNReal

namespace GlobalTheory.SupModel

open Classical

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem pnorm_nonneg₀ {r : ℕ} (X : Data E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (y : Frame X.Ψ r) :
    0 ≤ X.pnorm la P y := by
  unfold Data.pnorm; positivity

theorem pnorm_lact_eq {r : ℕ} (X : Data E r) {la : Wt X.Ψ r} {P : Frame X.Ψ r → ℂ} (hP : X.IsSec la P)
    {γ : GL (Fin r) E} (hγ : γ ∈ X.Γ) {y : Frame X.Ψ r} (hy : y ∈ X.dom) :
    X.pnorm la P (lact γ y) = X.pnorm la P y := by
  have hχ : ‖X.χ la γ‖ = 1 := by
    obtain ⟨n, hn, h⟩ := X.χ_fin la
    have := congrArg norm (h γ hγ)
    rw [norm_pow, norm_one] at this
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn.ne').1 this
  unfold Data.pnorm dmin
  simp only [GlobalTheory.MajInv.gram_lact X (X.Γ_stab γ hγ)]
  rw [hP.2.2 γ hγ _ hy, norm_mul, hχ, one_mul]

theorem pnorm_piecewise_eq {r : ℕ} (X : Data E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) {y : Frame X.Ψ r}
    (hy : y ∈ X.dom) : X.pnorm la (X.dom.piecewise P 0) y = X.pnorm la P y := by
  unfold Data.pnorm
  rw [Set.piecewise_eq_of_mem _ _ _ hy]

theorem epStar_eq_epsLev (d M : ℕ) (w M' k0 : ℝ) (hk : M' * k0 = 2 * (M : ℝ) * Real.sqrt d) :
    epStar M' (fdeg E) w k0 = epsLev E d M w := by
  unfold epsLev epStar
  congr 2
  rw [show M' * ((fdeg E : ℝ) * w + 2) * k0 * Real.log 2 = (M' * k0) * ((fdeg E : ℝ) * w + 2) * Real.log 2 by ring, hk]
  ring

theorem comp_bound {r : ℕ} (hr : 0 < r) (X : Data E r) (Xx : DataX E r) (hX : Xx.toData = X) (la : Wt X.Ψ r)
    (P : Frame X.Ψ r → ℂ) (hP : P ∈ X.SS la) (w : ℝ) (hw0 : 0 < w) (hw : (∑ τ, X.spread la τ) ≤ w)
    (hχ : ∀ γ ∈ X.Γ, X.χ la γ = 1) (d M : ℕ)
    (hL : ∀ γ ∈ Xx.Γ, ∀ v ∈ Xx.L', (γ : Matrix (Fin r) (Fin r) E).mulVec v ∈ Xx.L') (M' : ℝ) (hM' : 0 < M')
    (hk : M' * Xx.k0 = 2 * (M : ℝ) * Real.sqrt d)
    (hT : ∀ v ∈ Xx.L', herm Xx.Gm v v = 0 → ∀ b : E, cc b = b → IsIntegral ℤ b → ∃ γ ∈ Xx.Γ, ∀ τ : Xx.Ψ,
      (γ : Matrix (Fin r) (Fin r) E).map τ.1 = Xx.flowMat v τ ((M' : ℂ) * τ.1 b))
    (x0 : Frame X.Ψ r) (FF : Set (ReciprocityTheory.L2DbarEstimates.V (nd X))) (ho : IsOrth X x0) (hF : IsFundSet X x0 FF) :
    ∀ y ∈ X.dom, ENNReal.ofReal (X.pnorm la P y ^ 2) ≤ ENNReal.ofReal (locConst E r w (epsLev E d M w)) *
      ∫⁻ z in FF, ENNReal.ofReal (X.pnorm la (X.dom.piecewise P 0) (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x0 z) ^ 2) ∂(muF X x0) := by
  subst hX
  intro y hy
  have h := GlobalTheory.T.cuspForm_sup_norm_le_petersson_integral_component E r Xx la P M' w x0 FF hr hP hM' hw hw0 hL
    (fun v hv hiso b hb hbi => by
      obtain ⟨γ, hγ, he⟩ := hT v hv hiso b hb hbi
      exact ⟨γ, hγ, hχ γ hγ, he⟩) ho hF y hy
  rw [epStar_eq_epsLev d M w M' Xx.k0 hk] at h
  refine h.trans (mul_le_mul' le_rfl ?_)
  have hae : ∀ᵐ z ∂(muF Xx.toData x0), z ∈ OmF Xx.toData x0 := by
    have h1 : ∀ᵐ z ∂(volume.restrict (OmF Xx.toData x0)), z ∈ OmF Xx.toData x0 :=
      ae_restrict_mem (ExF.isOpen_OmF Xx.toData x0).measurableSet
    exact (withDensity_absolutelyContinuous _ _).ae_le h1
  refine lintegral_mono_ae (ae_restrict_of_ae ?_)
  filter_upwards [hae] with z hz
  rw [pnorm_piecewise_eq Xx.toData la P hz]

end GlobalTheory.SupModel


open GlobalTheory.SupModel in
theorem GlobalTheory.supPet_principal : GlobalTheory.UCls.MassBound → GlobalTheory.UCls.TorusBound → ∀ (D : D7) (j : ℕ) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ D.R.r) (dict : ∀ σ : c.F →+* ℂ, GA D (D.sp.W j) → Σ k, Frame ((U σ).X k).Ψ D.R.r), Laws D j Xo c U dict → ∀ σ, GoodEmb c σ → ∀ (la : ∀ k, Wt ((U σ).X k).Ψ D.R.r) (w : ℝ), 0 < w → (∀ k, (∑ τ, ((U σ).X k).spread (la k) τ) ≤ w) → (∀ k, ∀ γ ∈ ((U σ).X k).Γ, ((U σ).X k).χ (la k) γ = 1) → ∀ P ∈ holSub (U σ).X la, supE (U σ).X la P ^ 2 ≤ ENNReal.ofReal (supConst D.host.E D.R.r D.host.d l.M w) * petE (D.sp.W j) (dict σ) (muQ1 (D.sp.W j)) la P ^ 2 := by
  classical
  intro hMB hTB D j H Dw l Xo c U dict hLw σ hσ la w hw0 hspread hχ P hP
  have hr : 0 < D.R.r := by
    have := D.R.m_add_three_le_k
    unfold Formalism.BasicNotions.Ranks.r
    omega
  have hcusp := abelian₂.holSub_SS siegelSpaceAlgebra_holds (U σ).X la hP
  have hdat := fun k => GlobalTheory.T.exists_selfDual_data_transvection_principal_level D j H Dw l Xo c U dict hLw σ hσ k
  choose Xx hXx hg hΛ hL' M' hM' hk hT using hdat
  have hfs : ∀ k, ∃ x0, IsOrth ((U σ).X k) x0 ∧ ∃ FF, IsFundSet ((U σ).X k) x0 FF := fun k => by
    obtain ⟨x0, ho, FF, hF, -⟩ := GlobalTheory.DriftCovolume.finMu_unconditional D.R.r ((U σ).X k)
    exact ⟨x0, ho, FF, hF⟩
  choose x0 ho FF hF using hfs

  set Φ : ∀ k, Frame ((U σ).X k).Ψ D.R.r → ℝ≥0∞ := fun k u =>
    ENNReal.ofReal (((U σ).X k).pnorm (la k) (((U σ).X k).dom.piecewise (P k) 0) u ^ 2) with hΦdef
  have hsec : ∀ k, ((U σ).X k).IsSec (la k) (P k) := fun k => (hcusp k).1.1
  have hΦm : ∀ k, Measurable (Φ k) := fun k => by
    have hm := GlobalTheory.PeterssonCompare.measurable_pnorm ((U σ).X k) (la k)
      (P := ((U σ).X k).dom.piecewise (P k) 0)
      ((hsec k).1.continuousOn.congr fun u hu => Set.piecewise_eq_of_mem _ _ _ hu)
      (fun u hu => by rw [Set.piecewise_eq_of_notMem _ _ _ hu]; rfl)
    exact ENNReal.measurable_ofReal.comp (hm.pow_const 2)
  have hΦΓ : ∀ k, ∀ γ ∈ ((U σ).X k).Γ, ∀ x ∈ ((U σ).X k).dom, Φ k (lact γ x) = Φ k x := by
    intro k γ hγ u hu
    have hu' := GlobalTheory.MajInv.lact_mem_dom ((U σ).X k) (((U σ).X k).Γ_stab γ hγ) hu
    simp only [hΦdef]
    rw [pnorm_piecewise_eq _ _ _ hu, pnorm_piecewise_eq _ _ _ hu', pnorm_lact_eq _ (hsec k) hγ hu]
  have hΦB : ∀ k, ∀ b ∈ Bor ((U σ).X k).Ψ D.R.r, ∀ x ∈ ((U σ).X k).dom, Φ k (rmul x b) = Φ k x := by
    intro k b hb u hu
    have hu' := OrthogonalFrameDomain.rmul_mem_dom ((U σ).X k) hu hb
    simp only [hΦdef]
    rw [pnorm_piecewise_eq _ _ _ hu, pnorm_piecewise_eq _ _ _ hu',
      FrameDegreeData.pnorm_rmul ((U σ).X k) (la k) (P k) (hsec k).2.1 u hu b hb]
  obtain ⟨hS0, hStop, hΦeq⟩ := GlobalTheory.T.adelicProbability_eq_normalised_fundamentalSets D j H Dw l Xo c U dict hLw σ hσ x0 FF (fun k => ⟨ho k, hF k⟩)
  have heq := hΦeq Φ hΦm hΦΓ hΦB
  have hms := GlobalTheory.T.framed_dictionary_bound hMB hTB D j H Dw l Xo c U dict hLw σ hσ x0 FF (fun k => ⟨ho k, hF k⟩)

  obtain ⟨Kf, th, hr', -, -, hU, -⟩ := hLw.dictU σ hσ
  have hdom : ∀ g, (dict σ g).2 ∈ ((U σ).X (dict σ g).1).dom := hU.2.2.2.1

  have hpet : (∫⁻ q, Φ (dict σ q.out).1 (dict σ q.out).2 ∂(muQ1 (D.sp.W j))) =
      petE (D.sp.W j) (dict σ) (muQ1 (D.sp.W j)) la P ^ 2 := by
    rw [petE, eLpNorm'_eq_lintegral_eNorm, ← ENNReal.rpow_natCast,
      ← ENNReal.rpow_mul]
    norm_num
    refine lintegral_congr fun q => ?_
    simp only [hΦdef, ptN]
    rw [pnorm_piecewise_eq _ _ _ (hdom _), Real.enorm_eq_ofReal (pnorm_nonneg₀ _ _ _ _), ← ENNReal.ofReal_pow (pnorm_nonneg₀ _ _ _ _)]
  set S := ∑ k, muF ((U σ).X k) (x0 k) (FF k) with hSdef

  have hpt : ∀ p : Formalism.L2.Pj.FPt (U σ).X, ENNReal.ofReal (((U σ).X p.1).pnorm (la p.1) (P p.1) p.2) ^ 2 ≤
      ENNReal.ofReal (supConst D.host.E D.R.r D.host.d l.M w) * petE (D.sp.W j) (dict σ) (muQ1 (D.sp.W j)) la P ^ 2 := by
    rintro ⟨k, y, hy⟩
    rw [← ENNReal.ofReal_pow (pnorm_nonneg₀ _ _ _ _)]
    have h1 := GlobalTheory.SupModel.comp_bound hr ((U σ).X k) (Xx k) (hXx k) (la k) (P k) (hcusp k) w hw0 (hspread k) (hχ k)
      D.host.d l.M (hL' k) (M' k) (hM' k) (hk k) (hT k) (x0 k) (FF k) (ho k) (hF k) y hy
    have h2 : (∫⁻ z in FF k, Φ k (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt ((U σ).X k) (x0 k) z) ∂(muF ((U σ).X k) (x0 k))) ≤
        petE (D.sp.W j) (dict σ) (muQ1 (D.sp.W j)) la P ^ 2 * ENNReal.ofReal (massLev D.host.E D.R.r l.M) := by
      calc _ ≤ ∑ k', ∫⁻ z in FF k', Φ k' (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt ((U σ).X k') (x0 k') z) ∂(muF ((U σ).X k') (x0 k')) :=
            Finset.single_le_sum (f := fun k' => ∫⁻ z in FF k', Φ k' (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt ((U σ).X k') (x0 k') z)
              ∂(muF ((U σ).X k') (x0 k'))) (fun _ _ => bot_le) (Finset.mem_univ k)
        _ = petE (D.sp.W j) (dict σ) (muQ1 (D.sp.W j)) la P ^ 2 * S := by rw [← heq, hpet]
        _ ≤ _ := mul_le_mul' le_rfl hms
    by_cases hLc : 0 ≤ locConst D.host.E D.R.r w (epsLev D.host.E D.host.d l.M w)
    · calc _ ≤ ENNReal.ofReal (locConst D.host.E D.R.r w (epsLev D.host.E D.host.d l.M w)) * (petE (D.sp.W j) (dict σ) (muQ1 (D.sp.W j)) la P ^ 2 * ENNReal.ofReal (massLev D.host.E D.R.r l.M)) :=
            h1.trans (mul_le_mul' le_rfl h2)
        _ = _ := by
          rw [supConst, ENNReal.ofReal_mul hLc]
          ring
    · rw [ENNReal.ofReal_of_nonpos (le_of_lt (not_le.mp hLc)), zero_mul] at h1
      exact (le_antisymm h1 bot_le) ▸ bot_le

  show (⨆ p : Formalism.L2.Pj.FPt (U σ).X, ENNReal.ofReal (((U σ).X p.1).pnorm (la p.1) (P p.1) p.2)) ^ 2 ≤ _
  rcases isEmpty_or_nonempty (Formalism.L2.Pj.FPt (U σ).X) with hE | hN
  · rw [iSup_of_empty]; simp
  · rw [ENNReal.iSup_pow]
    exact iSup_le hpt
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram)

theorem _root_.GlobalTheory.T.rowEigensystem_carried_by_finite_type : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) {s : ℕ}, GlobalTheory.Chain.LiftInteg D → A3.fam3.Ok3 s → R.WeakCharacterisation F → R.toRealDat.ExAt → SchurAll R.toRealDat → (∀ P, Good R.toRealDat A3.A.μ0 P → _root_.Formalism.DivisionValues.conjPl P = P → TwoSided R.toRealDat A3.A.μ0 P) → ((∀ t (k : A3.okI t × List ℕ), A3.heckeRI t k = 0 ∨ ∃ y, Formalism.L2.Col.InertTypeOk (A3.A.fam.R t).n y ∧ A3.heckeRI t k = A3.heckeRI t (k.1, y)) ∧ ∀ j t (k : A3.okI t × List ℕ), A3.heckeLI j t k = 0 ∨ ∃ y, Formalism.L2.Col.InertTypeOk (A3.A.fam.L j t).n y ∧ A3.heckeLI j t k = A3.heckeLI j t (k.1, y)) → R.PGEquiv F → Nonempty A3.fam3.base3.Ix → (∀ c, R.EEc c ≠ ⊥ → ∃ p, R.Carries p c) := by
  first | exact @GlobalTheory.Div.carries_of_eEc_ne_bot | exact GlobalTheory.Div.carries_of_eEc_ne_bot | (intros; apply GlobalTheory.Div.carries_of_eEc_ne_bot <;> assumption)
end

section

open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdTh.VecNeCore

theorem thetaVector_ne_zero_core : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → ∀ i, VStd D i → R.vP i A.μ0 ≠ 0 := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hC i _
  exact GlobalTheory.AdTh.VecNe.thPVec_ne_zero (GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (hC.lev.βV i))
    (GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (hC.lev.βW i))
    ((D.sp.W_rank _ (Nat.le_add_left _ _) i.2).trans_le (r_le_V i)) (hC.thP.vP i A.μ0)

end GlobalTheory.AdTh.VecNeCore
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram)
namespace GlobalTheory.FixAllGood
open GlobalTheory.Hk3 (UnrPl VacFix)

theorem unrPl_mul {D : D7} {P : Pl D.host.E} {χ χ' : (AE D)ˣ →* Circle} (h : UnrPl P χ) (h' : UnrPl P χ') :
    UnrPl P (χ * χ') := fun e f hP x a b c => by
  rw [MonoidHom.mul_apply, h e f hP x a b c, h' e f hP x a b c, mul_one]

theorem unrPl_inv {D : D7} {P : Pl D.host.E} {χ : (AE D)ˣ →* Circle} (h : UnrPl P χ) :
    UnrPl P χ⁻¹ := fun e f hP x a b c => by
  rw [MonoidHom.inv_apply, h e f hP x a b c, inv_one]

theorem unrPl_chrStep {D : D7} {P : Pl D.host.E} {μ : ℕ → (AE D)ˣ →* Circle} {η : (AE D)ˣ →* Circle} {j : ℕ}
    (hμ : UnrPl P (μ j)) (hη : UnrPl P η) :
    UnrPl P (Lift.chrStep μ η j).1 ∧ UnrPl P (Lift.chrStep μ η j).2 := by
  unfold Lift.chrStep
  split_ifs
  · exact ⟨unrPl_mul hμ (unrPl_inv hη), hμ⟩
  · exact ⟨hμ, unrPl_mul hμ (unrPl_inv hη)⟩

theorem unrPl_chrTh {D : D7} {P : Pl D.host.E} {μ : ℕ → (AE D)ˣ →* Circle} {η : (AE D)ˣ →* Circle} {j : ℕ}
    (hμ : UnrPl P (μ j)) (hη : UnrPl P η) :
    UnrPl P (Lift.chrTh μ η j).1 ∧ UnrPl P (Lift.chrTh μ η j).2 :=
  ⟨hμ, unrPl_mul hμ (unrPl_inv hη)⟩

theorem fixAll_of_good : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), R.WeakCharacterisation F → R.toRealDat.ExAt → ∀ t P, Good R.toRealDat t P → Formalism.DivisionValues.conjPl P = P → FixAll R.toRealDat t P := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F h _ t P hP _
  have hu := GlobalTheory.T.splittingCharacters_unramified_offLevels R.toRealDat F.lv2 h.base.lev t P hP
  have hm := D.R.two_le_m
  refine ⟨fun k hk => ?_, ?_, fun i => ?_⟩
  · have hc := unrPl_chrStep (hu.2 (k + 1) (Nat.le_add_left _ _) hk.le) hu.1
    exact GlobalTheory.ConjVacFix.vacFix_of_unrPl _ _ _ _ _ _ P (h.fullY t k hk).datum hc.1 hc.2
  · have hc := unrPl_chrStep (hu.2 D.R.m (by omega) le_rfl) hu.1
    exact GlobalTheory.ConjVacFix.vacFix_of_unrPl _ _ _ _ _ _ P (h.fullX t).datum hc.1 hc.2
  · have hc := unrPl_chrTh (hu.2 ((i : ℕ) + 1) (Nat.le_add_left _ _) i.2) hu.1
    exact GlobalTheory.ConjVacFix.vacFix_of_unrPl _ _ _ _ _ _ P (h.fullP i t).datum hc.1 hc.2

end GlobalTheory.FixAllGood
end
