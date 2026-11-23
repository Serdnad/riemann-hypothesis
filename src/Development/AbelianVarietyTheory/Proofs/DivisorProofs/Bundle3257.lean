module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3104
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3234
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3224
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3211
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle533
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3172
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle440
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2932
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3133
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle578
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle535
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle019
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2875
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle066
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2920
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3132
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3230
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleIdentityIso
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2970
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3232
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3190
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
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBoxGenOfSection

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep

noncomputable section

namespace GlobalTheory.USepCov

theorem exists_cover : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c), ∀ (J : C.Z.IdealSheafData), (∀ x ∈ J.support, x ∉ Set.range C.i) → ∀ (S : Scheme.{0}) (π : S ⟶ pullback C.z (spMap C.b)), IsNormBl π (J.comap (pullback.fst C.z (spMap C.b))) → ∀ (M : Scheme.{0}) [IsIntegral M] (g : M ⟶ C.Z) (z₁ : M) (ζ : Sp (M.presheaf.stalk z₁) ⟶ pullback C.z (spMap C.b)), IsCov C g z₁ ζ → ∃ (S₁ : Scheme.{0}) (_ : IsIntegral S₁) (p₁ : S₁ ⟶ M) (sM : M ⟶ Sp ℤ) (U₁ : S₁.Opens), LocallyOfFiniteType sM ∧ QuasiCompact sM ∧ Flat (p₁ ≫ sM) ∧ ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme S₁ ∧ IsProper p₁ ∧ IsDominant p₁ ∧ FinalTheorems.EffCartier (J.comap (p₁ ≫ g)) ∧ (U₁ : Set S₁).Nonempty ∧ (∀ (K : Type) [Field K] (x : Sp K ⟶ S₁) (ev : M.presheaf.stalk z₁ →+* K), x ≫ p₁ = spMap ev ≫ M.fromSpecStalk z₁ → Set.range x ⊆ (U₁ : Set S₁) → ∃ y : Sp K ⟶ Xo.XF c, y ≫ C.iF = spMap ev ≫ ζ) ∧ ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsIntegrallyClosed R] (a : Sp R ⟶ S) (ev : M.presheaf.stalk z₁ →+* R), a ≫ π = spMap ev ≫ ζ → Set.range (jK R ≫ a ≫ π) ⊆ Set.range C.iF → ∃ ξ₁ : Sp R ⟶ S₁, ξ₁ ≫ p₁ = spMap ev ≫ M.fromSpecStalk z₁ ∧ ∀ (K : Type) [Field K] [IsAlgClosed K] (ev' : R →+* K) (k₀ : Subfield K), IsAlgClosed k₀ → (∀ p, (spMap ev' ≫ a) p = a (closedPoint R)) → GlobalTheory.UChart.DefOver k₀ (spMap ev' ≫ a) → (∀ p, (spMap ev' ≫ ξ₁) p = ξ₁ (closedPoint R)) ∧ GlobalTheory.UChart.DefOver k₀ (spMap ev' ≫ ξ₁) := by
  intro E _ _ _ H Dw _ l Xo c C J hJi S π hNB M _ g z₁ ζ hcov
  obtain ⟨hMn, ⟨U, g', hg'fin, hg'U, hUF⟩, hζ, hgen⟩ := hcov
  haveI := hg'fin
  haveI := C.ft
  haveI : Algebra.FiniteType ℤ (CommRingCat.of C.o) := ‹Algebra.FiniteType ℤ C.o›
  haveI : IsNoetherianRing C.o := Algebra.FiniteType.isNoetherianRing ℤ _
  haveI := C.iF_open
  obtain ⟨Z', b, hB, hBproj, -⟩ := GlobalTheory.ProjBlowup.exists_blowup C.z C.proj J
  haveI : IsProper C.z := by
    obtain ⟨m, e, he, he'⟩ := C.proj
    haveI := he
    have := isProper_str C.o m
    rw [← he']
    infer_instance
  haveI : IsProper (b ≫ C.z) := by
    obtain ⟨m, e, he, he'⟩ := hBproj
    haveI := he
    have := isProper_str C.o m
    rw [← he']
    infer_instance
  haveI : IsProper b := IsProper.of_comp b C.z
  obtain ⟨-, S₀, π₀, ν, -, hB₀, hνπ, -, -, -, -⟩ := hNB
  obtain ⟨ψ₀, hψ₀, -⟩ := hB.2 S₀ (π₀ ≫ pullback.fst C.z (spMap C.b))
    (by rw [Scheme.IdealSheafData.comap_comp]; exact hB₀.1)
  have hψU : Set.range ψ₀ ⊆ Set.range (b ⁻¹ᵁ U).ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨s, rfl⟩
    show b (ψ₀ s) ∈ U
    rw [← Scheme.Hom.comp_apply, hψ₀, Scheme.Hom.comp_apply]
    exact hUF ⟨_, rfl⟩
  let ψU : S₀ ⟶ (b ⁻¹ᵁ U).toScheme := IsOpenImmersion.lift (b ⁻¹ᵁ U).ι ψ₀ hψU
  have hψUf : ψU ≫ (b ⁻¹ᵁ U).ι = ψ₀ := IsOpenImmersion.lift_fac _ _ _
  have hψUb : ψU ≫ (b ∣_ U) ≫ U.ι = π₀ ≫ pullback.fst C.z (spMap C.b) := by
    rw [morphismRestrict_ι, ← Category.assoc, hψUf, hψ₀]
  have hpt : ∀ q : Sp (M.presheaf.stalk z₁), g (M.fromSpecStalk z₁ q) = pullback.fst C.z (spMap C.b) (ζ q) := by
    intro q
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hζ]
  haveI := hMn
  haveI : IsDomain (M.presheaf.stalk z₁) := inferInstance
  let p0 : Sp (M.presheaf.stalk z₁) := ⟨⊥, Ideal.isPrime_bot⟩
  obtain ⟨y0, hy0⟩ := hgen p0 rfl
  let m0 : M := M.fromSpecStalk z₁ p0
  have hm0 : g m0 = C.i y0 := by
    rw [hpt, ← hy0]; rfl
  have hgm : ∀ m, g m ∈ Set.range C.i → (g' ≫ U.ι) m ∉ J.support := by
    intro m ⟨y, hy⟩ hJ
    rw [hg'U] at hJ
    exact hJi _ hJ ⟨y, hy⟩
  have hm0J : (g' ≫ U.ι) m0 ∉ J.support := hgm m0 ⟨y0, hm0.symm⟩
  obtain ⟨S₁, hS₁i, p₁, ν₁, hS₁n, hp₁P, hν₁fin, hcomm, hEff, hrange, hlift⟩ :=
    GlobalTheory.T.exists_normalisation_blowup_pullback_finiteCover (o := CommRingCat.of C.o) C.z b J hB U g' ⟨m0, hm0J⟩
  haveI := hν₁fin

  haveI : IsPreimmersion (spMap C.b) := by
    letI := C.b.toAlgebra
    haveI := C.isFractionRing
    exact IsPreimmersion.of_isLocalization (nonZeroDivisors C.o)
  obtain ⟨W', hW'o, hW'⟩ := ((IsPreimmersion.isEmbedding (pullback.fst C.z (spMap C.b))).isInducing.isOpen_iff).mp
    C.iF.isOpenMap.isOpen_range
  let sM : M ⟶ Sp ℤ := g ≫ C.z ≫ Spec.map (CommRingCat.ofHom (algebraMap ℤ C.o))
  obtain ⟨x0, hx0⟩ := hrange m0 hm0J
  haveI hSpecZ : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap ℤ C.o))) := by
    rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
    exact RingHom.finiteType_algebraMap.mpr inferInstance
  refine ⟨S₁, hS₁i, p₁, sM, (p₁ ≫ g) ⁻¹ᵁ ⟨W', hW'o⟩, ?_, ?_, ?_, hS₁n, hp₁P, ?_, ?_, ?_, ?_, ?_⟩
  · show LocallyOfFiniteType (g ≫ C.z ≫ Spec.map (CommRingCat.ofHom (algebraMap ℤ C.o)))
    rw [← hg'U]
    infer_instance
  · show QuasiCompact (g ≫ C.z ≫ Spec.map (CommRingCat.ofHom (algebraMap ℤ C.o)))
    haveI : IsLocallyNoetherian C.Z := LocallyOfFiniteType.isLocallyNoetherian (C.z ≫ Spec.map (CommRingCat.ofHom (algebraMap ℤ C.o)))
    rw [← hg'U]
    infer_instance
  · apply GlobalTheory.T.flat_int_of_integral_scheme_generic_point _ x0
    have eM : C.i ≫ C.z ≫ Spec.map (CommRingCat.ofHom (algebraMap ℤ C.o)) =
        (C.iF ≫ pullback.snd C.z (spMap C.b)) ≫ Spec.map (CommRingCat.ofHom (C.b.comp (algebraMap ℤ C.o))) := by
      simp only [UCompact.i, Category.assoc, pullback.condition_assoc]
      rw [← Spec.map_comp]; rfl
    have e : (p₁ ≫ sM) x0 = Spec.map (CommRingCat.ofHom (C.b.comp (algebraMap ℤ C.o))) ((C.iF ≫ pullback.snd C.z (spMap C.b)) y0) := by
      rw [← Scheme.Hom.comp_apply, ← eM]
      show (C.z ≫ Spec.map (CommRingCat.ofHom (algebraMap ℤ C.o))) (g (p₁ x0)) = _
      rw [hx0, hm0]
      rfl
    rw [e]
    show Ideal.comap _ _ = ⊥
    haveI := ((C.iF ≫ pullback.snd C.z (spMap C.b)) y0).isPrime
    rw [Ideal.eq_bot_of_prime (((C.iF ≫ pullback.snd C.z (spMap C.b)) y0).asIdeal), Ideal.comap_bot_of_injective]
    exact fun u v h => Int.cast_injective (α := c.F) (by simpa using h)
  · constructor
    have hVo : IsOpen {m : M | (g' ≫ U.ι) m ∉ J.support} :=
      (g' ≫ U.ι).continuous.isOpen_preimage _ J.support.isClosed.isOpen_compl
    exact (hVo.dense ⟨m0, hm0J⟩).mono fun m hm => hrange m hm
  · rw [← hg'U]; exact hEff
  · refine ⟨x0, ?_⟩
    show g (p₁ x0) ∈ W'
    rw [hx0, hpt]
    show ζ p0 ∈ pullback.fst C.z (spMap C.b) ⁻¹' W'
    rw [hW']; exact ⟨y0, hy0⟩
  · intro K _ x ev hx hxU
    have hr : Set.range (spMap ev ≫ ζ) ⊆ Set.range C.iF := by
      rintro _ ⟨w, rfl⟩
      rw [← hW']
      show pullback.fst C.z (spMap C.b) (ζ (spMap ev w)) ∈ W'
      rw [← hpt, ← Scheme.Hom.comp_apply (spMap ev), ← hx, Scheme.Hom.comp_apply]
      exact hxU ⟨w, rfl⟩
    exact ⟨IsOpenImmersion.lift C.iF _ hr, IsOpenImmersion.lift_fac _ _ _⟩
  · intro R _ _ _ _ a ev ha hgR
    let β : Sp R ⟶ M := spMap ev ≫ M.fromSpecStalk z₁
    have hβg : β ≫ g = a ≫ π ≫ pullback.fst C.z (spMap C.b) := by
      simp only [β, Category.assoc, ← hζ]
      rw [← Category.assoc a π, ha, Category.assoc]
    have hab : (a ≫ ν ≫ ψU) ≫ (b ∣_ U) = β ≫ g' := by
      rw [← cancel_mono U.ι, Category.assoc, Category.assoc, Category.assoc, hψUb, Category.assoc, hg'U, hβg,
        ← hνπ, Category.assoc]
    have hgw : ∀ w, (jK R ≫ β ≫ g' ≫ U.ι) w ∉ J.support := by
      intro w
      have e : jK R ≫ β ≫ g' ≫ U.ι = (jK R ≫ a ≫ π) ≫ pullback.fst C.z (spMap C.b) := by
        rw [hg'U, hβg]; simp only [Category.assoc]
      rw [e]
      obtain ⟨y, hy⟩ := hgR ⟨w, rfl⟩
      intro hJ
      refine hJi _ hJ ⟨y, ?_⟩
      show _ = pullback.fst C.z (spMap C.b) ((jK R ≫ a ≫ π) w)
      rw [← hy]; rfl
    obtain ⟨ξ₁, hξν, hξp⟩ := hlift R (a ≫ ν ≫ ψU) β hab hgw
    refine ⟨ξ₁, hξp, ?_⟩
    intro K _ _ ev' k₀ hk₀ hcl hdef
    refine ⟨fun p => ?_, ?_⟩
    · have e1 : ∀ t, ν₁ (ξ₁ t) = ψU (ν (a t)) := fun t => by
        rw [← Scheme.Hom.comp_apply, hξν]; rfl
      apply GlobalTheory.T.eq_of_specializes_same_fibre_isIntegralHom ν₁
      · exact (IsLocalRing.specializes_closedPoint _).map ξ₁.continuous
      · have e2 := e1 (closedPoint R)
        have e3 : a ((spMap ev') p) = a (closedPoint R) := hcl p
        rw [Scheme.Hom.comp_apply, e1, e3]
        exact e2.symm
    · apply GlobalTheory.T.pointDefinedOverSubfield_of_isIntegralHom ν₁ k₀ hk₀
      obtain ⟨P₀, hP₀⟩ := hdef
      refine ⟨P₀ ≫ ν ≫ ψU, ?_⟩
      simp only [Category.assoc, hξν]
      rw [reassoc_of% hP₀]

end GlobalTheory.USepCov
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep
open GlobalTheory.UT.CoefBasic

theorem _root_.GlobalTheory.T.thetaMember_torus_character_unique : ∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (Y : Type) [AddCommGroup Y] (t : Y → V) (δ : I → Y → Y) (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev Y t δ) (τ : X₁.S.Gam) (χ χ' : Multiplicative 𝔪.D.toPre.X →* (FractionRing V)ˣ), GlobalTheory.GSep.TransTerms.TorChar 𝔪 τ χ → GlobalTheory.GSep.TransTerms.TorChar 𝔪 τ χ' → χ = χ' := by
  first | exact @GlobalTheory.GSep.TorCharUnique.torChar_unique | exact GlobalTheory.GSep.TorCharUnique.torChar_unique | (intros; apply GlobalTheory.GSep.TorCharUnique.torChar_unique <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam GlobalTheory.MumProd

theorem _root_.GlobalTheory.T.productData_firstFactor_adjointPair : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D D₁ D₂ : DegData R I) (p₁ : D.toPre.P.A ⟶ D₁.toPre.P.A) (p₂ : D.toPre.P.A ⟶ D₂.toPre.P.A) (q₁ : D.toPre.X →+ D₁.toPre.X) (q₂ : D.toPre.X →+ D₂.toPre.X), IsSumDeg D.toPre D₁.toPre D₂.toPre p₁ p₂ q₁ q₂ → ∀ (i₁ : D₁.toPre.P.A ⟶ D.toPre.P.A) (j₁ : D₁.toPre.X →+ D.toPre.X), i₁ ≫ p₁ = 𝟙 _ → i₁ ≫ p₂ = toUnit _ ≫ η[D₂.toPre.P.A] → (∀ y, q₁ (j₁ y) = y) → (∀ y, q₂ (j₁ y) = 0) → Adj (pol D₁) (pol D) i₁ p₁ j₁ q₁ := by
  first | exact @GlobalTheory.MumProdAdj.adj_first_factor | exact GlobalTheory.MumProdAdj.adj_first_factor | (intros; apply GlobalTheory.MumProdAdj.adj_first_factor <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam GlobalTheory.MumProd GlobalTheory.ProdUnif

noncomputable section

namespace GlobalTheory.ProdTorusExt

section Torus

variable {S : Scheme.{0}} {X X' X'' : Type} [AddCommGroup X] [AddCommGroup X'] [AddCommGroup X'']

theorem torusMap_comp' (a : X →+ X') (b : X'' →+ X) :
    GlobalTheory.SplitTorusPow.torusMap S a ≫ GlobalTheory.SplitTorusPow.torusMap S b = GlobalTheory.SplitTorusPow.torusMap S (a.comp b) := by
  apply (GlobalTheory.splitTorusPointsEquiv S X'' _).injective
  conv_rhs => rw [← Category.id_comp (GlobalTheory.SplitTorusPow.torusMap S (a.comp b))]
  conv_lhs => rw [← Category.id_comp (GlobalTheory.SplitTorusPow.torusMap S a)]
  rw [Category.assoc, ← Category.assoc (𝟙 _), GlobalTheory.SplitTorusPow.points_comp_torusMap,
    GlobalTheory.SplitTorusPow.points_comp_torusMap, GlobalTheory.SplitTorusPow.points_comp_torusMap]
  rfl

theorem torusMap_id' : GlobalTheory.SplitTorusPow.torusMap S (AddMonoidHom.id X) = 𝟙 _ := by
  apply (GlobalTheory.splitTorusPointsEquiv S X _).injective
  conv_lhs => rw [← Category.id_comp (GlobalTheory.SplitTorusPow.torusMap S (AddMonoidHom.id X))]
  rw [GlobalTheory.SplitTorusPow.points_comp_torusMap]
  rfl

theorem isIso_lift_torusMap {X₁ X₂ : Type} [AddCommGroup X₁] [AddCommGroup X₂] (E : X ≃+ X₁ × X₂) :
    IsIso (lift (GlobalTheory.SplitTorusPow.torusMap S (E.symm.toAddMonoidHom.comp (AddMonoidHom.inl X₁ X₂)))
      (GlobalTheory.SplitTorusPow.torusMap S (E.symm.toAddMonoidHom.comp (AddMonoidHom.inr X₁ X₂)))) := by
  haveI := GlobalTheory.SemiProd.torus_prod_iso S X₁ X₂
  have e : lift (GlobalTheory.SplitTorusPow.torusMap S (E.symm.toAddMonoidHom.comp (AddMonoidHom.inl X₁ X₂)))
      (GlobalTheory.SplitTorusPow.torusMap S (E.symm.toAddMonoidHom.comp (AddMonoidHom.inr X₁ X₂))) =
      GlobalTheory.SplitTorusPow.torusMap S E.symm.toAddMonoidHom ≫
        lift (GlobalTheory.SplitTorusPow.torusMap S (AddMonoidHom.inl X₁ X₂))
          (GlobalTheory.SplitTorusPow.torusMap S (AddMonoidHom.inr X₁ X₂)) := by
    rw [comp_lift, torusMap_comp', torusMap_comp']
  haveI : IsIso (GlobalTheory.SplitTorusPow.torusMap S E.symm.toAddMonoidHom) :=
    ⟨GlobalTheory.SplitTorusPow.torusMap S E.toAddMonoidHom, by
      rw [torusMap_comp', show E.symm.toAddMonoidHom.comp E.toAddMonoidHom = AddMonoidHom.id X from by ext; simp,
        torusMap_id'], by
      rw [torusMap_comp', show E.toAddMonoidHom.comp E.symm.toAddMonoidHom = AddMonoidHom.id (X₁ × X₂) from by
        ext <;> simp, torusMap_id']⟩
  rw [e]
  infer_instance

end Torus

end GlobalTheory.ProdTorusExt

namespace GlobalTheory.ProdTorusExt

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (e : ℕ) (D D₁ D₂ : DegPre R) (p₁ : D.P.A ⟶ D₁.P.A) (p₂ : D.P.A ⟶ D₂.P.A) (q₁ : D.X →+ D₁.X) (q₂ : D.X →+ D₂.X) (G₁ G₂ : Over (Sp R)) [GrpObj G₁] [IsCommMonObj G₁] [GrpObj G₂] [IsCommMonObj G₂] (g₁ : GtCoord I D₁ e G₁) (g₂ : GtCoord I D₂ e G₂), IsSumDeg D D₁ D₂ p₁ p₂ q₁ q₂ → ∃ (q : thickObj R I e (G₁ ⊗ G₂) ⟶ thickObj R I e D.P.A) (i : splitTorus (Sp (R ⧸ I ^ (e + 1))) D.X ⟶ thickObj R I e (G₁ ⊗ G₂)), IsMonHom q ∧ Flat q.left ∧ Surjective q.left ∧ IsAffineHom q.left ∧ IsMonHom i ∧ IsPullback i (toUnit _) q (η[thickObj R I e D.P.A]) ∧ q ≫ (Over.pullback (thick R I e)).map p₁ = ((Over.pullback (thick R I e)).map (fst G₁ G₂)) ≫ g₁.q ∧ q ≫ (Over.pullback (thick R I e)).map p₂ = ((Over.pullback (thick R I e)).map (snd G₁ G₂)) ≫ g₂.q ∧ (∀ h : D₁.X → D.X, (∀ y, q₁ (h y) = y) → (∀ y, q₂ (h y) = 0) → ∃ τ : splitTorus (Sp (R ⧸ I ^ (e + 1))) D.X ⟶ splitTorus (Sp (R ⧸ I ^ (e + 1))) D₁.X, TorusHomOf h τ ∧ i ≫ ((Over.pullback (thick R I e)).map (fst G₁ G₂)) = τ ≫ g₁.i) ∧ (∀ h : D₂.X → D.X, (∀ y, q₁ (h y) = 0) → (∀ y, q₂ (h y) = y) → ∃ τ : splitTorus (Sp (R ⧸ I ^ (e + 1))) D.X ⟶ splitTorus (Sp (R ⧸ I ^ (e + 1))) D₂.X, TorusHomOf h τ ∧ i ≫ ((Over.pullback (thick R I e)).map (snd G₁ G₂)) = τ ≫ g₂.i) := by
  intro R _ _ I e D D₁ D₂ p₁ p₂ q₁ q₂ G₁ G₂ _ _ _ _ g₁ g₂ hD
  let F := Over.pullback (thick R I e)
  let S₀ := Sp (R ⧸ I ^ (e + 1))
  haveI := hD.hom₁
  haveI := hD.hom₂
  haveI := g₁.q_hom
  haveI := g₂.q_hom
  haveI := g₁.i_hom
  haveI := g₂.i_hom
  let E : D.X ≃+ D₁.X × D₂.X := AddEquiv.ofBijective (q₁.prod q₂) hD.xsum
  let j₁ : D₁.X →+ D.X := E.symm.toAddMonoidHom.comp (AddMonoidHom.inl D₁.X D₂.X)
  let j₂ : D₂.X →+ D.X := E.symm.toAddMonoidHom.comp (AddMonoidHom.inr D₁.X D₂.X)
  let τ₁ := GlobalTheory.SplitTorusPow.torusMap S₀ j₁
  let τ₂ := GlobalTheory.SplitTorusPow.torusMap S₀ j₂
  have hτmon {X X' : Type} [AddCommGroup X] [AddCommGroup X'] (φ : X →+ X') :
      IsMonHom (GlobalTheory.SplitTorusPow.torusMap S₀ φ) := by
    refine ⟨?_, ?_⟩
    · have h : (1 : 𝟙_ (Over S₀) ⟶ splitTorus S₀ X') ≫
          GlobalTheory.SplitTorusPow.torusMap S₀ φ = 1 := by
        apply (GlobalTheory.splitTorusPointsEquiv S₀ X _).injective
        rw [GlobalTheory.SplitTorusPow.points_comp_torusMap, map_one, map_one, MonoidHom.one_comp]
      simpa [Hom.one_def] using h
    · have h {Z : Over S₀} (a b : Z ⟶ splitTorus S₀ X') :
          (a * b) ≫ GlobalTheory.SplitTorusPow.torusMap S₀ φ =
            (a ≫ GlobalTheory.SplitTorusPow.torusMap S₀ φ) *
              (b ≫ GlobalTheory.SplitTorusPow.torusMap S₀ φ) := by
        apply (GlobalTheory.splitTorusPointsEquiv S₀ X Z).injective
        rw [map_mul, GlobalTheory.SplitTorusPow.points_comp_torusMap,
          GlobalTheory.SplitTorusPow.points_comp_torusMap,
          GlobalTheory.SplitTorusPow.points_comp_torusMap, map_mul, MonoidHom.mul_comp]
      simpa only [Hom.mul_def, lift_fst_snd, Category.id_comp, lift_fst_comp_snd_comp] using
        h (fst (splitTorus S₀ X') (splitTorus S₀ X')) (snd _ _)
  haveI : IsMonHom τ₁ := hτmon j₁
  haveI : IsMonHom τ₂ := hτmon j₂
  haveI hτ : IsIso (lift τ₁ τ₂) := isIso_lift_torusMap E

  haveI hG : IsIso (lift (F.map (fst G₁ G₂)) (F.map (snd G₁ G₂))) :=
    isIso_prodComparison_of_preservesLimit_pair F G₁ G₂
  haveI := hD.lim
  have eB : lift (F.map p₁) (F.map p₂) = F.map (lift p₁ p₂) ≫ Functor.OplaxMonoidal.δ F D₁.P.A D₂.P.A :=
    (Functor.OplaxMonoidal.lift_δ F p₁ p₂).symm
  haveI hB : IsIso (lift (F.map p₁) (F.map p₂)) := by rw [eB]; infer_instance
  haveI : IsMonHom (inv (lift (F.map (fst G₁ G₂)) (F.map (snd G₁ G₂)))) :=
    inferInstanceAs (IsMonHom (asIso (lift (F.map (fst G₁ G₂)) (F.map (snd G₁ G₂)))).inv)
  haveI : IsMonHom (inv (lift (F.map p₁) (F.map p₂))) :=
    inferInstanceAs (IsMonHom (asIso (lift (F.map p₁) (F.map p₂))).inv)
  let q := lift (F.map (fst G₁ G₂)) (F.map (snd G₁ G₂)) ≫ (g₁.q ⊗ₘ g₂.q) ≫ inv (lift (F.map p₁) (F.map p₂))
  let i := lift τ₁ τ₂ ≫ (g₁.i ⊗ₘ g₂.i) ≫ inv (lift (F.map (fst G₁ G₂)) (F.map (snd G₁ G₂)))
  have hP : ∀ (P : MorphismProperty Scheme.{0}) [P.IsMultiplicative] [P.IsStableUnderBaseChange],
      P g₁.q.left → P g₂.q.left → P q.left := by
    intro P _ _ h₁ h₂
    haveI : IsIso (lift (F.map (fst G₁ G₂)) (F.map (snd G₁ G₂))).left :=
      inferInstanceAs (IsIso ((Over.forget _).map (lift (F.map (fst G₁ G₂)) (F.map (snd G₁ G₂)))))
    haveI : IsIso (inv (lift (F.map p₁) (F.map p₂))).left :=
      inferInstanceAs (IsIso ((Over.forget _).map (inv (lift (F.map p₁) (F.map p₂)))))
    rw [Over.comp_left, Over.comp_left]
    exact P.comp_mem _ _ (P.of_isIso _)
      (P.comp_mem _ _ (GlobalTheory.SemiProd.tensorHom_prop _ P _ _ _ _ _ _ h₁ h₂) (P.of_isIso _))
  have hq₁ : q ≫ F.map p₁ = F.map (fst G₁ G₂) ≫ g₁.q := by
    have : inv (lift (F.map p₁) (F.map p₂)) ≫ F.map p₁ = fst _ _ := by
      rw [IsIso.inv_comp_eq, lift_fst]
    rw [Category.assoc, Category.assoc, this, tensorHom_fst, lift_fst_assoc]
  have hq₂ : q ≫ F.map p₂ = F.map (snd G₁ G₂) ≫ g₂.q := by
    have : inv (lift (F.map p₁) (F.map p₂)) ≫ F.map p₂ = snd _ _ := by
      rw [IsIso.inv_comp_eq, lift_snd]
    rw [Category.assoc, Category.assoc, this, tensorHom_snd, lift_snd_assoc]
  have hi₁ : i ≫ F.map (fst G₁ G₂) = τ₁ ≫ g₁.i := by
    have : inv (lift (F.map (fst G₁ G₂)) (F.map (snd G₁ G₂))) ≫ F.map (fst G₁ G₂) = fst _ _ := by
      rw [IsIso.inv_comp_eq, lift_fst]
    rw [Category.assoc, Category.assoc, this, tensorHom_fst, lift_fst_assoc]
  have hi₂ : i ≫ F.map (snd G₁ G₂) = τ₂ ≫ g₂.i := by
    have : inv (lift (F.map (fst G₁ G₂)) (F.map (snd G₁ G₂))) ≫ F.map (snd G₁ G₂) = snd _ _ := by
      rw [IsIso.inv_comp_eq, lift_snd]
    rw [Category.assoc, Category.assoc, this, tensorHom_snd, lift_snd_assoc]

  have key := GlobalTheory.SemiProd.kernel_tensor _ _ _ _ _ _ _ g₁.i g₂.i g₁.q g₂.q g₁.isKernel g₂.isKernel
  have hK : IsPullback i (toUnit _) q (η[thickObj R I e D.P.A]) := by
    refine IsPullback.of_iso key (asIso (lift τ₁ τ₂)).symm
      (asIso (lift (F.map (fst G₁ G₂)) (F.map (snd G₁ G₂)))).symm (Iso.refl _)
      (asIso (lift (F.map p₁) (F.map p₂))).symm ?_ ?_ ?_ ?_
    · simp only [i, Iso.symm_hom, asIso_inv, Category.assoc, IsIso.inv_hom_id_assoc]
    · exact toUnit_unique _ _
    · simp only [q, Iso.symm_hom, asIso_inv, Category.assoc, IsIso.inv_hom_id_assoc]
    · simp only [Iso.refl_hom, Category.id_comp, Iso.symm_hom, asIso_inv]
      rw [IsIso.comp_inv_eq, IsMonHom.one_hom]

  have hE₁ : ∀ h : D₁.X → D.X, (∀ y, q₁ (h y) = y) → (∀ y, q₂ (h y) = 0) → h = j₁ := by
    intro h h₁ h₂
    funext y
    apply E.injective
    change (q₁.prod q₂) (h y) = E (E.symm (y, 0))
    rw [AddEquiv.apply_symm_apply]
    exact Prod.ext (h₁ y) (h₂ y)
  have hE₂ : ∀ h : D₂.X → D.X, (∀ y, q₁ (h y) = 0) → (∀ y, q₂ (h y) = y) → h = j₂ := by
    intro h h₁ h₂
    funext y
    apply E.injective
    change (q₁.prod q₂) (h y) = E (E.symm (0, y))
    rw [AddEquiv.apply_symm_apply]
    exact Prod.ext (h₁ y) (h₂ y)
  refine ⟨q, i, inferInstance, hP @Flat g₁.q_flat g₂.q_flat, hP @Surjective g₁.q_surj g₂.q_surj,
    hP @IsAffineHom g₁.q_affine g₂.q_affine, inferInstance, hK, hq₁, hq₂, fun h h₁ h₂ => ?_, fun h h₁ h₂ => ?_⟩
  · refine ⟨τ₁, ?_, hi₁⟩
    rw [hE₁ h h₁ h₂]
    exact GlobalTheory.MumProd.torusHomOf_torusMap j₁
  · refine ⟨τ₂, ?_, hi₂⟩
    rw [hE₂ h h₁ h₂]
    exact GlobalTheory.MumProd.torusHomOf_torusMap j₂

end GlobalTheory.ProdTorusExt
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum


theorem _root_.GlobalTheory.T.exists_frame_bundle_near_closedPoint_finite_etale_ext : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (hB : Base R) (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R') (hF : FinExt ρ) (hG : IsGal ρ) (D : DegData R (maximalIdeal R)) (D' : DegData R' (maximalIdeal R')) (hD : IsPullDeg ρ D.toPre D'.toPre) (A' : PolAV (Sp (FractionRing R'))) (G' : Over (Sp R')) [GrpObj G'] [IsCommMonObj G'] (hS' : IsSemiAbelian G') (U' : Unif (maximalIdeal R') D' A' G') (a : GalAct ρ hD U') (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (β : G'.left ⟶ G.left) (hS : IsSemiAbelian G) (hβ : IsGrpPullback G' G (spMap ρ) β) (hact : ∀ σ, a.act σ ≫ β = β) (θ : U'.LG.L.Sec), (∀ (σ : Gal ρ) (h : IsPullDeg (Gal.hom σ) D'.toPre D'.toPre) (bc : G' ≅ (Over.pullback (specOf (Gal.hom σ))).obj G'), bc.hom.left ≫ pullback.fst G'.hom (specOf (Gal.hom σ)) = a.act σ → ∀ hP : IsPullUnif (Gal.hom σ) h bc U' U', PullOver hD h → SecCarried U'.LG.L θ _ (Classical.choose hP.lg)) → ∀ O : G.left.Opens, (∃ g ∈ O, G.hom g = closedPoint R) → (∀ g' : G'.left, β g' ∈ O → G.hom (β g') = closedPoint R → g' ∈ secNz θ) → ∀ y : G.left, IsClosed ({y} : Set G.left) → G.hom y = closedPoint R → ∃ (R₁ : Type) (_ : CommRing R₁) (_ : IsDomain R₁) (_ : IsLocalRing R₁) (ρ₁ : R →+* R₁), FinExt ρ₁ ∧ ρ₁.Etale ∧ ∃ V₀ : G.left.Opens, y ∈ V₀ ∧ ∃ τ : ∀ k : U'.LG.L.ι, Γ(pullback (G'.hom ≫ spMap ρ) (spMap ρ₁), (pullback.fst (G'.hom ≫ spMap ρ) (spMap ρ₁)) ⁻¹ᵁ (β ⁻¹ᵁ V₀) ⊓ (pullback.fst (G'.hom ≫ spMap ρ) (spMap ρ₁)) ⁻¹ᵁ U'.LG.L.U k)ˣ, FrameAlong U'.LG.L (pullback.fst (G'.hom ≫ spMap ρ) (spMap ρ₁)) ((pullback.fst (G'.hom ≫ spMap ρ) (spMap ρ₁)) ⁻¹ᵁ (β ⁻¹ᵁ V₀)) τ ∧ (∀ (σ : Gal ρ) (h : IsPullDeg (Gal.hom σ) D'.toPre D'.toPre) (bc : G' ≅ (Over.pullback (specOf (Gal.hom σ))).obj G'), bc.hom.left ≫ pullback.fst G'.hom (specOf (Gal.hom σ)) = a.act σ → ∀ hP : IsPullUnif (Gal.hom σ) h bc U' U', PullOver hD h → ∀ f' : (pullback (G'.hom ≫ spMap ρ) (spMap ρ₁) : Scheme.{0}) ⟶ pullback (G'.hom ≫ spMap ρ) (spMap ρ₁), f' ≫ (pullback.fst (G'.hom ≫ spMap ρ) (spMap ρ₁)) = (pullback.fst (G'.hom ≫ spMap ρ) (spMap ρ₁)) ≫ a.act σ → f' ≫ (pullback.snd (G'.hom ≫ spMap ρ) (spMap ρ₁)) = (pullback.snd (G'.hom ≫ spMap ρ) (spMap ρ₁)) → FrameCarriedAlong U'.LG.L (pullback.fst (G'.hom ≫ spMap ρ) (spMap ρ₁)) ((pullback.fst (G'.hom ≫ spMap ρ) (spMap ρ₁)) ⁻¹ᵁ (β ⁻¹ᵁ V₀)) τ _ (Classical.choose hP.lg) f') := by
  first | exact @GlobalTheory.Mum.exists_carried_frame_upstairs | exact GlobalTheory.Mum.exists_carried_frame_upstairs | (intros; apply GlobalTheory.Mum.exists_carried_frame_upstairs <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.MumCmp

theorem exists_twist_of_samePol : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D₀ D : DegData R (maximalIdeal R)), SamePol D₀.toPre D.toPre → ∃ g : GtPt D.toPre (𝟙_ (Over (Sp R))), (∃ z : GtPt D.toPre (𝟙_ (Over (Sp R))), z.IsZero ∧ GtPt.IsAdd g g z) ∧ GlobalTheory.MumCmp.IsTwist D₀.toPre D.toPre g := by
  intro R _ _ _ hR D₀ D hS
  obtain ⟨β, xe, hβ, hc, wΛ, hwΛ, hτ⟩ := GlobalTheory.T.exists_iso_refinements_same_polarised R D₀.toPre D.toPre hS
  haveI : IsNoetherianRing R := hR.1.1
  obtain ⟨b, hb, w, hw⟩ := GlobalTheory.T.exists_translate_of_mumfordBundle_match R D₀.toPre D.toPre β hβ ⟨wΛ, hwΛ⟩
  obtain ⟨g, -, h2, ht⟩ := GlobalTheory.T.exists_order_two_point_torus_extension_translate R hR D₀ D β xe hβ hc wΛ hwΛ hτ b hb w hw
  exact ⟨g, h2, ht⟩

end GlobalTheory.MumCmp
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.MumCmp.LevelCmp

theorem exists_level_gen : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal R) D A G) (g : GtPt D.toPre (𝟙_ (Over (Sp R)))), (∃ z : GtPt D.toPre (𝟙_ (Over (Sp R))), z.IsZero ∧ GtPt.IsAdd g g z) → ∀ a : 𝟙_ (Over (Sp R)) ⟶ G, a ^ 2 = 1 → (∀ (e : ℕ) (ae : Spec (CommRingCat.of (R ⧸ maximalIdeal R ^ (e + 1))) ⟶ (thickObj R (maximalIdeal R) e G).left), ae ≫ (thickObj R (maximalIdeal R) e G).hom = 𝟙 _ → ae ≫ (fstG (maximalIdeal R) e G).left = thick R (maximalIdeal R) e ≫ a.left → ae ≫ (U.gt e).pG.left = thick R (maximalIdeal R) e ≫ g.b.left ∧ ∀ χ : D.toPre.X, LB.Gen.Corr D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ ((U.gt e).t χ) ae) (LB.pullGen D.toPre.P.L _ _ (g.s χ) (thick R (maximalIdeal R) e))) → ∀ (A₂ : PolAV (Sp (FractionRing R))) (D₂ : DegData R (maximalIdeal R)) (U₂ : Unif (maximalIdeal R) D₂ A₂ G) (wL : LB.Iso U₂.LG.L (U.LG.L.pull ((toUnit G ≫ a) * 𝟙 G).left)), wL.IsGen → ∀ β : D₂.toPre.P.A ≅ D.toPre.P.A, IsMonHom β.hom → (∀ e : ℕ, (U₂.gt e).pG.left ≫ β.hom.left = (U.gt e).pG.left) → ∀ w : LB.Iso D₂.toPre.P.L (LB.LinComb D.toPre.P.L (GlobalTheory.MumCmp.twφ D₂.toPre D.toPre β.hom g.b) GlobalTheory.MumCmp.twε), w.IsGen → ∃ ν : LB.Gen (LB.LinComb D.toPre.P.L (K := Fin 2) ![g.b.left, η[D.toPre.P.A].left] ![-1, 1]), ν.IsGen ∧ ∀ (e : ℕ) (h : (thickObj R (maximalIdeal R) e G).left ⟶ (thickObj R (maximalIdeal R) e G).left), h ≫ (thickObj R (maximalIdeal R) e G).hom = (thickObj R (maximalIdeal R) e G).hom → h ≫ (fstG (maximalIdeal R) e G).left = (fstG (maximalIdeal R) e G).left ≫ ((toUnit G ≫ a) * 𝟙 G).left → ∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R (maximalIdeal R) e G).left) (z : Z) (J : (Z ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι) (J' : (Z ⟶ D₂.toPre.P.A.left) → D₂.toPre.P.L.ι) (N : (Z ⟶ G.left) → U.LG.L.ι) (N' : (Z ⟶ G.left) → U₂.LG.L.ι), Geo.Tor.Good D.toPre.P.L z J → Geo.Tor.Good D₂.toPre.P.L z J' → Geo.Tor.Good U.LG.L z N → Geo.Tor.Good U₂.LG.L z N' → Geo.Tor.gv w (r ≫ (U₂.gt e).pG.left) z (fun i => J ((r ≫ (U₂.gt e).pG.left) ≫ GlobalTheory.MumCmp.twφ D₂.toPre D.toPre β.hom g.b i)) (J' (r ≫ (U₂.gt e).pG.left)) * Geo.Tor.gw (U₂.w e) r z (J' (r ≫ (U₂.gt e).pG.left)) (fun _ => N' (r ≫ (fstG (maximalIdeal R) e G).left)) = Geo.Tor.gw (U.w e) (r ≫ h) z (J (r ≫ h ≫ (U.gt e).pG.left)) (fun _ => N (r ≫ h ≫ (fstG (maximalIdeal R) e G).left)) * Geo.Tor.gw wL (r ≫ (fstG (maximalIdeal R) e G).left) z (N (r ≫ (fstG (maximalIdeal R) e G).left ≫ ((toUnit G ≫ a) * 𝟙 G).left)) (N' (r ≫ (fstG (maximalIdeal R) e G).left)) * Geo.Tor.val ν (r ≫ (thickObj R (maximalIdeal R) e G).hom ≫ thick R (maximalIdeal R) e) z J := by
  intro R _ _ _ hR D A G _ _ hG U g hg a ha hab A₂ D₂ U₂ wL hwL β hβm hβ w hw
  have hab' : ∀ (e : ℕ) (ae : Spec (CommRingCat.of (R ⧸ maximalIdeal R ^ (e + 1))) ⟶ (thickObj R (maximalIdeal R) e G).left), ae ≫ (thickObj R (maximalIdeal R) e G).hom = 𝟙 _ → ae ≫ (fstG (maximalIdeal R) e G).left = thick R (maximalIdeal R) e ≫ a.left → ae ≫ (U.gt e).pG.left = thick R (maximalIdeal R) e ≫ g.b.left :=
    fun e ae h1 h2 => (hab e ae h1 h2).1
  obtain ⟨W, hW, HW⟩ := GlobalTheory.T.exists_global_iso_translated_bundle_levelComparison hR hG U a ha g.b hab' U₂ wL hwL β hβ
  obtain ⟨ν, hν, Hν⟩ := GlobalTheory.T.exists_generator_ratio_translationTwist_isos D₂.toPre D.toPre β.hom g.b w hw W hW
  refine ⟨ν, hν, ?_⟩
  intro e h hh hh' Z r z J J' N N' hJ hJ' hN hN'
  have k0 := lift_comp_pG U a g.b hab' U₂ β hβ e h hh'
  have hm : r ≫ h ≫ (U.gt e).pG.left = (r ≫ (U₂.gt e).pG.left) ≫ GlobalTheory.MumCmp.twφ D₂.toPre D.toPre β.hom g.b 0 := by
    rw [k0, Category.assoc]
  have hf : r ≫ h ≫ (fstG (maximalIdeal R) e G).left = r ≫ (fstG (maximalIdeal R) e G).left ≫ ((toUnit G ≫ a) * 𝟙 G).left := by
    rw [hh']
  have hs : (r ≫ (U₂.gt e).pG.left) ≫ D₂.toPre.P.A.hom = r ≫ (thickObj R (maximalIdeal R) e G).hom ≫ thick R (maximalIdeal R) e := by
    rw [Category.assoc, Over.w]; rfl
  have k2 := Hν Z (r ≫ (U₂.gt e).pG.left) z J (J' (r ≫ (U₂.gt e).pG.left)) hJ (hJ' _)
  have m1 : (U.gt e).pG.left (h (r z)) ∈ D.toPre.P.L.U (J ((r ≫ (U₂.gt e).pG.left) ≫ GlobalTheory.MumCmp.twφ D₂.toPre D.toPre β.hom g.b 0)) := by
    have m1' : (U.gt e).pG.left (h (r z)) ∈ D.toPre.P.L.U (J (r ≫ h ≫ (U.gt e).pG.left)) := by
      simpa using hJ (r ≫ h ≫ (U.gt e).pG.left)
    rw [hm] at m1'
    exact m1'
  have m2 : (U₂.gt e).pG.left (r z) ∈ D₂.toPre.P.L.U (J' (r ≫ (U₂.gt e).pG.left)) := by
    simpa using hJ' (r ≫ (U₂.gt e).pG.left)
  have m3 : ((toUnit G ≫ a) * 𝟙 G).left ((fstG (maximalIdeal R) e G).left (r z)) ∈ U.LG.L.U (N (r ≫ (fstG (maximalIdeal R) e G).left ≫ ((toUnit G ≫ a) * 𝟙 G).left)) := by
    simpa using hN (r ≫ (fstG (maximalIdeal R) e G).left ≫ ((toUnit G ≫ a) * 𝟙 G).left)
  have m4 : (fstG (maximalIdeal R) e G).left (r z) ∈ U₂.LG.L.U (N' (r ≫ (fstG (maximalIdeal R) e G).left)) := by
    simpa using hN' (r ≫ (fstG (maximalIdeal R) e G).left)
  have k1 := HW e h hh hh' Z r z _ _ _ _ m1 m2 m3 m4
  rw [k2, hs, mul_right_comm, k1, hm, hf]

end GlobalTheory.MumCmp.LevelCmp
end
