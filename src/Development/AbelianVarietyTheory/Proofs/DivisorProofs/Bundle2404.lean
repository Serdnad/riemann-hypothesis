module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2368
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2369
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CotangentImagesLinearIndependent
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TensorProduct.IsBaseChangeFree
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
import Mathlib.Tactic.Polynomial.Basic
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings

@[expose] public section

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

set_option autoImplicit false

namespace GlobalTheory.LogKSDiv.LocSpan

theorem deriv_ext {k R A : Type} [CommRing k] [CommRing R] [CommRing A] [Algebra k A] (φ : R →+* A)
    (M : Submonoid R) (hloc : letI := φ.toAlgebra; IsLocalization M A) (D₁ D₂ : Derivation k A A)
    (h : ∀ r, D₁ (φ r) = D₂ (φ r)) : D₁ = D₂ := by
  letI := φ.toAlgebra
  ext y
  obtain ⟨⟨r, t⟩, e⟩ := IsLocalization.surj M y
  have hu : IsUnit (φ t) := IsLocalization.map_units A t
  have e' : y * φ t = φ r := e
  have h1 := congrArg D₁ e'
  have h2 := congrArg D₂ e'
  rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul] at h1 h2
  rw [h r, h t] at h1
  have : φ t * D₁ y = φ t * D₂ y := by linear_combination h1 - h2
  exact hu.mul_left_cancel this

end GlobalTheory.LogKSDiv.LocSpan

namespace GlobalTheory.LogKSDiv.LocSpan

theorem sum_apply {k R M : Type} [CommRing k] [CommRing R] [AddCommGroup M] [Algebra k R] [Module R M] [Module k M]
    {n : ℕ} (f : Fin n → Derivation k R M) (x : R) : (∑ j, f j) x = ∑ j, f j x := by

  rw [← Derivation.coeFnAddMonoidHom_apply, map_sum, Finset.sum_apply]
  rfl

theorem span_eq_top {k R A : Type} [Field k] [CommRing R] [CommRing A] [Algebra k R] [Algebra k A]
    [Algebra.FiniteType k R] (φ : R →+* A) (hk : φ.comp (algebraMap k R) = algebraMap k A)
    (M : Submonoid R) (hloc : letI := φ.toAlgebra; IsLocalization M A) (a : R) (ha : IsUnit (φ a)) {n : ℕ}
    (v : Fin n → Derivation ℤ R R)
    (hlog : ∀ D : Derivation k R R, a • D.restrictScalars ℤ ∈ Submodule.span R (Set.range v))
    (δ : Fin n → Derivation k A A) (hδ : ∀ j r, δ j (φ r) = φ (v j r)) :
    Submodule.span A (Set.range δ) = ⊤ := by
  letI := φ.toAlgebra
  haveI : IsScalarTower k R A := IsScalarTower.of_algebraMap_eq fun c => (congrArg (· c) hk).symm
  haveI : Algebra.FinitePresentation k R := Algebra.FinitePresentation.of_finiteType.mp inferInstance
  rw [Submodule.eq_top_iff']
  intro d
  let g : Derivation k R A := d.compAlgebraMap R
  obtain ⟨h, s, hs⟩ :=
    Module.FinitePresentation.exists_lift_of_isLocalizedModule M (Algebra.linearMap R A) g.liftKaehlerDifferential
  let D' : Derivation k R R := h.compDer (KaehlerDifferential.D k R)
  have hD' : ∀ r, φ (D' r) = φ s * d (φ r) := by
    intro r
    have := congrArg (fun L : Ω[R⁄k] →ₗ[R] A => L (KaehlerDifferential.D k R r)) hs
    simp only [LinearMap.coe_comp, Function.comp_apply, Algebra.linearMap_apply, LinearMap.smul_apply,
      Derivation.liftKaehlerDifferential_comp_D] at this
    rw [Submonoid.smul_def, Algebra.smul_def] at this
    exact this
  obtain ⟨cf, hcf⟩ := (Submodule.mem_span_range_iff_exists_fun R).1 (hlog D')
  have hsu : IsUnit (φ s) := IsLocalization.map_units A s
  have hu : IsUnit (φ a * φ s) := ha.mul hsu
  have key : (φ a * φ s) • d = ∑ j, φ (cf j) • δ j := by
    refine deriv_ext φ M hloc _ _ fun r => ?_
    have e1 := congrArg (fun D : Derivation ℤ R R => φ (D r)) hcf

    simp only [sum_apply, Derivation.coe_smul, Pi.smul_apply, smul_eq_mul, map_sum,
    map_mul, Derivation.coe_restrictScalars] at e1
    simp only [sum_apply, Derivation.coe_smul, Pi.smul_apply, smul_eq_mul, hδ]
    rw [e1, hD']
    ring
  have hmem : (φ a * φ s) • d ∈ Submodule.span A (Set.range δ) := by
    rw [key]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  have hmem' : ((hu.unit : Aˣ) : A) • d ∈ Submodule.span A (Set.range δ) := by
    rw [hu.unit_spec]
    exact hmem
  have := Submodule.smul_mem _ ((hu.unit⁻¹ : Aˣ) : A) hmem'
  rwa [smul_smul, Units.inv_mul, one_smul] at this

end GlobalTheory.LogKSDiv.LocSpan

namespace GlobalTheory.LogKSDiv.LocSpan

theorem appLE_germ {X S : Scheme.{0}} (f : X ⟶ S) (W : S.Opens) (V T : X.Opens) (hV : V ≤ f ⁻¹ᵁ W)
    (hT : T ≤ f ⁻¹ᵁ W) (x : X) (hxV : x ∈ V) (hxT : x ∈ T) :
    f.appLE W V hV ≫ X.presheaf.germ V x hxV = f.appLE W T hT ≫ X.presheaf.germ T x hxT := by
  rw [← X.presheaf.germ_res (homOfLE (inf_le_left : V ⊓ T ≤ V)) x ⟨hxV, hxT⟩,
    ← X.presheaf.germ_res (homOfLE (inf_le_right : V ⊓ T ≤ T)) x ⟨hxV, hxT⟩,
    Scheme.Hom.appLE_map_assoc, Scheme.Hom.appLE_map_assoc]

theorem appLE_appLE_germ {X Y S : Scheme.{0}} (ι : X ⟶ Y) (s : Y ⟶ S) (W : S.Opens) (U : Y.Opens) (V T : X.Opens)
    (h1 : U ≤ s ⁻¹ᵁ W) (hV : V ≤ ι ⁻¹ᵁ U) (h2 : T ≤ (ι ≫ s) ⁻¹ᵁ W) (x : X) (hxV : x ∈ V) (hxT : x ∈ T) :
    s.appLE W U h1 ≫ ι.appLE U V hV ≫ X.presheaf.germ V x hxV = (ι ≫ s).appLE W T h2 ≫ X.presheaf.germ T x hxT := by
  rw [Scheme.Hom.appLE_comp_appLE_assoc]
  exact appLE_germ _ _ _ _ _ _ _ _ _

end GlobalTheory.LogKSDiv.LocSpan

namespace GlobalTheory.LogKSDiv.LocSpan

open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

theorem stalkHom_comp_algX (TF : TorFlag Xo c) (Z : Comp Xo c) (x : X₀ TF.Y Z) (U : TF.Y.X.affineOpens)
    (hx : (barComp TF.Y Z).ι x ∈ U.1) :
    (stalkHom TF Z x U hx).comp (algX TF.Y.s U.1) = stalkAlg TF Z x := by
  ext a
  simp only [stalkHom, stalkAlg, algX, RingHom.comp_apply]
  have key : TF.Y.s.appLE ⊤ U.1 (by simp) ≫ (barComp TF.Y Z).ι.app U.1 ≫
      (X₀ TF.Y Z).presheaf.germ ((barComp TF.Y Z).ι ⁻¹ᵁ U.1) x hx =
      (s₀ TF.Y Z).appLE ⊤ ⊤ (by simp) ≫ (X₀ TF.Y Z).presheaf.germ ⊤ x trivial := by
    rw [Scheme.Hom.app_eq_appLE]
    exact appLE_appLE_germ _ _ _ _ _ _ _ _ _ _ _ _
  exact congrArg (fun f => f.hom ((Scheme.ΓSpecIso (CommRingCat.of c.F)).inv.hom a)) key

end GlobalTheory.LogKSDiv.LocSpan

namespace GlobalTheory.LogKSDiv.LocSpan

open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

theorem finiteType_algX (TF : TorFlag Xo c) (U : TF.Y.X.affineOpens) : (algX TF.Y.s U.1).FiniteType := by
  haveI := TF.smooth
  haveI : Smooth TF.Y.s := SmoothOfRelativeDimension.smooth Dw.dim _
  have h1 : (TF.Y.s.appLE ⊤ U.1 (by simp)).hom.FiniteType :=
    HasRingHomProperty.appLE @LocallyOfFiniteType TF.Y.s inferInstance ⟨⊤, isAffineOpen_top _⟩ U _
  exact h1.comp (RingHom.FiniteType.of_surjective _
    (Scheme.ΓSpecIso (CommRingCat.of c.F)).symm.commRingCatIsoToRingEquiv.surjective)

theorem isLocalization_stalkHom (TF : TorFlag Xo c) (Z : Comp Xo c) (x : X₀ TF.Y Z) (U : TF.Y.X.affineOpens)
    (hx : (barComp TF.Y Z).ι x ∈ U.1) :
    letI := (stalkHom TF Z x U hx).toAlgebra
    IsLocalization.AtPrime ((X₀ TF.Y Z).presheaf.stalk x) (U.2.primeIdealOf ⟨_, hx⟩).asIdeal := by
  letI := TopCat.Presheaf.algebra_section_stalk TF.Y.X.presheaf (⟨_, hx⟩ : U.1)
  have h1 := U.2.isLocalization_stalk ⟨_, hx⟩
  let e := (asIso ((barComp TF.Y Z).ι.stalkMap x)).commRingCatIsoToRingEquiv
  have h2 := (IsLocalization.isLocalization_iff_of_ringEquiv _ e).1 h1
  have heq : stalkHom TF Z x U hx = e.toRingHom.comp (TF.Y.X.presheaf.germ U.1 _ hx).hom :=
    RingHom.ext fun y => (Scheme.Hom.germ_stalkMap_apply _ _ _ hx y).symm
  rw [heq]
  convert h2

theorem exists_unit (TF : TorFlag Xo c) (Z : Comp Xo c) (x : X₀ TF.Y Z) (U : TF.Y.X.affineOpens)
    (hx : (barComp TF.Y Z).ι x ∈ U.1) (hint : x ∈ (j₀ TF.Y Z).opensRange) :
    ∃ a ∈ (Scheme.IdealSheafData.vanishingIdeal (LogKS.interior TF.Y).compl).ideal U,
      IsUnit (stalkHom TF Z x U hx a) := by
  have hin : (barComp TF.Y Z).ι x ∈ LogKS.interior TF.Y := by
    obtain ⟨y, rfl⟩ := hint
    refine ⟨i₀ TF.Y Z y, ?_⟩
    rw [← Scheme.Hom.comp_apply, ← j₀_ι, Scheme.Hom.comp_apply]
  obtain ⟨a, hle, hxa⟩ := U.2.exists_basicOpen_le (V := U.1 ⊓ LogKS.interior TF.Y) ⟨_, hx, hin⟩ hx
  refine ⟨a, ?_, ?_⟩
  · rw [Scheme.IdealSheafData.vanishingIdeal_ideal, PrimeSpectrum.mem_vanishingIdeal]
    intro p hp
    by_contra hpa
    have h3 : p ∈ PrimeSpectrum.basicOpen a := hpa
    rw [← U.2.fromSpec_preimage_basicOpen] at h3
    exact hp (hle h3).2
  · have h4 : x ∈ (barComp TF.Y Z).ι ⁻¹ᵁ TF.Y.X.basicOpen a := hxa
    rw [Scheme.preimage_basicOpen] at h4
    exact ((X₀ TF.Y Z).mem_basicOpen _ x hx).1 h4

end GlobalTheory.LogKSDiv.LocSpan

theorem GlobalTheory.LogKSDiv.span_logDer_germs : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), ∀ [IsIntegral (X₀ TF.Y Z)] [SmoothOfRelativeDimension Dw.dim (s₀ TF.Y Z)] (x : X₀ TF.Y Z) (U : TF.Y.X.affineOpens), U.1 ≤ barComp TF.Y Z → ∀ (hx : (barComp TF.Y Z).ι x ∈ U.1) (b : Module.Basis (Fin Dw.dim) Γ(TF.Y.X, U.1) (LogKS.logDer TF.Y.s (Scheme.IdealSheafData.vanishingIdeal (LogKS.interior TF.Y).compl) U)), letI := (GlobalTheory.LogKSDiv.stalkAlg TF Z x).toAlgebra; ∀ δ : Fin Dw.dim → Derivation c.F ((X₀ TF.Y Z).presheaf.stalk x) ((X₀ TF.Y Z).presheaf.stalk x), (∀ j r, δ j (GlobalTheory.LogKSDiv.stalkHom TF Z x U hx r) = GlobalTheory.LogKSDiv.stalkHom TF Z x U hx ((b j).1 r)) → x ∈ (j₀ TF.Y Z).opensRange → Submodule.span ((X₀ TF.Y Z).presheaf.stalk x) (Set.range δ) = ⊤ := by
  intro E _ _ _ H Dw l Xo c TF Z _ _ x U _ hx b
  intro δ hδ hint
  letI := (GlobalTheory.LogKSDiv.stalkAlg TF Z x).toAlgebra
  letI : Algebra c.F Γ(TF.Y.X, U.1) := (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX TF.Y.s U.1).toAlgebra
  haveI : Algebra.FiniteType c.F Γ(TF.Y.X, U.1) := LocSpan.finiteType_algX TF U
  obtain ⟨a, haI, hau⟩ := LocSpan.exists_unit TF Z x U hx hint
  refine LocSpan.span_eq_top (stalkHom TF Z x U hx) (LocSpan.stalkHom_comp_algX TF Z x U hx) _
    (LocSpan.isLocalization_stalkHom TF Z x U hx) a hau (fun j => (b j).1) ?_ δ hδ
  intro D
  have hmem : a • D.restrictScalars ℤ ∈
      LogKS.logDer TF.Y.s (Scheme.IdealSheafData.vanishingIdeal (LogKS.interior TF.Y).compl) U := by
    refine ⟨fun a' => ?_, fun f _ => ?_⟩
    · show a * D (constFn TF.Y.s U.1 a') = 0
      rw [show constFn TF.Y.s U.1 a' = algebraMap c.F _ a' from rfl, D.map_algebraMap, mul_zero]
    · show a * D f ∈ _
      exact Ideal.mul_mem_right _ _ haI
  have h7 := congrArg Subtype.val (b.sum_repr ⟨_, hmem⟩)
  rw [Submodule.coe_sum] at h7
  simp only [Submodule.coe_smul] at h7
  rw [← h7]
  exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

set_option autoImplicit false

namespace GlobalTheory.LogKSDiv.LocalExt

theorem exists_restrict_der {k A K R : Type} [CommRing k] [CommRing A] [CommRing K] [CommRing R]
    [Algebra k A] [Algebra k K] (φ : A →+* K) (hφ : Function.Injective φ)
    (hk : ∀ c : k, φ (algebraMap k A c) = algebraMap k K c)
    (h : R →+* A) (hfr : ∀ a : A, ∃ r s : R, IsUnit (h s) ∧ a * h s = h r)
    (d : Derivation ℤ R R) (D : Derivation k K K)
    (hD : ∀ r, D (φ (h r)) = φ (h (d r))) :
    ∃ δ : Derivation k A A, (∀ a, D (φ a) = φ (δ a)) ∧ ∀ r, δ (h r) = h (d r) := by
  have hmem : ∀ a, ∃ b, φ b = D (φ a) := by
    intro a
    obtain ⟨r, s, ⟨u, hu⟩, hrs⟩ := hfr a
    refine ⟨(h (d r) - a * h (d s)) * ((u⁻¹ : Aˣ) : A), ?_⟩
    have e1 : D (φ a * φ (h s)) = φ (h (d r)) := by rw [← map_mul, hrs, hD]
    rw [Derivation.leibniz, hD, smul_eq_mul, smul_eq_mul] at e1
    have hinv : φ (h s) * φ ((u⁻¹ : Aˣ) : A) = 1 := by rw [← map_mul, ← hu, Units.mul_inv, map_one]
    rw [map_mul, map_sub, map_mul, ← e1]
    linear_combination (D (φ a)) * hinv
  choose δ0 hδ0 using hmem
  let δ : Derivation k A A :=
    { toFun := δ0
      map_add' := fun a b => hφ (by simp only [hδ0, map_add (f := _)])
      map_smul' := fun c a => hφ (by
        simp only [RingHom.id_apply, Algebra.smul_def, map_mul, hk, hδ0]
        rw [← Algebra.smul_def, D.map_smul, Algebra.smul_def])
      map_one_eq_zero' := hφ (by show φ (δ0 1) = φ 0; rw [hδ0, map_one, Derivation.map_one_eq_zero, map_zero])
      leibniz' := fun a b => hφ (by
        show φ (δ0 (a * b)) = φ (a • δ0 b + b • δ0 a)
        simp only [hδ0, map_mul, map_add (f := _), smul_eq_mul, Derivation.leibniz]) }
  refine ⟨δ, fun a => (hδ0 a).symm, fun r => hφ ?_⟩
  show φ (δ0 (h r)) = _
  rw [hδ0, hD]

end GlobalTheory.LogKSDiv.LocalExt

namespace GlobalTheory.LogKSDiv.LocalExt

theorem exists_frac_germ {X : Scheme.{0}} (B : X.Opens) (y : B.toScheme) (U : X.affineOpens) (hy : B.ι y ∈ U.1)
    (a : B.toScheme.presheaf.stalk y) :
    ∃ r s : Γ(X, U.1), IsUnit ((B.ι.stalkMap y).hom (X.presheaf.germ U.1 (B.ι y) hy s)) ∧
      a * (B.ι.stalkMap y).hom (X.presheaf.germ U.1 (B.ι y) hy s) =
        (B.ι.stalkMap y).hom (X.presheaf.germ U.1 (B.ι y) hy r) := by
  letI := X.presheaf.algebra_section_stalk (⟨B.ι y, hy⟩ : U.1)
  haveI := U.2.isLocalization_stalk ⟨B.ι y, hy⟩
  let e := asIso (B.ι.stalkMap y)
  obtain ⟨⟨r, s⟩, hrs⟩ := IsLocalization.surj (U.2.primeIdealOf ⟨B.ι y, hy⟩).asIdeal.primeCompl (e.inv.hom a)
  refine ⟨r, s, (IsLocalization.map_units (X.presheaf.stalk (B.ι y)) s).map (B.ι.stalkMap y).hom, ?_⟩
  have h2 := congrArg (B.ι.stalkMap y).hom hrs
  rw [map_mul] at h2
  have h3 : (B.ι.stalkMap y).hom (e.inv.hom a) = a := by
    change (e.inv ≫ e.hom).hom a = a
    rw [Iso.inv_hom_id]
    rfl
  rw [h3] at h2
  exact h2

end GlobalTheory.LogKSDiv.LocalExt

namespace GlobalTheory.LogKSDiv

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

theorem stalkHom_eq_stalkMap (TF : TorFlag Xo c) (Z : Comp Xo c) (x : X₀ TF.Y Z) (U : TF.Y.X.affineOpens)
    (hx : (barComp TF.Y Z).ι x ∈ U.1) (r : Γ(TF.Y.X, U.1)) :
    stalkHom TF Z x U hx r = ((barComp TF.Y Z).ι.stalkMap x).hom (TF.Y.X.presheaf.germ U.1 _ hx r) :=
  (Scheme.Hom.germ_stalkMap_apply _ _ _ _ _).symm

theorem stalkHom_frac (TF : TorFlag Xo c) (Z : Comp Xo c) (x : X₀ TF.Y Z) (U : TF.Y.X.affineOpens)
    (hx : (barComp TF.Y Z).ι x ∈ U.1) (a : (X₀ TF.Y Z).presheaf.stalk x) :
    ∃ r s : Γ(TF.Y.X, U.1), IsUnit (stalkHom TF Z x U hx s) ∧ a * stalkHom TF Z x U hx s = stalkHom TF Z x U hx r := by
  obtain ⟨r, s, hu, e⟩ := LocalExt.exists_frac_germ (barComp TF.Y Z) x U hx a
  exact ⟨r, s, by rw [stalkHom_eq_stalkMap]; exact hu, by rw [stalkHom_eq_stalkMap, stalkHom_eq_stalkMap]; exact e⟩

end GlobalTheory.LogKSDiv

theorem GlobalTheory.LogKSDiv.exists_stalkDer_extend : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), ∀ [IsIntegral (X₀ TF.Y Z)] [SmoothOfRelativeDimension Dw.dim (s₀ TF.Y Z)] (x : X₀ TF.Y Z) (U : TF.Y.X.affineOpens), U.1 ≤ barComp TF.Y Z → ∀ (hx : (barComp TF.Y Z).ι x ∈ U.1) (ρ : Γ(TF.Y.X, U.1) →+* (X₀ TF.Y Z).functionField), (∀ r, ρ r = algebraMap ((X₀ TF.Y Z).presheaf.stalk x) (X₀ TF.Y Z).functionField (GlobalTheory.LogKSDiv.stalkHom TF Z x U hx r)) → ∀ (d : Fin Dw.dim → Derivation ℤ Γ(TF.Y.X, U.1) Γ(TF.Y.X, U.1)) (D : Fin Dw.dim → GlobalTheory.LogKSDiv.GenDer TF Z), (letI := (GlobalTheory.Cartier.constFn (s₀ TF.Y Z)).toAlgebra; ∀ j r, (show Derivation c.F (X₀ TF.Y Z).functionField (X₀ TF.Y Z).functionField from D j) (ρ r) = ρ (d j r)) → letI := (GlobalTheory.LogKSDiv.stalkAlg TF Z x).toAlgebra; ∃ δ : Fin Dw.dim → Derivation c.F ((X₀ TF.Y Z).presheaf.stalk x) ((X₀ TF.Y Z).presheaf.stalk x), (letI := (GlobalTheory.Cartier.constFn (s₀ TF.Y Z)).toAlgebra; ∀ j a, (show Derivation c.F (X₀ TF.Y Z).functionField (X₀ TF.Y Z).functionField from D j) (algebraMap ((X₀ TF.Y Z).presheaf.stalk x) (X₀ TF.Y Z).functionField a) = algebraMap ((X₀ TF.Y Z).presheaf.stalk x) (X₀ TF.Y Z).functionField (δ j a)) ∧ ∀ j r, δ j (GlobalTheory.LogKSDiv.stalkHom TF Z x U hx r) = GlobalTheory.LogKSDiv.stalkHom TF Z x U hx (d j r) := by
  intro E _ _ _ H Dw l Xo c TF Z _ _ x U _ hx ρ hρ d D hD
  letI := (GlobalTheory.Cartier.constFn (s₀ TF.Y Z)).toAlgebra
  letI := (GlobalTheory.LogKSDiv.stalkAlg TF Z x).toAlgebra
  have key := fun j => GlobalTheory.LogKSDiv.LocalExt.exists_restrict_der (k := c.F)
    (algebraMap ((X₀ TF.Y Z).presheaf.stalk x) (X₀ TF.Y Z).functionField)
    (IsFractionRing.injective _ _)
    (fun c => RingHom.congr_fun (GlobalTheory.LogKSDiv.algebraMap_comp_stalkAlg TF Z x) c)
    (GlobalTheory.LogKSDiv.stalkHom TF Z x U hx) (GlobalTheory.LogKSDiv.stalkHom_frac TF Z x U hx) (d j) (D j)
    (fun r => by rw [← hρ, ← hρ]; exact hD j r)
  choose δ h1 h2 using key
  exact ⟨δ, h1, h2⟩
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LogKSDiv

open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.TopForm

theorem frame_eq_unit_smul_dForm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), ∀ [IsIntegral (X₀ TF.Y Z)] [SmoothOfRelativeDimension Dw.dim (s₀ TF.Y Z)] (x : X₀ TF.Y Z) (U' : (X₀ TF.Y Z).Opens) (ω : TopForm.FormsOn (s₀ TF.Y Z) Dw.dim U'), TopForm.IsFrame ω → ∀ hx : x ∈ U', letI := (GlobalTheory.LogKSDiv.stalkAlg TF Z x).toAlgebra; ∃ (g : Fin Dw.dim → (X₀ TF.Y Z).presheaf.stalk x) (bΩ : Module.Basis (Fin Dw.dim) ((X₀ TF.Y Z).presheaf.stalk x) Ω[(X₀ TF.Y Z).presheaf.stalk x⁄c.F]) (u : (X₀ TF.Y Z).presheaf.stalk x), (∀ i, bΩ i = KaehlerDifferential.D c.F ((X₀ TF.Y Z).presheaf.stalk x) (g i)) ∧ IsUnit u ∧ formOf U' (gen_mem hx) ω = algebraMap ((X₀ TF.Y Z).presheaf.stalk x) (X₀ TF.Y Z).functionField u • TopForm.dForm (GlobalTheory.Cartier.constFn (s₀ TF.Y Z)) (fun i => algebraMap ((X₀ TF.Y Z).presheaf.stalk x) (X₀ TF.Y Z).functionField (g i)) := by
  intro E _ _ _ H Dw l Xo c TF Z _ _ x U' ω hω hx
  letI := (GlobalTheory.LogKSDiv.stalkAlg TF Z x).toAlgebra
  obtain ⟨U, y, b, hUU', hxU, hU, hb⟩ :=
    GlobalTheory.AdaptedFrame.exists_basis_dFun (s₀ TF.Y Z) Dw.dim hx
  have hy : IsFreeGen Γ(X₀ TF.Y Z, U) (dOn (s₀ TF.Y Z) y) := isFreeGen_dForm y b hb
  have hres : IsFrame (resForm hUU' ω) := hω.res hU hUU'
  obtain ⟨a, ha⟩ := hy.2 (resForm hUU' ω)
  have hau : IsUnit a := by
    have := hres.gen
    rw [← ha] at this
    exact hy.smul_iff.1 this
  have hgU : genericPoint (X₀ TF.Y Z) ∈ U := gen_mem hxU
  have hform : formOf U' (gen_mem hx) ω =
      fnOf U hgU a • dForm (constFn (s₀ TF.Y Z)) (fun i => fnOf U hgU (y i)) := by
    rw [← formOf_resForm hUU' hgU ω, ← ha, map_smulₛₗ]
    congr 1
    exact formMap_dForm _ _ _
  letI iΓ : Algebra c.F Γ(X₀ TF.Y Z, U) := (algX (s₀ TF.Y Z) U).toAlgebra
  letI iΓA : Algebra Γ(X₀ TF.Y Z, U) ((X₀ TF.Y Z).presheaf.stalk x) :=
    ((X₀ TF.Y Z).presheaf.germ U x hxU).hom.toAlgebra
  have hsc : algebraMap c.F ((X₀ TF.Y Z).presheaf.stalk x) =
      (algebraMap Γ(X₀ TF.Y Z, U) ((X₀ TF.Y Z).presheaf.stalk x)).comp
        (algebraMap c.F Γ(X₀ TF.Y Z, U)) := by
    ext t
    change ((X₀ TF.Y Z).presheaf.germ ⊤ x trivial).hom (algX (s₀ TF.Y Z) ⊤ t) =
      ((X₀ TF.Y Z).presheaf.germ U x hxU).hom (algX (s₀ TF.Y Z) U t)
    rw [← resG_comp_algX (s₀ TF.Y Z) (le_top : U ≤ ⊤), RingHom.comp_apply, germ_resG]
  haveI : IsScalarTower c.F Γ(X₀ TF.Y Z, U) ((X₀ TF.Y Z).presheaf.stalk x) :=
    IsScalarTower.of_algebraMap_eq' hsc
  haveI : IsLocalization.AtPrime ((X₀ TF.Y Z).presheaf.stalk x) (hU.primeIdealOf ⟨x, hxU⟩).asIdeal :=
    hU.isLocalization_stalk ⟨x, hxU⟩
  haveI : Algebra.FormallyEtale Γ(X₀ TF.Y Z, U) ((X₀ TF.Y Z).presheaf.stalk x) :=
    .of_isLocalization (hU.primeIdealOf ⟨x, hxU⟩).asIdeal.primeCompl
  have hbc := KaehlerDifferential.isBaseChange_of_formallyEtale c.F Γ(X₀ TF.Y Z, U)
    ((X₀ TF.Y Z).presheaf.stalk x)
  refine ⟨fun i => ((X₀ TF.Y Z).presheaf.germ U x hxU).hom (y i), hbc.basis b,
    ((X₀ TF.Y Z).presheaf.germ U x hxU).hom a, fun i => ?_, hau.map _, ?_⟩
  · rw [IsBaseChange.basis_apply, hb]
    exact KaehlerDifferential.map_D c.F c.F _ _ (y i)
  · rw [hform]
    simp only [algebraMap_germ]
end GlobalTheory.LogKSDiv
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

set_option autoImplicit false

namespace GlobalTheory.LogKSDiv

theorem blockRow_eq_sum {ι R : Type} [CommRing R] {m : ι → ℕ} {n n' : ℕ} (e : (Σ τ : ι, Fin (m τ)) ≃ Fin n)
    (e' : (Σ τ : ι, Fin (m τ)) ≃ Fin n') (B : Matrix (Fin n) (Fin n') R)
    (hB : ∀ (τ σ : ι) (i : Fin (m τ)) (k : Fin (m σ)), τ ≠ σ → B (e ⟨τ, i⟩) (e' ⟨σ, k⟩) = 0)
    (τ : ι) (i : Fin (m τ)) (c : Fin n') :
    B (e ⟨τ, i⟩) c = ∑ j : Fin (m τ), B (e ⟨τ, i⟩) (e' ⟨τ, j⟩) * (if c = e' ⟨τ, j⟩ then 1 else 0) := by
  obtain ⟨⟨σ, k⟩, rfl⟩ := e'.surjective c
  by_cases h : τ = σ
  · subst h
    rw [Finset.sum_eq_single k]
    · simp
    · intro j _ hj
      rw [if_neg, mul_zero]
      intro h
      exact hj (eq_of_heq (Sigma.mk.inj (e'.injective h)).2).symm
    · simp
  · rw [hB _ _ _ _ h]
    symm
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [if_neg, mul_zero]
    intro h'
    exact h (Sigma.mk.inj (e'.injective h')).1.symm

theorem transpose_mul_symm_mul_apply {R : Type} [CommRing R] {n n' : ℕ} (B : Matrix (Fin n) (Fin n') R) (a b : Fin n)
    (c d : Fin n') :
    (_root_.Matrix.transpose B * (Matrix.of fun x y : Fin n =>
      ((if x = a ∧ y = b then 1 else 0) + (if x = b ∧ y = a then 1 else 0) : R)) * B) c d =
      B a c * B b d + B b c * B a d := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply, mul_add, Finset.sum_add_distrib, add_mul,
    ite_and, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true, ite_mul, zero_mul]

theorem transpose_mul_symPair_mul_mem_span :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (R : Type) [CommRing R] (n n' : ℕ) (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n) (e' : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n') (ε' : Fin Dw.dim ≃ GlobalTheory.LogKSDiv.PairIx H Dw) (B : Matrix (Fin n) (Fin n') R), (∀ (τ σ : E →+* ℂ) (i : Fin (Dw.mult τ)) (k : Fin (Dw.mult σ)), τ ≠ σ → B (e ⟨τ, i⟩) (e' ⟨σ, k⟩) = 0) → ∀ P : GlobalTheory.LogKSDiv.PairIx H Dw, ∃ cf : Fin Dw.dim → R, _root_.Matrix.transpose B * GlobalTheory.LogKSDiv.symPair (R := R) e P * B = ∑ k, cf k • GlobalTheory.LogKSDiv.symPair (R := R) e' (ε' k) := by
  intro E _ _ _ H Dw R _ n n' e e' ε' B hB P
  have key : _root_.Matrix.transpose B * symPair (R := R) e P * B =
      ∑ j : Fin (Dw.mult P.1.1), ∑ k : Fin (Dw.mult ((starRingEnd ℂ).comp P.1.1)),
        (B (e ⟨P.1.1, P.2.1⟩) (e' ⟨P.1.1, j⟩) *
          B (e ⟨(starRingEnd ℂ).comp P.1.1, P.2.2⟩) (e' ⟨(starRingEnd ℂ).comp P.1.1, k⟩)) •
          symPair (R := R) e' (⟨P.1, (j, k)⟩ : PairIx H Dw) := by
    ext c d
    unfold symPair
    rw [transpose_mul_symm_mul_apply, blockRow_eq_sum e e' B hB _ _ c, blockRow_eq_sum e e' B hB _ P.2.2 d,
      blockRow_eq_sum e e' B hB _ P.2.2 c, blockRow_eq_sum e e' B hB _ P.2.1 d, mul_comm (Finset.sum _ _) (∑ j : Fin (Dw.mult P.1.1), _ * (if d = _ then _ else _)),
      Finset.sum_mul_sum, Finset.sum_mul_sum, ← Finset.sum_add_distrib]
    simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
    simp only [ite_and]
    split_ifs <;> ring
  have hmem : _root_.Matrix.transpose B * symPair (R := R) e P * B ∈
      Submodule.span R (Set.range fun k => symPair (R := R) e' (ε' k)) := by
    rw [key]
    refine Submodule.sum_mem _ fun j _ => Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ ?_
    exact Submodule.subset_span ⟨ε'.symm ⟨P.1, (j, k)⟩, by simp⟩
  obtain ⟨cf, hcf⟩ := (Submodule.mem_span_range_iff_exists_fun R).1 hmem
  exact ⟨cf, hcf.symm⟩

end GlobalTheory.LogKSDiv
end
