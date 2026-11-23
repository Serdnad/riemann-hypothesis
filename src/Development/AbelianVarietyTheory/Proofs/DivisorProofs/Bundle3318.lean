module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle777
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationAdjointEndomorphismsCommute
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2848
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2974
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle624
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3307
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2666
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle654
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle731
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle681
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle669
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle640
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle655
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle016
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrystallinePull2SumCup
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle023
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2668
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3308
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsChernExistsUniqueAndIso
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1628
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftLeftFst
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelToroidalPolCharts
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3309
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle025
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle127
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle048
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle121
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069
import Development.AbelianVarietyTheory.Definitions.Divisors.CommGroupMulMulEqMulInvMulMulMul
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueIsTanFrameOfIsEmpty
import Development.AbelianVarietyTheory.Definitions.Divisors.IsoOverOfIsOpenImmersion
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle012
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
public import Development.AbelianVarietyTheory.Definitions.Divisors.UnitaryWeightExponentVectorSignatureWeightMuZero

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two

noncomputable section
namespace GlobalTheory.Mum.Two

open GlobalTheory.Balanced

section Gen
variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D₁ D₂ : DegData R I}
  {A₁ A₂ : PolAV (Sp (FractionRing R))} {G₁ G₂ : Over (Sp R)} [GrpObj G₁] [IsCommMonObj G₁] [GrpObj G₂]
  [IsCommMonObj G₂] {U₁ : UnifPre I D₁ A₁ G₁} {U₂ : UnifPre I D₂ A₂ G₂}

theorem toG_gen₀ {a : G₁ ⟶ G₂} {c : A₁.A ⟶ A₂.A} (hc : Gen₀ U₁ U₂ a c) {F : Type} [Field F]
    [Algebra (FractionRing R) F] (x : TFK (R := R) F ⟶ A₁.A) : toG U₂ (x ≫ c) = toG U₁ x ≫ a.left := by
  have e : c ≫ U₂.gen.inv = U₁.gen.inv ≫ (Over.pullback (jK R)).map a := by
    rw [Iso.eq_inv_comp, ← Category.assoc, ← hc, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have e' : c.left ≫ U₂.gen.inv.left = U₁.gen.inv.left ≫ ((Over.pullback (jK R)).map a).left :=
    congrArg (fun q => q.left) e
  have e₂ : ((Over.pullback (jK R)).map a).left ≫ pullback.fst G₂.hom (jK R) = pullback.fst G₁.hom (jK R) ≫ a.left :=
    pullback.lift_fst _ _ _
  calc toG U₂ (x ≫ c) = x.left ≫ (c.left ≫ U₂.gen.inv.left) ≫ pullback.fst G₂.hom (jK R) := by
        simp only [toG, Over.comp_left, Category.assoc]
    _ = _ := by rw [e', Category.assoc, e₂, toG, Category.assoc, Category.assoc]

end Gen

theorem exists_toG_pull {R V : Type} [CommRing R] [IsDomain R] [CommRing V] [IsDomain V] {I : Ideal R} {I' : Ideal V}
    (φ : R →+* V) {D : DegData R I} {D' : DegData V I'} {A : PolAV (Sp (FractionRing R))}
    {A' : PolAV (Sp (FractionRing V))} {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G]
    (U : UnifPre I D A G) (U' : UnifPre I' D' A' ((Over.pullback (specOf φ)).obj G))
    {F : Type} [Field F] [Algebra (FractionRing R) F] [Algebra (FractionRing V) F]
    (hF : ∀ r : R, algebraMap (FractionRing R) F (algebraMap R _ r) =
      algebraMap (FractionRing V) F (algebraMap V _ (φ r))) (z : TFK (R := R) F ⟶ A.A) :
    ∃ z' : TFK (R := V) F ⟶ A'.A, toG U' z' ≫ pullback.fst G.hom (specOf φ) = toG U z := by
  have w : toG U z ≫ G.hom = (jFK (R := V) F ≫ jK V) ≫ specOf φ := by
    rw [toG_over]
    simp only [jFK, jK, specOf, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    exact RingHom.ext hF
  obtain ⟨z', hz'⟩ := exists_toG U' (pullback.lift _ _ w) (pullback.lift_snd _ _ _)
  exact ⟨z', by rw [hz']; exact pullback.lift_fst _ _ _⟩



theorem exists_key : ∀ (R : Type) [CommRing R] [IsDomain R] [CharZero R] (I : Ideal R), AdmBase R I → ∀ (D₁ D₂ : DegData R I) (A₁ A₂ : PolAV (Sp (FractionRing R))) (G₁ G₂ : Over (Sp R)) [GrpObj G₁] [IsCommMonObj G₁] [GrpObj G₂] [IsCommMonObj G₂], IsSemiAbelian G₁ → IsSemiAbelian G₂ → ∀ (U₁ : Unif I D₁ A₁ G₁) (U₂ : Unif I D₂ A₂ G₂) (a : G₁ ⟶ G₂) (c : A₁.A ⟶ A₂.A) (b : D₁.toPre.P.A ⟶ D₂.toPre.P.A) (h : D₂.toPre.X →+ D₁.toPre.X), IsMonHom c → Gen₀ U₁.toUnifPre U₂.toUnifPre a c → Lin U₁.toUnifPre U₂.toUnifPre a b h → Coord U₁.toUnifPre U₂.toUnifPre a b h → Function.Injective h → ∃ (F : Type) (_ : Field F) (_ : IsAlgClosed F) (_ : Algebra (FractionRing R) F), Key U₁.toUnifPre U₂.toUnifPre c b h F := by
  intro R _ _ _ I hR D₁ D₂ A₁ A₂ G₁ G₂ _ _ _ _ hG₁ hG₂ U₁ U₂ a c b h _ hgen hlin hcoord hinj
  have hL := GlobalTheory.firstFiveLaws
  obtain ⟨V, _, _, _, φ, hV, hφ, hI⟩ := GlobalTheory.adic_base_embeds_valuation_algebraic_closure.1 R I hR
  have : CharZero V := charZero_of_injective_ringHom hφ
  have hR' : AdmBase V (maximalIdeal V) := ⟨inferInstance, inferInstance, inferInstance, hV⟩
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible V
  obtain ⟨v, hv⟩ := GlobalTheory.adic_base_embeds_valuation_algebraic_closure.2 V ϖ hϖ
  obtain ⟨D₁', hD₁, A₁', U₁', hG₁', hU₁, hpt₁, -⟩ := GlobalTheory.T.uniformisation_endomorphisms_to_complete_dvr hL R I hR D₁ A₁ G₁ hG₁ U₁ V φ hV hφ hI
  obtain ⟨D₂', hD₂, A₂', U₂', hG₂', hU₂, hpt₂, -⟩ := GlobalTheory.T.uniformisation_endomorphisms_to_complete_dvr hL R I hR D₂ A₂ G₂ hG₂ U₂ V φ hV hφ hI
  let Ω := AlgebraicClosure (FractionRing V)
  let ψ : R →+* Ω := ((algebraMap (FractionRing V) Ω).comp (algebraMap V (FractionRing V))).comp φ
  have hψ : Function.Injective ψ :=
    ((algebraMap (FractionRing V) Ω).injective.comp (IsFractionRing.injective V (FractionRing V))).comp hφ
  let _ : Algebra (FractionRing R) Ω := (IsFractionRing.lift hψ).toAlgebra
  have hF : ∀ r : R, algebraMap (FractionRing R) Ω (algebraMap R _ r) =
      algebraMap (FractionRing V) Ω (algebraMap V _ (φ r)) := fun r => IsFractionRing.lift_algebraMap hψ r
  obtain ⟨ex₁, -, io₁, ns₁⟩ := hpt₁ Ω hF
  obtain ⟨ex₂, sur₂, io₂, ns₂⟩ := hpt₂ Ω hF
  obtain ⟨b', h', hlin', hb', hh'⟩ := GlobalTheory.T.uniformisedGroupHom_pullback_maps R V I (maximalIdeal V) φ D₁ D₂ A₁ A₂ G₁ G₂ U₁ U₂ D₁' D₂' A₁' A₂'
    hD₁ hD₂ U₁' U₂' hU₁ hU₂ a b h hlin
  have hcoord' := GlobalTheory.T.torusCoordinates_compare_normalisedGenerators V (maximalIdeal V) hR' D₁' D₂' A₁' A₂' _ _ U₁'.toUnifPre U₂'.toUnifPre
    ((Over.pullback (specOf φ)).map a) b' h' hlin'
  let c' : A₁'.A ⟶ A₂'.A := U₁'.gen.inv ≫ (Over.pullback (jK V)).map ((Over.pullback (specOf φ)).map a) ≫ U₂'.gen.hom
  have hgen' : Gen₀ U₁'.toUnifPre U₂'.toUnifPre ((Over.pullback (specOf φ)).map a) c' := by
    simp only [Gen₀, c', Iso.hom_inv_id_assoc]
  have hc' : IsMonHom c' := by
    have := U₁'.gen_hom
    have := U₂'.gen_hom
    have := hlin'.1
    dsimp only [c']
    infer_instance
  have hinj' : Function.Injective h' := fun x y hxy => hD₂.xe.injective (hinj (by rw [← hh', ← hh', hxy]))
  have key' := GlobalTheory.T.trait_torsion_point_map_commutes_char_injective_hom V hV ϖ hϖ Ω v hv D₁' D₂' A₁' A₂' _ _ hG₁' hG₂' U₁' U₂' ((Over.pullback (specOf φ)).map a)
    c' b' h' hc' hgen' hlin' hcoord' hinj'
  choose π₁ hπ₁ _ using ex₁
  choose π₂ hπ₂ _ using ex₂
  refine ⟨Ω, inferInstance, inferInstance, inferInstance, fun k hk p x hx g' hact => ?_⟩
  have hact' : Act D₁'.toPre D₂'.toPre b' h' (π₁ p.g) (π₂ g') :=
    (GlobalTheory.T.torusExtensionPointAction_pullback_data R V φ D₁.toPre D₂.toPre D₁'.toPre D₂'.toPre hD₁ hD₂ b h b' h' hlin.2.1 hlin'.2.1 hb' hh'
      (fun χ => (hcoord χ).imp fun _ hu => hu.1) Ω p.g g' (π₁ p.g) (π₂ g') (hπ₁ _) (hπ₂ _)).1 hact
  let ρp : QkPt D₁'.toPre Ω k := ⟨hD₁.xe.symm p.y, π₁ p.g, by
    obtain ⟨s, h1, h2⟩ := p.eq
    exact ⟨π₁ s, (ns₁ k _ _ _ _ (hπ₁ _) (hπ₁ _)).1 h1, (io₁ _ _ _ (hπ₁ _)).1 (by rwa [AddEquiv.apply_symm_apply])⟩⟩
  obtain ⟨x', hx'e⟩ := exists_toG_pull φ U₁.toUnifPre U₁'.toUnifPre hF x
  have hx' : QkToAkU U₁'.toUnifPre Ω k ρp x' :=
    hL.2.2.2.2.qkBaseChange R V I _ hR hR' φ D₁ A₁ G₁ U₁ _ (Iso.refl _) (inferInstanceAs (IsMonHom (𝟙 _))) A₁' D₁'
      hD₁ U₁' hU₁ Ω hF k hk p x ρp x' rfl (hπ₁ _)
      (by simpa only [toG, Category.assoc, Iso.refl_hom, Over.id_left, Category.id_comp] using hx'e) hx
  obtain ⟨r, rg, hr⟩ := key' k hk ρp x' hx' (π₂ g') hact'
  let p' : QkPt D₂.toPre Ω k := ⟨hD₂.xe r.y, g', by
    obtain ⟨s', h1, h2⟩ := r.eq
    obtain ⟨s, hs, -⟩ := sur₂ s'
    exact ⟨s, (ns₂ k _ _ _ _ (hπ₂ g') hs).2 (rg ▸ h1), (io₂ _ _ _ hs).2 h2⟩⟩
  refine ⟨p', rfl, ?_⟩
  obtain ⟨f₂, hf₂, -⟩ := GlobalTheory.T.uniformisation_torsion_identification_with_pairing hL R I hR D₂ A₂ G₂ hG₂ U₂ Ω k hk
  obtain ⟨f₂', hf₂', -⟩ := GlobalTheory.T.uniformisation_torsion_identification_with_pairing hL V _ hR' D₂' A₂' _ hG₂' U₂' Ω k hk
  obtain ⟨z', hz'e⟩ := exists_toG_pull φ U₂.toUnifPre U₂'.toUnifPre hF (f₂ p')
  have hz' : QkToAkU U₂'.toUnifPre Ω k r z' :=
    hL.2.2.2.2.qkBaseChange R V I _ hR hR' φ D₂ A₂ G₂ U₂ _ (Iso.refl _) (inferInstanceAs (IsMonHom (𝟙 _))) A₂' D₂'
      hD₂ U₂' hU₂ Ω hF k hk p' (f₂ p') r z' (hD₂.xe.symm_apply_apply r.y).symm (rg ▸ hπ₂ g')
      (by simpa only [toG, Category.assoc, Iso.refl_hom, Over.id_left, Category.id_comp] using hz'e) ((hf₂ _ _).2 rfl)
  have ez : z' = x' ≫ c' := ((hf₂' _ _).1 hz').trans ((hf₂' _ _).1 hr).symm
  have hpa : ((Over.pullback (specOf φ)).map a).left ≫ pullback.fst G₂.hom (specOf φ) =
      pullback.fst G₁.hom (specOf φ) ≫ a.left := pullback.lift_fst _ _ _
  refine (hf₂ _ _).2 (toG_injective U₂.toUnifPre ?_).symm
  rw [← hz'e, ez, toG_gen₀ hgen', toG_gen₀ hgen, ← hx'e, Category.assoc, Category.assoc, hpa]

end GlobalTheory.Mum.Two
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (Data Frame Bor rmul lact mat col dmin Wt)
open GlobalTheory.ShFam GlobalTheory.ShFam.BdArc GlobalTheory.Toroidal

noncomputable section

namespace GlobalTheory.KoecherArc

theorem tendsto_val {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
    {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} (Z : Model Xo c β)
    {σ : c.F →+* ℂ} {N : ℕ} {U : Unf Xo c σ N} (hσ : GoodEmb c σ) (hU : IsUnf U) (la : ∀ k, Wt (U.X k).Ψ N)
    (hχ : ∀ k, ∀ γ ∈ (U.X k).Γ, (U.X k).χ (la k) γ = 1) {e : Ix Dw → ℤ} (he : e none = 0) {g : Rul Xo c}
    (hg : g ∈ AllWt.secZ Xo c e) (hS : ∀ k, rdU U g k ∈ (U.X k).SS (la k)) {A : Type} [CommRing A] {φ : c.F →+* A}
    {x : Sp A ⟶ gen Z} (fr : EigFrame Z φ (x ≫ genι Z)) {ψ : ℂ → (A →+* ℂ)} {r : ℝ} {y : ℂ → FrPt Xo c (CAt σ)}
    (hb : IsBdArc Z σ φ x ψ r) (hm : ∀ u ∈ Metric.ball (0 : ℂ) r, u ≠ 0 → Matches fr (ψ u) (y u)) (p q : A)
    (hpq : ∀ u ∈ Metric.ball (0 : ℂ) r, u ≠ 0 → ψ u q ≠ 0 ∧ toC (evR Xo c g (y u)) * ψ u q = ψ u p) :
    Tendsto (fun u => toC (evR Xo c g (y u))) (𝓝[≠] 0) (𝓝 0) := by
  haveI : IsLocalRing (CAt σ) := inferInstanceAs (IsLocalRing ℂ)
  obtain ⟨k, T, M₀, γ₀, xx, hT, hO₀, hL⟩ := GlobalTheory.T.exists_holomorphicFrameOrbit_lift_of_arc E H Dw l Xo c O β Z σ N U A φ x fr ψ r y hσ hU hb.1 hm
  obtain ⟨M, γ, hO, hγ⟩ := GlobalTheory.T.exists_holomorphicFrameOrbit_unipotent_order_two E N _ T M₀ γ₀ xx hO₀
  have hne : γ ≠ 1 := by
    rintro rfl
    obtain ⟨x₀, hx₀, x', h1, h2⟩ := GlobalTheory.T.trivial_monodromy_orbit_converges_symmetric_domain E N _ T M xx hO
    exact GlobalTheory.T.boundary_arc_lift_not_converges_symmetric_domain E H Dw l Xo c O β Z σ N U A φ x fr ψ r y k T xx hσ hU hb hm hL x₀ hx₀ x' h1 h2
  obtain ⟨ξ, c', hξ, hc', ht⟩ := GlobalTheory.T.holomorphicFrameOrbit_isotropic_vector_short E N _ T M γ xx hO hγ hne
  obtain ⟨m, v, Lp, Lm, hlim⟩ :=
    GlobalTheory.T.exists_arcLift_periods_tendsto_span E H Dw l Xo c O β Z σ N U A φ x fr ψ r y k T M γ xx hσ hU hb.1 hm hO hL
  have hper := GlobalTheory.T.eigenframe_specialization_uniform_bound E H Dw l Xo c O β Z σ N U A φ x fr ψ r y k T M γ xx hσ hU hb.1 hm hO hL
  obtain ⟨C', B, hn⟩ := GlobalTheory.T.normFactor_inv_le_pow_holomorphicOrbit_periodBound E N _ T M γ xx (la k) m v Lp Lm hO hlim hper
  have hp := tendsto_cusp (hS k) hO.2.2.2.1 hξ hc' ht hn
  have hsec := (hS k).1.1
  obtain ⟨hM, hΓ, hdiff, hdom, hperd⟩ := hO
  have hγd : ∀ w : ℂ, T < w.im → lact γ (xx w) ∈ (U.X k).dom := fun w hw =>
    GlobalTheory.MajInv.lact_mem_dom _ ((U.X k).Γ_stab γ hΓ) (hdom w hw)
  refine GlobalTheory.T.meromorphic_germ_vanishes_of_periodic_exp_modulus (fun w => rdU U g k (xx w)) (fun _ => 0) _ (fun u => ψ u p) (fun u => ψ u q) T r M 1 1 hM
    one_pos (one_pow 1) hb.1.1.1 (hsec.1.comp hdiff hdom) (differentiableOn_const 0) (fun w hw => ?_) hp
    (hb.1.1.2 p) (hb.1.1.2 q) hpq
  obtain ⟨b, hb1, hb2, hb3⟩ := hperd w hw
  obtain ⟨h, hl⟩ := hL w hw
  refine ⟨?_, rfl, ?_⟩
  · simp only [hb3]
    rw [hsec.2.1 _ (hγd w hw) b hb1, hsec.2.2 γ hΓ _ (hdom w hw), hχ k γ hΓ]
    simp [ReciprocityTheory.ChartRestriction.G.FD.bchar, hb2]
  · rw [Complex.exp_zero, norm_one, mul_one]
    have rd : rdU U g k (xx w) = toC (evR Xo c g (U.un k ⟨xx w, h⟩)) := dif_pos h
    show ‖toC (evR Xo c g (y (eTwoPi w)))‖ = ‖rdU U g k (xx w)‖
    rw [rd, GlobalTheory.ShFam.KeyRel.evR_sameLie he hg hl]

theorem isBdArc_mono {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
    {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}
    {σ : c.F →+* ℂ} {A : Type} [CommRing A] {φ : c.F →+* A} {x : Sp A ⟶ gen Z} {ψ : ℂ → (A →+* ℂ)} {r ρ : ℝ}
    (h : IsBdArc Z σ φ x ψ r) (hρ : 0 < ρ) (hρr : ρ ≤ r) : IsBdArc Z σ φ x ψ ρ :=
  ⟨⟨⟨hρ, fun a => (h.1.1.2 a).mono (Metric.ball_subset_ball hρr)⟩, h.1.2.1,
    fun u hu => h.1.2.2 u (Metric.ball_subset_ball hρr hu)⟩, h.2.1, fun u hu => h.2.2 u (Metric.ball_subset_ball hρr hu)⟩

end GlobalTheory.KoecherArc
end
end

section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.AbDual.isPerfPair_of_abelianHodgeDeRham : GlobalTheory.Published.AbelianHodgeDeRham → ∀ (R : Type) [CommRing R] (A B : Over (Sp R)) [GrpObj A] [GrpObj B] (g : ℕ), IsAbelianScheme A → IsAbelianScheme B → SmoothOfRelativeDimension g A.hom → SmoothOfRelativeDimension g B.hom → ∀ P : LB (A ⊗ B).left, AbDual.IsPerfect A B P → ∀ φ : HdR A →ₗ[R] HdR B →ₗ[R] R, AbDual.IsCorrForm (dp0 R) (𝟙 _) A B P φ → φ.IsPerfPair := by
  intro H R _ A B _ _ g hA hB hgA hgB P hP φ hφ
  obtain ⟨Fr, -, BC⟩ := GlobalTheory.T.abelianSchemeDeRham_free_hodgeSequence_baseChange H
  obtain ⟨fA, pA, -⟩ := Published.AbelianDeRham.Free.prim Fr hA hgA
  obtain ⟨fB, pB, -⟩ := Published.AbelianDeRham.Free.prim Fr hB hgB
  refine GlobalTheory.T.isPerfectPair_of_geometric_fibres R (primDR A) (primDR B) φ ?_
  intro Ω _ _ _
  have iA := ReciprocityTheory.ChartRestriction.G.Geo.Tor.isGrpPullback_pullback A (spMap (algebraMap R Ω))
  have iB := ReciprocityTheory.ChartRestriction.G.Geo.Tor.isGrpPullback_pullback B (spMap (algebraMap R Ω))
  obtain ⟨h, h₁, h₂⟩ := AbDual.exists_prod_pullback iA iB
  have hP' := ReciprocityTheory.ChartRestriction.G.Geo.Tor.pull_isLB hP.isLB h
  have perf' := AbDual.IsPerfect.baseChange iA iB h₁ h₂ hP' (Cris.ChernExists.lbIso_refl hP') hP
  obtain ⟨φ', hφ', hcorr⟩ := hφ.pull hP.isLB (Published.AbelianDeRham.bcMor iA) (Published.AbelianDeRham.bcMor iB) h₁ h₂ hP'
    (Cris.ChernExists.lbIso_refl hP')
  have hA' := isAbelianScheme_pullback_obj (spMap (algebraMap R Ω)) A hA
  have hB' := isAbelianScheme_pullback_obj (spMap (algebraMap R Ω)) B hB
  have hgA' : SmoothOfRelativeDimension g ((Over.pullback (spMap (algebraMap R Ω))).obj A).hom :=
    (smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback (IsPullback.of_hasPullback _ _) hgA
  have hgB' : SmoothOfRelativeDimension g ((Over.pullback (spMap (algebraMap R Ω))).obj B).hom :=
    (smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback (IsPullback.of_hasPullback _ _) hgB
  exact ⟨primDR _, primDR _, inferInstance, inferInstance, inferInstance, inferInstance,
    (Published.AbelianDeRham.bcMor iA).pull, (Published.AbelianDeRham.bcMor iB).pull, φ',
    (BC R A g hA hgA Ω _ _ iA).1, (BC R B g hB hgB Ω _ _ iB).1,
    GlobalTheory.T.de_rham_polarization_perfect_pairing H Ω _ _ g hA' hB' hgA' hgB' _ perf' φ' hφ', fun x x' y y' hx hy ↦ hcorr x x' y y' hx hy⟩
end

section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj

theorem _root_.GlobalTheory.T.cechCocycle_verticalFields_eq_coboundary_add_logDerivatives : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X), IsProper t.G.hom → Out.RelAmple t.G t.PP.L → Out.KTriv t.G t.PP.L → ∀ (U : X.affineOpens) (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(X, U.1)) ⟶ t.G.left)), (∀ i, IsTanAtG t (chart U) (v i)) → (∀ w, IsTanAtG t (chart U) w → ∃! cf : Fin n → Γ(X, U.1), IsCombAtG t (chart U) v cf w) → ∀ (J : Type) (W : J → t.G.left.Opens) (j : J → t.PP.L.ι), (∀ i, IsAffineOpen (W i)) → ⨆ i, W i = t.G.hom ⁻¹ᵁ U.1 → (∀ i, W i ≤ t.PP.L.U (j i)) → ∀ (e : J → J → ∀ O : t.G.left.Opens, Γ(t.G.left, O) → Γ(t.G.left, O)), (∀ i i', IsField (W i ⊓ W i') (e i i')) → (∀ i i' (h : W i ⊓ W i' ≤ t.G.hom ⁻¹ᵁ U.1) (r : Γ(X, U.1)), e i i' (W i ⊓ W i') ((t.G.hom.appLE U.1 (W i ⊓ W i') h).hom r) = 0) → (∀ i i' i'' (O : t.G.left.Opens), O ≤ W i ⊓ W i' ⊓ W i'' → ∀ f : Γ(t.G.left, O), e i i' O f + e i' i'' O f = e i i'' O f) → ∃ (Θ : Matrix (Fin n) (Fin n) Γ(X, U.1)) (h : J → ∀ O : t.G.left.Opens, Γ(t.G.left, O) → Γ(t.G.left, O)), (∀ i, IsField (W i) (h i)) ∧ (∀ i (hW : W i ≤ t.G.hom ⁻¹ᵁ U.1) (r : Γ(X, U.1)), h i (W i) ((t.G.hom.appLE U.1 (W i) hW).hom r) = 0) ∧ ∀ (i i' : J) (O : t.G.left.Opens), O ≤ W i ⊓ W i' → ∀ (f : Γ(t.G.left, O)) (S : Type) [CommRing S] (φ : Γ(X, U.1) →+* S) (g₀ : Sp S ⟶ t.G.left) (w : Fin n → (Sp (DualNumber S) ⟶ t.G.left)), g₀ ≫ t.G.hom = spMap φ ≫ chart U → ⊤ ≤ g₀ ⁻¹ᵁ O → (∀ a, IsTranslate t φ g₀ (v a) (w a)) → valR g₀ O (e i i' O f) = valR g₀ O (h i O f - h i' O f) + ∑ a, ∑ b, φ (Θ a b) * ((valR (w b) _ (t.PP.L.g (j i) (j i')).val).snd * valR g₀ _ (t.PP.L.g (j i) (j i'))⁻¹.val) * (valR (w a) O f).snd := by
  first | exact @GlobalTheory.KSCocycle.exists_coboundary_add_dlog | exact GlobalTheory.KSCocycle.exists_coboundary_add_dlog | (intros; apply GlobalTheory.KSCocycle.exists_coboundary_add_dlog <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.siegelIntegralToroidal_of_polarisedCharts : (∀ g : ℕ, ∃ φ : InvFun ℤ, IsPolFan (id : ℤ → ℤ) g φ ∧ NoSelfInt (id : ℤ → ℤ) g φ) → GlobalTheory.Published.SiegelToroidalPolCharts → GlobalTheory.Published.SiegelToroidalIntegral := by
  first | exact @GlobalTheory.PolDeg.siegelToroidalIntegral_of_polCharts | exact GlobalTheory.PolDeg.siegelToroidalIntegral_of_polCharts | (intros; apply GlobalTheory.PolDeg.siegelToroidalIntegral_of_polCharts <;> assumption)
end

end

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two

theorem _root_.GlobalTheory.T.exists_algClosedField_torsionMaps_commute_hom : ∀ (R : Type) [CommRing R] [IsDomain R] [CharZero R] (I : Ideal R), AdmBase R I → ∀ (D₁ D₂ : DegData R I) (A₁ A₂ : PolAV (Sp (FractionRing R))) (G₁ G₂ : Over (Sp R)) [GrpObj G₁] [IsCommMonObj G₁] [GrpObj G₂] [IsCommMonObj G₂], IsSemiAbelian G₁ → IsSemiAbelian G₂ → ∀ (U₁ : Unif I D₁ A₁ G₁) (U₂ : Unif I D₂ A₂ G₂) (a : G₁ ⟶ G₂) (c : A₁.A ⟶ A₂.A) (b : D₁.toPre.P.A ⟶ D₂.toPre.P.A) (h : D₂.toPre.X →+ D₁.toPre.X), IsMonHom c → Gen₀ U₁.toUnifPre U₂.toUnifPre a c → Lin U₁.toUnifPre U₂.toUnifPre a b h → Coord U₁.toUnifPre U₂.toUnifPre a b h → Function.Injective h → ∃ (F : Type) (_ : Field F) (_ : IsAlgClosed F) (_ : Algebra (FractionRing R) F), Key U₁.toUnifPre U₂.toUnifPre c b h F := by
  first | exact @GlobalTheory.Mum.Two.exists_key | exact GlobalTheory.Mum.Two.exists_key | (intros; apply GlobalTheory.Mum.Two.exists_key <;> assumption)

end
end
