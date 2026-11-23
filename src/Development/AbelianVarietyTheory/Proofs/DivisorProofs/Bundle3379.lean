module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle074
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle071
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle068
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2752
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3212
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3160
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3101
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3104
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasTraitsOnOfHasTraitsP
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3152
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3373
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3280
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3102
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle309
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3211
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3251
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2648
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle665
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle632
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle019
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle002
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1509
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1427
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1574
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3375
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2615
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1569
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1429
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2670
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3376
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdditiveLiftIff
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Rat
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
import Mathlib.Tactic.Basify
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle007
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle013
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle001
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle012

@[expose] public section

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.Poinc GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TChartEt

theorem injective_of_flat_isLocalHom {A B : Type} [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B]
    (f : A →+* B) (hf : f.Flat) [hl : IsLocalHom f] : Function.Injective f := by
  algebraize [f]
  have : IsLocalHom (algebraMap A B) := hl
  have := Module.FaithfullyFlat.of_flat_of_isLocalHom (A := A) (B := B)
  exact FaithfulSMul.algebraMap_injective A B

theorem charZero_stalk_of_flat {o : Type} [CommRing o] [IsDomain o] [CharZero o] (X : Scheme.{0}) (s : X ⟶ Sp o)
    [Flat s] (x : X) : CharZero (X.presheaf.stalk x) := by
  have hf : (s.stalkMap x).hom.Flat := Flat.stalkMap s x
  have h0 : CharZero ((Sp o).presheaf.stalk (s x)) := by
    have : CharZero Γ(Sp o, ⊤) := (Scheme.ΓSpecIso (.of o)).hom.hom.charZero
    exact charZero_of_injective_ringHom (f := ((Sp o).presheaf.germ ⊤ (s x) trivial).hom)
      (germ_injective_of_isIntegral (Sp o) (U := ⊤) (s x) trivial)
  exact charZero_of_injective_ringHom (injective_of_flat_isLocalHom _ hf)

theorem essFiniteType_int_stalk (n : ℕ) (X : Scheme.{0}) (s : X ⟶ Sp (cycAway n)) [LocallyOfFiniteType s] (x : X) :
    Algebra.EssFiniteType ℤ (X.presheaf.stalk x) := by
  have h1 : (s.stalkMap x).hom.EssFiniteType := LocallyOfFiniteType.stalkMap s x
  let p : PrimeSpectrum (cycAway n) := s x
  have h2 : (algebraMap (cycAway n) ((Spec.structureSheaf (cycAway n)).presheaf.stalk p)).EssFiniteType :=
    RingHom.essFiniteType_algebraMap.2 (Algebra.EssFiniteType.of_isLocalization _ p.asIdeal.primeCompl)
  haveI := finiteType_cycAway n
  have h3 : (algebraMap ℤ (cycAway n)).EssFiniteType := RingHom.essFiniteType_algebraMap.2 inferInstance
  have h4 := (h3.comp h2).comp h1
  rw [← RingHom.essFiniteType_algebraMap]
  convert h4
  exact RingHom.ext_int _ _

theorem charZero_stalk_centre {g n : ℕ} (F : SFam g n (zetaAway n)) {S : Scheme.{0}} (j : F.X ⟶ S)
    {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] (y : Sp (FractionRing R) ⟶ F.X) (ξ : Sp R ⟶ S)
    (hy : y ≫ j = jK R ≫ ξ) : CharZero (S.presheaf.stalk (ξ (closedPoint R))) := by
  haveI := F.smooth
  haveI : Smooth F.s := SmoothOfRelativeDimension.smooth (g * (g + 1) / 2) F.s
  haveI : Flat F.s := inferInstance
  let w : Sp (FractionRing R) := closedPoint (FractionRing R)
  have hsp : ξ (jK R w) ⤳ ξ (closedPoint R) := (specializes_closedPoint _).map ξ.continuous
  have hjw : j (y w) = ξ (jK R w) := by
    rw [← Scheme.Hom.comp_apply, hy, Scheme.Hom.comp_apply]
  haveI : CharZero (F.X.presheaf.stalk (y w)) := charZero_stalk_of_flat F.X F.s (y w)
  haveI h₁ : CharZero (S.presheaf.stalk (j (y w))) := (j.stalkMap (y w)).hom.charZero
  rw [hjw] at h₁
  exact (S.presheaf.stalkSpecializes hsp).hom.charZero

end GlobalTheory.TChartEt

namespace GlobalTheory.TChartEt

theorem isEtaleCompletion_tautChart : GlobalTheory.Poinc.Sep.SepSt → ∀ g : ℕ, 1 ≤ g → ∀ φ : InvFun ℤ, IsPolFan id g φ → NoSelfInt id g φ → ∀ n : ℕ, 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (Z : Scheme.{0}) (z : Z ⟶ Sp (cycAway n)) (i : F.X ⟶ Z) (OZ : LB Z) (d : ℕ) (S : Scheme.{0}) (π : S ⟶ Z) (j : F.X ⟶ S) [IsOpenImmersion j] (BD : GlobalTheory.EffCartierData S), MinAt5 F z i OZ → BlowAt F z i φ d π j BD → ∀ (C : Taut (zetaAway n) g n φ) (G₁ : Over (Sp C.R)) [GrpObj G₁] [IsCommMonObj G₁] (y : Sp (FractionRing C.R) ⟶ F.X) (α₁ : pullback G₁.hom (jK C.R) ⟶ F.univ.A.left) (ξ : Sp C.R ⟶ S), C.IsFam F G₁ y α₁ → y ≫ j = jK C.R ≫ ξ → IsEtaleCompletion (Scheme.stalkClosedPointTo ξ).hom ∧ ((residue C.R).comp (Scheme.stalkClosedPointTo ξ).hom).FormallyUnramified := by
  intro hSep g hg φ hφ hns n hn ho F Z z i OZ d S π j _ BD hM hB C G₁ _ _ y α₁ ξ hF hy
  obtain ⟨J, h₁, h₂, h₃, hNB, hP, h₄⟩ := hB
  haveI : GlobalTheory.IsNormalScheme S := hNB.1
  haveI : CharZero (S.presheaf.stalk (ξ (closedPoint C.R))) := charZero_stalk_centre F j y ξ hy
  haveI : LocallyOfFiniteType (π ≫ z) := by
    obtain ⟨N, ιP, hιP, e⟩ := hP
    rw [← e]
    haveI := ReciprocityTheory.ChartRestriction.G.Geo.Tor.isProper_str (cycAway n) N
    infer_instance
  haveI : Algebra.EssFiniteType ℤ (S.presheaf.stalk (ξ (closedPoint C.R))) :=
    essFiniteType_int_stalk n S (π ≫ z) _
  haveI : IsNoetherianRing C.R := C.compl.1
  obtain ⟨hqf, hfin⟩ := GlobalTheory.T.quasiFinite_tautologicalChart_of_separation hSep g hg φ hφ hns n hn ho F Z z i OZ d S π j BD hM
    ⟨J, h₁, h₂, h₃, hNB, hP, h₄⟩ C G₁ y α₁ ξ hF hy
  have hdim := GlobalTheory.T.ringKrullDim_stalk_le_tautologicalChartRing g hg φ hφ hns n hn ho F Z z i OZ d S π j BD hM
    ⟨J, h₁, h₂, h₃, hNB, hP, h₄⟩ C G₁ y α₁ ξ hF hy hfin
  have hgal := GlobalTheory.T.tautologicalChart_galois_rigid_stalk hn F S j C G₁ y α₁ ξ hF hy
  exact GlobalTheory.T.isEtaleCompletion_of_quasiFinite_galoisRigid _ _ (Scheme.stalkClosedPointTo ξ).hom C.compl.2.1 hqf hfin hdim hgal

end GlobalTheory.TChartEt
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep

noncomputable section

namespace GlobalTheory.USep

theorem range_jK_spMap_subset : ∀ (V R : Type) [CommRing V] [IsDomain V] [CommRing R] [IsDomain R] (ρ : V →+* R), Function.Injective ρ → ∀ (X : Scheme.{0}) (χ : Sp V ⟶ X), Set.range (jK R ≫ spMap ρ ≫ χ) ⊆ Set.range (jK V ≫ χ) := by
  intro V R _ _ _ _ ρ hρ X χ x ⟨p, hp⟩
  let q : Sp (FractionRing V) := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (FractionRing V))
  have key : (spMap ρ) ((jK R) p) = (jK V) q := by
    apply PrimeSpectrum.ext
    change Ideal.comap ρ (Ideal.comap (algebraMap R (FractionRing R)) p.asIdeal) =
      Ideal.comap (algebraMap V (FractionRing V)) ⊥
    haveI : p.asIdeal.IsPrime := PrimeSpectrum.isPrime p
    rw [Ideal.eq_bot_of_prime p.asIdeal, Ideal.comap_comap,
      Ideal.comap_bot_of_injective _ (IsFractionRing.injective V (FractionRing V)),
      Ideal.comap_bot_of_injective _ (by rw [RingHom.coe_comp]; exact (IsFractionRing.injective R (FractionRing R)).comp hρ)]
  refine ⟨q, ?_⟩
  rw [← hp]
  change χ ((jK V) q) = χ ((spMap ρ) ((jK R) p))
  rw [key]

theorem exists_elements_cover : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c), ∀ (φ : InvFun (𝓞 E)), IsPolFan H.bar (min Dw.p Dw.q) φ → ∀ (d : ℕ) (J : C.Z.IdealSheafData), (∀ x ∈ J.support, x ∉ Set.range C.i) → UValOn Xo c C.i φ J d → ∀ (S : Scheme.{0}) (π : S ⟶ pullback C.z (spMap C.b)), IsNormBl π (J.comap (pullback.fst C.z (spMap C.b))) → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (Cm : GlobalTheory.UChart.MonoFam Xo c φ V), GlobalTheory.Mum.Base V → ∀ ξ : Sp V ⟶ S, Cm.y ≫ C.iF = jK V ≫ ξ ≫ π → ∀ (N₁ : ℕ) (M : Scheme.{0}) [IsIntegral M] (g : M ⟶ C.Z) (z₁ : M) (ζ : Sp (M.presheaf.stalk z₁) ⟶ pullback C.z (spMap C.b)) (Φ : VSys (H.bar : 𝓞 E → 𝓞 E) (min Dw.p Dw.q) !![(1 : ℤ)] N₁ (M.presheaf.stalk z₁)) (y : Φ.Y) (ρ : V →+* Φ.V y) (e : Φ.X y ≃ₗ[𝓞 E] Cm.P.D.toPre.X) (h : Fin (Φ.m y) ≃ Fin Cm.m) (U : M.Opens), (U : Set M).Nonempty → IsCov C g z₁ ζ → GlobalTheory.GSep.HasTraitsOn ζ Φ.pre U → IsMember ζ Φ Cm (ξ ≫ π) y ρ e h → ∀ (K : Type) [Field K] [IsAlgClosed K] (ev : V →+* K) (k₀ : Subfield K), IsAlgClosed k₀ → (∀ p, (spMap ev ≫ ξ) p = ξ (closedPoint V)) → GlobalTheory.UChart.DefOver k₀ (spMap ev ≫ ξ) → ∀ ga : Fin (Φ.m y) → LinearMap.BilinForm ℤ (Φ.X y), (∀ k a b, ga k a b = Cm.δ (h k) (e a) (e b)) → ∃ ev₁ : Φ.V y →+* K, ev₁.comp ρ = ev ∧ GlobalTheory.Poinc.Sep.Elements Φ y φ (2 * d) ga ev₁ k₀ := by
  intro E _ _ _ H Dw hpq l Xo c C φ hφ d J hJ hV S π hπ V _ _ _ Cm hB ξ hξ N₁ M _ g z₁ ζ Φ y ρ e h U hUne hcov htr hmem K _ _ ev k₀ hk₀ hpt hdef ga hga
  obtain ⟨hρi, hρf, hζ, hst, -⟩ := hmem
  obtain ⟨hρl, hext⟩ := GlobalTheory.T.finite_injective_ringHom_isLocalHom_and_extend V (Φ.V y) K ρ hρi hρf
  obtain ⟨ev₁, hev₁⟩ := hext ev
  have hcov' := hcov
  obtain ⟨-, -, hζg, -⟩ := hcov'
  obtain ⟨S₁, hS₁, p₁, sM, U₁, hft, hqc, hfl, hnorm, hprop, hdom, hcart, hU₁, hlift, hxi⟩ :=
    GlobalTheory.T.exists_normalisedBlowup_finite_normal_cover E H Dw hpq l Xo c C J hJ S π hπ M g z₁ ζ hcov
  haveI := hS₁
  haveI : IsIntegrallyClosed (Φ.V y) := (Φ.cn y).2.1
  have hζ' : (spMap ρ ≫ ξ) ≫ π = spMap (Φ.ev y) ≫ ζ := by rw [hζ, Category.assoc]
  have hgen : Set.range (jK (Φ.V y) ≫ (spMap ρ ≫ ξ) ≫ π) ⊆ Set.range C.iF := by
    intro x hx
    obtain ⟨p, hp⟩ := range_jK_spMap_subset V (Φ.V y) ρ hρi _ (ξ ≫ π) (by simpa only [Category.assoc] using hx)
    simp only [Category.assoc] at hp
    rw [← hξ, Scheme.Hom.comp_apply] at hp
    exact ⟨_, hp⟩
  obtain ⟨ξ₁, hξ₁p, hξ₁⟩ := hxi (Φ.V y) (spMap ρ ≫ ξ) (Φ.ev y) hζ' hgen
  have hcomp : spMap ev₁ ≫ spMap ρ = spMap ev := by
    rw [← hev₁, spMap, spMap, spMap, ← Spec.map_comp]; rfl
  have hpt' : ∀ p, (spMap ev₁ ≫ (spMap ρ ≫ ξ)) p = (spMap ρ ≫ ξ) (closedPoint (Φ.V y)) := by
    intro p
    rw [← Category.assoc, hcomp, hpt]
    change _ = ξ ((spMap ρ) (closedPoint (Φ.V y)))
    rw [spMap, Spec_closedPoint]
  have hdef' : GlobalTheory.UChart.DefOver k₀ (spMap ev₁ ≫ (spMap ρ ≫ ξ)) := by rwa [← Category.assoc, hcomp]
  obtain ⟨hpt₁, hdef₁⟩ := hξ₁ K ev₁ k₀ hk₀ hpt' hdef'
  obtain ⟨b', hb', hid⟩ := GlobalTheory.T.idealAlong_monomialFamily_eq_span_monomial E H Dw hpq l Xo c C φ hφ d J hJ hV S π hπ V Cm hB ξ hξ
  have hU₂ : ((U₁ ⊓ p₁ ⁻¹ᵁ U : S₁.Opens) : Set S₁).Nonempty := by
    have h1 : ((p₁ ⁻¹ᵁ U : S₁.Opens) : Set S₁).Nonempty := by
      obtain ⟨s, hs⟩ := (p₁.denseRange).exists_mem_open U.isOpen hUne
      exact ⟨s, hs⟩
    exact nonempty_preirreducible_inter U₁.isOpen (p₁ ⁻¹ᵁ U).isOpen hU₁ h1
  obtain ⟨g₀, hg₀, happ⟩ := GlobalTheory.T.exists_correction_properNormalCover_powerLocalEquation C.Z M S₁ sM p₁ g J hft hqc hfl hnorm hprop hdom hcart (U₁ ⊓ p₁ ⁻¹ᵁ U) hU₂ z₁ (Φ.V y) (Φ.ev y)
    (Φ.ev_loc y) ξ₁ hξ₁p
  have hpath : ξ₁ ≫ p₁ ≫ g = spMap ρ ≫ (ξ ≫ π ≫ pullback.fst C.z (spMap C.b)) := by
    rw [← Category.assoc, hξ₁p, Category.assoc, ← hζg, ← Category.assoc, hζ]
    simp only [Category.assoc]
  have hkey : Ideal.span {g₀} = Ideal.span {∏ k, Φ.t y k ^ (2 * b' (h k))} := by
    rw [← hg₀, GlobalTheory.TorRef.idlAlong_comap, hpath, GlobalTheory.TraitOrder.idlAlong_comp, hid, Ideal.map_span,
      Set.image_singleton, map_prod]
    congr 2
    exact (Equiv.prod_comp h _).symm.trans (Finset.prod_congr rfl fun j _ => by
      rw [map_pow, ← (hst j).1, ← pow_mul])
  have hδ : ∀ k, Φ.δ y k = GlobalTheory.PolFan.pull e.toLinearMap ((l.M' : ℤ) • Cm.δ (h k)) :=
    fun k => LinearMap.ext₂ fun a b => by rw [(hst k).2 a b]; rfl
  have hev : ∀ k, φ.evalZ (Φ.δ y k) = φ.evalZ ((l.M' : ℤ) • Cm.δ (h k)) := fun k => by
    rw [hδ k, evalZ_pull φ (r := e.toLinearMap) e.surjective]
  have hbdd : BddAct (H.bar : 𝓞 E → 𝓞 E) := (GlobalTheory.Poinc.bddAct_int_and_cm).2 E H
  have hM : 1 ≤ l.M' := GlobalTheory.LevelExist.M'_pos l
  have hδga : ∀ i, Φ.δ y i = ((l.M' : ℕ) : ℤ) • ga i := fun i => LinearMap.ext₂ fun a b => by
    rw [(hst i).2 a b]; simp [hga]
  refine ⟨ev₁, hev₁, (Scheme.stalkClosedPointTo ξ₁).hom.range, g₀, fun k => 2 * b' (h k),
    fun x hx => GlobalTheory.T.stalkValue_closedPoint_definedOver_subfield S₁ (Φ.V y) ξ₁ K ev₁ k₀ hpt₁ hdef₁ x hx, fun k => ?_,
    Ideal.span_singleton_eq_span_singleton.1 hkey, ?_⟩
  · push_cast
    rw [hev k, hb' (h k)]
    ring
  intro D l' a hdom c' e'
  obtain ⟨e₁, he₁⟩ := happ D e'
  obtain ⟨f, hord, hlead⟩ := GlobalTheory.T.exists_approximate_series_leading_term_fourierSystem (𝓞 E) (H.bar : 𝓞 E → 𝓞 E) hbdd (min Dw.p Dw.q) φ hφ 1 !![(1 : ℤ)] Φ.posW N₁ _ Φ y ga
    l.M' hM hδga (D * (2 * d)) l' a hdom c' (max e' e₁)
  have hord' : Φ.OrdGe φ (D * (2 * d)) e₁ f := fun y' hP hm i =>
    (sup_le_sup_left (α := Ideal (Φ.V y')) (Ideal.pow_le_pow_right (le_max_right e' e₁)) _) (hord y' hP hm i)
  obtain ⟨x, hx, hxe⟩ := he₁ f (by
    intro V' _ _ _ _ hc ξ' ev' hl hcomm hU
    have hj : jK V' ≫ spMap ev' = spMap ((algebraMap V' (FractionRing V')).comp ev') := by
      simp only [jK, spMap, ← Spec.map_comp]; rfl
    obtain ⟨y', hy'⟩ := hlift (FractionRing V') (jK V' ≫ ξ') ((algebraMap V' (FractionRing V')).comp ev')
      (by rw [Category.assoc, ← hcomm, ← Category.assoc, hj]) (fun x hx => (hU hx).1)
    have hUM : Set.range (jK V' ≫ spMap ev' ≫ M.fromSpecStalk z₁) ⊆ (U : Set M) := by
      rw [hcomm]
      rintro _ ⟨q, rfl⟩
      have := (hU ⟨q, rfl⟩).2
      rw [Scheme.Hom.comp_apply]
      exact this
    have htr' := GlobalTheory.T.mem_system_of_order_ge_along_traits GlobalTheory.T.exists_unitaryTrait_through_moduliGenericPoint E H Dw l Xo c C φ d J hV M z₁ U ζ N₁ Φ htr V' hc ev' hl hUM y' hy' D e₁ f hord'
    have hpath' : ξ' ≫ p₁ ≫ g = spMap ev' ≫ ζ ≫ pullback.fst C.z (spMap C.b) := by
      rw [hζg, ← Category.assoc (spMap ev'), hcomm, Category.assoc]
    rwa [GlobalTheory.TorRef.idlAlong_comap, hpath'])
  refine ⟨x, hx, ?_⟩
  have h1 : Φ.ev y f - Φ.coefT y a c' * Φ.monoT y a ∈
      Ideal.span {Φ.monoT y a} * Ideal.span (Set.range (Φ.t y)) ⊔ maximalIdeal (Φ.V y) ^ e' :=
    (sup_le_sup_left (α := Ideal (Φ.V y)) (Ideal.pow_le_pow_right (le_max_left e' e₁)) _) hlead
  have h2 : Φ.ev y f - x * g₀ ^ D ∈
      Ideal.span {Φ.monoT y a} * Ideal.span (Set.range (Φ.t y)) ⊔ maximalIdeal (Φ.V y) ^ e' :=
    Ideal.mem_sup_right hxe
  have h3 := Ideal.sub_mem _ h1 h2
  convert h3 using 1
  ring

end GlobalTheory.USep
end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair

namespace GlobalTheory.FieldPair

section Transport

variable {k K K' : Type} [Field k] [Field K] [Field K'] {c : k →+* K} {c' : k →+* K'}

theorem Place.contains_map_iff (e : K ≃+* K') (E : Place c) (E' : Place c')
    (hring : ∀ a, e a ∈ E'.ring ↔ a ∈ E.ring) (R : Subring K) :
    E'.Contains (R.map e.toRingHom) ↔ E.Contains R := by
  constructor
  · intro h f hf
    exact (hring f).1 (h _ ⟨f, hf, rfl⟩)
  · rintro h _ ⟨f, hf, rfl⟩
    exact (hring f).2 (h f hf)

theorem Place.isPrimeOf_map_iff (e : K ≃+* K') (E : Place c) (E' : Place c')
    (hring : ∀ a, e a ∈ E'.ring ↔ a ∈ E.ring) (hord : ∀ a, E'.ord (e a) = E.ord a)
    (R : Subring K) : E'.IsPrimeOf (R.map e.toRingHom) ↔ E.IsPrimeOf R := by
  rw [Place.IsPrimeOf, Place.IsPrimeOf, Place.contains_map_iff e E E' hring]
  refine and_congr_right fun _ => ⟨fun h f hf => ?_, fun h f' hf' => ?_⟩
  · obtain ⟨_, ⟨a, ha, rfl⟩, _, ⟨b, hb, rfl⟩, hb0, hbo, hfb⟩ := h (e f) ((hring f).2 hf)
    refine ⟨a, ha, b, hb, fun h0 => hb0 (by simp [h0]), (hord b).symm.trans hbo, e.injective ?_⟩
    simpa using hfb
  · obtain ⟨a, ha, b, hb, hb0, hbo, hfb⟩ := h (e.symm f') ((hring _).1 (by simpa using hf'))
    refine ⟨e a, ⟨a, ha, rfl⟩, e b, ⟨b, hb, rfl⟩, by simpa using hb0, (hord b).trans hbo, ?_⟩
    rw [← hfb]
    simp

theorem adjKlt_congr {n : ℕ} {T : Subring K} {S : Place c} {η : Forms c n} {φ ψ : K →₀ ℚ}
    (hφ : φ 0 = 0) (hψ : ψ 0 = 0)
    (h : ∀ P : Place c, P.ordQ φ = P.ordQ ψ) : AdjKlt c n T S η φ ↔ AdjKlt c n T S η ψ := by
  have h' : ∀ P : Place c, P.disc η φ = P.disc η ψ := fun P => by rw [Place.disc, Place.disc, h]
  simp only [AdjKlt, h', hφ, hψ]

end Transport

theorem klt_of_adjKlt_locModel : GlobalTheory.Published.Principalisation → ∀ {L : Type} [Field L] (c : ℂ →+* L)
    (n : ℕ) (T : Subring L) (x : Fin n → L) (φ : L →₀ ℚ) (f : L) (S : Place c), IsLocModel c T →
    IsIntegrallyClosed T → TrBasis c x → f ∈ T → f ≠ 0 → S.IsPrimeOf T → S.ord f = 1 →
    S.disc (dForm c x) φ = 0 → EffAt c n T (dForm c x) φ →
    AdjKlt c n T S (dForm c x) (φ + Finsupp.single f 1) → Klt c n T (dForm c x) φ := by
  intro hP L _ c n T x φ f S hT hTic hx hfT hf0 hS hSf hSd hEff hAdj
  obtain ⟨Y, hY, p, e, y, hproj, hdim, hc, hy⟩ := GlobalTheory.T.exists_projectiveVariety_of_isLocalRingOfVarietyPoint L c T n x hT hx
  haveI := hY
  haveI : LocallyOfFiniteType p := GlobalTheory.isProjOver_locallyOfFiniteType ℂ Y p hproj
  haveI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian p
  have hc' : ∀ a, e.symm (c a) = Cartier.constFn p a := fun a => by
    rw [← hc a]
    exact e.symm_apply_apply _
  have hyT : T.map e.symm.toRingHom = locRing y := by
    rw [← hy]
    ext z
    simp [Subring.mem_map]
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.T.exists_dvrPlace_equiv_of_ringEquiv_over_constants c (Cartier.constFn p) e.symm hc'
  obtain ⟨hx', -, -, -⟩ := GlobalTheory.T.ringEquiv_transports_varietyPair_data c (Cartier.constFn p) e.symm hc' n x T φ hx
  have hψ0 : (φ + Finsupp.single f 1 : L →₀ ℚ) 0 = 0 := by
    simp [hEff.apply_zero, Finsupp.single_apply, hf0]
  obtain ⟨m, g, hm, hg⟩ := GlobalTheory.T.exists_ordQ_eq_ord_div_of_rational_combination (Cartier.constFn p)
    (Finsupp.mapDomain e.symm (φ + Finsupp.single f 1)) (by
      rw [← map_zero e.symm, Finsupp.mapDomain_apply_of_injective e.symm.injective]
      exact hψ0)

  have hkey : ∀ E : Place c, (Φ E).disc (dForm (Cartier.constFn p) (e.symm ∘ x))
      (Finsupp.mapDomain e.symm (φ + Finsupp.single f 1)) =
      E.disc (dForm c x) (φ + Finsupp.single f 1) := fun E => by
    rw [Place.disc, Place.disc, (hΦ E).2.2.1, (hΦ E).2.2.2 n x hx]
    rfl
  have hψ : ∀ E : Place c, E.disc (dForm c x) (φ + Finsupp.single f 1) =
      E.disc (dForm c x) φ - E.ord f := fun E => by
    simp only [Place.disc, map_add (f := _), Place.ordQ_single]
    ring
  have hordQ : ∀ P : Place (Cartier.constFn p),
      P.ordQ (Finsupp.mapDomain e.symm (φ + Finsupp.single f 1)) =
      P.ordQ (Finsupp.single (g : Y.functionField) (1 / (m : ℚ))) := fun P => by
    rw [hg, Place.ordQ_single]
    ring
  have hdisc : ∀ D : DivOver p, discrep D (dForm (Cartier.constFn p) (e.symm ∘ x)) m g =
      (Φ.symm (placeEquiv p D)).disc (dForm c x) (φ + Finsupp.single f 1) := fun D => by
    rw [← disc_placeEquiv, ← hkey, Φ.apply_symm_apply, Place.disc, Place.disc, hordQ]
  let f' : Y.functionFieldˣ := Units.mk0 (e.symm f) (by simpa using hf0)
  have hord : ∀ D : DivOver p, (D.ord f' : ℚ) = (Φ.symm (placeEquiv p D)).ord f := fun D => by
    rw [← ord_placeEquiv]
    have h := (hΦ (Φ.symm (placeEquiv p D))).2.1 f
    rw [Φ.apply_symm_apply] at h
    exact_mod_cast h

  have hstalk : IsIntegrallyClosed (Y.presheaf.stalk y) := by
    let e₁ : Y.presheaf.stalk y ≃+* locRing y := RingEquiv.ofBijective
      (algebraMap (Y.presheaf.stalk y) Y.functionField).rangeRestrict
      ⟨fun _ _ h => IsFractionRing.injective _ Y.functionField (congrArg Subtype.val h),
        RingHom.rangeRestrict_surjective _⟩
    have : IsIntegrallyClosed (locRing y) := IsIntegrallyClosed.of_equiv
      ((T.equivMapOfInjective e.symm.toRingHom e.symm.injective).trans
        (RingEquiv.subringCongr hyT))
    exact IsIntegrallyClosed.of_equiv e₁.symm
  have hreg : RegAt y (f' : Y.functionField) := by
    rw [← mem_locRing, ← hyT]
    exact ⟨f, hfT, rfl⟩
  have hSprime : (placeEquiv p ((placeEquiv p).symm (Φ S))).IsPrimeOf (locRing y) := by
    rw [Equiv.apply_symm_apply, ← hyT]
    exact (Place.isPrimeOf_map_iff e.symm S (Φ S) (hΦ S).1 (hΦ S).2.1 T).2 hS
  have hSord : ((placeEquiv p).symm (Φ S)).ord f' = 1 := by
    have h := hord ((placeEquiv p).symm (Φ S))
    rw [Equiv.apply_symm_apply, Φ.symm_apply_apply, hSf] at h
    exact_mod_cast h
  have hSdisc : discrep ((placeEquiv p).symm (Φ S)) (dForm (Cartier.constFn p) (e.symm ∘ x)) m g
      = -1 := by
    rw [hdisc, Equiv.apply_symm_apply, Φ.symm_apply_apply, hψ, hSd, hSf]
    norm_num
  have heff : ∀ D : DivOver p, (placeEquiv p D).IsPrimeOf (locRing y) →
      discrep D (dForm (Cartier.constFn p) (e.symm ∘ x)) m g ≤ 0 := by
    intro D hD
    have hE : (Φ.symm (placeEquiv p D)).IsPrimeOf T := by
      refine (Place.isPrimeOf_map_iff e.symm _ (Φ (Φ.symm (placeEquiv p D)))
        (hΦ _).1 (hΦ _).2.1 T).1 ?_
      rw [Φ.apply_symm_apply, hyT]
      exact hD
    have h0 : (0 : ℚ) ≤ (Φ.symm (placeEquiv p D)).ord f := by
      exact_mod_cast ((Φ.symm (placeEquiv p D)).ord_nonneg_iff hf0).2 (hE.1 f hfT)
    rw [hdisc, hψ]
    linarith [hEff.disc_le hE]
  have hadj : AdjKlt (Cartier.constFn p) n (locRing y) (placeEquiv p ((placeEquiv p).symm (Φ S)))
      (dForm (Cartier.constFn p) (e.symm ∘ x)) (Finsupp.single (g : Y.functionField) (1 / (m : ℚ))) := by
    rw [Equiv.apply_symm_apply, ← hyT]
    have h := GlobalTheory.T.kltAlongPlaceNeighbours_ringEquiv c (Cartier.constFn p) e.symm hc' n x T _ S (Φ S) hx (hΦ S).1 hAdj
    exact (adjKlt_congr h.apply_zero (Finsupp.single_eq_of_ne g.ne_zero.symm) hordQ).1 h
  have hmain := GlobalTheory.T.inversion_of_adjunction_proj_alt hP Y p n hproj hdim (e.symm ∘ x) m g f' y ((placeEquiv p).symm (Φ S))
    hx' hm hstalk hreg hSprime hSord hSdisc heff hadj
  refine ⟨hEff.form_ne_zero, hEff.apply_zero, fun E hE => ?_⟩
  have hThr : ((placeEquiv p).symm (Φ E)).Through y := by
    rw [← contains_placeEquiv, Equiv.apply_symm_apply, ← hyT]
    exact (Place.contains_map_iff e.symm E (Φ E) (hΦ E).1 T).2 hE
  have h := hmain _ hThr
  rw [hdisc, hord, Equiv.apply_symm_apply, Φ.symm_apply_apply, hψ] at h
  linarith

end GlobalTheory.FieldPair
end
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.dualAbelianScheme_exists_biduality : GlobalTheory.Published.DualAbelianScheme := by
  first | exact @GlobalTheory.dualAbelianScheme | exact GlobalTheory.dualAbelianScheme | (intros; apply GlobalTheory.dualAbelianScheme <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
open GlobalTheory.ZM GlobalTheory.SiegelTor

open scoped CategoryTheory.Obj
open GlobalTheory.AbDual GlobalTheory.CechPic

namespace GlobalTheory.DualHomPull

theorem exists_dual_hom : ∀ (Y : Scheme.{0}) (A G : Over Y) [GrpObj A] [IsCommMonObj A] [GrpObj G] [IsCommMonObj G] (χ : A ⟶ G) (P'' : LB (G2 G).left), IsAbelianScheme A → IsAbelianScheme G → IsMonHom χ → P''.IsLB → (∃ t : (P''.pull (lift (1 : G ⟶ G) (𝟙 G)).left).Gen, t.IsGen) → (∃ t : (P''.pull (lift (𝟙 G) (1 : G ⟶ G)).left).Gen, t.IsGen) → ∃ (D : Over Y) (_ : GrpObj D) (Q : LB (A ⊗ D).left) (h : A ⟶ D), IsAbelianScheme D ∧ GlobalTheory.AbDual.IsDual A D Q ∧ GlobalTheory.AbDual.IsAdditive (GlobalTheory.AbDual.swap Q) ∧ IsMonHom h ∧ LBIso (P''.pull (χ ⊗ₘ χ).left) (Q.pull (lift (fst A A) (snd A A ≫ h)).left) := by
  intro Y A G _ _ _ _ χ P'' hA hG hχ hP h₁ h₂
  obtain ⟨D, _, Q, hD, -, q, q'⟩ := GlobalTheory.dualAbelianScheme Y A hA
  obtain ⟨a₁, a₂⟩ := GlobalTheory.CubeAxes.additive_of_triv_axes hG hP h₁ h₂
  have eχ : χ ⊗ₘ χ = lift (fst A A ≫ χ) (snd A A ≫ χ) := by ext <;> simp
  rw [eχ]
  have hE : (ev P'' (fst A A ≫ χ) (snd A A ≫ χ)).IsLB := pull_isLB hP _
  have k : ∀ {T : Over Y} (a t : T ⟶ A), evc hE a t = evc hP (a ≫ χ) (t ≫ χ) := fun a t ↦ by
    rw [evc_ev hP _ _ hE, lift_fst_assoc, lift_snd_assoc]
  have b₁ : IsAdditive (ev P'' (fst A A ≫ χ) (snd A A ≫ χ)) := (isAdditive_iff hE).2 fun T a a' t ↦ by
    haveI := hχ
    rw [k, k, k, MonObj.mul_comp]
    exact (isAdditive_iff hP).1 a₁ _ _ _ _
  have b₂ : IsAdditive (swap (ev P'' (fst A A ≫ χ) (snd A A ≫ χ))) :=
    (GlobalTheory.BirigidLift.isAdditive_swap_iff hE).2 fun T a t t' ↦ by
      haveI := hχ
      rw [k, k, k, MonObj.mul_comp]
      exact (GlobalTheory.BirigidLift.isAdditive_swap_iff hP).1 a₂ _ _ _ _
  obtain ⟨x, hx, e⟩ := GlobalTheory.BirigidLift.exists_hom q q'.additive hE b₁ b₂
  exact ⟨D, inferInstance, Q, x, hD, q, q'.additive, hx, (cls_eq_iff hE (pull_isLB q.isLB _)).1 e⟩

end GlobalTheory.DualHomPull
end
