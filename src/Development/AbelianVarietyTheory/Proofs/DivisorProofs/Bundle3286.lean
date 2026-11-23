module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle019
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle022
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle013
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle036
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2702
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3268
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle039
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1465
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3269
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3234
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1464
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1408
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1540
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1496
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2606
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2646
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1618
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1860
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1551
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3270
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1223
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1404
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2605
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle240
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Algebra.Ring.IsFormallyReal
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle063

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.UnitDescent

theorem one_left_pullback {S T : Scheme.{0}} (f : T ⟶ S) (G : Over S) [GrpObj G] :
    letI : (Over.pullback f).Monoidal := (Over.instBraidedPullback (f := f)).toMonoidal
    letI : GrpObj ((Over.pullback f).obj G) := Functor.grpObjObj (F := Over.pullback f)
    (toUnit (Over.mk (𝟙 T)) ≫ η[((Over.pullback f).obj G)]).left ≫ pullback.fst G.hom f =
      f ≫ (1 : Over.mk (𝟙 S) ⟶ G).left := by
  letI : (Over.pullback f).Monoidal := (Over.instBraidedPullback (f := f)).toMonoidal
  letI : GrpObj ((Over.pullback f).obj G) := Functor.grpObjObj (F := Over.pullback f)
  rw [Hom.one_def]
  erw [Functor.obj.η_def]
  have hw : (toUnit (Over.mk (𝟙 T)) ≫ Functor.LaxMonoidal.ε (Over.pullback f)).left ≫
      pullback.snd (𝟙_ (Over S)).hom f = 𝟙 T := by
    simpa using Over.w (toUnit (Over.mk (𝟙 T)) ≫ Functor.LaxMonoidal.ε (Over.pullback f))
  have hb : (toUnit (Over.mk (𝟙 S))).left = 𝟙 S := by
    simpa using Over.w (toUnit (Over.mk (𝟙 S)))
  have hc : pullback.fst (𝟙_ (Over S)).hom f = pullback.snd (𝟙_ (Over S)).hom f ≫ f := by
    have := pullback.condition (f := (𝟙_ (Over S)).hom) (g := f)
    simpa using this
  have hm : ((Over.pullback f).map (η : 𝟙_ (Over S) ⟶ G)).left ≫ pullback.fst G.hom f =
      pullback.fst (𝟙_ (Over S)).hom f ≫ (η : 𝟙_ (Over S) ⟶ G).left := by
    simp only [Over.pullback_map_left, pullback.lift_fst]
  simp only [Over.comp_left, Category.assoc] at hw ⊢
  rw [hm, hc, hb]
  simp only [← Category.assoc] at hw ⊢
  rw [hw]
  simp

theorem unit_descends : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (S : Scheme.{0}) (π : S ⟶ Sp R), IsProper π → Surjective π → IsIntegral S → ∀ (G' : Over S) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ N : Near π G', N.Law → Set.range (1 : Over.mk (𝟙 S) ⟶ G').left ⊆ Set.range N.u → ∃ e : Sp R ⟶ N.U.left, e ≫ N.U.hom = 𝟙 _ ∧ N.Pt (𝟙 S) (π ≫ e) (1 : Over.mk (𝟙 S) ⟶ G').left := by
  intro R _ _ _ hA S π hP hS hI G' _ _ hSA N hL hr
  haveI : IsNoetherianRing R := hA.1
  haveI : IsIntegrallyClosed R := hA.2.2.1
  haveI := N.isOpen
  have hone_w : (1 : Over.mk (𝟙 S) ⟶ G').left ≫ G'.hom = 𝟙 S := by
    simpa using Over.w (1 : Over.mk (𝟙 S) ⟶ G')
  let x₀ := IsOpenImmersion.lift N.u (1 : Over.mk (𝟙 S) ⟶ G').left hr
  have hx₀u : x₀ ≫ N.u = (1 : Over.mk (𝟙 S) ⟶ G').left := IsOpenImmersion.lift_fac _ _ _
  have hx₀s : x₀ ≫ pullback.snd N.U.hom π = 𝟙 S := by
    rw [← N.u_over, ← Category.assoc, hx₀u, hone_w]
  let h := x₀ ≫ pullback.fst N.U.hom π
  have hh : h ≫ N.U.hom = π := by
    simp only [h, Category.assoc, pullback.condition]
    rw [← Category.assoc, hx₀s]
    simp
  obtain ⟨φ, hmon, hφ⟩ := GlobalTheory.T.exists_descentDatum_of_descendedMultiplication R hA S π hP hS hI G' hSA N hL
  let x := (1 : Over.mk (𝟙 (pullback π π)) ⟶ (Over.pullback (pullback.fst π π)).obj G').left
  have hxs : x ≫ pullback.snd G'.hom (pullback.fst π π) = 𝟙 _ := by
    simpa using Over.w (1 : Over.mk (𝟙 (pullback π π)) ⟶ (Over.pullback (pullback.fst π π)).obj G')
  have hxf : x ≫ pullback.fst G'.hom (pullback.fst π π) = pullback.fst π π ≫ (1 : Over.mk (𝟙 S) ⟶ G').left :=
    one_left_pullback _ _
  have hφ1 : x ≫ φ.hom.left =
      (1 : Over.mk (𝟙 (pullback π π)) ⟶ (Over.pullback (pullback.snd π π)).obj G').left := by
    rw [← Over.comp_left]
    congr 1
    rw [Hom.one_def, Hom.one_def, Category.assoc, IsMonHom.one_hom]
  have hprem : N.Pt (x ≫ pullback.snd G'.hom (pullback.fst π π) ≫ pullback.fst π π) (pullback.fst π π ≫ h)
      (x ≫ pullback.fst G'.hom (pullback.fst π π)) := by
    rw [reassoc_of% hxs, hxf]
    exact ⟨pullback.fst π π ≫ x₀, by simp [h], by rw [Category.assoc, hx₀s, Category.comp_id],
      by rw [Category.assoc, hx₀u]⟩
  obtain ⟨y₀, hy1, -, hy3⟩ := hφ _ _ x hprem
  have hsnd : (1 : Over.mk (𝟙 (pullback π π)) ⟶ (Over.pullback (pullback.snd π π)).obj G').left ≫
      pullback.fst G'.hom (pullback.snd π π) = pullback.snd π π ≫ (1 : Over.mk (𝟙 S) ⟶ G').left :=
    one_left_pullback _ _
  rw [← Category.assoc, hφ1, hsnd] at hy3
  have hy : y₀ = pullback.snd π π ≫ x₀ := by
    rw [← cancel_mono N.u, hy3, Category.assoc, hx₀u]
  have heq : pullback.fst π π ≫ h = pullback.snd π π ≫ h := by
    rw [← hy1, hy, Category.assoc]
  have sq : IsPullback π (𝟙 S) (𝟙 (Sp R)) π := IsPullback.of_vert_isIso ⟨by simp⟩
  obtain ⟨e, he, -⟩ := GlobalTheory.T.exists_descent_of_equalised_proper_cover_normal R S (Sp R) S N.U.left π (𝟙 _) π (𝟙 S) hP hS hI inferInstance sq h heq
  obtain ⟨e₁, -, huniq⟩ := GlobalTheory.T.exists_descent_of_equalised_proper_cover_normal R S (Sp R) S (Sp R) π (𝟙 _) π (𝟙 S) hP hS hI inferInstance sq π
    pullback.condition
  refine ⟨e, ?_, x₀, he.symm, hx₀s, hx₀u⟩
  rw [huniq (e ≫ N.U.hom) (show π ≫ e ≫ N.U.hom = π by rw [← Category.assoc, he, hh]),
    huniq (𝟙 _) (show π ≫ 𝟙 _ = π by simp)]

end GlobalTheory.UnitDescent
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.TwFam

theorem _root_.GlobalTheory.T.multiplier_power_mul_pullback_small_family : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D : DegData R (maximalIdeal R)), ∀ (a a' : D.toPre.P.A ⟶ D.toPre.P.A) (h h' : D.toPre.X →+ D.toPre.X), EndData D.toPre a a' h h' → ∀ (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal R) D A G), ∀ b, FormalEnd U.toUnifPre a h' b → ∀ (N k : ℕ) (g : ∀ β, SecT D.toPre a N (-1) β) (ρ : ∀ β, SecT D.toPre a 0 k β), Small (maximalIdeal R) (w := id) g → Small (maximalIdeal R) (w := id) ρ → TFE h h' g → TFE h h' ρ → ∃ F : ∀ β, SecT D.toPre a ((N * k : ℕ) : ℤ) 0 β, Small (maximalIdeal R) (w := id) F ∧ TFE h h' F ∧ ∀ (e : ℕ) (τ : SecE U.toUnifPre (b e) N (-1)) (τ' : SecE U.toUnifPre (b e) 0 k), TExp U.toUnifPre τ (w := id) g → TExp U.toUnifPre τ' (w := id) ρ → ∃ τ'' : SecE U.toUnifPre (b e) ((N * k : ℕ) : ℤ) 0, (∀ (Z : Scheme.{0}) (x : Z ⟶ (thickObj R (maximalIdeal R) e G).left) (z : Z) (J'), Good U.LG.L z J' → sval τ'' x z J' = sval τ x z J' ^ k * sval τ' x z J') ∧ TExp U.toUnifPre τ'' (w := id) F := by
  first | exact @GlobalTheory.ZmPow.pow_mul_small | exact GlobalTheory.ZmPow.pow_mul_small | (intros; apply GlobalTheory.ZmPow.pow_mul_small <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UMin

theorem exists_nbhd_thetaMap : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (L : LB G.left) (ρ : LB.Gen (L.pull (eSec G))), L.IsLB → ρ.IsGen →
    ∀ (g m n : ℕ) (o : Type) [CommRing o] (X : Scheme.{0}) (s : X ⟶ Sp o) (q : X ⟶ S), Odd m → 3 ≤ m → IsUnit (m : o) → n + 1 = m ^ (4 * g) →
    (∀ (R : Type) [CommRing R] (x : Sp R ⟶ X), PolFib G L g (x ≫ q)) →
    ∀ (U : X.affineOpens), IsDomain Γ(X, U) → IsNoetherianRing Γ(X, U) → IsIntegrallyClosed Γ(X, U) → CharZero Γ(X, U) →
    ∀ x ∈ (U : X.Opens), ∃ (W : X.Opens) (h : W.toScheme ⟶ PSpace o n), x ∈ W ∧ h ≫ PSpace.str o n = W.ι ≫ s ∧ ThMap G L ρ m (W.ι ≫ q) h := by
  intro S G _ _ L ρ hL hρ g m n o _ X s q hmo hm3 hu hn hP U hD hN hI hC x hx
  let R : Type := Γ(X, U)
  have hU : IsAffineOpen (U : X.Opens) := U.2

  let β : o →+* R := (Spec.preimage (hU.fromSpec ≫ s)).hom
  have hβ : spMap β = hU.fromSpec ≫ s := Spec.map_preimage _
  let p : PrimeSpectrum R := hU.primeIdealOf ⟨x, hx⟩
  obtain ⟨r, hr, θ, hθ⟩ := GlobalTheory.T.exists_basicOpen_generating_section_all_fibres S G L hL g R (hU.fromSpec ≫ q) (hP R hU.fromSpec) p
  let Rr := Localization.Away r
  have hr0 : r ≠ 0 := fun h => hr (h ▸ p.asIdeal.zero_mem)
  have hle : Submonoid.powers r ≤ nonZeroDivisors R := powers_le_nonZeroDivisors_of_noZeroDivisors hr0
  haveI : IsDomain Rr := IsLocalization.isDomain_localization hle
  haveI : IsNoetherianRing Rr := IsLocalization.isNoetherianRing (Submonoid.powers r) Rr hN
  haveI : IsIntegrallyClosed Rr := isIntegrallyClosed_of_isLocalization Rr _ hle
  have hinj : Function.Injective (algebraMap R Rr) := IsLocalization.injective Rr hle
  haveI : CharZero Rr := charZero_of_injective_algebraMap hinj
  let β' : o →+* Rr := (algebraMap R Rr).comp β
  have hu' : IsUnit (m : Rr) := by
    have := hu.map β'
    simpa using this
  have hP' : PolFib G L g (spMap (algebraMap R Rr) ≫ hU.fromSpec ≫ q) := by
    have := hP Rr (spMap (algebraMap R Rr) ≫ hU.fromSpec)
    simpa [Category.assoc] using this
  obtain ⟨f, hf, hT⟩ := GlobalTheory.T.exists_thetaMap_affineNormalBase_universalGenerator S G L ρ hL hρ g m n o Rr β' (spMap (algebraMap R Rr) ≫ hU.fromSpec ≫ q) θ
    hmo hm3 hu' hn hP' hθ

  let Wo : X.Opens := X.basicOpen r
  have hW : IsAffineOpen Wo := hU.basicOpen r
  have hxW : x ∈ Wo := by
    have h1 : hU.fromSpec p ∈ X.basicOpen r := by
      show p ∈ hU.fromSpec ⁻¹ᵁ X.basicOpen r
      rw [hU.fromSpec_preimage_basicOpen]; exact hr
    rwa [hU.fromSpec_primeIdealOf] at h1
  have hle' : Wo ≤ (U : X.Opens) := X.basicOpen_le r
  let res : R →+* Γ(X, Wo) := (X.presheaf.map (homOfLE hle').op).hom
  have hres : IsUnit (res r) := RingedSpace.isUnit_res_basicOpen X.toRingedSpace r
  let lft : Rr →+* Γ(X, Wo) := IsLocalization.Away.lift r hres
  have hlft : lft.comp (algebraMap R Rr) = res := IsLocalization.Away.lift_comp r hres
  let e : Wo.toScheme ⟶ Sp Rr := hW.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom lft)
  have he : e ≫ spMap (algebraMap R Rr) ≫ hU.fromSpec = Wo.ι := by
    have : Spec.map (CommRingCat.ofHom lft) ≫ spMap (algebraMap R Rr) =
        Spec.map (X.presheaf.map (homOfLE hle').op) := by
      rw [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hlft]
      rfl
    simp only [e, Category.assoc]
    rw [reassoc_of% this, hU.map_fromSpec hW, hW.isoSpec_hom_fromSpec]
  refine ⟨Wo, e ≫ f, hxW, ?_, ?_⟩
  · rw [Category.assoc, hf, show spMap β' = spMap (algebraMap R Rr) ≫ spMap β from by
      rw [spMap, spMap, spMap, ← Spec.map_comp]; rfl, hβ, ← he]
    simp only [Category.assoc]
  · intro K _ x' c hc
    have hc' : HasTh G L ρ m ((x' ≫ e) ≫ spMap (algebraMap R Rr) ≫ hU.fromSpec ≫ q) c := by
      have : (x' ≫ e) ≫ spMap (algebraMap R Rr) ≫ hU.fromSpec ≫ q = x' ≫ Wo.ι ≫ q := by
        rw [← he]; simp only [Category.assoc]
      rw [this]; exact hc
    have := hT K (x' ≫ e) c hc'
    simpa [Category.assoc] using this

end GlobalTheory.UMin
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.fibreSection_extends_nonzero_of_integral_thetaConstants : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S : Scheme.{0}) (t : SAB H S) (g m N : ℕ) (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [CharZero R] (χ : Sp R ⟶ S) (θ : SecAt t.G t.PP.L (spMap (algebraMap R (FractionRing R)) ≫ χ)) (pt : Fin N → (Over.mk (spMap (algebraMap R (FractionRing R)) ≫ χ) ⟶ t.G)) (c : Fin N → R), Odd m → 3 ≤ m → IsUnit (m : R) → PolFib t.G t.PP.L g (spMap (algebraMap R (FractionRing R)) ≫ χ) → ThList t.G t.PP.L t.PP.rig m _ θ pt (fun a => algebraMap R (FractionRing R) (c a)) → (∃ a, IsUnit (c a)) → ∃ σ : SecAt t.G t.PP.L χ, SecM.ofSec t.G (SecAt.pull t.G t.PP.L σ (algebraMap R (FractionRing R))) = SecM.ofSec t.G θ ∧ ∀ s : Sp R, ∃ z : (Over.mk χ ⊗ t.G).left, (fst (Over.mk χ) t.G).left z = s ∧ z ∈ nonzeroLocus σ := by
  first | exact @GlobalTheory.UMin.OmExt.om_ext | exact GlobalTheory.UMin.OmExt.om_ext | (intros; apply GlobalTheory.UMin.OmExt.om_ext <;> assumption)
end

section

open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix
set_option autoImplicit false

namespace GlobalTheory.GoodTop

theorem hasInt_cut_topDens_patch : ∀ {F : Type} [Field F] {σ : F →+* ℂ} {X : Var F} {m : ℕ} (E : Fr (ratOf X) (fun _ : Unit => m) 0) (O : X.X.Opens) (H H₀ : Mat (fun _ : Unit => m) X.Fn → CxPts X.str σ → Mat (fun _ : Unit => m) ℂ), IsMetricOn E O H → IsMetricOn E ⊤ H₀ → ∀ {e : OpenPartialHomeomorph (CxPts X.str σ) (V X.dim)} {S : Finset (Fin X.dim)} {A : Mat (fun _ : Unit => m) X.Fn} {W : Set (CxPts X.str σ)} {c : ℝ}, GoodPatch E O H e S A W c → ∀ {ρ : CxPts X.str σ → ℝ}, (∀ y, CInfAt ρ y) → tsupport ρ ⊆ W → HasInt (fun c : AlgChart X.str σ X.dim => c.e) (fun c y => ρ y * topDens E H₀ c y) (ptsIn X.str σ ⊤) ((Real.pi ^ X.dim)⁻¹ * (∫ v in e '' W, (ρ (e.symm v) : ℂ) * mixTop fun _ => curvAt (fun v => H₀ A (e.symm v) ()) v).re) := by
  intro F _ σ X m E O H H₀ hH hH₀ e S A W c hp ρ hρ hsupp
  haveI := CxPts.secondCountableTopology_of_isProjOver σ X.isProjOver
  have hcont : Continuous ρ := continuous_iff_continuousAt.2 fun y => (hρ y).continuousAt
  have htop : ptsIn X.str σ ⊤ = Set.univ := Set.eq_univ_of_forall fun _ => mem_ptsIn_top
  set f : V X.dim → ℂ := fun v => (ρ (e.symm v) : ℂ) * mixTop fun _ => curvAt (fun v => H₀ A (e.symm v) ()) v with hf
  set g : V X.dim → ℝ := fun v => (Real.pi ^ X.dim)⁻¹ * (f v).re with hg
  obtain ⟨hUo, -, hK⟩ := GlobalTheory.T.goodPatch_chart_image_properties E O H hp

  have hfi : IntegrableOn f (e '' W) := by
    refine GlobalTheory.T.integrableOn_cutoff_topChernForm_smoothGram (e '' W) (e '' tsupport ρ) (fun v => H₀ A (e.symm v) ()) (fun v => ρ (e.symm v)) hUo
      (hK _ (isClosed_tsupport ρ) hsupp) (Set.image_mono hsupp) ?_ ?_ ?_
    · rintro _ ⟨z, hz, rfl⟩
      exact GlobalTheory.T.gramMatrix_smooth_isUnit_in_holomorphicChart E ⊤ H₀ hH₀ hp.holo mem_ptsIn_top (hp.sub hz) (hp.frame z hz)
    · rintro _ ⟨z, hz, rfl⟩
      exact (GlobalTheory.T.contDiffAt_holomorphicComplexChart_of_smoothAt hp.holo (hp.sub hz) (hρ z)).contDiffWithinAt
    · rintro _ ⟨z, hz, rfl⟩ hK'
      rw [e.left_inv (hp.sub hz)]
      by_contra h0
      exact hK' ⟨z, subset_tsupport ρ h0, rfl⟩
  have hgi : IntegrableOn g (e '' W) := hfi.re.const_mul _
  have key := GlobalTheory.T.topFormIntegral_of_support_in_holomorphicChart (fun c : AlgChart X.str σ X.dim => c.e)
    (fun i j => GlobalTheory.T.differentiableOn_holomorphicChart_trans_etaleChart i.holo j) (fun y => AlgChart.exists_mem_source y)
    (S := ptsIn X.str σ ⊤) (isOpen_ptsIn _).measurableSet (d := fun c y => ρ y * topDens E H₀ c y) e W g
    hp.isOpen hp.sub (fun j => GlobalTheory.T.differentiableOn_holomorphicChart_trans_etaleChart hp.holo j) (GlobalTheory.T.continuous_mul_top_chern_form_isTopDegree E ⊤ H₀ hH₀ hcont) ?_ ?_
    (by rw [htop, Set.univ_inter]; exact hgi)
  · rw [htop, Set.univ_inter] at key
    convert key using 1
    rw [hg, integral_const_mul]
    congr 1
    exact (integral_re hfi).symm
  · intro i y _ hyW _
    have : ρ y = 0 := by
      by_contra h0
      exact hyW (hsupp (subset_tsupport ρ h0))
    simp [this]
  · intro j y _ hyW hyj
    have ht := GlobalTheory.T.top_chern_density_holomorphic_chart_etale E ⊤ H₀ hH₀ hp.holo j mem_ptsIn_top (hp.sub hyW) hyj (hp.frame y hyW)
    simp only [hg, hf, e.left_inv (hp.sub hyW), Complex.re_ofReal_mul]
    rw [← mul_assoc, mul_comm _ (ρ y), mul_assoc, ht]
    ring

end GlobalTheory.GoodTop
end

section

open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

theorem _root_.GlobalTheory.T.transgression_term_density_good_patch : ∀ {F : Type} [Field F] {σ : F →+* ℂ} {X : Var F} {m : ℕ} (E : Fr (ratOf X) (fun _ : Unit => m) 0) (O : X.X.Opens) (H H₀ : Mat (fun _ : Unit => m) X.Fn → CxPts X.str σ → Mat (fun _ : Unit => m) ℂ), IsMetricOn E O H → IsMetricOn E ⊤ H₀ → ∀ {e : OpenPartialHomeomorph (CxPts X.str σ) (V X.dim)} {S : Finset (Fin X.dim)} {A : Mat (fun _ : Unit => m) X.Fn} {W : Set (CxPts X.str σ)} {c : ℝ}, GoodPatch E O H e S A W c → ∀ {ρ : CxPts X.str σ → ℝ}, (∀ y, CInfAt ρ y) → tsupport ρ ⊆ W → HasInt (fun c : AlgChart X.str σ X.dim => c.e) (corrDens E H₀ H ρ) (ptsIn X.str σ O) ((Real.pi ^ X.dim)⁻¹ * (∫ v in offHyp S (e '' W), corrC (fun v => ρ (e.symm v)) (fun v => H₀ A (e.symm v) ()) (fun v => H A (e.symm v) ()) v).re) := by
  first | exact @GlobalTheory.GoodTop.hasInt_corrDens_of_goodPatch | exact GlobalTheory.GoodTop.hasInt_corrDens_of_goodPatch | (intros; apply GlobalTheory.GoodTop.hasInt_corrDens_of_goodPatch <;> assumption)
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

namespace GlobalTheory.HSAmp.GoodH

variable {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k}

theorem mem_H_of_eq (P : Pair p) {a a' b b' : ℤ} {f : X.functionField} (ha : a = a') (hb : b = b')
    (h : f ∈ P.H a b) : f ∈ P.H a' b' := by
  subst ha hb; exact h

theorem nu_nonneg (P : Pair p) (a b : ℤ) (σ : k →+* ℂ) (y : CxPts p σ) (f : X.functionField) : 0 ≤ P.nu a b σ y f := by
  rw [Pair.nu]; positivity

theorem mono_mem {D : ℕ} (P : Pair p) (e : ℕ) (x : Fin (D + 1) → X.functionField) (hx : ∀ l, x l ∈ P.H e 0)
    (a b : ℤ) (g : X.functionField) (hg : g ∈ P.H a b) (α : Fin (D + 1) → ℕ) (S : Finset (Fin (D + 1))) :
    (∏ l ∈ S, x l ^ α l) * g ∈ P.H ((e : ℤ) * ((∑ l ∈ S, α l : ℕ) : ℤ) + a) b ∧
      ∀ (σ : k →+* ℂ) (y : CxPts p σ), P.nu ((e : ℤ) * ((∑ l ∈ S, α l : ℕ) : ℤ) + a) b σ y ((∏ l ∈ S, x l ^ α l) * g) =
        (∏ l ∈ S, P.nu e 0 σ y (x l) ^ α l) * P.nu a b σ y g := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty, Finset.sum_empty, one_mul, Nat.cast_zero, mul_zero, zero_add]
    exact ⟨hg, fun _ _ => trivial⟩
  | @insert j S hj ih =>
    obtain ⟨hp1, hp2⟩ := GlobalTheory.VolBr.NuPow.pow_mem_H_and_nu_pow k X p P (e : ℤ) 0 (x j) (hx j) (α j)
    obtain ⟨hm1, hm2⟩ := GlobalTheory.VolBr.NuMul.mul_mem_H_and_nu_mul k X p P _ _ _ _ _ _ hp1 ih.1
    have ea : ((α j : ℕ) : ℤ) * (e : ℤ) + ((e : ℤ) * ((∑ l ∈ S, α l : ℕ) : ℤ) + a) =
        (e : ℤ) * ((∑ l ∈ insert j S, α l : ℕ) : ℤ) + a := by
      rw [Finset.sum_insert hj]; push_cast; ring
    have eb : ((α j : ℕ) : ℤ) * 0 + b = b := by ring
    rw [ea, eb] at hm1 hm2
    have ep : (∏ l ∈ insert j S, x l ^ α l) * g = x j ^ α j * ((∏ l ∈ S, x l ^ α l) * g) := by
      rw [Finset.prod_insert hj, mul_assoc]
    rw [ep]
    refine ⟨hm1, fun σ y => ?_⟩
    rw [hm2, hp2, ih.2, Finset.prod_insert hj, mul_assoc]

end GlobalTheory.HSAmp.GoodH

namespace GlobalTheory.HSAmp.GoodH

theorem goodFam_H : GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ),
    IsArithVar p D → ∀ (P : Pair p), IsAmpleLB P.L.B → GoodFam P D (gdeg P.L D / D.factorial) fun m => P.H m 1 := by
  intro hAr k _ X _ p D hX P hL
  obtain ⟨e, x, hx⟩ := GlobalTheory.T.exists_basepointFreeSectionTuple_ample_arith k X p D hX P hL
  have he : 0 < e := hx.pos

  have hup : ∀ s : ℕ, ∃ c : ℕ, ∀ q : ℕ, (P.H ((e * q + s : ℕ) : ℤ) 1).FG ∧
      Module.finrank ℤ (P.H ((e * q + s : ℕ) : ℤ) 1) ≤
        Module.finrank (ratF x) X.functionField * (q + c + D).choose D := by
    intro s
    obtain ⟨c, C, -, h⟩ := GlobalTheory.T.arithHilbertSamuel_upperBound_count_rank_ample k X p D hX P hL e x hx (s : ℤ) 1
    refine ⟨c, fun q => ?_⟩
    have e1 : ((e * q + s : ℕ) : ℤ) = (e : ℤ) * (q : ℤ) + (s : ℤ) := by push_cast; ring
    rw [e1]
    exact ⟨(h q).1, (h q).2.1⟩

  have hlow : ∀ s : ℕ, ∃ c : ℕ, ∀ q : ℕ, Module.finrank (ratF x) X.functionField * (q + D).choose D ≤
      Module.finrank ℤ (P.H ((e * (q + c) + s : ℕ) : ℤ) 1) := by
    intro s
    obtain ⟨c, C, -, h⟩ := GlobalTheory.T.arithHilbertSamuel_lowerBound_count_rank_ample k X p D hX P hL e x hx (s : ℤ) 1
    obtain ⟨c', hc'⟩ := hup s
    refine ⟨c, fun q => ?_⟩
    obtain ⟨v, hv, hli⟩ := (h q).1
    have e1 : ((e * (q + c) + s : ℕ) : ℤ) = (e : ℤ) * ((q + c : ℕ) : ℤ) + (s : ℤ) := by push_cast; ring
    have hfg := (hc' (q + c)).1
    rw [e1] at hfg ⊢
    haveI : Module.Finite ℤ (P.H ((e : ℤ) * ((q + c : ℕ) : ℤ) + (s : ℤ)) 1) :=
      Module.Finite.iff_addGroup_fg.2 ((AddGroup.fg_iff_addSubgroup_fg _).2 hfg)
    let w : Fin (Module.finrank (ratF x) X.functionField * (q + D).choose D) →
        P.H ((e : ℤ) * ((q + c : ℕ) : ℤ) + (s : ℤ)) 1 := fun i => ⟨v i, hv i⟩
    have hw : LinearIndependent ℤ w :=
      LinearIndependent.of_comp (P.H ((e : ℤ) * ((q + c : ℕ) : ℤ) + (s : ℤ)) 1).subtype.toIntLinearMap hli
    simpa using hw.fintype_card_le_finrank
  have hrank := GlobalTheory.T.tendsto_div_pow_of_choose_bounds D e (Module.finrank (ratF x) X.functionField)
    (fun m => Module.finrank ℤ (P.H (m : ℤ) 1)) he (fun s _ => by
      obtain ⟨c, hc⟩ := hlow s
      obtain ⟨c', hc'⟩ := hup s
      exact ⟨c, c', fun q => ⟨hc q, (hc' q).2⟩⟩)
  have hdeg := GlobalTheory.T.finrank_functionField_quotientSubfield_eq_degree hAr k X p D hX P hL e x hx
  have hg : (Module.finrank (ratF x) X.functionField : ℝ) / ((e : ℝ) ^ D * D.factorial) = gdeg P.L D / D.factorial := by
    have : (e : ℝ) ^ D ≠ 0 := pow_ne_zero _ (by exact_mod_cast he.ne')
    rw [hdeg]
    exact mul_div_mul_left _ _ this

  have hkey : ∀ s : ℕ, ∃ C : ℝ, 1 ≤ C ∧ ∀ q : ℕ, 1 ≤ e * q + s →
      P.H ((e * q + s : ℕ) : ℤ) 1 ≤
        AddSubgroup.closure (ballIn P (P.H ((e * q + s : ℕ) : ℤ) 1) ((e * q + s : ℕ) : ℤ) 1 (C ^ (e * q + s))) := by
    intro s
    classical
    obtain ⟨c, w, Cr, -, hrep⟩ := GlobalTheory.T.sections_eq_sum_aeval_boundedIntCoeff_ample k X p D hX P hL e x hx (s : ℤ) 1
    let Λ : ℕ → AddSubgroup X.functionField := fun q => P.H ((e : ℤ) * (q : ℤ) + (s : ℤ)) 1
    have hmul : ∀ q l, ∀ f ∈ Λ q, x l * f ∈ Λ (q + 1) := by
      intro q l f hf
      have h := (GlobalTheory.VolBr.NuMul.mul_mem_H_and_nu_mul k X p P _ _ _ _ _ _ (hx.mem l) hf).1
      show x l * f ∈ P.H _ 1
      exact mem_H_of_eq P (by push_cast; ring) (by ring) h
    have hrepr : ∀ q, ∀ f ∈ Λ q, ∃ T : Fin (Module.finrank (ratF x) X.functionField) → MvPolynomial (Fin (D + 1)) ℤ,
        (∀ i, (T i).IsHomogeneous (q + c)) ∧ f = ∑ i, MvPolynomial.aeval x (T i) * w i := by
      intro q f hf
      obtain ⟨T, h1, h2, -⟩ := hrep q f hf
      exact ⟨T, h1, h2⟩
    obtain ⟨G, hG, hcl⟩ := GlobalTheory.T.exists_finite_homogeneous_generators_graded_subgroup X.functionField D c x _ w Λ hmul hrepr
    have hb : ∀ (a b : ℤ) (f : X.functionField), f ∈ P.H a b → ∃ C : ℝ, 0 ≤ C ∧ ∀ σ y, P.nu a b σ y f ≤ C := by
      intro a b f hf
      obtain ⟨C, hC⟩ := ((GlobalTheory.T.continuous_hermSectionValue_mul_conj_and_norm_bounded k X p D hX P a b).2 f hf).2
      exact ⟨|C|, abs_nonneg _, fun σ y => (hC σ y).trans (le_abs_self _)⟩
    choose Cx hCx0 hCx using fun l => hb _ _ _ (hx.mem l)
    have hbG : ∀ g : ℕ × X.functionField, ∃ C : ℝ, 0 ≤ C ∧
        (g ∈ G → ∀ σ y, P.nu ((e : ℤ) * (g.1 : ℤ) + s) 1 σ y g.2 ≤ C) := by
      intro g
      by_cases hg : g ∈ G
      · obtain ⟨C, hC0, hC⟩ := hb _ _ _ (hG g hg)
        exact ⟨C, hC0, fun _ => hC⟩
      · exact ⟨0, le_rfl, fun h => absurd h hg⟩
    choose Cg hCg0 hCg using hbG
    have hC1 : 1 ≤ 1 + ∑ l, Cx l := le_add_of_nonneg_right (Finset.sum_nonneg fun l _ => hCx0 l)
    have hC2 : 1 ≤ 1 + ∑ g ∈ G, Cg g := le_add_of_nonneg_right (Finset.sum_nonneg fun g _ => hCg0 g)
    have hxl : ∀ l σ y, P.nu e 0 σ y (x l) ≤ 1 + ∑ l, Cx l := fun l σ y => (hCx l σ y).trans (by
      have := Finset.single_le_sum (fun j _ => hCx0 j) (Finset.mem_univ l); linarith)
    have hgl : ∀ g ∈ G, ∀ σ y, P.nu ((e : ℤ) * (g.1 : ℤ) + s) 1 σ y g.2 ≤ 1 + ∑ g ∈ G, Cg g :=
      fun g hg σ y => (hCg g hg σ y).trans (by
        have := Finset.single_le_sum (fun j _ => hCg0 j) hg; linarith)
    refine ⟨(1 + ∑ l, Cx l) * (1 + ∑ g ∈ G, Cg g), one_le_mul_of_one_le_of_one_le hC1 hC2, fun q hq => ?_⟩
    have e1 : ((e * q + s : ℕ) : ℤ) = (e : ℤ) * (q : ℤ) + (s : ℤ) := by push_cast; ring
    rw [e1]
    refine (hcl q).trans (AddSubgroup.closure_mono ?_)
    rintro f ⟨g, hg, α, hα, rfl⟩
    obtain ⟨h1, h2⟩ := mono_mem P e x hx.mem ((e : ℤ) * (g.1 : ℤ) + s) 1 g.2 (hG g hg) α Finset.univ
    have ea : (e : ℤ) * ((∑ l, α l : ℕ) : ℤ) + ((e : ℤ) * (g.1 : ℤ) + s) = (e : ℤ) * (q : ℤ) + (s : ℤ) := by
      rw [← hα]; push_cast; ring
    rw [ea] at h1 h2
    refine ⟨h1, fun σ y => ?_⟩
    rw [h2]
    have hnu0 : ∀ l, 0 ≤ P.nu e 0 σ y (x l) := fun l => nu_nonneg P _ _ σ y _
    have hqe : q ≤ e * q := Nat.le_mul_of_pos_left q he
    have hsum : ∑ l, α l ≤ e * q + s := by omega
    calc (∏ l, P.nu e 0 σ y (x l) ^ α l) * P.nu ((e : ℤ) * (g.1 : ℤ) + s) 1 σ y g.2
        ≤ (∏ l, (1 + ∑ l, Cx l) ^ α l) * (1 + ∑ g ∈ G, Cg g) :=
          mul_le_mul (Finset.prod_le_prod₀ (fun l _ => pow_nonneg (hnu0 l) _)
            fun l _ => pow_le_pow_left₀ (hnu0 l) (hxl l σ y) _) (hgl g hg σ y) (nu_nonneg P _ _ σ y _)
            (Finset.prod_nonneg fun _ _ => pow_nonneg (by linarith) _)
      _ = (1 + ∑ l, Cx l) ^ (∑ l, α l) * (1 + ∑ g ∈ G, Cg g) := by rw [Finset.prod_pow_eq_pow_sum]
      _ ≤ (1 + ∑ l, Cx l) ^ (e * q + s) * (1 + ∑ g ∈ G, Cg g) ^ (e * q + s) :=
          mul_le_mul (pow_le_pow_right₀ hC1 hsum) (le_self_pow₀ hC2 (by omega)) (by linarith)
            (pow_nonneg (by linarith) _)
      _ = ((1 + ∑ l, Cx l) * (1 + ∑ g ∈ G, Cg g)) ^ (e * q + s) := (mul_pow _ _ _).symm
  choose Cs hCs1 hCs using hkey
  refine ⟨fun m => le_rfl, fun m => ?_, ⟨∑ s ∈ Finset.range e, Cs s, ?_, fun m hm => ?_⟩, ?_⟩
  · obtain ⟨c, hc⟩ := hup (m % e)
    have h := (hc (m / e)).1
    rw [Nat.div_add_mod] at h
    exact h
  · exact (hCs1 0).trans (Finset.single_le_sum (fun j _ => zero_le_one.trans (hCs1 j)) (Finset.mem_range.2 he))
  · have hs := Nat.mod_lt m he
    have h := hCs (m % e) (m / e) (by rw [Nat.div_add_mod]; exact hm)
    rw [Nat.div_add_mod] at h
    have hle : Cs (m % e) ≤ ∑ s ∈ Finset.range e, Cs s :=
      Finset.single_le_sum (fun j _ => zero_le_one.trans (hCs1 j)) (Finset.mem_range.2 hs)
    refine h.trans (AddSubgroup.closure_mono ?_)
    rintro f ⟨hf, hf'⟩
    exact ⟨hf, fun σ y => (hf' σ y).trans (pow_le_pow_left₀ (zero_le_one.trans (hCs1 _)) hle _)⟩
  · rw [← hg]
    exact hrank

end GlobalTheory.HSAmp.GoodH
end
end
