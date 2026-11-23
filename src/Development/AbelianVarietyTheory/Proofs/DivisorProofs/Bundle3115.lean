module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle066
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle065
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2719
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2917
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2791
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2900
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle680
public import Development.AbelianVarietyTheory.Definitions.Divisors.RigidForFan
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2729
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2883
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2861
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3045
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CohomologyLogDerivativeAdjointEndomorphisms
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle022
public import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsLocalizedModuleResBasicOpenOfQcqs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3046
public import Mathlib.AlgebraicGeometry.QuasiAffine
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2820
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3043
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3044
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle229
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2771
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle234
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2723
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2662
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2672
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3048
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
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTorPartTorusExtension
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Mathlib.Tactic.Polynomial.Basic
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle532
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle012

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.TorusPart
open Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Poinc.FibLat GlobalTheory.Poinc.Eq8

noncomputable section
namespace GlobalTheory.Poinc.FibMatrix

theorem main : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (l : u.Lab) (W : Matrix (Fin 8) (Fin 8) ℤ), PosW W → ∀ (X₀ : Type) [AddCommGroup X₀] (β : LinearMap.BilinForm ℤ X₀), (∀ a b, β a b = β b a) → (∀ a, a ≠ 0 → 0 < β a a) → ∀ sc : ℝ, 0 < sc → ∀ j : u.D.toPre.X ≃+ (Fin 8 → X₀), (∀ χ, l.q χ = sc * (qW W β (j χ) : ℤ)) → ∀ (e : ρ.P.A ⟶ ρ.P.A) (E E' : Matrix (Fin 8) (Fin 8) ℤ), (W + W.transpose) * E' = E.transpose * (W + W.transpose) → (∀ (m : ℕ) (pk pk' : QkPt u.D.toPre (PadicAlgCl p) m) (x x' : TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A), 1 ≤ m → QkToAkU u.U.toUnifPre (PadicAlgCl p) m pk x → QkToAkU u.U.toUnifPre (PadicAlgCl p) m pk' x' → x'.left ≫ u.φ = x.left ≫ u.φ ≫ e.left → CongMod m (j pk'.y) (fun a => ∑ b, E a b • j pk.y b)) → ∀ (F : u.G ⟶ u.G) (eA : u.A.A ⟶ u.A.A), IsMonHom F → eA.left ≫ u.φ = u.φ ≫ e.left → eA.left ≫ genMap u.U = genMap u.U ≫ F.left → ∀ m : u.D.toPre.X →+ u.D.toPre.X, EndChar u.U F m → ∀ χ, j (m χ) = fun a => ∑ b, E' a b • j χ b := by
  intro o Ω _ _ _ S ρ p _ y₀ u l W hW X₀ _ β hβs hβp sc hsc j hq e E E' hEE hlab F eA hF heA hgen m hm χ
  have hCZ : CharZero u.V :=
    RingHom.charZero ((algebraMap (FractionRing u.V) (PadicAlgCl p)).comp (algebraMap u.V (FractionRing u.V)))
  have hBase : GlobalTheory.Mum.Base u.V := ⟨⟨inferInstance, inferInstance, inferInstance, u.complete⟩, hCZ⟩
  let Em : (Fin 8 → X₀) →+ (Fin 8 → X₀) :=
    { toFun := fun y a => ∑ b, E a b • y b
      map_zero' := by ext; simp
      map_add' := fun y y' => by ext; simp [smul_add, Finset.sum_add_distrib] }
  have hEm : ∀ y, Em y = fun a => ∑ b, E a b • y b := fun _ => rfl
  let s : u.D.toPre.X →+ u.D.toPre.X := (j.symm.toAddMonoidHom.comp Em).comp j.toAddMonoidHom
  have hs : ∀ x, j (s x) = Em (j x) := fun x => by simp [s]
  have hlab' : ∀ (k : ℕ) (pk pk' : QkPt u.D.toPre (PadicAlgCl p) k) (x x' : TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A),
      1 ≤ k → QkToAkU u.U.toUnifPre (PadicAlgCl p) k pk x → QkToAkU u.U.toUnifPre (PadicAlgCl p) k pk' x' →
      x'.left = x.left ≫ eA.left → CongMod k pk'.y (s pk.y) := by
    intro k pk pk' x x' hk hx hx' hxx
    obtain ⟨w, hw⟩ := hlab k pk pk' x x' hk hx hx' (by rw [hxx, Category.assoc, heA])
    refine ⟨j.symm w, j.injective ?_⟩
    rw [map_add (f := _), map_nsmul, AddEquiv.apply_symm_apply, hs, hw, hEm]
  have hT := GlobalTheory.T.labelCongruence_endo_all_algClosed_fields o Ω S ρ p y₀ u eA s hlab'
  haveI : Mono (jK u.V) := GlobalTheory.PolDeg.Wit.mono_jK
  haveI : Mono (genMap u.U) := by unfold genMap; infer_instance
  have hTor := GlobalTheory.Poinc.TorEnd.torMatch_of_endChar u.V hBase u.G u.semi u.D u.A u.U F hF m hm
  have hmain := GlobalTheory.TauFormHom.main u.V hBase inferInstance u.G u.semi u.D u.A u.U u.G u.semi u.D u.A u.U F hF m s hTor
    (by
      intro F' _ _ _ k hk q q' a a' hqa hqa' haa
      have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.2 (by rintro rfl; simp at hk)
      have ha : a.left = a'.left ≫ eA.left := by
        rw [← cancel_mono (genMap u.U), haa, Category.assoc, hgen]
      exact hT F' k hk1 hk q q' a a' hqa hqa' ha)
  have hunit : ∀ w : u.Vˣ, ‖algebraMap (FractionRing u.V) (PadicAlgCl p) (algebraMap u.V _ (w : u.V))‖ = 1 := by
    intro w
    have h1 := (u.norm_le (algebraMap u.V _ (w : u.V))).2 ⟨w, rfl⟩
    have h2 := (u.norm_le (algebraMap u.V _ ((w⁻¹ : u.Vˣ) : u.V))).2 ⟨_, rfl⟩
    have h3 : ‖algebraMap (FractionRing u.V) (PadicAlgCl p) (algebraMap u.V _ (w : u.V))‖ *
        ‖algebraMap (FractionRing u.V) (PadicAlgCl p) (algebraMap u.V _ ((w⁻¹ : u.Vˣ) : u.V))‖ = 1 := by
      rw [← norm_mul, ← map_mul, ← map_mul, Units.mul_inv, map_one, map_one, norm_one]
    have h4 := norm_nonneg (algebraMap (FractionRing u.V) (PadicAlgCl p) (algebraMap u.V _ ((w⁻¹ : u.Vˣ) : u.V)))
    have h5 := norm_nonneg (algebraMap (FractionRing u.V) (PadicAlgCl p) (algebraMap u.V _ (w : u.V)))
    nlinarith
  have hpol : ∀ a' b, l.q (s a' + b) - l.q (s a') - l.q b = l.q (a' + m b) - l.q a' - l.q (m b) := by
    intro a' b
    obtain ⟨x, hx⟩ := GlobalTheory.PsiFromTau.exists_isTauCoord u.V u.D.toPre (s a') b
    obtain ⟨x', hx'⟩ := GlobalTheory.PsiFromTau.exists_isTauCoord u.V u.D.toPre a' (m b)
    obtain ⟨w, hw⟩ := hmain a' b x x' hx hx'
    have n₁ := GlobalTheory.T.norm_tauLineBundleCoordinate_eq_exp o Ω S ρ p y₀ u l (s a') b x hx
    have n₂ := GlobalTheory.T.norm_tauLineBundleCoordinate_eq_exp o Ω S ρ p y₀ u l a' (m b) x' hx'
    rw [hw, map_mul, norm_mul, hunit, _root_.one_mul, n₂] at n₁
    have := Real.exp_injective n₁
    linarith
  have hpolW : ∀ y : Fin 8 → X₀, qW W β ((fun a => ∑ b, E a b • y b) + j χ) - qW W β (fun a => ∑ b, E a b • y b) -
      qW W β (j χ) = qW W β (y + j (m χ)) - qW W β y - qW W β (j (m χ)) := by
    intro y
    have h := hpol (j.symm y) χ
    rw [hq, hq, hq, hq, hq, hq, map_add (f := _), map_add (f := _), hs, AddEquiv.apply_symm_apply, hEm] at h
    have h' : sc * ((qW W β ((fun a => ∑ b, E a b • y b) + j χ) - qW W β (fun a => ∑ b, E a b • y b) -
        qW W β (j χ) : ℤ) : ℝ) = sc * ((qW W β (y + j (m χ)) - qW W β y - qW W β (j (m χ)) : ℤ) : ℝ) := by
      push_cast; linarith
    exact_mod_cast mul_left_cancel₀ hsc.ne' h'
  exact GlobalTheory.T.eq_adjoint_apply_of_weightedQuadraticSum_polar W hW X₀ β hβs hβp E E' hEE (j χ) (j (m χ)) hpolW

end GlobalTheory.Poinc.FibMatrix
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PotIso

open GlobalTheory.KS GlobalTheory.KS.AdjDlog

theorem constFn_mul_c {R : Type} [CommRing R] {Y : Scheme.{0}} (q : Y ⟶ Sp R) (W : Y.Opens) (a b : R) :
    constFn q W (a * b) = constFn q W a * constFn q W b := by
  simp only [constFn, map_mul]

theorem constFn_one_c {R : Type} [CommRing R] {Y : Scheme.{0}} (q : Y ⟶ Sp R) (W : Y.Opens) :
    constFn q W 1 = 1 := by
  simp only [constFn, map_one]

theorem constFn_zero_c {R : Type} [CommRing R] {Y : Scheme.{0}} (q : Y ⟶ Sp R) (W : Y.Opens) :
    constFn q W 0 = 0 := by
  simp only [constFn, map_zero]

theorem constFn_comp_spMap_c {R S : Type} [CommRing R] [CommRing S] {Y : Scheme.{0}} (q : Y ⟶ Sp S) (x : R →+* S)
    (W : Y.Opens) (t : R) : constFn (q ≫ spMap x) W t = constFn q W (x t) := by
  have e1 : (q ≫ spMap x).appLE ⊤ W le_top = (spMap x).appLE ⊤ ⊤ le_top ≫ q.appLE ⊤ W le_top :=
    (Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _).symm
  have h2 := congrArg (fun k => k.hom t) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom x))
  change ((q ≫ spMap x).appLE ⊤ W le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom t) =
    (q.appLE ⊤ W le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom (x t))
  rw [e1, CommRingCat.comp_apply]
  congr 1
  simp only [CommRingCat.comp_apply] at h2
  exact h2.symm

theorem pull_g_val {X Y : Scheme.{0}} (L : LB X) (f : Y ⟶ X) (j j' : PUnit → L.ι) {O : Y.Opens}
    (h : O ≤ (L.pull f).U j ⊓ (L.pull f).U j') :
    (res h ((L.pull f).g j j')).val = pbT f (L.g (j PUnit.unit) (j' PUnit.unit)).val O := by
  have le : O ≤ f ⁻¹ᵁ (L.U (j PUnit.unit) ⊓ L.U (j' PUnit.unit)) :=
    le_inf ((h.trans inf_le_left).trans (LB.wchart_le L _ j PUnit.unit))
      ((h.trans inf_le_right).trans (LB.wchart_le L _ j' PUnit.unit))
  have e : res h ((L.pull f).g j j') = res le (pullU f _ (L.g (j PUnit.unit) (j' PUnit.unit))) := by
    show res h (∏ k : PUnit, _) = _
    erw [Fintype.prod_unique, zpow_one, res_res']
    rfl
  rw [e, val_res_pullU]

theorem isPullback_pr {k R : Type} [Field k] [CommRing R] (ρ : R →+* DualNumber k) {A B' A₀ : Scheme.{0}}
    (pA : A ⟶ Sp R) (pB : B' ⟶ Sp (DualNumber k)) (p₀ : A₀ ⟶ Sp k) (π₂ : B' ⟶ A) (m₀ : A₀ ⟶ A) (pr : B' ⟶ A₀)
    (h₂ : IsPullback π₂ pB pA (spMap (constHom ρ)))
    (hm : IsPullback m₀ p₀ pA (spMap ((TrivSqZeroExt.fstHom k k k).toRingHom.comp ρ)))
    (hpr : pr ≫ m₀ = π₂) (hprb : pr ≫ p₀ = pB ≫ spMap (algebraMap k (DualNumber k))) :
    IsPullback pr pB p₀ (spMap (algebraMap k (DualNumber k))) := by
  refine IsPullback.of_right ?_ hprb hm
  have e : spMap (constHom ρ) = spMap (algebraMap k (DualNumber k)) ≫
      spMap ((TrivSqZeroExt.fstHom k k k).toRingHom.comp ρ) := by
    rw [← Spec.map_comp]; rfl
  rw [hpr, ← e]; exact h₂

theorem conn_of_iso : ∀ (k : Type) [Field k] (R : Type) [CommRing R] (P : PolAV (Sp R)) (ρ : R →+* DualNumber k) (B' : Over (Sp (DualNumber k))) [GrpObj B'] (π₁ π₂ : B'.left ⟶ P.A.left), IsGrpPullback B' P.A (spMap ρ) π₁ → IsGrpPullback B' P.A (spMap (constHom ρ)) π₂ → (∀ (Z : Scheme.{0}) (x : Z ⟶ B'.left) (y : Z ⟶ Sp k), x ≫ B'.hom = y ≫ spMap (TrivSqZeroExt.fstHom k k k).toRingHom → x ≫ π₁ = x ≫ π₂) → ∀ (A₀ : Over (Sp k)) [GrpObj A₀] (m₀ : A₀.left ⟶ P.A.left), IsGrpPullback A₀ P.A (spMap ((TrivSqZeroExt.fstHom k k k).toRingHom.comp ρ)) m₀ → ∀ pr : B'.left ⟶ A₀.left, pr ≫ m₀ = π₂ → pr ≫ A₀.hom = B'.hom ≫ spMap (algebraMap k (DualNumber k)) → ∀ {J : Type} (V : J → P.A.left.Opens) (jj : J → P.L.ι), ⨆ i, V i = ⊤ → (∀ i, V i ≤ P.L.U (jj i)) → ∀ d : ∀ W : P.A.left.Opens, Γ(P.A.left, W) → Γ(A₀.left, m₀ ⁻¹ᵁ W), GlobalTheory.KS.LocDerK A₀.hom P.A.hom m₀ (fun r => (ρ r).snd) ⊤ d → (∀ (W : P.A.left.Opens) (f : Γ(P.A.left, W)), pbT π₁ f (π₂ ⁻¹ᵁ W) = pbT π₂ f (π₂ ⁻¹ᵁ W) + constFn B'.hom (π₂ ⁻¹ᵁ W) DualNumber.eps * pbT pr (d W f) (π₂ ⁻¹ᵁ W)) → ∀ w : LB.Iso (P.L.pull π₁) (P.L.pull π₂), w.IsGen → ∃ q : ∀ i, Γ(A₀.left, m₀ ⁻¹ᵁ V i), GlobalTheory.HeatConn.IsConnK P.A P.L A₀ m₀ (fun r => (ρ r).snd) V jj d q := by
  intro k _ R _ P ρ B' _ π₁ π₂ h₁ h₂ hfib A₀ _ m₀ hm₀ pr hpr hprb J V jj hV hVU d hd hdB w hw
  obtain ⟨a, b, hab⟩ := GlobalTheory.T.two_pullback_isomorphism_unit_constant_plus_eps_function k R P ρ B' π₁ π₂ h₁ h₂ hfib A₀ m₀ hm₀ pr hpr hprb V jj hV hVU w hw
  have hpre : ∀ W : P.A.left.Opens, π₁ ⁻¹ᵁ W = π₂ ⁻¹ᵁ W := GlobalTheory.T.preimage_eq_of_agree_on_closedFibre_dualNumbers k P.A.left B'.left B'.hom π₁ π₂ hfib
  have hpb : IsPullback pr B'.hom A₀.hom (spMap (algebraMap k (DualNumber k))) :=
    GlobalTheory.PotIso.isPullback_pr ρ _ _ _ π₂ m₀ pr h₂.1 hm₀.1 hpr hprb
  have thick := GlobalTheory.T.existsUnique_add_eps_mul_on_dualNumber_thickening k A₀.left B'.left A₀.hom B'.hom pr hpb
  subst hpr
  refine ⟨fun i => constFn A₀.hom (m₀ ⁻¹ᵁ V i) ((a⁻¹ : kˣ) : k) * b i, hd, hV, hVU, fun i i' => ?_⟩
  have hW : V i ⊓ V i' ≤ P.L.U (jj i) ⊓ P.L.U (jj i') := inf_le_inf (hVU i) (hVU i')
  have hO₀ : m₀ ⁻¹ᵁ (V i ⊓ V i') ≤ m₀ ⁻¹ᵁ (P.L.U (jj i) ⊓ P.L.U (jj i')) := m₀.preimage_mono hW
  have hO : (pr ≫ m₀) ⁻¹ᵁ (V i ⊓ V i') ≤ pr ⁻¹ᵁ (m₀ ⁻¹ᵁ (V i ⊓ V i')) := le_rfl
  have hchart : ∀ l, (pr ≫ m₀) ⁻¹ᵁ V l ≤ (LB.div (P.L.pull (pr ≫ m₀)) (P.L.pull π₁)).U (fun _ => jj l, fun _ => jj l) := by
    intro l x hx
    refine ⟨Set.mem_iInter.2 fun _ => hVU l hx, Set.mem_iInter.2 fun _ => ?_⟩
    have : x ∈ π₁ ⁻¹ᵁ P.L.U (jj l) := by rw [hpre]; exact hVU l hx
    exact this
  have hM : (pr ≫ m₀) ⁻¹ᵁ (V i ⊓ V i') ≤ (P.L.pull (pr ≫ m₀)).U (fun _ => jj i) ⊓ (P.L.pull (pr ≫ m₀)).U (fun _ => jj i') :=
    fun x hx => ⟨(hchart i hx.1).1, (hchart i' hx.2).1⟩
  have hL : (pr ≫ m₀) ⁻¹ᵁ (V i ⊓ V i') ≤ (P.L.pull π₁).U (fun _ => jj i) ⊓ (P.L.pull π₁).U (fun _ => jj i') :=
    fun x hx => ⟨(hchart i hx.1).2, (hchart i' hx.2).2⟩
  have iso := iso_rel w hw (fun _ => jj i) (fun _ => jj i') (fun _ => jj i) (fun _ => jj i') hM hL
  rw [GlobalTheory.PotIso.pull_g_val, GlobalTheory.PotIso.pull_g_val] at iso
  have hs : ∀ l, V i ⊓ V i' ≤ V l → rsT (w.s (fun _ => jj l, fun _ => jj l)).val ((pr ≫ m₀) ⁻¹ᵁ (V i ⊓ V i')) =
      constFn B'.hom ((pr ≫ m₀) ⁻¹ᵁ (V i ⊓ V i')) (algebraMap k (DualNumber k) (a : k)) +
        constFn B'.hom ((pr ≫ m₀) ⁻¹ᵁ (V i ⊓ V i')) DualNumber.eps *
          pbT pr (rsT (b l) (m₀ ⁻¹ᵁ (V i ⊓ V i'))) ((pr ≫ m₀) ⁻¹ᵁ (V i ⊓ V i')) := by
    intro l hl
    have hl' : (pr ≫ m₀) ⁻¹ᵁ (V i ⊓ V i') ≤ (pr ≫ m₀) ⁻¹ᵁ V l := (pr ≫ m₀).preimage_mono hl
    rw [← rsT_rsT (hchart l) hl', hab l, rsT_add, rsT_mul, GlobalTheory.KS.rsT_constFn _ hl', GlobalTheory.KS.rsT_constFn _ hl',
      rsT_pbT pr (show (pr ≫ m₀) ⁻¹ᵁ V l ≤ pr ⁻¹ᵁ (m₀ ⁻¹ᵁ V l) from le_rfl) hl', pbT_rsT pr (m₀.preimage_mono hl) hO]
  have hA : constFn B'.hom ((pr ≫ m₀) ⁻¹ᵁ (V i ⊓ V i')) (algebraMap k (DualNumber k) (a : k)) =
      pbT pr (constFn A₀.hom (m₀ ⁻¹ᵁ (V i ⊓ V i')) (a : k)) ((pr ≫ m₀) ⁻¹ᵁ (V i ⊓ V i')) := by
    rw [GlobalTheory.KS.pbT_constFn A₀.hom pr hO, hprb, GlobalTheory.PotIso.constFn_comp_spMap_c]
  have hd' := hdB (V i ⊓ V i') (rsT (P.L.g (jj i) (jj i')).val (V i ⊓ V i'))
  rw [pbT_rsT π₁ hW (hpre _).ge, pbT_rsT (pr ≫ m₀) hW le_rfl, ← pbT_pbT pr m₀ hO₀ hO] at hd'
  rw [← pbT_pbT pr m₀ hO₀ hO, hd', hs i inf_le_left, hs i' inf_le_right, hA] at iso
  have hee : constFn B'.hom ((pr ≫ m₀) ⁻¹ᵁ (V i ⊓ V i')) DualNumber.eps *
      constFn B'.hom ((pr ≫ m₀) ⁻¹ᵁ (V i ⊓ V i')) DualNumber.eps = 0 := by
    rw [← GlobalTheory.PotIso.constFn_mul_c, DualNumber.eps_mul_eps, GlobalTheory.PotIso.constFn_zero_c]
  generalize d (V i ⊓ V i') (rsT (P.L.g (jj i) (jj i')).val (V i ⊓ V i')) = D at iso ⊢
  generalize pbT m₀ (P.L.g (jj i) (jj i')).val (m₀ ⁻¹ᵁ (V i ⊓ V i')) = g₀ at iso ⊢
  have key : constFn B'.hom ((pr ≫ m₀) ⁻¹ᵁ (V i ⊓ V i')) DualNumber.eps *
      pbT pr (constFn A₀.hom (m₀ ⁻¹ᵁ (V i ⊓ V i')) (a : k) * D) ((pr ≫ m₀) ⁻¹ᵁ (V i ⊓ V i')) =
      constFn B'.hom ((pr ≫ m₀) ⁻¹ᵁ (V i ⊓ V i')) DualNumber.eps *
      pbT pr (g₀ * (rsT (b i') (m₀ ⁻¹ᵁ (V i ⊓ V i')) - rsT (b i) (m₀ ⁻¹ᵁ (V i ⊓ V i'))))
        ((pr ≫ m₀) ⁻¹ᵁ (V i ⊓ V i')) := by
    rw [pbT_mul, pbT_mul, pbT_sub]
    linear_combination iso - (pbT pr (rsT (b i) (m₀ ⁻¹ᵁ (V i ⊓ V i'))) ((pr ≫ m₀) ⁻¹ᵁ (V i ⊓ V i')) *
      pbT pr D ((pr ≫ m₀) ⁻¹ᵁ (V i ⊓ V i'))) * hee
  obtain ⟨_, _, huniq⟩ := thick (m₀ ⁻¹ᵁ (V i ⊓ V i'))
    (constFn B'.hom (pr ⁻¹ᵁ (m₀ ⁻¹ᵁ (V i ⊓ V i'))) DualNumber.eps *
      pbT pr (constFn A₀.hom (m₀ ⁻¹ᵁ (V i ⊓ V i')) (a : k) * D) (pr ⁻¹ᵁ (m₀ ⁻¹ᵁ (V i ⊓ V i'))))
  have u₁ := huniq (0, constFn A₀.hom (m₀ ⁻¹ᵁ (V i ⊓ V i')) (a : k) * D) (by
    simp only [map_zero, zero_add, app_eq_pbT])
  have u₂ := huniq (0, g₀ * (rsT (b i') (m₀ ⁻¹ᵁ (V i ⊓ V i')) - rsT (b i) (m₀ ⁻¹ᵁ (V i ⊓ V i')))) (by
    simp only [map_zero, zero_add, app_eq_pbT]; exact key)
  have hX := congrArg Prod.snd (u₁.trans u₂.symm)
  simp only at hX
  have hc : constFn A₀.hom (m₀ ⁻¹ᵁ (V i ⊓ V i')) ((a⁻¹ : kˣ) : k) * constFn A₀.hom (m₀ ⁻¹ᵁ (V i ⊓ V i')) (a : k) = 1 := by
    rw [← GlobalTheory.PotIso.constFn_mul_c, Units.inv_mul, GlobalTheory.PotIso.constFn_one_c]
  show D = g₀ * (rsT (constFn A₀.hom (m₀ ⁻¹ᵁ V i') ((a⁻¹ : kˣ) : k) * b i') (m₀ ⁻¹ᵁ (V i ⊓ V i')) -
    rsT (constFn A₀.hom (m₀ ⁻¹ᵁ V i) ((a⁻¹ : kˣ) : k) * b i) (m₀ ⁻¹ᵁ (V i ⊓ V i')))
  rw [rsT_mul, rsT_mul, GlobalTheory.KS.rsT_constFn _ (m₀.preimage_mono inf_le_right),
    GlobalTheory.KS.rsT_constFn _ (m₀.preimage_mono inf_le_left)]
  linear_combination constFn A₀.hom (m₀ ⁻¹ᵁ (V i ⊓ V i')) ((a⁻¹ : kˣ) : k) * hX - D * hc

end GlobalTheory.PotIso
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

noncomputable section

namespace GlobalTheory.Desc.ResInj

theorem cst_eq_fnOf {X : Scheme.{0}} [IsIntegral X] {R : Type} [CommRing R] (p : X ⟶ Sp R) (V : X.Opens)
    (hV : genericPoint X ∈ V) (r : R) : GlobalTheory.Desc.cst p r = fnOf V hV (GlobalTheory.AbLaw.cst p V r) := by
  simp only [GlobalTheory.Desc.cst, GlobalTheory.AbLaw.cst, fnOf, RingHom.comp_apply, Scheme.Hom.appLE, CommRingCat.hom_comp]
  rw [TopCat.Presheaf.germ_res_apply]

theorem zeroAt_fnOf_iff {X : Scheme.{0}} [IsIntegral X] {U : X.Opens} {x : X} (hx : x ∈ U) (b : Γ(X, U)) :
    ZeroAt x (fnOf U (gen_mem hx) b) ↔ (X.presheaf.germ U x hx).hom b ∈ maximalIdeal (X.presheaf.stalk x) := by
  refine ⟨fun ⟨a, ha, e⟩ => ?_, fun h => ⟨_, h, algebraMap_germ hx b⟩⟩
  rwa [IsFractionRing.injective (X.presheaf.stalk x) X.functionField (e.trans (algebraMap_germ hx b).symm)] at ha

theorem cst_zeroAt (R : Type) [CommRing R] [IsLocalRing R] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp R) (x : X)
    (hx : p x = closedPoint R) (r : R) (hr : r ∈ maximalIdeal R) : ZeroAt x (GlobalTheory.Desc.cst p r) := by
  have hreg : RegAt x (GlobalTheory.Desc.cst p r) := regAt_fnOf (U := ⊤) trivial trivial _
  refine zeroAt_iff.2 ⟨hreg, fun hu => ?_⟩
  have h1 := (unitAt_fnOf_iff (U := ⊤) trivial trivial _).1 hu
  have h2 : x ∈ p ⁻¹ᵁ (Sp R).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of R)).inv r) := by
    rw [Scheme.Hom.preimage_basicOpen]; exact h1
  have h3 : p x ∈ (Sp R).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of R)).inv r) := h2
  rw [basicOpen_eq_of_affine, hx] at h3
  exact (PrimeSpectrum.mem_basicOpen _ _).1 h3 hr

end GlobalTheory.Desc.ResInj

theorem GlobalTheory.Desc.ResInj.exists_affine_fnOf : ∀ (X : Scheme.{0}) [IsIntegral X] (x : X) (n : ℕ) (u : Fin n → X.functionField), (∀ i, GlobalTheory.Cartier.RegAt x (u i)) → ∃ (U : X.Opens) (hx : x ∈ U), IsAffineOpen U ∧ ∃ s : Fin n → Γ(X, U), ∀ i, GlobalTheory.Cartier.fnOf U (GlobalTheory.Cartier.gen_mem hx) (s i) = u i := by
  intro X _ x n u hu
  choose W hxW s hs using fun i => (hu i).exists_fnOf
  let W₀ : X.Opens := ⟨⋂ i, (W i : Set X), isOpen_iInter_of_finite fun i => (W i).isOpen⟩
  have hx₀ : x ∈ W₀ := Set.mem_iInter.2 hxW
  obtain ⟨U, hU, hxU, hUW⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp (Scheme.isBasis_affineOpens X)) hx₀
  have hle : ∀ i, U ≤ W i := fun i z hz => Set.mem_iInter.1 (hUW hz) i
  refine ⟨U, hxU, hU, fun i => resG X (hle i) (s i), fun i => ?_⟩
  rw [fnOf_resG, hs]

theorem GlobalTheory.Desc.ResInj.mem_map_of_germ_mem : ∀ (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (G : Over (Sp R)) [IsIntegral G.left], Smooth G.hom → GeometricallyConnected G.hom → ∀ y : G.left, G.hom y = closedPoint R → ringKrullDim (G.left.presheaf.stalk y) = 1 → ∀ (U : G.left.Opens) (hy : y ∈ U), IsAffineOpen U → ∀ b : Γ(G.left, U), (G.left.presheaf.germ U y hy).hom b ∈ maximalIdeal (G.left.presheaf.stalk y) → b ∈ (maximalIdeal R).map (GlobalTheory.AbLaw.cst G.hom U) := by
  intro R _ _ _ G _ hsm hgc y hy hdim U hyU hU b hb
  haveI : Nonempty U := ⟨⟨y, hyU⟩⟩
  letI : Algebra R Γ(G.left, U) := (GlobalTheory.AbLaw.cst G.hom U).toAlgebra
  haveI : Module.Flat R Γ(G.left, U) := GlobalTheory.AbLaw.flat_cst G.hom hU
  let p := hU.primeIdealOf ⟨y, hyU⟩
  letI : Algebra Γ(G.left, U) (G.left.presheaf.stalk y) := G.left.presheaf.algebra_section_stalk ⟨y, hyU⟩
  haveI hloc := hU.isLocalization_stalk ⟨y, hyU⟩
  have hmem : ∀ c : Γ(G.left, U), (G.left.presheaf.germ U y hyU).hom c ∈ maximalIdeal (G.left.presheaf.stalk y) ↔ c ∈ p.asIdeal := by
    intro c
    exact IsLocalization.AtPrime.to_map_mem_maximal_iff (G.left.presheaf.stalk y) p.asIdeal c
  have hle : (maximalIdeal R).map (algebraMap R Γ(G.left, U)) ≤ p.asIdeal := by
    rw [Ideal.map_le_iff_le_comap]
    intro t ht
    rw [Ideal.mem_comap, ← hmem, ← GlobalTheory.Desc.ResInj.zeroAt_fnOf_iff hyU]
    have := GlobalTheory.Desc.ResInj.cst_zeroAt R G.left G.hom y hy t ht
    rwa [GlobalTheory.Desc.ResInj.cst_eq_fnOf G.hom U (gen_mem hyU)] at this
  have hd : ringKrullDim (Localization.AtPrime p.asIdeal) = 1 := by
    rw [← hdim]
    exact ringKrullDim_eq_of_ringEquiv (IsLocalization.algEquiv p.asIdeal.primeCompl (Localization.AtPrime p.asIdeal) (G.left.presheaf.stalk y)).toRingEquiv
  have e := GlobalTheory.T.eq_map_maximalIdeal_of_ringKrullDim_eq_one' R Γ(G.left, U) p.asIdeal hle hd (GlobalTheory.T.isDomain_sections_quot_maximalIdeal_smooth_connected R G hsm hgc U hU y hyU hy)
  have : b ∈ p.asIdeal := (hmem b).1 hb
  rw [e] at this
  exact this

theorem GlobalTheory.Desc.ResInj.residue_linearIndependent : ∀ (T D : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [CommRing D] [IsDomain D] [IsDiscreteValuationRing D] (a : T →+* D), a.Flat → (maximalIdeal T).map a = maximalIdeal D → ∀ (H : Over (Sp T)) [GrpObj H] [IsIntegral H.left] (H' : Over (Sp D)) [GrpObj H'] [IsIntegral H'.left] (π : H'.left ⟶ H.left) (θ : H.left.functionField →+* H'.left.functionField), IsSemiAbelian H → IsPullback π H'.hom H.hom (spMap a) → PFF (𝟙 _) π θ → ∀ (y : H.left) (y' : H'.left), H.hom y = closedPoint T → H'.hom y' = closedPoint D → ringKrullDim (H.left.presheaf.stalk y) = 1 → ringKrullDim (H'.left.presheaf.stalk y') = 1 → ∀ (n : ℕ) (u : Fin n → H.left.functionField), (∀ i, GlobalTheory.Cartier.RegAt y (u i)) → (∀ c : Fin n → T, GlobalTheory.Cartier.ZeroAt y (∑ i, GlobalTheory.Desc.cst H.hom (c i) * u i) → ∀ i, c i ∈ maximalIdeal T) → ∀ d : Fin n → D, GlobalTheory.Cartier.ZeroAt y' (∑ i, GlobalTheory.Desc.cst H'.hom (d i) * θ (u i)) → ∀ i, d i ∈ maximalIdeal D := by
  intro T D _ _ _ _ _ _ a ha hm H _ _ H' _ _ π θ hH hpb hpff y y' hy hy' hdy hdy' n u hu hind d hz
  have hπy : π y' = y := GlobalTheory.T.baseChange_sends_closedFibre_genericPoint_dvr T D a ha hm H H' π θ hH hpb hpff y y' hy hy' hdy hdy'
  obtain ⟨U, hyU, hUa, x, hx⟩ := GlobalTheory.Desc.ResInj.exists_affine_fnOf H.left y n u hu
  set V : H'.left.Opens := π ⁻¹ᵁ U with hVdef
  have hy'V : y' ∈ V := by show π y' ∈ U; rw [hπy]; exact hyU
  have hgU : genericPoint H.left ∈ U := gen_mem hyU
  have hgV : genericPoint H'.left ∈ V := gen_mem hy'V
  letI : Algebra T D := a.toAlgebra
  letI : Algebra T Γ(H.left, U) := (GlobalTheory.AbLaw.cst H.hom U).toAlgebra
  letI : Algebra D Γ(H'.left, V) := (GlobalTheory.AbLaw.cst H'.hom V).toAlgebra
  letI : Algebra Γ(H.left, U) Γ(H'.left, V) := (π.app U).hom.toAlgebra
  letI : Algebra T Γ(H'.left, V) := ((GlobalTheory.AbLaw.cst H'.hom V).comp a).toAlgebra
  haveI : IsScalarTower T D Γ(H'.left, V) := .of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower T Γ(H.left, U) Γ(H'.left, V) := .of_algebraMap_eq fun r => by
    have e := GlobalTheory.AbLaw.appLE_cst hpb.w (V := U) (V' := V) le_rfl r
    rw [Scheme.Hom.appLE_eq_app] at e
    exact e.symm
  haveI : Algebra.IsPushout T D Γ(H.left, U) Γ(H'.left, V) := by
    have po := GlobalTheory.AbLaw.isPushout_cst hpb hUa (V' := V) rfl
    rw [Scheme.Hom.appLE_eq_app] at po
    exact CommRingCat.isPushout_iff_isPushout.mp po
  have hsm : Smooth H'.hom := MorphismProperty.of_isPullback hpb hH.smooth
  have hgc : GeometricallyConnected H'.hom := MorphismProperty.of_isPullback hpb hH.geomConnected

  have hindA : ∀ c : Fin n → T, ∑ i, c i • x i ∈ (maximalIdeal T).map (algebraMap T Γ(H.left, U)) →
      ∀ i, c i ∈ maximalIdeal T := by
    intro c hc
    apply hind c
    have hle : (maximalIdeal T).map (algebraMap T Γ(H.left, U)) ≤
        Ideal.comap (H.left.presheaf.germ U y hyU).hom (maximalIdeal _) := by
      rw [Ideal.map_le_iff_le_comap]
      intro t ht
      rw [Ideal.mem_comap, Ideal.mem_comap, ← GlobalTheory.Desc.ResInj.zeroAt_fnOf_iff hyU]
      have := GlobalTheory.Desc.ResInj.cst_zeroAt T H.left H.hom y hy t ht
      rwa [GlobalTheory.Desc.ResInj.cst_eq_fnOf H.hom U hgU] at this
    have h1 := hle hc
    rw [Ideal.mem_comap, ← GlobalTheory.Desc.ResInj.zeroAt_fnOf_iff hyU] at h1
    convert h1 using 1

    simp only [map_sum, Algebra.smul_def, map_mul, hx]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [GlobalTheory.Desc.ResInj.cst_eq_fnOf H.hom U hgU]
    rfl

  have hd := GlobalTheory.T.pushout_residue_linearIndependent' T D Γ(H.left, U) Γ(H'.left, V) hm n x hindA d
  apply hd
  apply GlobalTheory.Desc.ResInj.mem_map_of_germ_mem D H' hsm hgc y' hy' hdy' V hy'V (GlobalTheory.AbLaw.isAffineOpen_preimage_of_isPullback hpb hUa)
  rw [← GlobalTheory.Desc.ResInj.zeroAt_fnOf_iff hy'V]
  convert hz using 1

  simp only [map_sum, Algebra.smul_def, map_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← hx i, ← GlobalTheory.Desc.fnOf_app_of_pff H.left H'.left π θ hpff U hgU hgV, GlobalTheory.Desc.ResInj.cst_eq_fnOf H'.hom V hgV]
  rfl
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

theorem _root_.GlobalTheory.T.complex_symmetricAmple_square_decomposition : ∀ (A : Over (Sp ℂ)) [GrpObj A], IsAbelianScheme A → ∀ (L M : LB A.left), L.IsLB → M.IsLB → RelAmple A L → RelAmple A M → LBIso (L.pull (GrpObj.inv : A ⟶ A).left) L → LBIso (M.pull (GrpObj.inv : A ⟶ A).left) M → SqDec A L M := by
  first | exact @GlobalTheory.SqDecC.sqDec_complex | exact GlobalTheory.SqDecC.sqDec_complex | (intros; apply GlobalTheory.SqDecC.sqDec_complex <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

namespace GlobalTheory.Desc.OpenImmersionDescent

theorem openImm_of_isIso_appTop {X Y : Scheme.{0}} [IsAffine Y] [X.IsQuasiAffine] (g : X ⟶ Y) [IsIso g.appTop] :
    IsOpenImmersion g := by
  have e : g = X.toSpecΓ ≫ Spec.map g.appTop ≫ Y.isoSpec.inv := by
    rw [← Category.assoc, ← Scheme.toSpecΓ_naturality, Category.assoc, Scheme.toSpecΓ_isoSpec_inv, Category.comp_id]
  rw [e]; infer_instance

theorem bij_congr {X Y : Scheme.{0}} (f : X ⟶ Y) (V W : Y.Opens) (h : V = W) (hb : Function.Bijective (f.app W)) :
    Function.Bijective (f.app V) := by subst h; exact hb

end GlobalTheory.Desc.OpenImmersionDescent


open GlobalTheory.Desc.OpenImmersionDescent in
theorem GlobalTheory.Desc.openIn_model : ∀ (R F : Type) [CommRing R] [IsDomain R] [Field F] (c₀ : R →+* F) (N : ℕ → Set F), GradedFam c₀ N → ∀ (P : Scheme.{0}) [IsIntegral P] (p : P ⟶ Sp R) (ψ : P.functionField →+* F) (Dp : ℕ → F → P.Opens), IsModel c₀ N p ψ Dp → ∀ (R₁ : Type) [CommRing R₁] [IsDomain R₁] (ρ : R →+* R₁), ρ.Flat → Function.Injective c₀ → ∀ (Y : Scheme.{0}) [IsIntegral Y] [CompactSpace Y] [QuasiSeparatedSpace Y] (q : Y ⟶ Sp R₁) (θ : F →+* Y.functionField) (D₁ : CartierDiv Y), θ.comp c₀ = (GlobalTheory.Desc.cst q).comp ρ → LinDisj c₀ (GlobalTheory.Desc.cst q) θ → AmpleDiv D₁ → (∀ k, Sec D₁ k = spanBy (GlobalTheory.Desc.cst q) (θ '' N k)) → ∀ m : Y ⟶ P, m ≫ p = q ≫ spMap ρ → PFF (𝟙 _) m (θ.comp ψ) → (∀ k, 1 ≤ k → ∀ b ∈ N k, ∀ y, m y ∈ Dp k b ↔ y ∈ locus D₁ k (θ b)) → OpenIn m q p (spMap ρ) := by
  intro R F _ _ _ c₀ N hN P _ p ψ Dp hP R₁ _ _ ρ hρ hc₀ Y _ _ _ q θ D₁ hθ hLD hamp hSec m hm hPFF hloc
  refine ⟨hm, ?_⟩
  refine IsZariskiLocalAtTarget.of_forall_exists_morphismRestrict (P := @IsOpenImmersion) fun z => ?_
  obtain ⟨k, hk, b, hb, hz⟩ := hP.cover (pullback.fst p (spMap ρ) z)
  refine ⟨(pullback.fst p (spMap ρ)) ⁻¹ᵁ Dp k b, hz, ?_⟩
  haveI : IsAffineHom (pullback.fst p (spMap ρ)) := by first | infer_instance | exact MorphismProperty.pullback_fst (P := @IsAffineHom) p (spMap ρ) inferInstance | exact (isAffineHom_isStableUnderBaseChange.of_isPullback (IsPullback.of_hasPullback p (spMap ρ)).flip inferInstance)
  have hA : IsAffineOpen ((pullback.fst p (spMap ρ)) ⁻¹ᵁ Dp k b) := (hP.affine k hk b hb).preimage _
  haveI : IsAffine ((pullback.fst p (spMap ρ)) ⁻¹ᵁ Dp k b).toScheme := hA
  have hpre : ((pullback.lift m q hm) ⁻¹ᵁ ((pullback.fst p (spMap ρ)) ⁻¹ᵁ Dp k b) : Set Y) = locus D₁ k (θ b) := by
    ext y
    change pullback.fst p (spMap ρ) (pullback.lift m q hm y) ∈ Dp k b ↔ _
    rw [← Scheme.Hom.comp_apply, pullback.lift_fst]
    exact hloc k hk b hb y
  haveI : ((pullback.lift m q hm) ⁻¹ᵁ ((pullback.fst p (spMap ρ)) ⁻¹ᵁ Dp k b)).toScheme.IsQuasiAffine :=
    GlobalTheory.T.isQuasiAffine_cartierSectionGeneratingLocus_ample Y D₁ hamp k hk (θ b) (by rw [hSec]; exact subset_spanBy _ _ ⟨b, hb, rfl⟩) _ hpre
  haveI : IsIso (pullback.lift m q hm ∣_ ((pullback.fst p (spMap ρ)) ⁻¹ᵁ Dp k b)).appTop := by
    rw [morphismRestrict_appTop]
    have h1 := bij_congr (pullback.lift m q hm) _ _ (Scheme.Opens.ι_image_top _)
      ⟨GlobalTheory.T.proj_model_baseChange_standard_open_app_injective R F c₀ N hN P p ψ Dp hP R₁ ρ hρ hc₀ Y q θ D₁ hθ hLD hamp hSec m hPFF hloc hm k hk b hb,
       GlobalTheory.T.proj_model_baseChange_standard_open_app_surjective R F c₀ N hN P p ψ Dp hP R₁ ρ hρ hc₀ Y q θ D₁ hθ hLD hamp hSec m hPFF hloc hm k hk b hb⟩
    have h2 : IsIso (Scheme.Hom.app (pullback.lift m q hm) ((pullback.fst p (spMap ρ) ⁻¹ᵁ Dp k b).ι ''ᵁ ⊤)) :=
      (ConcreteCategory.isIso_iff_bijective _).2 h1
    exact @IsIso.comp_isIso _ _ _ _ _ _ _ h2 (Functor.map_isIso _ _)
  exact openImm_of_isIso_appTop _
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc


theorem _root_.GlobalTheory.T.zarhinBundle_principal : ∀ (h M d : ℕ) (S : Scheme.{0}) (t : S ⟶ Sp (cycAway M)) (c : SiegPre h M (zetaAway M) t) (B : Over S) [GrpObj B] [IsCommMonObj B] (Q : LB (c.A ⊗ B).left) (la : c.A ⟶ B) (mu : B ⟶ c.A) (hZ : GlobalTheory.ZarhinFam.ZData c d B Q la mu), 1 ≤ h → 3 ≤ M → Odd M → 0 < d → M.Coprime d → IsUnit ((d : ℕ) : Γ(S, ⊤)) → SiegKerBy c d → Out.RelAmple (GlobalTheory.ZarhinFam.Zob c.A B) ((GlobalTheory.ZarhinFam.zP c.A B c.isLB hZ.2.1.isLB d mu).pull (lift (𝟙 (GlobalTheory.ZarhinFam.Zob c.A B)) (𝟙 (GlobalTheory.ZarhinFam.Zob c.A B))).left) ∧ ∀ (T : Over S) (x : T ⟶ (GlobalTheory.ZarhinFam.Zob c.A B)), (∃ t : ((GlobalTheory.ZarhinFam.zP c.A B c.isLB hZ.2.1.isLB d mu).pull (lift (snd (GlobalTheory.ZarhinFam.Zob c.A B) T ≫ x) (fst (GlobalTheory.ZarhinFam.Zob c.A B) T)).left).Gen, t.IsGen) → x = 1 := by
  first | (exact @GlobalTheory.ZarhinFam.principal_zP) | (exact GlobalTheory.ZarhinFam.principal_zP) | (intros; apply GlobalTheory.ZarhinFam.principal_zP <;> assumption)
end
