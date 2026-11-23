module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle033
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1191
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1207
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle257
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle637
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle333
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1209
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1208
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
import Mathlib.RingTheory.RegularLocalRing.Defs
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

@[expose] public section

section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_pointwiseGenerator_of_dualNumberLineBundleGenerator : ∀ (R : Type) [CommRing R] (A B : Over (Sp R)) [GrpObj A] [GrpObj B] (P : LB (A ⊗ B).left), P.IsLB → ∀ v : epsR R ⟶ B, IsTangent v → ∀ T, IsEpsGen P v T → ∃ t, IsPtGen P (lift (fst A (epsR R)) (snd A (epsR R) ≫ v)) t := by
  first | exact @GlobalTheory.PtExt.exists_isPtGen_of_isEpsGen | exact GlobalTheory.PtExt.exists_isPtGen_of_isEpsGen | (intros; apply GlobalTheory.PtExt.exists_isPtGen_of_isEpsGen <;> assumption)
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc

namespace GlobalTheory.Nef.TanLoc

theorem ev_congr {R : Type} [CommRing R] {X : Scheme.{0}} {b b' : Sp R ⟶ X} (e : b = b') {U : X.Opens}
    (h : ⊤ ≤ b ⁻¹ᵁ U) (h' : ⊤ ≤ b' ⁻¹ᵁ U) (f : Γ(X, U)) : evAt b h f = evAt b' h' f := by
  subst e; rfl

theorem coeff_one_mul {E : Type} [CommRing E] (P Q : PowerSeries E) :
    PowerSeries.coeff 1 (P * Q) = PowerSeries.constantCoeff (R := E) P * PowerSeries.coeff 1 Q +
      PowerSeries.constantCoeff (R := E) Q * PowerSeries.coeff 1 P := by
  rw [PowerSeries.coeff_mul, Finset.Nat.antidiagonal_succ]
  simp [PowerSeries.coeff_zero_eq_constantCoeff_apply]
  ring

variable {S : Scheme.{0}} (G : Over S) [GrpObj G] {E : Type} [CommRing E] (b : Sp E ⟶ S) {n : ℕ}
  {V : S.Opens} (τ : Fin n → Γ(Lie G, V)) (w : Fin n → E)

theorem rhs_res {Ua Ub : G.left.Opens} (k : Ub ≤ Ua) {Va Vb : S.Opens} (hVa : Va ≤ V) (hVb : Vb ≤ V)
    (hab : Vb ≤ Va) (hea : Va ≤ unitSec G ⁻¹ᵁ Ua) (heb : Vb ≤ unitSec G ⁻¹ᵁ Ub) (hba : ⊤ ≤ b ⁻¹ᵁ Va)
    (hbb : ⊤ ≤ b ⁻¹ᵁ Vb) (g : Γ(G.left, Ua)) :
    ∑ i, w i * evAt b hbb (dualApp (τ i) hVb (dUnit G heb (G.left.presheaf.map (homOfLE k).op g))) =
      ∑ i, w i * evAt b hba (dualApp (τ i) hVa (dUnit G hea g)) := by
  obtain ⟨-, -, ev_res, -⟩ := GlobalTheory.T.evalSectionAtRingPoint_spMap_comp_restrict_stalk
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  have h1 : dUnit G heb (G.left.presheaf.map (homOfLE k).op g) = resM _ hab (dUnit G hea g) := by
    rw [resM_dUnit]; exact dUnit_resG G heb k g
  rw [h1]
  have h2 := dualApp_resM (τ i) hVa hab (dUnit G hea g)
  rw [h2]
  exact ev_res E S b Va Vb hab hba hbb _

theorem rhs_mul (ξ : Sp (PowerSeries E) ⟶ G.left)
    (hz : spMap (PowerSeries.constantCoeff (R := E)) ≫ ξ = b ≫ unitSec G) {U₂ : G.left.Opens}
    (hU₂ : ⊤ ≤ ξ ⁻¹ᵁ U₂) {V₂ : S.Opens} (hV₂ : V₂ ≤ V) (he₂ : V₂ ≤ unitSec G ⁻¹ᵁ U₂)
    (hb₂ : ⊤ ≤ b ⁻¹ᵁ V₂) (g k : Γ(G.left, U₂)) :
    ∑ i, w i * evAt b hb₂ (dualApp (τ i) hV₂ (dUnit G he₂ (g * k))) =
      PowerSeries.constantCoeff (R := E) (evAt ξ hU₂ g) * ∑ i, w i * evAt b hb₂ (dualApp (τ i) hV₂ (dUnit G he₂ k)) +
      PowerSeries.constantCoeff (R := E) (evAt ξ hU₂ k) * ∑ i, w i * evAt b hb₂ (dualApp (τ i) hV₂ (dUnit G he₂ g)) := by
  obtain ⟨ev_map, ev_comp, -, -⟩ := GlobalTheory.T.evalSectionAtRingPoint_spMap_comp_restrict_stalk
  have hc : ⊤ ≤ (b ≫ unitSec G) ⁻¹ᵁ U₂ := by
    intro x _
    show (b ≫ unitSec G) x ∈ U₂
    rw [← hz, Scheme.Hom.comp_apply]
    exact hU₂ (show _ ∈ (⊤ : (Sp (PowerSeries E)).Opens) from trivial)
  have hc' : ⊤ ≤ (spMap (PowerSeries.constantCoeff (R := E)) ≫ ξ) ⁻¹ᵁ U₂ := hz ▸ hc
  have hε : ∀ f : Γ(G.left, U₂), evAt b hb₂ ((unitSec G).appLE U₂ V₂ he₂ f) =
      PowerSeries.constantCoeff (R := E) (evAt ξ hU₂ f) := by
    intro f
    rw [← ev_comp E S G.left b (unitSec G) V₂ U₂ hb₂ hc he₂ f, ← ev_congr hz hc' hc,
      ev_map (PowerSeries E) E G.left (PowerSeries.constantCoeff (R := E)) ξ U₂ hU₂ hc' f]
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [dUnit_mul, map_add (f := _), LinearMap.map_smul, LinearMap.map_smul, smul_eq_mul, smul_eq_mul, map_add (f := _),
    map_mul, map_mul, hε, hε]
  ring

end GlobalTheory.Nef.TanLoc

namespace GlobalTheory.Nef


open TanLoc in
theorem hasTan_of_affine_chart : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (E : Type) [Field E] (c : E) (b : Sp E ⟶ S) (ξ : Sp (PowerSeries E) ⟶ G.left), IsPath G c b ξ → ∀ (n : ℕ) (V : S.Opens) (τ : Fin n → Γ(Lie G, V)) (w : Fin n → E) (U : G.left.Opens), IsAffineOpen U → ∀ (hU : ⊤ ≤ ξ ⁻¹ᵁ U) (V' : S.Opens) (hV : V' ≤ V) (he : V' ≤ unitSec G ⁻¹ᵁ U) (hb : ⊤ ≤ b ⁻¹ᵁ V'), (∀ f : Γ(G.left, U), PowerSeries.coeff 1 (evAt ξ hU f) = ∑ i, w i * evAt b hb (dualApp (τ i) hV (dUnit G he f))) → HasTan G b ξ τ w := by
  intro S G _ E _ c b ξ hξ n V τ w U hUa hU V' hV he hb H U₁ hU₁ V₁ hV₁ he₁ hb₁ f₁
  obtain ⟨-, -, ev_res, ev_loc, -⟩ := GlobalTheory.T.evalSectionAtRingPoint_spMap_comp_restrict_stalk
  have hyU := (ev_loc (PowerSeries E) G.left ξ U).1 hU
  have hyU₁ := (ev_loc (PowerSeries E) G.left ξ U₁).1 hU₁
  obtain ⟨t, htle, hyt⟩ := hUa.exists_basicOpen_le ⟨_, hyU₁⟩ hyU
  have hk : G.left.basicOpen t ≤ U := G.left.basicOpen_le t
  have hU₂ : ⊤ ≤ ξ ⁻¹ᵁ G.left.basicOpen t := (ev_loc (PowerSeries E) G.left ξ _).2 hyt
  have hV₂ : V' ⊓ V₁ ⊓ unitSec G ⁻¹ᵁ G.left.basicOpen t ≤ V := inf_le_left.trans (inf_le_left.trans hV)
  have he₂ : V' ⊓ V₁ ⊓ unitSec G ⁻¹ᵁ G.left.basicOpen t ≤ unitSec G ⁻¹ᵁ G.left.basicOpen t := inf_le_right
  have hb₂ : ⊤ ≤ b ⁻¹ᵁ (V' ⊓ V₁ ⊓ unitSec G ⁻¹ᵁ G.left.basicOpen t) := by
    intro x hx
    refine ⟨⟨hb hx, hb₁ hx⟩, ?_⟩
    show unitSec G (b x) ∈ G.left.basicOpen t
    rw [← Scheme.Hom.comp_apply, ← hξ.zero, Scheme.Hom.comp_apply]
    exact hU₂ (show _ ∈ (⊤ : (Sp (PowerSeries E)).Opens) from trivial)
  set L₂ : Γ(G.left, G.left.basicOpen t) → E := fun g => PowerSeries.coeff 1 (evAt ξ hU₂ g) with hL₂
  set R₂ : Γ(G.left, G.left.basicOpen t) → E :=
    fun g => ∑ i, w i * evAt b hb₂ (dualApp (τ i) hV₂ (dUnit G he₂ g)) with hR₂
  set ε : Γ(G.left, G.left.basicOpen t) →+* E := (PowerSeries.constantCoeff (R := E)).comp (evAt ξ hU₂) with hε
  have Lmul : ∀ g k, L₂ (g * k) = ε g * L₂ k + ε k * L₂ g := fun g k => by
    simp only [hL₂, hε, RingHom.comp_apply, map_mul, coeff_one_mul]
  have Rmul : ∀ g k, R₂ (g * k) = ε g * R₂ k + ε k * R₂ g := fun g k =>
    rhs_mul G b τ w ξ hξ.zero hU₂ hV₂ he₂ hb₂ g k
  have hA : ∀ g : Γ(G.left, U), L₂ (G.left.presheaf.map (homOfLE hk).op g) =
      R₂ (G.left.presheaf.map (homOfLE hk).op g) := by
    intro g
    simp only [hL₂, hR₂]
    rw [ev_res (PowerSeries E) G.left ξ U _ hk hU hU₂, H g,
      rhs_res G b τ w hk hV hV₂ (inf_le_left.trans inf_le_left) he he₂ hb hb₂ g]
  have hk₁ : G.left.basicOpen t ≤ U₁ := htle
  have hB : L₂ (G.left.presheaf.map (homOfLE hk₁).op f₁) = PowerSeries.coeff 1 (evAt ξ hU₁ f₁) ∧
      R₂ (G.left.presheaf.map (homOfLE hk₁).op f₁) =
        ∑ i, w i * evAt b hb₁ (dualApp (τ i) hV₁ (dUnit G he₁ f₁)) := by
    refine ⟨?_, ?_⟩
    · simp only [hL₂]; rw [ev_res (PowerSeries E) G.left ξ U₁ _ hk₁ hU₁ hU₂]
    · exact rhs_res G b τ w hk₁ hV₁ hV₂ (inf_le_left.trans inf_le_right) he₁ he₂ hb₁ hb₂ f₁
  rw [← hB.1, ← hB.2]
  have hl := hUa.isLocalization_basicOpen t
  obtain ⟨⟨a, s⟩, hs⟩ := IsLocalization.surj (Submonoid.powers t) (G.left.presheaf.map (homOfLE hk₁).op f₁)
  have hunit : IsUnit (algebraMap Γ(G.left, U) Γ(G.left, G.left.basicOpen t) (s : Γ(G.left, U))) :=
    IsLocalization.map_units _ s
  have hs' : algebraMap Γ(G.left, U) Γ(G.left, G.left.basicOpen t) = (G.left.presheaf.map (homOfLE hk).op).hom := rfl
  rw [hs'] at hs hunit
  have key := congrArg (fun z => L₂ z - R₂ z) hs
  simp only at key
  rw [Lmul, Rmul, hA a, hA s, sub_self] at key
  have hne : ε ((G.left.presheaf.map (homOfLE hk).op).hom s) ≠ 0 := (hunit.map ε).ne_zero
  have : ε ((G.left.presheaf.map (homOfLE hk).op).hom s) *
      (L₂ (G.left.presheaf.map (homOfLE hk₁).op f₁) - R₂ (G.left.presheaf.map (homOfLE hk₁).op f₁)) = 0 := by
    rw [← key]; ring
  exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_left hne)

end GlobalTheory.Nef
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc

namespace GlobalTheory.Nef

theorem den_along_path : ∀ (k E : Type) [Field k] [Field E] [Algebra k E] (p : Place k E) (u : E) (Y : Scheme.{0}) (ζ : Sp (PowerSeries p.O) ⟶ Y) (U : Y.Opens) (h : ⊤ ≤ (spMap (sc p u) ≫ ζ) ⁻¹ᵁ U) (f : Γ(Y, U)), ∃ e ψ : PowerSeries p.O, PowerSeries.constantCoeff e ≠ 0 ∧ (⊤ ≤ ζ ⁻¹ᵁ U → e = 1) ∧ sc p u e * evAt (spMap (sc p u) ≫ ζ) h f = sc p u ψ := by
  intro k E _ _ _ p u Y ζ U h f
  obtain ⟨hcomp, -, hres, hloc, -⟩ := GlobalTheory.T.evalSectionAtRingPoint_spMap_comp_restrict_stalk
  by_cases hU : ⊤ ≤ ζ ⁻¹ᵁ U
  · refine ⟨1, evAt ζ hU f, by simp, fun _ => rfl, ?_⟩
    rw [map_one, _root_.one_mul, hcomp (PowerSeries p.O) (PowerSeries E) Y (sc p u) ζ U hU h f]
  · obtain ⟨_, ⟨U₀, hU₀, rfl⟩, hy0, -⟩ := Y.isBasis_affineOpens.exists_subset_of_mem_open
      (Set.mem_univ (ζ (IsLocalRing.closedPoint (PowerSeries p.O)))) isOpen_univ
    have hζ0 : ⊤ ≤ ζ ⁻¹ᵁ U₀ := (hloc _ _ _ _).2 hy0
    have hη0 : ⊤ ≤ (spMap (sc p u) ≫ ζ) ⁻¹ᵁ U₀ := fun x _ => hζ0 (Set.mem_univ ((spMap (sc p u)) x))
    have hyU := (hloc _ _ _ _).1 h
    have hyU₀ := (hloc _ _ _ _).1 hη0
    obtain ⟨t, htU, hyt⟩ := hU₀.exists_basicOpen_le (V := U) ⟨_, hyU⟩ hyU₀
    have hηt : ⊤ ≤ (spMap (sc p u) ≫ ζ) ⁻¹ᵁ Y.basicOpen t := (hloc _ _ _ _).2 hyt
    haveI := hU₀.isLocalization_basicOpen t
    obtain ⟨⟨a, ⟨_, n, rfl⟩⟩, hmk⟩ := IsLocalization.mk'_surjective (Submonoid.powers t)
      (Y.presheaf.map (homOfLE htU).op f)
    have hspec := IsLocalization.mk'_spec Γ(Y, Y.basicOpen t) a (⟨t ^ n, n, rfl⟩ : Submonoid.powers t)
    simp only at hmk
    rw [hmk] at hspec
    have hle : Y.basicOpen t ≤ U₀ := Y.basicOpen_le t
    have key : evAt (spMap (sc p u) ≫ ζ) hηt (Y.presheaf.map (homOfLE htU).op f) *
        evAt (spMap (sc p u) ≫ ζ) hηt (Y.presheaf.map (homOfLE hle).op (t ^ n)) =
        evAt (spMap (sc p u) ≫ ζ) hηt (Y.presheaf.map (homOfLE hle).op a) := by
      rw [← map_mul]; exact congrArg _ hspec
    have h1 := hres _ _ _ _ _ htU h hηt f
    have h2 := hres _ _ _ _ _ hle hη0 hηt (t ^ n)
    have h3 := hres _ _ _ _ _ hle hη0 hηt a
    have hu : IsUnit (evAt (spMap (sc p u) ≫ ζ) hηt (Y.presheaf.map (homOfLE hle).op t)) :=
      (Y.toRingedSpace.isUnit_res_basicOpen t).map _
    refine ⟨evAt ζ hζ0 (t ^ n), evAt ζ hζ0 a, ?_, fun h' => absurd h' hU, ?_⟩
    · intro h0
      have hu' : IsUnit (sc p u (evAt ζ hζ0 (t ^ n))) := by
        rw [← hcomp (PowerSeries p.O) (PowerSeries E) Y (sc p u) ζ U₀ hζ0 hη0, ← h2, map_pow, map_pow]
        exact hu.pow n
      rw [PowerSeries.isUnit_iff_constantCoeff] at hu'
      apply hu'.ne_zero
      rw [sc, RingHom.comp_apply, ← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_rescale,
        PowerSeries.coeff_map, PowerSeries.coeff_zero_eq_constantCoeff_apply, h0]
      simp
    · rw [← hcomp (PowerSeries p.O) (PowerSeries E) Y (sc p u) ζ U₀ hζ0 hη0, ← hcomp (PowerSeries p.O) (PowerSeries E) Y (sc p u) ζ U₀ hζ0 hη0, ← h1, ← h2, ← h3, ← key]
      exact mul_comm _ _

end GlobalTheory.Nef
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc

namespace GlobalTheory.Nef

theorem path_bc_ring {S : Scheme.{0}} (G : Over S) [GrpObj G] {R : Type} [CommRing R] {R' : Type} [CommRing R']
    (φ : R →+* R') (c : R) (u : R') (b : Sp R ⟶ S) (ξ : Sp (PowerSeries R) ⟶ G.left) (h : IsPath G c b ξ) :
    IsPath G (φ c) (spMap φ ≫ b) (spMap ((PowerSeries.rescale u).comp (PowerSeries.map φ)) ≫ ξ) := by
  have hC : ((PowerSeries.rescale u).comp (PowerSeries.map φ)).comp (PowerSeries.C (R := R)) =
      (PowerSeries.C (R := R')).comp φ := by
    ext a n
    simp [PowerSeries.coeff_C]
    split_ifs <;> simp_all
  have h0 : (PowerSeries.constantCoeff (R := R')).comp ((PowerSeries.rescale u).comp (PowerSeries.map φ)) =
      φ.comp (PowerSeries.constantCoeff (R := R)) := by
    ext p
    simp only [RingHom.comp_apply]
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, ← PowerSeries.coeff_zero_eq_constantCoeff_apply,
      PowerSeries.coeff_rescale, PowerSeries.coeff_map]
    simp
  have hs : (PowerSeries.rescale (φ c)).comp ((PowerSeries.rescale u).comp (PowerSeries.map φ)) =
      ((PowerSeries.rescale u).comp (PowerSeries.map φ)).comp (PowerSeries.rescale c) := by
    ext p n
    simp [PowerSeries.coeff_rescale, PowerSeries.coeff_map]
    ring
  refine ⟨?_, ?_, ?_⟩
  · rw [Category.assoc, h.base, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hC,
      CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]
  · rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, h0, CommRingCat.ofHom_comp, Spec.map_comp,
      Category.assoc, h.zero, Category.assoc]
  · rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hs, CommRingCat.ofHom_comp, Spec.map_comp,
      Category.assoc, h.scale, Category.assoc]

theorem unitSec_comp {S : Scheme.{0}} {G H : Over S} [GrpObj G] [GrpObj H] (q : G ⟶ H) [IsMonHom q] :
    unitSec G ≫ q.left = unitSec H := by
  show (η[G]).left ≫ q.left = (η[H]).left
  rw [← Over.comp_left, IsMonHom.one_hom]

theorem sqr_comp {S : Scheme.{0}} {G H : Over S} [GrpObj G] [GrpObj H] (q : G ⟶ H) [IsMonHom q] :
    sqr G ≫ q.left = q.left ≫ sqr H := by
  unfold sqr
  rw [← Over.comp_left, ← Over.comp_left, MonObj.mul_comp, MonObj.comp_mul, Category.id_comp, Category.comp_id]

end GlobalTheory.Nef

theorem GlobalTheory.Nef.paths_bc : (∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (R : Type) [CommRing R], ∀ (R' : Type) [CommRing R'] (φ : R →+* R') (c : R) (u : R') (b : Sp R ⟶ S) (ξ : Sp (PowerSeries R) ⟶ G.left), IsPath G c b ξ → IsPath G (φ c) (spMap φ ≫ b) (spMap ((PowerSeries.rescale u).comp (PowerSeries.map φ)) ≫ ξ) ∧ ∀ [IsLocalRing R] (n : ℕ) (V : S.Opens) (τ : Fin n → Γ(Lie G, V)) (w : Fin n → R), ⊤ ≤ b ⁻¹ᵁ V → ∀ (U : G.left.Opens) (hU : ⊤ ≤ ξ ⁻¹ᵁ U), HasTan G b ξ τ w → ∀ (hU' : ⊤ ≤ (spMap ((PowerSeries.rescale u).comp (PowerSeries.map φ)) ≫ ξ) ⁻¹ᵁ U) (V' : S.Opens) (hV : V' ≤ V) (he : V' ≤ unitSec G ⁻¹ᵁ U) (hb : ⊤ ≤ b ⁻¹ᵁ V') (f : Γ(G.left, U)), PowerSeries.coeff 1 (evAt (spMap ((PowerSeries.rescale u).comp (PowerSeries.map φ)) ≫ ξ) hU' f) = ∑ i, u * φ (w i) * φ (evAt b hb (dualApp (τ i) hV (dUnit G he f)))) ∧ (∀ (S : Scheme.{0}) (G H : Over S) [GrpObj G] [GrpObj H] (q : G ⟶ H) [IsMonHom q] (R : Type) [CommRing R] (c : R) (b : Sp R ⟶ S) (ξ : Sp (PowerSeries R) ⟶ G.left), (IsPath G c b ξ → IsPath H c b (ξ ≫ q.left)) ∧ triv G b ≫ q.left = triv H b ∧ sqr G ≫ q.left = q.left ≫ sqr H) := by
  refine ⟨?_, ?_⟩
  · intro S G _ R _ R' _ φ c u b ξ h
    refine ⟨path_bc_ring G φ c u b ξ h, ?_⟩
    intro _ n V τ w _ U hU ht hU' V' hV he hb f
    rw [(GlobalTheory.T.evalSectionAtRingPoint_spMap_comp_restrict_stalk).1 (PowerSeries R) (PowerSeries R') G.left ((PowerSeries.rescale u).comp (PowerSeries.map φ)) ξ U hU hU' f]

    rw [RingHom.comp_apply, PowerSeries.coeff_rescale, PowerSeries.coeff_map, ht U hU V' hV he hb f, map_sum,
    Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, pow_one, ← _root_.mul_assoc]
  · intro S G H _ _ q _ R _ c b ξ
    refine ⟨fun h => ⟨?_, ?_, ?_⟩, ?_, sqr_comp q⟩
    · rw [Category.assoc, Over.w q, h.base]
    · rw [← Category.assoc, h.zero, Category.assoc, unitSec_comp]
    · rw [← Category.assoc, h.scale, Category.assoc, Category.assoc, sqr_comp]
    · rw [triv, Category.assoc, Category.assoc, unitSec_comp, triv]
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc

namespace GlobalTheory.Nef

theorem isRatPath_of_isRat : ∀ (F : Type) [Field F] (Y : Scheme.{0}) (ξ : Sp (PowerSeries F) ⟶ Y),
    (∀ (U : Y.Opens), IsAffineOpen U → ∀ (h : ⊤ ≤ ξ ⁻¹ᵁ U) (f : Γ(Y, U)), IsRat (evAt ξ h f)) → IsRatPath ξ := by
  intro F _ Y ξ hrat
  obtain ⟨h1, -, -, h4, h5, h6, -⟩ := GlobalTheory.T.evalSectionAtRingPoint_spMap_comp_restrict_stalk
  obtain ⟨U, hUa, hy, -⟩ := (Opens.isBasis_iff_nbhd.mp Y.isBasis_affineOpens)
    (show ξ (IsLocalRing.closedPoint (PowerSeries F)) ∈ (⊤ : Y.Opens) from trivial)
  have hξ : ⊤ ≤ ξ ⁻¹ᵁ U := (h4 _ Y ξ U).2 hy
  set ψ := evAt ξ hξ
  set ιR := algebraMap (RatFunc F) (LaurentSeries F)
  set ιP := algebraMap (PowerSeries F) (LaurentSeries F)
  have hR : Function.Injective ιR := ιR.injective
  have hmem : ∀ f, (ιP.comp ψ) f ∈ ιR.range := fun f => by
    obtain ⟨ρ, hρ⟩ := (isRat_iff_exists_ratFunc F (ψ f)).1 (hrat U hUa hξ f)
    exact ⟨ρ, hρ⟩
  let e := RingEquiv.ofBijective ιR.rangeRestrict ⟨fun a b hab => hR (congrArg Subtype.val hab), ιR.rangeRestrict_surjective⟩
  let φ : Γ(Y, U) →+* RatFunc F := e.symm.toRingHom.comp ((ιP.comp ψ).codRestrict ιR.range hmem)
  have hφ : ∀ f, ιR (φ f) = ιP (ψ f) := fun f => by
    have := congrArg Subtype.val (e.apply_symm_apply ((ιP.comp ψ).codRestrict ιR.range hmem f))
    exact this
  obtain ⟨β, hβ, hβφ⟩ := h6 (RatFunc F) Y U hUa φ
  refine ⟨β, ?_⟩
  have ha : ⊤ ≤ (spMap ιR ≫ β) ⁻¹ᵁ U := fun x _ => hβ (Set.mem_univ ((spMap ιR) x))
  have hb : ⊤ ≤ (spMap ιP ≫ ξ) ⁻¹ᵁ U := fun x _ => hξ (Set.mem_univ ((spMap ιP) x))
  refine h5 (LaurentSeries F) Y _ _ U hUa ha hb ?_
  refine RingHom.ext fun f => ?_
  rw [h1 _ _ Y ιR β U hβ ha f, h1 _ _ Y ιP ξ U hξ hb f, hβφ]
  exact hφ f

end GlobalTheory.Nef
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc

namespace GlobalTheory.Nef

theorem evAt_congr' {R : Type} [CommRing R] {X : Scheme.{0}} {ξ ξ' : Sp R ⟶ X} (e : ξ = ξ') {U : X.Opens}
    (h : ⊤ ≤ ξ ⁻¹ᵁ U) (h' : ⊤ ≤ ξ' ⁻¹ᵁ U) (f : Γ(X, U)) : evAt ξ h f = evAt ξ' h' f := by
  subst e; rfl

theorem top_le_preimage_comp' {X Y Z : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) (U : Z.Opens) (h : ⊤ ≤ g ⁻¹ᵁ U) :
    ⊤ ≤ (f ≫ g) ⁻¹ᵁ U := by
  intro z _
  exact h (Set.mem_univ (f z))

theorem finite_centre_not_mem (k K E : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field K] [Algebra k K] [Field E]
    [Algebra k E] [Algebra K E] [IsScalarTower k K E] [FiniteDimensional K E] (C : Scheme.{0}) [Algebra k Γ(C, ⊤)]
    (x : Sp K ⟶ C) (hx : IsGenOver k x) (V : C.Opens) (hV : (V : Set C).Nonempty) :
    {p : Place k E | ∃ b : Sp p.O ⟶ C, spMap p.O.subtype ≫ b = spMap (algebraMap K E) ≫ x ∧ ¬ ⊤ ≤ b ⁻¹ᵁ V}.Finite := by
  have hC := hx.1
  haveI : IsIntegral C := GlobalTheory.LieSemineg.isIntegral_curve hC.1 hC.2.2
  obtain ⟨z, hz⟩ := hV
  obtain ⟨V', hV'a, hzV', hV'V⟩ := Opens.isBasis_iff_nbhd.1 C.isBasis_affineOpens hz
  have hV'a : IsAffineOpen V' := hV'a
  obtain ⟨hxV', -, -⟩ := GlobalTheory.T.evalSectionAtRingPoint_generic_injective_fraction K C x hx.2.1 V' ⟨z, hzV'⟩
  obtain ⟨ev1, ev2, -, -, ev5, ev6, -⟩ := GlobalTheory.T.evalSectionAtRingPoint_spMap_comp_restrict_stalk
  let f : Γ(C, V') →+* E := (algebraMap K E).comp (evAt x hxV')
  haveI := hC.1
  haveI : Smooth (strHom k (X := C)) := SmoothOfRelativeDimension.smooth 1 _
  have eV : V' ≤ strHom k C ⁻¹ᵁ ⊤ := fun _ _ => trivial
  let ψ := ((strHom k C).appLE ⊤ V' eV).hom
  have hft : ψ.FiniteType :=
    HasRingHomProperty.appLE (P := @LocallyOfFiniteType) (strHom k C) inferInstance
      ⟨⊤, isAffineOpen_top _⟩ ⟨V', hV'a⟩ eV
  letI := ψ.toAlgebra
  obtain ⟨s, hs⟩ := hft.out

  have hconst : ∀ (p : Place k E) (c : Γ(Sp k, ⊤)), p.1 (f (ψ c)) ≤ 1 := by
    intro p c
    have hxs : ⊤ ≤ (x ≫ strHom k C) ⁻¹ᵁ (⊤ : (Sp k).Opens) := top_le_preimage_comp' x (strHom k C) ⊤ (fun _ _ => trivial)
    have htop : ⊤ ≤ (𝟙 (Sp k)) ⁻¹ᵁ (⊤ : (Sp k).Opens) := fun _ _ => trivial
    have h1 : evAt x hxV' (ψ c) = evAt (x ≫ strHom k C) hxs c :=
      (ev2 K C (Sp k) x (strHom k C) V' ⊤ hxV' _ eV c).symm
    have h2 : evAt (x ≫ strHom k C) hxs c =
        evAt (spMap (algebraMap k K) ≫ 𝟙 (Sp k)) (top_le_preimage_comp' _ _ _ htop) c :=
      evAt_congr' (by rw [Category.comp_id]; exact hx.2.2) _ _ c
    have h3 := ev1 k K (Sp k) (algebraMap k K) (𝟙 (Sp k)) ⊤ htop (top_le_preimage_comp' _ _ _ htop) c
    have hf : f (ψ c) = algebraMap k E (evAt (𝟙 (Sp k)) htop c) := by
      simp only [f, RingHom.comp_apply]
      rw [h1, h2, h3, ← IsScalarTower.algebraMap_apply]
    rw [hf]
    by_cases hd : evAt (𝟙 (Sp k)) htop c = 0
    · rw [hd, map_zero, map_zero]; exact zero_le'
    · exact (p.2.2 _ hd).le
  have key : ∀ p : Place k E, (∀ a ∈ s, p.1 (f a) ≤ 1) → ∀ g, p.1 (f g) ≤ 1 := by
    intro p hp g
    have hg : g ∈ Algebra.adjoin Γ(Sp k, ⊤) (s : Set Γ(C, V')) := by rw [hs]; trivial
    induction hg using Algebra.adjoin_induction with
    | mem a ha => exact hp a ha
    | algebraMap c => exact hconst p c
    | add a b _ _ ha hb => rw [map_add (f := _)]; exact (p.1.map_add _ _).trans (max_le ha hb)
    | mul a b _ _ ha hb => rw [map_mul, map_mul]; exact mul_le_one' ha hb
  have hE : IsFF k E := (GlobalTheory.T.functionFieldOneVariable_transcendental_finite_and_ext k K (GlobalTheory.T.isFunctionFieldOfOneVariable_of_genericPointOfCurve k K C x hx)).2 E
  refine ((s.finite_toSet.biUnion fun a _ => (?_ : {p : Place k E | ¬ p.1 (f a) ≤ 1}.Finite))).subset ?_
  · by_cases h0 : f a = 0
    · simpa [h0] using (Set.finite_empty : (∅ : Set (Place k E)).Finite)
    · exact (GlobalTheory.T.functionField_finite_support_sum_order_eq_zero k E hE (f a) h0).1.subset fun p hp h1 => hp h1.le
  · rintro p ⟨b, hb1, hb2⟩
    simp only [Set.mem_iUnion, Set.mem_setOf_eq]
    by_contra hno
    push_neg at hno
    have hall := key p fun a ha => hno a ha
    have hmem : ∀ g, f g ∈ p.O := fun g => (Valuation.mem_valuationSubring_iff _ _).2 (hall g)
    let φ : Γ(C, V') →+* p.O := f.codRestrict p.O hmem
    obtain ⟨b', hb', hev⟩ := ev6 p.O C V' hV'a φ
    have hc := top_le_preimage_comp' (spMap p.O.subtype) b' V' hb'
    have hd := top_le_preimage_comp' (spMap (algebraMap K E)) x V' hxV'
    have hcd : spMap p.O.subtype ≫ b' = spMap (algebraMap K E) ≫ x := by
      refine ev5 E C _ _ V' hV'a hc hd ?_
      ext g
      rw [ev1 p.O E C p.O.subtype b' V' hb' hc g, ev1 K E C (algebraMap K E) x V' hxV' hd g, hev]
      rfl
    have hbb := (GlobalTheory.T.existsUnique_centre_functionFieldPlace_curve k K E C x hx p).unique hb1 hcd
    subst hbb
    exact hb2 fun w hw => hV'V (hb' hw)

end GlobalTheory.Nef
end
end

section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PtExt

theorem exists_isSecAdd : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] [IsCommMonObj A] (n : ℕ),
    HasRoots (A := A) n → ∀ b : Fn0 A, IsTorsChar n b → ∀ S : SecFam A,
    (∀ (D : Type) [CommRing D] [Algebra R D] (x : Pt A D), IsSec n b x (S D x)) → ∃ g : Fn2 A, IsSecAdd n S g := by
  intro R _ A _ _ n hr b hb S hS
  have difference (D : Type) [CommRing D] [Algebra R D] (x y : Pt A D) :=
    (GlobalTheory.sec_mul_diff R A n hr b hb D x y (S D x) (S D y) (S D (x * y))
      (hS D x) (hS D y) (hS D (x * y))).exists
  refine ⟨fun D _ _ x y ↦ (difference D x y).choose, ?_⟩
  intro D _ _ x y E _ _ ψ z w hz hw
  exact ((difference D x y).choose_spec E ψ z w hz hw).symm

end GlobalTheory.PtExt
end

section

theorem GlobalTheory.T.existsUnique_pushoutTorsorSection_mul_difference :
    type_of% @GlobalTheory.sec_mul_diff :=
  @GlobalTheory.sec_mul_diff
end

section

open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.DualWeyl GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.DefPt MvPolynomial
open scoped Matrix

theorem _root_.GlobalTheory.T.fibre_action_preserves_adelic_matrices : ∀ (K : Type) [Field K] [NumberField K] (T : Type) [Fintype T] [DecidableEq T] (N : T → ℕ) (la : ∀ t, Fin (N t) → ℕ) (a : HeightOneSpectrum (𝓞 K) → K) (B : HeightOneSpectrum (𝓞 K) → ∀ t, Matrix (Fin (N t)) (Fin (N t)) K), (∀ w, a w ≠ 0) → (Function.support fun w => vAdd w (a w)).Finite → (∀ t, IsAdelic fun w => B w t) → IsAdelic fun w => fibA la (a w) (B w) := by
  first | exact @GlobalTheory.FibAdel.fibA_isAdelic | exact GlobalTheory.FibAdel.fibA_isAdelic | (intros; apply GlobalTheory.FibAdel.fibA_isAdelic <;> assumption)
end
