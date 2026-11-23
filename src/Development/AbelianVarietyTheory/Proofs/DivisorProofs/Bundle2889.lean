module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle004
import Mathlib.Algebra.Module.StablyFree.Basic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2008
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ConstGen
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2689
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2278
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2764
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle104
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSecImageNonzeroLocus
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.RelAmpleExternalTensorPowerGroupPower
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle008
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThickTransComp
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle108
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Lemma
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle013
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle029
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle005
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.EqOneOfUnimodular

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
namespace GlobalTheory.ConstDescent

open TensorProduct

theorem mem_range_of_tmul_one_eq {K L B : Type} [Field K] [Field L] [CommRing B] [Algebra K L]
    [Algebra K B] (b₁ b₂ : B) (l : L) (hb : b₂ ≠ 0) (h : b₁ ⊗ₜ[K] (1 : L) = b₂ ⊗ₜ[K] l) :
    l ∈ Set.range (algebraMap K L) := by
  by_contra hl
  have hx : l ∉ (K ∙ (1 : L)) := by
    intro hm
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 hm
    exact hl ⟨c, by rw [Algebra.algebraMap_eq_smul_one, hc]⟩
  obtain ⟨f, hf, hp⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hx inferInstance
  have h1 : f 1 = 0 := by
    have : f 1 ∈ (K ∙ (1 : L)).map f :=
      Submodule.mem_map_of_mem (Submodule.mem_span_singleton_self 1)
    rw [hp] at this
    simpa using this
  have h2 := congrArg ((TensorProduct.rid K B).toLinearMap ∘ₗ LinearMap.lTensor B f) h
  simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
    LinearMap.lTensor_tmul, TensorProduct.rid_tmul, h1, zero_smul] at h2
  exact hb ((smul_eq_zero.1 h2.symm).resolve_left hf)

end GlobalTheory.ConstDescent

namespace GlobalTheory.ConstDescent

theorem exists_affine_res_ne_zero {X : Scheme.{0}} {U : X.Opens} (f : Γ(X, U)) (hf : f ≠ 0) :
    ∃ (V : X.Opens) (hV : IsAffineOpen V) (hVU : V ≤ U), X.presheaf.map (homOfLE hVU).op f ≠ 0 := by
  have : ∃ (x : X) (hx : x ∈ U), X.presheaf.germ U x hx f ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hf (TopCat.Presheaf.section_ext X.sheaf U f 0 (fun x hx => by rw [map_zero]; exact hc x hx))
  obtain ⟨x, hx, hne⟩ := this
  obtain ⟨V, hV, hxV, hVU⟩ := exists_isAffineOpen_mem_and_subset (x := x) (U := U) hx
  refine ⟨V, hV, hVU, fun h0 => hne ?_⟩
  rw [← TopCat.Presheaf.germ_res_apply X.presheaf (homOfLE hVU) x hxV, h0, map_zero]

end GlobalTheory.ConstDescent

namespace GlobalTheory.ConstDescent

theorem fromSpec_appLE_hom {X : Scheme.{0}} {U V : X.Opens} (hV : IsAffineOpen V) (hVU : V ≤ U)
    (e : ⊤ ≤ hV.fromSpec ⁻¹ᵁ U) (f : Γ(X, U)) :
    (Scheme.ΓSpecIso Γ(X, V)).hom.hom ((hV.fromSpec.appLE U ⊤ e).hom f) =
      (X.presheaf.map (homOfLE hVU).op).hom f := by
  have : hV.fromSpec.appLE U ⊤ e ≫ (Scheme.ΓSpecIso Γ(X, V)).hom =
      X.presheaf.map (homOfLE hVU).op := by
    rw [Scheme.Hom.appLE, IsAffineOpen.fromSpec_app_of_le hV U hVU, Category.assoc, Category.assoc,
      Category.assoc, ← Functor.map_comp_assoc]
    have h' : ((homOfLE le_top).op ≫ (homOfLE e).op :
        Opposite.op (⊤ : (Spec Γ(X, V)).Opens) ⟶ Opposite.op ⊤) = 𝟙 _ := Subsingleton.elim _ _
    rw [h', CategoryTheory.Functor.map_id, Category.id_comp, Iso.inv_hom_id, Category.comp_id]
  rw [← this]
  rfl

theorem appLE_top_top {X Y : Scheme.{0}} (f : X ⟶ Y) (e : (⊤ : X.Opens) ≤ f ⁻¹ᵁ ⊤) :
    f.appLE ⊤ ⊤ e = f.appTop := by
  rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
  rfl

theorem appLE_congr {X Y : Scheme.{0}} {f g : X ⟶ Y} (hfg : f = g) (U : Y.Opens) (V : X.Opens)
    (e₁ : V ≤ f ⁻¹ᵁ U) (e₂ : V ≤ g ⁻¹ᵁ U) : f.appLE U V e₁ = g.appLE U V e₂ := by
  subst hfg; rfl

end GlobalTheory.ConstDescent

namespace GlobalTheory.ConstDescent

open TensorProduct

theorem mem_range_of_pullback_eq {K L : Type} [Field K] [Field L] (ψ : K →+* L) {X : Scheme.{0}}
    (h : X ⟶ Sp K) (U : X.Opens) (f₁ f₂ : Γ(X, U)) (l : L) (hf : f₂ ≠ 0)
    (heq : ((pullback.fst h (spMap ψ)).app U).hom f₁ =
      ((pullback.fst h (spMap ψ)).app U).hom f₂ * resTop _ (scal (pullback.snd h (spMap ψ)) l)) :
    l ∈ Set.range ψ := by
  obtain ⟨V, hV, hVU, hne⟩ := exists_affine_res_ne_zero f₂ hf
  let B : CommRingCat := Γ(X, V)
  let e : Spec B ⟶ X := hV.fromSpec
  let α : CommRingCat.of K ⟶ B := Spec.preimage (e ≫ h)
  letI : Algebra K B := α.hom.toAlgebra
  letI : Algebra K L := ψ.toAlgebra
  let Z : CommRingCat := CommRingCat.of (B ⊗[K] L)
  let a : Spec Z ⟶ Spec B := Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom)
  let b : Spec Z ⟶ Sp L :=
    Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight : L →ₐ[K] B ⊗[K] L).toRingHom)
  have hcomm : (a ≫ e) ≫ h = b ≫ spMap ψ := by
    rw [Category.assoc, ← Spec.map_preimage (e ≫ h)]
    simp only [a, b, spMap, ← Spec.map_comp]
    congr 1
    ext x
    show (algebraMap K B x) ⊗ₜ[K] (1 : L) = (1 : B) ⊗ₜ[K] (algebraMap K L x)
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
  let k : Spec Z ⟶ pullback h (spMap ψ) := pullback.lift (a ≫ e) b hcomm
  have hk1 : k ≫ pullback.fst h (spMap ψ) = a ≫ e := pullback.lift_fst _ _ _
  have hk2 : k ≫ pullback.snd h (spMap ψ) = b := pullback.lift_snd _ _ _
  have heU : ⊤ ≤ e ⁻¹ᵁ U := by
    intro z _
    show e z ∈ U
    apply hVU
    have hr : e z ∈ Set.range hV.fromSpec := ⟨z, rfl⟩
    rw [hV.range_fromSpec] at hr
    exact hr
  have hk : ⊤ ≤ k ⁻¹ᵁ ((pullback.fst h (spMap ψ)) ⁻¹ᵁ U) := by
    intro z _
    show (pullback.fst h (spMap ψ)) (k z) ∈ U
    rw [← Scheme.Hom.comp_apply, hk1, Scheme.Hom.comp_apply]
    exact heU (show a z ∈ (⊤ : (Spec B).Opens) from trivial)

  have heU' : ⊤ ≤ (a ≫ e) ⁻¹ᵁ U := by
    intro z _
    exact heU (show a z ∈ (⊤ : (Spec B).Opens) from trivial)
  have key1m : (pullback.fst h (spMap ψ)).app U ≫ k.appLE _ ⊤ hk =
      e.appLE U ⊤ heU ≫ (Scheme.ΓSpecIso B).hom ≫
        CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom ≫ (Scheme.ΓSpecIso Z).inv := by
    refine (Scheme.Hom.comp_appLE k _ U ⊤ hk).symm.trans ?_
    refine (appLE_congr hk1 U ⊤ _ heU').trans ?_
    refine (Scheme.Hom.appLE_comp_appLE a e U ⊤ ⊤ heU (fun _ _ => trivial)).symm.trans ?_
    congr 1
    refine (appLE_top_top a _).trans ?_
    rw [← Category.assoc, Iso.eq_comp_inv]
    exact Scheme.ΓSpecIso_naturality _
  have key2m : (Scheme.ΓSpecIso (CommRingCat.of L)).inv ≫ (pullback.snd h (spMap ψ)).appTop ≫
      k.appTop = CommRingCat.ofHom (Algebra.TensorProduct.includeRight : L →ₐ[K] B ⊗[K] L).toRingHom ≫
        (Scheme.ΓSpecIso Z).inv := by
    rw [← Scheme.Hom.comp_appTop, hk2, ← Scheme.ΓSpecIso_inv_naturality]
  have key1 : ∀ s : Γ(X, U), (k.appLE _ ⊤ hk).hom (((pullback.fst h (spMap ψ)).app U).hom s) =
      (Scheme.ΓSpecIso Z).inv.hom
        (((Scheme.ΓSpecIso B).hom.hom ((e.appLE U ⊤ heU).hom s)) ⊗ₜ[K] (1 : L)) := fun s =>
    congrArg (fun φ => φ.hom s) key1m
  have key2 : (k.appLE _ ⊤ hk).hom (resTop _ (scal (pullback.snd h (spMap ψ)) l)) =
      (Scheme.ΓSpecIso Z).inv.hom ((1 : B) ⊗ₜ[K] l) := by
    have e1 : ∀ c, (k.appLE _ ⊤ hk).hom (resTop ((pullback.fst h (spMap ψ)) ⁻¹ᵁ U) c) =
        k.appTop.hom c := by
      intro c
      show ((pullback h (spMap ψ)).presheaf.map _ ≫ k.appLE _ ⊤ hk).hom c = _
      rw [Scheme.Hom.map_appLE, appLE_top_top]
    rw [e1]
    exact congrArg (fun φ => φ.hom l) key2m
  have h3 := congrArg (k.appLE _ ⊤ hk).hom heq
  rw [map_mul, key1, key1, key2, ← map_mul, Algebra.TensorProduct.tmul_mul_tmul, _root_.mul_one,
    _root_.one_mul] at h3
  have inj : Function.Injective (Scheme.ΓSpecIso Z).inv.hom := fun x y hxy => by
    simpa using congrArg (Scheme.ΓSpecIso Z).hom.hom hxy
  have h4 := inj h3
  have hb : (Scheme.ΓSpecIso B).hom.hom ((e.appLE U ⊤ heU).hom f₂) ≠ 0 := by
    rw [fromSpec_appLE_hom hV hVU heU f₂]
    exact hne
  obtain ⟨c, hc⟩ := mem_range_of_tmul_one_eq _ _ l hb h4
  exact ⟨c, hc⟩

end GlobalTheory.ConstDescent
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum

def IsPullPt {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {φ : R →+* R'} {D : DegPre R} {D' : DegPre R'}
    (hD : IsPullDeg φ D D') {T : Over (Sp R)} {T' : Over (Sp R')} (h : T'.left ⟶ T.left) (ξ : GtPt D T) (ξ' : GtPt D' T') : Prop :=
  ξ'.b.left ≫ hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ) = h ≫ ξ.b.left ∧
  ∀ χ : D'.X, ∃ hψ : ∀ κ : Fin 4,
      DegPre.gtφT D' T' ξ'.b χ κ ≫ hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ) = h ≫ DegPre.gtφT D T ξ.b (hD.xe χ) κ,
    LB.Gen.Maps (LB.linCombIso hD.w _ DegPre.gtε) (ξ'.s χ)
      (GeneratorPullback.pullAlong D.P.L (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)) h _ DegPre.gtε _ hψ (ξ.s (hD.xe χ)))

end GlobalTheory.Mum
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.uniformisation_transfer_isPullDeg_id : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R), AdmBase R I → ∀ (D D' : DegData R I), Nonempty (IsPullDeg (RingHom.id R) D.toPre D'.toPre) → ∀ (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → (∀ U' : Unif I D' A G, ∃ U : Unif I D A G, U.LG = U'.LG ∧ U.gen = U'.gen) ∧ ∀ U : Unif I D A G, ∃ U' : Unif I D' A G, U'.LG = U.LG ∧ U'.gen = U.gen := by
  first | exact @GlobalTheory.Mum.UnifMove.unif_move | exact GlobalTheory.Mum.UnifMove.unif_move | (intros; apply GlobalTheory.Mum.UnifMove.unif_move <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

namespace GlobalTheory.WeilGeomPt

theorem exists_weilIs_geomPt : ∀ (S : Scheme.{0}) (B : Over S) [GrpObj B] [IsCommMonObj B] (M : LB B.left), IsAbelianScheme B → M.IsLB → ∀ (κ : Type) [Field κ] [IsAlgClosed κ] (x : Sp κ ⟶ S) (n : ℕ), 0 < n → (n : κ) ≠ 0 → ∀ y y' : Over.mk x ⟶ B, y ^ n = 1 → y' ^ n = 1 → ∃ e : (Γ((Over.mk x).left, ⊤))ˣ, Out.WeilIs B M n y y' e := by
  intro S B _ _ M hA hM κ _ _ x n _ _ y y' hy hy'
  obtain ⟨e, -, he⟩ := GlobalTheory.HolTorsionAny.exists_weilIs_pow_eq_one hA hM hy hy'
  exact ⟨e, he⟩

end GlobalTheory.WeilGeomPt
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ProjNormal

theorem exists_relAmple_of_affine : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] [IsDomain R] [IsIntegrallyClosed R] (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A → ∀ V : A.left.Opens, IsAffineOpen V → (∀ s : Sp R, ∃ x ∈ V, A.hom x = s) → ∃ L : LB A.left, L.IsLB ∧ Out.RelAmple A L := by
  intro R _ _ _ _ A _ hA V hV hV'
  obtain ⟨M, hM, s, hs⟩ := GlobalTheory.T.exists_section_nonzeroLocus_eq_affineOpen R A hA V hV hV'
  exact ⟨M, hM, GlobalTheory.T.relAmple_of_affine_nonzeroLocus_abelianScheme_noetherian R A hA M hM s (hs ▸ hV) (hs ▸ hV')⟩

end GlobalTheory.ProjNormal
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.EighthPowerLocal

open GlobalTheory.SS GlobalTheory.CechPic GlobalTheory.MatrixBundle

theorem relAmple_diag_lam {R : Type} [CommRing R] [IsLocalRing R] [IsNoetherianRing R] {B : Over (Sp R)} [GrpObj B]
    [IsCommMonObj B] (hB : IsAbelianScheme B) {M : LB B.left} (hM : M.IsLB) (hΘ : ∃ t : LB.Gen (Theta B M), t.IsGen)
    (ha : Out.RelAmple B M) : Out.RelAmple B ((abelian₂ B M).pull (lift (𝟙 B) (𝟙 B)).left) := by
  have hlam : (abelian₂ B M).IsLB := LB.isLB_linComb hM _ _
  let q := Out.powIsPowGrp B 2
  have hG : IsAbelianScheme (Out.powObj B 2) := (PowGrp.powers _ _ B 2 q).2.2.2.1 hB
  let ψ : B ⟶ Out.powObj B 2 := (Out.powIsLimit B 2).lift (Fan.mk B ![𝟙 B, (𝟙 B)⁻¹])
  have hψ : ∀ u, ψ ≫ q.pr u = ![𝟙 B, (𝟙 B)⁻¹] u := fun u => (Out.powIsLimit B 2).fac _ ⟨u⟩
  have hbox : (Out.boxLB M q.pr).IsLB := LB.isLB_linComb hM _ _
  have hfin : IsFinite ψ.left := by
    have := hB.proper
    have := hG.proper
    have : IsSeparated ((q.pr 0).left ≫ B.hom) := by rw [Over.w]; infer_instance
    have : IsSeparated (q.pr 0).left := IsSeparated.of_comp _ B.hom
    have : IsFinite (ψ.left ≫ (q.pr 0).left) := by
      rw [← Over.comp_left, hψ]
      exact inferInstanceAs (IsFinite (𝟙 B.left))
    exact IsFinite.of_comp _ (q.pr 0).left
  have hid : IsFinite (𝟙 B : B ⟶ B).left := inferInstanceAs (IsFinite (𝟙 B.left))
  have a₁ := (relAmple_finite_pow_iso _ B _ ψ _ 1 one_pos hB hG hbox hfin).1
    (relAmple_boxLB _ _ B 2 q M hM ha)
  refine (relAmple_finite_pow_iso _ B B (𝟙 B) _ 1 one_pos hB hB (pull_isLB hbox _) hid).2.2.2 _
    (pull_isLB hlam _) ((cls_eq_iff (pull_isLB hbox _) (pull_isLB hlam _)).1 ?_) a₁
  have h₀ : pull (1 : B ⟶ B).left (cls M hM) = 0 := by
    rw [Hom.one_def, Over.comp_left, pull_comp]
    obtain ⟨N, hN, e⟩ := cls_surj (pull (η[B]).left (cls M hM))
    have z : cls N hN = 0 := (cls_eq_zero_iff hN).2 (DVR.exists_gen_of_isLB_local (V := R) N hN)
    rw [← e, z, map_zero]
  have h₁ : cls _ hlam = lam (cls M hM) (fst B B) (snd B B) := cls_cube_two hM _ _ hlam
  have h₂ := lam_mul_left hM hΘ (𝟙 B) (𝟙 B)⁻¹ (𝟙 B)
  rw [mul_inv_cancel, lam_one_left, lam.eq_1 _ (𝟙 B)⁻¹, inv_mul_cancel, h₀] at h₂

  rw [cls_pull hbox, cls_pull hlam, h₁, pull_lam, lift_fst, lift_snd, cls_linComb hM, map_sum, Fin.sum_univ_two,
  one_smul, one_smul, ← pull_comp, ← pull_comp, ← Over.comp_left, ← Over.comp_left, hψ, hψ]
  refine Eq.trans ?_ (eq_neg_of_add_eq_zero_left h₂.symm).symm
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  abel


end GlobalTheory.EighthPowerLocal

end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.ThickPre

lemma thickTrans_surj (R' : Type) [CommRing R'] (I : Ideal R') (e : ℕ)
    (t : Spec (CommRingCat.of (R' ⧸ I ^ (e + 1 + 1)))) : ∃ t', (thickTrans R' I e) t' = t := by
  have hs : Function.Surjective (Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ (e + 1))) :
      R' ⧸ I ^ (e + 1 + 1) →+* R' ⧸ I ^ (e + 1)) := Ideal.Quotient.factor_surjective _
  have hr := _root_.range_comap_of_surjective _ _ hs
  have ht : (t : PrimeSpectrum _) ∈ Set.range (PrimeSpectrum.comap
      (Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ (e + 1))) :
        R' ⧸ I ^ (e + 1 + 1) →+* R' ⧸ I ^ (e + 1))) := by
    rw [hr]
    intro x hx
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    have ha : a ∈ I ^ (e + 1) := by
      rw [SetLike.mem_coe, RingHom.mem_ker, Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem] at hx
      exact hx
    have h2 : (Ideal.Quotient.mk (I ^ (e + 1 + 1)) a) ^ 2 = 0 := by
      rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
      have : a ^ 2 ∈ I ^ ((e + 1) * 2) := by rw [pow_mul]; exact Ideal.pow_mem_pow ha 2
      exact Ideal.pow_le_pow_right (by omega) this
    exact t.isPrime.mem_of_pow_mem 2 (by rw [h2]; exact Ideal.zero_mem _)
  obtain ⟨t', ht'⟩ := ht
  exact ⟨t', ht'⟩

lemma thickMap_surj (R' : Type) [CommRing R'] (I : Ideal R') (e : ℕ) (G' : Over (Sp R')) :
    Function.Surjective (thickMap R' I e G') := by
  intro y
  obtain ⟨t', ht'⟩ := thickTrans_surj R' I e (pullback.snd G'.hom (thick R' I (e + 1)) y)
  have hc : G'.hom (pullback.fst G'.hom (thick R' I (e + 1)) y) = thick R' I e t' := by
    have h1 : G'.hom (pullback.fst G'.hom (thick R' I (e + 1)) y) =
        thick R' I (e + 1) (pullback.snd G'.hom (thick R' I (e + 1)) y) := by
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pullback.condition]
    rw [h1, ← ht', ← Scheme.Hom.comp_apply, thickTrans_comp]
  obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback _ _ hc
  refine ⟨z, (pullback.fst G'.hom (thick R' I (e + 1))).isClosedEmbedding.injective ?_⟩
  rw [← Scheme.Hom.comp_apply, thickMap, pullback.lift_fst, Category.comp_id, hz]

end GlobalTheory.Mum.ThickPre

theorem GlobalTheory.Mum.thick_preimage_eq (R' : Type) [CommRing R'] (I : Ideal R') (G' : Over (Sp R')) (Y : Scheme.{0})
    (φ : ∀ e : ℕ, (thickObj R' I e G').left ⟶ Y) (hφ : ∀ e, thickMap R' I e G' ≫ φ (e + 1) = φ e)
    (V : G'.left.Opens) (W : Y.Opens)
    (h0 : φ 0 ⁻¹ᵁ W = (pullback.fst G'.hom (thick R' I 0)) ⁻¹ᵁ V) :
    ∀ e, φ e ⁻¹ᵁ W = (pullback.fst G'.hom (thick R' I e)) ⁻¹ᵁ V := by
  intro e
  induction e with
  | zero => exact h0
  | succ e ih =>
    have h1 : thickMap R' I e G' ⁻¹ᵁ (φ (e + 1) ⁻¹ᵁ W) =
        thickMap R' I e G' ⁻¹ᵁ ((pullback.fst G'.hom (thick R' I (e + 1))) ⁻¹ᵁ V) := by
      rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, hφ, ih, thickMap, pullback.lift_fst,
        Category.comp_id]
    ext y
    obtain ⟨x, rfl⟩ := GlobalTheory.Mum.ThickPre.thickMap_surj R' I e G' y
    have := congrArg (fun U : Scheme.Opens _ => x ∈ U) h1
    simpa using this
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.LocalInj

theorem base_to_stalk_injective : ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'], AdmBase R' (maximalIdeal R') → ∀ (G₁ : Over (Sp R')) [GrpObj G₁] [IsCommMonObj G₁], IsSemiAbelian G₁ → ∀ x : G₁.left, Function.Injective ((G₁.left.presheaf.germ ⊤ x trivial).hom.comp ((G₁.hom.appTop).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R')).inv.hom)) := by
  intro R' _ _ _ _ G₁ _ _ hG x
  haveI : Smooth G₁.hom := hG.smooth
  haveI : Flat G₁.hom := inferInstance

  have hst : Function.Injective (G₁.hom.stalkMap x).hom := by
    have h := Flat.stalkMap G₁.hom x
    letI := (G₁.hom.stalkMap x).hom.toAlgebra
    haveI : Module.Flat ((Sp R').presheaf.stalk (G₁.hom x)) (G₁.left.presheaf.stalk x) := h
    have : IsLocalHom (algebraMap ((Sp R').presheaf.stalk (G₁.hom x)) (G₁.left.presheaf.stalk x)) :=
      inferInstanceAs (IsLocalHom (G₁.hom.stalkMap x).hom)
    have := Module.FaithfullyFlat.of_flat_of_isLocalHom (A := (Sp R').presheaf.stalk (G₁.hom x))
      (B := G₁.left.presheaf.stalk x)
    exact FaithfulSMul.algebraMap_injective ((Sp R').presheaf.stalk (G₁.hom x)) (G₁.left.presheaf.stalk x)

  have hgerm : Function.Injective ((Sp R').presheaf.germ ⊤ (G₁.hom x) trivial).hom := by
    have hU := isAffineOpen_top (Sp R')
    let _ := (Sp R').presheaf.algebra_section_stalk (U := ⊤) ⟨G₁.hom x, trivial⟩
    have := hU.isLocalization_stalk ⟨G₁.hom x, trivial⟩
    haveI : IsDomain Γ(Sp R', ⊤) :=
      (Scheme.ΓSpecIso (CommRingCat.of R')).commRingCatIsoToRingEquiv.toMulEquiv.isDomain_iff.mpr inferInstance
    exact IsLocalization.injective (M := (hU.primeIdealOf ⟨G₁.hom x, trivial⟩).asIdeal.primeCompl)
      (S := (Sp R').presheaf.stalk ((⟨G₁.hom x, trivial⟩ : (⊤ : (Sp R').Opens)) : Sp R'))
      (Ideal.primeCompl_le_nonZeroDivisors _)
  have hiso : Function.Injective (Scheme.ΓSpecIso (CommRingCat.of R')).inv.hom :=
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of R')).inv).1
  have e : ⇑((G₁.left.presheaf.germ ⊤ x trivial).hom.comp ((G₁.hom.appTop).hom.comp
      (Scheme.ΓSpecIso (CommRingCat.of R')).inv.hom)) =
      ⇑(G₁.hom.stalkMap x).hom ∘ ⇑((Sp R').presheaf.germ ⊤ (G₁.hom x) trivial).hom ∘
        ⇑(Scheme.ΓSpecIso (CommRingCat.of R')).inv.hom := by
    funext a
    exact (Scheme.Hom.germ_stalkMap_apply G₁.hom ⊤ x trivial _).symm
  rw [e]
  exact hst.comp (hgerm.comp hiso)

end GlobalTheory.Mum.LocalInj
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.SquareNear

theorem stalk_props : ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'], AdmBase R' (maximalIdeal R') → ∀ (G₁ : Over (Sp R')) [GrpObj G₁] [IsCommMonObj G₁], IsSemiAbelian G₁ → ∀ x : G₁.left, IsDomain (G₁.left.presheaf.stalk x) ∧ IsNoetherianRing (G₁.left.presheaf.stalk x) ∧ IsIntegrallyClosed (G₁.left.presheaf.stalk x) := by
  intro R' _ _ _ hA G₁ _ _ hG x
  obtain ⟨_, -, _, -⟩ := hA
  haveI := hG.smooth
  have hS : GlobalTheory.IsNormalScheme (Sp R') := inferInstance
  have h := GlobalTheory.forall_isDomain_and_isIntegrallyClosed_stalk_of_smooth G₁.hom
    ((GlobalTheory.isNormalScheme_iff _).mp hS) x
  haveI : IsLocallyNoetherian G₁.left := LocallyOfFiniteType.isLocallyNoetherian G₁.hom
  exact ⟨h.1, inferInstance, h.2⟩

end GlobalTheory.SquareNear
end
