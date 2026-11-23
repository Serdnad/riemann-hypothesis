module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle074
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1481
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1023
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PushEquivSymmLeft
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2916
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle670
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle082
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle091
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsRegularLocalRingOfFlatOfMapEqMaximalIdeal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle032
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2933
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
import Mathlib.RingTheory.RegularLocalRing.Polynomial
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubePull
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle067
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.TorsDescent

theorem descend_point {K : Type} [Field K] [CharZero K] (X : Scheme.{0}) [IsAffine X]
    (f : Sp (AlgebraicClosure K) ⟶ X)
    (hf : ∀ σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K, spMap σ.toAlgHom.toRingHom ≫ f = f) :
    ∃ g : Sp K ⟶ X, spMap (algebraMap K (AlgebraicClosure K)) ≫ g = f := by
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (f ≫ X.isoSpec.hom)
  have hfix : ∀ (σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) a, σ (φ a) = φ a := by
    intro σ a
    have h1 : Spec.map (φ ≫ CommRingCat.ofHom σ.toAlgHom.toRingHom) = Spec.map φ := by
      rw [Spec.map_comp, hφ, ← Category.assoc]
      exact congrArg (· ≫ X.isoSpec.hom) (hf σ)
    exact congrArg (fun g => g.hom a) (Spec.map_injective h1)
  have hmem : ∀ a, φ a ∈ Set.range (algebraMap K (AlgebraicClosure K)) := by
    intro a
    have hb := InfiniteGalois.fixedField_fixingSubgroup (⊥ : IntermediateField K (AlgebraicClosure K))
    have h2 : φ a ∈ IntermediateField.fixedField (⊥ : IntermediateField K (AlgebraicClosure K)).fixingSubgroup :=
      (IntermediateField.mem_fixedField_iff _ _).2 fun σ _ => hfix σ a
    rw [hb] at h2
    exact IntermediateField.mem_bot.1 h2
  let jb := algebraMap K (AlgebraicClosure K)
  let e := RingEquiv.ofBijective jb.rangeRestrict
    ⟨fun a b h => jb.injective (congrArg Subtype.val h), jb.rangeRestrict_surjective⟩
  let ψ : Γ(X, ⊤) →+* K := e.symm.toRingHom.comp (φ.hom.codRestrict jb.range hmem)
  have hψ : CommRingCat.ofHom ψ ≫ CommRingCat.ofHom jb = φ := by
    ext r
    exact congrArg Subtype.val (e.apply_symm_apply (φ.hom.codRestrict jb.range hmem r))
  refine ⟨Spec.map (CommRingCat.ofHom ψ) ≫ X.isoSpec.inv, ?_⟩
  rw [← Category.assoc, spMap, ← Spec.map_comp, hψ, hφ, Category.assoc, Iso.hom_inv_id, Category.comp_id]

theorem torsRat_of_retract_galoisFixed : ∀ {R : Type} [CommRing R] [IsDomain R] [CharZero R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (G' : Over (Sp R)) [GrpObj G'] [IsCommMonObj G'] (A : PolAV (Sp (FractionRing R))) (gen : (Over.pullback (jK R)).obj G' ≅ A.A) (inc : G ⟶ G') (pr : G' ⟶ G) (n : ℕ), IsMonHom gen.hom → IsMonHom inc → IsMonHom pr → inc ≫ pr = 𝟙 G → 1 ≤ n → (∀ (σ : AlgebraicClosure (FractionRing R) ≃ₐ[FractionRing R] AlgebraicClosure (FractionRing R)) (x : Over.mk (spMap (algebraMap (FractionRing R) (AlgebraicClosure (FractionRing R))) ≫ jK R) ⟶ G), x ^ n = 1 → spMap σ.toAlgHom.toRingHom ≫ x.left = x.left) → TorsRat G n := by
  have spec_map_field_cancel {K C : Type} [Field K] [Field C] (gam : K →+* C)
      {X : Scheme} (y y' : Sp K ⟶ X)
      (h : spMap gam ≫ y = spMap gam ≫ y') : y = y' := by
    obtain ⟨⟨p, φ⟩, rfl⟩ := (Scheme.SpecToEquivOfField K X).symm.surjective y
    obtain ⟨⟨p', φ'⟩, rfl⟩ := (Scheme.SpecToEquivOfField K X).symm.surjective y'
    simp only [Scheme.SpecToEquivOfField_symm_apply] at h ⊢
    have e : ∀ (q : X) (ψ : X.residueField q ⟶ CommRingCat.of K),
        spMap gam ≫ (Spec.map ψ ≫ X.fromSpecResidueField q) =
          (Scheme.SpecToEquivOfField C X).symm ⟨q, ψ ≫ CommRingCat.ofHom gam⟩ := by
      intro q ψ
      simp only [Scheme.SpecToEquivOfField_symm_apply, spMap, Spec.map_comp, Category.assoc]
    rw [e, e] at h
    have h2 := (Scheme.SpecToEquivOfField C X).symm.injective h
    simp only [Sigma.mk.inj_iff] at h2
    obtain ⟨rfl, h3⟩ := h2
    have h4 : φ = φ' := by
      have h5 : φ ≫ CommRingCat.ofHom gam = φ' ≫ CommRingCat.ofHom gam := eq_of_heq h3
      ext x
      apply gam.injective
      have := congrArg (fun f => f.hom x) h5
      simpa using this
    rw [h4]
  intro R _ _ _ G _ _ G' _ _ A gen inc pr n hgen hinc hpr hret hn hfix
  haveI := hgen
  haveI := hinc
  haveI := hpr
  intro Ω _ _ κ x hx
  letI : Algebra (FractionRing R) Ω := κ.toAlgebra
  let jb := algebraMap (FractionRing R) (AlgebraicClosure (FractionRing R))
  let i₁ : AlgebraicClosure (FractionRing R) →ₐ[FractionRing R] Ω := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  have hκ : κ = i₁.toRingHom.comp jb := by
    ext a
    exact (i₁.commutes a).symm
  have hκs : spMap κ = spMap i₁.toRingHom ≫ spMap jb := by
    rw [hκ, spMap, spMap, spMap, ← Spec.map_comp]
    rfl
  have hip : inc.left ≫ pr.left = 𝟙 _ := by rw [← Over.comp_left, hret, Over.id_left]

  have hpb := isGrpPullback_pullback G' (jK R)
  let T : Over (Sp (FractionRing R)) := Over.mk (spMap κ)
  let x1 : Over.mk (T.hom ≫ jK R) ⟶ G' := x ≫ inc
  have hx1 : x1 ^ n = 1 := by
    show (x ≫ inc) ^ n = 1
    rw [← MonObj.pow_comp, hx, MonObj.one_comp]
  let x2 := (ObjPull.pushEquiv hpb T).symm x1
  have hx2 : x2 ^ n = 1 := by simp only [x2, ← map_pow, hx1, map_one]
  have hx2l : x2.left ≫ pullback.fst G'.hom (jK R) = x.left ≫ inc.left := ObjPull.pushEquiv_symm_left hpb T x1
  let x3 := x2 ≫ gen.hom
  have hx3 : x3 ^ n = 1 := by rw [← MonObj.pow_comp, hx2, MonObj.one_comp]
  have hmul : x3 ≫ mulN A.A n = toUnit _ ≫ η := by
    rw [GrpTangent.mulN_eq_pow, MonObj.comp_pow, Category.comp_id, hx3, Hom.one_def]
  let t : T ⟶ torsion A.A n := pullback.lift x3 (toUnit _) hmul
  have ht : t ≫ torsion.ι A.A n = x3 := pullback.lift_fst _ _ _

  have hfin := (AbTorsionAnyBase.isFinite_and_flat_torsion _ A.A A.isAb n hn).1
  obtain ⟨K', _, _, _, H⟩ := TorsRational.exists_ext_points (FractionRing R) (torsion A.A n) hfin
  let i' : K' →ₐ[FractionRing R] AlgebraicClosure (FractionRing R) := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  letI : Algebra K' (AlgebraicClosure (FractionRing R)) := i'.toRingHom.toAlgebra
  haveI : IsScalarTower (FractionRing R) K' (AlgebraicClosure (FractionRing R)) :=
    IsScalarTower.of_algebraMap_eq fun a => (i'.commutes a).symm
  obtain ⟨w, hw⟩ := H (AlgebraicClosure (FractionRing R)) Ω i₁.toRingHom t.left (by
    rw [Over.w t]
    show spMap κ = _
    rw [hκ])
  have hw2 : w ≫ (torsion A.A n).hom = spMap jb := by
    refine spec_map_field_cancel i₁.toRingHom _ _ ?_
    rw [← Category.assoc, hw, Over.w t]
    exact hκs
  let Tb : Over (Sp (FractionRing R)) := Over.mk (spMap jb)
  let t₀ : Tb ⟶ torsion A.A n := Over.homMk w hw2
  let g₀ : Tb ⟶ (Over.pullback (jK R)).obj G' := t₀ ≫ torsion.ι A.A n ≫ gen.inv
  let y₁ := ObjPull.pushEquiv hpb Tb g₀
  have hy₁l : y₁.left = w ≫ (torsion.ι A.A n).left ≫ gen.inv.left ≫ pullback.fst G'.hom (jK R) := by
    rw [ObjPull.pushEquiv_left]
    simp only [g₀, t₀, Over.comp_left, Over.homMk_left, Category.assoc]
  have hkey : spMap i₁.toRingHom ≫ y₁.left = x.left ≫ inc.left := by
    have hgh : gen.hom.left ≫ gen.inv.left = 𝟙 _ := by rw [← Over.comp_left, Iso.hom_inv_id, Over.id_left]
    rw [hy₁l, ← Category.assoc, hw, ← hx2l, ← Category.assoc, ← Over.comp_left, ht]
    show (x2.left ≫ gen.hom.left) ≫ gen.inv.left ≫ _ = _
    rw [Category.assoc, ← Category.assoc gen.hom.left, hgh, Category.id_comp]

  let y₀ : Over.mk (Tb.hom ≫ jK R) ⟶ G := y₁ ≫ pr
  have hy₀ : y₀ ^ n = 1 := by
    have h0 : (t₀ ≫ torsion.ι A.A n) ≫ mulN A.A n = toUnit _ ≫ η := by
      have hc : torsion.ι A.A n ≫ mulN A.A n = pullback.snd (mulN A.A n) η[A.A] ≫ η := pullback.condition
      rw [Category.assoc, hc]
      exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ η) (toUnit_unique _ _))
    rw [GrpTangent.mulN_eq_pow, MonObj.comp_pow, Category.comp_id] at h0
    have h1 : g₀ ^ n = 1 := by
      show (t₀ ≫ torsion.ι A.A n ≫ gen.inv) ^ n = 1
      rw [← Category.assoc, ← MonObj.pow_comp, h0, ← Hom.one_def, MonObj.one_comp]
    show (y₁ ≫ pr) ^ n = 1
    rw [← MonObj.pow_comp, ← map_pow, h1, map_one, MonObj.one_comp]
  have hy₁inc : y₁.left ≫ pr.left ≫ inc.left = y₁.left := by
    refine spec_map_field_cancel i₁.toRingHom _ _ ?_
    rw [← Category.assoc, hkey, Category.assoc, reassoc_of% hip]
  have hy₁fix : ∀ σ : AlgebraicClosure (FractionRing R) ≃ₐ[FractionRing R] AlgebraicClosure (FractionRing R),
      spMap σ.toAlgHom.toRingHom ≫ y₁.left = y₁.left := by
    intro σ
    calc spMap σ.toAlgHom.toRingHom ≫ y₁.left = spMap σ.toAlgHom.toRingHom ≫ (y₁.left ≫ pr.left) ≫ inc.left := by
          rw [Category.assoc, hy₁inc]
      _ = (y₁.left ≫ pr.left) ≫ inc.left := by
          rw [← Category.assoc]
          exact congrArg (· ≫ inc.left) (hfix σ y₀ hy₀)
      _ = y₁.left := by rw [Category.assoc, hy₁inc]
  haveI : Mono (torsion.ι A.A n) := inferInstanceAs (Mono (pullback.fst _ _))
  have hwfix : ∀ σ : AlgebraicClosure (FractionRing R) ≃ₐ[FractionRing R] AlgebraicClosure (FractionRing R),
      spMap σ.toAlgHom.toRingHom ≫ w = w := by
    intro σ
    have hσ : spMap σ.toAlgHom.toRingHom ≫ Tb.hom = Tb.hom := by
      show spMap _ ≫ spMap jb = spMap jb
      rw [spMap, spMap, ← Spec.map_comp]
      congr 2
      ext a
      exact σ.commutes a
    let eσ : Tb ⟶ Tb := Over.homMk (spMap σ.toAlgHom.toRingHom) hσ
    have h1 : eσ ≫ g₀ = g₀ := by
      apply (ObjPull.pushEquiv hpb Tb).injective
      apply Over.OverMorphism.ext
      rw [ObjPull.pushEquiv_left, ObjPull.pushEquiv_left, Over.comp_left, Category.assoc]
      exact hy₁fix σ
    have h2 : eσ ≫ t₀ = t₀ := by
      rw [← cancel_mono (torsion.ι A.A n ≫ gen.inv)]
      simpa only [Category.assoc] using h1
    exact congrArg (fun f => f.left) h2

  haveI := hfin
  haveI : IsAffine (torsion A.A n).left := isAffine_of_isAffineHom (torsion A.A n).hom
  obtain ⟨w₁, hw₁⟩ := descend_point (torsion A.A n).left w hwfix
  have hw₁s : w₁ ≫ (torsion A.A n).hom = 𝟙 _ := by
    refine spec_map_field_cancel jb _ _ ?_
    rw [← Category.assoc, hw₁, hw2, Category.comp_id]
  let z : Sp (FractionRing R) ⟶ G'.left :=
    w₁ ≫ (torsion.ι A.A n).left ≫ gen.inv.left ≫ pullback.fst G'.hom (jK R)
  have hz : z ≫ G'.hom = jK R := by
    simp only [z, Category.assoc]
    have hgi : gen.inv.left ≫ pullback.snd G'.hom (jK R) = A.A.hom := Over.w gen.inv
    rw [pullback.condition, ← Category.assoc gen.inv.left, hgi, ← Category.assoc (torsion.ι A.A n).left,
      Over.w (torsion.ι A.A n), ← Category.assoc w₁, hw₁s, Category.id_comp]
  refine ⟨Over.homMk z hz ≫ pr, ?_⟩
  have hz' : spMap κ ≫ z = x.left ≫ inc.left := by
    have e1 : spMap κ ≫ z = spMap i₁.toRingHom ≫ y₁.left := by
      show spMap κ ≫ (w₁ ≫ _ ≫ _ ≫ _) = _
      rw [hκs, Category.assoc, ← Category.assoc (spMap jb), hw₁, hy₁l]
    rw [e1, hkey]
  show x.left = spMap κ ≫ z ≫ pr.left
  rw [← Category.assoc, hz', Category.assoc, hip, Category.comp_id]

end GlobalTheory.TorsDescent
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UTraitExt

theorem exists_ext_unif {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁]
    (hV : CDvr V₁) (y₁ : Sp (FractionRing V₁) ⟶ Xo.XF c) (t : SAB H (Sp V₁)) (hg : GenOf Xo c y₁ t) :
    ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsLocalRing W) (f : V₁ →+* W)
      (fK : FractionRing V₁ →+* FractionRing W), CDvr W ∧ Function.Injective f ∧ IsLocalHom f ∧ f.Finite ∧
      (∀ a, fK (algebraMap V₁ _ a) = algebraMap W _ (f a)) ∧
      ∃ t' : SAB H (Sp W), GenOf Xo c (spMap fK ≫ y₁) t' ∧ Nonempty (PELUnif (maximalIdeal W) t') := by
  obtain ⟨hdvr, hc, hz⟩ := hV
  obtain ⟨tK, ⟨mK⟩, ⟨mx⟩⟩ := hg
  let T : Formalism.L2.Pj.CDVR := @Formalism.L2.Pj.CDVR.mk V₁ _ _ hdvr hc hz
  obtain ⟨T', φ, t', m', hi, hf, ⟨P⟩⟩ :=
    GlobalTheory.ChartCharacters.exists_finite_ext_pelUnif Xo T t tK mK (y₁ ≫ pullback.fst _ _) mx
  let fK : FractionRing V₁ →+* FractionRing T'.V :=
    IsFractionRing.map (A := V₁) (B := T'.V) (K := FractionRing V₁) (L := FractionRing T'.V) hi
  have hfK : ∀ a, fK (algebraMap V₁ _ a) = algebraMap T'.V _ (φ a) := fun a => IsLocalization.map_eq _ _
  have hsq : spMap fK ≫ jK V₁ = jK T'.V ≫ spMap φ := by
    simp only [spMap, jK, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext a
    exact hfK a
  obtain ⟨PP, cub, sym, adj, prim, n, -⟩ := sabPull Out.CubePf.cubePull (spMap fK) tK
  obtain ⟨b, -⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ mK n
  rw [hsq] at b
  obtain ⟨mK', -⟩ := sabCancel pullCubCancel E H _ _ _ _ _ _ _ _ m' b
  obtain ⟨mx', -⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ mx n
  have hloc : IsLocalHom φ := RingHom.IsIntegral.isLocalHom hf.to_isIntegral hi
  refine ⟨T'.V, inferInstance, inferInstance, inferInstance, φ, fK, ⟨inferInstance, inferInstance, inferInstance⟩, hi,
    hloc, hf, hfK, t', ⟨_, ⟨mK'⟩, ⟨?_⟩⟩, ⟨P⟩⟩
  rw [Category.assoc]
  exact mx'

end GlobalTheory.UTraitExt

namespace GlobalTheory.UTraitExt

theorem uTraitExtSt : UTraitExtSt := by
  intro E _ _ _ H Dw l Xo c V _ _ _ hB hV y
  obtain ⟨V₁, _, _, _, f₁, fK₁, hC₁, hi₁, hl₁, hf₁, hc₁, t₁, hg₁⟩ := GlobalTheory.T.exists_finite_extension_unitary_point_generic_fibre E H Dw l Xo c V hB hV y
  obtain ⟨W, _, _, _, f₂, fK₂, hC₂, hi₂, hl₂, hf₂, hc₂, t, hg, ⟨P⟩⟩ := exists_ext_unif Xo c V₁ hC₁ _ t₁ hg₁
  haveI : IsDiscreteValuationRing W := hC₂.1
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible W
  have hg' : GenOf Xo c (spMap fK₂ ≫ spMap fK₁ ≫ y) t := by rw [← Category.assoc]; exact hg
  obtain ⟨be, hbe, hmono⟩ := GlobalTheory.MonPeriods.exists_isMonomial_levelOne hC₂ ϖ hϖ t P
  have hy : spMap fK₂ ≫ spMap fK₁ ≫ y = spMap (fK₂.comp fK₁) ≫ y := by
    rw [← Category.assoc]; congr 1
    simp [spMap, ← Spec.map_comp]
  let T : UTrait Xo c :=
    { V := W
      cdvr := hC₂
      ϖ := ϖ
      irr := hϖ
      y := spMap fK₂ ≫ spMap fK₁ ≫ y
      t := t
      gen := hg'
      P := P
      be := be
      lev := hbe
      mono := hmono }
  refine ⟨T, f₂.comp f₁, fK₂.comp fK₁, hi₂.comp hi₁, ?_, hf₂.comp hf₁, fun a => ?_, hy⟩
  · exact RingHom.isLocalHom_comp f₂ f₁
  · show fK₂ (fK₁ _) = _
    rw [hc₁, hc₂]
    rfl

end GlobalTheory.UTraitExt
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Poinc GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TChart

theorem isRegularLocalRing_of_flat_of_map_comap_maximalIdeal (V : Type) [CommRing V]
    [IsRegularLocalRing V] (I : Type) [Fintype I] (S : Type) [CommRing S] [IsLocalRing S]
    [IsNoetherianRing S] (φ : MvPolynomial I V →+* S) (hflat : φ.Flat)
    (hmap : ((maximalIdeal S).comap φ).map φ = maximalIdeal S) : IsRegularLocalRing S := by
  haveI : IsRegularRing V := GlobalTheory.isRegularRing_of_isRegularLocalRing V
  set q : Ideal (MvPolynomial I V) := (maximalIdeal S).comap φ with hq
  haveI : q.IsPrime := Ideal.comap_isPrime φ (maximalIdeal S)
  let L := Localization.AtPrime q
  haveI : IsRegularLocalRing L := IsRegularRing.isRegularLocalRing_localization q
  have hu : ∀ y : q.primeCompl, IsUnit (φ y) := by
    intro y
    by_contra h
    exact y.2 ((mem_maximalIdeal _).2 h)
  let χ : L →+* S := IsLocalization.lift (M := q.primeCompl) hu
  letI : Algebra (MvPolynomial I V) S := φ.toAlgebra
  letI : Algebra L S := χ.toAlgebra
  haveI : IsScalarTower (MvPolynomial I V) L S := IsScalarTower.of_algebraMap_eq (fun a => by
    change φ a = χ (algebraMap _ L a)
    exact (IsLocalization.lift_eq (M := q.primeCompl) hu a).symm)
  haveI : Module.Flat (MvPolynomial I V) S := hflat
  haveI : IsLocalizedModule q.primeCompl (LinearMap.id : S →ₗ[MvPolynomial I V] S) :=
    isLocalizedModule_id q.primeCompl S L
  haveI : Module.Flat L S :=
    Module.Flat.of_isLocalizedModule L q.primeCompl (LinearMap.id : S →ₗ[MvPolynomial I V] S)
  have hm : maximalIdeal S = (maximalIdeal L).map (algebraMap L S) := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_map, ← IsScalarTower.algebraMap_eq]
    exact hmap.symm
  exact GlobalTheory.isRegularLocalRing_of_flat_of_map_eq_maximalIdeal L S (maximalIdeal L) hm

theorem isRegularLocalRing_quotient_of_isComplAt :
    ∀ (W : Type) [CommRing W] [IsLocalRing W] [IsNoetherianRing W] (I : Type) [Fintype I] (R : Type) [CommRing R]
      [IsLocalRing R] (ψ : MvPolynomial I W →+* R), IsComplAt ψ → IsLocalHom (ψ.comp MvPolynomial.C) →
      ∀ 𝔭 : Ideal W, 𝔭 ≠ ⊤ → IsRegularLocalRing (W ⧸ 𝔭) →
        IsRegularLocalRing (R ⧸ 𝔭.map (ψ.comp MvPolynomial.C)) := by
  intro W _ _ _ I _ R _ _ ψ hψ hloc 𝔭 h𝔭 hreg
  obtain ⟨hnoeth, -, hflat, hmap, -⟩ := hψ
  haveI : IsNoetherianRing R := hnoeth
  haveI : IsRegularLocalRing (W ⧸ 𝔭) := hreg
  rw [← Ideal.map_map]
  set J : Ideal R := (Ideal.map MvPolynomial.C 𝔭).map ψ with hJ
  have hJm : J ≤ maximalIdeal R := by
    rw [hJ, Ideal.map_map, Ideal.map_le_iff_le_comap]
    intro x hx
    rw [Ideal.mem_comap, mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    exact h𝔭 (Ideal.eq_top_of_isUnit_mem _ hx (isUnit_of_map_unit _ _ hu))
  haveI : Nontrivial (R ⧸ J) :=
    Ideal.Quotient.nontrivial_iff.2 (ne_top_of_le_ne_top (maximalIdeal.isMaximal R).ne_top hJm)
  haveI : IsLocalRing (R ⧸ J) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
  let e := MvPolynomial.quotientEquivQuotientMvPolynomial (σ := I) 𝔭
  have heC : ∀ a : W, e (MvPolynomial.C (Ideal.Quotient.mk 𝔭 a)) = Ideal.Quotient.mk _ (MvPolynomial.C a) := by
    intro a; simp [e, MvPolynomial.quotientEquivQuotientMvPolynomial]
  have heX : ∀ i : I, e (MvPolynomial.X i) = Ideal.Quotient.mk _ (MvPolynomial.X i) := by
    intro i; simp [e, MvPolynomial.quotientEquivQuotientMvPolynomial]
  let ψ' : MvPolynomial I (W ⧸ 𝔭) →+* R ⧸ J :=
    (Ideal.quotientMap J ψ Ideal.le_comap_map).comp e.toRingEquiv.toRingHom
  have hflat' : ψ'.Flat :=
    (RingHom.Flat.of_bijective e.bijective).comp (GlobalTheory.Pat.flat_quotientMap_map ψ hflat _)
  let π : MvPolynomial I W →+* MvPolynomial I (W ⧸ 𝔭) := MvPolynomial.map (Ideal.Quotient.mk 𝔭)
  have hcomm : ψ'.comp π = (Ideal.Quotient.mk J).comp ψ := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp only [RingHom.comp_apply, π, MvPolynomial.map_C, ψ']
      change Ideal.quotientMap J ψ Ideal.le_comap_map (e (MvPolynomial.C (Ideal.Quotient.mk 𝔭 a))) = _
      rw [heC, Ideal.quotientMap_mk]
    · intro i
      simp only [RingHom.comp_apply, π, MvPolynomial.map_X, ψ']
      change Ideal.quotientMap J ψ Ideal.le_comap_map (e (MvPolynomial.X i)) = _
      rw [heX, Ideal.quotientMap_mk]
  have hmax : maximalIdeal (R ⧸ J) = (maximalIdeal R).map (Ideal.Quotient.mk J) := by
    exact (IsLocalRing.map_maximalIdeal_of_surjective _ Ideal.Quotient.mk_surjective).symm
  refine isRegularLocalRing_of_flat_of_map_comap_maximalIdeal (W ⧸ 𝔭) I (R ⧸ J) ψ' hflat' ?_
  refine le_antisymm Ideal.map_comap_le ?_
  have h1 : maximalIdeal (R ⧸ J) = (((maximalIdeal R).comap ψ).map π).map ψ' := by
    rw [hmax, Ideal.map_map, hcomm, ← Ideal.map_map, hmap]
  refine h1.le.trans (Ideal.map_mono ?_)
  rw [Ideal.map_le_iff_le_comap, Ideal.comap_comap, hcomm, ← Ideal.comap_comap]
  apply Ideal.comap_mono
  rw [hmax]
  exact Ideal.le_comap_map

end GlobalTheory.TChart
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Poinc GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TChart

theorem isRegularLocalRing_and_isDomain_of_isComplAt :
    ∀ (W : Type) [CommRing W] [IsRegularLocalRing W] (I : Type) [Fintype I] (R : Type) [CommRing R]
      [IsLocalRing R] (ψ : MvPolynomial I W →+* R), IsComplAt ψ → IsLocalHom (ψ.comp MvPolynomial.C) →
      IsRegularLocalRing R ∧ IsDomain R := by
  intro W _ _ I _ R _ _ ψ hψ _
  obtain ⟨hnoeth, -, hflat, hmap, -⟩ := hψ
  haveI : IsRegularRing W := GlobalTheory.isRegularRing_of_isRegularLocalRing W
  set q : Ideal (MvPolynomial I W) := (maximalIdeal R).comap ψ with hq
  haveI : q.IsPrime := Ideal.comap_isPrime ψ (maximalIdeal R)
  let L := Localization.AtPrime q
  haveI : IsRegularLocalRing L := IsRegularRing.isRegularLocalRing_localization q
  have hu : ∀ y : q.primeCompl, IsUnit (ψ y) := by
    intro y
    by_contra h
    exact y.2 ((mem_maximalIdeal _).2 h)
  let φ : L →+* R := IsLocalization.lift (M := q.primeCompl) hu
  letI : Algebra (MvPolynomial I W) R := ψ.toAlgebra
  letI : Algebra L R := φ.toAlgebra
  haveI : IsScalarTower (MvPolynomial I W) L R := IsScalarTower.of_algebraMap_eq (fun a => by
    change ψ a = φ (algebraMap _ L a)
    exact (IsLocalization.lift_eq (M := q.primeCompl) hu a).symm)
  haveI : Module.Flat (MvPolynomial I W) R := hflat
  haveI : IsLocalizedModule q.primeCompl (LinearMap.id : R →ₗ[MvPolynomial I W] R) :=
    isLocalizedModule_id q.primeCompl R L
  haveI : Module.Flat L R :=
    Module.Flat.of_isLocalizedModule L q.primeCompl (LinearMap.id : R →ₗ[MvPolynomial I W] R)
  haveI : IsNoetherianRing R := hnoeth
  have hm : maximalIdeal R = (maximalIdeal L).map (algebraMap L R) := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_map, ← IsScalarTower.algebraMap_eq]
    exact hmap.symm
  haveI hreg : IsRegularLocalRing R :=
    GlobalTheory.isRegularLocalRing_of_flat_of_map_eq_maximalIdeal L R (maximalIdeal L) hm
  exact ⟨hreg, (GlobalTheory.isDomain_and_isIntegrallyClosed_of_isRegularLocalRing R).1⟩

end GlobalTheory.TChart
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.finite_mumfordClass_eq_zero_ample : ∀ (K : Type) [Field K] (A : AbVar K) (c : Pic A.X.left), IsAmpleCls c → Finite {x : A.Pt // AbVar.lam c (fst A.X (ptOver K (AlgebraicClosure K))) (snd A.X _ ≫ x) = 0} := by
  first | (exact @GlobalTheory.AV.AbVar.finite_lam_eq_zero) | (exact GlobalTheory.AV.AbVar.finite_lam_eq_zero) | (intros; apply GlobalTheory.AV.AbVar.finite_lam_eq_zero  <;> assumption)
end
