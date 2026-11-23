module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2858
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1241
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2607
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2860
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle535
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle065
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsoFreePerpLabelKernelWeights
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle127
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle120
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqTorusOfClassify
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle473
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SmoothCommGroupSchemeEqOfPowEqOfClosedPoint
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle048
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle131
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2794
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsSchemeTheoreticallyDominantSpecOfInjective
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle119
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyIsPullDegOfSameTorusTwist
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle546
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2842
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle067
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUnifOfIsMumfordOf
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle064
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle532
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle068
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle066

@[expose] public section

section

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Poinc
open ReciprocityTheory.AnForm.R
open scoped CategoryTheory.Obj
open GlobalTheory.SiegJoin
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.HodgeFrameGen
open GlobalTheory.QCoh (pullbackSections)

namespace GlobalTheory.HodgeFrameGen

theorem gm_eq_of_appLE {T Z : Scheme.{0}} (r : Z ⟶ T) (z : Z) {U : T.Opens} {W : Z.Opens} (hW : W ≤ r ⁻¹ᵁ U)
    (hz : z ∈ W) (u : Γ(T, U)ˣ) (v : Γ(Z, W)ˣ) (e : v.val = (r.appLE U W hW).hom u.val) :
    gm r z U u = gm (𝟙 Z) z W v := by
  refine Units.ext ?_
  rw [gm_val r z U (hW hz), gm_val (𝟙 Z) z W hz, e]
  exact (TopCat.Presheaf.germ_res_apply Z.presheaf (homOfLE hW) z hz _).symm

theorem val_gen_pull : ∀ {S' T Z : Scheme.{0}} {G : Over S'} [GrpObj G] {H : Over T} [GrpObj H] {x : T ⟶ S'}
    {ψ : H.left ⟶ G.left} [QuasiSeparated G.hom] {g : ℕ} (h : IsGrpPullback H G x ψ)
    {a : Fin g → Γ(omega H, ⊤)} (ha : IsFrame a) (r : Z ⟶ T) {B : Over Z} [GrpObj B] {ρ : B.left ⟶ H.left}
    (q : IsGrpPullback B H r ρ) (x' : Z ⟶ S') (ψ' : B.left ⟶ G.left) (h' : IsGrpPullback B G x' ψ'),
    r ≫ x = x' → ρ ≫ ψ = ψ' → ∀ {b : Fin g → Γ(omega B, ⊤)} (hb : IsFrame b),
    (∀ i, b i = (omegaBase q).app ⊤ (pullbackSections r _ le_top (a i))) → ∀ (z : Z)
    (J : (Z ⟶ S') → (hodge G g).ι), Good (hodge G g) z J →
    val (L := hodge G g) (φ := fun _ : PUnit => x) (ε := fun _ => 1) (gen h ha) r z J =
      val (L := hodge G g) (φ := fun _ : PUnit => x') (ε := fun _ => 1) (gen h' hb) (𝟙 Z) z J := by
  intro S' T Z G _ H _ x ψ _ g h a ha r B _ ρ q x' ψ' h' e e' b hb hab z J hJ
  have : QuasiSeparated H.hom := MorphismProperty.of_isPullback h.1 ‹_›
  rw [val_of (L := hodge G g) (φ := fun _ : PUnit => x) (ε := fun _ => 1) (gen h ha) r z J (fun _ => J x')
      (fun _ => by rw [e]),
    val_of (L := hodge G g) (φ := fun _ : PUnit => x') (ε := fun _ => 1) (gen h' hb) (𝟙 Z) z J (fun _ => J x')
      (fun _ => by rw [Category.id_comp])]
  have hW : LB.wchart (hodge G g) (fun _ : PUnit => x') (fun _ => J x') ≤
      r ⁻¹ᵁ LB.wchart (hodge G g) (fun _ : PUnit => x) (fun _ => J x') := fun y hy =>
    Set.mem_iInter.2 fun k => by
      have := Set.mem_iInter.1 hy k
      rw [← e] at this ⊢
      exact this
  have hz : z ∈ LB.wchart (hodge G g) (fun _ : PUnit => x') (fun _ => J x') := Set.mem_iInter.2 fun _ => hJ x'
  have k {U : T.Opens} {V W : Z.Opens} (hV : V ≤ r ⁻¹ᵁ U) (h₁ : W ≤ V) (s : Γ(omega H, U)) :
      GlobalTheory.Twist.resM _ h₁ ((omegaBase q).app V (pullbackSections r _ hV s)) =
        (omegaBase q).app W (pullbackSections r _ (h₁.trans hV) s) := by
    rw [← GlobalTheory.QCoh.res_pullbackSections r _ hV h₁ s]
    exact congr($((omegaBase q).mapPresheaf.naturality (homOfLE h₁).op) (pullbackSections r _ hV s)).symm
  refine gm_eq_of_appLE r z hW hz _ _ ?_
  have hc := isFrame_chart h (fun _ => J x')
  refine Eq.trans ?_ (hc.val_detUnit_pullback ha r le_rfl le_top hW)
  refine congrArg Units.val ?_
  refine Eq.trans ?_ (IsFrame.detUnit_map_iso _ _ (omegaBase q) _ _)
  refine GlobalTheory.Vert.DivPull.detUnit_congr _ _ _ _ _ _ _ _ (fun i => ?_) (fun i => ?_)
  · refine Eq.trans (GlobalTheory.Twist.resM_self _ _) (Eq.trans ?_ (k _ _ _).symm)
    exact (GlobalTheory.BadPt.Fibre.omegaBase_comp h q h' e e' _ _ _ _).symm
  · rw [hab]
    exact (k _ _ _).trans (k _ _ _).symm

end GlobalTheory.HodgeFrameGen
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
open GlobalTheory.Poinc.Eq8 GlobalTheory.Poinc.Sep.Spz Classical

namespace GlobalTheory.Poinc.Sep.Spz

theorem exists_torAt : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.Mum.Base V → ∀ (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D : DegData V (maximalIdeal V)) (A : PolAV (Sp (FractionRing V))) (U : Unif (maximalIdeal V) D A G) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing V) F] (k : ℕ) (z : F), 1 ≤ k → z ^ k = 1 → ∀ c : D.toPre.X →+ ℤ, ∃ x : TFK (R := V) F ⟶ A.A, TorAt U F k z c x := by
  intro V _ _ _ hB G _ _ hG D A U F _ _ _ k z hk hz c
  obtain ⟨hAdm, hChar⟩ := hB
  haveI := hChar
  have hz0 : z ≠ 0 := by
    rintro rfl
    rw [zero_pow (by omega)] at hz
    exact zero_ne_one hz
  let u : Fˣ := Units.mk0 z hz0
  let τ : Multiplicative D.toPre.X →* Fˣ :=
    (zpowersHom Fˣ u).comp (AddMonoidHom.toMultiplicative c)
  have hu : u ^ k = 1 := by
    ext; simp [u, hz]
  have hτ : τ ^ k = 1 := by
    refine MonoidHom.ext fun χ => ?_
    rw [MonoidHom.pow_apply, MonoidHom.one_apply]
    simp only [τ, MonoidHom.comp_apply, zpowersHom_apply]
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hu, one_zpow]
  obtain ⟨q, hy, hq⟩ := GlobalTheory.ZH.TorusPerp.exists_qkPt_tor (F := F) D.tau_bimult τ hτ
  obtain ⟨f, hf⟩ := GlobalTheory.TorsionIso.torsion_eq GlobalTheory.firstFiveLaws V (maximalIdeal V) hAdm D A G hG U F k hk
  refine ⟨f q, τ, q, fun χ => ?_, hy, hq, (hf.1 q (f q)).2 rfl⟩
  simp [τ, u]

end GlobalTheory.Poinc.Sep.Spz
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Eq8 GlobalTheory.Poinc.Sep.Spz Classical

namespace GlobalTheory.Poinc.Sep.Spz

theorem torAt_of_closedPoint : ∀ (B : Scheme.{0}) (H : Over B) [GrpObj H] (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.Mum.Base V → ∀ (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D : DegData V (maximalIdeal V)) (A : PolAV (Sp (FractionRing V))) (U : Unif (maximalIdeal V) D A G) (ξ : Sp V ⟶ B) (β : G.left ⟶ H.left), IsGrpPullback G H ξ β → ∀ (σ : Sp V ⟶ H.left), σ ≫ H.hom = ξ → ∀ (k : ℕ) (w : V), 1 ≤ k → IsUnit (k : V) → w ^ k = 1 → ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing V) F] (c : D.toPre.X →+ ℤ) (x : TFK (R := V) F ⟶ A.A), x ^ k = 1 → x.left ≫ genMap U ≫ β = spMap (algebraMap (FractionRing V) F) ≫ jK V ≫ σ → ∀ (κ : Type) [Field κ] (b : V →+* κ) (hb : ∀ y ∈ maximalIdeal V ^ (0 + 1), b y = 0) (Gκ : Over (Sp κ)) [GrpObj Gκ] (m : Gκ.left ⟶ G.left) (hm : IsGrpPullback Gκ G (spMap b) m) (τ : Multiplicative D.toPre.X →* κˣ), (∀ χ, (τ (Multiplicative.ofAdd χ) : κ) = b w ^ c χ) → ∀ (z : Over.mk (spMap (RingHom.id κ)) ⟶ splitTorus (Sp κ) D.toPre.X), (∀ χ, GlobalTheory.UU.chV z χ = unitOn (τ (Multiplicative.ofAdd χ))) → spMap b ≫ σ = (z ≫ GlobalTheory.TorusPart.gtTorus (U.gt 0) hb hm).left ≫ m ≫ β → TorAt U F k (algebraMap (FractionRing V) F (algebraMap V (FractionRing V) w)) c x := by
  intro B H _ V _ _ _ hV G _ _ hG D A U ξ β hβ σ hσ k w hk hkV hw F _ _ _ c x hx hxσ κ _ b hb Gκ _ m hm τ hτ z hz hbσ
  haveI : CharZero V := hV.2
  have hid : spMap (RingHom.id V) = 𝟙 (Sp V) := Spec.map_id _
  let σ₀ : Sp V ⟶ G.left := hβ.1.lift σ (𝟙 _) (hσ.trans (Category.id_comp _).symm)
  have hσ₀ : σ₀ ≫ β = σ := hβ.1.lift_fst _ _ _
  have hσ₀' : σ₀ ≫ G.hom = 𝟙 _ := hβ.1.lift_snd _ _ _
  let σ₁ : Over.mk (spMap (RingHom.id V)) ⟶ G := Over.homMk σ₀ (hσ₀'.trans hid.symm)
  obtain ⟨s, s1, s2, s3, s4⟩ := GlobalTheory.ToricTorsionUnif.main V hV G hG D A U k hk
  have hwu : IsUnit w := IsUnit.of_pow_eq_one hw (by omega)
  obtain ⟨u, rfl⟩ := hwu
  have hu : u ^ k = 1 := Units.ext (by simpa using hw)
  let τV : Multiplicative D.toPre.X →* Vˣ := (zpowersHom Vˣ u).comp (AddMonoidHom.toMultiplicative c)
  have hτV' : ∀ χ, τV χ = u ^ c (Multiplicative.toAdd χ) := fun χ => rfl
  have hτV : τV ^ k = 1 := MonoidHom.ext fun χ => by
    rw [MonoidHom.pow_apply, hτV', ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hu, one_zpow]; rfl
  have hval : ∀ (L : Type) [Field L] (f : V →+* L) (n : ℤ), f ((u ^ n : Vˣ) : V) = f u ^ n := fun L _ f n => by
    have := congrArg Units.val (map_zpow (Units.map (f : V →* L)) u n)
    rw [Units.val_zpow_eq_zpow_val] at this
    exact this
  let a : V →+* F := (algebraMap (FractionRing V) F).comp (algebraMap V (FractionRing V))
  have ha : spMap a = spMap (algebraMap (FractionRing V) F) ≫ jK V := GlobalTheory.ToricTorsionSec.spMap_comp _ _
  have hainj : Function.Injective a :=
    (algebraMap (FractionRing V) F).injective.comp (IsFractionRing.injective V (FractionRing V))
  haveI := U.gen_hom
  haveI : IsMonHom U.gen.symm.hom := inferInstanceAs (IsMonHom U.gen.inv)
  have hp₁ : IsGrpPullback A.A ((Over.pullback (jK V)).obj G) (𝟙 _) U.gen.inv.left :=
    isGrpPullback_of_iso U.gen.symm
  have hp₂ := isGrpPullback_pullback G (jK V)
  have hp : IsGrpPullback A.A G (jK V) (genMap U) := (hp₁.comp hp₂).congr (Category.id_comp _) rfl
  obtain ⟨e, he⟩ := GlobalTheory.LiePull.exists_pushEquiv hp (TFK (R := V) F) (spMap a) ha
  let ρ : Over.mk (spMap a) ⟶ Over.mk (spMap (RingHom.id V)) :=
    Over.homMk (spMap a) (by show spMap a ≫ spMap (RingHom.id V) = spMap a; rw [hid, Category.comp_id])
  have hex : e x = ρ ≫ σ₁ := by
    refine Over.OverMorphism.ext (hβ.1.hom_ext ?_ ((Over.w _).trans (Over.w _).symm))
    rw [he]
    show (x.left ≫ genMap U) ≫ β = (spMap a ≫ σ₀) ≫ β
    rw [Category.assoc, Category.assoc, hσ₀, ha, hxσ, Category.assoc]
  haveI : IsSeparated G.hom := hG.separated
  haveI : IsDominant (spMap a) :=
    ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical a).2
      (by rw [(RingHom.injective_iff_ker_eq_bot _).1 hainj]; exact bot_le)⟩
  have hσ₁ : σ₁ ^ k = 1 := by
    have h1 : ρ ≫ σ₁ ^ k = ρ ≫ 1 := by
      rw [MonObj.comp_pow, ← hex, ← map_pow, hx, map_one, MonObj.comp_one]
    haveI : AlgebraicGeometry.IsReduced (Over.mk (spMap (RingHom.id V))).left :=
      inferInstanceAs (AlgebraicGeometry.IsReduced (Sp V))
    refine Over.OverMorphism.ext (ext_of_isDominant_of_isSeparated G.hom
      ((Over.w _).trans (Over.w _).symm) (spMap a) ?_)
    exact congrArg (·.left) h1
  have hbl : IsLocalHom b := ⟨fun y hy => by
    by_contra hn
    rw [hb y (by simpa using (mem_maximalIdeal y).2 hn)] at hy
    exact not_isUnit_zero hy⟩
  have hτb : ∀ χ, (τ χ : κ) = b (τV χ : V) := fun χ => by
    rw [hτV', hval]; exact hτ (Multiplicative.toAdd χ)
  have hτk : τ ^ k = 1 := MonoidHom.ext fun χ => Units.ext (by
    rw [MonoidHom.pow_apply, Units.val_pow_eq_pow_val, hτb, ← map_pow, ← Units.val_pow_eq_pow_val,
      ← MonoidHom.pow_apply, hτV]; simp)
  have hσs : σ₁ = s V (RingHom.id V) τV hτV := by
    refine GlobalTheory.LocalRigid.eq_of_pow_eq_of_closedPoint (Sp V) G hG.smooth V _ k hkV _ _ (by rw [hσ₁, s1]) κ b hbl ?_
    rw [← s2 V κ (RingHom.id V) b b τV hτV τ hτk rfl hτb,
      s3 κ κ b hb b (RingHom.id κ) Gκ m hm τ hτk z rfl hz]
    refine hβ.1.hom_ext ?_ ?_
    · show (spMap b ≫ σ₀) ≫ β = _
      rw [Category.assoc, hσ₀, hbσ, Category.assoc]
    · show (spMap b ≫ σ₀) ≫ G.hom = _
      rw [Category.assoc, hσ₀', Category.comp_id,
        ← s3 κ κ b hb b (RingHom.id κ) Gκ m hm τ hτk z rfl hz]
      exact (Over.w (s κ b τ hτk)).symm
  let τF : Multiplicative D.toPre.X →* Fˣ := (Units.map (a : V →* F)).comp τV
  have hτF : τF ^ k = 1 := MonoidHom.ext fun χ => by
    rw [MonoidHom.pow_apply]
    show Units.map (a : V →* F) (τV χ) ^ k = 1
    rw [← map_pow, ← MonoidHom.pow_apply, hτV, MonoidHom.one_apply, map_one]
  obtain ⟨q, hqy, hqt⟩ := GlobalTheory.ZH.TorusPerp.exists_qkPt_tor D.tau_bimult (k := k) τF hτF
  obtain ⟨f, ⟨i, -⟩, -⟩ := GlobalTheory.TorsionIso.torsion_clause V (maximalIdeal V) hV.1 D A G hG U F k hk
  have hq := (i q _).2 rfl
  have hxq : x = f q := by
    apply e.injective
    refine Over.OverMorphism.ext ?_
    rw [he (f q), s4 F a τF hτF q (f q) rfl hqy hqt hq,
      s2 V F (RingHom.id V) a a τV hτV τF hτF rfl (fun χ => rfl), ← hσs, hex]
    rfl
  refine ⟨τF, q, fun χ => ?_, hqy, hqt, hxq ▸ hq⟩
  exact hval F a (c χ)

end GlobalTheory.Poinc.Sep.Spz
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Eq8 GlobalTheory.Poinc.Sep.Spz Classical

noncomputable section

theorem GlobalTheory.ToricTorsionClosedPt.main : ∀ (B : Scheme.{0}) (H : Over B) [GrpObj H] (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.Mum.Base V → ∀ (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D : DegData V (maximalIdeal V)) (A : PolAV (Sp (FractionRing V))) (U : Unif (maximalIdeal V) D A G) (ξ : Sp V ⟶ B) (β : G.left ⟶ H.left), IsGrpPullback G H ξ β → ∀ (σ : Sp V ⟶ H.left), σ ≫ H.hom = ξ → ∀ (k : ℕ) (w : V), 1 ≤ k → w ^ k = 1 → ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing V) F] (c : D.toPre.X →+ ℤ) (x : TFK (R := V) F ⟶ A.A), TorAt U F k (algebraMap (FractionRing V) F (algebraMap V (FractionRing V) w)) c x → x.left ≫ genMap U ≫ β = spMap (algebraMap (FractionRing V) F) ≫ jK V ≫ σ → ∀ (κ : Type) [Field κ] (b : V →+* κ) (hb : ∀ y ∈ maximalIdeal V ^ (0 + 1), b y = 0) (Gκ : Over (Sp κ)) [GrpObj Gκ] (m : Gκ.left ⟶ G.left) (hm : IsGrpPullback Gκ G (spMap b) m) (τ : Multiplicative D.toPre.X →* κˣ), (∀ χ, (τ (Multiplicative.ofAdd χ) : κ) = b w ^ c χ) → ∀ (z : Over.mk (spMap (RingHom.id κ)) ⟶ splitTorus (Sp κ) D.toPre.X), (∀ χ, GlobalTheory.UU.chV z χ = unitOn (τ (Multiplicative.ofAdd χ))) → spMap b ≫ σ = (z ≫ GlobalTheory.TorusPart.gtTorus (U.gt 0) hb hm).left ≫ m ≫ β := by
  intro B H _ V _ _ _ hV G _ _ hG D A U ξ β hβ σ hσ k w hk hw F _ _ _ c x hx hxσ κ _ b hb Gκ _ m hm τ hτ z hz
  have hk0 : k ≠ 0 := by omega
  let u : Vˣ := Units.ofPowEqOne w k hw hk0
  have hu : (u : V) = w := Units.val_ofPowEqOne w k hw hk0
  have huk : u ^ k = 1 := Units.pow_ofPowEqOne hw hk0
  let τV : Multiplicative D.toPre.X →* Vˣ := (zpowersHom Vˣ u).comp (AddMonoidHom.toMultiplicative c)
  have hτVv : ∀ χ, τV χ = u ^ c (Multiplicative.toAdd χ) := fun χ => rfl
  have hτV : τV ^ k = 1 := MonoidHom.ext fun χ => by
    rw [MonoidHom.pow_apply, MonoidHom.one_apply, hτVv, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul,
      zpow_natCast, huk, one_zpow]
  have powk : ∀ {L : Type} [Field L] (t : Multiplicative D.toPre.X →* Lˣ) (y : L), y ^ k = 1 →
      (∀ χ, (t (Multiplicative.ofAdd χ) : L) = y ^ c χ) → t ^ k = 1 := by
    intro L _ t y hy ht
    refine MonoidHom.ext fun χ => Units.ext ?_
    rw [MonoidHom.pow_apply, MonoidHom.one_apply, Units.val_pow_eq_pow_val, Units.val_one,
      ← ofAdd_toAdd χ, ht, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hy, one_zpow]
  have mapv : ∀ {L : Type} [Field L] (f : V →+* L) (χ : Multiplicative D.toPre.X),
      f (τV χ : V) = f w ^ c (Multiplicative.toAdd χ) := by
    intro L _ f χ
    rw [hτVv, ← hu]
    show ((Units.map (f : V →* L) (u ^ c (Multiplicative.toAdd χ)) : Lˣ) : L) = _
    rw [map_zpow, Units.val_zpow_eq_zpow_val]
    rfl
  obtain ⟨s, s1, s2, s3, s4⟩ := GlobalTheory.ToricTorsionUnif.main V hV G hG D A U k hk
  let sV := s V (RingHom.id V) τV hτV
  let σ₁ : Sp V ⟶ G.left := hβ.1.lift σ (𝟙 _) (by rw [hσ, Category.id_comp])
  have hσ₁β : σ₁ ≫ β = σ := hβ.1.lift_fst _ _ _
  have hσ₁G : σ₁ ≫ G.hom = 𝟙 _ := hβ.1.lift_snd _ _ _
  have hsVG : sV.left ≫ G.hom = 𝟙 _ := by
    rw [Over.w sV]
    show Spec.map (CommRingCat.ofHom (RingHom.id V)) = _
    exact Spec.map_id _

  let a : V →+* F := (algebraMap (FractionRing V) F).comp (algebraMap V (FractionRing V))
  have ha : spMap a = spMap (algebraMap (FractionRing V) F) ≫ jK V := by
    dsimp only [a, spMap, jK]
    rw [← Spec.map_comp]
    rfl
  have haI : Function.Injective a :=
    (algebraMap (FractionRing V) F).injective.comp (IsFractionRing.injective V (FractionRing V))
  haveI : IsDominant (spMap a) := ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical a).2
    (by rw [(RingHom.injective_iff_ker_eq_bot _).1 haI]; exact bot_le)⟩
  haveI : IsSeparated G.hom := hG.separated
  obtain ⟨τF, q, hτF, hq, hqt, hqx⟩ := hx
  have hτFk : τF ^ k = 1 := powk τF _ (by rw [← map_pow, ← map_pow, hw, map_one, map_one]) hτF
  have e4 := s4 F a τF hτFk q x rfl hq hqt hqx
  have e2 := s2 V F (RingHom.id V) a a τV hτV τF hτFk (RingHom.comp_id a).symm (fun χ => by
    rw [mapv a χ]; exact hτF (Multiplicative.toAdd χ))
  change _ = spMap a ≫ sV.left at e2
  have hi : σ₁ = sV.left := by
    refine ext_of_isDominant_of_isSeparated G.hom (hσ₁G.trans hsVG.symm) (spMap a) ?_
    refine hβ.1.hom_ext ?_ ?_
    · have l : spMap a ≫ σ₁ ≫ β = x.left ≫ genMap U ≫ β := by
        rw [hσ₁β, hxσ, ha, Category.assoc]
      have r : spMap a ≫ sV.left ≫ β = x.left ≫ genMap U ≫ β := by
        rw [← Category.assoc, ← e2, ← e4, Category.assoc]
      rw [Category.assoc, Category.assoc, l, r]
    · simp only [Category.assoc]
      exact congrArg (spMap a ≫ ·) (hσ₁G.trans hsVG.symm)
  have hτk : τ ^ k = 1 := powk τ (b w) (by rw [← map_pow, hw, map_one]) hτ
  have e2' := s2 V κ (RingHom.id V) b b τV hτV τ hτk (RingHom.comp_id b).symm (fun χ => by
    rw [mapv b χ]; exact hτ (Multiplicative.toAdd χ))
  have e3 := s3 κ κ b hb b (RingHom.id κ) Gκ m hm τ hτk z (RingHom.id_comp b).symm hz
  rw [← hσ₁β, hi, ← Category.assoc, ← e2', e3, Category.assoc]

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
open GlobalTheory.Poinc.Eq8 GlobalTheory.Poinc.Sep.Spz Classical

noncomputable section

namespace GlobalTheory.Poinc.Sep.Spz

theorem endU_gtTorus_comp {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] {D : DegData V (maximalIdeal V)}
    {A : PolAV (Sp (FractionRing V))} {G : Over (Sp V)} [GrpObj G] [IsCommMonObj G] (U : Unif (maximalIdeal V) D A G)
    (E : EndU U.toUnifPre) {κ : Type} [Field κ] {a : V →+* κ} (ha : ∀ x ∈ maximalIdeal V ^ (0 + 1), a x = 0)
    {G₀ : Over (Sp κ)} [GrpObj G₀] {φ : G₀.left ⟶ G.left} (h : IsGrpPullback G₀ G (spMap a) φ) (f₀ : G₀ ⟶ G₀)
    (hf : f₀.left ≫ φ = φ ≫ E.aG.left) :
    GlobalTheory.TorusPart.gtTorus (U.gt 0) ha h ≫ f₀ =
      GlobalTheory.SplitTorus.torusMap (Sp κ) E.h ≫ GlobalTheory.TorusPart.gtTorus (U.gt 0) ha h := by
  obtain ⟨t, ht, hi⟩ := E.i_lin 0
  have htm := GlobalTheory.Poinc.Eq8.eq_torusMap_of_torusEndOf E.h t ht
  have k := GlobalTheory.TorusPart.isGrpPullback_thickLift ha h
  have e : f₀.left ≫ GlobalTheory.TorusPart.thickLift ha h =
      GlobalTheory.TorusPart.thickLift ha h ≫ ((Over.pullback (thick V (maximalIdeal V) 0)).map E.aG).left := by
    apply pullback.hom_ext
    · rw [Category.assoc, GlobalTheory.TorusPart.thickLift_fst, hf, Category.assoc]
      simp only [GlobalTheory.TorusPart.thickLift, Over.pullback_map_left, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc]
    · simp only [GlobalTheory.TorusPart.thickLift, Over.pullback_map_left]
      rw [Category.assoc, pullback.lift_snd, Category.assoc, pullback.lift_snd, pullback.lift_snd, ← Category.assoc,
        Over.w]
  have hc := GlobalTheory.TorusPart.pullTorus_comp k k _ f₀ e (U.gt 0).i
  unfold GlobalTheory.TorusPart.gtTorus
  rw [← hc, hi, htm, GlobalTheory.TorusPart.pullTorus_torusMap_comp]

def pullEnd {S S' : Scheme.{0}} {G : Over S} [GrpObj G] {G' : Over S'} [GrpObj G'] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) (u : G ⟶ G) : G' ⟶ G' :=
  Over.homMk (h.1.lift (φ ≫ u.left) G'.hom (by rw [Category.assoc, Over.w, h.1.w])) (h.1.lift_snd _ _ _)

theorem pullEnd_left {S S' : Scheme.{0}} {G : Over S} [GrpObj G] {G' : Over S'} [GrpObj G'] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) (u : G ⟶ G) : (pullEnd h u).left ≫ φ = φ ≫ u.left :=
  h.1.lift_fst _ _ _

theorem over_of_two_pullbacks {B S₁ : Scheme.{0}} {H : Over B} {G₁ : Over S₁} {X Y : Scheme.{0}} {ξ₁ : S₁ ⟶ B}
    {β₁ : G₁.left ⟶ H.left} (h₁ : IsPullback β₁ G₁.hom H.hom ξ₁) {φW : Y ⟶ H.left} {n : X ⟶ Y} {n₁ : X ⟶ G₁.left}
    {f₀ : X ⟶ X} {FW : Y ⟶ Y} {Fm : H.left ⟶ H.left} {a : G₁.left ⟶ G₁.left}
    (e1 : f₀ ≫ n = n ≫ FW) (e2 : FW ≫ φW = φW ≫ Fm) (e3 : n ≫ φW = n₁ ≫ β₁) (e4 : a ≫ β₁ = β₁ ≫ Fm)
    (e5 : a ≫ G₁.hom = G₁.hom) (e6 : f₀ ≫ n₁ ≫ G₁.hom = n₁ ≫ G₁.hom) : f₀ ≫ n₁ = n₁ ≫ a := by
  apply h₁.hom_ext
  · rw [Category.assoc, ← e3, ← Category.assoc, e1, Category.assoc, e2, ← Category.assoc, e3, Category.assoc,
      Category.assoc, e4]
  · rw [Category.assoc, e6, Category.assoc, e5]

theorem spread₂_endU_comm : ∀ (B : Scheme.{0}) (H : Over B) [GrpObj H] [IsCommMonObj H], IsSemiAbelian H → ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], GlobalTheory.Mum.Base V₁ → ∀ (G₁ : Over (Sp V₁)) [GrpObj G₁] [IsCommMonObj G₁], IsSemiAbelian G₁ → ∀ (D₁ : DegData V₁ (maximalIdeal V₁)) (A₁ : PolAV (Sp (FractionRing V₁))) (U₁ : Unif (maximalIdeal V₁) D₁ A₁ G₁) (ξ₁ : Sp V₁ ⟶ B) (β₁ : G₁.left ⟶ H.left), IsGrpPullback G₁ H ξ₁ β₁ → ∀ (V₂ : Type) [CommRing V₂] [IsDomain V₂] [IsLocalRing V₂], GlobalTheory.Mum.Base V₂ → ∀ (G₂ : Over (Sp V₂)) [GrpObj G₂] [IsCommMonObj G₂], IsSemiAbelian G₂ → ∀ (D₂ : DegData V₂ (maximalIdeal V₂)) (A₂ : PolAV (Sp (FractionRing V₂))) (U₂ : Unif (maximalIdeal V₂) D₂ A₂ G₂) (ξ₂ : Sp V₂ ⟶ B) (β₂ : G₂.left ⟶ H.left), IsGrpPullback G₂ H ξ₂ β₂ → ∀ ρ : D₂.toPre.X →+ D₁.toPre.X, Spread₂ H U₁ ξ₁ β₁ U₂ ξ₂ β₂ ρ → ∀ (Fm : H ⟶ H) (E₁ : EndU U₁.toUnifPre) (E₂ : EndU U₂.toUnifPre), E₁.aG.left ≫ β₁ = β₁ ≫ Fm.left → E₂.aG.left ≫ β₂ = β₂ ≫ Fm.left → ∀ y, ρ (E₂.h y) = E₁.h (ρ y) := by
  intro B H _ _ hH V₁ _ _ _ hV₁ G₁ _ _ hG₁ D₁ A₁ U₁ ξ₁ β₁ h₁ V₂ _ _ _ hV₂ G₂ _ _ hG₂ D₂ A₂ U₂ ξ₂ β₂ h₂ ρ hsp
    Fm E₁ E₂ hE₁ hE₂
  obtain ⟨W, _, _, _, ψ, GW, _, _, φW, j, Ω, _, α, b₁, hb₁, GΩ, _, n, hn, n₁, hn₁, κ, _, c, b₂, hb₂, Gκ, _, m, hm, m₂, hm₂,
    hW, hj, hα, -, -, -, hnφ, hmφ, hjΩ, hjκ⟩ := hsp
  let FW := pullEnd hW Fm
  have hFW : FW.left ≫ φW = φW ≫ Fm.left := pullEnd_left hW Fm

  have key : j ≫ FW = GlobalTheory.SplitTorus.torusMap _ E₁.h ≫ j := by
    have : IsSchemeTheoreticallyDominant (spMap α) :=
      GlobalTheory.ExtUnique.isSchemeTheoreticallyDominant_spec_of_injective _ hα
    have : IsSeparated H.hom := hH.separated
    have : IsSeparated GW.hom := MorphismProperty.of_isPullback hW.1 this
    have : Flat (splitTorusAff ZU D₁.toPre.X).hom :=
      (GlobalTheory.ExtUnique.splitTorusAff_flat_and_isSeparated _ _).1
    have : Flat (splitTorus (Sp W) D₁.toPre.X).hom := inferInstanceAs (Flat (pullback.snd _ _))
    refine GlobalTheory.ExtUnique.over_hom_ext_of_isPullback (GlobalTheory.SplitTorus.isPullback_bcMap (spMap α) _) ?_
    let FΩ := pullEnd hn FW
    have hFΩ : FΩ.left ≫ n = n ≫ FW.left := pullEnd_left hn FW
    have hover : FΩ.left ≫ n₁ = n₁ ≫ E₁.aG.left :=
      over_of_two_pullbacks h₁.1 hFΩ hFW hnφ hE₁ (Over.w E₁.aG)
        (by rw [hn₁.1.w, ← Category.assoc, Over.w FΩ])
    have e1 := GlobalTheory.TorusPart.pullTorus_comp hn hn FW FΩ hFΩ j
    have e2 := GlobalTheory.TorusPart.pullTorus_torusMap_comp hn j E₁.h
    have e3 := endU_gtTorus_comp U₁ E₁ hb₁ hn₁ FΩ hover
    rw [hjΩ, e3] at e1
    rw [hjΩ] at e2
    rw [← GlobalTheory.TorusPart.pullTorus_left hn, ← GlobalTheory.TorusPart.pullTorus_left hn, e1, e2]

  let Fκ := pullEnd hm FW
  have hFκ : Fκ.left ≫ m = m ≫ FW.left := pullEnd_left hm FW
  have hover₂ : Fκ.left ≫ m₂ = m₂ ≫ E₂.aG.left :=
    over_of_two_pullbacks h₂.1 hFκ hFW hmφ hE₂ (Over.w E₂.aG)
      (by rw [hm₂.1.w, ← Category.assoc, Over.w Fκ])
  have hmono := (GlobalTheory.TorusPart.mono_gtTorus_and_factor (U₂.gt 0) hb₂ hm₂).1
  have e := congrArg (GlobalTheory.TorusPart.pullTorus hm) key
  rw [GlobalTheory.TorusPart.pullTorus_comp hm hm FW Fκ hFκ j, GlobalTheory.TorusPart.pullTorus_torusMap_comp hm j, hjκ, Category.assoc,
    endU_gtTorus_comp U₂ E₂ hb₂ hm₂ Fκ hover₂, ← Category.assoc, ← Category.assoc,
    ← GlobalTheory.SplitTorus.torusMap_comp, ← GlobalTheory.SplitTorus.torusMap_comp] at e
  have : Nonempty (Sp κ) := inferInstance
  have e' := GlobalTheory.SplitTorus.torusMap_injective ((cancel_mono _).1 e)
  intro y
  exact DFunLike.congr_fun e' y

end GlobalTheory.Poinc.Sep.Spz
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.nonempty_isPullDeg_of_same_torus_twist : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D₀ D₂ D : DegData R (maximalIdeal R)) (g : GtPt D.toPre (𝟙_ (Over (Sp R)))), GlobalTheory.MumCmp.IsTwist D₀.toPre D.toPre g → GlobalTheory.MumCmp.IsTwist D₂.toPre D.toPre g → Nonempty (IsPullDeg (RingHom.id R) D₀.toPre D₂.toPre) := by
  first | exact @GlobalTheory.MumCmp.Uniq.nonempty_isPullDeg_of_isTwist | exact GlobalTheory.MumCmp.Uniq.nonempty_isPullDeg_of_isTwist | (intros; apply GlobalTheory.MumCmp.Uniq.nonempty_isPullDeg_of_isTwist <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

theorem _root_.GlobalTheory.T.localTriviality_of_noetherian_descent : (∀ (R : Type) [CommRing R] [IsNoetherianRing R] (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A → ∀ (M : LB A.left), M.IsLB → (∃ t : (M.pull (1 : 𝟙_ (Over (Sp R)) ⟶ A).left).Gen, t.IsGen) → ∀ k : ℕ, IsUnit (k : R) → (∃ t : (GlobalTheory.UPel.HT.Hecke.lbPow M k).Gen, t.IsGen) → ∀ (K : Type) [Field K] (g₀ : R →+* K), (∃ t : (M.pull (pullback.fst A.hom (spMap g₀))).Gen, t.IsGen) → ∃ r : R, g₀ r ≠ 0 ∧ ∃ t : (M.pull (A.hom ⁻¹ᵁ PrimeSpectrum.basicOpen r).ι).Gen, t.IsGen) → ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A → ∀ (M : LB A.left), M.IsLB → (∃ t : (M.pull (1 : 𝟙_ (Over (Sp R)) ⟶ A).left).Gen, t.IsGen) → ∀ k : ℕ, IsUnit (k : R) → (∃ t : (GlobalTheory.UPel.HT.Hecke.lbPow M k).Gen, t.IsGen) → ∀ (K : Type) [Field K] (g₀ : R →+* K), (∃ t : (M.pull (pullback.fst A.hom (spMap g₀))).Gen, t.IsGen) → ∃ r : R, g₀ r ≠ 0 ∧ ∃ t : (M.pull (A.hom ⁻¹ᵁ PrimeSpectrum.basicOpen r).ι).Gen, t.IsGen := by
  first | (exact @GlobalTheory.LocTrivDescent.locTriv_of_noetherian) | (exact GlobalTheory.LocTrivDescent.locTriv_of_noetherian) | (intros; apply GlobalTheory.LocTrivDescent.locTriv_of_noetherian <;> assumption)
end
