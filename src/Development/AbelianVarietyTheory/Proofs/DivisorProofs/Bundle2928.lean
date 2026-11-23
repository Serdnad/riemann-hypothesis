module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle070
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle006
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPelUnifPull
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle127
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsPelUnifPsiCoord
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle104
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle191
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2761
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2805
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1972
public import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2589
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle670
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle665
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle004
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle071
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.DenseGenericOfFlat
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNsmulEqZeroOfIsIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2752
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle689
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle134
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle063

@[expose] public section

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UChart

theorem trait_pull {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    {l : Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l} {φ : InvFun (𝓞 E)} {R : Type} [CommRing R] [IsDomain R]
    [IsLocalRing R] (C : MonoFam Xo c φ R) (hR : GlobalTheory.Mum.Base R) (W : Type) [CommRing W] [IsDomain W]
    [IsLocalRing W] (hW : GlobalTheory.UU.CDVR W) (ϖ : W) (ρ : R →+* W) (hinj : Function.Injective ρ) (hloc : IsLocalHom ρ)
    (w : Fin C.m → ℕ) (u : Fin C.m → Wˣ) (hs : ∀ i, ρ (C.s i) = u i * ϖ ^ w i) :
    ∃ (t : SAB H (Sp W)) (P : PELUnif (maximalIdeal W) t) (e : P.D.toPre.X ≃ₗ[𝓞 E] C.P.D.toPre.X)
      (be : LinearMap.BilinForm ℤ P.D.toPre.X),
      Nonempty (SABMap t C.t (spMap ρ)) ∧
      (∀ κ : Sp (FractionRing W) ⟶ Sp (FractionRing R), κ ≫ jK R = jK W ≫ spMap ρ →
        ∃ tK : SAB H (Sp (FractionRing W)), Nonempty (SABMap tK t (jK W)) ∧
          Nonempty (SABMap tK Xo.univ.t ((κ ≫ C.y) ≫ pullback.fst _ _))) ∧
      be = ∑ i, (w i : ℤ) • pull e.toLinearMap ((l.M' : ℤ) • C.δ i) ∧
      be ∈ levelForms H 1 P.D.toPre.X ∧ IsMonomial P.D.toPre ![ϖ] ![be] ∧
      φ.evalZ be = ∑ i, (w i : ℝ) * φ.evalZ ((l.M' : ℤ) • C.δ i) := by
  obtain ⟨h1, -, h3, h4, h5⟩ := GlobalTheory.firstFiveLaws
  obtain ⟨hdvr, hcomp, -⟩ := hW
  have hWa : AdmBase W (maximalIdeal W) := ⟨inferInstance, inferInstance, inferInstance, hcomp⟩
  have hI : (maximalIdeal R).map ρ ≤ maximalIdeal W := ((IsLocalRing.local_hom_tfae ρ).out 1 3).1 hloc
  obtain ⟨t', m₀, P', hD, -, -, -, -, hlin, -⟩ := GlobalTheory.ArcDataDescent.exists_pelUnif_pull h3.cubePull h1.polBaseChange
    h4.unifBaseChange h5 hR.1 hWa C.t C.P ρ hinj hI
  let e : P'.D.toPre.X ≃ₗ[𝓞 E] C.P.D.toPre.X := { hD.xe with map_smul' := hlin }
  have he : ∀ y, e y = hD.xe y := fun _ => rfl
  refine ⟨t', P', e, ∑ i, (w i : ℤ) • pull e.toLinearMap ((l.M' : ℤ) • C.δ i), ⟨m₀⟩, ?_, rfl, ?_, ?_, ?_⟩
  · intro κ hκ
    obtain ⟨tKR, ⟨n1⟩, ⟨n2⟩⟩ := C.gen
    obtain ⟨tK, ⟨k⟩⟩ := GlobalTheory.Models.Inhab.exists_pull κ tKR
    obtain ⟨a, -⟩ := sabComp pullCubComp E H _ _ _ C.t tKR tK (jK R) κ n1 k
    rw [hκ] at a
    obtain ⟨b, -⟩ := sabCancel pullCubCancel E H _ _ _ C.t t' tK (spMap ρ) (jK W) m₀ a
    obtain ⟨d, -⟩ := sabComp pullCubComp E H _ _ _ Xo.univ.t tKR tK _ κ n2 k
    rw [← Category.assoc] at d
    exact ⟨tK, ⟨b⟩, ⟨d⟩⟩
  · rw [← balForms_eq_levelForms]
    exact Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _ (pull_mem _ (Submodule.smul_mem _ _ (C.cone.mem i)))
  · intro y
    obtain ⟨u0, n, hn, hc⟩ := C.mono (hD.xe y)
    obtain ⟨u', hu'⟩ := GlobalTheory.PelCoordPull.psiCoord_pull hD y _ hc
    refine ⟨u' * Units.map ρ.toMonoidHom u0 * ∏ i, u i ^ n i, fun _ => ∑ i, w i * n i, fun j => ?_, ?_⟩
    · fin_cases j
      show (∑ i, (w i : ℤ) • pull e.toLinearMap ((l.M' : ℤ) • C.δ i)) y y = 2 * ((∑ i, w i * n i : ℕ) : ℤ)
      rw [LinearMap.sum_apply, LinearMap.sum_apply]
      push_cast
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      have h2 : ((l.M' : ℤ) • C.δ i) (hD.xe y) (hD.xe y) = 2 * n i := hn i
      rw [LinearMap.smul_apply, LinearMap.smul_apply, pull_apply]
      rw [show (e.toLinearMap y) = hD.xe y from rfl, h2]
      simp only [smul_eq_mul]; ring
    · convert hu' using 1
      simp only [Fin.prod_univ_one, Matrix.cons_val_zero, map_mul, map_prod, map_pow, hs, Units.val_mul,
        Units.coe_map, Units.coe_prod, Units.val_pow_eq_pow_val, mul_pow, Finset.prod_mul_distrib,
        ← pow_mul, Finset.prod_pow_eq_pow_sum, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe]
      ring
  · have hsum : (∑ i, (w i : ℤ) • pull e.toLinearMap ((l.M' : ℤ) • C.δ i)) =
        pull e.toLinearMap (∑ i, (w i : ℤ) • ((l.M' : ℤ) • C.δ i)) := by
      ext a b; simp [LinearMap.sum_apply, pull_apply]
    rw [hsum, evalZ_pull φ e.surjective]
    have hl := C.cone.linearOn_smul l.M' (fun i => (w i : ℝ)) (fun i => Nat.cast_nonneg _)
    refine Eq.trans ?_ hl
    unfold InvFun.evalZ
    congr 1
    funext a b
    simp [LinearMap.sum_apply]

end GlobalTheory.UChart

namespace GlobalTheory.UChart

theorem pull_trait : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (C : MonoFam Xo c φ R) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], GlobalTheory.LN.CDvr W → ∀ (ψ : R →+* W), Function.Injective ψ → IsLocalHom ψ → ∀ (ϖ : W), Irreducible ϖ → ∀ (w : Fin C.m → ℕ), (∀ i, Associated (ψ (C.s i)) (ϖ ^ w i)) → ∀ κ : Sp (FractionRing W) ⟶ Sp (FractionRing R), κ ≫ jK R = jK W ≫ spMap ψ → ∃ (t : SAB H (Sp W)) (tK : SAB H (Sp (FractionRing W))) (P : PELUnif (maximalIdeal W) t), Nonempty (SABMap tK t (jK W)) ∧ Nonempty (SABMap tK Xo.univ.t ((κ ≫ C.y) ≫ pullback.fst _ _)) ∧ ∃ be ∈ levelForms H 1 P.D.toPre.X, IsMonomial P.D.toPre ![ϖ] ![be] ∧ φ.evalZ be = ∑ i, (w i : ℝ) * φ.evalZ ((l.M' : ℤ) • C.δ i) := by
  intro E _ _ _ H Dw l Xo c φ R _ _ _ hR C W _ _ _ hW ψ hinj hloc ϖ _ w hw κ hκ
  choose v hv using hw
  obtain ⟨t, P, e, be, -, htK, -, hbe, hmon, hev⟩ :=
    trait_pull C hR W hW ϖ ψ hinj hloc w (fun i => (v i)⁻¹) (fun i => by rw [← hv i, mul_left_comm, Units.inv_mul, _root_.mul_one])
  obtain ⟨tK, h1, h2⟩ := htK κ hκ
  exact ⟨t, tK, P, h1, h2, be, hbe, hmon, hev⟩

end GlobalTheory.UChart
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.FactorAmple

open GlobalTheory.CechPic

theorem lam_rosati {K : Type} [Field K] {B : Over (Sp K)} [GrpObj B] [IsCommMonObj B] {M : LB B.left} (hM : M.IsLB)
    {u v : B ⟶ B} (h : RosatiAdj B M u v) {T : Over (Sp K)} (x y : T ⟶ B) :
    lam (cls M hM) (x ≫ u) y = lam (cls M hM) x (y ≫ v) := by
  have e := GlobalTheory.AdjPolLocal.lbIso_of_rosatiAdj_local K B M u v hM h
  have h1 : (cubeLB B ![fst B B ≫ u, snd B B] M).IsLB := LB.isLB_linComb hM _ _
  have h2 : (cubeLB B ![fst B B, snd B B ≫ v] M).IsLB := LB.isLB_linComb hM _ _
  have e' := (cls_eq_iff h1 h2).2 e
  rw [cls_cube_two hM, cls_cube_two hM] at e'
  have e'' := congrArg (pull (lift x y : T ⟶ G2 B).left) e'
  rw [pull_lam, pull_lam] at e''
  simpa using e''

theorem act_nsmul {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] {O : Type} [Ring O] (ρ : RingAct A O)
    (u : O) (n : ℕ) : ρ.act (n • u) = ρ.act u ^ n := by
  have h0 : ρ.act 0 = 1 := by
    have e := ρ.map_add 0 0
    rw [add_zero] at e
    have e' : ρ.act 0 * 1 = ρ.act 0 * ρ.act 0 := by rw [_root_.mul_one]; exact e.trans (Hom.mul_def _ _).symm
    exact (mul_left_cancel e').symm
  induction n with
  | zero => rw [zero_smul, pow_zero, h0]
  | succ n ih => rw [succ_nsmul, ρ.map_add, ih, pow_succ]; exact (Hom.mul_def _ _).symm

theorem lam_push {S S' : Scheme.{0}} {G : Over S} {H : Over S'} [GrpObj G] [IsCommMonObj G] [GrpObj H]
    [IsCommMonObj H] {f : S' ⟶ S} {φ : H.left ⟶ G.left} (hp : IsGrpPullback H G f φ) (c : Pic G.left)
    {T : Over S'} (z w : T ⟶ H) :
    lam c (pushHom hp T z) (pushHom hp T w) = lam (pull φ c) z w := by
  simp only [lam, ← map_mul, ← map_one (pushHom hp T)]
  simp only [← pull_comp]
  rfl

end GlobalTheory.Mum.FactorAmple

namespace GlobalTheory.Mum

open GlobalTheory.CechPic GlobalTheory.Mum.FactorAmple

theorem factorPairing_diag_relAmple : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D D' : DegData R (maximalIdeal R)) (F : Factor D.toPre D'.toPre) (_ : F.Alg) (A' : PolAV (Sp (FractionRing R))) (G' : Over (Sp R)) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (U' : Unif (maximalIdeal R) D' A' G') (oA : A'.OAct F.O) (oG : RingAct G' F.O), U'.toUnifPre.OLinear F.O F.o oA oG → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (inc : G ⟶ G') (pr : G' ⟶ G), IsMonHom inc → IsMonHom pr → inc ≫ pr = 𝟙 G → pr ≫ inc = oG.act F.e → ∀ κ₀ : (G2 ((Over.pullback (jK R)).obj G)).left ⟶ (G2 G).left, Geo.Tor.IsSquare (G' := ((Over.pullback (jK R)).obj G)) (G := G) (pullback.fst G.hom (jK R)) κ₀ → Out.RelAmple ((Over.pullback (jK R)).obj G) ((((abelian₂ G' U'.LG.L).pull (lift (fst G G ≫ inc) (snd G G ≫ inc ≫ oG.act F.f) : G2 G ⟶ G2 G').left).pull κ₀).pull (lift (𝟙 ((Over.pullback (jK R)).obj G)) (𝟙 ((Over.pullback (jK R)).obj G)) : ((Over.pullback (jK R)).obj G) ⟶ G2 ((Over.pullback (jK R)).obj G)).left) := by
  intro R _ _ _ hR D D' F hF A' G' _ _ hG' U' oA oG hlin G _ _ hG inc pr hinc hpr hip hpi κ₀ hκ
  have := A'.isAb.comm
  have hp := isGrpPullback_pullback G (jK R)
  have hp' := isGrpPullback_pullback G' (jK R)
  let X := (Over.pullback (jK R)).obj G
  let ιK : X ⟶ (Over.pullback (jK R)).obj G' := (Over.pullback (jK R)).map inc
  let a : X ⟶ A'.A := ιK ≫ U'.gen.hom
  have hM := A'.isLB
  have hL' : U'.LG.L.IsLB := U'.LG.isLB
  have hΛ : (abelian₂ G' U'.LG.L).IsLB := LB.isLB_linComb hL' _ _
  have h1 := pull_isLB hΛ (lift (fst G G ≫ inc) (snd G G ≫ inc ≫ oG.act F.f) : G2 G ⟶ G2 G').left
  have h2 := pull_isLB h1 κ₀
  have h3 := pull_isLB h2 (lift (𝟙 X) (𝟙 X) : X ⟶ G2 X).left
  have e1 : pushHom hp X (𝟙 X) ≫ inc = pushHom hp' X ιK := by
    ext1
    show (𝟙 _ ≫ pullback.fst G.hom (jK R)) ≫ inc.left = ιK.left ≫ pullback.fst G'.hom (jK R)
    rw [Category.id_comp]
    exact (pullback.lift_fst _ _ _).symm
  have e2 : pushHom hp X (𝟙 X) ≫ inc ≫ oG.act F.f =
      pushHom hp' X (ιK ≫ (Over.pullback (jK R)).map (oG.act F.f)) := by
    rw [← Category.assoc, e1]
    ext1
    show (ιK.left ≫ pullback.fst G'.hom (jK R)) ≫ (oG.act F.f).left =
      (ιK ≫ (Over.pullback (jK R)).map (oG.act F.f)).left ≫ pullback.fst G'.hom (jK R)
    rw [Over.comp_left, Category.assoc, Category.assoc]
    exact congrArg (ιK.left ≫ ·) (pullback.lift_fst _ _ _).symm
  have eN : cls _ h3 = lam (cls _ hL') (pushHom hp X (𝟙 X) ≫ inc) (pushHom hp X (𝟙 X) ≫ inc ≫ oG.act F.f) := by
    rw [cls_pull h2, cls_pull h1, cls_pull hΛ, ← pull_comp, ← pull_comp]
    rw [← Category.assoc, FactorAdd.lift_square hp hκ, ← Over.comp_left]
    have e : cls (abelian₂ G' U'.LG.L) hΛ = lam (cls _ hL') (fst G' G') (snd G' G') := cls_cube_two hL' _ _ hΛ
    rw [e, pull_lam]
    simp
  have hgen := U'.gen_hom
  have eT : pull (pullback.fst G'.hom (jK R)) (cls _ hL') = pull U'.gen.hom.left (cls _ hM) := by
    obtain ⟨w, hw⟩ := U'.ext
    rw [← cls_pull hL' _ (pull_isLB hL' _), ← cls_pull hM _ (pull_isLB hM _)]
    exact ((cls_eq_iff (pull_isLB hM _) (pull_isLB hL' _)).2 ⟨w, hw⟩).symm
  have eN' : cls _ h3 = lam (cls _ hM) a (a ≫ oA.act F.f) := by
    rw [eN, e2, e1, lam_push hp', eT, lam_pull]
    congr 1
    rw [Category.assoc, Category.assoc, hlin.ext F.f]
  have hie : inc ≫ oG.act F.e = inc := by rw [← hpi, ← Category.assoc, hip, Category.id_comp]
  have ha : a ≫ oA.act F.e = a := by
    show (ιK ≫ U'.gen.hom) ≫ oA.act F.e = ιK ≫ U'.gen.hom
    rw [Category.assoc, ← hlin.ext F.e, ← Category.assoc, ← Functor.map_comp, hie]
  have hΘ : ∃ t : LB.Gen (Theta A'.A A'.L), t.IsGen := GlobalTheory.GenericAmpleDvr.triv_theta A'.isAb hM
  obtain ⟨⟨b, hb, hbe⟩, -, -⟩ := hF
  have rosE : ∀ x y : X ⟶ A'.A, lam (cls _ hM) (x ≫ oA.act F.e) y = lam (cls _ hM) x (y ≫ oA.act (star F.e)) :=
    fun x y => lam_rosati hM (oA.rosati F.e) x y
  have hpow : ∀ (u : F.O) (n : ℕ), (a ≫ oA.act u) ^ n = a ≫ oA.act (n • u) := by
    intro u n
    rw [act_nsmul oA.toRingAct]
    exact (map_pow (preHom (G := A'.A) a) (oA.act u) n).symm
  have eb : b • cls _ h3 = lam (cls _ hM) a a := by
    rw [eN']
    calc b • lam (cls _ hM) a (a ≫ oA.act F.f)
        = b • lam (cls _ hM) (a ≫ oA.act F.e) ((a ≫ oA.act F.e) ≫ oA.act F.f) := by rw [ha]
      _ = b • lam (cls _ hM) a (a ≫ oA.act (star F.e * F.f * F.e)) := by
          rw [rosE, oA.map_mul, oA.map_mul]; simp only [Category.assoc]
      _ = lam (cls _ hM) a ((a ≫ oA.act (star F.e * F.f * F.e)) ^ b) := (lam_pow_right hM hΘ _ _ b).symm
      _ = lam (cls _ hM) a (a ≫ oA.act (star F.e * F.e)) := by rw [hpow, hbe]
      _ = lam (cls _ hM) (a ≫ oA.act F.e) (a ≫ oA.act F.e) := by
          rw [oA.map_mul, ← Category.assoc, ← rosE]
      _ = lam (cls _ hM) a a := by rw [ha]
  have hΛA : (abelian₂ A'.A A'.L).IsLB := LB.isLB_linComb hM _ _
  have hDg := pull_isLB hΛA (lift (𝟙 A'.A) (𝟙 A'.A) : A'.A ⟶ G2 A'.A).left
  have eD : lam (cls _ hM) a a = cls _ (pull_isLB hDg a.left) := by
    have e : cls (abelian₂ A'.A A'.L) hΛA = lam (cls _ hM) (fst A'.A A'.A) (snd A'.A A'.A) := cls_cube_two hM _ _ hΛA
    rw [cls_pull hDg, cls_pull hΛA, e, pull_lam, pull_lam]
    simp
  have hNb := isLB_lbPow h3 b
  have iso := (cls_eq_iff hNb (pull_isLB hDg a.left)).1 (by rw [cls_lbPow h3, eb, eD])
  have := hG'.separated
  have : IsSeparated ((Over.pullback (jK R)).obj G').hom := by dsimp; infer_instance
  let prK : (Over.pullback (jK R)).obj G' ⟶ X := (Over.pullback (jK R)).map pr
  have hs : ιK ≫ prK = 𝟙 X := by rw [← Functor.map_comp, hip]; exact (Over.pullback (jK R)).map_id G
  have : IsSeparated prK.left := by
    have e : prK.left ≫ X.hom = ((Over.pullback (jK R)).obj G').hom := Over.w prK
    have : IsSeparated (prK.left ≫ X.hom) := by rw [e]; infer_instance
    exact IsSeparated.of_comp prK.left X.hom
  have : IsClosedImmersion ιK.left := by
    have : IsClosedImmersion (ιK.left ≫ prK.left) := by
      rw [← Over.comp_left, hs]; exact inferInstanceAs (IsClosedImmersion (𝟙 _))
    exact IsClosedImmersion.of_comp ιK.left prK.left
  have : IsIso U'.gen.hom.left := ((Over.forget _).mapIso U'.gen).isIso_hom
  have : IsFinite a.left := by
    show IsFinite (ιK ≫ U'.gen.hom).left
    rw [Over.comp_left]; infer_instance
  have := A'.isAb.proper
  have : IsProper X.hom := by
    have e : a.left ≫ A'.A.hom = X.hom := Over.w a
    rw [← e]; infer_instance
  have hDgA := GlobalTheory.isAmpleLB_of_relAmple_of_isAffine A'.A hDg
    (GlobalTheory.EighthPowerFactor.relAmple_diag_lam A'.isAb hM hΘ A'.ample)
  have hNa := (hDgA.pull_of_isFinite a.left).of_lbIso hNb iso
  exact (GlobalTheory.relAmple_iff_isAmpleLB_of_isAffine X h3).2 ((GlobalTheory.isAmpleLB_pow_iff h3 hb).1 hNa)

end GlobalTheory.Mum
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UChartOf

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem inv_apply_self {X Y : Scheme.{0}} (f : X ⟶ Y) [IsIso f] (x : X) : inv f (f x) = x := by
  rw [← Scheme.Hom.comp_apply, IsIso.hom_inv_id]; rfl

theorem chart_of_data {φ : InvFun (𝓞 E)} (Y : Model Xo c (RingHom.id c.F)) (BD' : EffCartierData Y.X) (d : ℕ)
    (x : gen Y) {k : Type} [Field k] {m e : ℕ} (ξ' : Sp (ChartRing k m e) ⟶ gen Y) (t : SAB H (Sp (ChartRing k m e)))
    (P : PELUnif (maximalIdeal (ChartRing k m e)) t) (n : ℕ) (h : n = m) (s : Fin n → ChartRing k m e)
    (hs : ∀ i, s i = bdParam k m e (Fin.cast h i)) (δ : Fin n → LinearMap.BilinForm ℤ P.D.toPre.X) (a : Fin n → ℕ)
    (hx : ξ' (closedPoint _) = x) (het : IsEtaleCompletion (Scheme.stalkClosedPointTo ξ').hom)
    (hid : idlAlong (genBdIdeal Y) ξ' = Ideal.span {∏ i, s i})
    (hset : ∀ p : Sp (ChartRing k m e), ξ' p ∈ genBd Y ↔ ∏ i, s i ∈ p.asIdeal)
    (hsab : Nonempty (SABMap t Y.t (ξ' ≫ genι Y)))
    (hmono : IsMonomial P.D.toPre s (fun i => (l.M' : ℤ) • δ i))
    (hrank : Module.finrank (𝓞 E) P.D.toPre.X ≤ min Dw.p Dw.q) (hcone : IsCone H.bar φ δ)
    (ha : ∀ i, (a i : ℝ) = d * φ.evalZ ((l.M' : ℤ) • δ i))
    (hBD : idlAlong BD'.idealSheaf (ξ' ≫ genι Y) = Ideal.span {∏ i, s i ^ a i})
    (hrig : GlobalTheory.RigChart.IsRigid P.D.toPre s (fun i => (l.M' : ℤ) • δ i)) :
    GlobalTheory.MumfordChart.HasChartOf φ Y BD' d x ∧ GlobalTheory.RigChart.HasRigidChart Y x := by
  subst h
  obtain rfl : s = bdParam k n e := funext fun i => by simpa using hs i
  have hmem : ∀ i, (l.M' : ℤ) • δ i ∈ levelForms H l.M' P.D.toPre.X := fun i =>
    (mem_levelForms_iff_smul (GlobalTheory.MumfordChart.level_ne_zero l)).2
      ⟨δ i, (balForms_eq_levelForms H P.D.toPre.X) ▸ hcone.mem i, rfl⟩
  let gam : Fin n → levelForms H l.M' P.D.toPre.X := fun i => ⟨(l.M' : ℤ) • δ i, hmem i⟩
  have hgam : ∀ i, (gam i : LinearMap.BilinForm ℤ P.D.toPre.X) = (l.M' : ℤ) • δ i := fun _ => rfl
  have hpb : IsPartOfBasis gam := hcone.isPartOfBasis_level (GlobalTheory.MumfordChart.level_ne_zero l) hgam
  exact ⟨⟨k, _, n, e, ξ', t, P, gam, δ, a, hx, het, hid, fun p => (hset p).trans Iff.rfl, hsab, hmono, hrank, hcone, hgam,
      ha, hBD⟩,
    ⟨k, _, n, e, ξ', t, P, gam, hx, het, hid, hset, hsab, hmono, hpb, hrig⟩⟩

end GlobalTheory.UChartOf

namespace GlobalTheory.UChartOf

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem charts_of_upre {φ : InvFun (𝓞 E)} {S : Scheme.{0}} {j : Xo.XF c ⟶ S} [IsOpenImmersion j]
    {BD : EffCartierData S} {d : ℕ} (Y : Model Xo c (RingHom.id c.F)) (ε : Y.X ≅ S) (hj : Y.j ≫ ε.hom = j)
    (hsab : ∀ {k : Type} [Field k] {m e : ℕ} (C : MonoFam Xo c φ (ChartRing k m e)), IsTaut C →
      ∀ ξ : Sp (ChartRing k m e) ⟶ S, C.y ≫ j = jK _ ≫ ξ → Nonempty (SABMap C.t Y.t (ξ ≫ ε.inv)))
    (hpre : ∀ x : S, x ∉ Set.range j → UPre Xo c φ j BD d x) (x : gen Y) (hx : x ∈ genBd Y) :
    GlobalTheory.MumfordChart.HasChartOf φ Y (BD.pull ε.hom (BD.keepsRegular_of_flat _)) d x ∧
      GlobalTheory.RigChart.HasRigidChart Y x := by
  let π : gen Y ⟶ S := genι Y ≫ ε.hom
  have hjQ : Y.jQ ≫ π = j := by
    simp only [π, ← Category.assoc]
    exact hj
  have hrange : ∀ w : gen Y, w ∈ Set.range Y.jQ ↔ π w ∈ Set.range j := by
    intro w
    constructor
    · rintro ⟨z, rfl⟩
      exact ⟨z, by rw [← hjQ]; rfl⟩
    · rintro ⟨z, hz⟩
      refine ⟨z, ?_⟩
      have : π (Y.jQ z) = π w := by rw [← hz, ← hjQ]; rfl
      rw [← inv_apply_self π (Y.jQ z), this, inv_apply_self]
  have hx' : π x ∉ Set.range j := fun h => hx ((hrange x).2 h)
  obtain ⟨k, _, m, e, C, ξ, a, htaut, hy, hcl, het, hbd, hset, ha, hBD⟩ := hpre (π x) hx'
  obtain ⟨hm, hs, -, -, hrig, -, -⟩ := id htaut
  let ξ' : Sp (ChartRing k m e) ⟶ gen Y := ξ ≫ inv π
  have hξ : ξ' ≫ π = ξ := by simp [ξ']
  have hξg : ξ' ≫ genι Y = ξ ≫ ε.inv := by
    simp only [ξ', π, IsIso.inv_comp, IsIso.Iso.inv_hom, Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  have hvan : (Scheme.IdealSheafData.vanishingIdeal j.opensRange.compl).comap π = genBdIdeal Y :=
    GlobalTheory.vanishingIdeal_comap_of_isOpenImmersion (gen Y) S π _ (genBd Y) fun w =>
      (not_congr (hrange w)).trans Iff.rfl
  refine chart_of_data Y _ d x ξ' C.t C.P C.m hm C.s hs C.δ a ?_ ?_ ?_ ?_ ?_ C.mono C.rank C.cone ha ?_ hrig.1
  · change inv π (ξ (closedPoint _)) = x
    rw [hcl, inv_apply_self]
  · exact GlobalTheory.Member.isEtaleCompletion_stalkClosedPointTo_comp_iso ξ (inv π) het
  · rw [← hvan, GlobalTheory.TorRef.idlAlong_comap, hξ]
    exact hbd
  · intro p
    rw [mem_genBd, hrange, ← Scheme.Hom.comp_apply, hξ, hset p, not_not]
  · rw [hξg]
    exact hsab C htaut ξ hy
  · rw [EffCartierData.idealSheaf_pull, GlobalTheory.TorRef.idlAlong_comap, hξg, Category.assoc, ε.inv_hom_id,
      Category.comp_id]
    exact hBD

end GlobalTheory.UChartOf
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.HodgeMin

open GlobalTheory.CechPic

theorem hodge_pow_iso_pull_pow_of_minimal_compactification : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (Z : Scheme.{0}) (z : Z ⟶ Sp (cycAway n)) (i : F.X ⟶ Z) (OZ : LB Z) (S : Scheme.{0}) (π : S ⟶ Z) (j : F.X ⟶ S) [IsOpenImmersion j] (G : Over S) [GrpObj G] (e : F.univ.A.left ⟶ G.left), MinAt5 F z i OZ → Geo.Tor.IsNormalScheme S → IsProjOver (π ≫ z) → Dense (Set.range j) → j ≫ π = i → IsSemiAbelian G → SmoothOfRelativeDimension g G.hom → IsGrpPullback F.univ.A G j e → ∃ a N : ℕ, 1 ≤ a ∧ 1 ≤ N ∧ LBIso (lbPow (hodge G g) N) (lbPow (OZ.pull π) a) := by
  intro g n F Z z i OZ S π j _ G _ e hM hS hp hj hji hG hsm he
  obtain ⟨o', _, β, S', s', U, c, π', G', _, e', _, N, ⟨-, hz, -, hiz, -, hO, -⟩,
    ⟨-, -, -, hS', -, _, _, hU, -, -, _, _⟩, ⟨hG', hsm', he'⟩, hN, hiso⟩ := hM
  have := GlobalTheory.CycAwayReg.isDedekindDomain_cycAway n
  have := GlobalTheory.ThetaDescent.isProper_of_isProjOver hp
  have : QuasiSeparated π := .of_comp π z
  have : IsLocallyNoetherian S' := LocallyOfFiniteType.isLocallyNoetherian π'
  have : IsLocallyNoetherian S := LocallyOfFiniteType.isLocallyNoetherian (π ≫ z)
  have : CompactSpace S := QuasiCompact.compactSpace_of_compactSpace (π ≫ z)
  have : AlgebraicGeometry.IsNoetherian S := {}
  have hd : Dense (⇑(c ≫ j) '' {x | (((c ≫ j) ≫ π ≫ z) x).asIdeal = ⊥}) := by
    refine (DenseRange.dense_image hj j.continuous F.isReduced_and_dense.2).mono ?_
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨y, rfl⟩ := c.surjective x
    refine ⟨y, ?_, by simp⟩
    rw [Category.assoc, reassoc_of% hji, hiz]
    exact hx
  obtain ⟨W, p, p', H, _, α, α', _, _, hw, h₁, h₂⟩ := exists_common_cover z π π' (GlobalTheory.IsNormalScheme.pred S') (c ≫ j) U.ι
    (by rw [Category.assoc, hji, hU]) hd hG hG' ((isGrpPullback_pullback F.univ.A c).comp he) he'
  have := hG.separated
  have := hG'.separated
  have v₁ := GlobalTheory.LieVB.isVB_omega G g
  have v₂ := GlobalTheory.LieVB.isVB_omega G' g
  have l₁ : (hodge G g).IsLB := v₁.isLB_det
  have l₂ : (hodge G' g).IsLB := v₂.isLB_det
  have l₃ : (hodge H g).IsLB := (GlobalTheory.LieVB.isVB_omega_of_isGrpPullback h₁ v₁).isLB_det
  have e₁ := (cls_eq_iff (pull_isLB l₁ p) l₃).2 (HodgeGenDesc.lbIso_hodge_pull h₁ v₁)
  have e₂ := (cls_eq_iff (pull_isLB l₂ p') l₃).2 (HodgeGenDesc.lbIso_hodge_pull h₂ v₂)
  have e₃ := (cls_eq_iff (pull_isLB hO π') (isLB_lbPow l₂ N)).2 hiso
  rw [cls_pull l₁] at e₁
  rw [cls_pull l₂] at e₂
  rw [cls_pull hO, cls_lbPow l₂] at e₃
  obtain ⟨d, hd, h⟩ := exists_nsmul_eq_zero hS p (N • cls _ l₁ - pull π (cls _ hO)) (by
    rw [map_sub, map_nsmul, ← pull_comp, hw, pull_comp, e₃, map_nsmul, e₁, e₂, sub_self])
  refine ⟨d, d * N, hd, Nat.mul_pos hd hN,
    (cls_eq_iff (isLB_lbPow l₁ _) (isLB_lbPow (pull_isLB hO π) _)).1 ?_⟩
  rw [cls_lbPow l₁, cls_lbPow (pull_isLB hO π), cls_pull hO, mul_smul, ← sub_eq_zero, ← smul_sub, h]

end GlobalTheory.HodgeMin

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

theorem GlobalTheory.UPoinc.compat_forces_congMod : ∀ (G₁ G Y : Type) [AddCommGroup G₁] [AddCommGroup G] [AddCommGroup Y] (L₁ L K : ℕ), K * L₁ = L → 0 < L → (∀ (n : ℕ) (x : Y), 0 < n → n • x = 0 → x = 0) → ∀ (lab : G₁ →+ G) (yy₁ : G₁ →+ ModN L₁ Y), Function.Surjective yy₁ → ∀ (yy yy' : G →+ ModN L Y), (∀ a μ, yy₁ a = QuotientAddGroup.mk μ → yy (lab a) = QuotientAddGroup.mk (K • μ)) → (∀ a μ, yy₁ a = QuotientAddGroup.mk μ → yy' (lab a) = QuotientAddGroup.mk (K • μ)) → ∀ g : Y →+ Y, (∀ a μ, yy a = QuotientAddGroup.mk μ → yy' a = QuotientAddGroup.mk (g μ)) → ∀ x, CongMod L₁ (g x) x := by
  intro G₁ G Y _ _ _ L₁ L K hKL hL htf lab yy₁ hsurj yy yy' h1 h2 g hg x
  obtain ⟨b, hb⟩ := hsurj (QuotientAddGroup.mk x)
  have e1 := h1 b x hb
  have e2 := h2 b x hb
  have e3 := hg (lab b) (K • x) e1
  rw [e2, map_nsmul] at e3
  rw [QuotientAddGroup.eq] at e3
  obtain ⟨w, hw⟩ := e3
  simp only [nsmulAddMonoidHom_apply] at hw
  have hK : 0 < K := by
    rcases Nat.eq_zero_or_pos K with h | h
    · subst h; omega
    · exact h
  refine ⟨w, ?_⟩
  apply sub_eq_zero.mp
  apply htf K _ hK
  rw [smul_sub, smul_add, smul_smul, hKL, hw]
  abel
end
