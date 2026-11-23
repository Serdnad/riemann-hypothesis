module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBTransport
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle002
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle021
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ThetaGen
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.CstDvdOfCstMulEqZero
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle013
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle006
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle024
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle187
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TraceFormTwistIsoOfPullback
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle044
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle125
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle175
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1016
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.OLinBaseChangeSt
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle127
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle037
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationDegenerationDataUnique
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle131
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle121
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.WittVector.IsPoly
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBCorr
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PullUUnitsCompatGeneric
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.GeneratorPullback.PullAlong
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.DimSplitPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle019
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.PullSec
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle643
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
public import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Mum.GenDesc

noncomputable section

namespace GlobalTheory.MumLin

variable {X Y Z : Scheme.{0}} {L : LB X}

theorem exists_gen_diff (hL : L.IsLB) (σ : X ⟶ X) (h : LBIso L (L.pull σ)) :
    ∃ w : LB.Gen (LB.LinComb L (K := Fin 2) ![𝟙 X, σ] ![1, -1]), w.IsGen := by
  have h1 := (GlobalTheory.TripleCompare.lbIso_iff_pull_id L (L.pull σ)).1 h
  obtain ⟨t, ht⟩ := (GlobalTheory.TripleCompare.lbIso_iff_gen _ _ _ _).1 h1
  obtain ⟨w, hw, -⟩ := DVR.gen_transport (φ' := ![𝟙 X, σ]) (ε' := ![1, -1]) hL (by
    rw [DVR.sameSum_iff_fsum, DVR.fsum_sumElim]
    simp [DVR.fsum, Fin.sum_univ_two]) t ht
  exact ⟨w, hw⟩

theorem corr_of_pull_section (hL : L.IsLB) {K K' : Type} [Fintype K] [Fintype K']
    {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ}
    {t : LB.Gen (LB.LinComb L φ ε)} {t' : LB.Gen (LB.LinComb L φ' ε')} (ht : t.IsGen) (ht' : t'.IsGen)
    (hs : DVR.fsum φ ε = DVR.fsum φ' ε') (p : Y ⟶ Z) (z : Z ⟶ Y) (hzp : z ≫ p = 𝟙 Z)
    (hp : Function.Surjective p.appTop.hom)
    (H : LB.Gen.Corr L _ ε _ ε' (LB.pullGen L φ ε t z) (LB.pullGen L φ' ε' t' z)) :
    LB.Gen.Corr L φ ε φ' ε' t t' := by
  have hq : (LB.mulGen L _ _ _ _ t (LB.invGen L φ' ε' t')).IsGen :=
    DVR.mulGen_isGen_of_isGen t ht _ (DVR.invGen_isGen_of_isGen t' ht')
  have h0 : DVR.fsum (fun k => 𝟙 Y ≫ Sum.elim φ φ' k) (Sum.elim ε fun k => -ε' k) = 0 := by
    rw [DVR.fsum_comp, DVR.fsum_sumElim, DVR.fsum_neg, hs, add_neg_cancel, Finsupp.mapDomain_zero]
  obtain ⟨c, hc⟩ := DVR.exists_value hL _ _ _ hq (𝟙 Y) h0
  have key : ∀ (W : Scheme.{0}) (r : W ⟶ Y) (w : W) (J : (W ⟶ X) → L.ι), Good L w J →
      val (LB.mulGen L _ _ _ _ t (LB.invGen L φ' ε' t')) r w J = gm r w ⊤ c := by
    intro W r w J hJ
    have e1 := val_pull hJ (LB.mulGen L _ _ _ _ t (LB.invGen L φ' ε' t')) (𝟙 Y) r
    rw [Category.comp_id] at e1
    rw [← e1, val_of _ r w J (fun k => J (r ≫ 𝟙 Y ≫ Sum.elim φ φ' k)) (fun _ => rfl),
      ← hc _ (fun k₁ k₂ e => by simp only [e])]
    exact gm_res r w le_top (hJ.mem _ r) c
  have hz1 : ∀ w : Z, gm z w ⊤ c = 1 := by
    intro w
    obtain ⟨J, hJ, -⟩ := exists_good (Z := Z) L hL w (K := PEmpty) PEmpty.elim PEmpty.elim
      (fun a => a.elim) (fun a => a.elim)
    have e1 := val_pull hJ t z (𝟙 Z)
    have e2 := val_pull hJ t' z (𝟙 Z)
    rw [Category.id_comp] at e1 e2
    rw [← key Z z w J hJ, val_mul hJ, val_inv, ← e1, ← e2, val_corr hJ H, mul_inv_cancel]
  obtain ⟨d, hd⟩ := hp c.val
  have d1 : d = 1 := fn_ext fun w _ => by
    have e' : gm (𝟙 Z ≫ z) w ⊤ c = 1 := by rw [Category.id_comp]; exact hz1 w
    have e'' := (gs_pull (𝟙 Z ≫ z) p w ⊤ trivial d).symm.trans ((congrArg (gs (𝟙 Z ≫ z) w ⊤) hd).trans
      ((gs_unit _ w ⊤ trivial c).trans (congrArg Units.val e')))
    rw [Category.assoc, hzp, Category.comp_id] at e''
    rw [e'', gs_eq _ w ⊤ trivial, map_one, map_one, Units.val_one]
  have c1 : c = 1 := Units.ext (by rw [← hd, d1, map_one]; rfl)
  refine corr_of_val hL fun y J hJ => ?_
  have e := key Y (𝟙 Y) y J hJ
  rw [c1, map_one, val_mul hJ, val_inv, mul_inv_eq_one] at e
  exact e

theorem exists_linearisation : ∀ (T X : Scheme.{0}) (π : X ⟶ T) (e : T ⟶ X), e ≫ π = 𝟙 T → Function.Surjective π.appTop.hom → ∀ (L : LB X), L.IsLB → (∃ r : LB.Gen (L.pull e), r.IsGen) → ∀ (Ga : Type) [Group Ga] (ρ : Ga → (X ⟶ X)) (θ : Ga → (T ⟶ T)), (∀ a c, ρ (a * c) = ρ a ≫ ρ c) → (∀ a c, θ (a * c) = θ a ≫ θ c) → (∀ a, e ≫ ρ a = θ a ≫ e) → (∀ a, LBIso L (L.pull (ρ a))) → ∃ u : ∀ a, LB.Gen (LB.LinComb L (K := Fin 2) ![𝟙 X, ρ a] ![1, -1]), (∀ a, (u a).IsGen) ∧ ∀ a c, LB.Gen.Corr L _ _ _ _ (u (a * c)) (LB.mulGen L _ _ _ _ (u a) (LB.pullGen L _ _ (u c) (ρ a))) := by
  intro T X π e he hπ L hL ⟨r, hr⟩ Ga _ ρ θ hρ hθ heρ hiso
  have hex : ∀ a, ∃ u : LB.Gen (LB.LinComb L (K := Fin 2) ![𝟙 X, ρ a] ![1, -1]), u.IsGen ∧
      LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ u e)
        (LB.mulGen L _ _ _ _ r (LB.invGen L _ _ (LB.pullGen L _ _ r (θ a)))) := by
    intro a
    obtain ⟨w, hw⟩ := exists_gen_diff hL (ρ a) (hiso a)
    refine DVR.exists_normalized_to hL _ _ w hw π e he _ _ _
      (DVR.mulGen_isGen_of_isGen r hr _ (DVR.invGen_isGen_of_isGen _ (DVR.pullGen_isGen_of_isGen _ _ r hr _))) ?_
    rw [DVR.fsum_sumElim]
    simp [DVR.fsum, Fin.sum_univ_two, heρ a]
  choose u hu hue using hex
  refine ⟨u, hu, fun a c => ?_⟩
  refine corr_of_pull_section hL (hu _) (DVR.mulGen_isGen_of_isGen _ (hu a) _ (DVR.pullGen_isGen_of_isGen _ _ _ (hu c) _))
    ?_ π e he hπ ?_
  · rw [DVR.fsum_sumElim]
    simp only [DVR.fsum, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Category.comp_id, hρ]
    rw [add_assoc, ← add_assoc (Finsupp.single (ρ a) (-1 : ℤ)), ← Finsupp.single_add, neg_add_cancel, Finsupp.single_zero,
      zero_add]
  · refine corr_of_val hL fun y J hJ => ?_
    have v1 := val_corr hJ (hue (a * c)) (𝟙 T)
    have v2 := val_corr hJ (hue a) (𝟙 T)
    have v3 := val_corr hJ (hue c) (θ a)
    simp only [val_mul hJ, val_inv, val_pull hJ, Category.id_comp, Category.assoc, hθ] at v1 v2 v3 ⊢
    rw [heρ a, v1, v2, v3, _root_.mul_assoc, inv_mul_cancel_left]

end GlobalTheory.MumLin
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem secIsMul_cancel : ∀ (R : Type) [CommRing R] [IsDomain R] (X : Scheme.{0}) (p : X ⟶ Spec (CommRingCat.of R)), Flat p → ∀ (L : LB X) (q : R), q ≠ 0 → ∀ s t t' : LB.Sec L, ReciprocityTheory.ChartRestriction.G.DVR.SecIsMul p q s t → ReciprocityTheory.ChartRestriction.G.DVR.SecIsMul p q s t' → t = t' := by
  intro R _ _ X p hp L q hq s t t' h h'
  haveI := hp
  have key : ∀ j, t.f j = t'.f j := by
    intro j
    refine fn_ext fun x hx => ?_
    have e1 := GlobalTheory.secIsMul_gs h (𝟙 X) x j hx
    have e2 := GlobalTheory.secIsMul_gs h' (𝟙 X) x j hx
    rw [Category.id_comp] at e1 e2
    have h0 : cst p x q * (gs (𝟙 X) x (L.U j) (t.f j) - gs (𝟙 X) x (L.U j) (t'.f j)) = 0 := by
      rw [mul_sub, ← e1, ← e2, sub_self]
    obtain ⟨u, hu⟩ := GlobalTheory.cst_dvd_of_cst_mul_eq_zero p x (a := q) (b := 0)
      (fun c hc => by
        rcases mul_eq_zero.1 hc with h1 | h1
        · exact absurd h1 hq
        · rw [h1]) h0
    have hz : cst p x (0 : R) = 0 := by
      rw [cst, map_zero, gs_eq _ _ ⊤ trivial, map_zero, map_zero]
    rw [hz, zero_mul, sub_eq_zero] at hu
    exact hu
  cases t; cases t'
  congr 1
  exact funext key

end GlobalTheory.Mum
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.UnifPull

open GlobalTheory.UT GlobalTheory.ArcPull GlobalTheory.PullLinear

theorem g_eq_of_isPullDeg {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {φ : R →+* R'}
    {D : DegPre R} {D' : DegPre R'} (hD : IsPullDeg φ D D') : D'.P.g = D.P.g :=
  H1.dim_unique _ D'.P.smoothDim
    ((smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback (pull_grp hD).1 D.P.smoothDim)
    (eSec D'.P.A (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum R'))

theorem exists_pull_of_deg : ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (I : Ideal R) (I' : Ideal R'),
    AdmBase R I → AdmBase R' I' → ∀ (φ : R →+* R'), Function.Injective φ → I.map φ ≤ I' →
    ∀ (D : DegData R I) (D' : DegData R' I') (hD : IsPullDeg φ D.toPre D'.toPre)
      (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G],
      IsSemiAbelian G → ∀ (U : Unif I D A G),
      ∃ (A' : PolAV (Spec (CommRingCat.of (FractionRing R')))) (U' : Unif I' D' A' ((Over.pullback (specOf φ)).obj G)),
        IsPullUnif φ hD (Iso.refl _) U U' := by
  intro R R' _ _ _ _ I I' hR hR' g hg hI D D' hD A G _ _ hG U
  have sq : spMap (fracMap hg) ≫ jK R = jK R' ≫ spMap g := (fracMap_sq hg).symm.trans (Category.id_comp _)
  obtain ⟨A', gA, pA, dA, mA, tA⟩ := GlobalTheory.abelianSchemeLaws_all.1.polBaseChange _ _ (spMap (fracMap hg)) A
  have gpA : IsGrpPullback A'.A A.A (spMap (fracMap hg)) gA := ⟨pA, fun T x y x₀ y₀ hx hy => by
    have e₁ : x₀ = Out.toBase pA.w x := Over.OverMorphism.ext hx
    have e₂ : y₀ = Out.toBase pA.w y := Over.OverMorphism.ext hy
    rw [e₁, e₂, ← mA]; rfl⟩
  have gpG := ThetaBaseChange.grp_generic U.toUnifPre
  have gp' : IsGrpPullback ((Over.pullback (jK R')).obj ((Over.pullback (specOf g)).obj G)) G (spMap (fracMap hg) ≫ jK R)
      (pullback.fst ((Over.pullback (specOf g)).obj G).hom (jK R') ≫ pullback.fst G.hom (spMap g)) :=
    ((isGrpPullback_pullback ((Over.pullback (specOf g)).obj G) (jK R')).comp (isGrpPullback_pullback G (spMap g))).congr sq.symm rfl
  obtain ⟨eA, mE, heA⟩ := grpPullback_iso gp' (gpA.comp gpG)
  have hgi : U.gen.inv.left ≫ U.gen.hom.left = 𝟙 _ := by
    rw [← Over.comp_left, Iso.inv_hom_id, Over.id_left]
  have hbc : (Iso.refl ((Over.pullback (specOf g)).obj G)).hom.left ≫ pullback.fst G.hom (specOf g) = pullback.fst G.hom (spMap g) :=
    Category.id_comp _
  have wA : LBIso (A'.L.pull eA.hom.left) (U.LG.L.pull (pullback.fst ((Over.pullback (specOf g)).obj G).hom (jK R') ≫
      (Iso.refl ((Over.pullback (specOf g)).obj G)).hom.left ≫ pullback.fst G.hom (specOf g))) := by
    refine LBIso.trans (pull_isLB A'.isLB _) (pull_isLB (pull_isLB A.isLB gA) eA.hom.left)
      (pull_isLB U.LG.isLB _)
      ((LBIso.symm tA).chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull A'.L _ _ rfl) (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull (A.L.pull gA) _ _ rfl)) ?_
    refine LBIso.chartPull (h := eA.hom.left ≫ gA ≫ U.gen.inv.left)
      (chartPullLinComb A.L gA (fun _ => eA.hom.left) (fun _ => U.gen.hom.left) _ _ fun _ => ?_)
      (chartPullSame U.LG.L _ (fun _ => pullback.fst G.hom (jK R)) _ _ fun _ => ?_) U.ext
    · rw [Category.assoc, Category.assoc, hgi, Category.comp_id]
    · rw [hbc, ← heA]; simp only [Category.assoc]
  have he : eSec ((Over.pullback (specOf g)).obj G) ≫ (Iso.refl ((Over.pullback (specOf g)).obj G)).hom.left ≫ pullback.fst G.hom (specOf g) = specOf g ≫ eSec G := by
    rw [hbc]; exact (cubeMapOf (isGrpPullback_pullback G (spMap g))).e_comm
  have hr : (rigPullOf (G := G) (G' := (Over.pullback (specOf g)).obj G) _ (specOf g) he U.LG.L U.LG.rig).IsGen :=
    LBxP.isGen_pullAlong U.LG.L _ (specOf g) (fun _ : PUnit => eSec G) (fun _ => 1) (fun _ => eSec ((Over.pullback (specOf g)).obj G))
      (fun _ => he) U.LG.rig U.LG.rigGen
  let L' : RigLB ((Over.pullback (specOf g)).obj G) := ⟨U.LG.L.pull ((Iso.refl ((Over.pullback (specOf g)).obj G)).hom.left ≫ pullback.fst G.hom (specOf g)),
    rigPullOf (G := G) (G' := (Over.pullback (specOf g)).obj G) _ (specOf g) he U.LG.L U.LG.rig, pull_isLB U.LG.isLB _, hr⟩
  have mR : IsMonHom (Iso.refl ((Over.pullback (specOf g)).obj G)).hom := by show IsMonHom (𝟙 _); infer_instance
  obtain ⟨U', -, -, hPU⟩ := GlobalTheory.TorsionFormCompare.exists_unif_pull_of_deg
    GlobalTheory.abelianSchemeLaws_all.1.polBaseChange GlobalTheory.abelianSchemeLaws_all.1.globalFns
    GlobalTheory.abelianSchemeLaws_all.1.secBaseChange GlobalTheory.twistBaseChange
    R R' I I' hR hR' g hI D A G hG U D' hD (g_eq_of_isPullDeg hD) ((Over.pullback (specOf g)).obj G)
    (Iso.refl _) mR A' dA eA mE wA L' (idIso _) he (idIso_isGen L'.isLB) (fun p => hr p.1 p.2)
  exact ⟨A', U', hPU⟩

end GlobalTheory.Mum.UnifPull

end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.DegPullId

theorem exists_isPullDeg_id_self : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R), AdmBase R I → ∀ (D : DegData R I),
    ∃ h : IsPullDeg (RingHom.id R) D.toPre D.toPre, (∀ x, h.xe x = x) ∧
      h.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf (RingHom.id R)) = 𝟙 _ := by
  intro R _ _ I hR D
  have hgen {F : D.toPre.P.A.left ⟶ D.toPre.P.A.left} (hF : F = 𝟙 _) : PGen (isoPullId (Geo.Tor.idIso D.toPre.P.L) hF) := by
    subst F
    intro Y f y j j' k k' hj hj' hk hk'
    have hgw : ∀ a b, f y ∈ D.toPre.P.L.U a → f y ∈ D.toPre.P.L.U b →
        gw (isoPullId (Geo.Tor.idIso D.toPre.P.L) rfl) f y a b =
          gm f y _ (D.toPre.P.L.g a b) := by
      intro a b ha hb
      have hm : f y ∈ (D.toPre.P.L.pull (𝟙 _)).U (fun _ => a) ⊓ D.toPre.P.L.U b := ⟨mem_pull.2 ha, hb⟩
      exact gm_res f y _ hm _
    rw [hgw j k hj hk, hgw j' k' hj' hk', Category.comp_id]
    have hV : f y ∈ (D.toPre.P.L.U j ⊓ D.toPre.P.L.U k) ⊓ (D.toPre.P.L.U j' ⊓ D.toPre.P.L.U k') := ⟨⟨hj, hk⟩, ⟨hj', hk'⟩⟩
    have hw' : res (inf_le_left : (D.toPre.P.L.U j ⊓ D.toPre.P.L.U k) ⊓ (D.toPre.P.L.U j' ⊓ D.toPre.P.L.U k') ≤ D.toPre.P.L.U j ⊓ D.toPre.P.L.U k) (D.toPre.P.L.g j k) =
      res (le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left) :
        (D.toPre.P.L.U j ⊓ D.toPre.P.L.U k) ⊓ (D.toPre.P.L.U j' ⊓ D.toPre.P.L.U k') ≤ D.toPre.P.L.U j ⊓ D.toPre.P.L.U j') (D.toPre.P.L.g j j') *
      (res (le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right) :
        (D.toPre.P.L.U j ⊓ D.toPre.P.L.U k) ⊓ (D.toPre.P.L.U j' ⊓ D.toPre.P.L.U k') ≤ D.toPre.P.L.U k ⊓ D.toPre.P.L.U k') (D.toPre.P.L.g k k'))⁻¹ *
      res (inf_le_right : (D.toPre.P.L.U j ⊓ D.toPre.P.L.U k) ⊓ (D.toPre.P.L.U j' ⊓ D.toPre.P.L.U k') ≤ D.toPre.P.L.U j' ⊓ D.toPre.P.L.U k') (D.toPre.P.L.g j' k') :=
      (idIso_isGen D.toPre.P.isLB) (j, k) (j', k')
    have key := congrArg (gm f y ((D.toPre.P.L.U j ⊓ D.toPre.P.L.U k) ⊓ (D.toPre.P.L.U j' ⊓ D.toPre.P.L.U k'))) hw'
    simp only [map_mul, map_inv, gm_res f y _ hV] at key
    exact key
  have : IsMonHom (Iso.refl D.toPre.P.A).hom := inferInstanceAs (IsMonHom (𝟙 D.toPre.P.A))
  have gp : IsGrpPullback D.toPre.P.A D.toPre.P.A (specOf (RingHom.id R)) (Iso.refl D.toPre.P.A).hom.left :=
    (isGrpPullback_of_iso (Iso.refl D.toPre.P.A)).congr (specOf_id R).symm rfl
  obtain ⟨e, me, hF⟩ := grpPullback_iso gp (isGrpPullback_pullback D.toPre.P.A (specOf (RingHom.id R)))
  have hF' : e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf (RingHom.id R)) = 𝟙 _ := hF
  obtain ⟨W, hW, ⟨ψW⟩⟩ := psiOnExists R I hR D
  obtain ⟨hD, h₁, -, h₃⟩ := UnifUniq.exists_isPullDeg_id D.toPre D.toPre W hW ψW e me
    (isoPullId (Geo.Tor.idIso D.toPre.P.L) hF') ((isGen_iff _).2 (hgen hF'))
    ((congrArg (_ ≫ ·) hF').trans (Category.comp_id _))
    (NoTorus.pmaps_id hF' (K := PUnit) (fun _ => eSec D.toPre.P.A) (fun _ => 1) D.toPre.rig_gen) (AddEquiv.refl _)
    (fun x => (congrArg (_ ≫ ·) hF').trans (Category.comp_id _))
    (fun x => NoTorus.pmaps_id hF' (K := PUnit) (fun _ => D.toPre.xK x) (fun _ => -1) (D.toPre.psi_gen x))
  refine ⟨hD, fun x => ?_, ?_⟩
  · rw [h₃]; rfl
  · rw [h₁]; exact hF'

end GlobalTheory.DegPullId
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.MumPull

theorem specOf_genericPoint {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (ρ : R →+* R')
    (hρ : Function.Injective ρ) :
    (specOf ρ).base (genericPoint (Spec (CommRingCat.of R'))) = genericPoint (Spec (CommRingCat.of R)) := by
  rw [genericPoint_eq_bot_of_affine, genericPoint_eq_bot_of_affine]
  apply PrimeSpectrum.ext
  show Ideal.comap ρ ⊥ = ⊥
  exact Ideal.comap_bot_of_injective ρ hρ

theorem exists_pull : ∀ (R R' : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), Function.Injective ρ → IsLocalHom ρ → ∀ D : DegData R (maximalIdeal R), ∃ D' : DegData R' (maximalIdeal R'), Nonempty (IsPullDeg ρ D.toPre D'.toPre) := by
  intro R R' _ _ _ _ _ _ ρ hρ hloc D
  obtain ⟨L, -⟩ := GlobalTheory.T.all_six_abelian_scheme_laws_hold
  obtain ⟨W, hW, hψ⟩ := GlobalTheory.PsiSpread.exists_psiOn D.toPre D.tau_bimult
  have hη : (specOf ρ).base (genericPoint (Spec (CommRingCat.of R'))) ∈ W := by
    rw [specOf_genericPoint ρ hρ]; exact hW
  have hI : (maximalIdeal R).map ρ ≤ maximalIdeal R' :=
    ((IsLocalRing.local_hom_tfae ρ).out 1 3).1 hloc
  obtain ⟨D', hD, -, -⟩ := GlobalTheory.exists_degData_isPullDeg L.polBaseChange L.globalFns R R' (maximalIdeal R)
    (maximalIdeal R') ρ hI D W hψ hη
  exact ⟨D', ⟨hD⟩⟩

end GlobalTheory.MumPull
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem exists_nhds_nonzero_of_isClosedMap :
    ∀ (Z Y : Scheme.{0}) (p : Z ⟶ Y), IsClosedMap p.base → ∀ (L : LB Z) (V : Y.Opens) (u : LB.Sec (L.pull (p ⁻¹ᵁ V).ι)) (y : Y), y ∈ V → (∀ z : (p ⁻¹ᵁ V).toScheme, p ((p ⁻¹ᵁ V).ι z) = y → z ∈ nonzeroLocus u) → ∃ V₁ : Y.Opens, y ∈ V₁ ∧ V₁ ≤ V ∧ ∀ z : (p ⁻¹ᵁ V).toScheme, p ((p ⁻¹ᵁ V).ι z) ∈ V₁ → z ∈ nonzeroLocus u := by
  intro Z Y p hp L V u y hy h
  have hO : IsOpen ((p ⁻¹ᵁ V).ι '' (nonzeroLocus u : Set (p ⁻¹ᵁ V).toScheme)) :=
    (p ⁻¹ᵁ V).ι.isOpenEmbedding.isOpenMap _ (nonzeroLocus u).isOpen
  have hC : IsClosed (p.base '' ((p ⁻¹ᵁ V).ι '' (nonzeroLocus u : Set (p ⁻¹ᵁ V).toScheme))ᶜ) :=
    hp _ hO.isClosed_compl
  refine ⟨V ⊓ ⟨_, hC.isOpen_compl⟩, ⟨hy, ?_⟩, inf_le_left, ?_⟩
  · rintro ⟨c, hc, hcy⟩
    have hcV : c ∈ p ⁻¹ᵁ V := by
      change p c ∈ V
      have : p c = y := hcy
      rw [this]; exact hy
    exact hc ⟨⟨c, hcV⟩, h ⟨c, hcV⟩ hcy, rfl⟩
  · intro z hz
    have h2 : (p ⁻¹ᵁ V).ι z ∈ (p ⁻¹ᵁ V).ι '' (nonzeroLocus u : Set (p ⁻¹ᵁ V).toScheme) := by
      by_contra hn
      exact hz.2 ⟨_, hn, rfl⟩
    obtain ⟨w, hw, hwz⟩ := h2
    have : w = z := (p ⁻¹ᵁ V).ι.isOpenEmbedding.injective hwz
    subst this
    exact hw

end GlobalTheory.Mum
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.GenRestrict

theorem exists_gen_restrict : ∀ (Z : Scheme.{0}) (L : LB Z), L.IsLB → ∀ (O O' : Z.Opens), O ≤ O' →
    ∀ u : LB.Sec (L.pull O'.ι), (∀ z : O'.toScheme, O'.ι z ∈ O → z ∈ nonzeroLocus u) →
    ∃ t : LB.Gen (L.pull O.ι), t.IsGen := by
  intro Z L _ O O' hle u hu
  have e : ∀ _k : PUnit, Z.homOfLE hle ≫ (fun _ : PUnit => O'.ι) _k = (fun _ : PUnit => O.ι) _k :=
    fun _ => Scheme.homOfLE_ι Z hle
  let v : LB.Sec (L.pull O.ι) := PullbackSections.pullSecLC L _ _ _ (Z.homOfLE hle) e u
  refine GlobalTheory.LocusPull.exists_gen_of_nonzeroLocus_eq_top v (top_unique fun z _ => ?_)
  have heq : O'.ι (Z.homOfLE hle z) = O.ι z := by
    exact congrArg (fun f : O.toScheme ⟶ Z => f z) (Scheme.homOfLE_ι Z hle)
  have hz : O'.ι (Z.homOfLE hle z) ∈ O := by
    rw [heq]
    exact (Scheme.Opens.ι_apply O z).symm ▸ z.2
  obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 (hu _ hz)
  refine TopologicalSpace.Opens.mem_iSup.2 ⟨k, ?_⟩
  show z ∈ O.toScheme.basicOpen ((Scheme.Hom.appLE (Z.homOfLE hle) _ _ _).hom (u.f k))
  rw [Scheme.basicOpen_appLE]
  refine ⟨?_, hk⟩
  have h1 : Z.homOfLE hle z ∈ (L.pull O'.ι).U k := Scheme.basicOpen_le _ _ hk
  refine mem_pull.2 ?_
  rw [← heq]
  exact mem_pull.1 h1

end GlobalTheory.GenRestrict
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.Recog

variable {R : Type} [CommRing R] [IsDomain R]

structure GoodLab (D : DegPre R) (A : PolAV (Sp (FractionRing R))) (F : Type) [Field F] [Algebra (FractionRing R) F]
    (f : ∀ k : ℕ, QkPt D F k → (TFK (R := R) F ⟶ A.A)) : Prop where
  pow : ∀ k, 1 ≤ k → ∀ p, f k p ^ k = 1
  onto : ∀ k, 1 ≤ k → ∀ x : TFK (R := R) F ⟶ A.A, x ^ k = 1 → ∃ p, f k p = x
  eqv : ∀ k, 1 ≤ k → ∀ p p', f k p = f k p' ↔ QkPt.Equiv D F p p'
  add : ∀ k, 1 ≤ k → ∀ p p' p'', QkAdd p p' p'' → f k p'' = f k p * f k p'
  weil : ∀ k, 1 ≤ k → ∀ p p' (z : Fˣ), WeilQkIs D F k p p' z → WeilIs A.A A.L k (f k p) (f k p') (unitOn z)
  level : ∀ k m N, 1 ≤ k → 1 ≤ m → N = k * m → ∀ (p : QkPt D F k) (q : QkPt D F N), q.y = m • p.y → q.g = p.g →
    f N q = f k p

def Lies {W : Type} [CommRing W] [IsDomain W] (φ : R →+* W) {D : DegPre R} {D' : DegPre W} (hD : IsPullDeg φ D D')
    {F F' : Type} [Field F] [Field F'] [Algebra (FractionRing R) F] [Algebra (FractionRing R) F']
    [Algebra (FractionRing W) F'] (em : F →+* F') {k : ℕ} (p : QkPt D F k) (p' : QkPt D' F' k) : Prop :=
  ∃ p₁ : QkPt D F' k, QkExt em p p₁ ∧ p'.y = hD.xe.symm p₁.y ∧ IsPullGtF φ hD F' p₁.g p'.g

theorem exists_goodLab [CharZero R] {I : Ideal R} (hR : AdmBase R I) {D : DegData R I} {A : PolAV (Sp (FractionRing R))}
    {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] (hG : IsSemiAbelian G) (U : Unif I D A G) (F : Type) [Field F]
    [IsAlgClosed F] [Algebra (FractionRing R) F] :
    ∃ f, GoodLab D.toPre A F f ∧ ∀ k, 1 ≤ k → ∀ p x, QkToAkU U.toUnifPre F k p x ↔ x = f k p := by
  have H : ∀ k : ℕ, ∃ f : QkPt D.toPre F k → (TFK (R := R) F ⟶ A.A), 1 ≤ k →
      GlobalTheory.UT.Tors U.toUnifPre F k f ∧ ∀ p, f p ^ k = 1 := fun k => by
    by_cases hk : 1 ≤ k
    · obtain ⟨f, hf⟩ := GlobalTheory.TorsionIso.torsion_clause R _ hR D A G hG U F k hk
      exact ⟨f, fun _ => hf⟩
    · exact ⟨fun _ => 1, fun h => absurd h hk⟩
  choose f hf using H
  refine ⟨f, ⟨fun k hk => (hf k hk).2, fun k hk => (hf k hk).1.2.1, fun k hk => (hf k hk).1.2.2.1,
    fun k hk => (hf k hk).1.2.2.2.1, fun k hk p p' z => ((hf k hk).1.2.2.2.2 p p' z).1, ?_⟩, fun k hk => (hf k hk).1.1⟩
  intro k m N hk hm hN p q hy hg
  have hN1 : 1 ≤ N := hN ▸ Nat.mul_pos hk hm
  exact (((hf N hN1).1.1 q _).1 (((GlobalTheory.LevelCompat.qkToAkU_level GlobalTheory.firstFiveLaws R _ hR D A G hG U F k m N hk hm hN p q
    (f k p)).1 hy hg).1 (((hf k hk).1.1 p _).2 rfl))).symm

end GlobalTheory.Mum.Recog
end
end

end

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_degenerationData_pullback_injective_localHom : ∀ (R R' : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), Function.Injective ρ → IsLocalHom ρ → ∀ D : DegData R (maximalIdeal R), ∃ D' : DegData R' (maximalIdeal R'), Nonempty (IsPullDeg ρ D.toPre D'.toPre) := by
  first | exact @GlobalTheory.MumPull.exists_pull | exact GlobalTheory.MumPull.exists_pull | (intros; apply GlobalTheory.MumPull.exists_pull <;> assumption)

end
end

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_pullDeg_identity_self_admissible : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R), AdmBase R I → ∀ (D : DegData R I),
    ∃ h : IsPullDeg (RingHom.id R) D.toPre D.toPre, (∀ x, h.xe x = x) ∧
      h.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf (RingHom.id R)) = 𝟙 _ := by
  first | exact @GlobalTheory.DegPullId.exists_isPullDeg_id_self | exact GlobalTheory.DegPullId.exists_isPullDeg_id_self | (intros; apply GlobalTheory.DegPullId.exists_isPullDeg_id_self <;> assumption)

end
end

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_uniformisation_pullback_to_pullDeg : ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (I : Ideal R) (I' : Ideal R'),
    AdmBase R I → AdmBase R' I' → ∀ (φ : R →+* R'), Function.Injective φ → I.map φ ≤ I' →
    ∀ (D : DegData R I) (D' : DegData R' I') (hD : IsPullDeg φ D.toPre D'.toPre)
      (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G],
      IsSemiAbelian G → ∀ (U : Unif I D A G),
      ∃ (A' : PolAV (Spec (CommRingCat.of (FractionRing R')))) (U' : Unif I' D' A' ((Over.pullback (specOf φ)).obj G)),
        IsPullUnif φ hD (Iso.refl _) U U' := by
  first | exact @GlobalTheory.Mum.UnifPull.exists_pull_of_deg | exact GlobalTheory.Mum.UnifPull.exists_pull_of_deg | (intros; apply GlobalTheory.Mum.UnifPull.exists_pull_of_deg <;> assumption)

end
end

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_generator_on_smaller_open_of_nonvanishing_section : ∀ (Z : Scheme.{0}) (L : LB Z), L.IsLB → ∀ (O O' : Z.Opens), O ≤ O' → ∀ u : LB.Sec (L.pull O'.ι), (∀ z : O'.toScheme, O'.ι z ∈ O → z ∈ nonzeroLocus u) → ∃ t : LB.Gen (L.pull O.ι), t.IsGen := by
  first | exact @GlobalTheory.GenRestrict.exists_gen_restrict | exact GlobalTheory.GenRestrict.exists_gen_restrict | (intros; apply GlobalTheory.GenRestrict.exists_gen_restrict <;> assumption)

end
end

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_nhds_subset_nonzeroLocus_of_isClosedMap : ∀ (Z Y : Scheme.{0}) (p : Z ⟶ Y), IsClosedMap p.base → ∀ (L : LB Z) (V : Y.Opens) (u : LB.Sec (L.pull (p ⁻¹ᵁ V).ι)) (y : Y), y ∈ V → (∀ z : (p ⁻¹ᵁ V).toScheme, p ((p ⁻¹ᵁ V).ι z) = y → z ∈ nonzeroLocus u) → ∃ V₁ : Y.Opens, y ∈ V₁ ∧ V₁ ≤ V ∧ ∀ z : (p ⁻¹ᵁ V).toScheme, p ((p ⁻¹ᵁ V).ι z) ∈ V₁ → z ∈ nonzeroLocus u := by
  first | exact @GlobalTheory.Mum.exists_nhds_nonzero_of_isClosedMap | exact GlobalTheory.Mum.exists_nhds_nonzero_of_isClosedMap | (intros; apply GlobalTheory.Mum.exists_nhds_nonzero_of_isClosedMap <;> assumption)

end
end
