module

public import Development.AbelianVarietyTheory.Definitions.Uniformization.SvalTwistOne
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsRatioPoints
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle017
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle076
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle015
public import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle077
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle042
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
import Mathlib.GroupTheory.IndexNSmul
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PullUUnitsCompatGeneric

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory.UU.ShiftExp

theorem sval_secScale {X Y Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (c : Γ(Y, ⊤)) (s : LB.Sec (LB.LinComb L φ ε)) (r : Z ⟶ Y) (z : Z) {J : (Z ⟶ X) → L.ι} (hJ : Good L z J) :
    sval (DVR.SecOps.secScale c s) r z J = gs r z ⊤ c * sval s r z J :=
  (gs_mul r z _ (hJ.mem _ r) _ _).trans (congrArg₂ (· * ·) (gs_res r z le_top (hJ.mem _ r) _) rfl)

theorem gs_scal {Y Z : Scheme.{0}} {R : Type} [CommRing R] (p : Y ⟶ Spec (CommRingCat.of R)) (r : Z ⟶ Y) (z : Z)
    (c : R) : gs r z ⊤ (scal p c) = gs (𝟙 _) z ⊤ (scal (r ≫ p) c) := by
  calc gs r z ⊤ (scal p c) = gs (𝟙 _ ≫ r) z ⊤ (scal p c) := by rw [Category.id_comp]
    _ = gs (𝟙 _) z (r ⁻¹ᵁ ⊤) ((r.app ⊤).hom (scal p c)) := (gs_pull (𝟙 _) r z ⊤ (by trivial) _).symm
    _ = gs (𝟙 _) z ⊤ (scal (r ≫ p) c) := rfl

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]

theorem shift (hG : GlobalFnsSt) (U : PreU I D A G) {W : Type} [CommRing W] [Algebra R W]
    (a : Multiplicative D.X →* Wˣ) (x : TA R W ⟶ G) (hx : U.TorPt a x) (e : ℕ) (Z : Scheme.{0})
    (y y' : Z ⟶ (thickObj R I e G).left) (rG : Z ⟶ (TA R W ⊗ G).left)
    (h₁ : rG ≫ (snd _ G).left = y ≫ (fstG I e G).left)
    (h₂ : y' ≫ (fstG I e G).left = rG ≫ (translPt G x).left) :
    y' ≫ (U.gt e).pG.left = y ≫ (U.gt e).pG.left ∧ ∀ (χ : D.X) (z : Z) (J), Good D.P.L z J →
      (val ((U.gt e).t χ) y' z J).val =
        gs (𝟙 Z) z ⊤ (scal (R := W) (rG ≫ (fst (TA R W) G).left) (a (Multiplicative.ofAdd χ)).val) *
          (val ((U.gt e).t χ) y z J).val := by
  let T : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) := Over.mk (y ≫ (thickObj R I e G).hom)
  let yo : T ⟶ thickObj R I e G := Over.homMk y rfl
  have hb : rG ≫ (TA R W ⊗ G).hom = T.hom ≫ thick R I e := by
    rw [← Over.w (snd (TA R W) G), ← Category.assoc, h₁, Category.assoc, Over.w (fstG I e G)]
    exact (Category.assoc _ _ _).symm
  let ro : Over.mk (T.hom ≫ thick R I e) ⟶ TA R W ⊗ G := Over.homMk rG hb
  let x₀ : Over.mk (T.hom ≫ thick R I e) ⟶ G := ro ≫ fst _ _ ≫ x
  let xe : T ⟶ thickObj R I e G :=
    Over.homMk (pullback.lift x₀.left T.hom (Over.w x₀)) (pullback.lift_snd _ _ _)
  have hxe : xe.left ≫ pullback.fst G.hom (thick R I e) = x₀.left := pullback.lift_fst _ _ _
  have hm := (isGrpPullback_pullback G (thick R I e)).2 T xe yo x₀ (ro ≫ snd _ _) hxe.symm h₁
  have ht : ro ≫ translPt G x = x₀ * (ro ≫ snd _ _) := MonObj.comp_mul ro (fst _ _ ≫ x) (snd _ _)
  have hf : y' ≫ pullback.fst G.hom (thick R I e) = (xe * yo).left ≫ pullback.fst G.hom (thick R I e) :=
    h₂.trans ((congrArg (fun q => q.left) ht).trans hm)
  haveI : Mono (thick R I e) := by
    haveI : IsClosedImmersion (thick R I e) := IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
    infer_instance
  have hy : y' = (xe * yo).left := (cancel_mono (pullback.fst G.hom (thick R I e))).1 hf
  obtain ⟨p₁, p₂⟩ := hx e Z (rG ≫ (fst (TA R W) G).left) xe.left (hxe.trans (Category.assoc _ _ _).symm)
  have hone : GlobalTheory.TorusCoord.im (U.gt e) xe = 1 := by
    have : (ro ≫ fst _ _) ≫ (1 : TA R W ⟶ D.P.A) = 1 := MonObj.comp_one _
    exact (Over.OverMorphism.ext p₁).trans this
  subst hy
  refine ⟨?_, fun χ z J hJ => ?_⟩
  · have := GlobalTheory.TorusCoord.im_mul (U.gt e) xe yo
    rw [hone, _root_.one_mul] at this
    exact congrArg (fun q => q.left) this
  · have k := GlobalTheory.TorusCoord.val_t_mul_points (U.gt e) hG χ xe yo z J hJ
    have c : GlobalTheory.TorusCoord.cubeVal (U.gt e) χ z J xe yo = 1 := by
      unfold GlobalTheory.TorusCoord.cubeVal
      rw [hone]
      exact (isCub_cubV D.cub (T := (Over.map (thick R I e)).obj T) hJ).face₂ _ _
    rw [c, _root_.mul_one] at k
    exact (congrArg Units.val k).trans ((Units.val_mul _ _).trans (congrArg (· * _) (p₂ χ z J hJ)))

end GlobalTheory.UU.ShiftExp

theorem GlobalTheory.UU.expansion_translate_torus : GlobalFnsSt → ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegPre R) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : PreU I D A G) (W : Type) [CommRing W] [Algebra R W] (a : Multiplicative D.X →* Wˣ) (x : TA R W ⟶ G), U.TorPt a x → ∀ (k : ℕ) (σ : U.SecGT (TA R W) k) (f : ∀ α, SecBT D (TA R W) k α), U.ExpT (TA R W) k σ f → ∀ e : ℕ, ∃ s : Finset D.X, ∀ (Z : Scheme.{0}) (y y' : Z ⟶ (thickObj R I e G).left) (rG : Z ⟶ (TA R W ⊗ G).left) (rB : Z ⟶ (TA R W ⊗ D.P.A).left), rG ≫ (snd _ G).left = y ≫ (fstG I e G).left → rB ≫ (snd _ D.P.A).left = y ≫ (U.gt e).pG.left → rB ≫ (fst _ D.P.A).left = rG ≫ (fst _ G).left → y' ≫ (fstG I e G).left = rG ≫ (translPt G x).left → ∀ (z : Z) (JG) (J), Good U.P.L.L z JG → Good D.P.L z J → (∀ α ∉ s, sval (twist a f α) rB z J = 0) ∧ (U.wv e y' z JG J).val ^ k * sval σ (rG ≫ (translT G x).left) z JG = ∑ α ∈ s, sval (twist a f α) rB z J * (val ((U.gt e).t α) y z J).val := by
  intro hG R _ _ I D A G _ _ U W _ _ a x hx k σ f hf e
  obtain ⟨s, hs⟩ := hf e
  refine ⟨s, fun Z y y' rG rB h₁ h₂ h₃ h₄ z JG J hJG hJ => ?_⟩
  obtain ⟨p₁, p₂⟩ := ShiftExp.shift hG U a x hx e Z y y' rG h₁ h₄
  have e₁ : (translT G x).left ≫ (snd (TA R W) G).left = (translPt G x).left :=
    congrArg (fun q => q.left) (lift_snd (fst (TA R W) G) (translPt G x))
  have e₂ : (translT G x).left ≫ (fst (TA R W) G).left = (fst (TA R W) G).left :=
    congrArg (fun q => q.left) (lift_fst (fst (TA R W) G) (translPt G x))
  obtain ⟨q₁, q₂⟩ := hs Z y' (rG ≫ (translT G x).left) rB (by rw [Category.assoc, e₁, h₄]) (h₂.trans p₁.symm)
    (by rw [Category.assoc, e₂, h₃]) z JG J hJG hJ
  have tw : ∀ α, sval (twist a f α) rB z J =
      gs (𝟙 Z) z ⊤ (scal (R := W) (rG ≫ (fst (TA R W) G).left) (a (Multiplicative.ofAdd α)).val) *
        sval (f α) rB z J := fun α => by
    rw [← h₃]
    exact (ShiftExp.sval_secScale _ _ rB z hJ).trans (congrArg (· * _) (ShiftExp.gs_scal _ rB z _))
  refine ⟨fun α hα => by rw [tw, q₁ α hα, mul_zero], q₂.trans (Finset.sum_congr rfl fun α _ => ?_)⟩
  rw [tw, p₂ α z J hJ]
  ring
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory.NullExp

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegPre R) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : PreU I D A G) (T : Over (Spec (CommRingCat.of R))) (k : ℕ) (σ : U.SecGT T k) (f : ∀ α, SecBT D T k α), U.ExpT T k σ f → NullFam I f := by
  intro R _ _ I D A G _ _ U T k σ f H e
  obtain ⟨s, hs⟩ := H e
  refine ⟨s, fun α hα Z r hr z J hJ => ?_⟩
  refine GlobalTheory.LiftTest.main R I D e G (U.gt e) (T ⊗ D.P.A) (snd T D.P.A) _ D.P.L D.P.isLB _ _ _ (f α)
    ?_ Z r hr z J hJ
  intro Z x r hx z J hJ
  have hc : (r ≫ (fst T D.P.A).left) ≫ T.hom = (x ≫ (fstG I e G).left) ≫ G.hom := by
    rw [Category.assoc, Category.assoc, Over.w (fst T D.P.A), Over.w (fstG I e G), ← Over.w (snd T D.P.A),
      ← Category.assoc, hx, Category.assoc, Over.w (U.gt e).pG]
  let rG : Z ⟶ (T ⊗ G).left := pullback.lift (r ≫ (fst T D.P.A).left) (x ≫ (fstG I e G).left) hc
  choose JG hJG using fun χ : Z ⟶ G.left => exists_chart U.P.L.isLB (χ z)
  exact (hs Z x rG r (pullback.lift_snd _ _ _) hx (pullback.lift_fst _ _ _).symm z JG J hJG hJ).1 α hα

end GlobalTheory.NullExp
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

noncomputable section

namespace GlobalTheory.UU.TorPtEx

theorem exists_gtPt {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (T : Over (Spec (CommRingCat.of R)))
    (a : Multiplicative D.X →* Γ(T.left, ⊤)ˣ) : ∃ g : GtPt D T, g.b = 1 ∧
      ∀ (χ : D.X) (Z : Scheme.{0}) (r : Z ⟶ T.left) (z : Z) (J), Good D.P.L z J →
        val (g.s χ) r z J = gm r z ⊤ (a (Multiplicative.ofAdd χ)) := by
  have h1 : (LB.oneGen D.P.L (Y := T.left)).IsGen := fun _ _ =>
    (map_one _).trans ((congrArg₂ (· * ·) (Fintype.prod_empty _) (map_one _)).trans (_root_.mul_one _)).symm
  have key : ∀ χ : D.X, ∃ t : LB.Gen (LB.LinComb D.P.L (DegPre.gtφT D T 1 χ) DegPre.gtε), t.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ T.left) (z : Z) (J), Good D.P.L z J →
        val t r z J = gm r z ⊤ (a (Multiplicative.ofAdd χ)) := by
    intro χ
    obtain ⟨t, ht, hv⟩ := exists_gen D.P.isLB (φ' := DegPre.gtφT D T 1 χ) (ε' := DegPre.gtε) (fun U _ h => by
        have e₁ : padd D.P.A (DegPre.cT D T χ) 1 = DegPre.cT D T χ := _root_.mul_one (DegPre.cT D T χ)
        have e₂ : DegPre.zeroT D T = 1 := rfl
        simp [DegPre.gtφT, DegPre.gtε, Fin.prod_univ_succ, e₁, e₂])
      (DVR.scaleGen (a (Multiplicative.ofAdd χ)) (LB.oneGen D.P.L)) (DVR.scaleGen_isGen _ _ h1)
    refine ⟨t, ht, fun Z r z J hJ => (hv Z r z J hJ).trans ?_⟩
    exact ((map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res r z le_top (hJ.mem PEmpty.elim r) _) (val_one r))).trans
      (_root_.mul_one _)
  choose s hs hv using key
  refine ⟨⟨1, s, hs, corr_of_val D.P.isLB fun y J hJ => ?_, fun χ χ' => corr_of_val D.P.isLB fun y J hJ => ?_⟩, rfl, hv⟩
  · rw [hv 0 _ _ y J hJ, val_one, ofAdd_zero, map_one, map_one]
  · have c := (val_cub D.cub (𝟙 T) hJ (DegPre.cT D T χ) (DegPre.cT D T χ') 1).trans
      ((congrArg (cubV D.cub y J _ _) (Category.id_comp (1 : T ⟶ D.P.A))).trans ((isCub_cubV D.cub hJ).face₃ _ _))
    refine ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (hv _ _ _ y J hJ) c)).trans
      (Eq.trans ?_ ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (hv _ _ _ y J hJ) (hv _ _ _ y J hJ))).symm)
    rw [_root_.mul_one, ofAdd_add, map_mul, map_mul]; rfl

theorem main : AllPre fun {V} _ _ _ {D} {_} {G} _ _ U => ∀ (W : Type) [CommRing W] [IsLocalRing W] [Algebra V W], FinExt V W → ∀ a : Multiplicative D.X →* Wˣ, ∃ x : TA V W ⟶ G, U.TorPt a x := by
  intro V _ _ _ hV D A G _ _ U W _ _ _ hW a
  obtain ⟨g, hb, hv⟩ := exists_gtPt D (TA V W)
    ((Units.map (Scheme.ΓSpecIso (CommRingCat.of W)).inv.hom.toMonoidHom).comp a)
  obtain ⟨x, hx, -⟩ := RedOnto.main V hV D A G U W hW g
  refine ⟨x, fun e Z r xe h => ?_⟩
  obtain ⟨h₁, h₂⟩ := hx e Z r xe h
  refine ⟨hb ▸ h₁, fun χ z J hJ => ?_⟩
  rw [h₂ χ z J hJ, hv χ Z r z J hJ, gm_val r z ⊤ trivial, gs_eq _ z ⊤ trivial]
  rfl

end GlobalTheory.UU.TorPtEx

end
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

noncomputable section
namespace GlobalTheory.UT
open GlobalTheory.TorusExt

attribute [local instance] gtGroup

theorem card_qk_eq_mul {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F]
    [Algebra (FractionRing R) F] (hB : D.TauBimult) {k : ℕ} (hk : k ≠ 0)
    (hd : ∀ y : D.X, ∃ g : GtPtF D F, k • g = iota hB F y) :
    Nat.card (Quot (QkPt.Equiv D F (k := k))) = k ^ D.rank * Nat.card {g : GtPtF D F // k • g = 0} := by
  choose r hr using hd
  let K : AddSubgroup D.X := (nsmulAddMonoidHom k : D.X →+ D.X).range
  have hK : Nat.card (D.X ⧸ K) = k ^ D.rank := AddSubgroup.index_range_nsmul D.X k
  let f : (D.X ⧸ K) × {g : GtPtF D F // k • g = 0} → Quot (QkPt.Equiv D F (k := k)) := fun x =>
    Quot.mk _ (qkMk hB x.1.out (r x.1.out + x.2.1) (by rw [nsmul_add, hr, x.2.2, add_zero]))
  rw [← hK, ← Nat.card_prod]
  refine (Nat.card_congr (Equiv.ofBijective f ⟨?_, ?_⟩)).symm
  · rintro ⟨c, t⟩ ⟨c', t'⟩ h
    obtain ⟨z, hy, hg⟩ := (equiv_iff hB _ _).1 ((equiv_equivalence hB).eqvGen_iff.1 (Quot.eqvGen_exact h))
    simp only [qkMk_y, qkMk_g] at hy hg
    obtain rfl : c = c' := by
      rw [← QuotientAddGroup.out_eq' c, ← QuotientAddGroup.out_eq' c', QuotientAddGroup.eq]
      exact ⟨z, by rw [hy, neg_add_cancel_left]; rfl⟩
    have hz : z = 0 := by
      have h0 : (k : ℤ) • z = 0 := by rw [natCast_zsmul]; exact left_eq_add.1 hy
      exact (smul_eq_zero.1 h0).resolve_left (by exact_mod_cast hk)
    rw [hz, map_zero, add_zero, add_right_inj] at hg
    exact Prod.ext rfl (Subtype.ext hg.symm)
  · rintro ⟨p⟩
    obtain ⟨z, hz⟩ : -p.y + (QuotientAddGroup.mk p.y : D.X ⧸ K).out ∈ K := by
      rw [← QuotientAddGroup.eq, QuotientAddGroup.out_eq']
    have hy : (QuotientAddGroup.mk p.y : D.X ⧸ K).out = p.y + k • z := by
      rw [show k • z = _ from hz, add_neg_cancel_left]
    refine ⟨⟨QuotientAddGroup.mk p.y, p.g + iota hB F z - r (QuotientAddGroup.mk p.y : D.X ⧸ K).out, ?_⟩,
      (Quot.sound ((equiv_iff hB _ _).2 ⟨z, hy, ?_⟩)).symm⟩
    · rw [nsmul_sub, hr, hy, nsmul_add, qk_nsmul hB, map_add (f := _), map_nsmul, sub_self]
    · exact add_sub_cancel _ _

theorem card_qk : LL → AllD fun {R} _ _ {I} D F _ _ => ∀ (k : ℕ), 1 ≤ k → Nat.card (Quot (QkPt.Equiv D.toPre F (k := k))) = k ^ (2 * (D.toPre.rank + D.toPre.P.g)) := by
  intro hL R _ _ _ I hA D F _ _ _ k hk
  have : IsNoetherianRing R := hA.1
  have : CharZero F := charZero_of_injective_algebraMap (algebraMap (FractionRing R) F).injective
  have h₁ := (GlobalTheory.GtCount.card_gtTors hL.1 hL.2.1 R D.toPre F k (Nat.cast_ne_zero.2 (by omega))).1
  simp only [GlobalTheory.GtCount.gtTors_iff] at h₁
  have h₂ := (gt_onto_divisible_kernel hL R I hA D F).2.1 k hk
  rw [card_qk_eq_mul D.tau_bimult (by omega) fun y => (h₂ _).imp fun _ e => ((isNsmul_iff_eq _ _ _).1 e).symm, h₁,
    ← pow_add]
  congr 1
  ring

end GlobalTheory.UT
end
end
