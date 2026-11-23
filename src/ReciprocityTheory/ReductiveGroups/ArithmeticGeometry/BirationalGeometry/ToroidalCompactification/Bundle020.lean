module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsGenVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle014
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
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle019
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigIsoCongr
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle018
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DualMapSCompScaleS
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi
open scoped CategoryTheory.Obj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
variable {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}



theorem ArcWit.witMove (h5 : Out.Laws5) (hQ : QkPullExistsSt) {Y : Model Xo c β} {O' : Type} [CommRing O']
    [IsDomain O'] {b : O →+* O'} {a : ArcIn D l β O' b} {R : Type} [CommRing R] [IsDomain R] {I : Ideal R}
    (hR : Out.AdmBase R I) {f : O' →+* R} {u : R} {χ : Sp R ⟶ Y.X} (W : ArcWit Y a I f u χ) {G'' : Over (Sp R)}
    [GrpObj G''] [IsCommMonObj G''] {D'' : Out.DegData R I} [Module (𝓞 E) D''.toPre.X]
    {A'' : Out.PolAV (Sp (FractionRing R))} (U'' : Out.Unif I D'' A'' G'')
    (oD'' : letI := H.starRing; D''.toPre.OAct (𝓞 E))
    (bc : G'' ≅ (Over.pullback (Out.specOf (RingHom.id R))).obj W.t.G) [IsMonHom bc.hom]
    (hD : Out.IsPullDeg (RingHom.id R) W.P.D.toPre D''.toPre) (hPU : Out.IsPullUnif (RingHom.id R) hD bc W.P.U U'')
    (xl : ∀ (x : 𝓞 E) y, hD.xe (x • y) = x • hD.xe y)
    (el : letI := H.starRing; ∀ x, oD''.onB.act x ≫ hD.e.hom =
      hD.e.hom ≫ (Over.pullback (Out.specOf (RingHom.id R))).map (W.P.oD.onB.act x)) :
    letI := H.starRing
    ∃ (he'' : eSec D''.toPre.P.A ≫ (hD.e.hom.left ≫ pullback.fst W.P.D.toPre.P.A.hom (Out.specOf (RingHom.id R))) ≫
        W.φ = spMap f ≫ eSec a.D₀.P.A)
      (w'' : LB.Iso D''.toPre.P.L (a.D₀.P.L.pull
        ((hD.e.hom.left ≫ pullback.fst W.P.D.toPre.P.A.hom (Out.specOf (RingHom.id R))) ≫ W.φ)))
      (e'' : a.D₀.X ≃ₗ[𝓞 E] D''.toPre.X),
      (∀ y, hD.xe (e'' y) = W.e y) ∧ Tri W.w hD.w w'' ∧
      IsGrpPullback D''.toPre.P.A a.D₀.P.A (spMap f)
        ((hD.e.hom.left ≫ pullback.fst W.P.D.toPre.P.A.hom (Out.specOf (RingHom.id R))) ≫ W.φ) ∧ w''.IsGen ∧
      LB.Gen.Maps (LB.linCombIso w'' (K := PUnit) (fun _ => eSec D''.toPre.P.A) (fun _ => 1)) D''.toPre.rig
        (rigPullOf ((hD.e.hom.left ≫ pullback.fst W.P.D.toPre.P.A.hom (Out.specOf (RingHom.id R))) ≫ W.φ)
          (spMap f) he'' a.D₀.P.L a.D₀.rig) ∧
      (∀ x, (oD''.onB.act x).left ≫
          (hD.e.hom.left ≫ pullback.fst W.P.D.toPre.P.A.hom (Out.specOf (RingHom.id R))) ≫ W.φ =
        ((hD.e.hom.left ≫ pullback.fst W.P.D.toPre.P.A.hom (Out.specOf (RingHom.id R))) ≫ W.φ) ≫
          (a.oa.onB.act x).left) ∧
      (∀ y, (D''.toPre.c (e'' y)).left ≫
          (hD.e.hom.left ≫ pullback.fst W.P.D.toPre.P.A.hom (Out.specOf (RingHom.id R))) ≫ W.φ =
        spMap f ≫ (a.D₀.c y).left) ∧
      ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] [Algebra (FractionRing O') F] (uF : F),
        (∀ x, algebraMap (FractionRing O') F (algebraMap O' _ x) =
          algebraMap (FractionRing R) F (algebraMap R _ (f x))) →
        uF = algebraMap (FractionRing R) F (algebraMap R _ u) →
        (∀ y, GenRel w'' (LB.pullGen _ _ _ (D''.toPre.psi (e'' y)) (Out.jFK (R := R) F))
          (LB.pullGen _ _ _ (a.D₀.psi y) (Out.jFK (R := O') F)) (uF ^ (a.be y y / 2))) ∧
        ∀ (yF : Sp F ⟶ Xo.XF c), yF ≫ Y.j = Out.jFK (R := R) F ≫ Out.jK R ≫ χ →
          ∀ (k : ℕ) (p₀ : Out.QkPt a.D₀ (FractionRing O') k) (σ : 𝟙_ (Over (Xo.XF c)) ⟶ Y.oF.t.G),
            ((k = l.A ∧ ∃ v, HEq p₀ (a.etaA v) ∧ σ = Y.oF.etaA v) ∨
              (k = l.M ∧ ∃ v ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La),
                HEq p₀ (a.eta v) ∧ σ = Y.oF.eta v)) →
            ∀ (q₀ : Out.QkPt a.D₀ F k) (q : Out.QkPt D''.toPre F k) (x : Out.TFK (R := R) F ⟶ A''.A),
              QkExt (algebraMap _ F) p₀ q₀ → q.y = e'' q₀.y →
              (∀ z, GenRel w'' (q.g.s (e'' z)) (q₀.g.s z) (uF ^ (a.be q₀.y z / k))) →
              x.left ≫ U''.gen.inv.left ≫ pullback.fst G''.hom (Out.jK R) ≫ bc.hom.left ≫
                pullback.fst W.t.G.hom (Out.specOf (RingHom.id R)) ≫ W.m.φ = yF ≫ σ.left ≫ Y.m.φ →
              Out.QkToAkU U''.toUnifPre F k q x := by
  letI := H.starRing
  have hs := specOf_id R
  obtain ⟨s1, s2, s3, s4, s5, s6⟩ := W.spec
  set Φ := hD.e.hom.left ≫ pullback.fst W.P.D.toPre.P.A.hom (Out.specOf (RingHom.id R)) with hΦ
  have gD := (isGen_iff hD.w).1 hD.w_gen
  have g0 := (isGen_iff W.w).1 s2
  obtain ⟨w', T⟩ := exists_comp W.P.D.toPre.P.isLB W.w hD.w g0 gD a.D₀.P.isLB D''.toPre.P.isLB
  let xe' : D''.toPre.X ≃ₗ[𝓞 E] W.P.D.toPre.X := { hD.xe with map_smul' := xl }
  have := hD.e_hom
  have gpB : IsGrpPullback D''.toPre.P.A W.P.D.toPre.P.A (spMap (RingHom.id R)) Φ :=
    ((isGrpPullback_of_iso hD.e).comp (isGrpPullback_pullback W.P.D.toPre.P.A (Out.specOf (RingHom.id R)))).congr
      (Category.id_comp _) rfl
  have hxe : ∀ y, hD.xe (xe'.symm (W.e y)) = W.e y := fun y => xe'.apply_symm_apply _
  have hsf : spMap (RingHom.id R) ≫ spMap f = spMap f := by
    simp [spMap]
  have he' : eSec D''.toPre.P.A ≫ Φ ≫ W.φ = spMap f ≫ eSec a.D₀.P.A := by
    rw [← Category.assoc, hD.he, Category.assoc, W.he, ← Category.assoc, hsf]
  refine ⟨he', w', W.e.trans xe'.symm, hxe, T, (gpB.comp s1).congr hsf rfl,
    (isGen_iff w').2 (T.pgen_comp W.P.D.toPre.P.isLB g0 gD), ?_, fun x => ?_, fun y => ?_,
    fun F _ _ _ _ uF ha hu => ?_⟩
  · have r₀ := (maps_iff W.w _ (fun _ => eSec a.D₀.P.A) _ W.P.D.toPre.rig a.D₀.rig (spMap f) _
      (rigPull_le W.φ (spMap f) W.he a.D₀.P.L) (fun _ => rfl)).1 s3
    have r₁ := (maps_iff hD.w _ (fun _ => eSec W.P.D.toPre.P.A) _ D''.toPre.rig W.P.D.toPre.rig
      (Out.specOf (RingHom.id R)) _ (rigPull_le Φ (Out.specOf (RingHom.id R)) hD.he W.P.D.toPre.P.L) (fun _ => rfl)).1
      hD.w_rig
    have r₂ := T.pmaps_comp W.P.D.toPre.P.isLB (fun _ => hD.he) r₀ r₁
    rw [hsf] at r₂
    exact (maps_iff w' _ (fun _ => eSec a.D₀.P.A) _ D''.toPre.rig a.D₀.rig (spMap f) _
      (rigPull_le (Φ ≫ W.φ) (spMap f) he' a.D₀.P.L) (fun _ => rfl)).2 r₂
  · have e₁ : (oD''.onB.act x).left ≫ Φ = Φ ≫ (W.P.oD.onB.act x).left := by
      have e₀ := congrArg (fun z => z.left ≫ pullback.fst W.P.D.toPre.P.A.hom (Out.specOf (RingHom.id R))) (el x)
      have e₂ : ((Over.pullback (Out.specOf (RingHom.id R))).map (W.P.oD.onB.act x)).left ≫
          pullback.fst W.P.D.toPre.P.A.hom (Out.specOf (RingHom.id R)) = pullback.fst _ _ ≫ (W.P.oD.onB.act x).left :=
        pullback.lift_fst _ _ _
      simp only [Over.comp_left, Category.assoc, e₂] at e₀
      simpa only [hΦ, Category.assoc] using e₀
    show (oD''.onB.act x).left ≫ Φ ≫ W.φ = (Φ ≫ W.φ) ≫ (a.oa.onB.act x).left
    rw [← Category.assoc, e₁, Category.assoc, s4 x, Category.assoc]; rfl
  · show (D''.toPre.c (xe'.symm (W.e y))).left ≫ Φ ≫ W.φ = spMap f ≫ (a.D₀.c y).left
    rw [← Category.assoc, hD.c_pr, hxe, Category.assoc, s5 y, ← Category.assoc, hsf]
  · have hF : ∀ r : R, algebraMap (FractionRing R) F (algebraMap R (FractionRing R) r) =
        algebraMap (FractionRing R) F (algebraMap R (FractionRing R) ((RingHom.id R) r)) := fun _ => rfl
    have hj : Out.jFK (R := R) F ≫ Out.jK R ≫ spMap (RingHom.id R) = Out.jFK (R := R) F ≫ Out.jK R := by
      simp [spMap]
    obtain ⟨k₁, k₂⟩ := s6 F uF ha hu
    refine ⟨fun y => ?_, fun yF hyF k p₀ σ hσ q₀ q' x' e1 e2 e3 e4 => ?_⟩
    · have pm := pmaps_psi hD F hj (xe'.symm (W.e y))
      have k := k₁ y
      rw [← hxe y] at k
      refine (genRel_transfer T W.P.D.toPre.P.isLB D''.toPre.P.isLB (fun _ => ?_) pm _ _).1 k
      have hx : D''.toPre.xK (xe'.symm (W.e y)) ≫ Φ =
          Out.jK R ≫ Out.specOf (RingHom.id R) ≫ (W.P.D.toPre.c (hD.xe (xe'.symm (W.e y)))).left := by
        rw [← hD.c_pr, ← Category.assoc]; rfl
      rw [Category.id_comp, Category.assoc, hx, ← Category.assoc (Out.jK R), ← Category.assoc]
      exact (congrArg (· ≫ _) hj).trans (Category.assoc _ _ _)
    · obtain ⟨q, hq₁, hq₂⟩ := hQ R R (RingHom.id R) W.P.D.toPre D''.toPre hD F hF k q'
      have a1 : bc.hom.left ≫ pullback.snd W.t.G.hom (Out.specOf (RingHom.id R)) = G''.hom := Over.w bc.hom
      have a2 : U''.gen.inv.left ≫ pullback.snd G''.hom (Out.jK R) = A''.A.hom := Over.w U''.gen.inv
      have a3 : x'.left ≫ A''.A.hom = Out.jFK (R := R) F := Over.w x'
      have hcomm : (x'.left ≫ U''.gen.inv.left ≫ pullback.fst G''.hom (Out.jK R) ≫ bc.hom.left ≫
          pullback.fst W.t.G.hom (Out.specOf (RingHom.id R))) ≫ W.t.G.hom = Out.jFK (R := R) F ≫ Out.jK R := by
        simp only [Category.assoc, pullback.condition, pullback.condition_assoc, reassoc_of% a1, reassoc_of% a2,
          reassoc_of% a3]
        simp [Out.specOf]
      let z : Out.TFK (R := R) F ⟶ (Over.pullback (Out.jK R)).obj W.t.G :=
        Over.homMk (pullback.lift _ (Out.jFK (R := R) F) hcomm) (pullback.lift_snd _ _ _)
      let x : Out.TFK (R := R) F ⟶ W.P.A.A := z ≫ W.P.U.gen.hom
      have hx : x'.left ≫ U''.gen.inv.left ≫ pullback.fst G''.hom (Out.jK R) ≫ bc.hom.left ≫
          pullback.fst W.t.G.hom (Out.specOf (RingHom.id R)) =
          x.left ≫ W.P.U.gen.inv.left ≫ pullback.fst W.t.G.hom (Out.jK R) := by
        have hgi : W.P.U.gen.hom.left ≫ W.P.U.gen.inv.left = 𝟙 _ := by
          rw [← Over.comp_left, Iso.hom_inv_id, Over.id_left]
        show _ = (z.left ≫ W.P.U.gen.hom.left) ≫ _
        rw [Category.assoc, ← Category.assoc W.P.U.gen.hom.left, hgi, Category.id_comp]
        exact (pullback.lift_fst _ _ _).symm
      have hk : 1 ≤ k := by
        rcases hσ with ⟨rfl, -⟩ | ⟨rfl, -⟩
        · exact l.A_pos
        · exact le_trans (by norm_num) l.three_le
      refine h5.qkBaseChange R R I I hR hR (RingHom.id R) W.P.D W.P.A W.t.G W.P.U G'' bc inferInstance A'' D'' hD U''
        hPU F hF k hk q x q' x' hq₁ hq₂ hx (k₂ yF hyF k p₀ σ hσ q₀ q x e1 ?_ (fun z => ?_) ?_)
      · have : hD.xe q'.y = q.y := by rw [hq₁, AddEquiv.apply_symm_apply]
        rw [← this, e2]; exact hxe _
      · obtain ⟨hψ', hm⟩ := hq₂.2 (xe'.symm (W.e z))
        have pm := (maps_iff hD.w _ _ _ (q'.g.s (xe'.symm (W.e z))) (q.g.s (hD.xe (xe'.symm (W.e z)))) (𝟙 _) _
          (Out.GeneratorPullback.pullAlong_le _ _ _ _ _ hψ') (fun _ => rfl)).1 hm
        have k' := (genRel_transfer T W.P.D.toPre.P.isLB D''.toPre.P.isLB hψ' pm _ _).2 (e3 z)
        rw [hxe z] at k'
        exact k'
      · rw [← e4]
        simpa only [Category.assoc] using congrArg (· ≫ W.m.φ) hx.symm

end ReciprocityTheory.ChartRestriction.G.Geo.Tor
end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj

namespace ReciprocityTheory.ChartRestriction.G.Chart

attribute [local instance] Over.cartesianMonoidalCategory

theorem ofId_ext {S : Type} [CommRing S] {B : Type} [CommRing B] [Algebra S B] (f g : S →ₐ[S] B) : f = g := Subsingleton.elim f g

theorem exists_away_not_mem {S : Type} [CommRing S] {n : ℕ} (s : Fin n → S) (hs : Ideal.span (Set.range s) = ⊤)
    (p : Ideal S) [p.IsPrime] : ∃ k, s k ∉ p := by
  by_contra hne
  push_neg at hne
  have hle : Ideal.span (Set.range s) ≤ p := by
    rw [Ideal.span_le]
    rintro _ ⟨k, rfl⟩
    exact hne k
  rw [hs, top_le_iff] at hle
  exact Ideal.IsPrime.ne_top ‹p.IsPrime› hle

variable {S : Type} [CommRing S] {G : Over (Spec (CommRingCat.of S))} [GrpObj G] [∀ s : S, Smooth (Gs G s).hom]

section Prime

variable (p : Ideal S) [p.IsPrime]

@[instance_reducible]
def awayAtPrime (t : S) (ht : t ∉ p) : Algebra (Localization.Away t) (Localization.AtPrime p) :=
  IsLocalization.localizationAlgebraOfSubmonoidLe _ _ (Submonoid.powers t) p.primeCompl
    ((Submonoid.powers_le (P := p.primeCompl)).mpr ht)

theorem tan_prime_lift {y' : sp (R₀ := S) (DualNumber (Localization.AtPrime p)) ⟶ G} (hy' : TanS y') :
    ∃ q ∈ p.primeCompl, ∃ w : sp (R₀ := S) (DualNumber S) ⟶ G, TanS w ∧
      spMap (dualMapS (Algebra.ofId S (Localization.AtPrime p))) ≫ w =
        spMap (scaleS (S := S) (algebraMap S (Localization.AtPrime p) q)) ≫ y' := by
  obtain ⟨n, s, hs, hC⟩ := exists_cover G
  have C : ∀ k, Chart (Gs G (s k)) := fun k => (hC k).some
  obtain ⟨k0, hk0⟩ := exists_away_not_mem s hs p
  have hle : Submonoid.powers (s k0) ≤ p.primeCompl := (Submonoid.powers_le (P := p.primeCompl)).mpr hk0
  let _ := awayAtPrime p (s k0) hk0
  have : IsScalarTower S (Localization.Away (s k0)) (Localization.AtPrime p) :=
    IsLocalization.localization_isScalarTower_of_submonoid_le _ _ (Submonoid.powers (s k0)) p.primeCompl hle
  have : Algebra.FinitePresentation (Localization.Away (s k0)) Γ((Gs G (s k0)).left, (C k0).U) := fp_chart (C k0)
  let M := p.primeCompl.map (algebraMap S (Localization.Away (s k0)))
  have hM : IsLocalization (Algebra.algebraMapSubmonoid (Localization.Away (s k0)) M) (Localization.AtPrime p) := by
    have e : Algebra.algebraMapSubmonoid (Localization.Away (s k0)) M = M := by
      rw [Algebra.algebraMapSubmonoid, Algebra.algebraMap_self]
      ext x
      simp
    rw [e]
    exact IsLocalization.isLocalization_of_submonoid_le _ _ (Submonoid.powers (s k0)) p.primeCompl hle
  obtain ⟨_, ⟨q, hq, rfl⟩, y₀, hy₀, he⟩ := tanS_lift (C k0) (A := Localization.Away (s k0)) M hy'
  obtain ⟨N, w, hw, hwr⟩ := tan_extend s hs C k0 hy₀
  refine ⟨s k0 ^ N * q, p.primeCompl.mul_mem (p.primeCompl.pow_mem hk0 N) hq, w, hw, ?_⟩
  rw [show Algebra.ofId S (Localization.AtPrime p) =
      (IsScalarTower.toAlgHom S (Localization.Away (s k0)) (Localization.AtPrime p)).comp
        (Algebra.ofId S (Localization.Away (s k0))) from ofId_ext _ _, ← res_res, hwr, res_scale, he, scale_scale,
    map_pow, AlgHom.commutes, ← IsScalarTower.algebraMap_apply, map_mul, map_pow]

theorem tan_prime_uniq {w : sp (R₀ := S) (DualNumber S) ⟶ G} (hw : TanS w)
    (h1 : spMap (dualMapS (Algebra.ofId S (Localization.AtPrime p))) ≫ w = 1) :
    ∃ q ∈ p.primeCompl, spMap (scaleS (S := S) q) ≫ w = 1 := by
  classical
  obtain ⟨n, s, hs, hC⟩ := exists_cover G
  have C : ∀ k, Chart (Gs G (s k)) := fun k => (hC k).some
  obtain ⟨k0, hk0⟩ := exists_away_not_mem s hs p
  have hle : Submonoid.powers (s k0) ≤ p.primeCompl := (Submonoid.powers_le (P := p.primeCompl)).mpr hk0
  let _ := awayAtPrime p (s k0) hk0
  have : IsScalarTower S (Localization.Away (s k0)) (Localization.AtPrime p) :=
    IsLocalization.localization_isScalarTower_of_submonoid_le _ _ (Submonoid.powers (s k0)) p.primeCompl hle
  have : Algebra.FinitePresentation (Localization.Away (s k0)) Γ((Gs G (s k0)).left, (C k0).U) := fp_chart (C k0)
  let M := p.primeCompl.map (algebraMap S (Localization.Away (s k0)))
  have hM : IsLocalization (Algebra.algebraMapSubmonoid (Localization.Away (s k0)) M) (Localization.AtPrime p) := by
    have e : Algebra.algebraMapSubmonoid (Localization.Away (s k0)) M = M := by
      rw [Algebra.algebraMapSubmonoid, Algebra.algebraMap_self]
      ext x
      simp
    rw [e]
    exact IsLocalization.isLocalization_of_submonoid_le _ _ (Submonoid.powers (s k0)) p.primeCompl hle
  have hwk : ∀ k, TanS (spMap (dualMapS (Algebra.ofId S (Localization.Away (s k)))) ≫ w) :=
    fun k => tanS_restrict _ hw
  have hone : ∀ (A : Type) [CommRing A] [Algebra S A], TanS (1 : sp (R₀ := S) (DualNumber A) ⟶ G) :=
    fun A _ _ => comp_one' _
  obtain ⟨_, ⟨q₀, hq₀, rfl⟩, hc0⟩ := tanS_uniq (C k0) (A := Localization.Away (s k0))
    (A' := Localization.AtPrime p) M (hwk k0) (hone _) (by
      rw [res_res, comp_one', show (IsScalarTower.toAlgHom S (Localization.Away (s k0)) (Localization.AtPrime p)).comp
        (Algebra.ofId S (Localization.Away (s k0))) = Algebra.ofId S (Localization.AtPrime p) from ofId_ext _ _, h1])
  rw [comp_one'] at hc0
  have h2 : ∀ k, ∃ N : ℕ, spMap (scaleS (S := S) (algebraMap S (Localization.Away (s k)) (s k0) ^ N)) ≫
      spMap (scaleS (S := S) (algebraMap S (Localization.Away (s k)) q₀)) ≫
        spMap (dualMapS (Algebra.ofId S (Localization.Away (s k)))) ≫ w =
      spMap (scaleS (S := S) (algebraMap S (Localization.Away (s k)) (s k0) ^ N)) ≫ 1 := by
    intro k
    apply tanS_away_uniq (C k) (A := Localization.Away (s k)) (s k0) (tanS_scale _ (hwk k)) (hone _)
    rw [comp_one', res_scale, res_res, AlgHom.commutes,
      show (qL (s k) (s k0)).comp (Algebra.ofId S (Localization.Away (s k))) =
        (qR (s k) (s k0)).comp (Algebra.ofId S (Localization.Away (s k0))) from ofId_ext _ _,
      ← res_res, show algebraMap S (Qv (s k) (s k0)) q₀ = qR (s k) (s k0) (algebraMap S (Localization.Away (s k0)) q₀)
        from ((qR (s k) (s k0)).commutes q₀).symm, ← res_scale]
    rw [show algebraMap (Localization.Away (s k0)) (Localization.Away (s k0)) (algebraMap S (Localization.Away (s k0)) q₀) =
      algebraMap S (Localization.Away (s k0)) q₀ from rfl] at hc0
    rw [hc0, comp_one']
  choose N hN using h2
  let N₂ := Finset.univ.sup N
  refine ⟨s k0 ^ N₂ * q₀, p.primeCompl.mul_mem (p.primeCompl.pow_mem hk0 N₂) hq₀, ?_⟩
  refine tan_ext_cover s hs fun k => ?_
  rw [comp_one', res_scale, Algebra.ofId_apply, map_mul, map_pow, ← scale_scale,
    scale_pow_mono _ (Finset.le_sup (f := N) (Finset.mem_univ k)) (hN k), comp_one']

end Prime

end ReciprocityTheory.ChartRestriction.G.Chart
end
end

section

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
open scoped Pointwise

theorem good_pt {F : Type} [Field F] {X : Scheme.{0}} {M : LB X} (hM : M.IsLB) (y : Sp F) : ∃ J, Good M y J := by
  choose I hI using fun χ : Sp F ⟶ X => exists_chart hM (χ y)
  exact ⟨I, hI⟩

theorem qkExtExists_g : QkExtExistsSt := by
  intro R _ _ D F F' _ _ _ _ f hf k p
  have hj : spMap f ≫ jFK (R := R) F = jFK (R := R) F' := (spMap_comp _ _).symm.trans (congrArg spMap (RingHom.ext hf))
  let ρ : TF (R := R) F' ⟶ TF (R := R) F := Over.homMk (spMap f) ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) hj))
  obtain ⟨J, hJ⟩ := good_pt D.P.isLB (default : PrimeSpectrum F')
  obtain ⟨q, hy, hb, hv⟩ := exists_qk (F := F') hJ (n := k) p.y (ρ ≫ p.g.b) _ (mult_gx ρ hJ p.g) fun χ =>
    (gx_qk ρ hJ p χ).trans (Ex.ext rfl (congrArg (fun q => val (D.tau p.y χ) q _ J) (hj.trans (Category.id_comp _).symm)))
  refine ⟨q, hy, congrArg (fun q => q.left) hb, fun χ => corr_pt D.P.isLB (fun U _ h => ?_) (q.g.isGen χ)
    (pullGen_isGen _ _ _ _ (p.g.isGen χ) _) hJ ((hv χ).trans ((val_pull hJ _ _ _).trans (by rw [Category.id_comp]; rfl)).symm)⟩
  refine (prod_gt _ χ h).trans (Eq.trans ?_ (prod_gt p.g.b χ fun q => h (ρ.left ≫ q)).symm)
  simp only [← Over.comp_left, MonObj.comp_mul, comp_cP, MonObj.comp_one, hb]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H} {c : Coeff l}
  {k : Type} [Field k] {bF : c.F →+* k} (a : ArcIn D l (RingHom.id c.F) k bF) {F : Type} [Field F] [IsAlgClosed F]
  [Algebra (FractionRing k) F]

theorem exists_level (hG : GlobalFnsSt) {y : (TF (R := k) F).left} {J} (hJ : Good a.D₀.P.L y J) (q : QkPt a.D₀ F l.M)
    (m : 𝓞 E) (hm : m ∈ l.Mb) : letI := H.starRing
    ∃ v ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La), ∃ (q₀ : QkPt a.D₀ F l.M) (z : a.D₀.X),
      QkExt (algebraMap _ F) (a.eta v) q₀ ∧ q₀.y + l.M • z = star m • q.y ∧
      q₀.g.b * cP a.D₀ _ z = q.g.b ≫ a.oa.onB.act (star m) ∧ (q.g.b = 1 → ∀ χ, gx (𝟙 _) hJ q₀.g χ * ix (𝟙 _) hJ z χ =
        ⟨1, val (q.g.s (m • χ)) (𝟙 _) y J⟩) := by
  letI := H.starRing
  have hM0 : 0 < l.M := by have := l.three_le; omega
  let r : c.F := ⟨H.rt0, c.le (IntermediateField.subset_adjoin _ _ (by simp))⟩
  let z : c.F := ⟨zeta l.A, c.le (IntermediateField.subset_adjoin _ _ (by simp))⟩
  obtain ⟨-, I, -, -, hI⟩ := a.geom F r z rfl rfl ((algebraMap (FractionRing k) F).comp (algebraMap k _)) rfl
  obtain ⟨x, hx⟩ := I.onto _ hM0 q
  have hv : star m • x ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La) :=
    Submodule.smul_mem_smul (Ideal.mem_map_of_mem _ hm) Submodule.mem_top
  obtain ⟨q₀, h₀⟩ := qkExtExists_g k a.D₀ _ F (algebraMap _ F) (fun _ => rfl) _ (a.eta (star m • x))
  obtain ⟨q', y', ⟨b', s'⟩, e'⟩ := I.lin _ hM0 (star m) x
  obtain ⟨z₁, y₁, g₁⟩ := gx_equiv (𝟙 _) hJ hx
  obtain ⟨z₂, y₂, g₂⟩ := gx_equiv (𝟙 _) hJ e'
  obtain ⟨z₃, y₃, g₃⟩ := gx_equiv (𝟙 _) hJ (hI _ hv q₀ h₀)
  have := a.oa.onB.hom m
  have := a.oa.onB.hom (star m)
  have hr := a.oa.onB.rosati (star (star m))
  have hbal := a.oa.tau_bal (star (star m))
  rw [star_star (star m)] at hr hbal
  have := a.oa.onB.hom (star (star m))
  obtain ⟨u, hu, u₀⟩ := exists_ros hG a.D₀.P.isAb a.D₀.P.isLB _ _ hr
  have C := isCub_cubV a.D₀.cub (T := TF (R := k) F) hJ
  have cf : ∀ (x : 𝓞 E) χ, cP a.D₀ (TF (R := k) F) (x • χ) = cP a.D₀ _ χ ≫ a.oa.onB.act x := fun x χ => by
    rw [cP, a.oa.c_lin, ← Category.assoc]; rfl
  have ra := ros_add a.D₀.cub hG a.D₀.P.isAb _ _ u hu u₀ (T := TF (R := k) F) hJ
  let Ac : ∀ χ, Ex C (cP a.D₀ _ (star (star m) • χ)) →* Ex C (cP a.D₀ _ χ) := fun χ => MonoidHom.mk'
    (fun p => ⟨p.b ≫ a.oa.onB.act (star m), p.u * val₂ u y J (cP a.D₀ _ χ) p.b⟩) fun p p' =>
      Ex.ext (MonObj.mul_comp _ _ _) (by
        have e := congrArg Additive.ofMul (ra p.b p'.b (cP a.D₀ _ χ)).2
        apply Additive.ofMul.injective
        simp only [Ex.mul_u, Ex.mul_b, cf, ofMul_mul, ofMul_inv] at e ⊢
        linear_combination (norm := abel) e)
  have A₁ : ∀ χ, Ac χ (gx (𝟙 _) hJ (I.ev l.M x).g _) = gx (𝟙 _) hJ q'.g χ := fun χ =>
    Ex.ext (by show (𝟙 _ ≫ _) ≫ _ = 𝟙 _ ≫ _; rw [b', Category.assoc]) (by
      have e := (val_mul hJ _ _ _).symm.trans (val_corr hJ (s' u hu u₀ χ) (𝟙 _))
      rw [val_pull hJ, Category.id_comp] at e
      show _ * val₂ u y J _ (𝟙 _ ≫ _) = _
      rw [Category.id_comp]; exact e)
  have A₂ : ∀ χ w, Ac χ (ix (𝟙 _) hJ w _) = ix (𝟙 _) hJ (star m • w) χ := fun χ w => Ex.ext (cf _ _).symm (by
    let κ : TF (R := k) F ⟶ TK k := Over.homMk (𝟙 _ ≫ jFK (R := k) F) (by rw [Category.id_comp]; rfl)
    have e := (val_mul hJ _ _ _).symm.trans (val_corr hJ (hbal u hu u₀ χ w) κ.left)
    have e' : val (LB.pullGen a.D₀.P.L _ _ u (a.D₀.pt2 χ w)) κ.left y J = val₂ u y J (cP a.D₀ _ χ) (cP a.D₀ _ w) := by
      rw [val_pull hJ, val₂, ← comp_cP a.D₀ κ, ← comp_cP a.D₀ κ w, ← comp_lift]; rfl
    exact (congrArg₂ (· * ·) (tau_symm (𝟙 (TF (R := k) F)) hJ _ _) e'.symm).trans
      (e.trans (tau_symm (𝟙 (TF (R := k) F)) hJ _ _)))
  have key : ∀ χ, gx (𝟙 _) hJ q₀.g χ * ix (𝟙 _) hJ (z₃ - z₂ + star m • z₁) χ = Ac χ (gx (𝟙 _) hJ q.g _) := fun χ => by
    have i := ix_add (𝟙 _) hJ a.bimult (z₃ - z₂) z₂ χ
    rw [sub_add_cancel] at i
    have := (g₃ χ).symm.trans (g₂ χ)
    rw [i, ← _root_.mul_assoc, mul_left_inj] at this
    rw [g₁, map_mul, A₁, A₂, ix_add _ _ a.bimult, ← _root_.mul_assoc, this]
  refine ⟨_, hv, q₀, z₃ - z₂ + star m • z₁, h₀, ?_, ?_, fun hb χ => (key χ).trans (Ex.ext ?_ ?_)⟩
  · rw [y₁, smul_add (star m), ← y', smul_add, smul_sub, smul_comm (star m) l.M]
    linear_combination (norm := abel) y₂ - y₃
  · have := congrArg Ex.b (key 0)
    exact (congrArg (· * _) (Category.id_comp _).symm).trans (this.trans (congrArg (· ≫ _) (Category.id_comp _)))
  · show (𝟙 _ ≫ q.g.b) ≫ _ = 1
    rw [Category.id_comp, hb, MonObj.one_comp]
  · have e := (ra 1 1 (cP a.D₀ _ χ)).2
    rw [_root_.mul_one, MonObj.one_comp (a.oa.onB.act (star m)), C.face₃, C.face₃, _root_.mul_one, _root_.one_mul] at e
    show val (q.g.s (star (star m) • χ)) _ y J * val₂ u y J _ (𝟙 _ ≫ q.g.b) = _
    have e₁ : val₂ u y J (cP a.D₀ _ χ) (𝟙 _ ≫ q.g.b) = 1 := by rw [Category.id_comp, hb, mul_eq_left.1 e.symm]
    rw [e₁, _root_.mul_one, star_star]; rfl

end ReciprocityTheory.ChartRestriction.G.Geo.Tor
end
end
