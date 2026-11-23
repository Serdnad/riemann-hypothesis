module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle029
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.ExistsIsInvariantSectionMemBasicOpenIff
public import Development.AbelianVarietyTheory.Definitions.Divisors.ComparisonMemCechHodgeFiltration
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1005
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
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle007
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.DimSplitPf
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle987
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.DualCon

variable {S : Scheme.{0}}

def addCls (A : Over S) [GrpObj A] (T : Over S) : AddSubgroup (Pic (A ⊗ T).left) where
  carrier := {c | ∀ (Y : Over S) (a a' : Y ⟶ A) (t : Y ⟶ T),
    CechPic.pull (lift (a * a') t).left c = CechPic.pull (lift a t).left c + CechPic.pull (lift a' t).left c}
  add_mem' {c d} hc hd Y a a' t := by
    simp only [map_add (f := _)]
    rw [hc Y a a' t, hd Y a a' t]
    abel
  zero_mem' Y a a' t := by simp only [map_zero, add_zero]
  neg_mem' {c} hc Y a a' t := by
    simp only [map_neg]
    rw [hc Y a a' t]
    abel

variable {A : Over S} [GrpObj A]

theorem fam_iff_mem {T : Over S} {N : LB (A ⊗ T).left} (hN : N.IsLB) : Fam A N ↔ cls N hN ∈ addCls A T :=
  ⟨fun h ↦ (isAdditive_iff hN).1 h.add, fun h ↦ ⟨hN, (isAdditive_iff hN).2 h⟩⟩

def resCls {T' T : Over S} (u : T' ⟶ T) : addCls A T →+ addCls A T' :=
  ((CechPic.pull (lift (fst A T') (snd A T' ≫ u)).left).comp (addCls A T).subtype).codRestrict _
    fun c Y a a' t ↦ by
      simp only [AddMonoidHom.coe_comp, AddSubgroup.coe_subtype, Function.comp_apply, ← CechPic.pull_comp,
        ← Over.comp_left, comp_lift, lift_fst, lift_snd_assoc]
      exact c.2 Y a a' (t ≫ u)


variable (A) in
def famFunctor : (Over S)ᵒᵖ ⥤ CommGrpCat.{1} where
  obj T := CommGrpCat.of (Multiplicative (addCls A T.unop))
  map g := CommGrpCat.ofHom (AddMonoidHom.toMultiplicative (resCls (A := A) g.unop))
  map_id T := by
    refine CommGrpCat.hom_ext (MonoidHom.ext fun c ↦ ?_)
    refine Subtype.ext ?_
    change CechPic.pull (lift (fst A T.unop) (snd A T.unop ≫ 𝟙 _)).left _ = _
    rw [Category.comp_id, lift_fst_snd, Over.id_left, CechPic.pull_id]
    rfl
  map_comp {T T' T''} g g' := by
    refine CommGrpCat.hom_ext (MonoidHom.ext fun c ↦ ?_)
    refine Subtype.ext ?_
    change CechPic.pull (lift (fst A T''.unop) (snd A T''.unop ≫ g'.unop ≫ g.unop)).left _ =
      CechPic.pull (lift (fst A T''.unop) (snd A T''.unop ≫ g'.unop)).left
        (CechPic.pull (lift (fst A T'.unop) (snd A T'.unop ≫ g.unop)).left _)
    rw [← CechPic.pull_comp, ← Over.comp_left, comp_lift, lift_fst, lift_snd_assoc, Category.assoc]

section Rep

variable {B : Over S} {P : LB (A ⊗ B).left} (h : Rep A (toUnit B) P)

include h

def ptCls (T : Over S) (x : T ⟶ B) : addCls A T :=
  ⟨evc h.fam.isLB (fst A T) (snd A T ≫ x), (fam_iff_mem (pull_isLB h.fam.isLB _)).1
    ⟨pull_isLB h.fam.isLB _, fun Y a a' t ↦ by
      refine (cls_eq_iff (pull_isLB (pull_isLB h.fam.isLB _) _)
        (isLB_tens (pull_isLB (pull_isLB h.fam.isLB _) _) (pull_isLB (pull_isLB h.fam.isLB _) _))).1 ?_
      rw [cls_tens (pull_isLB (pull_isLB h.fam.isLB _) _) (pull_isLB (pull_isLB h.fam.isLB _) _)]
      rw [cls_ev (pull_isLB h.fam.isLB _), cls_ev (pull_isLB h.fam.isLB _), cls_ev (pull_isLB h.fam.isLB _)]
      rw [evc_ev h.fam.isLB, evc_ev h.fam.isLB, evc_ev h.fam.isLB]
      simp only [lift_fst, lift_snd_assoc]
      exact (isAdditive_iff h.fam.isLB).1 h.fam.add Y _ _ _⟩⟩

theorem ptCls_bij (T : Over S) : Function.Bijective (ptCls h T) := by
  have hP := h.fam.isLB
  constructor
  · intro x x' e
    have hN : (ev P (fst A T) (snd A T ≫ x)).IsLB := pull_isLB hP _
    have fN : Fam A (ev P (fst A T) (snd A T ≫ x)) := (fam_iff_mem hN).2 (ptCls h T x).2
    refine (h.univ T (toUnit T) _ fN).unique ⟨toUnit_unique _ _, (cls_eq_iff hN hN).1 rfl⟩
      ⟨toUnit_unique _ _, (cls_eq_iff hN (pull_isLB hP _)).1 (congrArg Subtype.val e)⟩
  · intro c
    obtain ⟨N, hN, hc⟩ := cls_surj (c : Pic (A ⊗ T).left)
    have fN : Fam A N := (fam_iff_mem hN).2 (hc ▸ c.2)
    obtain ⟨x, ⟨-, hx⟩, -⟩ := h.univ T (toUnit T) N fN
    exact ⟨x, Subtype.ext (((cls_eq_iff hN (pull_isLB hP _)).2 hx).symm.trans hc)⟩

theorem ptCls_comp {T' T : Over S} (g : T' ⟶ T) (x : T ⟶ B) :
    ptCls h T' (g ≫ x) = resCls g (ptCls h T x) := by
  refine Subtype.ext ?_
  change evc h.fam.isLB (fst A T') (snd A T' ≫ g ≫ x) =
    CechPic.pull (lift (fst A T') (snd A T' ≫ g)).left (evc h.fam.isLB (fst A T) (snd A T ≫ x))
  rw [pull_evc, lift_fst, lift_snd_assoc, Category.assoc]

def famRep : (famFunctor A ⋙ forget CommGrpCat.{1}).RepresentableBy B where
  homEquiv {T} := (Equiv.ofBijective _ (ptCls_bij h T)).trans Multiplicative.ofAdd
  homEquiv_comp g x := ptCls_comp h g x

end Rep

end GlobalTheory.DualCon

namespace GlobalTheory.DualCon

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {B : Over S} {P : LB (A ⊗ B).left}

theorem evc_eq_pull_ptCls (h : Rep A (toUnit B) P) {Y : Over S} (a : Y ⟶ A) (x : Y ⟶ B) :
    evc h.fam.isLB a x = CechPic.pull (lift a (𝟙 Y)).left (ptCls h Y x : Pic (A ⊗ Y).left) := by
  change _ = CechPic.pull (lift a (𝟙 Y)).left (evc h.fam.isLB (fst A Y) (snd A Y ≫ x))
  rw [pull_evc, lift_fst, lift_snd_assoc, Category.id_comp]

theorem rep_isDual : ∀ (S : Scheme.{0}) (A B : Over S) [GrpObj A] (P : LB (A ⊗ B).left),
    Rep A (toUnit B) P → ∃ _ : GrpObj B, IsCommMonObj B ∧ IsDual A B P ∧ IsAdditive (swap P) := by
  intro S A B _ P h
  have hP := h.fam.isLB
  letI inst : CommGrpObj B := CommGrpObj.ofRepresentableBy B _ (famRep h)
  have hmul : ∀ (Y : Over S) (x y : Y ⟶ B), ptCls h Y (x * y) = ptCls h Y x + ptCls h Y y := by
    have hμ : ptCls h (B ⊗ B) μ[B] = ptCls h _ (fst B B) + ptCls h _ (snd B B) :=
      Equiv.ofBijective_apply_symm_apply (ptCls h (B ⊗ B)) (ptCls_bij h _) _
    intro Y x y
    rw [Hom.mul_def, ptCls_comp, hμ, map_add (f := _), ← ptCls_comp, ← ptCls_comp, lift_fst, lift_snd]
  have hone : ∀ (Y : Over S), ptCls h Y (1 : Y ⟶ B) = 0 := by
    have hη : ptCls h (𝟙_ (Over S)) η[B] = 0 :=
      Equiv.ofBijective_apply_symm_apply (ptCls h _) (ptCls_bij h _) 0
    intro Y
    rw [Hom.one_def, ptCls_comp, hη, map_zero]
  refine ⟨inferInstance, inferInstance, ⟨hP, h.fam.add, ?_, fun T M hM hA ↦ ?_⟩, ?_⟩
  · rw [triv_ev_iff hP, evc_eq_pull_ptCls h, hone, ZeroMemClass.coe_zero, map_zero]
  · obtain ⟨x, ⟨-, hx⟩, hu⟩ := h.univ T (toUnit T) M ⟨hM, hA⟩
    exact ⟨x, hx, fun y hy ↦ hu y ⟨toUnit_unique _ _, hy⟩⟩
  · have hs : (swap P).IsLB := pull_isLB hP _
    refine (isAdditive_iff hs).2 fun Y b b' a ↦ ?_
    rw [evc_swap hP hs, evc_swap hP hs, evc_swap hP hs, evc_eq_pull_ptCls h, evc_eq_pull_ptCls h,
      evc_eq_pull_ptCls h, hmul, AddSubgroup.coe_add, map_add]

end GlobalTheory.DualCon
end
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.DualCon

theorem of_isPullback_opens_cover (Q : MorphismProperty Scheme.{0}) [IsZariskiLocalAtTarget Q]
    {S X : Scheme.{0}} {I : Type} {U : I → S.Opens} (hU : iSup U = ⊤) {Z : I → Scheme.{0}} {p : X ⟶ S}
    {q : ∀ i, Z i ⟶ (U i).toScheme} {ψ : ∀ i, Z i ⟶ X} (h : ∀ i, IsPullback (ψ i) (q i) p (U i).ι)
    (hq : ∀ i, Q (q i)) : Q p := by
  refine IsZariskiLocalAtTarget.of_iSup_eq_top U hU fun i => ?_
  have e := (isPullback_morphismRestrict p (U i)).flip
  rw [← IsPullback.isoIsPullback_hom_snd _ _ e (h i), MorphismProperty.cancel_left_of_respectsIso Q]
  exact hq i

theorem isPullback_sigmaι_desc {X : Scheme.{0}} {κ : Type} (V : κ → X.Opens)
    (hd : Pairwise fun i i' => Disjoint (V i) (V i')) {B : κ → Scheme.{0}} (f : ∀ i, B i ⟶ (V i).toScheme)
    (i : κ) : IsPullback (Sigma.ι B i) (f i) (Sigma.desc fun j => f j ≫ (V j).ι) (V i).ι := by
  have : IsOpenImmersion (Sigma.ι B i) := inferInstance
  have hr : ∀ s : PullbackCone (Sigma.desc fun j => f j ≫ (V j).ι) (V i).ι,
      Set.range s.fst ⊆ Set.range (Sigma.ι B i) := by
    rintro s _ ⟨t, rfl⟩
    obtain ⟨⟨j, y⟩, hy⟩ := (sigmaMk B).surjective (s.fst t)
    rw [sigmaMk_mk] at hy
    have e1 : (Sigma.desc fun j => f j ≫ (V j).ι) (s.fst t) = (V i).ι (s.snd t) := congr($(s.condition) t)
    rw [← hy, ← Scheme.Hom.comp_apply, Sigma.ι_desc, Scheme.Hom.comp_apply] at e1
    by_cases hji : j = i
    · subst hji
      exact ⟨y, hy⟩
    · exfalso
      have h1 : (V j).ι (f j y) ∈ V j := ((V j).ι_apply _ ▸ ((f j y).2))
      have h2 : (V i).ι (s.snd t) ∈ V i := ((V i).ι_apply _ ▸ ((s.snd t).2))
      rw [e1] at h1
      have h3 := (hd hji).le_bot (show (V i).ι (s.snd t) ∈ V j ⊓ V i from ⟨h1, h2⟩)
      simp at h3
  refine ⟨⟨Sigma.ι_desc _ _⟩, ⟨PullbackCone.IsLimit.mk _
    (fun s => IsOpenImmersion.lift (Sigma.ι B i) s.fst (hr s)) ?_ ?_ ?_⟩⟩
  · intro s
    exact IsOpenImmersion.lift_fac _ _ _
  · intro s
    rw [← cancel_mono (V i).ι, Category.assoc, ← Sigma.ι_desc (fun j => f j ≫ (V j).ι) i,
      IsOpenImmersion.lift_fac_assoc, s.condition]
  · intro s m h1 _
    rw [← cancel_mono (Sigma.ι B i), IsOpenImmersion.lift_fac, h1]

theorem good_sigmaDesc_of_disjoint_cover : ∀ {X : Scheme.{0}} {κ : Type} [Finite κ] (V : κ → X.Opens), (⨆ i, V i = ⊤) → (Pairwise fun i i' => Disjoint (V i) (V i')) → ∀ {B : κ → Scheme.{0}} (f : ∀ i, B i ⟶ (V i).toScheme) (g : ℕ), (∀ i, Good g (f i)) → Good g (Sigma.desc fun i => f i ≫ (V i).ι) := by
  intro X κ _ V hU hd B f g hf
  have sq := isPullback_sigmaι_desc V hd f
  have hc : IsZariskiLocalAtTarget (@GeometricallyConnected.{0}) := by
    rw [GeometricallyConnected.eq_geometrically]; infer_instance
  have hs : IsZariskiLocalAtTarget (@SmoothOfRelativeDimension.{0} g) :=
    HasRingHomProperty.instIsZariskiLocalAtTarget _
  exact
    { proper := of_isPullback_opens_cover @IsProper hU sq fun i => (hf i).proper
      smooth := of_isPullback_opens_cover (@SmoothOfRelativeDimension.{0} g) hU sq fun i => (hf i).smooth
      conn := of_isPullback_opens_cover @GeometricallyConnected hU sq fun i => (hf i).conn }

end GlobalTheory.DualCon
end
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.DualCon

theorem cls_eq_evc_id {S : Scheme.{0}} {A T : Over S} {M : LB (A ⊗ T).left} (hM : M.IsLB) :
    cls M hM = evc hM (fst A T) (snd A T ≫ 𝟙 T) := by
  rw [Category.comp_id, evc, lift_fst_snd, Over.id_left, pull_id]

theorem cls_trans {S : Scheme.{0}} {A B B' B'' : Over S} {P : LB (A ⊗ B).left} {P' : LB (A ⊗ B').left}
    {Q : LB (A ⊗ B'').left} (hP : P.IsLB) (hP' : P'.IsLB) (hQ : Q.IsLB) (x : B ⟶ B') (y : B' ⟶ B'')
    (hx : LBIso P (ev P' (fst A B) (snd A B ≫ x))) (hy : LBIso P' (ev Q (fst A B') (snd A B' ≫ y))) :
    LBIso P (ev Q (fst A B) (snd A B ≫ x ≫ y)) := by
  refine (cls_eq_iff hP (pull_isLB hQ _)).1 ?_
  rw [(cls_eq_iff hP (pull_isLB hP' _)).2 hx, cls_ev hP', cls_ev hQ, evc,
    (cls_eq_iff hP' (pull_isLB hQ _)).2 hy, cls_ev hQ, pull_evc, lift_fst, lift_snd_assoc, Category.assoc]

theorem rep_unique (S : Scheme.{0}) (A B B' S' : Over S) [GrpObj A] (b : B ⟶ S') (P : LB (A ⊗ B).left)
    (b' : B' ⟶ S') (P' : LB (A ⊗ B').left) (h : Rep A b P) (h' : Rep A b' P') :
    ∃ e : B ≅ B', e.hom ≫ b' = b ∧ Same A P P' (𝟙 B) e.hom := by
  have hP := h.fam.isLB
  have hP' := h'.fam.isLB
  obtain ⟨x, ⟨hxb, hxP⟩, -⟩ := h'.univ B b P h.fam
  obtain ⟨y, ⟨hyb, hyP⟩, -⟩ := h.univ B' b' P' h'.fam
  have idB : LBIso P (ev P (fst A B) (snd A B ≫ 𝟙 B)) :=
    (cls_eq_iff hP (pull_isLB hP _)).1 (cls_eq_evc_id hP)
  have idB' : LBIso P' (ev P' (fst A B') (snd A B' ≫ 𝟙 B')) :=
    (cls_eq_iff hP' (pull_isLB hP' _)).1 (cls_eq_evc_id hP')
  have hxy : x ≫ y = 𝟙 B :=
    (h.univ B b P h.fam).unique ⟨by rw [Category.assoc, hyb, hxb], cls_trans hP hP' hP x y hxP hyP⟩
      ⟨Category.id_comp _, idB⟩
  have hyx : y ≫ x = 𝟙 B' :=
    (h'.univ B' b' P' h'.fam).unique ⟨by rw [Category.assoc, hxb, hyb], cls_trans hP' hP hP' y x hyP hxP⟩
      ⟨Category.id_comp _, idB'⟩
  exact ⟨⟨x, y, hxy, hyx⟩, hxb, (same_id_iff hP hP' x).2 hxP⟩

end GlobalTheory.DualCon
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace GlobalTheory GlobalTheory.DI GlobalTheory.LogDR GlobalTheory.LogPair GlobalTheory.Cartier ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.DI


open CategoryTheory AlgebraicGeometry TopologicalSpace in
theorem _root_.GlobalTheory.DI.mem_locRing_iff_exists_stalkIm : ∀ {X Y : Scheme.{0}} [IsIntegral X] (π : X ⟶ Y) (y : X) (h : π (genericPoint X) ⤳ π y), Function.Surjective (π.stalkMap y).hom → ∀ c : X.functionField, c ∈ _root_.GlobalTheory.LogDR.locRing y ↔ ∃ z ∈ _root_.GlobalTheory.DI.stalkIm h, (π.stalkMap (genericPoint X)).hom z = c := by
  intro X Y _ π y h hsurj c
  have hcomm : ∀ b : Y.presheaf.stalk (π y),
      (π.stalkMap (genericPoint X)).hom ((Y.presheaf.stalkSpecializes h).hom b) =
        algebraMap (X.presheaf.stalk y) X.functionField ((π.stalkMap y).hom b) := by
    intro b
    exact Scheme.Hom.stalkSpecializes_stalkMap_apply π _ _
      ((genericPoint_spec X).specializes (Set.mem_univ y)) b
  constructor
  · rintro ⟨a, rfl⟩
    obtain ⟨b, rfl⟩ := hsurj a
    exact ⟨(Y.presheaf.stalkSpecializes h).hom b, ⟨b, rfl⟩, hcomm b⟩
  · rintro ⟨z, ⟨b, rfl⟩, rfl⟩
    exact ⟨(π.stalkMap y).hom b, (hcomm b).symm⟩

end GlobalTheory.DI
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.DualCon

instance isZariskiLocalAtTarget_smoothDim (n : ℕ) : IsZariskiLocalAtTarget (@SmoothOfRelativeDimension n) :=
  HasRingHomProperty.instIsZariskiLocalAtTarget (@SmoothOfRelativeDimension n)
    (Q := RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension n))

theorem smoothDim_restrict_pullback {S T X : Scheme.{0}} (b : X ⟶ S) (t : T ⟶ S) (U : S.Opens) {n : ℕ}
    (h : SmoothOfRelativeDimension n (pullback.snd b U.ι)) :
    SmoothOfRelativeDimension n (pullback.snd b t ∣_ (t ⁻¹ᵁ U)) := by
  have big := (isPullback_morphismRestrict (pullback.snd b t) (t ⁻¹ᵁ U)).flip.paste_horiz
    (IsPullback.of_hasPullback b t)
  rw [← morphismRestrict_ι t U] at big
  have hc : ((pullback.snd b t ⁻¹ᵁ (t ⁻¹ᵁ U)).ι ≫ pullback.fst b t) ≫ b =
      (pullback.snd b t ∣_ (t ⁻¹ᵁ U) ≫ t ∣_ U) ≫ U.ι := by
    simp only [Category.assoc, pullback.condition, morphismRestrict_ι, morphismRestrict_ι_assoc]
  have sq := IsPullback.of_right (h₁₁ := pullback.lift _ _ hc) (by rw [pullback.lift_fst]; exact big)
    (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback b U.ι)
  exact (smoothOfRelativeDimension_isStableUnderBaseChange n).of_isPullback sq h

theorem dimLe_of_local : ∀ (S : Scheme.{0}) (A B : Over S), Surjective A.hom → ∀ (Ix : Type) (V : Ix → S.Opens) (g : Ix → ℕ), (∀ s : S, ∃ i, s ∈ V i) → (∀ i, SmoothOfRelativeDimension (g i) (pullback.snd A.hom (V i).ι)) → (∀ i, SmoothOfRelativeDimension (g i) (pullback.snd B.hom (V i).ι)) → DimLe A B := by
  intro S A B hs Ix V g hV hA hB n T t hn
  have hcov : iSup (fun i => t ⁻¹ᵁ V i) = ⊤ := by
    rw [eq_top_iff]
    intro y _
    obtain ⟨i, hi⟩ := hV (t y)
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨i, hi⟩
  refine IsZariskiLocalAtTarget.of_iSup_eq_top (P := @SmoothOfRelativeDimension n) _ hcov fun i => ?_
  by_cases hne : ∃ y, y ∈ t ⁻¹ᵁ V i
  · obtain ⟨y, hy⟩ := hne
    have : Surjective (pullback.snd A.hom t) := by haveI := hs; infer_instance
    obtain ⟨x, hx⟩ := (pullback.snd A.hom t).surjective y
    have h1 : SmoothOfRelativeDimension n (pullback.snd A.hom t ∣_ (t ⁻¹ᵁ V i)) :=
      IsZariskiLocalAtTarget.restrict hn _
    have h2 := smoothDim_restrict_pullback A.hom t (V i) (hA i)
    have e : n = g i := ReciprocityTheory.ChartRestriction.G.H1.dim_unique _ h1 h2
      ⟨x, by rw [Scheme.Hom.mem_preimage, hx]; exact hy⟩
    rw [e]
    exact smoothDim_restrict_pullback B.hom t (V i) (hB i)
  · push_neg at hne
    exact ⟨fun x => (hne _ x.2).elim⟩

end GlobalTheory.DualCon
end
end

section

open Module NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColRows

namespace GlobalTheory.ColRows

theorem exists_htNums_of_kerSide_lastSide :
    ∀ (J Pl Emb : Type) [Fintype J] [Fintype Pl] [DecidableEq Pl] [Fintype Emb] (R : RecNums J Pl) (C CT A : ℝ)
      (P : (J → Emb → ℝ) → Prop), 0 ≤ C → 0 ≤ CT → 2 * (16 + CT) ≤ R.Ch → 6 * C + 1 + 2 * C * C ≤ R.Ch →
      4 * C * (CT + C) ≤ R.Ch → KerSide R Emb C P → LastSide R CT A →
      ∃ hn : HtNums R Emb, hn.hPn = A ∧ P hn.sz := by
  intro J Pl Emb _ _ _ _ R C CT A P hC hCT h1 h2 h3 hK hL
  obtain ⟨g0, MainNotions, logOm, logth0, logh, logh', vv, logg, a1, a2, a3, a4, a5, a6, a7, a8, a9, hP⟩ := hK
  obtain ⟨bT, nτ, lam1, D0, D1, logc, logxi, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11⟩ := hL
  refine ⟨{ hPn := A, g0 := g0, MainNotions := MainNotions, logOmτ := logOm, logth0 := logth0, logh := logh, logh' := logh', vv := vv,
            logg := logg, C2 := C, Cth := C, C4 := C, c5 := C, c6 := C, CT := CT, C8 := C, Ce := C, ev := 0, bT := bT,
            nτ := nτ, lam1 := lam1, D0 := D0, D1 := D1, logc := logc, logxi := logxi, Cev := 0,
            i1 := a1, i2 := a2, i3 := a3, i4 := a4, i5 := a5, i6 := a6, i7 := a7, i8 := a8, i9 := a9,
            i10 := ⟨hC, hC, hC, hC, hC, hC, hC⟩,
            t1 := by simpa using b1, t2 := b2, t3 := b3, t4 := b4, t5 := b5, t6 := b6, t7 := b7, t8 := b8, t9 := b9,
            t10 := ⟨b10, b11, hCT⟩, t11 := ⟨by simp, le_rfl⟩,
            k1 := by linarith, k2 := by linarith, k3 := by linarith }, rfl, hP⟩

end GlobalTheory.ColRows
end

section

open Module NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColRows
open scoped ComplexOrder

namespace GlobalTheory.ColRows

theorem exists_inv_frame_of_posDef {n : Type} [Fintype n] [DecidableEq n] (A : Matrix n n ℂ) (hA : A.PosDef) :
    ∃ X : Matrix n n ℂ, IsUnit X.det ∧ (X⁻¹).conjTranspose * X⁻¹ = A := by
  open scoped MatrixOrder in
  obtain ⟨B, hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hA.posSemidef.nonneg
  have hdet : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det A).mp hA.isUnit
  have hBdet : IsUnit B.det := by
    rw [hB, Matrix.det_mul] at hdet
    exact isUnit_of_mul_isUnit_right hdet
  refine ⟨B⁻¹, Matrix.isUnit_nonsing_inv_det B hBdet, ?_⟩
  rw [Matrix.nonsing_inv_nonsing_inv B hBdet, hB, Matrix.star_eq_conjTranspose]

theorem exists_isFrames (K : Type) [Field K] [NumberField K] [StarRing K] (Bs : DefBase K) (Df : DefSide Bs)
    (h : ∀ v : InfinitePlace K, ((Df.HV Bs.μ0).map v.embedding).PosDef) : ∃ X0, IsFrames Df X0 := by
  choose X hX using fun v => exists_inv_frame_of_posDef _ (h v)
  exact ⟨X, hX⟩

end GlobalTheory.ColRows
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Pinch

theorem exists_affine_basicOpen_nbhd : ∀ (B' C Y : Scheme.{0}) (i : Y ⟶ B') (q : Y ⟶ C), IsClosedImmersion i →
    IsFinite q → FinAff B' → ∀ (y : Y) (O : C.Opens), IsAffineOpen O → q y ∈ O →
    ∃ (V' : B'.Opens) (r : Γ(C, O)), IsAffineOpen V' ∧ i y ∈ V' ∧ i ⁻¹ᵁ V' = q ⁻¹ᵁ (C.basicOpen r) := by
  intro B' C Y i q hi hq hB y O hO hyO
  have hF : (q ⁻¹' {q y}).Finite := q.finite_preimage_singleton (q y)
  classical
  obtain ⟨V₀, hV₀, hFV₀⟩ := hB ((hF.image i).toFinset)
  have hY₀ : IsAffineOpen (i ⁻¹ᵁ V₀) := hV₀.preimage i
  obtain ⟨h, hFh, hhO⟩ := GlobalTheory.exists_basicOpen_le_of_finite hY₀ (q ⁻¹ᵁ O) hF
    (fun x hx ↦ hFV₀ _ (by simpa using ⟨x, hx, rfl⟩)) (fun x hx ↦ by
      simp only [Set.mem_preimage, Set.mem_singleton_iff] at hx; simp [hx, hyO])
  have hcl : IsClosed (q '' (Y.basicOpen h : Set Y)ᶜ) :=
    q.isClosedMap _ (Y.basicOpen h).isOpen.isClosed_compl
  have hyW : q y ∉ q '' (Y.basicOpen h : Set Y)ᶜ := by
    rintro ⟨x, hx, hxy⟩
    exact hx (hFh (by simpa using hxy))
  let W : C.Opens := ⟨(q '' (Y.basicOpen h : Set Y)ᶜ)ᶜ, hcl.isOpen_compl⟩
  obtain ⟨r, hrW, hyr⟩ := hO.exists_basicOpen_le (V := W) ⟨q y, hyW⟩ hyO
  have hle : q ⁻¹ᵁ C.basicOpen r ≤ Y.basicOpen h := by
    intro x hx
    by_contra hxh
    exact hrW hx ⟨x, hxh, rfl⟩
  have hbo : q ⁻¹ᵁ C.basicOpen r = Y.basicOpen (q.app O r) := Scheme.preimage_basicOpen q r
  obtain ⟨f', hf'⟩ := hY₀.basicOpen_basicOpen_is_basicOpen h
    (Y.presheaf.map (homOfLE hhO).op (q.app O r))
  rw [Scheme.basicOpen_res, ← hbo, inf_eq_right.mpr hle] at hf'
  obtain ⟨t, ht⟩ := i.app_surjective V₀ hV₀ f'
  refine ⟨B'.basicOpen t, r, hV₀.basicOpen t, ?_, ?_⟩
  · have : y ∈ i ⁻¹ᵁ B'.basicOpen t := by
      rw [Scheme.preimage_basicOpen, ht, hf']; exact hyr
    exact this
  · rw [Scheme.preimage_basicOpen, ht, hf']

end GlobalTheory.Pinch
end

section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.ConjSeq GlobalTheory.AbDual
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_pow_eq_of_kaehlerD_eq_zero_smooth_affineOpen : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [IsAlgClosed k] (hk : (p : k) = 0) (X : Scheme.{0}) [IsIntegral X] (s : X ⟶ Sp k) [Smooth s] (U : X.affineOpens) (u : GlobalTheory.CechDR.Sec s U.1), KaehlerDifferential.D k (GlobalTheory.CechDR.Sec s U.1) u = 0 → ∃ h : GlobalTheory.CechDR.Sec s U.1, h ^ p = u := by
  first | exact @GlobalTheory.ConjSeq.sec_exists_pow_of_D_eq_zero | exact GlobalTheory.ConjSeq.sec_exists_pow_of_D_eq_zero | (intros; apply GlobalTheory.ConjSeq.sec_exists_pow_of_D_eq_zero <;> assumption)
end
