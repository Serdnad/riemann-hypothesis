module

public import Development.EtaleCohomology.CohomologicalPurity.LeafTubeCutHoc
public import Development.EtaleCohomology.CohomologicalPurity.Bundle016
public import Development.EtaleCohomology.EtaleSheaves.Bundle017
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle509
import Development.EtaleCohomology.EtaleTrace.Bundle001
public import Development.EtaleCohomology.EtaleTrace.LocalSplitting.Cover2
public import Development.EtaleCohomology.EtaleSheaves.Bundle029
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle343
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle463
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle462
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle408
public import Mathlib.Basic.Complex.Basic
public import Mathlib.RingTheory.FiniteType
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Limits.Types.Pushouts
import Mathlib.CategoryTheory.Presentable.Type
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.FieldTheory.PurelyInseparable.Exponent
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
public import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle005
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.CoeEqAlgebraMapZeroEquiv
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Edge1
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle001
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.Jacobson.Ideal
public import Mathlib.RingTheory.Jacobson.Ring
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd

@[expose] public section

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.CohomologicalPurity LateralTheory.CohomologicalPurity.TubeCut

namespace UpperTheory.Cb

private theorem dbl_map_id (P : Arrow Spc) : dbl.map (𝟙 P) = 𝟙 _ := by
  set_option synthInstance.maxHeartbeats 200000 in
    apply pushout.hom_ext <;> simp [dbl.map] <;> rfl

private theorem hs_pull_id (q : ℕ) (P : Arrow Spc) (n i : ℤ) (x : Hs q P n i) : Hs.pull q (𝟙 P) n i x = x := by
  apply Subtype.ext
  change pull _ (dbl.map (𝟙 P)) _ _ x.1 = x.1
  rw [dbl_map_id, pull_id]

private theorem exc_iso (q : ℕ) {P' P : Arrow Spc} (e : P' ≅ P) : Exc q e.hom := fun n i =>
  Function.bijective_iff_has_inverse.2 ⟨Hs.pull q e.inv n i,
    fun x => by rw [← hs_pull_comp, e.inv_hom_id, hs_pull_id],
    fun x => by rw [← hs_pull_comp, e.hom_inv_id, hs_pull_id]⟩

private theorem pb_app {X : Scheme.{0}} (U : X.Opens) {E : Spc} (π : E ⟶ sch.obj X) (n : SimplexCategoryᵒᵖ) :
    IsPullback (P := disc.obj ((pullback π (sch.map U.ι)).obj n)) (X := disc.obj (E.obj n)) (Y := sch.obj U.toScheme) (Z := sch.obj X)
      (disc.map ((pullback.fst π (sch.map U.ι)).app n))
      (disc.map ((pullback.snd π (sch.map U.ι)).app n)) (disc.map (π.app n)) (sch.map U.ι) := by
  have h := (IsPullback.of_hasPullback π (sch.map U.ι)).map ((evaluation _ _).obj n)
  exact IsPullback.of_forall_isPullback_app fun _ => h

private def levIso {X : Scheme.{0}} (U : X.Opens) {E : Spc} (π : E ⟶ sch.obj X) (n : SimplexCategoryᵒᵖ) :
    (lev n).obj (abv U π) ≅ abv U (E := disc.obj (E.obj n)) (disc.map (π.app n)) :=
  Arrow.isoMk (pb_app U π n).isoPullback (Iso.refl _)
    ((pb_app U π n).isoPullback_hom_fst.trans (Category.comp_id _).symm)

private theorem pbRel_fst {B G E' E : Spc} (g : G ⟶ B) (a : E' ⟶ E) (π' : E' ⟶ B) (π : E ⟶ B) (h : a ≫ π = π') :
    pbRel g a π' π h ≫ pullback.fst π g = pullback.fst π' g ≫ a := pullback.lift_fst _ _ _

private theorem pbRel_snd {B G E' E : Spc} (g : G ⟶ B) (a : E' ⟶ E) (π' : E' ⟶ B) (π : E ⟶ B) (h : a ≫ π = π') :
    pbRel g a π' π h ≫ pullback.snd π g = pullback.snd π' g :=
  (pullback.lift_snd _ _ _).trans (Category.comp_id _)

private theorem abvRel_square {X : Scheme.{0}} (U : X.Opens) {A B C D : Spc} (a : A ⟶ B) (b : B ⟶ D) (c : A ⟶ C) (d : C ⟶ D)
    (pA : A ⟶ sch.obj X) (pB : B ⟶ sch.obj X) (pC : C ⟶ sch.obj X) (pD : D ⟶ sch.obj X) (h1 : a ≫ pB = pA) (h2 : b ≫ pD = pB)
    (h3 : c ≫ pC = pA) (h4 : d ≫ pD = pC) (w : a ≫ b = c ≫ d) :
    abvRel U a pA pB h1 ≫ abvRel U b pB pD h2 = abvRel U c pA pC h3 ≫ abvRel U d pC pD h4 := by
  apply Arrow.hom_ext
  · change pbRel _ a _ _ h1 ≫ pbRel _ b _ _ h2 = pbRel _ c _ _ h3 ≫ pbRel _ d _ _ h4
    apply pullback.hom_ext
    · simp only [Category.assoc, pbRel_fst]
      rw [← Category.assoc, pbRel_fst, ← Category.assoc, pbRel_fst, Category.assoc, Category.assoc, w]
    · simp only [Category.assoc, pbRel_snd]
  · exact w

private theorem iso_gen {B G E' E P' P : Spc} (g : G ⟶ B) (a : E' ⟶ E) (π' : E' ⟶ B) (π : E ⟶ B) (h : a ≫ π = π')
    (f' : P' ⟶ E') (s' : P' ⟶ G) (f : P ⟶ E) (s : P ⟶ G) (hp' : IsPullback f' s' π' g) (hp : IsPullback f s π g)
    (t : P' ⟶ P) (h1 : t ≫ f = f' ≫ a) (h2 : t ≫ s = s') :
    t ≫ hp.isoPullback.hom = hp'.isoPullback.hom ≫ pbRel g a π' π h := by
  apply pullback.hom_ext
  · rw [Category.assoc, Category.assoc, pbRel_fst, hp.isoPullback_hom_fst, ← Category.assoc _ (pullback.fst _ _),
      hp'.isoPullback_hom_fst, h1]
  · rw [Category.assoc, Category.assoc, pbRel_snd, hp.isoPullback_hom_snd, hp'.isoPullback_hom_snd, h2]

private theorem lev_abvRel {X : Scheme.{0}} (U : X.Opens) {E' E : Spc} (a : E' ⟶ E) (π' : E' ⟶ sch.obj X) (π : E ⟶ sch.obj X)
    (h : a ≫ π = π') (n : SimplexCategoryᵒᵖ) (hn) :
    (lev n).map (abvRel U a π' π h) ≫ (levIso U π n).hom =
      (levIso U π' n).hom ≫ abvRel U (E' := disc.obj (E'.obj n)) (E := disc.obj (E.obj n)) (disc.map (a.app n))
        (disc.map (π'.app n)) (disc.map (π.app n)) hn := by
  have f1 := pbRel_fst (sch.map U.ι) a π' π h
  have f2 := pbRel_snd (sch.map U.ι) a π' π h
  apply Arrow.hom_ext
  · exact iso_gen _ _ _ _ hn _ _ _ _ (pb_app U π' n) (pb_app U π n) (disc.map ((pbRel _ a _ _ h).app n))
      ((disc.map_comp _ _).symm.trans ((congrArg (fun t => disc.map (NatTrans.app t n)) f1).trans (disc.map_comp _ _)))
      ((disc.map_comp _ _).symm.trans (congrArg (fun t => disc.map (NatTrans.app t n)) f2))
  · rfl

section
variable {J : Type} [SmallCategory J]

private theorem inj_aug {D : J ⥤ PSh} {Y : PSh} (c : ∀ j, D.obj j ⟶ Y) (hc : Coc D c) (n : SimplexCategoryᵒᵖ)
    (σ : Fin (n.unop.len + 1) ⥤ J) : inj D n σ ≫ (aug c hc).app n = c (σ.obj 0) := by
  have e : σ.map (homOfLE (Fin.zero_le (0 : Fin (n.unop.len + 1)))) = 𝟙 _ := σ.map_id _
  ext U x
  change (c (σ.obj 0)).app U ((D.map (σ.map (homOfLE (Fin.zero_le (0 : Fin (n.unop.len + 1)))))).app U x) = _
  rw [e]
  simp

private theorem inj_nat {D' D : J ⥤ PSh} (α : D' ⟶ D) (n : SimplexCategoryᵒᵖ) (σ : Fin (n.unop.len + 1) ⥤ J) :
    inj D' n σ ≫ ((hocF J).map α).app n = α.app (σ.obj 0) ≫ inj D n σ := by
  ext U x
  have e : (fun i => (α.app (σ.obj i)).app U ((D'.map (σ.map (homOfLE (Fin.zero_le i)))).app U x)) =
      fun i => (D.map (σ.map (homOfLE (Fin.zero_le i)))).app U ((α.app (σ.obj 0)).app U x) :=
    funext fun i => ConcreteCategory.congr_hom (NatTrans.congr_app (α.naturality (σ.map (homOfLE (Fin.zero_le i)))) U) x
  have hk : ∀ i k (g : i ⟶ k), (D.flip.obj U).map (σ.map g) ((α.app (σ.obj i)).app U ((D'.map (σ.map (homOfLE (Fin.zero_le i)))).app U x)) =
      (α.app (σ.obj k)).app U ((D'.map (σ.map (homOfLE (Fin.zero_le k)))).app U x) := fun i k g => by
    have a := congrFun e i
    have b := congrFun e k
    dsimp only at a b
    rw [a, b]
    exact ConcreteCategory.congr_hom (NatTrans.congr_app (laurent_adjoin_eq_of_image_eq D σ i k g) U) _
  exact mkChn_congr (F := D.flip.obj U) σ e hk
    (fun i k g => ConcreteCategory.congr_hom (NatTrans.congr_app (laurent_adjoin_eq_of_image_eq D σ i k g) U) _)

end

private theorem sum_transfer (q : ℕ) {P' P : Arrow Spc} (f : P' ⟶ P) {A : Type} (Q' Q : A → Arrow Spc)
    (r' : ∀ a, Q' a ⟶ P') (r : ∀ a, Q a ⟶ P) (t : ∀ a, Q' a ⟶ Q a) (w : ∀ a, r' a ≫ f = t a ≫ r a) (ht : ∀ a, Exc q (t a))
    (B : ∀ n i : ℤ, Function.Bijective fun (x : Hs q P n i) a => Hs.pull q (r a) n i x)
    (B' : ∀ n i : ℤ, Function.Bijective fun (x : Hs q P' n i) a => Hs.pull q (r' a) n i x) : Exc q f := by
  intro n i
  refine (Function.Bijective.of_comp_iff' (B' n i) _).1 ?_
  have T : Function.Bijective (Pi.map fun a => Hs.pull q (t a) n i) := Function.Bijective.piMap fun a => ht a n i
  convert T.comp (B n i) using 1
  funext x a
  change Hs.pull q (r' a) n i (Hs.pull q f n i x) = Hs.pull q (t a) n i (Hs.pull q (r a) n i x)
  rw [← hs_pull_comp, ← hs_pull_comp, w]

private theorem exc_lvl (hL : LeafLevel) (hS : LeafHsSum) (q : ℕ) {J : Type} [SmallCategory J] {D' D : J ⥤ PSh} (α : D' ⟶ D)
    {X : Scheme.{0}} (U : X.Opens) (c' : ∀ j, D'.obj j ⟶ yoneda.obj X) (c : ∀ j, D.obj j ⟶ yoneda.obj X)
    (hc' : Coc D' c') (hc : Coc D c) (h : ∀ j, disc.map (α.app j) ≫ disc.map (c j) = disc.map (c' j))
    (ht : ∀ j, Exc q (abvRel U (disc.map (α.app j)) (disc.map (c' j)) (disc.map (c j)) (h j)))
    (n : SimplexCategoryᵒᵖ) (π' : (hoc D').obj n ⟶ yoneda.obj X) (π : (hoc D).obj n ⟶ yoneda.obj X)
    (e' : π' = (aug c' hc').app n) (e : π = (aug c hc).app n) (hn) :
    Exc q (abvRel U (E' := disc.obj ((hoc D').obj n)) (E := disc.obj ((hoc D).obj n)) (disc.map (((hocF J).map α).app n))
      (disc.map π') (disc.map π) hn) := by
  obtain ⟨cD⟩ := hL J D n
  obtain ⟨cD'⟩ := hL J D' n
  have hp : ∀ σ : Fin (n.unop.len + 1) ⥤ J, disc.map (inj D n σ) ≫ disc.map π = disc.map (c (σ.obj 0)) :=
    fun σ => (disc.map_comp _ _).symm.trans (congrArg disc.map (e ▸ inj_aug c hc n σ))
  have hp' : ∀ σ : Fin (n.unop.len + 1) ⥤ J, disc.map (inj D' n σ) ≫ disc.map π' = disc.map (c' (σ.obj 0)) :=
    fun σ => (disc.map_comp _ _).symm.trans (congrArg disc.map (e' ▸ inj_aug c' hc' n σ))
  refine sum_transfer q _ (fun σ : Fin (n.unop.len + 1) ⥤ J => abv U (E := disc.obj (D'.obj (σ.obj 0))) (disc.map (c' (σ.obj 0))))
    (fun σ => abv U (E := disc.obj (D.obj (σ.obj 0))) (disc.map (c (σ.obj 0))))
    (fun σ => abvRel U (disc.map (inj D' n σ)) _ _ (hp' σ)) (fun σ => abvRel U (disc.map (inj D n σ)) _ _ (hp σ))
    (fun σ => abvRel U (disc.map (α.app (σ.obj 0))) _ _ (h _)) (fun σ => ?_) (fun σ => ht _) ?_ ?_
  · exact abvRel_square U _ _ _ _ _ _ _ _ _ _ _ _
      ((disc.map_comp _ _).symm.trans ((congrArg disc.map (inj_nat α n σ)).trans (disc.map_comp _ _)))
  · exact fun m i => hS q X U _ (fun σ : Fin (n.unop.len + 1) ⥤ J => D.obj (σ.obj 0)) (Cofan.mk _ (inj D n)) ⟨cD⟩
      π (fun σ => c (σ.obj 0)) hp m i
  · exact fun m i => hS q X U _ (fun σ : Fin (n.unop.len + 1) ⥤ J => D'.obj (σ.obj 0)) (Cofan.mk _ (inj D' n)) ⟨cD'⟩
      π' (fun σ => c' (σ.obj 0)) hp' m i

theorem etale_excision_hocolim_of_local_properties :
    LateralTheory.CohomologicalPurity.TubeCut.LeafExcLevel → LateralTheory.CohomologicalPurity.TubeCut.LeafLevel → LateralTheory.CohomologicalPurity.TubeCut.LeafHsSum → LateralTheory.CohomologicalPurity.LeafAW → LateralTheory.CohomologicalPurity.LeafBd → LateralTheory.CohomologicalPurity.LeafExc → LateralTheory.CohomologicalPurity.LeafHens → LateralTheory.CohomologicalPurity.LeafIndExc → LateralTheory.CohomologicalPurity.TubeCut.LeafExcHoc := by
  intro hE hL hS _ _ _ _ _ a3 q J _ D' D α X U c' c hc' hc h h' ht
  refine hE a3 q _ _ _ fun n => ?_
  have hn : disc.map (((hocF J).map α).app n) ≫ disc.map ((aug c hc).app n) = disc.map ((aug c' hc').app n) :=
    (disc.map_comp _ _).symm.trans (congrArg (fun t => disc.map (t.app n)) h')
  have e := lev_abvRel U ((hocF J).map α) (aug c' hc') (aug c hc) h' n hn
  have k := exc_lvl hL hS q α U c' c hc' hc h ht n _ _ rfl rfl hn
  have e' : (lev n).map (abvRel U ((hocF J).map α) (aug c' hc') (aug c hc) h') =
      (levIso U (aug c' hc') n).hom ≫ abvRel U (E' := disc.obj ((hoc D').obj n)) (E := disc.obj ((hoc D).obj n))
        (disc.map (((hocF J).map α).app n)) (disc.map ((aug c' hc').app n)) (disc.map ((aug c hc).app n)) hn ≫
        (levIso U (aug c hc) n).inv := by
    rw [← Category.assoc, ← e, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [e']
  exact exc_comp q (exc_iso q _) (exc_comp q k (exc_iso q (levIso U (aug c hc) n).symm))

end UpperTheory.Cb
end
end

section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC

theorem UpperTheory.Cb.curve_mayer_vietoris_of_degree_zero :
    LateralTheory.E.E4.H0TwistOverClosedField → LateralTheory.E.E4.CurveCut.LeafMV := by
  intro _ _ R _ F X U V hUV n
  obtain ⟨d, hd, -⟩ := mayerVietoris R F
  have hc := LateralTheory.EtaleTrace.LSplitPf.Sch.cover2 R U V hUV
  haveI : PreservesLimitsOfShape WalkingCospan sch := by
    unfold sch; infer_instance
  have P := (isPullback_opens_inf U V).map sch
  refine ⟨(d _ _ hc n).comp (pull R P.isoPullback.inv F n), fun x => ?_⟩
  rw [(hd _ _ hc n).2.2 x]
  constructor
  · rintro ⟨c, rfl⟩
    refine ⟨pull R P.isoPullback.hom F n c, ?_⟩
    rw [AddMonoidHom.comp_apply, ← pull_comp, Iso.inv_hom_id, pull_id]
  · rintro ⟨y, rfl⟩
    exact ⟨_, rfl⟩
end

section

theorem UpperTheory.Cb.etale_mayer_vietoris_short_exact :
    LateralTheory.E.MayerVietorisSequence.SES := by
  intro R _ U V E f g h
  exact GlobalTheory.T.etaleSpaceChains_mayerVietoris_shortExact R f g h
end

section

open CategoryTheory Limits CochainComplex CochainComplex.HomComplex GlobalTheory.EtC GlobalTheory.EtC.BiprodCls

namespace UpperTheory.Cb.EtaleMayerVietoris

variable {R : Type} [CommRing R]

private theorem cpull_lift_neg {N K L : Cx R} (a : N ⟶ K) (b : N ⟶ L) (I : Cx R) (n : ℤ)
    (y : CohomologyClass (K ⊞ L) I n) :
    cpull (biprod.lift a (-b)) I n y =
      cpull a I n (cpull biprod.inl I n y) - cpull b I n (cpull biprod.inr I n y) := by
  have hl : biprod.lift a (-b) = a ≫ biprod.inl + (-b) ≫ biprod.inr := by
    apply biprod.hom_ext <;> simp
  have h0 : ∀ {P Q : Cx R} (x : CohomologyClass Q I n), cpull (0 : P ⟶ Q) I n x = 0 := by
    intro P Q x
    have h := cpull_add (0 : P ⟶ Q) 0 I n x
    rw [add_zero] at h
    simpa using h
  have hn : ∀ {P Q : Cx R} (f : P ⟶ Q) (x : CohomologyClass Q I n),
      cpull (-f) I n x = -cpull f I n x := by
    intro P Q f x
    have h := cpull_add f (-f) I n x
    rw [add_neg_cancel, h0] at h
    exact eq_neg_of_add_eq_zero_right h.symm
  rw [hl, cpull_add, ← cpull_cpull, ← cpull_cpull, hn, sub_eq_add_neg]

private theorem cpull_inl_desc {K L M : Cx R} (c : K ⟶ M) (e : L ⟶ M) (I : Cx R) (n : ℤ)
    (z : CohomologyClass M I n) :
    cpull biprod.inl I n (cpull (biprod.desc c e) I n z) = cpull c I n z := by
  rw [cpull_cpull, biprod.inl_desc]

private theorem cpull_inr_desc {K L M : Cx R} (c : K ⟶ M) (e : L ⟶ M) (I : Cx R) (n : ℤ)
    (z : CohomologyClass M I n) :
    cpull biprod.inr I n (cpull (biprod.desc c e) I n z) = cpull e I n z := by
  rw [cpull_cpull, biprod.inr_desc]

end UpperTheory.Cb.EtaleMayerVietoris


open UpperTheory.Cb.EtaleMayerVietoris in
theorem UpperTheory.Cb.etale_mayer_vietoris_long_exact :
    LateralTheory.E.MayerVietorisSequence.LES := by
  intro R _ F
  obtain ⟨d0, hex, hnat⟩ := GlobalTheory.T.hypercohomology_longExact_first_of_injective R (res R F) (GlobalTheory.T.chosenInjectiveResolution_etaleSheaf_properties R F).2.1
  refine ⟨fun a b c e w hS n => d0 _ hS n, ?_, ?_⟩
  · intro N K L M a b c e w hS n
    have hE := hex _ hS n
    obtain ⟨hinj, hsurj⟩ := cpull_biprod_bijective R K L (res R F) n
    have back : ∀ (z : CohomologyClass M (res R F) n) (u : CohomologyClass (K ⊞ L) (res R F) n),
        cpull biprod.inl (res R F) n u = cpull c (res R F) n z →
        cpull biprod.inr (res R F) n u = cpull e (res R F) n z →
        cpull (biprod.desc c e) (res R F) n z = u := by
      intro z u h1 h2
      refine hinj (Prod.ext ?_ ?_)
      · change cpull biprod.inl _ n (cpull (biprod.desc c e) _ n z) = cpull biprod.inl _ n u
        rw [cpull_inl_desc, h1]
      · change cpull biprod.inr _ n (cpull (biprod.desc c e) _ n z) = cpull biprod.inr _ n u
        rw [cpull_inr_desc, h2]
    refine ⟨fun x y => ?_, fun t => ?_, fun z => ?_⟩
    · obtain ⟨u, hu⟩ := hsurj (x, y)
      simp only [Prod.mk.injEq] at hu
      obtain ⟨hx, hy⟩ := hu
      have key : HK.pull R a F n x = HK.pull R b F n y ↔
          cpull (biprod.lift a (-b)) (res R F) n u = 0 := by
        rw [cpull_lift_neg, hx, hy, sub_eq_zero]
        rfl
      refine key.trans ((hE.1 u).trans ?_)
      constructor
      · rintro ⟨z, hz⟩
        have hz' : cpull (biprod.desc c e) (res R F) n z = u := hz
        refine ⟨z, ?_, ?_⟩
        · change cpull c (res R F) n z = x
          rw [← hx, ← hz', cpull_inl_desc]
        · change cpull e (res R F) n z = y
          rw [← hy, ← hz', cpull_inr_desc]
      · rintro ⟨z, hzx, hzy⟩
        exact ⟨z, back z u (hx.trans hzx.symm) (hy.trans hzy.symm)⟩
    · refine (hE.2.1 t).trans ?_
      constructor
      · rintro ⟨u, hu⟩
        have hu' : cpull (biprod.lift a (-b)) (res R F) n u = t := hu
        refine ⟨cpull biprod.inl (res R F) n u, cpull biprod.inr (res R F) n u, ?_⟩
        rw [← hu', cpull_lift_neg]
        rfl
      · rintro ⟨x, y, rfl⟩
        obtain ⟨u, hu⟩ := hsurj (x, y)
        simp only [Prod.mk.injEq] at hu
        obtain ⟨hx, hy⟩ := hu
        refine ⟨u, ?_⟩
        change cpull (biprod.lift a (-b)) (res R F) n u = _
        rw [cpull_lift_neg, hx, hy]
        rfl
    · obtain ⟨hinj1, -⟩ := cpull_biprod_bijective R K L (res R F) (n + 1)
      refine Iff.trans ?_ (hE.2.2 z)
      change _ ↔ cpull (biprod.desc c e) (res R F) (n + 1) z = 0
      constructor
      · rintro ⟨h1, h2⟩
        refine hinj1 (Prod.ext ?_ ?_)
        · change cpull biprod.inl _ _ (cpull (biprod.desc c e) _ _ z) = cpull biprod.inl _ _ 0
          rw [cpull_inl_desc, map_zero]
          exact h1
        · change cpull biprod.inr _ _ (cpull (biprod.desc c e) _ _ z) = cpull biprod.inr _ _ 0
          rw [cpull_inr_desc, map_zero]
          exact h2
      · intro h
        constructor
        · change cpull c (res R F) (n + 1) z = 0
          rw [← cpull_inl_desc c e, h, map_zero]
        · change cpull e (res R F) (n + 1) z = 0
          rw [← cpull_inr_desc c e, h, map_zero]
  · intro N K L M N' K' L' M' a b c e a' b' c' e' w w' hS hS' φN φK φL φM h1 h2 h3 h4 n t
    let φ : ShortComplex.mk (biprod.lift a (-b)) (biprod.desc c e) w ⟶
        ShortComplex.mk (biprod.lift a' (-b')) (biprod.desc c' e') w' :=
      { τ₁ := φN
        τ₂ := biprod.map φK φL
        τ₃ := φM
        comm₁₂ := by
          apply biprod.hom_ext <;> simp [h1, h2]
        comm₂₃ := by
          apply biprod.hom_ext' <;> simp [h3, h4] }
    exact hnat _ _ hS hS' φ n t
end

section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.HodgeCoh GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 KaehlerDifferential
open scoped TensorProduct

private theorem exists_algHom_complex_ker_eq_maximal (A : Type) [CommRing A] [Algebra ℂ A] [Algebra.FiniteType ℂ A]
    (m : Ideal A) [m.IsMaximal] : ∃ e : A →ₐ[ℂ] ℂ, ∀ x, e x = 0 ↔ x ∈ m := by
  letI := Ideal.Quotient.field m
  haveI : Module.Finite ℂ (A ⧸ m) := finite_of_finite_type_of_isJacobsonRing ℂ (A ⧸ m)
  have hb := IsAlgClosed.algebraMap_bijective_of_isIntegral (k := ℂ) (K := A ⧸ m)
  let φ := AlgEquiv.ofBijective (Algebra.ofId ℂ (A ⧸ m)) hb
  refine ⟨φ.symm.toAlgHom.comp (Ideal.Quotient.mkₐ ℂ m), fun x => ?_⟩
  show φ.symm (Ideal.Quotient.mkₐ ℂ m x) = 0 ↔ _
  rw [map_eq_zero_iff _ φ.symm.injective, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem]

private theorem mem_of_reduced_vanishing_on_zeros (A : Type) [CommRing A] [Algebra ℂ A] [Algebra.FiniteType ℂ A]
    (J : Ideal A) (hred : IsReduced (A ⧸ J)) (x : A)
    (hx : ∀ e : A →ₐ[ℂ] ℂ, (∀ y ∈ J, e y = 0) → e x = 0) : x ∈ J := by
  haveI : IsJacobsonRing A := isJacobsonRing_of_finiteType (A := ℂ)
  have hj : x ∈ J.jacobson := by
    rw [Ideal.jacobson, Submodule.mem_sInf]
    rintro m ⟨hJm, hm⟩
    haveI := hm
    obtain ⟨e, he⟩ := exists_algHom_complex_ker_eq_maximal A m
    exact (he x).1 (hx e fun y hy => (he y).2 (hJm hy))
  rw [← Ideal.radical_eq_jacobson] at hj
  obtain ⟨n, hn⟩ := hj
  haveI := hred
  have hnil : IsNilpotent (Ideal.Quotient.mk J x) :=
    ⟨n, by rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]; exact hn⟩
  exact Ideal.Quotient.eq_zero_iff_mem.1 hnil.eq_zero

theorem UpperTheory.Cb.exists_unit_mul_mem_span_of_reduced_isolated_zero :
    ∀ (A : Type) [CommRing A] [Algebra ℂ A] [Algebra.FiniteType ℂ A] (d : ℕ) (t : Fin d → A), IsReduced (A ⧸ Ideal.span (Set.range t)) → Finite {e : A →ₐ[ℂ] ℂ // ∀ j, e (t j) = 0} → ∀ e : A →ₐ[ℂ] ℂ, (∀ j, e (t j) = 0) → ∀ b : A, e b = 0 → ∃ (c : A) (g : Fin d → A), e c ≠ 0 ∧ c * b = ∑ l, g l * t l := by
  intro A _ _ _ d t hred hfin e he b hb
  have key : ∀ s : {e' : A →ₐ[ℂ] ℂ // ∀ j, e' (t j) = 0},
      ∃ a : A, e a ≠ 0 ∧ (s.1 ≠ e → s.1 a = 0) := by
    intro s
    by_cases hs : s.1 = e
    · exact ⟨1, by simp, fun h => absurd hs h⟩
    · obtain ⟨y, hy⟩ : ∃ y, e y ≠ s.1 y := by
        by_contra hcon
        push_neg at hcon
        exact hs (AlgHom.ext fun y => (hcon y).symm)
      refine ⟨y - algebraMap ℂ A (s.1 y), ?_, fun _ => ?_⟩
      · rw [map_sub, AlgHom.commutes]
        exact sub_ne_zero.2 hy
      · rw [map_sub, AlgHom.commutes]
        exact sub_self _
  choose f hf using key
  haveI := Fintype.ofFinite {e' : A →ₐ[ℂ] ℂ // ∀ j, e' (t j) = 0}
  refine ⟨∏ s, f s, ?_⟩
  have hmem : (∏ s, f s) * b ∈ Ideal.span (Set.range t) := by
    apply mem_of_reduced_vanishing_on_zeros A _ hred
    intro e' he'
    have ht : ∀ j, e' (t j) = 0 := fun j => he' _ (Ideal.subset_span ⟨j, rfl⟩)
    by_cases hee : e' = e
    · subst hee
      rw [map_mul, hb, mul_zero]
    · rw [map_mul, map_prod, Finset.prod_eq_zero (Finset.mem_univ ⟨e', ht⟩) ((hf ⟨e', ht⟩).2 hee),
        zero_mul]
  obtain ⟨g, hg⟩ := Ideal.mem_span_range_iff_exists_fun.1 hmem
  refine ⟨g, ?_, hg.symm⟩
  rw [map_prod]
  exact Finset.prod_ne_zero_iff.2 fun s _ => (hf s).1
end
