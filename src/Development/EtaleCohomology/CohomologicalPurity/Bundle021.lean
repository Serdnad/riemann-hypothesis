module

public import Development.EtaleCohomology.CohomologicalPurity.Bundle012
public import Development.EtaleCohomology.CohomologicalPurity.Bundle013
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Limits.Types.Pushouts
public import Mathlib.CategoryTheory.Abelian.CommSq
import Mathlib.CategoryTheory.EffectiveEpi.Comp
import Mathlib.CategoryTheory.ExtremalEpi
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.TypeStar

@[expose] public section

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex.HomComplex

namespace LateralTheory.CohomologicalPurity

section Gen
variable {C : Type*} [Category C] [Abelian C]

theorem cokPO_iso {A B Q : C} (f : A ⟶ B) (l r : B ⟶ Q) (h : IsPushout f f l r) :
    IsIso (cokernel.map f r f l h.w.symm) := by
  refine ⟨⟨cokernel.desc r (h.desc (cokernel.π f) 0 (by simp)) (by simp), ?_, ?_⟩⟩
  · ext; simp
  · ext
    simp only [cokernel.π_desc_assoc, Category.comp_id]
    refine h.hom_ext ?_ ?_
    · simp
    · simp

theorem cokMap_comp {A B A' B' A'' B'' : C} (f : A ⟶ B) (f' : A' ⟶ B') (f'' : A'' ⟶ B'')
    (a : A ⟶ A') (b : B ⟶ B') (w : f ≫ b = a ≫ f') (a' : A' ⟶ A'') (b' : B' ⟶ B'') (w' : f' ≫ b' = a' ≫ f'') :
    cokernel.map f f' a b w.symm ≫ cokernel.map f' f'' a' b' w'.symm =
      cokernel.map f f'' (a ≫ a') (b ≫ b') (by rw [Category.assoc, ← w', ← Category.assoc, ← w, Category.assoc]) := by
  ext; simp

theorem cokPO_transfer {A' B' Q' A B Q : C} (f' : A' ⟶ B') (l' r' : B' ⟶ Q') (h' : IsPushout f' f' l' r')
    (f : A ⟶ B) (l r : B ⟶ Q) (h : IsPushout f f l r) (a : A' ⟶ A) (b : B' ⟶ B) (m : Q' ⟶ Q)
    (w : f' ≫ b = a ≫ f) (wl : l' ≫ m = b ≫ l) (wr : r' ≫ m = b ≫ r)
    (hi : IsIso (cokernel.map f' f a b w.symm)) : IsIso (cokernel.map r' r b m wr.symm) := by
  have := cokPO_iso f' l' r' h'
  have := cokPO_iso f l r h
  have e : cokernel.map f' r' f' l' h'.w.symm ≫ cokernel.map r' r b m wr.symm =
      cokernel.map f' f a b w.symm ≫ cokernel.map f r f l h.w.symm := by
    ext
    simp [Category.assoc, wl]
    simpa only [Category.assoc] using congrArg (fun k => k ≫ cokernel.π r) wl
  have : cokernel.map r' r b m wr.symm = inv (cokernel.map f' r' f' l' h'.w.symm) ≫
      (cokernel.map f' f a b w.symm ≫ cokernel.map f r f l h.w.symm) := by rw [← e]; simp
  rw [this]; infer_instance

theorem cokIso_comp {A B A' B' : C} (f : A ⟶ B) (f' : A' ⟶ B') (a : A ⟶ A') (b : B ⟶ B') (w : f ≫ b = a ≫ f')
    [IsIso a] [IsIso b] : IsIso (cokernel.map f f' a b w.symm) :=
  ⟨⟨cokernel.map f' f (inv a) (inv b) (by apply Eq.symm; rw [IsIso.eq_inv_comp, ← Category.assoc, ← w]; simp),
    by ext; simp, by ext; simp⟩⟩

end Gen

section Spec
variable (R : Type) [CommRing R]

theorem emb_f (p : ℕ) : ComplexShape.embeddingDownNat.f p = -(p : ℤ) := rfl

theorem extKey (p : ℕ) {K L : ChainComplex (Shv R) ℕ} (φ : K ⟶ L) :
    (HomologicalComplex.eval _ _ (-(p:ℤ))).map ((ComplexShape.embeddingDownNat.extendFunctor (Shv R)).map φ) =
      (K.extendXIso _ (emb_f p)).hom ≫ φ.f p ≫ (L.extendXIso _ (emb_f p)).inv :=
  HomologicalComplex.extendMap_f φ _ (emb_f p)

def chIso (p : ℕ) : chains R ⋙ HomologicalComplex.eval _ _ (-(p : ℤ)) ≅
    (evaluation SimplexCategoryᵒᵖ PSh).obj (op (SimplexCategory.mk p)) ⋙ free R :=
  NatIso.ofComponents (fun K => ((chainsN R).obj K).extendXIso ComplexShape.embeddingDownNat (emb_f p)) (by
    intro K L g
    change (HomologicalComplex.eval _ _ _).map ((ComplexShape.embeddingDownNat.extendFunctor (Shv R)).map
      ((chainsN R).map g)) ≫ _ = _ ≫ (free R).map (g.app _)
    rw [extKey]
    erw [Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rfl)

instance : PreservesColimitsOfShape WalkingSpan (free R) := by
  have h1 : PreservesColimitsOfShape WalkingSpan (uliftFunctor.{1, 0}) := inferInstance
  have h2' := (ModuleCat.adj (ULift.{1, 0} R)).leftAdjoint_preservesColimits
  have h2 : PreservesColimitsOfShape WalkingSpan (ModuleCat.free (ULift.{1, 0} R)) := inferInstance
  have h3 : PreservesColimitsOfShape WalkingSpan (uliftFunctor.{1, 0} ⋙ ModuleCat.free (ULift.{1, 0} R)) := inferInstance
  have : PreservesColimitsOfShape WalkingSpan (freeP R) := by
    unfold freeP; infer_instance
  unfold free; infer_instance

end Spec

section Gen2

theorem cokF {C D : Type*} [Category C] [Abelian C] [Category D] [Abelian D] (F : C ⥤ D)
    [F.PreservesZeroMorphisms] [PreservesColimitsOfShape WalkingParallelPair F] {A B A' B' : C}
    (f : A ⟶ B) (f' : A' ⟶ B') (a : A ⟶ A') (b : B ⟶ B') (w : f ≫ b = a ≫ f')
    (hi : IsIso (cokernel.map (F.map f) (F.map f') (F.map a) (F.map b) (by rw [← F.map_comp, ← w, F.map_comp]))) :
    IsIso (F.map (cokernel.map f f' a b w.symm)) := by
  have e : F.map (cokernel.map f f' a b w.symm) = inv (cokernelComparison f F) ≫
      (cokernel.map (F.map f) (F.map f') (F.map a) (F.map b) (by rw [← F.map_comp, ← w, F.map_comp]) ≫
        cokernelComparison f' F) := by
    rw [IsIso.eq_inv_comp]; ext; simp [← Functor.map_comp]
  rw [e]; infer_instance

theorem cokNat {C E : Type*} [Category C] [Abelian C] [Category E] (Φ Ψ : E ⥤ C) (α : Φ ≅ Ψ)
    {X' Y' X Y : E} (g' : X' ⟶ Y') (g : X ⟶ Y) (a : X' ⟶ X) (b : Y' ⟶ Y) (w : g' ≫ b = a ≫ g)
    (hi : IsIso (cokernel.map (Ψ.map g') (Ψ.map g) (Ψ.map a) (Ψ.map b) (by simp only [← Functor.map_comp, w]))) :
    IsIso (cokernel.map (Φ.map g') (Φ.map g) (Φ.map a) (Φ.map b) (by simp only [← Functor.map_comp, w])) := by
  have h1 := cokIso_comp (Φ.map g') (Ψ.map g') (α.hom.app X') (α.hom.app Y') (α.hom.naturality g')
  have h2 := cokIso_comp (Φ.map g) (Ψ.map g) (α.hom.app X) (α.hom.app Y) (α.hom.naturality g)
  have e : cokernel.map (Φ.map g') (Φ.map g) (Φ.map a) (Φ.map b) (by simp only [← Functor.map_comp, w]) =
      (cokernel.map (Φ.map g') (Ψ.map g') (α.hom.app X') (α.hom.app Y') (α.hom.naturality g').symm ≫
        cokernel.map (Ψ.map g') (Ψ.map g) (Ψ.map a) (Ψ.map b) (by simp only [← Functor.map_comp, w])) ≫
      inv (cokernel.map (Φ.map g) (Ψ.map g) (α.hom.app X) (α.hom.app Y) (α.hom.naturality g).symm) := by
    rw [IsIso.eq_comp_inv]; ext; simp [Category.assoc, ← Functor.map_comp]
  rw [e]; infer_instance

end Gen2

section Main
variable (R : Type) [CommRing R]

theorem dbl.inl_map' {P' P : Arrow Spc} (φ : P' ⟶ P) : dbl.inl P' ≫ dbl.map φ = φ.right ≫ dbl.inl P :=
  pushout.inl_desc (f := P'.hom) (g := P'.hom) _ _ _

theorem hPO (P : Arrow Spc) (p : SimplexCategoryᵒᵖ) :
    IsPushout ((free R).map (P.hom.app p)) ((free R).map (P.hom.app p)) ((free R).map ((dbl.inl P).app p))
      ((free R).map ((dbl.inr P).app p)) :=
  ((evaluation _ _).obj p ⋙ free R).map_isPushout (IsPushout.of_hasPushout P.hom P.hom)

theorem chains_zero {j : ℤ} (hj : ¬ ∃ p : ℕ, j = -(p : ℤ)) (X : Spc) : IsZero (((chains R).obj X).X j) :=
  ((chainsN R).obj X).isZero_extend_X ComplexShape.embeddingDownNat j (fun i hi => hj ⟨i, hi.symm⟩)

theorem cok_zero {A B : Cx R} (g : A ⟶ B) (j : ℤ) (hB : IsZero (B.X j)) : IsZero ((cokernel g).X j) :=
  (IsZero.of_epi (cokernel.π (g.f j)) hB).of_iso (PreservesCokernel.iso (HomologicalComplex.eval _ _ j) g)

end Main

theorem LeafExcDeg_of : LeafExcDeg := by
  intro q P' P φ h
  have key : ∀ j, IsIso ((cokC q φ).f j) := by
    intro j
    by_cases hj : ∃ p : ℕ, j = -(p : ℤ)
    · obtain ⟨p, rfl⟩ := hj
      show IsIso ((HomologicalComplex.eval _ _ _).map (cokC q φ))
      refine cokF (HomologicalComplex.eval _ _ (-(p : ℤ))) _ _ _ _ (chainsInrSq q φ) ?_
      refine cokNat (chains (ZMod q) ⋙ HomologicalComplex.eval _ _ (-(p : ℤ))) _ (chIso (ZMod q) p)
        (dbl.inr P') (dbl.inr P) φ.right (dbl.map φ) (dbl.inr_map φ) ?_
      exact cokPO_transfer _ _ _ (hPO (ZMod q) P' _) _ _ _ (hPO (ZMod q) P _) _ _ _ (freeSq _ φ _)
        (by
          show (free (ZMod q)).map (NatTrans.app (dbl.inl P') (op (SimplexCategory.mk p))) ≫
            (free (ZMod q)).map (NatTrans.app (dbl.map φ) (op (SimplexCategory.mk p))) = _
          rw [← Functor.map_comp, ← NatTrans.comp_app, dbl.inl_map', NatTrans.comp_app, Functor.map_comp])
        (by
          show (free (ZMod q)).map (NatTrans.app (dbl.inr P') (op (SimplexCategory.mk p))) ≫
            (free (ZMod q)).map (NatTrans.app (dbl.map φ) (op (SimplexCategory.mk p))) = _
          rw [← Functor.map_comp, ← NatTrans.comp_app, dbl.inr_map, NatTrans.comp_app, Functor.map_comp]) (h _)
    · exact isIso_of_source_target_iso_zero _ (cok_zero _ _ j (chains_zero _ hj _)).isoZero
        (cok_zero _ _ j (chains_zero _ hj _)).isoZero
  exact HomologicalComplex.Hom.isIso_of_components _

end LateralTheory.CohomologicalPurity
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.Thom

theorem pull_cast {q : ℕ} {E E' : Spc} (f : E ⟶ E') {n i n' i' : ℤ} (h1 : n = n') (h2 : i = i')
    (a : Ht q E' n i) :
    pull _ f (tw q i') n' (Ht.cast h1 h2 a) = Ht.cast h1 h2 (pull _ f (tw q i) n a) := by
  subst h1; subst h2; rfl

theorem pull_cpow (h : DivisorNaturality) (q : ℕ) [NeZero q] {E E' : Spc} (f : E ⟶ E') (hI : Inv q E') (x : Ht q E' 2 1) :
    ∀ k : ℕ, pull _ f (tw q k) (2 * k) (cpow q x k) = cpow q (pull _ f (tw q 1) 2 x) k
  | 0 => by
    rw [cpow_zero, cpow_zero, pull_cast, (h q).2.1 f hI]
  | k + 1 => by
    rw [cpow_succ, cpow_succ, pull_cast, (h q).1, pull_cpow h q f hI x k]

theorem hyp_pull (h : DivisorNaturality) (q : ℕ) [NeZero q] (d : ℕ) (R : Type) [CommRing R] (hI : Inv q (PR (d + 1) 0 R)) :
    pull _ (pr d R).hom (tw q 1) 2 (hyp q (d + 1) 0 R) = hyp q (d + 1) 1 R := by
  change pull _ (prod.map (Pj.incl (d + 1)) (𝟙 (sp R)) : PR (d + 1) 1 R ⟶ PR (d + 1) 0 R) (tw q 1) 2
    (c1 q (prod.fst ≫ Pj.line (d + 1) 0)) = c1 q (prod.fst ≫ Pj.line (d + 1) 1)
  rw [(h q).2.2.1 _ _ hI, prod.map_fst_assoc, Pj.incl_line]

theorem tauRes_unit (H : Hyp) (hG : LeafGeo) (q : ℕ) [NeZero q] (d : ℕ) (R : Type) [CommRing R]
    (hq : IsUnit (q : R)) (m : ℕ) (n i : ℤ) a :
    pull _ (pr d R).hom (tw q i) n (poly q (d + 1) 0 R m n i a) = poly q (d + 1) 1 R m n i a := by
  have h6 : DivisorNaturality := H.2.2.2.2.1
  have hI := hG.2.1 q (d + 1) 0 R hq
  change pull _ (prod.map (Pj.incl (d + 1)) (𝟙 (sp R)) : PR (d + 1) 1 R ⟶ PR (d + 1) 0 R) (tw q i) n
    (poly q (d + 1) 0 R m n i a) = _
  unfold poly

  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [pull_cast, (h6 q).1, pull_cpow h6 q _ hI, ← pull_comp, prod.map_snd, Category.comp_id]
  congr 3
  exact hyp_pull h6 q d R hI

theorem LeafTau_ofU (hBd : LeafBd) (hG : LeafGeo) (hPB : LeafPB) (hTl : LeafTail)
    (hU : LeafTauU) (hT : LeafTauTop) : LeafTau := by
  have hL := tauLin
  have hF := tauFgt
  intro H q _ d R _ hq
  have hR' := tauRes_unit H hG q d R hq
  obtain ⟨δ, hδ, -, -⟩ := hBd
  have hm : Mono (pr d R).hom := hG.1 d R
  have h6 : DivisorNaturality := H.2.2.2.2.1
  have hUb := hU hPB hTl H q d R hq
  have hPB' := hPB H.1 h6 H.2.2.2.2.2.2.2.2.2.2.1 q (d + 1) R hq
  have hpoly0 := poly_zero hL
  have hres0 : ∀ n i (σ : Hs q (pr d R) n i), pull _ (pr d R).hom (tw q i) n (Hs.fgt q _ n i σ) = 0 :=
    fun n i σ => ((hδ q _ hm n i).1 _).2 ⟨σ, rfl⟩
  have hinj : ∀ n i, Function.Injective (Hs.fgt q (pr d R) n i) := by
    intro N i
    obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by ring⟩
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro σ hσ
    obtain ⟨u, rfl⟩ := ((hδ q _ hm n i).2.2 σ).1 hσ
    obtain ⟨a, ha⟩ := (hUb n i).2 u
    exact ((hδ q _ hm n i).2.1 u).2 ⟨poly q (d + 1) 0 R d n i a, (hR' d n i a).trans ha⟩
  refine ⟨?_, ?_⟩
  · obtain ⟨b, hb⟩ := (hUb (2 * d) d).2 (pull _ (pr d R).hom (tw q d) _ (cpow q (hyp q (d + 1) 0 R) d))
    have hy : pull _ (pr d R).hom (tw q d) _
        (cpow q (hyp q (d + 1) 0 R) d + poly q (d + 1) 0 R d (2 * d) d (0 - b)) = 0 := by
      refine (map_add _ _ _).trans ?_
      rw [hR' d (2 * d) d (0 - b), hL, hpoly0, zero_sub, ← hb]
      exact add_neg_cancel _
    obtain ⟨τ, hτ⟩ := ((hδ q _ hm _ _).1 _).1 hy
    refine ⟨τ, ⟨0 - b, hτ⟩, ?_⟩
    rintro τ' ⟨a', ha'⟩
    have e1 := hres0 _ _ τ'
    rw [ha'] at e1
    have e2 := (map_add (pull _ (pr d R).hom (tw q d) (2 * d)) _ _).symm.trans e1
    rw [hR' d (2 * d) d a'] at e2
    have hab : a' = 0 - b := (hUb _ _).1 (by
      rw [hL, hpoly0, zero_sub, hb]
      exact eq_neg_iff_add_eq_zero.mpr ((add_comm _ _).trans e2))
    apply hinj
    rw [ha', hτ, hab]
  · rintro τ ⟨a, ha⟩ n i
    constructor
    · intro x y hxy
      obtain ⟨ex, hex, hex'⟩ := hT H q d R n i x a
      obtain ⟨ey, hey, hey'⟩ := hT H q d R n i y a
      have h1 := congrArg (Hs.fgt q (pr d R) (n + 2 * d) (i + d)) hxy
      dsimp only at h1
      have fx := hF h6 q (pr d R) n (2 * d) i d (pull _ (prod.snd : PR (d + 1) 0 R ⟶ sp R) (tw q i) n x) τ
      have fy := hF h6 q (pr d R) n (2 * d) i d (pull _ (prod.snd : PR (d + 1) 0 R ⟶ sp R) (tw q i) n y) τ
      rw [ha] at fx fy
      replace h1 := hex'.symm.trans (fx.symm.trans (h1.trans (fy.trans hey')))
      have h2 := congrFun ((hPB' _ _).1 h1) (Fin.last d)
      rw [hex, hey] at h2
      exact cast_inj _ _ h2
    · intro σ
      obtain ⟨c, hc⟩ := (hPB' (n + 2 * d) (i + d)).2 (Hs.fgt q (pr d R) (n + 2 * d) (i + d) σ)
      have k1 : n + 2 * (d : ℤ) - 2 * (((Fin.last d : Fin (d + 1)) : ℕ) : ℤ) = n := by
        simp only [Fin.val_last]; ring
      have k2 : i + (d : ℤ) - (((Fin.last d : Fin (d + 1)) : ℕ) : ℤ) = i := by
        simp only [Fin.val_last]; ring
      refine ⟨Ht.cast k1 k2 (c (Fin.last d)), ?_⟩
      obtain ⟨e, he, he'⟩ := hT H q d R n i (Ht.cast k1 k2 (c (Fin.last d))) a
      have hlast : (e - c) (Fin.last d) = 0 := by
        rw [Pi.sub_apply, he, cast_cast, sub_self]
      have hsnoc : poly q (d + 1) 0 R (d + 1) (n + 2 * d) (i + d) (e - c) =
          poly q (d + 1) 0 R d (n + 2 * d) (i + d) (fun j : Fin d => (e - c) j.castSucc) := by
        unfold poly
        rw [Fin.sum_univ_castSucc, hlast]
        simp only [map_zero, AddMonoidHom.zero_apply, cast_zero, add_zero]
        rfl
      have hd : poly q (d + 1) 0 R (d + 1) (n + 2 * d) (i + d) (e - c) =
          Hs.fgt q (pr d R) (n + 2 * d) (i + d) (Hs.act q (P := pr d R) (pull _ (prod.snd : PR (d + 1) 0 R ⟶ sp R) _ _
            (Ht.cast k1 k2 (c (Fin.last d)))) τ - σ) := by
        have hfx := hF h6 q (pr d R) n (2 * d) i d
          (pull _ (prod.snd : PR (d + 1) 0 R ⟶ sp R) (tw q i) n (Ht.cast k1 k2 (c (Fin.last d)))) τ
        rw [ha] at hfx
        rw [hL, map_sub, hc]
        exact congrArg (fun t : Ht q (pr d R).right (n + 2 * d) (i + d) => t - Hs.fgt q (pr d R) (n + 2 * d) (i + d) σ)
          (he'.symm.trans hfx.symm)
      have hg : (fun j : Fin d => (e - c) j.castSucc) = 0 := (hUb _ _).1 (by
        rw [hpoly0, ← hR', ← hsnoc, hd]
        exact hres0 _ _ _)
      rw [hg, hpoly0] at hsnoc
      rw [hsnoc] at hd
      replace hd := hd.symm
      rw [map_sub] at hd
      exact hinj _ _ (sub_eq_zero.mp hd)

end LateralTheory.CohomologicalPurity.Thom
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.Thom

theorem tt_cast_cast {q : ℕ} {E : Spc} {n i n' i' n'' i'' : ℤ} (h1 : n = n') (h2 : i = i') (h3 : n' = n'')
    (h4 : i' = i'') (a : Ht q E n i) : Ht.cast h3 h4 (Ht.cast h1 h2 a) = Ht.cast (h1.trans h3) (h2.trans h4) a := by
  subst h1; subst h2; subst h3; subst h4; rfl

theorem tt_pull_cast {q : ℕ} {E E' : Spc} (f : E ⟶ E') {n i n' i' : ℤ} (h1 : n = n') (h2 : i = i')
    (a : Ht q E' n i) : pull _ f _ _ (Ht.cast h1 h2 a) = Ht.cast h1 h2 (pull _ f _ _ a) := by
  subst h1; subst h2; rfl

theorem tt_cup_cast_right {q : ℕ} {E : Spc} {n i m j m' j' : ℤ} (h1 : m = m') (h2 : j = j') (a : Ht q E n i)
    (b : Ht q E m j) : cup q a (Ht.cast h1 h2 b) = Ht.cast (by rw [h1]) (by rw [h2]) (cup q a b) := by
  subst h1; subst h2; rfl

theorem tt_cup_cast_left {q : ℕ} {E : Spc} {n i m j n' i' : ℤ} (h1 : n = n') (h2 : i = i') (a : Ht q E n i)
    (b : Ht q E m j) : cup q (Ht.cast h1 h2 a) b = Ht.cast (by rw [h1]) (by rw [h2]) (cup q a b) := by
  subst h1; subst h2; rfl

theorem tauTop : LeafTauTop := by
  intro H q _ d R _ n i x a
  have h6 : DivisorNaturality := H.2.2.2.2.1
  have hr : DivisorRingCompatibility := H.2.2.2.2.2.1
  let e : ∀ j : Fin (d + 1), Ht q (sp R) (n + 2 * (d : ℤ) - 2 * ((j : ℕ) : ℤ)) (i + (d : ℤ) - ((j : ℕ) : ℤ)) :=
    Fin.lastCases (motive := fun j : Fin (d + 1) =>
        Ht q (sp R) (n + 2 * (d : ℤ) - 2 * ((j : ℕ) : ℤ)) (i + (d : ℤ) - ((j : ℕ) : ℤ)))
      (x.cast (by simp) (by simp))
      (fun j => (cup q x (a j)).cast (by simp only [Fin.val_castSucc]; ring) (by simp only [Fin.val_castSucc]; ring))
  refine ⟨e, by simp [e], ?_⟩
  have he : ∀ j : Fin d, e j.castSucc = (cup q x (a j)).cast (by simp only [Fin.val_castSucc]; ring)
      (by simp only [Fin.val_castSucc]; ring) := fun j => by simp [e]
  have hl : e (Fin.last d) = x.cast (by simp) (by simp) := by simp [e]
  unfold poly

  rw [map_add (f := _), map_sum, Fin.sum_univ_castSucc]
  refine (add_comm _ _).trans ?_
  congr 1
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [he, tt_pull_cast, tt_cup_cast_left, (h6 q).1, (hr q _).2.1, tt_cup_cast_right]
    repeat rw [tt_cast_cast]
    rfl
  · rw [hl, tt_pull_cast, tt_cup_cast_left]
    repeat rw [tt_cast_cast]
    rfl

theorem LeafTauTop_of : LeafTauTop := tauTop

end LateralTheory.CohomologicalPurity.Thom
end
end

section

noncomputable section
open CategoryTheory Limits Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.Thom.ExcSp

def LeafFreePb : Prop := ∀ (R : Type) [CommRing R] {A' A B' B : PSh} (t : A' ⟶ B') (l : A' ⟶ A) (r : B' ⟶ B)
  (b : A ⟶ B), IsPullback t l r b → Mono r → Mono b →
  IsPullback ((free R).map t) ((free R).map l) ((free R).map r) ((free R).map b)

theorem isIso_cokernel_map_of_pb_epi {C : Type*} [Category C] [Abelian C] {X₁ X₂ X₃ X₄ : C}
    {t : X₁ ⟶ X₂} {l : X₁ ⟶ X₃} {r : X₂ ⟶ X₄} {b : X₃ ⟶ X₄} (sq : IsPullback t l r b)
    (he : Epi (biprod.desc r b)) : IsIso (cokernel.map t b l r sq.w.symm) := by
  have := Abelian.mono_cokernel_map_of_isPullback sq
  have : Epi (cokernel.map t b l r sq.w.symm) := by
    have h1 : biprod.desc r b ≫ cokernel.π b = (biprod.fst : X₂ ⊞ X₃ ⟶ X₂) ≫ (r ≫ cokernel.π b) := by
      ext <;> simp
    have h3 : Epi (r ≫ cokernel.π b) := by
      have : Epi ((biprod.fst : X₂ ⊞ X₃ ⟶ X₂) ≫ (r ≫ cokernel.π b)) := by rw [← h1]; infer_instance
      exact epi_of_epi (biprod.fst : X₂ ⊞ X₃ ⟶ X₂) _
    have h2 : cokernel.π t ≫ cokernel.map t b l r sq.w.symm = r ≫ cokernel.π b := by simp
    rw [← h2] at h3
    exact epi_of_epi (cokernel.π t) _
  exact isIso_of_mono_of_epi _

theorem transport_sq {C : Type*} [Category C] [Abelian C] {X₁ X₂ X₃ X₄ Y₁ Y₂ Y₃ Y₄ : C}
    {t : X₁ ⟶ X₂} {l : X₁ ⟶ X₃} {r : X₂ ⟶ X₄} {b : X₃ ⟶ X₄}
    {t' : Y₁ ⟶ Y₂} {l' : Y₁ ⟶ Y₃} {r' : Y₂ ⟶ Y₄} {b' : Y₃ ⟶ Y₄}
    (e₁ : X₁ ≅ Y₁) (e₂ : X₂ ≅ Y₂) (e₃ : X₃ ≅ Y₃) (e₄ : X₄ ≅ Y₄)
    (ht : t = e₁.hom ≫ t' ≫ e₂.inv) (hl : l = e₁.hom ≫ l' ≫ e₃.inv)
    (hr : r = e₂.hom ≫ r' ≫ e₄.inv) (hb : b = e₃.hom ≫ b' ≫ e₄.inv)
    (sq : IsPullback t' l' r' b') (he : Epi (biprod.desc r' b')) :
    IsPullback t l r b ∧ Epi (biprod.desc r b) := by
  subst ht hl hr hb
  refine ⟨sq.of_iso e₁.symm e₂.symm e₃.symm e₄.symm (by simp) (by simp) (by simp) (by simp), ?_⟩
  have : biprod.desc (e₂.hom ≫ r' ≫ e₄.inv) (e₃.hom ≫ b' ≫ e₄.inv) =
      (biprod.mapIso e₂ e₃).hom ≫ biprod.desc r' b' ≫ e₄.inv := by
    ext <;> simp
  rw [this]
  infer_instance

theorem leafCokIso_of (hF : LeafFreePb) : LeafCokIso := by
  intro q P' P φ hpb hc n
  by_cases hn : ∃ p : ℕ, -(p : ℤ) = n
  · obtain ⟨p, rfl⟩ := hn
    have h : ComplexShape.embeddingDownNat.f p = -(p : ℤ) := rfl
    have key : ∀ {E' E : Spc} (f : E' ⟶ E), ((chains (ZMod q)).map f).f (-(p : ℤ)) =
        (HomologicalComplex.extendXIso _ _ h).hom ≫ (free (ZMod q)).map (f.app (op (SimplexCategory.mk p))) ≫
          (HomologicalComplex.extendXIso _ _ h).inv := by
      intro E' E f
      change (HomologicalComplex.extendMap ((chainsN (ZMod q)).map f) _).f _ = _
      rw [HomologicalComplex.extendMap_f _ _ h]
      rfl
    have hpb' : IsPullback (P'.hom.app (op (SimplexCategory.mk p))) (φ.left.app (op (SimplexCategory.mk p)))
        (φ.right.app (op (SimplexCategory.mk p))) (P.hom.app (op (SimplexCategory.mk p))) :=
      hpb.map ((evaluation _ _).obj (op (SimplexCategory.mk p)))
    have mr : Mono (φ.right.app (op (SimplexCategory.mk p))) := by
      have := hc.1; rw [NatTrans.mono_iff_mono_app] at this; exact this _
    have mb : Mono (P.hom.app (op (SimplexCategory.mk p))) := by
      have := hc.2.1; rw [NatTrans.mono_iff_mono_app] at this; exact this _
    obtain ⟨h1, h2⟩ := transport_sq _ _ _ _ (key P'.hom) (key φ.left) (key φ.right) (key P.hom)
      (hF (ZMod q) _ _ _ _ hpb' mr mb) (hc.2.2 _)
    exact isIso_cokernel_map_of_pb_epi h1 h2
  · push Not at hn
    have hz : ∀ E : Spc, IsZero (((chains (ZMod q)).obj E).X n) := fun E =>
      HomologicalComplex.isZero_extend_X _ _ _ (fun i => hn i)
    have hA : IsZero (cokernel ((chains (ZMod q)).map P'.hom |>.f n)) :=
      IsZero.of_epi (cokernel.π _) (hz _)
    have hB : IsZero (cokernel ((chains (ZMod q)).map P.hom |>.f n)) :=
      IsZero.of_epi (cokernel.π _) (hz _)
    exact ⟨0, hA.eq_of_src _ _, hB.eq_of_src _ _⟩

end LateralTheory.CohomologicalPurity.Thom.ExcSp
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.Cl.Flq

theorem sec_eq_zero_of_isZero {R : Type} [CommRing R] {G : Shv R} {X : Scheme.{0}} (hG : IsZero G) (a : Sec G X) :
    a = 0 := by
  have h1 : Sec.map (𝟙 G) a = a := rfl
  have h2 : Sec.map (0 : G ⟶ G) a = 0 := rfl
  rw [← h1, hG.eq_of_src (𝟙 G) 0, h2]

theorem LeafZero_of : LeafZero := by
  intro R _ K X U n hz
  refine ⟨?_, ?_, ?_⟩
  · intro V W h a _
    rw [sec_eq_zero_of_isZero hz (rs h a)]
    exact zero_mem _
  · intro W a _
    rw [sec_eq_zero_of_isZero hz a]
    exact zero_mem _
  · intro V W h a _
    exact ⟨0, zero_mem _, (sec_eq_zero_of_isZero hz _).trans (sec_eq_zero_of_isZero hz a).symm⟩

end LateralTheory.CohomologicalPurity.Cl.Flq
end
end
