module

public import Development.EtaleCohomology.CohomologicalPurity.Bundle008
import Development.EtaleCohomology.CohomologicalPurity.Bundle021
public import Development.EtaleCohomology.CohomologicalPurity.Bundle012
public import Development.EtaleCohomology.CohomologicalPurity.Bundle022
public import Development.EtaleCohomology.CohomologicalPurity.Bundle014
public import Development.EtaleCohomology.CohomologicalPurity.Bundle024
public import Development.EtaleCohomology.CohomologicalPurity.Bundle019
public import Mathlib.Order.CompletePartialOrder
public import Development.EtaleCohomology.CohomologicalPurity.Bundle025
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
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
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.TotallySplit
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

@[expose] public section

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity

theorem opnMap_tri {X'' X' X : Scheme.{0}} {g : X'' ⟶ X} (a : X'' ⟶ X') (b : X' ⟶ X) (e : g = a ≫ b)
    (U'' : X''.Opens) (U' : X'.Opens) (U : X.Opens) (h : U'' ≤ g ⁻¹ᵁ U) (h1 : U'' ≤ a ⁻¹ᵁ U') (h2 : U' ≤ b ⁻¹ᵁ U) :
    opnMap g U'' U h = opnMap a U'' U' h1 ≫ opnMap b U' U h2 := by
  subst e; exact opnMap_comp _ _ _ _ _ h1 h2 h

theorem fgt_pull (q : ℕ) {P' P : Arrow Spc} (φ : P' ⟶ P) (n i : ℤ) (x : Hs q P n i) :
    Hs.fgt q P' n i (Hs.pull q φ n i x) = pull _ φ.right (tw q i) n (Hs.fgt q P n i x) := by
  change pull _ (dbl.inl P') _ n (pull _ (dbl.map φ) _ n x.1) = pull _ φ.right _ n (pull _ (dbl.inl P) _ n x.1)
  rw [← pull_comp, ← pull_comp, dbl.inl_map']

theorem res_pull (q : ℕ) {P' P : Arrow Spc} (φ : P' ⟶ P) (n i : ℤ) (y : Ht q P.right n i) :
    pull _ P'.hom (tw q i) n (pull _ φ.right (tw q i) n y) = pull _ φ.left (tw q i) n (pull _ P.hom (tw q i) n y) := by
  rw [← pull_comp, ← pull_comp, ← Arrow.w φ]

theorem pull_left_comp (q : ℕ) {P'' P' P : Arrow Spc} (φ : P'' ⟶ P') (ψ : P' ⟶ P) (n i : ℤ) (y : Ht q P.left n i) :
    pull _ (φ ≫ ψ).left (tw q i) n y = pull _ φ.left (tw q i) n (pull _ ψ.left (tw q i) n y) := by
  rw [Arrow.comp_left, pull_comp]

theorem pull_right_comp (q : ℕ) {P'' P' P : Arrow Spc} (φ : P'' ⟶ P') (ψ : P' ⟶ P) (n i : ℤ) (y : Ht q P.right n i) :
    pull _ (φ ≫ ψ).right (tw q i) n y = pull _ φ.right (tw q i) n (pull _ ψ.right (tw q i) n y) := by
  rw [Arrow.comp_right, pull_comp]

theorem leafHsFive : LeafHsFive := by
  intro a1 b1 hBd q A B _ _ φ I hq J _ _ D s t hc he i hO n
  obtain ⟨δ, hδ⟩ := hBd
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by ring⟩
  have hqB : IsUnit (q : B) := by simpa using hq.map φ
  have hqj : ∀ j, IsUnit (q : D.obj j) := fun j => by simpa using hq.map (s.app j).hom
  have hsn : ∀ {j k : J} (f : j ⟶ k), s.app k = s.app j ≫ D.map f := fun f => by simpa using s.naturality f
  have htn : ∀ {j k : J} (f : j ⟶ k), D.map f ≫ t.app k = t.app j := fun f => by simpa using t.naturality f
  have hD : ∀ {j k : J} (f : j ⟶ k), off (D.obj k) (I.map (s.app k).hom) ≤
      Spec.map (D.map f) ⁻¹ᵁ off (D.obj j) (I.map (s.app j).hom) := by
    intro j k f
    have e1 := off_map (s.app k).hom I
    have e2 := off_map (s.app j).hom I
    simp only [CommRingCat.ofHom_hom] at e1 e2
    rw [e1, e2, hsn f, Spec.map_comp]
    intro x hx; exact hx
  have hT : ∀ j, off B (I.map φ) ≤ Spec.map (t.app j) ⁻¹ᵁ off (D.obj j) (I.map (s.app j).hom) := by
    intro j
    have e1 := off_map φ I
    have e2 := off_map (s.app j).hom I
    simp only [CommRingCat.ofHom_hom] at e2
    rw [e1, e2, ← he j, Spec.map_comp]
    intro x hx; exact hx
  have eT : ∀ {j k : J} (f : j ⟶ k), Spec.map (t.app j) = Spec.map (t.app k) ≫ Spec.map (D.map f) := fun f => by
    rw [← Spec.map_comp, htn f]
  have eD : ∀ {j k l : J} (f : j ⟶ k) (g : k ⟶ l), Spec.map (D.map (f ≫ g)) = Spec.map (D.map g) ≫ Spec.map (D.map f) :=
    fun f g => by rw [← Spec.map_comp, ← Functor.map_comp]
  have sc : ∀ k : ℤ, (∀ x : Ht q (opn (off B (I.map φ))).right k i, ∃ j, ∃ y : Ht q (opn (off (D.obj j) (I.map (s.app j).hom))).right k i,
      pull _ (opnMap (Spec.map (t.app j)) _ _ (hT j)).right (tw q i) k y = x) ∧
      ∀ j (y : Ht q (opn (off (D.obj j) (I.map (s.app j).hom))).right k i),
        pull _ (opnMap (Spec.map (t.app j)) _ _ (hT j)).right (tw q i) k y = 0 →
        ∃ (l : J) (f : j ⟶ l), pull _ (opnMap (Spec.map (D.map f)) _ _ (hD f)).right (tw q i) k y = 0 :=
    fun k => spec_cont b1 q D t hc hqB hqj k i
  have ex := fun {X : Scheme.{0}} (V : X.Opens) (k : ℤ) => hδ.1 q (opn V) (opn_mono V) k i
  constructor
  · intro x
    obtain ⟨j1, y1, hy1'⟩ := (sc (m + 1)).1 (Hs.fgt q _ (m + 1) i x)
    have h2 : pull _ (opnMap (Spec.map (t.app j1)) _ _ (hT j1)).left (tw q i) (m + 1)
        (pull _ (opn (off (D.obj j1) (I.map (s.app j1).hom))).hom (tw q i) (m + 1) y1) = 0 := by
      rw [← res_pull, hy1']
      exact (ex _ (m + 1)).1.apply_apply_eq_zero x
    obtain ⟨k, f, h', hk⟩ := (hO (m + 1)).2 j1 (hT j1) _ h2
    have h3 : pull _ (opn (off (D.obj k) (I.map (s.app k).hom))).hom (tw q i) (m + 1)
        (pull _ (opnMap (Spec.map (D.map f)) _ _ h').right (tw q i) (m + 1) y1) = 0 := by
      rw [res_pull]; exact hk
    obtain ⟨z, hz⟩ := ((ex (off (D.obj k) (I.map (s.app k).hom)) (m + 1)).1 _).1 h3
    have h4 : Hs.fgt q _ (m + 1) i (x - Hs.pull q (opnMap (Spec.map (t.app k)) _ _ (hT k)) (m + 1) i z) = 0 := by
      rw [map_sub, fgt_pull, hz, ← pull_right_comp,
        ← opnMap_tri (Spec.map (t.app k)) (Spec.map (D.map f)) (eT f) _ _ _ (hT j1) (hT k) h', hy1', sub_self]
    obtain ⟨w, hw⟩ := ((ex (off B (I.map φ)) m).2.2 _).1 h4
    obtain ⟨j2, h2', w2, hw2⟩ := (hO m).1 w
    refine ⟨IsFiltered.max k j2, hT _,
      Hs.pull q (opnMap (Spec.map (D.map (IsFiltered.leftToMax k j2))) _ _ (hD _)) (m + 1) i z +
      δ q _ m i (pull _ (opnMap (Spec.map (D.map (IsFiltered.rightToMax k j2))) _ _ (hD _)).left (tw q i) m w2), ?_⟩
    rw [map_add (f := _), ← Hs.pull_comp',
      ← opnMap_tri (Spec.map (t.app _)) (Spec.map (D.map (IsFiltered.leftToMax k j2))) (eT _) _ _ _ (hT k) (hT _) (hD _),
      hδ.2.1 q _ _ _ (opn_mono _) (opn_mono _), ← pull_left_comp,
      ← opnMap_tri (Spec.map (t.app _)) (Spec.map (D.map (IsFiltered.rightToMax k j2))) (eT _) _ _ _ h2' (hT _) (hD _),
      hw2, hw]
    abel
  · intro j h y hy
    have hf : pull _ (opnMap (Spec.map (t.app j)) _ _ h).right (tw q i) (m + 1) (Hs.fgt q _ (m + 1) i y) = 0 := by
      rw [← fgt_pull, hy, map_zero]
    obtain ⟨k, f, hk⟩ := (sc (m + 1)).2 j _ (by exact hf)
    have h5 : Hs.fgt q _ (m + 1) i (Hs.pull q (opnMap (Spec.map (D.map f)) _ _ (hD f)) (m + 1) i y) = 0 := by
      rw [fgt_pull]; exact hk
    obtain ⟨w, hw⟩ := ((ex (off (D.obj k) (I.map (s.app k).hom)) m).2.2 _).1 h5
    have h6 : δ q _ m i (pull _ (opnMap (Spec.map (t.app k)) _ _ (hT k)).left (tw q i) m w) = 0 := by
      rw [← hδ.2.1 q _ _ (opnMap (Spec.map (t.app k)) _ _ (hT k)) (opn_mono _) (opn_mono _), hw, ← Hs.pull_comp',
        ← opnMap_tri (Spec.map (t.app k)) (Spec.map (D.map f)) (eT f) _ _ _ h (hT k) (hD f), hy]
    obtain ⟨v, hv⟩ := ((ex (off B (I.map φ)) m).2.1 _).1 h6
    obtain ⟨j3, v3, hv3'⟩ := (sc m).1 v
    have h7 : pull _ (opnMap (Spec.map (t.app (IsFiltered.max k j3))) _ _ (hT _)).left (tw q i) m
        (pull _ (opnMap (Spec.map (D.map (IsFiltered.leftToMax k j3))) _ _ (hD _)).left (tw q i) m w -
          pull _ (opn (off (D.obj (IsFiltered.max k j3)) (I.map (s.app _).hom))).hom (tw q i) m
            (pull _ (opnMap (Spec.map (D.map (IsFiltered.rightToMax k j3))) _ _ (hD _)).right (tw q i) m v3)) = 0 := by
      rw [map_sub, sub_eq_zero, ← pull_left_comp,
        ← opnMap_tri (Spec.map (t.app _)) (Spec.map (D.map (IsFiltered.leftToMax k j3))) (eT _) _ _ _ (hT k) (hT _) (hD _),
        ← res_pull, ← pull_right_comp,
        ← opnMap_tri (Spec.map (t.app _)) (Spec.map (D.map (IsFiltered.rightToMax k j3))) (eT _) _ _ _ (hT j3) (hT _) (hD _),
        hv3', hv]
    obtain ⟨r, g, h8, hr⟩ := (hO m).2 _ (hT _) _ h7
    refine ⟨r, f ≫ IsFiltered.leftToMax k j3 ≫ g, hD _, ?_⟩
    rw [map_sub, sub_eq_zero] at hr
    rw [opnMap_tri (Spec.map (D.map (IsFiltered.leftToMax k j3 ≫ g))) (Spec.map (D.map f)) (eD _ _) _ _ _ _ (hD _) (hD f),
      Hs.pull_comp', ← hw,
      opnMap_tri (Spec.map (D.map g)) (Spec.map (D.map (IsFiltered.leftToMax k j3))) (eD _ _) _ _ _ _ h8 (hD _),
      Hs.pull_comp', hδ.2.1 q _ _ _ (opn_mono _) (opn_mono _), hδ.2.1 q _ _ _ (opn_mono _) (opn_mono _), hr,
      ← res_pull]
    exact (ex _ m).2.1.apply_apply_eq_zero _

theorem leafHsCont_of' (hB : LeafBd) (hE : LeafExc) (hO : LeafOffCont) : LeafHsCont :=
  leafHsCont_of hB hE hO leafHsFive

end LateralTheory.CohomologicalPurity
end
end

section

noncomputable section
open CategoryTheory Limits Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.Thom.ExcSp

theorem free_mono (R : Type) [CommRing R] {A B : PSh} (g : A ⟶ B) [Mono g] : Mono ((free R).map g) := by
  have : Mono ((freeP R).map g) := by
    rw [NatTrans.mono_iff_mono_app]
    intro U
    have hg : Function.Injective (g.app U) := (mono_iff_injective _).1 (inferInstance)
    rw [ModuleCat.mono_iff_injective]
    change Function.Injective ((ModuleCat.free (ULift.{1} R)).map (uliftFunctor.{1}.map (g.app U))).hom
    have hu : Function.Injective (uliftFunctor.{1}.map (g.app U)) := by
      intro a b h
      exact ULift.ext (hg (congrArg ULift.down h))
    exact Finsupp.mapDomain_injective hu
  change Mono ((presheafToSheaf _ _).map ((freeP R).map g))
  infer_instance

theorem leafChainsMono : LeafChainsMono := by
  intro R _ E' E f hf n
  by_cases hn : ∃ p : ℕ, -(p : ℤ) = n
  · obtain ⟨p, rfl⟩ := hn
    have h : ComplexShape.embeddingDownNat.f p = -(p : ℤ) := rfl
    change Mono ((HomologicalComplex.extendMap ((chainsN R).map f) _).f _)
    rw [HomologicalComplex.extendMap_f _ _ h]
    have : Mono (f.app (op (SimplexCategory.mk p))) := by
      rw [NatTrans.mono_iff_mono_app] at hf
      exact hf _
    have : Mono (((chainsN R).map f).f p) := by
      change Mono ((AlgebraicTopology.AlternatingFaceMapComplex.map _).f p)
      rw [AlgebraicTopology.AlternatingFaceMapComplex.map_f]
      exact free_mono R _
    infer_instance
  · push Not at hn
    refine ⟨fun g h _ => ?_⟩
    exact (HomologicalComplex.isZero_extend_X _ _ _ (fun i => hn i)).eq_of_tgt _ _

theorem etaleSplitExcision_of_cokernel_relative (hK : LeafCokIso) (hR : LeafHsRel) : LateralTheory.CohomologicalPurity.Thom.LeafExcSp :=
  etaleSplitExcision_of_mono_cokernel_relative leafChainsMono hK hR

end LateralTheory.CohomologicalPurity.Thom.ExcSp
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex.HomComplex

namespace LateralTheory.CohomologicalPurity.Cl

def LeafResK : Prop := ∀ (q : ℕ) (i : ℤ),
  (∀ s, Injective ((res _ (tw q i)).X s)) ∧ ∀ s < 0, IsZero ((res _ (tw q i)).X s)

def LeafZcPull : Prop := ∀ {R : Type} [CommRing R] (K : Cx R) {X' X : Scheme.{0}} (f : X' ⟶ X) (U' : X'.Opens)
  (U : X.Opens), U' ≤ f ⁻¹ᵁ U → ∀ (n : ℤ) (a : Sec (K.X n) X), a ∈ Zc K U n → Sec.res f a ∈ Zc K U' n

def LeafZcIn : Prop := ∀ {R : Type} [CommRing R] (K : Cx R) {X : Scheme.{0}} (U W V : X.Opens) (h : V ≤ W), V ≤ U →
  ∀ (n : ℤ) (a : Sec (K.X n) W.toScheme), a ∈ Zc K (W.ι ⁻¹ᵁ U) n → rs h a = 0

private theorem sres_zero {R : Type} [CommRing R] {G : Shv R} {X Y : Scheme.{0}} (f : Y ⟶ X) :
    Sec.res f (0 : Sec G X) = 0 := by
  show (G.obj.map f.op).hom 0 = 0
  exact map_zero _

private theorem smap_zero {R : Type} [CommRing R] {G H : Shv R} (φ : G ⟶ H) {X : Scheme.{0}} :
    Sec.map φ (0 : Sec G X) = 0 := by
  show (φ.hom.app (op X)).hom 0 = 0
  exact map_zero _

private theorem Bd_zero {R : Type} [CommRing R] (K : Cx R) {X : Scheme.{0}} (U : X.Opens) (n : ℤ) : Bd K U n 0 :=
  ⟨0, sres_zero _, smap_zero _⟩

private theorem leι {X : Scheme.{0}} {V W : X.Opens} (h : V ≤ W) (U : X.Opens) :
    V.ι ⁻¹ᵁ U ≤ X.homOfLE h ⁻¹ᵁ (W.ι ⁻¹ᵁ U) :=
  le_of_comp _ _ U rfl _ (Scheme.homOfLE_ι _ _) le_rfl

private theorem descent_glue_of_residue_pullback_inclusion (hK : LeafResK) (hP : LeafZcPull) (hI : LeafZcIn) : LeafDescOGlue := by
  intro hD hF q X U m i hL A V s hcov H
  obtain ⟨cls, hon, hker, hnat⟩ := hD q m i
  have H1 : ∀ n < m, ∀ (W : X.Opens), ∀ a ∈ Zc (res _ (tw q i)) (W.ι ⁻¹ᵁ U) n, ∀ x ∈ W,
      ∃ (V : X.Opens) (h : V ≤ W), x ∈ V ∧ Bd (res _ (tw q i)) (V.ι ⁻¹ᵁ U) n (rs h a) := by
    intro n hn W a ha x hx
    by_cases hxU : x ∈ U
    · refine ⟨W ⊓ U, inf_le_left, ⟨hx, hxU⟩, ?_⟩
      rw [hI _ U W (W ⊓ U) _ inf_le_right n a ha]
      exact Bd_zero _ _ _
    · obtain ⟨V', hV'W, hxV', hsub⟩ := hL x W hx
      refine ⟨V', hV'W, hxV', ?_⟩
      obtain ⟨cn, -, hkern, -⟩ := hD q n i
      have hz := hP _ (X.homOfLE hV'W) (V'.ι ⁻¹ᵁ U) (W.ι ⁻¹ᵁ U) (leι hV'W U) n a ha
      have := hsub n hn
      exact (hkern (V'.ι ⁻¹ᵁ U) ⟨_, hz⟩).1 (Subsingleton.elim _ _)
  obtain ⟨-, hglue⟩ := hF _ (res _ (tw q i)) (hK q i).1 (hK q i).2 X U m H1
  choose l hl using fun a => hon ((V a).ι ⁻¹ᵁ U) (s a)
  let V' : Option A → X.Opens := fun o => Option.elim o U V
  let a' : ∀ k, Sec ((res _ (tw q i)).X m) (V' k).toScheme := fun
    | none => 0
    | some a => (l a).1
  have hmem : ∀ k, a' k ∈ Zc (res _ (tw q i)) ((V' k).ι ⁻¹ᵁ U) m := by
    rintro (_ | a)
    · exact zero_mem _
    · exact (l a).2
  have hcv : ∀ x : X, ∃ k, x ∈ V' k := by
    intro x
    by_cases hx : x ∈ U
    · exact ⟨none, hx⟩
    · obtain ⟨a, ha⟩ := hcov x hx
      exact ⟨some a, ha⟩
  have hcmp : ∀ k l', ∀ x ∈ V' k, x ∈ V' l' → ∃ (T : X.Opens) (hk : T ≤ V' k) (hl : T ≤ V' l'), x ∈ T ∧
      Bd (res _ (tw q i)) (T.ι ⁻¹ᵁ U) m (rs hk (a' k) - rs hl (a' l')) := by
    intro k l' x hk hl'
    by_cases hxU : x ∈ U
    · refine ⟨V' k ⊓ V' l' ⊓ U, inf_le_left.trans inf_le_left, inf_le_left.trans inf_le_right, ⟨⟨hk, hl'⟩, hxU⟩, ?_⟩
      rw [hI _ U (V' k) _ _ inf_le_right m (a' k) (hmem k), hI _ U (V' l') _ _ inf_le_right m (a' l') (hmem l'),
        sub_zero]
      exact Bd_zero _ _ _
    · rcases k with _ | a
      · exact absurd hk hxU
      rcases l' with _ | b
      · exact absurd hl' hxU
      obtain ⟨T, ha, hb, ha', hb', hxT, heq⟩ := H a b x hk hl' hxU
      refine ⟨T, ha, hb, hxT, ?_⟩
      have za := hP _ (X.homOfLE ha) (T.ι ⁻¹ᵁ U) ((V a).ι ⁻¹ᵁ U) ha' m (l a).1 (l a).2
      have zb := hP _ (X.homOfLE hb) (T.ι ⁻¹ᵁ U) ((V b).ι ⁻¹ᵁ U) hb' m (l b).1 (l b).2
      have e1 := hnat (X.homOfLE ha) (T.ι ⁻¹ᵁ U) ((V a).ι ⁻¹ᵁ U) ha' (l a) ⟨_, za⟩ rfl
      have e2 := hnat (X.homOfLE hb) (T.ι ⁻¹ᵁ U) ((V b).ι ⁻¹ᵁ U) hb' (l b) ⟨_, zb⟩ rfl
      rw [hl a] at e1
      rw [hl b] at e2
      have h0 : cls (T.ι ⁻¹ᵁ U) (⟨_, za⟩ - ⟨_, zb⟩) = 0 := by
        rw [map_sub, ← e1, ← e2, heq, sub_self]
      exact (hker _ _).1 h0
  obtain ⟨c, hc, hcb⟩ := hglue (Option A) V' a' hmem hcv hcmp
  refine ⟨cls U ⟨c, hc⟩, fun a => ?_⟩
  have zc := hP _ (V a).ι ((V a).ι ⁻¹ᵁ U) U le_rfl m c hc
  show Hs.pull q (opnMap (V a).ι ((V a).ι ⁻¹ᵁ U) U le_rfl) m i (cls U ⟨c, hc⟩) = s a
  rw [hnat (V a).ι ((V a).ι ⁻¹ᵁ U) U le_rfl ⟨c, hc⟩ ⟨_, zc⟩ rfl, ← hl a, ← sub_eq_zero, ← map_sub]
  exact (hker _ _).2 (hcb (some a))

private theorem sres_comp {R : Type} [CommRing R] {G : Shv R} {X Y Z : Scheme.{0}} (g : Z ⟶ Y) (f : Y ⟶ X) (a : Sec G X) :
    Sec.res g (Sec.res f a) = Sec.res (g ≫ f) a := by
  show (G.obj.map g.op).hom ((G.obj.map f.op).hom a) = (G.obj.map (g ≫ f).op).hom a
  rw [op_comp, Functor.map_comp]; rfl

private theorem sres_id {R : Type} [CommRing R] {G : Shv R} {X : Scheme.{0}} (a : Sec G X) : Sec.res (𝟙 X) a = a := by
  show (G.obj.map (𝟙 X).op).hom a = a
  rw [op_id, CategoryTheory.Functor.map_id]; rfl

private theorem smap_res {R : Type} [CommRing R] {G H : Shv R} (φ : G ⟶ H) {X Y : Scheme.{0}} (f : Y ⟶ X) (a : Sec G X) :
    Sec.map φ (Sec.res f a) = Sec.res f (Sec.map φ a) := by
  show (φ.hom.app (op Y)).hom ((G.obj.map f.op).hom a) = (H.obj.map f.op).hom ((φ.hom.app (op X)).hom a)
  have h := φ.hom.naturality f.op
  exact congrArg (fun t => t.hom a) h

private theorem LeafZcPull_pf : LeafZcPull := by
  intro R _ K X' X f U' U h n a ha
  obtain ⟨h1, h2⟩ := (mem_Zc a).1 ha
  refine (mem_Zc _).2 ⟨?_, ?_⟩
  · rw [sres_comp, ← Scheme.Hom.resLE_comp_ι f h, ← sres_comp, h1, sres_zero]
  · rw [smap_res, h2, sres_zero]

private theorem LeafZcIn_pf : LeafZcIn := by
  intro R _ K X U W V h hU n a ha
  obtain ⟨h1, -⟩ := (mem_Zc a).1 ha
  have e : (⊤ : V.toScheme.Opens) ≤ X.homOfLE h ⁻¹ᵁ (W.ι ⁻¹ᵁ U) :=
    le_of_comp _ _ U rfl _ (Scheme.homOfLE_ι _ _) ((Scheme.Opens.ι_preimage_self V).symm.le.trans (fun y hy => hU hy))
  have h0 : Sec.res (⊤ : V.toScheme.Opens).ι (rs h a) = 0 := by
    rw [sres_comp, ← Scheme.Hom.resLE_comp_ι (X.homOfLE h) e, ← sres_comp, h1, sres_zero]
  rw [← sres_id (rs h a), ← Scheme.toIso_inv_ι, ← sres_comp, h0, sres_zero]

private theorem resK_inj (q : ℕ) (i : ℤ) (s : ℤ) : Injective ((res _ (tw q i)).X s) := by unfold GlobalTheory.EtC.res; infer_instance
private theorem LeafResK_pf : LeafResK := fun q i => ⟨resK_inj q i, fun s hs => by
  have : (res _ (tw q i)).IsStrictlyGE 0 := by unfold GlobalTheory.EtC.res; infer_instance
  exact CochainComplex.isZero_of_isStrictlyGE (res _ (tw q i)) 0 s hs⟩

theorem LeafDescOGlue_of : LeafDescOGlue := descent_glue_of_residue_pullback_inclusion LeafResK_pf LeafZcPull_pf LeafZcIn_pf

end LateralTheory.CohomologicalPurity.Cl
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.Thom.ExcP.Chart

theorem eqv_of_isIso {R : Type} [CommRing R] {E E' : Spc} (f : E ⟶ E') [IsIso f] (F : Shv R) : Eqv R f F := by
  intro n
  refine ⟨fun x y h => ?_, fun y => ⟨pull R (inv f) F n y, ?_⟩⟩
  · have := congrArg (pull R (inv f) F n) h
    rwa [← pull_comp, ← pull_comp, IsIso.inv_hom_id, pull_id, pull_id] at this
  · rw [← pull_comp, IsIso.hom_inv_id, pull_id]

theorem eqv_comp {R : Type} [CommRing R] {E E' E'' : Spc} {f : E ⟶ E'} {g : E' ⟶ E''} {F : Shv R}
    (hf : Eqv R f F) (hg : Eqv R g F) : Eqv R (f ≫ g) F := by
  intro n
  have : (pull R (f ≫ g) F n : _ → _) = pull R f F n ∘ pull R g F n := funext fun x => pull_comp R f g F n x
  rw [this]; exact (hf n).comp (hg n)

theorem eqv_of_section {R : Type} [CommRing R] {E E' : Spc} {f : E ⟶ E'} {r : E' ⟶ E} {F : Shv R}
    (h : f ≫ r = 𝟙 _) (hr : Eqv R r F) : Eqv R f F := by
  intro n
  have hc : (pull R f F n : _ → _) ∘ pull R r F n = id := by
    funext x; change pull R f F n (pull R r F n x) = x; rw [← pull_comp, h, pull_id]
  have : Function.Bijective ((pull R f F n : _ → _) ∘ pull R r F n) := by rw [hc]; exact Function.bijective_id
  exact (Function.Bijective.of_comp_iff _ (hr n)).1 this

def fW (d : ℕ) (R : Type) [CommRing R] :
    Spec (CommRingCat.of (LaurentPolynomial (MvPolynomial (Fin d) R))) ⟶ Spec (CommRingCat.of (MvPolynomial (Fin d) R)) :=
  Spec.map (CommRingCat.ofHom (LaurentPolynomial.C : MvPolynomial (Fin d) R →+* _))

theorem smooth_C (A : Type) [CommRing A] : (LaurentPolynomial.C : A →+* LaurentPolynomial A).Smooth := by
  have h1 : (Polynomial.C : A →+* Polynomial A).Smooth := by
    rw [show (Polynomial.C : A →+* Polynomial A) = algebraMap A (Polynomial A) from rfl]
    exact RingHom.smooth_algebraMap.2 ⟨inferInstance, inferInstance⟩
  have h2 : (algebraMap (Polynomial A) (LaurentPolynomial A)).Smooth :=
    RingHom.Smooth.holdsForLocalizationAway (R := Polynomial A) (S := LaurentPolynomial A) Polynomial.X
  have h3 := RingHom.Smooth.comp h1 h2
  convert h3 using 1
  ext a
  simp

instance (d : ℕ) (R : Type) [CommRing R] : Smooth (fW d R) := by
  rw [fW, HasRingHomProperty.Spec_iff (P := @Smooth)]
  exact smooth_C _

instance (d : ℕ) (R : Type) [CommRing R] : Surjective (fW d R) := by
  let s : LaurentPolynomial (MvPolynomial (Fin d) R) →+* MvPolynomial (Fin d) R := LaurentPolynomial.eval₂ (RingHom.id _) 1
  have hs : s.comp LaurentPolynomial.C = RingHom.id _ := by ext x <;> simp [s]
  have : Spec.map (CommRingCat.ofHom s) ≫ fW d R = 𝟙 _ := by
    rw [fW, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hs]; exact Spec.map_id _
  have : Surjective (Spec.map (CommRingCat.ofHom s) ≫ fW d R) := by rw [this]; infer_instance
  exact Surjective.of_comp (Spec.map (CommRingCat.ofHom s)) (fW d R)

def LeafWCech : Prop := ∀ (d : ℕ) (R : Type) [CommRing R],
  ∃ ψ : W d R ⟶ cech (fW d R), IsIso ψ ∧ wa d R ≫ ψ ≫ cechAug (fW d R) = 𝟙 _

theorem LeafWEqvR_of (hW : LeafWCech) : LeafWEqvR := by
  intro hH q _ d R _ _ i
  obtain ⟨ψ, hψ, he⟩ := hW d R
  have hA : Eqv _ (cechAug (fW d R)) (tw q i) := hH.2.1 (ZMod q) (fW d R) (tw q i)
  exact eqv_of_section (by rw [← he]) (eqv_comp (eqv_of_isIso ψ _) hA)

end LateralTheory.CohomologicalPurity.Thom.ExcP.Chart
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.Thom.ExcP.Chart

theorem wincl_mono (d : ℕ) : Mono (Wincl d) := by
  have h : ∀ n, Mono ((Wincl d).app n) := by
    intro n
    have : ∀ U, Mono (((Wincl d).app n).app U) := by
      intro U
      rw [mono_iff_injective]
      intro F G hFG
      change (F : ComposableArrows (WVec d U.unop) _) ⋙ WVec.incl d U.unop = G ⋙ WVec.incl d U.unop at hFG
      exact CategoryTheory.Functor.hext (fun i => Subtype.ext (congrArg (fun K => K.obj i) hFG))
        (fun i j a => Functor.hcongr_hom hFG a)
    exact NatTrans.mono_of_mono_app _
  exact NatTrans.mono_of_mono_app _

theorem wb_mono (d : ℕ) (R : Type) [CommRing R] : Mono (wb d R) := by
  have := wincl_mono d
  unfold wb; infer_instance

def LocCov {U V E : Spc} (f : U ⟶ E) (g : V ⟶ E) : Prop :=
  ∀ (n : SimplexCategoryᵒᵖ) (X : Scheme.{0}) (x : (E.obj n).obj (op X)), ∃ (ι : Type) (O : ι → X.Opens),
    iSup O = ⊤ ∧ ∀ i, (∃ y, (f.app n).app (op (O i : Scheme.{0})) y = (E.obj n).map (O i).ι.op x) ∨
      (∃ y, (g.app n).app (op (O i : Scheme.{0})) y = (E.obj n).map (O i).ι.op x)

def LeafCovLoc : Prop := ∀ (R : Type) [CommRing R] {U V E : Spc} (f : U ⟶ E) (g : V ⟶ E), Mono f → Mono g →
  LocCov f g → Cover2 R f g

def LeafWLoc : Prop := ∀ (d : ℕ) (R : Type) [CommRing R], LocCov (wb d R) (pr d R).hom

theorem LeafWCov_of (hG : LeafGeo) (hC : LeafCovLoc) (hW : LeafWLoc) : LeafWCov := by
  intro _ q _ d R _ _
  exact hC (ZMod q) (wb d R) (pr d R).hom (wb_mono d R) (hG.1 d R) (hW d R)

end LateralTheory.CohomologicalPurity.Thom.ExcP.Chart
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex.HomComplex

namespace LateralTheory.CohomologicalPurity.TubeCut

theorem LeafHensH_of : LeafHensH := by
  intro hH q _ C _ K hK hq i
  exact hH.2.2.2.2.2.2.2.2.2.2.2 q C K hq i

end LateralTheory.CohomologicalPurity.TubeCut
end
end
