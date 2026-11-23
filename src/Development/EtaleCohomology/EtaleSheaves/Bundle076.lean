module

public import Development.EtaleCohomology.EtaleSheaves.Bundle067
public import Mathlib.AlgebraicGeometry.QuasiAffine
public import Development.EtaleCohomology.EtaleSheaves.Bundle068
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Development.EtaleCohomology.EtaleSheaves.Bundle069
public import Mathlib.CategoryTheory.Adjunction.Evaluation
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.FlatMono
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Colim
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.Polynomial.Basic
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4 Order TopologicalSpace Topology

namespace LateralTheory.E.LeafGlueDimPf

theorem dim_le_of_cover {X U V : Type*} [TopologicalSpace X] [TopologicalSpace U] [TopologicalSpace V]
    (f : U → X) (g : V → X) (hf : IsOpenEmbedding f) (hg : IsOpenEmbedding g)
    (hc : Set.range f ∪ Set.range g = Set.univ) :
    topologicalKrullDim X ≤ max (topologicalKrullDim U) (topologicalKrullDim V) := by
  unfold topologicalKrullDim
  rw [krullDim_eq_iSup_coheight]
  refine iSup_le fun Z => ?_
  obtain ⟨z, hz⟩ := Z.2.nonempty
  have hzu : z ∈ Set.range f ∪ Set.range g := hc ▸ Set.mem_univ z
  rcases hzu with ⟨w, rfl⟩ | ⟨w, rfl⟩
  · let T := (IrreducibleCloseds.orderIsoOfIsOpenEmbedding f hf).symm ⟨Z, ⟨w, hz⟩⟩
    have hT : IrreducibleCloseds.map f hf.continuous T = Z := by
      have := (IrreducibleCloseds.orderIsoOfIsOpenEmbedding f hf).apply_symm_apply ⟨Z, ⟨w, hz⟩⟩
      exact congrArg Subtype.val this
    rw [← hT, hf.coheight_map]
    exact le_trans (coheight_le_krullDim T) le_sup_left
  · let T := (IrreducibleCloseds.orderIsoOfIsOpenEmbedding g hg).symm ⟨Z, ⟨w, hz⟩⟩
    have hT : IrreducibleCloseds.map g hg.continuous T = Z := by
      have := (IrreducibleCloseds.orderIsoOfIsOpenEmbedding g hg).apply_symm_apply ⟨Z, ⟨w, hz⟩⟩
      exact congrArg Subtype.val this
    rw [← hT, hg.coheight_map]
    exact le_trans (coheight_le_krullDim T) le_sup_right

theorem dim_eq_of_cover {X U V : Type*} [TopologicalSpace X] [TopologicalSpace U] [TopologicalSpace V]
    (f : U → X) (g : V → X) (hf : IsOpenEmbedding f) (hg : IsOpenEmbedding g)
    (hc : Set.range f ∪ Set.range g = Set.univ) :
    topologicalKrullDim X = max (topologicalKrullDim U) (topologicalKrullDim V) :=
  le_antisymm (dim_le_of_cover f g hf hg hc)
    (max_le hf.isInducing.topologicalKrullDim_le hg.isInducing.topologicalKrullDim_le)

theorem dim_Sp {Ω L : Type} [Field Ω] [Field L] [Algebra Ω L] (A : Subalgebra Ω L) :
    topologicalKrullDim (Sp A) = ringKrullDim A :=
  PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim A

theorem LeafGlueDim_of : LateralTheory.E.LeafGlueProperPf.LeafGlueDim := by
  intro Ω L _ _ _ A B u h G
  have hA : topologicalKrullDim (Sp A) = 1 := (dim_Sp A).trans h.2.2.2.2.2.2.2.1
  have hB : topologicalKrullDim (Sp B) = 1 := (dim_Sp B).trans h.2.2.2.2.2.2.2.2.1
  have := G.hiA; have := G.hiB
  rw [dim_eq_of_cover G.iA.base G.iB.base G.iA.isOpenEmbedding G.iB.isOpenEmbedding G.cover, hA, hB, max_self]

end LateralTheory.E.LeafGlueDimPf
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4 LateralTheory.E.LeafGlueProperPf

namespace LateralTheory.E.GluingExistence

theorem mul_pow_mem {Ω L : Type} [Field Ω] [Field L] [Algebra Ω L] (C : Subalgebra Ω L) (v : L)
    (hv : v ∈ C) (hv0 : v ≠ 0) (x : L) (hx : x ∈ Algebra.adjoin Ω ((C : Set L) ∪ {v⁻¹})) :
    ∃ n : ℕ, x * v ^ n ∈ C := by
  induction hx using Algebra.adjoin_induction with
  | mem x hx =>
    rcases hx with hx | hx
    · exact ⟨0, by simpa using hx⟩
    · rw [Set.mem_singleton_iff.mp hx]; exact ⟨1, by rw [pow_one, inv_mul_cancel₀ hv0]; exact C.one_mem⟩
  | algebraMap r => exact ⟨0, by simpa using C.algebraMap_mem r⟩
  | add x y _ _ hx hy =>
    obtain ⟨n, hn⟩ := hx; obtain ⟨m, hm⟩ := hy
    refine ⟨n + m, ?_⟩
    have : (x + y) * v ^ (n + m) = (x * v ^ n) * v ^ m + (y * v ^ m) * v ^ n := by ring
    rw [this]; exact C.add_mem (C.mul_mem hn (C.pow_mem hv _)) (C.mul_mem hm (C.pow_mem hv _))
  | mul x y _ _ hx hy =>
    obtain ⟨n, hn⟩ := hx; obtain ⟨m, hm⟩ := hy
    refine ⟨n + m, ?_⟩
    have : (x * y) * v ^ (n + m) = (x * v ^ n) * (y * v ^ m) := by ring
    rw [this]; exact C.mul_mem hn hm

theorem away {Ω L : Type} [Field Ω] [Field L] [Algebra Ω L] (C E : Subalgebra Ω L) (v : L)
    (hv : v ∈ C) (hv0 : v ≠ 0) (hCE : C ≤ E) (hE : E = Algebra.adjoin Ω ((C : Set L) ∪ {v⁻¹})) :
    letI := (Subalgebra.inclusion hCE).toRingHom.toAlgebra
    IsLocalization.Away (⟨v, hv⟩ : C) E := by
  letI := (Subalgebra.inclusion hCE).toRingHom.toAlgebra
  have hvi : v⁻¹ ∈ E := hE ▸ Algebra.subset_adjoin (Set.mem_union_right _ rfl)
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨y, n, rfl⟩
    refine isUnit_iff_exists_inv.mpr ⟨⟨v⁻¹, hvi⟩ ^ n, Subtype.ext ?_⟩
    show (v ^ n) * (v⁻¹) ^ n = 1
    rw [← mul_pow, mul_inv_cancel₀ hv0, one_pow]
  · rintro ⟨z, hz⟩
    obtain ⟨n, hn⟩ := mul_pow_mem C v hv hv0 z (hE ▸ hz)
    exact ⟨(⟨z * v ^ n, hn⟩, ⟨⟨v, hv⟩ ^ n, n, rfl⟩), Subtype.ext rfl⟩
  · intro x y h
    refine ⟨1, ?_⟩
    have : (x : L) = y := congrArg (fun w : E => (w : L)) h
    simp [Subtype.ext this]

theorem LeafGlueExists_of : LeafGlueExists := by
  intro Ω L _ _ _ A B u h
  obtain ⟨hu, huA, huB, -, -, -, -, -, -, -, -, hadj, -⟩ := h
  set D := Dr Ω A u
  have hAD : A ≤ D := le_Dr_A A u
  have hBD : B ≤ D := le_Dr_B A B u hadj
  letI iAD : Algebra A D := (Subalgebra.inclusion hAD).toRingHom.toAlgebra
  letI iBD : Algebra B D := (Subalgebra.inclusion hBD).toRingHom.toAlgebra
  haveI : IsLocalization.Away (⟨u, huA⟩ : A) D := away A D u huA hu hAD rfl
  haveI : IsLocalization.Away (⟨u⁻¹, huB⟩ : B) D :=
    away B D u⁻¹ huB (inv_ne_zero hu) hBD (by rw [inv_inv]; exact hadj)
  let fA : Sp D ⟶ Sp A := Spec.map (CommRingCat.ofHom (Subalgebra.inclusion hAD).toRingHom)
  let fB : Sp D ⟶ Sp B := Spec.map (CommRingCat.ofHom (Subalgebra.inclusion hBD).toRingHom)
  haveI hfA : IsOpenImmersion fA := IsOpenImmersion.of_isLocalization (S := D) (⟨u, huA⟩ : A)
  haveI hfB : IsOpenImmersion fB := IsOpenImmersion.of_isLocalization (S := D) (⟨u⁻¹, huB⟩ : B)
  haveI : ∀ {i j : WalkingSpan} (f : i ⟶ j), IsOpenImmersion ((span fA fB).map f) := by
    intro i j f
    rcases f with _ | j
    · exact inferInstanceAs (IsOpenImmersion (𝟙 _))
    · rcases j with _ | _
      · exact hfA
      · exact hfB
  have hc : fA ≫ Spec.map (CommRingCat.ofHom (algebraMap Ω A)) =
      fB ≫ Spec.map (CommRingCat.ofHom (algebraMap Ω B)) := by
    simp only [fA, fB, ← Spec.map_comp]; rfl
  refine ⟨{
    C0 := pushout fA fB
    c0 := pushout.desc _ _ hc
    iA := pushout.inl fA fB
    iB := pushout.inr fA fB
    hiA := inferInstanceAs (IsOpenImmersion (colimit.ι (span fA fB) _))
    hiB := inferInstanceAs (IsOpenImmersion (colimit.ι (span fA fB) _))
    hcA := pushout.inl_desc _ _ _
    hcB := pushout.inr_desc _ _ _
    agree := pushout.condition
    cover := ?_
    inter := ?_ }⟩
  · ext x
    simp only [Set.mem_union, Set.mem_range, Set.mem_univ, iff_true]
    obtain ⟨i, xi, rfl⟩ := Scheme.IsLocallyDirected.ι_jointly_surjective (span fA fB) x
    rcases i with _ | j
    · left; refine ⟨fA xi, ?_⟩
      rw [← colimit.w (span fA fB) (WidePushoutShape.Hom.init WalkingPair.left)]; rfl
    · rcases j with _ | _
      · left; exact ⟨xi, rfl⟩
      · right; exact ⟨xi, rfl⟩
  · ext x
    constructor
    · rintro ⟨⟨a, rfl⟩, ⟨b, hb⟩⟩
      have hab : colimit.ι (span fA fB) (some WalkingPair.left) a =
          colimit.ι (span fA fB) (some WalkingPair.right) b := hb.symm
      obtain ⟨k, fi, fj, y, hy1, hy2⟩ := (Scheme.IsLocallyDirected.ι_eq_ι_iff (span fA fB)).mp hab
      rcases k with _ | k
      · refine ⟨y, ?_⟩
        rw [← hy1, Subsingleton.elim fi (WidePushoutShape.Hom.init WalkingPair.left)]; rfl
      · rcases k with _ | _
        · cases (show WidePushoutShape.Hom (J := WalkingPair) (some WalkingPair.left) (some WalkingPair.right) from fj)
        · cases (show WidePushoutShape.Hom (J := WalkingPair) (some WalkingPair.right) (some WalkingPair.left) from fi)
    · rintro ⟨y, rfl⟩
      refine ⟨⟨fA y, rfl⟩, ⟨fB y, ?_⟩⟩
      show (fB ≫ pushout.inr fA fB).base y = (fA ≫ pushout.inl fA fB).base y
      rw [pushout.condition]

end LateralTheory.E.GluingExistence
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4 LateralTheory.E.LeafDescendVCut LateralTheory.E.LeafDescendChainPf
  LateralTheory.E.LeafDescendFPPf LateralTheory.E.LeafTripleFPPf

namespace LateralTheory.E.LeafPairRelPf

theorem incl_incl {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] {R R' R'' : Subalgebra k Ω} (h : R ≤ R')
    (h' : R' ≤ R'') : incl h' ≫ incl h = incl (h.trans h') := by
  rw [← Spec.map_comp]
  rfl

def LeafFactorStage : Prop := ∀ (k : Type) [Field k] (Ω : Type) [Field Ω] [Algebra k Ω] (R : Subalgebra k Ω), R.FG →
    ∀ {C E Y : Scheme.{0}} (c : C ⟶ Sp Ω) (p : E ⟶ Sp R) (w : C ⟶ E), FP p → ∀ (hs : IsPullback w c p (toR R))
    (f : Y ⟶ Sp R), LocallyOfFinitePresentation f → ∀ (a : C ⟶ Y), a ≫ f = c ≫ toR R →
    ∃ (R' : Subalgebra k Ω) (h : R ≤ R'), R'.FG ∧ ∃ (g : pullback p (incl h) ⟶ Y),
      g ≫ f = pullback.snd p (incl h) ≫ incl h ∧
      pullback.lift w (c ≫ toR R') (by rw [Category.assoc, toR_incl]; exact hs.w) ≫ g = a

theorem LeafPairRel_of (hO : LeafObjFP) (hF : LeafFactorStage) : LeafPairRel := by
  intro k _ Ω _ _ R hRfg C0 C1 c0 γ1 h1fp D0 q v0 hq hs
  obtain ⟨R1, hR1, E, p1, w, hp1, hsE⟩ := hO k Ω (γ1 ≫ c0) h1fp
  have h0 : R ≤ R ⊔ R1 := le_sup_left
  have h1 : R1 ≤ R ⊔ R1 := le_sup_right
  have hfg : (R ⊔ R1).FG := hRfg.sup hR1
  have hsE' := pb_lift h1 hsE
  have hlfp : LocallyOfFinitePresentation (pullback.snd q (incl h0)) := (fp_snd q (incl h0) hq).1
  obtain ⟨S, h, hS, g, hg1, hg2⟩ := hF k Ω (R ⊔ R1) hfg (γ1 ≫ c0) (pullback.snd p1 (incl h1)) _
    (fp_snd _ _ hp1) hsE' (pullback.snd q (incl h0)) hlfp
    (γ1 ≫ pullback.lift v0 (c0 ≫ toR (R ⊔ R1)) (by rw [Category.assoc, toR_incl]; exact hs.w))
    (by simp only [Category.assoc, pullback.lift_snd])
  refine ⟨S, h0.trans h, hS, pullback (pullback.snd p1 (incl h1)) (incl h),
    pullback.lift (g ≫ pullback.fst q (incl h0)) (pullback.snd _ _) ?_,
    pullback.lift (pullback.lift w ((γ1 ≫ c0) ≫ toR (R ⊔ R1)) (by rw [Category.assoc, toR_incl]; exact hsE.w))
      ((γ1 ≫ c0) ≫ toR S) (by simp only [Category.assoc, toR_incl, pullback.lift_snd]), ?_, ?_, ?_⟩
  · rw [Category.assoc, pullback.condition, ← Category.assoc, hg1, Category.assoc, incl_incl]
  · rw [pullback.lift_snd]; exact fp_snd _ _ (fp_snd _ _ hp1)
  · convert pb_lift h hsE' using 2
    simp only [pullback.lift_snd]
  · apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, Category.assoc, pullback.lift_fst, ← Category.assoc, hg2,
        Category.assoc, pullback.lift_fst]
    · simp only [Category.assoc, pullback.lift_snd]

end LateralTheory.E.LeafPairRelPf

end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry

namespace LateralTheory.E.FlatMonoLimPf

theorem exists_lift {X Y T : Scheme.{0}} (m : X ⟶ Y) [Mono m] [Flat m] [QuasiCompact m] (t : T ⟶ Y)
    (h : Set.range t ⊆ Set.range m) : ∃ b : T ⟶ X, b ≫ m = t := by
  have hs : Surjective (pullback.fst t m) := by
    constructor
    rw [← Set.range_eq_univ, Scheme.Pullback.range_fst]
    exact Set.eq_univ_of_forall fun x => h ⟨x, rfl⟩
  have : IsIso (pullback.fst t m) := Flat.isIso_of_surjective_of_mono _
  refine ⟨inv (pullback.fst t m) ≫ pullback.snd t m, ?_⟩
  rw [Category.assoc, ← pullback.condition, IsIso.inv_hom_id_assoc]

theorem FlatMonoLim_of : LateralTheory.E.NbIsoPf.FlatMonoLim := by
  intro Y J _ _ D ι hι hc X m hm hf hq hr c hl
  have ho : ∀ j, IsOpenImmersion (ι j) := fun j => (hι j).1
  have hsub : ∀ j, Set.range m ⊆ Set.range (ι j) := fun j => hr ▸ Set.iInter_subset _ j
  have hind : ∀ j k, c.π.app j ≫ ι j = c.π.app k ≫ ι k := by
    intro j k
    rw [← c.w (IsCofiltered.minToLeft j k), ← c.w (IsCofiltered.minToRight j k), Category.assoc, Category.assoc,
      hc, hc]
  obtain ⟨j0⟩ : Nonempty J := IsCofiltered.nonempty
  have hp : Set.range (c.π.app j0 ≫ ι j0) ⊆ Set.range m := by
    rw [hr]
    refine Set.subset_iInter fun j => ?_
    rw [hind j0 j]
    rintro _ ⟨x, rfl⟩
    exact ⟨c.π.app j x, (Scheme.Hom.comp_apply _ _ _).symm⟩
  obtain ⟨b, hb⟩ := exists_lift m _ hp
  let s : Cone D :=
    { pt := X
      π :=
        { app := fun j => IsOpenImmersion.lift (ι j) m (hsub j)
          naturality := fun j k f => by
            rw [← cancel_mono (ι k)]
            simp [hc] } }
  have hs : ∀ j, hl.lift s ≫ c.π.app j ≫ ι j = m := by
    intro j
    rw [hl.fac_assoc]
    exact IsOpenImmersion.lift_fac _ _ _
  refine ⟨⟨b, hl.lift s, ?_, ?_⟩⟩
  · refine hl.hom_ext fun j => ?_
    rw [← cancel_mono (ι j)]
    simp only [Category.assoc]
    erw [hs j, hb, Category.id_comp]
    exact hind j0 j
  · rw [← cancel_mono m, Category.assoc, hb, hs, Category.id_comp]

end LateralTheory.E.FlatMonoLimPf
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry LateralTheory.E.BuildCut

namespace LateralTheory.E.SysFMPf

def phi {P : Scheme.{0}} [CompactSpace P] [QuasiSeparatedSpace P] {W : Type} [CommRing W]
    (w : Spec (CommRingCat.of W) ⟶ P) : Γ(w.normalization, ⊤) →+* W :=
  (w.toNormalization.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of W)).hom).hom

def RR {P : Scheme.{0}} [CompactSpace P] [QuasiSeparatedSpace P] {W : Type} [CommRing W]
    (w : Spec (CommRingCat.of W) ⟶ P) (q : PrimeSpectrum W) : Set w.normalization :=
  {y | ∀ s : Γ(w.normalization, ⊤), IsIdempotentElem (phi w s) → phi w s ∉ q.asIdeal → y ∈ w.normalization.basicOpen s}

def Sys : Prop := ∀ {P : Scheme.{0}} [CompactSpace P] [QuasiSeparatedSpace P] (W : Type) [CommRing W]
  (w : Spec (CommRingCat.of W) ⟶ P), ProdACF W → ∀ y : w.normalization,
    ∃ (q : PrimeSpectrum W) (J : Type) (_ : SmallCategory J) (_ : IsCofiltered J) (D : J ⥤ Scheme.{0})
      (ι : ∀ j, D.obj j ⟶ w.normalization),
      (∀ j, IsOpenImmersion (ι j) ∧ IsClosedImmersion (ι j) ∧ y ∈ Set.range (ι j)) ∧
      (∀ {j k : J} (f : j ⟶ k), D.map f ≫ ι k = ι j ∧ IsAffineHom (D.map f)) ∧
      ⋂ j, Set.range (ι j) = RR w q

def FMex : Prop := ∀ {P : Scheme.{0}} [CompactSpace P] [QuasiSeparatedSpace P] (W : Type) [CommRing W]
  (w : Spec (CommRingCat.of W) ⟶ P), ProdACF W → ∀ q : PrimeSpectrum W,
    ∃ m : (Spec.map (CommRingCat.ofHom (algebraMap W (Localization.AtPrime q.asIdeal))) ≫ w).normalization ⟶ w.normalization,
      Spec.map (CommRingCat.ofHom (algebraMap W (Localization.AtPrime q.asIdeal))) ≫ w.toNormalization =
        (Spec.map (CommRingCat.ofHom (algebraMap W (Localization.AtPrime q.asIdeal))) ≫ w).toNormalization ≫ m ∧
      m ≫ w.fromNormalization = (Spec.map (CommRingCat.ofHom (algebraMap W (Localization.AtPrime q.asIdeal))) ≫ w).fromNormalization ∧
      Mono m ∧ Flat m ∧ QuasiCompact m

def FMrange : Prop := ∀ {P : Scheme.{0}} [CompactSpace P] [QuasiSeparatedSpace P] (W : Type) [CommRing W]
  (w : Spec (CommRingCat.of W) ⟶ P), ProdACF W → ∀ (q : PrimeSpectrum W)
    (m : (Spec.map (CommRingCat.ofHom (algebraMap W (Localization.AtPrime q.asIdeal))) ≫ w).normalization ⟶ w.normalization),
      Spec.map (CommRingCat.ofHom (algebraMap W (Localization.AtPrime q.asIdeal))) ≫ w.toNormalization =
        (Spec.map (CommRingCat.ofHom (algebraMap W (Localization.AtPrime q.asIdeal))) ≫ w).toNormalization ≫ m →
      m ≫ w.fromNormalization = (Spec.map (CommRingCat.ofHom (algebraMap W (Localization.AtPrime q.asIdeal))) ≫ w).fromNormalization →
      Set.range m = RR w q

theorem SysFM_of (hS : Sys) (hE : FMex) (hR : FMrange) : LateralTheory.E.NbIsoPf.SysFM := by
  intro P _ _ W _ w hW y
  obtain ⟨q, J, _, _, D, ι, h1, h2, h3⟩ := hS W w hW y
  obtain ⟨m, e1, e2, hm, hf, hq⟩ := hE W w hW q
  refine ⟨q, J, inferInstance, inferInstance, D, ι, h1, h2, m, hm, hf, hq, ?_⟩
  rw [h3]
  exact hR W w hW q m e1 e2

end LateralTheory.E.SysFMPf
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.LeafClosedSH0Pf
open LateralTheory.E.E4 LateralTheory.E.LeafVanBPf

def LeafSHSieve : Prop := ∀ (X : Scheme.{0}) [IsAffine X], SH Γ(X, ⊤) →
  ∀ S ∈ Scheme.etaleTopology X, S (𝟙 X)

def LeafSHQuot : Prop := ∀ (A : Type) [CommRing A], SH A → ∀ {W' : Scheme.{0}} (ι' : W' ⟶ Sp A) [IsClosedImmersion ι'],
  IsEmpty W' ∨ SH Γ(W', ⊤)

def LeafEmptySec : Prop := ∀ (R : Type) [CommRing R] (F : Shv R) (X : Scheme.{0}), IsEmpty X → Subsingleton (Sec F X)

def LeafPrimLift : Prop := ∀ (q : ℕ) (B C : Type) [CommRing B] [CommRing C] [HenselianLocalRing B] [Nontrivial C]
  (f : B →+* C), Function.Surjective f → Function.Surjective (Prim.map (q := q) f)

theorem a9_of_a0_a1_eigenbasis_a6 (hy : Hyps) : A9 := hy.2.2.2.2.2.2.2.1

theorem twF_surj (hP : LeafPrimLift) (q : ℕ) (i : ℤ) {B C : CommRingCat.{0}} [HenselianLocalRing B] [Nontrivial C]
    (f : B ⟶ C) (hf : Function.Surjective f) : Function.Surjective ((twF q i).map f) := by
  intro y
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  obtain ⟨x', rfl⟩ := Finsupp.mapDomain_surjective (hP q B C f.hom hf) x
  exact ⟨Submodule.Quotient.mk x', rfl⟩

theorem secSurj (hS : LeafSHSieve) (hQ : LeafSHQuot) (hE : LeafEmptySec) (hP : LeafPrimLift) (q : ℕ) (i : ℤ)
    (A : Type) [CommRing A] (hA : SH A) {W' : Scheme.{0}} (ι' : W' ⟶ Sp A) [IsClosedImmersion ι'] :
    Function.Surjective (Sec.res ι' : Sec (tw q i) (Sp A) → Sec (tw q i) W') := by
  rcases hQ A hA ι' with hW | hW
  · have := hE (ZMod q) (tw q i) W' hW
    exact fun y => ⟨0, Subsingleton.elim _ _⟩
  obtain ⟨hAff, hsurj⟩ := IsClosedImmersion.isAffine_surjective_of_isAffine ι'
  have hW0 := hW
  obtain ⟨_, _⟩ := hW
  obtain ⟨_, _⟩ := hA
  intro s
  let P : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} (ZMod q)) := Scheme.Γ ⋙ twF q i
  have hmem := Presheaf.imageSieve_mem Scheme.etaleTopology (toSheafify Scheme.etaleTopology P) s
  obtain ⟨t, ht⟩ := hS W' hW0 _ hmem
  let g : CommRingCat.of A ⟶ Γ(W', ⊤) := (Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ ι'.appTop
  have hg : Function.Surjective g := hsurj.comp (Scheme.ΓSpecIso (CommRingCat.of A)).commRingCatIsoToRingEquiv.symm.surjective
  obtain ⟨t', rfl⟩ := twF_surj hP q i g hg t
  refine ⟨(toSheafify Scheme.etaleTopology P).app (op (Sp A)) ((twF q i).map (Scheme.ΓSpecIso (CommRingCat.of A)).inv t'), ?_⟩
  have e1 := NatTrans.naturality_apply (toSheafify Scheme.etaleTopology P) ι'.op
    ((twF q i).map (Scheme.ΓSpecIso (CommRingCat.of A)).inv t')
  have e2 : P.map ι'.op ((twF q i).map (Scheme.ΓSpecIso (CommRingCat.of A)).inv t') = (twF q i).map g t' := by
    simp only [P, g, Functor.comp_map, Functor.map_comp, ConcreteCategory.comp_apply]
    rfl
  rw [e2, ht] at e1
  simp only [op_id] at e1
  refine Eq.trans ?_ (e1.symm.trans ?_)
  · rfl
  · simp
    rfl

theorem LeafClosedSH0_of (hS : LeafSHSieve) (hQ : LeafSHQuot) (hE : LeafEmptySec) (hP : LeafPrimLift) :
    LeafClosedSH0 := by
  intro hy q _ i A _ _ hA hq W' ι' _
  obtain ⟨-, e, he, -⟩ := a9_of_a0_a1_eigenbasis_a6 hy (ZMod q) (tw q i)
  intro y
  obtain ⟨s, rfl⟩ := (e W').surjective y
  obtain ⟨t, rfl⟩ := secSurj hS hQ hE hP q i A hA ι' s
  exact ⟨e _ t, he _ t⟩

end LateralTheory.E.LeafClosedSH0Pf
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex GlobalTheory.EtC

namespace LateralTheory.E.LeafSecInjPf

universe u v w

instance evaluationLeftAdjoint_preservesMono {C : Type u} [Category.{0} C] (R' : Type 1) [Ring R'] (c : C) :
    (evaluationLeftAdjoint (ModuleCat.{1} R') c).PreservesMonomorphisms where
  preserves {d₁ d₂} f _ := by
    rw [NatTrans.mono_iff_mono_app']
    intro t
    have e : ((evaluationLeftAdjoint (ModuleCat.{1} R') c).map f).app t =
        Limits.Sigma.map (fun _ : c ⟶ t => f) := by
      apply Limits.Sigma.hom_ext; intro h
      erw [Limits.Sigma.ι_desc]
    rw [e]
    have : HasCoproducts.{0} (ModuleCat.{1} R') := hasCoproducts_shrink.{0, 1}
    have : AB4OfSize.{0} (ModuleCat.{1} R') := AB4OfSize_shrink.{0, 1} _
    have : HasExactColimitsOfShape (Discrete (c ⟶ t)) (ModuleCat.{1} R') := AB4OfSize.ofShape _
    have : (MorphismProperty.monomorphisms (ModuleCat.{1} R')).IsStableUnderCoproductsOfShape (c ⟶ t) :=
      MorphismProperty.isStableUnderColimitsOfShape_monomorphisms _ _
    exact MorphismProperty.colimMap (W := MorphismProperty.monomorphisms (ModuleCat.{1} R'))
      (J := Discrete (c ⟶ t)) _ (fun _ => (inferInstance : Mono f))

theorem secInj (R : Type) [CommRing R] (F : Shv R) (hF : Injective F) (U : Scheme.{0}) :
    Injective ((sheafToPresheaf Scheme.etaleTopology.{0} (ModuleCat.{1} (ULift.{1} R)) ⋙
      (evaluation _ _).obj (op U)).obj F) :=
  ((evaluationAdjunctionRight (ModuleCat.{1} (ULift.{1} R)) (op U)).comp
    (sheafificationAdjunction Scheme.etaleTopology.{0} (ModuleCat.{1} (ULift.{1} R)))).map_injective _ hF

theorem LeafSecInj_of : LateralTheory.E.LeafTensQIsoPf.LeafSecInj := by
  intro R _ F hF U
  have h := secInj R F hF U
  exact (Module.injective_iff_injective_object (ULift.{1} R) (Sec F U)).mpr h

end LateralTheory.E.LeafSecInjPf
end
end
