module

public import Development.EtaleCohomology.EtaleSheaves.Bundle067
public import Mathlib.AlgebraicGeometry.ValuativeCriterion
public import Development.EtaleCohomology.EtaleSheaves.Bundle068
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.QuasiAffine
import Mathlib.Algebra.Order.Star.Int
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Linter.HaveILetI
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4 LateralTheory.E.LeafGlueProperPf

namespace LateralTheory.E.LeafGlueIsProperPf

variable {Ω L : Type} [Field Ω] [Field L] [Algebra Ω L] {A B : Subalgebra Ω L} {u : L}

def cov {hAD hBD} (G : Glued Ω L A B (Dr Ω A u) hAD hBD) : G.C0.OpenCover :=
  Scheme.Cover.mkOfCovers (P := @IsOpenImmersion) Bool (fun b => cond b (Sp A) (Sp B))
    (fun | true => G.iA | false => G.iB)
    (by
      intro x
      have hx : x ∈ Set.range G.iA.base ∪ Set.range G.iB.base := G.cover ▸ Set.mem_univ x
      rcases hx with ⟨z, rfl⟩ | ⟨z, rfl⟩
      · exact ⟨true, z, rfl⟩
      · exact ⟨false, z, rfl⟩)
    (by intro b; cases b <;> [exact G.hiB; exact G.hiA])

set_option backward.isDefEq.respectTransparency false in
theorem lft (h : GH Ω L A B u) {hAD hBD} (G : Glued Ω L A B (Dr Ω A u) hAD hBD) :
    LocallyOfFiniteType G.c0 := by
  refine IsZariskiLocalAtSource.of_openCover (P := @AlgebraicGeometry.LocallyOfFiniteType) (cov G) ?_
  intro b
  cases b
  · show LocallyOfFiniteType (G.iB ≫ G.c0)
    rw [G.hcB, HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
    exact RingHom.finiteType_algebraMap.mpr h.2.2.2.2.1
  · show LocallyOfFiniteType (G.iA ≫ G.c0)
    rw [G.hcA, HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
    exact RingHom.finiteType_algebraMap.mpr h.2.2.2.1

set_option backward.isDefEq.respectTransparency false in
theorem qc {hAD hBD} (G : Glued Ω L A B (Dr Ω A u) hAD hBD) : QuasiCompact G.c0 := by
  rw [HasAffineProperty.iff_of_isAffine (P := @AlgebraicGeometry.QuasiCompact)]
  refine ⟨?_⟩
  rw [← G.cover]
  exact (isCompact_range G.iA.base.hom.continuous).union (isCompact_range G.iB.base.hom.continuous)

def LeafGlueSep : Prop := ∀ (Ω L : Type) [Field Ω] [Field L] [Algebra Ω L] (A B : Subalgebra Ω L) (u : L)
  (h : GH Ω L A B u) (G : Glued Ω L A B (Dr Ω A u) (le_Dr_A A u) (le_Dr_B A B u h.2.2.2.2.2.2.2.2.2.2.2.1)),
  IsSeparated G.c0

def LeafGlueExistence : Prop := ∀ (Ω L : Type) [Field Ω] [Field L] [Algebra Ω L] (A B : Subalgebra Ω L) (u : L)
  (h : GH Ω L A B u) (G : Glued Ω L A B (Dr Ω A u) (le_Dr_A A u) (le_Dr_B A B u h.2.2.2.2.2.2.2.2.2.2.2.1)),
  ValuativeCriterion.Existence G.c0

theorem LeafGlueIsProper_of (hS : LeafGlueSep) (hE : LeafGlueExistence) : LeafGlueIsProper := by
  intro Ω L _ _ _ A B u h G
  have := hS Ω L A B u h G
  have := qc G
  have := lft h G
  have : UniversallyClosed G.c0 := UniversallyClosed.of_valuativeCriterion _ (hE Ω L A B u h G)
  exact {}

end LateralTheory.E.LeafGlueIsProperPf
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex CochainComplex.HomComplex

namespace LateralTheory.E.LeafInj0WPf
open LateralTheory.E.E4 LateralTheory.E.LeafGhostCut LateralTheory.E.EtaleTopologySheaves LateralTheory.E.LeafDegCut LateralTheory.E.LeafInj0Pf

theorem fgtInj0 (R : Type) [CommRing R] (F : Shv R) {U E : Spc} (f : U ⟶ E)
    (hU : Subsingleton (H R U F (-1))) (y : Hrel R f F 0) (hy : fgt R f F 0 y = 0) : y = 0 := by
  obtain ⟨z, rfl⟩ := y.mk_surjective
  obtain ⟨β, hβ⟩ : ∃ β : Cochain ((chains R).obj E) (res R F) (-1), δ (-1) 0 β = (Cochain.ofHom (mappingCone.inr ((chains R).map f))).comp z.1 (zero_add 0) := by
    have := hy
    change CohomologyClass.mk _ = 0 at this
    rw [CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ (-1) (by omega)] at this
    obtain ⟨β, hβ⟩ := this
    exact ⟨β, by rw [hβ]; rfl⟩
  have hdec : z.1 = mappingCone.descCochain ((chains R).map f) ((mappingCone.inl ((chains R).map f)).comp z.1 (show -1 + 0 = -1 by omega))
      ((Cochain.ofHom (mappingCone.inr ((chains R).map f))).comp z.1 (zero_add 0)) (show (-1 : ℤ) + 1 = 0 by omega) := by
    rw [mappingCone.ext_cochain_from_iff _ (-1) 0 (by omega)]
    simp [mappingCone.inl_descCochain]
  have hz : δ 0 1 z.1 = 0 := Cocycle.δ_eq_zero z 1
  rw [hdec, mappingCone.δ_descCochain _ _ _ _ _ (by omega)] at hz
  rw [mappingCone.ext_cochain_from_iff _ 0 1 (by omega)] at hz
  obtain ⟨hz1, -⟩ := hz
  simp only [Cochain.comp_zero, Cochain.comp_add, mappingCone.inl_fst_assoc, mappingCone.inl_snd_assoc, add_zero] at hz1
  have hw : δ (-1) 0 ((mappingCone.inl ((chains R).map f)).comp z.1 (show -1 + 0 = -1 by omega) - (Cochain.ofHom ((chains R).map f)).comp β (zero_add (-1))) = 0 := by
    rw [δ_sub, δ_ofHom_comp, hβ, sub_eq_zero]
    rw [show Int.negOnePow 1 = -1 by decide] at hz1
    simp only [Units.smul_def, Units.val_neg, Units.val_one, neg_smul, one_smul, ← sub_eq_add_neg, sub_eq_zero] at hz1
    exact hz1
  obtain ⟨γ, hγ⟩ : ∃ γ : Cochain ((chains R).obj U) (res R F) (-2), δ (-2) (-1) γ = (mappingCone.inl ((chains R).map f)).comp z.1 (show -1 + 0 = -1 by omega) - (Cochain.ofHom ((chains R).map f)).comp β (zero_add (-1)) := by
    have h0 : CohomologyClass.mk (Cocycle.mk _ 0 (by omega) hw) = 0 := Subsingleton.elim _ _
    rw [CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ (-2) (by omega)] at h0
    obtain ⟨γ, hγ⟩ := h0
    exact ⟨γ, by rw [hγ]; rfl⟩
  rw [CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ (-1) (by omega)]
  refine ⟨mappingCone.descCochain ((chains R).map f) γ β (show (-2 : ℤ) + 1 = -1 by omega), ?_⟩
  rw [mappingCone.δ_descCochain _ _ _ _ _ (by omega), hγ, hβ, show Int.negOnePow 0 = 1 by decide, one_smul, sub_add_cancel]
  conv_rhs => rw [hdec]
  rfl

theorem fgtPull (R : Type) [CommRing R] (F : Shv R) {U E : Spc} (f : U ⟶ E) (n : ℤ) (y : Hrel R f F n) :
    pull R f F n (fgt R f F n y) = 0 := by
  obtain ⟨y, rfl⟩ := y.mk_surjective
  change CohomologyClass.mk _ = 0
  rw [CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ (n - 1) (by omega)]
  refine ⟨n.negOnePow • (mappingCone.inl ((chains R).map f)).comp y.1 (by omega), ?_⟩
  rw [δ_units_smul]
  rw [δ_comp (mappingCone.inl ((chains R).map f)) y.1 (show -1 + n = n - 1 by omega) 0 (n + 1) n (by omega) (by omega) (by omega)]
  simp [zcomp, mappingCone.δ_inl, Cochain.ofHom_comp, Cochain.comp_assoc_of_first_is_zero_cochain, smul_smul, Int.units_mul_self]

theorem fgtNat (R : Type) [CommRing R] (F : Shv R) {U E U' E' : Spc} (f : U ⟶ E) (f' : U' ⟶ E') (u : U' ⟶ U)
  (e : E' ⟶ E) (comm : f' ≫ e = u ≫ f) (n : ℤ) (y : Hrel R f F n) :
  fgt R f' F n (rpull R f f' u e comm F n y) = pull R e F n (fgt R f F n y) := by
  obtain ⟨y, rfl⟩ := y.mk_surjective
  refine congrArg CohomologyClass.mk (Cocycle.ext ?_)
  have key : mappingCone.inr ((chains R).map f') ≫ mappingCone.map ((chains R).map f') ((chains R).map f) ((chains R).map u) ((chains R).map e) (by rw [← Functor.map_comp, ← Functor.map_comp, comm]) = (chains R).map e ≫ mappingCone.inr ((chains R).map f) := by
    simp [mappingCone.map]
  simp [zcomp, rmap]
  rw [← Cochain.comp_assoc_of_first_is_zero_cochain, ← Cochain.comp_assoc_of_first_is_zero_cochain, ← Cochain.ofHom_comp, ← Cochain.ofHom_comp, key]

theorem leafRelNat : LeafRelNat := fgtNat

def LeafSecTw : Prop := ∀ (q : ℕ) [NeZero q] (k : Type) [Field k], IsUnit (q : k) → ∀ (i : ℤ)
  {B W : Scheme.{0}} (_ : B ⟶ Sp k) (ι : W ⟶ B) [IsClosedImmersion ι] (U : B.Etale) (s : Sec (tw q i) U.left),
  Sec.res (prB ι U) s = 0 → ∀ x : U.left, U.hom x ∈ Set.range ι →
  ∃ (U' : B.Etale) (a : U' ⟶ U) (y : U'.left), a.left y = x ∧ Sec.res a.left s = 0

def LeafSec0W : Prop := Hyps → ∀ (q : ℕ) [NeZero q] (k : Type) [Field k], IsUnit (q : k) → ∀ (i : ℤ)
  {B W : Scheme.{0}} (_ : B ⟶ Sp k) (ι : W ⟶ B) [IsClosedImmersion ι] (U : B.Etale) (h : Ht q (sch.obj U.left) 0 i),
  pull (ZMod q) (sch.map (prB ι U)) (tw q i) 0 h = 0 → ∀ x : U.left, U.hom x ∈ Set.range ι →
  ∃ (U' : B.Etale) (a : U' ⟶ U) (y : U'.left), a.left y = x ∧ pull (ZMod q) (sch.map a.left) (tw q i) 0 h = 0

theorem etale_standing_hypotheses_imply_restriction_axiom (hH : Hyps) : A9 := by
  unfold Hyps at hH
  exact hH.2.2.2.2.2.2.2.1

theorem LeafSec0W_of (hT : LeafSecTw) : LeafSec0W := by
  intro hH q _ k _ hq i B W s ι _ U h h0 x hx
  obtain ⟨e, hnat, -⟩ := ((etale_standing_hypotheses_imply_restriction_axiom hH) (ZMod q) (tw q i)).2
  obtain ⟨t, rfl⟩ := (e U.left).surjective h
  rw [hnat] at h0
  have h1 : Sec.res (prB ι U) t = 0 := (e _).injective (by rw [h0, map_zero])
  obtain ⟨U', a, y, hy, h2⟩ := hT q k hq i s ι U t h1 x hx
  exact ⟨U', a, y, hy, by rw [hnat, h2, map_zero]⟩

theorem LeafInj0W_of (hT : LeafSecTw) : LeafInj0W := by
  intro hH q _ k _ hq i B W Y0 Y1 Y2 s ι _ V hV p g1 g2 hp1 hp2 hp3 hS U c x hx
  obtain ⟨U', a, y, hy, hz⟩ := LeafSec0W_of hT hH q k hq i s ι U _ (fgtPull (ZMod q) (tw q i) (sch.map (prB ι U)) 0 c) x hx
  refine ⟨U', a, y, hy, Cov.all ?_⟩
  intro U'' b
  apply fgtInj0 (ZMod q) (tw q i) (sch.map (prB ι U''))
  · exact ((etale_standing_hypotheses_imply_restriction_axiom hH) (ZMod q) (tw q i)).1 _ (-1) (by norm_num)
  · rw [fgtNat]
    have e : (b ≫ a).left = b.left ≫ a.left := rfl
    rw [e, Functor.map_comp, pull_comp, hz, map_zero]

end LateralTheory.E.LeafInj0WPf
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite Polynomial IsLocalRing GlobalTheory.EtC LateralTheory.E.E4

namespace LateralTheory.E.LeafClosedSHPosPf

theorem hens_of_surj {A B : Type} [CommRing A] [CommRing B] [HenselianLocalRing A] [Nontrivial B]
    (φ : A →+* B) (hφ : Function.Surjective φ) : HenselianLocalRing B := by
  have := IsLocalHom.of_surjective φ hφ
  have : IsLocalRing B := IsLocalRing.of_surjective φ hφ
  refine { is_henselian := ?_ }
  intro f hf a₀ h₁ h₂
  have hl : f ∈ Polynomial.lifts φ := (Polynomial.lifts_iff_coeff_lifts f).2 (fun n => hφ _)
  obtain ⟨g, hg, -, hgm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hl hf
  obtain ⟨b₀, rfl⟩ := hφ a₀
  have hev : ∀ (p : A[X]) (x : A), (p.map φ).eval (φ x) = φ (p.eval x) := fun p x => by
    rw [Polynomial.eval_map, eval₂_at_apply]
  subst hg
  have h1 : g.eval b₀ ∈ maximalIdeal A := by
    rw [hev] at h₁
    exact (mem_maximalIdeal _).2 (fun hu => (mem_maximalIdeal _).1 h₁ (hu.map φ))
  have h2 : IsUnit (g.derivative.eval b₀) := by
    rw [derivative_map, hev] at h₂
    exact IsUnit.of_map φ _ h₂
  obtain ⟨a, ha, ham⟩ := HenselianLocalRing.is_henselian g hgm b₀ h1 h2
  refine ⟨φ a, ?_, ?_⟩
  · rw [IsRoot, hev, ha.eq_zero, map_zero]
  · rw [← map_sub]
    exact (mem_maximalIdeal _).2 (fun hu => (mem_maximalIdeal _).1 ham (IsUnit.of_map φ _ hu))

theorem sepClosed_of_surj {A B : Type} [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B]
    (φ : A →+* B) [IsLocalHom φ] (hφ : Function.Surjective φ) [IsSepClosed (ResidueField A)] :
    IsSepClosed (ResidueField B) := by
  have hs : Function.Surjective (ResidueField.map φ) := by
    intro y
    obtain ⟨b, rfl⟩ := residue_surjective y
    obtain ⟨a, rfl⟩ := hφ b
    exact ⟨residue A a, ResidueField.map_residue φ a⟩
  let e : ResidueField A ≃+* ResidueField B :=
    RingEquiv.ofBijective (ResidueField.map φ) ⟨(ResidueField.map φ).injective, hs⟩
  refine ⟨fun p hp => ?_⟩
  have h1 : (p.map (e.symm : ResidueField B →+* ResidueField A)).Separable := hp.map
  have h2 := (IsSepClosed.splits_of_separable _ h1).map (e : ResidueField A →+* ResidueField B)
  rw [Polynomial.map_map] at h2
  convert h2
  ext x; simp

theorem sub_of_iso {X Y : Scheme.{0}} (e : X ≅ Y) (R : Type) [CommRing R] (F : Shv R) (n : ℤ)
    (h : Subsingleton (H R (sch.obj Y) F n)) : Subsingleton (H R (sch.obj X) F n) := by
  refine ⟨fun x y => ?_⟩
  have key : ∀ z : H R (sch.obj X) F n,
      z = pull R (sch.map e.hom) F n (pull R (sch.map e.inv) F n z) := by
    intro z
    rw [← pull_comp, ← CategoryTheory.Functor.map_comp, e.hom_inv_id, CategoryTheory.Functor.map_id, pull_id]
  rw [key x, key y, Subsingleton.elim (pull R (sch.map e.inv) F n x) (pull R (sch.map e.inv) F n y)]

theorem sub_of_empty (hy : Hyps) (R : Type) [CommRing R] (F : Shv R) (W : Scheme.{0}) [IsEmpty W] (n : ℤ)
    (hn : 0 < n) : Subsingleton (H R (sch.obj W) F n) := by
  have a5 : A5 := hy.2.2.2.2.1
  suffices h : ∀ x : H R (sch.obj W) F n, x = 0 from ⟨fun a b => by rw [h a, h b]⟩
  intro x
  obtain ⟨Z, f, -, -, hf⟩ := a5 R W F n hn x
  have : IsEmpty Z := ⟨fun z => isEmptyElim (f.base z)⟩
  let g : W ⟶ Z := (isInitialOfIsEmpty (X := W)).to Z
  have hgf : g ≫ f = 𝟙 W := (isInitialOfIsEmpty (X := W)).hom_ext _ _
  have : pull R (sch.map (g ≫ f)) F n x = x := by rw [hgf, CategoryTheory.Functor.map_id, pull_id]
  rw [← this, CategoryTheory.Functor.map_comp, pull_comp, hf, map_zero]

theorem LeafClosedSHPos_of : LateralTheory.E.LeafVanBPf.LeafClosedSHPos := by
  intro hy q _ i A _ _ hA hq W' ι' _ n hn
  rcases isEmpty_or_nonempty W' with hW | ⟨⟨w⟩⟩
  · exact sub_of_empty hy _ _ W' n hn
  obtain ⟨hAff, hsurj⟩ := IsClosedImmersion.isAffine_surjective_of_isAffine ι'
  let B : Type := Γ(W', ⊤)
  let ψ : A →+* B := (ι'.appTop).hom.comp (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom
  have hψ : Function.Surjective ψ := hsurj.comp
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of A)).inv).2
  have : Nontrivial B := by
    by_contra hB
    rw [not_nontrivial_iff_subsingleton] at hB
    let p := W'.isoSpec.hom.base w
    exact p.isPrime.ne_top (Subsingleton.elim _ _)
  obtain ⟨hH, hS⟩ := hA
  have := IsLocalHom.of_surjective ψ hψ
  have hHB : HenselianLocalRing B := hens_of_surj ψ hψ
  have hSB : SH B := ⟨hHB, sepClosed_of_surj ψ hψ⟩
  have h2 := LateralTheory.E.LeafVanBPf.heightFunctionalStatement_of_pairingProperties hy (ZMod q) B hSB (tw q i) n hn
  exact sub_of_iso W'.isoSpec (ZMod q) (tw q i) n h2

end LateralTheory.E.LeafClosedSHPosPf
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex CochainComplex.HomComplex

namespace LateralTheory.E.LeafVanVPf

theorem free_empty (R : Type) [CommRing R] (X : Scheme.{0}) [IsEmpty X] : IsZero ((free R).obj (yoneda.obj X)) := by
  have key : ∀ (F : Shv R) (f g : (freeP R).obj (yoneda.obj X) ⟶ F.obj), f = g := by
    intro F f g
    ext1
    funext U
    by_cases hU : IsEmpty U.unop
    · have hb : ⊥ ∈ Scheme.etaleTopology U.unop := Scheme.bot_mem_grothendieckTopology _
      exact (Sheaf.isTerminalOfBotCover F U.unop hb).hom_ext _ _
    · apply ModuleCat.free_hom_ext
      rintro ⟨x⟩
      exfalso
      apply hU
      exact ⟨fun u => IsEmpty.false ((show U.unop ⟶ X from x) u)⟩
  rw [IsZero.iff_id_eq_zero]
  apply ((sheafificationAdjunction Scheme.etaleTopology (ModuleCat.{1} (ULift.{1} R))).homEquiv _ _).injective
  exact key _ _ _

theorem chains_empty (R : Type) [CommRing R] (X : Scheme.{0}) [IsEmpty X] (n : ℤ) :
    IsZero (((chains R).obj (sch.obj X)).X n) := by
  by_cases h : n ≤ 0
  · obtain ⟨p, rfl⟩ : ∃ p : ℕ, n = -(p : ℤ) := ⟨(-n).toNat, by omega⟩
    exact (free_empty R X).of_iso (chainsXIso R _ p)
  · refine HomologicalComplex.isZero_extend_X ((chainsN R).obj (sch.obj X)) ComplexShape.embeddingDownNat n ?_
    intro i hi
    change -(i : ℤ) = n at hi
    omega

theorem isIso_inr {C : Type*} [Category C] [Abelian C] {K L : CochainComplex C ℤ} (φ : K ⟶ L)
    (h : ∀ n, IsZero (K.X n)) : IsIso (mappingCone.inr φ) := by
  have : ∀ n, IsIso ((mappingCone.inr φ).f n) := fun n =>
    ⟨(mappingCone.snd φ).v n n (add_zero n), by simp, by
      rw [← mappingCone.id_X φ n (n + 1) rfl, (h (n + 1)).eq_of_tgt ((mappingCone.fst φ).1.v n (n + 1) rfl) 0]
      simp⟩
  exact HomologicalComplex.Hom.isIso_of_components _

theorem subsingleton_of_iso {R : Type} [CommRing R] {K L : Cx R} (f : K ⟶ L) [IsIso f] (F : Shv R) (m : ℤ)
    (h : Subsingleton (HK R K F m)) : Subsingleton (HK R L F m) := by
  have key : ∀ x : HK R L F m, HK.pull R (inv f) F m (HK.pull R f F m x) = x := by
    intro x
    obtain ⟨x, rfl⟩ := x.mk_surjective
    refine congrArg CohomologyClass.mk (Cocycle.ext ?_)
    simp only [zcomp, Cocycle.mk_coe, Cocycle.ofHom_coe]
    rw [← Cochain.comp_assoc_of_first_is_zero_cochain, ← Cochain.ofHom_comp, IsIso.inv_hom_id, Cochain.id_comp]
  exact ⟨fun x y => by rw [← key x, ← key y, Subsingleton.elim (HK.pull R f F m x) (HK.pull R f F m y)]⟩

theorem LeafVanV_of : LateralTheory.E.LeafVan0Pf.LeafVanV := by
  intro _ q _ i B W Y S ι p s hs m hm
  have he : IsEmpty ↥(pullback (pullback.snd p s ≫ s) ι : Scheme.{0}) := ⟨fun z => by
    refine hs (pullback.snd p s (pullback.fst (pullback.snd p s ≫ s) ι z)) ⟨pullback.snd (pullback.snd p s ≫ s) ι z, ?_⟩
    have hc := congrArg (fun f => f z) (pullback.condition (f := pullback.snd p s ≫ s) (g := ι))
    simpa using hc.symm⟩
  have := isIso_inr ((chains (ZMod q)).map (sch.map (LateralTheory.E.LeafVan0Pf.prS p ι s))) (chains_empty _ _)
  exact subsingleton_of_iso (mappingCone.inr _) _ m hm

end LateralTheory.E.LeafVanVPf
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.E.LeafVanBStalkPf
open LateralTheory.E.E4 LateralTheory.E.LeafGhostCut LateralTheory.E.EtaleTopologySheaves LateralTheory.E.LeafDegCut LateralTheory.E.LeafVanBPf

theorem hkpull_comp (R : Type) [CommRing R] {K L M : Cx R} (f : K ⟶ L) (g : L ⟶ M) (F : Shv R) (n : ℤ)
    (y : HK R M F n) : HK.pull R (f ≫ g) F n y = HK.pull R f F n (HK.pull R g F n y) := by
  obtain ⟨y, rfl⟩ := y.mk_surjective
  refine congrArg CohomologyClass.mk (Cocycle.ext ?_)
  simp only [zcomp, Cocycle.mk_coe, Cocycle.ofHom_coe]
  rw [Cochain.ofHom_comp, Cochain.comp_assoc_of_first_is_zero_cochain]

theorem rmap_comp (R : Type) [CommRing R] {U E U' E' U'' E'' : Spc} (f : U ⟶ E) (f' : U' ⟶ E') (f'' : U'' ⟶ E'')
    (u : U' ⟶ U) (e : E' ⟶ E) (u' : U'' ⟶ U') (e' : E'' ⟶ E') (c1 : f' ≫ e = u ≫ f) (c2 : f'' ≫ e' = u' ≫ f')
    (c3 : f'' ≫ (e' ≫ e) = (u' ≫ u) ≫ f) :
    rmap R f f'' (u' ≫ u) (e' ≫ e) c3 = rmap R f' f'' u' e' c2 ≫ rmap R f f' u e c1 := by
  refine HomologicalComplex.hom_ext _ _ (fun n => ?_)
  rw [mappingCone.ext_from_iff _ (n + 1) n rfl]
  simp [rmap, mappingCone.map]

theorem rpull_comp (R : Type) [CommRing R] {U E U' E' U'' E'' : Spc} (f : U ⟶ E) (f' : U' ⟶ E') (f'' : U'' ⟶ E'')
    (u : U' ⟶ U) (e : E' ⟶ E) (u' : U'' ⟶ U') (e' : E'' ⟶ E') (c1 : f' ≫ e = u ≫ f) (c2 : f'' ≫ e' = u' ≫ f')
    (c3 : f'' ≫ (e' ≫ e) = (u' ≫ u) ≫ f) (F : Shv R) (n : ℤ) (y : Hrel R f F n) :
    rpull R f f'' (u' ≫ u) (e' ≫ e) c3 F n y = rpull R f' f'' u' e' c2 F n (rpull R f f' u e c1 F n y) := by
  simp only [rpull]
  rw [rmap_comp R f f' f'' u e u' e' c1 c2 c3, hkpull_comp]

theorem rpull_congr (R : Type) [CommRing R] {U E U' E' : Spc} (f : U ⟶ E) (f' : U' ⟶ E') {u u₀ : U' ⟶ U}
    {e e₀ : E' ⟶ E} (hu : u = u₀) (he : e = e₀) (c : f' ≫ e = u ≫ f) (c₀ : f' ≫ e₀ = u₀ ≫ f) (F : Shv R) (n : ℤ) :
    rpull R f f' u e c F n = rpull R f f' u₀ e₀ c₀ F n := by
  subst hu he; rfl

theorem rB_comp (q : ℕ) (i : ℤ) {B W : Scheme.{0}} (ι : W ⟶ B) {U U' U'' : B.Etale} (a : U' ⟶ U) (b : U'' ⟶ U')
    (m : ℤ) (c : Hrel (ZMod q) (sch.map (prB ι U)) (tw q i) m) :
    rB q i ι (b ≫ a) m c = rB q i ι b m (rB q i ι a m c) := by
  have h1 : resBW ι (b ≫ a) = resBW ι b ≫ resBW ι a := by
    apply pullback.hom_ext <;>
      simp only [resBW, pullback.map, Category.assoc, pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc,
        pullback.lift_snd_assoc] <;> rfl
  have h2 : (b ≫ a).left = b.left ≫ a.left := rfl
  simp only [rB, rpl]
  rw [rpull_congr (ZMod q) _ _ (show sch.map (resBW ι (b ≫ a)) = sch.map (resBW ι b) ≫ sch.map (resBW ι a) by
      rw [h1, Functor.map_comp])
    (show sch.map (b ≫ a).left = sch.map b.left ≫ sch.map a.left by rw [h2, Functor.map_comp]) _
    (by rw [← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp, ← h1, ← h2,
      pullback.lift_fst])]
  exact rpull_comp (ZMod q) _ _ _ _ _ _ _ _ _ _ (tw q i) m c

structure SHSys {B : Scheme.{0}} (U : B.Etale) (x : U.left) where
  J : Type
  [cat : SmallCategory J]
  [filt : IsFiltered J]
  D : J ⥤ CommRingCat.{0}
  V : J → B.Etale
  a : ∀ j, V j ⟶ U
  e : ∀ j, (V j).left ≅ Spec (D.obj j)
  tr : ∀ {j j' : J} (_ : j ⟶ j'), V j' ⟶ V j
  tr_a : ∀ {j j' : J} (g : j ⟶ j'), tr g ≫ a j = a j'
  tr_spec : ∀ {j j' : J} (g : j ⟶ j'), (e j').inv ≫ (tr g).left ≫ (e j).hom = Spec.map (D.map g)
  hx : ∀ j, x ∈ Set.range (a j).left
  c : Cocone D
  hc : IsColimit c
  sh : SH c.pt
  t : Spec c.pt ⟶ U.left
  ht : ∀ j, t = Spec.map (c.ι.app j) ≫ (e j).inv ≫ (a j).left

attribute [instance] SHSys.cat SHSys.filt

def LeafSHSys : Prop := ∀ {B : Scheme.{0}} (U : B.Etale) (x : U.left), Nonempty (SHSys U x)

def LeafSHCont : Prop := Hyps → ∀ (q : ℕ) [NeZero q] (k : Type) [Field k], IsUnit (q : k) → ∀ (i : ℤ)
  {B W : Scheme.{0}} (_ : B ⟶ Sp k) (ι : W ⟶ B) [IsClosedImmersion ι] (U : B.Etale) (m : ℤ)
  (c : Hrel (ZMod q) (sch.map (prB ι U)) (tw q i) m) (x : U.left) (S : SHSys U x),
  bpl q i ι U S.t m c = 0 → ∃ j, rB q i ι (S.a j) m c = 0

def LeafStalkPt : Prop := Hyps → ∀ (q : ℕ) [NeZero q] (k : Type) [Field k], IsUnit (q : k) → ∀ (i : ℤ)
  {B W : Scheme.{0}} (_ : B ⟶ Sp k) (ι : W ⟶ B) [IsClosedImmersion ι] (U : B.Etale) (m : ℤ)
  (c : Hrel (ZMod q) (sch.map (prB ι U)) (tw q i) m),
  (∀ (A : Type) [CommRing A] [IsLocalRing A] (t : Sp A ⟶ U.left), SH A → IsUnit (q : A) → bpl q i ι U t m c = 0) →
  ∀ x : U.left, ∃ (V : B.Etale) (a : V ⟶ U), x ∈ Set.range a.left ∧ rB q i ι a m c = 0

theorem cov_of_pts {B W : Scheme.{0}} (q : ℕ) (i : ℤ) (ι : W ⟶ B) (U : B.Etale) (m : ℤ)
    (c : Hrel (ZMod q) (sch.map (prB ι U)) (tw q i) m)
    (h : ∀ x : U.left, ∃ (V : B.Etale) (a : V ⟶ U), x ∈ Set.range a.left ∧ rB q i ι a m c = 0) :
    Cov U (fun _ a => rB q i ι a m c = 0) := by
  choose V a hx hz using h
  refine ⟨Sieve.ofArrows V a, ?_, ?_⟩
  · rw [Scheme.ofArrows_mem_smallEtaleTopology_iff]
    ext x; simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    exact ⟨x, hx x⟩
  · intro U' g hg
    rw [Sieve.mem_ofArrows_iff] at hg
    obtain ⟨x, b, rfl⟩ := hg
    rw [rB_comp, hz x, map_zero]

theorem stalkPt_of (hN : LeafSHSys) (hC : LeafSHCont) : LeafStalkPt := by
  intro hy q _ k _ hq i B W s ι _ U m c hc x
  obtain ⟨S⟩ := hN U x
  have hu : IsUnit (q : S.c.pt) := by
    have g := Spec.preimage (S.t ≫ U.hom ≫ s)
    simpa using hq.map g.hom
  haveI : IsLocalRing S.c.pt := S.sh.1.toIsLocalRing
  have h0 := hc S.c.pt S.t S.sh hu
  obtain ⟨j, hj⟩ := hC hy q k hq i s ι U m c x S h0
  exact ⟨S.V j, S.a j, S.hx j, hj⟩

theorem LeafVanBStalk_of_pt (hP : LeafStalkPt) : LeafVanBStalk := by
  intro hy q _ k _ hq i B W s ι _ U m c hc
  exact cov_of_pts q i ι U m c (hP hy q k hq i s ι U m c hc)

end LateralTheory.E.LeafVanBStalkPf
end
end
