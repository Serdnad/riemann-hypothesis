module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.Bundle011
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.OrdReadOf
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PairCalc
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
open GlobalTheory.IwLevel (InSub IsIsogDeg)
open GlobalTheory.AbDual (evc IsAdditive swap)
attribute [local instance] Ideal.Quotient.field
open UpperTheory.Gal.crystallineComparison UpperTheory.Gal.crystallineComparison.Mod

private theorem etale_restrict_of_isPullback {X Y W Z : Scheme.{0}} {h : Y ⟶ X} {t : W ⟶ X} {s : Z ⟶ Y} {g : Z ⟶ W}
    (hpb : IsPullback s g h t) (U : X.Opens) (ht : Etale (t ∣_ U)) : Etale (s ∣_ (h ⁻¹ᵁ U)) := by
  have P1 := isPullback_morphismRestrict t U
  have P2 := isPullback_morphismRestrict s (h ⁻¹ᵁ U)
  have P3 := isPullback_morphismRestrict h U
  have hcomm : ((s ∣_ (h ⁻¹ᵁ U)) ≫ (h ∣_ U)) ≫ U.ι = (s ⁻¹ᵁ (h ⁻¹ᵁ U)).ι ≫ g ≫ t := by
    rw [Category.assoc, morphismRestrict_ι, ← Category.assoc, morphismRestrict_ι, Category.assoc, hpb.w]
  let top : (s ⁻¹ᵁ (h ⁻¹ᵁ U)).toScheme ⟶ (t ⁻¹ᵁ U).toScheme :=
    P1.lift ((s ∣_ (h ⁻¹ᵁ U)) ≫ (h ∣_ U)) ((s ⁻¹ᵁ (h ⁻¹ᵁ U)).ι ≫ g) (by rw [hcomm, Category.assoc])
  have htop₁ : top ≫ (t ∣_ U) = (s ∣_ (h ⁻¹ᵁ U)) ≫ (h ∣_ U) := P1.lift_fst _ _ _
  have htop₂ : top ≫ (t ⁻¹ᵁ U).ι = (s ⁻¹ᵁ (h ⁻¹ᵁ U)).ι ≫ g := P1.lift_snd _ _ _
  have pasted := P2.flip.paste_horiz hpb.flip
  have pasted' : IsPullback (top ≫ (t ⁻¹ᵁ U).ι) (s ∣_ (h ⁻¹ᵁ U)) t ((h ∣_ U) ≫ U.ι) := by
    rw [htop₂, morphismRestrict_ι]; exact pasted
  have left : IsPullback top (s ∣_ (h ⁻¹ᵁ U)) (t ∣_ U) (h ∣_ U) :=
    IsPullback.of_right pasted' htop₁ P1.flip
  exact MorphismProperty.of_isPullback (P := @Etale) left ht

theorem UpperTheory.Gal.crystallineComparison.Mod.corrBC_of :
    WModEx → RankN → SecEquiv → GrCard → CorrBC := by
  intro hW hR hS hG p _ D O _ _ _ _ f b N r w _ hstd M j hj T Y Z h s g hpb
  refine ⟨?_, ?_, ?_⟩
  · have := T.fin
    exact MorphismProperty.of_isPullback (P := @IsFinite) hpb.flip this
  · have hV : Y.basicOpen ((p : ℕ) : Γ(Y, ⊤)) = h ⁻¹ᵁ M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤)) := by
      rw [Scheme.preimage_basicOpen_top, map_natCast]
    rw [hV]
    exact etale_restrict_of_isPullback hpb _ T.et
  · intro K _ _ hp y
    haveI : ValuationRing K := ValuationRing.of_field K
    haveI : IsAlgClosed (FractionRing K) :=
      IsAlgClosed.of_ringEquiv K (FractionRing K) (FractionRing.algEquiv K K).symm.toRingEquiv
    obtain ⟨W⟩ := hW p D O b N M.X M.s M.univ w (Over.mk (y ≫ h))
    obtain ⟨hfin, hrk⟩ := hR p D O f b N r w hstd M K hp (y ≫ h) W
    obtain ⟨e, -⟩ := hS p D O f b N r w hstd M j hj T K hp (y ≫ h) W
    let E : {z : Spec (CommRingCat.of K) ⟶ Z // z ≫ s = y} ≃ {z : Sp K ⟶ T.Y // z ≫ T.s = y ≫ h} :=
      { toFun := fun z => ⟨z.1 ≫ g, by rw [Category.assoc, ← hpb.w, ← Category.assoc, z.2]⟩
        invFun := fun z => ⟨hpb.lift y z.1 z.2.symm, hpb.lift_fst _ _ _⟩
        left_inv := fun z => Subtype.ext (hpb.hom_ext (by rw [hpb.lift_fst, z.2]) (by rw [hpb.lift_snd]))
        right_inv := fun z => Subtype.ext (hpb.lift_snd _ _ _) }
    rw [Nat.card_congr E, Nat.card_congr e]
    exact hG _ _ _ _ hrk
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
open GlobalTheory.IwLevel (InSub IsIsogDeg)
open GlobalTheory.AbDual (evc IsAdditive swap)
attribute [local instance] Ideal.Quotient.field
open UpperTheory.Gal.crystallineComparison UpperTheory.Gal.crystallineComparison.Mod

theorem UpperTheory.Gal.crystallineComparison.Mod.kerRead_of :
    KerU → FFRead → LiftFF → PullKer → WVal → KerRead := by
  intro hKU hFF hLF hPK hWV p _ D O _ _ _ _ f b N r w _ hS M j T V _ _ _ _ hp x z hz σ o₁ m₁ P
  haveI := M.smooth
  haveI := T.fin
  haveI : Smooth M.s := SmoothOfRelativeDimension.smooth (D.a * (D.n - 1)) M.s
  haveI : LocallyOfFiniteType M.s := inferInstance
  haveI : IsLocallyNoetherian M.X := LocallyOfFiniteType.isLocallyNoetherian M.s
  haveI : IsLocallyNoetherian T.Y := LocallyOfFiniteType.isLocallyNoetherian T.s
  have hcz : CharZero (FractionRing V) := by
    obtain ⟨φ, hφ⟩ := Spec.map_surjective (x ≫ M.s)
    have key : ∀ n : ℕ, n ≠ 0 → (n : V) ≠ 0 := by
      intro n hn
      obtain ⟨e, m, hm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn p (Fact.out : p.Prime).ne_one
      have hmu : IsUnit (m : O) :=
        b.unit m ((Nat.Prime.coprime_iff_not_dvd (Fact.out : p.Prime)).mpr hm).symm
      have hmV : IsUnit (m : V) := by simpa using hmu.map φ.hom
      push_cast
      exact mul_ne_zero (pow_ne_zero _ hp) hmV.ne_zero
    refine charZero_of_inj_zero fun n hn => by_contra fun h => key n h ?_
    rw [← map_natCast (algebraMap V (FractionRing V))] at hn
    exact IsFractionRing.injective V (FractionRing V) (by simpa using hn)
  obtain ⟨-, hmon, hact, -, -, ψ', hmon', h1, h2⟩ := T.isog
  obtain ⟨hRep, -, hKill⟩ := hKU p D O b N r w (Ideal.IsMaximal.ne_top ‹_›) hS.ule T.Y (T.s ≫ M.s)
    T.o T.o' T.ψ ψ' (f * j) hmon hmon' hact h1 h2
  have ukerComp : ∀ {T1 T2 : Over T.Y} (u : T1 ⟶ T2) (g : T2 ⟶ T.o.A),
      UKer r T.o T.ψ T2 g → UKer r T.o T.ψ T1 (u ≫ g) := by
    intro T1 T2 u g hg
    obtain ⟨hg1, e, hg2⟩ := hg
    exact ⟨by rw [Category.assoc, hg1, comp_one], e, fun c hc => by rw [Category.assoc, hg2 c hc, comp_one]⟩
  have compat : ∀ (T' : Over (Sp (IsLocalRing.ResidueField V))) (g : T' ⟶ o₁.A)
      (g₀ : Over.mk (T'.hom ≫ resPt V ≫ z) ⟶ T.o.A), g₀.left = g.left ≫ P.m₀.φ →
      (UKer r o₁ P.ψ T' g ↔ UKer r T.o T.ψ (Over.mk (T'.hom ≫ resPt V ≫ z)) g₀) := by
    intro T' g g₀ hg
    obtain ⟨hA, -, hC⟩ := (hPK _ _ _ _ _ _ _ _ _ _ _ _ _ _ P.m₀ P.m' T.ψ P.ψ P.sq).1 T'
      (Over.mk (T'.hom ≫ resPt V ≫ z)) rfl g g₀ (by simpa using hg)
    simp only [UKer, hA, hC]
  have HT := (hPK _ _ _ _ _ _ _ _ _ _ _ _ _ _ T.ms T.ms (𝟙 M.univ.A) (𝟙 T.o.A) (by simp)).1
  have hwu : ∀ (T' : Over T.Y) (g : T' ⟶ T.o.A), KilledBy T.o w g →
      (UKer r T.o T.ψ T' g ↔ g ≫ T.ψ = 1) := by
    intro T' g hg
    exact ⟨fun h => h.1, fun h => ⟨h, 1, fun c hc => hg c (hS.ule (by simpa using hc))⟩⟩
  have hcard : Nat.card {g // UKer r T.o T.ψ
      (Over.mk (spMap (algebraMap V (FractionRing V)) ≫ z)) g} = (p ^ f) ^ j := by
    have htj := T.tj (FractionRing V) (spMap (algebraMap V (FractionRing V)) ≫ z)
    have he : ∀ g, UKer r T.o T.ψ (Over.mk (spMap (algebraMap V (FractionRing V)) ≫ z)) g ↔
        (g ≫ T.ψ = 1 ∧ KilledBy T.o w g) := by
      intro g
      constructor
      · intro hg
        exact ⟨hg.1, htj.1 g hg.1 hg.2⟩
      · intro hg
        exact (hwu _ g hg.2).mpr hg.1
    rw [Nat.card_congr (Equiv.subtypeEquivRight he), htj.2, hS.norm, hS.m1, _root_.one_mul]
  refine ⟨?_, fun a => ?_⟩
  · have hc : ((p ^ (f * j) : ℕ) : V) ≠ 0 := by
      push_cast
      exact pow_ne_zero _ hp
    have hR := hFF T.Y T.o.A T.o.ab (UKer r T.o T.ψ) hRep (p ^ (f * j)) hKill V hc z o₁.A P.m₀.φ
      P.m₀.cart.1 (UKer r o₁ P.ψ) compat
    rwa [hcard] at hR
  have hw0 : (a.left ≫ P.m₀.φ) ≫ T.o.A.hom = (Over.mk ((𝟙_ (Over _)).hom ≫ resPt V ≫ z)).hom := by
    rw [Category.assoc, P.m₀.cart.1.w, ← Category.assoc, Over.w a]
    rfl
  let a₀ : Over.mk ((𝟙_ (Over _)).hom ≫ resPt V ≫ z) ⟶ T.o.A := Over.homMk (a.left ≫ P.m₀.φ) hw0
  have hiff : UKer r o₁ P.ψ _ a ↔ UKer r T.o T.ψ _ a₀ := compat _ a a₀ rfl
  rw [hiff]
  constructor
  · intro ha₀
    obtain ⟨K, i, -, hfin, hflat, hK⟩ := hRep
    obtain ⟨y0, hy0⟩ := (hK _ a₀).mpr ha₀
    obtain ⟨g', hg'1, hg'2⟩ := hLF T.Y K.left K.hom hfin hflat V z y0.left
      ((Over.w y0).trans (Category.id_comp _))
    have hw1 : (g' ≫ i.left) ≫ T.o.A.hom = (Over.mk z).hom := by
      rw [Category.assoc, Over.w i, hg'1]
      rfl
    let a' : Over.mk z ⟶ T.o.A := Over.homMk (g' ≫ i.left) hw1
    have ha' : UKer r T.o T.ψ _ a' := (hK _ a').mp ⟨Over.homMk g' hg'1, by
      apply Over.OverMorphism.ext
      simp [a']⟩
    have hUi : resPt V ≫ a'.left = a.left ≫ P.m₀.φ := by
      have e1 := congrArg CommaMorphism.left hy0
      simp only [Over.comp_left, Over.homMk_left, a₀] at e1
      simp only [a', Over.homMk_left]
      rw [← Category.assoc, hg'2, e1]
    have hw2 : (a'.left ≫ T.ms.φ) ≫ M.univ.A.hom = (Over.mk x).hom := by
      rw [Category.assoc, T.ms.cart.1.w, ← Category.assoc, Over.w a']
      exact hz
    let g : Over.mk x ⟶ M.univ.A := Over.homMk (a'.left ≫ T.ms.φ) hw2
    refine ⟨g, ?_, ?_, ?_⟩
    · obtain ⟨ρ, hρl, -, hρk, -⟩ := hWV p D O b N M w V x
      rw [hρk]
      let rz : Over.mk (spMap (algebraMap V (FractionRing V)) ≫ z) ⟶ Over.mk z :=
        Over.homMk (spMap (algebraMap V (FractionRing V))) rfl
      have hag := ukerComp rz a' ha'
      have hkill := (T.tj (FractionRing V) (spMap (algebraMap V (FractionRing V)) ≫ z)).1
        (rz ≫ a') hag.1 hag.2
      refine ((HT (Over.mk (spMap (algebraMap V (FractionRing V)) ≫ z))
        (Over.mk (spMap (algebraMap V (FractionRing V)) ≫ x)) rfl (rz ≫ a') (ρ g) ?_).2.2 w).mp hkill
      rw [hρl]
      simp [rz, g]
    · intro a'' ha''
      have e : a'' = a' := by
        apply Over.OverMorphism.ext
        exact T.ms.cart.1.hom_ext (by simpa [g] using ha'') ((Over.w a'').trans (Over.w a').symm)
      rw [e]
      exact ha'.1
    · simp only [g, Over.homMk_left]
      rw [← P.tri, ← Category.assoc, ← hUi, Category.assoc]
  · rintro ⟨g, hgk, hgker, hgeq⟩
    have hw3 : g.left ≫ M.univ.A.hom = z ≫ T.s := (Over.w g).trans hz.symm
    let a' : Over.mk z ⟶ T.o.A := Over.homMk (T.ms.cart.1.lift g.left z hw3) (T.ms.cart.1.lift_snd _ _ _)
    have ha'l : a'.left ≫ T.ms.φ = g.left := T.ms.cart.1.lift_fst _ _ _
    have hk' : KilledBy T.o w a' :=
      ((HT (Over.mk z) (Over.mk x) rfl a' g (by simp [ha'l])).2.2 w).mpr hgk
    have ha' : UKer r T.o T.ψ _ a' := (hwu _ a' hk').mpr (hgker a' ha'l)
    let rp : Over.mk ((𝟙_ (Over _)).hom ≫ resPt V ≫ z) ⟶ Over.mk z :=
      Over.homMk (resPt V) (Category.id_comp _).symm
    have e : a₀ = rp ≫ a' := by
      apply Over.OverMorphism.ext
      simp only [a₀, rp, Over.homMk_left, Over.comp_left]
      apply T.ms.cart.1.hom_ext
      · rw [Category.assoc, P.tri, Category.assoc, ha'l, hgeq]
      · rw [hw0, Category.assoc, Over.w a']
        exact Category.id_comp _
    rw [e]
    exact ukerComp rp a' ha'
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
open GlobalTheory.IwLevel (InSub IsIsogDeg)
open GlobalTheory.AbDual (evc IsAdditive swap)
attribute [local instance] Ideal.Quotient.field
open UpperTheory.Gal.crystallineComparison UpperTheory.Gal.crystallineComparison.Mod

theorem UpperTheory.Gal.crystallineComparison.Mod.pulledRead_of :
    PullKer → PulledRead := by
  intro hKer p _ D R _ b N M r w j c T S x σ o₁ m₁ y hy P a
  have hw : (a.left ≫ P.m₀.φ) ≫ T.o.A.hom = y := by
    have h1 := P.m₀.cart.1.w
    have h2 : a.left ≫ o₁.A.hom = 𝟙 S := Over.w a
    rw [Category.assoc, h1, ← Category.assoc, h2]
    exact Category.id_comp y
  have htri : (a.left ≫ P.m₀.φ) ≫ T.ms.φ = a.left ≫ m₁.φ := by
    rw [Category.assoc, P.tri]
  let a₀ : Over.mk y ⟶ T.o.A := Over.homMk (a.left ≫ P.m₀.φ) hw
  have ha₀ : a₀.left = a.left ≫ P.m₀.φ := rfl
  have hk := ((hKer p D R b N T.Y S (T.s ≫ M.s) σ y T.o T.o' o₁ P.o' P.m₀ P.m' T.ψ P.ψ P.sq).1
    (𝟙_ (Over S)) (Over.mk y) rfl a a₀ (by simp [ha₀])).1
  refine ⟨⟨fun h a' ha' => ?_, fun h => ?_⟩, fun h => ?_⟩
  · have hEq : a' = a₀ := by
      apply Over.OverMorphism.ext
      apply T.ms.cart.1.hom_ext
      · rw [ha', ha₀, htri]
      · have h3 : a'.left ≫ T.o.A.hom = y := Over.w a'
        rw [h3, ha₀, hw]
    rw [hEq]
    exact hk.1 h
  · exact hk.2 (h a₀ (by rw [ha₀, htri]))
  · have hl : T.ms.cart.1.lift (a.left ≫ m₁.φ) y h = a.left ≫ P.m₀.φ := by
      apply T.ms.cart.1.hom_ext
      · rw [T.ms.cart.1.lift_fst, htri]
      · rw [T.ms.cart.1.lift_snd, hw]
    unfold TjD.img
    rw [hl, Over.comp_left]
    simp only [Category.assoc]
    rw [reassoc_of% P.sq]
end

section

open UpperTheory.Gal.crystallineComparison UpperTheory.Gal.crystallineComparison.Mod

theorem UpperTheory.Gal.crystallineComparison.Mod.splitAlg_of :
    SplitAlg := by
  classical
  intro κ B Λ _ _ _ _ _ _ _ hcard ε g
  have hli := linearIndependent_toLinearMap κ B κ
  haveI : Finite (B →ₐ[κ] κ) := hli.finite
  letI := Fintype.ofFinite (B →ₐ[κ] κ)
  have hspan : Submodule.span κ (Set.range (AlgHom.toLinearMap : (B →ₐ[κ] κ) → B →ₗ[κ] κ)) = ⊤ := by
    apply hli.span_eq_top_of_card_eq_finrank'
    rw [← Nat.card_eq_fintype_card, hcard]
    exact (Subspace.dual_finrank_eq).symm
  have h0 : ∀ x : B, (∀ φ : B →ₐ[κ] κ, φ x = 0) → x = 0 := by
    intro x hx
    rw [← Module.forall_dual_apply_eq_zero_iff κ x]
    intro f
    have hf : f ∈ Submodule.span κ (Set.range (AlgHom.toLinearMap : (B →ₐ[κ] κ) → B →ₗ[κ] κ)) := by
      rw [hspan]; exact Submodule.mem_top
    induction hf using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨φ, rfl⟩ := hy
      exact hx φ
    | zero => rfl
    | add y z _ _ hy hz => simp [hy, hz]
    | smul a y _ hy => simp [hy]
  have hunit : ∀ y : Λ, ε y ≠ 0 → IsUnit y := by
    intro y hy
    by_contra h
    have hym : y ∈ IsLocalRing.maximalIdeal Λ := h
    have hk : RingHom.ker ε.toRingHom ≤ IsLocalRing.maximalIdeal Λ :=
      IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top _)
    have hd : y - algebraMap κ Λ (ε y) ∈ RingHom.ker ε.toRingHom := by
      rw [RingHom.mem_ker]
      simp
    have hm : algebraMap κ Λ (ε y) ∈ IsLocalRing.maximalIdeal Λ := by
      have := Ideal.sub_mem _ hym (hk hd)
      simpa using this
    exact hm ((isUnit_iff_ne_zero.mpr hy).map (algebraMap κ Λ))
  ext b
  simp only [AlgHom.comp_apply, Algebra.ofId_apply]
  set S : Finset κ := Finset.univ.image (fun φ : B →ₐ[κ] κ => φ b) with hS
  set c := ε (g b) with hc
  have hqb : Polynomial.aeval b (∏ s ∈ S, (Polynomial.X - Polynomial.C s)) = 0 := by
    apply h0
    intro φ
    rw [← Polynomial.aeval_algHom_apply, Polynomial.coe_aeval_eq_eval, Polynomial.eval_prod]
    apply Finset.prod_eq_zero (i := φ b) (by simp [hS])
    simp
  have hq : Polynomial.aeval (g b) (∏ s ∈ S, (Polynomial.X - Polynomial.C s)) = 0 := by
    rw [Polynomial.aeval_algHom_apply, hqb, map_zero]
  have hcS : c ∈ S := by
    have h1 := congrArg ε hq
    rw [← Polynomial.aeval_algHom_apply, map_zero, Polynomial.coe_aeval_eq_eval,
      Polynomial.eval_prod, Finset.prod_eq_zero_iff] at h1
    obtain ⟨s, hs, hs0⟩ := h1
    simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, sub_eq_zero] at hs0
    rw [hc, hs0]
    exact hs
  rw [← Finset.mul_prod_erase S _ hcS, map_mul] at hq
  have hr : IsUnit (Polynomial.aeval (g b) (∏ s ∈ S.erase c, (Polynomial.X - Polynomial.C s))) := by
    apply hunit
    rw [← Polynomial.aeval_algHom_apply, Polynomial.coe_aeval_eq_eval, Polynomial.eval_prod,
      Finset.prod_ne_zero_iff]
    intro s hs
    simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
    exact sub_ne_zero.mpr (Finset.ne_of_mem_erase hs).symm
  have h2 := hr.mul_left_eq_zero.mp hq
  simp only [map_sub, Polynomial.aeval_X, Polynomial.aeval_C] at h2
  exact sub_eq_zero.mp h2
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
open GlobalTheory.IwLevel (InSub IsIsogDeg)
open GlobalTheory.AbDual (evc IsAdditive swap)
attribute [local instance] Ideal.Quotient.field
open UpperTheory.Gal.crystallineComparison UpperTheory.Gal.crystallineComparison.Mod

private theorem tangent_of_form {κ B : Type} [Field κ] [CommRing B] [Algebra κ B] (ε : B →ₐ[κ] κ)
    (d : B →ₗ[κ] κ) (h1 : d 1 = 0) (h2 : ∀ x ∈ RingHom.ker ε.toRingHom ^ 2, d x = 0) :
    ∃ v : B →ₐ[κ] DualNumber κ, (TrivSqZeroExt.fstHom κ κ κ).comp v = ε ∧ ∀ x, (v x).snd = d x := by
  have hmem : ∀ x, x - algebraMap κ B (ε x) ∈ RingHom.ker ε.toRingHom := by
    intro x
    rw [RingHom.mem_ker]
    change ε (x - algebraMap κ B (ε x)) = 0
    rw [map_sub, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply, sub_self]
  have key : ∀ x y, d (x * y) = ε x * d y + ε y * d x := by
    intro x y
    have hm : (x - algebraMap κ B (ε x)) * (y - algebraMap κ B (ε y)) ∈
        RingHom.ker ε.toRingHom ^ 2 := by
      rw [pow_two]
      exact Ideal.mul_mem_mul (hmem x) (hmem y)
    have hz := h2 _ hm
    have e : x * y = (x - algebraMap κ B (ε x)) * (y - algebraMap κ B (ε y)) + ε y • x
        + ε x • y - (ε x * ε y) • (1 : B) := by
      simp only [Algebra.smul_def, map_mul, mul_one]
      ring
    rw [e, map_sub, map_add (f := _), map_add (f := _), hz, map_smul, map_smul, map_smul, h1]
    simp only [smul_eq_mul]
    ring
  let f : B →ₗ[κ] DualNumber κ :=
    { toFun := fun x => TrivSqZeroExt.inl (ε x) + TrivSqZeroExt.inr (d x)
      map_add' := by
        intro x y
        ext <;> simp <;> ring
      map_smul' := by
        intro a x
        ext <;> simp }
  have hf : ∀ x, f x = TrivSqZeroExt.inl (ε x) + TrivSqZeroExt.inr (d x) := fun _ => rfl
  refine ⟨AlgHom.ofLinearMap f ?_ ?_, ?_, ?_⟩
  · rw [hf]
    ext <;> simp [h1]
  · intro x y
    rw [hf, hf, hf]
    ext <;> simp [key] <;> ring
  · ext x
    simp [hf]
  · intro x
    simp [hf]

theorem UpperTheory.Gal.crystallineComparison.Mod.cotanOne_of :
    CotanOne := by
  intro κ B _ _ _ ε v₀ hall
  classical
  let m := RingHom.ker ε.toRingHom
  let s : B → κ := fun x => (v₀ x).snd
  have hs_sub : ∀ x y, s (x - y) = s x - s y := by
    intro x y
    simp [s]
  have hs_smul : ∀ (a : κ) x, s (a • x) = a * s x := by
    intro a x
    simp [s]
  have hkill : ∀ y ∈ m, s y = 0 → y ∈ m ^ 2 := by
    intro y hy hsy
    by_contra hy2
    let P : Submodule κ B := (m ^ 2).restrictScalars κ ⊔ Submodule.span κ {(1 : B)}
    have hyP : y ∉ P := by
      intro hyP
      obtain ⟨z, hz, w, hw, hzw⟩ := Submodule.mem_sup.1 hyP
      obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hw
      have hz' : z ∈ m ^ 2 := hz
      have hzm : z ∈ m := Ideal.pow_le_self two_ne_zero hz'
      have e1 : ε y = ε z + a * ε 1 := by
        rw [← hzw, map_add (f := _), map_smul, smul_eq_mul]
      have hεy : ε y = 0 := hy
      have hεz : ε z = 0 := hzm
      simp only [hεy, hεz, _root_.map_one, zero_add] at e1
      have ha : a = 0 := by simpa using e1.symm
      apply hy2
      rw [← hzw, ha, zero_smul, add_zero]
      exact hz'
    obtain ⟨d, hdy, hdP⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hyP inferInstance
    have hdP' : ∀ p ∈ P, d p = 0 := by
      intro p hp
      have h3 : d p ∈ Submodule.map d P := ⟨p, hp, rfl⟩
      rw [hdP, Submodule.mem_bot] at h3
      exact h3
    have hd1 : d 1 = 0 := hdP' 1 (Submodule.mem_sup_right (Submodule.mem_span_singleton_self 1))
    have hd2 : ∀ x ∈ m ^ 2, d x = 0 := fun x hx => hdP' x (Submodule.mem_sup_left hx)
    obtain ⟨v, hv, hvd⟩ := tangent_of_form ε d hd1 hd2
    obtain ⟨c, hc⟩ := hall v hv
    apply hdy
    rw [← hvd, hc]
    change c * s y = 0
    rw [hsy, mul_zero]
  by_cases hex : ∃ t ∈ m, s t ≠ 0
  · obtain ⟨t, ht, hst⟩ := hex
    refine ⟨t, ht, ?_⟩
    intro x hx
    have hy : x - (s x / s t) • t ∈ m := by
      refine m.sub_mem hx ?_
      rw [Algebra.smul_def]
      exact m.mul_mem_left _ ht
    have hsy : s (x - (s x / s t) • t) = 0 := by
      rw [hs_sub, hs_smul, div_mul_cancel₀ _ hst, sub_self]
    have h2 := hkill _ hy hsy
    have e : x = (s x / s t) • t + (x - (s x / s t) • t) := by abel
    rw [e]
    refine Ideal.add_mem _ (Ideal.mem_sup_left ?_) (Ideal.mem_sup_right h2)
    rw [Algebra.smul_def]
    exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self t)
  · push_neg at hex
    refine ⟨0, m.zero_mem, ?_⟩
    intro x hx
    exact Ideal.mem_sup_right (hkill x hx (hex x hx))
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
open GlobalTheory.IwLevel (InSub IsIsogDeg)
open GlobalTheory.AbDual (evc IsAdditive swap)
attribute [local instance] Ideal.Quotient.field
open UpperTheory.Gal.crystallineComparison UpperTheory.Gal.crystallineComparison.Mod

theorem UpperTheory.Gal.crystallineComparison.Mod.pulledEx_of :
    ObjTri → PullIsog → PullKer → PulledEx := by
  intro hTri hIsog hKer p _ D R _ b N hN hc M r w j c T S x σ hx o₁ m₁ y hy
  obtain ⟨m₀, htri⟩ := (hTri p D R b N hN hc S T.Y M.X σ (T.s ≫ M.s) M.s o₁ T.o M.univ y T.s).2 x hy m₁ T.ms
  have hσ : y ≫ T.s ≫ M.s = σ := by rw [← Category.assoc, hy, hx]
  obtain ⟨o', m', ψ, hisog, hsq⟩ := hIsog p D R b N T.Y S (T.s ≫ M.s) σ y hσ c T.o T.o' T.ψ T.isog o₁ m₀
  have htj := (hKer p D R b N T.Y S (T.s ≫ M.s) σ y T.o T.o' o₁ o' m₀ m' T.ψ ψ hsq).2 r w j T.tj
  exact ⟨⟨o', ψ, m₀, m', hsq, htri, hisog, htj⟩⟩
end
