module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1019
public import Formalism.LocalToGlobal.Divisibility.DivisionHeightBoundStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1029
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1043
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle228
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TaylorIsRingHom
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle243
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1040
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.TopPlaceLogTheta
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle029
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLineBundleDescentToSubfield
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.PublishedTheorems.AbelianLaws.PrincipalPolarisationOneSection
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open scoped ComplexOrder

theorem _root_.GlobalTheory.T.coupled_class_sum_cauchy_schwarz : ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (Q : KerChain K) (v : InfinitePlace K) (t₁ t₂ h₀ h h₁ ny : ℝ), 0 ≤ t₁ → 0 ≤ t₂ → 0 ≤ h₀ → 0 ≤ h → 0 ≤ h₁ → 0 ≤ ny → (∀ b, PosAt ((Q.F Q.n).mem b) v) → PosAt Q.S v → PosAt Q.S₁ v → (∀ b, (Nat.card ((Q.F Q.n).mem b).Cl : ℝ) ≤ h₀) → (Nat.card Q.S.Cl : ℝ) ≤ h → (Nat.card Q.S₁.Cl : ℝ) ≤ h₁ → (∀ d, ((Q.Y.ys d).ncard : ℝ) ≤ ny) → (∀ b d₀ d, ∀ y ∈ Q.Y.ys d, OpLe ((Q.F Q.n).mem b) Q.S v ((Q.cp b).k1 d₀ d y) t₁) → (∀ b d d₁, ∀ y ∈ Q.Y.ys d, OpLe Q.S Q.S₁ v ((Q.cp b).k2 d y d₁) t₂) → ∀ φ : (Q.F Q.n).Forms, (Q.S₁.ipAt Q.hS₁ v (Q.cpl φ) (Q.cpl φ)).re ≤ (Fintype.card (Q.F Q.n).β : ℝ) * h₀ * h ^ 2 * h₁ * ny ^ 2 * t₁ * t₂ * (famIpAt (Q.F Q.n) (Q.hF Q.n) v φ φ).re := by
  first | exact @GlobalTheory.ColNorms.CplCS.cpl_le | exact GlobalTheory.ColNorms.CplCS.cpl_le | (intros; apply GlobalTheory.ColNorms.CplCS.cpl_le <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.DualCon.LiftInduct

theorem same_comp {S : Scheme.{0}} (A : Over S) {T U Y Y' : Over S} {N : LB (A ⊗ T).left} {M : LB (A ⊗ U).left}
    (e : Y' ⟶ Y) {y : Y ⟶ T} {u : Y ⟶ U} (h : Same A N M y u) : Same A N M (e ≫ y) (e ≫ u) :=
  LBIso.chartPull (h := (lift (fst A Y') (snd A Y' ≫ e)).left)
    (chartPullSame N _ _ _ _ fun _ => by
      rw [← Over.comp_left, comp_lift, lift_fst, lift_snd_assoc, Category.assoc])
    (chartPullSame M _ _ _ _ fun _ => by
      rw [← Over.comp_left, comp_lift, lift_fst, lift_snd_assoc, Category.assoc]) h

variable {R : Type} [CommRing R] (A : Over (Sp R)) [GrpObj A] {U : Over (Sp R)} (M : LB (A ⊗ U).left)

def LiftsVia {B C : Type} [CommRing B] [CommRing C] (φ : B →+* C) : Prop :=
  ∀ (T : Over (Sp R)) (N : LB (A ⊗ T).left), Fam A N → ∀ (y : Spec (CommRingCat.of B) ⟶ T.left)
    (u₀ : Over.mk (Spec.map (CommRingCat.ofHom φ) ≫ y ≫ T.hom) ⟶ U),
    Same A N M (Over.homMk (Spec.map (CommRingCat.ofHom φ) ≫ y) (by simp) :
      Over.mk (Spec.map (CommRingCat.ofHom φ) ≫ y ≫ T.hom) ⟶ T) u₀ →
    ∃ u : Over.mk (y ≫ T.hom) ⟶ U, Same A N M (Over.homMk y rfl : Over.mk (y ≫ T.hom) ⟶ T) u

theorem liftsVia_of_leftInverse {B C : Type} [CommRing B] [CommRing C] (φ : B →+* C) (ψ : C →+* B)
    (hψ : ψ.comp φ = RingHom.id B) : LiftsVia A M φ := by
  intro T N _ y u₀ h
  have hs : Spec.map (CommRingCat.ofHom ψ) ≫ Spec.map (CommRingCat.ofHom φ) = 𝟙 _ := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hψ, CommRingCat.ofHom_id, Spec.map_id]
  let e : Over.mk (y ≫ T.hom) ⟶ Over.mk (Spec.map (CommRingCat.ofHom φ) ≫ y ≫ T.hom) :=
    Over.homMk (Spec.map (CommRingCat.ofHom ψ)) (by simp [reassoc_of% hs])
  refine ⟨e ≫ u₀, ?_⟩
  have h' := same_comp A e h
  convert h' using 1
  ext
  simp [e, reassoc_of% hs]

theorem liftsVia_comp {B C D : Type} [CommRing B] [CommRing C] [CommRing D] (φ : B →+* C) (ψ : C →+* D)
    (hφ : LiftsVia A M φ) (hψ : LiftsVia A M ψ) : LiftsVia A M (ψ.comp φ) := by
  intro T N hN y u₀ h
  have k : Spec.map (CommRingCat.ofHom (ψ.comp φ)) =
      Spec.map (CommRingCat.ofHom ψ) ≫ Spec.map (CommRingCat.ofHom φ) := by
    rw [CommRingCat.ofHom_comp, Spec.map_comp]
  let e : Over.mk (Spec.map (CommRingCat.ofHom ψ) ≫ (Spec.map (CommRingCat.ofHom φ) ≫ y) ≫ T.hom) ⟶
      Over.mk (Spec.map (CommRingCat.ofHom (ψ.comp φ)) ≫ y ≫ T.hom) := Over.homMk (𝟙 _) (by simp [k])
  obtain ⟨u₁, h₁⟩ := hψ T N hN (Spec.map (CommRingCat.ofHom φ) ≫ y) (e ≫ u₀) (by
    have h' := same_comp A e h
    convert h' using 1
    ext
    simp [e, k])
  let e' : Over.mk (Spec.map (CommRingCat.ofHom φ) ≫ y ≫ T.hom) ⟶
      Over.mk ((Spec.map (CommRingCat.ofHom φ) ≫ y) ≫ T.hom) := Over.homMk (𝟙 _) (by simp)
  exact hφ T N hN y (e' ≫ u₁) (by
    have h' := same_comp A e' h₁
    convert h' using 1
    ext
    simp [e'])

theorem liftsVia_of_list
    (hyp : ∀ (B : Type) [CommRing B] [IsLocalRing B] [IsArtinianRing B] (t : B),
      t ∈ IsLocalRing.maximalIdeal B → IsLocalRing.maximalIdeal B * Ideal.span {t} = ⊥ →
      LiftsAlong A M B (Ideal.span {t})) :
    ∀ (n : ℕ) (B : Type) [CommRing B] [IsLocalRing B] [IsArtinianRing B] (C : Type) [CommRing C] (φ : B →+* C)
      (l : List B), l.length = n → Function.Surjective φ → RingHom.ker φ = Ideal.span {x | x ∈ l} →
      RingHom.ker φ ≤ IsLocalRing.maximalIdeal B → IsLocalRing.maximalIdeal B * RingHom.ker φ = ⊥ →
      LiftsVia A M φ := by
  intro n
  induction n with
  | zero =>
    intro B _ _ _ C _ φ l hl hs hk _ _
    have hl0 : l = [] := List.eq_nil_of_length_eq_zero hl
    subst hl0
    have hinj : Function.Injective φ := by
      rw [RingHom.injective_iff_ker_eq_bot, hk]
      simp
    let e := RingEquiv.ofBijective φ ⟨hinj, hs⟩
    refine liftsVia_of_leftInverse A M φ e.symm.toRingHom ?_
    ext x
    exact e.symm_apply_apply x
  | succ n ih =>
    intro B _ _ _ C _ φ l hl hs hk hkm hmk
    obtain ⟨t, l', rfl⟩ : ∃ t l', l = t :: l' := by
      cases l with
      | nil => simp at hl
      | cons t l' => exact ⟨t, l', rfl⟩
    have ht : t ∈ RingHom.ker φ := hk ▸ Ideal.subset_span (by simp)
    have hJ : Ideal.span {t} ≤ RingHom.ker φ := (Ideal.span_singleton_le_iff_mem _).2 ht
    let ψ : B ⧸ Ideal.span {t} →+* C := Ideal.Quotient.lift _ φ (fun a ha => hJ ha)
    have hcomp : ψ.comp (Ideal.Quotient.mk _) = φ := by
      ext x
      rfl
    have hprin : LiftsVia A M (Ideal.Quotient.mk (Ideal.span {t})) :=
      hyp B t (hkm ht) (le_bot_iff.1 ((Ideal.mul_mono_right hJ).trans hmk.le))
    have hne : Ideal.span {t} ≠ ⊤ := fun h =>
      (IsLocalRing.maximalIdeal.isMaximal B).ne_top (top_le_iff.1 (h ▸ hJ.trans hkm))
    haveI : Nontrivial (B ⧸ Ideal.span {t}) := Ideal.Quotient.nontrivial_iff.2 hne
    haveI : IsLocalRing (B ⧸ Ideal.span {t}) :=
      IsLocalRing.of_surjective' _ Ideal.Quotient.mk_surjective
    have hψs : Function.Surjective ψ := Ideal.Quotient.lift_surjective_of_surjective _ _ hs
    have hC : Nontrivial C := by
      rcases subsingleton_or_nontrivial C with hC | hC
      · exact absurd (hkm (RingHom.mem_ker.2 (Subsingleton.elim _ _)))
          ((Ideal.ne_top_iff_one _).1 (IsLocalRing.maximalIdeal.isMaximal B).ne_top)
      · exact hC
    have h0 : Ideal.Quotient.mk (Ideal.span {t}) t = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self t)
    have hker : RingHom.ker ψ = (RingHom.ker φ).map (Ideal.Quotient.mk (Ideal.span {t})) := by
      refine le_antisymm (fun x hx => ?_) (Ideal.map_le_iff_le_comap.2 fun b hb => ?_)
      · obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
        exact Ideal.mem_map_of_mem _ (RingHom.mem_ker.2 (RingHom.mem_ker.1 hx))
      · exact RingHom.mem_ker.2 (RingHom.mem_ker.1 hb)
    have hkerψ : RingHom.ker ψ =
        Ideal.span {x | x ∈ l'.map (Ideal.Quotient.mk (Ideal.span {t}))} := by
      rw [hker, hk, Ideal.map_span]
      have hset : (Ideal.Quotient.mk (Ideal.span {t})) '' {x | x ∈ t :: l'} =
          insert 0 {x | x ∈ l'.map (Ideal.Quotient.mk (Ideal.span {t}))} := by
        ext x
        simp only [List.mem_cons, Set.mem_image, Set.mem_setOf_eq, Set.mem_insert_iff, List.mem_map]
        constructor
        · rintro ⟨a, rfl | ha, rfl⟩
          · exact Or.inl h0
          · exact Or.inr ⟨a, ha, rfl⟩
        · rintro (rfl | ⟨a, ha, rfl⟩)
          · exact ⟨t, Or.inl rfl, h0⟩
          · exact ⟨a, Or.inr ha, rfl⟩
      rw [hset, Ideal.span_insert_zero]
    have hkm' : RingHom.ker ψ ≤ IsLocalRing.maximalIdeal (B ⧸ Ideal.span {t}) :=
      IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top ψ)
    have hmk' : IsLocalRing.maximalIdeal (B ⧸ Ideal.span {t}) * RingHom.ker ψ = ⊥ := by
      rw [eq_bot_iff, Ideal.mul_le]
      intro x hx y hy
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
      obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
      have ha : a ∈ IsLocalRing.maximalIdeal B := by
        rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hx ⊢
        exact fun h => hx (h.map _)
      have hb : b ∈ RingHom.ker φ := RingHom.mem_ker.2 (RingHom.mem_ker.1 hy)
      have hab : a * b = 0 := by
        have := Ideal.mul_mem_mul ha hb
        rw [hmk] at this
        simpa using this
      rw [Ideal.mem_bot, ← map_mul, hab, map_zero]
    have hlen : (l'.map (Ideal.Quotient.mk (Ideal.span {t}))).length = n := by
      simpa using hl
    have hψ := ih (B ⧸ Ideal.span {t}) C ψ _ hlen hψs hkerψ hkm' hmk'
    rw [← hcomp]
    exact liftsVia_comp A M _ _ hprin hψ

end GlobalTheory.DualCon.LiftInduct

namespace GlobalTheory.DualCon

theorem liftsAlong_of_principal : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (U : Over (Sp R)) (M : LB (A ⊗ U).left), (∀ (B : Type) [CommRing B] [IsLocalRing B] [IsArtinianRing B] (t : B), t ∈ IsLocalRing.maximalIdeal B → IsLocalRing.maximalIdeal B * Ideal.span {t} = ⊥ → LiftsAlong A M B (Ideal.span {t})) → ∀ (B : Type) [CommRing B] [IsLocalRing B] [IsArtinianRing B] (I : Ideal B), I ≤ IsLocalRing.maximalIdeal B → IsLocalRing.maximalIdeal B * I = ⊥ → LiftsAlong A M B I := by
  intro R _ A _ U M hyp B _ _ _ I hI hmI
  obtain ⟨s, hs⟩ : I.FG := IsNoetherian.noetherian I
  refine LiftInduct.liftsVia_of_list A M hyp _ B (B ⧸ I) (Ideal.Quotient.mk I) s.toList rfl
    Ideal.Quotient.mk_surjective ?_ ?_ ?_
  · rw [Ideal.mk_ker, ← hs]
    congr 1
    ext x
    simp
  · rwa [Ideal.mk_ker]
  · rwa [Ideal.mk_ker]

end GlobalTheory.DualCon
end
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open GlobalTheory.LBDescent GlobalTheory.DescNorm
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.DescNormU

theorem germ_comp {X Y Z : Scheme.{0}} (r : Z ⟶ Y) (q : Y ⟶ X) (z : Z) (U : X.Opens)
    (h : q (r z) ∈ U) (a : Γ(X, U)ˣ) :
    gm (r ≫ q) z U a = Units.map (r.stalkMap z).hom.toMonoidHom (gm q (r z) U a) := by
  apply Units.ext
  rw [gm_val (r ≫ q) z U h]
  show _ = (r.stalkMap z).hom (gm q (r z) U a).val
  rw [gm_val q (r z) U h]
  exact (Scheme.Hom.germ_stalkMap_apply r (q ⁻¹ᵁ U) z h _).symm

variable {S : Scheme.{0}} {A A' B : Over S} [GrpObj A] [GrpObj B]

theorem zb_zb : zb A B ≫ zb A B = zb A B := by ext <;> simp [zb]
theorem zb_fst' : zb A B ≫ fst A B = fst A B := by simp [zb]
theorem fst_comp_lift_id_one_eq_prodSetSecondCoordZero : fst A B ≫ lift (𝟙 A) (1 : A ⟶ B) = zb A B := by ext <;> simp [zb]

theorem rhoZ_rhoZ (q : A ⟶ A') : rhoZ (B := B) q ≫ rhoZ q = rhoZ q := by
  have e : (zb A B).left ≫ (zb A B).left = (zb A B).left := by rw [← Over.comp_left, zb_zb]
  apply pullback.hom_ext <;> simp [e]

theorem rhoZ_a (q : A ⟶ A') : rhoZ (B := B) q ≫ pullback.fst (q ▷ B).left (q ▷ B).left ≫ (fst A B).left =
    pullback.fst (q ▷ B).left (q ▷ B).left ≫ (fst A B).left := by
  rw [rhoZ_fst_assoc, ← Over.comp_left, zb_fst']

theorem rhoZ_a' (q : A ⟶ A') : rhoZ (B := B) q ≫ pullback.snd (q ▷ B).left (q ▷ B).left ≫ (fst A B).left =
    pullback.snd (q ▷ B).left (q ▷ B).left ≫ (fst A B).left := by
  rw [rhoZ_snd_assoc, ← Over.comp_left, zb_fst']

theorem a_s (q : A ⟶ A') : (pullback.fst (q ▷ B).left (q ▷ B).left ≫ (fst A B).left) ≫ (lift (𝟙 A) (1 : A ⟶ B)).left =
    rhoZ q ≫ pullback.fst (q ▷ B).left (q ▷ B).left := by
  rw [rhoZ_fst, Category.assoc, ← Over.comp_left, fst_comp_lift_id_one_eq_prodSetSecondCoordZero]

theorem pullbackSnd_fst_comp_lift_id_one (q : A ⟶ A') : (pullback.snd (q ▷ B).left (q ▷ B).left ≫ (fst A B).left) ≫ (lift (𝟙 A) (1 : A ⟶ B)).left =
    rhoZ q ≫ pullback.snd (q ▷ B).left (q ▷ B).left := by
  rw [rhoZ_snd, Category.assoc, ← Over.comp_left, fst_comp_lift_id_one_eq_prodSetSecondCoordZero]

end GlobalTheory.DescNormU

namespace GlobalTheory.DescNormU

theorem germ_gen {X X' Y : Scheme.{0}} {L : LB X} {F : X' ⟶ X} (τ : LB.Gen (L.pull F)) (hτ : τ.IsGen)
    (g : Y ⟶ X') (y : Y) (i i' : L.ι) (hi : F (g y) ∈ L.U i) (hi' : F (g y) ∈ L.U i') :
    gm g y _ (τ.s fun _ => i) = gm (g ≫ F) y _ (L.g i i') * gm g y _ (τ.s fun _ => i') := by
  have hp : g y ∈ (L.pull F).U (fun _ => i) ⊓ (L.pull F).U (fun _ => i') := ⟨mem_pull.2 hi, mem_pull.2 hi'⟩
  have e : gm g y ((L.pull F).U (fun _ => i) ⊓ (L.pull F).U (fun _ => i')) ((L.pull F).g (fun _ => i) (fun _ => i')) =
      gm (g ≫ F) y _ (L.g i i') := by
    show gm g y _ (∏ _k : PUnit, (res _ (pullU F _ (L.g i i'))) ^ (1 : ℤ)) = _
    rw [Fintype.prod_unique, zpow_one]
    exact (gm_res g y _ hp _).trans (gm_pull g F y (L.U i ⊓ L.U i') ⟨hi, hi'⟩ _)
  have := congrArg (gm g y ((L.pull F).U (fun _ => i) ⊓ (L.pull F).U (fun _ => i'))) (hτ (fun _ => i) (fun _ => i'))
  rw [map_mul, gm_res g y _ hp, gm_res g y _ hp, e] at this
  exact this

end GlobalTheory.DescNormU

namespace GlobalTheory.DescNormU

theorem pt_eq {X Y Z : Scheme.{0}} {f : X ⟶ Y} {g : Y ⟶ Z} {h : X ⟶ Z} (e : f ≫ g = h) (x : X) : g (f x) = h x := by
  rw [← e]; rfl

theorem rhoZ_rhoZ_apply {S : Scheme.{0}} {A A' B : Over S} [GrpObj A] [GrpObj B] (q : A ⟶ A') (z) :
    rhoZ (B := B) q (rhoZ q z) = rhoZ q z := pt_eq (rhoZ_rhoZ q) z



theorem normalise : ∀ (K : Type) [Field K] (A A' B : Over (Sp K)) [GrpObj A] [GrpObj B] (q : A ⟶ A') (P : LB (A ⊗ B).left) (τ : LB.Gen (ev P (𝟙 A) (1 : A ⟶ B))), P.IsLB → τ.IsGen → ∀ φ : ∀ i j, Γ(pullback (q ▷ B).left (q ▷ B).left, chart (q ▷ B).left P i j)ˣ, DescCompat (q ▷ B).left P φ → ∃ u : Γ(pullback (q ▷ B).left (q ▷ B).left, ⊤)ˣ, NormAlong q P τ (GlobalTheory.DescNorm.twist (q ▷ B).left P φ u) := by
  intro K _ A A' B _ _ q P τ hP hτ φ hφ
  let W : P.ι × P.ι → (pullback (q ▷ B).left (q ▷ B).left).Opens := fun p => rhoZ q ⁻¹ᵁ chart (q ▷ B).left P p.1 p.2
  have h2 : ∀ p, W p ≤ (pullback.fst (q ▷ B).left (q ▷ B).left ≫ (fst A B).left) ⁻¹ᵁ
      (P.pull (lift (𝟙 A) (1 : A ⟶ B)).left).U (fun _ => p.1) := fun p z hz =>
    mem_pull.2 (by rw [pt_eq (a_s q) z]; exact hz.1)
  have h3 : ∀ p, W p ≤ (pullback.snd (q ▷ B).left (q ▷ B).left ≫ (fst A B).left) ⁻¹ᵁ
      (P.pull (lift (𝟙 A) (1 : A ⟶ B)).left).U (fun _ => p.2) := fun p z hz =>
    mem_pull.2 (by rw [pt_eq (pullbackSnd_fst_comp_lift_id_one q) z]; exact hz.2)
  let v : ∀ p, Γ(pullback (q ▷ B).left (q ▷ B).left, W p)ˣ := fun p =>
    (pullU (rhoZ q) _ (φ p.1 p.2))⁻¹ *
      (res (h2 p) (pullU (pullback.fst (q ▷ B).left (q ▷ B).left ≫ (fst A B).left) _ (τ.s fun _ => p.1)))⁻¹ *
      res (h3 p) (pullU (pullback.snd (q ▷ B).left (q ▷ B).left ≫ (fst A B).left) _ (τ.s fun _ => p.2))
  have hv : ∀ (Y : Scheme.{0}) (g : Y ⟶ pullback (q ▷ B).left (q ▷ B).left) (y : Y) (p : P.ι × P.ι), g y ∈ W p →
      gm g y (W p) (v p) = (gm (g ≫ rhoZ q) y _ (φ p.1 p.2))⁻¹ *
        (gm (g ≫ pullback.fst (q ▷ B).left (q ▷ B).left ≫ (fst A B).left) y _ (τ.s fun _ => p.1))⁻¹ *
        gm (g ≫ pullback.snd (q ▷ B).left (q ▷ B).left ≫ (fst A B).left) y _ (τ.s fun _ => p.2) := by
    intro Y g y p hy
    simp only [v, map_mul, map_inv]
    rw [gm_pull g (rhoZ q) y _ hy, gm_res g y (h2 p) hy, gm_pull g (pullback.fst (q ▷ B).left (q ▷ B).left ≫ (fst A B).left) y _ (h2 p hy),
      gm_res g y (h3 p) hy, gm_pull g (pullback.snd (q ▷ B).left (q ▷ B).left ≫ (fst A B).left) y _ (h3 p hy)]

  have indep : ∀ p p', ∀ z ∈ W p ⊓ W p', gm (𝟙 _) z (W p) (v p) = gm (𝟙 _) z (W p') (v p') := by
    rintro ⟨i, j⟩ ⟨i', j'⟩ z ⟨hz, hz'⟩
    rw [hv _ (𝟙 _) z _ hz, hv _ (𝟙 _) z _ hz']
    simp only [Category.id_comp]
    have hz1 : pullback.fst (q ▷ B).left (q ▷ B).left (rhoZ q z) ∈ P.U i := hz.1
    have hz2 : pullback.snd (q ▷ B).left (q ▷ B).left (rhoZ q z) ∈ P.U j := hz.2
    have hz1' : pullback.fst (q ▷ B).left (q ▷ B).left (rhoZ q z) ∈ P.U i' := hz'.1
    have hz2' : pullback.snd (q ▷ B).left (q ▷ B).left (rhoZ q z) ∈ P.U j' := hz'.2
    have c1 : gm (rhoZ q) z _ (φ i' j') = gm (rhoZ q ≫ pullback.fst (q ▷ B).left (q ▷ B).left) z _ (P.g i i') *
        gm (rhoZ q) z _ (φ i j) * gm (rhoZ q ≫ pullback.snd (q ▷ B).left (q ▷ B).left) z _ (P.g j' j) := by
      have e := congrArg (Units.map ((rhoZ q).stalkMap z).hom.toMonoidHom) (hφ (rhoZ q z) i i' j j' hz1 hz1' hz2 hz2')
      rw [map_mul, map_mul] at e
      have k1 := germ_comp (rhoZ q) (𝟙 _) z (chart (q ▷ B).left P i' j') ⟨hz1', hz2'⟩ (φ i' j')
      have k2 := germ_comp (rhoZ q) (𝟙 _) z (chart (q ▷ B).left P i j) ⟨hz1, hz2⟩ (φ i j)
      have k3 := germ_comp (rhoZ q) (pullback.fst (q ▷ B).left (q ▷ B).left) z (P.U i ⊓ P.U i') ⟨hz1, hz1'⟩ (P.g i i')
      have k4 := germ_comp (rhoZ q) (pullback.snd (q ▷ B).left (q ▷ B).left) z (P.U j' ⊓ P.U j) ⟨hz2', hz2⟩ (P.g j' j)
      rw [Category.comp_id] at k1 k2
      rw [k1, k2, k3, k4]
      exact e
    have t1 := germ_gen τ hτ (pullback.fst (q ▷ B).left (q ▷ B).left ≫ (fst A B).left) z i i'
      (by rw [pt_eq (a_s q) z]; exact hz1) (by rw [pt_eq (a_s q) z]; exact hz1')
    have t2 := germ_gen τ hτ (pullback.snd (q ▷ B).left (q ▷ B).left ≫ (fst A B).left) z j j'
      (by rw [pt_eq (pullbackSnd_fst_comp_lift_id_one q) z]; exact hz2) (by rw [pt_eq (pullbackSnd_fst_comp_lift_id_one q) z]; exact hz2')
    rw [a_s] at t1
    rw [pullbackSnd_fst_comp_lift_id_one] at t2
    have cc := gm_cocycle hP (rhoZ q ≫ pullback.snd (q ▷ B).left (q ▷ B).left) z hz2 hz2' hz2
    rw [gm_self hP _ z hz2] at cc
    rw [c1, t1, t2]
    generalize gm (rhoZ q) z _ (φ i j) = Φ
    generalize gm (rhoZ q ≫ pullback.fst (q ▷ B).left (q ▷ B).left) z _ (P.g i i') = G₁
    generalize gm (rhoZ q ≫ pullback.snd (q ▷ B).left (q ▷ B).left) z _ (P.g j' j) = G₂ at cc ⊢
    generalize gm (rhoZ q ≫ pullback.snd (q ▷ B).left (q ▷ B).left) z _ (P.g j j') = H at cc ⊢
    generalize gm (pullback.fst (q ▷ B).left (q ▷ B).left ≫ (fst A B).left) z _ (τ.s fun _ => i') = T₁
    generalize gm (pullback.snd (q ▷ B).left (q ▷ B).left ≫ (fst A B).left) z _ (τ.s fun _ => j') = T₂
    rw [eq_inv_of_mul_eq_one_left cc]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  have hc : (⊤ : (pullback (q ▷ B).left (q ▷ B).left).Opens) ≤ iSup W := fun z _ => by
    obtain ⟨i, hi⟩ := exists_chart hP (pullback.fst (q ▷ B).left (q ▷ B).left (rhoZ q z))
    obtain ⟨j, hj⟩ := exists_chart hP (pullback.snd (q ▷ B).left (q ▷ B).left (rhoZ q z))
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨(i, j), ⟨hi, hj⟩⟩
  obtain ⟨u, hu⟩ := glue_unit ⊤ W (fun _ => le_top) hc v indep
  refine ⟨u, fun T r t i j hi hj => ?_⟩
  have hm : (r ≫ rhoZ q) t ∈ chart (q ▷ B).left P i j := ⟨hi, hj⟩
  have hw : (r ≫ rhoZ q) t ∈ W (i, j) := by
    show rhoZ q (rhoZ q (r t)) ∈ chart (q ▷ B).left P i j
    rw [rhoZ_rhoZ_apply]; exact hm
  show gm _ t _ (φ i j * res le_top u) = _
  rw [map_mul, gm_res _ t le_top hm, ← gm_res _ t (le_top : W (i, j) ≤ ⊤) hw u, hu (i, j), hv T (r ≫ rhoZ q) t (i, j) hw]
  simp only [Category.assoc, rhoZ_rhoZ, rhoZ_a, rhoZ_a']
  rw [← _root_.mul_assoc, ← _root_.mul_assoc, _root_.mul_inv_cancel, _root_.one_mul]

end GlobalTheory.DescNormU
end
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open GlobalTheory.LBDescent GlobalTheory.DescNorm
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.DescNorm

theorem tripleFibreProductProjOneThree_comp_fst {X Y : Scheme.{0}} (f : X ⟶ Y) :
    pr13 f ≫ pullback.fst f f = pullback.fst (pullback.snd f f) (pullback.fst f f) ≫ pullback.fst f f :=
  pullback.lift_fst _ _ _

theorem tripleFibreProductProjOneThree_comp_snd {X Y : Scheme.{0}} (f : X ⟶ Y) :
    pr13 f ≫ pullback.snd f f = pullback.snd (pullback.snd f f) (pullback.fst f f) ≫ pullback.snd f f :=
  pullback.lift_snd _ _ _

theorem defect_eq_one_of_coboundary {X Y Z : Scheme.{0}} (f : X ⟶ Y) (L : LB X) (hL : L.IsLB)
    (φ : ∀ i j, Γ(pullback f f, chart f L i j)ˣ) (D : Γ(Triple f, ⊤)ˣ) (z : X ⟶ X)
    (ρ : pullback f f ⟶ pullback f f) (σ : Triple f ⟶ Triple f)
    (h₁ : ρ ≫ pullback.fst f f = pullback.fst f f ≫ z) (h₂ : ρ ≫ pullback.snd f f = pullback.snd f f ≫ z)
    (k₁ : σ ≫ pullback.fst (pullback.snd f f) (pullback.fst f f) =
      pullback.fst (pullback.snd f f) (pullback.fst f f) ≫ ρ)
    (k₂ : σ ≫ pullback.snd (pullback.snd f f) (pullback.fst f f) =
      pullback.snd (pullback.snd f f) (pullback.fst f f) ≫ ρ)
    (g : X ⟶ Z) (U : L.ι → Z.Opens) (s : ∀ i, Γ(Z, U i)ˣ)
    (hN : ∀ (T : Scheme.{0}) (r : T ⟶ pullback f f) (t : T) (i j : L.ι),
      pullback.fst f f (ρ (r t)) ∈ L.U i → pullback.snd f f (ρ (r t)) ∈ L.U j →
      gm (r ≫ ρ) t _ (φ i j) =
        (gm (r ≫ pullback.fst f f ≫ g) t _ (s i))⁻¹ * gm (r ≫ pullback.snd f f ≫ g) t _ (s j))
    (hD : Defect f L φ D) (w : Triple f) : gm σ w ⊤ D = 1 := by
  have c : pullback.fst (pullback.snd f f) (pullback.fst f f) ≫ pullback.snd f f =
      pullback.snd (pullback.snd f f) (pullback.fst f f) ≫ pullback.fst f f := pullback.condition
  have k₃ : σ ≫ pr13 f = pr13 f ≫ ρ := by
    apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc, tripleFibreProductProjOneThree_comp_fst, h₁, ← Category.assoc, k₁, Category.assoc, h₁,
        ← Category.assoc, ← Category.assoc, tripleFibreProductProjOneThree_comp_fst]
    · rw [Category.assoc, Category.assoc, tripleFibreProductProjOneThree_comp_snd, h₂, ← Category.assoc, k₂, Category.assoc, h₂,
        ← Category.assoc, ← Category.assoc, tripleFibreProductProjOneThree_comp_snd]
  obtain ⟨i, hi⟩ := exists_chart hL (pullback.fst f f (pullback.fst (pullback.snd f f) (pullback.fst f f) (σ w)))
  obtain ⟨j, hj⟩ := exists_chart hL (pullback.snd f f (pullback.fst (pullback.snd f f) (pullback.fst f f) (σ w)))
  obtain ⟨k, hk⟩ := exists_chart hL (pullback.snd f f (pullback.snd (pullback.snd f f) (pullback.fst f f) (σ w)))
  have e := hD _ σ w i j k hi hj hk
  have p₁ : ρ (pullback.fst (pullback.snd f f) (pullback.fst f f) w) =
      pullback.fst (pullback.snd f f) (pullback.fst f f) (σ w) := congrArg (fun m => m w) k₁.symm
  have p₂ : ρ (pullback.snd (pullback.snd f f) (pullback.fst f f) w) =
      pullback.snd (pullback.snd f f) (pullback.fst f f) (σ w) := congrArg (fun m => m w) k₂.symm
  have p₃ : ρ (pr13 f w) = pr13 f (σ w) := congrArg (fun m => m w) k₃.symm
  have pc : pullback.fst f f (pullback.snd (pullback.snd f f) (pullback.fst f f) (σ w)) =
      pullback.snd f f (pullback.fst (pullback.snd f f) (pullback.fst f f) (σ w)) :=
    congrArg (fun m => m (σ w)) c.symm
  have q₁ : pullback.fst f f (pr13 f (σ w)) =
      pullback.fst f f (pullback.fst (pullback.snd f f) (pullback.fst f f) (σ w)) :=
    congrArg (fun m => m (σ w)) (tripleFibreProductProjOneThree_comp_fst f)
  have q₂ : pullback.snd f f (pr13 f (σ w)) =
      pullback.snd f f (pullback.snd (pullback.snd f f) (pullback.fst f f) (σ w)) :=
    congrArg (fun m => m (σ w)) (tripleFibreProductProjOneThree_comp_snd f)
  have a := hN _ (pullback.fst (pullback.snd f f) (pullback.fst f f)) w i j (by rw [p₁]; exact hi)
    (by rw [p₁]; exact hj)
  have b := hN _ (pullback.snd (pullback.snd f f) (pullback.fst f f)) w j k (by rw [p₂, pc]; exact hj)
    (by rw [p₂]; exact hk)
  have d := hN _ (pr13 f) w i k (by rw [p₃, q₁]; exact hi) (by rw [p₃, q₂]; exact hk)
  simp only [← Category.assoc] at a b d
  rw [tripleFibreProductProjOneThree_comp_fst, tripleFibreProductProjOneThree_comp_snd] at d
  rw [← c] at b
  rw [k₁, k₂, k₃, a, b, d, _root_.mul_assoc, mul_inv_cancel_left] at e
  exact mul_eq_right.1 e

theorem defect_normalised : ∀ (K : Type) [Field K] (A A' B : Over (Sp K)) [GrpObj A] [GrpObj B] (q : A ⟶ A') (P : LB (A ⊗ B).left) (τ : LB.Gen (ev P (𝟙 A) (1 : A ⟶ B))), P.IsLB → ∀ (φ : ∀ i j, Γ(pullback (q ▷ B).left (q ▷ B).left, chart (q ▷ B).left P i j)ˣ) (D : Γ(Triple (q ▷ B).left, ⊤)ˣ), NormAlong q P τ φ → Defect (q ▷ B).left P φ D → ∀ w : Triple (q ▷ B).left, gm (rhoW q) w ⊤ D = 1 := by
  intro K _ A A' B _ _ q P τ hP φ D hN hD w
  exact defect_eq_one_of_coboundary (q ▷ B).left P hP φ D (zb A B).left (rhoZ q) (rhoW q) (rhoZ_fst q) (rhoZ_snd q)
    (rhoW_fst q) (rhoW_snd q) (fst A B).left _ (fun i => τ.s fun _ => i) hN hD w

end GlobalTheory.DescNorm
end
end

section

open IsLocalRing GlobalTheory.FormalOrigin

theorem _root_.GlobalTheory.T.exists_ringHom_eq_taylor : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra ℚ B] (n : ℕ) (ev : A →+* B) (ds : Fin n → Derivation ℤ A A), ∃ T : A →+* MvPowerSeries (Fin n) B, ∀ f, T f = taylor ev (fun i => ⇑(ds i)) f := by
  first | exact @GlobalTheory.FormalOrigin.taylor_isRingHom | exact GlobalTheory.FormalOrigin.taylor_isRingHom | (intros; apply GlobalTheory.FormalOrigin.taylor_isRingHom <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.lineBundleLocalSectionFamily_unit_at_finite_points : ∀ (X : Scheme.{0}) (L : LB X) (W : X.Opens) (J : Type) (D : J → X.Opens), (∀ j, D j ≤ W) → ∀ (k : J → L.ι) (hD : ∀ j, D j ≤ L.U (k j)) (F : Set X), F.Finite → ∀ (a : X → Γ(X, W)), (∀ x ∈ F, x ∈ X.basicOpen (a x)) → (∀ x ∈ F, ∀ y ∈ F, y ≠ x → y ∉ X.basicOpen (a x)) → ∀ (E : X → ∀ j, Γ(X, D j)), (∀ x ∈ F, GlobalTheory.Pinch.IsSecFam L D k hD (E x)) → (∀ x ∈ F, ∀ j (h : x ∈ D j), IsUnit ((X.presheaf.germ (D j) x h).hom (E x j))) → ∃ e : ∀ j, Γ(X, D j), GlobalTheory.Pinch.IsSecFam L D k hD e ∧ ∀ x ∈ F, ∀ j (h : x ∈ D j), IsUnit ((X.presheaf.germ (D j) x h).hom (e j)) := by
  first | exact @GlobalTheory.Pinch.secFam_unit_at_finite | exact GlobalTheory.Pinch.secFam_unit_at_finite | (intros; apply GlobalTheory.Pinch.secFam_unit_at_finite <;> assumption)
end
