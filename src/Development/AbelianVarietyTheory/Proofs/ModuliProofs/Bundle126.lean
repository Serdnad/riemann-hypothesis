module

public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle010
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle068
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle051
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle117
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsProjCoordRepresentationHomogeneousIdealFla
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsProjProperRelAmpleOfProjectiveCoordinateRep
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsQProjOverTargetOfIsGaloisCover
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.DenseOfDenseP
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle005
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle119
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LevelQuotientUnramifiedDualNumberPoints
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle115
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle088
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle109
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle103
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle118
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle001
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

noncomputable section
namespace GlobalTheory.SharpPull

section
variable {S S' : Scheme.{0}} {f : S' ⟶ S} {A C : Over S} {A' C' : Over S'}
  [GrpObj A] [GrpObj C] [GrpObj A'] [GrpObj C'] {φ : A'.left ⟶ A.left} {ψ : C'.left ⟶ C.left}

theorem push_inj (h : IsGrpPullback A' A f φ) {T : Over S'} {x y : T ⟶ A'}
    (e : pushHom h T x = pushHom h T y) : x = y :=
  Over.OverMorphism.ext (h.1.hom_ext (congrArg (fun q => q.left) e) (by rw [Over.w, Over.w]))

theorem push_left (h : IsGrpPullback A' A f φ) {T : Over S'} (x : T ⟶ A') :
    (pushHom h T x).left = x.left ≫ φ := rfl

theorem push_surj (h : IsGrpPullback A' A f φ) {T : Over S'} (y : Over.mk (T.hom ≫ f) ⟶ A) :
    ∃ x : T ⟶ A', pushHom h T x = y :=
  ⟨Over.homMk (h.1.lift y.left T.hom (Over.w y)) (h.1.lift_snd _ _ _),
    Over.OverMorphism.ext (h.1.lift_fst _ _ _)⟩

theorem push_comp (h : IsGrpPullback A' A f φ) (h' : IsGrpPullback C' C f ψ) {p : A ⟶ C} {p' : A' ⟶ C'}
    (e : p'.left ≫ ψ = φ ≫ p.left) {T : Over S'} (x : T ⟶ A') :
    pushHom h' T (x ≫ p') = pushHom h T x ≫ p :=
  Over.OverMorphism.ext (by
    show (x.left ≫ _) ≫ _ = (x.left ≫ _) ≫ _
    rw [Category.assoc, e, Category.assoc])

theorem exists_lift (h : IsGrpPullback A' A f φ) (h' : IsGrpPullback C' C f ψ) (p : A ⟶ C) :
    ∃ p' : A' ⟶ C', p'.left ≫ ψ = φ ≫ p.left :=
  ⟨Over.homMk (h'.1.lift (φ ≫ p.left) A'.hom (by rw [Category.assoc, Over.w, h.1.w])) (h'.1.lift_snd _ _ _),
    h'.1.lift_fst _ _ _⟩

theorem isMonHom_lift (h : IsGrpPullback A' A f φ) (h' : IsGrpPullback C' C f ψ) {p : A ⟶ C} [IsMonHom p]
    {p' : A' ⟶ C'} (e : p'.left ≫ ψ = φ ≫ p.left) : IsMonHom p' := by
  have h1 : (1 : 𝟙_ (Over S') ⟶ A') ≫ p' = 1 := by
    apply push_inj h'
    rw [push_comp h h' e, map_one, map_one, MonObj.one_comp]
  have h2 : (fst A' A' * snd A' A') ≫ p' = (fst A' A' ≫ p') * (snd A' A' ≫ p') := by
    apply push_inj h'
    rw [push_comp h h' e, map_mul, map_mul, MonObj.mul_comp, push_comp h h' e, push_comp h h' e]
  constructor
  · simpa [Hom.one_def] using h1
  · rw [Hom.mul_def, Hom.mul_def] at h2
    have e1 : lift (fst A' A' ≫ p') (snd A' A' ≫ p') = p' ⊗ₘ p' := by ext <;> simp
    simpa [e1] using h2
end

theorem sharp_pull : ∀ (h g k : ℕ) (W : Matrix (Fin 8) (Fin 8) ℤ) (J : Type) (a : J → Matrix (Fin 8) (Fin 8) ℤ) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] (Fin 8 → (Fin h ⊕ Fin h → ℤ))) (o : Type) [CommRing o] (b : TBase o k) (S S' : Scheme.{0}) (s : S ⟶ Sp o) (s' : S' ⟶ Sp o) (f : S' ⟶ S) (t : TObj g k J b s) (t' : TObj g k J b s') (c : SiegPre h k (b.ζ : o) s), f ≫ s = s' → TMap t' t f → c.Principal → IsSharp W a bas t c → ∃ c' : SiegPre h k (b.ζ : o) s', c'.Principal ∧ IsSharp W a bas t' c' := by
  intro h g k W J a bas o _ b S S' s s' f t t' c hf ⟨φ, hφ, hL, hpt, hact⟩ hc ⟨pr, hmon, huniv, hiso, hmat, hlev⟩
  obtain ⟨⟨c', hpb⟩, hprin⟩ := GlobalTheory.T.siegelObject_pullback_exists_and_principal h k o (b.ζ : o) S S' s s' f c hf
  refine ⟨c', hprin c' hpb hc, ?_⟩
  obtain ⟨ψ, ψ₂, hψ, hsq, ⟨w, hw⟩, hlv⟩ := hpb
  choose pr' hpr using fun u => exists_lift hφ hψ (pr u)
  refine ⟨pr', fun u => ?_, fun T y => ?_, ?_, fun j u => ?_, fun i u => ?_⟩
  · have := hmon u
    exact isMonHom_lift hφ hψ (hpr u)
  · obtain ⟨x₀, hx₀, hu⟩ := huniv (Over.mk (T.hom ≫ f)) (fun u => pushHom hψ T (y u))
    obtain ⟨x, rfl⟩ := push_surj hφ x₀
    refine ⟨x, fun u => push_inj hψ ?_, fun x' hx' => push_inj hφ (hu _ fun u => ?_)⟩
    · rw [push_comp hφ hψ (hpr u), hx₀ u]
    · rw [← push_comp hφ hψ (hpr u), hx' u]
  · have hc : ∀ uv : Fin 8 × Fin 8, (lift (pr' uv.1) (pr' uv.2)).left ≫ ψ₂ = φ ≫ (lift (pr uv.1) (pr uv.2)).left := by
      intro uv
      apply pullback.hom_ext
      · show (_ ≫ ψ₂) ≫ (fst c.A c.A).left = (φ ≫ _) ≫ (fst c.A c.A).left
        rw [Category.assoc, hsq.1, ← Category.assoc, ← Over.comp_left, lift_fst, hpr, Category.assoc,
          ← Over.comp_left, lift_fst]
      · show (_ ≫ ψ₂) ≫ (snd c.A c.A).left = (φ ≫ _) ≫ (snd c.A c.A).left
        rw [Category.assoc, hsq.2, ← Category.assoc, ← Over.comp_left, lift_snd, hpr, Category.assoc,
          ← Over.comp_left, lift_snd]
    have H₁ := iso_linComb ((isGen_iff w).1 hw)
      (fun uv : Fin 8 × Fin 8 => (lift (pr' uv.1) (pr' uv.2)).left) (fun uv => W uv.1 uv.2)
    have H₂ : LBIso (t.L.pull φ) (LB.LinComb c.P
        (fun uv : Fin 8 × Fin 8 => (lift (pr' uv.1) (pr' uv.2)).left ≫ ψ₂) (fun uv => W uv.1 uv.2)) :=
      LBIso.chartPull (Geo.Tor.chartPullPull t.L φ φ rfl) (chartPullSame c.P _ _ _ φ hc) hiso
    exact LBIso.trans t'.isLB (DVR.linComb_isLB _ c.isLB _ _) (DVR.linComb_isLB _ c'.isLB _ _)
      (LBIso.trans t'.isLB (DVR.linComb_isLB _ t.isLB _ _) (DVR.linComb_isLB _ c.isLB _ _) hL H₂) H₁.symm
  · apply push_inj hψ
    have e : ∀ v, pushHom hψ t'.A (pr' v) = preHom (pushHom hφ t'.A (𝟙 _)) (pr v) := fun v =>
      (congrArg _ (Category.id_comp _).symm).trans (push_comp hφ hψ (hpr v) (𝟙 _))
    have e₂ : pushHom hφ t'.A (t'.act j) = pushHom hφ t'.A (𝟙 _) ≫ t.act j :=
      (congrArg _ (Category.id_comp _).symm).trans (push_comp hφ hφ (hact j) (𝟙 _))
    rw [push_comp hφ hψ (hpr u), e₂, Category.assoc, hmat j u]
    refine (map_list_prod (preHom (pushHom hφ t'.A (𝟙 _))) _).trans (Eq.trans ?_ (map_list_prod _ _).symm)
    rw [List.map_ofFn, List.map_ofFn]
    congr 2
    funext v
    simp only [Function.comp_apply, map_zpow, e]
  · apply hψ.1.hom_ext
    · rw [hlv, ← hlev i u, Over.comp_left, Over.comp_left, Category.assoc, hpr, ← Category.assoc, hpt, Category.assoc]
    · rw [Over.w, Over.w]; rfl

end GlobalTheory.SharpPull
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.ZM.CoordChart

private theorem isIso_restrict_lemma {X Z Y : Scheme.{0}} (x : X ⟶ Z) [Mono x] (j : Y ⟶ X)
    [IsOpenImmersion (j ≫ x)] : IsIso (x ∣_ (j ≫ x).opensRange) := by
  set V := (j ≫ x).opensRange with hV
  let s : V.toScheme ⟶ X := (j ≫ x).isoOpensRange.inv ≫ j
  have hs : s ≫ x = V.ι := by
    rw [← cancel_epi (j ≫ x).isoOpensRange.hom]
    simp only [s, Category.assoc, Iso.hom_inv_id_assoc]
    exact (Scheme.Hom.isoOpensRange_hom_ι (j ≫ x)).symm
  have hr : Set.range s ⊆ Set.range (x ⁻¹ᵁ V).ι := by
    rintro _ ⟨y, rfl⟩
    rw [Scheme.Opens.range_ι]
    show x (s y) ∈ V
    have e : x (s y) = V.ι y := by rw [← Scheme.Hom.comp_apply, hs]
    rw [e]
    have hm : V.ι y ∈ Set.range V.ι := ⟨y, rfl⟩
    rw [Scheme.Opens.range_ι] at hm
    exact hm
  let s' := IsOpenImmersion.lift (x ⁻¹ᵁ V).ι s hr
  have h1 : s' ≫ (x ⁻¹ᵁ V).ι = s := IsOpenImmersion.lift_fac _ _ _
  refine ⟨⟨s', ?_, ?_⟩⟩
  · rw [← cancel_mono ((x ⁻¹ᵁ V).ι ≫ x), Category.assoc, reassoc_of% h1, hs, morphismRestrict_ι,
      Category.id_comp]
  · rw [← cancel_mono V.ι, Category.assoc, morphismRestrict_ι, reassoc_of% h1, hs, Category.id_comp]

theorem isOpenImmersion_of_mono_of_local {X Z : Scheme.{0}} (x : X ⟶ Z) [Mono x]
    (h : ∀ p : X, ∃ (Y : Scheme.{0}) (j : Y ⟶ X), IsOpenImmersion (j ≫ x) ∧
      x p ∈ Set.range (j ≫ x)) : IsOpenImmersion x := by
  choose Y j hj hp using h
  refine IsZariskiLocalAtTarget.of_range_subset_iSup (P := @IsOpenImmersion)
    (fun p => (j p ≫ x).opensRange) ?_ (fun p => ?_)
  · rintro _ ⟨p, rfl⟩
    simp only [TopologicalSpace.Opens.coe_iSup, Set.mem_iUnion, SetLike.mem_coe]
    exact ⟨p, by rw [Scheme.Hom.mem_opensRange]; exact hp p⟩
  · have := isIso_restrict_lemma x (j p)
    infer_instance

theorem spMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  simp only [spMap, ← Spec.map_comp, CommRingCat.ofHom_comp]

theorem spMap_inj {A B : Type} [CommRing A] [CommRing B] {f g : A →+* B} (h : spMap f = spMap g) :
    f = g := by
  have e := congrArg CommRingCat.Hom.hom (Spec.map_injective h)
  simpa using e

theorem exists_spMap {A B : Type} [CommRing A] [CommRing B] (y : Sp B ⟶ Sp A) :
    ∃ f : A →+* B, y = spMap f := by
  refine ⟨(Spec.preimage y).hom, ?_⟩
  simp only [spMap, CommRingCat.ofHom_hom, Spec.map_preimage]

theorem mono_of_ring_points {A : Type} [CommRing A] {Z : Scheme.{0}} (x : Sp A ⟶ Z)
    (h : ∀ (B : Type) [CommRing B] (f g : A →+* B), spMap f ≫ x = spMap g ≫ x → f = g) : Mono x := by
  refine ⟨fun {W} a b hab => ?_⟩
  have key : ∀ (B : Type) [CommRing B] (t : Sp B ⟶ W), t ≫ a = t ≫ b := by
    intro B _ t
    obtain ⟨f, hf⟩ := exists_spMap (t ≫ a)
    obtain ⟨g, hg⟩ := exists_spMap (t ≫ b)
    have hfg : f = g := h _ f g (by rw [← hf, ← hg, Category.assoc, Category.assoc, hab])
    rw [hf, hg, hfg]
  exact W.affineOpenCover.openCover.hom_ext a b
    (fun k => key (W.affineOpenCover.X k) (W.affineOpenCover.openCover.f k))

theorem exists_chart : ∀ (R σ : Type) [CommRing R] (I : Ideal (MvPolynomial σ R)) (Z : Scheme.{0}) (s : Z ⟶ Sp R) (M : LB Z) (th : σ → M.Sec) (i : σ), ProjRep I s M th → ∃ x : Sp (MvPolynomial σ R ⧸ (I ⊔ Ideal.span {MvPolynomial.X i - 1})) ⟶ Z, IsOpenImmersion x ∧ Set.range x = (Out.nonzeroLocus (th i) : Set Z) ∧ x ≫ s = spMap ((Ideal.Quotient.mk _).comp MvPolynomial.C) ∧ SecCoord M th x (fun a => Ideal.Quotient.mk _ (MvPolynomial.X a)) := by
  intro R σ _ I Z s M th i hP
  obtain ⟨hM, hpts, hrep⟩ := hP
  set J := I ⊔ Ideal.span {MvPolynomial.X i - 1} with hJ
  set q := Ideal.Quotient.mk J with hq

  have hq1 : q (MvPolynomial.X i) = 1 := by
    rw [← sub_eq_zero, ← map_one q, ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_sup_right (Ideal.subset_span rfl)

  have hev : ∀ F, MvPolynomial.eval₂ (q.comp MvPolynomial.C) (fun a => q (MvPolynomial.X a)) F = q F := by
    intro F
    have e : MvPolynomial.eval₂Hom (q.comp MvPolynomial.C) (fun a => q (MvPolynomial.X a)) = q :=
      MvPolynomial.ringHom_ext (fun r => by simp) (fun a => by simp)
    exact RingHom.congr_fun e F
  obtain ⟨x, ⟨hxs, hxc⟩, -⟩ := hrep _ (q.comp MvPolynomial.C) (fun a => q (MvPolynomial.X a))
    (by rw [Ideal.eq_top_iff_one, ← hq1]; exact Ideal.subset_span ⟨i, rfl⟩)
    (fun F hF => by rw [hev, Ideal.Quotient.eq_zero_iff_mem]; exact Ideal.mem_sup_left hF)

  have hmono : Mono x := by
    apply mono_of_ring_points
    intro B _ f g hfg
    have hcf := GlobalTheory.ZM.Coord.baseChange hxc f
    have hcg := GlobalTheory.ZM.Coord.baseChange hxc g
    rw [hfg] at hcf
    obtain ⟨u, hu⟩ := GlobalTheory.ZM.Coord.unique hM hcg hcf
    have hu1 : (u : B) = 1 := by
      have e := hu i
      simp only [hq1, map_one] at e
      simpa using e.symm
    have hv : ∀ a, f (q (MvPolynomial.X a)) = g (q (MvPolynomial.X a)) := fun a => by
      rw [hu a, hu1, _root_.one_mul]
    have hb : f.comp (q.comp MvPolynomial.C) = g.comp (q.comp MvPolynomial.C) := by
      apply spMap_inj
      rw [← spMap_comp (q.comp MvPolynomial.C) f, ← spMap_comp (q.comp MvPolynomial.C) g, ← hxs,
        reassoc_of% hfg]
    have hc : f.comp q = g.comp q :=
      MvPolynomial.ringHom_ext (fun r => by simpa using RingHom.congr_fun hb r) (fun a => by simpa using hv a)
    exact Ideal.Quotient.ringHom_ext hc

  have hsub : Set.range x ⊆ (Out.nonzeroLocus (th i) : Set Z) := by
    rintro _ ⟨p, rfl⟩
    refine (GlobalTheory.ZM.CoordMove.mem_nonzeroLocus_iff hM i p hxc).2 ?_
    show q (MvPolynomial.X i) ∉ p.asIdeal
    rw [hq1]
    exact fun h1 => p.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h1)

  have hloc : ∀ z ∈ (Out.nonzeroLocus (th i) : Set Z), ∃ (B : Type) (_ : CommRing B)
      (ψ : (MvPolynomial σ R ⧸ J) →+* B), IsOpenImmersion (spMap ψ ≫ x) ∧ z ∈ Set.range (spMap ψ ≫ x) := by
    intro z hz
    obtain ⟨R', _, x', v', hx'o, ⟨p, rfl⟩, hx'c⟩ := (GlobalTheory.T.sectionCoordinateVector_exists_locally Z M σ th hM).2.2 z
    have hp : v' i ∉ p.asIdeal := (GlobalTheory.ZM.CoordMove.mem_nonzeroLocus_iff hM i p hx'c).1 hz
    have hunit : IsUnit (algebraMap R' (Localization.Away (v' i)) (v' i)) :=
      IsLocalization.Away.algebraMap_isUnit (v' i)
    have hc1 := GlobalTheory.ZM.Coord.scale (GlobalTheory.ZM.Coord.baseChange hx'c (algebraMap R' (Localization.Away (v' i))))
      hunit.unit⁻¹
    set w : σ → Localization.Away (v' i) :=
      fun a => ((hunit.unit⁻¹ : (Localization.Away (v' i))ˣ) : Localization.Away (v' i)) *
        algebraMap R' (Localization.Away (v' i)) (v' a) with hw
    have hwi : w i = 1 := by simp [w]
    obtain ⟨β', hβ'⟩ := exists_spMap ((spMap (algebraMap R' (Localization.Away (v' i))) ≫ x') ≫ s)
    obtain ⟨hspan, hI⟩ := hpts _ β' _ w hβ' hc1
    have hker : J ≤ RingHom.ker (MvPolynomial.eval₂Hom β' w) := by
      refine sup_le (fun F hF => hI F hF) (Ideal.span_le.2 ?_)
      rintro _ rfl
      simp [hwi]
    let ψ : (MvPolynomial σ R ⧸ J) →+* Localization.Away (v' i) :=
      Ideal.Quotient.lift J (MvPolynomial.eval₂Hom β' w) (fun F hF => hker hF)
    have hψC : ∀ r, ψ (q (MvPolynomial.C r)) = β' r := fun r =>
      (Ideal.Quotient.lift_mk J _ _).trans (by simp)
    have hψX : ∀ a, ψ (q (MvPolynomial.X a)) = w a := fun a =>
      (Ideal.Quotient.lift_mk J _ _).trans (by simp)
    obtain ⟨y, -, hyu⟩ := hrep _ β' w hspan hI
    have e2 : spMap (algebraMap R' (Localization.Away (v' i))) ≫ x' = y := hyu _ ⟨hβ', hc1⟩
    have e1 : spMap ψ ≫ x = y := by
      refine hyu _ ⟨?_, ?_⟩
      · rw [Category.assoc, hxs, spMap_comp]
        congr 1
        exact RingHom.ext hψC
      · have e := GlobalTheory.ZM.Coord.baseChange hxc ψ
        convert e using 2 with a
        exact (hψX a).symm
    have hrange := PrimeSpectrum.localization_away_comap_range (Localization.Away (v' i)) (v' i)
    have hpm : p ∈ Set.range (PrimeSpectrum.comap (algebraMap R' (Localization.Away (v' i)))) := by
      rw [hrange]
      exact hp
    obtain ⟨p', hp'⟩ := hpm
    refine ⟨Localization.Away (v' i), inferInstance, ψ, ?_, p', ?_⟩
    · rw [e1, ← e2]
      infer_instance
    · rw [e1, ← e2]
      show x' (PrimeSpectrum.comap (algebraMap R' (Localization.Away (v' i))) p') = x' p
      rw [hp']
  have := hmono
  refine ⟨x, ?_, ?_, hxs, hxc⟩
  · apply isOpenImmersion_of_mono_of_local x
    intro p
    obtain ⟨B, _, ψ, h1, h2⟩ := hloc (x p) (hsub ⟨p, rfl⟩)
    exact ⟨Sp B, spMap ψ, h1, h2⟩
  · refine Set.Subset.antisymm hsub (fun z hz => ?_)
    obtain ⟨B, _, ψ, -, ⟨b, hb⟩⟩ := hloc z hz
    exact ⟨(spMap ψ) b, hb⟩

end GlobalTheory.ZM.CoordChart
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

theorem _root_.GlobalTheory.T.exists_projCoordRepresentation_homogeneousIdeal_flat : ∀ (R σ : Type) [CommRing R] [Finite σ] (I : Ideal (MvPolynomial σ R)) (d : ℕ), (∀ F ∈ I, ∀ e, MvPolynomial.homogeneousComponent e F ∈ I) → ∃ (Z : Scheme.{0}) (s : Z ⟶ Sp R) (M : LB Z) (th : σ → M.Sec), (Nonempty σ → IsProjOver s) ∧ ProjRep I s M th ∧ (I.FG → LocallyOfFinitePresentation s) ∧ ((∀ e ≥ d, Module.Flat R (↥(MvPolynomial.homogeneousSubmodule σ R e) ⧸ (I.restrictScalars R).comap (MvPolynomial.homogeneousSubmodule σ R e).subtype)) → Flat s) := by
  first | exact @GlobalTheory.ProjFlat.exists_projRep_flat | exact GlobalTheory.ProjFlat.exists_projRep_flat | (intros; apply GlobalTheory.ProjFlat.exists_projRep_flat <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
theorem _root_.GlobalTheory.T.isProj_proper_relAmple_of_projectiveCoordinateRep : ∀ (R σ : Type) [CommRing R] [Finite σ] (I : Ideal (MvPolynomial σ R)) (Z : Over (Sp R)) (M : LB Z.left) (th : σ → M.Sec), ProjRep I Z.hom M th → IsProjOver Z.hom ∧ IsProper Z.hom ∧ Out.RelAmple Z M := by
  first | exact @GlobalTheory.ZM.projRep_projective_ample | exact GlobalTheory.ZM.projRep_projective_ample | (intros; apply GlobalTheory.ZM.projRep_projective_ample <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

theorem _root_.GlobalTheory.T.projCoordRepresentation_geometric_fibre_spanning : Out.Laws → Out.Laws2 → ∀ (S : Scheme.{0}) (P : Out.PolAV S) (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ S) (k : ℤ) (I : Type) [Finite I] (σ : I → LB.Sec (Out.LPow P.A P.L k (Over.mk x))), 4 ≤ k → Submodule.span Γ((Over.mk x).left, ⊤) (Set.range fun a => (Out.SecM.ofSec P.A (σ a) : Out.SecM P.A P.L k (Over.mk x))) = ⊤ → ProjRep (idealOf (fst (Over.mk x) P.A).left _ σ (𝟙 _)) (fst (Over.mk x) P.A).left _ σ := by
  first | exact @GlobalTheory.FibreEmbed.projRep_fibre | exact GlobalTheory.FibreEmbed.projRep_fibre | (intros; apply GlobalTheory.FibreEmbed.projRep_fibre <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

theorem _root_.GlobalTheory.T.isQProjOver_target_of_isGaloisCover : ∀ (K : Type) [Field K] (X Y : Scheme.{0}) (π : X ⟶ Y) (sY : Y ⟶ Sp K) (Ga : Type) [Group Ga] (ρ : Ga → (X ⟶ X)), IsGaloisCover Ga ρ π → IsSeparated sY → LocallyOfFiniteType sY → IsQProjOver (π ≫ sY) → IsQProjOver sY := by
  first | exact @GlobalTheory.GaloisQuotient.isQProjOver_of_isGaloisCover | exact GlobalTheory.GaloisQuotient.isQProjOver_of_isGaloisCover | (intros; apply GlobalTheory.GaloisQuotient.isQProjOver_of_isGaloisCover <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

theorem _root_.GlobalTheory.T.levelQuotient_unramified_dualNumberPoints : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l l₂ : Level H) (Xo₂ : Moduli D l₂) (Q : LevelQuot l Xo₂), 1 ≤ D.p + D.q → l.Dvd l₂ → ∀ (k : Type) [Field k] (x : Sp (DualNumber k) ⟶ Q.X) (ob : Obj D l (baseKA l) (x ≫ Q.s)), Nonempty (ObjMap ob Q.univ x) → Nonempty (ObjMap ob Q.univ (constPt x)) → x = constPt x := by
  first | exact @GlobalTheory.levelQuot_unram | exact GlobalTheory.levelQuot_unram | (intros; apply GlobalTheory.levelQuot_unram <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
open GlobalTheory.ZM.NearBuild

noncomputable section
namespace GlobalTheory.ZM.NearBuild

theorem concl_map (hL : Out.Laws2) {o : Type} [CommRing o] {g N' : ℕ} {J : Type} {b : TBase o (N' ^ 2)}
    {Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ} {κ : ℕ} {R R' : Type} [CommRing R] [CommRing R']
    {β : o →+* R} {v : Ix g (N' ^ 2) → R} (h : Concl b Mat κ β v) (ρ : R →+* R') :
    Concl b Mat κ (ρ.comp β) (fun a => ρ (v a)) := by
  obtain ⟨t, hth, hall⟩ := h
  have hs : spMap ρ ≫ spMap β = spMap (ρ.comp β) := (spMap_comp ρ β).symm
  obtain ⟨t₂, h₂⟩ := GlobalTheory.T.exists_thetaLevelAbelianScheme_pullback o g (N' ^ 2) J b (Sp R) (Sp R') (spMap β) (spMap (ρ.comp β)) (spMap ρ) t hs
  refine ⟨t₂, ?_, ?_⟩
  · rw [GlobalTheory.T.hasThetaConstants_iff_of_thetaLevelPullback o g N' J b (Sp R) (spMap β) t (Sp R') (spMap (ρ.comp β)) t₂ (spMap ρ) R' (𝟙 _) _ h₂,
      Category.id_comp]
    have hpush := GlobalTheory.T.hasThetaConstants_ring_baseChange hL o g N' J b (Sp R) (spMap β) t R R' ρ (𝟙 _) v hth
    rwa [Category.comp_id] at hpush
  · intro K _ _ x s t' hg
    rw [good_comp] at hg
    have h3 := hall K (x.comp ρ) s t' hg
    rw [spMap_comp] at h3
    exact ((GlobalTheory.T.thetaLevelPullback_id_comp_cancel o g (N' ^ 2) J b (Sp R) (Sp R') (Sp K) (spMap β) (spMap (ρ.comp β)) s t t₂ t').2
      (spMap ρ) (spMap x) h₂).2 h3

theorem exists_loc_loc {R : Type} [CommRing R] (f : R) (q₁ : Ideal (Localization.Away f)) (hq : q₁.IsPrime)
    (f' : Localization.Away f) (hf' : f' ∉ q₁) :
    ∃ F : R, F ∉ q₁.comap (loc f) ∧ ∃ ρ : Localization.Away f' →+* Localization.Away F,
      (ρ.comp (loc f')).comp (loc f) = loc F := by
  obtain ⟨n, a, ha⟩ := IsLocalization.Away.surj f f'
  have hunit : IsUnit (loc f f) := IsLocalization.Away.algebraMap_isUnit f
  have hfq : loc f f ∉ q₁ := fun hm => hq.ne_top (Ideal.eq_top_of_isUnit_mem _ hm hunit)
  refine ⟨f * a, ?_, ?_⟩
  · intro hm
    rw [Ideal.mem_comap, map_mul] at hm
    rcases hq.mem_or_mem hm with h1 | h1
    · exact hfq h1
    · have h2 : f' * algebraMap R (Localization.Away f) f ^ n ∈ q₁ := by rw [ha]; exact h1
      rcases hq.mem_or_mem h2 with h3 | h3
      · exact hf' h3
      · exact hfq (hq.mem_of_pow_mem n h3)
  · have hF : IsUnit (loc (f * a) (f * a)) := IsLocalization.Away.algebraMap_isUnit (f * a)
    rw [map_mul] at hF
    have hf1 : IsUnit (loc (f * a) f) := isUnit_of_mul_isUnit_left hF
    have ha1 : IsUnit (loc (f * a) a) := isUnit_of_mul_isUnit_right hF
    have hσ : (IsLocalization.Away.lift f hf1).comp (loc f) = loc (f * a) := IsLocalization.Away.lift_comp f hf1
    have e : IsLocalization.Away.lift f hf1 f' * IsLocalization.Away.lift f hf1 (loc f f) ^ n = loc (f * a) a := by
      rw [← map_pow, ← map_mul, ha]
      exact RingHom.congr_fun hσ a
    rw [← e] at ha1
    have hu : IsUnit (IsLocalization.Away.lift f hf1 f') := isUnit_of_mul_isUnit_left ha1
    refine ⟨IsLocalization.Away.lift f' hu, ?_⟩
    rw [IsLocalization.Away.lift_comp f' hu]
    exact hσ

theorem nearC_of_loc : Out.Laws2 → ∀ (o : Type) [CommRing o] (g N' : ℕ) (J : Type) (b : TBase o (N' ^ 2)) (Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) (κ : ℕ) (R : Type) [CommRing R] (β : o →+* R) (v : Ix g (N' ^ 2) → R) (f : R) (q₁ : Ideal (Localization.Away f)), q₁.IsPrime → NearC b Mat κ ((loc f).comp β) (fun a => loc f (v a)) q₁ → NearC b Mat κ β v (q₁.comap (loc f)) := by
  intro hL o _ g N' J b Mat κ R _ β v f q₁ hq h
  obtain ⟨f', hf', hc⟩ := h
  obtain ⟨F, hF, ρ, hρ⟩ := exists_loc_loc f q₁ hq f' hf'
  refine ⟨F, hF, ?_⟩
  have key : ∀ r : R, ρ (loc f' (loc f r)) = loc F r := fun r => RingHom.congr_fun hρ r
  have hc2 : Concl b Mat κ (ρ.comp ((loc f').comp ((loc f).comp β))) (fun a => ρ (loc f' (loc f (v a)))) :=
    concl_map hL hc ρ
  have e1 : ρ.comp ((loc f').comp ((loc f).comp β)) = (loc F).comp β := RingHom.ext fun r => key (β r)
  have e2 : (fun a => ρ (loc f' (loc f (v a)))) = fun a => loc F (v a) := funext fun a => key (v a)
  rw [e1, e2] at hc2
  exact hc2

end GlobalTheory.ZM.NearBuild
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
theorem _root_.GlobalTheory.T.isProjOver_comp_finite : ∀ (R : Type) [CommRing R] (X Y : Scheme.{0}) (f : Y ⟶ X) (s : X ⟶ Sp R), IsFinite f → IsProjOver s → IsProjOver (f ≫ s) := by
  first | exact @GlobalTheory.isProjOver_comp_of_finite | exact GlobalTheory.isProjOver_comp_of_finite | (intros; apply GlobalTheory.isProjOver_comp_of_finite <;> assumption)
end
