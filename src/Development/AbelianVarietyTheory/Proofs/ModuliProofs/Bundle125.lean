module

public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle002
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CmModelCoefficientSubringDedekindCompatibleEmbed
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle119
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle118
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle005
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle116
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PolarisationFormIntPolynomialBundles
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle114
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HolomorphicLiftRegularOfPeriodsZero
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SymmetricBundleTrivialConstantFamilyDualNumber
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle117
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle009
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
import Mathlib.RingTheory.Radical.NatInt
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle007
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubePull
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

namespace GlobalTheory.Models

theorem Cpt.exists_above : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (U : Scheme.{0}) (F O : Type) [Field F] [CommRing O] (c : U ⟶ Sp F) (t : SAB H U) (β : O →+* F) (U' : Scheme.{0}) (F' O' : Type) [Field F'] [CommRing O'] (c' : U' ⟶ Sp F') (t' : SAB H U') (β' : O' →+* F') (C : Cpt c t β) (b : O →+* O') (k : F →+* F') (r : U' ⟶ U) (hr : r ≫ c = c' ≫ spMap k) (ν : SABMap t' t r), IsDedFrac β → IsDedFrac β' → β'.comp b = k.comp β → Geo.Tor.IsNormalScheme U' → IsFinite (pullback.lift r c' hr) → ∃ C' : Cpt c' t' β', Nonempty (C'.Above C b r ν) := by
  intro E _ _ _ H U F O _ _ c t β U' F' O' _ _ c' t' β' C b k r hr ν _ hD hβ hN hfin
  obtain ⟨⟨_, _⟩, _, hfr⟩ := hD
  let _ := β'.toAlgebra
  have hsq : spMap β' ≫ spMap b = spMap k ≫ spMap β := by rw [← spMap_comp, ← spMap_comp, hβ]
  have hjs : C.j ≫ C.s = c ≫ spMap β := by
    rw [Cpt.j, Category.assoc, pullback.condition, ← Category.assoc, C.jQ_over]
  have hopen := C.jQ_open
  let s₁ := pullback.snd C.s (spMap b)
  let q : pullback s₁ (spMap β') ⟶ pullback C.s (spMap β) :=
    pullback.lift (pullback.fst _ _ ≫ pullback.fst _ _) (pullback.snd _ _ ≫ spMap k) (by
      rw [Category.assoc, pullback.condition, ← Category.assoc, pullback.condition, Category.assoc, hsq,
        Category.assoc])
  have q₁ : q ≫ pullback.fst _ _ = pullback.fst _ _ ≫ pullback.fst _ _ := pullback.lift_fst _ _ _
  have q₂ : q ≫ pullback.snd _ _ = pullback.snd _ _ ≫ spMap k := pullback.lift_snd _ _ _
  have hq : IsPullback q (pullback.snd s₁ (spMap β')) (pullback.snd C.s (spMap β)) (spMap k) := by
    refine IsPullback.of_right ?_ q₂ (IsPullback.of_hasPullback C.s (spMap β))
    rw [q₁, ← hsq]
    exact (IsPullback.of_hasPullback s₁ (spMap β')).paste_horiz (IsPullback.of_hasPullback C.s (spMap b))
  let f : U' ⟶ pullback C.s (spMap b) := pullback.lift (r ≫ C.j) (c' ≫ spMap β') (by
    rw [Category.assoc, hjs, ← Category.assoc, hr, Category.assoc, Category.assoc, hsq])
  have f₁ : f ≫ pullback.fst _ _ = r ≫ C.j := pullback.lift_fst _ _ _
  let u : U' ⟶ pullback s₁ (spMap β') := pullback.lift f c' (pullback.lift_snd _ _ _)
  have u₁ : u ≫ pullback.fst _ _ = f := pullback.lift_fst _ _ _
  have u₂ : u ≫ pullback.snd _ _ = c' := pullback.lift_snd _ _ _
  have hu : r ≫ C.jQ = u ≫ q := by
    apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc, q₁, ← Category.assoc u, u₁, f₁, Cpt.j]
    · rw [Category.assoc, Category.assoc, q₂, ← Category.assoc u, u₂, C.jQ_over, hr]
  let g := pullback.snd C.jQ q
  let v : U' ⟶ pullback C.jQ q := pullback.lift r u hu
  have v₁ : v ≫ pullback.fst _ _ = r := pullback.lift_fst _ _ _
  have v₂ : v ≫ g = u := pullback.lift_snd _ _ _
  have hp : IsPullback (pullback.fst C.jQ q) (g ≫ pullback.snd _ _) c (spMap k) := by
    have := (IsPullback.of_hasPullback C.jQ q).paste_vert hq
    rwa [C.jQ_over] at this
  have hv : IsFinite v := by
    have e : v = pullback.lift r c' hr ≫ hp.isoPullback.inv := by
      rw [Iso.eq_comp_inv]
      apply pullback.hom_ext
      · rw [Category.assoc, hp.isoPullback_hom_fst, v₁, pullback.lift_fst]
      · rw [Category.assoc, hp.isoPullback_hom_snd, ← Category.assoc, v₂, u₂, pullback.lift_snd]
    rw [e]; infer_instance
  have hW : (v ≫ g.isoOpensRange.hom) ≫ g.opensRange.ι = u := by
    rw [Category.assoc, Scheme.Hom.isoOpensRange_hom_ι, v₂]
  obtain ⟨Y, π, jQ, hπ, hY, hproj, hflat, j₂, j₁, jo, jd, jr⟩ :=
    GlobalTheory.exists_normal_finite_model_of_finite_over_open O' F' _ U' s₁ c' f g.opensRange (v ≫ g.isoOpensRange.hom)
      (GlobalTheory.ProjSpace.isProjOver_pullback_snd b C.proj) hN inferInstance
      (by rw [← Category.assoc]; exact (congrArg (· ≫ _) hW).trans u₁)
      (by rw [← Category.assoc]; exact (congrArg (· ≫ _) hW).trans u₂)
  obtain ⟨pp, cub, sym, adj, prim, mu, hmu⟩ := sabPull Out.CubePf.cubePull (π ≫ pullback.fst C.s (spMap b)) C.t
  obtain ⟨n, hn⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ C.m ν
  have hj : (jQ ≫ pullback.fst (π ≫ s₁) (spMap β')) ≫ π ≫ pullback.fst C.s (spMap b) =
      r ≫ C.jQ ≫ pullback.fst _ _ := by
    refine Eq.trans ?_ f₁
    rw [← j₁]
    simp only [Category.assoc]
  obtain ⟨n', hn'⟩ : ∃ n' : SABMap t' C.t ((jQ ≫ pullback.fst (π ≫ s₁) (spMap β')) ≫ π ≫ pullback.fst C.s (spMap b)),
      n'.φ = ν.φ ≫ C.m.φ := by
    rw [hj]; exact ⟨n, hn⟩
  obtain ⟨m, hm⟩ := sabCancel pullCubCancel E H _ _ _ _ _ _ _ _ mu n'
  have hg : ∀ p, p ∈ g.opensRange ↔ pullback.fst C.s (spMap b) (pullback.fst s₁ (spMap β') p) ∈ abLocus C.t.G := by
    intro p
    have e : pullback.fst C.s (spMap b) (pullback.fst s₁ (spMap β') p) = pullback.fst C.s (spMap β) (q p) := by
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, q₁]
    rw [e]
    change p ∈ Set.range (pullback.snd C.jQ q) ↔ q p ∈ pullback.fst C.s (spMap β) ⁻¹' abLocus C.t.G
    rw [C.ab_gen, Scheme.Pullback.range_snd]
    rfl
  refine ⟨⟨Y, π ≫ s₁, hY, hproj, hflat, jQ, j₂, jo, jd, _, m, ?_⟩,
    ⟨⟨π ≫ pullback.fst _ _, ?_, ?_, mu, hj, hm.symm.trans hn'⟩⟩⟩
  · ext y
    refine Iff.trans ?_ (jr y).symm
    rw [Set.mem_preimage, ← abLocus_pullback abLocusOne C.t.semi mu.cart.1, Scheme.Hom.comp_apply]
    constructor
    · intro h
      let w : pullback (π ≫ s₁) (spMap β') ⟶ pullback s₁ (spMap β') :=
        pullback.lift (pullback.fst _ _ ≫ π) (pullback.snd _ _) (by rw [Category.assoc, pullback.condition])
      have hw : pullback.fst s₁ (spMap β') (w y) = π (pullback.fst (π ≫ s₁) (spMap β') y) := by
        rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pullback.lift_fst]
      refine ⟨⟨w y, (hg _).2 (by rw [hw]; exact h)⟩, ?_⟩
      exact (Scheme.Hom.comp_apply _ _ _).trans hw
    · rintro ⟨p, hp⟩
      replace hp := (Scheme.Hom.comp_apply _ _ _).symm.trans hp
      have := (hg p.1).1 p.2
      exact (congrArg (fun z => pullback.fst C.s (spMap b) z ∈ abLocus C.t.G) hp).mp this
  · simp only [Category.assoc, s₁, pullback.condition]
  · have key : ∀ h, IsFinite (pullback.lift (π ≫ pullback.fst C.s (spMap b)) (π ≫ s₁) h) := fun h => by
      have e : pullback.lift (π ≫ pullback.fst C.s (spMap b)) (π ≫ s₁) h = π := by
        apply pullback.hom_ext
        · rw [pullback.lift_fst]
        · rw [pullback.lift_snd]
      rw [e]; exact hπ
    exact key _

end GlobalTheory.Models
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

namespace GlobalTheory.Models

theorem Top.exists_cpt_above : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l) (n N : ℕ) (T : Top Xo n N) (l : Level H) (h : l.A = N) (S e : ℕ) (β : RZ H S N →+* KA l) (b : RZ H n N →+* RZ H S N), 0 < S → n ∣ S → N ∣ S ^ e → IsInc (RZ H S N).subtype (KA l).val.toRingHom β → IsInc (RZ H n N).subtype (RZ H S N).subtype b → ∃ (C : Cpt (Xo l).s (Xo l).univ.t β) (q : C.X ⟶ T.Z) (hq : q ≫ T.s = C.s ≫ spMap b) (qm : SABMap C.t T.t q), IsFinite (pullback.lift q C.s hq) ∧ C.j ≫ q = T.a l h ∧ C.m.φ ≫ qm.φ = (T.m l h).φ ∧ IsQProjOver (C.t.G.hom ≫ C.s) := by
  intro E _ _ _ H D Xo n N T l h S e β b hS _ hN hβ hb
  subst h
  obtain ⟨⟨_, _⟩, _, hfr⟩ := (GlobalTheory.BaseRing.isDedFrac_RZ E H l S e hS hN).2.2 β hβ
  let _ := β.toAlgebra
  obtain ⟨W, f₀, hW₀, hfin, -, fa, fs⟩ := T.fin l rfl (β.comp b) (fun x => (hβ (b x)).trans (hb x))
  have hsm := (Xo l).smooth
  have hnor : Geo.Tor.IsNormalScheme (Xo l).X :=
    (GlobalTheory.isReduced_isNormalScheme_isLocallyNoetherian_of_smooth_over_field _ _ (Xo l).s
      (SmoothOfRelativeDimension.smooth D.dim _)).2.1
  let s₁ := pullback.snd T.s (spMap b)
  have hp : IsPullback (pullback.fst s₁ (spMap β) ≫ pullback.fst T.s (spMap b)) (pullback.snd s₁ (spMap β)) T.s
      (spMap (β.comp b)) := by
    rw [spMap_comp]
    exact (IsPullback.of_hasPullback s₁ (spMap β)).paste_horiz (IsPullback.of_hasPullback T.s (spMap b))
  let g := W.ι ≫ hp.isoPullback.inv
  have g₁ : (g ≫ pullback.fst _ _) ≫ pullback.fst _ _ = W.ι ≫ pullback.fst _ _ := by
    rw [Category.assoc, Category.assoc, hp.isoPullback_inv_fst]
  have g₂ : g ≫ pullback.snd _ _ = W.ι ≫ pullback.snd _ _ := by
    rw [Category.assoc, hp.isoPullback_inv_snd]
  have hW : (f₀ ≫ g.isoOpensRange.hom) ≫ g.opensRange.ι = f₀ ≫ g := by
    rw [Category.assoc, Scheme.Hom.isoOpensRange_hom_ι]
  obtain ⟨Y, π, jQ, hπ, hY, hproj, hflat, j₂, j₁, jo, jd, jr⟩ :=
    GlobalTheory.exists_normal_finite_model_of_finite_over_open _ (KA l) _ (Xo l).X s₁ (Xo l).s (f₀ ≫ g ≫ pullback.fst _ _) g.opensRange (f₀ ≫ g.isoOpensRange.hom)
      (GlobalTheory.ProjSpace.isProjOver_pullback_snd b T.proj) hnor inferInstance
      (by rw [← Category.assoc]; exact (congrArg (· ≫ _) hW).trans (Category.assoc _ _ _))
      (by
        rw [← Category.assoc]
        exact (congrArg (· ≫ _) hW).trans ((Category.assoc _ _ _).trans ((congrArg (f₀ ≫ ·) g₂).trans fs)))
  obtain ⟨_, _, _, _, _, mu, -⟩ := sabPull Out.CubePf.cubePull (π ≫ pullback.fst T.s (spMap b)) T.t
  have hj : (jQ ≫ pullback.fst (π ≫ s₁) (spMap β)) ≫ π ≫ pullback.fst T.s (spMap b) = T.a l rfl := by
    rw [← fa, ← g₁, ← Category.assoc f₀, ← j₁]
    simp only [Category.assoc]
  obtain ⟨n', hn'⟩ : ∃ n' : SABMap (Xo l).univ.t T.t
      ((jQ ≫ pullback.fst (π ≫ s₁) (spMap β)) ≫ π ≫ pullback.fst T.s (spMap b)), n'.φ = (T.m l rfl).φ := by
    rw [hj]; exact ⟨_, rfl⟩
  obtain ⟨m, hm⟩ := sabCancel pullCubCancel E H _ _ _ _ _ _ _ _ mu n'
  have hg : ∀ p, p ∈ g.opensRange ↔ pullback.fst T.s (spMap b) (pullback.fst s₁ (spMap β) p) ∈ abLocus T.t.G := by
    intro p
    have e : pullback.fst T.s (spMap b) (pullback.fst s₁ (spMap β) p) =
        pullback.fst T.s (spMap (β.comp b)) (hp.isoPullback.hom p) := by
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hp.isoPullback_hom_fst]
    rw [e]
    change p ∈ Set.range g ↔ hp.isoPullback.hom p ∈ pullback.fst T.s (spMap (β.comp b)) ⁻¹' abLocus T.t.G
    rw [← hW₀]
    constructor
    · rintro ⟨z, rfl⟩
      rw [← Scheme.Hom.comp_apply, Category.assoc, Iso.inv_hom_id, Category.comp_id]
      exact z.2
    · intro hz
      refine ⟨⟨_, hz⟩, ?_⟩
      refine (Scheme.Hom.comp_apply _ _ _).trans ?_
      change hp.isoPullback.inv (hp.isoPullback.hom p) = p
      rw [← Scheme.Hom.comp_apply, Iso.hom_inv_id]
      rfl
  refine ⟨⟨Y, π ≫ s₁, hY, hproj, hflat, jQ, j₂, jo, jd, _, m, ?_⟩, π ≫ pullback.fst _ _, ?_, mu, ?_, hj,
    hm.symm.trans hn', ?_⟩
  · ext y
    refine Iff.trans ?_ (jr y).symm
    rw [Set.mem_preimage, ← abLocus_pullback abLocusOne T.t.semi mu.cart.1, Scheme.Hom.comp_apply]
    constructor
    · intro h
      let w : pullback (π ≫ s₁) (spMap β) ⟶ pullback s₁ (spMap β) :=
        pullback.lift (pullback.fst _ _ ≫ π) (pullback.snd _ _) (by rw [Category.assoc, pullback.condition])
      have hw : pullback.fst s₁ (spMap β) (w y) = π (pullback.fst (π ≫ s₁) (spMap β) y) := by
        rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pullback.lift_fst]
      refine ⟨⟨w y, (hg _).2 (by rw [hw]; exact h)⟩, ?_⟩
      exact (Scheme.Hom.comp_apply _ _ _).trans hw
    · rintro ⟨p, hp⟩
      replace hp := (Scheme.Hom.comp_apply _ _ _).symm.trans hp
      have := (hg p.1).1 p.2
      exact (congrArg (fun z => pullback.fst T.s (spMap b) z ∈ abLocus T.t.G) hp).mp this
  · simp only [Category.assoc, s₁, pullback.condition]
  · have key : ∀ h, IsFinite (pullback.lift (π ≫ pullback.fst T.s (spMap b)) (π ≫ s₁) h) := fun h => by
      have e : pullback.lift (π ≫ pullback.fst T.s (spMap b)) (π ≫ s₁) h = π := by
        apply pullback.hom_ext
        · rw [pullback.lift_fst]
        · rw [pullback.lift_snd]
      rw [e]; exact hπ
    exact key _
  · have P₁ := IsPullback.of_hasPullback T.t.G.hom (pullback.fst T.s (spMap b))
    have Q := GlobalTheory.isQProjOver_of_isPullback (P₁.paste_vert (IsPullback.of_hasPullback T.s (spMap b))) T.qproj
    have P₀ := IsPullback.of_hasPullback T.t.G.hom (π ≫ pullback.fst T.s (spMap b))
    let ψ := P₁.lift (pullback.fst T.t.G.hom (π ≫ pullback.fst T.s (spMap b))) (pullback.snd _ _ ≫ π)
      (by rw [Category.assoc]; exact P₀.w)
    have ψ₁ : ψ ≫ _ = _ := P₁.lift_fst _ _ _
    have ψ₂ : ψ ≫ _ = _ := P₁.lift_snd _ _ _
    have P₂ : IsPullback ψ (pullback.snd T.t.G.hom (π ≫ pullback.fst T.s (spMap b)))
        (pullback.snd T.t.G.hom (pullback.fst T.s (spMap b))) π :=
      IsPullback.of_right (by rw [ψ₁]; exact P₀) ψ₂ P₁
    have : IsFinite ψ := MorphismProperty.of_isPullback (P := @IsFinite) P₂.flip hπ
    have R := GlobalTheory.isQProjOver_comp_of_isFinite ψ Q
    rw [← Category.assoc, ψ₂, Category.assoc] at R
    exact R

end GlobalTheory.Models
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

theorem _root_.GlobalTheory.T.exists_semiAbelian_descent_tame_quotient : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Γ : Type) [Group Γ] [Finite Γ] (R : Type) [CommRing R] (X X' : Scheme.{0}) [IsLocallyNoetherian X'] (ρ : Γ →* Aut X) (π : X ⟶ X') (t : SAB H X) (s : X ⟶ Sp R) (τ : Γ →* Aut t.G.left) (mu : ∀ g, SABMap t t (ρ g).asIso.hom), (IsAffineHom π ∧ (∀ g, (ρ g).asIso.hom ≫ π = π) ∧ ∀ V : X'.Opens, Function.Injective (π.app V).hom ∧ ∀ f : Γ(X, π ⁻¹ᵁ V), (∀ g (h : π ⁻¹ᵁ V ≤ (ρ g).asIso.hom ⁻¹ᵁ (π ⁻¹ᵁ V)), ((ρ g).asIso.hom.appLE _ _ h).hom f = f) → f ∈ Set.range (π.app V).hom) → IsFinite π → IsQProjOver (t.G.hom ≫ s) → (IsReduced X ∧ genericPoints X ⊆ abLocus t.G) → (∀ g, (mu g).φ = (τ g).asIso.hom) → (∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ X), (Nat.card {g // x ≫ (ρ g).asIso.hom = x} : k) ≠ 0) → (∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ X) g, x ≫ (ρ g).asIso.hom = x → pullback.fst t.G.hom x ≫ (τ g).asIso.hom = pullback.fst t.G.hom x) → ∃ (t' : SAB H X') (ν : SABMap t t' π), (∀ g, (τ g).asIso.hom ≫ ν.φ = ν.φ) ∧ (Good t → PushInvertible t.G t.PP.L → Good t') := by
  first | exact @GlobalTheory.exists_sab_descent_of_tame_quotient | exact GlobalTheory.exists_sab_descent_of_tame_quotient | (intros; apply GlobalTheory.exists_sab_descent_of_tame_quotient <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

theorem _root_.GlobalTheory.T.siegelData_pullback_of_levelMap : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (O : Type) [CommRing O] (T T' : Scheme.{0}) (sT : T ⟶ Sp O) (f : T' ⟶ T) (t : SAB H T) (t' : SAB H T') (ν : SABMap t' t f) (lev : D.La → (𝟙_ (Over T) ⟶ t.G)) (lev' : D.La → (𝟙_ (Over T') ⟶ t'.G)) (g p N : ℕ) (Ag : SiegelFamily g p N) (z : ZP p N →+* O) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] D.La) (w : T ⟶ pullback Ag.s (spMap z)), (∀ x, (lev' x).left ≫ ν.φ = f ≫ (lev x).left) → SiegData sT t lev Ag z bas w → SiegData (f ≫ sT) t' lev' Ag z bas (f ≫ w) := by
  first | exact @GlobalTheory.SiegelDataPull.siegData_pull | exact GlobalTheory.SiegelDataPull.siegData_pull | (intros; apply GlobalTheory.SiegelDataPull.siegData_pull <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

noncomputable section

namespace GlobalTheory.SharpPrim

theorem matrix_identities {n : Type} [Fintype n] [DecidableEq n] {W m m' : Matrix n n ℤ}
    (hd : (W + W.transpose).det = 1) (h : (W + W.transpose) * m = W) (h' : (W + W.transpose) * m' = W.transpose) :
    m + m' = 1 ∧ m.transpose * (W + W.transpose) = (W + W.transpose) * m' := by
  set G := W + W.transpose with hG
  have hu : IsUnit G.det := by rw [hd]; exact isUnit_one
  have hT : G.transpose = G := by
    rw [hG, Matrix.transpose_add, Matrix.transpose_transpose, add_comm]
  constructor
  · have key : G * (m + m') = G := by rw [Matrix.mul_add, h, h']
    calc m + m' = G⁻¹ * (G * (m + m')) := by
          rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul G hu, Matrix.one_mul]
      _ = 1 := by rw [key, Matrix.nonsing_inv_mul G hu]
  · have ht := congrArg Matrix.transpose h
    rw [Matrix.transpose_mul, hT] at ht
    rw [ht, h']

theorem prod_mul_prod {M : Type} [CommGroup M] {n : ℕ} (x : Fin n → M) {m m' : Matrix (Fin n) (Fin n) ℤ}
    (h : m + m' = 1) (u : Fin n) :
    (List.ofFn fun v => x v ^ m u v).prod * (List.ofFn fun v => x v ^ m' u v).prod = x u := by
  have hm : ∀ v, m u v + m' u v = if u = v then 1 else 0 := by
    intro v
    have e := congrFun (congrFun h u) v
    rwa [Matrix.add_apply, Matrix.one_apply] at e
  rw [List.prod_ofFn, List.prod_ofFn, ← Finset.prod_mul_distrib]
  simp_rw [← zpow_add, hm]
  rw [Finset.prod_eq_single u (fun v _ hv => by rw [if_neg (Ne.symm hv), zpow_zero])
    (fun hu => absurd (Finset.mem_univ u) hu), if_pos rfl, zpow_one]

variable {o : Type} [CommRing o] {S : Scheme.{0}} {g k h : ℕ} {J : Type} {b : TBase o k} {s : S ⟶ Sp o}

theorem isSharp_of_tmap {W : Matrix (Fin 8) (Fin 8) ℤ} {a : J → Matrix (Fin 8) (Fin 8) ℤ}
    {bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] (Fin 8 → (Fin h ⊕ Fin h → ℤ))} {t t' : TObj g k J b s}
    {c : SiegPre h k (b.ζ : o) s} (H : IsSharp W a bas t c) (m : TMap t' t (𝟙 _)) : IsSharp W a bas t' c := by
  obtain ⟨φ, hpb, hLφ, hpt, hact⟩ := m
  obtain ⟨pr, hpr, huniv, hL, hpa, hlev⟩ := H
  have : IsMonHom (Iso.refl t.A).hom := inferInstanceAs (IsMonHom (𝟙 t.A))
  obtain ⟨e, he, heφ'⟩ := grpPullback_iso hpb (isGrpPullback_of_iso (Iso.refl t.A))
  have heφ : e.hom.left = φ := by simpa using heφ'
  have hcomm : ∀ j, t'.act j ≫ e.hom = e.hom ≫ t.act j := by
    intro j
    ext
    simp only [Over.comp_left, heφ, hact j]
  refine ⟨fun u => e.hom ≫ pr u, fun u => ?_, fun T y => ?_, ?_, fun j u => ?_, fun i u => ?_⟩
  · have := hpr u
    infer_instance
  · obtain ⟨x0, hx0, hu0⟩ := huniv T y
    refine ⟨x0 ≫ e.inv, fun u => by simpa using hx0 u, fun x hx => ?_⟩
    have hx' : x ≫ e.hom = x0 := hu0 _ fun u => by simpa using hx u
    rw [← hx']
    simp
  · have hfun : (fun uv : Fin 8 × Fin 8 => (lift (e.hom ≫ pr uv.1) (e.hom ≫ pr uv.2)).left) =
        fun uv => φ ≫ (lift (pr uv.1) (pr uv.2)).left := by
      funext uv
      rw [← comp_lift, Over.comp_left, heφ]
    rw [hfun]
    refine (CechPic.cls_eq_iff t'.isLB (LB.isLB_linComb c.isLB _ _)).1 ?_

    rw [(CechPic.cls_eq_iff t'.isLB (pull_isLB t.isLB φ)).2 hLφ, CechPic.cls_pull t.isLB,
    (CechPic.cls_eq_iff t.isLB (LB.isLB_linComb c.isLB _ _)).2 hL,
    CechPic.cls_linComb c.isLB, CechPic.cls_linComb c.isLB, map_sum]
    refine Finset.sum_congr rfl fun uv _ => ?_
    rw [map_zsmul, ← CechPic.pull_comp]
  · rw [← Category.assoc, hcomm j, Category.assoc, hpa j u, PowerAdjoint.comp_prod_zpow]
  · have hp := hpt i
    rw [Category.id_comp] at hp
    rw [← hlev i u, Over.comp_left, Over.comp_left, heφ, ← Category.assoc, hp, Over.comp_left]

end GlobalTheory.SharpPrim

theorem GlobalTheory.sharpClass_prim_and_iso : (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ∀ (o : Type) [CommRing o] (g k : ℕ) (J : Type) (b : TBase o k) (em : o →+* ℂ) (w w' : J) (h : ℕ) (W : Matrix (Fin 8) (Fin 8) ℤ) (a : J → Matrix (Fin 8) (Fin 8) ℤ) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] (Fin 8 → (Fin h ⊕ Fin h → ℤ))) (t : TObj g k J b (spMap em)), SharpClass W a bas em t → (IsE8 W → (W + W.transpose) * a w = W → (W + W.transpose) * a w' = W.transpose → t.Prim w w') ∧ ∀ t' : TObj g k J b (spMap em), TMap t' t (𝟙 _) → SharpClass W a bas em t' := by
  intro hΘ o _ g k J b em w w' h W a bas t ht
  obtain ⟨c, hc, hs⟩ := ht
  refine ⟨fun hE hw hw' => ?_, fun t' m => ⟨c, hc, SharpPrim.isSharp_of_tmap hs m⟩⟩
  obtain ⟨pr, hpr, huniv, hL, hact, -⟩ := hs
  have hid := SharpPrim.matrix_identities hE.2 hw hw'
  have key := PowerAdjoint.matrix_primitive_adjoint hΘ W ℂ o (spMap em) h k (b.ζ : o) c t.pol pr hpr huniv hL
    (a w) (t.act w) (hact w)
  refine ⟨?_, key.2 (a w') (t.act w') (hact w') hid.2, key.1 hw⟩
  obtain ⟨x0, -, hu0⟩ := huniv t.A pr
  have h1 : ∀ u, (t.act w * t.act w') ≫ pr u = pr u := by
    intro u
    have := hpr u
    rw [MonObj.mul_comp, hact w u, hact w' u]
    exact SharpPrim.prod_mul_prod pr hid.1 u
  rw [hu0 _ h1, hu0 (𝟙 t.A) fun u => Category.id_comp _]

end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZV

theorem _root_.GlobalTheory.T.weil_pairing_torsion_basis_symplectic : Out.Laws → Out.Laws2 → ∀ (g N k : ℕ) (Mat : Matrix (Fin (2 * g)) (Fin (2 * g)) (ZMod k)), ∃ S : Matrix (Fin (2 * g)) (Fin (2 * g)) (ZMod k), ∀ (K : Type) [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K)) (pt : Fin (2 * g) → (Out.baseOver (Sp K) ⟶ P.A)) (ζ : Kˣ) (f s : P.A ⟶ P.A), (k : K) ≠ 0 → IsPrimitiveRoot ζ k → TorsBasis P.A k pt → (∀ i j, Out.WeilIs P.A P.L k (pt i) (pt j) (unitOn (ζ ^ Out.stdSymp g i j))) → IsMonHom f → ActsBy pt f Mat → FormIs P (LB.LinComb P.L (K := Fin 2) ![𝟙 P.A.left, f.left] ![(N : ℤ), (N : ℤ)]) s → ActsBy pt s S := by
  first | exact @GlobalTheory.FormTorsion.exists_matrix_form | exact GlobalTheory.FormTorsion.exists_matrix_form | (intros; apply GlobalTheory.FormTorsion.exists_matrix_form <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZV

theorem _root_.GlobalTheory.T.polarisationForm_intPolynomial_bundles : Out.Laws → Out.Laws2 → ∀ (K : Type) [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K)) (M : LB P.A.left) (s : P.A ⟶ P.A), M.IsLB → FormIs P M s → (∃ ev : Polynomial ℤ → (P.A ⟶ P.A), ev 1 = 𝟙 P.A ∧ (∀ F G, ev (F + G) = ev F * ev G) ∧ ∀ F, ev (Polynomial.X * F) = ev F ≫ s) ∧ ∀ (ev : Polynomial ℤ → (P.A ⟶ P.A)), ev 1 = 𝟙 P.A → (∀ F G, ev (F + G) = ev F * ev G) → (∀ F, ev (Polynomial.X * F) = ev F ≫ s) → (∀ F, IsMonHom (ev F)) ∧ (∀ F G, ev (F * G) = ev F ≫ ev G) ∧ (∀ F, FormIs P (cubeLB P.A ![𝟙 P.A, ev (F)] P.L) (ev (2 * F))) ∧ (∀ F G, LBIso (cubeLB P.A ![𝟙 P.A, ev (G ^ 2 * F)] P.L) ((cubeLB P.A ![𝟙 P.A, ev (F)] P.L).pull (ev G).left)) ∧ (∀ F G, LBIso (LB.div (cubeLB P.A ![𝟙 P.A, ev (F + G)] P.L) (cubeLB P.A ![𝟙 P.A, ev (F)] P.L)) (cubeLB P.A ![𝟙 P.A, ev (G)] P.L)) ∧ LBIso (cubeLB P.A ![𝟙 P.A, ev (1)] P.L) (lbPow P.L 2) ∧ (SymB M → LBIso (cubeLB P.A ![𝟙 P.A, ev (Polynomial.X)] P.L) (lbPow M 2)) := by
  first | exact @GlobalTheory.formPoly_bundles | exact GlobalTheory.formPoly_bundles | (intros; apply GlobalTheory.formPoly_bundles <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.HkFam

theorem _root_.GlobalTheory.T.hecke_set_etale_level_structure_exists : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (𝔓 : Ideal (𝓞 E)) (p i : ℕ) (S : Scheme.{0}) [IsReduced S] (s : S ⟶ Sp (KA l)) (o : Ob D l s) (K : Set o.t.G.left), admitted l 𝔓 p → EtSet o.t.G K → HeckeSet D o.t 𝔓 p i K → ∃ (S' : Scheme.{0}) (π : S' ⟶ S) (o' : Ob D l (π ≫ s)) (m : ObjMap o' o π) (τ : Fin (p ^ (2 * (Module.finrank ℚ E / 2 * (D.p + D.q)))) → (𝟙_ (Over S') ⟶ o'.t.G)), IsFinite π ∧ Etale π ∧ Surjective π ∧ Lists (p ^ 2) τ (m.toSABMap.φ ⁻¹' K) := by
  first | exact @GlobalTheory.exists_cover_lists_heckeSet | exact GlobalTheory.exists_cover_lists_heckeSet | (intros; apply GlobalTheory.exists_cover_lists_heckeSet <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS

theorem _root_.GlobalTheory.T.torsionSection_constantFamily_dualNumbers : Out.Laws → ∀ (P₀ : Out.PolAV (Sp ℂ)), ∀ (A' : Over (Sp (DualNumber ℂ))) [GrpObj A'] (ρ : A'.left ⟶ P₀.A.left) (j : P₀.A.left ⟶ A'.left), IsConst A' P₀.A ρ j → ∀ (k : ℕ) (y : Out.baseOver (Sp (DualNumber ℂ)) ⟶ A') (y₀ : Out.baseOver (Sp ℂ) ⟶ P₀.A), k ≠ 0 → y ^ k = 1 → y₀ ^ k = 1 → (spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom) ≫ y.left = y₀.left ≫ j → y.left ≫ ρ = (spMap (algebraMap ℂ (DualNumber ℂ))) ≫ y₀.left := by
  first | exact @GlobalTheory.KS.torsion_section_const | exact GlobalTheory.KS.torsion_section_const | (intros; apply GlobalTheory.KS.torsion_section_const <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS

theorem _root_.GlobalTheory.T.holomorphic_lift_regular_of_periods_zero : Out.Laws → ∀ (P₀ : Out.PolAV (Sp ℂ)) (u : HolUnif P₀.A P₀.L P₀.g) (Hm : Matrix (Fin P₀.g) (Fin P₀.g) ℂ) (χ : u.Λ → ℂ), GoodU u Hm χ → ∀ (R : Type) [CommRing R] (x₀ : R →+* ℂ) (X : Scheme.{0}) (p : X ⟶ Sp R) (m : P₀.A.left ⟶ X), Smooth p → IsPullback m P₀.A.hom p (spMap x₀) → ∀ D s, IsDer x₀ D → KSRel u p m D 0 s → ∀ W₀, IsAffineOpen W₀ → ∀ W, W ≤ W₀ → ∀ f : Γ(X, W), ∃ a : Γ(P₀.A.left, m ⁻¹ᵁ W), ∀ z ∈ dom u m W, valAt' (u.ex z).left (m ⁻¹ᵁ W) a = s z W f := by
  first | exact @GlobalTheory.KS.regular_of_periods_zero | exact GlobalTheory.KS.regular_of_periods_zero | (intros; apply GlobalTheory.KS.regular_of_periods_zero <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS

theorem _root_.GlobalTheory.T.symmetric_bundle_trivial_constant_family_dualNumber : Out.Laws → ∀ (P₀ : Out.PolAV (Sp ℂ)) (u : HolUnif P₀.A P₀.L P₀.g) (Hm : Matrix (Fin P₀.g) (Fin P₀.g) ℂ) (χ : u.Λ → ℂ), GoodU u Hm χ → ∀ (A' : Over (Sp (DualNumber ℂ))) [GrpObj A'] (ρ : A'.left ⟶ P₀.A.left) (j : P₀.A.left ⟶ A'.left), IsConst A' P₀.A ρ j → ∀ (Q : LB A'.left) (k : ∀ i i', Γ(P₀.A.left, j ⁻¹ᵁ (Q.U i ⊓ Q.U i'))), Q.IsLB → (∀ i i' (h : Q.U i ⊓ Q.U i' ≤ ρ ⁻¹ᵁ (j ⁻¹ᵁ (Q.U i ⊓ Q.U i'))), (Q.g i i').val = 1 + constFn A'.hom _ DualNumber.eps * (ρ.appLE _ _ h).hom (k i i')) → Out.Sym A' Q → ∃ t : Q.Gen, t.IsGen := by
  first | exact @GlobalTheory.KS.EpsSym.trivial_of_symmetric | exact GlobalTheory.KS.EpsSym.trivial_of_symmetric | (intros; apply GlobalTheory.KS.EpsSym.trivial_of_symmetric <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

theorem _root_.GlobalTheory.T.sectionCoordinates_pull_iso_nonzeroLocus : ∀ (X : Scheme.{0}) (M : LB X) (I : Type) (th : I → M.Sec), M.IsLB → (∀ (X' : Scheme.{0}) (π : X' ⟶ X), ∃ th' : I → (M.pull π).Sec, ∀ (R : Type) [CommRing R] (x : Sp R ⟶ X') (v : I → R), SecCoord (M.pull π) th' x v ↔ SecCoord M th (x ≫ π) v) ∧ (∀ M' : LB X, M'.IsLB → LBIso M M' → ∃ th' : I → M'.Sec, ∀ (R : Type) [CommRing R] (x : Sp R ⟶ X) (v : I → R), SecCoord M' th' x v ↔ SecCoord M th x v) ∧ ∀ (R : Type) [CommRing R] (x : Sp R ⟶ X) (v : I → R) (i : I) (p : Sp R), SecCoord M th x v → (x p ∈ Out.nonzeroLocus (th i) ↔ v i ∉ p.asIdeal) := by
  first | exact @GlobalTheory.ZM.CoordMove.secCoord_pull_iso_locus | exact GlobalTheory.ZM.CoordMove.secCoord_pull_iso_locus | (intros; apply GlobalTheory.ZM.CoordMove.secCoord_pull_iso_locus <;> assumption)
end
