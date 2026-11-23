module

public import ReciprocityTheory.AnalyticForms.RegularLocalRings.LiftChartIdeal
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
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.Nullstellensatz
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle009
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.ExistsClosedOfChartIdeal
import ReciprocityTheory.AnalyticForms.RegularLocalRings.ProjHypA
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle008
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle010
import ReciprocityTheory.CommutativeAlgebra.MaximalIdealSquares.RingKrullDimQuotientSpanSingletonAddOne
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.ExistsBasicOpenCover

@[expose] public section

section

namespace ReciprocityTheory.AnForm.R

open MvPolynomial AlgebraicGeometry CategoryTheory

noncomputable section

theorem appLE_constSec_eq {S T : Scheme.{0}} (t : T ⟶ Spec (.of ℂ)) (g : S ⟶ T) {U : T.Opens}
    {V : S.Opens} (h : V ≤ g ⁻¹ᵁ U) (c : ℂ) :
    g.appLE U V h (constSec t U c) = constSec (g ≫ t) V c := by
  exact congrArg (fun φ => φ.hom ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom c))
    (Scheme.Hom.appLE_comp_appLE g t ⊤ U V le_top h)

theorem constSec_map_res {S : Scheme.{0}} (s : S ⟶ Spec (.of ℂ)) {U V : S.Opens} (h : V ≤ U) (c : ℂ) :
    S.presheaf.map (homOfLE h).op (constSec s U c) = constSec s V c := by
  exact congrArg (fun φ => φ.hom ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom c))
    (Scheme.Hom.appLE_map s (le_top : U ≤ s ⁻¹ᵁ ⊤) (homOfLE h).op)

variable {K : Type} [Fintype K] [Nonempty K] {ι : K → Type} [∀ k, Fintype (ι k)]
variable {P D : Ideal (MvPolynomial (Σ k, ι k) ℂ)} {hP : IsMultiHomogIdeal P}

theorem map_eval₂_constSec {S : Scheme.{0}} (s : S ⟶ Spec (.of ℂ)) {U V : S.Opens} (h : V ≤ U)
    {σ : Type} (u : σ → Γ(S, U)) (f : MvPolynomial σ ℂ) :
    S.presheaf.map (homOfLE h).op (eval₂ (constSec s U) u f) =
      eval₂ (constSec s V) (fun q => S.presheaf.map (homOfLE h).op (u q)) f := by
  have e := MvPolynomial.eval₂_comp_left (S.presheaf.map (homOfLE h).op).hom (constSec s U) u f
  refine e.trans ?_
  congr 1
  exact RingHom.ext fun c => constSec_map_res s h c

theorem chart_eval₂_overlap (p p' : (k : K) → ι k) (f : MvPolynomial (Σ k, ι k) ℂ) (a : K → ℕ)
    (hf : IsMultiHomog f a) :
    ∃ u : Γ(projX P hP, (chartOpen hP p).1 ⊓ (chartOpen hP p').1), IsUnit u ∧
      (projX P hP).presheaf.map (homOfLE (inf_le_right : (chartOpen hP p).1 ⊓ (chartOpen hP p').1 ≤ _)).op
          (eval₂ (constSec (toSpecC hP) (chartOpen hP p').1) (chartCoord hP p') f) =
        u * (projX P hP).presheaf.map
          (homOfLE (inf_le_left : (chartOpen hP p).1 ⊓ (chartOpen hP p').1 ≤ _)).op
          (eval₂ (constSec (toSpecC hP) (chartOpen hP p).1) (chartCoord hP p) f) := by
  have hinv : ∀ k,
      (projX P hP).presheaf.map (homOfLE (inf_le_right : (chartOpen hP p).1 ⊓ (chartOpen hP p').1 ≤ _)).op
          (chartCoord hP p' ⟨k, p k⟩) *
        (projX P hP).presheaf.map (homOfLE (inf_le_left : (chartOpen hP p).1 ⊓ (chartOpen hP p').1 ≤ _)).op
          (chartCoord hP p ⟨k, p' k⟩) = 1 := by
    intro k
    have h := chartCoord_overlap hP p p' ⟨k, p' k⟩
    dsimp only at h
    rw [mul_comm, h, chartCoord_self, map_one]
  refine ⟨∏ k, ((projX P hP).presheaf.map
      (homOfLE (inf_le_right : (chartOpen hP p).1 ⊓ (chartOpen hP p').1 ≤ _)).op
        (chartCoord hP p' ⟨k, p k⟩)) ^ a k, ?_, ?_⟩
  · have h1 : (∏ k, ((projX P hP).presheaf.map
        (homOfLE (inf_le_right : (chartOpen hP p).1 ⊓ (chartOpen hP p').1 ≤ _)).op
          (chartCoord hP p' ⟨k, p k⟩)) ^ a k) * (∏ k, ((projX P hP).presheaf.map
        (homOfLE (inf_le_left : (chartOpen hP p).1 ⊓ (chartOpen hP p').1 ≤ _)).op
          (chartCoord hP p ⟨k, p' k⟩)) ^ a k) = 1 := by
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_eq_one fun k _ => ?_
      rw [← mul_pow, hinv k, one_pow]
    exact ⟨⟨_, _, h1, by rw [mul_comm]; exact h1⟩, rfl⟩
  · rw [map_eval₂_constSec, map_eval₂_constSec]
    have hco : (fun q => (projX P hP).presheaf.map
        (homOfLE (inf_le_right : (chartOpen hP p).1 ⊓ (chartOpen hP p').1 ≤ _)).op (chartCoord hP p' q)) =
        fun q => (projX P hP).presheaf.map
          (homOfLE (inf_le_right : (chartOpen hP p).1 ⊓ (chartOpen hP p').1 ≤ _)).op
            (chartCoord hP p' ⟨q.1, p q.1⟩) *
          (projX P hP).presheaf.map
            (homOfLE (inf_le_left : (chartOpen hP p).1 ⊓ (chartOpen hP p').1 ≤ _)).op
              (chartCoord hP p q) := by
      funext q
      rw [← chartCoord_overlap hP p p' q, mul_comm]
    have key := eval₂_smul_of_isMultiHomog' (R := Γ(projX P hP, (chartOpen hP p).1 ⊓ (chartOpen hP p').1))
      (constSec (toSpecC hP) ((chartOpen hP p).1 ⊓ (chartOpen hP p').1)) hf
      (fun k => (projX P hP).presheaf.map
          (homOfLE (inf_le_right : (chartOpen hP p).1 ⊓ (chartOpen hP p').1 ≤ _)).op
            (chartCoord hP p' ⟨k, p k⟩))
      (fun q => (projX P hP).presheaf.map
            (homOfLE (inf_le_left : (chartOpen hP p).1 ⊓ (chartOpen hP p').1 ≤ _)).op
              (chartCoord hP p q))
    rw [hco]
    exact key

namespace WData

variable (w : WData P D hP)

theorem secHom_bind_lift (c : w.Idx) (f : MvPolynomial (Σ k, ι k) ℂ) :
    (w.pres c.1 c.2).secHom (bind₁ (w.lift c) f) =
      w.π.appLE _ (w.pres c.1 c.2).V (w.le_pres c.1 c.2)
        (eval₂ (constSec (toSpecC hP) (chartOpen hP c.1).1) (chartCoord hP c.1) f) := by
  have h : ((w.pres c.1 c.2).secHom).comp (bind₁ (w.lift c)).toRingHom =
      (w.π.appLE _ (w.pres c.1 c.2).V (w.le_pres c.1 c.2)).hom.comp
        (eval₂Hom (constSec (toSpecC hP) (chartOpen hP c.1).1) (chartCoord hP c.1)) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, bind₁_C_right,
        coe_eval₂Hom, eval₂_C]
      rw [AffPres.secHom_C, appLE_constSec_eq]
    · intro q
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, bind₁_X_right,
        coe_eval₂Hom, eval₂_X]
      by_cases hq : q.2 = c.1 q.1
      · have e : w.lift c q = 1 := by simp [lift, hq]
        rw [e, map_one]
        obtain ⟨k, i⟩ := q
        simp only at hq
        subst hq
        rw [chartCoord_self, map_one]
      · have e : w.lift c q = X (w.yq c.1 c.2 q) := by simp [lift, hq]
        rw [e, w.sec_yq]
  exact RingHom.congr_fun h f

theorem germ_lift_ratio (f : MvPolynomial (Σ k, ι k) ℂ) (a : K → ℕ) (hf : IsMultiHomog f a)
    (c c' : w.Idx) (x : w.W) (hx : x ∈ (w.pres c.1 c.2).V) (hx' : x ∈ (w.pres c'.1 c'.2).V) :
    ∃ u : (w.W.presheaf.stalk x)ˣ,
      w.W.presheaf.germ _ x hx ((w.pres c.1 c.2).secHom (bind₁ (w.lift c) f)) =
        u * w.W.presheaf.germ _ x hx' ((w.pres c'.1 c'.2).secHom (bind₁ (w.lift c') f)) := by
  obtain ⟨u, hu, he⟩ := chart_eval₂_overlap (hP := hP) c.1 c'.1 f a hf
  have hVO : (w.pres c.1 c.2).V ⊓ (w.pres c'.1 c'.2).V ≤
      w.π ⁻¹ᵁ ((chartOpen hP c.1).1 ⊓ (chartOpen hP c'.1).1) := fun y hy =>
    ⟨w.le_pres c.1 c.2 hy.1, w.le_pres c'.1 c'.2 hy.2⟩
  have hxx : x ∈ (w.pres c.1 c.2).V ⊓ (w.pres c'.1 c'.2).V := ⟨hx, hx'⟩
  have hU : IsUnit (w.W.presheaf.germ _ x hxx (w.π.appLE _ _ hVO u)) :=
    (hu.map (w.π.appLE _ _ hVO).hom).map _
  refine ⟨hU.unit⁻¹, ?_⟩
  have e1 : ∀ (d : w.Idx) (hd : (w.pres c.1 c.2).V ⊓ (w.pres c'.1 c'.2).V ≤ (w.pres d.1 d.2).V)
      (hO : (chartOpen hP c.1).1 ⊓ (chartOpen hP c'.1).1 ≤ (chartOpen hP d.1).1)
      (hxd : x ∈ (w.pres d.1 d.2).V),
      w.W.presheaf.germ _ x hxd ((w.pres d.1 d.2).secHom (bind₁ (w.lift d) f)) =
        w.W.presheaf.germ _ x hxx (w.π.appLE _ _ hVO ((projX P hP).presheaf.map (homOfLE hO).op
          (eval₂ (constSec (toSpecC hP) (chartOpen hP d.1).1) (chartCoord hP d.1) f))) := by
    intro d hd hO hxd
    rw [w.secHom_bind_lift d f, ← TopCat.Presheaf.germ_res_apply w.W.presheaf (homOfLE hd) x hxx]
    congr 1
    show (w.π.appLE _ _ _ ≫ w.W.presheaf.map (homOfLE hd).op).hom _ =
      ((projX P hP).presheaf.map (homOfLE hO).op ≫ w.π.appLE _ _ hVO).hom _
    rw [Scheme.Hom.appLE_map, Scheme.Hom.map_appLE]
  rw [e1 c inf_le_left inf_le_left hx, e1 c' inf_le_right inf_le_right hx', he, map_mul, map_mul,
    ← mul_assoc]
  rw [hU.val_inv_mul, one_mul]

end WData

end

end ReciprocityTheory.AnForm.R
end

section

namespace ReciprocityTheory.AnForm.R

open MvPolynomial AlgebraicGeometry CategoryTheory IsLocalRing

variable {K : Type} [Fintype K] [Nonempty K] {ι : K → Type} [∀ k, Fintype (ι k)]
variable {P D : Ideal (MvPolynomial (Σ k, ι k) ℂ)} {hP : IsMultiHomogIdeal P}

theorem ne_zero_of_span_eq_maximalIdeal {R : Type*} [CommRing R] [IsRegularLocalRing R] {d : ℕ}
    (hd : ringKrullDim R = d) (v : Fin d → R) (hv : Ideal.span (Set.range v) = maximalIdeal R)
    (l : Fin d) : v l ≠ 0 := by
  intro h0
  have hfin : (Set.range v \ {0}).Finite := (Set.finite_range v).sdiff
  have hncard : (Set.range v \ {0}).ncard < d := by
    have h1 : (Set.range v \ {0}).ncard < (Set.range v).ncard :=
      Set.ncard_sdiff_singleton_lt_of_mem ⟨l, h0⟩ (Set.finite_range v)
    have h2 : (Set.range v).ncard ≤ d := by
      calc (Set.range v).ncard ≤ (Set.univ : Set (Fin d)).ncard := by
            rw [← Set.image_univ]; exact Set.ncard_image_le (Set.finite_univ)
        _ = d := by simp
    omega
  have hspan : Ideal.span (Set.range v \ {0}) = maximalIdeal R := by
    rw [Ideal.span_sdiff_singleton_zero, hv]
  have hle : (maximalIdeal R).spanFinrank ≤ (Set.range v \ {0}).ncard := by
    rw [← hspan]; exact Submodule.spanFinrank_span_le_ncard_of_finite hfin
  have hdim := ringKrullDim_le_spanFinrank_maximalIdeal R
  rw [hd] at hdim
  have : (d : WithBot ℕ∞) ≤ ((Set.range v \ {0}).ncard : WithBot ℕ∞) :=
    hdim.trans (by exact_mod_cast hle)
  have := (Nat.cast_le (α := WithBot ℕ∞)).mp this
  omega

theorem WData.exists_closed_off (w : WData P D hP) (Q : AffPres (w.π ≫ toSpecC hP)) (x : w.M) (hxV : x.1 ∈ Q.V)
    (𝔮 : Ideal (MvPolynomial (Fin Q.n) ℂ)) (h𝔮min : 𝔮 ∈ Q.K.minimalPrimes)
    (h𝔮x : 𝔮 ≤ ptIdeal (Q.coord x.1 hxV)) (G : MvPolynomial (Fin Q.n) ℂ)
    (hG : eval (Q.coord x.1 hxV) G ≠ 0) :
    ∃ x' : w.M, ∃ hx' : x'.1 ∈ Q.V,
      𝔮 ≤ ptIdeal (Q.coord x'.1 hx') ∧
        w.π.base x'.1 ∉ (projB P D hP : Set (projX P hP)) ∧ eval (Q.coord x'.1 hx') G ≠ 0 := by
  generalize hp : Q.coord x.1 hxV = p at h𝔮x hG
  have := w.regular x.1
  haveI hregL : IsRegularLocalRing (locRing Q.K p) := by
    rw [← hp]; exact (Q.isRegularLocalRing_stalk_iff x.1 hxV x.2).mp (w.regular x.1)
  haveI : IsDomain (locRing Q.K p) := ReciprocityTheory.CA.AB.RegA.IsRegularLocalRing.isDomain _
  set d := (maximalIdeal (w.W.presheaf.stalk x.1)).spanFinrank with hdd
  have hd : ringKrullDim (w.W.presheaf.stalk x.1) = d :=
    (IsRegularLocalRing.spanFinrank_maximalIdeal).symm
  obtain ⟨S, -, -⟩ := exists_sncData w.snc_Zb Q w.compEquiv d x.1 hxV x.2 hd
  rw [hp] at S
  have hdL : ringKrullDim (locRing Q.K p) = d := by
    rw [← hp, ← Q.ringKrullDim_stalk x.1 hxV x.2]; exact hd
  have hmax : Ideal.map (algebraMap _ (locRing Q.K p)) (ptIdeal p) = maximalIdeal (locRing Q.K p) := by
    subst hp
    rw [← Q.map_maximalIdeal_stalk x.1 hxV x.2]; exact map_ringEquiv_maximalIdeal _

  set 𝔮' := RingHom.ker (algebraMap (MvPolynomial (Fin Q.n) ℂ) (locRing Q.K p)) with h𝔮'
  have h𝔮'prime : 𝔮'.IsPrime := RingHom.ker_isPrime _
  have hK𝔮' : Q.K ≤ 𝔮' := by
    intro f hf
    rw [h𝔮', RingHom.mem_ker, IsScalarTower.algebraMap_apply (MvPolynomial (Fin Q.n) ℂ) (locPt p),
      Ideal.Quotient.algebraMap_eq]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem _ hf)
  have h𝔮'p : 𝔮' ≤ ptIdeal p := by
    intro f hf
    by_contra hfp
    rw [h𝔮', RingHom.mem_ker, IsScalarTower.algebraMap_apply (MvPolynomial (Fin Q.n) ℂ) (locPt p),
      Ideal.Quotient.algebraMap_eq] at hf
    have hu : IsUnit (algebraMap (MvPolynomial (Fin Q.n) ℂ) (locPt p) f) :=
      IsLocalization.map_units (locPt p) (⟨f, hfp⟩ : (ptIdeal p).primeCompl)
    have := (hu.map (Ideal.Quotient.mk (Ideal.map (algebraMap _ (locPt p)) Q.K))).ne_zero
    exact this hf
  have h𝔮𝔮' : 𝔮 ≤ 𝔮' := by
    obtain ⟨Q', hQ'min, hQ'le⟩ := Ideal.exists_minimalPrimes_le hK𝔮'
    obtain ⟨q0, -, -, hu, -⟩ := regular_point_unique_minimalPrime Q.K p
    rw [hu 𝔮 h𝔮min h𝔮x, ← hu Q' hQ'min (hQ'le.trans h𝔮'p)]
    exact hQ'le
  have h𝔮prime : 𝔮.IsPrime := h𝔮min.1.1
  set F := S.h * ∏ l ∈ S.J, S.r l with hF
  have hFbd : F ∈ Q.bdIdeal w.Zb := S.mem_bd
  have hFq : F ∉ 𝔮 := by
    intro hmem
    rcases h𝔮prime.mem_or_mem hmem with hh | hprod
    · exact S.eval_h (by simpa [ptIdeal, RingHom.mem_ker] using h𝔮x hh)
    · haveI := h𝔮prime
      obtain ⟨l, -, hl⟩ := Ideal.IsPrime.prod_mem_iff.mp hprod
      have h0 : algebraMap _ (locRing Q.K p) (S.r l) = 0 := h𝔮𝔮' hl
      exact ne_zero_of_span_eq_maximalIdeal hdL (fun l => algebraMap _ (locRing Q.K p) (S.r l))
        (S.span_eq.trans hmax) l h0

  have hGq : G ∉ 𝔮 := fun hG𝔮 => hG (by simpa [ptIdeal, RingHom.mem_ker] using h𝔮x hG𝔮)
  have hFGq : F * G ∉ 𝔮 := fun hm => (h𝔮prime.mem_or_mem hm).elim hFq hGq
  obtain ⟨y, hy𝔮, hyFG⟩ : ∃ y : Fin Q.n → ℂ, (∀ f ∈ 𝔮, eval y f = 0) ∧ eval y (F * G) ≠ 0 := by
    by_contra hno
    push Not at hno
    apply hFGq
    have : F * G ∈ vanishingIdeal ℂ (zeroLocus ℂ 𝔮) := by
      rw [mem_vanishingIdeal_iff]
      intro y hy
      exact hno y (fun f hf => by simpa using hy f hf)
    rwa [vanishingIdeal_zeroLocus_eq_radical, h𝔮prime.radical] at this
  obtain ⟨x'', ⟨hx''V, hcl, hco⟩, -⟩ :=
    Q.existsUnique_closed_coord y (fun f hf => hy𝔮 f (h𝔮min.1.2 hf))
  have hyF : eval y F ≠ 0 := fun h0 => hyFG (by rw [eval_mul, h0, zero_mul])
  have hyG : eval y G ≠ 0 := fun h0 => hyFG (by rw [eval_mul, h0, mul_zero])
  refine ⟨⟨x'', hcl⟩, hx''V, ?_, ?_, by rw [hco]; exact hyG⟩
  · intro f hf
    show f ∈ ptIdeal (Q.coord x'' hx''V)
    rw [hco, ptIdeal, RingHom.mem_ker]
    exact hy𝔮 f hf
  · intro hB
    have hsupp : x'' ∈ (w.Zb.support : Set w.W) := by
      rw [w.support_Zb]; exact hB
    have := (Q.zero_bdIdeal_iff w.Zb x'' hx''V hcl).mpr hsupp F hFbd
    rw [hco] at this
    exact hyF this


set_option backward.isDefEq.respectTransparency.types false in
theorem WData.ringKrullDim_stalk_off (w : WData P D hP) (e : ℕ)
    (hdim : ∀ (p : (k : K) → ι k) (z : (Σ k, ι k) → ℂ), (∀ h ∈ chartIdeal P p, eval z h = 0) →
      ringKrullDim (chartLocRing P p z) = e)
    (y : w.M) (hy : w.π.base y.1 ∉ (projB P D hP : Set (projX P hP))) :
    ringKrullDim (w.W.presheaf.stalk y.1) = e := by
  have := w.lft
  have := w.isIso_off
  have hU : y.1 ∈ w.π ⁻¹ᵁ projBCompl P D hP := hy
  have hiso : IsIso (w.π.stalkMap y.1) := by
    have h := (MorphismProperty.isomorphisms CommRingCat).arrow_mk_iso_iff
      (morphismRestrictStalkMap w.π (projBCompl P D hP) ⟨y.1, hU⟩)
    haveI hoi : IsOpenImmersion (w.π ∣_ projBCompl P D hP) := IsOpenImmersion.of_isIso _
    have h2 : IsIso ((w.π ∣_ projBCompl P D hP).stalkMap ⟨y.1, hU⟩) := inferInstance
    exact h.mp h2
  rw [← ringKrullDim_eq_of_ringEquiv (asIso (w.π.stalkMap y.1)).commRingCatIsoToRingEquiv]
  have hcl : IsClosed ({w.π.base y.1} : Set (projX P hP)) :=
    (val_comp (w.π ≫ toSpecC hP) (toSpecC hP) w.π rfl (U := ⊤) (V := ⊤) (by simp) 0 y.1 trivial
      y.2).1
  obtain ⟨p, hp⟩ := chartOpen_cover hP (w.π.base y.1)
  obtain ⟨z, hz, -, ⟨ψ⟩⟩ := exists_closedPoint_stalk hP p _ hp hcl
  rw [ringKrullDim_eq_of_ringEquiv ψ]
  exact hdim p z hz

theorem WData.ringKrullDim_stalk (w : WData P D hP) (e : ℕ) (hD : IsMultiHomogIdeal D)
    (hcomp : ∀ Q ∈ P.minimalPrimes, IsRelevant Q → ¬ D ≤ Q)
    (hdim : ∀ (p : (k : K) → ι k) (z : (Σ k, ι k) → ℂ), (∀ h ∈ chartIdeal P p, eval z h = 0) →
      ringKrullDim (chartLocRing P p z) = e) :
    ∀ x : w.M, ringKrullDim (w.W.presheaf.stalk x.1) = e := by

  have offB : ∀ y : w.M, w.π.base y.1 ∉ (projB P D hP : Set (projX P hP)) →
      ringKrullDim (w.W.presheaf.stalk y.1) = e :=
    w.ringKrullDim_stalk_off e hdim
  intro x
  obtain ⟨c, hc⟩ := w.cover x
  have hxV : x.1 ∈ (w.pres c.1 c.2).V := hc
  rw [(w.pres c.1 c.2).ringKrullDim_stalk x.1 hxV x.2]
  have := ((w.pres c.1 c.2).isRegularLocalRing_stalk_iff x.1 hxV x.2).mp (w.regular x.1)
  obtain ⟨𝔮, h𝔮min, h𝔮x, -, -⟩ :=
    regular_point_unique_minimalPrime (w.pres c.1 c.2).K ((w.pres c.1 c.2).coord x.1 hxV)

  obtain ⟨x', hx'V, h𝔮x', hx'B, -⟩ :=
    w.exists_closed_off (w.pres c.1 c.2) x hxV 𝔮 h𝔮min h𝔮x 1 (by simp)
  have := ((w.pres c.1 c.2).isRegularLocalRing_stalk_iff x'.1 hx'V x'.2).mp (w.regular x'.1)
  rw [ringKrullDim_locRing_eq_of_minimalPrime (w.pres c.1 c.2).K _ _ 𝔮 h𝔮min h𝔮x h𝔮x',
    ← (w.pres c.1 c.2).ringKrullDim_stalk x'.1 hx'V x'.2]
  exact offB x' hx'B

theorem WData.dim_coord (w : WData P D hP) {e : ℕ}
    (he : ∀ x : w.M, ringKrullDim (w.W.presheaf.stalk x.1) = e) (c : w.Idx) (x : w.M)
    (hx : x ∈ w.src c) : ringKrullDim (locRing (w.pres c.1 c.2).K (w.coord c x)) = e := by
  have h1 : w.coord c x = (w.pres c.1 c.2).coord x.1 hx := by
    unfold WData.coord
    exact dif_pos hx
  rw [h1, ← (w.pres c.1 c.2).ringKrullDim_stalk x.1 hx x.2]
  exact he x

end ReciprocityTheory.AnForm.R
end

section

namespace ReciprocityTheory.AnForm.R

open MvPolynomial AlgebraicGeometry CategoryTheory

noncomputable section

variable {K : Type} [Fintype K] [Nonempty K] {ι : K → Type} [∀ k, Fintype (ι k)]
variable {P D : Ideal (MvPolynomial (Σ k, ι k) ℂ)} {hP : IsMultiHomogIdeal P}

namespace WData

variable (w : WData P D hP)

theorem surj' (hD : IsMultiHomogIdeal D) (z : (Σ k, ι k) → ℂ) (hz : z ∈ conePts P)
    (hzD : z ∉ conePts D) :
    ∃ c, ∃ x ∈ w.src c, SameOrbit (fun q => eval (w.coord c x) (w.lift c q)) z := by
  have := w.isIso_off
  obtain ⟨p, hzp, -⟩ := exists_chart z hz.1
  have hzc : ∀ h ∈ chartIdeal P p, eval (affCoord p z) h = 0 :=
    (mem_conePts_iff_chartIdeal hP p z hzp).1 hz
  obtain ⟨y, hy, hyc, hyv⟩ := exists_closed_of_chartIdeal (hP := hP) p (affCoord p z) hzc
  have hyB : y ∈ projBCompl P D hP := by
    intro hB
    have h1 := (mem_projB_iff_val hD p y hy hyc).1 hB
    rw [funext hyv] at h1
    exact hzD ((mem_conePts_iff_affCoord hD p z hzp).2 h1)
  obtain ⟨x, ⟨hxc, -⟩, hxy⟩ := (bijOn_closedPoints_of_isIso (sW := w.π ≫ toSpecC hP)
    (sX := toSpecC hP) w.π rfl (projBCompl P D hP)).2.2 ⟨hyc, hyB⟩
  subst hxy
  have hxp : x ∈ w.π ⁻¹ᵁ (chartOpen hP p).1 := hy
  rw [← w.iSup_pres p] at hxp
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hxp
  refine ⟨⟨p, i⟩, ⟨x, hxc⟩, hi, ?_⟩
  have hl : (fun q => eval (w.coord ⟨p, i⟩ ⟨x, hxc⟩) (w.lift ⟨p, i⟩ q)) = affCoord p z := by
    funext q
    rw [w.lift_eval_eq_val ⟨p, i⟩ ⟨x, hxc⟩ hi q]
    exact hyv q
  rw [hl]
  exact sameOrbit_symm' (sameOrbit_affCoord p z hzp)

theorem inj' (hD : IsMultiHomogIdeal D) (c c' : w.Idx) (x : w.M) (hx : x ∈ w.src c) (x' : w.M)
    (hx' : x' ∈ w.src c') (hxD : (fun q => eval (w.coord c x) (w.lift c q)) ∉ conePts D)
    (ho : SameOrbit (fun q => eval (w.coord c x) (w.lift c q))
      (fun q => eval (w.coord c' x') (w.lift c' q))) : x = x' := by
  have := w.isIso_off
  obtain ⟨a, ha0, ha⟩ := ho
  have hxc : w.π.base x.1 ∈ (chartOpen hP c.1).1 := w.le_pres c.1 c.2 hx
  have hone : ∀ k, eval (w.coord c x) (w.lift c ⟨k, c.1 k⟩) = 1 := fun k => by simp [lift]
  have hx'c : ∀ k, eval (w.coord c' x') (w.lift c' ⟨k, c.1 k⟩) ≠ 0 := by
    intro k h0
    have := congrFun ha ⟨k, c.1 k⟩
    simp only [hone k, h0, mul_zero] at this
    exact one_ne_zero this
  have hpx' : w.π.base x'.1 ∈ (chartOpen hP c.1).1 := (w.mem_chartOpen_iff c' x' hx' c.1).2 hx'c
  have heq : w.π.base x.1 = w.π.base x'.1 := by
    refine eq_of_val_chartCoord c.1 _ _ hxc hpx' (w.isClosed_image c x hx)
      (w.isClosed_image c' x' hx') fun q => ?_
    rw [w.val_chartCoord c x hx c.1 hxc q, w.val_chartCoord c' x' hx' c.1 hpx' q,
      affCoord_eq_of_sameOrbit c.1 ⟨a, ha0, ha⟩]
  have hxU : w.π.base x.1 ∈ projBCompl P D hP :=
    fun h => hxD ((w.mem_projB_iff_lift hD c x hx).1 h)
  have hbij := bijOn_closedPoints_of_isIso (sW := w.π ≫ toSpecC hP) (sX := toSpecC hP) w.π rfl
    (projBCompl P D hP)
  exact Subtype.ext (hbij.injOn ⟨x.2, hxU⟩ ⟨x'.2, heq ▸ hxU⟩ heq)

end WData

end

end ReciprocityTheory.AnForm.R
end
