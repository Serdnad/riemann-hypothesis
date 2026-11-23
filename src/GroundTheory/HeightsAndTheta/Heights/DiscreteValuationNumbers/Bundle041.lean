module

public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle030
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle029
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle004
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle005
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle031
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Algebra.GroupWithZero.Indicator

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

universe u

open IsLocalRing

theorem LengthMapIdealLe.proof : LengthMapIdealLe.Statement.{u} := by
  intro C D _ _ _ φ hφ
  suffices key : ∀ n : ℕ, ∀ I : Ideal C, Module.length C (C ⧸ I) = n →
      Module.length D (D ⧸ I.map φ) ≤ n by
    intro I
    cases h : Module.length C (C ⧸ I) with
    | top => exact le_top
    | coe n => exact key n I h
  intro n
  induction n with
  | zero =>
    intro I hI
    have hs : Subsingleton (C ⧸ I) := Module.length_eq_zero_iff.mp (by exact_mod_cast hI)
    have hItop : I = ⊤ := Ideal.Quotient.subsingleton_iff.mp hs
    subst hItop
    rw [Ideal.map_top]
    have : Subsingleton (D ⧸ (⊤ : Ideal D)) := Ideal.Quotient.subsingleton_iff.mpr rfl
    simp [Module.length_eq_zero]
  | succ n ih =>
    intro I hI
    have hfin : IsFiniteLength C (C ⧸ I) :=
      Module.length_ne_top_iff.mp (by rw [hI]; exact ENat.natCast_ne_top _)
    have : IsArtinian C (C ⧸ I) := (isFiniteLength_iff_isNoetherian_isArtinian.mp hfin).2
    have : Nontrivial (C ⧸ I) :=
      Module.length_pos_iff.mp (by rw [hI]; exact_mod_cast Nat.succ_pos n)
    have : IsAtomic (Submodule C (C ⧸ I)) := isAtomic_of_orderBot_wellFounded_lt wellFounded_lt
    obtain ⟨N, hN, -⟩ := (eq_bot_or_exists_atom_le (⊤ : Submodule C (C ⧸ I))).resolve_left top_ne_bot
    have hNs : IsSimpleModule C N := isSimpleModule_iff_isAtom.mpr hN

    have hlen : Module.length C (C ⧸ I) = Module.length C N + Module.length C ((C ⧸ I) ⧸ N) :=
      Module.length_eq_add_of_exact N.subtype N.mkQ N.injective_subtype N.mkQ_surjective
        (LinearMap.exact_subtype_mkQ N)
    rw [Module.length_eq_one (R := C) (M := N), hI] at hlen
    have hq : Module.length C ((C ⧸ I) ⧸ N) = n := by
      have hx : Module.length C ((C ⧸ I) ⧸ N) ≠ ⊤ := by
        intro h
        rw [h, add_top] at hlen
        exact ENat.natCast_ne_top _ hlen
      obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp hx
      rw [← hk] at hlen ⊢
      norm_cast at hlen ⊢
      omega

    obtain ⟨v, hvN, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hN.1
    have hspan : Submodule.span C {v} = N :=
      (hN.le_iff.mp ((Submodule.span_singleton_le_iff_mem _ _).mpr hvN)).resolve_left
        (by simpa using hv0)
    obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective v

    set I' : Ideal C := N.comap (Submodule.mkQ I) with hI'def
    have hII' : I ≤ I' := by
      intro x hx
      show Submodule.mkQ I x ∈ N
      rw [Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero I).mpr hx]
      exact N.zero_mem
    have hI'N : Submodule.map (Submodule.mkQ I) I' = N :=
      Submodule.map_comap_eq_of_surjective (Submodule.mkQ_surjective I) N
    have hlenI' : Module.length C (C ⧸ I') = n := by
      rw [← (Submodule.quotientQuotientEquivQuotient I I' hII').length_eq, hI'N, hq]
    have ih' := ih I' hlenI'

    set m : Ideal C := Module.annihilator C N
    have hm : m.IsMaximal := IsSimpleModule.annihilator_isMaximal
    have hmc : ∀ x ∈ m, x * c ∈ I := by
      intro x hx
      have h1 := Module.mem_annihilator.mp hx ⟨_, hvN⟩
      have h2 : x • (Ideal.Quotient.mk I c) = 0 := congrArg Subtype.val h1
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_mul]
      simpa [Algebra.smul_def] using h2

    have hI'le : I' ≤ I ⊔ Ideal.span {c} := by
      intro x hx
      have hx' : Submodule.mkQ I x ∈ Submodule.span C {Ideal.Quotient.mk I c} := hspan ▸ hx
      obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hx'
      have hxa : Ideal.Quotient.mk I x = Ideal.Quotient.mk I (a * c) := by
        rw [map_mul]
        simpa [Algebra.smul_def] using ha.symm
      have hd : x - a * c ∈ I := Ideal.Quotient.eq.mp hxa
      rw [show x = (x - a * c) + a * c by ring]
      exact Submodule.add_mem_sup hd (Ideal.mul_mem_left _ a (Ideal.subset_span rfl))

    set J : Ideal D := I.map φ
    set J' : Ideal D := I'.map φ
    have hJJ' : J ≤ J' := Ideal.map_mono hII'
    have hJ'le : J' ≤ J ⊔ Ideal.span {φ c} := by
      calc J' ≤ (I ⊔ Ideal.span {c}).map φ := Ideal.map_mono hI'le
        _ = J ⊔ Ideal.span {φ c} := by rw [Ideal.map_sup, Ideal.map_span, Set.image_singleton]
    set w : D ⧸ J := Submodule.Quotient.mk (p := J) (φ c)
    set K : Submodule D (D ⧸ J) := Submodule.map (Submodule.mkQ J) J'
    have hK : K ≤ Submodule.span D {w} := by
      rintro _ ⟨y, hy, rfl⟩
      obtain ⟨p, hp, q, hq', rfl⟩ := Submodule.mem_sup.mp (hJ'le hy)
      obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.mp hq'
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_add, (Submodule.Quotient.mk_eq_zero J).mpr hp,
        zero_add, ← smul_eq_mul, Submodule.Quotient.mk_smul]
      exact Submodule.smul_mem _ b (Submodule.mem_span_singleton_self w)
    have hlenD : Module.length D (D ⧸ J) = Module.length D K + Module.length D (D ⧸ J') := by
      rw [Module.length_eq_add_of_exact K.subtype K.mkQ K.injective_subtype K.mkQ_surjective
        (LinearMap.exact_subtype_mkQ K), (Submodule.quotientQuotientEquivQuotient J J' hJJ').length_eq]

    have hmX : m.map φ ≤ LinearMap.ker (LinearMap.toSpanSingleton D (D ⧸ J) w) := by
      rw [Ideal.map_le_iff_le_comap]
      intro x hx
      rw [Ideal.mem_comap, LinearMap.mem_ker, LinearMap.toSpanSingleton_apply, ← Submodule.Quotient.mk_smul,
        smul_eq_mul, ← map_mul, Submodule.Quotient.mk_eq_zero]
      exact Ideal.mem_map_of_mem φ (hmc x hx)
    have hKle1 : Module.length D K ≤ 1 := by
      rcases hφ m hm with htop | hle
      · have hw : w = 0 := by
          have h1 : (1 : D) ∈ LinearMap.ker (LinearMap.toSpanSingleton D (D ⧸ J) w) :=
            hmX (htop ▸ Submodule.mem_top)
          simpa using h1
        have hK0 : K = ⊥ := le_bot_iff.mp (hK.trans (by simp [hw]))
        rw [hK0, Module.length_bot]
        exact zero_le
      · have h1 : maximalIdeal D ≤ LinearMap.ker (LinearMap.toSpanSingleton D (D ⧸ J) w) :=
          hle.trans hmX
        let f := (maximalIdeal D).liftQ (LinearMap.toSpanSingleton D (D ⧸ J) w) h1
        have hrange : LinearMap.range f = Submodule.span D {w} := by
          rw [Submodule.range_liftQ, LinearMap.range_toSpanSingleton]
        have : IsSimpleModule D (D ⧸ maximalIdeal D) :=
          isSimpleModule_iff_quot_maximal.mpr ⟨_, inferInstance, ⟨LinearEquiv.refl _ _⟩⟩
        calc Module.length D K ≤ Module.length D (Submodule.span D {w}) :=
              Module.length_le_of_injective (Submodule.inclusion hK) (Submodule.inclusion_injective hK)
          _ = Module.length D (LinearMap.range f) := by rw [hrange]
          _ ≤ Module.length D (D ⧸ maximalIdeal D) :=
              Module.length_le_of_surjective f.rangeRestrict f.surjective_rangeRestrict
          _ = 1 := Module.length_eq_one _ _
    calc Module.length D (D ⧸ I.map φ) = Module.length D K + Module.length D (D ⧸ J') := hlenD
      _ ≤ 1 + n := add_le_add hKle1 ih'
      _ = ((n + 1 : ℕ) : ℕ∞) := by push_cast; ring

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

universe u

section Helpers

variable {K : Type*} [Fintype K] [DecidableEq K] {ι : K → Type} {R : Type*} [CommRing R]

theorem powMonomial_isMultiHomog (e : K → ℕ) (i : ∀ k, ι k) :
    IsMultiHomog (powMonomial (R := R) e i) e := by
  have h := IsWeightedHomogeneous.prod (R := R) Finset.univ (fun k => (X ⟨k, i k⟩ : MRing ι R) ^ e k)
    (fun k => e k • blockWeight ι ⟨k, i k⟩) (fun k _ => (isWeightedHomogeneous_X R _ _).pow (e k))
  have key : (∑ k, e k • blockWeight ι ⟨k, i k⟩) = e := by
    funext k'
    simp [blockWeight, Finset.sum_apply, Pi.single_apply]
  rw [key] at h
  exact h


omit [Fintype K] [DecidableEq K] in
theorem liftForm_C_eq {J : Type} (a : R) : liftForm (ι := ι) (J := J) (C a : MRing ι R) = C a := by
  simp [liftForm]


omit [Fintype K] [DecidableEq K] in
theorem cycEval_congr_on_support {n n' : Ideal (MRing ι R) → ℤ} (Z : Ideal (MRing ι R) → ℤ)
    (h : ∀ W, Z W ≠ 0 → n W = n' W) : cycEval n Z = cycEval n' Z := by
  unfold cycEval
  refine finsum_congr fun W => ?_
  by_cases hW : Z W = 0
  · rw [hW, zero_mul, zero_mul]
  · rw [h W hW]


open scoped Classical in
omit [Fintype K] [DecidableEq K] in
open Classical in
theorem cycEval_ite (p : Ideal (MRing ι R) → Prop) (A B : Ideal (MRing ι R) → ℤ)
    (Z : Ideal (MRing ι R) → ℤ) (hZ : (Function.support Z).Finite) :
    cycEval (fun W => if p W then A W else B W) Z =
      cycEval (fun W => if p W then A W else 0) Z + cycEval (fun W => if p W then 0 else B W) Z := by
  unfold cycEval
  rw [← finsum_add_distrib (hZ.subset (Function.support_mul_subset_left _ _))
    (hZ.subset (Function.support_mul_subset_left _ _))]
  refine finsum_congr fun W => ?_
  dsimp only
  split_ifs <;> ring


omit [Fintype K] [DecidableEq K] in
theorem vecCons_liftMDeg {d : ℕ} (c : K → ℕ) (L : Fin d → K → ℤ) :
    Matrix.vecCons (fun k => ((liftMDeg c k : ℕ) : ℤ)) (liftDegs L) =
      liftDegs (Matrix.vecCons (fun k => (c k : ℤ)) L) := by
  funext i o
  refine Fin.cases ?_ (fun i => ?_) i <;> cases o <;> simp [liftDegs, liftDeg, liftMDeg]

end Helpers

theorem BlowUpInvariance.proof (hvert : BlowUpVerticalPush.Statement.{u})
    (hdiv : BlowUpDivisorPush.Statement.{u}) (hhor : BlowUpHorizontalCorresp.Statement.{u})
    (hcomp : HorizontalComponentModel.Statement.{u}) (hfin : DivCycleFiniteSupport.Statement.{u}) :
    BlowUpInvariance.Statement.{u} := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ P d hP b f g hD c s hs hsP hsH e hce m hm hmP hmH L
  obtain ⟨bf, bg, hf, hg, hb⟩ := hD.1.degrees
  have hPp := hP.multiProj.isPrime

  have hdeg : bf + e = c + bg := by
    funext k
    have h1 := hce k
    have h2 := congrFun hb k
    simp only [Pi.add_apply] at h1 h2 ⊢
    omega
  have hN : ∀ j, IsMultiHomog (blowUpGens s g f m e j) (c + bg) := by
    rintro (_ | _ | i)
    · exact hs.mul hg
    · exact hdeg ▸ hf.mul hm
    · exact hdeg ▸ hf.mul (powMonomial_isMultiHomog e i)
  have hfm : f * m ∉ P := fun h => (hPp.mem_or_mem h).elim hD.1.num_not_mem hmP
  refine ⟨?_, ?_⟩
  · unfold cutIdentityLeftSide
    rw [vecCons_liftMDeg]
    exact hdiv O ϖ hϖ K ι _ P (d + 1) hP b f g hD.1 _ _ hN ⟨some none, hfm⟩ _

  have hinv : ∀ W : Ideal (MRing ι O), W.IsPrime → P ≤ W → IsRelevant W → (C ϖ : MRing ι O) ∉ W →
      ∃ j, ∀ j', ∃ v w : MRing ι O, v ∉ W ∧
        v * blowUpGens s g f m e j' - w * blowUpGens s g f m e j ∈ P := by
    intro W hW hPW hrel hϖW
    choose i hi using hrel
    have hμ : powMonomial e i ∉ W := by
      rw [powMonomial, hW.prod_mem_iff]
      rintro ⟨k, -, hk⟩
      exact hi k (hW.mem_of_pow_mem _ hk)
    obtain ⟨u', v', hu', hv', h⟩ := hD.1.unit_off_special W hW hPW (fun k => ⟨i k, hi k⟩) hϖW
    refine ⟨some (some i), ?_⟩
    rintro (_ | _ | i')
    · refine ⟨v' * powMonomial e i, s * u', fun h' => (hW.mem_or_mem h').elim hv' hμ, ?_⟩
      have e1 : v' * powMonomial e i * (s * g) - s * u' * (f * powMonomial e i) =
          -(s * powMonomial e i) * (u' * f - v' * g) := by ring
      simpa only [blowUpGens, e1] using P.mul_mem_left _ h
    · exact ⟨powMonomial e i, m, hμ, by simp only [blowUpGens]; rw [show powMonomial e i * (f * m) -
        m * (f * powMonomial e i) = 0 by ring]; exact P.zero_mem⟩
    · exact ⟨powMonomial e i, powMonomial e i', hμ, by simp only [blowUpGens]; rw [show powMonomial e i *
        (f * powMonomial e i') - powMonomial e i' * (f * powMonomial e i) = 0 by ring]; exact P.zero_mem⟩

  obtain ⟨htrans, hpt⟩ := hhor O ϖ hϖ K ι _ P (d + 1) hP _ _ hN ⟨some none, hfm⟩ hinv c s hs hsP
  unfold cutIdentityRightSide
  rw [cycEval_ite _ _ _ _ (hfin O (Option K) (extIdx ι (BlowUpIdx ι)) (blowUpOf P (blowUpGens s g f m e))
    (liftForm s)), cycEval_ite _ _ _ _ (hfin O K ι P s)]
  congr 1
  · have hdegrees : Matrix.vecCons (liftDeg b) (liftDegs L) = liftDegs (Matrix.vecCons b L) := by
      funext i
      exact Fin.cases rfl (fun _ => rfl) i
    rw [hdegrees]
    exact hvert O ϖ hϖ K ι _ P (d + 1) hP _ _ hN ⟨some none, hfm⟩ c s hs hsP (Matrix.vecCons b L)
  rw [← htrans (fun W => cycEval (fun G => vNum G L) (ratDiv W f g))]
  refine cycEval_congr_on_support _ fun W hW => ?_
  by_cases hϖ' : (C ϖ : MRing (extIdx ι (BlowUpIdx ι)) O) ∈ W
  · simp only [ite_eq_left hϖ']
  rw [ite_eq_right hϖ', ite_eq_right hϖ']
  obtain ⟨hWs, hWeq⟩ := hpt W hW hϖ'
  have hϖW : (C ϖ : MRing ι O) ∉ W.comap (liftForm (ι := ι) (J := BlowUpIdx ι) (R := O)) := by
    rwa [Ideal.mem_comap, liftForm_C_eq]
  generalize W.comap (liftForm (ι := ι) (J := BlowUpIdx ι) (R := O)) = V at hWs hWeq hϖW ⊢
  have hWm := hcomp O ϖ hϖ K ι P d hP c s hs hsP _ hWs hϖW
  have hWv := hsH _ hWs hϖW
  have hfmW : blowUpGens s g f m e (some none) ∉ V :=
    fun h => (hWm.multiProj.isPrime.mem_or_mem h).elim hWv.num_not_mem (hmH _ hWs hϖW)
  rw [hWeq ⟨_, hfmW⟩]
  exact hdiv O ϖ hϖ K ι _ _ d hWm b f g hWv _ _ hN ⟨_, hfmW⟩ L

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

section Pullback

variable {K : Type*} {ι : K → Type} {J : Type} {R : Type*} [CommRing R]

theorem liftForm_mem_blowUpOf_of_mem (P : Ideal (MRing ι R)) (u : J → MRing ι R) {p : MRing ι R}
    (hp : p ∈ P) : liftForm (J := J) p ∈ blowUpOf P u := by
  let φ : MRing ι R →ₐ[R] Polynomial (MRing ι R ⧸ P) :=
    (Polynomial.CAlgHom (R := R) (A := MRing ι R ⧸ P)).comp (Ideal.Quotient.mkₐ R P)
  have hcomp : (aeval (blowUpSubst P u)).comp (liftForm (ι := ι) (J := J) (R := R)) = φ := by
    apply MvPolynomial.algHom_ext
    intro v
    rw [AlgHom.comp_apply, liftForm, rename_X, aeval_X]
    rfl
  have h := DFunLike.congr_fun hcomp p
  rw [AlgHom.comp_apply] at h
  unfold blowUpOf
  rw [RingHom.mem_ker, h]
  show Polynomial.C (Ideal.Quotient.mk P p) = 0
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr hp, map_zero]

end Pullback

section Sums

open scoped Classical in
open Classical in
theorem finsum_sub_mul_eq_of_support {α : Type*} (Z₁ Z₂ n : α → ℤ) (p : α → Prop)
    (h₁ : (Function.support Z₁).Finite) (h₂ : (Function.support Z₂).Finite)
    (hv : ∀ W, Z₁ W - Z₂ W ≠ 0 → p W) :
    ∑ᶠ W, (Z₁ W - Z₂ W) * n W =
      ∑ᶠ W, Z₁ W * (if p W then n W else 0) - ∑ᶠ W, Z₂ W * (if p W then n W else 0) := by
  have e : ∀ W, (Z₁ W - Z₂ W) * n W =
      Z₁ W * (if p W then n W else 0) - Z₂ W * (if p W then n W else 0) := by
    intro W
    by_cases h : Z₁ W - Z₂ W = 0
    · rw [h, zero_mul, sub_eq_zero.mp h, sub_self]
    · rw [ite_eq_left (hv W h), ← sub_mul]
  rw [finsum_congr e, finsum_sub_distrib]
  · exact h₁.subset fun W hW => left_ne_zero_of_mul hW
  · exact h₂.subset fun W hW => left_ne_zero_of_mul hW

end Sums

theorem BlowUpDivisorPush.proof (hvert : BlowUpVerticalPush.Statement.{u}) :
    BlowUpDivisorPush.Statement.{u} := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ J _ P n hP b f g hD N u hu hu' a
  have hfin := DivCycleFiniteSupport.proof.{u}
  obtain ⟨bf, bg, hbf, hbg, -⟩ := hD.degrees

  have hvertB : ∀ W, divCycle (blowUpOf P u) (liftForm (J := J) f) W -
      divCycle (blowUpOf P u) (liftForm (J := J) g) W ≠ 0 → (C ϖ : MRing (extIdx ι J) O) ∈ W := by
    intro W hW
    by_contra hϖW
    have hsupp : W.IsPrime ∧ blowUpOf P u ≤ W ∧ IsRelevant W := by
      by_cases h1 : divCycle (blowUpOf P u) (liftForm (J := J) f) W = 0
      · have h2 : divCycle (blowUpOf P u) (liftForm (J := J) g) W ≠ 0 := by
          intro h2; apply hW; rw [h1, h2, sub_zero]
        exact le_and_isRelevant_of_divCycle_ne_zero h2
      · exact le_and_isRelevant_of_divCycle_ne_zero h1
    obtain ⟨hWp, hBW, hWrel⟩ := hsupp
    let W₀ : Ideal (MRing ι O) := W.comap (liftForm (ι := ι) (J := J) (R := O))
    have hW₀ : W₀.IsPrime := Ideal.comap_isPrime _ _
    have hPW₀ : P ≤ W₀ := fun p hp => hBW (liftForm_mem_blowUpOf_of_mem P u hp)
    have hrel₀ : IsRelevant W₀ := by
      intro k
      obtain ⟨i, hi⟩ := hWrel (some k)
      refine ⟨i, fun h => hi ?_⟩
      have h' : liftForm (ι := ι) (J := J) (R := O) (X ⟨k, i⟩) ∈ W := h
      rwa [liftForm, rename_X] at h'
    have hϖ₀ : (C ϖ : MRing ι O) ∉ W₀ := by
      intro h
      have h' : liftForm (ι := ι) (J := J) (R := O) (C ϖ) ∈ W := h
      rw [liftForm, rename_C] at h'
      exact hϖW h'
    obtain ⟨s, t, hs, ht, hst⟩ := hD.unit_off_special W₀ hW₀ hPW₀ hrel₀ hϖ₀
    apply hW
    rw [divCycle_eq_of_mul_sub_mem (u := liftForm (J := J) s) (v := liftForm (J := J) t) hs ht ?_,
      sub_self]
    have := liftForm_mem_blowUpOf_of_mem (J := J) P u hst
    rwa [map_sub, map_mul, map_mul] at this
  have e₁ := hvert O ϖ hϖ K ι J P n hP N u hu hu' bf f hbf hD.num_not_mem a
  have e₂ := hvert O ϖ hϖ K ι J P n hP N u hu hu' bg g hbg hD.den_not_mem a
  unfold cycEval at e₁ e₂
  unfold cycEval ratDiv
  rw [finsum_sub_mul_eq_of_support (divCycle (blowUpOf P u) (liftForm (J := J) f))
      (divCycle (blowUpOf P u) (liftForm (J := J) g)) _ _ (hfin _ _ _ _ _) (hfin _ _ _ _ _) hvertB,
    finsum_sub_mul_eq_of_support (divCycle P f) (divCycle P g) _ _ (hfin _ _ _ _ _)
      (hfin _ _ _ _ _) hD.vertical, e₁, e₂]

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

universe u

theorem ResidualContraction.proof (hle : BlowUpOrderLe.Statement.{u})
    (hcomp : ResidualContractionComponent.Statement.{u}) :
    ResidualContraction.Statement.{u} := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ P d hP b f g hD c s hs hsP hsH e he m hm hmP hmH G' hϖG' hsG' hresG'
    x hxP
  have hGmin := hcomp O ϖ hϖ K ι P d hP b f g hD c s hs hsP hsH e he m hm hmP hmH G' hϖG' hsG' hresG'

  have hG'supp : G' ∈ (blowUpOf P (blowUpGens s g f m e) ⊔ Ideal.span {liftForm s}).minimalPrimes ∧
      IsRelevant G' := by
    by_contra h
    unfold divCycle at hsG'
    rw [dite_eq_right h] at hsG'
    exact lt_irrefl _ hsG'

  have hsP' : liftForm (J := BlowUpIdx ι) s ∉ blowUpOf P (blowUpGens s g f m e) := by
    rw [blowUpOf, RingHom.mem_ker, aeval_blowUpSubst_liftForm, Polynomial.C_eq_zero,
      Ideal.Quotient.eq_zero_iff_mem]
    exact hsP
  exact hle O K ι (BlowUpIdx ι) P hP.multiProj.isPrime (blowUpGens s g f m e) G' (liftForm s) hsP'
    hG'supp.1 hG'supp.2 s hsP hGmin x hxP

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

universe u

theorem MultiHomogPrimeAvoid.proof : MultiHomogPrimeAvoid.Statement.{u} := by
  intro R _ K _ _ ι S hfin hS
  obtain ⟨e, L, hL, he, hLS⟩ := exists_form_avoid_primes hfin.toFinset
    (fun W hW => hS W (hfin.mem_toFinset.mp hW)) (fun _ => 1)
  exact ⟨e, L, hL, fun k => he k, fun Q hQ => hLS Q (hfin.mem_toFinset.mpr hQ)⟩

end GroundTheory.Heights₂.Heights.NumbersDVR
end
