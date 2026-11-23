module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle029
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle045
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle028
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle002
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Assembly
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle051
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle037
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
import Mathlib.RingTheory.KrullDimension.Field
import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

theorem IsolatedFibreOpenPoly.full : IsolatedFibreOpenPoly.Statement :=
  IsolatedFibreOpenPoly.proof
    (IndefiniteRowSideFullHecke.ComplexSets.IsolatedFibreOpenOfGeneric.proof
      (IndefiniteRowSideFullHecke.ComplexSets.GenericProjectionFinite.equiv.mp ComplexSets.GenericProjectionFinite.full)
      IndefiniteRowSideFullHecke.ComplexSets.FiniteMapOpen.full)

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ComplexSets

open MvPolynomial

noncomputable section

theorem LinearNoetherNormalization.ringKrullDim_quotient_le {R : Type*} [CommRing R] (J : Ideal R)
    (k : WithBot ℕ∞) (h : ∀ W ∈ J.minimalPrimes, ringKrullDim (R ⧸ W) ≤ k) :
    ringKrullDim (R ⧸ J) ≤ k := by
  rw [ringKrullDim_quotient]
  refine iSup_le fun l => ?_
  obtain ⟨W, hW, hle⟩ := Ideal.exists_minimalPrimes_le (show J ≤ l.head.1.asIdeal from l.head.2)
  let l' : LTSeries (PrimeSpectrum.zeroLocus (R := R) W) :=
    ⟨l.length, fun i => ⟨(l i).1, show (W : Set R) ⊆ (l i).1.asIdeal from hle.trans (l.head_le i)⟩,
      fun i => l.step i⟩
  calc (l.length : WithBot ℕ∞) = l'.length := rfl
    _ ≤ Order.krullDim (PrimeSpectrum.zeroLocus (R := R) W) := Order.LTSeries.length_le_krullDim l'
    _ = ringKrullDim (R ⧸ W) := (ringKrullDim_quotient W).symm
    _ ≤ k := h W hW

theorem LinearNoetherNormalization.exists_nat_of_le {x : WithBot ℕ∞} {d : ℕ} (h0 : 0 ≤ x)
    (hd : x ≤ d) : ∃ e : ℕ, e ≤ d ∧ x = e := by
  induction x using WithBot.recBotCoe with
  | bot => exact absurd h0 (by simp)
  | coe y =>
    induction y using ENat.recTopCoe with
    | top =>
      exfalso
      have h1 : ((⊤ : ℕ∞) : WithBot ℕ∞) ≤ ((d : ℕ∞) : WithBot ℕ∞) := by exact_mod_cast hd
      exact absurd (WithBot.coe_le_coe.mp h1) (by simp)
    | coe e => exact ⟨e, by exact_mod_cast hd, rfl⟩

theorem LinearNoetherNormalization.exists_monic_of_prefix {d e n : ℕ} (h : e ≤ d)
    (A : Matrix (Fin d) (Fin n) ℂ) (P : Ideal (MvPolynomial (Fin n) ℂ))
    (hP : IsFiniteProjection P (A.submatrix (Fin.castLE h) id)) (j : Fin n) :
    ∃ f : Polynomial (MvPolynomial (Fin d) ℂ), f.Monic ∧
      f.eval₂ (pullback A).toRingHom (X j) ∈ P := by
  obtain ⟨g, hg, hg0⟩ := hP.finite.to_isIntegral (Ideal.Quotient.mk P (X j))
  refine ⟨g.map (rename (R := ℂ) (Fin.castLE h)).toRingHom, hg.map _, ?_⟩
  rw [Polynomial.eval₂_map, ← Ideal.Quotient.eq_zero_iff_mem, Polynomial.hom_eval₂]
  refine (congrArg (fun φ => Polynomial.eval₂ φ (Ideal.Quotient.mk P (X j)) g) ?_).trans hg0
  apply MvPolynomial.ringHom_ext
  · intro r
    simp [projHom, pullback]
    rfl
  · intro i
    simp [projHom, pullback, linPoly]

theorem LinearNoetherNormalization.proof : LinearNoetherNormalization.Statement := by
  classical
  intro n d J hJ

  have hdim : ∀ P ∈ J.minimalPrimes, ∃ e : ℕ, e ≤ d ∧
      ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ P) = e := by
    intro P hP
    have : P.IsPrime := hP.1.1
    refine LinearNoetherNormalization.exists_nat_of_le ringKrullDim_nonneg_of_nontrivial ?_
    rw [← hJ]
    exact ringKrullDim_le_of_surjective (Ideal.Quotient.factor hP.1.2)
      (Ideal.Quotient.factor_surjective hP.1.2)

  have htop : ∃ P ∈ J.minimalPrimes, ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ P) = d := by
    by_contra hne
    push Not at hne
    rcases d with _ | d'
    · have hJt : J ≠ ⊤ := by
        rintro rfl
        have : Subsingleton (MvPolynomial (Fin n) ℂ ⧸ (⊤ : Ideal (MvPolynomial (Fin n) ℂ))) :=
          Ideal.Quotient.subsingleton_iff.mpr rfl
        rw [ringKrullDim_eq_bot_of_subsingleton] at hJ
        simp at hJ
      obtain ⟨M, hM, hJM⟩ := Ideal.exists_le_maximal J hJt
      obtain ⟨P, hP, -⟩ := Ideal.exists_minimalPrimes_le (J := M) hJM
      obtain ⟨e, he, he'⟩ := hdim P hP
      exact hne P hP (by rw [he', Nat.le_zero.mp he])
    · have hle := LinearNoetherNormalization.ringKrullDim_quotient_le J (d' : WithBot ℕ∞)
        (fun P hP => by
          obtain ⟨e, he, he'⟩ := hdim P hP
          have hne' : e ≠ d' + 1 := fun h => hne P hP (by rw [he', h])
          rw [he']
          exact_mod_cast (by omega : e ≤ d'))
      rw [hJ] at hle
      exact absurd hle (by norm_cast; omega)
  obtain ⟨P₀, hP₀, hP₀d⟩ := htop
  have hP₀p : P₀.IsPrime := hP₀.1.1
  obtain ⟨W₀, ⟨S₀, rfl⟩, ⟨A₀, p₀, hp₀S, hp₀⟩, hW₀⟩ :=
    FiniteProjectionsContainOpen.full n d P₀ hP₀p hP₀d
  have hp₀0 : p₀ ≠ 0 := fun h => hp₀ (by rw [h, map_zero])

  have hq : ∀ P ∈ J.minimalPrimes, ∃ q : MvPolynomial (Fin d × Fin n) ℂ, q ≠ 0 ∧
      ∀ A : Matrix (Fin d) (Fin n) ℂ, eval (fun ij : Fin d × Fin n => A ij.1 ij.2) q ≠ 0 →
        ∀ j, ∃ f : Polynomial (MvPolynomial (Fin d) ℂ), f.Monic ∧
          f.eval₂ (pullback A).toRingHom (X j) ∈ P := by
    intro P hP
    have : P.IsPrime := hP.1.1
    obtain ⟨e, he, hPe⟩ := hdim P hP
    obtain ⟨W, ⟨S, rfl⟩, ⟨B, p, hpS, hp⟩, hW⟩ := FiniteProjectionsContainOpen.full n e P this hPe
    refine ⟨rename (Prod.map (Fin.castLE he) id) p, fun h0 => ?_, fun A hA j => ?_⟩
    · apply hp
      rw [rename_injective _ ((Fin.castLE_injective he).prodMap Function.injective_id)
        (h0.trans (map_zero _).symm), map_zero]
    · rw [eval_rename] at hA
      exact LinearNoetherNormalization.exists_monic_of_prefix he A P (hW ⟨p, hpS, hA⟩) j
  choose! q hq0 hqA using hq
  have hfin := Ideal.finite_minimalPrimes_of_isNoetherianRing (MvPolynomial (Fin n) ℂ) J
  have hQ : p₀ * ∏ P ∈ hfin.toFinset, q P ≠ 0 :=
    mul_ne_zero hp₀0 (Finset.prod_ne_zero_iff.mpr fun P hP => hq0 P (hfin.mem_toFinset.mp hP))

  obtain ⟨x, hx⟩ : ∃ x, eval x (p₀ * ∏ P ∈ hfin.toFinset, q P) ≠ 0 := by
    by_contra! h
    exact hQ (MvPolynomial.funext fun x => by rw [h x, map_zero])
  let A : Matrix (Fin d) (Fin n) ℂ := Matrix.of fun i j => x (i, j)
  have hxA : (fun ij : Fin d × Fin n => A ij.1 ij.2) = x := rfl
  rw [← hxA, map_mul, map_prod] at hx
  have hall := Finset.prod_ne_zero_iff.mp (right_ne_zero_of_mul hx)
  have hA₀ : IsFiniteProjection P₀ A := hW₀ ⟨p₀, hp₀S, left_ne_zero_of_mul hx⟩

  have hint : ∀ j, (projHom J A).toRingHom.IsIntegralElem (Ideal.Quotient.mk J (X j)) := by
    intro j
    have hf : ∀ P ∈ J.minimalPrimes, ∃ f : Polynomial (MvPolynomial (Fin d) ℂ), f.Monic ∧
        f.eval₂ (pullback A).toRingHom (X j) ∈ P :=
      fun P hP => hqA P hP A (hall P (hfin.mem_toFinset.mpr hP)) j
    choose! f hfm hfP using hf
    have hFm : (∏ P ∈ hfin.toFinset, f P).Monic :=
      Polynomial.monic_prod_of_monic _ _ fun P hP => hfm P (hfin.mem_toFinset.mp hP)
    have hFrad : (∏ P ∈ hfin.toFinset, f P).eval₂ (pullback A).toRingHom (X j) ∈ J.radical := by
      rw [← Ideal.sInf_minimalPrimes, Submodule.mem_sInf]
      intro P hP
      rw [show (∏ P ∈ hfin.toFinset, f P).eval₂ (pullback A).toRingHom (X j) =
          ∏ P ∈ hfin.toFinset, (f P).eval₂ (pullback A).toRingHom (X j) from
        map_prod (Polynomial.eval₂RingHom (pullback A).toRingHom (X j)) _ _]
      obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem
        (fun P => (f P).eval₂ (pullback A).toRingHom (X j)) (hfin.mem_toFinset.mpr hP)
      rw [hc]
      exact Ideal.mul_mem_right c P (hfP P hP)
    obtain ⟨m, hm⟩ := hFrad
    refine ⟨(∏ P ∈ hfin.toFinset, f P) ^ m, hFm.pow m, ?_⟩
    rw [← Polynomial.eval₂_pow, ← Ideal.Quotient.eq_zero_iff_mem, Polynomial.hom_eval₂] at hm
    exact hm
  refine ⟨A, fun a b hab => hA₀.injective ?_, ?_⟩
  · have hfac : ∀ c, projHom P₀ A c = Ideal.Quotient.factor hP₀.1.2 (projHom J A c) :=
      fun c => (Ideal.Quotient.factor_mk hP₀.1.2 _).symm
    rw [hfac, hfac, hab]
  · have hI : (projHom J A).toRingHom.IsIntegral := by
      intro y
      obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective y
      induction p using MvPolynomial.induction_on with
      | C a =>
        have : Ideal.Quotient.mk J (C a) = (projHom J A).toRingHom (C a) := by
          simp [projHom, pullback]
          rfl
        rw [this]
        exact (projHom J A).toRingHom.isIntegralElem_map
      | add p q hp hq => rw [map_add (f := _)]; exact RingHom.IsIntegralElem.add _ hp hq
      | mul_X p i hp => rw [map_mul]; exact RingHom.IsIntegralElem.mul _ hp (hint i)
    refine hI.to_finite ?_
    apply RingHom.FiniteType.of_comp_finiteType (f := algebraMap ℂ (MvPolynomial (Fin d) ℂ))
    rw [show (projHom J A).toRingHom.comp (algebraMap ℂ (MvPolynomial (Fin d) ℂ)) =
      algebraMap ℂ (MvPolynomial (Fin n) ℂ ⧸ J) from (projHom J A).comp_algebraMap]
    exact RingHom.finiteType_algebraMap.mpr inferInstance

end

end GroundTheory.Heights₂.Heights.ComplexSets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Topology ComplexSets

noncomputable section

theorem IsolatedPointsCountPrime.exists_dim_eq {n : ℕ} (J : Ideal (MvPolynomial (Fin n) ℂ)) [J.IsPrime] :
    ∃ d : ℕ, ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = d := by
  have h0 : 0 ≤ ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) := ringKrullDim_nonneg_of_nontrivial
  have h1 := ringKrullDim_quotient_le J
  rw [MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite, ringKrullDim_eq_zero_of_field,
    Nat.card_eq_fintype_card, Fintype.card_fin, zero_add] at h1
  generalize ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = x at h0 h1 ⊢
  induction x using WithBot.recBotCoe with
  | bot => simp at h0
  | coe k =>
    induction k using ENat.recTopCoe with
    | top =>
      exfalso
      have h2 : ((⊤ : ℕ∞) : WithBot ℕ∞) ≤ ((n : ℕ∞) : WithBot ℕ∞) := h1
      exact absurd (WithBot.coe_le_coe.1 h2) (by simp)
    | coe k => exact ⟨k, rfl⟩

theorem IsolatedPointsCountPrime.eval_aeval {n m : ℕ} (Q : Fin m → MvPolynomial (Fin n) ℂ)
    (f : MvPolynomial (Fin m) ℂ) (x : Fin n → ℂ) :
    eval x (aeval Q f) = eval (fun i => eval x (Q i)) f := by
  induction f using MvPolynomial.induction_on with
  | C a => simp
  | add p p' hp hp' => rw [map_add (f := _), map_add (f := _), hp, hp', map_add (f := _)]
  | mul_X p i hp => rw [map_mul, map_mul, hp, aeval_X, map_mul, eval_X]

theorem IsolatedPointsCountPrime.exists_eval_ne_zero {d : ℕ} {Δ : MvPolynomial (Fin d) ℂ} (hΔ : Δ ≠ 0)
    {w : Fin d → ℂ} {S : Set (Fin d → ℂ)} (hS : S ∈ 𝓝 w) : ∃ w' ∈ S, eval w' Δ ≠ 0 := by
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hS
  by_contra h
  simp only [not_exists, not_and, not_not] at h
  apply hΔ
  refine funext_set (fun i => Metric.ball (w i) ε)
    (fun i => infinite_of_mem_nhds (w i) (Metric.ball_mem_nhds (w i) hε)) (fun y hy => ?_)
  rw [map_zero]
  refine h y (hball ?_)
  rw [ball_pi w hε]
  exact hy

theorem IsolatedPointsCountPrime.proof (hOpen : IsolatedFibreOpenPoly.Statement)
    (hDom : DominantFibreBound.Statement) (hDim : ImageDimLe.Statement) :
    IsolatedPointsCountPrime.Statement := by
  classical
  intro n m P hP Q

  have hKp : (RingHom.ker ((Ideal.Quotient.mkₐ ℂ P).comp (aeval Q))).IsPrime := RingHom.ker_isPrime _
  set K := RingHom.ker ((Ideal.Quotient.mkₐ ℂ P).comp (aeval Q)) with hK
  obtain ⟨d, hd⟩ := IsolatedPointsCountPrime.exists_dim_eq P
  obtain ⟨r, hr⟩ := IsolatedPointsCountPrime.exists_dim_eq K
  have hrd : r ≤ d := by
    have h := hDim n m P Q hP
    rw [← hK, hr, hd] at h
    exact_mod_cast h
  obtain ⟨B, hB⟩ := (GenericProjectionFinite.full m r K hKp hr).2.1
  have hfib := FibreBound.full m r K B hKp hr hB

  set Qm : (Fin n → ℂ) → (Fin m → ℂ) := fun x i => eval x (Q i) with hQm
  have hQZ : ∀ x ∈ zeroSet P, Qm x ∈ zeroSet K := by
    intro x hx f hf
    have hf' : aeval Q f ∈ P := by
      rw [hK, RingHom.mem_ker] at hf
      change Ideal.Quotient.mk P (aeval Q f) = 0 at hf
      exact Ideal.Quotient.eq_zero_iff_mem.mp hf
    rw [← IsolatedPointsCountPrime.eval_aeval]
    exact hx _ hf'
  have hQc : Continuous Qm := continuous_pi fun i => MvPolynomial.continuous_eval _

  set q : Fin r → MvPolynomial (Fin n) ℂ := fun i => aeval Q (linPoly B i) with hq
  have hqe : ∀ x, (fun i => eval x (q i)) = B.mulVec (Qm x) := by
    intro x
    funext i

    simp only [hq, IsolatedPointsCountPrime.eval_aeval, linPoly, map_sum, map_mul, eval_C, eval_X,
    Matrix.mulVec, dotProduct, hQm]

  have step1 : ∀ z x, x ∈ isolatedFibrePts P Q z →
      ∃ W ∈ 𝓝 x, ∀ x' ∈ zeroSet P ∩ W, (∀ i, eval x' (q i) = eval x (q i)) → x' = x := by
    rintro z x ⟨hxP, hxQ, V, hV, hiso⟩
    have hQx : Qm x = z := funext hxQ
    have hfin : (_root_.GroundTheory.Heights₂.Heights.ComplexSets.fibre K B (B.mulVec z) \ {z}).Finite :=
      (hfib (B.mulVec z)).2.1.subset Set.sdiff_subset
    have hO : (_root_.GroundTheory.Heights₂.Heights.ComplexSets.fibre K B (B.mulVec z) \ {z})ᶜ ∈ 𝓝 (Qm x) := by
      rw [hQx]
      exact hfin.isClosed.compl_mem_nhds fun h => h.2 rfl
    refine ⟨V ∩ Qm ⁻¹' (_root_.GroundTheory.Heights₂.Heights.ComplexSets.fibre K B (B.mulVec z) \ {z})ᶜ,
      Filter.inter_mem hV (hQc.continuousAt.preimage_mem_nhds hO), ?_⟩
    rintro x' ⟨hx'P, hx'V, hx'O⟩ hx'q
    refine hiso x' ⟨hx'P, hx'V⟩ fun i => congrFun (?_ : Qm x' = z) i
    have h1 : B.mulVec (Qm x') = B.mulVec z := by
      rw [← hqe, ← hQx, ← hqe]
      funext i
      exact hx'q i
    by_contra hne
    exact hx'O ⟨⟨hQZ x' hx'P, h1⟩, hne⟩
  rcases lt_or_eq_of_le hrd with hlt | rfl
  ·
    refine ⟨0, fun z => ?_⟩
    suffices isolatedFibrePts P Q z = ∅ by simp [this]
    refine Set.eq_empty_of_forall_notMem fun x hx => ?_
    obtain ⟨W, hW, hiso⟩ := step1 z x hx
    set p : Fin d → MvPolynomial (Fin n) ℂ := fun i => if h : (i : ℕ) < r then q ⟨i, h⟩ else 0 with hp
    have hiso' : ∃ W ∈ 𝓝 x, ∀ x' ∈ zeroSet P ∩ W, (∀ i, eval x' (p i) = eval x (p i)) → x' = x :=
      ⟨W, hW, fun x' hx' h => hiso x' hx' fun i => by
        simpa [hp, i.isLt] using h ⟨i, i.isLt.trans hlt⟩⟩
    have himg := hOpen n d P p x hP hd hx.1 hiso' Set.univ Filter.univ_mem
    set px : Fin d → ℂ := fun i => eval x (p i) with hpx
    set j : Fin d := ⟨r, hlt⟩
    have hsub : (fun x' : Fin n → ℂ => fun i => eval x' (p i)) '' (zeroSet P ∩ Set.univ) ⊆
        {w | w j = 0} := by
      rintro _ ⟨y, -, rfl⟩
      simp [hp, j]
    have hc : Continuous fun t : ℂ => Function.update px j t := continuous_const.update j continuous_id
    have h1 : (fun t : ℂ => Function.update px j t) ⁻¹' {w | w j = 0} ∈ 𝓝 (px j) := by
      refine hc.continuousAt.preimage_mem_nhds ?_
      rw [Function.update_eq_self]
      exact Filter.mem_of_superset himg hsub
    have h2 : (fun t : ℂ => Function.update px j t) ⁻¹' {w | w j = 0} ⊆ {0} := by
      intro t ht
      simpa using ht
    exact (infinite_of_mem_nhds (px j) (Filter.mem_of_superset h1 h2)) (Set.finite_singleton 0)
  ·
    have hinj : Function.Injective ((Ideal.Quotient.mkₐ ℂ P).comp (aeval q)) := by
      have hcomp : aeval q = (aeval Q).comp (pullback B) := by
        apply MvPolynomial.algHom_ext
        intro i
        simp [hq, pullback]
      intro a b hab
      apply hB.injective
      simp only [projHom, AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq] at hab ⊢
      rw [hcomp, AlgHom.comp_apply, AlgHom.comp_apply, ← map_sub] at hab
      rw [hK, RingHom.mem_ker, AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem]
      exact hab
    obtain ⟨e, Δ, hΔ, hbound⟩ := hDom n r P q hP hd hinj
    refine ⟨e, fun z => ?_⟩
    by_contra hlt
    rw [not_le] at hlt
    obtain ⟨t, hts, htc⟩ := Set.exists_subset_encard_eq (Order.add_one_le_of_lt hlt)
    have htc' : t.encard = ((e + 1 : ℕ) : ℕ∞) := by rw [htc]; push_cast; rfl
    have htf : t.Finite := Set.finite_of_encard_eq_coe htc'
    obtain ⟨U, hUo, hUd⟩ := htf.t2_separation
    have hw : ∀ x ∈ t, (fun x' : Fin n → ℂ => fun i => eval x' (q i)) '' (zeroSet P ∩ U x) ∈
        𝓝 (B.mulVec z) := by
      intro x hx
      have hx' := hts hx
      obtain ⟨W, hW, hiso⟩ := step1 z x hx'
      have h := hOpen n r P q x hP hd hx'.1 ⟨W, hW, hiso⟩ (U x) ((hUo x).2.mem_nhds (hUo x).1)
      have e1 : (fun i => eval x (q i)) = B.mulVec z := by
        rw [hqe]
        congr 1
        exact funext hx'.2.1
      rwa [e1] at h
    have hI := (Filter.biInter_mem htf).2 hw
    obtain ⟨w', hw'I, hΔw'⟩ := IsolatedPointsCountPrime.exists_eval_ne_zero hΔ hI
    have hpick : ∀ x ∈ t, ∃ y, y ∈ zeroSet P ∩ U x ∧ (fun i => eval y (q i)) = w' :=
      fun x hx => Set.mem_iInter₂.1 hw'I x hx
    choose! g hg1 hg2 using hpick
    have hinjg : Set.InjOn g t := by
      intro x hx y hy hxy
      by_contra hne
      refine Set.disjoint_left.1 (hUd hx hy hne) (hg1 x hx).2 ?_
      rw [hxy]
      exact (hg1 y hy).2
    have himg : g '' t ⊆ {x | x ∈ zeroSet P ∧ ∀ i, eval x (q i) = w' i} := by
      rintro _ ⟨x, hx, rfl⟩
      exact ⟨(hg1 x hx).1, fun i => congrFun (hg2 x hx) i⟩
    have hle := (Set.encard_le_encard himg).trans (hbound w' hΔw')
    rw [hinjg.encard_image, htc'] at hle
    have hle' : e + 1 ≤ e := by exact_mod_cast hle
    omega

end

end GroundTheory.Heights₂.Heights
end
