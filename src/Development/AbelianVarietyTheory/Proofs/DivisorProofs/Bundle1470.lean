module

public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
public import Development.AbelianVarietyTheory.Definitions.Foundations.OfInfProjInfMulOfFinProjFin
public import GroundTheory.GlobalFields.Adele.Bundle001
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.QuadraticClassFieldTheory
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle069
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle197
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsEverywhereNormDivOfEtaProdEqOne
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RealMetaplecticRepresentation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1194
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1346
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulRealAdEqZero
public import Formalism.LocalRingCardinality.DataTheta
public import Mathlib.RingTheory.PiTensorProduct
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1373
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.CStarAlgebra.Classes
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle007
import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AutomorphicArithmetic.IntegralCasts.Bundle001
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle266
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle011
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle704
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.QSA GlobalTheory.Published
open Matrix
open scoped Quaternion Topology TensorProduct

noncomputable section

namespace GlobalTheory.PlaceApprox

variable {F : Type} [Field F] [NumberField F]


open Classical in
def locAdele (S₁ : Finset (InfinitePlace F)) (S₂ : Finset (HeightOneSpectrum (𝓞 F)))
    (p : ((v : S₂) → Fv F v.1) × ((w : S₁) → w.1.Completion)) : AF F :=
  ((fun u : InfinitePlace F => if h : u ∈ S₁ then p.2 ⟨u, h⟩ else 0 : InfiniteAdeleRing F),
    ∑ v : S₂, GlobalTheory.AdelicU.singleFin v.1 (p.1 v))

open Classical in
theorem continuous_locAdele (S₁ : Finset (InfinitePlace F)) (S₂ : Finset (HeightOneSpectrum (𝓞 F))) :
    Continuous (locAdele S₁ S₂) := by
  refine Continuous.prodMk ?_ ?_
  · refine continuous_pi fun u => ?_
    by_cases h : u ∈ S₁
    · simp only [h, dite_true]
      exact (continuous_apply _).comp continuous_snd
    · simp only [h, dite_false]
      exact continuous_const
  · exact continuous_finsetSum _ fun v _ =>
      (GlobalTheory.AdelicU.continuous_singleFin v.1).comp ((continuous_apply v).comp continuous_fst)

open Classical in
theorem locAdele_zero (S₁ : Finset (InfinitePlace F)) (S₂ : Finset (HeightOneSpectrum (𝓞 F))) :
    locAdele S₁ S₂ 0 = 0 := by
  refine Prod.ext ?_ ?_
  · funext u
    change (if h : u ∈ S₁ then (0 : u.Completion) else 0) = 0
    split_ifs <;> rfl
  · simp [locAdele]

open Classical in
theorem mul_eq_locAdele {S₁ : Finset (InfinitePlace F)} {S₂ : Finset (HeightOneSpectrum (𝓞 F))} {ε : AF F}
    (hε : IsPlacesIdem S₁ S₂ ε) (a : AF F) :
    ε * a = locAdele S₁ S₂ ((fun v => evalV F v.1 (sndA F a)), (fun w => fstA F a w.1)) := by
  obtain ⟨h1, h2, h3, h4⟩ := hε
  refine Prod.ext ?_ ?_
  · funext u
    change fstA F ε u * fstA F a u = _
    by_cases h : u ∈ S₁
    · simp only [locAdele, h, dite_true, h1 u h, one_mul]
    · simp only [locAdele, h, dite_false, h2 u h, zero_mul]
  · apply GlobalTheory.AdelicU.af_ext
    intro u
    change evalV F u (sndA F ε) * evalV F u (sndA F a) = _

    simp only [locAdele, map_sum]
    by_cases h : u ∈ S₂
    · rw [h3 u h, one_mul, Finset.sum_eq_single ⟨u, h⟩]
      · exact (GlobalTheory.AdelicU.evalV_singleFin_self u _).symm
      · intro b _ hb
        exact GlobalTheory.AdelicU.evalV_singleFin_ne (fun e => hb (Subtype.ext e.symm)) _
      · intro hn; exact absurd (Finset.mem_univ _) hn
    · rw [h4 u h, zero_mul, Finset.sum_eq_zero]
      intro b _
      exact GlobalTheory.AdelicU.evalV_singleFin_ne (fun e => h (by rw [e]; exact b.2)) _

theorem loc_sub_algebraMap (S₁ : Finset (InfinitePlace F)) (S₂ : Finset (HeightOneSpectrum (𝓞 F))) (x : AF F) (t : F) :
    (((fun v : S₂ => evalV F v.1 (sndA F (x - algebraMap F (AF F) t))),
      (fun w : S₁ => fstA F (x - algebraMap F (AF F) t) w.1)) :
        ((v : S₂) → Fv F v.1) × ((w : S₁) → w.1.Completion)) =
      ((fun v : S₂ => evalV F v.1 (sndA F x)), (fun w : S₁ => fstA F x w.1)) -
        ((fun v : S₂ => algebraMap F (v.1.adicCompletion F) t), (fun w : S₁ => algebraMap F w.1.Completion t)) := by
  refine Prod.ext (funext fun v => ?_) (funext fun w => ?_)
  · simp only [map_sub, AlgHom.commutes, Prod.fst_sub, Pi.sub_apply]
  · simp only [map_sub, AlgHom.commutes, Prod.snd_sub, Pi.sub_apply]
    rfl

theorem weak_approx_idem : ∀ (F : Type) [Field F] [NumberField F], ∀ (S₁ : Finset (InfinitePlace F))
    (S₂ : Finset (HeightOneSpectrum (𝓞 F))) (ε : AF F), IsPlacesIdem S₁ S₂ ε →
    ∀ (x : AF F) (U : Set (AF F)), U ∈ 𝓝 (0 : AF F) → ∃ t : F, ε * (x - algebraMap F (AF F) t) ∈ U := by
  intro F _ _ S₁ S₂ ε hε x U hU
  set c : ((v : S₂) → Fv F v.1) × ((w : S₁) → w.1.Completion) :=
    ((fun v : S₂ => evalV F v.1 (sndA F x)), (fun w : S₁ => fstA F x w.1)) with hc
  have hO : {p | locAdele S₁ S₂ (c - p) ∈ U} ∈ 𝓝 c := by
    have hcont : Continuous fun p => locAdele S₁ S₂ (c - p) :=
      (continuous_locAdele S₁ S₂).comp (continuous_const.sub continuous_id)
    have h0 : locAdele S₁ S₂ (c - c) = 0 := by
      rw [sub_self, locAdele_zero]
    exact hcont.continuousAt.preimage_mem_nhds (by rw [h0]; exact hU)
  have hd := GroundTheory.Global.denseRange_algebraMap_prod_pi (K := F) S₂ S₁
  obtain ⟨_, hy, t, rfl⟩ := mem_closure_iff_nhds.1 (hd c) _ hO
  refine ⟨t, ?_⟩
  rw [mul_eq_locAdele hε, loc_sub_algebraMap]
  exact hy

end GlobalTheory.PlaceApprox
end
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.QuadSymbol.SignCount

theorem card_prod_eq_mul_two {ι : Type} [Fintype ι] [Nonempty ι] (c : ℤˣ) :
    Nat.card {s : ι → ℤˣ // c * ∏ i, s i = 1} * 2 = 2 ^ Fintype.card ι := by
  classical
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  let m : ι → ℤˣ := Pi.mulSingle i₀ (-1)
  have hm : ∏ i, m i = -1 := by simp [m, Finset.prod_pi_mulSingle']
  have hmm : m * m = 1 := by
    ext i
    by_cases h : i = i₀
    · subst h; simp [m]
    · simp [m, Pi.mulSingle_eq_of_ne h]
  have key : ∀ s : ι → ℤˣ, (c * ∏ i, (s * m) i = 1) ↔ ¬ (c * ∏ i, s i = 1) := by
    intro s
    simp only [Pi.mul_apply, Finset.prod_mul_distrib, hm]
    rcases Int.units_eq_one_or (c * ∏ i, s i) with h | h
    · rw [← mul_assoc, h]; decide
    · rw [← mul_assoc, h]; decide
  let e : {s : ι → ℤˣ // c * ∏ i, s i = 1} ≃ {s : ι → ℤˣ // ¬ (c * ∏ i, s i = 1)} :=
    { toFun := fun s => ⟨s.1 * m, fun h => (key s.1).1 h s.2⟩
      invFun := fun s => ⟨s.1 * m, by
        have := (key s.1).2 s.2
        exact this⟩
      left_inv := fun s => Subtype.ext (by simp [mul_assoc, hmm])
      right_inv := fun s => Subtype.ext (by simp [mul_assoc, hmm]) }
  have htot := Fintype.card_subtype_compl (fun s : ι → ℤˣ => c * ∏ i, s i = 1)
  rw [Nat.card_eq_fintype_card, mul_two]
  nth_rewrite 2 [Fintype.card_congr e]
  have hle := Fintype.card_subtype_le (fun s : ι → ℤˣ => c * ∏ i, s i = 1)
  rw [htot, Fintype.card_pi, Finset.prod_const, Fintype.card_units_int, Finset.card_univ] at *
  omega

end GlobalTheory.QuadSymbol.SignCount

namespace GlobalTheory.QuadSymbol.SignCount

theorem neg_one_not_mem_normGroup {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [Algebra.IsQuadraticExtension K L] (hL : NumberField.IsTotallyComplex L)
    {w : InfinitePlace K} (hw : w.IsReal) : (-1 : (w.Completion)ˣ) ∉ normGroup K L w.Completion := by
  obtain ⟨δ, b, -, h0, h1⟩ := AlmostNorm.exists_basis_sq K L
  have hneg : InfinitePlace.embedding_of_isReal hw δ < 0 := by
    by_contra hc
    obtain ⟨r, hr⟩ := Real.isSquare_iff.2 (not_lt.1 hc)
    let τ : L →+* ℂ := ComplexEmbedding.lift L w.embedding
    have hτ : ∀ x : K, τ (algebraMap K L x) = InfinitePlace.embedding_of_isReal hw x := fun x => by
      rw [InfinitePlace.embedding_of_isReal_apply]
      exact ComplexEmbedding.lift_algebraMap_apply L w.embedding x
    have h2 : τ (b 1) * τ (b 1) = (r : ℂ) * r := by rw [← map_mul, h1, hτ, hr]; push_cast; rfl
    have h3 : starRingEnd ℂ (τ (b 1)) = τ (b 1) := by
      rcases mul_self_eq_mul_self_iff.1 h2 with h | h <;> rw [h] <;> simp
    refine InfinitePlace.not_isReal_iff_isComplex.2 (hL.isComplex (InfinitePlace.mk τ))
      (InfinitePlace.isReal_mk_iff.2 (ComplexEmbedding.isReal_iff.2 (RingHom.ext fun x => ?_)))
    change starRingEnd ℂ (τ x) = τ x
    rw [← b.sum_repr x, Fin.sum_univ_two, h0, Algebra.smul_def, Algebra.smul_def]
    simp only [map_add (f := _), map_mul, map_one, hτ, h3, Complex.conj_ofReal]
  rw [mem_normGroup_iff_form b h0 h1]
  rintro ⟨x, y, hxy⟩
  let f := InfinitePlace.Completion.ringEquivRealOfIsReal hw
  have hf : f (algebraMap K w.Completion δ) = InfinitePlace.embedding_of_isReal hw δ := by
    rw [InfinitePlace.Completion.algebraMap_apply]
    simpa [f, InfinitePlace.Completion.instCoe] using
      InfinitePlace.Completion.extensionEmbeddingOfIsReal_coe hw ((WithAbs.equiv _).symm δ)
  have := congrArg f hxy
  simp only [Units.val_neg, Units.val_one, map_neg, map_one, map_sub, map_mul, map_pow, hf] at this
  nlinarith [sq_nonneg (f x), sq_nonneg (f y)]

end GlobalTheory.QuadSymbol.SignCount

namespace GlobalTheory.QuadSymbol.SignCount

def infSigns (K L : Type) [Field K] [NumberField K] [Field L] [Algebra K L] (t : Kˣ) :
    InfinitePlace K → ℤˣ :=
  fun w => eta K L w.Completion (infDiag K t w)

theorem infSigns_eq_of_mem {K L : Type} [Field K] [NumberField K] [Field L] [Algebra K L]
    [FiniteDimensional K L] {t t' : Kˣ} (h : t⁻¹ * t' ∈ globalNorms K L) :
    infSigns K L t' = infSigns K L t := by
  funext w
  refine eta_eq_of_div_mem ?_
  have := toUnits_mem_normGroup (K := K) (L := L) w.Completion h
  rw [← div_eq_inv_mul, _root_.map_div] at this
  exact this

theorem infSigns_out {K L : Type} [Field K] [NumberField K] [Field L] [Algebra K L]
    [FiniteDimensional K L] (t : Kˣ) :
    infSigns K L (Quotient.out (QuotientGroup.mk t : Kˣ ⧸ globalNorms K L)) = infSigns K L t :=
  infSigns_eq_of_mem (QuotientGroup.eq.1 (QuotientGroup.out_eq' _).symm)

theorem card_classes_mul_two : ∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [Algebra.IsQuadraticExtension K L], NumberField.IsTotallyReal K → NumberField.IsTotallyComplex L → ∀ x : GlobalTheory.QuadSymbol.FinFam K, GlobalTheory.QuadSymbol.AlmostNorm K L x → Nat.card {q : Kˣ ⧸ GlobalTheory.QuadSymbol.globalNorms K L // ∃ t : Kˣ, q = QuotientGroup.mk t ∧ ∀ u, x u / GlobalTheory.QuadSymbol.finDiag K t u ∈ GlobalTheory.QuadSymbol.normGroup K L (u.adicCompletion K)} * 2 = 2 ^ Fintype.card (InfinitePlace K) := by
  intro K L _ _ _ _ _ _ hK hL x hx
  have hfd : FiniteDimensional K L := Module.finite_of_finrank_eq_succ (Algebra.IsQuadraticExtension.finrank_eq_two K L)
  obtain ⟨-, hnorm, hseq, -⟩ := exactSequence K L
  obtain ⟨-, hc2⟩ := localCharacters K L
  set c : ℤˣ := ∏ᶠ v : HeightOneSpectrum (𝓞 K), eta K L (v.adicCompletion K) (x v) with hc
  rw [← card_prod_eq_mul_two c]
  congr 1
  have hprod : ∀ t : Kˣ, (∀ u, x u / finDiag K t u ∈ normGroup K L (u.adicCompletion K)) →
      c * ∏ w, infSigns K L t w = 1 := by
    intro t ht
    have := (hseq x (infDiag K t) hx).1 ⟨t, fun u => ht u, fun w => by simp [one_mem]⟩
    exact this
  refine Nat.card_congr (Equiv.ofBijective (fun q => ⟨infSigns K L (Quotient.out q.1), ?_⟩) ⟨?_, ?_⟩)
  · obtain ⟨t, hq, ht⟩ := q.2
    rw [hq, infSigns_out]
    exact hprod t ht
  · rintro ⟨q₁, t₁, rfl, h₁⟩ ⟨q₂, t₂, rfl, h₂⟩ he
    have he' : infSigns K L t₁ = infSigns K L t₂ := by
      have := congrArg Subtype.val he
      simpa only [infSigns_out] using this
    refine Subtype.ext (QuotientGroup.eq.2 ((hnorm (t₁⁻¹ * t₂)).1 ⟨fun u => ?_, fun w => ?_⟩))
    · have hm := div_mem (h₁ u) (h₂ u)
      rwa [div_div_div_cancel_left, finDiag, finDiag, ← _root_.map_div, div_eq_inv_mul] at hm
    · have hm := Converse.div_mem_normGroup (hc2 w) (congrFun he' w)
      rwa [infDiag, infDiag, ← _root_.map_div, div_eq_inv_mul] at hm
  · rintro ⟨s, hs⟩
    let y : InfFam K := fun w => if s w = 1 then 1 else -1
    have hy : ∀ w, eta K L w.Completion (y w) = s w := by
      intro w
      rcases Int.units_eq_one_or (s w) with h | h
      · simp only [y, h, if_true]
        exact eta_eq_one_iff.2 (one_mem _)
      · simp only [y, h, show (-1 : ℤˣ) ≠ 1 by decide, if_false]
        exact eta_eq_neg_one_iff.2 (neg_one_not_mem_normGroup hL (hK.isReal w))
    have hy1 : etaProd K L x y = 1 := by
      unfold etaProd
      rw [Finset.prod_congr rfl fun w _ => hy w]
      exact hs
    obtain ⟨t, ht1, ht2⟩ := (hseq x y hx).2 hy1
    refine ⟨⟨QuotientGroup.mk t, t, rfl, fun u => ht1 u⟩, Subtype.ext ?_⟩
    simp only [infSigns_out]
    funext w
    rw [← hy w]
    exact (eta_eq_of_div_mem (ht2 w)).symm

end GlobalTheory.QuadSymbol.SignCount
end
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.WeilTr MeasureTheory
open scoped Matrix ENNReal

noncomputable section

namespace GlobalTheory.ArchUniq.FormTransport

open GlobalTheory.RealWeil GlobalTheory.ArchUniq
open scoped SchwartzMap ComplexConjugate

theorem rhoFun_mul_conj {n : ℕ} (w : Fin n ⊕ Fin n → ℝ) (G G' : EuclideanSpace ℝ (Fin n) → ℂ)
    (x : EuclideanSpace ℝ (Fin n)) :
    rhoFun w G x * conj (rhoFun w G' x) = G (x + pPart w) * conj (G' (x + pPart w)) := by
  have h : phase w x * conj (phase w x) = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_phase]; simp
  simp only [rhoFun, map_mul]
  calc _ = (phase w x * conj (phase w x)) * (G (x + pPart w) * conj (G' (x + pPart w))) := by ring
    _ = _ := by rw [h, one_mul]

theorem integral_rhoFun_mul_conj {n : ℕ} (w : Fin n ⊕ Fin n → ℝ) (G G' : EuclideanSpace ℝ (Fin n) → ℂ) :
    ∫ x, rhoFun w G x * conj (rhoFun w G' x) = ∫ x, G x * conj (G' x) := by
  simp_rw [rhoFun_mul_conj]
  exact integral_add_right_eq_self (fun x => G x * conj (G' x)) (pPart w)


open scoped Classical in
theorem schr_eq_schrF {F : Type} [Field F] [NumberField F] [Invertible (2 : mixedEmbedding.mixedSpace F)]
    {κ : Type} [Fintype κ] (ψ : AddChar (mixedEmbedding.mixedSpace F) ℂ)
    (hψ : ∀ a, ψ a = Complex.exp (-(2 * Real.pi * Complex.I) *
      (Algebra.trace ℝ (mixedEmbedding.mixedSpace F) a : ℝ)))
    (w : (κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F))
    (u : (κ → mixedEmbedding.mixedSpace F) → ℂ) :
    schr ψ w u = schrF (trP F κ) w u := by
  funext x
  have h2 : (⅟(2 : mixedEmbedding.mixedSpace F)) = algebraMap ℝ (mixedEmbedding.mixedSpace F) (1 / 2) := by
    refine invOf_eq_right_inv ?_
    rw [← map_ofNat (algebraMap ℝ (mixedEmbedding.mixedSpace F)) 2, ← map_mul]
    norm_num
  have ht : Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (x ⬝ᵥ w.2 + ⅟(2 : mixedEmbedding.mixedSpace F) * (w.1 ⬝ᵥ w.2)) =
      trP F κ x w.2 + trP F κ w.1 w.2 / 2 := by
    rw [map_add (f := _), h2, ← Algebra.smul_def, map_smul, smul_eq_mul]
    simp only [trP, dotProduct]
    ring
  simp only [schr, schrF, hψ, ht]

theorem haar_coords_cplx {n : ℕ} {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [MeasurableSpace V]
    [BorelSpace V] [FiniteDimensional ℝ V] (μ : Measure V) [μ.IsAddHaarMeasure]
    (C : V ≃L[ℝ] EuclideanSpace ℝ (Fin n)) :
    ∃ k : ℝ, ∀ G : V → ℂ, ∫ y, G y ∂μ = (k : ℂ) * ∫ x, G (C.symm x) := by
  let e : V ≃ᵐ EuclideanSpace ℝ (Fin n) := C.toHomeomorph.toMeasurableEquiv
  have he : ∀ y, e y = C y := fun y => rfl
  haveI : (μ.map e).IsAddHaarMeasure := C.isAddHaarMeasure_map μ
  have hk := Measure.isAddLeftInvariant_eq_smul (μ.map e) (volume : Measure (EuclideanSpace ℝ (Fin n)))
  refine ⟨(Measure.addHaarScalarFactor (μ.map e) volume : ℝ), fun G => ?_⟩
  have h1 : ∫ y, G y ∂μ = ∫ x, G (C.symm x) ∂(μ.map e) := by
    rw [integral_map_equiv]
    simp [he]
  rw [h1, congrArg (fun m => ∫ x, G (C.symm x) ∂m) hk]
  simp only [integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul]


open scoped Classical in
theorem const_of_euclidean : (∀ (n : ℕ) (B : GlobalTheory.RealWeil.Sch (Fin n) → GlobalTheory.RealWeil.Sch (Fin n) → ℂ),
    (∀ h', ∃ L : GlobalTheory.RealWeil.Sch (Fin n) →L[ℂ] ℂ, ∀ h, B h h' = L h) →
    (∀ h h', B h' h = starRingEnd ℂ (B h h')) → (∀ h, 0 ≤ (B h h).re) →
    (∀ (w : Fin n ⊕ Fin n → ℝ) (h h' g g' : GlobalTheory.RealWeil.Sch (Fin n)), ⇑g = GlobalTheory.RealWeil.rhoFun w ⇑h →
      ⇑g' = GlobalTheory.RealWeil.rhoFun w ⇑h' → B g g' = B h h') →
    ∃ c : ℝ, 0 ≤ c ∧ ∀ h h', B h h' = c * ∫ x, h x * starRingEnd ℂ (h' x)) → ∀ (F : Type) [Field F] [NumberField F] [Invertible (2 : mixedEmbedding.mixedSpace F)] (κ : Type) [Fintype κ]
    (ψ : AddChar (mixedEmbedding.mixedSpace F) ℂ),
    (∀ a, ψ a = Complex.exp (-(2 * Real.pi * Complex.I) * (Algebra.trace ℝ (mixedEmbedding.mixedSpace F) a : ℝ))) →
    ∀ (T : SInf F κ →L[ℂ] SInf F κ)
      (A : (κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F) →
        (κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)),
      (∀ w (f g : SInf F κ), (g : (κ → mixedEmbedding.mixedSpace F) → ℂ) = schr ψ w f →
        (T g : (κ → mixedEmbedding.mixedSpace F) → ℂ) = schr ψ (A w) (T f)) →
      ∃ c : ℝ, 0 ≤ c ∧ ∀ μ : @Measure (κ → mixedEmbedding.mixedSpace F) (borel _),
        @Measure.IsAddHaarMeasure _ _ _ (borel _) μ → ∀ f f' : SInf F κ,
          @integral _ ℂ _ _ (borel _) μ (fun x => T f x * starRingEnd ℂ (T f' x)) =
            (c : ℂ) * @integral _ ℂ _ _ (borel _) μ (fun x => f x * starRingEnd ℂ (f' x)) := by
  intro H F _ _ _ κ _ ψ hψ T A hT
  letI : MeasurableSpace (κ → mixedEmbedding.mixedSpace F) := borel _
  haveI : BorelSpace (κ → mixedEmbedding.mixedSpace F) := ⟨rfl⟩
  have hP : IsPairing (trP F κ) := Coord.isPairing_trP κ
  obtain ⟨C, φ, -, hS⟩ := exists_pairing_coords (κ → mixedEmbedding.mixedSpace F) (trP F κ) hP _ rfl
  generalize Module.finrank ℝ (κ → mixedEmbedding.mixedSpace F) = n at C φ hS
  let toE : SInf F κ →L[ℂ] Sch (Fin n) := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (F := ℂ) C.symm
  let toV : Sch (Fin n) →L[ℂ] SInf F κ := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (F := ℂ) C
  have htoE : ∀ g, ⇑(toE g) = ⇑g ∘ ⇑C.symm := fun g => rfl
  have htoV : ∀ h, ⇑(toV h) = ⇑h ∘ ⇑C := fun h => rfl
  have hVE : ∀ g, toV (toE g) = g := fun g => by ext x; simp [htoE, htoV]
  let T' : Sch (Fin n) →L[ℂ] Sch (Fin n) := toE.comp (T.comp toV)
  have hT' : ∀ h, T' h = toE (T (toV h)) := fun h => rfl
  have hI : ∀ w (h g : Sch (Fin n)), ⇑g = rhoFun w ⇑h → ⇑(T' g) = rhoFun (φ (A (φ.symm w))) ⇑(T' h) := by
    intro w h g hg
    have e1 : ⇑(toV g) = schr ψ (φ.symm w) ⇑(toV h) := by
      rw [schr_eq_schrF ψ hψ]
      funext x
      have := congrFun (hS (φ.symm w) ⇑h) x
      simp only [Function.comp_apply, LinearEquiv.apply_symm_apply] at this
      simp only [htoV, Function.comp_apply, hg]
      exact this.symm
    have e2 := hT _ _ _ e1
    rw [schr_eq_schrF ψ hψ] at e2
    rw [hT', hT', htoE, htoE, e2]
    obtain ⟨G, hG⟩ : ∃ G : EuclideanSpace ℝ (Fin n) → ℂ, ⇑(T (toV h)) = G ∘ ⇑C :=
      ⟨⇑(T (toV h)) ∘ ⇑C.symm, by ext x; simp⟩
    have hGC : (G ∘ ⇑C) ∘ ⇑C.symm = G := by funext x; simp
    rw [hG, hS, hGC]
    funext x
    simp
  let B : Sch (Fin n) → Sch (Fin n) → ℂ := fun h h' => ∫ x, T' h x * conj (T' h' x)
  have hcont : ∀ h', ∃ L : Sch (Fin n) →L[ℂ] ℂ, ∀ h, B h h' = L h := by
    intro h'
    refine ⟨(innerSL ℂ ((T' h').toLp 2)).comp
      ((SchwartzMap.toLpCLM ℂ ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))).comp T'), fun h => ?_⟩
    simp only [ContinuousLinearMap.comp_apply, innerSL_apply_apply, SchwartzMap.toLpCLM_apply]
    rw [SchwartzMap.inner_toL2_toL2_eq (T' h') (T' h) volume]
    simp only [B, RCLike.inner_apply]
  have hherm : ∀ h h', B h' h = conj (B h h') := by
    intro h h'
    simp only [B]
    rw [← integral_conj]
    congr 1
    funext x
    simp [mul_comm]
  have hpos : ∀ h, 0 ≤ (B h h).re := by
    intro h
    have e : B h h = ((∫ x, Complex.normSq (T' h x) : ℝ) : ℂ) := by
      have e0 : B h h = ∫ x, ((Complex.normSq (T' h x) : ℝ) : ℂ) := by simp only [B, Complex.mul_conj]
      rw [e0]
      first
        | exact integral_complex_ofReal
        | exact integral_ofReal
    rw [e, Complex.ofReal_re]
    exact integral_nonneg fun x => Complex.normSq_nonneg _
  have hinv : ∀ (w : Fin n ⊕ Fin n → ℝ) (h h' g g' : Sch (Fin n)), ⇑g = rhoFun w ⇑h →
      ⇑g' = rhoFun w ⇑h' → B g g' = B h h' := by
    intro w h h' g g' hg hg'
    simp only [B]
    rw [hI w h g hg, hI w h' g' hg']
    exact integral_rhoFun_mul_conj _ _ _
  obtain ⟨c, hc0, hc⟩ := H n B hcont hherm hpos hinv
  have hB : ∀ f f' : SInf F κ, ∫ x, T f (C.symm x) * conj (T f' (C.symm x)) =
      (c : ℂ) * ∫ x, f (C.symm x) * conj (f' (C.symm x)) := by
    intro f f'
    have := hc (toE f) (toE f')
    simpa only [B, hT', hVE, htoE, Function.comp_apply] using this
  refine ⟨c, hc0, fun μ hμ f f' => ?_⟩
  haveI := hμ
  obtain ⟨k, hk⟩ := haar_coords_cplx μ C
  rw [hk, hk, hB]
  ring

end GlobalTheory.ArchUniq.FormTransport

end
end

section

open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix Classical
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift GlobalTheory.RealLift.Dbl


theorem _root_.GlobalTheory.T.tprod_constant_polynomials_ne_zero : ∀ (F : Type) [Field F] [NumberField F] (P Q R S : ℕ),
    (PiTensorProduct.tprod ℂ fun _ : InfinitePlace F => (1 : Formalism.BasicNotions.TH.Pol P Q R S)) ≠ 0 := by
  first | exact @GlobalTheory.tprod_one_pol_ne_zero | exact GlobalTheory.tprod_one_pol_ne_zero | (intros; apply GlobalTheory.tprod_one_pol_ne_zero <;> assumption)
end
