module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1784
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1752
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsNormalisedThetaSub
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.QuadraticClassFieldTheory
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle018
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EvenCardOfNotLone
public import Development.AbelianVarietyTheory.Definitions.Foundations.CdScaleTieIff
public import Development.AbelianVarietyTheory.Definitions.Foundations.ClassMassEqSumOfBijective
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCompactAdele
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsBoundedUnitary
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteClassSetHermitianUnitaryOpenLevel
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsCompactLatticeStabilizerBoundedReal
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle018
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Univ
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
public import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1778
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle040
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyNormFinLeOne
import Development.AbelianVarietyTheory.Definitions.Foundations.IsIwasawaOfIsCompact
import Development.AbelianVarietyTheory.Definitions.Foundations.NormEulerPolySubOneLe

@[expose] public section

section

noncomputable section

open NumberField IsDedekindDomain Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC
open scoped Classical TensorProduct
open GlobalTheory.BCT

namespace GlobalTheory.LocBound

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem continuous_cj (w : Pl E) : Continuous (cj w) := by
  by_cases h : ∃ s : w.adicCompletion E →+* w.adicCompletion E, Continuous s ∧
      ∀ x : E, s (algebraMap E _ x) = algebraMap E _ (IsCMField.complexConj E x)
  · exact (GlobalTheory.ConjAtPlace.cj_spec w h).1
  · rw [GlobalTheory.ConjAtPlace.cj_of_not w h]; exact continuous_id

theorem continuous_nrmL (n : ℕ) (w : Pl E) : Continuous (nrmL n w) := by
  by_cases hs : IsSplitAt w
  · have e : nrmL n w = fun y => y := funext fun y => by simp [nrmL, hs]
    rw [e]; exact continuous_id
  · have e : nrmL n w = fun y => y * thetaGL n (cj w) y := funext fun y => by simp [nrmL, hs]
    rw [e]
    exact continuous_id.mul (GlobalTheory.ThetaPull.continuous_thetaGL (cj w) (continuous_cj w))

theorem continuous_coeff_charpoly {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] (n i : ℕ) :
    Continuous fun M : Matrix (Fin n) (Fin n) K => M.charpoly.coeff i := by
  have h : (fun M : Matrix (Fin n) (Fin n) K => M.charpoly.coeff i) =
      fun M => MvPolynomial.eval (fun ij : Fin n × Fin n => M ij.1 ij.2)
        ((Matrix.charpoly.univ K (Fin n)).coeff i) := by
    funext M
    exact (Matrix.charpoly.univ_coeff_eval₂Hom (Fin n) (RingHom.id K) (fun ij : Fin n × Fin n => M ij.1 ij.2) i).symm
  rw [h]
  exact (MvPolynomial.continuous_eval _).comp
    (continuous_pi fun ij => (continuous_apply ij.2).comp (continuous_apply ij.1))

theorem exists_bound_of_isCompact (w : Pl E) {K : Set (w.adicCompletion E)} (hK : IsCompact K) :
    ∃ m : ℕ, ∀ x ∈ K, Valued.v x ≤ WithZero.exp (m : ℤ) := by
  let U : ℕ → Set (w.adicCompletion E) := fun m => {y | Valued.v y ≤ WithZero.exp (m : ℤ)}
  have hcov : K ⊆ ⋃ m : ℕ, U m := by
    intro x _
    rcases eq_or_ne (Valued.v x) 0 with h0 | h0
    · exact Set.mem_iUnion.2 ⟨0, by simp only [U, Set.mem_setOf_eq, h0]; exact zero_le'⟩
    · refine Set.mem_iUnion.2 ⟨(WithZero.log (Valued.v x)).toNat, ?_⟩
      show Valued.v x ≤ _
      conv_lhs => rw [← WithZero.exp_log h0]
      rw [WithZero.exp_le_exp]
      omega
  have hdir : Directed (· ⊆ ·) U :=
    Monotone.directed_le fun a b hab y hy => le_trans hy (WithZero.exp_le_exp.2 (by exact_mod_cast hab))
  obtain ⟨m, hm⟩ := hK.elim_directed_cover U (fun m => GlobalTheory.PrincCong.isOpen_ball w (m : ℤ)) hcov hdir
  exact ⟨m, fun x hx => hm hx⟩

theorem bound_charpoly_nrmL : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : Pl E)
    (C : Set (GLw n w)), IsCompact C →
    ∃ γ : WithZero (Multiplicative ℤ), γ ≠ 0 ∧ ∀ y ∈ C,
      (∀ i, Valued.v ((nrmL n w y).val.charpoly.coeff i) ≤ γ) ∧
        γ⁻¹ ≤ Valued.v ((nrmL n w y).val.charpoly.coeff 0) := by
  intro E _ _ _ n w C hC
  let F : Option (Fin (n + 1)) → GLw n w → w.adicCompletion E := fun o y =>
    match o with
    | none => ((nrmL n w y)⁻¹).val.det
    | some i => (nrmL n w y).val.charpoly.coeff i
  have hF : ∀ o, Continuous (F o) := by
    rintro (_ | i)
    · exact (Units.continuous_val.comp (continuous_nrmL n w).inv).matrix_det
    · exact (continuous_coeff_charpoly n i).comp (Units.continuous_val.comp (continuous_nrmL n w))
  have hK : IsCompact (⋃ o, F o '' C) := isCompact_iUnion fun o => hC.image (hF o)
  obtain ⟨m, hm⟩ := exists_bound_of_isCompact w hK
  have hb : ∀ o, ∀ y ∈ C, Valued.v (F o y) ≤ WithZero.exp (m : ℤ) := fun o y hy =>
    hm _ (Set.mem_iUnion.2 ⟨o, Set.mem_image_of_mem _ hy⟩)
  refine ⟨WithZero.exp (m : ℤ), WithZero.exp_ne_zero, fun y hy => ⟨fun i => ?_, ?_⟩⟩
  · by_cases hi : i ≤ n
    · exact hb (some ⟨i, Nat.lt_succ_of_le hi⟩) y hy
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]; omega)]
      simp
  · have h1 : Valued.v (((nrmL n w y)⁻¹).val.det) ≤ WithZero.exp (m : ℤ) := hb none y hy
    have hdet : (nrmL n w y).val.det * ((nrmL n w y)⁻¹).val.det = 1 := by
      rw [← Matrix.det_mul, Units.mul_inv, Matrix.det_one]
    have hc0 : (nrmL n w y).val.charpoly.coeff 0 = (-1) ^ n * (nrmL n w y).val.det := by
      rw [Matrix.det_eq_sign_charpoly_coeff, Fintype.card_fin, ← mul_assoc, ← pow_add, Even.neg_one_pow ⟨n, rfl⟩,
        one_mul]
    have hv : Valued.v ((nrmL n w y).val.charpoly.coeff 0) * Valued.v (((nrmL n w y)⁻¹).val.det) = 1 := by
      rw [hc0, map_mul, map_pow, Valuation.map_neg, map_one, one_pow, one_mul, ← map_mul, hdet, map_one]
    have hne : Valued.v (((nrmL n w y)⁻¹).val.det) ≠ 0 := fun h => by
      rw [h, mul_zero] at hv; exact zero_ne_one hv
    rw [eq_inv_of_mul_eq_one_left hv]
    exact inv_anti₀ (zero_lt_iff.2 hne) h1

end GlobalTheory.LocBound
end
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.UnitaryClasses
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.TotPosSign

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem embReal_algebraMap {w : InfinitePlace F} (hw : w.IsReal) (t : F) :
    InfinitePlace.Completion.extensionEmbeddingOfIsReal hw (algebraMap F w.Completion t) =
      InfinitePlace.embedding_of_isReal hw t := by
  have := InfinitePlace.Completion.extensionEmbeddingOfIsReal_coe hw ((WithAbs.equiv w.1).symm t)
  rw [AbsoluteValue.Completion.algebraMap_def, WithAbs.algebraMap_right_apply,
    Algebra.algebraMap_self_apply]
  rw [← WithAbs.equiv_symm_apply]
  simpa only [RingEquiv.apply_symm_apply] using this

theorem eta_inf_eq_one [Algebra.IsQuadraticExtension F E] {w : InfinitePlace F} (hw : w.IsReal) (t : Fˣ)
    (ht : 0 < InfinitePlace.embedding_of_isReal hw (t : F)) :
    GlobalTheory.QuadSymbol.eta F E w.Completion (GlobalTheory.QuadSymbol.infDiag F t w) = 1 := by
  rw [GlobalTheory.QuadSymbol.eta_eq_one_iff, GlobalTheory.QuadSymbol.mem_normGroup_iff]
  set g := InfinitePlace.Completion.ringEquivRealOfIsReal hw
  set a : w.Completion := algebraMap F w.Completion (t : F)
  have hga : g a = InfinitePlace.embedding_of_isReal hw (t : F) := by
    rw [InfinitePlace.Completion.ringEquivRealOfIsReal_apply, embReal_algebraMap]
  refine ⟨algebraMap w.Completion (w.Completion ⊗[F] E) (g.symm (Real.sqrt (g a))), ?_⟩
  rw [Algebra.norm_algebraMap, Module.finrank_baseChange, Algebra.IsQuadraticExtension.finrank_eq_two F E,
    ← map_pow, Real.sq_sqrt (hga ▸ ht.le), RingEquiv.symm_apply_apply]
  rfl

end GlobalTheory.TotPosSign

namespace GlobalTheory.TotPosSign

section Loc
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem ordL_congr {L L' : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] [Field L']
    [Valued L' (WithZero (Multiplicative ℤ))] {x : L} {y : L'} (h : Valued.v x = Valued.v y) : ordL x = ordL y := by
  change (fun z : WithZero (Multiplicative ℤ) =>
      if h : z = 0 then (0 : ℤ) else -Multiplicative.toAdd (WithZero.unzero h)) (Valued.v x) =
    (fun z : WithZero (Multiplicative ℤ) =>
      if h : z = 0 then (0 : ℤ) else -Multiplicative.toAdd (WithZero.unzero h)) (Valued.v y)
  rw [h]

theorem valued_eq_exp {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {x : L} (hx : x ≠ 0) :
    Valued.v x = WithZero.exp (-ordL x) := by
  have h0 : Valued.v x ≠ 0 := (Valuation.ne_zero_iff _).2 hx
  unfold ordL
  rw [dite_eq_right h0, neg_neg]
  conv_lhs => rw [← WithZero.coe_unzero h0]
  rfl

theorem eta_inert [Algebra.IsQuadraticExtension F E] {v : HeightOneSpectrum (𝓞 F)}
    (hv : ¬ Formalism.MainNotions.SchurIrreducible.IsSplit (E := E) v) (hu : Formalism.MainNotions.SchurIrreducible.IsUnram (E := E) v) (x : (v.adicCompletion F)ˣ) :
    GlobalTheory.QuadSymbol.eta F E (v.adicCompletion F) x = (-1) ^ ordL (x : v.adicCompletion F) := by
  have h2 : Module.finrank F E = 2 := Algebra.IsQuadraticExtension.finrank_eq_two F E
  let χ : (v.adicCompletion F)ˣ →* ℤˣ :=
    MonoidHom.mk' (GlobalTheory.QuadSymbol.eta F E (v.adicCompletion F)) ((GlobalTheory.QuadSymbol.localCharacters F E).1 v)
  set π := atFin v (unif v)
  set k := ordL (x : v.adicCompletion F)
  have hπ : Valued.v (π : v.adicCompletion F) = WithZero.exp (-1 : ℤ) := unif_spec v
  set u := x * π ^ (-k)
  have hu1 : IsUnitAt v u := by
    unfold IsUnitAt
    rw [Units.val_mul, Units.val_zpow_eq_zpow_val, map_mul, map_zpow₀, hπ, valued_eq_exp x.ne_zero,
      ← WithZero.exp_zsmul, ← WithZero.exp_add]
    simp [k]
  have hx : x = u * π ^ k := by simp [u]
  have e1 : χ u = 1 := GlobalTheory.QuadSymbol.eta_eq_one_iff.2 (GlobalTheory.LFun.mem_normGroup_of_isUnram h2 hu hu1)
  have e2 : χ π = -1 := GlobalTheory.QuadSymbol.eta_eq_neg_one_iff.2
    (GlobalTheory.LFun.not_mem_normGroup_of_inert h2 hv hu (unif_spec v))
  change χ x = _
  rw [hx, map_mul, map_zpow, e1, e2, one_mul]

end Loc

end GlobalTheory.TotPosSign

namespace GlobalTheory.TotPosSign

section CM
variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem isSplit_under {w : Pl E} (h : IsSplitAt w) : Formalism.MainNotions.SchurIrreducible.IsSplit (E := E) (w.under (𝓞 ↥(maximalRealSubfield E))) := by
  obtain ⟨u, hne, hu⟩ := h
  exact GlobalTheory.LFun.isSplit_iff.2 ⟨u, w, hne, hu, rfl⟩

theorem not_isSplit_under {w : Pl E} (h : ¬ IsSplitAt w) : ¬ Formalism.MainNotions.SchurIrreducible.IsSplit (E := E) (w.under (𝓞 ↥(maximalRealSubfield E))) := by
  rintro hs
  obtain ⟨a, b, hab, ha, hb⟩ := GlobalTheory.LFun.isSplit_iff.1 hs
  by_cases haw : a = w
  · subst haw
    exact h ⟨b, hab.symm, hb⟩
  · exact h ⟨a, haw, ha⟩

theorem isUnram_of_unr (hU : Unr E) (v : HeightOneSpectrum (𝓞 ↥(maximalRealSubfield E))) : Formalism.MainNotions.SchurIrreducible.IsUnram (E := E) v :=
  GlobalTheory.LFun.isUnram_iff.2 fun P _ => by
    haveI := hU P
    exact Ideal.ramificationIdx_eq_one_of_isUnramifiedAt

theorem neg_one_zpow_cast (k : ℤ) : ((((-1 : ℤˣ) ^ k : ℤˣ) : ℤ) : ℂ) = (-1 : ℂ) ^ k := by
  rcases Int.even_or_odd k with hk | hk
  · rw [hk.neg_one_zpow, hk.neg_one_zpow]; simp
  · rw [hk.neg_one_zpow, hk.neg_one_zpow]; simp

theorem term_eq (hU : Unr E) (w : Pl E) (t : Units ↥(maximalRealSubfield E)) :
    (if IsSplitAt w then (1 : ℂ) else (-1) ^ ordL (algebraMap E (w.adicCompletion E) (algebraMap ↥(maximalRealSubfield E) E t))) =
      ((GlobalTheory.QuadSymbol.eta ↥(maximalRealSubfield E) E ((w.under (𝓞 ↥(maximalRealSubfield E))).adicCompletion ↥(maximalRealSubfield E))
        (GlobalTheory.QuadSymbol.finDiag ↥(maximalRealSubfield E) t (w.under (𝓞 ↥(maximalRealSubfield E)))) : ℤ) : ℂ) := by
  have h2 : Module.finrank ↥(maximalRealSubfield E) E = 2 := Algebra.IsQuadraticExtension.finrank_eq_two ↥(maximalRealSubfield E) E
  split_ifs with hs
  · rw [GlobalTheory.QuadSymbol.eta_eq_one_iff.2 (GlobalTheory.LFun.mem_normGroup_of_isSplit h2 (isSplit_under hs) _)]
    simp
  · rw [eta_inert (not_isSplit_under hs) (isUnram_of_unr hU _), neg_one_zpow_cast]
    congr 1
    refine ordL_congr ?_
    have hx : ((GlobalTheory.QuadSymbol.finDiag ↥(maximalRealSubfield E) t (w.under (𝓞 ↥(maximalRealSubfield E))) : (w.under (𝓞 ↥(maximalRealSubfield E))).adicCompletion ↥(maximalRealSubfield E))) =
        algebraMap ↥(maximalRealSubfield E) _ (t : ↥(maximalRealSubfield E)) := rfl
    have e := GlobalTheory.LFun.valued_complMap (F := ↥(maximalRealSubfield E)) (E := E) (w := w) rfl
      (a := algebraMap ↥(maximalRealSubfield E) ((w.under (𝓞 ↥(maximalRealSubfield E))).adicCompletion ↥(maximalRealSubfield E)) (t : ↥(maximalRealSubfield E))) (by simp)
    rw [GlobalTheory.LFun.isUnram_iff.1 (isUnram_of_unr hU _) w rfl, pow_one, GlobalTheory.LFun.complMap_algebraMap] at e
    rw [hx, e]

theorem bijOn_under {S : Set (Pl E)} (hS : IsSection S) :
    Set.BijOn (fun w : Pl E => w.under (𝓞 ↥(maximalRealSubfield E))) S Set.univ := by
  refine ⟨fun _ _ => Set.mem_univ _, fun a ha b hb hab => ?_, fun v _ => ?_⟩
  · obtain ⟨u, -, hu⟩ := hS a
    exact (hu a ⟨ha, rfl⟩).trans (hu b ⟨hb, hab.symm⟩).symm
  · obtain ⟨w, hw⟩ := (GlobalTheory.QNorm.places_over ↥(maximalRealSubfield E) E).2.1 v
    obtain ⟨u, ⟨hu, hu'⟩, -⟩ := hS w
    exact ⟨u, hu, hu'.trans hw⟩

end CM

end GlobalTheory.TotPosSign

namespace GlobalTheory.UnitaryClasses


open GlobalTheory.TotPosSign in
theorem signProd_totPos : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ S : Set (Pl E), IsSection S →
    ∀ d : E, d ≠ 0 → (∀ τ : E →+* ℂ, ∃ r : ℝ, 0 < r ∧ τ d = r) →
    ∏ᶠ w ∈ S, (if IsSplitAt w then (1 : ℂ) else (-1) ^ ordL (algebraMap E (w.adicCompletion E) d)) = 1 := by
  intro E _ _ _ hU S hS d hd hpos
  have hmem : d ∈ maximalRealSubfield E := (mem_maximalRealSubfield_iff d).2 fun φ => by
    obtain ⟨r, -, hr⟩ := hpos φ
    rw [hr, Complex.star_def, Complex.conj_ofReal]
  set t0 : ↥(maximalRealSubfield E) := ⟨d, hmem⟩
  have ht0 : algebraMap (↥(maximalRealSubfield E)) E t0 = d := rfl
  have ht0' : t0 ≠ 0 := fun h => hd (by rw [← ht0, h, map_zero])
  set t := Units.mk0 t0 ht0'
  have PF := GlobalTheory.QuadSymbol.productFormula (↥(maximalRealSubfield E)) E t
  have hinf : ∀ w : InfinitePlace ↥(maximalRealSubfield E),
      GlobalTheory.QuadSymbol.eta (↥(maximalRealSubfield E)) E w.Completion (GlobalTheory.QuadSymbol.infDiag _ t w) = 1 := by
    intro w
    have hw : w.IsReal := IsTotallyReal.isReal w
    refine eta_inf_eq_one hw t ?_
    letI : Algebra (↥(maximalRealSubfield E)) ℂ := w.embedding.toAlgebra
    let τ : E →ₐ[↥(maximalRealSubfield E)] ℂ := (by
      refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
      solve_by_elim* (maxDepth := 2) only [*,
        @_root_.DivisionSemiring.to_moduleIsTorsionFree,
        @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
    obtain ⟨r, hr, e⟩ := hpos τ.toRingHom
    have e2 : (InfinitePlace.embedding_of_isReal hw (t : ↥(maximalRealSubfield E)) : ℂ) = r := by
      rw [InfinitePlace.embedding_of_isReal_apply, ← e]
      exact (τ.commutes t0).symm
    rw [Complex.ofReal_inj] at e2
    rw [e2]; exact hr
  have hfin : ∏ᶠ v : HeightOneSpectrum (𝓞 ↥(maximalRealSubfield E)),
      GlobalTheory.QuadSymbol.eta (↥(maximalRealSubfield E)) E (v.adicCompletion (↥(maximalRealSubfield E)))
        (GlobalTheory.QuadSymbol.finDiag (↥(maximalRealSubfield E)) t v) = 1 := by
    have h := PF.2
    unfold GlobalTheory.QuadSymbol.etaProd at h
    rwa [Finset.prod_eq_one fun w _ => hinf w, mul_one] at h
  let cz : ℤˣ →* ℂ := (Int.castRingHom ℂ).toMonoidHom.comp (Units.coeHom ℤ)
  have hd' : d = algebraMap (↥(maximalRealSubfield E)) E ((t : Units ↥(maximalRealSubfield E)) : ↥(maximalRealSubfield E)) := rfl
  rw [hd', finprod_mem_eq_of_bijOn _ (bijOn_under hS) (g := fun v : HeightOneSpectrum (𝓞 ↥(maximalRealSubfield E)) => cz
      (GlobalTheory.QuadSymbol.eta (↥(maximalRealSubfield E)) E (v.adicCompletion (↥(maximalRealSubfield E)))
        (GlobalTheory.QuadSymbol.finDiag (↥(maximalRealSubfield E)) t v))) fun w _ => term_eq hU w t,
    finprod_mem_univ, ← MonoidHom.map_finprod _ (GlobalTheory.QuadSymbol.AlmostNorm.finite_mulSupport PF.1), hfin, map_one]

end GlobalTheory.UnitaryClasses

end
end

section

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.Doubling
open GlobalTheory.SWLit

namespace GlobalTheory.AnisoCocompact

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

abbrev finP : AF F ⊗[F] E →+* Af F ⊗[F] E := (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E)).toRingHom

abbrev infP : AF F ⊗[F] E →+* Ainf F ⊗[F] E := (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E)).toRingHom

abbrev ratQ (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) : Subgroup (HA (AF F) σ J) := HFinIn (AF F) σ J

abbrev matA {σ : E →ₐ[F] E} {M : ℕ} {J : Matrix (Fin M) (Fin M) E} (g : HA (AF F) σ J) :
    Matrix (Fin M) (Fin M) (AF F ⊗[F] E) := (HA.mat (AF F) σ J g).1

theorem exists_finite_part (σ : E →ₐ[F] E) (hcm : IsCMExt F E σ) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (hJ : IsHermND σ J) : ∃ C : Set (Af F ⊗[F] E), IsCompact C ∧
    ∀ g : HA (AF F) σ J, ∃ γ ∈ ratQ σ J, ∀ B : Matrix (Fin M) (Fin M) E, (∀ a b, IsIntegral ℤ (B a b)) →
      ∀ a b, finP ((matA (g * γ) * B.map (inclR (F := F) (AF F))) a b) ∈ C := by
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ _ _
  haveI : IsModuleTopology (Af F) (Af F ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalRing (Af F ⊗[F] E) := IsModuleTopology.isTopologicalRing (Af F) _
  obtain ⟨π, hπ, -⟩ := GlobalTheory.Mass.existsUnique_isFinProj σ J
  obtain ⟨S, hS⟩ := GlobalTheory.Mem.ClassFinite.exists_finset_classes F E σ hcm M J hJ _ (GlobalTheory.Mass.isOpen_stdLevel σ J)
  obtain ⟨C, hC, hCe⟩ := (GlobalTheory.Mass.intTens_open_compact F E).2
  obtain ⟨C₁, hC₁, hCe₁⟩ := GlobalTheory.Mem.AnisoQuotient.exists_compact_mul hC
    (S.finite_toSet.image fun s => (HA.mat (Af F) σ J s⁻¹).1)
  refine ⟨C₁, hC₁, fun g => ?_⟩
  obtain ⟨γ₀, s, hs, k, hk, e⟩ := hS (π g⁻¹)
  obtain ⟨γ, hγ, hγe⟩ : (γ₀.1 : HA (Af F) σ J) ∈ (GlobalTheory.Mass.ratIn (AF F) σ J).map π := by
    rw [hπ.map_ratIn]; exact γ₀.2
  refine ⟨γ, hγ, fun B hBi a b => ?_⟩
  have e' : π (g * γ) = k⁻¹ * s⁻¹ := by
    have e1 : π g⁻¹ = π γ * (s * k) := by rw [hγe]; exact e
    rw [map_mul, ← inv_inv g, map_inv, e1]; group
  generalize g * γ = x at e'
  have e3 : (matA x).map finP = (HA.mat (Af F) σ J k⁻¹).1 * (HA.mat (Af F) σ J s⁻¹).1 := by
    have := congrArg Units.val (hπ x)
    rw [e'] at this
    exact this.symm
  have e4 : finP ((matA x * B.map (inclR (F := F) (AF F))) a b) =
      ((matA x).map finP * (B.map (inclR (F := F) (AF F))).map finP) a b :=
    congrFun (congrFun (Matrix.map_mul (L := matA x) (M := B.map (inclR (F := F) (AF F))) (f := finP)) a) b
  rw [e4, e3]
  refine hCe₁ _ ⟨s, hs, rfl⟩ _ _ (fun a b => hCe _ ((GlobalTheory.Mass.mem_stdLevel _ _ _).1 (inv_mem hk) a b).1)
    (fun a b => hCe _ ?_) a b
  exact Subring.subset_closure (Or.inl ⟨⟨B a b, ⟨_, hBi a b⟩, rfl⟩, rfl⟩)

theorem exists_real_part (σ : E →ₐ[F] E) (hcm : IsCMExt F E σ) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (hJ : J.det ≠ 0) (han : ∀ x, x ≠ 0 → Formalism.UG.hform (σ : E →+* E) J x x ≠ 0)
    {I : Type} [Fintype I] {τ : I → (E →+* ℂ)} (hτ : GlobalTheory.Mem.Vol.IsCMFam τ)
    {θ : I → (Ainf F ⊗[F] E →+* ℂ)} (hθ : ∀ ρ, Formalism.MainNotions.StandardLattice.IsInfEmb (τ ρ) (θ ρ)) :
    ∃ (R : ℝ) (𝓒 : Set (Matrix (Fin M) (Fin M) E)), 𝓒.Finite ∧ ∀ x : HA (AF F) σ J,
      ∃ u ∈ ratQ σ J, ∃ B : Matrix (Fin M) (Fin M) E, ∃ N ∈ 𝓒,
        matA u = (B * N).map (inclR (F := F) (AF F)) ∧ (∀ a b, IsIntegral ℤ (B a b)) ∧
        ∀ a b ρ, ‖θ ρ (infP ((matA x * B.map (inclR (F := F) (AF F))) a b))‖ ≤ R := by
  haveI := hcm.2.1
  obtain ⟨R, 𝓒, h𝓒, H⟩ := GlobalTheory.Mem.AnisoQuotient.exists_bounded_unitary (σ := (σ : E →+* E)) hτ
    (fun ρ x => hcm.2.2.2 _ x) hJ han
  refine ⟨R, 𝓒, h𝓒, fun x => ?_⟩
  let p : AF F ⊗[F] E →+* (I → ℂ) := Pi.ringHom fun ρ => (θ ρ).comp infP
  have hp : ∀ N : Matrix (Fin M) (Fin M) E, (N.map (inclR (F := F) (AF F))).map p = N.map (Pi.ringHom τ) :=
    fun N => by ext i j ρ; exact (hθ ρ).1 _
  have hev : ∀ (ρ : I) (X : Matrix (Fin M) (Fin M) (I → ℂ)), X.map (Pi.evalRingHom (fun _ => ℂ) ρ) = X.map (fun z => z ρ) :=
    fun _ _ => rfl
  obtain ⟨u, hu, B, N, hN, hum, hBi, hBR⟩ := H ((matA x).map p) (by
    ext i j ρ
    have h1 := congrFun (congrFun (GlobalTheory.Mem.VolExists.infMat_unitary J hcm (hθ ρ) x) i) j
    have h2 : ((Formalism.UG.cT (starRingEnd (I → ℂ)) ((matA x).map p) * J.map (Pi.ringHom τ) * (matA x).map p).map
        (Pi.evalRingHom (fun _ => ℂ) ρ)) = (Formalism.MainNotions.StandardLattice.infMat σ J (θ ρ) x).conjTranspose * J.map (τ ρ) *
        Formalism.MainNotions.StandardLattice.infMat σ J (θ ρ) x := by
      have e1 : ((matA x).map p).map (Pi.evalRingHom (fun _ => ℂ) ρ) = Formalism.MainNotions.StandardLattice.infMat σ J (θ ρ) x := by
        ext a b; rfl
      have e2 : (Formalism.UG.cT (starRingEnd (I → ℂ)) ((matA x).map p)).map (Pi.evalRingHom (fun _ => ℂ) ρ) =
          (Formalism.MainNotions.StandardLattice.infMat σ J (θ ρ) x).conjTranspose := by
        rw [← e1]; ext a b; rfl
      have e3 : (J.map (Pi.ringHom τ)).map (Pi.evalRingHom (fun _ => ℂ) ρ) = J.map (τ ρ) := by
        ext a b; rfl
      rw [Matrix.map_mul, Matrix.map_mul, e1, e2, e3]
    have h3 := congrFun (congrFun h2 i) j
    simp only [Matrix.map_apply, Pi.evalRingHom_apply] at h3
    rw [h3, h1]
    rfl)
  refine ⟨⟨_, GlobalTheory.Mem.ClassFinite.baseChange_mem (AF F) σ J u hu⟩, ⟨u, hu, rfl⟩, B, N, hN,
    congrArg (fun X => X.map (inclR (F := F) (AF F))) hum, hBi, fun a b ρ => ?_⟩
  have := hBR a b
  rw [← hp, ← Matrix.map_mul] at this
  exact (norm_le_pi_norm (p ((matA x * B.map (inclR (F := F) (AF F))) a b)) ρ).trans this

theorem exists_compact (σ : E →ₐ[F] E) (hcm : IsCMExt F E σ) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (hJ : IsHermND σ J) (han : ∀ x, x ≠ 0 → Formalism.UG.hform (σ : E →+* E) J x x ≠ 0) :
    ∃ K : Set (HA (AF F) σ J), IsCompact K ∧ ∀ g, ∃ γ ∈ ratQ σ J, ∃ k ∈ K, g = γ * k := by
  haveI := hcm.1
  let τ : InfinitePlace E → (E →+* ℂ) := fun w => w.embedding
  have hτ : GlobalTheory.Mem.Vol.IsCMFam τ := by
    have : (fun w => InfinitePlace.mk (τ w)) = id := funext fun w => InfinitePlace.mk_embedding w
    unfold GlobalTheory.Mem.Vol.IsCMFam; rw [this]; exact Function.bijective_id
  choose θ hθ1 hθ2 using fun ρ => GlobalTheory.InfAdeleCM.exists_hom (F := F) (τ ρ)
  have hθ : ∀ ρ, Formalism.MainNotions.StandardLattice.IsInfEmb (τ ρ) (θ ρ) := fun ρ => ⟨hθ1 ρ, hθ2 ρ⟩
  haveI : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ _ _
  haveI : IsTopologicalRing (AF F ⊗[F] E) := IsModuleTopology.isTopologicalRing (AF F) _
  haveI : IsTopologicalGroup (HA (AF F) σ J) := inferInstanceAs (IsTopologicalGroup (HR (AF F) σ J))
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  obtain ⟨C₁, hC₁, H₁⟩ := exists_finite_part σ hcm J hJ
  obtain ⟨R, 𝓒, h𝓒, H₂⟩ := exists_real_part σ hcm J hJ.2 han hτ hθ
  obtain ⟨C₂, hC₂, hCe₂⟩ := GlobalTheory.Mem.VolExists.exists_compact_adele hcm hτ hθ R C₁ hC₁
  obtain ⟨C₃, hC₃, hCe₃⟩ := GlobalTheory.Mem.AnisoQuotient.exists_compact_mul ((hC₂.insert 0).insert 1)
    (h𝓒.image fun N => N.map (inclR (F := F) (AF F)))
  obtain ⟨K, hK, hKe⟩ := GlobalTheory.StabCompact.exists_compact_of_entries (AF F) σ J hJ.2 C₃ hC₃
  refine ⟨Inv.inv '' K, hK.image continuous_inv, fun g => ?_⟩
  obtain ⟨γ, hγ, h₁⟩ := H₁ g⁻¹
  obtain ⟨u, hu, B, N, hN, hum, hBi, hBR⟩ := H₂ (g⁻¹ * γ)
  refine ⟨γ * u, mul_mem hγ hu, (g⁻¹ * γ * u)⁻¹, ⟨_, hKe _ fun a b => ?_, rfl⟩, by group⟩
  have e : matA (g⁻¹ * γ * u) = matA (g⁻¹ * γ) * B.map (inclR (F := F) (AF F)) *
      N.map (inclR (F := F) (AF F)) * 1 := by
    rw [show matA (g⁻¹ * γ * u) = matA (g⁻¹ * γ) * matA u from rfl, hum, Matrix.map_mul, Matrix.mul_one,
      Matrix.mul_assoc]
  change matA (g⁻¹ * γ * u) a b ∈ C₃
  rw [e]
  refine hCe₃ _ ⟨N, hN, rfl⟩ _ _ (fun a b => Or.inr (Or.inr (hCe₂ _ (h₁ B hBi a b) (hBR a b)))) (fun a b => ?_) a b
  rw [Matrix.one_apply]
  split_ifs
  exacts [Or.inl rfl, Or.inr (Or.inl rfl)]

end GlobalTheory.AnisoCocompact
end
end
