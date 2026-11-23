module

public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1469
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.QuadraticClassFieldTheory
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RealMetaplecticRepresentation
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1470
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle069
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle197
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsEverywhereNormDivOfEtaProdEqOne
public import Formalism.LocalRingCardinality.DataTheta
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1461
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle586
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle304
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorsionFiniteFlat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle794
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoNormalizationPullbackOfToIntegralClosure
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle418
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1471
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Limits.Shapes.Connected
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
import Mathlib.Tactic.ENatToNat
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
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle017
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle019
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle546
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle007
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle266
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle042
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle011
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.QSA GlobalTheory.Published
open Matrix
open scoped Quaternion Topology TensorProduct

theorem _root_.GlobalTheory.T.exists_placesIdempotent_near_one_adeles : ∀ (F : Type) [Field F] [NumberField F], ∀ U : Set (AF F), U ∈ 𝓝 (1 : AF F) → ∃ (S₁ : Finset (InfinitePlace F)) (S₂ : Finset (HeightOneSpectrum (𝓞 F))) (ε : AF F), IsPlacesIdem S₁ S₂ ε ∧ ε ∈ U := by
  first | exact @GlobalTheory.placesIdem_tendsto_one | exact GlobalTheory.placesIdem_tendsto_one | (intros; apply GlobalTheory.placesIdem_tendsto_one <;> assumption)
end

section

noncomputable section

open NumberField IsDedekindDomain

namespace GlobalTheory.QuadRecip

open GlobalTheory.QuadSymbol

theorem exists_global_iff_etaProd (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [Algebra.IsQuadraticExtension K L] (x : FinFam K) (y : InfFam K)
    (hx : AlmostNorm K L x) :
    (∃ t : Kˣ, (∀ v, x v / finDiag K t v ∈ normGroup K L (v.adicCompletion K)) ∧
        ∀ w, y w / infDiag K t w ∈ normGroup K L w.Completion) ↔
      etaProd K L x y = 1 :=
  (exactSequence K L).2.2.1 x y hx

theorem ringEquivReal_infDiag {K : Type} [Field K] [NumberField K] {w : InfinitePlace K}
    (hw : w.IsReal) (t : Kˣ) :
    InfinitePlace.Completion.ringEquivRealOfIsReal hw ((infDiag K t w : (w.Completion)ˣ) : w.Completion) =
      InfinitePlace.embedding_of_isReal hw (t : K) :=
  by
    simp [infDiag, QuadSymbol.toUnits, InfinitePlace.Completion.algebraMap_apply]

theorem mem_normGroup_of_pos {K L : Type} [Field K] [NumberField K] [Field L] [Algebra K L]
    [Algebra.IsQuadraticExtension K L] {w : InfinitePlace K} (hw : w.IsReal) (z : (w.Completion)ˣ)
    (hz : 0 < InfinitePlace.Completion.ringEquivRealOfIsReal hw (z : w.Completion)) :
    z ∈ normGroup K L w.Completion := by
  obtain ⟨δ, b, -, h0, h1⟩ := AlmostNorm.exists_basis_sq K L
  rw [mem_normGroup_iff_form b h0 h1]
  set e := InfinitePlace.Completion.ringEquivRealOfIsReal hw
  refine ⟨e.symm (Real.sqrt (e z)), 0, e.injective ?_⟩
  simp [Real.sq_sqrt hz.le]

theorem mem_normGroup_iff_pos {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [Algebra.IsQuadraticExtension K L] (hL : IsTotallyComplex L)
    {w : InfinitePlace K} (hw : w.IsReal) (z : (w.Completion)ˣ) :
    z ∈ normGroup K L w.Completion ↔
      0 < InfinitePlace.Completion.ringEquivRealOfIsReal hw (z : w.Completion) := by
  set e := InfinitePlace.Completion.ringEquivRealOfIsReal hw
  refine ⟨fun hz => ?_, mem_normGroup_of_pos hw z⟩
  have hne : e (z : w.Completion) ≠ 0 := (map_ne_zero e).2 z.ne_zero
  refine lt_of_le_of_ne (not_lt.1 fun hlt => ?_) hne.symm
  have hm : (-z) ∈ normGroup K L w.Completion :=
    mem_normGroup_of_pos hw (-z) (by rw [Units.val_neg, map_neg]; exact neg_pos.2 hlt)
  have h1 : (-1 : (w.Completion)ˣ) = z * (-z)⁻¹ := by rw [inv_neg, mul_neg, mul_inv_cancel]
  exact SignCount.neg_one_not_mem_normGroup hL hw (h1 ▸ mul_mem hz (inv_mem hm))

end GlobalTheory.QuadRecip

namespace GlobalTheory.QuadRecip

open GlobalTheory.QuadSymbol


open Classical in
theorem prod_sign_eq {K : Type} [Field K] [NumberField K] (S : Finset {w : InfinitePlace K // w.IsReal})
    (f : InfinitePlace K → ℤˣ)
    (hf : ∀ w, f w = if (∃ hw : w.IsReal, (⟨w, hw⟩ : {w : InfinitePlace K // w.IsReal}) ∈ S) then -1 else 1) :
    ∏ w, f w = (-1) ^ S.card := by
  classical
  simp_rw [hf]
  rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one]
  congr 1
  have : (Finset.univ.filter fun w : InfinitePlace K =>
      ∃ hw : w.IsReal, (⟨w, hw⟩ : {w : InfinitePlace K // w.IsReal}) ∈ S) =
      S.map (Function.Embedding.subtype _) := by
    ext w
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
      Function.Embedding.subtype_apply]
    constructor
    · rintro ⟨hw, h⟩
      exact ⟨_, h, rfl⟩
    · rintro ⟨u, hu, rfl⟩
      exact ⟨u.2, hu⟩
  rw [this, Finset.card_map]


open Classical in
theorem exists_signs_iff_even (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [Algebra.IsQuadraticExtension K L] (hL : IsTotallyComplex L)
    (S : Finset {w : InfinitePlace K // w.IsReal}) :
    (∃ h : Kˣ, (∀ w : {w : InfinitePlace K // w.IsReal},
        (w ∈ S → InfinitePlace.embedding_of_isReal w.2 (h : K) < 0) ∧
        (w ∉ S → 0 < InfinitePlace.embedding_of_isReal w.2 (h : K))) ∧
      ∀ v : HeightOneSpectrum (𝓞 K), finDiag K h v ∈ normGroup K L (v.adicCompletion K)) ↔
      Even S.card := by
  classical
  obtain ⟨δ, b, -, h0, h1⟩ := AlmostNorm.exists_basis_sq K L
  have hneg1 : ((-1 : ℤˣ) ≠ 1) := by decide
  constructor
  · rintro ⟨h, hsgn, hfin⟩
    have hpf := (productFormula K L h).2
    unfold etaProd at hpf
    have hf1 : ∀ v : HeightOneSpectrum (𝓞 K), eta K L (v.adicCompletion K) (finDiag K h v) = 1 :=
      fun v => eta_eq_one_iff.2 (hfin v)
    simp only [hf1, finprod_one, one_mul] at hpf
    rw [prod_sign_eq S _ (fun w => ?_)] at hpf
    · exact (neg_one_pow_eq_one_iff_even hneg1).1 hpf
    · by_cases hw : w.IsReal
      · have key := mem_normGroup_iff_pos hL hw (infDiag K h w)
        rw [ringEquivReal_infDiag hw h] at key
        by_cases hS : (⟨w, hw⟩ : {w : InfinitePlace K // w.IsReal}) ∈ S
        · rw [if_pos ⟨hw, hS⟩, eta_eq_neg_one_iff, key]
          exact not_lt.2 ((hsgn ⟨w, hw⟩).1 hS).le
        · rw [if_neg (by rintro ⟨hw', h'⟩; exact hS h'), eta_eq_one_iff, key]
          exact (hsgn ⟨w, hw⟩).2 hS
      · rw [if_neg (by rintro ⟨hw', _⟩; exact hw hw'), eta_eq_one_iff]
        exact Converse.mem_normGroup_of_isComplex b h0 h1 (InfinitePlace.not_isReal_iff_isComplex.1 hw) _
  · intro hS
    let P : InfinitePlace K → Prop := fun w =>
      ∃ hw : w.IsReal, (⟨w, hw⟩ : {w : InfinitePlace K // w.IsReal}) ∈ S
    let y : InfFam K := fun w => if P w then -1 else 1
    have hy : ∀ w, eta K L w.Completion (y w) = if P w then -1 else 1 := by
      intro w
      by_cases hP : P w
      · simp only [y, if_pos hP]
        exact eta_eq_neg_one_iff.2 (SignCount.neg_one_not_mem_normGroup hL hP.1)
      · simp only [y, if_neg hP]
        exact eta_eq_one_iff.2 (one_mem _)
    have hx : AlmostNorm K L (1 : FinFam K) := by
      refine Set.Finite.subset Set.finite_empty fun v hv => hv ?_
      exact one_mem _
    have hprod : etaProd K L 1 y = 1 := by
      unfold etaProd
      have hf1 : ∀ v : HeightOneSpectrum (𝓞 K),
          eta K L (v.adicCompletion K) ((1 : FinFam K) v) = 1 := fun v => eta_eq_one_iff.2 (one_mem _)
      simp only [hf1, finprod_one, one_mul]
      rw [prod_sign_eq S _ hy]
      exact hS.neg_one_pow
    obtain ⟨t, htf, hti⟩ := (exists_global_iff_etaProd K L 1 y hx).2 hprod
    refine ⟨t, fun w => ?_, fun v => ?_⟩
    · have key := (mem_normGroup_iff_pos hL w.2 _).1 (hti w.1)
      rw [Units.val_div_eq_div_val, map_div₀, ringEquivReal_infDiag w.2 t] at key
      have hP : P w.1 ↔ w ∈ S := ⟨by rintro ⟨_, h⟩; exact h, fun h => ⟨w.2, h⟩⟩
      constructor
      · intro hw
        have hyw : y w.1 = -1 := if_pos (hP.2 hw)
        rw [hyw, Units.val_neg, Units.val_one, map_neg, map_one] at key
        have := (div_pos_iff.1 key)
        rcases this with ⟨h1, -⟩ | ⟨-, h2⟩
        · linarith
        · exact h2
      · intro hw
        have hyw : y w.1 = 1 := if_neg (fun h => hw (hP.1 h))
        rw [hyw, Units.val_one, map_one] at key
        exact (one_div_pos).1 key
    · have := htf v
      rw [Pi.one_apply, one_div, inv_mem_iff] at this
      exact this

theorem exists_signs_of_even (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [Algebra.IsQuadraticExtension K L] (hK : IsTotallyReal K) (hL : IsTotallyComplex L)
    (S : Finset (InfinitePlace K)) (hS : Even S.card) :
    ∃ h : Kˣ, (∀ w (hw : w ∈ S), InfinitePlace.embedding_of_isReal (hK.isReal w) (h : K) < 0) ∧
      (∀ w (hw : w ∉ S), 0 < InfinitePlace.embedding_of_isReal (hK.isReal w) (h : K)) ∧
      ∀ v : HeightOneSpectrum (𝓞 K), finDiag K h v ∈ normGroup K L (v.adicCompletion K) := by
  classical
  let S' : Finset {w : InfinitePlace K // w.IsReal} := S.subtype _
  have hc : S'.card = S.card := by
    rw [Finset.card_subtype]
    congr 1
    exact Finset.filter_true_of_mem fun w _ => hK.isReal w
  obtain ⟨h, hsgn, hfin⟩ := (exists_signs_iff_even K L hL S').2 (hc ▸ hS)
  refine ⟨h, fun w hw => (hsgn ⟨w, hK.isReal w⟩).1 ?_, fun w hw => (hsgn ⟨w, hK.isReal w⟩).2 ?_, hfin⟩
  · simpa [S'] using hw
  · simpa [S'] using hw

end GlobalTheory.QuadRecip
end
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.WeilTr MeasureTheory
open scoped Matrix ENNReal

theorem _root_.GlobalTheory.T.rho_invariant_form_const_mul_inner : (∀ (n : ℕ) (B : GlobalTheory.RealWeil.Sch (Fin n) → GlobalTheory.RealWeil.Sch (Fin n) → ℂ),
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
  first | exact @GlobalTheory.ArchUniq.FormTransport.const_of_euclidean | exact GlobalTheory.ArchUniq.FormTransport.const_of_euclidean | (intros; apply GlobalTheory.ArchUniq.FormTransport.const_of_euclidean <;> assumption)
end

section

open scoped TensorProduct Matrix
open MeasureTheory Formalism.BasicNotions.TH GlobalTheory.RealLift GlobalTheory.RealWeil
open GlobalTheory.HoweD

theorem _root_.GlobalTheory.T.exists_oscillator_action_normalising_schrodinger : ∀ (ι l : Type) [Fintype ι] [DecidableEq ι] [Fintype l] [DecidableEq l] (P Q R S : ι → ℕ)
    (φ : (∀ w : ι, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ) ≃ₗ[ℝ] (l ⊕ l → ℝ)),
    (∀ c c', sympl (φ c) (φ c') = 2 * (∑ w, ∑ a, ∑ b, lineSign a b * c w a b * star (c' w a b)).im) →
    (∀ v : L2 l, Continuous fun w : l ⊕ l → ℝ => rho w v) →
    ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (k : G →* (∀ w : ι, Mat (R w) (S w))), Continuous k →
    (∀ g w, (k g w)ᴴ * Jm (R w) (S w) * k g w = Jm (R w) (S w)) →
    ∃ ω : G →* (L2 l ≃ₗᵢ[ℂ] L2 l), (∀ v, Continuous fun g => ω g v) ∧
      ∀ g c v, ω g (rho (φ c) v) = rho (φ fun w => c w * (k g w)ᵀ) (ω g v) := by
  first | exact @GlobalTheory.HoweD.exists_osc | exact GlobalTheory.HoweD.exists_osc | (intros; apply GlobalTheory.HoweD.exists_osc <;> assumption)
end

section

open scoped TensorProduct Matrix
open MeasureTheory Formalism.BasicNotions.TH GlobalTheory.RealLift GlobalTheory.RealWeil
open GlobalTheory.HoweD

theorem _root_.GlobalTheory.T.exists_symplectic_hom_of_unitary_transpose_action : ∀ (ι l : Type) [Fintype ι] [DecidableEq ι] [Fintype l] [DecidableEq l] (P Q R S : ι → ℕ)
    (φ : (∀ w : ι, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ) ≃ₗ[ℝ] (l ⊕ l → ℝ)),
    (∀ c c', sympl (φ c) (φ c') = 2 * (∑ w, ∑ a, ∑ b, lineSign a b * c w a b * star (c' w a b)).im) →
    ∀ (G : Type) [Group G] [TopologicalSpace G] (k : G →* (∀ w : ι, Mat (R w) (S w))), Continuous k →
    (∀ g w, (k g w)ᴴ * Jm (R w) (S w) * k g w = Jm (R w) (S w)) →
    ∃ s : G →* Matrix.symplecticGroup l ℝ, Continuous s ∧
      ∀ g c, (s g : Matrix (l ⊕ l) (l ⊕ l) ℝ) *ᵥ φ c = φ fun w => c w * (k g w)ᵀ := by
  first | exact @GlobalTheory.ColActionD.exists_symplectic_hom_of_unitary_dep | exact GlobalTheory.ColActionD.exists_symplectic_hom_of_unitary_dep | (intros; apply GlobalTheory.ColActionD.exists_symplectic_hom_of_unitary_dep <;> assumption)
end

section

open scoped TensorProduct Matrix
open MeasureTheory Formalism.BasicNotions.TH GlobalTheory.RealLift GlobalTheory.RealWeil
open GlobalTheory.HoweD

theorem _root_.GlobalTheory.T.exists_symplecticLie_right_action_realCoordinates : ∀ (ι l : Type) [Fintype ι] [DecidableEq ι] [Fintype l] [DecidableEq l] (P Q R S : ι → ℕ)
    (φ : (∀ w : ι, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ) ≃ₗ[ℝ] (l ⊕ l → ℝ)),
    (∀ c c', sympl (φ c) (φ c') = 2 * (∑ w, ∑ a, ∑ b, lineSign a b * c w a b * star (c' w a b)).im) →
    ∀ Y : ∀ w : ι, Mat (R w) (S w), (∀ w, Y w ∈ upq (R w) (S w)) →
    ∃ Z ∈ LieAlgebra.Symplectic.sp l ℝ, (∀ c, Z *ᵥ φ c = φ fun w => c w * (Y w)ᵀ) ∧
      ∀ (t : ℝ) c, NormedSpace.exp (t • Z) *ᵥ φ c = φ fun w => c w * (NormedSpace.exp (t • Y w))ᵀ := by
  first | exact @GlobalTheory.HoweD.SpLieD.exists_sp_rightActD | exact GlobalTheory.HoweD.SpLieD.exists_sp_rightActD | (intros; apply GlobalTheory.HoweD.SpLieD.exists_sp_rightActD <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
open scoped CategoryTheory.Obj

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.UPel.HT.ES.OrdCount


open GlobalTheory.IwLevel GlobalTheory.IwLevel.KerGrp in
theorem exists_idem_kernel : ∀ (S : Scheme.{0}) (A A' : Over S) [GrpObj A] [IsCommMonObj A] [GrpObj A'] [IsCommMonObj A'] (ψ : A ⟶ A') (f : A ⟶ A), IsMonHom ψ → IsMonHom f → IsFinite ψ.left → Flat ψ.left → (∀ (T : Over S) (z : T ⟶ A), z ≫ ψ = 1 → (z ≫ f) ≫ ψ = 1 ∧ (z ≫ f) ≫ f = z ≫ f) → ∃ (K : Over S) (_ : GrpObj K) (i : K ⟶ A), IsMonHom i ∧ Mono i ∧ IsFinite K.hom ∧ Flat K.hom ∧ ∀ (T : Over S) (z : T ⟶ A), GlobalTheory.IwLevel.InSub i z ↔ (z ≫ ψ = 1 ∧ z ≫ f = 1) := by
  intro S A A' _ _ _ _ ψ fx _ _ hfin hfl hyp
  letI gH : GrpObj (IwLevel.ker ψ) := grp ψ
  haveI : IsMonHom (pullback.fst ψ η[A']) := isMonHom_fst ψ
  have hPB := (IsPullback.of_hasPullback ψ η[A']).map (Over.forget S)
  have hHfin : IsFinite (IwLevel.ker ψ).hom := by
    rw [← Over.w (pullback.snd ψ η[A'])]
    haveI : IsFinite (pullback.snd ψ η[A']).left := MorphismProperty.of_isPullback (P := @IsFinite) hPB hfin
    exact inferInstanceAs (IsFinite (_ ≫ 𝟙 S))
  have hHflat : Flat (IwLevel.ker ψ).hom := by
    rw [← Over.w (pullback.snd ψ η[A'])]
    haveI : Flat (pullback.snd ψ η[A']).left := MorphismProperty.of_isPullback (P := @Flat) hPB hfl
    exact inferInstanceAs (Flat (_ ≫ 𝟙 S))
  set jH := pullback.fst ψ η[A'] with hjH
  have hj : jH ≫ ψ = 1 := fst_comp ψ
  let g : IwLevel.ker ψ ⟶ IwLevel.ker ψ := KerGrp.lift ψ (jH ≫ fx) (hyp _ jH hj).1
  have hg : g ≫ jH = jH ≫ fx := KerGrp.lift_fst _ _ _
  have hxx' : jH ≫ fx ≫ fx = jH ≫ fx := by rw [← Category.assoc]; exact (hyp _ jH hj).2
  letI gK : GrpObj (IwLevel.ker (jH ≫ fx)) := grp (jH ≫ fx)
  haveI : IsMonHom (pullback.fst (jH ≫ fx) η[A]) := isMonHom_fst (jH ≫ fx)
  set iK := pullback.fst (jH ≫ fx) η[A] with hiK
  have hk : iK ≫ jH ≫ fx = 1 := fst_comp (jH ≫ fx)
  have hrk : (𝟙 (IwLevel.ker ψ) / g) ≫ jH ≫ fx = 1 := by
    rw [← Category.assoc, GrpObj.div_comp, Category.id_comp, hg, GrpObj.div_comp, Category.assoc, hxx',
      div_self']
  let r : IwLevel.ker ψ ⟶ IwLevel.ker (jH ≫ fx) := KerGrp.lift (jH ≫ fx) (𝟙 (IwLevel.ker ψ) / g) hrk
  have hr : r ≫ iK = 𝟙 (IwLevel.ker ψ) / g := KerGrp.lift_fst _ _ _
  have hiKg : iK ≫ g = 1 := KerGrp.hom_ext ψ (by
    rw [Category.assoc, hg, hk, MonObj.one_comp])
  have hir : iK ≫ r = 𝟙 _ := KerGrp.hom_ext (jH ≫ fx) (by
    rw [Category.assoc, hr, GrpObj.comp_div, Category.comp_id, hiKg, div_one, Category.id_comp])
  have hirl : iK.left ≫ r.left = 𝟙 _ := by rw [← Over.comp_left, hir, Over.id_left]
  have hKfin : IsFinite (IwLevel.ker (jH ≫ fx)).hom := by
    haveI : IsFinite (r.left ≫ (IwLevel.ker (jH ≫ fx)).hom) := by rw [Over.w r]; exact hHfin
    haveI : IsSeparated (r.left ≫ (IwLevel.ker (jH ≫ fx)).hom) := by rw [Over.w r]; infer_instance
    haveI : IsSeparated r.left := IsSeparated.of_comp _ (IwLevel.ker (jH ≫ fx)).hom
    haveI : IsFinite (iK.left ≫ r.left) := by rw [hirl]; infer_instance
    haveI : IsFinite iK.left := IsFinite.of_comp _ r.left
    rw [← Over.w iK]; infer_instance
  have hKflat : Flat (IwLevel.ker (jH ≫ fx)).hom := by
    haveI : Flat (r.left ≫ (IwLevel.ker (jH ≫ fx)).hom) := by rw [Over.w r]; exact hHflat
    exact HTTorsionFF.flat_of_retract _ iK.left r.left hirl
  refine ⟨IwLevel.ker (jH ≫ fx), gK, iK ≫ jH, inferInstance, inferInstance, hKfin, hKflat, fun T z => ?_⟩
  refine ⟨?_, fun ⟨h1, h2⟩ => ?_⟩
  · rintro ⟨y, rfl⟩
    refine ⟨?_, ?_⟩
    · rw [Category.assoc, Category.assoc, hj, MonObj.comp_one, MonObj.comp_one]
    · rw [Category.assoc, Category.assoc, hk, MonObj.comp_one]
  · refine ⟨KerGrp.lift (jH ≫ fx) (KerGrp.lift ψ z h1) (by rw [← Category.assoc, KerGrp.lift_fst, h2]), ?_⟩
    rw [← Category.assoc, KerGrp.lift_fst, KerGrp.lift_fst]

def subEquiv {S : Scheme.{0}} {A K T : Over S} (i : K ⟶ A) [Mono i] (P : (T ⟶ A) → Prop)
    (h : ∀ x, GlobalTheory.IwLevel.InSub i x ↔ P x) : (T ⟶ K) ≃ {x : T ⟶ A // P x} :=
  Equiv.ofBijective (fun g => ⟨g ≫ i, (h _).1 ⟨g, rfl⟩⟩)
    ⟨fun g g' hgg => (cancel_mono i).1 (congrArg Subtype.val hgg),
     fun x => let ⟨g, hg⟩ := (h x.1).2 x.2; ⟨g, Subtype.ext hg⟩⟩

theorem eq_one_of_reg {S : Scheme.{0}} (A : Over S) [GrpObj A] [IsCommMonObj A] (hA : IsAbelianScheme A)
    {T : Over S} (x : T ⟶ A) (c : ℕ)
    (hc : ∀ (U : T.left.Opens) (f : Γ(T.left, U)), (c : Γ(T.left, U)) * f = 0 → f = 0) (hx : x ^ c = 1)
    (h : ∀ (k : Type) [Field k] [IsAlgClosed k], (c : k) ≠ 0 → ∀ (z : Sp k ⟶ S) (g : Over.mk z ⟶ T), g ≫ x = 1) :
    x = 1 := by
  obtain ⟨U, j, hj, hu⟩ := GlobalTheory.T.exists_dominant_natCast_isUnit_of_nonZeroDivisor T.left c hc
  let j' : Over.mk (j ≫ T.hom) ⟶ T := Over.homMk j
  have h1 : j' ≫ x = 1 := GlobalTheory.T.abelianScheme_torsionPoint_trivial_of_geometric S A hA _ (j' ≫ x) c hu (by rw [← MonObj.comp_pow, hx, MonObj.comp_one])
    (fun k _ _ hk z g => by rw [← Category.assoc]; exact h k hk z _)
  have h2 : j' ≫ x = j' ≫ 1 := by rw [h1, MonObj.comp_one]
  have := hA.proper
  exact Over.OverMorphism.ext (GlobalTheory.hom_ext_of_isSchemeTheoreticallyDominant j A.hom
    (congrArg CommaMorphism.left h2) (by rw [Over.w, Over.w]))

end GlobalTheory.UPel.HT.ES.OrdCount
end
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published
open scoped TensorProduct Pointwise

noncomputable section

namespace GlobalTheory.CompanionTheory.SaGen.ExtZero

open GlobalTheory.CompanionTheory.SaGen

variable {F E K : Type} [Field F] [NumberField F] [Field E] [Algebra F E] [Field K] [Algebra F K]
  [TopologicalSpace K]

theorem iB_tmul (P : PlaceMap F K) (x : K) (e : E) :
    iB (E := E) P (x ⊗ₜ[F] e) = P.inj x ⊗ₜ[F] e := rfl

theorem iB_eq_sum [FiniteDimensional F E] (P : PlaceMap F K) (y : K ⊗[F] E) :
    iB (E := E) P y = ∑ k, P.inj ((Algebra.TensorProduct.basis K (Module.finBasis F E)).repr y k) •
      ((1 : AF F) ⊗ₜ[F] (Module.finBasis F E) k) := by
  set B := Algebra.TensorProduct.basis K (Module.finBasis F E)
  conv_lhs => rw [← B.sum_repr y]

  rw [map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [B, Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one, iB_tmul]

theorem continuous_iB [FiniteDimensional F E] [IsTopologicalRing K] (P : PlaceMap F K) :
    Continuous (iB (E := E) P) := by
  haveI : IsModuleTopology K (K ⊗[F] E) := ⟨rfl⟩
  haveI : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  haveI : ContinuousAdd (AF F ⊗[F] E) := IsModuleTopology.toContinuousAdd (AF F) (AF F ⊗[F] E)
  haveI : ContinuousSMul (AF F) (AF F ⊗[F] E) := IsModuleTopology.toContinuousSMul (AF F) (AF F ⊗[F] E)
  have hc : ∀ k, Continuous fun y : K ⊗[F] E =>
      (Algebra.TensorProduct.basis K (Module.finBasis F E)).repr y k := fun k =>
    IsModuleTopology.continuous_of_linearMap ((Algebra.TensorProduct.basis K (Module.finBasis F E)).coord k)
  have h : (iB (E := E) P : K ⊗[F] E → AF F ⊗[F] E) = fun y => ∑ k,
      P.inj ((Algebra.TensorProduct.basis K (Module.finBasis F E)).repr y k) •
        ((1 : AF F) ⊗ₜ[F] (Module.finBasis F E) k) := funext (iB_eq_sum P)
  rw [h]
  exact continuous_finsetSum _ fun k _ =>
    Continuous.smul (f := fun y => P.inj ((Algebra.TensorProduct.basis K (Module.finBasis F E)).repr y k))
      (g := fun _ => (1 : AF F) ⊗ₜ[F] (Module.finBasis F E) k) (P.cont_inj.comp (hc k)) continuous_const

end GlobalTheory.CompanionTheory.SaGen.ExtZero

theorem GlobalTheory.CompanionTheory.SaGen.ExtZero.continuous_iB_place : ∀ {F E K : Type} [Field F] [NumberField F] [Field E] [Algebra F E] [FiniteDimensional F E] [Field K] [Algebra F K] [TopologicalSpace K] [IsTopologicalRing K] (P : GlobalTheory.CompanionTheory.SaGen.PlaceMap F K), Continuous (GlobalTheory.CompanionTheory.SaGen.iB (E := E) P) :=
  fun P => GlobalTheory.CompanionTheory.SaGen.ExtZero.continuous_iB P
end
end

section

open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR

theorem _root_.GlobalTheory.T.fockActions_lie_rationalWeights_commute : ∀ P Q R S : ℕ, IsLieAct (fockAct1 P Q R S) ∧ IsLieAct (fockAct2 P Q R S) ∧ (∀ v, v ∈ ⨆ μ : Ix P Q → ℚ, wtSub (fockAct1 P Q R S) μ) ∧ (∀ v, v ∈ ⨆ μ : Ix R S → ℚ, wtSub (fockAct2 P Q R S) μ) ∧ ∀ X Y f, fockAct1 P Q R S X (fockAct2 P Q R S Y f) = fockAct2 P Q R S Y (fockAct1 P Q R S X f) := by
  first | exact @GlobalTheory.HoweR.fock_lie_wts_comm | exact GlobalTheory.HoweR.fock_lie_wts_comm | (intros; apply GlobalTheory.HoweR.fock_lie_wts_comm <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.cuspFormsAgreement_contains_formIndependentFields : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) , Nonempty (FWTie T R κ v₀) → TieIn T R κ v₀ := by
  first | exact @GlobalTheory.tieIn_of_nonempty_tie | exact GlobalTheory.tieIn_of_nonempty_tie | (intros; apply GlobalTheory.tieIn_of_nonempty_tie <;> assumption)
end
