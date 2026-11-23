module

public import Development.AbelianVarietyTheory.Definitions.Divisors.FderivFnCongr
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle859
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasLevelStd
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle024
public import Mathlib.Analysis.Complex.UpperHalfPlane.MoebiusAction
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle729
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle670
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle728
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle862
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle676
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle686
public import Development.AbelianVarietyTheory.Definitions.Divisors.KerIdealCompOfSurjective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle863
public import Development.AbelianVarietyTheory.Definitions.Divisors.PullHlComp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle463
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle563
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle461
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle613
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle403
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle864
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle654
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle801
public import Development.AbelianVarietyTheory.Definitions.Divisors.TorsTransport
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle865
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Lemma
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
import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
import Development.AbelianVarietyTheory.Definitions.Divisors.Pullback1MemHodgeFiltration
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle001
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle023
import Development.AbelianVarietyTheory.Definitions.Divisors.ToSpanSingletonConstGenInjective
import Mathlib.Tactic.TypeStar
public import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle001

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.holomorphicPoint_ext_of_isSeparated : ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (W : Opens E) {X : Scheme.{0}}, X.IsSeparated → ∀ x x' : Sp (Hol W) ⟶ X, (∀ (p : E) (hp : p ∈ W), spMap (Hol.ev p hp).toRingHom ≫ x = spMap (Hol.ev p hp).toRingHom ≫ x') → x = x' := by
  first | exact @GlobalTheory.AnPer.point_hol_ext_of_isSeparated | exact GlobalTheory.AnPer.point_hol_ext_of_isSeparated | (intros; apply GlobalTheory.AnPer.point_hol_ext_of_isSeparated <;> assumption)
end

section

set_option autoImplicit false

noncomputable section

open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
open GlobalTheory.LatVal (Sz)
open GlobalTheory.LatJet (EisExp IsEis FR)
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (LatPair latRel eisClass eisTerm latPt eisClass_mk)

namespace GlobalTheory.HilbFam.EisCmp

variable {F : Type} [Field F] [NumberField F]

theorem card_realEmb (F : Type) [Field F] [NumberField F] [IsTotallyReal F] :
    Fintype.card (Emb F) = Module.finrank ℚ F := by
  rw [← NumberField.Embeddings.card F ℂ]
  refine Fintype.card_of_bijective (f := fun τ : F →+* ℝ ↦ (Complex.ofRealHom.comp τ : F →+* ℂ)) ⟨?_, ?_⟩
  · intro τ τ' hτ
    ext y
    have := DFunLike.congr_fun hτ y
    simpa using this
  · intro φ
    have hr : NumberField.ComplexEmbedding.IsReal φ := IsTotallyReal.complexEmbedding_isReal φ
    exact ⟨hr.embedding, by ext y; simp⟩

theorem mem_split (𝔞 𝔟 : Frac F) (v : Fin 2 → F) :
    v ∈ split 𝔞 𝔟 0 ↔ v 0 ∈ (𝔟 : FractionalIdeal (𝓞 F)⁰ F) ∧ v 1 ∈ latM 𝔞 := by
  show v 0 ∈ (𝔟 : FractionalIdeal (𝓞 F)⁰ F) ∧ v 1 - v 0 * 0 ∈ latM 𝔞 ↔ _
  rw [mul_zero, sub_zero]

theorem unit_smul_apply (ε : (𝓞 F)ˣ) (v : Fin 2 → F) (i : Fin 2) : (ε • v) i = ((ε : 𝓞 F) : F) * v i := by
  rw [Pi.smul_apply, Units.smul_def, Algebra.smul_def]

def pair (𝔞 𝔟 : Frac F) (q : cls (split 𝔞 𝔟 0)) : LatPair 𝔞 𝔟 :=
  ⟨(q.1.out 1, q.1.out 0), ((mem_split 𝔞 𝔟 _).1 q.2.1).2, ((mem_split 𝔞 𝔟 _).1 q.2.1).1, fun h ↦ q.2.2 (by
    funext i
    fin_cases i
    · exact congrArg Prod.snd h
    · exact congrArg Prod.fst h)⟩

theorem bij (𝔞 𝔟 : Frac F) :
    Function.Bijective (fun q : cls (split 𝔞 𝔟 0) ↦ Quotient.mk (latRel 𝔞 𝔟) (pair 𝔞 𝔟 q)) := by
  constructor
  · intro q1 q2 h
    obtain ⟨ε, h1, h2⟩ := Quotient.exact h
    apply Subtype.ext
    rw [← Quotient.out_eq q1.1, ← Quotient.out_eq q2.1]
    refine (Quotient.sound ?_).symm
    refine ⟨ε, ?_⟩
    funext i
    show (ε • q1.1.out) i = _
    rw [unit_smul_apply]
    fin_cases i
    · exact h2.symm
    · exact h1.symm
  · intro cl
    obtain ⟨p, rfl⟩ := Quotient.exists_rep cl
    let v : Fin 2 → F := ![p.1.2, p.1.1]
    have hv : v ∈ split 𝔞 𝔟 0 := (mem_split 𝔞 𝔟 v).2 ⟨p.2.2.1, p.2.1⟩
    have hv0 : v ≠ 0 := fun h ↦ p.2.2.2 (Prod.ext (congrFun h 1) (congrFun h 0))
    obtain ⟨ε, hε⟩ : (Quotient.mk (MulAction.orbitRel (𝓞 F)ˣ (Fin 2 → F)) v).out ∈ MulAction.orbit (𝓞 F)ˣ v :=
      Quotient.exact (Quotient.out_eq (Quotient.mk (MulAction.orbitRel (𝓞 F)ˣ (Fin 2 → F)) v))
    have hε' : (Quotient.mk (MulAction.orbitRel (𝓞 F)ˣ (Fin 2 → F)) v).out = ε • v := hε.symm
    refine ⟨⟨Quotient.mk _ v, ?_, ?_⟩, ?_⟩
    · rw [hε']; exact Submodule.smul_mem _ (ε : 𝓞 F) hv
    · rw [hε']; exact (smul_ne_zero_iff_ne ε).2 hv0
    · refine (Quotient.sound (show (latRel 𝔞 𝔟).r p _ from ⟨ε, ?_, ?_⟩)).symm
      · exact (congrFun hε' 1).trans (unit_smul_apply ε v 1)
      · exact (congrFun hε' 0).trans (unit_smul_apply ε v 0)

theorem term_eq [IsTotallyReal F] (k : ℕ) (σ : ℂ) (w : Emb F → ℂ) (x : Fin 2 → F) :
    gTerm k σ w 1 x = (((2 * Real.pi * Complex.I) ^ Module.finrank ℚ F) ^ k *
      ((‖(2 * Real.pi * Complex.I : ℂ) ^ Module.finrank ℚ F‖ : ℝ) : ℂ) ^ (2 * σ)) * eisTerm k σ w (x 1, x 0) := by
  have hP : ∏ τ, latPt w (x 1, x 0) τ = (2 * Real.pi * Complex.I) ^ Module.finrank ℚ F * ∏ τ, coord w 1 x τ := by
    rw [← card_realEmb, ← Finset.card_univ, ← Finset.prod_const, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun τ _ ↦ ?_
    simp only [latPt, coord, Pi.one_apply]; ring
  have hΛ : (2 * Real.pi * Complex.I : ℂ) ^ Module.finrank ℚ F ≠ 0 := pow_ne_zero _ Complex.two_pi_I_ne_zero
  unfold gTerm eisTerm
  rw [hP]
  generalize (2 * Real.pi * Complex.I : ℂ) ^ Module.finrank ℚ F = Λ at hΛ
  have hn : ((‖Λ‖ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (norm_ne_zero_iff.2 hΛ)
  have h1 : Λ ^ k * Λ⁻¹ ^ k = 1 := by rw [← mul_pow, mul_inv_cancel₀ hΛ, one_pow]
  have h2 : ((‖Λ‖ : ℝ) : ℂ) ^ (2 * σ) * ((‖Λ‖ : ℝ) : ℂ) ^ (-2 * σ) = 1 := by
    rw [← Complex.cpow_add _ _ hn, show 2 * σ + -2 * σ = 0 by ring, Complex.cpow_zero]
  rw [mul_inv, mul_pow, norm_mul, Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg (norm_nonneg _) (norm_nonneg _)]
  generalize (∏ τ, coord w 1 x τ)⁻¹ ^ k = A
  generalize ((‖∏ τ, coord w 1 x τ‖ : ℝ) : ℂ) ^ (-2 * σ) = B
  linear_combination (-(A * B) * (((‖Λ‖ : ℝ) : ℂ) ^ (2 * σ) * ((‖Λ‖ : ℝ) : ℂ) ^ (-2 * σ))) * h1 - (A * B) * h2

theorem hasSum_gTerm [IsTotallyReal F] (𝔞 𝔟 : Frac F) {k : ℕ} (hk : Even k) (σ : ℂ) (w : Emb F → ℂ) (S : ℂ)
    (h : HasSum (eisClass 𝔞 𝔟 k σ w) S) :
    HasSum (fun q : cls (split 𝔞 𝔟 0) ↦ gTerm k σ w 1 q.1.out)
      ((((2 * Real.pi * Complex.I) ^ Module.finrank ℚ F) ^ k *
        ((‖(2 * Real.pi * Complex.I : ℂ) ^ Module.finrank ℚ F‖ : ℝ) : ℂ) ^ (2 * σ)) * S) := by
  have h1 := ((Equiv.hasSum_iff (Equiv.ofBijective _ (bij 𝔞 𝔟))).2 h).mul_left
    (((2 * Real.pi * Complex.I) ^ Module.finrank ℚ F) ^ k *
        ((‖(2 * Real.pi * Complex.I : ℂ) ^ Module.finrank ℚ F‖ : ℝ) : ℂ) ^ (2 * σ))
  have h2 : (fun q : cls (split 𝔞 𝔟 0) ↦ gTerm k σ w 1 q.1.out) = fun q : cls (split 𝔞 𝔟 0) ↦
      (((2 * Real.pi * Complex.I) ^ Module.finrank ℚ F) ^ k *
        ((‖(2 * Real.pi * Complex.I : ℂ) ^ Module.finrank ℚ F‖ : ℝ) : ℂ) ^ (2 * σ)) *
        eisClass 𝔞 𝔟 k σ w (Quotient.mk (latRel 𝔞 𝔟) (pair 𝔞 𝔟 q)) := by
    funext q
    rw [eisClass_mk 𝔞 𝔟 hk, term_eq]
    rfl
  rw [h2]
  exact h1

theorem isGVal_of_isEis : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (k : ℕ) (𝔞 𝔟 : Frac F) (G : (Emb F → ℂ) → ℂ)
    (w : Emb F → ℂ), Even k → IsEis 𝔞 𝔟 k G → w ∈ upperHalf F →
    IsGVal k (split 𝔞 𝔟 0) w 1 (((2 * Real.pi * Complex.I) ^ Module.finrank ℚ F) ^ k * G w) := by
  intro F _ _ _ k 𝔞 𝔟 G w hk hG hw
  constructor
  · intro h2
    have h := hasSum_gTerm 𝔞 𝔟 hk 0 w _ (hG.1 h2 w hw)
    rwa [mul_zero, Complex.cpow_zero, mul_one] at h
  · rintro rfl
    obtain ⟨H, hH, rfl⟩ := hG.2 rfl
    have hn : ((‖(2 * Real.pi * Complex.I : ℂ) ^ Module.finrank ℚ F‖ : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.2 (norm_ne_zero_iff.2 (pow_ne_zero _ Complex.two_pi_I_ne_zero))
    refine ⟨fun σ ↦ (((2 * Real.pi * Complex.I) ^ Module.finrank ℚ F) ^ 2 *
        ((‖(2 * Real.pi * Complex.I : ℂ) ^ Module.finrank ℚ F‖ : ℝ) : ℂ) ^ (2 * σ)) * H σ w, ?_, ?_, ?_⟩
    · have hHd : DifferentiableOn ℂ (fun σ ↦ H σ w) {σ : ℂ | -1 / 2 < σ.re} := hH.2.2 [] w hw
      have hAd : Differentiable ℂ fun σ : ℂ ↦ ((2 * Real.pi * Complex.I) ^ Module.finrank ℚ F) ^ 2 *
          ((‖(2 * Real.pi * Complex.I : ℂ) ^ Module.finrank ℚ F‖ : ℝ) : ℂ) ^ (2 * σ) := fun σ ↦
        (differentiableAt_const _).mul (((differentiableAt_const (2 : ℂ)).mul differentiableAt_id).const_cpow (Or.inl hn))
      exact hAd.differentiableOn.mul hHd
    · intro σ hσ
      obtain ⟨hsm, hHe⟩ := hH.1 σ hσ w hw
      exact hasSum_gTerm 𝔞 𝔟 hk σ w _ (by rw [hHe]; exact hsm.hasSum)
    · simp only [mul_zero, Complex.cpow_zero, mul_one]

end GlobalTheory.HilbFam.EisCmp
end
end

section

open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
open GlobalTheory.LatVal (Sz)
open GlobalTheory.LatJet (EisExp IsEis FR)

namespace GlobalTheory.HilbFam

open NumberField UpperHalfPlane in
open scoped Classical MatrixGroups nonZeroDivisors in
private lemma length_word_eq_sum {I : Type} [Fintype I] (κ : I → ℕ) :
    (_root_.GlobalTheory.HilbFam.word κ).length = ∑ i, κ i := by
  unfold _root_.GlobalTheory.HilbFam.word
  simp [List.length_flatMap, Finset.sum_toList]

open NumberField UpperHalfPlane in
open scoped Classical MatrixGroups nonZeroDivisors in
private lemma lineDeriv_const_mul_comp_smul {I : Type} (f : (I → ℂ) → ℂ) (a c : ℂ)
    (z v : I → ℂ) :
    lineDeriv ℂ (fun z => a * f (c • z)) z v = a * c * lineDeriv ℂ f (c • z) v := by
  simp only [lineDeriv]
  have h : (fun t : ℂ => a * f (c • (z + t • v))) =
      fun t => a * (fun s : ℂ => f (c • z + s • v)) (c * t) := by
    funext t
    simp only [smul_add, smul_smul, mul_comm c t]
  rw [h]
  calc deriv (fun t => a * (fun s : ℂ => f (c • z + s • v)) (c * t)) 0
      = a * deriv (fun t => (fun s : ℂ => f (c • z + s • v)) (c * t)) 0 := by
        rw [deriv_const_mul_field']
    _ = a * (c • deriv (fun s : ℂ => f (c • z + s • v)) (c * 0)) :=
        congrArg (a * ·) (deriv_comp_mul_left c (fun s : ℂ => f (c • z + s • v)) 0)
    _ = a * c * deriv (fun t : ℂ => f (c • z + t • v)) 0 := by
        rw [mul_zero, smul_eq_mul, mul_assoc]

open NumberField UpperHalfPlane in
open scoped Classical MatrixGroups nonZeroDivisors in
private lemma iterD_comp_smul {I : Type} [DecidableEq I] (c : ℂ)
    (u : List I) (f : (I → ℂ) → ℂ) (z : I → ℂ) :
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.iterD u (fun z => f (c • z)) z =
      c ^ u.length * _root_.GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.iterD u f (c • z) := by
  induction u generalizing z with
  | nil => simp [_root_.GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.iterD]
  | cons i u ih =>
    simp only [_root_.GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.iterD, List.foldr_cons] at ih ⊢
    rw [show List.foldr _root_.GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.partialD (fun z => f (c • z)) u =
      fun z => c ^ u.length * List.foldr _root_.GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.partialD f u (c • z) from funext ih]
    unfold _root_.GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.partialD
    rw [lineDeriv_const_mul_comp_smul, List.length_cons, pow_succ]

open NumberField UpperHalfPlane in
open scoped Classical MatrixGroups nonZeroDivisors in
private lemma jet_mul_eq_pow_sum_mul {F : Type} [Field F] [NumberField F] (k : ℕ)
    (L : _root_.GlobalTheory.HilbFam.Lat F) (κ : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F → ℕ) (τ c t lam : ℂ) :
    _root_.GlobalTheory.HilbFam.jet k L κ τ (lam * c) (lam * t) =
      lam ^ (∑ i, κ i) * _root_.GlobalTheory.HilbFam.jet k L κ τ c t := by
  unfold _root_.GlobalTheory.HilbFam.jet
  rw [← length_word_eq_sum κ, ← smul_zero lam,
    ← iterD_comp_smul]
  congr 1
  · funext z
    simp only [Pi.smul_apply, smul_eq_mul]
    congr 2 <;> funext i <;> ring
  · exact smul_zero lam


open NumberField UpperHalfPlane in
open scoped Classical MatrixGroups nonZeroDivisors in
theorem _root_.GlobalTheory.HilbFam.hfun_slash : _root_.GlobalTheory.LatJet.EisExp → ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F], 2 ≤ Module.finrank ℚ F → ∀ (s N : ℕ) (L : _root_.GlobalTheory.HilbFam.Lat F), 1 ≤ s → 0 < N → _root_.GlobalTheory.HilbFam.HasLevel N L → ∀ (κ : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F → ℕ) (γ : SL(2, ℤ)) (Ch Ch' : ℍ → ℂ) (τ : ℍ), (∃ L', _root_.GlobalTheory.HilbFam.HasLevel N L' ∧ L' = _root_.GlobalTheory.HilbFam.mulMat L (γ : Matrix (Fin 2) (Fin 2) ℤ)) → Ch (γ • τ) = (((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 * (τ : ℂ) + (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1) : ℂ) ^ 2 * Ch' τ - ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℂ) * ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 * (τ : ℂ) + (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1) / (2 * Real.pi * Complex.I) → _root_.GlobalTheory.HilbFam.hfun (2 * s) L κ Ch (γ • τ) = (((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 * (τ : ℂ) + (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1) : ℂ) ^ _root_.GlobalTheory.HilbFam.wt (2 * s) κ * _root_.GlobalTheory.HilbFam.hfun (2 * s) (_root_.GlobalTheory.HilbFam.mulMat L (γ : Matrix (Fin 2) (Fin 2) ℤ)) κ Ch' τ := by
  intro _ F _ _ _ _ s N L _ _ _ κ γ Ch Ch' τ _ hCh
  have hP : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  simp only [_root_.GlobalTheory.HilbFam.hfun]
  rw [_root_.GlobalTheory.HilbFam.JetModular.jet_smul F (2 * s) L κ γ τ _ _ (even_two_mul s)]
  set j : ℂ := ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 * (τ : ℂ) + (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1) with hj
  set P : ℂ := 2 * Real.pi * Complex.I with hPdef
  have hc : P ^ 2 * Ch (γ • τ) - -P * ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℂ) * j =
      j ^ 2 * (P ^ 2 * Ch' τ) := by
    rw [hCh]
    field_simp
    ring
  rw [hc, show -P * j ^ 2 = j ^ 2 * -P by ring, jet_mul_eq_pow_sum_mul,
    _root_.GlobalTheory.HilbFam.wt, ← pow_mul, pow_add j]
  ring

end GlobalTheory.HilbFam
end

section

open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors

namespace GlobalTheory.HilbFam

theorem hasSum_iterD_gval_split : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (k : ℕ) (𝔞 𝔟 : Frac F) (a₀ : ℂ) (a : F → ℂ) (x : F) (τ c t : ℂ) (u : List (Emb F)), Even k → IsCoef k 𝔞 𝔟 a₀ a → 0 < τ.im → HasSum (fun ξ : F ↦ a ξ * eTr (ξ * x) * Complex.exp ((2 * Real.pi * Complex.I) * ((Algebra.trace ℚ F ξ : ℚ) : ℂ) * τ) * ∏ i : Emb F, lag k (u.count i) c ((2 * Real.pi * Complex.I) * (i ξ : ℂ) * t)) (iterD u (fun z ↦ (cK F k : ℂ) * gval k (split 𝔞 𝔟 x) (fun i ↦ τ + z i * (c * τ + t)) (fun i ↦ 1 + z i * c)) 0 / ((2 * Real.pi * Complex.I) ^ Module.finrank ℚ F * (omegaFactor 𝔞 : ℂ)) ^ k) := by
  intro F _ _ _ k 𝔞 𝔟 a₀ a x τ c t u hk ha hτ
  obtain ⟨r, hr, hrad⟩ := GlobalTheory.T.exists_radius_moebius_perturbation_upperHalfPlane τ c t hτ
  obtain ⟨M, hM, hbd⟩ := GlobalTheory.T.exists_summable_bound_hilbert_eisenstein_terms F k 𝔞 𝔟 a₀ a x τ c t ha hτ
  set D : ℂ := ((2 * Real.pi * Complex.I) ^ Module.finrank ℚ F * (omegaFactor 𝔞 : ℂ)) ^ k with hD
  set G : (Emb F → ℂ) → ℂ := fun z ↦ (cK F k : ℂ) * gval k (split 𝔞 𝔟 x) (fun i ↦ τ + z i * (c * τ + t)) (fun i ↦ 1 + z i * c) with hG
  have hcoord : ∀ z ∈ Metric.ball (0 : Emb F → ℂ) r, ∀ i, ‖z i‖ < r := fun z hz i ↦
    (norm_le_pi_norm z i).trans_lt (mem_ball_zero_iff.1 hz)
  have hne : ∀ w : ℂ, ‖w‖ < r → 1 + w * c ≠ 0 := fun w hw h ↦ by
    have := (hrad w hw).1
    rw [h, norm_zero] at this
    linarith
  have hψ : ∀ y : ℂ, DifferentiableOn ℂ (fun w : ℂ ↦ (1 + w * c)⁻¹ ^ k * Complex.exp (y * w / (1 + w * c))) (Metric.ball 0 r) := by
    intro y w hw
    have h0 := hne w (mem_ball_zero_iff.1 hw)
    have h1 : DifferentiableAt ℂ (fun w : ℂ ↦ 1 + w * c) w := by fun_prop
    have h2 : DifferentiableAt ℂ (fun w : ℂ ↦ y * w) w := by fun_prop
    exact (((h1.inv h0).pow k).mul (h2.div h1 h0).cexp).differentiableWithinAt
  have key := GlobalTheory.T.hasSum_iteratedComplexPartialDeriv_termwise (Emb F) F u r
    (fun ξ z ↦ a ξ * eTr (ξ * x) * Complex.exp ((2 * Real.pi * Complex.I) * ((Algebra.trace ℚ F ξ : ℚ) : ℂ) * τ) * ∏ i : Emb F, ((1 + z i * c)⁻¹ ^ k * Complex.exp ((2 * Real.pi * Complex.I) * (i ξ : ℂ) * t * z i / (1 + z i * c))))
    (fun z ↦ D⁻¹ * G z) M hr hM
    (fun ξ z hz ↦ by
      refine (DifferentiableAt.const_mul ?_ _).differentiableWithinAt
      refine (HasFDerivAt.finsetProd (𝕜 := ℂ) (u := (Finset.univ : Finset (Emb F)))
        (g := fun i (z : Emb F → ℂ) ↦ (1 + z i * c)⁻¹ ^ k * Complex.exp ((2 * Real.pi * Complex.I) * (i ξ : ℂ) * t * z i / (1 + z i * c)))
        (fun i _ ↦ DifferentiableAt.hasFDerivAt ?_)).differentiableAt
      have h1 := ((hψ ((2 * Real.pi * Complex.I) * (i ξ : ℂ) * t)).differentiableAt
        (Metric.isOpen_ball.mem_nhds (mem_ball_zero_iff.2 (hcoord z hz i))))
      exact h1.comp z (differentiableAt_apply (𝕜 := ℂ) i z))
    (fun ξ z hz ↦ hbd ξ z (fun i ↦ hrad _ (hcoord z hz i)))
    (fun z hz ↦ by
      have := GlobalTheory.T.hasSum_hilbertEisenstein_movedPoint F k 𝔞 𝔟 a₀ a x τ c t z hk ha (fun i ↦ ⟨hne _ (hcoord z hz i), by
        have := (hrad _ (hcoord z hz i)).2
        linarith⟩)
      rw [div_eq_inv_mul] at this
      exact this)
  have hc := GlobalTheory.T.iteratedPartialDeriv_const_mul_reindex (Emb F) (Emb F) (Equiv.refl _) u G D⁻¹ 0
  simp only [Equiv.refl_symm, Equiv.coe_refl, id_eq, List.map_id, List.map_id_fun] at hc
  have hc' : iterD u (fun z ↦ D⁻¹ * G z) 0 = iterD u G 0 / D := by
    rw [div_eq_inv_mul]; exact hc
  rw [hc'] at key
  convert key using 2 with ξ
  have := GlobalTheory.T.iteratedPartialDeriv_prod_oneVar_at_zero (Emb F) u r
    (fun i w ↦ (1 + w * c)⁻¹ ^ k * Complex.exp ((2 * Real.pi * Complex.I) * (i ξ : ℂ) * t * w / (1 + w * c)))
    (a ξ * eTr (ξ * x) * Complex.exp ((2 * Real.pi * Complex.I) * ((Algebra.trace ℚ F ξ : ℚ) : ℂ) * τ)) hr
    (fun i ↦ hψ _)
  rw [this]
  congr 1
  exact Finset.prod_congr rfl (fun i _ ↦ (GlobalTheory.T.iteratedDeriv_zero_eq_laguerreDerivativePolynomialValue k _ c _).symm)

end GlobalTheory.HilbFam
end

section

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu

namespace GlobalTheory.Dieu

theorem surjective_iff_finrank_quot_kerIdeal_eq_one :
    ∀ (k : Type) [Field k] (A : Type) [CommRing A] [HopfAlgebra k A] [IsCocomm k A]
      [Module.Finite k A] (C : Type) [CommRing C] [HopfAlgebra k C] [IsCocomm k C]
      [Module.Finite k C] (f : C →ₐc[k] A),
      Function.Surjective f ↔ Module.finrank k (A ⧸ kerIdeal f) = 1 := by
  intro k _ A _ _ _ _ C _ _ _ _ f
  constructor
  · intro hf
    rw [kerIdeal_of_surjective hf]
    have hs : Function.Surjective (counitAlgHom k A) := fun c =>
      ⟨algebraMap k A c, by simp⟩
    let e : (A ⧸ augIdeal (R := k) (A := A)) ≃ₐ[k] k := Ideal.quotientKerAlgEquivOfSurjective hs
    rw [e.toLinearEquiv.finrank_eq, Module.finrank_self]
  · intro h
    have hL := GlobalTheory.T.finrank_hopfAlgebra_eq_range_mul_kernel k A C f
    rw [h, mul_one] at hL
    have htop : LinearMap.range (f : C →ₐ[k] A).toLinearMap = ⊤ :=
      Submodule.eq_top_of_finrank_eq hL.symm
    intro a
    have ha : a ∈ LinearMap.range (f : C →ₐ[k] A).toLinearMap := htop ▸ Submodule.mem_top
    obtain ⟨c, hc⟩ := ha
    exact ⟨c, hc⟩

end GlobalTheory.Dieu
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC.RedUnit

theorem res_map {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U) (y : Sec F U) :
    Sec.res g (Sec.map φ y) = Sec.map φ (Sec.res g y) := by
  have := congrArg (fun f => f.hom y) (φ.hom.naturality g.op)
  exact this.symm

theorem res_resGen {q : ℕ} [NeZero q] (i : ℤ) {V U : Scheme.{0}} (g : V ⟶ U) (ζ : Prim q Γ(U, ⊤)) :
    Sec.res g (resGen i ζ) = resGen i (ζ.map g.appTop.hom) := by
  unfold resGen
  rw [res_map, (GlobalTheory.T.tateTwist_sections_locally_generated q i).2.2.2.1 V U g ζ]

theorem val_one_smul {q : ℕ} [NeZero q] {M : Type*} [AddCommGroup M] [Module (ULift.{1} (ZMod q)) M] (y : M) :
    (1 : ZMod q).val • y = y := by
  by_cases hq : q = 1
  · subst hq
    have : Subsingleton M := Module.subsingleton (ULift.{1} (ZMod 1)) M
    exact Subsingleton.elim _ _
  · haveI : Fact (1 < q) := ⟨by have := NeZero.ne q; omega⟩
    rw [ZMod.val_one, one_smul]

theorem resGen_zero_eq {q : ℕ} [NeZero q] {U : Scheme.{0}} (ζ ξ : Prim q Γ(U, ⊤)) : resGen 0 ζ = resGen 0 ξ := by
  apply (GlobalTheory.T.etaleSheafSections_ext_and_glue _ _ U).1
  obtain ⟨S, hS, hP⟩ := (GlobalTheory.T.etaleLocal_primitiveRoot_and_roots_of_unity q U).2.1 ζ ξ
  refine ⟨S, hS, fun W h hh => ?_⟩
  obtain ⟨a, ha⟩ := hP W h hh
  rw [res_resGen, res_resGen]
  have := (GlobalTheory.T.tateTwist_sections_locally_generated q 0).2.2.2.2.1 W (ζ.map h.appTop.hom) (ξ.map h.appTop.hom) a ha
  unfold resGen
  rw [this, zpow_zero, Units.val_one, val_one_smul]

end GlobalTheory.EtC.RedUnit

theorem GlobalTheory.EtC.red_one : ∀ (Q q : ℕ) [NeZero Q], q ∣ Q → ∀ E : Spc, Inv Q E → red Q q E 0 0 (one Q E) = one q E := by
  intro Q q _ hqQ E hE
  haveI : NeZero q := ⟨fun h => by subst h; exact NeZero.ne Q (Nat.eq_zero_of_zero_dvd hqQ)⟩
  have hEq : Inv q E := fun U hU => by
    obtain ⟨k, hk⟩ := hqQ
    have := hE U hU
    rw [hk, Nat.cast_mul] at this
    exact isUnit_of_mul_isUnit_left this
  obtain ⟨α, hα1, hα2⟩ := (GlobalTheory.T.tateTwistUnitClass_rootClass_spec Q).1 E hE
  obtain ⟨β, hβ⟩ := (GlobalTheory.T.exists_image_cocycle_semilinearSheafComplexMap _ _ (redMap Q q 0)).1 E 0 α
  have hred : red Q q E 0 0 (one Q E) = CohomologyClass.mk β := by
    rw [← hα1]; exact (GlobalTheory.T.exists_image_cocycle_semilinearSheafComplexMap _ _ (redMap Q q 0)).2 E 0 α β hβ
  rw [hred]
  refine (GlobalTheory.T.tateTwistUnitClass_rootClass_spec q).2.1 E hEq β fun U x ξ => ?_
  apply (GlobalTheory.T.etaleSheafSections_ext_and_glue _ _ U).1
  obtain ⟨S, hS, hP⟩ := (GlobalTheory.T.etaleLocal_primitiveRoot_and_roots_of_unity Q U).1 (hE U ⟨x⟩)
  refine ⟨S, hS, fun V g hg => ?_⟩
  obtain ⟨ζ⟩ := hP V g hg
  obtain ⟨ξ', hξ'⟩ := (GlobalTheory.T.primitiveRoot_pow_unit_sub_prod_properties Q Γ(V, ⊤)).2.2.2.2.2 q hqQ ζ
  rw [(GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties (ZMod q)).2.1 β.1 0 0 _ V U g x, hβ 0 0 _ V (x.res g), hα2 V (x.res g) ζ,
    GlobalTheory.T.tateTwistReductionResolutionMap_generator Q q hqQ 0 V ζ ξ' hξ', RedUnit.res_resGen]
  exact RedUnit.resGen_zero_eq _ _
end

section

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open NumberField GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.LatVal ReciprocityTheory.ChartRestriction.L1 Formalism.L2.Th1.F
open GlobalTheory.CMVal GlobalTheory.HeckeGal
open ModularForm (E₄ E₆)

theorem _root_.GlobalTheory.T.galois_transport_second_eisenstein_cm : ∀ (K : Type) [Field K] [NumberField K] (d : ℕ) (δ : K) (ι : K →+* ℂ) (g : ℂ ≃+* ℂ) (t : (Af K)ˣ) (Λ₀ Λ₁ : PeriodPair) (Ω₀ Ω₁ : ℂ), 0 < d → δ ^ 2 = -(d : K) → TorsTransport ι g t Λ₀ Λ₁ Ω₀ Ω₁ → g (s2 Λ₀ / Ω₀ ^ 2) = s2 Λ₁ / Ω₁ ^ 2 := by
  first | exact @GlobalTheory.NormSqOfSquareEqNeg.main | exact GlobalTheory.NormSqOfSquareEqNeg.main | (intros; apply GlobalTheory.NormSqOfSquareEqNeg.main <;> assumption)
end
