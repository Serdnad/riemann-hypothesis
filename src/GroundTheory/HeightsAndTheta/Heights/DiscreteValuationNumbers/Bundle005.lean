module

public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle003
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.BundleObjects
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.RingTheory.MvPolynomial.Localization
public import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

section SlopeTestRemainingChoices

variable {K : Type*} {ι : K → Type*} {R : Type*} [CommRing R]

theorem cycEval_eq_add_mul_of_cycle (φ : Ideal (MRing ι R) → ℤ) {Z₀ Z₁ Z₂ : Ideal (MRing ι R) → ℤ}
    (k : ℤ) (h₀ : (Function.support Z₀).Finite) (h₂ : (Function.support Z₂).Finite)
    (h : ∀ W, Z₁ W = Z₀ W + k * Z₂ W) :
    cycEval φ Z₁ = cycEval φ Z₀ + k * cycEval φ Z₂ := by
  unfold cycEval
  have f₀ : (Function.support fun W => Z₀ W * φ W).Finite :=
    h₀.subset fun W hW h0 => hW (by simp [h0])
  have f₂ : (Function.support fun W => k * (Z₂ W * φ W)).Finite :=
    h₂.subset fun W hW h0 => hW (by simp [h0])
  rw [mul_finsum, ← finsum_add_distrib f₀ f₂]
  refine finsum_congr fun W => ?_
  rw [h W]
  ring

theorem cycEval_eq_add_mul_of_fun {φ₀ φ₁ φ₂ : Ideal (MRing ι R) → ℤ} {Z : Ideal (MRing ι R) → ℤ}
    (k : ℤ) (hZ : (Function.support Z).Finite) (h : ∀ W, Z W ≠ 0 → φ₁ W = φ₀ W + k * φ₂ W) :
    cycEval φ₁ Z = cycEval φ₀ Z + k * cycEval φ₂ Z := by
  unfold cycEval
  have f₀ : (Function.support fun W => Z W * φ₀ W).Finite :=
    hZ.subset fun W hW h0 => hW (by simp [h0])
  have f₂ : (Function.support fun W => k * (Z W * φ₂ W)).Finite :=
    hZ.subset fun W hW h0 => hW (by simp [h0])
  rw [mul_finsum, ← finsum_add_distrib f₀ f₂]
  refine finsum_congr fun W => ?_
  by_cases hW : Z W = 0
  · simp [hW]
  · rw [h W hW]
    ring

end SlopeTestRemainingChoices

section VNum

variable {K : Type*} [DecidableEq K] {ι : K → Type*}
variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

theorem vNum_vecCons_zero (W : Ideal (MRing ι O)) {d : ℕ} (L : Fin d → K → ℤ) :
    vNum W (Matrix.vecCons (0 : K → ℤ) L) = 0 := by
  unfold vNum intNum
  have hm : mixedDiff (Matrix.vecCons (0 : K → ℤ) L) (hilbFn (specialIdeal W)) = fun _ => 0 := by
    funext m
    simp [mixedDiff, List.ofFn_succ, diffStep]
  rw [hm]
  unfold eventualValue
  have hex : ∃ c, ∀ᶠ m in Filter.atTop, (fun _ : K → ℤ => (0 : ℤ)) m = c :=
    ⟨0, Filter.Eventually.of_forall fun _ => rfl⟩
  rw [dite_eq_left hex]
  obtain ⟨m, hm'⟩ := hex.choose_spec.exists
  exact hm'.symm

end VNum

theorem ShiftByUniformiser.proof (h₁ : DivCycleMul.Statement.{u})
    (h₂ : DivCycleFiniteSupport.Statement.{u}) : ShiftByUniformiser.Statement.{u} := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ P d hP b f g hD c s _ hsP hH L n hI₁ hI₂
  have hfin : ∀ (Q : Ideal (MRing ι O)) (x : MRing ι O), (Function.support (divCycle Q x)).Finite :=
    fun Q x => h₂ O K ι Q x
  have hrat : ∀ (Q : Ideal (MRing ι O)) (x y : MRing ι O), (Function.support (ratDiv Q x y)).Finite :=
    fun Q x y => ((hfin Q x).union (hfin Q y)).subset fun W hW => by
      by_contra hc
      simp only [Set.mem_union, Function.mem_support, not_or, not_not] at hc
      exact hW (by simp [ratDiv, hc.1, hc.2])

  have hpow : ∀ (Q : Ideal (MRing ι O)), Q.IsPrime → (C ϖ : MRing ι O) ∉ Q → f ∉ Q → ∀ m : ℕ,
      ∀ W, divCycle Q (C ϖ ^ m * f) W = divCycle Q f W + m * divCycle Q (C ϖ) W := by
    intro Q hQ hϖQ hfQ m
    induction m with
    | zero => intro W; simp
    | succ m ih =>
      intro W
      have hm : C ϖ ^ m * f ∉ Q := fun h =>
        (hQ.mem_or_mem h).elim (fun h' => hϖQ (hQ.mem_of_pow_mem _ h')) hfQ
      have e : (C ϖ : MRing ι O) ^ (m + 1) * f = C ϖ * (C ϖ ^ m * f) := by ring
      rw [e, congrFun (h₁ O K ι Q (C ϖ) (C ϖ ^ m * f) hQ hϖQ hm) W, Pi.add_apply, ih W]
      push_cast
      ring
  have hshift : ∀ (Q : Ideal (MRing ι O)), Q.IsPrime → (C ϖ : MRing ι O) ∉ Q → f ∉ Q → ∀ W,
      ratDiv Q (C ϖ ^ n * f) g W = ratDiv Q f g W + (n : ℤ) * ratDiv Q (C ϖ) 1 W := by
    intro Q hQ hϖQ hfQ W
    simp only [ratDiv, divCycle_one, sub_zero]
    rw [hpow Q hQ hϖQ hfQ n W]
    ring
  have hPp : P.IsPrime := hP.multiProj.isPrime
  have hϖP : (C ϖ : MRing ι O) ∉ P := by
    intro h
    have h' : ϖ ∈ P.comap (C : O →+* MRing ι O) := h
    rw [hP.noTorsion, Ideal.mem_bot] at h'
    exact hϖ.ne_zero h'
  unfold cutIdentity at hI₁ hI₂ ⊢
  rw [cycEval_eq_add_mul_of_cycle _ (n : ℤ) (hrat P f g) (hrat P (C ϖ) 1)
      (hshift P hPp hϖP hD.num_not_mem)] at hI₁
  classical
  have hR : cycEval (fun W => if (C ϖ : MRing ι O) ∈ W then vNum W (Matrix.vecCons b L)
        else cycEval (fun G => vNum G L) (ratDiv W (C ϖ ^ n * f) g)) (divCycle P s) =
      cycEval (fun W => if (C ϖ : MRing ι O) ∈ W then vNum W (Matrix.vecCons b L)
        else cycEval (fun G => vNum G L) (ratDiv W f g)) (divCycle P s) +
      (n : ℤ) * cycEval (fun W => if (C ϖ : MRing ι O) ∈ W then vNum W (Matrix.vecCons (0 : K → ℤ) L)
        else cycEval (fun G => vNum G L) (ratDiv W (C ϖ) 1)) (divCycle P s) := by
    refine cycEval_eq_add_mul_of_fun (n : ℤ) (hfin P s) fun W hW => ?_
    by_cases hϖW : (C ϖ : MRing ι O) ∈ W
    · simp only [if_pos hϖW, vNum_vecCons_zero]
      ring
    · simp only [if_neg hϖW]
      have hV := hH W hW hϖW
      have hWp : W.IsPrime := by
        unfold divCycle at hW
        split_ifs at hW with hm
        · exact hm.1.1.1
        · exact absurd rfl hW
      exact cycEval_eq_add_mul_of_cycle _ (n : ℤ) (hrat W f g) (hrat W (C ϖ) 1)
        (hshift W hWp hϖW hV.num_not_mem)
  rw [hR, hI₂] at hI₁
  linarith

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

theorem weightedHomogeneousComponent_map {σ M R S : Type*} [AddCommMonoid M] [CommRing R]
    [CommRing S] (φ : R →+* S) (w : σ → M) (n : M) (p : MvPolynomial σ R) :
    weightedHomogeneousComponent w n (MvPolynomial.map φ p) =
      MvPolynomial.map φ (weightedHomogeneousComponent w n p) := by
  classical
  ext d
  rw [coeff_weightedHomogeneousComponent, coeff_map, coeff_map,
    coeff_weightedHomogeneousComponent]
  split_ifs <;> simp

attribute [local instance] MvPolynomial.algebraMvPolynomial

theorem GenericFibProps.proof : GenericFibProps.Statement := by
  intro O _ _ _ K _ _ ι _ P hP hT
  set φ := algebraMap O (FractionRing O) with hφ
  let M : Submonoid (MRing ι O) := (nonZeroDivisors O).map (C (σ := Σ k, ι k))
  have : IsLocalization M (MRing ι (FractionRing O)) :=
    MvPolynomial.isLocalization (nonZeroDivisors O) (FractionRing O)
  have hmap : algebraMap (MRing ι O) (MRing ι (FractionRing O)) = MvPolynomial.map φ := rfl
  have hdisj : Disjoint (M : Set (MRing ι O)) P := by
    rw [Set.disjoint_left]
    rintro _ ⟨m, hm, rfl⟩ hmP
    have : m ∈ P.comap (C : O →+* MRing ι O) := hmP
    rw [hT, Ideal.mem_bot] at this
    exact nonZeroDivisors.ne_zero hm this
  have hgen : genFib P = Ideal.map (algebraMap (MRing ι O) (MRing ι (FractionRing O))) P := rfl
  have hprime : (genFib P).IsPrime :=
    hgen ▸ IsLocalization.isPrime_of_isPrime_disjoint M _ P hP.isPrime hdisj
  have hunder : (genFib P).comap (MvPolynomial.map φ) = P :=
    IsLocalization.under_map_of_isPrime_disjoint M (MRing ι (FractionRing O)) hP.isPrime hdisj
  refine ⟨hprime, ?_, ?_⟩
  · intro x hx b
    rw [hgen, IsLocalization.mem_map_algebraMap_iff M] at hx
    obtain ⟨⟨⟨p, hp⟩, ⟨_, ⟨m, hm, rfl⟩⟩⟩, h⟩ := hx
    simp only [hmap, map_C] at h
    have hm0 : φ m ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hm
    have hx' : x = C (φ m)⁻¹ * MvPolynomial.map φ p := by
      rw [← h, mul_comm x, ← mul_assoc, ← C_mul, inv_mul_cancel₀ hm0, C_1, one_mul]
    rw [hx', weightedHomogeneousComponent_C_mul, weightedHomogeneousComponent_map]
    exact Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ (hP.multiHomog p hp b))
  · intro s c hs hsP
    refine ⟨?_, ?_⟩
    · intro d hd
      apply hs
      intro h0
      rw [coeff_map, h0, map_zero] at hd
      exact hd rfl
    · intro h
      apply hsP
      rw [← hunder]
      exact h

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

attribute [local instance] MvPolynomial.weightedGradedAlgebra


open scoped Classical in
theorem isHomogeneous_of_isMultiHomogIdeal' {K : Type*} [DecidableEq K] {ι : K → Type*}
    {R : Type*} [CommRing R] {I : Ideal (MRing ι R)} (hI : IsMultiHomogIdeal I) :
    (by
      classical
      exact I.IsHomogeneous (weightedHomogeneousSubmodule R (blockWeight ι))) := by
  classical
  have e : I = Ideal.span
      {g | ∃ f ∈ I, ∃ b, g = weightedHomogeneousComponent (blockWeight ι) b f} := by
    apply le_antisymm
    · intro f hf
      rw [← sum_weightedHomogeneousComponent (blockWeight ι) f,
        finsum_eq_sum _ (weightedHomogeneousComponent_finsupp f)]
      exact Ideal.sum_mem _ fun b _ => Ideal.subset_span ⟨f, hf, b, rfl⟩
    · rw [Ideal.span_le]
      rintro g ⟨f, hf, b, rfl⟩
      exact hI f hf b
  rw [e]
  refine Ideal.homogeneous_span _ _ fun x hx => ?_
  obtain ⟨f, -, b, rfl⟩ := hx
  exact ⟨b, weightedHomogeneousComponent_isWeightedHomogeneous b f⟩

theorem SupSpanMultiHomog.proof : SupSpanMultiHomog.Statement := by
  classical
  intro R _ K _ ι I x e hI hx
  have h1 := isHomogeneous_of_isMultiHomogIdeal' hI
  have h2 : (Ideal.span {x}).IsHomogeneous (weightedHomogeneousSubmodule R (blockWeight ι)) :=
    Ideal.homogeneous_span _ _ (by
      rintro y rfl
      exact ⟨e, hx⟩)
  have h := h1.sup h2
  intro f hf b
  exact weightedHomogeneousComponent_mem_of_mem R (blockWeight ι) h hf b

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

section Defs

variable {K : Type*} {ι : K → Type*}
variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

def commonExcess (ϖ : O) (P : Ideal (MRing ι O)) (f g s : MRing ι O) : ℕ :=
  ⨆ G : {G : Ideal (MRing ι O) // (C ϖ : MRing ι O) ∈ G}, (divCycle P s G.1 * ratDiv P f g G.1).toNat

end Defs

section Lemmas

def NoCommonComponentCase.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (P : Ideal (MRing ι O)) (d : ℕ), IsModelOver P (d + 1) →
    ∀ (b : K → ℤ) (f g : MRing ι O), IsEffectiveVertical P ϖ b f g →
    ∀ (c : K → ℕ) (s : MRing ι O), IsMultiHomog s c → s ∉ P →
    (∀ H, divCycle P s H ≠ 0 → (C ϖ : MRing ι O) ∉ H → IsVerticalDivisor H ϖ b f g) →
    (∀ G, (C ϖ : MRing ι O) ∈ G → divCycle P s G ≠ 0 → ratDiv P f g G = 0) →
    ∀ L : Fin d → K → ℤ, cutIdentity ϖ P b f g c s L

def CommonFactorInduction.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (P : Ideal (MRing ι O)) (d : ℕ), IsModelOver P (d + 1) →
    ∀ (b : K → ℤ) (f g : MRing ι O), IsEffectiveVertical P ϖ b f g →
    ∀ (c : K → ℕ) (s : MRing ι O), IsMultiHomog s c → s ∉ P →
    (∀ H, divCycle P s H ≠ 0 → (C ϖ : MRing ι O) ∉ H → IsVerticalDivisor H ϖ b f g) →
    (∃ G, (C ϖ : MRing ι O) ∈ G ∧ divCycle P s G ≠ 0 ∧ ratDiv P f g G ≠ 0) →
    (∀ (K' : Type) [Fintype K'] [DecidableEq K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
      (P' : Ideal (MRing ι' O)) (d' : ℕ), IsModelOver P' (d' + 1) →
      ∀ (b' : K' → ℤ) (f' g' : MRing ι' O), IsEffectiveVertical P' ϖ b' f' g' →
      ∀ (c' : K' → ℕ) (s' : MRing ι' O), IsMultiHomog s' c' → s' ∉ P' →
      (∀ H, divCycle P' s' H ≠ 0 → (C ϖ : MRing ι' O) ∉ H → IsVerticalDivisor H ϖ b' f' g') →
      commonExcess ϖ P' f' g' s' < commonExcess ϖ P f g s →
      ∀ L' : Fin d' → K' → ℤ, cutIdentity ϖ P' b' f' g' c' s' L') →
    ∀ L : Fin d → K → ℤ, cutIdentity ϖ P b f g c s L

end Lemmas

section Examples

end Examples

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

theorem SpecialQuotDim.proof : SpecialQuotDim.Statement := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ W hW
  let π : MRing ι O →+* MRing ι (IsLocalRing.ResidueField O) :=
    MvPolynomial.map (IsLocalRing.residue O)
  have hsurj : Function.Surjective π :=
    MvPolynomial.map_surjective _ IsLocalRing.residue_surjective
  have hker : RingHom.ker π ≤ W := by
    change RingHom.ker (MvPolynomial.map (IsLocalRing.residue O)) ≤ W
    rw [MvPolynomial.ker_map, IsLocalRing.ker_residue,
      (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ, Ideal.map_span,
      Set.image_singleton, Ideal.span_le, Set.singleton_subset_iff]
    exact hW
  have hcomap : (specialIdeal W).comap π = W := by
    change (W.map π).comap π = W
    rw [Ideal.comap_map_of_surjective' _ hsurj, sup_eq_left.2 hker]
  let f := (Ideal.Quotient.mk (specialIdeal W)).comp π
  have hf : Function.Surjective f := Ideal.Quotient.mk_surjective.comp hsurj
  have hkf : RingHom.ker f = W := by
    ext x
    change Ideal.Quotient.mk _ (π x) = 0 ↔ x ∈ W
    rw [Ideal.Quotient.eq_zero_iff_mem, ← Ideal.mem_comap, hcomap]
  exact (ringKrullDim_eq_of_ringEquiv
    ((Ideal.quotEquivOfEq hkf.symm).trans (RingHom.quotientKerEquivOfSurjective hf))).symm

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

universe u

theorem DivCycleFiniteSupport.proof : DivCycleFiniteSupport.Statement.{u} := by
  intro R _ _ K _ ι _ P f
  apply Set.Finite.subset (Ideal.finite_minimalPrimes_of_isNoetherianRing _ (P ⊔ Ideal.span {f}))
  intro W hW
  by_contra hmin
  apply hW
  unfold divCycle
  rw [dite_eq_right]
  exact fun h => hmin h.1

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

def PairNumberRelabel.Statement : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O)
    (K₁ : Type) [Fintype K₁] [DecidableEq K₁] (ι₁ : K₁ → Type) [∀ k, Fintype (ι₁ k)]
    (K₂ : Type) [Fintype K₂] [DecidableEq K₂] (ι₂ : K₂ → Type) [∀ k, Fintype (ι₂ k)]
    (e : K₁ ≃ K₂) (σ : (Σ k, ι₁ k) ≃ (Σ k, ι₂ k)), (∀ v, (σ v).1 = e v.1) →
    ∀ P : Ideal (MRing ι₁ O),
      (∀ d : ℕ, IsModelOver P d → IsModelOver (P.map (rename σ)) d) ∧
      (∀ (b : K₂ → ℤ) (f g : MRing ι₁ O), IsVerticalDivisor P ϖ (b ∘ e) f g →
        IsVerticalDivisor (P.map (rename σ)) ϖ b (rename σ f) (rename σ g)) ∧
      (∀ (n : ℕ) (x x' : Fin n → K₂ → ℤ) (f g : Fin n → MRing ι₁ O)
        (Gs : Fin n → MvPolynomial (Fin n ⊕ Fin n) ℤ) (Q : List (K₂ → ℤ)),
        pairNum (P.map (rename σ)) x x' (fun i => rename σ (f i)) (fun i => rename σ (g i)) Gs Q =
          pairNum P (fun i => x i ∘ e) (fun i => x' i ∘ e) f g Gs (Q.map (· ∘ e)))

section Examples

end Examples

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

def PointIdealMultiProj.Statement : Prop :=
  ∀ (F : Type) [Field F] (L : Type) [Field L] [Algebra F L]
    (K : Type) [DecidableEq K] (ι : K → Type) (z : (Σ k, ι k) → L),
    (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → IsMultiProjPrime (pointIdeal F z)

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

def VerticalDivisorJoinPullback.Statement : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O)
    (Ω : Type) [Field Ω] [Algebra O Ω]
    (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (K' : Type) [Fintype K'] [DecidableEq K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (y : (Σ k, ι k) → Ω) (y' : (Σ k, ι' k) → Ω) (b : K → ℤ) (f g : MRing ι O),
    IsVerticalDivisor (pointIdeal O y) ϖ b f g →
      IsVerticalDivisor (pointIdeal O (joinCoords y y')) ϖ (joinDeg b) (joinForm f) (joinForm g)

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end
