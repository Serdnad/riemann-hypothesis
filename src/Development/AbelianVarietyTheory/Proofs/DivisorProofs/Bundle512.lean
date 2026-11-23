module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ToBaseChangePtsBijective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle411
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle010
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralInvariantDerivationLog
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferentialOperatorDepthLeDividedPowerContent
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle002
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsUniqueLbIsoPullEqOfCoheightLeOne
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
public import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
import Aesop.Main
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsLocallyConstantModulus
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsUnitarisableOfCharIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle464
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle032
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle356
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle355
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle239
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle466
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
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
import Mathlib.Dynamics.Ergodic.Action.Regular
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle401
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle457
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.PtOrderProdSub
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle065

@[expose] public section

section

open Matrix MeasureTheory ValuativeRel GlobalTheory.SplitFlip GlobalTheory.SmGL GlobalTheory.WeilM GlobalTheory.RankFibre GlobalTheory.SplitWeil GlobalTheory.RankFibreKer
open scoped Pointwise

namespace GlobalTheory.HaarCosetSum

theorem integral_eq_vol_mul_sum_of_cosets :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (a : ℕ) (K : Subgroup (GL (Fin a) k)),
    IsOpen (K : Set (GL (Fin a) k)) → K ≤ KO k (Fin a) → ∀ F : GL (Fin a) k → ℂ,
    (∀ g x, x ∈ K → F (g * x) = F g) → ∀ R : Finset (GL (Fin a) k),
    (∀ r ∈ R, ∀ r' ∈ R, r⁻¹ * r' ∈ K → r = r') → (∀ g, F g ≠ 0 → ∃ r ∈ R, r⁻¹ * g ∈ K) →
    ∫ g, F g ∂(haarVol (KO k (Fin a))) = ((haarVol (KO k (Fin a))).real (K : Set (GL (Fin a) k)) : ℂ) * ∑ r ∈ R, F r := by
  intro k _ _ _ _ _ _ a K hKo hKle F hF R hR hsupp
  set μ := haarVol (KO k (Fin a)) with hμ
  have hKm : MeasurableSet (K : Set (GL (Fin a) k)) := hKo.measurableSet

  have hval : ∀ r g, r⁻¹ * g ∈ K → F g = F r := by
    intro r g h
    have := hF r (r⁻¹ * g) h
    rwa [mul_inv_cancel_left] at this

  have hpt : ∀ g, F g = ∑ r ∈ R, ((r • (K : Set (GL (Fin a) k))).indicator (fun _ => F r) g) := by
    intro g
    by_cases hg : F g = 0
    · rw [hg]
      refine (Finset.sum_eq_zero fun r _ => ?_).symm
      by_cases hm : g ∈ r • (K : Set (GL (Fin a) k))
      · rw [Set.indicator_of_mem hm, ← hval r g ((mem_leftCoset_iff r).1 hm), hg]
      · rw [Set.indicator_of_notMem hm]
    · obtain ⟨r₀, hr₀, hg₀⟩ := hsupp g hg
      rw [Finset.sum_eq_single r₀]
      · rw [Set.indicator_of_mem ((mem_leftCoset_iff r₀).2 hg₀), hval r₀ g hg₀]
      · intro r hr hne
        rw [Set.indicator_of_notMem]
        intro hm
        have h1 : r⁻¹ * g ∈ K := (mem_leftCoset_iff r).1 hm
        have h2 : r⁻¹ * r₀ ∈ K := by
          have := K.mul_mem h1 (K.inv_mem hg₀)
          simpa [mul_assoc] using this
        exact hne (hR r hr r₀ hr₀ h2)
      · intro h; exact absurd hr₀ h
  have hfin : μ (K : Set (GL (Fin a) k)) ≠ ⊤ :=
    ((measure_mono hKle).trans_lt isCompact_KO.measure_lt_top).ne
  have hcos : ∀ r : GL (Fin a) k, μ (r • (K : Set (GL (Fin a) k))) = μ K := fun r => measure_smul μ r _
  have hint : ∀ r ∈ R, Integrable ((r • (K : Set (GL (Fin a) k))).indicator (fun _ => F r)) μ := by
    intro r _
    rw [integrable_indicator_iff (hKm.const_smul r)]
    exact integrableOn_const (by rw [hcos]; exact hfin)
  calc ∫ g, F g ∂μ = ∫ g, ∑ r ∈ R, ((r • (K : Set (GL (Fin a) k))).indicator (fun _ => F r) g) ∂μ := by
          congr 1; funext g; exact hpt g
    _ = ∑ r ∈ R, ∫ g, ((r • (K : Set (GL (Fin a) k))).indicator (fun _ => F r) g) ∂μ :=
          MeasureTheory.integral_finsetSum R hint
    _ = ∑ r ∈ R, (μ.real (K : Set (GL (Fin a) k)) : ℂ) * F r := by
          refine Finset.sum_congr rfl fun r _ => ?_
          rw [integral_indicator_const _ (hKm.const_smul r), Measure.real, hcos, ← Measure.real,
            Complex.real_smul]
    _ = _ := by rw [Finset.mul_sum]

end GlobalTheory.HaarCosetSum
end

section

set_option autoImplicit false

noncomputable section

open TensorProduct Coalgebra Bialgebra CategoryTheory

namespace GlobalTheory

namespace PDiv

section Lift

variable {R R' M N : Type} [CommRing R] [CommRing R'] [Algebra R R'] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R' N]

def liftSemi (f : M →ₛₗ[algebraMap R R'] N) : R' ⊗[R] M →ₗ[R'] N :=
  letI : Module R N := Module.compHom _ (algebraMap R R')
  haveI : IsScalarTower R R' N := ⟨fun a b w => by rw [Algebra.smul_def, mul_smul]; rfl⟩
  LinearMap.liftBaseChange R'
    { toFun := f, map_add' := map_add f, map_smul' := fun r m => map_smulₛₗ f r m }

@[simp] theorem liftSemi_tmul (f : M →ₛₗ[algebraMap R R'] N) (r : R') (m : M) :
    liftSemi f (r ⊗ₜ m) = r • f m := rfl

end Lift

section Level

variable {R R' : Type} [CommRing R] [CommRing R'] {σ : R →+* R'} {A A' : Type} [CommRing A]
  [Bialgebra R A] [CommRing A'] [Bialgebra R' A']

def SemiBialgHom.prim (f : SemiBialgHom σ A A') :
    LinearMap.ker (cobOne R A) →ₛₗ[σ] LinearMap.ker (cobOne R' A') where
  toFun b := ⟨f b.1, by
    have hb : cobOne R A b.1 = 0 := b.2
    have hone : SemiBialgHom.lin f 1 = 1 := f.toRingHom.map_one
    have h := congrArg (SemiBialgHom.two f) hb
    simpa only [LinearMap.mem_ker, cobOne_apply, map_sub, SemiBialgHom.two_comul,
      TensorProduct.map_tmul, hone, SemiBialgHom.lin_apply, map_zero] using h⟩
  map_add' _ _ := Subtype.ext (f.toRingHom.map_add _ _)
  map_smul' _ _ := Subtype.ext (f.smul_map _ _)

@[simp] theorem SemiBialgHom.prim_val (f : SemiBialgHom σ A A') (b : LinearMap.ker (cobOne R A)) :
    (f.prim b).1 = f b.1 := rfl

theorem isPrimitiveElem_of_mem_ker {b : A} (hb : b ∈ LinearMap.ker (cobOne R A)) :
    IsPrimitiveElem R b := by
  rw [LinearMap.mem_ker, cobOne_apply, sub_sub, sub_eq_zero] at hb
  exact hb

theorem evalAt_mul [Module.Finite R A] [Module.Projective R A] [IsCocomm R A]
    (b : LinearMap.ker (cobOne R A)) (φ ψ : CartierDual R A) :
    CartierDual.evalAt R A b.1 (φ * ψ) =
      counitAlgHom R (CartierDual R A) φ • CartierDual.evalAt R A b.1 ψ +
        counitAlgHom R (CartierDual R A) ψ • CartierDual.evalAt R A b.1 φ :=
  (CartierDual.isPrimitiveElem_iff_mul b.1).1 (isPrimitiveElem_of_mem_ker b.2) φ ψ


variable (R A) in
def primTangent [Module.Finite R A] [Module.Projective R A] [IsCocomm R A] :
    LinearMap.ker (cobOne R A) →ₗ[R] Module.Dual R (Cot R (CartierDual R A)) where
  toFun b := AugCot.lift _ (CartierDual.evalAt R A b.1) (evalAt_mul b)
  map_add' b b' := AugCot.hom_ext fun φ => by simp
  map_smul' r b := AugCot.hom_ext fun φ => by simp

@[simp] theorem primTangent_d [Module.Finite R A] [Module.Projective R A] [IsCocomm R A]
    (b : LinearMap.ker (cobOne R A)) (φ : CartierDual R A) :
    primTangent R A b (dUnit (R := R) φ) = φ b.1 := AugCot.lift_d _ _ (evalAt_mul b) φ

variable [IsCocomm R A] [IsCocomm R' A']




end Level

end PDiv

namespace PDivGroup

open PDiv

variable {p : ℕ} {R : Type} [CommRing R] (G : PDivGroup p R)

def resOne (n : ℕ) : G.A (n + 1) →ₐc[R] G.A 1 :=
  Nat.rec (motive := fun n => G.A (n + 1) →ₐc[R] G.A 1) (BialgHom.id R _)
    (fun n f => f.comp (G.res (n + 1))) n

@[simp] theorem resOne_zero (a : G.A 1) : G.resOne 0 a = a := rfl

@[simp] theorem resOne_succ (n : ℕ) (a : G.A (n + 2)) :
    G.resOne (n + 1) a = G.resOne n (G.res (n + 1) a) := rfl

theorem resOne_surjective (n : ℕ) : Function.Surjective (G.resOne n) := by
  induction n with
  | zero => exact Function.surjective_id
  | succ n ih => exact ih.comp (G.res_surjective (n + 1))

theorem resOne_funs (B : G.funs) (n : ℕ) : G.resOne n (B.1 (n + 1)) = B.1 1 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [resOne_succ, B.2, ih]

theorem resOne_mulBy (n : ℕ) (a : G.A (n + 1)) :
    G.resOne n (mulBy R _ p a) = algebraMap R _ (counit a) := by
  have h := G.mulBy_pow_self 1 (G.resOne n a)
  rw [pow_one, CoalgHomClass.counit_comp_apply] at h
  rw [map_mulBy, h]

theorem resOne_mulP (n : ℕ) (a : G.A n) :
    G.resOne n (G.mulP n a) = algebraMap R _ (counit a) := by
  obtain ⟨b, rfl⟩ := G.res_surjective n a
  rw [mulP_res, resOne_mulBy, CoalgHomClass.counit_comp_apply]

def transl (n : ℕ) : G.A (n + 1) →ₐ[R] G.A (n + 1) ⊗[R] G.A 1 :=
  (Algebra.TensorProduct.map (AlgHom.id R _) (G.resOne n : G.A (n + 1) →ₐ[R] G.A 1)).comp
    (comulAlgHom R _)

theorem transl_apply (n : ℕ) (a : G.A (n + 1)) :
    G.transl n a = (G.resOne n : G.A (n + 1) →ₗ[R] G.A 1).lTensor _ (comul a) := rfl

theorem transl_res (n : ℕ) (a : G.A (n + 2)) :
    G.transl n (G.res (n + 1) a) =
      (G.res (n + 1) : G.A (n + 2) →ₗ[R] G.A (n + 1)).rTensor _ (G.transl (n + 1) a) := by
  rw [transl_apply, transl_apply, ← pullTwo_comul]
  generalize comul (R := R) a = t
  induction t with
  | add x y hx hy => simp only [map_add (f := _), hx, hy]
  | tmul x y => simp

theorem transl_mulP (n : ℕ) (a : G.A n) : G.transl n (G.mulP n a) = G.mulP n a ⊗ₜ 1 := by
  rw [transl_apply, ← pullTwo_comul]
  conv_rhs => rw [← (TensorProduct.rid R _).apply_symm_apply a, TensorProduct.rid_symm_apply,
    ← Coalgebra.lTensor_counit_comul]
  generalize comul (R := R) a = t
  induction t with
  | add x y hx hy => simp only [map_add (f := _), add_tmul, hx, hy]
  | tmul x y => simp [resOne_mulP, Algebra.algebraMap_eq_smul_one, smul_tmul]

theorem pullbackTwo_mulP_injective (n : ℕ) : Function.Injective (pullbackTwo (G.mulP n)) :=
  TensorProduct.map_injective_of_flat_flat _ _ (Test.mulP_injective G n) (Test.mulP_injective G n)

theorem res_eq_zero_of_cobOne_eq_zero (hp : (p : R) = 0) (n : ℕ) {b : G.A (n + 1)}
    (hb : cobOne R _ b = 0) : G.res n b = 0 :=
  Test.mulP_injective G n (by
    rw [mulP_res, (mulBy_of_cobOne_eq_zero hb p).1, ← Nat.cast_smul_eq_nsmul R, hp, zero_smul,
      map_zero])

theorem eq_zero_of_cob_eq_zero (hp : (p : R) = 0) {B : G.funs} (hB : G.cob B = 0) : B = 0 :=
  Subtype.ext (funext fun n => (B.2 n).symm.trans (G.res_eq_zero_of_cobOne_eq_zero hp n
    (congrArg (fun c : G.cocycles => c.1 (n + 1)) hB)))

theorem rigOfOmega_injective_of_eq_zero (hp : (p : R) = 0) : Function.Injective G.rigOfOmega := by
  refine (injective_iff_map_eq_zero _).2 fun w hw => ?_
  obtain ⟨b, hb⟩ := (Submodule.Quotient.mk_eq_zero _).1 hw
  rw [G.eq_zero_of_cob_eq_zero hp (congrArg Prod.fst hb), map_zero] at hb
  exact (congrArg Prod.snd hb).symm

theorem omegaLevel_one_bijective (hp : (p : R) = 0) : Function.Bijective (G.omegaLevel 1) := by
  refine ⟨(injective_iff_map_eq_zero _).2 fun w hw => ?_, G.omegaLevel_surjective 1⟩
  obtain ⟨v, rfl⟩ := (G.omega_val_eq_zero_iff 1 w).1 hw
  rw [pow_one, hp, zero_smul]

def primLie : LinearMap.ker (cobOne R (G.A 1)) →ₗ[R] G.dual.Lie :=
  (G.dual.omegaLevel 1).dualMap ∘ₗ primTangent R (G.A 1)

theorem primLie_apply (b : LinearMap.ker (cobOne R (G.A 1))) (w : G.dual.omega)
    (φ : CartierDual R (G.A 1)) (h : w.1 1 = dUnit (R := R) φ) : G.primLie b w = φ b.1 :=
  (congrArg (primTangent R (G.A 1) b) h).trans (primTangent_d b φ)

end PDivGroup

end GlobalTheory
end
end

section

open MvPowerSeries ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Sh GlobalTheory.FGDepth

theorem _root_.GlobalTheory.T.exists_integral_invariant_derivation_log : ∀ (C : Type) [Field C] [CharZero C] (v : AddValuation C (WithTop ℝ)) (d : ℕ) (G : LogFGL v d), ∃ D : Fin d → Fin d → MvPowerSeries (Fin d) C, (∀ k l, MvIsInt v (D k l)) ∧ ∀ (f : MvPowerSeries (Fin d) C) (k : Fin d) (α : Fin d →₀ ℕ), ((α k : C) + 1) * coeff (α + Finsupp.single k 1) (subst (expOf G) f) = coeff α (subst (expOf G) (∑ l, D k l * (show MvPowerSeries (Fin d) C from fun β => ((β l : C) + 1) * coeff (β + Finsupp.single l 1) f))) := by
  first | exact @GlobalTheory.LogJacobian.exists_integral_invariant_derivation | exact GlobalTheory.LogJacobian.exists_integral_invariant_derivation | (intros; apply GlobalTheory.LogJacobian.exists_integral_invariant_derivation <;> assumption)
end

section

open MvPowerSeries ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Sh GlobalTheory.FGDepth

theorem _root_.GlobalTheory.T.dividedPowerContentValuation_detPow_bounds : ∀ (C : Type) [Field C] [CharZero C] (v : AddValuation C (WithTop ℝ)) (p : ℕ), p.Prime → v (p : C) = 1 → ∀ (i c : ℕ), content v (detPow C i c) ≤ (((i * c : ℝ) / (p - 1) : ℝ) : EReal) ∧ ((((i * c : ℝ) / (p - 1) - (i : ℝ) ^ 2 * Real.logb p (c + 1) : ℝ)) : EReal) ≤ content v (detPow C i c) := by
  first | exact @GlobalTheory.DetPowContent.content_detPow_bounds | exact GlobalTheory.DetPowContent.content_detPow_bounds | (intros; apply GlobalTheory.DetPowContent.content_detPow_bounds <;> assumption)
end

section

open MvPowerSeries ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Sh GlobalTheory.FGDepth

theorem _root_.GlobalTheory.T.differentialOperatorDepth_le_dividedPowerContent : ∀ (C : Type) [Field C] [CharZero C] (v : AddValuation C (WithTop ℝ)) (κ : Type) [Fintype κ] [DecidableEq κ] (d n : κ → ℕ) (G : ∀ b, LogFGL v (d b)) (u : ∀ b, Fin (n b) → Fin (d b) → C) (P : MvPolynomial (Σ b, Fin (n b)) C) (D : ℕ), P.IsHomogeneous D → (∀ b, IsSatFrame v (u b)) → depth G (ι := fun b => Fin (n b)) u P ≤ content v P := by
  first | exact @GlobalTheory.FGDepth.DepthLeContent.depth_le_content | exact GlobalTheory.FGDepth.DepthLeContent.depth_le_content | (intros; apply GlobalTheory.FGDepth.DepthLeContent.depth_le_content <;> assumption)
end

section

open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr Polynomial

theorem _root_.GlobalTheory.T.card_residueField_localOrder_unitary_prod : ∀ (K : UQ) (B₁ B₂ : InvAlg K), B₁.g * B₁.σ B₁.g = 1 → B₂.g * B₂.σ B₂.g = 1 → (B₁.P * B₂.P).Separable → IsIntegral K.O B₁.g → IsIntegral K.O B₂.g → ∀ hl : IsLocalRing (Algebra.adjoin K.O ({(B₁.prod B₂).g} : Set (B₁.prod B₂).A)), ∃ d : ℕ, Odd d ∧ Nat.card (@IsLocalRing.ResidueField (Algebra.adjoin K.O ({(B₁.prod B₂).g} : Set (B₁.prod B₂).A)) _ hl) = K.q ^ (2 * d) := by
  first | exact @GlobalTheory.UnitLemma.ResDeg.card_residueField_prod_any | exact GlobalTheory.UnitLemma.ResDeg.card_residueField_prod_any | (intros; apply GlobalTheory.UnitLemma.ResDeg.card_residueField_prod_any <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

namespace GlobalTheory

theorem isIso_of_isAffine_of_coheight_le_one {X Y : Scheme.{0}} [IsLocallyNoetherian X]
    [GlobalTheory.IsNormalScheme X] [IsAffine X] [IsAffine Y] (f : Y ⟶ X) [IsOpenImmersion f]
    (hf : ∀ x : X, Order.coheight x ≤ 1 → x ∈ Set.range f) : IsIso f := by
  have h : IsIso (f.appTop) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr (bijective_app_of_coheight_le_one f hf ⊤)
  have : IsIso (Spec.map f.appTop) := inferInstance
  have e : f = Y.isoSpec.hom ≫ Spec.map f.appTop ≫ X.isoSpec.inv := by
    rw [← Category.assoc, Scheme.isoSpec_hom_naturality]
    simp
  rw [e]
  infer_instance

theorem eq_of_isAffineOpen_of_ringKrullDim_le_one (X : Scheme.{0}) [IsLocallyNoetherian X]
    [X.IsSeparated] (hX : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X) (V V' : X.Opens)
    (hV : IsAffineOpen V) (hle : V ≤ V')
    (h : ∀ z ∈ V', ringKrullDim (X.presheaf.stalk z) ≤ 1 → z ∈ V) : V' = V := by
  have := GlobalTheory.IsNormalScheme.of_pred hX
  refine le_antisymm (fun z hz ↦ ?_) hle
  obtain ⟨_, ⟨N, hN, rfl⟩, hzN, hNV⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hz V'.isOpen
  have hN' : IsAffineOpen N := hN
  have hNV' : IsAffineOpen (N ⊓ V) := hN'.inf hV
  have : IsAffine N := hN'
  have : IsAffine (N ⊓ V : X.Opens) := hNV'
  have hiso : IsIso (X.homOfLE (inf_le_left : N ⊓ V ≤ N)) := by
    refine isIso_of_isAffine_of_coheight_le_one _ fun x hx ↦ ?_
    have hx' : Order.coheight (Scheme.Opens.ι N x) ≤ 1 := by rwa [coheight_apply_of_isOpenImmersion]
    have hxV : Scheme.Opens.ι N x ∈ V := h _ (hNV x.2) ((ringKrullDim_stalk_le_one_iff _).mpr hx')
    exact ⟨⟨x.1, x.2, hxV⟩, Subtype.ext (Scheme.homOfLE_apply _ _)⟩
  obtain ⟨y, hy⟩ := (X.homOfLE (inf_le_left : N ⊓ V ≤ N)).surjective ⟨z, hzN⟩
  have hyz : y.1 = z := (Scheme.homOfLE_apply _ y).symm.trans (congrArg Subtype.val hy)
  exact hyz ▸ y.2.2

end GlobalTheory
end

section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil

namespace GlobalTheory.SmGL.ParIndAdm

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α]
  [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n]
  {W : Type} [AddCommGroup W] [Module ℂ W]

theorem exists_finset_KO_cover (K : Subgroup (GL n k)) (hK : IsOpen (K : Set (GL n k))) :
    ∃ R : Finset (GL n k), ∀ w ∈ KO k n, ∃ r ∈ R, r⁻¹ * w ∈ K := by
  obtain ⟨R, hR⟩ := (GlobalTheory.SplitFlip.isCompact_KO (k := k) (n := n)).elim_finite_subcover
    (fun x : GL n k => (fun y => x⁻¹ * y) ⁻¹' (K : Set (GL n k)))
    (fun x => hK.preimage (by fun_prop))
    (fun w _ => Set.mem_iUnion.2 ⟨w, by simp [one_mem]⟩)
  refine ⟨R, fun w hw => ?_⟩
  obtain ⟨r, hr, h⟩ := Set.mem_iUnion₂.1 (hR hw)
  exact ⟨r, hr, h⟩

theorem eq_zero_of_fixed (e : (Σ a, m a) ≃ n) (ρ : Representation ℂ (Levi k m) W) (K : Subgroup (GL n k))
    (R : Finset (GL n k)) (hR : ∀ w ∈ KO k n, ∃ r ∈ R, r⁻¹ * w ∈ K)
    (f : IndSp e ρ) (hf : f ∈ fixed (parInd e ρ) K) (h0 : ∀ r ∈ R, f.1.1 r = 0) : f = 0 := by
  have hfix : ∀ κ ∈ K, ∀ x, f.1.1 (x * κ) = f.1.1 x := fun κ hκ x => by
    have := congrArg (fun φ : IndSp e ρ => φ.1.1 x) (hf ⟨κ, hκ⟩)
    simpa using this
  apply Subtype.ext; apply Subtype.ext; funext x
  obtain ⟨u, l, w, hw, rfl⟩ := UnitInd.exists_iwasawa e x
  obtain ⟨r, hr, hrw⟩ := hR w hw
  let p : parab k e := ⟨(u : GL n k) * leviEmb k e l,
    mul_mem (unipRad_le_parab k e u.2) (leviEmb_mem_parab k e l)⟩
  have hw' : f.1.1 w = 0 := by
    have := hfix _ hrw r
    rw [mul_inv_cancel_left] at this
    rw [this, h0 r hr]
  show f.1.1 ((p : GL n k) * w) = 0
  rw [parInd_law, hw', map_zero, smul_zero]

theorem isAdmissible_parInd (e : (Σ a, m a) ≃ n) (ρ : Representation ℂ (Levi k m) W)
    [FiniteDimensional ℂ W] : IsAdmissible (parInd e ρ) := by
  refine ⟨isSmooth_parInd e ρ, fun K hKo _ => ?_⟩
  obtain ⟨R, hR⟩ := exists_finset_KO_cover K hKo
  let L : fixed (parInd e ρ) K →ₗ[ℂ] (R → W) :=
    { toFun := fun f r => f.1.1.1 r
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  refine Module.Finite.of_injective L fun f g hfg => ?_
  rw [← sub_eq_zero]
  have h := eq_zero_of_fixed e ρ K R hR (f - g).1 (f - g).2 fun r hr => by
    have := congrFun hfg ⟨r, hr⟩
    simp only [L, LinearMap.coe_mk, AddHom.coe_mk] at this
    show f.1.1.1 r - g.1.1.1 r = 0
    rw [this, sub_self]
  exact Subtype.ext h

end GlobalTheory.SmGL.ParIndAdm

namespace GlobalTheory.ThK.MidJac

end GlobalTheory.ThK.MidJac
end
end

section

open GlobalTheory.PRep GlobalTheory.SmGL

theorem _root_.GlobalTheory.T.finiteDimensional_compact_fixed_vectors_piTensor_smooth : ∀ {α : Type} [Finite α] {Γ X : α → Type} [∀ a, Group (Γ a)] [∀ a, TopologicalSpace (Γ a)] [∀ a, IsTopologicalGroup (Γ a)] [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)] (ρ : ∀ a, Representation ℂ (Γ a) (X a)), (∀ a, IsSmooth (ρ a)) → ∀ (K : ∀ a, Subgroup (Γ a)), (∀ a, IsCompact (K a : Set (Γ a))) → (∀ a, FiniteDimensional ℂ (fixed (ρ a) (K a))) → FiniteDimensional ℂ (fixed (piTensor ρ) (Subgroup.pi Set.univ K)) := by
  first | exact @GlobalTheory.PiTensorFixed.finiteDimensional_fixed_piTensor | exact GlobalTheory.PiTensorFixed.finiteDimensional_fixed_piTensor | (intros; apply GlobalTheory.PiTensorFixed.finiteDimensional_fixed_piTensor <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

namespace GlobalTheory.HilbAff

theorem exists_basic_nhd : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (N r : ℕ) (e : Module.Basis (Fin N) A B) (Z : Scheme.{0}) (y : (GlobalTheory.HilbAff.functor A B r).obj (op Z)) (z : Z), ∃ (σ : Fin r ↪ Fin N) (U : Z.Opens), z ∈ U ∧ GlobalTheory.HilbAff.Basic A B e σ ((GlobalTheory.HilbAff.functor A B r).map U.ι.op y) := by
  intro A B _ _ _ N r e Z y z
  obtain ⟨W₀, hW₀, hzW₀, -⟩ := exists_isAffineOpen_mem_and_subset (show z ∈ (⊤ : Z.Opens) from trivial)
  let W : Z.affineOpens := ⟨W₀, hW₀⟩
  obtain ⟨hfin, hflat⟩ := GlobalTheory.T.affineHilbertSections_finite_flat A B r Z y W
  obtain ⟨σ, f, hf, hbij⟩ := GlobalTheory.T.exists_localizedModule_map_bijective_of_rankAtStalk_eq Γ(Z, W₀) (GlobalTheory.HilbAff.Sec A B y W) N r
    (fun j => GlobalTheory.HilbAff.gen A B y W (e j)) (GlobalTheory.T.affineHilbertSections_basis_span_eq_top A B N r e Z y W) (GlobalTheory.T.affineHilbertSections_rankAtStalk A B r Z y W)
    (hW₀.primeIdealOf ⟨z, hzW₀⟩)
  have hD := (GlobalTheory.T.affineHilbertCoordinateMap_basicOpen_bijective A B N r e σ Z y W f).2 hbij
  have hzf : z ∈ Z.basicOpen f := by
    have h1 : hW₀.primeIdealOf ⟨z, hzW₀⟩ ∈ hW₀.fromSpec ⁻¹ᵁ Z.basicOpen f := by
      rw [hW₀.fromSpec_preimage_basicOpen]; exact hf
    have h2 := hW₀.fromSpec_primeIdealOf ⟨z, hzW₀⟩
    have h3 : hW₀.fromSpec (hW₀.primeIdealOf ⟨z, hzW₀⟩) ∈ Z.basicOpen f := h1
    rw [h2] at h3
    exact h3
  refine ⟨σ, Z.basicOpen f, hzf, ?_⟩
  rw [GlobalTheory.HilbAff.basic_iff]
  intro W'
  apply GlobalTheory.T.affineHilbertCoordinateMap_restrict_bijective
  exact GlobalTheory.T.hilbertCoordinateMap_bijective_of_le_affine A B N r e σ Z y ⟨Z.basicOpen f, hW₀.basicOpen f⟩
    ⟨_, W'.2.image_of_isOpenImmersion (Z.basicOpen f).ι⟩ (Scheme.Opens.ι_image_le _ _) hD

end GlobalTheory.HilbAff
end
