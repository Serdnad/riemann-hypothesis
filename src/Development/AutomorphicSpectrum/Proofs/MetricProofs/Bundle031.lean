module

public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Data.Nat.Prime.Defs
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle024
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Algebra.TrivSqZeroExt.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.RingTheory.Kaehler.Basic
import Mathlib.Algebra.DualNumber
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle023
public import Mathlib.Basic.Complex.Basic
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle025
public import ReciprocityTheory.AnalyticForms.LeviForms.HomDens
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.InFlagDomainOne
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle005
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
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsHorizontalTwist
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle006
public import Mathlib.Algebra.Algebra.Hom.Rat
public import Mathlib.RingTheory.Localization.Away.Basic
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle003
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.PairRelationOfScaledRatio
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle002
public import ReciprocityTheory.AnalyticForms.PotentialTheory.PshShiftA
import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.Statements
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.PermFinTwoUniv
import ReciprocityTheory.AnalyticForms.LeviForms.Bundle001
import ReciprocityTheory.AnalyticForms.MaIntEmpty
import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialOfFun
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.GenericFibreKerTarget
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.IsRatSectionOn
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsSemipositiveOn
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle006

@[expose] public section

section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo MeasureTheory GlobalTheory.CompanionTheory.Ar.Tw

theorem _root_.GlobalTheory.T.finite_primes_sum_squares_zero : ∀ (σ : Type) [Finite σ] (A : Type) [CommRing A] [IsDomain A] [CharZero A] (f : MvPolynomial σ ℤ →+* A), Function.Surjective f → {p : ℕ | p.Prime ∧ ∃ a b : A, b ≠ 0 ∧ a ^ 2 + (p : A) * b ^ 2 = 0}.Finite := by
  first | exact @GlobalTheory.CompanionTheory.QuadFin.finite_primes_neg_sq | exact GlobalTheory.CompanionTheory.QuadFin.finite_primes_neg_sq | (intros; apply GlobalTheory.CompanionTheory.QuadFin.finite_primes_neg_sq <;> assumption)
end

section

open MvPolynomial ReciprocityTheory.AnForm.R GlobalTheory.CompanionTheory.Ar.Cmp

namespace GlobalTheory.CompanionTheory.Ar.Cmp

theorem exists_mul_pow_eq_aeval_of_mem_adjoin_inv :
    ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (σ : Type) (τ : σ → Ω) (F : MvPolynomial σ ℚ)
      (S : Subalgebra ℚ Ω), aeval τ F ≠ 0 →
      S = Algebra.adjoin ℚ (insert (aeval τ F)⁻¹ (Set.range τ)) →
      ∀ s : S, ∃ (N : ℕ) (G : MvPolynomial σ ℚ), (s : Ω) * aeval τ F ^ N = aeval τ G := by
  intro Ω _ _ σ τ F S hf hS s
  obtain ⟨x, hx⟩ := s
  subst hS
  change ∃ (N : ℕ) (G : MvPolynomial σ ℚ), x * aeval τ F ^ N = aeval τ G
  induction hx using Algebra.adjoin_induction with
  | mem y hy =>
    rcases hy with rfl | ⟨q, rfl⟩
    · exact ⟨1, 1, by simp [hf]⟩
    · exact ⟨0, X q, by simp⟩
  | algebraMap r =>
    exact ⟨0, C r, by simp [MvPolynomial.algebraMap_eq]⟩
  | add a b _ _ iha ihb =>
    obtain ⟨N, G, h⟩ := iha
    obtain ⟨M, H, h'⟩ := ihb
    refine ⟨N + M, G * F ^ M + H * F ^ N, ?_⟩
    simp only [map_add (f := _), map_mul, map_pow, ← h, ← h']
    ring
  | mul a b _ _ iha ihb =>
    obtain ⟨N, G, h⟩ := iha
    obtain ⟨M, H, h'⟩ := ihb
    refine ⟨N + M, G * H, ?_⟩
    simp only [map_mul, ← h, ← h']
    ring

end GlobalTheory.CompanionTheory.Ar.Cmp
end

section

open MvPolynomial ReciprocityTheory.AnForm.R GlobalTheory.CompanionTheory.Ar.Cmp

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Ktan

open TrivSqZeroExt

def dualPt {σ : Type} (t v : σ → ℂ) : σ → TrivSqZeroExt ℂ ℂ := fun q => inl (t q) + inr (v q)

theorem aeval_dualPt {σ : Type} [Fintype σ] (t v : σ → ℂ) (G : MvPolynomial σ ℂ) :
    fst (aeval (dualPt t v) G) = eval t G ∧
      snd (aeval (dualPt t v) G) = ∑ q, v q * eval t (pderiv q G) := by
  classical
  induction G using MvPolynomial.induction_on with
  | C a => simp [algebraMap_eq_inl]
  | add p q hp hq =>
    refine ⟨by simp [hp.1, hq.1], ?_⟩
    simp [hp.2, hq.2, mul_add, Finset.sum_add_distrib]
  | mul_X p q hp =>
    refine ⟨by simp [hp.1, dualPt], ?_⟩
    simp only [map_mul, aeval_X, snd_mul, hp.1, hp.2, dualPt, fst_add, fst_inl, fst_inr, snd_add, snd_inl, snd_inr,
      Derivation.leibniz, pderiv_X, eval_mul, eval_X, smul_eq_mul, op_smul_eq_mul, add_zero, zero_add, map_add]
    simp [Pi.single_apply, mul_add, Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_mul, mul_comm, mul_left_comm, mul_assoc]

theorem snd_eq_zero_of_span {S : Type} [CommRing S] [Algebra ℚ S]
    (φ : S →ₐ[ℚ] TrivSqZeroExt ℂ ℂ) {e : ℕ} (z : Fin e → S)
    (hspan : Submodule.span S (Set.range fun i => KaehlerDifferential.D ℚ S (z i)) = ⊤)
    (h : ∀ i, snd (φ (z i)) = 0) (s : S) : snd (φ s) = 0 := by
  let f : S →+* ℂ := (TrivSqZeroExt.fstHom ℚ ℂ ℂ).toRingHom.comp φ.toRingHom
  letI : Module S ℂ := Module.compHom ℂ f
  haveI : IsScalarTower ℚ S ℂ := ⟨fun q a m => by
    show f (q • a) * m = q • (f a * m)
    rw [Algebra.smul_def, map_mul, Algebra.smul_def, mul_assoc]
    congr 1
    exact (eq_ratCast (f.comp (algebraMap ℚ S)) q).trans (eq_ratCast (algebraMap ℚ ℂ) q).symm⟩
  let d : Derivation ℚ S ℂ :=
    { toFun := fun a => snd (φ a)
      map_add' := fun a b => by simp
      map_smul' := fun q a => by simp
      map_one_eq_zero' := by simp
      leibniz' := fun a b => by
        show snd (φ (a * b)) = (φ a).fst * snd (φ b) + (φ b).fst * snd (φ a)
        rw [map_mul, snd_mul, smul_eq_mul, op_smul_eq_mul]
        ring }
  have key : d.liftKaehlerDifferential = 0 := by
    refine LinearMap.ext_on_range hspan fun i => ?_
    rw [Derivation.liftKaehlerDifferential_comp_D]
    exact h i
  have h2 := congrArg (fun L => L (KaehlerDifferential.D ℚ S s)) key
  simpa [Derivation.liftKaehlerDifferential_comp_D, d] using h2

theorem tangent_eq_zero : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (σ : Type) [Fintype σ] (τ : σ → Ω) (F : MvPolynomial σ ℚ) (S : Subalgebra ℚ Ω) (e : ℕ) (z : Fin e → S) (Z : Fin e → MvPolynomial σ ℚ) (N : Fin e → ℕ) (t v : σ → ℂ) (c : Fin e → ℂ), aeval τ F ≠ 0 → S = Algebra.adjoin ℚ (insert (aeval τ F)⁻¹ (Set.range τ)) → Submodule.span S (Set.range fun i => KaehlerDifferential.D ℚ S (z i)) = ⊤ → (∀ i, (z i : Ω) * aeval τ F ^ N i = aeval τ (Z i)) → (∀ G : MvPolynomial σ ℚ, aeval τ G = 0 → eval t (map (algebraMap ℚ ℂ) G) = 0) → eval t (map (algebraMap ℚ ℂ) F) ≠ 0 → (∀ G : MvPolynomial σ ℚ, aeval τ G = 0 → ∑ q, v q * eval t (pderiv q (map (algebraMap ℚ ℂ) G)) = 0) → (∀ i, eval t (map (algebraMap ℚ ℂ) (Z i)) = c i * eval t (map (algebraMap ℚ ℂ) F) ^ N i) → (∀ i, ∑ q, v q * eval t (pderiv q (map (algebraMap ℚ ℂ) (Z i) - C (c i) * map (algebraMap ℚ ℂ) F ^ N i)) = 0) → v = 0 := by
  intro Ω _ _ σ _ τ F S e z Z N t v c hF0 hS hspan hz hker0 hFt hker1 hZc hZd
  have hψ : ∀ G : MvPolynomial σ ℚ, (aeval (dualPt t v) G : TrivSqZeroExt ℂ ℂ) =
      aeval (dualPt t v) (map (algebraMap ℚ ℂ) G) := fun G =>
    (aeval_map_algebraMap ℂ (dualPt t v) G).symm
  have hker : ∀ G : MvPolynomial σ ℚ, aeval τ G = 0 → (aeval (dualPt t v) G : TrivSqZeroExt ℂ ℂ) = 0 := by
    intro G hG
    have h1 := aeval_dualPt t v (map (algebraMap ℚ ℂ) G)
    rw [hψ]
    refine TrivSqZeroExt.ext ?_ ?_
    · rw [h1.1, hker0 G hG]; simp
    · rw [h1.2, hker1 G hG]; simp
  have memInv : (aeval τ F)⁻¹ ∈ S := hS ▸ Algebra.subset_adjoin (Set.mem_insert _ _)
  have memτ : ∀ q, τ q ∈ S := fun q => hS ▸ Algebra.subset_adjoin (Set.mem_insert_of_mem _ ⟨q, rfl⟩)
  have hRS : (aeval τ : MvPolynomial σ ℚ →ₐ[ℚ] Ω).range ≤ S := by
    rw [← Algebra.adjoin_range_eq_range_aeval ℚ τ, hS]
    exact Algebra.adjoin_mono (Set.subset_insert _ _)
  have hsurjS : ∀ s ∈ S, ∃ r ∈ (aeval τ : MvPolynomial σ ℚ →ₐ[ℚ] Ω).range, ∃ n : ℕ, s = r * (aeval τ F)⁻¹ ^ n := by
    rw [hS]
    intro s hs
    induction hs using Algebra.adjoin_induction with
    | mem y hy =>
      rcases hy with rfl | ⟨q, rfl⟩
      · exact ⟨1, Subalgebra.one_mem _, 1, by ring⟩
      · exact ⟨τ q, ⟨X q, aeval_X τ q⟩, 0, by ring⟩
    | algebraMap r => exact ⟨algebraMap ℚ Ω r, Subalgebra.algebraMap_mem _ r, 0, by ring⟩
    | add y y' _ _ hy hy' =>
      obtain ⟨r, hr, n, rfl⟩ := hy
      obtain ⟨r', hr', n', rfl⟩ := hy'
      refine ⟨r * aeval τ F ^ n' + r' * aeval τ F ^ n, Subalgebra.add_mem _ (Subalgebra.mul_mem _ hr
        (Subalgebra.pow_mem _ (AlgHom.mem_range_self _ F) _)) (Subalgebra.mul_mem _ hr'
        (Subalgebra.pow_mem _ (AlgHom.mem_range_self _ F) _)), n + n', ?_⟩
      rw [inv_pow, inv_pow, inv_pow]
      field_simp
      ring
    | mul y y' _ _ hy hy' =>
      obtain ⟨r, hr, n, rfl⟩ := hy
      obtain ⟨r', hr', n', rfl⟩ := hy'
      exact ⟨r * r', Subalgebra.mul_mem _ hr hr', n + n', by rw [pow_add]; ring⟩
  letI : Algebra (aeval τ : MvPolynomial σ ℚ →ₐ[ℚ] Ω).range S := (Subalgebra.inclusion hRS).toRingHom.toAlgebra
  let xR : (aeval τ : MvPolynomial σ ℚ →ₐ[ℚ] Ω).range := ⟨aeval τ F, AlgHom.mem_range_self _ F⟩
  have hxS : IsUnit (algebraMap _ S xR) :=
    isUnit_iff_exists_inv.2 ⟨⟨(aeval τ F)⁻¹, memInv⟩, Subtype.ext (by
      show aeval τ F * (aeval τ F)⁻¹ = 1
      exact mul_inv_cancel₀ hF0)⟩
  haveI : IsLocalization.Away xR S := by
    refine ⟨?_, ?_, ?_⟩
    · rintro ⟨y, n, rfl⟩
      rw [map_pow]
      exact hxS.pow n
    · intro s
      obtain ⟨r, hr, n, hs⟩ := hsurjS s s.2
      refine ⟨(⟨r, hr⟩, ⟨xR ^ n, n, rfl⟩), Subtype.ext ?_⟩
      show (s : Ω) * ((xR ^ n : (aeval τ : MvPolynomial σ ℚ →ₐ[ℚ] Ω).range) : Ω) = r
      rw [SubmonoidClass.coe_pow, hs]
      show r * (aeval τ F)⁻¹ ^ n * aeval τ F ^ n = r
      rw [mul_assoc, ← mul_pow, inv_mul_cancel₀ hF0, one_pow, mul_one]
    · intro a b h
      have h' : ((algebraMap _ S a : S) : Ω) = ((algebraMap _ S b : S) : Ω) := congrArg (fun s : S => (s : Ω)) h
      exact ⟨1, congrArg _ (Subtype.ext h')⟩
  have hsurjR : Function.Surjective ((aeval τ : MvPolynomial σ ℚ →ₐ[ℚ] Ω).rangeRestrict :
      MvPolynomial σ ℚ →+* (aeval τ : MvPolynomial σ ℚ →ₐ[ℚ] Ω).range) := by
    rintro ⟨y, G, rfl⟩
    exact ⟨G, rfl⟩
  let ψR : (aeval τ : MvPolynomial σ ℚ →ₐ[ℚ] Ω).range →+* TrivSqZeroExt ℂ ℂ :=
    RingHom.liftOfSurjective _ hsurjR ⟨(aeval (dualPt t v) : MvPolynomial σ ℚ →ₐ[ℚ] TrivSqZeroExt ℂ ℂ).toRingHom,
      fun G hG => by
        rw [RingHom.mem_ker] at hG ⊢
        exact hker G (congrArg Subtype.val hG)⟩
  have hψR : ∀ G : MvPolynomial σ ℚ, ψR ((aeval τ : MvPolynomial σ ℚ →ₐ[ℚ] Ω).rangeRestrict G) =
      aeval (dualPt t v) G := fun G => RingHom.liftOfSurjective_comp_apply _ hsurjR _ G
  have hxR : xR = (aeval τ : MvPolynomial σ ℚ →ₐ[ℚ] Ω).rangeRestrict F := rfl
  have hFt' : IsUnit (aeval (dualPt t v) F : TrivSqZeroExt ℂ ℂ) := by
    rw [TrivSqZeroExt.isUnit_iff_isUnit_fst, hψ, (aeval_dualPt t v _).1]
    exact isUnit_iff_ne_zero.2 hFt
  have hu : IsUnit (ψR xR) := by rw [hxR, hψR]; exact hFt'
  let φS : S →+* TrivSqZeroExt ℂ ℂ := IsLocalization.Away.lift xR hu
  have hφS : ∀ G : MvPolynomial σ ℚ, φS (algebraMap _ S ((aeval τ : MvPolynomial σ ℚ →ₐ[ℚ] Ω).rangeRestrict G)) =
      aeval (dualPt t v) G := fun G => by
    rw [IsLocalization.Away.lift_eq, hψR]
  have hZ : ∀ i, (aeval (dualPt t v) (Z i) : TrivSqZeroExt ℂ ℂ) =
      inl (c i) * aeval (dualPt t v) F ^ N i := by
    intro i
    have h0 : (aeval (dualPt t v) (map (algebraMap ℚ ℂ) (Z i) - C (c i) * map (algebraMap ℚ ℂ) F ^ N i) :
        TrivSqZeroExt ℂ ℂ) = 0 := by
      have h1 := aeval_dualPt t v (map (algebraMap ℚ ℂ) (Z i) - C (c i) * map (algebraMap ℚ ℂ) F ^ N i)
      refine TrivSqZeroExt.ext ?_ ?_
      · rw [h1.1]; simp [hZc i]
      · rw [h1.2, hZd i]; simp
    rw [map_sub, map_mul, map_pow, aeval_C, algebraMap_eq_inl, ← hψ, ← hψ, sub_eq_zero] at h0
    exact h0
  have hφz : ∀ i, snd (φS.toRatAlgHom (z i)) = 0 := by
    intro i
    have e1 : z i * algebraMap _ S (xR ^ N i) =
        algebraMap _ S ((aeval τ : MvPolynomial σ ℚ →ₐ[ℚ] Ω).rangeRestrict (Z i)) := Subtype.ext (by
      show (z i : Ω) * ((xR ^ N i : (aeval τ : MvPolynomial σ ℚ →ₐ[ℚ] Ω).range) : Ω) = aeval τ (Z i)
      rw [SubmonoidClass.coe_pow]
      exact hz i)
    have e2 := congrArg φS e1
    have hφx : φS (algebraMap _ S xR) = aeval (dualPt t v) F := by rw [hxR]; exact hφS F
    rw [map_mul, map_pow, map_pow, hφx, hφS, hZ] at e2
    have e3 : φS (z i) = inl (c i) := (hFt'.pow (N i)).mul_left_inj.1 e2
    show snd (φS (z i)) = 0
    rw [e3, snd_inl]
  funext q
  have h := snd_eq_zero_of_span φS.toRatAlgHom z hspan hφz ⟨τ q, memτ q⟩
  have hq : (⟨τ q, memτ q⟩ : S) = algebraMap _ S ((aeval τ : MvPolynomial σ ℚ →ₐ[ℚ] Ω).rangeRestrict (X q)) :=
    Subtype.ext (aeval_X τ q).symm
  change snd (φS ⟨τ q, memτ q⟩) = 0 at h
  rw [hq, hφS, aeval_X] at h
  simpa [dualPt] using h

end GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Ktan
end
end

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.StepW GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical


theorem _root_.GlobalTheory.T.gram_matrix_sub_scalar_posSemidef : ∀ (n k : ℕ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (G : E → Matrix (Fin n) (Fin n) ℂ) (V : E → Matrix (Fin n) (Fin k) ℂ) (x : E) (a P Q : ℝ), 0 < a → 0 < P → P ≤ Q → (∀ p q, DifferentiableAt ℝ (fun y => G y p q) x) → (∀ p q, DifferentiableAt ℝ (fun y => V y p q) x) → (∀ᶠ y in nhds x, (G y).PosDef ∧ LinearIndependent ℂ (V y)ᵀ) → ((V x)ᴴ * G x * V x - (a : ℂ) • (1 : Matrix (Fin k) (Fin k) ℂ)).PosSemidef → (∀ p q, ‖G x p q‖ ≤ P ∧ ‖fderiv ℝ (fun y => G y p q) x‖ ≤ Q) → (∀ p q, ‖V x p q‖ ≤ P ∧ ‖fderiv ℝ (fun y => V y p q) x‖ ≤ Q) → ‖fderiv ℝ (fun y => Real.log ((V y)ᴴ * G y * V y).det.re) x‖ ≤ 3 * (k : ℝ) ^ 2 * (n : ℝ) ^ 2 * P ^ 2 * Q / a := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.StepW.gram_grad_scaled | exact GlobalTheory.CompanionTheory.Ar.PB.StepW.gram_grad_scaled | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.StepW.gram_grad_scaled <;> assumption)
end

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

theorem _root_.GlobalTheory.T.valuation_ring_extension_specialization : ∀ (L : Type) [Field L] (O : Subring L) (v : O →+* ℂ), (∀ s : O, v s ≠ 0 → (s : L)⁻¹ ∈ O) → ∃ V : ValuationSubring L, (∀ s ∈ O, s ∈ V) ∧ ∀ T : Finset L, (∀ t ∈ T, t ∈ V) → ∃ (R : Subring L) (hO : O ≤ R) (ψ : R →+* ℂ), (∀ t ∈ T, t ∈ R) ∧ (∀ s : O, ψ (Subring.inclusion hO s) = v s) ∧ ∀ t ∈ T, t ≠ 0 → t⁻¹ ∈ V → t⁻¹ ∈ R := by
  first | exact @GlobalTheory.CompanionTheory.Ar.ComplexPlace.exists_valuationSubring_place | exact GlobalTheory.CompanionTheory.Ar.ComplexPlace.exists_valuationSubring_place | (intros; apply GlobalTheory.CompanionTheory.Ar.ComplexPlace.exists_valuationSubring_place <;> assumption)
end

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB

theorem gramLog_cellMat (N : ℕ) (hd : Fin N → ℝ) (m : ℕ) (hm : m ≤ N) (z : Pairs N → ℂ) :
    gramLog hd m (cellMat N z) = logDetFlag N hd m hm z := by
  let e : Fin m ≃ {a : Fin N // (a : ℕ) < m} :=
    { toFun := fun i => ⟨Fin.castLE hm i, i.2⟩, invFun := fun a => ⟨a.1, a.2⟩,
      left_inv := fun _ => rfl, right_inv := fun _ => rfl }
  have hdet : (gramHead hd m (cellMat N z)).det =
      (((cellMat N z)ᴴ * diagonal (fun k => (hd k : ℂ)) * cellMat N z).submatrix
        (Fin.castLE hm) (Fin.castLE hm)).det := by
    rw [← Matrix.det_submatrix_equiv_self e (gramHead hd m (cellMat N z))]
    rfl
  delta GlobalTheory.CompanionTheory.Ar.PB.gramLog ReciprocityTheory.AnForm.P.logDetFlag
  rw [hdet]

theorem contDiffAt_gramLog_cellMat (N : ℕ) (hd : Fin N → ℝ) (hd0 : ∀ k, hd k ≠ 0) (m : ℕ) (hm : m ≤ N) :
    ContDiffAt ℝ 2 (fun z : Pairs N → ℂ => gramLog hd m (cellMat N z)) 0 := by
  have hE : logDetFlag N hd m hm = fun z => 1 / 2 * Real.log |detGram N hd m hm z| :=
    logDetFlag_eq N hd m hm
  have hf : (fun z : Pairs N → ℂ => gramLog hd m (cellMat N z)) =
      fun z => 1 / 2 * Real.log (detGram N hd m hm z) := by
    funext z
    rw [gramLog_cellMat N hd m hm z, hE]
    simp only [Real.log_abs]
  rw [hf]
  obtain ⟨hC, h0, -⟩ := detGram_deriv N hd m hm
  have hne : detGram N hd m hm 0 ≠ 0 := by
    rw [h0]
    exact Finset.prod_ne_zero_iff.mpr fun a _ => hd0 _
  exact contDiffAt_const.mul (hC.contDiffAt.log hne)

theorem levi_gramLog_cellMat (N : ℕ) (hd : Fin N → ℝ) (hd0 : ∀ k, hd k ≠ 0) (m : ℕ) (hm : m ≤ N)
    (w : Pairs N → ℂ) :
    levi (fun z : Pairs N → ℂ => gramLog hd m (cellMat N z)) 0 w =
      ∑ p : Pairs N, if p.1.1.val < m ∧ m ≤ p.1.2.val then
        hd p.1.2 / (2 * hd p.1.1) * ‖w p‖ ^ 2 else 0 := by
  have hf : (fun z : Pairs N → ℂ => gramLog hd m (cellMat N z)) = logDetFlag N hd m hm := by
    funext z
    exact gramLog_cellMat N hd m hm z
  rw [hf]
  exact homDensity N hd hd0 m hm w

theorem sigForm_ne_zero (N j : ℕ) (k : Fin N) : sigForm N j k ≠ 0 := by
  delta GlobalTheory.CompanionTheory.Ar.PB.sigForm
  split_ifs <;> norm_num

theorem levi_stepPot_cell : ∀ (N j : ℕ), j ≤ N → ∀ (i : Fin N) (w : Pairs N → ℂ),
    let r : Fin N → ℕ := fun a => if (a : ℕ) < N - j then j + a else a - (N - j)
    ContDiffAt ℝ 2 (fun z : Pairs N → ℂ => stepPot N j i (cellMat N z)) 0 ∧
      levi (fun z : Pairs N → ℂ => stepPot N j i (cellMat N z)) 0 w =
        ∑ p : Pairs N, if min (r p.1.1) (r p.1.2) ≤ (i : ℕ) ∧ (i : ℕ) < max (r p.1.1) (r p.1.2)
          then (1 / 2 : ℝ) * ‖w p‖ ^ 2 else 0 := by
  intro N j hj i w
  dsimp only
  have hs := sigForm_ne_zero N j
  have hσ : ∀ k : Fin N, sigForm N j k = if (k : ℕ) < N - j then -1 else 1 := fun k => rfl
  have G : ∀ m, m ≤ N →
      ContDiffAt ℝ 2 (fun z : Pairs N → ℂ => gramLog (sigForm N j) m (cellMat N z)) 0 :=
    fun m hm => contDiffAt_gramLog_cellMat N (sigForm N j) hs m hm
  have Lv : ∀ m, m ≤ N → levi (fun z : Pairs N → ℂ => gramLog (sigForm N j) m (cellMat N z)) 0 w =
      ∑ p : Pairs N, if p.1.1.val < m ∧ m ≤ p.1.2.val then
        sigForm N j p.1.2 / (2 * sigForm N j p.1.1) * ‖w p‖ ^ 2 else 0 :=
    fun m hm => levi_gramLog_cellMat N (sigForm N j) hs m hm w
  have hi := i.2
  by_cases hij : (i : ℕ) + 1 ≤ j
  · have h1 : N - j + ((i : ℕ) + 1) ≤ N := by omega
    have h0 : N - j ≤ N := by omega
    have hfun : (fun z : Pairs N → ℂ => stepPot N j i (cellMat N z)) = fun z =>
        gramLog (sigForm N j) (N - j + ((i : ℕ) + 1)) (cellMat N z) +
          (-1) * gramLog (sigForm N j) (N - j) (cellMat N z) := by
      funext z
      delta GlobalTheory.CompanionTheory.Ar.PB.stepPot
      rw [if_pos hij]
      ring
    rw [hfun]
    refine ⟨(G _ h1).add (contDiffAt_const.mul (G _ h0)), ?_⟩
    refine (levi_add_smul (f := fun z : Pairs N → ℂ => gramLog (sigForm N j) (N - j + ((i : ℕ) + 1)) (cellMat N z))
      (g := fun z : Pairs N → ℂ => gramLog (sigForm N j) (N - j) (cellMat N z)) (-1) (G _ h1) (G _ h0) w).trans ?_
    rw [Lv _ h1, Lv _ h0, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    rcases p with ⟨⟨a, b⟩, hab⟩
    have hab' : (a : ℕ) < b := hab
    have ha := a.2
    have hb := b.2
    dsimp only
    simp only [hσ]
    split_ifs <;> first | (exfalso; omega) | norm_num | ring
  · have h1 : N - j ≤ N := by omega
    have h2 : (i : ℕ) + 1 - j ≤ N := by omega
    have hN : N ≤ N := le_refl N
    have hfun : (fun z : Pairs N → ℂ => stepPot N j i (cellMat N z)) = fun z =>
        (gramLog (sigForm N j) N (cellMat N z) + (-1) * gramLog (sigForm N j) (N - j) (cellMat N z)) +
          1 * gramLog (sigForm N j) ((i : ℕ) + 1 - j) (cellMat N z) := by
      funext z
      delta GlobalTheory.CompanionTheory.Ar.PB.stepPot
      rw [if_neg hij]
      ring
    have GA : ContDiffAt ℝ 2 (fun z : Pairs N → ℂ => gramLog (sigForm N j) N (cellMat N z) +
        (-1) * gramLog (sigForm N j) (N - j) (cellMat N z)) 0 :=
      (G _ hN).add (contDiffAt_const.mul (G _ h1))
    rw [hfun]
    refine ⟨GA.add (contDiffAt_const.mul (G _ h2)), ?_⟩
    refine (levi_add_smul (f := fun z : Pairs N → ℂ => gramLog (sigForm N j) N (cellMat N z) +
        (-1) * gramLog (sigForm N j) (N - j) (cellMat N z))
      (g := fun z : Pairs N → ℂ => gramLog (sigForm N j) ((i : ℕ) + 1 - j) (cellMat N z)) 1 GA (G _ h2) w).trans ?_
    rw [levi_add_smul (f := fun z : Pairs N → ℂ => gramLog (sigForm N j) N (cellMat N z))
      (g := fun z : Pairs N → ℂ => gramLog (sigForm N j) (N - j) (cellMat N z)) (-1) (G _ hN) (G _ h1) w]
    rw [Lv _ hN, Lv _ h1, Lv _ h2, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    rcases p with ⟨⟨a, b⟩, hab⟩
    have hab' : (a : ℕ) < b := hab
    have ha := a.2
    have hb := b.2
    dsimp only
    simp only [hσ]
    split_ifs <;> first | (exfalso; omega) | norm_num | ring

end GlobalTheory.CompanionTheory.Ar.PB
end
end

section

namespace GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Kreg

open MvPolynomial ReciprocityTheory.AnForm.R GlobalTheory.CompanionTheory.Ar.Cmp

theorem isRegularLocalRing_locRing_of_span :
    ∀ (m e : ℕ) (I : Ideal (MvPolynomial (Fin m) ℂ)) (t : Fin m → ℂ)
      (r : Fin e → MvPolynomial (Fin m) ℂ), (∀ h ∈ I, eval t h = 0) →
      ringKrullDim (locRing I t) = e →
      Ideal.span (Set.range fun l => algebraMap _ (locRing I t) (r l)) =
        Ideal.map (algebraMap _ (locRing I t)) (ptIdeal t) →
      IsRegularLocalRing (locRing I t) := by
  intro m e I t r hI hdim hspan
  obtain ⟨hloc, hnoeth⟩ := locRing_isLocalRing_isNoetherian I t hI
  haveI := hloc
  haveI := hnoeth
  have hle : I ≤ ptIdeal t := (le_ptIdeal_iff' I t).2 hI
  apply IsRegularLocalRing.of_spanFinrank_maximalIdeal_le
  rw [maximalIdeal_locRing hle, ← hspan, hdim]
  have h1 : (Set.range fun l => algebraMap (MvPolynomial (Fin m) ℂ) (locRing I t) (r l)).ncard ≤ e := by
    rw [← Set.image_univ]
    calc _ ≤ (Set.univ : Set (Fin e)).ncard := Set.ncard_image_le Set.finite_univ
      _ = e := by rw [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin]
  have h2 : (Ideal.span (Set.range fun l => algebraMap (MvPolynomial (Fin m) ℂ) (locRing I t) (r l))).spanFinrank ≤ e :=
    (Submodule.spanFinrank_span_le_ncard_of_finite (Set.finite_range _)).trans h1
  exact_mod_cast h2

end GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Kreg
end
