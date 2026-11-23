module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.T2SpaceTensorRatFiniteAlgebraModuleTopology
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsValuationSubringDominatingSubring
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsClosedImmersionIffPullRatio
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1464
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AlgebraicHeckeCharValuesInNumberField
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle010
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntValuationEqOfMem
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.HasProdQuadExtLocalEulerFactorInvInv
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle163
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle231
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumOrdPullbackMulResidueDegreeCodimOne
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle053
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.RelAmpleOfLocallyOnBase
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle036
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle041
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle035
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle015
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1389
import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialOfFun
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle001
import Development.AbelianVarietyTheory.Definitions.Divisors.DetJacMatCoordsEqTransitionJacobianDet
import Development.AbelianVarietyTheory.Definitions.Divisors.IsFrameOfForallExists
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle104

@[expose] public section

section

open GlobalTheory.LKTrip GlobalTheory.LKMid
open scoped TensorProduct Classical

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

namespace GlobalTheory.RatDenAwayP

theorem val_le_one (p : ℕ) (q : ℚ) (h : algebraMap ℚ (AfP p) q ∈ LevelExists.intAfP p) (v : AwayP p) :
    v.1.valuation ℚ q ≤ 1 := by
  have h1 : (algebraMap ℚ (FiniteAdeleRing ℤ ℚ) q) v.1 ∈ v.1.adicCompletionIntegers ℚ := h v
  rw [FiniteAdeleRing.algebraMap_apply, HeightOneSpectrum.mem_adicCompletionIntegers,
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] at h1
  exact h1

def primeHOS (l : ℕ) (hl : l.Prime) : HeightOneSpectrum ℤ where
  asIdeal := Ideal.span {(l : ℤ)}
  isPrime := (Ideal.span_singleton_prime (by exact_mod_cast hl.ne_zero)).2 (Nat.prime_iff_prime_int.mp hl)
  ne_bot := by
    rw [Ne, Ideal.span_singleton_eq_bot]; exact_mod_cast hl.ne_zero

theorem prime_dvd_den (p : ℕ) (q : ℚ) (h : algebraMap ℚ (AfP p) q ∈ LevelExists.intAfP p) {l : ℕ} (hl : l.Prime)
    (hd : l ∣ q.den) : l = p := by
  by_contra hne
  have hv : (primeHOS l hl).asIdeal ≠ Ideal.span {(p : ℤ)} := by
    intro e
    have e' : Ideal.span {(l : ℤ)} = Ideal.span {(p : ℤ)} := e
    rw [Ideal.span_singleton_eq_span_singleton] at e'
    have h1 : l ∣ p := Int.natCast_dvd_natCast.1 e'.dvd
    have h2 : p ∣ l := Int.natCast_dvd_natCast.1 e'.symm.dvd
    exact hne (Nat.dvd_antisymm h1 h2)
  let v : AwayP p := ⟨primeHOS l hl, hv⟩
  have hq := val_le_one p q h v
  have hden : (primeHOS l hl).valuation ℚ (algebraMap ℤ ℚ (q.den : ℤ)) < 1 := by
    rw [valuation_lt_one_iff_mem]
    show ((q.den : ℤ)) ∈ Ideal.span {(l : ℤ)}
    rw [Ideal.mem_span_singleton]; exact_mod_cast hd
  have hnum : (primeHOS l hl).valuation ℚ (algebraMap ℤ ℚ q.num) < 1 := by
    have e : algebraMap ℤ ℚ q.num = q * algebraMap ℤ ℚ (q.den : ℤ) := by
      rw [algebraMap_int_eq, eq_intCast, eq_intCast, Int.cast_natCast, Rat.mul_den_eq_num]
    rw [e, map_mul]
    calc (primeHOS l hl).valuation ℚ q * (primeHOS l hl).valuation ℚ (algebraMap ℤ ℚ (q.den : ℤ))
        ≤ 1 * (primeHOS l hl).valuation ℚ (algebraMap ℤ ℚ (q.den : ℤ)) := by gcongr
      _ < 1 := by rw [one_mul]; exact hden
  rw [valuation_lt_one_iff_mem] at hnum
  change q.num ∈ Ideal.span {(l : ℤ)} at hnum
  rw [Ideal.mem_span_singleton, Int.natCast_dvd] at hnum
  have hc : Nat.Coprime l q.den := Nat.Coprime.coprime_dvd_left hnum q.reduced
  exact (Nat.Prime.coprime_iff_not_dvd hl).1 hc hd

end GlobalTheory.RatDenAwayP

namespace GlobalTheory

theorem ratDen_pow_of_intAfP : ∀ (p : ℕ) [Fact p.Prime] (q : ℚ), algebraMap ℚ (AfP p) q ∈ LevelExists.intAfP p →
    ∃ k : ℕ, ∃ a : ℤ, ((p ^ k : ℕ) : ℚ) * q = a := by
  intro p _ q h
  have hden : q.den = p ^ q.den.primeFactorsList.length :=
    Nat.eq_prime_pow_of_unique_prime_dvd q.den_nz (fun hl hd => RatDenAwayP.prime_dvd_den p q h hl hd)
  refine ⟨q.den.primeFactorsList.length, q.num, ?_⟩
  rw [← hden]
  exact Rat.den_mul_eq_num q

end GlobalTheory
end

section

noncomputable section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum GlobalTheory.LKTrip GlobalTheory.LKMid
open scoped TensorProduct Classical RestrictedProduct

namespace GlobalTheory.AfPCpctDen

theorem natCast_mul_apply {p : ℕ} (n : ℕ) (a : AfP p) (v : AwayP p) :
    (LevelExists.rp ((n : AfP p) * a)).1 v = (n : v.1.adicCompletion ℚ) * (LevelExists.rp a).1 v :=
  rfl

theorem natCast_mem_int (v : HeightOneSpectrum ℤ) (n : ℕ) :
    (n : v.adicCompletion ℚ) ∈ v.adicCompletionIntegers ℚ :=
  natCast_mem _ n

theorem exists_nat_local (v : HeightOneSpectrum ℤ) (x : v.adicCompletion ℚ) :
    ∃ n : ℕ, 0 < n ∧ (n : v.adicCompletion ℚ) * x ∈ v.adicCompletionIntegers ℚ := by
  obtain ⟨b, hb, hbx⟩ := adicCompletion.mul_nonZeroDivisor_mem_adicCompletionIntegers v x
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  refine ⟨b.natAbs, Int.natAbs_pos.mpr hb0, ?_⟩
  rcases Int.natAbs_eq b with h | h
  · have e : ((b.natAbs : ℕ) : v.adicCompletion ℚ) = algebraMap ℤ (v.adicCompletion ℚ) b := by
      conv_rhs => rw [h]
      simp
    rw [e, mul_comm]
    exact hbx
  · have e : ((b.natAbs : ℕ) : v.adicCompletion ℚ) = -algebraMap ℤ (v.adicCompletion ℚ) b := by
      conv_rhs => rw [h]
      simp
    rw [e, neg_mul, mul_comm]
    exact neg_mem hbx

theorem exists_nat_adele {p : ℕ} (a : AfP p) :
    ∃ n : ℕ, 0 < n ∧ (n : AfP p) * a ∈ LevelExists.intAfP p := by
  choose m hm0 hm using fun v : AwayP p => exists_nat_local v.1 ((LevelExists.rp a).1 v)
  have hS : {v : AwayP p | ¬ (LevelExists.rp a).1 v ∈ v.1.adicCompletionIntegers ℚ}.Finite :=
    Filter.eventually_cofinite.mp (LevelExists.rp a).2
  refine ⟨∏ v ∈ hS.toFinset, m v, Finset.prod_pos (fun v _ => hm0 v), fun w => ?_⟩
  rw [natCast_mul_apply]
  by_cases hw : w ∈ hS.toFinset
  · obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem m hw
    rw [hk, Nat.cast_mul, mul_comm ((m w : ℕ) : w.1.adicCompletion ℚ), mul_assoc]
    exact mul_mem (natCast_mem_int w.1 k) (hm w)
  · have hw' : (LevelExists.rp a).1 w ∈ w.1.adicCompletionIntegers ℚ := by
      by_contra h
      exact hw (hS.mem_toFinset.mpr h)
    exact mul_mem (natCast_mem_int w.1 _) hw'

theorem exists_den (p : ℕ) (S : Set (AfP p)) (hS : IsCompact S) :
    ∃ D : ℕ, 0 < D ∧ ∀ a ∈ S, (D : AfP p) * a ∈ LevelExists.intAfP p := by
  choose m hm0 hm using fun a : AfP p => exists_nat_adele a
  obtain ⟨t, ht⟩ := hS.elim_finite_subcover
    (fun a => (fun x => (m a : AfP p) * x) ⁻¹' (LevelExists.intAfP p : Set (AfP p)))
    (fun a => (LevelExists.isOpen_intAfP p).preimage (continuous_const_mul _))
    (fun x _ => Set.mem_iUnion.mpr ⟨x, hm x⟩)
  refine ⟨∏ a ∈ t, m a, Finset.prod_pos (fun a _ => hm0 a), fun f hf => ?_⟩
  obtain ⟨a, ha, hfa⟩ := Set.mem_iUnion₂.mp (ht hf)
  obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem m ha
  have hfa' : (m a : AfP p) * f ∈ LevelExists.intAfP p := hfa
  rw [hk, Nat.cast_mul, mul_comm ((m a : ℕ) : AfP p), mul_assoc]
  exact mul_mem (natCast_mem _ k) hfa'

theorem main : ∀ (p : ℕ) (S : Set (AfP p)), IsCompact S → ∃ D : ℕ, 0 < D ∧ ∀ a ∈ S, (D : AfP p) * a ∈ LevelExists.intAfP p :=
  exists_den

end GlobalTheory.AfPCpctDen
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

theorem _root_.GlobalTheory.T.map_genericPoint_eq_of_algIndependent_quotients : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ) [IsIntegral (PSpace k D)] (π : X ⟶ PSpace k D), π ≫ PSpace.str k D = p → ∀ x : Fin (D + 1) → X.functionField, x 0 ≠ 0 → (∃ h : genericPoint X ∈ π ⁻¹ᵁ ProjSpace.chart k D 0, ∀ j, X.presheaf.germ (π ⁻¹ᵁ ProjSpace.chart k D 0) (genericPoint X) h (ProjSpace.pullRatio π (π ⁻¹ᵁ ProjSpace.chart k D 0) 0 le_rfl j) = x j / x 0) → Function.Injective (MvPolynomial.eval₂Hom (GlobalTheory.toFunctionField p) fun j : Fin D => x j.succ / x 0) → π (genericPoint X) = genericPoint (PSpace k D) := by
  first | exact @GlobalTheory.GenericImage.map_genericPoint_eq | exact GlobalTheory.GenericImage.map_genericPoint_eq | (intros; apply GlobalTheory.GenericImage.map_genericPoint_eq <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

theorem _root_.GlobalTheory.T.residueDegree_genericPoint_eq_finrank_quotients : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ) [IsIntegral (PSpace k D)] (π : X ⟶ PSpace k D), π ≫ PSpace.str k D = p → ∀ x : Fin (D + 1) → X.functionField, x 0 ≠ 0 → (∃ h : genericPoint X ∈ π ⁻¹ᵁ ProjSpace.chart k D 0, ∀ j, X.presheaf.germ (π ⁻¹ᵁ ProjSpace.chart k D 0) (genericPoint X) h (ProjSpace.pullRatio π (π ⁻¹ᵁ ProjSpace.chart k D 0) 0 le_rfl j) = x j / x 0) → π (genericPoint X) = genericPoint (PSpace k D) → π.residueDegree (genericPoint X) = Module.finrank (Subfield.closure (Set.range (GlobalTheory.toFunctionField p) ∪ Set.range fun j : Fin D => x j.succ / x 0)) X.functionField := by
  first | exact @GlobalTheory.GenericResidueDegree.residueDegree_eq_finrank_quotients | exact GlobalTheory.GenericResidueDegree.residueDegree_eq_finrank_quotients | (intros; apply GlobalTheory.GenericResidueDegree.residueDegree_eq_finrank_quotients <;> assumption)
end

section

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host

namespace GlobalTheory.EtaValues

section General

variable {L : Type} [Field L] [NumberField L]

def hv (χ : HChar L) (v : HeightOneSpectrum (𝓞 L)) : ℂ :=
  ((χ.val v : ℂˣ) : ℂ) * (((Real.sqrt (Ideal.absNorm v.asIdeal : ℝ))⁻¹ : ℝ) : ℂ)

theorem absNorm_pos (v : HeightOneSpectrum (𝓞 L)) : (0 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ) := by
  exact_mod_cast Nat.pos_of_ne_zero (mt Ideal.absNorm_eq_zero_iff.1 v.ne_bot)

theorem hv_ne_zero (χ : HChar L) (v : HeightOneSpectrum (𝓞 L)) : hv χ v ≠ 0 :=
  mul_ne_zero (Units.ne_zero _) (Complex.ofReal_ne_zero.2 (inv_ne_zero (Real.sqrt_pos.2 (absNorm_pos v)).ne'))

theorem valTw_eq (χ : HChar L) (v : HeightOneSpectrum (𝓞 L)) : χ.valTw (1 / 2) v = hv χ v := by
  unfold HChar.valTw hv
  congr 1
  rw [Real.sqrt_eq_rpow, ← Real.rpow_neg (Nat.cast_nonneg _), Complex.ofReal_cpow (Nat.cast_nonneg _),
    Complex.ofReal_natCast, Complex.ofReal_neg]


open Classical in
def cnt (a : 𝓞 L) (v : HeightOneSpectrum (𝓞 L)) : ℕ :=
  (Associates.mk v.asIdeal).count (Associates.mk (Ideal.span {a} : Ideal (𝓞 L))).factors

theorem intValuation_eq {a : 𝓞 L} (ha : a ≠ 0) (v : HeightOneSpectrum (𝓞 L)) :
    v.intValuation a = WithZero.exp (-(cnt a v : ℤ)) := by
  rw [HeightOneSpectrum.intValuation_if_neg _ ha]
  rfl

theorem ordF_eq {a : 𝓞 L} (ha : a ≠ 0) (v : HeightOneSpectrum (𝓞 L)) : ordF v (GlobalTheory.Mem.ValAlg.uOf a ha) = cnt a v := by
  show -WithZero.log (v.valuation L (algebraMap (𝓞 L) L a)) = _
  rw [HeightOneSpectrum.valuation_of_algebraMap, intValuation_eq ha]
  simp

theorem cnt_eq_zero {a : 𝓞 L} (ha : a ≠ 0) {v : HeightOneSpectrum (𝓞 L)} (h : a ∉ v.asIdeal) : cnt a v = 0 := by
  have h1 := intValuation_eq ha v
  rw [HeightOneSpectrum.intValuation_eq_one_iff.2 h, ← WithZero.exp_zero, WithZero.exp_inj] at h1
  omega

theorem prod_hv (hL : IsTotallyComplex L) {I : Type} [Fintype I] (φ : I → L →+* ℂ)
    (hφ : Function.Bijective fun i => InfinitePlace.mk (φ i)) (χ : HChar L) (hu : ∀ v, χ.UnrAt v)
    (hinf : χ.HasInf φ fun _ => 1) {a : 𝓞 L} (ha : a ≠ 0) (U : Finset (HeightOneSpectrum (𝓞 L)))
    (hU : ∀ v, a ∈ v.asIdeal → v ∈ U) :
    ∏ v ∈ U, hv χ v ^ cnt a v = (∏ i, φ i (algebraMap (𝓞 L) L a))⁻¹ := by
  classical
  have h0 : ∀ v, v ∉ U → cnt a v = 0 := fun v h => cnt_eq_zero ha (mt (hU v) h)
  have hp := GlobalTheory.TypeValues.productRule χ ∅ (fun v _ => hu v) (GlobalTheory.Mem.ValAlg.uOf a ha)
  have e1 : ∀ v, (∏ᶠ (_ : v ∉ (∅ : Finset (HeightOneSpectrum (𝓞 L)))), χ.val v ^ ordF v (GlobalTheory.Mem.ValAlg.uOf a ha)) =
      χ.val v ^ cnt a v := fun v => by
    rw [finprod_eq_if, if_pos (Finset.notMem_empty v), ordF_eq, zpow_natCast]
  simp_rw [e1] at hp
  rw [Finset.prod_empty, mul_one, finprod_eq_prod_of_mulSupport_subset (s := U) _ (fun v hv' => by
    by_contra h
    exact hv' (by simp only [h0 v h, pow_zero]))] at hp
  have hp' := congrArg (Units.val : ℂˣ → ℂ) hp
  rw [Units.val_mul, hinf, Units.val_one, Units.coe_prod] at hp'
  have hf := Ideal.finprod_heightOneSpectrum_factorization (I := Ideal.span {a}) (by simpa using ha)
  rw [finprod_eq_prod_of_mulSupport_subset (s := U) _ (fun v hv' => by
    by_contra h
    refine hv' ?_
    show v.asIdeal ^ cnt a v = 1
    rw [h0 v h, pow_zero])] at hf
  have hN := GlobalTheory.Mem.ValAlg.absNorm_eq hL φ hφ a
  rw [← hf, map_prod, Nat.cast_prod] at hN
  have hN' : ∏ v ∈ U, Real.sqrt (Ideal.absNorm v.asIdeal : ℝ) ^ cnt a v = ∏ i, ‖φ i (algebraMap (𝓞 L) L a)‖ := by
    refine (pow_left_inj₀ (Finset.prod_nonneg fun _ _ => by positivity) (Finset.prod_nonneg fun _ _ => norm_nonneg _)
      two_ne_zero).1 ?_
    rw [← hN, ← Finset.prod_pow]
    refine Finset.prod_congr rfl fun v _ => ?_
    rw [← pow_mul, mul_comm, pow_mul, Real.sq_sqrt (Nat.cast_nonneg _)]
    show _ = ((Ideal.absNorm (v.asIdeal ^ cnt a v) : ℕ) : ℝ)
    rw [map_pow, Nat.cast_pow]
  refine eq_inv_of_mul_eq_one_right ?_
  rw [← hp']
  unfold hv
  simp_rw [mul_pow, Finset.prod_mul_distrib, zpow_one, Finset.prod_div_distrib, Units.val_pow_eq_pow_val,
    ← Complex.ofReal_pow, ← Complex.ofReal_prod, inv_pow, Finset.prod_inv_distrib, hN', Complex.ofReal_inv]
  show _ = (∏ i, φ i (algebraMap (𝓞 L) L a)) / ((∏ i, ‖φ i (algebraMap (𝓞 L) L a)‖ : ℝ) : ℂ) * _
  ring

theorem hv_mem (hL : IsTotallyComplex L) {I : Type} [Fintype I] (φ : I → L →+* ℂ)
    (hφ : Function.Bijective fun i => InfinitePlace.mk (φ i)) (χ : HChar L) (hu : ∀ v, χ.UnrAt v)
    (hinf : χ.HasInf φ fun _ => 1) (M : Subfield ℂ) (hM : ∀ i x, φ i x ∈ M) (S : Finset (HeightOneSpectrum (𝓞 L)))
    (hS : ∀ v, v ∉ S → hv χ v ∈ M) (P : HeightOneSpectrum (𝓞 L)) : hv χ P ∈ M := by
  classical
  by_cases hP : P ∈ S
  swap
  · exact hS P hP
  obtain ⟨b, hb1, hb2⟩ : ∃ b ∈ P.asIdeal, b ∉ P.asIdeal ^ 2 := by
    have := Ideal.pow_succ_lt_pow P.ne_bot 1 (P := P.asIdeal)
    rw [pow_one] at this
    exact SetLike.exists_of_lt this
  obtain ⟨a, ha⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal (s := S) (fun v => v.asIdeal) (fun _ => 2)
    (fun v _ => v.prime) (fun v _ w _ h h' => h (HeightOneSpectrum.ext h')) (fun v => if v.1 = P then b else 1)
  have haP := ha P hP
  rw [if_pos rfl] at haP
  have ha2 : a ∉ P.asIdeal ^ 2 := fun h => hb2 (by simpa using (P.asIdeal ^ 2).sub_mem h haP)
  have ha1 : a ∈ P.asIdeal := by simpa using P.asIdeal.add_mem (Ideal.pow_le_self two_ne_zero haP) hb1
  have ha0 : a ≠ 0 := by rintro rfl; exact ha2 (zero_mem _)
  have hc : cnt a P = 1 := by
    have h1 := intValuation_eq ha0 P
    rw [GlobalTheory.TypeValues.intValuation_eq_of_mem ha1 ha2, WithZero.exp_inj] at h1
    omega
  have hfin : {v : HeightOneSpectrum (𝓞 L) | v.asIdeal ∣ Ideal.span {a}}.Finite :=
    Ideal.finite_factors (by simpa using ha0)
  have hU : ∀ v, a ∈ v.asIdeal ↔ v ∈ hfin.toFinset := fun v => by
    rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq, Ideal.dvd_span_singleton]
  have h := prod_hv hL φ hφ χ hu hinf ha0 hfin.toFinset fun v => (hU v).1
  rw [← Finset.mul_prod_erase _ _ ((hU P).1 ha1), hc, pow_one] at h
  rw [eq_div_of_mul_eq (Finset.prod_ne_zero_iff.2 fun v _ => pow_ne_zero _ (hv_ne_zero χ v)) h]
  refine div_mem (inv_mem (prod_mem fun i _ => hM i _)) (prod_mem fun v hv' => pow_mem (hS v fun hvS => ?_) _)
  obtain ⟨hvP, hva⟩ := Finset.mem_erase.1 hv'
  have h1 := ha v hvS
  rw [if_neg hvP] at h1
  refine v.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 ?_)
  simpa using v.asIdeal.sub_mem ((hU v).2 hva) (Ideal.pow_le_self two_ne_zero h1)

theorem hv_mem_of_inert {F : Type} [Field F] [NumberField F] [Algebra F L] (χ : HChar L) (hr : χ.ResEta F)
    {v : HeightOneSpectrum (𝓞 L)} (hu : χ.UnrAt v) (ho : ∀ k : Fˣ, ordF v (upF F k) = ordF (v.under (𝓞 F)) k)
    (h1 : ((v.under (𝓞 F)).asIdeal.primesOver (𝓞 L)).ncard = 1)
    (hN : Ideal.absNorm v.asIdeal = Ideal.absNorm (v.under (𝓞 F)).asIdeal ^ 2) (M : Subfield ℂ) : hv χ v ∈ M := by
  have hab : aboveF (L := L) F (v.under (𝓞 F)) = {v} := by
    obtain ⟨Q, hQ⟩ := Set.ncard_eq_one.1 h1
    have key : ∀ w : HeightOneSpectrum (𝓞 L), w.under (𝓞 F) = v.under (𝓞 F) → w.asIdeal = Q := fun w hw => by
      have : w.asIdeal ∈ (v.under (𝓞 F)).asIdeal.primesOver (𝓞 L) := ⟨w.isPrime, ⟨by rw [← hw]; rfl⟩⟩
      rwa [hQ] at this
    ext P
    rw [aboveF, Set.Finite.mem_toFinset, Finset.mem_singleton]
    exact ⟨fun h => HeightOneSpectrum.ext ((key P h).trans (key v rfl).symm), fun h => by rw [h]; rfl⟩
  have hval : ∀ {K : Type} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) (k : Kˣ),
      IsUnifAt w (atFin w k) ↔ ordF w k = 1 := by
    intro K _ _ w k
    have h : Valued.v ((atFin w k : (w.adicCompletion K)ˣ) : w.adicCompletion K) = w.valuation K (k : K) :=
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w (k : K)
    have h0 : w.valuation K (k : K) ≠ 0 := (Valuation.ne_zero_iff _).2 k.ne_zero
    unfold IsUnifAt ordF
    rw [h, ← WithZero.exp_log h0, WithZero.exp_inj, WithZero.log_exp]
    omega
  have hk := (hval _ _).1 (unif_spec (v.under (𝓞 F)))
  have h := hr.1 (v.under (𝓞 F)) (unif (v.under (𝓞 F)))
  rw [HChar.resFin, etaFin, hab, Finset.prod_singleton, MonoidHom.comp_apply, if_pos (Finset.card_singleton _), hk, zpow_one] at h
  have h2 : χ.val v = -1 := (χ.val_eq hu _ ((hval _ _).2 ((ho _).trans hk))).symm.trans h
  unfold hv
  rw [h2, hN, Nat.cast_pow, Real.sqrt_sq (Nat.cast_nonneg _), Complex.ofReal_inv, Complex.ofReal_natCast, Units.val_neg,
    Units.val_one]
  exact mul_mem (neg_mem (one_mem _)) (inv_mem (natCast_mem _ _))

end General

end GlobalTheory.EtaValues

end

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature
open scoped TensorProduct InnerProductSpace
open GlobalTheory.GalLift

namespace GlobalTheory.EtaValues

open _root_.Formalism.L2.Col

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem hv_mem_host (D : D7) (χ : Formalism.L2.Host.HChar D.host.E) (hχ : Formalism.L2.Host.IsEtaT D.host χ) (T : Finset (Pl D.host.E))
    (hT : ∀ v, Bridge.SplitOff v (T : Set (Pl D.host.E)) → hv χ v ∈ D.what₂.embLL.fieldRange) (P : Pl D.host.E) :
    hv χ P ∈ D.what₂.embLL.fieldRange := by
  classical
  obtain ⟨c, -, hcm, ho, -⟩ := GlobalTheory.Mem.HostCM.host_cm D.R D.host
  refine hv_mem hcm.cplx _ hcm.bij χ hχ.unr hχ.inf D.what₂.embLL.fieldRange (fun g x => ⟨D.embE (D.host.sigmaOf g x),
    DFunLike.congr_fun D.embE_φ₀ (D.host.sigmaOf g x)⟩) (T ∪ T.image conjPrime₂) (fun v hv' => ?_) P
  by_cases hc : Formalism.HermitianLatticesTheory.conjIdeal (K := D.host.E) v.asIdeal = v.asIdeal
  · have hm : v.asIdeal ∈ (v.under (𝓞 D.host.F)).asIdeal.primesOver (𝓞 D.host.E) := ⟨v.isPrime, ⟨rfl⟩⟩
    rcases GlobalTheory.EtaEulerProduct.inert_or_split (σ := D.sp.cm.sig)
      ⟨D.sp.cm.totReal, D.sp.cm.cmUnram.1, D.sp.cm.deg2, fun τ x => D.sp.cm.cmUnram.2.1 τ x⟩ (fun _ => rfl)
      D.sp.cm.cmUnram (v.under (𝓞 D.host.F)) with ⟨-, h1, h2⟩ | ⟨-, -, h2⟩
    · exact hv_mem_of_inert χ hχ.res (hχ.unr v) (ho v) h1 (h2 _ hm).2 _
    · exact absurd hc (h2 _ hm).1
  · exact hT v ⟨hc, fun h => hv' (Finset.mem_union_left _ h), fun w hw h => hv' (Finset.mem_union_right _ (Finset.mem_image.2
      ⟨w, hw, by
        rw [show w = conjPrime₂ v from HeightOneSpectrum.ext (h.trans (conjIdeal_asIdeal v))]
        exact HeightOneSpectrum.ext (Ideal.ext fun a => by rw [mem_conjP, mem_conjP, cO_cO])⟩))⟩

theorem splitOff_mono {D : D7} {v : Pl D.host.E} {S S' : Set (Pl D.host.E)} (h : Bridge.SplitOff v S) (hS : S' ⊆ S) :
    Bridge.SplitOff v S' :=
  ⟨h.1, fun h' => h.2.1 (hS h'), fun w hw => h.2.2 w (hS hw)⟩

end GlobalTheory.EtaValues

end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

theorem _root_.GlobalTheory.T.finsum_ord_pullback_mul_residueDegree_codim_one : ∀ (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] [IsLocallyNoetherian X] [IsLocallyNoetherian Y] (π : Y ⟶ X) (hη : π (genericPoint Y) ⤳ genericPoint X) (z : X), Order.coheight z = 1 → (∃ U : X.Opens, z ∈ U ∧ IsFinite (π ∣_ U)) → ∀ f : X.functionField, f ≠ 0 → ∑ᶠ (w : Y) (_ : π w = z), Scheme.ord (TrueGeo.SmallSec.fnMap π hη f) w * (π.residueDegree w : ℤ) = (π.residueDegree (genericPoint Y) : ℤ) * Scheme.ord f z := by
  first | exact @GlobalTheory.OrdPush.finsum_ord_fnMap_mul_residueDegree | exact GlobalTheory.OrdPush.finsum_ord_fnMap_mul_residueDegree | (intros; apply GlobalTheory.OrdPush.finsum_ord_fnMap_mul_residueDegree <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB
open MonoidalCategory CartesianMonoidalCategory MonObj Limits
open scoped CategoryTheory.Obj
open GlobalTheory.CechPic (Pic cls lam)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RigidTranslate

open GlobalTheory.CoordToExt GlobalTheory.PolTranslate

variable {S : Scheme.{0}} {A : Over S} [GrpObj A]

theorem transl_transl_inv (t : 𝟙_ (Over S) ⟶ A) : transl t ≫ transl t⁻¹ = 𝟙 A := by
  rw [GlobalTheory.PolTranslate.comp_transl, transl, _root_.mul_assoc, ← MonObj.comp_mul, _root_.mul_inv_cancel,
    MonObj.comp_one, _root_.mul_one]

theorem transl_inv_transl (t : 𝟙_ (Over S) ⟶ A) : transl t⁻¹ ≫ transl t = 𝟙 A := by
  rw [GlobalTheory.PolTranslate.comp_transl, transl, _root_.mul_assoc, ← MonObj.comp_mul, _root_.inv_mul_cancel,
    MonObj.comp_one, _root_.mul_one]

instance isIso_transl_left (t : 𝟙_ (Over S) ⟶ A) : IsIso (transl t).left :=
  ⟨⟨(transl t⁻¹).left, congrArg (fun q => q.left) (transl_transl_inv t),
    congrArg (fun q => q.left) (transl_inv_transl t)⟩⟩

theorem relAmple_rigTransl_of_section [IsAffine S] [IsProper A.hom] {L : LB A.left} (t : 𝟙_ (Over S) ⟶ A)
    (hL : L.IsLB) (h : Out.RelAmple A L) : Out.RelAmple A (rigTransl L t) := by
  have hL' : (rigTransl L t).IsLB := DVR.linComb_isLB _ hL _ _
  refine AmpleLocal.relAmple_of_locally S A _ hL' inferInstance inferInstance fun s => ?_
  let t₀ : S ⟶ A.left := t.left
  obtain ⟨i, hi⟩ := exists_chart hL (t₀ s)
  let U : S.Opens := t₀ ⁻¹ᵁ L.U i
  refine ⟨U, hi, ?_⟩
  have hp : IsPullback (transl t).left A.hom A.hom (𝟙 _) :=
    IsPullback.of_horiz_isIso ⟨(Over.w _).trans (Category.comp_id _).symm⟩
  have H := (isPullback_morphismRestrict A.hom U).flip.paste_horiz hp
  have k : (toUnit A ≫ t).left = A.hom ≫ t₀ := rfl
  obtain ⟨w, hw⟩ := lbIso_diff_pull hL (transl t).left (toUnit A ≫ t).left (A.hom ⁻¹ᵁ U).ι i fun z => by
    rw [k]; exact z.2
  exact relAmple_pull (A' := Over.mk (A.hom ∣_ U)) H hL (pull_isLB hL' _) ((isGen_iff w).1 hw) ⊤
    (isAffineOpen_top _) (fun _ => trivial) h

theorem relAmple_rigTransl_point : ∀ (K : Type) [Field K] (B : Over (Sp K)) [GrpObj B], IsAbelianScheme B →
    ∀ (L : LB B.left), L.IsLB → ∀ a : 𝟙_ (Over (Sp K)) ⟶ B, Out.RelAmple B L →
      Out.RelAmple B (GlobalTheory.RigidTranslate.rigTransl L a) := by
  intro K _ B _ hB L hL a h
  have := hB.proper
  exact relAmple_rigTransl_of_section a hL h

end GlobalTheory.RigidTranslate
end
