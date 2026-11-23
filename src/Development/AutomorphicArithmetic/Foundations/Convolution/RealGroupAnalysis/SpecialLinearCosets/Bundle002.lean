module

public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.SplitAt
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnitaryActions.Bundle001
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.SpecialLinearCosets.GoodU

@[expose] public section

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.H UpperTheory.ConvolutionTheory.R2.I
open scoped Classical

private theorem tendsto_pow_zero_of_valuation {K : Type} [Field K] [NumberField K] (v : P K) (y : Kv v)
    (hy : Valued.v y < 1) : Tendsto (fun n : ℕ => y ^ n) atTop (𝓝 0) := by
  rw [(Valued.hasBasis_nhds_zero (Kv v) _).tendsto_right_iff]
  intro γ _
  obtain ⟨n, hn⟩ := exists_pow_lt₀ hy (Units.map (MonoidWithZeroHom.ValueGroup₀.embedding (f := ((Valued.v : Valuation (Kv v) (WithZero (Multiplicative ℤ))) : Kv v →*₀ WithZero (Multiplicative ℤ)))).toMonoidHom γ)
  filter_upwards [eventually_ge_atTop n] with m hm
  simp only [Set.mem_setOf_eq, Valuation.restrict_lt_iff_lt_embedding]
  rw [map_pow]
  exact lt_of_le_of_lt (pow_le_pow_right_of_le_one' hy.le hm) hn

private theorem valuation_lt_one_of_tendsto {K : Type} [Field K] [NumberField K] (v : P K) (y : Kv v)
    (hy : Tendsto (fun n : ℕ => y ^ n) atTop (𝓝 0)) : Valued.v y < 1 := by
  have h1 := (Valued.hasBasis_nhds_zero (Kv v) _).mem_of_mem (i := 1) trivial
  obtain ⟨n, hn⟩ := (hy.eventually h1 |>.and (eventually_gt_atTop 0)).exists
  obtain ⟨hn1, hn0⟩ := hn
  simp only [Set.mem_setOf_eq, Units.val_one, Valuation.restrict_lt_one_iff] at hn1
  rw [map_pow] at hn1
  by_contra hc
  exact absurd hn1 (not_lt.mpr (one_le_pow₀ (not_lt.mp hc)))

theorem UpperTheory.ConvolutionTheory.R2.I.below :
    ∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] (v : P K) (w : P L) (i : Kv v →+* Kv w),
      Continuous i → (∀ x : K, i (algebraMap K _ x) = algebraMap L _ (algebraMap K L x)) → Below v w := by
  intro K L _ _ _ _ _ v w i hi hx
  have hle : v.asIdeal ≤ w.asIdeal.comap (algebraMap (𝓞 K) (𝓞 L)) := by
    intro x hxv
    rw [Ideal.mem_comap]
    have h1 : Valued.v (algebraMap K (Kv v) (x : K)) < 1 := by
      have := (v.valuation_lt_one_iff_mem (K := K) x).mpr hxv
      rwa [← HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] at this
    have h2 := tendsto_pow_zero_of_valuation v _ h1
    have h3 : Tendsto (fun n : ℕ => (i (algebraMap K (Kv v) (x : K))) ^ n) atTop (𝓝 0) := by
      have := (hi.tendsto 0).comp h2
      simpa [Function.comp_def, map_pow] using this
    have h4 := valuation_lt_one_of_tendsto w _ h3
    rw [hx] at h4
    have h5 : algebraMap K L (x : K) = ((algebraMap (𝓞 K) (𝓞 L) x : 𝓞 L) : L) := rfl
    rw [h5] at h4
    apply (w.valuation_lt_one_iff_mem (K := L) _).mp
    rwa [← HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
  exact v.isMaximal.eq_of_le (Ideal.comap_ne_top _ w.isPrime.ne_top) hle
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.H UpperTheory.ConvolutionTheory.R2.I
open scoped Classical

private theorem fst_detFin {E : Type} [Field E] [NumberField E] (k : GL (Fin 2) (Af E)) :
    (((Matrix.GeneralLinearGroup.det (finGL E 2 k) : (A E)ˣ) : A E)).1 = 1 := by
  have h := GlobalTheory.CuspRep.det_map (RingHom.fst (InfiniteAdeleRing E) (Af E)) (finGL E 2 k)
  have h1 : Matrix.GeneralLinearGroup.map (RingHom.fst (InfiniteAdeleRing E) (Af E)) (finGL E 2 k) = 1 :=
    map_cornerGL_of_zero _ _ (fun _ => rfl) k
  rw [h1] at h
  refine h.symm.trans ?_
  simp

private theorem fst_norm {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (D : Dat F E) (z : (A E)ˣ) (hz : (z : A E).1 = 1) :
    ((GroundTheory.Global.ideleNorm F E z : (A F)ˣ) : A F).1 = 1 := by
  let e : A F := ((1, 0) : InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F)
  have h1 : am E e * (z : A E) = am E e := by
    have hi1 : (am E e).1 = 1 := map_one (GroundTheory.Global.InfinitePlace.infiniteAdeleRingMap (K := F) (L := E))
    have hi2 : (am E e).2 = 0 := map_zero (AdeleBaseChange.finiteAdeleMap F E)
    refine Prod.ext ?_ ?_
    · change (am E e).1 * (z : A E).1 = (am E e).1
      rw [hz, mul_one]
    · change (am E e).2 * (z : A E).2 = (am E e).2
      rw [hi2, zero_mul]
  have h2 := congrArg D.co h1
  rw [D.co_am_mul, ← D.mkE_base, D.co_mkE] at h2
  have hu : e * D.co z 0 = e := congrFun h2 0
  have ht : e * D.co z 1 = 0 := congrFun h2 1
  have hu1 : (D.co z 0).1 = 1 := by
    have h := congrArg Prod.fst hu
    change (1 : InfiniteAdeleRing F) * (D.co z 0).1 = 1 at h
    rwa [one_mul] at h
  have ht1 : (D.co z 1).1 = 0 := by
    have h := congrArg Prod.fst ht
    change (1 : InfiniteAdeleRing F) * (D.co z 1).1 = 0 at h
    rwa [one_mul] at h
  rw [D.coe_ideleNorm]
  change (D.co z 0).1 ^ 2 - (rt D.δ : A F).1 * (D.co z 1).1 ^ 2 = 1
  rw [hu1, ht1]
  simp

theorem UpperTheory.ConvolutionTheory.R2.I.locSm :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (π : TR.CuspSub F 2) (v : P F),
      (∀ f, IsOpen {g | π.locRep v g f = f}) ∧ (∀ x (f : π.V) g, (π.locRep v x f).1.1 g = f.1.1 (g * lc v x)) ∧
      ∀ (E : Type) [Field E] [NumberField E] [Algebra F E] (_ : Dat F E) (k : GL (Fin 2) (Af E)), ∀ f ∈ π.V,
        ∃ f' ∈ π.V, f'.1 = fun g => f.1 (g * dM (nu F (finGL E 2 k))) := by
  intro F _ _ _ π v
  refine ⟨fun f => ?_, fun x f g => rfl, ?_⟩
  · have e : {g | π.locRep v g f = f} = locGL F 2 v ⁻¹' {k | TR.finRep F 2 k f.1 = f.1} := by
      ext g
      exact Subtype.ext_iff
    rw [e]
    exact (π.cusp f.1 f.2).1.level.preimage (CuspSub.continuous_locGL v)
  · intro E _ _ _ D k f hf
    have h1 : ((nu F (finGL E 2 k) : (A F)ˣ) : A F).1 = 1 := fst_norm D _ (fst_detFin k)
    generalize nu F (finGL E 2 k) = t at h1
    have hp : TR.pInf F (t : A F) = 1 := by
      change (TR.infEq F).symm (t : A F).1 = 1
      rw [h1]
      exact map_one _
    have hinf : Matrix.GeneralLinearGroup.map (TR.pInf F) (dM t) = 1 := by
      apply Units.ext
      ext i j
      fin_cases i <;> fin_cases j <;> simp [dM, hp]
    have hd : finGL F 2 (Matrix.GeneralLinearGroup.map (pFin F) (dM t)) = dM t := by
      have h := TR.infGL_mul_finGL (dM t)
      rwa [hinf, map_one, one_mul] at h
    refine ⟨_, π.stable (.fin (Matrix.GeneralLinearGroup.map (pFin F) (dM t))) f hf, ?_⟩
    funext g
    change f.1 (g * finGL F 2 _) = f.1 (g * dM t)
    rw [hd]
end
