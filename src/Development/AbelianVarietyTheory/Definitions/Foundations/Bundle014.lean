module

public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFlatSecRankZero
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormEulerPolySubOneLe
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle010
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyNormFinLeOne

@[expose] public section

section

noncomputable section

namespace GlobalTheory.FlatLine.Model

open NumberField IsDedekindDomain Module AlgebraicGeometry CategoryTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.AllWt

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l}

variable {r : ℕ} {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} {x : ℝ}

theorem sum_flatWt (τ : Psi H) :
    ∑ ρ : E →+* ℂ, ∑ i : Fin (Dw.mult ρ), (((wtOf Dw (flatWt Dw τ) 0).1 (ρ, i) : ℤ) : ℝ) = Dw.q - Dw.p := by
  classical
  have hne : τ.1 ≠ conjEmb τ.1 := fun h => conj_not_mem τ (h ▸ τ.2)
  have key : ∀ ρ : E →+* ℂ, ∑ i : Fin (Dw.mult ρ), (((wtOf Dw (flatWt Dw τ) 0).1 (ρ, i) : ℤ) : ℝ) =
      (if ρ = conjEmb τ.1 then (Dw.q : ℝ) else 0) - if ρ = τ.1 then (Dw.p : ℝ) else 0 := fun ρ => by
    by_cases h : ρ (H.rt : E) = H.rt0
    · have hm : Dw.mult ρ = Dw.p := by simp [Datum.mult, h]
      have h1 : ρ ≠ conjEmb τ.1 := fun e => conj_not_mem τ (e ▸ h)
      have h2 : ∀ i : Fin (Dw.mult ρ), (wtOf Dw (flatWt Dw τ) 0).1 (ρ, i) = if ρ = τ.1 then -1 else 0 :=
        fun i => by
          have := wtOf_big (flatWt Dw τ) 0 ⟨ρ, h⟩ i (hm ▸ i.2)
          rw [this]
          simp [flatWt, parWt, Subtype.ext_iff]
      simp only [h2]
      split_ifs <;> simp_all
    · have hm : Dw.mult ρ = Dw.q := by simp [Datum.mult, h]
      have h1 : ρ ≠ τ.1 := fun e => h (e ▸ τ.2)
      have h2 : ∀ i : Fin (Dw.mult ρ), (wtOf Dw (flatWt Dw τ) 0).1 (ρ, i) = if ρ = conjEmb τ.1 then 1 else 0 :=
        fun i => by
          have := wtOf_small (flatWt Dw τ) 0 ⟨_, conj_mem h⟩ i (hm ▸ i.2)
          simp only [GlobalTheory.AllWt.conjEmb_conjEmb] at this
          rw [this]
          by_cases e : ρ = conjEmb τ.1
          · simp [flatWt, parWt, Subtype.ext_iff, e, GlobalTheory.AllWt.conjEmb_conjEmb]
          · have : conjEmb ρ ≠ τ.1 := fun e' => e (by rw [← e', GlobalTheory.AllWt.conjEmb_conjEmb])
            simp [flatWt, parWt, Subtype.ext_iff, e, this]
      simp only [h2]
      split_ifs <;> simp_all
  simp [key]

end GlobalTheory.FlatLine.Model
end
end

section

noncomputable section

namespace GlobalTheory.LFun.Model

open NumberField IsDedekindDomain Formalism.UG GlobalTheory.PRep GlobalTheory.AdelicU
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (bcParam)

def constMap (G : Type) : ℂ →ₗ[ℂ] (G → ℂ) := LinearMap.pi fun _ => LinearMap.id

theorem constMap_injective (G : Type) [Group G] : Function.Injective (constMap G) := fun _ _ h => congrFun h 1

section Linear

variable {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ)

def rhoGL (i : Fin n) : ℂˣ := npowU w (((n : ℂ) - 1) / 2 - (i : ℕ))

theorem chiDelta_rhoGL (b : GL (Fin n) (w.adicCompletion E)) : chiDelta E w (fun i => (rhoGL w n i : ℂ)) b = 1 := by
  refine Finset.prod_eq_one fun i _ => ?_
  have hq : ((qV E w : ℕ) : ℂ) ≠ 0 := by exact_mod_cast qV_ne_zero w
  change (((qV E w : ℕ) : ℂ) ^ (((n : ℂ) - 1) / 2 - (i : ℕ))) ^ _ * _ = 1
  rw [← Complex.cpow_mul_int, ← Complex.cpow_add _ _ hq]
  convert Complex.cpow_zero _ using 2
  ring

theorem hasSatGL_trivial : HasSatGL w (Representation.trivial ℂ (GL (Fin n) (w.adicCompletion E)) ℂ) (seg w 1 n) := by
  have e : seg w 1 n = Finset.univ.val.map (rhoGL w n) := by
    rw [seg, Finset.range_val, ← Multiset.coe_range, ← List.map_coe_finRange_eq_range, Multiset.map_coe, List.map_map]
    simp only [one_mul]
    rfl
  rw [e]
  refine ⟨(Submodule.ne_bot_iff _).2 ⟨1, GlobalTheory.LGrp.mem_fixed.2 fun _ _ => rfl, one_ne_zero⟩, fun x _ h0 => ?_⟩
  refine IsSatVecGL.of_map (constMap _) (fun _ _ => rfl) (constMap_injective _)
    (isSatVecGL_of_isSpherical (fun b g k _ _ => ?_) fun h => h0 (congrFun h 1))
  rw [chiDelta_rhoGL, one_mul]; rfl

end Linear

section U

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] {σ : L →+* L} {ϖ : L} {q : ℕ}

def rhoU {q : ℕ} (hq : q ≠ 0) (n : ℕ) (i : Fin (n / 2)) : ℂˣ :=
  Units.mk0 (q : ℂ) (by exact_mod_cast hq) ^ ((n : ℤ) - 1 - 2 * (i.val : ℤ))

theorem hasSatU_trivial (hU : IsUnramInv ϖ σ q) (hq : q ≠ 0) (n : ℕ) :
    HasSatU ϖ q (Representation.trivial ℂ (GU σ n) ℂ) (rhoU hq n) := by
  refine ⟨(Submodule.ne_bot_iff _).2 ⟨1, GlobalTheory.LGrp.mem_fixed.2 fun _ _ => rfl, one_ne_zero⟩, fun x _ h0 => ?_⟩
  refine IsSatVecU.of_map hU (constMap _) (fun _ _ => rfl) (constMap_injective _)
    (isSatVecU_of_isSphericalU hU (fun b g k _ _ => ?_) fun h => h0 (congrFun h 1))
  have : chiDeltaU q (fun i => (rhoU hq n i : ℂ)) b = 1 := by
    refine Finset.prod_eq_one fun i _ => ?_
    have hq' : (q : ℂ) ≠ 0 := by exact_mod_cast hq
    split_ifs
    · simp only [rhoU, Units.val_zpow_eq_zpow_val, Units.val_mk0]
      rw [← zpow_mul, ← zpow_add₀ hq']
      convert zpow_zero _ using 2
      ring
    · rfl
  rw [this, one_mul]; rfl

end U

section Global

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {L : Submodule (𝓞 E) (Fin n → E)}
  {v : HeightOneSpectrum (𝓞 F)} {w : HeightOneSpectrum (𝓞 E)} {h : w.under (𝓞 F) = v}


end Global

end GlobalTheory.LFun.Model

end
end
