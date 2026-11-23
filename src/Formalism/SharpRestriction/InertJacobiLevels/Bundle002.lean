module

public import Formalism.SharpRestriction.GrowthBounds.Bundle001
public import Formalism.SharpRestriction.InertJacobiLevels.PrimeSupply
public import Formalism.SharpRestriction.LevelLetterCocycles.DataN
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalRingCardinality.SpanPowerMembership.Primes

@[expose] public section

section

noncomputable section

namespace Formalism.MainNotions.Inhab

open Formalism.MainNotions.G MvPolynomial

variable {p : ℕ} {O Kf : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]

def levAll (P : Places p O Kf) : Level P where
  Γ := (∀ v, GL (Fin (P.m + 1)) (P.Qq v)) × ℤˣ
  act := fun v => (Pi.evalMonoidHom _ v).comp (MonoidHom.fst _ _)
  χ := (Units.map ((Int.castRingHom O : ℤ →+* O) : ℤ →* O)).comp (MonoidHom.snd _ _)

variable (P : Places p O Kf)

theorem gPos_one (v : Fin P.nV) (s : Fin (P.n' v)) : P.gPos v s 1 = 1 := by
  ext a b
  by_cases h : a = b
  · subst h; simp [Places.gPos]
  · simp [Places.gPos, Matrix.one_apply_ne h]

theorem subst_one : P.subst (fun _ _ => 1) = AlgHom.id Kf P.Xsp := by
  apply MvPolynomial.algHom_ext
  rintro ⟨v, s, a, t⟩
  simp only [Places.subst, aeval_X, AlgHom.id_apply]
  rw [Finset.sum_eq_single a]
  · simp
  · intro b _ hb
    rw [Matrix.one_apply_ne (Ne.symm hb)]; simp
  · intro h; exact absurd (Finset.mem_univ _) h

theorem natAct_one : P.natAct (fun _ => 1) = LinearMap.id := by
  unfold Places.natAct
  simp only [Units.val_one, inv_one, gPos_one, Matrix.det_one, one_zpow, Finset.prod_const_one, one_smul,
    subst_one]
  rfl

def sgnEl : (levAll P).Γ := ((1 : ∀ v, GL (Fin (P.m + 1)) (P.Qq v)), (-1 : ℤˣ))

theorem smul_sgnEl (L : P.Tup) : (levAll P).smul (sgnEl P) L = L := by
  funext v
  show (L v).map ((Matrix.mulVecLin ((1 : GL (Fin (P.m + 1)) (P.Qq v)) : Matrix _ _ (P.Qq v))).restrictScalars (P.W v)) = L v
  rw [Units.val_one, Matrix.mulVecLin_one]
  exact Submodule.map_id _

theorem actX_sgnEl : (levAll P).actX (sgnEl P) = LinearMap.id := natAct_one P

theorem chi_sgnEl : (((levAll P).χ (sgnEl P) : Oˣ) : O) = -1 := by
  show ((Int.castRingHom O : ℤ →+* O) : ℤ →* O) ((-1 : ℤˣ) : ℤ) = -1
  simp

theorem levAll_funMod (h2 : (2 : Kf) ≠ 0) (Hv : P.Tup → Submodule O P.Xsp) : (levAll P).funMod Hv = ⊥ := by
  rw [eq_bot_iff]
  intro F hF
  have h := hF.2
  rw [SetLike.mem_coe, Submodule.mem_iInf] at h
  have h' := h (sgnEl P)
  rw [Submodule.mem_iInf] at h'
  rw [Submodule.mem_bot]
  funext L
  have h3 := h' L
  rw [LinearMap.mem_ker] at h3
  simp only [LinearMap.sub_apply, LinearMap.proj_apply, LinearMap.comp_apply, smul_sgnEl, actX_sgnEl, chi_sgnEl,
    neg_smul, one_smul] at h3
  have h5 : F L - -(F L) = 0 := h3
  have h4 : (2 : Kf) • F L = 0 := by rw [two_smul, ← sub_neg_eq_add]; exact h5
  exact (smul_eq_zero.mp h4).resolve_left h2

theorem levAll_M (h2 : (2 : Kf) ≠ 0) : (levAll P).M = ⊥ := levAll_funMod P h2 _

theorem gat_M_bot (G : GAtP p) (h : ∀ c, (G.lev c).M = ⊥) : G.M = ⊥ := by
  rw [eq_bot_iff]
  intro F hF
  rw [Submodule.mem_bot]
  funext c
  have := hF c (Set.mem_univ c)
  have h1 : F c ∈ (G.lev c).M := this
  rw [h c] at h1
  exact h1

theorem gat_d_zero (G : GAtP p) (h : G.M = ⊥) : G.d = 0 := by
  unfold GAtP.d
  rw [h]
  exact finrank_bot _ _

end Formalism.MainNotions.Inhab

end
end

section

noncomputable section

namespace Formalism.MainNotions.Inhab

open Formalism.BasicNotions Formalism.BasicNotions.Examples₂ Formalism.FrobeniusOrbits Formalism.TwoAdicCyclotomicDecomposition NumberField IsDedekindDomain
open scoped Pointwise

section General

variable {R : Ranks} (H : Host R)

theorem primesOver_ncard (E : Type) [Field E] [NumberField E] (p : ℕ) (hp : p.Prime) :
    (Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 E)).ncard = (placesOver E p).ncard := by
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.1 hp
  have hpI : (Ideal.span {(p : ℤ)}).IsPrime := (Ideal.span_singleton_prime hpZ.ne_zero).2 hpZ
  have hpM : (Ideal.span {(p : ℤ)}).IsMaximal :=
    hpI.isMaximal (by rw [Ne, Ideal.span_singleton_eq_bot]; exact hpZ.ne_zero)
  have himg : (fun v : HeightOneSpectrum (𝓞 E) => v.asIdeal) '' placesOver E p =
      (Ideal.span {(p : ℤ)}).primesOver (𝓞 E) := by
    ext I
    constructor
    · rintro ⟨v, hv, rfl⟩
      refine ⟨v.isPrime, ⟨?_⟩⟩
      have hle : Ideal.span {(p : ℤ)} ≤ v.asIdeal.under ℤ := by
        rw [Ideal.span_le, Set.singleton_subset_iff]
        change algebraMap ℤ (𝓞 E) p ∈ v.asIdeal
        have hv' : ((p : ℕ) : 𝓞 E) ∈ v.asIdeal := hv
        simpa using hv'
      exact hpM.eq_of_le (Ideal.IsPrime.under ℤ v.asIdeal).ne_top hle
    · rintro ⟨hI, hIl⟩
      have hmem : ((p : ℕ) : 𝓞 E) ∈ I := by
        have : (p : ℤ) ∈ I.under ℤ := by rw [← hIl.over]; exact Ideal.mem_span_singleton_self _
        simpa using this
      have hne : I ≠ ⊥ := by
        rintro rfl
        have h0 : ((p : ℕ) : 𝓞 E) = 0 := by simpa using hmem
        exact hp.ne_zero (by exact_mod_cast h0)
      exact ⟨⟨I, hI, hne⟩, hmem, rfl⟩
  rw [← himg, Set.ncard_image_of_injective _ (fun v w h => HeightOneSpectrum.ext h)]

end General

def Yof (R : Ranks) (x eps : ℝ) : ℝ := ((R.k : ℝ) * Real.exp (x ^ eps)) ^ 8

structure Fld (R : Ranks) (x eps : ℝ) extends Formalism.HC.HostAx R.toFrame where
  flPS : toHostRaw.PsQ
  sqq : E
  sqq_sq : sqq ^ 2 = -(q : E)
  gal_sqq : ∀ σ : E ≃ₐ[ℚ] E, σ sqq = ((((gal σ).1.1 : ℤˣ) : ℤ) : E) * sqq
  QS_exact : toHostRaw.Exact
  QS_le : QS ≤ R.n ^ 2
  o_pow : R.toFrame.o ^ 64 ≤ 2 ^ R.e
  small_le : ∀ l : ℕ, l.Prime → l ≠ 2 → l ∣ QS → 4 * l ≤ ⌊x ^ (eps / 5)⌋₊
  good : QDGood x eps q d
  o_tie : (R.o : ℝ) ≤ x ^ (eps / 1000)
  QS_tie : (QS : ℝ) ≤ 4 * R.n * x ^ (eps / 1000)

structure Base (R : Ranks) (x eps Cp CT : ℝ) extends Fld R x eps where
  q_big : 4 * R.t * R.r + 1 < q
  d_big : 4 * R.t * R.r + 1 < d
  g0 : ℕ
  g1 : ℕ
  first_prime_isPrime : g0.Prime
  second_prime_isPrime : g1.Prime
  g_ne : g0 ≠ g1
  first_prime_in_window : Yof R x eps ≤ g0 ∧ (g0 : ℝ) ≤ 2 * Yof R x eps
  second_prime_in_window : Yof R x eps ≤ g1 ∧ (g1 : ℝ) ≤ 2 * Yof R x eps
  first_prime_norm_form : ∃ u v : ℤ, (g0 : ℤ) = (1 + (QS * q * d : ℕ) * u) ^ 2 + d * ((QS * q * d : ℕ) * v) ^ 2
  second_prime_norm_form : ∃ u v : ℤ, (g1 : ℤ) = (1 + (QS * q * d : ℕ) * u) ^ 2 + d * ((QS * q * d : ℕ) * v) ^ 2
  bb : Disjoint (Formalism.CyclotomicNorms.BB R.r g0) (Formalism.CyclotomicNorms.BB R.r g1)
  pde : ℕ
  pde' : ℕ
  pde_prime : pde.Prime
  pde'_prime : pde'.Prime
  pde_ne : pde ≠ pde'
  pde_mod : pde ≡ 1 [MOD 15 * (QS * q * d)]
  pde'_mod : pde' ≡ 1 [MOD 15 * (QS * q * d)]
  pde_ne_g : pde ≠ g0 ∧ pde ≠ g1 ∧ pde' ≠ g0 ∧ pde' ≠ g1
  pde_log : Real.log pde < x ^ (eps / 3) ∧ Real.log pde' < x ^ (eps / 3)
  Cp_pos : 0 < Cp
  Lw : ℕ
  two_le_Lw : 2 ≤ Lw
  T2 : Finset ℕ
  second_set_range : ∀ s ∈ T2, 4 * Lw * s < R.n0
  second_set_no_relation : NoRel T2 Lw
  T2_card : (R.n0 : ℝ) * Real.exp (-(CT * Real.sqrt (Real.log (R.n0 : ℝ) * Real.log Lw))) / Lw ≤ T2.card
  TT : Finset (R.A)

variable {R : Ranks} {x eps Cp CT : ℝ} (B : Base R x eps Cp CT)

namespace Base

end Base

end Formalism.MainNotions.Inhab

end
end
