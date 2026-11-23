module

public import Development.AbelianVarietyTheory.BlockTheory.JetGauges.Bundle005
public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle002
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle016
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle034
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsLiftHermitianIsometryModLevelSelfDual
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.FirstCoordinateAdmissible
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle027
public import Mathlib.NumberTheory.NumberField.CMField
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Presheaf
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IMemSiegel
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IntMIffInt
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsStabForm
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsSystem
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsWeightedHomogeneousOfMemOrbitSpan
import Development.AbelianVarietyTheory.Definitions.ThetaValues.PolyDerivSmulLetter
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle008
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict GlobalTheory.Phase GlobalTheory.IndefiniteRowSideFullHecke.UnitaryAdjointCongruence

set_option autoImplicit false

namespace GlobalTheory.ShortMove

section Lattices

variable {E : Type} [Field E] [NumberField E] {n : ℕ}

theorem trivAt_of_dvd {Λ : GenLat E n} {a b : ℕ} (h : a ∣ b) (hT : Λ.TrivAt b) : Λ.TrivAt a := by
  obtain ⟨k, hk, h1, h2⟩ := hT
  exact ⟨k, hk.coprime_dvd_right h, h1, h2⟩

theorem entries_of_congAt {b : ℕ} {g : Matrix (Fin n) (Fin n) E} (h : UnRep.CongAt (stdLat E n) b b g) :
    ∃ t : ℕ, t.Coprime b ∧ ∃ w : Fin n → Fin n → 𝓞 E, ∀ i j,
      (t : E) * (g i j - if i = j then 1 else 0) = (b : E) * (w i j : E) := by
  obtain ⟨t, ht, hw⟩ := h
  have h1 : ∀ j : Fin n, (Pi.single j 1 : Fin n → E) ∈ stdLat E n := fun j i _ => by
    refine Submodule.mem_one.2 ?_
    by_cases hij : i = j
    · subst hij; exact ⟨1, by simp⟩
    · exact ⟨0, by simp [hij]⟩
  choose w hw1 hw2 using fun j => hw _ (h1 j)
  choose u hu using fun j i => Submodule.mem_one.1 (hw1 j i (Set.mem_univ _))
  refine ⟨t, ht, fun i j => u j i, fun i j => ?_⟩
  have := congrFun (hw2 j) i
  simp only [Pi.smul_apply, Pi.sub_apply, nsmul_eq_mul, Matrix.mulVec_single_one, Matrix.col_apply,
    Pi.single_apply, ← hu] at this
  exact this

end Lattices

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H}

theorem quot_smul {R V : Type} [CommRing R] [AddCommGroup V] [Module R V] {I : Ideal R} {a : R} (ha : a ∈ I)
    (q : V ⧸ (I • ⊤ : Submodule R V)) : a • q = 0 := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
  exact Submodule.smul_mem_smul ha trivial

theorem level_smul (q : LevQ Dw l) : (l.M : 𝓞 E) • q = 0 := by
  have h : Ideal.span {((l.M : ℕ) : 𝓞 E)} ≤ l.Mb := l.prod.symm.le.trans Ideal.mul_le_left
  exact quot_smul (h (Ideal.mem_span_singleton_self _)) q

theorem fixesDatum_of_congAt (c : Coeff l) {n b : ℕ} (hb : l.M ∣ b) {g : Matrix (Fin n) (Fin n) E}
    (h : UnRep.CongAt (stdLat E n) b b g) (w : (Fin n → LevQ Dw l) → c.F) : FixesDatum c g w := by
  obtain ⟨t, ht, u, hu⟩ := entries_of_congAt h
  rintro q q' ⟨k, G, hk, hG, hq⟩
  congr 1
  funext i
  obtain ⟨e, rfl⟩ := hb
  have hent : ∀ j, (t : 𝓞 E) * G i j =
      (if i = j then (t : 𝓞 E) * k else 0) + (k * e * u i j) * (l.M : 𝓞 E) := fun j => by
    apply RingOfIntegers.coe_injective
    have h1 := hu i j
    have h2 := hG i j
    simp only [RingOfIntegers.coe_eq_algebraMap] at h1 h2
    simp only [map_mul, map_add (f := _), map_natCast, h2, apply_ite (algebraMap (𝓞 E) E), map_zero]
    push_cast at h1
    split_ifs at h1 ⊢ <;> linear_combination (k : E) * h1
  have key : ((t : 𝓞 E) * k) • (q' i - q i) = 0 := by
    rw [smul_sub, mul_smul, hq i, Finset.smul_sum]
    simp only [smul_smul, hent, add_smul, mul_smul _ (l.M : 𝓞 E), level_smul, smul_zero, add_zero, ite_smul,
      zero_smul, Finset.sum_ite_eq, Finset.mem_univ, if_true, sub_self]
  have hco : IsCoprime ((t * k : ℕ) : 𝓞 E) (l.M : 𝓞 E) :=
    (ht.coprime_mul_right_right.mul_left hk).cast
  obtain ⟨x, y, hxy⟩ := hco
  rw [← sub_eq_zero, ← one_smul (𝓞 E) (q' i - q i), ← hxy, add_smul, mul_smul, mul_smul y, level_smul,
    Nat.cast_mul, key, smul_zero, smul_zero, add_zero]

theorem evR_mul (Xo : Moduli Dw l) (c : Coeff l) (z : c.F) (f f' : Rul Xo c)
    (hf : ∀ p y, f' p y = algebraMap c.F p.R z * f p y) {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) :
    evR Xo c f' y = algebraMap c.F S z * evR Xo c f y := by
  unfold evR evalAt
  split_ifs
  · rw [hf, map_mul, AlgHom.commutes]
  · rw [mul_zero]

section Cover

variable {Xo : Moduli Dw l} {c : Coeff l} {n : ℕ} (d : DeltaDat Xo c n)

theorem isBeta_cover (hK : KPsiIn (Dw := Dw) c) {bad : ℕ} (hb : bad ≠ 1) (Λ : GenLat E n) (hU : Λ.Unimod)
    (hT : Λ.TrivAt bad) : IsBeta Dw d.c₂ Λ (d.eF (betaH (Dw := Dw) c Λ)) := by
  have hex := GlobalTheory.betaExists_of_ne_one E H Dw l c n bad hb hK Λ hU hT
  have hs := hex.choose_spec
  have e : betaH (Dw := Dw) c Λ = hex.choose := dif_pos hex
  rw [e]
  refine ⟨by simpa using hs.1, (PlaceInt.eF_transfer E H Dw l Xo c n d Λ).1 _ hs.2.1, fun s => ?_⟩
  exact hs.2.2 (s.comp (d.eF : c.F →+* d.c₂.F))

theorem map_pushLet (g : Matrix (Fin n) (Fin n) E) (P : MvPolynomial (LtN Dw n) c.F) :
    MvPolynomial.map (d.eF : c.F →+* d.c₂.F) (pushLet c g P) =
      pushLet d.c₂ g (MvPolynomial.map (d.eF : c.F →+* d.c₂.F) P) := by
  have he : ∀ τ x, (d.eF : c.F →+* d.c₂.F) (embF c τ x) = embF d.c₂ τ x := PlaceInt.eF_embF d
  generalize (d.eF : c.F →+* d.c₂.F) = f at he ⊢
  induction P using MvPolynomial.induction_on with
  | C a => simp [pushLet]
  | add p q hp hq => simp only [map_add (f := _), hp, hq]
  | mul_X p i hp =>
    simp only [map_mul, hp, MvPolynomial.map_X]
    congr 1

    simp only [pushLet, MvPolynomial.aeval_X, letB, map_sum, map_mul, MvPolynomial.map_C, MvPolynomial.map_X, he]

end Cover

end GlobalTheory.ShortMove
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict GlobalTheory.Phase GlobalTheory.IndefiniteRowSideFullHecke.UnitaryAdjointCongruence
open GlobalTheory.AdLat GlobalTheory.UnRep

theorem _root_.GlobalTheory.T.exists_lift_hermitianIsometryModLevel_selfDual : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n m : ℕ), Algebra.Unramified (𝓞 (maximalRealSubfield E)) (𝓞 E) → 0 < m → ∀ (Λ : GenLat E n) (io : Λ.La →ₗ[𝓞 E] StdMod E n m), Λ.Unimod → IsIsomMod Λ m io → ∀ k : ℕ, 0 < k → ∃ io' : Λ.La →ₗ[𝓞 E] StdMod E n (m * k), IsIsomMod Λ (m * k) io' ∧ ∀ (v : Λ.La) (x : Fin n → 𝓞 E), (∀ j, io' v j = Ideal.Quotient.mk _ (x j)) → ∀ j, io v j = Ideal.Quotient.mk _ (x j) := by
  first | exact @GlobalTheory.IsomLift.exists_lift | exact GlobalTheory.IsomLift.exists_lift | (intros; apply GlobalTheory.IsomLift.exists_lift <;> assumption)
end

section

open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real Classical

theorem _root_.GlobalTheory.T.summable_exp_neg_trace_totallyPositive_hermitian : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Finset (E →+* ℂ)), IsType Ψ → ∀ (N c : ℕ) (δ : ℝ), 0 < c → 0 < δ → Summable fun T : {T : Matrix (Fin N) (Fin N) E // ccT T = T ∧ Den c T ∧ ∀ τ : Ψ, (T.map τ.1).PosSemidef} => Real.exp (-(δ * ∑ τ : Ψ, (T.1.map τ.1).trace.re)) := by
  first | exact @GlobalTheory.SW.summable_exp_neg_trace | exact GlobalTheory.SW.summable_exp_neg_trace | (intros; apply GlobalTheory.SW.summable_exp_neg_trace <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

namespace GlobalTheory.Dict

theorem exists_span_eq_mul_coprime {R : Type*} [CommRing R] [IsDedekindDomain R]
    (J K : Ideal R) (hJ : J ≠ ⊥) (hK : K ≠ ⊥) :
    ∃ (a : R) (A : Ideal R), a ≠ 0 ∧ Ideal.span {a} = J * A ∧ IsCoprime A K := by
  classical
  have hJK : J * K ≠ ⊥ := mul_ne_zero hJ hK

  obtain ⟨a₀, ha₀⟩ := IsDedekindDomain.exists_sup_span_eq (Ideal.mul_le_inf.trans inf_le_left : J * K ≤ J) hJK
  obtain ⟨b, hbJK, hb0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hJK

  have key : ∃ a : R, a ≠ 0 ∧ J * K ⊔ Ideal.span {a} = J := by
    by_cases h0 : a₀ = 0
    · refine ⟨b, hb0, ?_⟩
      have hJKJ : J * K = J := by simpa [h0] using ha₀
      rw [sup_eq_left.mpr (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hbJK)), hJKJ]
    · exact ⟨a₀, h0, ha₀⟩
  obtain ⟨a, ha0, ha⟩ := key
  have haJ : Ideal.span {a} ≤ J := ha ▸ le_sup_right
  obtain ⟨A, hA⟩ := Ideal.dvd_iff_le.mpr haJ
  refine ⟨a, A, ha0, hA, ?_⟩
  rw [Ideal.isCoprime_iff_sup_eq]

  have h1 : J * (K ⊔ A) = J * ⊤ := by
    rw [Ideal.mul_sup, ← hA, ha, Ideal.mul_top]
  rw [sup_comm]
  exact mul_left_cancel₀ hJ h1

theorem exists_generator_at_primes_dividing :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (𝔍 : Ideal (𝓞 E)) (M : ℕ), 𝔍 ≠ ⊥ → 0 < M → ∃ (α : 𝓞 E) (𝔞 : Ideal (𝓞 E)), α ≠ 0 ∧ Ideal.span {α} = 𝔍 * 𝔞 ∧ IsCoprime 𝔞 (Ideal.span {(M : 𝓞 E)}) := by
  intro E _ _ _ 𝔍 M h𝔍 hM
  have hK : Ideal.span {(M : 𝓞 E)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hM.ne'
  exact exists_span_eq_mul_coprime 𝔍 _ h𝔍 hK

end GlobalTheory.Dict
end
