module

public import Formalism.ConjugateSelfDual.Bundle001
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle035
public import Formalism.CyclotomicNorms.StatementT
public import Formalism.GradedWeylDivisibility.StatementA
public import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IdeleClassFiniteness.Bundle001
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentApproximation.AddDense
public import Formalism.SatakeDualWeyl.Statement
public import Formalism.FormalDegreeBessel.StatementG
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle037
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.MeasureTheory.Group.FundamentalDomain
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle007
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfCoefficientsSeparatingCharactersEqZero
public import Mathlib.MeasureTheory.Integral.CircleIntegral
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle038
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle036
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Compactness.Paracompact
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.GeneralLinearIntegers.AlgebraMapIntMemOint

@[expose] public section

section

open NumberField IsDedekindDomain

theorem _root_.GlobalTheory.T.exists_zeta_pow_close_to_unit_zpow : ∀ {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    (P : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω) (ζ : Ω),
    Formalism.ConjugateSelfDual.IsPlaceOver A P → IsPrimitiveRoot ζ (Formalism.ConjugateSelfDual.normV P - 1) → ∀ (u : 𝓞 E) (e : ℤ), u ∉ P.asIdeal →
    ∃ a : ℕ, A.valuation (ζ ^ a - (algebraMap E Ω (u : E)) ^ e) < 1 := by
  first | exact @GlobalTheory.TamePowTeich.exists_zeta_pow_close | exact GlobalTheory.TamePowTeich.exists_zeta_pow_close | (intros; apply GlobalTheory.TamePowTeich.exists_zeta_pow_close <;> assumption)
end

section

open Polynomial

theorem _root_.GlobalTheory.T.fbar_exists_complexAut_comp_eq : ∀ (g : ℕ) [Fact g.Prime] (t t' : Formalism.CyclotomicNorms.Fbar g →* ℂ), (∀ x y : Formalism.CyclotomicNorms.Fbar g, x ≠ 0 → y ≠ 0 → t x = t y → x = y) → (∀ x y : Formalism.CyclotomicNorms.Fbar g, x ≠ 0 → y ≠ 0 → t' x = t' y → x = y) → ∃ σ : ℂ ≃+* ℂ, ∀ x, σ (t' x) = t x := by
  first | exact @GlobalTheory.TeichGalois.exists_ringEquiv_comp_eq | exact GlobalTheory.TeichGalois.exists_ringEquiv_comp_eq | (intros; apply GlobalTheory.TeichGalois.exists_ringEquiv_comp_eq <;> assumption)
end

section

noncomputable section

namespace GlobalTheory.Mem.CanonicalSurjection

open MvPolynomial

def bideterminantFunctionsOfShape (K : Type) [CommRing K] (N : ℕ) (ν : Fin N → ℕ) : Set (Matrix (Fin N) (Fin N) K → K) :=
  {g | ∃ (Kc : ℕ) (sz : Fin Kc → ℕ) (hsz : ∀ k, sz k ≤ N) (I : ∀ k, Fin (sz k) → Fin N),
    Formalism.GradedWeylDivisibility.shapeDeg sz = ν ∧ (∀ k, StrictMono (I k)) ∧
      g = fun Y => eval (fun v : Fin N × Fin N => Y v.1 v.2) (Formalism.GradedWeylDivisibility.bideterminant K sz hsz I)}

end GlobalTheory.Mem.CanonicalSurjection
end
end

section

open IsDedekindDomain NumberField

namespace GlobalTheory.LevelChars

variable (L : Type) [Field L] [NumberField L]

def compAt (v : HeightOneSpectrum (𝓞 L)) (a : (AdeleRing (𝓞 L) L)ˣ) : v.adicCompletion L :=
  (a : AdeleRing (𝓞 L) L).2 v

theorem compAt_mul (v : HeightOneSpectrum (𝓞 L)) (a b : (AdeleRing (𝓞 L) L)ˣ) :
    compAt L v (a * b) = compAt L v a * compAt L v b := rfl

theorem compAt_one (v : HeightOneSpectrum (𝓞 L)) : compAt L v 1 = 1 := rfl

def levSub (S : Set (HeightOneSpectrum (𝓞 L))) (N : ℕ) : Subgroup (AdeleRing (𝓞 L) L)ˣ where
  carrier := {a | ∀ v, Valued.v (compAt L v a) = 1 ∧ (v ∈ S → Valued.v (compAt L v a - 1) ≤ WithZero.exp (-(N : ℤ)))}
  one_mem' := fun v => by
    refine ⟨by rw [compAt_one, map_one], fun _ => ?_⟩
    rw [compAt_one, sub_self, map_zero]
    exact zero_le
  mul_mem' := fun {a b} ha hb v => by
    rw [compAt_mul]
    refine ⟨by rw [map_mul, (ha v).1, (hb v).1, one_mul], fun hv => ?_⟩
    have e : compAt L v a * compAt L v b - 1 = compAt L v a * (compAt L v b - 1) + (compAt L v a - 1) := by ring
    rw [e]
    refine (Valuation.map_add _ _ _).trans (max_le ?_ ((ha v).2 hv))
    rw [map_mul, (ha v).1, one_mul]
    exact (hb v).2 hv
  inv_mem' := fun {a} ha v => by
    have h1 : compAt L v a * compAt L v a⁻¹ = 1 := by rw [← compAt_mul, mul_inv_cancel, compAt_one]
    have hv1 : Valued.v (compAt L v a⁻¹) = 1 := by
      have := congrArg Valued.v h1
      rwa [map_mul, (ha v).1, one_mul, map_one] at this
    refine ⟨hv1, fun hv => ?_⟩
    have e : compAt L v a⁻¹ - 1 = -(compAt L v a⁻¹ * (compAt L v a - 1)) := by
      linear_combination h1
    rw [e, Valuation.map_neg, map_mul, hv1, one_mul]
    exact (ha v).2 hv

end GlobalTheory.LevelChars

open IsDedekindDomain NumberField

namespace GlobalTheory.LevelChars

theorem finite_chars {G : Type} [CommGroup G] (H : Subgroup G) [H.FiniteIndex] :
    {ψ : G →* ℂˣ | H ≤ ψ.ker}.Finite := by
  classical
  have : Finite (G ⧸ H) := Subgroup.finite_quotient_of_finiteIndex
  have : NeZero (Nat.card (G ⧸ H)) := ⟨Nat.card_pos.ne'⟩
  let f : {ψ : G →* ℂˣ | H ≤ ψ.ker} → (G ⧸ H → rootsOfUnity (Nat.card (G ⧸ H)) ℂ) := fun ψ q =>
    ⟨QuotientGroup.lift H ψ.1 ψ.2 q, by
      rw [mem_rootsOfUnity, ← map_pow, pow_card_eq_one', map_one]⟩
  have hf : Function.Injective f := by
    rintro ⟨ψ, hψ⟩ ⟨ψ', hψ'⟩ h
    refine Subtype.ext (MonoidHom.ext fun g => ?_)
    have := congrArg (fun F => ((F (QuotientGroup.mk g) : rootsOfUnity _ ℂ) : ℂˣ)) h
    simpa [f] using this
  exact Set.finite_coe_iff.1 (Finite.of_injective f hf)

theorem heckeFin_of
    (hA : ∀ (L : Type) [Field L] [NumberField L] (S : Set (HeightOneSpectrum (𝓞 L))) (N : ℕ) (ψ : Formalism.L2.Host.HChar L),
      (∀ k : Lˣ, ψ.inf k = 1) → (∀ v, v ∉ S → ψ.UnrAt v) → (∀ v ∈ S, ψ.LevelLe v N) → ∀ a ∈ levSub L S N, ψ.1 a = 1)
    (hC : ∀ (L : Type) [Field L] [NumberField L] (S : Set (HeightOneSpectrum (𝓞 L))) (N : ℕ), S.Finite →
      ((Units.map (algebraMap L (AdeleRing (𝓞 L) L)).toMonoidHom).range ⊔ levSub L S N).FiniteIndex) :
    ∀ (L : Type) [Field L] [NumberField L] (I : Type) [Fintype I] (φ : I → L →+* ℂ) (n : I → ℤ)
    (S : Set (HeightOneSpectrum (𝓞 L))) (N : ℕ), S.Finite →
    {χ : Formalism.L2.Host.HChar L | χ.HasInf φ n ∧ (∀ v, v ∉ S → χ.UnrAt v) ∧ ∀ v ∈ S, χ.LevelLe v N}.Finite := by
  intro L _ _ I _ φ n S N hS
  classical
  rcases Set.eq_empty_or_nonempty {χ : Formalism.L2.Host.HChar L | χ.HasInf φ n ∧ (∀ v, v ∉ S → χ.UnrAt v) ∧
    ∀ v ∈ S, χ.LevelLe v N} with h | ⟨χ0, hχ0⟩
  · rw [h]; exact Set.finite_empty
  have := hC L S N hS
  refine ((finite_chars ((Units.map (algebraMap L (AdeleRing (𝓞 L) L)).toMonoidHom).range ⊔ levSub L S N)).preimage (f := fun χ : Formalism.L2.Host.HChar L => (χ * χ0⁻¹).1)
    (fun χ _ χ' _ h => mul_right_cancel (Subtype.ext h))).subset ?_
  intro χ hχ
  show _ ≤ MonoidHom.ker _
  refine sup_le ?_ fun a ha => MonoidHom.mem_ker.2 (hA L S N (χ * χ0⁻¹) (fun k => ?_) (fun v hv x hx => ?_) (fun v hv x hx hle => ?_) a ha)
  · rintro _ ⟨k, rfl⟩
    exact MonoidHom.mem_ker.2 ((χ * χ0⁻¹).2.2 k)
  · have e : χ.inf k = χ0.inf k := Units.ext ((hχ.1 k).trans (hχ0.1 k).symm)
    rw [Formalism.L2.Host.HChar.inf_mul, Formalism.L2.Host.HChar.inf_inv, e, mul_inv_cancel]
  · change χ.loc v x * (χ0.loc v x)⁻¹ = 1
    rw [hχ.2.1 v hv x hx, hχ0.2.1 v hv x hx, inv_one, one_mul]
  · change χ.loc v x * (χ0.loc v x)⁻¹ = 1
    rw [hχ.2.2 v hv x hx hle, hχ0.2.2 v hv x hx hle, inv_one, one_mul]

end GlobalTheory.LevelChars
end

section

noncomputable section

namespace GlobalTheory.UnipApproxGL

open NumberField IsDedekindDomain Matrix PIW.ClassFinD

variable {F : Type} [Field F] [NumberField F]

theorem approx (x e : FiniteAdeleRing (𝓞 F) F) :
    ∃ r : F, e * (x + algebraMap F (FiniteAdeleRing (𝓞 F) F) r) ∈ Ohat F := by
  have hU : IsOpen ((fun y : FiniteAdeleRing (𝓞 F) F => e * (x + y)) ⁻¹'
      (ReciprocityTheory.GeneralLinearIntegers.GeneralLinearIntegersOpenCompact.Oint F)) :=
    ReciprocityTheory.GeneralLinearIntegers.GeneralLinearIntegersOpenCompact.isOpen_Oint.preimage (continuous_const.mul (continuous_const.add continuous_id))
  have h0 : (fun y : FiniteAdeleRing (𝓞 F) F => e * (x + y)) (-x) ∈ ReciprocityTheory.GeneralLinearIntegers.GeneralLinearIntegersOpenCompact.Oint F := by
    show e * (x + -x) ∈ ReciprocityTheory.GeneralLinearIntegers.GeneralLinearIntegersOpenCompact.Oint F
    rw [add_neg_cancel, mul_zero]
    exact (Ohat F).zero_mem
  obtain ⟨r, hr⟩ := (PI.UnipApproxD.additive_dense_integers F).exists_mem_open hU ⟨-x, h0⟩
  exact ⟨r, hr⟩

theorem row_exists (n : ℕ) (u : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 F) F))
    (hu : IsUpperUni u) (i : Fin n) (e : Fin n → FiniteAdeleRing (𝓞 F) F) :
    ∃ y : Fin n → F, y i = 1 ∧ (∀ k, k < i → y k = 0) ∧
      ∀ j, i < j → e j * ∑ k, algebraMap F (FiniteAdeleRing (𝓞 F) F) (y k) * u k j ∈ Ohat F := by
  classical
  have key : ∀ m : ℕ, ∃ y : Fin n → F, y i = 1 ∧ (∀ k, k < i → y k = 0) ∧
      ∀ j : Fin n, i < j → j.val < m →
        e j * ∑ k, algebraMap F (FiniteAdeleRing (𝓞 F) F) (y k) * u k j ∈ Ohat F := by
    intro m
    induction m with
    | zero =>
      refine ⟨fun k => if k = i then 1 else 0, by simp, fun k hk => ?_, fun j _ hj => absurd hj (Nat.not_lt_zero _)⟩
      simp [ne_of_lt hk]
    | succ m ih =>
      obtain ⟨y, hy1, hy0, hyc⟩ := ih
      by_cases h : ∃ hm : m < n, i < (⟨m, hm⟩ : Fin n)
      · obtain ⟨hm, him⟩ := h
        obtain ⟨r, hr⟩ := approx (∑ k, algebraMap F (FiniteAdeleRing (𝓞 F) F) (y k) * u k ⟨m, hm⟩)
          (e ⟨m, hm⟩)
        have hsum : ∀ j, ∑ k, algebraMap F (FiniteAdeleRing (𝓞 F) F)
              (y k + if k = (⟨m, hm⟩ : Fin n) then r else 0) * u k j
            = ∑ k, algebraMap F (FiniteAdeleRing (𝓞 F) F) (y k) * u k j +
                algebraMap F (FiniteAdeleRing (𝓞 F) F) r * u ⟨m, hm⟩ j := by
          intro j
          simp only [map_add (f := _), add_mul, Finset.sum_add_distrib, apply_ite (algebraMap F _), map_zero,
            ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
        refine ⟨fun k => y k + if k = (⟨m, hm⟩ : Fin n) then r else 0, ?_, ?_, ?_⟩
        · simp [hy1, ne_of_lt him]
        · intro k hk
          simp [hy0 k hk, ne_of_lt (hk.trans him)]
        · intro j hij hjm
          rw [hsum]
          rcases Nat.lt_succ_iff_lt_or_eq.mp hjm with hj | hj
          · rw [hu.1 ⟨m, hm⟩ j (by rw [Fin.lt_def]; exact hj), mul_zero, add_zero]
            exact hyc j hij hj
          · have hjM : j = ⟨m, hm⟩ := Fin.ext hj
            subst hjM
            rw [hu.2, mul_one]
            exact hr
      · refine ⟨y, hy1, hy0, fun j hij hjm => ?_⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hjm with hj | hj
        · exact hyc j hij hj
        · exfalso
          have hm : m < n := hj ▸ j.isLt
          exact h ⟨hm, by rwa [show (⟨m, hm⟩ : Fin n) = j from Fin.ext hj.symm]⟩
  obtain ⟨y, h1, h2, h3⟩ := key n
  exact ⟨y, h1, h2, fun j hij => h3 j hij j.isLt⟩

theorem matInt_inv_of_upperUni {n : ℕ} (g : GL (Fin n) (FiniteAdeleRing (𝓞 F) F))
    (hg : IsUpperUni g.val) (hi : MatInt g.val) : MatInt g⁻¹.val := by
  have hdet : g.val.det = 1 := by
    rw [det_of_upperTriangular (fun i j hij => hg.1 i j hij)]
    simp [hg.2]
  have h1 : g.val * adjugate g.val = 1 := by rw [mul_adjugate, hdet, one_smul]
  have hinv : g⁻¹.val = adjugate g.val := by
    calc g⁻¹.val = g⁻¹.val * (g.val * adjugate g.val) := by rw [h1, mul_one]
      _ = adjugate g.val := by rw [← mul_assoc, Units.inv_mul, one_mul]
  let W' : Matrix (Fin n) (Fin n) (Ohat F) := fun i j => ⟨g.val i j, hi i j⟩
  have hW : g.val = (Ohat F).subtype.mapMatrix W' := by ext i j; rfl
  intro i j
  rw [hinv, hW, ← RingHom.map_adjugate]
  exact ((adjugate W') i j).2

theorem unipApprox : PIW.ClassFinD.UnipApprox := by
  classical
  intro F _ _ n u t hu ht
  obtain ⟨τ, rfl⟩ := diag_eq_diagGL t ht
  choose y hy1 hy0 hyc using fun i => row_exists n u.val hu i
    (fun j => (((τ i)⁻¹ : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) * τ j)
  let Y : Matrix (Fin n) (Fin n) F := fun i k => y i k
  have hdet : Y.det = 1 := by
    rw [det_of_upperTriangular (fun i k hki => hy0 i k hki)]
    simp [Y, hy1]
  let Yg : GL (Fin n) F :=
    ((Matrix.isUnit_iff_isUnit_det Y).mpr (by rw [hdet]; exact isUnit_one)).unit

  let P : Fin n → Fin n → FiniteAdeleRing (𝓞 F) F := fun i j =>
    ∑ k, algebraMap F (FiniteAdeleRing (𝓞 F) F) (y i k) * u.val k j
  have hPlow : ∀ i j, j < i → P i j = 0 := by
    intro i j hji
    refine Finset.sum_eq_zero fun k _ => ?_
    rcases lt_or_ge k i with hk | hk
    · rw [hy0 i k hk, map_zero, zero_mul]
    · rw [hu.1 k j (lt_of_lt_of_le hji hk), mul_zero]
  have hPdiag : ∀ i, P i i = 1 := by
    intro i
    show ∑ k, _ = _
    rw [Finset.sum_eq_single i]
    · rw [hy1 i, map_one, one_mul, hu.2]
    · intro k _ hki
      rcases lt_or_gt_of_ne hki with hk | hk
      · rw [hy0 i k hk, map_zero, zero_mul]
      · rw [hu.1 k i hk, mul_zero]
    · intro h; exact absurd (Finset.mem_univ i) h
  let w := (diagGL n τ)⁻¹ * glIncl F n Yg * u * diagGL n τ
  have hw : ∀ i j, w.val i j =
      (((τ i)⁻¹ : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) * P i j * τ j := by
    intro i j
    simp only [w, ← map_inv, Units.val_mul, diagGL_val, Matrix.mul_assoc, Matrix.diagonal_mul,
      Matrix.mul_diagonal]
    rw [Matrix.mul_apply]
    rfl
  have hwu : IsUpperUni w.val := by
    refine ⟨fun i j hji => ?_, fun i => ?_⟩
    · rw [hw, hPlow i j hji, mul_zero, zero_mul]
    · rw [hw, hPdiag, mul_one, Units.inv_mul]
  have hwi : MatInt w.val := by
    intro i j
    rcases lt_trichotomy i j with hij | rfl | hji
    · rw [hw]
      have := hyc i j hij
      rw [show (((τ i)⁻¹ : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) * P i j * τ j =
        (((τ i)⁻¹ : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) * τ j * P i j by ring]
      exact this
    · rw [hwu.2]; exact (Ohat F).one_mem
    · rw [hwu.1 i j hji]; exact (Ohat F).zero_mem
  refine ⟨Yg⁻¹, w, ⟨hwi, matInt_inv_of_upperUni w hwu hwi⟩, ?_⟩
  simp only [w, map_inv]
  group

end GlobalTheory.UnipApproxGL

end
end

section

open Matrix

theorem _root_.GlobalTheory.T.definite_hermitian_eq_pm_gram_unitary_compact : ∀ (n p q : ℕ) (J : Matrix (Fin n) (Fin n) ℂ), Formalism.UG.HasSignature J p q → (p = 0 ∨ q = 0) → (∃ B : Matrix (Fin n) (Fin n) ℂ, IsUnit B.det ∧ (J = Bᴴ * B ∨ J = -(Bᴴ * B))) ∧ IsCompact (Formalism.QuantumDeterminants.UH J) := by
  first | exact @GlobalTheory.DefiniteFrame.definite_frame | exact GlobalTheory.DefiniteFrame.definite_frame | (intros; apply GlobalTheory.DefiniteFrame.definite_frame <;> assumption)
end

section

open MeasureTheory Filter Topology
open scoped ContDiff

theorem _root_.GlobalTheory.T.deriv_mem_and_contDiff_of_translation_stable : ∀ (G : Type) [Group G] (M : Submodule ℂ (G → ℂ)) [FiniteDimensional ℂ M] (ι : Type) (c : ι → ℝ → G), (∀ i s t, c i (s + t) = c i s * c i t) → (∀ i t, ∀ f ∈ M, (fun g => f (g * c i t)) ∈ M) → (∀ i, ∀ f ∈ M, ∀ g, Continuous fun t : ℝ => f (g * c i t)) → (∀ i, ∀ f ∈ M, (fun g => deriv (fun t : ℝ => f (g * c i t)) 0) ∈ M) ∧ ∀ (k : ℕ) (I : Fin k → ι), ∀ f ∈ M, ∀ g, ContDiff ℝ ∞ fun t : Fin k → ℝ => f (g * (List.ofFn fun a => c (I a) (t a)).prod) := by
  first | exact @GlobalTheory.smooth_of_finiteDimensional_translation_stable | exact GlobalTheory.smooth_of_finiteDimensional_translation_stable | (intros; apply GlobalTheory.smooth_of_finiteDimensional_translation_stable <;> assumption)
end

section

open MeasureTheory Filter Topology
open scoped ContDiff

theorem _root_.GlobalTheory.T.finiteDimensional_eigenspace_sum_sq_invariantFields_alt : ∀ (K : Type) [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K] [T2Space K] (L : Type) [NormedAddCommGroup L] [NormedSpace ℝ L] [FiniteDimensional ℝ L] (S : Submodule ℂ (K → ℂ)), (∀ f ∈ S, Continuous f) → ∀ e : L → K, (∀ X : L, Continuous fun t : ℝ => e (t • X)) → e 0 = 1 → (∀ r : ℝ, 0 < r → e '' Metric.ball 0 r ∈ 𝓝 (1 : K)) → ∀ d : L → Module.End ℂ S, (∀ X Y, d (X + Y) = d X + d Y) → (∀ (a : ℝ) X, d (a • X) = (a : ℂ) • d X) → (∀ (X : L) (f : S) (x : K) (t : ℝ), HasDerivAt (fun t : ℝ => f.1 (x * e (t • X))) ((d X f).1 (x * e (t • X))) t) → ∀ (ι : Type) [Fintype ι] (X : ι → L), Submodule.span ℝ (Set.range X) = ⊤ → ∀ lam : ℂ, FiniteDimensional ℂ (Module.End.eigenspace (∑ i, d (X i) * d (X i)) lam) := by
  first | exact @GlobalTheory.finiteDimensional_eigenspace_sum_sq_invariantFields | exact GlobalTheory.finiteDimensional_eigenspace_sum_sq_invariantFields | (intros; apply GlobalTheory.finiteDimensional_eigenspace_sum_sq_invariantFields <;> assumption)
end

section

open MeasureTheory
open scoped Pointwise

namespace GlobalTheory.AverageConst

@[to_additive setIntegral_add_left]
theorem setIntegral_mul_left {Z : Type} [Group Z] [TopologicalSpace Z] [IsTopologicalGroup Z] [MeasurableSpace Z]
    [BorelSpace Z] (hc : ∀ a b : Z, a * b = b * a) (Λ : Subgroup Z) [Countable Λ] (μ : Measure Z)
    [μ.IsMulLeftInvariant] {F : Set Z} (hF : IsFundamentalDomain Λ F μ) (φ : Z → ℂ)
    (hφ : ∀ γ ∈ Λ, ∀ z, φ (γ * z) = φ z) (a : Z) : ∫ z in F, φ (a * z) ∂μ = ∫ z in F, φ z ∂μ := by
  have : SMulCommClass Z Λ Z := ⟨fun a γ z => by
    change a * ((γ : Z) * z) = (γ : Z) * (a * z)
    rw [← mul_assoc, hc a, mul_assoc]⟩
  rw [hF.setIntegral_eq (hF.smul_of_comm a) fun γ z => hφ γ γ.2 z]
  exact ((measurePreserving_mul_left μ a).setIntegral_image_emb (measurableEmbedding_mulLeft a) φ F).symm

theorem average_const {Y Z A : Type} [AddCommGroup Y] [TopologicalSpace Y] [IsTopologicalAddGroup Y] [T2Space Y]
    [LocallyCompactSpace Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (Γ : AddSubgroup Y)
    [DiscreteTopology Γ] {K : Set Y} (hK : IsCompact K) (hcov : ∀ x, ∃ γ ∈ Γ, γ + x ∈ K) [AddCommGroup A] (χ : A → Y → ℂ)
    (h1 : ∀ a, Continuous (χ a)) (h2 : ∀ a x y, χ a (x + y) = χ a x * χ a y) (h3 : ∀ a b x, χ (a + b) x = χ a x * χ b x)
    (h4 : ∀ x, χ 0 x = 1) (h5 : ∀ a x, ‖χ a x‖ = 1) (h6 : ∀ x, (∀ a, χ a x = 1) ↔ x ∈ Γ)
    (ν : Measure Y) [ν.IsAddHaarMeasure] {G : Set Y} (hG : IsAddFundamentalDomain Γ G ν)
    [Group Z] [TopologicalSpace Z] [IsTopologicalGroup Z] [MeasurableSpace Z]
    [BorelSpace Z] (hc : ∀ a b : Z, a * b = b * a) (Λ : Subgroup Z) [Countable Λ] (μ : Measure Z)
    [μ.IsMulLeftInvariant] {F : Set Z} (hF : IsFundamentalDomain Λ F μ) (hfin : μ F ≠ ⊤)
    (k : Z → Y → ℂ) (kz : ∀ y, Continuous fun z => k z y) (ky : ∀ z, Continuous (k z)) {C : ℝ} (kb : ∀ z y, ‖k z y‖ ≤ C)
    (kΛ : ∀ γ ∈ Λ, ∀ z y, k (γ * z) y = k z y) (kΓ : ∀ γ ∈ Γ, ∀ z y, k z (γ + y) = k z y)
    (htw : ∀ a, (∀ y, χ a y = 1) ∨ ∃ (z₁ : Z) (c : ℂ), c ≠ 1 ∧
      ∀ z, ∫ y in G, χ a y * k (z₁ * z) y ∂ν = c * ∫ y in G, χ a y * k z y ∂ν) (y₀ : Y) :
    ∫ z in F, k z y₀ ∂μ = ∫ z in F, k z 0 ∂μ := by
  have : Countable Γ := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  have : IsFiniteMeasure (ν.restrict G) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact measure_addFundamentalDomain_lt_top_of_cocompact Γ hK hcov ν hG⟩
  have : IsFiniteMeasure (μ.restrict F) := ⟨by rw [Measure.restrict_apply_univ]; exact hfin.lt_top⟩
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : Y → ℂ, ∀ y, Φ y = ∫ z in F, k z y ∂μ := ⟨_, fun _ => rfl⟩
  have hΦc : Continuous Φ := by
    rw [funext hΦ]
    exact continuous_of_dominated (bound := fun _ => C) (fun y => (kz y).aestronglyMeasurable)
      (fun y => .of_forall fun z => kb z y) (integrable_const _) (.of_forall ky)
  have hΦp : ∀ γ ∈ Γ, ∀ y, Φ (γ + y) = Φ y := fun γ hγ y => by simp only [hΦ, kΓ γ hγ]
  have hΦb : ∀ y, ‖Φ y‖ ≤ C * (μ.restrict F).real Set.univ := fun y => by
    rw [hΦ]; exact norm_integral_le_of_norm_le_const (.of_forall fun z => kb z y)
  have hint : ∀ a y₁, Integrable (fun y => χ a y * Φ (y₁ + y)) (ν.restrict G) := fun a y₁ =>
    Integrable.of_bound ((h1 a).mul (hΦc.comp (continuous_const.add continuous_id))).aestronglyMeasurable _
      (.of_forall fun y => by rw [norm_mul, h5, one_mul]; exact hΦb _)
  have hco : ∀ a, (∀ y, χ a y = 1) ∨ ∫ y in G, χ a y * Φ y ∂ν = 0 := fun a => (htw a).imp_right fun ⟨z₁, c, hc1, h⟩ => by
    have hm : StronglyMeasurable (Function.uncurry fun y z => χ a y * k z y) :=
      stronglyMeasurable_uncurry_of_continuous_of_stronglyMeasurable (fun z => (h1 a).mul (ky z))
        fun y => (continuous_const.mul (kz y)).stronglyMeasurable
    have e : ∫ y in G, χ a y * Φ y ∂ν = ∫ z in F, ∫ y in G, χ a y * k z y ∂ν ∂μ := by
      simp only [hΦ, ← integral_const_mul]
      exact integral_integral_swap (Integrable.of_bound hm.aestronglyMeasurable C (.of_forall fun p => by
        rw [Function.uncurry, norm_mul, h5, one_mul]; exact kb _ _))
    have e2 := setIntegral_mul_left hc Λ μ hF (fun z => ∫ y in G, χ a y * k z y ∂ν)
      (fun γ hγ z => by simp only [kΛ γ hγ]) z₁
    simp only [h, integral_const_mul] at e2
    rw [e]
    exact (mul_left_eq_self₀.1 e2).resolve_left hc1
  have key := GlobalTheory.SeparatingCharacters.eq_zero_of_coefficients_eq_zero Y Γ K hK hcov A χ h1 h2 h3 h4 h5 h6 ν G
    inferInstance hG (fun y => Φ (y₀ + y) - Φ (0 + y))
    ((hΦc.comp (continuous_const.add continuous_id)).sub (hΦc.comp (continuous_const.add continuous_id)))
    (fun γ hγ y => by rw [add_left_comm, hΦp γ hγ, add_left_comm, hΦp γ hγ]) fun a => by
      have e := setIntegral_add_left add_comm Γ ν hG (fun y => χ a y * Φ y)
        (fun γ hγ y => by rw [h2, (h6 γ).2 hγ, one_mul, hΦp γ hγ]) y₀
      simp only [h2, mul_assoc, integral_const_mul] at e
      simp only [mul_sub]
      rw [integral_sub (hint a _) (hint a _), sub_eq_zero]
      simp only [zero_add]
      rcases hco a with h | h
      · rwa [h, one_mul] at e
      · rw [h] at e ⊢
        exact (mul_eq_zero.1 e).resolve_left fun h0 => by simpa [h0] using h5 a y₀
  have := congrFun key 0
  simp only [add_zero, Pi.zero_apply, sub_eq_zero] at this
  rw [← hΦ, ← hΦ, this]

end GlobalTheory.AverageConst
end

section

open MeasureTheory

theorem _root_.GlobalTheory.T.eq_zero_of_coefficients_separatingCharacters_eq_zero : ∀ (G : Type) [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (Γ : AddSubgroup G) [DiscreteTopology Γ] (K : Set G), IsCompact K → (∀ x, ∃ γ ∈ Γ, γ + x ∈ K) → ∀ (A : Type) [AddCommGroup A] (χ : A → G → ℂ), (∀ a, Continuous (χ a)) → (∀ a x y, χ a (x + y) = χ a x * χ a y) → (∀ a b x, χ (a + b) x = χ a x * χ b x) → (∀ x, χ 0 x = 1) → (∀ a x, ‖χ a x‖ = 1) → (∀ x, (∀ a, χ a x = 1) ↔ x ∈ Γ) → ∀ (μ : Measure G) (𝓕 : Set G), μ.IsAddHaarMeasure → IsAddFundamentalDomain Γ 𝓕 μ → ∀ Φ : G → ℂ, Continuous Φ → (∀ γ ∈ Γ, ∀ x, Φ (γ + x) = Φ x) → (∀ a, ∫ x in 𝓕, χ a x * Φ x ∂μ = 0) → Φ = 0 := by
  first | exact @GlobalTheory.SeparatingCharacters.eq_zero_of_coefficients_eq_zero | exact GlobalTheory.SeparatingCharacters.eq_zero_of_coefficients_eq_zero | (intros; apply GlobalTheory.SeparatingCharacters.eq_zero_of_coefficients_eq_zero <;> assumption)
end

section

open Metric Filter Topology Set

theorem _root_.GlobalTheory.T.differentiableAt_coordinate_cauchy_integral : ∀ (n : ℕ) (U : Set (Fin n → ℂ)) (k : Fin n) (f : (Fin n → ℂ) → ℂ) (z₀ : Fin n → ℂ) (r : ℝ), 0 < r → z₀ k = 0 → IsOpen U → Metric.closedBall z₀ r ⊆ U → DifferentiableOn ℂ f {z | z ∈ U ∧ z k ≠ 0} → DifferentiableAt ℂ (fun z => ∮ t in C(0, r), (t - z k)⁻¹ • f (Function.update z k t)) z₀ := by
  first | exact @GlobalTheory.cauchyCoord_differentiableAt | exact GlobalTheory.cauchyCoord_differentiableAt | (intros; apply GlobalTheory.cauchyCoord_differentiableAt <;> assumption)
end

section

open IsLocalRing

theorem _root_.GlobalTheory.T.isNoetherianRing_adicCompletion_of_noetherian : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R), IsNoetherianRing (AdicCompletion I R) := by
  first | exact @GlobalTheory.AdicNoeth.isNoetherianRing_adicCompletion | exact GlobalTheory.AdicNoeth.isNoetherianRing_adicCompletion | (intros; apply GlobalTheory.AdicNoeth.isNoetherianRing_adicCompletion <;> assumption)
end
