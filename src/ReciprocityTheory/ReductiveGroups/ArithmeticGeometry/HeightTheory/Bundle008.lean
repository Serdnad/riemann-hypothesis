module

public import Mathlib.RingTheory.Derivation.Basic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.TheoremA
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle007
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.SemistableReduction.Bundle001
public import ReciprocityTheory.SemistableReduction.ExistsDualDerivations
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.Algebra.MvPolynomial.PDeriv

@[expose] public section

section

namespace ReciprocityTheory.ChartRestriction.G.T0

open MvPolynomial ReciprocityTheory.MultiplicativeHeights.DerivationAlgebraicIndependence

open MvPolynomial ReciprocityTheory.MultiplicativeHeights.DerivationAlgebraicIndependence

theorem algebraicIndependent_scaledForms {K Ω : Type} [Field K] [CharZero K] [Field Ω] [Algebra K Ω] {D N : ℕ}
    (y : Fin (N + 1) → Ω) (jc : Fin (N + 1)) (hy : y jc = 1)
    (J : Fin D → Fin N) (δ : Fin D → Derivation K Ω Ω)
    (hδ : ∀ a b, δ a (y (jc.succAbove (J b))) = if a = b then 1 else 0)
    (ρ : Option (Fin D) → Fin (D + 2)) (hρ : Function.Injective ρ) :
    AlgebraicIndependent K (Sum.elim
      (fun p : Fin (D + 2) × Fin (N + 1) =>
        (X (some p) : MvPolynomial (Option (Fin (D + 2) × Fin (N + 1))) Ω))
      (fun o : Option (Fin D) => X none * ∑ j, X (some (ρ o, j)) * C (y j))) := by
  classical
  refine algebraicIndependent_of_derivations _ (Sum.elim
    (fun o => (pderiv o :
      Derivation Ω (MvPolynomial (Option (Fin (D + 2) × Fin (N + 1))) Ω)
        (MvPolynomial (Option (Fin (D + 2) × Fin (N + 1))) Ω)).restrictScalars K)
    (fun a => coeffDer (σ := Option (Fin (D + 2) × Fin (N + 1))) (δ a))) ?_
  intro c H
  have hZ : ∀ o, pderiv (none : Option (Fin (D + 2) × Fin (N + 1)))
      (∑ j, X (some (ρ o, j)) * C (y j) : MvPolynomial (Option (Fin (D + 2) × Fin (N + 1))) Ω) = 0 := by
    intro o; simp [pderiv_X]
  have hpn : ∀ o, pderiv (none : Option (Fin (D + 2) × Fin (N + 1)))
      (X none * ∑ j, X (some (ρ o, j)) * C (y j) : MvPolynomial (Option (Fin (D + 2) × Fin (N + 1))) Ω) =
        ∑ j, X (some (ρ o, j)) * C (y j) := by
    intro o; rw [Derivation.leibniz, hZ, smul_zero, zero_add, pderiv_X]; simp
  have hcd : ∀ a o, coeffDer (σ := Option (Fin (D + 2) × Fin (N + 1))) (δ a)
      (X none * ∑ j, X (some (ρ o, j)) * C (y j)) =
        X none * ∑ j, X (some (ρ o, j)) * C (δ a (y j)) := by
    intro a o

    simp [Derivation.leibniz, coeffDer_X, coeffDer_C, map_sum]
  let M : Matrix (Option (Fin D)) (Option (Fin D))
      (MvPolynomial (Option (Fin (D + 2) × Fin (N + 1))) Ω) := fun r o =>
    match r with
    | none => ∑ j, X (some (ρ o, j)) * C (y j)
    | some a => X none * ∑ j, X (some (ρ o, j)) * C (δ a (y j))
  have e1 : ∑ o, c (Sum.inr o) * ∑ j, (X (some (ρ o, j)) * C (y j) :
      MvPolynomial (Option (Fin (D + 2) × Fin (N + 1))) Ω) = 0 := by
    have := H (Sum.inl none)
    rw [Fintype.sum_sum_type] at this
    simp only [Sum.elim_inl, Sum.elim_inr, Derivation.coe_restrictScalars, hpn] at this
    rwa [Finset.sum_eq_zero (fun p _ => by simp [pderiv_X]), zero_add] at this
  have e2 : ∀ a, ∑ o, c (Sum.inr o) * (X none * ∑ j, (X (some (ρ o, j)) * C (δ a (y j)) :
      MvPolynomial (Option (Fin (D + 2) × Fin (N + 1))) Ω)) = 0 := by
    intro a
    have := H (Sum.inr a)
    rw [Fintype.sum_sum_type] at this
    simp only [Sum.elim_inl, Sum.elim_inr, hcd] at this
    rwa [Finset.sum_eq_zero (fun p _ => by simp [coeffDer_X]), zero_add] at this
  have hv : M.mulVec (fun o => c (Sum.inr o)) = 0 := by
    funext r
    cases r with
    | none =>
      simp only [Matrix.mulVec, dotProduct, Pi.zero_apply]
      rw [← e1]
      exact Finset.sum_congr rfl fun o _ => mul_comm _ _
    | some a =>
      simp only [Matrix.mulVec, dotProduct, Pi.zero_apply]
      rw [← e2 a]
      exact Finset.sum_congr rfl fun o _ => mul_comm _ _
  let pt : Option (Fin (D + 2) × Fin (N + 1)) → Ω := fun v =>
    match v with
    | none => 1
    | some q => ∑ o : Option (Fin D), if ρ o = q.1 then
        (match o with
          | none => if q.2 = jc then 1 else 0
          | some b => (if q.2 = jc then -y (jc.succAbove (J b)) else 0) +
              (if q.2 = jc.succAbove (J b) then 1 else 0))
        else 0
  have hpt0 : ∀ j, pt (some (ρ none, j)) = if j = jc then 1 else 0 := by
    intro j
    show (∑ o : Option (Fin D), _) = _
    rw [Finset.sum_eq_single none]
    · simp
    · intro o _ ho; rw [if_neg]; exact fun h => ho (hρ h)
    · simp
  have hpt1 : ∀ b j, pt (some (ρ (some b), j)) = (if j = jc then -y (jc.succAbove (J b)) else 0) +
      (if j = jc.succAbove (J b) then 1 else 0) := by
    intro b j
    show (∑ o : Option (Fin D), _) = _
    rw [Finset.sum_eq_single (some b)]
    · simp
    · intro o _ ho; rw [if_neg]; exact fun h => ho (hρ h)
    · simp
  have hptn : pt none = 1 := rfl
  have hne : ∀ b, jc.succAbove (J b) ≠ jc := fun b => Fin.succAbove_ne jc (J b)
  have hev : (MvPolynomial.eval pt).mapMatrix M = 1 := by
    ext r o
    rw [RingHom.mapMatrix_apply, Matrix.map_apply]
    cases r with
    | none =>
      cases o with
      | none => simp [M, hpt0, hy]
      | some b =>
        simp [M, hpt1, add_mul, Finset.sum_add_distrib, hy, Matrix.one_apply]
    | some a =>
      cases o with
      | none =>
        simp [M, hpt0, hy, hptn, Matrix.one_apply]
      | some b =>
        simp [M, hpt1, add_mul, Finset.sum_add_distrib, hy, hδ, Matrix.one_apply, hptn]
  have hdet : M.det ≠ 0 := by
    intro h0
    have := RingHom.map_det (MvPolynomial.eval pt) M
    rw [h0, map_zero, hev, Matrix.det_one] at this
    exact zero_ne_one this
  have hc2 : ∀ o, c (Sum.inr o) = 0 := fun o =>
    congrFun (Matrix.eq_zero_of_mulVec_eq_zero hdet hv) o
  intro i
  rcases i with p | o
  · have := H (Sum.inl (some p))
    simpa [Fintype.sum_sum_type, hc2, pderiv_X, Pi.single_apply] using this
  · exact hc2 o

theorem scalarRatio_self {Ω V : Type*} [Field Ω] [AddCommGroup V] [Module Ω V] {f : V}
    (hf : f ≠ 0) : ratio (Ω := Ω) f f = 1 := by
  unfold ratio
  split_ifs with h
  · have hc : f = h.choose • f := h.choose_spec
    have h0 : (h.choose - 1) • f = 0 := by
      rw [sub_smul, one_smul, ← hc, sub_self]
    rcases smul_eq_zero.mp h0 with h1 | h1
    · exact sub_eq_zero.mp h1
    · exact absurd h1 hf
  · exact absurd ⟨1, (one_smul Ω f).symm⟩ h

theorem optionEquivLeft_rename_some' {R S : Type*} [CommRing R] (a : MvPolynomial S R) :
    MvPolynomial.optionEquivLeft R S (MvPolynomial.rename some a) = Polynomial.C a := by
  induction a using MvPolynomial.induction_on
  next r => simp [MvPolynomial.optionEquivLeft_C]
  next p q hp hq => simp [hp, hq]
  next p s hp => simp [hp, MvPolynomial.optionEquivLeft_X_some]

end ReciprocityTheory.ChartRestriction.G.T0
end

section

namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}

namespace Data

variable (d : Data K ι Ω WT A)

noncomputable def unif (la : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) : 𝓞 K :=
  open Classical in
  if h : ∃ ϖ : 𝓞 K, ϖ ∈ la.asIdeal ∧ ϖ ∉ la.asIdeal ^ 2 then h.choose else 0

noncomputable def gOrd (la : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (q : KTf K d.D d.N) : ℤ :=
  open Classical in
  if h : ∃ m : ℤ, ∃ u : Op d.D d.N la, IsUnit u ∧
      q = (algebraMap K (KTf K d.D d.N) ((unif la : 𝓞 K) : K)) ^ m * OpToKT d.D d.N la u
  then h.choose else 0

noncomputable def De (hd : d.AxH 𝒜) (h : d.S1) : KTf K d.D d.N :=
  Matrix.det (Matrix.of fun k l : Fin d.del => ∑ c,
    letI : Algebra (KTf K d.D d.N) (OmS (Ω c) d.D d.N) := (d.KTtoS h c).toAlgebra
    Algebra.trace (KTf K d.D d.N) (OmS (Ω c) d.D d.N)
      (d.bvecG hd.sel hd.a4.choose k c * d.bvecG hd.sel hd.a4.choose l c))

end Data

end ReciprocityTheory.ChartRestriction.G.T0
end

section

namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField

namespace FractionFieldVariableLift

def eT (D N : ℕ) : TVar D N ≃ Fin (N + 1) ⊕ {v : TVar D N // v.1 ≠ 0} where
  toFun v := if h : v.1 = 0 then Sum.inl v.2 else Sum.inr ⟨v, h⟩
  invFun := Sum.elim (fun j => ((0 : Fin (D + 1)), j)) Subtype.val
  left_inv v := by
    by_cases h : v.1 = 0
    · simp only [h, dite_true, Sum.elim_inl]; exact Prod.ext h.symm rfl
    · simp [h]
  right_inv s := by
    rcases s with j | ⟨v, hv⟩
    · simp
    · simp [hv]

noncomputable def eS (D N : ℕ) (j0 : Fin (N + 1)) :
    SVar D N ≃ Fin (N + 1) ⊕ ({i : Fin (D + 1) // i ≠ 0} × Fin N) where
  toFun s := match s with
    | Sum.inl _ => Sum.inl j0
    | Sum.inr p => if h : p.1 = 0 then Sum.inl (j0.succAbove p.2) else Sum.inr (⟨p.1, h⟩, p.2)
  invFun t := match t with
    | Sum.inl j => if h : j = j0 then Sum.inl () else Sum.inr (0, (Fin.exists_succAbove_eq h).choose)
    | Sum.inr q => Sum.inr (q.1.1, q.2)
  left_inv s := by
    rcases s with u | ⟨i, k⟩
    · simp
    · by_cases h : i = 0
      · subst h
        have hne : j0.succAbove k ≠ j0 := Fin.succAbove_ne j0 k
        simp only [dite_true, hne, dite_false]
        congr
        exact Fin.succAbove_right_injective (Fin.exists_succAbove_eq hne).choose_spec
      · simp [h]
  right_inv t := by
    rcases t with j | ⟨⟨i, hi⟩, k⟩
    · by_cases h : j = j0
      · subst h; simp
      · simp only [h, dite_false, dite_true]
        exact congrArg Sum.inl (Fin.exists_succAbove_eq h).choose_spec
    · simp [hi]

noncomputable def hL (K : Type) [Field K] (D N : ℕ) :
    KTp K D N ≃+* MvPolynomial (Fin (N + 1)) (MvPolynomial {v : TVar D N // v.1 ≠ 0} K) :=
  (MvPolynomial.renameEquiv K (eT D N)).toRingEquiv.trans (MvPolynomial.sumRingEquiv K _ _)

noncomputable def hE (Ω : Type) [Field Ω] (D N : ℕ) (j0 : Fin (N + 1)) :
    MvPolynomial (SVar D N) Ω ≃+*
      MvPolynomial (Fin (N + 1)) (MvPolynomial ({i : Fin (D + 1) // i ≠ 0} × Fin N) Ω) :=
  (MvPolynomial.renameEquiv Ω (eS D N j0)).toRingEquiv.trans (MvPolynomial.sumRingEquiv Ω _ _)

variable {K : Type} [Field K] {Ω : Type} [Field Ω] {D N : ℕ}

theorem hL_C (r : K) : hL K D N (MvPolynomial.C r) = MvPolynomial.C (MvPolynomial.C r) := by
  simp [hL, MvPolynomial.sumRingEquiv_C, MvPolynomial.sumRingEquiv_X_inl, MvPolynomial.sumRingEquiv_X_inr]

theorem hL_X (v : TVar D N) : hL K D N (MvPolynomial.X v) =
    if h : v.1 = 0 then MvPolynomial.X v.2 else MvPolynomial.C (MvPolynomial.X ⟨v, h⟩) := by
  by_cases h : v.1 = 0
  · simp [hL, eT, h, MvPolynomial.sumRingEquiv_C, MvPolynomial.sumRingEquiv_X_inl, MvPolynomial.sumRingEquiv_X_inr]
  · simp [hL, eT, h, MvPolynomial.sumRingEquiv_C, MvPolynomial.sumRingEquiv_X_inl, MvPolynomial.sumRingEquiv_X_inr]

theorem hL_rename (p : MvPolynomial {v : TVar D N // v.1 ≠ 0} K) :
    hL K D N (MvPolynomial.rename Subtype.val p) = MvPolynomial.C p := by
  induction p using MvPolynomial.induction_on with
  | C a => rw [MvPolynomial.rename_C, hL_C]
  | add p q hp hq => rw [map_add (f := _), map_add (f := _), hp, hq, map_add (f := _)]
  | mul_X p n hp => rw [map_mul, map_mul, hp, MvPolynomial.rename_X, hL_X, dif_neg n.2, map_mul]

theorem hE_C (j0 : Fin (N + 1)) (r : Ω) :
    hE Ω D N j0 (MvPolynomial.C r) = MvPolynomial.C (MvPolynomial.C r) := by
  simp [hE, MvPolynomial.sumRingEquiv_C, MvPolynomial.sumRingEquiv_X_inl, MvPolynomial.sumRingEquiv_X_inr]

end FractionFieldVariableLift

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]

namespace Data

variable (d : Data K ι Ω WT A)

noncomputable def offBaseSubstitution (c : ι) :
    MvPolynomial {v : TVar d.D d.N // v.1 ≠ 0} K →ₐ[K]
      MvPolynomial ({i : Fin (d.D + 1) // i ≠ 0} × Fin d.N) (Ω c) :=
  MvPolynomial.aeval fun v =>
    Fin.succAboveCases (α := fun _ => MvPolynomial ({i : Fin (d.D + 1) // i ≠ 0} × Fin d.N) (Ω c))
      (d.jc c) (-∑ k, MvPolynomial.X (⟨v.1.1, v.2⟩, k) * MvPolynomial.C (d.x c k))
      (fun k => MvPolynomial.X (⟨v.1.1, v.2⟩, k)) v.1.2

end Data

end ReciprocityTheory.ChartRestriction.G.T0
end
