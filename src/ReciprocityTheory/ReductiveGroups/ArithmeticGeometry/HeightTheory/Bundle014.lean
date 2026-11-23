module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle010
public import Mathlib.RingTheory.Ideal.Height
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.ScaleMultiHomogeneous
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.CommutativeAlgebra.SaturatedChains.Bundle001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle008
import ReciprocityTheory.SemistableReduction.ExistsDualDerivations

@[expose] public section

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

theorem height_ker_scaledSubstitution_le_one (hd : d.AxH 𝒜) (c : ι) : (RingHom.ker (d.scaledSubstitution c)).height ≤ 1 := by
  classical
  obtain ⟨J, hJ⟩ := hd.a1 c
  obtain ⟨δ, hδ⟩ := ReciprocityTheory.MultiplicativeHeights.DerivationAlgebraicIndependence.exists_dual_derivations (K := K) (d.x c) J hJ
  have hy : d.affineCoord c (d.jc c) = 1 := scalarRatio_self (hd.w_base c)
  let ρ : Option (Fin d.D) → Fin (d.D + 2) := fun o =>
    (finSuccEquiv (d.D + 1)).symm (some ((finSuccEquiv d.D).symm o))
  have hρ : Function.Injective ρ := by
    intro o o' h
    simpa [ρ] using h
  have hind := algebraicIndependent_scaledForms (K := K) (d.affineCoord c) (d.jc c) hy J δ hδ ρ hρ
  let e : (Fin (d.D + 2) × Fin (d.N + 1)) ⊕ Fin (d.D + 2) ≃
      Option ((Fin (d.D + 2) × Fin (d.N + 1)) ⊕ Option (Fin d.D)) :=
    { toFun := fun x => match x with
        | Sum.inl p => some (Sum.inl p)
        | Sum.inr i => (finSuccEquiv (d.D + 1) i).map fun j => Sum.inr (finSuccEquiv d.D j)
      invFun := fun y => match y with
        | none => Sum.inr 0
        | some (Sum.inl p) => Sum.inl p
        | some (Sum.inr o) => Sum.inr (ρ o)
      left_inv := by
        rintro (p | i)
        · rfl
        · rcases h : finSuccEquiv (d.D + 1) i with _ | j <;>
          · have := (finSuccEquiv (d.D + 1)).symm_apply_apply i
            rw [h] at this
            simpa [h, ρ] using this
      right_inv := by
        rintro (_ | p | o)
        · simp
        · rfl
        · simp [ρ] }
  let g := (MvPolynomial.renameEquiv K e).trans
    (MvPolynomial.optionEquivLeft K ((Fin (d.D + 2) × Fin (d.N + 1)) ⊕ Option (Fin d.D)))
  let gr := g.toRingEquiv
  rw [← RingEquiv.height_comap gr.symm (RingHom.ker (d.scaledSubstitution c))]
  haveI hk : (RingHom.ker (d.scaledSubstitution c)).IsPrime := RingHom.ker_isPrime _
  haveI : (Ideal.comap gr.symm (RingHom.ker (d.scaledSubstitution c))).IsPrime := Ideal.comap_isPrime _ _
  refine ReciprocityTheory.CA.height_le_one_of_comap_C_eq_bot _ ?_
  rw [eq_bot_iff]
  intro a ha
  rw [Ideal.mem_comap, Ideal.mem_comap, RingHom.mem_ker] at ha
  rw [Ideal.mem_bot]
  have h2 : (MvPolynomial.optionEquivLeft K ((Fin (d.D + 2) × Fin (d.N + 1)) ⊕ Option (Fin d.D))).symm
      (Polynomial.C a) = MvPolynomial.rename some a := by
    rw [AlgEquiv.symm_apply_eq]
    exact (optionEquivLeft_rename_some' a).symm
  have h1 : gr.symm (Polynomial.C a) = MvPolynomial.rename (fun s => e.symm (some s)) a := by
    show (MvPolynomial.renameEquiv K e).symm ((MvPolynomial.optionEquivLeft K
      ((Fin (d.D + 2) × Fin (d.N + 1)) ⊕ Option (Fin d.D))).symm (Polynomial.C a)) = _
    rw [h2, MvPolynomial.renameEquiv_symm, MvPolynomial.renameEquiv_apply, MvPolynomial.rename_rename]
    rfl
  rw [h1, scaledSubstitution_eq, MvPolynomial.aeval_rename] at ha
  have hfam : (Sum.elim (fun p => (MvPolynomial.X (some p) :
        MvPolynomial (Option (Fin (d.D + 2) × Fin (d.N + 1))) (Ω c)))
      (fun i => MvPolynomial.X none *
        ∑ j, MvPolynomial.X (some (i, j)) * MvPolynomial.C (d.affineCoord c j))) ∘
      (fun s => e.symm (some s)) =
      Sum.elim (fun p => (MvPolynomial.X (some p) :
        MvPolynomial (Option (Fin (d.D + 2) × Fin (d.N + 1))) (Ω c)))
      (fun o => MvPolynomial.X none *
        ∑ j, MvPolynomial.X (some (ρ o, j)) * MvPolynomial.C (d.affineCoord c j)) := by
    funext s
    rcases s with p | o <;> rfl
  rw [hfam] at ha
  exact (injective_iff_map_eq_zero _).mp hind a ha

end Data

end ReciprocityTheory.ChartRestriction.G.T0
end

section

namespace ReciprocityTheory.ChartRestriction.G.T0

open MvPolynomial

section Gen

variable {K : Type} [Field K] {D N : ℕ}

theorem coeff_scaleEquiv {σ : Type*} [Fintype σ] (P : σ → Prop) [DecidablePred P] (u : Kˣ)
    (F : MvPolynomial σ K) (s : σ →₀ ℕ) :
    AddMonoidAlgebra.coeff (scaleEquiv P u F) s = (u : K) ^ (∑ v ∈ Finset.univ.filter P, s v) * AddMonoidAlgebra.coeff F s := by

  have hmon : ∀ (t : σ →₀ ℕ) (a : K), scaleEquiv P u (monomial t a) =
      monomial t ((u : K) ^ (∑ v ∈ Finset.univ.filter P, t v) * a) := by
    intro t a
    have hg : ∀ v, (if P v then C (u : K) * X v else X v) ^ t v =
        C (if P v then (u : K) ^ t v else 1) * (X v : MvPolynomial σ K) ^ t v := by
      intro v
      split_ifs <;> simp [mul_pow]
    rw [scaleEquiv, AlgEquiv.ofAlgHom_apply, aeval_monomial]
    rw [monomial_eq]
    simp only [Finsupp.prod_pow, algebraMap_eq, hg, Finset.prod_mul_distrib, ← map_prod, ← Finset.prod_filter,
      Finset.prod_pow_eq_pow_sum, map_mul]
    ring
  classical
  refine MvPolynomial.induction_on' F (fun t a => ?_) (fun p q hp hq => ?_)
  · rw [hmon, coeff_monomial, coeff_monomial]
    split_ifs with h
    · subst h
      rfl
    · simp
  · rw [map_add (f := _), MvPolynomial.coeff_add, MvPolynomial.coeff_add, hp, hq, mul_add]

theorem sum_filter_block (b : Fin (D + 1)) (s : TVar D N →₀ ℕ) :
    (∑ v ∈ Finset.univ.filter (fun v : TVar D N => v.1 = b), s v) = ∑ j, s (b, j) := by
  rw [Finset.sum_filter, Fintype.sum_prod_type]
  refine (Finset.sum_eq_single b (fun c _ hc => Finset.sum_eq_zero fun j _ => if_neg hc)
    (by simp)).trans (Finset.sum_congr rfl fun j _ => if_pos rfl)

theorem block_deg_of_scale [CharZero K] (b : Fin (D + 1)) (a : ℕ) (F : MvPolynomial (TVar D N) K)
    (hF : ∀ u : Kˣ, scaleEquiv (fun v : TVar D N => v.1 = b) u F = C ((u : K) ^ a) * F) :
    ∀ s ∈ F.support, ∑ j, s (b, j) = a := by
  intro s hs
  have h2 : (2 : K) ≠ 0 := two_ne_zero
  have h := congrArg (AddMonoidAlgebra.coeff · s) (hF (Units.mk0 2 h2))
  rw [coeff_scaleEquiv, coeff_C_mul, sum_filter_block] at h
  have hc : AddMonoidAlgebra.coeff F s ≠ 0 := mem_support_iff.1 hs
  have h' := mul_right_cancel₀ hc h
  simp only [Units.val_mk0] at h'
  have h'' : ((2 ^ (∑ j, s (b, j)) : ℕ) : K) = ((2 ^ a : ℕ) : K) := by
    push_cast
    exact h'
  exact Nat.pow_right_injective (le_refl 2) (Nat.cast_injective h'')

end Gen

section Blocks

variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] {D N : ℕ}

def IsBaseBlockVar (b : Fin (D + 1)) (v : SVar D N) : Prop :=
  Sum.elim (fun _ => b = 0) (fun w : Fin (D + 1) × Fin N => w.1 = b) v

instance (b : Fin (D + 1)) : DecidablePred (IsBaseBlockVar (D := D) (N := N) b) := by
  intro v
  cases v <;> simp only [IsBaseBlockVar, Sum.elim_inl, Sum.elim_inr] <;> infer_instance

noncomputable def tauPG (b : Fin (D + 1)) (u : Kˣ) :
    MvPolynomial (SVar D N) Ω ≃ₐ[Ω] MvPolynomial (SVar D N) Ω :=
  scaleEquiv (IsBaseBlockVar b) (Units.map (algebraMap K Ω).toMonoidHom u)

noncomputable def tauFG (b : Fin (D + 1)) (u : Kˣ) : OmS Ω D N ≃+* OmS Ω D N :=
  IsFractionRing.ringEquivOfRingEquiv (tauPG (Ω := Ω) (D := D) (N := N) b u).toRingEquiv

end Blocks

end ReciprocityTheory.ChartRestriction.G.T0
end
