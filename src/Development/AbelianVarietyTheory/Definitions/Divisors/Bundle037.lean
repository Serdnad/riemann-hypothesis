module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle001
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.Smooth
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.DSymmHypsInhabited
public import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle035
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle018
public import ReciprocityTheory.ClassFieldTheory.LocalClassField.ExistsIntEKMulVbar
public import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle133
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
public import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.MeasurePreservingRmulQuotMeas
import Mathlib.Tactic.Polynomial.Basic
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.TowU

variable {F : Type} [Field F] [NumberField F] {κ κ' : Type}

def dblAct (s : (κ → AF F) × (κ → AF F) → (κ' → AF F) × (κ' → AF F)) (w : (κ ⊕ κ → AF F) × (κ ⊕ κ → AF F)) :
    (κ' ⊕ κ' → AF F) × (κ' ⊕ κ' → AF F) :=
  (Sum.elim (s (w.1 ∘ Sum.inl, w.2 ∘ Sum.inl)).1 (s (w.1 ∘ Sum.inr, -(w.2 ∘ Sum.inr))).1,
    Sum.elim (s (w.1 ∘ Sum.inl, w.2 ∘ Sum.inl)).2 (-(s (w.1 ∘ Sum.inr, -(w.2 ∘ Sum.inr))).2))

variable [Fintype κ] [Fintype κ']

structure IsOp (ψ : AddChar (AF F) ℂ) (s : (κ → AF F) × (κ → AF F) → (κ' → AF F) × (κ' → AF F))
    (S : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ' → AF F) → ℂ)) (S' : ((κ' → AF F) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ)) : Prop where
  pres : ∀ φ ∈ schA F κ, S φ ∈ schA F κ'
  pres' : ∀ φ ∈ schA F κ', S' φ ∈ schA F κ
  left : ∀ φ ∈ schA F κ, S' (S φ) = φ
  right : ∀ φ ∈ schA F κ', S (S' φ) = φ
  adm : ∀ l ∈ (adeleClass F).adm κ', l ∘ₗ S ∈ (adeleClass F).adm κ
  adm' : ∀ l ∈ (adeleClass F).adm κ, l ∘ₗ S' ∈ (adeleClass F).adm κ'
  Heisenberg₂ : ∀ w, ∀ φ ∈ schA F κ, S (schr ψ w φ) = schr ψ (s w) (S φ)
  theta : ∃ c : ℂ, c ≠ 0 ∧ ∀ φ ∈ schA F κ, thetaSum F (S φ) = c * thetaSum F φ
  norm : ∀ (μ : @Measure (κ → AF F) (borel _)) (μ' : @Measure (κ' → AF F) (borel _)),
    @Measure.IsAddHaarMeasure _ _ _ (borel _) μ → @Measure.IsAddHaarMeasure _ _ _ (borel _) μ' →
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧ ∀ φ ∈ schA F κ, ∫⁻ x, ‖S φ x‖ₑ ^ 2 ∂μ' = c * ∫⁻ x, ‖φ x‖ₑ ^ 2 ∂μ

def IsOp2 (ψ : AddChar (AF F) ℂ) (s : (κ → AF F) × (κ → AF F) → (κ' → AF F) × (κ' → AF F))
    (S : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ' → AF F) → ℂ)) (S' : ((κ' → AF F) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ)) : Prop :=
  IsOp ψ s S S' ∧ ∃ Sd Sd', IsOp ψ (dblAct s) Sd Sd' ∧
    ∀ φ₁ ∈ schA F κ, ∀ φ₂ ∈ schA F κ, Sd (boxFun φ₁ φ₂) = boxFun (S φ₁) (star (S (star φ₂)))

end GlobalTheory.TowU

end
end

section

noncomputable section

open MeasureTheory ReciprocityTheory.ChartRestriction.DS GlobalTheory.Orb GlobalTheory.OpTrace GlobalTheory.AutomorphicL2Unitary
open Formalism.REAL (UJ KG toM toMK muK)
open GlobalTheory.PsCo.Pc1 (Mat Poly ev blockAlg detbP OmP dMode)
open scoped ComplexConjugate InnerProductSpace

namespace GlobalTheory.PsCo.PcEF

variable {n : ℕ}

def PolyOnK (ε : Fin n → Bool) (f : Mat n → ℂ) : Prop := ∃ P : Poly n, ∀ k ∈ Formalism.REAL.Kset ε, f k = ev k P

def trK {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] (T : Mat n → (W →L[ℂ] W)) (k : Mat n) : ℂ :=
  LinearMap.trace ℂ W (T k : W →ₗ[ℂ] W)

def IsKIrr (ε : Fin n → Bool) (γ : Fin n → ℝ) {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    (T : Mat n → (W →L[ℂ] W)) : Prop :=
  Nontrivial W ∧ Formalism.MainNotions.S.IsURepOn (Formalism.REAL.Kset ε) T ∧ Formalism.MainNotions.S.IsKTypeOf ε T γ ⊤

abbrev dD (ε : Fin n → Bool) {M : Type} [AddCommGroup M] [Module ℂ M] (E : Fin n → Fin n → Module.End ℂ M) :
    Module.End ℂ (TensorProduct ℂ M (Fock n)) := dOp ε (eT E) cpT + dOp' ε (eT E) cmT

abbrev tor (θ : Fin n → ℝ) : Fin n → ℂ := fun a => Complex.exp (θ a * Complex.I)

def BlockForm : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (P : Poly n), ∃ (M : ℕ) (Q : Poly n), Q ∈ blockAlg ε ∧
    ∀ k ∈ Formalism.REAL.Kset ε, ev k P = ev k (detbP n ^ M * Q)

def CoefPoly : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (W : Type) [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
    (T : Mat n → (W →L[ℂ] W)), Formalism.MainNotions.S.IsURepOn (Formalism.REAL.Kset ε) T →
    ∀ v w : W, PolyOnK ε fun k => ⟪w, T k v⟫_ℂ

def TrPoly : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (W : Type) [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
    (T : Mat n → (W →L[ℂ] W)), (∀ v w : W, PolyOnK ε fun k => ⟪w, T k v⟫_ℂ) → PolyOnK ε fun k => conj (trK T k)

def AvgMap : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (W : Type) [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
    (T : Mat n → (W →L[ℂ] W)) (Z : Type) [NormedAddCommGroup Z] [InnerProductSpace ℂ Z] [FiniteDimensional ℂ Z]
    (S : Mat n → (Z →L[ℂ] Z)) (Γ : Z →ₗ[ℂ] Z), Formalism.MainNotions.S.IsURepOn (Formalism.REAL.Kset ε) T →
    Formalism.MainNotions.S.IsURepOn (Formalism.REAL.Kset ε) S →
    ∫ k : KG ε, conj (trK T (toMK k)) * LinearMap.trace ℂ Z (Γ ∘ₗ (S (toMK k) : Z →ₗ[ℂ] Z)) ∂(muK ε) ≠ 0 →
    ∃ Φ : W →ₗ[ℂ] Z, Φ ≠ 0 ∧ ∀ k ∈ Formalism.REAL.Kset ε, ∀ v, Φ (T k v) = S k (Φ v)

def SchurOne : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (γ : Fin n → ℝ) (W : Type) [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    [FiniteDimensional ℂ W] (T : Mat n → (W →L[ℂ] W)), IsKIrr ε γ T →
    ∫ k : KG ε, conj (trK T (toMK k)) * trK T (toMK k) ∂(muK ε) = 1

def SumTypes : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Mat n → (H →L[ℂ] H)), IsURepOn (UJset ε) σ → ∀ S : Submodule ℂ H, FiniteDimensional ℂ S →
    Formalism.MainNotions.S.IsKStableOn ε σ S → S ≤ sSup {S' | S' ≤ S ∧ ∃ μ, Formalism.MainNotions.S.IsKTypeOf ε σ μ S'}

def PolyAvg : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (d : ℕ), ∃ A : Set (Fin n → ℝ), A.Finite ∧
    ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mat n → (H →L[ℂ] H)),
      IsURepOn (UJset ε) σ → ∀ u : H, ∃ S : Submodule ℂ H, FiniteDimensional ℂ S ∧ Formalism.MainNotions.S.IsKStableOn ε σ S ∧
        (∀ P : Poly n, P.totalDegree ≤ d → ∫ k : KG ε, ev (toMK k) P • σ (toMK k) u ∂(muK ε) ∈ S) ∧
        ∀ (μ : Fin n → ℝ) (s : H), s ∈ S → s ≠ 0 → Formalism.MainNotions.S.IsWtOn (Formalism.REAL.Kset ε) σ μ s → μ ∈ A

def DatumEquiv : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ), StdGap ε lam →
    ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mat n → (H →L[ℂ] H)),
    IsURepOn (UJset ε) σ → Formalism.MainNotions.S.IsIrredOn (Formalism.MainNotions.S.UJset ε) σ →
    ∀ V : Submodule ℂ (smD ε σ), IsKIrrHW ε (smE ε σ) (lowK ε lam) V → V ≠ ⊥ →
    (∀ v ∈ V, casimir (smE ε σ) v = (casVal lam : ℂ) • v) →
    ∀ (X : Type) [NormedAddCommGroup X] [InnerProductSpace ℂ X] (D : Mat n → (X →L[ℂ] X)), Formalism.MainNotions.S.IsDS ε lam D →
    ∃ U : H ≃ₗᵢ[ℂ] X, ∀ g ∈ UJset ε, ∀ x, U (σ g x) = D g (U x)

def MatRep : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (U : Type) [NormedAddCommGroup U] [InnerProductSpace ℂ U] (π : UJ ε →* (U →L[ℂ] U)),
    IsUnitaryRep π → IsTopIrreducible π → ∃ σ : Mat n → (U →L[ℂ] U), IsURepOn (UJset ε) σ ∧
      Formalism.MainNotions.S.IsIrredOn (Formalism.MainNotions.S.UJset ε) σ ∧ ∀ g : UJ ε, σ (toM g) = π g

end GlobalTheory.PsCo.PcEF
end
end

section

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArithBase GlobalTheory.CechPic

namespace GlobalTheory.ArInt.Model

variable {L M : HermLB (𝟙 (Sp ℤ))} {s t : ℝ}


open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MvPolynomial in
variable {L M : _root_.GlobalTheory.HermLB (𝟙 (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp ℤ))} {s t : ℝ} in
private theorem lin_pow_eq_eval_sum_multinomial {ι : Type} [Fintype ι] [DecidableEq ι]
    (Ψ : MvPolynomial ι ℝ →ₗ[ℝ] ℝ) (m : ℕ) (r : ι → ℝ) :
    Ψ (_root_.GlobalTheory.ArInt.lin r ^ m) =
      MvPolynomial.eval r (∑ k ∈ (Finset.univ : Finset ι).piAntidiag m,
        MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm k)
          ((Nat.multinomial Finset.univ k : ℝ) *
            Ψ (MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm k) 1))) := by
  unfold _root_.GlobalTheory.ArInt.lin

  rw [Finset.sum_pow_eq_sum_piAntidiag, map_sum, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hk : ∏ i, (MvPolynomial.C (r i) * MvPolynomial.X i) ^ k i =
      MvPolynomial.C (∏ i, r i ^ k i) *
        MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm k) (1 : ℝ) := by
    rw [MvPolynomial.monomial_eq, Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
    simp [mul_pow, Finset.prod_mul_distrib, map_prod]
  rw [hk, MvPolynomial.eval_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  rw [← mul_assoc, ← map_natCast (MvPolynomial.C : ℝ →+* MvPolynomial ι ℝ), ← map_mul,
    ← MvPolynomial.smul_eq_C_mul, map_smul, smul_eq_mul]
  simp
  ring

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MvPolynomial in
variable {L M : _root_.GlobalTheory.HermLB (𝟙 (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp ℤ))} {s t : ℝ} in
private theorem eq_zero_of_isHomogeneous_of_forall_lin_pow_eq_zero {ι : Type} [Fintype ι]
    (Ψ : MvPolynomial ι ℝ →ₗ[ℝ] ℝ) (m : ℕ)
    (hΨ : ∀ n : ι → ℤ, Ψ (_root_.GlobalTheory.ArInt.lin (fun i => (n i : ℝ)) ^ m) = 0)
    {P : MvPolynomial ι ℝ} (hP : P.IsHomogeneous m) : Ψ P = 0 := by
  classical
  set Q : MvPolynomial ι ℝ := ∑ k ∈ (Finset.univ : Finset ι).piAntidiag m,
    MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm k)
      ((Nat.multinomial Finset.univ k : ℝ) *
        Ψ (MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm k) 1)) with hQdef
  have hQ : Q = 0 := by
    refine MvPolynomial.funext_set (fun _ => Set.range (Int.cast : ℤ → ℝ))
      (fun _ => Set.infinite_range_of_injective Int.cast_injective) fun x hx => ?_
    choose n hn using fun i => hx i (Set.mem_univ i)
    have hxn : x = fun i => (n i : ℝ) := funext fun i => (hn i).symm
    rw [map_zero, hxn, hQdef, ← lin_pow_eq_eval_sum_multinomial, hΨ]
  have hmon : ∀ d : ι →₀ ℕ, (Finsupp.weight 1) d = m →
      Ψ (MvPolynomial.monomial d 1) = 0 := by
    intro d hd
    have hmem : ⇑d ∈ (Finset.univ : Finset ι).piAntidiag m := by
      rw [Finset.mem_piAntidiag]
      refine ⟨?_, fun i _ => Finset.mem_univ i⟩
      rw [← hd, Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]
      simp
    have hc := congrArg (AddMonoidAlgebra.coeff · d) hQ
    rw [hQdef, MvPolynomial.coeff_sum, Finset.sum_eq_single (⇑d)] at hc
    · rw [Finsupp.equivFunOnFinite_symm_coe, MvPolynomial.coeff_monomial, if_pos rfl,
        MvPolynomial.coeff_zero] at hc
      have hne : (Nat.multinomial Finset.univ ⇑d : ℝ) ≠ 0 := by
        exact_mod_cast (Nat.multinomial_pos _ _).ne'
      exact (mul_eq_zero.mp hc).resolve_left hne
    · intro b _ hb
      rw [MvPolynomial.coeff_monomial, if_neg]
      intro heq
      apply hb
      rw [← heq]
      simp
    · intro h
      exact absurd hmem h

  rw [P.as_sum, map_sum]
  refine Finset.sum_eq_zero fun d hd => ?_
  have hw := hP (MvPolynomial.mem_support_iff.mp hd)
  have hsm : MvPolynomial.monomial d (AddMonoidAlgebra.coeff P d) =
      AddMonoidAlgebra.coeff P d • MvPolynomial.monomial d (1 : ℝ) := by
    rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
  rw [hsm, map_smul, hmon d hw, smul_zero]


open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MvPolynomial in
variable {L M : _root_.GlobalTheory.HermLB (𝟙 (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp ℤ))} {s t : ℝ} in
theorem _root_.GlobalTheory.ArInt.Model.isArFun_unique {k : Type} [CommRing k] {X : Scheme.{0}}
    [IsIntegral X] {p : X ⟶ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp k} {D E : ℕ} (hX : _root_.GlobalTheory.IsArithVar p E)
    {ι : Type} [Fintype ι] {L : ι → _root_.GlobalTheory.HermLB p}
    {Φ Φ' : MvPolynomial ι ℝ →ₗ[ℝ] ℝ} (h : _root_.GlobalTheory.ArInt.IsArFun L D Φ)
    (h' : _root_.GlobalTheory.ArInt.IsArFun L D Φ') :
    Φ = Φ' := by
  obtain ⟨h1, h2⟩ := h
  obtain ⟨h1', h2'⟩ := h'
  have hpow : ∀ n : ι → ℤ,
      (Φ - Φ') (_root_.GlobalTheory.ArInt.lin (fun i => (n i : ℝ)) ^ (D + 1)) = 0 := by
    intro n
    rw [LinearMap.sub_apply, sub_eq_zero]
    exact _root_.GlobalTheory.HermLB.IsSelfInter.unique hX
      (h1 n) (h1' n)
  have hhom : ∀ (P : MvPolynomial ι ℝ) (d : ℕ), P.IsHomogeneous d → Φ P = Φ' P := by
    intro P d hP
    by_cases hd : d = D + 1
    · subst hd
      exact sub_eq_zero.mp (eq_zero_of_isHomogeneous_of_forall_lin_pow_eq_zero (Φ - Φ') (D + 1) hpow hP)
    · rw [h2 P d hd hP, h2' P d hd hP]
  refine LinearMap.ext fun P => ?_

  rw [← MvPolynomial.sum_homogeneousComponent P, map_sum, map_sum]
  exact Finset.sum_congr rfl fun j _ =>
    hhom _ j (MvPolynomial.homogeneousComponent_isHomogeneous j P)

end GlobalTheory.ArInt.Model
end
end

section

noncomputable section

open scoped Classical

namespace GlobalTheory.LKCount

section Vol

variable {G : Type} [Group G]

def vol (C H : Subgroup G) : ℚ := ((C.relIndex H : ℕ) : ℚ) / ((H.relIndex C : ℕ) : ℚ)

def orbC (θ : G →* G) (K C : Subgroup G) (δ : G) (f : G → ℂ) : ℂ :=
  ∑ᶠ q : DoubleCoset.Quotient (GlobalTheory.BCT.twCent θ δ : Set G) (K : Set G),
    ((vol C (GlobalTheory.BCT.twCent θ δ ⊓ K.map (MulAut.conj (Quotient.out q)).toMonoidHom) : ℚ) : ℂ)⁻¹ *
      f ((Quotient.out q)⁻¹ * δ * θ (Quotient.out q))

def orbK (θ : G →* G) (K : Subgroup G) (δ : G) (f : G → ℂ) : ℂ :=
  orbC θ K (GlobalTheory.BCT.twCent θ δ ⊓ K) δ f

def massC (Γ' T C : Subgroup G) : ℚ :=
  ∑ᶠ q : DoubleCoset.Quotient ((Γ'.subgroupOf T : Subgroup T) : Set T) ((C.subgroupOf T : Subgroup T) : Set T),
    ((Nat.card ((Γ'.subgroupOf T) ⊓ (C.subgroupOf T).map (MulAut.conj (Quotient.out q)).toMonoidHom : Subgroup T) : ℕ) : ℚ)⁻¹

end Vol

section Count

variable {Γ G₁ G₂ : Type} [Group Γ] [Group G₁] [Group G₂]

def stab (ι₁ : Γ →* G₁) (ι₂ : Γ →* G₂) (K₁ : Subgroup G₁) (K₂ : Subgroup G₂) (x : G₁ × G₂) : Subgroup Γ :=
  (K₁.map (MulAut.conj x.1).toMonoidHom).comap ι₁ ⊓ (K₂.map (MulAut.conj x.2).toMonoidHom).comap ι₂

def pointSum (ι₁ : Γ →* G₁) (ι₂ : Γ →* G₂) (θ : G₂ →* G₂) (K₁ : Subgroup G₁) (K₂ : Subgroup G₂) (γ : G₁) (δ : G₂)
    (f₁ : G₁ → ℂ) (φ : G₂ → ℂ) : ℂ :=
  ∑ᶠ q : DoubleCoset.Quotient ((ι₁.prod ι₂).range : Set (G₁ × G₂)) ((K₁.prod K₂ : Subgroup (G₁ × G₂)) : Set (G₁ × G₂)),
    ((Nat.card (stab ι₁ ι₂ K₁ K₂ (Quotient.out q)) : ℕ) : ℂ)⁻¹ *
      (f₁ ((Quotient.out q).1⁻¹ * γ * (Quotient.out q).1) * φ ((Quotient.out q).2⁻¹ * δ * θ (Quotient.out q).2))

def pointSide (ι₁ : Γ →* G₁) (ι₂ : Γ →* G₂) (θ : G₂ →* G₂) (K₁ : Subgroup G₁) (K₂ : Subgroup G₂) (γ : G₁) (δ : G₂)
    (f₁ : G₁ → ℂ) (φ : G₂ → ℂ) : ℂ :=
  ((massC (ι₁.prod ι₂).range (GlobalTheory.BCT.twCent ((MonoidHom.id G₁).prodMap θ) (γ, δ))
      (GlobalTheory.BCT.twCent ((MonoidHom.id G₁).prodMap θ) (γ, δ) ⊓ K₁.prod K₂) : ℚ) : ℂ) *
    (orbK (MonoidHom.id G₁) K₁ γ f₁ * orbK θ K₂ δ φ)

def term (ι₁ : Γ →* G₁) (ι₂ : Γ →* G₂) (θ : G₂ →* G₂) (δ : G₂) (f₁ : G₁ → ℂ) (φ : G₂ → ℂ) (x : G₁ × G₂) (γ : Γ) : ℂ :=
  f₁ (x.1⁻¹ * ι₁ γ * x.1) * φ (x.2⁻¹ * (ι₂ γ * δ) * θ x.2)

def centSum (ι₁ : Γ →* G₁) (ι₂ : Γ →* G₂) (θ : G₂ →* G₂) (K₁ : Subgroup G₁) (K₂ : Subgroup G₂) (δ : G₂)
    (f₁ : G₁ → ℂ) (φ : G₂ → ℂ) (γ : Γ) : ℂ :=
  ∑ᶠ q : DoubleCoset.Quotient (((Subgroup.centralizer {γ}).map (ι₁.prod ι₂) : Subgroup (G₁ × G₂)) : Set (G₁ × G₂))
      ((K₁.prod K₂ : Subgroup (G₁ × G₂)) : Set (G₁ × G₂)),
    ((Nat.card (stab ι₁ ι₂ K₁ K₂ (Quotient.out q) ⊓ Subgroup.centralizer {γ} : Subgroup Γ) : ℕ) : ℂ)⁻¹ *
      term ι₁ ι₂ θ δ f₁ φ (Quotient.out q) γ

end Count

section Examples

end Examples

end GlobalTheory.LKCount
end
end

section

noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host
open scoped Classical TensorProduct

namespace GlobalTheory.BCT

def SoleTerm {ι : Type} (C : ι → ℂ) (p q : ι → Prop) : Prop :=
  ∃ i, C i ≠ 0 ∧ p i ∧ ∀ i', C i' ≠ 0 → q i' → i' = i

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem isLocComp_iff_equiv {ρc : CuspSub E n} {w : Pl E} {σ : SmIrr (GLw n w)} (h : ρc.IsLocComp w σ)
    (τ : SmIrr (GLw n w)) : ρc.IsLocComp w τ ↔ Nonempty (τ.ρ.Equiv σ.ρ) :=
  ⟨fun h' => GlobalTheory.CuspRep.LocUniq.isLocComp_unique ρc w τ σ h' h,
    fun ⟨e⟩ => h.congr ((CuspSub.setoid E n).iseqv.refl ρc) ⟨e.symm⟩⟩

end GlobalTheory.BCT
end
end

section

noncomputable section
open ValuativeRel Matrix Polynomial
open scoped Classical

namespace GlobalTheory.DZA

def KO (k : Type) [Field k] [ValuativeRel k] (n : ℕ) : Subgroup (GL (Fin n) k) :=
  (GeneralLinearGroup.map (algebraMap 𝒪[k] k)).range

def K1 {k : Type} [Field k] [ValuativeRel k] {F : Type} [Field F] (rd : 𝒪[k] →+* F) (n : ℕ) : Subgroup (GL (Fin n) k) :=
  (GeneralLinearGroup.map rd).ker.map (GeneralLinearGroup.map (algebraMap 𝒪[k] k))

def infl {k : Type} [Field k] [ValuativeRel k] {F : Type} [Field F] (rd : 𝒪[k] →+* F) {n : ℕ}
    (fb : GL (Fin n) F → ℂ) (x : GL (Fin n) k) : ℂ :=
  if h : ∃ y : GL (Fin n) 𝒪[k], GeneralLinearGroup.map (algebraMap 𝒪[k] k) y = x then
    fb (GeneralLinearGroup.map rd h.choose) else 0

def IsFinNorm {F F' : Type} [Field F] [Field F'] [Algebra F F'] (s : F' ≃ₐ[F] F') {n : ℕ}
    (δ : GL (Fin n) F') (γ : GL (Fin n) F) : Prop :=
  IsConj (GlobalTheory.LBC.incl F' n γ) (GlobalTheory.LBC.norm F s δ)

def normLift {F F' : Type} [Field F] [Field F'] [Algebra F F'] (s : F' ≃ₐ[F] F') {n : ℕ}
    (fb : GL (Fin n) F → ℂ) (δ : GL (Fin n) F') : ℂ :=
  if h : ∃ γ, IsFinNorm s δ γ then fb h.choose else 0

def InflMatching : Prop :=
  ∀ (k K : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [Algebra k K],
    Continuous (algebraMap k K) → CharZero k →
    ∀ (F F' : Type) [Field F] [Fintype F] [Field F'] [Fintype F'] [Algebra F F'],
      Module.finrank F F' = Module.finrank k K →
    ∀ (rk : 𝒪[k] →+* F) (rK : 𝒪[K] →+* F'), Function.Surjective rk → Function.Surjective rK →
      (∀ (x : 𝒪[k]) (y : 𝒪[K]), (y : K) = algebraMap k K x → rK y = algebraMap F F' (rk x)) →
    ∀ (s : K ≃ₐ[k] K) (sb : F' ≃ₐ[F] F'),
      (∀ x y : 𝒪[K], (y : K) = s x → rK y = sb (rK x)) →
      (∀ z : F', sb z = z ^ Fintype.card F) →
    ∀ (n : ℕ) (fb : GL (Fin n) F → ℂ), (∀ a b, fb (b⁻¹ * a * b) = fb a) →
      (∀ δ : GL (Fin n) K, (GlobalTheory.LBC.norm k s δ : Matrix (Fin n) (Fin n) K).charpoly.Separable →
        ∀ γ : GL (Fin n) k, (γ : Matrix (Fin n) (Fin n) k).charpoly.map (algebraMap k K) =
            (GlobalTheory.LBC.norm k s δ : Matrix (Fin n) (Fin n) K).charpoly →
          GlobalTheory.BCT.twOrb (GlobalTheory.LBC.galAct s n) (KO K n) δ (infl rK (normLift sb fb)) =
            GlobalTheory.BCT.twOrb (MonoidHom.id _) (KO k n) γ (infl rk fb)) ∧
      (∀ γ : GL (Fin n) k, (γ : Matrix (Fin n) (Fin n) k).charpoly.Separable →
        GlobalTheory.BCT.twOrb (MonoidHom.id _) (KO k n) γ (infl rk fb) ≠ 0 →
          ∃ δ : GL (Fin n) K, (γ : Matrix (Fin n) (Fin n) k).charpoly.map (algebraMap k K) =
            (GlobalTheory.LBC.norm k s δ : Matrix (Fin n) (Fin n) K).charpoly)

end GlobalTheory.DZA
end
end

section

noncomputable section

open ReciprocityTheory.DiscreteGroups.LocalClassField Matrix
open scoped Classical

namespace GlobalTheory.LKLoc

section Generic

variable {G : Type} [Group G]

def locPart (T K : Subgroup G) (x : G) : Subgroup G := T ⊓ K.map (MulAut.conj x).toMonoidHom

def volRat (U V : Subgroup G) : ℝ := (V.relIndex U : ℝ) / (U.relIndex V : ℝ)

def orbSum (θ : G →* G) (K : Subgroup G) (δ : G) (w : G → ℝ) (f : G → ℂ) : ℂ :=
  ∑ᶠ q : DoubleCoset.Quotient (GlobalTheory.BCT.twCent θ δ : Set G) (K : Set G),
    (w (Quotient.out q) : ℂ) * GlobalTheory.BCT.avg fun k : K => f ((Quotient.out q * k)⁻¹ * δ * θ (Quotient.out q * k))

def twOrbU (θ : G →* G) (K : Subgroup G) (δ : G) (U : Subgroup G) (f : G → ℂ) : ℂ :=
  orbSum θ K δ (fun x => volRat U (locPart (GlobalTheory.BCT.twCent θ δ) K x)) f

end Generic

variable (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p))

def frobR (r : ℕ) : Kn p K r →+* Kn p K r where
  toFun x := ⟨frobK p K (x : PadicAlgCl p), Kn_stable p K r (frobK p K) x x.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' x y := Subtype.ext (by simp)
  map_zero' := Subtype.ext (by simp)
  map_add' x y := Subtype.ext (by simp)

def intR (r : ℕ) : Subring (Kn p K r) := (Obar p).toSubring.comap (algebraMap (Kn p K r) (PadicAlgCl p))

def intK : Subring K := (Obar p).toSubring.comap (algebraMap K (PadicAlgCl p))

def sig (n r : ℕ) : GL (Fin n) (Kn p K r) →* GL (Fin n) (Kn p K r) :=
  GeneralLinearGroup.map (frobR p K r)

def Kint (n r : ℕ) : Subgroup (GL (Fin n) (Kn p K r)) :=
  (GeneralLinearGroup.map (intR p K r).subtype).range

def KintK (n : ℕ) : Subgroup (GL (Fin n) K) :=
  (GeneralLinearGroup.map (intK p K).subtype).range

end GlobalTheory.LKLoc
end
end
