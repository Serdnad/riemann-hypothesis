module

public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle001
public import Mathlib.Data.Matrix.Mul
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Objects
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
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
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
public import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
public import Mathlib.LinearAlgebra.Dual.Basis
public import Mathlib.LinearAlgebra.LinearIndependent.Basic
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.RingTheory.AlgebraicIndependent.Basic
public import Mathlib.RingTheory.AlgebraicIndependent.Transcendental

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

theorem QuotientHeightAddOne.proof : QuotientHeightAddOne.Statement := by
  intro R _ _ I hI P _
  let φ : PrimeSpectrum (R ⧸ I) → PrimeSpectrum R := PrimeSpectrum.comap (Ideal.Quotient.mk I)
  have hφ : StrictMono φ := RingHom.strictMono_comap_of_surjective Ideal.Quotient.mk_surjective
  let z : PrimeSpectrum R := ⟨⊥, Ideal.isPrime_bot⟩

  have hz : ∀ q : PrimeSpectrum (R ⧸ I), z < φ q := by
    intro q
    refine lt_of_le_of_ne (show z.asIdeal ≤ (φ q).asIdeal from bot_le) fun h => hI ?_
    have hle : I ≤ (φ q).asIdeal := by
      intro x hx
      change Ideal.Quotient.mk I x ∈ q.asIdeal
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr hx]
      exact q.asIdeal.zero_mem
    rw [← h] at hle
    exact le_bot_iff.mp hle
  let p : PrimeSpectrum (R ⧸ I) := ⟨P, ‹_›⟩
  have h1 : P.height = Order.height p := PrimeSpectrum.height_eq_orderHeight p
  have h2 : (P.comap (Ideal.Quotient.mk I)).height = Order.height (φ p) :=
    PrimeSpectrum.height_eq_orderHeight (φ p)
  have hne : Nonempty { l : LTSeries (PrimeSpectrum (R ⧸ I)) // l.last = p } :=
    ⟨⟨RelSeries.singleton _ p, rfl⟩⟩
  rw [h1, h2, Order.height_eq_iSup_last_eq p, iSup_subtype', ENat.iSup_add, iSup_le_iff]
  rintro ⟨l, hl⟩
  let l' : LTSeries (PrimeSpectrum R) :=
    (l.map φ hφ).cons z (by simpa using hz l.head)
  have hlast : l'.last = φ p := by simp [l', hl]
  have := Order.length_le_height (p := l') hlast.le
  simpa [l'] using this

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

universe u

open Polynomial

theorem PolynomialDimensionInequality.proof (h : PolynomialPrimeOverZeroHeight.Statement.{u}) :
    PolynomialDimensionInequality.Statement.{u} := by
  intro A _ _ _ P _
  set p := P.under A with hp
  let I : Ideal A[X] := p.map (algebraMap A A[X])
  let Pb : Ideal (A[X] ⧸ I) := P.map (Ideal.Quotient.mk I)
  have hIP : I ≤ P := Ideal.map_comap_le
  have hPb : Pb.IsPrime := Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective
    (by rw [Ideal.mk_ker]; exact hIP)

  let x : A[X] ⧸ P := Ideal.Quotient.mk P X
  have key : ∀ f : A[X], aeval x (f.map (Ideal.Quotient.mk p)) = Ideal.Quotient.mk P f := by
    intro f
    rw [← Ideal.Quotient.algebraMap_eq, aeval_map_algebraMap]
    change aeval (Ideal.Quotient.mkₐ A P X) f = _
    rw [aeval_algHom_apply, aeval_X_left_apply]
    rfl
  have hsurj : Function.Surjective (aeval (R := A ⧸ p) x) := by
    intro y
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective y
    exact ⟨_, key f⟩

  have hPb1 : Pb.height ≤ 1 := by
    let e : (A[X] ⧸ I) ≃+* (A ⧸ p)[X] := (Ideal.polynomialQuotientEquivQuotientPolynomial p).symm
    let Q : Ideal (A ⧸ p)[X] := Pb.map e
    have hQ : Q.IsPrime := Ideal.map_isPrime_of_equiv e
    have hQb : Q.comap (C : A ⧸ p →+* (A ⧸ p)[X]) = ⊥ := by
      refine le_bot_iff.mp fun a ha => ?_
      obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective a
      rw [Ideal.mem_comap] at ha
      have he : C (Ideal.Quotient.mk p b) = e (Ideal.Quotient.mk I (C b)) := by
        change _ = (Ideal.polynomialQuotientEquivQuotientPolynomial p).symm
          (Ideal.Quotient.mk (p.map C) (C b))
        rw [Ideal.polynomialQuotientEquivQuotientPolynomial_symm_mk, Polynomial.map_C]
      rw [he] at ha
      obtain ⟨y, hy, hye⟩ := (Ideal.mem_map_of_equiv e _).mp ha
      rw [e.injective hye, Ideal.mem_quotient_iff_mem hIP] at hy
      rw [Ideal.mem_bot, Ideal.Quotient.eq_zero_iff_mem, hp, Ideal.under_def, Ideal.mem_comap,
        Polynomial.algebraMap_eq]
      exact hy
    have := h (A ⧸ p) Q hQb
    rwa [RingEquiv.height_map] at this
  have hht : P.height ≤ p.height + Pb.height := Ideal.height_le_height_add_of_liesOver p P
  by_cases hb : Pb = ⊥
  ·
    have : Nontrivial (A[X] ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr
      (ne_top_of_le_ne_top (Ideal.IsPrime.ne_top inferInstance) hIP)
    rw [hb, Ideal.height_bot, add_zero] at hht
    have htr : Algebra.trdeg (A ⧸ p) (A[X] ⧸ P) ≤ 1 :=
      (trdeg_le_of_surjective _ hsurj).trans (Polynomial.trdeg_of_isDomain).le
    exact add_le_add (Cardinal.ofENat_le_ofENat.mpr hht) htr
  ·
    obtain ⟨y, hyPb, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hb
    obtain ⟨f, hfP, rfl⟩ := (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).mp hyPb
    have hfI : f ∉ I := fun hf => hy0 (Ideal.Quotient.eq_zero_iff_mem.mpr hf)
    have hg : f.map (Ideal.Quotient.mk p) ≠ 0 := by
      intro hg
      apply hfI
      rw [show I = p.map C from rfl, Ideal.mem_map_C_iff]
      intro n
      rw [← Ideal.Quotient.eq_zero_iff_mem, ← coeff_map, hg, coeff_zero]
    have hx : IsAlgebraic (A ⧸ p) x :=
      ⟨_, hg, by rw [key]; exact Ideal.Quotient.eq_zero_iff_mem.mpr hfP⟩
    have hadj : Algebra.adjoin (A ⧸ p) {x} = ⊤ := by
      rw [Algebra.adjoin_singleton_eq_range_aeval, AlgHom.range_eq_top]
      exact hsurj
    have halg : Algebra.IsAlgebraic (A ⧸ p) (A[X] ⧸ P) := by
      have := Algebra.isAlgebraic_adjoin_singleton_iff.mpr hx
      rw [hadj] at this
      exact ⟨fun z => this z Algebra.mem_top⟩
    rw [trdeg_eq_zero_iff.mpr halg, add_zero, ← Cardinal.ofENat_one, ← Cardinal.ofENat_add,
      Cardinal.ofENat_le_ofENat]
    exact hht.trans (add_le_add le_rfl hPb1)

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

theorem PairConeLinesIndep.formMatrix_isUnit {Ω E : Type} [Field Ω] [AddCommGroup E] [Module Ω E] {N : ℕ}
    (e : Module.Basis (Fin N) Ω E) (ψ : Fin N → Module.Dual Ω E) (hψ : LinearIndependent Ω ψ) :
    IsUnit (Matrix.of fun i j => ψ i (e j)) := by
  rw [← Matrix.linearIndependent_rows_iff_isUnit]
  have h := hψ.map' e.dualBasis.equivFun.toLinearMap e.dualBasis.equivFun.ker
  have hrows : (Matrix.of fun i j => ψ i (e j)).row = ⇑e.dualBasis.equivFun ∘ ψ := by
    funext i
    funext j
    simp [Matrix.row, Module.Basis.equivFun_apply]
  rw [hrows]
  exact h

theorem PairConeLinesIndep.linearChange_indep {Ω Φ : Type} [Field Ω] [Field Φ] [Algebra Ω Φ] {N : ℕ}
    (P : Matrix (Fin N) (Fin N) Ω) (hP : IsUnit P) (t : Fin N → Φ) (ht : AlgebraicIndependent Ω t) :
    AlgebraicIndependent Ω (fun i => ∑ j, t j * algebraMap Ω Φ (P i j)) := by
  have hdet : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).mp hP
  let f : Fin N → MvPolynomial (Fin N) Ω := fun i => ∑ j, X j * C (P i j)
  let g : Fin N → MvPolynomial (Fin N) Ω := fun j => ∑ k, X k * C (P⁻¹ j k)
  have hgf : (fun i => aeval g (f i)) = X := by
    funext i

    simp only [f, g, map_sum, map_mul, aeval_X, aeval_C, MvPolynomial.algebraMap_eq]
    calc ∑ j, (∑ k, X k * C (P⁻¹ j k)) * C (P i j)
        = ∑ k, X k * C ((P * P⁻¹) i k) := by

          simp_rw [Finset.sum_mul, Matrix.mul_apply, map_sum, Finset.mul_sum]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => ?_
          rw [map_mul]
          ring
      _ = X i := by
          rw [Matrix.mul_nonsing_inv _ hdet]
          simp [Matrix.one_apply]
  have hf : AlgebraicIndependent Ω f := by
    apply AlgebraicIndependent.of_aeval (x := g)
    rw [hgf]
    exact algebraicIndependent_X _ _
  have h := ht.aeval_of_algebraicIndependent hf
  convert h using 1
  funext i

  simp [f, map_sum, aeval_X]

theorem PairConeLinesIndep.proof : PairConeLinesIndep.Statement := by
  intro Ω _ Φ _ _ K N E _ _ e ψ hψ t ht g hg
  have hw : AlgebraicIndependent Ω (fun i => ∑ j, t j * algebraMap Ω Φ (ψ i (e j))) :=
    PairConeLinesIndep.linearChange_indep (Matrix.of fun i j => ψ i (e j))
      (PairConeLinesIndep.formMatrix_isUnit e ψ hψ) t ht
  let T : K → MvPolynomial (Option (Option K)) Φ := fun k => X (some (some k))
  let idx : Unit ⊕ K → Option (Option K) := Sum.elim (fun _ => none) (fun k => some (some k))
  have hidx : Function.Injective idx := by
    rintro (_ | a) (_ | b) h <;> simp_all [idx]
  have hvars : AlgebraicIndependent Φ (X ∘ idx : Unit ⊕ K → MvPolynomial (Option (Option K)) Φ) :=
    (algebraicIndependent_X _ _).comp idx hidx
  have hA := AlgebraicIndependent.sumElim_comp hw hvars
  have hB : AlgebraicIndependent Ω
      (Sum.elim (Sum.elim (fun i => C (∑ j, t j * algebraMap Ω Φ (ψ i (e j))))
        (fun _ : Unit => (X none : MvPolynomial (Option (Option K)) Φ))) T) := by
    have h := hA.comp ((Equiv.sumAssoc _ _ _).trans (Equiv.sumComm _ _)) (Equiv.injective _)
    convert h using 1
    funext x
    rcases x with ((i | u) | k) <;> simp [idx, T, MvPolynomial.algebraMap_eq]
  have hC := (AlgebraicIndependent.sumElim_iff.mp hB).2
  let σ : MvPolynomial (Option (Option K)) Φ →ₐ[Φ] MvPolynomial (Option (Option K)) Φ :=
    aeval fun o => Option.elim o (C g⁻¹ * X none) (fun o' => Option.elim o' 1 (fun k => X (some (some k))))
  have hfix : Algebra.adjoin Ω (Set.range T) ≤ AlgHom.equalizer (σ.restrictScalars Ω) (AlgHom.id Ω _) := by
    refine Algebra.adjoin_le ?_
    rintro _ ⟨k, rfl⟩
    simp [σ, T]
  let f : MvPolynomial (Option (Option K)) Φ →ₐ[Algebra.adjoin Ω (Set.range T)]
      MvPolynomial (Option (Option K)) Φ :=
    { σ.toRingHom with commutes' := fun r => hfix r.2 }
  apply AlgebraicIndependent.of_comp f
  convert hC using 1
  funext x
  rcases x with i | u
  · simp [f, σ]
  · change σ (C g * X none) = X none
    simp only [σ, map_mul, aeval_C, aeval_X, Option.elim, MvPolynomial.algebraMap_eq]
    rw [← mul_assoc, ← C_mul, mul_inv_cancel₀ hg, C_1, one_mul]

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

section Defs

variable {K : Type*} [DecidableEq K] {ι : K → Type*}
variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

def IsEffectiveVertical (P : Ideal (MRing ι O)) (ϖ : O) (b : K → ℤ) (f g : MRing ι O) : Prop :=
  IsVerticalDivisor P ϖ b f g ∧ ∀ W : Ideal (MRing ι O), W.IsPrime → P ≤ W → IsRelevant W →
    ∃ u v : MRing ι O, u ∉ W ∧ u * f - v * g ∈ P


open Classical in
def cutIdentity (ϖ : O) (P : Ideal (MRing ι O)) (b : K → ℤ) (f g : MRing ι O) (c : K → ℕ)
    (s : MRing ι O) {d : ℕ} (L : Fin d → K → ℤ) : Prop :=
  by
    classical
    exact cycEval (fun G => vNum G (Matrix.vecCons (fun k => (c k : ℤ)) L)) (ratDiv P f g) =
      cycEval (fun W => if (C ϖ : MRing ι O) ∈ W then vNum W (Matrix.vecCons b L)
          else cycEval (fun G => vNum G L) (ratDiv W f g)) (divCycle P s)

end Defs

section Lemmas

def DivCycleMul.Statement : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R] (K : Type) [Fintype K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (P : Ideal (MRing ι R)) (x y : MRing ι R), P.IsPrime → x ∉ P → y ∉ P →
    divCycle P (x * y) = divCycle P x + divCycle P y

def DivCycleFiniteSupport.Statement : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R] (K : Type) [Fintype K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (P : Ideal (MRing ι R)) (f : MRing ι R),
    (Function.support (divCycle P f)).Finite

def SupSpanMultiHomog.Statement : Prop :=
  ∀ (R : Type u) [CommRing R] (K : Type) [DecidableEq K] (ι : K → Type) (I : Ideal (MRing ι R))
    (x : MRing ι R) (e : K → ℕ), IsMultiHomogIdeal I → IsMultiHomog x e →
    IsMultiHomogIdeal (I ⊔ Ideal.span {x})

def MinimalPrimeMultiHomog.Statement : Prop :=
  ∀ (R : Type u) [CommRing R] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    (J W : Ideal (MRing ι R)), IsMultiHomogIdeal J → W ∈ J.minimalPrimes → IsMultiHomogIdeal W

def IntNumAddFirst.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (n : ℕ) (G : Ideal (MRing ι F)), G.IsPrime → IsMultiHomogIdeal G →
    ringKrullDim (MRing ι F ⧸ G) < ((n + 2 + Fintype.card K : ℕ) : WithBot ℕ∞) →
    ∀ (b₁ b₂ : K → ℤ) (L : Fin n → K → ℤ),
      intNum F G (Matrix.vecCons (b₁ + b₂) L) =
        intNum F G (Matrix.vecCons b₁ L) + intNum F G (Matrix.vecCons b₂ L)

def SpecialQuotDim.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (W : Ideal (MRing ι O)), (C ϖ : MRing ι O) ∈ W →
    ringKrullDim (MRing ι (IsLocalRing.ResidueField O) ⧸ specialIdeal W) =
      ringKrullDim (MRing ι O ⧸ W)

def GenericDimBound.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (K : Type) [Fintype K]
    [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι O)),
    IsMultiProjPrime P → P.comap (C : O →+* MRing ι O) = ⊥ →
    ringKrullDim (MRing ι (FractionRing O) ⧸ genFib P) + 1 ≤ ringKrullDim (MRing ι O ⧸ P)

def GenericFibProps.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (K : Type) [Fintype K]
    [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι O)),
    IsMultiProjPrime P → P.comap (C : O →+* MRing ι O) = ⊥ →
    (genFib P).IsPrime ∧ IsMultiHomogIdeal (genFib P) ∧
    ∀ (s : MRing ι O) (c : K → ℕ), IsMultiHomog s c → s ∉ P →
      IsMultiHomog (MvPolynomial.map (algebraMap O (FractionRing O)) s) c ∧
        MvPolynomial.map (algebraMap O (FractionRing O)) s ∉ genFib P


open Classical in
def GenericCycleCorresp.Statement : Prop :=
  by
  classical
  exact ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι O)) (s : MRing ι O), P.IsPrime →
    P.comap (C : O →+* MRing ι O) = ⊥ → s ∉ P →
    ∀ n : Ideal (MRing ι (FractionRing O)) → ℤ,
      cycEval (fun W => if (C ϖ : MRing ι O) ∈ W then 0 else n (genFib W)) (divCycle P s) =
        cycEval n (divCycle (genFib P) (MvPolynomial.map (algebraMap O (FractionRing O)) s))

def ConservationOfNumberLE.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι O)) (d : ℕ), IsMultiProjPrime P →
    P.comap (C : O →+* MRing ι O) = ⊥ →
    ringKrullDim (MRing ι O ⧸ P) ≤ ((d + 1 + Fintype.card K : ℕ) : WithBot ℕ∞) →
    ∀ a : Fin d → K → ℤ, cycEval (fun W => vNum W a) (divCycle P (C ϖ)) = gNum P a

def UniformiserCase.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι O)) (d : ℕ), IsModelOver P (d + 1) →
    ∀ (c : K → ℕ) (s : MRing ι O), IsMultiHomog s c → s ∉ P →
    ∀ L : Fin d → K → ℤ, cutIdentity ϖ P 0 (C ϖ) 1 c s L

def ShiftByUniformiser.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι O)) (d : ℕ), IsModelOver P (d + 1) →
    ∀ (b : K → ℤ) (f g : MRing ι O), IsVerticalDivisor P ϖ b f g →
    ∀ (c : K → ℕ) (s : MRing ι O), IsMultiHomog s c → s ∉ P →
    (∀ H, divCycle P s H ≠ 0 → (C ϖ : MRing ι O) ∉ H → IsVerticalDivisor H ϖ b f g) →
    ∀ (L : Fin d → K → ℤ) (n : ℕ),
      cutIdentity ϖ P b (C ϖ ^ n * f) g c s L → cutIdentity ϖ P 0 (C ϖ) 1 c s L →
        cutIdentity ϖ P b f g c s L

def EffectiveShift.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι O)) (e : ℕ), IsModelOver P e →
    ∀ (b : K → ℤ) (f g : MRing ι O), IsVerticalDivisor P ϖ b f g →
    ∃ n : ℕ, IsEffectiveVertical P ϖ b (C ϖ ^ n * f) g

def EffectiveCase.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι O)) (d : ℕ), IsModelOver P (d + 1) →
    ∀ (b : K → ℤ) (f g : MRing ι O), IsEffectiveVertical P ϖ b f g →
    ∀ (c : K → ℕ) (s : MRing ι O), IsMultiHomog s c → s ∉ P →
    (∀ H, divCycle P s H ≠ 0 → (C ϖ : MRing ι O) ∉ H → IsVerticalDivisor H ϖ b f g) →
    ∀ L : Fin d → K → ℤ, cutIdentity ϖ P b f g c s L

def Representative.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι O)) (b : K → ℤ) (f g : MRing ι O), IsMultiProjPrime P →
    IsVerticalDivisor P ϖ b f g → ∀ T : Finset (Ideal (MRing ι O)),
    (∀ H ∈ T, IsMultiProjPrime H ∧ P ≤ H ∧ (C ϖ : MRing ι O) ∉ H ∧
      ∃ h : MRing ι O, h ∉ P ∧ H ∈ (P ⊔ Ideal.span {h}).minimalPrimes) →
    ∃ f₁ g₁ : MRing ι O, IsVerticalDivisor P ϖ b f₁ g₁ ∧ ratDiv P f₁ g₁ = ratDiv P f g ∧
      ∀ H ∈ T, IsVerticalDivisor H ϖ b f₁ g₁

end Lemmas

section Examples

theorem isMultiHomogIdeal_span_singleton {K : Type*} [DecidableEq K] {ι : K → Type*} {R : Type*}
    [CommRing R] {x : MRing ι R} {e : K → ℕ} (hx : IsMultiHomog x e) :
    IsMultiHomogIdeal (Ideal.span {x}) := by
  classical
  letI := MvPolynomial.weightedGradedAlgebra R (blockWeight ι)
  have h : (Ideal.span {x}).IsHomogeneous (weightedHomogeneousSubmodule R (blockWeight ι)) :=
    Ideal.homogeneous_span _ _ (by
      rintro y rfl
      exact ⟨e, hx⟩)
  intro f hf b
  exact MvPolynomial.weightedHomogeneousComponent_mem_of_mem R (blockWeight ι) h hf b

end Examples

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

def FibreVarieties.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (P : Ideal (MRing ι O)) (d : ℕ), IsModelOver P d →
      (IsMultiProjPrime (genFib P) ∧
        ringKrullDim (MRing ι (FractionRing O) ⧸ genFib P) =
          ((d + Fintype.card K : ℕ) : WithBot ℕ∞)) ∧
      ∀ W : Ideal (MRing ι O), divCycle P (C ϖ) W ≠ 0 →
        IsMultiProjPrime (specialIdeal W) ∧
          ringKrullDim (MRing ι (IsLocalRing.ResidueField O) ⧸ specialIdeal W) =
            ((d + Fintype.card K : ℕ) : WithBot ℕ∞)

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

def MultAtOfSaturated.Statement : Prop :=
  ∀ (R : Type u) [CommRing R] (K : Type) (ι : K → Type) (J Q : Ideal (MRing ι R)) [Q.IsPrime],
    J ≤ Q → (∀ q ∈ Q, ∃ s ∉ Q, s * q ∈ J) → Q ∈ J.minimalPrimes ∧ multAt J Q = 1

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end
