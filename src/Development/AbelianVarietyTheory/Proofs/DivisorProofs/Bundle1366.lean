module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1228
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle744
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsValuationSubringDominatingSubring
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1261
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GindikinKarpelevich
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1263
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
import Mathlib.LinearAlgebra.PiTensorProduct.Finite
public import Mathlib.LinearAlgebra.PiTensorProduct.Basis
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1193
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle704
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsAlgHomOfIsBaseChange
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1181
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle038

@[expose] public section

section

open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.RealLift

theorem atPl_mem_range_map {ι : Type} [Fintype ι] [DecidableEq ι] {V : ι → Type} [∀ i, AddCommGroup (V i)]
    [∀ i, Module ℂ (V i)] (L : ∀ i, Module.End ℂ (V i)) (N : ∀ i, Submodule ℂ (V i)) (hN : ∀ i, ∀ y ∈ N i, L i y ∈ N i)
    (w : ι) (y : ⨂[ℂ] i, V i) (hy : y ∈ LinearMap.range (PiTensorProduct.map fun i => (N i).subtype)) :
    atPl w (L w) y ∈ LinearMap.range (PiTensorProduct.map fun i => (N i).subtype) := by
  obtain ⟨t, rfl⟩ := hy
  induction t using PiTensorProduct.induction_on with
  | smul_tprod r x =>
    have hx : ∀ j, (Function.update (fun i => (LinearMap.id : V i →ₗ[ℂ] V i)) w (L w) j) (x j : V j) ∈ N j := by
      intro j
      by_cases h : j = w
      · subst h
        simp only [Function.update_self]
        exact hN j _ (x j).2
      · simp only [Function.update_of_ne h, LinearMap.id_apply]
        exact (x j).2
    refine ⟨r • PiTensorProduct.tprod ℂ (fun j => (⟨_, hx j⟩ : N j)), ?_⟩
    simp [atPl, PiTensorProduct.map_tprod]
  | add a b ha hb =>
    rw [map_add (f := _), map_add (f := _)]
    exact Submodule.add_mem _ ha hb

theorem locFin_sumPl : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (V : ι → Type) [∀ i, AddCommGroup (V i)]
    [∀ i, Module ℂ (V i)] (L : ∀ i, Module.End ℂ (V i)), (∀ i, GlobalTheory.RealLift.LocFin (L i)) →
    GlobalTheory.RealLift.LocFin (GlobalTheory.RealLift.sumPl L) := by
  intro ι _ _ V _ _ L hL v
  induction v using PiTensorProduct.induction_on with
  | smul_tprod r f =>
    choose N hNf hfN hN using fun i => hL i (f i)
    refine ⟨LinearMap.range (PiTensorProduct.map fun i => (N i).subtype), inferInstance, ?_, ?_⟩
    · exact ⟨r • PiTensorProduct.tprod ℂ (fun i => (⟨f i, hfN i⟩ : N i)), by simp [PiTensorProduct.map_tprod]⟩
    · intro y hy
      rw [sumPl, LinearMap.sum_apply]
      exact Submodule.sum_mem _ fun w _ => atPl_mem_range_map L N hN w y hy
  | add a b ha hb =>
    obtain ⟨N₁, h₁, ha₁, hs₁⟩ := ha
    obtain ⟨N₂, h₂, hb₂, hs₂⟩ := hb
    refine ⟨N₁ ⊔ N₂, inferInstance, Submodule.add_mem_sup ha₁ hb₂, ?_⟩
    intro y hy
    obtain ⟨y₁, hy₁, y₂, hy₂, rfl⟩ := Submodule.mem_sup.1 hy
    rw [map_add (f := _)]
    exact Submodule.add_mem_sup (hs₁ y₁ hy₁) (hs₂ y₂ hy₂)

end GlobalTheory.RealLift
end

section

noncomputable section

open scoped TensorProduct Matrix GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Classical
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift GlobalTheory.VacLn

namespace GlobalTheory.FockVac

theorem jm_mul_jm_apply {P Q R S : ℕ} (c : Matrix (Ix P Q) (Ix R S) ℂ) (i : Ix P Q) (j : Ix R S) :
    (Jm P Q * c * Jm R S : Matrix (Ix P Q) (Ix R S) ℂ) i j = lineSign (p := P) (q := Q) (r := R) (s := S) i j * c i j := by
  rcases i with i | i <;> rcases j with j | j <;>
    simp [Jm, Formalism.UG.Jpq, lineSign, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply]

theorem heisOp_one {P Q R S : ℕ} (c : Matrix (Ix P Q) (Ix R S) ℂ) :
    heisOp (Complex.I • (Jm P Q * c * Jm R S)) (1 : Formalism.BasicNotions.TH.Pol P Q R S) = Complex.I • heisOp c 1 := by
  simp only [heisOp, LinearMap.smul_apply, LinearMap.sum_apply, LinearMap.sub_apply]
  rw [smul_comm Complex.I]
  congr 1
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl ?_
  rintro ⟨i, j⟩ -
  rw [Matrix.smul_apply, jm_mul_jm_apply]
  rcases i with i | i <;> rcases j with j | j <;>
    simp [raiB, lowB, linePos, lineSign, smul_smul]

theorem atPl_tprod {ι : Type} [Fintype ι] [DecidableEq ι] {V : ι → Type} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
    (w : ι) (L : Module.End ℂ (V w)) (v : ∀ i, V i) :
    atPl w L (PiTensorProduct.tprod ℂ v) = PiTensorProduct.tprod ℂ (Function.update v w (L (v w))) := by
  unfold atPl
  rw [PiTensorProduct.map_tprod]
  congr 1
  funext i
  by_cases h : i = w
  · subst h; simp
  · simp [Function.update_of_ne h]

theorem sumPl_heisOp_vacuum {ι : Type} [Fintype ι] [DecidableEq ι] {P Q R S : ℕ} (c : ι → Matrix (Ix P Q) (Ix R S) ℂ) :
    sumPl (V := fun _ : ι => Pol P Q R S) (fun w => heisOp (Complex.I • (Jm P Q * c w * Jm R S)))
      (PiTensorProduct.tprod ℂ fun _ => 1) =
    Complex.I • sumPl (V := fun _ : ι => Pol P Q R S) (fun w => heisOp (c w)) (PiTensorProduct.tprod ℂ fun _ => 1) := by
  simp only [sumPl, LinearMap.sum_apply, Finset.smul_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [atPl_tprod, atPl_tprod, heisOp_one, MultilinearMap.map_update_smul]
  rfl

end GlobalTheory.FockVac
end
end

section

noncomputable section

open scoped TensorProduct Matrix Classical
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift

namespace GlobalTheory.RealLift

theorem atPl_tprod {ι : Type} [Fintype ι] [DecidableEq ι] {V : ι → Type} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
    (w : ι) (L : Module.End ℂ (V w)) (f : ∀ i, V i) :
    atPl w L (PiTensorProduct.tprod ℂ f) = PiTensorProduct.tprod ℂ (Function.update f w (L (f w))) := by
  unfold atPl
  rw [PiTensorProduct.map_tprod]
  congr 1
  funext i
  by_cases h : i = w
  · subst h; simp
  · simp [Function.update_of_ne h]

theorem mvPolynomial_submodule_eq_top {σ : Type} (S : Submodule ℂ (MvPolynomial σ ℂ)) (h1 : (1 : MvPolynomial σ ℂ) ∈ S)
    (hX : ∀ (l : σ), ∀ p ∈ S, MvPolynomial.X l * p ∈ S) : S = ⊤ := by
  rw [eq_top_iff]
  intro p _
  induction p using MvPolynomial.induction_on with
  | C a =>
    have : (MvPolynomial.C a : MvPolynomial σ ℂ) = a • (1 : MvPolynomial σ ℂ) := by
      rw [MvPolynomial.smul_eq_C_mul, mul_one]
    rw [this]; exact S.smul_mem a h1
  | add p q hp hq => exact S.add_mem (hp trivial) (hq trivial)
  | mul_X p n hp => rw [mul_comm]; exact hX n p (hp trivial)

theorem tensor_submodule_eq_top : ∀ {ι σ : Type} [Fintype ι] [DecidableEq ι] (N : Submodule ℂ (⨂[ℂ] _ : ι, MvPolynomial σ ℂ)),
    PiTensorProduct.tprod ℂ (fun _ => (1 : MvPolynomial σ ℂ)) ∈ N →
    (∀ (w : ι) (l : σ), ∀ T ∈ N, atPl w (LinearMap.mulLeft ℂ (MvPolynomial.X l : MvPolynomial σ ℂ)) T ∈ N) → N = ⊤ := by
  intro ι σ _ _ N h1 hX
  have key : ∀ s : Finset ι, ∀ f : ι → MvPolynomial σ ℂ, (∀ i ∉ s, f i = 1) → PiTensorProduct.tprod ℂ f ∈ N := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro f hf
      have : f = fun _ => 1 := funext fun i => hf i (Finset.notMem_empty i)
      rw [this]; exact h1
    | insert w₀ s hw₀ ih =>
      intro f hf
      let S : Submodule ℂ (MvPolynomial σ ℂ) :=
        N.comap ((PiTensorProduct.tprod ℂ : (∀ _ : ι, MvPolynomial σ ℂ) →ₘₗ[ℂ] (⨂[ℂ] _ : ι, MvPolynomial σ ℂ)).toLinearMap f w₀)
      have hS1 : (1 : MvPolynomial σ ℂ) ∈ S := by
        show PiTensorProduct.tprod ℂ (Function.update f w₀ 1) ∈ N
        apply ih
        intro i hi
        by_cases h : i = w₀
        · subst h; simp
        · rw [Function.update_of_ne h]; exact hf i (by simp [h, hi])
      have hSX : ∀ (l : σ), ∀ p ∈ S, MvPolynomial.X l * p ∈ S := by
        intro l p hp
        have hp' : PiTensorProduct.tprod ℂ (Function.update f w₀ p) ∈ N := hp
        show PiTensorProduct.tprod ℂ (Function.update f w₀ (MvPolynomial.X l * p)) ∈ N
        have := hX w₀ l _ hp'
        rw [atPl_tprod] at this
        simpa using this
      have htop := mvPolynomial_submodule_eq_top S hS1 hSX
      have hf0 : f w₀ ∈ S := by rw [htop]; trivial
      have : PiTensorProduct.tprod ℂ (Function.update f w₀ (f w₀)) ∈ N := hf0
      simpa using this
  rw [eq_top_iff, ← PiTensorProduct.span_tprod_eq_top, Submodule.span_le]
  rintro _ ⟨f, rfl⟩
  exact key Finset.univ f (fun i hi => absurd (Finset.mem_univ i) hi)

end GlobalTheory.RealLift

end
end

section

open scoped TensorProduct Matrix Classical
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift

namespace GlobalTheory.MulVarSpan

variable {P Q R S : ℕ}

theorem heisOp_single (l : Ln P Q R S) (a : ℂ) :
    heisOp (Matrix.single l.1 l.2 a) = ((Real.sqrt (2 * Real.pi) : ℝ) : ℂ) •
      (a • raiB l - (lineSign (p := P) (q := Q) (r := R) (s := S) l.1 l.2 * star a) • lowB l) := by
  unfold heisOp
  congr 1
  rw [Finset.sum_eq_single l]
  · simp [Matrix.single_apply]
  · intro l' _ hne
    have h : ¬ (l.1 = l'.1 ∧ l.2 = l'.2) := by
      rintro ⟨h1, h2⟩; exact hne (Prod.ext h1.symm h2.symm)
    simp [Matrix.single_apply, h]
  · intro h; exact absurd (Finset.mem_univ l) h

theorem sq_ne (l : Ln P Q R S) : ((Real.sqrt (2 * Real.pi) : ℝ) : ℂ) ≠ 0 := by
  have : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.mpr (by positivity)
  exact_mod_cast this.ne'

theorem lineSign_sq (a : Ix P Q) (b : Ix R S) : lineSign a b * lineSign a b = 1 := by
  cases a <;> cases b <;> simp [lineSign]

theorem raiB_mem (l : Ln P Q R S) :
    raiB l ∈ Submodule.span ℂ (Set.range (heisOp (P := P) (Q := Q) (R := R) (S := S))) := by
  set s : ℂ := ((Real.sqrt (2 * Real.pi) : ℝ) : ℂ)
  have key : (2 * s) • raiB l = heisOp (Matrix.single l.1 l.2 1) - Complex.I • heisOp (Matrix.single l.1 l.2 Complex.I) := by
    rw [heisOp_single, heisOp_single]
    simp only [star_one, Complex.star_def, Complex.conj_I, one_smul, mul_one]
    generalize raiB l = A
    generalize lowB l = B
    generalize lineSign (p := P) (q := Q) (r := R) (s := S) l.1 l.2 = σ
    simp only [smul_sub, smul_smul]
    have hI : Complex.I * (s * Complex.I) = -s := by ring_nf; simp [Complex.I_sq]
    have hI2 : Complex.I * (s * (σ * -Complex.I)) = s * σ := by ring_nf; simp [Complex.I_sq]
    rw [hI, hI2]
    module
  have hs : (2 * s) ≠ 0 := mul_ne_zero two_ne_zero (sq_ne l)
  have : raiB l = (2 * s)⁻¹ • (heisOp (Matrix.single l.1 l.2 1) - Complex.I • heisOp (Matrix.single l.1 l.2 Complex.I)) := by
    rw [← key, inv_smul_smul₀ hs]
  rw [this]
  exact Submodule.smul_mem _ _ (sub_mem (Submodule.subset_span ⟨_, rfl⟩)
    (Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)))

theorem lowB_mem (l : Ln P Q R S) :
    lowB l ∈ Submodule.span ℂ (Set.range (heisOp (P := P) (Q := Q) (R := R) (S := S))) := by
  set s : ℂ := ((Real.sqrt (2 * Real.pi) : ℝ) : ℂ)
  set σ := lineSign (p := P) (q := Q) (r := R) (s := S) l.1 l.2 with hσ
  have hσσ : σ * σ = 1 := lineSign_sq l.1 l.2
  have key : (-2 * s * σ) • lowB l = heisOp (Matrix.single l.1 l.2 1) + Complex.I • heisOp (Matrix.single l.1 l.2 Complex.I) := by
    rw [heisOp_single, heisOp_single, ← hσ]
    simp only [star_one, Complex.star_def, Complex.conj_I, one_smul, mul_one]
    generalize raiB l = A
    generalize lowB l = B
    simp only [smul_sub, smul_smul]
    have hI : Complex.I * (s * Complex.I) = -s := by ring_nf; simp [Complex.I_sq]
    have hI2 : Complex.I * (s * (σ * -Complex.I)) = s * σ := by ring_nf; simp [Complex.I_sq]
    rw [hI, hI2]
    module
  have hs : (-2 * s * σ) ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero (by norm_num) (sq_ne l)) ?_
    intro h; rw [h, zero_mul] at hσσ; exact zero_ne_one hσσ
  have : lowB l = (-2 * s * σ)⁻¹ • (heisOp (Matrix.single l.1 l.2 1) + Complex.I • heisOp (Matrix.single l.1 l.2 Complex.I)) := by
    rw [← key, inv_smul_smul₀ hs]
  rw [this]
  exact Submodule.smul_mem _ _ (add_mem (Submodule.subset_span ⟨_, rfl⟩)
    (Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)))

theorem mulX_mem_span : ∀ {P Q R S : ℕ} (l : Ln P Q R S), LinearMap.mulLeft ℂ (MvPolynomial.X l : Formalism.BasicNotions.TH.Pol P Q R S) ∈
    Submodule.span ℂ (Set.range (heisOp (P := P) (Q := Q) (R := R) (S := S))) := by
  intro P Q R S l
  cases h : linePos l
  · have e : LinearMap.mulLeft ℂ (MvPolynomial.X l : Formalism.BasicNotions.TH.Pol P Q R S) = lowB l := by simp [lowB, h]
    rw [e]; exact lowB_mem l
  · have e : LinearMap.mulLeft ℂ (MvPolynomial.X l : Formalism.BasicNotions.TH.Pol P Q R S) = raiB l := by simp [raiB, h]
    rw [e]; exact raiB_mem l

end GlobalTheory.MulVarSpan
end

section

open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix Classical
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift GlobalTheory.RealLift.Dbl

namespace GlobalTheory.HeisRot

theorem jm_eq (p q : ℕ) : Jm p q = Matrix.diagonal (Sum.elim (fun _ => (1 : ℂ)) (fun _ => -1)) := by
  unfold Jm Formalism.UG.Jpq
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [Matrix.fromBlocks, Matrix.one_apply, Matrix.diagonal_apply] <;> split_ifs <;> simp

theorem jm_conj_apply {P Q R S : ℕ} (c : Matrix (Ix P Q) (Ix R S) ℂ) (a : Ix P Q) (b : Ix R S) :
    (Jm P Q * c * Jm R S) a b = lineSign a b * c a b := by
  rw [jm_eq, jm_eq, Matrix.mul_diagonal, Matrix.diagonal_mul]
  rcases a with a | a <;> rcases b with b | b <;> simp [lineSign]

theorem term_eq {P Q R S : ℕ} (c : Matrix (Ix P Q) (Ix R S) ℂ) (t : ℝ) (l : Ln P Q R S) :
    ((((t : ℂ) * Complex.I) • (Jm P Q * c * Jm R S)) l.1 l.2 • raiB l
      - (lineSign (p := P) (q := Q) (r := R) (s := S) l.1 l.2 *
          star ((((t : ℂ) * Complex.I) • (Jm P Q * c * Jm R S)) l.1 l.2)) • lowB l)
        (1 : Formalism.BasicNotions.TH.Pol P Q R S)
      = ((t : ℂ) * Complex.I) • ((c l.1 l.2 • raiB l
          - (lineSign (p := P) (q := Q) (r := R) (s := S) l.1 l.2 * star (c l.1 l.2)) • lowB l)
        (1 : Formalism.BasicNotions.TH.Pol P Q R S)) := by
  obtain ⟨a, b⟩ := l
  rw [Matrix.smul_apply, jm_conj_apply]
  rcases a with a | a <;> rcases b with b | b <;>
    simp [raiB, lowB, linePos, lineSign, Complex.conj_ofReal, smul_smul] <;> ring_nf

theorem heisOp_rot_one (P Q R S : ℕ) (c : Matrix (Ix P Q) (Ix R S) ℂ) (t : ℝ) :
    heisOp (((t : ℂ) * Complex.I) • (Jm P Q * c * Jm R S)) 1 = ((t : ℂ) * Complex.I) • heisOp c 1 := by
  unfold heisOp
  rw [LinearMap.smul_apply, LinearMap.smul_apply, LinearMap.sum_apply, LinearMap.sum_apply,
    Finset.sum_congr rfl (fun l _ => term_eq c t l), ← Finset.smul_sum, smul_comm]

end GlobalTheory.HeisRot
end

section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

noncomputable section

namespace GlobalTheory.ThK.PolRank

open Module

theorem rank_tens_le (F : Type) [Field F] [NumberField F] (P Q R S : ℕ) :
    Module.rank ℂ (GlobalTheory.RealLift.Tens F P Q R S) ≤ Cardinal.aleph0 := by
  classical
  let b := Basis.piTensorProduct (fun _ : InfinitePlace F =>
    (MvPolynomial.basisMonomials _ ℂ : Basis _ ℂ (Formalism.BasicNotions.TH.Pol P Q R S)))
  have hb := b.mk_eq_rank
  rw [Cardinal.lift_id, Cardinal.lift_id] at hb
  rw [← hb]
  exact Cardinal.mk_le_aleph0

theorem incM_map_piInf {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {m : ℕ}
    (J : Matrix (Fin m) (Fin m) E) {w : InfinitePlace F} (τ : EmbOver E w) :
    (incM F J).map (piInf τ) = J.map τ.1 := by
  ext i j
  simp [incM, piInf, inclR, compInf, infEmb_tmul]

end GlobalTheory.ThK.PolRank

end
end

section

open scoped TensorProduct Matrix GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Classical
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift GlobalTheory.VacLn

namespace GlobalTheory.SDUnique

theorem proj_mem_adm {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (x₀ : κ → AF F) :
    (LinearMap.proj x₀ : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ) ∈ (adeleClass F).adm κ := by
  intro g _
  refine ⟨g (fun i => (x₀ i).2) • ((BoundedContinuousFunction.evalCLM ℂ
    (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x₀ i).1)).comp
      (SchwartzMap.toBoundedContinuousFunctionCLM ℂ _ ℂ)), fun f => ?_⟩
  simp [pureA, mul_comm]

theorem sd_unique : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]
    {T : ℝ → ((κ → AF F) → ℂ) → (κ → AF F) → ℂ} {f f₁ f₂ : SInf F κ}, SD T f f₁ → SD T f f₂ → f₁ = f₂ := by
  intro F _ _ κ _ T f f₁ f₂ h₁ h₂
  have hg := GlobalTheory.SchANonzero.indicator_intPts_mem_SB F κ
  refine SchwartzMap.ext fun x => ?_
  let x₀ : κ → AF F := fun i => ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (x i), 0)
  have h := (h₁ _ hg _ (proj_mem_adm x₀)).unique (h₂ _ hg _ (proj_mem_adm x₀))
  have h0 : (fun _ : κ => (0 : Af F)) ∈ GlobalTheory.SchANonzero.intPts F κ := fun i _ v =>
    zero_mem (v.adicCompletionIntegers F)
  have e : ∀ φ : SInf F κ, pureA F φ ((GlobalTheory.SchANonzero.intPts F κ).indicator 1) x₀ = φ x := fun φ => by
    have hx : (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x₀ i).1) = x :=
      funext fun i => RingEquiv.apply_symm_apply _ _
    have h1 : (GlobalTheory.SchANonzero.intPts F κ).indicator (1 : (κ → Af F) → ℂ) (fun i => (x₀ i).2) = 1 :=
      Set.indicator_of_mem h0 _
    unfold pureA
    rw [hx]
    exact (congrArg (φ x * ·) h1).trans (mul_one _)
  exact (e f₁).symm.trans (h.trans (e f₂))

end GlobalTheory.SDUnique
end

section

noncomputable section

open scoped TensorProduct Matrix Classical
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

namespace GlobalTheory.PolCompact

open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem incM_map_piInf' {n m : Type} (J : Matrix n m E) {w : InfinitePlace F} (τ : EmbOver E w) :
    (incM F J).map (piInf τ) = J.map τ.1 := by
  ext i j
  simp [incM, piInf, compInf, inclR, infEmb_tmul]

theorem locFin_second (P Q R S : ℕ) (Y : Mat R S) (hY : IsKC Y) (c : ℂ) :
    LocFin (fockAct2 P Q R S Y + c • 1) := fun v => by
  obtain ⟨⟨W, hW, hv, hs⟩, -⟩ := (GlobalTheory.FockPolGK.pol_locFin_weights P Q R S).2 v
  exact ⟨W, hW, hv, fun y hy => W.add_mem (hs Y hY y hy) (W.smul_mem c hy)⟩

end GlobalTheory.PolCompact

end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy

theorem _root_.GlobalTheory.T.finiteDimensional_functionField_of_etale_on_open' : ∀ (M W : Scheme.{0}) [IsIntegral M] [IsIntegral W] (f : M ⟶ W) [IsDominant f] (U : M.Opens), Etale (U.ι ≫ f) → (U : Set M).Nonempty → letI := (functionFieldMap f).toAlgebra; FiniteDimensional W.functionField M.functionField := by
  first | exact @GlobalTheory.FunctionFieldEtale.finiteDimensional_functionField_of_etale_on_open | exact GlobalTheory.FunctionFieldEtale.finiteDimensional_functionField_of_etale_on_open | (intros; apply GlobalTheory.FunctionFieldEtale.finiteDimensional_functionField_of_etale_on_open <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy

theorem _root_.GlobalTheory.T.etale_restrict_dvr_comap_dominatesStalk : ∀ (M W : Scheme.{0}) [IsIntegral M] [IsIntegral W] (f : M ⟶ W) [IsDominant f] (U : M.Opens), Etale (U.ι ≫ f) → ∀ z ∈ U, ∀ (V : ValuationSubring M.functionField) [IsDiscreteValuationRing V] [IsDiscreteValuationRing (V.comap (functionFieldMap f))], DominatesStalk V z → letI := ((functionFieldMap f).restrict (V.comap (functionFieldMap f)) V fun _ hx => hx).toAlgebra; Algebra.FormallyUnramified (V.comap (functionFieldMap f)) V := by
  first | exact @GlobalTheory.trace_dvr_formallyUnramified_of_etale | exact GlobalTheory.trace_dvr_formallyUnramified_of_etale | (intros; apply GlobalTheory.trace_dvr_formallyUnramified_of_etale <;> assumption)
end

section

open MeasureTheory GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SatakeBound GlobalTheory.WeylCell Formalism.UG GlobalTheory.WeylCell.WeylUnipotentShell

theorem _root_.GlobalTheory.T.hasSum_cSU_power_differences : ∀ (q : ℕ), 2 ≤ q → ∀ z : ℂ, ‖z‖ < 1 →
    HasSum (fun j : ℕ => (z / (q : ℂ) ^ 2) ^ j *
      ((q : ℂ) ^ (j + 2 * (j / 2)) - (if j = 0 then 0 else (q : ℂ) ^ (j - 1 + 2 * ((j - 1) / 2))))) (cSU q z) := by
  first | exact @GlobalTheory.SURankOneSeries.hasSum_series | exact GlobalTheory.SURankOneSeries.hasSum_series | (intros; apply GlobalTheory.SURankOneSeries.hasSum_series <;> assumption)
end
