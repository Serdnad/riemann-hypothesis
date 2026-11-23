module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DifferentiableAtChart
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
public import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm
public import Mathlib.Basic.Complex.Basic
public import Mathlib.GroupTheory.SemidirectProduct
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle308
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle184
import Mathlib.Algebra.Category.ModuleCat.Algebra
public import Development.AbelianVarietyTheory.Definitions.Degenerations.SepticCharacterInjective
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle037
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RiemannInequalityCofinalFunctionField
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle678
public import Development.AbelianVarietyTheory.Definitions.Divisors.PullHlComp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle677
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle676
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle507
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle679
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.Quiver.ReflQuiver
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsOpenKerFinIdele
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle003
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle003

@[expose] public section

section

open NumberField
open scoped ContDiff

namespace GlobalTheory.SecondKind

open GlobalTheory.CuspRep

variable {E : Type} [Field E] [NumberField E] {d : ℕ}

theorem prod_ofFn_eq_of_ne {M : Type*} [Monoid M] {k : ℕ} (f : Fin k → M) (i : Fin k)
    (h : ∀ j, j ≠ i → f j = 1) : (List.ofFn f).prod = f i := by
  induction k with
  | zero => exact i.elim0
  | succ k ih =>
    rw [List.ofFn_succ, List.prod_cons]
    cases i using Fin.cases with
    | zero =>
      rw [List.prod_eq_one, mul_one]
      intro x hx
      obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hx
      exact h _ (Fin.succ_ne_zero j)
    | succ i =>
      rw [h 0 (Fin.succ_ne_zero i).symm, one_mul]
      exact ih _ i fun j hj => h _ fun e => hj (Fin.succ_injective _ e)

theorem contDiff_prodExp (y : Lie E d) {k : ℕ} (X : Fin k → Matrix (Fin d) (Fin d) (Cinf E)) :
    ContDiff ℝ ∞ (fun t : Fin k → ℝ =>
      toL (Matrix.of y * (List.ofFn fun i => NormedSpace.exp (t i • X i)).prod)) := by
  letI : NormedRing (Matrix (Fin d) (Fin d) (Cinf E)) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℝ (Matrix (Fin d) (Fin d) (Cinf E)) := Matrix.linftyOpNormedAlgebra
  haveI : CompleteSpace (Matrix (Fin d) (Fin d) (Cinf E)) := FiniteDimensional.complete ℝ _
  let T : Matrix (Fin d) (Fin d) (Cinf E) →L[ℝ] Lie E d :=
    LinearMap.toContinuousLinearMap (LinearMap.id : Lie E d →ₗ[ℝ] Lie E d)
  have hexp : ContDiff ℝ ∞ (NormedSpace.exp : Matrix (Fin d) (Fin d) (Cinf E) → _) :=
    contDiff_iff_contDiffAt.2 fun x => (NormedSpace.exp_analytic (𝕂 := ℝ) x).contDiffAt
  have hprod : ∀ (n : ℕ) (g : Fin n → (Fin k → ℝ) → Matrix (Fin d) (Fin d) (Cinf E)),
      (∀ i, ContDiff ℝ ∞ (g i)) → ContDiff ℝ ∞ (fun t => (List.ofFn fun i => g i t).prod) := by
    intro n
    induction n with
    | zero => intro g _; simpa using contDiff_const
    | succ n ih =>
      intro g hg
      simp only [List.ofFn_succ, List.prod_cons]
      exact (hg 0).mul (ih _ fun i => hg _)
  have h := hprod k (fun i t => NormedSpace.exp (t i • X i))
    fun i => hexp.comp ((contDiff_apply ℝ (fun _ => ℝ) i).smul contDiff_const)
  exact T.contDiff.comp (contDiff_const.mul h)

end GlobalTheory.SecondKind

namespace GlobalTheory.SecondKind

open GlobalTheory.CuspRep

variable {E : Type} [Field E] [NumberField E] {d : ℕ}

theorem hasDerivAt_mulExp (y : Lie E d) (Z : Matrix (Fin d) (Fin d) (Cinf E)) :
    HasDerivAt (fun s : ℝ => toL (Matrix.of y * NormedSpace.exp (s • Z))) (toL (Matrix.of y * Z)) 0 := by
  letI : NormedRing (Matrix (Fin d) (Fin d) (Cinf E)) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℝ (Matrix (Fin d) (Fin d) (Cinf E)) := Matrix.linftyOpNormedAlgebra
  haveI : CompleteSpace (Matrix (Fin d) (Fin d) (Cinf E)) := FiniteDimensional.complete ℝ _
  let T : Matrix (Fin d) (Fin d) (Cinf E) →L[ℝ] Lie E d :=
    LinearMap.toContinuousLinearMap (LinearMap.id : Lie E d →ₗ[ℝ] Lie E d)
  have h := ((hasDerivAt_exp_smul_const' (𝕂 := ℝ) Z (0 : ℝ)).const_mul (Matrix.of y))
  rw [zero_smul, NormedSpace.exp_zero, mul_one] at h
  exact T.hasFDerivAt.comp_hasDerivAt (0 : ℝ) h

theorem fderiv_prodExp (y : Lie E d) {k : ℕ} (X : Fin k → Matrix (Fin d) (Fin d) (Cinf E)) (i : Fin k) (c : ℝ) :
    fderiv ℝ (fun t : Fin k → ℝ =>
      toL (Matrix.of y * (List.ofFn fun i => NormedSpace.exp (t i • X i)).prod)) 0 (Pi.single i c) =
      c • toL (Matrix.of y * X i) := by
  set Θ := fun t : Fin k → ℝ =>
      toL (Matrix.of y * (List.ofFn fun i => NormedSpace.exp (t i • X i)).prod)
  have hΘ : HasFDerivAt Θ (fderiv ℝ Θ 0) (0 : Fin k → ℝ) :=
    ((contDiff_prodExp y X).differentiable (by simp)).differentiableAt.hasFDerivAt
  let J : ℝ →L[ℝ] (Fin k → ℝ) := ContinuousLinearMap.single ℝ (fun _ : Fin k => ℝ) i
  have hJ0 : J 0 = 0 := map_zero J
  have h1 : HasFDerivAt (Θ ∘ J) ((fderiv ℝ Θ 0).comp J) 0 := by
    have hΘ' : HasFDerivAt Θ (fderiv ℝ Θ 0) (J 0) := by rw [hJ0]; exact hΘ
    exact hΘ'.comp (0 : ℝ) J.hasFDerivAt
  have e : Θ ∘ J = fun s : ℝ => toL (Matrix.of y * NormedSpace.exp (s • X i)) := by
    funext s
    simp only [Function.comp_apply, Θ]
    congr 2
    rw [prod_ofFn_eq_of_ne _ i]
    · simp [J]
    · intro j hj
      simp [J, Pi.single_eq_of_ne hj]
  rw [e] at h1
  have h2 := h1.hasDerivAt.unique (hasDerivAt_mulExp y (X i))
  have h3 : Pi.single i c = c • J 1 := by
    simp [J, ← Pi.single_smul]
  rw [h3, map_smul]
  simpa using congrArg (c • ·) h2

end GlobalTheory.SecondKind

namespace GlobalTheory.SecondKind

open GlobalTheory.CuspRep

theorem contDiffOn_of_prodExp : ∀ (E : Type) [Field E] [NumberField E] (d : ℕ) (f : GlobalTheory.CuspRep.Lie E d → ℂ)
    (S : Set (Matrix (Fin d) (Fin d) (GlobalTheory.CuspRep.Cinf E))), Submodule.span ℝ S = ⊤ →
    (∀ (k : ℕ) (X : Fin k → Matrix (Fin d) (Fin d) (GlobalTheory.CuspRep.Cinf E)), (∀ i, X i ∈ S) →
      ∀ y ∈ GlobalTheory.CuspRep.invSet E d, ContDiff ℝ ∞ fun t : Fin k → ℝ =>
        f (GlobalTheory.CuspRep.toL (Matrix.of y * (List.ofFn fun i => NormedSpace.exp (t i • X i)).prod))) →
    ContDiffOn ℝ ∞ f (GlobalTheory.CuspRep.invSet E d) := by
  intro E _ _ d f S hS hf x₀ hx₀
  refine ContDiffAt.contDiffWithinAt ?_

  obtain ⟨b, hbS, hbspan, hbli⟩ := exists_linearIndependent ℝ S
  haveI : Module.Finite ℝ (Matrix (Fin d) (Fin d) (Cinf E)) := inferInstance
  haveI : Finite b := hbli.finite
  letI : Fintype b := Fintype.ofFinite b
  set m := Fintype.card b
  let e := Fintype.equivFin b
  let X : Fin m → Matrix (Fin d) (Fin d) (Cinf E) := fun i => (e.symm i).1
  have hXS : ∀ i, X i ∈ S := fun i => hbS (e.symm i).2
  have hXli : LinearIndependent ℝ X := hbli.comp e.symm e.symm.injective
  have hXspan : Submodule.span ℝ (Set.range X) = ⊤ := by
    have : Set.range X = b := by
      ext x; constructor
      · rintro ⟨i, rfl⟩; exact (e.symm i).2
      · intro hx; exact ⟨e ⟨x, hx⟩, by simp [X]⟩
    rw [this, hbspan, hS]
  let B : Module.Basis (Fin m) ℝ (Matrix (Fin d) (Fin d) (Cinf E)) := Module.Basis.mk hXli hXspan.ge
  have hdim : Module.finrank ℝ (Fin m → ℝ) = Module.finrank ℝ (Lie E d) := by
    rw [Module.finrank_fin_fun]
    exact (Module.finrank_eq_card_basis B).trans (Fintype.card_fin m) |>.symm

  let Lin : (Fin m → ℝ) →ₗ[ℝ] Lie E d :=
    { toFun := fun t => toL (Matrix.of x₀ * ∑ i, t i • X i)
      map_add' := fun s t => by
        simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib, mul_add]; rfl
      map_smul' := fun c t => by
        simp only [Pi.smul_apply, smul_eq_mul, mul_smul, ← Finset.smul_sum, Matrix.mul_smul]; rfl }
  have hLinj : Function.Injective Lin := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro t ht
    have h1 : Matrix.of x₀ * ∑ i, t i • X i = Matrix.of x₀ * 0 := by
      rw [mul_zero]; exact ht
    have h2 := (show IsUnit (Matrix.of x₀) from hx₀).mul_left_cancel h1
    funext i
    exact Fintype.linearIndependent_iff.1 hXli t h2 i
  let L : (Fin m → ℝ) ≃L[ℝ] Lie E d :=
    (LinearMap.linearEquivOfInjective Lin hLinj hdim).toContinuousLinearEquiv
  set Θ := fun t : Fin m → ℝ =>
      toL (Matrix.of x₀ * (List.ofFn fun i => NormedSpace.exp (t i • X i)).prod) with hΘdef
  have hΘ : ContDiff ℝ ∞ Θ := contDiff_prodExp x₀ X
  have hΘ0 : Θ 0 = x₀ := by
    simp [Θ]
  have hD : HasFDerivAt Θ (L : (Fin m → ℝ) →L[ℝ] Lie E d) 0 := by
    have h := ((hΘ.differentiable (by simp)) 0).hasFDerivAt
    have hE : ((L : (Fin m → ℝ) →L[ℝ] Lie E d) : (Fin m → ℝ) →ₗ[ℝ] Lie E d) =
        ((fderiv ℝ Θ 0 : (Fin m → ℝ) →L[ℝ] Lie E d) : (Fin m → ℝ) →ₗ[ℝ] Lie E d) := by
      refine LinearMap.pi_ext fun i c => ?_
      change Lin (Pi.single i c) = fderiv ℝ Θ 0 (Pi.single i c)
      rw [hΘdef, fderiv_prodExp]
      simp only [Lin, LinearMap.coe_mk, AddHom.coe_mk]
      rw [Finset.sum_eq_single i (fun j _ hj => by simp [Pi.single_eq_of_ne hj]) (by simp)]
      simp only [Pi.single_eq_same, Matrix.mul_smul]
      rfl
    rw [ContinuousLinearMap.coe_injective hE]
    exact h
  have hn : (∞ : ℕ∞ω) ≠ 0 := by simp
  have hΨ := hΘ.contDiffAt.to_localInverse hD hn
  have hinv := (hΘ.contDiffAt.hasStrictFDerivAt' hD hn).eventually_right_inverse
  have hc : ContDiffAt ℝ ∞ (f ∘ Θ ∘ hΘ.contDiffAt.localInverse hD hn) (Θ 0) :=
    (hf m X hXS x₀ hx₀).contDiffAt.comp _ hΨ
  rw [hΘ0] at hc hinv
  refine hc.congr_of_eventuallyEq (hinv.mono fun x hx => ?_)
  simp only [Function.comp_apply]
  exact congrArg f hx.symm

end GlobalTheory.SecondKind
end

section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

namespace GlobalTheory.Shin.CosetOrth

def twist {H V : Type} [Group H] [AddCommGroup V] [Module ℂ V] (η : H →* ℂˣ) (a : ℕ)
    (ρ : Representation ℂ H V) : Representation ℂ H V where
  toFun x := ((η x : ℂ) ^ a) • ρ x
  map_one' := by simp
  map_mul' x y := by
    rw [map_mul, map_mul, Units.val_mul, mul_pow, Module.End.mul_eq_comp, Module.End.mul_eq_comp,
      LinearMap.smul_comp, LinearMap.comp_smul, smul_smul, mul_comm]

theorem trace_twist {H V : Type} [Group H] [AddCommGroup V] [Module ℂ V] (η : H →* ℂˣ) (a : ℕ)
    (ρ : Representation ℂ H V) (x : H) :
    LinearMap.trace ℂ V (twist η a ρ x) = LinearMap.trace ℂ V (ρ x) * (η x : ℂ) ^ a := by
  show LinearMap.trace ℂ V (((η x : ℂ) ^ a) • ρ x) = _
  rw [map_smul, smul_eq_mul, mul_comm]

theorem sum_trace_mul_star_nat {H V W : Type} [Group H] [Fintype H] [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (ρ : Representation ℂ H V) (σ : Representation ℂ H W) :
    ∃ k : ℕ, ∑ x, LinearMap.trace ℂ V (ρ x) * star (LinearMap.trace ℂ W (σ x)) = (Nat.card H : ℂ) * k := by
  have hne : (Nat.card H : ℂ) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
  haveI : Invertible (Nat.card H : ℂ) := invertibleOfNonzero hne
  have h := FDRep.scalar_product_char_eq_finrank_equivariant (FDRep.of σ) (FDRep.of ρ)
  refine ⟨Module.finrank ℂ (FDRep.of σ ⟶ FDRep.of ρ), ?_⟩
  rw [← h, mul_inv_cancel_left₀ hne]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [GlobalTheory.BadShare.ZCalc.character_inv]
  rfl

end GlobalTheory.Shin.CosetOrth

open GlobalTheory.Shin.CosetOrth in
theorem GlobalTheory.Shin.finsum_coset_mul_star_eq_zero : ∀ (G Γ : Type) [Group G] [Finite G] [Group Γ] [Fintype Γ] (φ : Γ →* MulAut G) (s : Γ), (Nat.card Γ).Prime → s ≠ 1 → ∀ X Y : G ⋊[φ] Γ → ℂ, IsChar ℂ ℂ X → IsChar ℂ ℂ Y → ∑ᶠ g, X (inl g) * star (Y (inl g)) = 0 → ∑ᶠ g, X (inl g * inr s) * star (Y (inl g * inr s)) = 0 := by
  intro G Γ _ _ _ _ φ s hp hs X Y hX hY h0
  haveI : Fact (Nat.card Γ).Prime := ⟨hp⟩
  have gen : ∀ t : Γ, t ∈ Subgroup.zpowers s := by
    intro t; rw [zpowers_eq_top_of_prime_card rfl hs]; trivial
  have hl0 : Nat.card Γ ≠ 0 := hp.ne_zero
  obtain ⟨η, -, -, hF⟩ := GlobalTheory.Shin.CosetFourier.fourier_coset_sums G Γ φ s gen _ (Complex.isPrimitiveRoot_exp _ hl0)
  obtain ⟨e1, e2⟩ := hF X Y
  haveI : Finite (G ⋊[φ] Γ) := Finite.of_equiv _ SemidirectProduct.equivProd.symm
  letI : Fintype (G ⋊[φ] Γ) := Fintype.ofFinite _
  have hm : ∀ a : ℕ, ∃ k : ℕ, ∑ᶠ x, X x * star (Y x * (η x : ℂ) ^ a) = (Nat.card (G ⋊[φ] Γ) : ℂ) * k := by
    intro a
    obtain ⟨n, ρ, hρ⟩ := hX
    obtain ⟨m, σ, hσ⟩ := hY
    obtain ⟨k, hk⟩ := sum_trace_mul_star_nat ρ (twist η a σ)
    refine ⟨k, ?_⟩
    rw [finsum_eq_sum_of_fintype, ← hk]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [trace_twist, hρ x, hσ x]
    rfl
  choose k hk using hm
  have hH : (Nat.card (G ⋊[φ] Γ) : ℂ) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
  have hsum : ∑ a ∈ Finset.range (Nat.card Γ), k a = 0 := by
    rw [h0, mul_zero] at e1
    simp_rw [hk] at e1
    rw [← Finset.mul_sum] at e1
    have := (mul_eq_zero.mp e1.symm).resolve_left hH
    exact_mod_cast this
  have hk0 : ∀ a ∈ Finset.range (Nat.card Γ), k a = 0 := Finset.sum_eq_zero_iff.mp hsum
  have hR : ∑ a ∈ Finset.range (Nat.card Γ), Complex.exp (2 * ↑Real.pi * Complex.I / ↑(Nat.card Γ)) ^ a *
      ∑ᶠ x, X x * star (Y x * (η x : ℂ) ^ a) = 0 := by
    refine Finset.sum_eq_zero fun a ha => ?_
    rw [hk a, hk0 a ha]; simp
  rw [hR] at e2
  exact (mul_eq_zero.mp e2).resolve_left (by exact_mod_cast hl0)
end

section

noncomputable section

open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex

namespace GlobalTheory.SympQ

variable {O : Type} [CommRing O] (N : NumD O)

def trivHom (k : ℕ) : Multiplicative N.X →* N.QT k where
  toFun z := N.qTriv k z.toAdd
  map_one' := Subtype.ext (Prod.ext (by simp [NumD.qTriv]) (by simp [NumD.qTriv, N.io_zero]))
  map_mul' a b := Subtype.ext (Prod.ext (by simp [NumD.qTriv, smul_add]) (by simp [NumD.qTriv, N.io_add]))

abbrev Qq (k : ℕ) : Type := N.QT k ⧸ (trivHom N k).range

theorem qEq_iff_mk_eq {k : ℕ} (p p' : N.QT k) : N.QEq p p' ↔ (QuotientGroup.mk p : Qq N k) = QuotientGroup.mk p' := by
  rw [N.qEq_iff, QuotientGroup.eq]
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨Multiplicative.ofAdd z, by simp [trivHom]⟩
  · rintro ⟨z, hz⟩
    refine ⟨z.toAdd, ?_⟩
    change N.qTriv k z.toAdd = p⁻¹ * p' at hz
    rw [hz, mul_inv_cancel_left]

def pushRep (M n : ℕ) : N.QT M →* N.QT n :=
  if h : n ∣ M then
    { toFun := fun p => ⟨(p.1.1, p.1.2 ^ (M / n)), by
        rw [NumD.mem_QT, ← pow_mul, Nat.div_mul_cancel h]
        exact p.2⟩
      map_one' := Subtype.ext (Prod.ext rfl (by simp))
      map_mul' := fun p q => Subtype.ext (Prod.ext rfl (by simp [mul_pow])) }
  else 1

theorem pushRep_fst {M n : ℕ} (h : n ∣ M) (p : N.QT M) : (pushRep N M n p).1.1 = p.1.1 := by
  simp [pushRep, h]

theorem pushRep_snd {M n : ℕ} (h : n ∣ M) (p : N.QT M) : (pushRep N M n p).1.2 = p.1.2 ^ (M / n) := by
  simp [pushRep, h]

theorem pushRep_triv (M n : ℕ) : (trivHom N M).range ≤ (trivHom N n).range.comap (pushRep N M n) := by
  rintro _ ⟨z, rfl⟩
  by_cases h : n ∣ M
  · refine ⟨Multiplicative.ofAdd ((M / n) • z.toAdd), Subtype.ext (Prod.ext ?_ ?_)⟩
    · simp only [trivHom, MonoidHom.coe_mk, OneHom.coe_mk, NumD.qTriv, toAdd_ofAdd]
      rw [pushRep_fst N h, smul_smul, Nat.mul_div_cancel' h]
    · simp only [trivHom, MonoidHom.coe_mk, OneHom.coe_mk, NumD.qTriv, toAdd_ofAdd]
      rw [pushRep_snd N h, N.io_nsmul]
  · simp [pushRep, h]

def pushQ (M n : ℕ) : Qq N M →* Qq N n := QuotientGroup.map _ _ (pushRep N M n) (pushRep_triv N M n)

theorem pushQ_mk (M n : ℕ) (p : N.QT M) :
    pushQ N M n (QuotientGroup.mk p) = QuotientGroup.mk (pushRep N M n p) := rfl

theorem wp_qTriv_right {k : ℕ} (p : N.QT k) (z : N.X) : N.wp p (N.qTriv k z) = 1 := by
  rw [← inv_inj, ← NumD.wp_swap, WpPairing.wp_qTriv, inv_one]

theorem wp_congr {k : ℕ} {p p' q q' : N.QT k} (hp : N.QEq p p') (hq : N.QEq q q') : N.wp p q = N.wp p' q' := by
  obtain ⟨z, rfl⟩ := (N.qEq_iff _ _).1 hp
  obtain ⟨w, rfl⟩ := (N.qEq_iff _ _).1 hq
  rw [WpPairing.wp_mul_left, WpPairing.wp_mul_right, WpPairing.wp_mul_right, WpPairing.wp_qTriv,
    WpPairing.wp_qTriv, wp_qTriv_right]
  simp

def wpQ (k : ℕ) (x y : Qq N k) : Oˣ :=
  Quotient.liftOn₂' x y (fun p q => N.wp p q) fun p q p' q' hp hq =>
    wp_congr N ((qEq_iff_mk_eq N _ _).2 (Quotient.sound' hp)) ((qEq_iff_mk_eq N _ _).2 (Quotient.sound' hq))

theorem wpQ_mk (k : ℕ) (p q : N.QT k) : wpQ N k (QuotientGroup.mk p) (QuotientGroup.mk q) = N.wp p q := rfl

end GlobalTheory.SympQ
end
end

section

open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef


theorem _root_.GlobalTheory.T.admissibleAdelicMatrixFamily_orders_finite : ∀ (k F : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field F] [Algebra k F], IsFF k F →
  ∀ (n : ℕ) (g : Place k F → Matrix (Fin n) (Fin n) F), admitted g → {v : Place k F | ord v (g v).det ≠ 0}.Finite ∧ ∀ w : Fin n → F, w ≠ 0 → {v : Place k F | nrm v ((g v).mulVec w) ≠ 1}.Finite ∧ ∀ v, (g v).mulVec w ≠ 0 := by
  first | exact @GlobalTheory.Nef.lineFin | exact GlobalTheory.Nef.lineFin | (intros; apply GlobalTheory.Nef.lineFin <;> assumption)
end

section

open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef


theorem _root_.GlobalTheory.T.isRational_powerSeries_of_adelicIntegral_positiveRadius : ∀ (k F : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field F] [Algebra k F], IsFF k F →
  ∀ (φ : PowerSeries F) (u : Place k F → F) (e ψ : ∀ v : Place k F, PowerSeries v.O), (∀ v, u v ≠ 0) → {v | ord v (u v) ≠ 0}.Finite → 0 < ∑ᶠ v, ord v (u v) → (∀ v, PowerSeries.constantCoeff (e v) ≠ 0) → {v | ¬ IsUnit (PowerSeries.constantCoeff (e v))}.Finite → (∀ v, sc v (u v) (e v) * φ = sc v (u v) (ψ v)) → IsRat φ := by
  first | exact @GlobalTheory.RatCrit.isRat_of_adelic | exact GlobalTheory.RatCrit.isRat_of_adelic | (intros; apply GlobalTheory.RatCrit.isRat_of_adelic <;> assumption)
end

section

open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef


theorem _root_.GlobalTheory.T.riemann_inequality_cofinal_functionField : ∀ (k F : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field F] [Algebra k F], IsFF k F →
  ∃ γ : ℕ, ∀ D : Place k F →₀ ℤ, ∃ D' : Place k F →₀ ℤ, D ≤ D' ∧ ∃ (n : ℕ) (f : Fin n → F), LinearIndependent k f ∧ (D'.sum fun _ m => m) - γ ≤ n ∧ ∀ (i : Fin n) (v : Place k F), -D' v ≤ ord v (f i) := by
  first | exact @GlobalTheory.Nef.riemann_cofinal | exact GlobalTheory.Nef.riemann_cofinal | (intros; apply GlobalTheory.Nef.riemann_cofinal <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

theorem _root_.GlobalTheory.T.tateTwist_isFreeRankOne_on_generatorSection : ∀ (q : ℕ) (i : ℤ) (S : Scheme.{0}) (ζ : Prim q Γ(S, ⊤)), Gen (tw q i) S (twGen i ζ) := by
  first | (exact @GlobalTheory.twGen_gen) | (exact GlobalTheory.twGen_gen) | (intros; apply GlobalTheory.twGen_gen  <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem tw_finitary : ∀ (q : ℕ) (i : ℤ), Finitary (tw q i) := fun q i =>
  GlobalTheory.T.etaleSheafOfRingFunctor_isFinitary (ZMod q) (twF q i) (GlobalTheory.EtC.TwistFiltered.twF_preservesFilteredColimits q i)

end GlobalTheory.EtC
end

section

open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

theorem GlobalTheory.holo_etale_iff_charts : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (U : Set Y) (z : Y → V n), Etale A U z → ∀ u : Y → ℂ, (Holo n (fun y : U => z y) (fun y : U => u y) ↔ ∀ i, DifferentiableOn ℂ (u ∘ (A.chart i).symm) ((A.chart i).target ∩ (A.chart i).symm ⁻¹' U)) := by
  intro n Y _ _ _ _ _ ι La _ A U z hz u
  have h := GlobalTheory.T.etale_holomorphic_iff_chart_holomorphic n Y ι La A U z hz Set.univ u isOpen_univ
  simp only [Set.preimage_univ, Set.inter_univ] at h
  exact h
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

theorem _root_.GlobalTheory.T.isCohomologyContinuousOnCone_of_levelwise : ∀ (R : Type) [CommRing R] (F : Shv R) (I : Type) [SmallCategory I] [IsCofiltered I] (G : I ⥤ Spc) (c : Cone G), (∀ k : SimplexCategoryᵒᵖ, ContCone R F (((evaluation _ PSh).obj k ⋙ disc).mapCone c)) → ContCone R F c := by
  first | (exact @GlobalTheory.EtC.contCone_of_levelwise) | (exact GlobalTheory.EtC.contCone_of_levelwise) | (intros; apply GlobalTheory.EtC.contCone_of_levelwise <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

theorem _root_.GlobalTheory.T.cohomology_filteredColimit_of_etaleDescent : ∀ (M : CommRingCat.{0} ⥤ AbCx) (F0 : CommRingCat.{0} ⥤ AddCommGrpCat.{1}) (ι : F0 ⟶ term M 0), PreservesFilteredColimitsOfSize.{0, 0} F0 → (∀ A, Function.Injective (ι.app A) ∧ ∀ z : (M.obj A).X 0, (M.obj A).d 0 (0 + 1) z = 0 ↔ ∃ x, ι.app A x = z) → (∀ n : ℤ, n < 0 → ∀ A, IsZero ((M.obj A).X n)) → (∀ n : ℤ, 0 < n → ∀ (A : CommRingCat.{0}) (z : (M.obj A).X n), (M.obj A).d n (n + 1) z = 0 → ∃ (B : CommRingCat.{0}) (g : A ⟶ B), EtFF g ∧ ∃ y : (M.obj B).X (n - 1), (M.obj B).d (n - 1) n y = (M.map g).f n z) → (∀ (A B : CommRingCat.{0}) (g : A ⟶ B), EtFF g → ∀ n, WExact (term M n) (coAug g)) → (∀ (J : Type) [SmallCategory J] [IsFiltered J] (D : J ⥤ CommRingCat.{0}) (c : Cocone D), IsColimit c → ∀ n : ℤ, (∀ z : ((M).obj c.pt).X n, ((M).obj c.pt).d n (n + 1) z = 0 → ∃ (j : J) (w : ((M).obj (D.obj j)).X n) (y : ((M).obj c.pt).X (n - 1)), ((M).obj (D.obj j)).d n (n + 1) w = 0 ∧ ((M).map (c.ι.app j)).f n w = z + ((M).obj c.pt).d (n - 1) n y) ∧ ∀ (j : J) (w : ((M).obj (D.obj j)).X n), ((M).obj (D.obj j)).d n (n + 1) w = 0 → (∃ y : ((M).obj c.pt).X (n - 1), ((M).map (c.ι.app j)).f n w = ((M).obj c.pt).d (n - 1) n y) → ∃ (k : J) (f : j ⟶ k) (y : ((M).obj (D.obj k)).X (n - 1)), ((M).map (D.map f)).f n w = ((M).obj (D.obj k)).d (n - 1) n y) := by
  first
  | exact @GlobalTheory.EtC.ContAlg.cohomology_filteredColimit_of_descent
  | exact GlobalTheory.EtC.ContAlg.cohomology_filteredColimit_of_descent
  | (intros; apply GlobalTheory.EtC.ContAlg.cohomology_filteredColimit_of_descent <;> assumption)
end
