module

public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle007
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle005
public import Mathlib.GroupTheory.Nilpotent
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle008
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle001
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle003
public import Mathlib.Analysis.Calculus.FDeriv.Const

@[expose] public section

section

noncomputable section

namespace GlobalTheory.LambdaValuationPowers

variable {K : Type*} [Field K] [CharZero K]

def chiProj (N p m k : ℕ) [NeZero N] (ψ : DirichletCharacter K (p ^ m)) (χ : ℕ → K) (c d x : ℤ) (s : ℕ) : K :=
  ∑ δ : (ZMod N)ˣ, χ (δ : ZMod N).val * coPtSb N p m k ψ c d (x * ((δ : ZMod N).val : ℤ)) ((δ : ZMod N).val : ℤ) s

end GlobalTheory.LambdaValuationPowers
end
end

section

noncomputable section

open scoped MatrixGroups

namespace GlobalTheory.Glue

open GlobalTheory.KZ GlobalTheory.K5

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

def zt (ε : Ω →+* ℂ) (l n : ℕ) : Ω := eOm ε (1 / (l : ℚ) ^ n)

def Stab (A : ValuationSubring Ω) (s : Ω ≃ₐ[ℚ] Ω) : Prop := ∀ x, s x ∈ A ↔ x ∈ A

def InZl (ε : Ω →+* ℂ) (l n : ℕ) (F : Ω) : Prop := ∃ D : ℕ, ¬ l ∣ D ∧ (D : Ω) * F ∈ Subring.closure {zt ε l n}


open Classical in
def IsNT (ε : Ω →+* ℂ) (l n m : ℕ) [NeZero l] (F F' : Ω) : Prop :=
  ∃ τ : (ZMod (l ^ n))ˣ → (Ω ≃ₐ[ℚ] Ω), (∀ a, τ a (zt ε l n) = zt ε l n ^ (a : ZMod (l ^ n)).val) ∧
    (l : Ω) ^ (n - m) * F' = ∑ a ∈ Finset.univ.filter (fun a : (ZMod (l ^ n))ˣ => (a : ZMod (l ^ n)).val ≡ 1 [MOD l ^ m]), τ a F

def KT (X : GlobalTheory.KZ.Tower Ω ε) (L : ℕ) : Subfield X.K :=
  RingHom.eqLocusField (X.sl (ofSL (ModularGroup.T ^ L))).toRingEquiv.toRingHom (RingHom.id X.K)

variable {p : ℕ} [Fact p.Prime] {Ωl : Type} [Field Ωl] [Algebra (O0 p) Ωl]

structure IsCusp (ε : Ω →+* ℂ) (A : ValuationSubring Ω) (T : GlobalTheory.K5.Tower p Ωl) (j : Ω →+* Ωl) : Prop where
  int : ∀ x, x ∈ A ↔ IsInt (p := p) (j x)
  alg : ∀ x, IsAlgZp (p := p) (j x)
  root : ∀ n, j (zt ε p n) = T.ζ n
  dense : ∀ (k : ℕ) (e : Ωl), IsInt (p := p) e → IsAlgZp (p := p) e → ∃ a ∈ A, Cong (p := p) k e (j a)
  down : ∀ g : Gal p Ωl, ∃ s : Ω ≃ₐ[ℚ] Ω, Stab A s ∧ ∀ x, g (j x) = j (s x)
  up : ∀ (n : ℕ) (s : Ω ≃ₐ[ℚ] Ω), Stab A s → ∃ g : Gal p Ωl, g (T.qq n) = T.qq n ∧ ∀ x, g (j x) = j (s x)

structure IsIo (X : GlobalTheory.KZ.Tower Ω ε) (A : ValuationSubring Ω) (T : GlobalTheory.K5.Tower p Ωl) (j : Ω →+* Ωl) (n : ℕ)
    (ψ : O0 p →+* Ωl) (io : KT X (p ^ n) →+* Ωl) : Prop where
  ev : ∀ (y : KT X (p ^ n)) (S : Finset Ω),
    (∀ r, (X.exp y).coeff r ∈ A ∧ (X.exp y).coeff r ∈ IntermediateField.adjoin ℚ (S : Set Ω)) →
    ∃ x', GlobalTheory.Glue.Ev ψ (fun r : ℤ => j ((X.exp y).coeff ((r : ℚ) / (p : ℚ) ^ n))) (io y) x'
  gal : ∀ (g : Gal p Ωl) (s : Ω ≃ₐ[ℚ] Ω), g (T.qq n) = T.qq n → (∀ x, g (j x) = j (s x)) →
    ∀ y y' : KT X (p ^ n), (y' : X.K) = X.gal s y → g (io y) = io y'

def IsNTr (ε : Ω →+* ℂ) (l n m : ℕ) [NeZero l] (F F' : Ω) : Prop :=
  1 ≤ m ∧ m ≤ n ∧ F ∈ IntermediateField.adjoin ℚ {zt ε l n} ∧ IsNT ε l n m F F'

theorem InZl.mem_adjoin {l n : ℕ} {F : Ω} (h : InZl ε l n F) : F ∈ IntermediateField.adjoin ℚ {zt ε l n} := by
  haveI : CharZero Ω := algebraRat.charZero Ω
  obtain ⟨D, hD, hF⟩ := h
  have hD0 : (D : Ω) ≠ 0 := by
    rintro h0
    exact hD (by rw [Nat.cast_eq_zero.1 h0]; exact dvd_zero _)
  have h1 : (D : Ω) * F ∈ IntermediateField.adjoin ℚ {zt ε l n} :=
    (Subring.closure_le (t := (IntermediateField.adjoin ℚ {zt ε l n}).toSubring)).2
      (IntermediateField.subset_adjoin ℚ _) hF
  have h2 := mul_mem (inv_mem (natCast_mem (IntermediateField.adjoin ℚ {zt ε l n}) D)) h1
  rwa [inv_mul_cancel_left₀ hD0] at h2

theorem IsNTr.apply_eq_of_mem_adjoin {z F : Ω} (hF : F ∈ IntermediateField.adjoin ℚ {z}) {s t : Ω ≃ₐ[ℚ] Ω} (h : s z = t z) :
    s F = t F := by
  induction hF using IntermediateField.adjoin_induction with
  | mem x hx => rw [Set.mem_singleton_iff.1 hx, h]
  | algebraMap r => rw [AlgEquiv.commutes, AlgEquiv.commutes]
  | add x y _ _ hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]
  | inv x _ hx => rw [map_inv₀, map_inv₀, hx]
  | mul x y _ _ hx hy => rw [map_mul, map_mul, hx, hy]

theorem IsNTr.add {l n m : ℕ} [NeZero l] {F F' G G' : Ω} (h : IsNTr ε l n m F F') (h' : IsNTr ε l n m G G') :
    IsNTr ε l n m (F + G) (F' + G') := by
  obtain ⟨h1, h2, hF, τ, hτ, e⟩ := h
  obtain ⟨-, -, hG, τ', hτ', e'⟩ := h'
  refine ⟨h1, h2, add_mem hF hG, τ, hτ, ?_⟩
  rw [mul_add, e, e', ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun a _ => by
    rw [map_add (f := _), IsNTr.apply_eq_of_mem_adjoin hG ((hτ a).trans (hτ' a).symm)]

theorem KT.mem_def (X : GlobalTheory.KZ.Tower Ω ε) (L : ℕ) (f : X.K) : f ∈ KT X L ↔ X.sl (ofSL (ModularGroup.T ^ L)) f = f := Iff.rfl

section

variable {X : GlobalTheory.KZ.Tower Ω ε} {A : ValuationSubring Ω} {T : GlobalTheory.K5.Tower p Ωl} {j : Ω →+* Ωl} {n : ℕ} {ψ : O0 p →+* Ωl}
  {io : KT X (p ^ n) →+* Ωl}

end

end GlobalTheory.Glue
end
end

section

noncomputable section

open scoped MatrixGroups TensorProduct
open Matrix

namespace GlobalTheory.ZetaB

open GlobalTheory.KZ GlobalTheory.K4 GlobalTheory.NeedB GlobalTheory.KEdge

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

def tInv (l N R : ℕ) : ZMod N := ((l : ZMod N) ^ R)⁻¹

def uIdxMu (l N R : ℕ) (x : ZMod N) : Fin 2 → ℚ := ![1 / (l : ℚ) ^ R + ((x * tInv l N R).val : ℚ) / N, 0]

def vIdxMu (l N R : ℕ) : Fin 2 → ℚ := ![((tInv l N R).val : ℚ) / N, 1 / (l : ℚ) ^ R]

abbrev Om (X : Tower Ω ε) : Type := AlgebraicClosure X.K

attribute [local instance] algMdl

theorem isScalarTower_mdl_om (X : Tower Ω ε) (Γ' : Subgroup SL(2, ℤ)) (S : Subgroup (Ω ≃ₐ[ℚ] Ω)) :
    @IsScalarTower (mdl X Γ' S) (lev X Γ') (Om X) Algebra.toSMul Algebra.toSMul Algebra.toSMul :=
  IsScalarTower.of_algebraMap_eq (fun _ => rfl)

attribute [local instance] isScalarTower_mdl_om





open Classical in
def unitOf (X : Tower Ω ε) (a : X.K) : X.Kˣ :=
  letI := Classical.propDecidable (a = 0)
  if h : a = 0 then 1 else Units.mk0 a h

def clsHat (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (a : X.K) : X.Khat l :=
  AdicCompletion.of (idl l) (X.Kl l) ((1 : ℤ_[l]) ⊗ₜ Additive.ofMul (unitOf X a))

def cR (l N : ℕ) (r₀ : ZMod l) : ℤ := (N : ℤ) * ((-r₀ * (N : ZMod l)⁻¹).val : ℤ)

def gR (l N : ℕ) (r₀ : ZMod l) : SL(2, ℤ) :=
  ⟨!![1, 0; cR l N r₀, 1], by simp [Matrix.det_fin_two]⟩



theorem cR_mod (l N : ℕ) [Fact l.Prime] (hN : (N : ZMod l) ≠ 0) (r₀ : ZMod l) : ((cR l N r₀ : ℤ) : ZMod l) = -r₀ := by
  simp only [cR, Int.cast_mul, Int.cast_natCast, ZMod.natCast_zmod_val]
  rw [mul_comm (-r₀), ← mul_assoc, mul_inv_cancel₀ hN, one_mul]


open scoped MatrixGroups TensorProduct in
open Matrix in
variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} in
attribute [local instance] _root_.GlobalTheory.K4.algMdl in
theorem _root_.GlobalTheory.ZetaB.eval_clsHat (X : _root_.GlobalTheory.KZ.Tower Ω ε) (l : ℕ)
    [Fact l.Prime] (n : ℕ) (a : X.K) :
    AdicCompletion.eval (_root_.GlobalTheory.KZ.idl l) (X.Kl l) n
        (_root_.GlobalTheory.ZetaB.clsHat X l a) =
      X.cls l n (_root_.GlobalTheory.ZetaB.unitOf X a) := by
  unfold _root_.GlobalTheory.ZetaB.clsHat
  rw [AdicCompletion.eval_of]
  rfl


open scoped MatrixGroups TensorProduct in
open Matrix in
variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} in
attribute [local instance] _root_.GlobalTheory.K4.algMdl in
theorem _root_.GlobalTheory.ZetaB.unitOf_val (X : _root_.GlobalTheory.KZ.Tower Ω ε) {a : X.K}
    (ha : a ≠ 0) : ((_root_.GlobalTheory.ZetaB.unitOf X a : (X.K)ˣ) : X.K) = a := by
  unfold _root_.GlobalTheory.ZetaB.unitOf
  rw [dite_eq_right ha]
  rfl


open scoped MatrixGroups TensorProduct in
open Matrix in
variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} in
attribute [local instance] _root_.GlobalTheory.K4.algMdl in
theorem _root_.GlobalTheory.ZetaB.unitOf_zero (X : _root_.GlobalTheory.KZ.Tower Ω ε) :
    _root_.GlobalTheory.ZetaB.unitOf X 0 = 1 := by
  unfold _root_.GlobalTheory.ZetaB.unitOf
  rw [dite_eq_left rfl]

end GlobalTheory.ZetaB
end
end

section

noncomputable section

open scoped MatrixGroups TensorProduct
open Matrix

namespace GlobalTheory.KZ.H3

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

def JHol (X : Tower Ω ε) : Prop :=
  ∃ φ : ℂ → ℂ, X.an X.jK = (φ : Mero) ∧ DifferentiableOn ℂ φ Hs

def IsRoot (X : Tower Ω ε) (m : ℕ) (f : X.Kˣ) (a b : ℂ → ℂ) : Prop :=
  DifferentiableOn ℂ a Hs ∧ DifferentiableOn ℂ b Hs ∧ (b : Mero) ≠ 0 ∧
    X.an (f : X.K) * (b : Mero) ^ m = (a : Mero) ^ m

def Kum (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (n : ℕ) (x : X.Khat l) (χ : SL(2, ℤ) → ZMod (l ^ n)) : Prop :=
  ∃ (f : X.Kˣ) (a b : ℂ → ℂ) (M : ℕ), 0 < M ∧ AdicCompletion.eval (idl l) (X.Kl l) n x = X.cls l n f ∧
    IsRoot X (l ^ n) f a b ∧ ∀ δ ∈ CongruenceSubgroup.Gamma M, ∀ z ∈ Hs,
      a (mob (ofSL δ) z) * b z =
        Complex.exp (2 * Real.pi * Complex.I * ((χ δ).val : ℂ) / ((l : ℂ) ^ n)) * (a z * b (mob (ofSL δ) z))

def Near {V : Type} (φ ψ : SL(2, ℤ) → V) : Prop :=
  ∃ M : ℕ, 0 < M ∧ ∀ δ ∈ CongruenceSubgroup.Gamma M, φ δ = ψ δ

def R1 (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (x : X.Khat l) (h : ℂ → ℤ_[l]) : Prop :=
  ∀ n : ℕ, ∃ χ : SL(2, ℤ) → ZMod (l ^ n), Kum X l n x χ ∧ ∃ M : ℕ, 0 < M ∧ ∀ δ ∈ CongruenceSubgroup.Gamma M, ∀ z ∈ Hs,
    PadicInt.toZModPow n (h (mob (ofSL δ) z) - h z) = χ δ

def Rel (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (b : X.Fn l) (F : ℂ → MvPolynomial (Fin 2) ℤ_[l]) : Prop :=
  ∀ u : Fin 2 → ℤ_[l], R1 X l (b u) (fun z => MvPolynomial.eval u (F z))


open scoped Classical in
open Classical in
def cj (m : Matrix (Fin 2) (Fin 2) ℤ) (δ : SL(2, ℤ)) : SL(2, ℤ) :=
  if h : ∃ δ' : SL(2, ℤ), m * (δ : Matrix (Fin 2) (Fin 2) ℤ) = (δ' : Matrix (Fin 2) (Fin 2) ℤ) * m then h.choose else 1

def IsCoc {R : Type} [CommRing R] (w : ℕ) (Γ : Subgroup SL(2, ℤ)) (c : SL(2, ℤ) → MvPolynomial (Fin 2) R) : Prop :=
  (∀ γ ∈ Γ, (c γ).IsHomogeneous w) ∧
    ∀ γ ∈ Γ, ∀ δ ∈ Γ, c (γ * δ) = slP (δ : Matrix (Fin 2) (Fin 2) ℤ) (c γ) + c δ

def IsFam (l w : ℕ) (Γ : Subgroup SL(2, ℤ)) (Φ : (n : ℕ) → SL(2, ℤ) → MvPolynomial (Fin 2) (ZMod (l ^ n))) : Prop :=
  (∀ n δ, (Φ n δ).IsHomogeneous w) ∧
  (∀ n, ∃ M : ℕ, 0 < M ∧ ∀ δ ∈ CongruenceSubgroup.Gamma M, ∀ δ' ∈ CongruenceSubgroup.Gamma M,
    Φ n (δ * δ') = Φ n δ + Φ n δ') ∧
  (∀ n, ∀ γ ∈ Γ, Near (fun δ => slP (γ : Matrix (Fin 2) (Fin 2) ℤ) (Φ n (γ * δ * γ⁻¹))) (Φ n)) ∧
  ∀ n, Near (fun δ => MvPolynomial.map (ZMod.castHom (pow_dvd_pow l (Nat.le_succ n)) (ZMod (l ^ n))) (Φ (n + 1) δ)) (Φ n)

def mon (R : Type) [CommRing R] (w : ℕ) (i : Fin (w + 1)) : MvPolynomial (Fin 2) R :=
  MvPolynomial.X 0 ^ (i : ℕ) * MvPolynomial.X 1 ^ (w - (i : ℕ))

def cf (w : ℕ) (m : Matrix (Fin 2) (Fin 2) ℤ) (i k : Fin (w + 1)) : ℤ :=
  AddMonoidAlgebra.coeff (slP m (mon ℤ w k)) (Finsupp.single 0 (i : ℕ) + Finsupp.single 1 (w - (i : ℕ)))

def SSBS (S : Letter → Prop) (X : Tower Ω ε) (N l w : ℕ) [Fact l.Prime] (E : Type) [Field E] [Algebra ℤ_[l] E]
    (lam : Letter → E) : Prop :=
  ∃ P ∈ Algebra.adjoin E (FreeAlgebra.ι E '' {T | S T}), FreeAlgebra.lift E lam P = 1 ∧ ∀ x ∈ X.VB N l w E, ∀ T : Letter, S T →
    (X.opV N l E T - lam T • (1 : Module.End E (E ⊗[ℤ_[l]] X.Fn l))) (FreeAlgebra.lift E (X.opV N l E) P x) = 0

def abelian₂ (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (E : Type) [Field E] [Algebra ℤ_[l] E] :
    Submodule E ((E ⊗[ℤ_[l]] X.Fn l) × (ℂ → MvPolynomial (Fin 2) E)) :=
  Submodule.span E {p | ∃ b F, Rel X l b F ∧
    p = ((1 : E) ⊗ₜ[ℤ_[l]] b, fun z => MvPolynomial.map (algebraMap ℤ_[l] E) (F z))}

def deh : MvPolynomial (Fin 2) ℂ →ₐ[ℂ] Polynomial ℂ := MvPolynomial.aeval ![Polynomial.X, 1]

def cocP (Γ : Subgroup SL(2, ℤ)) (F : ℂ → MvPolynomial (Fin 2) ℂ) : Γ → Polynomial ℂ := fun γ =>
  deh (slP ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) (F (mob (ofSL γ) Complex.I)) - F Complex.I)

theorem isRoot_one (X : Tower Ω ε) (m : ℕ) (h : ((fun _ => 1 : ℂ → ℂ) : Mero) ≠ 0) :
    IsRoot X m 1 (fun _ => 1) (fun _ => 1) :=
  ⟨differentiableOn_const 1, differentiableOn_const 1, h, by simp⟩

end GlobalTheory.KZ.H3
end
end

section

noncomputable section

open scoped MatrixGroups TensorProduct
open Matrix

namespace GlobalTheory.KZ

def SSPotA (N l w : ℕ) (lam : Letter → ℂ) : Prop :=
  ∃ P ∈ Algebra.adjoin ℂ (FreeAlgebra.ι ℂ '' {T : Letter | admitted N l T}),
    FreeAlgebra.lift ℂ lam P = 1 ∧ ∀ F ∈ Pot ℂ w (Gam N l), ∀ T : Letter, admitted N l T →
    (opL ℂ N l T - lam T • (1 : Module.End ℂ (ℂ → MvPolynomial (Fin 2) ℂ)))
      (FreeAlgebra.lift ℂ (opL ℂ N l) P F) ∈ Triv ℂ w (Gam N l)

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

namespace SSAdm

variable {R : Type} [CommRing R] {A : Set Letter}

theorem lift_congr {B : Type} [Semiring B] [Algebra R B] {f g : Letter → B} (h : ∀ T ∈ A, f T = g T)
    {P : FreeAlgebra R Letter} (hP : P ∈ Algebra.adjoin R (FreeAlgebra.ι R '' A)) :
    FreeAlgebra.lift R f P = FreeAlgebra.lift R g P := by
  induction hP using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨T, hT, rfl⟩ := hx
    simp [h T hT]
  | algebraMap r => simp
  | add x y _ _ hx hy => simp [hx, hy]
  | mul x y _ _ hx hy => simp [hx, hy]

variable {M : Type} [AddCommGroup M] [Module R M]


open scoped MatrixGroups TensorProduct in
open Matrix in
variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} in
variable {R : Type} [CommRing R] {A : Set _root_.GlobalTheory.KZ.Letter} in
variable {M : Type} [AddCommGroup M] [Module R M] in
theorem _root_.GlobalTheory.KZ.SSAdm.lift_sub_smul_mem {f : _root_.GlobalTheory.KZ.Letter → Module.End R M}
    {lam : _root_.GlobalTheory.KZ.Letter → R} {W : Submodule R M}
    (hW : ∀ T ∈ A, ∀ x ∈ W, f T x ∈ W) {x : M} (hx : ∀ T ∈ A, f T x - lam T • x ∈ W)
    {P : FreeAlgebra R _root_.GlobalTheory.KZ.Letter} (hP : P ∈ Algebra.adjoin R (FreeAlgebra.ι R '' A)) :
    FreeAlgebra.lift R f P x - FreeAlgebra.lift R lam P • x ∈ W := by
  have key : ∀ P ∈ Algebra.adjoin R (FreeAlgebra.ι R '' A),
      (∀ y ∈ W, FreeAlgebra.lift R f P y ∈ W) ∧
        FreeAlgebra.lift R f P x - FreeAlgebra.lift R lam P • x ∈ W := by
    intro P hP
    induction hP using Algebra.adjoin_induction with
    | mem P hP =>
      obtain ⟨T, hT, rfl⟩ := hP
      simp only [FreeAlgebra.lift_ι_apply]
      exact ⟨hW T hT, hx T hT⟩
    | algebraMap r =>
      simp only [AlgHom.commutes, Module.algebraMap_end_apply, Algebra.algebraMap_self,
        RingHom.id_apply, sub_self]
      exact ⟨fun y hy => W.smul_mem r hy, W.zero_mem⟩
    | add P Q _ _ hP hQ =>
      refine ⟨fun y hy => ?_, ?_⟩
      · rw [map_add (f := _), LinearMap.add_apply]
        exact W.add_mem (hP.1 y hy) (hQ.1 y hy)
      · convert W.add_mem hP.2 hQ.2 using 1
        simp only [map_add (f := _), LinearMap.add_apply, add_smul]
        abel
    | mul P Q _ _ hP hQ =>
      refine ⟨fun y hy => ?_, ?_⟩
      · rw [map_mul, Module.End.mul_apply]
        exact hP.1 _ (hQ.1 y hy)
      · convert W.add_mem (hP.1 _ hQ.2) (W.smul_mem (FreeAlgebra.lift R lam Q) hP.2) using 1
        simp only [map_mul, Module.End.mul_apply, map_sub, LinearMap.map_smul, smul_sub,
          smul_smul]
        rw [mul_comm (FreeAlgebra.lift R lam Q)]
        abel
  exact (key P hP).2

theorem eigen_of_two_step {f : Letter → Module.End R M} {lam : Letter → R} {Z : Submodule R M}
    (hZ : ∀ T ∈ A, ∀ z ∈ Z, f T z ∈ Z) {P : FreeAlgebra R Letter}
    (hP : P ∈ Algebra.adjoin R (FreeAlgebra.ι R '' A)) (h1 : FreeAlgebra.lift R lam P = 1) {x : M}
    (hPx : ∀ T ∈ A, (f T - lam T • (1 : Module.End R M)) (FreeAlgebra.lift R f P x) ∈ Z)
    (hx : ∀ S ∈ A, ∀ T ∈ A,
      (f S - lam S • (1 : Module.End R M)) ((f T - lam T • (1 : Module.End R M)) x) ∈ Z) :
    ∀ T ∈ A, (f T - lam T • (1 : Module.End R M)) x ∈ Z := by
  let W : Submodule R M := ⨅ T ∈ A, Z.comap (f T - lam T • (1 : Module.End R M))
  have hmem : ∀ y, y ∈ W ↔ ∀ T ∈ A, (f T - lam T • (1 : Module.End R M)) y ∈ Z := by
    intro y; simp only [W, Submodule.mem_iInf, Submodule.mem_comap]
  have hZW : ∀ z ∈ Z, z ∈ W := fun z hz => (hmem z).2 fun T hT => by
    simpa using Z.sub_mem (hZ T hT z hz) (Z.smul_mem _ hz)
  have hW : ∀ T ∈ A, ∀ y ∈ W, f T y ∈ W := fun T hT y hy => by
    have h := W.add_mem (hZW _ ((hmem y).1 hy T hT)) (W.smul_mem (lam T) hy)
    simpa using h
  have hx' : ∀ T ∈ A, f T x - lam T • x ∈ W := fun T hT => (hmem _).2 fun S hS => by
    simpa using hx S hS T hT
  have h2 := lift_sub_smul_mem hW hx' hP
  rw [h1, one_smul] at h2
  have h3 := W.sub_mem ((hmem _).2 hPx) h2
  rw [sub_sub_cancel] at h3
  exact (hmem x).1 h3

end SSAdm

theorem SSPotA_congr {N l w : ℕ} {lam lam' : Letter → ℂ} (h : ∀ T, admitted N l T → lam T = lam' T) :
    SSPotA N l w lam ↔ SSPotA N l w lam' := by
  have key : ∀ {a b : Letter → ℂ}, (∀ T, admitted N l T → a T = b T) → SSPotA N l w a → SSPotA N l w b := by
    rintro a b hab ⟨P, hP, h1, h2⟩
    refine ⟨P, hP, ?_, fun F hF T hT => ?_⟩
    · rw [← SSAdm.lift_congr (A := {T | admitted N l T}) hab hP, h1]
    · rw [← hab T hT]; exact h2 F hF T hT
  exact ⟨key h, key fun T hT => (h T hT).symm⟩

end GlobalTheory.KZ
end
end

section

noncomputable section

open scoped MatrixGroups TensorProduct
open Matrix

namespace GlobalTheory.KZ

def admissibleLettersSubalgebra (R : Type) [CommRing R] (N l : ℕ) : Subalgebra R (FreeAlgebra R Letter) :=
  Algebra.adjoin R (FreeAlgebra.ι R '' {T | admitted N l T})

def SSPotB (N l w : ℕ) (lam : Letter → ℂ) : Prop :=
  ∃ P ∈ admissibleLettersSubalgebra ℂ N l, FreeAlgebra.lift ℂ lam P = 1 ∧ ∀ F ∈ Pot ℂ w (Gam N l), ∀ T : Letter, admitted N l T →
    (opL ℂ N l T - lam T • (1 : Module.End ℂ (ℂ → MvPolynomial (Fin 2) ℂ)))
      (FreeAlgebra.lift ℂ (opL ℂ N l) P F) ∈ Triv ℂ w (Gam N l)

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

def Tower.SSBB (X : Tower Ω ε) (N l w : ℕ) [Fact l.Prime] (E : Type) [Field E] [Algebra ℤ_[l] E] (lam : Letter → E) :
    Prop :=
  ∃ P ∈ admissibleLettersSubalgebra E N l, FreeAlgebra.lift E lam P = 1 ∧ ∀ x ∈ X.VB N l w E, ∀ T : Letter, admitted N l T →
    (X.opV N l E T - lam T • (1 : Module.End E (E ⊗[ℤ_[l]] X.Fn l))) (FreeAlgebra.lift E (X.opV N l E) P x) = 0

theorem iota_mem_admissibleSubalgebra (R : Type) [CommRing R] {N l : ℕ} {T : Letter} (hT : admitted N l T) :
    FreeAlgebra.ι R T ∈ admissibleLettersSubalgebra R N l :=
  Algebra.subset_adjoin ⟨T, hT, rfl⟩

end GlobalTheory.KZ
end
end
