module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.HasConductorMulShift
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open MeasureTheory ValuativeRel Matrix IsLocalRing
open scoped Pointwise NNReal ENNReal

noncomputable section
namespace GlobalTheory.IndefiniteRowSideFullHecke.FlagVolumeFiltration
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.LatPair

section Objects
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n n' : Type} {c : ℕ}


variable (k n) in
def flagSub (c i : ℕ) : Submodule 𝒪[k] (n ⊕ Fin c → k) where
  carrier := {y | ∀ l : Fin c, i ≤ l.val → y (Sum.inr l) = 0}
  zero_mem' _ _ := rfl
  add_mem' h h' l hl := by simp [h l hl, h' l hl]
  smul_mem' s y h l hl := by simp [h l hl]

def latStep (L : Submodule 𝒪[k] (n ⊕ Fin c → k)) (i : ℕ) : Submodule 𝒪[k] (n ⊕ Fin c → k) :=
  L ⊓ flagSub k n c i

def interX (L : Submodule 𝒪[k] (n ⊕ Fin c → k)) : Submodule 𝒪[k] (n → k) :=
  L.comap (GlobalTheory.LatPair.inX k n c)

def flagIn (c i : ℕ) (y : n ⊕ Fin i → k) : n ⊕ Fin c → k :=
  Sum.elim (fun r => y (Sum.inl r)) fun l => if h : l.val < i then y (Sum.inr ⟨l.val, h⟩) else 0

variable [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']

def InCoset (L₀ : Submodule 𝒪[k] (n ⊕ Fin c → k)) (h₀ h : GL (n ⊕ Fin c) k) : Prop :=
  ∃ r ∈ R k n c 1, ∃ κ ∈ latStab L₀, h = r * h₀ * κ

variable [MeasurableSpace k] [BorelSpace k]

end Objects

section Statements
variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c : ℕ) (q : Unif k)

def DatumTranslate : Prop :=
  ∀ (μ : kˣ →* ℂˣ) (P : Pair k n') (L'₀ : Submodule 𝒪[k] (n' ⊕ Fin (c + 1) → k)) [L'₀.IsLattice k]
    (L₀ L : Submodule 𝒪[k] (n ⊕ Fin c → k)) [L₀.IsLattice k] (h' : GL (n' ⊕ Fin (c + 1)) k) (h : GL (n ⊕ Fin c) k),
    h' • L'₀ = GlobalTheory.LatPair.gluedS q (c + 1) P.ker P.vec → h • L₀ = L → ∀ x,
      GlobalTheory.LatPair.latInd (GlobalTheory.LatPair.gluedS q (c + 1) P.ker P.vec) L x =
        (((μ (GeneralLinearGroup.det h'))⁻¹ : ℂˣ) : ℂ) * (μ (GeneralLinearGroup.det h) : ℂ) *
          ((nabs k (GeneralLinearGroup.det h') ^ (-((Fintype.card n : ℝ) + c) / 2) : ℝ) : ℂ) *
          ((nabs k (GeneralLinearGroup.det h) ^ (((Fintype.card n' : ℝ) + c + 1) / 2) : ℝ) : ℂ) *
          om μ h' h (GlobalTheory.LatPair.latInd L'₀ L₀) x

def OneOrbit : Prop :=
  (∀ (L₁ L₂ : Submodule 𝒪[k] (n → k)) (f₁ f₂ : n → k), IsGlue L₁ f₁ → IsGlue L₂ f₂ →
    ∃ g : GL n k, g • L₁ = L₂ ∧ g • f₁ - f₂ ∈ L₂) ∧
  ∀ (L₀ : Submodule 𝒪[k] (n ⊕ Fin c → k)) [L₀.IsLattice k] (Q : Pair k n) (h₀ : GL (n ⊕ Fin c) k),
    h₀ • L₀ = GlobalTheory.LatPair.gluedS q c Q.ker Q.vec → ∀ h : GL (n ⊕ Fin c) k,
      (∃ u ∈ N k n c 1, ∃ (L'' : Submodule 𝒪[k] (n → k)) (f'' : n → k), IsGlue L'' f'' ∧
        h • L₀ = u • GlobalTheory.LatPair.gluedS q c L'' f'') ↔ InCoset L₀ h₀ h

variable [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle) (ν : Measure k)


end Statements

section Examples
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : Type} {c : ℕ}

end Examples

end GlobalTheory.IndefiniteRowSideFullHecke.FlagVolumeFiltration
end
end

section

open ValuativeRel Matrix IsLocalRing
open GlobalTheory.LatPair GlobalTheory.SplitWeil

noncomputable section
namespace GlobalTheory.IndefiniteRowSideFullHecke.AdjointOperatorIdentities

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

section Notions
variable {n : Type}

def KeepsFinite (A : Module.End ℂ (Form k n ℂ)) : Prop :=
  ∀ φ : Form k n ℂ, (Function.support φ).Finite → (Function.support (A φ)).Finite

def IsScaledUnitaryOn (W : Submodule ℂ (Form k n ℂ)) (a : ℂ) (A : Module.End ℂ (Form k n ℂ)) : Prop :=
  Set.BijOn A {φ | φ ∈ W ∧ (Function.support φ).Finite} {φ | φ ∈ W ∧ (Function.support φ).Finite} ∧
    ∀ φ ∈ W, ∀ φ' ∈ W, (Function.support φ).Finite → (Function.support φ').Finite →
      cntIp (A φ) (A φ') = a * cntIp φ φ'

def IsUnitStable {V : Type} [AddCommGroup V] [Module 𝓀[k] V] (S : Finset {x : V // x ≠ 0}) : Prop :=
  ∀ (c : 𝓀[k]ˣ) (x y : {x : V // x ≠ 0}), x ∈ S → y.1 = (c : 𝓀[k]) • x.1 → y ∈ S

end Notions


variable (k) in
structure Vanishing (n : Type) [Fintype n] [DecidableEq n] (M : Type) [AddCommGroup M] [Module ℂ M] (ϖ : Unif k) :
    Prop where

  trLat_eq_zero : ∀ φ ∈ Mram k n M, ∀ (L : Submodule 𝒪[k] (n → k)) [L.IsFullLattice k], trLat L φ = 0

  trKer_eq_zero : ∀ φ ∈ Mram k n M, ∀ (L : Submodule 𝒪[k] (n → k)) [L.IsFullLattice k], trKer L φ = 0

  partial_lat : ∀ φ ∈ Mram k n M, ∀ (L : Submodule 𝒪[k] (n → k)) [L.IsFullLattice k]
    (S : Finset {f : Module.Dual 𝓀[k] (Red L) // f ≠ 0}), IsUnitStable (k := k) S → ∑ f ∈ S, φ (ofDual L f) = 0

  partial_ker : ∀ φ ∈ Mram k n M, ∀ (L : Submodule 𝒪[k] (n → k)) [L.IsFullLattice k]
    (S : Finset {x : Red L // x ≠ 0}), IsUnitStable (k := k) S → ∑ x ∈ S, φ (up L ϖ x) = 0

  invariant_eq_zero : ∀ (π : Representation ℂ (GL n k) M) (P : Pair k n) (v : levelVec π P),
    formOf π P v ∈ Mram k n M → ∀ (M' : Type) [AddCommGroup M'] [Module ℂ M'] (θ : M →ₗ[ℂ] M'),
    ((∀ g ∈ latStab P.lat, ∀ w, θ (π g w) = θ w) ∨ (∀ g ∈ latStab P.ker, ∀ w, θ (π g w) = θ w)) → θ v = 0


variable (k) in
structure OperatorIdentities (n : Type) [Fintype n] (M : Type) [AddCommGroup M] [Module ℂ M] (ϖ : Unif k)
    (χ : AddChar 𝓀[k] ℂ) : Prop where

  FFStar_formula : ∀ (φ : Form k n M) (L : Submodule 𝒪[k] (n → k)) [L.IsFullLattice k]
    [Fintype {x : Red L // x ≠ 0}]
    (f : {f : Module.Dual 𝓀[k] (Red L) // f ≠ 0}),
    FFStar ϖ χ φ (ofDual L f) = ∑ x : {x : Red L // x ≠ 0}, χ (-f.1 x.1) • φ (up L ϖ x)

  FFStar_mul_FF : (FFStar ϖ χ * FF ϖ χ : Module.End ℂ (Form k n M)) = ((resCard k : ℂ) ^ Fintype.card n) • 1 - tr

  FF_mul_FFStar : (FF ϖ χ * FFStar ϖ χ : Module.End ℂ (Form k n M)) = ((resCard k : ℂ) ^ Fintype.card n) • 1 - tr'

  FFStar_FF_ram : ∀ φ ∈ Mram k n M, FFStar ϖ χ (FF ϖ χ φ) = ((resCard k : ℂ) ^ Fintype.card n) • φ

  FF_FFStar_ram : ∀ φ ∈ Mram k n M, FF ϖ χ (FFStar ϖ χ φ) = ((resCard k : ℂ) ^ Fintype.card n) • φ

  FF_mem_ram : ∀ φ ∈ Mram k n M, FF ϖ χ φ ∈ Mram k n M

  FFStar_mem_ram : ∀ φ ∈ Mram k n M, FFStar ϖ χ φ ∈ Mram k n M

  D_dia : ∀ c : 𝓀[k]ˣ, (D ϖ * dia c : Module.End ℂ (Form k n M)) = dia c * D ϖ

  FF_dia : ∀ c : 𝓀[k]ˣ, (FF ϖ χ * dia c : Module.End ℂ (Form k n M)) = dia c * FF ϖ χ

  FF_eq_D_Gs : ∀ φ ∈ Mram k n M, FF ϖ χ φ = D ϖ (Gs χ φ)

  Gs_mul_GsStar : (Gs χ * GsStar χ : Module.End ℂ (Form k n M)) = (resCard k : ℂ) • 1 - Nm

  D_U_ram : ∀ φ ∈ Mram k n M, D ϖ (U ϖ φ) = ((resCard k : ℂ) ^ ((Fintype.card n : ℤ) - 1)) • φ

  U_D_ram : ∀ φ ∈ Mram k n M, U ϖ (D ϖ φ) = ((resCard k : ℂ) ^ ((Fintype.card n : ℤ) - 1)) • φ

  FFStar_dia : ∀ c : 𝓀[k]ˣ, (FFStar ϖ χ * dia c : Module.End ℂ (Form k n M)) = dia c * FFStar ϖ χ

  U_dia : ∀ c : 𝓀[k]ˣ, (U ϖ * dia c : Module.End ℂ (Form k n M)) = dia c * U ϖ

  dia_mem_ram : ∀ c : 𝓀[k]ˣ, ∀ φ ∈ Mram k n M, dia c φ ∈ Mram k n M

  phiOne_dia : ∀ (c : 𝓀[k]ˣ) (m : Type) [Fintype m] (P : Pair k n) (Q : Pair k m),
    phiOne (c • P) (c • Q) = phiOne P Q

  twisted_class_sum : ∀ (ε : 𝓀[k]ˣ) (φ : Form k n M) (L : Submodule 𝒪[k] (n → k)) [L.IsFullLattice k]
    [Fintype {x : Red L // x ≠ 0}] (f : {f : Module.Dual 𝓀[k] (Red L) // f ≠ 0}),
    ∑ x : {x : Red L // x ≠ 0}, χ (-((ε : 𝓀[k]) * f.1 x.1)) • φ (up L ϖ x) = dia ε (FFStar ϖ χ φ) (ofDual L f)

  sign_FFStar_sign_FF : (dia (-1) * FFStar ϖ χ * (dia (-1) * FF ϖ χ) : Module.End ℂ (Form k n M)) =
    FFStar ϖ χ * FF ϖ χ

  sign_ram : ∀ φ ∈ Mram k n M,
    dia (-1) (FFStar ϖ χ (dia (-1) (FF ϖ χ φ))) = ((resCard k : ℂ) ^ Fintype.card n) • φ

  unit_ram : ∀ c : 𝓀[k]ˣ, ∀ φ ∈ Mram k n M,
    dia c (FFStar ϖ χ (dia c⁻¹ (FF ϖ χ φ))) = ((resCard k : ℂ) ^ Fintype.card n) • φ


variable (k) in
structure AdjointIdentities (n : Type) [Fintype n] (ϖ : Unif k) (χ : AddChar 𝓀[k] ℂ) : Prop where

  FF_finite : KeepsFinite (n := n) (FF ϖ χ) ∧ KeepsFinite (n := n) (FFStar ϖ χ)

  D_finite : KeepsFinite (n := n) (D ϖ) ∧ KeepsFinite (n := n) (U ϖ)

  FF_adj : IsAdj (n := n) (FF ϖ χ) (FFStar ϖ χ)

  FF_unitary : IsScaledUnitaryOn (Mram k n ℂ) ((resCard k : ℂ) ^ Fintype.card n) (FF ϖ χ)

  Gs_adj : IsAdj (n := n) (Gs χ) (GsStar χ)

  U_adj : IsAdj (n := n) (U ϖ) (D ϖ)

  dia_adj : ∀ c : 𝓀[k]ˣ, IsAdj (n := n) (dia c) (dia c⁻¹)

  dia_unitary : ∀ c : 𝓀[k]ˣ, IsScaledUnitaryOn (n := n) ⊤ 1 (dia c) ∧ IsScaledUnitaryOn (Mram k n ℂ) 1 (dia c)

  sign_adj : IsAdj (n := n) (dia (-1) * FF ϖ χ) (dia (-1) * FFStar ϖ χ)

  sign_unitary : IsScaledUnitaryOn (Mram k n ℂ) ((resCard k : ℂ) ^ Fintype.card n) (dia (-1) * FF ϖ χ)

  unit_unitary : ∀ c : 𝓀[k]ˣ, IsAdj (n := n) (dia c⁻¹ * FF ϖ χ) (dia c * FFStar ϖ χ) ∧
    IsScaledUnitaryOn (Mram k n ℂ) ((resCard k : ℂ) ^ Fintype.card n) (dia c⁻¹ * FF ϖ χ)

def PairOperatorStatement : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (ϖ : Unif k) (ψ : AddChar k Circle) (hψ : HasConductor ψ 1) (n : Type) [Fintype n] [DecidableEq n],
    (∀ (M : Type) [AddCommGroup M] [Module ℂ M],
      Vanishing k n M ϖ ∧ OperatorIdentities k n M ϖ (resChar ψ hψ ϖ)) ∧
    AdjointIdentities k n ϖ (resChar ψ hψ ϖ)

section Examples

end Examples

end GlobalTheory.IndefiniteRowSideFullHecke.AdjointOperatorIdentities
end
end

section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL ValuativeRel

namespace GlobalTheory.IndefiniteRowSideFullHecke.SatakeTrivialRangeBound

def InTrivialRange (q : ℕ) {n : ℕ} (α : Fin n → ℂˣ) : Prop :=
  ∀ i, (q : ℝ) ^ (-(((n : ℝ) - 1) / 2)) ≤ ‖(α i : ℂ)‖ ∧ ‖(α i : ℂ)‖ ≤ (q : ℝ) ^ (((n : ℝ) - 1) / 2)

def SatakeTrivialBound : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V)
    (α : Fin n → ℂˣ),
    IsSmooth π → π.IsIrreducible → IsUnitarisable π → IsSpherical π → HasSatake π α →
      InTrivialRange (resCard k) α

section Hecke

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]

end Hecke

section Basic₂

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem one_lt_resCard : 1 < resCard k := Finite.one_lt_card

end Basic₂

end GlobalTheory.IndefiniteRowSideFullHecke.SatakeTrivialRangeBound
end
end

section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL Matrix

namespace GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorLiftConclusion

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def IsUnitaryCharacter (μ : kˣ →* ℂˣ) : Prop := IsSmoothChar μ ∧ IsUnitaryChar μ

def IsIrredUnitary {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin n) k) V) : Prop :=
  IsSmooth π ∧ π.IsIrreducible ∧ IsUnitarisable π

def SupportCondition {a : ℕ} (t : ℕ) (μ : kˣ →* ℂˣ) {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin a) k) V) : Prop :=
  ∀ j : ℕ, ¬ InSupport π (μ * absPow k (((t : ℂ) + 1) / 2 + j)) ∧
    ¬ InSupport π (μ * absPow k (-(((t : ℂ) + 1) / 2 + j)))



def invTranspose (n : ℕ) (R : Type) [CommRing R] : GL (Fin n) R →* GL (Fin n) R where
  toFun h := ⟨(h⁻¹ : GL (Fin n) R).valᵀ, h.valᵀ,
    by rw [← transpose_mul, Units.mul_inv, transpose_one],
    by rw [← transpose_mul, Units.inv_mul, transpose_one]⟩
  map_one' := by
    apply Units.ext
    show ((1 : GL (Fin n) R)⁻¹ : GL (Fin n) R).valᵀ = 1
    rw [inv_one, Units.val_one, transpose_one]
  map_mul' x y := by
    apply Units.ext
    show ((x * y)⁻¹ : GL (Fin n) R).valᵀ = (x⁻¹ : GL (Fin n) R).valᵀ * (y⁻¹ : GL (Fin n) R).valᵀ
    rw [_root_.mul_inv_rev, Units.val_mul, transpose_mul]


end GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorLiftConclusion
end
end

section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL ValuativeRel
open scoped TensorProduct

namespace GlobalTheory.IndefiniteRowSideFullHecke.CuspidalSupportClasses

section Finite

variable {F : Type} [Field F] {n : ℕ} {Y : Type} [AddCommGroup Y] [Module ℂ Y]

end Finite

section Local

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def incl (n : ℕ) : GL (Fin n) 𝒪[k] →* GL (Fin n) k :=
  Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k)

def red (n : ℕ) : GL (Fin n) 𝒪[k] →* GL (Fin n) 𝓀[k] :=
  Matrix.GeneralLinearGroup.map (IsLocalRing.residue 𝒪[k])

def diagOne (r t : ℕ) : GL (Fin r) 𝒪[k] →* GL (Fin (r + t)) k :=
  (emb₂ k (stdSum (rfl : r + t = r + t))).comp ((MonoidHom.inl _ _).comp (incl k r))

def unipLevel (r : ℕ) : Subgroup (GL (Fin r) 𝒪[k]) := (unipB 𝓀[k] (Fin r)).comap (red k r)

variable {k} {r t n : ℕ} {V W Y : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  [AddCommGroup Y] [Module ℂ Y]

def HasBlocks (h : GL (Fin (r + t)) 𝒪[k]) (a : GL (Fin r) 𝒪[k]) (d : GL (Fin t) 𝒪[k]) : Prop :=
  (∀ i j, h.val (Fin.castAdd t i) (Fin.castAdd t j) = a.val i j) ∧
  (∀ i j, h.val (Fin.natAdd r i) (Fin.natAdd r j) = d.val i j) ∧
  ∀ i j, h.val (Fin.natAdd r i) (Fin.castAdd t j) ∈ IsLocalRing.maximalIdeal 𝒪[k]

def IsDatum (σ : Representation ℂ (GL (Fin r) k) V) (χW χV : kˣ →* ℂˣ) : Prop :=
  (σ.IsIrreducible ∧ IsSmooth σ ∧ IsUnitarisable σ) ∧
    IsUnitaryChar χW ∧ IsUnitaryChar χV ∧ IsTame χW ∧ IsUnram (χW * χV⁻¹)

end Local

section Places

variable {ι : Type} [Fintype ι] (k : ι → Type) [∀ v, Field (k v)] [∀ v, ValuativeRel (k v)]
  [∀ v, TopologicalSpace (k v)] [∀ v, IsNonarchimedeanLocalField (k v)] (r : ℕ)

variable {k r}

end Places

section Examples

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem isDatum_detRep (r : ℕ) {χ χW χV : kˣ →* ℂˣ} (h : IsUnram χ) (hu : IsUnitaryChar χ)
    (hW : IsUnitaryChar χW) (hV : IsUnitaryChar χV) (ht : IsTame χW) (hr : IsUnram (χW * χV⁻¹)) :
    IsDatum (detRep (Fin r) χ) χW χV :=
  ⟨⟨isIrreducible_ofChar _, (isSmooth_ofChar_iff _).2 (GlobalTheory.SmGL.isSmoothChar_of_isUnram h).detChar,
    (isUnitarisable_ofChar_iff _).2 fun _ => hu _⟩, hW, hV, ht, hr⟩

end Examples

end GlobalTheory.IndefiniteRowSideFullHecke.CuspidalSupportClasses
end
end
