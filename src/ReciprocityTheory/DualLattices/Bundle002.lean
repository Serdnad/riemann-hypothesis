module

public import Mathlib.Basic.NNReal.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.RingTheory.Valuation.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Perfectoid.FontaineTheta
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.LocalRing.Defs
public import Mathlib.NumberTheory.ArithmeticFunction.Misc
public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Basic
public import Mathlib.NumberTheory.ModularForms.QExpansion
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
public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.QExpansion
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
public import Mathlib.NumberTheory.Bernoulli

@[expose] public section

section

noncomputable section

open Finset

namespace ReciprocityTheory.PGsh.L2

variable {C : Type} [Field C] (R : Type) [CommRing R] [Algebra R C]

def intFun (X : Type) : Submodule R (X → C) where
  carrier := {f | ∀ x, ∃ r : R, algebraMap R C r = f x}
  add_mem' := by
    rintro f g hf hg x
    obtain ⟨r, hr⟩ := hf x
    obtain ⟨s, hs⟩ := hg x
    exact ⟨r + s, by simp [hr, hs]⟩
  zero_mem' := fun _ => ⟨0, by simp⟩
  smul_mem' := by
    rintro c f hf x
    obtain ⟨r, hr⟩ := hf x
    exact ⟨c * r, by simp [hr, Algebra.smul_def]⟩

def tensorSpan {X : Type} (M : Submodule R (X → C)) : Submodule R (X × X → C) :=
  Submodule.span R {F | ∃ g ∈ M, ∃ h ∈ M, F = fun p => g p.1 * h p.2}

def IsLat {X : Type} [Fintype X] [DecidableEq X] (M : Submodule R (X → C)) : Prop :=
  ∃ B : Matrix X X C, IsUnit B.det ∧ M = Submodule.span R (Set.range fun j x => B x j)

def HasColen (v : Valuation C NNReal) {X : Type} [Fintype X] [DecidableEq X]
    (M : Submodule R (X → C)) (c : NNReal) : Prop :=
  ∃ B : Matrix X X C, M = Submodule.span R (Set.range fun j x => B x j) ∧ v B.det = c

def addPull (N : Type) [AddCommGroup N] : (N → C) →ₗ[R] (N × N → C) :=
  LinearMap.funLeft R C (fun p : N × N => p.1 + p.2)

structure HopfOrder (N : Type) [AddCommGroup N] [Fintype N] [DecidableEq N] where
  carrier : Submodule R (N → C)
  lat : IsLat R carrier
  le_int : carrier ≤ intFun R N
  one_mem : (1 : N → C) ∈ carrier
  mul_mem : ∀ f g, f ∈ carrier → g ∈ carrier → f * g ∈ carrier
  comul : ∀ f ∈ carrier, addPull R N f ∈ tensorSpan R carrier
  antipode : ∀ f ∈ carrier, (fun x => f (-x)) ∈ carrier

variable {R}

def dualLat {X : Type} [Fintype X] (M : Submodule R (X → C)) : Submodule R (X → C) where
  carrier := {u | ∀ f ∈ M, ∃ r : R, algebraMap R C r = ∑ a, u a * f a}
  add_mem' := by
    rintro u w hu hw f hf
    obtain ⟨r, hr⟩ := hu f hf
    obtain ⟨s, hs⟩ := hw f hf
    exact ⟨r + s, by simp [hr, hs, add_mul, Finset.sum_add_distrib]⟩
  zero_mem' := fun _ _ => ⟨0, by simp⟩
  smul_mem' := by
    rintro c u hu f hf
    obtain ⟨r, hr⟩ := hu f hf
    refine ⟨c * r, ?_⟩
    simp only [map_mul, hr, Pi.smul_apply, Algebra.smul_def, Finset.mul_sum, mul_assoc]

def fourier {N H : Type} [Fintype N] (e : H → N → C) :
    (N → C) →ₗ[R] (H → C) where
  toFun u h := ∑ a, u a * e h a
  map_add' u w := by ext h; simp [add_mul, Finset.sum_add_distrib]
  map_smul' c u := by ext h; simp [Algebra.smul_def, Finset.mul_sum, mul_assoc]

def augIdeal {X : Type} [AddCommGroup X] (M : Submodule R (X → C)) : Submodule R (X → C) :=
  M ⊓ LinearMap.ker (LinearMap.proj (R := R) (φ := fun _ : X => C) 0)

def resK {N : Type} [AddCommGroup N] (K : AddSubgroup N) : (N → C) →ₗ[R] (K → C) :=
  LinearMap.funLeft R C (fun k : K => (k : N))

def pullQ {N : Type} [AddCommGroup N] (K : AddSubgroup N) : (N ⧸ K → C) →ₗ[R] (N → C) :=
  LinearMap.funLeft R C (QuotientAddGroup.mk : N → N ⧸ K)

def extK {N : Type} [AddCommGroup N] (K : AddSubgroup N) [DecidablePred (· ∈ K)] :
    (K → C) →ₗ[R] (N → C) where
  toFun u a := if h : a ∈ K then u ⟨a, h⟩ else 0
  map_add' u w := by ext a; by_cases h : a ∈ K <;> simp [h]
  map_smul' c u := by ext a; by_cases h : a ∈ K <;> simp [h]

def pushQ {N : Type} [AddCommGroup N] [Fintype N] (K : AddSubgroup N)
    [DecidableEq (N ⧸ K)] : (N → C) →ₗ[R] (N ⧸ K → C) where
  toFun u c := ∑ a ∈ Finset.univ.filter (fun a : N => (a : N ⧸ K) = c), u a
  map_add' u w := by ext c; simp [Finset.sum_add_distrib]
  map_smul' c u := by ext d; simp [Finset.smul_sum]

end ReciprocityTheory.PGsh.L2
end
end

section

noncomputable section

open Finset Filter Topology

namespace ReciprocityTheory.PGsh.Up.Det2

theorem v_det_scaled {C : Type} [Field C] (v : Valuation C NNReal) {ι : Type} [Fintype ι]
    [DecidableEq ι] (c : Matrix ι ι C) (y z : ι → C) :
    v (Matrix.of fun j k => c j k * (y j / z k)).det =
      v c.det * (∏ j, v (y j)) / ∏ k, v (z k) := by
  have hM : (Matrix.of fun j k => c j k * (y j / z k)) =
      Matrix.diagonal y * c * Matrix.diagonal fun k => (z k)⁻¹ := by
    ext j k
    simp only [Matrix.of_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, div_eq_mul_inv]
    ring
  rw [hM, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, Matrix.det_diagonal, map_mul, map_mul,
    map_prod, map_prod]
  simp only [map_inv₀, Finset.prod_inv_distrib, div_eq_mul_inv]
  ring

end ReciprocityTheory.PGsh.Up.Det2
end
end

section

noncomputable section

open WittVector Ideal

namespace ReciprocityTheory.PGsh

section Ainf

variable (p : ℕ) [Fact p.Prime] (C : Type) [Field C] (v : Valuation C NNReal)
  (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)]
  [IsAdicComplete (span {(p : O)}) O]

def KerThetaStatement : Prop :=
  ∀ pflat : PreTilt O p, pflat.untilt = (p : O) →
    RingHom.ker (fontaineTheta O p) =
        span {(p : WittVector p (PreTilt O p)) - teichmuller p pflat} ∧
      ((p : WittVector p (PreTilt O p)) - teichmuller p pflat) ∈
        nonZeroDivisors (WittVector p (PreTilt O p)) ∧
      RingHom.ker ((Ideal.Quotient.mk (span {(p : O)})).comp (fontaineTheta O p)) =
        span {(p : WittVector p (PreTilt O p)), teichmuller p pflat}

def XiNuStatement : Prop :=
  ∀ ε : PreTilt O p, v.Integers O →
    IsPrimitiveRoot (((frobeniusEquiv (PreTilt O p) p).symm ε).untilt) p →
      teichmuller p ε - 1 =
          (∑ i ∈ Finset.range p, teichmuller p ((frobeniusEquiv (PreTilt O p) p).symm ε) ^ i) *
            (teichmuller p ((frobeniusEquiv (PreTilt O p) p).symm ε) - 1) ∧
        fontaineTheta O p (teichmuller p ((frobeniusEquiv (PreTilt O p) p).symm ε) - 1) =
          ((frobeniusEquiv (PreTilt O p) p).symm ε).untilt - 1 ∧
        v (algebraMap O C (fontaineTheta O p
            (teichmuller p ((frobeniusEquiv (PreTilt O p) p).symm ε) - 1))) ^ (p - 1) =
          v (p : C) ∧
        ∀ pflat : PreTilt O p, pflat.untilt = (p : O) →
          RingHom.ker (fontaineTheta O p) =
              span {∑ i ∈ Finset.range p,
                teichmuller p ((frobeniusEquiv (PreTilt O p) p).symm ε) ^ i} ∧
            ∃ u : (WittVector p (PreTilt O p))ˣ,
              ∑ i ∈ Finset.range p, teichmuller p ((frobeniusEquiv (PreTilt O p) p).symm ε) ^ i =
                u * ((p : WittVector p (PreTilt O p)) - teichmuller p pflat)

def RegularStatement : Prop :=
  ∀ pflat : PreTilt O p, pflat.untilt = (p : O) →
    (p : WittVector p (PreTilt O p)) ∈ nonZeroDivisors (WittVector p (PreTilt O p)) ∧
      (∀ x : WittVector p (PreTilt O p),
          teichmuller p pflat * x ∈ span {(p : WittVector p (PreTilt O p))} →
            x ∈ span {(p : WittVector p (PreTilt O p))}) ∧
      span {(p : WittVector p (PreTilt O p)), teichmuller p pflat} ≠ ⊤

def FlatW'Statement : Prop :=
  ∀ pflat : PreTilt O p, pflat.untilt = (p : O) →
    span {(p : WittVector p (PreTilt O p)) ^ 2, teichmuller p pflat} =
        span {((p : WittVector p (PreTilt O p)) - teichmuller p pflat) ^ 2, teichmuller p pflat} ∧
      ((p : WittVector p (PreTilt O p) ⧸
          span {(p : WittVector p (PreTilt O p)) ^ 2, teichmuller p pflat}) ^ 2 = 0) ∧
      (∀ x : WittVector p (PreTilt O p) ⧸
            span {(p : WittVector p (PreTilt O p)) ^ 2, teichmuller p pflat},
          (p : WittVector p (PreTilt O p) ⧸
              span {(p : WittVector p (PreTilt O p)) ^ 2, teichmuller p pflat}) * x = 0 →
            ∃ y, x = (p : WittVector p (PreTilt O p) ⧸
              span {(p : WittVector p (PreTilt O p)) ^ 2, teichmuller p pflat}) * y) ∧
      ∀ [Algebra (ZMod (p ^ 2)) (WittVector p (PreTilt O p) ⧸
          span {(p : WittVector p (PreTilt O p)) ^ 2, teichmuller p pflat})],
        Module.Flat (ZMod (p ^ 2)) (WittVector p (PreTilt O p) ⧸
          span {(p : WittVector p (PreTilt O p)) ^ 2, teichmuller p pflat})

end Ainf

def TiltStructureStatement (p : ℕ) [Fact p.Prime] : Prop :=
  ∀ (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal)
    (O : Type) [CommRing O] [Algebra O C], v.Integers O →
    ∀ [Fact ¬IsUnit (p : O)] [IsAdicComplete (span {(p : O)}) O],
      (∃ pflat : PreTilt O p, pflat.untilt = (p : O)) ∧
      (∃ ε : PreTilt O p, IsPrimitiveRoot (((frobeniusEquiv (PreTilt O p) p).symm ε).untilt) p) ∧
      KerThetaStatement p O ∧ XiNuStatement p C v O ∧ RegularStatement p O ∧
      FlatW'Statement p O

def TeichSumStatement (p : ℕ) [Fact p.Prime] : Prop :=
  ∀ (ι : Type) (s : Finset ι),
    (∃ S : MvPolynomial ι ℤ, (p : MvPolynomial ι ℤ) * S =
      ∑ i ∈ s, MvPolynomial.X i ^ p - (∑ i ∈ s, MvPolynomial.X i) ^ p) ∧
    ∀ (K : Type) [CommRing K] [CharP K p] [PerfectRing K p] (X : ι → K) (S : MvPolynomial ι ℤ),
      (p : MvPolynomial ι ℤ) * S =
          ∑ i ∈ s, MvPolynomial.X i ^ p - (∑ i ∈ s, MvPolynomial.X i) ^ p →
        (∃ w : WittVector p K,
          ∑ i ∈ s, teichmuller p (X i) =
            teichmuller p (∑ i ∈ s, X i) + (p : WittVector p K) *
              teichmuller p (MvPolynomial.aeval (fun i => (frobeniusEquiv K p).symm (X i)) S) +
              (p : WittVector p K) ^ 2 * w) ∧
        ∀ (y : K) (t : WittVector p K), ∃ w : WittVector p K,
          (teichmuller p y + (p : WittVector p K) * t) ^ p =
            teichmuller p (y ^ p) + (p : WittVector p K) ^ 2 * w

end ReciprocityTheory.PGsh
end
end

section

noncomputable section

open IsLocalRing TensorProduct

namespace ReciprocityTheory.PGsh

universe u

structure LAlg (R₀ : Type u) [CommRing R₀] where
  carrier : Type u
  [cr : CommRing carrier]
  [alg : Algebra R₀ carrier]
  [loc : IsLocalRing carrier]

attribute [instance] LAlg.cr LAlg.alg LAlg.loc

variable {R₀ : Type u} [CommRing R₀]

instance : CoeSort (LAlg R₀) (Type u) := ⟨LAlg.carrier⟩

def LHom (R S : LAlg R₀) : Type u := {f : R →ₐ[R₀] S // IsLocalHom (f : R →+* S)}

def LHom.id (R : LAlg R₀) : LHom R R := ⟨AlgHom.id R₀ R, ⟨fun _ h => h⟩⟩

def LHom.comp {R S T : LAlg R₀} (g : LHom S T) (f : LHom R S) : LHom R T :=
  ⟨g.1.comp f.1, ⟨fun a h => f.2.map_nonunit a (g.2.map_nonunit (f.1 a) h)⟩⟩

abbrev LHom.ker {R S : LAlg R₀} (π : LHom R S) : Submodule R₀ R :=
  (RingHom.ker π.1).restrictScalars R₀

def LHom.SqZero {R S : LAlg R₀} (π : LHom R S) : Prop :=
  Function.Surjective π.1 ∧ RingHom.ker π.1 ^ 2 = ⊥

lemma LHom.sqZero_of_span {R S : LAlg R₀} (π : LHom R S) (ξ : (R : Type u))
    (hs : Function.Surjective π.1) (hk : RingHom.ker π.1 = Ideal.span {ξ}) (hξ : ξ * ξ = 0) :
    π.SqZero := by
  unfold ReciprocityTheory.PGsh.LHom.SqZero
  refine ⟨hs, ?_⟩
  rw [hk, Ideal.span_singleton_pow, pow_two, hξ]
  exact Ideal.span_singleton_eq_bot.mpr rfl

def LHom.NilSurj {R S : LAlg R₀} (π : LHom R S) : Prop :=
  Function.Surjective π.1 ∧ ∃ n : ℕ, RingHom.ker π.1 ^ n = ⊥

def IsFibreSq {F R₁ R₂ R : LAlg R₀} (p₁ : LHom F R₁) (p₂ : LHom F R₂) (f₁ : LHom R₁ R)
    (f₂ : LHom R₂ R) : Prop :=
  f₁.1.comp p₁.1 = f₂.1.comp p₂.1 ∧ f₁.NilSurj ∧ f₂.NilSurj ∧
    ∀ a b, f₁.1 a = f₂.1 b → ∃! c, p₁.1 c = a ∧ p₂.1 c = b

def CarriesFibre {X₁ X₂ X Y : Type*} (q₁ : Y → X₁) (q₂ : Y → X₂) (g₁ : X₁ → X) (g₂ : X₂ → X) :
    Prop :=
  ∀ a b, g₁ a = g₂ b → ∃! c, q₁ c = a ∧ q₂ c = b

structure BX (R₀ : Type u) [CommRing R₀] where
  G : LAlg R₀ → Type u
  [grp : ∀ R, AddCommGroup (G R)]
  map : ∀ {R S : LAlg R₀}, LHom R S → G R →+ G S
  map_id : ∀ (R : LAlg R₀) (x : G R), map (LHom.id R) x = x
  map_comp : ∀ {R S T : LAlg R₀} (f : LHom R S) (g : LHom S T) (x : G R),
    map (g.comp f) x = map g (map f x)
  gg : Type u
  [ggg : AddCommGroup gg]
  [ggm : Module R₀ gg]
  [ggfree : Module.Free R₀ gg]
  [ggfin : Module.Finite R₀ gg]
  tg : ∀ {R S : LAlg R₀} (π : LHom R S), π.SqZero → gg ⊗[R₀] π.ker →+ G R
  tg_nat : ∀ {R S R' S' : LAlg R₀} (π : LHom R S) (π' : LHom R' S') (hπ : π.SqZero)
    (hπ' : π'.SqZero) (f : LHom R R') (hf : ∀ a ∈ π.ker, f.1.toLinearMap a ∈ π'.ker)
    (v : gg ⊗[R₀] π.ker),
    tg π' hπ' (LinearMap.lTensor gg (f.1.toLinearMap.restrict hf) v) = map f (tg π hπ v)
  surj : ∀ {R S : LAlg R₀} (π : LHom R S), π.SqZero → Function.Surjective (map π)
  tg_inj : ∀ {R S : LAlg R₀} (π : LHom R S) (hπ : π.SqZero), Function.Injective (tg π hπ)
  tg_ker : ∀ {R S : LAlg R₀} (π : LHom R S) (hπ : π.SqZero) (x : G R),
    map π x = 0 ↔ ∃ v, tg π hπ v = x
  P : ∀ R : LAlg R₀, G R → G R → Type u
  smul : ∀ {R : LAlg R₀} {x y : G R}, (R : Type u)ˣ → P R x y → P R x y
  one_smul : ∀ {R : LAlg R₀} {x y : G R} (u : P R x y), smul 1 u = u
  mul_smul : ∀ {R : LAlg R₀} {x y : G R} (l l' : (R : Type u)ˣ) (u : P R x y),
    smul (l * l') u = smul l (smul l' u)
  nonempty : ∀ (R : LAlg R₀) (x y : G R), Nonempty (P R x y)
  trans : ∀ {R : LAlg R₀} {x y : G R} (u w : P R x y), ∃! l : (R : Type u)ˣ, smul l u = w
  pmap : ∀ {R S : LAlg R₀} (f : LHom R S) {x y : G R}, P R x y → P S (map f x) (map f y)
  pmap_smul : ∀ {R S : LAlg R₀} (f : LHom R S) {x y : G R} (l : (R : Type u)ˣ) (u : P R x y),
    pmap f (smul l u) = smul (Units.map (f.1 : R →* S) l) (pmap f u)
  pmap_id : ∀ {R : LAlg R₀} {x y : G R} (u : P R x y), HEq (pmap (LHom.id R) u) u
  pmap_comp : ∀ {R S T : LAlg R₀} (f : LHom R S) (g : LHom S T) {x y : G R} (u : P R x y),
    HEq (pmap (g.comp f) u) (pmap g (pmap f u))
  add1 : ∀ {R : LAlg R₀} {x x' y : G R}, P R x y → P R x' y → P R (x + x') y
  add2 : ∀ {R : LAlg R₀} {x y y' : G R}, P R x y → P R x y' → P R x (y + y')
  zero1 : ∀ {R : LAlg R₀} (y : G R), P R 0 y
  zero2 : ∀ {R : LAlg R₀} (x : G R), P R x 0
  addFst_assoc : ∀ {R : LAlg R₀} {x x' x'' y : G R} (u : P R x y) (u' : P R x' y)
    (u'' : P R x'' y), HEq (add1 (add1 u u') u'') (add1 u (add1 u' u''))
  addSnd_assoc : ∀ {R : LAlg R₀} {x y y' y'' : G R} (u : P R x y) (u' : P R x y')
    (u'' : P R x y''), HEq (add2 (add2 u u') u'') (add2 u (add2 u' u''))
  addFst_comm : ∀ {R : LAlg R₀} {x x' y : G R} (u : P R x y) (u' : P R x' y),
    HEq (add1 u u') (add1 u' u)
  addSnd_comm : ∀ {R : LAlg R₀} {x y y' : G R} (u : P R x y) (u' : P R x y'),
    HEq (add2 u u') (add2 u' u)
  zeroFst_add : ∀ {R : LAlg R₀} {x y : G R} (u : P R x y), HEq (add1 (zero1 y) u) u
  zeroSnd_add : ∀ {R : LAlg R₀} {x y : G R} (u : P R x y), HEq (add2 (zero2 x) u) u
  addFst_smul : ∀ {R : LAlg R₀} {x x' y : G R} (l l' : (R : Type u)ˣ) (u : P R x y)
    (u' : P R x' y), add1 (smul l u) (smul l' u') = smul (l * l') (add1 u u')
  addSnd_smul : ∀ {R : LAlg R₀} {x y y' : G R} (l l' : (R : Type u)ˣ) (u : P R x y)
    (u' : P R x y'), add2 (smul l u) (smul l' u') = smul (l * l') (add2 u u')
  interchange : ∀ {R : LAlg R₀} {x x' y y' : G R} (u : P R x y) (u' : P R x' y)
    (w : P R x y') (w' : P R x' y'),
    add2 (add1 u u') (add1 w w') = add1 (add2 u w) (add2 u' w')
  addFst_nat : ∀ {R S : LAlg R₀} (f : LHom R S) {x x' y : G R} (u : P R x y) (u' : P R x' y),
    HEq (pmap f (add1 u u')) (add1 (pmap f u) (pmap f u'))
  addSnd_nat : ∀ {R S : LAlg R₀} (f : LHom R S) {x y y' : G R} (u : P R x y) (u' : P R x y'),
    HEq (pmap f (add2 u u')) (add2 (pmap f u) (pmap f u'))
  zeroFst_nat : ∀ {R S : LAlg R₀} (f : LHom R S) (y : G R),
    HEq (pmap f (zero1 y)) (zero1 (map f y))
  zeroSnd_nat : ∀ {R S : LAlg R₀} (f : LHom R S) (x : G R),
    HEq (pmap f (zero2 x)) (zero2 (map f x))
  sw : ∀ {R : LAlg R₀} {x y : G R}, P R x y → P R y x
  sw_smul : ∀ {R : LAlg R₀} {x y : G R} (l : (R : Type u)ˣ) (u : P R x y),
    sw (smul l u) = smul l (sw u)
  sw_nat : ∀ {R S : LAlg R₀} (f : LHom R S) {x y : G R} (u : P R x y),
    sw (pmap f u) = pmap f (sw u)
  swap_addFst : ∀ {R : LAlg R₀} {x x' y : G R} (u : P R x y) (u' : P R x' y),
    sw (add1 u u') = add2 (sw u) (sw u')
  sw_sw : ∀ {R : LAlg R₀} {x y : G R} (u : P R x y), sw (sw u) = u
  fibre_G : ∀ {F R₁ R₂ R : LAlg R₀} (p₁ : LHom F R₁) (p₂ : LHom F R₂) (f₁ : LHom R₁ R)
    (f₂ : LHom R₂ R), IsFibreSq p₁ p₂ f₁ f₂ → CarriesFibre (map p₁) (map p₂) (map f₁) (map f₂)
  fibre_P : ∀ {F R₁ R₂ R : LAlg R₀} (p₁ : LHom F R₁) (p₂ : LHom F R₂) (f₁ : LHom R₁ R)
    (f₂ : LHom R₂ R), IsFibreSq p₁ p₂ f₁ f₂ →
    CarriesFibre
      (fun t : (Σ x y : G F, P F x y) =>
        (⟨map p₁ t.1, map p₁ t.2.1, pmap p₁ t.2.2⟩ : Σ x y : G R₁, P R₁ x y))
      (fun t : (Σ x y : G F, P F x y) =>
        (⟨map p₂ t.1, map p₂ t.2.1, pmap p₂ t.2.2⟩ : Σ x y : G R₂, P R₂ x y))
      (fun t : (Σ x y : G R₁, P R₁ x y) =>
        (⟨map f₁ t.1, map f₁ t.2.1, pmap f₁ t.2.2⟩ : Σ x y : G R, P R x y))
      (fun t : (Σ x y : G R₂, P R₂ x y) =>
        (⟨map f₂ t.1, map f₂ t.2.1, pmap f₂ t.2.2⟩ : Σ x y : G R, P R x y))

attribute [instance] BX.grp BX.ggg BX.ggm BX.ggfree BX.ggfin

namespace BX

variable (B : BX R₀) {R : LAlg R₀}

def tr1 {x x' y : B.G R} (h : x = x') (u : B.P R x y) : B.P R x' y := h ▸ u

def tr2 {x y y' : B.G R} (h : y = y') (u : B.P R x y) : B.P R x y' := h ▸ u

def nsmul1 {x y : B.G R} (u : B.P R x y) : (n : ℕ) → B.P R (n • x) y
  | 0 => B.tr1 (zero_nsmul x).symm (B.zero1 y)
  | n + 1 => B.tr1 (succ_nsmul x n).symm (B.add1 (nsmul1 u n) u)

def nsmul2 {x y : B.G R} (u : B.P R x y) : (n : ℕ) → B.P R x (n • y)
  | 0 => B.tr2 (zero_nsmul y).symm (B.zero2 x)
  | n + 1 => B.tr2 (succ_nsmul y n).symm (B.add2 (nsmul2 u n) u)

def IsPairing (N : ℕ) (x y : B.G R) (z : (R : Type u)ˣ) : Prop :=
  ∃ (hx : N • x = 0) (hy : N • y = 0) (u : B.P R x y) (l₁ l₂ : (R : Type u)ˣ),
    B.tr1 hx (B.nsmul1 u N) = B.smul l₁ (B.zero1 y) ∧
      B.tr2 hy (B.nsmul2 u N) = B.smul l₂ (B.zero2 x) ∧ z = l₁ / l₂

end BX

end ReciprocityTheory.PGsh
end
end

section

namespace ReciprocityTheory.PGsh

open ModularForm EisensteinSeries ArithmeticFunction PowerSeries UpperHalfPlane
open scoped ArithmeticFunction.sigma

def e4Z : PowerSeries ℤ := PowerSeries.mk fun n => if n = 0 then 1 else 240 * (σ 3 n : ℤ)

def e6Z : PowerSeries ℤ := PowerSeries.mk fun n => if n = 0 then 1 else -504 * (σ 5 n : ℤ)

theorem qExpansion_E₄_eq : qExpansion 1 E₄ = PowerSeries.map (Int.castRingHom ℂ) e4Z := by
  ext n
  rw [coeff_map, e4Z, coeff_mk]
  by_cases hn : n = 0
  · subst hn; norm_num [E_qExpansion_coeff _ ⟨2, rfl⟩]
  · norm_num [E_qExpansion_coeff _ ⟨2, rfl⟩, hn, show bernoulli 4 = -1 / 30 by decide +kernel]

theorem qExpansion_E₆_eq : qExpansion 1 E₆ = PowerSeries.map (Int.castRingHom ℂ) e6Z := by
  ext n
  rw [coeff_map, e6Z, coeff_mk]
  by_cases hn : n = 0
  · subst hn; norm_num [E_qExpansion_coeff _ ⟨3, rfl⟩]
  · norm_num [E_qExpansion_coeff _ ⟨3, rfl⟩, hn, show bernoulli 6 = 1 / 42 by decide +kernel]

end ReciprocityTheory.PGsh
end
