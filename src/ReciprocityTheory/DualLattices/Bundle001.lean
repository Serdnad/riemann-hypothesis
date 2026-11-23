module

public import Mathlib.Algebra.Algebra.ZMod
public import Mathlib.NumberTheory.MulChar.Basic
public import Mathlib.RingTheory.Trace.Defs
public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.RingTheory.Ideal.Quotient.Basic
public import Mathlib.RingTheory.Valuation.Integers
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.RingTheory.LocalRing.Defs
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.Matrix.MvPolynomial
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.ZMod.Basic
public import Mathlib.RingTheory.MvPowerSeries.Substitution
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.RingTheory.Valuation.Basic
public import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.Tactic.Continuity
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
public import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Algebra.CharP.Basic
public import Mathlib.Algebra.Ring.Hom.InjSurj
public import Mathlib.Data.Matrix.Basic
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic

@[expose] public section

section

namespace ReciprocityTheory.PGsh

open Matrix

def CharTableStatement : Prop :=
  ∀ (K : Type) [Field K] (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (e : G ≃ AddChar G K),
    (Matrix.of fun g h : G => e h g).det ^ 2 = (Fintype.card G : K) ^ Fintype.card G ∨
    (Matrix.of fun g h : G => e h g).det ^ 2 = -(Fintype.card G : K) ^ Fintype.card G

def GaussCongruenceStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : Type) [Field F] [Fintype F] [CharP F p]
    (O : Type) [CommRing O] [IsDomain O] (m : Ideal O) [m.IsPrime]
    (ι : F →+* O ⧸ m) (ω : MulChar F O) (ζ : O),
    Fintype.card F ≠ 2 → ζ ^ p = 1 → (∀ a, Ideal.Quotient.mk m (ω a) = ι a) →
    letI : Algebra (ZMod p) F := ZMod.algebra F p
    ∃ y ∈ m, (∑ a : F, ω⁻¹ a * ζ ^ (Algebra.trace (ZMod p) F a).val) = (ζ - 1) * (y - 1)

end ReciprocityTheory.PGsh
end

section

noncomputable section

open Finset Matrix

namespace ReciprocityTheory.PGsh.Up.FrobeniusGroupField

variable {C : Type} [Field C] {v : Valuation C NNReal} {R : Type} [CommRing R] [Algebra R C]

def mI (hv : v.Integers R) : Ideal R where
  carrier := {r | v (algebraMap R C r) < 1}
  add_mem' {a b} ha hb := by
    simp only [Set.mem_ofPred_eq, map_add (f := _)] at *
    exact v.map_add_lt ha hb
  zero_mem' := by simp
  smul_mem' c x hx := by
    simp only [Set.mem_ofPred_eq, smul_eq_mul, map_mul] at *
    calc v (algebraMap R C c) * v (algebraMap R C x) ≤ 1 * v (algebraMap R C x) :=
          mul_le_mul_of_nonneg_right (hv.map_le_one c) zero_le
      _ < 1 := by rwa [one_mul]

theorem mem_mI (hv : v.Integers R) (r : R) : r ∈ mI hv ↔ v (algebraMap R C r) < 1 := Iff.rfl

theorem v_eq_one_iff (hv : v.Integers R) (r : R) : v (algebraMap R C r) = 1 ↔ r ∉ mI hv := by
  rw [mem_mI, not_lt]
  exact ⟨fun h => h.ge, fun h => le_antisymm (hv.map_le_one r) h⟩

theorem isUnit_of_not_mem (hv : v.Integers R) {r : R} (h : r ∉ mI hv) : IsUnit r :=
  hv.isUnit_of_one' ((v_eq_one_iff hv r).2 h)

theorem mI_isMaximal (hv : v.Integers R) : (mI hv).IsMaximal := by
  rw [Ideal.isMaximal_iff]
  refine ⟨by simp [mem_mI], fun J x hle hx hxJ => ?_⟩
  obtain ⟨u, rfl⟩ := isUnit_of_not_mem hv hx
  have : (↑u⁻¹ : R) * u ∈ J := J.mul_mem_left _ hxJ
  simpa using this

theorem isDomain (hv : v.Integers R) : IsDomain R := by
  have : Nontrivial R := ⟨0, 1, fun h => by
    have := congrArg (fun r => v (algebraMap R C r)) h
    simp at this⟩
  exact hv.hom_inj.isDomain (algebraMap R C)

abbrev res (hv : v.Integers R) : R →+* R ⧸ mI hv := Ideal.Quotient.mk (mI hv)

theorem res_eq_zero (hv : v.Integers R) (r : R) : res hv r = 0 ↔ v (algebraMap R C r) < 1 :=
  Ideal.Quotient.eq_zero_iff_mem

theorem res_ne_zero (hv : v.Integers R) (r : R) : res hv r ≠ 0 ↔ v (algebraMap R C r) = 1 := by
  rw [Ne, res_eq_zero, v_eq_one_iff hv, mem_mI]

instance instField (hv : v.Integers R) : Field (R ⧸ mI hv) :=
  haveI := mI_isMaximal hv
  Ideal.Quotient.field _

theorem charP (p : ℕ) [hp : Fact p.Prime] (hv : v.Integers R)
    (hpv : v (algebraMap R C (p : R)) < 1) : CharP (R ⧸ mI hv) p := by
  have h0 : ((p : R ⧸ mI hv)) = 0 := by
    rw [← map_natCast (res hv), res_eq_zero]; exact hpv
  exact (CharP.charP_iff_prime_eq_zero hp.out).2 h0

theorem idem_eq_zero (hv : v.Integers R) {n : Type} [Fintype n] [DecidableEq n]
    (e : Matrix n n R) (he : e * e = e) (hm : ∀ a b, e a b ∈ mI hv) : e = 0 := by
  have hmap : e.map (res hv) = 0 := by
    ext a b; simpa [Ideal.Quotient.eq_zero_iff_mem] using hm a b
  have hdet : IsUnit (1 - e).det := by
    apply isUnit_of_not_mem hv
    intro h
    have h1 : res hv (1 - e).det = 0 := Ideal.Quotient.eq_zero_iff_mem.2 h
    rw [RingHom.map_det, map_sub, map_one, RingHom.mapMatrix_apply, hmap, sub_zero,
      Matrix.det_one] at h1
    exact one_ne_zero h1
  have hu : IsUnit (1 - e) := (Matrix.isUnit_iff_isUnit_det _).2 hdet
  have : e * (1 - e) = 0 := by rw [mul_sub, mul_one, he, sub_self]
  exact (hu.mul_left_eq_zero).1 this

end ReciprocityTheory.PGsh.Up.FrobeniusGroupField
end
end

section

noncomputable section

open PowerSeries

namespace ReciprocityTheory.PGsh

namespace TowerExample

variable (p : ℕ) [Fact p.Prime]

lemma ne_top (m : ℕ) (hm : 0 < m) : Ideal.span {(X : (ZMod p)⟦X⟧) ^ m} ≠ ⊤ := by
  rw [Ne, Ideal.span_singleton_eq_top, PowerSeries.isUnit_iff_constantCoeff]
  simp [zero_pow hm.ne']

lemma isLocalHom_of_surj {R S : Type} [CommRing R] [IsLocalRing R] [CommRing S] [Nontrivial S]
    (f : R →+* S) (hf : Function.Surjective f) : IsLocalHom f := by
  refine ⟨fun a ha => ?_⟩
  by_contra hna
  obtain ⟨c, hc⟩ := hf (↑ha.unit⁻¹ : S)
  have hker : RingHom.ker f ≤ IsLocalRing.maximalIdeal R :=
    IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top f)
  have h1 : 1 - a * c ∈ RingHom.ker f := by
    rw [RingHom.mem_ker, RingHom.map_sub, map_one, map_mul, hc, IsUnit.mul_val_inv, sub_self]
  have h2 : a * c ∈ IsLocalRing.maximalIdeal R :=
    Ideal.mul_mem_right c _ ((IsLocalRing.mem_maximalIdeal a).2 hna)
  have h3 := Ideal.add_mem _ (hker h1) h2
  rw [sub_add_cancel] at h3
  exact (Ideal.ne_top_iff_one _).1 (IsLocalRing.maximalIdeal.isMaximal R).ne_top h3

end TowerExample


end ReciprocityTheory.PGsh
end
end

section

noncomputable section

open MvPolynomial Matrix Finset

open scoped Classical

namespace ReciprocityTheory.PGsh

variable {ν : ℕ} {ι : Type*}

def vw (p : Fin ν × ι) : ℕ := 2 ^ (ν - 1 - (p.1 : ℕ))

def wt (A : Fin ν × ι →₀ ℕ) : ℕ := A.sum fun p e => e * vw p

def comp (d : ℕ) (P : MvPolynomial (Fin ν × ι) ℂ) : MvPolynomial (Fin ν × ι) ℂ :=
  ∑ A ∈ P.support.filter (fun A => wt A = d), monomial A (AddMonoidAlgebra.coeff P A)

end ReciprocityTheory.PGsh
end
end

section

noncomputable section

open MvPolynomial Matrix Finset

namespace ReciprocityTheory.PGsh

section Cayley

variable (n : ℕ) (R : Type*) [CommRing R]

abbrev cayDet : MvPolynomial (Fin n × Fin n) R :=
  (Matrix.mvPolynomialX (Fin n) (Fin n) R).det

def cayMono (σ : Equiv.Perm (Fin n)) : Module.End R (MvPolynomial (Fin n × Fin n) R) :=
  ((List.finRange n).map fun j => ((pderiv (σ j, j) : Derivation R _ _) :
    MvPolynomial (Fin n × Fin n) R →ₗ[R] MvPolynomial (Fin n × Fin n) R)).prod

def cayOp : Module.End R (MvPolynomial (Fin n × Fin n) R) :=
  ∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ)) • cayMono n R σ

def CayleyStatement : Prop :=
  ∀ (n : ℕ) (R : Type) [CommRing R] (s : ℕ),
    cayOp n R (cayDet n R ^ s) = (∏ k ∈ range n, (s + k)) • cayDet n R ^ (s - 1)

end Cayley

section Tests

variable (R : Type*) [CommRing R]

end Tests

section HW

variable {ν : ℕ} {ι : Type*}

def rowSubst (g : Matrix (Fin ν) (Fin ν) ℂ) :
    MvPolynomial (Fin ν × ι) ℂ →ₐ[ℂ] MvPolynomial (Fin ν × ι) ℂ :=
  aeval fun p => ∑ l, C (g l p.1) * X (l, p.2)


open scoped Classical in
def fischer (P Q : MvPolynomial (Fin ν × ι) ℂ) : ℂ := by
  classical
  exact ∑ A ∈ P.support ∪ Q.support,
    AddMonoidAlgebra.coeff P A * starRingEnd ℂ (AddMonoidAlgebra.coeff Q A) * ((A.prod fun _ e => e.factorial : ℕ) : ℂ)

def IsUpperUnitri (g : Matrix (Fin ν) (Fin ν) ℂ) : Prop :=
  (∀ i, g i i = 1) ∧ ∀ i j, j < i → g i j = 0

end HW

end ReciprocityTheory.PGsh
end
end

section

namespace ReciprocityTheory.PGsh

open MvPowerSeries

noncomputable section

variable {C : Type*} [Field C]

def IsIntV (v : AddValuation C (WithTop ℝ)) (x : C) : Prop := 0 ≤ v x

def MvIsInt (v : AddValuation C (WithTop ℝ)) {σ : Type*} (f : MvPowerSeries σ C) : Prop :=
  ∀ α, IsIntV v (coeff α f)

def PsIsInt (v : AddValuation C (WithTop ℝ)) (f : PowerSeries C) : Prop :=
  ∀ n, IsIntV v (PowerSeries.coeff n f)

theorem v_eq_zero_of_pow_eq_one {v : AddValuation C (WithTop ℝ)} {z : C} {N : ℕ} (hN : N ≠ 0)
    (hz : z ^ N = 1) : v z = 0 := by
  have h1 : N • v z = 0 := by rw [← AddValuation.map_pow, hz, AddValuation.map_one]
  generalize v z = x at h1 ⊢
  induction x using WithTop.recTopCoe with
  | top =>
    exfalso
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hN
    rw [succ_nsmul, WithTop.add_top] at h1
    exact WithTop.top_ne_zero h1
  | coe r =>
    rw [← WithTop.coe_nsmul] at h1
    have h2 : N • r = 0 := WithTop.coe_eq_zero.mp h1
    rw [nsmul_eq_mul] at h2
    rcases mul_eq_zero.mp h2 with h | h
    · exact absurd (Nat.cast_eq_zero.mp h) hN
    · rw [h]; rfl

structure LogFGL (v : AddValuation C (WithTop ℝ)) (d : ℕ) where
  lg : Fin d → MvPowerSeries (Fin d) C
  lg_const : ∀ a, constantCoeff (lg a) = 0
  lg_lin : ∀ a b, coeff (Finsupp.single b 1) (lg a) = if a = b then 1 else 0
  F : Fin d → MvPowerSeries (Fin d ⊕ Fin d) C
  F_int : ∀ a, MvIsInt v (F a)
  F_const : ∀ a, constantCoeff (F a) = 0
  lg_F : ∀ a, subst F (lg a) =
    subst (fun b => X (Sum.inl b)) (lg a) + subst (fun b => X (Sum.inr b)) (lg a)

def IsCurve (v : AddValuation C (WithTop ℝ)) {d : ℕ} (ga : Fin d → PowerSeries C) : Prop :=
  ∀ a, PowerSeries.constantCoeff (ga a) = 0 ∧ PsIsInt v (ga a)

def tangent {d : ℕ} (ga : Fin d → PowerSeries C) : Fin d → C :=
  fun a => PowerSeries.coeff 1 (ga a)

def rescaleCurve {d : ℕ} (x : C) (ga : Fin d → PowerSeries C) : Fin d → PowerSeries C :=
  fun a => PowerSeries.rescale x (ga a)

namespace LogFGL

variable {v : AddValuation C (WithTop ℝ)} {d : ℕ} (G : LogFGL v d)

def lgCurve (ga : Fin d → PowerSeries C) : Fin d → PowerSeries C :=
  fun a => subst ga (G.lg a)

def add (ga gb : Fin d → PowerSeries C) : Fin d → PowerSeries C :=
  fun a => subst (Sum.elim ga gb) (G.F a)

def sumList (G : LogFGL v d) : List (Fin d → PowerSeries C) → (Fin d → PowerSeries C)
  | [] => 0
  | g :: l => G.add g (sumList G l)

def sumF {m : ℕ} (g : Fin m → Fin d → PowerSeries C) : Fin d → PowerSeries C :=
  G.sumList (List.ofFn g)

def nsmulF (G : LogFGL v d) : ℕ → (Fin d → PowerSeries C) → (Fin d → PowerSeries C)
  | 0, _ => 0
  | n + 1, ga => G.add ga (nsmulF G n ga)

def lc (p : ℕ) (ga : Fin d → PowerSeries C) (n : ℕ) : Fin d → C :=
  fun a => PowerSeries.coeff (p ^ n) (G.lgCurve ga a)

def IsPTypical (p : ℕ) (ga : Fin d → PowerSeries C) : Prop :=
  ∀ a m, (∀ n, m ≠ p ^ n) → PowerSeries.coeff m (G.lgCurve ga a) = 0

def IsOfType (p : ℕ) {h : ℕ} (ty : Fin d → ZMod h) (i : ZMod h)
    (ga : Fin d → PowerSeries C) : Prop :=
  G.IsPTypical p ga ∧ ∀ (n : ℕ) a, ty a ≠ i + (n : ZMod h) → G.lc p ga n a = 0

end LogFGL

structure MuAction {v : AddValuation C (WithTop ℝ)} {d : ℕ} (G : LogFGL v d) (p h : ℕ)
    (ty : Fin d → ZMod h) where
  mul : C → Fin d → MvPowerSeries (Fin d) C
  mul_int : ∀ z, z ^ (p ^ h - 1) = 1 → ∀ a, MvIsInt v (mul z a)
  mul_const : ∀ z a, constantCoeff (mul z a) = 0
  lg_mul : ∀ z, z ^ (p ^ h - 1) = 1 → ∀ a,
    subst (mul z) (G.lg a) = (z ^ (p ^ (ty a).val)) • G.lg a

def expComp [CharZero C] (Ω : C) (lg : PowerSeries C) : PowerSeries C :=
  PowerSeries.mk fun m => ∑ n ∈ Finset.range (m + 1),
    Ω ^ n / (n.factorial : C) * PowerSeries.coeff m (lg ^ n)

def lgSum {d M : ℕ} (p : ℕ) (c : Fin d → ℕ → Fin d → C)
    (t : Fin d → MvPowerSeries (Fin M) C) (b : Fin d) : MvPowerSeries (Fin M) C :=
  fun α => ∑ n ∈ Finset.range (Finsupp.degree α + 1), ∑ a, c a n b * coeff α (t a ^ (p ^ n))

def OrdGe (v : AddValuation C (WithTop ℝ)) {M : ℕ} (ρ : Fin M → ℝ) (g : MvPowerSeries (Fin M) C)
    (r : ℝ) : Prop :=
  ∀ α : Fin M →₀ ℕ, (((r - ∑ m, ρ m * α m : ℝ)) : WithTop ℝ) ≤ v (coeff α g)

def radius (p : ℕ) (k : ℤ) : ℝ := (1 + (p : ℝ) ^ (-(2 * k + 1))) / ((p : ℝ) ^ 2 - 1)

end

end ReciprocityTheory.PGsh
end

section

noncomputable section

open Polynomial Matrix
open scoped TensorProduct

namespace ReciprocityTheory.PGsh

def stdJ (D : Type*) [CommRing D] (g : ℕ) : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) D :=
  Matrix.fromBlocks 0 (-1) 1 0

def ExistsPointLeviLogNormSqPos : Prop :=
  ∀ (D : Type) [CommRing D] [IsDomain D] (g : ℕ)
    (E Φ : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) D) (c : D),
    Eᵀ = -E → (∀ i, E i i = 0) → IsUnit E.det → c ≠ 0 →
    Φᵀ * stdJ D g * Φ = c • E →
    let Ht : Matrix (Fin g) (Fin g ⊕ Fin g) D := Φ.submatrix Sum.inl id
    let Bt : Matrix (Fin g) (Fin g ⊕ Fin g) D := Φ.submatrix Sum.inr id
    let hb : Matrix (Fin g ⊕ Fin g) (Fin g) D := (Eᵀ)⁻¹ * Htᵀ
    let ι := algebraMap D (FractionRing D)
    (∀ f : Fin g → D, ∃ t : Fin g ⊕ Fin g → D, Ht *ᵥ t = c • f) ∧
    Ht * hb = 0 ∧ Bt * hb = c • (1 : Matrix (Fin g) (Fin g) D) ∧ hbᵀ * E * hb = 0 ∧
    (∀ t : Fin g ⊕ Fin g → FractionRing D, Ht.map ι *ᵥ t = 0 →
      ∃ x : Fin g → FractionRing D, hb.map ι *ᵥ x = t) ∧
    (∀ x : Fin g → FractionRing D, (∃ w : Fin g ⊕ Fin g → D, hb.map ι *ᵥ x = ι ∘ w) →
      ∃ y : Fin g → D, c • x = ι ∘ y)

abbrev extModR (R K V : Type*) [CommRing R] [Field K] [Algebra R K] [AddCommGroup V]
    [Module K V] : Module R (ExteriorAlgebra K V) :=
  Module.compHom _ (algebraMap R K)

attribute [local instance] extModR

def TruncatedPolynomialStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (k H : Type) [Field k] [CharP k p] [CommRing H] [HopfAlgebra k H]
    [FiniteDimensional k H] (d : ℕ) (x : Fin d → H),
    (∀ f ∈ RingHom.ker (Bialgebra.counitAlgHom k H), f ^ p = 0) →
    (∀ i, x i ∈ RingHom.ker (Bialgebra.counitAlgHom k H)) →
    (∀ y ∈ RingHom.ker (Bialgebra.counitAlgHom k H), ∃ l : Fin d → k,
      y - ∑ i, l i • x i ∈ RingHom.ker (Bialgebra.counitAlgHom k H) ^ 2) →
    (∀ l : Fin d → k, ∑ i, l i • x i ∈ RingHom.ker (Bialgebra.counitAlgHom k H) ^ 2 → l = 0) →
    Function.Surjective (MvPolynomial.aeval (R := k) x) ∧
      RingHom.ker (MvPolynomial.aeval (R := k) x) =
        Ideal.span (Set.range fun i => (MvPolynomial.X i : MvPolynomial (Fin d) k) ^ p)

end ReciprocityTheory.PGsh
end
end
