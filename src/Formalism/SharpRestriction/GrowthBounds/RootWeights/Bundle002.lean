module

public import Formalism.SharpRestriction.GrowthBounds.ObjPol
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
import Formalism.SharpRestriction.GrowthBounds.CovariantDegrees

@[expose] public section

section

noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

private theorem laurent_mul_coeff_of_unique_decomp {B : Type*} [CommRing B] (f g : LaurentPolynomial B) (a b : ℤ)
    (h : ∀ k₁ ∈ f.coeff.support, ∀ k₂ ∈ g.coeff.support, k₁ + k₂ = a + b → k₁ = a ∧ k₂ = b) :
    (f * g).coeff (a + b) = f.coeff a * g.coeff b := by
  classical
  rw [AddMonoidAlgebra.coeff_mul, Finsupp.sum, Finset.sum_eq_single a]
  · rw [Finsupp.sum, Finset.sum_eq_single b]
    · simp
    · intro k₂ hk₂ hne
      by_cases ha : a ∈ f.coeff.support
      · rw [if_neg]; intro he; exact hne (h a ha k₂ hk₂ he).2
      · have : f.coeff a = 0 := by simpa using ha
        simp [this]
    · intro hb
      have : g.coeff b = 0 := by simpa using hb
      simp [this]
  · intro k₁ hk₁ hne
    apply Finset.sum_eq_zero
    intro k₂ hk₂
    dsimp only; rw [if_neg]; intro he; exact hne (h k₁ hk₁ k₂ hk₂ he).1
  · intro ha
    have : f.coeff a = 0 := by simpa using ha
    simp [this]

theorem mul_laurent_inf {B : Type*} [CommRing B] [IsDomain B] (f g : LaurentPolynomial B) :
    ((f * g).coeff.support.inf fun k => (k : WithTop ℤ)) =
      (f.coeff.support.inf fun k => (k : WithTop ℤ)) + (g.coeff.support.inf fun k => (k : WithTop ℤ)) := by
  classical
  apply le_antisymm
  · rcases f.coeff.support.eq_empty_or_nonempty with hf | hf
    · rw [hf, Finset.inf_empty, top_add]; exact le_top
    rcases g.coeff.support.eq_empty_or_nonempty with hg | hg
    · rw [hg, Finset.inf_empty, add_top]; exact le_top
    have hc := laurent_mul_coeff_of_unique_decomp f g (f.coeff.support.min' hf) (g.coeff.support.min' hg) (by
      intro k₁ hk₁ k₂ hk₂ he
      have h1 := Finset.min'_le _ _ hk₁
      have h2 := Finset.min'_le _ _ hk₂
      omega)
    have hmem : f.coeff.support.min' hf + g.coeff.support.min' hg ∈ (f * g).coeff.support := by
      rw [Finsupp.mem_support_iff, hc]
      exact mul_ne_zero (Finsupp.mem_support_iff.mp (Finset.min'_mem _ hf))
        (Finsupp.mem_support_iff.mp (Finset.min'_mem _ hg))
    calc _ ≤ (((f.coeff.support.min' hf + g.coeff.support.min' hg : ℤ)) : WithTop ℤ) := Finset.inf_le hmem
      _ = ((f.coeff.support.min' hf : ℤ) : WithTop ℤ) + ((g.coeff.support.min' hg : ℤ) : WithTop ℤ) :=
        WithTop.coe_add _ _
      _ = _ := by simp only [Finset.min'_eq_inf', Finset.coe_inf']; rfl
  · exact AddMonoidAlgebra.le_infDegree_mul { toFun := fun k : ℤ => (k : WithTop ℤ), map_add' := fun a b => WithTop.coe_add a b } f g

theorem mul_laurent_sup {B : Type*} [CommRing B] [IsDomain B] (f g : LaurentPolynomial B) :
    ((f * g).coeff.support.sup fun k => (k : WithBot ℤ)) =
      (f.coeff.support.sup fun k => (k : WithBot ℤ)) + (g.coeff.support.sup fun k => (k : WithBot ℤ)) := by
  classical
  apply le_antisymm
  · exact AddMonoidAlgebra.supDegree_mul_le (D := fun k : ℤ => (k : WithBot ℤ)) (fun a b => WithBot.coe_add a b) (p := f) (q := g)
  · rcases f.coeff.support.eq_empty_or_nonempty with hf | hf
    · rw [hf, Finset.sup_empty, WithBot.bot_add]; exact bot_le
    rcases g.coeff.support.eq_empty_or_nonempty with hg | hg
    · rw [hg, Finset.sup_empty, WithBot.add_bot]; exact bot_le
    have hc := laurent_mul_coeff_of_unique_decomp f g (f.coeff.support.max' hf) (g.coeff.support.max' hg) (by
      intro k₁ hk₁ k₂ hk₂ he
      have h1 := Finset.le_max' _ _ hk₁
      have h2 := Finset.le_max' _ _ hk₂
      omega)
    have hmem : f.coeff.support.max' hf + g.coeff.support.max' hg ∈ (f * g).coeff.support := by
      rw [Finsupp.mem_support_iff, hc]
      exact mul_ne_zero (Finsupp.mem_support_iff.mp (Finset.max'_mem _ hf))
        (Finsupp.mem_support_iff.mp (Finset.max'_mem _ hg))
    calc _ = ((f.coeff.support.max' hf : ℤ) : WithBot ℤ) + ((g.coeff.support.max' hg : ℤ) : WithBot ℤ) := by
          simp only [Finset.max'_eq_sup', Finset.coe_sup']; rfl
      _ = (((f.coeff.support.max' hf + g.coeff.support.max' hg : ℤ)) : WithBot ℤ) := (WithBot.coe_add _ _).symm
      _ ≤ _ := Finset.le_sup (f := fun k : ℤ => ((k : ℤ) : WithBot ℤ)) (b := f.coeff.support.max' hf + g.coeff.support.max' hg) hmem

def mul_Phi (σ A : Type*) [CommRing A] :
    MvPolynomial σ (LaurentPolynomial A) →+* LaurentPolynomial (MvPolynomial σ A) :=
  MvPolynomial.eval₂Hom (AddMonoidAlgebra.mapRingHom ℤ (C : A →+* MvPolynomial σ A))
    (fun i => LaurentPolynomial.C (X i))

private theorem laurent_mul_C_coeff {B : Type*} [CommRing B] (y : LaurentPolynomial B) (q : B) (k : ℤ) :
    (y * LaurentPolynomial.C q).coeff k = y.coeff k * q := by
  have hCc : ∀ j : ℤ, (LaurentPolynomial.C q).coeff j = if j = 0 then q else 0 := by
    intro j
    simp [LaurentPolynomial.C_apply, Finsupp.single_apply, eq_comm]
  have h := laurent_mul_coeff_of_unique_decomp y (LaurentPolynomial.C q) k 0 (by
    intro k₁ _ k₂ hk₂ he
    have : k₂ = 0 := by
      by_contra hne
      rw [Finsupp.mem_support_iff, hCc, if_neg hne] at hk₂
      exact hk₂ rfl
    omega)
  rw [add_zero] at h
  rw [h, hCc, if_pos rfl]

theorem mul_Phi_coeff {σ A : Type*} [CommRing A] (P : MvPolynomial σ (LaurentPolynomial A)) (m : σ →₀ ℕ) (k : ℤ) :
    AddMonoidAlgebra.coeff ((mul_Phi σ A P).coeff k) m = (AddMonoidAlgebra.coeff P m).coeff k := by
  classical
  induction P using MvPolynomial.induction_on' with
  | monomial m' c =>
    simp only [mul_Phi, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_monomial]
    have hprod : (m'.prod fun i e => (LaurentPolynomial.C (X i) : LaurentPolynomial (MvPolynomial σ A)) ^ e) =
        LaurentPolynomial.C (monomial m' 1) := by
      rw [MvPolynomial.monomial_eq, MvPolynomial.C_1, one_mul, map_finsuppProd]
      simp [map_pow]
    rw [hprod, laurent_mul_C_coeff]
    have hmap : (AddMonoidAlgebra.mapRingHom ℤ (C : A →+* MvPolynomial σ A) c).coeff k = C (c.coeff k) := by
      simp [AddMonoidAlgebra.mapRingHom]
    rw [hmap, MvPolynomial.C_mul_monomial, mul_one, MvPolynomial.coeff_monomial, MvPolynomial.coeff_monomial]
    split_ifs <;> simp
  | add p q hp hq => simp [map_add (f := _), hp, hq]

def mul_degs {σ A : Type*} [CommRing A] (P : MvPolynomial σ (LaurentPolynomial A)) : Finset ℤ :=
  P.support.biUnion fun m => (P.coeff m).coeff.support

theorem mul_degs_eq {σ A : Type*} [CommRing A] (P : MvPolynomial σ (LaurentPolynomial A)) :
    mul_degs P = (mul_Phi σ A P).coeff.support := by
  classical
  ext k
  simp only [mul_degs, Finset.mem_biUnion, MvPolynomial.mem_support_iff, Finsupp.mem_support_iff]
  constructor
  · rintro ⟨m, -, hm⟩ h
    apply hm
    rw [← mul_Phi_coeff, h]
    simp
  · intro h
    obtain ⟨m, hm⟩ : ∃ m, AddMonoidAlgebra.coeff ((mul_Phi σ A P).coeff k) m ≠ 0 := by
      by_contra hc
      push_neg at hc
      exact h (by ext m; simpa using hc m)
    rw [mul_Phi_coeff] at hm
    exact ⟨m, fun h0 => hm (by rw [h0]; simp), hm⟩

instance mul_domGL (R : Type*) [Field R] (n : ℕ) : IsDomain (GLCoord R n) :=
  IsLocalization.isDomain_localization (powers_le_nonZeroDivisors_of_noZeroDivisors
    (Matrix.det_mvPolynomialX_ne_zero (Fin n) R))

theorem mul_valS_mul {R : Type*} [Field R] {ι : Type*} {n : ℕ} [NeZero n] (LL : Letters ι) (S : Set ι)
    (F G : MvPolynomial (ι × Fin n) R) : valS LL S (F * G) = valS LL S F + valS LL S G := by
  have key : ∀ H : MvPolynomial (ι × Fin n) R, valS LL S H =
      ((mul_Phi _ _ (twistSub LL S (lastIdx n) H)).coeff.support.inf fun k => (k : WithTop ℤ)) := by
    intro H; rw [← mul_degs_eq]; rfl
  rw [key, key, key, map_mul, map_mul, mul_laurent_inf]

theorem mul_lam1S_mul {R : Type*} [Field R] {ι : Type*} {n : ℕ} [NeZero n] (LL : Letters ι) (S : Set ι)
    (F G : MvPolynomial (ι × Fin n) R) : lam1S LL S (F * G) = lam1S LL S F + lam1S LL S G := by
  have key : ∀ H : MvPolynomial (ι × Fin n) R, lam1S LL S H =
      ((mul_Phi _ _ (twistSub LL S (0 : Fin n) H)).coeff.support.sup fun k => (k : WithBot ℤ)) := by
    intro H; rw [← mul_degs_eq]; rfl
  rw [key, key, key, map_mul, map_mul, mul_laurent_sup]

end Formalism.MainNotions.G.GLWeightTheory
end
end

section

noncomputable section

open Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

section Arith

variable {p : ℕ} {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

theorem natCast_unit_of_coprime (S : UniformizedDVR p O) {c : ℕ} (hc : Nat.Coprime c p) : IsUnit (c : O) := by
  by_contra h
  have hc' : (c : O) ∈ IsLocalRing.maximalIdeal O :=
    (IsLocalRing.mem_maximalIdeal _).2 (mem_nonunits_iff.2 h)
  have key : ((c.gcd p : ℕ) : ℤ) = (c : ℤ) * c.gcdA p + (p : ℤ) * c.gcdB p := Nat.gcd_eq_gcd_ab c p
  rw [Nat.Coprime.gcd_eq_one hc, Nat.cast_one] at key
  have key' : (1 : O) = (c : O) * ((c.gcdA p : ℤ) : O) + (p : O) * ((c.gcdB p : ℤ) : O) := by
    have := congrArg (Int.cast : ℤ → O) key
    push_cast at this
    exact this
  have h1 : (1 : O) ∈ IsLocalRing.maximalIdeal O := by
    rw [key']
    exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ hc') (Ideal.mul_mem_right _ _ S.p_mem)
  exact (IsLocalRing.maximalIdeal.isMaximal O).ne_top ((Ideal.eq_top_iff_one _).2 h1)

theorem dvr_charZero_of_prime (S : UniformizedDVR p O) (hp : p.Prime) : CharZero O := by
  refine charZero_of_inj_zero (fun n hn => ?_)
  by_contra hne
  obtain ⟨e, m, hm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hne p hp.ne_one
  rw [Nat.cast_mul, Nat.cast_pow] at hn
  have hpe : (p : O) ^ e ≠ 0 := pow_ne_zero _ S.p_ne
  have hm0 : (m : O) = 0 := (mul_eq_zero.1 hn).resolve_left hpe
  have hu := natCast_unit_of_coprime S ((Nat.Prime.coprime_iff_not_dvd hp).2 hm).symm
  rw [hm0] at hu
  exact not_isUnit_zero hu

theorem dvr_fraction_field_charZero_prime (S : UniformizedDVR p O) (hp : p.Prime) : CharZero (KK O) := by
  haveI := dvr_charZero_of_prime S hp
  refine charZero_of_inj_zero (fun n hn => ?_)
  have h1 : algebraMap O (KK O) (n : O) = algebraMap O (KK O) 0 := by
    rw [map_natCast, map_zero]; exact hn
  have h2 : (n : O) = 0 := IsFractionRing.injective O (KK O) h1
  exact_mod_cast h2

end Arith

section Order

end Order

end Formalism.MainNotions.G.GLWeightTheory
end
end

section

noncomputable section

open Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

def highestWeightVectors {n : ℕ} {K V : Type*} [Field K] [AddCommGroup V] [Module K V] (E : GLOps n K V) (lam : Fin n → ℤ) :
    Submodule K V :=
  weightSp E lam ⊓ ⨅ a : Fin n, ⨅ b : Fin n, ⨅ (_ : a < b), LinearMap.ker (E a b)

def generatedSubrep {n : ℕ} {K V : Type*} [Field K] [AddCommGroup V] [Module K V] (E : GLOps n K V) (h : V) :
    Submodule K V :=
  Submodule.span K {x | ∃ u ∈ Umon E, x = u h}

def IsotypicProjectorFixedMem : Prop :=
  ∀ (K V : Type) [Field K] [CharZero K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] (n : ℕ)
    (E : GLOps n K V), IsGLRep E → ∀ (lam : Fin n → ℤ) (e : Module.End K V), IsIsoProj E lam e →
      ∀ Y : V, e Y = Y → Y ∈ isoSub E lam

def GeneratedMultipleOfHWV : Prop :=
  ∀ (K V : Type) [Field K] [AddCommGroup V] [Module K V] (n : ℕ)
    (E : GLOps n K V), IsGLRep E → ∀ (lam : Fin n → ℤ) (h : V), h ∈ highestWeightVectors E lam →
      generatedSubrep E h ≤ Submodule.span K {h} ⊔ ⨆ mu ∈ {mu : Fin n → ℤ | mu ≠ lam}, (weightSp E mu ⊓ generatedSubrep E h)

def DualLatticeDivisibility : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (V : Type) [AddCommGroup V] [Module (KK O) V] [Module O V] [IsScalarTower O (KK O) V]
    [FiniteDimensional (KK O) V] (M : Submodule O V), M.FG → MQ (K := KK O) M = ⊤ →
    ∀ (t : KK O) (z : V),
      (∀ f : V →ₗ[KK O] KK O, (∀ x ∈ M, ∃ o : O, f x = algebraMap O (KK O) o) →
        ∃ o : O, f z = t * algebraMap O (KK O) o) →
      ∃ m ∈ M, z = t • m

def LatticeSubspaceBasis : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (V : Type) [AddCommGroup V] [Module (KK O) V] [Module O V] [IsScalarTower O (KK O) V]
    [FiniteDimensional (KK O) V] (M : Submodule O V), M.FG → MQ (K := KK O) M = ⊤ →
    ∀ H : Submodule (KK O) V, ∃ (k : ℕ) (h : Fin k → V), (∀ j, h j ∈ M ∧ h j ∈ H) ∧
      LinearIndependent (KK O) h ∧ H ≤ Submodule.span (KK O) (Set.range h) ∧
      ∀ x ∈ M, x ∈ H → ∃ o : Fin k → O, x = ∑ j, o j • h j

def GeneratedLatticeCorollary : Prop :=
  ∀ (p n' : ℕ) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (_S : UniformizedDVR p O),
    AdmissibleDVR p n' O →
    ∀ (n : ℕ) [NeZero n] (V : Type) [AddCommGroup V] [Module (KK O) V] [Module O V]
      [IsScalarTower O (KK O) V] [FiniteDimensional (KK O) V] (E : GLOps n (KK O) V), IsGLRep E →
      ∀ M : Submodule O V, UZLattice E M →
      ∀ lam : Fin n → ℤ, Dominant lam →
      ∀ π : Module.End (KK O) V, IsWtProj E lam π →
      ∀ h : V, h ∈ M → h ∈ highestWeightVectors E lam → h ≠ 0 →
      ∀ (c : ℤ) (y : V), y ∈ generatedSubrep E h →
        (∀ u ∈ UZmon E, ∃ o : O, π (u y) = ((p : KK O) ^ c * algebraMap O (KK O) o) • h) →
        ∃ m ∈ M, y = ((p : KK O) ^ (c - ((N0 n * deF p n (ellWt lam) : ℕ) : ℤ))) • m

end Formalism.MainNotions.G.GLWeightTheory
end
end

section

noncomputable section

open Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

section defs
variable {n : ℕ} {K : Type} [Field K] {V V' : Type} [AddCommGroup V] [Module K V] [AddCommGroup V'] [Module K V']

def IsSubrepresentation (E : GLOps n K V) (W : Submodule K V) : Prop := ∀ a b, ∀ x ∈ W, E a b x ∈ W

def IsEquivariantMap (E : GLOps n K V) (E' : GLOps n K V') (T : V →ₗ[K] V') : Prop := ∀ a b x, T (E a b x) = E' a b (T x)

def restrictRepresentation (E : GLOps n K V) (W : Submodule K V) (h : IsSubrepresentation E W) : GLOps n K W :=
  fun a b => (E a b).restrict (h a b)

def homRepresentation (E : GLOps n K V) (E' : GLOps n K V') : GLOps n K (V →ₗ[K] V') :=
  fun a b => LinearMap.llcomp K V V' V' (E' a b) - LinearMap.lcomp K V' (E a b)

def cyclicSubmodule (E : GLOps n K V) (v : V) : Submodule K V := Submodule.span K {x | ∃ u ∈ Umon E, x = u v}

end defs

def RestrictionIsRepresentation : Prop :=
  ∀ (n : ℕ) (K V : Type) [Field K] [CharZero K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (E : GLOps n K V), IsGLRep E → ∀ (W : Submodule K V) (h : IsSubrepresentation E W), IsGLRep (restrictRepresentation E W h)

def HomSpaceIsRepresentation : Prop :=
  ∀ (n : ℕ) (K V V' : Type) [Field K] [CharZero K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [AddCommGroup V'] [Module K V'] [FiniteDimensional K V'] (E : GLOps n K V) (E' : GLOps n K V'),
    IsGLRep E → IsGLRep E' → IsGLRep (homRepresentation E E')

def IsotypicSubmodulesSpanTop : Prop :=
  ∀ (n : ℕ) (K V : Type) [Field K] [CharZero K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (E : GLOps n K V), IsGLRep E → (⨆ mu, isoSub E mu) = ⊤

def InvariantProjectionExists : Prop :=
  ∀ (n : ℕ) (K V : Type) [Field K] [CharZero K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (E : GLOps n K V), IsGLRep E → ∃ P : Module.End K V, IsInvProj E P

def EquivariantCommutesInvariantProjection : Prop :=
  ∀ (n : ℕ) (K V V' : Type) [Field K] [CharZero K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [AddCommGroup V'] [Module K V'] [FiniteDimensional K V'] (E : GLOps n K V) (E' : GLOps n K V'),
    IsGLRep E → IsGLRep E' → ∀ T : V →ₗ[K] V', IsEquivariantMap E E' T →
    ∀ (P : Module.End K V) (P' : Module.End K V'), IsInvProj E P → IsInvProj E' P' → ∀ x, T (P x) = P' (T x)

def OperatorsKillInvariantProjection : Prop :=
  ∀ (n : ℕ) (K V : Type) [Field K] [CharZero K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (E : GLOps n K V), IsGLRep E → ∀ P : Module.End K V, IsInvProj E P → ∀ x a b, E a b (P x) = 0

def IsotypicProjectorTraceFormula : Prop :=
  ∀ (n : ℕ) (K W : Type) [Field K] [CharZero K] [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    (E : GLOps n K W), IsGLRep E → ∀ (lam : Fin n → ℤ) (e : Module.End K W), IsIsoProj E lam e →
    ∀ v0, IsHWV E lam v0 → ∀ (hL : IsSubrepresentation E (cyclicSubmodule E v0))
      (P : Module.End K (cyclicSubmodule E v0 →ₗ[K] W)), IsInvProj (homRepresentation (restrictRepresentation E _ hL) E) P →
      ∀ (ι : Type) [Fintype ι] (b : Module.Basis ι K (cyclicSubmodule E v0)) (m : W),
        (Fintype.card ι : K) • ∑ i, P ((b.coord i).smulRight m) (b i) = e m

section lat
variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  {W : Type} [AddCommGroup W] [Module (KK O) W] [Module O W] [IsScalarTower O (KK O) W]

def homLattice (M : Submodule O W) (L : Submodule (KK O) W) : Submodule O (L →ₗ[KK O] W) where
  carrier := {f | ∀ x : L, (x : W) ∈ M → f x ∈ M}
  zero_mem' := fun _ _ => by simp
  add_mem' := fun hf hg x hx => by simpa using M.add_mem (hf x hx) (hg x hx)
  smul_mem' := fun c f hf x hx => by simpa using M.smul_mem c (hf x hx)

end lat

def LatticeAdaptedBasisExists : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (W : Type) [AddCommGroup W] [Module (KK O) W] [Module O W] [IsScalarTower O (KK O) W]
    [FiniteDimensional (KK O) W] (M : Submodule O W), M.FG → MQ (K := KK O) M = ⊤ →
    ∀ L : Submodule (KK O) W, ∃ (d : ℕ) (b : Module.Basis (Fin d) (KK O) L), (∀ i, ((b i : L) : W) ∈ M) ∧
      ∀ x : L, (x : W) ∈ M → ∀ i, ∃ o : O, b.coord i x = algebraMap O (KK O) o

def HomLatticeDividedPowerStable : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero (KK O)]
    (n : ℕ) (W : Type) [AddCommGroup W] [Module (KK O) W] [Module O W] [IsScalarTower O (KK O) W]
    [FiniteDimensional (KK O) W] (E : GLOps n (KK O) W), IsGLRep E →
    ∀ M : Submodule O W, UZLattice E M → MQ (K := KK O) M = ⊤ →
    ∀ (L : Submodule (KK O) W) (hL : IsSubrepresentation E L),
      UZLattice (homRepresentation (restrictRepresentation E L hL) E) (homLattice M L) ∧ MQ (K := KK O) (homLattice M L) = ⊤

end Formalism.MainNotions.G.GLWeightTheory
end
end

section

noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

section ops

variable {K : Type} [Field K] {σ : Type}

def polarizationOperator (K : Type) [Field K] {σ : Type} (v w : σ) : Module.End K (MvPolynomial σ K) :=
  (LinearMap.mulLeft K (X v)) ∘ₗ (pderiv w).toLinearMap

theorem polarization_monomial (v w : σ) (m : σ →₀ ℕ) (c : K) :
    polarizationOperator K v w (monomial m c) = monomial (m - Finsupp.single w 1 + Finsupp.single v 1) (c * (m w : K)) := by
  show X v * pderiv w (monomial m c) = _
  rw [pderiv_monomial, X, monomial_mul, one_mul, add_comm (Finsupp.single v 1)]

theorem polarization_commute (v w v' w' : σ) (h1 : w ≠ v') (h2 : w ≠ w') (h3 : w' ≠ v) :
    Commute (polarizationOperator K v w) (polarizationOperator K v' w') := by
  show polarizationOperator K v w * polarizationOperator K v' w' = polarizationOperator K v' w' * polarizationOperator K v w
  refine LinearMap.ext fun f => ?_
  induction f using MvPolynomial.induction_on' with
  | monomial m c =>
    rw [Module.End.mul_apply, Module.End.mul_apply, polarization_monomial, polarization_monomial,
      polarization_monomial, polarization_monomial]
    have e1 : (m - Finsupp.single w' 1 + Finsupp.single v' 1 : σ →₀ ℕ) w = m w := by
      simp [Finsupp.single_apply, h1, h2, Ne.symm h1, Ne.symm h2]
    have e2 : (m - Finsupp.single w 1 + Finsupp.single v 1 : σ →₀ ℕ) w' = m w' := by
      simp [Finsupp.single_apply, h3, Ne.symm h2, Ne.symm h3, h2]
    have hexp : (m - Finsupp.single w' 1 + Finsupp.single v' 1 - Finsupp.single w 1
        + Finsupp.single v 1 : σ →₀ ℕ) =
        m - Finsupp.single w 1 + Finsupp.single v 1 - Finsupp.single w' 1 + Finsupp.single v' 1 := by
      ext x
      simp only [Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_apply]
      by_cases a1 : w = x <;> by_cases a2 : w' = x <;> by_cases a3 : v = x <;>
        by_cases a4 : v' = x <;> (try subst_vars) <;> (try simp_all) <;> omega
    rw [e1, e2, hexp]
    congr 1
    ring
  | add p q hp hq =>
    rw [map_add (f := _), map_add (f := _), hp, hq]

end ops

section fact

variable {σ : Type}

theorem exponent_factorial_ne_zero_of (m : σ →₀ ℕ) : expFact m ≠ 0 := by
  unfold expFact Finsupp.prod
  exact Finset.prod_ne_zero_iff.mpr fun _ _ => Nat.factorial_ne_zero _

end fact

end Formalism.MainNotions.G.GLWeightTheory
end
end
