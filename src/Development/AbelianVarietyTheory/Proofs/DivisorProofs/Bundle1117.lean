module

public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle108
public import Formalism.LocalToGlobal.Divisibility.ProjLemmas
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.Bundle002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1083
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1085
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1087
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle031
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle001
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.ComplexMultiplicationJPremises
import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle029
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.EqOfAgreeOnTorsion
import Development.AbelianVarietyTheory.PublishedTheorems.AbelianLaws.PrincipalPolarisationOneSection
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle007
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueTorusCompat
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.DiagZEqNegAddY
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle005
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.StTransl

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links MeasureTheory
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SchurPolar

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar}

theorem exists_of_diag (M : DSModel V S) (μ : Measure (GA D V)) (𝓕 : Set (GA D V)) (T T' : MMap M)
    {a b s t : ℂ} (ha : IsMultIP M μ 𝓕 T T a) (hb : IsMultIP M μ 𝓕 T' T' b)
    (hs : IsMultIP M μ 𝓕 (T + T') (T + T') s)
    (ht : IsMultIP M μ 𝓕 (T + Complex.I • T') (T + Complex.I • T') t) :
    IsMultIP M μ 𝓕 T T' ((1 / 2) * ((s - a - b) - Complex.I * (t - a - b))) := by
  intro v v'
  obtain ⟨ia, ea⟩ := ha v v'
  obtain ⟨ib, eb⟩ := hb v v'
  obtain ⟨is, es⟩ := hs v v'
  obtain ⟨it, et⟩ := ht v v'
  have e : (fun g => star (T v g) * T' v' g) =
      fun g => (1 / 2 : ℂ) * ((star ((T + T') v g) * (T + T') v' g - star (T v g) * T v' g
        - star (T' v g) * T' v' g) - Complex.I * (star ((T + Complex.I • T') v g) * (T + Complex.I • T') v' g
        - star (T v g) * T v' g - star (T' v g) * T' v' g)) := by
    funext g
    show _ = (1 / 2 : ℂ) * ((star (T v g + T' v g) * (T v' g + T' v' g) - star (T v g) * T v' g
        - star (T' v g) * T' v' g) - Complex.I * (star (T v g + Complex.I * T' v g) * (T v' g + Complex.I * T' v' g)
        - star (T v g) * T v' g - star (T' v g) * T' v' g))
    have hI : star Complex.I = - Complex.I := by simp
    rw [star_add, star_add, star_mul, hI]
    have h2 := Complex.I_mul_I
    linear_combination (1 / 2 : ℂ) * (star (T v g) * T' v' g - star (T' v g) * T v' g
      - Complex.I * star (T' v g) * T' v' g) * h2
  have i1 : Integrable (fun g => star ((T + T') v g) * (T + T') v' g - star (T v g) * T v' g) (μ.restrict 𝓕) :=
    is.sub ia
  have i2 : Integrable (fun g => star ((T + T') v g) * (T + T') v' g - star (T v g) * T v' g
      - star (T' v g) * T' v' g) (μ.restrict 𝓕) := i1.sub ib
  have i3 : Integrable (fun g => star ((T + Complex.I • T') v g) * (T + Complex.I • T') v' g
      - star (T v g) * T v' g) (μ.restrict 𝓕) := it.sub ia
  have i4 : Integrable (fun g => star ((T + Complex.I • T') v g) * (T + Complex.I • T') v' g
      - star (T v g) * T v' g - star (T' v g) * T' v' g) (μ.restrict 𝓕) := i3.sub ib
  have i5 := i4.const_mul Complex.I
  rw [e]
  refine ⟨(i2.sub i5).const_mul _, ?_⟩
  rw [integral_const_mul, integral_sub i2 i5, integral_const_mul, integral_sub i1 ib, integral_sub i3 ib,
    integral_sub is ia, integral_sub it ia, ea, eb, es, et]
  ring

theorem isMultiplicityInner_inner : ∀ {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (μ : Measure (GA D V)) (𝓕 : Set (GA D V)) (HM : HMod (MMap M)) (U : Submodule ℂ (MMap M)), HM.Is U (ipM M μ 𝓕) → ∀ x y : HM.H, IsMultIP M μ 𝓕 (HM.e x) (HM.e y) (inner ℂ x y) := by
  intro D V S M μ 𝓕 HM U h x y
  have hip := h.2.2
  have hd : ∀ z : HM.H, ∃ c, IsMultIP M μ 𝓕 (HM.e z) (HM.e z) c := by
    intro z
    by_cases hz : z = 0
    · refine ⟨0, fun v v' => ?_⟩
      subst hz
      simp
    · by_contra hn
      have := hip z z
      unfold ipM at this
      rw [dite_eq_right hn] at this
      exact hz (inner_self_eq_zero.1 this)
  rw [hip]
  apply ipM_spec
  obtain ⟨a, ha⟩ := hd x
  obtain ⟨b, hb⟩ := hd y
  obtain ⟨s, hs⟩ := hd (x + y)
  obtain ⟨t, ht⟩ := hd (x + Complex.I • y)
  rw [map_add (f := _)] at hs ht
  rw [map_smul] at ht
  exact ⟨_, exists_of_diag M μ 𝓕 _ _ ha hb hs ht⟩

end GlobalTheory.SchurPolar
end

section

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LevelRankR

theorem exists_lift_of_mem_level : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), ∀ (i : Fin D.R.m) (P : LevelP R.Pg D.R.r ℂ) (κ' : GA D (Wc D i)), κ' ∈ levG (Wc D i) (R.βW i) (R.datWp i P) → ∃ g0 : P.H, IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) g0.1 κ' ∧ levChi (Wc D i) (R.βW i) (R.datWp i P) κ' = ((P.chi g0 : ℂˣ) : ℂ) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R i P κ' hκ
  have hp : rTup (R.βW i) (R.datWp i P) (finE (Wc D i) κ') ∈ P.H := hκ.2.2
  refine ⟨⟨_, hp⟩, ⟨hκ.1, hκ.2.1, rfl⟩, ?_⟩
  have h2 : ext1 (R.datWp i P).P.H (R.datWp i P).P.chi
      (rTup (R.βW i) (R.datWp i P) (finE (Wc D i) κ')) = P.chi ⟨_, hp⟩ := extendOne_of_mem _ hp
  unfold levChi levFn
  rw [h2]
  have hs : (R.datWp i P).s = 0 := rfl
  have hQ : (R.datWp i P).Q = ∅ := rfl
  rw [hs, hQ]
  simp

end GlobalTheory.LevelRankR

end
end

section

open Matrix Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.IndefR.Datum
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FrameEquiv

open Formalism.IndefR.Links Formalism.IndefR.Mult in
open scoped ComplexOrder in
theorem isCartanInv_cart_model {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (τ : D.what₂.Tau) :
    IsCartanInv (gramAt D V τ) (cart M τ) := by
  have hu := (Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ)
  have h1 : M.fr τ * (M.fr τ)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hu
  have h2 : (M.fr τ)⁻¹ * M.fr τ = 1 := Matrix.nonsing_inv_mul _ hu
  have hJ : Formalism.REAL.Jm (M.ε τ) * Formalism.REAL.Jm (M.ε τ) = 1 := by
    unfold Formalism.REAL.Jm
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1; funext a; split_ifs <;> simp
  have hJ' : (Formalism.REAL.Jm (M.ε τ))ᴴ = Formalism.REAL.Jm (M.ε τ) := by
    unfold Formalism.REAL.Jm
    rw [Matrix.diagonal_conjTranspose]
    congr 1; funext a; simp only [Pi.star_apply]; split_ifs <;> simp
  have hG : gramAt D V τ * cart M τ = (M.fr τ)ᴴ * M.fr τ := by
    rw [← M.fr_gram τ]; unfold cart
    calc _ = (M.fr τ)ᴴ * (Formalism.REAL.Jm (M.ε τ) * (M.fr τ * (M.fr τ)⁻¹) * Formalism.REAL.Jm (M.ε τ)) * M.fr τ := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [h1, Matrix.mul_one, hJ, Matrix.mul_one]
  have hs : cart M τ * cart M τ = 1 := by
    unfold cart
    calc _ = (M.fr τ)⁻¹ * (Formalism.REAL.Jm (M.ε τ) * (M.fr τ * (M.fr τ)⁻¹) * Formalism.REAL.Jm (M.ε τ)) * M.fr τ := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [h1, Matrix.mul_one, hJ, Matrix.mul_one, h2]
  refine ⟨hs, ?_, ?_⟩
  · have hGh : (gramAt D V τ)ᴴ = gramAt D V τ := by
      rw [← M.fr_gram τ]; simp [Matrix.conjTranspose_mul, hJ', Matrix.mul_assoc]
    have h3 : (cart M τ)ᴴ * gramAt D V τ = gramAt D V τ * cart M τ := by
      have := congrArg Matrix.conjTranspose hG
      rw [Matrix.conjTranspose_mul, hGh, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose] at this
      rw [this, hG]
    rw [h3, Matrix.mul_assoc, hs, Matrix.mul_one]
  · rw [hG]
    exact Matrix.PosDef.conjTranspose_mul_self _ (Matrix.mulVec_injective_of_isUnit (M.fr_unit τ))
end GlobalTheory.FrameEquiv
end

section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Proof.LevelCharacterConjugate

theorem levPOf_inv {D : D7} {G K : Type} [Group G] [Field K] {Pg : Finset (Pl D.host.E)} {r : ℕ}
    (eG : G ≃* G0 Pg r) (σ : K →+* ℂ) (P : Subgroup G) (ψ : P →* Kˣ) :
    levPOf eG σ P ψ⁻¹ = (levPOf eG σ P ψ).conj := by
  have hc : (Units.map (σ : K →* ℂ)).comp (ψ⁻¹.comp (eG.symm.toMonoidHom.subgroupComap P)) =
      ((Units.map (σ : K →* ℂ)).comp (ψ.comp (eG.symm.toMonoidHom.subgroupComap P)))⁻¹ :=
    MonoidHom.ext fun x => by simp only [MonoidHom.comp_apply, MonoidHom.inv_apply, map_inv]
  exact congrArg (LevelP.mk (Subgroup.comap eG.symm.toMonoidHom P)) hc

theorem liftLevel_fixedEmbedding_eq_conj_rowLevel {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (b : Bool)
    (h : A.v0 = InfinitePlace.mk D.what₂.embLL) : R.levL F b (sg0 D A) = (R.levR F b).conj := by
  rw [show sg0 D A = D.what₂.embLL from sgAt_mk _ h]
  exact levPOf_inv _ _ _ _

end GlobalTheory.Proof.LevelCharacterConjugate
end

section

noncomputable section

open Polynomial Formalism.L2 Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links

namespace GlobalTheory.AdjBlock

section Record

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}


variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)

theorem postOn_gaL {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (β : GL (Fin V.rank) (EAf D))
    (L : LevDat D.host.E ℂ V.rank) (eG : G ≃* G0 L.Pg L.r) (c : G → ℂ) (x : MMap M) :
    postOn M (gaL V β L eG c) x = ∑ g, c g • postOn M (actL V β L (eG g)) x := by
  ext v h
  simp [postOn, gaL, LinearMap.sum_apply, Finset.sum_apply]

variable {R} {F : Face D A}

end Record

end GlobalTheory.AdjBlock

end
end

section

noncomputable section

open Polynomial Formalism.L2 Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links

namespace GlobalTheory.AdjBlock

section Linear

variable {K V H E : Type} [Field K] [AddCommGroup V] [Module K V]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  {σ : K →+* ℂ} {j : V →ₛₗ[σ] H} {ι : Type} [Fintype ι] {b : Module.Basis ι K V}

theorem map_eq_sum (j : V →ₛₗ[σ] H) (b : Module.Basis ι K V) (v : V) : j v = ∑ i, σ (b.repr v i) • j (b i) := by
  conv_lhs => rw [← b.sum_repr v]

  simp only [map_sum, map_smulₛₗ]

theorem exists_cx (hli : LinearIndependent ℂ fun i => j (b i)) (hsp : Submodule.span ℂ (Set.range j) = ⊤)
    (f : Module.End K V) : ∃ U : Module.End ℂ H, ∀ v, U (j v) = j (f v) := by
  have h2 : ⊤ ≤ Submodule.span ℂ (Set.range fun i => j (b i)) := by
    rw [← hsp, Submodule.span_le]
    rintro _ ⟨v, rfl⟩
    rw [map_eq_sum j b]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  refine ⟨(Module.Basis.mk hli h2).constr ℂ fun i => j (f (b i)), fun v => ?_⟩
  have h3 : ∀ i, ((Module.Basis.mk hli h2).constr ℂ fun i => j (f (b i))) (j (b i)) = j (f (b i)) := fun i => by
    have := (Module.Basis.mk hli h2).constr_basis ℂ (fun i => j (f (b i))) i
    rwa [Module.Basis.mk_apply] at this

  rw [map_eq_sum j b v, map_sum]
  conv_rhs => rw [← b.sum_repr v]

  simp only [map_sum, map_smul, map_smulₛₗ, h3]

theorem ext_of_span {X : Type} [AddCommGroup X] [Module ℂ X] (hsp : Submodule.span ℂ (Set.range j) = ⊤)
    {f g : H →ₗ[ℂ] X} (h : ∀ v, f (j v) = g (j v)) : f = g :=
  LinearMap.ext_on_range hsp h

theorem sum_selfAdj {G : Type} [Group G] [Fintype G] (r : Representation K G V) (a : G → K)
    (ha : ∀ g, starRingEnd ℂ (σ (a g)) = σ (a g⁻¹))
    (hr : ∀ g v w, inner ℂ (j (r g v)) (j (r g w)) = inner ℂ (j v) (j w)) (v w : V) :
    inner ℂ (j ((∑ g, a g • r g) v)) (j w) = inner ℂ (j v) (j ((∑ g, a g • r g) w)) := by

  simp only [LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smulₛₗ, sum_inner, inner_sum, inner_smul_left,
  inner_smul_right, ha]
  refine Fintype.sum_equiv (Equiv.inv G) _ _ fun g => ?_
  rw [Equiv.inv_apply, ← hr g v, ← Module.End.mul_apply (r g) (r g⁻¹), ← map_mul, mul_inv_cancel, map_one,
    Module.End.one_apply]

end Linear

section Poly

end Poly

section Core

variable {K V H E Pl : Type} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  {σ : K →+* ℂ} {j : V →ₛₗ[σ] H} {ι : Type} [Fintype ι] {b : Module.Basis ι K V}

end Core

section Pres

variable {G Γ W K : Type} [Group G] [Group Γ] [NormedAddCommGroup W] [InnerProductSpace ℂ W]
  [Field K] [NumberField K] [StarRing K] {ι : Γ →* G} {S : CSD K} {σ : K →+* ℂ} {ρ : Γ →* Module.End ℂ W}
  {J : Subgroup G} {χ : J →* ℂˣ} (P : Bridge.ClassPres ι S σ ρ J χ) (M : HMod (G → W))
  (hM : M.Is (Bridge.AdForms ι ρ J χ) (Bridge.adInner ι J P.y)) {j : S.Forms →ₛₗ[σ] M.H}
  (hj : ∀ x, M.e (j x) = P.extL x)

include hM hj

theorem model_form : (LinearIndependent ℂ fun i => j (S.basis i)) ∧ Submodule.span ℂ (Set.range j) = ⊤ ∧
    ∀ x y, inner ℂ (j x) (j y) = σ (S.csum (x : S.Cl → S.V) (y : S.Cl → S.V)) := by
  obtain ⟨-, h2, ⟨h3, h4⟩, -⟩ := classPres_basic ι S σ ρ J χ P
  refine ⟨LinearIndependent.of_comp M.e (by simpa only [Function.comp_def, hj] using h3), ?_, fun x y => ?_⟩
  · refine Submodule.map_injective_of_injective hM.1 ?_
    rw [Submodule.map_top, hM.2.1, ← h4, Submodule.map_span, ← Set.range_comp]
    simp only [Function.comp_def, hj]
  · rw [hM.2.2, hj, hj]
    exact h2 x y

end Pres

theorem idem_idem {K G E : Type} [Field K] [CharZero K] [Group G] [Fintype G] [AddCommGroup E] [Module ℂ E]
    (σ : K →+* ℂ) {X : Finset (G → K)} (hX : ∀ c ∈ X, IsAbsIrrChar c) (ρ : Representation ℂ G E) (z : E) :
    ∑ g, σ ((idemOf X).coeff g) • ρ g (∑ h, σ ((idemOf X).coeff h) • ρ h z) = ∑ h, σ ((idemOf X).coeff h) • ρ h z := by
  conv_rhs => rw [← idemOf_mul_self X hX]

  simp only [coeff_mul_fin, map_sum, map_smul, Finset.smul_sum, Finset.sum_smul, map_mul]
  rw [Finset.sum_comm (f := fun h x => (σ ((idemOf X).coeff x) * σ ((idemOf X).coeff (x⁻¹ * h))) • ρ h z)]
  refine Finset.sum_congr rfl fun g _ => Fintype.sum_equiv (Equiv.mulLeft g) _ _ fun h => ?_
  simp [mul_smul]

theorem mem_range_adjoint_tw {E E' : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup E'] [InnerProductSpace ℂ E'] [FiniteDimensional ℂ E'] (s : Bool) (f : E →ₗ[ℂ] E') (y : E) :
    Tw.mk s y ∈ LinearMap.range (LinearMap.adjoint (Tw.map s f)) ↔ y ∈ LinearMap.range (LinearMap.adjoint f) := by
  have : Tw.map s (LinearMap.adjoint f) = LinearMap.adjoint (Tw.map s f) := by
    rw [LinearMap.eq_adjoint_iff]
    intro x y
    rw [Tw.inner_eq, Tw.inner_eq]
    exact congrArg (cj s) (LinearMap.adjoint_inner_left f (Tw.out y) (Tw.out x))
  rw [← this]
  exact Iff.rfl

end GlobalTheory.AdjBlock

end
end

section

open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology

theorem _root_.GlobalTheory.T.not_mem_half_lattice_of_odd_multiplier : ∀ (L : PeriodPair) (α a : ℂ) (S : Finset ℂ), α ≠ 0 → MulStable L α → IsKerReps L α S → Even S.card → α * a ∈ L.lattice → 2 * a ∈ L.lattice → a ∈ L.lattice := by
  first | exact @GlobalTheory.CMModel.mem_lattice_of_even_kerReps | exact GlobalTheory.CMModel.mem_lattice_of_even_kerReps | (intros; apply GlobalTheory.CMModel.mem_lattice_of_even_kerReps <;> assumption)
end

section

open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology

theorem _root_.GlobalTheory.T.prod_kernel_multiplier_translate_neg : ∀ (L : PeriodPair) (α : ℂ) (S : Finset ℂ) (φ : ℂ → ℂ), IsKerReps L α S → MulStable L α → (∀ z l, l ∈ L.lattice → φ (z + l) = φ z) → (∀ z s, α * s ∈ L.lattice → φ (z + s) * ∏ t ∈ S, φ (z + s + t) = φ z * ∏ t ∈ S, φ (z + t)) ∧ ∀ z, ∏ t ∈ S, φ (z - t) = ∏ t ∈ S, φ (z + t) := by
  first | exact @GlobalTheory.KerPerm.prod_ker_translate_neg | exact GlobalTheory.KerPerm.prod_ker_translate_neg | (intros; apply GlobalTheory.KerPerm.prod_ker_translate_neg <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.EndOnTorsion
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_translates_surjective_fibrewise_dense_open : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A], IsAbelianScheme A → ∀ (V : A.left.Opens) (B : Over S) (j : B ⟶ A), (∀ b, j.left b ∈ V) → Smooth B.hom → GeometricallyIntegral B.hom → Surjective ((((fst (A ⊗ A) B ≫ fst A A) * (fst (A ⊗ A) B ≫ snd A A)).left ⁻¹ᵁ V ⊓ ((fst (A ⊗ A) B ≫ fst A A) * (fst (A ⊗ A) B ≫ snd A A)⁻¹).left ⁻¹ᵁ V ⊓ ((snd (A ⊗ A) B ≫ j) * (fst (A ⊗ A) B ≫ snd A A)).left ⁻¹ᵁ V ⊓ ((snd (A ⊗ A) B ≫ j) * (fst (A ⊗ A) B ≫ snd A A)⁻¹).left ⁻¹ᵁ V).ι ≫ (fst (A ⊗ A) B ≫ fst A A).left) := by
  first | exact @GlobalTheory.TranslateSurj.exists_translates_surjective | exact GlobalTheory.TranslateSurj.exists_translates_surjective | (intros; apply GlobalTheory.TranslateSurj.exists_translates_surjective <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.DualOpen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_lift_mono_of_fpqc_cover_lift : ∀ (G T T' Y : Scheme.{0}) (π : G ⟶ Y) [Mono π] (y : T ⟶ Y) (t : T' ⟶ T) [Flat t] [Surjective t] [QuasiCompact t] (z : T' ⟶ G), z ≫ π = t ≫ y → ∃ w : T ⟶ G, w ≫ π = y := by
  first | exact @GlobalTheory.DualOpen.exists_lift_of_fpqc_cover | exact GlobalTheory.DualOpen.exists_lift_of_fpqc_cover | (intros; apply GlobalTheory.DualOpen.exists_lift_of_fpqc_cover <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj

namespace GlobalTheory

theorem injective_of_flat_of_range_subset_genericPoints :
    ∀ (R K : Type) [CommRing R] [IsDomain R] [Field K] (X : Scheme.{0}) (s : X ⟶ Sp R) (x : Sp K ⟶ X) (β : R →+* K), Flat s → Set.range x ⊆ genericPoints X → x ≫ s = spMap β → Function.Injective β := by
  intro R K _ _ _ X s x β hs hx hxs
  set pt : Sp K := IsLocalRing.closedPoint K with hpt
  have hp : x pt ∈ genericPoints X := hx ⟨_, rfl⟩
  let g₀ : Sp R := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum R)
  have hg₀ : g₀ ⤳ s (x pt) :=
    (PrimeSpectrum.le_iff_specializes _ _).mp bot_le
  obtain ⟨y, hy, e⟩ := Flat.generalizingMap s hg₀
  have h₁ : closure ({x pt} : Set X) ⊆ closure {y} :=
    specializes_iff_closure_subset.mp hy
  have h₂ : closure ({y} : Set X) ⊆ closure {x pt} :=
    hp.2 isIrreducible_singleton.closure h₁
  have hyx : y = x pt :=
    (hy.antisymm (specializes_iff_closure_subset.mpr h₂)).eq
  have h₃ : (x ≫ s) pt = g₀ := by
    rw [Scheme.Hom.comp_apply, ← hyx, e]
  rw [hxs] at h₃
  have h₄ : (spMap β pt).asIdeal = RingHom.ker β := by
    show Ideal.comap β (IsLocalRing.maximalIdeal K) = _
    rw [IsLocalRing.maximalIdeal_eq_bot]
    rfl
  rw [h₃] at h₄
  exact (RingHom.injective_iff_ker_eq_bot β).mpr h₄.symm

end GlobalTheory
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.DualOpen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.smooth_exists_point_lift_squareZero_localRing : ∀ (U S : Scheme.{0}) (p : U ⟶ S) [Smooth p] (C : Type) [CommRing C] [IsLocalRing C] (I : Ideal C), I ^ 2 = ⊥ → ∀ (s : Sp C ⟶ S) (u₀ : Sp (C ⧸ I) ⟶ U), u₀ ≫ p = spMap (Ideal.Quotient.mk I) ≫ s → ∃ u : Sp C ⟶ U, spMap (Ideal.Quotient.mk I) ≫ u = u₀ ∧ u ≫ p = s := by
  first | exact @GlobalTheory.SmoothPtLift.exists_lift | exact GlobalTheory.SmoothPtLift.exists_lift | (intros; apply GlobalTheory.SmoothPtLift.exists_lift <;> assumption)
end
