module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle601
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle647
public import Mathlib.Algebra.Homology.HomologicalComplex
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle256
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle258
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle450
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle292
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle452
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneCocycleCoboundaryCommaLocalBasis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle290
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle622
public import Formalism.LocalRingCardinality.DataDIV
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle004
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle637
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle005
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThickTransComp
import Development.AbelianVarietyTheory.Definitions.Degenerations.SepticCharacterInjective
import Development.AbelianVarietyTheory.Definitions.KeyFormula.KeyRootOfKeyFormula

@[expose] public section

section

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CMVal
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (betaBound_vp c_vp cE_vp a0 n_vp)
open GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport (IsConjWt upIdele IsInvIdealOf IsLatOf)
open GlobalTheory.ToricTransport (coordIn)
open scoped nonZeroDivisors

namespace GlobalTheory.LatVal.Model

variable {K : Type} [Field K] [NumberField K]

theorem exists_isLatOf (d : ℕ) (δ : K) (ι : K →+* ℂ) (h2 : Module.finrank ℚ K = 2) (hd : 0 < d) (hδ : δ ^ 2 = -(d : K)) :
    ∃ Λ : PeriodPair, IsLatOf ι 1 Λ := by
  have hc : Fintype.card (Module.Free.ChooseBasisIndex ℤ (𝓞 K)) = Fintype.card (Fin 2) := by
    rw [← Module.finrank_eq_card_chooseBasisIndex, RingOfIntegers.rank, h2]; simp
  let e := Fintype.equivOfCardEq hc
  let b := (RingOfIntegers.basis K).reindex e
  let B := (integralBasis K).reindex e
  have hB : ∀ i, B i = algebraMap (𝓞 K) K (b i) := fun i => by simp [B, b]
  have hrep : ∀ x : K, ∃ p q : ℚ, ι x = p * ι (B 0) + q * ι (B 1) := fun x => by
    refine ⟨B.repr x 0, B.repr x 1, ?_⟩
    conv_lhs => rw [← B.sum_repr x]
    simp [Fin.sum_univ_two, Rat.smul_def]
  have hδ' : ι δ ^ 2 = -(d : ℂ) := by rw [← map_pow, hδ]; simp
  have hind : LinearIndependent ℝ ![ι (B 0), ι (B 1)] := by
    rw [LinearIndependent.pair_iff]
    intro s t h
    simp only [Complex.real_smul] at h
    obtain ⟨p, q, h1⟩ := hrep 1
    obtain ⟨p', q', h3⟩ := hrep δ
    rw [map_one] at h1
    have key : ∀ u w : ℝ, (u : ℂ) * ι δ = w → u = 0 := fun u w huw => by
      have : ((u : ℂ) * ι δ) ^ 2 = (w : ℂ) ^ 2 := by rw [huw]
      rw [mul_pow, hδ'] at this
      have h' : u ^ 2 * (-(d : ℝ)) = w ^ 2 := by exact_mod_cast this
      have hd' : (0 : ℝ) < d := by exact_mod_cast hd
      have : u ^ 2 ≤ 0 := by nlinarith [sq_nonneg w, sq_nonneg u]
      exact pow_eq_zero_iff (two_ne_zero) |>.1 (le_antisymm this (sq_nonneg u))
    have k1 := key (s * q - t * p) (s * q' - t * p') (by
      push_cast
      have : ((s : ℂ) * q' - t * p') = ((s : ℂ) * q' - t * p') * 1 := by ring
      rw [this, h1, h3]
      linear_combination (q * p' - p * q' : ℂ) * h)
    have k1' : (s : ℂ) * q - t * p = 0 := by exact_mod_cast k1
    have hb0 : ι (B 0) ≠ 0 := by simpa using B.ne_zero 0
    have hb1 : ι (B 1) ≠ 0 := by simpa using B.ne_zero 1
    have hs : (s : ℂ) = 0 := by linear_combination (s : ℂ) * h1 + (p : ℂ) * h + ι (B 1) * k1'
    have ht : (t : ℂ) = 0 := by linear_combination (t : ℂ) * h1 + (q : ℂ) * h - ι (B 0) * k1'
    exact ⟨by exact_mod_cast hs, by exact_mod_cast ht⟩
  refine ⟨⟨ι (B 0), ι (B 1), hind⟩, ?_⟩
  ext z
  simp only [SetLike.mem_coe, PeriodPair.mem_lattice, Set.mem_image, FractionalIdeal.mem_coe, FractionalIdeal.mem_one_iff]
  constructor
  · rintro ⟨m, n, rfl⟩
    exact ⟨_, ⟨m * b 0 + n * b 1, rfl⟩, by simp [hB]⟩
  · rintro ⟨_, ⟨r, rfl⟩, rfl⟩
    refine ⟨b.repr r 0, b.repr r 1, ?_⟩
    conv_rhs => rw [← b.sum_repr r]
    simp [Fin.sum_univ_two, hB]

end GlobalTheory.LatVal.Model
end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbCoh

def FP (R M : Type) [CommRing R] [AddCommGroup M] [Module R M] (n : ℕ) : Prop :=
  Module.Finite R M ∧ Module.Projective R M ∧ ∀ p : PrimeSpectrum R, Module.rankAtStalk M p = n

section Formal

variable {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R)

def CohomZeroIsConstants : Prop := ∀ g : C0 F, d0 F g = 0 → ∃! r : R, ∀ T, g T = algebraMap R (F.obj T) r

def WedgeO : Prop :=
  ∃ e : ⋀[R]^2 (CatCoh.H1 F) ≃ₗ[R] CatCoh.H2 F, ∀ a b, e (exteriorPower.ιMulti R 2 ![a, b]) = cup F a b

structure Frame (n : ℕ) where

  w : Fin n → Glob1 F

  δ : Fin n → ∀ T : C, Ω[F.obj T⁄R] →ₗ[F.obj T] F.obj T
  nat : ∀ (i : Fin n) ⦃T T' : C⦄ (φ : T ⟶ T') (ω : Ω[F.obj T⁄R]), δ i T' (p1 F φ ω) = mp F φ (δ i T ω)
  sum : ∀ (T : C) (ω : Ω[F.obj T⁄R]), ω = ∑ i, δ i T ω • (w i).1 T

def HasFrame : Prop := ∃ n, Nonempty (Frame F n)

variable {n : ℕ}

def wsum (u v : Fin n → Glob1 F) : W0 F 2 := fun T ↦ ∑ k, wedge R (F.obj T) ((u k).1 T) ((v k).1 T)

def ClRel (w : Glob1 F) (u v : Fin n → Glob1 F) : Prop := ∀ T, dOne R (F.obj T) (w.1 T) = wsum F u v T

def DRel (x : CatCoh.H1 F) (y : Fin n → CatCoh.H1 F) (w : Fin n → Glob1 F) : Prop :=
  ∃ (f : Z1 F) (g : Fin n → Z1 F) (ω : A0 F), CatCoh.H1.mk F f = x ∧ (∀ k, CatCoh.H1.mk F (g k) = y k) ∧
    ∀ ⦃T T' : C⦄ (φ : T ⟶ T'),
      D R (F.obj T') (f.1 T T' φ) = ∑ k, (g k).1 T T' φ • (w k).1 T' + (ω T' - p1 F φ (ω T))

def ObRel (x : CatCoh.H1 F) (u v : Fin n → Glob1 F) : Prop :=
  ∃ (f : Z1 F) (ω : A0 F), CatCoh.H1.mk F f = x ∧
    (∀ ⦃T T' : C⦄ (φ : T ⟶ T'), ω T' = p1 F φ (ω T) + D R (F.obj T') (f.1 T T' φ)) ∧
    ∀ T, dOne R (F.obj T) (ω T) = wsum F u v T

def clAll (h : Closed1 F = ⊤) : Glob1 F →ₗ[R] Hyp1 F :=
  ofForm F ∘ₗ (LinearEquiv.ofTop _ h).symm.toLinearMap

end Formal

section Pull

variable {R R' : Type} [CommRing R] [CommRing R'] {X X' : Scheme.{0}}

abbrev HO2 (s : X ⟶ Sp R) : Type := CatCoh.H2 (OAff s)

theorem pairRes_pull2_bijective (φ : X' ⟶ X) (s' : X' ⟶ Sp R') : Function.Bijective (pairRes φ s').pull2 := by
  have H := _root_.GlobalTheory.CechDR.hasLoc_OAff s'
  have hcov := _root_.GlobalTheory.CechDR.pair_cover_affine φ s'
  have hdir := _root_.GlobalTheory.CechDR.exists_pair_below_two φ s'
  have hs := _root_.GlobalTheory.sep_of_factoring_cover (OAff s') (pairFst φ) H hcov
  have hg := _root_.GlobalTheory.CatCoh.Desc.glue_comma_of_basis (OAff s') (pairFst φ) H hcov hdir
  have hv := _root_.GlobalTheory.CatCoh.Desc.Basis.oneCocycle_vanishing_comma_of_basis (OAff s') (pairFst φ) H hcov hdir
  have hv2 := GlobalTheory.T.twoCocycle_coboundary_of_basisFunctor (OAff s') (pairFst φ) H hcov hdir
  exact ⟨GlobalTheory.T.comma_descent_injective _ _ hs hg hv, GlobalTheory.T.comma_descent_restriction_equiv _ _ hs hg hv hv2⟩

variable {s : X ⟶ Sp R} {s' : X' ⟶ Sp R'} {σ : R →+* R'} {φ : X' ⟶ X} (h : φ ≫ s = s' ≫ spMap σ)

def pullHO2 : HO2 s →ₛₗ[σ] HO2 s' :=
  (LinearEquiv.ofBijective (pairRes φ s').pull2 (pairRes_pull2_bijective φ s')).symm.toLinearMap.comp
    (pairPull h).pull2

def Red1 (f : C1 (OAff s)) (x : HO1 s') : Prop :=
  ∃ c : Z1 (OPair φ s'), (∀ p q (a : p ⟶ q), c.1 p q a = (pairPull h).α q (f _ _ ((pairPull h).G.map a))) ∧
    CatCoh.H1.mk _ c = (pairRes φ s').pull1 x

def Red2 (w : C2 (OAff s)) (z : HO2 s') : Prop :=
  ∃ c : Z2 (OPair φ s'), (∀ p q r (a : p ⟶ q) (b : q ⟶ r),
      c.1 p q r a b = (pairPull h).α r (w _ _ _ ((pairPull h).G.map a) ((pairPull h).G.map b))) ∧
    CatCoh.H2.mk _ c = (pairRes φ s').pull2 z

def TMul (t : R) (u : HO1 s') (y : HO1 s) : Prop :=
  ∃ (f : C1 (OAff s)) (c : Z1 (OAff s)), c.1 = t • f ∧ CatCoh.H1.mk _ c = y ∧ Red1 h f u

def Bock {R₀ : Type} [CommRing R₀] {X₀ : Scheme.{0}} {s₀ : X₀ ⟶ Sp R₀} {σ₀ : R →+* R₀} {φ₀ : X₀ ⟶ X}
    (h₀ : φ₀ ≫ s = s₀ ≫ spMap σ₀) (t : R) (x : HO1 s') (z : HO2 s₀) : Prop :=
  ∃ (f : C1 (OAff s)) (w : C2 (OAff s)), d1 (OAff s) f = t • w ∧ Red1 h f x ∧ Red2 h₀ w z

end Pull

def SmallExt {R R' R₀ : Type} [CommRing R] [CommRing R'] [CommRing R₀] (t : R) (σ : R →+* R') (σ₀ : R →+* R₀) : Prop :=
  Function.Surjective σ ∧ RingHom.ker σ = Ideal.span {t} ∧ Function.Surjective σ₀ ∧ ∀ a, σ₀ a = 0 ↔ a * t = 0

section BaseChange

variable {R : Type} [CommRing R] {X : Scheme.{0}} (s : X ⟶ Sp R)

def StructureSheafH1BaseChange : Prop := ∀ (R' : Type) [CommRing R'] [Algebra R R'] (X' : Scheme.{0}) (s' : X' ⟶ Sp R') (φ : X' ⟶ X)
  (h : IsPullback φ s' s (spMap (algebraMap R R'))),
    ∃ e : R' ⊗[R] HO1 s ≃ₗ[R'] HO1 s', ∀ c, e (1 ⊗ₜ c) = pullHO1 h.w c

def StructureSheafH2BaseChange : Prop := ∀ (R' : Type) [CommRing R'] [Algebra R R'] (X' : Scheme.{0}) (s' : X' ⟶ Sp R') (φ : X' ⟶ X)
  (h : IsPullback φ s' s (spMap (algebraMap R R'))),
    ∃ e : R' ⊗[R] HO2 s ≃ₗ[R'] HO2 s', ∀ c, e (1 ⊗ₜ c) = pullHO2 h.w c

def UConst : Prop := ∀ (R' : Type) [CommRing R'] [Algebra R R'] (X' : Scheme.{0}) (s' : X' ⟶ Sp R') (φ : X' ⟶ X),
  IsPullback φ s' s (spMap (algebraMap R R')) → CohomZeroIsConstants (OAff s')

abbrev dB (K : CochainComplex (ModuleCat.{0} R) ℕ) (R' : Type) [CommRing R'] [Algebra R R'] (i j : ℕ) :
    R' ⊗[R] K.X i →ₗ[R'] R' ⊗[R] K.X j := (K.d i j).hom.baseChange R'

abbrev ext {R' R'' : Type} [CommRing R'] [Algebra R R'] [CommRing R''] [Algebra R R''] (α : R' →ₐ[R] R'')
    (M : Type) [AddCommGroup M] [Module R M] : R' ⊗[R] M →ₗ[R] R'' ⊗[R] M := α.toLinearMap.rTensor M

structure Model (K : CochainComplex (ModuleCat.{0} R) ℕ) where

  θ0 : ∀ {R' : Type} [CommRing R'] [Algebra R R'] {X' : Scheme.{0}} {s' : X' ⟶ Sp R'} {φ : X' ⟶ X}
    (_ : IsPullback φ s' s (spMap (algebraMap R R'))),
    LinearMap.ker (dB K R' 0 1) ≃ₗ[R'] LinearMap.ker (d0 (OAff s'))

  one : K.X 0
  θ0_one : ∀ {R' : Type} [CommRing R'] [Algebra R R'] {X' : Scheme.{0}} {s' : X' ⟶ Sp R'} {φ : X' ⟶ X}
    (h : IsPullback φ s' s (spMap (algebraMap R R'))),
    ∃ e : (1 : R') ⊗ₜ[R] one ∈ LinearMap.ker (dB K R' 0 1), ∀ T, (θ0 h ⟨_, e⟩).1 T = 1

  θ1 : ∀ {R' : Type} [CommRing R'] [Algebra R R'] {X' : Scheme.{0}} {s' : X' ⟶ Sp R'} {φ : X' ⟶ X}
    (_ : IsPullback φ s' s (spMap (algebraMap R R'))), LinearMap.ker (dB K R' 1 2) →ₗ[R'] HO1 s'

  θ2 : ∀ {R' : Type} [CommRing R'] [Algebra R R'] {X' : Scheme.{0}} {s' : X' ⟶ Sp R'} {φ : X' ⟶ X}
    (_ : IsPullback φ s' s (spMap (algebraMap R R'))), LinearMap.ker (dB K R' 2 3) →ₗ[R'] HO2 s'
  exact : ∀ {R' : Type} [CommRing R'] [Algebra R R'] {X' : Scheme.{0}} {s' : X' ⟶ Sp R'} {φ : X' ⟶ X}
    (h : IsPullback φ s' s (spMap (algebraMap R R'))),
    Function.Surjective (θ1 h) ∧ (∀ z, θ1 h z = 0 ↔ z.1 ∈ LinearMap.range (dB K R' 0 1)) ∧
    Function.Surjective (θ2 h) ∧ ∀ z, θ2 h z = 0 ↔ z.1 ∈ LinearMap.range (dB K R' 1 2)
  nat : ∀ {R' : Type} [CommRing R'] [Algebra R R'] {X' : Scheme.{0}} {s' : X' ⟶ Sp R'} {φ : X' ⟶ X}
    (h : IsPullback φ s' s (spMap (algebraMap R R')))
    {R'' : Type} [CommRing R''] [Algebra R R''] {X'' : Scheme.{0}} {s'' : X'' ⟶ Sp R''} {φ' : X'' ⟶ X}
    (h' : IsPullback φ' s'' s (spMap (algebraMap R R''))) (α : R' →ₐ[R] R'') (ψ : X'' ⟶ X')
    (w : ψ ≫ s' = s'' ≫ spMap (α : R' →+* R'')), ψ ≫ φ = φ' →
    (∀ z z', z'.1 = ext α _ z.1 → θ1 h' z' = pullHO1 w (θ1 h z)) ∧
    ∀ z z', z'.1 = ext α _ z.1 → θ2 h' z' = pullHO2 w (θ2 h z)

def LiftsAt (K : CochainComplex (ModuleCat.{0} R) ℕ) {R' R'' : Type} [CommRing R'] [Algebra R R'] [CommRing R'']
    [Algebra R R''] (α : R' →ₐ[R] R'') (i : ℕ) : Prop :=
  ∀ z : R'' ⊗[R] K.X i, dB K R'' i (i + 1) z = 0 → ∃ (y : R' ⊗[R] K.X i) (b : R'' ⊗[R] K.X (i - 1)),
    dB K R' i (i + 1) y = 0 ∧ z = ext α _ y + dB K R'' (i - 1) i b

end BaseChange

section Over

variable {R : Type} [CommRing R] {Y A : Over (Sp R)}

theorem ovw (f : Y ⟶ A) : f.left ≫ A.hom = Y.hom ≫ spMap (RingHom.id R) := by
  rw [spMap_id, Over.w f]; exact (Category.comp_id _).symm

def pO1 (f : Y ⟶ A) : HO1 A.hom →ₗ[R] HO1 Y.hom := pullHO1 (ovw f)

def structureSheafH2Pullback (f : Y ⟶ A) : HO2 A.hom →ₗ[R] HO2 Y.hom := pullHO2 (ovw f)

def pF (f : Y ⟶ A) : GlobForm A.hom →ₗ[R] GlobForm Y.hom := pullForm (ovw f)

def deRhamH1Pullback (f : Y ⟶ A) : HH1 A.hom →ₗ[R] HH1 Y.hom := pullHH1 (ovw f)

def deRhamH2Pullback (f : Y ⟶ A) : HH2 A.hom →ₗ[R] HH2 Y.hom := pullHH2 (ovw f)

variable (A) [GrpObj A]

def StructureSheafH1Primitive : Prop := ∀ x : HO1 A.hom, pO1 μ[A] x = pO1 (fst A A) x + pO1 (snd A A) x

def PrimF : Prop := ∀ x : GlobForm A.hom, pF μ[A] x = pF (fst A A) x + pF (snd A A) x

def DeRhamH1Primitive : Prop := ∀ x : HH1 A.hom, deRhamH1Pullback μ[A] x = deRhamH1Pullback (fst A A) x + deRhamH1Pullback (snd A A) x

def NoPrimitiveStructureSheafH2 : Prop := ∀ z : HO2 A.hom, structureSheafH2Pullback μ[A] z = structureSheafH2Pullback (fst A A) z + structureSheafH2Pullback (snd A A) z → z = 0

def AxesVanishingStructureSheafDegOne : Prop := ∀ y : HO1 (A ⊗ A).hom, pO1 (lift (𝟙 A) (toUnit A ≫ η[A])) y = 0 →
  pO1 (lift (toUnit A ≫ η[A]) (𝟙 A)) y = 0 → y = 0

end Over

def OStr : Prop :=
  ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A →
    SmoothOfRelativeDimension g A.hom →
    FP R (HO1 A.hom) g ∧ WedgeO (OAff A.hom) ∧ StructureSheafH1BaseChange A.hom ∧ StructureSheafH2BaseChange A.hom

end GlobalTheory.AbCoh
end
end

section

open MvPolynomial Formalism.DegreeFormula Formalism.BasicNotions Formalism.BasicNotions.DV Filter Topology

noncomputable section

namespace GlobalTheory.FlagAr

open GlobalTheory.FlagPoly

variable {D : D7} (Y : ShimX D.what₂.Tau)

def setB (B : ℝ) : Finset ℕ :=
  ((Finset.range (⌊B⌋₊ + 1)).filter Nat.Prime) ∪
    (Nat.primeFactors (2 * (NumberField.discr D.host.E).natAbs) ∪ Y.lev)

end GlobalTheory.FlagAr
end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ArithmeticCylinders

namespace GlobalTheory.BadCount

def EmbReg {K Γ V : Type} [Field K] [Group Γ] [AddCommGroup V] [Module K V] (ρ : Representation K Γ V)
    (H : Subgroup Γ) (n : ℕ) : Prop :=
  ∃ j : V →ₗ[K] (Fin n → MonoidAlgebra K H), Function.Injective j ∧
    ∀ (h : H) (v : V) (i : Fin n), j (ρ h v) i = MonoidAlgebra.single h 1 * j v i

def eig {K Γ V : Type} [Field K] [Group Γ] [AddCommGroup V] [Module K V] (ρ : Representation K Γ V)
    (H : Subgroup Γ) (lam : H →* Kˣ) : Submodule K V :=
  ⨅ h : H, LinearMap.ker (ρ h - ((lam h : Kˣ) : K) • LinearMap.id)

theorem mem_eig {K Γ V : Type} [Field K] [Group Γ] [AddCommGroup V] [Module K V] (ρ : Representation K Γ V)
    (H : Subgroup Γ) (lam : H →* Kˣ) (v : V) : v ∈ eig ρ H lam ↔ ∀ h : H, ρ h v = ((lam h : Kˣ) : K) • v := by
  simp [eig, Submodule.mem_iInf, sub_eq_zero]

variable (D : D7)


open Classical in
def badElt (k : Fin 2) (S : Finset (Tup D k)) : MonoidAlgebra ℂ (G0g D.nd) :=
  haveI : ∀ k, NeZero (D.host.g k) := fun k => ⟨(D.host.g_prime k).ne_zero⟩
  MonoidAlgebra.ofCoeff <| Finsupp.equivFunOnFinite.symm fun g : G0g D.nd =>
    if ∀ kv : (Σ k : Fin 2, D.nd.PlG k), kv.1 ≠ k → g kv = 1 then
      ∑ t ∈ S, ∏ v : D.nd.PlG k, (D.ntypes.eSer k (t v)).coeff (g ⟨k, v⟩) else 0

def IsWhit (P : Subgroup (G0g D.nd)) (lam : P →* ℂˣ)
    (ψ : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), AddChar (ZMod (D.host.g kv.1)) ℂ) : Prop :=
  (∀ kv, ψ kv ≠ 1) ∧
  (∀ g : G0g D.nd, g ∈ P ↔ ∀ kv, IsUniUp (g kv : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1)))) ∧
  ∀ g : P, ((lam g : ℂˣ) : ℂ) = ∏ kv : (Σ k : Fin 2, D.nd.PlG k), ψ kv (∑ i ∈ Finset.range (D.R.r - 1),
    entN ((g : G0g D.nd) kv : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1))) i (i + 1))

def IsHalf (k : Fin 2) (H : Subgroup (G0g D.nd)) : Prop :=
  ∀ g : G0g D.nd, g ∈ H ↔ ∀ kv : (Σ k : Fin 2, D.nd.PlG k), kv.1 ≠ k →
    IsUniUp (g kv : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1)))

def IsSplit {Γ G : Type} [Group Γ] [Group G] (π : Γ →* G) (ι : G →* Γ) : Prop :=
  (∀ g, π (ι g) = g) ∧ ∀ g γ, π γ = 1 → ι g * γ = γ * ι g

end GlobalTheory.BadCount
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.KeyCl GlobalTheory.Ex
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.MBLow

def KeyAtMap {R R' : Type} [CommRing R] [CommRing R'] (x' : KeyIn R') (x : KeyIn R) (f : R →+* R')
    (φ : x'.P.A.left ⟶ x.P.A.left) : Prop :=
  ∃ (he : eSec x'.P.A ≫ φ = spMap f ≫ eSec x.P.A)
    (w : LB.Iso x'.P.L (x.P.L.pull φ)) (hg : x'.P.g = x.P.g) (F : DualNumber R →+* DualNumber R'),
    IsGrpPullback x'.P.A x.P.A (spMap f) φ ∧ w.IsGen ∧
    LB.Gen.Maps (LB.linCombIso w (K := PUnit) (fun _ => eSec x'.P.A) (fun _ => 1)) x'.rig
      (rigPullOf φ (spMap f) he x.P.L x.rig) ∧
    (∀ (j : (x.P.L.pull φ).ι) (i : x'.P.L.ι)
      (h : (x.P.L.pull φ).U j ⊓ x'.P.L.U i ≤ φ ⁻¹ᵁ x.P.L.U (j PUnit.unit)),
      (φ.appLE _ _ h).hom (x.th.f (j PUnit.unit)) =
        (show Γ(x'.P.A.left, (x.P.L.pull φ).U j ⊓ x'.P.L.U i) from (w.s (j, i)).val) *
          resG _ inf_le_right (x'.th.f i)) ∧
    (∀ a, F (algebraMap R _ a) = algebraMap R' _ (f a)) ∧ F DualNumber.eps = DualNumber.eps ∧
    ∀ i, (x'.v i).left ≫ φ = spMap F ≫ (x.v (i.cast hg)).left

end GlobalTheory.MBLow

end
end
