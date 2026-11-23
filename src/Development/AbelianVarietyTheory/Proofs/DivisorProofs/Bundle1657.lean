module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
public import Mathlib.Algebra.QuaternionBasis
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1488
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1646
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle017
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle586
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1652
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle048
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniformisationOfPoint
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle091
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle021
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianUnobstructed
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle023
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CobOneEqZeroOfConnecting
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1613
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle977
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle874
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle024
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle879
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1610
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle904
public import GroundTheory.AutomorphicForms.MultiplicityOne.Bundle001
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle031
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1300
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1099
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1640
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle033
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1615
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle036
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1616
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle010

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.QSA GlobalTheory.Published
open Matrix
open scoped Quaternion Topology TensorProduct

noncomputable section

namespace GlobalTheory.QSA.Split

variable {F : Type} [Field F] [NumberField F] {a b : F}

def qi : ℍ[F, a, b] := ⟨0, 1, 0, 0⟩

def qj : ℍ[F, a, b] := ⟨0, 0, 1, 0⟩

def qk : ℍ[F, a, b] := ⟨0, 0, 0, 1⟩

theorem decomp (y : ℍ[F, a, b]) : y = y.re • (1 : ℍ[F, a, b]) + y.imI • qi + y.imJ • qj + y.imK • qk := by
  ext <;> simp [qi, qj, qk]

theorem map_smul_F (c : F) (M : Matrix (Fin 2) (Fin 2) F) :
    (c • M).map (algebraMap F (AF F)) = algebraMap F (AF F) c • M.map (algebraMap F (AF F)) := by
  ext i j; simp

theorem map_smul_one (c : F) :
    (c • (1 : Matrix (Fin 2) (Fin 2) F)).map (algebraMap F (AF F)) = algebraMap F (AF F) c • 1 := by
  rw [map_smul_F, Matrix.map_one _ (map_zero _) (map_one _)]

variable (φ : ℍ[F, a, b] ≃ₐ[F] Matrix (Fin 2) (Fin 2) F)

def bcBasis : QuaternionAlgebra.Basis (Matrix (Fin 2) (Fin 2) (AF F)) (algebraMap F (AF F) a) 0
    (algebraMap F (AF F) b) where
  i := (φ qi).map (algebraMap F (AF F))
  j := (φ qj).map (algebraMap F (AF F))
  k := (φ qk).map (algebraMap F (AF F))
  i_mul_i := by
    rw [← Matrix.map_mul, ← map_mul]
    have : (qi : ℍ[F, a, b]) * qi = a • 1 := by ext <;> simp [qi]
    rw [this, map_smul, map_one, map_smul_one, zero_smul, add_zero]
  j_mul_j := by
    rw [← Matrix.map_mul, ← map_mul]
    have : (qj : ℍ[F, a, b]) * qj = b • 1 := by ext <;> simp [qj]
    rw [this, map_smul, map_one, map_smul_one]
  i_mul_j := by
    rw [← Matrix.map_mul, ← map_mul]
    have : (qi : ℍ[F, a, b]) * qj = qk := by ext <;> simp [qi, qj, qk]
    rw [this]
  j_mul_i := by
    rw [← Matrix.map_mul, ← map_mul, zero_smul, zero_sub]
    have : (qj : ℍ[F, a, b]) * qi = -qk := by ext <;> simp [qi, qj, qk]
    rw [this, map_neg, Matrix.map_neg _ (map_neg _)]

def Φ : DA F a b →ₐ[AF F] Matrix (Fin 2) (Fin 2) (AF F) := (bcBasis φ).liftHom

theorem Φ_apply (x : DA F a b) : Φ φ x = x.re • (1 : Matrix (Fin 2) (Fin 2) (AF F))
    + x.imI • (φ qi).map (algebraMap F (AF F)) + x.imJ • (φ qj).map (algebraMap F (AF F))
    + x.imK • (φ qk).map (algebraMap F (AF F)) := by
  simp [Φ, QuaternionAlgebra.Basis.liftHom, QuaternionAlgebra.Basis.lift, bcBasis, Algebra.algebraMap_eq_smul_one]

def Ψ (m : Matrix (Fin 2) (Fin 2) (AF F)) : DA F a b :=
  ∑ i, ∑ j, m i j • rat (φ.symm (Matrix.single i j 1))

theorem rat_add (x y : ℍ[F, a, b]) : rat (x + y) = rat x + rat y := by ext <;> simp [rat]

theorem rat_smul (c : F) (x : ℍ[F, a, b]) : rat (c • x) = algebraMap F (AF F) c • rat x := by
  ext <;> simp [rat] <;> rw [Algebra.smul_def]

theorem rat_sum {ι : Type} (s : Finset ι) (f : ι → ℍ[F, a, b]) : rat (∑ i ∈ s, f i) = ∑ i ∈ s, rat (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => ext <;> simp [rat]
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, rat_add, ih]

theorem rat_one : rat (1 : ℍ[F, a, b]) = 1 := by ext <;> simp [rat]

theorem Ψ_add (m n : Matrix (Fin 2) (Fin 2) (AF F)) : Ψ φ (m + n) = Ψ φ m + Ψ φ n := by
  simp only [Ψ, Matrix.add_apply, add_smul, Finset.sum_add_distrib]

theorem Ψ_smul (c : AF F) (m : Matrix (Fin 2) (Fin 2) (AF F)) : Ψ φ (c • m) = c • Ψ φ m := by
  simp only [Ψ, Matrix.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum]

theorem Ψ_map (M : Matrix (Fin 2) (Fin 2) F) : Ψ φ (M.map (algebraMap F (AF F))) = rat (φ.symm M) := by
  conv_rhs => rw [Matrix.matrix_eq_sum_single M]

  simp only [Ψ, Matrix.map_apply, map_sum, rat_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [show Matrix.single i j (M i j) = M i j • Matrix.single i j (1 : F) by rw [Matrix.smul_single, smul_eq_mul, mul_one],
    map_smul, rat_smul]

theorem Ψ_one : Ψ φ 1 = 1 := by
  rw [← Matrix.map_one (algebraMap F (AF F)) (map_zero _) (map_one _), Ψ_map, map_one, rat_one]

theorem Φ_rat (y : ℍ[F, a, b]) : Φ φ (rat y) = (φ y).map (algebraMap F (AF F)) := by
  conv_rhs => rw [decomp y]
  simp only [Φ_apply, map_add (f := _), map_smul, map_one, Matrix.map_add (f := _), map_smul_F, Matrix.map_one _ (map_zero _) (map_one (algebraMap F (AF F)))]
  ext i j
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.map_apply, Matrix.one_apply, smul_eq_mul, map_add (f := _), map_mul, rat]
  split_ifs <;> simp

theorem Φ_Ψ (m : Matrix (Fin 2) (Fin 2) (AF F)) : Φ φ (Ψ φ m) = m := by
  conv_rhs => rw [Matrix.matrix_eq_sum_single m]

  simp only [Ψ, map_sum, map_smul, Φ_rat, AlgEquiv.apply_symm_apply]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ext k l; simp [Matrix.single_apply]

theorem Ψ_Φ (x : DA F a b) : Ψ φ (Φ φ x) = x := by
  rw [Φ_apply, Ψ_add, Ψ_add, Ψ_add, Ψ_smul, Ψ_smul, Ψ_smul, Ψ_smul, Ψ_one, Ψ_map, Ψ_map, Ψ_map]
  simp only [AlgEquiv.symm_apply_apply]
  ext <;> simp [rat, qi, qj, qk]

theorem Ψ_mul (m n : Matrix (Fin 2) (Fin 2) (AF F)) : Ψ φ (m * n) = Ψ φ m * Ψ φ n := by
  conv_lhs => rw [← Φ_Ψ φ m, ← Φ_Ψ φ n, ← map_mul, Ψ_Φ]

theorem det_four {R : Type} [CommRing R] (A₀ A₁ A₂ A₃ : Matrix (Fin 2) (Fin 2) R) (x₀ x₁ x₂ x₃ : R) :
    (x₀ • A₀ + x₁ • A₁ + x₂ • A₂ + x₃ • A₃).det = x₀ ^ 2 * A₀.det + x₁ ^ 2 * A₁.det + x₂ ^ 2 * A₂.det
      + x₃ ^ 2 * A₃.det + x₀ * x₁ * ((A₀ + A₁).det - A₀.det - A₁.det) + x₀ * x₂ * ((A₀ + A₂).det - A₀.det - A₂.det)
      + x₀ * x₃ * ((A₀ + A₃).det - A₀.det - A₃.det) + x₁ * x₂ * ((A₁ + A₂).det - A₁.det - A₂.det)
      + x₁ * x₃ * ((A₁ + A₃).det - A₁.det - A₃.det) + x₂ * x₃ * ((A₂ + A₃).det - A₂.det - A₃.det) := by
  simp [Matrix.det_fin_two]; ring

theorem det_Φ (hφ : ∀ x, (φ x).det = nrm x) (x : DA F a b) : (Φ φ x).det = nrm x := by
  have hd : ∀ y : ℍ[F, a, b], ((φ y).map (algebraMap F (AF F))).det = algebraMap F (AF F) (nrm y) := by
    intro y; rw [← hφ y, RingHom.map_det]; rfl
  have hd2 : ∀ y z : ℍ[F, a, b], ((φ y).map (algebraMap F (AF F)) + (φ z).map (algebraMap F (AF F))).det
      = algebraMap F (AF F) (nrm (y + z)) := by
    intro y z; rw [← Matrix.map_add _ (map_add _), ← map_add (f := _)]; exact hd _
  have h1 : (1 : Matrix (Fin 2) (Fin 2) (AF F)) = (φ 1).map (algebraMap F (AF F)) := by
    rw [map_one, Matrix.map_one _ (map_zero _) (map_one _)]
  rw [Φ_apply, h1, det_four]
  simp only [hd2, hd]
  simp [nrm, qi, qj, qk]
  ring

theorem nrm_Ψ (hφ : ∀ x, (φ x).det = nrm x) (m : Matrix (Fin 2) (Fin 2) (AF F)) : nrm (Ψ φ m) = m.det := by
  rw [← det_Φ φ hφ, Φ_Ψ]

theorem Ψ_cont : Continuous (Ψ φ) := by
  have hc : ∀ x : DA F a b, coords x = QuaternionAlgebra.linearEquivTuple _ _ _ x := fun x => by
    ext k; fin_cases k <;> rfl
  apply continuous_induced_rng.2
  have : (coords ∘ Ψ φ : Matrix (Fin 2) (Fin 2) (AF F) → Fin 4 → AF F) =
      fun m => ∑ i, ∑ j, m i j • coords (rat (φ.symm (Matrix.single i j 1)) : DA F a b) := by
    funext m; simp only [Function.comp, Ψ, hc, map_sum, map_smul]
  rw [this]
  refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_
  exact (continuous_id.matrix_elem i j).smul continuous_const

theorem Ψ_sub_one (m : Matrix (Fin 2) (Fin 2) (AF F)) : Ψ φ (m - 1) = Ψ φ m - 1 := by
  rw [sub_eq_add_neg, Ψ_add, show -(1 : Matrix (Fin 2) (Fin 2) (AF F)) = (-1 : AF F) • 1 by simp, Ψ_smul, Ψ_one]
  simp [sub_eq_add_neg]

end GlobalTheory.QSA.Split


open GlobalTheory.QSA.Split in
theorem GlobalTheory.QSA.strongApprox_split : ∀ (F : Type) [Field F] [NumberField F] (a b : F), a ≠ 0 → b ≠ 0 → (∃ x : ℍ[F, a, b], x ≠ 0 ∧ nrm x = 0) → ∀ (S₁ : Finset (InfinitePlace F)) (S₂ : Finset (HeightOneSpectrum (𝓞 F))) (ε : AF F), IsPlacesIdem S₁ S₂ ε → (S₁.Nonempty ∨ S₂.Nonempty) → ∀ g : DA F a b, nrm g = 1 → g ∈ closure (H0 (a := a) (b := b) ε) := by
  intro F _ _ a b ha hb hiso S₁ S₂ ε hε hS g hg
  obtain ⟨φ, hφ⟩ := GlobalTheory.T.quaternion_split_of_isotropic_norm F a b ha hb hiso
  have hdet : (Φ φ g).det = 1 := by rw [det_Φ φ hφ, hg]
  have hcl := GlobalTheory.T.strong_approximation_SL2_adeles F S₁ S₂ ε hε hS (Φ φ g) hdet
  rw [← Ψ_Φ φ g]
  refine map_mem_closure (Ψ_cont φ) hcl ?_
  rintro _ ⟨γ, hγ, h, hh, hεh, rfl⟩
  refine ⟨φ.symm γ, ?_, Ψ φ h, ?_, ?_, ?_⟩
  · rw [← hφ, AlgEquiv.apply_symm_apply, hγ]
  · rw [nrm_Ψ φ hφ, hh]
  · rw [← Ψ_sub_one, ← Ψ_smul, hεh]
  · rw [Ψ_mul, Ψ_map]
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix

noncomputable section

namespace GlobalTheory.FibreExp

theorem exists_exp_lattice : ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] [IsCommMonObj G] (g : ℕ), IsAbelianScheme G →
    SmoothOfRelativeDimension g G.hom → ∀ y : Sp ℂ ⟶ X, ∃ (e : (Fin g → ℂ) → (Over.mk y ⟶ G))
      (Λ : Submodule ℤ (Fin g → ℂ)), IsExp y e ∧ DiscreteTopology Λ ∧ Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ ∧
        ∀ z, e z = 1 ↔ z ∈ Λ := by
  intro X G _ _ g hG hgG y
  letI : (Over.pullback y).Monoidal := (Over.instBraidedPullback (f := y)).toMonoidal
  letI : GrpObj ((Over.pullback y).obj G) := Functor.grpObjObj (F := Over.pullback y)
  have hj := isGrpPullback_pullback G y
  have hA : IsAbelianScheme ((Over.pullback y).obj G) := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hG hj
  have hgA : SmoothOfRelativeDimension g ((Over.pullback y).obj G).hom :=
    (smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback hj.1 hgG
  obtain ⟨L, ⟨u⟩⟩ := GlobalTheory.HomDescentQb.exists_holUnif _ g hA hgA
  obtain ⟨h1, h2⟩ := GlobalTheory.UnifTangent.tangent_bijection u hgA
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.LiePull.exists_pushEquiv hj (𝟙_ _) y (Category.id_comp _).symm
  have he := GlobalTheory.PointUnif.isExp_push hj u h1 h2 Φ hΦ
  exact ⟨fun z => Φ (u.ex z), u.Λ, he, u.discrete, u.full,
    fun z => (map_eq_one_iff Φ Φ.injective).trans (u.ker z)⟩

end GlobalTheory.FibreExp
end
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.abelianScheme_oneFormFrame_and_square : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → HasFrame (OAff A.hom) ∧ CohomZeroIsConstants (OAff A.hom) ∧ IsAbelianScheme (A ⊗ A) ∧ SmoothOfRelativeDimension (g + g) (A ⊗ A).hom := by
  first | exact @GlobalTheory.AbCoh.basic_of_isAbelianScheme | exact GlobalTheory.AbCoh.basic_of_isAbelianScheme | (intros; apply GlobalTheory.AbCoh.basic_of_isAbelianScheme <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.abelianScheme_unobstructed_of_cohomology_structure : GlobalTheory.AbCoh.OStr → (∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → GlobalTheory.AbCoh.HasFrame (OAff A.hom) ∧ GlobalTheory.AbCoh.UConst A.hom ∧ GlobalTheory.AbCoh.PrimF A) → GlobalTheory.Published.AbelianUnobstructed := by
  first | exact @GlobalTheory.abelianUnobstructed_of_struct | exact GlobalTheory.abelianUnobstructed_of_struct | (intros; apply GlobalTheory.abelianUnobstructed_of_struct <;> assumption)
end

section

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu

theorem _root_.GlobalTheory.T.exists_theta_dieudonne_mod_frobenius_differentials :
    ∀ (p : ℕ) [Fact p.Prime] (T : GlobalTheory.Dieu.Theory p)
      (k : Type) [Field k] [CharP k p] [PerfectRing k p],
      ∃ θ : ∀ G : PDivGroup p k, T.M G →+ G.omega,
        ∀ G : PDivGroup p k,
          (∀ m, G.rigOfOmega (θ G m) = T.red G (T.V G m)) ∧
          Function.Surjective (θ G) ∧
          (∀ m, θ G m = 0 ↔ ∃ n, m = T.F G n) ∧
          (∀ (a : WittVector p k) m,
            θ G (WittVector.frobenius a • m) = WittVector.constantCoeff a • θ G m) ∧
          ∀ (H : PDivGroup p k) (f : G ⟶ H) (m : T.M H),
            θ G (T.map f m) = omegaMap G H f (θ H m) :=
  @GlobalTheory.Dieu.theta_exists
end

section

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu

namespace GlobalTheory.Dieu

theorem colength_range_map_ge (p : ℕ) [Fact p.Prime] (T : GlobalTheory.Dieu.Theory p) (k : Type) [Field k] [CharP k p]
    [PerfectRing k p] (G H : PDivGroup p k) (q : G ⟶ H) :
    (Module.finrank k (G.omega ⧸ LinearMap.range (omegaMap G H q)) : ℕ∞) ≤
        Module.length (WittVector p k) (T.M G ⧸ LinearMap.range (T.map q)) ∧
      (Module.finrank k (G.dual.Lie ⧸ LinearMap.range (lieMap H.dual G.dual (dualHom G H q))) : ℕ∞) ≤
        Module.length (WittVector p k) (T.M G ⧸ LinearMap.range (T.map q)) := by
  have hp : (p : k) = 0 := CharP.cast_eq_zero k p
  haveI : Module.Finite k G.RigExt := (GlobalTheory.T.finrank_rigidExtensions_eq_height_and_dim_add_dual p k hp G).2.1
  obtain ⟨θ, hθ⟩ := GlobalTheory.Dieu.theta_exists p T k
  have hred : ∀ m : T.M H, T.red G (T.map q m) = rigExtMap q (T.red H m) := fun m => by
    show T.base.red G trivial (T.base.smap trivial trivial (SemiHom.ofHom q) m) = _
    rw [T.base.red_smap, SemiHom.ofHom_rig]
  constructor
  · haveI : Module.Finite k G.omega :=
      Module.Finite.of_injective G.rigOfOmega (G.rigOfOmega_injective_of_eq_zero hp)
    obtain ⟨-, hsurj, -, hsemi, hnat⟩ := hθ G
    let Q := LinearMap.range (omegaMap G H q)
    refine (GlobalTheory.T.length_ge_finrank_of_semilinear_surjective p k (T.M G) (G.omega ⧸ Q) (WittVector.frobeniusEquiv p k)
      (Q.mkQ.toAddMonoidHom.comp (θ G)) (Q.mkQ_surjective.comp hsurj) (fun a n => ?_)
      (LinearMap.range (T.map q))).1 ?_
    · show Q.mkQ (θ G (WittVector.frobenius a • n)) = WittVector.constantCoeff a • Q.mkQ (θ G n)
      exact (congrArg Q.mkQ (hsemi a n)).trans (Q.mkQ.map_smul _ _)
    · rintro _ ⟨m, rfl⟩
      show Q.mkQ (θ G (T.map q m)) = 0
      rw [hnat, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact ⟨_, rfl⟩
  · haveI : Module.Finite k G.dual.Lie := Module.Finite.of_surjective (G.rigToLie hp) (G.rigToLie_surjective hp)
    let Q := LinearMap.range (lieMap H.dual G.dual (dualHom G H q))
    refine (GlobalTheory.T.length_ge_finrank_of_semilinear_surjective p k (T.M G) (G.dual.Lie ⧸ Q) (RingEquiv.refl _)
      ((Q.mkQ ∘ₗ G.rigToLie hp).toAddMonoidHom.comp (T.red G).toAddMonoidHom)
      ((Q.mkQ_surjective.comp (G.rigToLie_surjective hp)).comp (T.base.red_surjective G trivial))
      (fun a n => ?_) (LinearMap.range (T.map q))).1 ?_
    · show Q.mkQ (G.rigToLie hp (T.red G (a • n))) = WittVector.constantCoeff a • Q.mkQ (G.rigToLie hp (T.red G n))
      rw [LinearMap.map_smulₛₗ]
      exact (congrArg Q.mkQ ((G.rigToLie hp).map_smul _ _)).trans (Q.mkQ.map_smul _ _)
    · rintro _ ⟨m, rfl⟩
      show Q.mkQ (G.rigToLie hp (T.red G (T.map q m))) = 0
      rw [hred]
      have heq := rigToLie_rigExtMap hp q (T.red H m)
      apply (congrArg Q.mkQ heq).trans
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact ⟨_, rfl⟩

end GlobalTheory.Dieu
end

section

open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun Matrix

namespace GlobalTheory.JSW

theorem eq_zero_of_whit_eq_zero : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (φ : Sm E a),
    IsCuspForm φ → (∀ g, GlobalTheory.JSW.whit φ.1 g = 0) → φ = 0 := by
  intro E _ _ _ a φ hφ hW
  have hc : Continuous φ.1 := GlobalTheory.T.automorphicForm_GL_continuous E a φ hφ.1
  have hcusp := GlobalTheory.T.isCuspidal_of_isCuspForm' E a φ hφ
  have hl : GroundTheory.Automorphic.AutomorphicForm.IsLeftInvariant (K := E) (n := a) φ.1 :=
    fun γ g => hφ.1.left γ g
  let V : Subgroup (GL (Fin a) (Af E)) :=
    { carrier := {k | finRep E a k φ = φ}
      one_mem' := by simp
      mul_mem' := fun {x y} hx hy => by
        simp only [Set.mem_setOf_eq] at *
        rw [map_mul, Module.End.mul_apply, hy, hx]
      inv_mem' := fun {x} hx => by
        simp only [Set.mem_setOf_eq] at *
        conv_lhs => rw [← hx]
        rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] }
  have hV : ∃ V : OpenSubgroup (GroundTheory.Automorphic.AdelicGLn.FiniteAdelicGL E a),
      ∀ g, ∀ v ∈ V, φ.1 (g * GroundTheory.Automorphic.AutomorphicForm.finEmb E a v) = φ.1 g :=
    ⟨⟨V, hφ.1.level⟩, fun g v hv => by
      rw [GlobalTheory.FinConj.finEmb_eq_finGL]
      have : (finRep E a v φ).1 g = φ.1 g := by rw [show finRep E a v φ = φ from hv]
      exact this⟩
  apply Subtype.ext
  exact GroundTheory.Automorphic.MultiplicityOne.eq_zero_of_whittaker_eq_zero hc hl hcusp hV hW

end GlobalTheory.JSW
end

section

open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology

namespace GlobalTheory.CMModel

theorem exists_mem_valuation_cube_eq_Δ : ∀ (p : ℕ) (F : IntermediateField ℚ ℂ) (L : PeriodPair) (t : ℂ),
    p.Prime → p % 4 = 3 → 3 < p → Datum p F L t → ∀ V : ValuationSubring ℂ,
      ∃ A ∈ F, A ≠ 0 ∧ V.valuation A ^ 3 = V.valuation (latticeCurve L).Δ := by
  intro p F L t hp h4 h3 hD V
  obtain ⟨N, ι, _, T, hNodd, hN3, hNv, hcard, hst, hT⟩ := GlobalTheory.T.exists_galoisStable_torsion_family_ker p F L t hp h4 h3 hD V
  have hΔ0 := latticeCurve_Δ_ne_zero L
  obtain ⟨u, hu⟩ := IsAlgClosed.exists_pow_nat_eq (latticeCurve L).Δ (by norm_num : 0 < 12)
  have hu0 : u ≠ 0 := by rintro rfl; exact hΔ0 (by rw [← hu]; simp)
  have hvu : V.valuation u ≠ 0 := (Valuation.ne_zero_iff _).2 hu0
  have hvΔ : V.valuation (latticeCurve L).Δ = V.valuation u ^ 12 := by rw [← hu, map_pow]
  have hβ : (sqrtNegNat p).im ≠ 0 := by
    have : (0 : ℝ) < p := by exact_mod_cast hp.pos
    simp [sqrtNegNat, Real.sqrt_ne_zero'.2 this]
  have hN3' : ¬ 3 ∣ N := by omega
  have hU := fun i => GlobalTheory.T.valuation_weierstrassP_sub_two_mul_eq_sq L (sqrtNegNat p) u V N hD.mul hβ hvΔ.symm hNv hNodd hN3' (T i)
    (hT i).1 (hT i).2
  have hmem := (GlobalTheory.T.galoisStable_lattice_points_symmetric_mem F L ι T hD.g₂_mem hD.g₃_mem hst (fun i => (hT i).1)).2.2.2
    (fun i => (hU i).1)
  have hΔmem : (latticeCurve L).Δ ∈ F := by
    rw [latticeCurve_Δ]
    exact sub_mem (pow_mem hD.g₂_mem 3)
      (mul_mem (by simpa using natCast_mem F 27) (pow_mem hD.g₃_mem 2))
  set U := ∏ i, (L.weierstrassP (T i) - L.weierstrassP (2 * T i)) with hUdef
  obtain ⟨n, hn⟩ : ∃ n, N = 3 * n + 2 := ⟨N / 3, by omega⟩
  have hvU : V.valuation U = V.valuation u ^ (12 * n) * V.valuation u ^ 4 := by
    rw [hUdef, map_prod]
    simp_rw [fun i => (hU i).2]
    rw [Finset.prod_const, Finset.card_univ, hcard, ← pow_mul, ← pow_add]
    congr 1
    omega
  have hU0 : U ≠ 0 := by
    intro h
    rw [h, map_zero] at hvU
    exact (mul_ne_zero (pow_ne_zero _ hvu) (pow_ne_zero _ hvu)) hvU.symm
  refine ⟨U / (latticeCurve L).Δ ^ n, div_mem hmem (pow_mem hΔmem n),
    div_ne_zero hU0 (pow_ne_zero _ hΔ0), ?_⟩
  rw [map_div₀, map_pow, hvU, hvΔ, ← pow_mul, mul_comm 12 n, mul_div_cancel_left₀ _ (pow_ne_zero _ hvu),
    ← pow_mul]

end GlobalTheory.CMModel
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc


theorem _root_.GlobalTheory.T.formalSquaringPath_unique_constant_localRing : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (R : Type) [CommRing R], (∀ (c : R) (b : Sp R ⟶ S), IsPath G c b (triv G b)) ∧ (∀ (z : Sp R ⟶ G.left), z ≫ sqr G = z → z = (z ≫ G.hom) ≫ unitSec G) ∧ (∀ [IsLocalRing R], QuasiSeparated G.hom → ∀ (c : R), (∀ j, 1 ≤ j → IsUnit (c ^ j - 2)) → ∀ (b : Sp R ⟶ S) (ξ : Sp (PowerSeries R) ⟶ G.left), IsPath G c b ξ → ξ = triv G b) := by
  first | exact @GlobalTheory.Nef.triv_unique | exact GlobalTheory.Nef.triv_unique | (intros; apply GlobalTheory.Nef.triv_unique <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc


theorem _root_.GlobalTheory.T.genericFormalPath_eq_scaling_valuationRingPath : ∀ (k K E : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field K] [Algebra k K] [Field E] [Algebra k E] [Algebra K E] [IsScalarTower k K E] [FiniteDimensional K E] (C : Scheme.{0}) [Algebra k Γ(C, ⊤)] (x : Sp K ⟶ C), IsGenOver k x →
  ∀ (G : Over C) [GrpObj G], IsSemiAbelian G → ∀ (W : C.Modules) (r : ℕ) (i : W ⟶ Lie G) (V₀ : C.Opens) (s : Fin r → Γ(W, V₀)) (ρ : Place k E → Place k K), IsRes ρ → ∀ (p : Place k E) (g : Matrix (Fin r) (Fin r) K), LocFrame x s (ρ p) g → ∀ (w : Fin r → E) (u : E), u ≠ 0 → p.1 u = nrm p ((g.map (algebraMap K E)).mulVec w) → ∀ ξ, IsPath G 2 (spMap (algebraMap K E) ≫ x) ξ → HasTan G (spMap (algebraMap K E) ≫ x) ξ (fun j => i.app V₀ (s j)) w → ∃ (b : Sp p.O ⟶ C) (ζ : Sp (PowerSeries p.O) ⟶ G.left), spMap p.O.subtype ≫ b = spMap (algebraMap K E) ≫ x ∧ IsPath G 2 b ζ ∧ ξ = spMap (sc p u) ≫ ζ := by
  first | exact @GlobalTheory.Nef.genPath_scaling | exact GlobalTheory.Nef.genPath_scaling | (intros; apply GlobalTheory.Nef.genPath_scaling <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.baseFrameBorel_acts_extremalVector_by_weight : ∀ (D : D7) (θ : InfFam D) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (w : D.what₂.Tau → Fin V.rank → ℤ) (v : M.Vec), IsInfFam θ → HolShape M → WtIs M w → IsExtVec M v → ∀ τ, SmoothVec (lieH (gramAt D V τ)) (M.rep τ) (v τ : M.H τ) ∧ ∀ a c : Fin V.rank, a ≤ c → dRepC (gramAt D V τ) (M.rep τ) (x0Mat M τ * Matrix.single a c 1 * (x0Mat M τ)⁻¹) (v τ : M.H τ) = if a = c then (w τ a : ℂ) • (v τ : M.H τ) else 0 := by
  first | exact @GlobalTheory.HolDict.VKill.borel_extVec | exact GlobalTheory.HolDict.VKill.borel_extVec | (intros; apply GlobalTheory.HolDict.VKill.borel_extVec <;> assumption)
end
