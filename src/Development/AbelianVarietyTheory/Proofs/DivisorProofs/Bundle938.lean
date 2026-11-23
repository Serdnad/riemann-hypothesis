module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHodgeSequenceFirstMapLattice
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle017
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle021
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle232
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle888
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperH2ExteriorSquareIso
public import Formalism.LocalToGlobal.Divisibility.GoodPartHermitianSpec
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle915
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle022
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle916
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle024
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle220
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle917
import Mathlib.Algebra.AffineMonoid.Basic
import Mathlib.Algebra.AffineMonoid.UniqueSums
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
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.HasLevelStd
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle001

@[expose] public section

section

open CategoryTheory Opposite Matrix GlobalTheory GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

theorem _root_.GlobalTheory.T.existsUnique_muPInfinity_hodgeTate_lattice_map : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ g : latt (PDivGroup.mu p O) →ₗ[Ainf p O] latt (const p O), (∀ m m' : latt (PDivGroup.mu p O), (∀ t, m'.1 t = WittVector.frobenius (m.1 t)) → ∀ t, (g m').1 t = WittVector.frobenius ((g m).1 t)) → ∃! f : const p O ⟶ PDivGroup.mu p O, lattMap f = g := by
  first | exact @GlobalTheory.PDivLat.ConstMu.existsUnique_lattMap | exact GlobalTheory.PDivLat.ConstMu.existsUnique_lattMap | (intros; apply GlobalTheory.PDivLat.ConstMu.existsUnique_lattMap <;> assumption)
end

section

open CategoryTheory Opposite Matrix GlobalTheory GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

theorem _root_.GlobalTheory.T.hodgeTate_separates_dual_lie_ghostComponent : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ G : PDivGroup p O, HasDatum hε G → (∀ x : G.dual.Lie, (∀ t, x (hodgeTate G t) = 0) → x = 0) ∧ (∀ x : G.dual.Lie, ∃ y : latt G, ∀ t, WittVector.fontaineTheta O p (y.1 t) = x (hodgeTate G t)) := by
  first | exact @GlobalTheory.LieHodgeTate.main | exact GlobalTheory.LieHodgeTate.main | (intros; apply GlobalTheory.LieHodgeTate.main <;> assumption)
end

section

open CategoryTheory Opposite Matrix GlobalTheory GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

theorem _root_.GlobalTheory.T.exists_hodgeSequence_first_map_lattice : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ (G : PDivGroup p O), HasDatum hε G → ∀ (M : Type) [AddCommGroup M] [Module O M] (r : latt G →ₛₗ[WittVector.fontaineTheta O p] M) (π : M →ₗ[O] G.dual.Lie), Function.Surjective r → (∀ m, r m = 0 ↔ ∃ n, m = xi ε • n) → (∀ (y : latt G) t, π (r y) (hodgeTate G t) = WittVector.fontaineTheta O p (y.1 t)) → ∃ ι : G.omega →ₗ[O] M, Function.Injective ι ∧ Function.Exact ι π ∧ (∀ (χ : G.dual.Tate) (y : latt G), (∀ t, y.1 t = Sandwich.mu ε * ofPadic p O (epsPairing hε G t χ)) → ι (dlog G χ) = r y) := by
  first | exact @GlobalTheory.LattIota.iota_exists | exact GlobalTheory.LattIota.iota_exists | (intros; apply GlobalTheory.LattIota.iota_exists <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix

theorem _root_.GlobalTheory.T.complexUniformisation_of_complexBaseChange : ∀ (O : Type) [Ring O] (bar : O → O) (g : ℕ) (ρ : O →+* Matrix (Fin g) (Fin g) ℂ) (R : Type) [CommRing R] (σ : R →+* ℂ) (Λ : Type) (F : Fam R O Λ g) (N : ℕ) (C : ∀ D' : PLat O bar, (Λ → D'.La) → Prop) (F' : Fam ℂ O Λ g), IsBC F' F σ → Nonempty (Unif F' (RingHom.id ℂ) ρ N C) → Nonempty (Unif F σ ρ N C) := by
  first | exact @GlobalTheory.PELU.unif_of_isBC | exact GlobalTheory.PELU.unif_of_isBC | (intros; apply GlobalTheory.PELU.unif_of_isBC <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix

theorem _root_.GlobalTheory.T.isFineModuliAtComplexEmbedding_complexBaseChange : ∀ (O : Type) [Ring O] (bar : O → O) (g : ℕ) (ρ : O →+* Matrix (Fin g) (Fin g) ℂ) (R : Type) [CommRing R] (σ : R →+* ℂ) (Λ : Type) (F : Fam R O Λ g) (N : ℕ) (C : ∀ D' : PLat O bar, (Λ → D'.La) → Prop) (F' : Fam ℂ O Λ g), IsBC F' F σ → FineAt F σ ρ N C → FineAt F' (RingHom.id ℂ) ρ N C := by
  first | exact @GlobalTheory.PELU.fineAt_of_isBC | exact GlobalTheory.PELU.fineAt_of_isBC | (intros; apply GlobalTheory.PELU.fineAt_of_isBC <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.DeRham

namespace GlobalTheory.AbCoh

theorem isAffineOpen_preimage_of_isPullback (R R' : Type) [CommRing R] [CommRing R'] [Algebra R R']
    (X X' : Scheme.{0}) (s : X ⟶ Sp R) (s' : X' ⟶ Sp R') (φ : X' ⟶ X)
    (h : IsPullback φ s' s (spMap (algebraMap R R'))) (U : X.affineOpens) : IsAffineOpen (φ ⁻¹ᵁ U.1) := by
  haveI : IsAffineHom φ := MorphismProperty.of_isPullback (P := @IsAffineHom) h.flip inferInstance
  exact U.2.preimage φ

theorem exists_equiv_globForm_baseChange : ∀ (R R' : Type) [CommRing R] [CommRing R'] [Algebra R R'] (X X' : Scheme.{0}) (s : X ⟶ Sp R) (s' : X' ⟶ Sp R') (φ : X' ⟶ X) (h : IsPullback φ s' s (spMap (algebraMap R R'))), HasFrame (OAff s) → CohomZeroIsConstants (OAff s) → HasFrame (OAff s') → CohomZeroIsConstants (OAff s') → Flat s' → Surjective s' → ∃ e : R' ⊗[R] GlobForm s ≃ₗ[R'] GlobForm s', ∀ c, e (1 ⊗ₜ c) = GlobalTheory.CechDR.pullForm h.w c := by
  intro R R' _ _ _ X X' s s' φ h hF hC hF' hC' hfl hsu
  have hb : Function.Bijective (liftSemi (pullForm h.w)) :=
    GlobalTheory.T.bijective_of_lTensor_bijective_of_flat_family R' _ _ (liftSemi (pullForm h.w)) X.affineOpens (fun U ↦ Sec s' (φ ⁻¹ᵁ U.1))
      (fun U ↦ GlobalTheory.T.flat_sections_affineOpen_of_flat_scheme R' X' s' hfl ⟨_, isAffineOpen_preimage_of_isPullback R R' X X' s s' φ h U⟩)
      (GlobalTheory.T.exists_affineOpen_map_maximal_proper R' X X' s' φ hsu)
      (fun U ↦ GlobalTheory.T.lTensor_liftBaseChange_globalOneForms_affinePreimage_bijective R R' X X' s s' φ h hF hC hF' hC' U
        (isAffineOpen_preimage_of_isPullback R R' X X' s s' φ h U))
  refine ⟨LinearEquiv.ofBijective _ hb, fun c ↦ ?_⟩
  rw [LinearEquiv.ofBijective_apply, liftSemi_tmul, one_smul]

end GlobalTheory.AbCoh
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.hyper_h2_exterior_square_iso : ∀ (R : Type) [CommRing R] (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R), HasFrame F → CohomZeroIsConstants F → Closed1 F = ⊤ → Function.Surjective (toO F) → WedgeO F → (∀ a, cupHyp F a a = 0) → ∃ e : ⋀[R]^2 (Hyp1 F) ≃ₗ[R] Hyp2 F, ∀ a b, e (exteriorPower.ιMulti R 2 ![a, b]) = cupHyp F a b := by
  first | exact @GlobalTheory.AbCoh.exists_wedge_hyp_equiv | exact GlobalTheory.AbCoh.exists_wedge_hyp_equiv | (intros; apply GlobalTheory.AbCoh.exists_wedge_hyp_equiv <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ArithmeticCylinders GlobalTheory.BadCount Module

theorem _root_.GlobalTheory.T.finrank_eigen_inf_ker_le_of_semidirect_split : ∀ (G Γ V : Type) [Group G] [Fintype G] [Group Γ] [Fintype Γ] [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (π : Γ →* G) (ι : G →* Γ), IsSplit π ι → ∀ (ρ : Representation ℂ Γ V) (P : Subgroup G) (lam : P →* ℂˣ) (lamb : P.comap π →* ℂˣ), (∀ γ : P.comap π, lamb γ = lam ⟨π γ, γ.2⟩) → ∀ (H : Fin 2 → Subgroup G) (n : Fin 2 → ℕ) (e : MonoidAlgebra ℂ G) (b : Fin 2 → MonoidAlgebra ℂ G) (s : Fin 2 → ℝ) (c : ℝ), (∀ k, EmbReg ρ ((H k).comap π) (n k)) → (∀ k, (n k : ℝ) * Nat.card ((H k).comap π) ≤ c * Nat.card (P.comap π) * finrank ℂ (eig ρ (P.comap π) lamb)) → (∀ k, b k * b k = b k) → (∀ k a, b k * a = a * b k) → 1 - e = b 0 + b 1 - b 0 * b 1 → (∀ k g, (b k * Formalism.L2.DIV.lvlIdem P lam).coeff g ≠ 0 → g ∈ H k) → (∀ k, (b k * Formalism.L2.DIV.lvlIdem P lam).coeff 1 = (s k : ℂ) / (Nat.card P : ℂ)) → (finrank ℂ (eig ρ (P.comap π) lamb ⊓ LinearMap.ker (Representation.asAlgebraHom (ρ.comp ι : Representation ℂ G V) e) : Submodule ℂ V) : ℝ) ≤ c * (s 0 + s 1) * finrank ℂ (eig ρ (P.comap π) lamb) := by
  first | exact @GlobalTheory.BadCount.finrank_eig_inf_ker_le_of_isSplit | exact GlobalTheory.BadCount.finrank_eig_inf_ker_le_of_isSplit | (intros; apply GlobalTheory.BadCount.finrank_eig_inf_ker_le_of_isSplit <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.small_extension_primitive_lift : ∀ (R R' R₀ : Type) [CommRing R] [CommRing R'] [CommRing R₀] (t : R) (σ : R →+* R') (σ₀ : R →+* R₀) (g : ℕ) (A : Over (Sp R)) [GrpObj A] (A' : Over (Sp R')) [GrpObj A'] (A₀ : Over (Sp R₀)) [GrpObj A₀] (φ : A'.left ⟶ A.left) (φ₀ : A₀.left ⟶ A.left) (h : IsGrpPullback A' A (spMap σ) φ) (h₀ : IsGrpPullback A₀ A (spMap σ₀) φ₀), SmallExt t σ σ₀ → IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → StructureSheafH1Primitive A' → NoPrimitiveStructureSheafH2 A₀ → Function.Surjective (pullHO1 h.1.w) := by
  first | exact @GlobalTheory.AbCoh.pullHO1_surjective_of_smallExt | exact GlobalTheory.AbCoh.pullHO1_surjective_of_smallExt | (intros; apply GlobalTheory.AbCoh.pullHO1_surjective_of_smallExt <;> assumption)
end

section

open GlobalTheory.FinGL Formalism.L2.DIV Module

theorem _root_.GlobalTheory.T.levi_whittaker_eq_one_of_cuspidal : ∀ (F : Type) [Field F] [Fintype F] (ψ : AddChar F ℂ), ψ ≠ 1 → ∀ (r : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (b : Fin r → ℕ) (σ : Representation ℂ (blockTri (κ := F) b) V), IsCuspDatum b σ → leviWh ψ b σ = 1 := by
  first | exact @GlobalTheory.FinGL.LeviWh.leviWh_eq_one | exact GlobalTheory.FinGL.LeviWh.leviWh_eq_one | (intros; apply GlobalTheory.FinGL.LeviWh.leviWh_eq_one <;> assumption)
end

section

open scoped Classical

open MvPolynomial in
theorem GlobalTheory.JSW.PieriDeterminant.vdm_ne (n : ℕ) : Matrix.det (Matrix.of fun i j : Fin n => (X i : MvPolynomial (Fin n) ℤ) ^ (n - 1 - (j : ℕ))) ≠ 0 := by
  have h : (Matrix.of fun i j : Fin n => (X i : MvPolynomial (Fin n) ℤ) ^ (n - 1 - (j : ℕ))) =
      (Matrix.vandermonde (fun i => (X i : MvPolynomial (Fin n) ℤ))).submatrix id Fin.revPerm := by
    ext i j
    simp only [Matrix.of_apply, Matrix.submatrix_apply, Matrix.vandermonde_apply, id, Fin.revPerm_apply, Fin.val_rev]
    rw [show n - 1 - (j : ℕ) = n - ((j : ℕ) + 1) by omega]
  rw [h, Matrix.det_permute']
  refine mul_ne_zero (by simp [Units.ne_zero]) ?_
  rw [Matrix.det_vandermonde_ne_zero_iff]
  exact MvPolynomial.X_injective

namespace GlobalTheory.JSW.PieriDeterminant

theorem adj {n : ℕ} (l : Fin n → ℕ) (hl : Antitone l) (J : Finset (Fin n)) :
    ∀ d : ℕ, ∀ a b : Fin n, (b : ℕ) = a + d + 1 → l a = l b → a ∉ J → b ∈ J →
      ∃ a' b' : Fin n, (b' : ℕ) = a' + 1 ∧ l a' = l b' ∧ a' ∉ J ∧ b' ∈ J := by
  intro d
  induction d with
  | zero => intro a b h1 h2 h3 h4; exact ⟨a, b, by omega, h2, h3, h4⟩
  | succ d ih =>
    intro a b h1 h2 h3 h4
    have hc : (a : ℕ) + 1 < n := by have := b.isLt; omega
    let c : Fin n := ⟨a + 1, hc⟩
    have hac : a ≤ c := by show (a : ℕ) ≤ a + 1; omega
    have hcb : c ≤ b := by show (a : ℕ) + 1 ≤ b; omega
    have hlc : l c = l a := le_antisymm (hl hac) (h2 ▸ hl hcb)
    by_cases hcJ : c ∈ J
    · exact ⟨a, c, rfl, hlc.symm, h3, hcJ⟩
    · exact ih c b (by show (b : ℕ) = a + 1 + d + 1; omega) (hlc.trans h2) hcJ h4

theorem det_zero {n : ℕ} (l : Fin n → ℕ) (hl : Antitone l) (J : Finset (Fin n))
    (hJ : ¬ Antitone (l + (fun i => if i ∈ J then 1 else 0))) :
    Matrix.det (Matrix.of fun i k : Fin n => (MvPolynomial.X i : MvPolynomial (Fin n) ℤ) ^
      ((l k + n - 1 - (k : ℕ)) + if k ∈ J then 1 else 0)) = 0 := by
  obtain ⟨a, b, hab, hlt⟩ : ∃ a b : Fin n, a ≤ b ∧ ((l + (fun i => if i ∈ J then 1 else 0) : Fin n → ℕ)) a <
      ((l + (fun i => if i ∈ J then 1 else 0) : Fin n → ℕ)) b := by
    simp only [Antitone, not_forall, not_le] at hJ
    obtain ⟨a, b, h1, h2⟩ := hJ; exact ⟨a, b, h1, h2⟩
  simp only [Pi.add_apply] at hlt
  have hla := hl hab
  have hA : a ∉ J := by intro h; simp only [h, if_true] at hlt; split_ifs at hlt <;> omega
  have hB : b ∈ J := by by_contra h; simp only [h, if_false] at hlt; split_ifs at hlt <;> omega
  have hE : l a = l b := by simp only [hA, hB, if_true, if_false] at hlt; omega
  have hne : a ≠ b := by rintro rfl; exact hA hB
  obtain ⟨a', b', h1, h2, h3, h4⟩ :=
    adj l hl J ((b : ℕ) - a - 1) a b (by have : (a : ℕ) < b := lt_of_le_of_ne hab (fun h => hne (Fin.ext h)); omega) hE hA hB
  refine Matrix.det_zero_of_column_eq (i := a') (j := b') (fun h => by rw [h] at h1; omega) (fun i => ?_)
  simp only [Matrix.of_apply, h3, h4, if_true, if_false]
  congr 1
  have := b'.isLt
  omega

end GlobalTheory.JSW.PieriDeterminant

open MvPolynomial in
theorem GlobalTheory.JSW.esymm_mul_schur : ∀ (n : ℕ) (l : Fin n → ℕ), Antitone l → ∀ j ≤ n, MvPolynomial.esymm (Fin n) ℤ j * GlobalTheory.JSW.schur n l = ∑ J ∈ (Finset.univ : Finset (Finset (Fin n))).filter (fun J => J.card = j ∧ Antitone (l + (fun i => if i ∈ J then 1 else 0))), GlobalTheory.JSW.schur n (l + (fun i => if i ∈ J then 1 else 0)) := by
  intro n l hl j _
  apply mul_right_cancel₀ (GlobalTheory.JSW.PieriDeterminant.vdm_ne n)
  have h1 := GlobalTheory.T.esymm_mul_det_pow_eq_sum_det_shifted n (fun k => l k + n - 1 - k) j
  beta_reduce at h1
  calc MvPolynomial.esymm (Fin n) ℤ j * GlobalTheory.JSW.schur n l * _
      = ∑ J ∈ (Finset.univ : Finset (Finset (Fin n))).filter (fun J => J.card = j),
          Matrix.det (Matrix.of fun i k : Fin n => (MvPolynomial.X i : MvPolynomial (Fin n) ℤ) ^
            ((l k + n - 1 - (k : ℕ)) + if k ∈ J then 1 else 0)) := by
        rw [mul_assoc, GlobalTheory.T.schur_mul_vandermonde_det_eq_det n l hl, h1]
    _ = ∑ J ∈ ((Finset.univ : Finset (Finset (Fin n))).filter (fun J => J.card = j)).filter
          (fun J => Antitone (l + (fun i => if i ∈ J then 1 else 0))),
          Matrix.det (Matrix.of fun i k : Fin n => (MvPolynomial.X i : MvPolynomial (Fin n) ℤ) ^
            ((l k + n - 1 - (k : ℕ)) + if k ∈ J then 1 else 0)) := by
        refine (Finset.sum_filter_of_ne fun J _ hJ => ?_).symm
        by_contra h
        exact hJ (GlobalTheory.JSW.PieriDeterminant.det_zero l hl J h)
    _ = ∑ J ∈ ((Finset.univ : Finset (Finset (Fin n))).filter (fun J => J.card = j)).filter
          (fun J => Antitone (l + (fun i => if i ∈ J then 1 else 0))),
          GlobalTheory.JSW.schur n (l + (fun i => if i ∈ J then 1 else 0)) *
            Matrix.det (Matrix.of fun i j : Fin n => (MvPolynomial.X i : MvPolynomial (Fin n) ℤ) ^ (n - 1 - (j : ℕ))) := by
        refine Finset.sum_congr rfl fun J hJ => ?_
        rw [GlobalTheory.T.schur_mul_vandermonde_det_eq_det n _ (Finset.mem_filter.1 hJ).2]
        have e : ∀ k : Fin n, ((l + (fun i => if i ∈ J then 1 else 0) : Fin n → ℕ)) k + n - 1 - (k : ℕ) =
            (l k + n - 1 - (k : ℕ)) + if k ∈ J then 1 else 0 := by
          intro k; have := k.isLt; simp only [Pi.add_apply]; split_ifs <;> omega
        simp only [e]
    _ = _ := by rw [Finset.filter_filter, Finset.sum_mul]
end

section

open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
open GlobalTheory.LatVal (Sz)
open GlobalTheory.LatJet (EisExp IsEis FR)
open GlobalTheory.CMVal (OF Af lattice IsCMType)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (IsDefSum IsEisValue polydisc)

theorem _root_.GlobalTheory.T.exists_equiv_cmType_realEmbeddings : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] (φ : I → E →+* ℂ), IsCMType φ → ∃ e : I ≃ Emb (FR E), ∀ i (x : FR E), φ i (x : E) = ((e i x : ℝ) : ℂ) := by
  first | exact @GlobalTheory.CMTypeEmb.exists_equiv | exact GlobalTheory.CMTypeEmb.exists_equiv | (intros; apply GlobalTheory.CMTypeEmb.exists_equiv <;> assumption)
end
