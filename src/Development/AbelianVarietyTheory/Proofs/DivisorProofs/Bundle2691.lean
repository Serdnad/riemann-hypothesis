module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsEqnIffGeneratesAtInv
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.TwistingSheafOneChartEqPreimageStandardChart
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2635
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmulEqSumVecMulVecSpanningFamily
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle681
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2636
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle003
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle035
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle004
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AmpleOnAbelianBase
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FirstIndexEqOfUnfolded
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FnAlgClosedOfFixedPoints
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemRiemannRochSpaceIffRegularAtEverywhere
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle027
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle035
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle064
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1409
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1410
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle026
import Development.AbelianVarietyTheory.Definitions.Foundations.IsProbabilityMeasureMuPart
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle001
import Mathlib.Tactic.Polynomial.Basic
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle063
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle036
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle001
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.DivMemOfForallPowSuccDivPowMem

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.ArInt GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.VertForm GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.TrueCx Filter Topology
open scoped Classical

namespace GlobalTheory.LatChain.CanTens

variable {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {q : X ⟶ Sp k}

theorem presents_dual {D : CartierDiv X} {L : LB X} {r : L.ι → X.functionFieldˣ} (h : Presents D L r) :
    Presents (-D) (CechPic.dual L) fun i => (r i)⁻¹ := by
  refine ⟨isLB_dual h.isLB, fun i j hij => ?_, fun i x hx => (h.isEqn i x hx).neg⟩
  change (((r i)⁻¹ : X.functionFieldˣ) : X.functionField) =
    fnOf (L.U i ⊓ L.U j) hij ((L.g i j)⁻¹ : Γ(X, L.U i ⊓ L.U j)ˣ) * ((r j)⁻¹ : X.functionFieldˣ)
  rw [Units.val_inv_eq_inv_val, Units.val_inv_eq_inv_val, map_units_inv, h.isRatSec i j hij, mul_inv]

end GlobalTheory.LatChain.CanTens

end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical

open CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.TrueGeo

namespace GlobalTheory.PullCoordComb

def evalF {X : Scheme.{0}} (L : LB X) (i : L.ι) : LB.Sec L →+ Γ(X, L.U i) where
  toFun s := s.f i
  map_zero' := rfl
  map_add' _ _ := rfl

theorem sum_smul_f {X : Scheme.{0}} {L : LB X} {n : ℕ} (a : Fin n → Γ(X, ⊤)) (s : Fin n → LB.Sec L)
    (i : L.ι) : (∑ k, a k • s k).f i = ∑ k, resG X le_top (a k) * (s k).f i := by
  change evalF L i (∑ k, a k • s k) = _

  rw [map_sum]
  rfl

theorem linComb_ratio_and_vanish : ∀ (K Ω : Type) [Field K] [NumberField K] [Field Ω] [Algebra K Ω] (m : ℕ) (y : Fin (m + 1) → Ω) (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp (𝓞 K)) (g : X ⟶ PSpace (𝓞 K) m) (ψ : Ω →+* X.functionField),
    (∀ a : 𝓞 K, ψ (algebraMap K Ω (a : K)) = fnOf ⊤ (TopologicalSpace.Opens.mem_top _) (algX p ⊤ a)) →
    (∀ (k l : Fin (m + 1)) (i : ((ProjSpace.O1 (𝓞 K) m).pull g).ι) (h : genericPoint X ∈ ((ProjSpace.O1 (𝓞 K) m).pull g).U i),
        ψ (y k) * fnOf _ h ((GlobalTheory.Cartier.secPull (ProjSpace.coord (𝓞 K) m l) g).f i) =
          ψ (y l) * fnOf _ h ((GlobalTheory.Cartier.secPull (ProjSpace.coord (𝓞 K) m k) g).f i)) →
    (∀ (lam : Fin (m + 1) → 𝓞 K) (l : Fin (m + 1)) (i : ((ProjSpace.O1 (𝓞 K) m).pull g).ι) (h : genericPoint X ∈ ((ProjSpace.O1 (𝓞 K) m).pull g).U i),
        ψ (y l) * fnOf _ h ((∑ k, algX p ⊤ (lam k) • GlobalTheory.Cartier.secPull (ProjSpace.coord (𝓞 K) m k) g).f i) =
          ψ (∑ k, algebraMap K Ω (lam k : K) * y k) * fnOf _ h ((GlobalTheory.Cartier.secPull (ProjSpace.coord (𝓞 K) m l) g).f i)) ∧
    (y ≠ 0 → ∀ lam : Fin (m + 1) → 𝓞 K, ∑ k, algebraMap K Ω (lam k : K) * y k = 0 →
        ∑ k, algX p ⊤ (lam k) • GlobalTheory.Cartier.secPull (ProjSpace.coord (𝓞 K) m k) g = 0) := by
  intro K Ω _ _ _ _ m y X _ p g ψ hbase hratio
  have hA : ∀ (lam : Fin (m + 1) → 𝓞 K) (l : Fin (m + 1)) (i : ((ProjSpace.O1 (𝓞 K) m).pull g).ι)
      (h : genericPoint X ∈ ((ProjSpace.O1 (𝓞 K) m).pull g).U i),
      ψ (y l) * fnOf _ h ((∑ k, algX p ⊤ (lam k) • GlobalTheory.Cartier.secPull (ProjSpace.coord (𝓞 K) m k) g).f i) =
        ψ (∑ k, algebraMap K Ω (lam k : K) * y k) * fnOf _ h ((GlobalTheory.Cartier.secPull (ProjSpace.coord (𝓞 K) m l) g).f i) := by
    intro lam l i h

    rw [sum_smul_f, map_sum, Finset.mul_sum, map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_mul, fnOf_resG, ← hbase, map_mul, mul_left_comm (ψ (y l)), hratio l k i h]
    ring
  refine ⟨hA, fun hy lam hsum => ?_⟩
  obtain ⟨k₀, hk₀⟩ : ∃ k₀, y k₀ ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hy (funext hc)
  apply GlobalTheory.LB.f_injective
  funext i
  apply GlobalTheory.Cartier.fn_ext
  intro hU
  have e := hA lam k₀ i hU
  rw [hsum, map_zero, zero_mul] at e
  have hψ : ψ (y k₀) ≠ 0 := (map_ne_zero ψ).2 hk₀
  rw [GlobalTheory.LB.zero_f, map_zero]
  exact (mul_eq_zero.1 e).resolve_left hψ

end GlobalTheory.PullCoordComb
end

section

open IsLocalRing GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.Poinc

theorem _root_.GlobalTheory.T.exists_smoothCone_interior_definite_balancedForm : ∀ (O : Type) [CommRing O] (bar : O → O) (φ : InvFun O) (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X] [Module.Free ℤ X] [Module.Finite ℤ X], IsPolFanOn bar φ X → ∀ β ∈ balForms bar X, (∀ x, x ≠ 0 → 0 < β x x) → ∃ (r : ℕ) (γ : Fin r → LinearMap.BilinForm ℤ X) (k : ℕ) (c : Fin r → ℕ), IsCone bar φ γ ∧ 0 < k ∧ (∀ j, 0 < c j) ∧ k • β = ∑ j, c j • γ j := by
  first | exact @GlobalTheory.Poinc.Cover.exists_cone | exact GlobalTheory.Poinc.Cover.exists_cone | (intros; apply GlobalTheory.Poinc.Cover.exists_cone <;> assumption)
end

section

open IsLocalRing GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.Poinc

theorem _root_.GlobalTheory.T.smoothCone_face_of_interior_common_point : ∀ (O : Type) [CommRing O] (bar : O → O) (φ : InvFun O) (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X], IsPolFanOn bar φ X → ∀ (r r' : ℕ) (γ : Fin r → LinearMap.BilinForm ℤ X) (γ' : Fin r' → LinearMap.BilinForm ℤ X), IsCone bar φ γ → IsCone bar φ γ' → ∀ (c : Fin r → ℕ) (c' : Fin r' → ℕ), (∀ j, 0 < c j) → ∑ j, c j • γ j = ∑ j, c' j • γ' j → ∀ j, ∃ j', γ j = γ' j' := by
  first | exact @GlobalTheory.Poinc.intCone_face | exact GlobalTheory.Poinc.intCone_face | (intros; apply GlobalTheory.Poinc.intCone_face <;> assumption)
end

section

open IsLocalRing GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.Poinc

theorem _root_.GlobalTheory.T.exists_pos_combination_smoothCone_symmIntForm : ∀ (g : ℕ) (φ : InvFun ℤ), IsPolFan id g φ → ∀ r : ℕ, r ≤ g → ∀ b : LinearMap.BilinForm ℤ (Fin r → ℤ), (∀ x y, b x y = b y x) → toReal b ∈ psdCone (bar := (id : ℤ → ℤ)) (X := (Fin r → ℤ)) → ∃ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ (Fin r → ℤ)) (cf : Fin m → ℕ), IsCone id φ γ ∧ (∀ j, 0 < cf j) ∧ b = ∑ j, cf j • γ j := by
  first | exact @GlobalTheory.ConeInterior.exists_pos_comb_int | exact GlobalTheory.ConeInterior.exists_pos_comb_int | (intros; apply GlobalTheory.ConeInterior.exists_pos_comb_int <;> assumption)
end

section

open IsLocalRing GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.Poinc

namespace GlobalTheory.Poinc.SumSqFunctional

open Matrix

def quadR {r : ℕ} (L : Matrix (Fin r) (Fin r) ℤ) (v : Fin r → ℝ) : ℝ :=
  ∑ i, ∑ j, v i * (L i j : ℝ) * v j

lemma quadR_eq {r : ℕ} (L : Matrix (Fin r) (Fin r) ℤ) (v : Fin r → ℝ) :
    star v ⬝ᵥ (L.map (Int.cast : ℤ → ℝ)) *ᵥ v = quadR L v := by
  simp [quadR, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_comm, mul_left_comm, mul_assoc]

lemma quadR_intCast {r : ℕ} (L : Matrix (Fin r) (Fin r) ℤ) (w : Fin r → ℤ) :
    quadR L (fun i => (w i : ℝ)) = ((w ⬝ᵥ L *ᵥ w : ℤ) : ℝ) := by
  simp [quadR, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_comm, mul_left_comm, mul_assoc]

lemma continuous_quadR {r : ℕ} (L : Matrix (Fin r) (Fin r) ℤ) : Continuous (quadR L) := by
  unfold quadR; fun_prop

lemma exists_int_multiple {r : ℕ} (q : Fin r → ℚ) :
    ∃ d : ℕ, 0 < d ∧ ∃ w : Fin r → ℤ, ∀ i, (w i : ℚ) = d * q i := by
  refine ⟨∏ i, (q i).den, Finset.prod_pos (fun i _ => (q i).den_pos), ?_⟩
  have : ∀ i, ∃ z : ℤ, (z : ℚ) = ((∏ j, (q j).den : ℕ) : ℚ) * q i := by
    intro i
    obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem (fun j => (q j).den) (Finset.mem_univ i)
    refine ⟨k * (q i).num, ?_⟩
    rw [hk]; push_cast
    rw [mul_comm ((q i).den : ℚ) (k : ℚ), mul_assoc, Rat.den_mul_eq_num]
  choose w hw using this
  exact ⟨w, hw⟩

lemma quadR_pos_rat {r : ℕ} (L : Matrix (Fin r) (Fin r) ℤ)
    (hp : ∀ v : Fin r → ℤ, v ≠ 0 → 0 < v ⬝ᵥ L *ᵥ v) (q : Fin r → ℚ) (hq : q ≠ 0) :
    0 < quadR L (fun i => (q i : ℝ)) := by
  obtain ⟨d, hd, w, hw⟩ := exists_int_multiple q
  have hwR : ∀ i, (w i : ℝ) = d * (q i : ℝ) := by
    intro i; have := congrArg (Rat.cast : ℚ → ℝ) (hw i); push_cast at this; exact this
  have hw0 : w ≠ 0 := by
    intro h; apply hq; funext i
    have := hw i; rw [h] at this; simp at this
    rcases this with h1 | h1
    · exact absurd h1 (by exact_mod_cast hd.ne')
    · exact h1
  have h1 := hp w hw0
  have h2 : quadR L (fun i => (w i : ℝ)) = (d : ℝ) ^ 2 * quadR L (fun i => (q i : ℝ)) := by
    simp only [quadR, hwR, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have h3 : 0 < quadR L (fun i => (w i : ℝ)) := by
    rw [quadR_intCast]; exact_mod_cast h1
  rw [h2] at h3
  have hd2 : (0 : ℝ) < (d : ℝ) ^ 2 := by positivity
  exact pos_of_mul_pos_right h3 hd2.le

lemma quadR_nonneg {r : ℕ} (L : Matrix (Fin r) (Fin r) ℤ)
    (hp : ∀ v : Fin r → ℤ, v ≠ 0 → 0 < v ⬝ᵥ L *ᵥ v) (x : Fin r → ℝ) : 0 ≤ quadR L x := by
  have hdense : DenseRange (Pi.map (fun (_ : Fin r) (t : ℚ) => (t : ℝ))) :=
    DenseRange.piMap (fun _ => Rat.denseRange_cast)
  have hcl : IsClosed {x : Fin r → ℝ | 0 ≤ quadR L x} :=
    isClosed_le continuous_const (continuous_quadR L)
  have hsub : Set.range (Pi.map (fun (_ : Fin r) (t : ℚ) => (t : ℝ))) ⊆ {x | 0 ≤ quadR L x} := by
    rintro _ ⟨q, rfl⟩
    by_cases hq : q = 0
    · subst hq; simp [quadR]
    · exact (quadR_pos_rat L hp q hq).le
  have := hcl.closure_subset_iff.mpr hsub
  rw [hdense.closure_range] at this
  exact this (Set.mem_univ x)

theorem posDef_of_pos_int {r : ℕ} (L : Matrix (Fin r) (Fin r) ℤ) (hs : Lᵀ = L)
    (hp : ∀ v : Fin r → ℤ, v ≠ 0 → 0 < v ⬝ᵥ L *ᵥ v) :
    (L.map (Int.cast : ℤ → ℝ)).PosDef := by
  have hH : (L.map (Int.cast : ℤ → ℝ)).IsHermitian := by
    ext i j
    have := congrFun (congrFun hs j) i
    simp only [Matrix.transpose_apply] at this
    simp [Matrix.conjTranspose_apply, this]
  have hPSD : (L.map (Int.cast : ℤ → ℝ)).PosSemidef :=
    Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hH (fun x => by
      rw [quadR_eq]; exact quadR_nonneg L hp x)
  refine Matrix.PosDef.of_dotProduct_mulVec_pos hH (fun x hx => ?_)
  rw [quadR_eq]
  refine lt_of_le_of_ne (quadR_nonneg L hp x) (fun h0 => ?_)
  have hz : (L.map (Int.cast : ℤ → ℝ)) *ᵥ x = 0 := by
    rw [← hPSD.dotProduct_mulVec_zero_iff, quadR_eq]; exact h0.symm
  have hdetR : (L.map (Int.cast : ℤ → ℝ)).det = 0 :=
    Matrix.exists_mulVec_eq_zero_iff.mp ⟨x, hx, hz⟩
  have hdet : L.det = 0 := by
    have := (Int.castRingHom ℝ).map_det L
    rw [RingHom.mapMatrix_apply] at this
    simp only [eq_intCast] at this
    have h' : ((L.det : ℤ) : ℝ) = 0 := by rw [this]; exact hdetR
    exact_mod_cast h'
  obtain ⟨w, hw, hLw⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  have := hp w hw
  rw [hLw, dotProduct_zero] at this
  exact lt_irrefl _ this

end GlobalTheory.Poinc.SumSqFunctional

namespace GlobalTheory.Poinc.SumSqFunctional

open Matrix

theorem sumsq_functional : ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (lam : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ), (∀ l : X →ₗ[ℤ] ℤ, l ≠ 0 → 0 < lam (GlobalTheory.PolFan.sqForm l)) → ∃ (D m : ℕ) (a : Fin m → X), 1 ≤ D ∧ Submodule.span ℤ (Set.range a) = ⊤ ∧ ∀ β : LinearMap.BilinForm ℤ X, (∀ x y, β x y = β y x) → ∑ i, β (a i) (a i) = (D : ℤ) * lam β := by
  intro X _ _ _ lam hpos
  let b : Module.Basis (Fin (Fintype.card (Module.Free.ChooseBasisIndex ℤ X))) ℤ X :=
    (Module.Free.chooseBasis ℤ X).reindex (Fintype.equivFin _)
  set r := Fintype.card (Module.Free.ChooseBasisIndex ℤ X)
  let C : Fin r → Fin r → LinearMap.BilinForm ℤ X := fun i j =>
    (LinearMap.mul ℤ ℤ).compl₁₂ (b.coord i) (b.coord j)
  have hexp : ∀ β : LinearMap.BilinForm ℤ X, β = ∑ i, ∑ j, β (b i) (b j) • C i j := by
    intro β
    refine b.ext fun k => b.ext fun l => ?_
    simp [C, LinearMap.sum_apply, Finsupp.single_apply]
  have hbil : ∀ (β : LinearMap.BilinForm ℤ X) (c d : Fin r → ℤ),
      β (∑ i, c i • b i) (∑ j, d j • b j) = ∑ i, ∑ j, c i * d j * β (b i) (b j) := by
    intro β c d

    simp [map_sum, map_smul, LinearMap.sum_apply, Finset.mul_sum, mul_comm, mul_left_comm, mul_assoc]
    rw [Finset.sum_comm]
  let L : Matrix (Fin r) (Fin r) ℤ := Matrix.of fun i j => lam (C i j) + lam (C j i)
  have hlam : ∀ β : LinearMap.BilinForm ℤ X, (∀ x y, β x y = β y x) →
      2 * lam β = ∑ i, ∑ j, L i j * β (b i) (b j) := by
    intro β hβ
    have h1 : lam β = ∑ i, ∑ j, β (b i) (b j) * lam (C i j) := by
      conv_lhs => rw [hexp β]

      simp [map_sum, map_smul]
    have h2 : lam β = ∑ i, ∑ j, β (b i) (b j) * lam (C j i) := by
      rw [h1, Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      rw [hβ]
    calc 2 * lam β = lam β + lam β := by ring
      _ = _ := by
        nth_rewrite 1 [h1]
        rw [h2]
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun j _ => ?_
        simp only [L, Matrix.of_apply]; ring
  have hs : Lᵀ = L := by
    ext i j; simp [L, add_comm]
  have hp : ∀ v : Fin r → ℤ, v ≠ 0 → 0 < v ⬝ᵥ L *ᵥ v := by
    intro v hv
    let l : X →ₗ[ℤ] ℤ := ∑ i, v i • b.coord i
    have hl : ∀ k, l (b k) = v k := by
      intro k; simp [l, Finsupp.single_apply]
    have hl0 : l ≠ 0 := by
      intro h; apply hv; funext k; rw [← hl k, h]; rfl
    have hsq : ∀ x y, GlobalTheory.PolFan.sqForm l x y = l x * l y := by
      intro x y; simp [GlobalTheory.PolFan.sqForm]
    have hsym : ∀ x y, GlobalTheory.PolFan.sqForm l x y = GlobalTheory.PolFan.sqForm l y x := by
      intro x y; rw [hsq, hsq, mul_comm]
    have h2 := hlam _ hsym
    have h3 : v ⬝ᵥ L *ᵥ v = 2 * lam (GlobalTheory.PolFan.sqForm l) := by
      rw [h2]
      simp only [hsq, hl, dotProduct, Matrix.mulVec, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    rw [h3]; have := hpos l hl0; omega
  have hPD := posDef_of_pos_int L hs hp
  obtain ⟨D, m, a', hD, hspan, hsum⟩ := GlobalTheory.Poinc.SumSq.exists_smul_eq_sum_vecMulVec_span r L hPD
  have hentry : ∀ i j, (D : ℤ) * L i j = ∑ k, a' k i * a' k j := by
    intro i j
    have := congrFun (congrFun hsum i) j
    simpa [Matrix.sum_apply, Matrix.vecMulVec_apply] using this
  refine ⟨2 * D, m, fun k => ∑ i, a' k i • b i, by omega, ?_, ?_⟩
  · have hfun : (fun k => ∑ i, a' k i • b i) = ⇑b.equivFun.symm.toLinearMap ∘ a' := by
      funext k; simp [Module.Basis.equivFun_symm_apply]
    rw [hfun, Set.range_comp, Submodule.span_image, hspan, Submodule.map_top]
    exact LinearMap.range_eq_top.mpr b.equivFun.symm.surjective
  · intro β hβ
    simp only [hbil]
    rw [Finset.sum_comm]
    have : ∀ i, (∑ y, ∑ x, a' y i * a' y x * β (b i) (b x)) = ∑ j, (D : ℤ) * L i j * β (b i) (b j) := by
      intro i
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hentry, Finset.sum_mul]
    simp only [this]
    have h2 := hlam β hβ
    push_cast
    rw [mul_comm 2 (D : ℤ), mul_assoc, h2, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => by ring

end GlobalTheory.Poinc.SumSqFunctional
end

section

open IsLocalRing GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.Poinc

noncomputable section

namespace GlobalTheory.Poinc

theorem toReal_mem_psdCone_of_pos_int : ∀ (r : ℕ) (b : LinearMap.BilinForm ℤ (Fin r → ℤ)), (∀ x y, b x y = b y x) →
    (∀ x, x ≠ 0 → 0 < b x x) → toReal b ∈ psdCone (bar := (id : ℤ → ℤ)) (X := (Fin r → ℤ)) := by
  intro r b hs hp
  refine TameZ.toReal_mem_psdCone_int (mem_balForms_int.2 hs) fun y => ?_
  by_cases hy : y = 0
  · subst hy; simp
  · exact (hp y hy).le

end GlobalTheory.Poinc
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.dvd_of_dvd_in_all_completeDVR_normal_noetherian : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [CharZero R] (a b : R), b ≠ 0 → (∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.LN.CDvr V → ∀ φ : R →+* V, Function.Injective φ → φ b ∣ φ a) → b ∣ a := by
  first | exact @GlobalTheory.DvrDiv.dvd_of_forall_cDvr | exact GlobalTheory.DvrDiv.dvd_of_forall_cDvr | (intros; apply GlobalTheory.DvrDiv.dvd_of_forall_cDvr <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ZH GlobalTheory.Poinc

namespace GlobalTheory.Izumi

theorem essFiniteType_int_O : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (M : RatModel o Ω)
    (x : M.Z), Algebra.EssFiniteType ℤ (M.O x) := by
  intro o Ω _ _ _ hA M x
  haveI : LocallyOfFiniteType M.s := M.lft
  let y : PrimeSpectrum o := M.s x
  letI A : Algebra o ((Sp o).presheaf.stalk (M.s x)) := StructureSheaf.stalkAlgebra _ y
  haveI : @IsLocalization.AtPrime o _ ((Sp o).presheaf.stalk (M.s x)) _ A y.asIdeal _ :=
    StructureSheaf.IsLocalization.to_stalk _ y
  let φ := @algebraMap o ((Sp o).presheaf.stalk (M.s x)) _ _ A
  have h₁ : (M.s.stalkMap x).hom.EssFiniteType := LocallyOfFiniteType.stalkMap M.s x
  have h₂ : φ.EssFiniteType :=
    RingHom.essFiniteType_algebraMap.2 (Algebra.EssFiniteType.of_isLocalization _ y.asIdeal.primeCompl)
  haveI : Algebra.FiniteType ℤ o := hA.ft
  have h₀ : (algebraMap ℤ o).EssFiniteType := RingHom.essFiniteType_algebraMap.2 inferInstance
  have h₃ : (M.stalkEquiv x).toRingHom.EssFiniteType :=
    (RingHom.FiniteType.of_surjective _ (M.stalkEquiv x).surjective).essFiniteType
  have h := ((h₀.comp h₂).comp h₁)
  have h' := h.comp h₃
  rw [← RingHom.essFiniteType_algebraMap]
  convert h'
  exact RingHom.ext_int _ _

end GlobalTheory.Izumi
end

section

open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ZH GlobalTheory.Poinc

namespace GlobalTheory.ResFin

theorem finite_residueField_O : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (M : RatModel o Ω)
    (x : M.Z), IsClosed ({x} : Set M.Z) → Finite (ResidueField (M.O x)) := by
  intro o Ω _ _ _ hA M x hx
  haveI : Algebra.FiniteType ℤ o := hA.ft
  haveI : LocallyOfFiniteType (spMap (algebraMap ℤ o)) :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).2 (RingHom.finiteType_algebraMap.2 inferInstance)
  haveI : LocallyOfFiniteType M.s := M.lft
  have h := finite_residueField_of_isClosed_of_locallyOfFiniteType_int (M.s ≫ spMap (algebraMap ℤ o)) x hx
  haveI : Finite (ResidueField (M.Z.presheaf.stalk x)) := h
  exact Finite.of_equiv _ (ResidueField.mapEquiv (M.stalkEquiv x)).toEquiv

end GlobalTheory.ResFin
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.SiegelTor GlobalTheory.UT
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.ThetaLevel

theorem isGenSec_real {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {S : ThetaSys o Ω} (ρ : S.Real) :
    IsGenSec ρ.P.A ρ.P.L 1 ρ.th₁ := by
  intro s
  obtain ⟨r, hr, -⟩ := ρ.th₁_basis s
  exact ⟨r 0, fun j => (hr j).trans (Fin.sum_univ_one _)⟩

end GlobalTheory.ThetaLevel
end
end
