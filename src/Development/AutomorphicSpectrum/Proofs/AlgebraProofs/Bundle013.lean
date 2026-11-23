module

public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsSplitGaussChars
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle006
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle008
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle009
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LatticeBasisAdaptedToSubspace
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Algebra.AffineMonoid.Basic
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.Discriminant.Defs
public import Mathlib.RingTheory.DedekindDomain.Different
public import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.Bundle004
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle004
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Basic.NNReal.Defs
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle007
public import Mathlib.Analysis.Complex.Order
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Topology.MetricSpace.Ultra.Basic
public import Development.WeilBound.CoreStatements.SesquilinearFractions.Bundle002
public import Mathlib.Data.Matrix.ColumnRowPartitioned
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.RingTheory.Valuation.Integers
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle010
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
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle001
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Monoidal.Mon
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Objects
import Development.AutomorphicSpectrum.Definitions.AdelicLattices.Bundle001

@[expose] public section

section

open GlobalTheory.CompanionTheory.Ar.Crv

theorem _root_.GlobalTheory.T.bundle_degree_eq_sum_valuations : ∀ (K : Type) [Field K] (C : ACurve K) (V : Type) [AddCommGroup V] [Module K V] [FiniteDimensional K V] (L : C.I → AddSubgroup V) (n : ℕ) (b₀ : Module.Basis (Fin n) K V) (b : C.I → Module.Basis (Fin n) K V), IsBun C L → (∀ i, IsLatOf C i (b i) (L i)) → {i | C.v i (b₀.det (b i)) ≠ 1}.Finite ∧ deg C L = ∑ᶠ i, (C.w i : ℤ) * WithZero.log (C.v i (b₀.det (b i))) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Crv.DegFormula.deg_formula | exact GlobalTheory.CompanionTheory.Ar.Crv.DegFormula.deg_formula | (intros; apply GlobalTheory.CompanionTheory.Ar.Crv.DegFormula.deg_formula <;> assumption)
end

section

open GlobalTheory.CompanionTheory.Ar.Crv

theorem _root_.GlobalTheory.T.degree_invariant_linear_equiv : ∀ (K : Type) [Field K] (C : ACurve K) (V : Type) [AddCommGroup V] [Module K V] [FiniteDimensional K V] (V' : Type) [AddCommGroup V'] [Module K V'] [FiniteDimensional K V'] (L : C.I → AddSubgroup V) (L' : C.I → AddSubgroup V') (e : V ≃ₗ[K] V'), IsBun C L → (∀ i x, x ∈ L i ↔ e x ∈ L' i) → IsBun C L' ∧ deg C L' = deg C L := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Crv.DegEquiv.deg_equiv | exact GlobalTheory.CompanionTheory.Ar.Crv.DegEquiv.deg_equiv | (intros; apply GlobalTheory.CompanionTheory.Ar.Crv.DegEquiv.deg_equiv <;> assumption)
end

section

open GlobalTheory.CompanionTheory.Ar.Crv

theorem _root_.GlobalTheory.T.eigen_projectors_split_action : ∀ (K : Type) [Field K] (C : ACurve K) (V : Type) [AddCommGroup V] [Module K V] [FiniteDimensional K V] (L : C.I → AddSubgroup V) (O k S : Type) [CommRing O] [Field k] [Algebra k K] [Fintype S] [DecidableEq S] (χ : S → (O →+* k)), IsSplit χ → (∀ i (c : k), C.v i (algebraMap k K c) ≤ 1) → ∀ ρ : O →+* Module.End K V, IsBun C L → (∀ a, IsHom C L L (ρ a)) → ∃ e : S → Module.End K V, (∀ s, IsHom C L L (e s)) ∧ (∀ s x, e s x ∈ (eig (fun a => ρ a) (fun a => algebraMap k K (χ s a)))) ∧ (∀ s, ∀ x ∈ (eig (fun a => ρ a) (fun a => algebraMap k K (χ s a))), e s x = x) ∧ (∀ x, ∑ s, e s x = x) ∧ ∀ s, ∃ (m : ℕ) (c : Fin m → k) (a : Fin m → O), (∀ t, ∑ j, c j * χ t (a j) = if t = s then 1 else 0) ∧ e s = ∑ j, algebraMap k K (c j) • ρ (a j) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Crv.SplitProj.split_proj | exact GlobalTheory.CompanionTheory.Ar.Crv.SplitProj.split_proj | (intros; apply GlobalTheory.CompanionTheory.Ar.Crv.SplitProj.split_proj <;> assumption)
end

section

open GlobalTheory.CompanionTheory.Ar.Crv

theorem _root_.GlobalTheory.T.lattice_basis_adapted_to_subspace : ∀ (K : Type) [Field K] (C : ACurve K) (V : Type) [AddCommGroup V] [Module K V] (i : C.I) (n : ℕ) (b : Module.Basis (Fin n) K V) (L : AddSubgroup V) (W : Submodule K V), IsLatOf C i b L → ∃ (bW : Module.Basis (Fin (Module.finrank K W)) K W) (bQ : Module.Basis (Fin (Module.finrank K (V ⧸ W))) K (V ⧸ W)) (b' : Module.Basis (Fin (Module.finrank K W + Module.finrank K (V ⧸ W))) K V), IsLatOf C i b' L ∧ IsLatOf C i bW (L.comap W.subtype.toAddMonoidHom) ∧ IsLatOf C i bQ (L.map W.mkQ.toAddMonoidHom) ∧ (∀ j, b' (Fin.castAdd _ j) = bW j) ∧ ∀ j, W.mkQ (b' (Fin.natAdd _ j)) = bQ j := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Crv.LatAdapted.exists_adapted | exact GlobalTheory.CompanionTheory.Ar.Crv.LatAdapted.exists_adapted | (intros; apply GlobalTheory.CompanionTheory.Ar.Crv.LatAdapted.exists_adapted <;> assumption)
end

section

noncomputable section

open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.Ar.Flat.DegCurve

open GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Crv.SplitProj

def act (k : Type) {K V O : Type} [Field K] [AddCommGroup V] [Module K V] [CommRing O] [Field k]
    [Algebra k K] (ρ : O →+* Module.End K V) : TensorProduct ℤ k O →+* Module.End K V :=
  (actMap (k := k) ρ).toRingHom

theorem act_tmul (k : Type) {K V O : Type} [Field K] [AddCommGroup V] [Module K V] [CommRing O]
    [Field k] [Algebra k K] (ρ : O →+* Module.End K V) (c : k) (a : O) :
    act k ρ (c ⊗ₜ[ℤ] a) = algebraMap k K c • ρ a :=
  actMap_tmul ρ c a

def toEnd {K O : Type} [Field K] [CommRing O] {d : ℕ} (ρ : O →+* Matrix (Fin d) (Fin d) K) :
    O →+* Module.End K (Fin d → K) :=
  (Matrix.toLinAlgEquiv' (R := K) (n := Fin d)).toAlgHom.toRingHom.comp ρ

theorem toEnd_apply {K O : Type} [Field K] [CommRing O] {d : ℕ}
    (ρ : O →+* Matrix (Fin d) (Fin d) K) (a : O) (v : Fin d → K) :
    toEnd ρ a v = (ρ a).mulVec v := rfl

def twist {K O : Type} [Field K] [CommRing O] {d : ℕ} (p : ℕ) [Fact p.Prime] [CharP K p]
    (ρ : O →+* Matrix (Fin d) (Fin d) K) : O →+* Matrix (Fin d) (Fin d) K :=
  (frobenius K p).mapMatrix.comp ρ

theorem twist_apply {K O : Type} [Field K] [CommRing O] {d : ℕ} (p : ℕ) [Fact p.Prime] [CharP K p]
    (ρ : O →+* Matrix (Fin d) (Fin d) K) (a : O) : twist p ρ a = (ρ a).map (· ^ p) := rfl

def conjT {K O : Type} [Field K] [CommRing O] [StarRing O] {d : ℕ}
    (ρ : O →+* Matrix (Fin d) (Fin d) K) : O →+* Matrix (Fin d) (Fin d) K where
  toFun a := (ρ (star a)).transpose
  map_one' := by simp
  map_mul' a b := by
    rw [star_mul, map_mul, Matrix.transpose_mul]
  map_zero' := by simp
  map_add' a b := by simp [star_add]

theorem conjT_apply {K O : Type} [Field K] [CommRing O] [StarRing O] {d : ℕ}
    (ρ : O →+* Matrix (Fin d) (Fin d) K) (a : O) : conjT ρ a = (ρ (star a)).transpose := rfl

def frobT (k O : Type) [Field k] [CommRing O] (p : ℕ) [Fact p.Prime] [CharP k p] :
    TensorProduct ℤ k O →+* TensorProduct ℤ k O :=
  (Algebra.TensorProduct.map (frobenius k p).toIntAlgHom (AlgHom.id ℤ O)).toRingHom

theorem frobT_tmul (k O : Type) [Field k] [CommRing O] (p : ℕ) [Fact p.Prime] [CharP k p] (c : k)
    (a : O) : frobT k O p (c ⊗ₜ[ℤ] a) = (c ^ p) ⊗ₜ[ℤ] a := by
  simp [frobT, frobenius_def]

def chiT {k O : Type} [Field k] [CommRing O] (χ : O →+* k) : TensorProduct ℤ k O →ₐ[k] k :=
  Algebra.TensorProduct.lift (AlgHom.id k k) χ.toIntAlgHom (fun _ _ => Commute.all _ _)

theorem chiT_tmul {k O : Type} [Field k] [CommRing O] (χ : O →+* k) (c : k) (a : O) :
    chiT χ (c ⊗ₜ[ℤ] a) = c * χ a := by
  simp [chiT]

def idealV {K A V : Type} [Field K] [CommRing A] [AddCommGroup V] [Module K V]
    (τ : A →+* Module.End K V) (J : Ideal A) : Submodule K V :=
  ⨆ a : J, LinearMap.range (τ a)

def FreeAt {K : Type} [Field K] (C : ACurve K) (k : Type) {A V : Type} [Field k] [Algebra k K]
    [CommRing A] [Algebra k A] [AddCommGroup V] [Module K V] (τ : A →+* Module.End K V)
    (L : C.I → AddSubgroup V) (r : ℕ) (i : C.I) : Prop :=
  ∃ (x : Fin r → V) (Θ : (A →ₗ[k] k) → Fin r → (V →ₗ[K] K)),
    (∀ s, x s ∈ L i) ∧
    (∀ l s s' a, Θ l s (τ a (x s')) = if s = s' then algebraMap k K (l a) else 0) ∧
    (∀ l s y, y ∈ L i → C.v i (Θ l s y) ≤ 1) ∧
    ∀ y : V, y ∈ Submodule.span K (Set.range fun q : A × Fin r => τ q.1 (x q.2))

end GlobalTheory.CompanionTheory.Ar.Flat.DegCurve
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar

theorem mem_differentIdeal_ringEquiv_iff :
    ∀ (E : Type) [Field E] [NumberField E] (s : 𝓞 E ≃+* 𝓞 E) (d : 𝓞 E),
      s d ∈ differentIdeal ℤ (𝓞 E) ↔ d ∈ differentIdeal ℤ (𝓞 E) :=
  @PositivityTheory.UnitarySelfGeneration.map_mem_differentIdeal_iff

end GlobalTheory.CompanionTheory.Ar
end

section

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num NumberField

namespace GlobalTheory.CompanionTheory.Ar.Num

theorem unramified_prime_idempotent : ∀ (E : Type) [Field E] [NumberField E] (p : ℕ), p.Prime → ¬ (p : ℤ) ∣ NumberField.discr E → ∀ (w : Ideal (𝓞 E)) [w.IsPrime], (p : 𝓞 E) ∈ w → ∃ ε : 𝓞 E, ε - 1 ∈ w ∧ (∀ w' : Ideal (𝓞 E), w'.IsPrime → (p : 𝓞 E) ∈ w' → w' ≠ w → ε ∈ w') ∧ (∀ a : 𝓞 E, (p : 𝓞 E) ∣ ε * a ↔ a ∈ w) ∧ (p : 𝓞 E) ∣ ε * ε - ε ∧ IsCoprime (Ideal.span {(p : 𝓞 E)}) (differentIdeal ℤ (𝓞 E)) :=
  PositivityTheory.HtPt.Gsplit.glue_split

end GlobalTheory.CompanionTheory.Ar.Num
end

section

open scoped Matrix TensorProduct
open Matrix

theorem _root_.GlobalTheory.T.product_inequalities_force_equality : ∀ (T S : Type) [Fintype T] [Fintype S] (a b : ℕ), 0 < a → 0 < b → ∀ (x D d : T → S → NNReal) (r : S → NNReal) (cA cN cO : NNReal), cN ≠ 0 → (∀ t s, x t s ≤ D t s) → ∏ t, ∏ s, D t s = cA → (∏ t, ∏ s, x t s) ^ (a * b) = cN ^ 2 → cA ^ (a * b) = cN ^ 2 → (∀ s, ∏ t, d t s ≤ r s) → ∏ s, r s = cO → ∏ t, ∏ s, d t s = (∏ t, ∏ s, x t s) ^ b → cO ^ a = cN ^ 2 → (∀ t s, D t s = x t s) ∧ ∀ s, ∏ t, d t s = r s := by
  first | exact @GlobalTheory.CompanionTheory.Ar.GR.grcount | exact GlobalTheory.CompanionTheory.Ar.GR.grcount | (intros; apply GlobalTheory.CompanionTheory.Ar.GR.grcount <;> assumption)
end

section

open NumberField Matrix GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.Fl.Sylvester

theorem neg_posDef_of_compl_posDef : ∀ (p q : ℕ) (A : Matrix (Fin p) (Fin p) ℂ) (B : Matrix (Fin q) (Fin q) ℂ) (C : Matrix (Fin q) (Fin p ⊕ Fin q) ℂ), A.PosDef → B.IsHermitian → (-(C * Matrix.fromBlocks A 0 0 B * Cᴴ)).PosDef → (-B).PosDef :=
  @PositivityTheory.Xgf.negDef_block_of_posDef

end GlobalTheory.CompanionTheory.Ar.Fl.Sylvester
end

section

open NumberField Matrix GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

theorem _root_.GlobalTheory.T.ultrametric_det_norm_le : ∀ (A : Type) [NormedField A] [IsUltrametricDist A] (I : Type) [Fintype I] [DecidableEq I] (M : Matrix I I A) (r : ℝ), 0 ≤ r → (∀ a b, ‖M a b‖ ≤ r) → ‖M.det‖ ≤ r ^ Fintype.card I := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Fl.norm_det_le_pow_card_of_ultrametric | exact GlobalTheory.CompanionTheory.Ar.Fl.norm_det_le_pow_card_of_ultrametric | (intros; apply GlobalTheory.CompanionTheory.Ar.Fl.norm_det_le_pow_card_of_ultrametric <;> assumption)
end

section

open NumberField Matrix GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.Fl

theorem norm_det_eq_of_entries_close : ∀ (A : Type) [NormedField A] [IsUltrametricDist A] (I : Type) [Fintype I] [DecidableEq I] (M M' : Matrix I I A) (r : ℝ), 0 < r → (∀ a b, ‖M a b‖ ≤ r) → (∀ a b, ‖M' a b - M a b‖ < r) → ‖M.det‖ = r ^ Fintype.card I → ‖M'.det‖ = r ^ Fintype.card I :=
  @PositivityTheory.Xgf.ultrametric_det_norm_stable

end GlobalTheory.CompanionTheory.Ar.Fl
end

section

open scoped Matrix TensorProduct
open Matrix

theorem _root_.GlobalTheory.T.symplectic_period_matrix_integrality : ∀ (C : Type) [Field C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → ∀ (g : ℕ) (Ht Bt : Matrix (Fin g) (Fin g ⊕ Fin g) R) (E : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) R) (cp : R), cp ≠ 0 → Eᵀ = -E → IsUnit E.det → Btᵀ * Ht - Htᵀ * Bt = cp • E → let φ := algebraMap R C; let intg : (Fin g → C) → Prop := fun w => ∀ k, v (w k) ≤ 1; let hb : Matrix (Fin g ⊕ Fin g) (Fin g) C := ((Eᵀ)⁻¹ * Htᵀ).map φ; v (φ (Matrix.fromRows Ht Bt).det) = v (φ cp) ^ g ∧ (∀ x : Fin g ⊕ Fin g → C, ((Ht.map φ) *ᵥ x = 0 ∧ intg ((Bt.map φ) *ᵥ x)) ↔ ∃ w, intg w ∧ x = (φ cp)⁻¹ • (hb *ᵥ w)) ∧ (∀ w, intg w → ∃ x : Fin g ⊕ Fin g → C, (Ht.map φ) *ᵥ x = w ∧ (Bt.map φ) *ᵥ x = 0) ∧ (∀ l : Fin g ⊕ Fin g → R, cp • l ∈ Submodule.span R (Set.range fun k => Matrix.fromRows Ht Bt k)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.GR.gp_mat_lattice | exact GlobalTheory.CompanionTheory.Ar.GR.gp_mat_lattice | (intros; apply GlobalTheory.CompanionTheory.Ar.GR.gp_mat_lattice <;> assumption)
end
