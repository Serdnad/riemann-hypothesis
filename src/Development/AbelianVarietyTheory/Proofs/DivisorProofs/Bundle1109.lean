module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1056
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNontrivialCharacterFiniteCommGroup
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.Tactic.ENatToNat
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1073
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1065
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1064
public import Development.AbelianVarietyTheory.Definitions.Divisors.TorsTransport
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle888
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle010
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle228
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1074
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle029
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.PublishedTheorems.AbelianLaws.PrincipalPolarisationOneSection
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle576
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OmegaFactorization
import Development.AbelianVarietyTheory.Definitions.Divisors.HasLevelStd
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle001
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle024

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CharKer

theorem _root_.GlobalTheory.T.kernelAction_isPullback_prodMap_torsor : ∀ (S : Scheme.{0}) (A A' N T : Over S) [GrpObj A] [GrpObj A'] [GrpObj N] (i : N ⟶ A) (q : A ⟶ A'), IsMonHom i → IsMonHom q → IsPullback i (toUnit N) q η[A'] → IsPullback (prMap A N T) (actMap i T) (pmap q T) (pmap q T) := by
  first | exact @GlobalTheory.CharKer.pmap_isPullback_actMap | exact GlobalTheory.CharKer.pmap_isPullback_actMap | (intros; apply GlobalTheory.CharKer.pmap_isPullback_actMap <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CharKer

theorem _root_.GlobalTheory.T.exists_nontrivial_character_finite_comm_group : ∀ (K : Type) [Field K] (N : Over (Sp K)) [GrpObj N] [IsCommMonObj N], IsFinite N.hom → (𝟙 N ≠ (1 : N ⟶ N)) → ∃ (T : Over (Sp K)) (χ : Γ((N ⊗ T).left, ⊤)ˣ), IsCharacter χ ∧ χ ≠ 1 := by
  first | exact @GlobalTheory.CharExists.exists_character_ne_one | exact GlobalTheory.CharExists.exists_character_ne_one | (intros; apply GlobalTheory.CharExists.exists_character_ne_one <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CharKer

theorem _root_.GlobalTheory.T.locally_trivial_unit_cocycle_scheme : ∀ (X Y Z W : Scheme.{0}) (p : X ⟶ Y) (a b : Z ⟶ X) (m₁₂ m₂₃ m₁₃ : W ⟶ Z) (χ : Γ(Z, ⊤)ˣ), IsAffineHom p → Flat p → Surjective p → IsPullback b a p p → IsPullback m₁₂ m₂₃ a b → m₁₃ ≫ b = m₁₂ ≫ b → m₁₃ ≫ a = m₂₃ ≫ a → pullTop m₁₃ χ = pullTop m₁₂ χ * pullTop m₂₃ χ → ∀ y : Y, ∃ V : Y.Opens, y ∈ V ∧ ∃ e : Γ(X, p ⁻¹ᵁ V)ˣ, ∀ (W' : Z.Opens) (h₁ : W' ≤ a ⁻¹ᵁ (p ⁻¹ᵁ V)) (h₂ : W' ≤ b ⁻¹ᵁ (p ⁻¹ᵁ V)), res h₁ (pullU a _ e) = res le_top χ * res h₂ (pullU b _ e) := by
  first | exact @GlobalTheory.CharKer.exists_local_charUnit | exact GlobalTheory.CharKer.exists_local_charUnit | (intros; apply GlobalTheory.CharKer.exists_local_charUnit <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TwoTors

set_option autoImplicit false

namespace GlobalTheory.CharKer

theorem exists_pullTop_of_isPullback : ∀ {S X : Scheme.{0}} (A Z : Over S) [GrpObj A], IsAbelianScheme A → ∀ (p : X ⟶ A.left) (q : X ⟶ Z.left), IsPullback p q A.hom Z.hom → ∀ D : Γ(X, ⊤)ˣ, ∃ c : Γ(Z.left, ⊤)ˣ, GlobalTheory.CharKer.pullTop q c = D := by
  intro S X A Z _ hA p q h D
  obtain ⟨c, hc⟩ := exists_pullTop_snd A Z hA (pullTop h.isoPullback.inv D)
  refine ⟨c, ?_⟩
  have h₁ : h.isoPullback.hom ≫ (snd A Z).left = q := h.isoPullback_hom_snd
  have h₂ := congrArg (pullTop h.isoPullback.hom) hc
  rw [← h₁]
  refine (pullTop_pullTop_comp _ _ c).symm.trans (h₂.trans ?_)
  rw [pullTop_pullTop_comp, Iso.hom_inv_id]
  rfl

end GlobalTheory.CharKer
end

section

set_option autoImplicit false

noncomputable section

open MvPolynomial ReciprocityTheory.MultiplicativeHeights GlobalTheory.HSChoice GlobalTheory.PencilDisc

namespace GlobalTheory.PencilDiscDeg

variable {F : Type} [Field F] {σ : Type}

def CoeffDeg (e : ℕ) (P : Polynomial (MvPolynomial σ F)) : Prop :=
  ∀ k, (P.coeff k).totalDegree ≤ e

theorem CoeffDeg.mono {e e' : ℕ} {P : Polynomial (MvPolynomial σ F)} (h : CoeffDeg e P) (he : e ≤ e') :
    CoeffDeg e' P := fun k => (h k).trans he

theorem coeffDeg_C {e : ℕ} {a : MvPolynomial σ F} (ha : a.totalDegree ≤ e) :
    CoeffDeg e (Polynomial.C a) := by
  intro k
  rw [Polynomial.coeff_C]
  split_ifs
  · exact ha
  · simp

theorem coeffDeg_one : CoeffDeg 0 (1 : Polynomial (MvPolynomial σ F)) := by
  rw [← Polynomial.C_1]
  exact coeffDeg_C (by simp)

theorem coeffDeg_X : CoeffDeg 0 (Polynomial.X : Polynomial (MvPolynomial σ F)) := by
  intro k
  rw [Polynomial.coeff_X]
  split_ifs <;> simp

theorem CoeffDeg.add {e : ℕ} {P Q : Polynomial (MvPolynomial σ F)} (hP : CoeffDeg e P) (hQ : CoeffDeg e Q) :
    CoeffDeg e (P + Q) := by
  intro k
  rw [Polynomial.coeff_add]
  exact (totalDegree_add _ _).trans (max_le (hP k) (hQ k))

theorem CoeffDeg.mul {e e' : ℕ} {P Q : Polynomial (MvPolynomial σ F)} (hP : CoeffDeg e P)
    (hQ : CoeffDeg e' Q) : CoeffDeg (e + e') (P * Q) := by
  intro k
  rw [Polynomial.coeff_mul]
  exact totalDegree_finsetSum_le fun x _ => (totalDegree_mul _ _).trans (add_le_add (hP _) (hQ _))

theorem coeffDeg_sum {ι : Type} (s : Finset ι) {e : ℕ} (P : ι → Polynomial (MvPolynomial σ F))
    (h : ∀ i ∈ s, CoeffDeg e (P i)) : CoeffDeg e (∑ i ∈ s, P i) := by
  intro k
  rw [Polynomial.finsetSum_coeff]
  exact totalDegree_finsetSum_le fun i hi => h i hi k

theorem coeffDeg_prod {ι : Type} [DecidableEq ι] (s : Finset ι) (e : ι → ℕ)
    (P : ι → Polynomial (MvPolynomial σ F)) (h : ∀ i ∈ s, CoeffDeg (e i) (P i)) :
    CoeffDeg (∑ i ∈ s, e i) (∏ i ∈ s, P i) := by
  induction s using Finset.induction_on with
  | empty => simpa using coeffDeg_one
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).mul (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem CoeffDeg.pow {e : ℕ} {P : Polynomial (MvPolynomial σ F)} (hP : CoeffDeg e P) (n : ℕ) :
    CoeffDeg (n * e) (P ^ n) := by
  induction n with
  | zero => simpa using coeffDeg_one
  | succ n ih =>
    rw [pow_succ, Nat.succ_mul]
    exact ih.mul hP

theorem CoeffDeg.derivative {e : ℕ} {P : Polynomial (MvPolynomial σ F)} (hP : CoeffDeg e P) :
    CoeffDeg e (Polynomial.derivative P) := by
  intro k
  rw [Polynomial.coeff_derivative]
  have h1 : ((k : MvPolynomial σ F) + 1) = C ((k : F) + 1) := by simp
  rw [h1]
  refine (totalDegree_mul _ _).trans ?_
  rw [totalDegree_C, add_zero]
  exact hP (k + 1)

theorem totalDegree_resultant_le {e : ℕ} {P Q : Polynomial (MvPolynomial σ F)} (hP : CoeffDeg e P)
    (hQ : CoeffDeg e Q) (m n : ℕ) : (Polynomial.resultant P Q m n).totalDegree ≤ (m + n) * e := by
  have hH : ∀ i j, (Polynomial.sylvester P Q m n i j).totalDegree ≤ e := by
    intro i j
    induction j using Fin.addCases with
    | left j =>
      simp only [Polynomial.sylvester, Matrix.of_apply, Fin.addCases_left]
      split_ifs
      · exact hQ _
      · simp
    | right j =>
      simp only [Polynomial.sylvester, Matrix.of_apply, Fin.addCases_right]
      split_ifs
      · exact hP _
      · simp
  rw [Polynomial.resultant, Matrix.det_apply]
  refine totalDegree_finsetSum_le fun s _ => ?_
  refine (totalDegree_smul_le _ _).trans ((totalDegree_finsetProd _ _).trans ?_)
  simpa using Finset.sum_le_card_nsmul Finset.univ _ e fun i _ => hH (s i) i

theorem coeffDeg_line {D N δ : ℕ} (f : MvPolynomial (Fin (D + 1) × Fin N) F)
    (hf : IsMultiHomogeneous (fun _ => δ) f) (ξ₀ ξ₁ : Fin N → F) :
    CoeffDeg (D * δ) (line (fun i j => (X (i, j) : MvPolynomial (Fin D × Fin N) F))
      (fun j => C (ξ₀ j)) (fun j => C (ξ₁ j)) f) := by
  rw [line, aeval_def, eval₂_eq']
  refine coeffDeg_sum _ _ fun d hd => ?_
  have hc : CoeffDeg 0 (algebraMap F (Polynomial (MvPolynomial (Fin D × Fin N) F)) (AddMonoidAlgebra.coeff f d)) := by
    rw [Polynomial.algebraMap_apply]
    exact coeffDeg_C (by rw [MvPolynomial.algebraMap_eq, totalDegree_C])
  have hw : ∀ p : Fin (D + 1) × Fin N, CoeffDeg (if p.1 = Fin.last D then 0 else 1)
      (join (fun i j => Polynomial.C (X (i, j) : MvPolynomial (Fin D × Fin N) F))
        (fun j => Polynomial.C (C (ξ₀ j)) + Polynomial.C (C (ξ₁ j)) * Polynomial.X) p) := by
    rintro ⟨i, j⟩
    refine Fin.lastCases ?_ (fun i => ?_) i
    · simp only [join, Fin.lastCases_last, if_true]
      exact (coeffDeg_C (totalDegree_C _).le).add ((coeffDeg_C (e := 0) (totalDegree_C _).le).mul coeffDeg_X)
    · simp only [join, Fin.lastCases_castSucc, if_neg (Fin.castSucc_ne_last i)]
      exact coeffDeg_C (totalDegree_X _).le
  refine (hc.mul (coeffDeg_prod Finset.univ _ _ fun p _ => (hw p).pow (d p))).mono (le_of_eq ?_)
  rw [zero_add, Fintype.sum_prod_type, Fin.sum_univ_castSucc]
  have h := hf d hd
  simp [Fin.castSucc_ne_last, h]

theorem totalDegree_disc_le (F : Type) [Field F] (D N δ : ℕ) (f : MvPolynomial (Fin (D + 1) × Fin N) F)
    (hf : IsMultiHomogeneous (fun _ => δ) f) (ξ₀ ξ₁ : Fin N → F) :
    (disc δ (fun i j => (X (i, j) : MvPolynomial (Fin D × Fin N) F))
      (fun j => C (ξ₀ j)) (fun j => C (ξ₁ j)) f).totalDegree ≤ 2 * D * δ ^ 2 := by
  have h := coeffDeg_line f hf ξ₀ ξ₁
  refine (totalDegree_resultant_le h h.derivative δ (δ - 1)).trans ?_
  calc (δ + (δ - 1)) * (D * δ) ≤ (2 * δ) * (D * δ) := Nat.mul_le_mul_right _ (by omega)
    _ = 2 * D * δ ^ 2 := by ring

end GlobalTheory.PencilDiscDeg
end
end

section

set_option autoImplicit false

noncomputable section

open MvPolynomial ReciprocityTheory.MultiplicativeHeights GlobalTheory.HSChoice GlobalTheory.PencilDisc

namespace GlobalTheory.PencilDisc.GenericLine

variable (F : Type) [Field F] (D N : ℕ)

abbrev Idx := (Fin D × Fin N) ⊕ (Fin N ⊕ Fin N)

def shiftFun (c : F) : Option (Idx D N) → MvPolynomial (Option (Idx D N)) F
  | some (Sum.inr (Sum.inl j)) =>
      X (some (Sum.inr (Sum.inl j))) + C c * (X (some (Sum.inr (Sum.inr j))) * X none)
  | o => X o

def shift (c : F) : MvPolynomial (Option (Idx D N)) F →ₐ[F] MvPolynomial (Option (Idx D N)) F :=
  aeval (shiftFun F D N c)

theorem shift_comp (c : F) : (shift F D N c).comp (shift F D N (-c)) = AlgHom.id F _ := by
  apply MvPolynomial.algHom_ext
  rintro (_ | (p | j | j))
  · simp [shift, shiftFun]
  · simp [shift, shiftFun]
  · simp [shift, shiftFun]
  · simp [shift, shiftFun]

def theta : MvPolynomial (Option (Idx D N)) F ≃ₐ[F] MvPolynomial (Option (Idx D N)) F :=
  AlgEquiv.ofAlgHom (shift F D N 1) (shift F D N (-1))
    (by simpa using shift_comp F D N 1) (by simpa using shift_comp F D N (-1))

def place : Fin (D + 1) × Fin N → Option (Idx D N) := fun p =>
  Fin.lastCases (motive := fun _ => Option (Idx D N)) (some (Sum.inr (Sum.inl p.2)))
    (fun i => some (Sum.inl (i, p.2))) p.1

theorem place_injective : Function.Injective (place D N) := by
  rintro ⟨a, b⟩ ⟨a', b'⟩ h
  induction a using Fin.lastCases <;> induction a' using Fin.lastCases <;> simp_all [place]

theorem line_eq (f : MvPolynomial (Fin (D + 1) × Fin N) F) :
    GlobalTheory.PencilDisc.line (fun i j => (X (Sum.inl (i, j)) : MvPolynomial (Idx D N) F))
      (fun j => X (Sum.inr (Sum.inl j))) (fun j => X (Sum.inr (Sum.inr j))) f =
    optionEquivLeft F (Idx D N) (theta F D N (rename (place D N) f)) := by
  have key : (aeval (join (fun i j => (Polynomial.C (X (Sum.inl (i, j)) : MvPolynomial (Idx D N) F)))
      (fun j => Polynomial.C (X (Sum.inr (Sum.inl j))) + Polynomial.C (X (Sum.inr (Sum.inr j))) * Polynomial.X)) :
      MvPolynomial (Fin (D + 1) × Fin N) F →ₐ[F] Polynomial (MvPolynomial (Idx D N) F)) =
      ((optionEquivLeft F (Idx D N)).toAlgHom.comp ((theta F D N).toAlgHom.comp (rename (place D N)))) := by
    apply MvPolynomial.algHom_ext
    rintro ⟨i, j⟩
    induction i using Fin.lastCases <;> simp [join, place, theta, shift, shiftFun, AlgEquiv.ofAlgHom_apply]
  exact congrArg (fun φ => φ f) key

end GlobalTheory.PencilDisc.GenericLine

private theorem irreducible_rename_of_injective' {σ τ K : Type} [Field K] (g : σ → τ)
    (hg : Function.Injective g) (f : MvPolynomial σ K) (hf : Irreducible f) :
    Irreducible (rename g f) := by
  classical
  have hk : ∀ p : MvPolynomial σ K, killCompl hg (rename g p) = p := killCompl_rename_app hg
  have hf0 : rename g f ≠ 0 := by
    intro h
    apply hf.ne_zero
    rw [← hk f, h, map_zero]
  have hvars : ∀ a : MvPolynomial τ K, a ∣ rename g f → ∃ q, rename g q = a := by
    rintro a ⟨b, hab⟩
    have ha : a ≠ 0 := by
      rintro rfl
      rw [zero_mul] at hab
      exact hf0 hab
    have hb : b ≠ 0 := by
      rintro rfl
      rw [mul_zero] at hab
      exact hf0 hab
    refine exists_rename_eq_of_vars_subset_range a g hg ?_
    intro i hi
    by_contra hni
    have h1 : degreeOf i (rename g f) = 0 := by
      by_contra hne
      have hmem : i ∈ (rename g f).vars := mem_vars_iff_degreeOf_ne_zero.2 hne
      obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 (vars_rename g f hmem)
      exact hni ⟨j, rfl⟩
    rw [hab, degreeOf_mul_eq ha hb] at h1
    exact mem_vars_iff_degreeOf_ne_zero.1 (Finset.mem_coe.1 hi) (by omega)
  refine irreducible_iff.2 ⟨?_, ?_⟩
  · intro hu
    exact (irreducible_iff.1 hf).1 (by simpa [hk] using hu.map (killCompl hg))
  · intro a b hab
    obtain ⟨a', rfl⟩ := hvars a ⟨b, hab⟩
    obtain ⟨b', rfl⟩ := hvars b ⟨rename g a', by rw [hab, mul_comm]⟩
    rw [← map_mul] at hab
    rcases (irreducible_iff.1 hf).2 (rename_injective g hg hab) with h | h
    · exact Or.inl (h.map _)
    · exact Or.inr (h.map _)


open GlobalTheory.PencilDisc.GenericLine in
theorem GlobalTheory.PencilDisc.irreducible_line_generic (F : Type) [Field F] (D N : ℕ)
    (f : MvPolynomial (Fin (D + 1) × Fin N) F) (hf : Irreducible f) :
    Irreducible (GlobalTheory.PencilDisc.line
      (fun i j => (MvPolynomial.X (Sum.inl (i, j)) : MvPolynomial ((Fin D × Fin N) ⊕ (Fin N ⊕ Fin N)) F))
      (fun j => MvPolynomial.X (Sum.inr (Sum.inl j))) (fun j => MvPolynomial.X (Sum.inr (Sum.inr j))) f) := by
  rw [line_eq F D N f, MulEquiv.irreducible_iff, MulEquiv.irreducible_iff]
  exact irreducible_rename_of_injective' (place D N) (place_injective D N) f hf
end
end

section

open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
open GlobalTheory.LatVal (Sz)
open GlobalTheory.LatJet (EisExp IsEis FR)
open IsDedekindDomain
open GlobalTheory.CMVal (OF Af lattice IsBaseCond IsFinSetSplitPlacesCoprimeConductor condQ hatO)
open GlobalTheory.LatVal (OneOver)
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (a0)

namespace GlobalTheory.HilbFam.LatDen

theorem nat_mul_integral_mem_lattice : ∀ (E : Type) [Field E] [NumberField E] (l : ℕ) (c : Ideal (OF E)) (y : (Af E)ˣ) (R : ℕ), l.Prime → OneOver l y → 0 < R → (R : OF E) ∈ c → ∃ M : ℕ, ¬ l ∣ M ∧ ∀ x : E, IsIntegral ℤ x → ((M * R : ℕ) : E) * x ∈ lattice c y := by
  intro E _ _ l c y R hl hy hR hRc
  obtain ⟨M, hM, hMz⟩ := GlobalTheory.HilbFam.AdeleDen.exists_den_prime_to E l ((y⁻¹ : (Af E)ˣ) : Af E) hl (fun w hw => by
    have h1 : ((y⁻¹ : (Af E)ˣ) : Af E) w * (y : Af E) w = 1 := by
      have h := congrArg (fun a : Af E => a w) (Units.inv_mul y)
      exact h
    rw [hy w hw, mul_one] at h1
    rw [h1, map_one])
  refine ⟨M, hM, fun x hx => ?_⟩
  show algebraMap E (Af E) (((M * R : ℕ) : E) * x) * ((y⁻¹ : (Af E)ˣ) : Af E) ∈ hatO c
  refine GlobalTheory.CMVal.LatEnt.mem_hatO_of_sub hR hRc (zero_mem _) fun P => ?_
  have e : (algebraMap E (Af E) (((M * R : ℕ) : E) * x) * ((y⁻¹ : (Af E)ˣ) : Af E)) P - (0 : Af E) P =
      (R : P.adicCompletion E) * (algebraMap E (P.adicCompletion E) x *
        (algebraMap E (Af E) (M : E) * ((y⁻¹ : (Af E)ˣ) : Af E)) P) := by
    rw [show (0 : Af E) P = 0 from rfl, sub_zero,
      show (algebraMap E (Af E) (M : E) * ((y⁻¹ : (Af E)ˣ) : Af E)) P =
        algebraMap E (P.adicCompletion E) (M : E) * ((y⁻¹ : (Af E)ˣ) : Af E) P from rfl]
    show algebraMap E (P.adicCompletion E) (((M * R : ℕ) : E) * x) * ((y⁻¹ : (Af E)ˣ) : Af E) P = _
    rw [map_mul, map_natCast, map_natCast]
    push_cast
    ring
  have hx1 : Valued.v (algebraMap E (P.adicCompletion E) x) ≤ 1 := by
    have h2 : Valued.v (algebraMap E (P.adicCompletion E) x) = P.valuation E x := by
      rw [← HeightOneSpectrum.valuedAdicCompletion_eq_valuation' P]
      rfl
    rw [h2]
    have : x = algebraMap (𝓞 E) E ⟨x, hx⟩ := rfl
    rw [this]
    exact P.valuation_le_one _
  rw [e, map_mul, GlobalTheory.CMVal.LatEnt.radN, map_mul]
  exact mul_le_of_le_one_right' (mul_le_one' hx1 (hMz P))

end GlobalTheory.HilbFam.LatDen
end

section

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.CMVal.LatEnt

namespace GlobalTheory.CMVal.LatEnt.Res

open GlobalTheory.CMVal.PicFin

theorem mk_eq_iff {E : Type} [Field E] [NumberField E] {N : ℕ} (hN : 0 < N) (z a : intR E) :
    Ideal.Quotient.mk (Ideal.span {(N : intR E)}) z = Ideal.Quotient.mk _ a ↔
      ∀ w, Valued.v (z.1 w - a.1 w) ≤ radN E N w := by
  have hn0 : (N : E) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  rw [Ideal.Quotient.eq, Ideal.mem_span_singleton]
  constructor
  · rintro ⟨β, hβ⟩ w
    have h3 : z.1 - a.1 = (N : Af E) * β.1 := congrArg Subtype.val hβ
    rw [← map_natCast (algebraMap E (Af E))] at h3
    have h4 : z.1 w - a.1 w = algebraMap E (w.adicCompletion E) (N : E) * β.1 w := congrArg (fun y : Af E => y w) h3
    rw [h4, map_mul, map_natCast]
    exact mul_le_of_le_one_right' ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 (β.2 w))
  · intro hz
    refine ⟨⟨algebraMap E (Af E) (N : E)⁻¹ * (z.1 - a.1), fun P => ?_⟩, Subtype.ext ?_⟩
    · have h0 := GlobalTheory.AdLat.valued_natCast_ne_zero P hN
      show Valued.v (algebraMap E (P.adicCompletion E) (N : E)⁻¹ * (z.1 P - a.1 P)) ≤ 1
      rw [map_mul, map_inv₀, map_inv₀, map_natCast, inv_mul_le_iff₀ (zero_lt_iff.2 h0), mul_one]
      exact hz P
    · show z.1 - a.1 = (N : Af E) * (algebraMap E (Af E) (N : E)⁻¹ * (z.1 - a.1))
      rw [← map_natCast (algebraMap E (Af E)), ← mul_assoc, ← map_mul, mul_inv_cancel₀ hn0, map_one, one_mul]

theorem exists_residues : ∀ (E : Type) [Field E] [NumberField E] (N : ℕ), 0 < N → ∃ R : Finset (Af E),
    (∀ a ∈ R, ∀ w, Valued.v (a w) ≤ 1) ∧ ∀ z : Af E, (∀ w, Valued.v (z w) ≤ 1) →
      ∃! a, a ∈ R ∧ ∀ w, Valued.v (z w - a w) ≤ radN E N w := by
  classical
  intro E _ _ N hN
  haveI := finite_quot (E := E) hN.ne'
  haveI := Fintype.ofFinite (intR E ⧸ Ideal.span {(N : intR E)})
  choose s hs using Ideal.Quotient.mk_surjective (I := Ideal.span {(N : intR E)})
  refine ⟨Finset.univ.image fun q => (s q).1, fun a ha w => ?_, fun z hz => ?_⟩
  · obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 ha
    exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 ((s q).2 w)
  · let z' : intR E := ⟨z, fun w => (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 (hz w)⟩
    refine ⟨(s (Ideal.Quotient.mk _ z')).1, ⟨Finset.mem_image.2 ⟨_, Finset.mem_univ _, rfl⟩,
      (mk_eq_iff hN z' _).1 (hs _).symm⟩, ?_⟩
    rintro a ⟨ha, h⟩
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 ha
    rw [(mk_eq_iff hN z' (s q)).2 h, hs]

end GlobalTheory.CMVal.LatEnt.Res
end
end

section

open IsLocalRing GlobalTheory.FormalOrigin

theorem _root_.GlobalTheory.T.derivation_extends_taylorPowerSeriesRing : ∀ (R A : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] [CommRing A] [IsLocalRing A] [IsNoetherianRing A] (inc : R →+* A) (ev : A →+* R), (∀ r, ev (inc r) = r) → ∀ (n : ℕ) (ds : Fin n → Derivation ℤ A A) (z : Fin n → A), (∀ i, ev (z i) = 0) → (∀ a i, ev (ds a (z i)) = if a = i then 1 else 0) → maximalIdeal A = (maximalIdeal R).map inc ⊔ Ideal.span (Set.range z) → (∀ a r, ds a (inc r) = 0) → ∀ (d : Derivation ℤ A A) (D : Derivation ℤ R R), (∀ r, d (inc r) = inc (D r)) → ∃ dΩ : Derivation ℤ (MvPowerSeries (Fin n) R) (MvPowerSeries (Fin n) R), (∀ r, dΩ (MvPowerSeries.C r) = MvPowerSeries.C (D r)) ∧ ∀ f, dΩ (taylor ev (fun i => ⇑(ds i)) f) = taylor ev (fun i => ⇑(ds i)) (d f) := by
  first | exact @GlobalTheory.FormalOrigin.Extend.derivation_extends | exact GlobalTheory.FormalOrigin.Extend.derivation_extends | (intros; apply GlobalTheory.FormalOrigin.Extend.derivation_extends <;> assumption)
end
