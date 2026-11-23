module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle001
public import Development.AbelianVarietyTheory.Definitions.Degenerations.PlOrdSomeOfAssociated
public import Mathlib.Basic.Complex.Basic
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle032
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle025
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle029
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsMonHomExtension
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle062
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.HomBaseChangeBijectiveOfLeNilradical
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.LocallyOfFinitePresentationDiagMap
import Mathlib.Algebra.AffineMonoid.UniqueSums
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsGrpObjOfStrictBirationalLaw
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.QuasiAffineSubgroupContainingTorusEqTorus
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle008
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle054
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle003
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle057
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle023
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CoordOfHasWeight
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle017
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle051
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle055
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle058
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle004
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.EffectiveEpi.Comp
import Mathlib.CategoryTheory.ExtremalEpi
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsaRos
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle049

@[expose] public section

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

namespace GlobalTheory.SS
open Polynomial

theorem exists_surj_of_torsion {N : Type} [AddCommGroup N] [Finite N] (l n c : ℕ) (hn : ∀ x : N, l ^ n • x = 0)
    (hc : Nat.card {x : N // l • x = 0} ≤ c) :
    ∃ π : (Fin c → ℤ) →ₗ[ℤ] N, Function.Surjective π := by
  classical
  let m : N →+ N := nsmulAddMonoidHom l
  have h1 : Nat.card (N ⧸ m.range) = Nat.card m.ker := by
    have a := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup m.range
    have b := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup m.ker
    rw [Nat.card_congr (QuotientAddGroup.quotientKerEquivRange m).toEquiv, _root_.mul_comm] at b
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos (a.symm.trans b)
  have h2 : Nat.card (N ⧸ m.range) ≤ Nat.card (Fin c) := by
    rw [h1, Nat.card_fin]; exact hc
  obtain ⟨e⟩ : Nonempty ((N ⧸ m.range) ↪ Fin c) := by
    have := Fintype.ofFinite (N ⧸ m.range)
    apply Function.Embedding.nonempty_of_card_le
    simpa using h2
  let v : Fin c → N := fun i => (Function.invFun e i).out
  let π : (Fin c → ℤ) →ₗ[ℤ] N := Fintype.linearCombination ℤ v
  have hv : ∀ i, v i ∈ LinearMap.range π := fun i => ⟨Pi.single i 1, by simp [π]⟩
  have key : ∀ j : ℕ, ∀ x : N, ∃ y : N, x - l ^ j • y ∈ LinearMap.range π := by
    intro j
    induction j with
    | zero => exact fun x => ⟨x, by simp⟩
    | succ j ih =>
      intro x
      obtain ⟨y, hy⟩ := ih x
      have h3 : (QuotientAddGroup.mk (v (e y)) : N ⧸ m.range) = QuotientAddGroup.mk y := by
        simp only [v, QuotientAddGroup.out_eq']
        exact Function.leftInverse_invFun e.injective _
      obtain ⟨z, hz⟩ := QuotientAddGroup.eq.1 h3
      have hz' : l • z = - v (e y) + y := hz
      refine ⟨z, ?_⟩
      have : x - l ^ (j + 1) • z = (x - l ^ j • y) + l ^ j • v (e y) := by
        rw [pow_succ, mul_smul, hz', smul_add, smul_neg]; abel
      rw [this]
      exact add_mem hy (nsmul_mem (hv _) _)
  refine ⟨π, fun x => ?_⟩
  obtain ⟨y, hy⟩ := key n x
  rwa [hn, sub_zero] at hy

theorem aeval_intertwine {M N : Type} [AddCommGroup M] [AddCommGroup N] (π : M →ₗ[ℤ] N) (S : Module.End ℤ M)
    (T : Module.End ℤ N) (h : ∀ x, T (π x) = π (S x)) (p : ℤ[X]) : ∀ x, aeval T p (π x) = π (aeval S p x) := by
  induction p using Polynomial.induction_on with
  | C a => intro x; rw [aeval_C, aeval_C, Module.algebraMap_end_apply, Module.algebraMap_end_apply, map_smul]
  | add p q hp hq => intro x; simp [hp, hq]
  | monomial n a ih =>
    intro x
    rw [pow_succ, ← _root_.mul_assoc, map_mul, map_mul (aeval _) _ X, aeval_X, aeval_X, Module.End.mul_apply,
      Module.End.mul_apply, h, ih]

theorem exists_monic_of_surj {N : Type} [AddCommGroup N] (c : ℕ) (π : (Fin c → ℤ) →ₗ[ℤ] N)
    (hπ : Function.Surjective π) (T : Module.End ℤ N) :
    ∃ χ : ℤ[X], χ.Monic ∧ χ.natDegree = c ∧ aeval T χ = 0 := by
  obtain ⟨S, hS⟩ := Module.projective_lifting_property π (T ∘ₗ π) hπ
  have h := aeval_intertwine π S T fun x => (LinearMap.congr_fun hS x).symm
  refine ⟨S.charpoly, S.charpoly_monic, by simp [LinearMap.charpoly_natDegree], ?_⟩
  ext x
  obtain ⟨y, rfl⟩ := hπ x
  rw [h, LinearMap.aeval_self_charpoly]
  simp

theorem exists_monic_torsion {M : Type} [AddCommGroup M] (l : ℕ) (hf : ∀ n : ℕ, Finite {x : M // l ^ n • x = 0})
    (T : Module.End ℤ M) : ∃ r : ℕ, ∀ n : ℕ, ∃ χ : ℤ[X], χ.Monic ∧ χ.natDegree = r ∧
      ∀ x : M, l ^ n • x = 0 → aeval T χ x = 0 := by
  refine ⟨Nat.card {x : M // l ^ 1 • x = 0}, fun n => ?_⟩
  let N : Submodule ℤ M := LinearMap.ker (l ^ n • LinearMap.id)
  have hN : ∀ x : M, x ∈ N ↔ l ^ n • x = 0 := fun x => Iff.rfl
  have : Finite N := by
    have := hf n
    exact Finite.of_equiv _ (Equiv.subtypeEquivRight fun x => (hN x).symm)
  have hT : ∀ x ∈ N, T x ∈ N := fun x hx => by
    rw [hN] at hx ⊢
    rw [← map_nsmul, hx, map_zero]
  have := hf 1
  obtain ⟨π, hπ⟩ := exists_surj_of_torsion (N := N) l n (Nat.card {x : M // l ^ 1 • x = 0})
    (fun x => Subtype.ext ((hN _).1 x.2))
    (Nat.card_le_card_of_injective (fun x => (⟨x.1.1, by rw [pow_one]; exact congrArg Subtype.val x.2⟩ :
      {x : M // l ^ 1 • x = 0})) fun x y h => Subtype.ext (Subtype.ext (by simpa using h)))
  obtain ⟨χ, h1, h2, h3⟩ := exists_monic_of_surj _ π hπ (T.restrict hT)
  refine ⟨χ, h1, h2, fun x hx => ?_⟩
  have h := aeval_intertwine N.subtype (T.restrict hT) T (fun _ => rfl) χ ⟨x, (hN x).2 hx⟩
  rw [h3] at h
  exact h

section
variable {S : Scheme.{0}} {B : Over S} [GrpObj B] [IsCommMonObj B]

noncomputable def ptEnd (F : End B) (hF : IsMonHom F.asHom) (Z : Over S) :
    Module.End ℤ (Additive (Z ⟶ B)) :=
  (MonoidHom.toAdditive (IsMonHom.monoidHom F.asHom Z)).toIntLinearMap

theorem ptEnd_pow (F : End B) (hF : IsMonHom F.asHom) {Z : Over S} (x : Z ⟶ B) (n : ℕ) :
    (ptEnd F hF Z ^ n) (Additive.ofMul x) = Additive.ofMul (x ≫ (F ^ n).asHom) := by
  induction n with
  | zero => simp only [pow_zero, Module.End.one_apply, End.one_asHom, Category.comp_id]
  | succ n ih =>
    rw [pow_succ', pow_succ', Module.End.mul_apply, ih, End.mul_asHom]
    exact congrArg Additive.ofMul (Category.assoc x (F ^ n).asHom F.asHom)

theorem aeval_ptEnd (F : End B) (hF : IsMonHom F.asHom) {Z : Over S} (x : Z ⟶ B) (P : ℤ[X]) :
    aeval (ptEnd F hF Z) P (Additive.ofMul x) = Additive.ofMul (polyPt F P x) := by
  rw [aeval_eq_sum_range, LinearMap.sum_apply, polyPt, ← List.prod_toFinset _ List.nodup_range,
    List.toFinset_range, ofMul_prod]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [LinearMap.smul_apply, ptEnd_pow, ofMul_zpow]

noncomputable def evalPt {Z : Over S} (x : Z ⟶ B) : Additive (B ⟶ B) →ₗ[ℤ] Additive (Z ⟶ B) :=
  (AddMonoidHom.mk' (fun f => Additive.ofMul (x ≫ Additive.toMul f))
    fun f g => by rw [toMul_add, MonObj.comp_mul, ofMul_mul]).toIntLinearMap

noncomputable def homSub (B : Over S) [GrpObj B] [IsCommMonObj B] : Submodule ℤ (Additive (B ⟶ B)) :=
  AddSubgroup.toIntSubmodule
    { carrier := {f | IsMonHom (Additive.toMul f)}
      zero_mem' := by
        change IsMonHom (1 : B ⟶ B)
        rw [Hom.one_def]; infer_instance
      add_mem' := fun {f g} hf hg => by
        change IsMonHom (Additive.toMul f) at hf
        change IsMonHom (Additive.toMul g) at hg
        change IsMonHom (Additive.toMul f * Additive.toMul g)
        rw [Hom.mul_def]; infer_instance
      neg_mem' := fun {f} hf => by
        change IsMonHom (Additive.toMul f) at hf
        change IsMonHom (Additive.toMul f)⁻¹
        infer_instance }

end

theorem exists_poly_normSq_roots : ∀ (k : Type) [Field k] [IsAlgClosed k] (B : Over (Sp k)) [GrpObj B], IsAbelianScheme B → ∀ (L : LB B.left), AmpleCub B L → ∀ (F : End B) (q : ℕ), IsMonHom F.asHom → PullPow F.asHom.left L q → ∃ P : Polynomial ℤ, P ≠ 0 ∧ (∀ β : ℂ, Polynomial.aeval β P = 0 → Complex.normSq β = q) ∧ ∀ x : (𝟙_ (Over (Sp k)) ⟶ B), polyPt F P x = 1 := by
  intro k _ _ B _ hB L hL F q hF hq
  have := hB.comm
  obtain ⟨l, hl2, hl⟩ : ∃ l : ℕ, 2 ≤ l ∧ (l : k) ≠ 0 := by
    by_cases h : ((2 : ℕ) : k) = 0
    · refine ⟨2 + 1, by norm_num, ?_⟩
      rw [Nat.cast_add, h]; simp
    · exact ⟨2, le_rfl, h⟩
  have hD := fun n : ℕ => GlobalTheory.T.abelianVariety_torsion_finite_endomorphism_divisible k B hB (l ^ n) (by rw [Nat.cast_pow]; exact pow_ne_zero _ hl)
  obtain ⟨Q, Q1, Q2, Q3, Q4⟩ := GlobalTheory.T.exists_positiveDefinite_quadraticForm_endomorphisms k B hB L hL
  obtain ⟨r, hr⟩ := exists_monic_torsion (M := Additive (𝟙_ (Over (Sp k)) ⟶ B)) l (fun n => (hD n).1) (ptEnd F hF _)
  have hT : ∀ f ∈ homSub B, ptEnd F hF B f ∈ homSub B := fun f hf => by
    change IsMonHom (Additive.toMul f) at hf
    change IsMonHom (Additive.toMul f ≫ F.asHom)
    infer_instance
  let e : homSub B := ⟨Additive.ofMul (𝟙 B), inferInstanceAs (IsMonHom (𝟙 B))⟩
  let φ : Module.End ℤ (homSub B) := (ptEnd F hF B).restrict hT
  have hev : ∀ (x : 𝟙_ (Over (Sp k)) ⟶ B) (p : ℤ[X]), aeval (ptEnd F hF _) p (Additive.ofMul x) =
      Additive.ofMul (x ≫ Additive.toMul (aeval φ p e).1) := fun x p => by
    have h := aeval_intertwine (evalPt x ∘ₗ (homSub B).subtype) φ (ptEnd F hF _)
      (fun f => congrArg Additive.ofMul (Category.assoc x (Additive.toMul f.1) F.asHom)) p e
    have h' : (evalPt x ∘ₗ (homSub B).subtype) e = Additive.ofMul x := congrArg Additive.ofMul (Category.comp_id x)
    rw [h'] at h
    exact h
  obtain ⟨P, hP, h0, hβ⟩ := GlobalTheory.T.similitude_definite_form_isAlgebraic_on_vector (homSub B) (fun f => Q (Additive.toMul f.1)) φ e q l r hl2
    (fun x y => by
      have := Q1 (Additive.toMul x.1) (Additive.toMul y.1)
      rw [sub_eq_add_neg]
      exact this)
    (fun x => Q2 _) (fun x hx => Subtype.ext (Q3 _ x.2 hx)) (fun x => Q4 _ q hq _)
    (fun n => by
      obtain ⟨χ, h1, h2, h3⟩ := hr n
      obtain ⟨g, hg, hg'⟩ := (hD n).2 (Additive.toMul (aeval φ χ e).1) (aeval φ χ e).2 fun x hx =>
        (hev x χ).symm.trans (h3 (Additive.ofMul x) hx)
      exact ⟨χ, ⟨Additive.ofMul g, hg⟩, h1, h2, Subtype.ext hg'⟩)
  refine ⟨P, hP, hβ, fun x => ?_⟩
  have h := (aeval_ptEnd F hF x P).symm.trans (hev x P)
  rw [h0] at h
  exact h.trans (MonObj.comp_one x)

end GlobalTheory.SS
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
open GlobalTheory.SS.ArcInf

namespace GlobalTheory.SS.ArcInf

theorem smConn_gm (k : Type) [Field k] : SmConn (Gm (Sp k)) :=
  ⟨inferInstance, inferInstance, inferInstance, inferInstance, inferInstance⟩

noncomputable def selfIso (k : Type) [CommRing k] : algOver k k ≅ 𝟙_ (Over (Sp k)) :=
  Over.isoMk (Iso.refl _) (by
    show 𝟙 _ ≫ 𝟙 _ = spMap (algebraMap k k)
    rw [Category.comp_id]
    exact (Spec.map_id _).symm)

theorem algHom_algebraMap_eq_eval {k B : Type} [CommRing k] [CommRing B] [Algebra k B]
    [Algebra (Polynomial k) B] [IsScalarTower k (Polynomial k) B] (x : B →ₐ[k] k) (q : Polynomial k) :
    x (algebraMap (Polynomial k) B q) = q.eval (x (algebraMap (Polynomial k) B Polynomial.X)) := by
  have h := Polynomial.aeval_algHom_apply (x.comp (IsScalarTower.toAlgHom k (Polynomial k) B))
    Polynomial.X q
  rw [Polynomial.aeval_X_left_apply, Polynomial.coe_aeval_eq_eval] at h
  exact h.symm

theorem exists_oneParameter_of_rational_family : ∀ (k : Type) [Field k] [IsAlgClosed k] (G : Over (Sp k)) [GrpObj G] (A : Type) [CommRing A] [Algebra k A] (j : algOver k A ⟶ G) (ε : A →ₐ[k] k) (r : ℕ) (f : Fin r → A) (Pd : Polynomial k) (P : Fin r → Polynomial k) (ψ : k → (A →ₐ[k] k)), SmConn G → IsChart G j ε f → Pd ≠ 0 → (∃ i, P i ≠ 0) → (∀ t, t ≠ 0 → Pd.eval t ≠ 0 → ∀ i, ψ t (f i) * Pd.eval t = (P i).eval t) → (∀ t t', t ≠ 0 → t' ≠ 0 → Pd.eval t ≠ 0 → Pd.eval t' ≠ 0 → Pd.eval (t * t') ≠ 0 → (algOverHom (ψ t) ≫ j) * (algOverHom (ψ t') ≫ j) = algOverHom (ψ (t * t')) ≫ j) → ∃ F : Gm (Sp k) ⟶ G, IsMonHom F ∧ F ≠ 1 := by
  intro k _ _ G _ A _ _ j ε r f Pd P ψ hG hc hPd hP hψ hmul
  obtain ⟨χ, hχ⟩ := GlobalTheory.T.exists_algHom_localizationAway_of_rational_points' k A r f Pd P ψ hc.2.2.1 hPd hψ
  obtain ⟨jj, hjj, hjm⟩ := GlobalTheory.T.exists_multiplicativeGroup_open_nonvanishing_polynomial k Pd
  have hq : Polynomial.X * Pd ≠ 0 := mul_ne_zero Polynomial.X_ne_zero hPd
  have hinj : Function.Injective
      (algebraMap (Polynomial k) (Localization.Away (Polynomial.X * Pd))) :=
    IsLocalization.injective _ (powers_le_nonZeroDivisors_of_noZeroDivisors hq)
  have hnt : Nontrivial (Localization.Away (Polynomial.X * Pd)) := hinj.nontrivial
  have hu : IsUnit (algebraMap (Polynomial k) (Localization.Away (Polynomial.X * Pd))
      (Polynomial.X * Pd)) := IsLocalization.Away.algebraMap_isUnit _
  have hpt : ∀ x : Localization.Away (Polynomial.X * Pd) →ₐ[k] k,
      x (algebraMap (Polynomial k) _ Polynomial.X) ≠ 0 ∧
      Pd.eval (x (algebraMap (Polynomial k) _ Polynomial.X)) ≠ 0 ∧
      x.comp χ = ψ (x (algebraMap (Polynomial k) _ Polynomial.X)) := by
    intro x
    have h := (hu.map x).ne_zero
    rw [algHom_algebraMap_eq_eval, Polynomial.eval_mul, Polynomial.eval_X] at h
    have h1 := left_ne_zero_of_mul h
    have h2 := right_ne_zero_of_mul h
    refine ⟨h1, h2, hc.hom_ext fun i => mul_right_cancel₀ h2 ?_⟩
    rw [hψ _ h1 h2, AlgHom.comp_apply, ← algHom_algebraMap_eq_eval x Pd, ← map_mul, hχ,
      algHom_algebraMap_eq_eval x (P i)]
  obtain ⟨F, hF, hFj⟩ := GlobalTheory.GenericHom.exists_monHom_extension k (Gm (Sp k)) G
    (algOver k (Localization.Away (Polynomial.X * Pd))) (smConn_gm k) hG jj (algOverHom χ ≫ j) hjj
    (inferInstanceAs (Nonempty (PrimeSpectrum (Localization.Away (Polynomial.X * Pd))))) (by
      intro x y z h
      obtain ⟨x', hx⟩ := algOverHom_surjective ((selfIso k).hom ≫ x)
      obtain ⟨y', hy⟩ := algOverHom_surjective ((selfIso k).hom ≫ y)
      obtain ⟨z', hz⟩ := algOverHom_surjective ((selfIso k).hom ≫ z)
      have h' := hjm x' y' z' (by
        rw [hx, hy, hz, Category.assoc, Category.assoc, Category.assoc, ← MonObj.comp_mul, h])
      obtain ⟨a1, a2, a3⟩ := hpt x'
      obtain ⟨b1, b2, b3⟩ := hpt y'
      obtain ⟨c1, c2, c3⟩ := hpt z'
      have hm := hmul _ _ a1 b1 a2 b2 (h' ▸ c2)
      rw [h', ← a3, ← b3, ← c3, algOverHom_comp, algOverHom_comp, algOverHom_comp, hx, hy, hz] at hm
      simp only [Category.assoc] at hm
      rw [← MonObj.comp_mul] at hm
      exact (cancel_epi (selfIso k).hom).1 hm)
  refine ⟨F, hF, fun h1 => ?_⟩
  obtain ⟨i, hi⟩ := hP
  have e : χ = (Algebra.ofId k _).comp ε := by
    apply eq_of_comp_eq hc.1
    rw [← hFj, h1, MonObj.comp_one, algOverHom_comp, Category.assoc, hc.2.1, MonObj.comp_one]
  have h2 := hχ i
  rw [e, AlgHom.comp_apply, hc.2.2.2, _root_.map_zero, zero_mul] at h2
  exact hi (hinj (h2.symm.trans (_root_.map_zero _).symm))

end GlobalTheory.SS.ArcInf
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

theorem _root_.GlobalTheory.T.isSemiAbelian_of_proper_generic_torusExtension_special : ∀ (W L : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field L] [Algebra W L] [IsFractionRing W L] (G : Over (Sp W)) [GrpObj G], SmConn G → IsProper ((Over.pullback (spMap (algebraMap W L))).obj G).hom → ∀ (k : Type) [Field k] (ρ : W →+* k), RingHom.ker ρ = IsLocalRing.maximalIdeal W → ρ.IsIntegral → Nonempty (TorusExtension ((Over.pullback (spMap ρ)).obj G)) → IsSemiAbelian G := by
  first | exact @GlobalTheory.SS.isSemiAbelian_of_proper_generic_of_torusExtension | exact GlobalTheory.SS.isSemiAbelian_of_proper_generic_of_torusExtension | (intros; apply GlobalTheory.SS.isSemiAbelian_of_proper_generic_of_torusExtension <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ
theorem _root_.GlobalTheory.T.kb_isAlgClosed_and_conj' : ∀ (p : ℕ) [Fact p.Prime], IsAlgClosed (kb p) ∧ (∀ x : kb p, x ≠ 0 → ∃ n : ℕ, 1 ≤ n ∧ x ^ n = 1) ∧ ∀ (F : Type) [Field F] [Finite F] (r r' : F →+* kb p), ∃ σ : OO p ≃+* OO p, ∀ (x : F) (a : OO p), IsLocalRing.residue (OO p) a = r x → IsLocalRing.residue (OO p) (σ a) = r' x := by
  first | exact @GlobalTheory.ZJ.kb_isAlgClosed_and_conj | exact GlobalTheory.ZJ.kb_isAlgClosed_and_conj | (intros; apply GlobalTheory.ZJ.kb_isAlgClosed_and_conj <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

theorem _root_.GlobalTheory.T.exists_grpObj_of_strictBirationalLaw : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [Field K] [Algebra R K], SH R K → ∀ (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ M : Model R A, Strict M → ∃ (G : Model R A) (_ : GrpObj G.Y), SmConn G.Y ∧ IsMonHom G.e.hom ∧ ∀ a : (𝟙_ (Over (Sp K)) ⟶ A), GenIso M M (transl a).hom → ∃ s : 𝟙_ (Over (Sp R)) ⟶ G.Y, spMap (algebraMap R K) ≫ s.left = a.left ≫ G.j := by
  first | exact @GlobalTheory.SS.exists_grpObj_of_strict | exact GlobalTheory.SS.exists_grpObj_of_strict | (intros; apply GlobalTheory.SS.exists_grpObj_of_strict <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

theorem _root_.GlobalTheory.T.quasiAffine_subgroup_containing_torus_eq_torus : ∀ (k : Type) [Field k] [IsAlgClosed k] (G : Over (Sp k)) [GrpObj G], SmConn G →  ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (B : Over (Sp k)) [GrpObj B] (i : splitTorus (Sp k) X ⟶ G) (q : G ⟶ B), IsQuot i q → IsAbelianScheme B → ∀ (N : Over (Sp k)) [GrpObj N] (ν : N ⟶ G) (i' : splitTorus (Sp k) X ⟶ N), SmConn N → IsMonHom ν → IsClosedImmersion ν.left → i' ≫ ν = i → (∀ x : N.left, ∃ f : Γ(N.left, ⊤), x ∈ N.left.basicOpen f ∧ IsAffineOpen (N.left.basicOpen f)) → ∀ x : (𝟙_ (Over (Sp k)) ⟶ N), ∃ t : (𝟙_ (Over (Sp k)) ⟶ splitTorus (Sp k) X), t ≫ i = x ≫ ν := by
  first | exact @GlobalTheory.QuasiAffineTorus.main | exact GlobalTheory.QuasiAffineTorus.main | (intros; apply GlobalTheory.QuasiAffineTorus.main <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ
theorem _root_.GlobalTheory.T.nonempty_law_abelianSchemeProperClosure : ∀ C : Core, SmoothOfRelativeDimension C.g C.GG.hom → C.TestCart → (∃ m : C.GG ⊗ C.GG ⟶ C.GG, ∀ φ₂ : (C.A ⊗ C.A).left ⟶ (C.GG ⊗ C.GG).left, IsSquare C.a φ₂ → φ₂ ≫ m.left = (μ[C.A]).left ≫ C.a) → (∃ i : C.GG ⟶ C.GG, C.a ≫ i.left = (ι[C.A]).left ≫ C.a) → Nonempty C.Law := by
  first | exact @GlobalTheory.ZJ.Core.nonempty_law | exact GlobalTheory.ZJ.Core.nonempty_law | (intros; apply GlobalTheory.ZJ.Core.nonempty_law <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ

namespace GlobalTheory.ZJ

theorem SplitAll.fieldPoint {Z : Scheme.{0}} {G : Over Z} [GrpObj G] (h : SplitAll G) (K : Type) [Field K]
    (t : Sp K ⟶ Z) : ∃ E : SplitExt (Sp K), E.IsGt ((Over.pullback t).obj G) := by
  obtain ⟨z, r, rfl⟩ : ∃ (z : Z) (r : Sp K ⟶ Sp (Z.residueField z)), t = r ≫ Z.fromSpecResidueField z :=
    ⟨_, _, (Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField K Z t).symm⟩
  obtain ⟨E, ⟨d⟩⟩ := h z
  have : IsMonHom (pullCompIso r (Z.fromSpecResidueField z) G).symm.hom :=
    inferInstanceAs (IsMonHom (pullCompIso r (Z.fromSpecResidueField z) G).inv)
  obtain ⟨E', _, _, _, _, hE'⟩ := gtBaseChange _ _ r E _ ⟨d⟩
  exact ⟨E', isGt_of_iso (pullCompIso r (Z.fromSpecResidueField z) G).symm hE'⟩

theorem isSemiAbelian_of_splitAll : ∀ (Z : Scheme.{0}) (G : Over Z) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] [IsSeparated G.hom] [QuasiCompact G.hom], SplitAll G → IsSemiAbelian G ∧ (∀ (K : Type) [Field K] (t : Sp K ⟶ Z), ∃ E : SplitExt (Sp K), E.IsGt ((Over.pullback t).obj G)) ∧ ∀ x : Z, ∃ (k : Type) (_ : Field k) (_ : Algebra (Z.residueField x) k), FiniteDimensional (Z.residueField x) k ∧ Algebra.IsSeparable (Z.residueField x) k ∧ ∃ S : SplitExt (Sp k), S.IsGt ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap (Z.residueField x) k)) ≫ Z.fromSpecResidueField x)).obj G) := by
  intro Z G _ hc hs hsep hq h
  refine ⟨⟨hc, hs, hsep, hq, ⟨geometrically_iff_of_isClosedUnderIsomorphisms.mpr fun K _ q => ?_⟩,
    fun Ω _ _ q => ?_⟩, h.fieldPoint, fun x => ⟨Z.residueField x, inferInstance, inferInstance, inferInstance,
      inferInstance, h.fieldPoint _ _⟩⟩
  · obtain ⟨E, hE⟩ := h.fieldPoint K q
    have hg : GeometricallyConnected (pullback.snd G.hom q) :=
      (UnitRigidity.smooth_geometricallyConnected_of_isGt E _ hE).2
    rw [← (pullbackLeftPullbackSndIso G.hom q (𝟙 _) ≪≫ pullback.congrHom rfl (Category.id_comp q)).hom.homeomorph.connectedSpace_iff]
    exact pullback_of_geometrically hg.1 K (𝟙 _)
  · obtain ⟨E, hE⟩ := h.fieldPoint Ω q
    exact nonempty_torusExtension_of_isGt E _ hE

end GlobalTheory.ZJ
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ThetaReal

theorem _root_.GlobalTheory.T.exists_monomial_matrices_projectiveRep : ∀ (o A M : Type) [CommRing o] [CommRing A] [Nontrivial A] [AddCommGroup M] [Module A M] (f : o →+* A), Function.Injective f → ∀ (g m r N : ℕ), N = m ^ 2 → 1 ≤ m → 1 ≤ r → ∀ (ζ : o) (q : ℕ), 1 ≤ q → ζ ^ q = 1 → ∀ (_ : Module.Basis (Fin (N ^ g)) A M) (u : (Fin g ⊕ Fin g → ZMod (r * N)) → M →ₗ[A] M) (s₀ : M), (∀ a, r • a = 0 → ∀ v, u a v = v) → (∀ a b, ∃ e : ℕ, ∀ v, u a (u b v) = f (ζ ^ e) • u (a + b) v) → (∀ a b, r • eStd g _ a b = 0 → ∀ v, u a (u b v) = u (a + b) v) → (∀ a, (r * m) • a = 0 → u a s₀ = s₀) → Submodule.span A (Set.range fun a => u a s₀) = ⊤ → ∃ (J : Type) (_ : Fintype J) (ρ : (Fin g ⊕ Fin g → ZMod (r * N)) → Matrix J J o) (s : Module.Basis J A M) (i₀ : J), Fintype.card J = N ^ g ∧ s i₀ = s₀ ∧ (∀ a, r • a = 0 → ρ a = 1) ∧ (∀ a b, ∃ k : ℕ, ρ a * ρ b = ζ ^ k • ρ (a + b)) ∧ (∀ a b, r • eStd g _ a b = 0 → ρ a * ρ b = ρ (a + b)) ∧ (∀ a i, u a (s i) = ∑ l, f (ρ a l i) • s l) ∧ ∀ i, ∃ a, ∃ e : ℕ, ∀ l, ρ a l i₀ = if l = i then ζ ^ e else 0 := by
  first | exact @GlobalTheory.ThetaReal.exists_monomial_matrices | exact GlobalTheory.ThetaReal.exists_monomial_matrices | (intros; apply GlobalTheory.ThetaReal.exists_monomial_matrices <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ

theorem _root_.GlobalTheory.T.geometricallyConnected_basePointFree_generic_fibre : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] [IsSeparated G.hom] [QuasiCompact G.hom] (C : Charts G.left) (d : ℕ) (c : Fin d → C.Cl) (Sg : Set (Sp R)) [IsAffineHom (pullback.fst G.hom (Out.jK R))], Dense Sg → C.SplitOn c Sg → GeometricallyConnected ((Over.pullback (Out.jK R)).obj G).hom ∧ ∀ (n : Fin d) (x : ((Over.pullback (Out.jK R)).obj G).left), ∃ a j, C.wt j = c n ∧ x ∈ ((Over.pullback (Out.jK R)).obj G).left.basicOpen ((C.pull (pullback.fst G.hom (Out.jK R))).r a j) := by
  first | exact @GlobalTheory.GenericSplit.geometricallyConnected_and_basePointFree_generic | exact GlobalTheory.GenericSplit.geometricallyConnected_and_basePointFree_generic | (intros; apply GlobalTheory.GenericSplit.geometricallyConnected_and_basePointFree_generic <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

theorem _root_.GlobalTheory.T.valuation_eq_polarForm_of_weightZero_max : ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (q : QuadraticMap ℤ X ℝ) (g N : ℕ) (J : Type) (cls : J → X) (p : ℕ) [Fact p.Prime] (w : J → PadicAlgCl p) (ν : X →+ ℝ), Filter.Tendsto q Filter.cofinite Filter.atTop → Module.finrank ℤ X ≤ g → 1 + 2 * (g : ℝ) * (2 : ℝ) ^ ((g : ℝ) / 2) < N → (∀ i, Short q N (cls i)) → Ser q N cls w ν → (∃ i₀, cls i₀ = 0 ∧ ∀ i, ‖w i‖ ≤ ‖w i₀‖) → ∃ m, ∀ α, ν α = QuadraticMap.polar q m α := by
  first | exact @GlobalTheory.ZH.ValLat.main | exact GlobalTheory.ZH.ValLat.main | (intros; apply GlobalTheory.ZH.ValLat.main <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.ZH.ZHPre
variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {S : ThetaSys o Ω} {ρ : S.Real}

theorem isLocalHom_of_test {p : ℕ} [Fact p.Prime] {y₀ : S.R →+* PadicAlgCl p} (u : ρ.UTest p y₀)
    (jV : u.V →+* OO p)
    (hj : ∀ x, (jV x : PadicAlgCl p) = algebraMap (FractionRing u.V) _ (algebraMap u.V (FractionRing u.V) x)) :
    IsLocalHom jV := by
  refine ⟨fun x hx => ?_⟩
  have h1 : ‖(jV x : PadicAlgCl p)‖ = 1 :=
    le_antisymm ((mem_OO_iff _).1 (jV x).2) (not_lt.1 fun h => (not_isUnit_OO_iff _).2 h hx)
  have h0 : algebraMap u.V (FractionRing u.V) x ≠ 0 := fun h => by
    rw [hj, h, map_zero, norm_zero] at h1
    exact zero_ne_one h1
  obtain ⟨v, hv⟩ := (u.norm_le (algebraMap u.V (FractionRing u.V) x)⁻¹).1 (by
    rw [map_inv₀, ← hj, norm_inv, h1, inv_one])
  refine IsUnit.of_mul_eq_one v (IsFractionRing.injective u.V (FractionRing u.V) ?_)
  rw [map_mul, hv, mul_inv_cancel₀ h0, map_one]

end GlobalTheory.ZH.ZHPre
end
end
