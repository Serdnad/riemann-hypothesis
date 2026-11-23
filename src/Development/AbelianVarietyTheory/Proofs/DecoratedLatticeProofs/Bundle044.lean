module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSingle
public import Formalism.LocalToGlobal.HermitianForms.Bundle003
public import Formalism.SatakeDualWeyl.DefsCS
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle111
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsGlob
import Mathlib.Algebra.Module.StablyFree.Basic
public import Formalism.LocalToGlobal.TorsionIntegrality.CMGoodModels.Statement
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.LatticeOnly
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.Bundle004
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.MulStableIntegral
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
import Mathlib.RingTheory.PiTensorProduct
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
import Formalism.LocalToGlobal.Columns.CoefficientsModP.WeTransposeWordTransposeWord
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle003

@[expose] public section

section

open Matrix Formalism.UG Formalism.L2.DIV GlobalTheory.LevNorm

namespace GlobalTheory.LevNorm

section Idem

variable {R : Type} [CommRing R] {n : ℕ}

theorem matrix_mul_orthogonal_three_idempotents_smul (a b c : R) (hab : a * b = 0) (hac : a * c = 0) (hbc : b * c = 0) (ha : a * a = a)
    (hb : b * b = b) (hc : c * c = c) (M₁ M₂ M₃ N₁ N₂ N₃ : Matrix (Fin n) (Fin n) R) :
    (a • M₁ + b • M₂ + c • M₃) * (a • N₁ + b • N₂ + c • N₃) = a • (M₁ * N₁) + b • (M₂ * N₂) + c • (M₃ * N₃) := by
  have hba : b * a = 0 := by rw [mul_comm]; exact hab
  have hca : c * a = 0 := by rw [mul_comm]; exact hac
  have hcb : c * b = 0 := by rw [mul_comm]; exact hbc
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_add, smul_smul, hab, hac, hbc, hba, hca, hcb,
    ha, hb, hc, zero_smul, add_zero, zero_add]

theorem cT_smul' (τ : R →+* R) (a : R) (M : Matrix (Fin n) (Fin n) R) : cT τ (a • M) = τ a • cT τ M := by
  ext i j; simp [cT]

theorem cT_add' (τ : R →+* R) (M N : Matrix (Fin n) (Fin n) R) : cT τ (M + N) = cT τ M + cT τ N := by
  ext i j; simp [cT]

theorem cT_cT' (τ : R →+* R) (hτ : ∀ x, τ (τ x) = x) (M : Matrix (Fin n) (Fin n) R) : cT τ (cT τ M) = M := by
  ext i j; simp [cT, hτ]

theorem map_idem3 (a b c : R) (X Y : Matrix (Fin n) (Fin n) R) {T : Type} [CommRing T] (f : R →+* T) :
    (a • X + b • Y + c • (1 : Matrix (Fin n) (Fin n) R)).map f
      = f a • X.map f + f b • Y.map f + f c • (1 : Matrix (Fin n) (Fin n) T) := by
  ext i j; simp [Matrix.one_apply]; split_ifs <;> simp

theorem idem_split_inv (τ : R →+* R) (a b : R) (ha : a * a = a) (hb : b * b = b) (hab : a * b = 0)
    (G Gi X Xi : Matrix (Fin n) (Fin n) R) (hG : G * Gi = 1) (hGi : Gi * G = 1) (hX : X * Xi = 1) :
    (a • X + b • (Gi * cT τ Xi * G) + (1 - a - b) • (1 : Matrix (Fin n) (Fin n) R)) *
      (a • Xi + b • (Gi * cT τ X * G) + (1 - a - b) • (1 : Matrix (Fin n) (Fin n) R)) = 1 := by
  have hac : a * (1 - a - b) = 0 := by linear_combination -ha - hab
  have hbc : b * (1 - a - b) = 0 := by linear_combination -hb - hab
  have hc : (1 - a - b) * (1 - a - b) = 1 - a - b := by linear_combination ha + hb + 2 * hab
  rw [matrix_mul_orthogonal_three_idempotents_smul a b _ hab hac hbc ha hb hc]
  have h1 : Gi * cT τ Xi * G * (Gi * cT τ X * G) = 1 := by
    calc _ = Gi * (cT τ Xi * (G * Gi) * cT τ X) * G := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hG, Matrix.mul_one, ← cT_mul, hX, cT_one, Matrix.mul_one, hGi]
  rw [hX, h1, Matrix.mul_one, ← add_smul, ← add_smul, show a + b + (1 - a - b) = 1 by ring, one_smul]

theorem idem_split_unitary (τ : R →+* R) (hτ : ∀ x, τ (τ x) = x) (a b : R) (ha : a * a = a) (hb : b * b = b)
    (hab : a * b = 0) (hτa : τ a = b)
    (G Gi X Xi : Matrix (Fin n) (Fin n) R) (hG : G * Gi = 1) (hXi : Xi * X = 1) (hGh : cT τ G = G) :
    cT τ (a • X + b • (Gi * cT τ Xi * G) + (1 - a - b) • (1 : Matrix (Fin n) (Fin n) R)) * G *
      (a • X + b • (Gi * cT τ Xi * G) + (1 - a - b) • (1 : Matrix (Fin n) (Fin n) R)) = G := by
  have hac : a * (1 - a - b) = 0 := by linear_combination -ha - hab
  have hbc : b * (1 - a - b) = 0 := by linear_combination -hb - hab
  have hc : (1 - a - b) * (1 - a - b) = 1 - a - b := by linear_combination ha + hb + 2 * hab
  have hτb : τ b = a := by rw [← hτa, hτ]
  have hτc : τ (1 - a - b) = 1 - a - b := by rw [map_sub, map_sub, map_one, hτa, hτb]; ring
  have hGc : cT τ Gi * G = 1 := by
    have : cT τ Gi * cT τ G = 1 := by rw [← cT_mul, hG, cT_one]
    rwa [hGh] at this
  have hct : cT τ (a • X + b • (Gi * cT τ Xi * G) + (1 - a - b) • (1 : Matrix (Fin n) (Fin n) R))
      = a • (G * (Xi * cT τ Gi)) + b • cT τ X + (1 - a - b) • (1 : Matrix (Fin n) (Fin n) R) := by
    rw [cT_add', cT_add', cT_smul', cT_smul', cT_smul', hτa, hτb, hτc, cT_one, cT_mul, cT_mul, hGh, cT_cT' τ hτ]
    abel
  have hGs : G = a • G + b • G + (1 - a - b) • G := by
    rw [← add_smul, ← add_smul, show a + b + (1 - a - b) = 1 by ring, one_smul]
  rw [hct, show (a • (G * (Xi * cT τ Gi)) + b • cT τ X + (1 - a - b) • (1 : Matrix (Fin n) (Fin n) R)) * G
      = a • (G * (Xi * cT τ Gi) * G) + b • (cT τ X * G) + (1 - a - b) • (1 * G) by
    simp only [Matrix.add_mul, Matrix.smul_mul]]
  rw [matrix_mul_orthogonal_three_idempotents_smul a b _ hab hac hbc ha hb hc]
  have e1 : G * (Xi * cT τ Gi) * G * X = G := by
    calc _ = G * (Xi * (cT τ Gi * G) * X) := by simp only [Matrix.mul_assoc]
      _ = G := by rw [hGc, Matrix.mul_one, hXi, Matrix.mul_one]
  have e2 : cT τ X * G * (Gi * cT τ Xi * G) = G := by
    calc _ = cT τ X * (G * Gi) * cT τ Xi * G := by simp only [Matrix.mul_assoc]
      _ = G := by rw [hG, Matrix.mul_one, ← cT_mul, hXi, cT_one, Matrix.one_mul]
  rw [e1, e2, Matrix.one_mul, Matrix.mul_one, ← hGs]

end Idem

end GlobalTheory.LevNorm

namespace GlobalTheory.LevNorm

theorem exists_unitary_int_of_component {A : Type} [CommRing A] {S : Subring A} {P : Type} {k : P → Type}
    [∀ Q, Field (k Q)] {r : ∀ Q, S →+* k Q} (Z : PlaceSys A S P k r) (σ : A →+* A) (hσ : ∀ a, σ (σ a) = a)
    (hS : ∀ a ∈ S, σ a ∈ S) (n : ℕ) (G : GL (Fin n) S)
    (hG : cT σ ((bc S.subtype G : GL (Fin n) A) : Matrix (Fin n) (Fin n) A)
      = ((bc S.subtype G : GL (Fin n) A) : Matrix (Fin n) (Fin n) A))
    (Q Q' : P) (hQ : σ (Z.e Q) = Z.e Q') (hne : Q ≠ Q') (y : GL (Fin n) (Z.O Q)) :
    ∃ u : GL (Fin n) S, bc S.subtype u ∈ UJ σ ((bc S.subtype G : GL (Fin n) A) : Matrix (Fin n) (Fin n) A) ∧
      bc (Z.pO Q) u = y ∧ ∀ Q'', Q'' ≠ Q → Q'' ≠ Q' → bc (Z.pO Q'') u = 1 := by
  obtain ⟨x, hx1, hx2⟩ := Z.gl_single Q (bc (Z.O Q).subtype y)
  obtain ⟨X, hX⟩ := Z.gl_int (x := x) fun R => by
    by_cases h : R = Q
    · subst h; exact ⟨y, hx1.symm⟩
    · exact ⟨1, by rw [map_one, hx2 R h]⟩
  have hcomp : ∀ R, bc (Z.O R).subtype (bc (Z.pO R) X) = bc (Z.p R) x := fun R => by
    rw [← hX]; rfl
  have binj : ∀ R, Function.Injective (bc (n := Fin n) (Z.O R).subtype) := fun R g h e =>
    Units.ext (Matrix.map_injective Subtype.val_injective (congrArg Units.val e))
  have hXQ : bc (Z.pO Q) X = y := binj Q (by rw [hcomp, hx1])
  have hXR : ∀ R, R ≠ Q → bc (Z.pO R) X = 1 := fun R h => binj R (by rw [hcomp, hx2 R h, map_one])
  let τ : S →+* S := σ.restrict S S hS
  have hτv : ∀ s : S, (τ s : A) = σ s := fun s => rfl
  have hτ : ∀ s, τ (τ s) = s := fun s => Subtype.ext (by rw [hτv, hτv, hσ])
  let a : S := ⟨Z.e Q, Z.e_mem Q⟩
  let b : S := ⟨Z.e Q', Z.e_mem Q'⟩
  have ha : a * a = a := Subtype.ext (Z.e_idem Q)
  have hb : b * b = b := Subtype.ext (Z.e_idem Q')
  have hab : a * b = 0 := Subtype.ext (by
    show Z.e Q * Z.e Q' = 0
    refine Z.ext _ fun R => ?_
    rw [map_mul]
    by_cases h : R = Q
    · subst h; rw [Z.e_ne Q' R hne, mul_zero]
    · rw [Z.e_ne Q R h, zero_mul])
  have hτa : τ a = b := Subtype.ext hQ
  have hmap : ∀ M : Matrix (Fin n) (Fin n) S, (cT τ M).map S.subtype = cT σ (M.map S.subtype) := fun M => by
    ext i j; rfl
  have hGh : cT τ (G : Matrix (Fin n) (Fin n) S) = G :=
    Matrix.map_injective (f := (S.subtype : S → A)) S.subtype_injective ((hmap _).trans hG)
  let uM : Matrix (Fin n) (Fin n) S := a • (X : Matrix (Fin n) (Fin n) S) +
    b • (((G⁻¹ : GL (Fin n) S) : Matrix (Fin n) (Fin n) S) * cT τ ((X⁻¹ : GL (Fin n) S) : Matrix (Fin n) (Fin n) S) * G) +
    (1 - a - b) • (1 : Matrix (Fin n) (Fin n) S)
  let vM : Matrix (Fin n) (Fin n) S := a • ((X⁻¹ : GL (Fin n) S) : Matrix (Fin n) (Fin n) S) +
    b • (((G⁻¹ : GL (Fin n) S) : Matrix (Fin n) (Fin n) S) * cT τ (X : Matrix (Fin n) (Fin n) S) * G) +
    (1 - a - b) • (1 : Matrix (Fin n) (Fin n) S)
  let u : GL (Fin n) S := ⟨uM, vM,
    idem_split_inv τ a b ha hb hab _ _ _ _ (Units.mul_inv G) (Units.inv_mul G) (Units.mul_inv X),
    idem_split_inv τ a b ha hb hab _ _ _ _ (Units.mul_inv G) (Units.inv_mul G) (Units.inv_mul X)⟩
  have hcompU : ∀ R, ((bc (Z.pO R) u : GL (Fin n) (Z.O R)) : Matrix (Fin n) (Fin n) (Z.O R)) =
      Z.pO R a • (X : Matrix (Fin n) (Fin n) S).map (Z.pO R) + Z.pO R b • _ + Z.pO R (1 - a - b) • 1 :=
    fun R => map_idem3 _ _ _ _ _ _
  refine ⟨u, ?_, ?_, ?_⟩
  · show cT σ (uM.map S.subtype) * (G : Matrix (Fin n) (Fin n) S).map S.subtype * uM.map S.subtype
      = (G : Matrix (Fin n) (Fin n) S).map S.subtype
    rw [← hmap, ← Matrix.map_mul, ← Matrix.map_mul,
      idem_split_unitary τ hτ a b ha hb hab hτa _ _ _ _ (Units.mul_inv G) (Units.inv_mul X) hGh]
  · have hpa : Z.pO Q a = 1 := Subtype.ext (Z.e_self Q)
    have hpb : Z.pO Q b = 0 := Subtype.ext (Z.e_ne Q' Q hne)
    refine Units.ext ?_
    rw [hcompU, map_sub, map_sub, map_one, hpa, hpb]
    simp only [one_smul, zero_smul, add_zero, sub_self]
    exact congrArg Units.val hXQ
  · intro R h1 h2
    have hpa : Z.pO R a = 0 := Subtype.ext (Z.e_ne Q R h1)
    have hpb : Z.pO R b = 0 := Subtype.ext (Z.e_ne Q' R h2)
    refine Units.ext ?_
    rw [hcompU, map_sub, map_sub, map_one, hpa, hpb]
    simp

end GlobalTheory.LevNorm
end

section

open Module NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Forms
open scoped Matrix ComplexOrder

namespace GlobalTheory.ClassLatticeSelfDual

section General

open Formalism.UG Formalism.UG.P
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {n : Type} [Fintype n] [DecidableEq n]


omit [NumberField F] [DecidableEq n] [Fintype n] in
theorem mem_span_of_mem_latS (R : Type) [CommRing R] [Algebra F R] [Nontrivial R] (S : Subring (E ⊗[F] R))
    (L : Submodule (𝓞 E) (n → E)) (x : n → E)
    (hx : (fun i => inclE (F := F) R (x i)) ∈ latS (F := F) R S L) :
    x ∈ Submodule.span E (L : Set (n → E)) := by
  obtain ⟨φ, hφ⟩ : ∃ φ : R →ₗ[F] F, φ 1 = 1 := Module.Projective.exists_dual_eq_one F one_ne_zero
  let π : E ⊗[F] R →ₗ[E] E :=
    (TensorProduct.AlgebraTensorModule.rid F E E).toLinearMap ∘ₗ (φ.baseChange E)
  have hπ : ∀ (s : E ⊗[F] R) (a : E), π (s * inclE (F := F) R a) = π s * a := by
    intro s a
    have : s * inclE (F := F) R a = a • s := by
      rw [mul_comm, Algebra.smul_def]; rfl
    rw [this, map_smul, smul_eq_mul, mul_comm]
  have hπ1 : π 1 = 1 := by
    simp [π, Algebra.TensorProduct.one_def, hφ]
  have key : ∀ u ∈ latS (F := F) R S L, ∀ s : E ⊗[F] R,
      (fun i => π (s * u i)) ∈ Submodule.span E (L : Set (n → E)) := by
    intro u hu
    unfold latS at hu
    induction hu using Submodule.span_induction with
    | mem u hu =>
      obtain ⟨y, hy, rfl⟩ := hu
      intro s
      have : (fun i => π (s * inclE (F := F) R (y i))) = π s • y := by
        funext i; rw [hπ]; rfl
      exact this ▸ Submodule.smul_mem _ _ (Submodule.subset_span hy)
    | zero =>
      intro s
      have : (fun i => π (s * (0 : n → E ⊗[F] R) i)) = 0 := by funext i; simp
      exact this ▸ zero_mem _
    | add u u' _ _ h h' =>
      intro s
      have : (fun i => π (s * (u + u') i)) = (fun i => π (s * u i)) + fun i => π (s * u' i) := by
        funext i; simp [mul_add]
      exact this ▸ add_mem (h s) (h' s)
    | smul r u _ h =>
      intro s
      have : (fun i => π (s * (r • u) i)) = fun i => π ((s * (r : E ⊗[F] R)) * u i) := by
        funext i; rw [mul_assoc]; rfl
      exact this ▸ h _
  have h := key _ hx 1
  have e : (fun i => π (1 * inclE (F := F) R (x i))) = x := by
    funext i; rw [hπ, hπ1, one_mul]
  rwa [e] at h

theorem eq_globLat (Λ L : Submodule (𝓞 E) (n → E)) (hfin : Module.Finite (𝓞 E) Λ)
    (hspan : Submodule.span E (Λ : Set (n → E)) = ⊤) (hL : Module.Finite (𝓞 E) L)
    (g : GL n (E ⊗[F] FiniteAdeleRing (𝓞 F) F))
    (h : ∀ x : n → E ⊗[F] FiniteAdeleRing (𝓞 F) F,
      x ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F)
        (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) L ↔
      (g⁻¹).1 *ᵥ x ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F)
        (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) Λ) :
    L = CS.globLat g Λ := by
  have : Nontrivial (FiniteAdeleRing (𝓞 F) F) := by
    obtain ⟨p, hp⟩ := Ideal.exists_maximal (𝓞 F)
    let v : HeightOneSpectrum (𝓞 F) :=
      ⟨p, hp.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hp (RingOfIntegers.not_isField F)⟩
    refine ⟨0, 1, fun h => ?_⟩
    have h1 : (0 : FiniteAdeleRing (𝓞 F) F) v = (1 : FiniteAdeleRing (𝓞 F) F) v := by rw [h]
    exact (zero_ne_one : (0 : v.adicCompletion F) ≠ 1) h1
  have hG := csGlob_lattice (F := F) Λ hfin hspan g
  have hLs : Submodule.span E (L : Set (n → E)) = ⊤ := by
    rw [eq_top_iff, ← hG.span_eq_top, Submodule.span_le]
    intro x hx
    exact mem_span_of_mem_latS (F := F) _ _ L x ((h _).2 hx)
  ext x
  conv_lhs => rw [← global_lattice_one_holds F E n L hL hLs]
  refine Iff.trans ?_ (h _)
  show ((1⁻¹ : GL n (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) : Matrix n n _) *ᵥ
      (fun i => inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (x i)) ∈
      latS (F := F) (FiniteAdeleRing (𝓞 F) F)
        (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) L ↔ _
  rw [inv_one, Units.val_one, Matrix.one_mulVec]

end General

theorem classLattice_selfDual : ∀ (D : D7) (u : D.what₂.Word) (K : ClsPTied u) (c : (D.fm u).clsP), Submodule.IsLattice D.host.E (K.lat c) ∧ ∀ y, y ∈ K.lat c ↔ ∀ x ∈ K.lat c, Formalism.UG.hform (sigD D : D.host.E →+* D.host.E) (gramP D) x y ∈ (algebraMap (𝓞 D.host.E) D.host.E).range := by
  intro D u K c
  have e := eq_globLat (F := D.host.F) K.lev.Lb (K.lat c) K.lev.Lb_fin K.lev.Lb_span (K.lat_fin c) (K.y c).1 (K.y_lat c)
  have hdual : ∀ x, x ∈ K.lev.Lb ↔ ∀ y ∈ K.lev.Lb,
      Formalism.UG.hform (sigD D : D.host.E →+* D.host.E) (gramP D) y x ∈ (algebraMap (𝓞 D.host.E) D.host.E).range := by
    intro x
    refine ⟨fun hx => K.lev.Lb_int x hx, fun hx => ?_⟩
    have := K.lev.Lb_dual x hx
    rwa [Nat.cast_one, one_smul] at this
  rw [e]
  exact ⟨(Formalism.UG.P.csGlob_lattice (F := D.host.F) _ K.lev.Lb_fin K.lev.Lb_span _).toIsLattice,
    fun y => GlobalTheory.PointLattice.globLat_selfDual (sigD D) (gramP D) _ hdual K.lev.Lb_fin K.lev.Lb_span _ (K.y c).2 y⟩

end GlobalTheory.ClassLatticeSelfDual
end

section

open PowerSeries GlobalTheory.Honda Formalism.L2.Th1.CM

namespace GlobalTheory

theorem homotheticLattice : ∀ (L : PeriodPair) (c : ℂ), c ≠ 0 → ∃ L' : PeriodPair,
    (∀ z, z ∈ L'.lattice ↔ c * z ∈ L.lattice) ∧ L'.g₂ = c ^ 4 * L.g₂ ∧ L'.g₃ = c ^ 6 * L.g₃ ∧
    (∀ z, L'.weierstrassP z = c ^ 2 * L.weierstrassP (c * z) ∧
      L'.derivWeierstrassP z = c ^ 3 * L.derivWeierstrassP (c * z)) ∧
    ∀ d, HasCMBy d L → HasCMBy d L' := by
  intro L c hc
  have hc' : c⁻¹ ≠ 0 := inv_ne_zero hc
  obtain ⟨hmem, -, -, hwp, -, -, -, -, -, hg2, hg3⟩ := Formalism.L2.Th1.F.homogeneity L c⁻¹ hc'
  refine ⟨Formalism.L2.Th1.F.scalePair L c⁻¹ hc', ?_, ?_, ?_, ?_, ?_⟩
  · intro z; rw [hmem, inv_inv]
  · rw [hg2, inv_pow, inv_inv]
  · rw [hg3, inv_pow, inv_inv]
  · intro z
    constructor
    · have := hwp (c * z)
      rw [← mul_assoc, inv_mul_cancel₀ hc, one_mul, inv_pow, inv_inv] at this
      exact this
    · unfold PeriodPair.derivWeierstrassP
      rw [Formalism.L2.Th1.F.Homog.tsum_scale L c⁻¹ hc' (fun l => 2 / (z - l) ^ 3), mul_neg,
        ← tsum_mul_left]
      congr 1
      refine tsum_congr fun l => ?_
      have : z - c⁻¹ * (l : ℂ) = c⁻¹ * (c * z - l) := by field_simp
      rw [this, mul_pow, inv_pow, div_eq_mul_inv, div_eq_mul_inv, mul_inv, inv_inv]
      ring
  · intro d hd
    exact Formalism.L2.Th1.F.hasCMByScale d L c⁻¹ hc' hd

end GlobalTheory
end
