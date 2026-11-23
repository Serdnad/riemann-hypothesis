module

public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.Matrix.Kronecker
public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.Algebra.Module.StablyFree.Basic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle018
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle008
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle008
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle006
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DualRestrictSurjectiveOfIsTorsionFreeQuotient
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.AlgebraicGeometry.PullbackCarrier
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle001
public import Mathlib.AlgebraicGeometry.Gluing
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Monoidal.Mon
public import Mathlib.Data.Sym.Card
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.CoverGlue

theorem existsUnique_hom {X Y : Scheme.{0}} {I : Type} {Z : I → Scheme.{0}} (ψ : ∀ i, Z i ⟶ X)
    (hψ : ∀ i, IsOpenImmersion (ψ i)) (hc : ∀ x : X, ∃ i, x ∈ Set.range (ψ i)) (f : ∀ i, Z i ⟶ Y)
    (hf : ∀ i j (T : Scheme.{0}) (x : T ⟶ Z i) (y : T ⟶ Z j), x ≫ ψ i = y ≫ ψ j → x ≫ f i = y ≫ f j) :
    ∃! F : X ⟶ Y, ∀ i, ψ i ≫ F = f i := by
  let C : X.OpenCover := Scheme.Cover.mkOfCovers I Z ψ (fun x => by simpa using hc x) hψ
  refine ⟨C.glueMorphisms f fun i j => hf i j _ _ _ pullback.condition, fun i => C.ι_glueMorphisms _ _ i,
    fun F hF => C.hom_ext _ _ fun i => (hF i).trans (C.ι_glueMorphisms f _ i).symm⟩

theorem hom_ext {X Y : Scheme.{0}} {I : Type} {Z : I → Scheme.{0}} (ψ : ∀ i, Z i ⟶ X)
    (hψ : ∀ i, IsOpenImmersion (ψ i)) (hc : ∀ x : X, ∃ i, x ∈ Set.range (ψ i)) {F F' : X ⟶ Y}
    (h : ∀ i, ψ i ≫ F = ψ i ≫ F') : F = F' :=
  (existsUnique_hom ψ hψ hc (fun i => ψ i ≫ F') fun _ _ _ _ _ e => by
    rw [← Category.assoc, e, Category.assoc]).unique h fun _ => rfl

theorem exists_hom {X Y : Scheme.{0}} {I : Type} {Z : I → Scheme.{0}} (ψ : ∀ i, Z i ⟶ X)
    (hψ : ∀ i, IsOpenImmersion (ψ i)) (hc : ∀ x : X, ∃ i, x ∈ Set.range (ψ i)) (f : ∀ i, Z i ⟶ Y)
    {B : I → I → Scheme.{0}} {a : ∀ i j, B i j ⟶ Z i} {b : ∀ i j, B i j ⟶ Z j}
    (hB : ∀ i j, IsPullback (a i j) (b i j) (ψ i) (ψ j)) (hf : ∀ i j, a i j ≫ f i = b i j ≫ f j) :
    ∃ F : X ⟶ Y, ∀ i, ψ i ≫ F = f i :=
  (existsUnique_hom ψ hψ hc f fun i j _ x y e => by
    rw [← (hB i j).lift_fst x y e, Category.assoc, hf, ← Category.assoc, (hB i j).lift_snd]).exists

variable {S : Scheme.{0}} {I : Type} {U : I → S.Opens}

theorem exists_mem (hU : iSup U = ⊤) (s : S) : ∃ i, s ∈ U i :=
  TopologicalSpace.Opens.mem_iSup.1 (show s ∈ iSup U by rw [hU]; trivial)

theorem isOpenImmersion {X Z : Scheme.{0}} {V : S.Opens} {p : X ⟶ S} {q : Z ⟶ V.toScheme} {ψ : Z ⟶ X}
    (h : IsPullback ψ q p V.ι) : IsOpenImmersion ψ :=
  MorphismProperty.of_isPullback (P := @IsOpenImmersion) h.flip inferInstance

theorem mem_range {X Z : Scheme.{0}} {V : S.Opens} {p : X ⟶ S} {q : Z ⟶ V.toScheme} {ψ : Z ⟶ X}
    (h : IsPullback ψ q p V.ι) (x : X) : x ∈ Set.range ψ ↔ p x ∈ V := by
  constructor
  · rintro ⟨z, rfl⟩
    rw [← Scheme.Hom.comp_apply, h.w, Scheme.Hom.comp_apply]
    exact (q z).2
  · intro hx
    obtain ⟨z, hz, -⟩ := Scheme.exists_preimage_of_isPullback h x ⟨p x, hx⟩ rfl
    exact ⟨z, hz⟩

theorem covers (hU : iSup U = ⊤) {X : Scheme.{0}} {Z : I → Scheme.{0}} {p : X ⟶ S} {q : ∀ i, Z i ⟶ (U i).toScheme}
    {ψ : ∀ i, Z i ⟶ X} (h : ∀ i, IsPullback (ψ i) (q i) p (U i).ι) (x : X) : ∃ i, x ∈ Set.range (ψ i) :=
  (exists_mem hU (p x)).imp fun i hi => (mem_range (h i) x).2 hi

theorem over_ext (hU : iSup U = ⊤) {T A : Over S} {f g : T ⟶ A}
    (h : ∀ i (T' : Over (U i).toScheme) (r : Over.mk (T'.hom ≫ (U i).ι) ⟶ T), r ≫ f = r ≫ g) : f = g := by
  ext1
  refine hom_ext (fun i => (T.hom ⁻¹ᵁ U i).ι) (fun _ => inferInstance)
    (covers hU fun i => (isPullback_morphismRestrict T.hom (U i)).flip) fun i => ?_
  exact congrArg (fun z => z.left) (h i (Over.mk (T.hom ∣_ U i))
    (Over.homMk (T.hom ⁻¹ᵁ U i).ι (morphismRestrict_ι _ _).symm))

theorem exists_lift {S' : Scheme.{0}} {f : S' ⟶ S} {A : Over S} {G : Over S'} {ψ : G.left ⟶ A.left}
    (h : IsPullback ψ G.hom A.hom f) {T : Over S'} (x₀ : Over.mk (T.hom ≫ f) ⟶ A) :
    ∃ x : T ⟶ G, x₀.left = x.left ≫ ψ :=
  ⟨Over.homMk (h.lift x₀.left T.hom (Over.w x₀)) (h.lift_snd _ _ _), (h.lift_fst _ _ _).symm⟩

theorem lift_ext {S' : Scheme.{0}} {f : S' ⟶ S} {A : Over S} {G : Over S'} {ψ : G.left ⟶ A.left}
    (h : IsPullback ψ G.hom A.hom f) {T : Over S'} {x y : T ⟶ G} (e : x.left ≫ ψ = y.left ≫ ψ) : x = y :=
  Over.OverMorphism.ext (h.hom_ext e ((Over.w x).trans (Over.w y).symm))

end GlobalTheory.CoverGlue
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.ZM.SymmCommutant



end GlobalTheory.ZM.SymmCommutant

namespace GlobalTheory.ZM

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj TensorProduct in
private lemma entry_eq_sum_of_mul_eq_mul_kronecker (K : Type) [Field K] (h : ℕ)
    (Ei Em : Matrix (Fin 8) (Fin 8) ℤ) (Θ : Matrix (Fin 8 × Fin h) (Fin 8 × Fin h) K)
    (hΘ : ∀ u v : Fin 8, Matrix.kronecker ((Matrix.single u v (1 : ℤ)).map (Int.cast : ℤ → K))
      (1 : Matrix (Fin h) (Fin h) K) * Θ = Θ * (Matrix.kronecker ((Ei * (Matrix.single u v
      (1 : ℤ)).transpose * Em).map (Int.cast : ℤ → K)) (1 : Matrix (Fin h) (Fin h) K)).transpose)
    (v c : Fin 8) (i j : Fin h) :
    Θ (v, i) (c, j) = (Ei c v : K) * ∑ d, Θ (0, i) (d, j) * (Em 0 d : K) := by
  have hX : ∀ u v : Fin 8, (Ei * (Matrix.single u v (1 : ℤ)).transpose * Em).map
      (Int.cast : ℤ → K) = Matrix.of fun c d => (Ei c v : K) * (Em u d : K) := by
    intro u v; ext c d
    simp [Matrix.mul_apply, Matrix.single_apply, Matrix.transpose_apply, Finset.sum_ite_eq',
      Finset.sum_ite_eq, ite_and]
  have hA : ∀ u v : Fin 8, (Matrix.single u v (1 : ℤ)).map (Int.cast : ℤ → K) =
      Matrix.single u v (1 : K) := by
    intro u v; ext a b
    simp only [Matrix.map_apply, Matrix.single_apply]
    split_ifs <;> simp
  have e := congrFun (congrFun (hΘ 0 v) (0, i)) (c, j)
  rw [hA, hX] at e
  simp only [Matrix.mul_apply, Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.transpose_apply,
    Matrix.of_apply, Fintype.sum_prod_type, Matrix.single_apply, Matrix.one_apply] at e
  simpa [Finset.mul_sum, _root_.mul_comm, _root_.mul_left_comm, _root_.mul_assoc] using e


open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj TensorProduct in
theorem _root_.GlobalTheory.ZM.finrank_symm_commutant_le : ∀ (K : Type) [Field K] (h : ℕ) (Em Ei : Matrix (Fin 8) (Fin 8) ℤ) (V : Submodule K (Matrix (Fin 8 × Fin h) (Fin 8 × Fin h) K)), Em.IsSymm → Ei * Em = 1 → (∀ Θ ∈ V, Θ.IsSymm ∧ ∀ u v : Fin 8, Matrix.kronecker ((Matrix.single u v (1 : ℤ)).map (Int.cast : ℤ → K)) (1 : Matrix (Fin h) (Fin h) K) * Θ = Θ * (Matrix.kronecker ((Ei * (Matrix.single u v (1 : ℤ)).transpose * Em).map (Int.cast : ℤ → K)) (1 : Matrix (Fin h) (Fin h) K)).transpose) → Module.finrank K V ≤ h * (h + 1) / 2 := by
  intro K _ h Em Ei V hEm hEiEm hV
  let B : Matrix (Fin 8 × Fin h) (Fin 8 × Fin h) K → Fin h → Fin h → K :=
    fun Θ i j => ∑ d, Θ (0, i) (d, j) * (Em 0 d : K)
  have key : ∀ Θ ∈ V, ∀ v c i j, Θ (v, i) (c, j) = (Ei c v : K) * B Θ i j :=
    fun Θ hΘ v c i j => entry_eq_sum_of_mul_eq_mul_kronecker K h Ei Em Θ (hV Θ hΘ).2 v c i j
  have hsum : ∑ d, (Ei 0 d : K) * (Em 0 d : K) = 1 := by
    have e := congrFun (congrFun hEiEm 0) 0
    simp only [Matrix.mul_apply, Matrix.one_apply_eq] at e
    have e' : ∑ d, Ei 0 d * Em 0 d = 1 := by
      rw [← e]; exact Finset.sum_congr rfl fun d _ => by rw [hEm.apply 0 d]
    have e'' := congrArg (Int.cast : ℤ → K) e'
    push_cast at e''
    exact e''
  have symmB : ∀ Θ ∈ V, ∀ i j, B Θ i j = B Θ j i := by
    intro Θ hΘ i j
    calc B Θ i j = ∑ d, (Ei 0 d : K) * B Θ j i * (Em 0 d : K) :=
          Finset.sum_congr rfl fun d _ => by
            rw [← key Θ hΘ d 0 j i, (hV Θ hΘ).1.apply (0, i) (d, j)]
      _ = B Θ j i * ∑ d, (Ei 0 d : K) * (Em 0 d : K) := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun d _ => by ring
      _ = B Θ j i := by rw [hsum, _root_.mul_one]
  let L : V →ₗ[K] (Sym2 (Fin h) → K) :=
    { toFun := fun Θ s => B Θ (Quot.out s).1 (Quot.out s).2
      map_add' := by
        intro x y; funext s
        simp [B, Finset.sum_add_distrib, add_mul]
      map_smul' := by
        intro r x; funext s
        simp [B, Finset.mul_sum, _root_.mul_assoc] }
  have inj : Function.Injective L := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro Θ hΘ0
    have hB : ∀ i j, B Θ i j = 0 := by
      intro i j
      have hs := congrFun hΘ0 s(i, j)
      have hout : s((Quot.out s(i, j)).1, (Quot.out s(i, j)).2) = s(i, j) := Quot.out_eq _
      rcases Sym2.eq_iff.1 hout with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · have : B Θ (Quot.out s(i, j)).1 (Quot.out s(i, j)).2 = 0 := hs
        rwa [h1, h2] at this
      · have : B Θ (Quot.out s(i, j)).1 (Quot.out s(i, j)).2 = 0 := hs
        rw [h1, h2] at this
        rwa [symmB Θ Θ.2] at this
    apply Subtype.ext
    ext ⟨v, i⟩ ⟨c, j⟩
    rw [key Θ Θ.2, hB]
    simp
  calc Module.finrank K V ≤ Module.finrank K (Sym2 (Fin h) → K) :=
        LinearMap.finrank_le_finrank_of_injective inj
    _ = h * (h + 1) / 2 := by
        rw [Module.finrank_fintype_fun_eq_card, Sym2.card, Fintype.card_fin, Nat.choose_two_right,
          Nat.add_sub_cancel, mul_comm]

end GlobalTheory.ZM
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS

namespace GlobalTheory.KS

theorem exists_dual_family_mod_subspace (K V : Type) [Field K] [AddCommGroup V] [Module K V]
    (B : Submodule K V) (g : ℕ) (φ : Fin g → V)
    (h : ∀ c : Fin g → K, ∑ a, c a • φ a ∈ B → c = 0) :
    ∃ β : Fin g → Module.Dual K V, (∀ b, B ≤ LinearMap.ker (β b)) ∧
      ∀ b a, β b (φ a) = if a = b then 1 else 0 := by
  classical

  have hli : LinearIndependent K (fun a => B.mkQ (φ a)) := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    have h0 : B.mkQ (∑ a, c a • φ a) = 0 := by

      simpa [map_sum, map_smul] using hc
    have hc0 := h c ((Submodule.Quotient.mk_eq_zero B).mp h0)
    intro i
    simp [hc0]

  let e := Module.Basis.span hli
  choose ext hext using fun b => LinearMap.exists_extend (e.coord b)
  refine ⟨fun b => (ext b).comp B.mkQ, fun b x hx => ?_, fun b a => ?_⟩
  · simp [LinearMap.mem_ker, (Submodule.Quotient.mk_eq_zero B).mpr hx]
  · have hmem : B.mkQ (φ a) ∈ Submodule.span K (Set.range fun a => B.mkQ (φ a)) :=
      Submodule.subset_span ⟨a, rfl⟩
    have he : (⟨B.mkQ (φ a), hmem⟩ : Submodule.span K (Set.range fun a => B.mkQ (φ a))) = e a :=
      (Module.Basis.span_apply hli a).symm
    have hb := LinearMap.congr_fun (hext b) ⟨B.mkQ (φ a), hmem⟩
    simp only [LinearMap.comp_apply, Submodule.subtype_apply] at hb
    rw [LinearMap.comp_apply, hb, he, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]

theorem exists_symm_matrix_mod_subspace :
    ∀ (K V : Type) [Field K] [AddCommGroup V] [Module K V] (B : Submodule K V) (g : ℕ) (θ φ : Fin g → V), (∀ c : Fin g → K, ∑ a, c a • φ a ∈ B → c = 0) → (∀ α β : Module.Dual K V, B ≤ LinearMap.ker α → B ≤ LinearMap.ker β → ∑ a, α (θ a) * β (φ a) = ∑ a, α (φ a) * β (θ a)) → ∃ Θ : Matrix (Fin g) (Fin g) K, Θ.IsSymm ∧ ∀ b, θ b - ∑ a, Θ b a • φ a ∈ B := by
  intro K V _ _ _ B g θ φ hind hsym
  classical
  obtain ⟨β, hβB, hβφ⟩ := exists_dual_family_mod_subspace K V B g φ hind

  have key : ∀ α : Module.Dual K V, B ≤ LinearMap.ker α →
      ∀ b, α (θ b) = ∑ a, α (φ a) * β b (θ a) := by
    intro α hα b
    rw [← hsym α (β b) hα (hβB b)]
    simp [hβφ]
  refine ⟨Matrix.of fun b a => β b (θ a), Matrix.IsSymm.ext fun i j => ?_, fun b => ?_⟩
  · simp only [Matrix.of_apply]
    rw [key (β i) (hβB i) j]
    simp [hβφ]
  · simp only [Matrix.of_apply]
    by_contra hx
    have hq : B.mkQ (θ b - ∑ a, β b (θ a) • φ a) ≠ 0 :=
      fun h0 => hx ((Submodule.Quotient.mk_eq_zero B).mp h0)
    obtain ⟨f, hf⟩ : ∃ f : Module.Dual K (V ⧸ B), f (B.mkQ (θ b - ∑ a, β b (θ a) • φ a)) ≠ 0 := by
      by_contra hall
      push_neg at hall
      exact hq ((Module.forall_dual_apply_eq_zero_iff K _).mp hall)
    apply hf
    have hα : B ≤ LinearMap.ker (f.comp B.mkQ) := fun x hx =>
      by simp [LinearMap.mem_ker, (Submodule.Quotient.mk_eq_zero B).mpr hx]
    have hk := key (f.comp B.mkQ) hα b
    simp only [LinearMap.comp_apply] at hk

    simp only [map_sub, map_sum, map_smul, smul_eq_mul, hk]
    simp [mul_comm]

end GlobalTheory.KS
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise

namespace GlobalTheory

theorem comp_eq_of_extending_section {X U W G T : Scheme.{0}} [IsReduced X] (j : U ⟶ X)
    [IsDominant j] (g : G ⟶ X) [IsSeparated g] (a : W ⟶ G) [IsOpenImmersion (a ≫ g)]
    (s : U ⟶ G) (hs : pullback.fst (a ≫ g) j ≫ a = pullback.snd (a ≫ g) j ≫ s)
    (r : X ⟶ X) (r₀ : U ⟶ U) (φ : G ⟶ G) (hr : r₀ ≫ j = j ≫ r) (hφ : φ ≫ g = g ≫ r)
    (hsφ : s ≫ φ = r₀ ≫ s) (w : T ⟶ W) (hw : w ≫ (a ≫ g) ≫ r = w ≫ a ≫ g) :
    w ≫ a ≫ φ = w ≫ a := by
  have key : ∀ {V : Scheme.{0}} (v : V ⟶ W) (u : V ⟶ U), v ≫ a ≫ g = u ≫ j → v ≫ a = u ≫ s := by
    intro V v u h
    have := congrArg (pullback.lift v u h ≫ ·) hs
    simpa only [pullback.lift_fst_assoc, pullback.lift_snd_assoc] using this
  let f₁ := pullback.fst (a ≫ g) ((a ≫ g) ≫ r)
  let f₂ := pullback.snd (a ≫ g) ((a ≫ g) ≫ r)
  have hc : f₁ ≫ a ≫ g = f₂ ≫ (a ≫ g) ≫ r := pullback.condition
  let t := f₂ ≫ a ≫ g
  have : IsOpenImmersion t := inferInstance
  have : IsReduced (pullback (a ≫ g) ((a ≫ g) ≫ r)) := isReduced_of_isOpenImmersion t
  have := isDominant_pullback_fst_of_isOpenMap j t t.isOpenEmbedding.isOpenMap
  have hd : pullback.fst t j ≫ f₂ ≫ a ≫ g = pullback.snd t j ≫ j := pullback.condition
  have he : f₂ ≫ a ≫ φ = f₁ ≫ a := by
    refine ext_of_isDominant_of_isSeparated g ?_ (pullback.fst t j) ?_
    · simp only [Category.assoc, hφ, hc]
    · have h₁ := key (pullback.fst t j ≫ f₂) (pullback.snd t j) ((Category.assoc _ _ _).trans hd)
      have h₂ := key (pullback.fst t j ≫ f₁) (pullback.snd t j ≫ r₀) (by
        simp only [Category.assoc, hc, hr, reassoc_of% hd])
      simp only [Category.assoc] at h₁ h₂
      rw [h₂, reassoc_of% h₁, hsφ]
  have := congrArg (pullback.lift w w hw.symm ≫ ·) he
  simpa only [f₁, f₂, pullback.lift_fst_assoc, pullback.lift_snd_assoc] using this

theorem torsion_point_fixed_of_generic_sections_fixed : ∀ (X U : Scheme.{0}) [IsLocallyNoetherian X] (j : U ⟶ X), ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X → IsPreimmersion j → Flat j → IsDominant j → QuasiCompact j → ∀ (G : Over X) [GrpObj G] (n : ℕ) (I : Type) [Finite I] (σ : I → (Over.mk j ⟶ G)) (r : X ⟶ X) (r₀ : U ⟶ U) (φ : G.left ⟶ G.left), IsSemiAbelian G → IsUnit (n : Γ(X, ⊤)) → (∀ i, σ i ^ n = 1) → (∀ (k : Type) [Field k] [IsAlgClosed k] (u : Sp k ⟶ U) (y : Over.mk (u ≫ j) ⟶ G), y ^ n = 1 → ∃ i, y.left = u ≫ (σ i).left) → r₀ ≫ j = j ≫ r → IsIso r → IsGrpPullback G G r φ → (∀ i, (σ i).left ≫ φ = r₀ ≫ (σ i).left) → ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ X) (y : Over.mk x ⟶ G), x ≫ r = x → y ^ n = 1 → y.left ≫ φ = y.left := by
  intro X U _ j hN hj₁ hj₂ hj₃ hj₄ G _ n I _ σ r r₀ φ hG hn hσ hgeo hr _ hφ hσφ k _ _ x y hx hy
  have := hG.comm
  have := hG.smooth
  have := hG.separated
  have := IsNormalScheme.of_pred hN
  have hex : ∀ {T : Over X} (z : T ⟶ G), z ^ n = 1 →
      ∃ z' : T ⟶ torsion G n, z' ≫ torsion.ι G n = z := fun z hz =>
    ⟨pullback.lift z (toUnit _) (by rw [GrpTangent.comp_mulN, hz, Hom.one_def]),
      pullback.lift_fst _ _ _⟩
  have hι : torsion.ι G n ^ n = 1 := by
    rw [← GrpTangent.comp_mulN, Hom.one_def]
    exact pullback.condition.trans (congrArg (· ≫ _) (toUnit_unique _ _))
  have hcl : IsClosedImmersion η[G].left := by
    have : IsClosedImmersion (η[G].left ≫ G.hom) := by
      rw [Over.w]; exact inferInstanceAs (IsClosedImmersion (𝟙 X))
    exact IsClosedImmersion.of_comp _ G.hom
  have : IsClosedImmersion (torsion.ι G n).left :=
    MorphismProperty.of_isPullback (P := @IsClosedImmersion)
      (GrpTangent.isPullback_torsion G n).flip hcl
  have hsep : IsSeparated (torsion G n).hom := by
    rw [← Over.w (torsion.ι G n)]; infer_instance
  choose τ hτ using fun i => hex (σ i) (hσ i)
  have hτ' : ∀ i, (τ i).left ≫ (torsion.ι G n).left = (σ i).left := fun i =>
    congrArg Over.Hom.left (hτ i)
  obtain ⟨y', rfl⟩ := hex y hy
  obtain ⟨i, W, hyW, hW, he⟩ := exists_opens_isOpenImmersion_extending_section X U j hN hj₁ hj₂
    hj₃ hj₄ _ (torsion G n).hom I (fun i => (τ i).left) (GrpTangent.etale_torsion G hn) hsep
    (fun i => Over.w (τ i)) (fun k _ _ u z hz => by
      obtain ⟨i, hi⟩ := hgeo k u (Over.homMk z hz ≫ torsion.ι G n)
        (by rw [← comp_pow, hι, comp_one])
      refine ⟨i, ?_⟩
      rw [← cancel_mono (torsion.ι G n).left, Category.assoc, hτ']
      exact hi) (y'.left (IsLocalRing.closedPoint k))
  have hrange : Set.range y'.left ⊆ Set.range W.ι := by
    rintro _ ⟨z, rfl⟩
    rw [Scheme.Opens.range_ι, Subsingleton.elim (α := PrimeSpectrum k) z (IsLocalRing.closedPoint k)]
    exact hyW
  have hw := IsOpenImmersion.lift_fac W.ι y'.left hrange
  have hq : (W.ι ≫ (torsion.ι G n).left) ≫ G.hom = W.ι ≫ (torsion G n).hom := by
    rw [Category.assoc, Over.w]
  have : IsOpenImmersion ((W.ι ≫ (torsion.ι G n).left) ≫ G.hom) := hq ▸ hW
  have hyx : y'.left ≫ (torsion G n).hom = x := Over.w y'
  have := comp_eq_of_extending_section j G.hom (W.ι ≫ (torsion.ι G n).left) (σ i).left (by
      have h := congrArg (pullback.lift (pullback.fst ((W.ι ≫ (torsion.ι G n).left) ≫ G.hom) j)
        (pullback.snd _ j) (by rw [← hq]; exact pullback.condition) ≫ · ≫ (torsion.ι G n).left) he
      simpa only [Category.assoc, pullback.lift_fst_assoc, pullback.lift_snd_assoc, hτ'] using h)
    r r₀ φ hr hφ.1.w (hσφ i) (IsOpenImmersion.lift W.ι y'.left hrange)
    (by rw [hq, Category.assoc, reassoc_of% hw, reassoc_of% hw, reassoc_of% hyx, hyx, hx])
  simpa only [Category.assoc, reassoc_of% hw, Over.comp_left] using this

end GlobalTheory
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory

theorem hermForm_self_im_eq_zero {g : ℕ} {Hm : Matrix (Fin g) (Fin g) ℂ} (h : Hm.IsHermitian)
    (z : Fin g → ℂ) : (hermForm Hm z z).im = 0 := by
  rw [← Complex.conj_eq_iff_im]

  simp only [hermForm, dotProduct, Matrix.mulVec, Finset.mul_sum, map_sum, map_mul,
  Pi.star_apply, Complex.star_def, Complex.conj_conj]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  rw [← h.apply j k, Complex.star_def]
  ring

theorem free_finite_finrank_of_discrete_span {La : Type} [AddCommGroup La] {g : ℕ}
    (Q : La →+ (Fin g → ℂ)) (hinj : Function.Injective Q) (hd : DiscreteTopology Q.range)
    (hsp : Submodule.span ℝ (Set.range Q) = ⊤) :
    Module.Free ℤ La ∧ Module.Finite ℤ La ∧ Module.finrank ℤ La = 2 * g := by
  set L : Submodule ℤ (Fin g → ℂ) := LinearMap.range Q.toIntLinearMap with hL
  haveI : DiscreteTopology L := hd
  haveI : IsZLattice ℝ L := ⟨by
    rw [hL, LinearMap.coe_range]
    exact hsp⟩
  let e : La ≃ₗ[ℤ] L := LinearEquiv.ofInjective Q.toIntLinearMap hinj
  haveI : Module.Free ℤ L := ZLattice.module_free ℝ L
  haveI : Module.Finite ℤ L := ZLattice.module_finite ℝ L
  refine ⟨Module.Free.of_equiv e.symm, Module.Finite.equiv e.symm, ?_⟩
  rw [e.finrank_eq, ZLattice.rank ℝ L, Module.finrank_pi_fintype]
  simp [Complex.finrank_real_complex, mul_comm]

theorem unimodular_symplectic_coordinates_and_lattice_rank :
    (∀ (La : Type) [AddCommGroup La] [Module.Free ℤ La] [Module.Finite ℤ La] (EF : LinearMap.BilinForm ℤ La) (g : ℕ), Function.Bijective EF → (∀ x, EF x x = 0) → Module.finrank ℤ La = 2 * g → ∃ bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] La, ∀ a b, EF (bas a) (bas b) = omegaStd a b) ∧ ∀ (La : Type) [AddCommGroup La] (EF : LinearMap.BilinForm ℤ La) (g : ℕ) (Q : La →+ (Fin g → ℂ)) (Hm : Matrix (Fin g) (Fin g) ℂ), (Function.Injective Q ∧ DiscreteTopology (Q).range ∧ Submodule.span ℝ (Set.range Q) = ⊤ ∧ (Hm).IsHermitian ∧ (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) ∧ ∀ x y, (hermForm Hm (Q x) (Q y)).im = EF x y) → Module.Free ℤ La ∧ Module.Finite ℤ La ∧ Module.finrank ℤ La = 2 * g ∧ ∀ x, EF x x = 0 := by
  refine ⟨fun La _ _ _ EF g hbij halt hrk => ?_,
    fun La _ EF g Q Hm ⟨hinj, hd, hsp, hH, _, hIm⟩ => ?_⟩
  · obtain ⟨b, hb⟩ := exists_isSymplecticBasis_of_finrank (B := EF) halt hbij hrk
    have hf : IsSymplecticFamily EF (fun i => b (Sum.inl i)) (fun i => b (Sum.inr i))
        (fun _ => 1) := hb
    classical
    refine ⟨b.equivFun.symm, fun x y => ?_⟩

    simp only [Module.Basis.equivFun_symm_apply, Fintype.sum_sum_type, map_add (f := _), LinearMap.add_apply,
    map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply, smul_eq_mul]
    simp only [hf.left_left, hf.right_right, hf.left_right, hf.right_left halt, mul_zero,
      Finset.sum_const_zero, add_zero, zero_add, mul_ite, _root_.mul_one, mul_neg,
      Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.sum_neg_distrib, omegaStd]
    rw [neg_add_eq_sub, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  · obtain ⟨h1, h2, h3⟩ := free_finite_finrank_of_discrete_span Q hinj hd hsp
    exact ⟨h1, h2, h3, fun x => by
      have e : ((EF x x : ℤ) : ℝ) = 0 := by rw [← hIm x x]; exact hermForm_self_im_eq_zero hH _
      exact_mod_cast e⟩

end GlobalTheory
end
