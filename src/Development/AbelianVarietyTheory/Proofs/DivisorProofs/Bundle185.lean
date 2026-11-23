module

public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.GroupTheory.Index
public import Mathlib.Order.Filter.Cofinite
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle008
public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.Algebra.Category.Ring.Constructions
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle004
import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.RingTheory.FinitePresentation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyFiniteBaseChangeFilteredColimit
public import Mathlib.Algebra.Central.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.Algebra.DualNumber
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.FieldTheory.IntermediateField.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import GroundTheory.Brauer.TensorSimple
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Mathlib.RingTheory.Kaehler.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle013
public import Mathlib.RingTheory.Smooth.StandardSmooth
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Data.Matrix.Mul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle011
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle014
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
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PiTensorProduct
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
public import Mathlib.CategoryTheory.Limits.Preserves.Basic
public import Mathlib.CategoryTheory.Limits.Types.Colimits
public import Mathlib.CategoryTheory.Limits.Types.Filtered
import Mathlib.Topology.Sheaves.Presheaf
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.CMField
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf

@[expose] public section

section

open Filter
open scoped Classical

theorem _root_.GlobalTheory.T.relIndex_inf_conj_eq_finprod_restrictedProduct : ∀ (ι G : Type) [Group G] (H : ι → Type) [∀ i, Group (H i)] (p : ∀ i, G →* H i) (K T C : Subgroup G) (KH TH CH : ∀ i, Subgroup (H i)) (g : G), (∀ y : ∀ i, H i, (∀ᶠ i in cofinite, y i ∈ KH i) → ∃ x : G, ∀ i, p i x = y i) → (∀ x : G, ∀ᶠ i in cofinite, p i x ∈ KH i) → (∀ x : G, x ∈ K ↔ ∀ i, p i x ∈ KH i) → (∀ x, x ∈ T ↔ ∀ i, p i x ∈ TH i) → (∀ x, x ∈ C ↔ x ∈ T ∧ ∀ i, p i x ∈ CH i) → (∀ i, CH i ≤ TH i) → (∀ i, TH i ⊓ (KH i).map (MulAut.conj (p i g)).toMonoidHom ≤ CH i ∧ (TH i ⊓ (KH i).map (MulAut.conj (p i g)).toMonoidHom).relIndex (CH i) ≠ 0) → (∀ᶠ i in cofinite, CH i ≤ KH i) → (T ⊓ K.map (MulAut.conj g).toMonoidHom).relIndex C = ∏ᶠ i, (TH i ⊓ (KH i).map (MulAut.conj (p i g)).toMonoidHom).relIndex (CH i) := by
  first | exact @GlobalTheory.relIndex_inf_conj_eq_finprod_of_restricted_product | exact GlobalTheory.relIndex_inf_conj_eq_finprod_of_restricted_product | (intros; apply GlobalTheory.relIndex_inf_conj_eq_finprod_of_restricted_product <;> assumption)
end

section

open CategoryTheory Limits TensorProduct

namespace GlobalTheory.TorsorColim

theorem poly_eventually_solvable :
    ∀ (J : Type) [SmallCategory J] [IsFiltered J] (F : J ⥤ CommRingCat.{0}) (c : Cocone F),
    IsColimit c → ∀ (j : J) (σ ι : Type) [Finite σ] [Finite ι] (p : ι → MvPolynomial σ (F.obj j)) (x : σ → c.pt),
    (∀ i, MvPolynomial.eval₂ (c.ι.app j).hom x (p i) = 0) →
    ∃ (k₀ : J) (f₀ : j ⟶ k₀), ∀ (k : J) (f : k₀ ⟶ k), ∃ y : σ → F.obj k,
      ∀ i, MvPolynomial.eval₂ (F.map (f₀ ≫ f)).hom y (p i) = 0 := by
  classical
  intro J _ _ F c hc j σ ι _ _ p x hx
  haveI := Fintype.ofFinite σ
  haveI := Fintype.ofFinite ι
  have hc' := isColimitOfPreserves (forget _) hc

  choose jx x' hx' using fun s : σ => Types.jointly_surjective_of_isColimit hc' (x s)
  obtain ⟨K, hK⟩ := IsFiltered.sup_objs_exists (insert j (Finset.univ.image jx))
  obtain ⟨h⟩ := hK (Finset.mem_insert_self j _)
  have hm : ∀ s, Nonempty (jx s ⟶ K) := fun s =>
    hK (Finset.mem_insert_of_mem (Finset.mem_image_of_mem jx (Finset.mem_univ s)))
  let u : σ → F.obj K := fun s => (F.map (hm s).some).hom (x' s)
  have hu : ∀ s, (c.ι.app K).hom (u s) = x s := by
    intro s
    have h2 := congr(($(c.w (hm s).some)).hom (x' s))
    simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply] at h2
    rw [h2]
    exact hx' s

  have hz : ∀ i, (c.ι.app K).hom (MvPolynomial.eval₂ (F.map h).hom u (p i)) = 0 := by
    intro i
    rw [MvPolynomial.eval₂_comp_left]
    have e1 : (c.ι.app K).hom.comp (F.map h).hom = (c.ι.app j).hom := by
      rw [← CommRingCat.hom_comp, c.w h]
    have e2 : ⇑(c.ι.app K).hom ∘ u = x := funext hu
    rw [e1, e2]; exact hx i

  have one : ∀ i, ∃ (k₀ : J) (f₀ : K ⟶ k₀), ∀ (k : J) (f : k₀ ⟶ k),
      (F.map (f₀ ≫ f)).hom (MvPolynomial.eval₂ (F.map h).hom u (p i)) = 0 := by
    intro i
    have h0 : (c.ι.app K).hom (MvPolynomial.eval₂ (F.map h).hom u (p i)) = (c.ι.app K).hom 0 := by
      rw [hz i, map_zero]
    obtain ⟨k₀, f₀, e⟩ := (Types.FilteredColimit.isColimit_eq_iff' hc' _ 0).1 (by exact h0)
    refine ⟨k₀, f₀, fun k f => ?_⟩
    have e' : (F.map f₀).hom (MvPolynomial.eval₂ (F.map h).hom u (p i)) = 0 := by simpa using e
    rw [Functor.map_comp, CommRingCat.hom_comp, RingHom.comp_apply, e', map_zero]

  have all : ∀ S : Finset ι, ∃ (k₀ : J) (f₀ : K ⟶ k₀), ∀ (k : J) (f : k₀ ⟶ k),
      ∀ i ∈ S, (F.map (f₀ ≫ f)).hom (MvPolynomial.eval₂ (F.map h).hom u (p i)) = 0 := by
    intro S
    induction S using Finset.induction_on with
    | empty => exact ⟨K, 𝟙 K, fun _ _ i hi => absurd hi (Finset.notMem_empty i)⟩
    | insert a S _ ih =>
      obtain ⟨k₀, f₀, hh⟩ := eventually_and
        (fun k (g : K ⟶ k) => (F.map g).hom (MvPolynomial.eval₂ (F.map h).hom u (p a)) = 0)
        (fun k (g : K ⟶ k) => ∀ i ∈ S, (F.map g).hom (MvPolynomial.eval₂ (F.map h).hom u (p i)) = 0)
        (one a) ih
      refine ⟨k₀, f₀, fun k f i hi => ?_⟩
      rcases Finset.mem_insert.1 hi with rfl | hi
      · exact (hh k f).1
      · exact (hh k f).2 i hi
  obtain ⟨k₀, f₀, h0⟩ := all Finset.univ
  refine ⟨k₀, h ≫ f₀, fun k f => ⟨fun s => (F.map (f₀ ≫ f)).hom (u s), fun i => ?_⟩⟩
  have := h0 k f i (Finset.mem_univ i)
  rw [MvPolynomial.eval₂_comp_left, ← CommRingCat.hom_comp, ← Functor.map_comp] at this
  rw [Category.assoc]
  exact this

end GlobalTheory.TorsorColim
end

section

open CategoryTheory Limits TensorProduct

theorem _root_.GlobalTheory.T.eventually_finite_baseChange_filtered_colimit : ∀ (J : Type) [SmallCategory J] [IsFiltered J] (F : J ⥤ CommRingCat.{0}) (c : Cocone F),
    IsColimit c → ∀ (j : J) (A : Type) [CommRing A] [Algebra (F.obj j) A]
    [Algebra.FinitePresentation (F.obj j) A],
    (letI : Algebra (F.obj j) c.pt := (c.ι.app j).hom.toAlgebra;
      Module.Finite c.pt (c.pt ⊗[F.obj j] A)) →
    ∃ (k₀ : J) (f₀ : j ⟶ k₀), ∀ (k : J) (f : k₀ ⟶ k),
      (letI : Algebra (F.obj j) (F.obj k) := (F.map (f₀ ≫ f)).hom.toAlgebra;
        Module.Finite (F.obj k) (F.obj k ⊗[F.obj j] A)) := by
  exact @GlobalTheory.FiniteColim.eventually_finite_baseChange
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

theorem _root_.GlobalTheory.T.pullbackCone_surjective_nilpotent_ker : ∀ {A B C : CommRingCat.{0}} (f : A ⟶ C) (g : B ⟶ C), Function.Surjective f.hom → IsNilpotent (RingHom.ker f.hom) → Function.Surjective g.hom → IsNilpotent (RingHom.ker g.hom) → (Function.Surjective (CommRingCat.pullbackCone f g).fst.hom ∧ IsNilpotent (RingHom.ker (CommRingCat.pullbackCone f g).fst.hom)) ∧ (Function.Surjective (CommRingCat.pullbackCone f g).snd.hom ∧ IsNilpotent (RingHom.ker (CommRingCat.pullbackCone f g).snd.hom)) ∧ (Function.Surjective ((CommRingCat.pullbackCone f g).fst ≫ f).hom ∧ IsNilpotent (RingHom.ker ((CommRingCat.pullbackCone f g).fst ≫ f).hom)) := by
  first | exact @GlobalTheory.pullbackCone_fst_snd_ring_nilpotent | exact GlobalTheory.pullbackCone_fst_snd_ring_nilpotent | (intros; apply GlobalTheory.pullbackCone_fst_snd_ring_nilpotent <;> assumption)
end

section

open NumberField Matrix
open scoped TensorProduct ComplexConjugate

namespace GlobalTheory.UPel.HT.RealRepBij

end GlobalTheory.UPel.HT.RealRepBij

namespace GlobalTheory.UPel.HT.RealRepBij

theorem span_range_eq_top {F B : Type} [Field F] [Ring B] [Algebra F B] [Algebra.IsCentral F B]
    [IsSimpleRing B] [FiniteDimensional F B] {n : ℕ} (σ : F →+* ℂ)
    (f : B →+* Matrix (Fin n) (Fin n) ℂ) (hdim : Module.finrank F B = n ^ 2)
    (hf : ∀ a, f (algebraMap F B a) = Matrix.scalar (Fin n) (σ a)) :
    Submodule.span ℂ (Set.range f) = ⊤ := by
  letI : Algebra F ℂ := σ.toAlgebra
  have hg : ∀ a, f (algebraMap F B a) = algebraMap F (Matrix (Fin n) (Fin n) ℂ) a := fun a => by
    rw [hf, Matrix.algebraMap_eq_diagonal]; rfl
  let g : B →ₐ[F] Matrix (Fin n) (Fin n) ℂ := { f with commutes' := hg }
  let L : ℂ ⊗[F] B →ₐ[ℂ] Matrix (Fin n) (Fin n) ℂ :=
    Algebra.TensorProduct.lift (Algebra.ofId ℂ _) g (fun r y => Algebra.commute_algebraMap_left r _)
  have hn : 0 < n := by
    have := Module.finrank_pos (R := F) (M := B)
    rw [hdim] at this
    exact Nat.pos_of_ne_zero fun h => by simp [h] at this
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hinj : Function.Injective L :=
    (IsSimpleRing.injective_ringHom_or_subsingleton_codomain L.toRingHom).resolve_right
      (not_subsingleton _)
  have hdim' : Module.finrank ℂ (ℂ ⊗[F] B) = Module.finrank ℂ (Matrix (Fin n) (Fin n) ℂ) := by
    rw [Module.finrank_baseChange, hdim, Module.finrank_matrix, Module.finrank_self]
    simp [sq]
  have hsurj : Function.Surjective L.toLinearMap :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim').1 hinj
  refine eq_top_iff.2 fun m _ => ?_
  clear ‹m ∈ ⊤›
  obtain ⟨x, rfl⟩ := hsurj m
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul c b =>
    have : L.toLinearMap (c ⊗ₜ b) = c • f b := by
      dsimp only [L]
      rw [AlgHom.toLinearMap_apply]
      erw [Algebra.TensorProduct.lift_tmul]
      rw [Algebra.ofId_apply, Algebra.smul_def]; rfl
    rw [this]
    exact Submodule.smul_mem _ c (Submodule.subset_span ⟨b, rfl⟩)
  | add x y hx hy => rw [map_add (f := _)]; exact Submodule.add_mem _ hx hy

end GlobalTheory.UPel.HT.RealRepBij

namespace GlobalTheory.UPel.HT.RealRepBij

variable {K F : Type} [Field K] [NumberField K] [NumberField.IsCMField K]
  [Field F] [NumberField F] [NumberField.IsCMField F]
  [Algebra K F] {p : ℕ} [Fact p.Prime]

end GlobalTheory.UPel.HT.RealRepBij
end

section


theorem _root_.GlobalTheory.T.frobeniusSemilinearMatrix_iterate_eq_zero_of_nilpotent : ∀ (p : ℕ) [Fact p.Prime] (S : Type) [CommRing S] [CharP S p] (ι : Type) [Fintype ι] [DecidableEq ι] (Q : Matrix ι ι S) (N : ℕ), (∀ j i, IsNilpotent ((fun w : ι → S => Q.mulVec fun k => frobenius S p (w k))^[N] (Pi.single j 1) i)) → ∃ K : ℕ, ∀ z : ι → S, (fun w : ι → S => Q.mulVec fun k => frobenius S p (w k))^[K] z = 0 := by
  first | exact @GlobalTheory.frobSemilinear_iterate_eq_zero | exact GlobalTheory.frobSemilinear_iterate_eq_zero | (intros; apply GlobalTheory.frobSemilinear_iterate_eq_zero <;> assumption)
end

section


theorem _root_.GlobalTheory.T.ringHom_numberField_dualNumber_snd_eq_zero : ∀ (F : IntermediateField ℚ ℂ) [FiniteDimensional ℚ F] {R : Type} [CommRing R] (φ : F →+* DualNumber R) (a : F), (φ a).snd = 0 := by
  first | exact @GlobalTheory.ringHom_dualNumber_snd_eq_zero | exact GlobalTheory.ringHom_dualNumber_snd_eq_zero | (intros; apply GlobalTheory.ringHom_dualNumber_snd_eq_zero <;> assumption)
end

section

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory MonObj MonoidalCategory
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.TorsConst

theorem sp_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) :=
  (Spec.map_comp (CommRingCat.ofHom f) (CommRingCat.ofHom g)).symm

theorem ext_of_two {B C : Type} [CommRing B] [CommRing C] [IsLocalRing B] [IsLocalRing C]
    (d e : B →+* C) [IsLocalHom d] [IsLocalHom e] (hde : ∀ x y, d x = d y → e x = e y → x = y)
    {X : Scheme.{0}} (a b : Sp B ⟶ X) (h1 : spMap d ≫ a = spMap d ≫ b) (h2 : spMap e ≫ a = spMap e ≫ b) :
    a = b := by
  obtain ⟨⟨x, f, hf⟩, rfl⟩ := (SpecToEquivOfLocalRing X (CommRingCat.of B)).symm.surjective a
  obtain ⟨⟨y, g, hg⟩, rfl⟩ := (SpecToEquivOfLocalRing X (CommRingCat.of B)).symm.surjective b
  have l1 : ∀ (k : B →+* C) [IsLocalHom k] (φ : X.presheaf.stalk x ⟶ CommRingCat.of B),
      IsLocalHom φ.hom → IsLocalHom (φ ≫ CommRingCat.ofHom k).hom := by
    intro k _ φ _
    rw [CommRingCat.hom_comp]; exact RingHom.isLocalHom_comp k φ.hom
  have l2 : ∀ (k : B →+* C) [IsLocalHom k] (φ : X.presheaf.stalk y ⟶ CommRingCat.of B),
      IsLocalHom φ.hom → IsLocalHom (φ ≫ CommRingCat.ofHom k).hom := by
    intro k _ φ _
    rw [CommRingCat.hom_comp]; exact RingHom.isLocalHom_comp k φ.hom
  have key : ∀ (k : B →+* C) [IsLocalHom k], spMap k ≫ (SpecToEquivOfLocalRing X (CommRingCat.of B)).symm ⟨x, f, hf⟩ =
      spMap k ≫ (SpecToEquivOfLocalRing X (CommRingCat.of B)).symm ⟨y, g, hg⟩ →
      (⟨x, f ≫ CommRingCat.ofHom k, l1 k f hf⟩ : Σ z : X, {φ : X.presheaf.stalk z ⟶ CommRingCat.of C // IsLocalHom φ.hom}) =
        ⟨y, g ≫ CommRingCat.ofHom k, l2 k g hg⟩ := by
    intro k _ h
    apply (SpecToEquivOfLocalRing X (CommRingCat.of C)).symm.injective
    simpa [SpecToEquivOfLocalRing] using h
  have k1 := key d h1
  have k2 := key e h2
  obtain rfl : x = y := congrArg Sigma.fst k1
  have h5 : f ≫ CommRingCat.ofHom d = g ≫ CommRingCat.ofHom d :=
    congrArg Subtype.val (eq_of_heq (Sigma.mk.inj k1).2)
  have h6 : f ≫ CommRingCat.ofHom e = g ≫ CommRingCat.ofHom e :=
    congrArg Subtype.val (eq_of_heq (Sigma.mk.inj k2).2)
  obtain rfl : f = g := by
    ext s
    exact hde _ _ (congrArg (fun k => k.hom s) h5) (congrArg (fun k => k.hom s) h6)
  rfl

variable {K : Type} [Field K]

theorem isLocalRing_tsze (M : Type) [AddCommGroup M] [Module K M] [Module Kᵐᵒᵖ M] [IsCentralScalar K M] :
    IsLocalRing (TrivSqZeroExt K M) :=
  IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun a => by
    simp only [TrivSqZeroExt.isUnit_iff_isUnit_fst, TrivSqZeroExt.fst_sub, TrivSqZeroExt.fst_one]
    exact IsLocalRing.isUnit_or_isUnit_one_sub_self _

attribute [local instance] isLocalRing_tsze

theorem isLocalHom_map {M N : Type} [AddCommGroup M] [Module K M] [Module Kᵐᵒᵖ M] [IsCentralScalar K M]
    [AddCommGroup N] [Module K N] [Module Kᵐᵒᵖ N] [IsCentralScalar K N] (l : M →ₗ[K] N) :
    IsLocalHom (TrivSqZeroExt.map l).toRingHom :=
  ⟨fun a ha => by
    rw [TrivSqZeroExt.isUnit_iff_isUnit_fst] at ha ⊢
    simpa using ha⟩

abbrev ovO (B : Type) [CommRing B] [Algebra K B] : Over (Sp K) := Over.mk (spMap (algebraMap K B))

def ovH {B C : Type} [CommRing B] [Algebra K B] [CommRing C] [Algebra K C] (φ : B →ₐ[K] C) :
    ovO (K := K) C ⟶ ovO B :=
  Over.homMk (spMap φ.toRingHom) (by
    simp only [ovO, Over.mk_hom]
    rw [sp_comp]
    congr 2
    exact φ.comp_algebraMap)

theorem ovH_left {B C : Type} [CommRing B] [Algebra K B] [CommRing C] [Algebra K C] (φ : B →ₐ[K] C) :
    (ovH φ).left = spMap φ.toRingHom := rfl

theorem ovH_comp {B C E : Type} [CommRing B] [Algebra K B] [CommRing C] [Algebra K C] [CommRing E] [Algebra K E]
    (φ : B →ₐ[K] C) (ψ : C →ₐ[K] E) : ovH (ψ.comp φ) = ovH ψ ≫ ovH φ := by
  ext1
  simp only [Over.comp_left, ovH_left, sp_comp]
  rfl

theorem ovH_id {B : Type} [CommRing B] [Algebra K B] : ovH (AlgHom.id K B) = 𝟙 (ovO B) := by
  ext1
  simp only [ovH_left, Over.id_left]
  exact Spec.map_id _

abbrev sc (t : K) : DualNumber K →ₐ[K] DualNumber K := TrivSqZeroExt.map (t • LinearMap.id)

abbrev jj (s t : K) : DualNumber K →ₐ[K] TrivSqZeroExt K (K × K) :=
  TrivSqZeroExt.map (LinearMap.prod (s • LinearMap.id) (t • LinearMap.id))

abbrev r1 : TrivSqZeroExt K (K × K) →ₐ[K] DualNumber K := TrivSqZeroExt.map (LinearMap.fst K K K)
abbrev r2 : TrivSqZeroExt K (K × K) →ₐ[K] DualNumber K := TrivSqZeroExt.map (LinearMap.snd K K K)
abbrev dd : TrivSqZeroExt K (K × K) →ₐ[K] DualNumber K := TrivSqZeroExt.map (LinearMap.fst K K K + LinearMap.snd K K K)

theorem dualNumberFirstProj_comp_twoEpsLinearComb (s t : K) : (r1 (K := K)).comp (jj s t) = sc s := by
  apply AlgHom.ext; intro x; ext <;> simp
theorem dualNumberSecondProj_comp_twoEpsLinearComb (s t : K) : (r2 (K := K)).comp (jj s t) = sc t := by
  apply AlgHom.ext; intro x; ext <;> simp
theorem dd_jj (s t : K) : (dd (K := K)).comp (jj s t) = sc (s + t) := by
  apply AlgHom.ext; intro x; ext <;> simp [add_mul]
theorem sc_sc (a b : K) : (sc a).comp (sc b) = sc (a * b) := by
  apply AlgHom.ext; intro x; ext <;> simp <;> ring
theorem sc_one : sc (1 : K) = AlgHom.id K _ := by
  apply AlgHom.ext; intro x; ext <;> simp

section Pts
variable {A : Over (Sp K)} [GrpObj A]

theorem ext2 (a b : ovO (K := K) (TrivSqZeroExt K (K × K)) ⟶ A) (h1 : ovH r1 ≫ a = ovH r1 ≫ b)
    (h2 : ovH r2 ≫ a = ovH r2 ≫ b) : a = b := by
  haveI := isLocalHom_map (K := K) (LinearMap.fst K K K)
  haveI := isLocalHom_map (K := K) (LinearMap.snd K K K)
  ext1
  refine ext_of_two (r1 (K := K)).toRingHom (r2 (K := K)).toRingHom ?_ a.left b.left
    (by simpa only [Over.comp_left, ovH_left] using congrArg CommaMorphism.left h1)
    (by simpa only [Over.comp_left, ovH_left] using congrArg CommaMorphism.left h2)
  intro x y hx hy
  have a1 := congrArg TrivSqZeroExt.fst hx
  have a2 := congrArg TrivSqZeroExt.snd hx
  have a3 := congrArg TrivSqZeroExt.snd hy
  simp at a1 a2 a3
  ext
  · exact a1
  · exact a2
  · exact a3

theorem hadd (hc : ∀ x y : ovO (K := K) (DualNumber K) ⟶ A, x * y = y * x) (x : ovO (DualNumber K) ⟶ A) (s t : K) :
    ovH (sc (s + t)) ≫ x * ovH (sc 0) ≫ x = ovH (sc s) ≫ x * ovH (sc t) ≫ x := by
  have e : ovH (jj s t) ≫ x * ovH (jj 0 0) ≫ x = ovH (jj s 0) ≫ x * ovH (jj 0 t) ≫ x := by
    apply ext2
    · simp only [MonObj.comp_mul, ← Category.assoc, ← ovH_comp, dualNumberFirstProj_comp_twoEpsLinearComb]
    · simp only [MonObj.comp_mul, ← Category.assoc, ← ovH_comp, dualNumberSecondProj_comp_twoEpsLinearComb]
      exact hc _ _
  have e2 := congrArg (fun z => ovH dd ≫ z) e
  simp only [MonObj.comp_mul, ← Category.assoc, ← ovH_comp, dd_jj, add_zero, zero_add] at e2
  exact e2

end Pts

theorem eq_zeroScale_of_pow_eq_one_of_affine_fieldAction {G : Type} [CharZero K] [Group G] (hc : ∀ x y : G, x * y = y * x) (P : K → G → G)
    (hmul : ∀ t x y, P t (x * y) = P t x * P t y) (hcomp : ∀ a b x, P a (P b x) = P (a * b) x)
    (h1 : ∀ x, P 1 x = x) (hadd : ∀ s t x, P (s + t) x * P 0 x = P s x * P t x)
    (u : G) (n : ℕ) (hn : 0 < n) (hu : u ^ n = 1) : u = P 0 u := by
  letI : CommGroup G := { ‹Group G› with mul_comm := hc }
  have hone : ∀ t, P t 1 = 1 := fun t => mul_left_cancel (a := P t 1) (by rw [_root_.mul_one, ← hmul, _root_.one_mul])
  have hpow : ∀ t x (m : ℕ), P t (x ^ m) = P t x ^ m := by
    intro t x m
    induction m with
    | zero => simp [hone]
    | succ m ih => rw [pow_succ, hmul, ih, pow_succ]
  have step : ∀ m : ℕ, P m u * P 0 u ^ m = u ^ m * P 0 u := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      have h := hadd m 1 u
      rw [h1] at h
      rw [Nat.cast_succ, pow_succ', ← _root_.mul_assoc, h, mul_right_comm, ih, pow_succ]
      exact mul_right_comm _ _ _
  have e := step n
  rw [← hpow, hu, hone, _root_.mul_one, _root_.one_mul] at e
  calc u = P 1 u := (h1 u).symm
    _ = P ((n : K)⁻¹ * n) u := by rw [inv_mul_cancel₀ (Nat.cast_ne_zero.mpr hn.ne')]
    _ = P (n : K)⁻¹ (P n u) := (hcomp _ _ _).symm
    _ = P (n : K)⁻¹ (P 0 u) := by rw [e]
    _ = P 0 u := by rw [hcomp, mul_zero]

end GlobalTheory.TorsConst

theorem GlobalTheory.TorsConst.torsion_eq_const : ∀ (K : Type) [Field K] [CharZero K] (A : Over (Sp K)) [GrpObj A] (f : Sp (DualNumber K) ⟶ Sp K), f = spMap (algebraMap K (DualNumber K)) → (∀ x y : Over.mk f ⟶ A, x * y = y * x) → ∀ (u : Over.mk f ⟶ A) (n : ℕ), 0 < n → u ^ n = 1 → u.left = spMap (algebraMap K (DualNumber K)) ≫ spMap (TrivSqZeroExt.fstHom K K K).toRingHom ≫ u.left := by
  intro K _ _ A _ f hf hc u n hn hu
  subst hf
  open GlobalTheory.TorsConst in
  have key : u = ovH (sc 0) ≫ u :=
    eq_zeroScale_of_pow_eq_one_of_affine_fieldAction hc (fun t x => ovH (sc t) ≫ x) (fun t x y => MonObj.comp_mul _ _ _)
      (fun a b x => by simp only [← Category.assoc, ← ovH_comp, sc_sc])
      (fun x => by simp only [sc_one, ovH_id, Category.id_comp]) (fun s t x => hadd hc x s t) u n hn hu
  have e : (algebraMap K (DualNumber K)).comp (TrivSqZeroExt.fstHom K K K).toRingHom = (GlobalTheory.TorsConst.sc (0 : K)).toRingHom := by
    ext x <;> simp [TrivSqZeroExt.algebraMap_eq_inl]
  conv_lhs => rw [key]
  rw [Over.comp_left, GlobalTheory.TorsConst.ovH_left, ← e, ← Category.assoc, GlobalTheory.TorsConst.sp_comp]
end
end

section


theorem _root_.GlobalTheory.T.eq_of_universal_tangent_dualNumber : ∀ (R A k : Type) [CommRing R] [CommRing A] [Algebra R A] [Field k] (n d : ℕ)
    [Module.Free A (Ω[A⁄R])] [Module.Finite A (Ω[A⁄R])], Module.finrank A (Ω[A⁄R]) = n →
    ∀ (φ : A →+* k) (ψ : A →+* TrivSqZeroExt k (Fin d → k)),
    (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom.comp ψ = φ →
    ψ.comp (algebraMap R A) = (algebraMap k (TrivSqZeroExt k (Fin d → k))).comp (φ.comp (algebraMap R A)) →
    (∀ v : A →+* DualNumber k, (TrivSqZeroExt.fstHom k k k).toRingHom.comp v = φ →
      v.comp (algebraMap R A) = (algebraMap k (DualNumber k)).comp (φ.comp (algebraMap R A)) →
      ∃! c : (Fin d → k) →ₗ[k] k, v = (TrivSqZeroExt.map c).toRingHom.comp ψ) → d = n := by
  first | exact @GlobalTheory.finrank_kaehler_eq_of_universal_tangent | exact GlobalTheory.finrank_kaehler_eq_of_universal_tangent | (intros; apply GlobalTheory.finrank_kaehler_eq_of_universal_tangent <;> assumption)
end

section


theorem _root_.GlobalTheory.T.square_zero_deformation_factors_through_linear : ∀ (R₀ B K : Type) [CommRing R₀] [CommRing B] [Algebra R₀ B] [Field K] (n : ℕ),
    Algebra.IsStandardSmoothOfRelativeDimension n R₀ B → ∀ (ι : Type) [Fintype ι], Fintype.card ι = n →
    ∀ R : B →+* TrivSqZeroExt K (ι → K), (∀ a : R₀, R (algebraMap R₀ B a) = TrivSqZeroExt.inl (R (algebraMap R₀ B a)).fst) →
    (∀ M M' : ι → K, (TrivSqZeroExt.map (Fintype.linearCombination K M)).toRingHom.comp R =
      (TrivSqZeroExt.map (Fintype.linearCombination K M')).toRingHom.comp R → M = M') →
    ∀ g : B →+* DualNumber K, (∀ b, (g b).fst = (R b).fst) →
    (∀ a : R₀, g (algebraMap R₀ B a) = TrivSqZeroExt.inl (g (algebraMap R₀ B a)).fst) →
    ∃ M : ι → K, g = (TrivSqZeroExt.map (Fintype.linearCombination K M)).toRingHom.comp R := by
  first | exact @GlobalTheory.FirstOrderPoints.exists_linearCombination_eq | exact GlobalTheory.FirstOrderPoints.exists_linearCombination_eq | (intros; apply GlobalTheory.FirstOrderPoints.exists_linearCombination_eq <;> assumption)
end

section

open Matrix

theorem _root_.GlobalTheory.T.finite_joint_eigenvalues_of_commute : ∀ (K : Type) [Field K] (n : ℕ) (ι : Type) (A : ι → Matrix (Fin n) (Fin n) K), (∀ i j, Commute (A i) (A j)) → Set.Finite {χ : ι → K | ∃ c : Fin n → K, c ≠ 0 ∧ ∀ i, A i *ᵥ c = χ i • c} := by
  first | exact @GlobalTheory.finite_joint_eigensystems | exact GlobalTheory.finite_joint_eigensystems | (intros; apply GlobalTheory.finite_joint_eigensystems <;> assumption)
end
