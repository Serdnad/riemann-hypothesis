module

public import Development.AbelianVarietyTheory.Definitions.Divisors.GalMapMul
public import Development.AbelianVarietyTheory.BlockTheory.CMModuli.ProjectiveSpaceOverSpec
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.Definitions.Divisors.KerIdealCompOfSurjective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle090
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle092
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle091
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle128
public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle002
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct

namespace GlobalTheory.EtC

abbrev AbCx : Type 2 := CochainComplex AddCommGrpCat.{1} ℤ

def SurjH {C D : AbCx} (ψ : C ⟶ D) : Prop :=
  ∀ (n : ℤ) (z : D.X n), D.d n (n + 1) z = 0 →
    ∃ (c : C.X n) (y : D.X (n - 1)), C.d n (n + 1) c = 0 ∧ ψ.f n c = z + D.d (n - 1) n y

def InjH {C D : AbCx} (ψ : C ⟶ D) : Prop :=
  ∀ (n : ℤ) (c : C.X n), C.d n (n + 1) c = 0 → (∃ y : D.X (n - 1), ψ.f n c = D.d (n - 1) n y) →
    ∃ b : C.X (n - 1), C.d (n - 1) n b = c

section Abstract
variable {T : Type 1} [Category.{0} T]

def WExact (M : T ⥤ AddCommGrpCat.{1}) {U : T} {X : CosimplicialObject T} (a : (CosimplicialObject.const T).obj U ⟶ X) : Prop :=
  Function.Injective (M.map (a.app ⦋0⦌)) ∧
  (∀ y : M.obj (X.obj ⦋0⦌), M.map (X.δ (n := 0) 0) y = M.map (X.δ (n := 0) 1) y → ∃ x : M.obj U, M.map (a.app ⦋0⦌) x = y) ∧
  ∀ n : ℕ, ((AlgebraicTopology.alternatingCofaceMapComplex AddCommGrpCat.{1}).obj (X ⋙ M)).ExactAt (n + 1)

abbrev term (C : T ⥤ AbCx) (n : ℤ) : T ⥤ AddCommGrpCat.{1} := C ⋙ HomologicalComplex.eval _ _ n

def LocExact (Cov : MorphismProperty T) (C : T ⥤ AbCx) : Prop :=
  ∀ (n : ℤ) (U : T) (z : (C.obj U).X n), (C.obj U).d n (n + 1) z = 0 →
    ∃ (V : T) (g : U ⟶ V), Cov g ∧ ∃ y : (C.obj V).X (n - 1), (C.obj V).d (n - 1) n y = (C.map g).f n z

def LocSurj (Cov : MorphismProperty T) {C D : T ⥤ AbCx} (φ : C ⟶ D) : Prop :=
  ∀ (n : ℤ) (U : T) (z : (D.obj U).X n), (D.obj U).d n (n + 1) z = 0 →
    ∃ (V : T) (g : U ⟶ V), Cov g ∧ ∃ (c : (C.obj V).X n) (y : (D.obj V).X (n - 1)), (C.obj V).d n (n + 1) c = 0 ∧
      (φ.app V).f n c = (D.map g).f n z + (D.obj V).d (n - 1) n y

def LocInj (Cov : MorphismProperty T) {C D : T ⥤ AbCx} (φ : C ⟶ D) : Prop :=
  ∀ (n : ℤ) (U : T) (c : (C.obj U).X n), (C.obj U).d n (n + 1) c = 0 →
    (∃ y : (D.obj U).X (n - 1), (φ.app U).f n c = (D.obj U).d (n - 1) n y) →
    ∃ (V : T) (g : U ⟶ V), Cov g ∧ ∃ b : (C.obj V).X (n - 1), (C.obj V).d (n - 1) n b = (C.map g).f n c

def Refines (Cov : MorphismProperty T)
    (Q : ∀ (U : T) (X : CosimplicialObject T), ((CosimplicialObject.const T).obj U ⟶ X) → Prop) : Prop :=
  ∀ (U V : T) (g : U ⟶ V), Cov g → ∃ (X : CosimplicialObject T) (a : (CosimplicialObject.const T).obj U ⟶ X) (h : V ⟶ X.obj ⦋0⦌),
    g ≫ h = a.app ⦋0⦌ ∧ Q U X a

def lev (Ψ : T ⥤ PShᵒᵖ) {U : T} {X : CosimplicialObject T} (a : (CosimplicialObject.const T).obj U ⟶ X) :
    ((X ⋙ Ψ).leftOp : Spc) ⟶ disc.obj (Ψ.obj U).unop where
  app n := (Ψ.map (a.app n.unop)).unop
  naturality m n f := by
    have h : a.app n.unop ≫ X.map f.unop = a.app m.unop := (a.naturality f.unop).symm.trans (Category.id_comp _)
    change (Ψ.map (a.app n.unop) ≫ Ψ.map (X.map f.unop)).unop = (Ψ.map (a.app m.unop)).unop ≫ 𝟙 _
    rw [← Ψ.map_comp, h, Category.comp_id]

def coAug [HasFiniteWidePushouts T] {U V : T} (g : U ⟶ V) : (CosimplicialObject.const T).obj U ⟶ (Arrow.mk g).cechConerve :=
  (Arrow.mk g).augmentedCechConerve.hom

end Abstract

variable (R : Type) [CommRing R]

def HCK (I : Cx R) : (Cx R)ᵒᵖ ⥤ AbCx where
  obj K := HomComplex K.unop I
  map f :=
    { f := fun n => AddCommGrpCat.ofHom (AddMonoidHom.mk' (fun β : Cochain _ I n => (Cochain.ofHom f.unop).comp β (zero_add n))
        (fun _ _ => Cochain.comp_add _ _ _ _))
      comm' := fun i j _ => by
        ext β
        exact δ_ofHom_comp f.unop β j }
  map_id K := by
    ext n β
    exact Cochain.id_comp β
  map_comp f g := by
    ext n β
    change (Cochain.ofHom (g.unop ≫ f.unop)).comp β (zero_add n) =
      (Cochain.ofHom g.unop).comp ((Cochain.ofHom f.unop).comp β (zero_add n)) (zero_add n)
    rw [Cochain.ofHom_comp]
    exact Cochain.comp_assoc_of_first_is_zero_cochain _ _ _ (zero_add n)

def HC (F : Shv R) : Spcᵒᵖ ⥤ AbCx := (chains R).op ⋙ HCK R (res R F)

def Hyp {T : Type 1} [Category.{0} T] (Φ : T ⥤ Spcᵒᵖ) {U : T} {X : CosimplicialObject T}
    (a : (CosimplicialObject.const T).obj U ⟶ X) : Prop :=
  ∀ k : SimplexCategoryᵒᵖ, QuasiIso ((chains R).map (lev (Φ ⋙ ((evaluation _ PSh).obj k).op) a))


variable {R} in
def onRings (F : Shv R) : CommRingCat.{0} ⥤ ModuleCat.{1} (ULift.{1} R) := Scheme.Spec.rightOp ⋙ F.obj


variable {R} in
def Finitary (F : Shv R) : Prop := PreservesFilteredColimitsOfSize.{0, 0} (onRings F)


variable {R} in
abbrev Sec.pull {F : Shv R} {U V : Scheme.{0}} (j : V ⟶ U) (x : Sec F U) : Sec F V := (F.obj.map j.op).hom x

def ContCone (F : Shv R) {I : Type} [SmallCategory I] [IsCofiltered I] {G : I ⥤ Spc} (c : Cone G) : Prop :=
  ∀ n : ℤ, (∀ x : H R c.pt F n, ∃ (i : I) (y : H R (G.obj i) F n), pull R (c.π.app i) F n y = x) ∧
    ∀ (i : I) (y : H R (G.obj i) F n), pull R (c.π.app i) F n y = 0 → ∃ (k : I) (f : k ⟶ i), pull R (G.map f) F n y = 0

def AcycF (E : Spc) (F : Shv R) : Prop := ∀ n : ℤ, 0 < n → Subsingleton (H R E F n)

def EtFF : MorphismProperty CommRingCat.{0} := fun _ _ g => g.hom.Etale ∧ g.hom.FaithfullyFlat

def IndEt (A O : Type) [CommRing A] [CommRing O] [Algebra A O] : Prop :=
  GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsIndEtale (algebraMap A O)

def IndFEt (A O : Type) [CommRing A] [CommRing O] [Algebra A O] : Prop :=
  MorphismProperty.ind.{0} (RingHom.toMorphismProperty fun f => f.Etale ∧ f.Finite) (CommRingCat.ofHom (algebraMap A O))

theorem indEt_of_etale (A O : Type) [CommRing A] [CommRing O] [Algebra A O] [Algebra.Etale A O] : IndEt A O :=
  MorphismProperty.le_ind _ _ (RingHom.etale_algebraMap.2 inferInstance)

theorem indFEt_of_finite_etale (A O : Type) [CommRing A] [CommRing O] [Algebra A O] [Algebra.Etale A O] [Module.Finite A O] :
    IndFEt A O :=
  MorphismProperty.le_ind _ _ ⟨RingHom.etale_algebraMap.2 inferInstance, RingHom.finite_algebraMap.2 inferInstance⟩

set_option synthInstance.maxHeartbeats 200000 in
def bc {E : Spc} {S : Scheme.{0}} (p : E ⟶ sch.obj S) : Over S ⥤ Spc where
  obj U := pullback p (sch.map U.hom)
  map {U V} g := pullback.map p (sch.map U.hom) p (sch.map V.hom) (𝟙 _) (sch.map g.left) (𝟙 _) (by simp)
    (by rw [Category.comp_id, ← sch.map_comp, Over.w g])
  map_id U := by apply pullback.hom_ext <;> simp
  map_comp f g := by apply pullback.hom_ext <;> simp [pullback.map]

set_option synthInstance.maxHeartbeats 200000 in
def bcMap {E E' : Spc} {S : Scheme.{0}} (α : E ⟶ E') (p : E' ⟶ sch.obj S) : bc (α ≫ p) ⟶ bc p where
  app U := pullback.map (α ≫ p) (sch.map U.hom) p (sch.map U.hom) α (𝟙 _) (𝟙 _) (by simp) (by simp)
  naturality U V g := by apply pullback.hom_ext <;> simp [bc, pullback.map]

def QcqsOver {E : Spc} {S : Scheme.{0}} (p : E ⟶ sch.obj S) : Prop :=
  ∀ k : SimplexCategoryᵒᵖ, ∃ (X : Scheme.{0}) (r : X ⟶ S) (e : yoneda.obj X ≅ E.obj k),
    QuasiCompact r ∧ QuasiSeparated r ∧ e.hom ≫ p.app k = yoneda.map r

def IsStalk {S : Scheme.{0}} (O : Type) [CommRing O] (s : Spec (CommRingCat.of O) ⟶ S) : Prop :=
  SH O ∧ ∃ (A : Type) (_ : CommRing A) (_ : Algebra A O) (j : Spec (CommRingCat.of A) ⟶ S), Etale j ∧ IndEt A O ∧
    s = Spec.map (CommRingCat.ofHom (algebraMap A O)) ≫ j


variable {R} in
def Gen (F : Shv R) (S : Scheme.{0}) (g : Sec F S) : Prop :=
  ∀ (U : Scheme.{0}) (s : U ⟶ S),
    (∀ (x : Sec F U) (u : U), ∃ (V : Scheme.{0}) (j : V ⟶ U) (v : V) (c : R), Etale j ∧ j v = u ∧
      Sec.pull j x = (ULift.up c : ULift.{1} R) • Sec.pull (j ≫ s) g) ∧
    ∀ c : R, Nonempty U → (ULift.up c : ULift.{1} R) • Sec.pull s g = 0 → c = 0


variable {R} in
def val {P : PSh} {F : Shv R} (s : (free R).obj P ⟶ F) (U : Scheme.{0}) (x : P.obj (op U)) : Sec F U :=
  (s.hom.app (op U)).hom (freeGen R P U x)

def cechPt {Y X : Scheme.{0}} (f : Y ⟶ X) (k : ℕ) {U : Scheme.{0}} (x : U ⟶ X) (y : Fin (k + 1) → (U ⟶ Y)) (h : ∀ i, y i ≫ f = x) :
    Sx (cech f) k U :=
  (WidePullback.lift (arrows := fun _ : Fin (k + 1) => yoneda.map f) (yoneda.map x) (fun i => yoneda.map (y i))
    (fun i => by rw [← yoneda.map_comp, h i])).app (op U) (𝟙 U)


variable {R} in
def cobd {E : Spc} {F : Shv R} {n : ℕ} (s : (free R).obj (E.obj (op ⦋n⦌)) ⟶ F) : (free R).obj (E.obj (op ⦋n + 1⦌)) ⟶ F :=
  ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • ((free R).map (SimplicialObject.δ E i) ≫ s)


variable {R} in
def IsCls {E : Spc} {F : Shv R} {n : ℕ} (s : (free R).obj (E.obj (op ⦋n⦌)) ⟶ F) (x : H R E F n) : Prop :=
  ∃ z : Cocycle ((chains R).obj E) (res R F) n, CohomologyClass.mk z = x ∧
    z.1 = Cochain.single (p := -(n : ℤ)) (q := 0) ((chainsXIso R E n).hom ≫ s ≫ resι R F) n


variable {R} in
def Z1 (F : Shv R) (A B : Type) [CommRing A] [CommRing B] [Algebra A B] : AddSubgroup ((onRings F).obj (CommRingCat.of (B ⊗[A] B))) :=
  AddMonoidHom.eqLocus
    ((onRings F).map (CommRingCat.ofHom (Algebra.TensorProduct.map (AlgHom.id A B)
      (Algebra.TensorProduct.includeRight : B →ₐ[A] B ⊗[A] B)).toRingHom)).hom.toAddMonoidHom
    (((onRings F).map (CommRingCat.ofHom (Algebra.TensorProduct.map (AlgHom.id A B)
      (Algebra.TensorProduct.includeLeft : B →ₐ[A] B ⊗[A] B)).toRingHom)).hom.toAddMonoidHom +
     ((onRings F).map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeRight : B ⊗[A] B →ₐ[A] B ⊗[A] (B ⊗[A] B)).toRingHom)).hom.toAddMonoidHom)

def UCoc (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (u : (B ⊗[A] B)ˣ) : Prop :=
  Algebra.TensorProduct.map (AlgHom.id A B) (Algebra.TensorProduct.includeRight : B →ₐ[A] B ⊗[A] B) (u : B ⊗[A] B) =
    Algebra.TensorProduct.map (AlgHom.id A B) (Algebra.TensorProduct.includeLeft : B →ₐ[A] B ⊗[A] B) (u : B ⊗[A] B) *
      (Algebra.TensorProduct.includeRight : B ⊗[A] B →ₐ[A] B ⊗[A] (B ⊗[A] B)) (u : B ⊗[A] B)

def descMod (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (u : (B ⊗[A] B)ˣ) : Submodule A B :=
  LinearMap.eqLocus ((LinearMap.mulLeft A (u : B ⊗[A] B)) ∘ₗ (Algebra.TensorProduct.includeRight : B →ₐ[A] B ⊗[A] B).toLinearMap)
    (Algebra.TensorProduct.includeLeft : B →ₐ[A] B ⊗[A] B).toLinearMap

end GlobalTheory.EtC

end
end

section

noncomputable section

open TensorProduct Coalgebra Bialgebra WithConv Module

namespace GlobalTheory.PDiv

theorem finrank_eq_ker_mul_range (k A B : Type) [Field k] [CommRing A] [CommRing B]
    [HopfAlgebra k A] [HopfAlgebra k B] [Module.Finite k A] (f : B →ₐc[k] A) :
    finrank k A = finrank k (A ⧸ kerIdeal f) *
      finrank k (LinearMap.range (f : B →ₐ[k] A).toLinearMap) := by
  obtain ⟨e⟩ := GlobalTheory.HopfShear.shear k A B f
  exact GlobalTheory.finrank_eq_mul_of_basis_tensor_self k (AlgHom.range (f : B →ₐ[k] A)) A _ Subtype.val_injective
    ⟨((Module.finBasis k _).baseChange A).map e.symm⟩

variable {O : Type} [CommRing O]

abbrev fibreDim (M : Type) [AddCommGroup M] [Module O M] (q : PrimeSpectrum O) : ℕ :=
  finrank q.asIdeal.ResidueField (q.asIdeal.ResidueField ⊗[O] M)

abbrev fibreRank {M N : Type} [AddCommGroup M] [Module O M] [AddCommGroup N] [Module O N]
    (f : M →ₗ[O] N) (q : PrimeSpectrum O) : ℕ :=
  finrank q.asIdeal.ResidueField (LinearMap.range (f.baseChange q.asIdeal.ResidueField))

section Linear

variable {M N P : Type} [AddCommGroup M] [Module O M] [AddCommGroup N] [Module O N]
  [AddCommGroup P] [Module O P]

theorem fibreDim_congr (e : M ≃ₗ[O] N) (q : PrimeSpectrum O) : fibreDim M q = fibreDim N q :=
  (e.baseChange O _ M N).finrank_eq

theorem fibreRank_comp_of_surjective (g : N →ₗ[O] P) {f : M →ₗ[O] N}
    (hf : Function.Surjective f) (q : PrimeSpectrum O) :
    fibreRank (g ∘ₗ f) q = fibreRank g q := by
  rw [fibreRank, LinearMap.baseChange_comp, LinearMap.range_comp_of_range_eq_top]
  exact LinearMap.range_eq_top.2 (LinearMap.lTensor_surjective _ hf)

theorem fibreRank_equiv_comp (e : N ≃ₗ[O] P) (f : M →ₗ[O] N) (q : PrimeSpectrum O) :
    fibreRank (e.toLinearMap ∘ₗ f) q = fibreRank f q := by
  rw [fibreRank, LinearMap.baseChange_comp, LinearMap.range_comp]
  exact LinearEquiv.finrank_map_eq (e.baseChange O _ N P) _

variable [Module.Finite O M] [Module.Projective O M] [Module.Finite O N] [Module.Projective O N]

theorem fibreDim_dual (q : PrimeSpectrum O) : fibreDim (CartierDual O M) q = fibreDim M q :=
  (fibreDim_congr (CartierDual.toDual O M) q).trans (GlobalTheory.DualFibreRank.finrank_dual_and_range_dualMap_baseChange O M M _ LinearMap.id).1

theorem rankAtStalk_dual (q : PrimeSpectrum O) :
    rankAtStalk (CartierDual O M) q = rankAtStalk M q := by
  rw [rankAtStalk_eq, rankAtStalk_eq]
  exact fibreDim_dual q

theorem fibreRank_transpose (f : M →ₗ[O] N) (q : PrimeSpectrum O) :
    fibreRank (CartierDual.transpose f) q = fibreRank f q := by
  have h : CartierDual.transpose f = (CartierDual.toDual O M).symm.toLinearMap ∘ₗ
      (f.dualMap ∘ₗ (CartierDual.toDual O N).toLinearMap) := rfl
  rw [h, fibreRank_equiv_comp, fibreRank_comp_of_surjective _ (CartierDual.toDual O N).surjective]
  exact (GlobalTheory.DualFibreRank.finrank_dual_and_range_dualMap_baseChange O M N _ f).2

end Linear

variable {A B : Type} [CommRing A] [CommRing B] [HopfAlgebra O A] [HopfAlgebra O B]
  [Module.Finite O A]

theorem fibreDim_eq_ker_mul_range (f : B →ₐc[O] A) (q : PrimeSpectrum O) :
    fibreDim A q = fibreDim (A ⧸ kerIdeal f) q * fibreRank (f : B →ₐ[O] A).toLinearMap q :=
  GlobalTheory.hopf_order_formula_fibre finrank_eq_ker_mul_range O A B _ f

theorem fibreDim_ne_zero (q : PrimeSpectrum O) : fibreDim A q ≠ 0 := by
  have : Nontrivial (q.asIdeal.ResidueField ⊗[O] A) :=
    (counitAlgHom q.asIdeal.ResidueField (q.asIdeal.ResidueField ⊗[O] A)).domain_nontrivial
  exact finrank_pos.ne'

variable [Module.Projective O A] [Module.Finite O B] [Module.Projective O B]

theorem dual_map_surjective (f : B →ₐc[O] A)
    (h : ∀ q : PrimeSpectrum O, fibreDim A q = fibreDim (A ⧸ kerIdeal f) q * fibreDim B q) :
    Function.Surjective (CartierDual.map f) := by
  refine (GlobalTheory.surjective_injective_of_fibre_rank O _ _ (CartierDual.transpose (f : B →ₐ[O] A).toLinearMap)).1 fun q => ?_
  refine (fibreRank_transpose _ q).trans (Eq.trans ?_ (fibreDim_dual q).symm)
  have h1 := fibreDim_eq_ker_mul_range f q
  have h2 : fibreDim (A ⧸ kerIdeal f) q ≠ 0 := fun h0 =>
    fibreDim_ne_zero (A := A) q (by rw [h1, h0, zero_mul])
  exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero h2) (h1.symm.trans (h q))

theorem fibreDim_ker_dual [IsCocomm O A] (g : A →ₐc[O] A) (q : PrimeSpectrum O) :
    fibreDim (CartierDual O A ⧸ kerIdeal (CartierDual.map g)) q =
      fibreDim (A ⧸ kerIdeal g) q := by
  have h1 := fibreDim_eq_ker_mul_range g q
  have h2 := fibreDim_eq_ker_mul_range (CartierDual.map g) q
  have h3 : fibreRank (CartierDual.map g : CartierDual O A →ₐ[O] CartierDual O A).toLinearMap q =
    fibreRank (g : A →ₐ[O] A).toLinearMap q := fibreRank_transpose (g : A →ₐ[O] A).toLinearMap q
  rw [h3, fibreDim_dual, h1] at h2
  have h4 : fibreRank (g : A →ₐ[O] A).toLinearMap q ≠ 0 := fun h0 =>
    fibreDim_ne_zero (A := A) q (by rw [h1, h0, mul_zero])
  exact (Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero h4) h2).symm

theorem ker_eq_of_fibreDim_eq {D E : Type} [CommRing D] [CommRing E] [Algebra O D] [Algebra O E]
    [Module.Finite O D] [Module.Finite O E] [Module.Projective O E] (π : D →ₐ[O] E)
    (hπ : Function.Surjective π) (I : Ideal D) (hI : I ≤ RingHom.ker π)
    (h : ∀ q : PrimeSpectrum O, fibreDim (D ⧸ I) q = fibreDim E q) : RingHom.ker π = I := by
  refine le_antisymm (fun d hd => ?_) hI
  let π' : (D ⧸ I) →ₐ[O] E := Ideal.Quotient.liftₐ I π hI
  have hs : Function.Surjective π' := fun e => by
    obtain ⟨d, rfl⟩ := hπ e
    exact ⟨Ideal.Quotient.mk I d, rfl⟩
  have hi := (GlobalTheory.surjective_injective_of_fibre_rank O _ _ π'.toLinearMap).2 inferInstance inferInstance hs h
  exact Ideal.Quotient.eq_zero_iff_mem.1 (hi (a₁ := Ideal.Quotient.mk I d) (a₂ := 0)
    (by rw [map_zero]; exact hd))

end GlobalTheory.PDiv
end
end

section

namespace GlobalTheory.OTY

open MeasureTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y
open scoped ENNReal

noncomputable section

variable {n : ℕ} {Y : Type*} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La]

def jz (A : WeightedAtlas n Y ι La) (z : Y → V n) (i : ι) (y : Y) : V n →L[ℂ] V n :=
  fderiv ℂ (z ∘ (A.chart i).symm) (A.chart i y)

def jdet (A : WeightedAtlas n Y ι La) (z : Y → V n) : ι → Y → ℂ :=
  fun i y => (jz A z i y).det

structure Etale (A : WeightedAtlas n Y ι La) (U : Set Y) (z : Y → V n) : Prop where
  isOpen : IsOpen U
  holo : ∀ i, DifferentiableOn ℂ (z ∘ (A.chart i).symm)
    ((A.chart i).target ∩ (A.chart i).symm ⁻¹' U)
  det_ne : ∀ i y, y ∈ U → y ∈ (A.chart i).source → jdet A z i y ≠ 0

def nz (A : WeightedAtlas n Y ι La) (τ : ι → Y → ℂ) : Set Y := {y | τ (A.pick y) y ≠ 0}

structure Cover (A : WeightedAtlas n Y ι La) where

  m : ℕ

  idx : Fin m → ι

  c : Fin m → V n

  r : Fin m → ℝ

  chi : Fin m → Y → ℝ
  r_pos : ∀ a, 0 < r a
  sub : ∀ a, Metric.closedBall (c a) (r a) ⊆ (A.chart (idx a)).target
  smooth : ∀ a, A.SmoothFn (chi a)
  supp : ∀ a, tsupport (chi a) ⊆
    (A.chart (idx a)).source ∩ A.chart (idx a) ⁻¹' Metric.ball (c a) (r a)
  nonneg : ∀ a y, 0 ≤ chi a y
  sum_one : ∀ y, ∑ a, chi a y = 1

def n0 (A : WeightedAtlas n Y ι La) (la : La) (F : ι → Y → ℂ) : ℝ≥0∞ :=
  ∫⁻ y, ENNReal.ofReal (A.nsq (A.kap + la) F y) ∂A.mu

def n1 {A : WeightedAtlas n Y ι La} (C : Cover A) (la : La) (F : ι → Y → ℂ) : ℝ≥0∞ :=
  ∑ a, ∫⁻ v in Metric.ball (C.c a) (C.r a), ENNReal.ofReal
    ((∑ j, ‖wdb n j (F (C.idx a) ∘ (A.chart (C.idx a)).symm) v‖ ^ 2) *
      Real.exp (-A.ph la (C.idx a) ((A.chart (C.idx a)).symm v)))

def CurvGe {A : WeightedAtlas n Y ι La} (C : Cover A) (la : La) (t : ℝ) : Prop :=
  ∀ a, ∀ v ∈ Metric.ball (C.c a) (C.r a), ∀ ξ : Fin n → ℂ,
    t * ∑ j, ‖ξ j‖ ^ 2 ≤ A.leviAt (C.idx a) (A.ph la (C.idx a)) ((A.chart (C.idx a)).symm v) ξ

def glue {A : WeightedAtlas n Y ι La} (C : Cover A) (la : La) (u : Fin C.m → V n → ℂ) :
    ι → Y → ℂ :=
  fun i y => ∑ a, (C.chi a y : ℂ) * A.g (A.kap + la) i (C.idx a) y * u a (A.chart (C.idx a) y)

def wT (T x : ℝ) : ℝ := 1 / (1 + min (x ^ 2) ((T + 1) ^ 2))

def IsCut (T : ℝ) (θ : ℝ → ℝ) : Prop :=
  ContDiff ℝ (⊤ : ℕ∞) θ ∧ (∀ x, x ≤ -T - 1 → θ x = 1) ∧ (∀ x, -T + 1 ≤ x → θ x = 0) ∧
    (∀ x, 0 ≤ θ x ∧ θ x ≤ 1) ∧ ∀ x, |deriv θ x| ≤ 3 / 4

end

end GlobalTheory.OTY
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.LogPair

def SameDiv {X : Scheme.{0}} {L M : LB X} (σ : L.Sec) (τ : M.Sec) : Prop :=
  ∀ x : X, ∃ (U : X.Opens) (i : L.ι) (j : M.ι) (hi : U ≤ L.U i) (hj : U ≤ M.U j) (u : Γ(X, U)ˣ),
    x ∈ U ∧ resG X hi (σ.f i) = (u : Γ(X, U)) * resG X hj (τ.f j)

end GlobalTheory.LogPair
end
end
