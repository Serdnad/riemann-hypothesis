module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.RepresentationTheory.Coinduced
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.LongExactSequence
public import Mathlib.RepresentationTheory.Homological.Resolution
public import Mathlib.RepresentationTheory.Homological.TateCohomology.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Monoidal.Mon
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Basic

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.GroupCoh

open CategoryTheory Limits

universe u

section ModuleHomologyData

variable {R : Type u} [CommRing R]

noncomputable def moduleKernelIsLimit (S : ShortComplex (ModuleCat.{u} R))
    (K : Type u) [AddCommGroup K] [Module R K] (ι : K →ₗ[R] S.X₂) (hι : Function.Injective ι)
    (hrange : LinearMap.range ι = LinearMap.ker S.g.hom) (wi : ModuleCat.ofHom ι ≫ S.g = 0) :
    IsLimit (KernelFork.ofι (ModuleCat.ofHom ι) wi) :=
  KernelFork.IsLimit.ofι _ _
    (fun {A} k hk => ModuleCat.ofHom ((LinearEquiv.ofInjective ι hι).symm.toLinearMap ∘ₗ
      k.hom.codRestrict (LinearMap.range ι) (fun a => by
        rw [hrange, LinearMap.mem_ker]
        exact congr($hk a))))
    (fun {A} k hk => by
      ext a
      simp)
    (fun {A} k hk m hm => by
      ext a
      apply hι
      simp [← hm])

noncomputable def moduleLeftHomologyData (S : ShortComplex (ModuleCat.{u} R))
    (K : Type u) [AddCommGroup K] [Module R K] (ι : K →ₗ[R] S.X₂) (hι : Function.Injective ι)
    (hrange : LinearMap.range ι = LinearMap.ker S.g.hom) (N : Submodule R K)
    (hN : ∀ x, x ∈ N ↔ ι x ∈ LinearMap.range S.f.hom) : S.LeftHomologyData :=
  have wi : ModuleCat.ofHom ι ≫ S.g = 0 := by
    ext x
    have : ι x ∈ LinearMap.ker S.g.hom := hrange ▸ LinearMap.mem_range_self ι x
    simpa using LinearMap.mem_ker.1 this
  have hi := moduleKernelIsLimit S K ι hι hrange wi
  have hlift : ∀ c, ι ((hi.lift (KernelFork.ofι S.f S.zero)).hom c) = S.f.hom c := fun c =>
    congr($(Fork.IsLimit.lift_ι hi) c)
  have wπ : hi.lift (KernelFork.ofι S.f S.zero) ≫ ModuleCat.ofHom N.mkQ = 0 := by
    ext c
    simp [Submodule.Quotient.mk_eq_zero, hN, hlift]
  { K := ModuleCat.of R K
    H := ModuleCat.of R (K ⧸ N)
    i := ModuleCat.ofHom ι
    wi := wi
    hi := hi
    π := ModuleCat.ofHom N.mkQ
    wπ := wπ
    hπ := CokernelCofork.IsColimit.ofπ _ _
      (fun {A} k hk => ModuleCat.ofHom (N.liftQ k.hom (fun x hx => by
        obtain ⟨c, hc⟩ := (hN x).1 hx
        have : (hi.lift (KernelFork.ofι S.f S.zero)).hom c = x := hι (by rw [hlift, hc])
        rw [LinearMap.mem_ker, ← this]
        exact congr($hk c))))
      (fun {A} k hk => by
        ext x
        simp)
      (fun {A} k hk m hm => by
        ext x
        simp [← hm]) }

variable (S : ShortComplex (ModuleCat.{u} R))
    (K : Type u) [AddCommGroup K] [Module R K] (ι : K →ₗ[R] S.X₂) (hι : Function.Injective ι)
    (hrange : LinearMap.range ι = LinearMap.ker S.g.hom) (N : Submodule R K)
    (hN : ∀ x, x ∈ N ↔ ι x ∈ LinearMap.range S.f.hom)

lemma moduleLeftHomologyData_homologyIso_hom_homologyπ [S.HasHomology]
    (z : S.cycles) (x : K) (hx : ι x = S.iCycles.hom z) :
    (moduleLeftHomologyData S K ι hι hrange N hN).homologyIso.hom.hom (S.homologyπ.hom z) =
      Submodule.Quotient.mk x := by
  set h := moduleLeftHomologyData S K ι hι hrange N hN
  have h1 : (S.homologyπ ≫ h.homologyIso.hom).hom z = (h.cyclesIso.hom ≫ h.π).hom z := by
    rw [h.homologyπ_comp_homologyIso_hom]
  have h2 : (h.cyclesIso.hom ≫ h.i).hom z = S.iCycles.hom z := by
    rw [h.cyclesIso_hom_comp_i]
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h1 h2
  rw [h1]
  have : h.cyclesIso.hom.hom z = x := hι (by rw [hx, ← h2]; rfl)
  rw [this]
  rfl

variable {S₁ S₂ : ShortComplex (ModuleCat.{u} R)} (φ : S₁ ⟶ S₂)
    (K₁ : Type u) [AddCommGroup K₁] [Module R K₁] (ι₁ : K₁ →ₗ[R] S₁.X₂)
    (hι₁ : Function.Injective ι₁) (hrange₁ : LinearMap.range ι₁ = LinearMap.ker S₁.g.hom)
    (N₁ : Submodule R K₁) (hN₁ : ∀ x, x ∈ N₁ ↔ ι₁ x ∈ LinearMap.range S₁.f.hom)
    (K₂ : Type u) [AddCommGroup K₂] [Module R K₂] (ι₂ : K₂ →ₗ[R] S₂.X₂)
    (hι₂ : Function.Injective ι₂) (hrange₂ : LinearMap.range ι₂ = LinearMap.ker S₂.g.hom)
    (N₂ : Submodule R K₂) (hN₂ : ∀ x, x ∈ N₂ ↔ ι₂ x ∈ LinearMap.range S₂.f.hom)

noncomputable def moduleLeftHomologyMapData (φK : K₁ →ₗ[R] K₂)
    (hφK : ∀ x, ι₂ (φK x) = φ.τ₂.hom (ι₁ x)) (hφN : N₁ ≤ N₂.comap φK) :
    ShortComplex.LeftHomologyMapData φ (moduleLeftHomologyData S₁ K₁ ι₁ hι₁ hrange₁ N₁ hN₁)
      (moduleLeftHomologyData S₂ K₂ ι₂ hι₂ hrange₂ N₂ hN₂) where
  φK := ModuleCat.ofHom φK
  φH := ModuleCat.ofHom (N₁.mapQ N₂ φK hφN)
  commi := by
    ext x
    exact hφK x
  commf' := by
    ext c
    apply hι₂
    have e₁ : ι₁ ((moduleLeftHomologyData S₁ K₁ ι₁ hι₁ hrange₁ N₁ hN₁).f'.hom c) = S₁.f.hom c :=
      congr($((moduleLeftHomologyData S₁ K₁ ι₁ hι₁ hrange₁ N₁ hN₁).f'_i).hom c)
    have e₂ : ι₂ ((moduleLeftHomologyData S₂ K₂ ι₂ hι₂ hrange₂ N₂ hN₂).f'.hom (φ.τ₁.hom c)) =
        S₂.f.hom (φ.τ₁.hom c) :=
      congr($((moduleLeftHomologyData S₂ K₂ ι₂ hι₂ hrange₂ N₂ hN₂).f'_i).hom (φ.τ₁.hom c))
    have e₃ : S₂.f.hom (φ.τ₁.hom c) = φ.τ₂.hom (S₁.f.hom c) := congr($(φ.comm₁₂).hom c)
    exact (hφK _).trans ((congrArg φ.τ₂.hom e₁).trans (e₃.symm.trans e₂.symm))
  commπ := by
    ext x
    rfl

end ModuleHomologyData
section Complexes

variable {R : Type u} [CommRing R]

lemma homologyFunctorIso'_moduleLeftHomologyData_apply {ιc : Type*} {c : ComplexShape ιc}
    (C : HomologicalComplex (ModuleCat.{u} R) c) (i j k : ιc) (hi : c.prev j = i)
    (hk : c.next j = k) (K : Type u) [AddCommGroup K] [Module R K]
    (ι : K →ₗ[R] (C.sc' i j k).X₂) (hι : Function.Injective ι)
    (hrange : LinearMap.range ι = LinearMap.ker (C.sc' i j k).g.hom) (N : Submodule R K)
    (hN : ∀ x, x ∈ N ↔ ι x ∈ LinearMap.range (C.sc' i j k).f.hom)
    (z : C.cycles j) (x : K) (hx : ι x = (C.iCycles j).hom z) :
    (moduleLeftHomologyData _ K ι hι hrange N hN).homologyIso.hom.hom
      (((HomologicalComplex.homologyFunctorIso' _ c i j k hi hk).hom.app C).hom
        ((C.homologyπ j).hom z)) = Submodule.Quotient.mk x := by
  set e := (HomologicalComplex.natIsoSc' (ModuleCat.{u} R) c i j k hi hk).hom.app C
  have h1 : (HomologicalComplex.homologyFunctorIso' _ c i j k hi hk).hom.app C =
      ShortComplex.homologyMap e := by
    simp [HomologicalComplex.homologyFunctorIso', e]
  have h2 : (ShortComplex.homologyMap e).hom ((C.sc j).homologyπ.hom z) =
      (C.sc' i j k).homologyπ.hom ((ShortComplex.cyclesMap e).hom z) :=
    congr(($(ShortComplex.homologyπ_naturality e)).hom z)
  have h3 : (C.sc' i j k).iCycles.hom ((ShortComplex.cyclesMap e).hom z) =
      e.τ₂.hom ((C.sc j).iCycles.hom z) :=
    congr(($(ShortComplex.cyclesMap_i e)).hom z)
  have h4 : (C.sc' i j k).iCycles.hom ((ShortComplex.cyclesMap e).hom z) = (C.iCycles j).hom z := by
    rw [h3]
    simp [e]
    rfl
  rw [h1]
  refine (congrArg (fun w => (moduleLeftHomologyData _ K ι hι hrange N hN).homologyIso.hom.hom w)
    h2).trans ?_
  exact moduleLeftHomologyData_homologyIso_hom_homologyπ _ K ι hι hrange N hN _ x (hx.trans h4.symm)

lemma exists_cycles_of_moduleLeftHomologyData {ιc : Type*} {c : ComplexShape ιc}
    (C : HomologicalComplex (ModuleCat.{u} R) c) (i j k : ιc) (hi : c.prev j = i)
    (hk : c.next j = k) (K : Type u) [AddCommGroup K] [Module R K]
    (ι : K →ₗ[R] (C.sc' i j k).X₂) (hι : Function.Injective ι)
    (hrange : LinearMap.range ι = LinearMap.ker (C.sc' i j k).g.hom) (N : Submodule R K)
    (hN : ∀ x, x ∈ N ↔ ι x ∈ LinearMap.range (C.sc' i j k).f.hom) (x : K) :
    ∃ z : C.cycles j, (C.iCycles j).hom z = ι x := by
  set e := (HomologicalComplex.natIsoSc' (ModuleCat.{u} R) c i j k hi hk).inv.app C
  set h := moduleLeftHomologyData _ K ι hι hrange N hN
  refine ⟨(ShortComplex.cyclesMap e).hom (h.cyclesIso.inv.hom x), ?_⟩
  have h3 : (C.sc j).iCycles.hom ((ShortComplex.cyclesMap e).hom (h.cyclesIso.inv.hom x)) =
      e.τ₂.hom ((C.sc' i j k).iCycles.hom (h.cyclesIso.inv.hom x)) :=
    congr(($(ShortComplex.cyclesMap_i e)).hom (h.cyclesIso.inv.hom x))
  have h4 : (C.sc' i j k).iCycles.hom (h.cyclesIso.inv.hom x) = ι x :=
    congr(($(h.cyclesIso_inv_comp_iCycles)).hom x)
  refine h3.trans ?_
  rw [h4]
  simp [e]

end Complexes

end GroundTheory.GroupCoh
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.GroupCoh

open CategoryTheory groupCohomology Rep

universe u

variable {k G : Type u} [CommRing k] [Group G] (A : Rep k G) (S : Subgroup G) [S.Normal]

def conjHom (g : G) : S →* S where
  toFun s := ⟨g⁻¹ * s * g, ‹S.Normal›.conj_mem' (s : G) s.2 g⟩
  map_one' := by ext; simp
  map_mul' s t := by ext; simp only [Subgroup.coe_mul]; group

@[simp]
lemma coe_conjHom_apply (g : G) (s : S) : (conjHom S g s : G) = g⁻¹ * s * g := rfl

noncomputable def conjMor (g : G) : res (conjHom S g) (res S.subtype A) ⟶ res S.subtype A :=
  ofHom ⟨A.ρ g, fun s => by
    ext a
    simp only [LinearMap.comp_apply, MonoidHom.coe_comp, Function.comp_apply,
      Subgroup.coe_subtype, coe_conjHom_apply]
    rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
    congr 2
    group⟩


end GroundTheory.GroupCoh
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.GroupCoh

open CategoryTheory groupCohomology Rep

universe u

variable {k G H : Type u} [CommRing k] [Group G] [Group H]

noncomputable def cochainsMapShortComplex (f : G →* H) {X : ShortComplex (Rep k H)}
    {Y : ShortComplex (Rep k G)} (F : X.map (resFunctor f) ⟶ Y) :
    X.map (cochainsFunctor k H) ⟶ Y.map (cochainsFunctor k G) where
  τ₁ := cochainsMap f F.τ₁
  τ₂ := cochainsMap f F.τ₂
  τ₃ := cochainsMap f F.τ₃
  comm₁₂ := by
    ext n x
    refine funext fun g => ?_
    exact congrArg (fun φ => φ.hom (x (f ∘ g))) F.comm₁₂
  comm₂₃ := by
    ext n x
    refine funext fun g => ?_
    exact congrArg (fun φ => φ.hom (x (f ∘ g))) F.comm₂₃

theorem δ_comp_map (f : G →* H) {X : ShortComplex (Rep k H)} {Y : ShortComplex (Rep k G)}
    (hX : X.ShortExact) (hY : Y.ShortExact) (F : X.map (resFunctor f) ⟶ Y)
    (i j : ℕ) (hij : i + 1 = j) :
    δ hX i j hij ≫ map f F.τ₁ j = map f F.τ₃ i ≫ δ hY i j hij :=
  HomologicalComplex.HomologySequence.δ_naturality (cochainsMapShortComplex f F)
    (map_cochainsFunctor_shortExact hX) (map_cochainsFunctor_shortExact hY) i j hij

theorem δ_comp_map_res (f : G →* H) {X : ShortComplex (Rep k H)} (hX : X.ShortExact)
    (i j : ℕ) (hij : i + 1 = j) :
    δ hX i j hij ≫ map f (𝟙 (res f X.X₁)) j =
      map f (𝟙 (res f X.X₃)) i ≫ δ ((shortExact_res f).2 hX) i j hij :=
  δ_comp_map f hX ((shortExact_res f).2 hX) (𝟙 _) i j hij

end GroundTheory.GroupCoh
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.GroupCoh

open CategoryTheory Limits groupCohomology Rep

universe v w u

section HomComplex

variable {R : Type w} [Ring R] {C : Type u} [Category.{v} C] [Abelian C] [Linear R C]

noncomputable def linearYonedaObjMap {X Y : ChainComplex C ℕ} (f : X ⟶ Y) (B : C) :
    Y.linearYonedaObj R B ⟶ X.linearYonedaObj R B :=
  (HomologicalComplex.unopFunctor (ModuleCat R) (ComplexShape.down ℕ)).map
    ((((linearYoneda R C).obj B).rightOp.mapHomologicalComplex _).map f).op

lemma linearYonedaObjMap_comp {X Y Z : ChainComplex C ℕ} (f : X ⟶ Y) (g : Y ⟶ Z) (B : C) :
    linearYonedaObjMap (R := R) (f ≫ g) B = linearYonedaObjMap g B ≫ linearYonedaObjMap f B := by
  ext n x
  change (f ≫ g).f n ≫ x = f.f n ≫ g.f n ≫ x
  rw [HomologicalComplex.comp_f]
  exact Category.assoc _ _ _

lemma linearYonedaObjMap_id (X : ChainComplex C ℕ) (B : C) :
    linearYonedaObjMap (R := R) (𝟙 X) B = 𝟙 _ := by
  ext n x
  change (𝟙 X : X ⟶ X).f n ≫ x = x
  rw [HomologicalComplex.id_f]
  exact Category.id_comp _

noncomputable def linearYonedaObjHomotopy {X Y : ChainComplex C ℕ} {f g : X ⟶ Y}
    (h : Homotopy f g) (B : C) :
    Homotopy (linearYonedaObjMap (R := R) f B) (linearYonedaObjMap g B) :=
  ((((linearYoneda R C).obj B).rightOp).mapHomotopy h).unop

noncomputable def linearYonedaObjHomotopyEquiv {X Y : ChainComplex C ℕ} (e : HomotopyEquiv X Y)
    (B : C) : HomotopyEquiv (Y.linearYonedaObj R B) (X.linearYonedaObj R B) where
  hom := linearYonedaObjMap e.hom B
  inv := linearYonedaObjMap e.inv B
  homotopyHomInvId := (Homotopy.ofEq (linearYonedaObjMap_comp _ _ _).symm).trans
    ((linearYonedaObjHomotopy e.homotopyInvHomId B).trans
      (Homotopy.ofEq (linearYonedaObjMap_id _ _)))
  homotopyInvHomId := (Homotopy.ofEq (linearYonedaObjMap_comp _ _ _).symm).trans
    ((linearYonedaObjHomotopy e.homotopyHomInvId B).trans
      (Homotopy.ofEq (linearYonedaObjMap_id _ _)))

end HomComplex

section Bar

variable {k G : Type u} [CommRing k] [Group G]


set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
lemma diagonalSuccIsoFree_inv_single (m : ℕ) (f : Fin m → G) (g : G) (r : k) :
    (diagonalSuccIsoFree k G m).inv.hom (Finsupp.single f (MonoidAlgebra.single g r)) =
      MonoidAlgebra.single (g • Fin.partialProd f) r := by
  simp only [diagonalSuccIsoFree, diagonalSuccIsoTensorTrivial, Iso.trans_inv, Rep.hom_comp,
    Representation.IntertwiningMap.comp_apply]
  have step1 : (Hom.hom (leftRegularTensorTrivialIsoFree k G (Fin m → G)).inv)
      (Finsupp.single f (.single g r)) = .single g 1 ⊗ₜ[k] .single f r :=
    Representation.leftRegularTensorTrivialIsoFree_symm_apply_single_single f g r
  rw [step1]
  simp only [mkIso_inv, Representation.linearizeOfMulActionIso, Representation.Equiv.mk_symm,
    LinearEquiv.refl_symm, ConcreteCategory.hom_ofHom, Action.tensorObj_V, Action.trivial_V,
    Functor.mapIso_inv, tensor_V, tensor_ρ, Iso.symm_inv, Functor.Monoidal.μIso_hom, μ_hom,
    MonoidalCategory.tensorIso_inv, Representation.linearizeTrivialIso, hom_tensorHom,
    Representation.IntertwiningMap.tensor_apply, Representation.Equiv.coe_toIntertwiningMap,
    Representation.Equiv.mk_apply, LinearEquiv.refl_apply]
  have key₁ := Representation.linearizeMap_single (k := k)
    (Action.diagonalSuccIsoTensorTrivial G m).inv (g, f) ((1 : k) * r)
  have key₂ := Representation.LinearizeMonoidal.μ_apply_single_single (k := k)
    (X := Action.leftRegular G) (Y := Action.trivial G (Fin m → G)) g f 1 r
  exact ((congrArg (fun z => (Representation.linearizeMap
    (Action.diagonalSuccIsoTensorTrivial G m).inv) z) key₂).trans key₁).trans (by
      rw [one_mul]
      exact congrArg (fun h => MonoidAlgebra.single h r)
        (Action.diagonalSuccIsoTensorTrivial_inv_hom_apply g f))

lemma barResolution_π_f_zero_single (v : Fin 0 → G) (g : G) (r : k) :
    ((barResolution k G).π.f 0).hom (Finsupp.single v (MonoidAlgebra.single g r)) = r := by
  change (standardComplex.ε k G).hom ((diagonalSuccIsoFree k G 0).inv.hom
    (Finsupp.single v (MonoidAlgebra.single g r))) = r
  rw [diagonalSuccIsoFree_inv_single]
  simp [standardComplex.ε]

end Bar

section Norm

variable {k H : Type u} [CommRing k] [Group H] [Fintype H]

lemma ρ_apply_norm (B : Rep.{u} k H) (b : B) (s : H) : B.ρ s (B.ρ.norm b) = B.ρ.norm b := by

  rw [Representation.norm, LinearMap.sum_apply, map_sum]
  refine Fintype.sum_equiv (Equiv.mulLeft s) _ _ fun t => ?_
  simp [← Module.End.mul_apply, ← map_mul]

end Norm

end GroundTheory.GroupCoh
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.GroupCoh

universe w u v

variable {k : Type u} {G : Type v} [CommRing k] [Group G]

def repSubOne (A : Rep.{w} k G) (σ : G) : A →+ A :=
  (A.ρ σ - 1 : Module.End k A).toAddMonoidHom

theorem repSubOne_apply (A : Rep.{w} k G) (σ : G) (x : A) : repSubOne A σ x = A.ρ σ x - x :=
  rfl

variable [Fintype G]

def repNorm (A : Rep.{w} k G) : A →+ A :=
  A.ρ.norm.toAddMonoidHom

end GroundTheory.GroupCoh
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.GroupCoh

open CategoryTheory groupHomology TensorProduct Finsupp

universe u

section General

variable {k G : Type u} [CommRing k] [Group G] (A : Rep k G) [A.IsTrivial]

end General

section Tate

variable {k G : Type u} [CommRing k] [Group G] [Fintype G] (A : Rep k G)

noncomputable def tateNegTwoIsoH1 : tateCohomology A (-2) ≅ H1 A :=
  (TateCohomology.isoGroupHomology (-2) 1 (by norm_num)).app A

variable [A.IsTrivial]

end Tate

section Int

variable (G : Type) [Group G]

variable [Fintype G]

end Int

section ULiftInt

variable (G : Type u) [Group G]

variable [Fintype G]

end ULiftInt

end GroundTheory.GroupCoh
end
