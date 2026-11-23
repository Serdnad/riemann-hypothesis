module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.RestrictionMemInvariantH1
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Length
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
public import Mathlib.RingTheory.RootsOfUnity.EnoughRootsOfUnity
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
public import Mathlib.GroupTheory.FiniteAbelian.Duality
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.RingTheory.LocalRing.Length

@[expose] public section

section

noncomputable section

open ReciprocityTheory.Gal TensorProduct

namespace UpperTheory.V.Base

section Alg

variable {R O ι N N' : Type} [CommRing R] [CommRing O] [Algebra R O] [Fintype ι] [AddCommGroup N] [Module R N]
  [AddCommGroup N'] [Module O N'] [Module R N'] [IsScalarTower R O N']

def coordSum (b : Module.Basis ι R O) (j : N →ₗ[R] N') : (ι → N) →ₗ[R] N' where
  toFun x := ∑ i, b i • j (x i)
  map_add' x y := by simp [Finset.sum_add_distrib]
  map_smul' r x := by simp [Finset.smul_sum, smul_comm r]

theorem coordSum_apply (b : Module.Basis ι R O) (j : N →ₗ[R] N') (x : ι → N) :
    coordSum b j x = ∑ i, b i • j (x i) := rfl

theorem isBaseChange_iff_coordSum (b : Module.Basis ι R O) (j : N →ₗ[R] N') :
    IsBaseChange O j ↔ Function.Bijective (coordSum b j) := by
  classical
  let e : (ι → N) ≃ₗ[R] O ⊗[R] N :=
    (Finsupp.linearEquivFunOnFinite R N ι).symm ≪≫ₗ (TensorProduct.equivFinsuppOfBasisLeft b).symm
  have he : ∀ x, e x = ∑ i, b i ⊗ₜ x i := fun x => by
    simp [e, TensorProduct.equivFinsuppOfBasisLeft_symm_apply, Finsupp.sum_fintype]
  unfold IsBaseChange IsTensorProduct
  rw [← Function.Bijective.of_comp_iff _ e.bijective]
  refine iff_of_eq (congrArg _ (funext fun x => ?_))
  simp [he, coordSum_apply]

theorem isBaseChange_restrict (b : Module.Basis ι R O) {j : N →ₗ[R] N'} (hj : IsBaseChange O j)
    (P : Submodule R N) (P' : Submodule O N') (h : ∀ x, coordSum b j x ∈ P' ↔ ∀ i, x i ∈ P)
    (j' : P →ₗ[R] P') (hj' : ∀ x, (j' x : N') = j x) : IsBaseChange O j' := by
  rw [isBaseChange_iff_coordSum b] at hj ⊢
  have e : ∀ x : ι → P, (coordSum b j' x : N') = coordSum b j fun i => x i := fun x => by
    simp [coordSum_apply, hj']
  refine ⟨fun x y hxy => funext fun i => Subtype.ext ?_, fun y => ?_⟩
  · exact congrFun (hj.1 ((e x).symm.trans ((congrArg Subtype.val hxy).trans (e y)))) i
  · obtain ⟨x, hx⟩ := hj.2 y
    exact ⟨fun i => ⟨x i, (h x).1 (hx ▸ y.2) i⟩, Subtype.ext ((e _).trans hx)⟩

theorem length_of_isBaseChange [IsLocalRing R] [IsLocalRing O] [IsLocalHom (algebraMap R O)] [Module.Flat R O]
    {j : N →ₗ[R] N'} (hj : IsBaseChange O j) :
    Module.length O N' =
      Module.length R N * Module.length O (O ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R O)) := by
  rw [← hj.equiv.length_eq, IsLocalRing.length_baseChange]

theorem map_coordSum (b : Module.Basis ι R O) (j : N →ₗ[R] N') (f : N → N) (f' : N' →ₗ[O] N')
    (h : ∀ x, j (f x) = f' (j x)) (x : ι → N) : f' (coordSum b j x) = coordSum b j fun i => f (x i) := by
  simp [coordSum_apply, h]

end Alg

section Coh

variable {R G M : Type} [CommRing R] [Group G] [TopologicalSpace G] [AddCommGroup M] [Module R M]
  [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul R M] [DiscreteTopology M]
  {O M' : Type} [CommRing O] [Algebra R O] [AddCommGroup M'] [Module O M'] [Module R M'] [IsScalarTower R O M']
  [TopologicalSpace M'] [IsTopologicalAddGroup M'] [ContinuousConstSMul O M']
  (ρ : Representation R G M) (ρ' : Representation O G M') (j : M →ₗ[R] M') (hj : ∀ g m, j (ρ g m) = ρ' g (j m))
  (U : Subgroup G)

def continuousCocycleMap : Z1U ρ U →ₗ[R] Z1U ρ' U where
  toFun z := ⟨fun u => j (z.1 u), (continuous_of_discreteTopology (f := j)).comp z.2.1, fun g h => by
    show j _ = j _ + ρ' g (j _)
    rw [z.2.2, map_add (f := _), ← hj]
    rfl⟩
  map_add' _ _ := Subtype.ext (funext fun _ => map_add j _ _)
  map_smul' _ _ := Subtype.ext (funext fun _ => map_smul j _ _)

theorem continuousCocycleMap_apply (z : Z1U ρ U) (u : U) : (continuousCocycleMap ρ ρ' j hj U z).1 u = j (z.1 u) := rfl

def h1Map : H1U ρ U →ₗ[R] H1U ρ' U :=
  Submodule.liftQ _ (((Submodule.mkQ _).restrictScalars R).comp (continuousCocycleMap ρ ρ' j hj U)) fun z hz => by
    obtain ⟨m, hm⟩ := (mem_coboundaries1 _ _).1 hz
    refine (Submodule.Quotient.mk_eq_zero _).2 ((mem_coboundaries1 _ _).2 ⟨j m, fun u => ?_⟩)
    have e : z.1 u = ρ u m - m := hm u
    show j (z.1 u) = ρ' u (j m) - j m
    rw [e, map_sub, hj]

theorem h1Map_mk (z : Z1U ρ U) :
    h1Map ρ ρ' j hj U (Submodule.Quotient.mk z) = Submodule.Quotient.mk (continuousCocycleMap ρ ρ' j hj U z) := rfl

theorem h1Map_mem_locSel (𝒟 : Set (Subgroup G)) {x : H1U ρ U} (hx : x ∈ LocSel ρ U 𝒟) :
    h1Map ρ ρ' j hj U x ∈ LocSel ρ' U 𝒟 := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [h1Map_mk, mk_mem_locSel]
  intro D hD
  obtain ⟨m, hm⟩ := mk_mem_locSel.1 hx D hD
  exact ⟨j m, fun u hu => by rw [continuousCocycleMap_apply, hm u hu, map_sub, hj]⟩

def selMap (𝒟 : Set (Subgroup G)) : LocSel ρ U 𝒟 →ₗ[R] LocSel ρ' U 𝒟 where
  toFun x := ⟨h1Map ρ ρ' j hj U x, h1Map_mem_locSel ρ ρ' j hj U 𝒟 x.2⟩
  map_add' _ _ := Subtype.ext (by simp)
  map_smul' _ _ := Subtype.ext (by simp)

variable {ι : Type} [Fintype ι] (b : Module.Basis ι R O)

theorem coordSum_z1Map (z : ι → Z1U ρ U) (u : U) :
    (coordSum b (continuousCocycleMap ρ ρ' j hj U) z).1 u = coordSum b j fun i => (z i).1 u := by
  simp [coordSum_apply, continuousCocycleMap_apply]

theorem coordSum_h1Map (z : ι → Z1U ρ U) :
    coordSum b (h1Map ρ ρ' j hj U) (fun i => Submodule.Quotient.mk (z i)) =
      Submodule.Quotient.mk (coordSum b (continuousCocycleMap ρ ρ' j hj U) z) := by

  simp only [coordSum_apply, h1Map_mk, ← Submodule.mkQ_apply, map_sum, map_smul]
  rfl

include hj in
theorem exists_cob_iff (hb : IsBaseChange O j) (p : U → Prop) (z : ι → U → M) :
    (∃ m', ∀ u : U, p u → coordSum b j (fun i => z i u) = ρ' u m' - m') ↔
      ∀ i, ∃ m, ∀ u : U, p u → z i u = ρ u m - m := by
  rw [isBaseChange_iff_coordSum b] at hb
  have e : ∀ (u : U) (m : ι → M), ρ' u (coordSum b j m) - coordSum b j m = coordSum b j fun i => ρ u (m i) - m i :=
    fun u m => by
      rw [map_coordSum b j (ρ u) (ρ' u) (hj u), ← map_sub]
      rfl
  constructor
  · rintro ⟨m', hm⟩ i
    obtain ⟨m, rfl⟩ := hb.2 m'
    exact ⟨m i, fun u hu => congrFun (hb.1 ((hm u hu).trans (e u m))) i⟩
  · intro h
    choose m hm using h
    exact ⟨coordSum b j m, fun u hu => by rw [e]; exact congrArg _ (funext fun i => hm i u hu)⟩

theorem coordSum_z1Map_surjective [DiscreteTopology M'] (hb : IsBaseChange O j) :
    Function.Surjective (coordSum b (continuousCocycleMap ρ ρ' j hj U)) := by
  rw [isBaseChange_iff_coordSum b] at hb
  intro y
  let e := LinearEquiv.ofBijective _ hb
  have he : ∀ m, coordSum b j (e.symm m) = m := e.apply_symm_apply
  refine ⟨fun i => ⟨fun u => e.symm (y.1 u) i,
    (continuous_of_discreteTopology (f := fun m => e.symm m i)).comp y.2.1, fun g h => ?_⟩, ?_⟩
  · have : e.symm (y.1 (g * h)) = e.symm (y.1 g) + fun i => ρ g (e.symm (y.1 h) i) := by
      apply hb.1
      rw [map_add (f := _), ← map_coordSum b j (ρ g) (ρ' g) (hj g), he, he, he]
      exact y.2.2 g h
    exact congrFun this i
  · exact Subtype.ext (funext fun u => (coordSum_z1Map ρ ρ' j hj U b _ u).trans (he _))

include b in
private theorem isBaseChange_h1Map' [DiscreteTopology M'] (hb : IsBaseChange O j) :
    IsBaseChange O (h1Map ρ ρ' j hj U) := by
  rw [isBaseChange_iff_coordSum b]
  constructor
  · rw [injective_iff_map_eq_zero]
    intro x hx
    choose z hz using fun i => Submodule.Quotient.mk_surjective _ (x i)
    obtain rfl : x = fun i => Submodule.Quotient.mk (z i) := funext fun i => (hz i).symm
    rw [coordSum_h1Map] at hx
    obtain ⟨m', hm'⟩ := (mem_coboundaries1 _ _).1 ((Submodule.Quotient.mk_eq_zero _).1 hx)
    funext i
    obtain ⟨m, hm⟩ := (exists_cob_iff ρ ρ' j hj U b hb (fun _ => True) fun i => (z i).1).1
      ⟨m', fun u _ => (coordSum_z1Map ρ ρ' j hj U b z u).symm.trans (hm' u)⟩ i
    exact (Submodule.Quotient.mk_eq_zero _).2 ((mem_coboundaries1 _ _).2 ⟨m, fun u => hm u trivial⟩)
  · intro y
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    obtain ⟨z, rfl⟩ := coordSum_z1Map_surjective ρ ρ' j hj U b hb y
    exact ⟨_, coordSum_h1Map ρ ρ' j hj U b z⟩

theorem coordSum_mem_locSel (hb : IsBaseChange O j) (𝒟 : Set (Subgroup G)) (x : ι → H1U ρ U) :
    coordSum b (h1Map ρ ρ' j hj U) x ∈ LocSel ρ' U 𝒟 ↔ ∀ i, x i ∈ LocSel ρ U 𝒟 := by
  choose z hz using fun i => Submodule.Quotient.mk_surjective _ (x i)
  obtain rfl : x = fun i => Submodule.Quotient.mk (z i) := funext fun i => (hz i).symm
  rw [coordSum_h1Map]
  simp only [mk_mem_locSel, coordSum_z1Map]
  rw [forall_comm]
  refine forall_congr' fun D => ?_
  rw [forall_comm]
  exact imp_congr_right fun _ => exists_cob_iff ρ ρ' j hj U b hb (fun u => u.1 ∈ D) fun i => (z i).1


omit [Fintype ι] in
theorem isBaseChange_h1Map [Module.Free R O] [Module.Finite R O] [DiscreteTopology M'] (hb : IsBaseChange O j) :
    IsBaseChange O (h1Map ρ ρ' j hj U) :=
  isBaseChange_h1Map' ρ ρ' j hj U (Module.Free.chooseBasis R O) hb


omit [Fintype ι] in
theorem isBaseChange_selMap [Module.Free R O] [Module.Finite R O] [DiscreteTopology M'] (hb : IsBaseChange O j)
    (𝒟 : Set (Subgroup G)) : IsBaseChange O (selMap ρ ρ' j hj U 𝒟) :=
  isBaseChange_restrict (Module.Free.chooseBasis R O) (isBaseChange_h1Map ρ ρ' j hj U hb) _ _
    (coordSum_mem_locSel ρ ρ' j hj U _ hb 𝒟) _ fun _ => rfl

end Coh

end UpperTheory.V.Base

end
end

section

open ReciprocityTheory.Gal UpperTheory.V.Base

section

variable {R G M : Type} [CommRing R] [Group G] [TopologicalSpace G] [AddCommGroup M] [Module R M]
  [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul R M]

private noncomputable def h1MapOfAgreeOnSubgroup (ρ ρ' : Representation R G M) (U : Subgroup G)
    (h : ∀ (u : U) m, ρ u m = ρ' u m) : H1U ρ U →ₗ[R] H1U ρ' U :=
  pairH1DecompositionMap _ _ (MonoidHom.id U) continuous_id LinearMap.id continuous_id fun u m => h u m

private theorem sameH1_mk (ρ ρ' : Representation R G M) (U : Subgroup G)
    (h : ∀ (u : U) m, ρ u m = ρ' u m) (z : Z1U ρ U) :
    ∃ z' : Z1U ρ' U, h1MapOfAgreeOnSubgroup ρ ρ' U h (Submodule.Quotient.mk z) = Submodule.Quotient.mk z' ∧
      ∀ u : U, z'.1 u = z.1 u := ⟨_, rfl, fun _ => rfl⟩

private theorem sameH1_involutive (ρ ρ' : Representation R G M) (U : Subgroup G)
    (h : ∀ (u : U) m, ρ u m = ρ' u m) (h' : ∀ (u : U) m, ρ' u m = ρ u m) (x : H1U ρ U) :
    h1MapOfAgreeOnSubgroup ρ' ρ U h' (h1MapOfAgreeOnSubgroup ρ ρ' U h x) = x := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rfl

private theorem sameH1_mem_localSelmer (ρ ρ' : Representation R G M) (U : Subgroup G)
    (h : ∀ (u : U) m, ρ u m = ρ' u m) (𝒟 : Set (Subgroup G)) (x : H1U ρ U) (hx : x ∈ LocSel ρ U 𝒟) :
    h1MapOfAgreeOnSubgroup ρ ρ' U h x ∈ LocSel ρ' U 𝒟 := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  obtain ⟨z', e, f⟩ := sameH1_mk ρ ρ' U h z
  rw [e]
  rw [mk_mem_locSel] at hx ⊢
  intro D hD
  obtain ⟨m, hm⟩ := hx D hD
  exact ⟨m, fun u hu => by rw [f, hm u hu, h]⟩

private noncomputable def sameSel (ρ ρ' : Representation R G M) (U : Subgroup G)
    (h : ∀ (u : U) m, ρ u m = ρ' u m) (𝒟 : Set (Subgroup G)) : LocSel ρ U 𝒟 ≃ₗ[R] LocSel ρ' U 𝒟 :=
  LinearEquiv.ofLinear ((h1MapOfAgreeOnSubgroup ρ ρ' U h).restrict (sameH1_mem_localSelmer ρ ρ' U h 𝒟))
    ((h1MapOfAgreeOnSubgroup ρ' ρ U fun u m => (h u m).symm).restrict (sameH1_mem_localSelmer ρ' ρ U _ 𝒟))
    (LinearMap.ext fun x => Subtype.ext (sameH1_involutive ρ' ρ U _ h x.1))
    (LinearMap.ext fun x => Subtype.ext (sameH1_involutive ρ ρ' U h _ x.1))

private theorem sameH1_conjugation_scalar [IsTopologicalGroup G] [DiscreteTopology M] (ρ ρ' : Representation R G M)
    (U : Subgroup G) [U.Normal] (h : ∀ (u : U) m, ρ u m = ρ' u m) (g : G) (c : R)
    (hg : ∀ m, ρ g m = c • ρ' g m) (x : H1U ρ U) :
    h1MapOfAgreeOnSubgroup ρ ρ' U h (conjRep ρ U g x) = c • conjRep ρ' U g (h1MapOfAgreeOnSubgroup ρ ρ' U h x) := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  obtain ⟨z₁, e₁, f₁⟩ := sameH1_mk ρ ρ' U h z
  obtain ⟨z₂, e₂, f₂⟩ := conjU_mk ρ' U g z₁
  obtain ⟨z₃, e₃, f₃⟩ := conjU_mk ρ U g z
  obtain ⟨z₄, e₄, f₄⟩ := sameH1_mk ρ ρ' U h z₃
  rw [conjRep_apply, conjRep_apply, e₁, e₂, e₃, e₄, ← Submodule.Quotient.mk_smul]
  congr 1
  refine Subtype.ext (funext fun u => ?_)
  show z₄.1 u = c • z₂.1 u
  rw [f₄, f₃, f₂, f₁, hg]

end

theorem UpperTheory.V.Base.selTwist :
    ∀ (R G M : Type) [CommRing R] [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup M] [Module R M]
      [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul R M] [DiscreteTopology M] (ρ : Representation R G M) (ρ' : Representation R G M) (θ : G →* Rˣ), (∀ g m, ρ g m = ((θ g : Rˣ) : R) • ρ' g m) →
      ∀ (U : Subgroup G) [U.Normal], (∀ u ∈ U, θ u = 1) → ∀ (𝒟 : Set (Subgroup G)) (h𝒟 : ConjStable 𝒟),
      (∃ Φ : LocSel ρ U 𝒟 ≃ₗ[R] LocSel ρ' U 𝒟, ∀ g x, Φ (selRep ρ U h𝒟 g x) = ((θ g : Rˣ) : R) • selRep ρ' U h𝒟 g (Φ x)) ∧
      ∀ (W : Subgroup G) (φ : W →* Rˣ), Module.length R (selEig ρ U h𝒟 W (θ.comp W.subtype * φ)) = Module.length R (selEig ρ' U h𝒟 W φ) := by
  intro R G M _ _ _ _ _ _ _ _ _ _ ρ ρ' θ hθ U _ hU 𝒟 h𝒟
  have h : ∀ (u : U) m, ρ u m = ρ' u m := fun u m => by
    rw [hθ, hU u u.2, Units.val_one, one_smul]
  have hΦ : ∀ g x, sameSel ρ ρ' U h 𝒟 (selRep ρ U h𝒟 g x) =
      ((θ g : Rˣ) : R) • selRep ρ' U h𝒟 g (sameSel ρ ρ' U h 𝒟 x) := fun g x =>
    Subtype.ext (sameH1_conjugation_scalar ρ ρ' U h g _ (hθ g) x.1)
  refine ⟨⟨_, hΦ⟩, fun W φ => ?_⟩
  generalize sameSel ρ ρ' U h 𝒟 = Φ at hΦ
  have key : ∀ x, x ∈ selEig ρ U h𝒟 W (θ.comp W.subtype * φ) ↔ Φ x ∈ selEig ρ' U h𝒟 W φ := by
    intro x
    rw [mem_eig, mem_eig]
    refine forall_congr' fun w => ?_
    show selRep ρ U h𝒟 w x = ((θ w * φ w : Rˣ) : R) • x ↔ selRep ρ' U h𝒟 w (Φ x) = ((φ w : Rˣ) : R) • Φ x
    rw [← Φ.injective.eq_iff, hΦ, map_smul, Units.val_mul, mul_smul]
    exact (Units.isUnit (θ w)).smul_left_cancel
  have hmap : (selEig ρ U h𝒟 W (θ.comp W.subtype * φ)).map (Φ : _ →ₗ[R] _) = selEig ρ' U h𝒟 W φ := by
    ext y
    obtain ⟨x, rfl⟩ := Φ.surjective y
    rw [← key]
    exact ⟨fun ⟨x', hx', e⟩ => Φ.injective e ▸ hx', fun hx => ⟨x, hx, rfl⟩⟩
  exact (Φ.ofSubmodules _ _ hmap).length_eq
end

section

open ReciprocityTheory.Gal UpperTheory.V.Base

section

variable {O Q N : Type} [CommRing O] [CommGroup Q] [Fintype Q] [AddCommGroup N] [Module O N]

private noncomputable def prj (π : Representation O Q N) (c : O) (ψ : Q →* Oˣ) : N →ₗ[O] N :=
  c • ∑ g : Q, ((ψ g⁻¹ : Oˣ) : O) • π g

private theorem prj_apply (π : Representation O Q N) (c : O) (ψ : Q →* Oˣ) (x : N) :
    prj π c ψ x = c • ∑ g : Q, ((ψ g⁻¹ : Oˣ) : O) • π g x := by
  simp only [prj, LinearMap.smul_apply, LinearMap.sum_apply]

private theorem prj_mem (π : Representation O Q N) (c : O) (ψ : Q →* Oˣ) (x : N) :
    prj π c ψ x ∈ eig π ψ := by
  rw [mem_eig]
  intro h

  rw [prj_apply, map_smul, smul_comm, map_sum, Finset.smul_sum (r := ((ψ h : Oˣ) : O))]
  congr 1
  refine Fintype.sum_equiv (Equiv.mulLeft h) _ _ fun g => ?_
  rw [map_smul, smul_smul, Equiv.coe_mulLeft, ← Units.val_mul, ← map_mul, map_mul π, Module.End.mul_apply]
  congr 3
  rw [mul_inv, mul_inv_cancel_left]

private theorem prj_act (π : Representation O Q N) (c : O) (ψ : Q →* Oˣ) (h : Q) (x : N) :
    prj π c ψ (π h x) = ((ψ h : Oˣ) : O) • prj π c ψ x := by

  rw [← mem_eig.1 (prj_mem π c ψ x) h, prj_apply, prj_apply, map_smul, map_sum]
  congr 1
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [map_smul, ← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, mul_comm]

private theorem prj_self (π : Representation O Q N) {c : O} (hc : c * (Fintype.card Q : O) = 1) (ψ : Q →* Oˣ)
    {x : N} (hx : x ∈ eig π ψ) : prj π c ψ x = x := by
  rw [prj_apply]
  have : ∀ g : Q, ((ψ g⁻¹ : Oˣ) : O) • π g x = x := fun g => by
    rw [mem_eig.1 hx, smul_smul, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one, one_smul]
  simp only [this]
  rw [Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul O, smul_smul, hc, one_smul]

private theorem prj_ne [IsDomain O] (π : Representation O Q N) (c : O) {ψ χ : Q →* Oˣ} (hne : ψ ≠ χ)
    {x : N} (hx : x ∈ eig π χ) : prj π c ψ x = 0 := by
  rw [prj_apply]
  have : ∀ g : Q, ((ψ g⁻¹ : Oˣ) : O) • π g x = ((Units.coeHom O).comp (ψ⁻¹ * χ) g) • x := fun g => by
    rw [mem_eig.1 hx, smul_smul]
    simp
  simp only [this]
  rw [← Finset.sum_smul, sum_hom_units_eq_zero, zero_smul, smul_zero]
  intro h
  apply hne
  ext g
  have h1 := DFunLike.congr_fun h g
  have h2 : (ψ g)⁻¹ * χ g = 1 := Units.ext (by simpa using h1)
  rw [inv_mul_eq_one.1 h2]

private theorem sub_prj_mem (π : Representation O Q N) {c : O} (hc : c * (Fintype.card Q : O) = 1) (ψ : Q →* Oˣ)
    (x : N) : prj π c ψ x - x ∈ coeig π ψ := by
  have hx : x = c • ∑ g : Q, ((ψ g⁻¹ : Oˣ) : O) • ((ψ g : Oˣ) : O) • x := by
    have : ∀ g : Q, ((ψ g⁻¹ : Oˣ) : O) • ((ψ g : Oˣ) : O) • x = x := fun g => by
      rw [smul_smul, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one, one_smul]
    simp only [this]
    rw [Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul O, smul_smul, hc, one_smul]
  have : prj π c ψ x - x = c • ∑ g : Q, ((ψ g⁻¹ : Oˣ) : O) • (π g x - ((ψ g : Oˣ) : O) • x) := by
    simp only [smul_sub, Finset.sum_sub_distrib]
    rw [← hx, prj_apply]
  rw [this]
  refine Submodule.smul_mem _ _ (Submodule.sum_mem _ fun g _ => Submodule.smul_mem _ _ ?_)
  exact Submodule.mem_iSup_of_mem g ⟨x, rfl⟩

private theorem sum_prj [IsDomain O] [HasEnoughRootsOfUnity O (Monoid.exponent Q)] [Fintype (Q →* Oˣ)]
    (π : Representation O Q N) {c : O} (hc : c * (Fintype.card Q : O) = 1) (x : N) :
    ∑ ψ : Q →* Oˣ, prj π c ψ x = x := by
  simp only [prj_apply]
  rw [← Finset.smul_sum, Finset.sum_comm, Finset.sum_eq_single (1 : Q)]
  · simp only [inv_one, map_one, Units.val_one, one_smul, Module.End.one_apply]
    rw [Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card,
      CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity, Nat.card_eq_fintype_card,
      ← Nat.cast_smul_eq_nsmul O, smul_smul, hc, one_smul]
  · intro g _ hg
    rw [← Finset.sum_smul]
    obtain ⟨φ, hφ⟩ := CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity Q O (inv_ne_one.2 hg)
    have := sum_hom_units_eq_zero ((Units.coeHom O).comp (MonoidHom.eval g⁻¹ : (Q →* Oˣ) →* Oˣ)) (by
      intro h
      exact hφ (Units.ext (DFunLike.congr_fun h φ)))
    have h2 : ∑ ψ : Q →* Oˣ, ((ψ g⁻¹ : Oˣ) : O) = 0 := this
    rw [h2, zero_smul]
  · simp

end

theorem UpperTheory.V.Base.lenEigEq :
    ∀ (O Q N : Type) [CommRing O] [IsDomain O] [CommGroup Q] [Finite Q] [HasEnoughRootsOfUnity O (Monoid.exponent Q)]
      [Fintype (Q →* Oˣ)] [AddCommGroup N] [Module O N] (π : Representation O Q N), IsUnit (Nat.card Q : O) →
      Module.length O N = ∑ ψ : Q →* Oˣ, Module.length O (eig π ψ) ∧ ∀ ψ : Q →* Oˣ, IsCompl (eig π ψ) (coeig π ψ) := by
  intro O Q N _ _ _ _ _ _ _ _ π hu
  classical
  letI := Fintype.ofFinite Q
  rw [Nat.card_eq_fintype_card] at hu
  obtain ⟨c, hc⟩ := hu.exists_left_inv
  refine ⟨?_, fun ψ => ⟨?_, ?_⟩⟩
  · rw [← Module.length_pi_of_fintype]
    let f : N →ₗ[O] (∀ ψ : Q →* Oˣ, eig π ψ) :=
      LinearMap.pi fun ψ => (prj π c ψ).codRestrict (eig π ψ) (prj_mem π c ψ)
    have hf : ∀ x ψ, ((f x ψ : eig π ψ) : N) = prj π c ψ x := fun _ _ => rfl
    refine (LinearEquiv.ofBijective f ⟨?_, ?_⟩).length_eq
    · intro x y hxy
      rw [← sum_prj π hc x, ← sum_prj π hc y]
      exact Finset.sum_congr rfl fun ψ _ => by rw [← hf, ← hf, hxy]
    · intro y
      refine ⟨∑ χ, (y χ : N), funext fun ψ => Subtype.ext ?_⟩

      rw [hf, map_sum, Finset.sum_eq_single ψ, prj_self π hc ψ (y ψ).2]
      · intro χ _ hχ
        exact prj_ne π c hχ.symm (y χ).2
      · simp
  · rw [Submodule.disjoint_def]
    intro x hx hy
    have hle : coeig π ψ ≤ LinearMap.ker (prj π c ψ) := by
      refine iSup_le fun g => ?_
      rintro _ ⟨z, rfl⟩
      simp [prj_act]
    rw [← prj_self π hc ψ hx]
    exact hle hy
  · rw [codisjoint_iff, eq_top_iff]
    intro x _
    have : x = prj π c ψ x - (prj π c ψ x - x) := by abel
    rw [this]
    exact Submodule.sub_mem _ (Submodule.mem_sup_left (prj_mem π c ψ x))
      (Submodule.mem_sup_right (sub_prj_mem π hc ψ x))
end
