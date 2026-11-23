module

public import GroundTheory.TateCohomology.CupProduct
public import GroundTheory.TateCohomology.CochainReverse
public import GroundTheory.TateCohomology.TateShapiro
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.RepresentationTheory.Coinduced
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.LongExactSequence
public import Mathlib.Topology.Instances.AddCircle.Defs
public import GroundTheory.TateCohomology.Bundle004
import GroundTheory.TateCohomology.Bundle003
import GroundTheory.TateCohomology.InducedNorm
public import GroundTheory.TateCohomology.TateLow
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
import Mathlib.RepresentationTheory.FiniteIndex
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.GroupCoh

open CategoryTheory Limits Rep

universe u

section Bijective

variable {k H K : Type u} [CommRing k] [Group H] [Group K] [Fintype H] [Fintype K]
  (f : H →* K) (hf : Function.Bijective f)

include hf

theorem norm_res_of_bijective (B : Rep.{u} k K) (m : B) :
    (res f B).ρ.norm m = B.ρ.norm m := by
  rw [Representation.norm, Representation.norm, LinearMap.sum_apply, LinearMap.sum_apply]
  exact Fintype.sum_bijective f hf _ _ fun _ => rfl

theorem isZero_tateCohomology_zero_res_iff (B : Rep.{u} k K) :
    IsZero (tateCohomology (res f B) 0) ↔ IsZero (tateCohomology B 0) := by
  rw [isZero_tateCohomology_zero_iff_forall, isZero_tateCohomology_zero_iff_forall]
  have hinv : ∀ x : B, x ∈ (res f B).ρ.invariants ↔ x ∈ B.ρ.invariants := fun x => by
    simp only [Representation.mem_invariants]
    constructor
    · intro h g
      obtain ⟨h', rfl⟩ := hf.2 g
      exact h h'
    · intro h h'
      exact h (f h')
  constructor
  · intro h x hx
    obtain ⟨m, hm⟩ := h x ((hinv x).2 hx)
    exact ⟨m, by rw [← norm_res_of_bijective f hf]; exact hm⟩
  · intro h x hx
    obtain ⟨m, hm⟩ := h x ((hinv x).1 hx)
    exact ⟨m, by rw [norm_res_of_bijective f hf]; exact hm⟩

theorem tateAcyclic_res_of_sum_eq (B : Rep.{u} k K) (φ : B.V →ₗ[k] B.V)
    (hφ : ∀ m : B, ∑ g : K, B.ρ g (φ (B.ρ g⁻¹ m)) = m) : TateAcyclic (res f B) :=
  tateAcyclic_of_sum_eq (res f B) φ fun m => by
    conv_rhs => rw [← hφ m]
    exact Fintype.sum_bijective f hf _ _ fun h => by
      simp only [MonoidHom.comp_apply, map_inv]

theorem isZero_tateCohomology_res_iff (n : ℤ) (B : Rep.{u} k K) :
    IsZero (tateCohomology (res f B) n) ↔ IsZero (tateCohomology B n) := by
  refine Int.inductionOn' (motive := fun n => ∀ B : Rep.{u} k K,
    IsZero (tateCohomology (res f B) n) ↔ IsZero (tateCohomology B n)) n 0
    (fun B => isZero_tateCohomology_zero_res_iff f hf B) ?_ ?_ B
  · intro n _ ih B
    have hX' : ((coindSES.obj B).map (resFunctor f)).ShortExact :=
      (shortExact_res f).2 (coindSES_shortExact B)
    have h2 : TateAcyclic ((coindSES.obj B).map (resFunctor f)).X₂ := by
      rw [ShortComplex.map_X₂, coindSES_obj_X₂]
      exact tateAcyclic_res_of_sum_eq f hf _ (coindBotProj _) (sum_coindBotProj _)
    have e1 := @asIso _ _ _ _ (TateCohomology.δ hX' n) (isIso_δ_of_tateAcyclic hX' h2 n)
    rw [ShortComplex.map_X₃, ShortComplex.map_X₁, coindSES_obj_X₁] at e1
    rw [← e1.isZero_iff, ← (coindShiftIso B n).isZero_iff]
    exact ih _
  · intro n _ ih B
    have hX' : ((indSES.obj B).map (resFunctor f)).ShortExact :=
      (shortExact_res f).2 (indSES_shortExact B)
    have h2 : TateAcyclic ((indSES.obj B).map (resFunctor f)).X₂ := by
      classical
      rw [ShortComplex.map_X₂, indSES_obj_X₂]
      exact (tateAcyclic_res_of_sum_eq f hf _ (coindBotProj _) (sum_coindBotProj _)).of_iso
        ((resFunctor f).mapIso (indCoindIso _))
    have e1 := @asIso _ _ _ _ (TateCohomology.δ hX' (n - 1))
      (isIso_δ_of_tateAcyclic hX' h2 (n - 1))
    rw [ShortComplex.map_X₃, ShortComplex.map_X₁, indSES_obj_X₃] at e1
    rw [e1.isZero_iff, (indShiftIso B (n - 1)).isZero_iff, sub_add_cancel]
    exact ih _

theorem tateAcyclic_res_iff (B : Rep.{u} k K) : TateAcyclic (res f B) ↔ TateAcyclic B :=
  forall_congr' fun n => isZero_tateCohomology_res_iff f hf n B

end Bijective

section Consequences

variable {k G : Type u} [CommRing k] [Group G]


omit [Group G] in
theorem res_res {H K : Type u} [Group H] [Group K] [Group G] (f : H →* K) (g : K →* G)
    (A : Rep.{u} k G) : res f (res g A) = res (g.comp f) A :=
  rfl

theorem CohTrivial.tateAcyclic [Fintype G] {A : Rep.{u} k G} (h : CohTrivial A) :
    TateAcyclic A := by
  let _ : Fintype (⊤ : Subgroup G) := Fintype.ofFinite _
  have hbij : Function.Bijective (⊤ : Subgroup G).subtype :=
    ⟨Subgroup.subtype_injective _, fun g => ⟨⟨g, Subgroup.mem_top g⟩, rfl⟩⟩
  have h1 : TateAcyclic (res (⊤ : Subgroup G).subtype A) := h ⊤
  exact (tateAcyclic_res_iff _ hbij A).1 h1

theorem tateAcyclic_res_conj {A : Rep.{u} k G} (U V : Subgroup G) [Fintype U] [Fintype V] (g : G)
    (hUV : ∀ x, x ∈ U ↔ g⁻¹ * x * g ∈ V) (hV : TateAcyclic (res V.subtype A)) :
    TateAcyclic (res U.subtype A) := by
  let c : U →* V :=
    { toFun := fun u => ⟨g⁻¹ * u * g, (hUV u).1 u.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by simp [mul_assoc]) }
  have hinj : Function.Injective c := fun a b hab => by
    have h := congrArg (fun x : V => (x : G)) hab
    simp only [c, MonoidHom.coe_mk, OneHom.coe_mk, mul_left_inj, mul_right_inj] at h
    exact Subtype.ext h
  have hsurj : Function.Surjective c := fun v =>
    ⟨⟨g * v * g⁻¹, (hUV _).2 (by simp [mul_assoc])⟩, Subtype.ext (by simp [c, mul_assoc])⟩
  have hc := (tateAcyclic_res_iff c ⟨hinj, hsurj⟩ (res V.subtype A)).2 hV
  let e : A.V ≃ₗ[k] A.V := LinearEquiv.ofLinearMap (A.ρ g⁻¹) (A.ρ g)
    (LinearMap.ext fun a => by simp) (LinearMap.ext fun a => by simp)
  let eqv : (res U.subtype A).ρ.Equiv (res c (res V.subtype A)).ρ :=
    Representation.Equiv.mk e fun u => LinearMap.ext fun a => by
      change A.ρ g⁻¹ (A.ρ u a) = A.ρ (g⁻¹ * u * g) (A.ρ g⁻¹ a)
      rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul, mul_assoc,
        mul_inv_cancel, mul_one]
  exact hc.of_iso (Rep.mkIso eqv)

end Consequences

end GroundTheory.GroupCoh
end

section

set_option maxSynthPendingDepth 1

noncomputable section

universe u

open CategoryTheory MonoidalCategory TensorProduct groupCohomology

namespace GroundTheory.GroupCoh

variable {k G : Type u} [CommRing k] [Group G] {A B : Rep k G} {p q n : ℕ}

theorem braiding_hom_tmul (X Y : Rep k G) (a : X) (b : Y) :
    (β_ X Y).hom.hom ((a ⊗ₜ[k] b : (X ⊗ Y : Rep k G))) = b ⊗ₜ[k] a :=
  rfl

theorem revCochain_cupCochain (h : p + q = n) (h' : q + p = n) (f : (Fin p → G) → A)
    (g : (Fin q → G) → B) (x : Fin n → G) :
    revCochain n (cupCochain h f g) x =
      (-1 : k) ^ (p * q) • (β_ B A).hom.hom (cupCochain h' (revCochain q g) (revCochain p f) x) := by
  subst h'
  have hpre : (fun i : Fin p => revInv x ⟨i, by omega⟩) =
      revInv (fun j : Fin p => x ⟨q + j, by omega⟩) := by
    funext i
    simp only [revInv_apply]
    congr 2
    ext
    simp only [Fin.val_rev]
    omega
  have hsuf : (fun j : Fin q => revInv x ⟨p + j, by omega⟩) =
      revInv (fun i : Fin q => x ⟨i, by omega⟩) := by
    funext j
    simp only [revInv_apply]
    congr 2
    ext
    simp only [Fin.val_rev]
    omega
  have hP₁ : Fin.partialProd (revInv x) ⟨p, by omega⟩ =
      (Fin.partialProd (fun j : Fin p => x ⟨q + j, by omega⟩) (Fin.last p))⁻¹ := by
    rw [← partialProd_prefix (revInv x) (m := p) (by omega) le_rfl, hpre, ← partialProd_last_revInv]
    rfl
  have hP : Fin.partialProd x (Fin.last (q + p)) =
      Fin.partialProd (fun i : Fin q => x ⟨i, by omega⟩) (Fin.last q) *
        Fin.partialProd (fun j : Fin p => x ⟨q + j, by omega⟩) (Fin.last p) := by
    have := partialProd_add x (fun j : Fin p => x ⟨q + j, by omega⟩) (p := q) (q := p)
      le_rfl (fun _ => rfl) le_rfl
    rw [← partialProd_prefix x (m := q) (by omega) le_rfl] at this
    exact this
  have hP₂ : Fin.partialProd x ⟨q, by omega⟩ =
      Fin.partialProd (fun i : Fin q => x ⟨i, by omega⟩) (Fin.last q) :=
    (partialProd_prefix x (m := q) (by omega) le_rfl).symm
  rw [revCochain_apply, cupCochain_apply, cupCochain_apply, revCochain_apply, revCochain_apply,
    hpre, hsuf, hP₁, hP₂, map_smul, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul, smul_smul,
    map_smul, braiding_hom_tmul, tensor_ρ_tmul, ← Module.End.mul_apply, ← map_mul,
    ← Module.End.mul_apply, ← map_mul, hP, mul_inv_cancel_right, smul_smul, ← pow_add, ← pow_add,
    triangle_add]
  congr 2
  ring

theorem cupH_eq_neg_one_pow_smul_map_braiding (h : p + q = n) (h' : q + p = n)
    (x : groupCohomology A p) (y : groupCohomology B q) :
    cupH h x y = (-1 : k) ^ (p * q) • map (MonoidHom.id G) (β_ B A).hom n (cupH h' y x) := by
  refine groupCohomology_induction_on x fun z => ?_
  refine groupCohomology_induction_on y fun w => ?_
  have key : HomologicalComplex.cyclesMap (revHom (A ⊗ B)) n (cupCocycles h z w) =
      (-1 : k) ^ (p * q) • cocyclesMap (MonoidHom.id G) (β_ B A).hom n
        (cupCocycles h' (HomologicalComplex.cyclesMap (revHom B) q w)
          (HomologicalComplex.cyclesMap (revHom A) p z)) := by
    refine cocycles_ext ?_
    rw [iCocycles_cyclesMap_revHom, map_smul, iCocycles_cocyclesMap, iCocycles_cupCocycles]
    erw [iCocycles_cupCocycles]
    rw [iCocycles_cyclesMap_revHom, iCocycles_cyclesMap_revHom]
    funext x
    exact revCochain_cupCochain h h' _ _ x
  rw [cupH_π, ← π_cyclesMap_revHom (cupCocycles h z w), key, map_smul, ← map_π_apply]
  erw [← cupH_π]
  rw [π_cyclesMap_revHom, π_cyclesMap_revHom]

theorem map_braiding_cupH (h : p + q = n) (h' : q + p = n) (x : groupCohomology A p)
    (y : groupCohomology B q) :
    map (MonoidHom.id G) (β_ A B).hom n (cupH h x y) = (-1 : k) ^ (p * q) • cupH h' y x := by
  rw [cupH_eq_neg_one_pow_smul_map_braiding h' h y x, smul_smul, ← pow_add, mul_comm q p,
    ← two_mul, pow_mul, neg_one_sq, one_pow, one_smul]

end GroundTheory.GroupCoh
end
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.GroupCoh

open CategoryTheory Limits Rep

universe u

variable {k G : Type u} [CommRing k] [Group G] [Fintype G] (S : Subgroup G) [Fintype S]


section Res

noncomputable def tateRes (n : ℤ) :
    tateCohomologyFunctor (R := k) (G := G) n ⟶
      resFunctor S.subtype ⋙ tateCohomologyFunctor (R := k) (G := S) n :=
  (Functor.leftUnitor _).inv ≫
    Functor.whiskerRight (Rep.resCoindAdjunction.{u, u} k S.subtype).unit _ ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft (resFunctor S.subtype) (tateCoindNatIso S n).hom

lemma tateRes_app (n : ℤ) (A : Rep.{u} k G) :
    (tateRes S n).app A =
      (tateCohomologyFunctor n).map ((Rep.resCoindAdjunction.{u, u} k S.subtype).unit.app A) ≫
        (tateCoindIso S (res S.subtype A) n).hom := by
  simp only [tateRes, NatTrans.comp_app, Functor.leftUnitor_inv_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.whiskerLeft_app, Category.id_comp]
  rfl

end Res

section Cores


open scoped Classical in
noncomputable def tateCores (n : ℤ) :
    resFunctor S.subtype ⋙ tateCohomologyFunctor (R := k) (G := S) n ⟶
      tateCohomologyFunctor (R := k) (G := G) n :=
  Functor.whiskerLeft (resFunctor S.subtype) (tateIndNatIso S n).inv ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight (Rep.indResAdjunction.{u} k S.subtype).counit _ ≫
    (Functor.leftUnitor _).hom

lemma tateCores_app (n : ℤ) (A : Rep.{u} k G) :
    (tateCores S n).app A =
      (tateIndIso S (res S.subtype A) n).inv ≫
        (tateCohomologyFunctor n).map ((Rep.indResAdjunction.{u} k S.subtype).counit.app A) := by
  simp only [tateCores, NatTrans.comp_app, Functor.leftUnitor_hom_app, Functor.whiskerRight_app,
    Functor.associator_inv_app, Functor.whiskerLeft_app, Category.id_comp]
  rfl

end Cores

end GroundTheory.GroupCoh
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.GroupCoh

open CategoryTheory Limits Rep groupCohomology

section Exactness

universe u

variable {k G : Type u} [CommRing k] [Group G]

theorem shortComplex_exact_of_forall {S : ShortComplex (Rep.{u} k G)}
    (h : ∀ x : S.X₂, S.g.hom x = 0 → ∃ y : S.X₁, S.f.hom y = x) : S.Exact := by
  rw [← ShortComplex.exact_map_iff_of_faithful _ (forget₂ (Rep.{u} k G) (ModuleCat.{u} k)),
    ShortComplex.moduleCat_exact_iff]
  exact h

end Exactness

section Sequence

variable (G : Type) [Group G]

noncomputable def intToRat : Rep.trivial ℤ G ℤ ⟶ Rep.trivial ℤ G ℚ :=
  Rep.ofHom ⟨(Int.castAddHom ℚ).toIntLinearMap, fun _ => rfl⟩

noncomputable def ratToRatModInt : Rep.trivial ℤ G ℚ ⟶ Rep.trivial ℤ G (AddCircle (1 : ℚ)) :=
  Rep.ofHom ⟨(QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℚ))).toIntLinearMap, fun _ => rfl⟩

noncomputable def ratSES : ShortComplex (Rep.{0} ℤ G) :=
  ShortComplex.mk (intToRat G) (ratToRatModInt G) (by
    refine Rep.hom_ext (Representation.IntertwiningMap.ext (LinearMap.ext fun n => ?_))
    change ((n : ℚ) : AddCircle (1 : ℚ)) = 0
    rw [AddCircle.coe_eq_zero_iff]
    exact ⟨n, by simp⟩)

theorem ratSES_shortExact : (ratSES G).ShortExact := by
  refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
  · refine shortComplex_exact_of_forall fun q hq => ?_
    have hq' : ((show ℚ from q) : AddCircle (1 : ℚ)) = 0 := hq
    obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff _).1 hq'
    exact ⟨n, by change ((n : ℤ) : ℚ) = (show ℚ from q); rw [← hn, zsmul_one]⟩
  · exact (Rep.mono_iff_injective (intToRat G)).2 (Int.cast_injective (α := ℚ))
  · exact (Rep.epi_iff_surjective (ratToRatModInt G)).2 QuotientAddGroup.mk_surjective

end Sequence

section H2

variable (G : Type) [Group G] [Fintype G]

noncomputable def h1RatModIntIso :
    H1 (Rep.trivial ℤ G (AddCircle (1 : ℚ))) ≅ ModuleCat.of ℤ (Additive G →+ AddCircle (1 : ℚ)) :=
  H1IsoOfIsTrivial _


omit [Fintype G] in
theorem h1RatModIntIso_inv_apply (χ : Additive G →+ AddCircle (1 : ℚ)) :
    (h1RatModIntIso G).inv χ =
      H1π _ ((cocycles₁IsoOfIsTrivial (Rep.trivial ℤ G (AddCircle (1 : ℚ)))).inv χ) :=
  rfl

theorem isIso_δ_ratSES : IsIso (groupCohomology.δ (ratSES_shortExact G) 1 2 rfl) :=
  isIso_δ_of_isZero (ratSES_shortExact G) 1 (isZero_groupCohomology_trivial_rat 1)
    (isZero_groupCohomology_trivial_rat 2)

noncomputable def h1RatModIntIsoH2Int :
    H1 (Rep.trivial ℤ G (AddCircle (1 : ℚ))) ≅ H2 (Rep.trivial ℤ G ℤ) :=
  @asIso _ _ _ _ (groupCohomology.δ (ratSES_shortExact G) 1 2 rfl) (isIso_δ_ratSES G)

noncomputable def h2IntIsoHom :
    H2 (Rep.trivial ℤ G ℤ) ≅ ModuleCat.of ℤ (Additive G →+ AddCircle (1 : ℚ)) :=
  (h1RatModIntIsoH2Int G).symm ≪≫ h1RatModIntIso G

noncomputable def h2IntAddEquiv :
    H2 (Rep.trivial ℤ G ℤ) ≃+ (Additive G →+ AddCircle (1 : ℚ)) :=
  (h2IntIsoHom G).toLinearEquiv.toAddEquiv

theorem h2IntAddEquiv_symm_apply (χ : Additive G →+ AddCircle (1 : ℚ)) :
    (h2IntAddEquiv G).symm χ =
      groupCohomology.δ (ratSES_shortExact G) 1 2 rfl ((h1RatModIntIso G).inv χ) :=
  rfl

theorem h2IntAddEquiv_symm_apply_eq_H2_class (χ : Additive G →+ AddCircle (1 : ℚ)) (y : G → ℚ)
    (hy : ∀ g : G, (y g : AddCircle (1 : ℚ)) = χ (Additive.ofMul g)) (x : G × G → ℤ)
    (hx : ∀ g h : G, (x (g, h) : ℚ) = y g + y h - y (g * h)) :
    ∃ hc : x ∈ cocycles₂ (Rep.trivial ℤ G ℤ),
      (h2IntAddEquiv G).symm χ = H2π (Rep.trivial ℤ G ℤ) ⟨x, hc⟩ := by
  have hfx : (ratSES G).f.hom ∘ x = d₁₂ (ratSES G).X₂ y := by
    funext p
    change ((x p : ℤ) : ℚ) = y p.2 - y (p.1 * p.2) + y p.1
    rw [hx]; ring
  refine ⟨mem_cocycles₂_of_comp_eq_d₁₂ (ratSES_shortExact G) hfx, ?_⟩
  rw [h2IntAddEquiv_symm_apply, h1RatModIntIso_inv_apply]
  refine δ₁_apply (ratSES_shortExact G)
    ((cocycles₁IsoOfIsTrivial (Rep.trivial ℤ G (AddCircle (1 : ℚ)))).inv χ) y ?_ x hfx
  funext g
  change ((y g : ℚ) : AddCircle (1 : ℚ)) = χ (Additive.ofMul g)
  exact hy g

end H2

section Cyclic

variable {G : Type} [Group G] [Fintype G] (σ : G) (hσ : ∀ g : G, g ∈ Subgroup.zpowers σ)



include hσ in
theorem orderOf_ofAdd_div_card_dvd :
    orderOf (Multiplicative.ofAdd (((1 : ℚ) / Nat.card G : ℚ) : AddCircle (1 : ℚ))) ∣
      orderOf σ := by
  have : Fact ((0 : ℚ) < 1) := ⟨one_pos⟩
  rw [orderOf_ofAdd_eq_addOrderOf, AddCircle.addOrderOf_period_div Nat.card_pos,
    orderOf_eq_card_of_forall_mem_zpowers hσ]

noncomputable def cyclicChar : Additive G →+ AddCircle (1 : ℚ) :=
  MonoidHom.toAdditiveLeft (monoidHomOfForallMemZpowers hσ (orderOf_ofAdd_div_card_dvd σ hσ))

theorem cyclicChar_apply_gen :
    cyclicChar σ hσ (Additive.ofMul σ) = (((1 : ℚ) / Nat.card G : ℚ) : AddCircle (1 : ℚ)) := by
  change Multiplicative.toAdd
    (monoidHomOfForallMemZpowers hσ (orderOf_ofAdd_div_card_dvd σ hσ) σ) = _
  rw [monoidHomOfForallMemZpowers_apply_gen]
  rfl


end Cyclic

end GroundTheory.GroupCoh
end
