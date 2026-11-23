module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.HomologyRank.RankHomology
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle105
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle239
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.KLevTop
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IdeleClassFiniteness.LatticeIdealNonzero
public import Formalism.SharpRestriction.CuspSpanNormBounds.BridgeLevelGenB
import GroundTheory.GlobalFields.Adele.Bundle003
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Shapiro
import Mathlib.RingTheory.Radical.NatInt
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

@[expose] public section

section

open TensorProduct Module GlobalTheory.Pst GlobalTheory.Pst.DpstMap in
theorem UpperTheory.weilDeligne_functor_exact :
    UpperTheory.V.Af.Wd.LetterExact := by
  intro LL U D' D D'' F _ _ _ _ _ _ _ _ _ _ m' m m'' τ T S hT hS hex hsurj
  have hS' : Function.Surjective (S.baseChange F) := LinearMap.lTensor_surjective F hsurj
  have hex' : Function.Exact (T.baseChange F) (S.baseChange F) := lTensor_exact F hex hsurj
  have eT : ∀ y, letterLin m' m F τ T hT (letterQ m' F τ y) = letterQ m F τ (T.baseChange F y) := fun _ => rfl
  have eS : ∀ y, letterLin m m'' F τ S hS (letterQ m F τ y) = letterQ m'' F τ (S.baseChange F y) := fun _ => rfl
  have hker : letterKer m'' F τ ≤ (letterKer m F τ).map (S.baseChange F) := iSup_le fun c => by
    rintro _ ⟨y, rfl⟩
    obtain ⟨y, rfl⟩ := hS' y
    refine ⟨_, Submodule.mem_iSup_of_mem c ⟨y, rfl⟩, ?_⟩
    have := LinearMap.congr_fun (congrArg (LinearMap.baseChange F) (hS c)) y
    rw [LinearMap.baseChange_comp, LinearMap.baseChange_comp, LinearMap.comp_apply, LinearMap.comp_apply] at this
    simp [this]
  refine ⟨fun y => ?_, fun y => ?_⟩
  · obtain ⟨y, rfl⟩ := letterQ_surjective m F τ y
    constructor
    · intro h
      rw [eS, ← LinearMap.mem_ker, ker_letterQ] at h
      obtain ⟨z, hz, hzy⟩ := hker h
      obtain ⟨w, hw⟩ := (hex' (y - z)).mp (by rw [map_sub, hzy, sub_self])
      refine ⟨letterQ m' F τ w, ?_⟩
      have hz0 : letterQ m F τ z = 0 := by
        rw [← LinearMap.mem_ker, ker_letterQ]; exact hz
      rw [eT, hw, map_sub, hz0, sub_zero]
    · rintro ⟨w, hw⟩
      obtain ⟨w, rfl⟩ := letterQ_surjective m' F τ w
      rw [← hw, eT, eS, hex'.apply_apply_eq_zero, map_zero]
  · obtain ⟨y, rfl⟩ := letterQ_surjective m'' F τ y
    obtain ⟨y, rfl⟩ := hS' y
    exact ⟨letterQ m F τ y, eS y⟩
end

section

open scoped Matrix in
theorem UpperTheory.cohomology_to_coinvariants_surjective :
    UpperTheory.V.Af.CohB.ToCoSurj := by
  intro Γ X Y _ _ _ p hp y h d ξ F
  choose c hc using h
  have hm : ∀ x, c x • x ∈ UpperTheory.V.Af.CohB.fib p hp y := fun x => by
    change p (c x • x) = y
    rw [hp, hc]
  have key : ∀ (g g' : Γ) (z z' : ↥(UpperTheory.V.Af.CohB.fib p hp y)), g⁻¹ • z.1 = g'⁻¹ • z'.1 →
      ξ g *ᵥ (ξ g'⁻¹ *ᵥ F.1 g' z') = F.1 g z := by
    intro g g' z z' hz
    have hz' : z.1 = (g * g'⁻¹) • z'.1 := by rw [mul_smul, ← hz, smul_inv_smul]
    have hs : g * g'⁻¹ ∈ MulAction.stabilizer Γ y := by
      have h1 : p z.1 = y := z.2
      have h2 : p z'.1 = y := z'.2
      rw [hz', hp, h2] at h1
      exact h1
    have h3 := congrFun (F.2 ⟨_, hs⟩ g') z
    have h4 : (⟨_, hs⟩ : ↥(MulAction.stabilizer Γ y))⁻¹ • z = z' := by
      apply Subtype.ext
      change (g * g'⁻¹)⁻¹ • z.1 = z'.1
      rw [hz', inv_smul_smul]
    change F.1 (g * g'⁻¹ * g') z = ξ (g * g'⁻¹) *ᵥ F.1 g' ((⟨_, hs⟩ : ↥(MulAction.stabilizer Γ y))⁻¹ • z) at h3
    rw [h4, inv_mul_cancel_right] at h3
    rw [h3, map_mul, Matrix.mulVec_mulVec]
  refine ⟨fun x => ξ (c x)⁻¹ *ᵥ F.1 (c x) ⟨c x • x, hm x⟩, ?_⟩
  apply Subtype.ext
  funext g z
  rw [UpperTheory.V.Af.CohB.toCo_apply]
  exact key g _ z _ (by simp)
end

section

theorem UpperTheory.orbit_bound_of_shapiro_functorial :
    UpperTheory.V.Af.CohB.ShapiroFun → UpperTheory.V.Af.CohB.OrbBound := by
  intro h Γ Y _ _ y hB
  obtain ⟨c, hc⟩ := hB
  refine ⟨c, ?_⟩
  intro X _ p hp hsurj D hD d ξ
  rw [h Γ X Y p hp y hsurj d ξ]
  refine (hc _).trans ?_
  have h1 : Cardinal.mk ↥(UpperTheory.V.Af.CohB.fib p hp y) ≤ D := hD
  have hfin : Finite ↥(UpperTheory.V.Af.CohB.fib p hp y) :=
    Cardinal.lt_aleph0_iff_finite.mp (h1.trans_lt Cardinal.natCast_lt_aleph0)
  have hr : Module.rank ℂ ↑(Rep.of (UpperTheory.V.Af.CohB.fibRep p hp y ξ)) =
      Cardinal.mk ↥(UpperTheory.V.Af.CohB.fib p hp y) * d := by
    change Module.rank ℂ (↥(UpperTheory.V.Af.CohB.fib p hp y) → Fin d → ℂ) = _
    rw [rank_pi]
    simp only [rank_fun', Fintype.card_fin]
    rw [Cardinal.sum_const']
  rw [hr]
  push_cast
  rw [mul_assoc]
  gcongr
end

section

private theorem card_sum_finset_swap {I : Type} (s : Finset I) (f : ℕ → I → Cardinal.{0}) :
    (Cardinal.sum fun q => ∑ i ∈ s, f q i) = ∑ i ∈ s, Cardinal.sum fun q => f q i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    rw [Cardinal.sum_add_distrib', ih]

theorem UpperTheory.cohomology_part_bound_of_sum_bound :
    UpperTheory.V.Af.CohB.SumBound → UpperTheory.V.Af.CohB.PartSplit → UpperTheory.V.Af.CohB.PartBound := by
  intro h1 h2 Γ X I _ _ _ c hc d ξ
  obtain ⟨π, ι, h⟩ := h2 Γ X I c hc d ξ
  unfold UpperTheory.V.Af.CohB.totCoh
  rw [← card_sum_finset_swap]
  exact Cardinal.sum_le_sum _ _ fun q => h1 Γ I _ _ π ι h q
end

section

open CategoryTheory UpperTheory.V.Af.CohB

theorem UpperTheory.cohomology_part_split :
    UpperTheory.V.Af.CohB.PartSplit := by
  classical
  intro Γ X I _ _ _ c hc d ξ
  let p : ∀ i, (X → Fin d → ℂ) →ₗ[ℂ] (↥(part c hc i) → Fin d → ℂ) := fun i =>
    { toFun := fun f x => f x.1
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let e : ∀ i, (↥(part c hc i) → Fin d → ℂ) →ₗ[ℂ] (X → Fin d → ℂ) := fun i =>
    { toFun := fun f x => if h : c x = i then f ⟨x, h⟩ else 0
      map_add' := fun f g => funext fun x => by
        by_cases h : c x = i <;> simp [h]
      map_smul' := fun a f => funext fun x => by
        by_cases h : c x = i <;> simp [h] }
  refine ⟨fun i => Rep.ofHom ⟨p i, fun γ => ?_⟩, fun i => Rep.ofHom ⟨e i, fun γ => ?_⟩, ?_⟩
  · refine LinearMap.ext fun f => funext fun x => ?_
    rfl
  · refine LinearMap.ext fun f => funext fun x => ?_
    change (if h : c x = i then (funRep ↥(part c hc i) ξ γ f) ⟨x, h⟩ else 0) =
      Matrix.mulVec (ξ γ) (if h : c (γ⁻¹ • x) = i then f ⟨γ⁻¹ • x, h⟩ else 0)
    by_cases h : c x = i
    · rw [dite_eq_left h, dite_eq_left ((hc _ _).trans h)]
      rfl
    · rw [dite_eq_right h, dite_eq_right (fun h' => h ((hc _ _).symm.trans h')), Matrix.mulVec_zero]
  · apply Rep.hom_ext
    rw [Rep.sum_hom]
    apply Representation.IntertwiningMap.ext
    refine LinearMap.ext fun f => funext fun x => ?_
    rw [Representation.IntertwiningMap.toLinearMap_sum, LinearMap.sum_apply, Finset.sum_apply]
    change ∑ i, (if h : c x = i then f x else 0) = f x
    simp
end

section

open CategoryTheory UpperTheory.V.Af.CohB in
theorem UpperTheory.shapiro_functorial_of_coinduction_bijective :
    UpperTheory.V.Af.CohB.ToCoInj → UpperTheory.V.Af.CohB.ToCoSurj → UpperTheory.V.Af.CohB.ShapiroFun := by
  intro hi hs Γ X Y _ _ _ p hp y hy d ξ
  let e := LinearEquiv.ofBijective (toCo p hp y ξ) ⟨hi Γ X Y p hp y hy d ξ, hs Γ X Y p hp y hy d ξ⟩
  have he : ∀ g : Γ, e.toLinearMap ∘ₗ funRep X ξ g =
      Representation.coind (MulAction.stabilizer Γ y).subtype (fibRep p hp y ξ) g ∘ₗ e.toLinearMap := by
    intro g
    refine LinearMap.ext fun f => Subtype.ext (funext fun h => funext fun x => ?_)
    change funRep X ξ h (funRep X ξ g f) x.1 = funRep X ξ (h * g) f x.1
    rw [map_mul]
    rfl
  let i : Rep.of (funRep X ξ) ≅ Rep.coind (MulAction.stabilizer Γ y).subtype (Rep.of (fibRep p hp y ξ)) :=
    Rep.mkIso (Representation.Equiv.mk e he)
  unfold totCoh
  congr 1
  funext q
  exact (((groupCohomology.functor ℂ Γ q).mapIso i) ≪≫
    groupCohomology.coindIso (Rep.of (fibRep p hp y ξ)) q).toLinearEquiv.rank_eq
end

section

open NumberField IsDedekindDomain GlobalTheory.CuspRep UpperTheory.V.Af

private theorem alg_mem_Ohat {F : Type} [Field F] [NumberField F] (x : F) :
    algebraMap F (Af F) x ∈ Ohat F ↔ ∃ r : 𝓞 F, (r : F) = x := by
  rw [← GlobalTheory.AdelicMatLat.algebraMap_mem_iff, GlobalTheory.AdelicMatLat.mem_intAdeles, Ohat, Subring.mem_iInf]
  rfl

theorem UpperTheory.arithmetic_subgroup_level_one :
    UpperTheory.V.Af.CohB.ArithOne := by
  intro F _ _ n
  ext g
  rw [Subgroup.mem_comap, mem_KLev]
  constructor
  · rintro ⟨ha, hb, -⟩
    rw [← map_inv] at hb
    have ha' : ∀ a b, ∃ r : 𝓞 F, (r : F) = g a b := fun a b => (alg_mem_Ohat _).1 (ha a b)
    have hb' : ∀ a b, ∃ r : 𝓞 F, (r : F) = (g⁻¹ : GL (Fin n) F) a b := fun a b => (alg_mem_Ohat _).1 (hb a b)
    choose A hA using ha'
    choose B hB using hb'
    have inj : Function.Injective (RingHom.mapMatrix (m := Fin n) (algebraMap (𝓞 F) F)) := fun x y h =>
      Matrix.ext fun a b => IsFractionRing.injective (𝓞 F) F (congrFun (congrFun h a) b)
    have eA : RingHom.mapMatrix (m := Fin n) (algebraMap (𝓞 F) F) (Matrix.of A) = g.val :=
      Matrix.ext fun a b => hA a b
    have eB : RingHom.mapMatrix (m := Fin n) (algebraMap (𝓞 F) F) (Matrix.of B) = (g⁻¹).val :=
      Matrix.ext fun a b => hB a b
    refine ⟨⟨Matrix.of A, Matrix.of B, inj ?_, inj ?_⟩, Units.ext eA⟩
    · rw [map_mul, map_one, eA, eB]; exact g.mul_inv
    · rw [map_mul, map_one, eA, eB]; exact g.inv_mul
  · rintro ⟨k, rfl⟩
    have h1 : ∀ (k : GL (Fin n) (𝓞 F)) a b, (CohB.ratAf F n
        (Matrix.GeneralLinearGroup.map (n := Fin n) (algebraMap (𝓞 F) F) k)) a b ∈ Ohat F :=
      fun k a b => (alg_mem_Ohat _).2 ⟨k a b, rfl⟩
    refine ⟨h1 k, fun a b => ?_, fun a b => ⟨_, ?_, by rw [Nat.cast_one]; exact (one_mul _).symm⟩⟩
    · rw [← map_inv, ← map_inv]; exact h1 _ a b
    · refine sub_mem (h1 k a b) ?_
      rw [Matrix.one_apply]; split_ifs
      · exact one_mem _
      · exact zero_mem _
end

section

open NumberField IsDedekindDomain GlobalTheory.CuspRep

private theorem ohat_of {F : Type} [Field F] [NumberField F] {x : Af F} (hx : x ∈ PIW.ClassFinD.Ohat F) :
    x ∈ UpperTheory.V.Af.Ohat F :=
  UpperTheory.V.Af.mem_Ohat.2 (GroundTheory.Global.mem_integralFiniteAdeles.2 hx)

theorem UpperTheory.finite_adelic_double_cosets :
    UpperTheory.V.Af.CohB.FinDC := by
  intro F _ _ n
  obtain ⟨S, hS⟩ := PIW.ClassFinD.borelKGL_of GlobalTheory.T.iwasawaDecomposition_finiteAdeles_GL GlobalTheory.T.strongApproximation_upperUnitriangular_finiteAdeles PIW.ClassFinD.idele_class_finite F n
  refine ⟨S, fun g => ?_⟩
  obtain ⟨γ, s, hs, k, hk, hx⟩ := hS g
  refine ⟨γ, s, hs, k, UpperTheory.V.Af.mem_KLev.2 ⟨fun a b => ohat_of (hk.1 a b), fun a b => ohat_of (hk.2 a b),
    fun a b => ⟨_, sub_mem (ohat_of (hk.1 a b)) (ohat_of (PIW.ClassFinD.matInt_one F n a b)), ?_⟩⟩, hx⟩
  rw [Nat.cast_one, one_mul]
end

section

open UpperTheory.V.Af UpperTheory.V.Af.CohB GlobalTheory.CuspRep in
private theorem relIndex_open_compact {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (U K : Subgroup G) (hU : IsOpen (U : Set G)) (hK : IsCompact (K : Set G)) : U.relIndex K ≠ 0 := by
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 hK
  haveI : Finite (K ⧸ U.subgroupOf K) :=
    Subgroup.quotient_finite_of_isOpen _ (hU.preimage continuous_subtype_val)
  exact Subgroup.index_ne_zero_of_finite

private theorem comm_comap {G H : Type} [Group G] [Group H] (f : H →* G) (U K : Subgroup G)
    (h : U.relIndex K ≠ 0) : (U.comap f).relIndex (K.comap f) ≠ 0 := by
  rw [Subgroup.relIndex_comap]
  intro h0
  exact h (Subgroup.relIndex_eq_zero_of_le_right (Subgroup.map_comap_le f K) h0)

theorem UpperTheory.arithmetic_subgroups_commensurable :
    UpperTheory.V.Af.CohB.ArithComm := by
  intro F _ _ n Γ hΓ g U hUo hUc
  set U' := U.comap (MulAut.conj g⁻¹).toMonoidHom with hU'
  have hc : Continuous (fun x : GL (Fin n) (GlobalTheory.CuspRep.Af F) => g⁻¹ * x * g) := by fun_prop
  have hc' : Continuous (fun x : GL (Fin n) (GlobalTheory.CuspRep.Af F) => g * x * g⁻¹) := by fun_prop
  have e1 : (U' : Set (GL (Fin n) (GlobalTheory.CuspRep.Af F))) = (fun x => g⁻¹ * x * g) ⁻¹' U := by
    ext x; simp [hU']
  have e2 : (U' : Set (GL (Fin n) (GlobalTheory.CuspRep.Af F))) = (fun x => g * x * g⁻¹) '' U := by
    rw [e1]
    ext x
    constructor
    · intro hx
      exact ⟨_, hx, by simp [mul_assoc]⟩
    · rintro ⟨y, hy, rfl⟩
      simpa [mul_assoc] using hy
  have ho : IsOpen (U' : Set (GL (Fin n) (GlobalTheory.CuspRep.Af F))) := e1 ▸ hUo.preimage hc
  have hk : IsCompact (U' : Set (GL (Fin n) (GlobalTheory.CuspRep.Af F))) := e2 ▸ hUc.image hc'
  have h1 := comm_comap (UpperTheory.V.Af.CohB.ratAf F n) _ _
    (relIndex_open_compact U' _ ho (UpperTheory.V.Af.isCompact_KLev (F := F) (n := n) le_rfl))
  have h2 := comm_comap (UpperTheory.V.Af.CohB.ratAf F n) _ _
    (relIndex_open_compact _ U' (UpperTheory.V.Af.isOpen_KLev (F := F) (n := n) le_rfl) hk)
  have h3 : Γ.relIndex ((UpperTheory.V.Af.KLev F n 1).comap (UpperTheory.V.Af.CohB.ratAf F n)) ≠ 0 := fun h0 =>
    hΓ.index_ne_zero (by
      rw [← Subgroup.relIndex_top_right]
      exact Subgroup.relIndex_eq_zero_of_le_right le_top h0)
  have h4 := Subgroup.relIndex_inf_ne_zero h3 h1
  have h5 : ((UpperTheory.V.Af.KLev F n 1).comap (UpperTheory.V.Af.CohB.ratAf F n)).relIndex (Γ ⊓ UpperTheory.V.Af.CohB.arith g U) ≠ 0 :=
    fun h0 => h2 (Subgroup.relIndex_eq_zero_of_le_right inf_le_right h0)
  first
    | exact ⟨h4, h5⟩
    | exact ⟨⟨h4⟩, ⟨h5⟩⟩
end

section

open NumberField IsDedekindDomain GlobalTheory.CuspRep UpperTheory.V.Af

private theorem card_int_mod (F : Type) [Field F] [NumberField F] (N : ℕ) :
    Nat.card (𝓞 F ⧸ Ideal.span {(N : 𝓞 F)}) = N ^ Module.finrank ℚ F := by
  have h := Ideal.absNorm_span_singleton (N : 𝓞 F)
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply] at h
  rw [h, ← map_natCast (algebraMap ℤ (𝓞 F)), Algebra.norm_algebraMap, RingOfIntegers.rank, Int.natAbs_pow,
    Int.natAbs_natCast]

theorem UpperTheory.card_ohat_quotient_natCast :
    UpperTheory.V.Af.CohB.CardOhat := by
  intro F _ _ N hN
  have hm : ∀ x : Af F, x ∈ Ohat F ↔ x ∈ Formalism.UG.intAd F := fun x => by
    rw [Ohat, Subring.mem_iInf]
    rfl
  let f : 𝓞 F →+* ↥(Ohat F) :=
    ((algebraMap F (Af F)).comp (algebraMap (𝓞 F) F)).codRestrict (Ohat F) fun a =>
      mem_Ohat.2 (GroundTheory.Global.algebraMap_integers_mem_integralFiniteAdeles F a)
  let g : (𝓞 F ⧸ Ideal.span {(N : 𝓞 F)}) →+* (↥(Ohat F) ⧸ Ideal.span {(N : ↥(Ohat F))}) :=
    Ideal.quotientMap _ f (by
      rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, map_natCast]
      exact Ideal.mem_span_singleton_self _)
  have hg : Function.Surjective g := by
    intro q
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective q
    obtain ⟨s, c, hc, e⟩ := Formalism.MainNotions.BridgeLevelGenB.dense_mod N hN y.1 ((hm _).1 y.2)
    refine ⟨Ideal.Quotient.mk _ s, ?_⟩
    change Ideal.Quotient.mk _ (f s) = _
    refine (Ideal.Quotient.eq.2 (Ideal.mem_span_singleton.2 ⟨⟨c, (hm _).2 hc⟩, Subtype.ext ?_⟩)).symm
    change y.1 - algebraMap F (Af F) (algebraMap (𝓞 F) F s) = (N : Af F) * c
    exact sub_eq_of_eq_add' e
  haveI : Finite (𝓞 F ⧸ Ideal.span {(N : 𝓞 F)}) :=
    Nat.finite_of_card_ne_zero (by rw [card_int_mod]; exact pow_ne_zero _ (by omega))
  exact ⟨Finite.of_surjective g hg, (Nat.card_le_card_of_surjective g hg).trans (card_int_mod F N).le⟩
end
