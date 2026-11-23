module

public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.LengthCommensurableMapIffOfInjective
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.OrderOfVanishing.Basic
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.MemSaturatedOrderIsoSubspaceSpanSymmApply
public import Mathlib.Algebra.Module.Projective
public import Mathlib.RingTheory.Valuation.ValuationRing
import Mathlib.Algebra.Module.StablyFree.Basic
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsFiniteProjectiveComplexQuasiIso
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.IsIsoTermComparisonRestrictScalars
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
import Mathlib.RingTheory.KrullDimension.PID
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.LinearAlgebra.FreeModule.Finite.Quotient
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.LocalRing.Module

@[expose] public section

section

universe u_1 u_2 u_3 u_4

namespace GlobalTheory.SignedLengthTower

theorem relLength_tower {R V : Type*} [Ring R] [AddCommGroup V] [Module R V]
    {A B C : Submodule R V} (hBA : B ≤ A) (hCB : C ≤ B) :
    relLength A C = relLength B C + relLength A B := by
  have hle : C.submoduleOf A ≤ B.submoduleOf A := Submodule.comap_mono hCB
  rw [← relLength_submoduleOf hBA C, relLength_eq_length_map_mkQ (B.submoduleOf A),
    relLength_def, relLength_def]
  refine Module.length_eq_add_of_exact (Submodule.subtype _) (Submodule.factor hle)
    (Submodule.injective_subtype _) (Submodule.factor_surjective _) ?_
  intro y
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ y
  constructor
  · intro h
    have hx : x ∈ B.submoduleOf A := by
      simpa [Submodule.factor_mk] using h
    exact ⟨⟨_, x, hx, rfl⟩, rfl⟩
  · rintro ⟨⟨_, z, hz, rfl⟩, h⟩
    have h' : (C.submoduleOf A).mkQ z = (C.submoduleOf A).mkQ x := h
    rw [← h']
    simpa [Submodule.factor_mk] using hz

theorem ord_prod {R ι : Type*} [CommRing R] [IsDomain R] (s : Finset ι) (d : ι → R)
    (hd : ∀ i, d i ≠ 0) : Ring.ord R (∏ i ∈ s, d i) = ∑ i ∈ s, Ring.ord R (d i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Ring.ord_one]
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi,
      Ring.ord_mul' R (mem_nonZeroDivisors_of_ne_zero (hd i)), ih]

theorem length_coker {R ι : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    [Fintype ι] (f : (ι → R) →ₗ[R] (ι → R)) (hf : Function.Injective f) :
    Module.length R ((ι → R) ⧸ LinearMap.range f) = Ring.ord R (LinearMap.det f) := by
  classical
  have h : Module.finrank R (LinearMap.range f) = Module.finrank R (ι → R) :=
    LinearMap.finrank_range_of_inj hf
  set e := Pi.basisFun R ι
  set d := Submodule.smithNormalFormCoeffs e h with hd
  set top := Submodule.smithNormalFormTopBasis e h with htop
  set bot := Submodule.smithNormalFormBotBasis e h with hbot
  have hass := LinearMap.associated_det_comp_equiv (LinearMap.range f).subtype
    (LinearEquiv.ofInjective f hf) (top.equiv bot (Equiv.refl ι))
  have h1 : (LinearMap.range f).subtype ∘ₗ (LinearEquiv.ofInjective f hf).toLinearMap = f := by
    ext1 i
    ext1
    rfl
  have h2 : LinearMap.det ((LinearMap.range f).subtype ∘ₗ
      (top.equiv bot (Equiv.refl ι)).toLinearMap) = ∏ i, d i := by
    rw [← LinearMap.det_toMatrix top, ← Matrix.det_diagonal]
    congr 1
    ext i j
    have := Submodule.smithNormalFormBotBasis_def e h j
    rw [← hd, ← htop, ← hbot] at this
    rw [LinearMap.toMatrix_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
      Module.Basis.equiv_apply, Equiv.refl_apply, Submodule.subtype_apply, this]
    by_cases hij : i = j
    · subst hij; simp
    · simp [hij, Finsupp.single_apply, Ne.symm hij]
  rw [h1, h2] at hass
  obtain ⟨v, hv⟩ := hass.symm
  rw [(Submodule.quotientEquivPiSpan _ e h).length_eq, Module.length_pi_of_fintype, ← hv,
    Ring.ord_mul R (v.isUnit.mem_nonZeroDivisors), Ring.ord_of_isUnit v.isUnit, add_zero,
    ord_prod _ _ (Submodule.smithNormalFormCoeffs_ne_zero e h)]
  rfl

theorem relLength_span_matrix {R V ι : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    [AddCommGroup V] [Module R V] [Fintype ι] [DecidableEq ι] {a c : ι → V}
    (ha : LinearIndependent R a) (M : Matrix ι ι R) (hM : M.det ≠ 0)
    (hc : ∀ j, c j = ∑ i, M i j • a i) :
    relLength (Submodule.span R (Set.range a)) (Submodule.span R (Set.range c)) =
      Ring.ord R M.det := by
  let φ := Fintype.linearCombination R a
  have hφ : Function.Injective φ := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro x hx
    funext i
    exact Fintype.linearIndependent_iff.mp ha x (by simpa [φ, Fintype.linearCombination_apply] using hx) i
  have hf : Function.Injective (Matrix.toLin' M) := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro x hx
    exact Matrix.eq_zero_of_mulVec_eq_zero hM (by simpa using hx)
  have hA : Submodule.span R (Set.range a) = Submodule.map φ ⊤ := by
    rw [Submodule.map_top, Fintype.range_linearCombination]
  have hC : Submodule.span R (Set.range c) =
      Submodule.map φ (LinearMap.range (Matrix.toLin' M)) := by
    rw [Matrix.range_toLin', Submodule.map_span, ← Set.range_comp]
    congr 2
    funext j
    simp [φ, Fintype.linearCombination_apply, hc]
  rw [hA, hC, relLength_map_of_injective φ hφ, relLength_top_left, length_coker _ hf,
    LinearMap.det_toLin']

theorem signedLength_span_eq {R : Type u_1} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {K : Type u_2} [Field K] [Algebra R K] [IsFractionRing R K]
    {V : Type u_3} [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]
    {ι : Type u_4} [Fintype ι] [DecidableEq ι] {a b : ι → V} (ha : LinearIndependent K a)
    (g : Matrix ι ι K) (hb : ∀ j, b j = ∑ i, g i j • a i) {ϖ : R} (hϖ : Irreducible ϖ)
    (u : Rˣ) (n : ℤ) (hdet : g.det = algebraMap R K (u : R) * algebraMap R K ϖ ^ n) :
    signedLength (Submodule.span R (Set.range a)) (Submodule.span R (Set.range b)) = n := by
  have hinj : Function.Injective (algebraMap R K) := IsFractionRing.injective R K
  have hϖK : algebraMap R K ϖ ≠ 0 := (map_ne_zero_iff _ hinj).mpr hϖ.ne_zero
  have hg : g.det ≠ 0 := by
    rw [hdet]
    exact mul_ne_zero ((map_ne_zero_iff _ hinj).mpr u.ne_zero) (zpow_ne_zero _ hϖK)
  have hbK : LinearIndependent K b := by
    rw [Fintype.linearIndependent_iff] at ha ⊢
    intro x hx
    have h0 : g.mulVec x = 0 := by
      funext i
      refine ha (g.mulVec x) ?_ i
      rw [← hx]
      simp only [hb, Matrix.mulVec, dotProduct, Finset.sum_smul, Finset.smul_sum, smul_smul]
      rw [Finset.sum_comm]
      simp only [mul_comm]
    exact congrFun (Matrix.eq_zero_of_mulVec_eq_zero hg h0)
  have hres : ∀ {v : ι → V}, LinearIndependent K v → LinearIndependent R v := fun hv =>
    hv.restrict_scalars (by simpa [← Algebra.algebraMap_eq_smul_one] using hinj)
  obtain ⟨⟨t, ht⟩, hint⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors R)
    (fun p : ι × ι => g p.1 p.2)
  choose m hm using hint
  let M : Matrix ι ι R := Matrix.of fun i j => m (i, j)
  have hM : (algebraMap R K).mapMatrix M = algebraMap R K t • g := by
    ext i j
    simp [M, hm, Algebra.smul_def]
  let D : Matrix ι ι R := Matrix.diagonal fun _ => t
  have hD : D.det ≠ 0 := by
    rw [Matrix.det_diagonal]
    exact Finset.prod_ne_zero_iff.mpr fun _ _ => nonZeroDivisors.ne_zero ht
  have hMD : algebraMap R K M.det = algebraMap R K D.det * g.det := by
    rw [RingHom.map_det, hM, Matrix.det_smul, Matrix.det_diagonal]
    simp
  have hM0 : M.det ≠ 0 := by
    rw [← map_ne_zero_iff _ hinj, hMD]
    exact mul_ne_zero ((map_ne_zero_iff _ hinj).mpr hD) hg
  let c : ι → V := fun j => t • b j
  have hca : ∀ j, c j = ∑ i, M i j • a i := by
    intro j
    simp only [c, hb, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← smul_assoc, ← hm (i, j), algebraMap_smul]
    rfl
  have hcb : ∀ j, c j = ∑ i, D i j • b i := by
    intro j
    simp [c, D, Matrix.diagonal_apply, ite_smul]
  have hle : ∀ {v : ι → V} {N : Matrix ι ι R}, (∀ j, c j = ∑ i, N i j • v i) →
      Submodule.span R (Set.range c) ≤ Submodule.span R (Set.range v) := by
    intro v N hN
    rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    rw [hN]
    exact Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have h1 := relLength_span_matrix (hres ha) M hM0 hca
  have h2 := relLength_span_matrix (hres hbK) D hD hcb
  have hC := le_inf (hle hca) (hle hcb)
  rw [relLength_tower inf_le_left hC, relLength_inf_right] at h1
  rw [relLength_tower inf_le_right hC, relLength_inf_right'] at h2
  have hord : Ring.ord R ϖ = 1 := by
    have := PrincipalIdealRing.isMaximal_of_irreducible hϖ
    have h := relLength_top_of_isMaximal (Ideal.span {ϖ})
    rw [relLength_top_left] at h
    exact h
  obtain ⟨p, q, rfl⟩ : ∃ p q : ℕ, n = (p : ℤ) - q := ⟨n.toNat, (-n).toNat, by omega⟩
  have hR : M.det * ϖ ^ q = D.det * (u * ϖ ^ p) := by
    apply hinj
    rw [map_mul, map_mul, map_mul, map_pow, map_pow, hMD, hdet, zpow_sub₀ hϖK, zpow_natCast,
      zpow_natCast]
    field_simp
  have hϖ0 : ϖ ∈ nonZeroDivisors R := mem_nonZeroDivisors_of_ne_zero hϖ.ne_zero
  have hlen := congrArg (Ring.ord R) hR
  rw [Ring.ord_mul R (pow_mem hϖ0 q), Ring.ord_mul' R (mem_nonZeroDivisors_of_ne_zero hD),
    Ring.ord_mul R (pow_mem hϖ0 p), Ring.ord_of_isUnit u.isUnit, Ring.ord_pow hϖ0,
    Ring.ord_pow hϖ0, hord, ← h1, ← h2] at hlen
  have f1 := Ring.ord_ne_top (mem_nonZeroDivisors_of_ne_zero hM0)
  have f2 := Ring.ord_ne_top (mem_nonZeroDivisors_of_ne_zero hD)
  rw [← h1] at f1
  rw [← h2] at f2
  obtain ⟨x, hx⟩ := ENat.ne_top_iff_exists.mp (WithTop.add_ne_top.mp f1).1
  obtain ⟨y, hy⟩ := ENat.ne_top_iff_exists.mp (WithTop.add_ne_top.mp f1).2
  obtain ⟨z, hz⟩ := ENat.ne_top_iff_exists.mp (WithTop.add_ne_top.mp f2).2
  rw [signedLength_eq_of_relLength_eq hy.symm hz.symm]
  rw [← hx, ← hy, ← hz, nsmul_one, nsmul_one, zero_add] at hlen
  have : x + y + q = x + z + p := by exact_mod_cast hlen
  omega

end GlobalTheory.SignedLengthTower
end

section

open Module

namespace GlobalTheory

section General

variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]

theorem exists_isCompl_of_projective_quotient (N : Submodule R M) [Module.Projective R (M ⧸ N)] :
    ∃ N' : Submodule R M, IsCompl N N' := by
  obtain ⟨s, hs⟩ := Module.projective_lifting_property N.mkQ LinearMap.id N.mkQ_surjective
  have hs' (y : M ⧸ N) : N.mkQ (s y) = y := LinearMap.congr_fun hs y
  refine ⟨LinearMap.range s, ?_, ?_⟩
  · rw [Submodule.disjoint_def]
    rintro _ hx ⟨y, rfl⟩
    have hy : y = 0 := by
      rw [← hs' y, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact hx
    rw [hy, map_zero]
  · rw [codisjoint_iff, eq_top_iff]
    intro x _
    refine Submodule.mem_sup.2 ⟨x - s (N.mkQ x), ?_, s (N.mkQ x), ⟨_, rfl⟩, sub_add_cancel _ _⟩
    rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply, map_sub, hs', sub_self]

theorem finite_of_isCompl [Module.Finite R M] {N N' : Submodule R M} (h : IsCompl N N') :
    Module.Finite R N :=
  Module.Finite.equiv (Submodule.quotientEquivOfIsCompl N' N h.symm)

end General

section Dedekind

variable {R : Type*} [CommRing R] [IsDedekindDomain R] {M : Type*} [AddCommGroup M] [Module R M]


end Dedekind

section PID

variable {R : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
  {M : Type*} [AddCommGroup M] [Module R M]

end PID

section Valuation

variable {R : Type*} [CommRing R] [IsDomain R] [ValuationRing R]
  {M : Type*} [AddCommGroup M] [Module R M]


variable (R M) in
theorem free_of_finite_of_isTorsionFree_of_valuationRing [Module.Finite R M]
    [Module.IsTorsionFree R M] : Module.Free R M :=
  haveI : Module.Flat R M := Module.Flat.flat_iff_torsion_eq_bot_of_isBezout.2
    (Submodule.isTorsionFree_iff_torsion_eq_bot.1 ‹_›)
  Module.free_of_flat_of_isLocalRing

theorem IsSaturatedSubmodule.free_quotient_of_valuationRing [Module.Finite R M]
    {N : Submodule R M} (h : IsSaturatedSubmodule N) : Module.Free R (M ⧸ N) :=
  haveI := h.isTorsionFree_quotient
  free_of_finite_of_isTorsionFree_of_valuationRing (R := R) (M := M ⧸ N)

theorem IsSaturatedSubmodule.exists_isCompl_of_valuationRing [Module.Finite R M]
    {N : Submodule R M} (h : IsSaturatedSubmodule N) : ∃ N' : Submodule R M, IsCompl N N' :=
  haveI := h.free_quotient_of_valuationRing
  exists_isCompl_of_projective_quotient N

theorem IsSaturatedSubmodule.finite_of_valuationRing [Module.Finite R M]
    {N : Submodule R M} (h : IsSaturatedSubmodule N) : Module.Finite R N :=
  let ⟨_, h'⟩ := h.exists_isCompl_of_valuationRing
  finite_of_isCompl h'

theorem IsSaturatedSubmodule.free_of_valuationRing [Module.Finite R M] [Module.IsTorsionFree R M]
    {N : Submodule R M} (h : IsSaturatedSubmodule N) : Module.Free R N :=
  haveI := h.finite_of_valuationRing
  free_of_finite_of_isTorsionFree_of_valuationRing (R := R) (M := N)

end Valuation

universe u

end GlobalTheory
end

section

open CategoryTheory CategoryTheory.Limits DirectSum MvPolynomial TensorProduct GlobalTheory

namespace GlobalTheory

theorem bijOn_ker_and_exact_of_quasiIso {R : Type} [CommRing R]
    {K C : CochainComplex (ModuleCat.{0} R) ℕ} (φ : K ⟶ C) (h : QuasiIso φ) :
    Set.BijOn (φ.f 0).hom (LinearMap.ker (K.d 0 1).hom) (LinearMap.ker (C.d 0 1).hom) ∧
      (Function.Exact (C.d 0 1).hom (C.d 1 2).hom → Function.Exact (K.d 0 1).hom (K.d 1 2).hom) := by
  have h0 := (quasiIsoAt_zero_iff φ).1 inferInstance
  have h1 := (quasiIsoAt_succ_iff φ 0).1 inferInstance
  refine ⟨⟨fun x hx => ?_, fun x hx y hy hxy => ?_, fun y hy => ?_⟩, fun hC x => ⟨fun hx => ?_, ?_⟩⟩
  · have hx' : (K.d 0 1).hom x = 0 := hx
    change (C.d 0 1).hom ((φ.f 0).hom x) = 0
    rw [cochain_comm_apply, hx', map_zero]
  · have hx' : (K.d 0 1).hom x = 0 := hx
    have hy' : (K.d 0 1).hom y = 0 := hy
    exact sub_eq_zero.1 (h0.2 (x - y) (by rw [map_sub, hx', hy', sub_zero])
      (by rw [map_sub, hxy, sub_self]))
  · obtain ⟨x, hx, hx'⟩ := h0.1 y hy
    exact ⟨x, hx, hx'⟩
  · obtain ⟨z, hz⟩ := (hC ((φ.f 1).hom x)).1 (by rw [cochain_comm_apply, hx, map_zero])
    exact h1.2 x z hx hz
  · rintro ⟨w, rfl⟩
    exact cochain_d_d_apply K 0 1 2 w

theorem bijOn_ker_and_exact_of_quasiIso_baseChange (R R' : Type) [CommRing R] [CommRing R']
    [inst : Algebra R R'] (K C : CochainComplex (ModuleCat.{0} R) ℕ) (φ : K ⟶ C)
    (h : QuasiIso
      (((ModuleCat.extendScalars.{0, 0, 0} (algebraMap R R')).mapHomologicalComplex _).map φ)) :
    Set.BijOn ((φ.f 0).hom.baseChange R') (LinearMap.ker ((K.d 0 1).hom.baseChange R'))
        (LinearMap.ker ((C.d 0 1).hom.baseChange R')) ∧
      (Function.Exact ((C.d 0 1).hom.baseChange R') ((C.d 1 2).hom.baseChange R') →
        Function.Exact ((K.d 0 1).hom.baseChange R') ((K.d 1 2).hom.baseChange R')) := by
  have key := bijOn_ker_and_exact_of_quasiIso _ h
  clear h
  generalize hf : algebraMap R R' = f at key
  have e : inst = f.toAlgebra := Algebra.algebra_ext _ _ (fun r => by rw [hf]; rfl)
  subst e
  exact key

end GlobalTheory
end

section

open CategoryTheory CategoryTheory.Limits DirectSum MvPolynomial TensorProduct GlobalTheory

namespace GlobalTheory

theorem Cube.nonempty_extendScalars_iso_baseChange {ι : Type} {R₀ R : Type} [CommRing R₀]
    [CommRing R] [inst : Algebra R₀ R] (C : Cube.{0} ι R₀) :
    Nonempty (C ⋙ ModuleCat.extendScalars.{0, 0, 0} (algebraMap R₀ R) ≅ Cube.baseChange R C) := by
  obtain ⟨f, rfl⟩ : ∃ f : R₀ →+* R, inst = f.toAlgebra := ⟨_, toAlgebra_algebraMap.symm⟩
  exact ⟨NatIso.ofComponents (fun s => Iso.refl _) fun h => by
    rw [Iso.refl_hom, Iso.refl_hom]
    exact (Category.comp_id _).trans (Category.id_comp _).symm⟩

theorem finite_projective_extendScalars_obj {R₀ R : Type} [CommRing R₀] [CommRing R]
    (f : R₀ →+* R) (M : ModuleCat.{0} R₀) [Module.Finite R₀ M] [Module.Projective R₀ M] :
    Module.Finite R ((ModuleCat.extendScalars.{0, 0, 0} f).obj M) ∧
      Module.Projective R ((ModuleCat.extendScalars.{0, 0, 0} f).obj M) := by
  letI := f.toAlgebra
  exact ⟨inferInstanceAs (Module.Finite R (R ⊗[R₀] M)),
    inferInstanceAs (Module.Projective R (R ⊗[R₀] M))⟩

theorem quasiIso_extendScalars_extendScalars {R₀ R R' : Type} [CommRing R₀] [CommRing R]
    [CommRing R'] (f : R₀ →+* R) (g : R →+* R') {K L : CochainComplex (ModuleCat.{0} R₀) ℕ}
    (φ : K ⟶ L)
    (h : QuasiIso (((ModuleCat.extendScalars.{0, 0, 0} (g.comp f)).mapHomologicalComplex _).map φ)) :
    QuasiIso (((ModuleCat.extendScalars.{0, 0, 0} g).mapHomologicalComplex _).map
      (((ModuleCat.extendScalars.{0, 0, 0} f).mapHomologicalComplex _).map φ)) := by
  let e := NatIso.mapHomologicalComplex (ModuleCat.extendScalarsComp.{0} f g)
    (ComplexShape.up ℕ)
  have h' : QuasiIso (((ModuleCat.extendScalars.{0, 0, 0} f ⋙
      ModuleCat.extendScalars.{0, 0, 0} g).mapHomologicalComplex _).map φ) := by
    rw [← NatIso.naturality_1 e φ]
    infer_instance
  exact h'

theorem exists_finite_projective_complex_of_noetherian_model :
    ∀ (ι : Type) [LinearOrder ι] [Fintype ι] (R₀ R : Type) [CommRing R₀] [IsNoetherianRing R₀] [CommRing R] [Algebra R₀ R] (C₀ : Cube.{0} ι R₀) (A : Cube.{0} ι R) (θ : Cube.baseChange R C₀ ⟶ A), (∀ s : Finset ι, s.Nonempty → Module.Flat R₀ (C₀.obj s)) → (∀ p, Module.Finite R₀ ((cechComplex C₀).homology p)) → (∀ s : Finset ι, s.Nonempty → Function.Bijective (θ.app s).hom) → ∃ (K : CochainComplex (ModuleCat.{0} R) ℕ) (φ : K ⟶ cechComplex A), (∀ p, Fintype.card ι ≤ p + 1 → IsZero (K.X (p + 1))) ∧ (∀ p, Module.Finite R (K.X p) ∧ Module.Projective R (K.X p)) ∧ ∀ (R' : Type) [CommRing R'] [Algebra R R'], QuasiIso (((ModuleCat.extendScalars.{0, 0, 0} (algebraMap R R')).mapHomologicalComplex _).map φ) := by
  intro ι _ _ R₀ R _ _ _ _ C₀ A θ hflat hfin hθ
  obtain ⟨K₀, φ₀, h0, h1, -, h2, -, -, h3⟩ :=
    exists_finite_projective_complex_quasiIso.{0, 0} (cechComplex C₀) (Fintype.card ι - 1)
      (fun p hp => isZero_cechComplex_X C₀ (by omega))
      (fun p => Cube.flat_term C₀ (p + 1) fun s hs => hflat s (Finset.card_pos.1 (by omega))) hfin
  obtain ⟨e⟩ := Cube.nonempty_extendScalars_iso_baseChange (R := R) C₀
  let F := (ModuleCat.extendScalars.{0, 0, 0} (algebraMap R₀ R)).mapHomologicalComplex
    (ComplexShape.up ℕ)
  let ψ : F.obj (cechComplex C₀) ≅ cechComplex A :=
    cechExtendScalarsIso (algebraMap R₀ R) C₀ ≪≫ (cechFunctor ι R).mapIso e ≪≫
      @asIso _ _ _ _ (cechComplexMap θ) (isIso_cechComplexMap θ hθ)
  refine ⟨F.obj K₀, F.map φ₀ ≫ ψ.hom, fun p hp => ?_, fun p => ?_, fun R' _ _ => ?_⟩
  · exact (ModuleCat.extendScalars.{0, 0, 0} (algebraMap R₀ R)).map_isZero (h0 _ (by omega))
  · have := h1 p
    have := h2 p
    exact finite_projective_extendScalars_obj (algebraMap R₀ R) (K₀.X p)
  · letI := ((algebraMap R R').comp (algebraMap R₀ R)).toAlgebra
    have := quasiIso_extendScalars_extendScalars (algebraMap R₀ R) (algebraMap R R') φ₀ (h3 R')
    rw [Functor.map_comp]
    infer_instance

end GlobalTheory
end
