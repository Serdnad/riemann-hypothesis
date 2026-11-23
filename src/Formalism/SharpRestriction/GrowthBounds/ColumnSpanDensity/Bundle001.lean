module

public import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.Algebra.Module.StablyFree.Basic
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.HopfAlgebra.Basic
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
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.RingTheory.DiscreteValuationRing.TFAE
public import Mathlib.LinearAlgebra.Multilinear.Basic
public import Mathlib.LinearAlgebra.Multilinear.Basis

@[expose] public section

section

namespace Formalism.MainNotions.flipOneThree.Pf.KP

open Submodule

section LatRetract

variable {O K V V' : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K]
  [Algebra O K] [IsFractionRing O K] [AddCommGroup V] [Module K V] [Module O V]
  [IsScalarTower O K V] [AddCommGroup V'] [Module K V'] [Module O V'] [IsScalarTower O K V']
  {ι ι' : Type} [Fintype ι] [Fintype ι']

omit [IsDiscreteValuationRing O] in
private theorem lrt_am_ne {a : O} (ha : a ≠ 0) : algebraMap O K a ≠ 0 :=
  (map_ne_zero_iff _ (IsFractionRing.injective O K)).2 ha

private theorem lrt_tf (O K V : Type) [CommRing O] [IsDomain O] [Field K] [Algebra O K]
    [IsFractionRing O K] [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V] :
    Module.IsTorsionFree O V :=
  ⟨fun r hr x y hxy => by
    have hr0 : r ≠ 0 := hr.ne_zero
    have h1 : algebraMap O K r • x = algebraMap O K r • y := by
      rw [algebraMap_smul, algebraMap_smul]; exact hxy
    exact smul_right_injective V (lrt_am_ne (K := K) hr0) h1⟩


omit [IsDomain O] [IsDiscreteValuationRing O] [IsFractionRing O K] [Fintype ι] in
private theorem lrt_coord (b : Module.Basis ι K V) {y : V}
    (hy : y ∈ span O (Set.range b)) (i : ι) : b.repr y i ∈ Set.range (algebraMap O K) := by
  classical
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨j, rfl⟩ := hx
    by_cases hji : j = i
    · subst hji; exact ⟨1, by simp⟩
    · exact ⟨0, by simp [hji]⟩
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨u, hu⟩ := hx
    obtain ⟨v, hv⟩ := hy
    exact ⟨u + v, by simp [hu, hv]⟩
  | smul a x _ hx =>
    obtain ⟨u, hu⟩ := hx
    exact ⟨a * u, by
      rw [← algebraMap_smul K a x, map_smul, Finsupp.smul_apply, smul_eq_mul, map_mul, hu]⟩


omit [IsDiscreteValuationRing O] in
private theorem lrt_den (b : Module.Basis ι K V) (F : V) :
    ∃ a : O, a ≠ 0 ∧ a • F ∈ span O (Set.range b) := by
  obtain ⟨a, ha⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors O)
    (fun i => b.repr F i)
  refine ⟨a, nonZeroDivisors.ne_zero a.2, ?_⟩
  have hF : (a : O) • F = ∑ i, (a : O) • (b.repr F i • b i) := by
    rw [← Finset.smul_sum, b.sum_repr F]
  rw [hF]
  refine Submodule.sum_mem _ fun i _ => ?_
  obtain ⟨z, hz⟩ := ha i
  rw [← smul_assoc, ← hz, algebraMap_smul]
  exact Submodule.smul_mem _ _ (subset_span ⟨i, rfl⟩)

private theorem lrt_inj (b : Module.Basis ι K V) (b' : Module.Basis ι' K V') (io : V →ₗ[K] V')
    (h : ∀ F, io F ∈ Submodule.span O (Set.range b') ↔ F ∈ Submodule.span O (Set.range b)) :
    Function.Injective io := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro F hF
  by_contra hne
  have h0 : b.repr F ≠ 0 := by simpa using hne
  obtain ⟨i, hi⟩ := DFunLike.ne_iff.1 h0
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hmem : ((b.repr F i * algebraMap O K ϖ)⁻¹) • F ∈ span O (Set.range b) := by
    rw [← h, map_smul, hF, smul_zero]; exact zero_mem _
  obtain ⟨z, hz⟩ := lrt_coord b hmem i
  have hϖ0 : algebraMap O K ϖ ≠ 0 := lrt_am_ne hϖ.ne_zero
  have hi' : b.repr F i ≠ 0 := by simpa using hi
  have h1 : algebraMap O K (ϖ * z) = algebraMap O K 1 := by
    rw [map_mul, hz, map_one, map_smul, Finsupp.smul_apply, smul_eq_mul]
    field_simp
  have h2 := IsFractionRing.injective O K h1
  exact hϖ.not_isUnit (IsUnit.of_mul_eq_one _ h2)

theorem latRetract {O K V V' : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] [IsFractionRing O K] [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V] [AddCommGroup V'] [Module K V'] [Module O V'] [IsScalarTower O K V'] {ι ι' : Type} [Fintype ι] [Fintype ι'] (b : Module.Basis ι K V) (b' : Module.Basis ι' K V') (io : V →ₗ[K] V') (h : ∀ F, io F ∈ Submodule.span O (Set.range b') ↔ F ∈ Submodule.span O (Set.range b)) : ∃ ret : V' →ₗ[K] V, (∀ F, ret (io F) = F) ∧ ∀ G ∈ Submodule.span O (Set.range b'), ret G ∈ Submodule.span O (Set.range b) := by
  classical
  have : Module.IsTorsionFree O V := lrt_tf O K V
  have : Module.IsTorsionFree O V' := lrt_tf O K V'
  let R : Submodule O V := span O (Set.range b)
  let R' : Submodule O V' := span O (Set.range b')
  have : Module.Finite O R := Module.Finite.span_of_finite O (Set.finite_range b)
  have : Module.Finite O R' := Module.Finite.span_of_finite O (Set.finite_range b')
  let ioR : R →ₗ[O] R' := (io.restrictScalars O).restrict (fun F hF => (h F).2 hF)
  have hinj : Function.Injective ioR := fun x y hxy =>
    Subtype.ext (lrt_inj b b' io h (congrArg Subtype.val hxy))
  let N : Submodule O R' := LinearMap.range ioR
  have : Module.IsTorsionFree O (R' ⧸ N) := by
    refine ⟨fun r hr x y hxy => ?_⟩
    obtain ⟨x, rfl⟩ := N.mkQ_surjective x
    obtain ⟨y, rfl⟩ := N.mkQ_surjective y
    have h1 : N.mkQ (r • (x - y)) = 0 := by
      rw [smul_sub, map_sub, map_smul, map_smul, sub_eq_zero]; exact hxy
    rw [mkQ_apply, Quotient.mk_eq_zero] at h1
    obtain ⟨F, hF⟩ := h1
    have hr0 : r ≠ 0 := hr.ne_zero
    rw [← sub_eq_zero, ← map_sub, mkQ_apply, Quotient.mk_eq_zero]
    have hFv : io (F : V) = r • ((x - y : R') : V') := congrArg Subtype.val hF
    have hcalc : io ((algebraMap O K r)⁻¹ • (F : V)) = ((x - y : R') : V') := by
      rw [map_smul, hFv, ← algebraMap_smul K r, smul_smul, inv_mul_cancel₀ (lrt_am_ne hr0),
        one_smul]
    have hmem : (algebraMap O K r)⁻¹ • (F : V) ∈ R := by
      rw [← h, hcalc]
      exact (x - y).2
    exact ⟨⟨_, hmem⟩, Subtype.ext hcalc⟩
  obtain ⟨s, hs⟩ := N.mkQ.exists_rightInverse_of_surjective N.range_mkQ
  let e := LinearEquiv.ofInjective ioR hinj
  let p : R' →ₗ[O] N := (LinearMap.id - s ∘ₗ N.mkQ).codRestrict N (fun y => by
    rw [← Quotient.mk_eq_zero, ← mkQ_apply, LinearMap.sub_apply, map_sub, sub_eq_zero]
    exact (LinearMap.congr_fun hs (N.mkQ y)).symm)
  let retO : R' →ₗ[O] R := e.symm.toLinearMap ∘ₗ p
  have hretO : ∀ x : R, retO (ioR x) = x := by
    intro x
    show e.symm (p (ioR x)) = x
    rw [LinearEquiv.symm_apply_eq]
    apply Subtype.ext
    have h0 : N.mkQ (ioR x) = 0 := by
      rw [mkQ_apply, Quotient.mk_eq_zero]; exact ⟨x, rfl⟩
    show (LinearMap.id - s ∘ₗ N.mkQ : R' →ₗ[O] R') (ioR x) = ioR x
    simp [h0]
  let ret : V' →ₗ[K] V :=
    b'.constr K (fun j => ((retO ⟨b' j, subset_span ⟨j, rfl⟩⟩ : R) : V))
  have hret : ∀ G (hG : G ∈ R'), ret G = retO ⟨G, hG⟩ := by
    intro G hG
    induction hG using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨j, rfl⟩ := hx
      exact b'.constr_basis K _ j
    | zero =>
      rw [map_zero]
      exact (congrArg Subtype.val (map_zero retO)).symm
    | add x y hx hy ihx ihy =>
      rw [map_add (f := _), ihx, ihy]
      exact (congrArg Subtype.val (map_add retO ⟨x, hx⟩ ⟨y, hy⟩)).symm
    | smul a x hx ih =>
      have h1 : ret (a • x) = a • ret x := by
        rw [← algebraMap_smul K a x, map_smul, algebraMap_smul]
      rw [h1, ih]
      exact (congrArg Subtype.val (map_smul retO a ⟨x, hx⟩)).symm
  refine ⟨ret, fun F => ?_, fun G hG => by rw [hret G hG]; exact (retO _).2⟩
  obtain ⟨a, ha, haF⟩ := lrt_den (O := O) b F
  have h1 : ret (io (a • F)) = a • F := by
    rw [hret _ ((h _).2 haF)]
    exact congrArg Subtype.val (hretO ⟨a • F, haF⟩)
  have h2 : a • ret (io F) = a • F := by
    rw [← h1, ← algebraMap_smul K a F, map_smul, map_smul, algebraMap_smul]
  exact smul_right_injective V ha h2

end LatRetract

end Formalism.MainNotions.flipOneThree.Pf.KP
end

section

namespace Formalism.MainNotions.flipOneThree.Pf.KP

open Module

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

private noncomputable def bspZ (n : ℕ) (z : O) : Submodule O (Fin n → O) :=
  LinearMap.range (z • (LinearMap.id : (Fin n → O) →ₗ[O] (Fin n → O)))

private theorem bsp_one (n : ℕ) (z : O) (A : Matrix (Fin n) (Fin n) O) :
    ∃ (ν : ℕ) (v : Fin ν → (Fin n → O)),
      LinearMap.range (Matrix.mulVecLin A) ≤
        Submodule.span O (Set.range v) ⊔ IsLocalRing.maximalIdeal O • bspZ n z ∧
      ∃ (P : Matrix (Fin ν) (Fin n) O) (Q : Matrix (Fin n) (Fin ν) O),
        P * A * Q = z • (1 : Matrix (Fin ν) (Fin ν) O) := by
  classical
  haveI : ValuationRing O :=
    ((IsDiscreteValuationRing.TFAE O (IsDiscreteValuationRing.not_isField O)).out 1 2).mp
      (inferInstance : IsDiscreteValuationRing O)
  obtain ⟨m, S⟩ := Submodule.smithNormalForm (Pi.basisFun O (Fin n))
    (LinearMap.range (Matrix.mulVecLin A))
  let T : Finset (Fin m) := Finset.univ.filter (fun k => S.a k ∣ z)
  let e : Fin T.card ≃ T := T.equivFin.symm
  choose x hx using fun k : Fin m => (S.bN k).2
  have hc : ∀ t : T, ∃ c, z = S.a t.1 * c := fun t => (Finset.mem_filter.mp t.2).2
  choose c hc' using hc
  let w : Fin T.card → (Fin n → O) := fun i => c (e i) • x (e i).1
  have hAw : ∀ i, Matrix.mulVec A (w i) = z • S.bM (S.f (e i).1) := by
    intro i
    have h1 := hx (e i).1
    rw [Matrix.mulVecLin_apply] at h1
    show Matrix.mulVec A (c (e i) • x (e i).1) = _
    rw [Matrix.mulVec_smul, h1, S.snf, smul_smul, hc' (e i), mul_comm]
  refine ⟨T.card, fun i => S.bM (S.f (e i).1), ?_, ?_⟩
  · intro y hy
    have e2 := congrArg Subtype.val (S.bN.sum_repr ⟨y, hy⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul] at e2
    rw [← e2]
    refine Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ ?_
    rw [S.snf]
    by_cases hk : S.a k ∣ z
    · apply Submodule.mem_sup_left
      apply Submodule.smul_mem
      apply Submodule.subset_span
      exact ⟨e.symm ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk⟩⟩, by simp⟩
    · apply Submodule.mem_sup_right
      obtain ⟨d, hd⟩ := (ValuationRing.dvd_total (S.a k) z).resolve_left hk
      have hdm : d ∈ IsLocalRing.maximalIdeal O := by
        rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
        intro hu
        exact hk ⟨↑hu.unit⁻¹, by rw [hd, mul_assoc, IsUnit.mul_val_inv, mul_one]⟩
      rw [hd, mul_comm, ← smul_smul]
      exact Submodule.smul_mem_smul hdm ⟨S.bM (S.f k), rfl⟩
  · refine ⟨Matrix.of fun i r => S.bM.coord (S.f (e i).1) (fun j => if r = j then 1 else 0),
      Matrix.of fun r i => w i r, ?_⟩
    ext i i'
    rw [Matrix.mul_assoc, Matrix.mul_apply]
    have hcol : ∀ r, (A * Matrix.of fun r i => w i r) r i' = (z • S.bM (S.f (e i').1)) r := by
      intro r
      rw [← hAw i']
      simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]
    simp only [hcol, Matrix.of_apply]
    have hφ : ∑ r, S.bM.coord (S.f (e i).1) (fun j => if r = j then 1 else 0) *
        (z • S.bM (S.f (e i').1)) r = S.bM.coord (S.f (e i).1) (z • S.bM (S.f (e i').1)) := by
      rw [LinearMap.pi_apply_eq_sum_univ (S.bM.coord (S.f (e i).1)) (z • S.bM (S.f (e i').1))]
      refine Finset.sum_congr rfl fun r _ => ?_
      rw [smul_eq_mul, mul_comm]
    rw [hφ, map_smul, Module.Basis.coord_apply, Module.Basis.repr_self, Matrix.smul_apply,
      Matrix.one_apply, smul_eq_mul, smul_eq_mul]
    by_cases hii : i = i'
    · subst hii
      simp
    · have hne : S.f (e i).1 ≠ S.f (e i').1 := fun h =>
        hii (e.injective (Subtype.ext (S.f.injective h)))
      simp [Finsupp.single_apply, hne, hii]

theorem blockSplit {J : Type} [Fintype J] (n : ℕ) (z : O) (hz : z ≠ 0)
    (A : J → Matrix (Fin n) (Fin n) O) (h : ∑ j, A j = z • (1 : Matrix (Fin n) (Fin n) O)) :
    ∃ ν : J → ℕ, n ≤ ∑ j, ν j ∧ ∀ j, ∃ (P : Matrix (Fin (ν j)) (Fin n) O)
      (Q : Matrix (Fin n) (Fin (ν j)) O), P * A j * Q = z • (1 : Matrix _ _ O) := by
  classical
  choose ν v hv P Q hPQ using fun j => bsp_one n z (A j)
  refine ⟨ν, ?_, fun j => ⟨P j, Q j, hPQ j⟩⟩
  let V : (Σ j, Fin (ν j)) → (Fin n → O) := fun jk => v jk.1 jk.2
  let W : Submodule O (Fin n → O) := Submodule.span O (Set.range V)
  have hvW : ∀ j, Submodule.span O (Set.range (v j)) ≤ W := by
    intro j
    apply Submodule.span_mono
    rintro _ ⟨k, rfl⟩
    exact ⟨⟨j, k⟩, rfl⟩
  have hsum : ∀ (s : Finset J) (x : Fin n → O), Matrix.mulVec (∑ j ∈ s, A j) x = ∑ j ∈ s, Matrix.mulVec (A j) x := by
    intro s x
    induction s using Finset.induction_on with
    | empty => simp
    | insert j s hj ih => rw [Finset.sum_insert hj, Finset.sum_insert hj, Matrix.add_mulVec, ih]
  have hZ : bspZ n z ≤ W ⊔ IsLocalRing.maximalIdeal O • bspZ n z := by
    rintro _ ⟨x, rfl⟩
    have hx : (z • (LinearMap.id : (Fin n → O) →ₗ[O] (Fin n → O))) x = ∑ j, Matrix.mulVec (A j) x := by
      rw [LinearMap.smul_apply, LinearMap.id_apply, ← hsum, h, Matrix.smul_mulVec,
        Matrix.one_mulVec]
    rw [hx]
    refine Submodule.sum_mem _ fun j _ => ?_
    exact sup_le_sup_right (hvW j) _ (hv j ⟨x, rfl⟩)
  have hfg : (bspZ n z).FG := by
    unfold bspZ
    rw [LinearMap.range_eq_map]
    exact Module.Finite.fg_top.map _
  have hjac : IsLocalRing.maximalIdeal O ≤ Ideal.jacobson ⊥ := by
    rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]
  have hZW : bspZ n z ≤ W := Submodule.le_of_le_smul_of_le_jacobson_bot hfg hjac hZ
  let f := z • (LinearMap.id : (Fin n → O) →ₗ[O] (Fin n → O))
  have hinj : LinearMap.ker f = ⊥ := by
    rw [LinearMap.ker_eq_bot]
    intro x y hxy
    exact smul_right_injective _ hz hxy
  have hli : LinearIndependent O (fun i : Fin n => f (Pi.basisFun O (Fin n) i)) :=
    (Pi.basisFun O (Fin n)).linearIndependent.map' f hinj
  have hle := linearIndependent_le_span' _ hli (Set.range V) (by
    rintro _ ⟨i, rfl⟩
    exact hZW ⟨_, rfl⟩)
  calc n = Fintype.card (Fin n) := (Fintype.card_fin n).symm
    _ ≤ Fintype.card (Set.range V) := by
        rw [Cardinal.mk_fintype] at hle
        exact_mod_cast hle
    _ ≤ Fintype.card (Σ j, Fin (ν j)) := Fintype.card_range_le V
    _ = ∑ j, ν j := by simp [Fintype.card_sigma]

end Formalism.MainNotions.flipOneThree.Pf.KP
end

section

open MvPolynomial

namespace Formalism.MainNotions.flipOneThree.Pf.KP

private theorem tm_comap {S α : Type} [Fintype S] [DecidableEq S] (n : S → α →₀ ℕ) (s : S) :
    (∑ t, Finsupp.mapDomain (fun v => (t, v)) (n t)).comapDomain (fun v => (s, v))
      (Prod.mk_right_injective s).injOn = n s := by
  ext a
  rw [Finsupp.comapDomain_apply, Finsupp.finsetSum_apply, Finset.sum_eq_single s]
  · exact Finsupp.mapDomain_apply_of_injective (Prod.mk_right_injective s) (n s) a
  · intro t _ hts
    apply Finsupp.mapDomain_of_notMem_range
    rintro ⟨v, hv⟩
    exact hts (congrArg Prod.fst hv)
  · intro h
    exact absurd (Finset.mem_univ s) h

theorem tensorMap {K : Type} [Field K] {S α B : Type} [Fintype S] [DecidableEq S] [CommRing B]
    [Algebra K B] (g : S → MvPolynomial α K →ₗ[K] B) :
    ∃ F : MvPolynomial (S × α) K →ₗ[K] B, ∀ P : S → MvPolynomial α K,
      F (∏ s, rename (fun v => (s, v)) (P s)) = ∏ s, g s (P s) := by
  classical
  let F : MvPolynomial (S × α) K →ₗ[K] B :=
    (MvPolynomial.basisMonomials (S × α) K).constr K
      (fun m => ∏ s, g s (monomial (m.comapDomain (fun v => (s, v))
        (Prod.mk_right_injective s).injOn) 1))
  refine ⟨F, ?_⟩
  have key : F.compMultilinearMap
      ((MultilinearMap.mkPiAlgebra K S (MvPolynomial (S × α) K)).compLinearMap
        (fun s => (rename (R := K) (fun v : α => (s, v))).toLinearMap)) =
      (MultilinearMap.mkPiAlgebra K S B).compLinearMap g := by
    apply Module.Basis.ext_multilinear (fun _ => MvPolynomial.basisMonomials α K)
    intro n
    simp only [LinearMap.compMultilinearMap_apply, MultilinearMap.compLinearMap_apply,
      MultilinearMap.mkPiAlgebra_apply, AlgHom.toLinearMap_apply, coe_basisMonomials,
      rename_monomial]
    rw [← monomial_sum_one]
    have h := (MvPolynomial.basisMonomials (S × α) K).constr_basis K
      (fun m => ∏ s, g s (monomial (m.comapDomain (fun v => (s, v))
        (Prod.mk_right_injective s).injOn) 1))
      (∑ t, Finsupp.mapDomain (fun v => (t, v)) (n t))
    rw [coe_basisMonomials] at h
    refine h.trans ?_
    refine Finset.prod_congr rfl fun s _ => ?_
    rw [tm_comap]
  intro P
  have := congrArg (fun f => f P) key
  simpa using this

end Formalism.MainNotions.flipOneThree.Pf.KP

open MvPolynomial

namespace Formalism.MainNotions.flipOneThree.Pf.KP

end Formalism.MainNotions.flipOneThree.Pf.KP

open MvPolynomial

namespace Formalism.MainNotions.flipOneThree.Pf.KP

end Formalism.MainNotions.flipOneThree.Pf.KP

open MvPolynomial

namespace Formalism.MainNotions.flipOneThree.Pf.KP

private theorem rg_prod_mem {R A : Type} [CommSemiring R] [CommSemiring A] [Algebra R A]
    {T : Type} [DecidableEq T] (U : Finset T) (M : T → Submodule R A) (z : T → A)
    (hz : ∀ s, z s ∈ M s) : ∏ s ∈ U, z s ∈ ∏ s ∈ U, M s := by
  induction U using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty]
    exact Submodule.one_le.mp (le_refl (1 : Submodule R A))
  | insert a U ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    exact Submodule.mul_mem_mul (hz a) ih

theorem regroup {R K : Type} [CommRing R] [CommRing K] [Algebra R K] {T α : Type} [Fintype T]
    [DecidableEq T] (N : T × Bool → Submodule R (MvPolynomial α K))
    (y : T → MvPolynomial (Bool × α) K)
    (hy : ∀ s, y s ∈ Submodule.span R {P | ∃ F : Bool → MvPolynomial α K,
      (∀ b, F b ∈ N (s, b)) ∧ P = ∏ b, rename (fun v => (b, v)) (F b)}) :
    ∏ s, rename (fun v : Bool × α => ((s, v.1), v.2)) (y s) ∈
      Submodule.span R {P | ∃ F : T × Bool → MvPolynomial α K,
        (∀ x, F x ∈ N x) ∧ P = ∏ x, rename (fun v => (x, v)) (F x)} := by
  classical
  set G : T → Set (MvPolynomial (Bool × α) K) := fun s => {P | ∃ F : Bool → MvPolynomial α K,
      (∀ b, F b ∈ N (s, b)) ∧ P = ∏ b, rename (fun v => (b, v)) (F b)} with hG
  let ρ : ∀ s : T, MvPolynomial (Bool × α) K →ₗ[R] MvPolynomial ((T × Bool) × α) K := fun s =>
    ((rename (fun v : Bool × α => ((s, v.1), v.2)) :
      MvPolynomial (Bool × α) K →ₐ[K] MvPolynomial ((T × Bool) × α) K).restrictScalars R).toLinearMap
  have h1 : ∀ s, rename (fun v : Bool × α => ((s, v.1), v.2)) (y s) ∈
      Submodule.span R (ρ s '' G s) := by
    intro s
    rw [← Submodule.map_span]
    exact Submodule.mem_map_of_mem (f := ρ s) (hy s)
  have h2 := rg_prod_mem Finset.univ (fun s => Submodule.span R (ρ s '' G s)) _ h1
  rw [Submodule.prod_span] at h2
  refine Submodule.span_mono ?_ h2
  intro P hP
  rw [Set.mem_fintype_prod] at hP
  obtain ⟨g, hg, rfl⟩ := hP
  choose a ha hag using hg
  choose F hF hFa using ha
  refine ⟨fun x => F x.1 x.2, fun x => hF x.1 x.2, ?_⟩
  rw [Fintype.prod_prod_type]
  refine Finset.prod_congr rfl fun s _ => ?_
  rw [← hag s, hFa s]
  show rename (fun v : Bool × α => ((s, v.1), v.2)) _ = _
  rw [map_prod]
  refine Finset.prod_congr rfl fun b _ => ?_
  rw [rename_rename]
  rfl

end Formalism.MainNotions.flipOneThree.Pf.KP
end
