module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
public import Mathlib.Algebra.DualNumber
public import Mathlib.Topology.Algebra.Group.Defs
import Mathlib.Algebra.Module.StablyFree.Basic
public import Mathlib.Algebra.TrivSqZeroExt.Basic
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
import Mathlib.GroupTheory.Nilpotent
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.DualNumber
import Mathlib.RingTheory.Henselian
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
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.Algebra.Algebra.ZMod
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.Topology.Algebra.OpenSubgroup

@[expose] public section

section

open IsLocalRing MvPowerSeries UpperTheory.V.Alg

private theorem co_span_dual (O : Type) [CommRing O] [IsLocalRing O] (M : Type) [AddCommGroup M] [Module O M]
    (h : Module.IsTorsionBySet O M (maximalIdeal O)) (x : M) (hx : x ≠ 0) :
    ∃ D : M →ₗ[O] ResidueField O, D x ≠ 0 := by
  letI : Module (ResidueField O) M := h.module
  haveI : IsScalarTower O (ResidueField O) M := h.isScalarTower
  have := (Module.forall_dual_apply_eq_zero_iff (ResidueField O) x).not.2 hx
  push Not at this
  obtain ⟨φ, hφ⟩ := this
  exact ⟨φ.restrictScalars O, hφ⟩

theorem UpperTheory.V.Alg.co_span :
    ∀ (O : Type) [CommRing O] [IsLocalRing O] (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (B : Type) [CommRing B] [Algebra O B] [IsCO O B] (i : B →ₐ[O] R) (S : Set R), S ⊆ maximalIdeal R →
      (∀ f f' : R →ₐ[O] DualNumber (ResidueField O), f.comp i = f'.comp i → (∀ s ∈ S, f s = f' s) → f = f') →
      maximalIdeal R ≤ Ideal.span S ⊔ (maximalIdeal B).map i ⊔ maximalIdeal R ^ 2 := by
  intro O _ _ R _ _ _ B _ _ _ i S hS H x hx
  set I : Ideal R := Ideal.span S ⊔ (maximalIdeal B).map i ⊔ maximalIdeal R ^ 2 with hI
  by_contra hxI
  have hIm : I ≤ maximalIdeal R := by
    refine sup_le (sup_le (Ideal.span_le.2 hS) (Ideal.map_le_iff_le_comap.2 fun b hb => ?_))
      (Ideal.pow_le_self two_ne_zero)
    show i b ∈ maximalIdeal R
    rw [← res_eq_zero_iff O, res_map, res_eq_zero_iff]
    exact hb
  have hB : ∀ b ∈ maximalIdeal B, i b ∈ I := fun b hb =>
    Ideal.mem_sup_left (Ideal.mem_sup_right (Ideal.mem_map_of_mem _ hb))
  have hO : ∀ a ∈ maximalIdeal O, algebraMap O R a ∈ I := fun a ha => by
    have := hB (algebraMap O B a) (fun h => ha (IsLocalHom.map_nonunit a h))
    rwa [AlgHom.commutes] at this
  let N : Submodule O R := I.restrictScalars O ⊔ Submodule.span O {1}
  have hIN : ∀ y ∈ I, y ∈ N := fun y hy => Submodule.mem_sup_left hy
  have hON : ∀ a : O, algebraMap O R a ∈ N := fun a =>
    Submodule.mem_sup_right (Submodule.mem_span_singleton.2 ⟨a, (Algebra.algebraMap_eq_smul_one a).symm⟩)
  have hxN : N.mkQ x ≠ 0 := by
    intro h
    obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.1 ((Submodule.Quotient.mk_eq_zero N).1 h)
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hz
    rw [← Algebra.algebraMap_eq_smul_one] at hyz
    have h1 : algebraMap O R a ∈ maximalIdeal R := by
      have := Ideal.sub_mem _ hx (hIm hy)
      rwa [← hyz, add_sub_cancel_left] at this
    have h2 : a ∈ maximalIdeal O := fun h => h1 (h.map _)
    exact hxI (hyz ▸ I.add_mem hy (hO a h2))
  have htor : Module.IsTorsionBySet O (R ⧸ N) (maximalIdeal O) := by
    rintro y ⟨a, ha⟩
    obtain ⟨y, rfl⟩ := N.mkQ_surjective y
    show a • N.mkQ y = 0
    rw [← map_smul]
    refine (Submodule.Quotient.mk_eq_zero N).2 (hIN _ ?_)
    rw [Algebra.smul_def]
    exact I.mul_mem_right _ (hO a ha)
  obtain ⟨φ, hφ⟩ := co_span_dual O _ htor _ hxN
  let D : R →ₗ[O] ResidueField O := φ ∘ₗ N.mkQ
  have hD : ∀ y ∈ N, D y = 0 := fun y hy => by
    show φ (N.mkQ y) = 0
    rw [show N.mkQ y = 0 from (Submodule.Quotient.mk_eq_zero N).2 hy, map_zero]
  have hres : ∀ (y : R) (a : O), y - algebraMap O R a ∈ maximalIdeal R → res O R y = algebraMap O _ a :=
    fun y a ha => by
      have := (res_eq_zero_iff O R _).2 ha
      rwa [map_sub, AlgHom.commutes, sub_eq_zero] at this
  have hmul : ∀ y z, D (y * z) = res O R y * D z + D y * res O R z := fun y z => by
    obtain ⟨a, ha⟩ := IsCO.res_surj (O := O) y
    obtain ⟨b, hb⟩ := IsCO.res_surj (O := O) z
    have h1 : D ((y - algebraMap O R a) * (z - algebraMap O R b)) = 0 :=
      hD _ (hIN _ (Ideal.mem_sup_right (by rw [pow_two]; exact Ideal.mul_mem_mul ha hb)))
    have h2 : y * z = (y - algebraMap O R a) * (z - algebraMap O R b) + a • z + b • y
        - algebraMap O R (a * b) := by
      simp only [Algebra.smul_def, map_mul]; ring
    rw [h2, map_sub, map_add (f := _), map_add (f := _), h1, hD _ (hON _), map_smul, map_smul, hres y a ha, hres z b hb]
    simp only [Algebra.smul_def]; ring
  let f : R →ₐ[O] DualNumber (ResidueField O) :=
    { toFun := fun y => (res O R y, D y)
      map_one' := by
        ext
        · exact map_one (res O R)
        · exact hD _ (by simpa using hON 1)
      map_mul' := fun y z => by
        ext
        · exact map_mul (res O R) y z
        · exact hmul y z
      map_zero' := by
        ext
        · exact map_zero (res O R)
        · exact map_zero D
      map_add' := fun y z => by
        ext
        · exact map_add (res O R) y z
        · exact map_add D y z
      commutes' := fun a => by
        ext
        · exact (res O R).commutes a
        · exact hD _ (hON a) }
  let f' : R →ₐ[O] DualNumber (ResidueField O) :=
    (TrivSqZeroExt.inlAlgHom O (ResidueField O) (ResidueField O)).comp (res O R)
  have key : ∀ y, D y = 0 → f y = f' y := fun y hy => by
    ext
    · rfl
    · exact hy
  have hff : f = f' := by
    refine H f f' (AlgHom.ext fun b => key _ ?_) fun s hs => key _ (hD _ (hIN _ ?_))
    · obtain ⟨a, ha⟩ := IsCO.res_surj (O := O) b
      have := hD _ (hIN _ (hB _ ha))
      rwa [map_sub, AlgHom.commutes, map_sub, hD _ (hON a), sub_zero] at this
    · exact Ideal.mem_sup_left (Ideal.mem_sup_left (Ideal.subset_span hs))
  exact hφ (congrArg (fun g : R →ₐ[O] DualNumber (ResidueField O) => (g x).snd) hff)
end

section

open IsLocalRing MvPowerSeries UpperTheory.V.Alg

private theorem complete_of_sq {R : Type} [CommRing R] (I : Ideal R) (h : I ^ 2 = ⊥) :
    IsAdicComplete I R := by
  have h0 : ∀ x : R, x ∈ (I ^ 2 • ⊤ : Submodule R R) → x = 0 := by
    intro x hx
    rw [Ideal.smul_eq_mul, Ideal.mul_top, h] at hx
    exact (Submodule.mem_bot R).mp hx
  refine { haus' := ?_, prec' := ?_ }
  · intro x hx
    have hx2 := hx 2
    rw [SModEq.sub_mem, sub_zero] at hx2
    exact h0 x hx2
  · intro f hf
    refine ⟨f 2, fun n => ?_⟩
    rcases le_or_gt 2 n with hn | hn
    · have hfn := hf hn
      rw [SModEq.sub_mem] at hfn
      have e : f 2 = f n := sub_eq_zero.mp (h0 _ hfn)
      rw [SModEq.sub_mem, e, sub_self]
      exact Submodule.zero_mem _
    · exact hf hn.le

theorem UpperTheory.V.Alg.co_res :
    ∀ (O : Type) [CommRing O] [IsLocalRing O], IsCO O (ResidueField O) ∧ IsCO O (DualNumber (ResidueField O)) := by
  intro O _ _
  constructor
  · refine IsCO.mk ?_ ?_ ?_
    · apply complete_of_sq
      rw [maximalIdeal_eq_bot, pow_two, Ideal.bot_mul]
    · show IsLocalHom (residue O)
      infer_instance
    · intro x
      obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective x
      refine ⟨a, ?_⟩
      have h : x - algebraMap O (ResidueField O) a = 0 := sub_eq_zero.mpr ha.symm
      rw [h]
      exact zero_mem _
  · have hm : ∀ x : DualNumber (ResidueField O), x ∈ maximalIdeal _ ↔ x.fst = 0 := by
      intro x
      rw [mem_maximalIdeal, mem_nonunits_iff, TrivSqZeroExt.isUnit_iff_isUnit_fst, isUnit_iff_ne_zero,
        not_not]
    have hfst : ∀ a : O, (algebraMap O (DualNumber (ResidueField O)) a).fst =
        algebraMap O (ResidueField O) a :=
      fun a => (TrivSqZeroExt.fstHom O (ResidueField O) (ResidueField O)).commutes a
    refine IsCO.mk ?_ ?_ ?_
    · apply complete_of_sq
      rw [pow_two]
      refine le_bot_iff.mp (Ideal.mul_le.mpr fun r hr s hs => ?_)
      rw [hm] at hr hs
      refine Ideal.mem_bot.mpr (TrivSqZeroExt.ext ?_ ?_) <;> simp [hr, hs]
    · refine ⟨fun a ha => ?_⟩
      have h1 := ha.map (TrivSqZeroExt.fstHom O (ResidueField O) (ResidueField O))
      rw [(TrivSqZeroExt.fstHom O (ResidueField O) (ResidueField O)).commutes] at h1
      exact isUnit_of_map_unit (residue O) a h1
    · intro x
      obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective x.fst
      refine ⟨a, ?_⟩
      rw [hm, TrivSqZeroExt.fst_sub, hfst]
      exact sub_eq_zero.mpr ha.symm
end

section

open IsLocalRing MvPowerSeries UpperTheory.V.Alg

private theorem pullback_fin_relation (l : ℕ) [Fact l.Prime] (k : Type) [Field k] [Finite k] [CharP k l] (Γ ι : Type) [Group Γ]
    [TopologicalSpace Γ] [Fintype ι] [DecidableEq ι] (rbar : Γ →* Matrix ι ι k) [IsTopologicalGroup Γ]
    [CompactSpace Γ] (hΦ : PhiCond (Γ := Γ) l) (hlc : IsLocallyConstant rbar) :
    Finite {r : Γ →* Matrix ι ι (DualNumber k) //
      (∀ g a b, (r g a b).fst = rbar g a b) ∧ ∀ a b, IsLocallyConstant fun g => r g a b} := by
  classical
  letI : Algebra (ZMod l) k := ZMod.algebra k l
  have hHopen : IsOpen (rbar.ker : Set Γ) := by
    have h := hlc.isOpen_fiber 1
    convert h using 1
    ext x
    simp [MonoidHom.mem_ker]
  haveI : Finite (Γ ⧸ rbar.ker) := Subgroup.quotient_finite_of_isOpen _ hHopen
  haveI := hΦ rbar.ker hHopen
  haveI : Finite (Module.Dual (ZMod l) k) :=
    Finite.of_injective (fun f => (f : k → ZMod l)) DFunLike.coe_injective
  haveI : Finite (DualNumber k) := inferInstanceAs (Finite (k × k))
  have hfst : ∀ r : {r : Γ →* Matrix ι ι (DualNumber k) //
      (∀ g a b, (r g a b).fst = rbar g a b) ∧ ∀ a b, IsLocallyConstant fun g => r g a b},
      ∀ x ∈ rbar.ker, ∀ a b, (r.1 x a b).fst = (1 : Matrix ι ι k) a b := by
    intro r x hx a b
    rw [r.2.1, (MonoidHom.mem_ker).1 hx]
  have key : ∀ r : {r : Γ →* Matrix ι ι (DualNumber k) //
      (∀ g a b, (r g a b).fst = rbar g a b) ∧ ∀ a b, IsLocallyConstant fun g => r g a b},
      ∀ x ∈ rbar.ker, ∀ y ∈ rbar.ker, ∀ a b,
        (r.1 (x * y) a b).snd = (r.1 x a b).snd + (r.1 y a b).snd := by
    intro r x hx y hy a b
    rw [map_mul, Matrix.mul_apply, TrivSqZeroExt.snd_sum]
    simp only [TrivSqZeroExt.snd_mul, hfst r x hx, hfst r y hy]
    simp [Finset.sum_add_distrib, Matrix.one_apply, ite_smul, add_comm]
  have hone : ∀ r : {r : Γ →* Matrix ι ι (DualNumber k) //
      (∀ g a b, (r g a b).fst = rbar g a b) ∧ ∀ a b, IsLocallyConstant fun g => r g a b},
      ∀ a b, (r.1 1 a b).snd = 0 := by
    intro r a b
    rw [map_one]
    by_cases hab : a = b <;> simp [Matrix.one_apply, hab]
  let φ : {r : Γ →* Matrix ι ι (DualNumber k) //
      (∀ g a b, (r g a b).fst = rbar g a b) ∧ ∀ a b, IsLocallyConstant fun g => r g a b} →
      ι → ι → Module.Dual (ZMod l) k → (rbar.ker →* Multiplicative (ZMod l)) := fun r a b f =>
    { toFun := fun x => Multiplicative.ofAdd (f (r.1 x a b).snd)
      map_one' := by
        show Multiplicative.ofAdd (f (r.1 1 a b).snd) = 1
        rw [hone r a b, map_zero]
        rfl
      map_mul' := by
        intro x y
        simp only [Subgroup.coe_mul, key r x x.2 y y.2, map_add (f := _), ofAdd_add] }
  have hφopen : ∀ r a b f, IsOpen ((φ r a b f).ker : Set rbar.ker) := by
    intro r a b f
    have hlc' : IsLocallyConstant fun x : rbar.ker => φ r a b f x :=
      ((r.2.2 a b).comp_continuous continuous_subtype_val).comp
        (fun z => Multiplicative.ofAdd (f z.snd))
    have h := hlc'.isOpen_fiber 1
    convert h using 1
    ext x
    simp [MonoidHom.mem_ker]
  let F : {r : Γ →* Matrix ι ι (DualNumber k) //
      (∀ g a b, (r g a b).fst = rbar g a b) ∧ ∀ a b, IsLocallyConstant fun g => r g a b} →
      (Γ ⧸ rbar.ker → Matrix ι ι (DualNumber k)) ×
        (ι → ι → Module.Dual (ZMod l) k →
          {φ : rbar.ker →* Multiplicative (ZMod l) // IsOpen (φ.ker : Set rbar.ker)}) :=
    fun r => (fun q => r.1 q.out, fun a b f => ⟨φ r a b f, hφopen r a b f⟩)
  refine Finite.of_injective F ?_
  intro r s hrs
  have h1 : ∀ q : Γ ⧸ rbar.ker, r.1 q.out = s.1 q.out := fun q => congrFun (congrArg Prod.fst hrs) q
  have h2 : ∀ (a b : ι) (f : Module.Dual (ZMod l) k) (x : rbar.ker), f (r.1 x a b).snd = f (s.1 x a b).snd := by
    intro a b f x
    have h := congrArg (fun p => ((p.2 a b f).1 x)) hrs
    exact Multiplicative.ofAdd.injective h
  have hK : ∀ x ∈ rbar.ker, r.1 x = s.1 x := by
    intro x hx
    refine Matrix.ext fun a b => TrivSqZeroExt.ext ?_ ?_
    · rw [hfst r x hx, hfst s x hx]
    · have h := (Module.forall_dual_apply_eq_zero_iff (ZMod l) ((r.1 x a b).snd - (s.1 x a b).snd)).1
        (fun f => by rw [map_sub, h2 a b f ⟨x, hx⟩, sub_self])
      exact sub_eq_zero.1 h
  apply Subtype.ext
  ext1 g
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul rbar.ker g
  have hg : g = (QuotientGroup.mk g : Γ ⧸ rbar.ker).out * (h : Γ)⁻¹ := by
    rw [hh]
    group
  rw [hg, map_mul, map_mul, h1, hK _ (rbar.ker.inv_mem h.2)]

theorem UpperTheory.finite_lift_dualNumber_of_phiCond :
    ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsLocalRing O] [Finite (ResidueField O)] [CharP (ResidueField O) l] (Γ ι : Type) [Group Γ] [TopologicalSpace Γ] [Fintype ι] [DecidableEq ι] (rbar : Γ →* Matrix ι ι (ResidueField O)) [IsTopologicalGroup Γ] [CompactSpace Γ] [IsCO O (DualNumber (ResidueField O))], PhiCond (Γ := Γ) l → IsLocallyConstant rbar → Finite (Lift O rbar (DualNumber (ResidueField O))) := by
  intro l _ O _ _ _ _ Γ ι _ _ _ _ rbar _ _ _ hΦ hlc
  classical
  have hmem : ∀ x : DualNumber (ResidueField O), x ∈ maximalIdeal (DualNumber (ResidueField O)) ↔ x.fst = 0 := by
    intro x
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, TrivSqZeroExt.isUnit_iff_isUnit_fst, isUnit_iff_ne_zero,
      not_not]
  have hres : ∀ x : DualNumber (ResidueField O), res O (DualNumber (ResidueField O)) x = x.fst := by
    intro x
    obtain ⟨a, ha⟩ := IsLocalRing.residue_surjective x.fst
    have hx : x = algebraMap O (DualNumber (ResidueField O)) a + TrivSqZeroExt.inr x.snd := by
      rw [TrivSqZeroExt.algebraMap_eq_inl']
      refine TrivSqZeroExt.ext ?_ ?_
      · simp [IsLocalRing.ResidueField.algebraMap_eq, ha]
      · simp
    have hz : res O (DualNumber (ResidueField O)) (TrivSqZeroExt.inr x.snd) = 0 := by
      rw [res_eq_zero_iff, hmem]
      simp
    conv_lhs => rw [hx]
    rw [map_add (f := _), hz, add_zero, AlgHom.commutes, IsLocalRing.ResidueField.algebraMap_eq, ha]
  have hsq : maximalIdeal (DualNumber (ResidueField O)) ^ 2 = ⊥ := by
    rw [sq, eq_bot_iff]
    refine Ideal.mul_le.2 fun x hx y hy => ?_
    rw [hmem] at hx hy
    rw [Ideal.mem_bot]
    refine TrivSqZeroExt.ext ?_ ?_
    · simp [hx]
    · simp [TrivSqZeroExt.snd_mul, hx, hy]
  have hinj : Function.Injective (Ideal.Quotient.mk (maximalIdeal (DualNumber (ResidueField O)) ^ 2)) := by
    intro x y hxy
    rw [Ideal.Quotient.mk_eq_mk_iff_sub_mem, hsq, Ideal.mem_bot, sub_eq_zero] at hxy
    exact hxy
  haveI := pullback_fin_relation l (ResidueField O) Γ ι rbar hΦ hlc
  refine Finite.of_injective
    (fun r : Lift O rbar (DualNumber (ResidueField O)) =>
      (⟨r.hom, fun g a b => by rw [← hres]; exact r.red g a b,
        fun a b => IsLocallyConstant.desc _ _ (r.cont a b 2) hinj⟩ :
        {r : Γ →* Matrix ι ι (DualNumber (ResidueField O)) //
          (∀ g a b, (r g a b).fst = rbar g a b) ∧ ∀ a b, IsLocallyConstant fun g => r g a b}))
    ?_
  intro r s hrs
  exact Lift.ext (congrArg Subtype.val hrs)
end

section

open IsLocalRing MvPowerSeries UpperTheory.V.Alg

theorem UpperTheory.V.Alg.der_hom :
    ∀ (O A B Q : Type) [CommRing O] [CommRing A] [Algebra O A] [CommRing B] [Algebra O B] [AddCommGroup Q] [Module O Q] [Module B Q] [Module Bᵐᵒᵖ Q] [IsCentralScalar B Q] [IsScalarTower O B Q] [Module Oᵐᵒᵖ Q] [IsCentralScalar O Q] [IsScalarTower O Bᵐᵒᵖ Q] (x : A →ₐ[O] B) (D : A → Q),
      (∃ D' ∈ PtDer x Q, ⇑D' = D) ↔ ∃ y : A →ₐ[O] TrivSqZeroExt B Q, ∀ f, (y f).fst = x f ∧ (y f).snd = D f := by
  intro O A B Q _ _ _ _ _ _ _ _ _ _ _ _ _ _ x D
  constructor
  · rintro ⟨D', hD', rfl⟩
    have hL : ∀ f g : A, D' (f * g) = x f • D' g + x g • D' f := hD'
    have h1 : D' 1 = 0 := by
      have h := hL 1 1
      simp only [mul_one, map_one, one_smul] at h
      exact left_eq_add.mp h
    refine ⟨{ toFun := fun f => TrivSqZeroExt.inl (x f) + TrivSqZeroExt.inr (D' f)
              map_one' := ?_
              map_mul' := ?_
              map_zero' := ?_
              map_add' := ?_
              commutes' := ?_ }, fun f => ?_⟩
    · ext <;> simp [h1]
    · intro f g
      ext
      · simp
      · simp only [TrivSqZeroExt.snd_mul, TrivSqZeroExt.snd_add, TrivSqZeroExt.fst_add,
          TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, TrivSqZeroExt.fst_inl,
          TrivSqZeroExt.fst_inr, add_zero, zero_add, op_smul_eq_smul, hL]
    · ext <;> simp
    · intro f g
      ext <;> simp [add_add_add_comm]
    · intro r
      rw [TrivSqZeroExt.algebraMap_eq_inl']
      have h0 : D' (algebraMap O A r) = 0 := by
        rw [Algebra.algebraMap_eq_smul_one, D'.map_smul, h1, smul_zero]
      ext <;> simp [h0]
    · simp
  · rintro ⟨y, hy⟩
    have hD : ∀ f, D f = (y f).snd := fun f => (hy f).2.symm
    have hX : ∀ f, x f = (y f).fst := fun f => (hy f).1.symm
    refine ⟨{ toFun := D
              map_add' := ?_
              map_smul' := ?_ }, ?_, rfl⟩
    · intro f g
      simp only [hD, map_add (f := _), TrivSqZeroExt.snd_add]
    · intro r f
      simp only [hD, map_smul, TrivSqZeroExt.snd_smul, RingHom.id_apply]
    · show ∀ f g : A, _ = _
      intro f g
      show D (f * g) = x f • D g + x g • D f
      rw [hD, hD, hD, hX, hX, map_mul, TrivSqZeroExt.snd_mul, op_smul_eq_smul, add_comm]
end
