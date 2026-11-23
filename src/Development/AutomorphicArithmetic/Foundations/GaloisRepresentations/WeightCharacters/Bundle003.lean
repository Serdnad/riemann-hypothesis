module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.DeltaNear
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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

@[expose] public section

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU GlobalTheory.Branching
open UpperTheory.Gal.Gen (IsLevel fixedBy)
open UpperTheory.Gal.Wt

private theorem entry_mul_le {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {a : ℕ}
    {A B : Matrix (Fin a) (Fin a) ℂ} {r s : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s)
    (hA : ∀ i j, ‖ι.symm (A i j)‖ ≤ r) (hB : ∀ i j, ‖ι.symm (B i j)‖ ≤ s) (i j : Fin a) :
    ‖ι.symm ((A * B) i j)‖ ≤ r * s := by

  rw [Matrix.mul_apply, map_sum]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (mul_nonneg hr hs) fun k _ => ?_
  rw [map_mul, norm_mul]
  exact mul_le_mul (hA i k) (hB k j) (norm_nonneg _) hr

theorem UpperTheory.Gal.Wt.nearSub_of :
    UpperTheory.Gal.Wt.NearSub := by
  intro l _ ι a Γ _ _ _ φ hc hI ε hε
  refine ⟨{ carrier := {g | NearOne ι ε (φ g)}
            mul_mem' := ?_
            one_mem' := ?_
            inv_mem' := ?_ }, ?_, fun g => Iff.rfl⟩
  · intro g h hg hh
    have hg' : NearOne ι ε (φ g) := hg
    have hh' : NearOne ι ε (φ h) := hh
    show NearOne ι ε (φ (g * h))
    intro i j
    have key : ((φ (g * h) : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ) - 1
        = (((φ g : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ) - 1) * ((φ h : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ)
          + (((φ h : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ) - 1) := by
      rw [map_mul, Units.val_mul]
      noncomm_ring
    have e := congrFun (congrFun key i) j
    rw [Matrix.sub_apply] at e
    rw [e, Matrix.add_apply, map_add (f := _)]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
    · have := entry_mul_le ι hε.le zero_le_one
        (A := ((φ g : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ) - 1)
        (B := ((φ h : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ))
        (fun i j => by rw [Matrix.sub_apply]; exact hg' i j) (fun i j => (hI h i j).1) i j
      exact this.trans_eq (mul_one ε)
    · rw [Matrix.sub_apply]
      exact hh' i j
  · show NearOne ι ε (φ 1)
    intro i j
    rw [map_one, Units.val_one, sub_self, map_zero, norm_zero]
    exact hε.le
  · intro g hg
    have hg' : NearOne ι ε (φ g) := hg
    show NearOne ι ε (φ g⁻¹)
    intro i j
    have key : ((φ g⁻¹ : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ) - 1
        = -((((φ g)⁻¹ : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ)
            * (((φ g : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ) - 1)) := by
      rw [map_inv, mul_sub, Units.inv_mul, mul_one, neg_sub]
    have e := congrFun (congrFun key i) j
    rw [Matrix.sub_apply] at e
    rw [e, Matrix.neg_apply, map_neg, norm_neg]
    have := entry_mul_le ι zero_le_one hε.le
      (A := (((φ g)⁻¹ : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ))
      (B := ((φ g : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ) - 1)
      (fun i j => (hI g i j).2) (fun i j => by rw [Matrix.sub_apply]; exact hg' i j) i j
    exact this.trans_eq (one_mul ε)
  · have hset : ({g | NearOne ι ε (φ g)} : Set Γ)
        = ⋂ i, ⋂ j, (fun g => ι.symm (((φ g : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ) i j)) ⁻¹'
            Metric.closedBall (ι.symm ((1 : Matrix (Fin a) (Fin a) ℂ) i j)) ε := by
      ext g
      simp only [Set.mem_setOf_eq, NearOne, map_sub, Set.mem_iInter, Set.mem_preimage,
        Metric.mem_closedBall, dist_eq_norm]
    show IsOpen ({g | NearOne ι ε (φ g)} : Set Γ)
    rw [hset]
    exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
      (hc i j).isOpen_preimage _ (IsUltrametricDist.isOpen_closedBall _ hε.ne')
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU GlobalTheory.Branching
open UpperTheory.Gal.Gen (IsLevel fixedBy)
open UpperTheory.Gal.Wt

private noncomputable def chiZ (m : ℤ) : Circle →* ℂ where
  toFun z := (z : ℂ) ^ m
  map_one' := by simp
  map_mul' x y := by simp [mul_zpow]

private theorem chiZ_injective : Function.Injective chiZ := by
  intro m n h
  by_contra hmn
  have hk : m - n ≠ 0 := sub_ne_zero.mpr hmn
  set z : Circle := Circle.exp (Real.pi / (m - n : ℤ)) with hz
  have hpow : (z : ℂ) ^ (m - n) = -1 := by
    rw [hz, Circle.coe_exp, ← Complex.exp_int_mul]
    have : ((m - n : ℤ) : ℂ) * (((Real.pi / ((m - n : ℤ) : ℝ) : ℝ) : ℂ) * Complex.I) = Real.pi * Complex.I := by
      have hk' : ((m - n : ℤ) : ℂ) ≠ 0 := by exact_mod_cast hk
      push_cast
      push_cast at hk'
      field_simp
    rw [this, Complex.exp_pi_mul_I]
  have h1 : (z : ℂ) ^ m = (z : ℂ) ^ n := DFunLike.congr_fun h z
  have hz0 : (z : ℂ) ≠ 0 := Circle.coe_ne_zero z
  have h2 : (z : ℂ) ^ (m - n) = 1 := by
    rw [zpow_sub₀ hz0, h1, div_self (zpow_ne_zero _ hz0)]
  rw [h2] at hpow
  norm_num at hpow

theorem UpperTheory.Gal.Wt.expDisj_of :
    UpperTheory.Gal.Wt.ExpDisj := by
  intro s t f hst hle hge
  let v : ℤ → (Circle → ℂ) := fun m z => (z : ℂ) ^ m
  have hli : LinearIndependent ℂ v :=
    (linearIndependent_monoidHom Circle ℂ).comp chiZ chiZ_injective
  have hd : Disjoint (Set.Iic s) (Set.Ici t) := by
    rw [Set.disjoint_left]
    intro x hx hx'
    exact absurd (lt_of_le_of_lt (Set.mem_Iic.mp hx) hst) (not_lt.mpr (Set.mem_Ici.mp hx'))
  have hdisj := hli.disjoint_span_image hd
  have e1 : ExpLe s = Submodule.span ℂ (v '' Set.Iic s) := by
    unfold ExpLe
    congr 1
    ext g
    constructor
    · rintro ⟨m, hm, rfl⟩
      exact ⟨m, hm, rfl⟩
    · rintro ⟨m, hm, rfl⟩
      exact ⟨m, hm, rfl⟩
  have e2 : ExpGe t = Submodule.span ℂ (v '' Set.Ici t) := by
    unfold ExpGe
    congr 1
    ext g
    constructor
    · rintro ⟨m, hm, rfl⟩
      exact ⟨m, hm, rfl⟩
    · rintro ⟨m, hm, rfl⟩
      exact ⟨m, hm, rfl⟩
  rw [e1] at hle
  rw [e2] at hge
  exact Submodule.disjoint_def.mp hdisj f hle hge
end

section

noncomputable section

open Formalism.BasicNotions GlobalTheory.Branching

namespace UpperTheory.Gal.Wt

private theorem tor_isUp (a k : ℕ) (z : Circle) : IsUp (tor a k z) := by
  intro i j hij
  rw [tor_coe]
  exact Matrix.diagonal_apply_ne _ (ne_of_gt hij)

private theorem circ_mul_conj (z : Circle) : (starRingEnd ℂ) (z : ℂ) * (z : ℂ) = 1 := by
  rw [← Complex.normSq_eq_conj_mul_self]
  simp

private theorem tor_unitary (a k : ℕ) (z : Circle) :
    ∃ u : Matrix.unitaryGroup (Fin a) ℂ, unitaryIncl a u = tor a k z := by
  set d : Fin a → ℂ := fun i => if (i : ℕ) < k then (z : ℂ) else 1 with hd
  have hdd : ∀ i, d i * (starRingEnd ℂ) (d i) = 1 := by
    intro i
    simp only [hd]
    split_ifs
    · rw [mul_comm]
      exact circ_mul_conj z
    · simp
  have hmem : Matrix.diagonal d ∈ Matrix.unitaryGroup (Fin a) ℂ := by
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose,
      Matrix.diagonal_mul_diagonal]
    rw [← Matrix.diagonal_one]
    congr 1
    funext i
    exact hdd i
  refine ⟨⟨Matrix.diagonal d, hmem⟩, ?_⟩
  ext : 1
  rw [unitaryIncl_coe, tor_coe]

private theorem tor_chi {a : ℕ} (k : ℕ) (z : Circle) (κ : DomWeight a) :
    chi κ (tor a k z) = (z : ℂ) ^ psum κ k := by
  have hz : (z : ℂ) ≠ 0 := by simp
  simp only [chi, psum, tor_coe, Matrix.diagonal_apply_eq]
  rw [Finset.sum_filter]
  have key : ∀ s : Finset (Fin a), ∏ i ∈ s, (if (i : ℕ) < k then (z : ℂ) else 1) ^ κ.w i =
      (z : ℂ) ^ ∑ i ∈ s, (if (i : ℕ) < k then κ.w i else 0) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert j s hj ih =>
      rw [Finset.prod_insert hj, Finset.sum_insert hj, ih, zpow_add₀ hz]
      split_ifs <;> simp
  exact key _

private theorem tor_conj (a k : ℕ) (z : Circle) :
    Matrix.GeneralLinearGroup.map (starRingEnd ℂ) (tor a k z) = tor a k z⁻¹ := by
  have hinv : (starRingEnd ℂ) (z : ℂ) = ((z⁻¹ : Circle) : ℂ) := by
    rw [Circle.coe_inv]
    exact eq_inv_of_mul_eq_one_left (circ_mul_conj z)
  ext i j
  simp only [Matrix.GeneralLinearGroup.map_apply, tor_coe, Matrix.map_apply, Matrix.diagonal_apply]
  split_ifs <;> simp [hinv]

theorem torFacts_of : TorFacts := fun a k z =>
  ⟨tor_isUp a k z, tor_unitary a k z, fun κ => tor_chi k z κ, tor_conj a k z⟩

end UpperTheory.Gal.Wt

end
end

section

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU GlobalTheory.Branching

namespace UpperTheory.Gal.Wt

theorem famProj_of : EvLem → SumRep → FamProj := by
  intro hEv hSum E _ _ _ a τ W K ν d B hB
  classical
  obtain ⟨S₀, hS₀, hBS₀⟩ := hB.fin
  let S := S₀ ⊓ autU E a
  haveI : FiniteDimensional ℂ S := Submodule.finiteDimensional_of_le inf_le_left
  have hBS : ∀ y₁ y₂ v, B y₁ y₂ v ∈ S := fun y₁ y₂ v => ⟨hBS₀ y₁ y₂ v, hB.aut y₁ y₂ v⟩
  obtain ⟨t, ht, hind, hle⟩ := hSum E a S inferInstance fun φ hφ => hφ.2
  have hex : ∀ U : Submodule ℂ (UA E a → ℂ), ∃ p : (UA E a → ℂ) →ₗ[ℂ] (UA E a → ℂ), U ∈ t → (∀ φ, p φ ∈ U) ∧
      (∀ φ ∈ U, p φ = φ) ∧ ∀ V ∈ t, V ≠ U → ∀ φ ∈ V, p φ = 0 := fun U => by
    by_cases hU : U ∈ t
    · obtain ⟨C, hC, hc⟩ := (hind (Finset.mem_coe.2 hU)).symm.exists_isCompl
      refine ⟨U.subtype ∘ₗ Submodule.projectionOnto U C hc.symm, fun _ => ⟨fun φ => Subtype.property _, fun φ hφ =>
        congrArg Subtype.val (Submodule.projectionOnto_apply_left hc.symm ⟨φ, hφ⟩), fun V hV hne φ hφ => ?_⟩⟩
      have h0 : Submodule.projectionOnto U C hc.symm φ = 0 :=
        Submodule.projectionOnto_apply_of_mem_right hc.symm
          (hC (le_sSup (show V ∈ (t : Set (Submodule ℂ (UA E a → ℂ))) \ {U} from ⟨hV, hne⟩) hφ))
      simp [h0]
    · exact ⟨0, fun h => absurd h hU⟩
  choose p hp using hex
  have key : ∀ φ ∈ S, ∑ U ∈ t, p U φ = φ ∧ ∀ U ∈ t, ∀ x, p U (RU E a x φ) = RU E a x (p U φ) := by
    let P : Submodule ℂ (UA E a → ℂ) :=
      { carrier := {φ | ∑ U ∈ t, p U φ = φ ∧ ∀ U ∈ t, ∀ x, p U (RU E a x φ) = RU E a x (p U φ)}
        add_mem' := fun h1 h2 => ⟨by simp only [map_add (f := _), Finset.sum_add_distrib, h1.1, h2.1], fun U hU x => by
          simp only [map_add (f := _), h1.2 U hU x, h2.2 U hU x]⟩
        zero_mem' := ⟨by simp, fun U _ x => by simp⟩
        smul_mem' := fun c φ h => ⟨by simp only [map_smul, ← Finset.smul_sum, h.1], fun U hU x => by
          simp only [map_smul, h.2 U hU x]⟩ }
    refine fun φ hφ => (sSup_le (a := P) fun V hV ψ hψ => ⟨?_, fun U hU x => ?_⟩) (hle hφ)
    · rw [Finset.sum_eq_single_of_mem V hV fun U hU hne => (hp U hU).2.2 V hV hne.symm ψ hψ]
      exact (hp V hV).2.1 ψ hψ
    · have hx := (ht V hV).stable x ψ hψ
      by_cases h : V = U
      · subst h
        rw [(hp V hV).2.1 _ hx, (hp V hV).2.1 _ hψ]
      · rw [(hp U hU).2.2 V hV h _ hx, (hp U hU).2.2 V hV h _ hψ, map_zero]
  have hexp : ∀ (T : Submodule ℂ (Circle → ℂ)) (Φ : Circle → UA E a → ℂ), (∀ z, Φ z ∈ S) → (∀ g, (fun z => Φ z g) ∈ T) →
      ∀ U g, (fun z => p U (Φ z) g) ∈ T := fun T Φ h1 h2 U g =>
    hEv S (UA E a) Circle (fun g => LinearMap.proj g ∘ₗ S.subtype) (fun m hm => Subtype.ext (funext hm)) T
      (fun z => ⟨Φ z, h1 z⟩) h2 (LinearMap.proj g ∘ₗ p U ∘ₗ S.subtype)
  refine ⟨t, fun U y₁ y₂ => p U ∘ₗ B y₁ y₂, fun U hU => ⟨ht U hU, ⟨fun y₁ y₂ v => (ht U hU).aut _ ((hp U hU).1 _),
    fun k hk y₁ y₂ v => ?_, fun x y₁ y₂ v => ?_, fun b hb y₁ y₂ v => ?_, fun k x hx y₁ y₂ v g => ?_, fun k x hx y₂ v g => ?_,
    ⟨S.map (p U), inferInstance, fun y₁ y₂ v => ⟨_, hBS y₁ y₂ v, rfl⟩⟩⟩, fun y₁ y₂ v => (hp U hU).1 _⟩,
    fun y₁ y₂ v => (key _ (hBS y₁ y₂ v)).1⟩
  · show RU E a k (p U (B y₁ y₂ v)) = p U (B y₁ y₂ v)
    rw [← (key _ (hBS y₁ y₂ v)).2 U hU, hB.fix k hk]
  · show RU E a x (p U (B y₁ y₂ v)) = p U (B _ _ _)
    rw [← (key _ (hBS y₁ y₂ v)).2 U hU, hB.inf x]
  · show p U (B _ y₂ v) = chi ν b • p U (B y₁ y₂ v)
    rw [hB.up b hb, map_smul]
  · exact hexp _ _ (fun z => hBS _ _ _) (fun g => hB.le k x hx y₁ y₂ v g) U g
  · exact hexp _ _ (fun z => hBS _ _ _) (fun g => hB.ge k x hx y₂ v g) U g

end UpperTheory.Gal.Wt

end
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU GlobalTheory.Branching
open UpperTheory.Gal.Gen (IsLevel fixedBy)
open UpperTheory.Gal.Wt

private theorem RU_mul' {E : Type} [Field E] [NumberField E] [IsCMField E] {a : ℕ} (x : UA E a) (φ ψ : UA E a → ℂ) :
    RU E a x (fun g => φ g * ψ g) = RU E a x φ * RU E a x ψ := by
  ext g
  rfl

theorem UpperTheory.Gal.Wt.autMul_of :
    UpperTheory.Gal.Wt.AutMul := by
  intro E _ _ _ a φ ψ hφ hψ
  refine ⟨hφ.cont.mul hψ.cont, fun γ hγ g => ?_, ?_, ?_⟩
  · change φ (γ * g) * ψ (γ * g) = φ g * ψ g
    rw [hφ.left γ hγ, hψ.left γ hγ]
  · refine isOpen_stab_of_mem_nhds ((RU E a).comp (finU (E := E) (n := a)).subtype) (fun g => φ g * ψ g) ?_
    refine Filter.mem_of_superset ((hφ.level.inter hψ.level).mem_nhds ⟨?_, ?_⟩) fun k hk => ?_
    · change RU E a 1 φ = φ
      simp
    · change RU E a 1 ψ = ψ
      simp
    · have h1 : RU E a k φ = φ := hk.1
      have h2 : RU E a k ψ = ψ := hk.2
      change RU E a k (fun g => φ g * ψ g) = fun g => φ g * ψ g
      rw [RU_mul', h1, h2]
      rfl
  · haveI := hφ.kfin
    haveI := hψ.kfin
    have f1 : (Submodule.span ℂ (Set.range fun k : infU E a => RU E a k φ)).FG :=
      Submodule.fg_iff_finiteDimensional _ |>.2 inferInstance
    have f2 : (Submodule.span ℂ (Set.range fun k : infU E a => RU E a k ψ)).FG :=
      Submodule.fg_iff_finiteDimensional _ |>.2 inferInstance
    haveI : FiniteDimensional ℂ ↥(Submodule.span ℂ (Set.range fun k : infU E a => RU E a k φ) *
        Submodule.span ℂ (Set.range fun k : infU E a => RU E a k ψ)) :=
      Submodule.fg_iff_finiteDimensional _ |>.1 (f1.mul f2)
    refine Submodule.finiteDimensional_of_le (S₂ := Submodule.span ℂ (Set.range fun k : infU E a => RU E a k φ) *
        Submodule.span ℂ (Set.range fun k : infU E a => RU E a k ψ)) (Submodule.span_le.2 ?_)
    rintro _ ⟨k, rfl⟩
    change RU E a k (fun g => φ g * ψ g) ∈ _
    rw [RU_mul']
    exact Submodule.mul_mem_mul (Submodule.subset_span ⟨k, rfl⟩) (Submodule.subset_span ⟨k, rfl⟩)
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU GlobalTheory.Branching
open UpperTheory.Gal.Gen (IsLevel fixedBy)
open UpperTheory.Gal.Wt

theorem UpperTheory.Gal.Wt.famOfA_of :
    UpperTheory.Gal.Wt.AutMul → UpperTheory.Gal.Wt.NrmAut → UpperTheory.Gal.Wt.RFinEx → UpperTheory.Gal.Wt.FamOfA := by
  intro hMul hNrm hR E _ _ _ a τ C hC n hn W ν Q _ f P X
  have hp := fun q => hNrm E a τ C hC n hn (pev (P q)) ((hR a).2 (P q))
  have hd := fun q => hNrm E a τ C hC n hn (fun m => delta ν (X q * m)) ((hR a).1 ν (X q))
  have key : ∀ y₁ y₂ v, famOf n ν f P X y₁ y₂ v =
      ∑ q, ((fun g => pev (P q) (n g * y₂)) * (fun g => delta ν (X q * (n g * y₁)))) * (f q).1 v := by
    intro y₁ y₂ v
    funext g
    rw [famOf_apply, Finset.sum_apply]
    rfl
  refine ⟨fun y₁ y₂ v => ?_, ?_⟩
  · rw [key]
    exact mem_autU.1 (Submodule.sum_mem _ fun q _ => mem_autU.2
      (hMul E a _ _ (hMul E a _ _ ((hp q).1 y₂) ((hd q).1 y₁)) ((f q).2.1 v)))
  · choose S₁ hS₁f hS₁ using fun q => (hp q).2
    choose S₂ hS₂f hS₂ using fun q => (hd q).2
    have hfin : ∀ q, FiniteDimensional ℂ ↥(S₁ q * S₂ q * LinearMap.range (f q).1) := fun q => by
      have h₁ : (S₁ q).FG := Submodule.fg_iff_finiteDimensional _ |>.2 (hS₁f q)
      have h₂ : (S₂ q).FG := Submodule.fg_iff_finiteDimensional _ |>.2 (hS₂f q)
      have h₃ : (LinearMap.range (f q).1).FG := Submodule.fg_iff_finiteDimensional _ |>.2 inferInstance
      exact Submodule.fg_iff_finiteDimensional _ |>.1 ((h₁.mul h₂).mul h₃)
    refine ⟨⨆ q, S₁ q * S₂ q * LinearMap.range (f q).1, Submodule.finiteDimensional_iSup _, ?_⟩
    intro y₁ y₂ v
    rw [key]
    exact Submodule.sum_mem _ fun q _ => Submodule.mem_iSup_of_mem q
      (Submodule.mul_mem_mul (Submodule.mul_mem_mul (hS₁ q y₂) (hS₂ q y₁)) (LinearMap.mem_range_self _ v))
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU GlobalTheory.Branching
open UpperTheory.Gal.Gen (IsLevel fixedBy)
open UpperTheory.Gal.Wt


theorem UpperTheory.Gal.Wt.famOf_of : ExpBasic → PevExp → SqExp → TopUp → WExp → FamOfA → FamOf := by
  intro hB hP hS hT hW hA E _ _ _ a τ C hC n hn W Q _ f hf P
  obtain ⟨hLe, hGe, hmono, -, hconst, -⟩ := hB
  obtain ⟨d₀, hd₀⟩ := hW E a τ W
  refine ⟨Finset.univ.sup (fun q => (P q).totalDegree) + d₀, fun ν X => ?_⟩
  have hsum : ∀ (T : Submodule ℂ (Circle → ℂ)) (F : Q → Circle → ℂ), (∀ q, F q ∈ T) → (fun z => ∑ q, F q z) ∈ T := by
    intro T F h
    have : (fun z => ∑ q, F q z) = ∑ q, F q := by funext z; simp [Finset.sum_apply]
    rw [this]
    exact T.sum_mem fun q _ => h q
  refine ⟨(hA E a τ C hC n hn W ν Q f P X).1, ?_, ?_, ?_, ?_, ?_, (hA E a τ C hC n hn W ν Q f P X).2⟩
  · intro k hk y₁ y₂ v
    funext g
    rw [RU_apply, famOf_apply, famOf_apply, hn.lev k hk]
    exact Finset.sum_congr rfl fun q _ => by rw [hf q k hk]
  · intro x y₁ y₂ v
    funext g
    rw [RU_apply, famOf_apply, famOf_apply, hn.inf x x.2]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [(f q).2.2 x v, RU_apply, mul_assoc (n g), mul_assoc (n g)]
  · intro b hb y₁ y₂ v
    funext g
    rw [Pi.smul_apply, famOf_apply, famOf_apply, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    have : delta ν (X q * (n g * (y₁ * b))) = chi ν b * delta ν (X q * (n g * y₁)) := by
      have e : X q * (n g * (y₁ * b)) = X q * (n g * y₁) * b := by simp only [mul_assoc]
      unfold delta
      rw [e, map_mul, Module.End.mul_apply, hT a ν b hb, map_smul, map_smul, smul_eq_mul]
    rw [this]; ring
  · intro k x hx y₁ y₂ v g
    simp only [famOf_apply]
    refine hsum _ _ fun q => ?_
    have h1 := (hP a k (P q) (n g) y₂).1
    have h2 : (fun z => delta ν (X q * (n g * (tor a k z * y₁)))) ∈ ExpLe (psum ν k) := by
      have := (hS a k ν (sqRep ℂ a ν y₁ (top ν)) ((ev1 ν) ∘ₗ (sqRep ℂ a ν (X q * n g)))).1
      refine (congrArg (· ∈ ExpLe (psum ν k)) (funext fun z => ?_)).mpr this
      rw [delta, LinearMap.comp_apply, ← mul_assoc (X q), map_mul (sqRep ℂ a ν) (X q * n g), map_mul (sqRep ℂ a ν) (tor a k z),
        Module.End.mul_apply, Module.End.mul_apply]
    have h3 := (hd₀ k x hx v ((LinearMap.proj g) ∘ₗ (f q).1)).1
    refine (hmono _ _ ?_).1 (hLe _ _ _ _ (hLe _ _ _ _ h1 h2) h3)
    have : (P q).totalDegree ≤ Finset.univ.sup (fun q => (P q).totalDegree) :=
      Finset.le_sup (f := fun q => (P q).totalDegree) (Finset.mem_univ q)
    push_cast
    omega
  · intro k x hx y₂ v g
    simp only [famOf_apply]
    refine hsum _ _ fun q => ?_
    have h1 := (hP a k (P q) (n g) y₂).2
    have h2 := (hconst (delta ν (X q * (n g * 1)))).2
    have h3 := (hd₀ k x hx v ((LinearMap.proj g) ∘ₗ (f q).1)).2
    refine (hmono _ _ ?_).2 (hGe _ _ _ _ (hGe _ _ _ _ h1 h2) h3)
    push_cast
    omega
end
