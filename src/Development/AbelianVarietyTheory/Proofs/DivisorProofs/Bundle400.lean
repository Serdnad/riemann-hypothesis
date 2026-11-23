module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle008
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsAlgHomOfIsBaseChange
import Mathlib.Algebra.GroupWithZero.Submonoid.CancelMulZero
import Mathlib.Algebra.Module.StablyFree.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle008
public import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
public import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
public import Development.AbelianVarietyTheory.Definitions.Divisors.EllFamNontrivial
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle005
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle376
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle338
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
public import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
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
public import Mathlib.RingTheory.Trace.Basic
public import Mathlib.RingTheory.Flat.TorsionFree

@[expose] public section

section

open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

set_option autoImplicit false

namespace GlobalTheory.PD

theorem wedge_pairing_sep {K V : Type} [Field K] [AddCommGroup V] [Module K V] {p q : ℕ}
    (b : Module.Basis (Fin (p + q)) K V) (τ : ExteriorAlgebra K V →ₗ[K] K)
    (hτ : τ (ExteriorAlgebra.ιMulti K (p + q) b) ≠ 0) (y : ExteriorAlgebra K V) (hy : y ∈ ⋀[K]^q V)
    (h : ∀ a ∈ ⋀[K]^p V, τ (a * y) = 0) : y = 0 := by
  classical
  have hdet : ∀ v : Fin (p + q) → V,
      τ (ExteriorAlgebra.ιMulti K (p + q) v) = τ (ExteriorAlgebra.ιMulti K (p + q) b) * b.det v := by
    intro v
    have e := congrArg (fun f => f v)
      (AlternatingMap.eq_smul_basis_det b (τ.compAlternatingMap (ExteriorAlgebra.ιMulti K (p + q))))
    simpa [mul_comm] using e
  have htop : ∀ U : Set.powersetCard (Fin (p + q)) (p + q),
      τ (ExteriorAlgebra.ιMulti_family K (p + q) b U) ≠ 0 := by
    intro U
    set e := Set.powersetCard.ofFinEmbEquiv.symm U
    have hinj : Function.Injective e := e.injective
    have hbij : Function.Bijective e := ⟨hinj, Finite.injective_iff_surjective.1 hinj⟩
    let σ := Equiv.ofBijective e hbij
    have hb : (b ∘ e) = ⇑(b.reindex σ.symm) := by
      funext i; simp [σ]
    rw [ExteriorAlgebra.ιMulti_family, hdet, hb]
    exact mul_ne_zero hτ (b.isUnit_det _).ne_zero
  have hcoe : ∀ {n : ℕ} (I : Set.powersetCard (Fin (p + q)) n),
      ((Module.Basis.exteriorPower n b I : ⋀[K]^n V) : ExteriorAlgebra K V) =
        ExteriorAlgebra.ιMulti_family K n b I := by
    intro n I
    simp [exteriorPower.basis_apply, exteriorPower.ιMulti_family, ExteriorAlgebra.ιMulti_family]
  set B := Module.Basis.exteriorPower q b
  set Y : ⋀[K]^q V := ⟨y, hy⟩
  suffices hY : B.repr Y = 0 by
    have : Y = 0 := B.repr.injective (by rw [hY, map_zero])
    exact congrArg Subtype.val this
  ext J
  have hJc : (J.valᶜ : Finset (Fin (p + q))).card = p := by
    rw [Finset.card_compl, Fintype.card_fin, show (J.val).card = q from J.prop]; omega
  let Jc : Set.powersetCard (Fin (p + q)) p := ⟨J.valᶜ, by simpa using hJc⟩
  have hdisj : Disjoint Jc.val J.val := disjoint_compl_left
  set a : ExteriorAlgebra K V := ExteriorAlgebra.ιMulti_family K p b Jc
  have ha : a ∈ ⋀[K]^p V := by
    rw [show a = _ from (hcoe Jc).symm]; exact (Module.Basis.exteriorPower p b Jc).2
  have hy' : y = ∑ I, B.repr Y I • (ExteriorAlgebra.ιMulti_family K q b I) := by
    have := congrArg Subtype.val (B.sum_repr Y)
    change (Y : ExteriorAlgebra K V) = _
    rw [← this, Submodule.coe_sum]
    refine Finset.sum_congr rfl fun I _ => ?_
    rw [Submodule.coe_smul, hcoe]
  have key := h a ha

  rw [hy', Finset.mul_sum, map_sum, Finset.sum_eq_single J] at key
  · rw [mul_smul_comm, map_smul, ExteriorAlgebra.ιMulti_family_mul_of_disjoint _ _ _ _ hdisj,
      Units.smul_def, map_zsmul, smul_eq_mul] at key
    rcases mul_eq_zero.1 key with h0 | h0
    · simpa using h0
    · exfalso
      rcases Int.units_eq_one_or (Set.powersetCard.permOfDisjoint hdisj).sign with hs | hs <;>
        rw [hs] at h0 <;> simp at h0 <;> exact htop _ h0
  · intro I _ hI
    rw [mul_smul_comm, ExteriorAlgebra.ιMulti_family_mul_of_not_disjoint, smul_zero, map_zero]
    intro hd
    apply hI
    have hsub : I.val ⊆ J.val := by
      intro i hi
      by_contra hj
      exact Finset.disjoint_left.1 hd (show i ∈ J.valᶜ from Finset.mem_compl.2 hj) hi
    have hle : J.val.card ≤ I.val.card := by
      rw [show (I.val).card = q from I.prop, show (J.val).card = q from J.prop]
    exact Subtype.ext (Finset.eq_of_subset_of_card_le hsub hle)
  · intro hJ; exact absurd (Finset.mem_univ J) hJ

end GlobalTheory.PD

namespace GlobalTheory.PD

theorem IsFinCover.trace_wedge_perfect : ∀ (k : Type) [Field k] [CharZero k] (F K : Type) [Field F] [Field K] [Algebra k F] [Algebra k K] [Algebra F K] [IsScalarTower k F K] (d : ℕ) (x : Fin (d + 1) → F), IsFinCover k K x → ∀ (τ : DR k K →ₗ[K] K), IsTop k K x τ → ∀ p q : ℕ, p + q = d → (∀ y ∈ ⋀[K]^q Ω[K⁄k], (∀ a ∈ ⋀[K]^p Ω[K⁄k], Algebra.trace F K (τ (a * y)) = 0) → y = 0) ∧ Module.finrank K (⋀[K]^p Ω[K⁄k]) = Module.finrank K (⋀[K]^q Ω[K⁄k]) ∧ FiniteDimensional K (⋀[K]^p Ω[K⁄k]) := by
  intro k _ _ F K _ _ _ _ _ _ d x h τ hτ p q hpq
  haveI := h.fin
  haveI := h.sep
  obtain ⟨b, hb⟩ := h.exists_basis
  haveI : Module.Finite K Ω[K⁄k] := Module.Finite.of_basis b
  haveI : Module.Free K Ω[K⁄k] := Module.Free.of_basis b
  have hfr : Module.finrank K Ω[K⁄k] = d := by rw [Module.finrank_eq_card_basis b, Fintype.card_fin]
  refine ⟨fun y hy hy0 => ?_, ?_, inferInstance⟩
  · have hτb : τ (ExteriorAlgebra.ιMulti K d b) ≠ 0 := by
      intro h0
      have hv : vol0 k K x =
          (∏ j : Fin d, (algebraMap F K (x j.succ / x 0))⁻¹) • ExteriorAlgebra.ιMulti K d b := by
        rw [← AlternatingMap.map_smul_univ]
        simp only [vol0, hb]
      have h1 := hτ.1
      rw [hv, map_smul, h0, smul_zero] at h1
      exact zero_ne_one h1
    have h2 : ∀ a ∈ ⋀[K]^p Ω[K⁄k], τ (a * y) = 0 := by
      intro a ha
      refine (traceForm_nondegenerate F K).1 _ fun c => ?_
      rw [Algebra.traceForm_apply, mul_comm, ← smul_eq_mul, ← map_smul, ← smul_mul_assoc]
      exact hy0 _ (Submodule.smul_mem _ c ha)
    subst hpq
    exact wedge_pairing_sep b τ hτb y hy h2
  · rw [exteriorPower.finrank_eq, exteriorPower.finrank_eq, hfr]
    exact Nat.choose_symm_of_eq_add hpq.symm

end GlobalTheory.PD
end

section

open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PD

theorem smul_mem_omB_regForms {k K : Type} [Field k] [Field K] [Algebra k K] (B : Subalgebra k K) (q : ℕ)
    {b : K} (hb : b ∈ B) {y : DR k K} (hy : y ∈ omB k K B q) : b • y ∈ omB k K B q := by
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨c, hc, v, hv, rfl⟩ := hy
    apply Submodule.subset_span
    refine ⟨b * c, B.mul_mem hb hc, v, hv, ?_⟩
    rw [smul_smul]
  | zero => rw [smul_zero]; exact Submodule.zero_mem _
  | add _ _ _ _ h1 h2 => rw [smul_add]; exact add_mem h1 h2
  | smul r y _ h => rw [smul_comm]; exact Submodule.smul_mem _ r h

theorem ιMulti_D_mem_omB_regForms {k K : Type} [Field k] [Field K] [Algebra k K] (B : Subalgebra k K) (q : ℕ)
    (w : Fin q → B) : (ExteriorAlgebra.ιMulti K q fun j => D k K (w j : K)) ∈ omB k K B q := by
  apply Submodule.subset_span
  exact ⟨1, B.one_mem, fun j => (w j : K), fun j => (w j).2, (one_smul K _).symm⟩

theorem omB_eq_range_exteriorPower : ∀ (k K : Type) [Field k] [Field K] [Algebra k K] (B : Subalgebra k K)
    [IsFractionRing B K] [Algebra.Smooth k B] (q : ℕ), ∃ e : (⋀[B]^q Ω[B⁄k]) →ₗ[B] DR k K,
    Function.Injective e ∧ (∀ y, y ∈ omB k K B q ↔ ∃ z, e z = y) ∧
    ∀ v : Fin q → B, e (exteriorPower.ιMulti B q fun j => D k B (v j)) =
      ExteriorAlgebra.ιMulti K q fun j => D k K (v j : K) := by
  intro k K _ _ _ B _ _ q
  haveI : Algebra.FormallyEtale B K := .of_isLocalization (nonZeroDivisors B)
  let φ : Ω[B⁄k] →ₗ[B] Ω[K⁄k] := KaehlerDifferential.map k k B K
  have hD : ∀ x : B, φ (D k B x) = D k K (x : K) := fun x => KaehlerDifferential.map_D k k B K x
  have hφ : IsBaseChange K φ := IsBaseChange.of_equiv (tensorKaehlerEquivOfFormallyEtale k B K) fun x => by
    rw [tensorKaehlerEquivOfFormallyEtale_apply, mapBaseChange_tmul, one_smul]
    rfl
  let E := GlobalTheory.exteriorPowerMapOver K q φ
  have hE : IsLocalizedModule (nonZeroDivisors B) E :=
    (isLocalizedModule_iff_isBaseChange _ K E).2 (GlobalTheory.TopForm.isBaseChange_exteriorPower hφ q)
  haveI : Module.Projective B (⋀[B]^q Ω[B⁄k]) := by
    obtain ⟨s, hs⟩ := Module.projective_def'.1 (inferInstance : Module.Projective B Ω[B⁄k])
    exact Module.Projective.of_split (exteriorPower.map q s)
      (exteriorPower.map q (Finsupp.linearCombination B id))
      (by rw [← exteriorPower.map_comp, hs, exteriorPower.map_id])
  haveI : Module.Flat B (⋀[B]^q Ω[B⁄k]) := inferInstance
  haveI : Module.IsTorsionFree B (⋀[B]^q Ω[B⁄k]) := Module.Flat.isTorsionFree
  have hEinj : Function.Injective E := by
    intro x y hxy
    obtain ⟨c, hc⟩ := IsLocalizedModule.exists_of_eq (S := nonZeroDivisors B) hxy
    exact (Module.IsTorsionFree.isSMulRegular (M := ⋀[B]^q Ω[B⁄k])
      (IsRegular.of_ne_zero (nonZeroDivisors.coe_ne_zero c))) hc
  let e : (⋀[B]^q Ω[B⁄k]) →ₗ[B] DR k K := ((⋀[K]^q Ω[K⁄k]).subtype.restrictScalars B) ∘ₗ E
  have hι : ∀ a : Fin q → Ω[B⁄k], e (exteriorPower.ιMulti B q a) =
      ExteriorAlgebra.ιMulti K q fun j => φ (a j) := by
    intro a
    change ((E (exteriorPower.ιMulti B q a) : ⋀[K]^q Ω[K⁄k]) : DR k K) = _
    rw [GlobalTheory.exteriorPowerMapOver_ιMulti, exteriorPower.ιMulti_apply_coe]
  have hιD : ∀ v : Fin q → B, e (exteriorPower.ιMulti B q fun j => D k B (v j)) =
      ExteriorAlgebra.ιMulti K q fun j => D k K (v j : K) := by
    intro v
    rw [hι]
    simp only [hD]
  have hB : ∀ (b : B) (y : DR k K), b • y = (b : K) • y := fun b y => (algebraMap_smul K b y).symm
  refine ⟨e, Subtype.val_injective.comp hEinj, fun y => ⟨fun hy => ?_, ?_⟩, hιD⟩
  · have : omB k K B q ≤ LinearMap.range (e.restrictScalars k) := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨b, hb, v, hv, rfl⟩
      refine ⟨(⟨b, hb⟩ : B) • exteriorPower.ιMulti B q (fun j => D k B ⟨v j, hv j⟩), ?_⟩
      rw [LinearMap.restrictScalars_apply, map_smul, hιD, hB]
    obtain ⟨z, hz⟩ := this hy
    exact ⟨z, hz⟩
  · rintro ⟨z, rfl⟩
    have htop := exteriorPower.ιMulti_span_of_span B q Ω[B⁄k] (span_range_derivation k B)
    have hz : z ∈ Submodule.span B
        (⇑(exteriorPower.ιMulti B q) '' {a | Set.range a ⊆ Set.range (D k B)}) := by
      rw [htop]; exact Submodule.mem_top
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨a, ha, rfl⟩ := hz
      choose w hw using fun j => ha ⟨j, rfl⟩
      have ha' : a = fun j => D k B (w j) := funext fun j => (hw j).symm
      subst ha'
      rw [hιD]
      exact ιMulti_D_mem_omB_regForms B q w
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add _ _ _ _ h1 h2 => rw [map_add]; exact add_mem h1 h2
    | smul b z _ h => rw [map_smul, hB]; exact smul_mem_omB_regForms B q b.2 h

end GlobalTheory.PD
end
end

section

set_option autoImplicit false
noncomputable section
open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

namespace GlobalTheory.PD.ResVan

variable {F : Type} [Field F] {d : ℕ}

theorem prod_zpow_add (x : Fin (d + 1) → F) (hx : ∀ i, x i ≠ 0) (m n : Fin (d + 1) → ℤ) :
    ∏ j, x j ^ (m j + n j) = (∏ j, x j ^ m j) * ∏ j, x j ^ n j := by
  first
  | exact @_root_.GlobalTheory.ProductZpowAdd.prod_zpow_add
  | exact _root_.GlobalTheory.ProductZpowAdd.prod_zpow_add
  | (apply _root_.GlobalTheory.ProductZpowAdd.prod_zpow_add <;> assumption)
  | (intros; apply _root_.GlobalTheory.ProductZpowAdd.prod_zpow_add <;> assumption)
  | (intros; apply @_root_.GlobalTheory.ProductZpowAdd.prod_zpow_add <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.ProductZpowAdd.prod_zpow_add ..)

def monoA (x : Fin (d + 1) → F) (hx : ∀ i, x i ≠ 0) (I : Finset (Fin (d + 1))) : Submonoid F where
  carrier := {f | ∃ m : Fin (d + 1) → ℤ, ∑ j, m j = 0 ∧ (∀ j ∉ I, 0 ≤ m j) ∧ f = ∏ j, x j ^ m j}
  one_mem' := ⟨0, by simp, fun _ _ => le_rfl, by simp⟩
  mul_mem' := by
    rintro _ _ ⟨m, hm, hm', rfl⟩ ⟨n, hn, hn', rfl⟩
    refine ⟨m + n, ?_, fun j hj => add_nonneg (hm' j hj) (hn' j hj), ?_⟩
    · simp [Finset.sum_add_distrib, hm, hn]
    · simp only [Pi.add_apply]; exact (prod_zpow_add x hx m n).symm

theorem prod_single_sub (x : Fin (d + 1) → F) (hx : ∀ i, x i ≠ 0) (i j : Fin (d + 1)) :
    ∏ l, x l ^ ((Pi.single j 1 : Fin (d + 1) → ℤ) l - (Pi.single i 1 : Fin (d + 1) → ℤ) l) = x j / x i := by
  simp_rw [zpow_sub₀ (hx _)]
  rw [Finset.prod_div_distrib]
  congr 1
  · rw [Fintype.prod_eq_single j (fun l hl => by simp [Pi.single_apply, hl])]; simp
  · rw [Fintype.prod_eq_single i (fun l hl => by simp [Pi.single_apply, hl])]; simp

theorem prod_exp (x : Fin (d + 1) → F) (hx : ∀ i, x i ≠ 0) (i0 : Fin (d + 1)) :
    (∏ j, x j ^ ((1 : ℤ) - if j = i0 then ((d : ℤ) + 1) else 0)) * ∏ j, x i0 / x j = 1 := by
  simp_rw [zpow_sub₀ (hx _), zpow_one]
  rw [Finset.prod_div_distrib, Finset.prod_div_distrib]
  have hq : ∏ j, x j ^ (if j = i0 then ((d : ℤ) + 1) else 0) = x i0 ^ (d + 1) := by
    rw [Fintype.prod_eq_single i0 (fun l hl => by simp [hl])]
    rw [if_pos rfl, show ((d : ℤ) + 1) = ((d + 1 : ℕ) : ℤ) by push_cast; ring, zpow_natCast]
  rw [hq]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have h0 : ∏ j, x j ≠ 0 := Finset.prod_ne_zero_iff.2 fun j _ => hx j
  have h1 := hx i0
  field_simp

theorem resvan : ∀ (k : Type) [Field k] (F : Type) [Field F] [Algebra k F] (d : ℕ) (x : Fin (d + 1) → F), IsPd k x →
    ∀ ρ : F →ₗ[k] k, IsRes k x ρ → ∀ (i : Fin (d + 1)) (I : Finset (Fin (d + 1))), I.Nonempty → i ∉ I →
    ∀ y ∈ omA k x I, ρ y = 0 := by
  intro k _ F _ _ d x hx ρ hρ i I hI hi y hy
  obtain ⟨i0, hi0⟩ := hI
  have hne := hx.ne
  have hii0 : i ≠ i0 := fun h => hi (h ▸ hi0)
  have h1 : (∏ j, x i0 / x j) * y ∈ rA k x I := by
    have h2 := (Submodule.mem_iInf _).1 hy i0
    have h3 := (Submodule.mem_iInf _).1 h2 hi0
    simpa using h3
  have hz : (∏ j, x i0 / x j) * y ∈ Submodule.span k (monoA x hne I : Set F) := by
    rw [rA, ← Subalgebra.mem_toSubmodule, Algebra.adjoin_eq_span] at h1
    refine Submodule.span_mono (Submonoid.closure_le.2 ?_) h1
    rintro _ ⟨i', hi', j, rfl⟩
    refine ⟨(Pi.single j 1 : Fin (d + 1) → ℤ) - Pi.single i' 1, by simp, fun l hl => ?_,
      (prod_single_sub x hne i' j).symm⟩
    have hl' : l ≠ i' := fun h => hl (h ▸ hi')
    simp only [Pi.sub_apply, Pi.single_apply, hl', if_false, sub_zero]
    split_ifs <;> omega
  have hP := prod_exp x hne i0
  have hy' : y = (∏ j, x j ^ ((1 : ℤ) - if j = i0 then ((d : ℤ) + 1) else 0)) * ((∏ j, x i0 / x j) * y) := by
    rw [← mul_assoc, hP, one_mul]
  rw [hy']
  generalize (∏ j, x i0 / x j) * y = z at hz
  induction hz using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨m, hm, hm', rfl⟩ := hf
    rw [← prod_zpow_add x hne]
    refine hρ.2 _ ?_ ?_
    · rw [Finset.sum_add_distrib, hm, add_zero, Finset.sum_sub_distrib]
      simp
    · intro h0
      have := congrFun h0 i
      simp only [hii0, if_false, Pi.zero_apply] at this
      have := hm' i hi
      omega
  | zero => simp
  | add a b _ _ ha hb => rw [mul_add, map_add (f := _), ha, hb, add_zero]
  | smul c a _ ha => rw [mul_smul_comm, map_smul, ha, smul_zero]

end GlobalTheory.PD.ResVan
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite

namespace GlobalTheory.EtC

def pbfMap (q : ℕ) {E : Spc} {N : ℕ} (V : E ⟶ ofCat (glCat N)) (n i : ℤ)
    (a : ∀ j : Fin N, Ht q E (n - 2 * (j : ℕ)) (i - (j : ℕ))) : Ht q (pullback V (PGL.pr N)) n i :=
  ∑ j : Fin N, ((cup q (pull _ (pullback.fst V (PGL.pr N)) _ _ (a j))
      (cpow q (c1 q (pullback.snd V (PGL.pr N) ≫ PGL.line N)) j)).cast (by ring) (by ring) : Ht q _ n i)

def PBF (q : ℕ) {E : Spc} {N : ℕ} (V : E ⟶ ofCat (glCat N)) : Prop :=
  ∀ n i : ℤ, Function.Bijective (pbfMap q V n i)

theorem projectiveBundleFormula_of_unitOnEtalePoints (h : ∀ (q : ℕ) [NeZero q] {E : Spc} {N : ℕ} (V : E ⟶ ofCat (glCat N)), Inv q E → PBF q V) : D1 :=
  fun q _ _ _ V hq n i => h q V hq n i

end GlobalTheory.EtC

end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem pull_htCast (q : ℕ) {E E' : Spc} (f : E ⟶ E') {n i n' i' : ℤ} (hn : n = n') (hi : i = i') (x : Ht q E' n i) :
    pull _ f _ _ (Ht.cast hn hi x) = Ht.cast hn hi (pull _ f _ _ x : Ht q E n i) := by
  subst hn; subst hi; rfl

theorem pull_cpow (q : ℕ) [NeZero q] (hA : DivisorNaturality) {E E' : Spc} (f : E ⟶ E') (hE' : Inv q E') (x : Ht q E' 2 1) (k : ℕ) :
    pull _ f _ _ (cpow q x k) = cpow q (pull _ f _ _ x : Ht q E 2 1) k := by
  induction k with
  | zero => rw [cpow_zero, cpow_zero, pull_htCast, (hA q).2.1 f hE']
  | succ k ih => rw [cpow_succ, cpow_succ, pull_htCast, (hA q).1, ih]

theorem inv_pullback_pgl (q : ℕ) {E : Spc} {N : ℕ} (V : E ⟶ ofCat (glCat N)) (hE : Inv q E) :
    Inv q (pullback V (PGL.pr N)) := fun U ⟨x⟩ => hE U ⟨Sx.map (pullback.fst V (PGL.pr N)) x⟩

end GlobalTheory.EtC
end
end

section

set_option autoImplicit false

open CategoryTheory GlobalTheory.CatCoh GlobalTheory.AnPer GlobalTheory.AnPer.Charts TopologicalSpace

namespace GlobalTheory.AnPer.Charts

theorem exists_param_of_deg_zero {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ}
    (K : Charts F) (hK : K.Rich) (G : C0 K.Oc)
    (hG : ∀ (T T' : K.Obj) (φ : T ⟶ T'), φ.deg = 0 → G T' = φ.φ (G T)) :
    ∃ p : Hol F.V, ∀ T : K.Obj, G T = algebraMap (Hol F.V) T.C p := by
  let a : ∀ k, Hol (K.W k) := fun k ↦ G (K.triv k)
  have h1 : ∀ k k' (e : K.le 0 k' k), K.sh e (a k) = a k' := fun k k' e ↦
    (hG (K.triv k) (K.triv k') (ptHom (K.triv k') e) rfl).symm
  have h2 : ∀ k i, dw i (a k) = 0 := fun k i ↦ by
    have e0 : G (K.jet k) = TrivSqZeroExt.inl (K.sh (K.le_refl k) (a k)) := hG _ _ (ptHom (K.jet k) (K.le_refl k)) rfl
    let j : K.Hom (K.triv k) (K.jet k) :=
      fromTriv (K.jet k) (K.le_refl k) (tszeSec dw)
        (fun f ↦ TrivSqZeroExt.ext (fst_tszeSec _ _) (funext fun a ↦ (snd_tszeSec _ _ a).trans (dw_cst k a f)))
        (Relation.ReflTransGen.single ⟨fun a ↦ TrivSqZeroExt.inr (Pi.single a 1), fun _ ↦ rfl,
          fun a b ↦ TrivSqZeroExt.inr_mul_inr _ _ _, fun h ↦ by
            simp only [RingHom.comp_apply, sh_refl]
            exact tsze_expand h fun a ↦ dw a h⟩)
    have e1 : G (K.jet k) = tszeSec dw (a k) := hG _ _ j rfl
    have e2 := congrArg (fun x : TrivSqZeroExt (Hol (K.W k)) (Fin g → Hol (K.W k)) ↦ x.snd i) (e1.symm.trans e0)
    exact (snd_tszeSec dw (a k) i).symm.trans e2
  obtain ⟨p, hp⟩ := GlobalTheory.T.exists_parameter_function_of_fibreDeriv_zero K hK a h1 h2
  refine ⟨p, fun T ↦ ?_⟩
  have e : G T = T.ρ (K.sh (K.le_refl T.k) (a T.k)) := hG _ _ (ptHom T (K.le_refl T.k)) rfl
  rw [e, sh_refl, hp, T.ρ_cst]

end GlobalTheory.AnPer.Charts
end

section

open TopologicalSpace CategoryTheory GlobalTheory.CatCoh GlobalTheory.AnPer GlobalTheory.AnPer.Charts

namespace GlobalTheory.AnPer

theorem step_single {I : Type} [Fintype I] {g : ℕ} {W : Opens (Tot I g)} {C : Type} [CommRing C] {J : Ideal C}
    {ρ₁ ρ₂ : Hol W →+* C} (a : Fin g) (e : C) (he : e ∈ J) (h2 : e * e = 0)
    (h : ∀ x, ρ₂ x = ρ₁ x + ρ₁ (dw a x) * e) : Step J ρ₁ ρ₂ := by
  refine ⟨Pi.single a e, fun c ↦ ?_, fun c d ↦ ?_, fun x ↦ ?_⟩
  · by_cases hc : c = a
    · subst hc; simpa using he
    · simp [hc]
  · by_cases hc : c = a
    · by_cases hd : d = a
      · subst hc; subst hd; simpa using h2
      · simp [hd]
    · simp [hc]
  · rw [h, Finset.sum_eq_single a]
    · simp
    · intro c _ hc; simp [hc]
    · simp

theorem exists_second_order_nbhd : ∀ (I : Type) [Fintype I] (g : ℕ) (Λ : Type) [AddCommGroup Λ] (F : Fam I g Λ) (K : Charts F) (k : K.K) (a b : Fin g), ∃ (T : K.Obj) (φ₀ φ₁ φ₂ φ₃ : K.triv k ⟶ T) (e₁ e₂ : T.C), φ₀.deg = 0 ∧ φ₁.deg = 0 ∧ φ₂.deg = 0 ∧ φ₃.deg = 0 ∧ e₁ ∈ T.J ∧ e₂ ∈ T.J ∧ e₁ * e₁ = 0 ∧ e₂ * e₂ = 0 ∧ (∀ x : Hol (K.W k), φ₁.φ x = φ₀.φ x + φ₀.φ (dw a x) * e₁) ∧ (∀ x : Hol (K.W k), φ₂.φ x = φ₀.φ x + φ₀.φ (dw b x) * e₂) ∧ (∀ x : Hol (K.W k), φ₃.φ x = φ₁.φ x + φ₁.φ (dw b x) * e₂) ∧ (∀ x : Hol (K.W k), φ₃.φ x = φ₂.φ x + φ₂.φ (dw a x) * e₁) ∧ ∀ x : Hol (K.W k), φ₀.φ x * e₁ * e₂ = 0 → x = 0 := by
  intro I _ g Λ _ F K k a b
  obtain ⟨C, _, J, φ₀, φ₁, φ₂, φ₃, e₁, e₂, hJ, h1, h2, h11, h22, H1, H2, H3, H4, H5⟩ :=
    GlobalTheory.T.exists_secondOrderNbhd_commuting_derivations (Hol (K.W k)) (dw a) (dw b) (GlobalTheory.T.fibreCoordinatePartialDerivation_comm I g (K.W k) a b)
  let T : K.Obj :=
    { k := k, C := C, alg := (φ₀.comp (K.cst k)).toAlgebra, J := J, nil := hJ, ρ := φ₀, ρ_cst := fun _ ↦ rfl }
  have hs : T.ρ.comp (K.sh (K.le_refl k)) = φ₀ := RingHom.ext fun f ↦ congrArg φ₀ (K.sh_refl _ f)
  have c0 : Close T.J (T.ρ.comp (K.sh (K.le_refl k))) φ₀ := by rw [hs]; exact Relation.ReflTransGen.refl
  have c1 : Close T.J (T.ρ.comp (K.sh (K.le_refl k))) φ₁ := Relation.ReflTransGen.tail c0 (step_single a e₁ h1 h11 H1)
  have c2 : Close T.J (T.ρ.comp (K.sh (K.le_refl k))) φ₂ := Relation.ReflTransGen.tail c0 (step_single b e₂ h2 h22 H2)
  have c3 : Close T.J (T.ρ.comp (K.sh (K.le_refl k))) φ₃ := Relation.ReflTransGen.tail c1 (step_single b e₂ h2 h22 H3)
  have a1 : ∀ f, φ₁ (K.cst k f) = φ₀ (K.cst k f) := fun f ↦ by rw [H1, dw_cst]; simp
  have a2 : ∀ f, φ₂ (K.cst k f) = φ₀ (K.cst k f) := fun f ↦ by rw [H2, dw_cst]; simp
  have a3 : ∀ f, φ₃ (K.cst k f) = φ₀ (K.cst k f) := fun f ↦ by rw [H3, dw_cst, a1]; simp
  exact ⟨T, fromTriv T (K.le_refl k) φ₀ (fun _ ↦ rfl) c0, fromTriv T (K.le_refl k) φ₁ a1 c1,
    fromTriv T (K.le_refl k) φ₂ a2 c2, fromTriv T (K.le_refl k) φ₃ a3 c3, e₁, e₂, rfl, rfl, rfl, rfl,
    h1, h2, h11, h22, H1, H2, H3, H4, H5⟩

end GlobalTheory.AnPer
end
