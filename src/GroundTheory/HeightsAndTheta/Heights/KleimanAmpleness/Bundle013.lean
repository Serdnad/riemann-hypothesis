module

public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle005
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Statements
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.StepTwoFiltGraded
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Objects
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle004
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
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

noncomputable section

universe u v w

namespace Cech

theorem Transport.proof : Transport.Statement.{u, v, w} := by
  intro n U R _ G _ _ G' _ _ ρ ρ' deg deg' φ hφ hdeg hinj hmap i

  have minj : ∀ i, Function.Injective (mapC (G := G) (G' := G') φ i) :=
    fun i s t h => funext fun I => hinj I.1 (congrFun h I)

  have lift : ∀ (i : ℕ) (w' : Cochain G' i), w' ∈ Cdeg G' deg' i →
      ∃ w ∈ Cdeg G deg i, mapC φ i w = w' := by
    intro i w' hw'
    have h : ∀ I : Idx U i, ∃ x ∈ deg I.1, φ I.1 x = w' I := fun I => by
      have hI : w' I ∈ deg' I.1 := hw' I (Set.mem_univ _)
      rw [← hmap I.1] at hI
      exact Submodule.mem_map.mp hI
    choose w hw hφw using h
    exact ⟨w, fun I _ => hw I, funext fun I => hφw I⟩

  have bdry : ∀ (i : ℕ) (z : Cochain G i), mapC φ i z ∈ bdryDeg G' deg' ρ' i → z ∈ bdryDeg G deg ρ i := by
    intro i z h
    cases i with
    | zero =>
      change mapC φ 0 z ∈ (⊥ : Submodule R _) at h
      change z ∈ (⊥ : Submodule R _)
      rw [Submodule.mem_bot] at h ⊢
      exact minj 0 (h.trans (map_zero _).symm)
    | succ i =>
      change mapC φ (i + 1) z ∈ (Cdeg G' deg' i).map (d G' ρ' i) at h
      change z ∈ (Cdeg G deg i).map (d G ρ i)
      obtain ⟨w', hw', hd⟩ := Submodule.mem_map.mp h
      obtain ⟨w, hw, rfl⟩ := lift i w' hw'
      refine Submodule.mem_map.mpr ⟨w, hw, minj (i + 1) ?_⟩
      rw [mapC_d φ hφ]
      exact hd
  constructor
  · rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    change Submodule.Quotient.mk _ = 0 at hx
    have hx' := (Submodule.Quotient.mk_eq_zero _).mp hx
    exact (Submodule.Quotient.mk_eq_zero _).mpr (bdry i z hx')
  · intro y
    obtain ⟨z', rfl⟩ := Submodule.Quotient.mk_surjective _ y
    obtain ⟨w, hw, hwz⟩ := lift i z' z'.2.2
    have hdw : d G ρ i w = 0 := by
      apply minj (i + 1)
      rw [mapC_d φ hφ, hwz, map_zero]
      exact z'.2.1
    refine ⟨Submodule.Quotient.mk ⟨w, hdw, hw⟩, ?_⟩
    change Submodule.Quotient.mk _ = _
    congr 1
    exact Subtype.ext hwz

end Cech

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u v

theorem GradedULift.proof : GradedULift.Statement.{u, v} := by
  intro S _ N M _ _ _ _ 𝓜
  let e : M ≃ₗ[S] ULift.{u} M := (ULift.moduleEquiv (R := S)).symm
  let eP : M ≃ₗ[Poly S N] ULift.{u} M := (ULift.moduleEquiv (R := Poly S N)).symm
  let pc : ℤ → Submodule S (ULift.{u} M) := fun c => (𝓜.piece c).map (e : M →ₗ[S] ULift.{u} M)
  have hpc : ∀ c, pc c = Submodule.orderIsoMapComap e (𝓜.piece c) := fun _ => rfl
  have hint : DirectSum.IsInternal pc := by
    have h0 := (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top _).1 𝓜.isInternal
    refine (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top _).2 ⟨?_, ?_⟩
    · have : pc = (Submodule.orderIsoMapComap e) ∘ 𝓜.piece := funext hpc
      rw [this]
      exact h0.1.map_orderIso _
    · have h1 : (⨆ c, pc c) = Submodule.orderIsoMapComap e (⨆ c, 𝓜.piece c) := by
        rw [OrderIso.map_iSup]
        rfl
      rw [h1, h0.2]
      exact (Submodule.orderIsoMapComap e).map_top
  let 𝓜' : GradedPMod S N (ULift.{u} M) :=
    { piece := pc
      isInternal := hint
      smul_mem := by
        intro d c p m hp hm
        obtain ⟨x, hx, rfl⟩ := hm
        refine ⟨p • x, 𝓜.smul_mem d c p x hp hx, ?_⟩
        rfl }
  refine ⟨ULift.{u} M, inferInstance, inferInstance, inferInstance, inferInstance, 𝓜',
    ⟨eP.toLinearMap, fun c m hm => ⟨m, hm, rfl⟩⟩,
    ⟨eP.symm.toLinearMap, fun c m hm => ?_⟩, fun m => rfl, fun m => rfl⟩
  obtain ⟨x, hx, rfl⟩ := hm
  exact hx

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

noncomputable section

universe u v w

section

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω} {E : Type v} [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E]

theorem SubFamily.mem_twist_iff (F : SubFamily S x E) (Q : SubFamily S x Ω) (I J : Chart x) (h : I.1 ⊆ J.1)
    (y : E) : y ∈ (F.toSubSystem.twist Q.toSubSystem).sub J ↔
      ∃ a : chartRing S x I, IsUnit (chartIncl h a) ∧
        (a : Ω) • y ∈ (F.toSubSystem.twist Q.toSubSystem).sub I := by
  constructor
  · intro hy
    refine Submodule.span_induction (p := fun y _ => ∃ a : chartRing S x I, IsUnit (chartIncl h a) ∧
      (a : Ω) • y ∈ (F.toSubSystem.twist Q.toSubSystem).sub I) ?_ ?_ ?_ ?_ hy
    · rintro _ ⟨q, hq, z, hz, rfl⟩
      obtain ⟨a₁, ha₁, hq₁⟩ := (Q.mem_iff I J h q).mp hq
      obtain ⟨a₂, ha₂, hz₂⟩ := (F.mem_iff I J h z).mp hz
      refine ⟨a₁ * a₂, by rw [map_mul]; exact ha₁.mul ha₂, ?_⟩
      have e : ((a₁ * a₂ : chartRing S x I) : Ω) • (q • z) = ((a₁ : Ω) • q) • ((a₂ : Ω) • z) := by
        rw [Subalgebra.coe_mul, smul_eq_mul, smul_smul, smul_smul]
        congr 1
        ring
      rw [e]
      exact Submodule.subset_span ⟨_, hq₁, _, hz₂, rfl⟩
    · exact ⟨1, by rw [map_one]; exact isUnit_one, by rw [smul_zero]; exact Submodule.zero_mem _⟩
    · rintro y₁ y₂ _ _ ⟨a₁, ha₁, h₁⟩ ⟨a₂, ha₂, h₂⟩
      refine ⟨a₁ * a₂, by rw [map_mul]; exact ha₁.mul ha₂, ?_⟩
      have e : ((a₁ * a₂ : chartRing S x I) : Ω) • (y₁ + y₂) =
          a₂ • ((a₁ : Ω) • y₁) + a₁ • ((a₂ : Ω) • y₂) := by
        rw [Subalgebra.smul_def, Subalgebra.smul_def, smul_add, smul_smul, smul_smul, Subalgebra.coe_mul,
          mul_comm (a₂ : Ω) (a₁ : Ω)]
      rw [e]
      exact Submodule.add_mem _ (Submodule.smul_mem _ _ h₁) (Submodule.smul_mem _ _ h₂)
    · rintro b z _ ⟨a, ha, hz⟩
      obtain ⟨c, hc, hcb⟩ := exists_isUnit_mul_mem h b
      refine ⟨c * a, by rw [map_mul]; exact hc.mul ha, ?_⟩
      have e : ((c * a : chartRing S x I) : Ω) • (b • z) =
          (⟨_, hcb⟩ : chartRing S x I) • ((a : Ω) • z) := by
        rw [Subalgebra.smul_def, Subalgebra.smul_def, smul_smul, smul_smul, Subalgebra.coe_mul]
        congr 1
        ring
      rw [e]
      exact Submodule.smul_mem _ _ hz
  · rintro ⟨a, ⟨u, hu⟩, hay⟩
    have hJ := (F.toSubSystem.twist Q.toSubSystem).mono I J h _ hay
    have hinv : ((↑u⁻¹ : chartRing S x J) : Ω) * (a : Ω) = 1 := by
      have := congrArg Subtype.val (Units.inv_mul u)
      rw [hu] at this
      exact this
    have hy : y = (↑u⁻¹ : chartRing S x J) • ((a : Ω) • y) := by
      rw [Subalgebra.smul_def, smul_smul, hinv, one_smul]
    rw [hy]
    exact Submodule.smul_mem _ _ hJ

def SubFamily.twistFam (F : SubFamily S x E) (Q : SubFamily S x Ω) : SubFamily S x E where
  toSubSystem := F.toSubSystem.twist Q.toSubSystem
  mem_iff := F.mem_twist_iff Q

theorem SubFamily.exists_pow (Q : SubFamily S x Ω) (n : ℕ) :
    ∃ P : SubFamily S x Ω, P.toSubSystem = Q.toSubSystem.pow n := by
  induction n with
  | zero => exact ⟨(twistBundle S x 0).toSubFamily, rfl⟩
  | succ n ih =>
    obtain ⟨P, hP⟩ := ih
    refine ⟨P.twistFam Q, ?_⟩
    change P.toSubSystem.twist Q.toSubSystem = (Q.toSubSystem.pow n).twist Q.toSubSystem
    rw [hP]

end

theorem SubFamilyTwistPow.proof : SubFamilyTwistPow.Statement.{u, v, w} := by
  intro S _ Ω _ _ N x E _ _ _ _ F Q a
  obtain ⟨P, hP⟩ := SubFamily.exists_pow Q a
  exact ⟨F.twistFam P, by rw [← hP]; rfl⟩

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u v w

theorem StepTwo.Filt.proof (h : PrimeFiltration.Exists.Statement.{u, v, w}) :
    StepTwo.Filt.Statement.{u, v, w} := by
  intro S _ _ Ω _ _ N x E _ _ _ _ M₁ M₂ hle J hJ
  classical
  obtain ⟨⟨F⟩, -⟩ := h S Ω N x (quotLaurent M₁ M₂) (quotLaurentGraded M₁ M₂) (quotLaurent_finite M₁ M₂)
    fun p hp y => quotLaurent_smul_eq_zero M₁ M₂ hp y
  have hrep : ∀ k, ∃ g : M₁.piece (F.deg k), quotIota M₁ M₂ (F.deg k) g = F.gen k :=
    fun k => LinearMap.mem_range.mp (F.gen_mem k)
  choose g hg using hrep
  have hstab : ∀ k : Fin (F.n + 1), IsProjStable M₁ M₂ (F.step k) := by
    intro k
    induction k using Fin.induction with
    | zero => rw [F.step_zero]; exact isProjStable_bot
    | succ k ih => rw [F.step_succ k, ← hg k]; exact isProjStable_sup ih (g k)
  have hfg : ∀ k : Fin (F.n + 1), ∃ (n : ℕ) (deg : Fin n → ℤ) (gen : Fin n → E),
      (∀ j, gen j ∈ filtPiece M₁ M₂ (F.step k) (deg j)) ∧
      ∀ c, filtPiece M₁ M₂ (F.step k) c ≤ Submodule.span S {z | ∃ (j : Fin n) (f : Poly S N) (e : ℕ),
        f.IsHomogeneous e ∧ (e : ℤ) + deg j = c ∧ z = aeval x f • gen j} := by
    intro k
    induction k using Fin.induction with
    | zero =>
      rw [F.step_zero]
      simp only [filtPiece_bot hle]
      exact M₂.fg
    | succ k ih =>
      obtain ⟨n, deg, gen, hmem, hspan⟩ := ih
      have hsup := filtPiece_sup (hstab k.castSucc) (g k)
      rw [F.step_succ k, ← hg k]
      refine ⟨n + 1, Fin.cons (F.deg k) deg, Fin.cons (g k : E) gen, fun j => ?_, fun c => ?_⟩
      · refine Fin.cases ?_ (fun j => ?_) j
        · rw [Fin.cons_zero, Fin.cons_zero, hsup]
          refine Submodule.mem_sup_right (Submodule.subset_span ⟨1, 0, isHomogeneous_one _ _, by simp, ?_⟩)
          rw [map_one, one_smul]
        · rw [Fin.cons_succ, Fin.cons_succ]
          exact filtPiece_mono le_sup_left _ (hmem j)
      · rw [hsup]
        refine sup_le ((hspan c).trans (Submodule.span_mono ?_)) (Submodule.span_mono ?_)
        · rintro _ ⟨j, f, e, hf, he, rfl⟩
          exact ⟨j.succ, f, e, hf, by rw [Fin.cons_succ]; exact he, by rw [Fin.cons_succ]⟩
        · rintro _ ⟨f, d, hf, hd, rfl⟩
          exact ⟨0, f, d, hf, by rw [Fin.cons_zero]; omega, by rw [Fin.cons_zero]⟩
  refine ⟨F.n, fun k => filtSub M₁ M₂ (F.step k) (hfg k), fun k => (g k : E), F.deg, F.prime, ?_, ?_,
    fun k => ⟨F.isPrime k, F.isHomogeneous k, ?_, ?_, ?_, ?_, ?_⟩⟩
  · refine FinGradedSub.eq_of_piece_eq (funext fun c => ?_)
    change filtPiece M₁ M₂ (F.step 0) c = _
    rw [F.step_zero, filtPiece_bot hle]
  · refine FinGradedSub.eq_of_piece_eq (funext fun c => ?_)
    change filtPiece M₁ M₂ (F.step (Fin.last F.n)) c = _
    rw [F.step_last, filtPiece_top]
  · exact fun p hp => F.ann_le k
      (Module.mem_annihilator.mpr fun y => quotLaurent_smul_eq_zero M₁ M₂ hp y)
  · exact fun f e hf he => F.ann_le k
      (Module.mem_annihilator.mpr fun y => quotLaurent_smul_eq_zero_of M₁ M₂ he (hJ f e hf he) y)
  · change ((g k : M₁.piece (F.deg k)) : E) ∈ filtPiece M₁ M₂ (F.step k.succ) (F.deg k)
    rw [coe_mem_filtPiece, hg k, F.step_succ]
    exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)
  · intro c
    change filtPiece M₁ M₂ (F.step k.succ) c = filtPiece M₁ M₂ (F.step k.castSucc) c ⊔ _
    rw [F.step_succ, ← hg k, filtPiece_sup (hstab k.castSucc) (g k) c]
  · intro f d hf
    rw [F.mem_prime, ← hg k, smul_quotIota M₁ M₂ hf]
    exact (coe_mem_filtPiece _).symm

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial
open scoped Pointwise

noncomputable section

universe u w

section Lemmas

variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}

theorem xProd_ne_zero (I : Chart x) : xProd I ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun _ hi => (mem_support x).mp (I.2.2 hi)

theorem exists_mul_eq_prod_pow {J : Finset (Fin (N + 1))} {s : Poly k N} (hs : s ∈ monos J) :
    ∃ (t : Poly k N) (m d : ℕ), t.IsHomogeneous d ∧ s * t = (∏ i ∈ J, X i) ^ m := by
  classical
  induction hs using Submonoid.closure_induction with
  | mem a ha =>
    obtain ⟨i, hi, rfl⟩ := ha
    refine ⟨∏ i' ∈ J.erase i, X i', 1, ∑ _i' ∈ J.erase i, 1,
      IsHomogeneous.prod _ _ _ fun i' _ => isHomogeneous_X k i', ?_⟩
    rw [pow_one, Finset.mul_prod_erase J (fun i' => (X i' : Poly k N)) (Finset.mem_coe.mp hi)]
  | one => exact ⟨1, 0, 0, isHomogeneous_one _ _, by simp⟩
  | mul a b _ _ ha hb =>
    obtain ⟨t₁, m₁, d₁, ht₁, h₁⟩ := ha
    obtain ⟨t₂, m₂, d₂, ht₂, h₂⟩ := hb
    exact ⟨t₁ * t₂, m₁ + m₂, d₁ + d₂, ht₁.mul ht₂, by rw [pow_add, ← h₁, ← h₂]; ring⟩

theorem exists_mem_chartRing_mul_pow (I J : Chart x) {c : Ω} (hc : c ∈ chartRing k x J) :
    ∃ (c' : Ω) (m : ℕ), c' ∈ chartRing k x I ∧
      c = c' * (xProd I ^ J.1.card / xProd J ^ I.1.card) ^ m := by
  classical
  obtain ⟨f, s, e, hs, hf, hse, rfl⟩ := hc
  obtain ⟨t, m, d, ht, hst⟩ := exists_mul_eq_prod_pow (k := k) hs
  have hs0 := eval_ne_zero_of_mem_monos J hs
  have hJ0 : xProd J ≠ 0 := xProd_ne_zero J
  have hI0 : xProd I ≠ 0 := xProd_ne_zero I
  have hevJ : aeval x (∏ i ∈ J.1, (X i : Poly k N)) = xProd J := by simp [xProd, map_prod]
  have hevI : aeval x (∏ i ∈ I.1, (X i : Poly k N)) = xProd I := by simp [xProd, map_prod]
  have hst' : aeval x s * aeval x t = xProd J ^ m := by rw [← map_mul, hst, map_pow, hevJ]
  have ht0 : aeval x t ≠ 0 := right_ne_zero_of_mul (hst' ▸ pow_ne_zero m hJ0)
  have hpJ : (∏ i ∈ J.1, (X i : Poly k N)).IsHomogeneous J.1.card := by
    simpa using IsHomogeneous.prod J.1 (fun i => (X i : Poly k N)) (fun _ => 1)
      fun i _ => isHomogeneous_X k i
  have hpI : (∏ i ∈ I.1, (X i : Poly k N)).IsHomogeneous I.1.card := by
    simpa using IsHomogeneous.prod I.1 (fun i => (X i : Poly k N)) (fun _ => 1)
      fun i _ => isHomogeneous_X k i
  have hdeg : e + d = J.1.card * m := by
    have h2 : (s * t).IsHomogeneous (J.1.card * m) := by rw [hst]; exact hpJ.pow m
    have hne : s * t ≠ 0 := by
      rw [hst]
      exact pow_ne_zero _ fun h0 => hJ0 (by rw [← hevJ, h0, map_zero])
    exact (hse.mul ht).inj_right h2 hne
  obtain ⟨i', hi'⟩ : ∃ i', I.1.card = i' + 1 :=
    ⟨I.1.card - 1, (Nat.succ_pred_eq_of_pos I.2.1.card_pos).symm⟩
  refine ⟨aeval x (f * t * (∏ i ∈ J.1, X i) ^ (m * i')) /
      aeval x ((∏ i ∈ I.1, X i) ^ (m * J.1.card)), m,
    ⟨f * t * (∏ i ∈ J.1, X i) ^ (m * i'), (∏ i ∈ I.1, X i) ^ (m * J.1.card),
      I.1.card * (m * J.1.card),
      pow_mem (Submonoid.prod_mem _ fun i hi => X_mem_monos hi) _, ?_, hpI.pow _, rfl⟩, ?_⟩
  · have h3 := (hf.mul ht).mul (hpJ.pow (m * i'))
    convert h3 using 1
    rw [hdeg, hi']
    ring
  · have key : aeval x f / aeval x s = aeval x f * aeval x t / xProd J ^ m := by
      rw [← hst', mul_div_mul_right _ _ ht0]
    rw [key]
    simp only [map_mul, map_pow, hevJ, hevI]
    rw [hi', div_pow, ← pow_mul, ← pow_mul, div_mul_div_comm,
      div_eq_div_iff (pow_ne_zero _ hJ0) (mul_ne_zero (pow_ne_zero _ hI0) (pow_ne_zero _ hJ0))]
    ring

theorem ampleChart_mul {H : SubSystem k x Ω} {m : ℕ} {hh : Ω} {I : Chart x} {z₁ z₂ : Ω}
    (h₁ : z₁ ∈ ampleChart H m hh I) (h₂ : z₂ ∈ ampleChart H m hh I) :
    z₁ * z₂ ∈ ampleChart H m hh I := by
  obtain ⟨n₁, hn₁⟩ := h₁
  obtain ⟨n₂, hn₂⟩ := h₂
  refine ⟨n₁ + n₂, ?_⟩
  rw [SubSystem.pow_sub_eq_pow] at hn₁ hn₂ ⊢
  rw [mul_add, pow_add]
  have h3 := Submodule.mul_mem_mul hn₁ hn₂
  convert h3 using 1
  ring

theorem mem_ampleChart_of_mem_chartRing {H : SubSystem k x Ω} {m : ℕ} {hh : Ω} {I : Chart x}
    {c : Ω} (hc : c ∈ chartRing k x I) : c ∈ ampleChart H m hh I :=
  ⟨0, by
    rw [pow_zero, mul_one, mul_zero, SubSystem.pow_sub_eq_pow, pow_zero]
    exact Submodule.mem_one.mpr ⟨⟨c, hc⟩, rfl⟩⟩

theorem ampleChart_pow {H : SubSystem k x Ω} {m : ℕ} {hh : Ω} {I : Chart x} {z : Ω}
    (hz : z ∈ ampleChart H m hh I) (n : ℕ) : z ^ n ∈ ampleChart H m hh I := by
  induction n with
  | zero => rw [pow_zero]; exact mem_ampleChart_of_mem_chartRing (one_mem _)
  | succ n ih => rw [pow_succ]; exact ampleChart_mul ih hz

theorem exists_pow_mul_mem_ampleRing {L : SubSystem k x Ω} {hl b c : Ω} {J : Chart x}
    (hb : b ∈ ampleRing L 1 hl)
    (hbJ : ∀ I : Chart x, ∃ e : ℕ,
      b ^ e * (xProd I ^ J.1.card / xProd J ^ I.1.card) ∈ ampleChart L 1 hl I)
    (hc : c ∈ chartRing k x J) : ∃ E : ℕ, b ^ E * c ∈ ampleRing L 1 hl := by
  classical
  have hI : ∀ I : Chart x, ∃ E₀ : ℕ, ∀ E, E₀ ≤ E → b ^ E * c ∈ ampleChart L 1 hl I := by
    intro I
    obtain ⟨e, he⟩ := hbJ I
    obtain ⟨c', m, hc', hcc⟩ := exists_mem_chartRing_mul_pow I J hc
    have hbI : b ∈ ampleChart L 1 hl I := Set.mem_iInter.mp hb I
    refine ⟨e * m, fun E hE => ?_⟩
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hE
    have h4 : b ^ (e * m + d) * c =
        b ^ d * (c' * (b ^ e * (xProd I ^ J.1.card / xProd J ^ I.1.card)) ^ m) := by
      rw [hcc]; ring
    rw [h4]
    exact ampleChart_mul (ampleChart_pow hbI d)
      (ampleChart_mul (mem_ampleChart_of_mem_chartRing hc') (ampleChart_pow he m))
  choose E₀ hE₀ using hI
  exact ⟨∑ I, E₀ I, Set.mem_iInter.mpr fun I =>
    hE₀ I _ (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ I))⟩

variable {L G : SubSystem k x Ω} {r₁ s₁ : ℕ} {h : Fin (r₁ + 1) → Ω} {g : Fin (s₁ + 1) → Ω}

end Lemmas

end

end GroundTheory.Heights₂.Heights.Kleiman
end
