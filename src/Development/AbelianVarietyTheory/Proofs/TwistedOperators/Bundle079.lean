module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NotCompactOfIdempotent
public import Development.AbelianVarietyTheory.BlockTheory.AdelicCMFields.UnitaryHeckeCharacterIdele
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle019
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle003
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle018
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle002
public import Mathlib.MeasureTheory.Measure.Haar.MulEquivHaarChar
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AlgebraicValuesFinite.ClassSame
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AlgebraicValuesFinite.AlgValsFinMain
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AlgebraicValuesFinite.EvFLocalIdeleSelf
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.RingTheory.Coalgebra.CoassocSimps
import Mathlib.RingTheory.Henselian
import Mathlib.Order.CompletePartialOrder
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
import Mathlib.Tactic.Lemma
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

@[expose] public section

section

open GlobalTheory.RegSS Formalism.UG NumberField GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms
open scoped TensorProduct

namespace GlobalTheory.RegSS

theorem normOne_bounded_of_unit_bounded {B X : Type} [CommRing B] [CommRing X]
    [TopologicalSpace X] [IsTopologicalRing X] (i : B →+* X) (τ : B →+* B) (s : X →+* X)
    (hs : Continuous s) (hi : ∀ b, i (τ b) = s (i b))
    (hfin : ∀ D : Set X, IsCompact D → {β : B | i β ∈ D}.Finite)
    (D : Set X) (hD : IsCompact D)
    (h : ∀ u : X, u * s u = 1 → ∃ β : B, IsUnit β ∧ u * i β ∈ D) :
    ∃ D' : Set X, IsCompact D' ∧
      ∀ u : X, u * s u = 1 → ∃ β : B, β * τ β = 1 ∧ u * i β ∈ D' := by
  classical

  set K : Set X := (fun x => x * s x) '' D with hK
  have hKc : IsCompact K := hD.image (continuous_id.mul hs : Continuous fun x : X => x * s x)

  set T : Set B := {γ : B | i γ ∈ K} with hT
  have hTf : T.Finite := hfin K hKc

  let c : B → B := fun γ =>
    if h : ∃ p : B × B, p.1 * p.2 = 1 ∧ p.1 * τ p.1 = γ then (Classical.choose h).2 else 0
  refine ⟨⋃ γ ∈ T, (fun x => x * i (c γ)) '' D,
    hTf.isCompact_biUnion fun γ _ => hD.image (continuous_mul_const _), ?_⟩
  intro u hu
  obtain ⟨β, hβ, hβD⟩ := h u hu
  obtain ⟨β', hβ'⟩ := hβ.exists_right_inv
  have hex : ∃ p : B × B, p.1 * p.2 = 1 ∧ p.1 * τ p.1 = β * τ β := ⟨(β, β'), hβ', rfl⟩
  set p := Classical.choose hex with hpdef
  have hp : p.1 * p.2 = 1 ∧ p.1 * τ p.1 = β * τ β := Classical.choose_spec hex
  have hc : c (β * τ β) = p.2 := by
    show (if h : ∃ q : B × B, q.1 * q.2 = 1 ∧ q.1 * τ q.1 = β * τ β
      then (Classical.choose h).2 else 0) = p.2
    rw [dite_eq_left hex]

  refine ⟨β * p.2, ?_, ?_⟩
  · calc β * p.2 * τ (β * p.2) = (β * τ β) * (p.2 * τ p.2) := by rw [map_mul]; ring
      _ = (p.1 * τ p.1) * (p.2 * τ p.2) := by rw [hp.2]
      _ = (p.1 * p.2) * τ (p.1 * p.2) := by rw [map_mul τ p.1 p.2]; ring
      _ = 1 := by rw [hp.1, map_one, one_mul]
  · have hmem : β * τ β ∈ T := by
      show i (β * τ β) ∈ K
      refine ⟨u * i β, hβD, ?_⟩
      show u * i β * s (u * i β) = i (β * τ β)
      rw [map_mul s, map_mul i, hi]
      calc u * i β * (s u * s (i β)) = (u * s u) * (i β * s (i β)) := by ring
        _ = i β * s (i β) := by rw [hu, one_mul]
    refine Set.mem_biUnion hmem ⟨u * i β, hβD, ?_⟩
    show u * i β * i (c (β * τ β)) = u * i (β * p.2)
    rw [hc, map_mul i, mul_assoc]

theorem normOfUnitBounded_of_tensorLattice :
    GlobalTheory.RegSS.TensorLattice → GlobalTheory.RegSS.NormOfUnitBounded := by
  intro hL F B _ _ _ _ _ τ hU
  let _ : TopologicalSpace (B ⊗[F] AdeleRing (𝓞 F) F) :=
    Formalism.BasicNotions.tensTopL (F := F) (E := B) (AdeleRing (𝓞 F) F)
  obtain ⟨hTR, -, -, -, -, hfin, -⟩ := hL F B
  have := hTR
  obtain ⟨D, hD, hDu⟩ := hU
  exact normOne_bounded_of_unit_bounded (inclE (F := F) (AdeleRing (𝓞 F) F)) (τ : B →+* B)
    (sigR τ (AdeleRing (𝓞 F) F)) (continuous_sigR τ _) (fun b => inclE_conj τ _ b) hfin D hD hDu

end GlobalTheory.RegSS
end

section

noncomputable section

open Matrix Formalism.UG NumberField GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele IsDedekindDomain
open scoped TensorProduct

namespace GlobalTheory.RegSS

theorem bddAbove_of_compact_quotient {G : Type} [Group G] [TopologicalSpace G] (H : Subgroup G)
    [CompactSpace (G ⧸ H)] (f : G →* ℝ) (hf : Continuous f) (hH : ∀ h ∈ H, f h = 1) :
    ∃ C : ℝ, ∀ g, f g ≤ C := by
  let φ : G ⧸ H → ℝ := Quotient.lift f fun a b hab => by
    have h := hH _ (QuotientGroup.leftRel_apply.1 hab)
    rw [← mul_one (f a), ← h, ← map_mul, mul_inv_cancel_left]
  have hφ : Continuous φ := hf.quotient_lift _
  obtain ⟨C, hC⟩ := (isCompact_range hφ).bddAbove
  exact ⟨C, fun g => hC ⟨(g : G ⧸ H), rfl⟩⟩

theorem exists_one_lt_ideleNorm (F : Type) [Field F] [NumberField F] :
    ∃ t : Idele F, 1 < ideleNorm t := by
  obtain ⟨m, hm⟩ := Ideal.exists_maximal (𝓞 F)
  let P : HeightOneSpectrum (𝓞 F) :=
    ⟨m, hm.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hm (RingOfIntegers.not_isField F)⟩
  obtain ⟨ϖ, hϖ⟩ := exists_isUniformiser P
  have h1 : ‖(ϖ : P.adicCompletion F)‖ = (Ideal.absNorm P.asIdeal : ℝ)⁻¹ := by
    rw [FinitePlace.norm_def, hϖ, WithZeroMulInt.toNNReal_neg_apply _ WithZero.exp_ne_zero]
    simp
  refine ⟨(localIdele P ϖ)⁻¹, ?_⟩
  rw [map_inv, UnitaryHeckeChar.ideleNorm_localIdele, h1, inv_inv]
  exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm P

theorem commute_map_of_mem_centPts {F E : Type} [Field F] [CommRing E] [Algebra F E]
    {n : Type} [Fintype n] [DecidableEq n] {σ : E →ₐ[F] E} {J : Matrix n n E} {γ : GL n E}
    (R : Type) [CommRing R] [Algebra F R] {ε : Matrix n n E} (hε : ε ∈ genAlg (γ : Matrix n n E))
    {g : GL n (E ⊗[F] R)} (hg : g ∈ centPts σ J γ R) :
    (g : Matrix n n (E ⊗[F] R)) * ε.map (inclE (F := F) R) = ε.map (inclE (F := F) R) * g := by
  have h : (g : Matrix n n (E ⊗[F] R)) * (γ : Matrix n n E).map (inclE (F := F) R) =
      (γ : Matrix n n E).map (inclE (F := F) R) * g :=
    congrArg Units.val (Subgroup.mem_centralizer_singleton_iff.1 hg.2)
  refine commute_of_mem_genAlg h ?_
  induction hε using Algebra.adjoin_induction with
  | mem x hx =>
    rw [Set.mem_singleton_iff.1 hx]; exact Algebra.self_mem_adjoin_singleton _ _
  | algebraMap r =>
    have : (algebraMap E (Matrix n n E) r).map (inclE (F := F) R) =
        algebraMap (E ⊗[F] R) _ (inclE (F := F) R r) := by
      ext i j
      by_cases hij : i = j <;> simp [Matrix.algebraMap_matrix_apply, hij]
    rw [this]; exact Subalgebra.algebraMap_mem _ _
  | add x y _ _ hx hy =>
    rw [Matrix.map_add _ (map_add _)]; exact add_mem hx hy
  | mul x y _ _ hx hy =>
    rw [Matrix.map_mul]; exact mul_mem hx hy

theorem notCompactOfIdempotent_of (hD : IdempotentDet) : NotCompactOfIdempotent := by
  intro F E _ _ _ _ n _ _ σ J γ hreg ε hε hε0 hεε ht hc
  haveI := quad_finite hreg.quad
  letI : TopologicalSpace (E ⊗[F] AdeleRing (𝓞 F) F) :=
    Formalism.BasicNotions.tensTopL (F := F) (E := E) (AdeleRing (𝓞 F) F)
  obtain ⟨d, χ, hd, hχ, h1, hmul, hrat, hval⟩ := hD F E n ε hε0 hεε (AdeleRing (𝓞 F) F)
  let χ₀ : centPts σ J γ (AdeleRing (𝓞 F) F) →* AdeleRing (𝓞 F) F :=
    { toFun := fun g => χ (g.1 : Matrix n n _)
      map_one' := h1
      map_mul' := fun g h => hmul _ _ (commute_map_of_mem_centPts _ hε h.2) }
  have hχ₀ : Continuous χ₀ := hχ.comp (Units.continuous_val.comp continuous_subtype_val)
  have hχi : Continuous fun g => χ₀ g⁻¹ :=
    hχ.comp (Units.continuous_coe_inv.comp continuous_subtype_val)
  have hχ₁ : Continuous χ₀.toHomUnits := Units.continuous_iff.2 ⟨hχ₀, hχi⟩
  haveI : CompactSpace (centPts σ J γ (AdeleRing (𝓞 F) F) ⧸
    ((centRat σ J γ).map (bc (inclE (F := F) (AdeleRing (𝓞 F) F)))).subgroupOf
      (centPts σ J γ (AdeleRing (𝓞 F) F))) := hc
  obtain ⟨C, hC⟩ := bddAbove_of_compact_quotient
    (((centRat σ J γ).map (bc (inclE (F := F) (AdeleRing (𝓞 F) F)))).subgroupOf
      (centPts σ J γ (AdeleRing (𝓞 F) F))) (ideleNorm.comp χ₀.toHomUnits)
    (continuous_ideleNorm.comp hχ₁) (by
      rintro g ⟨δ, -, hδ⟩
      obtain ⟨c, hc⟩ := hrat δ
      have e : ((χ₀.toHomUnits g : Idele F) : AdeleRing (𝓞 F) F) = algebraMap F _ c := by
        rw [← hc]
        change χ (g.1 : Matrix n n _) = _
        rw [show g.1 = _ from hδ.symm]
        rfl
      have hc0 : c ≠ 0 := by
        rintro rfl
        rw [map_zero] at e
        haveI : Nontrivial (AdeleRing (𝓞 F) F) := (AdeleRing.algebraMap_injective (𝓞 F) F).nontrivial
        exact Units.ne_zero _ e
      have e' : χ₀.toHomUnits g = principalIdele F (Units.mk0 c hc0) := Units.ext e
      rw [MonoidHom.comp_apply, e', ideleNorm_principalIdele])
  obtain ⟨t, ht1⟩ := exists_one_lt_ideleNorm F
  obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt C (one_lt_pow₀ ht1 hd.ne')
  obtain ⟨g, hg, hgt⟩ := ht (t ^ m)
  have e : χ₀.toHomUnits ⟨g, hg⟩ = (t ^ m) ^ d := Units.ext (hval _ _ hgt)
  have := hC ⟨g, hg⟩
  rw [MonoidHom.comp_apply, e, map_pow, map_pow, ← pow_mul, mul_comm, pow_mul] at this
  exact absurd hm (not_lt.2 this)

end GlobalTheory.RegSS
end
end

section

open GlobalTheory.RegSS

open Formalism.UG NumberField Topology
open scoped TensorProduct

namespace GlobalTheory.RegSSLattice

open NumberField Topology in
open scoped TensorProduct in
private lemma finite_setOf_algebraMap_mem_of_isCompact (F : Type) [Field F] [NumberField F]
    {K : Set (AdeleRing (𝓞 F) F)} (hK : IsCompact K) :
    {c : F | algebraMap F (AdeleRing (𝓞 F) F) c ∈ K}.Finite := by
  obtain ⟨U, hU, hUF⟩ := _root_.GlobalTheory.AdeleDiscrete.exists_nhds_zero_principal_eq_zero F
  have hsub : Filter.Tendsto (fun p : AdeleRing (𝓞 F) F × AdeleRing (𝓞 F) F => p.1 - p.2)
      (𝓝 (0, 0)) (𝓝 0) :=
    (continuous_fst.sub continuous_snd).tendsto' _ _ (by simp)
  have hpre : (fun p : AdeleRing (𝓞 F) F × AdeleRing (𝓞 F) F => p.1 - p.2) ⁻¹' U ∈
      𝓝 ((0 : AdeleRing (𝓞 F) F), (0 : AdeleRing (𝓞 F) F)) := hsub hU
  rw [nhds_prod_eq] at hpre
  obtain ⟨V, hV, W, hW, hVW⟩ := Filter.mem_prod_iff.mp hpre
  have hVU : ∀ v ∈ V ∩ W, ∀ w ∈ V ∩ W, v - w ∈ U := fun v hv w hw =>
    hVW (Set.mk_mem_prod hv.1 hw.2)
  obtain ⟨t, -, ht⟩ := hK.elim_nhds_subcover (fun k => {y | y - k ∈ V ∩ W}) fun k _ =>
    (continuous_id.sub continuous_const).continuousAt.preimage_mem_nhds
      (by simpa using Filter.inter_mem hV hW)
  refine (t.finite_toSet.biUnion
    (t := fun k => {c : F | algebraMap F (AdeleRing (𝓞 F) F) c - k ∈ V ∩ W})
    fun k _ => ?_).subset fun c hc => ?_
  · refine Set.Subsingleton.finite fun c hc c' hc' => ?_
    have := hUF (c - c') (by simpa [map_sub] using hVU _ hc _ hc')
    exact sub_eq_zero.mp this
  · simpa using ht hc


open NumberField Topology in
open scoped TensorProduct in
theorem _root_.GlobalTheory.RegSSLattice.tensorLattice : _root_.GlobalTheory.RegSS.TensorLattice := by
  unfold _root_.GlobalTheory.RegSS.TensorLattice
  intro F B _ _ _ _ _
  haveI := _root_.GlobalTheory.AdelicUnitaryTop.locallyCompact_adele F
  haveI := _root_.GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  haveI := _root_.GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  obtain ⟨U, hU, hUF⟩ := _root_.GlobalTheory.AdeleDiscrete.exists_nhds_zero_principal_eq_zero F
  haveI : Nontrivial (AdeleRing (𝓞 F) F) := ⟨⟨0, 1, fun h01 => one_ne_zero
    (hUF 1 (by rw [map_one, ← h01]; exact mem_of_mem_nhds hU))⟩⟩
  letI : Algebra (AdeleRing (𝓞 F) F) (B ⊗[F] AdeleRing (𝓞 F) F) :=
    Algebra.TensorProduct.rightAlgebra
  letI : TopologicalSpace (B ⊗[F] AdeleRing (𝓞 F) F) := _root_.Formalism.BasicNotions.tensTopL (AdeleRing (𝓞 F) F)
  haveI : IsModuleTopology (AdeleRing (𝓞 F) F) (B ⊗[F] AdeleRing (𝓞 F) F) := ⟨rfl⟩
  haveI : ContinuousAdd (B ⊗[F] AdeleRing (𝓞 F) F) :=
    IsModuleTopology.toContinuousAdd (AdeleRing (𝓞 F) F) _
  let b := Module.finBasis F B
  let c : B ⊗[F] AdeleRing (𝓞 F) F ≃ₗ[AdeleRing (𝓞 F) F] AdeleRing (𝓞 F) F ⊗[F] B :=
    { TensorProduct.comm F B (AdeleRing (𝓞 F) F) with
      map_smul' := fun a t => by
        induction t using TensorProduct.induction_on with
        | zero => simp
        | tmul x y =>
          change TensorProduct.comm F B _ (a • (x ⊗ₜ y)) = a • TensorProduct.comm F B _ (x ⊗ₜ y)
          rw [Algebra.smul_def]
          simp [Algebra.TensorProduct.right_algebraMap_apply, TensorProduct.smul_tmul', mul_comm]
        | add x y hx hy => simp_all [smul_add] }
  let e := c.trans (Algebra.TensorProduct.basis (AdeleRing (𝓞 F) F) b).equivFun
  haveI : Module.Finite (AdeleRing (𝓞 F) F) (B ⊗[F] AdeleRing (𝓞 F) F) :=
    Module.Finite.of_basis ((Algebra.TensorProduct.basis (AdeleRing (𝓞 F) F) b).map c.symm)
  let h : B ⊗[F] AdeleRing (𝓞 F) F ≃L[AdeleRing (𝓞 F) F]
      (Fin (Module.finrank F B) → AdeleRing (𝓞 F) F) :=
    { e with
      continuous_toFun := IsModuleTopology.continuous_of_linearMap e.toLinearMap
      continuous_invFun := IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap }
  have he : ∀ β : B, h (_root_.Formalism.UG.inclE (AdeleRing (𝓞 F) F) β) =
      fun i => algebraMap F (AdeleRing (𝓞 F) F) (b.equivFun β i) := by
    intro β
    ext i
    show e (β ⊗ₜ 1) i = _
    simp [e, c, Algebra.TensorProduct.basis_repr_tmul]
  refine ⟨IsModuleTopology.isTopologicalRing (AdeleRing (𝓞 F) F) _,
    h.toHomeomorph.isClosedEmbedding.locallyCompactSpace, h.toHomeomorph.isEmbedding.t2Space,
    h.toHomeomorph.secondCountableTopology, _root_.Formalism.UG.P.inclE_injective F B (AdeleRing (𝓞 F) F), ?_, ?_⟩
  · intro D hD
    have hD' : IsCompact (h '' D) := hD.image h.continuous
    refine ((Set.Finite.pi (t := fun i => {x : F | algebraMap F (AdeleRing (𝓞 F) F) x ∈
      (fun y => y i) '' (h '' D)}) fun i => finite_setOf_algebraMap_mem_of_isCompact F
        (hD'.image (continuous_apply i))).preimage b.equivFun.injective.injOn).subset ?_
    intro β hβ
    simp only [Set.mem_preimage, Set.mem_univ_pi, Set.mem_setOf_eq]
    intro i
    exact ⟨h (_root_.Formalism.UG.inclE (AdeleRing (𝓞 F) F) β), ⟨_, hβ, rfl⟩, by rw [he]⟩
  · obtain ⟨K, hK, hKF⟩ := _root_.GlobalTheory.AdeleCocompact.exists_compact_adele F
    refine ⟨h.symm '' Set.univ.pi fun _ => K,
      (isCompact_univ_pi fun _ => hK).image h.symm.continuous, fun x => ?_⟩
    choose y hy using fun i => hKF (h x i)
    refine ⟨b.equivFun.symm y, h (x - _root_.Formalism.UG.inclE (AdeleRing (𝓞 F) F) (b.equivFun.symm y)), ?_,
      by simp⟩
    intro i _
    rw [map_sub, he, LinearEquiv.apply_symm_apply]
    simpa using hy i

end GlobalTheory.RegSSLattice
end

section

open MeasureTheory MeasureTheory.Measure GlobalTheory.RegSS
open scoped NNReal ENNReal

namespace GlobalTheory.RegSS

theorem measure_le_of_sub_mem_imp_eq {X : Type} [AddCommGroup X] [MeasurableSpace X]
    [MeasurableAdd X] (μ : Measure X) [μ.IsAddLeftInvariant] (Λ : AddSubgroup X) [Countable Λ]
    (C S : Set X) (hCm : MeasurableSet C) (hC : ∀ x, ∃ l ∈ Λ, x - l ∈ C) (hS : MeasurableSet S)
    (h : ∀ x ∈ S, ∀ y ∈ S, x - y ∈ Λ → x = y) : μ S ≤ μ C := by
  let A : Λ → Set X := fun l => (fun x => (l : X) + x) ⁻¹' S ∩ C
  have hAm : ∀ l, MeasurableSet (A l) := fun l =>
    ((measurable_const_add (l : X)) hS).inter hCm
  have hdisj : Pairwise (Function.onFun Disjoint A) := by
    intro l m hlm
    rw [Function.onFun, Set.disjoint_left]
    rintro x ⟨hx, -⟩ ⟨hx', -⟩
    apply hlm
    have := h _ hx _ hx' (by simpa using Λ.sub_mem l.2 m.2)
    exact Subtype.ext (add_right_cancel this)
  have hcov : S ⊆ ⋃ l : Λ, (fun x => -(l : X) + x) ⁻¹' A l := by
    intro x hx
    obtain ⟨l, hl, hxl⟩ := hC x
    refine Set.mem_iUnion.2 ⟨⟨l, hl⟩, ?_, ?_⟩
    · simpa using hx
    · simpa [neg_add_eq_sub] using hxl
  calc μ S ≤ μ (⋃ l : Λ, (fun x => -(l : X) + x) ⁻¹' A l) := measure_mono hcov
    _ ≤ ∑' l : Λ, μ ((fun x => -(l : X) + x) ⁻¹' A l) := measure_iUnion_le _
    _ = ∑' l : Λ, μ (A l) := by simp_rw [measure_preimage_add]
    _ = μ (⋃ l, A l) := (measure_iUnion hdisj hAm).symm
    _ ≤ μ C := measure_mono (Set.iUnion_subset fun l => Set.inter_subset_right)

theorem measure_preimage_mul_of_norm_one {X : Type} [CommRing X] [TopologicalSpace X]
    [IsTopologicalRing X] [LocallyCompactSpace X] [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) [μ.IsAddHaarMeasure] [μ.Regular] (τ : X →+* X) (hτ : Continuous τ)
    (hττ : ∀ x, τ (τ x) = x) (u : X) (hu : u * τ u = 1) (S : Set X) :
    μ ((fun x => u * x) ⁻¹' S) = μ S := by
  let T : X ≃ₜ+ X :=
    { toFun := τ, invFun := τ, left_inv := hττ, right_inv := hττ, map_add' := map_add τ,
      continuous_toFun := hτ, continuous_invFun := hτ }
  let M : X ≃ₜ+ X :=
    { toFun := fun x => u * x, invFun := fun x => τ u * x,
      left_inv := fun x => by simp only [← mul_assoc, mul_comm (τ u) u, hu, one_mul],
      right_inv := fun x => by simp only [← mul_assoc, hu, one_mul],
      map_add' := mul_add u,
      continuous_toFun := continuous_const_mul u, continuous_invFun := continuous_const_mul _ }
  have h1 : T.trans T = ContinuousAddEquiv.refl X := by
    ext x; exact hττ x
  have h2 : (T.trans M).trans (T.trans M) = ContinuousAddEquiv.refl X := by
    ext x
    change u * τ (u * τ x) = x
    rw [map_mul, hττ, ← mul_assoc, hu, one_mul]
  have e1 := congrArg addEquivAddHaarChar h1
  have e2 := congrArg addEquivAddHaarChar h2
  simp only [addEquivAddHaarChar_trans, addEquivAddHaarChar_refl] at e1 e2
  have e3 : addEquivAddHaarChar M * addEquivAddHaarChar M = 1 := by
    rw [← e2, mul_mul_mul_comm, e1, one_mul]
  have e4 : addEquivAddHaarChar M = 1 := by
    have := (pow_eq_one_iff_of_nonneg (a := addEquivAddHaarChar M) zero_le two_ne_zero).1
      (by rw [sq, e3])
    exact this
  have := addEquivAddHaarChar_smul_preimage μ (X := S) M
  rw [e4, one_smul] at this
  exact this

theorem normOnePacking : NormOnePacking := by
  intro X _ _ _ _ _ _ _ τ hτ hττ Λ hΛ ⟨C, hCc, hC⟩
  borelize X
  let μ : Measure X := addHaar
  have huniv : μ Set.univ = ∞ := measure_univ_of_isAddLeftInvariant μ
  obtain ⟨K, -, hKc, hK⟩ := isOpen_univ.exists_lt_isCompact (μ := μ) (r := μ C)
    (by rw [huniv]; exact hCc.measure_lt_top)
  refine ⟨(fun p : X × X => p.1 - p.2) '' (K ×ˢ K), (hKc.prod hKc).image (by fun_prop), ?_⟩
  intro u hu
  by_contra hcon
  have hle := measure_le_of_sub_mem_imp_eq μ Λ C ((fun x => u * x) ⁻¹' K) hCc.measurableSet hC
    ((continuous_const_mul u).measurable hKc.measurableSet) (by
      intro x hx y hy hxy
      by_contra hne
      exact hcon ⟨x - y, hxy, sub_ne_zero.2 hne, (u * x, u * y), ⟨hx, hy⟩, (mul_sub u x y).symm⟩)
  rw [measure_preimage_mul_of_norm_one μ τ hτ hττ u hu] at hle
  exact absurd hK (not_lt.2 hle)

end GlobalTheory.RegSS
end

section

open NumberField IsDedekindDomain Formalism.L2.Host

noncomputable section

open Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR

namespace GlobalTheory.HeckeLocDec

theorem localIdele_unitPart_mem (L : Type) [Field L] [NumberField L] (w : HeightOneSpectrum (𝓞 L))
    (x : (w.adicCompletion L)ˣ) (a : ℤ) (ha : Valued.v (x : w.adicCompletion L) = WithZero.exp (-a)) :
    localIdele L w (x * (atFin w (unif w)) ^ (-a)) ∈ PI.AlgValsFin.W.UFin L := by
  refine ⟨?_, fun w' => ?_⟩
  · funext v
    exact (localIdele_isSupportedAt L w _).1 v
  · by_cases h : w' = w
    · subst h
      rw [← PI.AlgValsFin.W.evF_val, PI.AlgValsFin.W.evF_localIdele_self]
      have h1 : Valued.v ((atFin w' (unif w') : (w'.adicCompletion L)ˣ) : w'.adicCompletion L) =
          WithZero.exp (-1) := unif_spec w'
      rw [Units.val_mul, Units.val_zpow_eq_zpow_val, map_mul, map_zpow₀, h1, ha,
        ← WithZero.exp_zsmul, ← WithZero.exp_add]
      simp
    · rw [← PI.AlgValsFin.W.evF_val, PI.AlgValsFin.W.evF_localIdele_ne w' w h]
      simp

theorem loc_div_val_pow (L : Type) [Field L] [NumberField L] (χ : HChar L) :
    ∃ N : ℕ, 0 < N ∧ ∀ (w : HeightOneSpectrum (𝓞 L)) (x : (w.adicCompletion L)ˣ),
      ∃ a : ℤ, ((χ.loc w x / χ.val w ^ a : ℂˣ) : ℂ) ^ N = 1 := by
  obtain ⟨N, hN, hT⟩ := PI.AlgValsFin.W.torsUnits L χ
  refine ⟨N, hN, fun w x => ?_⟩
  have hx0 : Valued.v (x : w.adicCompletion L) ≠ 0 := by simp
  obtain ⟨a, ha⟩ : ∃ a : ℤ, Valued.v (x : w.adicCompletion L) = WithZero.exp (-a) :=
    ⟨-WithZero.log (Valued.v (x : w.adicCompletion L)), by rw [neg_neg, WithZero.exp_log hx0]⟩
  refine ⟨a, ?_⟩
  have hmem := localIdele_unitPart_mem L w x a ha
  have h := hT _ hmem
  have e : χ.loc w x / χ.val w ^ a = χ.1 (localIdele L w (x * (atFin w (unif w)) ^ (-a))) := by
    show χ.loc w x / χ.loc w (atFin w (unif w)) ^ a = χ.loc w (x * (atFin w (unif w)) ^ (-a))
    rw [map_mul, map_zpow, zpow_neg, div_eq_mul_inv]
  rw [e, ← Units.val_pow_eq_pow_val, h, Units.val_one]

end GlobalTheory.HeckeLocDec
end
end
