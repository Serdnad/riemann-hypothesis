module

import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle015
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.NumberTheory.LocalField.Basic
public import Mathlib.Topology.Instances.Matrix
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ProductFormulaHaar.Bundle001
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle002
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.Padics.Complex
public import Development.AbelianVarietyTheory.BlockTheory.CMModuli.ProjectiveSpaceOverSpec
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle001
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OmegaFactorization
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle001
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Rat
import Mathlib.Algebra.Ring.IsFormallyReal
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
import Mathlib.Geometry.Manifold.StructureGroupoid

@[expose] public section

section

open Filter Topology ValuativeRel

noncomputable section

namespace GlobalTheory.LinSchurLatt

theorem eq_one_of_pow_near (z : ℂ) (h : ∀ m : ℕ, ‖z ^ m - 1‖ ≤ 1 / 2) : z = 1 := by
  apply GlobalTheory.ConductorAdicCompletion.eq_one_of_pow_near_one <;> assumption

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem valuation_natCast_le_one (m : ℕ) : valuation k (m : k) ≤ 1 :=
  (Valuation.mem_integer_iff _ _).1 (natCast_mem (valuation k).integer m)

theorem ker_int_mem_nhds (ψ0 : AddChar k ℂ) (hc : Continuous ψ0) :
    {u : k | ∀ o : k, valuation k o ≤ 1 → ψ0 (o * u) = 1} ∈ 𝓝 (0 : k) := by
  have hO : IsCompact {x : k | valuation k x ≤ 1} := IsNonarchimedeanLocalField.isCompact_closedBall k 1
  have hU : {u : k | ‖ψ0 u - 1‖ ≤ 1 / 2} ∈ 𝓝 (0 : k) := by
    have h1 : Metric.closedBall (ψ0 0) (1 / 2) ∈ 𝓝 (ψ0 0) := Metric.closedBall_mem_nhds _ (by norm_num)
    filter_upwards [hc.continuousAt.preimage_mem_nhds h1] with u hu
    simpa [Metric.mem_closedBall, dist_eq_norm, AddChar.map_zero_eq_one] using hu
  have hev : ∀ᶠ w in 𝓝 (0 : k), ∀ a ∈ {x : k | valuation k x ≤ 1}, a * w ∈ {u : k | ‖ψ0 u - 1‖ ≤ 1 / 2} := by
    refine hO.eventually_forall_of_forall_eventually fun a _ => ?_
    have hcm : Continuous fun z : k × k => z.2 * z.1 := continuous_snd.mul continuous_fst
    have h0 : (fun z : k × k => z.2 * z.1) (0, a) = 0 := by simp
    exact hcm.continuousAt.preimage_mem_nhds (by simpa using hU)
  filter_upwards [hev] with w hw o ho
  apply eq_one_of_pow_near
  intro m
  have hmo : valuation k ((m : k) * o) ≤ 1 := by
    rw [map_mul]
    exact mul_le_one' (valuation_natCast_le_one m) ho
  have h1 := hw _ hmo
  have h2 : (m : k) * o * w = m • (o * w) := by rw [nsmul_eq_mul, mul_assoc]
  rwa [h2, AddChar.map_nsmul_eq_pow] at h1

theorem ker_int_lt {ψ0 : AddChar k ℂ} {t : k} (ht : ψ0 t ≠ 1) {u : k}
    (hu : ∀ o : k, valuation k o ≤ 1 → ψ0 (o * u) = 1) : valuation k u < valuation k t := by
  by_contra h
  push_neg at h
  have hu0 : u ≠ 0 := by
    rintro rfl
    apply ht
    have : t = 0 := by simpa using h
    rw [this, AddChar.map_zero_eq_one]
  have hvu : valuation k u ≠ 0 := by simpa using hu0
  apply ht
  have hle : valuation k (t / u) ≤ 1 := by
    rw [map_div₀, div_eq_mul_inv]
    calc valuation k t * (valuation k u)⁻¹ ≤ valuation k u * (valuation k u)⁻¹ := by gcongr
      _ = 1 := mul_inv_cancel₀ hvu
  have := hu (t / u) hle
  rwa [div_mul_cancel₀ _ hu0] at this

theorem nhdsNE_neBot' : (𝓝[≠] (0 : k)).NeBot := by
  letI := IsTopologicalAddGroup.rightUniformSpace k
  haveI := isUniformAddGroup_of_addCommGroup (G := k)
  letI : (Valued.v (R := k)).RankOne :=
  { hom' := IsRankLeOne.nonempty.some.emb (R := k).comp MonoidWithZeroHom.ValueGroup₀.embedding
    strictMono' := IsRankLeOne.nonempty.some.strictMono.comp
        MonoidWithZeroHom.ValueGroup₀.embedding_strictMono }
  open scoped Valued in
  exact NormedField.nhdsNE_neBot (0 : k)

theorem isCompact_ball_mat (n d : ℕ) (γ : ValueGroupWithZero k) :
    IsCompact {x : Matrix (Fin n) (Fin d) k | ∀ i j, valuation k (x i j) ≤ γ} := by
  have : {x : Matrix (Fin n) (Fin d) k | ∀ i j, valuation k (x i j) ≤ γ} =
      Set.univ.pi fun _ => Set.univ.pi fun _ => {x : k | valuation k x ≤ γ} := by
    ext x
    exact ⟨fun h i _ j _ => h i j, fun h i j => h i (Set.mem_univ _) j (Set.mem_univ _)⟩
  rw [this]
  exact isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => IsNonarchimedeanLocalField.isCompact_closedBall k γ

theorem exists_smul_int_mem' (n d : ℕ) (W : Set (Matrix (Fin n) (Fin d) k)) (hW : W ∈ 𝓝 0) :
    ∃ c : k, c ≠ 0 ∧ ∀ x : Matrix (Fin n) (Fin d) k, (∀ i j, valuation k (x i j) ≤ 1) → c • x ∈ W := by
  have hev : ∀ᶠ c in 𝓝 (0 : k), ∀ x ∈ {x : Matrix (Fin n) (Fin d) k | ∀ i j, valuation k (x i j) ≤ 1}, c • x ∈ W := by
    refine (isCompact_ball_mat n d 1).eventually_forall_of_forall_eventually fun y _ => ?_
    have hc : Continuous fun z : k × Matrix (Fin n) (Fin d) k => z.1 • z.2 := continuous_fst.smul continuous_snd
    have h0 : (fun z : k × Matrix (Fin n) (Fin d) k => z.1 • z.2) (0, y) = 0 := by simp
    exact hc.continuousAt.preimage_mem_nhds (by simpa using hW)
  haveI := nhdsNE_neBot' (k := k)
  obtain ⟨c, hc1, hc2⟩ := ((hev.filter_mono (nhdsWithin_le_nhds (s := {(0 : k)}ᶜ))).and
    (self_mem_nhdsWithin (s := {(0 : k)}ᶜ))).exists
  exact ⟨c, hc2, fun x hx => hc1 x hx⟩

end GlobalTheory.LinSchurLatt

namespace GlobalTheory.LinSchurLatt

theorem latt_open_compact_basis : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n d : ℕ) (ψ0 : AddChar k ℂ), Continuous ψ0 → ψ0 ≠ 1 → (∀ s : k, s ≠ 0 → IsOpen (GlobalTheory.LinSchur.latt ψ0 n d s : Set (Matrix (Fin n) (Fin d) k)) ∧ IsCompact (GlobalTheory.LinSchur.latt ψ0 n d s : Set (Matrix (Fin n) (Fin d) k))) ∧ ∀ W ∈ 𝓝 (0 : Matrix (Fin n) (Fin d) k), ∃ s : k, s ≠ 0 ∧ (GlobalTheory.LinSchur.latt ψ0 n d s : Set (Matrix (Fin n) (Fin d) k)) ⊆ W := by
  intro k _ _ _ _ n d ψ0 hc hne
  obtain ⟨t, ht⟩ : ∃ t, ψ0 t ≠ 1 := by
    by_contra h
    push_neg at h
    exact hne (AddChar.ext _ _ fun x => by rw [h x, AddChar.one_apply])
  have ht0 : t ≠ 0 := by
    rintro rfl
    exact ht (AddChar.map_zero_eq_one ψ0)
  have hvt : valuation k t ≠ 0 := by simpa using ht0
  have hK := ker_int_mem_nhds ψ0 hc
  refine ⟨fun s hs => ⟨?_, ?_⟩, fun W hW => ?_⟩
  · apply AddSubgroup.isOpen_of_mem_nhds (g := 0)
    have hev : ∀ᶠ Y in 𝓝 (0 : Matrix (Fin n) (Fin d) k), ∀ i j,
        s * Y i j ∈ {u : k | ∀ o : k, valuation k o ≤ 1 → ψ0 (o * u) = 1} := by
      refine eventually_all.2 fun i => eventually_all.2 fun j => ?_
      have hcont : Continuous fun Y : Matrix (Fin n) (Fin d) k => s * Y i j :=
        continuous_const.mul (continuous_id.matrix_elem i j)
      exact hcont.continuousAt.preimage_mem_nhds (by simpa using hK)
    filter_upwards [hev] with Y hY
    exact GlobalTheory.LinSchur.mem_latt.2 fun i j o ho => hY i j o ho
  · have hsub : (GlobalTheory.LinSchur.latt ψ0 n d s : Set (Matrix (Fin n) (Fin d) k)) ⊆
        {x : Matrix (Fin n) (Fin d) k | ∀ i j, valuation k (x i j) ≤ valuation k t * (valuation k s)⁻¹} := by
      intro Y hY i j
      have h1 := ker_int_lt ht fun o ho => GlobalTheory.LinSchur.mem_latt.1 hY i j o ho
      have hvs : valuation k s ≠ 0 := by simpa using hs
      rw [map_mul] at h1
      calc valuation k (Y i j) = valuation k s * valuation k (Y i j) * (valuation k s)⁻¹ := by
            rw [mul_comm (valuation k s), mul_assoc, mul_inv_cancel₀ hvs, mul_one]
        _ ≤ valuation k t * (valuation k s)⁻¹ := by gcongr
    have hcl : IsClosed (GlobalTheory.LinSchur.latt ψ0 n d s : Set (Matrix (Fin n) (Fin d) k)) := by
      have e : (GlobalTheory.LinSchur.latt ψ0 n d s : Set (Matrix (Fin n) (Fin d) k)) =
          ⋂ i, ⋂ j, ⋂ o : {o : k // valuation k o ≤ 1}, {Y | ψ0 (o.1 * (s * Y i j)) = 1} := by
        ext Y
        simp only [SetLike.mem_coe, GlobalTheory.LinSchur.mem_latt, Set.mem_iInter, Set.mem_setOf_eq, Subtype.forall]
      rw [e]
      exact isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun o =>
        isClosed_eq (hc.comp (continuous_const.mul (continuous_const.mul (continuous_id.matrix_elem i j))))
          continuous_const
    exact (isCompact_ball_mat n d _).of_isClosed_subset hcl hsub
  · obtain ⟨c, hc0, hcW⟩ := exists_smul_int_mem' n d W hW
    refine ⟨t / c, div_ne_zero ht0 hc0, fun Y hY => ?_⟩
    have hx : ∀ i j, valuation k ((c⁻¹ • Y) i j) ≤ 1 := by
      intro i j
      have h1 := ker_int_lt ht fun o ho => GlobalTheory.LinSchur.mem_latt.1 hY i j o ho
      have e : (c⁻¹ • Y) i j = (t / c * Y i j) * t⁻¹ := by
        rw [Matrix.smul_apply, smul_eq_mul]
        field_simp
      rw [e, map_mul, map_inv₀]
      calc valuation k (t / c * Y i j) * (valuation k t)⁻¹ ≤ valuation k t * (valuation k t)⁻¹ := by gcongr
        _ = 1 := mul_inv_cancel₀ hvt
    have := hcW _ hx
    rwa [smul_smul, mul_inv_cancel₀ hc0, one_smul] at this

end GlobalTheory.LinSchurLatt
end
end

section

open NumberField Polynomial

namespace GlobalTheory

def unitBallSubring (A : Type) [NormedField A] [IsUltrametricDist A] : Subring A :=
  GlobalTheory.ClosedBallValuationSubring.closedBallSubring A

theorem den_eq_one_of_padicNorm_le_one (c : ℚ)
    (h : ∀ q : ℕ, q.Prime → padicNorm q c ≤ 1) : c.den = 1 := by
  apply PI.ProdFormulaE.Frac.den_eq_one_of_forall_padicNorm_le_one <;> assumption

theorem isIntegral_of_forall_padicAlgCl_norm_le_one :
    ∀ (M : Type) [Field M] [NumberField M] (a : M),
      (∀ (q : ℕ) [Fact q.Prime] (τ : M →+* PadicAlgCl q), ‖τ a‖ ≤ 1) → IsIntegral ℤ a := by
  intro M _ _ a h
  set f := minpoly ℚ a with hf
  have hint : IsIntegral ℚ a := Algebra.IsIntegral.isIntegral a
  have hmon : f.Monic := minpoly.monic hint
  have hcoeff : ∀ q : ℕ, q.Prime → ∀ n, padicNorm q (f.coeff n) ≤ 1 := by
    intro q hq n
    have : Fact q.Prime := ⟨hq⟩
    let S := unitBallSubring (PadicAlgCl q)
    set g := f.map (algebraMap ℚ (PadicAlgCl q)) with hg
    have hroots : ∀ b ∈ g.roots, b ∈ S := by
      intro b hb
      have hb' : b ∈ f.rootSet (PadicAlgCl q) := by
        rw [Polynomial.mem_rootSet]
        obtain ⟨hne, hr⟩ := (mem_roots'.mp hb)
        refine ⟨fun h0 => hne (by rw [hg, h0, Polynomial.map_zero]), ?_⟩
        rw [← eval_map_algebraMap]; exact hr
      rw [← NumberField.Embeddings.range_eval_eq_rootSet_minpoly] at hb'
      obtain ⟨τ, rfl⟩ := hb'
      exact h q τ
    have hcard : Multiset.card g.roots = g.natDegree := IsAlgClosed.card_roots_eq_natDegree
    have hgmon : g.Monic := hmon.map _
    have hgc : g.coeff n ∈ S := by
      by_cases hn : n ≤ g.natDegree
      · rw [coeff_eq_esymm_roots_of_card hcard hn, hgmon.leadingCoeff, one_mul]
        refine S.mul_mem (S.pow_mem (S.neg_mem S.one_mem) _) ?_
        unfold Multiset.esymm
        refine S.multiset_sum_mem _ fun x hx => ?_
        obtain ⟨s, hs, rfl⟩ := Multiset.mem_map.mp hx
        refine S.multiset_prod_mem _ fun y hy => hroots y ?_
        exact Multiset.mem_of_le (Multiset.mem_powersetCard.mp hs).1 hy
      · rw [coeff_eq_zero_of_natDegree_lt (by omega)]; exact S.zero_mem
    have h1 : ‖algebraMap ℚ (PadicAlgCl q) (f.coeff n)‖ ≤ 1 := by
      rw [← coeff_map]; exact hgc
    have e : algebraMap ℚ (PadicAlgCl q) (f.coeff n) =
        ((f.coeff n : ℚ_[q]) : PadicAlgCl q) := by simp
    rw [e, PadicAlgCl.norm_extends, Padic.eq_padicNorm] at h1
    exact_mod_cast h1
  have hlift : f ∈ Polynomial.lifts (Int.castRingHom ℚ) := by
    rw [lifts_iff_coeff_lifts]
    intro n
    refine ⟨(f.coeff n).num, ?_⟩
    have := den_eq_one_of_padicNorm_le_one _ (fun q hq => hcoeff q hq n)
    simpa using Rat.intCast_num_of_den_eq_one this
  obtain ⟨g, hg, -, hgm⟩ := lifts_and_natDegree_eq_and_monic hlift hmon
  refine ⟨g, hgm, ?_⟩
  have h0 : aeval a f = 0 := minpoly.aeval ℚ a
  rw [← hg, ← algebraMap_int_eq, aeval_map_algebraMap] at h0
  exact h0

end GlobalTheory
end

section

open scoped TensorProduct
open IsLocalRing Polynomial

noncomputable section

namespace GlobalTheory.LocAcyc

abbrev GenFib (T O : Type) [CommRing T] [CommRing O] [Algebra T O] : Type :=
  Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))

def TorsorsTrivial (B : Type) [CommRing B] (q : ℕ) : Prop :=
  ∀ (D : Type) [CommRing D] [Algebra B D], Module.Finite B D → Module.Projective B D →
    Module.FaithfullyFlat B D →
    ∀ act : Multiplicative (ZMod q) →* (D ≃ₐ[B] D),
    Function.Bijective (Algebra.TensorProduct.productMap
      (Pi.algHom B (fun _ : Multiplicative (ZMod q) => D) (fun _ => AlgHom.id B D))
      (Pi.algHom B (fun _ : Multiplicative (ZMod q) => D) (fun g => (act g).toAlgHom))) →
    Nonempty (D →ₐ[B] B)

def AbsIntClosed (T : Type) [CommRing T] : Prop :=
  ∀ f : Polynomial T, f.Monic → 0 < f.natDegree → ∃ x : T, f.eval x = 0

def KeyAll : Prop :=
  ∀ (T O : Type) [CommRing T] [IsDomain T] [CommRing O] [IsLocalRing O] [Algebra T O]
    [Algebra (Polynomial T) O] [IsScalarTower T (Polynomial T) O], AbsIntClosed T →
    ∀ (P : Ideal (Polynomial T)) [P.IsPrime] (φ : Localization.AtPrime P →+* O),
    φ.comp (algebraMap (Polynomial T) _) = algebraMap (Polynomial T) O →
    GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsStrictHenselisation φ →
    ∀ (q : ℕ), 0 < q → IsUnit (q : T) → TorsorsTrivial (GenFib T O) q

def KeyLocalWith (S : ∀ (T : Type) [CommRing T] [IsLocalRing T], Ideal (Polynomial T) → Prop) : Prop :=
  ∀ (T O : Type) [CommRing T] [IsDomain T] [IsLocalRing T] [CommRing O] [IsLocalRing O] [Algebra T O]
    [Algebra (Polynomial T) O] [IsScalarTower T (Polynomial T) O], AbsIntClosed T →
    ∀ (P : Ideal (Polynomial T)) [P.IsPrime] (φ : Localization.AtPrime P →+* O),
    φ.comp (algebraMap (Polynomial T) _) = algebraMap (Polynomial T) O →
    GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsStrictHenselisation φ →
    P.comap (Polynomial.C : T →+* Polynomial T) = maximalIdeal T → S T P →
    ∀ (q : ℕ), 0 < q → IsUnit (q : T) → TorsorsTrivial (GenFib T O) q

def KeyLocal : Prop := KeyLocalWith (fun _ _ _ _ => True)

def KeyGeneric : Prop :=
  KeyLocalWith (fun T _ _ P => P = (maximalIdeal T).map (Polynomial.C : T →+* Polynomial T))

def KeyClosedPts : Prop :=
  KeyLocalWith (fun T _ _ P => P ≠ (maximalIdeal T).map (Polynomial.C : T →+* Polynomial T))

def KeyOrigin : Prop :=
  KeyLocalWith (fun T _ _ P =>
    P = (maximalIdeal T).map (Polynomial.C : T →+* Polynomial T) ⊔ Ideal.span {Polynomial.X})

end GlobalTheory.LocAcyc
end
end

section

open scoped NNReal

namespace GlobalTheory

open GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference

theorem addVal_inv_pow_mul {C : Type} [Field C] (w : Valuation C ℝ≥0) (ℓ : C)
    (h0 : 0 < w ℓ) (h1 : w ℓ < 1) {d c : C} (hd : d ≠ 0) (hc : c ≠ 0) (n : ℕ) :
    addVal w ℓ (d⁻¹ ^ n * c) = addVal w ℓ c - (n : ℝ) * addVal w ℓ d := by
  have hwd : ((w d : ℝ≥0) : ℝ) ≠ 0 := by
    exact_mod_cast (w.ne_zero_iff.2 hd)
  have hwc : ((w c : ℝ≥0) : ℝ) ≠ 0 := by
    exact_mod_cast (w.ne_zero_iff.2 hc)
  have hl : Real.log ((w ℓ : ℝ≥0) : ℝ) ≠ 0 := by
    refine (Real.log_neg ?_ ?_).ne
    · exact_mod_cast h0
    · exact_mod_cast h1
  unfold addVal
  rw [map_mul, map_pow, map_inv₀]
  push_cast
  rw [Real.log_mul (pow_ne_zero _ (inv_ne_zero hwd)) hwc, Real.log_pow, Real.log_inv]
  field_simp
  ring

theorem detRel_of_detRel_lsmul (C : Type) [Field C] (w : Valuation C ℝ≥0) (ℓ : C)
    (h0 : 0 < w ℓ) (h1 : w ℓ < 1) (p q : ℕ) (F : Submodule C (Fin (p + q) → C))
    (X0 : Submodule w.valuationSubring (Fin (p + q) → C))
    (L : Submodule w.valuationSubring ((Fin (p + q) → C) ⧸ F))
    (M : Submodule w.valuationSubring (Fin (p + q) → C)) (y : ℝ) (d : w.valuationSubring)
    (hd : d ≠ 0)
    (h : DetRel w ℓ F (X0.map (LinearMap.lsmul w.valuationSubring (Fin (p + q) → C) d)) L M y) :
    DetRel w ℓ F X0 L M (y - ((p + q : ℕ) : ℝ) * addVal w ℓ (d : C)) := by
  obtain ⟨x, u, m, c, hx, hu, hm, hmF, ⟨hc0, hcy⟩, hdet⟩ := h
  have hdC : (d : C) ≠ 0 := fun e => hd (Subtype.ext e)
  have hsm : ∀ v : Fin (p + q) → C, d • v = (d : C) • v := fun v => rfl
  have hinj : Function.Injective (LinearMap.lsmul w.valuationSubring (Fin (p + q) → C) d) := by
    intro a b hab
    simp only [LinearMap.lsmul_apply, hsm] at hab
    exact smul_right_injective _ hdC hab
  refine ⟨fun i => (d : C)⁻¹ • x i, u, m, (d : C)⁻¹ ^ (p + q) * c, ⟨?_, ?_⟩, hu, hm, hmF,
    ⟨mul_ne_zero (pow_ne_zero _ (inv_ne_zero hdC)) hc0, ?_⟩, ?_⟩
  · exact hx.1.units_smul (fun _ => Units.mk0 _ (inv_ne_zero hdC))
  · apply Submodule.map_injective_of_injective hinj
    rw [← hx.2, Submodule.map_span, ← Set.range_comp]
    congr 2
    funext i
    simp [hsm, smul_smul, hdC]
  · rw [addVal_inv_pow_mul w ℓ h0 h1 hdC hc0, hcy]
  · have : Matrix.of (fun i => (d : C)⁻¹ • x i) = (d : C)⁻¹ • Matrix.of x := by
      ext i j; simp
    rw [this, Matrix.det_smul, Fintype.card_fin, hdet, mul_assoc]

end GlobalTheory
end

section

open NumberField Complex
open scoped nonZeroDivisors
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization

namespace GlobalTheory.NormLe

theorem absNorm_le_abs_norm {F : Type} [Field F] [NumberField F] (𝔟 : Frac F) {b : F}
    (hb : b ∈ (𝔟 : FractionalIdeal (𝓞 F)⁰ F)) (hb0 : b ≠ 0) :
    FractionalIdeal.absNorm (𝔟 : FractionalIdeal (𝓞 F)⁰ F) ≤ |Algebra.norm ℚ b| := by
  set B : FractionalIdeal (𝓞 F)⁰ F := (𝔟 : FractionalIdeal (𝓞 F)⁰ F)
  set S : FractionalIdeal (𝓞 F)⁰ F := FractionalIdeal.spanSingleton (𝓞 F)⁰ b
  set J : FractionalIdeal (𝓞 F)⁰ F := ((𝔟⁻¹ : Frac F) : FractionalIdeal (𝓞 F)⁰ F) * S
  have hSB : S ≤ B := (FractionalIdeal.spanSingleton_le_iff_mem).2 hb
  have hSJ : S = B * J := by
    simp only [J, B, ← mul_assoc, Units.mul_inv, one_mul]
  have hJ1 : J ≤ 1 := by
    have : J ≤ ((𝔟⁻¹ : Frac F) : FractionalIdeal (𝓞 F)⁰ F) * B := by
      simp only [J]; gcongr
    simpa [B, Units.inv_mul] using this
  obtain ⟨I₀, hI₀⟩ := FractionalIdeal.le_one_iff_exists_coeIdeal.1 hJ1
  have hS0 : S ≠ 0 := by
    rw [Ne, FractionalIdeal.spanSingleton_eq_zero_iff]; exact hb0
  have hJ0 : J ≠ 0 := by
    rintro h; rw [h, mul_zero] at hSJ; exact hS0 hSJ
  have hN : (1 : ℚ) ≤ FractionalIdeal.absNorm J := by
    rw [← hI₀, FractionalIdeal.coeIdeal_absNorm]
    have : Ideal.absNorm I₀ ≠ 0 := by
      intro h
      rw [Ideal.absNorm_eq_zero_iff] at h
      apply hJ0; rw [← hI₀, h]; simp
    exact_mod_cast Nat.one_le_iff_ne_zero.2 this
  have key : FractionalIdeal.absNorm S = FractionalIdeal.absNorm B * FractionalIdeal.absNorm J := by
    rw [hSJ, map_mul]
  rw [← FractionalIdeal.absNorm_span_singleton (𝓞 F) b]
  change FractionalIdeal.absNorm B ≤ FractionalIdeal.absNorm S
  rw [key]
  have := FractionalIdeal.absNorm_nonneg B
  nlinarith

theorem main : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (𝔞 𝔟 : Frac F) (p : QPair 𝔞 𝔟),
    |(Algebra.norm ℚ p.1.1 : ℝ)| ≤ |(Algebra.norm ℚ (p.1.1 * p.1.2) : ℝ)| / nrm 𝔟 := by
  intro F _ _ _ 𝔞 𝔟 p
  obtain ⟨⟨ν, b⟩, h𝔞, h𝔟, hpos⟩ := p
  dsimp only at h𝔞 h𝔟 hpos ⊢
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  have τ : Emb F := w.embedding_of_isReal (IsTotallyReal.isReal w)
  have hνb : ν * b ≠ 0 := fun h => by have := hpos τ; rw [h, map_zero] at this; exact lt_irrefl _ this
  have hb0 : b ≠ 0 := right_ne_zero_of_mul hνb
  have hle := absNorm_le_abs_norm 𝔟 h𝔟 hb0
  have hB0 : (𝔟 : FractionalIdeal (𝓞 F)⁰ F) ≠ 0 := 𝔟.ne_zero
  have hnpos : 0 < nrm 𝔟 := by
    unfold nrm
    have h1 := FractionalIdeal.absNorm_nonneg (𝔟 : FractionalIdeal (𝓞 F)⁰ F)
    have h2 : FractionalIdeal.absNorm (𝔟 : FractionalIdeal (𝓞 F)⁰ F) ≠ 0 :=
      fun h => hB0 (FractionalIdeal.absNorm_eq_zero_iff.1 h)
    exact_mod_cast lt_of_le_of_ne h1 (Ne.symm h2)
  have hle' : nrm 𝔟 ≤ |(Algebra.norm ℚ b : ℝ)| := by
    unfold nrm; rw [← Rat.cast_abs]; exact_mod_cast hle
  rw [le_div_iff₀ hnpos, map_mul, Rat.cast_mul, abs_mul]
  exact mul_le_mul_of_nonneg_left hle' (abs_nonneg _)

end GlobalTheory.NormLe
end

section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam

namespace GlobalTheory.QFam

theorem hasQ_mul_spread : ∀ (N M : ℕ) (f : ℍ → ℂ) (a : ℕ → ℂ), 0 < N → 0 < M → HasQ N f a →
    HasQ (N * M) f (spread M a) := by
  intro N M f a hN hM h τ
  have hN' : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  have hM' : (M : ℂ) ≠ 0 := by exact_mod_cast hM.ne'
  have hinj : Function.Injective (fun k : ℕ => M * k) := fun x y hxy =>
    Nat.eq_of_mul_eq_mul_left hM hxy
  refine (hinj.hasSum_iff ?_).mp ?_
  · intro n hn
    simp only [spread]
    rw [if_neg, zero_mul]
    rintro ⟨k, rfl⟩
    exact hn ⟨k, rfl⟩
  · convert h τ using 1
    funext k
    simp only [Function.comp, spread, dvd_mul_right, if_true, Nat.mul_div_cancel_left k hM]
    congr 2
    push_cast
    field_simp

end GlobalTheory.QFam
end
