module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.Bundle002
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.Bundle001
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.FFInert2Holds
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.Bundle001
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.LocDensFFS
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.PairHermZeroRight
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.SdDual
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.AdeleLC
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.T2SpaceTensorProductFiniteExtension
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.Bundle003
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.TensTop
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section

namespace PI.OmLocU

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain MeasureTheory
open PI.VolStabSW PI.OmLocU.CntFF
open scoped TensorProduct

theorem prod_fin_rev (f : ℕ → ℝ) (n : ℕ) : ∀ a : ℕ, a ≤ n →
    ∏ j : Fin a, f (n - (j : ℕ)) = ∏ i ∈ Finset.Icc (n - a + 1) n, f i := by
  intro a
  induction a with
  | zero =>
    intro _
    rw [Finset.Icc_eq_empty (by omega)]
    simp
  | succ a ih =>
    intro ha
    rw [Fin.prod_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    rw [ih (by omega), show n - (a + 1) + 1 = n - a by omega,
      ← Finset.insert_Icc_add_one_left_eq_Icc (show n - a ≤ n by omega), Finset.prod_insert (by simp), mul_comm]

theorem prod_pow_rev (q : ℝ) (n : ℕ) : ∀ a : ℕ, a ≤ n →
    ∏ j : Fin a, q ^ (2 * (n - (j : ℕ)) - 1) = q ^ (2 * n * a - a ^ 2) := by
  intro a
  induction a with
  | zero => intro _; simp
  | succ a ih =>
    intro ha
    rw [Fin.prod_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    rw [ih (by omega), ← pow_add]
    congr 1
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le ha
    have e1 : 2 * (a + 1 + m) * a - a ^ 2 = a ^ 2 + 2 * a + 2 * m * a := by
      apply Nat.sub_eq_of_eq_add; ring
    have e2 : 2 * (a + 1 + m) * (a + 1) - (a + 1) ^ 2 = (a + 1) ^ 2 + 2 * m * (a + 1) := by
      apply Nat.sub_eq_of_eq_add; ring
    rw [e1, e2, show 2 * (a + 1 + m - a) - 1 = 2 * m + 1 by omega]
    ring

theorem inert_prod (q : ℝ) (hq : 0 < q) (n a : ℕ) (ha : a ≤ n) :
    ∏ j : Fin a, (q ^ (2 * (n - (j : ℕ)) - 1) - (-1) ^ (n - (j : ℕ)) * q ^ (n - (j : ℕ) - 1)) =
      q ^ (2 * n * a - a ^ 2) * ∏ i ∈ Finset.Icc (n - a + 1) n, (1 - (-1 : ℝ) ^ i * q ^ (-(i : ℤ))) := by
  set f : ℕ → ℝ := fun i => 1 - (-1 : ℝ) ^ i * q ^ (-(i : ℤ)) with hf
  have ht : ∀ j : Fin a, q ^ (2 * (n - (j : ℕ)) - 1) - (-1) ^ (n - (j : ℕ)) * q ^ (n - (j : ℕ) - 1) =
      q ^ (2 * (n - (j : ℕ)) - 1) * f (n - (j : ℕ)) := by
    intro j
    have hj : (j : ℕ) < n := lt_of_lt_of_le j.2 ha
    simp only [hf]
    have e : q ^ (2 * (n - (j : ℕ)) - 1) * q ^ (-((n - (j : ℕ) : ℕ) : ℤ)) = q ^ (n - (j : ℕ) - 1) := by
      rw [← zpow_natCast, ← zpow_natCast, ← zpow_add₀ hq.ne']
      congr 1
      push_cast [Nat.cast_sub (show 1 ≤ 2 * (n - (j : ℕ)) by omega), Nat.cast_sub hj.le,
        Nat.cast_sub (show 1 ≤ n - (j : ℕ) by omega)]
      ring
    rw [mul_sub, mul_one, ← e]
    ring
  rw [Finset.prod_congr rfl (fun j _ => ht j), Finset.prod_mul_distrib, prod_pow_rev q n a ha,
    prod_fin_rev f n a ha]

theorem split_prod (q : ℝ) (hq : 0 < q) (n a : ℕ) (ha : a ≤ n) :
    (∏ i : Fin a, (q ^ n - q ^ (i : ℕ))) * q ^ (a * (n - a)) =
      q ^ (2 * n * a - a ^ 2) * ∏ i ∈ Finset.Icc (n - a + 1) n, (1 - (1 : ℝ) ^ i * q ^ (-(i : ℤ))) := by
  set f : ℕ → ℝ := fun i => 1 - (1 : ℝ) ^ i * q ^ (-(i : ℤ)) with hf
  have ht : ∀ j : Fin a, q ^ n - q ^ (j : ℕ) = q ^ n * f (n - (j : ℕ)) := by
    intro j
    have hj : (j : ℕ) < n := lt_of_lt_of_le j.2 ha
    simp only [hf, one_pow, one_mul]
    have e : q ^ n * q ^ (-((n - (j : ℕ) : ℕ) : ℤ)) = q ^ (j : ℕ) := by
      rw [← zpow_natCast, ← zpow_natCast, ← zpow_add₀ hq.ne']
      congr 1
      push_cast [Nat.cast_sub hj.le]
      ring
    rw [mul_sub, mul_one, e]
  rw [Finset.prod_congr rfl (fun j _ => ht j), Finset.prod_mul_distrib, prod_fin_rev f n a ha,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_mul]
  have e : n * a + a * (n - a) = 2 * n * a - a ^ 2 := by
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le ha
    rw [show a + m - a = m by omega]
    symm; apply Nat.sub_eq_of_eq_add; ring
  rw [← e, pow_add]
  ring

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F)) (Λ : Set (Fin n → E))

def RedU (a : ℕ) (Y : TupV (E := E) v n a) : Prop :=
  GoodY σ J ψ v Λ a Y → ∀ ϖ : Fv F v, IsUnif v ϖ →
    ∃ (k : Type) (_ : Field k) (_ : Finite k), Nat.card k = Ideal.absNorm v.asIdeal ∧
      ((etaV (E := E) v = -1 ∧ ∃ (K : Type) (_ : Field K) (_ : Algebra k K) (σ' : K ≃ₐ[k] K)
          (J' : Matrix (Fin n) (Fin n) K) (T' : Matrix (Fin a) (Fin a) K),
          (∀ x, σ' (σ' x) = x) ∧ Module.finrank k K = 2 ∧ σ' ≠ AlgEquiv.refl ∧
          (∀ i j, σ' (J' j i) = J' i j) ∧ IsUnit J'.det ∧ (∀ i j, σ' (T' j i) = T' i j) ∧ IsUnit T'.det ∧
          Nat.card (clsU σ J v Λ a ϖ (gramR (Fv F v) σ J Y)) =
            Nat.card {X : Fin a → Fin n → K // ffGram (σ' : K →+* K) J' X = T'}) ∨
       (etaV (E := E) v = 1 ∧ ∃ (J' : Matrix (Fin n) (Fin n) (k × k)) (T' : Matrix (Fin a) (Fin a) (k × k)),
          (∀ i j, (J' j i).swap = J' i j) ∧ IsUnit J'.det ∧ (∀ i j, (T' j i).swap = T' i j) ∧ IsUnit T'.det ∧
          Nat.card (clsU σ J v Λ a ϖ (gramR (Fv F v) σ J Y)) =
            Nat.card {X : Fin a → Fin n → k × k //
              ffGram (RingEquiv.prodComm (R := k) (S := k)).toRingHom J' X = T'}))

theorem clsU_of (a : ℕ) (Y : TupV (E := E) v n a) (hR : RedU σ J ψ v Λ a Y) : ClsU σ J ψ v Λ a Y := by
  intro hG ϖ hϖ
  have ha : a ≤ n := hG.2.2.2.2.1
  have hq := qv_pos v
  obtain ⟨k, _, _, hk, h⟩ := hR hG ϖ hϖ
  rcases h with ⟨hη, K, _, _, σ', J', T', hσ, h2, hne, hJ, hJu, hT, hTu, hc⟩ |
    ⟨hη, J', T', hJ, hJu, hT, hTu, hc⟩
  · rw [hc, fFInert2_holds k K σ' hσ h2 hne n a ha J' hJ hJu T' hT hTu, hk]
    unfold prodEta
    rw [hη]
    push_cast
    exact inert_prod (qv v) hq n a ha
  · rw [hc, fFSplit_holds k n a ha J' hJ hJu T' hT hTu, hk]
    unfold prodEta
    rw [hη]
    push_cast
    exact split_prod (qv v) hq n a ha

end PI.OmLocU
end
end

section

noncomputable section

namespace PI.OmLocU

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.LocVol NumberField IsDedekindDomain MeasureTheory PI.VolStabSW
  PI.VolStabSW.PositiveNearLattice PI.VolStabSW.SdDualW
open scoped TensorProduct

section Top

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F))

def oevS : AddSubgroup (Fv F v ⊗[F] E) :=
  (Submodule.span (v.adicCompletionIntegers F)
    ((fun x : 𝓞 E => inclR (F := F) (Fv F v) (x : E)) '' Set.univ)).toAddSubgroup

theorem coe_oevS : (oevS (E := E) v : Set (Fv F v ⊗[F] E)) = OEv (E := E) v := rfl

theorem inclR_mem_oev (x : 𝓞 E) : inclR (F := F) (Fv F v) (x : E) ∈ OEv (E := E) v :=
  Submodule.subset_span ⟨x, Set.mem_univ _, rfl⟩

theorem exists_int_basis : ∃ (d : ℕ) (b : Module.Basis (Fin d) F E), ∀ k, IsIntegral ℤ (b k) := by
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  classical
  obtain ⟨y, hy, hint⟩ := exists_integral_multiples ℤ ℚ (Finset.univ.image (Module.finBasis F E))
  have hyF : IsUnit ((y : F)) := by
    rw [isUnit_iff_ne_zero]
    exact_mod_cast hy
  refine ⟨_, (Module.finBasis F E).isUnitSMul (fun _ => hyF), fun k => ?_⟩
  rw [Module.Basis.isUnitSMul_apply, Int.cast_smul_eq_zsmul]
  exact hint _ (Finset.mem_image_of_mem _ (Finset.mem_univ k))

theorem latA_le_oevS [FiniteDimensional F E] {d : ℕ} (b : Module.Basis (Fin d) F E)
    (hb : ∀ k, IsIntegral ℤ (b k)) : latA v b ≤ oevS (E := E) v := by
  intro z hz
  have hz' : ∀ k, crd b (Fv F v) z k ∈ v.adicCompletionIntegers F := hz
  rw [← (Algebra.TensorProduct.basis (Fv F v) b).sum_repr z]
  refine AddSubgroup.sum_mem _ fun k _ => ?_
  rw [Algebra.TensorProduct.basis_apply]
  have hm : inclR (F := F) (Fv F v) (((⟨b k, hb k⟩ : 𝓞 E)) : E) ∈ OEv (E := E) v :=
    inclR_mem_oev v (⟨b k, hb k⟩ : 𝓞 E)
  exact Submodule.smul_mem _ (⟨_, hz' k⟩ : v.adicCompletionIntegers F) hm

theorem isOpen_oev : IsOpen (OEv (E := E) v) := by
  have : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  obtain ⟨d, b, hb⟩ := exists_int_basis (F := F) (E := E)
  rw [← coe_oevS]
  exact AddSubgroup.isOpen_mono (latA_le_oevS v b hb) (isOpen_latA v b)

theorem isCompact_oev : IsCompact (OEv (E := E) v) := by
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  obtain ⟨m, s, hs⟩ := Module.Finite.exists_fin (R := ℤ) (M := 𝓞 E)
  set g : Fin m → Fv F v ⊗[F] E := fun i => inclR (F := F) (Fv F v) ((s i : 𝓞 E) : E) with hg
  have e : OEv (E := E) v = (fun c : Fin m → Fv F v => ∑ i, c i • g i) ''
      Set.pi Set.univ (fun _ => (v.adicCompletionIntegers F : Set (Fv F v))) := by
    ext z
    constructor
    · intro hz
      have h1 : z ∈ Submodule.span (v.adicCompletionIntegers F) (Set.range g) := by
        refine (Submodule.span_le.2 ?_) hz
        rintro _ ⟨x, _, rfl⟩
        have hx : x ∈ Submodule.span ℤ (Set.range s) := by rw [hs]; exact Submodule.mem_top
        induction hx using Submodule.span_induction with
        | mem y hy =>
          obtain ⟨i, rfl⟩ := hy
          exact Submodule.subset_span ⟨i, rfl⟩
        | zero => simpa using Submodule.zero_mem _
        | add p q _ _ hp hq =>
          have e1 : inclR (F := F) (Fv F v) (((p + q : 𝓞 E)) : E) =
              inclR (F := F) (Fv F v) (p : E) + inclR (F := F) (Fv F v) (q : E) := by
            rw [← map_add (f := _)]
            rfl
          show inclR (F := F) (Fv F v) (((p + q : 𝓞 E)) : E) ∈ _
          rw [e1]
          exact Submodule.add_mem _ (hp trivial) (hq trivial)
        | smul r p _ hp =>
          have e1 : inclR (F := F) (Fv F v) (((r • p : 𝓞 E)) : E) =
              r • inclR (F := F) (Fv F v) (p : E) := by
            rw [show ((r • p : 𝓞 E) : E) = r • (p : E) from map_zsmul (algebraMap (𝓞 E) E) r p,
              map_zsmul]
          show inclR (F := F) (Fv F v) (((r • p : 𝓞 E)) : E) ∈ _
          rw [e1]
          exact zsmul_mem (hp trivial) r
      rw [Submodule.mem_span_range_iff_exists_fun] at h1
      obtain ⟨c, rfl⟩ := h1
      exact ⟨fun i => (c i : Fv F v), fun i _ => (c i).2, rfl⟩
    · rintro ⟨c, hc, rfl⟩
      exact Submodule.sum_mem _ fun i _ =>
        Submodule.smul_mem _ (⟨c i, hc i (Set.mem_univ _)⟩ : v.adicCompletionIntegers F)
          (inclR_mem_oev v (s i))
  rw [e]
  exact (isCompact_univ_pi fun _ => PI.AdicCompletionValuation.isCompact_adicCompletionIntegers F v).image
    (continuous_finsetSum _ fun i _ => by fun_prop)

variable (σ : E →ₐ[F] E)

theorem coe_HO (a : ℕ) : (HO σ v a : Set (HermR (Fv F v) σ a)) =
    Subtype.val ⁻¹' (Set.pi Set.univ fun _ : Fin a => Set.pi Set.univ fun _ : Fin a => OEv (E := E) v) := by
  ext S
  constructor
  · intro h
    rw [SetLike.mem_coe, mem_HO] at h
    exact fun i _ j _ => h i j
  · intro h
    rw [SetLike.mem_coe, mem_HO]
    exact fun i j => h i (Set.mem_univ _) j (Set.mem_univ _)

theorem topH_holds (a : ℕ) : TopH σ v a := by
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  have hK : IsCompact (Set.pi Set.univ fun _ : Fin a => Set.pi Set.univ fun _ : Fin a => OEv (E := E) v) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_oev v
  have := locallyCompact_Fv F v
  refine ⟨?_, ?_⟩
  · rw [coe_HO]
    exact (isClosed_HermR (Fv F v) σ a).isClosedEmbedding_subtypeVal.isCompact_preimage hK
  · rw [coe_HO]
    exact (isOpen_set_pi Set.finite_univ fun _ _ =>
      isOpen_set_pi Set.finite_univ fun _ _ => isOpen_oev v).preimage continuous_subtype_val

end Top

end PI.OmLocU
end
end
