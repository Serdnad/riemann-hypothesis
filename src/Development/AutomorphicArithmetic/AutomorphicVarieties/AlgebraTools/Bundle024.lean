module

public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.IsQuasiRegularSeqSelfIffLocalizationMaximal
public import Mathlib.RingTheory.Regular.RegularSequence
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle004
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsRegularOfSupportDimQuotientAddLengthLe
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsWeaklyRegularIffIsQuasiRegularSeqOfIsLocalRing
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Flat.Basic
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle046
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle019
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle021
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle017
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle020
public import Mathlib.FieldTheory.Separable
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingIntegralClosure
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
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
public import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
public import Mathlib.RingTheory.Flat.Stability
public import Mathlib.RingTheory.Finiteness.Ideal
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.RingTheory.DedekindDomain.IntegralClosure

@[expose] public section

section

open IsLocalRing UpperTheory.V.AlgebraTools

theorem UpperTheory.V.AlgebraTools.patched_depth_dim :
    ∀ (L B : Type) [CommRing L] [IsRegularLocalRing L] [CommRing B] [IsLocalRing B] [IsNoetherianRing B]
      [Algebra L B] [IsLocalHom (algebraMap L B)] (M : Type) [AddCommGroup M] [Module B M] [Module L M]
      [IsScalarTower L B M] [Module.Finite B M] [Nontrivial M] (r e : ℕ) (y : Fin r → B),
      ringKrullDim L = e → (∀ i, y i ∈ maximalIdeal B) → GlobalTheory.IsQuasiRegularSeq M y →
      Module.Free L (M ⧸ Ideal.span (Set.range y) • (⊤ : Submodule B M)) →
      Module.Finite L (M ⧸ Ideal.span (Set.range y) • (⊤ : Submodule B M)) →
      (∃ xs : List B, xs.length = r + e ∧ (∀ x ∈ xs, x ∈ maximalIdeal B) ∧ RingTheory.Sequence.IsRegular M xs) ∧
      ∀ Z ∈ (Module.annihilator B M).minimalPrimes, ringKrullDim (B ⧸ Z) = ((r + e : ℕ) : WithBot ℕ∞) := by
  intro L B _ _ _ _ _ _ _ M _ _ _ _ _ _ r e y hL hy hq hfree hfin
  refine ⟨exists_isRegular_of_free_quotient L B M r e y hL hy hq hfree, ?_⟩
  obtain ⟨xs, hlen, hxs, hreg⟩ := exists_isRegular_of_free_quotient L B M r e y hL hy hq hfree
  have hys : ∀ z ∈ List.ofFn y, z ∈ maximalIdeal B := by
    intro z hz
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hz
    exact hy i
  have h1 := GlobalTheory.supportDim_le_supportDim_quotient_add_length (M := M) hys
  rw [GlobalTheory.ofList_ofFn_eq_span_range, List.length_ofFn] at h1
  have h2 := supportDim_le_of_finite L B (M ⧸ Ideal.span (Set.range y) • (⊤ : Submodule B M))
  rw [hL] at h2
  have hdim : Module.supportDim B M ≤ ((xs.length : ℕ) : WithBot ℕ∞) := by
    refine h1.trans ?_
    rw [hlen]
    calc Module.supportDim B (M ⧸ Ideal.span (Set.range y) • (⊤ : Submodule B M)) + ((r : ℕ) : WithBot ℕ∞)
        ≤ ((e : ℕ) : WithBot ℕ∞) + ((r : ℕ) : WithBot ℕ∞) := by gcongr
      _ = ((r + e : ℕ) : WithBot ℕ∞) := by
        rw [add_comm]; norm_cast
  intro Z hZ
  have := dim_minimalPrime_eq B M xs hxs hreg.toIsWeaklyRegular hdim Z hZ
  rw [this, hlen]
end

section

open MvPolynomial Equiv UpperTheory.V.AlgebraTools.Hk

theorem UpperTheory.V.AlgebraTools.hkSpan :
    ∀ (R : Type) [CommRing R] (n : ℕ) (q : R) (H : Type) [Ring H] [Algebra R H] (b : Bern n q H) (w : Perm (Fin n)) (c : Perm (Fin n) → MvPolynomial (Fin n) R),
      ∃ c' : Perm (Fin n) → MvPolynomial (Fin n) R, b.T w * ∑ u, b.th (c u) * b.T u = ∑ u, b.th (c' u) * b.T u := by
  intro R _ n q H _ _ b
  classical
  let S : Submodule R H :=
    { carrier := {h | ∃ c' : Perm (Fin n) → MvPolynomial (Fin n) R, h = ∑ u, b.th (c' u) * b.T u}
      add_mem' := by
        rintro _ _ ⟨c₁, rfl⟩ ⟨c₂, rfl⟩
        exact ⟨c₁ + c₂, by simp [add_mul, Finset.sum_add_distrib]⟩
      zero_mem' := ⟨0, by simp⟩
      smul_mem' := by
        rintro r _ ⟨c₁, rfl⟩
        exact ⟨r • c₁, by simp [Finset.smul_sum]⟩ }
  have hone : ∀ x u, b.th x * b.T u ∈ S := by
    intro x u
    refine ⟨Pi.single u x, ?_⟩
    rw [Finset.sum_eq_single u]
    · simp
    · intro v _ hv
      simp [Pi.single_eq_of_ne hv]
    · simp
  have hTT : ∀ a c : Fin n, a.val + 1 = c.val → ∀ x u, b.th x * (b.T (swap a c) * b.T u) ∈ S := by
    intro a c hac x u
    by_cases hlt : u⁻¹ a < u⁻¹ c
    · rw [← b.T_mul a c hac u hlt]
      exact hone _ _
    · have hne : u⁻¹ c ≠ u⁻¹ a := by
        intro e
        have := (u⁻¹).injective e
        rw [this] at hac
        omega
      have hw' : (swap a c * u)⁻¹ a < (swap a c * u)⁻¹ c := by
        rw [mul_inv_rev, swap_inv, Perm.mul_apply, Perm.mul_apply, swap_apply_left, swap_apply_right]
        exact lt_of_le_of_ne (not_lt.mp hlt) hne
      have e := b.T_mul a c hac _ hw'
      rw [swap_mul_self_mul] at e
      have e2 : b.T (swap a c) * b.T u = (q - 1) • b.T u + q • b.T (swap a c * u) := by
        calc b.T (swap a c) * b.T u = (b.T (swap a c) * b.T (swap a c)) * b.T (swap a c * u) := by
              rw [mul_assoc, ← e]
          _ = (q - 1) • b.T u + q • b.T (swap a c * u) := by
              rw [b.T_sq a c hac, add_mul, smul_mul_assoc, smul_mul_assoc, one_mul, ← e]
      rw [e2, mul_add, mul_smul_comm, mul_smul_comm]
      exact S.add_mem (S.smul_mem _ (hone _ _)) (S.smul_mem _ (hone _ _))
  have hs : ∀ a c : Fin n, a.val + 1 = c.val → ∀ h ∈ S, b.T (swap a c) * h ∈ S := by
    rintro a c hac _ ⟨c₁, rfl⟩
    rw [Finset.mul_sum]
    refine S.sum_mem fun u _ => ?_
    obtain ⟨y, -, hy⟩ := (UpperTheory.V.AlgebraTools.hkBern R n q H b).1 a c hac (c₁ u)
    rw [← mul_assoc, hy, add_mul, smul_mul_assoc, mul_assoc]
    exact S.add_mem (hTT a c hac _ _) (S.smul_mem _ (hone _ _))
  have key : ∀ w, ∀ h ∈ S, b.T w * h ∈ S := by
    refine UpperTheory.V.AlgebraTools.hkInd n _ ?_ ?_
    · intro h hh
      rwa [b.T_one, one_mul]
    · intro a c hac w hw ih h hh
      rw [b.T_mul a c hac w hw, mul_assoc]
      exact hs a c hac _ (ih h hh)
  intro w c
  exact key w _ ⟨c, rfl⟩
end

section

open Filter UpperTheory.V.AlgebraTools
open scoped TensorProduct

private theorem topNil_map_mem {R M M' κ : Type} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup M'] [Module R M'] (I : Ideal R) (T : κ → Module.End R M)
    (T' : κ → Module.End R M') (f : M →ₗ[R] M') (hf : ∀ i x, f (T i x) = T' i (f x))
    {x : M} (hx : x ∈ topNil I T) : f x ∈ topNil I T' := by
  change ∀ i (j : ℕ), ∀ᶠ r : ℕ in atTop, (T i ^ r) x ∈ (I ^ j • ⊤ : Submodule R M) at hx
  change ∀ i (j : ℕ), ∀ᶠ r : ℕ in atTop, (T' i ^ r) (f x) ∈ (I ^ j • ⊤ : Submodule R M')
  intro i j
  have hpow : ∀ r : ℕ, f ((T i ^ r) x) = (T' i ^ r) (f x) := by
    intro r
    induction r with
    | zero => simp
    | succ n ih => rw [pow_succ', pow_succ', Module.End.mul_apply, Module.End.mul_apply, hf, ih]
  have hle : Submodule.map f (I ^ j • (⊤ : Submodule R M)) ≤ I ^ j • (⊤ : Submodule R M') := by
    rw [Submodule.map_smul'']
    exact Submodule.smul_mono le_rfl le_top
  filter_upwards [hx i j] with r hr
  rw [← hpow]
  exact hle ⟨_, hr, rfl⟩

theorem UpperTheory.V.AlgebraTools.topNil_map :
    ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (IsLocalRing.maximalIdeal R) R] (κ : Type) (M : Type) [AddCommGroup M] [Module R M] (M' : Type) [AddCommGroup M'] [Module R M'] [Module.Finite R M] [Module.Finite R M'] (T : κ → Module.End R M) (T' : κ → Module.End R M'),
      (∀ i j, Commute (T i) (T j)) → (∀ i j, Commute (T' i) (T' j)) → ∀ f : M →ₗ[R] M', (∀ i x, f (T i x) = T' i (f x)) →
      (topNil (IsLocalRing.maximalIdeal R) T).map f = topNil (IsLocalRing.maximalIdeal R) T' ⊓ LinearMap.range f ∧
      ∀ I : Ideal R, LinearMap.ker f = I • ⊤ → LinearMap.ker f ⊓ topNil (IsLocalRing.maximalIdeal R) T = I • topNil (IsLocalRing.maximalIdeal R) T := by
  intro R _ _ _ _ κ M _ _ M' _ _ _ _ T T' hT hT' f hf
  have hsmul := (topNil_free R κ M T hT).2.1
  refine ⟨le_antisymm ?_ ?_, fun I hI => by rw [hI]; exact hsmul I⟩
  · rw [Submodule.map_le_iff_le_comap]
    intro x hx
    exact ⟨topNil_map_mem _ T T' f hf hx, x, rfl⟩
  · rintro y ⟨hy, x, rfl⟩
    have hTx : ∀ i j x, T i (T j x) = T j (T i x) := fun i j x => by
      rw [← Module.End.mul_apply, (hT i j).eq, Module.End.mul_apply]
    have hT'x : ∀ i j x, T' i (T' j x) = T' j (T' i x) := fun i j x => by
      rw [← Module.End.mul_apply, (hT' i j).eq, Module.End.mul_apply]
    let S : κ → Module.End R (M × M') := fun i => (T i).prodMap (T' i)
    have hS : ∀ i j, Commute (S i) (S j) := by
      intro i j
      show S i * S j = S j * S i
      apply LinearMap.ext
      intro p
      simp [S, Module.End.mul_apply, hTx i j, hT'x i j]
    obtain ⟨⟨C, hC, hstab⟩, -⟩ := topNil_free R κ (M × M') S hS
    let φ : Module.End R (M × M') := (LinearMap.inr R M M').comp (f.comp (LinearMap.fst R M M'))
    have hφ : ∀ i, Commute φ (S i) := by
      intro i
      show φ * S i = S i * φ
      apply LinearMap.ext
      intro p
      simp [φ, S, Module.End.mul_apply, hf]
    have hmem : ((x, 0) : M × M') ∈ topNil (IsLocalRing.maximalIdeal R) S ⊔ C := by
      rw [hC.sup_eq_top]
      exact Submodule.mem_top
    obtain ⟨n, hn, c, hc, hnc⟩ := Submodule.mem_sup.mp hmem
    have hn1 : n.1 ∈ topNil (IsLocalRing.maximalIdeal R) T :=
      topNil_map_mem _ S T (LinearMap.fst R M M') (fun i p => rfl) hn
    have hφc : φ c ∈ C := (hstab φ hφ).2 c hc
    have hx : x = n.1 + c.1 := by
      have := congrArg Prod.fst hnc
      simpa using this.symm
    have hfc : f c.1 ∈ topNil (IsLocalRing.maximalIdeal R) T' := by
      have : f c.1 = f x - f n.1 := by
        rw [hx]
        simp
      rw [this]
      exact Submodule.sub_mem _ hy (topNil_map_mem _ T T' f hf hn1)
    have hφn : φ c ∈ topNil (IsLocalRing.maximalIdeal R) S := by
      have := topNil_map_mem _ T' S (LinearMap.inr R M M') (fun i y => by simp [S]) hfc
      simpa [φ] using this
    have h0 : φ c = 0 := (Submodule.disjoint_def.mp hC.disjoint) _ hφn hφc
    have hfc0 : f c.1 = 0 := by
      have := congrArg Prod.snd h0
      simpa [φ] using this
    refine ⟨n.1, hn1, ?_⟩
    rw [hx, map_add (f := _), hfc0, add_zero]
end

section

open IsLocalRing UpperTheory.V.AlgebraTools

theorem UpperTheory.V.AlgebraTools.IsCplAt.flat :
    ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (p : Ideal R) (B : Type) [CommRing B] [IsLocalRing B] [Algebra R B], IsCplAt R p B → Module.Flat R B := by
  intro R _ _ p B _ _ _ h
  haveI := h.isPrime
  haveI : Module.Flat (Localization.AtPrime p) (CplAt R p) := AdicCompletion.flat_of_isNoetherian _
  haveI : Module.Flat R (CplAt R p) := Module.Flat.trans R (Localization.AtPrime p) (CplAt R p)
  obtain ⟨e⟩ := IsCplAt.nonempty_algEquiv R p B (CplAt R p) h (isCplAt_cplAt R p)
  exact Module.Flat.of_linearEquiv e.toLinearEquiv
end

section

open IsLocalRing UpperTheory.V.AlgebraTools

theorem UpperTheory.V.AlgebraTools.IsCplAt.regular :
    ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (p : Ideal R) [p.IsPrime] (B : Type) [CommRing B] [IsLocalRing B]
      [Algebra R B], IsCplAt R p B → IsRegularLocalRing (Localization.AtPrime p) →
      IsRegularLocalRing B ∧ ringKrullDim B = ringKrullDim (Localization.AtPrime p) := by
  intro R _ _ p _ B _ _ _ hB hT
  obtain ⟨e⟩ := IsCplAt.nonempty_algEquiv R p B (CplAt R p) hB (isCplAt_cplAt R p)
  have hC : IsRegularLocalRing (CplAt R p) :=
    GlobalTheory.RegularCompletion.isRegularLocalRing_adicCompletion (Localization.AtPrime p)
  refine ⟨IsRegularLocalRing.of_ringEquiv e.toRingEquiv.symm, ?_⟩
  rw [ringKrullDim_eq_of_ringEquiv e.toRingEquiv, ← hC.spanFinrank_maximalIdeal,
    ← hT.spanFinrank_maximalIdeal]
  exact congrArg _ (AdicCompletion.spanFinrank_maximalIdeal_eq (R := Localization.AtPrime p))
end

section

open Filter UpperTheory.V.AlgebraTools
open scoped TensorProduct

theorem UpperTheory.V.AlgebraTools.ULim.trans_ker :
    ∀ (R : Type) [CommRing R] (F : Filter ℕ), F ≤ atTop → ∀ (I : ℕ → Ideal R) (M : ℕ → Type) [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)] (a b : Ideal R), a.FG → Antitone I → ∀ h : b ≤ a,
      Function.Surjective (ULim.map F (I := fun j => b ⊔ I j) (I' := fun j => a ⊔ I j) (M := M) (fun _ => sup_le_sup_right h _) fun _ => LinearMap.id) ∧
      LinearMap.ker (ULim.map F (I := fun j => b ⊔ I j) (I' := fun j => a ⊔ I j) (M := M) (fun _ => sup_le_sup_right h _) fun _ => LinearMap.id) = a • ⊤ ∧
      (a • ⊤ : Submodule R (ULim F (fun j => a ⊔ I j) M)) = ⊥ := by
  intro R _ F hF I M _ _ a b ha hI h
  have hI1 : Antitone fun j => b ⊔ I j := fun i j hij => sup_le_sup_left (hI hij) b
  have hI2 : Antitone fun j => a ⊔ I j := fun i j hij => sup_le_sup_left (hI hij) a
  have e1 : ∀ j, a ⊔ (b ⊔ I j) = a ⊔ I j := fun j => by rw [← sup_assoc, sup_eq_left.mpr h]
  have e2 : ∀ j, a ⊔ (a ⊔ I j) = a ⊔ I j := fun j => by rw [← sup_assoc, sup_idem]
  refine ⟨?_, ?_, ?_⟩
  · intro y
    obtain ⟨p, rfl⟩ := ULim.mk_surjective F (fun j => a ⊔ I j) M y
    exact ⟨ULim.mk F (fun j => b ⊔ I j) M p, by rw [ULim.map_mk]; rfl⟩
  · ext x
    obtain ⟨p, rfl⟩ := ULim.mk_surjective F (fun j => b ⊔ I j) M x
    rw [LinearMap.mem_ker, ULim.map_mk, ULim.mk_eq_zero, ULim.mem_smul_top_iff R F hF _ M a ha hI1]
    simp only [LinearMap.id_apply, e1]
  · refine eq_bot_iff.mpr fun x hx => ?_
    obtain ⟨p, rfl⟩ := ULim.mk_surjective F (fun j => a ⊔ I j) M x
    rw [ULim.mem_smul_top_iff R F hF _ M a ha hI2] at hx
    rw [Submodule.mem_bot, ULim.mk_eq_zero]
    simpa only [e2] using hx
end

section

open Filter UpperTheory.V.AlgebraTools
open scoped TensorProduct

theorem UpperTheory.V.AlgebraTools.qRegAt_uLim :
    ∀ (R σ : Type) [CommRing R] [Finite σ] (F : Filter ℕ), F ≤ atTop → ∀ (I : ℕ → Ideal R) (M : ℕ → Type) [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)] (y : σ → R) (a k : ℕ), Antitone I → a < k →
      (∀ j, ∀ᶠ N in F, QRegAt (M N) y (I j) a) →
      QRegAt (ULim F (fun j => Ideal.span (Set.range y) ^ k ⊔ I j) M) y ⊥ a := by
  intro R σ _ _ F hF I M _ _ y a k hI hak hq
  classical
  set Y : Ideal R := Ideal.span (Set.range y) with hY
  have hYfg : Y.FG := ⟨(Set.finite_range y).toFinset, by simp [hY]⟩
  have hK : Antitone (fun j ↦ Y ^ k ⊔ I j) := fun i j hij ↦ sup_le_sup_left (hI hij) _
  have hk1 : Y ^ k ≤ Y ^ (a + 1) := Ideal.pow_le_pow_right (by omega)
  intro c hc
  choose p hp using fun α ↦ ULim.mk_surjective F (fun j ↦ Y ^ k ⊔ I j) M (c α)
  have hsum : ∑ α : GlobalTheory.MonoDeg σ a, GlobalTheory.monoVal y ↑α • c α =
      ULim.mk F (fun j ↦ Y ^ k ⊔ I j) M
        (fun N ↦ ∑ α : GlobalTheory.MonoDeg σ a, GlobalTheory.monoVal y ↑α • p α N) := by
    have e : (fun N ↦ ∑ α : GlobalTheory.MonoDeg σ a, GlobalTheory.monoVal y ↑α • p α N) =
        ∑ α : GlobalTheory.MonoDeg σ a, GlobalTheory.monoVal y ↑α • p α := by
      ext N
      simp [Finset.sum_apply]

    rw [e, map_sum]
    simp [hp]
  rw [sup_bot_eq, hsum, ULim.mem_smul_top_iff R F hF _ M (Y ^ (a + 1)) hYfg.pow hK] at hc
  intro α
  rw [sup_bot_eq, ← hp α, ULim.mem_smul_top_iff R F hF _ M Y hYfg hK]
  intro j
  filter_upwards [hc j, hq j] with N hN hqN
  have hN' : ∑ β : GlobalTheory.MonoDeg σ a, GlobalTheory.monoVal y ↑β • p β N ∈
      (Y ^ (a + 1) ⊔ I j) • (⊤ : Submodule R (M N)) :=
    Submodule.smul_mono_left (sup_le le_sup_left (sup_le (hk1.trans le_sup_left) le_sup_right)) hN
  exact Submodule.smul_mono_left (sup_le_sup_left le_sup_right Y) (hqN (fun β ↦ p β N) hN' α)
end

section

open IsLocalRing

theorem UpperTheory.V.AlgebraTools.integralClosure_complete_dvr :
    ∀ (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [IsAdicComplete (maximalIdeal A) A]
      (F K : Type) [Field F] [Field K] [Algebra A F] [IsFractionRing A F] [Algebra F K] [Algebra A K]
      [IsScalarTower A F K] [FiniteDimensional F K] [Algebra.IsSeparable F K]
      (B : Type) [CommRing B] [IsDomain B] [Algebra A B] [Algebra B K] [IsScalarTower A B K] [IsIntegralClosure B A K],
      Module.Finite A B ∧ Module.Free A B ∧ IsFractionRing B K ∧
      ∃ _ : IsDiscreteValuationRing B, IsAdicComplete (maximalIdeal B) B ∧ IsLocalHom (algebraMap A B) ∧
        (Finite (ResidueField A) → Finite (ResidueField B)) := by
  intro A _ _ _ _ F K _ _ _ _ _ _ _ _ _ B _ _ _ _ _ _
  have hinjK : Function.Injective (algebraMap A K) := by
    rw [IsScalarTower.algebraMap_eq A F K]
    exact (algebraMap F K).injective.comp (IsFractionRing.injective A F)
  have hinj : Function.Injective (algebraMap A B) := by
    rw [IsScalarTower.algebraMap_eq A B K, RingHom.coe_comp] at hinjK
    exact hinjK.of_comp
  haveI : FaithfulSMul A B := (faithfulSMul_iff_algebraMap_injective A B).2 hinj
  haveI hfin : Module.Finite A B := IsIntegralClosure.finite A F K B
  haveI hfree : Module.Free A B := Module.free_of_finite_type_torsion_free'
  have hfr : IsFractionRing B K := IsIntegralClosure.isFractionRing_of_finite_extension A F K B
  haveI := GlobalTheory.FormalIsogeny.isDiscreteValuationRing_integralClosure A F K
  haveI hdvr : IsDiscreteValuationRing B :=
    IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing
      (IsIntegralClosure.equiv A (integralClosure A K) K B)
  haveI hloc : IsLocalHom (algebraMap A B) := inferInstance
  refine ⟨hfin, hfree, hfr, hdvr, GlobalTheory.FormalIsogeny.isAdicComplete_maximalIdeal_of_finite A B,
    hloc, fun h => ?_⟩
  exact IsLocalRing.ResidueField.finite_of_finite h
end
