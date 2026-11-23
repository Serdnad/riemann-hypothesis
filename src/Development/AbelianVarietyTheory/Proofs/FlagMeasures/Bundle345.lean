module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.PairVal
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.Bundle001
public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NotDvdDiscrIffRamificationIdx
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsGoodSplitPrimeCmField
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
import Mathlib.RingTheory.KrullDimension.PID
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
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle006
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AtBase
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermOp
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RowsConc
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.PoincareConstantEq
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.HidaSetting
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle016

@[expose] public section

section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem unitriangular_mul_superdiagonal_add {E : Type} [Field E] {n : ℕ} (X Y : Matrix (Fin n) (Fin n) E)
    (hX0 : ∀ i j, j < i → X i j = 0) (hX1 : ∀ i, X i i = 1)
    (hY0 : ∀ i j, j < i → Y i j = 0) (hY1 : ∀ i, Y i i = 1) :
    (∀ i j, j < i → (X * Y) i j = 0) ∧ (∀ i, (X * Y) i i = 1) ∧
    (∀ (a : Fin n) (h : a.val + 1 < n), (X * Y) a ⟨a.val + 1, h⟩ = X a ⟨a.val + 1, h⟩ + Y a ⟨a.val + 1, h⟩) := by
  refine ⟨fun i j hij => ?_, fun i => ?_, fun a h => ?_⟩
  · rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero (fun k _ => ?_)
    rcases lt_or_ge k i with hk | hk
    · rw [hX0 i k hk, zero_mul]
    · rw [hY0 k j (lt_of_lt_of_le hij hk), mul_zero]
  · rw [Matrix.mul_apply, Finset.sum_eq_single i]
    · simp [hX1, hY1]
    · intro k _ hk
      rcases lt_or_gt_of_ne hk with hk | hk
      · rw [hX0 i k hk, zero_mul]
      · rw [hY0 k i hk, mul_zero]
    · intro h; exact absurd (Finset.mem_univ i) h
  · set b : Fin n := ⟨a.val + 1, h⟩ with hb
    have hab : a ≠ b := by
      intro e; have := congrArg Fin.val e; simp [hb] at this
    rw [Matrix.mul_apply, Fintype.sum_eq_add a b hab]
    · rw [hX1, hY1, one_mul, mul_one, add_comm]
    · rintro k ⟨hka, hkb⟩
      rcases lt_or_ge k a with hk | hk
      · rw [hX0 a k hk, zero_mul]
      · have hk' : a.val < k.val := lt_of_le_of_ne hk (fun e => hka (Fin.ext e.symm))
        have hk'' : b.val < k.val := by
          have : k.val ≠ a.val + 1 := fun e => hkb (Fin.ext (by simp [hb, e]))
          simp [hb]; omega
        rw [hY0 k b hk'', mul_zero]

theorem unitri_mul_inv_sgUp : ∀ {E : Type} [Field E] {n : ℕ} (B C : Matrix (Fin n) (Fin n) E), (∀ i j, j < i → B i j = 0) → (∀ i, B i i = 1) → (∀ i j, j < i → C i j = 0) → (∀ i, C i i = 1) → (∀ i j, j < i → (B * C⁻¹) i j = 0) ∧ (∀ i, (B * C⁻¹) i i = 1) ∧ Formalism.L2.SG.PairVal.sgUp (B * C⁻¹) = Formalism.L2.SG.PairVal.sgUp B - Formalism.L2.SG.PairVal.sgUp C := by
  intro E _ n B C hB0 hB1 hC0 hC1
  obtain ⟨hD0, hD1⟩ := Formalism.L2.SG.TermLoc.inv_unitri C hC0 hC1
  obtain ⟨hP0, hP1, hP2⟩ := unitriangular_mul_superdiagonal_add B C⁻¹ hB0 hB1 hD0 hD1
  obtain ⟨-, -, hQ2⟩ := unitriangular_mul_superdiagonal_add C C⁻¹ hC0 hC1 hD0 hD1
  have hdet : IsUnit C.det := by
    rw [Matrix.det_of_upperTriangular (fun i j hij => hC0 i j hij)]; simp [hC1]
  have hCC : C * C⁻¹ = 1 := Matrix.mul_nonsing_inv C hdet
  refine ⟨hP0, hP1, ?_⟩
  unfold Formalism.L2.SG.PairVal.sgUp
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  split_ifs with h
  · have hq := hQ2 a h
    rw [hCC, Matrix.one_apply_ne] at hq
    · rw [hP2 a h]; linear_combination -hq
    · intro e; have := congrArg Fin.val e; simp at this
  · simp

end GlobalTheory
end

section

noncomputable section

open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St
open scoped TensorProduct InnerProductSpace

namespace GlobalTheory.St

section Abstract

open Formalism.L2.SG.ColsDim

theorem cols_sharp_abstract {Γ Gi Gf : Type} [Group Γ] [Group Gi] [Group Gf] {V : Type} [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] (ιi : Γ →* Gi) (ιf : Γ →* Gf)
    (K : Subgroup Gf) (ψ : K →* ℂˣ) (π : Representation ℂ Gi V)
    (hπ : ∀ h : Gi, ∀ v w : V, ⟪π h v, π h w⟫_ℂ = ⟪v, w⟫_ℂ)
    (hψ : ∀ κ : K, ‖((ψ κ : ℂˣ) : ℂ)‖ = 1)
    (sh : (V →ₗ[ℂ] (Gi × Gf → ℂ)) → Gf → V)
    (hsh : ∀ (T : V →ₗ[ℂ] (Gi × Gf → ℂ)) (x : Gf) (ξ : V), ⟪sh T x, ξ⟫_ℂ = T ξ (1, x)) :
    (∀ (T : Cols ℂ ιi ιf K ψ π) (γ : Γ) (x : Gf) (κ : K),
      sh T.1 (ιf γ * x * κ) = (((ψ κ)⁻¹ : ℂˣ) : ℂ) • π (ιi γ) (sh T.1 x)) ∧
    (∀ T : Cols ℂ ιi ιf K ψ π, (∀ x, sh T.1 x = 0) → T = 0) ∧
    ∀ φ : Gf → V, (∀ (γ : Γ) (x : Gf) (κ : K),
      φ (ιf γ * x * κ) = (((ψ κ)⁻¹ : ℂˣ) : ℂ) • π (ιi γ) (φ x)) →
      ∃ T : Cols ℂ ιi ιf K ψ π, ∀ x, sh T.1 x = φ x := by
  obtain ⟨e, he, hsm⟩ := sharp_bijective Γ Gi Gf V ιi ιf K ψ π hπ hψ
  have key : ∀ (T : Cols ℂ ιi ιf K ψ π) (x : Gf), sh T.1 x = (e T).1 x := fun T x =>
    ext_inner_right ℂ fun ξ => by
      rw [hsh]
      exact he T x ξ
  refine ⟨?_, ?_, ?_⟩
  · intro T γ x κ
    rw [key, key]
    exact (e T).2 γ x κ
  · intro T hT
    have h0 : e T = e ((0 : ℂ) • T) := by
      apply Subtype.ext
      rw [hsm]
      funext x
      rw [← key, hT x]
      simp
    have := e.injective h0
    rw [this]
    simp
  · intro φ hφ
    refine ⟨e.symm ⟨φ, hφ⟩, fun x => ?_⟩
    rw [key, Equiv.apply_symm_apply]

end Abstract

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem cols_sharp_dictionary :
    ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (hK : X.LevelSubgroupCharacter), (∀ κ : Ku X u hK, ‖((psiK X u hK κ : ℂˣ) : ℂ)‖ = 1) ∧ (∀ (h : Hinf X u) (v w : X.Vpi u), ⟪piRep X u h v, piRep X u h w⟫_ℂ = ⟪v, w⟫_ℂ) ∧ (∀ (T : Cu X u hK) (γ : Gam X u) (x : Hfin X u) (κ : Ku X u hK), shP X u T.1 (iotaF X u γ * x * κ) = (((psiK X u hK κ)⁻¹ : ℂˣ) : ℂ) • piRep X u (iotaI X u γ) (shP X u T.1 x)) ∧ (∀ T : Cu X u hK, (∀ x, shP X u T.1 x = 0) → T = 0) ∧ ∀ φ : Hfin X u → X.Vpi u, (∀ (γ : Gam X u) (x : Hfin X u) (κ : Ku X u hK), φ (iotaF X u γ * x * κ) = (((psiK X u hK κ)⁻¹ : ℂˣ) : ℂ) • piRep X u (iotaI X u γ) (φ x)) → ∃ T : Cu X u hK, ∀ x, shP X u T.1 x = φ x := by
  intro D X u hK
  have hψ : ∀ κ : Ku X u hK, ‖((psiK X u hK κ : ℂˣ) : ℂ)‖ = 1 := fun κ => hK.2.2.2.2 _ κ.2
  have hπ : ∀ (h : Hinf X u) (v w : X.Vpi u), ⟪piRep X u h v, piRep X u h w⟫_ℂ = ⟪v, w⟫_ℂ :=
    fun h v w => (X.piU_rep u).2.2.1 _ (hinf_le_sinf X u _ h.2) v w
  exact ⟨hψ, hπ, cols_sharp_abstract (iotaI X u) (iotaF X u) (Ku X u hK) (psiK X u hK) (piRep X u) hπ hψ
    (shP X u) (inner_shP X u)⟩

end GlobalTheory.St

end
end

section

open NumberField Polynomial

namespace GlobalTheory.LargeSplitPrime

theorem exists_degree_one_avoiding (N : Type) [Field N] [NumberField N] (m : ℤ) (hm : m ≠ 0) :
    ∃ P : Ideal (𝓞 N), P.IsMaximal ∧ (m : 𝓞 N) ∉ P ∧ Function.Surjective (Int.castRingHom (𝓞 N ⧸ P)) := by
  obtain ⟨θ, d, hd, -, hden⟩ := GlobalTheory.SW.SplitPrime.exists_prim_den N
  by_cases hθ : θ = 0
  · refine GlobalTheory.SW.SplitPrime.exists_degree_one (1 : 𝓞 N) one_ne_zero d hd (fun a => ?_) m hm
    obtain ⟨g, hg⟩ := hden a
    refine ⟨C (g.coeff 0), ?_⟩
    rw [hg, hθ, aeval_C, aeval_def, eval₂_at_zero]
  · exact GlobalTheory.SW.SplitPrime.exists_degree_one θ hθ d hd hden m hm

theorem surjective_of_conj {N : Type} [Field N] [NumberField N] [IsGalois ℚ N] {p : ℕ} (hp : p.Prime)
    (P Q : Ideal (𝓞 N)) [hP : P.IsMaximal] [hQ : Q.IsMaximal] (h1 : (p : 𝓞 N) ∈ P) (h2 : (p : 𝓞 N) ∈ Q)
    (hs : Function.Surjective (Int.castRingHom (𝓞 N ⧸ P))) :
    Function.Surjective (Int.castRingHom (𝓞 N ⧸ Q)) := by
  have hp' : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have : P.LiesOver (Ideal.span {(p : ℤ)}) := (Ideal.liesOver_span_iff hP.ne_top hp').mpr (by simpa using h1)
  have : Q.LiesOver (Ideal.span {(p : ℤ)}) := (Ideal.liesOver_span_iff hQ.ne_top hp').mpr (by simpa using h2)
  obtain ⟨σ, hσ⟩ := Ideal.exists_smul_eq_of_isGaloisGroup (Ideal.span {(p : ℤ)}) P Q (N ≃ₐ[ℚ] N)
  intro x
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨t, ht⟩ := hs (Ideal.Quotient.mk P (σ⁻¹ • a))
  have h3 : (t : 𝓞 N) - σ⁻¹ • a ∈ P := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, ← ht]; simp
  have h4 : σ • ((t : 𝓞 N) - σ⁻¹ • a) ∈ Q := hσ ▸ Ideal.smul_mem_pointwise_smul σ _ _ h3
  have h5 : σ • (t : 𝓞 N) = t := map_intCast (MulSemiringAction.toRingHom _ _ σ) t
  rw [smul_sub, smul_inv_smul, h5] at h4
  exact ⟨t, by simpa using Ideal.Quotient.eq.2 h4⟩

theorem exists_splitsCompl (E : Type) [Field E] [NumberField E] (m : ℕ) :
    ∃ p : ℕ, p.Prime ∧ m < p ∧ Formalism.MainNotions.S.SplitsCompl E p := by
  let N : Type := IntermediateField.normalClosure ℚ E (AlgebraicClosure E)
  haveI : NumberField N := { to_charZero := inferInstance, to_finiteDimensional := inferInstance }
  haveI : IsAlgClosure ℚ (AlgebraicClosure E) := IsAlgClosure.ofAlgebraic ℚ E (AlgebraicClosure E)
  haveI : Normal ℚ N := normalClosure.normal ℚ E (AlgebraicClosure E)
  haveI : IsGalois ℚ N := IsGalois.mk
  obtain ⟨P, hP, hm, hs⟩ := exists_degree_one_avoiding N ((m.factorial : ℤ) * discr E)
    (mul_ne_zero (by exact_mod_cast m.factorial_ne_zero) (discr_ne_zero E))
  have hp := GlobalTheory.SW.SplitPrime.absNorm_prime P hP hs
  have hnd : ¬ ((Ideal.absNorm P : ℕ) : ℤ) ∣ (m.factorial : ℤ) * discr E := by
    rintro ⟨c, hc⟩
    apply hm
    rw [hc]
    push_cast
    exact P.mul_mem_right _ (Ideal.absNorm_mem P)
  refine ⟨_, hp, ?_, fun P' hP' hmem => ⟨?_, ?_⟩⟩
  · by_contra h
    exact hnd (Dvd.dvd.mul_right (by exact_mod_cast Nat.dvd_factorial hp.pos (not_lt.1 h)) _)
  · obtain ⟨Q, hQ, hQo⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 N) P'
    have hQm : ((Ideal.absNorm P : ℕ) : 𝓞 N) ∈ Q := by
      have := (Ideal.mem_of_liesOver Q P' _).1 hmem
      simpa using this
    have hsQ := surjective_of_conj hp P Q (Ideal.absNorm_mem P) hQm hs
    have hs' : Function.Surjective (Int.castRingHom (𝓞 E ⧸ P')) := by
      intro x
      obtain ⟨t, ht⟩ := hsQ (algebraMap (𝓞 E ⧸ P') (𝓞 N ⧸ Q) x)
      refine ⟨t, FaithfulSMul.algebraMap_injective (𝓞 E ⧸ P') (𝓞 N ⧸ Q) ?_⟩
      rw [← ht]; simp
    have hq := GlobalTheory.SW.SplitPrime.absNorm_prime P' hP' hs'
    by_contra hne
    have hco : IsCoprime ((Ideal.absNorm P' : ℕ) : 𝓞 E) ((Ideal.absNorm P : ℕ) : 𝓞 E) :=
      ((Nat.coprime_primes hq hp).2 hne).cast
    obtain ⟨a, b, hab⟩ := hco
    exact hP'.ne_top ((Ideal.eq_top_iff_one _).2
      (hab ▸ P'.add_mem (P'.mul_mem_left _ (Ideal.absNorm_mem P')) (P'.mul_mem_left _ hmem)))
  · exact GlobalTheory.Mem.RaySplit.not_mem_sq hp hmem
      ((GlobalTheory.Mem.RaySplit.not_dvd_discr_iff_ramificationIdx E hp).1 (fun h => hnd (h.mul_left _)) P'
        hP'.isPrime hmem)

end GlobalTheory.LargeSplitPrime
end
