module

public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.IsQuasiRegularSeqSelfIffLocalizationMaximal
public import Mathlib.RingTheory.Regular.RegularSequence
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsRegularOfSupportDimQuotientAddLengthLe
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsWeaklyRegularIffIsQuasiRegularSeqOfIsLocalRing
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle001
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle008
public import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle017
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle015
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
public import Mathlib.RingTheory.Noetherian.Defs
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle014
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle002
import Mathlib.Algebra.Module.StablyFree.Basic
public import Mathlib.RingTheory.AdicCompletion.LocalRing
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle036
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Lemma
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

open IsLocalRing

theorem UpperTheory.V.AlgebraTools.exists_isRegular_of_free_quotient :
    ∀ (L B : Type) [CommRing L] [IsRegularLocalRing L] [CommRing B] [IsLocalRing B] [IsNoetherianRing B]
      [Algebra L B] [IsLocalHom (algebraMap L B)] (M : Type) [AddCommGroup M] [Module B M] [Module L M]
      [IsScalarTower L B M] [Module.Finite B M] [Nontrivial M] (r e : ℕ) (y : Fin r → B),
      ringKrullDim L = e → (∀ i, y i ∈ maximalIdeal B) → GlobalTheory.IsQuasiRegularSeq M y →
      Module.Free L (M ⧸ Ideal.span (Set.range y) • (⊤ : Submodule B M)) →
      ∃ xs : List B, xs.length = r + e ∧ (∀ x ∈ xs, x ∈ maximalIdeal B) ∧ RingTheory.Sequence.IsRegular M xs := by
  intro L B _ _ _ _ _ _ _ M _ _ _ _ _ _ r e y he hy hq hfree
  obtain ⟨zs, h, hd⟩ := GlobalTheory.exists_ofList_eq_maximalIdeal_length_eq L
  have hreg := (GlobalTheory.isRegular_of_ofList_eq_maximalIdeal h hd.le).toIsWeaklyRegular
  have hlen : zs.length = e := by
    rw [he] at hd
    exact_mod_cast hd
  have hmem : ∀ x ∈ List.ofFn y ++ zs.map (algebraMap L B), x ∈ maximalIdeal B := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
      exact hy i
    · refine map_maximalIdeal_le (algebraMap L B) ?_
      rw [← h, Ideal.map_ofList]
      exact Ideal.subset_span hx
  refine ⟨List.ofFn y ++ zs.map (algebraMap L B), by simp [hlen], hmem, ?_⟩
  rw [IsLocalRing.isRegular_iff_isWeaklyRegular_of_subset_maximalIdeal hmem,
    RingTheory.Sequence.isWeaklyRegular_append_iff, GlobalTheory.ofList_ofFn_eq_span_range,
    RingTheory.Sequence.isWeaklyRegular_map_algebraMap_iff]
  refine ⟨hq.isWeaklyRegular ?_, ?_⟩
  · exact fun i => maximalIdeal_le_jacobson _ (hy i)
  · exact ((TensorProduct.lid L _).isWeaklyRegular_congr zs).mp hreg.isWeaklyRegular_rTensor
end

section

open Polynomial Matrix IsLocalRing TensorProduct UpperTheory.V.AlgebraTools

private theorem UpperTheory.V.AlgebraTools.entry_of_single {R ι : Type} [CommRing R] [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι R) (a b : ι) :
    (single a a (1 : R) * M * single b b (1 : R) : Matrix ι ι R) a b = M a b := by
  simp

theorem UpperTheory.V.AlgebraTools.lemma_L :
    ∀ {R Γ : Type} [CommRing R] [IsLocalRing R] [Group Γ] {n : ℕ} (r : Γ →* GL (Fin n) R) (ψ : Fin n → Γ →* Rˣ), (n : Cardinal) ≤ Cardinal.mk (ResidueField R) → (∀ g : Fin n → Γ, (List.ofFn fun i => ((r (g i) : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) - algebraMap R _ ((ψ i (g i) : Rˣ) : R)).prod = 0) → Function.Injective (fun i => (residue R : R →* ResidueField R).comp ((Units.coeHom R).comp (ψ i))) → (∀ z : MonoidAlgebra R Γ, (MonoidAlgebra.lift R (Matrix (Fin n) (Fin n) R) Γ ((Units.coeHom _).comp r) z).charpoly.map (residue R) = ∏ i, (X - C (residue R (MonoidAlgebra.lift R R Γ ((Units.coeHom _).comp (ψ i)) z)))) → ∃ (z : MonoidAlgebra R Γ) (g : GL (Fin n) R), (∀ i j, i ≠ j → IsUnit (MonoidAlgebra.lift R R Γ ((Units.coeHom R).comp (ψ i)) z - MonoidAlgebra.lift R R Γ ((Units.coeHom R).comp (ψ j)) z)) ∧ (∀ i, (g : Matrix (Fin n) (Fin n) R) * lag (fun i => MonoidAlgebra.lift R R Γ ((Units.coeHom R).comp (ψ i)) z) (MonoidAlgebra.lift R (Matrix (Fin n) (Fin n) R) Γ ((Units.coeHom _).comp r) z) i * ((g⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) = single i i 1) ∧ ∀ s, (∀ i j, j < i → (g * r s * g⁻¹ : GL (Fin n) R) i j = 0) ∧ ∀ i, (g * r s * g⁻¹ : GL (Fin n) R) i i = (ψ i s : R) := by
  intro R Γ _ _ _ n r ψ hcard hprod hinj hchar
  obtain ⟨z, hz⟩ := sep_chars (fun i => (Units.coeHom R).comp (ψ i)) hcard hinj
  have hord := ord_ext ((Units.coeHom _).comp r) (fun i => (Units.coeHom R).comp (ψ i)) hprod
  obtain ⟨hcoi, htri, hdiag⟩ := lag_triangular
    (MonoidAlgebra.lift R (Matrix (Fin n) (Fin n) R) Γ ((Units.coeHom _).comp r))
    (fun i => MonoidAlgebra.lift R R Γ ((Units.coeHom R).comp (ψ i))) z hord hz
  have hne := lag_ne_zero (fun i => MonoidAlgebra.lift R R Γ ((Units.coeHom R).comp (ψ i)) z) _ hz (hchar z)
  obtain ⟨g, hg⟩ := coi_conj_single _ hcoi hne
  refine ⟨z, g, hz, hg, fun s => ?_⟩
  set e := lag (fun i => MonoidAlgebra.lift R R Γ ((Units.coeHom R).comp (ψ i)) z)
    (MonoidAlgebra.lift R (Matrix (Fin n) (Fin n) R) Γ ((Units.coeHom _).comp r) z) with he
  have hρ : MonoidAlgebra.lift R (Matrix (Fin n) (Fin n) R) Γ ((Units.coeHom _).comp r)
      (MonoidAlgebra.of R Γ s) = ((r s : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) := by
    simp [MonoidAlgebra.lift_of]
  have hχ : ∀ i, MonoidAlgebra.lift R R Γ ((Units.coeHom R).comp (ψ i)) (MonoidAlgebra.of R Γ s)
      = ((ψ i s : Rˣ) : R) := fun i => by
    simp [MonoidAlgebra.lift_of]
  have hinv : ((g⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) * (g : Matrix (Fin n) (Fin n) R) = 1 :=
    Units.inv_mul g
  have key : ∀ i j, ((g * r s * g⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) i j =
      ((g : Matrix (Fin n) (Fin n) R) * (e i * ((r s : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) * e j)
        * ((g⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R)) i j := by
    intro i j
    refine (UpperTheory.V.AlgebraTools.entry_of_single (((g * r s * g⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R)) i j).symm.trans ?_
    rw [← hg i, ← hg j]
    congr 1
    simp only [Units.val_mul, Matrix.mul_assoc]
    simp only [← Matrix.mul_assoc (((g⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R)), hinv, Matrix.one_mul]
  refine ⟨fun i j hji => ?_, fun i => ?_⟩
  · rw [key, ← hρ, htri _ i j hji]
    simp
  · rw [key, ← hρ, hdiag, Matrix.mul_smul, Matrix.smul_mul, hg i, hχ]
    simp
end

section

open MvPolynomial Equiv UpperTheory.V.AlgebraTools.Hk

private theorem pair_lt {R : Type} [CommRing R] {n : ℕ} {q : R} {H : Type} [Ring H] [Algebra R H] (b : Bern n q H)
    {a c : Fin n} (h : a.val + 1 = c.val) (u : Perm (Fin n)) (hu : u⁻¹ a < u⁻¹ c) :
    (b.T (swap a c) * b.T u - q • b.T u) + (b.T (swap a c) * b.T (swap a c * u) - q • b.T (swap a c * u)) = 0 := by
  have hu : b.T (swap a c * u) = b.T (swap a c) * b.T u := b.T_mul a c h u hu
  have hsq := b.T_sq a c h
  rw [hu, ← mul_assoc, hsq, add_mul, smul_mul_assoc, smul_mul_assoc, one_mul]
  module

private theorem swap_one {R : Type} [CommRing R] {n : ℕ} {q : R} {H : Type} [Ring H] [Algebra R H] (b : Bern n q H)
    {a c : Fin n} (h : a.val + 1 = c.val) : b.T (swap a c) * b.one = q • b.one := by
  have hac : a ≠ c := by
    intro e
    rw [e] at h
    omega
  have key : ∀ w : Perm (Fin n), (b.T (swap a c) * b.T w - q • b.T w)
      + (b.T (swap a c) * b.T (swap a c * w) - q • b.T (swap a c * w)) = 0 := by
    intro w
    rcases lt_or_gt_of_ne (show w⁻¹ a ≠ w⁻¹ c from fun e => hac (w⁻¹.injective e)) with hw | hw
    · exact pair_lt b h w hw
    · have hu : (swap a c * w)⁻¹ a < (swap a c * w)⁻¹ c := by
        simpa [Perm.mul_apply, mul_inv_rev, swap_inv, swap_apply_left, swap_apply_right] using hw
      have := pair_lt b h (swap a c * w) hu
      rw [← mul_assoc, swap_mul_self, one_mul] at this
      rw [add_comm]
      exact this
  have hsum : ∑ w, (b.T (swap a c) * b.T w - q • b.T w) = 0 := by
    refine Finset.sum_ninvolution (fun w => swap a c * w) key ?_ (fun _ => Finset.mem_univ _) ?_
    · intro w _ e
      apply hac
      have := congrArg (fun x : Perm (Fin n) => (x * w⁻¹) a) e
      simp [mul_assoc] at this
      exact this.symm
    · intro w
      rw [← mul_assoc, swap_mul_self, one_mul]
  unfold Bern.one
  rw [Finset.mul_sum, Finset.smul_sum, ← sub_eq_zero, ← Finset.sum_sub_distrib]
  exact hsum

theorem UpperTheory.V.AlgebraTools.hkOne :
    ∀ (R : Type) [CommRing R] (n : ℕ) (q : R) (H : Type) [Ring H] [Algebra R H] (b : Bern n q H),
      (∀ w, b.T w * b.one = q ^ invN w • b.one) ∧ b.one * b.one = poin (n := n) q • b.one := by
  intro R _ n q H _ _ b
  have hinv := UpperTheory.V.AlgebraTools.hkInv n
  have p1 : ∀ w, b.T w * b.one = q ^ invN w • b.one := by
    refine UpperTheory.V.AlgebraTools.hkInd n _ ?_ ?_
    · rw [b.T_one, one_mul]
      simp [invN, hinv.2.2.1]
    · intro a c h w hw ih
      rw [b.T_mul a c h w hw, mul_assoc, ih, mul_smul_comm, swap_one b h, smul_smul,
        (hinv.1 a c h w hw).2.2, pow_succ]
  refine ⟨p1, ?_⟩
  show (∑ w, b.T w) * b.one = _
  rw [Finset.sum_mul]
  simp_rw [p1]
  rw [← Finset.sum_smul]
  rfl
end

section

open MvPolynomial Equiv UpperTheory.V.AlgebraTools.Hk

private theorem UpperTheory.V.AlgebraTools.hkBern_reg {R : Type} [CommRing R] {n : ℕ} {a c : Fin n} (hac : a ≠ c)
    (y : MvPolynomial (Fin n) R) (h : (X a - X c) * y = 0) : y = 0 := by
  let φ : MvPolynomial (Fin n) R →ₐ[R] MvPolynomial (Fin n) R :=
    aeval fun j => if j = a then X a + X c else X j
  let ψ : MvPolynomial (Fin n) R →ₐ[R] MvPolynomial (Fin n) R :=
    aeval fun j => if j = a then X a - X c else X j
  have hψ : ψ.comp φ = AlgHom.id R _ := by
    apply MvPolynomial.algHom_ext
    intro j
    by_cases hj : j = a
    · simp [φ, ψ, hj, hac.symm]
    · simp [φ, ψ, hj]
  have h1 : φ (X a - X c) = X a := by simp [φ, hac.symm]
  have h2 : X a * φ y = X a * 0 := by rw [mul_zero, ← h1, ← map_mul, h, map_zero]
  have h3 : φ y = 0 := (MvPolynomial.isRegular_X (R := R) (n := a)).left h2
  have h4 := AlgHom.congr_fun hψ y
  rw [AlgHom.comp_apply, h3, map_zero, AlgHom.id_apply] at h4
  exact h4.symm

theorem UpperTheory.V.AlgebraTools.hkBern :
    ∀ (R : Type) [CommRing R] (n : ℕ) (q : R) (H : Type) [Ring H] [Algebra R H] (b : Bern n q H),
      (∀ (a c : Fin n), a.val + 1 = c.val → ∀ x : MvPolynomial (Fin n) R, ∃ y : MvPolynomial (Fin n) R, (X a - X c) * y = x - rename (swap a c) x ∧
        b.T (swap a c) * b.th x = b.th (rename (swap a c) x) * b.T (swap a c) + (q - 1) • b.th (X a * y)) ∧
      ∀ z : MvPolynomial (Fin n) R, z.IsSymmetric → ∀ w, b.T w * b.th z = b.th z * b.T w := by
  intro R _ n q H _ _ b
  have main : ∀ (a c : Fin n), a.val + 1 = c.val → ∀ x : MvPolynomial (Fin n) R, ∃ y : MvPolynomial (Fin n) R,
      (X a - X c) * y = x - rename (swap a c) x ∧
        b.T (swap a c) * b.th x = b.th (rename (swap a c) x) * b.T (swap a c) + (q - 1) • b.th (X a * y) := by
    intro a c hac
    have hX : ∀ j : Fin n, ∃ y : MvPolynomial (Fin n) R,
        (X a - X c) * y = X j - rename (swap a c) (X j) ∧
        b.T (swap a c) * b.th (X j) = b.th (rename (swap a c) (X j)) * b.T (swap a c) + (q - 1) • b.th (X a * y) := by
      intro j
      by_cases ha : j = a
      · subst ha
        refine ⟨1, by simp, ?_⟩
        rw [rename_X, swap_apply_left, mul_one]
        exact b.relA j c hac
      · by_cases hc : j = c
        · subst hc
          refine ⟨-1, by simp, ?_⟩
          rw [rename_X, swap_apply_right, mul_neg, mul_one, map_neg, smul_neg, ← sub_eq_add_neg]
          exact b.relB a j hac
        · refine ⟨0, by simp [swap_apply_of_ne_of_ne ha hc], ?_⟩
          rw [rename_X, swap_apply_of_ne_of_ne ha hc, mul_zero, map_zero, smul_zero, add_zero]
          exact b.comm a c hac j ha hc
    intro x
    induction x using MvPolynomial.induction_on with
    | C r =>
      refine ⟨0, by simp, ?_⟩
      rw [rename_C, mul_zero, map_zero, smul_zero, add_zero, ← MvPolynomial.algebraMap_eq, AlgHom.commutes,
        Algebra.commutes]
    | add p p' hp hp' =>
      obtain ⟨y, h1, h2⟩ := hp
      obtain ⟨y', h1', h2'⟩ := hp'
      refine ⟨y + y', ?_, ?_⟩
      · rw [mul_add, h1, h1', map_add (f := _)]; ring
      · rw [map_add (f := _), map_add (f := _), map_add (f := _), mul_add, h2, h2', mul_add, map_add (f := _), add_mul, smul_add]; abel
    | mul_X p j hp =>
      obtain ⟨y, h1, h2⟩ := hp
      obtain ⟨y', h1', h2'⟩ := hX j
      refine ⟨y * X j + rename (swap a c) p * y', ?_, ?_⟩
      · rw [map_mul]
        linear_combination (X j) * h1 + rename (swap a c) p * h1'
      · have e : X a * (y * X j + rename (swap a c) p * y') =
            (X a * y) * X j + rename (swap a c) p * (X a * y') := by ring
        rw [e, map_add (f := _), map_mul b.th (X a * y), map_mul b.th _ (X a * y'), map_mul (rename _), map_mul b.th p,
          map_mul b.th (rename _ p), ← mul_assoc, h2, add_mul, mul_assoc, h2', mul_add, smul_add, smul_mul_assoc,
          mul_smul_comm, mul_assoc]
        abel
  refine ⟨main, fun z hz => ?_⟩
  refine UpperTheory.V.AlgebraTools.hkInd n (fun w => b.T w * b.th z = b.th z * b.T w) ?_ ?_
  · simp only [b.T_one, one_mul, mul_one]
  · intro a c hac w hw ih
    obtain ⟨y, h1, h2⟩ := main a c hac z
    have hne : a ≠ c := by
      rintro rfl
      omega
    rw [hz (swap a c)] at h1 h2
    rw [sub_self] at h1
    rw [UpperTheory.V.AlgebraTools.hkBern_reg hne y h1, mul_zero, map_zero, smul_zero, add_zero] at h2
    rw [b.T_mul a c hac w hw, mul_assoc, ih, ← mul_assoc, h2, mul_assoc]
end

section

open IsLocalRing UpperTheory.V.AlgebraTools

theorem UpperTheory.V.AlgebraTools.IsCplAt.nonempty_algEquiv :
    ∀ (R : Type) [CommRing R] (p : Ideal R) (B : Type) [CommRing B] [IsLocalRing B] [Algebra R B] (B' : Type) [CommRing B'] [IsLocalRing B'] [Algebra R B'],
      IsCplAt R p B → IsCplAt R p B' → Nonempty (B ≃ₐ[R] B') := by
  intro R _ p B _ _ _ B' _ _ _ hB hB'
  haveI : IsAdicComplete (maximalIdeal B) B := hB.complete
  haveI : IsAdicComplete (maximalIdeal B') B' := hB'.complete
  obtain ⟨ψ, hψ, -⟩ := IsCplAt.existsUnique_lift R p B hB B' (algebraMap R B') hB'.comap_eq
  obtain ⟨χ, hχ, -⟩ := IsCplAt.existsUnique_lift R p B' hB' B (algebraMap R B) hB.comap_eq
  obtain ⟨_, -, huB⟩ := IsCplAt.existsUnique_lift R p B hB B (algebraMap R B) hB.comap_eq
  obtain ⟨_, -, huB'⟩ := IsCplAt.existsUnique_lift R p B' hB' B' (algebraMap R B') hB'.comap_eq
  have h1 : χ.comp ψ = RingHom.id B := by
    have ha : (χ.comp ψ).comp (algebraMap R B) = algebraMap R B := by
      rw [RingHom.comp_assoc, hψ, hχ]
    rw [huB _ ha, huB (RingHom.id B) (RingHom.id_comp _)]
  have h2 : ψ.comp χ = RingHom.id B' := by
    have ha : (ψ.comp χ).comp (algebraMap R B') = algebraMap R B' := by
      rw [RingHom.comp_assoc, hχ, hψ]
    rw [huB' _ ha, huB' (RingHom.id B') (RingHom.id_comp _)]
  refine ⟨AlgEquiv.ofRingEquiv (f := RingEquiv.ofRingHom ψ χ h2 h1) ?_⟩
  intro x
  exact congrArg (fun φ : R →+* B' => φ x) hψ
end

section

open Filter UpperTheory.V.AlgebraTools
open scoped TensorProduct

theorem UpperTheory.V.AlgebraTools.topNil_free :
    ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (IsLocalRing.maximalIdeal R) R] (κ : Type) (M : Type) [AddCommGroup M] [Module R M] [Module.Finite R M] (T : κ → Module.End R M), (∀ i j, Commute (T i) (T j)) →
      (∃ C : Submodule R M, IsCompl (topNil (IsLocalRing.maximalIdeal R) T) C ∧ ∀ φ : Module.End R M, (∀ i, Commute φ (T i)) →
        (∀ x ∈ topNil (IsLocalRing.maximalIdeal R) T, φ x ∈ topNil (IsLocalRing.maximalIdeal R) T) ∧ ∀ x ∈ C, φ x ∈ C) ∧
      (∀ I : Ideal R, (I • ⊤ : Submodule R M) ⊓ topNil (IsLocalRing.maximalIdeal R) T = I • topNil (IsLocalRing.maximalIdeal R) T) ∧
      (∀ i, ∃ r : ℕ, ∀ x ∈ topNil (IsLocalRing.maximalIdeal R) T, (T i ^ r) x ∈ (IsLocalRing.maximalIdeal R) • topNil (IsLocalRing.maximalIdeal R) T) ∧
      (Module.Free R M → Module.Free R (topNil (IsLocalRing.maximalIdeal R) T) ∧ Module.finrank R (topNil (IsLocalRing.maximalIdeal R) T) ≤ Module.finrank R M) := by
  intro R _ _ _ _ κ M _ _ _ T hT
  obtain ⟨e, he, hid, hr⟩ := UpperTheory.V.AlgebraTools.exists_idem_topNil R κ M T hT
  have hee : ∀ x, e (e x) = e x := fun x => by
    have h := congrArg (fun f : Module.End R M => f x) hid.eq
    simpa using h
  have hfix : ∀ x ∈ topNil (IsLocalRing.maximalIdeal R) T, e x = x := by
    rw [← hr]
    rintro _ ⟨y, rfl⟩
    exact hee y
  have hmem : ∀ x, e x ∈ topNil (IsLocalRing.maximalIdeal R) T := fun x => by
    rw [← hr]; exact ⟨x, rfl⟩
  have hcomm : ∀ φ : Module.End R M, (∀ i, Commute φ (T i)) → ∀ x, φ (e x) = e (φ x) := by
    intro φ hφ x
    have h : Commute φ e := by
      refine Algebra.commute_of_mem_adjoin_of_forall_mem_commute he ?_
      rintro _ ⟨i, rfl⟩
      exact hφ i
    have h2 := congrArg (fun f : Module.End R M => f x) h.eq
    simpa using h2
  have hstab : ∀ φ : Module.End R M, (∀ i, Commute φ (T i)) →
      ∀ x ∈ topNil (IsLocalRing.maximalIdeal R) T, φ x ∈ topNil (IsLocalRing.maximalIdeal R) T := by
    intro φ hφ x hx
    rw [← hfix x hx, hcomm φ hφ]
    exact hmem _
  have hI : ∀ I : Ideal R, (I • ⊤ : Submodule R M) ⊓ topNil (IsLocalRing.maximalIdeal R) T =
      I • topNil (IsLocalRing.maximalIdeal R) T := by
    intro I
    refine le_antisymm ?_ (le_inf (Submodule.smul_mono le_rfl le_top) Submodule.smul_le_right)
    rintro x ⟨hx1, hx2⟩
    have h1 : e x ∈ Submodule.map e (I • ⊤ : Submodule R M) := ⟨x, hx1, rfl⟩
    rw [Submodule.map_smul'', Submodule.map_top, hr, hfix x hx2] at h1
    exact h1
  refine ⟨⟨LinearMap.ker e, ?_, fun φ hφ => ⟨hstab φ hφ, ?_⟩⟩, hI, ?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · rw [Submodule.disjoint_def]
      intro x hx hk
      rw [← hfix x hx]
      exact hk
    · rw [codisjoint_iff, eq_top_iff]
      intro x _
      refine Submodule.mem_sup.2 ⟨e x, hmem x, x - e x, ?_, by abel⟩
      rw [LinearMap.mem_ker, map_sub, hee, sub_self]
  · intro x hx
    rw [LinearMap.mem_ker] at hx ⊢
    rw [← hcomm φ hφ, hx, map_zero]
  · intro i
    obtain ⟨S, hS⟩ := IsNoetherian.noetherian (topNil (IsLocalRing.maximalIdeal R) T)
    have hev : ∀ᶠ r : ℕ in atTop, ∀ x ∈ S,
        (T i ^ r) x ∈ ((IsLocalRing.maximalIdeal R) ^ 1 • ⊤ : Submodule R M) := by
      rw [Filter.eventually_all_finset]
      intro x hx
      have hx' : x ∈ topNil (IsLocalRing.maximalIdeal R) T := hS ▸ Submodule.subset_span hx
      exact mem_topNil.1 hx' i 1
    obtain ⟨r, hr'⟩ := hev.exists
    refine ⟨r, fun x hx => ?_⟩
    rw [← hI]
    refine ⟨?_, hstab _ (fun j => (hT i j).pow_left r) x hx⟩
    have hle : Submodule.span R (S : Set M) ≤
        Submodule.comap (T i ^ r) ((IsLocalRing.maximalIdeal R) • ⊤ : Submodule R M) := by
      rw [Submodule.span_le]
      intro y hy
      have h := hr' y hy
      rw [pow_one] at h
      exact h
    rw [hS] at hle
    exact hle hx
  · intro hF
    refine ⟨?_, Submodule.finrank_le _⟩
    have hP : Module.Projective R (topNil (IsLocalRing.maximalIdeal R) T) :=
      Module.Projective.of_split (topNil (IsLocalRing.maximalIdeal R) T).subtype
        (LinearMap.codRestrict _ e hmem) (by
          ext x
          simpa using hfix x.1 x.2)
    exact Module.free_of_flat_of_isLocalRing
end

section

open IsLocalRing UpperTheory.V.AlgebraTools

private lemma mem_pow_iff (L : Type) [CommRing L] [IsNoetherianRing L] [IsLocalRing L] (n : ℕ)
    (x : AdicCompletion (maximalIdeal L) L) :
    x ∈ maximalIdeal (AdicCompletion (maximalIdeal L) L) ^ n ↔
      AdicCompletion.eval (maximalIdeal L) L n x = 0 := by
  rw [AdicCompletion.maximalIdeal_eq_map, ← Ideal.map_pow, ← Submodule.restrictScalars_mem L,
    ← Ideal.smul_top_eq_map,
    AdicCompletion.pow_smul_top_eq_ker_eval (maximalIdeal L).fg_of_isNoetherianRing]
  rfl

private lemma strict_loc (L : Type) [CommRing L] [IsNoetherianRing L] [IsLocalRing L] (n : ℕ)
    (a : L) (h : algebraMap L (AdicCompletion (maximalIdeal L) L) a ∈
      maximalIdeal (AdicCompletion (maximalIdeal L) L) ^ n) : a ∈ maximalIdeal L ^ n := by
  rw [mem_pow_iff, AdicCompletion.algebraMap_apply, AdicCompletion.eval_apply,
    AdicCompletion.of_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h
  simpa [smul_eq_mul, Ideal.mul_top] using h

private lemma dense_loc (L : Type) [CommRing L] [IsNoetherianRing L] [IsLocalRing L] (n : ℕ)
    (b : AdicCompletion (maximalIdeal L) L) :
    ∃ a : L, b - algebraMap L (AdicCompletion (maximalIdeal L) L) a ∈
      maximalIdeal (AdicCompletion (maximalIdeal L) L) ^ n := by
  obtain ⟨a, ha⟩ := Submodule.Quotient.mk_surjective _ (AdicCompletion.eval (maximalIdeal L) L n b)
  refine ⟨a, ?_⟩
  rw [mem_pow_iff, map_sub, ← ha, AdicCompletion.algebraMap_apply, AdicCompletion.eval_apply,
    AdicCompletion.of_apply]
  simp

theorem UpperTheory.V.AlgebraTools.isCplAt_cplAt :
    ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (p : Ideal R) [p.IsPrime], IsCplAt R p (CplAt R p) := by
  intro R _ _ p _
  let L := Localization.AtPrime p
  have hRB : ∀ r : R, algebraMap R (CplAt R p) r =
      algebraMap L (CplAt R p) (algebraMap R L r) := fun r =>
    IsScalarTower.algebraMap_apply R L (CplAt R p) r
  refine ⟨GlobalTheory.AdicNoeth.isNoetherianRing_adicCompletion L (maximalIdeal L), inferInstance, ?_, ?_, ?_⟩
  · rw [IsScalarTower.algebraMap_eq R L (CplAt R p), ← Ideal.comap_comap,
      IsLocalRing.maximalIdeal_comap]
    exact Localization.AtPrime.under_maximalIdeal
  · intro n b
    obtain ⟨a', ha'⟩ := dense_loc L n b
    obtain ⟨⟨r, s⟩, rfl⟩ := IsLocalization.mk'_surjective p.primeCompl a'
    refine ⟨r, s, s.2, ?_⟩
    have e : algebraMap R (CplAt R p) s * b - algebraMap R (CplAt R p) r =
        algebraMap R (CplAt R p) s *
          (b - algebraMap L (CplAt R p) (IsLocalization.mk' L r s)) := by
      rw [mul_sub, hRB, hRB, ← map_mul, mul_comm (algebraMap R L s), IsLocalization.mk'_spec]
    rw [e]
    exact Ideal.mul_mem_left _ _ ha'
  · intro n a ha
    rw [hRB] at ha
    have h1 := strict_loc L n _ ha
    rw [← Localization.AtPrime.map_eq_maximalIdeal, ← Ideal.map_pow,
      IsLocalization.mem_map_algebraMap_iff p.primeCompl] at h1
    obtain ⟨⟨⟨b, hb⟩, s⟩, hx⟩ := h1
    simp only [← map_mul] at hx
    obtain ⟨c, hc⟩ := (IsLocalization.eq_iff_exists p.primeCompl L).1 hx
    refine ⟨c * s, ?_, ?_⟩
    · exact p.primeCompl.mul_mem c.2 s.2
    · have : (c : R) * s * a = c * b := by
        rw [mul_assoc, mul_comm (s : R) a]
        exact hc
      rw [this]
      exact Ideal.mul_mem_left _ _ hb
end
