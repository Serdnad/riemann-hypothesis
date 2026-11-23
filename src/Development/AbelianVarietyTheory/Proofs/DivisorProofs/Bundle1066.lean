module

public import Development.AbelianVarietyTheory.Definitions.Divisors.GalMapMul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle454
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle320
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle686
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1053
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasLevelStd
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle024
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1034
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle765
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle652
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle256
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle712
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle942
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle651
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle637
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrystallinePull2SumCup
public import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveStructureSheafDegTwoVanish
public import Development.AbelianVarietyTheory.Definitions.Divisors.PullHlComp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1035
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle636
public import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1036
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle019
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle463
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1037
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.RingTheory.Radical.NatInt
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle001
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle027
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasExponentZeroIff
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle002
import Development.DiscreteGroups.GlobalIrreducibility.Bundle011

@[expose] public section

section

open GlobalTheory.EtC

namespace GlobalTheory.QUnits

theorem tensorFractionRing_units_pow_surj : ∀ (q : ℕ) [NeZero q] (T : Type) [CommRing T] [IsDomain T] [IsLocalRing T], AIC T → IsUnit (q : T) → ∀ (O : Type) [CommRing O] [Algebra T O] [Algebra (Polynomial T) O] [IsScalarTower T (Polynomial T) O] [HenselianLocalRing O] [IsSepClosed (IsLocalRing.ResidueField O)], (∃ (ι : Type) (_ : Preorder ι) (_ : IsDirected ι (· ≤ ·)) (_ : Nonempty ι) (Si : ι → Subalgebra (Polynomial T) O), Monotone Si ∧ (∀ s : O, ∃ i, s ∈ Si i) ∧ ∀ i, ∃ (E : Type) (_ : CommRing E) (_ : Algebra (Polynomial T) E) (_ : Algebra.Etale (Polynomial T) E) (P : Ideal E) (_ : P.IsPrime), Nonempty (Localization.AtPrime P ≃ₐ[(Polynomial T)] Si i)) → ∀ (A : Type) [CommRing A] [Algebra (Polynomial T) A] [Algebra T A] [IsScalarTower T (Polynomial T) A] (π : O →ₐ[Polynomial T] A), Function.Surjective π → ∀ u : (TensorProduct T (FractionRing T) A)ˣ, ∃ v : (TensorProduct T (FractionRing T) A)ˣ, v ^ q = u := by
  intro q _ T _ _ _ hAIC hq O _ _ _ _ _ _ hind A _ _ _ _ π hπ u
  have hq0 : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  let L := Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))
  let R := TensorProduct T (FractionRing T) A
  let f : O →+* R := (Algebra.TensorProduct.includeRight : A →ₐ[T] R).toRingHom.comp π.toRingHom
  have hπT : ∀ t : T, π (algebraMap T O t) = algebraMap T A t := by
    intro t
    rw [IsScalarTower.algebraMap_apply T (Polynomial T) O, AlgHom.commutes,
      ← IsScalarTower.algebraMap_apply]
  have hfT : ∀ t : T, f (algebraMap T O t) = algebraMap T R t := by
    intro t
    change Algebra.TensorProduct.includeRight (π (algebraMap T O t)) = _
    rw [hπT, AlgHom.commutes]
  have hf : ∀ y : Algebra.algebraMapSubmonoid O (nonZeroDivisors T), IsUnit (f y) := by
    rintro ⟨_, t, ht, rfl⟩
    change IsUnit (f (algebraMap T O t))
    rw [hfT, IsScalarTower.algebraMap_apply T (FractionRing T) R]
    exact (IsLocalization.map_units (FractionRing T) ⟨t, ht⟩).map _
  let φ : L →+* R := IsLocalization.lift hf
  have hφ : Function.Surjective φ := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => exact ⟨0, map_zero φ⟩
    | add x y hx hy =>
      obtain ⟨a, rfl⟩ := hx
      obtain ⟨b, rfl⟩ := hy
      exact ⟨a + b, map_add φ a b⟩
    | tmul k a =>
      obtain ⟨o, rfl⟩ := hπ a
      obtain ⟨⟨x, s⟩, rfl⟩ := IsLocalization.mk'_surjective (nonZeroDivisors T) k
      refine ⟨IsLocalization.mk' L (algebraMap T O x * o)
        (⟨algebraMap T O s, Algebra.mem_algebraMapSubmonoid_of_mem s⟩ :
          Algebra.algebraMapSubmonoid O (nonZeroDivisors T)), ?_⟩
      rw [IsLocalization.lift_mk'_spec]
      change f (algebraMap T O x * o) = f (algebraMap T O (s : T)) * _
      rw [map_mul, hfT, hfT]
      change algebraMap T R x * (Algebra.TensorProduct.includeRight (π o)) = _
      have hR : ∀ t : T, algebraMap T R t = algebraMap T (FractionRing T) t ⊗ₜ[T] (1 : A) := fun t => rfl
      rw [Algebra.TensorProduct.includeRight_apply, hR, hR, Algebra.TensorProduct.tmul_mul_tmul,
        Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one, IsLocalization.mk'_spec']
  have hB : ∀ P : Ideal L, P.IsPrime → P ≠ ⊥ → P.IsMaximal ∧ ∀ x : L, ∃ c d : T, d ≠ 0 ∧
      algebraMap T L d * x - algebraMap T L c ∈ P := by
    intro P hP hne
    obtain ⟨g, hg, hgP⟩ := GlobalTheory.T.exists_ne_zero_polynomial_mem_prime_localization T hAIC O hind P hP hne
    exact GlobalTheory.T.prime_tensor_polynomial_isMaximal_of_mem_image T hAIC O hind P hP g hg hgP
  by_cases hJ : RingHom.ker φ = ⊥
  · have hinj : Function.Injective φ := (RingHom.injective_iff_ker_eq_bot φ).2 hJ
    let e : L ≃+* R := RingEquiv.ofBijective φ ⟨hinj, hφ⟩
    obtain ⟨v, hv⟩ := GlobalTheory.LocAcycUnits.units_localization_pow_surj T O q ⟨inferInstance, hAIC⟩ hq hq0
      hind (Units.map e.symm.toMonoidHom u)
    refine ⟨Units.map e.toMonoidHom v, ?_⟩
    rw [← map_pow, hv]; ext; simp
  · let J := RingHom.ker φ
    let e : L ⧸ J ≃+* R := RingHom.quotientKerEquivOfSurjective hφ
    have hne : ∀ I : Ideal (L ⧸ J), I.comap (Ideal.Quotient.mk J) ≠ ⊥ := by
      intro I h
      apply hJ
      rw [eq_bot_iff]
      intro x hx
      rw [← h, Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.2 hx]
      exact I.zero_mem
    haveI : Ring.KrullDimLE 0 (L ⧸ J) := by
      refine Ring.KrullDimLE.mk₀ ?_
      intro I hI
      have hP : (I.comap (Ideal.Quotient.mk J)).IsPrime := Ideal.comap_isPrime _ _
      have hmax := (hB _ hP (hne I)).1
      have := Ideal.map_eq_top_or_isMaximal_of_surjective (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective hmax
      rw [Ideal.map_comap_of_surjective (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective] at this
      exact this.resolve_left hI.ne_top
    have hqL : IsUnit (q : L ⧸ J) := by
      have := hq.map (algebraMap T (L ⧸ J)); simpa using this
    have hroot : ∀ m : Ideal (L ⧸ J), m.IsMaximal → ∃ x : L ⧸ J,
        x ^ q - ((Units.map e.symm.toMonoidHom u : (L ⧸ J)ˣ) : L ⧸ J) ∈ m := by
      intro m hm
      obtain ⟨w0, hw0⟩ := Ideal.Quotient.mk_surjective
        ((Units.map e.symm.toMonoidHom u : (L ⧸ J)ˣ) : L ⧸ J)
      have hP : (m.comap (Ideal.Quotient.mk J)).IsPrime := Ideal.comap_isPrime _ _
      obtain ⟨c, d, hd, hcd⟩ := (hB _ hP (hne m)).2 w0
      obtain ⟨n, rfl⟩ : ∃ n, q = n + 1 := ⟨q - 1, by omega⟩
      obtain ⟨r, hr⟩ := hAIC (Polynomial.X ^ (n + 1) - Polynomial.C (c * d ^ n))
        (Polynomial.monic_X_pow_sub_C _ (Nat.succ_ne_zero n))
        (by rw [Polynomial.natDegree_X_pow_sub_C _]; exact hq0)
      have hrq : r ^ (n + 1) = c * d ^ n := by simpa [sub_eq_zero] using hr
      have hdu : IsUnit (algebraMap T L d) := by
        rw [IsScalarTower.algebraMap_apply T O L]
        exact IsLocalization.map_units L (⟨algebraMap T O d,
          Algebra.mem_algebraMapSubmonoid_of_mem (⟨d, mem_nonZeroDivisors_of_ne_zero hd⟩ :
            nonZeroDivisors T)⟩ : Algebra.algebraMapSubmonoid O (nonZeroDivisors T))
      set D := algebraMap T L d
      set Dinv : L := ((hdu.unit⁻¹ : Lˣ) : L)
      have hDn : Dinv ^ (n + 1) * D ^ (n + 1) = 1 := by
        rw [← mul_pow, IsUnit.val_inv_mul, one_pow]
      have hR : algebraMap T L r ^ (n + 1) = algebraMap T L c * D ^ n := by
        rw [← map_pow, hrq, map_mul, map_pow]
      refine ⟨Ideal.Quotient.mk J (algebraMap T L r * Dinv), ?_⟩
      rw [← hw0, ← map_pow, ← map_sub, ← Ideal.mem_comap]
      have key : (algebraMap T L r * Dinv) ^ (n + 1) - w0 =
          -(Dinv ^ (n + 1) * D ^ n) * (D * w0 - algebraMap T L c) := by
        linear_combination Dinv ^ (n + 1) * hR + w0 * hDn
      rw [key]
      exact Ideal.mul_mem_left _ _ hcd
    obtain ⟨v, hv⟩ := GlobalTheory.T.exists_root_of_unit_zero_dimensional (L ⧸ J) q hq0 hqL (Units.map e.symm.toMonoidHom u) hroot
    exact ⟨Units.map e.toMonoidHom v, by rw [← map_pow, hv]; ext; simp⟩

end GlobalTheory.QUnits
end

section

open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
open GlobalTheory.LatVal (Sz)
open GlobalTheory.LatJet (EisExp IsEis FR)
open GlobalTheory.WpFam

namespace GlobalTheory.HilbFam.GalFamily

theorem ch_one (N : ℕ) [NeZero N] : ch N 1 = Complex.exp ((2 * Real.pi * Complex.I) / N) := by
  unfold ch
  rcases Nat.lt_or_ge 1 N with h | h
  · haveI : Fact (1 < N) := ⟨h⟩
    rw [ZMod.val_one]; simp
  · have hN : N = 1 := by have := NeZero.pos N; omega
    subst hN
    have : (1 : ZMod 1).val = 0 := rfl
    rw [this]; simp [Complex.exp_two_pi_mul_I]

theorem diag_eq {N : ℕ} [NeZero N] (a : (ZMod N)ˣ) :
    Matrix.diagonal ![1, ((((a : ZMod N).val : ℕ) : ℤ) : ZMod N)] = ((dg a : GL (Fin 2) (ZMod N)) : Matrix (Fin 2) (Fin 2) (ZMod N)) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [dg]

theorem qConj_family : EisExp → ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F], 2 ≤ Module.finrank ℚ F → ∀ (s N : ℕ) [NeZero N] (L : Lat F), 1 ≤ s → HasLevel N L → ∀ (z : ClassGroup (𝓞 F) → ℚ), ZetaVals (2 * s) z → ∀ (g : ℂ ≃+* ℂ) (a : (ZMod N)ˣ) (κ κ' : Emb F → ℕ) (y : Fin 2 → ZMod N), ZetaAct g N a → (∀ i j : Emb F, (∀ x : F, g ((i x : ℝ) : ℂ) = ((j x : ℝ) : ℂ)) → κ' j = κ i) → y ≠ 0 → ∀ α : GL (Fin 2) (ZMod N), QConj g N (hfun (2 * s) (twist N L ((α : GL (Fin 2) (ZMod N)) : Matrix (Fin 2) (Fin 2) (ZMod N))) κ (wB N (vmul y (α)))) (hfun (2 * s) (twist N L ((α * dg a : GL (Fin 2) (ZMod N)) : Matrix (Fin 2) (Fin 2) (ZMod N))) κ' (wB N (vmul y (α * dg a)))) := by
  intro hE F _ _ _ hf s N _ L hs hL z hz g a κ κ' y hg hκ hy α
  have hact := GlobalTheory.WpFam.Act.rightActions N
  have hy' : vmul y α ≠ 0 := fun h ↦ hy ((hact.2.2.2.2.1 y α).1 h)
  have hq := (GlobalTheory.T.qConj_torsion_points N g a hg (vmul y α)).2.2 hy'
  rw [hact.2.2.1] at hq
  have hcop : IsCoprime (((a : ZMod N).val : ℕ) : ℤ) (N : ℤ) :=
    Nat.isCoprime_iff_coprime.2 (ZMod.val_coe_unit_coprime a)
  have hz1 : g (Complex.exp ((2 * Real.pi * Complex.I) / N)) =
      Complex.exp ((2 * Real.pi * Complex.I) * ((((a : ZMod N).val : ℕ) : ℤ) : ℂ) / N) := by
    rw [← ch_one, hg 1, mul_one, ch, Int.cast_natCast]
  have h := GlobalTheory.T.hilbert_eisenstein_jet_galois_conj_coefficients hE F hf s N (twist N L (α : Matrix (Fin 2) (Fin 2) (ZMod N))) hs (NeZero.pos N)
    (GlobalTheory.HilbFam.hasLevel_twist_of_hasLevel F N L _ hL) z hz g _ κ κ' _ _ hcop hz1 hκ hq
  rw [diag_eq, GlobalTheory.T.hilbertLatticeTwistByMatrixModN_mul F N L _ _ hL.2, ← Units.val_mul] at h
  exact h

end GlobalTheory.HilbFam.GalFamily
end

section

open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
open GlobalTheory.LatVal (Sz)
open GlobalTheory.LatJet (EisExp IsEis FR)

namespace GlobalTheory.HilbFam

theorem jet_conj_expand : EisExp → ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F], 2 ≤ Module.finrank ℚ F → ∀ (s N : ℕ) (L : Lat F), 1 ≤ s → 0 < N → HasLevel N L → ∀ (τ : ℍ) (κ : Emb F → ℕ) (Ch : ℍ → ℂ), jet (2 * s) L κ τ 1 (starRingEnd ℂ (τ : ℂ) - τ) * ((Real.pi / τ.im : ℝ) : ℂ) ^ (∑ i, κ i) / (2 * Real.pi * Complex.I) ^ wt (2 * s) κ = ∑ μ ∈ Finset.Iic κ, ((∏ i, rco (2 * s) (κ i) (μ i) : ℤ) : ℂ) * (((Real.pi / τ.im : ℝ) : ℂ) / (2 * Real.pi * Complex.I) ^ 2 - Ch τ) ^ (∑ i, (κ i - μ i)) * hfun (2 * s) L μ Ch τ := by
  intro hE F _ _ _ hf s N L hs hN hL τ κ Ch
  have him : 0 < (τ : ℂ).im := τ.im_pos
  have hne : τ.im ≠ 0 := τ.im_pos.ne'
  set v : ℂ := ((Real.pi / τ.im : ℝ) : ℂ) with hv
  set T : ℂ := 2 * Real.pi * Complex.I with hT
  have hT0 : T ≠ 0 := by
    simp [hT, Real.pi_ne_zero, Complex.I_ne_zero]
  have hw : v * (starRingEnd ℂ (τ : ℂ) - τ) = -T := by
    have : starRingEnd ℂ (τ : ℂ) - τ = -(2 * ((τ : ℂ).im : ℂ) * Complex.I) := by
      apply Complex.ext <;> simp <;> ring
    rw [this, hv, hT]
    have : ((τ : ℂ).im : ℂ) = (τ.im : ℂ) := rfl
    rw [this]; push_cast
    have h0 : (τ.im : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hne
    field_simp
  set C : ℂ := T ^ 2 * Ch τ with hC
  have h1 := GlobalTheory.T.hilbert_eisenstein_jet_smul_direction hE F hf s N L hs hN hL τ 1 (starRingEnd ℂ (τ : ℂ) - τ) v κ him
  have h2 := GlobalTheory.T.hilbert_eisenstein_jet_add_direction hE F hf s N L hs hN hL τ C (-T) (v - C) κ him
  rw [mul_one, hw] at h1
  have h3 : jet (2 * s) L κ τ 1 (starRingEnd ℂ (τ : ℂ) - τ) * v ^ (∑ i, κ i) = jet (2 * s) L κ τ (C + (v - C)) (-T) := by
    rw [add_sub_cancel, h1, mul_comm]
  rw [h3, h2, Finset.sum_div]
  refine Finset.sum_congr rfl fun μ hμ ↦ ?_
  have hle : μ ≤ κ := Finset.mem_Iic.mp hμ
  have hwt : wt (2 * s) κ = wt (2 * s) μ + 2 * ∑ i, (κ i - μ i) := by
    have : ∑ i, κ i = ∑ i, μ i + ∑ i, (κ i - μ i) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ ↦ (Nat.add_sub_of_le (hle i)).symm
    simp only [wt, this]; ring
  have hsub : v / T ^ 2 - Ch τ = (v - C) / T ^ 2 := by
    rw [hC]; field_simp
  rw [hsub, hfun, ← hT, ← hC, hwt, pow_add, pow_mul, div_pow]
  field_simp

end GlobalTheory.HilbFam
end

section

open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
open GlobalTheory.LatVal (Sz)
open GlobalTheory.LatJet (EisExp IsEis FR)
open GlobalTheory.CMVal (OF Af lattice IsCMType)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (IsDefSum IsEisValue polydisc)

namespace GlobalTheory.HilbFam

theorem iterD_defSum_eq_jet : EisExp → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] [DecidableEq I] (φ : I → E →+* ℂ) (e : I ≃ Emb (FR E)) (θ : E) (τ : ℍ) (Λ : Set E) (L : Lat (FR E)) (n : ℕ) (s N : ℕ) (g : (I → ℂ) → ℂ) (κ : I → ℕ) (u : List I), 2 ≤ Module.finrank ℚ (FR E) → 1 ≤ s → 0 < N → HasLevel N L → (∀ i (x : FR E), φ i (x : E) = ((e i x : ℝ) : ℂ)) → (∀ i, φ i θ = (τ : ℂ)) → 0 < n → (∀ x : Fin 2 → FR E, x ∈ L ↔ ∃ y ∈ Λ, (n : E) * y = (x 0 : E) * θ + (x 1 : E)) → IsDefSum φ (2 * s) Λ g → (∀ i, u.count i = κ i) → iterD u g 0 = (n : ℂ) ^ (2 * s * Module.finrank ℚ (FR E)) * jet (2 * s) L (fun j ↦ κ (e.symm j)) τ 1 (starRingEnd ℂ (τ : ℂ) - τ) := by
  intro hE E _ _ _ I _ _ φ e θ τ Λ L n s N g κ u hf hs hN hL hφ hθ hn hLΛ hg hu
  have hI : Nonempty I := by
    obtain ⟨σ⟩ : Nonempty (FR E →+* ℂ) := by
      rw [← Fintype.card_pos_iff, NumberField.Embeddings.card]; omega
    exact ⟨e.symm (NumberField.ComplexEmbedding.IsReal.embedding
      (IsTotallyReal.complexEmbedding_isReal σ))⟩
  set W : (Emb (FR E) → ℂ) → ℂ := fun w ↦ (cK (FR E) (2 * s) : ℂ) *
    gval (2 * s) L (fun j ↦ (τ : ℂ) + w j * (1 * (τ : ℂ) + (starRingEnd ℂ (τ : ℂ) - τ))) (fun j ↦ 1 + w j * 1) with hW
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have key : g =ᶠ[nhds 0] fun z ↦ (n : ℂ) ^ (2 * s * Module.finrank ℚ (FR E)) * W (fun j ↦ z (e.symm j)) := by
    filter_upwards [Metric.ball_mem_nhds (0 : I → ℂ) one_pos] with z hz
    have hzp : z ∈ polydisc I := fun i ↦ by
      have := norm_le_pi_norm z i
      rw [Metric.mem_ball, dist_zero_right] at hz
      exact lt_of_le_of_lt this hz
    obtain ⟨G, hG, hgz⟩ := hg z hzp
    have hv := GlobalTheory.T.deformedLattice_value_eq_hilbertEisenstein_value E I φ e θ τ Λ L n (2 * s) z G hI ⟨s, two_mul s⟩ hφ hθ hn hLΛ hG
    have hu' := GlobalTheory.HilbFam.gval_eq_of_isGVal (FR E) (2 * s) L _ _ _ hv
    simp only [hW]
    rw [hu', hgz]
    have : (GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.cWt E (2 * s) : ℂ) = (cK (FR E) (2 * s) : ℂ) := rfl
    rw [this, inv_pow, ← pow_mul, mul_comm (Module.finrank ℚ (FR E)) (2 * s)]
    have h1 : (n : ℂ) ^ (2 * s * Module.finrank ℚ (FR E)) ≠ 0 := pow_ne_zero _ hn0
    rw [mul_left_comm, mul_inv_cancel_left₀ h1]
  rw [GlobalTheory.HilbFam.iterD_eq_of_eventuallyEq I u g _ 0 key, GlobalTheory.HilbFam.iterD_const_mul_reindex I (Emb (FR E)) e u W _ 0]
  congr 1
  have hc : ∀ j, (u.map e).count j = κ (e.symm j) := fun j ↦ by
    rw [← hu (e.symm j)]
    conv_lhs => rw [← e.apply_symm_apply j]
    convert List.count_map_of_injective u e e.injective (e.symm j)
  have := GlobalTheory.T.iterated_derivative_eq_hilbert_eisenstein_jet hE (FR E) hf s N L hs hN hL τ 1 (starRingEnd ℂ (τ : ℂ) - τ) (fun j ↦ κ (e.symm j)) (u.map e) τ.im_pos hc
  exact this

end GlobalTheory.HilbFam
end

section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp)
open GlobalTheory.DeRham (push push_comp push_congr push_id push_mul)
open GlobalTheory.AbDual (isMonHom_one push_one)

set_option autoImplicit false
noncomputable section
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PolPrimeTo

section Push

variable {S : Scheme.{0}} {R : Type} [CommRing R] {I : Ideal R} (κ : DividedPowers I) (t : S ⟶ Sp R)

theorem isMonHom_id_pow (A : Over S) [GrpObj A] [IsCommMonObj A] (n : ℕ) : IsMonHom ((𝟙 A) ^ n : A ⟶ A) := by
  induction n with
  | zero => rw [pow_zero]; exact isMonHom_one A A
  | succ n ih => rw [pow_succ]; exact inferInstanceAs (IsMonHom (lift ((𝟙 A) ^ n) (𝟙 A) ≫ μ[A]))

theorem push_id_pow (A : Over S) [GrpObj A] [IsCommMonObj A] (n : ℕ) :
    haveI := isMonHom_id_pow A n
    push κ t ((𝟙 A) ^ n : A ⟶ A) = (n : R) • LinearMap.id := by
  induction n with
  | zero =>
    haveI := isMonHom_id_pow A 0
    rw [push_congr κ t (pow_zero (𝟙 A)), push_one, Nat.cast_zero, zero_smul]
  | succ n ih =>
    haveI := isMonHom_id_pow A n
    haveI := isMonHom_id_pow A (n + 1)
    haveI : IsMonHom ((𝟙 A) ^ n * 𝟙 A) := inferInstanceAs (IsMonHom (lift ((𝟙 A) ^ n) (𝟙 A) ≫ μ[A]))
    rw [push_congr κ t (pow_succ (𝟙 A) n), push_mul, ih, push_id, Nat.cast_succ, add_smul, one_smul]

end Push

theorem bijective_push {S : Scheme.{0}} {R : Type} [CommRing R] {I : Ideal R} (κ : DividedPowers I) (t : S ⟶ Sp R)
    {A B : Over S} [GrpObj A] [GrpObj B] [IsCommMonObj A] [IsCommMonObj B] (f : A ⟶ B) (h : B ⟶ A)
    [IsMonHom f] [IsMonHom h] (m : ℕ) (hm : IsUnit (m : R)) (e₁ : f ≫ h = 𝟙 A ^ m) (e₂ : h ≫ f = 𝟙 B ^ m) :
    Function.Bijective (push κ t f) := by
  haveI := isMonHom_id_pow A m
  haveI := isMonHom_id_pow B m
  have k₁ : ∀ x, push κ t h (push κ t f x) = (m : R) • x := fun x ↦ by
    rw [← LinearMap.comp_apply, ← push_comp, push_congr κ t e₁, push_id_pow]; rfl
  have k₂ : ∀ y, push κ t f (push κ t h y) = (m : R) • y := fun y ↦ by
    rw [← LinearMap.comp_apply, ← push_comp, push_congr κ t e₂, push_id_pow]; rfl
  refine ⟨fun x y hxy ↦ ?_, fun y ↦ ⟨push κ t h ((↑hm.unit⁻¹ : R) • y), ?_⟩⟩
  · have e := congrArg (push κ t h) hxy
    rw [k₁, k₁] at e
    exact (hm.smul_left_cancel).1 e
  · rw [k₂, smul_smul, hm.mul_val_inv, one_smul]

end GlobalTheory.PolPrimeTo
end
end

section

open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.lifts_natural_of_obstructionOne_zero : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (R₁ : Type) [CommRing R₁] [Algebra R₀ R₁] (α : Aug I π R₁) (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀), Par s₀ → Module.Projective R₀ (GlobForm s₀) → ∀ (C' : Type) [Category.{0} C'] (F' : C' ⥤ CommAlgCat.{0} R₀) (L : Pre I π (OAff s₀)) (L' : Pre I π F') (n : CoefMap (RingHom.id R₀) (OAff s₀) F') (l : ∀ T : C', L.B (n.G.obj T) →ₐ[R] L'.B T), L.IsLift L' n l → (∀ w, L.IsOb1 L' n l α w 0) → ∃ l' : ∀ T : C', L.B (n.G.obj T) →ₐ[R] L'.B T, L.IsLift L' n l' ∧ L.IsNat L' n l' := by
  first | exact @GlobalTheory.Obs.exists_natural_lift_of_ob1_eq_zero | exact GlobalTheory.Obs.exists_natural_lift_of_ob1_eq_zero | (intros; apply GlobalTheory.Obs.exists_natural_lift_of_ob1_eq_zero <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

theorem _root_.GlobalTheory.T.red_c1_eq_c1_of_dvd : ∀ (Q q : ℕ) [NeZero Q], q ∣ Q → ∀ E : Spc, Inv Q E → ∀ L : E ⟶ ofCat (glCat 1), red Q q E 2 1 (c1 Q L) = c1 q L := by
  first
  | exact @GlobalTheory.EtC.RedChern.coefficientReduction_firstChernClass_tateTwist
  | exact GlobalTheory.EtC.RedChern.coefficientReduction_firstChernClass_tateTwist
  | (intros; apply GlobalTheory.EtC.RedChern.coefficientReduction_firstChernClass_tateTwist <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

theorem _root_.GlobalTheory.T.tateTwistCohomology_spec_twist_independent : ∀ (q : ℕ) [NeZero q] (A : Type) [CommRing A], IsUnit (q : A) → (∃ ζ : A, Polynomial.aeval ζ (Polynomial.cyclotomic q ℤ) = 0) → ∀ n i j : ℤ, Nonempty (Ht q (sp A) n i ≃+ Ht q (sp A) n j) := by
  first | (exact @GlobalTheory.EtC.untwist) | (exact GlobalTheory.EtC.untwist) | (intros; apply GlobalTheory.EtC.untwist  <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

theorem _root_.GlobalTheory.T.exists_kummer_boundary_etale_cohomology : ∀ (q : ℕ) [NeZero q], ∃ κ : (restr (Int.castRingHom (ZMod q))).obj (tw q 1) ⟶ Gm, (∀ (U : Scheme.{0}) (ζ : Prim q Γ(U, ⊤)) (u : (Γ(U, ⊤))ˣ), (u : Γ(U, ⊤)) = ζ.1 → Sec.map κ (show Sec ((restr (Int.castRingHom (ZMod q))).obj (tw q 1)) U from twGen 1 ζ) = unitSec u) ∧ ∃ bd : ∀ (E : Spc) (n : ℤ), H ℤ E Gm n →+ Ht q E (n + 1) 1, (∀ {E E' : Spc} (f : E ⟶ E'), Inv q E' → ∀ (n : ℤ) x, pull _ f _ _ (bd E' n x) = bd E n (pull _ f _ _ x)) ∧ (∀ (E : Spc), Inv q E → ∀ n : ℤ, Function.Exact (HK.post ℤ ((chains ℤ).obj E) ((q : ℤ) • 𝟙 Gm) n) (bd E n) ∧ Function.Exact (bd E n) (fun c => HK.post ℤ ((chains ℤ).obj E) κ (n + 1) (restrH (Int.castRingHom (ZMod q)) E (tw q 1) (n + 1) c)) ∧ Function.Exact (fun c => HK.post ℤ ((chains ℤ).obj E) κ (n + 1) (restrH (Int.castRingHom (ZMod q)) E (tw q 1) (n + 1) c)) (HK.post ℤ ((chains ℤ).obj E) ((q : ℤ) • 𝟙 Gm) (n + 1))) ∧ (∃ s : ℤˣ, ∀ (X : Scheme.{0}) (u : (Γ(X, ⊤))ˣ), IsUnit (q : Γ(X, ⊤)) → bd (sch.obj X) 0 (secClass Gm (unitSec u)) = s • kum q u) ∧ ∃ s : ℤˣ, ∀ (E : Spc) (L : E ⟶ ofCat (glCat 1)), Inv q E → bd E 1 (picClass L) = s • c1 q L := by
  first | (exact @GlobalTheory.kummer_boundary) | (exact GlobalTheory.kummer_boundary) | (intros; apply GlobalTheory.kummer_boundary <;> assumption)
end

section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.JHMult

namespace GlobalTheory.SegDualProof

theorem segDual_exists_terms : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], ∀ D : IrrGL (k := k) → IrrGL (k := k), (∀ x y, DualCl x y ↔ y = D x) → (∀ x, D (D x) = x) → (∀ (x : IrrGL (k := k)) (s : ℂ), D (x.nu s) = (D x).nu (-s)) → (∀ x, x.IsCusp → (D x).IsCusp) → (∀ x, (D x).1 = x.1) → ∀ Δ : Segment k, (∃ Δ', SegDual Δ Δ') ∧ ∀ Δ', SegDual Δ Δ' → Δ'.len = Δ.len ∧ ∀ a : ℕ, a < Δ.len → Δ'.first.nu (a : ℂ) = D (Δ.first.nu ((Δ.len : ℂ) - 1 - a)) := by
  intro k _ _ _ _ D hD _ hnu hcusp _ Δ
  have hρ : (D (Δ.first.nu ((Δ.len : ℂ) - 1))).IsCusp := hcusp _ (Δ.isCusp_first.nu _)
  refine ⟨⟨Segment.ofFirst _ hρ Δ.len Δ.len_pos, rfl, (hD _ _).2 rfl⟩, ?_⟩
  rintro Δ' ⟨hl, hd⟩
  refine ⟨hl, fun a _ => ?_⟩
  rw [(hD _ _).1 hd]
  have h1 := hnu (Δ.first.nu ((Δ.len : ℂ) - 1)) (-(a : ℂ))
  rw [neg_neg, IrrGL.nu_nu, ← sub_eq_add_neg] at h1
  exact h1.symm

end GlobalTheory.SegDualProof
end

section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.JHMult

namespace GlobalTheory.LocLanglands

theorem precedes_of_segDual_precedes :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k],
    ∀ D : IrrGL (k := k) → IrrGL (k := k), (∀ x y, DualCl x y ↔ y = D x) → (∀ x, D (D x) = x) →
      (∀ (x : IrrGL (k := k)) (s : ℂ), D (x.nu s) = (D x).nu (-s)) → (∀ x, x.IsCusp → (D x).IsCusp) →
      (∀ x, (D x).1 = x.1) → ∀ Δ Γ Δ' Γ' : Segment k, SegDual Δ Δ' → SegDual Γ Γ' → Γ'.Precedes Δ' → Δ.Precedes Γ := by
  intro k _ _ _ _ D hD hDD hnu _ _ Δ Γ Δ' Γ' ⟨l1, d1⟩ ⟨l2, d2⟩ H
  obtain ⟨j, h0, h1, h2, e⟩ := Segment.precedes_iff.1 H
  rw [(hD _ _).1 d1, (hD _ _).1 d2] at e
  have e' := congrArg D e
  rw [hnu (D _), hDD, hDD, IrrGL.nu_nu] at e'
  rw [l1] at h2
  rw [l2] at h1 h2
  obtain ⟨i, hi⟩ : ∃ i : ℕ, j + Δ.len = Γ.len + i := ⟨j + Δ.len - Γ.len, by omega⟩
  refine Segment.precedes_iff.2 ⟨i, by omega, by omega, by omega, ?_⟩
  have hc : (j : ℂ) + Δ.len = Γ.len + i := by exact_mod_cast hi
  have e2 := congrArg (fun x => IrrGL.nu x (-((Γ.len : ℂ) - 1 + -(j : ℂ)))) e'
  simp only [IrrGL.nu_nu, add_neg_cancel, IrrGL.nu_zero] at e2
  rw [← e2]
  congr 1
  linear_combination hc

end GlobalTheory.LocLanglands
end

section

open ValuativeRel Matrix MeasureTheory
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.LocLanglands GlobalTheory.GamMul DiscreteGroups.sglob.LConv

theorem _root_.GlobalTheory.T.centralCharacter_subquotient_productIrreducibles : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], (∀ x : IrrGL (k := k), ∃ ω : kˣ →* ℂˣ, HasCentralChar x.rep ω) ∧ ∀ (t m : ℕ) (x : Fin t → IrrGL (k := k)) (hd : ∑ a, (x a).1 = m) (ω : Fin t → kˣ →* ℂˣ), (∀ a, HasCentralChar (x a).rep (ω a)) → ∀ (τ : IrrRep (GL (Fin m) k)) (ω' : kˣ →* ℂˣ), IsSubquotient τ.ρ (prodIrr x hd) → HasCentralChar τ.ρ ω' → ω' = ∏ a, ω a := by
  first | exact @GlobalTheory.GamMul.centralChar_subquotient_prodIrr | exact GlobalTheory.GamMul.centralChar_subquotient_prodIrr | (intros; apply GlobalTheory.GamMul.centralChar_subquotient_prodIrr <;> assumption)
end
