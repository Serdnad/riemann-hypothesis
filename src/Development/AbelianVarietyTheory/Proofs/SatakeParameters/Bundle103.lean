module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsPlaceCofactorValuationLowerBound
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle097
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle085
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsUnitarisableOfCharIff
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle088
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemParahoricOfTrivialReduction
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.RedPEqZeroOfDiv
public import Formalism.LocalToGlobal.Columns.Bundle010
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle096
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle025
public import Formalism.SatakeDualWeyl.KpqSubgroupCompact
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsNotCongPow
import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle080
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasExponentZeroIff
import Formalism.ConjugateSelfDual.Bundle001
import ReciprocityTheory.GaloisValuations.GlobalA
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.FrobeniusOrbits GlobalTheory.TwU Classical

namespace GlobalTheory.TwU.LowGen

theorem le_order_subst' {σ τ K : Type} [Finite σ] [Field K] {a : σ → MvPowerSeries τ K}
    (ha : ∀ s, MvPowerSeries.constantCoeff (a s) = 0) (f : MvPowerSeries σ K) :
    f.order ≤ (MvPowerSeries.subst a f).order := by
  refine le_trans ?_ (MvPowerSeries.le_order_subst (MvPowerSeries.hasSubst_of_constantCoeff_zero ha) f)
  have h1 : (1 : ℕ∞) ≤ ⨅ i, (a i).order :=
    le_iInf fun i => MvPowerSeries.one_le_order_iff_constCoeff_eq_zero.mpr (ha i)
  calc f.order = 1 * f.order := (one_mul _).symm
    _ ≤ _ := by gcongr

theorem applyD_eq_zero {σ τ K : Type} [Field K] (P : MvPolynomial σ (MvPolynomial τ ℤ)) (f : MvPowerSeries σ K)
    (h : ((P.totalDegree + 1 : ℕ) : ℕ∞) ≤ f.order) : applyD P f = 0 := by
  unfold applyD
  refine Finset.sum_eq_zero fun n hn => ?_
  have h1 : n.degree ≤ P.totalDegree := MvPolynomial.le_totalDegree hn
  have h2 : MvPowerSeries.coeff n f = 0 := by
    apply MvPowerSeries.coeff_of_lt_order
    refine lt_of_lt_of_le ?_ h
    exact_mod_cast Nat.lt_succ_of_le h1
  rw [h2, mul_zero, zero_smul]

noncomputable def applyDL {σ τ : Type} (K : Type) [Field K] (P : MvPolynomial σ (MvPolynomial τ ℤ)) :
    MvPowerSeries σ K →ₗ[K] MvPolynomial τ K where
  toFun := applyD P
  map_add' f g := by
    simp only [applyD, map_add (f := _), mul_add, add_smul, Finset.sum_add_distrib]
  map_smul' c f := by
    simp only [applyD, RingHom.id_apply, Finset.smul_sum, smul_smul, MvPowerSeries.coeff_smul]
    refine Finset.sum_congr rfl fun n _ => ?_
    congr 1
    ring

theorem applyD_map {σ τ K L : Type} [Field K] [Field L] (φ : K →+* L) (P : MvPolynomial σ (MvPolynomial τ ℤ))
    (f : MvPowerSeries σ K) :
    applyD P (MvPowerSeries.map φ f) = MvPolynomial.map φ (applyD P f) := by
  unfold applyD

  rw [map_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [MvPolynomial.smul_eq_C_mul, MvPolynomial.smul_eq_C_mul, map_mul (MvPolynomial.map φ), MvPolynomial.map_C,
    MvPolynomial.map_map, RingHom.ext_int (φ.comp (Int.castRingHom K)) (Int.castRingHom L)]
  simp

variable {p : ℕ} [Fact p.Prime]

theorem constantCoeff_coordZA (X : Sys p) (K : Type) [Field K] [Algebra (K0 p) K] (j : ℕ) (s : X.EA j ⊕ X.EA j) :
    MvPowerSeries.constantCoeff (X.coordZA K j s) = 0 := by
  rcases s with ⟨v, r, a, b⟩ | ⟨v, r, a, b⟩ <;> simp [Sys.coordZA, map_sum]

theorem map_coordZA (X : Sys p) (K : Type) [Field K] [Algebra (K0 p) K] (j : ℕ) (s : X.EA j ⊕ X.EA j) :
    MvPowerSeries.map (algebraMap (K0 p) K) (X.coordZA (K0 p) j s) = X.coordZA K j s := by
  rcases s with ⟨v, r, a, b⟩ | ⟨v, r, a, b⟩ <;> simp [Sys.coordZA, map_sum]

theorem ThZA_map (X : Sys p) (K : Type) [Field K] [Algebra (K0 p) K] (j : ℕ)
    (f : MvPowerSeries (X.EA j ⊕ X.EA j) (K0 p)) :
    X.ThZA K j (MvPowerSeries.map (algebraMap (K0 p) K) f) =
      MvPowerSeries.map (algebraMap (K0 p) K) (X.ThZA (K0 p) j f) := by
  unfold Sys.ThZA
  rw [MvPowerSeries.map_subst (MvPowerSeries.hasSubst_of_constantCoeff_zero (constantCoeff_coordZA X _ j))]
  congr 1
  funext s
  exact (map_coordZA X K j s).symm

theorem p_ne_zero (K : Type) [Field K] [Algebra (K0 p) K] : (p : K) ≠ 0 := by
  have h : (p : WW p) ≠ 0 := WittVector.p_nonzero p (kb p)
  have h2 := (map_ne_zero_iff _ (IsFractionRing.injective (WW p) (K0 p))).mpr h
  have h3 := (map_ne_zero (algebraMap (K0 p) K)).mpr h2
  simpa using h3

theorem geC_of_mem {X : Sys p} (Y : Pend X) (g : ℝ) (y : Y.Kc) (hy : y ∈ Y.Oc) :
    Y.geC ((p : Y.Kc) ^ ⌈g⌉ * y) g := by
  intro a b hb hab
  have hp := p_ne_zero (p := p) Y.Kc
  have h1 : a ≤ ⌈g⌉ * b := by
    have : (a : ℝ) ≤ (⌈g⌉ : ℝ) * b := hab.trans (mul_le_mul_of_nonneg_right (Int.le_ceil g) (Nat.cast_nonneg b))
    exact_mod_cast this
  obtain ⟨k, hk⟩ := Int.eq_ofNat_of_zero_le (sub_nonneg.mpr h1)
  have : ((p : Y.Kc) ^ ⌈g⌉ * y) ^ b * (p : Y.Kc) ^ (-a) = (p : Y.Kc) ^ k * y ^ b := by
    rw [mul_pow, ← zpow_natCast ((p : Y.Kc) ^ ⌈g⌉), ← zpow_mul, mul_right_comm, ← zpow_add₀ hp, ← sub_eq_add_neg, hk,
      zpow_natCast]
  rw [this]
  exact Y.Oc.mul_mem (Y.Oc.pow_mem (natCast_mem Y.Oc p) _) (Y.Oc.pow_mem hy _)

theorem cofactor_lower_bound_of_place_bound_witt : ∀ (p : ℕ) [Fact p.Prime] (X : Sys p) (Y : Pend X) (j : ℕ) (v : X.Pl) (g : ℝ),
    MvPowerSeries.constantCoeff Y.be = 0 → IsPlaceCofactorValuationLowerBound X Y.be j v g → Y.LowAt j v g := by
  intro p _ X Y j v g _ hL U hU I m
  choose Un hUn using GlobalTheory.T.exists_inParam_eq_monomial_low_coeff_zero p (X.EA j ⊕ X.EA j)
  set P := X.PIv j I v with hP
  set d := P.totalDegree with hd
  have hfin : {n : (X.EA j ⊕ X.EA j) →₀ ℕ | n.degree ≤ d}.Finite := Finsupp.finite_of_degree_le d
  set S := hfin.toFinset with hS
  have hspan := GlobalTheory.T.lowCoefficients_of_parameterCoefficients p (X.EA j ⊕ X.EA j) Y.Kc Un hUn U d S (fun n hn => hfin.mem_toFinset.mpr hn)
  have hint : ∀ n, IntS p (inParam p (Un n)) := fun n =>
    ⟨MvPowerSeries.monomial n 1, by rw [(hUn n).1, MvPowerSeries.map_monomial, RingHom.map_one]⟩
  choose a ha using fun n => hL (Un n) (hint n) I m
  have hE : Y.PhAt j v = phAt X Y.be j v := rfl
  rw [hE]
  set E := expS p (-phAt X Y.be j v) with hEdef
  set φ := algebraMap (K0 p) Y.Kc with hφ
  set c : _ → Y.Kc := fun n => MvPowerSeries.coeff n (inParamK p Y.Kc U) with hc
  have hsub := MvPowerSeries.hasSubst_of_constantCoeff_zero (constantCoeff_coordZA X Y.Kc j)
  set A := U - ∑ n ∈ S, c n • MvPowerSeries.map φ (Un n) with hA
  have hAo : ((d + 1 : ℕ) : ℕ∞) ≤ A.order := by
    apply MvPowerSeries.nat_le_order
    intro k hk

    rw [hA, map_sub, hspan k (Nat.le_of_lt_succ hk), map_sum, sub_eq_zero]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [MvPowerSeries.coeff_smul, MvPowerSeries.coeff_map]
  have hz : applyD P (X.ThZA Y.Kc j (MvPowerSeries.map φ E * A)) = 0 := by
    apply applyD_eq_zero
    refine le_trans ?_ (le_order_subst' (constantCoeff_coordZA X Y.Kc j) _)
    exact hAo.trans (le_trans le_add_self MvPowerSeries.le_order_mul)
  have hU' : MvPowerSeries.map φ E * U =
      MvPowerSeries.map φ E * A + ∑ n ∈ S, c n • MvPowerSeries.map φ (E * Un n) := by
    rw [hA, mul_sub, Finset.mul_sum]
    simp only [mul_smul_comm, map_mul, sub_add_cancel]
  have hTh : ∀ f, applyD P (X.ThZA Y.Kc j f) =
      ((applyDL Y.Kc P) ∘ₗ (MvPowerSeries.substAlgHom (R := Y.Kc) hsub).toLinearMap) f := by
    intro f
    rw [Sys.ThZA, ← MvPowerSeries.coe_substAlgHom hsub]
    rfl
  have hval : AddMonoidAlgebra.coeff (applyD P (X.ThZA Y.Kc j (MvPowerSeries.map φ E * U))) m =
      (p : Y.Kc) ^ ⌈g⌉ * ∑ n ∈ S, c n * φ (algebraMap (WW p) (K0 p) (a n)) := by

    rw [hU', hTh, map_add (f := _), ← hTh, hz, zero_add, map_sum, MvPolynomial.coeff_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [map_smul, ← hTh, hφ, ThZA_map, applyD_map, MvPolynomial.coeff_smul, MvPolynomial.coeff_map, ha n, map_mul,
      map_zpow₀, map_natCast, smul_eq_mul]
    ring
  rw [hval]
  exact geC_of_mem Y g _ (Y.Oc.sum_mem fun n _ => Y.Oc.mul_mem (hU n) (Y.witt_mem_integers_Cp _))

end GlobalTheory.TwU.LowGen
end

section

open NumberField IsDedekindDomain ValuativeRel Matrix Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.InvPairing

variable {G V W : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

def pairMap (π : Representation ℂ G V) {π' : Representation ℂ G W} (hπ' : IsSmooth π')
    (B : V →ₗ[ℂ] W →ₗ[ℂ] ℂ) (hB : ∀ g a b, B (π g a) (π' g b) = B a b) :
    π'.IntertwiningMap (contra π) where
  toLinearMap :=
    { toFun := fun b => ⟨B.flip b, mem_smoothPart_of_nhds (Filter.mem_of_superset
        ((hπ' b).mem_nhds (by simp)) fun g hg => by
          have hg' : π' g b = b := hg
          ext a
          show B (π g⁻¹ a) b = B a b
          have h := hB g (π g⁻¹ a) b
          rw [hg'] at h
          rw [← h, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply])⟩
      map_add' := fun b c => Subtype.ext (by simp)
      map_smul' := fun c b => Subtype.ext (by simp) }
  isIntertwining' g := by
    refine LinearMap.ext fun b => Subtype.ext (LinearMap.ext fun a => ?_)
    show B a (π' g b) = B (π g⁻¹ a) b
    have h := hB g (π g⁻¹ a) b
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply] at h
    exact h

theorem pairMap_apply (π : Representation ℂ G V) {π' : Representation ℂ G W} (hπ' : IsSmooth π')
    (B : V →ₗ[ℂ] W →ₗ[ℂ] ℂ) (hB : ∀ g a b, B (π g a) (π' g b) = B a b) (a : V) (b : W) :
    ((pairMap π hπ' B hB b : smoothPart π.dual) : Module.Dual ℂ V) a = B a b := rfl

theorem eq_zero_of_pairMap (π : Representation ℂ G V) {π' : Representation ℂ G W} (hπ' : IsSmooth π')
    (B : V →ₗ[ℂ] W →ₗ[ℂ] ℂ) (hB : ∀ g a b, B (π g a) (π' g b) = B a b)
    (h : ∀ b, pairMap π hπ' B hB b = 0) : B = 0 :=
  LinearMap.ext fun a => LinearMap.ext fun b => by
    have := congrArg (fun l : smoothPart π.dual => (l : Module.Dual ℂ V) a) (h b)
    simpa [pairMap_apply] using this

theorem pairMap_bijective (π : Representation ℂ G V) {π' : Representation ℂ G W} (hπ' : IsSmooth π')
    (B : V →ₗ[ℂ] W →ₗ[ℂ] ℂ) (hB : ∀ g a b, B (π g a) (π' g b) = B a b) (hB0 : B ≠ 0)
    (hirr' : π'.IsIrreducible) (hirr : (contra π).IsIrreducible) :
    Function.Bijective (pairMap π hπ' B hB) := by
  set f := pairMap π hπ' B hB with hf
  constructor
  · let S : Subrepresentation π' :=
      { toSubmodule := LinearMap.ker f.toLinearMap
        apply_mem_toSubmodule := fun g v hv => by
          simp only [LinearMap.mem_ker] at hv ⊢
          have := LinearMap.congr_fun (f.isIntertwining' g) v
          simp only [LinearMap.comp_apply] at this
          rw [this, hv, map_zero] }
    rcases hirr'.eq_bot_or_eq_top S with hS | hS
    · intro x y hxy
      have : x - y ∈ S.toSubmodule := by
        show f.toLinearMap (x - y) = 0
        rw [map_sub]; exact sub_eq_zero.2 hxy
      rw [hS] at this
      exact sub_eq_zero.1 ((Submodule.mem_bot ℂ).1 this)
    · exfalso
      refine hB0 (eq_zero_of_pairMap π hπ' B hB fun b => ?_)
      have : b ∈ S.toSubmodule := by rw [hS]; exact Submodule.mem_top
      exact this
  · let R : Subrepresentation (contra π) :=
      { toSubmodule := LinearMap.range f.toLinearMap
        apply_mem_toSubmodule := fun g v hv => by
          obtain ⟨w, rfl⟩ := hv
          refine ⟨π' g w, ?_⟩
          have := LinearMap.congr_fun (f.isIntertwining' g) w
          simpa only [LinearMap.comp_apply] using this }
    rcases hirr.eq_bot_or_eq_top R with hR | hR
    · exfalso
      refine hB0 (eq_zero_of_pairMap π hπ' B hB fun b => ?_)
      have : f b ∈ R.toSubmodule := ⟨b, rfl⟩
      rw [hR] at this
      exact (Submodule.mem_bot ℂ).1 this
    · intro l
      have : l ∈ R.toSubmodule := by rw [hR]; exact Submodule.mem_top
      obtain ⟨b, hb⟩ := this
      exact ⟨b, hb⟩

end GlobalTheory.InvPairing
end
end

section

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.LatHecke Formalism.UG

namespace GlobalTheory.ElemCartan

section Dvr

variable {O K : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K]
  [IsFractionRing O K] {r : ℕ}

theorem coord_of_mem_std {x : Fin r → K} (hx : x ∈ (std O K r).1) (i : Fin r) :
    ∃ a : O, algebraMap O K a = x i := by
  apply _root_.GlobalTheory.LatHecke.coord_of_mem_std <;> assumption

end Dvr

section Adic

variable {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E))

theorem zpow_mem_iff {ϖ : w.adicCompletion E} (hϖ : IsUnifV E w ϖ) (m : ℤ) :
    ϖ ^ m ∈ w.adicCompletionIntegers E ↔ 0 ≤ m := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_zpow₀, hϖ, ← WithZero.coe_zpow,
    ← WithZero.coe_one, WithZero.coe_le_coe, ← ofAdd_zsmul, ← ofAdd_zero, Multiplicative.ofAdd_le,
    smul_eq_mul]
  omega

theorem ne_zero_of_unif {ϖ : w.adicCompletion E} (hϖ : IsUnifV E w ϖ) : ϖ ≠ 0 := by
  intro h
  rw [IsUnifV, h, map_zero] at hϖ
  exact WithZero.zero_ne_coe hϖ

theorem antitone_zero_one {n j : ℕ} (a : Fin n → ℤ) (ha : Antitone a)
    (h01 : ∀ i, a i = 0 ∨ a i = 1)
    (hS : (Finset.univ.filter fun i => a i = 1).card = j) (i : Fin n) :
    a i = 1 ↔ (i : ℕ) < j := by
  rw [← hS]
  refine (Fin.lt_card_filter_univ_iff_apply_of_imp (fun k => a k = 1) ?_).symm
  intro k l hlk hk
  have hle := ha hlk
  rcases h01 l with hl | hl <;> omega

end Adic

theorem mem_doubleCoset_of_subElem :
    ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E))
      (n : ℕ) (ϖ : w.adicCompletion E), IsUnifV E w ϖ →
      ∀ (j : ℕ), j ≤ n → ∀ (g : GL (Fin n) (w.adicCompletion E)),
        (haveI := GlobalTheory.RowSatakeBound.finite_residue w
         glMap g (std (w.adicCompletionIntegers E) (w.adicCompletion E) n).1 ∈
           Subtype.val '' subElem j (std (w.adicCompletionIntegers E) (w.adicCompletion E) n) →
         ∃ a ∈ GLint (Fin n) (Ov E w), ∃ b ∈ GLint (Fin n) (Ov E w),
           (g : Matrix (Fin n) (Fin n) (w.adicCompletion E)) =
             (a : Matrix (Fin n) (Fin n) (w.adicCompletion E)) * diagJ n ϖ j *
               (b : Matrix (Fin n) (Fin n) (w.adicCompletion E))) := by
  intro E _ _ w n ϖ hϖ j _ g hg
  have := GlobalTheory.RowSatakeBound.finite_residue w
  obtain ⟨M₀, hM, hMg⟩ := hg
  set L := std (w.adicCompletionIntegers E) (w.adicCompletion E) n with hLdef
  set M : Lat (w.adicCompletionIntegers E) (w.adicCompletion E) n := M₀ with hMdef
  have hϖ0 := ne_zero_of_unif w hϖ
  have hϖO : ϖ ∈ Ov E w := by
    have := (zpow_mem_iff w hϖ 1).2 zero_le_one
    simpa using this
  obtain ⟨a, ha, k₁, hk₁, k₂, hk₂, e⟩ := Formalism.UG.Final.CartanDecomp E w n ϖ hϖO hϖ g
  have hs₁ : glMap k₁⁻¹ L.1 = L.1 := (GlobalTheory.T.glMap_standardLattice_eq_iff_mem_GLint_adic E w n k₁⁻¹).2 (inv_mem hk₁)
  have hs₂ : glMap k₂⁻¹ L.1 = L.1 := (GlobalTheory.T.glMap_standardLattice_eq_iff_mem_GLint_adic E w n k₂⁻¹).2 (inv_mem hk₂)
  set D : GL (Fin n) (w.adicCompletion E) := k₁⁻¹ * g * k₂⁻¹ with hDdef
  have hD : (D : Matrix (Fin n) (Fin n) (w.adicCompletion E)) = diagPow E w ϖ a := by
    rw [hDdef, Units.val_mul, Units.val_mul, e]
    simp only [← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
    rw [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]

  have hDL : glMap D L.1 = (k₁⁻¹ • M).1 := by
    rw [smul_def, glLat_val, hMg, hDdef, glMap_mul, glMap_mul, hs₂]
  have hMD : k₁⁻¹ • M ∈ subElem j L := by
    have h := (smul_mem_subElem_iff k₁⁻¹ j M L).2 hM
    have hL : k₁⁻¹ • L = L := Subtype.ext (by rw [smul_def, glLat_val, hs₁])
    rwa [hL] at h
  obtain ⟨⟨hle, hidx⟩, hmax⟩ := hMD
  rw [← hDL] at hle hidx hmax
  have hDe : ∀ (x : Fin n → w.adicCompletion E) (i : Fin n),
      Matrix.toLin' (D : Matrix (Fin n) (Fin n) (w.adicCompletion E)) x i = ϖ ^ (a i) * x i := by
    intro x i
    rw [Matrix.toLin'_apply, hD, diagPow, Matrix.mulVec_diagonal]

  have hpos : ∀ i, 0 ≤ a i := by
    intro i
    have hmem : Matrix.toLin' (D : Matrix (Fin n) (Fin n) (w.adicCompletion E)) (Pi.basisFun (w.adicCompletion E) (Fin n) i) ∈ glMap D L.1 :=
      ⟨_, Submodule.subset_span ⟨i, rfl⟩, rfl⟩
    obtain ⟨c, hc⟩ := coord_of_mem_std (hle hmem) i
    rw [hDe] at hc
    simp only [Pi.basisFun_apply, Pi.single_eq_same, mul_one] at hc
    rw [← zpow_mem_iff w hϖ, ← hc]
    exact c.2

  have hle1 : ∀ i, a i ≤ 1 := by
    intro i
    have hϖm : (⟨ϖ, hϖO⟩ : w.adicCompletionIntegers E) ∈ IsLocalRing.maximalIdeal (w.adicCompletionIntegers E) := by
      apply (Valuation.mem_maximalIdeal_iff (v := (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ))))).2
      show Valued.v ϖ < 1
      rw [hϖ, ← WithZero.coe_one, WithZero.coe_lt_coe, ← ofAdd_zero, Multiplicative.ofAdd_lt]
      omega
    have hmem : (⟨ϖ, hϖO⟩ : w.adicCompletionIntegers E) • Pi.basisFun (w.adicCompletion E) (Fin n) i ∈ IsLocalRing.maximalIdeal (w.adicCompletionIntegers E) • L.1 :=
      Submodule.smul_mem_smul hϖm (Submodule.subset_span ⟨i, rfl⟩)
    obtain ⟨x, hx, hxe⟩ := hmax hmem
    obtain ⟨c, hc⟩ := coord_of_mem_std hx i
    have hxi := congrFun hxe i
    simp only [LinearMap.coe_restrictScalars] at hxi
    rw [hDe] at hxi
    have hval : (((⟨ϖ, hϖO⟩ : w.adicCompletionIntegers E) • Pi.basisFun (w.adicCompletion E) (Fin n) i) i) = ϖ := by
      simp [Algebra.smul_def]
    rw [hval] at hxi
    have hx' : x i = ϖ ^ (1 - a i) := by
      rw [zpow_sub₀ hϖ0, zpow_one, eq_div_iff (zpow_ne_zero (a i) hϖ0), mul_comm]
      exact hxi
    rw [← sub_nonneg, ← zpow_mem_iff w hϖ, ← hx', ← hc]
    exact c.2
  have h01 : ∀ i, a i = 0 ∨ a i = 1 := fun i => by
    have := hpos i; have := hle1 i; omega

  set S : Finset (Fin n) := Finset.univ.filter fun i => a i = 1 with hSdef
  have hdiag : (fun i => ϖ ^ (a i)) = fun i => if i ∈ S then ϖ else 1 := by
    funext i
    rcases h01 i with h | h <;> simp [hSdef, h]
  have hD' : (D : Matrix (Fin n) (Fin n) (w.adicCompletion E)) = Matrix.diagonal fun i => if i ∈ S then ϖ else 1 := by
    rw [hD, diagPow, hdiag]
  obtain ⟨M₂, ⟨⟨-, hidx₂⟩, -⟩, hM₂⟩ := GlobalTheory.T.glMap_diagUniformizer_elementarySublattice E w n ϖ hϖ S D hD'
  rw [hM₂] at hidx₂
  have hcard : S.card = j := by
    have h := hidx₂.symm.trans hidx
    exact Nat.pow_right_injective (two_le_qRes (O := w.adicCompletionIntegers E)) h
  have hkey := antitone_zero_one a ha h01 hcard
  refine ⟨k₁, hk₁, k₂, hk₂, ?_⟩
  rw [e]
  congr 2
  rw [diagPow, diagJ]
  congr 1
  funext i
  by_cases hi : (i : ℕ) < j
  · rw [ite_eq_left hi, (hkey i).2 hi, zpow_one]
  · rw [ite_eq_right hi]
    have : a i = 0 := (h01 i).resolve_right fun h => hi ((hkey i).1 h)
    rw [this, zpow_zero]

end GlobalTheory.ElemCartan
end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col

namespace GlobalTheory.QCong

theorem conj_extE_cong : ∀ {E : Type} [Field E] [NumberField E] [StarRing E] (P : HeightOneSpectrum (𝓞 E)) {n : ℕ} (c j D : ℕ) (h : Sp E (n + c) ≃ₗ[E] Sp E (n + c)) (κ : GLint E n P), κ ∈ GlobalTheory.TopStep.prinCong n P D → j + 1 ≤ D → (∀ x ∈ stdAt E (n + c) P, h⁻¹ x ∈ stdAt E (n + c) P ∧ ((qOf P : E) ^ j) • h x ∈ stdAt E (n + c) P) → ∀ x ∈ stdAt E (n + c) P, (qOf P : E)⁻¹ • ((h⁻¹ * GlobalTheory.CongLevel.extE c κ.1 * h) x - x) ∈ stdAt E (n + c) P := by
  intro E _ _ _ P n c j D h κ hκ hjD hh x hx
  obtain ⟨m, rfl⟩ : ∃ m, D = j + 1 + m := ⟨D - (j + 1), by omega⟩
  have hq : ((qOf P : ℕ) : E) ≠ 0 := GlobalTheory.TopStep.qOf_ne_zero
  have hu := (hh x hx).2
  have hw : GlobalTheory.CongLevel.resX c (((qOf P : E) ^ j) • h x) ∈ stdAt E n P :=
    GlobalTheory.TopStep.mem_stdAt.2 fun i => GlobalTheory.TopStep.mem_stdAt.1 hu (Fin.castAdd c i)
  have hw' := (GlobalTheory.TopStep.mem_prinCong.1 hκ) _ hw
  have key : (qOf P : E)⁻¹ • (GlobalTheory.CongLevel.extE c κ.1 (h x) - h x) = ((qOf P : E) ^ m) • Loc.inX E n c
      ((((qOf P : E) ^ (j + 1 + m))⁻¹) • (κ.1 (GlobalTheory.CongLevel.resX c (((qOf P : E) ^ j) • h x)) - GlobalTheory.CongLevel.resX c (((qOf P : E) ^ j) • h x))) := by
    rw [GlobalTheory.CongLevel.extE_apply, add_sub_cancel_left, map_smul (GlobalTheory.CongLevel.resX c), map_smul κ.1, ← smul_sub, smul_smul,
      ← map_smul, ← map_smul, smul_smul]
    congr 2
    field_simp
    ring
  have e1 : (h⁻¹ * GlobalTheory.CongLevel.extE c κ.1 * h) x - x = h⁻¹ (GlobalTheory.CongLevel.extE c κ.1 (h x) - h x) := by
    rw [map_sub]
    congr 1
    exact (LinearEquiv.symm_apply_apply h x).symm
  rw [e1, ← map_smul, key]
  refine (hh _ ?_).1
  refine GlobalTheory.TopStep.mem_stdAt.2 fun l => ?_
  rw [Pi.smul_apply, smul_eq_mul, GlobalTheory.CongLevel.inX_apply]
  split_ifs with hl
  · exact (GlobalTheory.TopStep.intAt_pow (GlobalTheory.TopStep.intAt_nat _) m).mul (GlobalTheory.TopStep.mem_stdAt.1 hw' _)
  · rw [mul_zero]; exact GlobalTheory.TopStep.intAt_zero

end GlobalTheory.QCong
end

section

open NumberField IsDedekindDomain


theorem _root_.GlobalTheory.T.intAtAdele_mul_of_placeComponent_eq_zero : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (v : HeightOneSpectrum (𝓞 F)) (Q : HeightOneSpectrum (𝓞 E)), Formalism.L2.Col.IsOver v Q → ∀ a : TensorProduct F E (FiniteAdeleRing (𝓞 F) F), Formalism.UG.prV (E := E) v a = 0 → ∀ c : E, Formalism.L2.Col.IntAtA (F := F) Q (Formalism.L2.Col.iA F E c * a) := by
  first | exact @GlobalTheory.VanishAtOver.intAtA_mul_of_prV_eq_zero | exact GlobalTheory.VanishAtOver.intAtA_mul_of_prV_eq_zero | (intros; apply GlobalTheory.VanishAtOver.intAtA_mul_of_prV_eq_zero <;> assumption)
end
