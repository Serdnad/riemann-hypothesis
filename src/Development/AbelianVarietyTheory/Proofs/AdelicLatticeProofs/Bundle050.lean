module

public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle001
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.TensorProduct.Maps
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle003
public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle002
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle035
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle048
import Mathlib.Algebra.Module.StablyFree.Basic
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle045
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle033
public import Mathlib.Basic.Complex.Basic
public import Mathlib.RepresentationTheory.Semisimple
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle049
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.Topology.Algebra.Module.ModuleTopology
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle023
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
import Mathlib.RingTheory.Henselian
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
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Hat1
public import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic

@[expose] public section

section

open NumberField IsDedekindDomain Matrix GlobalTheory.UTrans GlobalTheory.AdLat
open scoped TensorProduct

theorem _root_.GlobalTheory.T.exists_traceZero_adjustment_of_hermitian_lattice : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (c : E ≃ₐ[F] E) (n : ℕ) (G : Matrix (Fin n) (Fin n) E), Module.finrank F E = 2 → IsHerm (c : E →+* E) G → ∀ L : Submodule (𝓞 E) (Fin n → E), L.FG → Submodule.span E (L : Set (Fin n → E)) = ⊤ → ∀ (x : Fin n → E) (t : E) (b : ℕ), 0 < b → t + c t = 0 → ∃ (t' : E) (k e : ℕ), t' + c t' = 0 ∧ k.Coprime b ∧ ∀ v ∈ L, (∃ w ∈ L, k • (tv (c : E →+* E) G x t' *ᵥ v - tv (c : E →+* E) G x t *ᵥ v) = b • w) ∧ b ^ e • (tv (c : E →+* E) G x t' *ᵥ v) ∈ L ∧ b ^ e • (tv (c : E →+* E) G x (-t') *ᵥ v) ∈ L := by
  first | exact @GlobalTheory.TvAdjust.exists_tv_adjust | exact GlobalTheory.TvAdjust.exists_tv_adjust | (intros; apply GlobalTheory.TvAdjust.exists_tv_adjust <;> assumption)
end

section

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin

theorem tensor_eq_zero_of_forall_contract {V W : Type} [AddCommGroup V] [Module ℚ V] [AddCommGroup W]
    [Module ℚ W] (t : V ⊗[ℚ] W)
    (h : ∀ m : W →ₗ[ℚ] ℚ, TensorProduct.rid ℚ V (LinearMap.lTensor V m t) = 0) : t = 0 := by
  first
  | exact @_root_.GlobalTheory.CoefficientContraction.eq_zero_of_contractions
  | exact _root_.GlobalTheory.CoefficientContraction.eq_zero_of_contractions
  | (apply _root_.GlobalTheory.CoefficientContraction.eq_zero_of_contractions <;> assumption)
  | (intros; apply _root_.GlobalTheory.CoefficientContraction.eq_zero_of_contractions <;> assumption)
  | (intros; apply @_root_.GlobalTheory.CoefficientContraction.eq_zero_of_contractions <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.CoefficientContraction.eq_zero_of_contractions ..)

theorem aeval_sum_elim_eq_zero_of_tensor {ι : Type} [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ))
    (hΓ : ∀ σ : ℂ ≃+* ℂ, ∀ g ∈ Γ, g.map σ ∈ Γ)
    (t : MvPolynomial (ι × ι) ℚ ⊗[ℚ] MvPolynomial (ι × ι) ℚ)
    (ht : ∀ g ∈ Γ, ∀ h ∈ Γ, Algebra.TensorProduct.productMap
      (MvPolynomial.aeval (fun ij : ι × ι => g ij.1 ij.2))
      (MvPolynomial.aeval (fun ij : ι × ι => h ij.1 ij.2)) t = (0 : ℂ))
    (R : Type) [CommRing R] [Algebra ℚ R] (x : Matrix ι ι R) (hx : x ∈ pts Γ R)
    (y : Matrix ι ι R) (hy : y ∈ pts Γ R) :
    Algebra.TensorProduct.productMap
      (MvPolynomial.aeval (fun ij : ι × ι => x ij.1 ij.2))
      (MvPolynomial.aeval (fun ij : ι × ι => y ij.1 ij.2)) t = (0 : R) := by
  set ex : MvPolynomial (ι × ι) ℚ →ₐ[ℚ] R := MvPolynomial.aeval (fun ij : ι × ι => x ij.1 ij.2) with hex
  set ey : MvPolynomial (ι × ι) ℚ →ₐ[ℚ] R := MvPolynomial.aeval (fun ij : ι × ι => y ij.1 ij.2) with hey
  have key : TensorProduct.map ex.toLinearMap ey.toLinearMap t = 0 := by
    apply tensor_eq_zero_of_forall_contract
    intro m
    have h1 : TensorProduct.rid ℚ _ (LinearMap.lTensor _ (m ∘ₗ ey.toLinearMap) t) ∈ vanI Γ := by
      intro g hg
      set eg : MvPolynomial (ι × ι) ℚ →ₐ[ℚ] ℂ := MvPolynomial.aeval (fun ij : ι × ι => g ij.1 ij.2) with heg
      refine (Module.forall_dual_apply_eq_zero_iff ℚ _).1 fun l => ?_
      let φ : MvPolynomial (ι × ι) ℚ ⊗[ℚ] MvPolynomial (ι × ι) ℚ →ₐ[ℚ] MvPolynomial (ι × ι) ℂ :=
        Algebra.TensorProduct.productMap
          (((Algebra.ofId ℂ (MvPolynomial (ι × ι) ℂ)).restrictScalars ℚ).comp eg)
          (MvPolynomial.mapAlgHom (Algebra.ofId ℚ ℂ))
      have h2 : TensorProduct.lid ℚ _ (LinearMap.rTensor _ (l ∘ₗ eg.toLinearMap) t) ∈ vanI Γ := by
        refine GlobalTheory.T.rat_component_mem_ratPolysVanishingOnMatrixSet ι Γ hΓ (φ t) ?_ l _ ?_
        · intro h hh
          rw [← ht g hg h hh]
          clear ht
          induction t using TensorProduct.induction_on with
          | zero => simp [evC]
          | tmul a b =>
            simp [evC, φ, ← heg, MvPolynomial.eval_map, MvPolynomial.aeval_def, Algebra.ofId_apply]
          | add s t hs ht =>
            simp only [evC] at hs ht
            simp only [evC, map_add (f := _), hs, ht]
        · intro k
          clear ht
          induction t using TensorProduct.induction_on with
          | zero => simp
          | tmul a b =>
            simp [φ, MvPolynomial.coeff_map, Algebra.ofId_apply]
            rw [mul_comm (eg a), ← eq_ratCast (algebraMap ℚ ℂ), ← Algebra.smul_def, map_smul, smul_eq_mul, mul_comm]
          | add s t hs ht => simp only [map_add (f := _), MvPolynomial.coeff_add, hs, ht]
      have h3 : ey _ = 0 := hy _ h2
      have h4 := congrArg m h3
      rw [map_zero] at h4
      rw [← h4]
      change l (eg _) = _
      clear ht h2 h3 h4
      induction t using TensorProduct.induction_on with
      | zero => simp
      | tmul a b => simp [mul_comm]
      | add s t hs ht => simp only [map_add (f := _), hs, ht]
    have h5 : ex _ = 0 := hx _ h1
    rw [← h5]
    clear ht h1 h5
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp
    | add s t hs ht => simp only [map_add (f := _), hs, ht]
  have h6 := congrArg (LinearMap.mul' ℚ R) key
  rw [map_zero] at h6
  rw [← h6]
  clear ht key h6
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp
  | add s t hs ht => simp only [map_add (f := _), hs, ht]

theorem aeval_sum_elim_eq_zero_of_mem_pts : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ)), (∀ σ : ℂ ≃+* ℂ, ∀ g ∈ Γ, g.map σ ∈ Γ) → ∀ F : MvPolynomial ((ι × ι) ⊕ (ι × ι)) ℚ, (∀ g ∈ Γ, ∀ h ∈ Γ, MvPolynomial.aeval (Sum.elim (fun ij : ι × ι => g ij.1 ij.2) (fun ij : ι × ι => h ij.1 ij.2)) F = (0 : ℂ)) → ∀ (R : Type) [CommRing R] [Algebra ℚ R], ∀ x ∈ pts Γ R, ∀ y ∈ pts Γ R, MvPolynomial.aeval (Sum.elim (fun ij : ι × ι => x ij.1 ij.2) (fun ij : ι × ι => y ij.1 ij.2)) F = (0 : R) := by
  intro ι _ _ Γ hΓ F hF R _ _ x hx y hy
  let T : MvPolynomial ((ι × ι) ⊕ (ι × ι)) ℚ →ₐ[ℚ]
      MvPolynomial (ι × ι) ℚ ⊗[ℚ] MvPolynomial (ι × ι) ℚ :=
    MvPolynomial.aeval (Sum.elim (fun ij => MvPolynomial.X ij ⊗ₜ 1) (fun ij => 1 ⊗ₜ MvPolynomial.X ij))
  have hT : ∀ (S : Type) [CommRing S] [Algebra ℚ S] (a b : ι × ι → S),
      Algebra.TensorProduct.productMap (MvPolynomial.aeval a) (MvPolynomial.aeval b) (T F) =
        MvPolynomial.aeval (Sum.elim a b) F := by
    intro S _ _ a b
    have : (Algebra.TensorProduct.productMap (MvPolynomial.aeval a) (MvPolynomial.aeval b)).comp T =
        MvPolynomial.aeval (Sum.elim a b) := by
      ext (i | i) <;> simp [T]
    exact DFunLike.congr_fun this F
  rw [← hT]
  refine aeval_sum_elim_eq_zero_of_tensor Γ hΓ _ (fun g hg h hh => ?_) R x hx y hy
  rw [hT]
  exact hF g hg h hh

end GlobalTheory.ClassFin
end

section

open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

namespace GlobalTheory.CNorm

theorem mem_kNorm_iff_map_mem_id (p : ℕ) {F L : Type} [Field F] [Field L] (φ : F →+* L) (δ : F)
    (x : Fˣ) :
    x ∈ kNorm p φ δ ↔ Units.map (φ : F →* L) x ∈ kNorm p (RingHom.id L) (φ δ) := by
  rw [mem_kNorm, mem_kNorm]
  exact Iff.rfl

theorem pow_tNon_le_index_finNorm :
    ∀ (p : ℕ) (F : Type) [Field F] [NumberField F] [_root_.NumberField.IsTotallyComplex F] (ζ δ : F)
      (S : Finset (HeightOneSpectrum (𝓞 F))), p.Prime → IsPrimitiveRoot ζ p →
      (finNorm p F δ S).index ≠ 0 ∧ p ^ tNon p F δ S ≤ (finNorm p F δ S).index := by
  intro p F _ _ _ ζ δ S hp hζ
  classical
  have hpow := (GlobalTheory.T.unitsMappingToPowers_le_unitsLocalKummerNorms p hp.pos).1
  have hPN : finPow p F S ≤ finNorm p F δ S := by
    unfold finPow finNorm
    exact iInf_mono fun v => iInf_mono fun _ => hpow _ _ _ _
  have h0 : (finNorm p F δ S).index ≠ 0 :=
    ne_zero_of_dvd_ne_zero (GlobalTheory.T.unitsLocalPowersAtPlaces_index_le p F S hp.pos).1 (Subgroup.index_dvd_of_le hPN)
  refine ⟨h0, ?_⟩
  set A : Set (HeightOneSpectrum (𝓞 F)) :=
    {v | v ∈ S ∧ ∀ r : v.adicCompletion F, r ^ p ≠ algebraMap F (v.adicCompletion F) δ} with hA
  have hAf : A.Finite := S.finite_toSet.subset fun v hv => hv.1
  letI : Fintype A := hAf.fintype
  let K : A → Subgroup Fˣ := fun v => kNorm p (algebraMap F (v.1.adicCompletion F)) δ
  have hle : finNorm p F δ S ≤ ⨅ i, K i := le_iInf fun v => iInf₂_le v.1 v.2.1
  have hdvd := Subgroup.index_dvd_of_le hle
  have hcard : Fintype.card A = tNon p F δ S := by
    rw [← Nat.card_eq_fintype_card]
    rfl
  rw [← hcard]
  refine le_trans (GlobalTheory.T.pow_card_le_index_iInf_of_prime' p Fˣ A K hp ?_ ?_ (ne_zero_of_dvd_ne_zero h0 hdvd))
    (Nat.le_of_dvd (Nat.pos_of_ne_zero h0) hdvd)
  · intro v x
    exact hpow _ _ _ _ ⟨algebraMap F _ (x : F), by simp⟩
  · intro v
    obtain ⟨c, hc⟩ := GlobalTheory.T.exists_unit_not_localKummerNorm_of_not_pow p F ζ δ v.1 hp hζ v.2.2
    obtain ⟨x, hx0, hxv⟩ := GlobalTheory.T.exists_approx_mod_powers' p F S
      (Function.update (fun w : HeightOneSpectrum (𝓞 F) => (1 : w.adicCompletion F)) v.1
        (c : v.1.adicCompletion F)) hp.pos (by
        intro w
        by_cases hw : w = v.1
        · subst hw; simp
        · simp [Function.update_of_ne hw])
    refine ⟨Units.mk0 x hx0, ?_, ?_⟩
    · intro hm
      obtain ⟨r, hr⟩ := hxv v.1 v.2.1
      rw [Function.update_self] at hr
      have hr0 : r ≠ 0 := by
        rintro rfl
        rw [zero_pow hp.ne_zero, mul_zero] at hr
        exact hx0 (by simpa using hr)
      have hm' := (mem_kNorm_iff_map_mem_id p _ δ _).1 hm
      have hrm : (Units.mk0 r hr0) ^ p ∈ kNorm p (RingHom.id (v.1.adicCompletion F))
          (algebraMap F (v.1.adicCompletion F) δ) := hpow _ _ _ _ ⟨r, by simp⟩
      apply hc
      have hq := Subgroup.div_mem _ hm' hrm
      convert hq using 1
      rw [eq_div_iff_mul_eq']
      apply Units.ext
      simpa using hr.symm
    · intro w hj
      have hw : w.1 ≠ v.1 := fun h => hj (Subtype.ext h)
      obtain ⟨r, hr⟩ := hxv w.1 w.2.1
      rw [Function.update_of_ne hw, one_mul] at hr
      exact hpow _ _ _ _ ⟨r, hr.symm⟩

end GlobalTheory.CNorm
end

section

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

theorem _root_.GlobalTheory.T.isSemisimpleRepresentation_tprod_chevalley : ∀ (G : Type) [Group G] (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (W : Type) [AddCommGroup W] [Module ℂ W] (ρ' : Representation ℂ G W) [FiniteDimensional ℂ V] [FiniteDimensional ℂ W], ρ.IsSemisimpleRepresentation → ρ'.IsSemisimpleRepresentation → (ρ.tprod ρ').IsSemisimpleRepresentation := by
  first | exact @GlobalTheory.ClassFin.isSemisimpleRepresentation_tprod | exact GlobalTheory.ClassFin.isSemisimpleRepresentation_tprod | (intros; apply GlobalTheory.ClassFin.isSemisimpleRepresentation_tprod <;> assumption)
end

section

open NumberField IsDedekindDomain NumberField.mixedEmbedding MeasureTheory Complex Classical
open scoped ContDiff nonZeroDivisors Topology

namespace GlobalTheory.IdeleCharLevel

variable (K : Type) [Field K] [NumberField K]

theorem exists_level (U : Set (FiniteAdeleRing (𝓞 K) K)) (hU : U ∈ 𝓝 (0 : FiniteAdeleRing (𝓞 K) K)) :
    ∃ M : ℕ, M ≠ 0 ∧ ∀ a : FiniteAdeleRing (𝓞 K) K,
      (∀ P : HeightOneSpectrum (𝓞 K), Valued.v (a P) ≤ P.intValuation (M : 𝓞 K)) → a ∈ U := by
  obtain ⟨M, hM, h⟩ := GlobalTheory.AdLat.OpenLat.exists_nsmul_adele K U hU
  refine ⟨M, hM.ne', fun a ha => ?_⟩
  have hM0 : (M : K) ≠ 0 := Nat.cast_ne_zero.mpr hM.ne'
  have hM1 : (M : 𝓞 K) ≠ 0 := Nat.cast_ne_zero.mpr hM.ne'
  have := h (algebraMap K (FiniteAdeleRing (𝓞 K) K) (M : K)⁻¹ * a) fun P => by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers]
    change Valued.v ((algebraMap K (FiniteAdeleRing (𝓞 K) K) (M : K)⁻¹) P * a P) ≤ 1
    rw [map_mul, FiniteAdeleRing.algebraMap_apply,
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation', map_inv₀,
      ← map_natCast (algebraMap (𝓞 K) K), HeightOneSpectrum.valuation_of_algebraMap]
    have h0 : P.intValuation (M : 𝓞 K) ≠ 0 := P.intValuation_ne_zero _ hM1
    rw [inv_mul_le_iff₀ (zero_lt_iff.mpr h0), mul_one]
    exact ha P
  rwa [nsmul_eq_mul, ← mul_assoc, ← map_natCast (algebraMap K (FiniteAdeleRing (𝓞 K) K)) M,
    ← map_mul, mul_inv_cancel₀ hM0, map_one, one_mul] at this

end GlobalTheory.IdeleCharLevel
end

section

open NumberField IsDedekindDomain NumberField.mixedEmbedding Complex Classical
open scoped TensorProduct ContDiff nonZeroDivisors
open scoped Topology

namespace GlobalTheory.AdeleBaseChange

theorem continuous_symm_finite : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (ι : FiniteAdeleRing (𝓞 F) F ⊗[F] E ≃+* FiniteAdeleRing (𝓞 E) E), (∀ y, y ∈ AddSubgroup.closure {y : FiniteAdeleRing (𝓞 F) F ⊗[F] E | ∃ a ∈ {a : FiniteAdeleRing (𝓞 F) F | ∀ v : HeightOneSpectrum (𝓞 F), a v ∈ v.adicCompletionIntegers F}, ∃ x : 𝓞 E, y = a ⊗ₜ[F] (x : E)} ↔ ∀ P, Valued.v (ι y P) ≤ 1) → letI : TopologicalSpace (FiniteAdeleRing (𝓞 F) F ⊗[F] E) := moduleTopology (FiniteAdeleRing (𝓞 F) F) (FiniteAdeleRing (𝓞 F) F ⊗[F] E); Continuous ι.symm := by
  intro F E _ _ _ _ _ ι hι
  letI : TopologicalSpace (FiniteAdeleRing (𝓞 F) F ⊗[F] E) :=
    moduleTopology (FiniteAdeleRing (𝓞 F) F) (FiniteAdeleRing (𝓞 F) F ⊗[F] E)
  haveI : IsModuleTopology (FiniteAdeleRing (𝓞 F) F) (FiniteAdeleRing (𝓞 F) F ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalAddGroup (FiniteAdeleRing (𝓞 F) F ⊗[F] E) :=
    IsModuleTopology.topologicalAddGroup (FiniteAdeleRing (𝓞 F) F) _
  have h0 := (GlobalTheory.AdLat.OpenLat.isOpen_nsmul_hat F E 0 ⊤ (Subsingleton.elim _ _)).2
  refine continuous_of_continuousAt_zero ι.symm.toAddMonoidHom ?_
  rw [ContinuousAt, map_zero]
  intro W hW
  obtain ⟨N, hN, hNW⟩ := h0 W hW
  rw [Filter.mem_map]
  refine Filter.mem_of_superset (GlobalTheory.AdLat.OpenLat.nsmul_integral_mem_nhds E N hN) ?_
  rintro _ ⟨a, ha, rfl⟩
  rw [Set.mem_preimage, map_nsmul]
  apply hNW
  have h1 := (hι (ι.symm a)).2 (fun P => by rw [ι.apply_symm_apply]; exact ha P)
  refine AddSubgroup.closure_mono ?_ h1
  rintro _ ⟨b, hb, x, rfl⟩
  exact ⟨b, hb, _, ⟨x, rfl⟩, rfl⟩

end GlobalTheory.AdeleBaseChange
end
