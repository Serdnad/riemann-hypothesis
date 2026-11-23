module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MemBallOfGaugeLt
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle029
public import Mathlib.Topology.MetricSpace.Ultra.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueJointTop
public import Formalism.LocalRingCardinality.DataHost
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle495
public import GroundTheory.GlobalFields.Adele.Bundle003
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle520
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle519
public import GroundTheory.GlobalFields.TateThesis.Bundle006
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnipotentBlockColumnIndex
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle523
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.InvertibleSpanSingleton
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsAdicCompleteOfPowLe
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Mathlib.RingTheory.Ideal.BigOperators
public import Mathlib.Analysis.Normed.Group.Ultra
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle022
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.LocalToGlobal.Divisibility.CoefMod
import Formalism.LocalToGlobal.IndefiniteForms.IndefSide
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Formalism.LocalToGlobal.IndefiniteReal.PartsOrth
import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.Bundle001
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsOpenKerFinIdele
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle036
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEqColGenMulBlkU
import Development.AutomorphicArithmetic.IntegralCasts.Bundle001

@[expose] public section

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem TopBasis.exists_of_pow_le_of_pow_le :
    ∀ (S A : Type) [CommRing S] [CommRing A] (s : S →+* A) (I : Ideal S) (ι : Type) (TB : TopBasis s I ι)
      (I' : Ideal S) (n m : ℕ), IsHausdorff I S → 0 < n → 0 < m → I ^ n ≤ I' → I' ^ m ≤ I →
      ∃ TB' : TopBasis s I' ι, TB'.b = TB.b ∧ TB'.c = TB.c := by
  intro S A _ _ s I ι TB I' n m _ _ _ h1 h2
  have hk : ∀ k : ℕ, I ^ (n * k) ≤ I' ^ k := fun k => by
    rw [pow_mul]; exact Ideal.pow_right_mono h1 k
  classical
  refine ⟨{ TB with fin := ?_, approx := ?_, complete := ?_ }, rfl, rfl⟩
  · intro x k
    exact (TB.fin x (n * k)).subset fun i hi h => hi (hk k h)
  · intro x k F hF
    set G : Finset ι := F ∪ (TB.fin x (n * k)).toFinset with hG
    have hG' : ∀ i, i ∉ G → TB.c i x ∈ I ^ (n * k) := by
      intro i hi
      by_contra h
      exact hi (Finset.mem_union_right _ ((Set.Finite.mem_toFinset _).2 h))
    have hmain := TB.approx x (n * k) G hG'
    have hmap : (I ^ (n * k)).map s ≤ (I' ^ k).map s := Ideal.map_mono (hk k)
    have hsplit : ∑ i ∈ G, s (TB.c i x) * TB.b i =
        ∑ i ∈ F, s (TB.c i x) * TB.b i + ∑ i ∈ G \ F, s (TB.c i x) * TB.b i := by
      rw [add_comm, Finset.sum_sdiff (Finset.subset_union_left)]
    have hrest : ∑ i ∈ G \ F, s (TB.c i x) * TB.b i ∈ (I' ^ k).map s := by
      refine Ideal.sum_mem _ fun i hi => ?_
      have : i ∉ F := (Finset.mem_sdiff.1 hi).2
      exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem s (hF i this))
    have : x - ∑ i ∈ F, s (TB.c i x) * TB.b i =
        (x - ∑ i ∈ G, s (TB.c i x) * TB.b i) + ∑ i ∈ G \ F, s (TB.c i x) * TB.b i := by
      rw [hsplit]; ring
    rw [this]
    exact add_mem (hmap hmain) hrest
  · refine GlobalTheory.isAdicComplete_of_pow_le_of_pow_le A (I.map s) (I'.map s) n m ?_ ?_ TB.complete
    · rw [← Ideal.map_pow]; exact Ideal.map_mono h1
    · rw [← Ideal.map_pow]; exact Ideal.map_mono h2

end GlobalTheory.BSP
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BSP.DiscBasic

variable (l : ℕ) [hl : Fact l.Prime] {A : Type} [CommRing A] (u : A) (ρ : ℝ≥0)

theorem norm_add_le_max_disc (x y : Disc l u ρ) : ‖x + y‖ ≤ max ‖x‖ ‖y‖ := by
  refine (denseRange_ofPre l u ρ).induction_on₂ (p := fun x y => ‖x + y‖ ≤ max ‖x‖ ‖y‖)
    (isClosed_le (by fun_prop) (by fun_prop)) (fun a b => ?_) x y
  rw [← map_add (f := _), norm_ofPre, norm_ofPre, norm_ofPre]
  exact gauge_add_le_max l u ρ a b

theorem isUltrametricDist_disc : IsUltrametricDist (Disc l u ρ) :=
  IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm (norm_add_le_max_disc l u ρ)

theorem norm_l_disc_le : ‖((l : ℕ) : Disc l u ρ)‖ ≤ 1 / l := by
  have hl0 : (0 : ℝ) < l := Nat.cast_pos.2 hl.out.pos
  rw [← map_natCast (ofPre l u ρ), norm_ofPre]
  refine gauge_le l u ρ (by positivity) (Submodule.subset_span ⟨1, 0, 0, ?_, ?_⟩)
  · field_simp; simp
  · simp

theorem norm_inv_disc_le : ‖ofPre l u ρ (IsLocalization.Away.invSelf (l : A))‖ ≤ l := by
  have hl0 : (0 : ℝ) < l := Nat.cast_pos.2 hl.out.pos
  rw [norm_ofPre]
  refine gauge_le l u ρ hl0 (Submodule.subset_span ⟨0, 0, 1, ?_, ?_⟩)
  · simp
  · simp

theorem inv_mul_l_disc : ofPre l u ρ (IsLocalization.Away.invSelf (l : A)) * ((l : ℕ) : Disc l u ρ) = 1 := by
  rw [← map_natCast (ofPre l u ρ), ← map_mul, ← map_one (ofPre l u ρ)]
  congr 1
  rw [mul_comm, ← map_natCast (algebraMap A (PreDisc l u ρ))]
  exact IsLocalization.Away.mul_invSelf _

theorem norm_l_mul (y : Disc l u ρ) : ‖((l : ℕ) : Disc l u ρ) * y‖ = ‖y‖ / l := by
  have hl0 : (0 : ℝ) < l := Nat.cast_pos.2 hl.out.pos
  apply le_antisymm
  · calc ‖((l : ℕ) : Disc l u ρ) * y‖ ≤ ‖((l : ℕ) : Disc l u ρ)‖ * ‖y‖ := norm_mul_le _ _
      _ ≤ 1 / l * ‖y‖ := mul_le_mul_of_nonneg_right (norm_l_disc_le l u ρ) (norm_nonneg _)
      _ = ‖y‖ / l := by ring
  · rw [div_le_iff₀ hl0]
    calc ‖y‖ = ‖ofPre l u ρ (IsLocalization.Away.invSelf (l : A)) * (((l : ℕ) : Disc l u ρ) * y)‖ := by
          rw [← mul_assoc, inv_mul_l_disc, one_mul]
      _ ≤ ‖ofPre l u ρ (IsLocalization.Away.invSelf (l : A))‖ * ‖((l : ℕ) : Disc l u ρ) * y‖ := norm_mul_le _ _
      _ ≤ l * ‖((l : ℕ) : Disc l u ρ) * y‖ :=
          mul_le_mul_of_nonneg_right (norm_inv_disc_le l u ρ) (norm_nonneg _)
      _ = _ := by ring

theorem addHom_ext (N : Type) [NormedAddCommGroup N] (hN : ∀ z : N, l • z = 0 → z = 0)
    (F G : Disc l u ρ →+ N) (hF : Continuous F) (hG : Continuous G)
    (h : ∀ a, F (toDisc l u ρ a) = G (toDisc l u ρ a)) : F = G := by
  have hN' : ∀ n : ℕ, ∀ z : N, (l ^ n) • z = 0 → z = 0 := by
    intro n
    induction n with
    | zero => intro z hz; simpa using hz
    | succ n ih => intro z hz; exact ih z (hN _ (by rw [← mul_smul, ← pow_succ']; exact hz))
  have hpre : ∀ y : PreDisc l u ρ, F (ofPre l u ρ y) = G (ofPre l u ρ y) := by
    intro y
    obtain ⟨n, a, hy⟩ := IsLocalization.Away.surj (l : A) y
    have e : ((l ^ n : ℕ) : Disc l u ρ) * ofPre l u ρ y = toDisc l u ρ a := by
      rw [toDisc, RingHom.comp_apply, ← hy, map_mul, mul_comm (ofPre l u ρ y), ← map_natCast (ofPre l u ρ),
        ← map_natCast (algebraMap A (PreDisc l u ρ)), Nat.cast_pow, map_pow, map_pow]
    refine sub_eq_zero.1 (hN' n _ ?_)
    rw [smul_sub, ← map_nsmul F, ← map_nsmul G, nsmul_eq_mul, e, h, sub_self]
  ext x
  exact (denseRange_ofPre l u ρ).induction_on x (isClosed_eq hF hG) hpre

theorem isDiscMap_comp {A' A'' : Type} [CommRing A'] [CommRing A''] {u' : A'} {u'' : A''} {ρ' ρ'' : ℝ≥0}
    {f : A →+* A'} {f' : A' →+* A''} {F : Disc l u ρ →+* Disc l u' ρ'} {F' : Disc l u' ρ' →+* Disc l u'' ρ''}
    (hF : IsDiscMap (l := _) (u := _) (ρ := _) f F) (hF' : IsDiscMap (l := _) (u := _) (ρ := _) f' F') : IsDiscMap (l := _) (u := _) (ρ := _) (f'.comp f) (F'.comp F) :=
  ⟨fun a => by rw [RingHom.comp_apply, hF.ext, hF'.ext, RingHom.comp_apply],
    fun x => (hF'.norm_le _).trans (hF.norm_le x)⟩

theorem disc_basic : ∀ (l : ℕ) [Fact l.Prime] (A : Type) [CommRing A] (u : A) (ρ : ℝ≥0), IsUltrametricDist (Disc l u ρ) ∧ (∀ y : Disc l u ρ, ‖((l : ℕ) : Disc l u ρ) * y‖ = ‖y‖ / l) ∧ (∀ (N : Type) [NormedAddCommGroup N], (∀ z : N, l • z = 0 → z = 0) → ∀ F G : Disc l u ρ →+ N, Continuous F → Continuous G → (∀ a, F (toDisc l u ρ a) = G (toDisc l u ρ a)) → F = G) ∧ ∀ (A' A'' : Type) [CommRing A'] [CommRing A''] (u' : A') (u'' : A'') (ρ' ρ'' : ℝ≥0) (f : A →+* A') (f' : A' →+* A'') (F : Disc l u ρ →+* Disc l u' ρ') (F' : Disc l u' ρ' →+* Disc l u'' ρ''), IsDiscMap (l := _) (u := _) (ρ := _) f F → IsDiscMap (l := _) (u := _) (ρ := _) f' F' → IsDiscMap (l := _) (u := _) (ρ := _) (f'.comp f) (F'.comp F) :=
  fun l _ A _ u ρ => ⟨isUltrametricDist_disc l u ρ, norm_l_mul l u ρ,
    fun N _ hN F G hF hG h => addHom_ext l u ρ N hN F G hF hG h,
    fun _ _ _ _ _ _ _ _ _ _ _ _ hF hF' => isDiscMap_comp l u ρ hF hF'⟩

end GlobalTheory.BSP.DiscBasic
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift

namespace GlobalTheory.Slice

open MvPolynomial GlobalTheory.Capelli

variable {σ σ₀ : Type} (ι : σ₀ → σ)

abbrev Outer := {v : σ // v ∉ Set.range ι}

noncomputable def sliceVar (v : σ) : MvPolynomial (Outer ι) (MvPolynomial σ₀ ℂ) := by
  classical
  exact if h : v ∈ Set.range ι then C (X h.choose) else X ⟨v, h⟩

noncomputable def slice : MvPolynomial σ ℂ →ₐ[ℂ] MvPolynomial (Outer ι) (MvPolynomial σ₀ ℂ) :=
  aeval (sliceVar ι)

variable {ι}

theorem slice_X_inner (hι : Function.Injective ι) (u : σ₀) : slice ι (X (ι u)) = C (X u) := by
  have h : ι u ∈ Set.range ι := ⟨u, rfl⟩
  simp only [slice, aeval_X, sliceVar, dite_eq_left h]
  rw [hι h.choose_spec]

theorem slice_X_outer {v : σ} (hv : v ∉ Set.range ι) : slice ι (X v) = X ⟨v, hv⟩ := by
  simp only [slice, aeval_X, sliceVar, dite_eq_right hv]

theorem slice_C (a : ℂ) : slice ι (C a) = C (C a) := by
  simp [slice, MvPolynomial.algebraMap_apply]

variable (ι)

noncomputable def coefAt (t : Outer ι →₀ ℕ) : MvPolynomial σ ℂ →ₗ[ℂ] MvPolynomial σ₀ ℂ where
  toFun Q := AddMonoidAlgebra.coeff (slice ι Q) t
  map_add' _ _ := by simp
  map_smul' c Q := by simp

variable {ι}

theorem coefAt_X_mul (hι : Function.Injective ι) (t : Outer ι →₀ ℕ) (u : σ₀)
    (Q : MvPolynomial σ ℂ) : coefAt ι t (X (ι u) * Q) = X u * coefAt ι t Q := by
  simp [coefAt, map_mul, slice_X_inner hι, coeff_C_mul]

theorem coefAt_pderiv (hι : Function.Injective ι) (u : σ₀) (Q : MvPolynomial σ ℂ) :
    ∀ t, coefAt ι t (pderiv (ι u) Q) = pderiv u (coefAt ι t Q) := by
  classical
  simp only [coefAt, LinearMap.coe_mk, AddHom.coe_mk]
  induction Q using MvPolynomial.induction_on with
  | C a => intro t; simp only [pderiv_C, map_zero, AddMonoidAlgebra.coeff_zero, slice_C, coeff_C]; split_ifs <;> simp
  | add p q hp hq => intro t; simp [hp, hq]
  | mul_X p v hp =>
    intro t
    by_cases hv : v ∈ Set.range ι
    · obtain ⟨w, rfl⟩ := hv
      by_cases huw : w = u
      · subst huw
        simp [Derivation.leibniz, map_mul, slice_X_inner hι, hp, pderiv_X, coeff_C_mul,
          mul_comm (slice ι p) (C (X w))]
        ring
      · have h1 : ι u ≠ ι w := fun h => huw (hι h).symm
        have h2 : u ≠ w := fun h => huw h.symm
        simp [Derivation.leibniz, map_mul, slice_X_inner hι, hp, pderiv_X,
          h1, h2, coeff_C_mul, mul_comm (slice ι p) (C (X w))]
    · have h1 : ι u ≠ v := fun h => hv ⟨u, h⟩
      simp only [Derivation.leibniz, map_mul, smul_eq_mul, pderiv_X, Pi.single_apply,
        ite_eq_right h1.symm, mul_zero, zero_add, slice_X_outer hv]
      rw [coeff_X_mul', coeff_mul_X']
      split_ifs
      · rw [hp]
      · simp

theorem coefAt_jointTop (hι : Function.Injective ι) (t : Outer ι →₀ ℕ) {k l N : ℕ}
    (z : Fin k × Fin N → σ₀) (y : Fin l × Fin N → σ₀) (κ : Fin N → ℂ) (α : Fin k → ℂ)
    (β : Fin l → ℂ) (P : MvPolynomial σ ℂ)
    (h : GlobalTheory.CompactHarm.JointTop (ι ∘ z) (ι ∘ y) κ α β P) :
    GlobalTheory.CompactHarm.JointTop z y κ α β (coefAt ι t P) := by
  have hm : ∀ i j, coefAt ι t (mixedOp ℂ (ι ∘ z) (ι ∘ y) i j P) =
      mixedOp ℂ z y i j (coefAt ι t P) := fun i j => by

    simp only [mixedOp_apply, map_sub, map_sum, Function.comp_apply, coefAt_X_mul hι,
    coefAt_pderiv hι]
  have hr : ∀ {K : ℕ} (w : Fin K × Fin N → σ₀) (a b : Fin K),
      coefAt ι t (rowOp ℂ (ι ∘ w) a b P) = rowOp ℂ w a b (coefAt ι t P) := fun w a b => by

    simp only [rowOp_apply, map_sum, Function.comp_apply, coefAt_X_mul hι, coefAt_pderiv hι]
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  refine ⟨fun i j hij => ?_, fun i => ?_, fun c c' hc => ?_, fun c => ?_, fun d d' hd => ?_,
    fun d => ?_, fun c d => ?_⟩
  · rw [← hm, h1 i j hij, map_zero]
  · rw [← hm, h2 i, map_smul]
  · rw [← hr, h3 c c' hc, map_zero]
  · rw [← hr, h4 c, map_smul]
  · rw [← hr, h5 d d' hd, map_zero]
  · rw [← hr, h6 d, map_smul]
  · have := congrArg (coefAt ι t) (h7 c d)

    simpa only [map_sum, Function.comp_apply, coefAt_pderiv hι, map_zero] using this

variable (ι)

noncomputable def unslice : MvPolynomial (Outer ι) (MvPolynomial σ₀ ℂ) →+* MvPolynomial σ ℂ :=
  eval₂Hom (rename ι).toRingHom (fun r => X r.1)

variable {ι}

theorem unslice_slice_X (hι : Function.Injective ι) (v : σ) : unslice ι (slice ι (X v)) = X v := by
  by_cases hv : v ∈ Set.range ι
  · obtain ⟨w, rfl⟩ := hv
    rw [slice_X_inner hι]
    simp only [unslice, coe_eval₂Hom, eval₂_C, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, rename_X]
  · rw [slice_X_outer hv]
    simp only [unslice, coe_eval₂Hom, eval₂_X]

theorem unslice_slice (hι : Function.Injective ι) (Q : MvPolynomial σ ℂ) :
    unslice ι (slice ι Q) = Q := by
  induction Q using MvPolynomial.induction_on with
  | C a =>
    rw [slice_C]
    simp only [unslice, coe_eval₂Hom, eval₂_C, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, rename_C]
  | add p q hp hq => rw [map_add (f := _), map_add (f := _), hp, hq]
  | mul_X p v hp =>
    rw [map_mul, map_mul, hp, unslice_slice_X hι]

theorem slice_decomp (hι : Function.Injective ι) (P : MvPolynomial σ ℂ) :
    P = ∑ t ∈ (slice ι P).support,
      rename ι (coefAt ι t P) * t.prod (fun r e => (X r.1 : MvPolynomial σ ℂ) ^ e) := by

  conv_lhs => rw [← unslice_slice hι P, (slice ι P).as_sum, map_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  simp [unslice, eval₂_monomial, coefAt]

theorem vars_outer_prod (t : Outer ι →₀ ℕ) :
    ∀ v ∈ (t.prod (fun r e => (X r.1 : MvPolynomial σ ℂ) ^ e)).vars, v ∉ Set.range ι := by
  classical
  intro v hv
  obtain ⟨r, -, hr⟩ := Finset.mem_biUnion.1 (vars_prod _ hv)
  have := vars_pow _ _ hr
  rw [vars_X, Finset.mem_singleton] at this
  exact this ▸ r.2

noncomputable def outerEmb : (Outer ι →₀ ℕ) ↪ (σ →₀ ℕ) :=
  ⟨Finsupp.mapDomain Subtype.val, Finsupp.mapDomain_injective Subtype.val_injective⟩

noncomputable def outerBack (i : σ →₀ ℕ) : Outer ι →₀ ℕ :=
  Finsupp.comapDomain Subtype.val i Subtype.val_injective.injOn

theorem outerBack_emb (t : Outer ι →₀ ℕ) : outerBack (outerEmb t) = t :=
  Finsupp.comapDomain_mapDomain _ Subtype.val_injective t

end GlobalTheory.Slice

open GlobalTheory.Slice in
theorem GlobalTheory.jointTop_slice : ∀ {σ σ₀ : Type} [DecidableEq σ] (ι : σ₀ → σ), Function.Injective ι →
    ∀ {k l N : ℕ} (z : Fin k × Fin N → σ₀) (y : Fin l × Fin N → σ₀) (κ : Fin N → ℂ)
    (α : Fin k → ℂ) (β : Fin l → ℂ) (P : MvPolynomial σ ℂ),
    GlobalTheory.CompactHarm.JointTop (ι ∘ z) (ι ∘ y) κ α β P →
    ∃ (s : Finset (σ →₀ ℕ)) (f : (σ →₀ ℕ) → MvPolynomial σ₀ ℂ) (g : (σ →₀ ℕ) → MvPolynomial σ ℂ),
      P = ∑ i ∈ s, MvPolynomial.rename ι (f i) * g i ∧
      (∀ i ∈ s, GlobalTheory.CompactHarm.JointTop z y κ α β (f i)) ∧
      ∀ i ∈ s, ∀ v ∈ (g i).vars, v ∉ Set.range ι := by
  intro σ σ₀ _ ι hι k l N z y κ α β P hP
  refine ⟨(slice ι P).support.map (outerEmb (ι := ι)), fun i => coefAt ι (outerBack (ι := ι) i) P,
    fun i => (outerBack (ι := ι) i).prod (fun r n => (MvPolynomial.X r.1 : MvPolynomial σ ℂ) ^ n), ?_, ?_, ?_⟩
  · rw [Finset.sum_map]
    simp only [outerBack_emb]
    exact slice_decomp hι P
  · intro i _
    exact coefAt_jointTop hι _ z y κ α β P hP
  · intro i _
    exact vars_outer_prod _
end

section

open NumberField IsDedekindDomain Matrix Formalism.UG GlobalTheory.CuspRep MeasureTheory
open scoped ENNReal

noncomputable section

namespace GlobalTheory.CellDec

def unipFund (E : Type) [Field E] [NumberField E] (n : ℕ) : Set (NA E n) :=
  {u | ∀ i j : Fin n, i < j → ((u : GA E n) : Matrix (Fin n) (Fin n) (Ad E)) i j ∈ GroundTheory.Global.fundamentalSet E}

variable {E : Type} [Field E] [NumberField E] {n : ℕ}

theorem ratGL_mem_NA {γ : GL (Fin n) E} (hγ : γ ∈ GlobalTheory.SmGL.unipB E (Fin n)) : ratGL E n γ ∈ NA E n := by
  obtain ⟨h1, h2⟩ := (GlobalTheory.SmGL.mem_unipB E).1 hγ
  refine (GlobalTheory.SmGL.mem_unipB (Ad E)).2 ⟨fun i j hij => ?_, fun i => ?_⟩
  · simp [ratGL, h1 i j hij]
  · simp [ratGL, h2 i]

theorem exists_fundamentalDomain_NE (E : Type) [Field E] [NumberField E] (n : ℕ) [MeasurableSpace (GA E n)]
    [BorelSpace (GA E n)] (ν : Measure (NA E n)) [ν.IsHaarMeasure] : ∃ D : Set (NA E n),
    IsFundamentalDomain ((NE E n).subgroupOf (NA E n)) D ν ∧ 0 < ν D ∧ ν D < ⊤ := by
  classical
  have hfd : IsFundamentalDomain ((NE E n).subgroupOf (NA E n)) (unipFund E n) ν := by
    refine IsFundamentalDomain.mk' ?_ ?_
    · refine MeasurableSet.nullMeasurableSet ?_
      have : unipFund E n = ⋂ i : Fin n, ⋂ j : Fin n, ⋂ (_ : i < j),
          (fun u : NA E n => ((u : GA E n) : Matrix (Fin n) (Fin n) (Ad E)) i j) ⁻¹'
            GroundTheory.Global.fundamentalSet E := by
        ext u; simp [unipFund]
      rw [this]
      refine MeasurableSet.iInter fun i => MeasurableSet.iInter fun j => MeasurableSet.iInter fun _ => ?_
      refine (Continuous.measurable ?_) (GroundTheory.Global.measurableSet_fundamentalSet E)
      exact (Units.continuous_val.comp continuous_subtype_val).matrix_elem i j
    · intro x
      obtain ⟨γ, ⟨hγ, hγD⟩, huniq⟩ := GlobalTheory.T.existsUnique_ratUnitriangular_mul_entries_mem_fundamentalSet E n (x : GA E n) x.2
      refine ⟨⟨⟨ratGL E n γ, ratGL_mem_NA hγ⟩, Subgroup.mem_subgroupOf.2 (Subgroup.mem_map.2 ⟨γ, hγ, rfl⟩)⟩,
        fun i j hij => hγD i j hij, ?_⟩
      intro g hg
      obtain ⟨γ', hγ', hγ'g⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 g.2)
      have he : γ' = γ := huniq γ' ⟨hγ', fun i j hij => by
        have := hg i j hij
        rw [hγ'g]; exact this⟩
      apply Subtype.ext; apply Subtype.ext
      change ((g : NA E n) : GA E n) = ratGL E n γ
      rw [← hγ'g, he]
  have hE : Countable E := (Module.finBasis ℚ E).equivFun.injective.countable
  have hG : Countable ((NE E n).subgroupOf (NA E n)) := by
    have h : ∀ g : (NE E n).subgroupOf (NA E n), ∃ γ : GL (Fin n) E, ratGL E n γ = ((g : NA E n) : GA E n) :=
      fun g => by
        obtain ⟨γ, -, hγ⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 g.2)
        exact ⟨γ, hγ⟩
    choose f hf using h
    have : Countable (Matrix (Fin n) (Fin n) E) := inferInstanceAs (Countable (Fin n → Fin n → E))
    have : Countable (GL (Fin n) E) :=
      Function.Injective.countable (f := fun g : GL (Fin n) E => (g : Matrix (Fin n) (Fin n) E))
        fun a b h => Units.ext h
    exact Function.Injective.countable (f := f) fun a b hab =>
      Subtype.ext (Subtype.ext (by rw [← hf a, ← hf b, hab]))
  have hinv : SMulInvariantMeasure ((NE E n).subgroupOf (NA E n)) (NA E n) ν :=
    ⟨fun g s _ => by
      have : (fun x : NA E n => g • x) = fun x => (g : NA E n) * x := rfl
      show ν ((fun x => g • x) ⁻¹' s) = ν s
      rw [this]; exact measure_preimage_mul ν (g : NA E n) s⟩
  refine ⟨unipFund E n, hfd, pos_iff_ne_zero.2 (hfd.measure_ne_zero (NeZero.ne ν)), ?_⟩
  set C : Set (Ad E) := closure (GroundTheory.Global.fundamentalSetInfinite E) ×ˢ
    (GroundTheory.Global.integralFiniteAdeles (𝓞 E) E : Set (FiniteAdeleRing (𝓞 E) E)) with hCdef
  have hC : IsCompact C := (GroundTheory.Global.isCompact_closure_fundamentalSetInfinite E).prod
    (GroundTheory.Global.isCompact_integralFiniteAdeles E)
  set K : Set (GA E n) := {g : GA E n | g ∈ NA E n ∧ ∀ i j : Fin n, i < j →
    (g : Matrix (Fin n) (Fin n) (Ad E)) i j ∈ C} with hKdef
  have hK : IsCompact ((Subtype.val : NA E n → GA E n) ⁻¹' K) := by
    rw [Subtype.isCompact_iff, Set.image_preimage_eq_inter_range, Subtype.range_coe_subtype]
    change IsCompact (K ∩ (NA E n : Set (GA E n)))
    rw [Set.inter_eq_left.2 (fun g (hg : g ∈ K) => hg.1)]
    exact GlobalTheory.T.isCompact_adelicUnitriangular_entries_mem_compact E n C hC
  refine (measure_mono fun u hu => ?_).trans_lt hK.measure_lt_top
  refine ⟨u.2, fun i j hij => ?_⟩
  have h := hu i j hij
  exact ⟨subset_closure h.1, h.2⟩

end GlobalTheory.CellDec
end
end

section

open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW Formalism.UG GlobalTheory.LFun Formalism.L2.Host
open scoped ENNReal ComplexConjugate ContDiff
open GlobalTheory.MirTower GlobalTheory.CuspGeneric
open GroundTheory.Automorphic.FourierWhittaker (partialCoeff blockGL uGL)

theorem _root_.GlobalTheory.T.isMirabolicWhittakerStage_mul_invariant_continuous : ∀ (E : Type) [Field E] [NumberField E] (a m : ℕ) (ψ : AddChar (Ad E) ℂ) (f c : GA E a → ℂ),
    Good ψ m f → Continuous c → (∀ γ : GL (Fin a) E, IsMir m γ → ∀ g, c (ratGL E a γ * g) = c g) →
    (∀ (r l : ℕ) (y : UnipotentBlockColumnIndex a r l → Ad E) (g : GA E a), c (blkU y * g) = c g) → Good ψ m (fun g => c g * f g) := by
  first | (exact @GlobalTheory.GoodMul.good_mul_invariant) | (exact GlobalTheory.GoodMul.good_mul_invariant) | (intros; apply GlobalTheory.GoodMul.good_mul_invariant  <;> assumption)
end
