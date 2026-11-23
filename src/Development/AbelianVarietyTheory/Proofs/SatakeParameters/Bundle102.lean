module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MonodromyZeroOfWeilDeligneRepClassIff
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle037
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle005
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle088
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle009
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle080
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle069
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle070
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle089
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle096
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Edge1
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.TcoMem
public import Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.ExistsChartLiftOfFiniteCover
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle025
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsCuspidalIffCompositions
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TameIwahoriVectorTwoBlockProductPermValueFirst
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasExponentZeroIff
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.TrivialOnInertiaOfUnr
import Development.AutomorphicArithmetic.IntegralCasts.Bundle001
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle008

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory

theorem WeilDeligne.WD.lpTw_one_ne {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    [IsAlgClosure E Ω] {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
    (x : WD h) : 0 < x.lpDim → x.lpTw 1 ≠ x := by
  obtain ⟨n, a, rfl⟩ := WD.exists_rep x
  intro hn heq
  rw [WD.lpTw_mk, WD.mk_eq_mk] at heq
  obtain ⟨e, he, -⟩ := heq
  rw [WD.lpDim_mk, Module.finrank_fin_fun] at hn
  set σ := frob h
  set T := (a.tw 1).ρ σ
  set B := a.ρ σ
  have hconj : (e : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)) ∘ₗ T ∘ₗ (e.symm : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)) = B := by
    refine LinearMap.ext fun v => ?_
    show e ((a.tw 1).ρ σ (e.symm v)) = a.ρ σ v
    rw [he, LinearEquiv.apply_symm_apply]
  have hdet : LinearMap.det T = LinearMap.det B := by
    rw [← hconj, LinearMap.det_conj]
  have hT : T = ((normV w : ℕ) : ℂ) • B := by
    show (a.tw 1).ρ σ = _
    rw [WDRep.tw_ρ, deg_frob]
    simp only [Complex.ofReal_one, Complex.cpow_one, zpow_one]
    rfl
  rw [hT, LinearMap.det_smul, Module.finrank_fin_fun] at hdet
  have hB : LinearMap.det B ≠ 0 := by
    intro h0
    have h1 : B * a.ρ σ⁻¹ = 1 := by
      show a.ρ σ * a.ρ σ⁻¹ = 1
      rw [← map_mul, mul_inv_cancel, map_one]
    have := congrArg LinearMap.det h1
    rw [map_mul, h0, zero_mul, map_one] at this
    exact zero_ne_one this
  have hq : ((normV w : ℕ) : ℂ) ^ n = 1 := by
    have := mul_right_cancel₀ hB (hdet.trans (one_mul _).symm)
    exact this
  have hq' : (normV w : ℕ) ^ n = 1 := by exact_mod_cast hq
  have h1q := one_lt_normV w
  have : 1 < (normV w : ℕ) ^ n := Nat.one_lt_pow hn.ne' h1q
  omega

end GlobalTheory
end
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

open Polynomial TensorProduct Module

namespace GlobalTheory.WeilDeligne

section VecShift

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

def vecShift (n : ℕ) : End ℂ (Fin n → V) where
  toFun v i := if 1 ≤ (i : ℕ) then v ⟨i - 1, by omega⟩ else 0
  map_add' v v' := by ext i; by_cases hi : 1 ≤ (i : ℕ) <;> simp [hi]
  map_smul' a v := by ext i; by_cases hi : 1 ≤ (i : ℕ) <;> simp [hi]

theorem vecShift_apply {n : ℕ} (v : Fin n → V) (i : Fin n) :
    vecShift n v i = if 1 ≤ (i : ℕ) then v ⟨i - 1, by omega⟩ else 0 := rfl

theorem vecShift_pow_apply {n : ℕ} (k : ℕ) (v : Fin n → V) (i : Fin n) :
    (vecShift n ^ k) v i = if k ≤ (i : ℕ) then v ⟨i - k, by omega⟩ else 0 := by
  induction k generalizing i with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', End.mul_apply, vecShift_apply]
    by_cases h1 : 1 ≤ (i : ℕ)
    · rw [if_pos h1, ih]
      by_cases h2 : k + 1 ≤ (i : ℕ)
      · rw [if_pos h2, if_pos (by simp only; omega)]
        congr 2
        simp only; omega
      · rw [if_neg h2, if_neg (by simp only; omega)]
    · rw [if_neg h1, if_neg (by omega)]

def scaledDiag {n : ℕ} (f : End ℂ V) (c : Fin n → ℂ) : End ℂ (Fin n → V) where
  toFun v i := c i • f (v i)
  map_add' v v' := by ext i; simp [smul_add]
  map_smul' a v := by ext i; simp [smul_comm (c i) a]

theorem scaledDiag_apply {n : ℕ} (f : End ℂ V) (c : Fin n → ℂ) (v : Fin n → V) (i : Fin n) :
    scaledDiag f c v i = c i • f (v i) := rfl

theorem mem_absSpace_scaledDiag [FiniteDimensional ℂ V] {f : End ℂ V} (hs : f.IsSemisimple)
    (hf : ∀ α ∈ f.charpoly.roots, ‖α‖ = 1) {n : ℕ} (c : Fin n → ℂ) (hc : ∀ i, c i ≠ 0) (r : ℝ)
    (v : Fin n → V) : v ∈ absSpace (scaledDiag f c) r ↔ ∀ i, ‖c i‖ ≠ r → v i = 0 := by
  classical
  constructor
  · intro hv i hi
    have hle : absSpace (scaledDiag f c) r ≤
        LinearMap.ker (LinearMap.proj i : (Fin n → V) →ₗ[ℂ] V) := by
      refine iSup₂_le fun α hα u hu => ?_
      have h1 := congrFun (End.mem_eigenspace_iff.mp hu) i
      simp only [scaledDiag_apply, Pi.smul_apply] at h1
      have h2 : u i ∈ absSpace f ‖α / c i‖ := by
        refine Submodule.mem_iSup_of_mem (α / c i) (Submodule.mem_iSup_of_mem rfl ?_)
        rw [End.mem_eigenspace_iff]
        have : f (u i) = (c i)⁻¹ • (α • u i) := by
          rw [← h1, smul_smul, inv_mul_cancel₀ (hc i), one_smul]
        rw [this, smul_smul, div_eq_inv_mul]
      have h3 : ‖α / c i‖ ≠ 1 := by
        rw [norm_div, Ne, div_eq_one_iff_eq (norm_ne_zero_iff.mpr (hc i)), hα]
        exact fun h => hi h.symm
      rw [absSpace_eq_bot_of_norm_charpoly_roots hf h3, Submodule.mem_bot] at h2
      simp [h2]
    simpa using hle hv
  · intro hv
    rw [← Finset.univ_sum_single v]
    refine Submodule.sum_mem _ fun i _ => ?_
    by_cases hi : ‖c i‖ = r
    · have hvi : v i ∈ absSpace f 1 := by
        rw [absSpace_one_eq_top_of_norm_charpoly_roots hs hf]; trivial
      have hle : (absSpace f 1).map (LinearMap.single ℂ (fun _ : Fin n => V) i) ≤
          absSpace (scaledDiag f c) r := by
        simp only [absSpace, Submodule.map_iSup]
        refine iSup₂_le fun β hβ => ?_
        rintro _ ⟨x, hx, rfl⟩
        refine Submodule.mem_iSup_of_mem (c i * β)
          (Submodule.mem_iSup_of_mem (by rw [norm_mul, hβ, mul_one, hi]) ?_)
        rw [SetLike.mem_coe, End.mem_eigenspace_iff] at hx
        rw [End.mem_eigenspace_iff]
        ext j
        by_cases hj : j = i
        · subst hj; simp [scaledDiag_apply, hx, smul_smul]
        · simp [scaledDiag_apply, hj]
      exact hle ⟨v i, hvi, by simp⟩
    · simp [hv i hi]

theorem isPurePair_scaledDiag_vecShift [FiniteDimensional ℂ V] {q : ℝ} (hq : 1 < q)
    {f : End ℂ V} (hs : f.IsSemisimple) (hf : ∀ α ∈ f.charpoly.roots, ‖α‖ = 1) {n : ℕ}
    (c : Fin n → ℂ) (hc : ∀ i : Fin n, ‖c i‖ = q ^ (((i : ℕ) : ℝ) - ((n : ℝ) - 1) / 2)) :
    IsPurePair q (scaledDiag f c) (vecShift n) := by
  classical
  have hc0 : ∀ i, c i ≠ 0 := fun i h0 => by
    have := hc i
    rw [h0, norm_zero] at this
    exact (Real.rpow_pos_of_pos (zero_lt_one.trans hq) _).ne this
  have hmem : ∀ (j : ℤ) (v : Fin n → V), v ∈ absSpace (scaledDiag f c) (q ^ ((j : ℝ) / 2)) ↔
      ∀ i : Fin n, 2 * ((i : ℕ) : ℤ) + 1 - n ≠ j → v i = 0 := by
    intro j v
    rw [mem_absSpace_scaledDiag hs hf c hc0]
    refine forall_congr' fun i => imp_congr_left (not_congr ?_)
    rw [hc, Real.rpow_right_inj (zero_lt_one.trans hq) hq.ne', ← @Int.cast_inj ℝ]
    push_cast
    constructor <;> intro h <;> linarith
  refine ⟨eq_top_iff.mpr fun v _ => ?_, fun k => ?_⟩
  · rw [← Finset.univ_sum_single v]
    refine Submodule.sum_mem _ fun i _ =>
      Submodule.mem_iSup_of_mem (2 * ((i : ℕ) : ℤ) + 1 - n) ((hmem _ _).mpr fun j hj => ?_)
    rw [Pi.single_eq_of_ne]
    rintro rfl
    exact hj rfl
  · have e1 : (-(k : ℝ) / 2) = ((-(k : ℤ) : ℤ) : ℝ) / 2 := by push_cast; ring
    have e2 : ((k : ℝ) / 2) = (((k : ℤ) : ℤ) : ℝ) / 2 := by push_cast; ring
    rw [e1, e2]
    refine ⟨fun v hv => ?_, fun v hv v' hv' hvv => ?_, fun v hv => ?_⟩
    · rw [SetLike.mem_coe, hmem] at hv ⊢
      intro i hi
      rw [vecShift_pow_apply]
      split_ifs with hk
      · exact hv _ (by simp only; omega)
      · rfl
    · rw [SetLike.mem_coe, hmem] at hv hv'
      ext1 i
      by_cases hi : 2 * ((i : ℕ) : ℤ) + 1 - n = -(k : ℤ)
      · have := congrFun hvv ⟨i + k, by omega⟩
        rw [vecShift_pow_apply, vecShift_pow_apply, if_pos (by simp), if_pos (by simp)] at this
        simpa using this
      · rw [hv i hi, hv' i hi]
    · rw [SetLike.mem_coe, hmem] at hv
      refine ⟨fun i => if hi : (i : ℕ) + k < n then v ⟨i + k, hi⟩ else 0, ?_, ?_⟩
      · rw [SetLike.mem_coe, hmem]
        intro i hi
        split_ifs with hk
        · exact hv _ (by simp only; omega)
        · rfl
      · ext1 i
        rw [vecShift_pow_apply]
        split_ifs with hk h2
        · congr 2
          simp only; omega
        · exfalso; apply h2; simp only; omega
        · exact (hv i (by omega)).symm

end VecShift

end GlobalTheory.WeilDeligne

theorem GlobalTheory.WeilDeligne.WD.tempered_lpChar_lpSp_of_mono0 : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (x : WD h), x.mono0 → (∀ φ : Weil h, deg φ = 1 → ∀ α ∈ x.eig φ, ‖α‖ = 1) → ∀ l : ℕ, (x.lpChar (WD.lpSp (h := h) l)).tempered := by
  intro E Ω _ _ _ _ _ A w h x
  induction x using WD.ind with
  | hP n a =>
  intro hx heig l
  have hN : a.N = 0 := (WD.monodromyZero_ofWeilDeligneRepClass_iff a).mp hx
  rw [WD.lpSp, WD.lpChar_mk, WD.tempered_mk]
  intro φ hφ
  have hroots : ∀ α ∈ (a.ρ φ).charpoly.roots, ‖α‖ = 1 := fun α hα =>
    heig φ hφ α (by rw [WD.eig_mk]; exact hα)
  have hq : (1 : ℝ) < ((normV w : ℕ) : ℝ) := by exact_mod_cast one_lt_normV w
  have hp := isPurePair_scaledDiag_vecShift hq (a.semisimple φ) hroots
    (fun i => (WDRep.spEig w l i : ℂ)) (fun i => by rw [WDRep.spEig, norm_qPow])
  let e := TensorProduct.piScalarRight ℂ ℂ (Fin n → ℂ) (Fin l)
  have h1 : ∀ t, e ((a.tensor (WDRep.sp (h := h) l)).ρ φ t) =
      scaledDiag (a.ρ φ) (fun i => (WDRep.spEig w l i : ℂ)) (e t) := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul x y =>
      ext1 i
      simp [e, TensorProduct.piScalarRightHom_tmul, scaledDiag_apply, hφ, smul_smul]
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  have h2 : ∀ t, e ((a.tensor (WDRep.sp (h := h) l)).N t) = vecShift l (e t) := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul x y =>
      ext1 i
      by_cases hi : 1 ≤ (i : ℕ) <;>
        simp [e, TensorProduct.piScalarRightHom_tmul, vecShift_apply, shiftEnd_apply, hN, hi]
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  refine hp.of_equiv e.symm (fun v => ?_) (fun v => ?_)
  · obtain ⟨t, rfl⟩ := e.surjective v
    rw [← h1, e.symm_apply_apply, e.symm_apply_apply]
  · obtain ⟨t, rfl⟩ := e.surjective v
    rw [← h2, e.symm_apply_apply, e.symm_apply_apply]
end
end

section

open NumberField IsDedekindDomain HeckeValGen GlobalTheory.HeckeSplit

namespace GlobalTheory.HeckeSplit

theorem heckeChar_eq_one_of_degOne : ∀ (F E : Type) [Field F] [NumberField F] [Field E]
    [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E]
    [Algebra.IsQuadraticExtension F E] (χ : Ideles E →* ℂˣ), IsHeckeChar E χ →
    (∀ᶠ w in Filter.cofinite, DegOne F w → TrivAt χ w) → χ = 1 := by
  intro F E _ _ _ _ _ _ _ _ χ hχ hdeg
  have hinf := GlobalTheory.T.heckeChar_inf_trivial_of_trivAt_degOne F E χ hχ hdeg
  have hfin := GlobalTheory.T.heckeChar_trivialAtPlace_of_degOne_cofinite_trivial F E χ hχ hdeg hinf
  ext1 x
  have hfact := (GlobalTheory.T.continuous_ideleChar_local_factorization E χ hχ.1).2.2 x ∅ (fun v _ => hfin v _)
  rw [hfact, hinf]
  simp

end GlobalTheory.HeckeSplit
end

section

open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW

theorem abs_szT_sub_floor_le {R : Ranks} (P : HCParam R) (j : Fin R.m) (s : Bool) :
    |((szT P j s : ℤ) : ℝ) - ((⌊P.e j⌋ : ℤ) : ℝ)| ≤ ((R.t : ℝ) + 1) / 2 := by
  have h0 : (0 : ℤ) ≤ ((R.t : ℤ) + 1) / 2 := by omega
  have h1 : 2 * (((R.t : ℤ) + 1) / 2) ≤ (R.t : ℤ) + 1 := by omega
  have h0' : (0 : ℝ) ≤ ((((R.t : ℤ) + 1) / 2 : ℤ) : ℝ) := by exact_mod_cast h0
  have h1' : 2 * ((((R.t : ℤ) + 1) / 2 : ℤ) : ℝ) ≤ (R.t : ℝ) + 1 := by exact_mod_cast h1
  unfold szT
  generalize ((R.t : ℤ) + 1) / 2 = q at h0' h1'
  cases s
  · simp only [Bool.false_eq_true, if_false, Int.cast_sub]
    rw [abs_le]; constructor <;> linarith
  · simp only [if_true, Int.cast_add]
    rw [abs_le]; constructor <;> linarith

theorem pageWord_not_thick_size : ∀ {D : D7} (L : SizeData₂ D) (C : ℝ) (j : Fin D.R.m) (ε : ℤˣ) (τ φ : D.R.GG), Roomy L C → ∀ i, ¬ (pageWord L j ε τ φ).thick i → ∃ s : ℝ, L.sc.w'' D.R.n ≤ s ∧ s ≤ (wMax D : ℝ) ∧ s ≤ 8 / 5 * L.sc.b' ∧ |(((pageWord L j ε τ φ).sz i : ℤ) : ℝ) - s| ≤ ((D.R.t : ℝ) + 1) / 2 := by
  intro D L C j ε τ φ hR i hi
  have hnt : ¬ Thick D.host (letter τ φ i) := fun h => hi ((GlobalTheory.T.twistedDualOrbitPageWord_thick_iff_thickEmbedding L C j ε τ φ hR i).2 h)
  have h1 := GlobalTheory.T.floor_size_bounds_not_thick_embedding L C (letter τ φ i) j hR hnt
  have h2 := (GlobalTheory.T.maxSizeAtNonThickPlace_le_and_bound L C hR).2 (letter τ φ i) j hnt
  refine ⟨((⌊(hcAt D (letter τ φ i)).e j⌋ : ℤ) : ℝ), h1.1, ?_, h1.2, ?_⟩
  · exact_mod_cast h2
  · exact abs_szT_sub_floor_le _ j _

end GlobalTheory.HTW
end

section

open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW

theorem bHat_large_of_roomy {D : D7} (L : SizeData₂ D) (C : ℝ) (h : Roomy L C) :
    (100 : ℝ) ≤ bHat L ∧ 2 * (etaHat L : ℝ) + sHat L ≤ (bHat L : ℝ) / 10 := by
  obtain ⟨hC, hw, hr, hwb, -, hb⟩ := h
  have he := L.etaSz_pos
  have hS := L.Sc_pos
  have ht : (0 : ℝ) ≤ D.R.t := Nat.cast_nonneg _
  have hL : (0 : ℝ) ≤ D.host.Lw := Nat.cast_nonneg _
  have hb' : (0 : ℝ) ≤ L.sc.b' := by linarith
  have hCL : (100 : ℝ) ≤ C * ((D.host.Lw : ℝ) + 1) := by nlinarith
  have hbb : 100 * L.sc.b' ≤ L.sc.b := le_trans (mul_le_mul_of_nonneg_right hCL hb') hb
  have h1 : (etaHat L : ℝ) ≤ L.etaSz + D.R.t + 2 := by
    have := Nat.floor_le he.le
    unfold etaHat
    push_cast
    linarith
  have h2 : (sHat L : ℝ) ≤ L.Sc := Nat.floor_le hS.le
  have h3 : ⌈L.sc.b⌉₊ ≤ bHat L + D.R.t := by
    unfold bHat
    omega
  have h4 : L.sc.b ≤ (bHat L : ℝ) + D.R.t := by
    have h5 : ((⌈L.sc.b⌉₊ : ℕ) : ℝ) ≤ (bHat L : ℝ) + D.R.t := by exact_mod_cast h3
    exact le_trans (Nat.le_ceil _) h5
  constructor <;> linarith

theorem conjWord_hypAT {D : D7} (L : SizeData₂ D) (C : ℝ) (j : Fin D.R.m) (ε : ℤˣ) (τ : D.R.GG) (l : ℕ)
    (hR : Roomy L C) (hl : 11 ≤ l) (hτ : Thick D.host τ) :
    (pageWord L j ε τ (D.R.cc)).HypAT l ∧ ∀ i, (pageWord L j ε τ (D.R.cc)).thick i := by
  obtain ⟨hord, hplc⟩ := GlobalTheory.T.complexConjugation_orbit_one_realPlace τ
  have hth : ∀ i, (pageWord L j ε τ (D.R.cc)).thick i := by
    intro i
    rw [GlobalTheory.T.twistedDualOrbitPageWord_thick_iff_thickEmbedding L C j ε τ (D.R.cc) hR i]
    unfold Thick at hτ ⊢
    rw [hplc i]
    exact hτ
  refine ⟨⟨?_, ?_, ?_⟩, hth⟩
  · rw [hord]; exact even_two
  · exact (GlobalTheory.T.embeddingSign_alternate_of_sign_neg ε τ (D.R.cc) rfl).2
  · intro M hM i
    obtain ⟨hB, hroom⟩ := bHat_large_of_roomy L C hR
    have hη : (0 : ℝ) ≤ etaHat L := Nat.cast_nonneg _
    have hS : (0 : ℝ) ≤ sHat L := Nat.cast_nonneg _
    have key : ∀ k, (bHat L : ℝ) ≤ ((pageWord L j ε τ (D.R.cc)).sz k : ℝ) ∧
        ((pageWord L j ε τ (D.R.cc)).sz k : ℝ) ≤ (bHat L : ℝ) + etaHat L := by
      intro k
      obtain ⟨h1, h2⟩ := hth k
      have h1' : ((bHat L : ℕ) : ℤ) ≤ (pageWord L j ε τ (D.R.cc)).sz k := h1
      have h2' : (pageWord L j ε τ (D.R.cc)).sz k ≤ ((bHat L : ℕ) : ℤ) + ((etaHat L : ℕ) : ℤ) := h2
      exact ⟨by exact_mod_cast h1', by exact_mod_cast h2'⟩
    obtain ⟨k, hk⟩ := hM.1
    have hMk := key k
    rw [hk] at hMk
    have hi := key i
    obtain ⟨h1, h2⟩ := GlobalTheory.T.alternatingWord_large_size_numerical_bounds l (bHat L) (etaHat L) (sHat L) (M : ℝ)
      ((pageWord L j ε τ (D.R.cc)).sz i : ℝ) hl hB hη hS hroom
      (abs_le.2 ⟨by linarith [hMk.1], by linarith [hMk.2]⟩)
      (abs_le.2 ⟨by linarith [hi.1], by linarith [hi.2]⟩)
    refine ⟨?_, h1, h2⟩
    have : (1 : ℝ) ≤ ((pageWord L j ε τ (D.R.cc)).sz i : ℝ) := by linarith [hi.1]
    exact_mod_cast this

end GlobalTheory.HTW
end

section

open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits

theorem _root_.GlobalTheory.T.mul_smallBounds_le_roundedSizeBound : ∀ {D : D7} (L : SizeData₂ D) (C C' : ℝ) (j : ℕ), Roomy L C' → 0 ≤ C → 2 * C ≤ C' → 2 * j + 2 ≤ D.host.Lw → C * ((j : ℝ) + 1) * (((wHat D + sHat L + etaHat L : ℕ) : ℝ) + 1) ≤ (bHat L : ℝ) := by
  first | exact @GlobalTheory.HTW.mul_small_le_bHat | exact GlobalTheory.HTW.mul_small_le_bHat | (intros; apply GlobalTheory.HTW.mul_small_le_bHat <;> assumption)
end

section

open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits

theorem _root_.GlobalTheory.T.twistedDualOrbitPageWord_box : ∀ {D : D7} (L : SizeData₂ D) (C : ℝ) (j : Fin D.R.m) (ε : ℤˣ) (τ φ : D.R.GG), Roomy L C → (pageWord L j ε τ φ).Box := by
  first | exact @GlobalTheory.HTW.pageWord_box | exact GlobalTheory.HTW.pageWord_box | (intros; apply GlobalTheory.HTW.pageWord_box <;> assumption)
end

section

open GlobalTheory.WH GlobalTheory.PD GlobalTheory.W1 GlobalTheory.CechDR KaehlerDifferential
open scoped TensorProduct
theorem _root_.GlobalTheory.T.exists_chart_lift_of_finite_cover : ∀ (d a : ℕ) (F K K' : Type) [Field F] [Field K] [Field K'] [Algebra ℂ F] [Algebra ℂ K] [Algebra ℂ K'] [Algebra F K] [IsScalarTower ℂ F K] [Algebra K K'] [IsScalarTower ℂ K K'] [Algebra F K'] [IsScalarTower F K K'] [IsScalarTower ℂ F K'] (x : Fin (d + 1) → F) (j2 : K →ₐ[ℂ] K'),
  IsFinCover ℂ K x → IsFinCover ℂ K' x →
  (∀ (i : Fin (d + 1)) (e : rB ℂ K' x {i} →ₐ[ℂ] ℂ), ∃ j : Fin (d + 1), ∀ v ∈ R2 x j2 {j}, ∃ (b : K') (hb : b ∈ rB ℂ K' x {i}), e ⟨b, hb⟩ ≠ 0 ∧ b * v ∈ rB ℂ K' x {i}) →
  IsReduced ((rB ℂ K' x {0}) ⧸ (Ideal.span (Set.range fun j : Fin d => (⟨_, tco_mem ℂ K' x j⟩ : rB ℂ K' x {0})))) →
  (∀ (i : Fin (d + 1)), i ≠ 0 → ∀ e : rB ℂ K' x {i} →ₐ[ℂ] ℂ, ¬ IsFix (rB ℂ K' x {i}) e j2 (rB ℂ K x {i})) →
  (∀ e : rB ℂ K' x {0} →ₐ[ℂ] ℂ, IsFix (rB ℂ K' x {0}) e j2 (rB ℂ K x {0}) → ∀ j : Fin d, e ⟨_, tco_mem ℂ K' x j⟩ = 0) →
  ∀ (Fx : Finset (fib ℂ K' x)), (∀ e : fib ℂ K' x, e ∈ Fx ↔ IsFix (rB ℂ K' x {0}) e.1 j2 (rB ℂ K x {0})) →
  (∀ e ∈ Fx, ∀ (b : K) (hb1 : algebraMap K K' b ∈ rB ℂ K' x {0}), b ∈ rB ℂ K x {0} → e.1 ⟨_, hb1⟩ = 0 →
    ∃ (c : K) (hc1 : algebraMap K K' c ∈ rB ℂ K' x {0}), c ∈ rB ℂ K x {0} ∧ e.1 ⟨_, hc1⟩ ≠ 0 ∧
      ∃ g : Fin d → K, (∀ l, g l ∈ rB ℂ K x {0}) ∧ c * b = ∑ l, g l * algebraMap F K (x l.succ / x 0)) →
  ∀ A : fib ℂ K' x → Matrix (Fin d) (Fin d) ℂ,
  (∀ e ∈ Fx, ∀ m : Fin d, ∃ (c : K') (hc : c ∈ rB ℂ K' x {0}) (g : Fin d → K') (hg : ∀ l, g l ∈ rB ℂ K' x {0}), e.1 ⟨c, hc⟩ ≠ 0 ∧
    c * j2 (algebraMap F K (x m.succ / x 0)) = ∑ l, g l * algebraMap F K' (x l.succ / x 0) ∧ ∀ l, e.1 ⟨g l, hg l⟩ = e.1 ⟨c, hc⟩ * A e m l) →
  (∀ e ∈ Fx, (1 - A e).det ≠ 0) →
  ∀ u : ∀ p : ℕ, (cech fun I => omB ℂ K (rB ℂ K x I) a).H p →ₗ[ℂ] (cech fun I => omB ℂ K (rB ℂ K x I) a).H p,
  (∀ (p : ℕ) (b : Finset (Fin (d + 1)) → DR ℂ K) (hb : b ∈ (cech fun I => omB ℂ K (rB ℂ K x I) a).Z p),
    ∃ bt ∈ (cech fun s : Finset (Fin (d + 1) ⊕ₗ Fin (d + 1)) => omB ℂ K' (RY x j2 (lft s) (rgt s)) a).Z p,
      (∀ J, bt (uni ∅ J) = pr2L j2 (b J)) ∧
      ∃ h : trC (k := ℂ) (K := K) (L := K') (fun I => bt (uni I ∅)) ∈ (cech fun I => omB ℂ K (rB ℂ K x I) a).Z p,
        u p (Submodule.Quotient.mk ⟨b, hb⟩) = Submodule.Quotient.mk ⟨_, h⟩) →
  (∀ p : ℕ, FiniteDimensional ℂ ((cech fun I => omB ℂ K (rB ℂ K x I) a).H p)) →
  ∑ p ∈ Finset.range (d + 1), (-1 : ℂ) ^ p * LinearMap.trace ℂ _ (u p) =
    ∑ e ∈ Fx, (Matrix.det (1 + (Polynomial.X : Polynomial ℂ) • (A e).map Polynomial.C)).coeff a / (1 - A e).det := by
  first | exact @UpperTheory.Cb.exists_chart_lift_of_finite_cover | exact UpperTheory.Cb.exists_chart_lift_of_finite_cover
end

section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead GlobalTheory.ThetaGL GlobalTheory.TameIwahori ValuativeRel

theorem _root_.GlobalTheory.T.tameIwahoriVector_twoBlockProduct_perm_value_first : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (r t : ℕ) (θ : Fin (r + t) → kˣ →* ℂˣ) (V : Type) [AddCommGroup V] [Module ℂ V] (W : Type) [AddCommGroup W] [Module ℂ W] (σ₁ : Representation ℂ (GL (Fin r) k) V) (σ₂ : Representation ℂ (GL (Fin t) k) W) (f : _) (w : Equiv.Perm (Fin (r + t))), IsIwVec θ (prod₂ σ₁ σ₂) f → f.1.1 (GlobalTheory.Parabolic.permGL k w) ≠ 0 → ∃ (s : Equiv.Perm (Fin r)) (y : V), y ≠ 0 ∧ IsIwVec (fun i => θ (w.symm (Fin.castAdd t (s i)))) σ₁ y := by
  first | exact @GlobalTheory.TameIwahori.PermCell.exists_isIwVec_fst | exact GlobalTheory.TameIwahori.PermCell.exists_isIwVec_fst | (intros; apply GlobalTheory.TameIwahori.PermCell.exists_isIwVec_fst <;> assumption)
end
