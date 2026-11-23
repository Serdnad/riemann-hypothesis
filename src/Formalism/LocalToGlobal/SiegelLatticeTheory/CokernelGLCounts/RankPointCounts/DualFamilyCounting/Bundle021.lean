module

public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.NeZeroOfNotMem
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsLatticeOfFibLocNeZeroGood
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.AlmostEverywhereSpherical
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle012
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle016
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle019
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle018
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle001
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle003
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle017

@[expose] public section

section

open NumberField Module Matrix

noncomputable section

namespace Formalism.L2.SG.Pf.GluingBases

open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt Formalism.HermitianLattices.Ext.L3.HU

variable {K F V : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem jι_eq' (t : 𝓞 F) :
    algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) t) = algebraMap F K (t : F) := by
  have e := UnimodularLocalization.algebraMap_smul_K (K := K) t (1 : K)
  rwa [Algebra.smul_def, mul_one, mul_one] at e

theorem inP_of_mem_pow {𝔭 : Ideal (𝓞 F)} [𝔭.IsPrime] {k : ℕ} {t : 𝓞 F} (ht : t ∈ 𝔭 ^ k) :
    InP 𝔭 k (algebraMap F K (t : F)) := by
  rw [← jι_eq']
  apply inP_jK
  rw [extP, ← Ideal.map_pow]
  exact Ideal.mem_map_of_mem _ ht

theorem inP_vF {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {t : 𝓞 F} (ht : t ≠ 0) :
    InP 𝔭 (vF 𝔭 t) (algebraMap F K (t : F)) := by
  have := h𝔭.isPrime
  exact inP_of_mem_pow ((G1.mem_pow_iff h𝔭 ht _).2 le_rfl)

theorem mem_SP_of_inP {𝔭 : Ideal (𝓞 F)} [𝔭.IsPrime] {π s₀ : 𝓞 F} (hu : IsUnif0 𝔭 π s₀) {k : ℕ}
    {x : K} (hx : InP 𝔭 k x) : (algebraMap F K (π : F))⁻¹ ^ k * x ∈ SP K 𝔭 := by
  obtain ⟨s, hs, rfl⟩ := (mem_noncompactPart_iff hu k x).1 hx
  have h0 : algebraMap F K (π : F) ≠ 0 := by
    rw [← jι_eq']; exact jι_ne_zero hu.ne_zero
  rw [jι_eq', ← mul_assoc, ← mul_pow, inv_mul_cancel₀ h0, one_pow, one_mul]
  exact hs

theorem star_fix (hF : IsFixF K F) (x : F) : star (algebraMap F K x) = algebraMap F K x :=
  (hF _).2 ⟨x, rfl⟩

theorem star_inv_pow (hF : IsFixF K F) (x : F) (k : ℕ) :
    star ((algebraMap F K x)⁻¹ ^ k) = (algebraMap F K x)⁻¹ ^ k := by
  rw [← map_inv₀, ← map_pow]; exact star_fix hF _

theorem form_smul_left (h : V →ₗ⋆[K] V →ₗ[K] K) (r : K) (x y : V) :
    h (r • x) y = star r * h x y := by
  rw [map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply]

theorem form_smul_right (h : V →ₗ⋆[K] V →ₗ[K] K) (r : K) (x y : V) :
    h x (r • y) = r * h x y := by
  rw [map_smul, smul_eq_mul]

theorem form_smul_smul (h : V →ₗ⋆[K] V →ₗ[K] K) (r r' : K) (x y : V) :
    h (r • x) (r' • y) = star r * r' * h x y := by
  rw [form_smul_left, form_smul_right]; ring

end Formalism.L2.SG.Pf.GluingBases
end
end

section

namespace Formalism.L2.SG.Pf.Cnt

open Formalism.L2.SG.Pf.G6

theorem glueLoc_of_fibCount (hn : FibCount) : GlueLoc :=
  glueLoc_of projection_into_holds (projOnto_of summand_localization riesz_hermitian_holds) hn

end Formalism.L2.SG.Pf.Cnt
end

section

noncomputable section

namespace Formalism.L2.SG.Pf.NcX.OmVSt

open Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocVol Formalism.L2.SG.TypedSets Formalism.L2.SG.Sub Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
  MeasureTheory NumberField IsDedekindDomain
open scoped TensorProduct

variable {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ)

def scl (v : PlX X) : Fin (D.R.rS + 1 + D.R.rS) → Fv X.B.I.F v :=
  Fin.append (alp v D.R.rS) (fun b : Fin D.R.rS => (alp v D.R.rS b.castSucc)⁻¹)

def yTup (v : PlX X) : TupV (E := X.B.I.E) v X.B.I.n (D.R.rS + 1 + D.R.rS) :=
  fun i => sc (E := X.B.I.E) v (scl X v i) • ratTup (Fv X.B.I.F v) (tupH (frameOf X u')) i

def localGramMatrixFrame (v : PlX X) : Matrix (Fin (D.R.rS + 1 + D.R.rS)) (Fin (D.R.rS + 1 + D.R.rS)) (Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E) :=
  (gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u'))).map (inclR (Fv X.B.I.F v))

abbrev abelian₂ : Set (Fin X.B.I.n → X.B.I.E) := (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E))

def OmVStd : Prop :=
  IsCharAF X.B.I.F ψ → IsStdChar ψ → StdHyp X.B.I.cm.sig X.B.I.J ψ

def OmVLat : Prop :=
  ∃ L : Submodule (𝓞 X.B.I.E) (Fin X.B.I.n → X.B.I.E), Submodule.IsLattice X.B.I.E L ∧ (L : Set (Fin X.B.I.n → X.B.I.E)) = abelian₂ X

def OmVSD : Prop := ∀ v : PlX X, IsSDLoc X.B.I.cm.sig X.B.I.J v (abelian₂ X)

def OmVUnram : Prop := ∀ v : PlX X, UnramAt (E := X.B.I.E) v

def OmVPrim : Prop := ∀ v : PlX X, IsPrim v (abelian₂ X) (yTup X u' v)

def OmVGram : Prop := ∀ v : PlX X, gramR (Fv X.B.I.F v) X.B.I.cm.sig X.B.I.J (yTup X u' v) = localGramMatrixFrame X u' v

def OmVDet : Prop :=
  ∀ v : PlX X, ¬ (((Tw u' : ℕ) : 𝓞 X.B.I.F) ∈ v.asIdeal) →
    ∃ w ∈ OEv (E := X.B.I.E) v, (localGramMatrixFrame X u' v).det ∈ OEv (E := X.B.I.E) v ∧ (localGramMatrixFrame X u' v).det * w = 1

def OmVScale : Prop :=
  IsCharAF X.B.I.F ψ → IsStdChar ψ → ∀ v : PlX X,
    omAt X.B.I.cm.sig X.B.I.J ψ v (localGramMatrixFrame X u' v)
        {Y | ∃ k ∈ Kv X.B.I.cm.sig X.B.I.J (abelian₂ X) v, Y = k • ratTup (Fv X.B.I.F v) (tupH (frameOf X u'))} =
      omAt X.B.I.cm.sig X.B.I.J ψ v (localGramMatrixFrame X u' v)
        {Y | ∃ k ∈ Kv X.B.I.cm.sig X.B.I.J (abelian₂ X) v, Y = k • yTup X u' v}

def OmVBadT : Prop :=
  IsCharAF X.B.I.F ψ → IsStdChar ψ → ∀ v : PlX X, ((Tw u' : ℕ) : 𝓞 X.B.I.F) ∈ v.asIdeal →
    IsSDLoc X.B.I.cm.sig X.B.I.J v (abelian₂ X) → UnramAt (E := X.B.I.E) v → IsPrim v (abelian₂ X) (yTup X u' v) →
    omAt X.B.I.cm.sig X.B.I.J ψ v (localGramMatrixFrame X u' v)
        {Y | ∃ k ∈ Kv X.B.I.cm.sig X.B.I.J (abelian₂ X) v, Y = k • yTup X u' v} =
      ENNReal.ofReal (absV v (dV v) ^ ((X.B.I.n : ℝ) * (D.R.rS + 1 + D.R.rS : ℕ) - ((D.R.rS + 1 + D.R.rS : ℕ) : ℝ) ^ 2 / 2) *
        ∏ j ∈ Finset.Icc (X.B.I.n - (D.R.rS + 1 + D.R.rS)) X.B.I.n,
          (1 - (etaV (E := X.B.I.E) v : ℝ) ^ j * ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-(j : ℤ))))

def OmVLocU : Prop :=
  ∀ (v : PlX X) (a : ℕ) (Y : TupV (E := X.B.I.E) v X.B.I.n a),
    Formalism.L2.SG.Pf.NcLoc.OmLocU X.B.I.cm.sig X.B.I.J ψ v (abelian₂ X) a Y

end Formalism.L2.SG.Pf.NcX.OmVSt
end
end

section

noncomputable section

namespace Formalism.L2.SG.Pf.NcS.IntWittAlg

open Matrix Formalism.UG

section GS

variable {K : Type} [Field K] (σ : K →+* K) {n : ℕ} (J : Matrix (Fin n) (Fin n) K)

theorem exists_aniso (hσ : ∀ z, σ (σ z) = z) (hJ : IsHerm σ J) (h2 : (2 : K) ≠ 0) (u w : Fin n → K)
    (huw : hform σ J u w ≠ 0) : ∃ r t : K, hform σ J (r • u + t • w) (r • u + t • w) ≠ 0 := by
  by_contra H
  push Not at H
  have hexp : ∀ r t : K, hform σ J (r • u + t • w) (r • u + t • w) =
      σ r * r * hform σ J u u + σ r * t * hform σ J u w + σ t * r * hform σ J w u +
        σ t * t * hform σ J w w := by
    intro r t
    simp only [hform_add_left, hform_add_right, hform_smul_left, hform_smul_right]
    ring
  set q := hform σ J u w with hq
  set t : K := 2⁻¹ / q with htdef
  have h1 := H 1 0
  have h2' := H 0 1
  have h3 := H 1 t
  rw [hexp, map_one, map_zero] at h1 h2'
  rw [hexp, map_one] at h3
  have ht : t * q = 2⁻¹ := div_mul_cancel₀ _ huw
  have hst : σ t * hform σ J w u = 2⁻¹ := by
    rw [← hform_conj σ J hσ hJ u w, ← hq, ← map_mul, ht, map_inv₀, map_ofNat]
  have hinv : (2 : K) * 2⁻¹ = 1 := mul_inv_cancel₀ h2
  exact one_ne_zero (by linear_combination h3 - h1 - (σ t * t) * h2' - ht - hst - hinv : (1 : K) = 0)

end GS

theorem hermDiag : Formalism.L2.SG.Pf.NcS.IntWittPf.HermDiag := by
  intro K _ σ hσ h2 n J hJ a X0 hT
  classical
  have hconj := hform_conj σ J hσ hJ
  let W : Submodule K (Fin n → K) := Submodule.span K (Set.range X0)
  let comb : (Fin a → K) → (Fin n → K) := fun c => ∑ l, c l • X0 l
  have hN : ∀ c : Fin a → K, (∀ j, hform σ J (X0 j) (comb c) = 0) → c = 0 := by
    intro c hc
    refine Matrix.eq_zero_of_mulVec_eq_zero hT ?_
    funext j
    have e : hform σ J (X0 j) (∑ l, c l • X0 l) = 0 := hc j
    rw [hform_sum_right] at e
    simp only [mulVec, dotProduct, Matrix.of_apply, Pi.zero_apply]
    rw [← e]
    exact Finset.sum_congr rfl fun l _ => mul_comm _ _
  have hcW : ∀ c, comb c ∈ W := fun c => W.sum_mem fun l _ => W.smul_mem _ (Submodule.subset_span ⟨l, rfl⟩)
  have main : ∀ k ≤ a, ∃ Z : Fin k → Fin n → K, (∀ i, Z i ∈ W) ∧
      (∀ i j, i ≠ j → hform σ J (Z i) (Z j) = 0) ∧ ∀ i, hform σ J (Z i) (Z i) ≠ 0 := by
    intro k
    induction k with
    | zero => intro _; exact ⟨fun i => i.elim0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0⟩
    | succ k ih =>
      intro hk
      obtain ⟨Z, hZW, hZo, hZd⟩ := ih (by omega)
      let f : (Fin a → K) →ₗ[K] (Fin k → K) :=
        { toFun := fun c i => hform σ J (Z i) (comb c)
          map_add' := by
            intro c d
            funext i
            simp only [comb, Pi.add_apply, add_smul, Finset.sum_add_distrib, hform_add_right]
          map_smul' := by
            intro r c
            funext i
            simp only [comb, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, ← smul_smul, ← Finset.smul_sum,
              hform_smul_right] }
      have hlt : Module.finrank K (Fin k → K) < Module.finrank K (Fin a → K) := by
        simp only [Module.finrank_fin_fun]
        omega
      obtain ⟨c, hc, hc0⟩ := (Submodule.ne_bot_iff _).1 (LinearMap.ker_ne_bot_of_finrank_lt (f := f) hlt)
      have hcZ : ∀ i, hform σ J (Z i) (comb c) = 0 := fun i => congrFun (LinearMap.mem_ker.1 hc) i
      obtain ⟨j, hj⟩ : ∃ j, hform σ J (X0 j) (comb c) ≠ 0 := by
        by_contra H
        push Not at H
        exact hc0 (hN c H)
      let w := X0 j - ∑ i, (hform σ J (Z i) (X0 j) / hform σ J (Z i) (Z i)) • Z i
      have hwZ : ∀ m, hform σ J (Z m) w = 0 := by
        intro m
        simp only [w, hform_sub_right, hform_sum_right]
        rw [Finset.sum_eq_single m]
        · rw [div_mul_cancel₀ _ (hZd m), sub_self]
        · intro i _ him
          rw [hZo m i (Ne.symm him), mul_zero]
        · simp
      have hwc : hform σ J w (comb c) ≠ 0 := by
        simp only [w, hform_sub_left, hform_sum_left]
        rw [Finset.sum_eq_zero, sub_zero]
        · exact hj
        · intro i _
          rw [hcZ i, mul_zero]
      have hwW : w ∈ W := W.sub_mem (Submodule.subset_span ⟨j, rfl⟩) (W.sum_mem fun i _ => W.smul_mem _ (hZW i))
      obtain ⟨r, t, hz⟩ := exists_aniso σ J hσ hJ h2 w (comb c) hwc
      set z := r • w + t • comb c with hzdef
      have hzZ : ∀ m, hform σ J (Z m) z = 0 := by
        intro m
        rw [hzdef, hform_add_right, hform_smul_right, hform_smul_right, hwZ, hcZ, mul_zero, mul_zero, add_zero]
      refine ⟨Fin.snoc Z z, ?_, ?_, ?_⟩
      · intro i
        refine Fin.lastCases ?_ (fun i => ?_) i
        · rw [Fin.snoc_last]
          exact W.add_mem (W.smul_mem _ hwW) (W.smul_mem _ (hcW c))
        · rw [Fin.snoc_castSucc]
          exact hZW i
      · intro i j
        refine Fin.lastCases ?_ (fun i => ?_) i <;> refine Fin.lastCases ?_ (fun j => ?_) j
        · intro h; exact absurd rfl h
        · intro _
          rw [Fin.snoc_last, Fin.snoc_castSucc, ← hconj, hzZ, map_zero]
        · intro _
          rw [Fin.snoc_last, Fin.snoc_castSucc]
          exact hzZ i
        · intro hij
          rw [Fin.snoc_castSucc, Fin.snoc_castSucc]
          exact hZo i j (fun e => hij (by rw [e]))
      · intro i
        refine Fin.lastCases ?_ (fun i => ?_) i
        · rw [Fin.snoc_last]
          exact hz
        · rw [Fin.snoc_castSucc]
          exact hZd i
  obtain ⟨Z, hZW, hZo, hZd⟩ := main a le_rfl
  have hex : ∀ i, ∃ c : Fin a → K, ∑ l, c l • X0 l = Z i :=
    fun i => (Submodule.mem_span_range_iff_exists_fun K).1 (hZW i)
  choose C hC using hex
  let P : Matrix (Fin a) (Fin a) K := Matrix.of C
  have hPX : ∀ i, ∑ l, P i l • X0 l = Z i := fun i => hC i
  have hdet : P.det ≠ 0 := by
    intro hd
    obtain ⟨c, hc0, hcP⟩ := Matrix.exists_vecMul_eq_zero_iff.2 hd
    apply hc0
    funext j
    have e : ∑ i, c i • Z i = 0 := by
      have hl : ∀ l, ∑ i, c i * P i l = 0 := fun l => by
        have := congrFun hcP l
        simpa [vecMul, dotProduct] using this
      simp_rw [← hPX, Finset.smul_sum, smul_smul]
      rw [Finset.sum_comm]
      simp_rw [← Finset.sum_smul, hl, zero_smul, Finset.sum_const_zero]
    have h := congrArg (hform σ J (Z j)) e
    rw [hform_sum_right, hform_zero_right, Finset.sum_eq_single j] at h
    · exact (mul_eq_zero.1 h).resolve_right (hZd j)
    · intro i _ hij
      rw [hZo j i (Ne.symm hij), mul_zero]
    · simp
  refine ⟨P, P⁻¹, Matrix.nonsing_inv_mul P (isUnit_iff_ne_zero.2 hdet), ?_, ?_⟩
  · intro i j hij
    rw [hPX, hPX]
    exact hZo i j hij
  · intro i
    rw [hPX]
    exact hZd i

end Formalism.L2.SG.Pf.NcS.IntWittAlg
end
end

section

noncomputable section

namespace Formalism.L2.SG.Pf.NcS.IntWittAlg

open Matrix Formalism.UG

private theorem s_inv_eq_of_s_eq_of_mul_eq_one {S : Type} [CommRing S] (s : S →+* S) (b b' : S) (hb : s b = b)
    (h : b * b' = 1) : s b' = b' := by
  have h1 : s b * s b' = 1 := by rw [← map_mul, h, map_one]
  rw [hb] at h1
  calc s b' = (b' * b) * s b' := by rw [mul_comm b' b, h, one_mul]
    _ = b' * (b * s b') := by ring
    _ = b' := by rw [h1, mul_one]

private theorem hform_transvection_preserves {S : Type} [CommRing S] (s : S →+* S) (hs : ∀ z, s (s z) = z) {n : ℕ}
    (J : Matrix (Fin n) (Fin n) S) (hJ : IsHerm s J) (v : Fin n → S) (b b' lam : S)
    (hvv : hform s J v v = b) (hbb : b * b' = 1) (hb' : s b' = b') (hlam : lam * s lam = 1)
    (z w : Fin n → S) :
    hform s J (z + ((s lam - 1) * (b' * hform s J v z)) • v)
      (w + ((s lam - 1) * (b' * hform s J v w)) • v) = hform s J z w := by
  have hzv : hform s J z v = s (hform s J v z) := (hform_conj s J hs hJ v z).symm
  simp only [hform_add_left, hform_add_right, hform_smul_left, hform_smul_right]
  rw [hzv, hvv]
  simp only [map_mul, map_sub, map_one, hs, hb']
  linear_combination (b' * hform s J v w * s (hform s J v z)) * hlam +
    (b' * hform s J v w * s (hform s J v z) * (lam - 1) * (s lam - 1)) * hbb

theorem algWitt : Formalism.L2.SG.Pf.NcS.IntWittPf.AlgWitt := by
  unfold Formalism.L2.SG.Pf.NcS.IntWittPf.AlgWitt
  intro S _ s O hs hsO n J J' hJ hJJ' hJO hJ'O a β β' hβO hβ'O hββ' hH x y hxO hyO hxx hyy

  have key : ∀ k : ℕ, k ≤ a → ∃ M : Matrix (Fin n) (Fin n) S,
      (∀ z w, hform s J (M *ᵥ z) (M *ᵥ w) = hform s J z w) ∧ (∀ i j, M i j ∈ O) ∧
      ∀ i : Fin a, i.val < k → M *ᵥ y i = x i := by
    intro k
    induction k with
    | zero =>
      intro _
      refine ⟨1, fun z w => by rw [Matrix.one_mulVec, Matrix.one_mulVec],
        fun i j => Formalism.L2.SG.Pf.NcS.IntWittAlg.one_mem' O i j, fun i hi => absurd hi (Nat.not_lt_zero _)⟩
    | succ k ih =>
      intro hk
      obtain ⟨M, hMp, hMO, hMy⟩ := ih (Nat.le_of_succ_le hk)
      obtain ⟨i0, hi0⟩ : ∃ i0 : Fin a, i0.val = k := ⟨⟨k, hk⟩, rfl⟩
      obtain ⟨yy, hyy_def⟩ : ∃ yy : Fin n → S, yy = M *ᵥ y i0 := ⟨_, rfl⟩
      have hyyO : ∀ l, yy l ∈ O := fun l => by
        rw [hyy_def]; exact mulVec_mem O M hMO (y i0) (hyO i0) l
      have htO : hform s J (x i0) yy ∈ O := hform_mem O s hsO J hJO (x i0) yy (hxO i0) hyyO
      obtain ⟨lam, hlamO, hlam, c', hc'O, hc'⟩ := hH i0 (hform s J (x i0) yy) htO
      have hxx0 : hform s J (x i0) (x i0) = β i0 := by rw [hxx, if_pos rfl]
      have hyy0 : hform s J yy yy = β i0 := by rw [hyy_def, hMp, hyy, if_pos rfl]
      have hβr : s (β i0) = β i0 := by
        have h := hform_conj s J hs hJ (x i0) (x i0)
        rwa [hxx0] at h
      have hβ'r : s (β' i0) = β' i0 := s_inv_eq_of_s_eq_of_mul_eq_one s (β i0) (β' i0) hβr (hββ' i0)

      obtain ⟨u, hu_def⟩ : ∃ u : Fin n → S, u = yy - lam • x i0 := ⟨_, rfl⟩
      have huO : ∀ l, u l ∈ O := fun l => by
        rw [hu_def, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
        exact O.sub_mem (hyyO l) (O.mul_mem hlamO (hxO i0 l))
      have huy : hform s J u yy = β i0 - s lam * hform s J (x i0) yy := by
        rw [hu_def, hform_sub_left, hform_smul_left, hyy0]
      have huu : hform s J u u =
          (β i0 - s lam * hform s J (x i0) yy) + s (β i0 - s lam * hform s J (x i0) yy) := by
        rw [hu_def]
        simp only [hform_sub_left, hform_sub_right, hform_smul_left, hform_smul_right]
        rw [hyy0, hxx0, ← hform_conj s J hs hJ (x i0) yy]
        simp only [map_sub, map_mul, hs, hβr]
        linear_combination (β i0) * hlam
      have hcc : c' * (β i0 - s lam * hform s J (x i0) yy) = 1 := by rw [mul_comm]; exact hc'
      obtain ⟨T, hT⟩ : ∃ T : Matrix (Fin n) (Fin n) S, T = rT s J u c' 1 := ⟨_, rfl⟩
      have hT_mul : ∀ z, T *ᵥ z = z - (c' * hform s J u z) • u := fun z => by
        rw [hT, rT_mulVec, map_one, one_smul]
      have hT_pres : ∀ z w, hform s J (T *ᵥ z) (T *ᵥ w) = hform s J z w := fun z w => by
        rw [hT]
        exact rT_preserves s J hs hJ u _ c' 1 (by rw [map_one, one_mul]) huu hcc z w
      have hT_O : ∀ i j, T i j ∈ O := fun i j => by
        rw [hT]; exact rT_mem O s hsO J hJO u huO c' 1 hc'O O.one_mem i j
      have hT_yy : T *ᵥ yy = lam • x i0 := by
        rw [hT_mul, huy, hcc, one_smul, hu_def, sub_sub_cancel]

      obtain ⟨D, hD⟩ : ∃ D : Matrix (Fin n) (Fin n) S,
          D = 1 + (s lam - 1) • pM s J {i0} x β' := ⟨_, rfl⟩
      have hD_mul : ∀ z, D *ᵥ z = z + ((s lam - 1) * (β' i0 * hform s J (x i0) z)) • x i0 :=
        fun z => by
          rw [hD, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, pM_mulVec,
            Finset.sum_singleton, smul_smul]
      have hD_pres : ∀ z w, hform s J (D *ᵥ z) (D *ᵥ w) = hform s J z w := fun z w => by
        rw [hD_mul, hD_mul]
        exact hform_transvection_preserves s hs J hJ (x i0) (β i0) (β' i0) lam hxx0 (hββ' i0) hβ'r hlam z w
      have hD_O : ∀ i j, D i j ∈ O := fun i j => by
        rw [hD, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
        exact O.add_mem (Formalism.L2.SG.Pf.NcS.IntWittAlg.one_mem' O i j)
          (O.mul_mem (O.sub_mem (hsO lam hlamO) O.one_mem)
            (pM_mem O s hsO J hJO {i0} x hxO β' hβ'O i j))
      have hD_x : D *ᵥ (lam • x i0) = x i0 := by
        rw [hD_mul, hform_smul_right, hxx0]
        funext l
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        linear_combination (x i0 l) * hlam + (x i0 l * (lam * s lam - lam)) * hββ' i0

      have hfix : ∀ i : Fin a, i.val < k → D *ᵥ (T *ᵥ x i) = x i := by
        intro i hi
        have hne : i0 ≠ i := fun h => by subst h; omega
        have h0 : hform s J u (x i) = 0 := by
          rw [hu_def, hform_sub_left, hform_smul_left, hxx i0 i, if_neg hne, ← hMy i hi, hyy_def,
            hMp, hyy i0 i, if_neg hne]
          ring
        rw [hT_mul, h0, mul_zero, zero_smul, sub_zero, hD_mul, hxx i0 i, if_neg hne, mul_zero,
          mul_zero, zero_smul, add_zero]
      refine ⟨D * T * M, fun z w => ?_, fun i j => ?_, fun i hi => ?_⟩
      · rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
          ← Matrix.mulVec_mulVec, hD_pres, hT_pres, hMp]
      · exact Formalism.L2.SG.Pf.NcS.IntWittAlg.mul_mem' O (D * T) M
          (fun i j => Formalism.L2.SG.Pf.NcS.IntWittAlg.mul_mem' O D T hD_O hT_O i j) hMO i j
      · rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
        rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hlt | heq
        · rw [hMy i hlt]; exact hfix i hlt
        · have hi' : i = i0 := Fin.ext (by omega)
          rw [hi', ← hyy_def, hT_yy, hD_x]
  obtain ⟨M, hMp, hMO, hMy⟩ := key a le_rfl
  have hU : cT s M * J * M = J := unitary_of s J M hMp
  have hNM : (J' * cT s M * J) * M = 1 := by
    calc (J' * cT s M * J) * M = J' * (cT s M * J * M) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hU, hJJ']
  have hMN : M * (J' * cT s M * J) = 1 := mul_eq_one_comm.mp hNM
  refine ⟨⟨M, J' * cT s M * J, hMN, hNM⟩, ?_, fun i j => hMO i j, fun i j => ?_, fun i => hMy i i.isLt⟩
  · show cT s M * J * M = J
    exact hU
  · show (J' * cT s M * J) i j ∈ O
    exact Formalism.L2.SG.Pf.NcS.IntWittAlg.mul_mem' O (J' * cT s M) J
      (fun i j => Formalism.L2.SG.Pf.NcS.IntWittAlg.mul_mem' O J' (cT s M) hJ'O
        (fun i j => cT_mem O s hsO M hMO i j) i j) hJO i j

end Formalism.L2.SG.Pf.NcS.IntWittAlg
end
end
