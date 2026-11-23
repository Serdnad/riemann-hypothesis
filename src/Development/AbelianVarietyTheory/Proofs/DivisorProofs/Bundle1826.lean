module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1778
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle004
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1752
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1784
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1237
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StableTwistedOrbitalProduct
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1235
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsNormalisedThetaSub
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MvIsIntMapMap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankOfMulEqOne
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobeniusMatrixFrameAtPrimitiveRootFactor
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle367
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle045
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1571
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle426
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle048
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle006
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle011
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1792
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1793
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
import Mathlib.LinearAlgebra.LinearIndependent.BaseChange
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction

@[expose] public section

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.UnitaryClasses
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section
namespace GlobalTheory.UnitaryClasses.BaseChangeSign

section Gen
variable {L : Type} [Field L] (τ : L →+* L) {n : ℕ}

theorem hform_eq_mat (J : Matrix (Fin n) (Fin n) L) {ι : Type} [Fintype ι] (f : ι → Fin n → L) (i j : ι) :
    hform τ J (f i) (f j) = (cT τ (Matrix.of fun r i => f i r) * J * Matrix.of fun r i => f i r) i j := by
  simp only [hform, cT, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Matrix.of_apply, Finset.sum_mul]
  rw [Finset.sum_comm]

theorem gram_det_change (J : Matrix (Fin n) (Fin n) L) (V : Submodule L (Fin n → L)) {ι : Type} [Fintype ι]
    [DecidableEq ι] (c b : Module.Basis ι L V) :
    (Matrix.of fun i j => hform τ J (b i).1 (b j).1).det =
      τ (c.toMatrix b).det * (Matrix.of fun i j => hform τ J (c i).1 (c j).1).det * (c.toMatrix b).det := by
  have hM : (Matrix.of fun r i => ((b i : V) : Fin n → L) r) =
      (Matrix.of fun r i => ((c i : V) : Fin n → L) r) * c.toMatrix b := by
    ext r j
    simp only [Matrix.of_apply, Matrix.mul_apply]
    have h := c.sum_toMatrix_smul_self b j
    calc ((b j : V) : Fin n → L) r = ((∑ i, c.toMatrix b i j • c i : V) : Fin n → L) r := by rw [h]
      _ = _ := by
        simp only [Submodule.coe_sum, Finset.sum_apply, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul]
        exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have e1 : (Matrix.of fun i j => hform τ J (b i).1 (b j).1) =
      cT τ (Matrix.of fun r i => ((b i : V) : Fin n → L) r) * J * Matrix.of fun r i => ((b i : V) : Fin n → L) r := by
    ext i j; exact hform_eq_mat τ J (fun i => ((b i : V) : Fin n → L)) i j
  have e2 : (Matrix.of fun i j => hform τ J (c i).1 (c j).1) =
      cT τ (Matrix.of fun r i => ((c i : V) : Fin n → L) r) * J * Matrix.of fun r i => ((c i : V) : Fin n → L) r := by
    ext i j; exact hform_eq_mat τ J (fun i => ((c i : V) : Fin n → L)) i j
  have hdet : ∀ P : Matrix ι ι L, (cT τ P).det = τ P.det := by
    intro P; unfold cT; rw [Matrix.det_transpose, RingHom.map_det]; rfl
  rw [e1, e2, hM, cT_mul]
  set Mc := Matrix.of fun r i => ((c i : V) : Fin n → L) r
  set P := c.toMatrix b
  have : cT τ P * cT τ Mc * J * (Mc * P) = cT τ P * (cT τ Mc * J * Mc) * P := by
    simp only [Matrix.mul_assoc]
  rw [this, Matrix.det_mul, Matrix.det_mul, hdet]

theorem toMatrix_det_ne {V : Submodule L (Fin n → L)} {ι : Type} [Fintype ι] [DecidableEq ι]
    (c b : Module.Basis ι L V) : (c.toMatrix b).det ≠ 0 := by
  intro h
  have := congrArg Matrix.det (c.toMatrix_mul_toMatrix_flip b)
  rw [Matrix.det_mul, h, zero_mul, Matrix.det_one] at this
  exact zero_ne_one this

end Gen

section BC
variable {K L : Type} [Field K] [Field L] (φ : K →+* L) {n : ℕ}

theorem mem_ker_map {A : Matrix (Fin n) (Fin n) K} {x : Fin n → K} (hx : x ∈ LinearMap.ker (Matrix.toLin' A)) :
    (φ ∘ x) ∈ LinearMap.ker (Matrix.toLin' (A.map φ)) := by
  rw [LinearMap.mem_ker, Matrix.toLin'_apply] at hx ⊢
  funext i
  rw [← RingHom.map_mulVec, hx]; simp

theorem finrank_ker_map (A : Matrix (Fin n) (Fin n) K) :
    Module.finrank L (LinearMap.ker (Matrix.toLin' (A.map φ))) =
      Module.finrank K (LinearMap.ker (Matrix.toLin' A)) := by
  have h1 := LinearMap.finrank_range_add_finrank_ker (Matrix.toLin' (A.map φ))
  have h2 := LinearMap.finrank_range_add_finrank_ker (Matrix.toLin' A)
  have h3 : (A.map φ).rank = A.rank := GlobalTheory.Core.Rk.rank_map_field φ A
  have hr1 : Module.finrank L (LinearMap.range (Matrix.toLin' (A.map φ))) = (A.map φ).rank := Matrix.finrank_range_mulVecLin (A.map φ)
  have hr2 : Module.finrank K (LinearMap.range (Matrix.toLin' A)) = A.rank := Matrix.finrank_range_mulVecLin A
  rw [hr1] at h1
  rw [hr2] at h2
  simp only [Module.finrank_fin_fun] at h1 h2
  omega

end BC

section Val
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem ordL_mul {x y : L} (hx : x ≠ 0) (hy : y ≠ 0) : ordL (x * y) = ordL x + ordL y := by
  have hx' : Valued.v x ≠ 0 := (Valuation.ne_zero_iff _).2 hx
  have hy' : Valued.v y ≠ 0 := (Valuation.ne_zero_iff _).2 hy
  have hxy' : Valued.v (x * y) ≠ 0 := (Valuation.ne_zero_iff _).2 (mul_ne_zero hx hy)
  unfold ordL
  rw [dite_eq_right hx', dite_eq_right hy', dite_eq_right hxy']
  have : WithZero.unzero hxy' = WithZero.unzero hx' * WithZero.unzero hy' := by
    apply WithZero.coe_injective
    rw [WithZero.coe_mul, WithZero.coe_unzero, WithZero.coe_unzero, WithZero.coe_unzero, map_mul]
  rw [this, toAdd_mul]; ring

theorem sign_conj_mul {τ : L →+* L} (hv : ∀ x, Valued.v (τ x) = Valued.v x) {t : L} (ht : t ≠ 0) (a : L) :
    (-1 : ℂ) ^ ordL (τ t * a * t) = (-1) ^ ordL a := by
  by_cases ha : a = 0
  · simp [ha]
  have hτ : τ t ≠ 0 := (map_ne_zero τ).2 ht
  have ho : ordL (τ t) = ordL t := by
    unfold ordL; simp only [hv]
  rw [ordL_mul (mul_ne_zero hτ ha) ht, ordL_mul hτ ha, ho,
    show ordL t + ordL a + ordL t = ordL a + 2 * ordL t by ring, zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0), _root_.zpow_mul]
  norm_num

end Val

section Main
variable {K L : Type} [Field K] [Field L] (σ : K →+* K) (τ : L →+* L) (φ : K →+* L) {n : ℕ}

theorem gram_det_map (hφ : ∀ x, τ (φ x) = φ (σ x)) (H A : Matrix (Fin n) (Fin n) K) :
    ∃ t : L, t ≠ 0 ∧ (gramOn τ (H.map φ) (LinearMap.ker (Matrix.toLin' (A.map φ)))).det =
      τ t * φ (gramOn σ H (LinearMap.ker (Matrix.toLin' A))).det * t := by
  letI := φ.toAlgebra
  haveI : FaithfulSMul K L := (faithfulSMul_iff_algebraMap_injective K L).2 φ.injective
  set V := LinearMap.ker (Matrix.toLin' A) with hV
  set V' := LinearMap.ker (Matrix.toLin' (A.map φ)) with hV'
  have hk : Module.finrank L V' = Module.finrank K V := finrank_ker_map φ A
  rcases isEmpty_or_nonempty (Fin (Module.finrank L V')) with he | hne
  · haveI : IsEmpty (Fin (Module.finrank K V)) := hk ▸ he
    refine ⟨1, one_ne_zero, ?_⟩
    rw [Matrix.det_isEmpty, Matrix.det_isEmpty]; simp
  let b := Module.finBasis K V
  let v : Fin (Module.finrank L V') → V' := fun i =>
    ⟨φ ∘ ((b (Fin.cast hk i) : V) : Fin n → K), mem_ker_map φ (b (Fin.cast hk i)).2⟩
  have hli : LinearIndependent L v := by
    apply LinearIndependent.of_comp V'.subtype
    have h0 : LinearIndependent K (fun i => ((b (Fin.cast hk i) : V) : Fin n → K)) :=
      (b.linearIndependent.map' V.subtype V.ker_subtype).comp _ (Fin.cast_injective hk)
    exact linearIndependent_algebraMap_comp_iff.2 h0
  let c := basisOfLinearIndependentOfCardEqFinrank hli (Fintype.card_fin _)
  have hc : ∀ i, c i = v i := fun i => by simp [c]
  refine ⟨(c.toMatrix (Module.finBasis L V')).det, toMatrix_det_ne c _, ?_⟩
  have e1 : gramOn τ (H.map φ) V' =
      Matrix.of fun i j => hform τ (H.map φ) (Module.finBasis L V' i).1 (Module.finBasis L V' j).1 := rfl
  rw [e1, gram_det_change τ (H.map φ) V' c (Module.finBasis L V')]
  have e2 : (Matrix.of fun i j => hform τ (H.map φ) (c i).1 (c j).1) =
      ((gramOn σ H V).map φ).submatrix (finCongr hk) (finCongr hk) := by
    ext i j

    simp only [Matrix.of_apply, hc, v, Matrix.submatrix_apply, Matrix.map_apply, gramOn, hform, map_sum, map_mul,
    Function.comp_apply, hφ, finCongr_apply]
    rfl
  rw [e2, Matrix.det_submatrix_equiv_self,
    show ((gramOn σ H V).map φ).det = φ (gramOn σ H V).det from (RingHom.map_det φ _).symm]

end Main

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (w : Pl E), ¬ IsSplitAt w →
    ∀ (n : ℕ) (H A : Matrix (Fin n) (Fin n) E),
    (-1 : ℂ) ^ ordL (gramOn (cj w) (H.map (algebraMap E (w.adicCompletion E)))
      (LinearMap.ker (Matrix.toLin' (A.map (algebraMap E (w.adicCompletion E)))))).det =
    (-1) ^ ordL (algebraMap E (w.adicCompletion E)
      (gramOn (IsCMField.complexConj E).toRingEquiv.toRingHom H (LinearMap.ker (Matrix.toLin' A))).det) := by
  intro E _ _ _ hU w hw n H A
  have hc := GlobalTheory.ConjAtPlace.main E hU w
  have hφ : ∀ x : E, cj w (algebraMap E (w.adicCompletion E) x) =
      algebraMap E (w.adicCompletion E) ((IsCMField.complexConj E).toRingEquiv.toRingHom x) :=
    fun x => (hc.2.2.2.1 hw).1 x
  obtain ⟨t, ht, hdet⟩ := gram_det_map (IsCMField.complexConj E).toRingEquiv.toRingHom (cj w)
    (algebraMap E (w.adicCompletion E)) hφ H A
  rw [hdet, sign_conj_mul hc.2.2.1 ht]

end GlobalTheory.UnitaryClasses.BaseChangeSign
end
end

section

open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT
open scoped Classical

noncomputable section

namespace GlobalTheory.BCT.StTwLevel

theorem finsum_const_mul {ι : Type} (c : ℂ) (g : ι → ℂ) : ∑ᶠ i, c * g i = c * ∑ᶠ i, g i := by
  by_cases hc : c = 0
  · simp [hc]
  by_cases h : (Function.support g).Finite
  · exact (mul_finsum _ _).symm
  · have hs : Function.support (fun i => c * g i) = Function.support g := by
      ext i; simp [hc]
    rw [finsum_of_infinite_support h, mul_zero, finsum_of_infinite_support (by rwa [hs])]

theorem avg_const_mul {H : Type} [Group H] (c : ℂ) (u : H → ℂ) : avg (fun h => c * u h) = c * avg u := by
  by_cases hc : c = 0
  · simp [hc, avg]
  have hR : rStab (fun h => c * u h) = rStab u := by
    ext k
    simp only [GlobalTheory.TwOrbConj.mem_rStab, mul_right_inj' hc]
  unfold avg
  rw [hR, finsum_const_mul]
  ring

theorem twOrb_const_mul {G : Type} [Group G] [TopologicalSpace G] (θ : G →* G) (K : Subgroup G) (δ : G) (c : ℂ)
    (f : G → ℂ) : twOrb θ K δ (fun x => c * f x) = c * twOrb θ K δ f := by
  unfold twOrb
  simp_rw [avg_const_mul]
  rw [← finsum_const_mul]
  refine finsum_congr fun q => ?_
  ring

theorem clSum_const_mul {G : Type} [Group G] [TopologicalSpace G] (θ : G →* G) (K : Subgroup G) (S : Set G)
    (wt : G → ℂ) (c : ℂ) (f : G → ℂ) : clSum θ K S wt (fun x => c * f x) = c * clSum θ K S wt f := by
  unfold clSum
  rw [← finsum_const_mul]
  refine finsum_congr fun d => ?_
  split_ifs
  · rw [twOrb_const_mul]; ring
  · simp

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem stTw2_const_mul (a b : ℕ) (w : Pl E) (Q₁ Q₂ : (w.adicCompletion E)[X]) (c : ℂ)
    (φ : GLw a w × GLw b w → ℂ) : stTw2 a b w Q₁ Q₂ (fun y => c * φ y) = c * stTw2 a b w Q₁ Q₂ φ := by
  unfold stTw2
  exact clSum_const_mul _ _ _ _ _ _

def lev (n : ℕ) (w : Pl E) (k : ℕ) (y : GLw n w) : ℂ :=
  if y ∈ GlobalTheory.LFun.KGL w (n := n) ∧ nrmL n w y ∈ GlobalTheory.PrincCong.congSub w n k then 1 else 0

theorem nrm_eq {w : Pl E} (hw : ¬ IsSplitAt w) (n : ℕ) (y : GLw n w) : nrmL n w y = y * thL n w y := by
  unfold nrmL thL
  rw [if_neg hw, if_neg hw]

theorem thL_KGL {w : Pl E} (hw : ¬ IsSplitAt w) (n : ℕ) {g : GLw n w} (hg : g ∈ GlobalTheory.LFun.KGL w (n := n)) :
    thL n w g ∈ GlobalTheory.LFun.KGL w (n := n) := by
  have ht : thL n w = thetaGL n (cj w) := by unfold thL; rw [if_neg hw]
  rw [ht]
  obtain ⟨h, rfl⟩ := hg
  let c' : Ov E w →+* Ov E w := (cj w).restrict (Ov E w) (Ov E w) (GlobalTheory.PrincCong.cj_mem_Ov w)
  exact ⟨thetaGL n c' h, GlobalTheory.ThetaPull.map_thetaGL (Ov E w).subtype c' (cj w) (fun x => rfl) h⟩

theorem conj_mem_congSub {w : Pl E} {n k : ℕ} {h g : GLw n w} (hh : h ∈ GlobalTheory.LFun.KGL w (n := n))
    (hg : g ∈ GlobalTheory.PrincCong.congSub w n k) : h * g * h⁻¹ ∈ GlobalTheory.PrincCong.congSub w n k := by
  obtain ⟨h', rfl⟩ := hh
  obtain ⟨g', hg', rfl⟩ := hg
  exact ⟨h' * g' * h'⁻¹, (MonoidHom.normal_ker _).conj_mem g' hg' h', by simp only [map_mul, map_inv]⟩

end GlobalTheory.BCT.StTwLevel

namespace GlobalTheory.BCT.StTwLevel

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem congSub_le {w : Pl E} {n k : ℕ} {g : GLw n w} (hg : g ∈ GlobalTheory.PrincCong.congSub w n k) :
    g ∈ GlobalTheory.LFun.KGL w (n := n) := ((GlobalTheory.PrincCong.mem_congSub_iff w n k g).1 hg).1

theorem lev_level {w : Pl E} (hw : ¬ IsSplitAt w) (n k : ℕ) :
    IsLevel (thL n w) (GlobalTheory.LFun.KGL w (n := n)) (GlobalTheory.PrincCong.congSub w n k) :=
  ⟨GlobalTheory.PrincCong.isOpen_congSub w n k, fun _ hg => congSub_le hg, GlobalTheory.PrincCong.thL_mem_congSub w hw n k⟩

theorem lev_hecke {w : Pl E} (hw : ¬ IsSplitAt w) (n k : ℕ) :
    IsHecke (GlobalTheory.PrincCong.congSub w n k) (lev n w k) := by
  refine ⟨?_, fun x hx y => ⟨?_, ?_⟩⟩
  · have hc := GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w n
    refine HasCompactSupport.intro' hc.2 (Subgroup.isClosed_of_isOpen _ hc.1) fun y hy => ?_
    unfold lev
    exact if_neg fun h => hy h.1
  · have hxK := congSub_le hx
    have hθx := GlobalTheory.PrincCong.thL_mem_congSub w hw n k x hx
    unfold lev
    refine if_congr ?_ rfl rfl
    by_cases hy : y ∈ GlobalTheory.LFun.KGL w (n := n)
    · have hxy : x * y ∈ GlobalTheory.LFun.KGL w (n := n) := mul_mem hxK hy
      have hθy := thL_KGL hw n hy
      have hm : (thL n w y)⁻¹ * thL n w x * thL n w y ∈ GlobalTheory.PrincCong.congSub w n k := by
        simpa using conj_mem_congSub (inv_mem hθy) hθx
      have e : nrmL n w (x * y) = x * nrmL n w y * ((thL n w y)⁻¹ * thL n w x * thL n w y) := by
        rw [nrm_eq hw, nrm_eq hw, map_mul]; group
      rw [e, Subgroup.mul_mem_cancel_right _ hm, Subgroup.mul_mem_cancel_left _ hx]
      exact ⟨fun h => ⟨hy, h.2⟩, fun h => ⟨hxy, h.2⟩⟩
    · have hxy : x * y ∉ GlobalTheory.LFun.KGL w (n := n) := fun h => hy (by simpa using mul_mem (inv_mem hxK) h)
      exact ⟨fun h => absurd h.1 hxy, fun h => absurd h.1 hy⟩
  · have hxK := congSub_le hx
    have hθx := GlobalTheory.PrincCong.thL_mem_congSub w hw n k x hx
    unfold lev
    refine if_congr ?_ rfl rfl
    by_cases hy : y ∈ GlobalTheory.LFun.KGL w (n := n)
    · have hxy : y * x ∈ GlobalTheory.LFun.KGL w (n := n) := mul_mem hy hxK
      have hθy := thL_KGL hw n hy
      have hm : (thL n w y)⁻¹ * x * thL n w y ∈ GlobalTheory.PrincCong.congSub w n k := by
        simpa using conj_mem_congSub (inv_mem hθy) hx
      have e : nrmL n w (y * x) = nrmL n w y * ((thL n w y)⁻¹ * x * thL n w y) * thL n w x := by
        rw [nrm_eq hw, nrm_eq hw, map_mul]; group
      rw [e, Subgroup.mul_mem_cancel_right _ hθx, Subgroup.mul_mem_cancel_right _ hm]
      exact ⟨fun h => ⟨hy, h.2⟩, fun h => ⟨hxy, h.2⟩⟩
    · have hxy : y * x ∉ GlobalTheory.LFun.KGL w (n := n) := fun h => hy (by simpa using mul_mem h (inv_mem hxK))
      exact ⟨fun h => absurd h.1 hxy, fun h => absurd h.1 hy⟩

theorem lev_eq {w : Pl E} (n k : ℕ) :
    (fun y : GLw n w => if y ∈ GlobalTheory.LFun.KGL w (n := n) ∧ nrmL n w y ∈ {g : GLw n w | g ∈ GlobalTheory.LFun.KGL w (n := n) ∧ ∀ i j,
      Valued.v (g.val i j - (1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i j) ≤ WithZero.exp (-(k : ℤ))}
      then (1 : ℂ) else 0) = lev n w k := by
  funext y
  unfold lev
  exact if_congr (and_congr Iff.rfl (GlobalTheory.PrincCong.mem_congSub_iff w n k _).symm) rfl rfl

theorem stTw2_lev : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E), ¬ IsSplitAt w → ∀ (a b k : ℕ) (Q₁ Q₂ : (w.adicCompletion E)[X]) (c : ℂ), Q₁.Monic → Q₂.Monic → Q₁.natDegree = a → Q₂.natDegree = b → (Q₁ * Q₂).Separable → stTw2 a b w Q₁ Q₂ (fun y : GLw a w × GLw b w => c * (if y.1 ∈ GlobalTheory.LFun.KGL w (n := a) ∧ nrmL a w y.1 ∈ {g : GLw a w | g ∈ GlobalTheory.LFun.KGL w (n := a) ∧ ∀ i j, Valued.v (g.val i j - (1 : Matrix (Fin a) (Fin a) (w.adicCompletion E)) i j) ≤ WithZero.exp (-(k : ℤ))} ∧ y.2 ∈ GlobalTheory.LFun.KGL w (n := b) ∧ nrmL b w y.2 ∈ {g : GLw b w | g ∈ GlobalTheory.LFun.KGL w (n := b) ∧ ∀ i j, Valued.v (g.val i j - (1 : Matrix (Fin b) (Fin b) (w.adicCompletion E)) i j) ≤ WithZero.exp (-(k : ℤ))} then 1 else 0)) = c * (stTw a w Q₁ (fun y : GLw a w => if y ∈ GlobalTheory.LFun.KGL w (n := a) ∧ nrmL a w y ∈ {g : GLw a w | g ∈ GlobalTheory.LFun.KGL w (n := a) ∧ ∀ i j, Valued.v (g.val i j - (1 : Matrix (Fin a) (Fin a) (w.adicCompletion E)) i j) ≤ WithZero.exp (-(k : ℤ))} then 1 else 0) * stTw b w Q₂ (fun y : GLw b w => if y ∈ GlobalTheory.LFun.KGL w (n := b) ∧ nrmL b w y ∈ {g : GLw b w | g ∈ GlobalTheory.LFun.KGL w (n := b) ∧ ∀ i j, Valued.v (g.val i j - (1 : Matrix (Fin b) (Fin b) (w.adicCompletion E)) i j) ≤ WithZero.exp (-(k : ℤ))} then 1 else 0)) := by
  intro E _ _ _ w hw a b k Q₁ Q₂ c _ _ _ _ _
  rw [lev_eq a k, lev_eq b k]
  have e : (fun y : GLw a w × GLw b w => c * (if y.1 ∈ GlobalTheory.LFun.KGL w (n := a) ∧ nrmL a w y.1 ∈ {g : GLw a w | g ∈ GlobalTheory.LFun.KGL w (n := a) ∧ ∀ i j, Valued.v (g.val i j - (1 : Matrix (Fin a) (Fin a) (w.adicCompletion E)) i j) ≤ WithZero.exp (-(k : ℤ))} ∧ y.2 ∈ GlobalTheory.LFun.KGL w (n := b) ∧ nrmL b w y.2 ∈ {g : GLw b w | g ∈ GlobalTheory.LFun.KGL w (n := b) ∧ ∀ i j, Valued.v (g.val i j - (1 : Matrix (Fin b) (Fin b) (w.adicCompletion E)) i j) ≤ WithZero.exp (-(k : ℤ))} then (1 : ℂ) else 0)) =
      fun y => c * GlobalTheory.BCT.tens (lev a w k) (lev b w k) y := by
    funext y
    congr 1
    have h1 := congrFun (lev_eq (w := w) a k) y.1
    have h2 := congrFun (lev_eq (w := w) b k) y.2
    rw [GlobalTheory.BCT.tens, ← h1, ← h2, ite_zero_mul_ite_zero, mul_one]
    exact if_congr and_assoc.symm rfl rfl
  rw [e, stTw2_const_mul, GlobalTheory.BCT.StTwTens.stTw2_tens E a b w Q₁ Q₂ _ _ _ _ (lev_level hw a k) (lev_level hw b k)
    (lev_hecke hw a k) (lev_hecke hw b k)]

end GlobalTheory.BCT.StTwLevel
end
end

section

open GlobalTheory.IsoTriv

theorem _root_.GlobalTheory.T.constCoeffOperatorLinearSubstitution_proof : LinSt := by
  first | exact @GlobalTheory.IsoTriv.linSt_holds | exact GlobalTheory.IsoTriv.linSt_holds | (intros; apply GlobalTheory.IsoTriv.linSt_holds <;> assumption)
end

section

open NumberField PowerSeries Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.CohomologicalDescent Formalism.CohomologicalDescent.HeightDescentMinors Formalism.CohomologicalDescent.FrobeniusPeriodChange IsLocalRing GlobalTheory.WachPlace

theorem _root_.GlobalTheory.T.frobeniusMatrix_frame_at_primitiveRoot_factor : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (hA : CaseA K LL) (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (n : ℕ) (U : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → Fin n → ℤ) (γ : ((HW l).W K 1 LL hA.2.2).Gam) (b : Module.Basis (Fin n) (LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K))) ↥(((HW l).W K 1 LL hA.2.2).N T)) (N : Lat (ZMod (Module.finrank ℚ_[l] ↥(K0 K))) n ↥(OL LL)) (u c : ℤ_[l]) (ζ : ↥(OL LL)) (jj : PowerSeries ↥(OL LL) →+* PowerSeries ↥LL.1), GlobalTheory.AdmLoc.CrysWith ((D.loc l).PD K) ((HW l).W K 1 LL hA.2.2).emb T.ρ (fun i => Finset.univ.val.map (U i)) → (∀ i a, 0 ≤ U i a) → IsFrame ((HW l).W K 1 LL hA.2.2) T γ b N → (((HW l).W K 1 LL hA.2.2).χΓ γ : ↥(OL LL)) = algebraMap ℤ_[l] ↥(OL LL) u → u = 1 + (l : ℤ_[l]) * c → IsPrimitiveRoot ζ l → IsExpAt (OL LL).val.toRingHom ζ jj → ∀ i, ∃ G H : (Mx (PowerSeries ↥LL.1) n n)ˣ, (N.P i).map (fun y => jj (inc l ↥(OL LL) y)) = (G : Mx (PowerSeries ↥LL.1) n n) * Matrix.diagonal (fun a => (X : PowerSeries ↥LL.1) ^ (U i a).toNat) * (H : Mx (PowerSeries ↥LL.1) n n) ∧ ((1 + (X : PowerSeries ↥(OL LL)) • N.D i).map (fun y => jj (inc l ↥(OL LL) y))) * ((G : Mx (PowerSeries ↥LL.1) n n) * Matrix.diagonal (fun a => (X : PowerSeries ↥LL.1) ^ (U i a).toNat)).map (rescale ((OL LL).val.toRingHom (algebraMap ℤ_[l] ↥(OL LL) u))) = (G : Mx (PowerSeries ↥LL.1) n n) * Matrix.diagonal (fun a => (X : PowerSeries ↥LL.1) ^ (U i a).toNat) := by
  first | exact @GlobalTheory.WachRoots.frame_at_root | exact GlobalTheory.WachRoots.frame_at_root | (intros; apply GlobalTheory.WachRoots.frame_at_root <;> assumption)
end

section

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Module
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.DivisionValues Formalism.EigenvalueLevelCeiling Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links
open Formalism.IndefR.Cx Formalism.IndefR.FWT Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.FormTies GlobalTheory.BigOn
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.OnAtPlacesBase

section Free

variable {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K} {Df : DefSide Bs} {S : IndefData Df} {P : Type}
  [Group P] [Finite P] {c : OnConst}

theorem on_of_has_atPlaces (N : IndefNum Bs) (O : OnObj S P c) (CE : ℝ) (hRk : RankRows S)
    (hMk : LeafMackey O) (hSup : LeafSup O) (hProj : LeafProj O) (hC : TieCoord O)
    (hSp : LeafSpan O) (hS : LeafLemmaS O) (hT0 : HasIndexBound O) (hD : LeafData O) (hJ : GlobalTheory.TraceClassRank.RankAtPlaces O)
    (hI : LeafIdentity O) (h2 : LeafTW2 O) (h1 : HasTwistBound O)
    (hSh : LeafShareI O) (hIU : LeafIndexU O) (hBS : LeafBadShare O) (hUn : LeafUnip O)
    (hG : LeafDepthGood N O) (hR : LeafDepthRam N O) (h2p : LeafDepth2 N O) (hL : LeafDepthLevel N O)
    (hPg : LeafPage O) (hSz : LeafSizes O) (hX : LeafX O) (hBad : LeafBad O)
    (hE : HasExpBound N O) (hCE : c.CE ≤ CE) (tE1 : ErrorConstantMatchesDefinition N O CE) : ∃ err, ONwith S N err := by
  obtain ⟨Th1, a, r1, r2, de2, hT0⟩ := hT0
  obtain ⟨ε, h1⟩ := h1
  obtain ⟨-, Jp, hJS, hJE⟩ := hE
  exact ⟨_, GlobalTheory.TraceClassRank.on_core_atPlaces N
    ({ O with Th1 := Th1, a := a, r1 := r1, r2 := r2, de2 := de2, ε0 := ε, Jp := Jp } : OnObj S P c) CE hRk
    hMk hSup hProj hC hSp hS hT0 hD hJ hI h2 h1 hSh hIU hBS hUn hG hR h2p hL hPg hSz hX hBad hJS hJE hCE tE1⟩

end Free

theorem on_base_atPlaces : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (J : CoreJ D) [Algebra J.Q.c.F D.what₂.LL] (R : RealDat D A J.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (fw : FWTie J R κ v₀) (L : SizeData₂ D) (Pm : ParameterChoice' D L) (Tp : ParamsT D L Pm) (hK : DV.KapDef D) (EX : ErrX D) (r : TwoRuns J G) (c : OnConst) (O : OnObj ((R.toCx F).data F.cr false) (Mir R) c), IsRec Tp hK EX F fw r O → ∀ (s : ℕ) (N : IndefNum A.fam.base) (C : ℝ), A.fam.Ok s → R.grp_levels F → R.grp_chiW → R.IsModels → R.tup_mu_conj → R.thP_thG → R.LUnif → BaseLinks R F → TwistedRational R F (fun _ => 1) → RankRows ((R.toCx F).data F.cr false) → LeafLevelSq O (Res R) D.R.f → LeafYBound O → LeafSup O → LeafSpan O → LeafLemmaS O → HasIndexBound O → LeafData O → GlobalTheory.TraceClassRank.RankAtPlaces O → LeafIdentity O → LeafTW2 O → HasTwistBound O → LeafShareI O → LeafBadShare O → LeafDepthGood N O → LeafDepthRam N O → LeafDepth2 N O → LeafDepthLevel N O → LeafPage O → LeafSizes O → LeafX O → LeafBad O → HasExpBound N O → c.CE ≤ C → ErrorConstantMatchesDefinition N O C → ∃ err, ONwith ((R.toCx F).data F.cr false) N err := by
  intro D G _ _ Pl0 T0 A J _ R F κ v₀ fw L Pm Tp hK EX r c O hO s N C hOk h1 h2 hM hμ hth hU hB hrat hRk hSq hY hSup hSp hS hT0
    hD hJ hI hT2 hT1 hSh hBS hDG hDR hD2 hDL hPg hSz hX hBad hE hCE tE1
  classical
  obtain ⟨hc, hinj, ht⟩ := hO.tied
  obtain ⟨st, hd⟩ := hO.depth
  have hN : TieLevelNum O (rankPred D.R) D.R.f := by
    letI := st
    letI := hostAlg D
    refine ⟨hd.f_eq, ?_⟩
    rw [hO.rr_eq, OntoChain.rank_eq]
    push_cast
    rfl
  obtain ⟨w, hw⟩ := GlobalTheory.BigOnBase.exists_tieCoord_base ht (fun g hg => by
    obtain ⟨u, -, e⟩ := (mem_base_iff h1 g).1 hg
    exact ⟨u, e⟩) hOk h1 h2 hM.HV hM.jV hM.HW hμ (phasedLift_one hth) hU hB hrat hI hT2
  obtain ⟨tU, hMk, hP⟩ := level_of_tied ht hOk.irr h1
  exact on_of_has_atPlaces N (withCoord O w) C hRk hMk hSup hP hw hSp hS hT0 hD hJ hI hT2 hT1 hSh
    (leafIndexU_of O D.R.f (mirab_levelGroups _ _) hSq hY tU hN) hBS (leafUnip_of O D.R.f (mirab_levelGroups _ _) hSq tU hN)
    hDG hDR hD2 hDL hPg hSz hX hBad hE hCE tE1

end GlobalTheory.OnAtPlacesBase

end
end

section

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory GlobalTheory.DeRham GlobalTheory.Cris
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_tangent_frame_of_framedPoint_commRing : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) {A : Over (Sp S)} [GrpObj A] {π : A.left ⟶ Xo.univ.t.G.left}, IsGrpPullback A Xo.univ.t.G y.x π → ∀ (a : OAct (𝓞 E) A), (∀ z, (a.act z).left ≫ π = π ≫ (Xo.univ.t.act.act z).left) → ∃ ub : ∀ σ : E →+* ℂ, Fin (Dw.mult σ) → (epsR S ⟶ A), (∀ σ k, (ub σ k).left ≫ π = y.u σ k) ∧ (∀ σ k, IsTangent (ub σ k)) ∧ (∀ σ k z, ub σ k ≫ a.act z = GlobalTheory.GrpTangent.epsScale (algebraMap c.F S (embK c σ z)) ≫ ub σ k) ∧ ∀ σ (w : epsR S ⟶ A), IsTangent w → (∀ z, w ≫ a.act z = GlobalTheory.GrpTangent.epsScale (algebraMap c.F S (embK c σ z)) ≫ w) → ∃ cf, IsLieComb cf (ub σ) w := by
  first | exact @GlobalTheory.KSExist.exists_frame_of_isGrpPullback_ring | exact GlobalTheory.KSExist.exists_frame_of_isGrpPullback_ring | (intros; apply GlobalTheory.KSExist.exists_frame_of_isGrpPullback_ring <;> assumption)
end

section

theorem GlobalTheory.FourClauses.irreducibleAdmissibleGL : GlobalTheory.Published.IrreducibleAdmissibleGL :=
  GlobalTheory.FourClauses.adm GlobalTheory.CompanionTheory.Published.bernsteinZelevinskyFiniteness
end

section

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory GlobalTheory.DeRham GlobalTheory.Cris
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.grp_pullback_basis_lift_compatible : GlobalTheory.Published.AbelianDeRham → ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) {A : Over (Sp S)} [GrpObj A] {π : A.left ⟶ Xo.univ.t.G.left}, IsGrpPullback A Xo.univ.t.G y.x π → ∀ (ub : ∀ σ : E →+* ℂ, Fin (Dw.mult σ) → (epsR S ⟶ A)), (∀ σ k, (ub σ k).left ≫ π = y.u σ k) → ∀ (hb : (Σ σ : E →+* ℂ, Fin (Dw.mult σ)) → HdR A), (∀ k, IsLieImage (hb k) (ub k.1 k.2)) → Submodule.span S (Set.range hb) ⊔ Fil A = ⊤ ∧ LinearIndependent S (fun k => (Submodule.Quotient.mk (hb k) : HdR A ⧸ Fil A)) := by
  first | exact @GlobalTheory.LieBasisRing.lifts_basis_mod_fil | exact GlobalTheory.LieBasisRing.lifts_basis_mod_fil | (intros; apply GlobalTheory.LieBasisRing.lifts_basis_mod_fil <;> assumption)
end
