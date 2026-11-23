module

public import Formalism.LocalToGlobal.LatticeGeometry.GeometryDefinitions.Bundle001
public import Formalism.QuotientMetricDivisors.Statement
public import Formalism.SharpRestriction.GlobalSchurBounds.FlipTwoThree
public import Formalism.LocalToGlobal.GlobalTheory.GL4.PMuFrames
public import Formalism.LocalToGlobal.HermitianColumns.InLocalDiscriminantKernel
public import Formalism.LocalToGlobal.LatticeGeometry.GeometryDefinitions.ExistsFrameOfSig
public import Formalism.LocalToGlobal.LatticeGeometry.GeometryDefinitions.SingleFacts
public import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.IdxChange
public import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.LcvBasis
public import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.LocBasis
public import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.Bundle002
public import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.RatHerm
public import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.ReductionSecondStep
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.ValBasic
import Formalism.SizeWindowBrackets.ChainSlopeWindows.TruncatedLatticeHolds
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
import Formalism.LocalToGlobal.Columns.CoefficientsModP.WeTransposeWordTransposeWord
import Formalism.LocalToGlobal.GlobalTheory.Bundle001

@[expose] public section

section

open Module NumberField IsDedekindDomain
open scoped Matrix

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.TraceIntegrality

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.HN Formalism.BasicNotions.SkeletonIndexLemmas Formalism.L2.DIV Formalism.L2.Col Formalism.L2.GlobalTheoryTheory.HLatOps
open Formalism.LFunctionChainParameters.slopeLatticeData (FinPl)

section Gen

variable {K : Type} [Field K] [NumberField K] {V W : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
  [AddCommGroup W] [Module K W]
  {Cl : Type} [Fintype Cl] [DecidableEq Cl] {J0 : Type} [Fintype J0] [DecidableEq J0]

def sumBasis (coE : V ≃ₗ[K] (Cl → W)) (BK : Basis J0 K W) : Basis (J0 × Cl) K V :=
  ((Pi.basis fun _ : Cl => BK).map coE.symm).reindex ((Equiv.sigmaEquivProd Cl J0).trans (Equiv.prodComm Cl J0))

theorem sumBasis_apply (coE : V ≃ₗ[K] (Cl → W)) (BK : Basis J0 K W) (i : J0) (c : Cl) :
    sumBasis coE BK (i, c) = coE.symm (Pi.single c (BK i)) := by
  simp [sumBasis, Basis.reindex_apply, Basis.map_apply, Pi.basis_apply, Equiv.prodComm, Equiv.sigmaEquivProd]

theorem famOf_sumBasis (coE : V ≃ₗ[K] (Cl → W)) (BK : Basis J0 K W) (φ : Cl → Module.End K W) :
    famOf (sumBasis coE BK) (Matrix.blockDiagonal fun c => LinearMap.toMatrix BK BK (φ c)) =
      fun j : J0 × Cl => coE.symm (Pi.single j.2 (φ j.2 (BK j.1))) := by
  funext j
  obtain ⟨i, c⟩ := j
  have hφ : φ c (BK i) = ∑ i', LinearMap.toMatrix BK BK (φ c) i' i • BK i' := by
    simp [LinearMap.toMatrix_apply, BK.sum_repr]
  have hs : ∀ (f : J0 → W), Pi.single (M := fun _ : Cl => W) c (∑ i', f i') = ∑ i', Pi.single c (f i') := by
    intro f
    exact (map_sum (LinearMap.single K (fun _ : Cl => W) c) f Finset.univ)
  simp only [famOf, sumBasis_apply]
  rw [Fintype.sum_prod_type]
  simp only [Matrix.blockDiagonal_apply, ite_smul, zero_smul]
  simp only [Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true]

  rw [hφ, hs, map_sum]
  simp only [Pi.single_smul, map_smul, sumBasis_apply]

end Gen

section Sum

variable {K : Type} [Field K] [NumberField K] [StarRing K] [_root_.NumberField.IsTotallyComplex K]
  {ι : Type} [Fintype ι] {W : Type} [AddCommGroup W] [Module K W]
  {Cl : Type} [Fintype Cl] [DecidableEq Cl] {J0 : Type} [Fintype J0] [DecidableEq J0]

theorem conj_mul_real_mul (z : ℂ) (r : ℝ) : starRingEnd ℂ z * (r : ℂ) * z = ((Complex.normSq z * r : ℝ) : ℂ) := by
  apply Complex.ext <;> simp [Complex.normSq_apply] <;> ring

def ownFrame (Q : HLat K) {n : ℕ} (eQ : Q.ι ≃ Fin n) (g : FinPl K → Matrix (Fin n) (Fin n) K) (hg : ∀ p, (g p).det ≠ 0)
    (hloc : ∀ p, localization₂ (toH p).asIdeal Q.L =
      localization₂ (toH p).asIdeal (latOf (K := K) fun a' : Fin n => ∑ i, g p i a' • Q.b (eQ.symm i))) : FrameData Q Q.ι where
  e := Q.b
  Γ := fun p => (g p).submatrix eQ eQ
  det_ne := fun p => by rw [Matrix.det_submatrix_equiv_self]; exact hg p
  loc := fun p => by
    rw [hloc p]
    congr 1
    unfold latOf
    congr 1
    have h : famOf Q.b ((g p).submatrix eQ eQ) = (fun a' : Fin n => ∑ i, g p i a' • Q.b (eQ.symm i)) ∘ eQ := by
      funext i'
      unfold famOf
      simp only [Function.comp_apply, Matrix.submatrix_apply]
      exact Fintype.sum_equiv eQ _ _ fun k => by simp
    rw [h, EquivLike.range_comp]

private theorem det_gramJ_self_basis_eq_normSq_det_inv (Q : HLat K) (v : InfinitePlace K) :
    (gramJ Q (⇑Q.b) v).det = ((Complex.normSq ((Q.X v)⁻¹).det : ℝ) : ℂ) := by
  have h : gramJ Q (⇑Q.b) v = ((Q.X v)⁻¹)ᴴ * (Q.X v)⁻¹ := by
    ext a c
    simp [gramJ, majAt, fcoord, vecAt, Matrix.mul_apply, Basis.repr_self, Finsupp.single_apply, Matrix.mulVec, dotProduct]
  rw [h, Matrix.det_mul, Matrix.det_conjTranspose]
  have := conj_mul_real_mul ((Q.X v)⁻¹).det 1
  simpa [Complex.star_def] using this

theorem mu_sum_functor [Nonempty J0] [Nonempty Cl] (A : HLat K) (hA : A.Good) (coE : A.V ≃ₗ[K] (Cl → W)) (BK : Basis J0 K W)
    (Q : Cl → ι → HLat K) (hQ : ∀ c τ, (Q c τ).Good) (n : ℕ) (hn : 0 < n) (eQ : ∀ c τ, (Q c τ).ι ≃ Fin n) (a : ι → ℤ)
    (g : FinPl K → Cl → ι → Matrix (Fin n) (Fin n) K) (hg : ∀ p c τ, (g p c τ).det ≠ 0)
    (hQloc : ∀ p c τ, localization₂ (toH p).asIdeal (Q c τ).L =
      localization₂ (toH p).asIdeal (latOf (K := K) fun a' : Fin n => ∑ i, g p c τ i a' • (Q c τ).b ((eQ c τ).symm i)))
    (φ : FinPl K → Cl → Module.End K W)
    (hφ : ∀ p c, LinearMap.det (φ p c) ^ n = ∏ τ, (g p c τ).det ^ a τ)
    (hAloc : ∀ p, localization₂ (toH p).asIdeal A.L =
      localization₂ (toH p).asIdeal (latOf (K := K) fun j : J0 × Cl => coE.symm (Pi.single j.2 (φ p j.2 (BK j.1)))))
    (G0 : Matrix J0 J0 ℝ) (N : InfinitePlace K → Cl → Matrix J0 J0 ℂ)
    (hN : ∀ v c, (N v c).det ^ n = ∏ τ, (((Q c τ).X v)⁻¹).det ^ a τ)
    (hGram : ∀ v (i i' : J0) (c c' : Cl),
      majAt A.b A.X v (coE.symm (Pi.single c (BK i))) (coE.symm (Pi.single c' (BK i'))) =
        if c = c' then ((N v c)ᴴ * G0.map Complex.ofReal * N v c) i i' else 0) :
    ((Fintype.card J0 : ℝ) * Fintype.card Cl) * A.mu =
      -((Fintype.card Cl : ℝ) * Real.log G0.det) + ∑ c, ∑ τ, (a τ : ℝ) * (Q c τ).mu := by
  have hne : ∀ p c, LinearMap.det (φ p c) ≠ 0 := by
    intro p c h
    have h1 := hφ p c
    rw [h, zero_pow hn.ne'] at h1
    exact (Finset.prod_ne_zero_iff.mpr fun τ _ => zpow_ne_zero _ (hg p c τ)) h1.symm
  let FA : FrameData A (J0 × Cl) :=
    { e := sumBasis coE BK
      Γ := fun p => Matrix.blockDiagonal fun c => LinearMap.toMatrix BK BK (φ p c)
      det_ne := fun p => by
        rw [Matrix.det_blockDiagonal]
        exact Finset.prod_ne_zero_iff.mpr fun c _ => by rw [LinearMap.det_toMatrix]; exact hne p c
      loc := fun p => by rw [hAloc p, famOf_sumBasis] }
  let FQ : (s : Cl × ι) → FrameData (Q s.1 s.2) (Q s.1 s.2).ι := fun s =>
    ownFrame (Q s.1 s.2) (eQ s.1 s.2) (fun p => g p s.1 s.2) (fun p => hg p s.1 s.2) (fun p => hQloc p s.1 s.2)
  have hdet : ∀ v c, ((N v c)ᴴ * G0.map Complex.ofReal * N v c).det =
      ((Complex.normSq (N v c).det * G0.det : ℝ) : ℂ) := by
    intro v c
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose, ← conj_mul_real_mul]
    have hm : (G0.map Complex.ofReal).det = (G0.det : ℂ) := by
      rw [show G0.map Complex.ofReal = Complex.ofRealHom.mapMatrix G0 from rfl, ← RingHom.map_det]
      rfl
    rw [hm, Complex.star_def]
  have hgramA : ∀ v, (gramJ A (⇑FA.e) v).det.re =
      (∏ c, Complex.normSq (N v c).det) * G0.det ^ Fintype.card Cl := by
    intro v
    have h1 : gramJ A (⇑FA.e) v = Matrix.blockDiagonal fun c => (N v c)ᴴ * G0.map Complex.ofReal * N v c := by
      ext ⟨i, c⟩ ⟨i', c'⟩
      simp only [gramJ, Matrix.of_apply, Matrix.blockDiagonal_apply]
      show majAt A.b A.X v (sumBasis coE BK (i, c)) (sumBasis coE BK (i', c')) = _
      rw [sumBasis_apply, sumBasis_apply, hGram]
    rw [h1, Matrix.det_blockDiagonal]
    simp_rw [hdet]
    rw [← Complex.ofReal_prod, Complex.ofReal_re, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]
  have hgramQ : ∀ (s : Cl × ι) v, (gramJ (Q s.1 s.2) (⇑(FQ s).e) v).det.re =
      Complex.normSq ((Q s.1 s.2).X v)⁻¹.det := by
    intro s v
    rw [show (FQ s).e = (Q s.1 s.2).b from rfl, det_gramJ_self_basis_eq_normSq_det_inv, Complex.ofReal_re]
  have hpos : 0 < G0.det ^ Fintype.card Cl := by
    obtain ⟨v⟩ : Nonempty (InfinitePlace K) := inferInstance
    have h := (mu_of_frames A hA FA).1 v
    rw [hgramA] at h
    have h0 : 0 ≤ ∏ c, Complex.normSq (N v c).det := Finset.prod_nonneg fun c _ => Complex.normSq_nonneg _
    rcases lt_or_ge 0 (G0.det ^ Fintype.card Cl) with h2 | h2
    · exact h2
    · exact absurd h (not_lt.mpr (mul_nonpos_of_nonneg_of_nonpos h0 h2))
  have key := mu_functor A hA FA (fun s : Cl × ι => Q s.1 s.2) (fun s => hQ s.1 s.2) n hn
    (fun s => (Fintype.card_congr (eQ s.1 s.2)).trans (Fintype.card_fin n)) FQ (fun s => a s.2)
    (G0.det ^ Fintype.card Cl) hpos ?_ ?_
  · rw [Fintype.card_prod, Real.log_pow, Fintype.sum_prod_type] at key
    push_cast at key
    linarith [key]
  · intro p
    show (Matrix.blockDiagonal fun c => LinearMap.toMatrix BK BK (φ p c)).det ^ n =
      ∏ s : Cl × ι, ((g p s.1 s.2).submatrix (eQ s.1 s.2) (eQ s.1 s.2)).det ^ a s.2
    rw [Matrix.det_blockDiagonal, ← Finset.prod_pow, Fintype.prod_prod_type]
    refine Finset.prod_congr rfl fun c _ => ?_
    rw [LinearMap.det_toMatrix, hφ]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [Matrix.det_submatrix_equiv_self]
  · intro v
    rw [hgramA]
    simp_rw [hgramQ]
    rw [Fintype.prod_prod_type, mul_pow, mul_comm, ← Finset.prod_pow]
    congr 1
    refine Finset.prod_congr rfl fun c _ => ?_
    rw [← map_pow, hN, map_prod]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [map_zpow₀]

end Sum

end Formalism.L2.GlobalTheoryTheory.TraceIntegrality

end
end

section

open Module NumberField IsDedekindDomain
open scoped Matrix

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.TraceIntegrality

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.HN Formalism.MainNotions.flipTwoThree Formalism.L2.Herm Formalism.L2.Geo.Def Formalism.L2.Geo.Def.G1
open Formalism.LFunctionChainParameters.slopeLatticeData (FinPl)

def finPlEquiv (K : Type) [Field K] [NumberField K] : FinPl K ≃ HeightOneSpectrum (𝓞 K) where
  toFun := toH
  invFun w := ⟨w.asIdeal, w.isMaximal⟩
  left_inv _ := rfl
  right_inv _ := rfl

section E

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]

private lemma hform_crd_lemma (S : HSpace E) (a b : S.V) :
    Formalism.DivisionValues.hform S.gram (crd S a) (crd S b) = S.hT a b := by
  conv_rhs => rw [← S.frame.sum_equivFun a, ← S.frame.sum_equivFun b]

  simp only [Formalism.DivisionValues.hform, Matrix.toLinearMapₛₗ₂'_apply, map_sum, LinearMap.sum_apply,
  LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, crd, HSpace.gram, RingHom.id_apply,
  Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem mem_dual_crdLat (hc : CMData F E) (S : HSpace E) (L : Submodule (𝓞 E) S.V) (x : S.V) :
    crd S x ∈ Formalism.HermitianLatticesTheory.dual (Formalism.DivisionValues.hform S.gram) (crdLat S L) ↔ x ∈ dualSub S L := by
  unfold dualSub
  simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap,
    LinearMap.restrictScalars_apply, Submodule.mem_one, crdLat, Submodule.mem_map,
    forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, LinearEquiv.coe_coe,
    LinearMap.coe_restrictScalars, hform_crd_lemma, Submodule.mem_mk, AddSubmonoid.mem_mk,
    AddSubsemigroup.mem_mk, Set.mem_setOf_eq, RingHom.mem_range]
  exact Iff.rfl

theorem relIndex_crdLat (hc : CMData F E) (S : HSpace E) (L : Submodule (𝓞 E) S.V) :
    (crdLat S L).toAddSubgroup.relIndex (Formalism.HermitianLatticesTheory.dual (Formalism.DivisionValues.hform S.gram) (crdLat S L)).toAddSubgroup =
      L.toAddSubgroup.relIndex (dualSub S L) := by
  let f : S.V →+ (Fin S.rank → E) := (crd S).toAddEquiv.toAddMonoidHom
  have hf : Function.Injective f := (crd S).injective
  have hL : (crdLat S L).toAddSubgroup = L.toAddSubgroup.map f := by
    ext z
    exact Iff.rfl
  have hD : (Formalism.HermitianLatticesTheory.dual (Formalism.DivisionValues.hform S.gram) (crdLat S L)).toAddSubgroup =
      (dualSub S L).map f := by
    ext z
    obtain ⟨x, rfl⟩ := (crd S).surjective z
    rw [Submodule.mem_toAddSubgroup, mem_dual_crdLat hc S L x]
    constructor
    · intro h
      exact ⟨x, h, rfl⟩
    · rintro ⟨y, hy, hyx⟩
      exact hf hyx ▸ hy
  rw [hD, hL, ← AddSubgroup.relIndex_comap, AddSubgroup.comap_map_eq_self_of_injective hf]

variable [_root_.NumberField.IsTotallyComplex E]

open Formalism.DivisionValues Formalism.DivisionValues.RationalHermitianForm in
private theorem lcv_eq_neg_sum_jw {d : ℕ} {E₀ : Subfield E} (hCM : IsCMSub E₀)
    {H : Matrix (Fin d) (Fin d) E} {X : InfinitePlace E → Matrix (Fin d) (Fin d) ℂ}
    (hR : IsRatHerm E₀ H X) (M : Submodule (𝓞 E) (Fin d → E))
    (hM : Submodule.IsFullLattice E M) :
    lcv X M = -∑ᶠ w : HeightOneSpectrum (𝓞 E), lw w * (jw H w M : ℝ) := by
  classical
  let e (i : Fin d) : Fin d → E := Pi.single i 1
  let N := Submodule.span (𝓞 E) (Set.range e)
  have he : LinearIndependent E e := StepBAux.std_li d
  obtain ⟨hfin, hlcv⟩ := covolume_via_basis E d X (fun v => (hR.2 v).1) M hM e he
  have hdet := det_ne_zero hR
  obtain ⟨hfinDet, hprod⟩ := prod_formula' E H.det hdet
  have hlog (v : InfinitePlace E) : Real.log (gram X v e).det.re = Real.log ‖v.embedding H.det‖ := by
    have heMat : StepBAux.fmat v.embedding e = 1 := by
      ext i j
      simp [StepBAux.fmat, e, Pi.single_apply, Matrix.one_apply]
    have hgram : (gram X v e).det = v.embedding H.det := by
      rw [StepBAux.gram_eq_fmat, heMat, Matrix.conjTranspose_one, one_mul, mul_one,
        StepBAux.met, (hR.2 v).2, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    have hnorm : v.embedding H.det = (Complex.normSq ((X v)⁻¹.det) : ℂ) := by
      rw [emb_det hR v, Complex.normSq_eq_conj_mul_self, starRingEnd_apply]
    rw [hgram, hnorm, Complex.ofReal_re, Complex.norm_real, Real.norm_of_nonneg (Complex.normSq_nonneg _)]
  let a (w : HeightOneSpectrum (𝓞 E)) : ℝ := lw w * (idx w N M : ℝ)
  let c (w : HeightOneSpectrum (𝓞 E)) : ℝ := lw w * (vw w H.det : ℝ)
  have hpt (w : HeightOneSpectrum (𝓞 E)) : lw w * (jw H w M : ℝ) =
      -(a w + a (conjPl w) + c w) := by
    obtain ⟨f, hf⟩ := semilocal_basis_exists E d M hM w
    have hloc : IsLocBasis M w (fun i => ∑ k, (Matrix.of f)ᵀ k i • e k) := by
      simpa only [e, expand_std] using hf
    obtain ⟨i₁, i₂⟩ := index_change_formula E d M hM.toIsLattice e he w _ hloc
    have hj := jwGram_of index_change_formula E E₀ hCM d H X hR M hM.toIsLattice w f hf
    have hfdet := det_of_ne_zero hf.1
    have ⟨hmul, hstar, hlw, _⟩ := valuation_basic_properties E w
    rw [gramR_eq_std, hmul _ _ (mul_ne_zero (star_ne_zero.mpr hfdet) hfdet) hdet,
      hmul _ _ (star_ne_zero.mpr hfdet) hfdet, hstar] at hj
    dsimp only [a, c, N]
    rw [hj, i₁, i₂, hlw]
    push_cast
    ring
  have ha : (Function.support a).Finite := hfin
  have ha' : (Function.support (a ∘ conjPl)).Finite := by
    rw [Function.support_comp_eq_preimage]
    exact ha.preimage (Function.Involutive.injective ValuationRepresentative.conjPl_conjPl).injOn
  have haa' := (ha.union ha').subset (Function.support_add a (a ∘ conjPl))
  have hfun : (fun w => lw w * (jw H w M : ℝ)) = fun w => -(a w + (a ∘ conjPl) w + c w) :=
    funext hpt
  have hconj : finsum (a ∘ conjPl) = finsum a := finite_sum_conjugation E a
  rw [hfun, finsum_neg_distrib, neg_neg, finsum_add_distrib haa' hfinDet,
    finsum_add_distrib ha ha', hconj, hlcv]
  simp only [hlog]
  rw [hprod]
  change (∑ᶠ w, c w) + 2 * (∑ᶠ w, a w) = (∑ᶠ w, a w) + (∑ᶠ w, a w) + (∑ᶠ w, c w)
  ring

theorem eLat_mu (hc : CMData F E) (S : HSpace E) (hsig : S.SigOK) (hpos : S.IsPosDef) (hn : 0 < S.rank)
    (L : Submodule (𝓞 E) S.V) (hL : Submodule.IsFullLattice E L) (q : ℕ) (hq : q ≠ 0) (hLT : LatT S q L) :
    muDef (Pi.basisFun E (Fin S.rank)) (fun v => frameOf (S.gram.map v.embedding)) (crdLat S L) =
      -Real.log q / ((finrank ℚ E : ℝ) * S.rank) := by
  have hspan : Submodule.span E (crdLat S L : Set (Fin S.rank → E)) = ⊤ := by
    change Submodule.span E ((crd S).toLinearMap '' (L : Set S.V)) = ⊤
    rw [← Submodule.map_span (crd S).toLinearMap, hL.span_eq_top, Submodule.map_top,
      LinearMap.range_eq_top.mpr (crd S).surjective]
  have hM : Submodule.IsFullLattice E (crdLat S L) :=
    { toIsLattice := crdLat_lattice S L hL, span_eq_top := hspan }
  have hY : ∀ v : InfinitePlace E, IsUnit (frameOf (S.gram.map v.embedding)).det ∧
      ((frameOf (S.gram.map v.embedding))⁻¹).conjTranspose * (frameOf (S.gram.map v.embedding))⁻¹ = S.gram.map v.embedding := by
    intro v
    apply frameOf_spec
    apply exists_frame_of_sig _ S.rank
    have h1 := hsig v.embedding
    rwa [hpos v.embedding] at h1
  have hCM : Formalism.DivisionValues.IsCMSub (⊤ : Subfield E) := fun σ a _ => hc.cmUnram.2.1 σ a
  have hRat : Formalism.DivisionValues.IsRatHerm (⊤ : Subfield E) S.gram (fun v => frameOf (S.gram.map v.embedding)) :=
    ⟨fun _ _ => Subfield.mem_top _, hY⟩
  have h2 := lcv_eq_neg_sum_jw hCM hRat _ hM
  set M := crdLat S L with hMdef
  set Md := Formalism.HermitianLatticesTheory.dual (Formalism.DivisionValues.hform S.gram) M with hMd
  have hle : M ≤ Md := by
    intro z hz
    obtain ⟨x, rfl⟩ := (crd S).surjective z
    exact (mem_dual_crdLat hc S L x).2 (hLT.1 x ((crdLat_mem S L x).1 hz))
  have hidx : M.toAddSubgroup.relIndex Md.toAddSubgroup = q := by
    rw [hMd, hMdef, relIndex_crdLat hc S L]; exact hLT.2
  have hjw : ∀ w : HeightOneSpectrum (𝓞 E), (Formalism.DivisionValues.jw S.gram w M : ℝ) = -(Formalism.HermitianLatticesTheory.locLen w.asIdeal Md M : ℝ) := by
    intro w
    unfold Formalism.DivisionValues.jw Formalism.HermitianLatticesTheory.jIdx Formalism.HermitianLatticesTheory.lidx
    rw [← hMd, inf_eq_left.2 hle]
    have h0 : Formalism.HermitianLatticesTheory.locLen w.asIdeal M M = 0 := by
      unfold Formalism.HermitianLatticesTheory.locLen
      rw [Submodule.comap_subtype_self]
      simp
    rw [h0]
    push_cast
    ring
  obtain ⟨-, -, h3⟩ := Formalism.LFunctionChainParameters.LLcv.index_local_length E (Fin S.rank → E) Md M hle (by rw [hidx]; exact hq)
  rw [hidx] at h3
  have hnE : (0 : ℝ) < (finrank ℚ E : ℝ) := by exact_mod_cast (Module.finrank_pos : 0 < finrank ℚ E)
  have h4 : (∑ᶠ w : HeightOneSpectrum (𝓞 E), Formalism.DivisionValues.lw w * (Formalism.DivisionValues.jw S.gram w M : ℝ)) = -(Real.log q / (finrank ℚ E : ℝ)) := by
    rw [h3, ← finsum_comp_equiv (finPlEquiv E), div_eq_mul_inv, ← mul_neg, finsum_mul]
    refine finsum_congr fun p => ?_
    rw [hjw]
    unfold Formalism.DivisionValues.lw
    show Real.log (Ideal.absNorm p.1 : ℝ) / (finrank ℚ E : ℝ) * -(Formalism.HermitianLatticesTheory.locLen (toH p).asIdeal Md M : ℝ) =
      Real.log (Ideal.absNorm p.1 : ℝ) * (Formalism.HermitianLatticesTheory.locLen (toH p).asIdeal Md M : ℝ) * -(finrank ℚ E : ℝ)⁻¹
    ring
  rw [h4, neg_neg] at h2
  have hrk : rkK M = S.rank := by
    show finrank E (Submodule.span E (M : Set (Fin S.rank → E))) = _
    rw [hMdef, hspan]
    simp
  have h5 := lcv_eq_mu hn _ (fun v => (hY v).1) M hM.fg hrk
  rw [h2] at h5
  have hr : (0 : ℝ) < (S.rank : ℝ) := by exact_mod_cast hn
  field_simp
  field_simp at h5
  linarith

end E

end Formalism.L2.GlobalTheoryTheory.TraceIntegrality

end
end
