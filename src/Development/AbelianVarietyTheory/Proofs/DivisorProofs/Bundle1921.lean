module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.UnitaryConjugation
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsNotRelZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1887
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1888
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceTensorProductFiniteExtension
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.DecayZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle689
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1330
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1891
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle044
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle137
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle152
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle045
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1344
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle018
import Formalism.LocalToGlobal.IndefiniteReal.Bundle009
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1910
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1907
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1199

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA skewGram blkU conjU UB)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple UAt ratU mat Acts SInf)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.SquareFlipReach

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

def rowE (t : T) (w : Pl D.host.E) (i j : Fin D.R.m) :
    Fin ((locGrid G t w).rank (i + 1, j + 1)) ≃ Fin (spW G i j).rank :=
  finCongr (rank_vertex G t w (X := ((i : ℕ) + 1, (j : ℕ) + 1)) ⟨i.2, j.2⟩)

def colE (t : T) (w : Pl D.host.E) {i j : Fin D.R.m} (e : Num G i j) :
    (locGrid G t w).Cols i j ≃ Fin ((spW G i j).rank + (spW₁ G i j).rank) :=
  (Equiv.sumCongr (finCongr (rank_vertex G t w (X := ((i : ℕ), (j : ℕ) + 1)) ⟨i.2.le, j.2⟩))
    (finCongr (rank_vertex G t w (X := ((i : ℕ) + 1, (j : ℕ))) ⟨i.2, j.2.le⟩))).trans e

def trA (t : T) {w : Pl D.host.E} {v : Pl D.host.F} (hv : w.under (𝓞 D.host.F) = v) {i j : Fin D.R.m} (e : Num G i j)
    (Z : Matrix (Fin (spW G i j).rank) (Fin ((spW G i j).rank + (spW₁ G i j).rank)) (Fv D.host.F v)) :
    Matrix (Fin ((locGrid G t w).rank (i + 1, j + 1))) ((locGrid G t w).Cols i j) (Kw w) :=
  Matrix.of fun r c => GlobalTheory.LFun.complMap hv (Z (rowE t w i j r) (colE t w e c))

def sqCore (W : G.Weil) (t : T) (i j : ℕ) (w : Pl D.host.E) (n : ℕ)
    (Φ : Matrix (Fin ((locGrid G t w).rank (i, j))) ((locGrid G t w).Cols i j) (Kw w) → ℂ) :
    Matrix (Fin ((locGrid G t w).rank (i + 1, j + 1))) ((locGrid G t w).Cols i j) (Kw w) → ℂ :=
  phiA (haarVol ((givenLevel G t w (i, j)).map invT)) (stdSplit ((locGrid G t w).rank_square i j)) ((locGrid G t w).nu i j)
    (unifAt w) n (blockLat (unifAt w) n (Assignment.one.block _ _))
    (fourierSum (psiAt W w) (unifAt w) n (Assignment.one.block _ _) Φ)

theorem flipAt_eq (W : G.Weil) (t : T) (i j : ℕ) (w : Pl D.host.E) (n : ℕ)
    (Φ : Matrix (Fin ((locGrid G t w).rank (i, j))) ((locGrid G t w).Cols i j) (Kw w) → ℂ) :
    flipAt W t i j w n Φ = invFourierSum (psiAt W w)⁻¹ (unifAt w) n (Assignment.one.block _ _)ᶜ (sqCore W t i j w n Φ) := rfl

end GlobalTheory.SquareFlipReach

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw


theorem _root_.GlobalTheory.T.alpha_div_beta_ramified_at_level : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (_hL : L.Is μ₀) (t : T)
    (i j : Fin D.R.m) (w : HeightOneSpectrum (𝓞 D.host.E)) (P : HeightOneSpectrum (𝓞 D.host.E)), P ∈ L.Q t →
      P.under (𝓞 D.host.F) = w.under (𝓞 D.host.F) → w.under (𝓞 D.host.F) ∉ G.pl.S0 →
      ¬ GlobalTheory.LFun.UnrAt (F := D.host.F) (E := D.host.E) (alpha G t i j / beta G i j) w := by
  first | exact @GlobalTheory.TwistRam.not_unrAt_alpha_div_beta | exact GlobalTheory.TwistRam.not_unrAt_alpha_div_beta | (intros; apply GlobalTheory.TwistRam.not_unrAt_alpha_div_beta <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw


theorem _root_.GlobalTheory.T.not_unrAt_of_under_eq_v0 : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (_hL : L.Is μ₀) (t : T)
    (i j : Fin D.R.m) (w : HeightOneSpectrum (𝓞 D.host.E)), w.under (𝓞 D.host.F) = G.pl.v0 →
      ¬ GlobalTheory.LFun.UnrAt (F := D.host.F) (E := D.host.E) (alpha G t i j / beta G i j) w := by
  first | exact @GlobalTheory.ThetaGridRamifiedOverBasePlace.thetaGridCharacterQuotient_not_unramified_over_basePlace | exact GlobalTheory.ThetaGridRamifiedOverBasePlace.thetaGridCharacterQuotient_not_unramified_over_basePlace | (intros; apply GlobalTheory.ThetaGridRamifiedOverBasePlace.thetaGridCharacterQuotient_not_unramified_over_basePlace <;> assumption)
end

section

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.SiegelValGood

open scoped TensorProduct

theorem det_ne_zero_of_hasSig {n : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} {r s : ℕ} (h : HasSig M r s) : M.det ≠ 0 := by
  obtain ⟨hn, A, hA⟩ := h
  let e : Fin r ⊕ Fin s ≃ Fin n := finSumFinEquiv.trans (finCongr hn)
  let A' : Matrix (Fin n) (Fin n) ℂ := A.submatrix id e.symm
  have key : A'ᵀ * M * A'.map star =
      (Matrix.fromBlocks 1 0 0 (-1) : Matrix (Fin r ⊕ Fin s) (Fin r ⊕ Fin s) ℂ).submatrix e.symm e.symm := by
    rw [← hA]
    ext i j
    simp [A', Matrix.mul_apply]
  have h2 := congrArg Matrix.det key
  rw [Matrix.det_submatrix_equiv_self, Matrix.det_mul, Matrix.det_mul, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one,
    Matrix.det_neg, Matrix.det_one] at h2
  intro h0
  rw [h0, mul_zero, zero_mul] at h2
  simp at h2
  exact absurd h2.symm (pow_ne_zero _ (neg_ne_zero.2 one_ne_zero))

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem det_mul_cA {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (hJ : J.det ≠ 0) (h : UA σ J) :
    (mat h).det * cA σ (mat h).det = 1 := by
  have hm : (mat h)ᵀ * incM F J * (mat h).map (cA σ) = incM F J := h.2
  have h2 := congrArg Matrix.det hm
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose] at h2
  have e1 : ((mat h).map (cA σ)).det = cA σ (mat h).det := (AlgHom.map_det (cA σ) _).symm
  have e2 : (incM F J).det = inclR (F := F) (AF F) J.det := (RingHom.map_det _ J).symm
  rw [e1, e2] at h2
  have hu : IsUnit (inclR (F := F) (AF F) J.det) := (isUnit_iff_ne_zero.2 hJ).map _
  have h3 : (mat h).det * cA σ (mat h).det * inclR (F := F) (AF F) J.det = 1 * inclR (F := F) (AF F) J.det := by
    linear_combination h2
  exact hu.mul_left_injective h3

theorem piW_algebraMap {v : Pl (F := F)} (τ : E →ₐ[F] Fv F v) (a : AF F) :
    piW τ (algebraMap (AF F) (AE F E) a) = evFin F v a := by
  show splitProj τ (compFin F E v (a ⊗ₜ[F] (1 : E))) = _
  show splitProj τ (evFin F v a ⊗ₜ[F] (1 : E)) = _
  rw [splitProj_tmul, map_one, mul_one]

theorem at_mul {v : Pl (F := F)} {x : AE F E} (hx : At (evFin F v) x) (y : AE F E) : At (evFin F v) (x * y) := fun u hu => by
  rw [← smul_mul_assoc, hx u hu, zero_mul]

theorem at_add {v : Pl (F := F)} {x y : AE F E} (hx : At (evFin F v) x) (hy : At (evFin F v) y) : At (evFin F v) (x + y) :=
  fun u hu => by rw [smul_add, hx u hu, hy u hu, add_zero]

theorem at_det_sub_one {v : Pl (F := F)} {n : ℕ} {M : Matrix (Fin n) (Fin n) (AE F E)} (hM : At (evFin F v) (M - 1)) :
    At (evFin F v) (M.det - 1) := by
  intro u hu
  let I : Ideal (AE F E) := Ideal.span (Set.range fun p : Fin n × Fin n => (M - 1) p.1 p.2)
  have hdet : M.det - 1 ∈ I := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_one, RingHom.map_det, sub_eq_zero]
    have : (Ideal.Quotient.mk I).mapMatrix M = 1 := by
      ext i j
      rw [RingHom.mapMatrix_apply, Matrix.map_apply, ← map_one (Ideal.Quotient.mk I).mapMatrix,
        RingHom.mapMatrix_apply, Matrix.map_apply, Ideal.Quotient.eq]
      exact Ideal.subset_span ⟨(i, j), rfl⟩
    rw [this, Matrix.det_one]
  have hle : I ≤ (Submodule.span (AE F E) {algebraMap (AF F) (AE F E) u}).annihilator := by
    rw [Ideal.span_le]
    rintro _ ⟨p, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_annihilator_span_singleton, smul_eq_mul, mul_comm, ← Algebra.smul_def]
    have := congrFun (congrFun (hM u hu) p.1) p.2
    simpa using this
  have := (Submodule.mem_annihilator_span_singleton _ _).1 (hle hdet)
  rw [Algebra.smul_def, mul_comm]
  rwa [smul_eq_mul] at this

theorem algebraMap_injective_AE : Function.Injective (algebraMap (AF F) (AE F E)) :=
  Algebra.TensorProduct.includeLeft_injective (R := F) (S := AF F) (A := AF F) (B := E) (algebraMap F E).injective

theorem norm_det_eq_one {σ : E →ₐ[F] E} (hσ : IsCMExt F E σ) {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (hJ : J.det ≠ 0)
    (h : UA σ J) :
    Units.map (Algebra.norm (AF F) : AE F E →* AF F) (Matrix.GeneralLinearGroup.det (h : GL (Fin n) (AE F E))) = 1 := by
  apply Units.ext
  apply algebraMap_injective_AE (F := F) (E := E)
  show algebraMap (AF F) (AE F E) (Algebra.norm (AF F) (mat h).det) = algebraMap (AF F) (AE F E) 1
  rw [GlobalTheory.Doubling.algebraMap_norm_eq hσ, map_one]
  exact det_mul_cA hJ h

theorem ratio_algebraMap_eq_one {X : Chars F E} {a a' : ℕ}
    (hα : ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range X.α a')
    (hβ : ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range X.β a) (he : Even (a + a')) (u : (AF F)ˣ) :
    X.ν (Units.map (algebraMap (AF F) (AE F E) : AF F →* AE F E) u) = 1 := by
  have h1 := hα u
  have h2 := hβ u
  show (X.α / X.β) _ = 1
  rw [MonoidHom.div_apply, div_eq_one]
  apply Circle.ext
  rw [h1, h2]
  split_ifs
  · rfl
  · have key : Even a ↔ Even a' := Nat.even_add.1 he
    by_cases ha : Even a
    · rw [ha.neg_one_pow, (key.1 ha).neg_one_pow]
    · rw [(Nat.not_even_iff_odd.1 ha).neg_one_pow, (Nat.not_even_iff_odd.1 (fun h => ha (key.2 h))).neg_one_pow]

theorem at_localIdele (v : Pl (F := F)) (x : (Fv F v)ˣ) :
    At (evFin F v) (algebraMap (AF F) (AE F E) (Neutral.B1.localIdele F v x : AF F) - 1) := by
  intro c hc
  have hs := Neutral.B1.localIdele_isSupportedAt F v x
  have key : c * ((Neutral.B1.localIdele F v x : AF F) - 1) = 0 := by
    apply Prod.ext
    · funext w
      show c.1 w * ((Neutral.B1.localIdele F v x : AF F).1 w - 1) = 0
      rw [hs.1 w, sub_self, mul_zero]
    · apply RestrictedProduct.ext
      intro P
      show c.2 P * ((Neutral.B1.localIdele F v x : AF F).2 P - 1) = 0
      by_cases hP : P = v
      · subst hP
        have : c.2 P = 0 := hc
        rw [this, zero_mul]
      · rw [hs.2 P hP, sub_self, mul_zero]
  rw [Algebra.smul_def, ← map_one (algebraMap (AF F) (AE F E)), ← map_sub, ← map_mul, key, map_zero]

end GlobalTheory.SiegelValGood

open GlobalTheory.SiegelValGood in
theorem GlobalTheory.SiegelValGood.siegel_factor_eq_sq : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ v, X.Good v → ∀ (t : E →ₐ[F] Fv F v)
    (K : GL (Fin a') (Fv F v) →* UA σ G.V'.J), (∀ g, K g ∈ UAt σ G.V' (evFin F v) ∧
      (mat (K g)).map (piW t) = g.val ∧
      (mat (K g)).map (piW (t.comp σ)) = (G.V'.J.map t)⁻¹ * ((g⁻¹ : GL _ _).val)ᵀ * G.V'.J.map t) →
    ∀ g : GL (Fin a') (Fv F v),
      ((X.α / X.β) (Matrix.GeneralLinearGroup.det ((K g : UA σ G.V'.J) : GL (Fin a') (AE F E))) : ℂ) *
        ((((adeleClass F).modu (Units.map (Algebra.norm (AF F) : AE F E →* AF F)
          (Matrix.GeneralLinearGroup.det ((K g : UA σ G.V'.J) : GL (Fin a') (AE F E)))) : ℝ) ^
            ((Fintype.card (Fin (a + a')) : ℝ) / 2) : ℝ) : ℂ) = (chrW X.ν t (GlobalTheory.SplitFlip.gdet g) : ℂ) ^ 2 ∨
      ((X.α / X.β) (Matrix.GeneralLinearGroup.det ((K g : UA σ G.V'.J) : GL (Fin a') (AE F E))) : ℂ) *
        ((((adeleClass F).modu (Units.map (Algebra.norm (AF F) : AE F E →* AF F)
          (Matrix.GeneralLinearGroup.det ((K g : UA σ G.V'.J) : GL (Fin a') (AE F E)))) : ℝ) ^
            ((Fintype.card (Fin (a + a')) : ℝ) / 2) : ℝ) : ℂ) = (((chrW X.ν t (GlobalTheory.SplitFlip.gdet g))⁻¹ : ℂˣ) : ℂ) ^ 2 := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT v hv t K hK g
  left
  have hσ : IsCMExt F E σ := hT.base.cm
  have hJ : G.V'.J.det ≠ 0 := by
    intro h0
    obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
    apply det_ne_zero_of_hasSig (hT.geo.hV'.sig w)
    have e : (G.V'.J.map (B.emb w).1).det = (B.emb w).1 G.V'.J.det := (RingHom.map_det _ _).symm
    rw [e, h0, map_zero]
  obtain ⟨hat, h1, h2⟩ := hK g
  set D := Matrix.GeneralLinearGroup.det ((K g : UA σ G.V'.J) : GL (Fin a') (AE F E)) with hD
  have hDv : (D : AE F E) = (mat (K g)).det := rfl
  have hN : Units.map (Algebra.norm (AF F) : AE F E →* AF F) D = 1 := norm_det_eq_one hσ hJ (K g)
  rw [hN, map_one, NNReal.coe_one, Real.one_rpow, Complex.ofReal_one, mul_one]
  have hpt : piW t (D : AE F E) = (GlobalTheory.SplitFlip.gdet g : Fv F v) := by
    rw [hDv, RingHom.map_det, RingHom.mapMatrix_apply, h1]; rfl
  have hJt : (G.V'.J.map t).det ≠ 0 := by
    have : (G.V'.J.map t).det = t G.V'.J.det := (AlgHom.map_det t _).symm
    rw [this]
    exact (map_ne_zero _).2 hJ
  have hgi : ((g⁻¹ : GL (Fin a') (Fv F v)) : Matrix (Fin a') (Fin a') (Fv F v)).det =
      (((GlobalTheory.SplitFlip.gdet g)⁻¹ : (Fv F v)ˣ) : Fv F v) := by
    rw [show (GlobalTheory.SplitFlip.gdet g)⁻¹ = Matrix.GeneralLinearGroup.det g⁻¹ from (map_inv _ _).symm]; rfl
  have hps : piW (t.comp σ) (D : AE F E) = (((GlobalTheory.SplitFlip.gdet g)⁻¹ : (Fv F v)ˣ) : Fv F v) := by
    rw [hDv, RingHom.map_det, RingHom.mapMatrix_apply, h2, Matrix.det_mul, Matrix.det_mul, Matrix.det_nonsing_inv,
      Matrix.det_transpose, Ring.inverse_eq_inv, mul_right_comm, inv_mul_cancel₀ hJt, one_mul, hgi]
  set u := Neutral.B1.localIdele F v (GlobalTheory.SplitFlip.gdet g) with hu
  set zz : (AE F E)ˣ := Units.map (algebraMap (AF F) (AE F E) : AF F →* AE F E) u with hzz
  have hzt : ∀ τ : E →ₐ[F] Fv F v, piW τ (zz : AE F E) = (GlobalTheory.SplitFlip.gdet g : Fv F v) := fun τ => by
    show piW τ (algebraMap (AF F) (AE F E) (u : AF F)) = _
    rw [piW_algebraMap]
    exact Neutral.B1.localIdele_snd_self F v _
  have hzat : At (evFin F v) ((zz : AE F E) - 1) := at_localIdele v _
  have hνz : X.ν zz = 1 := ratio_algebraMap_eq_one hT.chars.resα hT.chars.resβ hT.geo.even u
  have hyat : At (evFin F v) (((D * zz : (AE F E)ˣ) : AE F E) - 1) := by
    have e : ((D * zz : (AE F E)ˣ) : AE F E) - 1 = ((D : AE F E) - 1) * zz + ((zz : AE F E) - 1) := by
      rw [Units.val_mul]; ring
    rw [e]
    exact at_add (at_mul (at_det_sub_one hat) _) hzat
  have hy1 : piW (t.comp σ) ((D * zz : (AE F E)ˣ) : AE F E) = 1 := by
    rw [Units.val_mul, map_mul, hps, hzt, Units.inv_mul]
  have key := GlobalTheory.ChrLocal.chrW_piW_eq F E σ hσ X.ν v t (D * zz) hyat hy1
  have hsq : Units.map (piW t).toMonoidHom (D * zz) = GlobalTheory.SplitFlip.gdet g ^ 2 := by
    apply Units.ext
    show piW t ((D * zz : (AE F E)ˣ) : AE F E) = ((GlobalTheory.SplitFlip.gdet g ^ 2 : (Fv F v)ˣ) : Fv F v)
    rw [Units.val_mul, map_mul, hpt, hzt, Units.val_pow_eq_pow_val, sq]
  rw [hsq, map_pow, map_mul, hνz, mul_one] at key
  show ((X.ν D : Circle) : ℂ) = _
  rw [← Units.val_pow_eq_pow_val, key]
  rfl
end

section

open scoped Matrix GlobalTheory.VacAny
open NumberField IsDedekindDomain MeasureTheory Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RatWeilOp

noncomputable section

namespace GlobalTheory.PoissonReindex

open GlobalTheory.SWQ

variable {F : Type} [Field F] [NumberField F]

def reidx {κ ι : Type} (e : κ ≃ ι) : (ι → AF F) ≃ₜ+ (κ → AF F) where
  toFun u i := u (e i)
  invFun x j := x (e.symm j)
  left_inv u := by funext j; simp
  right_inv x := by funext i; simp
  map_add' u v := rfl
  continuous_toFun := continuous_pi fun i => continuous_apply _
  continuous_invFun := continuous_pi fun j => continuous_apply _

theorem reidx_apply {κ ι : Type} (e : κ ≃ ι) (u : ι → AF F) (i : κ) : reidx (F := F) e u i = u (e i) := rfl

theorem dot_reidx {κ ι : Type} [Fintype κ] [Fintype ι] (e : κ ≃ ι) (u y : ι → AF F) :
    reidx e u ⬝ᵥ reidx e y = u ⬝ᵥ y := by
  simp only [dotProduct, reidx_apply]
  exact e.sum_comp (fun j => u j * y j)

theorem Bd_half {N : ℕ} (s u : Fin N → AF F) : Bd (AF F) (fun _ : Fin N => (1 / 2 : F)) s u = s ⬝ᵥ u := by
  simp only [Bd, dotProduct]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [show (2 : F) * (1 / 2) = 1 by norm_num, map_one, one_mul]

theorem mem_schA_reidx {κ ι : Type} [Fintype κ] [Fintype ι] (e : κ ≃ ι) {Φ : (κ → AF F) → ℂ}
    (hΦ : Φ ∈ schA F κ) : (fun u => Φ (reidx e u)) ∈ schA F ι := by
  have h := GlobalTheory.RestrSchA.mem_schA_comp_extend F e.symm e.symm.injective Φ hΦ
  convert h using 2 with u
  congr 1
  funext i
  rw [reidx_apply]
  conv_rhs => rw [← e.symm_apply_apply i]
  exact (e.symm.injective.extend_apply u 0 (e i)).symm

end GlobalTheory.PoissonReindex


open GlobalTheory.SWQ GlobalTheory.PoissonReindex in
theorem GlobalTheory.PoissonReindex.poisson_any : ∀ (F : Type) [Field F] [NumberField F], IsTotallyReal F → ∀ (ψ : AddChar (AF F) ℂ), IsStd ψ → ∀ (κ : Type) [Fintype κ]
    [MeasurableSpace (κ → AF F)] [BorelSpace (κ → AF F)] (μ : Measure (κ → AF F)) [μ.IsAddHaarMeasure],
    ∃ c : ℂ, c ≠ 0 ∧ ∀ Φ ∈ schA F κ, (fun y : κ → AF F => ∫ x, Φ x * ψ (x ⬝ᵥ y) ∂μ) ∈ schA F κ →
      thetaSum F (fun y : κ → AF F => ∫ x, Φ x * ψ (x ⬝ᵥ y) ∂μ) = c * thetaSum F Φ := by
  intro F _ _ hF ψ hψ κ _ inst hB μ hμ
  haveI : BorelSpace (AF F) := ⟨rfl⟩
  haveI : SecondCountableTopology (AF F) := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  have hinst : inst = MeasurableSpace.pi := by
    rw [hB.measurable_eq]
    exact (Pi.borelSpace (ι := κ) (X := fun _ => AF F)).measurable_eq.symm
  subst hinst
  set N := Fintype.card κ
  let e : κ ≃ Fin N := Fintype.equivFin κ
  have hC1 := GlobalTheory.StdCharFromIsStd.isCharAF hψ
  obtain ⟨lam, hlam⟩ := GlobalTheory.SWQ.exists_isLam F hF ψ hC1
  obtain ⟨ν, hν⟩ := GlobalTheory.SWQ.exists_adeles_haarMeasure_covolume_one F
  let a : Fin N → F := fun _ => 1 / 2
  have hC : Ctx ψ lam ν a := ⟨hF, hC1, hlam, hν, fun _ => by norm_num [a]⟩
  obtain ⟨hHaar, -⟩ := GlobalTheory.SWQ.rat_lattice_fundamentalDomain F N ν hν
  haveI := hHaar
  let T : (Fin N → AF F) ≃ₜ+ (κ → AF F) := reidx e
  let Tm : (Fin N → AF F) ≃ᵐ (κ → AF F) := T.toHomeomorph.toMeasurableEquiv
  have hTm : ∀ u, Tm u = T u := fun _ => rfl
  haveI hm : (Measure.map Tm (muV N ν)).IsAddHaarMeasure := T.isAddHaarMeasure_map (muV N ν)
  have hr := Measure.isAddLeftInvariant_eq_smul μ (Measure.map Tm (muV N ν))
  set r := μ.addHaarScalarFactor (Measure.map Tm (muV N ν))
  have hr0 : (r : ℂ) ≠ 0 := by
    intro h
    have h' : r = 0 := by exact_mod_cast h
    rw [h', zero_smul] at hr
    exact (NeZero.ne μ) hr
  refine ⟨(r : ℂ), hr0, fun Φ hΦ hFΦ => ?_⟩
  set G : (κ → AF F) → ℂ := fun y => ∫ x, Φ x * ψ (x ⬝ᵥ y) ∂μ with hG
  set Φ' : (Fin N → AF F) → ℂ := fun u => Φ (T u) with hΦ'
  have key : ∀ y', G (T y') = (r : ℂ) * Fo ψ ν a Φ' y' := by
    intro y'
    simp only [hG]
    rw [hr, integral_smul_nnreal_measure, integral_map_equiv]
    simp only [Fo, hΦ', hTm, a, Bd_half, T, dot_reidx]
    rw [NNReal.smul_def, Complex.real_smul]
  have hΦ's : Φ' ∈ schA F (Fin N) := mem_schA_reidx e hΦ
  have hD : Decay Φ' := GlobalTheory.SchwartzDecay.decay_of_mem_schA F N Φ' hΦ's
  have hGs : (fun u => G (T u)) ∈ schA F (Fin N) := mem_schA_reidx e hFΦ
  have hFeq : Fo ψ ν a Φ' = (r : ℂ)⁻¹ • fun u => G (T u) := by
    funext u
    simp only [Pi.smul_apply, smul_eq_mul, key u]
    rw [← mul_assoc, inv_mul_cancel₀ hr0, one_mul]
  have hFD : Decay (Fo ψ ν a Φ') := by
    rw [hFeq]
    exact GlobalTheory.SchwartzDecay.decay_smul _ (GlobalTheory.SchwartzDecay.decay_of_mem_schA F N _ hGs)
  have hP := GlobalTheory.SWQ.poisson_summation F N ψ lam ν a hC Φ' hD hFD
  let E2 : (Fin N → F) ≃ (κ → F) :=
    { toFun := fun ξ i => ξ (e i), invFun := fun η j => η (e.symm j),
      left_inv := fun ξ => by funext j; simp, right_inv := fun η => by funext i; simp }
  have hth : ∀ H : (κ → AF F) → ℂ, thetaSum F H = th (fun u => H (T u)) := by
    intro H
    simp only [thetaSum, th]
    exact ((E2.tsum_eq (fun η => H (fun i => algebraMap F (AF F) (η i))))).symm
  rw [hth G, hth Φ]
  simp only [th] at hP ⊢
  simp only [key, tsum_mul_left]
  rw [hP]
end
end

section

open scoped Matrix GlobalTheory.VacAny ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RatWeilOp

namespace GlobalTheory.WeilAdm.HaarSplit

theorem lintegral_split_mul : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] [MeasurableSpace (κ → AF F)] [BorelSpace (κ → AF F)]
    [MeasurableSpace (κ → mixedEmbedding.mixedSpace F)] [BorelSpace (κ → mixedEmbedding.mixedSpace F)]
    [MeasurableSpace (κ → Af F)] [BorelSpace (κ → Af F)]
    (μ : Measure (κ → AF F)) [μ.IsAddHaarMeasure] (μi : Measure (κ → mixedEmbedding.mixedSpace F)) [μi.IsAddHaarMeasure]
    (μf : Measure (κ → Af F)) [μf.IsAddHaarMeasure],
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧ ∀ (fi : (κ → mixedEmbedding.mixedSpace F) → ℝ≥0∞) (g : (κ → Af F) → ℝ≥0∞),
      Measurable fi → Measurable g →
        ∫⁻ x, fi (fun i => evI F (x i)) * g (fun i => sndA F (x i)) ∂μ = c * ((∫⁻ z, fi z ∂μi) * ∫⁻ y, g y ∂μf) := by
  intro F _ _ κ _ mA _ mI _ mf _ μ _ μi _ μf _
  haveI : LocallyCompactSpace (Af F) := GlobalTheory.AdelicUnitaryTop.locallyCompact_finiteAdele F
  haveI : SecondCountableTopology (Af F) := GlobalTheory.AdelicUnitaryTop.secondCountable_finiteAdele F
  haveI : T2Space (Af F) := GlobalTheory.AdelicUnitaryTop.t2Space_finiteAdeleRing_of_numberField F
  haveI : BorelSpace ((κ → mixedEmbedding.mixedSpace F) × (κ → Af F)) := Prod.borelSpace
  haveI : (μi.prod μf).IsAddHaarMeasure := Measure.prod.instIsAddHaarMeasure μi μf
  have hH : ((μ.map (splitE F κ).symm)).IsAddHaarMeasure :=
    (splitE F κ).symm.isAddHaarMeasure_map μ (continuous_splitE_symm F κ) (continuous_splitE F κ)
  let em : (κ → AF F) ≃ᵐ ((κ → mixedEmbedding.mixedSpace F) × (κ → Af F)) :=
    (Homeomorph.mk (splitE F κ).symm.toEquiv (continuous_splitE_symm F κ) (continuous_splitE F κ)).toMeasurableEquiv
  set c : NNReal := Measure.addHaarScalarFactor (μ.map (splitE F κ).symm) (μi.prod μf) with hc
  have heq : μ.map (splitE F κ).symm = c • (μi.prod μf) :=
    Measure.isAddLeftInvariant_eq_smul _ _
  refine ⟨(c : ℝ≥0∞), ?_, ENNReal.coe_ne_top, ?_⟩
  · exact ENNReal.coe_ne_zero.2 (Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure _ _).ne'
  intro fi g hfi hg
  have h1 : ∫⁻ x, fi (fun i => evI F (x i)) * g (fun i => sndA F (x i)) ∂μ
      = ∫⁻ p, fi p.1 * g p.2 ∂(μ.map (splitE F κ).symm) := by
    rw [show μ.map (splitE F κ).symm = μ.map em from rfl, lintegral_map_equiv]
    rfl
  rw [h1, heq, lintegral_smul_measure, lintegral_prod_mul hfi.aemeasurable hg.aemeasurable]
  rfl

end GlobalTheory.WeilAdm.HaarSplit
end
