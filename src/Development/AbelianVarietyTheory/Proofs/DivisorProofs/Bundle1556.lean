module

import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1542
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import Development.WeilBound.ThetaLifts.LocalTheory.ToralCohomology.ExistsTorus
import Development.WeilBound.ThetaLifts.TowerModels.PlaneIso
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.DiscreteSeriesCharacters.CapelliDeterminantBlockProduct
public import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.DiscreteSeriesCharacters.DiscreteSeriesInfinitesimalCharacter
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle015
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1473
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaIntegrandIntegrable
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle135
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle016
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ScaledIntegerPeriodic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1483
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1484
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
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle011
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceTensorProductFiniteExtension
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1287
public import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.LowKMultOneP
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle005
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1389
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1193

@[expose] public section

section

noncomputable section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published
open scoped TensorProduct

namespace GlobalTheory.SUAssemble

section Ring

variable {R : Type} [CommRing R] {n : Type} [Fintype n] [DecidableEq n]

theorem idem_mul (e : R) (he : e * e = e) (A B : Matrix n n R) :
    (1 + e • (A - 1)) * (1 + e • (B - 1)) = 1 + e • (A * B - 1) := by
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul, he, Matrix.sub_mul, Matrix.mul_sub, smul_sub, smul_add]
  abel

theorem idem_cT (c : R →+* R) (e : R) (hc : c e = e) (A : Matrix n n R) :
    Formalism.UG.cT c (1 + e • (A - 1)) = 1 + e • (Formalism.UG.cT c A - 1) := by
  ext i j
  simp [Formalism.UG.cT, Matrix.one_apply, hc, eq_comm]

theorem idem_unitary (c : R →+* R) (e : R) (he : e * e = e) (hc : c e = e) (J A : Matrix n n R)
    (hA : Formalism.UG.cT c A * J * A = J) :
    Formalism.UG.cT c (1 + e • (A - 1)) * J * (1 + e • (A - 1)) = J := by
  rw [idem_cT c e hc]
  have : (1 + e • (Formalism.UG.cT c A - 1)) * J * (1 + e • (A - 1)) =
      J + e • (Formalism.UG.cT c A * J * A - J) := by
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul, Matrix.smul_mul, Matrix.mul_smul,
      smul_smul, he, Matrix.sub_mul, Matrix.mul_sub, smul_sub, smul_add, Matrix.mul_assoc]
    abel
  rw [this, hA, sub_self, smul_zero, add_zero]

theorem idem_det (e : R) (he : e * e = e) (A : Matrix n n R) (hA : A.det = 1) :
    (1 + e • (A - 1)).det = 1 := by
  apply GlobalTheory.SUTrunc.det_trunc <;> assumption

end Ring

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {M : ℕ}
  (J : Matrix (Fin M) (Fin M) E)

def qr (x : Fin M → E) (u : E) : Matrix (Fin M) (Fin M) E :=
  1 + ((u - 1) / hE σ J x x) • Matrix.vecMulVec x (Matrix.vecMul (fun i => σ (x i)) J)

theorem sigR_inclR (e : E) : sigR (AF F) σ (inclR (AF F) e) = inclR (AF F) (σ e) := by
  simp [sigR, inclR]

def rmat (g : GL (Fin M) E) : Matrix (Fin M) (Fin M) (AF F ⊗[F] E) :=
  RingHom.mapMatrix (inclR (AF F)) (g : Matrix (Fin M) (Fin M) E)

theorem cT_rmat (g : GL (Fin M) E) :
    Formalism.UG.cT (sigR (AF F) σ) (rmat (F := F) g) =
      RingHom.mapMatrix (inclR (AF F)) (Formalism.UG.cT (σ : E →+* E) (g : Matrix (Fin M) (Fin M) E)) := by
  ext i j
  simp [rmat, Formalism.UG.cT, sigR_inclR]

theorem rmat_unitary {g : GL (Fin M) E} (hg : g ∈ Formalism.UG.UJ (σ : E →+* E) J) :
    Formalism.UG.cT (sigR (AF F) σ) (rmat (F := F) g) * JR (AF F) J * rmat (F := F) g = JR (AF F) J := by
  have h : Formalism.UG.cT (σ : E →+* E) (g : Matrix (Fin M) (Fin M) E) * J * (g : Matrix (Fin M) (Fin M) E) = J := hg
  rw [cT_rmat, show JR (AF F) J = RingHom.mapMatrix (inclR (AF F)) J from rfl, rmat, ← map_mul, ← map_mul, h]

def tm (η : AF F) (A : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) : Matrix (Fin M) (Fin M) (AF F ⊗[F] E) :=
  1 + algebraMap (AF F) (AF F ⊗[F] E) η • (A - 1)

theorem tm_mul (η : AF F) (hη : η * η = η) (A B : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) :
    tm η A * tm η B = tm η (A * B) :=
  idem_mul _ (by rw [← map_mul, hη]) A B

def trunc (η : AF F) (hη : η * η = η) : Formalism.UG.UJ (σ : E →+* E) J →* HA (AF F) σ J where
  toFun g := (⟨⟨tm η (rmat g.1), tm η (rmat g.1⁻¹),
      by rw [tm_mul η hη, rmat, rmat, ← map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, map_one, tm,
        sub_self, smul_zero, add_zero],
      by rw [tm_mul η hη, rmat, rmat, ← map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, map_one, tm,
        sub_self, smul_zero, add_zero]⟩,
    idem_unitary _ _ (by rw [← map_mul, hη]) (StrongApprox.sigR_algebraMap σ η) _ _ (rmat_unitary σ J g.2)⟩ : HR (AF F) σ J)
  map_one' := by
    apply Subtype.ext
    apply Units.ext
    change tm η (rmat (1 : GL (Fin M) E)) = 1
    rw [rmat, Units.val_one, map_one, tm, sub_self, smul_zero, add_zero]
  map_mul' g h := by
    apply Subtype.ext
    apply Units.ext
    change tm η (rmat (g.1 * h.1)) = tm η (rmat g.1) * tm η (rmat h.1)
    rw [tm_mul η hη, rmat, rmat, rmat, ← map_mul, Units.val_mul]

theorem mv_trunc (η : AF F) (hη : η * η = η) (g : Formalism.UG.UJ (σ : E →+* E) J) :
    ((HA.mat (AF F) σ J (trunc σ J η hη g)).1 : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) =
      1 + algebraMap (AF F) (AF F ⊗[F] E) η • (rmat (F := F) g.1 - 1) := rfl

theorem trunc_mem_SUAdelic (η : AF F) (hη : η * η = η) (g : Formalism.UG.UJ (σ : E →+* E) J)
    (hg : (g.1 : Matrix (Fin M) (Fin M) E).det = 1) : trunc σ J η hη g ∈ SUAdelic σ J := by
  rw [StrongApprox.mem_SUAdelic, mv_trunc]
  refine idem_det _ (by rw [← map_mul, hη]) _ ?_
  rw [rmat, ← RingHom.map_det, hg, map_one]

theorem idem_mul_of_sub {S₁ S₁' : Finset (InfinitePlace F)} {S₂ S₂' : Finset (HeightOneSpectrum (𝓞 F))}
    {ε ε' : AF F} (h : IsPlacesIdem S₁ S₂ ε) (h' : IsPlacesIdem S₁' S₂' ε') (hS₁ : S₁' ⊆ S₁) (hS₂ : S₂' ⊆ S₂) :
    ε * ε' = ε' := by
  obtain ⟨a1, -, b1, -⟩ := h
  obtain ⟨-, a0', -, b0'⟩ := h'
  apply Prod.ext
  · funext w
    change fstA F ε w * fstA F ε' w = fstA F ε' w
    by_cases hw : w ∈ S₁'
    · rw [a1 w (hS₁ hw), one_mul]
    · rw [a0' w hw, mul_zero]
  · apply RestrictedProduct.ext
    intro v
    change evalV F v (sndA F ε) * evalV F v (sndA F ε') = evalV F v (sndA F ε')
    by_cases hv : v ∈ S₂'
    · rw [b1 v (hS₂ hv), one_mul]
    · rw [b0' v hv, mul_zero]

theorem idem_sq {S₁ : Finset (InfinitePlace F)} {S₂ : Finset (HeightOneSpectrum (𝓞 F))} {ε : AF F}
    (h : IsPlacesIdem S₁ S₂ ε) : ε * ε = ε :=
  idem_mul_of_sub h h subset_rfl subset_rfl

theorem SUSupp_mono {ε ε' : AF F} (hε : ε * ε' = ε') {g : HA (AF F) σ J} (hg : g ∈ SUSupp σ J ε') :
    g ∈ SUSupp σ J ε := by
  refine ⟨hg.1, fun i j => ?_⟩
  rw [← hg.2 i j, ← mul_assoc, ← map_mul, hε]

end GlobalTheory.SUAssemble
end
end

section

open scoped TensorProduct Matrix Classical
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift

noncomputable section

namespace GlobalTheory.PolRangeInf

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def adAt (w : InfinitePlace F) (c : w.Completion) : AF F :=
  LinearMap.inl F (Ainf F) (Af F) (Pi.single w c)

theorem piInf_adAt_same (v : InfinitePlace F) (τ : EmbOver E v) (c : v.Completion) (x : E) :
    piInf τ (adAt v c ⊗ₜ[F] x) = InfinitePlace.Completion.extensionEmbedding v c * τ.1 x := by
  change infEmb τ (evInf F v (adAt v c) ⊗ₜ[F] x) = _
  have : evInf F v (adAt v c) = c := by
    change (Pi.single v c : Ainf F) v = c
    exact Pi.single_eq_same v c
  rw [this, infEmb_tmul]

theorem piInf_adAt_ne {v w : InfinitePlace F} (h : v ≠ w) (τ : EmbOver E v) (c : w.Completion) (x : E) :
    piInf τ (adAt w c ⊗ₜ[F] x) = 0 := by
  change infEmb τ (evInf F v (adAt w c) ⊗ₜ[F] x) = _
  have : evInf F v (adAt w c) = 0 := by
    change (Pi.single w c : Ainf F) v = 0
    exact Pi.single_eq_of_ne h c
  rw [this, TensorProduct.zero_tmul, map_zero]

theorem ext_symm_real {w : InfinitePlace F} (hw : w.IsReal) (t : ℝ) :
    InfinitePlace.Completion.extensionEmbedding w ((InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm t) =
      (t : ℂ) := by
  rw [← InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply hw,
    ← InfinitePlace.Completion.ringEquivRealOfIsReal_apply, RingEquiv.apply_symm_apply]

theorem smul_adAt_tmul (u : AF F) (hu : evI F u = 0) (w : InfinitePlace F) (c : w.Completion) (x : E) :
    u • (adAt w c ⊗ₜ[F] x : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) = 0 := by
  have hu1 : u.1 = 0 := (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective (hu.trans (map_zero _).symm)
  rw [TensorProduct.smul_tmul', smul_eq_mul]
  have : u * adAt w c = 0 := by
    refine Prod.ext ?_ ?_
    · change u.1 * (adAt w c).1 = 0
      rw [hu1, zero_mul]
    · change u.2 * (adAt w c).2 = 0
      exact mul_eq_zero_of_right _ rfl
  rw [this, TensorProduct.zero_tmul]

theorem exists_at_inf_values : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E}, IsCMExt F E σ → ∀ (τ : ∀ w : InfinitePlace F, EmbOver E w) (z : InfinitePlace F → ℂ),
    ∃ a : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E), At (evI F) a ∧ ∀ w, piInf (τ w) a = z w := by
  apply PositivityTheory.ThKG.CayleyTransformDarboux.exists_inf <;> assumption

end GlobalTheory.PolRangeInf
end
end

section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

namespace GlobalTheory.RealLift

theorem exists_atInf_piInf_eq : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (emb : ∀ w : InfinitePlace F, EmbOver E w) (f : InfinitePlace F → ℂ),
    ∃ z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E), At (evI F) z ∧ ∀ w, piInf (emb w) z = f w := by
  apply PositivityTheory.ThKG.CayleyTransformDarboux.exists_inf <;> assumption

end GlobalTheory.RealLift
end

section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

namespace GlobalTheory.ThK

theorem exists_at_evI_piInf_eq (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (h : IsCMExt F E σ) (τ : ∀ w : InfinitePlace F, EmbOver E w) (c : InfinitePlace F → ℂ) :
    ∃ z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E), At (evI F) z ∧ ∀ w, piInf (τ w) z = c w := by
  apply PositivityTheory.ThKG.CayleyTransformDarboux.exists_inf <;> assumption

end GlobalTheory.ThK
end

section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.LeviModulus
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.ImaginaryModulus

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem sig_sig {σ : E →ₐ[F] E} (h : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply τ.injective
  rw [h.2.2.2, h.2.2.2, star_star]

theorem exists_anti {σ : E →ₐ[F] E} (h : IsCMExt F E σ) : ∃ δ : E, δ ≠ 0 ∧ σ δ = -δ := by
  apply PositivityTheory.ThKG.Tow.Pln.exists_skew <;> assumption

theorem cA_inclR (σ : E →ₐ[F] E) (e : E) : cA σ (inclR (F := F) (AF F) e) = inclR (F := F) (AF F) (σ e) := by
  simp [cA, inclR]

theorem cA_eq_sigR (σ : E →ₐ[F] E) (z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) : cA σ z = sigR (AF F) σ z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add (f := _), hx, hy]
  | tmul a x => simp [cA, sigR]

section Iso

variable (σ : E →ₐ[F] E) [IsTopologicalRing (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))]

end Iso


end GlobalTheory.ImaginaryModulus
end
end

section

open Matrix GlobalTheory.HolDS
open Formalism.REAL (GlRel IsUnitary IsWeight KHighest root Jm inG)
open Formalism.QuantumDeterminants (lowK IsHCParam)
open Formalism.MainNotions.S (IsURepOn IsIrredOn UJset IsKFin IsKTypeOf IsKStableOn IsDS lowKSub vNormSq)
open CompanionTheory.D.DSIC (KRel KUnit KStab IsSmMod)
open CompanionTheory.D.LK (IsKMod IsMin)
open scoped InnerProductSpace

namespace GlobalTheory.HDUniq

noncomputable def height (n : ℕ) : (Fin n → ℝ) →ₗ[ℝ] ℝ :=
  ∑ i : Fin n, ((i : ℕ) : ℝ) • LinearMap.proj i

theorem height_apply {n : ℕ} (u : Fin n → ℝ) : height n u = ∑ i : Fin n, ((i : ℕ) : ℝ) * u i := by
  simp [height, LinearMap.sum_apply]

theorem height_root {n : ℕ} (a b : Fin n) : height n (PI.UpqRep.root a b) = (a : ℝ) - (b : ℝ) := by
  rw [height_apply]
  simp [PI.UpqRep.root, Pi.single_apply, mul_sub, Finset.sum_sub_distrib]

theorem height_cdom {n : ℕ} {ε : Fin n → Bool} {μ Λ : Fin n → ℝ} (h : PI.UpqRep.CDom ε μ Λ) :
    height n (Λ - μ) ≤ 0 ∧ (height n (Λ - μ) = 0 → Λ = μ) := by
  obtain ⟨c, hc, e⟩ := h
  have hval : height n (Λ - μ) = ∑ a, ∑ b, (c a b : ℝ) * ((a : ℝ) - (b : ℝ)) := by

    rw [e, map_sum]; refine Finset.sum_congr rfl fun a _ => ?_

    rw [map_sum]; refine Finset.sum_congr rfl fun b _ => ?_
    rw [map_smul, height_root, smul_eq_mul]
  have term : ∀ a b, (c a b : ℝ) * ((a : ℝ) - (b : ℝ)) ≤ 0 ∧
      ((c a b : ℝ) * ((a : ℝ) - (b : ℝ)) = 0 → c a b = 0) := by
    intro a b
    by_cases h0 : c a b = 0
    · simp [h0]
    · have hab : ((a : ℕ) : ℝ) < (b : ℕ) := by exact_mod_cast (hc a b h0).1
      have hpos : (0 : ℝ) < c a b := by exact_mod_cast Nat.pos_of_ne_zero h0
      refine ⟨mul_nonpos_of_nonneg_of_nonpos hpos.le (by linarith), fun h => ?_⟩
      exact absurd h (mul_neg_of_pos_of_neg hpos (by linarith)).ne
  refine ⟨?_, fun h0 => ?_⟩
  · rw [hval]; exact Finset.sum_nonpos fun a _ => Finset.sum_nonpos fun b _ => (term a b).1
  · rw [hval] at h0
    have hz : ∀ a b, c a b = 0 := by
      intro a b
      have h1 := (Finset.sum_eq_zero_iff_of_nonpos fun a _ =>
        Finset.sum_nonpos fun b _ => (term a b).1).1 h0 a (Finset.mem_univ _)
      exact (term a b).2 ((Finset.sum_eq_zero_iff_of_nonpos fun b _ => (term a b).1).1 h1 b
        (Finset.mem_univ _))
    rw [← sub_eq_zero, e]
    simp [hz]

theorem cdom_antisymm {n : ℕ} {ε : Fin n → Bool} {μ Λ : Fin n → ℝ} (h : PI.UpqRep.CDom ε μ Λ)
    (h' : PI.UpqRep.CDom ε Λ μ) : μ = Λ := by
  have a := height_cdom h
  have b := height_cdom h'
  have hn : height n (μ - Λ) = - height n (Λ - μ) := by rw [← map_neg, neg_sub]
  exact (a.2 (by linarith [a.1, b.1])).symm

theorem khighest_weight_unique : ∀ (n : ℕ) (ε : Fin n → Bool) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (E : Fin n → Fin n → Module.End ℂ V), KRel ε E → KUnit ε E → ∀ L : Submodule ℂ V, FiniteDimensional ℂ L →
    KStab ε E L → (∀ L' ≤ L, KStab ε E L' → L' = ⊥ ∨ L' = L) → ∀ (Λ : Fin n → ℝ) (v : V), v ∈ L → v ≠ 0 →
    KHighest ε E Λ v → (∀ ν : Fin n → ℝ, ∀ x ∈ L, x ≠ 0 → KHighest ε E ν x → ν = Λ) := by
  intro n ε V _ _ E hR hU L hfin hst hirr Λ v hvL hv0 hv ν x hxL hx0 hx
  have dom : ∀ (μ : Fin n → ℝ) (y : V) (μ' : Fin n → ℝ) (z : V), y ∈ L → y ≠ 0 → KHighest ε E μ y →
      z ∈ L → z ≠ 0 → IsWeight E μ' z → PI.UpqRep.CDom ε μ' μ := by
    intro μ y μ' z hyL hy0 hy hzL hz0 hz
    obtain ⟨L₁, hle, hyL₁, hst₁, -, hdom, -⟩ :=
      CompanionTheory.D.DSIC.hLowSpan n ε V E μ y L hR hU hy0 hy hfin hst hyL
    have hL₁ : L₁ = L := by
      rcases hirr L₁ hle hst₁ with h | h
      · exact absurd (by simpa [h] using hyL₁) hy0
      · exact h
    exact hdom μ' z (hL₁ ▸ hzL) hz0 hz
  exact cdom_antisymm (dom Λ v ν x hvL hv0 hv hxL hx0 hx.1) (dom ν x Λ v hxL hx0 hx hvL hv0 hv.1)

end GlobalTheory.HDUniq
end

section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature
open scoped TensorProduct InnerProductSpace Topology ComplexOrder
open GlobalTheory.GalLift

namespace GlobalTheory.ConjThetaIntegral

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem conjVal_one {D : D7} {σ : D.what₂.LL →+* ℂ} {a b : ℂ} (h : ConjVal σ a b) (ha : a = 1) : b = 1 := by
  obtain ⟨y, h1, h2⟩ := h
  have : y = 1 := D.what₂.embLL.injective (by rw [h1, ha, map_one])
  rw [← h2, this, map_one]

theorem ext_continuous {D : D7} {V : HSp D} (c : CoefA V) (hc : c.Is) (β : GL (Fin V.rank) (Lev.EAf D))
    (L : LevDat D.host.E ℂ V.rank) (χ' : (levEnv V β L).J →* ℂˣ) (hχ : ∀ k, (levEnv V β L).χ k = 1 → χ' k = 1)
    {f : Bridge.Gf V → c.W}
    (hf : f ∈ Bridge.AdForms (Bridge.ratF V) c.coef.ρ (levEnv V β L).J χ') : Continuous (c.ext f) := by
  haveI : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  haveI : Module.Finite D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ _ _
  haveI : IsTopologicalRing (AE D) := IsModuleTopology.isTopologicalRing (AF D.host.F) _
  haveI : IsTopologicalGroup (GA D V) := inferInstanceAs (IsTopologicalGroup (HR (AF D.host.F) D.sp.cm.sig V.gram))
  exact GlobalTheory.ThetaIntegrand.form_continuous (finHom V).rangeRestrict (GQ V) c.ρ hc.2.2.1
    ((GlobalTheory.ThetaIntegrand.eventually_level V β L).mono fun _ h => h.elim fun hk h1 => ⟨hk, hχ _ h1⟩) hf

theorem IsThetaP₂ {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle}
    {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} (hom : IsWeilDatumO ψ S T χS χT om) (hs : S.SigOK)
    (hp : S.IsPosDef) (c : CoefA S) (hc : c.Is) (β : GL (Fin S.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ S.rank)
    (χ' : (levEnv S β L).J →* ℂˣ) (hχ : ∀ k, (levEnv S β L).χ k = 1 → χ' k = 1)
    {X : Type} [AddCommGroup X] [Module ℂ X] (e : X →ₗ[ℂ] (Bridge.Gf S → c.W))
    (he : ∀ x, e x ∈ Bridge.AdForms (Bridge.ratF S) c.coef.ρ (levEnv S β L).J χ')
    (pt : PolF D T.rank S.rank →ₗ[ℂ] (WO S T → ℂ)) (hpt : ∀ P, IsThetaFunO ψ S T (pt P))
    {TK : Type} [AddCommGroup TK] [Module ℂ TK]
    (io : TK →ₗ[ℂ] c.W →ₗ[ℂ] PolF D T.rank S.rank) {K : Subgroup (GL (Fin S.rank) (Lev.EAf D))} {μ : Measure (GA D S)}
    {𝓕 : Set (GA D S)} (hμ : IsMeasDef S K μ 𝓕) :
    ∃ thP, Lift.IsThetaP μ 𝓕 (fun g h φ => thetaKO om h g φ) (fun P => pt P) io (LinearMap.range (c.ext ∘ₗ e)) thP := by
  have hpos : ∀ τ, (gramAt D S τ).PosDef := fun τ => by
    have := hs (tauE D τ)
    rw [hp] at this
    exact GlobalTheory.DefiniteQuotient.posDef_of_signature this
  refine GlobalTheory.ThetaIntegralLinear.exists_isThetaP_of_integrable μ 𝓕
    (fun g h => LinearMap.proj (R := ℂ) (φ := fun _ : WO S T => ℂ) 0 ∘ₗ om (h, g)) pt io _ ?_
  rintro ⟨_, x, rfl⟩ v g
  exact GlobalTheory.DefiniteQuotient.integrableOn_theta D ψ hom.std S T χS χT om hom hpos c.W (pt ∘ₗ io v)
    (fun w => hpt _) _ (ext_continuous c hc β L χ' hχ (he x)) (GlobalTheory.ThetaIntegrand.ext_invariant c (he x)) μ 𝓕 hμ.1.1 hμ.2 g

end GlobalTheory.ConjThetaIntegral

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.prod_lowestKTypeDims_indep_complexEmbedding : ∀ (D : D7) (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (∏ ρ, ((dimK _ _ (kapAt (Wc D i) σ ρ) : ℚ) : ℂ)) = ((∏ τ, GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.dimAt D i τ : ℝ) : ℂ) := by
  first | exact @GlobalTheory.DimProdLab.prod_dims | exact GlobalTheory.DimProdLab.prod_dims | (intros; apply GlobalTheory.DimProdLab.prod_dims <;> assumption)
end

section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.KSplit

theorem _root_.GlobalTheory.T.zetaIntegralShells_vanish_beyondPeriod_ramified : GlobalTheory.IndefiniteRowSideFullHecke.ScaledIntegerPeriodic.ShellLemma := by
  first | exact @GlobalTheory.ShellVan.shell_lemma | exact GlobalTheory.ShellVan.shell_lemma | (intros; apply GlobalTheory.ShellVan.shell_lemma <;> assumption)
end

section

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun

theorem _root_.GlobalTheory.T.lattice_stable_almost_all_places_right : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n d : ℕ) (X : Spc F E n)
    (Y : Spc F E d), Y.L.IsFullLattice E → ∀ N : Matrix (Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)),
    Set.Finite {w : Pl (F := F) | ¬ ∀ γ ∈ latAtV X Y w, γ * Matrix.transpose N ∈ latAtV X Y w} := by
  intro F E _ _ _ _ _ n d X Y hY N
  first
  | exact GlobalTheory.AdelMatLatRight.almost_all_stable_right F E n d X Y hY N
  | exact GlobalTheory.AdelMatLatRight.almost_all_stable_right F E n d X Y hY.toIsLattice N
end
