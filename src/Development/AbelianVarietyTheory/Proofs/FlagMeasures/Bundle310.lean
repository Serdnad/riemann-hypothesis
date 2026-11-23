module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle006
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.RealObj
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle007
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle009
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AmplitudeAbsolutelyConvergentOperatorNormLe
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle010
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle120
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle111
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle137
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle308
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsProjector
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HasSignatureComplement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle295
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle012
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.StandardBaseFlagComplementIntegralLattice
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle307
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle067
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GluingImageCardPowLeDefectGroupCard
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle249
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle292
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermExponentsNonnegAndDefectGroupBound
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.HermitianFormUnitaryOneOne
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CuspidalOfUnipotentFibreIntegralsVanish
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PosPartUnitaryMul
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LowestKTypeInfinitesimalCharLargeGap
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.EigenfunctionFiniteCoefficients

@[expose] public section

section

noncomputable section

open MeasureTheory NumberField Matrix Formalism.BasicNotions Formalism.MainNotions.S
open scoped Classical

namespace GlobalTheory.LoopVol

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem root_fst_lt (w : Point D.host.E (D.R.rS + 1)) (q : GlobalTheory.LoopV.roots (ptMat w)) : q.1.1.1 < D.R.rS := by
  have hq := q.2
  simp only [GlobalTheory.LoopV.roots, Finset.mem_filter] at hq
  have h := hq.2.1
  have h2 := q.1.2.2
  rw [Fin.lt_def] at h
  omega

def ratCoord (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u' : D.what₂.Word) (w : Point D.host.E (D.R.rS + 1))
    (γ s y : X.B.I.Ginf) : D.what₂.Tau → GlobalTheory.LoopV.roots (ptMat w) → ℂ :=
  fun τ q => Formalism.L2.SG.HidaSetting.hJ (X.B.I.ε (X.pl.symm τ))
    (Formalism.L2.SG.HidaSetting.rv X.B.I (X.pl.symm τ) (X.fR ⟨q.1.1.1, root_fst_lt w q⟩))
    (uMat ((γ⁻¹ * (s⁻¹ * y * s) * γ) (X.pl.symm τ)) *ᵥ Formalism.L2.SG.RealObj.frm X u' 1 (X.pl.symm τ) q.1.2)

theorem ratCoord_cont (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u' : D.what₂.Word) (w : Point D.host.E (D.R.rS + 1))
    (γ s : X.B.I.Ginf) : Continuous (ratCoord X u' w γ s) := by
  unfold ratCoord Formalism.L2.SG.HidaSetting.hJ
  refine continuous_pi fun τ => continuous_pi fun q => ?_
  refine Continuous.dotProduct continuous_const (Continuous.matrix_mulVec continuous_const ?_)
  refine Continuous.matrix_mulVec ?_ continuous_const
  exact Units.continuous_val.comp (continuous_subtype_val.comp ((continuous_apply _).comp
    ((continuous_const.mul ((continuous_const.mul continuous_id).mul continuous_const)).mul continuous_const)))

end GlobalTheory.LoopVol

end
end

section

open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical

theorem _root_.GlobalTheory.T.hermFrame_weightSum_sameDatum_le : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ) (N : NF H r), ∀ (g : ℕ) (Λ : Submodule (𝓞 K) V), 1 ≤ g → N.IsTerm g Λ → N.omSum (fun Λ' => N.IsTerm g Λ' ∧ N.SameDat g Λ Λ') ≤ ENNReal.ofReal ((N.Del / N.gI g Λ) ^ ((Module.finrank K N.Wt : ℝ) / 2) * N.Del ^ (cf K + 2) * (N.Db * N.Del * N.NT) ^ (10000 * (r + 1) ^ 3)) := by
  first | exact @GlobalTheory.DegCnt.omSum_sameDat_le | exact GlobalTheory.DegCnt.omSum_sameDat_le | (intros; apply GlobalTheory.DegCnt.omSum_sameDat_le <;> assumption)
end

section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

theorem _root_.GlobalTheory.T.amplitude_absolutelyConvergent_operatorNorm_le : ∀ (k r : ℕ) {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] {Wq : Type} [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (z z' : (Fin (2 * r + k + 1) → ℂ)) (π : Mat k r → (Wp →L[ℂ] Wp)) (π' : Mat k r → (Wq →L[ℂ] Wq)) (ψ ψ' : Mat k r → ℂ) (μG μW μW' νS νS' μR νR : Measure (Mt k r)) (Φ : Mat k r → Wp) (Φ' : Mat k r → Wq) (γ : Mat k r) (c κ s H₁ De : ℝ), 1 ≤ r → 2 * r + 6 ≤ k → 0 < κ → 0 < s → 1 ≤ H₁ → OneSide z π ψ μG μW (ENNReal.ofReal κ • lebN k r) νS Φ c → OneSide z' π' ψ' μG μW' (ENNReal.ofReal κ • lebN k r) νS' Φ' c → MomBd z νS Φ (24 * r ^ 3 + 1) H₁ → MomBd z' νS' Φ' (24 * r ^ 3 + 1) H₁ → TwoFl k r z z' γ → DeOK k r z z' γ De → NormR k r γ s μR → IsQuotMeas μG μR νR → Integrable (fun x => (innerSL ℂ (Φ' (Matrix.of x))).smulRight (Φ (γ * Matrix.of x))) νR ∧ ‖(haveI := FiniteDimensional.complete ℂ Wp; ampJ νR c Φ Φ' γ)‖ ≤ κ / s * absBd k r H₁ De (Dr k r z z' γ) := by
  first | exact @GlobalTheory.Amp.AbsConv.abs_core | exact GlobalTheory.Amp.AbsConv.abs_core | (intros; apply GlobalTheory.Amp.AbsConv.abs_core <;> assumption)
end

section

open Formalism.FourierDecayAlt GlobalTheory.ThA MeasureTheory Formalism.QuantumDeterminants Matrix
open scoped InnerProductSpace

theorem _root_.GlobalTheory.T.lebesgue_rootCoordinates_map_besselTorus_conj : ∀ (k r : ℕ) (α : ℂ), α ≠ 0 → (D.muN k r).map (conjM (aT k r α)) = ENNReal.ofReal ((‖α‖ ^ B.kap k r)⁻¹) • D.muN k r := by
  first | exact @GlobalTheory.ThA.TorusJac.muN_map_conj | exact GlobalTheory.ThA.TorusJac.muN_map_conj | (intros; apply GlobalTheory.ThA.TorusJac.muN_map_conj <;> assumption)
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase

namespace GlobalTheory.AdaptedExists

theorem exists_complement (I I₀ : AutInst) (e : I₀.E ≃+* I.E) (p q : ℕ) (he : ∀ y, e (star y) = star (e y))
    {κ : Type} [Fintype κ] [DecidableEq κ] (hI : HasSig I p q)
    (hI₀ : HasSig I₀ (p - Fintype.card κ) (q - Fintype.card κ)) (hn : I.n = I₀.n + 2 * Fintype.card κ)
    (Λ : Submodule (𝓞 I.E) (Fin I.n → I.E)) (hΛ : Submodule.IsLattice I.E Λ)
    (hdual : ∀ x, x ∈ Λ ↔ ∀ y ∈ Λ, star y ⬝ᵥ (I.J *ᵥ x) ∈ (algebraMap (𝓞 I.E) I.E).range)
    (T T' : Matrix (Fin I.n) κ I.E) (B : Matrix (Fin I.n) (Fin I₀.n) I.E)
    (h1 : Tᴴ * I.J * T = 0) (h2 : T'ᴴ * I.J * T' = 0) (h3 : Tᴴ * I.J * T' = 1) (h4 : Tᴴ * I.J * B = 0)
    (h5 : T'ᴴ * I.J * B = 0) (h6 : (Bᴴ * I.J * B).det ≠ 0)
    (h7 : ∀ z ∈ Λ, ∃ y, B *ᵥ y ∈ Λ ∧ (Bᴴ * I.J) *ᵥ (z - B *ᵥ y) = 0) :
    ∃ (γ : GL (Fin I₀.n) I.E) (x₀ : I₀.Gf), (B * γ.1)ᴴ * I.J * (B * γ.1) = I₀.J.map e ∧
      ∀ y, y ∈ lamX I₀ (1, x₀) ↔ ((B * γ.1) *ᵥ fun l => e (y l)) ∈ Λ := by
  obtain ⟨xΛ, hxΛ⟩ := GlobalTheory.SelfDualPoint.exists_lamX_eq I Λ hΛ (by simpa only [hform_eq] using hdual)
  have hΛfull : Submodule.IsFullLattice I.E Λ :=
    { toIsLattice := hΛ
      span_eq_top := by rw [← hxΛ]; exact (GlobalTheory.PointLattice.lamX_selfDual I (1, xΛ)).2.2.1 }
  have he' : ∀ y, e.symm (star y) = star (e.symm y) := fun y => e.injective (by simp [he])
  set G : Matrix (Fin I₀.n) (Fin I₀.n) I₀.E := (Bᴴ * I.J * B).map e.symm with hG
  have hGe : Bᴴ * I.J * B = G.map e := by ext r s; exact (e.apply_symm_apply _).symm
  have hGd : G.det ≠ 0 := fun h => h6 (by
    rw [hGe]; exact ((e : I₀.E →+* I.E).map_det G).symm.trans (by rw [h, map_zero]))
  have hGh : Gᴴ = G := by
    rw [hG, ← Matrix.conjTranspose_map _ he', ← gram_swap (J_herm I)]
  obtain ⟨L, hL, -, hLd⟩ := exists_factor_lattice I.E I₀.E e he _ _ I.J B G Λ (J_herm I) hGe hGd hΛfull hdual h7
  obtain ⟨γ, hγ⟩ := GlobalTheory.FlagMeas.sameKindIsometric I₀.E I₀.cm.cmUnram I₀.n G I₀.J hGh (J_herm I₀) hGd I₀.J_det ⟨L, hL.toIsLattice, hLd⟩
    ⟨I₀.L, Submodule.IsLattice.of_fg I₀.E I₀.L_fg, by simpa only [hform_eq] using I₀.L_dual⟩ (fun φ => by
      refine ⟨_, _, ?_, hasSignature_map I₀ _ _ hI₀ φ⟩
      set ψ : I.E →+* ℂ := φ.comp e.symm.toRingHom
      have hψ : ∀ x, ψ (star x) = star (ψ x) := I.cm.cmUnram.2.1 ψ
      have hm : G.map φ = (B.map ψ)ᴴ * I.J.map ψ * B.map ψ := by rw [map_gram ψ hψ]; rfl
      rw [hm]
      refine hasSignature_complement _ _ p q κ _ (T.map ψ) (T'.map ψ) _ ?_ (hasSignature_map I p q hI ψ) hn ?_ ?_ ?_ ?_ ?_ ?_
      · rw [← Matrix.conjTranspose_map _ hψ, J_herm]
      · rw [map_gram ψ hψ, h1, Matrix.map_zero _ (map_zero ψ)]
      · rw [map_gram ψ hψ, h2, Matrix.map_zero _ (map_zero ψ)]
      · rw [map_gram ψ hψ, h3, Matrix.map_one _ (map_zero ψ) (map_one ψ)]
      · rw [map_gram ψ hψ, h4, Matrix.map_zero _ (map_zero ψ)]
      · rw [map_gram ψ hψ, h5, Matrix.map_zero _ (map_zero ψ)]
      · rw [← hm]
        exact fun h => hGd (φ.injective ((φ.map_det G).trans (h.trans (map_zero φ).symm))))
  set γ' : GL (Fin I₀.n) I.E := Matrix.GeneralLinearGroup.map (e : I₀.E →+* I.E) γ
  have hγ' : γ'.1 = γ.1.map (e : I₀.E →+* I.E) := rfl
  have hT : (B * γ'.1)ᴴ * I.J * (B * γ'.1) = I₀.J.map e := by
    have := map_gram (e : I₀.E →+* I.E) he G γ.1 γ.1
    rw [hγ, ← hγ'] at this
    refine Eq.trans ?_ this
    rw [show G.map (e : I₀.E →+* I.E) = _ from hGe.symm]
    simp only [conjTranspose_mul, Matrix.mul_assoc]
  obtain ⟨L', hL', hm, hLd'⟩ := exists_factor_lattice I.E I₀.E e he _ _ I.J (B * γ'.1) I₀.J Λ (J_herm I) hT I₀.J_det hΛfull hdual
    fun z hz => by
      obtain ⟨y, hy, hy'⟩ := h7 z hz
      have : (B * γ'.1) *ᵥ (γ'⁻¹.1 *ᵥ y) = B *ᵥ y := by
        rw [mulVec_mulVec, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
      refine ⟨γ'⁻¹.1 *ᵥ y, by rwa [this], ?_⟩
      rw [this, conjTranspose_mul, Matrix.mul_assoc, ← mulVec_mulVec, hy', mulVec_zero]
  obtain ⟨x₀, hx₀⟩ := GlobalTheory.SelfDualPoint.exists_lamX_eq I₀ L' hL'.toIsLattice (by simpa only [hform_eq] using hLd')
  exact ⟨γ', x₀, hT, by rwa [hx₀]⟩

theorem exists_isAdapted : ∀ (I I₀ : AutInst) (e : I₀.E ≃+* I.E) (p q a : ℕ) (j : Fin a → ℕ), (∀ y, e (star y) = star (e y)) → HasSig I p q → ∑ i, j i ≤ p → ∑ i, j i ≤ q → HasSig I₀ (p - ∑ i, j i) (q - ∑ i, j i) → ∀ (xf : I.Gf) (S : Fin (a + 1) → Submodule (𝓞 I.E) (Fin I.n → I.E)), IsSatFlag I (lamX I (1, xf)) j S → ∃ Λ x₀ T T' T₀, IsAdapted I I₀ e xf j S Λ x₀ T T' T₀ := by
  intro I I₀ e p q a j he hI hp hq hI₀ xf S ⟨h0, hmono, hrk, hsat, hiso⟩
  obtain ⟨-, hfg, hspan, hdual, -⟩ := GlobalTheory.PointLattice.lamX_selfDual I (1, xf)
  simp only [hform_eq] at hdual hiso
  have hn : I.n = I₀.n + 2 * ∑ i, j i := by
    have h1 := (GlobalTheory.FlagMeas.instance_numbers I).2.2.2.2.2 _ _ hI
    have h2 := (GlobalTheory.FlagMeas.instance_numbers I₀).2.2.2.2.2 _ _ hI₀
    omega
  have hle : ∀ k, S k ≤ lamX I (1, xf) := fun k y hy => ((hsat k y).1 hy).1
  have hSfg : (S (Fin.last a)).FG := hfg.of_le (hle _)
  obtain ⟨A, hA⟩ := GlobalTheory.saturatedFlag_splits I.E I.n a S h0 hmono hSfg fun i y hy h => (hsat i y).2 ⟨hle _ hy, h⟩
  obtain ⟨Λ, Ti, hΛ, hS⟩ := exists_blocks I.E I.n a j S A h0 hmono hSfg hrk hA
  set κ := Σ i, Fin (j i)
  have hκ : Fintype.card κ = ∑ i, j i := by simp [κ]
  have hsum : ∀ (M : Matrix (Fin I.n) κ I.E) (u : κ → I.E),
      M *ᵥ u = ∑ i, M.submatrix id (Sigma.mk i) *ᵥ fun s => u ⟨i, s⟩ := fun M u => by
    ext r
    simp [mulVec, dotProduct, Finset.sum_apply, κ, Fintype.sum_sigma]
  obtain ⟨T, hT⟩ : ∃ T : Matrix (Fin I.n) κ I.E, ∀ i, Ti i = T.submatrix id (Sigma.mk i) :=
    ⟨fun r s => Ti s.1 r s.2, fun _ => rfl⟩
  have hlast : ∀ z, z ∈ S (Fin.last a) ↔ ∃ u : κ → I.E, (∀ i, (fun s => u ⟨i, s⟩) ∈ Λ i) ∧ z = T *ᵥ u := fun z => by
    rw [hS]
    refine ⟨fun ⟨u, hu, _, hz⟩ => ⟨fun s => u s.1 s.2, hu, by rw [hsum, hz]; simp only [hT]⟩,
      fun ⟨u, hu, hz⟩ => ⟨_, hu, fun i hi => absurd (Fin.castSucc_lt_last i) hi, by rw [hz, hsum]; simp only [hT]⟩⟩
  have hone : ∀ i, ∀ t ∈ Λ i, Ti i *ᵥ t ∈ S (Fin.last a) := fun i t ht => by
    refine (hS _ _).2 ⟨Pi.single i t, fun k => ?_, fun i hi => absurd (Fin.castSucc_lt_last i) hi, ?_⟩
    · by_cases h : k = i
      · subst h; simpa using ht
      · simp [h]
    · rw [Finset.sum_eq_single i] <;> simp +contextual
  set W := Submodule.span I.E (S (Fin.last a) : Set (Fin I.n → I.E)) with hW
  have hrange : LinearMap.range T.mulVecLin = W := by
    refine le_antisymm ?_ (Submodule.span_le.2 fun z hz => ?_)
    · rintro _ ⟨u, rfl⟩
      rw [mulVecLin_apply, hsum]
      refine Submodule.sum_mem _ fun i _ => ?_
      have : Submodule.span I.E (Λ i : Set (Fin (j i) → I.E)) ≤ W.comap (Ti i).mulVecLin :=
        Submodule.span_le.2 fun t ht => Submodule.subset_span (hone i t ht)
      rw [← hT]
      have hsp := Submodule.IsFullLattice.span_eq_top (self := hΛ i)
      exact this (hsp ▸ Submodule.mem_top)
    · obtain ⟨u, -, rfl⟩ := (hlast z).1 hz
      exact ⟨u, rfl⟩
  have hdim : Module.finrank I.E W = Fintype.card κ := by
    have := telescope a j (fun k => Formalism.HN.rkK (S k)) hrk
    simp only [h0] at this
    rw [hκ]
    rw [show Formalism.HN.rkK (⊥ : Submodule (𝓞 I.E) (Fin I.n → I.E)) = 0 by
      rw [Formalism.HN.rkK, Submodule.bot_coe, Submodule.span_zero_singleton, finrank_bot], zero_add] at this
    exact this
  have hWiso : ∀ x ∈ W, ∀ y ∈ W, star x ⬝ᵥ (I.J *ᵥ y) = 0 := fun x hx y hy => by
    induction hx, hy using Submodule.span_induction₂ with
    | mem_mem x y hx hy => exact hiso x hx y hy
    | zero_left => simp
    | zero_right => simp
    | add_left x y z _ _ _ h h' => simp [h, h']
    | add_right x y z _ _ _ h h' => simp [mulVec_add, h, h']
    | smul_left c x y _ _ h => simp [h]
    | smul_right c x y _ _ h => simp [mulVec_smul, h]
  obtain ⟨W', hW'iso, hW'dim, hW'nd, hsplit⟩ := GlobalTheory.WittInt.main I.E I.cm.cmUnram I.n I.J (J_herm I) I.J_det _
    (Submodule.IsLattice.of_fg I.E hfg) hdual W hWiso
  obtain ⟨T', B, hrange', h3, h6, hB⟩ := exists_witt I.E I.n I₀.n κ I.J T W W' (J_herm I) I.J_det (hκ ▸ hn) hrange hdim
    (hW'dim.trans hdim) hWiso hW'iso hW'nd
  have mT : ∀ u, T *ᵥ u ∈ W := fun u => hrange ▸ ⟨u, rfl⟩
  have mT' : ∀ u, T' *ᵥ u ∈ W' := fun u => hrange' ▸ ⟨u, rfl⟩
  have h1 : Tᴴ * I.J * T = 0 := gram_eq_zero _ _ _ fun x y => hWiso _ (mT x) _ (mT y)
  have h2 : T'ᴴ * I.J * T' = 0 := gram_eq_zero _ _ _ fun x y => hW'iso _ (mT' x) _ (mT' y)
  have h4 : Tᴴ * I.J * B = 0 := gram_eq_zero _ _ _ fun x y =>
    (hB _).1 ⟨y, rfl⟩ _ (Submodule.mem_sup_left (mT x))
  have h5 : T'ᴴ * I.J * B = 0 := gram_eq_zero _ _ _ fun x y =>
    (hB _).1 ⟨y, rfl⟩ _ (Submodule.mem_sup_right (mT' x))
  have hdec : ∀ z ∈ lamX I (1, xf), ∃ u u' y, T *ᵥ u ∈ S (Fin.last a) ∧ T' *ᵥ u' ∈ lamX I (1, xf) ∧
      B *ᵥ y ∈ lamX I (1, xf) ∧ z = T *ᵥ u + T' *ᵥ u' + B *ᵥ y := fun z hz => by
    obtain ⟨x, hx, y, hy, hxW, hyW, h⟩ := hsplit z hz
    obtain ⟨w, hw⟩ := (hB _).2 h
    have hxS := (hsat _ x).2 ⟨hx, hxW⟩
    rw [← hrange] at hxW
    rw [← hrange'] at hyW
    obtain ⟨u, rfl⟩ := hxW
    obtain ⟨u', rfl⟩ := hyW
    simp only [mulVecLin_apply] at hw hx hy hxS
    exact ⟨u, u', w, hxS, hy, hw ▸ sub_mem (sub_mem hz hx) hy, by rw [hw]; abel⟩
  obtain ⟨γ, x₀, hG, hx₀⟩ := exists_complement I I₀ e p q he hI (hκ ▸ hI₀) (hκ ▸ hn) _ (Submodule.IsLattice.of_fg I.E hfg) hdual T T' B
    h1 h2 h3 h4 h5 h6 fun z hz => by
      obtain ⟨u, u', y, -, -, hy, rfl⟩ := hdec z hz
      refine ⟨y, hy, ?_⟩
      rw [add_sub_cancel_right, mulVec_add, mulVec_mulVec, mulVec_mulVec, gram_swap (J_herm I) T,
        gram_swap (J_herm I) T', h4, h5]
      simp
  have hsub : ∀ {l : Type} (M : Matrix (Fin I.n) κ I.E) (N : Matrix (Fin I.n) l I.E) {k₁ k₂ : Type}
      (f : k₁ → κ) (g : k₂ → l),
      (M.submatrix id f)ᴴ * I.J * N.submatrix id g = (Mᴴ * I.J * N).submatrix f g := fun M N _ _ f g => by
    ext r s
    simp [Matrix.mul_apply]
  have hpair : ∀ i t u', star (Ti i *ᵥ t) ⬝ᵥ (I.J *ᵥ (T' *ᵥ u')) = star t ⬝ᵥ fun s => u' ⟨i, s⟩ := fun i t u' => by
    rw [form_mulVec, hT, ← Matrix.submatrix_id_id T', hsub, h3]
    congr 1
    ext s
    simp [mulVec, dotProduct, Matrix.one_apply]
  refine ⟨Λ, x₀, Ti, fun i => T'.submatrix id fun s => ⟨i, s⟩, B * γ.1, he, hn, hΛ, fun i k => ⟨?_, ?_, fun h => ?_⟩,
    fun i => ⟨?_, ?_, ?_⟩, hG, fun z => ⟨fun hz => ?_, ?_⟩, hS⟩
  · rw [hT, hT, hsub, h1]; rfl
  · rw [hsub, h2]; rfl
  · rw [hT, hsub, h3]
    ext r s
    simp [h]
  · rw [hT, hsub, h3]
    ext r s
    simp [Matrix.one_apply]
  · rw [← Matrix.mul_assoc, hT, ← Matrix.submatrix_id_id B, hsub, h4]
    simp
  · rw [← Matrix.mul_assoc, ← Matrix.submatrix_id_id B, hsub, h5]
    simp
  · obtain ⟨u, u', y, hu, hu', hy, rfl⟩ := hdec z hz
    obtain ⟨v, hv, hv'⟩ := (hlast _).1 hu
    have hy' : ((B * γ.1) *ᵥ fun l => e (e.symm ((γ⁻¹.1 *ᵥ y) l))) = B *ᵥ y := by
      simp only [e.apply_symm_apply]
      rw [mulVec_mulVec, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
    refine ⟨fun i s => v ⟨i, s⟩, fun i s => u' ⟨i, s⟩, fun l => e.symm ((γ⁻¹.1 *ᵥ y) l), hv, fun i t ht => ?_,
      (hx₀ _).2 (hy' ▸ hy), ?_⟩
    · rw [← hpair]
      exact (hdual _).1 hu' _ (hle _ (hone i t ht))
    · rw [hy', hv', hsum T, hsum T']
      simp only [hT]
  · rintro ⟨u, u', y, hu, hu', hy, rfl⟩
    refine add_mem (add_mem (Submodule.sum_mem _ fun i _ => hle _ (hone i _ (hu i))) ?_) ((hx₀ y).1 hy)
    have e1 := hsum T' fun s => u' s.1 s.2
    refine e1 ▸ (hdual _).2 fun w hw => ?_
    obtain ⟨v, v', y', hv, -, -, rfl⟩ := hdec w hw
    obtain ⟨t, ht, ht'⟩ := (hlast _).1 hv
    rw [star_add, star_add, add_dotProduct, add_dotProduct, form_mulVec _ T', form_mulVec _ B, h2,
      gram_swap (J_herm I) T', h5, ht', hsum T, star_sum, sum_dotProduct]
    simp only [← hT, hpair, conjTranspose_zero, zero_mulVec, dotProduct_zero, add_zero]
    exact Subring.sum_mem _ fun i _ => hu' i _ (ht i)

end GlobalTheory.AdaptedExists
end

section

open NumberField Module Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt GlobalTheory.LoopC
open scoped ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.standardBaseFlag_complement_integralLattice : ∀ (D : D7) (u u' : D.what₂.Word) (F0 : Fb D u) (Λ : LatV D), Stand D u u' → IsBase D u F0 → IsRowLat D F0 Λ → WHyp D (lf D F0) (Wsp D) ∧ Function.Injective (D.sp.iXY 0) ∧ IsPosDef (D.sp.X 0).hT ∧ Submodule.IsLattice D.host.E (L0X D Λ (lf D F0)) ∧ Formalism.HermitianLatticesTheory.IsIntegralLat (D.sp.X 0).hT (L0X D Λ (lf D F0)) ∧ detW D (L0X D Λ (lf D F0)) = NT D u ∧ Wb D = Wsp D ⊔ Submodule.span D.host.E {D.zmOf u} := by
  first | exact @GlobalTheory.LoopC.Base.main | exact GlobalTheory.LoopC.Base.main | (intros; apply GlobalTheory.LoopC.Base.main <;> assumption)
end

section

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.FamilyBound

theorem geom_le (x : ℝ) (hx : 2 ≤ x) (i : ℕ) : ∑ m ∈ Finset.range (i + 1), x ^ m ≤ 2 * x ^ i := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [Finset.sum_range_succ]
    have h0 : 0 ≤ x ^ i := by positivity
    have : 2 * x ^ i ≤ x ^ (i + 1) := by rw [pow_succ]; nlinarith
    linarith

section
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)

theorem mass_mono (d : S.Datum) (P Q : Submodule L.O S.V → Prop)
    (h : ∀ Λ, S.IsTerm d Λ → P Λ → Q Λ) : S.mass d P ≤ S.mass d Q := by
  unfold Frames.mass
  refine ENNReal.tsum_le_tsum fun o => ?_
  by_cases ho : S.IsTerm d o.out ∧ P o.out
  · rw [if_pos ho, if_pos ⟨ho.1, h _ ho.1 ho.2⟩]
  · rw [if_neg ho]; exact bot_le

theorem mass_le_sum {ι : Type} (s : Finset ι) (d : S.Datum) (P : Submodule L.O S.V → Prop)
    (Q : ι → Submodule L.O S.V → Prop)
    (h : ∀ Λ, S.IsTerm d Λ → P Λ → ∃ m ∈ s, Q m Λ) : S.mass d P ≤ ∑ m ∈ s, S.mass d (Q m) := by
  unfold Frames.mass
  rw [← Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
  refine ENNReal.tsum_le_tsum fun o => ?_
  by_cases ho : S.IsTerm d o.out ∧ P o.out
  · obtain ⟨m, hm, hq⟩ := h _ ho.1 ho.2
    rw [if_pos ho]
    refine le_trans ?_ (Finset.single_le_sum (f := fun m =>
      if S.IsTerm d o.out ∧ Q m o.out then ENNReal.ofReal (S.mu o.out) else 0) (fun _ _ => bot_le) hm)
    rw [if_pos ⟨ho.1, hq⟩]
  · rw [if_neg ho]; exact bot_le

theorem sumData_mono (φ ψ : S.Datum → ℝ≥0∞) (h : ∀ d, φ d ≤ ψ d) : S.sumData φ ≤ S.sumData ψ := by
  unfold Frames.sumData
  exact ENNReal.tsum_le_tsum fun o => by gcongr; exact h _

end

theorem family_bound : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), 4 * r + 7 ≤ k → ∀ β J βJ : ℕ, S.ampSq (S.InFF β J βJ) ≤ ENNReal.ofReal (98 * S.Hp ^ (9 * (r + 1) ^ 2 + 12 * (r + 1)) * (4 * S.Hp ^ (4 * (r + 1))) * ((S.q : ℝ) ^ (1 - ((k : ℤ) - 2 * r - 3))) ^ 2) * S.nn := by
  intro F _ _ _ _ _ E _ _ _ L r k S hk β J βJ
  by_cases hex : ∃ d Λ, S.IsTerm d Λ ∧ S.InFF β J βJ d Λ
  swap
  · have h0 : ∀ d, S.amp d (S.InFF β J βJ d) = 0 := by
      intro d
      unfold Frames.amp
      have : ∀ o : MulAction.orbitRel.Quotient S.St (Submodule L.O S.V),
          ¬ (S.IsTerm d o.out ∧ S.InFF β J βJ d o.out) := fun o ho => hex ⟨d, _, ho⟩
      simp [this]
    have : S.ampSq (S.InFF β J βJ) = 0 := by
      unfold Frames.ampSq Frames.sumData
      simp [h0]
    rw [this]; exact bot_le
  obtain ⟨d₀, Λ₀, ht, hF⟩ := hex
  obtain ⟨-, -, -, -, hH, ⟨i, -, hi⟩, hbz, -⟩ := GlobalTheory.HL.Defect.exponents_and_defect L r k S d₀ Λ₀ ht
  have hβ : β = S.q ^ i := by rw [← hF.2.1, hi]
  have hq0 : 0 < S.q := GlobalTheory.HL.SmallImage.resQ_pos S.ϖ S.ϖ_irr
  have hq1 : S.q ≠ 1 := by
    intro h
    exact hF.1.1 (hbz.2 (by rw [hi, h, one_pow]))
  have hq : 2 ≤ S.q := by omega
  have hβ1 : 1 ≤ β := by rw [hβ]; exact Nat.one_le_pow _ _ hq0
  have hk1 : 1 ≤ k := by omega
  set A0 : ℝ := S.Hp ^ (9 * (r + 1) ^ 2 + 12 * (r + 1)) with hA0
  set A1 : ℝ := 4 * S.Hp ^ (4 * (r + 1)) with hA1
  set e : ℝ := (S.q : ℝ) ^ (1 - ((k : ℤ) - 2 * r - 3)) with he
  have hA0p : 0 ≤ A0 := by positivity
  have hA1p : 0 ≤ A1 := by positivity
  have hep : 0 ≤ e := by positivity
  have hmass : ∀ d, S.mass d (S.InFF β J βJ d) ≤ ENNReal.ofReal (2 * A0 * (β : ℝ) ^ (k - 1)) := by
    intro d
    refine (mass_le_sum S (Finset.range (i + 1)) d _ (fun m Λ => S.cardI d Λ = S.q ^ m) ?_).trans ?_
    · intro Λ hΛ hP
      obtain ⟨⟨m, hm⟩, hle, -⟩ := GlobalTheory.HL.SmallImage.small_image L r k S d Λ hΛ
      refine ⟨m, ?_, hm⟩
      rw [hm, hP.2.1, hβ] at hle
      have := (Nat.pow_le_pow_iff_right (by omega)).1 hle
      exact Finset.mem_range.2 (by omega)
    · refine (Finset.sum_le_sum fun m _ => (GlobalTheory.T.hermitianDoubleCoset_mass_le_and_finite L r k S hk1 d).1 (S.q ^ m)).trans ?_
      rw [← ENNReal.ofReal_sum_of_nonneg (fun m _ => by positivity)]
      apply ENNReal.ofReal_le_ofReal
      have hx : (2 : ℝ) ≤ (S.q : ℝ) ^ (k - 1) := by
        have h2 : (2 : ℝ) ≤ S.q := by exact_mod_cast hq
        exact h2.trans (le_self_pow₀ (by linarith) (by omega))
      have hg := geom_le _ hx i
      have hc : ∀ m : ℕ, ((S.q ^ m : ℕ) : ℝ) ^ (k - 1) = ((S.q : ℝ) ^ (k - 1)) ^ m := by
        intro m; push_cast; rw [← pow_mul, ← pow_mul, mul_comm]
      rw [← Finset.mul_sum, hβ]
      simp only [hc]
      nlinarith [mul_le_mul_of_nonneg_left hg hA0p]
  have h1 := (GlobalTheory.HL.BasicIneq.basic_inequality L r k S hk1).2 (S.InFF β J βJ) _ (7 * e) (by positivity)
    hmass (fun d => GlobalTheory.T.amplitude_le_mass_secondType_family L r k S hk β J βJ d)
  have h2 : (S.sumData fun d => S.mass d (S.InFF β J βJ d)) ≤
      ENNReal.ofReal (A1 * ((β : ℝ) ^ (k - 1))⁻¹) * S.nn :=
    (sumData_mono S _ _ fun d => mass_mono S d _ _ fun Λ _ h => h.2.1).trans (GlobalTheory.T.sumData_mass_be_eq_le L r k S hk β hβ1)
  refine h1.trans ?_
  refine (mul_le_mul_right h2 _).trans ?_
  rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
  have hb : (β : ℝ) ^ (k - 1) ≠ 0 := by
    have : (0 : ℝ) < β := by exact_mod_cast hβ1
    positivity
  have : (7 * e) ^ 2 * (2 * A0 * (β : ℝ) ^ (k - 1)) * (A1 * ((β : ℝ) ^ (k - 1))⁻¹) = 98 * A0 * A1 * e ^ 2 := by
    field_simp
    ring
  rw [this]

end GlobalTheory.HL.FamilyBound
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.DSId
open scoped InnerProductSpace ComplexOrder ContDiff

theorem _root_.GlobalTheory.T.cuspidal_of_unipotent_fibre_integrals_vanish : ∀ (B : RowsAut) (d : InfinitePlace B.I.F → ℝ) (h : ℝ), IsDSData B d → (∀ (v : InfinitePlace B.I.F) (Wv : Submodule ℂ (Fin B.I.n → ℂ)), IsIsoC (B.I.ε v) Wv → ∀ ν : Measure (UJ (B.I.ε v)), IsHaarSub (NW (B.I.ε v) Wv) ν → ∀ x y : B.I.GA, ∫ m, phe B d (x * (open Classical in ((Pi.mulSingle v m, 1) : B.I.GA)) * y) ∂ν = 0) → LocDec B h → HBig B 40 h → FiniteDimensional ℂ (B.I.eHom B.σs B.μf B.fund B.R B.Re) → ∀ T, B.I.IsRConv B.μf B.fund B.R (phe B d) T → ∀ y : B.I.L2 B.μf B.fund, (∀ f : B.I.GA → ℂ, IsContRep B (T y) f → ∀ W, B.I.IsIsot W → ∀ ν : Measure B.I.GA, B.I.IsNQuotMeas W ν → ∀ x, ∫ m, f (m * x) ∂ν = 0) ∧ B.I.IsCuspFn (B.I.muA B.μf) (B.I.ext (T y)) := by
  first | exact @GlobalTheory.CuspCore.cusp_of_fibre_vanish | exact GlobalTheory.CuspCore.cusp_of_fibre_vanish | (intros; apply GlobalTheory.CuspCore.cusp_of_fibre_vanish <;> assumption)
end

section

open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.DSId
open scoped InnerProductSpace ComplexOrder

theorem _root_.GlobalTheory.T.lowestKType_infinitesimalChar_large_gap : ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsHCParam lam → IsDS ε lam σ → ∀ h : ℝ, GapAtLeast ε lam h → 120 * (n : ℝ) * ((rkR ε : ℕ) : ℝ) ^ ((3 : ℝ) / 2) ≤ h → ∀ s ∈ lowKSub ε lam σ, ∀ y : H, IsZEigen ε (fun a => (lam a : ℂ)) (fun g => ⟪y, σ g s⟫_ℂ) := by
  first | exact @GlobalTheory.DSId.LowCharGap.lowChar | exact GlobalTheory.DSId.LowCharGap.lowChar | (intros; apply GlobalTheory.DSId.LowCharGap.lowChar <;> assumption)
end
