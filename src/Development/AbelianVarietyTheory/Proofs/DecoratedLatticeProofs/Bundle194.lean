module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.T2SpaceMatrixOfIsNonarchimedeanLocalField
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle172
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle315
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle016
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsSplitChartOfBasis
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousKapSymm
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1917
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle370
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle171
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle013
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle175
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
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle162
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsPairingSingleNe
import Formalism.LocalToGlobal.IndefiniteReal.Bundle001
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle157
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes

@[expose] public section

section

open MeasureTheory ValuativeRel Matrix IsLocalRing GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (cosetInd mainDatum)
open GlobalTheory.FinPl.Comm (fpair)

theorem _root_.GlobalTheory.T.fourierPairing_dualIndicator_add_nonzeroCosets : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n : Type) [Fintype n] [DecidableEq n] (q : Unif k) (χ : AddChar k Circle), HasConductor χ 1 → ∀ (e : k), (e = 1 ∨ e = -1) → ∀ (μ : Measure (n → k)) [μ.IsAddHaarMeasure] (L : Submodule 𝒪[k] (n → k)) [L.IsLattice k], fpair χ e μ (vecInd L) (dualInd L + ∑ Q ∈ withLat L, cosetInd q Q.lat Q.red) = fpair χ e μ (vecInd L) (dualInd L) := by
  first | exact @GlobalTheory.FinPl.Comm.fpair_vecInd_dualInd_add_cosets | exact GlobalTheory.FinPl.Comm.fpair_vecInd_dualInd_add_cosets | (intros; apply GlobalTheory.FinPl.Comm.fpair_vecInd_dualInd_add_cosets <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep
open GlobalTheory.FinZeta (Gv embV Kv VacFin IsLocKer KerU)
open GlobalTheory.SphTheta (IsStd CayleyRule intMat liftPar)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke IsCommensurated Tj SatU ordL Ov)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (hyp IsVacAt UnrPl)

noncomputable section

namespace GlobalTheory.UnrPlDict

open GlobalTheory.IdemSupport

variable {D : D7}

theorem exists_glue_kill {χ : (AE D)ˣ →* Circle} {w : HeightOneSpectrum (𝓞 D.host.E)} (hu : UnrAt χ w)
    {e : AE D} (hd : GlobalTheory.IdemSupport.IsDelta (GlobalTheory.LFun.EulerTie.finComp D.host.F D.host.E) w e)
    (x : (AE D)ˣ) (h1 : finPart D (x : AE D) ∈ intAE D) (h2 : finPart D ((x⁻¹ : (AE D)ˣ) : AE D) ∈ intAE D) :
    ∃ y : (AE D)ˣ, (y : AE D) = e * (x : AE D) + (1 - e) ∧ χ y = 1 := by
  have hΦ : Comp D (GlobalTheory.LFun.EulerTie.finComp D.host.F D.host.E) := by
    obtain ⟨a, b, c, d, e⟩ := (GlobalTheory.LFun.EulerTie.comp_finComp (F := D.host.F) (E := D.host.E))
    exact ⟨a, b, c, d, e⟩
  have hm : GlobalTheory.LFun.EulerTie.finComp D.host.F D.host.E (x : AE D) w *
      GlobalTheory.LFun.EulerTie.finComp D.host.F D.host.E ((x⁻¹ : (AE D)ˣ) : AE D) w = 1 := by
    rw [← ev_mul, Units.mul_inv, map_one]
    try rfl
  let u : (w.adicCompletion D.host.E)ˣ :=
    ⟨_, _, hm, by rw [mul_comm]; exact hm⟩
  have hU : Formalism.L2.Host.IsUnitAt w u := by
    rw [GlobalTheory.LFun.EulerTie.isUnitAt_iff]
    exact ⟨(hΦ.int _).1 h1 w, (hΦ.int _).1 h2 w⟩
  refine ⟨GlobalTheory.LFun.locIdele D.host.F w u, (GlobalTheory.LFun.EulerTie.glue_eq_locIdele hd rfl).symm, ?_⟩
  have := congrArg (fun z : ℂˣ => (z : ℂ)) (hu u hU)
  exact Circle.ext this

theorem unrPl_of_unrAt : ∀ (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) (w : HeightOneSpectrum (𝓞 D.host.E)),
    w.under (𝓞 D.host.F) = v → ∀ χ : (AE D)ˣ →* Circle,
    (∀ w' : HeightOneSpectrum (𝓞 D.host.E), w'.under (𝓞 D.host.F) = v → UnrAt χ w') → UnrPl w χ := by
  intro D v w hw χ hχ e f hp x hx h1 h2
  have hΦ : Comp D (GlobalTheory.LFun.EulerTie.finComp D.host.F D.host.E) := by
    obtain ⟨a, b, c, d, e⟩ := (GlobalTheory.LFun.EulerTie.comp_finComp (F := D.host.F) (E := D.host.E))
    exact ⟨a, b, c, d, e⟩
  have hd := (of_isPrimeIdem hΦ hp).1
  rcases hp with ⟨hi, rfl⟩ | ⟨rfl, -, -⟩
  · have hd' := delta_conj hΦ hd
    obtain ⟨y, hy, hy1⟩ := exists_glue_kill (hχ w hw) hd x h1 h2
    obtain ⟨z, hz, hz1⟩ := exists_glue_kill (hχ (cP w) ((under_cP w).trans hw)) hd' x h1 h2
    have ho : e * cA D e = 0 := hi.1.2.1
    have e1 : x = y * z := Units.ext (by
      rw [Units.val_mul, hy, hz]
      linear_combination (-1 : AE D) * hx - ((x : AE D) - 1) ^ 2 * ho)
    rw [e1, map_mul, hy1, hz1, one_mul]
  · obtain ⟨y, hy, hy1⟩ := exists_glue_kill (hχ w hw) hd x h1 h2
    have e1 : x = y := Units.ext (by rw [hy]; linear_combination (-1 : AE D) * hx)
    rw [e1, hy1]

end GlobalTheory.UnrPlDict

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep
open GlobalTheory.FinZeta (Gv embV Kv VacFin IsLocKer KerU)
open GlobalTheory.SphTheta (IsStd CayleyRule intMat liftPar)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke IsCommensurated Tj SatU ordL Ov)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ChainOnto.SatInv


open GlobalTheory.LFun.ConjPlace in
theorem Tj_inv_eq_invT {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ)
    (u : (w.adicCompletion E)ˣ) (j : ℕ) (g : GL (Fin n) (w.adicCompletion E)) :
    Tj ℂ n (Ov E w) (u : w.adicCompletion E) j g⁻¹ =
      Tj ℂ n (Ov E w) (u : w.adicCompletion E) j (invT (RingEquiv.refl (w.adicCompletion E)) n g) := by
  classical
  have hK := mem_iff_invT (n := n) (RingEquiv.refl (w.adicCompletion E)) (O := Ov E w) (O' := Ov E w)
    fun _ => Iff.rfl
  have hd : invT (RingEquiv.refl (w.adicCompletion E)) n (dGL n u j)⁻¹ = dGL n u j :=
    (invT_dGL _ u j).trans (congrArg (fun v => dGL n v j) (Units.ext rfl))
  rw [Tj_apply, Tj_apply]
  refine if_congr ⟨?_, ?_⟩ rfl rfl
  · rintro ⟨a, ha, b, hb, H⟩
    refine ⟨_, (hK _).1 (inv_mem hb), _, (hK _).1 (inv_mem ha), ?_⟩
    rw [← hd, ← map_mul, ← map_mul, (invT _ n).apply_eq_iff_eq, ← inv_inv g, H]
    group
  · rintro ⟨a, ha, b, hb, H⟩
    obtain ⟨a, rfl⟩ := (invT (RingEquiv.refl (w.adicCompletion E)) n).surjective a
    obtain ⟨b, rfl⟩ := (invT (RingEquiv.refl (w.adicCompletion E)) n).surjective b
    rw [← hd, ← map_mul, ← map_mul, (invT _ n).apply_eq_iff_eq] at H
    refine ⟨_, inv_mem ((hK b).2 hb), _, inv_mem ((hK a).2 ha), ?_⟩
    rw [H]
    group


open GlobalTheory.LFun.ConjPlace in
theorem invT_invT {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ)
    (g : GL (Fin n) (w.adicCompletion E)) :
    invT (RingEquiv.refl (w.adicCompletion E)) n (invT (RingEquiv.refl (w.adicCompletion E)) n g) = g :=
  Units.ext (Matrix.ext fun i j => by
    rw [invT_val, ← map_inv, invT_val, inv_inv]; rfl)


open GlobalTheory.LFun.ConjPlace in
theorem heckeVec_inv_eq {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ) (V : Type)
    [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin n) (w.adicCompletion E)) V) (x : V)
    (hx : x ∈ fixed ρ (KGL w (n := n))) {ϖ : w.adicCompletion E} (hϖ : IsUnifV E w ϖ) (j : ℕ) :
    heckeVec ρ (KGL w (n := n)) (fun g => Tj ℂ n (Ov E w) ϖ j g⁻¹) x =
      heckeVec (ρ.comp (invT (RingEquiv.refl (w.adicCompletion E)) n).symm.toMonoidHom) (KGL w (n := n))
        (Tj ℂ n (Ov E w) ϖ j) x := by
  have hK := mem_iff_invT (n := n) (RingEquiv.refl (w.adicCompletion E)) (O := Ov E w) (O' := Ov E w)
    fun _ => Iff.rfl
  rw [heckeVec_comp_symm _ hK (Tj_mem_hecke hϖ j).1 hx]
  obtain ⟨u, rfl⟩ : ∃ u : (w.adicCompletion E)ˣ, (u : w.adicCompletion E) = ϖ :=
    ⟨Units.mk0 ϖ fun e => by simp [IsUnifV, e] at hϖ, rfl⟩
  congr 1
  funext g
  exact Tj_inv_eq_invT w n u j g

open GlobalTheory.LFun.ConjPlace in
theorem satVec_iff_inv : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin n) (w.adicCompletion E)) V) (x : V) (B : Multiset ℂˣ), x ≠ 0 → x ∈ fixed ρ (KGL w (n := n)) → B.card = n → (IsSatVecGL w ρ x B ↔ ∀ ϖ, IsUnifV E w ϖ → ∀ j ≤ n, heckeVec ρ (KGL w (n := n)) (fun g => Tj ℂ n (Ov E w) ϖ j g⁻¹) x = satEig (qV E w) n (B.map (·⁻¹)) j • x) := by
  intro E _ _ w n V _ _ ρ x B h0 hx hB
  have hK := mem_iff_invT (n := n) (RingEquiv.refl (w.adicCompletion E)) (O := Ov E w) (O' := Ov E w)
    fun _ => Iff.rfl
  let ρ' := ρ.comp (invT (RingEquiv.refl (w.adicCompletion E)) n).symm.toMonoidHom
  have hx' : x ∈ fixed ρ' (KGL w (n := n)) := (mem_fixed_comp_symm _ hK).2 hx
  have hs : ∀ g, (invT (RingEquiv.refl (w.adicCompletion E)) n).symm g =
      invT (RingEquiv.refl (w.adicCompletion E)) n g := fun g =>
    (MulEquiv.symm_apply_eq _).2 (invT_invT w n g).symm
  have hρ : ρ'.comp (invT (RingEquiv.refl (w.adicCompletion E)) n).symm.toMonoidHom = ρ := MonoidHom.ext fun g => by
    simp only [ρ', MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, hs, invT_invT]
  constructor
  · intro h ϖ hϖ j hj
    rw [heckeVec_inv_eq w n V ρ x hx hϖ j]
    exact (isSatVecGL_invT (.refl _) (fun _ => rfl) rfl h).2.2.2 ϖ hϖ j hj
  · intro h
    have h1 : IsSatVecGL w ρ' x (B.map (·⁻¹)) :=
      ⟨h0, hx', by simpa using hB, fun ϖ hϖ j hj => (heckeVec_inv_eq w n V ρ x hx hϖ j).symm.trans (h ϖ hϖ j hj)⟩
    have h2 := isSatVecGL_invT (.refl _) (fun _ => rfl) rfl h1
    rw [hρ, Multiset.map_map] at h2
    simpa using h2

end GlobalTheory.ChainOnto.SatInv
end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

namespace GlobalTheory.TargetIsom

open GlobalTheory.Mem.Isom

variable {D : D7}

theorem entries_fix {A : Type} [CommRing A] {m n : ℕ} (c : A) {M : Matrix (Fin n) (Fin n) A} (hM : ∀ i j, c * M i j = M i j)
    (P : Matrix (Fin m) (Fin n) A) (Q : Matrix (Fin n) (Fin m) A) (i j : Fin m) : c * (P * M * Q) i j = (P * M * Q) i j := by
  simp only [Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  conv_rhs => rw [← hM l k]
  ring

theorem entries_fix' {A : Type} [CommRing A] {m n k : ℕ} (c : A) {M : Matrix (Fin n) (Fin k) A} (hM : ∀ i j, c * M i j = M i j)
    (P : Matrix (Fin m) (Fin n) A) (i : Fin m) (j : Fin k) : c * (P * M) i j = (P * M) i j := by
  simp only [Matrix.mul_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  conv_rhs => rw [← hM l j]
  ring

theorem sub_one_conj {A : Type} [CommRing A] {m n : ℕ} {P : Matrix (Fin m) (Fin n) A} {Q : Matrix (Fin n) (Fin m) A} (PQ : P * Q = 1)
    (M : Matrix (Fin n) (Fin n) A) : P * M * Q - 1 = P * (M - 1) * Q := by
  rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, PQ]

theorem det_conj_rect {A : Type} [CommRing A] {m n : ℕ} (h : n = m) {P : Matrix (Fin m) (Fin n) A} {Q : Matrix (Fin n) (Fin m) A}
    (QP : Q * P = 1) (M : Matrix (Fin n) (Fin n) A) : (P * M * Q).det = M.det := by
  subst h
  rw [Matrix.det_mul, Matrix.det_mul, mul_comm (P.det), mul_assoc, ← Matrix.det_mul, mul_eq_one_comm.1 QP, Matrix.det_one, mul_one]

theorem isThetaFunO_tr {V V' : HSp D} (I : IsoMat V V') (S : HSp D) {ψ : AddChar (AF D.host.F) ℂ} {f : WO S V → ℂ}
    (hf : IsThetaFunO ψ S V f) : IsThetaFunO ψ S V' (I.trW S f) := by
  have hinf : ∀ w : WO S V', w.map (infPart D) = 0 → ((I.phi S).symm w).map (infPart D) = 0 := fun w h => by
    show (HMul.hMul I.aQ w).map (infPart D) = 0
    rw [Matrix.map_mul, h, Matrix.mul_zero]
  have hfin : ∀ w : WO S V', w.map (finPart D) = 0 → ((I.phi S).symm w).map (finPart D) = 0 := fun w h => by
    show (HMul.hMul I.aQ w).map (finPart D) = 0
    rw [Matrix.map_mul, h, Matrix.mul_zero]
  refine ⟨fun γ w => ?_, ?_, hf.cont.comp (I.continuous_phi_symm S), fun k L hL h0 w => ?_⟩
  · obtain ⟨w, rfl⟩ := (I.phi S).surjective w
    have e : ratW V' S γ = I.phi S (ratW V S (I.Q * γ)) := by
      rw [IsoMat.phi_ratW, ← Matrix.mul_assoc, I.PQ, Matrix.one_mul]
    rw [e, ← map_add (f := _), I.symplOH_phi]
    simp only [IsoMat.trW, AddEquiv.symm_apply_apply]
    exact hf.quasi _ _
  · obtain ⟨U, hU, e⟩ := hf.level
    refine ⟨U.map (I.phi S).toAddMonoidHom, ?_, ?_⟩
    · have e : ((U.map (I.phi S).toAddMonoidHom : AddSubgroup (WO S V')) : Set (WO S V')) = (I.phi S).symm ⁻¹' U := by
        ext w
        simp only [AddSubgroup.coe_map, Set.mem_image, Set.mem_preimage, SetLike.mem_coe]
        constructor
        · rintro ⟨u, hu, rfl⟩
          simpa using hu
        · intro hw
          exact ⟨_, hw, by simp⟩
      rw [e]
      exact hU.preimage (I.continuous_phi_symm S)
    · rintro _ ⟨u, hu, rfl⟩ h0
      have h1 : u.map (infPart D) = 0 := by
        have := hinf _ h0
        simpa using this
      show heisO ψ S V' (I.phi S u) (I.trW S f) = I.trW S f
      rw [I.heisO_trW, e u hu h1]
  · have := hf.smooth k ((I.phi S).symm.toAddMonoidHom.comp L) ((I.continuous_phi_symm S).comp hL) (fun t => hfin _ (h0 t))
      ((I.phi S).symm w)
    simpa [IsoMat.trW] using this

theorem isWeilDatumO_tr {V V' : HSp D} (I : IsoMat V V') (S : HSp D) {ψ : AddChar (AF D.host.F) ℂ} {χ χ' : (AE D)ˣ →* Circle}
    {om : GA D S × GA D V →* Module.End ℂ (WO S V → ℂ)}
    (h : IsWeilDatumO ψ S V χ χ' om) : IsWeilDatumO ψ S V' χ χ' (I.omT S om) := by
  have hT : ∀ f, IsThetaFunO ψ S V' f → IsThetaFunO ψ S V (I.symm.trW S f) := fun f hf => isThetaFunO_tr I.symm S hf
  refine ⟨h.std, h.hecS, h.hecT, h.resS, I.rank_eq ▸ h.resT, fun p f hf => ?_, fun g k w₀ f hf => ?_, fun γ hγ γ' hγ' f hf => ?_,
    fun f hf w => ?_, fun μ 𝓕 hμ h𝓕 p f hf => ?_, fun e he g k hg hk x y hx hy => ?_⟩
  · exact isThetaFunO_tr I S (h.om_pres _ _ (hT f hf))
  · rw [IsoMat.omT_apply, IsoMat.omT_apply, ← I.symm.heisO_trW S ψ w₀ f, h.om_heis _ _ _ _ (hT f hf), ← I.heisO_trW, I.actO_phi]
    congr 2
    · exact I.kap.apply_symm_apply k
    · exact (I.phi S).apply_symm_apply w₀
  · rw [IsoMat.omT_apply]
    show om (γ, I.kap.symm γ') (I.symm.trW S f) ((I.phi S).symm 0) = f 0
    have := h.om_aut γ hγ (I.kap.symm γ') (I.symm.kap_mem_GQ hγ') _ (hT f hf)
    rw [map_zero, this]
    show f ((I.phi S) 0) = f 0
    rw [map_zero]
  · exact (h.om_cont _ (hT f hf) ((I.phi S).symm w)).comp
      (continuous_fst.prodMk ((I.continuous_kap_symm).comp continuous_snd))
  · obtain ⟨ν, 𝓖, hν, h𝓖, hu⟩ := GlobalTheory.Mem.Isom.haar_fd_phi D V V' I S μ 𝓕 hμ h𝓕
    have e1 := hu fun x => ‖om (p.1, I.kap.symm p.2) (I.symm.trW S f) x‖ₑ ^ 2
    have e2 := hu fun x => ‖I.symm.trW S f x‖ₑ ^ 2
    have e3 : ∀ w, I.symm.trW S f ((I.phi S).symm w) = f w := fun w => congrArg f ((I.phi S).apply_symm_apply w)
    simp only [e3] at e2
    rw [IsoMat.omT_apply]
    exact e1.trans ((h.om_unit ν 𝓖 hν h𝓖 _ _ (hT f hf)).trans e2.symm)
  · have e0 : mt V (I.kap.symm k) - 1 = _ := sub_one_conj I.aQ_aP (mt V' k)
    have hsupp : SuppAt e V (I.kap.symm k) := fun i j => by
      unfold SuppAt at hk
      rw [e0]
      exact entries_fix _ hk _ _ i j
    have e1 : (mt V (I.kap.symm k)).det = (mt V' k).det := det_conj_rect I.rank_eq.symm I.aP_aQ (mt V' k)
    have hdet : IsDetAt e V (I.kap.symm k) y := by
      unfold IsDetAt at hy ⊢
      rw [e1]
      exact hy
    obtain ⟨r, hr, H⟩ := h.om_split e he g (I.kap.symm k) hg hsupp x y hx hdet
    refine ⟨r, hr, fun ℓ hℓ f hf => ?_⟩
    have hinv : ∀ u : WO S V, (∀ i j, cA D e * u i j = u i j) → ∀ f, IsThetaFunO ψ S V f →
        (ℓ ∘ₗ I.trL S) (heisO ψ S V u f) = (ℓ ∘ₗ I.trL S) f := by
      intro u hu f hf
      show ℓ (I.trW S (heisO ψ S V u f)) = ℓ (I.trW S f)
      rw [← I.heisO_trW]
      exact hℓ _ (fun i j => entries_fix' _ hu I.aP i j) _ (isThetaFunO_tr I S hf)
    have := H (ℓ ∘ₗ I.trL S) hinv _ (hT f hf)
    have e1 : (ℓ ∘ₗ I.trL S) (I.symm.trW S f) = ℓ f := congrArg ℓ (I.symm.trW_symm_trW S f)
    rw [e1] at this
    exact this

variable {T T₀ : HSp D} (d : HypDec T T₀ 0)

theorem mul_fin_zero {m n : ℕ} (A : Matrix (Fin m) (Fin 0) D.host.E) (B : Matrix (Fin 0) (Fin n) D.host.E) : A * B = 0 := by
  ext i j; simp [Matrix.mul_apply]

theorem mul_fin_zero' {m n : ℕ} (A : Mx D m 0) (B : Mx D 0 n) : A ⬝ B = 0 := by
  ext i j; simp [Matrix.mul_apply]

theorem wittHyperbolicRankZero_proj_mul_emb : d.q0 * d.i₀ = 1 := rat_injective (by rw [rat_mul, rat_one]; exact d.p0_j0)

theorem wittHyperbolicRankZero_emb_mul_proj : d.i₀ * d.q0 = 1 := by
  have h := d.sum_eq_one_rat
  rwa [mul_fin_zero, mul_fin_zero, zero_add, add_zero] at h

def iso : IsoMat T₀ T where
  P := d.i₀
  Q := d.q0
  PQ := wittHyperbolicRankZero_emb_mul_proj d
  QP := wittHyperbolicRankZero_proj_mul_emb d
  gram := d.iso

theorem kap_eq (h : GA D T₀) : (iso d).kap h = d.emb0 h := by
  apply mt_injective T
  rw [IsoMat.mt_kap, IsoMat.conjM_apply, HypDec.unitaryMatrix_wittCoreEmbedding, mul_fin_zero' d.jX, mul_fin_zero' d.jY, zero_add, add_zero]
  rfl

end GlobalTheory.TargetIsom

open GlobalTheory.TargetIsom in
theorem GlobalTheory.TargetIsom.transport : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T T₀ : HSp D) (d : HypDec T T₀ 0), IsStdChar D ψ (-1) → Function.Bijective (d.inc0 S) ∧ (∀ f : WO S T → ℂ, IsThetaFunO ψ S T₀ (fun w => f (d.inc0 S w)) ↔ IsThetaFunO ψ S T f) ∧ ∀ (χS χT : (AE D)ˣ →* Circle) (om : Om S T) (om₀ : Om S T₀), IsWeilDatumO ψ S T χS χT om → IsWeilDatumO ψ S T₀ χS χT om₀ → ∀ g h f, IsThetaFunO ψ S T f → om₀ (g, h) (fun w => f (d.inc0 S w)) = fun w => om (g, d.emb0 h) f (d.inc0 S w) := by
  intro D ψ S T T₀ d hψ
  have hphi : (d.inc0 S : WO S T₀ → WO S T) = (iso d).phi S := funext fun w => rfl
  refine ⟨hphi ▸ ((iso d).phi S).bijective, fun f => ⟨fun hf => ?_, fun hf => ?_⟩, fun χS χT om om₀ hom hom₀ g h f hf => ?_⟩
  · have := isThetaFunO_tr (iso d) S hf
    convert this using 1
    funext w
    show f w = f ((iso d).phi S (((iso d).phi S).symm w))
    rw [AddEquiv.apply_symm_apply]
  · exact isThetaFunO_tr (iso d).symm S hf
  · have hT := isWeilDatumO_tr (iso d).symm S hom
    have hf0 : IsThetaFunO ψ S T₀ (fun w => f (d.inc0 S w)) := isThetaFunO_tr (iso d).symm S hf
    rw [GlobalTheory.WeilUniq.weilDatum_unique D ψ hψ S T₀ χS χT om₀ _ hom₀ hT (g, h) _ hf0]
    funext w
    rw [GlobalTheory.Mem.Isom.IsoMat.omT_apply]
    have e1 : ((iso d).symm.kap.symm h) = d.emb0 h := kap_eq d h
    have e2 : (iso d).symm.symm.trW S (fun w => f (d.inc0 S w)) = f := (iso d).symm.trW_symm_trW S f
    rw [e1, e2]
    rfl
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl IsDedekindDomain NumberField GlobalTheory.FixedUnitNorm
open scoped TensorProduct

theorem _root_.GlobalTheory.T.exists_integer_of_relative_trace_norm_integral : ∀ (D : D7) (w : D.host.E) (t n : 𝓞 D.host.F), w + D.sp.cm.sig w = algebraMap D.host.F D.host.E t → w * D.sp.cm.sig w = algebraMap D.host.F D.host.E n → ∃ x : 𝓞 D.host.E, (x : D.host.E) = w := by
  first | exact @GlobalTheory.FixedUnitNorm.integral_of_trace_norm_integral | exact GlobalTheory.FixedUnitNorm.integral_of_trace_norm_integral | (intros; apply GlobalTheory.FixedUnitNorm.integral_of_trace_norm_integral <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ChainOnto.FrameAct

theorem mt_one' {D : D7} (V : HSp D) : Formalism.L2.Theta.mt V 1 = 1 := by
  show (matHom V 1).1 = 1
  simp

theorem finE_inv_val' {D : D7} (V : HSp D) (g : GA D V) :
    ((Lev.finE V g)⁻¹).1 = (Formalism.L2.Theta.mt V g⁻¹).map (toEAf D) := by
  rw [← map_inv]; rfl

theorem conj_inv_val' {D : D7} {n : ℕ} (β y : GL (Fin n) (Lev.EAf D)) :
    ((β⁻¹ * y * β)⁻¹ : GL (Fin n) (Lev.EAf D)).1 = (β⁻¹).1 * (y⁻¹).1 * β.1 := by
  rw [_root_.mul_inv_rev, _root_.mul_inv_rev, inv_inv, Units.val_mul, Units.val_mul, Matrix.mul_assoc]

theorem frMapO_actO_left : ∀ (D : D7) (S T : HSp D) (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)) (g : GA D S) (x : WO S T), frMapO S T βS βT (actO S T g 1 x) = HMul.hMul (frMapO S T βS βT x) ((βS⁻¹ * Lev.finE S g * βS)⁻¹ : GL (Fin S.rank) (Lev.EAf D)).val := by
  intro D S T βS βT g x
  rw [frMapO, frMapO, actO, mt_one', Matrix.one_mul, Matrix.map_mul, conj_inv_val', finE_inv_val']
  have hb : βS.1 * (βS⁻¹).1 = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc βS.1, hb, Matrix.one_mul]

end GlobalTheory.ChainOnto.FrameAct
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.frameMatrix_weilPairAction_left_inv : ∀ (D : D7) (S T : HSp D) (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)) (g : GA D S) (x : WO S T), frMapO S T βS βT (actO S T g 1 x) = HMul.hMul (frMapO S T βS βT x) ((βS⁻¹ * Lev.finE S g * βS)⁻¹ : GL (Fin S.rank) (Lev.EAf D)).val := by
  intro D S T βS βT g x
  have mt_one' : Formalism.L2.Theta.mt T 1 = 1 := by
    show (matHom T 1).1 = 1
    simp
  have finE_inv_val' : ((Lev.finE S g)⁻¹).1 = (Formalism.L2.Theta.mt S g⁻¹).map (toEAf D) := by
    rw [← map_inv]; rfl
  have conj_inv_val' : ((βS⁻¹ * Lev.finE S g * βS)⁻¹ : GL (Fin S.rank) (Lev.EAf D)).1 = (βS⁻¹).1 * ((Lev.finE S g)⁻¹).1 * βS.1 := by
    rw [_root_.mul_inv_rev, _root_.mul_inv_rev, inv_inv, Units.val_mul, Units.val_mul, Matrix.mul_assoc]
  rw [frMapO, frMapO, actO, mt_one', Matrix.one_mul, Matrix.map_mul, conj_inv_val', finE_inv_val']
  have hb : βS.1 * (βS⁻¹).1 = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc βS.1, hb, Matrix.one_mul]
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.multiplicity_map_right_translate_real_point : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (J : Set (GA D V)) (χ : GA D V → ℂ) (T : MMap M), IsMultMap θ M J χ T → ∀ k ∈ GinfC V, ∀ v : M.Vec, ∃ v' : M.Vec, (∀ τ, (v' τ : M.H τ) = M.rep τ (infMat D.sp.cm.sig V.gram (θ τ) k) (v τ)) ∧ ∀ x, T v (x * k) = T v' x := by
  first | exact @GlobalTheory.RealPointMove.translate_eq_move | exact GlobalTheory.RealPointMove.translate_eq_move | (intros; apply GlobalTheory.RealPointMove.translate_eq_move <;> assumption)
end
