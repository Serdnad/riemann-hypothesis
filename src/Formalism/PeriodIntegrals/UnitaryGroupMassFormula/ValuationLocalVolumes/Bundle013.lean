module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.Bundle008
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.Bundle003
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.FibPOfDual
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.Bundle007
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle021
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.Bundle015
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.Bundle006
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.NearTIff
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.NormOneUnitFixedPoints
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.Bundle010
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.TrPerfOfRes
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SelfDualContinuity.SdExistsHolds
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.CfCoe

@[expose] public section

section

noncomputable section

namespace PI.OmVd

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain MeasureTheory PI.OmLocU
  PI.OmLocU.Orb
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F)) (Λ : Set (Fin n → E))

def augT {a : ℕ} (X : TupV (E := E) v n a) (w : Fin n → Fv F v ⊗[F] E) : TupV (E := E) v n (a + 1) :=
  Fin.snoc (α := fun _ => Fin n → Fv F v ⊗[F] E) X w

theorem augT_castSucc {a : ℕ} (X : TupV (E := E) v n a) (w : Fin n → Fv F v ⊗[F] E) (i : Fin a) :
    augT v X w i.castSucc = X i := by
  simp [augT]

def IsoExt (a : ℕ) (Y : TupV (E := E) v n a) : Prop :=
  GoodP σ J ψ v Λ a Y → ∃ T : Matrix (Fin (a + 1)) (Fin (a + 1)) (Fv F v ⊗[F] E),
    (∃ u ∈ OEv (E := E) v, T.det ∈ OEv (E := E) v ∧ T.det * u = 1) ∧
    ∀ X ∈ PrimT v Λ a, gramR (Fv F v) σ J X = gramR (Fv F v) σ J Y →
      ∃ w : Fin n → Fv F v ⊗[F] E, IsPrim v Λ (augT v X w) ∧ gramR (Fv F v) σ J (augT v X w) = T

theorem extP_of (a : ℕ) (Y : TupV (E := E) v n a) (hn : a + 1 ≤ n) (hI : IsoExt σ J ψ v Λ a Y) :
    ExtP σ J ψ v Λ a Y := by
  intro h hG
  have hR : Red.ResAlg σ J ψ v := Red.resAlg_of_sp σ J ψ v (Red.etaSp_holds σ J ψ v)
  have hU : UnitV σ J ψ v Λ :=
    unitV_of σ J ψ v Λ (PI.OmLocU.NormOneUnitFixedPoints.normOne_of σ J ψ v hR) (UnN.unitNorm_of_res σ J ψ v Λ hR)
  obtain ⟨T, hTu, hext⟩ := hI hG
  obtain ⟨hS, hL, hSD, hUn, -, hP⟩ := hG
  obtain ⟨wY, hPY, hgY⟩ := hext Y hP rfl
  have hGY : GoodY σ J ψ v Λ (a + 1) (augT v Y wY) := ⟨hS, hL, hSD, hUn, hn, hPY, by rw [hgY]; exact hTu⟩
  have hE := extOrth_of σ J ψ v Λ (a + 1) (augT v Y wY) (oSub (E := E) v) (oSmul v Λ)
    (orthoB_of σ J ψ v Λ (a + 1) (augT v Y wY) hU)
  have hT : IsUnit (gramR (Fv F v) σ J (augT v Y wY)).det := by
    obtain ⟨u, -, -, hu⟩ := hTu
    rw [hgY]
    exact ⟨⟨_, u, hu, by rw [mul_comm]; exact hu⟩, rfl⟩
  refine ⟨gT v hn (gramR (Fv F v) σ J (augT v Y wY)), fun X hX hXY => ?_⟩
  obtain ⟨wX, hPX, hgX⟩ := hext X hX hXY
  obtain ⟨Z, hZb, hZe, hZg⟩ := hE hn hGY (augT v X wX) hPX.1 (by rw [hgX, hgY])
  refine ⟨Z, hZb, fun i => ?_, hZg, isUnit_det_colM σ J v hn _ hT Z hZg⟩
  have e1 : eSp h (Sum.inl i) = eSp hn (Sum.inl i.castSucc) := by
    apply Fin.ext
    simp [eSp]
  rw [e1, hZe i.castSucc, augT_castSucc]

end PI.OmVd
end
end

section

noncomputable section

namespace PI.OmVg

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain PI.OmLocU PI.OmLocU.Red
  PI.VolStabSW
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F)) (Λ : Set (Fin n → E))

theorem card_clsP (hL : ∃ L : Submodule (𝓞 E) (Fin n → E), Submodule.IsLattice E L ∧ (L : Set (Fin n → E)) = Λ)
    (hcm : IsCMExt F E σ) (hJ : ∀ i j, σ (J j i) = J i j) (hSD : IsSDLoc σ J v Λ)
    {e : Fin n → Fin n → Fv F v ⊗[F] E} (he : Orb.IsOBas v Λ e) (he1 : gramR (Fv F v) σ J e = 1)
    {ϖ : Fv F v} (hϖ : IsUnif v ϖ) {K : Type} [CommRing K] (τ : K →+* K) (π : OR (E := E) v →+* K)
    (hπ : IsRes σ v ϖ τ π) {a : ℕ} (T : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E))
    (hT : ∀ i j, T i j ∈ OR (E := E) v) :
    Nat.card (PI.OmVd.clsP σ J v Λ a ϖ T) =
      Nat.card {X : Fin a → Fin n → K //
        ffGram τ 1 X = (fun i j => π ⟨T i j, hT i j⟩) ∧ LinearIndependent K X} := by
  set Φ := phi σ J v Λ hSD he π a with hΦ
  let eq : (lamA v Λ a ⧸ (lamP v Λ a ϖ).addSubgroupOf (lamA v Λ a)) ≃+ (Fin a → Fin n → K) :=
    (QuotientAddGroup.quotientAddEquivOfEq (phi_ker σ J v Λ hSD he he1 hπ a)).trans
      (QuotientAddGroup.quotientKerEquivOfSurjective Φ (phi_surj σ J v Λ hSD he he1 hπ a))
  have heq : ∀ x : lamA v Λ a, eq (QuotientAddGroup.mk x) = Φ x := fun x => rfl
  set P : (Fin a → Fin n → K) → Prop := fun M =>
    ffGram τ 1 M = (fun i j => π ⟨T i j, hT i j⟩) ∧ LinearIndependent K M with hP
  have hset : PI.OmVd.clsP σ J v Λ a ϖ T = {q | P (eq q)} := by
    ext q
    induction q using QuotientAddGroup.induction_on with
    | H x =>
      constructor
      · rintro ⟨y, ⟨hyP, hyN⟩, hyx⟩
        show P (eq (QuotientAddGroup.mk x))
        rw [← hyx, heq]
        exact ⟨(nearT_iff σ J v Λ hcm hJ hSD he he1 hπ T hT y).1 hyN,
          (prim_iff σ J v Λ hSD he he1 hL hϖ hπ y).1 hyP⟩
      · intro hx
        have h2 : P (eq (QuotientAddGroup.mk x)) := hx
        rw [heq] at h2
        exact ⟨x, ⟨(prim_iff σ J v Λ hSD he he1 hL hϖ hπ x).2 h2.2,
          (nearT_iff σ J v Λ hcm hJ hSD he he1 hπ T hT x).2 h2.1⟩, rfl⟩
  rw [hset]
  exact Nat.card_congr (Equiv.subtypeEquiv (p := fun q => q ∈ {q | P (eq q)}) eq.toEquiv (fun q => Iff.rfl))

def GramCor (ϖ : Fv F v) {a : ℕ} (T : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) : Prop :=
  ∃ i₀ : Fin a, (∀ j, T i₀ j ∈ PO (E := E) v ϖ) ∧ (∀ j, T j i₀ ∈ PO (E := E) v ϖ) ∧
    ∃ w ∈ OEv (E := E) v, (T + Matrix.single i₀ i₀ 1).det * w = 1

theorem corOne_red {ϖ : Fv F v} {K : Type} [CommRing K] {τ : K →+* K} {π : OR (E := E) v →+* K}
    (hπ : IsRes σ v ϖ τ π) {a : ℕ} (T : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E))
    (hT : ∀ i j, T i j ∈ OR (E := E) v) (hC : GramCor v ϖ T) :
    PI.OmVd.CorOne (fun i j => π ⟨T i j, hT i j⟩ : Matrix (Fin a) (Fin a) K) := by
  obtain ⟨i₀, hr, hc, w, hw, hd⟩ := hC
  refine ⟨i₀, fun j => (hπ.2.1 _).2 (hr j), fun j => (hπ.2.1 _).2 (hc j), ?_⟩
  have hT' : ∀ i j, (T + Matrix.single i₀ i₀ 1 : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) i j ∈ OR (E := E) v := by
    intro i j
    rw [Matrix.add_apply, Matrix.single_apply]
    split_ifs
    · exact (OR (E := E) v).add_mem (hT i j) (OR (E := E) v).one_mem
    · simpa using hT i j
  convert det_red v π _ hT' hw hd using 2
  congr 1
  ext i j
  by_cases h : i₀ = i ∧ i₀ = j
  · obtain ⟨h1', h2'⟩ := h
    subst h1'
    subst h2'
    have h1 : (⟨(T + Matrix.single i₀ i₀ 1 : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) i₀ i₀, hT' i₀ i₀⟩ :
        OR (E := E) v) = ⟨T i₀ i₀, hT i₀ i₀⟩ + 1 := by
      apply Subtype.ext
      simp [Matrix.add_apply]
    rw [h1, map_add (f := _), map_one]
    show π ⟨T i₀ i₀, hT i₀ i₀⟩ + (Matrix.single i₀ i₀ 1 : Matrix (Fin a) (Fin a) K) i₀ i₀ = _
    simp
  · have h1 : (⟨(T + Matrix.single i₀ i₀ 1 : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) i j, hT' i j⟩ :
        OR (E := E) v) = ⟨T i j, hT i j⟩ := by
      apply Subtype.ext
      simp [Matrix.add_apply, Matrix.single_apply, h]
    rw [h1]
    show π ⟨T i j, hT i j⟩ + (Matrix.single i₀ i₀ 1 : Matrix (Fin a) (Fin a) K) i j = _
    simp [Matrix.single_apply, h]

theorem redP_of_gramCor (a : ℕ) (Y : TupV (E := E) v n a)
    (hC : ∀ ϖ : Fv F v, IsUnif v ϖ → GramCor v ϖ (gramR (Fv F v) σ J Y)) :
    PI.OmVd.RedP σ J ψ v Λ a Y := by
  intro hG ϖ hϖ
  have hR : ResAlg σ J ψ v := resAlg_of_sp σ J ψ v (etaSp_holds σ J ψ v)
  have hU : Orb.UnitV σ J ψ v Λ :=
    Orb.unitV_of σ J ψ v Λ (NormOneUnitFixedPoints.normOne_of σ J ψ v hR) (UnN.unitNorm_of_res σ J ψ v Λ hR)
  have hstd := hG.1
  have hcm := hstd.1
  have hJ : ∀ i j, σ (J j i) = J i j := hstd.2.1.1
  have hL := hG.2.1
  have hSD : IsSDLoc σ J v Λ := hG.2.2.1
  obtain ⟨e, he, he1⟩ := oBas1_of_unitV σ J ψ v Λ hU hstd hL hSD hG.2.2.2.1
  have hY := hG.2.2.2.2.2.1
  have hT : ∀ i j, gramR (Fv F v) σ J Y i j ∈ OR (E := E) v := fun i j =>
    (hSD (Y j)).1 (hY j) (Y i) (hY i)
  have hconj : ∀ i j, gramR (Fv F v) σ J Y i j = _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Fv F v) σ (gramR (Fv F v) σ J Y j i) := fun i j =>
    (Orb.hR_conj σ J v hcm hJ (Y j) (Y i)).symm
  obtain ⟨k, _, _, hk, h⟩ := hR hstd hG.2.2.2.1 ϖ hϖ
  refine ⟨k, inferInstance, inferInstance, hk, ?_⟩
  rcases h with ⟨hη, K, _, _, σ', π, hσ, h2, hne, hπ⟩ | ⟨hη, π, hπ⟩
  · refine Or.inl ⟨hη, K, inferInstance, inferInstance, σ', 1, fun i j => π ⟨_, hT i j⟩, hσ, h2, hne, ?_,
      by simp, ?_, corOne_red σ v hπ _ hT (hC ϖ hϖ),
      card_clsP σ J v Λ hL hcm hJ hSD he he1 hϖ (σ' : K →+* K) π hπ _ hT⟩
    · intro i j
      by_cases h : i = j
      · subst h; simp
      · simp [h, Ne.symm h]
    · intro i j
      exact (hπ.2.2 _ _ (hconj i j)).symm
  · refine Or.inr ⟨hη, 1, fun i j => π ⟨_, hT i j⟩, ?_, by simp, ?_, corOne_red σ v hπ _ hT (hC ϖ hϖ),
      card_clsP σ J v Λ hL hcm hJ hSD he he1 hϖ (RingEquiv.prodComm (R := k) (S := k)).toRingHom π hπ _ hT⟩
    · intro i j
      by_cases h : i = j
      · subst h; ext <;> simp
      · ext <;> simp [h, Ne.symm h]
    · intro i j
      exact (hπ.2.2 _ _ (hconj i j)).symm

end PI.OmVg
end
end

section

noncomputable section

namespace PI.OmVd

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain MeasureTheory PI.OmLocU
open Formalism.L2.SG.Pf.NcVal.OmVSt Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.TypedSets
open scoped TensorProduct

variable {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ)

theorem omVdEx_holds : OmVdEx X ψ := fun v hS =>
  ⟨(PI.SelfDualBridge.W.sdExists_holds X.B.I.cm.sig X.B.I.J ψ v (D.R.rS + 1 + D.R.rS) (Fin 1) hS).1,
    (PI.SelfDualBridge.W.sdExists_holds X.B.I.cm.sig X.B.I.J ψ v (D.R.rS + 1 + D.R.rS) (Fin 1) hS).2.1⟩

theorem omVdUniq_holds : OmVdUniq X ψ := fun v => omUnique X.B.I.cm.sig X.B.I.J ψ v (D.R.rS + 1 + D.R.rS)

theorem omVdSdW_holds : OmVdSdW X ψ := fun v =>
  SdB.sdVolW_of_perf X.B.I.cm.sig X.B.I.J ψ v (abelian₂ X) (D.R.rS + 1 + D.R.rS)
    (SdB.trPerf_of_res X.B.I.cm.sig X.B.I.J ψ v
      (Red.resAlg_of_sp X.B.I.cm.sig X.B.I.J ψ v (Red.etaSp_holds X.B.I.cm.sig X.B.I.J ψ v)))

theorem omVdSdH_holds : OmVdSdH X ψ := fun v =>
  SdB.sdVolH_of_perf X.B.I.cm.sig X.B.I.J ψ v (D.R.rS + 1 + D.R.rS)
    (SdB.trPerf_of_res X.B.I.cm.sig X.B.I.J ψ v
      (Red.resAlg_of_sp X.B.I.cm.sig X.B.I.J ψ v (Red.etaSp_holds X.B.I.cm.sig X.B.I.J ψ v)))

theorem omVBadT_of_steps (hStd : OmVStd X ψ) (hLat : OmVLat X) (hGram : OmVGram X u')
    (hExt : ∀ v : PlX X, ((Tw u' : ℕ) : 𝓞 X.B.I.F) ∈ v.asIdeal →
      ExtP X.B.I.cm.sig X.B.I.J ψ v (abelian₂ X) (D.R.rS + 1 + D.R.rS) (yTup X u' v))
    (hPC : ∀ v : PlX X, PrimCos X.B.I.cm.sig X.B.I.J ψ v (abelian₂ X) (D.R.rS + 1 + D.R.rS))
    (hPD : ∀ v : PlX X, PrimDual X.B.I.cm.sig X.B.I.J ψ v (abelian₂ X) (D.R.rS + 1 + D.R.rS))
    (hM : ∀ v : PlX X, MeasP X.B.I.cm.sig X.B.I.J ψ v (abelian₂ X) (D.R.rS + 1 + D.R.rS) (yTup X u' v))
    (hI : ∀ v : PlX X, IdxP X.B.I.cm.sig X.B.I.J ψ v (abelian₂ X) (D.R.rS + 1 + D.R.rS) (yTup X u' v))
    (hCl : ∀ v : PlX X, ((Tw u' : ℕ) : 𝓞 X.B.I.F) ∈ v.asIdeal →
      ClsP X.B.I.cm.sig X.B.I.J ψ v (abelian₂ X) (D.R.rS + 1 + D.R.rS) (yTup X u' v)) :
    OmVBadT X u' ψ :=
  omVBadT_of X u' ψ hStd hLat hGram (omVdEx_holds X ψ) (omVdUniq_holds X ψ)
    (fun v hv => orbP_of _ _ _ _ _ _ _ (hExt v hv))
    (fun v => fibP_of_dual _ _ _ _ _ _ _ (hPC v) (hPD v))
    (fun v hv => countP_of _ _ _ _ _ _ _ (hM v) (hI v) (hCl v hv) (hPC v))
    (omVdSdW_holds X ψ) (omVdSdH_holds X ψ)

end PI.OmVd
end
end
