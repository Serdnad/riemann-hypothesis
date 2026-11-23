module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle410
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsTransportAdelicCorrection
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle146
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle174
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle172
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle228
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle147
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualSplitComponentIsLatticeStabilizerEq
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle192
import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasWeil
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatSelfDualOfUnimod
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle007
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle063
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalBlockDetBlockTriangular
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle554
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsOneComb
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsOpenKerUnramMulTame
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.JointSmooth
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiStarOfMid
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MidChart

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV Moves MonoAt OrthAt PrimAt idAt intAt grpAt colMul Lat SplitPt GoodBF GluedCore IsSumFrame)
open GlobalTheory.SeeSaw (idV dI FI)
open ValuativeRel
open GlobalTheory.Core.Mi.LatMatch

namespace GlobalTheory.Core.Mi.LatMatch.TraceX

theorem mulVec_mem_ideal {R : Type} [CommRing R] {I : Ideal R} {m n : ℕ} (A : Matrix (Fin m) (Fin n) R) {y : Fin n → R}
    (hy : ∀ i, y i ∈ I) (k : Fin m) : (A *ᵥ y) k ∈ I := by
  simp only [Matrix.mulVec, dotProduct]
  exact Ideal.sum_mem _ fun i _ => I.mul_mem_left _ (hy i)

theorem latV_iff_hatL {D : D7} (S : HSp D) (L : Lat S) (P : GlobalTheory.FinPl.Pl D → Prop) (y : Fin S.rank → AE D)
    (hy : ∀ i, y i ∈ idAt D P) :
    y ∈ latV S L P ↔ (fun i => toEAf D (y i)) ∈ Formalism.L2.Herm.hatL (F := D.host.F) L :=
  ⟨GlobalTheory.LatVHat.latV_mem_hatL D S L P y, GlobalTheory.HatLatV.mem_latV_of_hatL D S L P y hy⟩

theorem hat_reindex {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {m n : ℕ} (hn : m = n)
    (L : Submodule (𝓞 E) (Fin n → E)) (z : Fin m → E ⊗[F] Formalism.L2.Herm.Af F) :
    z ∈ Formalism.L2.Herm.hatL (F := F) (L.map ((LinearEquiv.funCongrLeft E E (finCongr hn)).toLinearMap.restrictScalars (𝓞 E))) ↔
      (fun j => z (Fin.cast hn.symm j)) ∈ Formalism.L2.Herm.hatL (F := F) L := by
  subst hn
  have e : L.map ((LinearEquiv.funCongrLeft E E (finCongr (rfl : m = m))).toLinearMap.restrictScalars (𝓞 E)) = L := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨x, hx, rfl⟩
  rw [e]
  rfl

theorem transport (D : D7) (I : AutInst) (ιE : I.E ≃+* D.host.E) (hId : ∀ y, HEq (ιE y) y)
    (hI : I = Formalism.L2.SG.InstExistsPf.instOf D) (hr : (D.sp.Y 0).rank = I.n)
    (ιA : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F ≃+* D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)
    (hrat : ∀ x : I.E, ιA (Formalism.UG.inclE (F := I.F) (Formalism.MainNotions.S.Af I.F) x) =
      Formalism.UG.inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) (ιE x))
    (hint : ∀ a, a ∈ IntAf I.F I.E ↔ ιA a ∈ IntAf D.host.F D.host.E)
    {n : ℕ} (q : Fin n → Fin I.n → I.E) (c : Fin n → GlobalTheory.AdForm.EF D) :
    (∑ i, ιA.symm (c i) • incl I (q i)) ∈ I.Lf ↔
      (∑ i, c i • fun k => Formalism.UG.inclE (F := D.host.F) (Formalism.MainNotions.S.Af D.host.F) (ιE (q i (Fin.cast hr k)))) ∈
        Formalism.L2.Herm.hatL (F := D.host.F) (latS D) := by
  subst hI
  have hid : ∀ y, ιE y = y := fun y => eq_of_heq (hId y)
  have hA : ∀ a, ιA a = a := GlobalTheory.Core.Mi.FinFrame.eq_self_of_rat_of_int (Formalism.L2.SG.InstExistsPf.instOf D).F
    (Formalism.L2.SG.InstExistsPf.instOf D).E ιA.toRingHom
    (fun x => (hrat x).trans (congrArg _ (hid x))) (fun a ha => (hint a).1 ha)
  have hA' : ∀ a, ιA.symm a = a := fun a => (hA _).symm.trans (ιA.apply_symm_apply a)
  simp only [hid, hA']
  have e : latS D = GlobalTheory.PlaceModel.latFrame (Yc D 0) := GlobalTheory.ConjPlaceRed.crdLat_eq_latFrame (D.sp.Y 0)
  rw [e]
  exact (GlobalTheory.ConjPlaceRed.mem_Lf D _).symm

theorem fin_emb {D : D7} {S S₀ A L : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (o : OrthDec S₀ A L) (w : Fin A.rank → AE D) :
    (fun k => toEAf D ((d.j0 *ᵥ (o.jA *ᵥ w)) k)) =
      ∑ i, toEAf D (w i) • fun k => Formalism.UG.inclE (F := D.host.F) (Formalism.MainNotions.S.Af D.host.F) ((d.i₀ * o.iA) k i) := by
  have h2 : HMul.hMul d.j0 o.jA = (d.i₀ * o.iA).map (incA D) := (Matrix.map_mul (f := incA D)).symm
  rw [Matrix.mulVec_mulVec, h2]
  funext k

  simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, Matrix.map_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
  GlobalTheory.Core.Mi.FinFrame.toEAf_incA]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

theorem fin_mt {D : D7} (V : HSp D) {n : ℕ} (hn : V.rank = n) (g : GA D V) (y : Fin V.rank → AE D) :
    GlobalTheory.AdForm.finM V hn g *ᵥ (fun j => toEAf D (y (Fin.cast hn.symm j))) =
      fun j => toEAf D ((Formalism.L2.Theta.mt V g *ᵥ y) (Fin.cast hn.symm j)) := by
  subst hn
  funext i
  exact (RingHom.map_mulVec (toEAf D) (Formalism.L2.Theta.mt V g) y i).symm



theorem trace_iff : ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (u : D.what₂.Word) (ψ : AddChar (AF D.host.F) ℂ) (F : Formalism.L2.Forms.Forms0 D u) (tr : Formalism.L2.SG.ColDict.Transport X u F) (hK : X.LevelSubgroupCharacter) (B : SBes X h u ψ (D.sp.X 0)) (a₀ : GA D (D.sp.X 0)), GlobalTheory.Core.Mi.IdE X → Formalism.L2.SG.ColDict.LevelMatch X tr hK → B.Adapted tr.wt → IsTransportAdelicCorrection tr a₀ → ∀ (v : GlobalTheory.FinPl.Pl D) (y : Fin (D.sp.X 0).rank → AE D), (∀ i, y i ∈ idAt D (· = v)) → (y ∈ latV (D.sp.X 0) (lat0 F) (· = v) ↔ B.d.j0 *ᵥ (B.o.jA *ᵥ (Formalism.L2.Theta.mt (D.sp.X 0) a₀ *ᵥ y)) ∈ latV (D.sp.Y 0) (latS D) (· = v)) := by
  intro D X h u ψ F tr hK B a₀ hId hL hAd h0 v y hy
  have hn := Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)
  have hy' : ∀ k, (B.d.j0 *ᵥ (B.o.jA *ᵥ (Formalism.L2.Theta.mt (D.sp.X 0) a₀ *ᵥ y))) k ∈ idAt D (· = v) :=
    mulVec_mem_ideal _ (mulVec_mem_ideal _ (mulVec_mem_ideal _ hy))
  refine (latV_iff_hatL _ _ _ _ hy).trans
    (Iff.trans ?_ (latV_iff_hatL _ _ _ _ hy').symm)
  change (fun i => toEAf D (y i)) ∈ Formalism.L2.Herm.hatL (F := D.host.F) (lat0 F) ↔
    (fun k => toEAf D ((B.d.j0 *ᵥ (B.o.jA *ᵥ (Formalism.L2.Theta.mt (D.sp.X 0) a₀ *ᵥ y))) k)) ∈
      Formalism.L2.Herm.hatL (F := D.host.F) (latS D)
  refine (hat_reindex hn F.cls0.lev.Lb _).trans ?_
  have H := hL.1 (tr.h0.1.1 *ᵥ fun j => toEAf D (y (Fin.cast hn.symm j)))
  have e1 : (tr.h0⁻¹).1.1 *ᵥ (tr.h0.1.1 *ᵥ fun j => toEAf D (y (Fin.cast hn.symm j))) =
      fun j => toEAf D (y (Fin.cast hn.symm j)) := by
    rw [Matrix.mulVec_mulVec]
    have : HMul.hMul (tr.h0⁻¹).1.1 tr.h0.1.1 = 1 := Units.inv_mul tr.h0.1
    rw [this, Matrix.one_mulVec]
  rw [e1] at H
  refine H.trans ?_
  rw [← h0.2, fin_mt, fin_emb]
  refine (transport D X.B.I X.ιE hId h (rank_eq X h) tr.ιA tr.ιA_rat tr.ιA_int
    (fun i => X.crd (Formalism.L2.SG.ColDict.qFr tr.wt i)) _).trans ?_
  simp only [hAd _ _]
  refine iff_of_eq (congrArg (· ∈ Formalism.L2.Herm.hatL (F := D.host.F) (latS D)) ?_)
  exact (Fintype.sum_equiv (finCongr hn) _ _ fun i => rfl).symm

end GlobalTheory.Core.Mi.LatMatch.TraceX
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV Moves MonoAt OrthAt PrimAt idAt intAt grpAt colMul Lat SplitPt GoodBF GluedCore IsSumFrame)
open GlobalTheory.SeeSaw (idV dI FI)
open ValuativeRel
open GlobalTheory.Core.Mi.LatMatch

noncomputable section





open Formalism.MainNotions.StandardLattice (intAf)

namespace GlobalTheory.Core.Mi.LineSD

variable {D : D7}

theorem mul_mem_intAt {v : GlobalTheory.FinPl.Pl D} {a b : AE D} (ha : a ∈ intAt D (· = v)) (hb : b ∈ intAt D (· = v)) :
    a * b ∈ intAt D (· = v) :=
  ⟨Ideal.mul_mem_right _ _ ha.1, by rw [map_mul]; exact GlobalTheory.FinPl.FrameLat.mul_mem_intAE ha.2 hb.2⟩

theorem one_mem_intAf : (1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) ∈ intAf D.host.F := fun w => by
  rw [map_one]; exact one_mem _

theorem incA_mem_intAE (x : 𝓞 D.host.E) : finPart D (incA D (x : D.host.E)) ∈ intAE D :=
  AddSubgroup.subset_closure ⟨1, one_mem_intAf, x, rfl⟩

theorem mul_incA_mem {v : GlobalTheory.FinPl.Pl D} {a : AE D} (ha : a ∈ intAt D (· = v)) (x : 𝓞 D.host.E) :
    a * incA D (x : D.host.E) ∈ intAt D (· = v) :=
  ⟨Ideal.mul_mem_right _ _ ha.1, by
    rw [map_mul]; exact GlobalTheory.FinPl.FrameLat.mul_mem_intAE ha.2 (incA_mem_intAE x)⟩

theorem cA_mem_intAt {v : GlobalTheory.FinPl.Pl D} {a : AE D} (ha : a ∈ intAt D (· = v)) : cA D a ∈ intAt D (· = v) := by
  refine ⟨?_, (GlobalTheory.FinPl.FrameLat.cA_int_iff a).2 ha.2⟩
  have h := (GlobalTheory.FinPlLoc.mem_idAt_iff _ a).1 ha.1
  rw [GlobalTheory.FinPlLoc.mem_idAt_iff, ← GlobalTheory.FinPlLoc.cA_idem, ← map_mul, h]

theorem unit_at {v : GlobalTheory.FinPl.Pl D} {T : ℕ} (hT : (T : 𝓞 D.host.F) ∉ v.asIdeal) :
    GlobalTheory.FinPlLoc.idem D (· = v) * incA D ((T : D.host.E)⁻¹) ∈ intAt D (· = v) := by
  refine ⟨Ideal.mul_mem_right _ _ (GlobalTheory.FinPlLoc.idem_mem_idAt _), ?_⟩
  have hc : ((T : D.host.E)⁻¹) = algebraMap D.host.F D.host.E ((T : D.host.F)⁻¹) := by simp
  have e : finPart D (GlobalTheory.FinPlLoc.idem D (· = v) * incA D ((T : D.host.E)⁻¹)) =
      ((T : D.host.F)⁻¹ • GlobalTheory.FinPlLoc.ePl D (· = v)) ⊗ₜ[D.host.F] (1 : D.host.E) := by
    rw [map_mul, GlobalTheory.FinPlLoc.idem, GlobalTheory.FinPlLoc.finPart_pair]
    show (GlobalTheory.FinPlLoc.ePl D (· = v) ⊗ₜ[D.host.F] (1 : D.host.E)) *
      ((1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) ⊗ₜ[D.host.F] ((T : D.host.E)⁻¹)) = _
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul, hc, Algebra.algebraMap_eq_smul_one,
      TensorProduct.tmul_smul, TensorProduct.smul_tmul']
  rw [e]
  refine AddSubgroup.subset_closure ⟨(T : D.host.F)⁻¹ • GlobalTheory.FinPlLoc.ePl D (· = v), fun w => ?_, (1 : 𝓞 D.host.E), ?_⟩
  swap
  · rfl
  rw [Algebra.smul_def, map_mul, AlgHom.commutes, GlobalTheory.FinPlLoc.evalV_ePl]
  by_cases hw : w = v
  · subst hw
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, if_pos rfl, mul_one]
    show Valued.v (((T : D.host.F)⁻¹ : D.host.F) : w.adicCompletion D.host.F) ≤ 1
    rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation', map_inv₀]
    have h1 : w.valuation D.host.F (T : D.host.F) = 1 := by
      have := HeightOneSpectrum.valuation_of_algebraMap (K := D.host.F) w (T : 𝓞 D.host.F)
      rw [HeightOneSpectrum.intValuation_eq_one_iff.2 hT] at this
      simpa using this
    rw [h1, inv_one]
  · rw [if_neg hw, mul_zero]; exact zero_mem _

def traceLine {S A L : HSp D} (o : OrthDec S A L) (M' : Lat S) (v : GlobalTheory.FinPl.Pl D) :
    AddSubgroup (Fin L.rank → AE D) where
  carrier := {l | (∀ i, l i ∈ idAt D (· = v)) ∧ o.jB *ᵥ l ∈ latV S M' (· = v)}
  add_mem' := fun {a b} ha hb => ⟨fun i => add_mem (ha.1 i) (hb.1 i), by
    show o.jB *ᵥ (a + b) ∈ _
    rw [mulVec_add]; exact add_mem ha.2 hb.2⟩
  zero_mem' := ⟨fun i => zero_mem _, by
    show o.jB *ᵥ 0 ∈ _
    rw [mulVec_zero]; exact zero_mem _⟩
  neg_mem' := fun {a} ha => ⟨fun i => neg_mem (ha.1 i), by
    show o.jB *ᵥ (-a) ∈ _
    rw [mulVec_neg]; exact neg_mem ha.2⟩

theorem exists_isSDAt_line : ∀ (D : D7) (S A L : HSp D) (o : OrthDec S A L) (ζ : Fin L.rank → D.host.E) (M' : Lat S) (μ : D.host.E) (T : ℕ) (v : GlobalTheory.FinPl.Pl D), IsLineVec L ζ → μ ≠ 0 → LineAt (vecB o ζ) μ M' v → star ζ ⬝ᵥ L.gram *ᵥ ζ = -(μ * star μ * (T : D.host.E)) → (T : 𝓞 D.host.F) ∉ v.asIdeal → ∃ Λ' : AddSubgroup (Fin L.rank → AE D), GlobalTheory.IwaPlace.IsSDAt L v Λ' ∧ ∀ l : Fin L.rank → AE D, (∀ i, l i ∈ idAt D (· = v)) → (l ∈ Λ' ↔ o.jB *ᵥ l ∈ latV S M' (· = v)) := by
  intro D S A L o ζ M' μ T v hζ hμ hline hgram hT
  obtain ⟨hr, hne⟩ := hζ
  obtain ⟨i₀, hall⟩ : ∃ i₀ : Fin L.rank, ∀ i, i = i₀ :=
    ⟨⟨0, by omega⟩, fun i => Fin.ext (by have := i.2; simp only; omega)⟩
  have hs : ∀ {M : Type} [AddCommMonoid M] (f : Fin L.rank → M), ∑ i, f i = f i₀ := fun f =>
    Fintype.sum_eq_single _ fun i hi => absurd (hall i) hi
  have hdot : star ζ ⬝ᵥ L.gram *ᵥ ζ = star (ζ i₀) * L.gram i₀ i₀ * ζ i₀ := by
    simp only [dotProduct, mulVec, hs, Pi.star_apply]; ring
  have hz0 : ζ i₀ ≠ 0 := by
    intro h; apply hne; rw [hdot, h, mul_zero]
  have hsz : star (ζ i₀) ≠ 0 := star_ne_zero.2 hz0
  have hT0 : (T : D.host.E) ≠ 0 := by
    have : T ≠ 0 := by rintro rfl; exact hT (by simp)
    exact_mod_cast this
  have hq : star (ζ i₀) * L.gram i₀ i₀ * ζ i₀ = -(μ * star μ * (T : D.host.E)) := by rw [← hdot, hgram]
  have hjB : ∀ l : Fin L.rank → AE D, o.jB *ᵥ l = (l i₀ * incA D (ζ i₀)⁻¹) • ratV (vecB o ζ) := by
    intro l; funext r
    simp only [OrthDec.jB, rat, vecB, ratV, mulVec, dotProduct, Matrix.map_apply, Pi.smul_apply, smul_eq_mul, hs]
    rw [map_mul]
    have h1 : incA D (ζ i₀)⁻¹ * incA D (ζ i₀) = 1 := by rw [← map_mul, inv_mul_cancel₀ hz0, map_one]
    linear_combination (-(incA D (o.iB r i₀) * l i₀)) * h1
  have hK : ∀ l : Fin L.rank → AE D, (∀ i, l i ∈ idAt D (· = v)) →
      (o.jB *ᵥ l ∈ latV S M' (· = v) ↔ l i₀ * incA D (μ / ζ i₀) ∈ intAt D (· = v)) := by
    intro l hl
    rw [hjB, hline _ (Ideal.mul_mem_right _ _ (hl i₀))]
    have : incA D μ * (l i₀ * incA D (ζ i₀)⁻¹) = l i₀ * incA D (μ / ζ i₀) := by
      rw [div_eq_mul_inv, map_mul]; ring
    rw [this]
  let Λ' := traceLine o M' v
  have hmem : ∀ l, l ∈ Λ' ↔ (∀ i, l i ∈ idAt D (· = v)) ∧ o.jB *ᵥ l ∈ latV S M' (· = v) := fun l => Iff.rfl
  have hΛ : ∀ x, x ∈ Λ' ↔ (∀ i, x i ∈ idAt D (· = v)) ∧ x i₀ * incA D (μ / ζ i₀) ∈ intAt D (· = v) :=
    fun x => (hmem x).trans (and_congr_right fun hx => hK x hx)
  refine ⟨Λ', ⟨fun y hy => hy.1, ?_, ?_⟩, fun l hl => by rw [hmem]; exact ⟨fun h => h.2, fun h => ⟨hl, h⟩⟩⟩
  · obtain ⟨y, hy0, hyint⟩ :=
      exists_integral_multiples ℤ ℚ (L := D.host.E) {μ / ζ i₀}
    replace hyint := hyint _ (Finset.mem_singleton_self _)
    have hn : IsIntegral ℤ ((y.natAbs : D.host.E) * (μ / ζ i₀)) := by
      rcases Int.natAbs_eq y with h | h
      · rw [h, zsmul_eq_mul, Int.cast_natCast] at hyint; exact hyint
      · rw [h, neg_smul, zsmul_eq_mul, Int.cast_natCast] at hyint; simpa using hyint.neg
    refine ⟨y.natAbs, Int.natAbs_pos.2 hy0, fun x hx => ?_⟩
    refine (hΛ _).2 ⟨fun i => ?_, ?_⟩
    · rw [Pi.smul_apply, smul_eq_mul]; exact Ideal.mul_mem_left _ _ (hx i).1
    · have : ((y.natAbs : AE D) • x) i₀ * incA D (μ / ζ i₀) =
          x i₀ * incA D ((y.natAbs : D.host.E) * (μ / ζ i₀)) := by
        rw [Pi.smul_apply, smul_eq_mul, map_mul, map_natCast]; ring
      rw [this]; exact mul_incA_mem (hx i₀) ⟨_, hn⟩
  · intro y hy
    have hherm : ∀ x : Fin L.rank → AE D, GlobalTheory.IwaPlace.hermAt L y x = cA D (x i₀) * incA D (L.gram i₀ i₀) * y i₀ := by
      intro x; simp only [GlobalTheory.IwaPlace.hermAt, hs, gA, rat, Matrix.map_apply]
    have hG : L.gram i₀ i₀ = star (μ / ζ i₀) * (-(T : D.host.E)) * (μ / ζ i₀) := by
      have h1 : L.gram i₀ i₀ = -(μ * star μ * (T : D.host.E)) / (star (ζ i₀) * ζ i₀) := by
        rw [eq_div_iff (mul_ne_zero hsz hz0)]; linear_combination hq
      rw [h1, div_eq_mul_inv μ, star_mul', star_inv₀]
      field_simp
    have hid : ∀ a : AE D, cA D a * incA D (L.gram i₀ i₀) * y i₀ =
        cA D (a * incA D (μ / ζ i₀)) * (y i₀ * incA D (μ / ζ i₀)) * incA D (-(T : D.host.E)) := by
      intro a
      rw [hG]; simp only [map_mul, GlobalTheory.FinPl.FrameLat.cA_incA]; ring
    have hay : y i₀ * incA D (μ / ζ i₀) ∈ idAt D (· = v) := Ideal.mul_mem_right _ _ (hy i₀)
    have he : GlobalTheory.FinPlLoc.idem D (· = v) * incA D (ζ i₀ / μ) * incA D (μ / ζ i₀) = GlobalTheory.FinPlLoc.idem D (· = v) := by
      rw [mul_assoc, ← map_mul, show ζ i₀ / μ * (μ / ζ i₀) = 1 by field_simp, map_one, mul_one]
    constructor
    · intro hyΛ x hx
      obtain ⟨-, hyK⟩ := (hΛ y).1 hyΛ
      obtain ⟨-, hxK⟩ := (hΛ x).1 hx
      rw [hherm, hid]
      have := mul_incA_mem (mul_mem_intAt (cA_mem_intAt hxK) hyK) (-(T : 𝓞 D.host.E))
      simpa using this
    · intro h
      refine (hΛ y).2 ⟨hy, ?_⟩
      have hx₁ : (fun _ => GlobalTheory.FinPlLoc.idem D (· = v) * incA D (ζ i₀ / μ) : Fin L.rank → AE D) ∈ Λ' := by
        refine (hΛ _).2 ⟨fun i => Ideal.mul_mem_right _ _ (GlobalTheory.FinPlLoc.idem_mem_idAt _), ?_⟩
        show GlobalTheory.FinPlLoc.idem D (· = v) * incA D (ζ i₀ / μ) * incA D (μ / ζ i₀) ∈ _
        rw [he]; exact GlobalTheory.FinPlLoc.idem_mem_intAt _
      have h1 := h _ hx₁
      rw [hherm, hid] at h1
      rw [he, GlobalTheory.FinPlLoc.cA_idem, (GlobalTheory.FinPlLoc.mem_idAt_iff _ _).1 hay] at h1
      have h2 := mul_incA_mem (mul_mem_intAt h1 (unit_at hT)) (-1 : 𝓞 D.host.E)
      have hT' : incA D (-(T : D.host.E)) * incA D ((T : D.host.E)⁻¹) * incA D (((-1 : 𝓞 D.host.E)) : D.host.E) = 1 := by
        rw [← map_mul, ← map_mul]; push_cast; rw [neg_mul, mul_inv_cancel₀ hT0]; simp
      have hay' := (GlobalTheory.FinPlLoc.mem_idAt_iff _ _).1 hay
      have e2 : y i₀ * incA D (μ / ζ i₀) * incA D (-(T : D.host.E)) *
          (GlobalTheory.FinPlLoc.idem D (· = v) * incA D ((T : D.host.E)⁻¹)) * incA D (((-1 : 𝓞 D.host.E)) : D.host.E) =
          y i₀ * incA D (μ / ζ i₀) := by
        linear_combination (GlobalTheory.FinPlLoc.idem D (· = v) * (y i₀ * incA D (μ / ζ i₀))) * hT' + hay'
      rw [e2] at h2; exact h2

end GlobalTheory.Core.Mi.LineSD
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV Moves MonoAt OrthAt PrimAt idAt intAt grpAt colMul Lat SplitPt GoodBF GluedCore IsSumFrame)
open GlobalTheory.SeeSaw (idV dI FI)
open ValuativeRel
open GlobalTheory.Core.Mi.LatMatch

noncomputable section

namespace GlobalTheory.Core.Mi.LatMatch

variable {D : D7}


open GlobalTheory.IwaPlace in
theorem hermAt_colMul_jY {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (i : Fin ρ) (a : AE D)
    (x : Fin S.rank → AE D) : hermAt S (colMul d.jY i a) x = a * cA D ((d.pX *ᵥ x) i) := by
  have hg : ∀ j k, cA D (gA S j k) = gA S k j := fun j k => congrFun (congrFun (adj_gA S) k) j
  rw [d.pX_eq]

  simp only [hermAt, colMul, Matrix.mulVec, dotProduct, Matrix.mul_apply, adj, Matrix.transpose_apply,
  Matrix.map_apply, map_sum, map_mul, cA_cA, hg, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem pX_colMul_jX {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (i : Fin ρ) (b : AE D) :
    (d.pX *ᵥ colMul d.jX i b) i = b := by
  have h := congrFun (congrFun d.pX_jX i) i
  simp only [Matrix.mul_apply, Matrix.one_apply_eq] at h
  simp only [Matrix.mulVec, dotProduct, colMul]
  calc ∑ k, d.pX i k * (b * d.jX k i) = b * ∑ k, d.pX i k * d.jX k i := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring
    _ = b := by rw [h, mul_one]

theorem mem_idAt_of_colMul_jX {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) {L : Lat S} (hL : IsSelfDualC S L)
    (v : GlobalTheory.FinPl.Pl D) (i : Fin ρ) {b : AE D} (hb : colMul d.jX i b ∈ latV S L (· = v)) : b ∈ idAt D (· = v) := by
  rw [← pX_colMul_jX d i b]
  exact GlobalTheory.IwaPlace.mulVec_mem_idAt d.pX ((GlobalTheory.IwaPlace.LocSD.isSDAt_latV D S L v hL).1 _ hb) i

theorem colMul_jY_mem_iff {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) {L : Lat S} {M : Lat S₀} {v : GlobalTheory.FinPl.Pl D}
    (hL : IsSelfDualC S L) (hM : MonoAt d L M v) (i : Fin ρ) {a : AE D} (ha : a ∈ idAt D (· = v)) :
    colMul d.jY i a ∈ latV S L (· = v) ↔
      ∀ b, colMul d.jX i b ∈ latV S L (· = v) → a * cA D b ∈ intAt D (· = v) := by
  have hy : ∀ k, colMul d.jY i a k ∈ idAt D (· = v) := fun k => Ideal.mul_mem_right _ _ ha
  rw [(GlobalTheory.IwaPlace.LocSD.isSDAt_latV D S L v hL).2.2 _ hy]
  constructor
  · intro h b hb
    have h1 := h _ hb
    rwa [hermAt_colMul_jY, pX_colMul_jX] at h1
  · intro h x hx
    rw [hermAt_colMul_jY]
    exact h _ (((hM x).1 hx).1 i)

theorem dualLine_match : ∀ (D : D7) (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (L L' : Lat S) (M M' : Lat S₀) (v : GlobalTheory.FinPl.Pl D) (c : AE D), IsSelfDualC S L → IsSelfDualC S L' → MonoAt d L M v → MonoAt d L' M' v → NormOneAt v c → (∀ i, ∀ a ∈ idAt D (· = v), (colMul d.jX i a ∈ latV S L (· = v) ↔ colMul d.jX i (c * a) ∈ latV S L' (· = v))) → ∀ i, ∀ a ∈ idAt D (· = v), (colMul d.jY i a ∈ latV S L (· = v) ↔ colMul d.jY i (c * a) ∈ latV S L' (· = v)) := by
  intro D S S₀ ρ d L L' M M' v c hL hL' hM hM' hc hX i a ha
  have hca : c * a ∈ idAt D (· = v) := Ideal.mul_mem_left _ _ ha
  rw [colMul_jY_mem_iff d hL hM i ha, colMul_jY_mem_iff d hL' hM' i hca]
  have hcc : c * cA D c = 1 := hc.1
  constructor
  · intro h b' hb'
    have hbI : cA D c * b' ∈ idAt D (· = v) :=
      Ideal.mul_mem_left _ _ (mem_idAt_of_colMul_jX d hL' v i hb')
    have e : c * (cA D c * b') = b' := by rw [← mul_assoc, hcc, one_mul]
    have h1 : colMul d.jX i (cA D c * b') ∈ latV S L (· = v) := (hX i _ hbI).2 (by rw [e]; exact hb')
    have h2 := h _ h1
    rw [map_mul, cA_cA] at h2
    have e2 : c * a * cA D b' = a * (c * cA D b') := by ring
    rw [e2]
    exact h2
  · intro h b hb
    have h1 := (hX i b (mem_idAt_of_colMul_jX d hL v i hb)).1 hb
    have h2 := h _ h1
    have e : c * a * cA D (c * b) = a * cA D b := by
      rw [map_mul]
      calc c * a * (cA D c * cA D b) = (c * cA D c) * (a * cA D b) := by ring
        _ = a * cA D b := by rw [hcc, one_mul]
    rwa [e] at h2

end GlobalTheory.Core.Mi.LatMatch

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StepData GlobalTheory.SplitWeil ValuativeRel

noncomputable section

namespace GlobalTheory.SplitOffRed

theorem resS_eq_zero_of_cpt {D : D7} (PP' : Formalism.L2.DIV.Pl D.host.E) (s : Formalism.L2.Herm.intAf D.host.F D.host.E)
    (h : GlobalTheory.StdFrames.cpt PP' (s : Formalism.IndefR.Datum.EAf D) = 0) : Formalism.L2.DIV.resS D.host.F PP' s = 0 := by
  obtain ⟨a, h1, h2⟩ := GlobalTheory.FunObj.Comparison₂.exists_resS_eq PP' s
  rw [h1, GlobalTheory.FunObj.Comparison₂.mk_eq_zero_iff]
  rw [GlobalTheory.FunObj.Comparison₂.cptO_apply PP' s] at h2
  change Valued.v (GlobalTheory.StdFrames.cpt PP' (s : Formalism.IndefR.Datum.EAf D) - _) < 1 at h2
  rw [h, zero_sub, Valuation.map_neg] at h2
  exact h2

theorem redFn_eq_one_off : ∀ {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k) {PP : Formalism.L2.DIV.Pl D.host.E}, Formalism.L2.NTheta.IsIdemAt q.e PP → ∀ (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (κ : GA D V), Formalism.L2.Theta.SuppAt q.e V κ → Lev.finE V κ ∈ Formalism.L2.DIV.St β → ∀ PP' : Formalism.L2.DIV.Pl D.host.E, (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP') ≠ (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) → Formalism.L2.DIV.redFn β PP' (Lev.finE V κ) = 1 := by
  intro D k _ _ _ _ q PP hq V β κ hS hst PP' hne
  have hPP' : PP' ≠ PP := fun h => hne (h ▸ rfl)
  have hcP : GlobalTheory.IdemSupport.cP PP' ≠ PP := fun h => hne (by rw [← h, GlobalTheory.IdemSupport.under_cP])
  have h1 : q.e * q.e = q.e := q.split.1
  have hc1 : cA D q.e * cA D q.e = cA D q.e := by rw [← map_mul, h1]
  have hi1 : toEAf D q.e ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := (GlobalTheory.IdemRes.resS_idem_eq_one D q.e PP hq).1
  have hi2 : toEAf D (cA D q.e) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E :=
    GlobalTheory.IdemRes.toEAf_mem_of_finPart (GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← RingHom.map_mul, hc1]))
  have hint : toEAf D (q.e + cA D q.e) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
    rw [RingHom.map_add (f := _)]; exact add_mem hi1 hi2
  have hc0 : GlobalTheory.StdFrames.cpt PP' (toEAf D (q.e + cA D q.e)) = 0 := by
    rw [RingHom.map_add (f := _), RingHom.map_add (f := _), (GlobalTheory.StdFrames.cpt_of_isIdemAt hq).2 PP' hPP', zero_add,
      GlobalTheory.StdFrames.toEAf_cA]
    exact GlobalTheory.StdFrames.cpt_sg_eq_zero ((GlobalTheory.StdFrames.cpt_of_isIdemAt hq).2 _ hcP)
  have hres : Formalism.L2.DIV.resS D.host.F PP' ⟨toEAf D (q.e + cA D q.e), hint⟩ = 0 :=
    resS_eq_zero_of_cpt PP' _ hc0
  have hval : (Lev.finE V κ).val = (Formalism.L2.Theta.mt V κ).map (toEAf D) := rfl
  refine GlobalTheory.LevSplit.redFn_eq_one β PP' (Lev.finE V κ) hst ⟨toEAf D (q.e + cA D q.e), hint⟩ hres ?_
  ext i j
  have := congrArg (toEAf D) (hS i j)
  rw [RingHom.map_mul, Matrix.sub_apply, RingHom.map_sub] at this
  show toEAf D (q.e + cA D q.e) * ((Lev.finE V κ).val - 1) i j = ((Lev.finE V κ).val - 1) i j
  rw [Matrix.sub_apply, hval, Matrix.map_apply]
  have e1 : (1 : Matrix (Fin V.rank) (Fin V.rank) (Lev.EAf D)) i j = toEAf D ((1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) i j) := by
    rw [Matrix.one_apply, Matrix.one_apply]; split_ifs <;> simp
  rw [e1]
  exact this

end GlobalTheory.SplitOffRed

end
end
