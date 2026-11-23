module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SubsetTwistExceptionalPlaces
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
public import GroundTheory.GlobalFields.IdeleGroups.IdeleNorms
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.WdOfMono0L
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle009
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Hat1
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle037
public import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle890
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdmissibleEmptyOfGood
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle857
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle867
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle008
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle021
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsIsScalar
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle891
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GoodSetupCountEqZeroOffBadPlaces
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle894
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Topology.Sheaves.Init
import Mathlib.Tactic.Polynomial.Basic
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsSplitOfMemAdmissibleConjugatePairPlaces
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle034
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivOfNotLinearIndependent
import Formalism.LocalToGlobal.Divisibility.CoefMod
import Formalism.LocalToGlobal.IndefiniteReal.Bundle001
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.SharpRestriction.LevelLetterCocycles.IntegralHeckeForms
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsFramedPointChangedByLetters
import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle173

@[expose] public section

section

noncomputable section

namespace GlobalTheory.ChoiceRead

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice _root_.Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev
  Formalism.IndefR.Mult Formalism.IndefR.RecTie Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain GlobalTheory.Mem
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar



section Choice

variable {D : D7}

abbrev Tgt (c : NChoice D) (w : D.what₂.places.Pl) (j : ℕ) : Type :=
  FractionRing (c.Oe w) ⊗[D.ntw.Ok (c.twI w) (c.k' w)]
    D.nexp.MtV (c.twI w) j (c.sd w) (c.k' w) (c.Q w) ((c.psi' w).comp (D.ntw.art (c.twI w) (c.Q w)))

def BasisAt (c : NChoice D) (w : D.what₂.places.Pl) (j : ℕ)
    (e : D.what₂.MtL (D.what₂.muTw w) j →ₛₗ[c.embW w] Tgt c w j) : Prop :=
  ∀ b : Module.Basis (Module.Free.ChooseBasisIndex D.what₂.LL (D.what₂.MtL (D.what₂.muTw w) j))
      D.what₂.LL (D.what₂.MtL (D.what₂.muTw w) j),
    LinearIndependent (FractionRing (c.Oe w)) (fun i => e (b i)) ∧
      Submodule.span (FractionRing (c.Oe w)) (Set.range fun i => e (b i)) = ⊤

def latT (c : NChoice D) (w : D.what₂.places.Pl) (j : ℕ) : Submodule (c.Oe w) (Tgt c w j) :=
  Submodule.span (c.Oe w)
      ((TensorProduct.mk (D.ntw.Ok (c.twI w) (c.k' w)) (FractionRing (c.Oe w))
          (D.nexp.MtV (c.twI w) j (c.sd w) (c.k' w) (c.Q w) ((c.psi' w).comp (D.ntw.art (c.twI w) (c.Q w)))) 1) ''
        (D.nexp.MtLat (c.twI w) j (c.sd w) (c.k' w) (c.Q w) ((c.psi' w).comp (D.ntw.art (c.twI w) (c.Q w))) :
          Set (D.nexp.MtV (c.twI w) j (c.sd w) (c.k' w) (c.Q w) ((c.psi' w).comp (D.ntw.art (c.twI w) (c.Q w))))))

def latS (w : D.what₂.places.Pl) (j : ℕ) : Set (D.what₂.MtL (D.what₂.muTw w) j) :=
  {x | D.what₂.jMt (D.what₂.muTw w) j x ∈ (D.what₂.MtLat (D.what₂.muTw w) j).gen}

def LatAt (c : NChoice D) (w : D.what₂.places.Pl) (j : ℕ)
    (e : D.what₂.MtL (D.what₂.muTw w) j →ₛₗ[c.embW w] Tgt c w j) (t : FractionRing (c.Oe w)) : Prop :=
  Submodule.span (c.Oe w) (e '' latS w j) = Submodule.span (c.Oe w) ((fun y => t • y) '' (latT c w j : Set (Tgt c w j)))

theorem BasisAt.smul {c : NChoice D} {w : D.what₂.places.Pl} {j : ℕ}
    {e : D.what₂.MtL (D.what₂.muTw w) j →ₛₗ[c.embW w] Tgt c w j} (h : BasisAt c w j e) (u : (FractionRing (c.Oe w))ˣ) :
    BasisAt c w j ((u : FractionRing (c.Oe w)) • e) := by
  intro b
  obtain ⟨h1, h2⟩ := h b
  refine ⟨?_, ?_⟩
  · exact h1.units_smul (fun _ => u)
  · have h3 : (Set.range fun i => ((u : FractionRing (c.Oe w)) • e) (b i)) =
        (u : FractionRing (c.Oe w)) • Set.range fun i => e (b i) := by
      rw [← Set.range_smul]; rfl
    rw [h3, Submodule.span_smul_eq_of_isUnit _ _ u.isUnit, h2]

theorem LatAt.smul_inv {c : NChoice D} {w : D.what₂.places.Pl} {j : ℕ}
    {e : D.what₂.MtL (D.what₂.muTw w) j →ₛₗ[c.embW w] Tgt c w j} (u : (FractionRing (c.Oe w))ˣ)
    (h : LatAt c w j e (u : FractionRing (c.Oe w))) :
    Submodule.span (c.Oe w) ((((u⁻¹ : (FractionRing (c.Oe w))ˣ) : FractionRing (c.Oe w)) • e) '' latS w j) = latT c w j := by
  let f : Tgt c w j →ₗ[c.Oe w] Tgt c w j :=
    { toFun := fun y => ((u⁻¹ : (FractionRing (c.Oe w))ˣ) : FractionRing (c.Oe w)) • y
      map_add' := fun _ _ => smul_add _ _ _
      map_smul' := fun r y => by
        simp only [RingHom.id_apply]
        rw [← algebraMap_smul (FractionRing (c.Oe w)) r y, ← algebraMap_smul (FractionRing (c.Oe w)) r,
          smul_smul, smul_smul, mul_comm] }
  have h1 : ((((u⁻¹ : (FractionRing (c.Oe w))ˣ) : FractionRing (c.Oe w)) • e) '' latS w j) = f '' (e '' latS w j) := by
    rw [Set.image_image]; rfl
  rw [h1, Submodule.span_image, h, ← Submodule.span_image, Set.image_image]
  have h2 : (fun y => f ((u : FractionRing (c.Oe w)) • y)) = id := by
    funext y
    show ((u⁻¹ : (FractionRing (c.Oe w))ˣ) : FractionRing (c.Oe w)) • ((u : FractionRing (c.Oe w)) • y) = y
    rw [smul_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_smul]
  rw [h2, Set.image_id, Submodule.span_eq]

def withE (c : NChoice D) (E : ∀ w j, D.what₂.MtL (D.what₂.muTw w) j →ₛₗ[c.embW w] Tgt c w j)
    (hb : ∀ w j, D.what₂.muAt w ≠ D.what₂.mu0 → 1 ≤ j → j ≤ D.R.m → BasisAt c w j (E w j))
    (hl : ∀ w j, D.what₂.muAt w ≠ D.what₂.mu0 → 1 ≤ j → j ≤ D.R.m →
      Submodule.span (c.Oe w) (E w j '' latS w j) = latT c w j) : NChoice D :=
  { c with
    eMt := E
    eMt_basis := fun w j hw h1 h2 b => hb w j hw h1 h2 b
    eMt_lat := fun w j hw h1 h2 => hl w j hw h1 h2 }

def tupWithE {cf : CharFrame D} {c : NChoice D} (tp : TupTied D cf c) (E : ∀ w j, D.what₂.MtL (D.what₂.muTw w) j →ₛₗ[c.embW w] Tgt c w j)
    (hb : ∀ w j, D.what₂.muAt w ≠ D.what₂.mu0 → 1 ≤ j → j ≤ D.R.m → BasisAt c w j (E w j))
    (hl : ∀ w j, D.what₂.muAt w ≠ D.what₂.mu0 → 1 ≤ j → j ≤ D.R.m →
      Submodule.span (c.Oe w) (E w j '' latS w j) = latT c w j) : TupTied D cf (withE c E hb hl) :=
  { tp with }

theorem choiceSide_withE {cf : CharFrame D} {mt : MtFam D} {exp : NExpTied D} {c : NChoice D} {tp : TupTied D cf c}
    (h : GlobalTheory.HeightCounting.ChoiceSide D cf mt exp c tp) (E : ∀ w j, D.what₂.MtL (D.what₂.muTw w) j →ₛₗ[c.embW w] Tgt c w j)
    (hb : ∀ w j, D.what₂.muAt w ≠ D.what₂.mu0 → 1 ≤ j → j ≤ D.R.m → BasisAt c w j (E w j))
    (hl : ∀ w j, D.what₂.muAt w ≠ D.what₂.mu0 → 1 ≤ j → j ≤ D.R.m →
      Submodule.span (c.Oe w) (E w j '' latS w j) = latT c w j) :
    GlobalTheory.HeightCounting.ChoiceSide D cf mt exp (withE c E hb hl) (tupWithE tp E hb hl) :=
  ⟨⟨h.nct.twOf_eq, h.nct.twSide_eq, h.nct.Q_eq, h.nct.psi_eq, h.nct.embedding_baseField_condition⟩,
    ⟨h.choice.twI_conj, h.choice.sd_place, h.choice.emb_side, h.choice.sd_conj, h.choice.one, h.choice.conj⟩,
    h.off, h.adm, h.psi, h.eMt_level⟩


open Classical in
def pick (c : NChoice D)
    (G : ∀ w, D.what₂.muAt w ≠ D.what₂.mu0 → ∀ i : Fin D.R.m,
      D.what₂.MtL (D.what₂.muTw w) (i.1 + 1) →ₛₗ[c.embW w] Tgt c w (i.1 + 1)) :
    ∀ w j, D.what₂.MtL (D.what₂.muTw w) j →ₛₗ[c.embW w] Tgt c w j
  | w, 0 => c.eMt w 0
  | w, k + 1 => if h : D.what₂.muAt w ≠ D.what₂.mu0 ∧ k < D.R.m then G w h.1 ⟨k, h.2⟩ else c.eMt w (k + 1)

theorem pick_eq (c : NChoice D)
    (G : ∀ w, D.what₂.muAt w ≠ D.what₂.mu0 → ∀ i : Fin D.R.m,
      D.what₂.MtL (D.what₂.muTw w) (i.1 + 1) →ₛₗ[c.embW w] Tgt c w (i.1 + 1))
    (w : D.what₂.places.Pl) (hw : D.what₂.muAt w ≠ D.what₂.mu0) (i : Fin D.R.m) : pick c G w (i.1 + 1) = G w hw i := by
  simp only [pick, dite_eq_left (And.intro hw i.2)]

theorem pick_prop (c : NChoice D)
    (G : ∀ w, D.what₂.muAt w ≠ D.what₂.mu0 → ∀ i : Fin D.R.m,
      D.what₂.MtL (D.what₂.muTw w) (i.1 + 1) →ₛₗ[c.embW w] Tgt c w (i.1 + 1))
    (p : ∀ w j, (D.what₂.MtL (D.what₂.muTw w) j →ₛₗ[c.embW w] Tgt c w j) → Prop)
    (h : ∀ w hw (i : Fin D.R.m), p w (i.1 + 1) (G w hw i)) :
    ∀ w j, D.what₂.muAt w ≠ D.what₂.mu0 → 1 ≤ j → j ≤ D.R.m → p w j (pick c G w j) := by
  intro w j hw h1 h2
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
  have := h w hw ⟨k, by omega⟩
  rwa [← pick_eq c G w hw ⟨k, by omega⟩] at this

end Choice

section Rows

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type}
  [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat3 D A3 Ks} {F : Face3 D A3} {X0 : BaseLevelRowSide D}
  {cG : G0 R.Pg D.R.r ≃* G0g D.nd} {S : RatDat D.ntw}

def ThetaAt (Y : R3.Read (A3 := A3) R.toRealDat F.lv2 X0) (YS : NExpRealS R cG S) (c : NChoice D) (w : D.what₂.places.Pl)
    (i : Fin D.R.m) (e : D.what₂.MtL (D.what₂.muTw w) (i.1 + 1) →ₛₗ[c.embW w] Tgt c w (i.1 + 1)) (t : FractionRing (c.Oe w)) :
    Prop :=
  ∀ x ∈ Idx.TjV D (D.what₂.muTw w) (i.1 + 1), ∀ (n : ℕ) (a : Fin n → D.what₂.LL) (f : Fin n → FmK S (i.1 + 1)),
    (R.FW i).j (sg0 D A3.A) ((YS.fi i).e (∑ k, a k • (show ↥(S.A (i.1 + 1)).WK from f k).1)) =
      Y.mj.eW i (D.what₂.thetaP (D.what₂.muTw w) (i.1 + 1) (D.what₂.jMt (D.what₂.muTw w) (i.1 + 1) x)) →
    NChoice.thPe D c w (i.1 + 1) (e x) =
      t • ∑ k, c.embW w (a k) ⊗ₜ[D.ntw.O (c.twI w)]
        (YS.eF (c.twI w) (i.1 + 1) (c.sd w) (by omega) (by omega)).symm ((1 : KB S (c.twI w) (c.sd w)) ⊗ₜ[S.Ks] f k)

theorem ThetaAt.smul_inv {Y : R3.Read (A3 := A3) R.toRealDat F.lv2 X0} {YS : NExpRealS R cG S} {c : NChoice D}
    {w : D.what₂.places.Pl} {i : Fin D.R.m} {e : D.what₂.MtL (D.what₂.muTw w) (i.1 + 1) →ₛₗ[c.embW w] Tgt c w (i.1 + 1)}
    (u : (FractionRing (c.Oe w))ˣ) (h : ThetaAt Y YS c w i e (u : FractionRing (c.Oe w))) :
    ThetaAt Y YS c w i ((((u⁻¹ : (FractionRing (c.Oe w))ˣ) : FractionRing (c.Oe w))) • e) 1 := by
  intro x hx n a f hf
  rw [one_smul, LinearMap.smul_apply, map_smul, h x hx n a f hf, smul_smul, ← Units.val_mul, inv_mul_cancel,
    Units.val_one, one_smul]

theorem emtTheta_withE {Y : R3.Read (A3 := A3) R.toRealDat F.lv2 X0} {YS : NExpRealS R cG S} {c : NChoice D}
    (E : ∀ w j, D.what₂.MtL (D.what₂.muTw w) j →ₛₗ[c.embW w] Tgt c w j)
    (hb : ∀ w j, D.what₂.muAt w ≠ D.what₂.mu0 → 1 ≤ j → j ≤ D.R.m → BasisAt c w j (E w j))
    (hl : ∀ w j, D.what₂.muAt w ≠ D.what₂.mu0 → 1 ≤ j → j ≤ D.R.m →
      Submodule.span (c.Oe w) (E w j '' latS w j) = latT c w j)
    (h : ∀ w (i : Fin D.R.m), D.what₂.muAt w ≠ D.what₂.mu0 → ThetaAt Y YS c w i (E w (i.1 + 1)) 1) :
    GlobalTheory.HeightCounting.EMtTheta Y YS (withE c E hb hl) := by
  intro w i hw x hx n a f hf
  have := h w i hw x hx n a f hf
  rw [one_smul] at this
  exact this

end Rows

end GlobalTheory.ChoiceRead

end
end

section

open NumberField Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.ThetaPoisson GroundTheory.Global GroundTheory.Global.IdeleGroup
open scoped ComplexConjugate nonZeroDivisors ContDiff

theorem _root_.GlobalTheory.T.integrableOn_absDet_rpow_le_one_fundamentalDomain : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ), 0 < a → ∀ (μ : Measure (GA E a)) [μ.IsHaarMeasure] (𝓕 : Set (GA E a)), IsFundamentalDomain (ratGL E a).range 𝓕 μ → ∀ s : ℝ, 0 < s → IntegrableOn (fun g : GA E a => (ideleModule E (GeneralLinearGroup.det g) : ℝ) ^ s) (𝓕 ∩ {g | (ideleModule E (GeneralLinearGroup.det g) : ℝ) ≤ 1}) μ := by
  first | exact @GlobalTheory.RSThetaLow.integrableOn_absDet_rpow_low | exact GlobalTheory.RSThetaLow.integrableOn_absDet_rpow_low | (intros; apply GlobalTheory.RSThetaLow.integrableOn_absDet_rpow_low <;> assumption)
end

section

open NumberField Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL

theorem _root_.GlobalTheory.T.integrableOn_min_absDet_inv_fundamentalDomain : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m : ℕ), 0 < m →
    ∀ (μ : Measure (GA E m)) [μ.IsHaarMeasure] (𝓕 : Set (GA E m)),
      IsFundamentalDomain (ratGL E m).range 𝓕 μ →
      IntegrableOn (fun h : GA E m => min (GroundTheory.Global.IdeleGroup.ideleModule E (GeneralLinearGroup.det h) : ℝ)
        (GroundTheory.Global.IdeleGroup.ideleModule E (GeneralLinearGroup.det h) : ℝ)⁻¹) 𝓕 μ := by
  first | exact @GlobalTheory.FinVolGL.integrableOn_min_absDet | exact GlobalTheory.FinVolGL.integrableOn_min_absDet | (intros; apply GlobalTheory.FinVolGL.integrableOn_min_absDet <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.WildFull

open Polynomial

theorem main : ∀ (D : D7) (T : GlobalTheory.RowTie.WDTie D.nd D.naut), GlobalTheory.HeightCounting.LabTrue D T → GlobalTheory.TypeLeaf.WildOne D := by
  intro D T hL k v L hdeg s hsI hsW
  haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  have h1 := hL k v L
  rw [h1, ← T.dim] at hdeg
  rw [T.inePol _ L s hsI, ← T.dim]
  exact GlobalTheory.WeilDeligne.WD.inePol_wild_of_natDegree_lab hdeg hsW

end GlobalTheory.WildFull
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar


namespace GlobalTheory.HatIntSmul

theorem mem_stdLat_coord {E : Type} [Field E] [NumberField E] {n : ℕ} {s : Fin n → E}
    (hs : s ∈ Formalism.L2.Pj.stdLat E n) (j : Fin n) : ∃ o : 𝓞 E, s j = (o : E) := by
  have := (Submodule.mem_pi.mp hs) j (Set.mem_univ _)
  obtain ⟨o, ho⟩ := Submodule.mem_one.mp this
  exact ⟨o, ho.symm⟩

theorem single_mem_stdLat {E : Type} [Field E] [NumberField E] {n : ℕ} (i : Fin n) (o : 𝓞 E) :
    Pi.single i (o : E) ∈ Formalism.L2.Pj.stdLat E n := by
  refine Submodule.mem_pi.mpr fun j _ => ?_
  rw [Submodule.mem_one]
  by_cases h : j = i
  · subst h; exact ⟨o, by simp⟩
  · exact ⟨0, by simp [Pi.single_apply, h]⟩

theorem nsmul_tmul {F : Type} [Field F] [NumberField F] {E : Type} [Field E] [NumberField E] [Algebra F E]
    (a : ℕ) (β : Af F) (x : E) : a • (β ⊗ₜ[F] x) = β ⊗ₜ[F] (((a : 𝓞 E) : E) * x) := by
  have h := map_nsmul (TensorProduct.mk F (Af F) E β) a x
  simp only [TensorProduct.mk_apply] at h
  rw [← h, nsmul_eq_mul]
  simp



theorem sq_smul_mulVec_mem_hat : ∀ (D : D7) (n : ℕ) (Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) (a : ℕ), (∀ x ∈ Formalism.L2.Pj.stdLat D.host.E n, (a : 𝓞 D.host.E) • x ∈ Λ) → (∀ x ∈ Λ, (a : 𝓞 D.host.E) • x ∈ Formalism.L2.Pj.stdLat D.host.E n) → ∀ (M : Matrix (Fin n) (Fin n) (Af D.host.F ⊗[D.host.F] D.host.E)), (∀ i j, M i j ∈ intAE D) → ∀ y ∈ GlobalTheory.AdLat.hat D.host.F (Λ : Set (Fin n → D.host.E)), (a ^ 2) • (M *ᵥ y) ∈ GlobalTheory.AdLat.hat D.host.F (Λ : Set (Fin n → D.host.E)) := by
  intro D n Λ a h1 h2 M hM y hy
  have mulMem : ∀ {x y : Af D.host.F ⊗[D.host.F] D.host.E}, x ∈ intAE D → y ∈ intAE D → x * y ∈ intAE D := by
    intro x y hx hy
    refine AddSubgroup.closure_induction₂ (p := fun x y _ _ => x * y ∈ intAE D) ?_ ?_ ?_ ?_ ?_ ?_ ?_ hx hy
    · rintro _ _ ⟨a, ha, u, rfl⟩ ⟨b, hb, v, rfl⟩
      refine AddSubgroup.subset_closure ⟨a * b, fun w => ?_, u * v, ?_⟩
      · rw [map_mul]; exact mul_mem (ha w) (hb w)
      · rw [Algebra.TensorProduct.tmul_mul_tmul]; rfl
    · intro x _; rw [zero_mul]; exact zero_mem _
    · intro x _; rw [mul_zero]; exact zero_mem _
    · intro x y z _ _ _ h1 h2; rw [add_mul]; exact add_mem h1 h2
    · intro x y z _ _ _ h1 h2; rw [mul_add]; exact add_mem h1 h2
    · intro x y _ _ h; rw [neg_mul]; exact neg_mem h
    · intro x y _ _ h; rw [mul_neg]; exact neg_mem h

  have stepA : ∀ w : Fin n → Af D.host.F ⊗[D.host.F] D.host.E, (∀ i, w i ∈ intAE D) →
      a • w ∈ GlobalTheory.AdLat.hat D.host.F (Λ : Set (Fin n → D.host.E)) := by
    intro w hw
    have hw' : a • w = ∑ i, a • Pi.single i (w i) := by
      rw [← Finset.smul_sum, Finset.univ_sum_single]
    rw [hw']
    refine sum_mem fun i _ => ?_
    have key : ∀ z ∈ intAE D, a • Pi.single i z ∈ GlobalTheory.AdLat.hat D.host.F (Λ : Set (Fin n → D.host.E)) := by
      intro z hz
      induction hz using AddSubgroup.closure_induction with
      | mem z hz =>
        obtain ⟨β, hβ, o, rfl⟩ := hz
        apply AddSubgroup.subset_closure
        refine ⟨β, fun v => hβ v, (a : 𝓞 D.host.E) • Pi.single i (o : D.host.E), h1 _ (single_mem_stdLat i o), ?_⟩
        funext k
        by_cases hk : k = i
        · subst hk
          rw [Pi.smul_apply, Pi.smul_apply, Pi.single_eq_same, Pi.single_eq_same, nsmul_tmul, Algebra.smul_def]
        · simp [Pi.single_apply, hk]
      | zero => simp
      | add x y _ _ hx hy => rw [Pi.single_add, smul_add]; exact add_mem hx hy
      | neg x _ hx => rw [Pi.single_neg, smul_neg]; exact neg_mem hx
    exact key _ (hw i)
  induction hy using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨α, hα, x, hx, rfl⟩ := hz
    obtain ⟨o, ho⟩ := Classical.axiomOfChoice (mem_stdLat_coord (h2 x hx))
    have e : (a ^ 2) • (M *ᵥ fun i => α ⊗ₜ[D.host.F] x i) =
        a • (M *ᵥ fun j => α ⊗ₜ[D.host.F] ((o j : 𝓞 D.host.E) : D.host.E)) := by
      rw [pow_two, mul_smul, ← Matrix.mulVec_smul]
      congr 2
      funext j
      rw [Pi.smul_apply, nsmul_tmul, ← ho j]
      simp [Algebra.smul_def]
    rw [e]
    refine stepA _ fun i => ?_
    simp only [Matrix.mulVec, dotProduct]
    refine sum_mem fun j _ => mulMem (hM i j) (AddSubgroup.subset_closure ⟨α, fun v => hα v, o j, rfl⟩)
  | zero => simp
  | add y z _ _ hy hz => rw [Matrix.mulVec_add, smul_add]; exact add_mem hy hz
  | neg y _ hy => rw [Matrix.mulVec_neg, smul_neg]; exact neg_mem hy

end GlobalTheory.HatIntSmul
end

section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix

theorem _root_.GlobalTheory.T.detCharacter_eq_of_marked_lattice_isometry : ∀ {D : D7} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} (l : Level H) (V : HSp D)
    (io : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)) (hio : LinearMap.range io = latG V 1)
    (A A' : Datum H) (t : Dw.La →ₗ[𝓞 D.host.E] A.La) (t' : Dw.La →ₗ[𝓞 D.host.E] A'.La)
    (X X' : Data D.host.E V.rank) (φ : A.La ≃ₗ[𝓞 D.host.E] X.Λ) (φ' : A'.La ≃ₗ[𝓞 D.host.E] X'.Λ) (g g' : GA D V)
    (hW : ModelW V rfl X) (hW' : ModelW V rfl X')
    (hE : ∀ a b, ((A.EF a b : ℤ) : ℚ) =
      Algebra.trace ℚ D.host.E (-X.ξ0 * herm X.Gm (φ a : Fin V.rank → D.host.E) (φ b)))
    (hE' : ∀ a b, ((A'.EF a b : ℤ) : ℚ) =
      Algebra.trace ℚ D.host.E (-X'.ξ0 * herm X'.Gm (φ' a : Fin V.rank → D.host.E) (φ' b)))
    (hL : (X.Λ : Set (Fin V.rank → D.host.E)) =
      (fun v : Fin V.rank → D.host.E => v ∘ Fin.cast rfl) '' (latG V g : Set _))
    (hL' : (X'.Λ : Set (Fin V.rank → D.host.E)) =
      (fun v : Fin V.rank → D.host.E => v ∘ Fin.cast rfl) '' (latG V g' : Set _))
    (hm : ∀ a ∈ l.Mb.map (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) • (⊤ : Submodule (𝓞 D.host.E) Dw.La),
      ∃ w ∈ latGHat V g, finVec V ((φ (t a) : Fin V.rank → D.host.E) ∘ Fin.cast rfl) -
        (finHom V g).1.mulVec (finVec V (io a)) = (l.M : ℕ) • w)
    (hm' : ∀ a ∈ l.Mb.map (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) • (⊤ : Submodule (𝓞 D.host.E) Dw.La),
      ∃ w ∈ latGHat V g', finVec V ((φ' (t' a) : Fin V.rank → D.host.E) ∘ Fin.cast rfl) -
        (finHom V g').1.mulVec (finVec V (io a)) = (l.M : ℕ) • w)
    (gam : A.La ≃ₗ[𝓞 D.host.E] A'.La) (hgE : ∀ a b, A'.EF (gam a) (gam b) = A.EF a b)
    (hgm : ∀ a ∈ l.Mb.map (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) • (⊤ : Submodule (𝓞 D.host.E) Dw.La),
      ∃ x, gam (t a) = t' a + l.M • x)
    (xi : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ →* ℂˣ)
    (hxi1 : ∀ u : GA D V, gLat V u = latHat V → (∃ w ∈ GlobalTheory.AdLat.hat1 D.host.F (Set.range (algebraMap (𝓞 D.host.E) D.host.E)),
      ((Matrix.GeneralLinearGroup.det (finHom V u) : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ) :
        (Af D.host.F ⊗[D.host.F] D.host.E)) - 1 = (l.M : ℕ) • w) → xi (Matrix.GeneralLinearGroup.det (finHom V u)) = 1)
    (hxi2 : ∀ γ ∈ GQ V, xi (Matrix.GeneralLinearGroup.det (finHom V γ)) = 1), xi (Matrix.GeneralLinearGroup.det (finHom V g')) = xi (Matrix.GeneralLinearGroup.det (finHom V g)) := by
  first | exact @GlobalTheory.MarkIso.xi_det_eq_of_marked_isometry | exact GlobalTheory.MarkIso.xi_det_eq_of_marked_isometry | (intros; apply GlobalTheory.MarkIso.xi_det_eq_of_marked_isometry <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwistTypeDet


open Classical in
theorem detChar_eq_one_of_suppAt : ∀ (D : D7) (S T : HSp D) (B : Base S T), B.Good → S.SigOK → ∀ (A : Type) [CommGroup A] (t : Twist D A), t.Good → B.admitted t.Q → ∀ (u : G0 B.G.Pg T.rank) (κ : GA D T), Lev.IsLevelLift T B.F.βT B.G.levT u κ → SuppAt (idem B.G.Pg) T κ → detChar T t.chi κ = 1 := by
  intro D S T B hB _ A _ t ht hadm u κ hlift hsupp
  have hst : Lev.finE T κ ∈ St B.F.βT := Formalism.L2.DIV.parLev_St hlift.2.1
  rw [GlobalTheory.TwistDetStabAll.detChar_eq_prod_res B hB t ht hlift.1 hst]
  refine Finset.prod_eq_one fun PP hPP => ?_
  obtain ⟨P, hPg, hQ, hsplit⟩ := hadm.1.split
  have hnot : PP ∉ B.G.Pg := fun h => Finset.disjoint_left.mp hadm.1.disj h (Finset.mem_union_right _ hPP)
  rw [GlobalTheory.ExportSeries.redFn_eq_one_of_suppAt B.F.βT hsplit hPg (hQ (Finset.mem_union_right _ hPP)) hnot hst hsupp,
    map_one, map_one]

end GlobalTheory.TwistTypeDet
end

section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.ArcQ GlobalTheory.Frames GlobalTheory.Reg GlobalTheory.GoodPts GlobalTheory.GoodTransfer

theorem _root_.GlobalTheory.T.integral_framed_point_good_reduction_definite_signature : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), Dw.q = 0 → ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io), Good y := by
  first | exact @GlobalTheory.GoodDefinite.good_of_definite | exact GlobalTheory.GoodDefinite.good_of_definite | (intros; apply GlobalTheory.GoodDefinite.good_of_definite <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

theorem _root_.GlobalTheory.T.localCoeff_vanishes_offLevel_badPlaces : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Laws R F → R.FullP → ∀ i t, BadSupp R i t := by
  first | exact @GlobalTheory.BadSuppPf.badSupp | exact GlobalTheory.BadSuppPf.badSupp | (intros; apply GlobalTheory.BadSuppPf.badSupp <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie
open Formalism.IndefR.Links
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.Lev Formalism.L2.DIV Formalism.IndefR.Mult



theorem _root_.GlobalTheory.T.complex_principal_level_eq_realisation_principal_level : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (Rl : RealDat3 D A3 Ks) {cG : G0 Rl.Pg D.R.r ≃* G0g D.nd} {ρ : Setup D.ntw}, RealPin Rl cG ρ → ∀ (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool), ρ.levK i j b = levG (Wc D j) (Rl.βW j) (Rl.datWp j Rl.triv) := by
  first | exact @GlobalTheory.SeriesTie.levK_eq_levG_triv | exact GlobalTheory.SeriesTie.levK_eq_levG_triv | (intros; apply GlobalTheory.SeriesTie.levK_eq_levG_triv <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie
open Formalism.IndefR.Links
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.twistingCharacter_admissibleGaloisTwist_good : ∀ (D : D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (ρ : Setup X), ρ.Good → ∀ (i : X.Tw) (j : Fin D.R.m) (b : Bool) (k : ℕ) (Q : Finset (Pl D.host.E)) (ψ : G D.host.E N.Om →* (X.Ok i k)ˣ), Formalism.MainNotions.IntegralHeckeForms.TwOK i k Q ψ → (ρ.tw i b k Q ψ).Good ∧ (ρ.B i j b).admitted (ρ.tw i b k Q ψ).Q ∧ ∀ x, ∃ u : (X.Ok i k)ˣ, (((ρ.tw i b k Q ψ).chi x : Circle) : ℂ) = ρ.eOk i b k u := by
  first | exact @GlobalTheory.TwistGood.tw_good | exact GlobalTheory.TwistGood.tw_good | (intros; apply GlobalTheory.TwistGood.tw_good <;> assumption)
end
