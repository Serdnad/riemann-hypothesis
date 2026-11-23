module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle007
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle006
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle020
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TowerEx
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittCoreInclusionMemCompletedHomLattice
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle163
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevelStepVectorEqHeisenbergCombinationVacuum
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle063
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle064
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilRepresentationVacuumCosetVectorsGrid
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNsmulIntMemLatO
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle632
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FinitePartTraceCharacterIdempotentInverseDiffere
import Formalism.LocalToGlobal.ProjectiveLattices.HostInt
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PeriodGroupsReduceSplitPlaceFamilySucc
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle550
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawLastTwoStepsDoubleLiftPeriodValue
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle688
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle450
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle502
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle544
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle469
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle699
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle704
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle701
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle726
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
open NumberField

theorem _root_.GlobalTheory.T.exists_heckeKernel_coset_framedPoint : ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.HeckePrimeDetection.HeckePointLaws → GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.SplitLinearModel D → GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.VacFixed D →
    ∀ (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m)
    (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A)
    (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec),
    R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsFam → R.IsModels → R.IsThP → TieIn T R κ v₀ →
    ∀ (i : Fin D.R.m) (σ : T.Q.c.F →+* ℂ), σ = T.σ₀ → ∀ hV : T.V ((i : ℕ) + 1) σ = Wc D i,
      GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.FramePin T R i σ hV →
    ∀ (P : Formalism.L2.DIV.Pl D.host.E) (p k : ℕ) (α : GA D (Wc D i)) (Rc : Finset (GA D (Wc D i))),
      GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.IsUnitaryHeckeOperatorSplitPrimeData T R i P p k α Rc →
    ∀ (h : GA D (Wc D i)) (hx : (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).2 ∈ ((T.U ((i : ℕ) + 1) σ).X (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).1).dom),
      letI : Field (CAt σ) := inferInstanceAs (Field ℂ)
      haveI : IsAlgClosed (CAt σ) := inferInstanceAs (IsAlgClosed ℂ)
      ∀ C : hkKer (Xo := T.Q.Xo ((i : ℕ) + 1)) P.asIdeal p k (CAt σ) ((T.U ((i : ℕ) + 1) σ).un (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).1 ⟨(GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).2, hx⟩),
        ∃ a ∈ Rc, ∀ z, hkRelFr P.asIdeal p k (GlobalTheory.ThetaTrace.hkTr (T.Q.Xo ((i : ℕ) + 1)) T.Q.c p) (CAt σ) ((T.U ((i : ℕ) + 1) σ).un (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).1 ⟨(GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).2, hx⟩) C z →
          ∃ (hx' : (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV (h * a)).2 ∈ ((T.U ((i : ℕ) + 1) σ).X (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV (h * a)).1).dom) (t : Ix (T.Q.Dw ((i : ℕ) + 1)) → (CAt σ)ˣ),
            (∀ j, j ≠ none → t j = 1) ∧ FrBor t ((T.U ((i : ℕ) + 1) σ).un (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV (h * a)).1 ⟨(GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV (h * a)).2, hx'⟩) z := by
  first | exact @GlobalTheory.HeckeExist.exists_coset_frBor_of_hkKer | exact GlobalTheory.HeckeExist.exists_coset_frBor_of_hkKer | (intros; apply GlobalTheory.HeckeExist.exists_coset_frBor_of_hkKer <;> assumption)
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

namespace GlobalTheory.RowInt

variable {D : D7}

theorem latO_negSp_le (S T : HSp D) (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E))
    (P : HeightOneSpectrum (𝓞 D.host.F) → Prop) : latO (negSp S) T LS LT P ≤ latO S T LS LT P := by
  unfold latO
  rw [AddSubgroup.closure_le]
  rintro w ⟨α, hα, hP, a, ha, s, hs, t, ht, rfl⟩
  rw [← neg_neg (Matrix.of _)]
  refine neg_mem (AddSubgroup.subset_closure ⟨α, hα, hP, a, ha, s, hs, t, ht, ?_⟩)
  funext i j
  simp [negSp_gram, Finset.sum_neg_distrib, TensorProduct.tmul_neg]

theorem smul_mem_latO_at : All fun {D} _ _ _ {G} _ _ =>
    ∀ i, i < D.R.m → ∀ v, ∀ e ∈ intAt D (· = v), ∀ u ∈ latRow G i,
      e • u ∈ latO _ _ (G.Λ (.grid (i + 1) 0) : Set _) (G.Λ (.grid i 0) : Set _) (· = v) := by
  intro D _ T L μ0 _ sc G W M _ i _ v e he u hu
  have h0 : u ∈ latO (negSp (G.V (.grid (i + 1) 0))) (G.V (.grid i 0)) (G.Λ (.grid (i + 1) 0) : Set _)
      (G.Λ (.grid i 0) : Set _) (fun _ => True) := hu.1
  have h1 : u ∈ latO (G.V (.grid (i + 1) 0)) (G.V (.grid i 0)) (G.Λ (.grid (i + 1) 0) : Set _)
      (G.Λ (.grid i 0) : Set _) (fun _ => True) := latO_negSp_le _ _ _ _ _ h0
  have h2 := GlobalTheory.LatticeStable.smul_mem_latO D _ _ _ _ _ e he.2 u h1
  have h3 : MxAt (· = v) (e • u) := fun a b => Ideal.mul_mem_right _ _ he.1
  exact (GlobalTheory.AscFinWit.mem_latO_at h3).1 h2

end GlobalTheory.RowInt
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

namespace GlobalTheory.RowLoc

variable {D : D7}

theorem gen_negSp (S T : HSp D) (α : Af D.host.F) (a : D.host.E) (s : Fin S.rank → D.host.E) (t : Fin T.rank → D.host.E) :
    (Matrix.of fun i j => (pairA D.host.F 0 α) ⊗ₜ[D.host.F] (a * t i * ∑ k, star (s k) * (negSp S).gram k j) : WO (negSp S) T) =
      -(Matrix.of fun i j => (pairA D.host.F 0 α) ⊗ₜ[D.host.F] (a * t i * ∑ k, star (s k) * S.gram k j) : WO S T) := by
  funext i j
  simp [negSp_gram, Finset.sum_neg_distrib, TensorProduct.tmul_neg]

theorem mem_latO_negSp {S T : HSp D} {LS : Set (Fin S.rank → D.host.E)} {LT : Set (Fin T.rank → D.host.E)}
    {P : GlobalTheory.FinPl.Pl D → Prop} {u : WO S T} : u ∈ latO (negSp S) T LS LT P ↔ u ∈ latO S T LS LT P := by
  constructor
  · intro hu
    induction hu using AddSubgroup.closure_induction with
    | mem w hw =>
      obtain ⟨α, hα, hP, a, ha, s, hs, t, ht, rfl⟩ := hw
      rw [gen_negSp]
      exact neg_mem (AddSubgroup.subset_closure ⟨α, hα, hP, a, ha, s, hs, t, ht, rfl⟩)
    | zero => exact zero_mem _
    | add x y _ _ hx hy => exact add_mem hx hy
    | neg x _ hx => exact neg_mem hx
  · intro hu
    induction hu using AddSubgroup.closure_induction with
    | mem w hw =>
      obtain ⟨α, hα, hP, a, ha, s, hs, t, ht, rfl⟩ := hw
      rw [← neg_neg (Matrix.of _), ← gen_negSp]
      exact neg_mem (AddSubgroup.subset_closure ⟨α, hα, hP, a, ha, s, hs, t, ht, rfl⟩)
    | zero => exact zero_mem _
    | add x y _ _ hx hy => exact add_mem hx hy
    | neg x _ hx => exact neg_mem hx

theorem latRow_at : All fun {D} _ _ _ {G} _ _ => ∀ i, i < D.R.m → ∀ v ∉ G.pl.S0, ∀ u : WO (G.V (.grid (i + 1) 0)) (G.V (.grid i 0)),
    MxAt (· = v) u → (u ∈ latRow G i ↔ u ∈ latO _ _ (G.Λ (.grid (i + 1) 0) : Set _) (G.Λ (.grid i 0) : Set _) (· = v)) := by
  intro D _ T L μ0 _ sc G W M _ i _ v hv u hu
  have hoff : ∀ e : AE D, IsIdemSum e G.pl.W0 → e • u = 0 := by
    intro e he
    have he' := GlobalTheory.StepComb.idemSum_mem_idAt he
    have hev : e ∈ idOff D (· = v) := by
      rw [idOff, Ideal.mem_iInf]
      rintro ⟨w, rfl⟩
      rw [idAt, Ideal.mem_inf, Ideal.mem_iInf] at he'
      refine he'.2 ⟨w, ?_⟩
      rintro ⟨PP, hPP, hw⟩
      classical
      simp only [Places.W0, Finset.mem_image] at hPP
      obtain ⟨s, hs, rfl⟩ := hPP
      exact hv (by rw [hw, G.pl.under_w hs]; exact hs)
    refine Matrix.ext fun a b => ?_
    rw [Matrix.smul_apply, smul_eq_mul, mul_comm, Matrix.zero_apply]
    exact GlobalTheory.FinPl.FlatUnitPf.idAt_mul_idOff _ _ _ (hu a b) hev
  have k1 : u ∈ latO (negSp (G.V (.grid (i + 1) 0))) (G.V (.grid i 0)) (G.Λ (.grid (i + 1) 0) : Set _) (G.Λ (.grid i 0) : Set _) (fun _ => True) ↔
      u ∈ latO (G.V (.grid (i + 1) 0)) (G.V (.grid i 0)) (G.Λ (.grid (i + 1) 0) : Set _) (G.Λ (.grid i 0) : Set _) (fun _ => True) := mem_latO_negSp
  have k2 : u ∈ latO (G.V (.grid (i + 1) 0)) (G.V (.grid i 0)) (G.Λ (.grid (i + 1) 0) : Set _) (G.Λ (.grid i 0) : Set _) (fun _ => True) ↔
      u ∈ latO (G.V (.grid (i + 1) 0)) (G.V (.grid i 0)) (G.Λ (.grid (i + 1) 0) : Set _) (G.Λ (.grid i 0) : Set _) (· = v) :=
    GlobalTheory.AscFinWit.mem_latO_at (LS := G.Λ (.grid (i + 1) 0)) (LT := G.Λ (.grid i 0)) hu
  exact ⟨fun h => k2.1 (k1.1 h.1), fun h => ⟨k1.2 (k2.2 h), fun e he => by rw [hoff e he]; exact zero_mem _⟩⟩

end GlobalTheory.RowLoc
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory.AscFin.DepLat

variable {D : D7}

theorem finLat_of_nsmul {m n : ℕ} {Λ A : AddSubgroup (Mx D m n)} (h : FinLat Λ) (hle : A ≤ Λ)
    {K : ℕ} (hK : 0 < K) (hA : ∀ u ∈ Λ, K • u ∈ A) : FinLat A := by
  obtain ⟨U, h1, h2, h3⟩ := h.opn
  have inv : (K : AE D) * incA D (K : D.host.E)⁻¹ = 1 := by
    rw [← map_natCast (incA D), ← map_mul, mul_inv_cancel₀ (Nat.cast_ne_zero.2 hK.ne'), map_one]
  have hc : Continuous fun a : Mx D m n => incA D (K : D.host.E)⁻¹ • a := continuous_id.const_smul (incA D (K : D.host.E)⁻¹)
  refine GlobalTheory.AscFinWit.finLat_of (fun a ha => h.fin a (hle ha))
    ⟨_, h1.preimage hc, by rwa [Set.mem_preimage, smul_zero], fun a ha hb => ?_⟩ h.cpt fun a ha => hle ha
  have := hA _ (h3 _ ha fun i j => Ideal.mul_mem_left _ _ (hb i j))
  rwa [← Nat.cast_smul_eq_nsmul (AE D), smul_smul, inv, one_smul] at this

theorem finLat_depLat : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (p : Pair T), IsSelfDualC (G.pS p) (G.latS p) → IsSelfDualC (G.pT p) (G.latT p) → FinLat (depLat G p) := by
  intro D T L sc G p hS hT
  obtain ⟨K, hK, h⟩ := GlobalTheory.GridWeil.exists_nsmul_latO (T := G.pT p) (ΛT := G.latT p) hS (G.pl.modul_ne_bot sc)
  refine finLat_of_nsmul (GlobalTheory.AscFinWit.finLat_latO (GlobalTheory.ProjXCols.selfDual_isFullLattice _ _ hS) (GlobalTheory.ProjXCols.selfDual_isFullLattice _ _ hT)) (fun u hu => hu.1) hK
    fun u hu => ⟨nsmul_mem hu K, fun e he => ?_⟩
  rw [smul_comm]
  exact h _ (GlobalTheory.LatticeStable.smul_mem_latO D _ _ _ _ _ e
    (GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← RingHom.map_mul, GlobalTheory.PlaceVec.idemSum_mul_self he])) _ hu)

end GlobalTheory.AscFin.DepLat
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory.AscFin

theorem finLat_latO_selfDual : ∀ {D : D7} (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → FinLat (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) := fun S T ΛS ΛT hS hT => GlobalTheory.AscFinWit.finLat_latO (GlobalTheory.ProjXCols.selfDual_isFullLattice _ _ hS) (GlobalTheory.ProjXCols.selfDual_isFullLattice _ _ hT)

end GlobalTheory.AscFin
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

namespace GlobalTheory.BigLoc

variable {D : D7}

theorem latO_tgt_le {S T : HSp D} {LS : Set (Fin S.rank → D.host.E)} {LT LT' : Set (Fin T.rank → D.host.E)}
    (v : GlobalTheory.FinPl.Pl D) (c : 𝓞 D.host.F) (hc : c ∉ v.asIdeal)
    (h : ∀ t ∈ LT, (((c : D.host.F) : D.host.E)) • t ∈ LT') :
    latO S T LS LT (· = v) ≤ latO S T LS LT' (· = v) := by
  refine (AddSubgroup.closure_le _).2 ?_
  rintro w ⟨α, hα, hsupp, a, ha, s, hs, t, ht, rfl⟩
  refine AddSubgroup.subset_closure ⟨GlobalTheory.IdeleAA.gam v c * α, GlobalTheory.IdeleAA.gam_mul_int v c hc hα,
    GlobalTheory.IdeleAA.gam_mul_supp v c α, a, ha, s, hs, _, h t ht, ?_⟩
  ext i j
  simp only [Matrix.of_apply]
  rw [← GlobalTheory.IdeleAA.pair_scale v c α hsupp]
  congr 1
  have h0 := GlobalTheory.IdeleAA.coe_ne_zero v c hc
  rw [Pi.smul_apply, smul_eq_mul]
  field_simp

end GlobalTheory.BigLoc

namespace GlobalTheory.BigLoc

variable {D : D7}

theorem coe_alg (c : 𝓞 D.host.F) :
    algebraMap (𝓞 D.host.E) D.host.E (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) c) = ((c : D.host.F) : D.host.E) := rfl

theorem exists_c {T : Type} {L : LevCh D T} (P : Places L) (sc : Consts) {v : GlobalTheory.FinPl.Pl D} (hv : v ∉ P.S0) :
    ∃ c : 𝓞 D.host.F, c ∉ v.asIdeal ∧ algebraMap (𝓞 D.host.F) (𝓞 D.host.E) c ∈ P.modul sc ∧
      algebraMap (𝓞 D.host.F) (𝓞 D.host.E) c ∈ P.modulBar sc := by
  classical
  set J : Ideal (𝓞 D.host.F) := ∏ v' ∈ P.S0, v'.asIdeal ^ P.depth sc v' with hJdef
  have hJ : ¬ J ≤ v.asIdeal := by
    intro h
    obtain ⟨v', hv', hle⟩ := (Ideal.IsPrime.prod_le v.isPrime).1 h
    have h1 : v'.asIdeal ≤ v.asIdeal := Ideal.IsPrime.le_of_pow_le (hP := v.isPrime) hle
    have : v' = v := HeightOneSpectrum.ext (v'.isMaximal.eq_of_le v.isPrime.ne_top h1)
    exact hv (this ▸ hv')
  obtain ⟨c, hcJ, hcv⟩ := Set.not_subset.1 hJ
  have hmap : J.map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) ≤ P.modul sc := by
    rw [hJdef]
    change Ideal.mapHom (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) _ ≤ _
    rw [map_prod]
    refine Finset.prod_le_prod' fun v' hv' => ?_
    rw [map_pow]
    refine pow_le_pow_left' ?_ _
    refine Ideal.map_le_iff_le_comap.2 (le_of_eq ?_)
    have := congrArg HeightOneSpectrum.asIdeal (P.under_w hv')
    exact this.symm
  have hmod : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) c ∈ P.modul sc := hmap (Ideal.mem_map_of_mem _ hcJ)
  refine ⟨c, hcv, hmod, ?_⟩
  have hfix : D.host.conj • algebraMap (𝓞 D.host.F) (𝓞 D.host.E) c = algebraMap (𝓞 D.host.F) (𝓞 D.host.E) c := by
    apply FaithfulSMul.algebraMap_injective (𝓞 D.host.E) D.host.E
    rw [Formalism.L2.Pj.algebraMap_conj_smul, coe_alg]
    exact GlobalTheory.IdeleAA.conj_F c
  unfold Places.modulBar
  rw [← hfix]
  exact Ideal.smul_mem_pointwise_smul _ _ _ hmod

end GlobalTheory.BigLoc

namespace GlobalTheory.BigLoc

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts}

theorem smul_mem_idLat (G : GridData L sc) {n : ℕ} {Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)} {c : 𝓞 D.host.F}
    (hc : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) c ∈ G.pl.modul sc) (hne : G.pl.modulBar sc ≠ ⊥)
    {y : Fin n → D.host.E} (hy : y ∈ Λ) : ((c : D.host.F) : D.host.E) • y ∈ idLat (shiftId G) Λ := by
  refine Submodule.subset_span ⟨_, ?_, y, hy, rfl⟩
  unfold shiftId
  rw [← mul_one ((c : D.host.F) : D.host.E)]
  exact FractionalIdeal.mul_mem_mul ((FractionalIdeal.mem_coeIdeal (𝓞 D.host.E)⁰).2 ⟨_, hc, coe_alg c⟩)
    (FractionalIdeal.one_mem_inv_coe_ideal hne)

theorem smul_idLat_mem (G : GridData L sc) {n : ℕ} {Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)} {c : 𝓞 D.host.F}
    (hcb : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) c ∈ G.pl.modulBar sc) (hne : G.pl.modulBar sc ≠ ⊥)
    {z : Fin n → D.host.E} (hz : z ∈ idLat (shiftId G) Λ) : ((c : D.host.F) : D.host.E) • z ∈ Λ := by
  refine Submodule.span_induction (p := fun z _ => ((c : D.host.F) : D.host.E) • z ∈ Λ) ?_ ?_ ?_ ?_ hz
  · rintro _ ⟨s, hs, y, hy, rfl⟩
    have hm : ((c : D.host.F) : D.host.E) * s ∈ ((G.pl.modul sc : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) := by
      have := FractionalIdeal.mul_mem_mul ((FractionalIdeal.mem_coeIdeal (𝓞 D.host.E)⁰).2 ⟨_, hcb, coe_alg c⟩) hs
      have h0 : ((G.pl.modulBar sc : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) ≠ 0 := by
        rwa [Ne, FractionalIdeal.coeIdeal_eq_zero]
      rwa [shiftId, mul_left_comm, mul_inv_cancel₀ h0, mul_one] at this
    obtain ⟨o, -, ho⟩ := (FractionalIdeal.mem_coeIdeal (𝓞 D.host.E)⁰).1 hm
    rw [smul_smul, ← ho, algebraMap_smul]
    exact Λ.smul_mem o hy
  · simp
  · intro x y _ _ hx hy; rw [smul_add]; exact add_mem hx hy
  · intro a x _ hx; rw [smul_comm]; exact Λ.smul_mem a hx

end GlobalTheory.BigLoc

theorem GlobalTheory.BigLoc.latBig_at : All fun {D} _ _ _ {G} _ _ => ∀ i, i < D.R.m → ∀ v ∉ G.pl.S0,
    ∀ u : WO (G.V (.grid (i + 1) 0)) (G.V (.grid i 0)), MxAt (· = v) u →
      (u ∈ latBig G i ↔ u ∈ latO _ _ (G.Λ (.grid (i + 1) 0) : Set _) (G.Λ (.grid i 0) : Set _) (· = v)) := by
  intro D _ T L μ0 _ sc G W M _ i _ v hv u hu
  obtain ⟨c, hcv, hc, hcb⟩ := GlobalTheory.BigLoc.exists_c G.pl sc hv
  have hne : G.pl.modulBar sc ≠ ⊥ := fun h => by
    rw [h, Ideal.mem_bot] at hcb
    apply GlobalTheory.IdeleAA.coe_ne_zero v c hcv
    rw [← GlobalTheory.BigLoc.coe_alg, hcb, map_zero]
  unfold latBig
  rw [GlobalTheory.AscFinWit.mem_latO_at hu]
  exact ⟨fun h => GlobalTheory.BigLoc.latO_tgt_le v c hcv (fun t ht => GlobalTheory.BigLoc.smul_idLat_mem G hcb hne ht) h,
    fun h => GlobalTheory.BigLoc.latO_tgt_le v c hcv (fun t ht => GlobalTheory.BigLoc.smul_mem_idLat G hc hne ht) h⟩
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

namespace GlobalTheory.CosetFJ

variable {D : D7}

theorem coset_of_places {V₀ W W₀ : HSp D} {ρ σ : ℕ} (dW : HypDec W W₀ σ) (p : Pieces V₀ W W₀ ρ σ)
    (x : Mx D W.rank ρ) (y : Mx D V₀.rank σ) (ψ : AddChar (AF D.host.F) ℂ) (K : Subgroup (GA D W))
    (S : Finset (GlobalTheory.FinPl.Pl D)) :
    (∀ v ∈ S, ∀ g ∈ grpAt W (· = v), Cond dW p x y ψ (· = v) g →
      ∃ r ∈ Rgrp W x, r ∈ grpAt W (· = v) ∧ ∃ k ∈ K, k ∈ grpAt W (· = v) ∧ g = r * k) →
    ∀ g ∈ grpAt W (· ∈ S), Cond dW p x y ψ (· ∈ S) g →
      ∃ r ∈ Rgrp W x, r ∈ grpAt W (· ∈ S) ∧ ∃ k ∈ K, k ∈ grpAt W (· ∈ S) ∧ g = r * k := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    intro _ g hg _
    have e : g = 1 := GlobalTheory.QRed.grpAt_eq_one (fun v => by simp) hg
    exact ⟨1, one_mem _, one_mem _, 1, one_mem _, one_mem _, by rw [e, one_mul]⟩
  | insert v s hv ih =>
    intro hloc g hg hc
    obtain ⟨g₁, hg₁, g₂, hg₂o, rfl⟩ := ((GlobalTheory.FinPl.localComponents D (· = v)).2 W).1 g
    have mono : ∀ {P : GlobalTheory.FinPl.Pl D → Prop} {a : GA D W}, (∀ w, P w → w ∈ insert v s) → a ∈ grpAt W P →
        a ∈ grpAt W (· ∈ insert v s) := fun hP ha => GlobalTheory.DStepSuppSecond.grpAt_mono hP ha
    have hg₁' : g₁ ∈ grpAt W (· ∈ insert v s) := mono (fun w hw => by simp [hw]) hg₁
    have hg₂ : g₂ ∈ grpAt W (· ∈ insert v s) := by
      have := mul_mem (inv_mem hg₁') hg
      rwa [inv_mul_cancel_left] at this
    have hg₂s : g₂ ∈ grpAt W (· ∈ s) :=
      GlobalTheory.QRed.grpAt_of_off (fun w hw => by rcases Finset.mem_insert.1 hw with h | h; exacts [Or.inl h.symm, Or.inr h])
        hg₂ hg₂o
    have hcomm : g₁ * g₂ = g₂ * g₁ := ((GlobalTheory.FinPl.localComponents D (· = v)).2 W).2.1 g₁ hg₁ g₂ hg₂o
    have hdisj : ∀ w, w = v → ¬ w ∈ s := fun w hw hws => hv (hw ▸ hws)
    have hg₁o : g₁ ∈ grpOff W (· ∈ s) := GlobalTheory.QRed.grpAt_off hdisj hg₁
    have hc₁ := GlobalTheory.T.of_mul_trivialAtPlaces_subset dW p x y ψ _ _ g₁ g₂ (fun w hw => by simp [hw]) hg₁ hg₂o hcomm hc
    have hc₂ := GlobalTheory.T.of_mul_trivialAtPlaces_subset dW p x y ψ _ _ g₂ g₁ (fun w hw => Finset.mem_insert_of_mem hw) hg₂s hg₁o hcomm.symm
      (hcomm ▸ hc)
    obtain ⟨r₁, hr₁, hr₁a, k₁, hk₁, hk₁a, e₁⟩ := hloc v (Finset.mem_insert_self v s) g₁ hg₁ hc₁
    obtain ⟨r₂, hr₂, hr₂a, k₂, hk₂, hk₂a, e₂⟩ :=
      ih (fun w hw => hloc w (Finset.mem_insert_of_mem hw)) g₂ hg₂s hc₂
    have hk₁r₂ : k₁ * r₂ = r₂ * k₁ := GlobalTheory.SeeSawLastValue.grpAt_comm hdisj hk₁a hr₂a
    refine ⟨r₁ * r₂, mul_mem hr₁ hr₂, mul_mem (mono (fun w hw => by simp [hw]) hr₁a)
      (mono (fun w hw => Finset.mem_insert_of_mem hw) hr₂a), k₁ * k₂, mul_mem hk₁ hk₂,
      mul_mem (mono (fun w hw => by simp [hw]) hk₁a) (mono (fun w hw => Finset.mem_insert_of_mem hw) hk₂a), ?_⟩
    rw [e₁, e₂]
    calc r₁ * k₁ * (r₂ * k₂) = r₁ * (k₁ * r₂) * k₂ := by simp only [mul_assoc]
      _ = r₁ * r₂ * (k₁ * k₂) := by rw [hk₁r₂]; simp only [mul_assoc]

theorem one_coset_decomposition_base : OnStd fun {D} _ _ {sc} {G} W F => ∀ σ (h : 2 * (σ + 1) + 2 ≤ D.R.m) (h' : 2 * σ + 2 ≤ D.R.m), ∀ g ∈ grpAt _ (fun v => v ∈ G.pl.S0), Cond (F.dB σ h') (pcFB W F σ h h') (xFB F σ h') 0 W.ψ (fun v => v ∈ G.pl.S0) g → ∃ r ∈ Rgrp _ (xFB F σ h'), r ∈ grpAt _ (fun v => v ∈ G.pl.S0) ∧ ∃ k ∈ lev G (.grid (2 * σ + 2) 0), k ∈ grpAt _ (fun v => v ∈ G.pl.S0) ∧ g = r * k := by
  intro D hD T L μ0 hL sc G W M hM F _hF σ h h' g hg hc
  refine coset_of_places (F.dB σ h') (pcFB W F σ h h') (xFB F σ h') 0 W.ψ (lev G (.grid (2 * σ + 2) 0)) G.pl.S0 ?_ g hg hc
  intro v hv g hg hc
  obtain ⟨u, a, ha, hoff⟩ := hc.pt
  obtain ⟨k, hk, hka, hk'⟩ := GlobalTheory.T.exists_level_element_off_place D hD T L μ0 hL sc G W M hM F _hF σ h h' v hv g hg u a ha hoff
  obtain ⟨r, hr, hra, e⟩ := GlobalTheory.T.exists_unitriangularStabilizer_of_principal_move _ (xFB F σ h') (· = v) g k u hg hka hk'
  exact ⟨r, hr, hra, k⁻¹, inv_mem hk, inv_mem hka, e⟩

end GlobalTheory.CosetFJ
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RowBasic

theorem c3 : Big fun ch => ∀ t (M : Vol ch.G), M.Is t → IsHaarDef M := by
  refine ⟨0, fun _ _ _ => ⟨0, fun D _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ch _ _ => ?_⟩⟩
  intro t M hM X hX _
  refine (hM.vtx X ?_).haar_fund
  cases X <;> simp only [DefNode, Node.InRange] at hX ⊢ <;> omega

theorem c4 : Big fun ch => ∀ t Φ β M, IsTermVol t ch.S.toGridChoice Φ β M → IsHaarDef M := by
  refine ⟨0, fun _ _ _ => ⟨0, fun D _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ch _ _ => ?_⟩⟩
  intro t Φ β M hM X hX hne
  cases X with
  | grid i j =>
    obtain ⟨hi, rfl⟩ := hX
    exact (hM.2 i hi).haar_fund
  | top j =>
    have : j < D.R.m := lt_of_le_of_ne hX (fun e => hne (by rw [e]))
    exact (hM.1 j this).haar_fund
  | core i => exact hX.elim

theorem basicAt : Big fun ch => BasicAt ch := by
  have hall := (((((((GlobalTheory.T.besselColumnScalarFunction_continuous_leftInvariant.and GlobalTheory.T.gridTopVertexFormFunction_continuous_left_invariant).and c3).and c4).and GlobalTheory.T.unfoldingJointData_jointlySmoothTheta_evenIndex).and GlobalTheory.T.rowTest_flippedFiniteTensor_row_isThetaFunction).and GlobalTheory.T.rowTest_heisenberg_combinations_joint_row_good).and GlobalTheory.T.rowTest_exists_combinations_of_expansion)
  refine GlobalTheory.RowReal.big_mono (fun ch h => ?_) hall
  rcases h with ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5a⟩, h5b⟩, h6⟩, h7⟩
  refine ⟨fun a => ⟨(h1 a).2, (h1 a).1⟩, fun t y => ⟨(h2 t y).2, (h2 t y).1⟩, h3, h4, ?_, h6, h7⟩
  intro t Φ τ hτ M hM d hd P hh
  exact ⟨fun j hj hjm => h5a t Φ τ hτ M hM d hd P hh j hj hjm, h5b t Φ τ hτ d hd⟩

end GlobalTheory.RowBasic
end
