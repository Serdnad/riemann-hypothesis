module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle007
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle006
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle020
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Formalism.SharpRestriction.CuspSpanNormBounds.BesselShellMomentBounds
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle081
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle005
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittCoreInclusionMemCompletedHomLattice
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlatDictionaryRelativeBaseVacuaLargeDepth
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TiltedPointsCoveredByRepresentativeCells
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.PartFixed
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralStripEqZeroOfRealModulationVanishing
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle310
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle736
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle446
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle252
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle410
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TowerEx
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle489
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle735
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle680
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle043
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle667
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
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle024

@[expose] public section

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

set_option autoImplicit false

namespace GlobalTheory.HeckeTerm

open NumberField in
theorem splitSup {D : D7} (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) {P : Formalism.L2.DIV.Pl D.host.E}
    (h : Formalism.HermitianLatticesTheory.conjIdeal (K := D.host.E) P.asIdeal ≠ P.asIdeal) :
    P.asIdeal ⊔ P.asIdeal.map (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) = ⊤ := by
  by_contra hne
  have hsub : P.asIdeal.map (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) ≤ P.asIdeal :=
    le_sup_right.trans (P.isMaximal.eq_of_le hne le_sup_left).ge
  apply h
  rw [Formalism.L2.Col.conjIdeal_asIdeal]
  refine (P.isMaximal.eq_of_le (Formalism.L2.Col.conjPrime₂ P).isPrime.ne_top fun a ha => ?_).symm
  rw [Formalism.L2.Col.mem_conjP]
  have : Formalism.L2.Col.cO D.host.E a = H.bar a := RingOfIntegers.ext (H.bar_eq a).symm
  rw [this]
  exact hsub (Ideal.mem_map_of_mem (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) ha)

theorem phiW_unfold {D : D7} (T : CoreJ D) (j : ℕ) (σ : T.Q.c.F →+* ℂ) {W : HSp D} (hV : T.V j σ = W)
    (a : (D.host.E →+* ℂ) × ℕ → ℕ) (f : T.R j) (g : GA D W) :
    castDict hV (T.phiJ j σ a f) g = (lieFac (T.Q.Dw j) (xiR D) a : ℂ) *
      (T.cE j σ (castDict hV (T.dict j σ) g).1 * castDict hV (T.mu j σ) g *
        rdU (T.U j σ) f (castDict hV (T.dict j σ) g).1 (castDict hV (T.dict j σ) g).2) := by
  subst hV
  rfl

theorem heckeTerm : ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.HeckePrimeDetection.HeckePointLaws → GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.SplitLinearModel D → GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.VacFixed D →
    ∀ (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m)
    (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A)
    (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec),
    R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsFam → R.IsModels → R.IsThP → TieIn T R κ v₀ →
    ∀ (i : Fin D.R.m) (σ : T.Q.c.F →+* ℂ), σ = T.σ₀ → ∀ hV : T.V ((i : ℕ) + 1) σ = Wc D i,
      GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.FramePin T R i σ hV →
    ∀ (P : Formalism.L2.DIV.Pl D.host.E) (p k : ℕ) (α : GA D (Wc D i)) (Rc : Finset (GA D (Wc D i))),
      GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.IsUnitaryHeckeOperatorSplitPrimeData T R i P p k α Rc →
    ∀ (h : GA D (Wc D i))
      (hx : (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).2 ∈ ((T.U ((i : ℕ) + 1) σ).X (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).1).dom),
      letI : Field (CAt σ) := inferInstanceAs (Field ℂ)
      haveI : IsAlgClosed (CAt σ) := inferInstanceAs (IsAlgClosed ℂ)
      ∃ e : hkKer (Xo := T.Q.Xo ((i : ℕ) + 1)) P.asIdeal p k (CAt σ)
          ((T.U ((i : ℕ) + 1) σ).un (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).1 ⟨(GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).2, hx⟩) ≃ Rc,
        ∀ C, (∃ z, hkRelFr P.asIdeal p k (GlobalTheory.ThetaTrace.hkTr (T.Q.Xo ((i : ℕ) + 1)) T.Q.c p) (CAt σ)
              ((T.U ((i : ℕ) + 1) σ).un (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).1 ⟨(GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).2, hx⟩) C z) ∧
          ∀ z, hkRelFr P.asIdeal p k (GlobalTheory.ThetaTrace.hkTr (T.Q.Xo ((i : ℕ) + 1)) T.Q.c p) (CAt σ)
              ((T.U ((i : ℕ) + 1) σ).un (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).1 ⟨(GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).2, hx⟩) C z →
          ∀ f ∈ sec (T.Q.Xo ((i : ℕ) + 1)) T.Q.c (wtA (κ i)) (κ i).n,
            (lieFac (T.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA (κ i)) : ℂ) *
              (T.cE ((i : ℕ) + 1) σ (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).1 * castDict hV (T.mu ((i : ℕ) + 1) σ) h) *
              σ (hkScal T.Q.c 1 P.asIdeal k D.R.nV) * toC (evR (T.Q.Xo ((i : ℕ) + 1)) T.Q.c f z) =
            (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.muAt T R i P)⁻¹ ^ k * GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.phiW T i σ hV (wtA (κ i)) f (h * (e C : GA D (Wc D i))) := by
  intro D hP hS hVF G _ _ Pl0 T0 A T _ R F κ v₀ hlev hgrp hfam hmod hthp ht i σ hσ hV hpin P p k α Rc hs h hx
  letI : Field (CAt σ) := inferInstanceAs (Field ℂ)
  haveI : IsAlgClosed (CAt σ) := inferInstanceAs (IsAlgClosed ℂ)
  obtain ⟨e, he⟩ := GlobalTheory.T.heckeKernel_complex_point_matches_cosets D hP hS hVF G Pl0 T0 A T R F κ v₀ hlev hgrp hfam hmod hthp ht i σ hσ hV hpin P p k α Rc hs h hx
  refine ⟨e, fun C => ⟨?_, fun z hz f hf => ?_⟩⟩
  · have hsp := splitSup T.Q.H hs.1.1
    have hHP : GlobalTheory.IndefiniteRowSideFullHecke.HeckePrimeDetection.IsHeckePrime T.Q.l P.asIdeal p :=
      GlobalTheory.IndefiniteRowSideFullHecke.HeckePrimeDetection.isHeckePrime_iff.2 ⟨P.isMaximal, hsp, hs.2.1, hs.2.2.1, hs.2.2.2.1⟩
    have hT := hP.2.1 _ _ _ _ (T.Q.Xo ((i : ℕ) + 1)) T.Q.c P.asIdeal p k hHP
    exact @hT (CAt σ) _ (inferInstanceAs (IsAlgClosed ℂ)) _ _ C
  · obtain ⟨hx', t, ht1, hB⟩ := he C z hz
    have hg := GlobalTheory.T.heckeTerm_generator_constant_via_frame D hP hS hVF G Pl0 T0 A T R F κ v₀ hlev hgrp hfam hmod hthp ht i σ hσ hV hpin P p k α Rc hs h hx
      _ (e C).2 C z hz hx' t ht1 hB
    have hw := GlobalTheory.FrameEval.evR_frBor _ _ _ _ _ _ (CAt σ) _ _ f hf t _ z hB
    have hwc : wchar (ex (T.Q.Dw ((i : ℕ) + 1)) (wtA (κ i)) (κ i).n) t = (t none : CAt σ) ^ (κ i).n := by
      unfold wchar
      rw [Finset.prod_eq_single none (fun j _ hj => by rw [ht1 j hj]; simp) (fun h0 => absurd (Finset.mem_univ _) h0)]
      rfl
    rw [hwc] at hw
    show _ = _ * castDict hV (T.phiJ ((i : ℕ) + 1) σ (wtA (κ i)) f) (h * (e C : GA D (Wc D i)))
    rw [phiW_unfold]
    have hr : rdU (T.U ((i : ℕ) + 1) σ) f (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV (h * (e C : GA D (Wc D i)))).1
        (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV (h * (e C : GA D (Wc D i)))).2 =
        toC (evR (T.Q.Xo ((i : ℕ) + 1)) T.Q.c f ((T.U ((i : ℕ) + 1) σ).un _ ⟨_, hx'⟩)) := dif_pos hx'
    rw [hr, hw]
    have hz' : toC ((t none : CAt σ) ^ (κ i).n * evR (T.Q.Xo ((i : ℕ) + 1)) T.Q.c f ((T.U ((i : ℕ) + 1) σ).un _ ⟨_, hx'⟩)) =
        toC (t none : CAt σ) ^ (κ i).n * toC (evR (T.Q.Xo ((i : ℕ) + 1)) T.Q.c f ((T.U ((i : ℕ) + 1) σ).un _ ⟨_, hx'⟩)) := rfl
    rw [hz']
    linear_combination ((lieFac (T.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA (κ i)) : ℂ) *
      toC (evR (T.Q.Xo ((i : ℕ) + 1)) T.Q.c f ((T.U ((i : ℕ) + 1) σ).un _ ⟨_, hx'⟩))) * hg

end GlobalTheory.HeckeTerm
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_cosetFockVacuumDatum : DatumEx := by
  first | exact @GlobalTheory.CoreOnto.datumEx | exact GlobalTheory.CoreOnto.datumEx | (intros; apply GlobalTheory.CoreOnto.datumEx <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
open GlobalTheory.FinPlLoc (idem mem_idOff_iff idem_mul_self)
open GlobalTheory.AscFinWit (mem_latO_at idem_mem_latO mxAt_mul mxAt_mul')

noncomputable section

namespace GlobalTheory.AscFin.StdOff

theorem latO_le_negSp {D : D7} (S T : HSp D) (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E))
    (P : HeightOneSpectrum (𝓞 D.host.F) → Prop) : latO S T LS LT P ≤ latO (negSp S) T LS LT P := by
  unfold latO
  rw [AddSubgroup.closure_le]
  rintro w ⟨α, hα, hP, a, ha, s, hs, t, ht, rfl⟩
  rw [← neg_neg (Matrix.of _)]
  refine neg_mem (AddSubgroup.subset_closure ⟨α, hα, hP, a, ha, s, hs, t, ht, ?_⟩)
  funext i j
  simp [negSp_gram, Finset.sum_neg_distrib, TensorProduct.tmul_neg]

theorem latO_negSp_le' {D : D7} (S T : HSp D) (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E))
    (P : HeightOneSpectrum (𝓞 D.host.F) → Prop) : latO (negSp S) T LS LT P ≤ latO S T LS LT P := by
  unfold latO
  rw [AddSubgroup.closure_le]
  rintro w ⟨α, hα, hP, a, ha, s, hs, t, ht, rfl⟩
  rw [← neg_neg (Matrix.of _)]
  refine neg_mem (AddSubgroup.subset_closure ⟨α, hα, hP, a, ha, s, hs, t, ht, ?_⟩)
  funext i j
  simp [negSp_gram, Finset.sum_neg_distrib, TensorProduct.tmul_neg]

theorem depLat_iff_at {D : D7} {S T : HSp D} {LS : GlobalTheory.FinPl.Lat S} {LT : GlobalTheory.FinPl.Lat T}
    {v : GlobalTheory.FinPl.Pl D} {W0 : Finset (Formalism.L2.DIV.Pl D.host.E)} (hoff : ∀ PP ∈ W0, (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) ≠ v)
    (H : AddSubgroup (WO S T)) {u : WO S T} (hu : MxAt (· = v) u) :
    (u ∈ latO (negSp S) T (LS : Set _) (LT : Set _) (fun _ => True) ∧ ∀ e : AE D, IsIdemSum e W0 → e • u ∈ H) ↔
      u ∈ latO S T (LS : Set _) (LT : Set _) (· = v) := by
  constructor
  · rintro ⟨h1, -⟩
    exact latO_negSp_le' S T _ _ _ ((mem_latO_at (S := negSp S) hu).1 h1)
  · intro h1
    refine ⟨(mem_latO_at (S := negSp S) hu).2 (latO_le_negSp S T _ _ _ h1), fun e he => ?_⟩
    have : e • u = 0 := Matrix.ext fun i j => (GlobalTheory.FinZeta.VacOff.idemSum_mul_off he hoff h1 i j).1
    rw [this]
    exact zero_mem _

theorem pair_tmul_scale {D : D7} (α' : Af D.host.F) (d : D.host.F) (X : D.host.E) :
    pairA D.host.F 0 (α' * algebraMap D.host.F (Af D.host.F) d) ⊗ₜ[D.host.F] X =
      pairA D.host.F 0 α' ⊗ₜ[D.host.F] ((d : D.host.E) * X) := by
  have e : (d : D.host.E) * X = d • X := rfl
  have e2 : pairA D.host.F 0 (α' * algebraMap D.host.F (Af D.host.F) d) = d • pairA D.host.F 0 α' := by
    refine Prod.ext ?_ ?_
    · show (0 : Ainf D.host.F) = d • (0 : Ainf D.host.F)
      rw [smul_zero]
    · show α' * algebraMap D.host.F (Af D.host.F) d = d • α'
      rw [Algebra.smul_def, mul_comm]
  rw [e, e2, ← TensorProduct.smul_tmul']
  exact ((TensorProduct.mk D.host.F (AF D.host.F) D.host.E (pairA D.host.F 0 α')).map_smul d X).symm

def gen {D : D7} (S U : HSp D) (α : Af D.host.F) (a : D.host.E) (s : Fin S.rank → D.host.E) (t : Fin U.rank → D.host.E) :
    WO S U :=
  Matrix.of fun i j => pairA D.host.F 0 α ⊗ₜ[D.host.F] (a * t i * ∑ k, star (s k) * S.gram k j)

theorem gen_zero {D : D7} (S U : HSp D) (α : Af D.host.F) (a : D.host.E) (s : Fin S.rank → D.host.E) :
    gen S U α a s 0 = 0 := by
  ext i j
  rw [gen, Matrix.of_apply, Matrix.zero_apply, Pi.zero_apply, mul_zero, zero_mul, TensorProduct.tmul_zero]

theorem gen_add {D : D7} (S U : HSp D) (α : Af D.host.F) (a : D.host.E) (s : Fin S.rank → D.host.E)
    (t t' : Fin U.rank → D.host.E) : gen S U α a s (t + t') = gen S U α a s t + gen S U α a s t' := by
  ext i j
  rw [Matrix.add_apply, gen, gen, gen, Matrix.of_apply, Matrix.of_apply, Matrix.of_apply, Pi.add_apply, mul_add, add_mul,
    TensorProduct.tmul_add]

theorem gen_smul {D : D7} (S U : HSp D) (α : Af D.host.F) (a : D.host.E) (s : Fin S.rank → D.host.E)
    (c : 𝓞 D.host.E) (t : Fin U.rank → D.host.E) : gen S U α a s (c • t) = gen S U α (a * (c : D.host.E)) s t := by
  ext i j
  have hc : c • t i = (c : D.host.E) * t i := Algebra.smul_def c (t i)
  rw [gen, gen, Matrix.of_apply, Matrix.of_apply, Pi.smul_apply, hc, ← mul_assoc]

theorem gen_smulE {D : D7} (S U : HSp D) (α : Af D.host.F) (a b : D.host.E) (s : Fin S.rank → D.host.E)
    (t : Fin U.rank → D.host.E) : gen S U α a s (b • t) = gen S U α (a * b) s t := by
  ext i j
  rw [gen, gen, Matrix.of_apply, Matrix.of_apply, Pi.smul_apply, smul_eq_mul, ← mul_assoc]

theorem gen_scale {D : D7} (S U : HSp D) (α : Af D.host.F) (d : D.host.F) (a b : D.host.E) (s : Fin S.rank → D.host.E)
    (t : Fin U.rank → D.host.E) :
    gen S U (α * algebraMap D.host.F (Af D.host.F) d) a s (b • t) = gen S U α (a * ((d : D.host.E) * b)) s t := by
  ext i j
  rw [gen, gen, Matrix.of_apply, Matrix.of_apply, pair_tmul_scale, Pi.smul_apply, smul_eq_mul]
  congr 1
  ring

theorem latO_idLat_at {D : D7} (S U : HSp D) (LS : Set (Fin S.rank → D.host.E)) (LU : GlobalTheory.FinPl.Lat U)
    (I : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) (v : GlobalTheory.FinPl.Pl D) (d : D.host.F) (hdI : (d : D.host.E) ∈ I)
    (hdI' : ∀ x ∈ I, ∃ y : 𝓞 D.host.E, (y : D.host.E) = (d : D.host.E) * x)
    (hsc : ∀ α ∈ intAf D.host.F, (∀ w, ¬ w = v → evalV D.host.F w α = 0) →
      ∃ α' ∈ intAf D.host.F, (∀ w, ¬ w = v → evalV D.host.F w α' = 0) ∧ α = α' * algebraMap D.host.F (Af D.host.F) d) :
    latO S U LS (idLat I LU : Set _) (· = v) = latO S U LS (LU : Set _) (· = v) := by
  have hAA : ∀ a ∈ D.host.AA, ∀ c : 𝓞 D.host.E, a * (c : D.host.E) ∈ D.host.AA := fun a ha c => by
    have := Submodule.smul_mem (D.host.AA : Submodule (𝓞 D.host.E) D.host.E) c ha
    rwa [Algebra.smul_def, mul_comm] at this
  have hgen : ∀ α ∈ intAf D.host.F, (∀ w, ¬ w = v → evalV D.host.F w α = 0) → ∀ a ∈ D.host.AA, ∀ s ∈ LS, ∀ t ∈ LU,
      gen S U α a s t ∈ latO S U LS (LU : Set _) (· = v) := fun α hα hP a ha s hs t ht =>
    AddSubgroup.subset_closure ⟨α, hα, hP, a, ha, s, hs, t, ht, rfl⟩
  refine le_antisymm ((AddSubgroup.closure_le _).2 ?_) ((AddSubgroup.closure_le _).2 ?_)
  · rintro w ⟨α, hα, hP, a, ha, s, hs, t, ht, rfl⟩
    obtain ⟨α', hα', hP', rfl⟩ := hsc α hα hP
    show gen S U (α' * algebraMap D.host.F (Af D.host.F) d) a s t ∈ (latO S U LS (LU : Set _) (· = v) : Set (WO S U))
    rw [SetLike.mem_coe]
    induction ht using Submodule.span_induction generalizing a with
    | mem z hz =>
      obtain ⟨s', hs', y, hy, rfl⟩ := hz
      obtain ⟨yy, hyy⟩ := hdI' s' hs'
      rw [gen_scale, ← hyy]
      exact hgen α' hα' hP' _ (hAA a ha yy) s hs y hy
    | zero =>
      rw [gen_zero]
      exact zero_mem _
    | add x y _ _ hx hy =>
      rw [gen_add]
      exact add_mem (hx a ha) (hy a ha)
    | smul c x _ hx =>
      rw [gen_smul]
      exact hx _ (hAA a ha c)
  · rintro w ⟨α, hα, hP, a, ha, s, hs, t, ht, rfl⟩
    obtain ⟨α', hα', hP', rfl⟩ := hsc α hα hP
    show gen S U (α' * algebraMap D.host.F (Af D.host.F) d) a s t ∈ (latO S U LS (idLat I LU : Set _) (· = v) : Set (WO S U))
    have e := gen_scale S U α' d a 1 s t
    rw [one_smul, mul_one, mul_comm a] at e
    rw [SetLike.mem_coe, e, mul_comm (d : D.host.E) a, ← gen_smulE]
    exact AddSubgroup.subset_closure ⟨α', hα', hP', a, ha, s, hs, _, Submodule.subset_span ⟨_, hdI, t, ht, rfl⟩, rfl⟩

theorem latO_shiftId {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (v : GlobalTheory.FinPl.Pl D)
    (hv : v ∉ G.pl.S0) (S U : HSp D) (LS : Set (Fin S.rank → D.host.E)) (LU : GlobalTheory.FinPl.Lat U) :
    latO S U LS (idLat (shiftId G) LU : Set _) (· = v) = latO S U LS (LU : Set _) (· = v) := by
  obtain ⟨d, hdv, hdI, hdI'⟩ := GlobalTheory.T.exists_unit_mem_modulusDivConjugateIdeal G v hv
  exact latO_idLat_at S U LS LU _ v (d : D.host.F) hdI hdI' (GlobalTheory.T.integralFiniteAdele_supported_div_prime_to_place D v d hdv)

end GlobalTheory.AscFin.StdOff

open GlobalTheory.AscFin.StdOff GlobalTheory.FinZeta.VacOff

theorem GlobalTheory.AscFin.stdAt_pcBF : OnStd fun {D} _ _ {sc} {G} W F => ∀ ρ (h : 2 * ρ + 2 ≤ D.R.m), ∀ v ∉ G.pl.S0,
    StdAt (F.dB ρ h) (F.dJ ρ h) (pcBF W F ρ h) (G.Λ (.grid (2 * ρ + 2) 0)) (G.Λ (.grid (2 * ρ + 1) 0)) v := by
  classical
  intro D _ T L _ _ sc G W _ _ F _ ρ h v hv
  have hoff : ∀ PP ∈ G.pl.W0, (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) ≠ v := fun PP hPP e => by
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.1 hPP
    exact hv (by rw [← e, G.pl.under_w hu]; exact hu)
  refine ⟨fun a ha => ?_, fun a ha => ?_, fun ξ hξ => ?_⟩
  · have hu := mxAt_mul' ha (F.dB ρ h).pX
    exact depLat_iff_at hoff _ hu
  · refine ⟨idem D (· = v) • a, fun i j => (mem_idOff_iff _ _).2 (by
      rw [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, mul_sub, ← mul_assoc, idem_mul_self, sub_self]), ?_⟩
    rw [HypDec.extX_apply, Matrix.smul_mul]
    exact idem_mem_latO (latO_negSp_le' _ _ _ _ _ ha.1)
  · have hu := mxAt_mul' (mxAt_mul (F.dJ ρ h).jX hξ) (F.dB ρ h).p0
    show (F.dB ρ h).ext0 _ ((F.dJ ρ h).incX _ ξ) ∈ latBig G (2 * ρ + 1) ↔ _
    exact (mem_latO_at hu).trans (by rw [latO_shiftId G v hv]; exact Iff.rfl)

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

theorem _root_.GlobalTheory.T.depthLatticeGridRow_zero_le_selfDualHomLattice : All fun {D} _ _ _ {G} _ _ => 0 < D.R.m → latRow G 0 ≤ latBig G 0 := by
  first | exact @GlobalTheory.RowBig.latRow_zero_le_latBig | exact GlobalTheory.RowBig.latRow_zero_le_latBig | (intros; apply GlobalTheory.RowBig.latRow_zero_le_latBig <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.unfolded_integrand_biInvariant_large_depth : Big fun ch => InvAt ch := by
  first | exact @GlobalTheory.RowInv.main | exact GlobalTheory.RowInv.main | (intros; apply GlobalTheory.RowInv.main <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.cell_masses_against_level_volumes_large_depth : Big fun ch => ∀ s, WtAt ch s := by
  first | exact @GlobalTheory.RowWt.wtAt_big | exact GlobalTheory.RowWt.wtAt_big | (intros; apply GlobalTheory.RowWt.wtAt_big <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.unfolded_vacua_real_up_to_twist_large_depth : Big fun ch => VacAt ch := by
  first | exact @GlobalTheory.RowVal.OneVac.big_vacAt | exact GlobalTheory.RowVal.OneVac.big_vacAt | (intros; apply GlobalTheory.RowVal.OneVac.big_vacAt <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.flat_dictionary_relative_base_vacua_large_depth : Big fun ch => ∀ s, PlaceAt ch s → ConLin ch → LocAt ch s := by
  first | exact @GlobalTheory.LocAsm.locAt_of_placeAt | exact GlobalTheory.LocAsm.locAt_of_placeAt | (intros; apply GlobalTheory.LocAsm.locAt_of_placeAt <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.tiltedPoints_covered_by_representativeCells : Big fun ch => ∀ s, CoverAt ch s := by
  first | exact @GlobalTheory.RowVal.cover_at | exact GlobalTheory.RowVal.cover_at | (intros; apply GlobalTheory.RowVal.cover_at <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc

theorem _root_.GlobalTheory.T.integral_strip_eq_zero_of_real_modulation_vanishing : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V V₀ W : HSp D) (ρ : ℕ) (Y : Type) [TopologicalSpace Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (a : Gen ψ V V₀ W ρ Y), a.Is → ∀ (G : GA D W → ℂ), RapidDec W G → ∀ Φ : WO V W → ℂ, IsThetaFunO ψ V W Φ → (∀ c : Mx D W.rank ρ, c.map (finPart D) = 0 → a.lhs G (heisO ψ V W (a.d.extY W c) Φ) = 0) → ∀ 𝓑 : Set (GA D W), IsFundamentalDomain (GQ W ⊓ Rgrp W (rat a.x₀) : Subgroup (GA D W)) 𝓑 a.vW.μ → ∀ C : Set (GA D W), IsCompact C → C ⊆ GinfC W → ∫ h in 𝓑 ∩ strip W (Rgrp W (rat a.x₀)) C, a.ker G Φ h ∂a.vW.μ = 0 := by
  first | exact @GlobalTheory.StripVanish.integral_strip_eq_zero | exact GlobalTheory.StripVanish.integral_strip_eq_zero | (intros; apply GlobalTheory.StripVanish.integral_strip_eq_zero <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.RowVertexInv GlobalTheory.SplitFlip
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

theorem _root_.GlobalTheory.T.vacuum_scalars_eq_product_edge_factors_row : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) {μ₀ : T}, L.Is μ₀ → ∀ {t : T}, t ∈ U → ∀ (j : ℕ) (hj : j + 1 < D.R.m) (k : FinPt G (.grid (j + 1) D.R.m)),
    finG (G.V (.grid (j + 1) D.R.m)) k ∈ S.levRow t (j + 1) hj.le → ∀ (c₁ c₂ : ℂ),
    W.om (.chi j D.R.m) (G.toPair (.chi j D.R.m) 1 (moved S j k)) (S.Z.vac (.chi j D.R.m)) = c₁ • S.Z.vac (.chi j D.R.m) →
    W.om (.chi (j + 1) D.R.m) (G.toPair (.chi (j + 1) D.R.m) (moved S j k) 1) (S.Z.vac (.chi (j + 1) D.R.m)) =
      c₂ • S.Z.vac (.chi (j + 1) D.R.m) →
    c₁ * c₂ = ∏ w : locPl G t, ((oppositePath D.R.m).map ((locGrid G t w.1).edgeFactor .one (Pi.mulSingle (j + 1, D.R.m)
      (inBasis (rank_vertex G t w.1 (X := (j + 1, D.R.m)) ⟨hj.le, le_rfl⟩) (S.B.β (j + 1) D.R.m) w.1
        (finG (G.V (.grid (j + 1) D.R.m)) k))))).prod := by
  first | exact @GlobalTheory.RowVacScalar.scalars_eq_edgeFactors | exact GlobalTheory.RowVacScalar.scalars_eq_edgeFactors | (intros; apply GlobalTheory.RowVacScalar.scalars_eq_edgeFactors <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
open GlobalTheory.CharXFB

noncomputable section
namespace GlobalTheory.CharXFB.HeisenbergPairBadPlaces

theorem traceCharacter_trivial_heisenbergPair_at_badPlaces : All fun {D} _ _ {sc} {G} W _ => ∀ σ (h : 2 * (σ + 1) + 2 ≤ D.R.m) (h' : 2 * σ + 2 ≤ D.R.m) (u : WO (G.V (.grid (2 * σ + 2 + 1) 0)) (G.V (.grid (2 * σ + 2) 0))), u ∈ latRow G (2 * σ + 2) → ∀ (p : Fin (σ + 1)) (v : GlobalTheory.FinPl.Pl D), v ∈ G.pl.S0 → psiE W.ψ (GlobalTheory.FinPlLoc.idem D (· = v) * (incA D D.host.xi0 * hA _ (ratV fun k => (G.colDec (2 * σ + 2) (by omega) h').a k (Fin.castLE (by omega) p)) (u *ᵥ ratV fun k => (G.colDec (2 * (σ + 1) + 1) (by omega) (by omega)).a k (Fin.castLE (by omega) p : Fin (2 * (σ + 1) + 1 - 1)).rev))) = 1 := by
  intro D hQ T L μ0 hL sc G W M hM σ h h' u hu p v hv
  have hb := GlobalTheory.T.lattice_scaling_at_S0 D hQ T L μ0 hL sc G W M hM (2 * σ + 2) (by omega) u hu v hv
  have hC := GlobalTheory.T.thetaGrid_pairingBound_mem_completion_of_mapBound G σ h h' u v hb p
  generalize hA _ _ _ = x at hC ⊢
  obtain ⟨-, -, h3, -, h5, -⟩ := GlobalTheory.SeeSaw.idV_props D W.ψ W.ψ_std v
  have hε : GlobalTheory.FinPlLoc.idem D (· = v) ∈ idAt D (· = v) := GlobalTheory.FinPlLoc.idem_mem_idAt _
  have hs : GlobalTheory.FinPlLoc.idem D (· = v) * (incA D D.host.xi0 * x) ∈ idAt D (· = v) := Ideal.mul_mem_right _ _ hε
  have hx0 : D.host.xi0 ≠ 0 := cmHost_imaginaryGenerator_ne_zero
  have hdI : GlobalTheory.FinPlLoc.idem D (· = v) * (incA D D.host.xi0 * x) ∈ GlobalTheory.SeeSaw.idV (GlobalTheory.SeeSaw.dI D) v := by
    have e : GlobalTheory.SeeSaw.dI D = FractionalIdeal.spanSingleton _ D.host.xi0 * (D.host.AA * D.host.AAbar) := by
      unfold GlobalTheory.SeeSaw.dI; rw [mul_assoc]
    rw [e, h3 _ _ hx0]
    refine ⟨?_, hs⟩
    have e1 : incA D D.host.xi0⁻¹ * incA D D.host.xi0 = 1 := by rw [← map_mul, inv_mul_cancel₀ hx0, map_one]
    convert hC using 1
    linear_combination (GlobalTheory.FinPlLoc.idem D (· = v) * x) * e1
  have h6 := (h5 _ hs).1 hdI _ (GlobalTheory.FinPlLoc.idem_mem_intAt _)
  have e2 : GlobalTheory.FinPlLoc.idem D (· = v) * (incA D D.host.xi0 * x) * GlobalTheory.FinPlLoc.idem D (· = v) =
      GlobalTheory.FinPlLoc.idem D (· = v) * (incA D D.host.xi0 * x) := by
    rw [mul_comm, ← mul_assoc, GlobalTheory.FinPlLoc.idem_mul_self]
  rwa [e2] at h6

end GlobalTheory.CharXFB.HeisenbergPairBadPlaces
end
end
