module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle251
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle264
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.LevelStructureProperties
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SelfDualLatticesAtLevel
import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNsmulIntMemLatO
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle305
public import Formalism.SharpRestriction.CuspSpanNormBounds.BesselShellMomentBounds
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelCharacterEmbeddingCompat
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle266
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemHatLConjIIffHform
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle267
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle048
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle013
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle271
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
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.Bundle002
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsSystem
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle236
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle247
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open GlobalTheory.AdSpan.ReVec
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.frameAdjointMap_reframedHermitianSpace : ∀ (D : D7) (S T : HSp D) (b : Module.Basis (Fin S.rank) D.host.E S.V) (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)) (x : WO (reS S b) T), frMapAdj (reS S b) T (frPinvGL S b * βS) βT x = frMapAdj S T βS βT (reW S T b x) := by
  first | exact @GlobalTheory.AdSpan.ReVec.FrMap.frMapAdj_reS | exact GlobalTheory.AdSpan.ReVec.FrMap.frMapAdj_reS | (intros; apply GlobalTheory.AdSpan.ReVec.FrMap.frMapAdj_reS <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open GlobalTheory.AdSpan.ReVec
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.isFrame_frameChangeInverseGL_mul : ∀ (D : D7) (S : HSp D) (b : Module.Basis (Fin S.rank) D.host.E S.V) (βS : GL (Fin S.rank) (Lev.EAf D)) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)), StdFrame.OrthFrame (reS S b) → (ΛS : Set (Fin S.rank → D.host.E)) = L0c D S → Formalism.L2.DIV.IsFrame βS ΛS → Formalism.L2.DIV.IsFrame (frPinvGL S b * βS) (stdL D.host.E (reS S b).rank) := by
  first | exact @GlobalTheory.AdSpan.ReVec.isFrame_frPinvGL_mul | exact GlobalTheory.AdSpan.ReVec.isFrame_frPinvGL_mul | (intros; apply GlobalTheory.AdSpan.ReVec.isFrame_frPinvGL_mul <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LiftDat

open GlobalTheory.LiftLevel

variable {D : D7}

def rowAdj (T : HSp D) (βT : GL (Fin T.rank) (EAf D)) (a e : AE D) (v : Fin T.rank → D.host.E) :
    Matrix (Fin 1) (Fin T.rank) (EAf D) :=
  toEAf D a • HMul.hMul ((Matrix.of fun (_ : Fin 1) (l : Fin T.rank) =>
      ∑ k, cA D (cA D e * (pairA D.host.F 0 1) ⊗ₜ[D.host.F] v k) * incA D (T.gram k l)).map (toEAf D)) βT.val

def rowRed (T : HSp D) (βT : GL (Fin T.rank) (EAf D)) (a e : AE D) (PP : Formalism.L2.DIV.Pl D.host.E)
    (v : Fin T.rank → D.host.E) : Fin T.rank → Formalism.L2.DIV.kP PP :=
  fun j => redM PP (rowAdj T βT a e v) 0 j

theorem liftI_le {Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)} {PP : Formalism.L2.DIV.Pl D.host.E} (h : PP ∈ Pg ∪ Q) :
    liftI Pg Q ≤ conjI PP.asIdeal :=
  Ideal.prod_le_inf.trans (Finset.inf_le h)

def toConj (Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (PP : Formalism.L2.DIV.Pl D.host.E) (h : PP ∈ Pg ∪ Q) :
    𝓞 D.host.E ⧸ liftI Pg Q →+* 𝓞 D.host.E ⧸ conjI PP.asIdeal :=
  Ideal.quotientMap (conjI PP.asIdeal) (RingHom.id _) (fun _ hx => liftI_le h hx)

def conjRes (Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (PP : Formalism.L2.DIV.Pl D.host.E) (h : PP ∈ Pg ∪ Q) :
    𝓞 D.host.E ⧸ liftI Pg Q →+* Formalism.L2.DIV.kP PP :=
  Ideal.quotientMap PP.asIdeal GlobalTheory.SW.Lev.bar (fun _ hx => GlobalTheory.SW.Lev.mem_conjI.1 (liftI_le h hx))

def Jgrp (Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (r : ℕ) : Subgroup (GL (Fin r) (𝓞 D.host.E ⧸ liftI Pg Q)) :=
  ⨅ PP : Pg, (Matrix.GeneralLinearGroup.map (toConj Pg Q PP.1 (Finset.mem_union_left _ PP.2))).ker

def lamHom (Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (r : ℕ)
    (ξ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ) : Jgrp Pg Q r →* ℂˣ :=
  (∏ PP ∈ Q.attach, (ξ PP.1).comp ((Units.map (conjRes Pg Q PP.1 (Finset.mem_union_right _ PP.2)).toMonoidHom).comp
    (Matrix.GeneralLinearGroup.det.comp (Jgrp Pg Q r).subtype)))⁻¹

theorem mem_Jgrp {Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)} {r : ℕ} {κ : GL (Fin r) (𝓞 D.host.E ⧸ liftI Pg Q)} :
    κ ∈ Jgrp Pg Q r ↔ ∀ PP (h : PP ∈ Pg),
      Matrix.GeneralLinearGroup.map (toConj Pg Q PP (Finset.mem_union_left _ h)) κ = 1 := by
  simp [Jgrp, Subgroup.mem_iInf, MonoidHom.mem_ker]

theorem lamHom_apply {Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)} {r : ℕ}
    (ξ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ) (κ : Jgrp Pg Q r) :
    lamHom Pg Q r ξ κ = (∏ PP ∈ Q.attach, ξ PP.1 (Units.map (conjRes Pg Q PP.1
      (Finset.mem_union_right _ PP.2)).toMonoidHom (Matrix.GeneralLinearGroup.det (κ : GL (Fin r) _))))⁻¹ := by
  simp [lamHom]

def mkLevel {S T : HSp D} (C : Ctx S T) (Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E))
    (ξ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ) (h1 : liftI Pg Q ≠ ⊤) (h2 : liftI Pg Q ≠ ⊥)
    (h3 : IsCoprime (liftI Pg Q) (conjI (liftI Pg Q))) (h4 : IsCoprime (liftI Pg Q) (Ideal.span {2}))
    (β : Fin T.rank → Fin T.rank → D.host.E) (hβ : ∀ i, β i ∈ C.X.Λ)
    (hsp : C.X.Λ ≤ Submodule.span (𝓞 D.host.E) (Set.range β) ⊔ liftI Pg Q • C.X.Λ)
    (Lv0 : GlobalTheory.SW.Level C.X) : GlobalTheory.SW.Level C.X where
  𝔪 := liftI Pg Q
  proper := h1
  ne_bot := h2
  cop := h3
  odd := h4
  β := β
  β_mem := hβ
  β_span := hsp
  J := Jgrp Pg Q T.rank
  lam := lamHom Pg Q T.rank ξ
  w := Lv0.w
  w_int := Lv0.w_int
  w_tr := Lv0.w_tr

end GlobalTheory.LiftDat

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TrOffShift

theorem algebraMap_mem_conjI {D : D7} (I : Ideal (𝓞 D.host.E)) (s : 𝓞 D.host.F)
    (h : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) s ∈ I) :
    algebraMap (𝓞 D.host.F) (𝓞 D.host.E) s ∈ conjI I := by
  apply Ideal.subset_span
  refine ⟨_, h, ?_⟩
  have h2 := GlobalTheory.Ker.MovLev.bar_algebraMap (D := D) s
  have h3 := congrArg (fun x : 𝓞 D.host.E => (x : D.host.E)) h2
  simp only [Lev.bar] at h3
  have h4 := IsCMField.coe_ringOfIntegersComplexConj D.host.E (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) s)
  exact h3.symm.trans h4

theorem shift_mult : ∀ (D : D7) (r : ℕ) (Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (L : Lt D.host.E r) (w : HeightOneSpectrum (𝓞 D.host.F)), (∀ PP ∈ Pg ∪ Q, HeightOneSpectrum.under (𝓞 D.host.F) PP ≠ w) → ∀ u ∈ idq (GlobalTheory.LiftLevel.liftI Pg Q) (conjI (GlobalTheory.LiftLevel.liftI Pg Q)) L, ∃ t : 𝓞 D.host.F, t ∉ w.asIdeal ∧ algebraMap (𝓞 D.host.F) (𝓞 D.host.E) t • u ∈ L := by
  intro D r Pg Q L w hne u hu
  classical
  have hex : ∀ PP ∈ Pg ∪ Q, ∃ s : 𝓞 D.host.F,
      algebraMap (𝓞 D.host.F) (𝓞 D.host.E) s ∈ PP.asIdeal ∧ s ∉ w.asIdeal := by
    intro PP hPP
    by_contra hcon
    push_neg at hcon
    apply hne PP hPP
    have hle : (HeightOneSpectrum.under (𝓞 D.host.F) PP).asIdeal ≤ w.asIdeal := by
      intro s hs
      exact hcon s hs
    exact HeightOneSpectrum.ext
      ((HeightOneSpectrum.isMaximal _).eq_of_le w.isPrime.ne_top hle)
  choose! tf htf1 htf2 using hex
  refine ⟨∏ PP ∈ Pg ∪ Q, tf PP, ?_, ?_⟩
  · have : ∏ PP ∈ Pg ∪ Q, tf PP ∈ w.asIdeal.primeCompl :=
      Submonoid.prod_mem _ (fun c hc => htf2 c hc)
    exact this
  · have hmem : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) (∏ PP ∈ Pg ∪ Q, tf PP)
        ∈ GlobalTheory.LiftLevel.liftI Pg Q := by
      rw [map_prod]
      exact Ideal.prod_mem_prod (fun PP hPP => algebraMap_mem_conjI (D := D) _ _ (htf1 PP hPP))
    have h1 := hu _ (algebraMap_mem_conjI (D := D) _ _ hmem)
    exact Submodule.smul_le_right h1

end GlobalTheory.TrOffShift
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.LiftLevel

noncomputable section
namespace GlobalTheory.AdjScalar
variable {D : D7}

theorem cA_cA (z : AE D) : cA D (cA D z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => rw [RingHom.map_zero, RingHom.map_zero]
  | add x y hx hy => rw [RingHom.map_add (f := _), RingHom.map_add (f := _), hx, hy]
  | tmul a x =>
    change a ⊗ₜ[D.host.F] star (star x) = _
    rw [star_star]

theorem map_adj_smul {R K : Type} [CommRing R] [CommRing K] (f : R →+* K) (σ : R →+* R) {m n : ℕ}
    (G1 : Matrix (Fin m) (Fin m) R) (G2 : Matrix (Fin n) (Fin n) R) (P : Matrix (Fin m) (Fin m) K)
    (Q : Matrix (Fin n) (Fin n) K) (X : Matrix (Fin n) (Fin m) R) (a : R) :
    P * ((G1 * ((a • X).map σ)ᵀ * G2).map f) * Q = f (σ a) • (P * ((G1 * (X.map σ)ᵀ * G2).map f) * Q) := by
  have h1 : (a • X).map σ = σ a • X.map σ := by
    ext i j; simp [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul]
  have h2 : ∀ (M : Matrix (Fin m) (Fin n) R) (b : R), (b • M).map f = f b • M.map f := by
    intro M b; ext i j; simp [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul]
  rw [h1, Matrix.transpose_smul, Matrix.mul_smul, Matrix.smul_mul, h2, Matrix.mul_smul, Matrix.smul_mul]

theorem frMapAdj_smul (S T : HSp D) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D))
    (a : AE D) (x : WO S T) :
    frMapAdj S T βS βT (a • x) = toEAf D (cA D a) • frMapAdj S T βS βT x :=
  map_adj_smul (toEAf D) (cA D) _ _ _ _ x a

theorem cA_incA' (c : D.host.E) : cA D (incA D c) = incA D (star c) := rfl

theorem smul_absorb {K : Type} [CommRing K] {m n : ℕ} (B : Matrix (Fin m) (Fin m) K) (F : Matrix (Fin m) (Fin n) K)
    (u v : K) (hF : u • F = F) : (u * v) • (B * F) = (1 : K) • (B * (v • F)) := by
  rw [one_smul, Matrix.mul_smul, mul_comm, mul_smul, ← Matrix.mul_smul B u F, hF]

theorem adjA_half_smul (D : D7) (S T : HSp D) (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D))
    (e : AE D) (c : D.host.E) (x : WO S T) (h : IsHalf (cA D e) x) :
    adjA S T βS βT (e * incA D (star c)) x = adjA S T βS βT 1 (incA D c • x) := by
  have hx : cA D e • x = x := by
    ext i j; exact h i j
  have hF : toEAf D e • frMapAdj S T βS βT x = frMapAdj S T βS βT x := by
    conv_rhs => rw [← hx]
    rw [frMapAdj_smul, cA_cA]
  unfold adjA
  rw [frMapAdj_smul, cA_incA', map_one, map_mul]
  exact smul_absorb _ _ _ _ hF

end GlobalTheory.AdjScalar
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LiftLevel

theorem isLattice_stdL (E : Type) [Field E] [NumberField E] (n : ℕ) :
    Submodule.IsLattice E (stdL E n) := by
  refine ⟨Submodule.fg_span (Set.finite_range _), ?_⟩
  intro s hs hli
  exact (LinearIndependent.iff_fractionRing _ _).mp hli
theorem isFullLattice_stdL (E : Type) [Field E] [NumberField E] (n : ℕ) :
    Submodule.IsFullLattice E (stdL E n) := by
  letI := isLattice_stdL E n
  refine ⟨?_⟩
  rw [stdL, Submodule.span_span_of_tower, ← (Pi.basisFun E (Fin n)).span_eq]
  congr 2
  funext i
  exact (Pi.basisFun_apply E (Fin n) i).symm

theorem liftL_nsmul_mem_latO : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (hn : T.rank ≤ S.rank) (ΛT : Lt D.host.E T.rank), IsSelfDualC T ΛT → IsAA C.X.Λ ΛT → ∀ (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)), Formalism.L2.DIV.IsFrame βS (stdL D.host.E S.rank) → Formalism.L2.DIV.IsFrame βT ΛT → ∀ (Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (ξ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ), Pg.Nonempty → (∀ PP, PP ∈ Pg ∨ PP ∈ Q → (2 : 𝓞 D.host.E) ∉ PP.asIdeal) → ∀ e : AE D, IsIdemSum e (Pg ∪ Q) → ∃ m : ℕ, 0 < m ∧ ∀ x ∈ GlobalTheory.LiftLevel.liftL S T βS βT Pg Q e, m • x ∈ latO S T (stdL D.host.E S.rank : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True := by
  intro D S T C hn ΛT hΛT hAA βS βT hβS hβT Pg Q ξ hPg h2 e he
  obtain ⟨k₂, hk₂, h₂⟩ := GlobalTheory.PlaceVec.frMapAdj_down S T βS βT
  obtain ⟨k₄, hk₄, h₄⟩ := GlobalTheory.PlaceVec.exists_nsmul_int_mem_latO (S := S) (T := T)
    (ΛS := stdL D.host.E S.rank) (ΛT := ΛT) (isFullLattice_stdL D.host.E S.rank) (GlobalTheory.PlaceVec.selfDual_isFullLattice T ΛT hΛT)
  have hinf : infPart D (cA D e) = 0 := GlobalTheory.PlaceVec.infPart_cA (GlobalTheory.PlaceVec.idemSum_infPart he)
  refine ⟨k₄ * k₂, Nat.mul_pos hk₄ hk₂, fun x hx => ?_⟩
  obtain ⟨hhalf, hint, -⟩ := hx
  have hx0 : (k₂ • x).map (infPart D) = 0 := by
    ext i j
    show infPart D ((k₂ • x) i j) = 0
    rw [Matrix.smul_apply, ← hhalf i j, nsmul_eq_mul, RingHom.map_mul, RingHom.map_mul, hinf, zero_mul, mul_zero]
  rw [mul_smul]
  exact h₄ (k₂ • x) hx0 (by rw [GlobalTheory.PlaceVec.map_toEAf_nsmul]; exact h₂ x hint)

end GlobalTheory.LiftLevel
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.LiftLevel

namespace GlobalTheory.DualRed

theorem adjA_entry : ∀ (D : D7) (S T : HSp D), S.gram = 1 → ∀ (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)) (x : WO S T) (k : Fin S.rank) (j : Fin T.rank), adjA S T βS βT 1 x k j = Formalism.UG.hform (Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F)) (T.gram.map (Formalism.UG.inclE (F := D.host.F) (Formalism.L2.Herm.Af D.host.F))) (fun c => toEAf D (x c k)) (fun c => βT.1 c j) := by
  intro D S T hS βS βT x k j
  have hE : toEAf D = GlobalTheory.LevSplit.finSw D := rfl
  unfold adjA frMapAdj
  rw [hS, inv_one, Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mul, map_one, one_smul, ← Matrix.mul_assoc,
    ← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul, Matrix.map_mul]
  unfold Formalism.UG.hform
  simp only [Matrix.mul_apply, Matrix.map_apply, Matrix.transpose_apply, hE, GlobalTheory.LevSplit.finSw_cA,
    GlobalTheory.LevSplit.finSw_incA, Finset.sum_mul]
  rw [Finset.sum_comm]

theorem adj_int_iff : ∀ (D : D7) (S T : HSp D), S.gram = 1 → ∀ (ΛT : Lt D.host.E T.rank), IsSelfDualC T ΛT → ∀ (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)), Formalism.L2.DIV.IsFrame βT ΛT → ∀ (J : Ideal (𝓞 D.host.E)), Squarefree J → ∀ x : WO S T, IsFinPt x → ((IsIntM (adjA S T βS βT 1 x) ∧ ∀ PP : Formalism.L2.DIV.Pl D.host.E, J ≤ PP.asIdeal → redM PP (adjA S T βS βT 1 x) = 0) ↔ x ∈ hatA S T (tens (stdL D.host.E S.rank) (conjI J • ΛT))) := by
  intro D S T hS ΛT hsd βS βT hfr J hJ x hx
  have hJ0 : J ≠ ⊥ := by
    rw [← Submodule.zero_eq_bot]
    exact hJ.ne_zero
  rw [GlobalTheory.TensColRead.mem_hatA_stdL_iff D S T _ x hx]
  simp only [GlobalTheory.FrameIdeal.mem_hatL_conjI_iff_hform D T ΛT hsd βT hfr J hJ0, ← adjA_entry D S T hS βS βT x]
  unfold IsIntM redM
  constructor
  · rintro ⟨hint, hred⟩ k j
    refine ⟨⟨_, hint k j⟩, GlobalTheory.LiftLevel.mem_idS hJ fun PP hPP => ?_, rfl⟩
    have h0 := congrFun (congrFun (hred PP hPP) k) j
    simpa only [Matrix.zero_apply, Pi.zero_apply, dif_pos (hint k j)] using h0
  · intro h
    have hint : ∀ k j, adjA S T βS βT 1 x k j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
      intro k j
      obtain ⟨s, -, hs⟩ := h k j
      rw [← hs]
      exact s.2
    refine ⟨hint, fun PP hPP => ?_⟩
    funext k j
    obtain ⟨s, hsI, hs⟩ := h k j
    have hse : (⟨adjA S T βS βT 1 x k j, hint k j⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) = s := Subtype.ext hs.symm
    simp only [Matrix.zero_apply, Pi.zero_apply, dif_pos (hint k j), hse]
    exact GlobalTheory.LiftLevel.resS_eq_zero hPP hsI

end GlobalTheory.DualRed
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdSpan.ConjHol

theorem torProd_spec : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (B : C.Bas), C.IsB B → ∀ (s : D.what₂.Tau → Fin T.rank → ℝ), GlobalTheory.AdSpan.ConjHol.torProd C.θ T B s ∈ GinfC T ∧ ∀ ρ, compAt C.θ ρ (Formalism.L2.Theta.mt T (GlobalTheory.AdSpan.ConjHol.torProd C.θ T B s)) = B ρ * diagonal (fun c => cexp ((s ρ c : ℂ) * I)) * (B ρ)⁻¹ := by
  intro D S T C B hB s
  have R : GlobalTheory.SmoothForms.RealPoints C.θ T := (GlobalTheory.SmoothForms.RealPts.realPoints D).2 C.θ C.inf T
  have hu : ∀ ρ, IsAtTau C.θ T ρ (B ρ * diagonal (fun c => cexp ((s ρ c : ℂ) * I)) * (B ρ)⁻¹) (torAt C.θ T B ρ (s ρ)) := by
    intro ρ
    have hS : (diagonal fun c => cexp ((s ρ c : ℂ) * I))ᴴ * sgnM C.X * (diagonal fun c => cexp ((s ρ c : ℂ) * I)) = sgnM C.X := by
      unfold sgnM
      exact GlobalTheory.HolRead.AdExt.diag_unitary _ _
    exact GlobalTheory.HolRead.AdExt.atTau_spec R ρ (GlobalTheory.HolRead.AdExt.conj_mem_unitary (isUnit_det_B C hB ρ) (hB ρ) hS)
  suffices H : ∀ l : List D.what₂.Tau, l.Nodup → (l.map fun ρ => torAt C.θ T B ρ (s ρ)).prod ∈ GinfC T ∧
      ∀ ρ, infMat D.sp.cm.sig T.gram (C.θ ρ) (l.map fun ρ => torAt C.θ T B ρ (s ρ)).prod =
        if ρ ∈ l then B ρ * diagonal (fun c => cexp ((s ρ c : ℂ) * I)) * (B ρ)⁻¹ else 1 by
    obtain ⟨h1, h2⟩ := H (Finset.univ : Finset D.what₂.Tau).toList (Finset.nodup_toList _)
    refine ⟨h1, fun ρ => ?_⟩
    have := h2 ρ
    rw [if_pos (Finset.mem_toList.2 (Finset.mem_univ _))] at this
    exact this
  intro l hl
  induction l with
  | nil =>
    refine ⟨one_mem _, fun ρ => ?_⟩
    simpa using R.2.2.2.2.1 1 (one_mem _) ρ
  | cons τ l ih =>
    rw [List.nodup_cons] at hl
    obtain ⟨i1, i2⟩ := ih hl.2
    rw [List.map_cons, List.prod_cons]
    refine ⟨mul_mem (hu τ).1 i1, fun ρ => ?_⟩
    rw [R.2.2.2.1, i2 ρ]
    by_cases c : ρ = τ
    · subst c
      rw [(hu ρ).2.1, if_neg hl.1, if_pos List.mem_cons_self, Matrix.mul_one]
    · rw [(hu τ).2.2 ρ c, Matrix.one_mul]
      simp only [List.mem_cons, c, false_or]

end GlobalTheory.AdSpan.ConjHol
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdSpan.ConjHol.ToLie

lemma conj_mem_sgn {n : ℕ} (d : Fin n → ℂ) (hd : ∀ a, star (d a) = d a)
    (A : Matrix (Fin n) (Fin n) ℂ) (h : Aᴴ * diagonal d + diagonal d * A = 0) :
    (A.map (starRingEnd ℂ))ᴴ * diagonal d + diagonal d * A.map (starRingEnd ℂ) = 0 := by
  ext i j
  have hij := congrFun (congrFun h i) j
  simp only [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.add_apply, Matrix.zero_apply,
    Matrix.conjTranspose_apply, Matrix.map_apply] at hij ⊢
  have := congrArg star hij
  simp only [star_add, star_mul', star_star, star_zero, hd] at this
  simpa [RCLike.star_def, add_comm, mul_comm] using this

end GlobalTheory.AdSpan.ConjHol.ToLie

open GlobalTheory.AdSpan.ConjHol GlobalTheory.HolRead.AdExt in
theorem GlobalTheory.AdSpan.ConjHol.ToLie.toLieC_spec : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (R : GlobalTheory.SmoothForms.RealPoints C.θ T) (B : C.Bas), C.IsB B → ∀ Z ∈ GlobalTheory.HolRead.unitLie C.X, (∀ ρ, (GlobalTheory.AdSpan.ConjHol.toLieC C R B Z ρ).1 = B ρ * (mat Z (C.m.e ρ)).map (starRingEnd ℂ) * (B ρ)⁻¹) ∧ GlobalTheory.AdSpan.ConjHol.toLieC C R B (I • Z) = 0 := by
  intro D S T C R B hB Z hZ
  have hfix : ∀ ρ, conjAt T ρ (B ρ * (mat Z (C.m.e ρ)).map (starRingEnd ℂ) * (B ρ)⁻¹)
      = B ρ * (mat Z (C.m.e ρ)).map (starRingEnd ℂ) * (B ρ)⁻¹ := by
    intro ρ
    have hW := GlobalTheory.AdSpan.ConjHol.ToLie.conj_mem_sgn _ ?_ _ (hZ (C.m.e ρ))
    · have hB' : (B ρ)ᴴ * gramAt D T ρ * B ρ = diagonal fun (a : Fin T.rank) => ((sgn C.X.p0 (a : ℕ) : ℝ) : ℂ) := hB ρ
      have hL := conj_mem_lie (isUnit_det_B C hB ρ) hB' hW
      exact conj_eq_of_mem_lie (R.1 ρ).2 hL
    · intro a; simp
  refine ⟨fun ρ => ?_, ?_⟩
  · show ((HolRead.AdExt.toLie R B fun ρ => C.m.e ρ) (conjL Z) ρ).1 = _
    rw [toLie_val, mat_conjL, hfix ρ]
    module
  · funext ρ
    apply Subtype.ext
    show ((HolRead.AdExt.toLie R B fun ρ => C.m.e ρ) (conjL (I • Z)) ρ).1 = (0 : Matrix (Fin T.rank) (Fin T.rank) ℂ)
    have hc : conjL (I • Z) = I • (-(conjL Z)) := by
      funext τ a b
      simp [conjL]
    have hm : mat (-(conjL Z)) (C.m.e ρ) = -(mat (conjL Z) (C.m.e ρ)) := rfl
    have hneg : ∀ M : Matrix (Fin T.rank) (Fin T.rank) ℂ,
        conjAt T ρ (B ρ * -M * (B ρ)⁻¹) = -(conjAt T ρ (B ρ * M * (B ρ)⁻¹)) := by
      intro M; simp [conjAt]
    rw [hc, toLie_I, hm, hneg, mat_conjL, hfix ρ]
    simp
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.exists_finiteAdele_of_splitPlaces_idempotentSum : ∀ (D : D7) (P : Finset (Formalism.L2.DIV.Pl D.host.E)) (e : AE D), IsIdemSum e P → ∃ σ : Af D.host.F, algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 σ) = e + cA D e ∧ (∀ w : HeightOneSpectrum (𝓞 D.host.F), (∀ PP ∈ P, HeightOneSpectrum.under (𝓞 D.host.F) PP ≠ w) → evalV D.host.F w σ = 0) ∧ ∀ PP ∈ P, evalV D.host.F (HeightOneSpectrum.under (𝓞 D.host.F) PP) σ = 1 := by
  first | exact @GlobalTheory.IdemSumFinAdele.exists_finAdele_of_idemSum | exact GlobalTheory.IdemSumFinAdele.exists_finAdele_of_idemSum | (intros; apply GlobalTheory.IdemSumFinAdele.exists_finAdele_of_idemSum <;> assumption)
end
