module

public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.AtTauExUniqueHolds
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.UnimodInst
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.Bundle007
public import Formalism.LocalToGlobal.IndefiniteReal.HaarTransfer.UnimodP
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.NumFieldHosCountable
public import Formalism.PeriodIntegrals.ExplicitFormulaCounts.AdUnimod
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle011
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta
open scoped TensorProduct

namespace Formalism.IndefR.Eqv

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {V : HSp D} (fr : UI.Frames D V)

def uM (x : (UI.instV fr).GA) (v : InfinitePlace D.host.F) : Matrix (Fin V.rank) (Fin V.rank) ℂ := uMat (x.1 v)

theorem thetaV_eq_psiT (ρ : D.what₂.Tau) :
    Formalism.L2.SG.AdBridge.thetaV (UI.instV fr) (Formalism.L2.Host.tauPl D ρ) = psiT D ρ := by
  refine RingHom.ext fun z => ?_
  induction z using TensorProduct.induction_on with
  | zero => exact (map_zero _).trans (map_zero _).symm
  | tmul a x =>
    have h1 := Formalism.L2.SG.AdBridge.thetaV_tmul (UI.instV fr) (Formalism.L2.Host.tauPl D ρ) a x
    have h2 : ∀ (a : AF D.host.F) (x : D.host.E),
        psiT D ρ (a ⊗ₜ[D.host.F] x) = gW D (plW D ρ) (fstA D.host.F a) * tauE D ρ x := fun a x => by
      show thetaC D ρ ((fstA D.host.F a) ⊗ₜ[D.host.F] x) = _
      rw [thetaC_tmul]
    refine h1.trans (Eq.trans ?_ (h2 a x).symm)
    have h3 : tauE D ((Formalism.L2.Host.tauPl D).symm (Formalism.L2.Host.tauPl D ρ)) x = tauE D ρ x := by
      rw [Equiv.symm_apply_apply]
    exact congrArg₂ (· * ·) rfl h3
  | add x y hx hy => exact (map_add _ x y).trans ((congrArg₂ (· + ·) hx hy).trans (map_add _ x y).symm)

theorem P_isUnit_det (v : InfinitePlace D.host.F) : IsUnit (fr.P v).det :=
  (Matrix.isUnit_iff_isUnit_det _).mp (fr.unit v)

theorem infMat_brg (x : (UI.instV fr).GA) (ρ : D.what₂.Tau) :
    infMat D.sp.cm.sig V.gram (thetaC D ρ) (UI.brg fr x) =
      fr.P (Formalism.L2.Host.tauPl D ρ) * uM fr x (Formalism.L2.Host.tauPl D ρ) * (fr.P (Formalism.L2.Host.tauPl D ρ))⁻¹ := by
  have hb : uM fr x (Formalism.L2.Host.tauPl D ρ) = (fr.P (Formalism.L2.Host.tauPl D ρ))⁻¹ *
      (matA D V (UI.brg fr x)).map (psiT D ρ) * fr.P (Formalism.L2.Host.tauPl D ρ) := by
    have h := ((UI.brg_isBridge fr) x).1 (Formalism.L2.Host.tauPl D ρ)
    have h2 := thetaV_eq_psiT fr ρ
    unfold Formalism.L2.SG.AdBridge.ofHAInf at h
    rw [h2] at h
    exact h
  rw [hb, infMat_thetaC]
  have hu := P_isUnit_det fr (Formalism.L2.Host.tauPl D ρ)
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu, Matrix.one_mul, Matrix.mul_assoc,
    Matrix.mul_nonsing_inv _ hu, Matrix.mul_one]

theorem mat_eq_one_of_thetaC {M : Matrix (Fin V.rank) (Fin V.rank) (Ainf D.host.F ⊗[D.host.F] D.host.E)}
    (h : ∀ ρ, M.map (thetaC D ρ) = 1) : M = 1 := by
  ext i j
  have hz : M i j - (1 : Matrix (Fin V.rank) (Fin V.rank) (Ainf D.host.F ⊗[D.host.F] D.host.E)) i j = 0 := by
    apply thetaC_inj
    intro ρ
    have := congrFun (congrFun (h ρ) i) j
    rw [Matrix.map_apply] at this
    rw [map_sub, this, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  exact sub_eq_zero.mp hz

theorem uM_one_iff (x : (UI.instV fr).GA) : x.1 = 1 ↔ ∀ v, uM fr x v = 1 := by
  unfold uM uMat
  constructor
  · rintro h v
    rw [h]
    rfl
  · intro h
    funext v
    exact Subtype.ext (Units.ext (h v))

theorem brg_mem_GfC (x : (UI.instV fr).GA) : UI.brg fr x ∈ GfC V ↔ x.1 = 1 := by
  have key : UI.brg fr x ∈ GfC V ↔ (matA D V (UI.brg fr x)).map (infPart D) = 1 := by
    constructor
    · intro hh
      exact congrArg (fun u : GL (Fin V.rank) (Ainf D.host.F ⊗[D.host.F] D.host.E) => u.1) (MonoidHom.mem_ker.mp hh)
    · intro hh
      exact MonoidHom.mem_ker.mpr (Units.ext hh)
  rw [key, uM_one_iff]
  have hc : ∀ ρ, ((matA D V (UI.brg fr x)).map (infPart D)).map (thetaC D ρ) =
      fr.P (Formalism.L2.Host.tauPl D ρ) * uM fr x (Formalism.L2.Host.tauPl D ρ) * (fr.P (Formalism.L2.Host.tauPl D ρ))⁻¹ := by
    intro ρ
    rw [← infMat_brg, infMat_thetaC, Matrix.map_map]
    rfl
  constructor
  · intro h1 v
    obtain ⟨ρ, rfl⟩ := (Formalism.L2.Host.tauPl D).surjective v
    have hu := P_isUnit_det fr (Formalism.L2.Host.tauPl D ρ)
    have e' : fr.P (Formalism.L2.Host.tauPl D ρ) * uM fr x (Formalism.L2.Host.tauPl D ρ) * (fr.P (Formalism.L2.Host.tauPl D ρ))⁻¹ = 1 := by
      rw [← hc ρ, h1, Matrix.map_one _ (map_zero _) (map_one _)]
    calc uM fr x (Formalism.L2.Host.tauPl D ρ)
        = (fr.P (Formalism.L2.Host.tauPl D ρ))⁻¹ * (fr.P (Formalism.L2.Host.tauPl D ρ) * uM fr x (Formalism.L2.Host.tauPl D ρ) *
          (fr.P (Formalism.L2.Host.tauPl D ρ))⁻¹) * fr.P (Formalism.L2.Host.tauPl D ρ) := by
          rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu, Matrix.one_mul, Matrix.mul_assoc,
            Matrix.nonsing_inv_mul _ hu, Matrix.mul_one]
      _ = 1 := by rw [e', Matrix.mul_one, Matrix.nonsing_inv_mul _ hu]
  · intro h1
    apply mat_eq_one_of_thetaC
    intro ρ
    rw [hc ρ, h1, Matrix.mul_one, Matrix.mul_nonsing_inv _ (P_isUnit_det fr _)]

theorem tauF_eq : Formalism.L2.SG.AdBridge.tauF (UI.instV fr) =
    (Lev.swapAE D).comp (Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E)).toRingHom := by
  refine RingHom.ext fun z => ?_
  induction z using TensorProduct.induction_on with
  | zero => exact (map_zero _).trans (map_zero _).symm
  | tmul a x => exact (Formalism.L2.SG.AdBridge.tauF_tmul (UI.instV fr) a x).trans rfl
  | add x y hx hy => exact (map_add _ x y).trans ((congrArg₂ (· + ·) hx hy).trans (map_add _ x y).symm)

theorem finE_brg (x : (UI.instV fr).GA) : Lev.finE V (UI.brg fr x) = (x.2.1 : GL (Fin V.rank) (Lev.EAf D)) := by
  apply Units.ext
  have hb := ((UI.brg_isBridge fr) x).2
  unfold Formalism.L2.SG.AdBridge.ofHAFin at hb
  rw [tauF_eq] at hb
  exact hb.symm

end Formalism.IndefR.Eqv

end
end

section

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta

namespace Formalism.IndefR.Eqv

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Fin

variable {D : D7} {V : HSp D} (fr : UI.Frames D V)

def jf (x : (UI.instV fr).Gf) : GA D V := UI.brg fr (1, x)

theorem jf_isClosedEmbedding : Topology.IsClosedEmbedding (jf fr) := by
  haveI : T2Space (Matrix (Fin (UI.instV fr).n) (Fin (UI.instV fr).n) ℂ)ˣ :=
    Units.isEmbedding_embedProduct.t2Space
  haveI : T2Space (UI.instV fr).Ginf := inferInstance
  have hemb : Topology.IsEmbedding (fun x : (UI.instV fr).Gf => ((1 : (UI.instV fr).Ginf), x)) :=
    Function.LeftInverse.isEmbedding (f := Prod.snd) (fun _ => rfl) continuous_snd
      (continuous_const.prodMk continuous_id)
  have hcl : IsClosed (Set.range fun x : (UI.instV fr).Gf => ((1 : (UI.instV fr).Ginf), x)) := by
    have hr : (Set.range fun x : (UI.instV fr).Gf => ((1 : (UI.instV fr).Ginf), x)) =
        ({1} : Set (UI.instV fr).Ginf) ×ˢ Set.univ := by
      ext ⟨a, b⟩
      constructor
      · rintro ⟨y, hy⟩
        simp only [Prod.mk.injEq] at hy
        exact ⟨hy.1.symm, Set.mem_univ _⟩
      · rintro ⟨ha, -⟩
        have ha' : a = 1 := ha
        exact ⟨b, by rw [ha']⟩
    rw [hr]
    exact isClosed_singleton.prod isClosed_univ
  have h1 : Topology.IsClosedEmbedding
      (fun x : (UI.instV fr).Gf => ((1 : (UI.instV fr).Ginf), x)) := ⟨hemb, hcl⟩
  exact (UI.brg fr).toHomeomorph.isClosedEmbedding.comp h1

theorem gf_facts : T2Space (UI.instV fr).Gf ∧ LocallyCompactSpace (UI.instV fr).Gf ∧
    SecondCountableTopology (UI.instV fr).Gf := by
  obtain ⟨h1, h2, h3⟩ := G5.af_facts D.host.F
  obtain ⟨h1, h2, h3, h4, h5⟩ := G5.ha_facts (AF D.host.F) D.sp.cm.deg2 D.sp.cm.sig V.gram
  have he := jf_isClosedEmbedding fr
  exact ⟨he.isEmbedding.t2Space, he.locallyCompactSpace, he.isInducing.secondCountableTopology⟩

end Fin

theorem uJ_rightInv {n : ℕ} (ε : Fin n → Bool) (μ : Measure (Formalism.REAL.UJ ε)) (hμ : μ.IsHaarMeasure) :
    μ.IsMulRightInvariant := by
  have hR : (Formalism.REAL.muG ε).IsMulRightInvariant := unitary_unimodular_right_inv n ε
  rw [Measure.isMulLeftInvariant_eq_smul μ (Formalism.REAL.muG ε)]
  exact ⟨fun g => by rw [Measure.map_smul _ (continuous_mul_const g).aemeasurable,
    hR.map_mul_right_eq_self]⟩

theorem unimodGA_of_frames {D : D7} {V : HSp D} (fr : UI.Frames D V) : UnimodGA V := by
  obtain ⟨h1, h2, h3⟩ := G5.af_facts D.host.F
  obtain ⟨h1, h2, h3, h4, h5⟩ := G5.ha_facts (AF D.host.F) D.sp.cm.deg2 D.sp.cm.sig V.gram
  obtain ⟨g1, g2, g3⟩ := gf_facts fr
  have hinf : ∀ μ : Measure (UI.instV fr).Ginf, μ.IsHaarMeasure → μ.IsMulRightInvariant :=
    Leaf.Proofs.piStatement_holds (InfinitePlace D.host.F) (fun v => Formalism.REAL.UJ (fr.ε v))
      (fun v μ hμ => uJ_rightInv (fr.ε v) μ hμ)
  have hf : ∀ μ : Measure (UI.instV fr).Gf, μ.IsHaarMeasure → μ.IsMulRightInvariant :=
    fun μ hμ => adUnimod_closed (UI.instV fr) μ hμ
  have hprod := Leaf.Proofs.prodStatement_holds (UI.instV fr).Ginf (UI.instV fr).Gf hinf hf
  exact Leaf.Proofs.transferStatement_holds (UI.instV fr).GA (GA D V) (UI.brg fr) hprod

theorem unimodGA_holds {D : D7} (V : HSp D) : UnimodGA V :=
  unimodGA_of_frames (UI.frames_nonempty D V).some

end Formalism.IndefR.Eqv

end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open scoped TensorProduct InnerProductSpace

namespace Formalism.IndefR.Eqv.Act

open Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Links.RealDat

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Gen

variable {D : D7} {V : HSp D} {β : GL (Fin V.rank) (EAf D)}

variable {n r : ℕ} {κF : Type} [CommRing κF]

theorem mem_blockTriangular_twoBlockSizes_of_le {r : ℕ} (hn : n ≤ r) (g : GL (Fin n) κF) : g ∈ blockTri (blk2 (n := n) r) := by
  show (g : Matrix (Fin n) (Fin n) κF).BlockTriangular (blk2 r)
  intro i j hij
  have hi : i.val < r := lt_of_lt_of_le i.2 hn
  have hj : j.val < r := lt_of_lt_of_le j.2 hn
  simp [blk2, hi, hj] at hij

theorem block_determinant_empty_eq_one {r : ℕ} (hn : n ≤ r) (g : GL (Fin n) κF) : dBlk (blk2 (n := n) r) 1 g = 1 := by
  unfold dBlk
  rw [extendOne_of_mem _ (mem_blockTriangular_twoBlockSizes_of_le hn g)]
  have : IsEmpty {a : Fin n // blk2 r a = 1} :=
    ⟨fun a => by
      have ha := a.2
      simp [blk2, lt_of_lt_of_le a.1.2 hn] at ha⟩
  ext
  simp [blkDet]

theorem mem_parLev_datY_noQ (hn : V.rank ≤ r) (hr : r ≤ V.rank) (t j : ℕ) (Pg Q : Finset (Pl D.host.E))
    (P : LevelP Pg r ℂ) (χ : ℕ → ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (ξ ξ' : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (fr : Formalism.IndefR.Lev.Frm)
    (x : GL (Fin V.rank) (EAf D)) :
    x ∈ parLev D.sp.cm V.gram β (datY V.rank r t j hr Pg Q P χ ξ fr) ↔
      x ∈ parLev D.sp.cm V.gram β (datY V.rank r t j hr Pg ∅ P χ ξ' fr) := by
  unfold parLev
  simp only [Subgroup.mem_inf, Subgroup.mem_iInf]
  constructor
  · rintro ⟨h1, -⟩
    refine ⟨h1, fun PP hPP => absurd hPP (Finset.notMem_empty _)⟩
  · rintro ⟨h1, -⟩
    refine ⟨h1, fun PP _ => ?_⟩
    have hst : x ∈ St β := h1.1.2
    exact mem_parah.2 ⟨hst, mem_blockTriangular_twoBlockSizes_of_le (n := V.rank) (κF := kP PP) hn (redFn β PP x)⟩

theorem levFn_datY_noQ (hn : V.rank ≤ r) (hr : r ≤ V.rank) (t j : ℕ) (Pg Q : Finset (Pl D.host.E))
    (P : LevelP Pg r ℂ) (χ : ℕ → ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (ξ ξ' : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (fr : Formalism.IndefR.Lev.Frm)
    (x : GL (Fin V.rank) (EAf D)) :
    levFn β (flagL (datY V.rank r t j hr Pg Q P χ ξ fr)) x = levFn β (flagL (datY V.rank r t j hr Pg ∅ P χ ξ' fr)) x := by
  unfold levFn
  have hq : ∀ PP ∈ (flagL (datY V.rank r t j hr Pg Q P χ ξ fr)).Q,
      (flagL (datY V.rank r t j hr Pg Q P χ ξ fr)).xq PP
        (dBlk (blk2 (flagL (datY V.rank r t j hr Pg Q P χ ξ fr)).r) 1 (redFn β PP x)) = 1 := by
    intro PP _
    show _ = 1
    rw [show (flagL (datY V.rank r t j hr Pg Q P χ ξ fr)).r = r from rfl, block_determinant_empty_eq_one hn, map_one]
  rw [Finset.prod_eq_one hq]
  rfl

end Gen

section Idem

variable {K : Type} [Field K] {G : Type} [Group G] [Fintype G]

end Idem

section GA

variable {D : D7} {V : HSp D} {β : GL (Fin V.rank) (EAf D)} {L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank}

end GA

section MultLev

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar}

end MultLev

section Real

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
variable {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)

theorem rank_lowerChainSpace_zero_le : (Yc D 0).rank ≤ D.R.r := by
  rw [D.sp.Y_rank _ (min_le_right _ _)]
  show D.R.r + min 0 D.R.m * D.R.t ≤ D.R.r
  simp

end Real

end Formalism.IndefR.Eqv.Act

end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open scoped TensorProduct InnerProductSpace

namespace Formalism.IndefR.Eqv.Act

open Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Links.RealDat

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
variable {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)

def SpanP : Prop :=
  ∀ i, ∀ S ∈ R.Wall i (sg0 D A), (∀ v : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ, S (fun ρ => v ρ) = 0) → S = 0

end Formalism.IndefR.Eqv.Act

end
end
