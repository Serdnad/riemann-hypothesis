module

public import Development.AbelianVarietyTheory.Definitions.Foundations.MemSiegelOfIffRightAct
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle163
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle149
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle147
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlagUnipotentFourierJacobiGroupStructure
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle164
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle165
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PlacesToAdeles
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle166
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
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SphericalVolumeLift
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SphericalZero
import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyEqOfIsPreconnected
import Development.AbelianVarietyTheory.Definitions.Foundations.WittIndexEqZeroIff
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.KerBF

@[expose] public section

section

open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

noncomputable section

namespace GlobalTheory.Core.Rk.Dich

open Matrix

section Mat

variable {A B : Type} [CommRing A] [CommRing B] {n : ℕ}

def diagSnd (M : Matrix (Fin (n + n)) (Fin (n + n)) A) : Matrix (Fin n) (Fin n) A :=
  (M.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₂₁ + (M.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₂₂

theorem mulVec_pairVec_diag (M : Matrix (Fin (n + n)) (Fin (n + n)) A) (x : Fin n → A) :
    M *ᵥ pairVec finSumFinEquiv x x =
      pairVec finSumFinEquiv (leviMat finSumFinEquiv M *ᵥ x) (diagSnd M *ᵥ x) := by
  rw [mulVec_pairVec, leviMat, diagSnd, add_mulVec, add_mulVec]

theorem diagSnd_map (f : A →+* B) (M : Matrix (Fin (n + n)) (Fin (n + n)) A) :
    diagSnd (M.map f) = (diagSnd M).map f := by
  ext i j; simp [diagSnd, toBlocks₂₁, toBlocks₂₂]

theorem isotropic_diag {σ : A →+* A} {J : Matrix (Fin n) (Fin n) A} {M : Matrix (Fin (n + n)) (Fin (n + n)) A}
    (hM : Formalism.UG.cT σ M * dblGram finSumFinEquiv J * M = dblGram finSumFinEquiv J) :
    Formalism.UG.cT σ (leviMat finSumFinEquiv M) * J * leviMat finSumFinEquiv M =
      Formalism.UG.cT σ (diagSnd M) * J * diagSnd M := by
  have h1 : Formalism.UG.cT σ (M.submatrix finSumFinEquiv finSumFinEquiv) * fromBlocks J 0 0 (-J) *
      M.submatrix finSumFinEquiv finSumFinEquiv = fromBlocks J 0 0 (-J) := by
    rw [← submatrix_blkMat finSumFinEquiv,
      show Formalism.UG.cT σ (M.submatrix finSumFinEquiv finSumFinEquiv) =
        (Formalism.UG.cT σ M).submatrix finSumFinEquiv finSumFinEquiv from rfl, submatrix_mul_equiv, submatrix_mul_equiv]
    exact congrArg (fun X => X.submatrix finSumFinEquiv finSumFinEquiv) hM
  rw [← fromBlocks_toBlocks (M.submatrix finSumFinEquiv finSumFinEquiv)] at h1
  simp only [Formalism.UG.cT, fromBlocks_map, fromBlocks_transpose, fromBlocks_multiply, Matrix.mul_zero, add_zero,
    zero_add, Matrix.mul_neg, Matrix.neg_mul, fromBlocks_inj] at h1
  obtain ⟨h11, h12, h21, h22⟩ := h1
  simp only [Formalism.UG.cT, leviMat, diagSnd, Matrix.map_add _ (map_add σ), transpose_add, Matrix.add_mul, Matrix.mul_add]
  set a := (M.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₁₁
  set b := (M.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₁₂
  set c := (M.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₂₁
  set d := (M.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₂₂
  rw [← sub_eq_zero]
  have := congrArg₂ (fun a b => a + b) (congrArg₂ (fun a b => a + b) h11 h12) (congrArg₂ (fun a b => a + b) h21 h22)
  simp only [add_zero, add_neg_cancel] at this
  rw [← sub_eq_zero] at this
  rw [← this]
  abel

end Mat

section Rat

open Formalism.BasicNotions Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem exists_rat (W : HSp D) {γ : GA D W} (hγ : γ ∈ GQ W) :
    ∃ g : GL (Fin W.rank) D.host.E, g ∈ Formalism.UG.UJ (D.sp.cm.sig : D.host.E →+* D.host.E) W.gram ∧
      (matHom W γ).1 = g.1.map (incA D) ∧ (matHom W γ⁻¹).1 = (g⁻¹).1.map (incA D) := by
  obtain ⟨g, hg, e⟩ := hγ
  have e' : matHom W γ = Formalism.UG.bc (incA D) g := e.symm
  refine ⟨g, hg, congrArg Units.val e', ?_⟩
  rw [map_inv, e', ← map_inv]
  rfl

theorem exists_of_rat (W : HSp D) {g : GL (Fin W.rank) D.host.E}
    (hg : g ∈ Formalism.UG.UJ (D.sp.cm.sig : D.host.E →+* D.host.E) W.gram) :
    ∃ δ ∈ GQ W, (matHom W δ).1 = g.1.map (incA D) := by
  have hm : Formalism.UG.bc (incA D) g ∈ HR (AF D.host.F) D.sp.cm.sig W.gram := by
    have hc : Formalism.UG.cT (sigR (AF D.host.F) D.sp.cm.sig) ((g : Matrix (Fin W.rank) (Fin W.rank) D.host.E).map (incA D)) =
        (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (g : Matrix (Fin W.rank) (Fin W.rank) D.host.E)).map (incA D) := by
      ext i j; simp [Formalism.UG.cT, sigR, inclR]
    have hg' : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (g : Matrix (Fin W.rank) (Fin W.rank) D.host.E) * W.gram *
        (g : Matrix (Fin W.rank) (Fin W.rank) D.host.E) = W.gram := hg
    change Formalism.UG.cT (sigR (AF D.host.F) D.sp.cm.sig) ((g : Matrix (Fin W.rank) (Fin W.rank) D.host.E).map (incA D)) *
      W.gram.map (incA D) * (g : Matrix (Fin W.rank) (Fin W.rank) D.host.E).map (incA D) = W.gram.map (incA D)
    rw [hc, ← Matrix.map_mul, ← Matrix.map_mul, hg']
  exact ⟨⟨_, hm⟩, ⟨g, hg, rfl⟩, rfl⟩

end Rat

end GlobalTheory.Core.Rk.Dich
end
end

section

open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

namespace GlobalTheory.LatMove

theorem stab_conj_iff {R ι : Type} [CommRing R] [Fintype ι] [DecidableEq ι] (M M' : Set (ι → R)) (B X : GL ι R)
    (hB : ∀ Y, Y ∈ M ↔ B.1 *ᵥ Y ∈ M') :
    (∀ Y, Y ∈ M' ↔ X.1 *ᵥ Y ∈ M') ↔ (∀ Y, Y ∈ M ↔ (B⁻¹ * X * B).1 *ᵥ Y ∈ M) := by
  have key : ∀ Y, B.1 *ᵥ ((B⁻¹ * X * B).1 *ᵥ Y) = X.1 *ᵥ (B.1 *ᵥ Y) := fun Y => by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Units.val_mul, ← Units.val_mul,
      show B * (B⁻¹ * X * B) = X * B by group]
  constructor
  · intro h Y
    rw [hB Y, hB, key]
    exact h _
  · intro h Y
    have hY : B.1 *ᵥ ((B⁻¹).1 *ᵥ Y) = Y := by
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
    have := h ((B⁻¹).1 *ᵥ Y)
    rw [hB, hB, key, hY] at this
    exact this

theorem map_conj_of_eq_one {G H : Type} [Group G] [Group H] (f : G →* H) {g : G} (hg : f g = 1) (x : G) :
    f (g⁻¹ * x * g) = f x := by
  rw [map_mul, map_mul, map_inv, hg, inv_one, one_mul, mul_one]

theorem map_conj' {G H : Type} [Group G] [Group H] (f : G →* H) (g x : G) :
    f (g⁻¹ * x * g) = (f g)⁻¹ * f x * f g := by
  rw [map_mul, map_mul, map_inv]

section General

open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
  {J : Matrix (Fin n) (Fin n) E} {Q : Matrix (Fin (n + n)) (Fin (n + n)) E}

theorem mem_KFin_conj (h : Q = dblGram finSumFinEquiv J) {L L' : Submodule (𝓞 E) (Fin n → E)}
    {v : HeightOneSpectrum (𝓞 F)} (g : GLoc σ J v)
    (hg : ∀ z, z ∈ latLoc F L v ↔ (GlobalTheory.AdelicU.matHom _ σ J g).val *ᵥ z ∈ latLoc F L' v) (x : GLoc σ Q v) :
    x ∈ GlobalTheory.Doubling.KFin σ Q L' v ↔ (ioH _ σ h (g, g))⁻¹ * x * ioH _ σ h (g, g) ∈ GlobalTheory.Doubling.KFin σ Q L v := by
  refine mem_stabLoc.trans (Iff.trans ?_ mem_stabLoc.symm)
  rw [map_conj', matHom_ioH, latLoc_sumLat, latLoc_sumLat]
  refine stab_conj_iff (SetLike.coe (sumLat finSumFinEquiv (latLoc F L v) (latLoc F L v)))
    (SetLike.coe (sumLat finSumFinEquiv (latLoc F L' v) (latLoc F L' v))) _ _ fun Y => ?_
  rw [← pairVec_eta finSumFinEquiv Y, val_blkGL, blkMat_mulVec, SetLike.mem_coe, SetLike.mem_coe,
    pairVec_mem_sumLat, pairVec_mem_sumLat]
  exact and_congr (hg _) (hg _)

theorem mem_KAd_conj (h : Q = dblGram finSumFinEquiv J) {L L' : Submodule (𝓞 E) (Fin n → E)} (k : GAd σ J)
    (hk : k ∈ finPts σ J)
    (hL : ∀ (v : HeightOneSpectrum (𝓞 F)) z,
      z ∈ latLoc F L v ↔ (GlobalTheory.AdelicU.matHom _ σ J (proj σ J v k)).val *ᵥ z ∈ latLoc F L' v)
    (a : GL (Fin n) (AF F ⊗[F] E)) (x : GAd σ Q) :
    x ∈ KAd σ Q L' a ↔ (ioH _ σ h (k, k))⁻¹ * x * ioH _ σ h (k, k) ∈ KAd σ Q L a := by
  refine mem_KAd.trans (Iff.trans (and_congr (forall_congr' fun v => ?_) (forall_congr' fun w => ?_)) mem_KAd.symm)
  · rw [map_conj', proj_ioH]
    exact mem_KFin_conj h _ (hL v) _
  · rw [map_conj_of_eq_one _ (by rw [projArch_ioH, mem_finPts_iff_forall.1 hk w, ioH_one])]

end General

theorem mem_KAd_io_conj : ∀ (D : D7) (A : HSp D) (L L' : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E)) (k : GA D A), k ∈ GfC A →
    (∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (z : Fin A.rank → TensorProduct D.host.F (Fv D.host.F v) D.host.E),
      z ∈ latLoc D.host.F L v ↔
        (GlobalTheory.AdelicU.matHom _ D.sp.cm.sig A.gram (proj D.sp.cm.sig A.gram v k)).val *ᵥ z ∈ latLoc D.host.F L' v) →
    ∀ (a : GL (Fin A.rank) (AE D)) (x : GA D (dblSp A)), x ∈ KAd D.sp.cm.sig (dblSp A).gram L' a ↔
      (io A (k, k))⁻¹ * x * io A (k, k) ∈ KAd D.sp.cm.sig (dblSp A).gram L a :=
  fun D A _ _ k hk hL a x => mem_KAd_conj (σ := D.sp.cm.sig) (gram_hdbl A) k hk hL a x

end GlobalTheory.LatMove
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer
open IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.fixes_latV_of_mem_grpOff : ∀ (D : D7) (S : HSp D) (L : Lat S) (P : Pl D → Prop), ∀ g ∈ grpOff S P, Moves S g L L P := by
  intro D S L P g hg y hy
  obtain ⟨⟨ε, -, -, -, hAt, hOff⟩, -⟩ := GlobalTheory.T.adelicPoint_components_atPlaces_lattices_vacua D P
  have hmul : ∀ a ∈ idOff D P, ∀ b ∈ idAt D P, a * b = 0 := by
    intro a ha b hb
    rw [← (hAt b).1 hb, ← mul_assoc, mul_comm a ε, (hOff a).1 ha, zero_mul]
  have hker := MonoidHom.mem_ker.1 hg
  have hent : ∀ i j, mt S g i j - (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) i j ∈ idOff D P := by
    intro i j
    rw [← Ideal.Quotient.eq]
    have h2 := congrArg (fun u : GL (Fin S.rank) (AE D ⧸ idOff D P) => u.1 i j) hker
    simp only [MonoidHom.comp_apply, Matrix.GeneralLinearGroup.map_apply, Units.val_one] at h2
    have h3 : Ideal.Quotient.mk (idOff D P) ((1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) i j) =
        (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D ⧸ idOff D P)) i j := by
      by_cases hij : i = j
      · subst hij; simp only [Matrix.one_apply_eq, map_one]
      · simp only [Matrix.one_apply_ne hij, map_zero]
    rw [h3, ← h2]
    rfl
  have hfix : mt S g *ᵥ y = y := by
    funext i
    have e : (mt S g *ᵥ y) i = y i + ∑ j, (mt S g i j - (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) i j) * y j := by
      simp [Matrix.mulVec, dotProduct, sub_mul, Finset.sum_sub_distrib, Matrix.one_apply]
    rw [e, Finset.sum_eq_zero (fun j _ => hmul _ (hent i j) _ (hy j)), add_zero]
  rw [hfix]
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open GlobalTheory.FinPl
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.splitPlace_stdChar_continuous_nontrivial : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (ψ : AddChar (AF D.host.F) ℂ) (χ : AddChar k Circle), p.IsChar ψ χ → IsStdChar D ψ (-1) → Continuous χ ∧ χ ≠ 1 := by
  first | exact @GlobalTheory.FinPl.SplitChar.cont_ne_one | exact GlobalTheory.FinPl.SplitChar.cont_ne_one | (intros; apply GlobalTheory.FinPl.SplitChar.cont_ne_one <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (compFin ExtUnramAt CharUnramAt)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer lastPair)
open GlobalTheory.FinPl

theorem _root_.GlobalTheory.T.unitaryAdelic_eq_componentAtPlace_mul_offPlace : ∀ (D : D7) (S : HSp D) (h : GA D S) (v : Pl D), ∃ hv ∈ grpAt S (· = v), ∃ h' ∈ grpOff S (· = v), h = hv * h' := by
  first | exact @GlobalTheory.FinPl.decompAt | exact GlobalTheory.FinPl.decompAt | (intros; apply GlobalTheory.FinPl.decompAt <;> assumption)
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.IwaPlace Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.IwaFlag

variable {D : D7}

theorem cA_mem_idAt' {v : Pl D} {y : AE D} (h : y ∈ idAt D (· = v)) : cA D y ∈ idAt D (· = v) := by
  obtain ⟨ε, -, hc, -, hε, -⟩ := (GlobalTheory.T.adelicPoint_components_atPlaces_lattices_vacua D (· = v)).1
  rw [hε] at h ⊢
  have := congrArg (cA D) h
  rwa [map_mul, hc] at this

theorem mul_left_mem {R : Type} [CommRing R] {I : Ideal R} {l m k : ℕ} (A : Matrix (Fin l) (Fin m) R)
    {M : Matrix (Fin m) (Fin k) R} (h : ∀ i j, M i j ∈ I) (i : Fin l) (j : Fin k) : (A * M) i j ∈ I := by
  rw [Matrix.mul_apply]
  exact Ideal.sum_mem _ fun x _ => Ideal.mul_mem_left _ _ (h x j)

theorem mul_right_mem {R : Type} [CommRing R] {I : Ideal R} {l m k : ℕ} {M : Matrix (Fin l) (Fin m) R}
    (B : Matrix (Fin m) (Fin k) R) (h : ∀ i j, M i j ∈ I) (i : Fin l) (j : Fin k) : (M * B) i j ∈ I := by
  rw [Matrix.mul_apply]
  exact Ideal.sum_mem _ fun x _ => Ideal.mul_mem_right _ _ (h i x)

end GlobalTheory.IwaFlag

namespace GlobalTheory.IwaFlag

variable {D : D7}



theorem flag_stab : ∀ (D : D7) (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (v : Pl D) (g : GA D S), g ∈ grpAt S (· = v) → (∃ a : Mx D ρ ρ, (∀ i j, j < i → a i j = 0) ∧ mt S g ⬝ d.jX = d.jX ⬝ a) → ∃ n ∈ flagN d, n ∈ grpAt S (· = v) ∧ ∃ t : GL (Fin ρ) (AE D), (∀ i j, i ≠ j → t.1 i j = 0) ∧ d.levi t ∈ grpAt S (· = v) ∧ ∃ γ ∈ grpAt S₀ (· = v), g = n * d.levi t * d.emb0 γ := by
  intro D S S₀ ρ d v g hg ⟨a, hup, hgX⟩
  have hG' : ∀ i j, (mt S g - 1) i j ∈ idAt D (· = v) := fun i j => by
    rw [Matrix.sub_apply]; exact (mem_congGrp_iff S (idAt D (· = v)) g).1 hg i j

  have hba : (adj (mt S g ⬝ d.jY) ⬝ (gA S ⬝ d.jX)) * a = 1 := by
    have h1 : adj (mt S g ⬝ d.jY) ⬝ (gA S ⬝ (mt S g ⬝ d.jX)) = 1 := by
      rw [adj_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (gA S), ← Matrix.mul_assoc (adj (mt S g)), mt_unitary]
      exact d.gram_YX
    rw [hgX] at h1
    simpa only [Matrix.mul_assoc] using h1
  have hab : a * (adj (mt S g ⬝ d.jY) ⬝ (gA S ⬝ d.jX)) = 1 := mul_eq_one_comm.1 hba
  obtain ⟨A, hA⟩ : ∃ A : GL (Fin ρ) (AE D), A.1 = a := ⟨⟨a, _, hab, hba⟩, rfl⟩

  have hdet : IsUnit a.det := Matrix.isUnit_det_of_left_inverse hba
  rw [Matrix.det_of_upperTriangular (M := a) (fun ⦃i j⦄ h => hup i j h)] at hdet
  have hu : ∀ i, IsUnit (a i i) := fun i =>
    isUnit_of_dvd_unit (Finset.dvd_prod_of_mem (fun k => a k k) (Finset.mem_univ i)) hdet
  obtain ⟨t, ht1, htinv⟩ : ∃ t : GL (Fin ρ) (AE D), t.1 = diagonal (fun i => a i i) ∧
      (t⁻¹).1 = diagonal (fun i => (((hu i).unit⁻¹ : (AE D)ˣ) : AE D)) :=
    ⟨⟨diagonal (fun i => a i i), diagonal (fun i => (((hu i).unit⁻¹ : (AE D)ˣ) : AE D)),
      by rw [diagonal_mul_diagonal]; simp only [IsUnit.mul_val_inv, diagonal_one],
      by rw [diagonal_mul_diagonal]; simp only [IsUnit.val_inv_mul, diagonal_one]⟩, rfl, rfl⟩
  have ht_diag : ∀ i j, i ≠ j → t.1 i j = 0 := fun i j h => by rw [ht1]; exact diagonal_apply_ne _ h

  have hAt : (A * t⁻¹).1 =
      a * diagonal (fun i => (((hu i).unit⁻¹ : (AE D)ˣ) : AE D)) := by
    rw [Units.val_mul A t⁻¹, htinv, hA]
  have hUX : A * t⁻¹ ∈ UX D ρ := fun i j =>
    ⟨fun h => by rw [hAt, mul_diagonal, hup i j h, zero_mul],
      by rw [hAt, mul_diagonal]; exact IsUnit.mul_val_inv (hu i)⟩
  have hR' : mt S (g * (d.levi t)⁻¹) ⬝ d.jX = d.jX ⬝ (A * t⁻¹).1 := by
    rw [Units.val_mul A t⁻¹, hA, ← map_inv d.levi t, mt_mul, Matrix.mul_assoc, d.levi_jX]
    simpa only [Matrix.mul_assoc] using congrArg (fun M : Mx D S.rank ρ => M ⬝ (t⁻¹).1) hgX
  have hR : g * (d.levi t)⁻¹ ∈ GlobalTheory.Unf.Rgrp S (rat d.e) := ⟨A * t⁻¹, hUX, hR'⟩
  rw [GlobalTheory.Unf.Rgrp_eq d] at hR
  obtain ⟨n, hn, γ, hnγ⟩ := ((flag_jacobi_structure D S S₀ ρ d).2.2.2.1 _).1 hR

  have hcomm : d.levi t * d.emb0 γ = d.emb0 γ * d.levi t := by
    refine d.ga_ext ?_ ?_ ?_
    · rw [GlobalTheory.MixModel.mt_mul S (d.levi t) (d.emb0 γ), GlobalTheory.MixModel.mt_mul S (d.emb0 γ) (d.levi t), Matrix.mul_assoc, Matrix.mul_assoc,
        d.wittDecomp_anisotropicEmbedding_inclX, d.levi_jX, ← Matrix.mul_assoc, d.wittDecomp_anisotropicEmbedding_inclX]
    · rw [GlobalTheory.MixModel.mt_mul S (d.levi t) (d.emb0 γ), GlobalTheory.MixModel.mt_mul S (d.emb0 γ) (d.levi t), Matrix.mul_assoc, Matrix.mul_assoc,
        d.wittDecomp_anisotropicEmbedding_inclAnisotropic, d.wittDecomp_levi_inclAnisotropic, ← Matrix.mul_assoc, d.wittDecomp_levi_inclAnisotropic, d.wittDecomp_anisotropicEmbedding_inclAnisotropic]
    · rw [GlobalTheory.MixModel.mt_mul S (d.levi t) (d.emb0 γ), GlobalTheory.MixModel.mt_mul S (d.emb0 γ) (d.levi t), Matrix.mul_assoc, Matrix.mul_assoc,
        d.wittDecomp_anisotropicEmbedding_inclY, d.levi_jY, ← Matrix.mul_assoc, d.wittDecomp_anisotropicEmbedding_inclY]
  have hgfac : g = n * d.levi t * d.emb0 γ := by
    rw [mul_assoc, hcomm, ← mul_assoc, ← hnγ, inv_mul_cancel_right]

  have hmtγ : mt S₀ γ = d.p0 ⬝ (mt S g ⬝ d.j0) := by
    have e1 : mt S (g * (d.levi t)⁻¹) ⬝ d.j0 = mt S g ⬝ d.j0 := by
      rw [← map_inv d.levi t, mt_mul, Matrix.mul_assoc, d.wittDecomp_levi_inclAnisotropic]
    have e2 : d.p0 ⬝ (mt S (n * d.emb0 γ) ⬝ d.j0) = mt S₀ γ := by
      rw [mt_mul, Matrix.mul_assoc, d.wittDecomp_anisotropicEmbedding_inclAnisotropic, ← Matrix.mul_assoc (mt S n), ← Matrix.mul_assoc,
        GlobalTheory.Unf.flagUnipotent_anisotropic_projection_eq_one d hn, Matrix.one_mul]
    rw [← e2, ← hnγ, e1]
  have hγ : γ ∈ grpAt S₀ (· = v) := (mem_congGrp_iff S₀ _ γ).2 fun i j => by
    have e : mt S₀ γ - 1 = d.p0 ⬝ ((mt S g - 1) ⬝ d.j0) := by
      rw [hmtγ, Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, d.p0_j0]
    rw [← Matrix.sub_apply, e]
    exact mul_left_mem _ (mul_right_mem _ hG') i j

  have haI : ∀ i j, (a - 1) i j ∈ idAt D (· = v) := by
    have e : a - 1 = d.pX ⬝ ((mt S g - 1) ⬝ d.jX) := by
      rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, d.pX_jX, hgX, ← Matrix.mul_assoc, d.pX_jX, Matrix.one_mul]
    intro i j
    rw [e]
    exact mul_left_mem _ (mul_right_mem _ hG') i j
  have ht1I : ∀ i j, (t.1 - 1) i j ∈ idAt D (· = v) := by
    intro i j
    rw [ht1, Matrix.sub_apply]
    by_cases h : i = j
    · subst h
      have := haI i i
      rw [Matrix.sub_apply] at this
      rwa [diagonal_apply_eq]
    · rw [diagonal_apply_ne _ h, Matrix.one_apply_ne h, sub_zero]
      exact Ideal.zero_mem _
  have htiI : ∀ i j, ((t⁻¹).1 - 1) i j ∈ idAt D (· = v) := by
    intro i j
    rw [htinv, Matrix.sub_apply]
    by_cases h : i = j
    · subst h
      have := haI i i
      rw [Matrix.sub_apply, Matrix.one_apply_eq] at this
      rw [diagonal_apply_eq, Matrix.one_apply_eq]
      have e : (((hu i).unit⁻¹ : (AE D)ˣ) : AE D) - 1 = -((((hu i).unit⁻¹ : (AE D)ˣ) : AE D) * (a i i - 1)) := by
        rw [mul_sub, IsUnit.val_inv_mul (hu i)]; ring
      rw [e]
      exact (idAt D (· = v)).neg_mem (Ideal.mul_mem_left _ _ this)
    · rw [diagonal_apply_ne _ h, Matrix.one_apply_ne h, sub_zero]
      exact Ideal.zero_mem _
  have hadjI : ∀ i j, (adj (t⁻¹).1 - 1) i j ∈ idAt D (· = v) := by
    intro i j
    rw [← adj_one, ← adj_sub]
    exact cA_mem_idAt' (htiI j i)
  have hlevI : d.levi t ∈ grpAt S (· = v) := by
    have e : mt S (d.levi t) - 1 = d.jX ⬝ (t.1 - 1) ⬝ d.pX + d.jY ⬝ (adj (t⁻¹).1 - 1) ⬝ d.pY := by
      rw [d.mt_levi, ← d.sum_eq_one]
      simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one]
      abel
    refine (mem_congGrp_iff S _ _).2 fun i j => ?_
    rw [← Matrix.sub_apply, e, Matrix.add_apply]
    exact add_mem (mul_right_mem _ (mul_left_mem _ ht1I) i j) (mul_right_mem _ (mul_left_mem _ hadjI) i j)
  have hnI : n ∈ grpAt S (· = v) := by
    have e : n = g * (d.levi t * d.emb0 γ)⁻¹ := eq_mul_inv_of_mul_eq ((mul_assoc _ _ _).symm.trans hgfac.symm)
    rw [e]
    exact mul_mem hg (inv_mem (mul_mem hlevI (wittCoreEmbedding_preserves_supportedUnitarySubgroup d hγ)))
  exact ⟨n, hn, hnI, t, ht_diag, hlevI, γ, hγ, hgfac⟩

end GlobalTheory.IwaFlag

end
end

section

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (compFin ExtUnramAt CharUnramAt)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.latticeLineRatio_transport_of_columnsCarryLines : ∀ (D : D7) (V V₀ W W₀ : HSp D) (ρ : ℕ) (dV : HypDec V V₀ ρ) (dW : HypDec W W₀ ρ) (LV : Lat V) (LV₀ : Lat V₀) (LW : Lat W) (LW₀ : Lat W₀) (v : Pl D), Tame D v → IsSelfDualC V LV → IsSelfDualC W LW → MonoAt dV LV LV₀ v → MonoAt dW LW LW₀ v → ColsAt dV dW.jX LV LW v → ∀ (i j : Fin ρ) (r : AE D), r ∈ idAt D (· = v) → (∀ a : AE D, colMul dV.jX j a ∈ latV V LV (· = v) → colMul dV.jX i (r * a) ∈ latV V LV (· = v)) → ∀ a ∈ idAt D (· = v), colMul dW.jX j a ∈ latV W LW (· = v) → colMul dW.jX i (r * a) ∈ latV W LW (· = v) := by
  first | exact @GlobalTheory.FinPl.ratio_of_colsAt | exact GlobalTheory.FinPl.ratio_of_colsAt | (intros; apply GlobalTheory.FinPl.ratio_of_colsAt <;> assumption)
end
end

section

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (compFin ExtUnramAt CharUnramAt)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.emb0_mem_grpAt_of_mem_grpAt : ∀ (D : D7) (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (P : Pl D → Prop) (g : GA D S₀), g ∈ grpAt S₀ P → d.emb0 g ∈ grpAt S P := by
  first | exact @GlobalTheory.OneCosetEmb.wittCoreEmbedding_mem_unitaryAdelicSupportedSubgroup | exact GlobalTheory.OneCosetEmb.wittCoreEmbedding_mem_unitaryAdelicSupportedSubgroup | (intros; apply GlobalTheory.OneCosetEmb.wittCoreEmbedding_mem_unitaryAdelicSupportedSubgroup <;> assumption)
end
end

section

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (compFin ExtUnramAt CharUnramAt)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.besselToJacobi_flatMap_vacuum_at_goodPlace : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (ρ : ℕ) (B : BesLev D ρ) (J : JacLev D ρ) (s : StepBF ψ B J) (LV : Lat B.V) (LV₀ : Lat B.V₀) (LW : Lat J.W) (LW₀ : Lat J.W₀) (v : Pl D), GoodBF ψ B J LV LV₀ LW LW₀ v → ∀ 𝔉, IsFlatBF s (· = v) 𝔉 → ∀ f, Vac ψ B.V J.W LV LW (· = v) f → Vac ψ B.V₀ J.W₀ LV₀ LW₀ (· = v) (𝔉 f) := by
  first | exact @GlobalTheory.FinPl.VacFlat.flat_vac | exact GlobalTheory.FinPl.VacFlat.flat_vac | (intros; apply GlobalTheory.FinPl.VacFlat.flat_vac <;> assumption)
end
end

section

open Formalism.BasicNotions

theorem _root_.GlobalTheory.T.ramifiedOperator_bijective_finite_translation_combination : ∀ D : D7, GlobalTheory.FinPl.RamBijective D := by
  first | exact @GlobalTheory.FinPl.ramBijective_holds | exact GlobalTheory.FinPl.ramBijective_holds | (intros; apply GlobalTheory.FinPl.ramBijective_holds <;> assumption)
end
