module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsBlockOrderedSumEquivTrueIndex
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle440
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle455
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle441
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NVNeZero
public import Formalism.LocalToGlobal.Columns.MtHeckeLoc
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle457
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle010
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle335
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FramesStdMatched
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle451
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle011
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftAdelicFormLevelTypeEqColumnLevel
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BlockFrameConjugationIdentity
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGoodFixedVectorOfTypeOccurringInRows
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1177
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle011
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle261
public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.LevelCuspCharacters
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle456
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Countable
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Formalism.LocalToGlobal.HilbertRowConditions.CenterIdempotentAction
import Formalism.LocalToGlobal.IndefiniteReal.RecTie

@[expose] public section

section

open Matrix NumberField MeasureTheory Formalism.DegreeFormula Formalism.MJ Formalism.UG Formalism.L2.Geo
open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.HodgeDomain GlobalTheory.TrueCx GlobalTheory.FlagFibre
open scoped ComplexOrder ENNReal

namespace GlobalTheory.FlagFibre.FlagInt

theorem isEmpty_low_one : IsEmpty (Low 1) :=
  ⟨fun s => by have h := s.2; rw [Subsingleton.elim s.1.1 s.1.2] at h; exact lt_irrefl _ h⟩

theorem isEmpty_low_zero : IsEmpty (Low 0) := ⟨fun s => s.1.1.elim0⟩

theorem volume_univ_of_isEmpty {ι : Type} [Fintype ι] [IsEmpty ι] : (volume : Measure (ι → ℂ)) Set.univ = 1 := by
  rw [volume_pi, Measure.pi_univ]; simp

theorem dens_one (A : Matrix (Fin 1) (Fin 1) ℂ) (y : Low 1 → ℂ) : dens A y = 1 := by
  simp only [dens, lminor, Fin.prod_univ_one]
  have : IsEmpty (Fin ((0 : Fin 1).castSucc : ℕ)) := ⟨fun x => x.elim0⟩
  rw [det_isEmpty]; simp

theorem re_facts {n : Type} [Fintype n] [DecidableEq n] {H : Matrix n n ℂ} (h : H.PosDef) :
    0 < H.det.re ∧ H.det = (H.det.re : ℂ) := by
  have := Complex.pos_iff.1 h.det_pos
  exact ⟨this.1, Complex.ext (by simp) (by simp [← this.2])⟩

theorem lintegral_dens : ∀ (m : ℕ) (A : Matrix (Fin m) (Fin m) ℂ), A.PosDef →
    ∫⁻ y : Low m → ℂ, ENNReal.ofReal (dens A y) = ENNReal.ofReal (A.det.re ^ (1 - (m : ℤ)) / flagConst m) := by
  intro m
  induction m with
  | zero =>
    intro A _
    have := isEmpty_low_zero
    simp [dens, flagConst, volume_univ_of_isEmpty]
  | succ p ih =>
    intro A hA
    have := isEmpty_low_one
    obtain ⟨e, he⟩ := exists_isBlockOrderedSumEquiv p 1
    have hA' : (reindex e e A).PosDef := hA.submatrix e.symm.injective
    have hd : (reindex e e A).det = A.det := det_reindex_self e A
    have hm : Measurable fun y : Low (p + 1) → ℂ => ENNReal.ofReal (dens A y) := (measurable_dens A).ennreal_ofReal
    have hm2 : Measurable fun w => ENNReal.ofReal (dens A (glue e w)) := hm.comp (continuous_glue e).measurable
    obtain ⟨hDpos, hD⟩ := re_facts hA
    have hf := flagConst_pos p
    have hc : 0 ≤ A.det.re ^ (1 - (p : ℤ)) / flagConst p := by positivity
    rw [← (GlobalTheory.T.measurePreserving_glueLowerUnitriangularBlocks _ _ _ e he).lintegral_comp hm, Measure.volume_eq_prod, lintegral_prod _ hm2.aemeasurable]
    have key : ∀ v : Fin p × Fin 1 → ℂ,
        ∫⁻ w : (Low 1 → ℂ) × (Low p → ℂ), ENNReal.ofReal (dens A (glue e (v, w))) =
        ENNReal.ofReal (A.det.re ^ (1 - (p : ℤ)) / flagConst p) *
          ENNReal.ofReal ((shear (reindex e e A) (toMat v)).toBlocks₂₂.det.re ^ (-((p + 1 : ℕ) : ℤ))) := by
      intro v
      have hS := posDef_shear hA' (toMat v)
      obtain ⟨-, h2, h3⟩ := posDef_blocks hS
      have hu := h2.det_pos.ne'.isUnit
      have hm3 : Measurable fun w : (Low 1 → ℂ) × (Low p → ℂ) => ENNReal.ofReal (dens A (glue e (v, w))) :=
        hm2.comp measurable_prodMk_left
      rw [Measure.volume_eq_prod, lintegral_prod _ hm3.aemeasurable]
      have hg := fun (y1 : Low 1 → ℂ) (y2 : Low p → ℂ) => GlobalTheory.T.leadingMinorFlagDensity_glueLowerUnitriangular _ _ _ e he A (v, y1, y2) hu
      simp only [dens_one, one_mul] at hg
      simp only [hg]
      have hdet := det_eq_mul_schur hu
      rw [det_shear, hd] at hdet
      obtain ⟨hp2, he2⟩ := re_facts h2
      obtain ⟨hp3, he3⟩ := re_facts h3
      have hI := ih _ h3
      set S := shear (reindex e e A) (toMat v)
      have hn : ‖S.toBlocks₂₂.det‖ = S.toBlocks₂₂.det.re := by
        conv_lhs => rw [he2, Complex.norm_real, Real.norm_of_nonneg hp2.le]
      have hre : A.det.re = S.toBlocks₂₂.det.re * (schur S).det.re := by
        rw [hdet]; conv_lhs => rw [he2, he3, ← Complex.ofReal_mul, Complex.ofReal_re]
      rw [lintegral_const, volume_univ_of_isEmpty, mul_one, hn]
      simp only [ENNReal.ofReal_mul (zpow_nonneg hp2.le _)]
      rw [lintegral_const_mul _ (measurable_dens _).ennreal_ofReal, hI, ← ENNReal.ofReal_mul (zpow_nonneg hp2.le _),
        ← ENNReal.ofReal_mul hc, hre, mul_zpow]
      congr 1
      have : S.toBlocks₂₂.det.re ^ (-(2 * p : ℤ)) =
          S.toBlocks₂₂.det.re ^ (1 - (p : ℤ)) * S.toBlocks₂₂.det.re ^ (-((p + 1 : ℕ) : ℤ)) := by
        rw [← zpow_add₀ hp2.ne']; congr 1; push_cast; ring
      rw [this]; ring
    simp only [key]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, GlobalTheory.T.hua_integral_positive_definite_quadric p 1 _ hA', ← ENNReal.ofReal_mul hc, hd,
      flagConst_add p 1]
    congr 1
    have h1 : flagConst 1 = 1 := by simp [flagConst]
    have : A.det.re ^ (1 - ((p + 1 : ℕ) : ℤ)) = A.det.re ^ (1 - (p : ℤ)) * A.det.re ^ (-((1 : ℕ) : ℤ)) := by
      rw [← zpow_add₀ hDpos.ne']; congr 1; push_cast; ring
    rw [this, h1]; ring

end GlobalTheory.FlagFibre.FlagInt
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2
open GlobalTheory.Mem.R3.LiftBrg

theorem _root_.GlobalTheory.T.heckeElementInv_latticeClauses_of_frameConj : ∀ {D : D7} (V : HSp D) (n : ℕ) [NeZero n] (h : n = V.rank) (v : HeightOneSpectrum (𝓞 D.host.F)) (Pb : Formalism.L2.DIV.Pl D.host.E) (Ut : Formalism.L2.Col.MhlUnif Pb) (d : ℕ) (e : Formalism.L2.Theta.AE D) (C : GL (Fin n) (Formalism.IndefR.Lev.EAf D)) (α : GA D V), Formalism.L2.NTheta.IsIdemAt e (Formalism.L2.Col.conjPrime₂ Pb) → (∀ z : Formalism.IndefR.Lev.EAf D, Formalism.UG.prV v z = 0 → swapAE D (finPart D e) * z = 0) → (∀ y : Fin V.rank → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E, y ∈ Formalism.L2.NTheta.LamHat V ↔ ∀ j, swapAE D (y j) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) → C ∈ Formalism.L2.DIV.St 1 → α ∈ GfC V → castGL h.symm (Formalism.UG.bc (swapAE D) (finHom V α)) = C * ((Formalism.L2.Col.mhlEta D.sp.cm n v Ut.hπ0 d : Formalism.L2.Col.UAd D.sp.cm n) : GL (Fin n) (Formalism.IndefR.Lev.EAf D)) * C⁻¹ →
    (∀ y ∈ Formalism.L2.NTheta.LamHat V, (fun a => finPart D e * (finMat D.sp.cm.sig V.gram α⁻¹).mulVec y a) ∈ Formalism.L2.NTheta.LamHat V) ∧
    (∀ y ∈ Formalism.L2.NTheta.LamHat V, ∃ z ∈ Formalism.L2.NTheta.LamHat V, (fun a => finPart D e * (finPart D (incA D ((Formalism.L2.Col.cO D.host.E Ut.π : 𝓞 D.host.E) : D.host.E)) * y a)) =
      fun a => finPart D e * (finMat D.sp.cm.sig V.gram α⁻¹).mulVec z a) := by
  first | exact @GlobalTheory.Mem.R3.LiftBrg.EtaInvLat.eta_inv_lat | exact GlobalTheory.Mem.R3.LiftBrg.EtaInvLat.eta_inv_lat | (intros; apply GlobalTheory.Mem.R3.LiftBrg.EtaInvLat.eta_inv_lat <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2
open GlobalTheory.Mem.R3.LiftBrg

namespace GlobalTheory.Mem.R3.LiftBrg.EtaSupp

theorem castGL_bc_comm {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) {m k : ℕ} (h : m = k) (x : GL (Fin m) R) :
    castGL h (Formalism.UG.bc φ x) = Formalism.UG.bc φ (castGL h x) := by
  subst h
  ext i j
  simp [castGL, Formalism.UG.bc]

theorem finE_prV_eq_one {D : D7} (V : HSp D) (n : ℕ) [NeZero n] (h : n = V.rank) (v : HeightOneSpectrum (𝓞 D.host.F))
    (Pb : Formalism.L2.DIV.Pl D.host.E) (Ut : Formalism.L2.Col.MhlUnif Pb) (d : ℕ) (C : GL (Fin n) (Formalism.IndefR.Lev.EAf D)) (α : GA D V)
    (hα : castGL h.symm (Formalism.UG.bc (swapAE D) (finHom V α)) = C * ((Formalism.L2.Col.mhlEta D.sp.cm n v Ut.hπ0 d : Formalism.L2.Col.UAd D.sp.cm n) : GL (Fin n) (Formalism.IndefR.Lev.EAf D)) * C⁻¹)
    (w : HeightOneSpectrum (𝓞 D.host.F)) (hw : w ≠ v) :
    Formalism.UG.bc (Formalism.UG.prV (E := D.host.E) w) (finE V α) = 1 := by
  apply (castGL h.symm).injective
  rw [map_one, castGL_bc_comm]
  show Formalism.UG.bc (Formalism.UG.prV (E := D.host.E) w) (castGL h.symm (Formalism.UG.bc (swapAE D) (finHom V α))) = 1
  rw [hα]
  have key : ∀ {G H : Type} [Group G] [Group H] (f : G →* H) (c x : G), f x = 1 → f (c * x * c⁻¹) = 1 := by
    intro G H _ _ f c x hx
    rw [map_mul, map_mul, hx, mul_one, map_inv, mul_inv_cancel]
  have h1 : Formalism.UG.bc (Formalism.UG.prV (E := D.host.E) w)
      ((Formalism.L2.Col.mhlEta D.sp.cm n v Ut.hπ0 d : Formalism.L2.Col.UAd D.sp.cm n) : GL (Fin n) (Formalism.IndefR.Lev.EAf D)) = 1 :=
    Formalism.L2.Col.rll_put_ne n v w hw _
  exact key _ _ _ h1

end GlobalTheory.Mem.R3.LiftBrg.EtaSupp

namespace GlobalTheory.Mem.R3.LiftBrg

theorem eta_suppAt : ∀ {D : D7} (V : HSp D) (n : ℕ) [NeZero n] (h : n = V.rank) (v : HeightOneSpectrum (𝓞 D.host.F)) (Pb : Formalism.L2.DIV.Pl D.host.E) (Ut : Formalism.L2.Col.MhlUnif Pb) (d : ℕ) (e : Formalism.L2.Theta.AE D) (C : GL (Fin n) (Formalism.IndefR.Lev.EAf D)) (α : GA D V), Formalism.L2.Col.IsOver v Pb → Formalism.L2.NTheta.IsIdemAt e (Formalism.L2.Col.conjPrime₂ Pb) → α ∈ GfC V → castGL h.symm (Formalism.UG.bc (swapAE D) (finHom V α)) = C * ((Formalism.L2.Col.mhlEta D.sp.cm n v Ut.hπ0 d : Formalism.L2.Col.UAd D.sp.cm n) : GL (Fin n) (Formalism.IndefR.Lev.EAf D)) * C⁻¹ → SuppAt e V α := by
  intro D V n _ h v Pb Ut d e C α hv he hα hη
  exact GlobalTheory.T.supportedAt_conjPrimeIdempotent_of_trivial_offPlace V v Pb e hv he α hα fun w hw =>
    EtaSupp.finE_prV_eq_one V n h v Pb Ut d C α hη w hw

end GlobalTheory.Mem.R3.LiftBrg
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2


noncomputable section

namespace GlobalTheory.Mem.R3.LiftBrg.StdGroups

theorem castGL_bc {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) {m n : ℕ} (h : m = n) (x : GL (Fin m) A) :
    castGL h (Formalism.UG.bc f x) = Formalism.UG.bc f (castGL h x) := by
  subst h
  ext i j
  simp [castGL, Formalism.UG.bc, Matrix.reindexAlgEquiv_apply]

theorem castGL_symm_castGL' {A : Type} [CommRing A] {m n : ℕ} (h : m = n) (x : GL (Fin m) A) :
    castGL h.symm (castGL h x) = x := by
  subst h
  ext i j
  simp [castGL, Matrix.reindexAlgEquiv_apply]

theorem castGL_mem_UJ_one {A : Type} [CommRing A] (σ : A →+* A) {m n : ℕ} (h : m = n) (x : GL (Fin m) A)
    (hx : x ∈ Formalism.UG.UJ σ (1 : Matrix (Fin m) (Fin m) A)) : castGL h x ∈ Formalism.UG.UJ σ (1 : Matrix (Fin n) (Fin n) A) := by
  subst h
  have e : castGL (rfl : m = m) x = x := by
    ext i j
    simp [castGL, Matrix.reindexAlgEquiv_apply]
  rwa [e]

theorem bc_injective {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (hf : Function.Injective f) {m : ℕ} :
    Function.Injective (Formalism.UG.bc (n := Fin m) f) := by
  intro x y hxy
  ext i j
  exact hf (congrArg (fun z : GL (Fin m) B => (z : Matrix (Fin m) (Fin m) B) i j) hxy)

def phiG (X : Stages) (i : Fin X.toD7.R.m) (hg : (Vc X.toD7 i).gram = 1) :
    Bridge.Gf (Vc X.toD7 i) →* Formalism.L2.Col.UAd X.toD7.sp.cm X.B.R.nV where
  toFun g := ⟨castGL (rkEq X i).symm (Formalism.UG.bc (swapAE X.toD7) g.1), by
    obtain ⟨k, hk⟩ := g.2
    have h1 : Formalism.UG.bc (swapAE X.toD7) g.1 ∈ Formalism.L2.DIV.UA X.toD7.sp.cm (Vc X.toD7 i).gram := by
      rw [← hk]
      exact GlobalTheory.LevSplit.finE_mem_UA _ k
    rw [hg] at h1
    exact castGL_mem_UA_std _ _ _ h1⟩
  map_one' := Subtype.ext (by simp)
  map_mul' a b := Subtype.ext (by simp)

theorem phiG_val (X : Stages) (i : Fin X.toD7.R.m) (hg : (Vc X.toD7 i).gram = 1) (g : Bridge.Gf (Vc X.toD7 i)) :
    (phiG X i hg g : GL (Fin X.B.R.nV) (LiftBrg.EA X)) = castGL (rkEq X i).symm (Formalism.UG.bc (swapAE X.toD7) g.1) := rfl

theorem phiG_injective (X : Stages) (i : Fin X.toD7.R.m) (hg : (Vc X.toD7 i).gram = 1) :
    Function.Injective (phiG X i hg) := by
  intro a b hab
  have h1 := congrArg (fun z : Formalism.L2.Col.UAd X.toD7.sp.cm X.B.R.nV => (z : GL (Fin X.B.R.nV) (LiftBrg.EA X))) hab
  simp only [phiG_val] at h1
  have h2 := (castGL (rkEq X i).symm).injective h1
  exact Subtype.ext (bc_injective _ (Algebra.TensorProduct.comm _ _ _).injective h2)

theorem phiG_surjective (X : Stages) (i : Fin X.toD7.R.m) (hg : (Vc X.toD7 i).gram = 1) :
    Function.Surjective (phiG X i hg) := by
  intro x
  have hy : castGL (rkEq X i) (x : GL (Fin X.B.R.nV) (LiftBrg.EA X)) ∈ Formalism.L2.DIV.UA X.toD7.sp.cm (Vc X.toD7 i).gram := by
    rw [hg]
    exact castGL_mem_UA_std _ _ _ x.2
  refine ⟨⟨finHom (Vc X.toD7 i) (GlobalTheory.StdFrameExist.liftF (Vc X.toD7 i) _ hy), _, rfl⟩, Subtype.ext ?_⟩
  rw [phiG_val]
  have e := GlobalTheory.StdFrameExist.finE_liftF (Vc X.toD7 i) _ hy
  change castGL (rkEq X i).symm (finE (Vc X.toD7 i) (GlobalTheory.StdFrameExist.liftF (Vc X.toD7 i) _ hy)) = _
  rw [e, castGL_symm_castGL']

end GlobalTheory.Mem.R3.LiftBrg.StdGroups

namespace GlobalTheory.Mem.R3.LiftBrg.StdGroups

theorem bc_inclR_mem_HR {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
    (σ : E →ₐ[F] E) {m : ℕ} (J : Matrix (Fin m) (Fin m) E) (γ : GL (Fin m) E) (hγ : γ ∈ Formalism.UG.UJ (σ : E →+* E) J) :
    Formalism.UG.bc (inclR (F := F) R) γ ∈ HR R σ J := by
  have h : Formalism.UG.cT (σ : E →+* E) (γ : Matrix (Fin m) (Fin m) E) * J * γ = J := hγ
  show Formalism.UG.cT (sigR R σ) ((γ : Matrix (Fin m) (Fin m) E).map (inclR R)) * J.map (inclR R) *
    (γ : Matrix (Fin m) (Fin m) E).map (inclR R) = J.map (inclR R)
  have h2 : Formalism.UG.cT (sigR R σ) ((γ : Matrix (Fin m) (Fin m) E).map (inclR R)) =
      (Formalism.UG.cT (σ : E →+* E) (γ : Matrix (Fin m) (Fin m) E)).map (inclR (F := F) R) := by
    ext i j
    simp [Formalism.UG.cT, sigR, inclR]
  rw [h2, ← Matrix.map_mul, ← Matrix.map_mul, h]

def psiQ (X : Stages) (i : Fin X.toD7.R.m) (hg : (Vc X.toD7 i).gram = 1) :
    Formalism.L2.Col.URat X.toD7.sp.cm X.B.R.nV →* GQ (Vc X.toD7 i) where
  toFun γ :=
    have hm : castGL (rkEq X i) (γ : GL (Fin X.B.R.nV) X.toD7.host.E) ∈
        Formalism.UG.UJ (X.toD7.sp.cm.sig : X.toD7.host.E →+* X.toD7.host.E) (Vc X.toD7 i).gram := by
      rw [hg]
      exact castGL_mem_UJ_one _ _ _ γ.2
    ⟨(show GA X.toD7 (Vc X.toD7 i) from
        (⟨Formalism.UG.bc (inclR (F := X.toD7.host.F) (AF X.toD7.host.F)) (castGL (rkEq X i) (γ : GL (Fin X.B.R.nV) X.toD7.host.E)),
          bc_inclR_mem_HR _ _ _ _ hm⟩ : HR (AF X.toD7.host.F) X.toD7.sp.cm.sig (Vc X.toD7 i).gram)),
      Subgroup.mem_subgroupOf.2 ⟨_, hm, rfl⟩⟩
  map_one' := Subtype.ext (Subtype.ext (by first | rfl | (simp only [map_one]; rfl) | (simp <;> rfl)))
  map_mul' a b := Subtype.ext (Subtype.ext (by first | rfl | (simp only [map_mul]; rfl) | (simp <;> rfl)))

theorem psiQ_mat (X : Stages) (i : Fin X.toD7.R.m) (hg : (Vc X.toD7 i).gram = 1) (γ : Formalism.L2.Col.URat X.toD7.sp.cm X.B.R.nV) :
    matHom (Vc X.toD7 i) (psiQ X i hg γ : GA X.toD7 (Vc X.toD7 i)) =
      Formalism.UG.bc (incA X.toD7) (castGL (rkEq X i) (γ : GL (Fin X.B.R.nV) X.toD7.host.E)) := rfl

theorem phiG_ratF_psiQ (X : Stages) (i : Fin X.toD7.R.m) (hg : (Vc X.toD7 i).gram = 1) (γ : Formalism.L2.Col.URat X.toD7.sp.cm X.B.R.nV) :
    phiG X i hg (Bridge.ratF (Vc X.toD7 i) (psiQ X i hg γ)) = Formalism.L2.Col.ratIn X.toD7.sp.cm X.B.R.nV γ := by
  apply Subtype.ext
  rw [phiG_val, Formalism.L2.Col.ratIn_val]
  have e1 : ((Bridge.ratF (Vc X.toD7 i) (psiQ X i hg γ)) : GL (Fin (Vc X.toD7 i).rank) _) =
      Formalism.UG.bc (inclR (F := X.toD7.host.F) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af X.toD7.host.F)) (castGL (rkEq X i) (γ : GL (Fin X.B.R.nV) X.toD7.host.E)) := by
    change finHom (Vc X.toD7 i) _ = _
    rw [finHom, MonoidHom.comp_apply, Subgroup.coe_subtype, psiQ_mat]
    exact GlobalTheory.HLatMove.bc_map_bc_inclR _ _
  rw [e1]
  have e2 : Formalism.UG.bc (swapAE X.toD7) (Formalism.UG.bc (inclR (F := X.toD7.host.F) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af X.toD7.host.F))
      (castGL (rkEq X i) (γ : GL (Fin X.B.R.nV) X.toD7.host.E))) =
      Formalism.UG.bc (Formalism.L2.Col.iA X.toD7.host.F X.toD7.host.E) (castGL (rkEq X i) (γ : GL (Fin X.B.R.nV) X.toD7.host.E)) := by
    ext a b
    simp [Formalism.UG.bc, swapAE, inclR, Formalism.UG.inclE]
  rw [e2, ← castGL_bc, castGL_symm_castGL']

theorem psiQ_injective (X : Stages) (i : Fin X.toD7.R.m) (hg : (Vc X.toD7 i).gram = 1) :
    Function.Injective (psiQ X i hg) := by
  intro a b hab
  have h1 : Formalism.L2.Col.ratIn X.toD7.sp.cm X.B.R.nV a = Formalism.L2.Col.ratIn X.toD7.sp.cm X.B.R.nV b := by
    rw [← phiG_ratF_psiQ X i hg a, ← phiG_ratF_psiQ X i hg b, hab]
  have h2 := congrArg (fun z : Formalism.L2.Col.UAd X.toD7.sp.cm X.B.R.nV => (z : GL (Fin X.B.R.nV) (LiftBrg.EA X))) h1
  simp only [Formalism.L2.Col.ratIn_val] at h2
  exact Subtype.ext (Formalism.L2.DIV.incl_inj _ _ _ h2)

theorem psiQ_surjective (X : Stages) (i : Fin X.toD7.R.m) (hg : (Vc X.toD7 i).gram = 1) :
    Function.Surjective (psiQ X i hg) := by
  intro δ
  obtain ⟨γE, hγE, e⟩ := Subgroup.mem_subgroupOf.1 δ.2
  have hγ : castGL (rkEq X i).symm γE ∈ Formalism.L2.Col.URat X.toD7.sp.cm X.B.R.nV := by
    rw [hg] at hγE
    exact castGL_mem_UJ_one _ _ _ hγE
  refine ⟨⟨_, hγ⟩, Subtype.ext (Subtype.ext ?_)⟩
  change Formalism.UG.bc (inclR (F := X.toD7.host.F) (AF X.toD7.host.F)) (castGL (rkEq X i) (castGL (rkEq X i).symm γE)) = _
  rw [castGL_symm_castGL' (rkEq X i).symm γE]
  exact e

theorem stdGroups_equiv : ∀ (X : Stages) (i : Fin X.toD7.R.m), (Vc X.toD7 i).gram = 1 →
    ∃ (eG : Formalism.L2.Col.UAd X.toD7.sp.cm X.B.R.nV ≃* Bridge.Gf (Vc X.toD7 i))
      (eΓ : Formalism.L2.Col.URat X.toD7.sp.cm X.B.R.nV ≃* GQ (Vc X.toD7 i)),
      (∀ x, LiftBrg.castGL (LiftBrg.rkEq X i).symm (Formalism.UG.bc (swapAE X.toD7)
          ((eG x : Bridge.Gf (Vc X.toD7 i)) : GL (Fin (Vc X.toD7 i).rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af X.toD7.host.F ⊗[X.toD7.host.F] X.toD7.host.E))) =
        (x : GL (Fin X.B.R.nV) (LiftBrg.EA X))) ∧
      (∀ γ, Bridge.ratF (Vc X.toD7 i) (eΓ γ) = eG (Formalism.L2.Col.ratIn X.toD7.sp.cm X.B.R.nV γ)) ∧
      (∀ γ, Bridge.IsRatMat (Vc X.toD7 i) (eΓ γ) (LiftBrg.castGL (LiftBrg.rkEq X i) (γ : GL (Fin X.B.R.nV) X.toD7.host.E))) := by
  intro X i hg
  let eG0 := MulEquiv.ofBijective (phiG X i hg) ⟨phiG_injective X i hg, phiG_surjective X i hg⟩
  let eQ := MulEquiv.ofBijective (psiQ X i hg) ⟨psiQ_injective X i hg, psiQ_surjective X i hg⟩
  refine ⟨eG0.symm, eQ, fun x => ?_, fun γ => ?_, fun γ => ?_⟩
  · have h := eG0.apply_symm_apply x
    exact congrArg (fun z : Formalism.L2.Col.UAd X.toD7.sp.cm X.B.R.nV => (z : GL (Fin X.B.R.nV) (LiftBrg.EA X))) h
  · rw [MulEquiv.eq_symm_apply]
    exact phiG_ratF_psiQ X i hg γ
  · exact psiQ_mat X i hg γ

end GlobalTheory.Mem.R3.LiftBrg.StdGroups
end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2



theorem _root_.GlobalTheory.T.liftAdelicForm_level_type_eq_columnLevel : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (U : Set I.ι)
    (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)), I.Ok → ValsIn I → LevOf X I U L →
    ∀ (i : Fin X.toD7.R.m) (t : TupU I U) (eG : Formalism.L2.Col.UAd X.toD7.sp.cm X.B.R.nV ≃* Bridge.Gf (Vc X.toD7 i)),
    (∀ x, LiftBrg.castGL (LiftBrg.rkEq X i).symm (Formalism.UG.bc (swapAE X.toD7)
          ((eG x : Bridge.Gf (Vc X.toD7 i)) : GL (Fin (Vc X.toD7 i).rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af X.toD7.host.F ⊗[X.toD7.host.F] X.toD7.host.E))) =
        (x : GL (Fin X.B.R.nV) (LiftBrg.EA X))) →
    ∃ hJ : (levEnv (Vc X.toD7 i) (L.βV i) (L.datVt i t)).J =
        (Bridge.colJ X.toD7.sp.cm X.B.R.nV ∅ (LiftBrg.sgL X I U t)
          (Formalism.L2.Col.mtTyKK I.Ch I.sel t.1 ((i : ℕ) + 1)).inv.grp).map eG.toMonoidHom,
      ∀ (k : Bridge.colJ X.toD7.sp.cm X.B.R.nV ∅ (LiftBrg.sgL X I U t) (Formalism.L2.Col.mtTyKK I.Ch I.sel t.1 ((i : ℕ) + 1)).inv.grp)
        (hk : eG (k : Formalism.L2.Col.UAd X.toD7.sp.cm X.B.R.nV) ∈ (levEnv (Vc X.toD7 i) (L.βV i) (L.datVt i t)).J),
        (((levEnv (Vc X.toD7 i) (L.βV i) (L.datVt i t)).χ ⟨eG k, hk⟩)⁻¹ : ℂˣ) =
          Units.map X.toD7.what₂.embLL.toMonoidHom ((Formalism.L2.Col.mtTyKK I.Ch I.sel t.1 ((i : ℕ) + 1)).inv.chr
            (Formalism.L2.Col.redH X.toD7.sp.cm X.B.R.nV ∅ (LiftBrg.sgL X I U t) _
              ((Bridge.colJEquiv X.toD7.sp.cm X.B.R.nV ∅ (LiftBrg.sgL X I U t) _).symm k))) ∧
        ((k : Formalism.L2.Col.UAd X.toD7.sp.cm X.B.R.nV) ∈ Bridge.principalCongruenceSubgroup X.toD7.sp.cm X.B.R.nV ∅ (LiftBrg.sgL X I U t) →
          (levEnv (Vc X.toD7 i) (L.βV i) (L.datVt i t)).χ ⟨eG k, hk⟩ = 1) := by
  first | exact @GlobalTheory.Mem.LevPres.lev_type_eq | exact GlobalTheory.Mem.LevPres.lev_type_eq | (intros; apply GlobalTheory.Mem.LevPres.lev_type_eq <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3
attribute [local instance] Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.CuspMult

namespace GlobalTheory.IsotHom

theorem isotIn_eq_iSup_homInto : ∀ {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (M : DSModel V S) {n : ℕ} (P : principalLevelFrame.RowPsi V n) (π : Formalism.L2.NG.FinTyp D.host.E n), principalLevelFrame.isotIn (principalLevelFrame.actM P M) (principalLevelFrame.Minf θ P M) π = ⨆ f ∈ homInto ((GlobalTheory.OccRowVec.finRep π).comp (GlobalTheory.KapIsot.eqv P).symm.toMonoidHom) (finRep M) (allMaps θ M), LinearMap.range f := by
  intro D V S θ M n P π
  classical
  set e := GlobalTheory.KapIsot.eqv P with he
  have hσ : ∀ κ (x : π.S), ((GlobalTheory.OccRowVec.finRep π).comp e.symm.toMonoidHom) (e κ) x = GlobalTheory.OccRowVec.finRep π κ x := fun κ x => by
    show GlobalTheory.OccRowVec.finRep π (e.symm (e κ)) x = _
    rw [MulEquiv.symm_apply_apply]
  have hact : ∀ κ (T : MMap M), principalLevelFrame.actM P M κ T = finRep M (e κ) T := fun κ T => by
    refine MultilinearMap.ext fun v => funext fun g => ?_
    rw [principalLevelFrame.actM_apply, finRep_apply]
    rfl
  have hle : principalLevelFrame.Minf θ P M ≤ allMaps θ M := iSup_le fun N => GlobalTheory.PartDims.mult_le θ M fun k hk => hk.elim
  apply le_antisymm
  · refine iSup₂_le fun Φ hΦ => ?_
    refine le_iSup₂_of_le (f := fun f (_ : f ∈ homInto ((GlobalTheory.OccRowVec.finRep π).comp e.symm.toMonoidHom) (finRep M) (allMaps θ M)) => LinearMap.range f) Φ ⟨fun s => hle (hΦ.2 ⟨s, rfl⟩), fun g s => ?_⟩ le_rfl
    obtain ⟨κ, rfl⟩ := e.surjective g
    rw [hσ, ← hact]
    exact hΦ.1 κ s
  · refine iSup₂_le fun f hf => ?_
    have hfe : principalLevelFrame.IsEqvA (principalLevelFrame.actM P M) π f := by
      intro κ x
      have h1 := hf.2 (e κ) x
      rw [hσ, ← hact] at h1
      exact h1
    have hfr : LinearMap.range f ≤ principalLevelFrame.Minf θ P M := by
      rintro _ ⟨x, rfl⟩
      obtain ⟨N, hN, hfix⟩ := π.smooth x x.2
      obtain ⟨N, rfl⟩ : ∃ N', N = N' + 1 := ⟨N - 1, by omega⟩
      refine Submodule.mem_iSup_of_mem N (Submodule.subset_span ?_)
      have h1 := (GlobalTheory.MultMem.mem_mult_iff ..).1 (hf.1 x)
      refine ⟨h1.aut, h1.cusp, ?_, h1.equiv, h1.cont⟩
      rintro v _ ⟨κ, hκ, rfl⟩ g
      have h2 := hfe κ x
      rw [show (⟨Formalism.L2.NG.rt D.host.E n κ x, π.stable κ x x.2⟩ : π.S) = x from Subtype.ext (hfix κ hκ)] at h2
      rw [one_mul]
      exact (congrArg (fun T : MMap M => T v g) h2).symm
    exact le_iSup₂_of_le (f := fun (Φ : π.S →ₗ[ℂ] MMap M) (_ : principalLevelFrame.IsEqvA (principalLevelFrame.actM P M) π Φ ∧ LinearMap.range Φ ≤ principalLevelFrame.Minf θ P M) => LinearMap.range Φ) f ⟨hfe, hfr⟩ le_rfl

end GlobalTheory.IsotHom
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3
open Classical
open GlobalTheory.Mem.R3.HasLabelling

theorem _root_.GlobalTheory.T.exists_familyLabel_containing_finiteTypeParts : GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y), Pins R F cG → Holds R F → HostHyp D → ∀ σ : D.what₂.FT, ∃ p, HasLab Y σ p := by
  first | exact @GlobalTheory.Mem.R3.LabProof.hasLab_exists | exact GlobalTheory.Mem.R3.LabProof.hasLab_exists | (intros; apply GlobalTheory.Mem.R3.LabProof.hasLab_exists <;> assumption)
end
