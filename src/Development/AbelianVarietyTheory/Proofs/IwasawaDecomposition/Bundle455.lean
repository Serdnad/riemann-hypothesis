module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle423
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle439
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle437
public import Formalism.LocalToGlobal.Columns.RowFormsSum
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsBlockOrderedSumEquivTrueIndex
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemSmulLk
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle015
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle306
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle430
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle286
import Formalism.LocalToGlobal.GlobalTheory.GL6.PBwLocBases
import Formalism.LocalToGlobal.GlobalTheory.GL6.PRLocV
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Afsplit
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NVNeZero
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle440
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1603
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParahoricLevelLiftsExist
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle319
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle365
import Formalism.LocalToGlobal.Columns.AdelicLemmas
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle441
public import Formalism.LocalToGlobal.Divisibility.QLocTied
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTypeDimensionAndLocalIntegralsDegreeOne
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsAbsIrrCharCompIff
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.HilbertRowConditions.CenterIdempotentAction
import Formalism.LocalToGlobal.IndefiniteReal.RecTie
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle018

@[expose] public section

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct

theorem _root_.GlobalTheory.T.heckePoly_mul_centralIdempotent_mul_genericProjector : ∀ (D : D7) (S : RatDat D.ntw) (In : RatIn D S) (j k : ℕ) (P : PlE D.host), 1 ≤ j → j ≤ D.R.m → 1 ≤ k → k ≤ D.R.r →
    IsSplitPl D.host P → P ∉ In.Sb → phiLop D S In j k P * eLop D S j * piLop D S In.θ j = 0 := by
  first | exact @GlobalTheory.HeightCounting.FormsStep.phiLop_eLop_piLop | exact GlobalTheory.HeightCounting.FormsStep.phiLop_eLop_piLop | (intros; apply GlobalTheory.HeightCounting.FormsStep.phiLop_eLop_piLop <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.R3 GlobalTheory.Mem.ColTie

namespace GlobalTheory.Mem.ColTie

theorem ipK_eq_card_mul_ipLev {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
    (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)
    (P : LevFam X.E X.K R.r Pr.vGs) (hX : X.Ok) (z z' : MtildeV W Ch sel mu P) :
    ipK W Ch sel mu P hX z z' = (Nat.card P.grp : X.K) * ipLev W Ch sel mu P hX z z' := by
  have h0 : (Nat.card P.grp : X.K) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have h1 := levelSumX W Ch sel mu P (mtildeOk W Ch sel mu hX P) (mtildeKOk W Ch sel mu hX) z.1 z'.1 z.2 z'.2
  unfold ipLev ipK
  rw [h1, mul_inv_cancel_left₀ h0]

end GlobalTheory.Mem.ColTie
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2



noncomputable section

namespace GlobalTheory.Mem.R3.LiftBrg.ActQ

theorem castGL_rfl_apply' {R : Type} [CommRing R] {m : ℕ} (x : GL (Fin m) R) : castGL (rfl : m = m) x = x := by
  apply Units.ext
  ext i j
  simp [castGL]

theorem castGL_St_redFn (X : Stages) {m n : ℕ} (h : m = n) (x : GL (Fin m) (EA X)) (hx : x ∈ Formalism.L2.DIV.St 1)
    (PP : Pl X.toD7.host.E) :
    castGL h x ∈ Formalism.L2.DIV.St 1 ∧
      Formalism.L2.DIV.redFn 1 PP (castGL h x) = castGL h (Formalism.L2.DIV.redFn 1 PP x) := by
  subst h
  rw [castGL_rfl_apply', castGL_rfl_apply']
  exact ⟨hx, rfl⟩

theorem redZ_eq_castGL_redFn : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (U : Set I.ι)
    (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)), LevOf X I U L →
    ∀ (i : Fin X.toD7.R.m) (t : TupU I U) (A k : GL (Fin X.B.R.nV) (LiftBrg.EA X)), LiftBrg.FrameOK X I U i t A k →
    ∀ (κ : (levEnv (Vc X.toD7 i) (L.βV i) (L.datVt i t)).Q) (w : Formalism.L2.Col.rowSG (X.B.primes px) I.sel t.1),
      LiftBrg.ActQ.redZ X I U L i t A k κ w =
        LiftBrg.castGL (LiftBrg.rkEq X i).symm (Formalism.L2.DIV.redFn (L.βV i) w.1
          (Formalism.UG.bc (swapAE X.toD7) ((κ : Bridge.Gf (Vc X.toD7 i)) : GL (Fin (Vc X.toD7 i).rank) _))) := by
  intro X px I U L hL i t A k hF κ w
  have hAk : A * k ∈ Formalism.L2.DIV.St (1 : GL (Fin X.B.R.nV) (EA X)) := Subgroup.mul_mem _ hF.2.1 hF.2.2.2.2.1
  have hred : Formalism.L2.DIV.redFn (1 : GL (Fin X.B.R.nV) (EA X)) w.1 (A * k) = 1 := (Formalism.L2.DIV.mem_princAt.1 (hF.2.2.2.2.2 w.1 w.2)).2
  have hy := Formalism.L2.DIV.parLev_St (mem_parLev_of_Q X I U L i t κ)
  have hβ := hL.beta.1 i
  show Formalism.L2.DIV.redFn (1 : GL (Fin X.B.R.nV) (EA X)) w.1
    ((A * k)⁻¹ * castGL (rkEq X i).symm
      (Formalism.UG.bc (swapAE X.toD7) ((κ : Bridge.Gf (Vc X.toD7 i)) : GL (Fin (Vc X.toD7 i).rank) _)) * (A * k)) = _
  generalize (Formalism.UG.bc (swapAE X.toD7) ((κ : Bridge.Gf (Vc X.toD7 i)) : GL (Fin (Vc X.toD7 i).rank) _)) = y at hy ⊢
  generalize L.βV i = β at hy hβ ⊢
  subst hβ
  obtain ⟨hc, hcr⟩ := castGL_St_redFn X (rkEq X i).symm y hy w.1
  have e1 := Formalism.L2.DIV.redFn_mul (Subgroup.mul_mem _ (Subgroup.inv_mem _ hAk) hc) hAk w.1
  have e2 := Formalism.L2.DIV.redFn_mul (Subgroup.inv_mem _ hAk) hc w.1
  have e3 := Formalism.L2.DIV.redFn_inv hAk w.1
  refine e1.trans ?_
  rw [e2, e3, hred, hcr]
  simp

end GlobalTheory.Mem.R3.LiftBrg.ActQ
end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2

noncomputable section

namespace GlobalTheory.Mem.R3.LiftBrg.ActQ


theorem redQ_surjective : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (U : Set I.ι) (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)) (eG : Gc X.B px ≃* G0 L.Pg X.toD7.R.r), I.Ok → ValsIn I → LevOf X I U L → IsPlacewiseIdentity X (px := px) eG → ∀ (i : Fin X.toD7.R.m) (t : TupU I U), Function.Surjective (LiftBrg.ActQ.redQ X I U L eG i t) := by
  intro X px I U L eG _ _ hL _ i t g
  obtain ⟨c, hc⟩ := hL.is.βV i
  obtain ⟨κ, -, hpar, hr⟩ := GlobalTheory.ParahoricLift.liftsExist (Vc X.toD7 i) (L.βV i) (L.datVt i t) _ _ hc
    (GlobalTheory.StepLifts.places_apart L hL.is t).1 (GlobalTheory.StepLifts.places_apart L hL.is t).2 (eG g)
  refine ⟨⟨(finHom (Vc X.toD7 i)).rangeRestrict κ, ⟨hpar, Subgroup.mem_top _⟩⟩, ?_⟩
  rw [redQ_apply]
  show eG.symm (rTup (L.βV i) (L.datVt i t) (finE (Vc X.toD7 i) κ)) = g
  rw [hr, MulEquiv.symm_apply_apply]

end GlobalTheory.Mem.R3.LiftBrg.ActQ
end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2



noncomputable section

namespace GlobalTheory.Mem.R3.LiftBrg.ActQ

theorem castGL_castGL_symm {R : Type} [CommRing R] {a b : ℕ} (h : a = b) (m : GL (Fin b) R) :
    castGL h (castGL h.symm m) = m := by
  subst h
  ext i j
  simp [castGL]

theorem castGL_mem_St_one {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {a b : ℕ} (h : a = b) (m : GL (Fin a) (E ⊗[F] Formalism.L2.Herm.Af F)) (hm : m ∈ Formalism.L2.DIV.St 1) :
    castGL h m ∈ Formalism.L2.DIV.St 1 := by
  subst h
  have e : castGL (rfl : a = a) m = m := by
    ext i j
    simp [castGL]
  rwa [e]

theorem ptS_mul_Q : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (U : Set I.ι) (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)), I.Ok → ValsIn I → LevOf X I U L → ∀ (i : Fin X.toD7.R.m) (t : TupU I U) (A k : GL (Fin X.B.R.nV) (LiftBrg.EA X)), LiftBrg.FrameOK X I U i t A k →
    ∀ (κ : (levEnv (Vc X.toD7 i) (L.βV i) (L.datVt i t)).Q) (x : Bridge.Gf (Vc X.toD7 i)),
      LiftBrg.ActQ.ptS X I U i t A k (x * κ) =
        ((1 : Formalism.L2.Col.UF X.B.fields.E X.B.R.nV), (LiftBrg.ActQ.redZ X I U L i t A k κ)⁻¹) • LiftBrg.ActQ.ptS X I U i t A k x := by
  intro X px I U L _ _ hL i t A k hF κ x
  obtain ⟨-, hASt, hAU, hkU, hkSt, -⟩ := hF
  set w : Bridge.Gf (Vc X.toD7 i) → GL (Fin X.B.R.nV) (EA X) := fun g =>
    castGL (rkEq X i).symm (Formalism.UG.bc (swapAE X.toD7) (g : GL (Fin (Vc X.toD7 i).rank) _)) with hw
  have hwmul : w (x * κ) = w x * w κ := by
    simp only [hw, Subgroup.coe_mul, map_mul]

  have hconj : ∀ g : GL (Fin (Vc X.toD7 i).rank) (EA X), g ∈ Formalism.L2.DIV.UA X.toD7.sp.cm (Vc X.toD7 i).gram →
      A⁻¹ * castGL (rkEq X i).symm g * A ∈ Formalism.L2.Col.UAd X.toD7.sp.cm X.B.R.nV := by
    intro g hg
    refine (hAU _).2 ?_
    have e : A * (A⁻¹ * castGL (rkEq X i).symm g * A) * A⁻¹ = castGL (rkEq X i).symm g := by group
    rw [e, castGL_castGL_symm]
    exact hg
  have hxU : Formalism.UG.bc (swapAE X.toD7) ((x : Bridge.Gf (Vc X.toD7 i)) : GL (Fin (Vc X.toD7 i).rank) _) ∈
      Formalism.L2.DIV.UA X.toD7.sp.cm (Vc X.toD7 i).gram := by
    obtain ⟨g, hg⟩ := x.2
    rw [← hg]
    exact GlobalTheory.LevFinCong.finE_mem_UA _ g
  have hκP := mem_parLev_of_Q X I U L i t κ
  have hκU := Formalism.L2.DIV.parLev_UA hκP
  have hκS : Formalism.UG.bc (swapAE X.toD7) ((κ : Bridge.Gf (Vc X.toD7 i)) : GL (Fin (Vc X.toD7 i).rank) _) ∈
      Formalism.L2.DIV.St (1 : GL (Fin (Vc X.toD7 i).rank) (EA X)) := by
    have h0 := Formalism.L2.DIV.parLev_St hκP
    have hb : L.βV i = 1 := hL.beta.1 i
    exact hb ▸ h0
  set y := A⁻¹ * w x * A * k with hy
  set z := (A * k)⁻¹ * w κ * (A * k) with hz
  have hyU : y ∈ Formalism.L2.Col.UAd X.toD7.sp.cm X.B.R.nV := mul_mem (hconj _ hxU) hkU
  have hzU : z ∈ Formalism.L2.Col.UAd X.toD7.sp.cm X.B.R.nV := by
    have e : z = k⁻¹ * (A⁻¹ * w κ * A) * k := by rw [hz]; group
    rw [e]
    exact mul_mem (mul_mem (inv_mem hkU) (hconj _ hκU)) hkU
  have hzS : z ∈ Formalism.L2.DIV.St (1 : GL (Fin X.B.R.nV) (EA X)) := by
    have hwS : w κ ∈ Formalism.L2.DIV.St (1 : GL (Fin X.B.R.nV) (EA X)) := castGL_mem_St_one _ _ hκS
    have hAk := mul_mem hASt hkSt
    exact mul_mem (mul_mem (inv_mem hAk) hwS) hAk
  have hzJ : z ∈ Formalism.L2.Col.J0 X.toD7.sp.cm X.B.R.nV (∅ : Finset (Pl X.toD7.host.E)) :=
    ⟨⟨hzU, hzS⟩, Subgroup.mem_iInf.2 fun P => Subgroup.mem_iInf.2 fun hP => absurd hP (Finset.notMem_empty _)⟩
  have hyz : A⁻¹ * w (x * κ) * A * k = y * z := by
    rw [hwmul, hy, hz]; group
  have hyzU : y * z ∈ Formalism.L2.Col.UAd X.toD7.sp.cm X.B.R.nV := mul_mem hyU hzU
  have hred : Formalism.L2.Col.redG X.toD7.sp.cm X.B.R.nV ∅ (sgL X I U t) ⟨z, hzJ⟩ = redZ X I U L i t A k κ := by
    funext v
    show _ = Formalism.L2.DIV.redFn (1 : GL (Fin X.B.R.nV) (EA X)) v.1 z
    unfold Formalism.L2.DIV.redFn
    rw [Formalism.L2.DIV.extendOne_of_mem _ hzS]
    rfl
  have hraw := GlobalTheory.Mem.Col2.TopCh.decoRaw_mul_levelIwahori_reduction X.toD7.sp.cm ∅ (sgL X I U t) y z hzJ
  rw [hred] at hraw
  apply Subtype.ext
  show (Formalism.L2.Col.decoOf ∅ (sgL X I U t) (A⁻¹ * w (x * κ) * A * k)).1 =
    (Formalism.L2.Col.decoOf ∅ (sgL X I U t) y).1.act 1 (redZ X I U L i t A k κ)⁻¹
  rw [hyz]
  unfold Formalism.L2.Col.decoOf
  rw [dite_eq_left (Formalism.L2.Col.decorated_lattice_exists X.toD7.sp.cm X.B.R.nV ∅ (sgL X I U t) _ hyzU),
    dite_eq_left (Formalism.L2.Col.decorated_lattice_exists X.toD7.sp.cm X.B.R.nV ∅ (sgL X I U t) _ hyU)]
  exact hraw

end GlobalTheory.Mem.R3.LiftBrg.ActQ
end
end

section

open Matrix NumberField MeasureTheory Formalism.DegreeFormula Formalism.MJ Formalism.UG Formalism.L2.Geo
open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.HodgeDomain GlobalTheory.TrueCx GlobalTheory.FlagFibre
open scoped ComplexOrder ENNReal

theorem _root_.GlobalTheory.T.leadingMinorFlagDensity_glueLowerUnitriangular : ∀ (r p q : ℕ) (e : Fin r ≃ Fin p ⊕ Fin q), IsBlockSL2Embedding e → ∀ (A : Matrix (Fin r) (Fin r) ℂ) (w : (Fin p × Fin q → ℂ) × (Low q → ℂ) × (Low p → ℂ)), IsUnit (shear (reindex e e A) (toMat w.1)).toBlocks₂₂.det → dens A (glue e w) = dens (shear (reindex e e A) (toMat w.1)).toBlocks₂₂ w.2.1 * ‖(shear (reindex e e A) (toMat w.1)).toBlocks₂₂.det‖ ^ (-(2 * p : ℤ)) * dens (schur (shear (reindex e e A) (toMat w.1))) w.2.2 := by
  first | exact @GlobalTheory.FlagFibre.dens_glue | exact GlobalTheory.FlagFibre.dens_glue | (intros; apply GlobalTheory.FlagFibre.dens_glue <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.HAt Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.HAt.FvOff
open Formalism.L2.GlobalTheoryTheory.LocalLatticeBases



theorem fT_move {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))}
    (S : StepLevel F E σ J T f bad) (w : HeightOneSpectrum (𝓞 F)) (hw : (T : 𝓞 F) ∈ w.asIdeal)
    (y y' η κ : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (γ : GL (Fin n) E)
    (hκ : κ ∈ S.U) (hη : bc (prV (E := E) w) η = 1)
    (he : bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ * y' = y * η * κ) (z' : Fin n → E)
    (hx : ((bc (prV (E := E) w) y)⁻¹).1 *ᵥ (fun a => inclE (F := F) (w.adicCompletion F) ((γ.1 *ᵥ z') a)) ∈
      latS (F := F) (w.adicCompletion F) (intV E w) (Submodule.span (𝓞 E) (dualSet (σ : E →+* E) J S.Lb)))
    (hx' : ((bc (prV (E := E) w) y')⁻¹).1 *ᵥ (fun a => inclE (F := F) (w.adicCompletion F) (z' a)) ∈
      latS (F := F) (w.adicCompletion F) (intV E w) (Submodule.span (𝓞 E) (dualSet (σ : E →+* E) J S.Lb))) :
    S.fT w hw ⟨_, hx'⟩ = S.fT w hw ⟨_, hx⟩ := by
  have hk : y⁻¹ * bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ * y' = η * κ := by
    rw [mul_assoc, he]; group
  have hkw : bc (prV (E := E) w) (y⁻¹ * bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ * y') =
      bc (prV (E := E) w) κ := by
    rw [hk, map_mul, hη, one_mul]
  have hm := GlobalTheory.LevelHecke.MovePair.mov_mulVec w y y' γ z'
  rw [hkw] at hm
  have hloc : bc (prV (E := E) w) κ ∈ S.Uloc w := ((S.U_eq κ).1 hκ).2 w
  rw [S.UlocAlt w hw] at hloc
  obtain ⟨hg, hf⟩ := (Subgroup.mem_inf.1 hloc).2
  rw [← hf ⟨_, hx'⟩]
  congr 1
  exact Subtype.ext hm



theorem fT_adStep {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))}
    (S : StepLevel F E σ J T f bad) (w w' : HeightOneSpectrum (𝓞 F)) (hw : (T : 𝓞 F) ∈ w'.asIdeal) (hne : w' ≠ w)
    (y y' : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (γ : GL (Fin n) E)
    (hA : Formalism.L2.Herm.AdStep σ J S.U y y' γ w) (z z' : Fin n → E) (hz : z = γ.1 *ᵥ z')
    (hx : ((bc (prV (E := E) w') y)⁻¹).1 *ᵥ (fun a => inclE (F := F) (w'.adicCompletion F) (z a)) ∈
      latS (F := F) (w'.adicCompletion F) (intV E w') (Submodule.span (𝓞 E) (dualSet (σ : E →+* E) J S.Lb)))
    (hx' : ((bc (prV (E := E) w') y')⁻¹).1 *ᵥ (fun a => inclE (F := F) (w'.adicCompletion F) (z' a)) ∈
      latS (F := F) (w'.adicCompletion F) (intV E w') (Submodule.span (𝓞 E) (dualSet (σ : E →+* E) J S.Lb))) :
    S.fT w' hw ⟨_, hx'⟩ = S.fT w' hw ⟨_, hx⟩ := by
  obtain ⟨κ, hκ, η, -, hη, he⟩ := hA
  subst hz
  exact fT_move S w' hw y y' η κ γ hκ (hη _ hne) he z' hx hx'




theorem ld_loc_ch {D : D7} {u : D.what₂.Word} {i : ℕ} {hi : i ≤ D.R.m} {cl : Type} {stab : cl → Type} [∀ c, Group (stab c)]
    {cc : cl → (D.mem u).C.cls i}
    (K : LevelChart D (D.mem u).A.T (badG D) i hi stab (fun c => clsCrd D u i hi (cc c)))
    (v : HeightOneSpectrum (𝓞 D.host.F)) (c : cl)
    (x : Fin (D.R.N i) → D.host.E ⊗[D.host.F] v.adicCompletion D.host.F) :
    x ∈ latS (F := D.host.F) (v.adicCompletion D.host.F) (intV D.host.E v) (Ld D u i hi (cc c)) ↔
      ((bc (prV (E := D.host.E) v) (K.y c).1)⁻¹).1 *ᵥ x ∈
        latS (F := D.host.F) (v.adicCompletion D.host.F) (intV D.host.E v)
          (Submodule.span (𝓞 D.host.E) (dualSet (sigD D : D.host.E →+* D.host.E) (gramN D i hi) K.lev.Lb)) := by
  let φ := (D.sp.X i).frame.equivFun.trans
    (LinearEquiv.funCongrLeft D.host.E D.host.E (finCongr (rankN D i hi)).symm)
  letI : Submodule.IsLattice D.host.E (clsCrd D u i hi (cc c)) := bwB_clsCrd_lat D u i hi (cc c)
  have hL : Submodule.IsFullLattice D.host.E (clsCrd D u i hi (cc c)) := by
    constructor
    change Submodule.span D.host.E (((D.clsLat u i (cc c)).map
      (φ.toLinearMap.restrictScalars (𝓞 D.host.E)) : Submodule (𝓞 D.host.E) (Fin (D.R.N i) → D.host.E)) : Set (Fin (D.R.N i) → D.host.E)) = ⊤
    rw [show Submodule.span D.host.E (((D.clsLat u i (cc c)).map
        (φ.toLinearMap.restrictScalars (𝓞 D.host.E)) : Submodule (𝓞 D.host.E) (Fin (D.R.N i) → D.host.E)) : Set (Fin (D.R.N i) → D.host.E)) =
        (Submodule.span D.host.E (D.clsLat u i (cc c) : Set _)).map φ.toLinearMap by
          rw [Submodule.map_span]; rfl,
      (D.clsLat_lat u i (cc c)).span_eq_top, Submodule.map_top, LinearMap.range_eq_top]
    exact φ.surjective
  letI : Submodule.IsLattice D.host.E K.lev.Lb :=
    Submodule.IsLattice.of_fg D.host.E (Module.Finite.iff_fg.1 K.lev.Lb_fin)
  have hLb : Submodule.IsFullLattice D.host.E K.lev.Lb := ⟨K.lev.Lb_span⟩
  refine GlobalTheory.DualCompletion.dual_move D.host.F D.host.E (sigD D) _ (gramN D i hi) v (clsCrd D u i hi (cc c)) K.lev.Lb
    (bc (prV (E := D.host.E) v) (K.y c).1) (bwB_gramN_det D i hi) hL hLb
    (Formalism.UG.P.afsplit_bc_mem _ _ _ _ (K.y c).2) (fun x => ?_) x
  rw [← map_inv]
  exact rlv_yloc v (K.y c).1 (K.y_lat c) x




theorem ld_in {D : D7} {u : D.what₂.Word} {i : ℕ} {hi : i ≤ D.R.m} {cl : Type} {stab : cl → Type} [∀ c, Group (stab c)]
    {cc : cl → (D.mem u).C.cls i}
    (K : LevelChart D (D.mem u).A.T (badG D) i hi stab (fun c => clsCrd D u i hi (cc c)))
    (v : HeightOneSpectrum (𝓞 D.host.F)) (c : cl) (z : Fin (D.R.N i) → D.host.E) (hz : z ∈ Ld D u i hi (cc c)) :
      ((bc (prV (E := D.host.E) v) (K.y c).1)⁻¹).1 *ᵥ (fun a => inclE (F := D.host.F) (v.adicCompletion D.host.F) (z a)) ∈
        latS (F := D.host.F) (v.adicCompletion D.host.F) (intV D.host.E v)
          (Submodule.span (𝓞 D.host.E) (dualSet (sigD D : D.host.E →+* D.host.E) (gramN D i hi) K.lev.Lb)) :=
  (ld_loc_ch K v c _).1 (Submodule.subset_span ⟨z, hz, rfl⟩)




theorem fv_off_cls {D : D7} {u : D.what₂.Word} {A : AtTTied u} {i : ℕ} {hi : i ≤ D.R.m} (P : LvTied u A i hi)
    (K : ClsTied u i hi) (fMe : ∀ v, K.lev.fM (A.eV v).1 (A.eV v).2 ≃+ (D.mem u).A.Fv v) (hT : FvTie P K fMe)
    (v v' : (D.mem u).A.vT) (c c' : (D.mem u).C.cls i) (γ : GL (Fin (D.R.N i)) D.host.E)
    (hA : Formalism.L2.Herm.AdStep (sigD D) (gramN D i hi) K.lev.U (K.y c).1 (K.y c').1 γ (A.eV v).1) (hv : v' ≠ v)
    (z : Ld D u i hi c) (z' : Ld D u i hi c') (hz : z.1 = γ.1 *ᵥ z'.1) :
    (D.fm u).fv i v' c' (P.pr v' c' z') = (D.fm u).fv i v' c (P.pr v' c z) := by
  have hw : (A.eV v').1 ≠ (A.eV v).1 := fun h => hv (A.eV.injective (Subtype.ext h))
  have hx := ld_in (cc := fun c => c) K.toChart (A.eV v').1 c z.1 z.2
  have hx' := ld_in (cc := fun c => c) K.toChart (A.eV v').1 c' z'.1 z'.2
  have e := fT_adStep K.lev (A.eV v).1 (A.eV v').1 (A.eV v').2 hw (K.y c).1 (K.y c').1 γ hA z.1 z'.1 hz hx hx'
  exact (hT v' c' z' hx').trans ((congrArg (fMe v') e).trans (hT v' c z hx).symm)




theorem fv_off_ch {D : D7} {u : D.what₂.Word} {i : ℕ} {hi : i ≤ D.R.m} {Ch : Type} {chOf : (D.mem u).C.cls i → Ch}
    {res : ∀ v, 𝓞 D.host.E →+* (D.mem u).A.Fv v}
    (L : LevelCompatibleLattices (D.fm u) (D.mem u).A.T res i hi (fun c => clsCrd D u i hi c))
    (eV : (D.mem u).A.vT ≃ {v : HeightOneSpectrum (𝓞 D.host.F) // (((D.mem u).A.T : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal})
    (K : ∀ β : Ch, LevelChart D (D.mem u).A.T (badG D) i hi (fun c : {c // chOf c = β} => (D.mem u).C.stab i c.1)
      (fun c => clsCrd D u i hi c.1))
    (fMe : ∀ β v, (K β).lev.fM (eV v).1 (eV v).2 ≃+ (D.mem u).A.Fv v) (hT : FvTieG L eV K fMe)
    (v v' : (D.mem u).A.vT) (c c' : (D.mem u).C.cls i) (hβ : chOf c' = chOf c) (γ : GL (Fin (D.R.N i)) D.host.E)
    (hA : Formalism.L2.Herm.AdStep (sigD D) (gramN D i hi) (K (chOf c)).lev.U ((K (chOf c)).y ⟨c, rfl⟩).1
      ((K (chOf c)).y ⟨c', hβ⟩).1 γ (eV v).1) (hv : v' ≠ v)
    (z : LdG D i hi (clsCrd D u i hi c)) (z' : LdG D i hi (clsCrd D u i hi c')) (hz : z.1 = γ.1 *ᵥ z'.1) :
    (D.fm u).fv i v' c' (L.pr v' c' z') = (D.fm u).fv i v' c (L.pr v' c z) := by
  have hw : (eV v').1 ≠ (eV v).1 := fun h => hv (eV.injective (Subtype.ext h))
  have hx := ld_in (cc := fun c : {c' // chOf c' = chOf c} => c.1) (K (chOf c)) (eV v').1 ⟨c, rfl⟩ z.1 z.2
  have hx' := ld_in (cc := fun c : {c' // chOf c' = chOf c} => c.1) (K (chOf c)) (eV v').1 ⟨c', hβ⟩ z'.1 z'.2
  have e := fT_adStep (K (chOf c)).lev (eV v).1 (eV v').1 (eV v').2 hw _ _ γ hA z.1 z'.1 hz hx hx'
  exact (hT v' (chOf c) ⟨c', hβ⟩ z' hx').trans ((congrArg (fMe (chOf c) v') e).trans (hT v' (chOf c) ⟨c, rfl⟩ z hx).symm)




theorem fv_eq_of_adC : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (H : Formalism.L2.Herm.HermColsCh (I.rec7 l Z)) (F : ∀ u, FormsTiedSym (I.rec7 l Z) u (H.Ch u) (H.chOf u)), (∀ u, I.StdF l Z u (F u) ∧ I.StdLvC l Z u (F u)) → CarH H F → ∀ u i (hi : i ≤ (I.rec7 l Z).R.m) v v' (c c' : ((I.rec7 l Z).mem u).C.cls i) (γ : GL (Fin ((I.rec7 l Z).R.N i)) (I.rec7 l Z).host.E), AdC (F u) i hi c c' γ ((F u).atT.eV v).1 → v' ≠ v → ∀ (z : Formalism.L2.Forms.Ld (I.rec7 l Z) u i hi c) (z' : Formalism.L2.Forms.Ld (I.rec7 l Z) u i hi c'), z.1 = γ.1 *ᵥ z'.1 → ((I.rec7 l Z).fm u).fv i v' c' (((F u).lv i hi).pr v' c' z') = ((I.rec7 l Z).fm u).fv i v' c (((F u).lv i hi).pr v' c z) := by
  intro B X I hI hP l Z H F hF hC u i hi v v' c c' γ hA hv z z' hz
  by_cases h : i = 0 ∨ i = (I.rec7 l Z).R.m
  · exact fv_off_cls ((F u).lv i hi) ((F u).cls i hi h) ((F u).fMe i hi h) ((F u).fv i hi h) v v' c c' γ (hA.1 h) hv z z' hz
  · have h1 : 1 ≤ i := by omega
    have h2 : i + 1 ≤ (I.rec7 l Z).R.m := by omega
    obtain ⟨hβ, hA'⟩ := hA.2 h1 h2
    have e := fv_off_ch ((F u).lvC i h1 h2) (F u).atT.eV ((F u).ch i h1 h2) ((F u).fMeC i h1 h2) ((F u).fvC i h1 h2)
      v v' c c' hβ γ hA' hv z z' hz
    have e1 := (pr_lvC_eq_lv I hI hP l Z H F hF hC u i h1 h2 v' c).1 z z rfl
    have e2 := (pr_lvC_eq_lv I hI hP l Z H F hF hC u i h1 h2 v' c').1 z' z' rfl
    exact (congrArg _ e2).symm.trans (e.trans (congrArg _ e1))

end GlobalTheory.Mem.Col2.HAt.FvOff
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2

theorem _root_.GlobalTheory.T.identity_integralUnitaryFrameCoordinates_of_unitGram : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (U : Set I.ι) (i : Fin X.toD7.R.m) (t : TupU I U), (Vc X.toD7 i).gram = 1 → LiftBrg.FrameOK X I U i t 1 1 := by
  first | exact @GlobalTheory.Mem.R3.LiftBrg.frameOK_one_of_gram_eq_one | exact GlobalTheory.Mem.R3.LiftBrg.frameOK_one_of_gram_eq_one | (intros; apply GlobalTheory.Mem.R3.LiftBrg.frameOK_one_of_gram_eq_one <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2

theorem _root_.GlobalTheory.T.levelCharacter_inv_mul_diagEmbedding_eq_char_det : ∀ {κ K : Type} [CommRing κ] [Field K] {a n r t : ℕ} (h : a = n) (hn : n = r + t) (hra : r ≤ a)
    (hrn : r ≤ n) (y : GL (Fin a) κ) (hy : y ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blkOf r t)) (χ : κˣ →* Kˣ)
    (hz : (LiftBrg.castGL h y)⁻¹ * Formalism.L2.Col.diagEmb κ hrn (Formalism.L2.DIV.upperLeftBlock hra y) ∈ Formalism.L2.Col.HKV κ n r t),
    Formalism.L2.Col.lamKV χ n r t ⟨_, hz⟩ = χ (Formalism.L2.DIV.dBlk (Formalism.L2.DIV.blkOf r t) 1 y) := by
  first | exact @GlobalTheory.Mem.R3.LiftBrg.LamKV.lamKV_inv_mul_diagEmb | exact GlobalTheory.Mem.R3.LiftBrg.LamKV.lamKV_inv_mul_diagEmb | (intros; apply GlobalTheory.Mem.R3.LiftBrg.LamKV.lamKV_inv_mul_diagEmb <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2

theorem _root_.GlobalTheory.T.upperParahoric_character_inv_eq_inv_det_block : ∀ {κ K : Type} [CommRing κ] [Field K] {a n r b : ℕ} (h : a = n) (hn : n = r + b) (y : GL (Fin a) κ)
    (hy : y ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blk2 r)) (χ : κˣ →* Kˣ)
    (hz : (LiftBrg.castGL h y)⁻¹ * 1 ∈ Formalism.L2.Col.HQ κ n r b),
    Formalism.L2.Col.lamQ χ n r b ⟨_, hz⟩ = (χ (Formalism.L2.DIV.dBlk (Formalism.L2.DIV.blk2 r) 1 y))⁻¹ := by
  first | exact @GlobalTheory.Mem.R3.LiftBrg.LamQInv.lamQ_castGL_inv | exact GlobalTheory.Mem.R3.LiftBrg.LamQInv.lamQ_castGL_inv | (intros; apply GlobalTheory.Mem.R3.LiftBrg.LamQInv.lamQ_castGL_inv <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2
open GlobalTheory.Mem.R3.LiftBrg

theorem _root_.GlobalTheory.T.finiteAdelicUnitary_conj_integralFrame : ∀ (X : Stages) {px : PreX X.B.toPre} (I : Col2.ColIn X.B px) (hX : X.B.fields.Ok) (U : Set I.ι) (Xg : Finset (Gc X.B px → X.B.LL)) (tr : TrI X.B px) (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)) (i : Fin X.toD7.R.m) (t : TupU I U) (A k : GL (Fin X.B.R.nV) (EA X)) (hF : FrameOK X I U i t A k),
    ∃ Φ : Formalism.L2.Col.UAd X.toD7.sp.cm X.B.R.nV ≃* Bridge.Gf (Vc X.toD7 i), ∀ u,
      castGL (rkEq X i).symm (Formalism.UG.bc (swapAE X.toD7) ((Φ u : Bridge.Gf (Vc X.toD7 i)) : GL (Fin (Vc X.toD7 i).rank) _)) = A * k * (u : GL (Fin X.B.R.nV) (EA X)) * (A * k)⁻¹ := by
  first | exact @GlobalTheory.Mem.R3.LiftBrg.FrameEquiv.frame_equiv | exact GlobalTheory.Mem.R3.LiftBrg.FrameEquiv.frame_equiv | (intros; apply GlobalTheory.Mem.R3.LiftBrg.FrameEquiv.frame_equiv <;> assumption)
end

section

open MeasureTheory Matrix NumberField IsDedekindDomain Formalism.BasicNotions Formalism.DoubleCosetMeasures Formalism.L2.Host Formalism.L2.DIV Formalism.L2.DIV.QLoc GlobalTheory.Mem.HD

theorem _root_.GlobalTheory.T.exists_type_dimension_and_local_integrals_degree_one : ∀ (L : Type) [Field L] [NumberField L] (P : HeightOneSpectrum (𝓞 L)), Deg1 P → ∀ (δ : (P.adicCompletion L)ˣ →* ℂˣ) (ν : ℕ → (P.adicCompletion L)ˣ →* ℂˣ), IsDel P δ → (∀ i, IsNu P (ν i)) → ∀ r t j : ℕ, 1 ≤ t → (∃ n, TypeDimAt P δ ν r t j n) ∧ ∃ z, StepAt P δ ν r t j z := by
  first | exact @GlobalTheory.TypeStep.exists_typeDim_step | exact GlobalTheory.TypeStep.exists_typeDim_step | (intros; apply GlobalTheory.TypeStep.exists_typeDim_step <;> assumption)
end
