module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MidChart
public import Formalism.LocalToGlobal.Columns.StdLatUnimodular
public import Formalism.LocalToGlobal.Columns.AdelicLemmas
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsGlob
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RecHeightSWith
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BesselCharacterGenericCharacterLaws
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.HidaSetting
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle114
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsFlagUnipotentRealPlaceIffFrameUnipotentRadical
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle065
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle064
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle103
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle113
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle152
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle006
public import ReciprocityTheory.NeutralLocalFields.Bundle001
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HilbertClassFieldOfGlobalArtinReciprocity
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Rat
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
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsDiscriminantTwelfthRootOfIdealLatticeIffDelta1
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle003
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle004
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1016

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.AdForm.RdLaw

variable {D : D7}

theorem finM_rfl (V : HSp D) (g : GA D V) : finM V rfl g = (Formalism.L2.Theta.mt V g).map (toEAf D) := by
  simp [finM]

theorem infM_eq (θ : InfFam D) (V : HSp D) (g : GA D V) (τ : D.what₂.Tau) :
    infM θ V rfl g τ = (Formalism.L2.Theta.mt V g).map ((θ τ).comp (infPart D)) := by
  simp [infM, Formalism.IndefR.Datum.compAt]; rfl

theorem infM_rfl (θ : InfFam D) (V : HSp D) (g : GA D V) (τ : D.what₂.Tau) :
    infM θ V rfl g τ = infMat D.sp.cm.sig V.gram (θ τ) g := by
  rw [infM_eq]; rfl

theorem mt_mul (V : HSp D) (g h : GA D V) : Formalism.L2.Theta.mt V (g * h) = Formalism.L2.Theta.mt V g * Formalism.L2.Theta.mt V h := by
  simp [Formalism.L2.Theta.mt, map_mul]

theorem finM_mul (V : HSp D) (g h : GA D V) : finM V rfl (g * h) = finM V rfl g * finM V rfl h := by
  simp only [finM_rfl, mt_mul, Matrix.map_mul]

theorem infM_mul (θ : InfFam D) (V : HSp D) (g h : GA D V) (τ) :
    infM θ V rfl (g * h) τ = infM θ V rfl g τ * infM θ V rfl h τ := by
  simp only [infM_eq, mt_mul, Matrix.map_mul]

theorem infM_fin (θ : InfFam D) (V : HSp D) (k : GA D V) (hk : k ∈ GfC V) (τ) : infM θ V rfl k τ = 1 := by
  have h : (infHom V k) = 1 := hk
  have h2 : (infHom V k).val = 1 := by rw [h]; rfl
  rw [infM_eq]
  have e : (Formalism.L2.Theta.mt V k).map ((θ τ).comp (infPart D)) = (infHom V k).val.map (θ τ) := rfl
  rw [e, h2, Matrix.map_one _ (map_zero _) (map_one _)]

theorem finM_inf (V : HSp D) (k : GA D V) (hk : k ∈ GinfC V) : finM V rfl k = 1 := by
  have h : (finHom V k) = 1 := hk
  have h2 : (finHom V k).val = 1 := by rw [h]; rfl
  rw [finM_rfl]
  have e : (Formalism.L2.Theta.mt V k).map (toEAf D) = (finHom V k).val.map
      (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E) := rfl
  rw [e, h2, Matrix.map_one _ (map_zero _) (map_one _)]

end GlobalTheory.AdForm.RdLaw

noncomputable section
namespace GlobalTheory.AdForm.RdLaw
variable {D : D7}

theorem rat_mt (V : HSp D) (γ : GA D V) (hγ : γ ∈ GQ V) :
    ∃ γ0 : GL (Fin V.rank) D.host.E, γ0 ∈ UJ (D.sp.cm.sig : D.host.E →+* D.host.E) V.gram ∧
      Formalism.L2.Theta.mt V γ = γ0.val.map (incA D) := by
  have h : matHom V γ ∈ HFin (AF D.host.F) D.sp.cm.sig V.gram := hγ
  obtain ⟨γ0, h0, e⟩ := Subgroup.mem_map.1 h
  refine ⟨γ0, h0, ?_⟩
  show (matHom V γ).val = _
  rw [← e]; rfl

theorem rat_finM (V : HSp D) (γ0 : GL (Fin V.rank) D.host.E) (γ : GA D V) (e : Formalism.L2.Theta.mt V γ = γ0.val.map (incA D)) :
    finM V rfl γ = (bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ0).val := by
  rw [finM_rfl, e, Matrix.map_map]; rfl

theorem rat_infM (θ : InfFam D) (hθ : IsInfFam θ) (V : HSp D) (γ0 : GL (Fin V.rank) D.host.E) (γ : GA D V)
    (e : Formalism.L2.Theta.mt V γ = γ0.val.map (incA D)) (τ) :
    infM θ V rfl γ τ = atInf (embT D) γ0.val τ := by
  rw [infM_eq, e, Matrix.map_map]
  ext i j
  simp only [Matrix.map_apply, atInf, Function.comp_apply, RingHom.coe_comp]
  exact (hθ τ).1 _

end GlobalTheory.AdForm.RdLaw

noncomputable section
namespace GlobalTheory.AdForm.RdLaw
variable {D : D7}

def e0 (D : D7) : AF D.host.F := ((0, 1) : Ainf D.host.F × Af D.host.F)

theorem finiteAdeleIdempotentOfF_mul_self : e0 D * e0 D = e0 D := Prod.ext (zero_mul _) (one_mul _)

def eps (D : D7) : AE D := e0 D ⊗ₜ[D.host.F] (1 : D.host.E)

theorem eps_mul_self : eps D * eps D = eps D := by
  rw [eps, Algebra.TensorProduct.tmul_mul_tmul, mul_one, finiteAdeleIdempotentOfF_mul_self]

theorem eps_mul_one_sub : eps D * (1 - eps D) = 0 := by
  rw [mul_sub, mul_one, eps_mul_self, sub_self]

theorem one_sub_mul_self : (1 - eps D) * (1 - eps D) = 1 - eps D := by
  rw [sub_mul, one_mul, mul_sub, mul_one, eps_mul_self]; abel

theorem sig_eps : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF D.host.F) D.sp.cm.sig (eps D) = eps D := by
  show Algebra.TensorProduct.map (AlgHom.id _ _) D.sp.cm.sig (_ ⊗ₜ _) = _
  rw [Algebra.TensorProduct.map_tmul, map_one]; rfl


theorem infPart_eps : infPart D (eps D) = 0 := by
  have h1 : infPart D (eps D) = fstA D.host.F (e0 D) ⊗ₜ[D.host.F] (AlgHom.id D.host.F D.host.E 1) :=
    Algebra.TensorProduct.map_tmul _ _ _ _
  have : fstA D.host.F (e0 D) = 0 := rfl
  rw [h1, this, TensorProduct.zero_tmul]


theorem finPart_eps : finPart D (eps D) = 1 := by
  have h1 : finPart D (eps D) = sndA D.host.F (e0 D) ⊗ₜ[D.host.F] (AlgHom.id D.host.F D.host.E 1) :=
    Algebra.TensorProduct.map_tmul _ _ _ _
  have : sndA D.host.F (e0 D) = 1 := rfl
  rw [h1, this]; rfl

theorem toEAf_eps : toEAf D (eps D) = 1 := by
  show (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E) (finPart D (eps D)) = 1
  rw [finPart_eps, map_one]

def PM {r : ℕ} (M : Matrix (Fin r) (Fin r) (AE D)) : Matrix (Fin r) (Fin r) (AE D) :=
  eps D • M + (1 - eps D) • (1 : Matrix (Fin r) (Fin r) (AE D))

theorem PM_mul {r : ℕ} (M N : Matrix (Fin r) (Fin r) (AE D)) : PM (M * N) = PM M * PM N := by
  simp only [PM, add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.one_mul, Matrix.mul_one,
    eps_mul_self, one_sub_mul_self, eps_mul_one_sub, mul_comm (1 - eps D) (eps D), zero_smul, add_zero, zero_add]

theorem PM_one {r : ℕ} : PM (1 : Matrix (Fin r) (Fin r) (AE D)) = 1 := by
  simp only [PM, ← add_smul, add_sub_cancel, one_smul]

end GlobalTheory.AdForm.RdLaw
end
end
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RepLattice

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] {n : ℕ}

theorem mem_iff_of_carries (y k : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (N : Submodule (𝓞 E) (Fin n → E))
    (hN : Submodule.IsFullLattice E N) (h1 : Formalism.L2.Herm.Carries (y * k) (Formalism.L2.Col.stdLat E n) N)
    (h2 : Formalism.L2.Herm.Carries k (Formalism.L2.Col.stdLat E n) (Formalism.L2.Col.stdLat E n)) (x : Fin n → E) :
    x ∈ N ↔ ∀ i, (((y⁻¹ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) _) *ᵥ
      fun j => Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F) (x j)) i ∈ Formalism.L2.Herm.intAf F E := by
  have hone := Formalism.UG.P.global_lattice_one_holds F E (Fin n) N (Module.Finite.iff_fg.mpr hN.fg) hN.span_eq_top
  have e0 : x ∈ N ↔ (fun j => Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F) (x j)) ∈ Formalism.L2.Herm.hatL (F := F) N := by
    conv_lhs => rw [← hone]
    show (((1 : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))⁻¹ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) *ᵥ (fun i => Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F) (x i)) ∈ Formalism.L2.Herm.hatL (F := F) N ↔ _
    rw [inv_one, Units.val_one, Matrix.one_mulVec]
  rw [e0, h1, _root_.mul_inv_rev, Units.val_mul, ← Matrix.mulVec_mulVec, ← h2]
  exact Formalism.L2.Col.mem_latS_std _

theorem finM_mul' {D : D7} (V : HSp D) {m : ℕ} (hn : V.rank = m) (g h : GA D V) :
    finM V hn (g * h) = finM V hn g * finM V hn h := by
  subst hn
  change (Formalism.L2.Theta.mt V (g * h)).map (toEAf D) = (Formalism.L2.Theta.mt V g).map (toEAf D) * (Formalism.L2.Theta.mt V h).map (toEAf D)
  rw [← Matrix.map_mul]
  congr 1

theorem finM_one' {D : D7} (V : HSp D) {m : ℕ} (hn : V.rank = m) : finM V hn 1 = 1 := by
  subst hn
  change (Formalism.L2.Theta.mt V 1).map (toEAf D) = 1
  have e : Formalism.L2.Theta.mt V 1 = 1 := by
    unfold Formalism.L2.Theta.mt
    rw [map_one]
    rfl
  rw [e, Matrix.map_one _ (map_zero _) (map_one _)]

end GlobalTheory.RepLattice

namespace GlobalTheory.RepLattice
open GlobalTheory.AdForm

end GlobalTheory.RepLattice
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Core GlobalTheory.Core.Ht2 GlobalTheory.CoreHt
open GlobalTheory.ColumnNormCompare (numDatumOfParameters codeRec plRec)
attribute [local instance] GlobalTheory.Mem.Col2.starE

namespace GlobalTheory.CoreHt.SpreadBound

theorem spread_lamOf_le {R : Ranks} (p : HCParam R) (j : ℕ) (hj : j ≤ R.m) (hk : 0 < R.k) (hm : R.m - 1 < R.m) :
    (((Formalism.BasicNotions.Examples₂.lamOf p j).spread : ℤ) : ℚ) ≤ p.u ⟨0, hk⟩ + p.e ⟨R.m - 1, hm⟩ + R.N R.m := by
  have hN : 0 < R.N j := by unfold Ranks.N; omega
  have hNm := Formalism.BasicNotions.Examples₂.N_mono (R := R) hj
  have h2 := R.two_le_m
  unfold DomWeight.spread
  rw [dite_eq_left hN]
  push_cast
  rw [Formalism.BasicNotions.Examples₂.lamOf_eq p j hj, Formalism.BasicNotions.Examples₂.lamOf_eq p j hj, Formalism.BasicNotions.Examples₂.wtQ_eq_wtN, Formalism.BasicNotions.Examples₂.wtQ_eq_wtN]
  have a1 : Formalism.BasicNotions.Examples₂.wtN p (R.N R.m - 1) ≤ Formalism.BasicNotions.Examples₂.wtN p (R.N j - 1) :=
    Formalism.BasicNotions.Examples₂.wtN_anti p (by omega) (by omega)
  have hmul : R.m * (R.t + 1) = (R.m - 1) * (R.t + 1) + (R.t + 1) := by
    obtain ⟨n, hn⟩ : ∃ n, R.m = n + 1 := ⟨R.m - 1, by omega⟩
    rw [hn, Nat.add_sub_cancel]; ring
  have hb : Formalism.BasicNotions.Examples₂.blkN R (R.N R.m - 1) = R.m - 1 := by
    unfold Formalism.BasicNotions.Examples₂.blkN Ranks.N
    have : R.k + R.m * (R.t + 1) - 1 - R.k = R.t + (R.t + 1) * (R.m - 1) := by
      rw [hmul, mul_comm (R.t + 1)]; omega
    rw [this, Nat.add_mul_div_left _ _ (by omega), Nat.div_eq_of_lt (by omega), zero_add]
  have a2 : -p.e ⟨R.m - 1, hm⟩ ≤ Formalism.BasicNotions.Examples₂.wtN p (R.N R.m - 1) := by
    have c1 : ¬ R.N R.m - 1 < R.k := by unfold Ranks.N; omega
    have c2 : Formalism.BasicNotions.Examples₂.blkN R (R.N R.m - 1) < R.m := by omega
    unfold Formalism.BasicNotions.Examples₂.wtN
    rw [dite_eq_right c1, dite_eq_left c2]
    have e : (⟨Formalism.BasicNotions.Examples₂.blkN R (R.N R.m - 1), c2⟩ : Fin R.m) = ⟨R.m - 1, hm⟩ := Fin.ext hb
    rw [e]
    unfold wG
    push_cast
    have : (0 : ℚ) ≤ (2 * ((Formalism.BasicNotions.Examples₂.blkN R (R.N R.m - 1) : ℚ) + 1) - 1) * ((R.t : ℚ) + 1) / 2 := by
      have : (0 : ℚ) ≤ 2 * ((Formalism.BasicNotions.Examples₂.blkN R (R.N R.m - 1) : ℚ) + 1) - 1 := by
        have : (0 : ℚ) ≤ (Formalism.BasicNotions.Examples₂.blkN R (R.N R.m - 1) : ℚ) := by positivity
        linarith
      positivity
    have : (0 : ℚ) ≤ (R.k : ℚ) / 2 := by positivity
    linarith
  have a3 : Formalism.BasicNotions.Examples₂.wtN p 0 ≤ p.u ⟨0, hk⟩ := by
    unfold Formalism.BasicNotions.Examples₂.wtN
    rw [dite_eq_left hk]
    unfold hcToWeightQ rhoVec
    have : (1 : ℚ) ≤ R.k := by exact_mod_cast hk
    simp only [Nat.cast_zero]
    linarith
  have a4 : (R.N j : ℚ) ≤ R.N R.m := by exact_mod_cast hNm
  simp only
  linarith

end GlobalTheory.CoreHt.SpreadBound

namespace GlobalTheory.CoreHt.SpreadBound

theorem spread_lamTrue_le : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X) (h : I.Ok) (l : I.Laws) (Z : TC.Later B (I.cols l))
    (L : SizeData₂ (I.rec7 l Z)) (CY : ℝ), HtRowsS L CY → 8 ≤ L.sc.X' → 2 ≤ L.sc.x → ∀ (u : B.Word) (j : ℕ), j ≤ B.R.m → ∀ τ,
    ((B.wts.lamTrue u j τ).spread : ℝ) ≤ 2 * L.sc.a := by
  intro B X I _ l Z L CY hS hX hx u j hj τ
  obtain ⟨⟨P⟩, -, -, ⟨hN3, -, hmt, hkS, hbT⟩, -, hT⟩ := hS
  have hm := B.R.two_le_m
  have hk : 5 ≤ B.R.k := by have := B.R.m_add_three_le_k; omega
  have hk0 : 0 < B.R.k := by omega
  have hm1 : B.R.m - 1 < B.R.m := by omega
  have c1 := spread_lamOf_le (B.hcW u τ) j hj hk0 hm1
  have c2 : (((B.wts.lamTrue u j τ).spread : ℤ) : ℝ) ≤
      (((B.hcW u τ).u ⟨0, hk0⟩ : ℚ) : ℝ) + (((B.hcW u τ).e ⟨B.R.m - 1, hm1⟩ : ℚ) : ℝ) + B.R.N B.R.m := by
    unfold Wts.lamTrue
    rw [spread_shiftW]
    exact_mod_cast c1
  refine c2.trans ?_
  have hx1 := L.sc.one_lt_alt
  have hL1 : 1 ≤ L.sc.L := Real.one_le_rpow hx1.le L.sc.eps_pos.le
  have hb1 : 1 ≤ L.sc.b := Real.one_le_exp (by linarith)
  have ha : L.sc.a = L.sc.x * L.sc.b := rfl
  have hb2 : 2 * L.sc.b ≤ L.sc.a := by rw [ha]; nlinarith
  have hX0 : 0 < L.sc.X' := by linarith
  have hb'a : L.sc.b' ≤ L.sc.a / 8 := by
    have : 0 < L.sc.a := by linarith
    exact div_le_div_of_nonneg_left this.le (by norm_num) hX
  have hb'0 : 0 < L.sc.b' := by
    have : 0 < L.sc.a := by linarith
    exact div_pos this hX0
  have hn1 : (1 : ℝ) ≤ (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).R.n := by
    have : 1 ≤ (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).R.n := by
      have h₁ := (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).R.two_le_m
      have h₂ := (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).R.m_le_f
      unfold Ranks.n
      omega
    exact_mod_cast this
  have hw : L.sc.w'' (I.rec7 l Z).R.n ≤ L.sc.b' :=
    div_le_self hb'0.le (one_le_mul_of_one_le_of_one_le hx1.le hn1)
  have he := L.etaSz_pos
  have hS0 := L.Sc_pos
  have hm' : (2 : ℝ) ≤ B.R.m := by exact_mod_cast hm
  have hk' : (5 : ℝ) ≤ B.R.k := by exact_mod_cast hk
  have ht : (0 : ℝ) ≤ B.R.t := Nat.cast_nonneg _
  have heta : 2 * L.etaSz ≤ L.sc.b' := by
    have h1 : (2 : ℝ) ≤ B.R.m * ((B.R.t : ℝ) + 1) := by nlinarith
    have h2 := mul_le_mul_of_nonneg_right h1 he.le
    have h3 : (B.R.m : ℝ) * ((B.R.t : ℝ) + 1) * L.etaSz ≤ L.sc.w'' (I.rec7 l Z).R.n := hmt
    linarith
  have hSc : 5 * L.Sc ≤ L.sc.b' := by
    have h3 : (B.R.k : ℝ) * L.Sc ≤ L.sc.w'' (I.rec7 l Z).R.n := hkS
    nlinarith
  have hN1 : (1 : ℝ) ≤ B.R.N B.R.m := by
    have : 1 ≤ B.R.N B.R.m := by unfold Ranks.N; omega
    exact_mod_cast this
  have hNeta : (B.R.N B.R.m : ℝ) ≤ L.etaSz := by
    have h3 : 4 * (B.R.N B.R.m : ℝ) ^ 3 ≤ L.etaSz := hN3
    have h4 : (B.R.N B.R.m : ℝ) ^ 1 ≤ (B.R.N B.R.m : ℝ) ^ 3 := pow_le_pow_right₀ hN1 (by norm_num)
    rw [pow_one] at h4
    linarith
  have hkN : (B.R.k : ℝ) ≤ B.R.N B.R.m := by
    have : B.R.k ≤ B.R.N B.R.m := by unfold Ranks.N; omega
    exact_mod_cast this
  have hu0 : (B.hcW u τ).u ⟨0, hk0⟩ = ((I.rec7 l Z).hc τ).u ⟨0, hk0⟩ := (I.rec7 l Z).hcW_first u τ hk0
  have he0 : (B.hcW u τ).e = ((I.rec7 l Z).hc τ).e := (I.rec7 l Z).hcW_e u τ
  have hwm : wj (I.rec7 l Z) B.R.m τ = (((B.hcW u τ).e ⟨B.R.m - 1, hm1⟩ : ℚ) : ℝ) := by
    unfold wj
    rw [dite_eq_left (show B.R.m - 1 < (I.rec7 l Z).R.m from hm1)]
    exact (congrArg (fun f => ((f ⟨B.R.m - 1, hm1⟩ : ℚ) : ℝ)) he0).symm
  rw [← hwm, hu0]
  by_cases htop : ((I.rec7 l Z).eTau τ : (I.rec7 l Z).R.GG) ∈ (I.rec7 l Z).host.topPlaces
  · obtain ⟨t, htt⟩ : ∃ t : (I.rec7 l Z).host.TT,
        ((I.rec7 l Z).eTau τ : (I.rec7 l Z).R.GG) = (I.rec7 l Z).R.tau1 t := by
      unfold Host.topPlaces at htop
      obtain ⟨t, ht, hte⟩ := Finset.mem_image.1 htop
      exact ⟨⟨t, ht⟩, hte.symm⟩
    rw [(L.top_u τ t hk0 htt).1]
    show (L.aT t : ℝ) + ((B.R.k : ℝ) - 1) / 2 + wj (I.rec7 l Z) B.R.m τ + (B.R.N B.R.m : ℝ) ≤ 2 * L.sc.a
    have a1 : wj (I.rec7 l Z) B.R.m τ ≤ (L.bT t : ℝ) + L.sc.b' / L.sc.x + L.etaSz :=
      (L.win_top B.R.m (by omega) le_rfl τ t htt).2
    have a2 : (L.aT t : ℝ) ≤ L.sc.a + L.sc.a / ((B.R.k : ℝ) * L.sc.x ^ (Scale.A / 2)) := (L.aT_win t).2
    have a3 : (5 : ℝ) ≤ (B.R.k : ℝ) * L.sc.x ^ (Scale.A / 2) :=
      hk'.trans (le_mul_of_one_le_right (by linarith) (Real.one_le_rpow hx1.le (by unfold Scale.A; norm_num)))
    have a4 : L.sc.a / ((B.R.k : ℝ) * L.sc.x ^ (Scale.A / 2)) ≤ L.sc.a / 5 :=
      div_le_div_of_nonneg_left (by linarith) (by norm_num) a3
    have a5 : L.sc.b' / L.sc.x ≤ L.sc.b' := div_le_self hb'0.le hx1.le
    have a6 := hbT t
    linarith
  · have h1 := P.cloud_place_bound τ (by show 0 < B.R.k - 1; omega) htop
    have h2 := (L.cloud_v τ ⟨0, by show 0 < B.R.k - 1; omega⟩).2
    push_cast at h1
    by_cases hc : ((I.rec7 l Z).eTau τ : (I.rec7 l Z).R.GG) ∈ (I.rec7 l Z).host.thickPlaces
    · have a1 := hT B.R.m (by omega) le_rfl τ hc
      linarith
    · have a1 := (L.win_thin B.R.m (by omega) le_rfl τ ⟨((I.rec7 l Z).eTau τ).2, htop, hc⟩).2
      linarith

end GlobalTheory.CoreHt.SpreadBound
end

section

open Matrix

theorem _root_.GlobalTheory.T.isFlagUnipotentMatrix_iff_jointlyBijective_pair : ∀ {A R₁ R₂ : Type} [CommRing A] [CommRing R₁] [CommRing R₂] (f : A →+* R₁) (g : A →+* R₂), (∀ y, f y = 0 → g y = 0 → y = 0) → (∀ a b, ∃ y, f y = a ∧ g y = b) → ∀ {n ρ : ℕ} (E : Matrix (Fin n) (Fin ρ) A) (K : Matrix (Fin ρ) (Fin n) A) (M : Matrix (Fin n) (Fin n) A), GlobalTheory.BesselChar.Unip E K M ↔ GlobalTheory.BesselChar.Unip (E.map f) (K.map f) (M.map f) ∧ GlobalTheory.BesselChar.Unip (E.map g) (K.map g) (M.map g) := by
  first | exact @GlobalTheory.BesselChar.JointSplit.unip_iff_of_joint | exact GlobalTheory.BesselChar.JointSplit.unip_iff_of_joint | (intros; apply GlobalTheory.BesselChar.JointSplit.unip_iff_of_joint <;> assumption)
end

section

open Matrix

theorem _root_.GlobalTheory.T.isFlagUnipotentMatrix_pi_iff_forall_eval : ∀ {ι S : Type} [Fintype ι] [DecidableEq ι] [CommRing S] {n ρ : ℕ} (E : Matrix (Fin n) (Fin ρ) (ι → S)) (K : Matrix (Fin ρ) (Fin n) (ι → S)) (M : Matrix (Fin n) (Fin n) (ι → S)), GlobalTheory.BesselChar.Unip E K M ↔ ∀ i, GlobalTheory.BesselChar.Unip (E.map (Pi.evalRingHom (fun _ => S) i)) (K.map (Pi.evalRingHom (fun _ => S) i)) (M.map (Pi.evalRingHom (fun _ => S) i)) := by
  first | exact @GlobalTheory.BesselChar.unip_pi_iff | exact GlobalTheory.BesselChar.unip_pi_iff | (intros; apply GlobalTheory.BesselChar.unip_pi_iff <;> assumption)
end

section

open Matrix NumberField
open scoped TensorProduct

theorem _root_.GlobalTheory.T.isFlagUnipotent_finiteAdeles_iff_frame_unipotentRadical : ∀ (I : Formalism.MainNotions.S.AutInst) {ρ : ℕ} (x : Fin ρ → Fin I.n → I.E) (c : Fin ρ → I.E) (z : Fin I.n → I.E), (∀ a, c a ≠ 0) → (∀ a, Formalism.UG.hform (starRingEnd I.E) I.J (x a) z = 0) → ∀ (N : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)), GlobalTheory.BesselChar.Unip ((Matrix.of fun k a => c a * x a k).map (Formalism.UG.inclE (F := I.F) (Formalism.MainNotions.S.Af I.F))) ((Formalism.UG.cT (starRingEnd I.E) (Matrix.of fun k a => c a * x a k) * I.J).map (Formalism.UG.inclE (F := I.F) (Formalism.MainNotions.S.Af I.F))) N ↔ ((∀ a : Fin ρ, (N - 1) *ᵥ Formalism.L2.SG.HidaSetting.incl I (x a) ∈ Submodule.span (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) ((fun b => Formalism.L2.SG.HidaSetting.incl I (x b)) '' {b | b.1 < a.1})) ∧ (N - 1) *ᵥ Formalism.L2.SG.HidaSetting.incl I z ∈ Submodule.span (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) (Set.range fun b => Formalism.L2.SG.HidaSetting.incl I (x b)) ∧ ∀ y : Formalism.L2.SG.HidaSetting.VA I, (∀ a, Formalism.L2.SG.HidaSetting.hA I (Formalism.L2.SG.HidaSetting.incl I (x a)) y = 0) → (N - 1) *ᵥ y ∈ Submodule.span (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) (Set.range fun b => Formalism.L2.SG.HidaSetting.incl I (x b))) := by
  first | exact @GlobalTheory.UnipFin.unip_flag_iff_Nfin | exact GlobalTheory.UnipFin.unip_flag_iff_Nfin | (intros; apply GlobalTheory.UnipFin.unip_flag_iff_Nfin <;> assumption)
end

section

open Matrix NumberField
open scoped TensorProduct

theorem _root_.GlobalTheory.T.isFlagUnipotent_realPlace_iff_frame_unipotentRadical : ∀ (I : Formalism.MainNotions.S.AutInst) (v : InfinitePlace I.F) {ρ : ℕ} (x : Fin ρ → Fin I.n → I.E) (c : Fin ρ → I.E) (z : Fin I.n → I.E), (∀ a, c a ≠ 0) → (∀ a, Formalism.UG.hform (starRingEnd I.E) I.J (x a) z = 0) → ∀ (N : Matrix (Fin I.n) (Fin I.n) ℂ), GlobalTheory.BesselChar.Unip ((Matrix.of fun k a => c a * x a k).map (I.φ v)) ((Formalism.UG.cT (starRingEnd I.E) (Matrix.of fun k a => c a * x a k) * I.J).map (I.φ v)) N ↔ Formalism.L2.SG.HidaSetting.InN (I.ε v) (fun a => Formalism.L2.SG.HidaSetting.rv I v (x a)) (Formalism.L2.SG.HidaSetting.rv I v z) ((I.P v)⁻¹ * N * I.P v) := by
  first | exact @GlobalTheory.RealUnipFrame.unip_iff_inN | exact GlobalTheory.RealUnipFrame.unip_iff_inN | (intros; apply GlobalTheory.RealUnipFrame.unip_iff_inN <;> assumption)
end

section

open Formalism.BasicNotions.TH GlobalTheory.RealPar

noncomputable section

namespace GlobalTheory.CoverDS

theorem discreteSeriesCover_of_classification :
    GlobalTheory.Published.DiscreteSeriesClassification → GlobalTheory.Published.DiscreteSeriesCover := by
  intro hcl
  obtain ⟨hExists, hExhaust, hUnique, hInfChar, hLowK, hKTypes, -⟩ :=
    GlobalTheory.ClassificationConsequences.consequences_of_dsClass
      (GlobalTheory.Published.discreteSeriesClassification_iff.1 hcl)
  have hC : GlobalTheory.Published.DiscreteSeriesCoverExists :=
    GlobalTheory.Published.CoverSeries.of_upq
      (GlobalTheory.Published.discreteSeriesUpqExists_iff_dsExists.2 hExists)
      (fun p q h T U hU => ((GlobalTheory.T.harishChandraModules_indefiniteUnitaryGroup.1 p q h T).1 U hU).2.1)
  intro p q hn T
  choose D hD using fun lam : {lam : Ix p q → ℚ // IsParam lam} => hC p q T lam.1 lam.2
  refine ⟨D, ?_, ?_⟩
  · intro lam
    exact GlobalTheory.T.hasDiscreteSeriesKTypes_of_hasParam_cover
      hLowK hKTypes hInfChar p q hn T (D lam) lam.1 lam.2 (hD lam)
  · intro R
    obtain ⟨lam, hl, hR⟩ := GlobalTheory.T.exists_param_coverDiscreteSeries hExhaust p q hn T R
    exact ⟨⟨lam, hl⟩, GlobalTheory.T.coverDiscreteSeriesUnitarilyEquiv_of_sameParam
      hUnique p q hn T R (D ⟨lam, hl⟩) lam hl hR (hD ⟨lam, hl⟩)⟩

end GlobalTheory.CoverDS

end
end

section


theorem _root_.GlobalTheory.T.hilbertClassField_of_globalArtinReciprocity : GlobalTheory.Published.GlobalArtinReciprocity → Neutral.HilbertClassField.Statement := by
  first | exact @GlobalTheory.Published.GlobalArtinReciprocity.hilbertClassField | exact GlobalTheory.Published.GlobalArtinReciprocity.hilbertClassField | (intros; apply GlobalTheory.Published.GlobalArtinReciprocity.hilbertClassField <;> assumption)
end
