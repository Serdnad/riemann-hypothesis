module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
import Development.AbelianVarietyTheory.Definitions.Foundations.OfInfProjInfMulOfFinProjFin
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittHyperbolicAnisotropicCommuteLevi
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle340
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsMulRightInvariantOfFundamentalDomain
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.FstACoordOfInfPart
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle138
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TopLevExists
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle042
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle048
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle313
public import Formalism.LocalToGlobal.IndefiniteReal.GvPairOfOrbitDerivCont
import Formalism.LocalToGlobal.IndefiniteReal.SchurOrthogonality
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle139
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle309
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle152
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
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle004
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.QuasiOfFam
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle012
import Formalism.LocalToGlobal.Columns.CoefficientsModP.WeTransposeWordTransposeWord
import Formalism.LocalToGlobal.IndefiniteReal.Bundle017
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowDict
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowsJoinPinned
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.HidaSetting
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.PoincareInHH
import Std.Tactic.BVDecide.Normalize.Prop
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle003

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

noncomputable section
namespace GlobalTheory.Unf

def coordFlip (D : D7) (ρ m : ℕ) : skewA D ρ × (Mx D ρ m × UX D ρ) ≃ₜ UX D ρ × (Mx D ρ m × skewA D ρ) :=
  haveI : IsTopologicalAddGroup (Mx D ρ m) := (lattice_Mx D ρ m).1
  haveI : IsTopologicalAddGroup (Mx D ρ ρ) := (lattice_Mx D ρ ρ).1
  { toFun := fun p => (p.2.2⁻¹, (-p.2.1, -p.1))
    invFun := fun q => (-q.2.2, (-q.2.1, q.1⁻¹))
    left_inv := fun p => Prod.ext (neg_neg _) (Prod.ext (neg_neg _) (inv_inv _))
    right_inv := fun q => Prod.ext (inv_inv _) (Prod.ext (neg_neg _) (neg_neg _))
    continuous_toFun := continuous_snd.snd.inv.prodMk (continuous_snd.fst.neg.prodMk continuous_fst.neg)
    continuous_invFun := continuous_snd.snd.neg.prodMk (continuous_snd.fst.neg.prodMk continuous_fst.inv) }

theorem coordFlip_apply (D : D7) (ρ m : ℕ) (p : skewA D ρ × (Mx D ρ m × UX D ρ)) :
    coordFlip D ρ m p = (p.2.2⁻¹, (-p.2.1, -p.1)) := rfl

end GlobalTheory.Unf

namespace GlobalTheory.Unf

theorem flagCoord_measEquiv : ∀ (D : D7) (V V₀ : HSp D) (ρ : ℕ) (d : HypDec V V₀ ρ),
    ∃ e : skewA D ρ × (Mx D ρ V₀.rank × UX D ρ) ≃ᵐ flagN d,
      ∀ p, (e p : GA D V) = d.nC p.1 * (d.nB p.2.1 * d.levi p.2.2.1) := by
  intro D V V₀ ρ d
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.T.exists_homeomorph_wittFlagCoordinates D V V₀ ρ d
  haveI : SecondCountableTopology (Mx D ρ V₀.rank) := (lattice_Mx D ρ V₀.rank).2.2.1
  haveI : SecondCountableTopology (Mx D ρ ρ) := (lattice_Mx D ρ ρ).2.2.1
  haveI : SecondCountableTopology (UX D ρ) := (GlobalTheory.UnitU.topology D ρ).2.1
  haveI : BorelSpace (Mx D ρ V₀.rank) := ⟨rfl⟩
  haveI : BorelSpace (Mx D ρ ρ) := ⟨rfl⟩
  haveI : BorelSpace (UX D ρ) := ⟨rfl⟩
  haveI : BorelSpace (skewA D ρ) := Subtype.borelSpace _
  haveI : SecondCountableTopology (skewA D ρ) := Topology.IsEmbedding.subtypeVal.secondCountableTopology
  refine ⟨((coordFlip D ρ V₀.rank).trans (Φ.trans (Homeomorph.inv (flagN d)))).toMeasurableEquiv, fun p => ?_⟩
  change (((Φ (coordFlip D ρ V₀.rank p))⁻¹ : flagN d) : GA D V) = _
  rw [Subgroup.coe_inv, hΦ, coordFlip_apply]
  change (d.levi ((p.2.2⁻¹ : UX D ρ) : GL (Fin ρ) (AE D)) * (d.nB (-p.2.1) * d.nC (-p.1)))⁻¹ = _
  rw [_root_.mul_inv_rev, _root_.mul_inv_rev, d.nB_inv, d.nC_inv, neg_neg, neg_neg, Subgroup.coe_inv, map_inv, inv_inv,
    mul_assoc]

end GlobalTheory.Unf

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf GlobalTheory.Unf.FB

namespace GlobalTheory

theorem mt_jB_eq_of_fixes_lineVec (D : D7) (S A L : HSp D) (o : OrthDec S A L) (ζ : Fin L.rank → D.host.E)
    (hζ : IsLineVec L ζ) (k : GA D S) (hk : mt S k *ᵥ ratV (o.iB *ᵥ ζ) = ratV (o.iB *ᵥ ζ)) :
    mt S k ⬝ o.jB = o.jB := by
  obtain ⟨hL, hq⟩ := hζ
  obtain ⟨j0, hall⟩ : ∃ j0 : Fin L.rank, ∀ j : Fin L.rank, j = j0 :=
    ⟨⟨0, by omega⟩, fun j => Fin.ext (by have := j.isLt; show j.val = 0; omega)⟩
  have hζ0 : ζ j0 ≠ 0 := by
    intro h0
    apply hq
    have : ζ = 0 := funext fun j => by rw [hall j, h0]; rfl
    simp [this]
  have hv : ratV (o.iB *ᵥ ζ) = o.jB *ᵥ ratV ζ := by
    funext i; exact RingHom.map_mulVec (incA D) o.iB ζ i
  rw [hv, Matrix.mulVec_mulVec] at hk
  have hM : (mt S k ⬝ o.jB - o.jB) *ᵥ ratV ζ = 0 := by rw [Matrix.sub_mulVec, hk, sub_self]
  rw [← sub_eq_zero]
  funext i j
  rw [hall j]
  have h1 := congrFun hM i
  simp only [Matrix.mulVec, dotProduct, Pi.zero_apply] at h1
  rw [Fintype.sum_eq_single j0 (fun j hj => absurd (hall j) hj)] at h1
  have hu : incA D (ζ j0) * incA D (ζ j0)⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel₀ hζ0, map_one]
  have e : (mt S k ⬝ o.jB - o.jB) i j0 = (mt S k ⬝ o.jB - o.jB) i j0 * ratV ζ j0 * incA D (ζ j0)⁻¹ := by
    rw [mul_assoc]; show _ = _ * (incA D (ζ j0) * _); rw [hu, mul_one]
  rw [e, h1, zero_mul]; rfl

theorem mat_eq_of_splitting {R : Type} [CommRing R] {n a b : ℕ} (M : Matrix (Fin n) (Fin n) R)
    (jA : Matrix (Fin n) (Fin a) R) (pA : Matrix (Fin a) (Fin n) R) (jB : Matrix (Fin n) (Fin b) R)
    (pB : Matrix (Fin b) (Fin n) R) (H : Matrix (Fin a) (Fin a) R) (hX : M * jA = jA * H) (hfix : M * jB = jB)
    (hsum : jA * pA + jB * pB = 1) : M = jA * H * pA + jB * pB := by
  calc M = M * (jA * pA + jB * pB) := by rw [hsum, Matrix.mul_one]
    _ = M * jA * pA + M * jB * pB := by rw [Matrix.mul_add, Matrix.mul_assoc, Matrix.mul_assoc]
    _ = jA * H * pA + jB * pB := by rw [hX, hfix]

theorem exists_emb_of_mt_jB_eq (D : D7) (S A B : HSp D) (o : OrthDec S A B) (k : GA D S)
    (hfix : mt S k ⬝ o.jB = o.jB) : ∃ h : GA D A, k = o.emb (h, 1) := by
  have hu : adj (mt S k) ⬝ (gA S ⬝ mt S k) = gA S := GlobalTheory.MixModel.mt_unitary S k
  have hBA : adj o.jB ⬝ (gA S ⬝ (mt S k ⬝ o.jA)) = 0 := by
    calc adj o.jB ⬝ (gA S ⬝ (mt S k ⬝ o.jA)) = adj (mt S k ⬝ o.jB) ⬝ (gA S ⬝ (mt S k ⬝ o.jA)) := by rw [hfix]
      _ = adj o.jB ⬝ (gA S ⬝ o.jA) := by
        rw [adj_mul, Matrix.mul_assoc, GlobalTheory.MixModel.cancel₃ hu o.jA]
      _ = 0 := o.gram_BA
  have hpB : o.pB ⬝ (mt S k ⬝ o.jA) = 0 := by
    rw [o.pB_eq, Matrix.mul_assoc, Matrix.mul_assoc, hBA, Matrix.mul_zero]
  have hX : mt S k ⬝ o.jA = o.jA ⬝ (o.pA ⬝ (mt S k ⬝ o.jA)) := by
    calc mt S k ⬝ o.jA = (o.jA ⬝ o.pA + o.jB ⬝ o.pB) ⬝ (mt S k ⬝ o.jA) := by rw [o.sum_eq_one, Matrix.one_mul]
      _ = o.jA ⬝ (o.pA ⬝ (mt S k ⬝ o.jA)) + o.jB ⬝ (o.pB ⬝ (mt S k ⬝ o.jA)) := by
        simp only [Matrix.add_mul, Matrix.mul_assoc]
      _ = _ := by rw [hpB, Matrix.mul_zero, add_zero]
  have e1 : adj (mt S k ⬝ o.jA) ⬝ (gA S ⬝ (mt S k ⬝ o.jA)) = gA A := by
    rw [adj_mul, Matrix.mul_assoc, GlobalTheory.MixModel.cancel₃ hu o.jA]
    exact o.gram_AA
  set H := o.pA ⬝ (mt S k ⬝ o.jA) with hHdef
  have e2 : adj (o.jA ⬝ H) ⬝ (gA S ⬝ (o.jA ⬝ H)) = adj H ⬝ (gA A ⬝ H) := by
    rw [adj_mul, Matrix.mul_assoc, GlobalTheory.MixModel.cancel₃ o.gram_AA H]
  rw [← hX] at e2
  have hH : adj H * (gA A * H) = gA A := e2.symm.trans e1
  refine ⟨GlobalTheory.MixModel.ofMat A H hH, GlobalTheory.MixModel.mt_injective S ?_⟩
  rw [o.mt_emb, GlobalTheory.MixModel.mt_ofMat, GlobalTheory.MixModel.mt_one, Matrix.mul_one]
  exact mat_eq_of_splitting (mt S k) o.jA o.pA o.jB o.pB H hX hfix o.sum_eq_one

theorem exists_emb_of_fixes_lineVec (D : D7) (S A L : HSp D) (o : OrthDec S A L) (ζ : Fin L.rank → D.host.E)
    (hζ : IsLineVec L ζ) (k : GA D S) (hk : mt S k *ᵥ ratV (o.iB *ᵥ ζ) = ratV (o.iB *ᵥ ζ)) :
    ∃ h : GA D A, k = o.emb (h, 1) :=
  exists_emb_of_mt_jB_eq D S A L o k (mt_jB_eq_of_fixes_lineVec D S A L o ζ hζ k hk)

end GlobalTheory
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.L2.SG.AdBridge GlobalTheory.BesselChar


theorem _root_.GlobalTheory.T.exists_orthogonalComplement_preimage_of_fix_line : ∀ {D : D7} {S₀ A L : HSp D} (o : OrthDec S₀ A L) (ζ : Fin L.rank → D.host.E), IsLineVec L ζ → ∀ (b : GA D S₀), (mt S₀ b *ᵥ (fun k => incA D (vecB o ζ k)) = fun k => incA D (vecB o ζ k)) → ∃ a : GA D A, o.emb (a, 1) = b := by
  first | exact @GlobalTheory.LineFix.exists_emb_of_fix_line | exact GlobalTheory.LineFix.exists_emb_of_fix_line | (intros; apply GlobalTheory.LineFix.exists_emb_of_fix_line <;> assumption)
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.FinPl GlobalTheory.FinPlLoc Filter Topology
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.PsiUnit

variable {D : D7}


open Formalism.IndefR.Fin.LevelGroupLemmas in
theorem char_eq_one_of_local (ψ : AddChar (AF D.host.F) ℂ) (hψ : Continuous ψ) (t : AF D.host.F)
    (ht : fstA D.host.F t = 0) (h : ∀ v : Pl D, ψ (pairA D.host.F 0 (ePl D (· = v)) * t) = 1) : ψ t = 1 := by
  classical
  have h1 : ∀ A : Finset (Pl D), ψ (idemS A * t) = 1 := by
    intro A
    induction A using Finset.induction_on with
    | empty => rw [idemS_empty, zero_mul, AddChar.map_zero_eq_one]
    | insert v A hv ih =>
      have e : idemS (insert v A) = idemS A + pairA D.host.F 0 (ePl D (· = v)) := by
        unfold idemS
        rw [← pairA_add]
        congr 1
        refine RestrictedProduct.ext _ _ fun w => ?_
        change evalV D.host.F w (sglS (insert v A)) = evalV D.host.F w (sglS A + ePl D (· = v))
        rw [map_add (f := _), evalV_sglS, evalV_sglS, evalV_ePl]
        by_cases hw : w = v
        · subst hw; simp [hv]
        · simp [hw]
      rw [e, add_mul, AddChar.map_add_eq_mul, ih, h, one_mul]
  have h2 := (hψ.tendsto 0).comp (tendsto_AF t ht)
  rw [AddChar.map_zero_eq_one] at h2
  refine tendsto_nhds_unique tendsto_const_nhds (h2.congr fun A => ?_)
  have e : t = idemS A * t + (1 - idemS A) * t := by ring
  change ψ ((1 - idemS A) * t) = ψ t
  conv_rhs => rw [e, AddChar.map_add_eq_mul, h1, one_mul]

theorem trace_idem (Q : Pl D → Prop) (s : AE D) : Algebra.trace (AF D.host.F) (AE D) (idem D Q * s) =
    pairA D.host.F 0 (ePl D Q) * Algebra.trace (AF D.host.F) (AE D) s := by
  rw [← smul_eq_mul (pairA D.host.F 0 (ePl D Q)), ← map_smul, Algebra.smul_def]
  rfl

theorem psiE_eq_one_of_local (ψ : AddChar (AF D.host.F) ℂ) (hψ : Continuous ψ) {P : Pl D → Prop} {s : AE D}
    (hs : s ∈ idAt D P) (h : ∀ v, P v → psiE ψ (idem D (· = v) * s) = 1) : psiE ψ s = 1 := by
  refine char_eq_one_of_local ψ hψ _ ?_ fun v => ?_
  · rw [← (mem_idAt_iff P s).1 hs, trace_idem, map_mul]
    exact zero_mul _
  · rw [← trace_idem]
    by_cases hv : P v
    · exact h v hv
    · have h0 : idem D (· = v) * s = 0 := by
        refine (mem_idOff_iff _ s).1 ((Submodule.mem_iInf _).2 fun w => RingHom.mem_ker.2 ?_)
        exact compAt_of_idAt hs (by rw [w.2]; exact hv)
      rw [h0]
      exact psiE_zero ψ

theorem latV_mono {S : HSp D} {L : Lat S} {P : Pl D → Prop} {v : Pl D} (hv : P v) : latV S L (· = v) ≤ latV S L P := by
  refine AddSubgroup.closure_mono ?_
  rintro y ⟨α, h1, h2, h3⟩
  exact ⟨α, h1, fun w hw => h2 w fun e => hw (e ▸ hv), h3⟩

theorem mulVec_colMul {l m n : ℕ} (A : Mx D l m) (x : Mx D m n) (i : Fin n) (a : AE D) :
    A *ᵥ colMul x i a = colMul (A ⬝ x) i a := by
  funext k
  simp only [Matrix.mulVec, dotProduct, colMul, Matrix.mul_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring

end GlobalTheory.FinPl.PsiUnit

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.L2.Forms GlobalTheory.Core.Rk GlobalTheory.Core.Rk.Top
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical

noncomputable section

namespace GlobalTheory.Core.Rk.TopOnto

open GlobalTheory.Mem.ColAd GlobalTheory.Core.Rk.TopLift GlobalTheory.Core.Rk.Top.Model GlobalTheory.PointAtPlaceHom Formalism.MainNotions.StandardLattice Matrix

section General

variable {D : D7} {θ : InfFam D} {V : HSp D} {S : D.what₂.Tau → SPar}

theorem rep_mem_sm (M : DSModel V S) (τ : D.what₂.Tau) {g : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hg : g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) (w : M.H τ) (hw : w ∈ M.sm τ) : M.rep τ g w ∈ M.sm τ := by
  have hG : IsUnit (gramAt D V τ) := by
    rw [← M.fr_gram τ]
    exact (((Matrix.isUnit_conjTranspose _).2 (M.fr_unit τ)).mul
      (IsUnit.of_mul_eq_one _ (Formalism.REAL.Jm_mul_self (M.ε τ)))).mul (M.fr_unit τ)
  have hg' : gᴴ * gramAt D V τ * g = gramAt D V τ := hg
  obtain ⟨u, rfl⟩ : IsUnit g := isUnit_of_mul_isUnit_right (hg'.symm ▸ hG : IsUnit (gᴴ * gramAt D V τ * g))
  exact Submodule.subset_span
    (Formalism.IndefR.SchurOrthogonalityAlt.smoothVec_rep M τ ⟨u, hg⟩ (Formalism.IndefR.SchurOrthogonalityAlt.gp_sv_of_mem hw))

theorem real_induction (hθ : IsInfFam θ) (P : GA D V → Prop) (h1 : P 1) (hmul : ∀ a b, P a → P b → P (a * b))
    (hat : ∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), P (atTau θ V τ g)) : ∀ a ∈ GinfC V, P a := by
  have R := (GlobalTheory.SmoothForms.RealPts.realPoints D).2 θ hθ V
  have key : ∀ s : Finset D.what₂.Tau, ∀ a ∈ GinfC V, (∀ τ ∉ s, infMat D.sp.cm.sig V.gram (θ τ) a = 1) → P a := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro a ha h
      rw [R.2.2.1 a ha 1 (one_mem _) fun τ => by rw [h τ (Finset.notMem_empty τ), infMat_one]]
      exact h1
    | insert τ s hτ ih =>
      intro a ha h
      have hg := GlobalTheory.FockCompare.RealAction.infMat_mem_UH hθ V a τ
      have hb := atTau_spec hθ V τ hg
      have hi : ∀ ρ, infMat D.sp.cm.sig V.gram (θ ρ) (atTau θ V τ (infMat D.sp.cm.sig V.gram (θ τ) a))⁻¹ *
          infMat D.sp.cm.sig V.gram (θ ρ) (atTau θ V τ (infMat D.sp.cm.sig V.gram (θ τ) a)) = 1 := fun ρ => by
        rw [← infMat_mul, inv_mul_cancel, infMat_one]
      rw [← mul_inv_cancel_left (atTau θ V τ (infMat D.sp.cm.sig V.gram (θ τ) a)) a]
      refine hmul _ _ (hat τ _ hg) (ih _ (mul_mem (inv_mem hb.1) ha) fun ρ hρ => ?_)
      rw [infMat_mul]
      by_cases c : ρ = τ
      · subst c
        have := hi ρ
        rwa [hb.2.1] at this
      · have := hi ρ
        rw [hb.2.2 ρ c] at this
        rw [h ρ (by simp [c, hρ])]
        exact this
  exact fun a ha => key Finset.univ a ha fun τ h => absurd (Finset.mem_univ τ) h

theorem multT_rel {M : DSModel V S} {J : Set (GA D V)} {χ : GA D V → ℂ} (v v' : M.Vec) (x x' : GA D V) (c : ℂ)
    (h : ∀ m, IsMultMap θ M J χ m → m v' x' = c * m v x) {T} (hT : T ∈ MultT θ M J χ) :
    T (PiTensorProduct.tprod ℂ v') x' = c * T (PiTensorProduct.tprod ℂ v) x := by
  obtain ⟨m, hm, rfl⟩ := hT
  show PiTensorProduct.lift m _ x' = c * PiTensorProduct.lift m _ x
  rw [PiTensorProduct.lift.tprod, PiTensorProduct.lift.tprod]
  induction hm using Submodule.span_induction with
  | mem m hm => exact h m hm
  | zero => simp
  | add a b _ _ ha hb => simp only [MultilinearMap.add_apply, Pi.add_apply, ha, hb, mul_add]
  | smul r a _ ha => simp only [MultilinearMap.smul_apply, Pi.smul_apply, ha, smul_eq_mul]; ring

theorem multT_rel' {M : DSModel V S} {J : Set (GA D V)} {χ : GA D V → ℂ} (x x' : GA D V) (c : ℂ)
    (h : ∀ m, IsMultMap θ M J χ m → ∀ v, m v x' = c * m v x) {T} (hT : T ∈ MultT θ M J χ) (v : SmT M) :
    T v x' = c * T v x := by
  induction v using PiTensorProduct.induction_on with
  | smul_tprod r v =>
    rw [map_smul, Pi.smul_apply, Pi.smul_apply, multT_rel v v x x' c (fun m hm => h m hm v) hT, smul_eq_mul, smul_eq_mul]
    ring
  | add a b ha hb => rw [map_add (f := _), Pi.add_apply, Pi.add_apply, ha, hb, mul_add]

theorem exists_ratPt (hθ : IsInfFam θ) {n : ℕ} (hn : V.rank = n) (δ : GL (Fin n) D.host.E)
    (hδ : δ ∈ Formalism.UG.UJ (D.sp.cm.sig : D.host.E →+* D.host.E) (V.gram.reindex (finCongr hn) (finCongr hn))) :
    ∃ γ ∈ GQ V, finN V hn γ = Formalism.UG.bc (Formalism.UG.inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) δ ∧
      ∀ τ, (infN θ V hn (Equiv.refl _) γ τ : Matrix (Fin n) (Fin n) ℂ) = (δ : Matrix (Fin n) (Fin n) D.host.E).map (tauE D τ) := by
  subst hn
  have hm : Formalism.UG.bc (incA D) δ ∈ Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF D.host.F) D.sp.cm.sig V.gram :=
    unit_transfer (Equiv.refl _) (incA D) (D.sp.cm.sig : D.host.E →+* D.host.E) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR _ D.sp.cm.sig)
      (fun _ => rfl) V.gram _ (fun _ _ => rfl) δ.1 _ (fun _ _ => rfl) hδ
  refine ⟨⟨_, hm⟩, ⟨δ, hδ, rfl⟩, rfl, fun τ => ?_⟩
  exact Matrix.ext fun i j => (hθ τ).1 _

theorem infN_eq {n : ℕ} (hn : V.rank = n) (γ : GA D V) (τ : D.what₂.Tau) :
    (infN θ V hn (Equiv.refl _) γ τ : Matrix (Fin n) (Fin n) ℂ) =
      (infMat D.sp.cm.sig V.gram (θ τ) γ).reindex (finCongr hn) (finCongr hn) := by
  subst hn
  rfl

end General

section Law

variable {D : D7} {u : D.what₂.Word} {K : ClsPTied u} {θ : InfFam D} {S : D.what₂.Tau → SPar} {M : DSModel D.sp.X' S}
  {j : SmT M →ₗ[ℂ] (FrP D → ℂ)} {J : Set (GA D D.sp.X')} {χ : GA D D.sp.X' → ℂ}



theorem real_translate (hθ : IsInfFam θ) (hj : IsJ u M j) : ∀ a ∈ GinfC D.sp.X', ∀ v : SmT M, ∃ v' : SmT M,
    lT _ (infPt θ a) (j v') = j v ∧ ∀ T ∈ MultT θ M J χ, ∀ h, T v' h = T v (h * a) := by
  refine real_induction hθ _ (fun v => ⟨v, by rw [map_one, lT_one], fun T _ h => by rw [mul_one]⟩) (fun a b ha hb v => ?_)
    fun τ g hg v => ?_
  · obtain ⟨v₁, e1, f1⟩ := hb v
    obtain ⟨v₂, e2, f2⟩ := ha v₁
    refine ⟨v₂, by rw [map_mul (infPt θ), lT_mul, e2, e1], fun T hT h => ?_⟩
    rw [f2 T hT, f1 T hT, mul_assoc]
  · induction v using PiTensorProduct.induction_on with
    | smul_tprod r v =>
      let w : M.sm τ := ⟨M.rep τ g (v τ), rep_mem_sm M τ hg _ (v τ).2⟩
      refine ⟨r • PiTensorProduct.tprod ℂ (Function.update v τ w), ?_, fun T hT h => ?_⟩
      · rw [map_smul, map_smul, map_smul]
        congr 1
        funext y
        refine hj.eqv τ g hg v w rfl _ y fun ρ => ?_
        refine (congrArg (· * y.1 ρ) (infN_atTau θ _ (rankP D) hθ τ hg ρ)).trans ?_
        by_cases c : ρ = τ
        · subst c
          simp only [Function.update_self]
        · simp only [Function.update_of_ne c, Matrix.reindex_apply, Matrix.submatrix_one_equiv]
      · rw [map_smul, map_smul, Pi.smul_apply, Pi.smul_apply,
          multT_rel v (Function.update v τ w) (h * atTau θ _ τ g) h 1 (fun m hm => by
            rw [one_mul]; exact congrFun (hm.equiv τ g hg v w rfl) h) hT, one_mul]
    | add a b ha hb =>
      obtain ⟨a', e1, f1⟩ := ha
      obtain ⟨b', e2, f2⟩ := hb
      refine ⟨a' + b', by rw [map_add j, map_add j, map_add, e1, e2], fun T hT h => ?_⟩
      rw [map_add T, map_add T, Pi.add_apply, Pi.add_apply, f1 T hT, f2 T hT]

theorem hasMat_finPt {h : GA D D.sp.X'} (hh : h ∈ GfC D.sp.X') : HasMat h (finPt h).1 :=
  ⟨hh, fun i j => (finN_apply D.sp.X' (rankP D) h (finCongr (rankP D) i) (finCongr (rankP D) j)).symm⟩

end Law

section Form

variable {D : D7} {u : D.what₂.Word} {K : ClsPTied u} {θ : InfFam D} {S : D.what₂.Tau → SPar} {M : DSModel D.sp.X' S}
  {j : SmT M →ₗ[ℂ] (FrP D → ℂ)} {J : Set (GA D D.sp.X')} {χ : GA D D.sp.X' → ℂ}

end Form

end GlobalTheory.Core.Rk.TopOnto

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Core.SBesEx

theorem gram_eq_of_inst {D : D7} (I : AutInst) (hI : I = Formalism.L2.SG.InstExistsPf.instOf D)
    (ιE : I.E ≃+* D.host.E) (hId : ∀ x : I.E, HEq (ιE x) x) (hn : (D.sp.Y 0).rank = I.n)
    (k l : Fin (D.sp.Y 0).rank) :
    ιE (I.J (Fin.cast hn k) (Fin.cast hn l)) = (D.sp.Y 0).gram k l := by
  subst hI
  rw [eq_of_heq (hId _)]
  rfl

theorem cY_isom : ∀ (D : D7) (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), IdE X → ∀ y y' : (VS D).V, star (GlobalTheory.Core.SBesEx.cY X h y') ⬝ᵥ ((D.sp.Y 0).gram *ᵥ GlobalTheory.Core.SBesEx.cY X h y) = (VS D).hT y' y := by
  intro D X h hId y y'
  set b := X.bas.reindex (finCongr (rank_eq X h)).symm with hb
  have hc : ∀ z, cY X h z = b.repr z := by
    intro z; funext k
    simp [cY, HidaSetting.crd, crdOf, hb, Module.Basis.repr_reindex]
  have hG : (D.sp.Y 0).gram = fun k l => (VS D).hT (b k) (b l) := by
    funext k l
    rw [← gram_eq_of_inst X.B.I h X.ιE hId (rank_eq X h) k l, X.J_eq]
    simp [hb]
  rw [hc, hc, hG]
  conv_rhs => rw [← b.sum_repr y', ← b.sum_repr y]

  simp only [map_sum, map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, dotProduct, mulVec,
  Finset.mul_sum, Pi.star_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp [starRingEnd_apply]
  ring

end GlobalTheory.Core.SBesEx

end
end

section

open scoped TensorProduct

theorem _root_.GlobalTheory.T.piTensor_submodule_eq_top_of_absolutely_irreducible_stable : ∀ (ι : Type) [Fintype ι] (K : ι → Type) [∀ i, AddCommGroup (K i)] [∀ i, Module ℂ (K i)] (G : ι → Type) (a : ∀ i, G i → Module.End ℂ (K i)), (∀ i, GlobalTheory.Chain.IoLift.AbsIrr (a i)) → ∀ N : Submodule ℂ (PiTensorProduct ℂ K), (∀ i g, ∀ x ∈ N, GlobalTheory.Chain.IoLift.intersection_update_fsHerm_neg_one i (a i g) x ∈ N) → N ≠ ⊥ → N = ⊤ := by
  first | exact @GlobalTheory.TensorIrr.eq_top_of_stable | exact GlobalTheory.TensorIrr.eq_top_of_stable | (intros; apply GlobalTheory.TensorIrr.eq_top_of_stable <;> assumption)
end
