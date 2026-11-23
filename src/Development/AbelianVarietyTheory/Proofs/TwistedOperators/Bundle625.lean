module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle264
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle280
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Formalism.SharpRestriction.CuspSpanNormBounds.BesselShellMomentBounds
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle063
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNsmulIntMemLatO
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.CompletedTensorLatticeStrongApproxOpenCompact
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle592
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle275
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle289
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.IsLatticeVacuumIffSignedRationalFixed
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle615
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle324
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle576
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle007
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOrEqOfPlaceIdem
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle170
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ThetaAtEqSumHeisOfFourierSum
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HighestWeightBelow
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2227
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle597
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle613
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdempotentMulAddOneSubInverse
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle606
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle333
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle614
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle552
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle391
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle523
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle553
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle003
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle236
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle287

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LiftLevel



theorem exists_isGen : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (hn : T.rank ≤ S.rank) (ΛT : Lt D.host.E T.rank), IsSelfDualC T ΛT → IsAA C.X.Λ ΛT → ∀ (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)), Formalism.L2.DIV.IsFrame βS (stdL D.host.E S.rank) → Formalism.L2.DIV.IsFrame βT ΛT → ∀ (Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (ξ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ), Pg.Nonempty → (∀ PP, PP ∈ Pg ∨ PP ∈ Q → (2 : 𝓞 D.host.E) ∉ PP.asIdeal) → ∀ e : AE D, IsIdemSum e (Pg ∪ Q) → ∃ a : AE D, (∃ b : AE D, a * b = e) ∧ GlobalTheory.LiftLevel.IsGen C βS βT Pg Q e a := by
  intro D S T C hn ΛT hsd hAA βS βT hβS hβT Pg Q ξ hPg h2 e he
  have hS : S.gram = 1 := C.m.gS
  obtain ⟨γ, hγ, s, hs, h1, h2'⟩ := GlobalTheory.T.exists_global_scalar_prime_to_conj_polarisationLattice' D T.rank C.X.Λ ΛT hAA (Pg ∪ Q)
  obtain ⟨t, ht, hte⟩ := GlobalTheory.T.exists_integral_inverse_on_conjugate_half D (Pg ∪ Q) e he s hs
  have hee : e * e = e := GlobalTheory.PlaceVec.idemSum_mul_self he
  have hecinf : infPart D (cA D e) = 0 := GlobalTheory.PlaceVec.infPart_cA (GlobalTheory.PlaceVec.idemSum_infPart he)
  have hinf : ∀ x : WO S T, IsHalf (cA D e) x → IsFinPt x := by
    intro x hx
    ext i j
    simp only [Matrix.map_apply, Matrix.zero_apply]
    rw [← hx i j, map_mul, hecinf, zero_mul]
  have hmulA : ∀ (L1 L2 : Lt D.host.E T.rank) (c : D.host.E), (∀ v ∈ L1, ((s : D.host.E) * c) • v ∈ L2) →
      ∀ x : WO S T, IsHalf (cA D e) x → x ∈ hatA S T (tens (stdL D.host.E S.rank) L1) →
        incA D c • x ∈ hatA S T (tens (stdL D.host.E S.rank) L2) := by
    intro L1 L2 c hc x hx hxm
    have h3 := GlobalTheory.T.incA_smul_mem_adelicCompletionMatrixGroup D S T _ L1 L2 _ hc x hxm
    have h4 := smul_mem_hatA_of_int (fun o y hy => HatLat.smul_mem_tens _ _ o hy) ht h3
    convert h4 using 1
    ext i j
    simp only [Matrix.smul_apply, smul_eq_mul, map_mul]
    have hxij := hx i j
    calc incA D c * x i j = incA D c * (cA D e * x i j) := by rw [hxij]
      _ = (t * incA D (s : D.host.E) * cA D e) * (incA D c * x i j) := by rw [hte]; ring
      _ = t * (incA D (s : D.host.E) * incA D c * (cA D e * x i j)) := by ring
      _ = t * (incA D (s : D.host.E) * incA D c * x i j) := by rw [hxij]
  have hsc : ∀ (I : Ideal (𝓞 D.host.E)) (L1 L2 : Lt D.host.E T.rank) (c : D.host.E), (∀ v ∈ L1, c • v ∈ L2) →
      ∀ v ∈ I • L1, c • v ∈ I • L2 := by
    intro I L1 L2 c hc v hv
    refine Submodule.smul_induction_on hv (fun i hi w hw => ?_) (fun a b ha hb => ?_)
    · rw [smul_comm]
      exact Submodule.smul_mem_smul hi (hc w hw)
    · rw [smul_add]; exact add_mem ha hb
  refine ⟨e * incA D (star γ⁻¹), ⟨e * incA D (star γ), ?_⟩, ?_⟩
  · have hu : incA D (star γ⁻¹) * incA D (star γ) = 1 := by
      rw [← map_mul, star_inv₀, inv_mul_cancel₀ (star_ne_zero.mpr hγ), map_one]
    calc e * incA D (star γ⁻¹) * (e * incA D (star γ)) = (e * e) * (incA D (star γ⁻¹) * incA D (star γ)) :=
          mul_mul_mul_comm _ _ _ _
      _ = e := by rw [hu, mul_one, hee]
  intro x hx
  have hadj : adjA S T βS βT (e * incA D (star γ⁻¹)) x = adjA S T βS βT 1 (incA D γ⁻¹ • x) :=
    GlobalTheory.T.ideleFrameAdjointMatrix_half_idempotent_smul D S T βS βT e γ⁻¹ x hx
  have hy : IsHalf (cA D e) (incA D γ⁻¹ • x) := by
    intro i j
    simp only [Matrix.smul_apply, smul_eq_mul]
    rw [mul_left_comm, hx i j]
  have hyf := hinf _ hy
  have hback : incA D γ • (incA D γ⁻¹ • x) = x := by
    rw [smul_smul, ← map_mul, mul_inv_cancel₀ hγ, map_one, one_smul]
  rw [hadj]
  obtain ⟨hsq, hle, hconj⟩ := GlobalTheory.T.prod_primes_squarefree_conjugateIdeal_prod D (Pg ∪ Q)
  have hmem : ∀ (I : Ideal (𝓞 D.host.E)),
      (incA D γ⁻¹ • x ∈ hatA S T (tens (stdL D.host.E S.rank) (I • ΛT)) ↔
        x ∈ hatA S T (tens (stdL D.host.E S.rank) (I • C.X.Λ))) := by
    intro I
    constructor
    · intro hm
      have := hmulA (I • ΛT) (I • C.X.Λ) γ (hsc I ΛT C.X.Λ _ h2') _ hy hm
      rwa [hback] at this
    · intro hm
      exact hmulA (I • C.X.Λ) (I • ΛT) γ⁻¹ (hsc I C.X.Λ ΛT _ h1) x hx hm
  have hctop : conjI (⊤ : Ideal (𝓞 D.host.E)) = ⊤ := by
    rw [Ideal.eq_top_iff_one]
    unfold conjI
    exact Ideal.subset_span ⟨1, Submodule.mem_top, by simp⟩
  constructor
  · have hB := GlobalTheory.T.ideleFrameAdjoint_integral_iff_dualLattice D S T hS ΛT hsd βS βT hβT ⊤ (by rw [← Ideal.one_eq_top]; exact squarefree_one) _ hyf
    rw [hctop, Submodule.top_smul] at hB
    have h5 := hmem ⊤
    rw [Submodule.top_smul, Submodule.top_smul] at h5
    rw [← h5, ← hB]
    constructor
    · intro h; exact ⟨h, fun PP hPP => absurd (top_le_iff.mp hPP) PP.isPrime.ne_top⟩
    · intro h; exact h.1
  · have hB := GlobalTheory.T.ideleFrameAdjoint_integral_iff_dualLattice D S T hS ΛT hsd βS βT hβT _ hsq _ hyf
    rw [hconj] at hB
    have hB' : (IsIntM (adjA S T βS βT 1 (incA D γ⁻¹ • x)) ∧ ∀ PP : Formalism.L2.DIV.Pl D.host.E,
        (∏ PP ∈ Pg ∪ Q, PP.asIdeal) ≤ PP.asIdeal → redM PP (adjA S T βS βT 1 (incA D γ⁻¹ • x)) = 0) ↔
        incA D γ⁻¹ • x ∈ hatA S T (tens (stdL D.host.E S.rank) (liftI Pg Q • ΛT)) := hB
    have h5 := hmem (liftI Pg Q)
    rw [← h5, ← hB']
    simp only [hle]

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




noncomputable section

namespace GlobalTheory.LiftDat

theorem rowAdj_isIntM_of_mem : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (hn : T.rank ≤ S.rank) (ΛT : Lt D.host.E T.rank), IsSelfDualC T ΛT → IsAA C.X.Λ ΛT → ∀ (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)), Formalism.L2.DIV.IsFrame βS (stdL D.host.E S.rank) → Formalism.L2.DIV.IsFrame βT ΛT → ∀ (Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (ξ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ), Pg.Nonempty → (∀ PP, PP ∈ Pg ∨ PP ∈ Q → (2 : 𝓞 D.host.E) ∉ PP.asIdeal) → ∀ e : AE D, IsIdemSum e (Pg ∪ Q) → ∀ (a : AE D) (k₀ : GA D S), (∃ b : AE D, a * b = e) → GlobalTheory.LiftLevel.IsMover S T βS βT e a k₀ → GlobalTheory.LiftLevel.IsGen C βS βT Pg Q e a → GlobalTheory.LiftLevel.liftI Pg Q ≠ ⊤ → GlobalTheory.LiftLevel.liftI Pg Q ≠ ⊥ → IsCoprime (GlobalTheory.LiftLevel.liftI Pg Q) (conjI (GlobalTheory.LiftLevel.liftI Pg Q)) → IsCoprime (GlobalTheory.LiftLevel.liftI Pg Q) (Ideal.span {2}) → ∀ v ∈ C.X.Λ, IsIntM (GlobalTheory.LiftDat.rowAdj T βT a e v) := by
  intro D S T C hn ΛT hsd hAA βS βT hβS hβT Pg Q ξ hPg h2P e he a k₀ hab hmov hgen h1 h2 h3 h4 v hv
  rcases Nat.eq_zero_or_pos T.rank with h0 | hpos
  · intro i j; exact absurd j.2 (by omega)
  have hS : 0 < S.rank := lt_of_lt_of_le hpos hn
  let i0 : Fin S.rank := ⟨0, hS⟩
  let y : Matrix (Fin S.rank) (Fin T.rank) D.host.E := vecMulVec (Pi.single i0 1) v
  have hy : y ∈ tens (stdL D.host.E S.rank) C.X.Λ :=
    AddSubgroup.subset_closure ⟨_, Submodule.subset_span ⟨i0, rfl⟩, v, hv, rfl⟩
  have hce : cA D e * cA D e = cA D e := by rw [← map_mul, GlobalTheory.PlaceVec.idemSum_mul_self he]
  have hfin : finPart D (cA D e) ∈ intAE D :=
    GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← map_mul, hce])
  have hA : ∀ o : 𝓞 D.host.E, ∀ z ∈ tens (stdL D.host.E S.rank) C.X.Λ,
      (o : D.host.E) • z ∈ tens (stdL D.host.E S.rank) C.X.Λ :=
    fun o z hz => GlobalTheory.LiftLevel.smul_mem_tens o (fun u hu => Submodule.smul_mem _ o hu) hz
  have h0 : finW S T y ∈ hatA S T (tens (stdL D.host.E S.rank) C.X.Λ) := by
    rw [GlobalTheory.Ker.SignVac.finW_eq]; exact GlobalTheory.Ker.SignVac.finTens_mem (GlobalTheory.LatVac.one_mem_intAf _) hy
  have hx : cA D e • finW S T y ∈ hatA S T (tens (stdL D.host.E S.rank) C.X.Λ) :=
    GlobalTheory.LiftLevel.smul_mem_hatA_of_int hA hfin h0
  have hhalf : IsHalf (cA D e) (cA D e • finW S T y) := fun i j => by
    simp only [Matrix.smul_apply, smul_eq_mul, ← mul_assoc, hce]
  have hint := ((hgen _ hhalf).1).2 hx
  have hM : ∀ N : Matrix (Fin S.rank) (Fin T.rank) (EAf D),
      HMul.hMul βS.val (HMul.hMul (HMul.hMul (βS⁻¹).val N) βT.val) = HMul.hMul N βT.val := by
    intro N
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, βS.mul_inv, Matrix.one_mul]
  have key : ∀ j, GlobalTheory.LiftDat.rowAdj T βT a e v 0 j =
      GlobalTheory.LiftLevel.adjA S T βS βT a (cA D e • finW S T y) i0 j := by
    intro j
    simp only [GlobalTheory.LiftLevel.adjA, frMapAdj]
    rw [hM]
    simp only [GlobalTheory.LiftDat.rowAdj, Matrix.smul_apply, C.m.gS, inv_one]
    rw [Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mul]
    congr 1
    simp only [Matrix.mul_apply, Matrix.map_apply, Matrix.of_apply, Matrix.transpose_apply, Matrix.smul_apply,
      smul_eq_mul, finW, y, vecMulVec_apply, Pi.single_eq_same, one_mul, i0]
  intro i j
  rw [Fin.fin_one_eq_zero i, key]
  exact hint i0 j

end GlobalTheory.LiftDat

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopLevelInv

noncomputable section
namespace GlobalTheory.TopLevelInv


open GlobalTheory.PlaceModel GlobalTheory.PlaceDatum GlobalTheory.SplitHecke GlobalTheory.ThetaMove in
theorem vac_high_law (hA : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) {t : T} {μ₀ : T}, L.Is μ₀ → t ∈ U → ∀ {Φ : G.Datum} {β : CosFam G t} (j : ℕ) (hj : j + 1 < D.R.m) (k : FinPt G (.top (j + 1))),
    finG (G.V (.top (j + 1))) k ∈ S.levTop t Φ β (j + 1) hj → ∀ (e : AE D) (he : IsIdemSum e (locPl G t)),
    W.om (.top t (j + 1)) (cutPart (1 - (e + cA D e)) (G.V (.top (j + 1))) ((((S.N.u (.top (j + 1)))⁻¹ * k * S.N.u (.top (j + 1)) : FinPt G (.top (j + 1))) : GA D (G.V (.top (j + 1))))), 1) (S.Z.vac (.top t (j + 1))) = S.Z.vac (.top t (j + 1))) (hC1 : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) {t : T} {μ₀ : T}, L.Is μ₀ → t ∈ U → ∀ {Φ : G.Datum} {β : CosFam G t} (j : ℕ) (hj : j + 1 < D.R.m) (k : FinPt G (.top (j + 1))),
    finG (G.V (.top (j + 1))) k ∈ S.levTop t Φ β (j + 1) hj → ∀ (e : AE D) (he : IsIdemSum e (locPl G t)),
    GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.absFin D (GlobalTheory.VecInv.detAt e (GlobalTheory.PlaceModelSum.isOrthSum_of_isIdemSum he).idem (G.V (.top (j + 1)))
      (cutPart (e + cA D e) (G.V (.top (j + 1))) ((((S.N.u (.top (j + 1)))⁻¹ * k * S.N.u (.top (j + 1)) : FinPt G (.top (j + 1))) : GA D (G.V (.top (j + 1))))))) = 1) (hC2 : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) {t : T} {μ₀ : T}, L.Is μ₀ → t ∈ U → ∀ {Φ : G.Datum} {β : CosFam G t} (j : ℕ) (hj : j + 1 < D.R.m) (k : FinPt G (.top (j + 1))),
    finG (G.V (.top (j + 1))) k ∈ S.levTop t Φ β (j + 1) hj → ∀ (e : AE D) (he : IsIdemSum e (locPl G t)),
    ((L.mu t (j + 1 + 1) (GlobalTheory.VecInv.detAt e (GlobalTheory.PlaceModelSum.isOrthSum_of_isIdemSum he).idem (G.V (.top (j + 1)))
      (cutPart (e + cA D e) (G.V (.top (j + 1))) ((((S.N.u (.top (j + 1)))⁻¹ * k * S.N.u (.top (j + 1)) : FinPt G (.top (j + 1))) : GA D (G.V (.top (j + 1))))))) : Circle) : ℂ) =
      ∏ w : locPl G t, (((locGrid G t w).mu (j + 1 + 1) (gdet (kapAt S t j hj k w)) : ℂˣ) : ℂ)) : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) {t : T} {μ₀ : T}, L.Is μ₀ → t ∈ U → ∀ {Φ : G.Datum} {β : CosFam G t} (j : ℕ) (hj : j + 1 < D.R.m) (k : FinPt G (.top (j + 1))),
    finG (G.V (.top (j + 1))) k ∈ S.levTop t Φ β (j + 1) hj → ∀ e : AE D, IsIdemSum e (locPl G t) →
    ∀ Tm : (WO (G.pS (.top t (j + 1) : Pair T)) (G.pT (.top t (j + 1) : Pair T)) → ℂ) →ₗ[ℂ] (WO (G.pS (.top t (j + 1) : Pair T)) (G.pT (.top t (j + 1) : Pair T)) → ℂ),
      IsPlaceModel W.ψ (symplO _ _) (heisO W.ψ _ _) e (stdLatO S (.top t (j + 1))) 1 (S.Z.vac (.top t (j + 1))) Tm →
      W.om (.top t (j + 1)) ((((S.N.u (.top (j + 1)))⁻¹ * k * S.N.u (.top (j + 1)) : FinPt G (.top (j + 1))) : GA D (G.V (.top (j + 1)))), 1) (S.Z.vac (.top t (j + 1))) =
        (∏ w : locPl G t, ((((locGrid G t w).mu (j + 1 + 1) (gdet (kapAt S t j hj k w)))⁻¹ : ℂˣ) : ℂ)) •
          Tm fun x => halfInd e (stdLatO S (.top t (j + 1))) (actO _ _ (((S.N.u (.top (j + 1)))⁻¹ * k * S.N.u (.top (j + 1)) : FinPt G (.top (j + 1))) : GA D (G.V (.top (j + 1))))⁻¹ 1⁻¹ x) := by
  intro D T L sc G W U S t μ₀ hL ht Φ β j hj k hk e he Tm hTm
  have ho := GlobalTheory.PlaceModelSum.isOrthSum_of_isIdemSum he
  have hee : e * e = e := ho.idem
  have hce : e * cA D e = 0 := he.2
  have hf := idem_conj_sum hee hce
  have hW := W.om_is (.top t (j + 1)) (show j + 1 + 1 ≤ D.R.m by omega)
  have hvac := S.Z.vac_is (.top t (j + 1)) (show j + 1 + 1 ≤ D.R.m by omega)
  have hS := GlobalTheory.FunObj.OrthoFrame.isSelfDualC_colLat_of_orthonormal _ _ (S.N.fr_on (.top (j + 1)) (show j + 1 ≤ D.R.m by omega))
  have hT := GlobalTheory.FunObj.OrthoFrame.isSelfDualC_colLat_of_orthonormal _ _ (S.N.fr_on (.top (j + 1 + 1)) (show j + 1 + 1 ≤ D.R.m by omega))
  set g : GA D (G.V (.top (j + 1))) := ((((S.N.u (.top (j + 1)))⁻¹ * k * S.N.u (.top (j + 1)) : FinPt G (.top (j + 1))) : GA D (G.V (.top (j + 1))))) with hgdef
  have key := GlobalTheory.SplitLinear.splitLinearModel D W.ψ _ _ _ _ _ hW _ _ hS hT (locPl G t) e he _ hvac.2.theta hvac.2.lat 1
    one_ne_zero Tm hTm (cutPart (e + cA D e) _ g) 1 (suppAt_cutPart hee hce _ g) (GlobalTheory.SplitLinear.suppAt_one e _) _ _
    (GlobalTheory.VecInv.isDetAt_detAt e hee _ _) (GlobalTheory.VecInv.isDetAt_detAt e hee _ _) _ (GlobalTheory.isSBHalf_halfInd e _)
  have hvacTm : Tm (halfInd e (stdLatO S (.top t (j + 1)))) = S.Z.vac (.top t (j + 1)) := by
    have := hTm.vac
    rwa [one_smul] at this
  have hr1 : Even (G.V (.top (j + 1 + 1))).rank := by
    rw [GlobalTheory.FunObj.rank_top G (j := j + 1 + 1) (by omega)]; exact GlobalTheory.FunObj.rankX_even D (j + 1 + 1)
  have hr0 : Even (G.V (.top (j + 1))).rank := by
    rw [GlobalTheory.FunObj.rank_top G (j := j + 1) (by omega)]; exact GlobalTheory.FunObj.rankX_even D (j + 1)
  have hTc : G.chrT (.top t (j + 1)) = L.mu t (j + 1 + 1) := by
    simp only [GridData.chrT, Formalism.IndefR.Lift.attChr, GridData.chr, GridData.pT, Nat.not_odd_iff_even.2 hr1, if_false]
  have hc : ((splitFacO (G.chrS (.top t (j + 1) : Pair T)) (G.chrT (.top t (j + 1) : Pair T))
      (GlobalTheory.VecInv.detAt e hee (G.pS (.top t (j + 1) : Pair T)) (cutPart (e + cA D e) _ g))
      (GlobalTheory.VecInv.detAt e hee (G.pT (.top t (j + 1) : Pair T)) 1) : ℂ) *
    (GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.modFac (G.pS (.top t (j + 1) : Pair T)) (G.pT (.top t (j + 1) : Pair T))
      (GlobalTheory.VecInv.detAt e hee (G.pS (.top t (j + 1) : Pair T)) (cutPart (e + cA D e) _ g))
      (GlobalTheory.VecInv.detAt e hee (G.pT (.top t (j + 1) : Pair T)) 1) : ℂ)) =
      ∏ w : locPl G t, ((((locGrid G t w).mu (j + 1 + 1) (gdet (kapAt S t j hj k w)))⁻¹ : ℂˣ) : ℂ) := by
    have h1 : GlobalTheory.VecInv.detAt e hee (G.pT (.top t (j + 1) : Pair T)) 1 = 1 := map_one _
    have h2 := hC1 S hL ht j hj k hk e he
    have h3 := hC2 S hL ht j hj k hk e he
    rw [h1, GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.modFac, h2, hTc]
    simp only [splitFacO, map_one, mul_one, Real.one_rpow, Complex.ofReal_one, Circle.coe_inv]
    have h4 : GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.absFin D 1 = 1 := by simp [GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.absFin, GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.absV]
    simp only [h4, Real.one_rpow, mul_one, Complex.ofReal_one]
    have h5 : ((L.mu t (j + 1 + 1) (GlobalTheory.VecInv.detAt e hee (G.pS (.top t (j + 1) : Pair T)) (cutPart (e + cA D e) _ g)) : Circle) : ℂ) =
        ∏ w : locPl G t, (((locGrid G t w).mu (j + 1 + 1) (gdet (kapAt S t j hj k w)) : ℂˣ) : ℂ) := h3
    rw [h5, ← Finset.prod_inv_distrib]
    simp only [Units.val_inv_eq_inv_val]
  calc W.om (.top t (j + 1)) (g, 1) (S.Z.vac (.top t (j + 1)))
      = W.om (.top t (j + 1)) (cutPart (e + cA D e) _ g, 1)
          (W.om (.top t (j + 1)) (cutPart (1 - (e + cA D e)) _ g, 1) (S.Z.vac (.top t (j + 1)))) := by
        rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one, ← cutPart_mul hf]
    _ = W.om (.top t (j + 1)) (cutPart (e + cA D e) _ g, 1) (S.Z.vac (.top t (j + 1))) := by
        rw [hA S hL ht j hj k hk e he]
    _ = _ := by
        rw [← hvacTm]
        erw [key]
        rw [← hc]
        conv_rhs => rw [← map_smul]
        congr 1
        funext x
        rw [Pi.smul_apply, smul_eq_mul, GlobalTheory.SplitLinear.subst_eq, halfInd_cutPart hee hce]
        rfl

theorem vac_move_high_eq : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) {t : T} {μ₀ : T}, L.Is μ₀ → t ∈ U → ∀ {Φ : G.Datum} {β : CosFam G t} (j : ℕ) (hj : j + 1 < D.R.m) (k : FinPt G (.top (j + 1))),
    finG (G.V (.top (j + 1))) k ∈ S.levTop t Φ β (j + 1) hj → ∀ e : AE D, IsIdemSum e (locPl G t) →
    ∀ Tm : (WO (G.pS (.top t (j + 1) : Pair T)) (G.pT (.top t (j + 1) : Pair T)) → ℂ) →ₗ[ℂ] (WO (G.pS (.top t (j + 1) : Pair T)) (G.pT (.top t (j + 1) : Pair T)) → ℂ),
      IsPlaceModel W.ψ (symplO _ _) (heisO W.ψ _ _) e (stdLatO S (.top t (j + 1))) 1 (S.Z.vac (.top t (j + 1))) Tm →
      W.om (.top t (j + 1)) ((((S.N.u (.top (j + 1)))⁻¹ * k * S.N.u (.top (j + 1)) : FinPt G (.top (j + 1))) : GA D (G.V (.top (j + 1)))), 1) (S.Z.vac (.top t (j + 1))) =
        (∏ w : locPl G t, ((((locGrid G t w).mu (j + 1 + 1) (gdet (kapAt S t j hj k w)))⁻¹ : ℂˣ) : ℂ)) •
          Tm fun x => halfInd e (stdLatO S (.top t (j + 1))) (actO _ _ (((S.N.u (.top (j + 1)))⁻¹ * k * S.N.u (.top (j + 1)) : FinPt G (.top (j + 1))) : GA D (G.V (.top (j + 1))))⁻¹ 1⁻¹ x) :=
  vac_high_law (by intros; apply GlobalTheory.T.offPlacePart_fixes_standardVacuum <;> assumption) (by intros; apply GlobalTheory.T.finiteIdeleModulus_conjLevelDet_eq_one <;> assumption)
    (by intros; apply GlobalTheory.T.gridTupleHeckeCharacter_detIdele_eq_prod_local <;> assumption)

end GlobalTheory.TopLevelInv

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree

noncomputable section

namespace GlobalTheory.SquareAgree

theorem isDatum_zero_zero {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {n d : ℕ} {Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {Wd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d} (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ Y Wd)
    (ψ : AddChar (AF F) ℂ) {Z : Type} (crd : Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) → Z) :
    IsDatum M ψ crd 0 0 := by
  refine ⟨zero_mem _, fun u => ?_⟩
  simp [GlobalTheory.WeilM.thetaSum, GlobalTheory.WeilM.Darboux.rho, GlobalTheory.WeilM.schr]

theorem isDatum_smul_smul {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {n d : ℕ} {Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {Wd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d} (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ Y Wd)
    (ψ : AddChar (AF F) ℂ) {Z : Type} (crd : Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) → Z)
    {Φ : (Fin n × Fin d → AF F) → ℂ} {f : Z → ℂ} (h : IsDatum M ψ crd Φ f) (c : ℂ) :
    IsDatum M ψ crd (c • Φ) (c • f) := by
  refine ⟨Submodule.smul_mem _ _ h.1, fun u => ?_⟩
  rw [Pi.smul_apply, ← h.2 u]
  simp only [GlobalTheory.WeilM.thetaSum, GlobalTheory.WeilM.Darboux.rho, GlobalTheory.WeilM.schr, Pi.smul_apply, smul_eq_mul]
  rw [← tsum_mul_left]
  exact tsum_congr fun η => mul_left_comm _ _ _

theorem algVec_correspond : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsInfFam θ →
    ∀ (ε : Bool) (S X : HSp D) (A : Fr S) (B : Fr X) {d : ℕ} (e : Fin X.rank ≃ Fin d)
      (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E), Bs.IsGood D.sp.cm.sig → Bs.ψ = ψ →
    ∀ (Vs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E S.rank) (Ws : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E d) (r s r' s' : ℕ)
      (hJ : Vs.J = (if ε then 1 else -1 : D.host.E) • S.gram) (hJW : Ws.J = D.host.xi0 • reindex e e X.gramᵀ),
      Vs.IsHerm D.sp.cm.sig Bs r s → Ws.IsSkew D.sp.cm.sig Bs r' s' →
      (∀ w, ∃ τ, (∀ x, (Bs.emb w).1 x = starRingEnd ℂ (tauE D τ x)) ∧ Vs.θ w = (if ε then 1 else -1 : ℂ) • A.cart τ ∧
        Ws.θ w = (reindex e e (B.cart τ)).map (starRingEnd ℂ)) →
    ∀ M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model D.sp.cm.sig Vs Ws, M.IsGood Bs.ψ →
    ∀ cS : Matrix (Fin S.rank) (Fin d) (AE D) ≃+ WO S X,
      (∀ u, cS u = (HMul.hMul (uᵀ.submatrix e id) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM ((if ε then -1 else 1 : D.host.E) • S.gram)) : Matrix (Fin X.rank) (Fin S.rank) (AE D))) →
      (∀ Φ ∈ algF ψ θ ε A B, ∃ ΦD ∈ algD M Bs.ψ Bs.emb, IsDatum M ψ cS ΦD Φ) ∧
      ∀ ΦD ∈ algD M Bs.ψ Bs.emb, ∃ Φ ∈ algF ψ θ ε A B, IsDatum M ψ cS ΦD Φ := by
  intro D ψ θ hθ ε S X A B d e Bs hBs hψ Vs Ws r s r' s' hJ hJW hVs hWs hcart M hM cS hcS
  have hstd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ := hψ ▸ hBs.std
  have hadd : ∀ {Φ Φ' : (Fin S.rank × Fin d → AF D.host.F) → ℂ} {f f' : WO S X → ℂ},
      IsDatum M ψ cS Φ f → IsDatum M ψ cS Φ' f' → IsDatum M ψ cS (Φ + Φ') (f + f') :=
    fun h h' => GlobalTheory.T.isSchrodingerThetaDatum_add_adelicSchwartz M ψ hstd cS _ _ _ _ h h'

  set Aop := aPlusAll (heisO ψ (sgn ε S) X) θ (fun τ => cplxO ((frSgn ε A).cart τ) (B.cart τ)) A.onb B.onb with hAop
  have hfock : ∀ f P, fockF ψ θ ε A B f P = pureTensorL Aop f P := fun f P => rfl
  have step : ∀ g : WO S X → ℂ, (∃ ΦD ∈ algD M Bs.ψ Bs.emb, IsDatum M ψ cS ΦD g) →
      ∀ k, ∃ ΦD ∈ algD M Bs.ψ Bs.emb, IsDatum M ψ cS ΦD (Aop k g) := by
    rintro g ⟨ΦD, hD, hd⟩ k
    obtain ⟨a, ha, h1⟩ := GlobalTheory.T.realPlaceHeisenbergDeriv_thetaTransform_algebraicDatum D ψ θ hθ ε S X A B e Bs hBs hψ Vs Ws r s r' s' hJ hJW hVs hWs hcart M hM cS hcS ΦD hD g hd k.1
      (unitMap (A.onb k.1) (B.onb k.1) k.2.1 k.2.2)
    obtain ⟨b, hb, h2⟩ := GlobalTheory.T.realPlaceHeisenbergDeriv_thetaTransform_algebraicDatum D ψ θ hθ ε S X A B e Bs hBs hψ Vs Ws r s r' s' hJ hJW hVs hWs hcart M hM cS hcS ΦD hD g hd k.1
      (cplxO ((frSgn ε A).cart k.1) (B.cart k.1) (unitMap (A.onb k.1) (B.onb k.1) k.2.1 k.2.2))
    refine ⟨((fockScale D k.1 : ℂ)⁻¹) • (a + (-Complex.I) • b),
      Submodule.smul_mem _ _ (add_mem ha (Submodule.smul_mem _ _ hb)), ?_⟩
    have e1 := isDatum_smul_smul M ψ cS (hadd h1 (isDatum_smul_smul M ψ cS h2 (-Complex.I))) ((fockScale D k.1 : ℂ)⁻¹)
    convert e1 using 1
    simp only [hAop, aPlusAll, aPlus, crea, sub_eq_add_neg, neg_smul]
  have gen : ∀ f, IsFinF ψ θ ε A B f → ∀ P, ∃ ΦD ∈ algD M Bs.ψ Bs.emb, IsDatum M ψ cS ΦD (fockF ψ θ ε A B f P) := by
    intro f hf P
    have h0 := GlobalTheory.T.exists_algebraicDatum_thetaTransform_eq D ψ θ hθ ε S X A B e Bs hBs hψ Vs Ws r s r' s' hJ hJW hVs hWs hcart M hM cS hcS f hf
    have hl : ∀ l : List (FVar D X.rank S.rank), ∃ ΦD ∈ algD M Bs.ψ Bs.emb,
        IsDatum M ψ cS ΦD (l.foldr (fun i g => Aop i g) f) := by
      intro l
      induction l with
      | nil => exact h0
      | cons k l ih => exact step _ ih k
    rw [hfock]
    induction P using MvPolynomial.induction_on' with
    | monomial u a =>
      have em : MvPolynomial.monomial u a = a • MvPolynomial.basisMonomials (FVar D X.rank S.rank) ℂ u := by
        rw [MvPolynomial.coe_basisMonomials, MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
      obtain ⟨ΦD, hD, hd⟩ := hl (Multiset.toList (Finsupp.toMultiset u))
      refine ⟨a • ΦD, Submodule.smul_mem _ _ hD, ?_⟩
      rw [em, map_smul]
      unfold pureTensorL
      rw [Module.Basis.constr_basis]
      exact isDatum_smul_smul M ψ cS hd a
    | add p q hp hq =>
      obtain ⟨a, ha, h1⟩ := hp
      obtain ⟨b, hb, h2⟩ := hq
      exact ⟨a + b, add_mem ha hb, by rw [map_add (f := _)]; exact hadd h1 h2⟩
  have fin_mem : ∀ f, IsFinF ψ θ ε A B f → f ∈ algF ψ θ ε A B := by
    intro f hf
    refine Submodule.subset_span ⟨f, 1, hf, ?_⟩
    have e1 : (1 : MvPolynomial (FVar D X.rank S.rank) ℂ) = MvPolynomial.basisMonomials (FVar D X.rank S.rank) ℂ 0 := by
      rw [MvPolynomial.coe_basisMonomials]; rfl
    rw [hfock, e1]
    unfold pureTensorL
    rw [Module.Basis.constr_basis]
    simp [opPow]
  refine ⟨fun Φ hΦ => ?_, fun ΦD hΦD => ?_⟩
  · induction hΦ using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨f, P, hf, rfl⟩ := hx
      exact gen f hf P
    | zero => exact ⟨0, zero_mem _, isDatum_zero_zero M ψ cS⟩
    | add x y _ _ hx hy =>
      obtain ⟨a, ha, h1⟩ := hx
      obtain ⟨b, hb, h2⟩ := hy
      exact ⟨a + b, add_mem ha hb, hadd h1 h2⟩
    | smul c x _ hx =>
      obtain ⟨a, ha, h1⟩ := hx
      exact ⟨c • a, Submodule.smul_mem _ _ ha, isDatum_smul_smul M ψ cS h1 c⟩
  · have pure_add : ∀ (g g' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf D.host.F (Fin S.rank × Fin d)) (φ : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.F), (Fin S.rank × Fin d → v.adicCompletion D.host.F) → ℂ),
        GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (g + g') φ = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g φ + GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g' φ := by
      intro g g' φ; funext x; simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, add_mul]
    have pure_smul : ∀ (c : ℂ) (g : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf D.host.F (Fin S.rank × Fin d)) (φ : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.F), (Fin S.rank × Fin d → v.adicCompletion D.host.F) → ℂ),
        GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (c • g) φ = c • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g φ := by
      intro c g φ; funext x; simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, mul_assoc]
    have pure_zero : ∀ (φ : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.F), (Fin S.rank × Fin d → v.adicCompletion D.host.F) → ℂ),
        GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (0 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf D.host.F (Fin S.rank × Fin d)) φ = 0 := by
      intro φ; funext x; simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure]
    let N : Submodule ℂ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf D.host.F (Fin S.rank × Fin d)) :=
      { carrier := {g | ∀ (φ : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.F), (Fin S.rank × Fin d → v.adicCompletion D.host.F) → ℂ), (∀ v, φ v ∈ GlobalTheory.WeilM.SB _) → (∀ᶠ v in Filter.cofinite, φ v = M.vac v) →
          ∃ f ∈ algF ψ θ ε A B, IsDatum M ψ cS (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g φ) f}
        zero_mem' := fun φ _ _ => ⟨0, zero_mem _, by rw [pure_zero]; exact isDatum_zero_zero M ψ cS⟩
        add_mem' := by
          intro g g' hg hg' φ h1 h2
          obtain ⟨a, ha, d1⟩ := hg φ h1 h2
          obtain ⟨b, hb, d2⟩ := hg' φ h1 h2
          exact ⟨a + b, add_mem ha hb, by rw [pure_add]; exact hadd d1 d2⟩
        smul_mem' := by
          intro c g hg φ h1 h2
          obtain ⟨a, ha, d1⟩ := hg φ h1 h2
          exact ⟨c • a, Submodule.smul_mem _ _ ha, by rw [pure_smul]; exact isDatum_smul_smul M ψ cS d1 c⟩ }
    have hPol : M.Pol Bs.ψ Bs.emb ≤ N := by
      refine sInf_le ⟨fun g₀ hg₀ φ h1 h2 => ?_, fun u hu g hg g₁ hg₁ φ h1 h2 => ?_⟩
      · obtain ⟨f, hf, hd⟩ := GlobalTheory.T.thetaTransform_gaussianVacuum_isFiniteDatum D ψ θ hθ ε S X A B e Bs hBs hψ Vs Ws r s r' s' hJ hJW hVs hWs hcart M hM cS hcS g₀ φ hg₀ h1 h2
        exact ⟨f, fin_mem f hf, hd⟩
      · obtain ⟨f, hf, hd⟩ := hg φ h1 h2
        exact GlobalTheory.T.exists_algebraicVector_thetaTransform_heisenbergDerivative D ψ θ hθ ε S X A B e Bs hBs hψ Vs Ws r s r' s' hJ hJW hVs hWs hcart M hM cS hcS g φ h1 h2 f hf hd u hu g₁ hg₁
    induction hΦD using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨g, φ, hg, h1, h2, rfl⟩ := hx
      exact hPol hg φ h1 h2
    | zero => exact ⟨0, zero_mem _, isDatum_zero_zero M ψ cS⟩
    | add x y _ _ hx hy =>
      obtain ⟨a, ha, h1⟩ := hx
      obtain ⟨b, hb, h2⟩ := hy
      exact ⟨a + b, add_mem ha hb, hadd h1 h2⟩
    | smul c x _ hx =>
      obtain ⟨a, ha, h1⟩ := hx
      exact ⟨c • a, Submodule.smul_mem _ _ ha, isDatum_smul_smul M ψ cS h1 c⟩

end GlobalTheory.SquareAgree

end
end
