module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle012
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FinTensMemLatO
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle326
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle159
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle397
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2536
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOverBoth
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergOperatorFinitePartLatticeVacuumSign
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle088
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.FinPartDetAtInvInt
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.AlternatingFormStandardHermitian
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle016
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle495
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle018
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle017
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle020
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle004
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle515
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle021
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle396
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle514
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle488
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle445
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle292
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle118
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle007
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle202
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle237
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle333
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle518
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HeckeFormNSOfHeckeForm
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle516
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle066
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle004
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.StabOrd
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.HalfBInt

variable {D : D7}

theorem selfDualC_of (V : HSp D) (hV : V.gram = 1) (N : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E))
    (h : Formalism.L2.Col.IsSdLat N) : IsSelfDualC V N := by
  refine ⟨h.1, fun y => ?_⟩
  have h2 : Formalism.HermitianLatticesTheory.dual (Formalism.L2.Col.hStd D.host.E V.rank) N = N := h.2
  conv_lhs => rw [← h2]
  simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap,
    LinearMap.restrictScalars_apply, Submodule.mem_one]
  refine forall_congr' fun x => imp_congr_right fun _ => ?_
  have e : Formalism.L2.Col.hStd D.host.E V.rank x y = ∑ i, ∑ j, star (x i) * V.gram i j * y j := by
    rw [hV]
    simp [Formalism.L2.Col.hStd, Matrix.one_apply]
  rw [e]

theorem noConj {e : AE D} {SS : Finset (Formalism.L2.DIV.Pl D.host.E)} (hE : IsIdemSum e SS) :
    ∀ P ∈ SS, Formalism.L2.Col.conjPrime₂ P ∉ SS := by
  obtain ⟨⟨es, hes, he⟩, hc⟩ := hE
  intro P hP hP'
  have hv : Formalism.IndefR.Fin.belowPl P = Formalism.IndefR.Fin.belowPl (Formalism.L2.Col.conjPrime₂ P) :=
    HeightOneSpectrum.ext (congrArg HeightOneSpectrum.asIdeal (GlobalTheory.GridPlaces.under_conjP P)).symm
  have h := Formalism.IndefR.Fin.LevelGroupLemmas.idemSum_below_inj hes he hc hP hP' hv
  exact GlobalTheory.ModulusNorm.conjPl_ne_of_isIdemAt (hes P hP) ((GlobalTheory.PlaceDict.conjP_eq_conjPl D P).symm.trans h.symm)

end GlobalTheory.HalfBInt


open GlobalTheory.HalfBInt in
theorem GlobalTheory.HalfBInt.trace_int : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (a b : ℕ) (hS : S.rank = a) (hT : T.rank = b) (δ : ℂ) (sc : ℝ), StdPair θ S T δ sc ψ → ∀ (e : AE D) (SS : Finset (Formalism.L2.DIV.Pl D.host.E)), IsIdemSum e SS → ∀ (N : Submodule (𝓞 D.host.E) (Fin a → D.host.E)) (N' : Submodule (𝓞 D.host.E) (Fin b → D.host.E)) (c : ℕ), 0 < c → Odd c → (∀ Q ∈ SS, ((D.host.QS * D.host.q * D.host.d : ℕ) : 𝓞 D.host.E) ∉ Q.asIdeal) → ∀ (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → (ΛS : Set (Fin S.rank → D.host.E)) = latFr S hS N → (ΛT : Set (Fin T.rank → D.host.E)) = latFr T hT N' → ∀ y ∈ halfBO SS (perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N') c, ∃ k : ℤ, (k : ℚ) = Algebra.trace ℚ D.host.E (D.host.xi0 * ((1 + D.host.sqrtMinusD) / 2) ^ 2 * GlobalTheory.LatVac.hRat S T ((LinearMap.toMatrix' (y)).reindex (finCongr hT.symm) (finCongr hS.symm)) ((LinearMap.toMatrix' (y)).reindex (finCongr hT.symm) (finCongr hS.symm))) := by
  intro D ψ θ S T a b hS hT δ sc hP e SS hE N N' c hc _ _ ΛS ΛT dS dT eS eT y hy
  subst hS hT
  obtain rfl : ΛS = N := SetLike.coe_injective eS
  obtain rfl : ΛT = N' := SetLike.coe_injective eT
  have hnc := noConj hE
  have hyT : y ∈ perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) ΛS (twist₂ ΛT c (expS SS)) := by
    rw [← Formalism.L2.Ker.twist_homomorphism _ _ _ _ ΛS ΛT c _ dS.1.fg hc]
    exact hy
  have hsdT := (GlobalTheory.ThetaMove.TwistSd.isSdLat_twO_expS _ _ ΛT c SS hnc (GlobalTheory.StdMove.isSdLat_of T hP.gT ΛT dT) hc).1
  have dT' : IsSelfDualC T (twist₂ ΛT c (expS SS)) := selfDualC_of T hP.gT _ hsdT
  have hrat := GlobalTheory.AdForm.RatLatPer.finRat_mem_latO_of_perO D ψ θ S T _ _ rfl rfl δ sc hP ΛS (twist₂ ΛT c (expS SS)) ΛS (twist₂ ΛT c (expS SS)) dS dT' rfl rfl y hyT
  have hneg : GlobalTheory.VacUnique.finRat S T (-((LinearMap.toMatrix' y).reindex (finCongr (rfl : T.rank = T.rank).symm) (finCongr (rfl : S.rank = S.rank).symm))) ∈
      latO S T ((ΛS : Set (Fin S.rank → D.host.E))) ((twist₂ ΛT c (expS SS) : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) : Set (Fin T.rank → D.host.E)) (fun _ => True) := by
    rw [map_neg]
    exact neg_mem hrat
  have h0 : IsLatVac (heisO ψ S T) (latO S T ((ΛS : Set (Fin S.rank → D.host.E))) ((twist₂ ΛT c (expS SS) : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) : Set (Fin T.rank → D.host.E)) (fun _ => True)) (0 : WO S T → ℂ) :=
    ⟨fun _ _ => by funext w; simp [heisO], fun _ _ _ _ _ => by funext w; simp [heisO]⟩
  obtain ⟨k, hk, -⟩ := GlobalTheory.LatVacSign.heisO_finRat_sign ψ S T ΛS (twist₂ ΛT c (expS SS)) hP.std dS dT' 0 h0 _ hneg
  exact ⟨k, hk⟩
end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep
open GlobalTheory.FinZeta (Gv embV Kv VacFin IsLocKer KerU)
open GlobalTheory.SphTheta (IsStd CayleyRule intMat liftPar)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke IsCommensurated Tj SatU ordL Ov)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ChainOnto

theorem transferOn_all : GlobalTheory.Hk3.HoweUnram → ∀ D : D7, TransferOn D fun _ => True := by
  intro hH D ψ S T χS χT om hW t ht v _
  by_cases hv : IsSplit (E := D.host.E) v
  · exact GlobalTheory.T.sphericalParameterTransfer_splitPlace D ψ S T χS χT om hW t ht v hv
  · exact GlobalTheory.T.sphericalTransfer_weilPairing_inertPlaces hH D ψ S T χS χT om hW t ht v hv

end GlobalTheory.ChainOnto

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing GlobalTheory.AdForm
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.AdForm

theorem diaSum_iff : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : TwDat I l Z u a Ch), A.Is → ∀ θ, IsInfFam θ → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type)
    (p : ι → SplitPt (I.rec7 l Z) k) (β : ∀ j i, Frame (p i) ((I.rec7 l Z).sp.X j) (Fin ((I.rec7 l Z).sp.X j).rank))
    (Q : ∀ j, ι → Pair k (Fin ((I.rec7 l Z).sp.X j).rank)) (L : ∀ j, Lat ((I.rec7 l Z).sp.X j)),
    StdT I l Z u p β Q L → ∀ j (hj : j ≤ B.R.m), ∀ φ ∈ (I.fm l u a).Fi j, ∀ (i : ι) (v : (I.atT l u a).vT), Formalism.L2.NTheta.IsIdemAt (p i).e v.1 →
    ∀ g : 𝓀[k]ˣ → GL (Fin ((I.rec7 l Z).sp.X j).rank) k, (∀ s, g s • Q j i = s • Q j i) →
      ((∀ b y, ∑ᶠ s, rTrans ((β j i).gl (g s)) (A.rd θ j hj b φ y) = 0) ↔
        ∀ c, ∑ᶠ s : ((I.atT l u a).Fv v)ˣ, (I.fm l u a).dilT j v s c (φ ((I.fm l u a).dil j v s c)) = 0) := by
  intro B X I hI hP l Z u a Ch A hA θ hθ k _ _ _ _ ι p β Q L hS j hj φ hφ i v hv g hg
  have hfin : ∀ (f : 𝓀[k]ˣ → GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j) → ℂ) x, (∑ᶠ s, f s) x = ∑ᶠ s, f s x :=
    fun f x => finsum_apply (Set.toFinite _) x
  constructor
  · intro H c
    funext y
    have h1 := congrFun (H (A.chOf j c) y) (A.h j _ ⟨c, rfl⟩)
    rw [hfin] at h1
    simp only [GlobalTheory.MixPer.rTrans] at h1
    rw [GlobalTheory.T.representative_diamond_translate_sum_scalarForm I hI hP l Z u a Ch A hA θ hθ k ι p β Q L hS j hj φ hφ i v hv g hg _ y ⟨c, rfl⟩] at h1
    simpa using h1
  · intro H b y
    funext x
    rw [hfin]
    simp only [GlobalTheory.MixPer.rTrans, Pi.zero_apply]
    refine GlobalTheory.T.diamondTranslateSum_eq_zero_of_chartRepresentatives I hI hP l Z u a Ch A hA θ hθ k ι p β Q L hS j hj φ hφ i v hv g hg b y (fun c y' => ?_) x
    rw [GlobalTheory.T.representative_diamond_translate_sum_scalarForm I hI hP l Z u a Ch A hA θ hθ k ι p β Q L hS j hj φ hφ i v hv g hg b y' c]
    exact congrFun (H c.1) y'

end GlobalTheory.AdForm
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker
open GlobalTheory.SeeSaw GlobalTheory.Unf

theorem _root_.GlobalTheory.T.finiteDatum_basePoints_law_rational_twistPrimes : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : TwDat I l Z u a Ch), A.Is → ∀ (i : ℕ) (hi : i + 1 ≤ B.R.m) α γ (k : ℕ), 0 < k → (∀ (z₁ z₂ : Matrix (Fin ((I.rec7 l Z).sp.X (i + 1)).rank) (Fin ((I.rec7 l Z).sp.X i).rank) (I.rec7 l Z).host.E) (t : WO ((I.rec7 l Z).sp.X i) ((I.rec7 l Z).sp.X (i + 1))), t ∈ stdHom _ _ → IsHalf A.e t → z₁.map (fun r => A.e * incA (I.rec7 l Z) r) = z₂.map (fun r => A.e * incA (I.rec7 l Z) r) + k • t → A.xi i hi α γ z₁ = A.xi i hi α γ z₂) → ∀ (κ : A.U i α) (κ' : A.U (i + 1) γ), (∀ P ∈ I.Q a, ∃ M : Matrix (Fin (B.R.N i)) (Fin (B.R.N i)) B.host.E, ∀ r s, adAt B.host.F P ((finM _ (rankN (I.rec7 l Z) i (Nat.le_of_succ_le hi)) κ.1 : Matrix (Fin (B.R.N i)) (Fin (B.R.N i)) (Formalism.L2.DIV.AfE B.host.F B.host.E)) r s) = algebraMap B.host.E _ (M r s)) → (∀ P ∈ I.Q a, ∃ M : Matrix (Fin (B.R.N (i + 1))) (Fin (B.R.N (i + 1))) B.host.E, ∀ r s, adAt B.host.F P ((finM _ (rankN (I.rec7 l Z) (i + 1) hi) κ'.1 : Matrix (Fin (B.R.N (i + 1))) (Fin (B.R.N (i + 1))) (Formalism.L2.DIV.AfE B.host.F B.host.E)) r s) = algebraMap B.host.E _ (M r s)) → ∀ x y, IsDetRoot _ κ.1 x → IsDetRoot _ κ'.1 y → ∀ (z z' : Matrix (Fin ((I.rec7 l Z).sp.X (i + 1)).rank) (Fin ((I.rec7 l Z).sp.X i).rank) (I.rec7 l Z).host.E) (v : WO ((I.rec7 l Z).sp.X i) ((I.rec7 l Z).sp.X (i + 1))), v ∈ stdHom _ _ → IsHalf A.e v → actO _ _ κ.1⁻¹ κ'.1⁻¹ (z.map fun r => A.e * incA (I.rec7 l Z) r) = z'.map (fun r => A.e * incA (I.rec7 l Z) r) + k • v → (A.chr (i + 1) x : ℂ)⁻¹ * (A.chr (i + 1) y : ℂ) * A.xi i hi α γ z' = ((A.chi i α κ : ℂˣ) : ℂ)⁻¹ * ((A.chi (i + 1) γ κ' : ℂˣ) : ℂ) * A.xi i hi α γ z := by
  first | exact @GlobalTheory.AdForm.ReadLaw.law_read | exact GlobalTheory.AdForm.ReadLaw.law_read | (intros; apply GlobalTheory.AdForm.ReadLaw.law_read <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.seeSawWeilBiAction_commutes : ∀ D : D7, BiAct D := by
  first | exact @GlobalTheory.SeeSaw.biAct_all | exact GlobalTheory.SeeSaw.biAct_all | (intros; apply GlobalTheory.SeeSaw.biAct_all <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker
open GlobalTheory.SeeSaw GlobalTheory.Unf

theorem _root_.GlobalTheory.T.chainStepKernel_preserves_levelRamifiedForms : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (a : I.ι) (i : ℕ), i < B.R.m → ∀ φ : ColT I l u a i, RamT i φ → RamT (i + 1) ((I.chain l u a).K i φ) := by
  first | exact @GlobalTheory.KRamT.kernel_keeps_ramT | exact GlobalTheory.KRamT.kernel_keeps_ramT | (intros; apply GlobalTheory.KRamT.kernel_keeps_ramT <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.LiftRows (Given)

theorem _root_.GlobalTheory.T.realTupleTwistedChain_of_scalarHypotheses : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Given R F → ∀ h : RangeX R, RChain R h := by
  first | exact @GlobalTheory.ChainTw.rChain_of_given | exact GlobalTheory.ChainTw.rChain_of_given | (intros; apply GlobalTheory.ChainTw.rChain_of_given <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.LiftRows (Given)

theorem _root_.GlobalTheory.T.realDatumNormShrink_of_scalarHypotheses : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Given R F → RNrm R := by
  first | exact @GlobalTheory.ChainTw.RNrmProof.rNrm_of_given | exact GlobalTheory.ChainTw.RNrmProof.rNrm_of_given | (intros; apply GlobalTheory.ChainTw.RNrmProof.rNrm_of_given <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.LiftRows (Given)

theorem _root_.GlobalTheory.T.realQuotientVolumeGrowth_of_scalarHypotheses : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Given R F → (∀ h : RangeX R, RChain R h) → RangeX R → RVol R := by
  first | exact @GlobalTheory.ChainTw.VolScale.rVol_of_given | exact GlobalTheory.ChainTw.VolScale.rVol_of_given | (intros; apply GlobalTheory.ChainTw.VolScale.rVol_of_given <;> assumption)
end

section

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing GlobalTheory.KJInf
open scoped TensorProduct Pointwise
namespace GlobalTheory.AdForm.TransAct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem mem_Fi : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : TwDat I l Z u a Ch), A.Is → ∀ θ, IsInfFam θ → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type)
    (p : ι → SplitPt (I.rec7 l Z) k) (β : ∀ j i, Frame (p i) ((I.rec7 l Z).sp.X j) (Fin ((I.rec7 l Z).sp.X j).rank))
    (Q : ∀ j, ι → Pair k (Fin ((I.rec7 l Z).sp.X j).rank)) (L : ∀ j, Lat ((I.rec7 l Z).sp.X j)),
    StdT I l Z u p β Q L → ∀ j (hj : j ≤ B.R.m) (c : GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j) →₀ ℂ),
      (∀ g ∈ c.support, g ∈ grpAt _ fun x => ∃ i, x = (p i).v) → ∀ φ ∈ (I.fm l u a).Fi j,
      (∀ b y i g, g • Q j i = Q j i → rTrans ((β j i).gl g) (trc c (A.rd θ j hj b φ y)) = trc c (A.rd θ j hj b φ y)) →
      (fun e z => trc c (A.rd θ j hj (A.chOf j e) φ z) (A.h j (A.chOf j e) ⟨e, rfl⟩) : ColT I l u a j) ∈ (I.fm l u a).Fi j := by
  intro B X I hI hP l Z u a Ch A hA θ hθ k _ _ _ _ ι p β Q L hS j hj c hc φ hφ hinv e
  exact ⟨GlobalTheory.T.heckeCombination_scalarForm_values_mem_weylModule I hI hP l Z u a Ch A hA θ hθ k ι p β Q L hS j hj c hc φ hφ hinv e,
    fun s => GlobalTheory.T.heckeCombination_scalarForm_values_stabiliser_invariant I hI hP l Z u a Ch A hA θ hθ k ι p β Q L hS j hj c hc φ hφ hinv e s⟩

theorem twTransAct : TwTrans' := by
  intro B X I hI hP l Z u a Ch A hA θ hθ k _ _ _ _ ι p β Q L hS j hj c hc φ hφ hinv
  refine ⟨_, mem_Fi I hI hP l Z u a Ch A hA θ hθ k ι p β Q L hS j hj c hc φ hφ hinv, fun b y => funext fun g => ?_⟩
  obtain ⟨γ, hγ, e, g', hg', κ, hκ, rfl⟩ := (GlobalTheory.T.chartLevels_reps_represent_unitaryDoubleCosets I hI hP l Z u a Ch A hA j hj b).1.dec g
  obtain ⟨e, rfl⟩ := e
  let M : (I.rec7 l Z).what₂.Tau → Matrix (Fin (B.R.N j)) (Fin (B.R.N j)) ℂ := infM θ _ (rankN (I.rec7 l Z) j hj) g'
  have hu : ∀ τ, IsUnit (M τ * y.1 τ).det := fun τ => by
    rw [Matrix.det_mul]; exact (RdVal.infM_unit θ _ (rankN (I.rec7 l Z) j hj) g' τ).mul (y.2 τ)
  let y' : (I.chain l u a).Y j := ⟨fun τ => M τ * y.1 τ, hu⟩
  have htr : IsTr (G := fun _ => 1) (infM θ _ (rankN (I.rec7 l Z) j hj) g') ⟨y.1, y.2⟩ ⟨y'.1, y'.2⟩ := fun τ => rfl
  have h1 := (GlobalTheory.T.scalarForms_on_charts_of_trueColumnTuple I hI hP l Z u a Ch A hA θ hθ j hj _
    (mem_Fi I hI hP l Z u a Ch A hA θ hθ k ι p β Q L hS j hj c hc φ hφ hinv)).2 (A.chOf j e) y γ hγ ⟨e, rfl⟩ g' hg' ⟨κ, hκ⟩ y' htr
  rw [h1, GlobalTheory.T.heckeCombination_scalarForm_keeps_adelicLaws I hI hP l Z u a Ch A hA θ hθ k ι p β Q L hS j hj c hc φ hφ hinv _ y γ hγ ⟨e, rfl⟩ g' hg' ⟨κ, hκ⟩ y' htr]

end GlobalTheory.AdForm.TransAct
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.PairLift GlobalTheory.Chain.RealIt
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ChainOnto

variable {D : D7}

theorem multT_le_noLevel {V : HSp D} {S : D.what₂.Tau → SPar} (θ : InfFam D) (M : DSModel V S) (J : Set (GA D V))
    (χ : GA D V → ℂ) : MultT θ M J χ ≤ MultT θ M ∅ 1 := by
  intro x hx
  rw [mem_multT] at hx ⊢
  refine Submodule.span_mono ?_ hx
  intro T hT
  exact ⟨hT.aut, hT.cusp, fun v k hk => absurd hk (Set.notMem_empty k), hT.equiv, hT.cont⟩

theorem conj_inv_of_norm_one {z : ℂ} (hz : ‖z‖ = 1) : conj z⁻¹ = z := by
  have h1 : Complex.normSq z = 1 := by rw [Complex.normSq_eq_norm_sq, hz]; norm_num
  rw [Complex.inv_def, h1, inv_one, Complex.ofReal_one, mul_one, Complex.conj_conj]

theorem upSpan_of : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay →
    GlobalTheory.Published.CasselmanWallach → ∀ D : D7, GlobalTheory.ChainOnto.LevFacts D → GlobalTheory.ChainOnto.LevelLaw D → GlobalTheory.ChainOnto.UpSpan D := by
  intro h1 h2 h3 h4 D hLF hLL hgap c hc k hk s s' hs hs' p hp u φ v _hv
  have hLF' := hLF c hc (k + 1) (Nat.succ_le_of_lt hk) s' hs'
  beta_reduce at hLF'
  obtain ⟨hwe, hvac⟩ := GlobalTheory.T.thetaChainStep_weilDatum_nonzero_fockVacuum D hgap c hc k hk s s' hs hs' p hp hk
  have hpar := GlobalTheory.T.chainPar_of_nodeGap' D hgap ⟨k, hk⟩
  obtain ⟨T, hTK, hKT, hL⟩ := GlobalTheory.T.thetaLift_upward_multiplicity_cuspidal_realType h1 h2 h3 h4 D ⟨k, hk⟩ s.V s'.V s.par s'.par s.M s'.M c.θ c.ψ p.ω p.f
    hs.par hs'.par hc.inf hpar hwe hvac s.ν s.fd hs.haar hs.fund
  obtain ⟨F', hF', hint⟩ := hL _ (multT_le_noLevel c.θ s.M _ _ u.2)

  have hlaw : ∀ P v', ∀ κ ∈ Lev.levG s'.V s'.β s'.L, ∀ g,
      F' (T P v') (g * κ) = Lev.levChi s'.V s'.β s'.L κ * F' (T P v') g := by
    intro P v' κ hκ g
    rw [← (hint P v' (g * κ)).2, ← (hint P v' g).2, ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun g' => ?_)
    have hω : thetaKO p.ω g' (g * κ) (ptOf c.ψ c.θ s.M s'.M p.f P) =
        (Lev.levChi s'.V s'.β s'.L κ)⁻¹ * thetaKO p.ω g' g (ptOf c.ψ c.θ s.M s'.M p.f P) := by
      have hm : ((g', g * κ) : GA D s.V × GA D s'.V) = (g', g) * (1, κ) := by simp
      have h2 := (hLL hgap c hc k hk s s' hs hs' p hp P).2 κ hκ
      simp only [thetaKO]
      rw [hm, map_mul, Module.End.mul_apply]
      erw [h2]
      rw [map_smul]
      rfl
    simp only
    rw [hω, map_mul, conj_inv_of_norm_one (hLF'.2.2.2.2.2 κ hκ), mul_assoc]
  have hCC : F' ∈ s'.CC c := by
    refine GlobalTheory.T.mem_multiplicitySpace_level_of_KFinite_tensors D s'.V s'.par s'.M c.θ hc.inf _ _ ?_ F' hF' ?_
    · intro κ hκ
      exact (Subgroup.mem_inf.1 hκ).1
    · intro w hw κ hκ g
      have hx := hKT hw
      clear hw
      induction hx using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨P, v', _, rfl⟩ := hx
        exact hlaw P v' κ hκ g
      | zero => simp
      | add x y _ _ hx hy => simp only [map_add (f := _), Pi.add_apply, hx, hy, mul_add]
      | smul a x _ hx => simp only [map_smul, Pi.smul_apply, smul_eq_mul, hx]; ring
  have hup : p.up φ (PiLocalization₂.val u v) = F' (T φ v) := by
    funext h
    exact (hint φ v h).2
  rw [hup]
  exact Submodule.subset_span ⟨⟨F', hCC⟩, T φ v, hTK φ v, rfl⟩

end GlobalTheory.ChainOnto
end
end

section

open scoped ComplexConjugate Matrix NNReal ENNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP GlobalTheory.Core.Rk.SWLaw
open GlobalTheory.Core.Rk.SW


theorem _root_.GlobalTheory.T.schrodingerFunction_unitary_levi_radical_actions : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (A B : HSp D) (χB : (AE D)ˣ →* Circle) (omh : WRep (dblSp A) B), IsWeilDatumO ψ (dblSp A) B 1 χB omh → ∀ (ν : Measure (WO A B)) (𝓨 : Set (WO A B)), IsCovolOne (ratL B A) ν 𝓨 → ∀ f, IsThetaFunO ψ (dblSp A) B f → (∀ h x, sch ψ A B ν 𝓨 (omh (1, h) f) x = sch ψ A B ν 𝓨 f (mt B h⁻¹ ⬝ x)) ∧ (∀ (m : GL (Fin A.rank) (AE D)) x, sch ψ A B ν 𝓨 (omh ((dblDec A).levi m, 1) f) x = ((χB⁻¹ (Matrix.GeneralLinearGroup.det m) : Circle) : ℂ) * npow (absA D (Matrix.GeneralLinearGroup.det m)) ((B.rank : ℂ) / 2) * sch ψ A B ν 𝓨 f (x ⬝ m.1)) ∧ (∀ c x, sch ψ A B ν 𝓨 (omh ((dblDec A).nC c, 1) f) x = chr ψ (gramOf B x) c * sch ψ A B ν 𝓨 f x) ∧ swSec A B omh ν 𝓨 f 1 = sch ψ A B ν 𝓨 f 0 := by
  first | exact @GlobalTheory.Core.Rk.SchLaws.sch_laws | exact GlobalTheory.Core.Rk.SchLaws.sch_laws | (intros; apply GlobalTheory.Core.Rk.SchLaws.sch_laws <;> assumption)
end
