module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
public import Development.AbelianVarietyTheory.Definitions.Divisors.DetJacMatCoordsEqTransitionJacobianDet
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle008
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle010
public import Formalism.LocalToGlobal.KernelLattices.Bundle004
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle134
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle012
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle011
public import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.Bundle005
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.KummerThetaLogarithms.ComplexMultiplicationFieldData
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.KurComplete
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.TransportFirstLevel
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NotDvdCondN
public import Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.Bundle003
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle082
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle087
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle094
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle084
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle135
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle080
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PeriodDataDeRhamAdmissible
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle095
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle083
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle057
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle136
public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.BaseFont
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.OmegaPullOmegaTraceOfSecTraceOne
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FormResFormPullFormPull
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle046
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KummerNotCoboundary
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle051
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.IsDiscriminantTwelfthRootOfIdealLattice
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle029

@[expose] public section

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Polynomial GlobalTheory.Pst GlobalTheory.MemLoc GlobalTheory.Pst.StLat GlobalTheory.Pst.NoLog
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.exists_kummerFracCoboundary_full_galois : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) [IsDomain P.R.B] (K : FinExt l) (b b' : P.R.B), b ≠ 0 →
  (∀ g ∈ GK K, b * P.actQ g b' - P.actQ g b * b' = b * P.actQ g b * ((kummer P g : ℚ_[l]) • P.tB)) →
  ∃ x y : P.R.B, x ≠ 0 ∧ ∀ g : GQ l, x * P.actQ g y - P.actQ g x * y = x * P.actQ g x * ((kummer P g : ℚ_[l]) • P.tB) := by
  first | exact @GlobalTheory.Pst.NoLog.exists_full_frac | exact GlobalTheory.Pst.NoLog.exists_full_frac | (intros; apply GlobalTheory.Pst.NoLog.exists_full_frac <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory

theorem _root_.GlobalTheory.T.ker_evalComplexPoint_le_span_jacobian : ∀ (X : Scheme.{0}) (p : X ⟶ Sp ℂ) (d : ℕ) [SmoothOfRelativeDimension d p] (U : X.Opens), IsAffineOpen U →
    ∀ (ch : GlobalTheory.AlgChart p (RingHom.id ℂ) d) (φ : Fin d → Γ(X, U)) (z : GlobalTheory.CxPts p (RingHom.id ℂ))
      (_hzc : z ∈ ch.e.source) (hz : z ∈ GlobalTheory.CxPts.ptsIn p (RingHom.id ℂ) U), (ch.jacMat φ z).det ≠ 0 →
      RingHom.ker (GlobalTheory.CxPts.evHom hz) ≤
        Ideal.span (Set.range fun j => φ j - ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p U (GlobalTheory.CxPts.evHom hz (φ j))) ⊔
          RingHom.ker (GlobalTheory.CxPts.evHom hz) ^ 2 := by
  first | (exact @GlobalTheory.JacSpan.ker_le_span_jac) | (exact GlobalTheory.JacSpan.ker_le_span_jac) | (intros; apply GlobalTheory.JacSpan.ker_le_span_jac  <;> assumption)
end

section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead
open scoped TensorProduct

namespace GlobalTheory.ProdReorder

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {V₀ V₁ V₂ V₃ V₄ V₅ : Type} [AddCommGroup V₀] [Module ℂ V₀] [AddCommGroup V₁] [Module ℂ V₁]
  [AddCommGroup V₂] [Module ℂ V₂] [AddCommGroup V₃] [Module ℂ V₃] [AddCommGroup V₄] [Module ℂ V₄]
  [AddCommGroup V₅] [Module ℂ V₅]

theorem ind₂_congr_right_prod {a b c N M : ℕ} (h : a + M = N) (h' : b + c = M)
    (ρ₀ : Representation ℂ (GL (Fin a) k) V₀) (ρ₁ : Representation ℂ (GL (Fin b) k) V₁)
    (ρ₂ : Representation ℂ (GL (Fin c) k) V₂) (μ : Representation ℂ (GL (Fin M) k) V₃)
    (φ : Nonempty (μ.Equiv (ind₂ (stdSum h') (extTensor ρ₁ ρ₂)))) :
    Nonempty ((ind₂ (stdSum h) (extTensor ρ₀ μ)).Equiv
      (ind₂ (stdSum h) (extTensor ρ₀ (ind₂ (stdSum h') (extTensor ρ₁ ρ₂))))) :=
  ind₂_congr h (eqv_refl ρ₀) φ

theorem ind₂_congr_left_prod {a b c N M : ℕ} (h : M + c = N) (h' : a + b = M)
    (ρ₁ : Representation ℂ (GL (Fin a) k) V₁) (ρ₂ : Representation ℂ (GL (Fin b) k) V₂)
    (ρ₃ : Representation ℂ (GL (Fin c) k) V₃) (μ : Representation ℂ (GL (Fin M) k) V₀)
    (φ : Nonempty (μ.Equiv (ind₂ (stdSum h') (extTensor ρ₁ ρ₂)))) :
    Nonempty ((ind₂ (stdSum h) (extTensor μ ρ₃)).Equiv
      (ind₂ (stdSum h) (extTensor (ind₂ (stdSum h') (extTensor ρ₁ ρ₂)) ρ₃))) :=
  ind₂_congr h φ (eqv_refl ρ₃)

theorem ind₂_congr_left_prod₂ {a b c d e N M : ℕ} (h : M + e = N) (h₁ : a + b = M) (h₂ : c + d = M)
    (ρ₁ : Representation ℂ (GL (Fin a) k) V₁) (ρ₂ : Representation ℂ (GL (Fin b) k) V₂)
    (ρ₃ : Representation ℂ (GL (Fin c) k) V₃) (ρ₄ : Representation ℂ (GL (Fin d) k) V₄)
    (ρ₅ : Representation ℂ (GL (Fin e) k) V₅)
    (φ : Nonempty ((ind₂ (stdSum h₁) (extTensor ρ₁ ρ₂)).Equiv (ind₂ (stdSum h₂) (extTensor ρ₃ ρ₄)))) :
    Nonempty ((ind₂ (stdSum h) (extTensor (ind₂ (stdSum h₁) (extTensor ρ₁ ρ₂)) ρ₅)).Equiv
      (ind₂ (stdSum h) (extTensor (ind₂ (stdSum h₂) (extTensor ρ₃ ρ₄)) ρ₅))) :=
  ind₂_congr h φ (eqv_refl ρ₅)

theorem multiProd_head_comp {s u : ℕ} {d : Fin s → ℕ} (σ : ∀ a, Irr k (d a)) (ι : Fin (u + 1) → Fin s)
    (a₀ : Fin s) (κ : Fin u → Fin s) (h0 : ι 0 = a₀) (hκ : ∀ i, ι i.succ = κ i) {T N : ℕ}
    (e : (Σ i, Fin (d (ι i))) ≃ Fin N) (h : d a₀ + T = N) (e' : (Σ i, Fin (d (κ i))) ≃ Fin T) :
    Nonempty ((multiProd e fun i => (σ (ι i)).π).Equiv
      (ind₂ (stdSum h) (extTensor (σ a₀).π (multiProd e' fun i => (σ (κ i)).π)))) := by
  subst h0
  have hk : (fun i => ι i.succ) = κ := funext hκ
  subst hk
  exact multiProd_head (fun i => (σ (ι i)).π) e h e'

end GlobalTheory.ProdReorder
end
end

section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric GlobalTheory.KerStd Classical

theorem _root_.GlobalTheory.T.atLin_adaptedCoef_eq_standardSeries : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (N N' : ℕ) (P : D.what₂.Tau → Matrix (Fin N) (Fin N) D.host.E) (P' : D.what₂.Tau → Matrix (Fin N') (Fin N') D.host.E) (F : MvPowerSeries (D.what₂.Tau × Fin N' × Fin N) ℂ_[p]), atLin (Formalism.L2.Ker.adCoef lam P P') (fun j => MvPowerSeries.X j) F = stdSer D lam (fun _ => 1) P P' F := by
  first | exact @GlobalTheory.atLin_adCoef_eq_stdSer | exact GlobalTheory.atLin_adCoef_eq_stdSer | (intros; apply GlobalTheory.atLin_adCoef_eq_stdSer <;> assumption)
end

section

noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric GlobalTheory.KerStd Classical
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.D (F1 F2 OwOK TrDual phFF)
open Formalism.InvariantFactorPaths.G7 (UnrOK IsLawOfLog cob)

namespace GlobalTheory.KerStd

theorem BeData.exists_of_curveData : ∀ (p : ℕ) [Fact p.Prime] (g2 g3 s2 ε : MaximalUnramifiedExtension p) (σ : MaximalUnramifiedExtension p →+* MaximalUnramifiedExtension p)
    (F : MvPowerSeries (Fin 2) (MaximalUnramifiedExtension p)), CurveData p g2 g3 s2 ε σ F → ∀ (d : ℕ) [NeZero d], Even d →
    ∃ (om oms : Fin (d / 2) → MaximalUnramifiedExtension p) (ζ : MaximalUnramifiedExtension p), BeData p d σ F (cob F (phFF p g2 g3 s2 ε)) om oms ζ := by
  intro p _ g2 g3 s2 ε σ F hC d _ hd
  obtain ⟨-, hg2, hg3, hε, hth, hσ, hF, hN⟩ := hC
  have hff := Formalism.L2.Th1.D.FAux.ffs (l := p) Formalism.L2.Th1.D.first_level_on_curve g2 g3 ε hg2 hg3 hε hth σ hσ F hF s2 hN
  have hp : p.Prime := Fact.out
  have hd0 : d ≠ 0 := NeZero.ne d
  have h1 : 1 < p ^ d := Nat.one_lt_pow hd0 hp.one_lt
  obtain ⟨ζ, hζ⟩ := Formalism.L2.Th1.D.kurRoots p (p ^ d - 1) (by omega) (fun hdv => by
    have h2 : p ∣ p ^ d := dvd_pow_self p hd0
    have h3 : p ∣ 1 := by
      have := Nat.dvd_sub h2 hdv
      rwa [Nat.sub_sub_self h1.le] at this
    exact hp.one_lt.ne' (Nat.dvd_one.1 h3))
  obtain ⟨om, oms, hO, hT⟩ := Formalism.L2.Th1.D.trDualExists (MaximalUnramifiedExtension p) p d σ hσ hd ζ hζ
  exact ⟨om, oms, ζ, hσ, hF, hff.1, hff.2.1, hO, hT, hζ⟩

end GlobalTheory.KerStd
end
end

section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric GlobalTheory.KerStd Classical
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.D (F1 F2 OwOK TrDual addC thetaInZ sumE)
open Formalism.InvariantFactorPaths.G7 (UnrOK IsLawOfLog cob)

theorem _root_.GlobalTheory.T.kvalGe_orbitGainWithoutOperator : ∀ (Lc : product_zeroth_first_parts.Loc) (ep : ℂ_[Lc.l]) (be : MvPowerSeries (ZMod Lc.d) ℂ_[Lc.l]), ‖ep‖ = 1 → BeStd Lc.l Lc.d be → OrbitPlaces.OrbitThetaExpansion Lc ep (-1) be → product_zeroth_first_parts.KvalGe Lc.N0 Lc.N1 Lc.l Lc.nu Lc.Th (gainA Lc) := by
  first | exact @GlobalTheory.KerGaussA.kvalGe_gainA | exact GlobalTheory.KerGaussA.kvalGe_gainA | (intros; apply GlobalTheory.KerGaussA.kvalGe_gainA <;> assumption)
end

section

open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW.Rec

theorem jumpIn_of_reads : ∀ {D : D7} (L : SizeData₂ D) (C₀ : ℝ) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (C : Enl D i w hw) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (ε : ℤˣ) (κ : D.host.E →+* ↥C.LL.1), Roomy L C₀ → Formalism.MainNotions.LocalSituation.adm7 D → (∀ (A A' : GRep (Br.G D.nbr i w hw) ℚ_[D.nd.l i] ↥C.LL.1 ↥(OL C.LL)) (Pr : A.V →ₗ[↥C.LL.1] A'.V →ₗ[↥C.LL.1] ↥C.LL.1), IsDual1 (Br.PD D.loc D.nbr i w hw) A.ρ A'.ρ Pr → IsCrys (Br.PD D.loc D.nbr i w hw) A.ρ → IsCrys (Br.PD D.loc D.nbr i w hw) A'.ρ) → (∀ z : ℚ_[D.nd.l i], C.inc (algebraMap _ _ z) = algebraMap _ _ z) → (∀ x, Continuous (C.loc (rTwO D.nd i r x))) → Continuous (C.loc (WpO D.nd i ρ π)) → (∀ x, IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (C.loc (rTwO D.nd i r x)))) → GlobalTheory.IndefiniteRowSideFullHecke.CrystallineAtPlaces.Splits D i r ρ π → (∀ τ : Br.Kw D.nbr i w hw →ₐ[ℚ_[D.nd.l i]] ↥C.LL.1, ∃ g, Reads (K := (D.nbr i w hw).Kw) D.host (Br.cEw D.nbr i w hw) κ τ g ∧ (∀ x a, IsJumpV (Br.PD D.loc D.nbr i w hw) (matRep (C.loc (rDuO D.nd i r x))) τ a → a ∈ jT1 (hcAt D g) (liftIdx D i) (pos ε g)) ∧ ∀ a : ℤ, multV (Br.PD D.loc D.nbr i w hw) (matRep (C.loc (T2O D.nd i ρ π))) τ a = if a ∈ jT2 (hcAt D g) (liftIdx D i) (pos ε g) then 1 else 0) → JumpIn (D.loc (D.nd.l i)) (K := (D.nbr i w hw).Kw) D (liftIdx D i) ε (Br.cEw D.nbr i w hw) κ (fun x => C.loc (rDuO D.nd i r x)) (C.loc (T2O D.nd i ρ π)) := by
  intro D L C₀ i w hw C r ρ π ε κ hR hA hT hinc hc hcW hcr hS hτ
  have hε := GlobalTheory.T.coefficientFieldEnlargement_locChi_cyclotomic i w hw C hinc
  obtain ⟨h1, h2⟩ := GlobalTheory.T.twistedDuals_eq_tateDuals_at_enlargement i w hw C r ρ π hε
  have hO := goodO_finExt_integers (D.nd.l i) C.LL
  haveI : IsTopologicalRing ↥C.LL.1 := hO.2.2.2.1
  have hsub := GlobalTheory.T.block_complement_isSub_at_enlargement i w hw C r ρ π hS
  have hF : Formalism.MainNotions.LocalSituation.fontCore (Br.PD D.loc D.nbr i w hw) := hA (D.nd.l i) (D.nbr i w hw).Kw
  let A : GRep (Br.G D.nbr i w hw) ℚ_[D.nd.l i] ↥C.LL.1 ↥(OL C.LL) :=
    { V := Fin D.R.r → ↥C.LL.1
      ρ := matRep (C.loc (WpO D.nd i ρ π))
      cont := fun x => by
        change Continuous fun g => (C.loc (WpO D.nd i ρ π) g).mulVec x
        exact hcW.matrix_mulVec continuous_const }
  have hcrW : IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (C.loc (WpO D.nd i ρ π))) :=
    GlobalTheory.CrysSub.isCrys_of_isSubOfSums (Br.PD D.loc D.nbr i w hw) hF hO A
      (fun _ : Unit => C.loc (rTwO D.nd i r π)) (fun _ => hc π) hsub (fun _ => hcr π)
  have dual := fun x => GlobalTheory.T.tateDual_matrixRep_continuous_crystalline (D.loc (D.nd.l i)) (D.nbr i w hw).Kw C.LL
    (C.loc (rTwO D.nd i r x)) hT (hc x) (hcr x)
  have dualW := GlobalTheory.T.tateDual_matrixRep_continuous_crystalline (D.loc (D.nd.l i)) (D.nbr i w hw).Kw C.LL
    (C.loc (WpO D.nd i ρ π)) hT hcW hcrW
  have uniq : ∀ τ g g', Reads (K := (D.nbr i w hw).Kw) D.host (Br.cEw D.nbr i w hw) κ τ g →
      Reads (K := (D.nbr i w hw).Kw) D.host (Br.cEw D.nbr i w hw) κ τ g' → g = g' := fun τ g g' hg hg' =>
    (GlobalTheory.T.existsUnique_embeddingReadsGaloisElement D.host (D.nbr i w hw).Kw C.LL (Br.cEw D.nbr i w hw) κ τ).unique hg hg'
  refine ⟨fun x => ?_, fun x => ?_, fun x τ g hg => ?_, ?_, fun τ g hg u => ?_⟩
  · rw [h1 x]; exact (dual x).1
  · rw [h1 x]; exact (dual x).2
  · obtain ⟨g', hg', hj, -⟩ := hτ τ
    obtain rfl := uniq τ g g' hg hg'
    exact fun a ha => hj x a ha
  · rw [h2]; exact dualW.2
  · obtain ⟨g', hg', -, hm⟩ := hτ τ
    obtain rfl := uniq τ g g' hg hg'
    refine (hm u).trans ?_
    have hnd := GlobalTheory.T.jT2_hcAt_nodup_of_roomy L C₀ (liftIdx D i) g (pos ε g) hR
    split_ifs with hu
    · rw [Multiset.count_eq_one_of_mem hnd hu]; rfl
    · rw [Multiset.count_eq_zero_of_notMem hu]; rfl

end GlobalTheory.HTW.Rec
end

section

open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits

theorem _root_.GlobalTheory.T.twistedDualSizeWord_boxesAndSizes : ∀ {D : D7} (L : SizeData₂ D) (C : ℝ) (j : Fin D.R.m) (ε : ℤˣ) {n : ℕ} (g : ZMod n → D.R.GG) (ψ : D.R.GG), Roomy L C → IsOrbit g ψ → WordBox L (recWord L j ε g) := by
  first | exact @GlobalTheory.HTW.Rec.recWord_wordBox | exact GlobalTheory.HTW.Rec.recWord_wordBox | (intros; apply GlobalTheory.HTW.Rec.recWord_wordBox <;> assumption)
end

section

open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits

theorem _root_.GlobalTheory.T.twistedDualSizeWord_inert_dichotomy : ∀ {D : D7} (L : SizeData₂ D) (C : ℝ) (j : Fin D.R.m) (ε : ℤˣ) {n : ℕ} (g : ZMod n → D.R.GG) (ψ : D.R.GG) (l : ℕ), Roomy L C → IsOrbit g ψ → 11 ≤ l → ψ.1.2 = -1 → WordsNT (recWord L j ε g) ∨ ∃ d, WordsAT l (recWord L j ε g) d := by
  first | exact @GlobalTheory.HTW.Rec.recWord_dichotomy | exact GlobalTheory.HTW.Rec.recWord_dichotomy | (intros; apply GlobalTheory.HTW.Rec.recWord_dichotomy <;> assumption)
end

section

open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW.Rec

theorem fits_of_isSubOfSums : ∀ {D : D7} (L : SizeData₂ D) (C : ℝ) (j : Fin D.R.m) (ε : ℤˣ) {l : ℕ} [Fact l.Prime] (P : LocPrime l) (K LL : FinExt l) (W : Wach P K LL) (c : D.host.E →+* ↥K.1) (κ : D.host.E →+* ↥LL.1) {ι : Type} {k r : ℕ} (Ms : ι → (↥(GK K) →* Matrix (Fin k) (Fin k) ↥LL.1)) (M' : ↥(GK K) →* Matrix (Fin r) (Fin r) ↥LL.1) (g : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → D.R.GG), Roomy L C → Formalism.MainNotions.LocalSituation.fontCore (P.PD K) → JumpIn P D j ε c κ Ms M' → (∀ τ a, Over W τ a → Reads D.host c κ τ (g a)) → ∀ T : Lat K LL, IsSubOfSums T.ρ (fun x s => Ms x s) → Fits W T (recWord L j ε g) := by
  intro D L C j ε l _ P K LL W c κ ι k r Ms M' g hR hF hJ hRd T hT
  have hO := GlobalTheory.T.goodCoefficientRing_integers_padicFiniteExtension l LL
  have hW := GlobalTheory.T.twistedDualJumps_mem_window_box L C j ε g hR
  have hjump : ∀ a τ, Over W τ a →
      JumpsInV (P.PD K) T.ρ τ {u | u ∈ jT1 (hcAt D (g a)) j (pos ε (g a))} := fun a τ hτ =>
    GlobalTheory.SubSumJumps.jumpsInV_of_isSubOfSums (P.PD K) T.ρ Ms τ _ hT
      (fun x => hJ.jumps x τ (g a) (hRd τ a hτ))
  refine ⟨?_, ?_, ?_⟩
  · exact GlobalTheory.CrysSub.isCrys_of_isSubOfSums (P.PD K) hF hO (GRep.ofLat T) Ms hJ.cont hT hJ.crys
  · intro a τ hτ u hu
    exact ((hW a).1 u (hjump a τ hτ u hu)).1
  · intro a τ hτ u hu
    exact ((hW a).1 u (hjump a τ hτ u hu)).2

end GlobalTheory.HTW.Rec
end

section

open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW.Rec

theorem fits_lowCount_of_matRep : ∀ {D : D7} (L : SizeData₂ D) (C : ℝ) (j : Fin D.R.m) (ε : ℤˣ) {l : ℕ} [Fact l.Prime] (P : LocPrime l) (K LL : FinExt l) (W : Wach P K LL) (c : D.host.E →+* ↥K.1) (κ : D.host.E →+* ↥LL.1) {ι : Type} {k r : ℕ} (Ms : ι → (↥(GK K) →* Matrix (Fin k) (Fin k) ↥LL.1)) (M' : ↥(GK K) →* Matrix (Fin r) (Fin r) ↥LL.1) (g : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → D.R.GG), Roomy L C → Formalism.MainNotions.LocalSituation.fontCore (P.PD K) → K.1 ≤ MaximalUnramifiedExtension l → JumpIn P D j ε c κ Ms M' → (∀ τ a, Over W τ a → Reads D.host c κ τ (g a)) → ∀ T : Lat K LL, IsMatRep T M' → Fits W T (recWord L j ε g) ∧ ∀ (_ft : Fintype (↥K.1 →ₐ[ℚ_[l]] ↥LL.1)) (a), lowCount W T a (recWord L j ε g).η ≤ ((recWord L j ε g).m : ℤ) := by
  intro D L C j ε l _ P K LL W c κ ι k r Ms M' g hR hF hK hJ hRd T hT
  obtain ⟨hcr, hmu⟩ := GlobalTheory.T.isCrystalline_jumps_of_isIsoMatrixGaloisRepresentation P K LL T M' hT
  have hmem : ∀ a τ, Over W τ a → ∀ u, IsJumpV (P.PD K) T.ρ τ u →
      u ∈ (recWord L j ε g).win a ∧
        u ∈ Set.Icc (-((recWord L j ε g).Mi a : ℤ)) ((recWord L j ε g).hi a : ℤ) := by
    intro a τ hτ u hu
    have h0 := GlobalTheory.T.crystalline_hodgeTateMultiplicity_ne_zero_of_jump P K LL T hF τ u hu
    rw [hmu, hJ.mult' τ (g a) (hRd τ a hτ) u] at h0
    have hc : u ∈ jT2 (hcAt D (g a)) j (pos ε (g a)) := by
      by_contra hn
      exact h0 (by simp [Multiset.count_eq_zero.mpr hn])
    obtain ⟨h1, h2, _⟩ := GlobalTheory.T.twistedDualJumps_mem_window_box L C j ε g hR a
    exact h1 u (h2 u hc)
  refine ⟨⟨hcr hJ.crys', fun a τ hτ u hu => (hmem a τ hτ u hu).1,
    fun a τ hτ u hu => (hmem a τ hτ u hu).2⟩, ?_⟩
  intro _ft a
  obtain ⟨τ0, hτ0, huniq⟩ := GlobalTheory.T.existsUnique_embeddingRestrictsToWachLetter_unramified P K LL W hK a
  unfold lowCount
  rw [Finset.sum_eq_single_of_mem τ0 (by simpa using hτ0) (fun b hb hne => by
    exact absurd (huniq b (by simpa using hb)) hne)]
  have h3 := (GlobalTheory.T.twistedDualJumps_mem_window_box L C j ε g hR a).2.2
  have he : ∀ u, multV (P.PD K) T.ρ τ0 u = (((jT2 (hcAt D (g a)) j (pos ε (g a))).count u : ℕ) : ℤ) := fun u => by
    rw [hmu, hJ.mult' τ0 (g a) (hRd τ0 a hτ0) u]
  simp only [he]
  exact h3

end GlobalTheory.HTW.Rec
end

section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.HodgeCoh GlobalTheory.CechDR KaehlerDifferential GlobalTheory.W1

set_option autoImplicit false

open Opposite TensorProduct Limits GlobalTheory.Points

noncomputable section
namespace GlobalTheory.GalTrace

theorem preimage_le {Z Y W : Scheme.{0}} {c : Y ⟶ Z} {π : W ⟶ Z} {σ : W ⟶ Y} (hσ : σ ≫ c = π)
    (U : Z.Opens) : π ⁻¹ᵁ U ≤ σ ⁻¹ᵁ (c ⁻¹ᵁ U) := by
  rw [← Scheme.Hom.comp_preimage, hσ]

section Forms

variable {k : Type} [CommRing k] {Z Y W : Scheme.{0}} {s : Z ⟶ Sp k} {s' : Y ⟶ Sp k}
  {sW : W ⟶ Sp k} {c : Y ⟶ Z} {π : W ⟶ Z}

def liftPull {σ : W ⟶ Y} (hσ : σ ≫ c = π) (hσs : σ ≫ s' = sW) (j : ℕ) :
    (Scheme.Modules.pushforward c).obj (Omega s' j) ⟶
      (Scheme.Modules.pushforward π).obj (Omega sW j) :=
  (Scheme.Modules.pushforward c).map (omegaPull hσs j) ≫
    (Scheme.Modules.pushforwardComp σ c).hom.app _ ≫
      (Scheme.Modules.pushforwardCongr hσ).hom.app _

theorem liftPull_app (hc : c ≫ s = s') (hπ : π ≫ s = sW) {σ : W ⟶ Y} (hσ : σ ≫ c = π)
    (hσs : σ ≫ s' = sW) (j : ℕ) (U : Z.Opens) (b : Sec s' (c ⁻¹ᵁ U)) (x : OmU s U j) :
    (liftPull hσ hσs j).app U (toOm s' j (c ⁻¹ᵁ U) (b • formPull hc U j x)) =
      toOm sW j (π ⁻¹ᵁ U) (Sec.res sW (preimage_le hσ U) (appSec s' sW σ (c ⁻¹ᵁ U) b) •
        formPull hπ U j x) := by
  change (Omega sW j).presheaf.map (homOfLE (preimage_le hσ U)).op
    ((omegaPull hσs j).val.app (op (c ⁻¹ᵁ U))
      ((toOmega s' j).app (op (c ⁻¹ᵁ U)) (b • formPull hc U j x))) = _
  rw [omegaPull_toOmega]
  refine (res_toOm sW j (preimage_le hσ U) (formPull hσs (c ⁻¹ᵁ U) j (b • formPull hc U j x))).trans
    (congrArg (toOm sW j (π ⁻¹ᵁ U)) ?_)
  have h : (σ ≫ c) ≫ s = sW := by rw [hσ, hπ]
  rw [formPull_smul hσs (c ⁻¹ᵁ U) b (formPull hc U j x), formRes_smul,
    formPull_formPull hc hσs h U j x]
  exact congrArg (_ • ·) (formRes_formPull_congr hσ h hπ U (preimage_le hσ U) j x)

theorem sum_app {F G : Z.Modules} {ι : Type} (R : Finset ι) (φ : ι → (F ⟶ G)) (U : Z.Opens)
    (y : Γ(F, U)) : (∑ r ∈ R, φ r).app U y = ∑ r ∈ R, (φ r).app U y := by
  classical
  induction R using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.sum_empty]; rfl
  | insert a R ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, Scheme.Modules.Hom.add_app]
    exact congrArg ((φ a).app U y + ·) ih

variable [IsFinite c] [Etale c] (hc : c ≫ s = s') (hπ : π ≫ s = sW) {ι : Type} (R : Finset ι)
  {σ : ι → (W ⟶ Y)} (hσ : ∀ r, σ r ≫ c = π) (hσs : ∀ r, σ r ≫ s' = sW)

theorem omegaTrace_omegaPull
    (hF : ∀ (U : Z.Opens) (hU : IsAffineOpen U) (b : Sec s' (c ⁻¹ᵁ U)),
      appSec s sW π U (secTrace s s' hU b) =
        ∑ r ∈ R, Sec.res sW (preimage_le (hσ r) U) (appSec s' sW (σ r) (c ⁻¹ᵁ U) b)) (j : ℕ) :
    omegaTrace hc j ≫ omegaPull hπ j = ∑ r ∈ R, liftPull (hσ r) (hσs r) j := by
  refine hom_ext_affine fun U hU y ↦ ?_
  obtain ⟨z, rfl⟩ := toOm_surjective (s := s') (j := j) (hU.preimage c) y
  refine formOm_induction (P := fun z ↦ (omegaTrace hc j ≫ omegaPull hπ j).app U
      (toOm s' j (c ⁻¹ᵁ U) z) = (∑ r ∈ R, liftPull (hσ r) (hσs r) j).app U
        (toOm s' j (c ⁻¹ᵁ U) z)) hc hU ?_ (fun y z hy hz ↦ ?_) (fun b x ↦ ?_) z
  · erw [map_zero, map_zero, map_zero]
  · erw [map_add, map_add, map_add]; exact congrArg₂ (· + ·) hy hz
  · refine Eq.trans ?_ (sum_app R _ U _).symm
    refine Eq.trans ?_ (Finset.sum_congr rfl fun r _ ↦
      liftPull_app hc hπ (hσ r) (hσs r) j U b x).symm
    rw [Scheme.Modules.Hom.comp_app]
    change (omegaPull hπ j).val.app (op U)
      ((omegaTrace hc j).app U (toOm s' j (c ⁻¹ᵁ U) (b • formPull hc U j x))) = _
    rw [omegaTrace_toOm_smul_formPull hc j hU, toOm_apply, omegaPull_toOmega, formPull_smul, hF,
      Finset.sum_smul]
    exact map_sum (toOm sW j (π ⁻¹ᵁ U)) _ _

theorem hodgePull_hodgeTrace (j : ℕ)
    (H : omegaTrace hc j ≫ omegaPull hπ j = ∑ r ∈ R, liftPull (hσ r) (hσs r) j) (q : ℕ)
    (x : hodgeH s' j q) :
    hodgePull hπ j q (hodgeTrace hc j q x) = ∑ r ∈ R, hodgePull (hσs r) j q x := by
  letI := algΓ s; letI := algΓ s'; letI := algΓ sW
  obtain ⟨y, rfl⟩ := (coh.pushforwardEquiv k (appTop_algebraMap hc) (Omega s' j) q).surjective x
  have e1 : hodgeTrace hc j q (coh.pushforwardEquiv k (appTop_algebraMap hc) (Omega s' j) q y) =
      cohOn.map k (omegaTrace hc j) ⊤ q y :=
    congrArg (cohOn.map k (omegaTrace hc j) ⊤ q)
      ((coh.pushforwardEquiv k (appTop_algebraMap hc) (Omega s' j) q).symm_apply_apply y)
  have e2 : ∀ φ : (Scheme.Modules.pushforward c).obj (Omega s' j) ⟶
      (Scheme.Modules.pushforward π).obj (Omega sW j),
      cohOn.pull (σ := RingHom.id k) (appTop_algebraMap hπ) (𝟙 _) (le_refl (π ⁻¹ᵁ ⊤)) q
        (cohOn.map k φ ⊤ q y) =
      cohOn.pull (σ := RingHom.id k) (appTop_algebraMap hπ) φ (le_refl (π ⁻¹ᵁ ⊤)) q y := fun φ ↦ by
    rw [cohOn.pull_map, Category.comp_id]
  have e4 := cohOn.pull_map (σ := RingHom.id k) (appTop_algebraMap hπ)
    (omegaPull hπ j) (omegaTrace hc j) (le_refl (π ⁻¹ᵁ ⊤)) (n := q) y
  have e5 : cohOn.map k (∑ r ∈ R, liftPull (hσ r) (hσs r) j) ⊤ q =
      ∑ r ∈ R, cohOn.map k (liftPull (hσ r) (hσs r) j) ⊤ q :=
    map_sum (cohOn.mapAddHom k _ _ ⊤ q) _ _

  rw [H, ← e2, e5, LinearMap.sum_apply, map_sum] at e4
  rw [e1]
  refine e4.trans (Finset.sum_congr rfl fun r _ ↦ (e2 _).trans ?_)
  have h : (σ r ≫ c) ≫ s = sW := by rw [hσ, hπ]
  have s2 := cohOn_pull_pull (appTop_algebraMap hc) (appTop_algebraMap (hσs r))
    (appTop_algebraMap h) (𝟙 _) (omegaPull (hσs r) j) (le_refl (c ⁻¹ᵁ ⊤)) (le_refl _) (le_refl _) q y
  have s3 := cohOn_pull_congr (hσ r) (appTop_algebraMap h) (appTop_algebraMap hπ)
    (G := Omega sW j) (𝟙 ((Scheme.Modules.pushforward c).obj (Omega s' j)) ≫
      (Scheme.Modules.pushforward c).map (omegaPull (hσs r) j) ≫
        (Scheme.Modules.pushforwardComp (σ r) c).hom.app _)
    (V := ⊤) (W := σ r ⁻¹ᵁ (c ⁻¹ᵁ ⊤)) (le_refl _) (fun _ _ ↦ trivial) q y
  have hm : liftPull (hσ r) (hσs r) j = (𝟙 ((Scheme.Modules.pushforward c).obj (Omega s' j)) ≫
      (Scheme.Modules.pushforward c).map (omegaPull (hσs r) j) ≫
        (Scheme.Modules.pushforwardComp (σ r) c).hom.app _) ≫
          (Scheme.Modules.pushforwardCongr (hσ r)).hom.app _ := by
    simp [liftPull]
  rw [hm]
  exact s3.symm.trans s2.symm

end Forms

end GlobalTheory.GalTrace
end
end
