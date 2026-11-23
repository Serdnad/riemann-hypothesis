module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle028
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle354
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle351
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle350
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle372
import Formalism.SharpRestriction.AdmissibleParameterJoins.GandSp
public import Formalism.LocalToGlobal.GroupLattices.Joint0
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemberRepresentativeMovedAtTwistEqTupleFrames
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle003
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle008
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle007
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle022
import Formalism.AlgebraicWeights.IsAlgWeight
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ReadsMove

@[expose] public section

section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries GlobalTheory.TwV GlobalTheory.TwV.DelB GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV.DelA

theorem cKs_unit_indep : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => S.Pos → ∀ ι : ℂ →+* ℂ_[D.what₂.places.resChar w], (∀ z : TaylorLogMetric.Qbar, ι z = S.lam z) → ∀ j (hj : j + 1 ≤ D.R.m) (a : Lv.comp j) (a' : Lv.comp (j + 1)), ‖cKs S ι j hj a a'‖ = 1 ∧ ι (kS J j (Nat.le_of_succ_le hj) a * cOp (sysS H X std) D (hT.gat_pos u w hg) j (t.O u μ).dgen) ≠ 0 ∧ ∀ b b', cKs S ι j hj b b' = cKs S ι j hj a a') := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S hPos ι hι j hj a a'
  have hB := GlobalTheory.T.orthonormalChartBasis_det_norm_one S hPos ι hι
  have hG := GlobalTheory.T.norm_derivation_generators_eq_one_at_site S ι hι
  have hD := GlobalTheory.T.det_rational_unitary_orthonormalChange_matrices S
  have hL := GlobalTheory.T.norm_site_coordinate_scale_eq_one S
  have hN := GlobalTheory.T.norm_prod_cmType_embeddings_norm_one_eq_one S hPos ι hι
  have hBas := bAt_orth_lev S
  beta_reduce at hD hL hBas
  have hdPow : ∀ {n : ℕ} (M : Matrix (Fin n) (Fin n) D.host.E) (e : D.what₂.Tau → ℤ),
      (∀ τ, ‖ι (embT D τ M.det)‖ = 1) → ‖ι (dPow M e)‖ = 1 := by
    intro n M e hM
    unfold dPow
    rw [map_prod, norm_prod]
    exact Finset.prod_eq_one (fun τ _ => by rw [map_zpow₀, norm_zpow, hM τ, one_zpow])
  have hdPowC : ∀ (k : ℕ) (hk : k ≤ D.R.m) (c : ℤ), ‖ι (dPow (gMat J k hk 1) (fun _ => c))‖ = 1 := by
    intro k hk c
    unfold dPow
    rw [Finset.prod_zpow, map_zpow₀, norm_zpow]
    rw [show (∏ τ, embT D τ (gMat J k hk 1).det) = ∏ τ, TaylorLogMetric.embT D τ (gMat J k hk 1).det from rfl]
    rw [hN _ (hD k hk).1, one_zpow]
  have hsg : ∀ n, ‖ι (sgRev n)‖ = 1 := by
    intro n
    unfold sgRev
    rcases Int.units_eq_one_or (Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin n))) with h | h <;> simp [h]
  have hcOp : ‖ι (cOp (sysS H X std) D (hT.gat_pos u w hg) j (t.O u μ).dgen)‖ = 1 := by
    have h1 : ‖ι (sgO (sysS H X std) D (hT.gat_pos u w hg) j)‖ = 1 := by
      unfold sgO
      rw [map_prod, norm_prod]
      refine Finset.prod_eq_one (fun τ _ => ?_)
      split_ifs
      · simp [hsg]
      · simp
    have h2 : ‖ι (∏ τ, (t.O u μ).dgen τ ^ (-(szT (sysS H X std) D (hT.gat_pos u w hg) j τ)))‖ = 1 := by
      rw [map_prod, norm_prod]
      exact Finset.prod_eq_one (fun τ _ => by rw [map_zpow₀, norm_zpow, hG τ, one_zpow])
    unfold cOp
    rw [map_mul, norm_mul, h1, h2, one_mul]
  have hkS : ∀ b : Lv.comp j, ‖ι (kS J j (Nat.le_of_succ_le hj) b)‖ = 1 := by
    intro b
    unfold kS
    rw [map_mul, norm_mul, hdPow _ _ (hB _ _ b), hdPowC, one_mul]
  have hkT : ∀ b : Lv.comp (j + 1), ‖ι (kT J j hj b)‖ = 1 := by
    intro b
    unfold kT
    rw [map_mul, norm_mul, hdPow _ _ (hB _ _ b), hdPowC, one_mul]
  have hkSc : ∀ b : Lv.comp j,
      ‖ι (kS J j (Nat.le_of_succ_le hj) b * cOp (sysS H X std) D (hT.gat_pos u w hg) j (t.O u μ).dgen)‖ = 1 := by
    intro b
    rw [map_mul, norm_mul, hkS, hcOp, one_mul]
  have hkSeq : ∀ b : Lv.comp j, kS J j (Nat.le_of_succ_le hj) b = kS J j (Nat.le_of_succ_le hj) a := by
    intro b
    simp only [kS, uB, (hBas j (Nat.le_of_succ_le hj) a).2 b]
  have hkTeq : ∀ b : Lv.comp (j + 1), kT J j hj b = kT J j hj a' := by
    intro b
    simp only [kT, uB, (hBas (j + 1) hj a').2 b]
  refine ⟨?_, ?_, ?_⟩
  · unfold cKs
    rw [norm_mul, norm_zpow, hL, one_zpow, mul_one, map_mul, norm_mul, map_inv₀, norm_inv, hkT, hkSc, inv_one, mul_one]
  · intro h
    have h1 := hkSc a
    rw [h, norm_zero] at h1
    exact zero_ne_one h1
  · intro b b'
    unfold cKs
    rw [hkSeq b, hkTeq b']

end GlobalTheory.TwV.DelA
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum
open GlobalTheory.LocMod GlobalTheory.PlaceModel ValuativeRel

theorem _root_.GlobalTheory.T.heisenbergOperator_fixedVector_mem_localModelImage : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : GlobalTheory.LocMod.Place D k) (Y Y' : Type) [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] (S T : Formalism.BasicNotions.TH.HSp D) (FS : GlobalTheory.LocMod.Frame k S.rank Y') (FT : GlobalTheory.LocMod.Frame k T.rank Y) (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF D.host.F) ℂ), Formalism.L2.Theta.IsStdChar D ψ (-1) → ∀ (c : k), c ≠ 0 → ∀ g, Formalism.IndefR.Datum.IsThetaFunO ψ S T g → (∀ x : Matrix Y Y' k, (∀ i j, x i j ∈ 𝒪[k]) → Formalism.IndefR.Datum.heisO ψ S T (p.up FS FT (c • x)) g = g) → (∀ y : Formalism.IndefR.Datum.WO S T, Formalism.IndefR.Datum.IsHalf (Formalism.L2.Theta.cA D p.e) y → (∀ x : Matrix Y Y' k, (∀ i j, x i j ∈ 𝒪[k]) → ψ (Formalism.IndefR.Datum.symplO S T (p.up FS FT (c • x)) y) = 1) → Formalism.IndefR.Datum.heisO ψ S T y g = g) → ∀ r : Formalism.IndefR.Datum.WO S T, Formalism.IndefR.Datum.IsHalf p.e r → Formalism.IndefR.Datum.heisO ψ S T r g ∈ ⨆ (Tm : GlobalTheory.SplitWeil.SB (Matrix Y Y' k) →ₗ[ℂ] (Formalism.IndefR.Datum.WO S T → ℂ)) (_ : p.IsModel ψ FS FT Tm), LinearMap.range Tm := by
  first | exact @GlobalTheory.LocMod.Place.heisO_mem_iSup_range_of_fixed | exact GlobalTheory.LocMod.Place.heisO_mem_iSup_range_of_fixed | (intros; apply GlobalTheory.LocMod.Place.heisO_mem_iSup_range_of_fixed <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix GlobalTheory.TwU GlobalTheory.TwU.AtTrue
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.memberRepresentative_moved_at_twist_eq_tupleFrames : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) {Ch0 : ℕ → Type} {chOf0 : ∀ i, ((I.rec7 l Z).mem u).C.cls i → Ch0 i} (F : FormsTiedSym (I.rec7 l Z) u Ch0 chOf0) (a : I.ι) (Q : Finset (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))), (∀ v, v ∈ Q ↔ I.UnderQ a v) → I.StdF l Z u F → ∀ (k : GA B (B.R.N 0)), I.Reads u I.mu0 0 (fun _ => ()) (fun _ => F.to0.cls0.lev.Lb) (fun _ => F.to0.cls0.lev.U) (fun _ => F.to0.cls0.lev.chi) (fun c => (F.to0.cls0.y c).1) (fun c s => (F.to0.cls0.stabI c s).1) (fun _ => k) → ∀ c, ∃ κ : F.to0.cls0.lev.U, (∀ v, v ∉ Q → bc (prV (E := (I.rec7 l Z).host.E) v) κ.1 = 1) ∧ F.to0.cls0.lev.chi κ = 1 ∧ PtOf (B := B) ((show GA B (B.R.N 0) from (F.to0.cls0.y c).1 * κ.1) * k) (extTo I.SQ ((I.stp u a 0).rep (I.eCls0 l u a c)).1.1) := by
  first | exact @GlobalTheory.Mem.Col2.ZeroMove.main | exact GlobalTheory.Mem.Col2.ZeroMove.main | (intros; apply GlobalTheory.Mem.Col2.ZeroMove.main <;> assumption)
end
