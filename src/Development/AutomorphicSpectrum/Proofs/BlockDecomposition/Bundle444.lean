module

public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.ThetaOrbits
import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.FriedrichsKernels.Friedrichs
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FunctionalCalculusJointCurve
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle424
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle321
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IsotropicMahlerBounds.LogAbsoluteWedges.LogAbsBasic
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle423
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle425
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle426
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle427
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
import Mathlib.RingTheory.PicardGroup
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
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.EisCellsDefs
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.Bundle001

@[expose] public section

section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.EC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.ThetaInv

variable {D : D7}

theorem trA_incA (e : D.host.E) :
    trA (incA D e) = algebraMap D.host.F (AF D.host.F) (Algebra.trace D.host.F D.host.E e) := by
  change Algebra.trace (AF D.host.F) (AE D) ((1 : AF D.host.F) ⊗ₜ[D.host.F] e) = _
  rw [Algebra.trace_apply, Algebra.trace_apply, ← Algebra.baseChange_lmul, LinearMap.trace_baseChange]

theorem halfTr_incA (e : D.host.E) :
    halfTr (incA D e) =
      algebraMap D.host.F (AF D.host.F) (1 / 2 * Algebra.trace D.host.F D.host.E e) := by
  rw [halfTr, trA_incA, map_mul]

theorem psi_unip_rat {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) {n : ℕ} (V : HSp D)
    (b : Matrix (Fin n) (Fin n) D.host.E) (ξ : Matrix (Fin V.rank) (Fin n) D.host.E) :
    ψ (halfTr (Matrix.trace (b.map (incA D) ⬝ inner V (ξ.map (incA D)) (ξ.map (incA D)) : Mx D n n))) = 1 := by
  have h : (b.map (incA D) ⬝ inner V (ξ.map (incA D)) (ξ.map (incA D)) : Mx D n n) =
      (b * (ξᴴ * (V.gram * ξ))).map (incA D) := by
    change (rat b ⬝ (adj (rat ξ) ⬝ (gA V ⬝ rat ξ)) : Mx D n n) = rat (b * (ξᴴ * (V.gram * ξ)))
    rw [rat_mul, rat_mul, rat_mul, rat_conjTranspose, gA]
  have ht : ∀ M : Matrix (Fin n) (Fin n) D.host.E,
      Matrix.trace (M.map (incA D)) = incA D (Matrix.trace M) := fun M => by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.trace, Matrix.diag, Matrix.map_apply, map_sum]
  rw [h, ht, halfTr_incA]
  exact hψ.2.2.1 _

theorem theta_unip : ∀ (D : D7) (n : ℕ) (V : HSp D) ψ χ θ μ ω, HidaSetting D n V ψ χ θ μ ω →
    ∀ (g : G D n) (b : Matrix (Fin n) (Fin n) D.host.E), mat g = blk4 1 (b.map (incA D)) 0 1 →
    ∀ Φ : schwartzA θ V.rank n,
      ∑' ξ : Matrix (Fin V.rank) (Fin n) D.host.E, (ω g Φ).1 (ξ.map (incA D)) =
        ∑' ξ : Matrix (Fin V.rank) (Fin n) D.host.E, Φ.1 (ξ.map (incA D)) := by
  intro D n V ψ χ θ μ ω hS g b hg Φ
  refine tsum_congr fun ξ => ?_
  rw [hS.2.2.2.2.2.2.2.unip g (b.map (incA D)) hg Φ (ξ.map (incA D)), psi_unip_rat hS.2.2.1, one_mul]

end GlobalTheory.CompanionTheory.ThetaInv
end
end

section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.EC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.ThetaInvLevi

theorem theta_levi_invariant : ∀ (D : D7) (n : ℕ) (V : HSp D) ψ χ θ μ ω,
    PositivityTheory.GramSchwartzFunctions.HidaSetting D n V ψ χ θ μ ω →
    ∀ (g : G D n) (a : GL (Fin n) D.host.E), mat g = blk4 (a.1.map (incA D)) 0 0 (adj ((a⁻¹).1.map (incA D))) →
    ∀ Φ : schwartzA θ V.rank n,
      ∑' ξ : Matrix (Fin V.rank) (Fin n) D.host.E, (ω g Φ).1 (ξ.map (incA D)) =
        ∑' ξ : Matrix (Fin V.rank) (Fin n) D.host.E, Φ.1 (ξ.map (incA D)) := by
  intro D n V ψ χ θ μ ω hS g a hg Φ
  obtain ⟨-, -, -, hχ, -, -, -, hW⟩ := hS
  obtain ⟨-, hχ⟩ := hχ
  let a' : GL (Fin n) (Formalism.L2.Theta.AE D) := Matrix.GeneralLinearGroup.map (incA D) a
  have hg' : GlobalTheory.StdUnn.mat g = GlobalTheory.StdUnn.blk4 (a' : Matrix (Fin n) (Fin n) (Formalism.L2.Theta.AE D)) 0 0
      (GlobalTheory.MixModel.adj ((a'⁻¹ : GL (Fin n) (Formalism.L2.Theta.AE D)) : Matrix (Fin n) (Fin n) (Formalism.L2.Theta.AE D))) :=
    hg
  have hdet : Matrix.GeneralLinearGroup.det a' =
      Units.map (incA D : D.host.E →* Formalism.L2.Theta.AE D) (Matrix.GeneralLinearGroup.det a) :=
    Units.ext (by exact (RingHom.map_det (incA D) a.1).symm)
  have hχ1 : χ (Matrix.GeneralLinearGroup.det a') = 1 := by
    rw [hdet]
    exact hχ _
  have habs : GlobalTheory.Doubling.absA D (Matrix.GeneralLinearGroup.det a') = 1 := by
    rw [hdet]
    exact GlobalTheory.Doubling.absE_inclR _
  have hc : ∀ x, ((ω g Φ : GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz.schwartzA θ V.rank n) : Formalism.IndefR.Datum.Mx D V.rank n → ℂ) x =
      (Φ : Formalism.IndefR.Datum.Mx D V.rank n → ℂ) (x * (a' : Matrix (Fin n) (Fin n) (Formalism.L2.Theta.AE D))) := by
    intro x
    rw [hW.levi g a' hg' Φ x, hχ1, habs]
    simp [GlobalTheory.Doubling.npow]
  have hterm : ∀ ξ : Matrix (Fin V.rank) (Fin n) D.host.E,
      (ω g Φ).1 (ξ.map (incA D)) = Φ.1 ((ξ * (a : Matrix (Fin n) (Fin n) D.host.E)).map (incA D)) := by
    intro ξ
    rw [hc, Matrix.map_mul]
    rfl
  let e : Matrix (Fin V.rank) (Fin n) D.host.E ≃ Matrix (Fin V.rank) (Fin n) D.host.E :=
    { toFun := fun ξ => ξ * (a : Matrix (Fin n) (Fin n) D.host.E)
      invFun := fun ξ => ξ * ((a⁻¹ : GL (Fin n) D.host.E) : Matrix (Fin n) (Fin n) D.host.E)
      left_inv := fun ξ => by simp [Matrix.mul_assoc]
      right_inv := fun ξ => by simp [Matrix.mul_assoc] }
  rw [tsum_congr hterm]
  exact e.tsum_eq (fun ξ => Φ.1 (ξ.map (incA D)))

end GlobalTheory.CompanionTheory.ThetaInvLevi
end
end

section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.WeilSiegel.Deg

variable {D : D7}

def congrH {r : ℕ} (a : Matrix (Fin r) (Fin r) D.host.E) (β : HermE D r) : HermE D r :=
  ⟨(a.map (D.sp.cm.sig : D.host.E → D.host.E))ᵀ * β.1 * a, by
    have hσ : ∀ x, D.sp.cm.sig (D.sp.cm.sig x) = x := fun x => star_star x
    have hβ := β.2
    have hm : ∀ (X Y : Matrix (Fin r) (Fin r) D.host.E),
        (X * Y).map (D.sp.cm.sig : D.host.E → D.host.E) =
          X.map (D.sp.cm.sig : D.host.E → D.host.E) * Y.map (D.sp.cm.sig : D.host.E → D.host.E) :=
      fun X Y => Matrix.map_mul (f := (D.sp.cm.sig : D.host.E →+* D.host.E))
    rw [hm, hm, Matrix.transpose_mul, Matrix.transpose_mul, hβ]
    have h2 : ((a.map (D.sp.cm.sig : D.host.E → D.host.E))ᵀ.map (D.sp.cm.sig : D.host.E → D.host.E))ᵀ = a := by
      ext i j; simp [hσ]
    rw [h2, Matrix.mul_assoc]⟩

def IsBlockNF {r : ℕ} (t : ℕ) (β : HermE D r) : Prop :=
  ∃ h : t < r, (∀ i j : Fin r, (t ≤ i.1 ∨ t ≤ j.1) → β.1 i j = 0) ∧
    (β.1.submatrix (Fin.castLE h.le) (Fin.castLE h.le)).det ≠ 0

end GlobalTheory.CompanionTheory.WeilSiegel.Deg
end
end

section

open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace ZeroAtInfty ENNReal
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Fc
open PositivityTheory.RgTw (Mat G)
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.SobComplete

section Limit

variable {n : ℕ} [MeasurableSpace (G n)] {μ : Measure (G n)}
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

theorem ae_eq_of_tendsto {K : ℕ → Mat n → V} {L : Mat n → V} {y : Lp V 2 μ}
    (hK : ∀ k, MemLp (fun g : G n => K k g.val) 2 μ)
    (hy : Tendsto (fun k => cls μ (K k)) atTop (𝓝 y))
    (hp : ∀ g : G n, Tendsto (fun k => K k g.val) atTop (𝓝 (L g.val))) :
    y =ᵐ[μ] fun g : G n => L g.val := by
  have hm : TendstoInMeasure μ (fun k => (cls μ (K k) : G n → V)) atTop y :=
    tendstoInMeasure_of_tendsto_Lp hy
  obtain ⟨ns, hns0, hns⟩ := hm.exists_seq_tendsto_ae
  have hc : ∀ᵐ g ∂μ, ∀ k, (cls μ (K k) : G n → V) g = K k (g : G n).val :=
    ae_all_iff.2 fun k => by
      have e : cls μ (K k) = (hK k).toLp _ := dif_pos (hK k)
      rw [e]
      exact (hK k).coeFn_toLp
  filter_upwards [hns, hc] with g h1 h2
  simp only [h2] at h1
  exact tendsto_nhds_unique h1 ((hp g).comp (StrictMono.tendsto_atTop hns0))

end Limit

theorem sob_complete : ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (V : Type)
    [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V], SobG →
    ∀ a : ℕ → Mat n → V, (∀ k, Sob μ (a k)) → (∀ w, CauchySeq fun k => cls μ (Rw w (a k))) →
    ∃ b : Mat n → V, Sob μ b ∧ (∀ w, Tendsto (fun k => cls μ (Rw w (a k))) atTop (𝓝 (cls μ (Rw w b)))) ∧
      ∀ g ∈ GLs n, Tendsto (fun k => a k g) atTop (𝓝 (b g)) := by
  intro n _ _ μ _ V _ _ _ hS a ha hC
  obtain ⟨S, C, hb'⟩ := GlobalTheory.CompanionTheory.CurveJ.sup_bound hS n μ
  have hb := hb' V
  have hs : ∀ k w, Sob μ (Rw w (a k)) := fun k w => GlobalTheory.CompanionTheory.SobOpsPf.sob_Rw w (ha k)
  have hU : ∀ w, UniformCauchySeqOn (fun k => Rw w (a k)) atTop (GLs n) := by
    intro w
    have hT : Tendsto (fun p : ℕ × ℕ => C * ∑ w' ∈ S,
        dist (cls μ (Rw w' (Rw w (a p.1)))) (cls μ (Rw w' (Rw w (a p.2))))) (atTop ×ˢ atTop) (𝓝 0) := by
      have e0 : (C * ∑ w' ∈ S, (0 : ℝ)) = 0 := by simp
      rw [← e0]
      refine Tendsto.const_mul C (tendsto_finsetSum _ fun w' _ => ?_)
      have h1 := hC (w' ++ w)
      simp only [← GlobalTheory.CompanionTheory.CurveJ.Rw_append] at h1
      rw [prod_atTop_atTop_eq]
      exact cauchySeq_iff_tendsto_dist_atTop_0.1 h1
    intro u hu
    obtain ⟨ε, hε, hεu⟩ := Metric.mem_uniformity_dist.1 hu
    filter_upwards [hT.eventually (gt_mem_nhds hε)] with p hp x hx
    refine hεu ?_
    have b := GlobalTheory.CompanionTheory.CurveJ.bound3 hb (hs p.1 w) (hs p.2 w) (hs p.2 w) 0 hx
    simp only [zero_smul, sub_zero, ← dist_eq_norm] at b
    exact lt_of_le_of_lt b hp
  obtain ⟨Gf, hG, hsm, hR⟩ := GlobalTheory.T.uniform_limit_right_derivatives n V a (fun k => (ha k).1) hU
  have hy : ∀ w, ∃ y : Lp V 2 μ, Tendsto (fun k => cls μ (Rw w (a k))) atTop (𝓝 y) := fun w =>
    cauchySeq_tendsto_of_complete (hC w)
  choose y hy using hy
  have hae : ∀ w, y w =ᵐ[μ] fun g : G n => Rw w (Gf []) g.val := by
    intro w
    have h := ae_eq_of_tendsto (fun k => (hs k w).2 []) (K := fun k => Rw w (a k)) (L := Gf w) (hy w)
      (fun g => (hG w).tendsto_at (GlobalTheory.CompanionTheory.SobOpsPf.val_mem g))
    filter_upwards [h] with g hg
    rw [hg, hR w _ (GlobalTheory.CompanionTheory.SobOpsPf.val_mem g)]
  have hM : ∀ w, MemLp (fun g : G n => Rw w (Gf []) g.val) 2 μ := fun w =>
    (Lp.memLp (y w)).ae_eq (hae w)
  have hcl : ∀ w, cls μ (Rw w (Gf [])) = y w := by
    intro w
    rw [GlobalTheory.CompanionTheory.CurveJ.cls_of (hM w)]
    exact Lp.ext ((hM w).coeFn_toLp.trans (hae w).symm)
  refine ⟨Gf [], ⟨hsm, hM⟩, fun w => ?_, fun g hg => (hG []).tendsto_at hg⟩
  rw [hcl w]
  exact hy w

end GlobalTheory.CompanionTheory.SobComplete
end

section

open Matrix PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D1

theorem _root_.GlobalTheory.T.finite_support_of_size : MulF → MulI → SzFin → FinSupp := by
  first | exact @GlobalTheory.CompanionTheory.WedgeSupport.finSupp_of_mul | exact GlobalTheory.CompanionTheory.WedgeSupport.finSupp_of_mul | (intros; apply GlobalTheory.CompanionTheory.WedgeSupport.finSupp_of_mul <;> assumption)
end

section

open Matrix PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D1

theorem _root_.GlobalTheory.T.adelic_degree_formula : MulF → MulI → LogAbsBasic → FinSupp → DegAdelic := by
  first | exact @GlobalTheory.CompanionTheory.DegAdelicProof.degAdelic_of | exact GlobalTheory.CompanionTheory.DegAdelicProof.degAdelic_of | (intros; apply GlobalTheory.CompanionTheory.DegAdelicProof.degAdelic_of <;> assumption)
end

section

open Matrix PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D1

theorem _root_.GlobalTheory.T.degree_basis_general : WedgeF → WedgeI → MulF → MulI → LogAbsBasic → FinSupp → DegBasisG := by
  first | exact @GlobalTheory.CompanionTheory.DegBasisGen.degBasisG_of | exact GlobalTheory.CompanionTheory.DegBasisGen.degBasisG_of | (intros; apply GlobalTheory.CompanionTheory.DegBasisGen.degBasisG_of <;> assumption)
end

section

open Matrix PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D1

theorem _root_.GlobalTheory.T.degree_under_translation : MulF → MulI → SzFin → FinSupp → DegBasisG → DegMove := by
  first | exact @GlobalTheory.CompanionTheory.DegMoveProof.degMove_of | exact GlobalTheory.CompanionTheory.DegMoveProof.degMove_of | (intros; apply GlobalTheory.CompanionTheory.DegMoveProof.degMove_of <;> assumption)
end

section

open Matrix PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D1

theorem _root_.GlobalTheory.T.log_abs_basic_facts : LogAbsBasic := by
  first | exact @GlobalTheory.CompanionTheory.LogAbs.logAbsBasic | exact GlobalTheory.CompanionTheory.LogAbs.logAbsBasic | (intros; apply GlobalTheory.CompanionTheory.LogAbs.logAbsBasic <;> assumption)
end

section

open Matrix PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D1

theorem _root_.GlobalTheory.T.radical_subspace_facts : Radical := by
  first | exact @GlobalTheory.CompanionTheory.RadicalForm.radical | exact GlobalTheory.CompanionTheory.RadicalForm.radical | (intros; apply GlobalTheory.CompanionTheory.RadicalForm.radical <;> assumption)
end

section

open Matrix PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D1

theorem _root_.GlobalTheory.T.two_bases_comparison : TwoBases := by
  first | exact @GlobalTheory.CompanionTheory.LinAlg.twoBases | exact GlobalTheory.CompanionTheory.LinAlg.twoBases | (intros; apply GlobalTheory.CompanionTheory.LinAlg.twoBases <;> assumption)
end

section

open Matrix PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D1

theorem _root_.GlobalTheory.T.degree_submodule_bound : WedgeF → WedgeI → WedgeSub → FinSupp → DegBasisG → TwoBases → DegSubmod := by
  first | exact @GlobalTheory.CompanionTheory.DegreeSubmod.degSubmod_of | exact GlobalTheory.CompanionTheory.DegreeSubmod.degSubmod_of | (intros; apply GlobalTheory.CompanionTheory.DegreeSubmod.degSubmod_of <;> assumption)
end
