module

public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitarySchrodinger
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle431
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.Bundle001
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsSelfDualSiegelWeilMeasures
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle502
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle706
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PtMMapOfZero
public import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.CoefDataExists
public import Mathlib.MeasureTheory.Measure.Haar.MulEquivHaarChar
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle389
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle093
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.Bundle001
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaRestrictIsotropicQuotientWittTowerPropertie
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle432
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle705
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.IntegralEqTsumFd
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemElt
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
import Mathlib.Topology.Compactness.Paracompact
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.PfSWUS

open GlobalTheory.StdUnn

theorem height_mul_K {D : D7} {n : ℕ} {H : G D n → ℝ≥0} (hH : IsHeight H) (x : G D n) {k : G D n} (hk : k ∈ K D n) :
    H (x * k) = H x := by
  obtain ⟨p, hp, k', hk', rfl⟩ := GlobalTheory.StdUnn.Iwasawa.exists_mul D n x
  obtain ⟨a, ha⟩ := GlobalTheory.StdUnn.LeftInvSect.exists_blkA hp
  rw [mul_assoc, hH p hp a ha _ ((K D n).mul_mem hk' hk), hH p hp a ha k' hk']

end GlobalTheory.CompanionTheory.PfSWUS

end
end

section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_self_dual_siegel_weil_measures : ∀ (D : D7) (r : ℕ) (V : HSp D) (ψ : AddChar (AF D.host.F) ℂ), IsCharAF D.host.F ψ →
  ∀ μ : Measure (Mx D V.rank r), (∃ 𝓕, IsCovolOne (ratMx D V.rank r) μ 𝓕) →
  ∀ lam : Measure (hermA D r), (∃ 𝓖, IsCovolOneH lam 𝓖) →
  ∃ (dx : Measure (Fin r → Fin V.rank → AE D)) (db : Measure (HermR (AF D.host.F) D.sp.cm.sig r)),
    SdW D.host.F D.host.E D.sp.cm.sig V.rank V.gram (AF D.host.F) ψ r dx ∧
    SdHerm D.host.F D.host.E D.sp.cm.sig (AF D.host.F) ψ r db ∧
    ∀ (φ : Mx D V.rank r → ℂ) (β : HermE D r),
      W ψ V μ lam φ β = coefN D.sp.cm.sig V.gram ψ dx db (fun X => φ (tupOf X)) β.1 := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.whit_eq_coefN | exact GlobalTheory.CompanionTheory.SiegelND.whit_eq_coefN | (intros; apply GlobalTheory.CompanionTheory.SiegelND.whit_eq_coefN <;> assumption)
end

section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.shift_conj_heisenberg : ∀ {D : D7} {n ρ p : ℕ} {hn : ρ + p = n} (M : Maps D hn) (y : Mx D ρ p) (z : hermA D ρ) (x : Mx D ρ p), M.sh y * M.nzx z x = M.nzx (z + GlobalTheory.CompanionTheory.FJE.jc y x) x * M.sh y := by
  first | exact @GlobalTheory.CompanionTheory.FJE.sh_mul_nzx | exact GlobalTheory.CompanionTheory.FJE.sh_mul_nzx | (intros; apply GlobalTheory.CompanionTheory.FJE.sh_mul_nzx <;> assumption)
end

section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L PositivityTheory.Rg.Rsw.Cell

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.CellDecomp

section Weyl

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

theorem matHom_proj_weyl (σ : E →ₐ[F] E) (J : Matrix (Fin (n + n)) (Fin (n + n)) E)
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) (g : GAd σ J)
    (hg : (matHom _ σ J g).1 = blk4 0 1 (-1) 0) :
    (matHom _ σ J (proj σ J v g)).1 = blk4 (0 : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) 1 (-1) 0 := by
  rw [matHom_proj, bc_val, hg]
  exact weyl_map _

theorem stab_of_weyl (σ : E →ₐ[F] E) (J : Matrix (Fin (n + n)) (Fin (n + n)) E)
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) (k : GLoc σ J v)
    (hk : (matHom _ σ J k).1 = blk4 (0 : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) 1 (-1) 0) :
    k ∈ stabLoc σ J (stdLattice E (n + n)) v := by
  rw [stabLoc, Subgroup.mem_comap]
  change ∀ x, x ∈ latLoc F (stdLattice E (n + n)) v ↔ (↑(matHom _ σ J k) : Matrix _ _ _).mulVec x ∈ latLoc F (stdLattice E (n + n)) v
  rw [hk]
  have hmap : ∀ y ∈ latLoc F (stdLattice E (n + n)) v,
      (blk4 (0 : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) 1 (-1) 0).mulVec y ∈ latLoc F (stdLattice E (n + n)) v := by
    intro y hy
    change y ∈ AddSubgroup.closure _ at hy
    change _ ∈ AddSubgroup.closure _
    induction hy using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨a, ha, x, hx, rfl⟩ := hy
      apply AddSubgroup.subset_closure
      refine ⟨a, ha, (blk4 (0 : Matrix (Fin n) (Fin n) E) 1 (-1) 0).mulVec x, ?_, ?_⟩
      · change _ ∈ Submodule.pi _ _ at hx ⊢
        rw [Submodule.mem_pi] at hx ⊢
        intro j _
        obtain ⟨s, rfl⟩ := finSumFinEquiv.surjective j
        rcases s with i | i
        · rw [(weyl_mulVec x i).1]
          exact hx _ (Set.mem_univ _)
        · rw [(weyl_mulVec x i).2]
          exact neg_mem (hx _ (Set.mem_univ _))
      · funext j
        obtain ⟨s, rfl⟩ := finSumFinEquiv.surjective j
        rcases s with i | i
        · rw [(weyl_mulVec _ i).1, (weyl_mulVec x i).1]
        · rw [(weyl_mulVec _ i).2, (weyl_mulVec x i).2, TensorProduct.tmul_neg]
    | zero =>
      rw [Matrix.mulVec_zero]
      exact zero_mem _
    | add y z _ _ hy hz =>
      rw [Matrix.mulVec_add]
      exact add_mem hy hz
    | neg y _ hy =>
      rw [Matrix.mulVec_neg]
      exact neg_mem hy
  have hWW : ∀ y : Fin (n + n) → Fv F v ⊗[F] E,
      (blk4 (0 : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) 1 (-1) 0).mulVec
        ((blk4 (0 : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) 1 (-1) 0).mulVec y) = -y := by
    intro y
    funext j
    obtain ⟨s, rfl⟩ := finSumFinEquiv.surjective j
    rcases s with i | i
    · rw [(weyl_mulVec _ i).1, (weyl_mulVec y i).2, Pi.neg_apply]
    · rw [(weyl_mulVec _ i).2, (weyl_mulVec y i).1, Pi.neg_apply]
  intro x
  constructor
  · exact hmap x
  · intro hx
    have h2 := neg_mem (hmap _ hx)
    rwa [hWW, neg_neg] at h2

end Weyl

section Main

variable {D : D7} {n : ℕ}

theorem pt_comm {e : AE D} (he : e * e = e) (hc : cA D e = e) (he' : (1 - e) * (1 - e) = 1 - e)
    (hc' : cA D (1 - e) = 1 - e) (x y : G D n) :
    pt e he hc x * pt (1 - e) he' hc' y = pt (1 - e) he' hc' y * pt e he hc x := by
  apply mat_inj
  rw [mat_mul', mat_mul', mat_pt, mat_pt, (ptM_mul_compl he he' _ _).1, (ptM_mul_compl he he' _ _).2]

theorem pt_mul_compl_self {e : AE D} (he : e * e = e) (hc : cA D e = e) (he' : (1 - e) * (1 - e) = 1 - e)
    (hc' : cA D (1 - e) = 1 - e) (x : G D n) : pt e he hc x * pt (1 - e) he' hc' x = x := by
  apply mat_inj
  rw [mat_mul', mat_pt, mat_pt, (ptM_mul_compl he he' _ _).1, ← add_smul, add_sub_cancel, one_smul]

theorem pt_nb {e : AE D} (he : e * e = e) (hc : cA D e = e) {nb : hermA D n → G D n} (hnb : IsNMap nb)
    (x : hermS D n e) : pt e he hc (nb x.1) = nb x.1 := by
  apply mat_inj
  rw [mat_pt, hnb, ptM_unip he x.2]

theorem proj_weyl {w : G D n} (hw : IsW w) (v : Pl D) :
    proj D.sp.cm.sig (Jst D n) v w ∈ stabLoc D.sp.cm.sig (Jst D n) (stdLattice D.host.E (n + n)) v := by
  exact stab_of_weyl _ _ v _ (matHom_proj_weyl _ _ v w hw)

theorem proj_pt_zero {f : AE D} (hf : f * f = f) (hc : cA D f = f) (x : G D n) {v : Pl D} (h : cv D v f = 0) :
    proj D.sp.cm.sig (Jst D n) v (pt f hf hc x) = 1 := by
  refine matHom_injective _ _ _ (Units.ext ?_)
  rw [matHom_proj, map_one, bc_val]
  exact ptM_map_of_zero (cv D v) hf h (mat x)

theorem proj_pt_one {f : AE D} (hf : f * f = f) (hc : cA D f = f) (x : G D n) {v : Pl D} (h : cv D v f = 1) :
    proj D.sp.cm.sig (Jst D n) v (pt f hf hc x) = proj D.sp.cm.sig (Jst D n) v x := by
  refine matHom_injective _ _ _ (Units.ext ?_)
  rw [matHom_proj, matHom_proj, bc_val, bc_val]
  exact ptM_map_of_one (cv D v) hf h (mat x)

theorem projArch_pt_zero {f : AE D} (hf : f * f = f) (hc : cA D f = f) (x : G D n) {w : NumberField.InfinitePlace D.host.F}
    (h : compInf D.host.F D.host.E w f = 0) : projArch D.sp.cm.sig (Jst D n) w (pt f hf hc x) = 1 := by
  refine matHom_injective _ _ _ (Units.ext ?_)
  rw [matHom_projArch, map_one, bc_val]
  exact ptM_map_of_zero (compInf D.host.F D.host.E w) hf h (mat x)

theorem cv_of_mem {S : Finset (Pl D)} {e : AE D} (hS : IsIdem S e) {v : Pl D} (hv : v ∈ S) : cv D v e = 1 := by
  rw [hS.2 v, if_pos hv]

theorem cv_of_not_mem {S : Finset (Pl D)} {e : AE D} (hS : IsIdem S e) {v : Pl D} (hv : v ∉ S) : cv D v e = 0 := by
  rw [hS.2 v, if_neg hv]

theorem pt_mem_KOff {S : Finset (Pl D)} {e : AE D} (hS : IsIdem S e) (he' : (1 - e) * (1 - e) = 1 - e)
    (hc' : cA D (1 - e) = 1 - e) {x : G D n}
    (hx : ∀ v, proj D.sp.cm.sig (Jst D n) v x ∈ stabLoc D.sp.cm.sig (Jst D n) (stdLattice D.host.E (n + n)) v) :
    pt (1 - e) he' hc' x ∈ KOff D n S := by
  refine mem_levelOff.2 ⟨mem_finPts_iff_forall.2 fun w => ?_, fun v hv => ?_, fun v hv => ?_⟩
  · exact projArch_pt_zero he' hc' x (map_compl_zero _ (hS.1 w))
  · exact proj_pt_zero he' hc' x (map_compl_zero _ (cv_of_mem hS hv))
  · rw [proj_pt_one he' hc' x (map_compl_one _ (cv_of_not_mem hS hv))]
    exact hx v

theorem mat_inv_wn {w : G D n} (hw : IsW w) {nb : hermA D n → G D n} (hnb : IsNMap nb) (y : hermA D n) :
    mat (w * nb y)⁻¹ = blk4 (-y.1) (-1) 1 0 := by
  have hw' : mat w = blk4 0 1 (-1) 0 := hw
  have h1 : mat (w * nb y) * blk4 (-y.1) (-1) 1 0 = 1 := by
    rw [mat_mul', hw', hnb, weyl_inv]
  have h2 : mat (w * nb y)⁻¹ * mat (w * nb y) = 1 := by
    rw [← mat_mul', inv_mul_cancel, mat_one']
  calc mat (w * nb y)⁻¹ = mat (w * nb y)⁻¹ * (mat (w * nb y) * blk4 (-y.1) (-1) 1 0) := by
        rw [h1, mul_one]
    _ = blk4 (-y.1) (-1) 1 0 := by rw [← mul_assoc, h2, one_mul]

theorem cB_quot {e : AE D} (he : e * e = e) (hc : cA D e = e) {w : G D n} (hw : IsW w) {nb : hermA D n → G D n}
    (hnb : IsNMap nb) (g : G D n) (y : hermA D n) (hy : mm (e • cB g) y.1 = e • dB g) :
    cB (pt e he hc (g * (w * nb y)⁻¹)) = 0 := by
  rw [cB_pt, cB_mul, blkA_of (mat_inv_wn hw hnb y), cB_of (mat_inv_wn hw hnb y)]
  exact cell_alg hy

theorem cB_off {f : AE D} (hf : f * f = f) (hc : cA D f = f) {q : G D n} (hq : q ∈ P D n) :
    cB (pt f hf hc q) = 0 := by
  rw [cB_pt, cB_of_mem_P hq, smul_zero]

theorem decomp (hI : IdemEx) : Decomp := by
  intro D p nb hnb w hw S e hS g _ y hy
  obtain ⟨he, hc⟩ := (hI D S).2 e hS
  have he' := idem_compl he
  have hc' : cA D (1 - e) = 1 - e := by rw [map_sub, map_one, hc]
  obtain ⟨q₀, hq₀, k₀, hk₀, hgk⟩ := GlobalTheory.StdUnn.Iwasawa.exists_mul D p g
  have hA : pt e he hc (nb y.1) = nb y.1 := pt_nb he hc hnb y
  have key := assemble (pt e he hc) (pt (1 - e) he' hc') (pt_comm he hc he' hc')
    (pt_mul_compl_self he hc he' hc') (w := w) hA hgk
  refine ⟨pt e he hc (g * (w * nb y.1)⁻¹) * pt (1 - e) he' hc' q₀, ?_, pt (1 - e) he' hc' (w⁻¹ * k₀), ?_, key, ?_⟩
  · exact mul_mem (mem_siegelParabolic_of_lowerLeft_eq_zero (cB_quot he hc hw hnb g y.1 hy)) (mem_siegelParabolic_of_lowerLeft_eq_zero (cB_off he' hc' hq₀))
  · apply pt_mem_KOff hS he' hc'
    intro v
    have hk : proj D.sp.cm.sig (Jst D p) v k₀ ∈
        stabLoc D.sp.cm.sig (Jst D p) (stdLattice D.host.E (p + p)) v :=
      Subgroup.mem_iInf.1 (Subgroup.mem_inf.1 hk₀).1 v
    rw [map_mul, map_inv]
    exact mul_mem (inv_mem (proj_weyl hw v)) hk
  · intro x
    rw [← pt_nb he hc hnb x]
    exact pt_comm he hc he' hc' _ _

end Main

end GlobalTheory.CompanionTheory.CellDecomp

end
end

section

noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
namespace GlobalTheory.CompanionTheory.IwaAd
open GlobalTheory.StdUnn GlobalTheory.StdUnn.Model GlobalTheory.StdUnn.LeftInvSect PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
variable {D : D7} {n : ℕ}

theorem absA_pos (z : (AE D)ˣ) : 0 < absA D z := by
  have h : absA D z * absA D z⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
  exact pos_iff_ne_zero.2 fun h0 => by rw [h0, zero_mul] at h; exact zero_ne_one h

theorem npow_neg_nat {r : ℝ≥0} (hr : 0 < r) (m : ℕ) : ((((r ^ m)⁻¹ : ℝ≥0) : ℝ) : ℂ) = npow r (-(m : ℂ)) := by
  have h0 : ((r : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  simp [npow, Complex.cpow_neg, Complex.cpow_natCast]

theorem integral_comp_char {A : Type} [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A]
    [LocallyCompactSpace A] [SecondCountableTopology A] [T2Space A] [MeasurableSpace A] [BorelSpace A]
    (μ : Measure A) [μ.IsAddHaarMeasure] (φ : A ≃ₜ+ A) (f : A → ℂ) :
    ∫ y, f (φ y) ∂μ = ((((addEquivAddHaarChar φ)⁻¹ : ℝ≥0) : ℝ) : ℂ) * ∫ y, f y ∂μ := by
  have hmap : μ.map φ = (addEquivAddHaarChar φ)⁻¹ • μ := by
    have key := addEquivAddHaarChar_smul_map μ φ
    have hne : addEquivAddHaarChar φ ≠ 0 := (addEquivAddHaarChar_pos φ).ne'
    calc μ.map φ = ((addEquivAddHaarChar φ)⁻¹ * addEquivAddHaarChar φ) • μ.map φ := by
          rw [inv_mul_cancel₀ hne, one_smul]
      _ = (addEquivAddHaarChar φ)⁻¹ • μ := by rw [mul_smul, key]
  have hint : ∫ u, f u ∂(μ.map φ) = ∫ y, f (φ y) ∂μ :=
    integral_map_equiv (μ := μ) φ.toHomeomorph.toMeasurableEquiv f
  rw [← hint, hmap, integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul]

theorem nb_add {nb : hermA D n → G D n} (h : IsNMap nb) (x y : hermA D n) : nb (x + y) = nb x * nb y :=
  mat_inj (by
    rw [mat_mul, h, h, h, submatrix_fromBlocks_mul]
    simp [add_comm])

def cg (a : GL (Fin n) (AE D)) (c : hermA D n) : hermA D n :=
  ⟨a.1 * c.1 * adj a.1, by
    change adj (a.1 * c.1 * adj a.1) = a.1 * c.1 * adj a.1
    have hc : adj c.1 = c.1 := c.2
    rw [adj_mul, adj_mul, adj_adj, hc, Matrix.mul_assoc]⟩

theorem adj_mul_adj_inv (a : GL (Fin n) (AE D)) : (adj a.1 : Mx D n n) * adj (a⁻¹).1 = 1 := by
  rw [← adj_mul]; simp [adj_one]

theorem adj_inv_mul_adj (a : GL (Fin n) (AE D)) : (adj (a⁻¹).1 : Mx D n n) * adj a.1 = 1 := by
  rw [← adj_mul]; simp [adj_one]

def ad (a : GL (Fin n) (AE D)) : GL (Fin n) (AE D) :=
  ⟨adj (a⁻¹).1, adj a.1, adj_inv_mul_adj a, adj_mul_adj_inv a⟩

theorem nb_cg_mul {nb : hermA D n → G D n} (h : IsNMap nb) (a : GL (Fin n) (AE D)) {m : G D n}
    (hm : mat m = blk4 a.1 0 0 (adj (a⁻¹).1)) (c : hermA D n) : nb (cg a c) * m = m * nb c :=
  mat_inj (by
    rw [mat_mul, mat_mul, hm, h, h, submatrix_fromBlocks_mul, submatrix_fromBlocks_mul]
    have e : a.1 * c.1 * adj a.1 * adj (a⁻¹).1 = a.1 * c.1 := by
      rw [Matrix.mul_assoc, adj_mul_adj_inv, Matrix.mul_one]
    simp [cg, e, -Matrix.coe_units_inv])

theorem weyl_mul {w m m' : G D n} (hw : mat w = blk4 0 1 (-1) 0) (a : GL (Fin n) (AE D))
    (hm : mat m = blk4 a.1 0 0 (adj (a⁻¹).1)) (hm' : mat m' = blk4 (adj (a⁻¹).1) 0 0 a.1) : w * m = m' * w :=
  mat_inj (by
    rw [mat_mul, mat_mul, hm, hw, hm', submatrix_fromBlocks_mul, submatrix_fromBlocks_mul]
    simp)

theorem mulVec_mem_upper {g : G D n} {x y : Mx D n n} (hg : mat g = blk4 x 0 0 y) {v : Fin (n + n) → AE D}
    (hv : v ∈ upperHalf D n) : (mat g).mulVec v ∈ upperHalf D n := by
  have hv' : ∀ i : Fin n, v (finSumFinEquiv (Sum.inr i : Fin n ⊕ Fin n)) = 0 := fun i => congrFun hv i
  refine LinearMap.mem_ker.2 (funext fun i => ?_)
  simp only [LinearMap.funLeft_apply, Pi.zero_apply, hg, Matrix.mulVec, dotProduct]
  rw [← finSumFinEquiv.sum_comp, Fintype.sum_sum_type]
  simp only [blk4, Matrix.submatrix_apply, Equiv.symm_apply_apply, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂,
    hv', mul_zero, Matrix.zero_apply, zero_mul, Finset.sum_const_zero, add_zero]

theorem levi_mem_P {g g' : G D n} {x y x' y' : Mx D n n} (hg : mat g = blk4 x 0 0 y) (hg' : mat g' = blk4 x' 0 0 y')
    (h1 : g' * g = 1) : g ∈ P D n := by
  have hinv : g⁻¹ = g' := inv_eq_of_mul_eq_one_left h1
  intro v
  refine ⟨fun hv => mulVec_mem_upper hg hv, fun hv => ?_⟩
  have h2 := mulVec_mem_upper hg' (v := (mat g).mulVec v) hv
  rwa [Matrix.mulVec_mulVec, ← mat_mul, h1, mat_one, Matrix.one_mulVec] at h2

theorem height_mul {H : G D n → ℝ≥0} (hH : IsHeight H) {p : G D n} (hp : p ∈ P D n) (a : GL (Fin n) (AE D))
    (ha : blkA (mat p) = a.1) (x : G D n) :
    H (p * x) = absA D (Matrix.GeneralLinearGroup.det a) * H x := by
  obtain ⟨q, hq, k, hk, rfl⟩ := GlobalTheory.StdUnn.Iwasawa.exists_mul D n x
  obtain ⟨c, hc⟩ := exists_blkA hq
  have e : blkA (mat (p * q)) = (a * c).1 := by rw [blkA_mul hq, ha, hc, Units.val_mul]
  rw [← mul_assoc, hH _ ((P D n).mul_mem hp hq) (a * c) e k hk, hH q hq c hc k hk, map_mul, map_mul]

end GlobalTheory.CompanionTheory.IwaAd
end
end

section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.BigCellJ

theorem integrable_schwartzA {D : D7} {θ : InfFam D} (hθ : IsInfFam θ) {m n : ℕ} {μ : Measure (Mx D m n)}
    {𝓕 : Set (Mx D m n)} (hμ : IsCovolOne (ratMx D m n) μ 𝓕) {φ : Mx D m n → ℂ}
    (hφ : φ ∈ schwartzA θ m n) : Integrable φ μ := by
  obtain ⟨i1, i2, i3, i4, i5, K, hK, hKc⟩ := GlobalTheory.TowerRestrict.lattice_Mx D m n
  haveI : BorelSpace (Mx D m n) := ⟨rfl⟩
  haveI := hμ.1
  haveI i6 : DiscreteTopology (ratMx D m n) := i5
  haveI : SecondCountableTopology (ratMx D m n) := TopologicalSpace.Subtype.secondCountableTopology _
  haveI : Countable (ratMx D m n) := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  have hc : Continuous φ := (GlobalTheory.CompanionTheory.WeilTheta.schwartzA_continuous_and_dominated D θ hθ _ _ φ hφ).1
  have hU : GlobalTheory.CompanionTheory.Hypotheses₂.OneV.PoiAbs.UnifSummable (ratMx D m n).subtype φ := fun Q hQ => by
    obtain ⟨b, hb1, hb2⟩ := GlobalTheory.CompanionTheory.ThetaPoisson.translates_bound hθ ⟨φ, hφ⟩ Q hQ
    refine ⟨b, hb1, fun c x hx => ?_⟩
    have h := hb2 x hx c
    rwa [add_comm] at h
  exact GlobalTheory.CompanionTheory.Hypotheses₂.OneV.PoiAbs.integrable_of_unif hc hU μ hK fun x => by
    obtain ⟨γ, hγ, h⟩ := hKc x
    refine ⟨⟨-γ, (ratMx D m n).neg_mem hγ⟩, ?_⟩
    simpa [sub_neg_eq_add, add_comm] using h

theorem continuous_halfTr {D : D7} : Continuous (halfTr : AE D → AF D.host.F) := by
  haveI := isTopologicalRing_tens (F := D.host.F) (E := D.host.E) (R := AF D.host.F)
  haveI : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  have ht : Continuous (trA : AE D → AF D.host.F) :=
    IsModuleTopology.continuous_of_linearMap (Algebra.trace (AF D.host.F) (AE D))
  unfold halfTr
  exact continuous_const.mul ht

theorem continuous_integral_twist {X Y : Type*} [TopologicalSpace X] [FirstCountableTopology X]
    [TopologicalSpace Y] [SecondCountableTopology Y] [MeasurableSpace Y] [OpensMeasurableSpace Y]
    {μ : Measure Y} {φ : Y → ℂ} {g : X → Y → ℂ} (hi : Integrable φ μ)
    (hj : Continuous fun p : X × Y => g p.1 p.2) (hn : ∀ b y, ‖g b y‖ = 1) :
    Continuous fun b => ∫ y, φ y * g b y ∂μ := by
  have hg1 : ∀ b, AEStronglyMeasurable (g b) μ := fun b =>
    (hj.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  have hg2 : ∀ y, Continuous fun b => g b y := fun y =>
    hj.comp (continuous_id.prodMk continuous_const)
  refine continuous_of_dominated (bound := fun y => ‖φ y‖) (fun b => ?_) (fun b => ?_) hi.norm ?_
  · exact hi.aestronglyMeasurable.mul (hg1 b)
  · refine Filter.Eventually.of_forall fun y => ?_
    rw [norm_mul, hn, mul_one]
  · refine Filter.Eventually.of_forall fun y => ?_
    exact (hg2 y).const_mul (φ y)

theorem continuous_inner_self {D : D7} (V : HSp D) (r : ℕ) :
    Continuous fun y : Mx D V.rank r => (GlobalTheory.StdUnn.inner V y y : Mx D r r) := by
  haveI := isTopologicalRing_tens (F := D.host.F) (E := D.host.E) (R := AF D.host.F)
  unfold GlobalTheory.StdUnn.inner
  exact GlobalTheory.MixModel.continuous_adj.matrix_mul (continuous_const.matrix_mul continuous_id)

theorem continuous_phase {D : D7} (V : HSp D) (r : ℕ) {ψ : AddChar (AF D.host.F) ℂ}
    (hψ : IsCharAF D.host.F ψ) :
    Continuous fun p : hermA D r × Mx D V.rank r =>
      ψ (halfTr (Matrix.trace (HMul.hMul p.1.1 (GlobalTheory.StdUnn.inner V p.2 p.2) : Mx D r r))) := by
  haveI := isTopologicalRing_tens (F := D.host.F) (E := D.host.E) (R := AF D.host.F)
  exact hψ.1.comp (continuous_halfTr.comp
    ((continuous_subtype_val.comp continuous_fst).matrix_mul
      ((continuous_inner_self V r).comp continuous_snd)).matrix_trace)

theorem jt_continuous : ∀ (D : D7) (r : ℕ) (V : HSp D) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D)
    (μ : Measure (Mx D V.rank r)) (φ : Mx D V.rank r → ℂ), IsCharAF D.host.F ψ → IsInfFam θ →
    (∃ 𝓕, IsCovolOne (ratMx D V.rank r) μ 𝓕) → φ ∈ schwartzA θ V.rank r → Continuous (Jt ψ V μ φ) := by
  intro D r V ψ θ μ φ hψ hθ ⟨𝓕, hμ⟩ hφ
  obtain ⟨i1, i2, i3, i4, i5, -⟩ := GlobalTheory.TowerRestrict.lattice_Mx D V.rank r
  obtain ⟨j1, j2, j3, j4, j5, -⟩ := GlobalTheory.TowerRestrict.lattice_Mx D r r
  haveI : BorelSpace (Mx D V.rank r) := ⟨rfl⟩
  haveI : SecondCountableTopology (hermA D r) := TopologicalSpace.Subtype.secondCountableTopology _
  haveI : FirstCountableTopology (hermA D r) :=
    TopologicalSpace.SecondCountableTopology.to_firstCountableTopology _
  exact continuous_integral_twist (g := fun (b : hermA D r) (y : Mx D V.rank r) =>
      ψ (halfTr (Matrix.trace (HMul.hMul b.1 (GlobalTheory.StdUnn.inner V y y) : Mx D r r))))
    (integrable_schwartzA hθ hμ hφ) (continuous_phase V r hψ) (fun b y => hψ.2.1 _)

end GlobalTheory.CompanionTheory.BigCellJ

end
end
