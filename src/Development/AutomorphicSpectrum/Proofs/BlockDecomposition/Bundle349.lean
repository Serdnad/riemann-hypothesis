module

import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle332
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle333
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle312
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle150
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle338
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.ColMatMulGlEmbMat
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle001
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
public import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
public import Mathlib.Basic.Complex.Basic
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle328
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle002
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle127
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle326
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivProdIrrTw
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsIrreducibleSubquotientTwoBlockConstituents
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle134
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.SegmentCuspLines.Bundle001
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.LSegJacquet
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle302
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.TwistedKernels.ExPhiPlusOnto
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle313
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle316
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle297
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.LeibnizDerivatives.EPGFalseEqLastIff
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.UnipApplyCastSuccLast
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.LeibnizOrders.ProdGPn
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.GenericUnlinkedGL.UnlinkedRealize
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyCosocles.LUnlinkedComm

@[expose] public section

section

noncomputable section

open Matrix MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZSeg GlobalTheory.BZMir GlobalTheory.SplitWeil GlobalTheory.CompanionTheory.MirFourier GlobalTheory.CompanionTheory.BZOnto.PerpSmall ValuativeRel Zc
open scoped Topology

namespace GlobalTheory.CompanionTheory.MirPair

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem continuous_leviMir (m : ℕ) : Continuous (levi k m) := by
  apply _root_.GlobalTheory.CompanionTheory.MirPair.ShearOrbit.continuous_levi <;> assumption

theorem tendsto_shearGL_zero (n : ℕ) :
    Filter.Tendsto (shearGL (k := k) n) (𝓝 0) (𝓝 1) := by
  have key : ∀ b : Fin (n + 1) → k, 1 + b (Fin.last n) ≠ 0 →
      ((GlobalTheory.CompanionTheory.MirPair.shearGL n b : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) =
        1 + vecMulVec (GlobalTheory.BZMir.eLast k n) b ∧
      (((GlobalTheory.CompanionTheory.MirPair.shearGL n b)⁻¹ : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) =
        1 - (1 + b (Fin.last n))⁻¹ • vecMulVec (GlobalTheory.BZMir.eLast k n) b := by
    intro b hb
    have hd : b ⬝ᵥ GlobalTheory.BZMir.eLast k n = b (Fin.last n) := by
      simp [GlobalTheory.BZMir.eLast, dotProduct_single]
    have hM : vecMulVec (GlobalTheory.BZMir.eLast k n) b * vecMulVec (GlobalTheory.BZMir.eLast k n) b =
        b (Fin.last n) • vecMulVec (GlobalTheory.BZMir.eLast k n) b := by
      rw [vecMulVec_mul_vecMulVec, hd]
      ext i j
      simp only [vecMulVec_apply, Pi.smul_apply, Matrix.smul_apply, smul_eq_mul]
      ring
    have hc : (1 + b (Fin.last n))⁻¹ + (1 + b (Fin.last n))⁻¹ * b (Fin.last n) = 1 := by
      rw [← mul_one_add]
      exact inv_mul_cancel₀ hb
    have hmul : (1 + vecMulVec (GlobalTheory.BZMir.eLast k n) b) *
        (1 - (1 + b (Fin.last n))⁻¹ • vecMulVec (GlobalTheory.BZMir.eLast k n) b) = 1 := by
      rw [mul_sub, mul_one, mul_smul_comm, add_mul, one_mul, hM, smul_add, smul_smul, ← add_smul, hc,
        one_smul, add_sub_cancel_right]
    have hu : IsUnit (1 + vecMulVec (GlobalTheory.BZMir.eLast k n) b) :=
      ⟨⟨_, _, hmul, mul_eq_one_comm.mp hmul⟩, rfl⟩
    have hcoe : ((GlobalTheory.CompanionTheory.MirPair.shearGL n b : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) =
        1 + vecMulVec (GlobalTheory.BZMir.eLast k n) b := by
      rw [GlobalTheory.CompanionTheory.MirPair.shearGL, dite_eq_left hu]
      exact hu.unit_spec
    refine ⟨hcoe, Units.inv_eq_of_mul_eq_one_right ?_⟩
    rw [hcoe]
    exact hmul
  have h0 : {x : k | valuation k x < 1} ∈ 𝓝 (0 : k) := by
    have h := (IsValuativeTopology.hasBasis_nhds_zero k).mem_of_mem (i := 1) trivial
    simpa using h
  have hev : ∀ᶠ b : Fin (n + 1) → k in 𝓝 0, 1 + b (Fin.last n) ≠ 0 := by
    have h1 : ∀ᶠ b : Fin (n + 1) → k in 𝓝 0, valuation k (b (Fin.last n)) < 1 :=
      (continuous_apply (Fin.last n)).continuousAt.preimage_mem_nhds
        (show {x : k | valuation k x < 1} ∈ 𝓝 ((fun b : Fin (n + 1) → k => b (Fin.last n)) 0) from h0)
    filter_upwards [h1] with b hb h
    have h2 := (valuation k).map_one_add_of_lt hb
    rw [h, map_zero] at h2
    exact zero_ne_one h2
  have hv : Continuous fun b : Fin (n + 1) → k => vecMulVec (GlobalTheory.BZMir.eLast k n) b :=
    continuous_matrix fun i j => by
      simp only [vecMulVec_apply]
      exact continuous_const.mul (continuous_apply j)
  have hv0 : vecMulVec (GlobalTheory.BZMir.eLast k n) (0 : Fin (n + 1) → k) = 0 := by
    ext i j
    simp [vecMulVec_apply]
  have h1 : Filter.Tendsto (fun b : Fin (n + 1) → k => 1 + vecMulVec (GlobalTheory.BZMir.eLast k n) b)
      (𝓝 0) (𝓝 1) := by
    have hc : Continuous fun b : Fin (n + 1) → k =>
        (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) k) + vecMulVec (GlobalTheory.BZMir.eLast k n) b :=
      continuous_const.add hv
    simpa [hv0] using hc.tendsto (0 : Fin (n + 1) → k)
  have hinv0 : Filter.Tendsto (fun b : Fin (n + 1) → k => (1 + b (Fin.last n))⁻¹) (𝓝 0) (𝓝 1) := by
    have h : Filter.Tendsto (fun b : Fin (n + 1) → k => 1 + b (Fin.last n)) (𝓝 0) (𝓝 1) := by
      have hc : Continuous fun b : Fin (n + 1) → k => (1 : k) + b (Fin.last n) :=
        continuous_const.add (continuous_apply (Fin.last n))
      simpa using hc.tendsto (0 : Fin (n + 1) → k)
    simpa using h.inv₀ one_ne_zero
  have h2 : Filter.Tendsto (fun b : Fin (n + 1) → k =>
      1 - (1 + b (Fin.last n))⁻¹ • vecMulVec (GlobalTheory.BZMir.eLast k n) b) (𝓝 0) (𝓝 1) := by
    have hconst : Filter.Tendsto (fun _ : Fin (n + 1) → k => (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) k))
        (𝓝 0) (𝓝 1) := tendsto_const_nhds
    have h := hconst.sub (hinv0.smul (hv.tendsto 0))
    simpa [hv0] using h
  have h1' : Filter.Tendsto (fun b : Fin (n + 1) → k =>
      ((GlobalTheory.CompanionTheory.MirPair.shearGL n b : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k))
      (𝓝 0) (𝓝 1) := by
    refine h1.congr' ?_
    filter_upwards [hev] with b hb
    exact (key b hb).1.symm
  have h2' : Filter.Tendsto (fun b : Fin (n + 1) → k =>
      (((GlobalTheory.CompanionTheory.MirPair.shearGL n b)⁻¹ : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k))
      (𝓝 0) (𝓝 1) := by
    refine h2.congr' ?_
    filter_upwards [hev] with b hb
    exact (key b hb).2.symm
  rw [Units.isEmbedding_embedProduct.tendsto_nhds_iff]
  simp only [Function.comp_def, Units.embedProduct_apply, inv_one, Units.val_one]
  exact h1'.prodMk_nhds ((MulOpposite.continuous_op.tendsto _).comp h2')

theorem shear_fix_vector {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (T : Representation ℂ (Mir k (n + 1)) V) (hT : IsSmooth T) (v : V) :
    ∃ r : kˣ, valuation k (r : k) < 1 ∧
      ∀ b ∈ box (n + 1) r, T (levi k (n + 1) (shearGL n b)) v = v := by
  have hopen : IsOpen {g : GlobalTheory.BZMir.Mir k (n + 1) | T g v = v} := hT v
  have htend : Filter.Tendsto (fun b : Fin (n + 1) → k => GlobalTheory.BZMir.levi k (n + 1) (GlobalTheory.CompanionTheory.MirPair.shearGL n b))
      (𝓝 0) (𝓝 1) := by
    have h := ((GlobalTheory.CompanionTheory.MirPair.continuous_leviMir (k := k) (n + 1)).tendsto 1).comp (GlobalTheory.CompanionTheory.MirPair.tendsto_shearGL_zero (k := k) n)
    rw [map_one] at h
    exact h
  have hΩ : (fun b : Fin (n + 1) → k => GlobalTheory.BZMir.levi k (n + 1) (GlobalTheory.CompanionTheory.MirPair.shearGL n b)) ⁻¹'
      {g | T g v = v} ∈ 𝓝 (0 : Fin (n + 1) → k) :=
    htend (hopen.mem_nhds (by simp))
  obtain ⟨r, hr⟩ := GlobalTheory.CompanionTheory.BZOnto.PerpSmall.exists_box_subset hΩ
  haveI : (valuation k).IsNontrivial :=
    (ValuativeRel.isNontrivial_iff_isNontrivial (valuation k)).1 inferInstance
  obtain ⟨x, hx0, hx1⟩ := Valuation.IsNontrivial.exists_lt_one (v := valuation k)
  by_cases hr1 : valuation k (r : k) < 1
  · exact ⟨r, hr1, fun b hb => hr hb⟩
  · refine ⟨Units.mk0 x hx0, by simpa using hx1, fun b hb => hr ?_⟩
    intro j
    have h1 : valuation k (b j) ≤ valuation k x := hb j
    show valuation k (b j) ≤ valuation k (r : k)
    exact le_trans h1 (le_trans hx1.le (not_lt.mp hr1))

end GlobalTheory.CompanionTheory.MirPair

end
end

section

open Matrix MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZSeg GlobalTheory.BZMir GlobalTheory.SplitWeil GlobalTheory.CompanionTheory.MirFourier GlobalTheory.CompanionTheory.BZOnto.PerpSmall ValuativeRel Zc
open scoped Topology
open GlobalTheory.CompanionTheory.MirPair

namespace GlobalTheory.CompanionTheory.MirPair

theorem continuous_coef : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ} {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] (T : Representation ℂ (Mir k n) V) (B : V →ₗ[ℂ] V' →ₗ[ℂ] ℂ), IsSmooth T → ∀ (v : V) (v' : V'), Continuous (coef T B v v') := by
  apply GlobalTheory.CompanionTheory.MirPair.EvLin.continuous_coef <;> assumption

end GlobalTheory.CompanionTheory.MirPair
end

section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibPhi Topology
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.LeibPhi.UNorm

theorem mirProj_eq_one_of_mem {k : Type} [Field k] {n : ℕ} (u : Mir k n) (hu : u ∈ MirUin k n) :
    mirabolicProjection k n u = 1 := by
  rw [GlobalTheory.BZMir.MirUin, Subgroup.mem_subgroupOf, GlobalTheory.BZMir.MirU,
    MonoidHom.mem_range] at hu
  obtain ⟨v, hv⟩ := hu
  apply Units.ext
  ext i j
  change ((u : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) i.castSucc j.castSucc =
    (1 : Matrix (Fin n) (Fin n) k) i j
  rw [← hv]
  change (1 + GlobalTheory.BZMir.colMat k n (Multiplicative.toAdd v)) i.castSucc j.castSucc = _
  simp [GlobalTheory.BZMir.colMat, Matrix.one_apply, Fin.castSucc_ne_last]

theorem mem_of_mirProj_eq_one {k : Type} [Field k] {n : ℕ} (u : Mir k n) (hu : mirabolicProjection k n u = 1) :
    u ∈ MirUin k n := by
  apply GlobalTheory.CompanionTheory.BZPhiPG.Grp.mem_of_mirProj_eq_one' <;> assumption

theorem mirUin_normal : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (n : ℕ), (MirUin k n).Normal := by
  intro k _ _ _ _ n
  refine ⟨fun u hu g => ?_⟩
  apply GlobalTheory.CompanionTheory.LeibPhi.UNorm.mem_of_mirProj_eq_one
  rw [map_mul, map_mul, map_inv, GlobalTheory.CompanionTheory.LeibPhi.UNorm.mirProj_eq_one_of_mem u hu,
    mul_one, mul_inv_cancel]

end GlobalTheory.CompanionTheory.LeibPhi.UNorm
end
end

section

noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.BZMir GlobalTheory.BZMir.Fun

namespace GlobalTheory.CompanionTheory.BZMirAdj

section Alg

variable (k : Type) [Field k]

theorem mirProj_levi (n : ℕ) (g : GL (Fin n) k) : mirabolicProjection k n (levi k n g) = g := by
  apply Units.ext
  ext i j
  change GlobalTheory.BZMir.blockMat k n (GlobalTheory.BZMir.glEmbMat k n (g : Matrix (Fin n) (Fin n) k)) i j =
    (g : Matrix (Fin n) (Fin n) k) i j
  simp [GlobalTheory.BZMir.blockMat, GlobalTheory.BZMir.glEmbMat]

theorem mirProj_eq_one_of_mem (n : ℕ) (u : Mir k n) (hu : u ∈ MirUin k n) : mirabolicProjection k n u = 1 := by
  rw [GlobalTheory.BZMir.MirUin, Subgroup.mem_subgroupOf, GlobalTheory.BZMir.MirU,
    MonoidHom.mem_range] at hu
  obtain ⟨v, hv⟩ := hu
  apply Units.ext
  ext i j
  change GlobalTheory.BZMir.blockMat k n ((u : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) i j =
    (1 : Matrix (Fin n) (Fin n) k) i j
  rw [GlobalTheory.BZMir.blockMat, ← hv]
  change ((1 : Matrix (Fin (n + 1)) (Fin (n + 1)) k) +
    GlobalTheory.BZMir.colMat k n (Multiplicative.toAdd v)) (Fin.castSucc i) (Fin.castSucc j) =
    (1 : Matrix (Fin n) (Fin n) k) i j
  simp [GlobalTheory.BZMir.colMat, Matrix.one_apply, Fin.castSucc_ne_last]

theorem mem_of_mirProj_eq_one (n : ℕ) (y : Mir k n) (hy : mirabolicProjection k n y = 1) : y ∈ MirUin k n := by
  apply GlobalTheory.CompanionTheory.BZPhiPG.Grp.mem_of_mirProj_eq_one' <;> assumption

end Alg

section Rep

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

end Rep

end GlobalTheory.CompanionTheory.BZMirAdj
end
end

section


theorem _root_.GlobalTheory.T.admissible_parabolic_induction : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {c n : ℕ} (N : Fin c → ℕ) (h : ∑ i, N i = n) (σ : ∀ i, GlobalTheory.CuspRep.SmIrr (GL (Fin (N i)) k)), GlobalTheory.PRep.IsAdmissible (GlobalTheory.SmGL.multiProd (GlobalTheory.SmGL.stdBlocks N h) fun i => (σ i).ρ) := by
  first | exact @GlobalTheory.CompanionTheory.ProdAdm.isAdmissible_multiProd_smIrr | exact GlobalTheory.CompanionTheory.ProdAdm.isAdmissible_multiProd_smIrr | (intros; apply GlobalTheory.CompanionTheory.ProdAdm.isAdmissible_multiProd_smIrr <;> assumption)
end

section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZRes Topology
open scoped TensorProduct

theorem _root_.GlobalTheory.T.support_induced_function_closed : ∀ {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {W₁ : Type} [AddCommGroup W₁] [Module ℂ W₁] {Q : Subgroup G} (σ : Representation ℂ Q W₁) (f : smoothPart (ind Q σ)), IsClosed {g : G | f.1.1 g ≠ 0} := by
  first | exact @GlobalTheory.CompanionTheory.BZRes.isClosed_support_smooth_ind | exact GlobalTheory.CompanionTheory.BZRes.isClosed_support_smooth_ind | (intros; apply GlobalTheory.CompanionTheory.BZRes.isClosed_support_smooth_ind <;> assumption)
end

section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.BZPsiPG
open scoped TensorProduct

theorem _root_.GlobalTheory.T.exists_induced_section_supported_open : ∀ {G Z : Type} [Group G] [AddCommGroup Z] [Module ℂ Z] [TopologicalSpace G] [IsTopologicalGroup G] (H : Subgroup G) (ρ : Representation ℂ H Z) (B : Subgroup G), IsOpen (B : Set G) → IsCompact (B : Set G) → ∀ z : Z, (∀ h : H, (h : G) ∈ B → ρ h z = z) → ∃ b : cIndSpace H ρ, (∀ (h : H) (β : G), β ∈ B → b.1.1.1 ((h : G) * β) = ρ h z) ∧ ∀ p : G, (¬ ∃ h : H, ∃ β ∈ B, p = (h : G) * β) → b.1.1.1 p = 0 := by
  first | exact @GlobalTheory.CompanionTheory.HBBump.exists_bump | exact GlobalTheory.CompanionTheory.HBBump.exists_bump | (intros; apply GlobalTheory.CompanionTheory.HBBump.exists_bump <;> assumption)
end

section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.BZPsiPG
open scoped TensorProduct

theorem _root_.GlobalTheory.T.sum_over_compact_cosets_jacquet_kernel : ∀ {G Z : Type} [Group G] [AddCommGroup Z] [Module ℂ Z] [TopologicalSpace G] [IsTopologicalGroup G] (ρ : Representation ℂ G Z), IsSmooth ρ → ∀ (L : Subgroup G), IsCompact (L : Set G) → ∀ v : Z, v ∈ twKer ρ L 1 → ∀ (K : Subgroup L) (T : Finset L), IsOpen (K : Set L) → (∀ x ∈ K, ρ (x : G) v = v) → (∀ x : L, ∃! t, t ∈ T ∧ t⁻¹ * x ∈ K) → ∑ t ∈ T, ρ (t : G) v = 0 := by
  first | exact @GlobalTheory.CompanionTheory.TwistedAverage.sum_reps_eq_zero_of_mem_twKer | exact GlobalTheory.CompanionTheory.TwistedAverage.sum_reps_eq_zero_of_mem_twKer | (intros; apply GlobalTheory.CompanionTheory.TwistedAverage.sum_reps_eq_zero_of_mem_twKer <;> assumption)
end

section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL Filter Topology

theorem _root_.GlobalTheory.T.square_integrable_unitarizable : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (x : IrrGL (k := k)), IsSqIntCoeff x.rep → IsUnitarisable x.rep := by
  first | exact @GlobalTheory.CompanionTheory.SqIntUnit.isUnitarisable_of_isSqIntCoeff | exact GlobalTheory.CompanionTheory.SqIntUnit.isUnitarisable_of_isSqIntCoeff | (intros; apply GlobalTheory.CompanionTheory.SqIntUnit.isUnitarisable_of_isSqIntCoeff <;> assumption)
end

section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.RgGu
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.GenSupp

theorem hasSupport_std : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V) (s : Multiset (IrrGL (k := k))), HasSupport π s → ∃ (h : ℕ) (x : Fin h → IrrGL (k := k)) (hd : ∑ a, (x a).1 = N), Finset.univ.val.map x = s ∧ (∀ a, (x a).IsCusp) ∧ IsSubquotient π (prodIrr x hd) := by
  intro k _ _ _ _ N V _ _ π s hπ
  obtain ⟨h, x, hs, -, hc, e, hsq⟩ := hπ
  have hd : ∑ a, (x a).1 = N := by
    have := Fintype.card_congr e
    simpa [Fintype.card_sigma] using this
  obtain ⟨φ⟩ := GlobalTheory.T.multiProd_equiv_standard_blocks k (fun a => (x a).1) hd e _ (fun a => (x a).rep)
  exact ⟨h, x, hd, hs, fun a => ⟨(hc a).1, (hc a).2.2⟩, hsq.trans (GlobalTheory.JacStages.isSubquotient_of_equiv φ)⟩

end GlobalTheory.CompanionTheory.GenSupp
end

section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc

namespace GlobalTheory.CompanionTheory.ExhGood

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem ind₂_map_injective_right {r t N : ℕ} (e : Fin r ⊕ Fin t ≃ Fin N) {U W W' : Type} [AddCommGroup U] [Module ℂ U]
    [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W'] (σ : Representation ℂ (GL (Fin r) k) U)
    {ρ : Representation ℂ (GL (Fin t) k) W} {ρ' : Representation ℂ (GL (Fin t) k) W'} (f : ρ.IntertwiningMap ρ')
    (hf : Function.Injective f) :
    ∃ F : (ind₂ e (extTensor σ ρ)).IntertwiningMap (ind₂ e (extTensor σ ρ')), Function.Injective F := by
  have hι : Function.Injective (GlobalTheory.ParIndExact.extTensorMapRight σ f) :=
    Module.Flat.lTensor_preserves_injective_linearMap f.toLinearMap hf
  have hι' : Function.Injective
      (compMap (GlobalTheory.ParIndExact.extTensorMapRight σ f) (leviTwo k (Fin r) (Fin t)).symm.toMonoidHom) := hι
  exact ⟨parIndMap (two e)
      (compMap (GlobalTheory.ParIndExact.extTensorMapRight σ f) (leviTwo k (Fin r) (Fin t)).symm.toMonoidHom),
    GlobalTheory.ParIndExact.parIndMap_injective _ _ hι'⟩

theorem pair_equiv {N : ℕ} (y : Fin 2 → IrrGL (k := k)) (hd : ∑ i, (y i).1 = N) {a : IrrGL (k := k)} (ha : y 0 = a)
    (h : a.1 + (y 1).1 = N) :
    Nonempty ((ind₂ (stdSum h) (extTensor a.rep (y 1).rep)).Equiv (prodIrr y hd)) := by
  subst ha h
  exact nonempty_prod₂_equiv_prodIrr_rep y hd

theorem embed_family {N c : ℕ} (y : Fin 2 → IrrGL (k := k)) (v : Fin (c + 1) → IrrGL (k := k)) (t : Fin c → IrrGL (k := k))
    (h0 : y 0 = v 0) (hs : ∀ i, v i.succ = t i) (hd : ∑ i, (y i).1 = N) (hv : ∑ i, (v i).1 = N)
    (ht : ∑ i, (t i).1 = (y 1).1) (g : (y 1).rep.IntertwiningMap (prodIrr t ht)) (hg : Function.Injective g) :
    ∃ F : (prodIrr y hd).IntertwiningMap (prodIrr v hv), Function.Injective F := by
  have e : t = fun i => v i.succ := funext fun i => (hs i).symm
  subst e
  have h : (v 0).1 + (y 1).1 = N := by
    rw [← h0, ← hd, Fin.sum_univ_two]
  have A0 := pair_equiv y hd h0 h
  have B0 := GlobalTheory.ProdReorder.multiProd_head (k := k) (d := fun i => (v i).1) (fun i => (v i).rep)
    (stdBlocks (fun i => (v i).1) hv) h (stdBlocks (fun i : Fin c => (v i.succ).1) ht)
  have F0 := ind₂_map_injective_right (stdSum h) (v 0).rep g hg
  obtain ⟨A⟩ := A0
  obtain ⟨B⟩ := B0
  obtain ⟨F, hF⟩ := F0
  exact ⟨(B.symm.toIntertwiningMap.comp F).comp A.symm.toIntertwiningMap,
    B.symm.toLinearEquiv.injective.comp (hF.comp A.symm.toLinearEquiv.injective)⟩

theorem isOrderedForm_snoc {h : ℕ} {Δ : Fin h → Segment k} {𝔫 : Multiset (Segment k)} (H : IsOrderedForm Δ 𝔫)
    (s : Segment k) (hs : ∀ D ∈ 𝔫, ¬ D.Precedes s) :
    IsOrderedForm (Fin.snoc (α := fun _ => Segment k) Δ s) (𝔫 + {s}) := by
  refine ⟨?_, fun i j hij => ?_⟩
  · rw [← H.1, Fin.univ_val_map, Fin.univ_val_map, List.ofFn_succ']
    simpa using (Multiset.coe_add _ [s]).symm
  · induction j using Fin.lastCases with
    | last =>
      obtain ⟨i, rfl⟩ : ∃ i', Fin.castSucc i' = i :=
        ⟨i.castPred (Fin.ne_last_of_lt hij), by simp⟩
      simp only [Fin.snoc_castSucc, Fin.snoc_last]
      exact hs _ (H.1 ▸ Multiset.mem_map_of_mem _ (Finset.mem_univ_val i))
    | cast j =>
      obtain ⟨i, rfl⟩ : ∃ i', Fin.castSucc i' = i :=
        ⟨i.castPred (Fin.ne_last_of_lt hij), by simp⟩
      simp only [Fin.snoc_castSucc]
      exact H.2 i j (by simpa using hij)

end GlobalTheory.CompanionTheory.ExhGood

end
end

section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Cos GlobalTheory.SplitRead GlobalTheory.ProdReorder

noncomputable section

namespace GlobalTheory.CompanionTheory.SegReorder

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem famCongr {u : ℕ} {f g : Fin u → IrrGL (k := k)} (hfg : ∀ i, f i = g i) {T : ℕ}
    (e : (Σ i, Fin (f i).1) ≃ Fin T) (e' : (Σ i, Fin (g i).1) ≃ Fin T) :
    Nonempty ((multiProd e fun i => (f i).rep).Equiv (multiProd e' fun i => (g i).rep)) := by
  obtain rfl : f = g := funext hfg
  exact multiProd_placing e e' _

end GlobalTheory.CompanionTheory.SegReorder
end
end
