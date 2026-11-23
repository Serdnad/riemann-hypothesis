module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle011
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Formalism.SharpRestriction.Divisibility.LiftErrorLocal
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle613
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle200
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftMatrixComputesLiftRational
import Formalism.LocalToGlobal.Divisibility.LiftLatLemmas
import Formalism.LocalToGlobal.IndefiniteReal.CxLemmas
import Formalism.LocalToGlobal.IndefiniteReal.NormalDecomposition.UnitaryTwoPackage
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle261

@[expose] public section

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3
open Classical
open GlobalTheory.Mem.R3.HasLabelling

noncomputable section

namespace GlobalTheory.Mem.LiftOnto



theorem thetaMap_surjective : GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y), Pins R F cG → Holds R F → HostHyp D → ∀ (i : Fin D.R.m) (t : T), Used0 D (Y.tup t) → Function.Surjective (D.what₂.thetaP (Y.tup t) ((i : ℕ) + 1)) := by
  intro _ _ _ _ D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y Z hP hH _ i t _
  have hR := complex_data_conditions_base_level_of_primitive_links hH.ok hH.sep hP.char hH.prim
  have hb : Function.Bijective ((A3.indefDown (s0Of R F)).θ i t).mulVec :=
    CxData.liftMat_bij (R.toCx3 F) F.cr false hR.kForm hR.ewNorm (hR.h4pos.2.2 false) hR.lifts0.1 hR.ratTh i t
  have hB : BlockHyp (A3.A.fam.L i t) (A3.A.fam.lvlA F.P0 F.ψ0) A3.A.v0 1 :=
    ⟨hH.ok.ok2.conj, hH.ok.ok2.irr, hH.ok.ok2.lifts i t⟩
  have hp : Formalism.DivisionValues.IsOrthProj (lH D A3.A F.P0 F.ψ0 i t) (lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t)
      (lPrj D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t) := BlockDat.lf_l_proj hB
  obtain ⟨hTh, hθ⟩ := GlobalTheory.T.liftCuspFormSpace_thetaMap_eq_data D G Pl0 I0 T A3 Ks R F cG X0 Y Z hP hH
  rw [← LinearMap.range_eq_top, eq_top_iff, ← hTh.span i, Submodule.span_le]
  rintro _ ⟨k, rfl⟩
  obtain ⟨z, hz⟩ := hb.2 (Pi.single k 1)
  refine ⟨D.what₂.jMt (Y.tup t) ((i : ℕ) + 1) (Y.eMt i t (lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ z)), ?_⟩
  have hz' : lPrj D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ
      (lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ z) = z := by
    refine (Matrix.mulVec_mulVec _ _ _).trans ?_
    exact (congrArg (fun M => M *ᵥ z) hp.1).trans (Matrix.one_mulVec z)
  show _ = Z.jW i (Pi.single k 1)
  rw [hθ i t]
  exact congrArg (Z.jW i) ((congrArg (((A3.indefDown (s0Of R F)).θ i t).mulVec) hz').trans hz)

end GlobalTheory.Mem.LiftOnto

end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

noncomputable section

namespace GlobalTheory.Mem.R3.DivisionRationalLift

section Core

variable {K : Type} [Field K] [NumberField K] [StarRing K] {σ : K →+* ℂ} {M W : Type} [NormedAddCommGroup M]
  [InnerProductSpace ℂ M] [AddCommGroup W] [Module ℂ W]


omit [NumberField K] [StarRing K] in
theorem mulVec_map_injective {a b : ℕ} (Θ : Matrix (Fin a) (Fin b) K) (hΘ : Function.Injective Θ.mulVec) :
    Function.Injective (Θ.map σ).mulVec := by
  obtain ⟨g, hg⟩ := Θ.mulVecLin.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.2 hΘ)
  have hL : LinearMap.toMatrix' g * Θ = 1 := by
    have := congrArg LinearMap.toMatrix' hg
    rwa [LinearMap.toMatrix'_comp, ← Matrix.toLin'_apply', LinearMap.toMatrix'_toLin', LinearMap.toMatrix'_id] at this
  have hL' : (LinearMap.toMatrix' g).map σ * Θ.map σ = 1 := by
    rw [← Matrix.map_mul, hL, Matrix.map_one _ (map_zero σ) (map_one σ)]
  intro x y hxy
  have := congrArg (fun v => (LinearMap.toMatrix' g).map σ *ᵥ v) hxy
  simp only [Matrix.mulVec_mulVec, hL', Matrix.one_mulVec] at this
  exact this

theorem orth_ker_inf_range {n d e : ℕ} (J : (Fin n → K) →ₛₗ[σ] M)
    (hsp : Submodule.span ℂ (Set.range fun k => J (Pi.single k 1)) = ⊤)
    (H : Matrix (Fin n) (Fin n) K) (hin : ∀ x y, inner ℂ (J x) (J y) = σ (Formalism.DivisionValues.hform H x y))
    (eM : M →ₗ[ℂ] M) (E : Matrix (Fin n) (Fin n) K) (hop : ∀ x, eM (J x) = J (E *ᵥ x))
    (Zm : Matrix (Fin n) (Fin d) K) (Pr : Matrix (Fin d) (Fin n) K) (hP : Formalism.DivisionValues.IsOrthProj H Zm Pr)
    (hEZ : ∀ z, E *ᵥ (Zm *ᵥ z) = Zm *ᵥ z)
    (jW : (Fin e → K) →ₛₗ[σ] W) (hW : LinearIndependent ℂ fun k => jW (Pi.single k 1))
    (Θ : Matrix (Fin e) (Fin d) K) (hΘ : Function.Injective Θ.mulVec)
    (θ' : M →ₗ[ℂ] W) (hθ : ∀ x, θ' (J x) = jW (Θ *ᵥ (Pr *ᵥ x))) :
    (LinearMap.ker θ')ᗮ ⊓ LinearMap.range eM = Submodule.span ℂ (Set.range fun k => J (Zm *ᵥ Pi.single k 1)) := by

  classical
  set S := Submodule.span ℂ (J '' Set.range fun z => Zm *ᵥ z) with hS
  set N := Submodule.span ℂ (J '' {y | Pr *ᵥ y = 0}) with hN
  have hSN : ∀ a ∈ S, ∀ b ∈ N, inner ℂ a b = 0 := by
    have hle : N ≤ Sᗮ := by
      rw [hN, Submodule.span_le]
      rintro _ ⟨y, hy, rfl⟩
      rw [SetLike.mem_coe, Submodule.mem_orthogonal]
      intro u hu
      have hle2 : S ≤ (Submodule.span ℂ {J y})ᗮ := by
        rw [hS, Submodule.span_le]
        rintro _ ⟨_, ⟨z, rfl⟩, rfl⟩
        rw [SetLike.mem_coe, Submodule.mem_orthogonal_singleton_iff_inner_left, hin]
        have h0 := GlobalTheory.Mem.LiftForms.hform_orth hP z y
        rw [show Pr *ᵥ y = 0 from hy, Matrix.mulVec_zero, map_zero] at h0
        rw [← h0, map_zero]
      exact Submodule.mem_orthogonal_singleton_iff_inner_left.1 (hle2 hu)
    intro a ha b hb
    exact (Submodule.mem_orthogonal _ _).1 (hle hb) a ha
  have hker : ∀ x, Pr *ᵥ (x - Zm *ᵥ (Pr *ᵥ x)) = 0 := by
    intro x
    rw [Matrix.mulVec_sub, Matrix.mulVec_mulVec, hP.1, Matrix.one_mulVec, sub_self]
  have htop : ∀ v : M, ∃ a ∈ S, ∃ b ∈ N, a + b = v := by
    intro v
    have hv : v ∈ S ⊔ N := by
      have : (⊤ : Submodule ℂ M) ≤ S ⊔ N := by
        rw [← hsp, Submodule.span_le]
        rintro _ ⟨k, rfl⟩
        have hd : J (Pi.single k 1) = J (Zm *ᵥ (Pr *ᵥ Pi.single k 1)) + J (Pi.single k 1 - Zm *ᵥ (Pr *ᵥ Pi.single k 1)) := by
          rw [← map_add (f := _), add_sub_cancel]
        show J (Pi.single k 1) ∈ S ⊔ N
        rw [hd]
        exact Submodule.add_mem_sup (Submodule.subset_span ⟨_, ⟨_, rfl⟩, rfl⟩) (Submodule.subset_span ⟨_, hker _, rfl⟩)
      exact this Submodule.mem_top
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 hv
    exact ⟨a, ha, b, hb, hab⟩
  have hNk : N ≤ LinearMap.ker θ' := by
    rw [hN, Submodule.span_le]
    rintro _ ⟨y, hy, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker, hθ, show Pr *ᵥ y = 0 from hy, Matrix.mulVec_zero, map_zero]
  have hexp : ∀ y : Fin e → K, jW y = ∑ l, σ (y l) • jW (Pi.single l 1) := by
    intro y
    have hz : y = ∑ l, y l • (Pi.single l 1 : Fin e → K) := by
      ext i; simp [Pi.single_apply]
    conv_lhs => rw [hz]

    simp only [map_sum, map_smulₛₗ]
  have hSk : ∀ a ∈ S, θ' a = 0 → a = 0 := by
    intro a ha h0
    rw [hS, GlobalTheory.Mem.LiftForms.span_range_mulVec, ← Fintype.range_linearCombination] at ha
    obtain ⟨c, rfl⟩ := ha
    have hcomp : θ' (Fintype.linearCombination ℂ (fun k => J (Zm *ᵥ Pi.single k 1)) c) =
        ∑ l, ((Θ.map σ) *ᵥ c) l • jW (Pi.single l 1) := by

      simp only [Fintype.linearCombination_apply, map_sum, map_smul, hθ, Matrix.mulVec_mulVec, hP.1, Matrix.one_mulVec]
      simp only [hexp (Θ *ᵥ _), Finset.smul_sum, smul_smul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [← Finset.sum_smul]
      congr 1
      simp [Matrix.mulVec, dotProduct, Pi.single_apply, mul_comm]
    rw [hcomp] at h0
    have hc0 : (Θ.map σ) *ᵥ c = 0 := funext fun l => Fintype.linearIndependent_iff.1 hW _ h0 l
    have hc : c = 0 := mulVec_map_injective Θ hΘ (hc0.trans (Matrix.mulVec_zero _).symm)
    rw [hc, map_zero]
  have hSZ : S ≤ LinearMap.range eM := by
    rw [hS, Submodule.span_le]
    rintro _ ⟨_, ⟨z, rfl⟩, rfl⟩
    exact ⟨J (Zm *ᵥ z), by rw [hop, hEZ]⟩
  have hmain : (LinearMap.ker θ')ᗮ = S := by
    apply le_antisymm
    · intro v hv
      obtain ⟨a, ha, b, hb, rfl⟩ := htop v
      have h1 : inner ℂ b (a + b) = 0 := (Submodule.mem_orthogonal _ _).1 hv b (hNk hb)
      have h2 : inner ℂ b a = 0 := by rw [← inner_conj_symm, hSN a ha b hb, map_zero]
      rw [inner_add_right, h2, zero_add, inner_self_eq_zero] at h1
      rw [h1, add_zero]
      exact ha
    · intro s hs
      rw [Submodule.mem_orthogonal]
      intro w hw
      obtain ⟨a, ha, b, hb, rfl⟩ := htop w
      have hθa : θ' a = 0 := by
        have h3 := LinearMap.mem_ker.1 hw
        rwa [map_add, LinearMap.mem_ker.1 (hNk hb), add_zero] at h3
      rw [hSk a ha hθa, zero_add, ← inner_conj_symm, hSN s hs b hb, map_zero]
  rw [hmain, inf_eq_left.2 hSZ, hS, GlobalTheory.Mem.LiftForms.span_range_mulVec]

end Core

section Main

theorem divisionRows_rationalLift : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y), Pins R F cG → Holds R F → ∀ (i : Fin D.R.m) (t : T), Formalism.BasicNotions.Idx.Z0 D (Y.tup t) ((i : ℕ) + 1) = Submodule.span ℂ (Set.range fun k => (D.what₂.jMt (Y.tup t) ((i : ℕ) + 1)) (Y.eMt i t ((lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t).mulVec (Pi.single k 1)))) := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y Z hP hH i t
  have hR := complex_data_conditions_base_level_of_primitive_links hH.ok hH.sep hP.char hH.prim
  have hb : Function.Bijective ((A3.indefDown (s0Of R F)).θ i t).mulVec :=
    CxData.liftMat_bij (R.toCx3 F) F.cr false hR.kForm hR.ewNorm (hR.h4pos.2.2 false) hR.lifts0.1 hR.ratTh i t
  have hB : BlockHyp (A3.A.fam.L i t) (A3.A.fam.lvlA F.P0 F.ψ0) A3.A.v0 1 :=
    ⟨hH.ok.ok2.conj, hH.ok.ok2.irr, hH.ok.ok2.lifts i t⟩
  have hp : Formalism.DivisionValues.IsOrthProj (lH D A3.A F.P0 F.ψ0 i t) (lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t)
      (lPrj D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t) := BlockDat.lf_l_proj hB
  have he : ∀ z, lE D A3.A F.P0 F.ψ0 i t *ᵥ (lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ z) =
      lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ z := fun z => GlobalTheory.Mem.LiftForms.lvlOp_lE hB z
  obtain ⟨hTh, hθ⟩ := GlobalTheory.T.liftCuspFormSpace_thetaMap_eq_data D G Pl0 I0 T A3 Ks R F cG X0 Y Z hP hH
  have hf := Y.formsL i t
  exact orth_ker_inf_range ((D.what₂.jMt (Y.tup t) ((i : ℕ) + 1)).comp (Y.eMt i t).toLinearMap) hf.span
    (lH D A3.A F.P0 F.ψ0 i t) hf.inner (D.what₂.eMt (Y.tup t) ((i : ℕ) + 1)) (lE D A3.A F.P0 F.ψ0 i t) hf.op_eq
    _ _ hp he (Z.jW i) (hTh.li i) _ hb.1 (D.what₂.thetaP (Y.tup t) ((i : ℕ) + 1)) (hθ i t)

end Main

end GlobalTheory.Mem.R3.DivisionRationalLift

end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3
open Classical
open GlobalTheory.Mem.R3.HasLabelling

noncomputable section

namespace GlobalTheory.Mem.KerSpan

variable {K : Type} [Field K] {σ : K →+* ℂ}

theorem semi_expand {W : Type} [AddCommGroup W] [Module ℂ W] {m : ℕ} (f : (Fin m → K) →ₛₗ[σ] W) (v : Fin m → K) :
    f v = ∑ l, σ (v l) • f (Pi.single l 1) := by
  conv_lhs => rw [← Finset.univ_sum_single v]

  rw [map_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [← map_smulₛₗ]
  congr 1
  ext k
  by_cases h : k = l
  · subst h; simp
  · simp [h]

theorem left_inv_of_inj {m d : ℕ} (Θ : Matrix (Fin m) (Fin d) K) (hΘ : ∀ a, Θ *ᵥ a = 0 → a = 0) :
    ∃ L : Matrix (Fin d) (Fin m) K, L * Θ = 1 := by
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (Matrix.mulVecLin Θ)
    (LinearMap.ker_eq_bot'.2 fun a ha => hΘ a ha)
  refine ⟨LinearMap.toMatrix' g, ?_⟩
  have h := congrArg LinearMap.toMatrix' hg
  rwa [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_id, ← Matrix.toLin'_apply', LinearMap.toMatrix'_toLin'] at h

theorem map_mulVec_inj {m d : ℕ} (Θ : Matrix (Fin m) (Fin d) K) (hΘ : ∀ a, Θ *ᵥ a = 0 → a = 0)
    (c : Fin d → ℂ) (hc : (Θ.map σ) *ᵥ c = 0) : c = 0 := by
  obtain ⟨L, hL⟩ := left_inv_of_inj Θ hΘ
  have h1 : (L.map σ) * (Θ.map σ) = 1 := by
    rw [← Matrix.map_mul, hL, Matrix.map_one _ (map_zero σ) (map_one σ)]
  calc c = ((L.map σ) * (Θ.map σ)) *ᵥ c := by rw [h1, Matrix.one_mulVec]
    _ = 0 := by rw [← Matrix.mulVec_mulVec, hc, Matrix.mulVec_zero]

theorem orth_ker_eq_span [NumberField K] [StarRing K] {V W : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [AddCommGroup W] [Module ℂ W]
    {n d m : ℕ} (j : (Fin n → K) →ₛₗ[σ] V) (H : Matrix (Fin n) (Fin n) K)
    (hinner : ∀ x y, inner ℂ (j x) (j y) = σ (Formalism.DivisionValues.hform H x y))
    (hspan : Submodule.span ℂ (Set.range fun k => j (Pi.single k 1)) = ⊤)
    (Z : Matrix (Fin n) (Fin d) K) (Pr : Matrix (Fin d) (Fin n) K) (hp : Formalism.DivisionValues.IsOrthProj H Z Pr)
    (θ : V →ₗ[ℂ] W) (jW : (Fin m → K) →ₛₗ[σ] W) (hli : LinearIndependent ℂ fun k => jW (Pi.single k 1))
    (Θ : Matrix (Fin m) (Fin d) K) (hΘ : ∀ a, Θ *ᵥ a = 0 → a = 0)
    (hθ : ∀ x, θ (j x) = jW (Θ *ᵥ (Pr *ᵥ x))) :
    (LinearMap.ker θ)ᗮ = Submodule.span ℂ (Set.range fun a => j (Z *ᵥ a)) := by
  set U := Submodule.span ℂ (Set.range fun a => j (Z *ᵥ a)) with hU
  set r : (Fin n → K) → V := fun x => j (x - Z *ᵥ (Pr *ᵥ x)) with hr
  set R := Submodule.span ℂ (Set.range r) with hR
  have hPZ : ∀ a, Pr *ᵥ (Z *ᵥ a) = a := fun a => by rw [Matrix.mulVec_mulVec, hp.1, Matrix.one_mulVec]
  have hθr : ∀ x, θ (r x) = 0 := fun x => by
    simp only [hr]
    rw [hθ, Matrix.mulVec_sub, hPZ, sub_self, Matrix.mulVec_zero, map_zero]
  have horth : ∀ a x, inner ℂ (j (Z *ᵥ a)) (r x) = 0 := fun a x => by
    simp only [hr]
    rw [hinner, map_sub, GlobalTheory.Mem.LiftForms.hform_orth hp, sub_self, map_zero]
  have hRk : R ≤ LinearMap.ker θ := Submodule.span_le.2 (by rintro _ ⟨x, rfl⟩; exact hθr x)
  have hUR : U ≤ Rᗮ := by
    have h : U ⟂ R := Submodule.isOrtho_span.2 (by rintro _ ⟨a, rfl⟩ _ ⟨x, rfl⟩; exact horth a x)
    exact h
  have htop : ∀ y : V, ∃ a ∈ U, ∃ b ∈ R, y = a + b := by
    intro y
    have hle : (⊤ : Submodule ℂ V) ≤ U ⊔ R := by
      rw [← hspan, Submodule.span_le]
      rintro _ ⟨k, rfl⟩
      have e : j (Pi.single k 1) = j (Z *ᵥ (Pr *ᵥ Pi.single k 1)) + r (Pi.single k 1) := by
        simp only [hr]; rw [map_sub, add_sub_cancel]
      rw [SetLike.mem_coe]
      dsimp only
      rw [e]
      exact Submodule.add_mem_sup (Submodule.subset_span ⟨_, rfl⟩) (Submodule.subset_span ⟨_, rfl⟩)
    obtain ⟨a, ha, b, hb, e⟩ := Submodule.mem_sup.1 (hle Submodule.mem_top)
    exact ⟨a, ha, b, hb, e.symm⟩
  have hinj : ∀ y ∈ U, θ y = 0 → y = 0 := by
    intro y hy h0
    have hsub : U ≤ Submodule.span ℂ (Set.range fun k => j (Z *ᵥ Pi.single k 1)) := by
      rw [Submodule.span_le]
      rintro _ ⟨a, rfl⟩
      rw [SetLike.mem_coe]
      dsimp only
      rw [show j (Z *ᵥ a) = (j.comp (Matrix.mulVecLin Z)) a from rfl, semi_expand]
      exact Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨l, rfl⟩)
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 (hsub hy)
    have hc : (Θ.map σ) *ᵥ c = 0 := by

      rw [map_sum] at h0
      simp only [map_smul, hθ, hPZ] at h0
      have e : ∀ k, jW (Θ *ᵥ Pi.single k 1) = ∑ l, σ (Θ l k) • jW (Pi.single l 1) := fun k => by
        rw [semi_expand jW]
        simp
      have h1 : ∑ k, c k • jW (Θ *ᵥ Pi.single k 1) = ∑ l, ((Θ.map σ) *ᵥ c) l • jW (Pi.single l 1) := by
        simp only [e, Finset.smul_sum, smul_smul]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [← Finset.sum_smul]
        congr 1
        simp only [Matrix.mulVec, dotProduct, Matrix.map_apply]
        exact Finset.sum_congr rfl fun k _ => mul_comm _ _
      rw [h1] at h0
      exact funext (Fintype.linearIndependent_iff.1 hli _ h0)
    have hc0 := map_mulVec_inj Θ hΘ c hc
    subst hc0
    simp
  have hker : LinearMap.ker θ = R := by
    refine le_antisymm (fun y hy => ?_) hRk
    obtain ⟨a, ha, b, hb, rfl⟩ := htop y
    have hb0 : θ b = 0 := hRk hb
    have ha0 : θ a = 0 := by
      rw [LinearMap.mem_ker, map_add (f := _), hb0, add_zero] at hy; exact hy
    rw [hinj a ha ha0, zero_add]; exact hb
  rw [hker]
  refine le_antisymm (fun y hy => ?_) hUR
  obtain ⟨a, ha, b, hb, rfl⟩ := htop y
  have hb' : b ∈ Rᗮ := by
    have h := Rᗮ.sub_mem hy (hUR ha); rwa [add_sub_cancel_left] at h
  have hb0 : b = 0 := by
    have h : b ∈ R ⊓ Rᗮ := Submodule.mem_inf.2 ⟨hb, hb'⟩
    rw [Submodule.inf_orthogonal_eq_bot] at h
    exact (Submodule.mem_bot ℂ).1 h
  rw [hb0, add_zero]; exact ha



theorem orth_ker_thetaP : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y), Pins R F cG → Holds R F → ∀ (i : Fin D.R.m) (t : T), (LinearMap.ker (D.what₂.thetaP (Y.tup t) ((i : ℕ) + 1)))ᗮ = Submodule.span ℂ (Set.range fun a => D.what₂.jMt (Y.tup t) ((i : ℕ) + 1) (Y.eMt i t (lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ a))) := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y Z hP hH i t
  have hR : ComplexDataConditionsBaseLevel A3 F.P0 F.ψ0 F.P1 F.ψ1 F.Dc F.Sp F.Zsc (R.toCx3 F) 1 (U2.eigensystemChoice A3 (R.toCx3 F) F.P0 F.ψ0 F.P1 F.ψ1 hH.prim.hecke.2.choose) hH.prim.hecke.1.choose hH.prim.hecke.2.choose (R.gEx F) (R.gWx F) := by
    have hUnitary := U2.unitary_two_package A3 (R.toCx3 F) 1 F.P0 F.ψ0 F.P1 F.ψ1 F.Dc F.Sp F.Zsc hH.prim.hecke.2.choose (R.gWx F) hH.ok
      (RealDat3.kFormR_of hP.char.base.models) (RealDat3.kFormL_of hP.char.base.models) (RealDat3.jIsoR_of hP.char.base.models)
      (RealDat3.jIsoL_of hP.char.base.models) hH.prim.rowTest hH.prim.liftTest hH.prim.heckeL hH.prim.hecke.2.choose_spec hH.prim.gUnit.2 hH.prim.gEquiv.2 hH.prim.levW
      hH.prim.sumW (hH.prim.liftOnto _ hH.prim.hecke.2.choose_spec)
    exact {
      kFormR := RealDat3.kFormR_of hP.char.base.models
      kFormL := RealDat3.kFormL_of hP.char.base.models
      jIsoR := RealDat3.jIsoR_of hP.char.base.models
      jIsoL := RealDat3.jIsoL_of hP.char.base.models
      npTie := ⟨rfl, rfl⟩
      ok := hH.ok
      sep := hH.sep
      heckeR := hH.prim.heckeR
      heckeL := hH.prim.heckeL
      thetaR := hH.prim.hecke.1.choose_spec
      thetaL := hH.prim.hecke.2.choose_spec
      gUnit := hH.prim.gUnit.1
      gEquiv := hH.prim.gEquiv.1
      lev0 := hH.prim.levE.1
      lev1 := hH.prim.levE.2
      h2P := hH.prim.h2P
      gUnitL := hH.prim.gUnit.2
      gEquivL := hH.prim.gEquiv.2
      lower_level_lift_type := hH.prim.levW
      inBlock := hH.prim.block
      rowTest := hH.prim.rowTest
      liftTest := hH.prim.liftTest
      pos := hH.prim.pos
      h0 := RealDat3.height_change_of_D0 hP.char.tup
      h4pos := ⟨fun _ => hH.prim.posScal.1, hH.prim.posScal.2, RealDat.nP_pos⟩
      thmBop := RealDat3.thmBop_of hH.prim.thmB
      partsE := hH.prim.sumE
      kForm := RealDat3.kForm_of hH.prim.unif false
      mLat := hH.prim.mLat
      ewNorm := RealDat3.ewNorm false
      thmAop := RealDat3.thmAop_of hP.char.phase hH.prim.thmA false
      partsW := hH.prim.sumW
      base_lift_test := hH.prim.liftTestB
      galD := hH.prim.scalConj
      dimParts := hH.prim.dimParts
      eig0 := hUnitary.1
      typ0 := hUnitary.2
    }
  have hOk := hH.ok.ok2
  have hT := GlobalTheory.T.liftCuspFormSpace_thetaMap_eq_data D G Pl0 I0 T A3 Ks R F cG X0 Y Z hP hH
  have hp : Formalism.DivisionValues.IsOrthProj (lH D A3.A F.P0 F.ψ0 i t) (lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t)
      (lPrj D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t) := BlockDat.lf_l_proj ⟨hOk.conj, hOk.irr, hOk.lifts i t⟩
  have hΘ : ∀ a, ((A3.indefDown (s0Of R F)).θ i t) *ᵥ a = 0 → a = 0 := by
    intro a ha
    have h2 := GlobalTheory.Mem.LiftTheta.liftMatrix_computes_lift_rational (R.toCx3 F) F.cr false hR.lifts0.1 hR.ratTh i t a
    have h6 := CxData.tC_cpt_eq (R.toCx3 F) F.cr false i t a
    have ha' : (R.toCx3 F).liftMat F.cr false i t *ᵥ a = 0 := ha
    have h7 : (R.toCx3 F).tC F.cr false i t (cpt A3.fam3.base3.v0.embedding a) = (R.toCx3 F).tC F.cr false i t (cpt A3.fam3.base3.v0.embedding 0) := by
      rw [h6, ← h2, ha']
      have hz : ∀ {k : ℕ}, cpt A3.fam3.base3.v0.embedding (0 : Fin k → D.what₂.LL) = 0 := fun {k} => by
        funext l; simp [cpt]
      simp only [hz, map_zero]
    exact cpt_injective _ ((hR.lifts0.1 i t).1 h7)
  exact GlobalTheory.Mem.KerSpan.orth_ker_eq_span _ _ (Y.formsL i t).inner (Y.formsL i t).span _ _ hp
    (D.what₂.thetaP (Y.tup t) ((i : ℕ) + 1)) (Z.jW i) (hT.1.li i) _ hΘ (fun x => hT.2 i t x)

end GlobalTheory.Mem.KerSpan
end
end

end

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3
open Classical
open GlobalTheory.Mem.R3.HasLabelling

theorem _root_.GlobalTheory.T.liftThetaMap_surjective_onto_cuspForms_usedTuple : GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y), Pins R F cG → Holds R F → HostHyp D → ∀ (i : Fin D.R.m) (t : T), Used0 D (Y.tup t) → Function.Surjective (D.what₂.thetaP (Y.tup t) ((i : ℕ) + 1)) := by
  first | exact @GlobalTheory.Mem.LiftOnto.thetaMap_surjective | exact GlobalTheory.Mem.LiftOnto.thetaMap_surjective | (intros; apply GlobalTheory.Mem.LiftOnto.thetaMap_surjective <;> assumption)

end
end

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

theorem _root_.GlobalTheory.T.zeroSubspace_spanned_by_dataZeroSubspace_lifts : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y), Pins R F cG → Holds R F → ∀ (i : Fin D.R.m) (t : T), Formalism.BasicNotions.Idx.Z0 D (Y.tup t) ((i : ℕ) + 1) = Submodule.span ℂ (Set.range fun k => (D.what₂.jMt (Y.tup t) ((i : ℕ) + 1)) (Y.eMt i t ((lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t).mulVec (Pi.single k 1)))) := by
  first | exact @GlobalTheory.Mem.R3.DivisionRationalLift.divisionRows_rationalLift | exact GlobalTheory.Mem.R3.DivisionRationalLift.divisionRows_rationalLift | (intros; apply GlobalTheory.Mem.R3.DivisionRationalLift.divisionRows_rationalLift <;> assumption)

end
end

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3
open Classical
open GlobalTheory.Mem.R3.HasLabelling

theorem _root_.GlobalTheory.T.liftThetaMap_orthogonalKernel_eq_rationalSpan : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y), Pins R F cG → Holds R F → ∀ (i : Fin D.R.m) (t : T), (LinearMap.ker (D.what₂.thetaP (Y.tup t) ((i : ℕ) + 1)))ᗮ = Submodule.span ℂ (Set.range fun a => D.what₂.jMt (Y.tup t) ((i : ℕ) + 1) (Y.eMt i t (lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ a))) := by
  first | exact @GlobalTheory.Mem.KerSpan.orth_ker_thetaP | exact GlobalTheory.Mem.KerSpan.orth_ker_thetaP | (intros; apply GlobalTheory.Mem.KerSpan.orth_ker_thetaP <;> assumption)

end
end
