module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle006
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalBlockDetBlockTriangular
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle023
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle129
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle073
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.StrongApproximationUnitaryUnipotentRadical
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.ConcreteLevelAdelicSubset
import Development.AbelianVarietyTheory.Definitions.Foundations.MeasurePreservingRmulQuotMeas
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.LevelSubgroupProperties
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.IUnfold
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.Bundle001
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPtOfOfDecoRaw
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
public import Formalism.LocalToGlobal.Columns.Bundle010
public import Formalism.LocalToGlobal.Columns.RecLevelDiv
import Formalism.LocalToGlobal.Columns.RecLevelLoc
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle134
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
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
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle004
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle012
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MidChart
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Formalism.LocalToGlobal.Columns.CoefficientsModP.WeTransposeWordTransposeWord
import Formalism.LocalToGlobal.IndefiniteReal.Bundle017
import Formalism.LocalToGlobal.IndefiniteReal.Bundle001
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowDict
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowsJoinPinned
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.HidaSetting
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.PoincareInHH

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open ValuativeRel

namespace GlobalTheory.SymRes

theorem exists_red_iff_isPat {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {O : Type} [CommRing O] (I : Ideal O) (π : O →+* k) (h : GlobalTheory.FunObj.Comparison₂.IsRed (Ideal.Quotient.mk I) π)
    {s κ r : ℕ} (hr : r = κ + (s + 1)) (S : GlobalTheory.SymChain.SymData k s κ) (g : GL (Fin r) (O ⧸ I)) :
    (∃ x : S.P.J, ∀ (a b : Fin κ ⊕ Fin (s + 1)) (a' b' : Fin r), a'.val = GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.framePos _ _ a →
      b'.val = GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.framePos _ _ b → ∀ z : O, Ideal.Quotient.mk I z = g.val a' b' →
      valuation k ((x : GL (Fin κ ⊕ Fin (s + 1)) k).val a b - π z) < 1) ↔ IsPat S.ρ κ g := by
  subst hr
  let e : Fin κ ⊕ Fin (s + 1) ≃ Fin (κ + (s + 1)) := finSumFinEquiv
  have he : ∀ a, (e a).val = GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.framePos _ _ a := by
    rintro (a | a) <;> simp [e, GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.framePos]
  have hfree : ∀ a b, FreePos S.ρ κ (e a).val (e b).val ↔ GlobalTheory.SymChain.FreeTop S.ρ a b := by
    intro a b
    rw [he, he]
    rcases a with a | a <;> rcases b with b | b <;>
      simp only [GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.framePos, Sum.elim_inl, Sum.elim_inr, GlobalTheory.SymChain.FreeTop, FreePos, Fin.lt_def] <;>
      have := a.2 <;> have := b.2 <;> omega
  choose l hl using fun a b => Ideal.Quotient.mk_surjective (I := I) (g.val (e a) (e b))
  have key : ∀ a b, g.val (e a) (e b) = (1 : Matrix _ _ (O ⧸ I)) (e a) (e b) ↔
      valuation k (π (l a b) - (1 : Matrix _ _ k) a b) < 1 := by
    intro a b
    have h4 := h.ker (l a b - if a = b then 1 else 0)
    rw [map_sub, map_sub, sub_eq_zero, apply_ite (Ideal.Quotient.mk I), apply_ite π, map_one, map_one, map_zero,
      map_zero, hl] at h4
    rw [Matrix.one_apply, Matrix.one_apply]
    simp only [e.apply_eq_iff_eq]
    convert h4
  constructor
  · rintro ⟨x, hx⟩ i j hij
    obtain ⟨a, rfl⟩ := e.surjective i
    obtain ⟨b, rfl⟩ := e.surjective j
    have h1 := hx a b _ _ (he a) (he b) _ (hl a b)
    have h2 := ((GlobalTheory.SymChain.SymData.mem_J_iff_pattern k s κ S x.1).1 x.2).2 a b (fun h' => hij ((hfree a b).2 h'))
    have h3 := (valuation k).map_sub_lt h2 h1
    rw [sub_sub_sub_cancel_left] at h3
    exact (key a b).2 h3
  · intro hg
    have hM : (Matrix.of l).map (Ideal.Quotient.mk I) = g.val.submatrix e e := Matrix.ext hl
    have hu : IsUnit ((Matrix.of l).map (Ideal.Quotient.mk I)).det := by
      rw [hM, det_submatrix_equiv_self]
      convert (Matrix.isUnit_iff_isUnit_det _).1 g.isUnit
    obtain ⟨x, hx1, hx2⟩ := (h.isUnit_det_iff _).1 hu
    have hx3 : ∀ a b, x.val a b = π (l a b) := fun a b => congrFun (congrFun hx2 a) b
    refine ⟨⟨x, (GlobalTheory.SymChain.SymData.mem_J_iff_pattern k s κ S x).2 ⟨by convert hx1, fun a b hab => ?_⟩⟩, ?_⟩
    · rw [hx3]
      exact (key a b).1 (hg _ _ fun h' => hab ((hfree a b).1 h'))
    · intro a b a' b' ha hb z hz
      obtain rfl : a' = e a := Fin.ext (ha.trans (he a).symm)
      obtain rfl : b' = e b := Fin.ext (hb.trans (he b).symm)
      change valuation k (x.val a b - π z) < 1
      rw [hx3, ← map_sub, ← h.ker, map_sub, hl, hz, sub_self]

end GlobalTheory.SymRes
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

namespace GlobalTheory.HeckeSplitAll

theorem char_trivial_modSet : ∀ (D : D7) (ν : (AE D)ˣ →* Circle), Continuous ν →
    ∃ N : ℕ, 0 < N ∧ ∀ x ∈ GlobalTheory.HeckeSplitAll.modSet D N, ν x = 1 := by
  intro D ν hν
  obtain ⟨N, hN, hker, -⟩ := GlobalTheory.CharFin.char_finUnit_finite_order D ν hν
  refine ⟨N, hN, fun x hx => ?_⟩
  obtain ⟨h1, ⟨r, hr, hxr⟩, h3⟩ := hx
  have hNr : (N : Af D.host.F ⊗[D.host.F] D.host.E) * r = N • r := (nsmul_eq_mul _ _).symm
  have hfin : finPart D (x : AE D) ∈ intAE D := by
    have : finPart D (x : AE D) = 1 + N • r := by rw [← hNr, ← hxr]; ring
    rw [this]
    exact add_mem (AddSubgroup.subset_closure ⟨1, fun w => by rw [map_one]; exact one_mem _, 1, by simp [Algebra.TensorProduct.one_def]⟩) (nsmul_mem hr N)
  exact hker x ⟨h1, hfin, h3⟩ ⟨r, hr, by rw [hxr, hNr]⟩

end GlobalTheory.HeckeSplitAll
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.SfinHaar

open Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH Topology

theorem exists_idem_of_subspace {E : Type} [Field E] {n : ℕ} (W : Submodule E (Fin n → E)) :
    ∃ e : Matrix (Fin n) (Fin n) E, e * e = e ∧ ∀ x, x ∈ W ↔ e *ᵥ x = x := by
  obtain ⟨W', hc⟩ := W.exists_isCompl
  obtain ⟨p, hp⟩ : ∃ p : Matrix (Fin n) (Fin n) E, ∀ x, p *ᵥ x = Submodule.projection W W' hc x :=
    ⟨LinearMap.toMatrix' _, fun x => LinearMap.toMatrix'_mulVec _ x⟩
  have h1 : ∀ x, p *ᵥ x ∈ W := fun x => hp x ▸ Submodule.projection_apply_mem hc x
  have h2 : ∀ x ∈ W, p *ᵥ x = x := fun x hx => (hp x).trans (Submodule.projection_apply_of_mem_left hc hx)
  refine ⟨p, Matrix.ext_iff_mulVec.2 fun y => by rw [← Matrix.mulVec_mulVec, h2 _ (h1 y)], fun x =>
    ⟨fun hx => h2 x hx, fun hx => hx ▸ h1 x⟩⟩

theorem span_incl_eq (I : AutInst) (T : Set (Fin I.n → I.E)) :
    Submodule.span (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) (incl I '' T) =
      Submodule.span (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)
        ((fun w i => GlobalTheory.UnipApprox.inc I (w i)) '' (Submodule.span I.E T : Set (Fin I.n → I.E))) := by
  apply le_antisymm
  · exact Submodule.span_mono (Set.image_mono Submodule.subset_span)
  · rw [Submodule.span_le]
    rintro _ ⟨w, hw, rfl⟩
    induction hw using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
    | zero =>
      have : (fun i => GlobalTheory.UnipApprox.inc I ((0 : Fin I.n → I.E) i)) = 0 := by ext; simp
      beta_reduce; rw [this]; exact zero_mem _
    | add x y _ _ hx hy =>
      have : (fun i => GlobalTheory.UnipApprox.inc I ((x + y) i)) =
          (fun i => GlobalTheory.UnipApprox.inc I (x i)) + fun i => GlobalTheory.UnipApprox.inc I (y i) := by ext; simp
      rw [SetLike.mem_coe] at hx hy; beta_reduce at hx hy ⊢; rw [this]; exact add_mem hx hy
    | smul a x _ hx =>
      have : (fun i => GlobalTheory.UnipApprox.inc I ((a • x) i)) =
          GlobalTheory.UnipApprox.inc I a • fun i => GlobalTheory.UnipApprox.inc I (x i) := by ext; simp
      rw [SetLike.mem_coe] at hx; beta_reduce at hx ⊢; rw [this]; exact Submodule.smul_mem _ _ hx

theorem isClosed_cond (I : AutInst) (v : Fin I.n → I.E) (T : Set (Fin I.n → I.E)) :
    IsClosed {x : I.Gf | (I.fmat x - 1) *ᵥ incl I v ∈ Submodule.span (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) (incl I '' T)} := by
  obtain ⟨t, hr, h2, -, -, -, hind⟩ := GlobalTheory.UnipApprox.exists_top I
  obtain ⟨e, he, hW⟩ := exists_idem_of_subspace (Submodule.span I.E T)
  have hset : {x : I.Gf | (I.fmat x - 1) *ᵥ incl I v ∈ Submodule.span (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) (incl I '' T)} =
      {x | e.map (GlobalTheory.UnipApprox.inc I) *ᵥ ((I.fmat x - 1) *ᵥ incl I v) = (I.fmat x - 1) *ᵥ incl I v} := by
    ext x
    simp only [Set.mem_setOf_eq]
    rw [span_incl_eq]
    exact GlobalTheory.UnipApprox.mem_span_iff (GlobalTheory.UnipApprox.inc I) he _ hW _
  rw [hset]
  have hc : Continuous fun x : I.Gf => I.fmat x := Units.continuous_val.comp hind.continuous
  have hc2 : Continuous fun x : I.Gf => (I.fmat x - 1) *ᵥ incl I v :=
    (hc.sub continuous_const).matrix_mulVec continuous_const
  exact isClosed_eq (continuous_const.matrix_mulVec hc2) hc2

theorem isClosed_sfin (I : AutInst) {r : ℕ} (e : Fin r → Fin I.n → I.E) (z : Fin I.n → I.E) :
    IsClosed (Sfin I e z) := by
  have h1 : ∀ a : Fin r, IsClosed {x : I.Gf | (I.fmat x - 1) *ᵥ incl I (e a) ∈
      Submodule.span (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) ((fun b => incl I (e b)) '' {b | b.1 < a.1})} := by
    intro a
    have := isClosed_cond I (e a) (e '' {b : Fin r | b.1 < a.1})
    rwa [Set.image_image] at this
  have h2 : IsClosed {x : I.Gf | (I.fmat x - 1) *ᵥ incl I z ∈
      Submodule.span (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) (Set.range fun b => incl I (e b))} := by
    have := isClosed_cond I z (Set.range e)
    rwa [← Set.range_comp] at this
  unfold Sfin
  rw [Set.setOf_and, Set.setOf_forall]
  exact (isClosed_iInter h1).inter h2

end GlobalTheory.SfinHaar

namespace GlobalTheory.SfinHaar

open Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH Topology MeasureTheory

theorem disint_finPart : ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u : D.what₂.Word),
    ∃ μSf : Measure (Formalism.L2.SG.Pf.SfinSub X.B.I X.eR (X.zR u)), μSf.IsHaarMeasure ∧ SigmaFinite μSf ∧
      ∃ c : ℝ, 0 < c ∧ ∀ φ : X.B.I.Gf → ENNReal, Measurable φ →
        (∀ x, φ x ≠ 0 → ∃ s ∈ SfinU X u, ∃ k ∈ X.K2, x = s * X.xu u * k) →
        ∫⁻ x, φ x ∂X.B.μf = ENNReal.ofReal c * ∫⁻ t, ∫⁻ k in X.K2, φ (t.1 * X.xu u * k) ∂X.B.μf ∂μSf := by
  intro D X u
  set G := X.B.I.Gf
  set S := Formalism.L2.SG.Pf.SfinSub X.B.I X.eR (X.zR u) with hSdef
  set K := X.K2 with hKdef
  set x := X.xu u with hxdef
  haveI : SecondCountableTopology G := Formalism.L2.SG.Pf.gf_secondCountable X.B.I
  haveI : X.B.μf.IsHaarMeasure := X.B.haar
  have hKg := Formalism.L2.SG.Closed.level_subgroup_is_group X
  have hKt := Formalism.L2.SG.Pf.level_subgroup_compact_open X
  have hK1 : (1 : G) ∈ K := hKg.1
  have hKmul : ∀ a ∈ K, ∀ b ∈ K, a * b ∈ K := hKg.2.1
  have hKinv : ∀ a ∈ K, a⁻¹ ∈ K := hKg.2.2.1
  have hKo : IsOpen K := hKt.1
  have hKc : IsCompact K := hKt.2
  haveI : LocallyCompactSpace G := hKc.locallyCompactSpace_of_mem_nhds_of_group (hKo.mem_nhds hK1)
  have hSc : IsClosed (S : Set G) := isClosed_sfin X.B.I X.eR (X.zR u)

  set C : Set G := {g | x⁻¹ * g * x ∈ K} with hCdef
  have hCeq : C = (fun k => x * k * x⁻¹) '' K := by
    ext g
    constructor
    · intro hg; exact ⟨x⁻¹ * g * x, hg, by group⟩
    · rintro ⟨k, hk, rfl⟩
      show x⁻¹ * (x * k * x⁻¹) * x ∈ K
      simpa [mul_assoc] using hk
  have hCc : IsCompact C := hCeq ▸ hKc.image ((continuous_const_mul _).mul continuous_const)
  have hCo : IsOpen C := hKo.preimage ((continuous_const_mul _).mul continuous_const)
  set H : Set S := Subtype.val ⁻¹' C with hHdef
  have hHc : IsCompact H := hSc.isClosedEmbedding_subtypeVal.isCompact_preimage hCc
  have hHo : IsOpen H := hCo.preimage continuous_subtype_val
  have hH1 : (1 : S) ∈ H := by
    show x⁻¹ * ((1 : S) : G) * x ∈ K
    simpa using hK1
  haveI : LocallyCompactSpace S := hHc.locallyCompactSpace_of_mem_nhds_of_group (hHo.mem_nhds hH1)
  let K₀ : TopologicalSpace.PositiveCompacts S := ⟨⟨H, hHc⟩, ⟨1, hHo.subset_interior_iff.2 le_rfl hH1⟩⟩
  set ν : Measure S := Measure.haarMeasure K₀ with hνdef
  haveI : ν.IsHaarMeasure := Measure.isHaarMeasure_haarMeasure K₀
  have hνH : ν H = 1 := Measure.haarMeasure_self
  refine ⟨ν, inferInstance, inferInstance, 1, one_pos, fun φ hφ hsupp => ?_⟩
  rw [ENNReal.ofReal_one, one_mul]

  set Z : Set (S × G) := {p | x⁻¹ * ((p.1 : G)⁻¹ * p.2) ∈ K} with hZdef
  have hZo : IsOpen Z := hKo.preimage
    (continuous_const.mul ((continuous_subtype_val.comp continuous_fst).inv.mul continuous_snd))
  have hZm : MeasurableSet Z := hZo.measurableSet
  have hKm : MeasurableSet K := hKo.measurableSet
  let F : S → G → ENNReal := fun t g => φ g * Z.indicator 1 (t, g)
  have hF : Measurable (Function.uncurry F) :=
    (hφ.comp measurable_snd).mul (measurable_one.indicator hZm)

  have hA : ∀ t : S, ∫⁻ g, F t g ∂X.B.μf = ∫⁻ k in K, φ ((t : G) * x * k) ∂X.B.μf := by
    intro t
    rw [← lintegral_mul_left_eq_self _ ((t : G) * x), ← lintegral_indicator hKm]
    refine lintegral_congr fun k => ?_
    have e : x⁻¹ * ((t : G)⁻¹ * ((t : G) * x * k)) = k := by group
    by_cases hk : k ∈ K
    · have : ((t, (t : G) * x * k) : S × G) ∈ Z := by show x⁻¹ * ((t : G)⁻¹ * ((t : G) * x * k)) ∈ K; rw [e]; exact hk
      simp only [F]
      rw [Set.indicator_of_mem this, Set.indicator_of_mem hk, Pi.one_apply, mul_one]
    · have : ((t, (t : G) * x * k) : S × G) ∉ Z := by show ¬ x⁻¹ * ((t : G)⁻¹ * ((t : G) * x * k)) ∈ K; rw [e]; exact hk
      simp only [F]
      rw [Set.indicator_of_notMem this, Set.indicator_of_notMem hk, mul_zero]

  have hC' : ∀ g, ∫⁻ t, F t g ∂ν = φ g := by
    intro g
    by_cases h0 : φ g = 0
    · simp [F, h0]
    obtain ⟨s, hs, k, hk, rfl⟩ := hsupp g h0
    have hset : {t : S | (t, s * x * k) ∈ Z} = (fun t => (⟨s, hs⟩ : S)⁻¹ * t) ⁻¹' H := by
      ext t
      simp only [Set.mem_setOf_eq, Set.mem_preimage]
      show x⁻¹ * ((t : G)⁻¹ * (s * x * k)) ∈ K ↔ x⁻¹ * (s⁻¹ * (t : G)) * x ∈ K
      have e : x⁻¹ * ((t : G)⁻¹ * (s * x * k)) = (x⁻¹ * (s⁻¹ * (t : G)) * x)⁻¹ * k := by group
      rw [e]
      constructor
      · intro h
        have := hKinv _ (hKmul _ h _ (hKinv _ hk))
        simpa using this
      · intro h
        exact hKmul _ (hKinv _ h) _ hk
    have hmeas : MeasurableSet {t : S | (t, s * x * k) ∈ Z} :=
      hZm.preimage (measurable_id.prodMk measurable_const)
    calc ∫⁻ t, F t (s * x * k) ∂ν = ∫⁻ t, φ (s * x * k) * {t : S | (t, s * x * k) ∈ Z}.indicator 1 t ∂ν := by
          refine lintegral_congr fun t => ?_
          simp only [F]
          congr 1
      _ = φ (s * x * k) * ν {t : S | (t, s * x * k) ∈ Z} := by
          rw [lintegral_const_mul _ (measurable_one.indicator hmeas), lintegral_indicator_one hmeas]
      _ = φ (s * x * k) := by
          rw [hset, measure_preimage_mul, hνH, mul_one]
  calc ∫⁻ g, φ g ∂X.B.μf = ∫⁻ g, ∫⁻ t, F t g ∂ν ∂X.B.μf := lintegral_congr fun g => (hC' g).symm
    _ = ∫⁻ t, ∫⁻ g, F t g ∂X.B.μf ∂ν := (lintegral_lintegral_swap hF.aemeasurable).symm
    _ = ∫⁻ t, ∫⁻ k in K, φ ((t : G) * x * k) ∂X.B.μf ∂ν := lintegral_congr fun t => hA t

end GlobalTheory.SfinHaar
end
end

section

noncomputable section

namespace GlobalTheory.SeeSaw.TopLevel

section Gen

open NumberField IsDedekindDomain Formalism.BasicNotions _root_.Formalism.L2.Col Formalism.L2.DIV Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TypeLev Matrix
open scoped TensorProduct

variable {F E K : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] [Field K]

theorem lev_iff (hc : CMData F E) {n n' : ℕ} (e : n' = n) [NeZero n] {J' : Matrix (Fin n') (Fin n') E} {J : Matrix (Fin n) (Fin n) E}
    (hJ' : J' = 1) (hJ : J = 1) {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))} (S : StepLevel F E hc.sig J T f bad)
    (hL : S.Lb = Formalism.L2.Col.stdLat E n) {r t s : ℕ} (h : r ≤ n) (h' : r ≤ n') (ht : 0 < t) (hn : n = r + s * t) {SG : Finset (Pl E)}
    (P : LevFam E K r SG) (χ : ∀ w : SG, ℕ → (𝓞 E ⧸ w.1.asIdeal)ˣ →* Kˣ) (emb : K →+* ℂ)
    (hR : RdLev hc S.U S.chi Set.univ (parFam h t s P χ) emb) (P' : LevelP SG r ℂ)
    (cg : ℕ → ∀ PP : Pl E, (kP PP)ˣ →* ℂˣ) (xq : ∀ PP : Pl E, (kP PP)ˣ →* ℂˣ)
    (hH : ∀ g, g ∈ P'.H ↔ ∀ w, g w ∈ (P w).H)
    (hchi : ∀ (g : P'.H) (hg : ∀ w, g.1 w ∈ (P w).H), ((P'.chi g : ℂˣ) : ℂ) = ∏ w, emb (((P w).lam ⟨g.1 w, hg w⟩ : Kˣ) : K))
    (hcg : ∀ c (w : SG) a, ((cg (c + 1) w.1 a : ℂˣ) : ℂ) = emb ((χ w c a : Kˣ) : K))
    (g : GL (Fin n') (E ⊗[F] Formalism.L2.Herm.Af F)) (y : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))
    (hgy : ∀ i j, g.1 i j = y.1 (finCongr e i) (finCongr e j)) :
    (g ∈ lev hc J' 1 ⟨r, h', t, s, SG, ∅, P', cg, xq⟩ ↔ y ∈ S.U) ∧
      ∀ hy : y ∈ S.U, ((levFn 1 ⟨r, h', t, s, SG, ∅, P', cg, xq⟩ g : ℂˣ) : ℂ) = star ((S.chi ⟨y, hy⟩ : ℂˣ) : ℂ) := by
  classical
  subst e hJ' hJ
  obtain rfl : g = y := Units.ext (Matrix.ext hgy)
  have e0 : g ∈ lev hc 1 1 ⟨r, h', t, s, SG, ∅, P', cg, xq⟩ ↔ g ∈ lev hc 1 1 (parDat h t s P χ) := by
    rw [mem_lev, mem_lev, mem_parLev, mem_parLev]
    refine and_congr Iff.rfl ((hH _).trans ⟨fun h w _ => h w, fun h w => h w (Set.mem_univ w)⟩)
  have hred : ∀ (hz : g ∈ St (1 : GL (Fin n') (E ⊗[F] Formalism.L2.Herm.Af F))) (w : Pl E), redFn 1 w g = redAt 1 w ⟨g, hz⟩ :=
    fun hz w => extendOne_of_mem _ hz
  have hU : g ∈ S.U → g ∈ UAd hc n' ∧ g ∈ St (1 : GL (Fin n') (E ⊗[F] Formalism.L2.Herm.Af F)) := fun hy => by
    obtain ⟨h1, h2⟩ := (S.U_eq g).1 hy
    refine ⟨h1, rll_St_of_loc n' g fun v => ⟨_, rll_put_mem_St n' v ?_, rll_put_self n' v _⟩⟩
    have := (S.Uloc_lev v (h2 v)).2
    rw [hL] at this
    exact this
  have e1 : g ∈ levU hc n' ∅ SG (parFam h t s P χ).grp ↔ g ∈ S.U := by
    rw [mem_levU_iff]
    constructor
    · rintro ⟨h1, h2, -, h4⟩
      exact (hR g h2 h1 fun v hv => absurd (Set.mem_univ v) hv).1.2 fun w => hred h2 w.1 ▸ h4 w (Set.mem_univ w)
    · intro hy
      obtain ⟨h1, h2⟩ := hU hy
      refine ⟨h1, h2, fun P hP => absurd hP (Finset.notMem_empty P), fun w _ => ?_⟩
      have := (hR g h2 h1 fun v hv => absurd (Set.mem_univ v) hv).1.1 hy w
      rwa [← hred h2] at this
  refine ⟨by rw [e0, ← levU_parFam_eq_lev hc h ht hn, e1], fun hy => ?_⟩
  obtain ⟨h1, h2⟩ := hU hy
  have h3 := e1.2 hy
  have h4 : g ∈ lev hc 1 1 (parDat h t s P χ) := levU_parFam_eq_lev hc h ht hn P χ ▸ h3
  have h5 := e0.2 h4
  obtain ⟨r1, r2⟩ := hR g h2 h1 fun v hv => absurd (Set.mem_univ v) hv
  have a1 : ((levFn 1 ⟨r, h', t, s, SG, ∅, P', cg, xq⟩ g : ℂˣ) : ℂ) = emb ((levFn 1 (parDat h t s P χ) g : Kˣ) : K) := by
    unfold levFn
    rw [extendOne_of_mem _ h5.2, extendOne_of_mem _ h4.2]
    simp only [Units.val_mul, Units.coe_prod, map_mul, map_prod]
    congr 1
    congr 1
    · rw [hchi _ fun w => h4.2 w (Set.mem_univ w)]
      have := rld_ofLocal_chi (fun w => (P w).H) (fun w => (P w).lam) ⟨_, h4.2⟩
      refine Eq.trans ?_ (congrArg (fun x : Kˣ => emb (x : K)) this).symm
      simp only [Units.coe_prod, map_prod]
      rfl
    · show ∏ PP ∈ SG, _ = ∏ PP ∈ SG, _
      refine Finset.prod_congr rfl fun w hw => ?_
      show ∏ c ∈ Finset.range s, _ = ∏ c ∈ Finset.range s, _
      refine Finset.prod_congr rfl fun c _ => ?_
      rw [rld_parDat_cg h P χ c ⟨w, hw⟩]
      exact hcg c ⟨w, hw⟩ _
  have a2 := levChr_parFam_eq_levChar hc h ht hn P χ g h3 h4
  rw [levChar_apply] at a2
  rw [a1, ← a2, r2 hy (r1.1 hy)]
  show emb ((piChar (fun w => (parFam h t s P χ w).H) (fun w => (parFam h t s P χ w).lam) (levRed hc n' ∅ SG _ ⟨g, h3⟩) : Kˣ) : K) = _
  rw [piChar_apply, Units.coe_prod, map_prod, star_prod]
  refine Finset.prod_congr rfl fun w _ => ?_
  have : Finite (𝓞 E ⧸ w.1.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ w.1.ne_bot
  have b1 := ((emb.toMonoidHom.comp ((Units.coeHom K).comp (parFam h t s P χ w).lam)).isOfFinOrder
    (isOfFinOrder_of_finite ⟨_, r1.1 hy w⟩)).norm_eq_one
  refine Eq.trans ?_ ((congrArg star (Complex.inv_eq_conj b1)).trans (Complex.conj_conj _)).symm
  exact congrArg (fun x => emb (((parFam h t s P χ w).lam x : Kˣ) : K))
    (Subtype.ext ((levRed_apply hc n' ∅ SG _ ⟨g, h3⟩ w).trans (hred h2 w.1)))

theorem exists_copy {A : Type} [CommRing A] {n n' : ℕ} (e : n' = n) (g : GL (Fin n') A) :
    ∃ y : GL (Fin n) A, ∀ i j, g.1 i j = y.1 (finCongr e i) (finCongr e j) := by
  subst e
  exact ⟨g, fun _ _ => rfl⟩


attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar in

theorem rd_all {B : Base} {X : PreX B.toPre} (I : TC B X) [NeZero (B.R.N B.R.m - 1)] {Lb U chi y lat st}
    (h : I.ReadsP I.mu0 Lb U chi y lat st) (c : (I.stX I.mu0).Cl) :
    RdLev (E := B.fields.E) B.sp.cm U chi Set.univ (rowTyG I.Ch I.Ps) B.embLL :=
  haveI : IsEmpty (I.Q I.mu0) := by rw [I.twistPrimes_reference_tuple_eq_empty]; infer_instance
  rdLev_of_reads (X := B.fields) (hc := B.sp.cm) (bad := Set.univ) (rowTyG I.Ch I.Ps) (levQX B.R I.sel (I.tup I.mu0))
    B.embLL (U := U) (chi := chi) (y := y c) (k := 1) (p := ((I.stX I.mu0).rep c).1.1) (by rw [mul_one]; exact h.pt c)
    (fun v _ => map_one _) (fun P hP => absurd hP (Finset.notMem_empty _))
    (fun x q hq => h.lev c x q (by rwa [mul_one] at hq))
    (fun x κ h1 h2 => h.chr c x κ h1 (by rwa [mul_one] at h2))

end Gen

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms
open NumberField IsDedekindDomain Matrix MeasureTheory ValuativeRel GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.AdForm GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar


end GlobalTheory.SeeSaw.TopLevel

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

theorem _root_.GlobalTheory.T.stableRangeOne_adeles_cmField : ∀ (D : D7) (a b : AE D), IsCoprime a b → ∃ t : AE D, IsUnit (a + t * b) := by
  first | exact @GlobalTheory.StableRange.adeles_stableRange_one | exact GlobalTheory.StableRange.adeles_stableRange_one | (intros; apply GlobalTheory.StableRange.adeles_stableRange_one <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

theorem _root_.GlobalTheory.T.rational_unitary_subgroup_countable_discrete_fundDomain : ∀ (D : D7) (W : HSp D) (Γ : Subgroup (GA D W)), Γ ≤ GQ W → Countable Γ ∧ DiscreteTopology Γ ∧ ∀ μ : Measure (GA D W), μ.IsHaarMeasure → ∃ 𝓑 : Set (GA D W), IsFundamentalDomain Γ 𝓑 μ := by
  first | exact @GlobalTheory.RationalSubgroupFund.countable_discrete_exists_fundamentalDomain | exact GlobalTheory.RationalSubgroupFund.countable_discrete_exists_fundamentalDomain | (intros; apply GlobalTheory.RationalSubgroupFund.countable_discrete_exists_fundamentalDomain <;> assumption)
end
