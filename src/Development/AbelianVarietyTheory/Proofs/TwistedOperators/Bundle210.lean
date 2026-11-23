module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.L2UnitaryRepresentationData
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle116
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFiniteDimensionalKill
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle098
import Mathlib.Algebra.Module.StablyFree.Basic
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.EmbRelExistsUnique
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemClosureUnitary
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle077
public import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
import Formalism.LocalToGlobal.Divisibility.TrivialExtensionSideWellFormed
import Formalism.LocalToGlobal.IndefiniteReal.Bundle006
import Formalism.LocalToGlobal.IndefiniteReal.LiftCoordinatesInGoodPartFamily
import Formalism.LocalToGlobal.IndefiniteReal.Bundle011
import Formalism.LocalToGlobal.IndefiniteReal.Bundle005
import Formalism.LocalToGlobal.IndefiniteReal.NormalDecomposition.UnitaryTwoPackage
import Formalism.LocalToGlobal.IndefiniteReal.RationalAdjoints.Bundle001
import Formalism.LocalToGlobal.IndefiniteReal.RationalAdjoints.RatThOfLiftTest
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
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
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.UnitCharTriangle
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.HermitianOrthogonalExtensionData
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RatInOfUnit
import Formalism.LocalToGlobal.Divisibility.CoefMod
import Formalism.LocalToGlobal.IndefiniteForms.IndefSide
import Formalism.LocalToGlobal.IndefiniteReal.Bundle001
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle015
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle026

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum
open Formalism.IndefR.Mult (DSModel dualPar parA parB)
open Formalism.MainNotions.SchurIrreducible (AdmGK ARi ARiiiUp ARiiiDown ARiiiLine DiscreteSeriesBlattner admQ5)
open GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction hiding Mat
open GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix (SignCompat plainMat barMat)
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (fockIp)
open GlobalTheory.Chain (signed)
open GlobalTheory.Chain.RealIt (LPol locS locT IsPolyIso)
open MeasureTheory Matrix
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ArchRec

namespace GlobalTheory.ArchRec.PairTensor

open GlobalTheory.InvPairingTensor (exists_real_parts inner_act_skew exists_frame)

variable {p q : ℕ} {T : GrpData p q} (R : DSRep T)

theorem eq_zero_of_ctr (U : Type) [AddCommGroup U] [Module ℂ U] (y : R.HK.V ⊗[ℂ] U)
    (hy : ∀ v, ctr R U v y = 0) : y = 0 := by
  let m : R.HK.V → R.HK.V →ₗ[ℂ] ℂ := fun v => innerₛₗ ℂ (R.ι v) ∘ₗ R.ι
  have sepm : ∀ b, (∀ v, m v b = 0) → b = 0 := fun b h => by
    apply R.ι_inj
    rw [map_zero]
    exact inner_self_eq_zero.1 (h b)
  have key : ∀ v (z : R.HK.V ⊗[ℂ] U),
      GlobalTheory.PairingTensor.contrR (m v) (TensorProduct.comm ℂ _ _ z) = ctr R U v z := by
    intro v z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => rw [TensorProduct.comm_tmul, GlobalTheory.PairingTensor.contrR_tmul, ctr_tmul]; rfl
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  apply (TensorProduct.comm ℂ _ _).injective
  rw [map_zero]
  exact GlobalTheory.PairingTensor.eq_zero_of_contrR m sepm _ fun v => by rw [key, hy]

theorem ext_ctr (U : Type) [AddCommGroup U] [Module ℂ U] (z w : R.HK.V ⊗[ℂ] U)
    (h : ∀ v, ctr R U v z = ctr R U v w) : z = w := by
  rw [← sub_eq_zero]
  exact eq_zero_of_ctr R U _ fun v => by rw [map_sub, h, sub_self]

theorem ctr_add (U : Type) [AddCommGroup U] [Module ℂ U] (v w : R.HK.V) (z : R.HK.V ⊗[ℂ] U) :
    ctr R U (v + w) z = ctr R U v z + ctr R U w z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp only [ctr_tmul, map_add (f := _), inner_add_left, add_smul]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]; abel

theorem ctr_smul (U : Type) [AddCommGroup U] [Module ℂ U] (c : ℂ) (v : R.HK.V)
    (z : R.HK.V ⊗[ℂ] U) : ctr R U (c • v) z = (starRingEnd ℂ) c • ctr R U v z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp only [ctr_tmul, map_smul, inner_smul_left, mul_smul]
  | add x y hx hy => simp only [map_add (f := _), hx, hy, smul_add]

theorem ctr_act (U : Type) [AddCommGroup U] [Module ℂ U] {X : Mat p q} (hX : X ∈ upq p q)
    (v : R.HK.V) (z : R.HK.V ⊗[ℂ] U) :
    ctr R U v (TensorProduct.map (R.HK.act X) LinearMap.id z) = -ctr R U (R.HK.act X v) z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
    rw [TensorProduct.map_tmul, ctr_tmul, ctr_tmul,
      eq_neg_of_add_eq_zero_left (inner_act_skew R hX v a), neg_smul, LinearMap.id_apply]
  | add x y hx hy => simp only [map_add (f := _), hx, hy, neg_add]

variable {W U : Type} [AddCommGroup W] [Module ℂ W] [AddCommGroup U] [Module ℂ U]
  (a : Mat p q →ₗ[ℂ] Module.End ℂ W)

theorem exists_finiteDimensional_kill (ha : IsGK a) (hA : AdmGK R.HK)
    (B : W →ₗ[ℂ] R.HK.V →ₛₗ[starRingEnd ℂ] U) (hB : PInv a R B) (P : W) :
    ∃ E : Submodule ℂ R.HK.V, FiniteDimensional ℂ E ∧
      ∀ y, (∀ x ∈ E, inner ℂ (R.ι y) (R.ι x) = 0) → B P y = 0 := by
  obtain ⟨W₀, hW, hP, hst⟩ := ha.2.1 P
  obtain ⟨E, hE, hE'⟩ := GlobalTheory.T.exists_finiteDimensional_forall_map_mem' p q R.HK hA _ a
    (fun Y Z _ _ => ha.1 Y Z) W₀ hW hst (fun v _ => ha.2.2 v)
  refine ⟨E, hE, fun y hy => ?_⟩
  rw [← Module.forall_dual_apply_eq_zero_iff ℂ]
  intro l
  obtain ⟨F, hF, hyF, hFst⟩ := R.HK.kfin y
  obtain ⟨n, e, heF, he⟩ := exists_frame R.ι R.ι_inj F
  let φ : W →ₗ[ℂ] R.HK.V := ∑ j, (l ∘ₗ B.flip (e j)).smulRight (e j)
  have hφ : ∀ w, φ w = ∑ j, l (B w (e j)) • e j := fun w => by
    simp [φ, LinearMap.sum_apply]
  have hφF : ∀ w, φ w ∈ F := fun w => by
    rw [hφ]; exact F.sum_mem fun j _ => F.smul_mem _ (heF j)
  have hR : ∀ w, ∀ x ∈ F, inner ℂ (R.ι x) (R.ι (φ w)) = l (B w x) := fun w x hx => by
    conv_rhs => rw [← he x hx]
    rw [hφ]

    simp only [map_sum, map_smul, inner_sum, inner_smul_right, LinearMap.map_smulₛₗ,
    inner_conj_symm, smul_eq_mul, mul_comm]
  have hreal : ∀ X ∈ upq p q, IsKC X → ∀ w, φ (a X w) = R.HK.act X (φ w) := by
    intro X hX hK w
    have hd : φ (a X w) - R.HK.act X (φ w) ∈ F :=
      F.sub_mem (hφF _) (hFst X hK _ (hφF w))
    have h0 : ∀ x ∈ F, inner ℂ (R.ι x) (R.ι (φ (a X w) - R.HK.act X (φ w))) = 0 := by
      intro x hx
      have h1 := inner_act_skew R hX x (φ w)
      have h2 := congrArg l (hB X hX w x)
      rw [map_add (f := _), map_zero] at h2
      rw [hR w _ (hFst X hK x hx)] at h1
      rw [map_sub, inner_sub_right, hR _ x hx]
      linear_combination h2 - h1
    rw [← sub_eq_zero]
    apply R.ι_inj
    rw [map_zero]
    exact inner_self_eq_zero.1 (h0 _ hd)
  have heq : ∀ Z, IsKC Z → ∀ w, φ (a Z w) = R.HK.act Z (φ w) := by
    intro Z hZ w
    obtain ⟨X, Y, hX, hY, hK, rfl⟩ := exists_real_parts Z
    simp only [map_add (f := _), map_smul, LinearMap.add_apply, LinearMap.smul_apply,
      hreal X hX (hK hZ).1, hreal Y hY (hK hZ).2]
  rw [← hR P y hyF]
  exact hy _ (hE' φ heq P hP)

theorem exists_pairing (f : W →ₗ[ℂ] R.HK.V ⊗[ℂ] U)
    (hf : ∀ Z, f ∘ₗ a Z = TensorProduct.map (R.HK.act Z) LinearMap.id ∘ₗ f) :
    ∃ B : W →ₗ[ℂ] R.HK.V →ₛₗ[starRingEnd ℂ] U, PInv a R B ∧ ∀ P v, B P v = ctr R U v (f P) := by
  let B : W →ₗ[ℂ] R.HK.V →ₛₗ[starRingEnd ℂ] U :=
    { toFun := fun P =>
        { toFun := fun v => ctr R U v (f P)
          map_add' := fun v w => ctr_add R U v w _
          map_smul' := fun c v => ctr_smul R U c v _ }
      map_add' := fun P Q => by ext v; simp
      map_smul' := fun c P => by ext v; simp }
  refine ⟨B, fun Z hZ P v => ?_, fun _ _ => rfl⟩
  change ctr R U v (f (a Z P)) + ctr R U (R.HK.act Z v) (f P) = 0
  have := LinearMap.congr_fun (hf Z) P
  rw [LinearMap.comp_apply, LinearMap.comp_apply] at this
  rw [this, ctr_act R U hZ, neg_add_cancel]

theorem exists_map (ha : IsGK a) (hA : AdmGK R.HK)
    (B : W →ₗ[ℂ] R.HK.V →ₛₗ[starRingEnd ℂ] U) (hB : PInv a R B) :
    ∃ f : W →ₗ[ℂ] R.HK.V ⊗[ℂ] U,
      (∀ Z, f ∘ₗ a Z = TensorProduct.map (R.HK.act Z) LinearMap.id ∘ₗ f) ∧
        ∀ P v, B P v = ctr R U v (f P) := by
  have ex : ∀ P, ∃ z : R.HK.V ⊗[ℂ] U, ∀ y, ctr R U y z = B P y := by
    intro P
    obtain ⟨E, hE, hkill⟩ := exists_finiteDimensional_kill R a ha hA B hB P
    obtain ⟨n, e, heE, he⟩ := exists_frame R.ι R.ι_inj E
    refine ⟨∑ j, e j ⊗ₜ[ℂ] B P (e j), fun y => ?_⟩
    have h1 := hkill (y - ∑ j, inner ℂ (R.ι (e j)) (R.ι y) • e j) (fun x hx => by
      rw [map_sub, inner_sub_left, sub_eq_zero]
      conv_lhs => rw [← he x hx]

      simp only [map_sum, map_smul, inner_sum, sum_inner, inner_smul_right, inner_smul_left,
      inner_conj_symm, mul_comm])
    rw [map_sub, sub_eq_zero] at h1
    rw [h1]

    simp only [map_sum, ctr_tmul, LinearMap.map_smulₛₗ, inner_conj_symm]
  choose g hg using ex
  let f : W →ₗ[ℂ] R.HK.V ⊗[ℂ] U :=
    { toFun := g
      map_add' := fun P Q => ext_ctr R U _ _ fun y => by
        rw [map_add (f := _), hg, hg, hg, map_add (f := _), LinearMap.add_apply]
      map_smul' := fun t P => ext_ctr R U _ _ fun y => by
        rw [map_smul, hg, hg, map_smul, RingHom.id_apply, LinearMap.smul_apply] }
  have hf : ∀ P y, ctr R U y (f P) = B P y := hg
  have hreal : ∀ X ∈ upq p q, ∀ P,
      f (a X P) = TensorProduct.map (R.HK.act X) LinearMap.id (f P) := by
    intro X hX P
    refine ext_ctr R U _ _ fun y => ?_
    rw [ctr_act R U hX, hf, hf]
    exact eq_neg_of_add_eq_zero_left (hB X hX P y)
  refine ⟨f, fun Z => ?_, fun P y => (hf P y).symm⟩
  obtain ⟨X, Y, hX, hY, -, rfl⟩ := exists_real_parts Z
  refine LinearMap.ext fun P => ?_
  simp only [LinearMap.comp_apply, map_add (f := _), map_smul, LinearMap.add_apply, LinearMap.smul_apply,
    TensorProduct.map_add_left, TensorProduct.map_smul_left, hreal X hX, hreal Y hY]

end GlobalTheory.ArchRec.PairTensor
end

section

namespace EqZeroOfFinite
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped Pointwise TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Grid GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle GlobalTheory.ConstRatio

namespace GlobalTheory.CompanionTheory.FiniteVanish

end GlobalTheory.CompanionTheory.FiniteVanish

end

end EqZeroOfFinite
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped Pointwise TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Grid GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle GlobalTheory.ConstRatio
theorem _root_.GlobalTheory.Adopt.continuous_automorphic_eq_zero_of_vanish_on_finiteAdelic : ∀ (D : D7) (V : HSp D) (φ : GA D V → ℂ), (∀ τ, (gramAt D V τ).PosDef) → Continuous φ → (∀ γ ∈ GQ V, ∀ h, φ (γ * h) = φ h) → (∀ h ∈ GfC V, φ h = 0) → ∀ h, φ h = 0 := by
  intro D V φ _ hcont hleft hzero g
  haveI := GlobalTheory.AutFunCounterexample.topGroup_GA D V
  obtain ⟨u, hu, f, hf, rfl⟩ := (GlobalTheory.UnitarySplit.real_finite_split D V).1 g

  set ψ : GA D V → ℂ := fun x => φ (x * f) with hψ
  have hψc : Continuous ψ := hcont.comp (continuous_mul_const f)
  have hvan : ∀ γ ∈ GQ V, ∀ k ∈ GfC V, ψ (γ * k) = 0 := fun γ hγ k hk => by
    simp only [hψ, mul_assoc, hleft γ hγ]
    exact hzero _ ((GfC V).mul_mem hk hf)
  show ψ u = 0
  by_contra hne
  obtain ⟨γ, hγ, k, hk, hin, -⟩ :=
    GlobalTheory.RealApprox.weak_approx_real V u hu {x | ψ x ≠ 0} (isOpen_ne_fun hψc continuous_const) hne
  exact hin (hvan γ hγ k hk)

end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem scalConj_base_facts : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T0 : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (s : ℕ), A3.fam3.Ok3 s → A3.fam3.TypesSep3 → R.WeakCharacterisation F → (∀ t, (A3.A.fam.R t).OkH ∧ (A3.rowI t).InertRationalAdjoint) → (∀ j t, (A3.A.fam.L j t).OkH ∧ (A3.liftI j t).InertRationalAdjoint) → R.PHecke F → R.PGUnit F → R.PGEquiv F → (R.toCx3 F).zs.InBlock → Formalism.IndefR.Rat.RowTest (R.toCx3 F) → Formalism.IndefR.Rat.LiftTest (R.toCx3 F) → Formalism.IndefR.Rat.LiftTestB (R.toCx3 F) false → (∀ hW, HeckeIntertwiningLifts A3 (R.toCx3 F) hW → U2.OntoC A3 (R.toCx3 F) F.P0 F.ψ0 F.P1 F.ψ1 hW) → 0 < R.kap → (∀ i t p, 0 < R.lam3 i t p A3.A.v0) → R.toRealDat.LUnif → R.PLevW F → R.PThmA → (R.toCx3 F).PartsW false → (R.toCx3 F).H5 F.cr false ∧ (R.toCx3 F).RATth F.cr false ∧ (R.toCx3 F).H3W F.cr false ∧ (lv (F.fc (R.toCx3 F).zs) false).Proviso := by
  intro D G _ _ Pl0 I0 T0 A3 Ks _ _ _ R F s hOk hsep hC hR hL hH hU hE hblk hrt hlt hltb honto hk hl hun hlev hA hsum
  have kR := RealDat3.kFormR_of (F := F) hC.base.models
  have kL := RealDat3.kFormL_of (F := F) hC.base.models
  have jR := RealDat3.jIsoR_of (F := F) hC.base.models
  have jL := RealDat3.jIsoL_of (F := F) hC.base.models
  have thR := hH.1.choose_spec
  have thL := hH.2.choose_spec
  have st : (R.toCx3 F).zs.Stable := CxData.cutStable (R.toCx3 F) kR kL
    (Formalism.IndefR.CxPass.definite_kernel_stable kR hE.1 thR) (Formalism.IndefR.CxPass.lift_kernel_stable kL hE.2 thL)
    (definite_adjoint_closed hOk hR kR jR) (lift_adjoint_closed hOk hL kL jL)
  have wf := A3.side_well_formed hOk F.P0 F.ψ0 (R.toCx3 F).zs st hblk hsep
  have rz : (R.toCx3 F).RatZ := Formalism.IndefR.Rat.ratZOfTests (R.toCx3 F) (cvOf3 A3 F.P0 F.ψ0 F.P1 F.ψ1) kR kL jR jL hrt hlt
  have eig0 := (U2.unitary_two_package A3 (R.toCx3 F) s F.P0 F.ψ0 F.P1 F.ψ1 F.Dc F.Sp F.Zsc hH.2.choose (R.gWx F) hOk kR kL jR jL hrt hlt hL thL hU.2 hE.2 hlev hsum (honto _ thL)).1
  have kf := RealDat3.kForm_of (F := F) hun false
  let X' : CxData A3.fam3.amb3 := { R.toCx3 F with lam := fun j t p _ => (R.toCx3 F).lam j t p A3.fam3.base3.v0 }
  have h5 : (R.toCx3 F).H5 F.cr false := (CxData.cutLifts X' (crdOf3 A3 F.P0 F.ψ0 F.P1 F.ψ1 F.Dc F.Sp F.Zsc) (cvOf3 A3 F.P0 F.ψ0 F.P1 F.ψ1) false wf
    ⟨fun _ => hk, fun j t p _ => hl j t p, RealDat.nP_pos⟩ kf
    (lift_isometry_of_norms hOk jL ⟨rfl, rfl⟩ false) (lift_coordinates_in_subspaces (R.toCx3 F) false) (lift_coordinates_in_good_part_family (R.toCx3 F) false)
    (Formalism.IndefR.CxPass.lift_rationality_of_equivariance hOk kL jL rz hU.2 hE.2 false)
    (Formalism.IndefR.CxPass.lift_descent_at_lower_type hOk kL jL rz hU.2 hE.2 hlev)
    (Formalism.IndefR.CxPass.upper_level_lift_at_lower_type hOk kL jL hU.2 hE.2 hlev)
    (RealDat3.thmAop_of hC.phase hA false) hsum).1
  exact ⟨h5, Formalism.IndefR.Rat.ratThOfLiftTest (R.toCx3 F) _ false hltb h5 kf (RealDat3.ewNorm false) (RealDat.nP_pos false),
    lift_equivariance_of_primitive F.P0 F.ψ0 F.P1 F.ψ1 F.Dc F.Sp F.Zsc kL st hOk thL false,
    proviso_of_lift_eigenvalues A3 (R.toCx3 F) hOk (fun j => hL j A3.A.fam.μ0) F.P0 F.ψ0 eig0⟩

end GlobalTheory
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem phiC_zero_rule {D : D7} (T : CoreJ D) {j : ℕ} {σ : T.Q.c.F →+* ℂ} {W : HSp D} (hV : T.V j σ = W)
    (a : (D.host.E →+* ℂ) × ℕ → ℕ) : phiC T hV a (0 : T.R j) = 0 := by
  subst hV
  show T.phiJ j σ a 0 = 0
  unfold CoreJ.phiJ
  rw [map_zero, map_zero, smul_zero]


set_option linter.unusedVariables false in
theorem evaluates_of_unif : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (fw : FWTie T R κ v₀), R.LUnif → fw.Evaluates := by
  set_option synthInstance.maxHeartbeats 200000 in
    intro D G _ _ Pl0 T0 A T _ R F κ v₀ fw hU i σ hσ hV f
    by_cases hj : ∃ j' : (Fin (R.nW i) → D.what₂.LL) →ₛₗ[σ] (R.HW i σ).H,
        ∀ f : T.cuspA ((i : ℕ) + 1) (wtA (κ i)) (κ i).n,
          ((R.HW i σ).e (j' ((fw.e i f : (R.FW i).WK) : Fin (R.nW i) → D.what₂.LL))) (v₀ i σ) =
            hV ▸ T.phiJ ((i : ℕ) + 1) (σ.comp (algebraMap T.Q.c.F D.what₂.LL)) (wtA (κ i)) (f : T.R ((i : ℕ) + 1))
    · exact fw.ev i σ hσ hV hj f
    · exfalso
      have hz : (R.FW i).j σ = 0 := fw.ev0 i σ hσ hV hj

      have hx : ∀ x : Fin (R.nW i) → D.what₂.LL, x = 0 := by
        intro x
        by_contra hne
        have hli := (hU i σ).1 1 (fun _ => x) (linearIndependent_unique_iff.mpr hne)
        simp only [hz, LinearMap.zero_apply] at hli
        exact hli.ne_zero 0 rfl

      apply hj
      refine ⟨0, fun f' => ?_⟩
      have hf' : f' = 0 := by
        simpa using hx ((fw.e i f' : (R.FW i).WK) : Fin (R.nW i) → D.what₂.LL)
      subst hf'
      simp
      exact (phiC_zero_rule T hV (wtA (κ i))).symm

end GlobalTheory
end

section

noncomputable section

open NumberField IsDedekindDomain

namespace GlobalTheory.GeoActCompare

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.L2.Pj
  Formalism.IndefR.FWT
open GlobalTheory.IndefiniteRowSideFullHecke.GeometricConstantEquiv (Cusp IsLift IsGeo ReadTwist KeepsIntegral IsIntegralForm ConstEquiv IsKappa GeoActAt)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

section Model

variable {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)

theorem levChi_flag (i : Fin D.R.m) (k : GA D (Wc D i)) : levChi _ (R.βW i) (flagL (R.datWp i R.triv)) k = 1 := by
  simp [levChi, Formalism.L2.DIV.levFn, flagL, withP, LevCh.datWp, datY, LevelP.full]
  first
    | exact subgroupCharExtension_one_apply _ _
    | (unfold Formalism.L2.DIV.ext1; exact dite_eq_right_iff.2 fun _ => rfl)

private theorem wall_apply_mul_eq_levChi_mul_of_mem_levS {i : Fin D.R.m} {σ : D.what₂.LL →+* ℂ} {T : MMap (R.MW i σ)} (hT : T ∈ R.Wall i σ)
    (v : (R.MW i σ).Vec) {k : GA D (Wc D i)} (hk : k ∈ levS _ (R.βW i) (R.datWp i R.triv)) (g : GA D (Wc D i)) :
    T v (g * k) = levChi _ (R.βW i) (R.datWp i R.triv) k * T v g := by
  unfold RealDat.Wall Formalism.IndefR.Mult.Mult at hT
  induction hT using Submodule.span_induction with
  | mem x hx =>
    have hx' : IsMultMap R.θ (R.MW i σ) (levS _ (R.βW i) (R.datWp i R.triv))
        (levChi _ (R.βW i) (R.datWp i R.triv)) x := hx
    exact hx'.lev v k hk g
  | zero => simp
  | add x y _ _ hx hy =>
    simp only [MultilinearMap.add_apply, Pi.add_apply, hx, hy]
    ring
  | smul a x _ hx =>
    simp only [MultilinearMap.smul_apply, Pi.smul_apply, smul_eq_mul, hx]
    ring

theorem hasType_e (he : R.models_HW) (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (y : (R.HW i σ).H) (v : (R.MW i σ).Vec) :
    HasType (Wc D i) (R.βW i) (flag1L (R.datWp i R.triv)) ((R.HW i σ).e y v) := by
  have hm : (R.HW i σ).e y ∈ R.Wall i σ := by
    rw [← (he i σ).2.1]
    exact LinearMap.mem_range_self _ y
  intro k hk h
  exact wall_apply_mul_eq_levChi_mul_of_mem_levS R hm v hk h

theorem actW_apply (he : R.models_HW) {i : Fin D.R.m} (σ : D.what₂.LL →+* ℂ) {g : G} {k : GA D (Wc D i)}
    (hk : IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g) k) (y : (R.HW i σ).H) (v : (R.MW i σ).Vec)
    (x : GA D (Wc D i)) : actW R i σ g ((R.HW i σ).e y) v x = (R.HW i σ).e y v (x * k) := by
  have hs := level_action_spec (hasType_e R he i σ y v) ⟨k, hk⟩ k hk x
  rw [levChi_flag R i k, inv_one, one_mul] at hs
  exact hs

end Model

variable (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1))
  (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec)

variable {T R κ v₀}

end GlobalTheory.GeoActCompare
end
end

section

noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.DivisionValues Formalism.IndefR Formalism.IndefR.Links
  Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.IndefR.Arith Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.L2.Pj

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LiftRatObj

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

theorem phiC_congr (T : CoreJ D) {j : ℕ} {σ σ' : T.Q.c.F →+* ℂ} (e : σ = σ') {W : HSp D} (hV : T.V j σ = W)
    (hV' : T.V j σ' = W) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (f : T.R j) : phiC T hV a f = phiC T hV' a f := by
  subst e
  rfl

section General
variable {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (ph : Fin D.R.m → ℂ)

end General

section Obj

variable (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A)
  (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec)
  (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)) (ph : Fin D.R.m → ℂ)

end Obj

end GlobalTheory.LiftRatObj

end
end
