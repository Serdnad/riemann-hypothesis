module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ValLastX
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle018
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle126
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HandBFSmul
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle308
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.T2SpaceTensorProductFiniteExtension
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle002
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle129
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1474
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2173
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1917
import Development.AbelianVarietyTheory.Proofs.HeightProofs.EmbeddingXiZeroNeZero
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIdeleAt
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle150
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle307
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle190
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle181
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle013
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle310
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle006
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.JointSmooth
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SeeSaw.LastStepsX

variable {D : D7}

theorem liftS_smul {S T : HSp D} (om : Om S T) (ν : Measure (GA D T)) (𝓕 : Set (GA D T)) (a : ℂ)
    (G : GA D T → ℂ) (f : WO S T → ℂ) : liftS om ν 𝓕 (a • G) f = a • liftS om ν 𝓕 G f := by
  funext g
  simp only [liftS, Lift.liftInt, Pi.smul_apply, smul_eq_mul]
  rw [← integral_const_mul]
  congr 1; funext x; ring

theorem trc_smul {V : HSp D} (e : GA D V →₀ ℂ) (a : ℂ) (f : GA D V → ℂ) : trc e (a • f) = a • trc e f := by
  funext x
  simp only [trc, rTrans, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun g _ => by ring

theorem perF_smul {c : Comm D} (t : Tup c) (j ρ : ℕ) (h : j + 2 * ρ + 2 = D.R.m) (φ : t.Ch j → GA D (c.X j) → ℂ)
    (a : ℂ) (f : GA D (c.V j) → ℂ) : t.perF j ρ h φ (a • f) = a * t.perF j ρ h φ f := by
  simp only [Tup.perF, trc_smul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun α _ => ?_
  have e := GlobalTheory.HandHom.per_smul (c.B j ρ h) c.ψ 1 a (φ α) (trc (t.e j α) f)
  rw [one_smul, one_mul] at e
  exact e

theorem contAut_trc {V : HSp D} (e : GA D V →₀ ℂ) {f : GA D V → ℂ} (hf : IsContAut V f) : IsContAut V (trc e f) := by
  refine ⟨fun γ hγ g => ?_, ?_⟩
  · simp only [trc, rTrans, Finset.sum_apply, Pi.smul_apply]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [mul_assoc, hf.1 γ hγ]
  · have e : trc e f = fun x => ∑ g ∈ e.support, e g * f (x * g) := by
      funext x
      simp only [trc, rTrans, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [e]
    exact continuous_finsetSum _ fun g _ => continuous_const.mul (hf.2.comp (continuous_mul_const g))

theorem contAut_emb {S A B : HSp D} (o : OrthDec S A B) {f : GA D S → ℂ} (hf : IsContAut S f) :
    Continuous (fun h : GA D A => f (o.emb (h, 1))) ∧ ∀ γ ∈ GQ A, ∀ g, f (o.emb (γ * g, 1)) = f (o.emb (g, 1)) := by
  refine ⟨hf.2.comp (o.continuous_emb.comp (continuous_id.prodMk continuous_const)), fun γ hγ g => ?_⟩
  have e : o.emb (γ * g, 1) = o.emb (γ, 1) * o.emb (g, 1) := by
    rw [← map_mul, Prod.mk_mul_mk, mul_one]
  rw [e, hf.1 _ (o.emb_mem_GQ hγ (one_mem _))]

theorem integrableOn_contAut {V : HSp D} (hV : CoCpt V) (vol : Vol V) {f : GA D V → ℂ} (hc : Continuous f)
    (hi : ∀ γ ∈ GQ V, ∀ g, f (γ * g) = f g) : IntegrableOn f vol.𝓕 vol.μ :=
  (GlobalTheory.CocompactParam.continuous_integral_param D V hV vol Unit (fun g _ => f g) (hc.comp continuous_fst)
    (fun γ hγ g _ => hi γ hγ g)).1 ()

theorem io_ioT {c : Comm D} (t : Tup c) (ht : t.Is) (j : ℕ) (h : j + 2 * 0 + 2 = D.R.m) (F : t.CT)
    (P₁ : PolF D (c.V (j + 1)).rank (c.V j).rank) (P₂ : PolF D c.T.rank (c.V (j + 1)).rank) (v : SmT c.MT) :
    (t.cI j * t.cI (j + 1)) • ((t.io j (t.ioT j h F)).1 (c.It j P₁ (c.ItT j h P₂ v))) =
      liftS (t.om j) (c.vol (j + 1)).μ (c.vol (j + 1)).𝓕
        (liftS (t.omT j h) c.volT.μ c.volT.𝓕 (F.1 v) (t.ptT j h P₂)) (t.pt j P₁) := by
  rw [ht.ioT j h F P₂ v, liftS_smul, ht.io j (by omega) (t.ioT j h F) P₁ (c.ItT j h P₂ v), smul_smul, mul_comm]

theorem perT_comb {c : Comm D} (t : Tup c) (n : ℕ) (h : n = D.R.m) {Y : Type} (S : Finset Y) (k : ℂ) (a : Y → ℂ)
    (φ : Y → t.Ch n → GA D (c.X n) → ℂ) (f : GA D c.T → ℂ)
    (hi : ∀ y' β, IntegrableOn (fun h' => trc (t.eT n h β) f h' * φ y' β ((c.oT n h).emb (h', 1))) c.volT.𝓕 c.volT.μ) :
    t.perT n h (fun β => k • ∑ y' ∈ S, a y' • φ y' β) f = k * ∑ y' ∈ S, a y' * t.perT n h (φ y') f := by
  have e1 : ∀ β, ∫ h' in c.volT.𝓕, trc (t.eT n h β) f h' * (k • ∑ y' ∈ S, a y' • φ y' β) ((c.oT n h).emb (h', 1)) ∂c.volT.μ
      = ∑ y' ∈ S, k * a y' * ∫ h' in c.volT.𝓕, trc (t.eT n h β) f h' * φ y' β ((c.oT n h).emb (h', 1)) ∂c.volT.μ := by
    intro β
    have e2 : (fun h' => trc (t.eT n h β) f h' * (k • ∑ y' ∈ S, a y' • φ y' β) ((c.oT n h).emb (h', 1))) =
        fun h' => ∑ y' ∈ S, (k * a y') * (trc (t.eT n h β) f h' * φ y' β ((c.oT n h).emb (h', 1))) := by
      funext h'
      simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun y' _ => by ring
    rw [e2, integral_finsetSum _ (fun y' _ => (hi y' β).const_mul _)]
    simp_rw [integral_const_mul]
  simp only [Tup.perT, e1, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun y' _ => Finset.sum_congr rfl fun β _ => by ring

end GlobalTheory.SeeSaw.LastStepsX



open GlobalTheory.SeeSaw.LastStepsX in
theorem GlobalTheory.SeeSaw.lastX_of_laws : GlobalTheory.Published.HarishChandraModules → ∀ (D : D7) (c : Comm D) (𝒯 : Type) (t : 𝒯 → Tup c), RapidVal D → c.Is → (∀ s, (t s).Is) → ValLastX t → TwoX t → PerX t → RdX t → LastX t := by
  intro hHC D c 𝒯 t hRV hc ht hVL hTX hPX hRD
  intro j h I _ s α ψ F hψ hF y v
  obtain ⟨χ, hχ⟩ := hRD j (by omega)
  obtain ⟨χ₂, hχ₂⟩ := hRD (j + 1 + 1) (by omega)
  refine GlobalTheory.T.period_linear_relation_density_of_unfolding_steps hHC D c 𝒯 t hc j 0 h I s (fun i => α i * ((t (s i)).cI j * (t (s i)).cI (j + 1)))
    (fun i β => (t (s i)).rd j β (ψ i) y) (fun i => (t (s i)).io j ((t (s i)).ioT j h (F i))) ht
    (fun i β => (hχ (s i) (ψ i) (hψ i) β y).1) c.T c.T c.parT c.MT (c.ItT j h) (hc.spanT j h) ?_ v
  intro P₁ P₂ w
  obtain ⟨C, hCr, hC⟩ := hVL j h P₁ P₂
  obtain ⟨a, ha⟩ := hTX j (by omega) C hCr y
  choose b hb using fun y' => hPX (j + 1 + 1) h y' w
  have hterm : ∀ i, α i * ((t (s i)).cI j * (t (s i)).cI (j + 1)) * (t (s i)).perF j 0 h (fun β => (t (s i)).rd j β (ψ i) y)
      (((t (s i)).io j ((t (s i)).ioT j h (F i))).1 (c.It j P₁ (c.ItT j h P₂ w))) =
      ∑ y' ∈ a.support, a y' * b y' * (α i * ((t (s i)).cV j * (t (s i)).cK j * (t (s i)).cK (j + 1) * (t (s i)).cP) *
        (t (s i)).tail (j + 1 + 1) h ((t (s i)).K (j + 1) ((t (s i)).K j ((t (s i)).S j (ψ i)))) (F i)) := by
    intro i
    have hSψ : (t (s i)).S j (ψ i) ∈ (t (s i)).Ram j := (ht (s i)).stabS j (by omega) _ (hψ i)
    have hψ₁ := (ht (s i)).stabK j (by omega) _ hSψ
    have hψ₂ := (ht (s i)).stabK (j + 1) (by omega) _ hψ₁
    rw [mul_assoc, ← perF_smul, io_ioT (t (s i)) (ht (s i)) j h (F i) P₁ P₂ w, hC (s i) (ψ i) (hψ i) y (F i) w]
    have e2 : (t (s i)).two j (fun β => (t (s i)).rd j β ((t (s i)).S j (ψ i)) y) C = fun β =>
        ((t (s i)).cK j * (t (s i)).cK (j + 1)) • ∑ y' ∈ a.support, a y' •
          (t (s i)).rd (j + 1 + 1) β ((t (s i)).K (j + 1) ((t (s i)).K j ((t (s i)).S j (ψ i)))) y' :=
      funext fun β => ha (s i) _ hSψ β
    have hE : RapidDec c.T ((F i).1 w) := by
      obtain ⟨J, χ', hle⟩ := (ht (s i)).CT
      exact hRV c.θ hc.inf c.T c.parT c.MT J χ' _ (hle (F i).2) w
    have e3 := perT_comb (t (s i)) (j + 1 + 1) h a.support ((t (s i)).cK j * (t (s i)).cK (j + 1)) a
      (fun y' β => (t (s i)).rd (j + 1 + 1) β ((t (s i)).K (j + 1) ((t (s i)).K j ((t (s i)).S j (ψ i)))) y') ((F i).1 w)
      (fun y' β => by
        have ht' := contAut_trc ((t (s i)).eT (j + 1 + 1) h β) ⟨hE.1, hE.2.1⟩
        obtain ⟨hcont, hinv⟩ := contAut_emb (c.oT (j + 1 + 1) h) (hχ₂ (s i) _ hψ₂ β y').1
        exact integrableOn_contAut hc.cpt c.volT (ht'.2.mul hcont) (fun γ hγ g => by rw [ht'.1 γ hγ g, hinv γ hγ g]))
    beta_reduce at e3
    have hb' : ∀ y', (t (s i)).perT (j + 1 + 1) h
        (fun β => (t (s i)).rd (j + 1 + 1) β ((t (s i)).K (j + 1) ((t (s i)).K j ((t (s i)).S j (ψ i)))) y') ((F i).1 w) =
        (t (s i)).cP * b y' * (t (s i)).tail (j + 1 + 1) h ((t (s i)).K (j + 1) ((t (s i)).K j ((t (s i)).S j (ψ i)))) (F i) :=
      fun y' => hb y' (s i) _ hψ₂ (F i)
    rw [e2, e3]
    simp only [hb', Finset.mul_sum]
    exact Finset.sum_congr rfl fun y' _ => by ring
  rw [Finset.sum_congr rfl fun i _ => hterm i, Finset.sum_comm]
  refine Finset.sum_eq_zero fun y' _ => ?_
  rw [← Finset.mul_sum, hF, mul_zero]

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.KJInf Formalism.L2.Forms GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RealEqWeil

theorem weilDatum_realEq : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT χS' χT' : (AE D)ˣ →* Circle) (om om' : Om S T), IsWeilDatumO ψ S T χS χT om → IsWeilDatumO ψ S T χS' χT' om' → (∀ τ, ∃ e : ℚ, HasInfExp D χS τ e ∧ HasInfExp D χS' τ e) → (∀ τ, ∃ e : ℚ, HasInfExp D χT τ e ∧ HasInfExp D χT' τ e) → ∀ a ∈ GinfC S, ∀ b ∈ GinfC T, ∀ f, IsThetaFunO ψ S T f → om (a, b) f = om' (a, b) f := by
  intro D ψ S T χS χT χS' χT' om om' hW hW' hS hT a ha b hb f hf
  obtain ⟨θ, hθ⟩ := GlobalTheory.DualPairCompare.exists_infFam D

  have eS : ∀ τ, HasInfExp D (χS' * χS⁻¹) τ ((0 : ℤ) : ℚ) := fun τ => by
    obtain ⟨e, h1, h2⟩ := hS τ
    simpa using GlobalTheory.Chain.hasInfExp_div h2 h1
  have eT : ∀ τ, HasInfExp D (χT' * χT⁻¹) τ ((0 : ℤ) : ℚ) := fun τ => by
    obtain ⟨e, h1, h2⟩ := hT τ
    simpa using GlobalTheory.Chain.hasInfExp_div h2 h1
  obtain ⟨om'', hW'', hmv⟩ := GlobalTheory.WeilChange.exists_weilDatum_twist D ψ hW.std S T χS χT (χS' * χS⁻¹) (χT' * χT⁻¹) om hW
    (GlobalTheory.WeilVacChar.hecke_mul_inv hW'.hecS hW.hecS) (GlobalTheory.WeilVacChar.hecke_mul_inv hW'.hecT hW.hecT)
    (GlobalTheory.WeilVacChar.resEta_mul_inv hW'.resS hW.resS) (GlobalTheory.WeilVacChar.resEta_mul_inv hW'.resT hW.resT)
  rw [GlobalTheory.WeilVacChar.mul_mul_inv_cancel, GlobalTheory.WeilVacChar.mul_mul_inv_cancel] at hW''
  obtain ⟨x, hx, hxv⟩ := GlobalTheory.OneMapRef.RealMove.exists_root hθ S (GlobalTheory.RealPairBound.gramAt_det_ne D S) a ha
  obtain ⟨y, hy, hyv⟩ := GlobalTheory.OneMapRef.RealMove.exists_root hθ T (GlobalTheory.RealPairBound.gramAt_det_ne D T) b hb
  have x1 : (χT' * χT⁻¹) x = 1 := by
    apply Circle.coe_injective
    rw [hxv _ (fun _ => 0) eT]
    simp
  have y1 : (χS' * χS⁻¹) y = 1 := by
    apply Circle.coe_injective
    rw [hyv _ (fun _ => 0) eS]
    simp
  have h1 := hmv a b x y hx hy
  rw [x1, y1, inv_one, one_mul, Circle.coe_one, one_smul] at h1
  rw [← h1]
  exact GlobalTheory.WeilUniq.weilDatum_unique D ψ hW.std S T χS' χT' om'' om' hW'' hW' (a, b) f hf

end GlobalTheory.RealEqWeil
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

noncomputable section

namespace GlobalTheory.WeilSlice

variable {D : D7}

theorem symplOH_zero_right' (S T : HSp D) (x : WO S T) : symplOH S T x 0 = 0 := by
  simp [symplOH, symplO, hO]

theorem symplOH_zero_left' (S T : HSp D) (x : WO S T) : symplOH S T 0 x = 0 := by
  simp [symplOH, symplO, hO]

def shiftA {S A B : HSp D} (o : OrthDec S A B) (T : HSp D) (g : GA D A) (h : GA D T) : WO S T →+ WO S T where
  toFun w := (o.resS T).symm (actO A T g⁻¹ h⁻¹ (o.resS T w).1, (o.resS T w).2)
  map_zero' := by simp [actO_eq]
  map_add' x y := by
    rw [map_add (f := _), Prod.fst_add, Prod.snd_add, ← map_add (f := _)]
    congr 1
    simp [actO_eq, Matrix.mul_add, Matrix.add_mul]

theorem shiftA_apply {S A B : HSp D} (o : OrthDec S A B) (T : HSp D) (g : GA D A) (h : GA D T) (w : WO S T) :
    shiftA o T g h w = (o.resS T).symm (actO A T g⁻¹ h⁻¹ (o.resS T w).1, (o.resS T w).2) := rfl

theorem actO_shift (A T : HSp D) (g : GA D A) (h : GA D T) (u : WO A T) : actO A T g h (actO A T g⁻¹ h⁻¹ u) = u := by
  simp only [actO_eq, inv_inv, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (mt T h), mt_mul_inv, Matrix.one_mul, mt_mul_inv, Matrix.mul_one]

theorem continuous_shiftA {S A B : HSp D} (o : OrthDec S A B) (T : HSp D) (g : GA D A) (h : GA D T) :
    Continuous (shiftA o T g h) := by
  have h1 : Continuous fun w : WO S T => (o.resS T w).1 := continuous_fst.comp (o.continuous_resS T)
  have h2 : Continuous fun w : WO S T => (o.resS T w).2 := continuous_snd.comp (o.continuous_resS T)
  refine (o.continuous_resS_symm T).comp (Continuous.prodMk ?_ h2)
  simp only [actO_eq]
  exact (continuous_const.matrix_mul h1).matrix_mul continuous_const

theorem shiftA_fin {S A B : HSp D} (o : OrthDec S A B) (T : HSp D) (g : GA D A) (h : GA D T) (w : WO S T)
    (hw : w.map (finPart D) = 0) : (shiftA o T g h w).map (finPart D) = 0 := by
  rw [shiftA_apply, OrthDec.resS_symm_apply]
  simp only [OrthDec.resS_apply, actO_eq]
  rw [Matrix.map_add _ (map_add (finPart D))]
  simp only [Matrix.map_mul, hw, Matrix.zero_mul, Matrix.mul_zero, zero_add]

theorem shiftA_inf {S A B : HSp D} (o : OrthDec S A B) (T : HSp D) (g : GA D A) (h : GA D T) (w : WO S T)
    (hw : w.map (infPart D) = 0) : (shiftA o T g h w).map (infPart D) = 0 := by
  rw [shiftA_apply, OrthDec.resS_symm_apply]
  simp only [OrthDec.resS_apply, actO_eq]
  rw [Matrix.map_add _ (map_add (infPart D))]
  simp only [Matrix.map_mul, hw, Matrix.zero_mul, Matrix.mul_zero, zero_add]

theorem half (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S A B T : HSp D) (o : OrthDec S A B) (f : WO S T → ℂ)
    (hf : IsThetaFunO ψ S T f) (χ χ' : (AE D)ˣ →* Circle) (om : Om A T) (hom : IsWeilDatumO ψ A T χ χ' om)
    (p : GA D A × GA D T) :
    IsThetaFunO ψ S T fun x => om p (fun u => f ((o.resS T).symm (u, (o.resS T x).2))) (o.resS T x).1 := by
  obtain ⟨g, h⟩ := p
  have hstd := hom.std
  obtain ⟨θ, hθ⟩ := GlobalTheory.Member.exists_isInfFam_family D
  have hslice := (GlobalTheory.T.thetaFunction_products_slices_orthogonalDecomposition D ψ hstd S A B T o).2.2.2
  have hsob := (GlobalTheory.T.weil_operator_orth_summand_slices_sobolev_bounded D ψ θ hθ S A B T o).1 χ χ' om hom (g, h)
  refine GlobalTheory.T.theta_of_heisenberg_intertwiner_bounded_at_zero D ψ hstd θ hθ S T S T (shiftA o T g h) (continuous_shiftA o T g h) (shiftA_fin o T g h)
    (shiftA_inf o T g h) (fun F x => om (g, h) (fun u => F ((o.resS T).symm (u, (o.resS T x).2))) (o.resS T x).1)
    ?_ ?_ ?_ f hf
  · have e : (fun F : WO S T → ℂ => om (g, h) (fun u => F ((o.resS T).symm (u, (o.resS T 0).2))) (o.resS T 0).1) =
        fun F => om (g, h) (fun u => F ((o.resS T).symm (u, 0))) 0 := by
      funext F
      simp only [map_zero, Prod.fst_zero, Prod.snd_zero]
    exact e ▸ hsob
  · intro F w hF
    funext x
    have hG := (hslice F hF).1 ((o.resS T x).2 + (o.resS T w).2)
    have hin : (fun u => heisO ψ S T (shiftA o T g h w) F ((o.resS T).symm (u, (o.resS T x).2))) =
        ψ (symplOH B T (o.resS T x).2 (o.resS T w).2) • heisO ψ A T (actO A T g⁻¹ h⁻¹ (o.resS T w).1)
          (fun u => F ((o.resS T).symm (u, (o.resS T x).2 + (o.resS T w).2))) := by
      funext u
      simp only [heisO, shiftA_apply, Pi.smul_apply, smul_eq_mul]
      rw [o.symplOH_resS]
      simp only [AddEquiv.apply_symm_apply]
      rw [← map_add (f := _), Prod.mk_add_mk, AddChar.map_add_eq_mul]
      ring
    show om (g, h) (fun u => heisO ψ S T (shiftA o T g h w) F ((o.resS T).symm (u, (o.resS T x).2))) (o.resS T x).1 = _
    rw [hin, map_smul, hom.om_heis g h _ _ hG, actO_shift]
    simp only [Pi.smul_apply, heisO, smul_eq_mul]
    rw [o.symplOH_resS, map_add (o.resS T) x w, AddChar.map_add_eq_mul]
    simp only [Prod.fst_add, Prod.snd_add]
    ring
  · intro F γ hF
    have hr : ratW T S γ ∈ ratL T S := ⟨γ, rfl⟩
    obtain ⟨ha, hb⟩ := (o.mem_ratL_resS T _).1 hr
    have hsl : (fun u => F ((o.resS T).symm (u, (o.resS T (ratW T S γ)).2))) =
        fun u => F ((o.resS T).symm (u, 0)) := by
      funext u
      have hb' : (o.resS T).symm (0, (o.resS T (ratW T S γ)).2) ∈ ratL T S := by
        refine (o.mem_ratL_resS T _).2 ?_
        simp only [AddEquiv.apply_symm_apply]
        exact ⟨zero_mem _, hb⟩
      obtain ⟨δ, hδ⟩ := hb'
      have hδ' : ratW T S δ = (o.resS T).symm (0, (o.resS T (ratW T S γ)).2) := hδ
      have e : (o.resS T).symm (u, (o.resS T (ratW T S γ)).2) = ratW T S δ + (o.resS T).symm (u, 0) := by
        rw [hδ', ← map_add (f := _), Prod.mk_add_mk, zero_add, add_zero]
      rw [e, hF.quasi δ, hδ', o.symplOH_resS]
      simp only [AddEquiv.apply_symm_apply, symplOH_zero_left', symplOH_zero_right', add_zero, neg_zero,
        AddChar.map_zero_eq_one, one_mul]
    show om (g, h) (fun u => F ((o.resS T).symm (u, (o.resS T (ratW T S γ)).2))) (o.resS T (ratW T S γ)).1 =
      om (g, h) (fun u => F ((o.resS T).symm (u, (o.resS T 0).2))) (o.resS T 0).1
    simp only [map_zero, Prod.fst_zero, Prod.snd_zero]
    rw [hsl]
    obtain ⟨γa, hγa⟩ := ha
    have ea : (o.resS T (ratW T S γ)).1 = ratW T A γa + 0 := by rw [add_zero]; exact hγa.symm
    rw [ea, (hom.om_pres (g, h) _ ((hslice F hF).1 0)).quasi γa 0, symplOH_zero_right', neg_zero,
      AddChar.map_zero_eq_one, one_mul]

theorem resS_symm_swap {S A B : HSp D} (o : OrthDec S A B) (T : HSp D) (u : WO B T) (v : WO A T) :
    (o.symm.resS T).symm (u, v) = (o.resS T).symm (v, u) := by
  rw [OrthDec.resS_symm_apply, OrthDec.resS_symm_apply]; exact add_comm _ _

theorem weilSlice_theta : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S A B T : HSp D) (o : OrthDec S A B) (f : WO S T → ℂ), IsThetaFunO ψ S T f → (∀ (χ χ' : (AE D)ˣ →* Circle) (om : Om A T), IsWeilDatumO ψ A T χ χ' om → ∀ p, IsThetaFunO ψ S T fun x => om p (fun u => f ((o.resS T).symm (u, (o.resS T x).2))) (o.resS T x).1) ∧ ∀ (χ χ' : (AE D)ˣ →* Circle) (om : Om B T), IsWeilDatumO ψ B T χ χ' om → ∀ p, IsThetaFunO ψ S T fun x => om p (fun v => f ((o.resS T).symm ((o.resS T x).1, v))) (o.resS T x).2 := by
  intro D ψ S A B T o f hf
  refine ⟨fun χ χ' om hom p => half D ψ S A B T o f hf χ χ' om hom p, fun χ χ' om hom p => ?_⟩
  have h2 := half D ψ S B A T o.symm f hf χ χ' om hom p
  have key : (fun x => om p (fun v => f ((o.resS T).symm ((o.resS T x).1, v))) (o.resS T x).2) =
      fun x => om p (fun u => f ((o.symm.resS T).symm (u, (o.symm.resS T x).2))) (o.symm.resS T x).1 := by
    funext x
    simp only [resS_symm_swap]
    rfl
  exact key ▸ h2

end GlobalTheory.WeilSlice
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical

theorem _root_.GlobalTheory.T.thetaChainStep_finiteDatum_isSchwartzBruhat_half : ∀ (D : D7) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ S.rank) (χ ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (Z : Finset (Pl D.host.E)) (e : AE D), IsSelfDualC S ΛS → IsSelfDualC T ΛT → Formalism.L2.DIV.IsFrame βS ΛS → Formalism.L2.DIV.IsFrame βT ΛT → IsIdemSum e Z → IsSBHalf e (latO S T ΛS ΛT fun _ => True) (fun x : WO S T => if IsHalf e x ∧ IsIntM (frMapO S T βS βT x) then omegaG L χ (fun PP => redM PP (frMapO S T βS βT x)) * omegaQ ∅ L.r ξ 1 (fun PP => redM PP (frMapO S T βS βT x)) else 0) := by
  first | exact @GlobalTheory.ChainOnto.isSBHalf_stepDatum | exact GlobalTheory.ChainOnto.isSBHalf_stepDatum | (intros; apply GlobalTheory.ChainOnto.isSBHalf_stepDatum <;> assumption)
end
