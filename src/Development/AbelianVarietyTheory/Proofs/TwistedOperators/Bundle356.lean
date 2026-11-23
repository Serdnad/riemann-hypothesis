module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle004
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.PartW
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1177
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1245
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle159
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSphericalOperatorsRowsNormalEigenspaces
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalOperatorsFormsOnRankSpaceNormal
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle334
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOneOfConjMemOfPow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1781
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle205
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.HermitianOrthogonalExtensionData
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicUnitaryTopology
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle354
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle220
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle294
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralRightTranslate
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle137
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittHyperbolicAnisotropicCommuteLevi
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsClosedNFlag
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle340
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle302
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.T2SpaceTensorProductFiniteExtension
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1389
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle016
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle339
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
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle143
import Mathlib.Topology.Compactness.Paracompact
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.UnitCharTriangle
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RatInOfUnit
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.LiftRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.RowsNeProof

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]



theorem exists_part (R : RealDat D A Ks) (F : Face D A) {s : ℕ} (hs : A.fam.Ok s) (hC : GlobalTheory.Hk3.Core R F)
    (hS : GlobalTheory.Hk3.SchurAll R) (SF : Finset (HeightOneSpectrum (𝓞 D.host.F))) (hSF : GlobalTheory.Hk3.IsSF R SF) (b : Bool)
    (i : Fin D.R.m) (hi : R.Wat i (sg0 D A) (R.levL F b (sg0 D A)) ≠ ⊥) :
    ∃ c, ∃ z ∈ GlobalTheory.Hk3.Wcc R SF i c, z ≠ 0 ∧ (R.HW i (sg0 D A)).e z ∈ R.Wat i (sg0 D A) (R.levL F b (sg0 D A)) := by
  classical
  have irr : ∀ χ ∈ A.X, IsAbsIrrChar χ := hs.irr
  obtain ⟨y, hy, hy0⟩ := Submodule.ne_bot_iff _ |>.1 hi
  have hWall : R.Wat i (sg0 D A) (R.levL F b (sg0 D A)) ≤ R.Wall i (sg0 D A) :=
    (GlobalTheory.PartDims.goodPart_le_flag (L := R.datWp i R.triv) R.θ _ rfl rfl _ _).trans inf_le_left
  have hR : LinearMap.range (R.HW i (sg0 D A)).e = R.Wall i (sg0 D A) := (hC.models.HW i (sg0 D A)).2.1
  obtain ⟨x, rfl⟩ : y ∈ LinearMap.range (R.HW i (sg0 D A)).e := hR ▸ hWall hy
  have hx0 : x ≠ 0 := by rintro rfl; exact hy0 (map_zero _)
  obtain ⟨hxe, hxt⟩ := (GlobalTheory.WatType.wat_iff_type R F hs hC b i x).1 hy
  obtain ⟨h, -, -, -, hsup, hstab, -, -⟩ := GlobalTheory.SphOpsModel.sphericalOperators_forms_on_rank_space_normal_alt R F hC hS irr SF hSF i
  obtain ⟨hidem, -, -, -⟩ := GlobalTheory.Hk3.eH_laws R F hC irr i
  obtain ⟨lam, hlam⟩ : ∃ lam : (F.lvl b).P → ℂ, ∀ p, lam p = sg0 D A ((((F.lvl b).ψ⁻¹ p : D.what₂.LLˣ)) : D.what₂.LL) :=
    ⟨_, fun _ => rfl⟩
  have lam_mul : ∀ p q, lam (p * q) = lam p * lam q := fun p q => by
    simp only [hlam, map_mul, Units.val_mul]
  have lam_ne : ∀ p, lam p ≠ 0 := fun p => by rw [hlam]; exact (map_ne_zero _).2 (Units.ne_zero _)
  have hxt' : ∀ p : (F.lvl b).P, R.gW i (sg0 D A) (p : G) x = lam p • x := fun p => by rw [hlam]; exact hxt p
  obtain ⟨π, hπ⟩ : ∃ π : Module.End ℂ (R.HW i (sg0 D A)).H,
      ∀ w, π w = ∑ p : (F.lvl b).P, (lam p)⁻¹ • R.gW i (sg0 D A) (p : G) w :=
    ⟨∑ p : (F.lvl b).P, (lam p)⁻¹ • R.gW i (sg0 D A) (p : G), fun w => by
      simp only [LinearMap.sum_apply, LinearMap.smul_apply]⟩
  have htype : ∀ w (q : (F.lvl b).P), R.gW i (sg0 D A) (q : G) (π w) = lam q • π w := by
    intro w q

    rw [hπ, map_sum, Finset.smul_sum]
    refine Fintype.sum_equiv (Equiv.mulLeft q) _ _ fun p => ?_
    rw [map_smul, ← Module.End.mul_apply, ← map_mul, smul_smul, Equiv.coe_mulLeft]
    show (lam p)⁻¹ • R.gW i (sg0 D A) ((q : G) * p) w =
      (lam q * (lam (q * p))⁻¹) • R.gW i (sg0 D A) ((q * p : (F.lvl b).P) : G) w
    rw [lam_mul, mul_inv, ← mul_assoc, mul_inv_cancel₀ (lam_ne q), one_mul]
    exact congrArg (fun g => (lam p)⁻¹ • R.gW i (sg0 D A) g w) (Subgroup.coe_mul _ q p).symm
  have hπmem : ∀ c w, w ∈ GlobalTheory.Hk3.Wcc R SF i c → π w ∈ GlobalTheory.Hk3.Wcc R SF i c := by
    intro c w hw
    rw [hπ]
    refine Submodule.sum_mem _ fun p _ => ?_
    refine Submodule.smul_mem _ _ ?_
    have h2 : R.gW i (sg0 D A) (p : G) w ∈ (GlobalTheory.Hk3.Wcc R SF i c).map (R.gW i (sg0 D A) (p : G)) :=
      Submodule.mem_map_of_mem hw
    exact hstab c (p : G) h2
  have hfix : π x = (Fintype.card (F.lvl b).P : ℂ) • x := by
    have h1 : ∀ p : (F.lvl b).P, (lam p)⁻¹ • R.gW i (sg0 D A) (p : G) x = x := fun p => by
      rw [hxt' p, smul_smul, inv_mul_cancel₀ (lam_ne p), one_smul]
    rw [hπ, Finset.sum_congr rfl fun p _ => h1 p, Finset.sum_const, Finset.card_univ, Nat.cast_smul_eq_nsmul]
  have hπx : π x ≠ 0 := by
    intro h0
    apply hx0
    have hc : (Fintype.card (F.lvl b).P : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
    have h3 := congrArg (fun z => (Fintype.card (F.lvl b).P : ℂ)⁻¹ • z) (hfix.symm.trans h0)
    rwa [smul_zero, smul_smul, inv_mul_cancel₀ hc, one_smul] at h3
  have hxR := hsup.ge (LinearMap.mem_range.2 ⟨x, hxe⟩)
  have hmem := (Submodule.map_iSup π (fun c => GlobalTheory.Hk3.Wcc R SF i c)).le (Submodule.mem_map_of_mem (f := π) hxR)
  by_contra hall
  push_neg at hall
  have hbot : ∀ c, (GlobalTheory.Hk3.Wcc R SF i c).map π = ⊥ := by
    intro c
    rw [eq_bot_iff]
    rintro _ ⟨w, hw, rfl⟩
    have hz : π w ∈ GlobalTheory.Hk3.Wcc R SF i c := hπmem c w hw
    have he : GlobalTheory.Hk3.eH R i (π w) = π w := by
      obtain ⟨u, hu⟩ := LinearMap.mem_range.1 (hsup.le (Submodule.mem_iSup_of_mem c hz))
      rw [← hu, ← Module.End.mul_apply, hidem]
    by_contra h0
    exact hall c (π w) hz h0
      ((GlobalTheory.WatType.wat_iff_type R F hs hC b i _).2 ⟨he, fun p => by rw [htype w p, hlam]⟩)
  simp only [hbot, iSup_bot, Submodule.mem_bot] at hmem
  exact hπx hmem

theorem rowsNe : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), ∀ s : ℕ, A.fam.Ok s → GlobalTheory.Hk3.Core R F → GlobalTheory.Hk3.SchurAll R → ∀ SF, GlobalTheory.Hk3.IsSF R SF → GlobalTheory.TrCopy.TRLev R F SF → (∀ b, ∃ i, R.Wat i (sg0 D A) (R.levL F b (sg0 D A)) ≠ ⊥) → RowsNe R F := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F s hs hC hS SF hSF hTR hW b
  obtain ⟨i, hi⟩ := hW b
  obtain ⟨c, z, hzc, hz0, hzW⟩ := exists_part R F hs hC hS SF hSF b i hi
  have hinj := (hC.models.HW i (sg0 D A)).1
  have hez : (R.HW i (sg0 D A)).e z ≠ 0 := fun h => hz0 (hinj (h.trans (map_zero _).symm))
  have hzc' := (Submodule.mem_inf.1 (Submodule.mem_comap.1 hzc)).2
  have hpart : (R.HW i (sg0 D A)).e z ∈ GlobalTheory.TrCopy.partW R.θ (R.MW i (sg0 D A))
      (levS _ (R.βW i) (R.datWp i (R.levL F b (sg0 D A)))) (levChi _ (R.βW i) (R.datWp i (R.levL F b (sg0 D A))))
      (R.eWf i (sg0 D A)) SF c := by
    refine Submodule.mem_inf.2 ⟨Submodule.mem_inf.2 ⟨(Submodule.mem_inf.1 hzW).1, ?_⟩, hzW⟩
    have h1 := (Submodule.mem_inf.1 hzc').2
    simp only [Submodule.mem_iInf] at h1 ⊢
    exact fun P d B hB => h1 P d B (GlobalTheory.T.heckeOperator_faceLevel_eq_principalLevel R F hC SF hSF b i P d B hB)
  have hne : GlobalTheory.TrCopy.partW R.θ (R.MW i (sg0 D A))
      (levS _ (R.βW i) (R.datWp i (R.levL F b (sg0 D A)))) (levChi _ (R.βW i) (R.datWp i (R.levL F b (sg0 D A))))
      (R.eWf i (sg0 D A)) SF c ≠ ⊥ := fun h => hez ((Submodule.mem_bot ℂ).1 (h ▸ hpart))
  have hr := (hTR i).2 b c
  intro hE
  apply hne
  rw [← Submodule.rank_eq_zero, ← hr, Submodule.rank_eq_zero]
  exact eq_bot_iff.2 (inf_le_right.trans hE.le)

end GlobalTheory.RowsNeProof

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.LiftRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdjointInjectiveOfParts

theorem adjoint_inj_of_parts {H H' : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
    [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [FiniteDimensional ℂ H'] (T : H' →ₗ[ℂ] H) {ι : Type*}
    (P : ι → Submodule ℂ H) (s : ι → ℂ) (hs : ∀ c, s c ≠ 0)
    (hP : ∀ c, ∀ x ∈ P c, T (LinearMap.adjoint T x) = s c • x) {x : H} (hx : x ∈ ⨆ c, P c)
    (h0 : LinearMap.adjoint T x = 0) : x = 0 := by
  have hle : (⨆ c, P c) ≤ LinearMap.range T := by
    refine iSup_le fun c y hy => ⟨LinearMap.adjoint T ((s c)⁻¹ • y), ?_⟩
    rw [hP c _ ((P c).smul_mem _ hy), smul_smul, mul_inv_cancel₀ (hs c), one_smul]
  obtain ⟨w, rfl⟩ := hle hx
  have h1 : ⟪T w, T w⟫_ℂ = 0 := by
    rw [← LinearMap.adjoint_inner_right, h0, inner_zero_right]
  exact inner_self_eq_zero.1 h1

end GlobalTheory.AdjointInjectiveOfParts


open GlobalTheory.Hk3 in
theorem GlobalTheory.LiftRows.upInj_of_scal : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → GlobalTheory.Hk3.SchurAll R → (∀ χ ∈ A.X, IsAbsIrrChar χ) → ∀ SF, GlobalTheory.Hk3.IsSF R SF → Scal R SF → UpInj R ∧ UpInjW R := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hC hS hI SF hSF hScal
  obtain ⟨lam, κ, hκ, hl, hW, hE⟩ := hScal
  constructor
  · intro t
    refine (injective_iff_map_eq_zero _).2 fun x h0 => ?_
    obtain ⟨h, -, -, hsp, -⟩ := GlobalTheory.Hk3.OpsRows.exists_opsE R F hC hS SF hSF
    refine GlobalTheory.AdjointInjectiveOfParts.adjoint_inj_of_parts (R.Th t) (fun c => EEc R SF c)
      (fun c => ((κ * ∏ i, lam i t c : ℝ) : ℂ))
      (fun c => Complex.ofReal_ne_zero.2 (mul_pos hκ (Finset.prod_pos fun i _ => hl i t c)).ne')
      (fun c x hx => hE t c x hx) ?_ h0
    rw [hsp]; trivial
  · intro i t x hx h0
    obtain ⟨h, -, -, -, hsp, -⟩ := GlobalTheory.SphOpsModel.sphericalOperators_forms_on_rank_space_normal_alt R F hC hS hI SF hSF i
    refine GlobalTheory.AdjointInjectiveOfParts.adjoint_inj_of_parts (R.thG i t) (fun c => Wcc R SF i c)
      (fun c => ((lam i t c : ℝ) : ℂ)) (fun c => Complex.ofReal_ne_zero.2 (hl i t c).ne')
      (fun c x hx => hW i t c x hx) ?_ h0
    rw [hsp]; exact ⟨x, hx⟩
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus posDef_dual Cols levPlus mem_cols)

namespace GlobalTheory.RowTest

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}

section Generic

variable {G Γ W Cl ι : Type} [Group G] [Group Γ] [NormedAddCommGroup W] [InnerProductSpace ℂ W] [Finite Cl]


open Classical in
theorem eq_adForms_of_values (ιG : Γ →* G) (ρ : Γ →* Module.End ℂ W) (J : Subgroup G) (y : Cl → G)
    (hdec : ∀ g, ∃ (γ : Γ) (c : Cl) (k : J), g = ιG γ * y c * k) (S : Submodule ℂ (G → W))
    (hS : S ≤ Bridge.AdForms ιG ρ J 1) (w : ι → W) (hw : Submodule.span ℂ (Set.range w) = ⊤)
    (hsingle : ∀ c i, ∃ s ∈ S, ∀ c', s (y c') = if c' = c then w i else 0) : S = Bridge.AdForms ιG ρ J 1 := by
  classical
  have : Fintype Cl := Fintype.ofFinite _
  refine le_antisymm hS fun F hF => ?_
  let ev : (G → W) →ₗ[ℂ] (Cl → W) := LinearMap.pi fun c => LinearMap.proj (y c)
  have hev : ∀ f c, ev f c = f (y c) := fun _ _ => rfl
  have hinj : ∀ f ∈ Bridge.AdForms ιG ρ J 1, ev f = 0 → f = 0 := by
    intro f hf h0
    funext g
    obtain ⟨γ, c, k, rfl⟩ := hdec g
    have h1 : f (y c) = 0 := congrFun h0 c
    have h2 := hf γ (y c) k
    rw [h2, h1, map_zero, smul_zero]
    rfl
  have hsurj : S.map ev = ⊤ := by
    refine eq_top_iff.2 fun f _ => ?_
    rw [← Finset.univ_sum_single f]
    refine Submodule.sum_mem _ fun c _ => ?_
    have hfc : f c ∈ Submodule.span ℂ (Set.range w) := by rw [hw]; trivial
    have e : Pi.single c (f c) = LinearMap.single ℂ (fun _ : Cl => W) c (f c) := rfl
    rw [e]
    refine Submodule.mem_comap.1 (((Submodule.span_le (p := (S.map ev).comap (LinearMap.single ℂ (fun _ : Cl => W) c))).2 ?_) hfc)
    rintro _ ⟨i, rfl⟩
    obtain ⟨s, hs, hsv⟩ := hsingle c i
    refine Submodule.mem_comap.2 ⟨s, hs, funext fun c' => ?_⟩
    rw [hev, hsv]
    by_cases h : c' = c
    · subst h; simp
    · simp [h]
  obtain ⟨s, hs, hse⟩ : ev F ∈ S.map ev := by rw [hsurj]; trivial
  have h0 : F - s = 0 := hinj _ (sub_mem hF (hS hs)) (by rw [map_sub, hse, sub_self])
  rwa [sub_eq_zero.1 h0]

end Generic

section Reps

variable {T' : Type} {L : LevCh D T'} {sc : Consts} {G : GridData L sc}

theorem exists_gf_reps (rp : ClassReps G) :
    ∃ y : G.ClPlus → Bridge.Gf (G.V (.top 0)),
      (∀ c, Formalism.UG.bc (Lev.swapAE D) ((y c : Bridge.Gf (G.V (.top 0))) : GL _ _) = (rp.x c : GLf G)) ∧
      ∀ g : Bridge.Gf (G.V (.top 0)), ∃ (γ : GQ (G.V (.top 0))) (c : G.ClPlus) (k : levPlus G),
        g = Bridge.ratF (G.V (.top 0)) γ * y c * k := by
  obtain ⟨hfin, -, -, -, hcl⟩ := GlobalTheory.DefFree.AdelCls.adelic_classes D (G.V (.top 0))
  choose h _ hh using fun c => hfin (rp.x c)
  refine ⟨fun c => (finHom (G.V (.top 0))).rangeRestrict (h c), fun c => ?_, fun g => ?_⟩
  · have := congrArg Subtype.val (hh c)
    exact this
  · have hg0 : ∃ h0 : GA D (G.V (.top 0)), finHom (G.V (.top 0)) h0 = g.1 := g.2
    obtain ⟨h0, hg⟩ := hg0
    have hc : GlobalTheory.DefFree.clsA (G.V (.top 0)) G.Kplus (h (GlobalTheory.DefFree.clsA (G.V (.top 0)) G.Kplus h0)) =
        GlobalTheory.DefFree.clsA (G.V (.top 0)) G.Kplus h0 := by
      show (Quotient.mk'' (GlobalTheory.DefFree.finU (G.V (.top 0)) (h (GlobalTheory.DefFree.clsA (G.V (.top 0)) G.Kplus h0))) :
        Cl D.sp.cm (G.V (.top 0)).gram G.Kplus) = _
      rw [hh]
      exact rp.classRepresentative_mk _
    have hx := (hcl G.Kplus (h (GlobalTheory.DefFree.clsA (G.V (.top 0)) G.Kplus h0)) h0).1 hc
    obtain ⟨γ, hγ, hx⟩ := hx
    obtain ⟨κ, hκ, k, hk, e⟩ := hx
    have hκ' : (finHom (G.V (.top 0))).rangeRestrict κ ∈ levPlus G := by
      show Formalism.UG.bc (Lev.swapAE D) (finHom (G.V (.top 0)) κ) ∈ G.Kplus
      exact hκ.2
    refine ⟨⟨γ, hγ⟩, GlobalTheory.DefFree.clsA (G.V (.top 0)) G.Kplus h0, ⟨_, hκ'⟩, Subtype.ext ?_⟩
    have hk1 : finHom (G.V (.top 0)) k = 1 := hk
    show g.1 = finHom (G.V (.top 0)) γ * finHom (G.V (.top 0)) (h (GlobalTheory.DefFree.clsA (G.V (.top 0)) G.Kplus h0)) *
      finHom (G.V (.top 0)) κ
    have e2 := congrArg (finHom (G.V (.top 0))) e
    simp only [map_mul (finHom (G.V (.top 0))), hk1, mul_one] at e2
    exact hg.symm.trans e2


open Classical in
theorem span_colOf_psi {θ : InfFam D} (hθ : IsInfFam θ) (rp : ClassReps G) {n : ℕ} (e : Fin n ≃ TestIx G × VVIdx (LaP G))
    (Φ : G.Datum) :
    Submodule.span ℂ ((fun a => colOf θ (psi rp e a)) '' {a | datumOf e a = Φ}) = Cols G θ := by
  classical
  obtain ⟨y, hy, hdec⟩ := exists_gf_reps rp
  have hspan : Submodule.span ℂ (Set.range fun i => GlobalTheory.CoefModel.toHilb (LaP G) (posDef_dual G)
      (GlobalTheory.CoefModel.mapVV D.what₂.embLL (LaP G) (bVV D.what₂.LL (LaP G) i))) = ⊤ := by
    have := congrArg (Submodule.map (GlobalTheory.CoefModel.toHilb (LaP G) (posDef_dual G)).toLinearMap)
      (GlobalTheory.CoefModel.span_mapVV D.what₂.embLL (LaP G))
    rw [Submodule.map_span, Submodule.map_top, LinearEquiv.range, ← Set.range_comp] at this
    exact this
  refine eq_adForms_of_values (W := (coefPlus G θ).W) (Bridge.ratF (G.V (.top 0))) (coefPlus G θ).coef.ρ
    (levPlus G) y hdec _ ?_ _ hspan fun c i => ?_
  · rw [Submodule.span_le]
    rintro _ ⟨a, -, rfl⟩
    exact colOf_mem hθ (psi_left _ _ a) fun g _ hk => psi_right _ _ a g hk
  · refine ⟨colOf θ (psi rp e (e.symm ((Φ, c), i))), Submodule.subset_span ⟨_, ?_, rfl⟩, fun c' => ?_⟩
    · show (e (e.symm ((Φ, c), i))).1.1 = Φ
      rw [Equiv.apply_symm_apply]
    · unfold colOf psi
      rw [hy c', Equiv.apply_symm_apply, rp.gridClassReps_delta_apply_rep (ClassReps.neat rp)]
      by_cases h : c' = c <;> simp [h] <;> rfl

end Reps

variable (ch : Choice R)

theorem span_col_eq_cols (Φ : ch.G.Datum) :
    Submodule.span ℂ (ch.col '' {a | ch.Phi a = Φ}) = Cols ch.G ch.W.θ :=
  span_colOf_psi ch.W.θ_is ch.rp ch.e Φ

end GlobalTheory.RowTest

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped Pointwise TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Grid GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle GlobalTheory.ConstRatio

namespace GlobalTheory.DefSourceInt

theorem theta_integral_source_definite : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (ε : Bool) (S W : HSp D) (χS χW : (AE D)ˣ →* Circle) (ω : WRep S W) (μ : Measure (GA D S)) (𝓕 : Set (GA D S)) (f : WO S W → ℂ), IsWeil ψ ε S W χS χW ω → (∀ τ, (gramAt D S τ).PosDef) → μ.IsHaarMeasure → IsFundamentalDomain (GQ S) 𝓕 μ → IsThetaFunO ψ (sgn ε S) W f → (∀ h, IntegrableOn (fun g => thetaKO ω g h f) 𝓕 μ) ∧ (Continuous fun h => ∫ g in 𝓕, thetaKO ω g h f ∂μ) ∧ ∀ γ ∈ GQ W, ∀ h, ∫ g in 𝓕, thetaKO ω g (γ * h) f ∂μ = ∫ g in 𝓕, thetaKO ω g h f ∂μ := by
  intro D ψ ε S W χS χW ω μ 𝓕 f hω hpos hμ h𝓕 hf
  obtain ⟨C, hC, hcov⟩ := GlobalTheory.definite_unitary_cocompact S hpos
  obtain ⟨hcont, hinv⟩ := GlobalTheory.thetaKO_continuous_and_rat_invariant ψ (sgn ε S) W χS χW (WRep.toSgn ε ω) hω f hf
  have hK : ∀ g h, thetaKO ω g h f = thetaKO (WRep.toSgn ε ω) ((ofSgn ε S).symm g) h f := fun _ _ => rfl
  have hKc : Continuous fun p : GA D S × GA D W => thetaKO ω p.1 p.2 f :=
    (hcont.comp (((continuous_ofSgn_symm ε S).comp continuous_fst).prodMk continuous_snd)).congr fun p => (hK p.1 p.2).symm
  have hI : ∀ γ ∈ GQ S, ∀ γ' ∈ GQ W, ∀ g h, thetaKO ω (γ * g) (γ' * h) f = thetaKO ω g h f := by
    intro γ hγ γ' hγ' g h
    rw [hK, hK, map_mul]
    exact hinv _ (GlobalTheory.SquareComm.ofSgn_symm_mem_GQ ε hγ) γ' hγ' _ _
  have hIS : ∀ γ ∈ GQ S, ∀ g h, thetaKO ω (γ * g) h f = thetaKO ω g h f := fun γ hγ g h => by
    have := hI γ hγ 1 (one_mem _) g h
    rwa [one_mul] at this
  have hIW : ∀ γ ∈ GQ W, ∀ g h, thetaKO ω g (γ * h) f = thetaKO ω g h f := fun γ hγ g h => by
    have := hI 1 (one_mem _) γ hγ g h
    rwa [one_mul] at this
  obtain ⟨_, _, _, _, _, _, _⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D S
  obtain ⟨_, _, _, _, _, _, _⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D W
  refine ⟨fun h => ?_, ?_, fun γ hγ h => ?_⟩
  · exact GlobalTheory.CocompactIntegrable.integrableOn_fundamentalDomain S μ 𝓕 C hμ h𝓕 hC hcov _
      (hKc.comp (Continuous.prodMk_left h)) (fun γ hγ g => hIS γ hγ g h)
  · exact GlobalTheory.DefLiftCont.continuous_integral_of_cocompact (GQ S) μ 𝓕 C h𝓕 hC hcov
      (fun h g => thetaKO ω g h f) (hKc.comp continuous_swap) (fun γ hγ h g => hIS γ hγ g h)
  · have e : (fun g => thetaKO ω g (γ * h) f) = fun g => thetaKO ω g h f := funext fun g => hIW γ hγ g h
    exact congrArg (fun F : GA D S → ℂ => ∫ g in 𝓕, F g ∂μ) e

end GlobalTheory.DefSourceInt
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.fockCreation_preserves_fockVectors_two_frames : ∀ (D : D7) (V W : HSp D) (A : GlobalTheory.ChainFr.Fr V) (B : GlobalTheory.ChainFr.Fr W) (θ : InfFam D) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → IsInfFam θ → ∀ f, IsThetaFunO ψ V W f → ∀ (τ : D.what₂.Tau) (z : Matrix (Fin W.rank) (Fin V.rank) ℂ) (P : PolF D W.rank V.rank), ∃ Q : PolF D W.rank V.rank, crea (heisO ψ V W) θ τ (cplxO (A.cart τ) (B.cart τ)) z (GlobalTheory.ChainFr.ptF ψ θ A B f P) = GlobalTheory.ChainFr.ptF ψ θ A B f Q := by
  first | exact @GlobalTheory.FockCreaDir.crea_ptF | exact GlobalTheory.FockCreaDir.crea_ptF | (intros; apply GlobalTheory.FockCreaDir.crea_ptF <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.MixModel GlobalTheory.MixPer
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FlagModulus

variable {D : D7} {S S₀ : HSp D} {ρ : ℕ}

theorem wittHyperbolic_conj_smallerGroup_coords (d : HypDec S S₀ ρ) (h : GA D S₀) (u : GL (Fin ρ) (AE D)) (b : Mx D ρ S₀.rank)
    (c : skewA D ρ) : d.emb0 h * (d.levi u * (d.nB b * d.nC c)) * (d.emb0 h)⁻¹ =
      d.levi u * (d.nB (b ⬝ mt S₀ h⁻¹) * d.nC c) := by
  simp only [mul_assoc]
  rw [← mul_assoc (d.emb0 h) (d.levi u), d.wittHyperbolic_anisotropic_commute_levi h u, mul_assoc, ← mul_assoc (d.emb0 h) (d.nB b),
    d.wittHyperbolic_anisotropic_conj_nB b h, mul_assoc, ← mul_assoc (d.emb0 h) (d.nC c), d.wittHyperbolic_anisotropic_commute_nC c h, mul_assoc, mul_inv_cancel,
    mul_one]

theorem map_conj_smallerUnitary_flagUnipotent_haar : ∀ (D : D7) (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (ν : Measure (flagN d)),
    ν.IsHaarMeasure → ∀ h : GA D S₀,
      ν.map (fun n : flagN d => d.emb0 h * n.1 * (d.emb0 h)⁻¹) = ν.map Subtype.val := by
  intro D S S₀ ρ d ν hν h
  haveI : BorelSpace (GA D S) := ⟨rfl⟩
  haveI : BorelSpace (Mx D ρ S₀.rank) := ⟨rfl⟩
  obtain ⟨hlc, hsc, -, -⟩ := GlobalTheory.Mem.TrueRecord.top_NFlag S (isIsoSub_e d)
  obtain ⟨μ, lB, lC, hμ, hB, hC, sμ, sB, sC, hΦ, ν₀, hν₀, hmap⟩ := GlobalTheory.HaarCoords.haar_coords D S S₀ ρ d
  have hk : ν = Measure.haarScalarFactor ν ν₀ • ν₀ := Measure.isMulLeftInvariant_eq_smul ν ν₀
  have hconj : Measurable (fun g : GA D S => d.emb0 h * g * (d.emb0 h)⁻¹) :=
    ((continuous_const.mul continuous_id).mul continuous_const).measurable
  have hval : Measurable (Subtype.val : flagN d → GA D S) := measurable_subtype_coe
  have hf : Measurable (fun b : Mx D ρ S₀.rank => b ⬝ mt S₀ h⁻¹) :=
    (continuous_id.matrix_mul continuous_const).measurable
  have hT : Measurable (Prod.map (id : UX D ρ → UX D ρ)
      (Prod.map (fun b : Mx D ρ S₀.rank => b ⬝ mt S₀ h⁻¹) (id : skewA D ρ → skewA D ρ))) :=
    measurable_id.prodMap (hf.prodMap measurable_id)
  have key : ν₀.map (fun n : flagN d => d.emb0 h * n.1 * (d.emb0 h)⁻¹) = ν₀.map Subtype.val := by
    have e1 : (fun n : flagN d => d.emb0 h * n.1 * (d.emb0 h)⁻¹) =
        (fun g : GA D S => d.emb0 h * g * (d.emb0 h)⁻¹) ∘ Subtype.val := rfl
    rw [e1, ← Measure.map_map hconj hval, hmap, Measure.map_map hconj hΦ]
    have e2 : (fun g : GA D S => d.emb0 h * g * (d.emb0 h)⁻¹) ∘
        (fun p : UX D ρ × (Mx D ρ S₀.rank × skewA D ρ) => d.levi p.1.1 * (d.nB p.2.1 * d.nC p.2.2)) =
        (fun p : UX D ρ × (Mx D ρ S₀.rank × skewA D ρ) => d.levi p.1.1 * (d.nB p.2.1 * d.nC p.2.2)) ∘
          Prod.map (id : UX D ρ → UX D ρ)
            (Prod.map (fun b : Mx D ρ S₀.rank => b ⬝ mt S₀ h⁻¹) (id : skewA D ρ → skewA D ρ)) :=
      funext fun p => wittHyperbolic_conj_smallerGroup_coords d h p.1.1 p.2.1 p.2.2
    rw [e2, ← Measure.map_map hΦ hT]
    congr 1
    rw [← Measure.map_prod_map _ _ measurable_id (hf.prodMap measurable_id), ← Measure.map_prod_map _ _ hf measurable_id,
      Measure.map_id, Measure.map_id, GlobalTheory.AdelicModulus.RowMat.map_mul_mt_eq D S₀ ρ lB hB h⁻¹]
  rw [hk, Measure.map_smul, Measure.map_smul, key]
  · exact hval.aemeasurable
  · exact (hconj.comp hval).aemeasurable

end GlobalTheory.FlagModulus

end
end

section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.conjugate_theta_lift_matched_hecke_combination : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → ∀ gramR c0R c0L, GlobalTheory.GalLift.Comparison₂ R gramR c0R c0L → ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (c : CoefA (Vc D i)) (c₁ : VsV D i D.what₂.LL →ₛₗ[σ] c.W) (H : HMod (Bridge.Gf (Vc D i) → c.W)) (j : A.fam.amb.FL i A.μ0 →ₛₗ[σ] H.H), GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.OverK σ → GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.IsConjForms R i σ (c0L i) c c₁ H j → ∀ (μ' η' : (AE D)ˣ →* Circle) (th : H.H →ₗ[ℂ] (R.HW i σ).H), ∀ ω f₀ f B io thP, GlobalTheory.GalLift.LiftData R i σ μ' η' c H ω f₀ f B io thP → GlobalTheory.GalLift.IsProjOf R i σ thP th → ∀ P, GlobalTheory.Hk3.Good R A.μ0 P → GlobalTheory.Hk3.VacFix R.ψ ω P → ∀ cV cW, GlobalTheory.Hk3.Match R.ψ ω P (GlobalTheory.Hk3.dualC cV) cW → ∀ y y' : H.H, H.e y' = GlobalTheory.Hk3.hkF (Vc D i) P cV (H.e y) → (R.HW i σ).e (th y') = postOn (R.MW i σ) (GlobalTheory.Hk3.hk (Wc D i) P cW) ((R.HW i σ).e (th y)) := by
  first | exact @GlobalTheory.ConjLiftHecke.lift_match | exact GlobalTheory.ConjLiftHecke.lift_match | (intros; apply GlobalTheory.ConjLiftHecke.lift_match <;> assumption)
end
