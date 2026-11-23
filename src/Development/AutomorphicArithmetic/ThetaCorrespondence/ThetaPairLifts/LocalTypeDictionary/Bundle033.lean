module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle001
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.Bundle001
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1996
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2296
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle018
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteCoefficientBound
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.Bundle002
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.UnitCharTriangle
import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Mathlib.Tactic.TypeStar

@[expose] public section

section

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop GlobalTheory.SquareComm
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.DefIrred
theorem theta_vanish_all_of_irreducible : GlobalTheory.Published.HoweDualityReal → _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching → GlobalTheory.SquareSt.ThetaIntegralsAgree → ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ → ∀ (W W₁ X : HSp D) (A : GlobalTheory.ChainFr.Fr W) (A₁ : GlobalTheory.ChainFr.Fr W₁) (B : GlobalTheory.ChainFr.Fr X) (α β : (AE D)ˣ →* Circle), IsTriple W W₁ X α β → (∀ τ, Formalism.UG.HasSignature (gramAt D W τ) W.rank 0) → (∀ τ, Formalism.UG.HasSignature (gramAt D W₁ τ) W₁.rank 0) → (∀ τ, Formalism.UG.HasSignature (gramAt D X τ) X.rank 0) → ∀ (ν : Measure (GA D W)) (𝓕 : Set (GA D W)) (ν₁ : Measure (GA D W₁)) (𝓕₁ : Set (GA D W₁)), IsHaarFD W ν 𝓕 → IsHaarFD W₁ ν₁ 𝓕₁ → ∀ ωA ωB Pi rf rl p p', IsMatch ψ θ A A₁ B α β ωA ωB Pi rf rl p p' → ∀ Φ' ∈ algF ψ θ false A₁ B, p' Φ' ≠ 0 → thetaInt ωB ν₁ 𝓕₁ Φ' = 0 → ∀ Φ'' ∈ algF ψ θ false A₁ B, thetaInt ωB ν₁ 𝓕₁ Φ'' = 0 := by
  intro _ hP _ _ hTA D ψ θ hψ hθ W W₁ X A A₁ B α β hT _ hs₁ _ ν 𝓕 ν₁ 𝓕₁ hν hν₁ ωA ωB Pm rf rl p p' hm Φ₁ hΦ₁ hp₁ hz₁ Φ₂ hΦ₂
  set S := algF ψ θ false A₁ B with hSdef
  have hint := integrable_algF hψ hθ A₁ B hm.weilB hs₁ hν₁
  have tr : ∀ (Φ : WO W₁ X → ℂ) (g : GA D W₁) (h k : GA D X), thetaKO ωB g h (ωB (1, k) Φ) = thetaKO ωB g (h * k) Φ := by
    intro Φ g h k
    show (ωB (g, h) * ωB (1, k)) Φ 0 = _
    rw [← map_mul, Prod.mk_mul_mk, mul_one]
    rfl
  have tsub : ∀ Φ Ψ, (∀ h, IntegrableOn (fun g => thetaKO ωB g h Φ) 𝓕₁ ν₁) →
      (∀ h, IntegrableOn (fun g => thetaKO ωB g h Ψ) 𝓕₁ ν₁) →
      thetaInt ωB ν₁ 𝓕₁ (Φ - Ψ) = thetaInt ωB ν₁ 𝓕₁ Φ - thetaInt ωB ν₁ 𝓕₁ Ψ := by
    intro Φ Ψ hΦ hΨ; funext h
    have e : (fun g => thetaKO ωB g h (Φ - Ψ)) = fun g => thetaKO ωB g h Φ - thetaKO ωB g h Ψ := by
      funext g; simp [thetaKO, map_sub]
    simp only [thetaInt, Pi.sub_apply]
    rw [e]
    exact integral_sub (hΦ h) (hΨ h)
  have tadd : ∀ Φ Ψ, (∀ h, IntegrableOn (fun g => thetaKO ωB g h Φ) 𝓕₁ ν₁) →
      (∀ h, IntegrableOn (fun g => thetaKO ωB g h Ψ) 𝓕₁ ν₁) →
      thetaInt ωB ν₁ 𝓕₁ (Φ + Ψ) = thetaInt ωB ν₁ 𝓕₁ Φ + thetaInt ωB ν₁ 𝓕₁ Ψ := by
    intro Φ Ψ hΦ hΨ; funext h
    have e : (fun g => thetaKO ωB g h (Φ + Ψ)) = fun g => thetaKO ωB g h Φ + thetaKO ωB g h Ψ := by
      funext g; simp [thetaKO, map_add (f := _)]
    simp only [thetaInt, Pi.add_apply]
    rw [e]
    exact integral_add (hΦ h) (hΨ h)
  have tsmul : ∀ (c : ℂ) Φ, thetaInt ωB ν₁ 𝓕₁ (c • Φ) = c • thetaInt ωB ν₁ 𝓕₁ Φ := by
    intro c Φ; funext h
    have e : (fun g => thetaKO ωB g h (c • Φ)) = fun g => c * thetaKO ωB g h Φ := by
      funext g; simp [thetaKO, map_smul]
    simp only [thetaInt, Pi.smul_apply, smul_eq_mul]
    rw [e]
    exact integral_const_mul c _
  let Kint : Submodule ℂ (WO W₁ X → ℂ) :=
    { carrier := {Φ | (∀ h, IntegrableOn (fun g => thetaKO ωB g h Φ) 𝓕₁ ν₁) ∧ thetaInt ωB ν₁ 𝓕₁ Φ = 0}
      add_mem' := fun {a b} ha hb => ⟨fun h => by
          have e : (fun g => thetaKO ωB g h (a + b)) = fun g => thetaKO ωB g h a + thetaKO ωB g h b := by
            funext g; simp [thetaKO, map_add (f := _)]
          rw [e]; exact (ha.1 h).add (hb.1 h),
        by rw [tadd a b ha.1 hb.1, ha.2, hb.2, add_zero]⟩
      zero_mem' := ⟨fun h => by simp [thetaKO], by funext h; simp [thetaInt, thetaKO]⟩
      smul_mem' := fun c a ha => ⟨fun h => by
          have e : (fun g => thetaKO ωB g h (c • a)) = fun g => c * thetaKO ωB g h a := by
            funext g; simp [thetaKO, map_smul]
          rw [e]; exact (ha.1 h).const_mul c,
        by rw [tsmul, ha.2, smul_zero]⟩ }
  let K : Submodule ℂ (WO W₁ X → ℂ) := S ⊓ Kint
  obtain ⟨c, hc0, hc⟩ := hTA D ψ θ hθ W W₁ X A A₁ B α β hT ν 𝓕 ν₁ 𝓕₁ hν hν₁ ωA ωB Pm rf rl p p' hm
  have hrel := _root_.GlobalTheory.T.theta_integral_vanishes_on_finite_relations hP D ψ θ hψ hθ W₁ X A₁ B α (α / β) ωB hm.weilB hs₁ ν₁ 𝓕₁ hν₁
  have kerp' : finRel ωB S ≤ LinearMap.ker p' := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨u, hu, Ψ, hΨ, rfl⟩
    simp [map_sub, hm.mapB.invf u hu Ψ hΨ]
  have kill : ∀ Ψ ∈ S, p' Ψ = 0 → thetaInt ωB ν₁ 𝓕₁ Ψ = 0 := by
    intro Ψ hΨ hp0
    obtain ⟨Φ₀, hΦ₀, hd, -, hI⟩ := hc Ψ hΨ
    have hp00 : p' Φ₀ = 0 := by
      have := kerp' hd
      rw [LinearMap.mem_ker, map_sub, hp0, zero_sub, neg_eq_zero] at this
      exact this
    have h1 := hI 0 (zero_mem _) (by rw [map_zero, hp00])
    have h2 : thetaInt ωA ν 𝓕 0 = 0 := by funext h; simp [thetaInt, thetaKO]
    rw [h2] at h1
    have h3 : thetaInt ωB ν₁ 𝓕₁ Φ₀ = 0 := (smul_eq_zero.1 h1.symm).resolve_left hc0
    have h4 := hrel _ hd
    rw [tsub Ψ Φ₀ (hint Ψ hΨ) (hint Φ₀ hΦ₀), h3, sub_zero] at h4
    exact h4
  have stf : ∀ g ∈ GfC X, ∀ x ∈ K.map p', rf g x ∈ K.map p' := by
    rintro g hg _ ⟨Ψ, ⟨hΨS, hΨi, hΨ0⟩, rfl⟩
    refine ⟨ωB (1, g) Ψ, ⟨hm.mapB.stabX.1 g hg Ψ hΨS, fun h => ?_, ?_⟩, hm.mapB.eqf g hg Ψ hΨS⟩
    · simp only [tr]; exact hΨi (h * g)
    · funext h
      simp only [thetaInt, tr]
      exact congrFun hΨ0 (h * g)
  have stl : ∀ τ, ∀ Y ∈ lieAt X τ, ∀ x ∈ K.map p', rl τ Y x ∈ K.map p' := by
    rintro τ Y hY _ ⟨Ψ, ⟨hΨS, hΨi, hΨ0⟩, rfl⟩
    obtain ⟨Φ', hΦ'S, hder⟩ := hm.mapB.stabX.2 τ Y hY Ψ hΨS
    refine ⟨Φ', ⟨hΦ'S, ?_⟩, hm.mapB.eql τ Y hY Ψ hΨS Φ' hΦ'S hder⟩
    obtain ⟨V, hVfd, hV⟩ := GlobalTheory.T.oneParamSubgroup_fockOrbit_finiteDimensional D ψ θ hψ hθ W₁ X A₁ B α (α / β) ωB hm.weilB (fun τ => by
        obtain ⟨a, b, ha, hb, -⟩ := hT.gap τ
        exact ⟨a, a - b, ha, by rw [div_eq_mul_inv]; exact GlobalTheory.Chain.hasInfExp_div ha hb⟩)
      ‹_› τ Y hY Ψ hΨS
    set F : ℝ → (WO W₁ X → ℂ) := fun t => ωB (1, oneP θ X τ Y t) Ψ with hF
    set V' := Submodule.span ℂ (Set.range F) with hV'
    have hV'le : V' ≤ V := Submodule.span_le.2 (by rintro _ ⟨t, rfl⟩; exact hV t)
    haveI : FiniteDimensional ℂ V' := Submodule.finiteDimensional_of_le hV'le
    have hV'K : V' ≤ Kint := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨t, rfl⟩
      refine ⟨fun h => ?_, ?_⟩
      · simp only [hF, tr]; exact hΨi (h * oneP θ X τ Y t)
      · funext h
        simp only [thetaInt, hF, tr]
        exact congrFun hΨ0 (h * oneP θ X τ Y t)
    have hlim : Filter.Tendsto (fun s : ℝ => s⁻¹ • (F (0 + s) - F 0)) (nhdsWithin 0 {0}ᶜ) (nhds Φ') := by
      rw [tendsto_pi_nhds]
      intro z
      have := (hder z).tendsto_slope_zero
      simpa [hF] using this
    have hmem : ∀ s : ℝ, s⁻¹ • (F (0 + s) - F 0) ∈ V' := fun s =>
      V'.smul_of_tower_mem _ (V'.sub_mem (Submodule.subset_span ⟨0 + s, rfl⟩) (Submodule.subset_span ⟨0, rfl⟩))
    have hΦ'V : Φ' ∈ V' :=
      (Submodule.closed_of_finiteDimensional V').mem_of_tendsto hlim (Filter.Eventually.of_forall hmem)
    exact hV'K hΦ'V
  rcases hm.irred.2 (K.map p') stf stl with hbot | htop
  · exfalso
    have : p' Φ₁ ∈ K.map p' := ⟨Φ₁, ⟨hΦ₁, hint Φ₁ hΦ₁, hz₁⟩, rfl⟩
    rw [hbot, Submodule.mem_bot] at this
    exact hp₁ this
  · have : p' Φ₂ ∈ K.map p' := by rw [htop]; exact Submodule.mem_top
    obtain ⟨Ψ, ⟨hΨS, hΨi, hΨ0⟩, hΨp⟩ := this
    have h0 := kill (Φ₂ - Ψ) (S.sub_mem hΦ₂ hΨS) (by rw [map_sub, hΨp, sub_self])
    rw [tsub Φ₂ Ψ (hint Φ₂ hΦ₂) hΨi, hΨ0, sub_zero] at h0
    exact h0
end GlobalTheory.DefIrred
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop GlobalTheory.SquareComm
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.theta_lift_vanishes_of_irreducible_defect : GlobalTheory.Published.HoweDualityReal → _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching → GlobalTheory.SquareSt.ThetaIntegralsAgree → ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ → ∀ (W W₁ X : HSp D) (A : GlobalTheory.ChainFr.Fr W) (A₁ : GlobalTheory.ChainFr.Fr W₁) (B : GlobalTheory.ChainFr.Fr X) (α β : (AE D)ˣ →* Circle), IsTriple W W₁ X α β → (∀ τ, Formalism.UG.HasSignature (gramAt D W τ) W.rank 0) → (∀ τ, Formalism.UG.HasSignature (gramAt D W₁ τ) W₁.rank 0) → (∀ τ, Formalism.UG.HasSignature (gramAt D X τ) X.rank 0) → ∀ (ν : Measure (GA D W)) (𝓕 : Set (GA D W)) (ν₁ : Measure (GA D W₁)) (𝓕₁ : Set (GA D W₁)), IsHaarFD W ν 𝓕 → IsHaarFD W₁ ν₁ 𝓕₁ → ∀ ωA ωB Pi rf rl p p', IsMatch ψ θ A A₁ B α β ωA ωB Pi rf rl p p' → ∀ Φ' ∈ algF ψ θ false A₁ B, p' Φ' ≠ 0 → thetaInt ωB ν₁ 𝓕₁ Φ' = 0 → ∀ Φ'' ∈ algF ψ θ false A₁ B, thetaInt ωB ν₁ 𝓕₁ Φ'' = 0 := by
  first | exact @_root_.GlobalTheory.DefIrred.theta_vanish_all_of_irreducible | exact _root_.GlobalTheory.DefIrred.theta_vanish_all_of_irreducible | (intros; apply _root_.GlobalTheory.DefIrred.theta_vanish_all_of_irreducible <;> assumption)
end
end

section

section
namespace ResidueCardinalityNilpotence
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SplitFlip GlobalTheory.SplitWeil
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
namespace GlobalTheory.CompanionTheory.ResCardPlace
end GlobalTheory.CompanionTheory.ResCardPlace
end
section
open GlobalTheory.SumSize GlobalTheory.RowClaim
noncomputable section
namespace GlobalTheory.CompanionTheory.VolVal
open GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.RootEx GlobalTheory.FunObj ValuativeRel Matrix
section Unip
variable {k : Type*} [Field k] {ι : Type*} [Fintype ι] [DecidableEq ι]
end Unip
section Sym
variable {k : Type*} [Field k] {n : Type*} [Fintype n] [DecidableEq n] {c : ℕ}
end Sym
end GlobalTheory.CompanionTheory.VolVal
namespace GlobalTheory.CompanionTheory.VolVal
open GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.RootEx GlobalTheory.FunObj ValuativeRel Matrix
section Root
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {ι : Type} [Fintype ι] [DecidableEq ι]
variable {n : Type} [Fintype n] [DecidableEq n] {c : ℕ}
end Root
end GlobalTheory.CompanionTheory.VolVal
namespace GlobalTheory.CompanionTheory.VolVal
open GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.RootEx GlobalTheory.FunObj ValuativeRel Matrix
open Formalism.BasicNotions Formalism.L2.DIV IsDedekindDomain NumberField
open Formalism.DivisionValues (vw lw)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField GlobalTheory.FunObj.borelKw
  GlobalTheory.FunObj.borelSpaceKw
section Place
variable {D : D7}
end Place
end GlobalTheory.CompanionTheory.VolVal
namespace GlobalTheory.CompanionTheory.VolVal
open Formalism.DivisionValues (vw lw)
open IsDedekindDomain NumberField
section Val
variable {K : Type} [Field K] [NumberField K] [StarRing K]
end Val
end GlobalTheory.CompanionTheory.VolVal
namespace GlobalTheory.CompanionTheory.VolVal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.SumSize GlobalTheory.FunObj.AaCoef
open Formalism.DivisionValues (vw lw)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField GlobalTheory.FunObj.borelKw
  GlobalTheory.FunObj.borelSpaceKw
section Factors
variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc)
end Factors
end GlobalTheory.CompanionTheory.VolVal
namespace GlobalTheory.CompanionTheory.VolVal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.SumSize GlobalTheory.FunObj.AaCoef
open Formalism.DivisionValues (vw lw)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField GlobalTheory.FunObj.borelKw
  GlobalTheory.FunObj.borelSpaceKw
section Coef
variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}
end Coef
end GlobalTheory.CompanionTheory.VolVal
namespace GlobalTheory.CompanionTheory.VolVal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.SumSize GlobalTheory.FunObj.AaCoef
open Formalism.DivisionValues (vw lw)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField GlobalTheory.FunObj.borelKw
  GlobalTheory.FunObj.borelSpaceKw
section Loss
variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc)
end Loss
end GlobalTheory.CompanionTheory.VolVal
namespace GlobalTheory.CompanionTheory.VolVal
open Formalism.BasicNotions Formalism.L2.DIV
theorem finCoefK_alt : _root_.GlobalTheory.FunPr.ThetaLocalInputs → FinCoefK := by
  intro _
  refine ⟨0, fun CF _ => ⟨2, fun ε C hC => ⟨0, fun D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F s ch _ _ _ => ?_⟩⟩⟩
  have hL := s.core.lev
  have hde := Test.pde_ne_q s
  have hb : 1 ≤ large₂.sc.b := Real.one_le_exp (Real.rpow_nonneg (by linarith [large₂.sc.one_lt_alt]) _)
  have hf : 1 ≤ D.R.f := by
    have h1 : D.R.m ≤ D.R.f := D.R.m_le_f
    have h2 := D.R.two_le_m
    omega
  refine ⟨dlF ch.G, loss_dlF ch.G hC hb hf, fun t w hA Φ β hβ => ?_⟩
  have hq := coef_QL hL ch.S.toGridChoice t Φ hde (GlobalTheory.RowTest.guard_of_qGuard s.guard t) hA hβ
  refine ⟨((∏ v, (ch.S.term t Φ β v).coef : ℚ) : D.what₂.LL), ?_, ?_⟩
  · rw [map_ratCast]
    push_cast
    rfl
  · rcases hq with h | h
    · exact Or.inl (by rw [h]; simp)
    · exact Or.inr h
end GlobalTheory.CompanionTheory.VolVal
end
end
end ResidueCardinalityNilpotence
section
open GlobalTheory.SumSize GlobalTheory.RowClaim
theorem _root_.GlobalTheory.Adopt.finCoefK_of_theta_inputs : _root_.GlobalTheory.FunPr.ThetaLocalInputs → FinCoefK := by
  first | exact @_root_.ResidueCardinalityNilpotence.GlobalTheory.CompanionTheory.VolVal.finCoefK_alt | exact _root_.ResidueCardinalityNilpotence.GlobalTheory.CompanionTheory.VolVal.finCoefK_alt | (intros; apply _root_.ResidueCardinalityNilpotence.GlobalTheory.CompanionTheory.VolVal.finCoefK_alt <;> assumption)
end
end
end
