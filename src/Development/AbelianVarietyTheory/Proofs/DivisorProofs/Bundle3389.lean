module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle077
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsActIffIsDiagEnd
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsWithoutCohomology
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2946
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3097
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3100
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3350
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLocalRingTrivSqZeroExt
public import Development.AbelianVarietyTheory.Definitions.Divisors.PullHlComp
public import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3383
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3215
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2936
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3301
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle007
import Development.AbelianVarietyTheory.Statements.PrincipalLattices.LogHermFormOfUnitDiscriminant
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2926
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2932
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3059
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommonFibre
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3128
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3130
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RosatiGeneratorComponentsTorusExtension
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3129
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3127
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3302
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle633
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3384
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2640
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3106
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle644
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3385
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2629
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle068
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3112
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle004
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle074

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section

namespace GlobalTheory.Poinc.Sep

theorem Tower.div_lam : ∀ g : ℕ, 1 ≤ g → ∀ n : ℕ, 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (Z : Scheme.{0}) (z : Z ⟶ Sp (cycAway n)) (i : F.X ⟶ Z) [IsOpenImmersion i], IsProjOver z → _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Z → i ≫ z = F.s → Dense (Set.range i) → ∀ W : Matrix (Fin 8) (Fin 8) ℤ, IsE8 W → ThetaInt F W i → ∀ (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), IsAct X₁ act → ∀ (𝔗 : Tower X₁ act) (z₂ : 𝔗.X₂.M.Z), 𝔗.p z₂ = z₁ → ∀ x₀ : X₁.S.Gam, X₁.M.Div X₁.S.th x₀ z₁ → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (m : ℕ) (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ X) (𝔪 : UMem X₁ z₁ act V ev X t δ), 𝔗.X₂.M.Div 𝔗.X₂.S.th (𝔗.lam x₀) z₂ := by
  intro g _ n _ _ F Z z i _ _ _ _ _ W _ _ X₁ z₁ act hact 𝔗 z₂ hz₂ x₀ hx V _ _ _ ev X _ m t δ _
  have hk : 0 < X₁.S.r * X₁.S.N := Nat.mul_pos X₁.S.r_pos (by have := X₁.S.N_ge; omega)
  have hdvd : X₁.S.r * X₁.S.N ∣ 𝔗.X₂.S.r * 𝔗.X₂.S.N := ⟨𝔗.d, 𝔗.lev⟩
  obtain ⟨a, ha, hdv⟩ := DivDeep.exists_div_torsion 𝔗.X₂ 𝔗.isAct z₂
    (X₁.S.N_ge.trans (Nat.le_mul_of_pos_left _ X₁.S.r_pos)) hdvd
  have hL : 0 < 𝔗.X₂.S.r * 𝔗.X₂.S.N := Nat.mul_pos 𝔗.X₂.S.r_pos (by have := 𝔗.X₂.S.N_ge; omega)
  choose x hxa using fun s => DivDeep.exists_eq_smul_of_smul_eq_zero hL hdvd (a s) (congrFun ha s)
  have hd : 𝔗.X₂.S.r * 𝔗.X₂.S.N / (X₁.S.r * X₁.S.N) = 𝔗.d := by
    rw [𝔗.lev]; exact Nat.mul_div_cancel_left _ hk
  rw [hd] at hxa
  obtain ⟨b, hb⟩ := 𝔗.lam_range x
  obtain rfl : 𝔗.lam b = a := hb.trans (funext hxa)
  obtain ⟨k, hk, e⟩ := DivDeep.same_ratio (GlobalTheory.T.thetaSetupTower_same_genericFibre_realisations g n F W Z i X₁ act hact 𝔗) x₀ b
  set φ := algebraMap X₁.Ω₁ 𝔗.X₂.Ω₁
  have h₁ : φ (X₁.S.th x₀) ≠ 0 := (map_ne_zero φ).2 hx.1
  have h₂ := hdv.1
  have h₃ : 𝔗.X₂.S.th (𝔗.lam x₀) * φ (X₁.S.th b) ≠ 0 := fun h => by
    rw [h, zero_pow hk.ne'] at e
    exact pow_ne_zero k (mul_ne_zero h₂ h₁) e.symm
  have h₄ := left_ne_zero_of_mul h₃
  have h₅ := right_ne_zero_of_mul h₃
  have hN : IsIntegrallyClosed (𝔗.X₂.M.O z₂) := RatModel.isIntegrallyClosed_O (fun z => by
    haveI := 𝔗.X₂.normal
    exact ⟨𝔗.X₂.normal.isDomain_stalk z, GlobalTheory.IsNormalScheme.isIntegrallyClosed_stalk z⟩) z₂
  have m₁ : 𝔗.X₂.S.th (𝔗.lam b) * φ (X₁.S.th x₀) / (𝔗.X₂.S.th (𝔗.lam x₀) * φ (X₁.S.th b)) ∈ 𝔗.X₂.M.O z₂ :=
    DivDeep.root_mem_O hN hk (by rw [div_pow, e, div_self (pow_ne_zero k (mul_ne_zero h₂ h₁))])
  have m₂ : φ (X₁.S.th b / X₁.S.th x₀) ∈ 𝔗.X₂.M.O z₂ := by
    obtain ⟨U, f, hU, hf⟩ := hx.2 b
    refine ⟨𝔗.p ⁻¹ᵁ U, 𝔗.p.app U f, show 𝔗.p z₂ ∈ U from hz₂ ▸ hU, ?_⟩
    refine (GlobalTheory.Points.valR_comp 𝔗.X₂.M.pt 𝔗.p U f).symm.trans ?_
    rw [𝔗.p_pt, ← hf]
    exact GlobalTheory.Points.valR_spMap_comp _ X₁.M.pt U (X₁.M.top_le_preimage_pt ⟨_, hU⟩) f
  refine ⟨h₄, fun j => ?_⟩
  have := mul_mem (hdv.2 j) (mul_mem m₁ m₂)
  convert this using 1
  rw [map_div₀]
  field_simp

end GlobalTheory.Poinc.Sep
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
noncomputable section
namespace GlobalTheory.Poinc.Sep.MkMember

theorem exists_uMem : ∀ g : ℕ, 1 ≤ g → ∀ n : ℕ, 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (Z : Scheme.{0}) (z : Z ⟶ Sp (cycAway n)) (i : F.X ⟶ Z) [IsOpenImmersion i], IsProjOver z → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Z → i ≫ z = F.s → Dense (Set.range i) → ∀ W : Matrix (Fin 8) (Fin 8) ℤ, IsE8 W → ThetaInt F W i → ∀ (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), IsAct X₁ act → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (Q : Data V) (m : ℕ) (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ Q.X), (∀ k, t k ≠ 0) → (∀ k a b, δ k a b = δ k b a) → (∀ k a, 0 ≤ δ k a a) → Q.IsMonomialTau t δ → ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁] (ρ : V →+* V₁), IsCN V₁ → Function.Injective ρ → ρ.Finite → ∀ (D₀ : DegData V₁ (maximalIdeal V₁)) (e₀ : D₀.toPre.X ≃+ Q.X), Refines Q ρ D₀.toPre e₀ → ∀ (G₀ : Over (Sp V₁)) [GrpObj G₀] [IsCommMonObj G₀] (A₀ : PolAV (Sp (FractionRing V₁))) (U₀ : Unif (maximalIdeal V₁) D₀ A₀ G₀) (y : Sp (FractionRing V₁) ⟶ F.X) (α : A₀.A.left ⟶ F.univ.A.left) (α₂ : (G2 A₀.A).left ⟶ (G2 F.univ.A).left), IsSemiAbelian G₀ → IsGrpPullback A₀.A F.univ.A y α → IsSquare α α₂ → LBIso (abelian₂ A₀.A A₀.L) (F.univ.P.pull α₂) → ∀ ev : X₁.M.Z.presheaf.stalk z₁ →+* V₁, IsLocalHom ev → RegAt X₁ z₁ ev → jK V₁ ≫ spMap ev ≫ X₁.M.Z.fromSpecStalk z₁ ≫ X₁.π = y ≫ i → ∃ 𝔪 : UMem X₁ z₁ act V₁ ev Q.X (fun k => ρ (t k)) δ, SharpRef W Q ρ 𝔪.D.toPre 𝔪.e₈ := by
  intro g hg n hn hodd F Z z i _ hproj hnorm hiz hdense W hW hTI X₁ z₁ act hact V _ _ _ Q m t δ ht hsym hnn hmono V₁ _ _ _ ρ hCN hρi hρf D₀ e₀ href G₀ _ _ A₀ U₀ y α α₂ hS hpb hsq hlb ev hloc hreg hcomm
  obtain ⟨yK, hyK, hy⟩ := GlobalTheory.T.thetaValuePoint_lies_over_moduliPoint g n F Z i W X₁ z₁ V₁ ev y hreg hcomm
  subst hy
  obtain ⟨A, φ, -, cart, hlbA⟩ := GlobalTheory.exists_isPolFibre GlobalTheory.polBaseChange_holds yK X₁.ρ.P
  obtain ⟨wl, hwl⟩ := LBIso.symm hlbA
  obtain ⟨c, hc, pr, hpr, huniv, hbun, hactc⟩ := hact
  obtain ⟨c', hc', pr', hpr', huniv', hbun', hlift⟩ := GlobalTheory.T.eighthPowerPresentation_endomorphisms_pullback g n (cycAway n) (zetaAway n) F W _ _ X₁.ρ.P A X₁.u (spMap yK) φ c hc pr hpr huniv hbun cart (LBIso.symm hlbA)
  have hsharp : SharpOver F W A (spMap yK ≫ X₁.u) := ⟨c', hc', pr', hpr', huniv', hbun'⟩
  obtain ⟨D, ⟨U⟩⟩ := GlobalTheory.T.uniformization_eighth_power_exists g n (cycAway n) (zetaAway n) F W hW V₁ hCN D₀ G₀ A₀ U₀ _ α α₂ hS hpb hsq hlb A hsharp
  have hS8 : IsSemiAbelian (powObj G₀ 8) := GlobalTheory.PowGrp.isSemiAbelian_pow _ _ _ 8 (powIsPowGrp G₀ 8) hS
  obtain ⟨e, hsr, heq⟩ := GlobalTheory.T.uniformisation_eighthPower_data_equivariant g n (cycAway n) (zetaAway n) F W hW V Q V₁ ρ hCN hρi hρf D₀ e₀ href G₀ A₀ U₀ _ α α₂ hS hpb hsq hlb A c' hc' pr' hpr' huniv' hbun' (powObj G₀ 8) hS8 D U
  refine ⟨{ cn := hCN, loc := hloc, reg := hreg, yK := yK, yK_eq := hyK, D := D, e₈ := e, G := powObj G₀ 8, semi := hS8, A := A, U := U, φ := φ, cart := cart, wl := wl, wl_gen := hwl, equiv := ?_, psi := ?_ }, hsr⟩
  · intro a a' h
    obtain ⟨aA, h1, h2⟩ := hlift (act a) (fun u v => a u v) (hactc a)
    obtain ⟨E, hE, hE2⟩ := heq a a' h aA h1
    exact ⟨E, hE ▸ h2, hE2⟩
  · exact GlobalTheory.T.eighthPower_trivialisation_eq_unit_mul_monomial W X₁.posW V V₁ Q ρ hρi m t δ hsym hnn ht hmono D.toPre e hsr

end GlobalTheory.Poinc.Sep.MkMember
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep

noncomputable section

theorem GlobalTheory.Poinc.Sep.twistSum_translate : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (x₀ : X₁.S.Gam), X₁.M.Div X₁.S.th x₀ z₁ → ∃ (sg : ℤˣ) (eps : X₁.S.Gam → X₁.S.Gam → ℕ), ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (m : ℕ) (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ X) (𝔪 : UMem X₁ z₁ act V ev X t δ) (C : Type) (lab : C → X₁.S.Gam), (∀ c, lab c ∈ X₁.S.HH X₁.M z₁) → ∀ T : (Fin 8 → X) → C → V, 𝔪.Terms x₀ lab T → ∀ (c : C), ∀ τ ∈ X₁.S.TT X₁.M z₁, ∀ zt h : X₁.M.Z.presheaf.stalk z₁, X₁.M.stalkHom z₁ zt = algebraMap X₁.o₁ X₁.Ω₁ (X₁.S.ζ ^ (X₁.S.r * X₁.S.N)) → X₁.M.stalkHom z₁ h = algebraMap X₁.o₁ X₁.Ω₁ (X₁.S.ζ ^ eps (lab c) τ) * X₁.S.th (lab c + τ) / X₁.S.th x₀ → ∀ wt : (Fin 8 → X) → ZMod (X₁.S.r * X₁.S.N), (∀ a mu, 𝔪.YY a mu → wt mu = (sg : ℤ) • eStd X₁.S.g _ τ a) → SumI (maximalIdeal V) (fun mu => ev zt ^ (wt mu).val * T mu c) (ev h) := by
  intro g n F W Z i X₁ z₁ act x₀ hdiv
  obtain ⟨sg, hsg, hweil⟩ := GlobalTheory.T.exists_thetaTwistedSum_sign_everyMember g n F W Z i X₁ z₁ act x₀ hdiv
  classical
  let Wit : X₁.S.Gam → X₁.S.Gam → ℕ → Prop := fun a τ e =>
    ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsLocalRing V) (ev : X₁.M.Z.presheaf.stalk z₁ →+* V)
      (X : Type) (_ : AddCommGroup X) (m : ℕ) (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ X)
      (𝔪 : UMem X₁ z₁ act V ev X t δ) (C : Type) (lab : C → X₁.S.Gam) (_ : ∀ c, lab c ∈ X₁.S.HH X₁.M z₁)
      (T : (Fin 8 → X) → C → V) (_ : 𝔪.Terms x₀ lab T) (c : C), lab c = a ∧
      TwistSum X₁ z₁ act x₀ 𝔪 lab T sg c τ e ∧
      ∃ r : X₁.M.Z.presheaf.stalk z₁, X₁.M.stalkHom z₁ r = X₁.S.th (lab c + τ) / X₁.S.th x₀ ∧ ev r ≠ 0
  refine ⟨sg, fun a τ => if h : ∃ e, Wit a τ e then h.choose else 0, ?_⟩
  intro V _ _ _ ev X _ m t δ 𝔪 C lab hlab T hT c τ hτ zt h hzt hh wt hwt
  obtain ⟨e₂, he₂⟩ := hsg V ev X m t δ 𝔪 C lab hlab T hT c τ hτ
  by_cases hW : ∃ e, Wit (lab c) τ e
  · beta_reduce at hh
    rw [dite_eq_left hW] at hh
    obtain ⟨V₁, _, _, _, ev₁, Y₁, _, m₁, t₁, δ₁, 𝔪₁, C₁, lab₁, hlab₁, T₁, hT₁, c₁, hc₁, hts, r, hr, hr0⟩ := hW.choose_spec
    have key := GlobalTheory.T.twistedThetaSum_zeta_exponent_independent_member g n F W Z i X₁ z₁ act x₀ hdiv sg hsg hweil V₁ ev₁ Y₁ m₁ t₁ δ₁ 𝔪₁ C₁ lab₁ hlab₁ T₁ hT₁ c₁
      V ev X m t δ 𝔪 C lab hlab T hT c hc₁ τ hτ _ e₂ hts he₂ ⟨r, hr, hr0⟩
    exact key zt h hzt hh wt hwt
  · beta_reduce at hh
    rw [dite_eq_right hW] at hh
    have hh' : X₁.M.stalkHom z₁ h = X₁.S.th (lab c + τ) / X₁.S.th x₀ := by rw [hh]; simp
    have hev : ev h = 0 := by
      by_contra hne
      exact hW ⟨e₂, V, inferInstance, inferInstance, inferInstance, ev, X, inferInstance, m, t, δ, 𝔪, C, lab, hlab, T, hT, c,
        rfl, he₂, h, hh', hne⟩
    obtain ⟨s, hs⟩ := exists_stalk_zeta X₁ z₁ (X₁.S.ζ ^ e₂)
    have := he₂ zt (s * h) hzt (by rw [map_mul, hs, hh', mul_div_assoc]) wt hwt
    rw [map_mul, hev, mul_zero] at this
    rwa [hev]
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham

attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
noncomputable section

namespace GlobalTheory.KSGraph

theorem connectedSpace_sp_dualNumber (k : Type) [Field k] : ConnectedSpace (Sp (DualNumber k)) := by
  change ConnectedSpace (PrimeSpectrum (DualNumber k))
  have : PreconnectedSpace (PrimeSpectrum (DualNumber k)) := by
    refine ⟨isPreconnected_of_forall (IsLocalRing.closedPoint (DualNumber k)) fun y _ ↦
      ⟨closure {y}, Set.subset_univ _, ?_, subset_closure rfl, isPreconnected_singleton.closure⟩⟩
    exact (IsLocalRing.specializes_closedPoint y).mem_closure
  exact ⟨inferInstance⟩

theorem exists_dim {k : Type} [Field k] (A' : Over (Sp (DualNumber k))) [GrpObj A']
    (hA' : IsAbelianScheme A') : ∃ g, SmoothOfRelativeDimension g A'.hom := by
  have := hA'.smooth
  have := hA'.geomConnected
  have := connectedSpace_sp_dualNumber k
  have : ConnectedSpace A'.left := GeometricallyConnected.connectedSpace A'.hom A'.hom.isOpenMap
  exact exists_dim_of_preconnected A'.hom (Classical.arbitrary _)

theorem isFilLift_iff_sub_mem : ∀ (k : Type) [Field k] (A₀ : Over (Sp k)) [GrpObj A₀] (A' : Over (Sp (DualNumber k))) [GrpObj A'] (i : A₀.left ⟶ A'.left) (h : IsGrpPullback A₀ A' (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) i), IsAbelianScheme A' → ∀ x ∈ Fil A₀, ∀ y y' : HdR A₀, IsFilLift h x y → (IsFilLift h x y' ↔ y' - y ∈ Fil A₀) := by
  intro k _ A₀ _ A' _ i h hA' x hx y y' hy
  obtain ⟨g, hg⟩ := exists_dim A' hA'
  have P := GlobalTheory.abelianDeRham
  have hA₀ : IsAbelianScheme A₀ := by
    have := hA'.comm
    have hc : IsCommMonObj A₀ := by
      rw [isCommMonObj_iff_isMulCommutative]
      intro T
      refine ⟨⟨fun x y => Over.OverMorphism.ext (h.1.hom_ext ?_ (by rw [Over.w, Over.w]))⟩⟩
      rw [← h.2 T x y (pushPt h.1.w x) (pushPt h.1.w y) rfl rfl,
        ← h.2 T y x (pushPt h.1.w y) (pushPt h.1.w x) rfl rfl, _root_.mul_comm]
    exact ⟨hc, MorphismProperty.of_isPullback (P := @Smooth) h.1 hA'.smooth,
      MorphismProperty.of_isPullback (P := @IsProper) h.1 hA'.proper,
      MorphismProperty.of_isPullback (P := @GeometricallyConnected) h.1 hA'.geomConnected⟩
  have g₀ := (smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback h.1 hg
  have hL := (P.2.1 k A₀ g hA₀ g₀).1
  have reg := ksRegular_of_isAbelianScheme P h hA' hg
  constructor
  · intro hy'
    obtain ⟨w, hw, -⟩ := hL.1 y
    obtain ⟨w', hw', -⟩ := hL.1 y'
    have e := (reg x hx).unique ⟨y, hy, hw⟩ ⟨y', hy', hw'⟩
    subst e
    exact hw'.sub_mem hw
  · intro hz
    obtain ⟨v, ⟨z, hz', -⟩, -⟩ := reg (y' - y) hz
    obtain ⟨d, hd, e⟩ := hy
    obtain ⟨d', hd', e'⟩ := hz'
    refine ⟨d + (TrivSqZeroExt.inr 1 : DualNumber k) • d', add_mem hd (Submodule.smul_mem _ _ hd'), fun c ↦ ?_⟩
    rw [LinearMap.add_apply, LinearMap.smul_apply, e, e', smul_eq_mul]
    ext <;> simp

end GlobalTheory.KSGraph
end
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

theorem _root_.GlobalTheory.T.tateTwistCohomology_laurent_absIntClosedLocalDomain : ∀ (q : ℕ) [NeZero q] (T : Type) [CommRing T] [IsDomain T] [IsLocalRing T], AIC T → IsUnit (q : T) → ∀ n i : ℤ, (2 ≤ n → Subsingleton (Ht q (sp (LaurentPolynomial T)) n i)) ∧ Nonempty (Ht q (sp (LaurentPolynomial T)) 1 i ≃+ ZMod q) := by
  first | (exact @GlobalTheory.EtC.GmAic.main) | (exact GlobalTheory.EtC.GmAic.main) | (intros; apply GlobalTheory.EtC.GmAic.main  <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

theorem _root_.GlobalTheory.T.etaleHomotopyInvariance_absIntClosedLocalDomain : ∀ (q : ℕ) [NeZero q] (T : Type) [CommRing T] [IsDomain T] [IsLocalRing T], AIC T → IsUnit (q : T) → ∀ i : ℤ, Eqv _ (spMap (Polynomial.C : T →+* Polynomial T)) (tw q i) := by
  first | (exact @GlobalTheory.EtC.HtpyLine.htpy_AIC) | (exact GlobalTheory.EtC.HtpyLine.htpy_AIC) | (intros; apply GlobalTheory.EtC.HtpyLine.htpy_AIC  <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

theorem _root_.GlobalTheory.T.extendsToSemiAbelian_away_of_charts : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] (f : R), f ≠ 0 → ∀ (A : Over (Sp (Localization.Away f))) [GrpObj A], IsAbelianScheme A → ∀ L : LB A.left, L.IsLB → RelAmple A L → (∀ x : Sp R, Nonempty (Chart (awayMap f) A x)) → HasExt (awayMap f) A := by
  first | exact @GlobalTheory.Desc.hasExt_awayMap_of_charts | exact GlobalTheory.Desc.hasExt_awayMap_of_charts | (intros; apply GlobalTheory.Desc.hasExt_awayMap_of_charts <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.thetaSetup_labelling_transport_galoisConjugate : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i), 1 ≤ g → 3 ≤ n → Odd n → IsOpenImmersion i → IsE8 W → ThetaInt F W i → IsProjOver X₁.M.s → ∀ (ε₁ : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), IsDiagEnd F W X₁.ρ.P X₁.u ε₁ → ∀ (D : Deep X₁ ε₁) (σ : D.X.Ω₁ ≃ₐ[X₁.Ω₁] D.X.Ω₁), ∀ (s : D.X.M.Z ⟶ D.X.M.Z), D.X.M.pt ≫ s = spMap (σ : D.X.Ω₁ →+* D.X.Ω₁) ≫ D.X.M.pt → ∀ a : D.X.S.Gam ≃+ D.X.S.Gam, D.GalLab σ a → ∀ (p : ℕ) [Fact p.Prime] (z₁ : X₁.M.Z) (c : CTrait X₁ p z₁) (y : Sp (OO p) ⟶ D.X.M.Z) (h : y ≫ D.q = c.y) (h' : (y ≫ s) ≫ D.q = c.y) (yy : D.X.S.Gam →+ ModN (D.X.S.r * D.X.S.N) (Fin 8 → c.T.D.toPre.X)), IsLab D.X D.ε (D.lift c y h) yy → IsLab D.X D.ε (D.lift c (y ≫ s) h') (yy.comp a.toAddMonoidHom) := by
  first | exact @GlobalTheory.Poinc.GalTrans.isLab_conj | exact GlobalTheory.Poinc.GalTrans.isLab_conj | (intros; apply GlobalTheory.Poinc.GalTrans.isLab_conj <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum GlobalTheory.MumFam

theorem _root_.GlobalTheory.T.uniformisedGroups_adjointHomPair_closedForm : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D₁ : DegData R (maximalIdeal R)) (A₁ : PolAV (Sp (FractionRing R))) (G₁ : Over (Sp R)) [GrpObj G₁] [IsCommMonObj G₁], IsSemiAbelian G₁ → ∀ (U₁ : Unif (maximalIdeal R) D₁ A₁ G₁) (D₂ : DegData R (maximalIdeal R)) (A₂ : PolAV (Sp (FractionRing R))) (G₂ : Over (Sp R)) [GrpObj G₂] [IsCommMonObj G₂], IsSemiAbelian G₂ → ∀ (U₂ : Unif (maximalIdeal R) D₂ A₂ G₂) (a : D₁.toPre.P.A ⟶ D₂.toPre.P.A) (a' : D₂.toPre.P.A ⟶ D₁.toPre.P.A) (h : D₁.toPre.X →+ D₂.toPre.X) (h' : D₂.toPre.X →+ D₁.toPre.X), Adj (pol D₁) (pol D₂) a a' h h' → ∃ (u : G₁ ⟶ G₂) (u' : G₂ ⟶ G₁), LinHom U₁.toUnifPre U₂.toUnifPre a h' u ∧ LinHom U₂.toUnifPre U₁.toUnifPre a' h u' ∧ GAdj U₁.LG.L U₂.LG.L u u' := by
  first | exact @GlobalTheory.MumAdj.adj_groups | exact GlobalTheory.MumAdj.adj_groups | (intros; apply GlobalTheory.MumAdj.adj_groups <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UPoinc.UGalTrans

theorem exists_lift_rat {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] [CharZero Ω] {R : Subalgebra o Ω}
    {P : PolAV (Sp R)} {G : Over (Sp (ratHull R))} [GrpObj G] {α : G.left ⟶ P.A.left}
    (hα : IsGrpPullback G P.A (spMap (toRat R)) α) {K : Type} [Field K] [CharZero K] (q : Sp K ⟶ P.A.left) :
    ∃ g : Sp K ⟶ G.left, g ≫ α = q := by
  obtain ⟨x', hx', -⟩ := existsUnique_ratPoint R (q ≫ P.A.hom)
  exact ⟨hα.1.lift q x' hx'.symm, hα.1.lift_fst _ _ _⟩


theorem isLab_conj : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (cf : Coeff l) (C : UCompact Xo cf), ∀ (X₁ : USetup C) (D : UDeep X₁) (σ : D.X.Ω₁ ≃ₐ[X₁.Ω₁] D.X.Ω₁) (s : D.X.M.Z ⟶ D.X.M.Z), D.X.M.pt ≫ s = spMap (σ : D.X.Ω₁ →+* D.X.Ω₁) ≫ D.X.M.pt → ∀ a : D.X.S.Gam ≃+ D.X.S.Gam, D.GalLab σ a → (∀ x, a (D.lab x) = D.lab x) → ∀ (p : ℕ) [Fact p.Prime] (z₁ : X₁.M.Z) (ct : UCTrait X₁ p z₁) (y : Sp (OO p) ⟶ D.X.M.Z) (h : y ≫ D.q = ct.y) (h' : (y ≫ s) ≫ D.q = ct.y) (yy : D.X.S.Gam →+ ModN (D.X.S.r * D.X.S.N) ct.T.P.D.toPre.X), UIsLab D.X (D.lift ct y h) yy → UIsLab D.X (D.lift ct (y ≫ s) h') (yy.comp a.toAddMonoidHom) := by
  intro E _ _ _ H Dw hpq l Xo cf C X₁ D σ s hs a hG _ p _ z₁ ct y h h' yy hy
  haveI : CharZero D.X.Ω₁ := D.X.ar.char
  obtain ⟨c₀, hc, R', fg, frac, hth, hev, ρ', u', hS, -, hu', hR, G, _, α, β, hα, hβ, hL, y₀, hy₀, u, lb, j, hq, hyy,
    hall⟩ := hy
  obtain ⟨wi, W₀, _, e, k₀, he, hk₀, heβ, htw⟩ :=
    GlobalTheory.T.exists_conj_universalTriple_identification E H Dw l Xo cf C X₁ D σ a hG c₀ hc R' fg frac hth hev ρ' u' hS hu' G _ α β hα hβ hL
  obtain ⟨yy₁, hW⟩ := GlobalTheory.T.exists_labels_unitaryClassicalTrait E H Dw hpq l Xo cf C D.X wi p _ (D.lift ct (y ≫ s) h')
  obtain ⟨c₁, hc₁, R'', fg₁, frac₁, hth₁, hev₁, ρ'', u'', hS₁, hi₁, hu₁, hR₁, G'', _, α'', β'', hα'', hβ'', hL'',
    ⟨m'', hm'', hmβ, hmt⟩, y₁, hy₁, u₁, lb₁, j₁, -, -, -⟩ := hW
  have hk'' : IsGrpPullback W₀ G'' (spMap ((σ : D.X.Ω₁ →+* D.X.Ω₁).comp (ratHull R'').val.toRingHom)) (e ≫ m'') :=
    (he.comp hm'').congr (GalTrans.sp_comp rfl) rfl
  have hββ : k₀ ≫ β = (e ≫ m'') ≫ β'' := by rw [Category.assoc, hmβ, heβ]
  obtain ⟨P₀, ka, ka', hka, hka', lka, lka', htor, hβeq⟩ := GlobalTheory.T.unitaryRechartings_common_geometricFibre E H Dw l Xo cf C D.X (σ : D.X.Ω₁ →+* D.X.Ω₁) s hs p
    (gPt p ≫ y) _ _ ρ' ρ'' hR (by rw [Category.assoc]; exact hR₁) y₀ y₁ hy₀ (by rw [Category.assoc]; exact hy₁) u u₁ u'
    u'' G _ α β G'' _ α'' β'' hα hβ hL hα'' hβ'' hL'' W₀ _ k₀ (e ≫ m'') hk₀ hk'' hββ
  obtain ⟨ee, hqe, hlab, hback⟩ := GalTrans.compare u u₁ lb lb₁ P₀ ka ka' hka hka' lka lka'
  have hrN : 1 ≤ D.X.S.r * D.X.S.N := Nat.mul_pos D.X.S.r_pos (by have := D.X.S.N_ge; omega)
  refine ⟨c₁, hc₁, R'', fg₁, frac₁, hth₁, hev₁, ρ'', u'', hS₁, hi₁, hu₁, hR₁, G'', _, α'', β'', hα'', hβ'', hL'', y₁, hy₁,
    u₁, lb₁, ee.symm.trans j, fun χ => ?_, fun x χ hχ => ?_, fun m A pk' pk₂' x' x₂' w w₂ hm hQ' hQ₂' hw hw₂ hA => ?_⟩
  · rw [← ee.apply_symm_apply χ, hqe, ee.apply_symm_apply]
    exact hq (ee.symm χ)
  · obtain ⟨w, hw1, hw2⟩ := hmt x
    obtain ⟨w₀, hw₀, hw₀e, hw₀k⟩ := htw x w hw1
    have c'' : w₀ ≫ (e ≫ m'') ≫ α'' =
        spMap ((σ : D.X.Ω₁ →+* D.X.Ω₁).comp R''.val.toRingHom) ≫ (ρ''.pt x).left := by
      rw [Category.assoc, reassoc_of% hw₀e, hw2, ← Category.assoc, GalTrans.sp_comp rfl]
    obtain ⟨v, xo, xo', hv, hva, hva', hx, hx'⟩ := htor (a x) x w₀ hw₀ hw₀k c''
    obtain ⟨pk, pk', hQ, hQ', hcm⟩ := hlab _ xo xo' v hrN
      (GlobalTheory.LabelTorsion.pow_eq_one_of_over_label _ ρ' p y₀ u _ xo hx)
      (GlobalTheory.LabelTorsion.pow_eq_one_of_over_label _ ρ'' p y₁ u₁ _ xo' hx') hv hva hva'
    refine (hyy (a x) pk.y (lb.yy_eq _ pk xo hQ hx)).trans (GalTrans.cm_mk ?_)
    have c2 : CongMod (D.X.S.r * D.X.S.N) χ pk'.y := GalTrans.cm_of_mk (hχ.symm.trans (lb₁.yy_eq x pk' xo' hQ' hx'))
    simpa using GalTrans.cm_symm (GalTrans.cm_map (ee.symm.trans j).toAddMonoidHom (GalTrans.cm_trans c2 hcm))
  · obtain ⟨pk, xo, vo, hQ, -, hvo, hvoa, hvoa', c1⟩ := hback m pk' x' hm hQ'
    obtain ⟨pk₂, xo₂, vo₂, hQ₂, -, hvo₂, hvo₂a, hvo₂a', c2⟩ := hback m pk₂' x₂' hm hQ₂'
    obtain ⟨g, hg⟩ := exists_lift_rat hα (xo.left ≫ u.φ)
    obtain ⟨g₂, hg₂⟩ := exists_lift_rat hα (xo₂.left ≫ u.φ)
    have e1 : g ≫ β = w ≫ β'' := hβeq vo g w hvo (by rw [hg, ← hvoa, Category.assoc])
      (by rw [hw, ← hvoa', Category.assoc])
    have e2 : g₂ ≫ β = w₂ ≫ β'' := hβeq vo₂ g₂ w₂ hvo₂ (by rw [hg₂, ← hvo₂a, Category.assoc])
      (by rw [hw₂, ← hvo₂a', Category.assoc])
    have hA' : g₂ ≫ β = g ≫ β ≫ (Xo.univ.t.act.act A).left := by
      rw [e2, hA, ← Category.assoc, ← e1, Category.assoc]
    have c3 := hall m A pk pk₂ xo xo₂ g g₂ hm hQ hQ₂ hg hg₂ hA'
    have c4 : CongMod m ((ee.symm.trans j) pk₂'.y) (j pk₂.y) := by
      have := GalTrans.cm_map (ee.symm.trans j).toAddMonoidHom c2
      rwa [show (ee.symm.trans j).toAddMonoidHom (ee pk₂.y) = j pk₂.y from
        congrArg j (ee.symm_apply_apply pk₂.y)] at this
    have c5 : CongMod m ((ee.symm.trans j) pk'.y) (j pk.y) := by
      have := GalTrans.cm_map (ee.symm.trans j).toAddMonoidHom c1
      rwa [show (ee.symm.trans j).toAddMonoidHom (ee pk.y) = j pk.y from
        congrArg j (ee.symm_apply_apply pk.y)] at this
    have c6 : CongMod m (A • j pk.y) (A • (ee.symm.trans j) pk'.y) :=
      GalTrans.cm_symm (GalTrans.cm_map (DistribSMul.toAddMonoidHom _ A) c5)
    exact GalTrans.cm_trans c4 (GalTrans.cm_trans c3 c6)

end GlobalTheory.UPoinc.UGalTrans
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_genericEndomorphism_mumford_ringAction : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal R) D A G) (O : Type) [Ring O] [StarRing O] [Module O D.toPre.X] (o : D.toPre.OAct O) (a : O), ∃ f : A.A ⟶ A.A, IsMonHom f ∧ ∀ g : G ⟶ G, IsMonHom g → (Over.pullback (jK R)).map g ≫ U.gen.hom = U.gen.hom ≫ f → ActsAs U.toUnifPre (o.onB.act a) (fun χ => star a • χ) g := by
  first | exact @GlobalTheory.Mum.GenericEnd.main | exact GlobalTheory.Mum.GenericEnd.main | (intros; apply GlobalTheory.Mum.GenericEnd.main <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES


theorem _root_.GlobalTheory.T.harrisTaylor_pullback_bundle_dual_hom : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (Y : Scheme.{0}) (s : Y ⟶ Sp R) (o : Obj b N s) (B : Over Y) [GrpObj B] [IsCommMonObj B] (ψ' : B ⟶ o.A), IsAbelianScheme B → IsMonHom ψ' → ∃ (C : Over Y) (_ : GrpObj C) (Q : LB (B ⊗ C).left) (h : B ⟶ C), IsAbelianScheme C ∧ GlobalTheory.AbDual.IsDual B C Q ∧ GlobalTheory.AbDual.IsAdditive (GlobalTheory.AbDual.swap Q) ∧ IsMonHom h ∧ LBIso (o.P.pull (ψ' ⊗ₘ ψ').left) (Q.pull (lift (fst B B) (snd B B ≫ h)).left) ∧ ∀ (T : Over Y) (x : T ⟶ B), PullPolTriv o ψ' x ↔ x ≫ h = 1 := by
  first | (exact @GlobalTheory.UPel.HT.ES.pullPol_dual_hom) | (exact GlobalTheory.UPel.HT.ES.pullPol_dual_hom) | (intros; apply GlobalTheory.UPel.HT.ES.pullPol_dual_hom  <;> assumption)
end
