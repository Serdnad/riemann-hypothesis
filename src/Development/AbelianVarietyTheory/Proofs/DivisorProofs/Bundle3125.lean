module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2932
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3062
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2934
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3063
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2936
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RosatiAdjTensorPowerIntMatrixEndomorphism
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2939
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2680
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2833
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3023
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2955
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2959
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3065
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2964
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3064
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3066
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle001
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle068
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open GlobalTheory.Ex GlobalTheory.Mum.TensTor


theorem _root_.GlobalTheory.T.tensorTorusValueCorrespondence_period : ∀ (F : Type) [Field F] (N N' : NumD F) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (φ : N'.A → Fin r → N.A) (e : N'.X → Fin r → N.X) (wv : N'.A → F), TensFacts W φ e wv → ∀ y' : N'.X, GtRelV W φ e wv (N'.io y') (fun j => N.io (e y' j)) := by
  first | exact @GlobalTheory.Mum.TensTor.gtRelV_io | exact GlobalTheory.Mum.TensTor.gtRelV_io | (intros; apply GlobalTheory.Mum.TensTor.gtRelV_io <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open GlobalTheory.Ex GlobalTheory.Mum.TensTor


theorem _root_.GlobalTheory.T.tensorData_cubicalStructure_values : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D D' : DegData R (maximalIdeal R)) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (T : Tens D.toPre D'.toPre W) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (N N' : NumD F) (ν : NumOf D.toPre F N) (ν' : NumOf D'.toPre F N'), ∀ x y u, (N'.θ x y u : F) * wv T ν ν' (x * y * u) * wv T ν ν' x * wv T ν ν' y * wv T ν ν' u =
    ((∏ i, ∏ j, (N.θ (cmp T ν ν' x i * cmp T ν ν' x j) (cmp T ν ν' y i * cmp T ν ν' y j) (cmp T ν ν' u i * cmp T ν ν' u j) /
        (N.θ (cmp T ν ν' x i) (cmp T ν ν' y i) (cmp T ν ν' u i) * N.θ (cmp T ν ν' x j) (cmp T ν ν' y j) (cmp T ν ν' u j))) ^ W i j : Fˣ) : F) *
      wv T ν ν' (x * y) * wv T ν ν' (x * u) * wv T ν ν' (y * u) * wv T ν ν' 1 := by
  first | exact @GlobalTheory.Mum.TensCube.theta_tens | exact GlobalTheory.Mum.TensCube.theta_tens | (intros; apply GlobalTheory.Mum.TensCube.theta_tens <;> assumption)
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam

namespace GlobalTheory.MumFam


open AdjComp in
theorem Adj.of_twisted_comp : ∀ (R : Type) [CommRing R] [IsDomain R] (Q₁ Q₂ : Data R) (a : Q₁.B ⟶ Q₂.B) (a₁ a₁' : Q₁.B ⟶ Q₁.B) (a' : Q₂.B ⟶ Q₁.B) (h : Q₁.X →+ Q₂.X) (h₁ h₁' : Q₁.X →+ Q₁.X) (h' : Q₂.X →+ Q₁.X), IsMonHom a → IsMonHom a' → (∀ y, Q₂.c (h y) = Q₁.c y ≫ a) → (∀ z, Q₁.c (h' z) = Q₂.c z ≫ a') → Adj Q₁ Q₁ a₁ a₁' h₁ h₁' → (∃ w : LB.Iso (cubeLB Q₂.B ![fst Q₁.B Q₂.B ≫ a, snd Q₁.B Q₂.B] Q₂.M.L) (cubeLB Q₁.B ![fst Q₁.B Q₂.B ≫ a₁, snd Q₁.B Q₂.B ≫ a'] Q₁.M.L), w.IsGen ∧ ∀ y y' z J₁ J₂, Good Q₁.M.L z J₁ → Good Q₂.M.L z J₂ → val (Q₂.tau (h y) y') (𝟙 _) z J₂ = adjVal w (lift (toUnit (TK R) ≫ Q₁.c y) (toUnit (TK R) ≫ Q₂.c y')).left z J₁ J₂ * val (Q₁.tau (h₁ y) (h' y')) (𝟙 _) z J₁) → Adj Q₁ Q₂ a (a' ≫ a₁') h (h₁'.comp h') := by
  intro R _ _ Q₁ Q₂ a a₁ a₁' a' h h₁ h₁' h' ma ma' ca ca' H₁ H₂
  obtain ⟨mb, mb', cb, cb', w₁, g₁, V₁⟩ := H₁
  obtain ⟨w₂, g₂, V₂⟩ := H₂
  let m₂ : Q₁.B ⊗ Q₂.B ⟶ Q₁.B ⊗ Q₁.B := lift (fst _ _) (snd _ _ ≫ a')
  have xB : ∀ i, (![fst Q₁.B Q₂.B ≫ a₁, snd Q₁.B Q₂.B ≫ a'] : Fin 2 → _) i = m₂ ≫ (![fst Q₁.B Q₁.B ≫ a₁, snd Q₁.B Q₁.B] : Fin 2 → _) i := by
    intro i; fin_cases i <;> simp [m₂]
  have xC : ∀ i, (![fst Q₁.B Q₂.B, snd Q₁.B Q₂.B ≫ a' ≫ a₁'] : Fin 2 → _) i = m₂ ≫ (![fst Q₁.B Q₁.B, snd Q₁.B Q₁.B ≫ a₁'] : Fin 2 → _) i := by
    intro i; fin_cases i <;> simp [m₂]
  let cB := cubePull Q₁.M.L m₂ _ _ xB
  let cC := cubePull Q₁.M.L m₂ _ _ xC
  have lA : (cubeLB Q₂.B ![fst Q₁.B Q₂.B ≫ a, snd Q₁.B Q₂.B] Q₂.M.L).IsLB := DVR.linComb_isLB _ Q₂.M.isLB _ _
  have lB : (cubeLB Q₁.B ![fst Q₁.B Q₂.B ≫ a₁, snd Q₁.B Q₂.B ≫ a'] Q₁.M.L).IsLB := DVR.linComb_isLB _ Q₁.M.isLB _ _
  have lC : (cubeLB Q₁.B ![fst Q₁.B Q₂.B, snd Q₁.B Q₂.B ≫ a' ≫ a₁'] Q₁.M.L).IsLB := DVR.linComb_isLB _ Q₁.M.isLB _ _
  obtain ⟨w, gw, hw⟩ := exists_comp lA lB lC w₂ g₂ (pullIso cB cC w₁) (pullIso_isGen cB cC g₁)
  refine ⟨ma, inferInstance, ca, fun y => ?_, w, gw, fun y y' z J₁ J₂ hJ₁ hJ₂ => ?_⟩
  · rw [AddMonoidHom.comp_apply, cb', ca', Category.assoc]
  · have e₂ := V₂ y y' z J₁ J₂ hJ₁ hJ₂
    have e₁ := V₁ y (h' y') z J₁ J₁ hJ₁ hJ₁
    have hP : (lift (toUnit (TK R) ≫ Q₁.c y) (toUnit (TK R) ≫ Q₁.c (h' y'))).left =
        (lift (toUnit (TK R) ≫ Q₁.c y) (toUnit (TK R) ≫ Q₂.c y')).left ≫ m₂.left := by
      rw [← Over.comp_left, comp_lift, lift_fst, lift_snd_assoc, ca', Category.assoc]
    rw [hP] at e₁
    generalize (lift (toUnit (TK R) ≫ Q₁.c y) (toUnit (TK R) ≫ Q₂.c y')).left = P at e₂ e₁ ⊢
    have mC := Good.mem hJ₁ (fun I : ULift (Finset (Fin 2)) => (psum Q₁.B ![fst Q₁.B Q₂.B, snd Q₁.B Q₂.B ≫ a' ≫ a₁'] I.down).left) P
    have mB := Good.mem hJ₁ (fun I : ULift (Finset (Fin 2)) => (psum Q₁.B ![fst Q₁.B Q₂.B ≫ a₁, snd Q₁.B Q₂.B ≫ a'] I.down).left) P
    have mA := Good.mem hJ₂ (fun I : ULift (Finset (Fin 2)) => (psum Q₂.B ![fst Q₁.B Q₂.B ≫ a, snd Q₁.B Q₂.B] I.down).left) P
    have K : adjVal w P z J₁ J₂ = adjVal w₂ P z J₁ J₂ * adjVal w₁ (P ≫ m₂.left) z J₁ J₁ := by
      refine ((adjVal_of w P z J₁ J₂ _ _ (fun _ => rfl) (fun _ => rfl)).trans ((hw _ P z _ _ _ mC mB mA).trans
        (congrArg₂ (· * ·) (gm_pullIso cB cC w₁ P z (_, _) ⟨mC, mB⟩) rfl))).trans ?_
      rw [mul_comm]
      refine congrArg₂ (· * ·) (adjVal_of w₂ P z J₁ J₂ _ _ (fun _ => rfl) (fun _ => rfl)).symm
        (adjVal_of w₁ (P ≫ m₂.left) z J₁ J₁ _ _ (fun I => ?_) (fun I => ?_)).symm
      · show J₁ _ = J₁ _
        rw [Category.assoc, ← psum_left_pull m₂ _ _ xC I]
      · show J₁ _ = J₁ _
        rw [Category.assoc, ← psum_left_pull m₂ _ _ xB I]
    rw [AddMonoidHom.comp_apply, e₂, e₁, K]
    exact (_root_.mul_assoc _ _ _).symm

end GlobalTheory.MumFam
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.ZH GlobalTheory.UPoinc GlobalTheory.UCovSep
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.unitaryAction_baseChange_subalgebra : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (R R' : Subalgebra o Ω) (h : R ≤ R') (P : PolAV (Sp R)) (P' : PolAV (Sp R')) (φ : P'.A.left ⟶ P.A.left), IsGrpPullback P'.A P.A (spMap (Subalgebra.inclusion h).toRingHom) φ → LBIso P'.L (P.L.pull φ) → ∀ (act : 𝓞 E → (P.A ⟶ P.A)) (u : Sp (ratHull R) ⟶ Xo.XF c), (∀ a, IsMonHom (act a)) → GlobalTheory.UCovSep.UAct Xo c P act (toRat R) u → ∃ act' : 𝓞 E → (P'.A ⟶ P'.A), (∀ a, IsMonHom (act' a)) ∧ (∀ a, (act' a).left ≫ φ = φ ≫ (act a).left) ∧ GlobalTheory.UCovSep.UAct Xo c P' act' (toRat R') (spMap (Subalgebra.inclusion (ratHull_mono h)).toRingHom ≫ u) := by
  first | exact @GlobalTheory.UCovSep.uAct_baseChange | exact GlobalTheory.UCovSep.uAct_baseChange | (intros; apply GlobalTheory.UCovSep.uAct_baseChange <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.rosatiAdj_tensorPowerIntMatrixEndomorphism : ∀ (R : Type) [CommRing R] [IsDomain R] (D D' : DegPre R) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (T : Tens D D' W) (A A' : Matrix (Fin r) (Fin r) ℤ), A.transpose * (W + W.transpose) = (W + W.transpose) * A' → RosatiAdj D'.P.A D'.P.L (GlobalTheory.TensAct.matAct T A) (GlobalTheory.TensAct.matAct T A') := by
  first | exact @GlobalTheory.TensAct.rosatiAdj_matAct | exact GlobalTheory.TensAct.rosatiAdj_matAct | (intros; apply GlobalTheory.TensAct.rosatiAdj_matAct <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.UPoinc.USpread.noeth (o Ω : Type) [CommRing o] [IsNoetherianRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω)
    (z : M.Z) : IsNoetherianRing (M.O z) := by
  haveI := M.lft
  haveI : IsLocallyNoetherian M.Z := LocallyOfFiniteType.isLocallyNoetherian M.s
  exact isNoetherianRing_of_ringEquiv _ (M.stalkEquiv z)

theorem GlobalTheory.UPoinc.USpread.same_of_uSame {o Ω o' Ω' : Type} [CommRing o] [Field Ω] [Algebra o Ω] [CommRing o'] [Field Ω']
    [Algebra o' Ω'] {S : ThetaSys o Ω} {S' : ThetaSys o' Ω'} {ρ : S.Real} {ρ' : S'.Real} {lab : S.Gam → S'.Gam}
    {φ : Ω →+* Ω'} (h : USame ρ ρ' lab φ) :
    Same ρ (fun _ => 𝟙 _) ρ' (fun _ => 𝟙 _) lab φ := by
  obtain ⟨P₀, a, a', ha, ha', hL, hL', ht⟩ := h
  exact ⟨P₀, a, a', fun _ => 𝟙 _, ha, ha', hL, hL', fun _ => ⟨by simp, by simp⟩, ht⟩

theorem GlobalTheory.UPoinc.USpread.endo_id {R O : Type} [CommRing R] [CommRing O] [IsDomain O] (f : R →+* O)
    (hf : ∀ o : O, ∃ a b : R, f b ≠ 0 ∧ f b * o = f a) (σ : Sp O ⟶ Sp O) (h : σ ≫ spMap f = spMap f) : σ = 𝟙 _ := by
  obtain ⟨s, rfl⟩ := Spec.map_surjective σ
  rw [← Spec.map_comp] at h
  have h' := Spec.map_injective h
  have hs : ∀ r, s.hom (f r) = f r := fun r => congrArg (fun g => g.hom r) h'
  have : s = 𝟙 _ := by
    ext o
    obtain ⟨a, b, hb, e⟩ := hf o
    have e2 := congrArg s.hom e
    rw [map_mul, hs, hs, ← e] at e2
    exact mul_left_cancel₀ hb e2
  rw [this, Spec.map_id]

theorem GlobalTheory.UPoinc.USpread.sec {R₁ R₂ O M Γ : Type} [CommRing R₁] [CommRing R₂] [CommRing O] [IsDomain O] {P₁ : PolAV (Sp R₁)} {P₂ : PolAV (Sp R₂)} {f₁ : R₁ →+* O} {f₂ : R₂ →+* O} {e₁ : M → (P₁.A ⟶ P₁.A)} {e₂ : M → (P₂.A ⟶ P₂.A)} {t₁ : Γ → (baseOver (Sp R₁) ⟶ P₁.A)} {t₂ : Γ → (baseOver (Sp R₂) ⟶ P₂.A)}
    (hf : ∀ o : O, ∃ a b : R₁, f₁ b ≠ 0 ∧ f₁ b * o = f₁ a) (h : SameAt P₁ P₂ f₁ f₂ e₁ e₂ t₁ t₂) :
    ∃ (P : PolAV (Sp O)) (b₁ : P.A.left ⟶ P₁.A.left) (b₂ : P.A.left ⟶ P₂.A.left), IsGrpPullback P.A P₁.A (spMap f₁) b₁ ∧ IsGrpPullback P.A P₂.A (spMap f₂) b₂ ∧ LBIso P.L (P₁.L.pull b₁) ∧ LBIso P.L (P₂.L.pull b₂) ∧ (∀ E, ∃ e : P.A ⟶ P.A, e.left ≫ b₁ = b₁ ≫ (e₁ E).left ∧ e.left ≫ b₂ = b₂ ≫ (e₂ E).left) ∧ ∀ x, ∃ w : Sp O ⟶ P.A.left, w ≫ P.A.hom = 𝟙 _ ∧ w ≫ b₁ = spMap f₁ ≫ (t₁ x).left ∧ w ≫ b₂ = spMap f₂ ≫ (t₂ x).left := by
  obtain ⟨P, b₁, b₂, h₁, h₂, l₁, l₂, he, ht⟩ := h
  refine ⟨P, b₁, b₂, h₁, h₂, l₁, l₂, he, fun x => ?_⟩
  obtain ⟨w, w₁, w₂⟩ := ht x
  refine ⟨w, GlobalTheory.UPoinc.USpread.endo_id f₁ hf _ ?_, w₁, w₂⟩
  have := Over.w (t₁ x)
  rw [Category.assoc, ← h₁.1.w, ← Category.assoc, w₁, Category.assoc, this]
  exact Category.comp_id _

theorem GlobalTheory.UPoinc.USpread.main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (cf : Coeff l) (C : UCompact Xo cf) (X : USetup C) (p : ℕ) [Fact p.Prime] (z : X.M.Z) (ct : UCTrait X p z) (c₀ : X.Ω₁) (hc : c₀ ≠ 0) (R' : Subalgebra X.o₁ X.Ω₁) (fg : R'.FG) (frac : ∀ x : X.Ω₁, ∃ a ∈ R', ∃ b ∈ R', x = a / b) (hth : ∀ x, c₀ * X.S.th x ∈ R') (hev : ∀ x k, c₀ * X.S.ev x k ∈ R') (ρ' : (X.S.rechart c₀ hc R' fg frac hth hev).Real), USame X.ρ ρ' (fun x => x) (RingHom.id _) → R' ≤ X.M.O ((gPt p ≫ ct.y) (closedPoint (PadicAlgCl p))) → ∀ (y₀ : R' →+* PadicAlgCl p), (∀ a : R', y₀ a = X.M.val (gPt p ≫ ct.y) a) → ∀ (c₁ : X.Ω₁) (hc₁ : c₁ ≠ 0) (R'' : Subalgebra X.o₁ X.Ω₁) (fg₁ : R''.FG) (frac₁ : ∀ x : X.Ω₁, ∃ a ∈ R'', ∃ b ∈ R'', x = a / b) (hth₁ : ∀ x, c₁ * X.S.th x ∈ R'') (hev₁ : ∀ x k, c₁ * X.S.ev x k ∈ R'') (ρ'' : (X.S.rechart c₁ hc₁ R'' fg₁ frac₁ hth₁ hev₁).Real), USame X.ρ ρ'' (fun x => x) (RingHom.id _) → R'' ≤ X.M.O ((gPt p ≫ ct.y) (closedPoint (PadicAlgCl p))) → ∀ (y₁ : R'' →+* PadicAlgCl p), (∀ a : R'', y₁ a = X.M.val (gPt p ≫ ct.y) a) → ∀ (u : ρ'.UTest p y₀) (u' : ρ''.UTest p y₁), ∃ (P₀ : PolAV (Sp (PadicAlgCl p))) (a : P₀.A.left ⟶ u.A.A.left) (a' : P₀.A.left ⟶ u'.A.A.left), IsGrpPullback P₀.A u.A.A (spMap (algebraMap (FractionRing u.V) (PadicAlgCl p))) a ∧ IsGrpPullback P₀.A u'.A.A (spMap (algebraMap (FractionRing u'.V) (PadicAlgCl p))) a' ∧ LBIso P₀.L (u.A.L.pull a) ∧ LBIso P₀.L (u'.A.L.pull a') ∧ ∀ b : X.S.Gam, ∃ (w : Sp (PadicAlgCl p) ⟶ P₀.A.left) (x : TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A) (x' : TFK (R := u'.V) (PadicAlgCl p) ⟶ u'.A.A), w ≫ P₀.A.hom = 𝟙 _ ∧ w ≫ a = x.left ∧ w ≫ a' = x'.left ∧ x.left ≫ u.φ = spMap y₀ ≫ (ρ'.pt b).left ∧ x'.left ≫ u'.φ = spMap y₁ ≫ (ρ''.pt b).left := by
  intro E _ _ _ H Dw l Xo cf C X p _ z ct c₀ hc R' fg frac hth hev ρ' hS' hR' y₀ hy₀ c₁ hc₁ R'' fg₁ frac₁ hth₁ hev₁ ρ'' hS'' hR'' y₁ hy₁ u u'
  set z' := (gPt p ≫ ct.y) (closedPoint (PadicAlgCl p)) with hz'
  haveI : IsDedekindDomain X.o₁ := ArithBase.ded (Ω := X.Ω₁)
  haveI : IsNoetherianRing (X.M.O z') := GlobalTheory.UPoinc.USpread.noeth X.o₁ X.Ω₁ X.M z'
  haveI : IsIntegrallyClosed (X.M.Z.presheaf.stalk z') := X.normal.isIntegrallyClosed_stalk z'
  haveI : IsIntegrallyClosed (X.M.O z') := IsIntegrallyClosed.of_equiv (X.M.stalkEquiv z')
  let ι' : R' →+* X.M.O z' := (Subalgebra.inclusion hR').toRingHom
  let ι'' : R'' →+* X.M.O z' := (Subalgebra.inclusion hR'').toRingHom
  have h0 := GlobalTheory.T.realisations_common_generic_fibre_of_common_third _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (GlobalTheory.UPoinc.USpread.same_of_uSame hS') (GlobalTheory.UPoinc.USpread.same_of_uSame hS'')
  have h1 := GlobalTheory.T.sameAt_of_sameAt_comp_algebraMap (X.M.O z') X.Ω₁ _ _ _ _ _ _ ι' ι'' _ _ _ _ h0
  let v : X.M.O z' →+* PadicAlgCl p := RatModel.valHom (gPt p ≫ ct.y) z' (RatModel.range_eq_singleton _ _)
  have e₀ : v.comp ι' = y₀ := RingHom.ext fun a => (hy₀ a).symm
  have e₁ : v.comp ι'' = y₁ := RingHom.ext fun a => (hy₁ a).symm
  have hfr : ∀ o : X.M.O z', ∃ a b : R', ι' b ≠ 0 ∧ ι' b * o = ι' a := by
    intro o
    obtain ⟨a, ha, b, hb, e⟩ := frac (o : X.Ω₁)
    by_cases hb0 : b = 0
    · refine ⟨0, 1, by simp, ?_⟩
      have : o = 0 := Subtype.ext (by simpa [hb0] using e)
      simp [this]
    · refine ⟨⟨a, ha⟩, ⟨b, hb⟩, fun h => hb0 (congrArg Subtype.val h), Subtype.ext ?_⟩
      change b * (o : X.Ω₁) = a
      rw [e]; field_simp
  obtain ⟨P₀, a, a', ha, ha', hL, hL', ht, -⟩ := GlobalTheory.Poinc.Special.main _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (GlobalTheory.UPoinc.USpread.sec hfr h1) v u.yK u'.yK
    (u.fac.trans e₀.symm) (u'.fac.trans e₁.symm) u.A u'.A u.φ u'.φ u.cart u'.cart u.lb u'.lb
  refine ⟨P₀, a, a', ha, ha', hL, hL', fun b => ?_⟩
  obtain ⟨w, hw, h₁, h₂⟩ := ht b
  have q₁ : (w ≫ a) ≫ u.A.A.hom = jFK (R := u.V) (PadicAlgCl p) := by
    rw [Category.assoc, ha.1.w, ← Category.assoc, hw, Category.id_comp]
  have q₂ : (w ≫ a') ≫ u'.A.A.hom = jFK (R := u'.V) (PadicAlgCl p) := by
    rw [Category.assoc, ha'.1.w, ← Category.assoc, hw, Category.id_comp]
  refine ⟨w, Over.homMk (w ≫ a) q₁, Over.homMk (w ≫ a') q₂, hw, rfl, rfl, ?_, ?_⟩
  · simpa [e₀] using h₁
  · simpa [e₁] using h₂
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.unitaryTraitLabels_surjective_kernel : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (cf : Coeff l) (C : UCompact Xo cf), ∀ (X : USetup C) (p : ℕ) [Fact p.Prime] (z : X.M.Z) (ct : UCTrait X p z) (yy : X.S.Gam →+ ModN (X.S.r * X.S.N) ct.T.P.D.toPre.X), UIsLab X ct yy → Function.Surjective yy ∧ yy.ker = X.S.HH X.M z := by
  first | exact @GlobalTheory.UPoinc.uIsLab_onto_and_ker | exact GlobalTheory.UPoinc.uIsLab_onto_and_ker | (intros; apply GlobalTheory.UPoinc.uIsLab_onto_and_ker <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.isPullback_descentSquarePairToOpenSquare : ∀ {R : Type} [CommRing R] [IsLocalRing R] {S : Scheme.{0}} {π : S ⟶ Sp R} {G : Over S} (N : Near π G), IsPullback (DescKP.pairU N) (Desc.UT N ⊗ Desc.UT N).hom (N.U ⊗ N.U).hom (pullback.fst π π ≫ π) := by
  first | exact @GlobalTheory.Mum.DescKP.pairU_isPullback | exact GlobalTheory.Mum.DescKP.pairU_isPullback | (intros; apply GlobalTheory.Mum.DescKP.pairU_isPullback <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.nearOpen_sum_eq_embedding_descendedMultiplication : ∀ {R : Type} [CommRing R] [IsLocalRing R] {S : Scheme.{0}} {π : S ⟶ Sp R} {G : Over S} [GrpObj G] (N : Near π G) (V : (N.U ⊗ N.U).left.Opens) (m : V.toScheme ⟶ N.U.left) (hm : m ≫ N.U.hom = V.ι ≫ (N.U ⊗ N.U).hom), (∀ (T : Scheme.{0}) (v : T ⟶ V.toScheme) (s : T ⟶ S) (x y : Over.mk s ⟶ G), N.Pt s (v ≫ V.ι ≫ (fst N.U N.U).left) x.left → N.Pt s (v ≫ V.ι ≫ (snd N.U N.U).left) y.left → N.Pt s (v ≫ m) (x * y).left) → ∀ (p : pullback π π ⟶ S) (hp : p ≫ π = pullback.fst π π ≫ π), (DescKP.VT N V).ι ≫ (Desc.sum N p hp).left = DescKP.mT N V m hm ≫ (Desc.emb N p hp).left := by
  first | exact @GlobalTheory.Mum.DescKP.sum_eq_mT_emb | exact GlobalTheory.Mum.DescKP.sum_eq_mT_emb | (intros; apply GlobalTheory.Mum.DescKP.sum_eq_mT_emb <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory


theorem _root_.GlobalTheory.T.e8_prod_torsion_section_bound : ∀ (W : Matrix (Fin 8) (Fin 8) ℤ) (hW : IsE8 W) (gQ : ℕ) {S : Scheme.{0}} (A B : Over S) [GrpObj A] [IsCommMonObj A]
  [GrpObj B] [IsCommMonObj B] (pr : Fin 8 → (A ⟶ B)) (hP : E8Fibration.IsProd pr) (N : ℕ) {T : Over S}
  (b : Fin gQ ⊕ Fin gQ → (T ⟶ B)), (∀ c, b c ^ N = 1) → ∀ (_hN : 0 < N := by assumption),
  (∀ i, E8Fibration.Lab.ptOf hP b (E8Fibration.Lab.sharpBasis W hW.2 gQ (Pi.single i 1)) ^ N = 1) ∧
  ∀ (act : Fin 2 → (A ⟶ A)), (∀ i, E8Fibration.ActsBy pr (act i) (E8Fibration.actMat W i)) → ∀ (a : Fin 2) (i : Fin (2 * (8 * gQ))),
    E8Fibration.Lab.ptOf hP b (E8Fibration.Lab.sharpBasis W hW.2 gQ (Pi.single i 1)) ≫ act a =
      Out.linComb (fun i' => E8Fibration.Lab.ptOf hP b (E8Fibration.Lab.sharpBasis W hW.2 gQ (Pi.single i' 1)))
        (fun i' => ((E8Fibration.Lab.labMat W hW.2 gQ a i' i : ZMod N)).val) := by
  first | exact @GlobalTheory.Poinc.Sep.E8Fibration.Lab.ptOf_torsion_and_act | exact GlobalTheory.Poinc.Sep.E8Fibration.Lab.ptOf_torsion_and_act | (intros; apply GlobalTheory.Poinc.Sep.E8Fibration.Lab.ptOf_torsion_and_act <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum


theorem _root_.GlobalTheory.T.isUnit_rigidifiedValueAtOrigin : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegPre R) (k : ℕ) (α : D.X) (b : D.SecB k α) (v : R), OrigVal D b v → eSec D.P.A (closedPoint R) ∈ nonzeroLocus b → IsUnit v := by
  first | exact @GlobalTheory.Mum.isUnit_origVal | exact GlobalTheory.Mum.isUnit_origVal | (intros; apply GlobalTheory.Mum.isUnit_origVal <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum


theorem _root_.GlobalTheory.T.exists_rigidifiedValueAtOrigin : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegPre R) (k : ℕ) (α : D.X) (b : D.SecB k α), ∃ v : R, OrigVal D b v := by
  first | exact @GlobalTheory.Mum.exists_origVal | exact GlobalTheory.Mum.exists_origVal | (intros; apply GlobalTheory.Mum.exists_origVal <;> assumption)
end
