module

public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThickTransComp
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsIvDOfDefinite
public import Development.AbelianVarietyTheory.Definitions.Degenerations.NormNatCastPadicAlgClOfCoprime
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle006
public import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle013
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3370
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle018
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle019
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle066
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3203
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3360
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2998
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle035
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle002
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle042
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3367
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1858
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle336
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistFinitaryStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1735
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3210
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3369
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2639
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3016
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle043
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2926
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle063
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3104
import Mathlib.Tactic.Polynomial.Basic
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle016
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle546

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.FormalAlg GlobalTheory.Degen.FormalEmb

theorem _root_.GlobalTheory.T.lineBundleIso_algebraised_powers_compatible : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R), IsAdicComplete I R → ∀ (X : Over (Spec (CommRingCat.of R))), IsProper X.hom → ∀ (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left) (b : ∀ e, (Y e).left ⟶ X.left), (∀ e, IsPullback (b e) (Y e).hom X.hom (thick R I e)) → (∀ e, β e ≫ b (e + 1) = b e) → ∀ (N : ∀ e, LB (Y e).left) (v : ∀ e, LB.Iso (N e) ((N (e + 1)).pull (β e))), (∀ e, (N e).IsLB) → ∀ (p q : ℤ) (A A' : LB X.left), A.IsLB → A'.IsLB → ∀ (w : ∀ e, LB.Iso (GlobalTheory.AbLaw.pw (N e) p) (A.pull (b e))) (w' : ∀ e, LB.Iso (GlobalTheory.AbLaw.pw (N e) q) (A'.pull (b e))), (∀ e, (w e).IsGen ∧ (w' e).IsGen) → (∀ e z k l' l, b e z ∈ A.U k → β e z ∈ (N (e + 1)).U l' → z ∈ (N e).U l → Geo.Tor.gw (w e) (𝟙 _) z k l = Geo.Tor.gw (w (e + 1)) (β e) z k l' * Geo.Tor.gw (v e) (𝟙 _) z l' l ^ p) → (∀ e z k l' l, b e z ∈ A'.U k → β e z ∈ (N (e + 1)).U l' → z ∈ (N e).U l → Geo.Tor.gw (w' e) (𝟙 _) z k l = Geo.Tor.gw (w' (e + 1)) (β e) z k l' * Geo.Tor.gw (v e) (𝟙 _) z l' l ^ q) → LBIso (GlobalTheory.AbLaw.pw A q) (GlobalTheory.AbLaw.pw A' p) := by
  first | exact @GlobalTheory.FormalAlg.lbIso_pw_cross | exact GlobalTheory.FormalAlg.lbIso_pw_cross | (intros; apply GlobalTheory.FormalAlg.lbIso_pw_cross <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep

theorem _root_.GlobalTheory.T.exists_correction_properNormalCover_powerLocalEquation : ∀ (Z M S₁ : Scheme.{0}) [IsIntegral M] [IsIntegral S₁] (sM : M ⟶ Sp ℤ) (p₁ : S₁ ⟶ M) (g : M ⟶ Z) (J : Z.IdealSheafData), LocallyOfFiniteType sM → QuasiCompact sM → Flat (p₁ ≫ sM) → Geo.Tor.IsNormalScheme S₁ → IsProper p₁ → IsDominant p₁ → FinalTheorems.EffCartier (J.comap (p₁ ≫ g)) → ∀ (U₁ : S₁.Opens), (U₁ : Set S₁).Nonempty → ∀ (z₁ : M) (R : Type) [CommRing R] [IsLocalRing R] (ev : M.presheaf.stalk z₁ →+* R), IsLocalHom ev → ∀ ξ₁ : Sp R ⟶ S₁, ξ₁ ≫ p₁ = spMap ev ≫ M.fromSpecStalk z₁ → ∃ g₀ : R, idlAlong (J.comap (p₁ ≫ g)) ξ₁ = Ideal.span {g₀} ∧ ∀ D e : ℕ, ∃ e' : ℕ, ∀ f : M.presheaf.stalk z₁, (∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V], IsAdicComplete (maximalIdeal V) V → ∀ (ξ' : Sp V ⟶ S₁) (ev' : M.presheaf.stalk z₁ →+* V), IsLocalHom ev' → spMap ev' ≫ M.fromSpecStalk z₁ = ξ' ≫ p₁ → Set.range (jK V ≫ ξ') ⊆ (U₁ : Set S₁) → ev' f ∈ idlAlong (J.comap (p₁ ≫ g)) ξ' ^ D ⊔ ((maximalIdeal (M.presheaf.stalk z₁)).map ev') ^ e') → ∃ h ∈ (Scheme.stalkClosedPointTo ξ₁).hom.range, ev f - h * g₀ ^ D ∈ maximalIdeal R ^ e := by
  first | exact @GlobalTheory.CorrCover.exists_corr | exact GlobalTheory.CorrCover.exists_corr | (intros; apply GlobalTheory.CorrCover.exists_corr <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.Poinc.CNorm

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω]

theorem transport (S : ThetaSys o Ω) {T T' : AddSubgroup S.Gam} (h : T = T') (c : T →+ ZMod S.N)
    (c' : T' →+ ZMod S.N) (hc : ∀ t (h1 : t ∈ T) (h2 : t ∈ T'), c ⟨t, h1⟩ = c' ⟨t, h2⟩) :
    S.proj T c = S.proj T' c' ∧ ∀ k', ∃ k, S.FF T c k = S.FF T' c' k' := by
  subst h
  obtain rfl : c = c' := AddMonoidHom.ext fun t => hc t t.2 t.2
  exact ⟨rfl, fun k' => ⟨k', rfl⟩⟩

theorem mem_supI_iff_norm {S : ThetaSys o Ω} {M : RatModel o Ω} {U₀ : M.Z.Opens} (hO : S.Over₀ M U₀) {x : M.Z}
    {p : ℕ} [Fact p.Prime] {y : Sp (OO p) ⟶ M.Z} (hc : M.Cen U₀ x y) {y₀ : S.R →+* PadicAlgCl p}
    (hat : S.At M y y₀) (τ : S.Test p y₀) (a : S.Gam) :
    a ∈ S.supI M x ↔ ‖y₀ ⟨S.th a, S.th_mem a⟩‖ = τ.δ := by
  set w : Sp (PadicAlgCl p) := IsLocalRing.closedPoint _
  have hsp : ∀ w', (gPt p ≫ y) w' ⤳ (gPt p ≫ y) w :=
    RatModel.specializes_of_range_eq (RatModel.range_eq_singleton _ w)
  have hR : ∀ b ∈ S.R, b ∈ M.O ((gPt p ≫ y) w) := fun b hb =>
    RatModel.mem_ringOn.1 (hO.le hb) _ (hc.2 ⟨w, rfl⟩)
  have hOx : ∀ b ∈ M.O x, b ∈ M.O ((gPt p ≫ y) w) := fun b hb =>
    RatModel.O_le_of_specializes (RatModel.gPt_specializes hc.1 w) hb
  have hval : ∀ b (hb : b ∈ S.R), y₀ ⟨b, hb⟩ = M.val (gPt p ≫ y) b := fun b hb => hat ⟨b, hb⟩
  have key : ∀ a₁ ∈ S.supI M x, ∀ a', ‖y₀ ⟨S.th a', S.th_mem a'⟩‖ =
      ‖M.val (gPt p ≫ y) (S.th a' / S.th a₁)‖ * ‖y₀ ⟨S.th a₁, S.th_mem a₁⟩‖ := by
    intro a₁ h₁ a'
    rw [hval, hval, ← norm_mul, ← RatModel.val_mul hsp (hOx _ (h₁.2 a')) (hR _ (S.th_mem a₁)),
      div_mul_cancel₀ _ h₁.1]
  have hmax : ∀ a₁ ∈ S.supI M x, ‖y₀ ⟨S.th a₁, S.th_mem a₁⟩‖ = τ.δ := by
    intro a₁ h₁
    refine IsGreatest.unique (s := Set.range fun x => ‖y₀ ⟨S.th x, S.th_mem x⟩‖) ⟨⟨a₁, rfl⟩, ?_⟩ τ.δ_max
    rintro _ ⟨a', rfl⟩
    show ‖y₀ ⟨S.th a', S.th_mem a'⟩‖ ≤ _
    rw [key a₁ h₁ a']
    exact mul_le_of_le_one_left (norm_nonneg _) (hc.norm_val_le_one (h₁.2 a'))
  refine ⟨hmax a, fun h => ?_⟩
  obtain ⟨a₁, h₁⟩ := hO.div x
  have e := key a₁ h₁ a
  rw [h, hmax a₁ h₁] at e
  have h1 : ‖M.val (gPt p ≫ y) (S.th a / S.th a₁)‖ = 1 :=
    mul_right_cancel₀ τ.δ_pos.ne' (e.symm.trans (_root_.one_mul _).symm)
  exact (RatModel.Div.div_iff_isUnit h₁ a).2 ((RatModel.norm_val_eq_one_iff hc.1 (h₁.2 a)).1 h1)

theorem HH_eq {S : ThetaSys o Ω} {M : RatModel o Ω} {U₀ : M.Z.Opens} (hO : S.Over₀ M U₀) {x : M.Z}
    {p : ℕ} [Fact p.Prime] {y : Sp (OO p) ⟶ M.Z} (hc : M.Cen U₀ x y) {y₀ : S.R →+* PadicAlgCl p}
    (hat : S.At M y y₀) (τ : S.Test p y₀) : S.HH M x = τ.yy.ker := by
  rw [← τ.supp, ThetaSys.HH]
  congr 1
  ext a
  exact mem_supI_iff_norm hO hc hat τ a

theorem norm_val_div {S : ThetaSys o Ω} {M : RatModel o Ω} {U₀ : M.Z.Opens} (hO : S.Over₀ M U₀) {x : M.Z}
    {p : ℕ} [Fact p.Prime] {y : Sp (OO p) ⟶ M.Z} (hc : M.Cen U₀ x y) {y₀ : S.R →+* PadicAlgCl p}
    (hat : S.At M y y₀) {F : Ω} (hF : F ∈ S.R) {a : S.Gam} (ha : S.th a ≠ 0) :
    ‖M.val (gPt p ≫ y) (F / S.th a)‖ = ‖y₀ ⟨F, hF⟩‖ / ‖y₀ ⟨S.th a, S.th_mem a⟩‖ := by
  set w : Sp (PadicAlgCl p) := IsLocalRing.closedPoint _
  have hsp : ∀ w', (gPt p ≫ y) w' ⤳ (gPt p ≫ y) w :=
    RatModel.specializes_of_range_eq (RatModel.range_eq_singleton _ w)
  have hU : ∀ b ∈ M.ringOn U₀, b ∈ M.O ((gPt p ≫ y) w) := fun b hb =>
    RatModel.mem_ringOn.1 hb _ (hc.2 ⟨w, rfl⟩)
  have hth := hU _ (hO.le (S.th_mem a))
  have hinv := hU _ (hO.th_unit a ha)
  have hval : ∀ b (hb : b ∈ S.R), y₀ ⟨b, hb⟩ = M.val (gPt p ≫ y) b := fun b hb => hat ⟨b, hb⟩
  have e1 : M.val (gPt p ≫ y) (S.th a) * M.val (gPt p ≫ y) (S.th a)⁻¹ = 1 := by
    rw [← RatModel.val_mul hsp hth hinv, mul_inv_cancel₀ ha, RatModel.val_one]
  rw [div_eq_mul_inv, RatModel.val_mul hsp (hU _ (hO.le hF)) hinv, hval, hval, norm_mul, div_eq_mul_inv,
    eq_inv_of_mul_eq_one_right e1, norm_inv]

theorem norm_FF_le {S : ThetaSys o Ω} {p : ℕ} [Fact p.Prime] {y₀ : S.R →+* PadicAlgCl p} (τ : S.Test p y₀)
    {β : τ.X} (hβ : ∀ v0, τ.q β ≤ τ.q (β + S.N • v0)) {T : AddSubgroup S.Gam} (hT : T = S.perp τ.yy.ker)
    (c : T →+ ZMod S.N) (hc : ∀ t (h1 : t ∈ T) (h2 : t ∈ S.perp τ.yy.ker), c ⟨t, h1⟩ = τ.wt β ⟨t, h2⟩)
    (κ : S.J × (T → ZMod ((S.r * S.N) ^ 2))) :
    ‖y₀ ⟨S.FF T c κ, S.FF_mem T c κ⟩‖ ≤ τ.δ * Real.exp (-(τ.q β / S.N)) := by
  have hproj := (transport S hT c (τ.wt β) hc).1
  have := Fintype.ofFinite T
  rw [S.map_FF y₀ T c κ]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (mul_pos τ.δ_pos (Real.exp_pos _)).le
    fun t _ => ?_
  rw [norm_mul, norm_pow, S.norm_ζ, one_pow, _root_.one_mul, hproj]
  exact τ.le β hβ t (τ.perp_ker_le_ker (hT ▸ t.2)) κ.1

theorem main : ∀ (o' Ω : Type) [CommRing o'] [Field Ω] [Algebra o' Ω] [ArithBase o' Ω] (S : ThetaSys o' Ω) (ρ : S.Real), S.Big → ∀ (M : RatModel o' Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (FinalForm : ZHOut ρ M U₀ EE), S.admitted M U₀ → S.IsEE M U₀ EE → ∀ x : M.Z, IsClosed ({x} : Set M.Z) → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (j : M.Z.presheaf.stalk x →+* R), GlobalTheory.Mum.Base R → IsCpl j → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (gm : G.left ⟶ FinalForm.G.left), IsGrpPullback G FinalForm.G (spMap j ≫ M.Z.fromSpecStalk x) gm → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G), LBIso U.LG.L (FinalForm.L.L.pull gm) → (∀ y, PsiUnitOn D.toPre y ((spMap j ≫ M.Z.fromSpecStalk x) ⁻¹' abLocus FinalForm.G)) → S.IsoFree (S.TT M x) ∧ ∀ α₀ : D.toPre.X, ∃ c' : S.TT M x →+ ZMod S.N, ∀ (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z) (ev : R →+* OO p), M.Cen U₀ x y → spMap ev ≫ (spMap j ≫ M.Z.fromSpecStalk x) = y → ∀ x₀ ∈ S.supI M x, (∀ κ, ∃ α s, CongMod S.N α α₀ ∧ PsiCoord D.toPre α s ∧ ‖M.val (gPt p ≫ y) (S.FF (S.TT M x) c' κ / S.th x₀)‖ ^ S.N ≤ ‖(ev s : PadicAlgCl p)‖) ∧ ∃ κ, ∀ α s, CongMod S.N α α₀ → PsiCoord D.toPre α s → ‖(ev s : PadicAlgCl p)‖ ≤ ‖M.val (gPt p ≫ y) (S.FF (S.TT M x) c' κ / S.th x₀)‖ ^ S.N := by
  intro o' Ω _ _ _ _ S ρ hBig M U₀ EE FinalForm hAdm hEE x hx R _ _ _ j hBase hCpl G _ _ gm hpb D A U hLB hPsi
  obtain ⟨yy, H⟩ := GlobalTheory.T.complete_local_base_at_closed_point_group o' Ω S ρ hBig M U₀ EE FinalForm hAdm hEE x hx R j hBase hCpl G gm hpb D A U hLB hPsi
  have hO := hAdm.1
  obtain ⟨p₁, hp₁, y₁, hc₁⟩ := GlobalTheory.Poinc.exists_cen_main o' Ω M x hx U₀ hO.ne
  obtain ⟨V, _, _, _, ev₀, i, -, -, -, -, hcomp₁, -⟩ :=
    GlobalTheory.ClassicalPt.extend_completion o' Ω M x R j hCpl p₁ y₁ hc₁.1
  obtain ⟨y₀₁, hat₁, -⟩ := S.exists_at_of_cen M hO.le hc₁
  obtain ⟨τ₁, ε₁, -, hlab₁⟩ := H p₁ y₁ (i.comp ev₀) hc₁ hcomp₁ y₀₁ hat₁
  have hTT₁ : S.TT M x = S.perp τ₁.yy.ker := by rw [ThetaSys.TT, HH_eq hO hc₁ hat₁ τ₁]
  refine ⟨by rw [hTT₁]; exact τ₁.isoFree, fun α₀ => ?_⟩
  obtain ⟨a₀, ha₀⟩ := τ₁.yy_onto (QuotientAddGroup.mk (ε₁ α₀))
  have hya₀ : yy a₀ = QuotientAddGroup.mk α₀ := (hlab₁ a₀ α₀).2 ha₀
  let c' : S.TT M x →+ ZMod S.N :=
    { toFun := fun t => ZMod.castHom (dvd_mul_left S.N S.r) (ZMod S.N) (eStd S.g _ (t : S.Gam) a₀)
      map_zero' := by simp
      map_add' := fun t t' => by simp [eStd_add_left] }
  refine ⟨c', ?_⟩
  intro p _ y ev hc hcomp x₀ hx₀
  obtain ⟨y₀, hat, -⟩ := S.exists_at_of_cen M hO.le hc
  obtain ⟨τ, ε, hnorm, hlab⟩ := H p y ev hc hcomp y₀ hat
  have hTT : S.TT M x = S.perp τ.yy.ker := by rw [ThetaSys.TT, HH_eq hO hc hat τ]
  obtain ⟨v, hv⟩ := τ.exists_shortest (ε α₀)
  have hwt : ∀ t (h1 : t ∈ S.TT M x) (h2 : t ∈ S.perp τ.yy.ker),
      c' ⟨t, h1⟩ = τ.wt (ε α₀ + S.N • v) ⟨t, h2⟩ := by
    intro t h1 h2
    have hτa : τ.yy a₀ = QuotientAddGroup.mk (ε α₀) := (hlab a₀ α₀).1 hya₀
    rw [map_add (f := _), τ.wt_nsmul, add_zero, τ.wt_eq a₀ (ε α₀) hτa]
    rfl
  have hqβ : ∀ α', CongMod S.N α' α₀ → τ.q (ε α₀ + S.N • v) ≤ τ.q (ε α') := by
    rintro α' ⟨w', rfl⟩
    have e : ε (α₀ + S.N • w') = ε α₀ + S.N • v + S.N • (ε w' - v) := by
      rw [map_add (f := _), map_nsmul, smul_sub]
      abel
    rw [e]
    exact hv _
  have hα : CongMod S.N (ε.symm (ε α₀ + S.N • v)) α₀ :=
    ⟨ε.symm v, by rw [map_add (f := _), map_nsmul, AddEquiv.symm_apply_apply]⟩
  obtain ⟨s, hs⟩ := (GlobalTheory.PeriodFormCompare.exists_psiCoord_iff D.toPre (ε.symm (ε α₀ + S.N • v))).2
    (GlobalTheory.PeriodFormCompare.psiIn_top D _)
  have hsn : ‖(ev s : PadicAlgCl p)‖ = Real.exp (-τ.q (ε α₀ + S.N • v)) := by
    rw [hnorm _ s hs, AddEquiv.apply_symm_apply]
  have hN : (S.N : ℝ) ≠ 0 := by have := S.N_ge; positivity
  have hexp : Real.exp (-(τ.q (ε α₀ + S.N • v) / S.N)) ^ S.N = Real.exp (-τ.q (ε α₀ + S.N • v)) := by
    rw [← Real.exp_nat_mul]
    congr 1
    field_simp
  have hδ : ‖y₀ ⟨S.th x₀, S.th_mem x₀⟩‖ = τ.δ := (mem_supI_iff_norm hO hc hat τ x₀).1 hx₀
  refine ⟨fun κ => ⟨_, s, hα, hs, ?_⟩, ?_⟩
  · rw [norm_val_div hO hc hat (S.FF_mem _ c' κ) hx₀.1, hδ, hsn, ← hexp]
    refine pow_le_pow_left₀ (div_nonneg (norm_nonneg _) τ.δ_pos.le) ?_ _
    rw [div_le_iff₀ τ.δ_pos, mul_comm]
    exact norm_FF_le τ hv hTT c' hwt κ
  · obtain ⟨k, hk, hkeq⟩ := τ.eq _ hv
    obtain ⟨κ, hκ⟩ := (transport S hTT c' _ hwt).2 k
    refine ⟨κ, fun α' s' hα' hs' => ?_⟩
    have e : ‖M.val (gPt p ≫ y) (S.FF (S.TT M x) c' κ / S.th x₀)‖ ^ S.N =
        Real.exp (-τ.q (ε α₀ + S.N • v)) := by
      rw [norm_val_div hO hc hat (S.FF_mem _ c' κ) hx₀.1, hδ,
        show (⟨S.FF (S.TT M x) c' κ, S.FF_mem _ c' κ⟩ : S.R) = ⟨_, hk⟩ from Subtype.ext hκ, hkeq,
        mul_div_cancel_left₀ _ τ.δ_pos.ne', hexp]
    rw [e, hnorm α' s' hs']
    exact Real.exp_le_exp.2 (neg_le_neg (hqβ α' hα'))

end GlobalTheory.Poinc.CNorm
end
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC TensorProduct

noncomputable section

namespace GlobalTheory.EtC.LineAcyc

theorem spMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  dsimp only [spMap]
  rw [CommRingCat.ofHom_comp, Spec.map_comp, Functor.map_comp]

theorem spMap_id' (A : Type) [CommRing A] : spMap (RingHom.id A) = 𝟙 (sp A) := by
  dsimp only [spMap]
  rw [CommRingCat.ofHom_id, Spec.map_id]
  exact sch.map_id _

theorem pull_bijective_of_ringEquiv {A B : Type} [CommRing A] [CommRing B] (e : A ≃+* B)
    (R : Type) [CommRing R] (F : Shv R) (n : ℤ) :
    Function.Bijective (pull R (spMap (e : A →+* B)) F n) := by
  have h1 : ∀ x, pull R (spMap (e.symm : B →+* A)) F n (pull R (spMap (e : A →+* B)) F n x) = x := by
    intro x
    rw [← pull_comp, ← spMap_comp', show ((e.symm : B →+* A).comp (e : A →+* B)) = RingHom.id A by
      ext; simp, spMap_id', pull_id]
  have h2 : ∀ x, pull R (spMap (e : A →+* B)) F n (pull R (spMap (e.symm : B →+* A)) F n x) = x := by
    intro x
    rw [← pull_comp, ← spMap_comp', show ((e : A →+* B).comp (e.symm : B →+* A)) = RingHom.id B by
      ext; simp, spMap_id', pull_id]
  exact ⟨Function.LeftInverse.injective h1, Function.RightInverse.surjective h2⟩

theorem eqv_of_square {X Y X' Y' : Type} [CommRing X] [CommRing Y] [CommRing X'] [CommRing Y']
    (g : X →+* Y) (g' : X' →+* Y') (eX : X ≃+* X') (eY : Y ≃+* Y')
    (h : (eY : Y →+* Y').comp g = g'.comp (eX : X →+* X')) {R : Type} [CommRing R] (F : Shv R) :
    Eqv R (spMap g') F → Eqv R (spMap g) F := by
  intro hg' n
  have hc : spMap (eY : Y →+* Y') ≫ spMap g = spMap g' ≫ spMap (eX : X →+* X') := by
    rw [← spMap_comp', ← spMap_comp', h]
  have key : (pull R (spMap (eY : Y →+* Y')) F n) ∘ (pull R (spMap g) F n) =
      (pull R (spMap g') F n) ∘ (pull R (spMap (eX : X →+* X')) F n) := by
    funext x
    simp only [Function.comp_apply]
    rw [← pull_comp, ← pull_comp, hc]
  have hY := pull_bijective_of_ringEquiv eY R F n
  have hX := pull_bijective_of_ringEquiv eX R F n
  refine (Function.Bijective.of_comp_iff' hY _).mp ?_
  rw [key]
  exact (hg' n).comp hX

end GlobalTheory.EtC.LineAcyc

namespace GlobalTheory.EtC.LineAcyc

theorem affineLine_localAcyclicity_of_strictHenselian_points (core : ∀ (q : ℕ) [NeZero q] (T : Type) [CommRing T] [IsDomain T] [IsLocalRing T], AIC T → IsUnit (q : T) →
    ∀ (O : Type) [CommRing O] [Algebra (Polynomial T) O] [Algebra T O] [IsScalarTower T (Polynomial T) O],
    SH O → IndEt (Polynomial T) O → ∀ i : ℤ,
    Eqv _ (spMap (Algebra.TensorProduct.includeRight (R := T) (A := FractionRing T) (B := O)).toRingHom) (tw q i)) : C3 := by
  intro q _ T _ _ _ hT hq B _ _ _ _ _ i

  have hB := GlobalTheory.T.etaleCohomology_local_to_global_ringMap_indEtale (ZMod q) (tw q i) (GlobalTheory.T.tateTwist_finitary q i) B B (B ⊗[T] FractionRing T)
    (Algebra.ofId B (B ⊗[T] FractionRing T))

  refine eqv_of_square _ (Algebra.ofId B (B ⊗[T] FractionRing T)).toRingHom (RingEquiv.refl B)
    (Algebra.TensorProduct.comm T (FractionRing T) B).toRingEquiv ?_ _ (hB ?_)
  · ext b
    simp [Algebra.TensorProduct.algebraMap_apply]
  intro O _ _ hO hOi
  letI : Algebra (Polynomial T) O := ((algebraMap B O).comp (algebraMap (Polynomial T) B)).toAlgebra
  letI : Algebra T O := ((algebraMap B O).comp (algebraMap T B)).toAlgebra
  haveI : IsScalarTower T (Polynomial T) O := IsScalarTower.of_algebraMap_eq fun x => by
    show algebraMap B O (algebraMap T B x) = algebraMap B O (algebraMap (Polynomial T) B (algebraMap T (Polynomial T) x))
    rw [IsScalarTower.algebraMap_apply T (Polynomial T) B x]
  haveI : IsScalarTower T B O := IsScalarTower.of_algebraMap_eq fun x => rfl
  have hOi' : IndEt (Polynomial T) O :=
    isIndEtale_comp_etale (algebraMap (Polynomial T) B) (RingHom.etale_algebraMap.2 inferInstance)
      (algebraMap B O) hOi
  have hc := core q T hT hq O hO hOi' i
  refine eqv_of_square _ _ (Algebra.TensorProduct.rid B B O).toRingEquiv
    ((Algebra.TensorProduct.cancelBaseChange T B B O (FractionRing T)).toRingEquiv.trans
      (Algebra.TensorProduct.comm T O (FractionRing T)).toRingEquiv) ?_ _ hc
  refine RingHom.ext fun x => ?_
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul o b => simp [Algebra.smul_def]
  | add x y hx hy => simp only [map_add (f := _)] at hx hy ⊢; rw [hx, hy]

end GlobalTheory.EtC.LineAcyc

namespace GlobalTheory.EtC.LineAcyc

theorem c3 : C3 := affineLine_localAcyclicity_of_strictHenselian_points GlobalTheory.T.etaleCohomology_equiv_strictHenselian_line_point

end GlobalTheory.EtC.LineAcyc
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj

namespace GlobalTheory.HomFixAff

theorem exists_homFixRep_finiteType : ∀ (Rg : Type) [CommRing Rg] [IsNoetherianRing Rg] (A B : Over (Sp Rg)) [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B] (L : LB A.left) (M : LB B.left), IsAbelianScheme A → IsAbelianScheme B → L.IsLB → M.IsLB → Out.Rigidified A L → Out.Rigidified B M → Out.RelAmple A L → Out.RelAmple B M → ∃ R : HomFixRep A B L M, QuasiCompact R.π ∧ IsSeparated R.π ∧ LocallyOfFiniteType R.π := by
  intro Rg _ _ A B _ _ _ _ L M hA hB hL hM rL rM aL aM
  have h := fun p => GlobalTheory.T.exists_local_representing_scheme_homFixedPullback Rg A B L M hA hB hL hM rL rM aL aM p
  choose U hpU hdat using h
  exact GlobalTheory.T.homFixedPullbackRepresentable_glue_openCover (Sp Rg) A B L M hA hB hL hM rL rM (Sp Rg) U (fun p => ⟨p, hpU p⟩) hdat

end GlobalTheory.HomFixAff
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem formalEnd_algebraic : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∀ (a a' : D.toPre.P.A ⟶ D.toPre.P.A) (h h' : D.toPre.X →+ D.toPre.X), EndData D.toPre a a' h h' → ∀ b, FormalEnd U.toUnifPre a h' b → ∃ g : G ⟶ G, IsMonHom g ∧ ∀ e, (Over.pullback (thick R (maximalIdeal R) e)).map g = b e := by
  intro R _ _ _ hR D A G _ _ hG U a a' h h' hE b hb
  obtain ⟨N, hN, S, hS, hnd⟩ := GlobalTheory.T.mumford_thickening_endomorphism_maps_sections R hR D A G hG U a a' h h' hE b hb
  obtain ⟨φ, hφ, hgen⟩ := GlobalTheory.T.exists_genericFibreHom_of_formalSectionRatios R hR D A G hG U a a' h h' hE b hb N S hN hS hnd
  have := hR.1.1
  have := hR.1.2.2.1
  obtain ⟨g, hg, hgφ⟩ := GlobalTheory.T.semiAbelian_genericFibre_hom_extends_normal_noetherian R G hG φ hφ
  exact ⟨g, hg, GlobalTheory.T.thickening_eq_of_generic_section_ratios R hR D A G hG U a a' h h' hE b hb N S hS hnd φ hgen g hg hgφ⟩

end GlobalTheory.Mum
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.EtLev
open scoped TensorProduct


theorem _root_.GlobalTheory.T.abelianScheme_card_kernel_eq_norm_pow : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ (F : Type) [Field F] [NumberField F] (act : OAct (𝓞 F) A) (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S) (h ℓ : ℕ), ℓ.Prime → (ℓ : k) ≠ 0 → (∀ j : ℕ, ∃ f : (Fin h → 𝓞 F ⧸ Ideal.span {((ℓ ^ j : ℕ) : 𝓞 F)}) → (Over.mk x ⟶ A), (∀ a a', f (a + a') = f a * f a') ∧ (∀ (c : 𝓞 F) a, f (Ideal.Quotient.mk (Ideal.span {((ℓ ^ j : ℕ) : 𝓞 F)}) c • a) = f a ≫ act.act c) ∧ Function.Injective f ∧ ∀ g : Over.mk x ⟶ A, g ^ (ℓ ^ j) = 1 → ∃ a, f a = g) → ∀ c : 𝓞 F, c ≠ 0 → (∀ v : epsPtR x ⟶ A, spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ v.left = (1 : Over.mk x ⟶ A).left → v ≫ act.act c = 1 → v = 1) → Nat.card {g : Over.mk x ⟶ A // g ≫ act.act c = 1} = (Algebra.norm ℤ c).natAbs ^ h := by
  first | (exact @GlobalTheory.AVCount.card_ker_eq_norm_pow) | (exact GlobalTheory.AVCount.card_ker_eq_norm_pow) | (intros; apply GlobalTheory.AVCount.card_ker_eq_norm_pow  <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke

theorem _root_.GlobalTheory.T.exists_heckeMap_harrisTaylorIntegralModels : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] [IsNoetherianRing R] (b : Base D R) (g : D.La →ₗ[D.O] D.La) (c k N : ℕ), c.Coprime p → k.Coprime p → 3 ≤ N → N.Coprime p → (∀ x y, D.EF (g x) (g y) = c * D.EF x y) → (∀ x, ∃ y, g y = k • x) → c ∣ k ^ 2 → ∀ (M : Model b N) (M' : Model b (N * k)), ∃ π : M'.X ⟶ M.X, IsHeckeMap g c k N M.toRepFam M'.toRepFam π := by
  first | (exact @GlobalTheory.UPel.HT.Hecke.exists_isHeckeMap) | (exact GlobalTheory.UPel.HT.Hecke.exists_isHeckeMap) | (intros; apply GlobalTheory.UPel.HT.Hecke.exists_isHeckeMap <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_galoisInvariant_local_frames_uniformisation : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), FinExt ρ → IsGal ρ → ∀ (D : DegData R (maximalIdeal R)) (D' : DegData R' (maximalIdeal R')) (hD : IsPullDeg ρ D.toPre D'.toPre) (A' : PolAV (Sp (FractionRing R'))) (G' : Over (Sp R')) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (U' : Unif (maximalIdeal R') D' A' G'), ∀ (a : GalAct ρ hD U') (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (β : G'.left ⟶ G.left), IsSemiAbelian G → IsGrpPullback G' G (spMap ρ) β → (∀ σ, a.act σ ≫ β = β) → ∃ (V : G.left → G.left.Opens) (T : ∀ (y : G.left) (k : U'.LG.L.ι), Γ(G'.left, β ⁻¹ᵁ V y ⊓ U'.LG.L.U k)ˣ), (∀ y, y ∈ V y) ∧ (∀ y k k', res (inf_le_left : β ⁻¹ᵁ V y ⊓ U'.LG.L.U k ⊓ (β ⁻¹ᵁ V y ⊓ U'.LG.L.U k') ≤ β ⁻¹ᵁ V y ⊓ U'.LG.L.U k) (T y k) = res (le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right) : β ⁻¹ᵁ V y ⊓ U'.LG.L.U k ⊓ (β ⁻¹ᵁ V y ⊓ U'.LG.L.U k') ≤ U'.LG.L.U k ⊓ U'.LG.L.U k') (U'.LG.L.g k k') * res (inf_le_right : β ⁻¹ᵁ V y ⊓ U'.LG.L.U k ⊓ (β ⁻¹ᵁ V y ⊓ U'.LG.L.U k') ≤ β ⁻¹ᵁ V y ⊓ U'.LG.L.U k') (T y k')) ∧ ∀ (y y' : G.left) (r : Γ(G'.left, β ⁻¹ᵁ (V y ⊓ V y'))ˣ), (∀ (z : G'.left) (k : U'.LG.L.ι), z ∈ β ⁻¹ᵁ (V y ⊓ V y') → z ∈ U'.LG.L.U k → gm (𝟙 G'.left) z _ r = gm (𝟙 G'.left) z _ (T y' k) * (gm (𝟙 G'.left) z _ (T y k))⁻¹) → ∀ σ (h : β ⁻¹ᵁ (V y ⊓ V y') ≤ a.act σ ⁻¹ᵁ (β ⁻¹ᵁ (V y ⊓ V y'))), ((a.act σ).appLE _ _ h).hom r.val = r.val := by
  first | exact @GlobalTheory.Mum.unif_lb_frames_gal | exact GlobalTheory.Mum.unif_lb_frames_gal | (intros; apply GlobalTheory.Mum.unif_lb_frames_gal <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

theorem _root_.GlobalTheory.T.arithReciprocity_noCommonDivisor_projective : GlobalTheory.Published.Principalisation → ∀ (F : Type) [Field F] (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp F) (σ : F →+* ℂ) (e : ℕ), IsProjOver p → topologicalKrullDim X = (e + 1 : ℕ) → ∀ (L : Fin e → MLine p σ) (M N : MLine p σ) (s : M.B.Sec) (hs : genericPoint X ∈ nonzeroLocus s) (t : N.B.Sec) (ht : genericPoint X ∈ nonzeroLocus t), (∀ z : X, Order.coheight z = 1 → z ∈ nonzeroLocus s ∨ z ∈ nonzeroLocus t) → side N L (M.logSec s) (N.logSec t) (divOfSec M.φ.isLB s hs) = side M L (N.logSec t) (M.logSec s) (divOfSec N.φ.isLB t ht) := by
  first | exact @GlobalTheory.Mix.reciprocity_of_noCommonDivisor | exact GlobalTheory.Mix.reciprocity_of_noCommonDivisor | (intros; apply GlobalTheory.Mix.reciprocity_of_noCommonDivisor <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt

namespace GlobalTheory.MixHt

theorem exists_isMix_of_arch : ArchInteg → ArchRecip →
    (∀ (k : Type) [CommRing k] (Y : Scheme.{0}) (q : Y ⟶ Sp k), IsAmb q → ∀ m : ℕ, ∃ T, IsMix q m T) := by
  intro hI hR
  have key : ∀ m : ℕ, ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) (q : Y ⟶ Sp k), IsAmb q → ∃ T, IsMix q m T := by
    intro m
    induction m with
    | zero => intro k _ Y q _; exact ⟨_, isMix_zero q⟩
    | succ m ih => exact GlobalTheory.T.isMixedHeightByInduction_succ hI hR m ih
  intro k _ Y q h m
  exact key m k Y q h

end GlobalTheory.MixHt
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.MumTwist

theorem exists_twist : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D₀ D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, SamePol D₀.toPre D.toPre → ∃ (a : 𝟙_ (Over (Sp R)) ⟶ G) (P : GlobalTheory.UU.CP G) (A₂ : PolAV (Sp (FractionRing R))) (gen₂ : (Over.pullback (jK R)).obj G ≅ A₂.A), a ^ 2 = 1 ∧ LBIso P.L.L (U.LG.L.pull ((toUnit G ≫ a) * 𝟙 G).left) ∧ EvenOn P ∧ IsMonHom gen₂.hom ∧ LBIso (A₂.L.pull gen₂.hom.left) (P.L.L.pull (pullback.fst G.hom (jK R))) ∧ ∀ (D₂ : DegData R (maximalIdeal R)) (U₂ : Unif (maximalIdeal R) D₂ A₂ G), U₂.LG = P.L → ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : IsLocalRing R') (ρ : R →+* R') (D₁ : DegData R' (maximalIdeal R')), FinExt ρ ∧ IsLocalHom ρ ∧ Nonempty (IsPullDeg ρ D₀.toPre D₁.toPre) ∧ ∀ D' : DegData R' (maximalIdeal R'), Nonempty (IsPullDeg ρ D₂.toPre D'.toPre) → Nonempty (IsPullDeg (RingHom.id R') D₁.toPre D'.toPre) := by
  intro R _ _ _ hR D₀ D A G _ _ hG U hS
  obtain ⟨a, ha, hcmp⟩ := GlobalTheory.T.exists_orderTwo_section_translate_refinement R hR D₀ D A G hG U hS
  obtain ⟨P, hP, hE⟩ := GlobalTheory.T.exists_evenCubicalSymmetricBundle_translate_orderTwo R hR D A G hG U a ha
  obtain ⟨A₂, gen₂, hm, hl⟩ := GlobalTheory.T.exists_principal_polarisation_genericFibre_twoTorsion_translate R hR D A G hG U a ha P hP
  refine ⟨a, P, A₂, gen₂, ha, hP, hE, hm, hl, fun D₂ U₂ hU => ?_⟩
  exact hcmp A₂ D₂ U₂ (by rw [hU]; exact hP)

end GlobalTheory.MumTwist
end
