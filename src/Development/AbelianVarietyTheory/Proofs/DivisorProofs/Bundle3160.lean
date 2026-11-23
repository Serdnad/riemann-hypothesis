module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle074
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle018
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle071
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle068
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiFiniteTautologicalChartOfSeparation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1382
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1516
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2708
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3102
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle065
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3034
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle075
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
public import Mathlib.FieldTheory.FinTrdeg
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle001
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle067
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle070
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle077

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Poinc GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TChart

theorem lbIso_pull_both {X X' Y Z : Scheme.{0}} {L : LB X} {M : LB X'} {a : Y ⟶ X} {b : Y ⟶ X'}
    (h : LBIso (L.pull a) (M.pull b)) (j : Z ⟶ Y) {a' : Z ⟶ X} {b' : Z ⟶ X'} (ea : a' = j ≫ a) (eb : b' = j ≫ b) :
    LBIso (L.pull a') (M.pull b') :=
  LBIso.chartPull (Geo.Tor.chartPullSame L _ (fun _ => a) _ j fun _ => ea)
    (Geo.Tor.chartPullSame M _ (fun _ => b) _ j fun _ => eb) h

theorem isSquare_eq {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} {φ φ' : G'.left ⟶ G.left}
    {a b : (G' ⊗ G').left ⟶ (G ⊗ G).left} (ha : IsSquare φ a) (hb : IsSquare φ' b) (e : φ = φ') : a = b := by
  subst e
  apply pullback.hom_ext
  · exact ha.1.trans hb.1.symm
  · exact ha.2.trans hb.2.symm


set_option backward.isDefEq.respectTransparency false in
theorem IsMumPol.exists_isMumfordFam {o : Type} [CommRing o] {ζ : o} {g n : ℕ} (F : SFam g n ζ) {R : Type} [CommRing R]
    [IsDomain R] [IsLocalRing R] {Q : Data R} {G₁ : Over (Sp R)} [GrpObj G₁] [IsCommMonObj G₁] {P : LB (G2 G₁).left}
    (h : IsMumPol Q G₁ P) {T : Scheme.{0}} {i : T ⟶ Sp R} {l : Sp (FractionRing R) ⟶ T} (hl : l ≫ i = jK R)
    {A₀ : Over T} [GrpObj A₀] [IsCommMonObj A₀] {P₀ : LB (G2 A₀).left} (hP₀ : P₀.IsLB)
    {a : A₀.left ⟶ G₁.left} {a₂ : (G2 A₀).left ⟶ (G2 G₁).left} (ha : IsGrpPullback A₀ G₁ i a) (ha₂ : IsSquare a a₂)
    (hPa : LBIso P₀ (P.pull a₂)) {yU : T ⟶ F.X} {φ : A₀.left ⟶ F.univ.A.left} {φ₂ : (G2 A₀).left ⟶ (G2 F.univ.A).left}
    (hφ : IsGrpPullback A₀ F.univ.A yU φ) (hφ₂ : IsSquare φ φ₂) (hPφ : LBIso P₀ (F.univ.P.pull φ₂)) :
    ∃ α₁ : pullback G₁.hom (jK R) ⟶ F.univ.A.left, IsGenFibre F (l ≫ yU) α₁ ∧ IsMumfordFam F (l ≫ yU) α₁ Q := by
  obtain ⟨hR, hpos, -, hbi, hU⟩ := h
  have w : pullback.fst G₁.hom (jK R) ≫ G₁.hom = (pullback.snd G₁.hom (jK R) ≫ l) ≫ i := by
    rw [Category.assoc, hl, pullback.condition]
  obtain ⟨ω, ω₁, ω₂⟩ : ∃ ω : pullback G₁.hom (jK R) ⟶ A₀.left, ω ≫ a = pullback.fst G₁.hom (jK R) ∧
      ω ≫ A₀.hom = pullback.snd G₁.hom (jK R) ≫ l := ⟨ha.1.lift _ _ w, ha.1.lift_fst _ _ w, ha.1.lift_snd _ _ w⟩
  have h₁ := isGrpPullback_pullback G₁ (jK R)
  have hω : IsGrpPullback ((Over.pullback (jK R)).obj G₁) A₀ l ω := ha.cancel (h₁.congr hl.symm ω₁.symm) ω₂
  refine ⟨ω ≫ φ, hω.comp hφ, hR, hpos, fun R' _ _ _ ρ hR' hρ hf D ε hD => ?_⟩
  obtain ⟨G', _, _, π, π₂, A, U, hπ, hπ₂, hL⟩ := hU R' ρ hR' hρ hf D ε hD
  obtain ⟨κ, hκ⟩ := exists_genericMap hρ
  letI := A.isAb.comm
  have w' : (pullback.fst G'.hom (jK R') ≫ π) ≫ G₁.hom = (pullback.snd G'.hom (jK R') ≫ κ) ≫ jK R := by
    rw [Category.assoc, hπ.1.w, Category.assoc, hκ, pullback.condition_assoc]
  obtain ⟨πK, p₁, p₂⟩ : ∃ πK : pullback G'.hom (jK R') ⟶ pullback G₁.hom (jK R),
      πK ≫ pullback.fst G₁.hom (jK R) = pullback.fst G'.hom (jK R') ≫ π ∧
      πK ≫ pullback.snd G₁.hom (jK R) = pullback.snd G'.hom (jK R') ≫ κ :=
    ⟨pullback.lift _ _ w', pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  have h₂ := isGrpPullback_pullback G' (jK R')
  have hπK : IsGrpPullback ((Over.pullback (jK R')).obj G') ((Over.pullback (jK R)).obj G₁) κ πK :=
    h₁.cancel ((h₂.comp hπ).congr hκ.symm p₁.symm) p₂
  haveI := U.gen_hom
  haveI : IsMonHom U.gen.symm.hom := inferInstanceAs (IsMonHom U.gen.inv)
  have hi := isGrpPullback_of_iso U.gen.symm
  have e₁ : U.gen.hom.left ≫ U.gen.symm.hom.left = 𝟙 _ := by
    rw [← Over.comp_left, Iso.symm_hom, U.gen.hom_inv_id, Over.id_left]
  have e₂ : U.gen.symm.hom.left ≫ U.gen.hom.left = 𝟙 _ := by
    rw [← Over.comp_left, Iso.symm_hom, U.gen.inv_hom_id, Over.id_left]
  have hβ := hi.comp (hπK.comp hω)
  have hδ := hi.comp h₂
  obtain ⟨β₂, hβ₂⟩ : ∃ β₂, IsSquare _ β₂ := ⟨_, GlobalTheory.LamPull.exists_isSquare hβ.1.w⟩
  obtain ⟨δ₂, hδ₂⟩ : ∃ δ₂, IsSquare _ δ₂ := ⟨_, GlobalTheory.LamPull.exists_isSquare hδ.1.w⟩
  have r : LBIso A.L (U.LG.L.pull (U.gen.symm.hom.left ≫ pullback.fst G'.hom (jK R'))) :=
    LBIso.trans A.isLB (pull_isLB A.isLB _) (pull_isLB U.LG.isLB _)
      (LBIso.chartPull (chartPullId A.L) (Geo.Tor.chartPullPull A.L (𝟙 _) (𝟙 _) rfl) (GlobalTheory.PolBaseChange.lbIso_refl A.isLB))
      (lbIso_pull_both U.ext U.gen.symm.hom.left e₂.symm rfl)
  have l₁ := GlobalTheory.LamPull.lbIso_lam_pull hδ U.LG.isLB A.isLB r hδ₂
  have i₁ : (abelian₂ G' U.LG.L).IsLB := DVR.linComb_isLB _ U.LG.isLB _ _
  have i₀ : (abelian₂ A.A A.L).IsLB := DVR.linComb_isLB _ A.isLB _ _
  have e₃ : β₂ ≫ a₂ = δ₂ ≫ π₂ := isSquare_eq (isSquare_comp hβ₂ ha₂) (isSquare_comp hδ₂ hπ₂) (by
    simp only [Category.assoc]
    rw [ω₁, p₁])
  have l₂ := lbIso_pull_comp hL δ₂ e₃
  have l₃ := (lbIso_pull_comp hPa β₂ rfl).symm
  have l₄ := lbIso_pull_comp hPφ β₂ rfl
  refine ⟨G', inferInstance, inferInstance, π, A, U, hπ, κ, πK, (U.gen.symm.hom.left ≫ πK ≫ ω) ≫ φ, β₂ ≫ φ₂, hκ, p₁,
    (hβ.comp hφ).congr (by simp only [Category.id_comp, Category.assoc]) rfl, isSquare_comp hβ₂ hφ₂,
    LBIso.trans i₀ (pull_isLB i₁ _) (pull_isLB F.univ.isLB _) l₁
      (LBIso.trans (pull_isLB i₁ _) (pull_isLB hbi.1 _) (pull_isLB F.univ.isLB _) l₂
        (LBIso.trans (pull_isLB hbi.1 _) (pull_isLB hP₀ _) (pull_isLB F.univ.isLB _) l₃ l₄)), ?_⟩
  simp only [Category.assoc]
  rw [← Category.assoc, e₁, Category.id_comp]

theorem dense_generic_away {o R : Type} [CommRing o] [CommRing R] [IsDomain R] {b : o →+* R} (hb : Function.Injective b)
    {f : R} (hf : f ≠ 0) :
    Dense {x : Sp (Localization.Away f) | (spMap ((algebraMap R (Localization.Away f)).comp b) x).asIdeal = ⊥} := by
  have hle := powers_le_nonZeroDivisors_of_noZeroDivisors hf
  haveI : IsDomain (Localization.Away f) := IsLocalization.isDomain_localization hle
  have hinj : Function.Injective ((algebraMap R (Localization.Away f)).comp b) :=
    (IsLocalization.injective (Localization.Away f) hle).comp hb
  let p : PrimeSpectrum (Localization.Away f) := ⟨⊥, Ideal.isPrime_bot⟩
  have hp : Dense ({p} : Set (PrimeSpectrum (Localization.Away f))) := by
    rw [dense_iff_closure_eq, PrimeSpectrum.closure_singleton]
    simp [p]
  refine Dense.mono ?_ hp
  rintro x rfl
  exact (RingHom.injective_iff_ker_eq_bot _).1 hinj


set_option backward.isDefEq.respectTransparency false in
theorem Taut.exists_isFam_of_siegPre : ∀ (g n : ℕ) (φ : InvFun ℤ), 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (C : Taut (zetaAway n) g n φ) (G₁ : Over (Sp C.R)) [GrpObj G₁] [IsCommMonObj G₁] (P : LB (G2 G₁).left), IsMumPol C.Q G₁ P → (∀ p : Sp C.R, p ∈ abLocus G₁ ↔ ∏ k, C.t k ∉ p.asIdeal) → ∀ c : SiegPre g n (zetaAway n) (spMap ((algebraMap C.R (Localization.Away (∏ k, C.t k))).comp C.b)), c.Principal → (∃ (a : c.A.left ⟶ G₁.left) (a₂ : (G2 c.A).left ⟶ (G2 G₁).left), IsGrpPullback c.A G₁ (spMap (algebraMap C.R (Localization.Away (∏ k, C.t k)))) a ∧ IsSquare a a₂ ∧ LBIso c.P (P.pull a₂)) → ∃ (y : Sp (FractionRing C.R) ⟶ F.X) (α₁ : pullback G₁.hom (jK C.R) ⟶ F.univ.A.left) (yU : Sp (Localization.Away (∏ k, C.t k)) ⟶ F.X) (l : Localization.Away (∏ k, C.t k) →+* FractionRing C.R), C.IsFam F G₁ y α₁ ∧ SiegPB c F.univ yU ∧ l.comp (algebraMap C.R (Localization.Away (∏ k, C.t k))) = algebraMap C.R (FractionRing C.R) ∧ y = spMap l ≫ yU := by
  intro g n φ hn _ F C G₁ _ _ P hM hab c hc ⟨a, a₂, ha, ha₂, hPa⟩
  obtain ⟨-, -, hinj, -, hrel, -⟩ := Taut.isRegularLocalRing_and_isRelParam g n φ hn C
  have hf : ∏ k, C.t k ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ => ne_zero_of_isRelParam hrel i
  haveI : IsDomain (Localization.Away (∏ k, C.t k)) :=
    IsLocalization.isDomain_localization (powers_le_nonZeroDivisors_of_noZeroDivisors hf)
  obtain ⟨yU, hs, hPB⟩ := F.rep _ _ c inferInstance (dense_generic_away hinj hf) hc
  have hu : IsUnit (algebraMap C.R (FractionRing C.R) (∏ k, C.t k)) :=
    IsUnit.mk0 _ ((map_ne_zero_iff _ (IsFractionRing.injective C.R _)).2 hf)
  let l : Localization.Away (∏ k, C.t k) →+* FractionRing C.R := IsLocalization.Away.lift _ hu
  have hl : l.comp (algebraMap C.R (Localization.Away (∏ k, C.t k))) = algebraMap C.R (FractionRing C.R) :=
    IsLocalization.Away.lift_comp _ hu
  have hl' : spMap l ≫ spMap (algebraMap C.R (Localization.Away (∏ k, C.t k))) = jK C.R := by
    rw [← Geo.Tor.spMap_comp, hl]
  obtain ⟨ψ, ψ₂, h₁, h₂, h₃, h₄⟩ := hPB
  obtain ⟨α₁, hα, hF⟩ := hM.exists_isMumfordFam F hl' c.isLB ha ha₂ hPa h₁ h₂ h₃
  refine ⟨spMap l ≫ yU, α₁, yU, l, ⟨hM.2.2.1, hab, hα, hF, ?_⟩, ⟨ψ, ψ₂, h₁, h₂, h₃, h₄⟩, hl, rfl⟩
  rw [Category.assoc, hs, Geo.Tor.spMap_comp, ← Category.assoc, hl']

end GlobalTheory.TChart
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.Poinc GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.quasiFinite_tautologicalChart_of_separation : GlobalTheory.Poinc.Sep.SepSt → ∀ g : ℕ, 1 ≤ g → ∀ φ : InvFun ℤ, IsPolFan id g φ → NoSelfInt id g φ → ∀ n : ℕ, 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (Z : Scheme.{0}) (z : Z ⟶ Sp (cycAway n)) (i : F.X ⟶ Z) (OZ : LB Z) (d : ℕ) (S : Scheme.{0}) (π : S ⟶ Z) (j : F.X ⟶ S) [IsOpenImmersion j] (BD : GlobalTheory.EffCartierData S), MinAt5 F z i OZ → BlowAt F z i φ d π j BD → ∀ (C : Taut (zetaAway n) g n φ) (G₁ : Over (Sp C.R)) [GrpObj G₁] [IsCommMonObj G₁] (y : Sp (FractionRing C.R) ⟶ F.X) (α₁ : pullback G₁.hom (jK C.R) ⟶ F.univ.A.left) (ξ : Sp C.R ⟶ S), C.IsFam F G₁ y α₁ → y ≫ j = jK C.R ≫ ξ → (∀ p : Ideal C.R, p.IsPrime → (maximalIdeal (S.presheaf.stalk (ξ (closedPoint C.R)))).map (Scheme.stalkClosedPointTo ξ).hom ≤ p → p = maximalIdeal C.R) ∧ ((residue C.R).comp (Scheme.stalkClosedPointTo ξ).hom).Finite := by
  first | exact @GlobalTheory.QFChart.quasiFinite_tautChart | exact GlobalTheory.QFChart.quasiFinite_tautChart | (intros; apply GlobalTheory.QFChart.quasiFinite_tautChart <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CDimAlg

theorem trdeg_lt_aleph0_of_essFiniteType (F W : Type) [Field F] [CommRing W] [IsDomain W] [Algebra F W]
    [Algebra.EssFiniteType F W] : Algebra.trdeg F W < Cardinal.aleph0 := by
  set W₀ := Algebra.EssFiniteType.subalgebra F W
  haveI : FaithfulSMul W₀ W := (faithfulSMul_iff_algebraMap_injective _ _).2 Subtype.val_injective
  haveI : Algebra.IsAlgebraic W₀ W := IsLocalization.isAlgebraic W (Algebra.EssFiniteType.submonoid F W)
  have h := trdeg_add_eq F W₀ (A := W)
  rw [trdeg_eq_zero (R := W₀) (A := W), add_zero] at h
  rw [← h]
  exact trdeg_lt_aleph0_of_finiteType

theorem exists_nat_of_add_eq {d : WithBot ℕ∞} {n m : ℕ} (h : d + n = m) : ∃ k : ℕ, d = k ∧ k + n = m := by
  induction d using WithBot.recBotCoe with
  | bot => simp at h
  | coe e =>
    induction e using ENat.recTopCoe with
    | top =>
      exfalso
      have h' : ((⊤ + n : ℕ∞) : WithBot ℕ∞) = ((m : ℕ∞) : WithBot ℕ∞) := by exact_mod_cast h
      rw [WithBot.coe_inj, top_add] at h'
      exact ENat.top_ne_natCast m h'
    | coe k =>
      refine ⟨k, rfl, ?_⟩
      exact_mod_cast h

end GlobalTheory.CDimAlg

namespace GlobalTheory.CDimAlg

theorem ringKrullDim_add_trdeg_of_isComplAt : ∀ (F W R : Type) [Field F] [CommRing W] [IsDomain W] [IsLocalRing W] [CommRing R] [IsLocalRing R] (b : F →+* W), b.EssFiniteType → ∀ (I : Type) [Fintype I] (ψ : MvPolynomial I W →+* R), GlobalTheory.TChart.IsComplAt ψ → IsLocalHom (ψ.comp MvPolynomial.C) → ∀ bR : F →+* R, (ψ.comp MvPolynomial.C).comp b = bR → ((residue R).comp bR).EssFiniteType ∧ ∀ a t : ℕ, ringKrullDim W = a → (letI := ((residue W).comp b).toAlgebra; Algebra.trdeg F (ResidueField W) = t) → ∃ a' t' : ℕ, ringKrullDim R = a' ∧ (letI := ((residue R).comp bR).toAlgebra; Algebra.trdeg F (ResidueField R) = t') ∧ a' + t' = a + t + Fintype.card I := by
  intro F W R _ _ _ _ _ _ b hb I _ ψ hψ hloc bR hbR
  obtain ⟨hRn, -, hfl, hmap, hres⟩ := hψ
  letI : Algebra F W := b.toAlgebra
  haveI : Algebra.EssFiniteType F W := hb
  haveI : IsNoetherianRing W := Algebra.EssFiniteType.isNoetherianRing F W
  set q : Ideal (MvPolynomial I W) := (maximalIdeal R).comap ψ with hq
  haveI : q.IsPrime := Ideal.comap_isPrime ψ _
  have hmemq : ∀ x, x ∈ q ↔ ¬ IsUnit (ψ x) := fun x => by
    rw [hq, Ideal.mem_comap, mem_maximalIdeal, mem_nonunits_iff]
  have hu : ∀ s : q.primeCompl, IsUnit (ψ s) := fun s => by
    have h := s.2
    rw [Ideal.mem_primeCompl_iff, hmemq, not_not] at h
    exact h
  let ψA : Localization.AtPrime q →+* R := IsLocalization.lift hu
  have hψA' : ∀ x, ψA (algebraMap _ (Localization.AtPrime q) x) = ψ x := fun x => IsLocalization.lift_eq hu x
  have hψA : ψA.comp (algebraMap _ (Localization.AtPrime q)) = ψ := RingHom.ext hψA'
  haveI hlocA : IsLocalHom ψA := by
    refine ⟨fun x hx => ?_⟩
    obtain ⟨⟨p, s⟩, rfl⟩ := IsLocalization.mk'_surjective q.primeCompl x
    have e1 := IsLocalization.mk'_spec (Localization.AtPrime q) p s
    have hp : IsUnit (ψ p) := by
      rw [← hψA', ← e1, map_mul, hψA']
      exact hx.mul (hu s)
    have hpq : p ∈ q.primeCompl := by
      rw [Ideal.mem_primeCompl_iff, hmemq, not_not]; exact hp
    have h2 : IsUnit (algebraMap _ (Localization.AtPrime q) p) := IsLocalization.map_units _ ⟨p, hpq⟩
    rw [← e1] at h2
    exact isUnit_of_mul_isUnit_left h2
  letI : Algebra (MvPolynomial I W) R := ψ.toAlgebra
  letI : Algebra (Localization.AtPrime q) R := ψA.toAlgebra
  haveI : IsScalarTower (MvPolynomial I W) (Localization.AtPrime q) R :=
    IsScalarTower.of_algebraMap_eq (fun x => (hψA' x).symm)
  haveI : Module.Flat (MvPolynomial I W) R := hfl
  haveI : Module.Flat (Localization.AtPrime q) R :=
    (Module.flat_iff_of_isLocalization (Localization.AtPrime q) q.primeCompl R).2 inferInstance
  haveI : IsNoetherianRing (Localization.AtPrime q) :=
    IsLocalization.isNoetherianRing q.primeCompl _ inferInstance
  haveI : IsNoetherianRing R := hRn
  haveI : IsLocalHom (algebraMap (Localization.AtPrime q) R) := hlocA
  have hmA : (maximalIdeal (Localization.AtPrime q)).map (algebraMap (Localization.AtPrime q) R) = maximalIdeal R := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_map]
    change q.map (ψA.comp (algebraMap _ (Localization.AtPrime q))) = _
    rw [hψA]; exact hmap
  have hdim : ringKrullDim (Localization.AtPrime q) = ringKrullDim R :=
    GlobalTheory.RegSmooth.ringKrullDim_eq_of_flat_of_map_maximalIdeal hmA

  let κ : ResidueField (Localization.AtPrime q) →+* ResidueField R := ResidueField.map ψA
  have hκs : Function.Surjective κ := by
    intro y
    obtain ⟨r, rfl⟩ := residue_surjective y
    obtain ⟨a, c, hc, hr⟩ := hres r
    have hcq : c ∈ q.primeCompl := by rw [Ideal.mem_primeCompl_iff, hmemq, not_not]; exact hc
    refine ⟨residue _ (IsLocalization.mk' (Localization.AtPrime q) a ⟨c, hcq⟩), ?_⟩
    have e1 : ψA (IsLocalization.mk' (Localization.AtPrime q) a ⟨c, hcq⟩) * ψ c = ψ a := by
      rw [← hψA' c, ← map_mul, IsLocalization.mk'_spec, hψA']
    have e2 : residue R (r * ψ c) = residue R (ψ a) := Ideal.Quotient.eq.2 hr
    have hne : residue R (ψ c) ≠ 0 := (residue_ne_zero_iff_isUnit _).2 hc
    change residue R (ψA _) = residue R r
    refine mul_right_cancel₀ hne ?_
    rw [← map_mul, e1, ← e2, map_mul]
  let e : ResidueField (Localization.AtPrime q) ≃+* ResidueField R := RingEquiv.ofBijective κ ⟨κ.injective, hκs⟩
  have hcomp : ∀ x : F, e (residue _ (algebraMap F (Localization.AtPrime q) x)) = residue R (bR x) := by
    intro x
    change residue R (ψA _) = _
    rw [IsScalarTower.algebraMap_apply F (MvPolynomial I W) (Localization.AtPrime q), hψA', ← hbR]
    rfl
  haveI : Algebra.EssFiniteType F (MvPolynomial I W) := Algebra.EssFiniteType.comp F W _
  haveI : Algebra.EssFiniteType (MvPolynomial I W) (Localization.AtPrime q) :=
    Algebra.EssFiniteType.of_isLocalization _ q.primeCompl
  haveI hAft : Algebra.EssFiniteType F (Localization.AtPrime q) :=
    Algebra.EssFiniteType.comp F (MvPolynomial I W) _
  have hresA : ((residue (Localization.AtPrime q)).comp (algebraMap F (Localization.AtPrime q))).EssFiniteType :=
    RingHom.EssFiniteType.comp (RingHom.essFiniteType_algebraMap.2 hAft)
      (RingHom.FiniteType.of_surjective _ residue_surjective).essFiniteType
  have hRe : (residue R).comp bR =
      e.toRingHom.comp ((residue (Localization.AtPrime q)).comp (algebraMap F (Localization.AtPrime q))) :=
    RingHom.ext fun x => (hcomp x).symm
  refine ⟨?_, ?_⟩
  · rw [hRe]
    exact RingHom.EssFiniteType.comp hresA (RingHom.FiniteType.of_surjective _ e.surjective).essFiniteType
  intro a t ha ht

  obtain ⟨mW, hmW⟩ : ∃ m : ℕ, Algebra.trdeg F W = m :=
    Cardinal.lt_aleph0.1 (trdeg_lt_aleph0_of_essFiniteType F W)
  have hW : ringKrullDim W + t = mW := by
    letI : Algebra F (ResidueField W) := ((residue W).comp b).toAlgebra
    haveI : IsScalarTower F W (ResidueField W) := IsScalarTower.of_algebraMap_eq' rfl
    exact GlobalTheory.LocModelDim.ringKrullDim_add_trdeg (k := F) (R := W) (Ω := ResidueField W) residue_surjective ht hmW

  haveI : FaithfulSMul F W := (faithfulSMul_iff_algebraMap_injective _ _).2 b.injective
  haveI : FaithfulSMul W (MvPolynomial I W) :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (MvPolynomial.C_injective I W)
  have hP : Algebra.trdeg F (MvPolynomial I W) = ((mW + Fintype.card I : ℕ) : Cardinal) := by
    rw [← trdeg_add_eq F W (A := MvPolynomial I W), MvPolynomial.trdeg_of_isDomain, hmW, Cardinal.lift_id,
      Cardinal.mk_fintype]
    push_cast; rfl
  haveI : FaithfulSMul (MvPolynomial I W) (Localization.AtPrime q) :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (IsLocalization.injective _ q.primeCompl_le_nonZeroDivisors)
  haveI : Algebra.IsAlgebraic (MvPolynomial I W) (Localization.AtPrime q) :=
    IsLocalization.isAlgebraic _ q.primeCompl
  have hA : Algebra.trdeg F (Localization.AtPrime q) = ((mW + Fintype.card I : ℕ) : Cardinal) := by
    rw [← trdeg_add_eq F (MvPolynomial I W) (A := Localization.AtPrime q),
      trdeg_eq_zero (R := MvPolynomial I W) (A := Localization.AtPrime q), add_zero, hP]

  letI alA : Algebra F (ResidueField (Localization.AtPrime q)) :=
    ((residue (Localization.AtPrime q)).comp (algebraMap F (Localization.AtPrime q))).toAlgebra
  haveI : IsScalarTower F (Localization.AtPrime q) (ResidueField (Localization.AtPrime q)) :=
    IsScalarTower.of_algebraMap_eq' rfl
  haveI : Algebra.EssFiniteType F (ResidueField (Localization.AtPrime q)) := hresA
  obtain ⟨tA, htA⟩ : ∃ m : ℕ, Algebra.trdeg F (ResidueField (Localization.AtPrime q)) = m :=
    Cardinal.lt_aleph0.1 (trdeg_lt_aleph0 F (ResidueField (Localization.AtPrime q)))
  have hAf := GlobalTheory.LocModelDim.ringKrullDim_add_trdeg (k := F) (R := Localization.AtPrime q)
    (Ω := ResidueField (Localization.AtPrime q)) residue_surjective htA hA
  obtain ⟨k, hk, hkt⟩ := exists_nat_of_add_eq hAf
  letI alR : Algebra F (ResidueField R) := ((residue R).comp bR).toAlgebra
  let eA : ResidueField (Localization.AtPrime q) ≃ₐ[F] ResidueField R := { e with commutes' := fun x => hcomp x }
  refine ⟨k, tA, by rw [← hdim, hk], by rw [← eA.trdeg_eq, htA], ?_⟩
  obtain ⟨a0, ha0, ha0t⟩ := exists_nat_of_add_eq hW
  rw [ha] at ha0
  have : a = a0 := by exact_mod_cast ha0
  omega

end GlobalTheory.CDimAlg
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Poinc GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TChart.Taut

theorem X_mem_nonZeroDivisors (W : Type) [CommRing W] {σ : Type} (k : σ) :
    (MvPolynomial.X k : MvPolynomial σ W) ∈ nonZeroDivisors (MvPolynomial σ W) := by
  refine mem_nonZeroDivisors_iff.2 ⟨fun p hp => ?_, fun p hp => ?_⟩
  · ext m
    have := congrArg (AddMonoidAlgebra.coeff · (m + Finsupp.single k 1)) hp
    rwa [mul_comm, MvPolynomial.coeff_mul_X, MvPolynomial.coeff_zero] at this
  · ext m
    have := congrArg (AddMonoidAlgebra.coeff · (m + Finsupp.single k 1)) hp
    rwa [MvPolynomial.coeff_mul_X, MvPolynomial.coeff_zero] at this

theorem monomial_chart : ∀ {o : Type} [CommRing o] {ζ : o} (g n : ℕ) (φ : InvFun ℤ), 1 ≤ n → ∀ C : Taut ζ g n φ,
    C.Q.IsMonomialTau C.t (fun k => (n : ℤ) • C.δ k) ∧ Module.finrank ℤ C.Q.X ≤ g ∧ IsCone id φ C.δ ∧
      (∀ z, z ≠ 0 → ∃ k, 0 < C.δ k z z) ∧ (∀ k, C.t k ≠ 0) := by
  intro o _ ζ g n φ _ C
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro a b
    obtain ⟨k, hk, hc⟩ := GlobalTheory.T.tautologicalBase_periods_factor_mul_generator C.T (C.ψ.comp MvPolynomial.C) (fun k => C.ψ (MvPolynomial.X k))
      (fun k => (C.ε k : LinearMap.BilinForm ℤ (Fin C.T.r → ℤ))) n C.Q C.e C.data a b
    let z : Fin C.N → ℤ := fun j => (n : ℤ) * (C.ε (.inr j) : LinearMap.BilinForm ℤ (Fin C.T.r → ℤ)) (C.e a) (C.e b)
    let w : C.Rˣ := ∏ j, (C.tor j).unit ^ z j
    refine ⟨k * Units.map (algebraMap C.R (FractionRing C.R) : C.R →* FractionRing C.R) w⁻¹, ?_,
      GlobalTheory.PolDeg.Taut.tauCoord_mul_unit hc w⁻¹⟩
    rw [Units.val_mul, hk, Fintype.prod_sum_type]
    have hw : ((Units.map (algebraMap C.R (FractionRing C.R) : C.R →* FractionRing C.R) w⁻¹ : (FractionRing C.R)ˣ) : FractionRing C.R) *
        ∏ j : Fin C.N, algebraMap C.R (FractionRing C.R) (C.ψ (MvPolynomial.X (.inr j))) ^ z j = 1 := by
      rw [← Units.val_one, ← mul_inv_cancel (Units.map (algebraMap C.R (FractionRing C.R) : C.R →* FractionRing C.R) w)]
      simp [w, map_prod, Units.coe_prod, map_zpow]
      refine inv_mul_cancel₀ (Finset.prod_ne_zero_iff.2 fun j _ => zpow_ne_zero _ ?_)
      exact (map_ne_zero_iff _ (IsFractionRing.injective C.R (FractionRing C.R))).2 (C.tor j).ne_zero
    have hl : ∏ i, algebraMap C.R (FractionRing C.R) (C.t i) ^ (((n : ℤ) • C.δ i) a b) =
        ∏ k : Fin C.m, algebraMap C.R (FractionRing C.R) (C.ψ (MvPolynomial.X (.inl k))) ^
          ((n : ℤ) * (C.ε (.inl k) : LinearMap.BilinForm ℤ (Fin C.T.r → ℤ)) (C.e a) (C.e b)) := by
      rfl
    rw [hl, _root_.mul_assoc, mul_comm (∏ j : Fin C.N, _), hw, _root_.mul_one]
  · have h : Module.finrank ℤ C.Q.X = C.T.r := by
      rw [C.e.toIntLinearEquiv.finrank_eq, Module.finrank_fin_fun]
    have := C.genus
    omega
  · exact C.cone.pull_equiv C.e.toIntLinearEquiv
  · intro z hz
    obtain ⟨k, hk⟩ := C.defin (C.e z) (by simpa using hz)
    exact ⟨k, hk⟩
  · intro k hk
    letI := C.ψ.toAlgebra
    haveI : Module.Flat (MvPolynomial (Fin C.m ⊕ Fin C.N) C.W) C.R := C.compl.2.2.1
    have hreg := Module.Flat.isSMulRegular_of_nonZeroDivisors (M := C.R) (X_mem_nonZeroDivisors C.W (Sum.inl k : Fin C.m ⊕ Fin C.N))
    apply one_ne_zero (α := C.R)
    apply hreg
    show C.ψ (MvPolynomial.X (.inl k)) * 1 = C.ψ (MvPolynomial.X (.inl k)) * 0
    rw [show C.ψ (MvPolynomial.X (.inl k)) = 0 from hk]; simp

end GlobalTheory.TChart.Taut
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.closedPoint_of_values_in_small_algClosed : ∀ (F A R K : Type) [Field F] [NumberField F] [CommRing A] [IsDomain A] [CommRing R] [IsLocalRing R] [Field K] (b : F →+* A), b.EssFiniteType → ∀ ψ : A →+* R, GlobalTheory.TChart.IsComplAt ψ → ∀ (ev : R →+* K) (k₀ : Subfield K), Nonempty (k₀ →+* AlgebraicClosure (ResidueField R)) → (∀ a, ev (ψ a) ∈ k₀) → (∀ r ∈ maximalIdeal R, ev r = 0) ∧ ∀ r, ev r ∈ k₀ := by
  first | exact @GlobalTheory.PointAlg.closed_point_of_values | exact GlobalTheory.PointAlg.closed_point_of_values | (intros; apply GlobalTheory.PointAlg.closed_point_of_values <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical

theorem _root_.GlobalTheory.T.traitsOfModuliPoint_have_isomorphic_proportional_lattices : UTraitUniqSt := by
  first | exact @GlobalTheory.UPoinc.uTraitUniqSt_holds | exact GlobalTheory.UPoinc.uTraitUniqSt_holds | (intros; apply GlobalTheory.UPoinc.uTraitUniqSt_holds <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.UChart.FromBaseAlong

theorem gm_comp_map {X Y Z : Scheme.{0}} (f : Z ⟶ Y) (g : Y ⟶ X) (z : Z) (U : X.Opens) (h : g (f z) ∈ U)
    (a : Γ(X, U)ˣ) :
    Units.map (f.stalkMap z).hom.toMonoidHom (gm g (f z) U a) = gm (f ≫ g) z U a := by
  apply Units.ext
  show (f.stalkMap z).hom (gm g (f z) U a).val = _
  rw [← gs_unit (f ≫ g) z U h, ← gs_unit g (f z) U h, ← gs_pull f g z U h, gs_eq f z (g ⁻¹ᵁ U) h, gs_eq g (f z) U h]
  exact Scheme.Hom.germ_stalkMap_apply f (g ⁻¹ᵁ U) z h _

theorem val_comp_map {X Y Y' Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (t : LB.Gen (LB.LinComb L φ ε)) (r : Z ⟶ Y') (g : Y' ⟶ Y) (z : Z) {J : (Z ⟶ X) → L.ι} (hJ : Good L z J) :
    Units.map (r.stalkMap z).hom.toMonoidHom (val t g (r z) (fun ψ => J (r ≫ ψ))) = val t (r ≫ g) z J := by
  rw [val_of t (r ≫ g) z J (fun k => J (r ≫ g ≫ φ k)) (fun k => by rw [Category.assoc])]
  exact gm_comp_map r g z _ (Set.mem_iInter.2 fun k => hJ (r ≫ g ≫ φ k)) _

theorem fromBase_along : ∀ {R : Type} [CommRing R] [IsDomain R] (Q : DegPre R) (τ₀ : Gens Q) {W₀ : Type} [CommRing W₀] (ιb : W₀ →+* R), FromBase Q τ₀ ιb → ∃ (B₀ : Over (Sp W₀)) (_ : GrpObj B₀) (M₀ : LB B₀.left) (c₀ : Q.X → (Sp W₀ ⟶ B₀.left)) (τ₁ : ∀ a b : Q.X, LB.Gen (LB.LinComb M₀ (K := Fin 4) ![c₀ (a + b), c₀ a, c₀ b, c₀ 0] ![-1, 1, 1, -1])) (β : Q.P.A.left ⟶ B₀.left) (w : LB.Iso Q.P.L (M₀.pull β)), IsAbelianScheme B₀ ∧ M₀.IsLB ∧ IsGrpPullback Q.P.A B₀ (spMap ιb) β ∧ w.IsGen ∧ (∀ a, cpt Q a ≫ β = spMap ιb ≫ c₀ a) ∧ (∀ a b, (τ₁ a b).IsGen) ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ Sp R) (a b : Q.X) (zz : Z) (J : (Z ⟶ Q.P.A.left) → Q.P.L.ι) (J₀ : (Z ⟶ B₀.left) → M₀.ι), Good Q.P.L zz J → Good M₀ zz J₀ → val (τ₀ a b) r zz J = gm (r ≫ cpt Q (a + b)) zz _ (w.s (fun _ => J₀ (r ≫ cpt Q (a + b) ≫ β), J (r ≫ cpt Q (a + b)))) * (gm (r ≫ cpt Q a) zz _ (w.s (fun _ => J₀ (r ≫ cpt Q a ≫ β), J (r ≫ cpt Q a))))⁻¹ * (gm (r ≫ cpt Q b) zz _ (w.s (fun _ => J₀ (r ≫ cpt Q b ≫ β), J (r ≫ cpt Q b))))⁻¹ * gm (r ≫ cpt Q 0) zz _ (w.s (fun _ => J₀ (r ≫ cpt Q 0 ≫ β), J (r ≫ cpt Q 0))) * val (τ₁ a b) (r ≫ spMap ιb) zz J₀ := by
  intro R _ _ Q τ₀ W₀ _ ιb ⟨B₀, i, M₀, c₀, τ₁, β, w, h₁, h₂, h₃, h₄, h₅, h₆, h⟩
  refine ⟨B₀, i, M₀, c₀, τ₁, β, w, h₁, h₂, h₃, h₄, h₅, h₆, fun Z r a b zz J J₀ hJ hJ₀ => ?_⟩
  have e := congrArg (Units.map (r.stalkMap zz).hom.toMonoidHom)
    (h a b (r zz) (fun ψ => J (r ≫ ψ)) (fun ψ => J₀ (r ≫ ψ)) (fun ψ => hJ (r ≫ ψ)) (fun ψ => hJ₀ (r ≫ ψ)))
  have g : ∀ x : Q.X, Units.map (r.stalkMap zz).hom.toMonoidHom
      (gm (cpt Q x) (r zz) _ (w.s (fun _ => J₀ (r ≫ cpt Q x ≫ β), J (r ≫ cpt Q x)))) =
      gm (r ≫ cpt Q x) zz _ (w.s (fun _ => J₀ (r ≫ cpt Q x ≫ β), J (r ≫ cpt Q x))) := fun x =>
    gm_comp_map r (cpt Q x) zz _
      (show cpt Q x (r zz) ∈ (M₀.pull β).U (fun _ => J₀ (r ≫ cpt Q x ≫ β)) ⊓ Q.P.L.U (J (r ≫ cpt Q x)) from
        ⟨Set.mem_iInter.2 fun _ => hJ₀ (r ≫ cpt Q x ≫ β), hJ (r ≫ cpt Q x)⟩) _
  have v₀ := val_comp_map (τ₀ a b) r (𝟙 _) zz hJ
  have v₁ := val_comp_map (τ₁ a b) r (spMap ιb) zz hJ₀
  rw [Category.comp_id] at v₀
  rw [map_mul, map_mul, map_mul, map_mul, map_inv, map_inv] at e
  exact v₀.symm.trans (e.trans (congrArg₂ (· * ·) (congrArg₂ (· * ·) (congrArg₂ (· * ·) (congrArg₂ (· * ·)
    (g (a + b)) (congrArg (·⁻¹) (g a))) (congrArg (·⁻¹) (g b))) (g 0)) v₁))

end GlobalTheory.UChart.FromBaseAlong
end
end
