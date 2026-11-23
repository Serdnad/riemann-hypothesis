module

public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle042
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle033
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle011
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle029
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
import Development.AbelianVarietyTheory.Definitions.CMLattices.IsDiffOf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.LminorSubmatrixCastSucc
import Development.AbelianVarietyTheory.Definitions.CMLattices.IntegralOf
import Development.AbelianVarietyTheory.Definitions.CMLattices.IsCyclotomicExtensionCyclotomicField28
import Development.AbelianVarietyTheory.Definitions.CMLattices.LamLetters
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DualRestrictSurjectiveOfIsTorsionFreeQuotient
import Formalism.LocalToGlobal.CMDeterminantIdeals.DetIdeal
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.ConjSymm

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

namespace GlobalTheory.CM

theorem exists_oAct_extend_dedekind : (∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (G G' : Over (Sp T)) [GrpObj G] [GrpObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ f : (Over.pullback (spMap (algebraMap T K))).obj G ⟶ (Over.pullback (spMap (algebraMap T K))).obj G', IsMonHom f → ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback (spMap (algebraMap T K))).map F = f) → ∀ (R K : Type) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K] (O : Type) [CommRing O] (G : Over (Sp R)) [GrpObj G] (G₀ : Over (Sp K)) [GrpObj G₀] (φ : G₀.left ⟶ G.left), IsAbelianScheme G → IsGrpPullback G₀ G (spMap (algebraMap R K)) φ → ∀ a₀ : OAct O G₀, ∃ a : OAct O G, ∀ c, (a₀.act c).left ≫ φ = φ ≫ (a.act c).left := by
  intro H R K _ _ _ _ _ O _ G _ G₀ _ φ hG hφ a₀
  have key := fun c => GlobalTheory.T.abelianScheme_hom_extends_dedekind_of_isGrpPullback_alt H R K G G G₀ G₀ φ φ hG hG hφ hφ (a₀.act c) (a₀.hom c)
  choose F hF hc hu using key
  refine ⟨⟨F, hF, ?_, ?_, ?_⟩, hc⟩
  · refine (hu 1 (𝟙 G) ?_).symm
    rw [a₀.one]
    simp
  · intro a b
    refine (hu (a * b) (F a ≫ F b) ?_).symm
    rw [a₀.mul, Over.comp_left, Over.comp_left, Category.assoc, hc b, ← Category.assoc, hc a, Category.assoc]
  · intro a b
    refine (hu (a + b) (F a * F b) ?_).symm
    let ψ : Over.mk (G₀.hom ≫ spMap (algebraMap R K)) ⟶ G := Over.homMk φ hφ.1.w
    have h := hφ.2 G₀ (a₀.act a) (a₀.act b) (ψ ≫ F a) (ψ ≫ F b) (hc a).symm (hc b).symm
    rw [a₀.add, ← h, ← MonObj.comp_mul]
    rfl

end GlobalTheory.CM
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

set_option backward.isDefEq.respectTransparency false

namespace GlobalTheory.IsoDescent

theorem exists_gen_pull_div_iff {X Y : Scheme.{0}} (f : Y ⟶ X) {N N' : LB X} (hN : N.IsLB) (hN' : N'.IsLB) :
    (∃ t : LB.Gen ((LB.div N N').pull f), t.IsGen) ↔ LBIso (N.pull f) (N'.pull f) := by
  obtain ⟨Pic, groups, cl, pl, iso_iff, gen_iff, -, -, linComb, div⟩ :=
    CechPicMul.exists_picardGroup
  let _ := groups
  have pull_class {L : LB X} (hL : L.IsLB) :
      (L.pull f).IsLB ∧ cl (L.pull f) = pl f (cl L) := by
    simpa only [Fintype.prod_unique, zpow_one] using
      linComb X Y L hL PUnit (fun _ => f) (fun _ => 1)
  obtain ⟨hD, eD⟩ := div X N' N hN' hN
  obtain ⟨hDf, eDf⟩ := pull_class hD
  obtain ⟨hNf, eNf⟩ := pull_class hN
  obtain ⟨hN'f, eN'f⟩ := pull_class hN'
  rw [← gen_iff Y _ hDf, eDf, eD, map_div, div_eq_one, ← eNf, ← eN'f,
    iso_iff Y _ _ hNf hN'f]

theorem lbIso_of_field : ∀ (R k : Type) [CommRing R] [IsDedekindDomain R] [Field k] (β : R →+* k), Function.Injective β → ∀ (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A → ∀ (X' : Scheme.{0}) (π : X' ⟶ A.left) (p : X' ⟶ Sp k), IsPullback π p A.hom (spMap β) → ∀ N N' : LB A.left, N.IsLB → N'.IsLB → LBIso (N.pull (eSec A)) (N'.pull (eSec A)) → LBIso (N.pull π) (N'.pull π) → LBIso N N' := by
  intro R k _ _ _ β hβ A _ hA X' π p H N N' hN hN' he hπ
  have := hA.proper
  have := forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ A.hom hA.smooth hA.geomConnected
  let K := FractionRing R
  let δ : K →+* k := IsFractionRing.lift hβ
  have hδ : spMap δ ≫ spMap (algebraMap R K) = spMap β := by
    have e : δ.comp (algebraMap R K) = β := RingHom.ext fun x => IsFractionRing.lift_algebraMap hβ x
    rw [← e]
    exact (Spec.map_comp _ _).symm
  have H₀ := IsPullback.of_hasPullback A.hom (spMap (algebraMap R K))
  set π₀ := pullback.fst A.hom (spMap (algebraMap R K))
  set p₀ := pullback.snd A.hom (spMap (algebraMap R K))
  let q := H₀.lift π (p ≫ spMap δ) (by rw [Category.assoc, hδ, H.w])
  have hq : q ≫ π₀ = π := H₀.lift_fst _ _ _
  have H₁ : IsPullback q p p₀ (spMap δ) := by
    refine IsPullback.of_right ?_ (H₀.lift_snd _ _ _) H₀
    rw [hq, hδ]
    exact H
  obtain ⟨Pic, groups, cl, pl, iso_iff, gen_iff, -, comp, linComb, div⟩ :=
    CechPicMul.exists_picardGroup
  let _ := groups
  have pull_class {S T : Scheme.{0}} (f : T ⟶ S) {L : LB S} (hL : L.IsLB) :
      (L.pull f).IsLB ∧ cl (L.pull f) = pl f (cl L) := by
    simpa only [Fintype.prod_unique, zpow_one] using
      linComb S T L hL PUnit (fun _ => f) (fun _ => 1)
  obtain ⟨hD, eD⟩ := div A.left N' N hN' hN
  obtain ⟨hD₀, eD₀⟩ := pull_class π₀ hD
  have h₁ : ∃ t : LB.Gen (((LB.div N N').pull π₀).pull q), t.IsGen := by
    obtain ⟨hDq, eDq⟩ := pull_class q hD₀
    obtain ⟨hDπ, eDπ⟩ := pull_class π hD
    rw [← gen_iff X' _ hDq, eDq, eD₀, ← comp, hq, ← eDπ, gen_iff X' _ hDπ]
    exact (exists_gen_pull_div_iff π hN hN').2 hπ
  obtain ⟨t, ht⟩ := h₁
  have h₂ := FieldTriv.exists_gen_of_isPullback δ p₀ q p H₁ hD₀ t ht
  have h₃ := TrivDedekind.exists_gen_of_generic R K A hA _ π₀ p₀ H₀ _ hD
    ((exists_gen_pull_div_iff _ hN hN').2 he) h₂
  rwa [← gen_iff A.left _ hD, eD, div_eq_one, iso_iff A.left _ _ hN hN'] at h₃

end GlobalTheory.IsoDescent
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF


theorem _root_.GlobalTheory.T.exists_prod_polAV_add_g : Out.Laws → ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (P P' : Out.PolAV (Sp R)), ∃ (Q : Out.PolAV (Sp R)) (p : Q.A ⟶ P.A) (q : Q.A ⟶ P'.A), IsMonHom p ∧ IsMonHom q ∧ IsIso (lift p q) ∧ Q.g = P.g + P'.g := by
  first | exact @GlobalTheory.PolProd.exists_prod_polAV | exact GlobalTheory.PolProd.exists_prod_polAV | (intros; apply GlobalTheory.PolProd.exists_prod_polAV <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM Formalism.L2.Pj
open scoped ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.Frames GlobalTheory.LamT

namespace GlobalTheory.PurePer

open ReciprocityTheory.ChartRestriction.G.FD

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem emb_smul' (τ : E →+* ℂ) (a : E) (v : Fin r → E) :
    FD.Data.emb τ (a • v) = τ a • FD.Data.emb τ v := by
  funext k
  simp [FD.Data.emb]

theorem inv_mulVec_eq_zero {p : ℕ} (hp : p ≤ r) (M : Matrix (Fin r) (Fin r) ℂ) (hM : M.det ≠ 0)
    {u : Fin r → ℂ}
    (hu : u ∈ Submodule.span ℂ (Set.range fun a : Fin p => FD.col M (Fin.castLE hp a)))
    (k : Fin r) (hk : p ≤ (k : ℕ)) : (M⁻¹.mulVec u) k = 0 := by
  induction hu using Submodule.span_induction with
  | mem u hu =>
    obtain ⟨a, rfl⟩ := hu
    have h1 : (M⁻¹.mulVec (FD.col M (Fin.castLE hp a))) k = (M⁻¹ * M) k (Fin.castLE hp a) := by
      simp [Matrix.mulVec, dotProduct, Matrix.mul_apply, FD.col]
    have hne : k ≠ Fin.castLE hp a := by
      intro h
      have h2 := congrArg Fin.val h
      have h3 := a.isLt
      simp at h2
      omega
    show (M⁻¹.mulVec (FD.col M (Fin.castLE hp a))) k = 0
    rw [h1, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hM), Matrix.one_apply_ne hne]
  | zero => simp
  | add a b _ _ ha hb => rw [Matrix.mulVec_add, Pi.add_apply, ha, hb, add_zero]
  | smul c a _ ha => rw [Matrix.mulVec_smul, Pi.smul_apply, ha, smul_zero]

theorem perFr_pure : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : FD.DataX E r) (La : ℝ) (x : FD.Frame X.Ψ r) (lam : Fin r → Fin r → E), x ∈ X.toData.dom → FD.LamBasis X La x lam → ∀ (a : E) (j : Fin r) (τ : E →+* ℂ) (i : ℕ), ((j : ℕ) < X.p0 → τ ∈ X.Ψ → perFr X.toData x (a • lam j) τ i = 0) ∧ (X.p0 ≤ (j : ℕ) → τ ∉ X.Ψ → i < X.p0 → perFr X.toData x (a • lam j) τ i = 0) := by
  intro E _ _ _ r X La x lam hx hb a j τ i
  obtain ⟨-, -, ho, -, -, -, hsp⟩ := hb
  refine ⟨fun hj hτ => ?_, fun hj hτ hi => ?_⟩
  · unfold perFr
    rw [dite_eq_left hτ]
    split_ifs with h
    · refine inv_mulVec_eq_zero X.p0_le _ (hx ⟨τ, hτ⟩).1 ?_ _ (by simp)
      rw [hsp ⟨τ, hτ⟩, emb_smul']
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨j, hj⟩, rfl⟩)
    · rfl
  · unfold perFr
    rw [dite_eq_right hτ]
    split_ifs with h' h
    · have hm : FD.col (FD.mat x ⟨conjEmb τ, h'⟩) ⟨X.p0 - 1 - i, h⟩ ∈
          Submodule.span ℂ (Set.range fun a : Fin X.p0 =>
            FD.Data.emb (conjEmb τ) (lam (Fin.castLE X.p0_le a))) := by
        have := hsp ⟨conjEmb τ, h'⟩
        simp only at this
        rw [← this]
        exact Submodule.subset_span ⟨⟨X.p0 - 1 - i, by omega⟩, rfl⟩
      rw [emb_smul', FD.hermC_smul_right]
      refine mul_eq_zero_of_right _ ?_
      generalize FD.col (FD.mat x ⟨conjEmb τ, h'⟩) ⟨X.p0 - 1 - i, h⟩ = w at hm
      induction hm using Submodule.span_induction with
      | mem w hw =>
        obtain ⟨k, rfl⟩ := hw
        rw [FD.hermC_emb, ho _ j (by simpa using k.isLt) hj, map_zero]
      | zero => exact FD.hermC_zero_left _ _ _
      | add a b _ _ ha hb => rw [FD.hermC_add_left, ha, hb, add_zero]
      | smul c a _ ha => rw [FD.hermC_smul_left, ha, mul_zero]
    · rfl
    · rfl

end GlobalTheory.PurePer
end

end

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM


theorem _root_.GlobalTheory.T.lineBundleIso_descends_field_to_dedekindDomain : ∀ (R k : Type) [CommRing R] [IsDedekindDomain R] [Field k] (β : R →+* k), Function.Injective β → ∀ (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A → ∀ (X' : Scheme.{0}) (π : X' ⟶ A.left) (p : X' ⟶ Sp k), IsPullback π p A.hom (spMap β) → ∀ N N' : LB A.left, N.IsLB → N'.IsLB → LBIso (N.pull (eSec A)) (N'.pull (eSec A)) → LBIso (N.pull π) (N'.pull π) → LBIso N N' := by
  first | exact @GlobalTheory.IsoDescent.lbIso_of_field | exact GlobalTheory.IsoDescent.lbIso_of_field | (intros; apply GlobalTheory.IsoDescent.lbIso_of_field <;> assumption)

end
end
