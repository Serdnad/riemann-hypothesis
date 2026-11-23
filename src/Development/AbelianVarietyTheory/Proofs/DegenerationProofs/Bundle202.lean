module

public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle118
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PeriodicValuation
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle012
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.IsThetaPtOverMove
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle083
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle031
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle130
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle133
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle002
public import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle007
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.Bundle001
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle005
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle193
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle176
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle168
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle041
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle184
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle199
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle192
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle201
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ConstBFMul
import Development.AbelianVarietyTheory.Definitions.Degenerations.InducedModelMorphismCompStructureMap
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SpanEqTopOfFunctionals
import Development.AbelianVarietyTheory.Definitions.Degenerations.SepticCharacterInjective

@[expose] public section

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex

theorem _root_.GlobalTheory.T.mem_thetaPoints_of_closure_coset_condition : HV → Laws6 → GlobalTheory.LN.UDvrSt → GlobalTheory.LN.HomExtSt → ThetaPtDeterminesSt → EndDeterminedOnTorsionSt → ThetaUnifAV → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (W₀ : ValuationSubring ℂ) (Y : Model Xo c (c.V W₀).subtype), ∀ (K : Type) [Field K] [IsAlgClosed K] [CharZero K] (n j : ℕ) (ρ z : K) (v : D.La → K), n.Prime → Odd n → 2 ≤ j → Compat H ((n ^ j) ^ 2) z ρ → (∀ G, VanishC D (n ^ j) G → MvPolynomial.eval₂ (cf z ρ) v G = 0) → (∀ x, ∃ h, v (x + n ^ (j - 1) • h) ≠ 0) → ∃ o : Full D K, o.ρ = ρ ∧ (o.I.ζ ((n ^ j) ^ 2) : K) = z ∧ o.Theta (n ^ j) v := by
  first | exact @GlobalTheory.Ex.ClosurePoint.exists_full_of_closure_of_cosets | exact GlobalTheory.Ex.ClosurePoint.exists_full_of_closure_of_cosets | (intros; apply GlobalTheory.Ex.ClosurePoint.exists_full_of_closure_of_cosets <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.ZH

namespace GlobalTheory.ZH

theorem eq_mul_of_isTwistPull {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} (hL : L.IsLB) {T : Over S}
    {m : T ⊗ A ⟶ A} {a b : ℤ} {α : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T A).left, m.left] ![a, -b])}
    {s s₀ : LB.Sec (LPow A L b T)} {t t₀ : LB.Sec (LPow A L a T)} {c : Γ(T.left, ⊤)}
    (e : ∀ j, s.f j = liftFun A _ c * s₀.f j)
    (h : IsTwistPull A L (lift (fst T A) m) m (lift_snd _ _) a b α s t)
    (h₀ : IsTwistPull A L (lift (fst T A) m) m (lift_snd _ _) a b α s₀ t₀) (j) :
    t.f j = liftFun A _ c * t₀.f j := by
  have f₁ : (lift (fst T A) m).left ≫ (fst T A).left = (fst T A).left := by
    rw [← Over.comp_left, lift_fst]
  have key : (SecM.ofSec A t : SecM A L a T) = SecM.ofSec A (SecM.toSec A (c • SecM.ofSec A t₀)) :=
    VVRank.ofSec_ext A hL fun y J hJ => by
      rw [ThetaPtMove.sv_of_eq_mul (s := SecM.toSec A (c • SecM.ofSec A t₀)) (t := t₀) (c := c) (fun j => rfl) _ y hJ,
        VVRank.sv_of_isTwistPull A h _ y hJ, VVRank.sv_of_isTwistPull A h₀ _ y hJ,
        ThetaPtMove.sv_of_eq_mul e _ y hJ]
      simp only [Category.assoc, f₁]
      ring
  exact congrArg (fun q => q.1 j) key

theorem nuGe_translate_pull_smul : LL → TwistBCSpanStatement → TWM.VRatioGtStatement → TWStatement → UUStatement → AllUV fun {V} _ _ _ {ϖ} hϖ {D} Q {F} _ _ {v} hv {A} {G} _ _ U => ∀ w₀ ρ, NormW U.toUnifPre w₀ ρ → ∀ (th₀ : SecA A F 1) (ϑ : Fam D.toPre F 1), U.ExpandsF F 1 w₀ th₀ ϑ → Prim D Q v ϑ → ∀ (m N : ℕ), N = m ^ 2 → Odd m → IsUnit (m : V) → ∀ (c : F) (r : ℚ) (th : SecA A F 1), (r : WithTop ℚ) ≤ v c → (∀ j, th.f j = liftFun A.A _ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom c) * th₀.f j) → ∀ (α : LB.Gen (LB.LinComb A.L (K := Fin 2) ![(snd (TFK (R := V) F) A.A).left, (snd (TFK (R := V) F) A.A ^ m).left] ![(N : ℤ), -((1 : ℕ) : ℤ)])), α.IsGen → LB.Gen.Corr A.L _ _ _ _ (LB.pullGen A.L _ _ α (ptSecT A.A 1).left) (rigT A.A A.L ρ (TFK (R := V) F) ((N : ℤ) - 1)) → ∀ (s₁ t : SecA A F N) (x : TFK (R := V) F ⟶ A.A) (θ : ThetaGrp A.A A.L N (TFK (R := V) F)) (s : Fam D.toPre F N), IsTwistPull A.A A.L (mulT A.A _ m) (snd _ A.A ^ m) (lift_snd _ _) (N : ℤ) ((1 : ℕ) : ℤ) α th s₁ → x ^ N = 1 → SymLift A.A A.L N N x θ → IsActOf A.A A.L N θ s₁ t → U.ExpandsF F N w₀ t s → NuGe D Q F v N s r := by
  intro hLL hBC hVR hTW hUU V _ _ _ _ hc ϖ hϖ D Q hQ F _ _ _ v hv A G _ _ hG U w₀ ρ hN th₀ ϑ hth hprim m N hNm hm hmu
    c r th hr eth α hα hn s₁ t x θ s hs₁ hx hθ ht hs
  subst hNm
  have hA : AdmBase V (maximalIdeal V) := ⟨inferInstance, inferInstance, inferInstance, hc⟩
  have hN1 : 1 ≤ m ^ 2 := Nat.one_le_pow _ _ hm.pos
  obtain ⟨hB, hlin⟩ := expBijF_and_expandsF_lin hLL V _ hA D A G hG U
  obtain ⟨hB₁, -⟩ := hB F (m ^ 2) hN1 w₀ hN.1
  let T := TFK (R := V) F
  let κ : F ≃+* Γ(T.left, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of F)).symm.commRingCatIsoToRingEquiv
  obtain ⟨u₁, hu₁⟩ := VVRank.exists_isTwistPull A.A (ψ := mulT A.A T m) (hm := lift_snd _ _) A.isLB hα th₀
  obtain ⟨t₀, ht₀⟩ := VVRank.exists_isTwistPull A.A (ψ := translT A.A θ.pt) (hm := lift_snd _ _) A.isLB θ.isGen u₁
  obtain ⟨c₀, hc₀⟩ := NormTheta.exists_value A.isLB hN.2.1 _ t₀
  obtain ⟨c', rfl⟩ := κ.surjective c₀
  obtain ⟨s₀, hs₀, -⟩ := hB₁ t₀
  have hP := GlobalTheory.T.primitive_expansion_thetaPullback_heisenbergTranslates hLL hBC hVR hTW hUU V hc ϖ hϖ D Q hQ F v hv A G hG U w₀ ρ hN th₀ ϑ hth hprim m hm hmu
    x t₀ c' s₀ hx ⟨α, u₁, θ, hα, hn, hu₁, hθ, ht₀, hc₀⟩ hs₀
  have e₁ := eq_mul_of_isTwistPull (c := κ c) A.isLB eth hs₁ hu₁
  have e₂ := eq_mul_of_isTwistPull (c := κ c) A.isLB e₁ ht ht₀
  have h₁ := hlin F (m ^ 2) w₀ t₀ t₀ t s₀ s₀ (c - 1) hs₀ hs₀ fun j => by
    refine (e₂ j).trans ?_
    have : κ c • SecM.ofSec A.A t₀ = κ (c - 1) • SecM.ofSec A.A t₀ + SecM.ofSec A.A t₀ := by
      rw [map_sub, map_one, sub_smul, one_smul, sub_add_cancel]
    exact congrArg (fun q => q.1 j) this
  rw [sub_smul, one_smul, sub_add_cancel] at h₁
  have := NuGe.smul Q hr ((isSmul_iff c s₀ s).2 ((hB₁ t).unique hs h₁)) hP.1
  rwa [zero_add] at this

end GlobalTheory.ZH
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.LN GlobalTheory.Ex GlobalTheory.OneBasis

theorem _root_.GlobalTheory.T.torusExtension_torsion_mem_unitThetaConstantGroup : LL → TwistBCSpanStatement → TWM.VRatioGtStatement → TWStatement → UUStatement → AllUV fun {V} _ _ _ {ϖ} hϖ {D} Q {F} _ _ {v} hv {A} {G} _ _ U => ∀ w₀ ρ, NormW U.toUnifPre w₀ ρ → ∀ (th : SecA A F 1) (ϑ : Fam D.toPre F 1), U.ExpandsF F 1 w₀ th ϑ → Prim D Q v ϑ → ∀ n j : ℕ, n.Prime → Odd n → IsUnit (n : V) → 2 ≤ j → ∀ x : TFK (R := V) F ⟶ A.A, FromGt U.toUnifPre (n ^ j) x → x ∈ unitGrp v ρ th (n ^ j) := by
  first | exact @GlobalTheory.OneBasis.UnitGen.fromGt_mem_unitGrp | exact GlobalTheory.OneBasis.UnitGen.fromGt_mem_unitGrp | (intros; apply GlobalTheory.OneBasis.UnitGen.fromGt_mem_unitGrp <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.ThetaPtMove GlobalTheory.ConstFam
open GlobalTheory.Ex.OneGen GlobalTheory.UT


theorem _root_.GlobalTheory.T.normalisedThetaConstants_primitive_integral_one_unit : HV → AllUV fun {V} _ _ _ {ϖ} hϖ {D} Q {F} _ _ {v} hv {A} {G} _ _ U => ∀ w₀ ρ, NormW U.toUnifPre w₀ ρ → ∀ (th : SecA A F 1) (ϑ : Fam D.toPre F 1), U.ExpandsF F 1 w₀ th ϑ → Prim D Q v ϑ → ∀ m : ℕ, Odd m → IsUnit (m : V) → 3 ≤ m → (∀ x (c : F), ThG A.A A.L ρ m th x (fnOf c) → 0 ≤ v c) ∧ ∃ x, ∃ c : F, ThG A.A A.L ρ m th x (fnOf c) ∧ v c = 0 := by
  first | exact @GlobalTheory.Ex.OneGen.thG_val_of_prim | exact GlobalTheory.Ex.OneGen.thG_val_of_prim | (intros; apply GlobalTheory.Ex.OneGen.thG_val_of_prim <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

namespace GlobalTheory.ZH.GeoExist

theorem link_smul {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {S : ThetaSys o Ω} {ρ : S.Real} {p : ℕ}
    [Fact p.Prime] {y₀ : S.R →+* PadicAlgCl p} (u : ρ.UTest p y₀) (σ : S.J → (u.H S.N).Sec)
    (b : Matrix S.J S.J (FractionRing u.V)) (h : u.Link σ b) (c : FractionRing u.V) (hc : c ≠ 0) :
    u.Link σ (c • b) := by
  intro a v hv
  have hc' : algebraMap (FractionRing u.V) (PadicAlgCl p) c ≠ 0 := (map_ne_zero _).2 hc
  have h₁ := CrdCalc.crd_smul (Units.mk0 _ hc') (h a v hv)
  convert h₁ using 1
  ext j
  simp [Matrix.mulVec, dotProduct, Finset.mul_sum, _root_.mul_assoc]

theorem hasGeo_of_hasU : GlobalTheory.UT.LL → UTorsSt → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real), S.Big → ρ.HasU → ρ.HasGeo := by
  intro hL hT o Ω _ _ _ _ S ρ hB hU p _ y₀ hy Fs
  obtain ⟨u, l, τ, hm, hF⟩ := hU p y₀ hy Fs
  obtain ⟨σ, cls, f, hb⟩ := GlobalTheory.T.exists_adapted_basis_sections_mod_k hL o Ω S ρ p y₀ u l S.N (le_trans one_le_two S.N_ge) S.J ρ.card
  obtain ⟨md⟩ := GlobalTheory.T.uniformisedModel_adaptedBasis_is_modelWithSeries hL hT o Ω S ρ p y₀ u l σ cls f hb
  obtain ⟨b, hd, hl⟩ := GlobalTheory.T.exists_invertible_adaptedBasis_link_matrix hL o Ω S ρ p y₀ u l σ cls f hb
  obtain ⟨c, hc, hs⟩ := GlobalTheory.T.testLattice_eq_span_model_sections hL o Ω S ρ p y₀ u l τ σ cls md b hB hy hm hl hd
  have hl' := link_smul u σ b hl c hc
  exact ⟨⟨u, l, τ, hm, σ, cls, md, c • b, hl', hs,
    GlobalTheory.T.adaptedBasis_rows_have_class_weight hL hT o Ω S ρ p y₀ u l σ cls f hb (c • b) hl'⟩, hF⟩

end GlobalTheory.ZH.GeoExist
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.UT
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TestFibre

theorem _root_.GlobalTheory.T.torusPoints_level_weights_from_orthogonal_labels : Laws → Laws2 → UTorsSt → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (l : u.Lab), (∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1) → ∀ (x : S.Gam → (TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A)), PtsOver u x → ∀ t : S.perp l.yy.ker, ∃ (τ : Multiplicative u.D.toPre.X →* (PadicAlgCl p)ˣ) (q : QkPt u.D.toPre (PadicAlgCl p) S.N), q.y = 0 ∧ IsTor τ q.g ∧ QkToAkU u.U.toUnifPre (PadicAlgCl p) S.N q (x (S.r • (t : S.Gam))) ∧ ∀ β, (τ (Multiplicative.ofAdd β) : PadicAlgCl p) = y₀ (algebraMap o S.R S.ζN) ^ (l.wt β t).val := by
  first | exact @GlobalTheory.TestFibre.torus_points_level_weights | exact GlobalTheory.TestFibre.torus_points_level_weights | (intros; apply GlobalTheory.TestFibre.torus_points_level_weights <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.thetaConstant_bounded_by_shortestVector : Laws → Laws2 → UTorsSt → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (l : u.Lab), (∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1) → (∀ x, y₀ ⟨S.th x, S.th_mem x⟩ ≠ 0 → ∃ w : u.D.toPre.X, l.yy x = QuotientAddGroup.mk w ∧ ‖y₀ ⟨S.th x, S.th_mem x⟩‖ ≤ S.delta y₀ * Real.exp (-(l.q w / ((S.r * S.N : ℕ) : ℝ) ^ 2))) := by
  first | exact @GlobalTheory.ZH.TestVal.main | exact GlobalTheory.ZH.TestVal.main | (intros; apply GlobalTheory.ZH.TestVal.main <;> assumption)
end
