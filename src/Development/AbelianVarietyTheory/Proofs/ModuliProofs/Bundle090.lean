module

public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle005
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsDomainAndIsIntegrallyClosedLocalizationOfIsInv
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.ExistsIsAffineOpenOfFiniteOpensProj
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.ExistsSecNonzeroLocusEqOfLbIso
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSmulApplyEqOfEqOnInvariants
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.PolarizedAbelianEmbeddingBySections
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle005
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LocGenOfTrivial
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SecMInvariantEqBotOrUnivAtGeometricPoint
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SpanEqTopOfFunctionals
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ThetaGrpActsLinearly
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsIsoAppTopOfIsAffine
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle004
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle043
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle086
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle027
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle070
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFiniteSchemeLatticeTorsionHomPrimitiveRoot
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.WittVector.IsPoly
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DivCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle001

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

noncomputable section

namespace GlobalTheory.EmbSpan

open ReciprocityTheory.ChartRestriction.G.Out

theorem pt_pow_and_surjective (hL : Laws) {S S' : Scheme.{0}} [IsLocallyNoetherian S'] (P : PolAV S) (f : S' ⟶ S)
    (n : ℕ) (hn : 1 ≤ n) : (∀ θ : ThetaGrp P.A P.L n (Over.mk f), θ.pt ^ n = 1) ∧
      Surjective (mulT P.A (Over.mk f) n).left := by
  obtain ⟨P', g, hg, -, hmul, hiso⟩ := hL.polBaseChange S S' f P
  obtain ⟨w, hw⟩ := LBIso.symm hiso
  have hw' := (isGen_iff w).1 hw
  obtain ⟨h, k, hk, -, hs, hf, -⟩ := GeomPointSections.exists_totalIso hg hmul
  let Φ : ∀ T : Over S', (T ⟶ P'.A) →* (Over.mk (T.hom ≫ f) ⟶ P.A) := fun T =>
    MonoidHom.mk' (toBase hg.w) (hmul T)
  have c' : (fst (baseOver S') P'.A).left = (baseOver S' ⊗ P'.A).hom :=
    (Category.comp_id _).symm.trans (Over.w (fst (baseOver S') P'.A))
  let H : Over.mk ((baseOver S' ⊗ P'.A).hom ≫ f) ⟶ Over.mk f ⊗ P.A := Over.homMk h (by
    have e := Over.w (fst (Over.mk f) P.A)
    exact (congrArg (h ≫ ·) e.symm).trans ((Category.assoc _ _ _).symm.trans
      (congrArg (· ≫ f) (hf.trans c'))))
  have Hs : H ≫ snd (Over.mk f) P.A = Φ _ (snd (baseOver S') P'.A) := Over.OverMorphism.ext hs.symm
  constructor
  · intro θ
    have sq : θ.pt.left ≫ P.A.hom = 𝟙 S' ≫ f := (Over.w θ.pt).trans (Category.id_comp f).symm
    let x' : baseOver S' ⟶ P'.A := Over.homMk (hg.lift _ _ sq) (hg.lift_snd _ _ _)
    have ex : x'.left ≫ g = θ.pt.left := hg.lift_fst _ _ _
    have e₀ : H ≫ fst (Over.mk f) P.A ≫ θ.pt = Φ _ (fst (baseOver S') P'.A ≫ x') :=
      Over.OverMorphism.ext ((Category.assoc h _ _).symm.trans ((congrArg₂ (· ≫ ·) hf ex.symm).trans
        (Category.assoc _ _ _).symm))
    have e₁ : H ≫ translPt P.A θ.pt = Φ _ (translPt P'.A x') := by
      refine (MonObj.comp_mul H (fst (Over.mk f) P.A ≫ θ.pt) (snd (Over.mk f) P.A)).trans
        (Eq.trans ?_ (map_mul (Φ _) (fst (baseOver S') P'.A ≫ x') (snd (baseOver S') P'.A)).symm)
      rw [e₀, Hs]
    have e₂ : h ≫ (translPt P.A θ.pt).left = (translPt P'.A x').left ≫ g := congrArg (fun q => q.left) e₁
    obtain ⟨t₁, h₁⟩ := KerPow.HasGen.pull (L := P.L)
      (φ := ![(snd (Over.mk f) P.A).left, (translPt P.A θ.pt).left]) (ε := ![(n : ℤ), -n]) ⟨θ.φ, θ.isGen⟩ h
      (φ' := fun i => ![(snd (baseOver S') P'.A).left, (translPt P'.A x').left] i ≫ g)
      (fun i => by fin_cases i; exacts [hs.symm, e₂])
    obtain ⟨t₂, h₂⟩ := exists_down hw' P.isLB P'.isLB t₁ h₁
    have hx : x' ^ n = 1 := (hL.kerPow S' P' n hn _ x').1 fun _ =>
      ⟨⊤, trivial, _, LB.isGen_genPull _ t₂ h₂ _⟩
    let j : Over.mk ((baseOver S').hom ≫ f) ⟶ Over.mk f := Over.homMk (𝟙 S') rfl
    have ej : j ≫ θ.pt = Φ _ x' := Over.OverMorphism.ext ((Category.id_comp _).trans ex.symm)
    have : j ≫ θ.pt ^ n = j ≫ 1 := by
      rw [MonObj.comp_pow, ej, ← map_pow, hx, map_one, MonObj.comp_one]
    exact Over.OverMorphism.ext ((Category.id_comp _).symm.trans
      ((congrArg (fun q => q.left) this).trans (Category.id_comp _)))
  · have s₁ := VVRank.surjective_mulT P'.A n (hL.mulN S' P' n hn).2.2.1 (baseOver S')
    have s₂ : Surjective h := by
      have : Surjective (k ≫ h) := by rw [hk]; infer_instance
      exact Surjective.of_comp k h
    have t₁ : (mulT P.A (Over.mk f) n).left ≫ (fst (Over.mk f) P.A).left = (fst (Over.mk f) P.A).left :=
      congrArg (fun q => q.left) (lift_fst (fst (Over.mk f) P.A) (snd (Over.mk f) P.A ^ n))
    have t₂ : (mulT P.A (Over.mk f) n).left ≫ (snd (Over.mk f) P.A).left = (snd (Over.mk f) P.A ^ n).left :=
      congrArg (fun q => q.left) (lift_snd (fst (Over.mk f) P.A) (snd (Over.mk f) P.A ^ n))
    have t₁' : (mulT P'.A (baseOver S') n).left ≫ (fst (baseOver S') P'.A).left = (fst (baseOver S') P'.A).left :=
      congrArg (fun q => q.left) (lift_fst (fst (baseOver S') P'.A) (snd (baseOver S') P'.A ^ n))
    have t₂' : (mulT P'.A (baseOver S') n).left ≫ (snd (baseOver S') P'.A).left =
        (snd (baseOver S') P'.A ^ n).left :=
      congrArg (fun q => q.left) (lift_snd (fst (baseOver S') P'.A) (snd (baseOver S') P'.A ^ n))
    have e₁ : H ≫ snd (Over.mk f) P.A ^ n = Φ _ (snd (baseOver S') P'.A ^ n) := by
      rw [MonObj.comp_pow, Hs, map_pow]
    have e₂ : h ≫ (snd (Over.mk f) P.A ^ n).left = (snd (baseOver S') P'.A ^ n).left ≫ g :=
      congrArg (fun q => q.left) e₁
    have ext₁ : ∀ {Z : Scheme.{0}} {r r' : Z ⟶ (Over.mk f ⊗ P.A).left},
        r ≫ (fst (Over.mk f) P.A).left = r' ≫ (fst (Over.mk f) P.A).left →
        r ≫ (snd (Over.mk f) P.A).left = r' ≫ (snd (Over.mk f) P.A).left → r = r' :=
      fun e e' => pullback.hom_ext e e'
    have e : (mulT P'.A (baseOver S') n).left ≫ h = h ≫ (mulT P.A (Over.mk f) n).left := ext₁
      (by rw [Category.assoc, Category.assoc, t₁, hf, t₁'])
      (by rw [Category.assoc, Category.assoc, t₂, ← hs, ← Category.assoc, t₂', e₂])
    have : Surjective (h ≫ (mulT P.A (Over.mk f) n).left) := by rw [← e]; infer_instance
    exact Surjective.of_comp h _

theorem exists_pow_eq {G : Type} [CommGroup G] {r N u v : ℕ} (hN : N = u * v) (hN0 : N ≠ 0) (p : Fin r → G)
    (hp : ∀ i, p i ^ N = 1) (hb : ∀ y : G, y ^ N = 1 → ∃! c : Fin r → ZMod N, ∏ i, p i ^ (c i).val = y)
    (y : G) (hy : y ^ u = 1) : ∃ a : Fin r → ZMod N, (∏ i, p i ^ (a i).val) ^ v = y := by
  have : NeZero N := ⟨hN0⟩
  have hu : u ≠ 0 := fun h => hN0 (by rw [hN, h, zero_mul])
  obtain ⟨c, hc, -⟩ := hb y (by rw [hN, pow_mul, hy, one_pow])
  have h0 : (fun i => (((c i).val * u : ℕ) : ZMod N)) = 0 := by
    refine (hb 1 (one_pow _)).unique ?_ (by simp)
    rw [← hy, ← hc, ← Finset.prod_pow]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [ZMod.val_natCast, ← pow_eq_pow_mod _ (hp i), pow_mul]
  have hd : ∀ i, v ∣ (c i).val := fun i => by
    have := (ZMod.natCast_eq_zero_iff _ _).1 (congrFun h0 i)
    exact Nat.dvd_of_mul_dvd_mul_right (Nat.pos_of_ne_zero hu)
      ((dvd_of_eq (hN.trans (mul_comm u v)).symm).trans this)
  refine ⟨fun i => (((c i).val / v : ℕ) : ZMod N), ?_⟩
  rw [← hc, ← Finset.prod_pow]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [ZMod.val_natCast, ← pow_eq_pow_mod _ (hp i), ← pow_mul, Nat.div_mul_cancel (hd i)]

theorem span_eq_top (hL : Laws) {S : Scheme.{0}} (P : PolAV S) {K : Type} [Field K] [IsAlgClosed K]
    (x : Sp K ⟶ S) {k : ℤ} {n : ℕ} (hk : k = n) (h4 : 4 ≤ n) (hn : (n : K) ≠ 0) {I : Type} [Nonempty I]
    (U : I → ThetaGrp P.A P.L k (Over.mk x)) (hU : ∀ y : Over.mk x ⟶ P.A, y ^ n = 1 → ∃ c, (U c).pt = y)
    (s₁ : LB.Sec (LPow P.A P.L k (Over.mk x))) (σ : I → LB.Sec (LPow P.A P.L k (Over.mk x)))
    (hσ : ∀ c, IsActOf P.A P.L k (U c) s₁ (σ c)) (h0 : (SecM.ofSec P.A s₁ : SecM P.A P.L k (Over.mk x)) ≠ 0) :
    Submodule.span Γ((Over.mk x).left, ⊤)
      (Set.range fun c => (SecM.ofSec P.A (σ c) : SecM P.A P.L k (Over.mk x))) = ⊤ := by
  subst hk
  obtain ⟨ρ, k₁, -, k₃, k₄⟩ := thetaGrp_acts_linearly hL.globalFns S P n (Over.mk x)
  have e : (fun c => (SecM.ofSec P.A (σ c) : SecM P.A P.L n (Over.mk x))) =
      fun c => ρ (U c) (SecM.ofSec P.A s₁) := funext fun c => ((k₁ _ _ _).1 (hσ c)).symm
  rw [e]
  exact VVRank.span_translates_eq_top P.A
    ((secM_invariant_eq_bot_or_univ_at_geometric_point hL.polBaseChange).2 hL.irred S P K x n (Or.inr h4) hn) ρ k₁ k₃ k₄ U
    (fun θ => hU _ ((pt_pow_and_surjective hL P x n (by omega)).1 θ)) _ h0

theorem ne_zero_of_isGenSec (hL : Laws) {S : Scheme.{0}} (P : PolAV S) {K : Type} [Field K] [IsAlgClosed K]
    (x : Sp K ⟶ S) (th : LB.Sec (LPow P.A P.L 1 (Over.mk x))) (h : IsGenSec P.A P.L 1 th) :
    (SecM.ofSec P.A th : SecM P.A P.L 1 (Over.mk x)) ≠ 0 := by
  intro h0
  have hnt : Nontrivial Γ((Over.mk x).left, ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom.domain_nontrivial
  have hr : Module.finrank Γ((Over.mk x).left, ⊤) (SecM P.A P.L 1 (Over.mk x)) = 1 ^ P.g :=
    (secM_invariant_eq_bot_or_univ_at_geometric_point hL.polBaseChange).1 hL.globalSectionsRank S P K x 1 le_rfl
  have z : ∀ v : SecM P.A P.L 1 (Over.mk x), v = 0 := fun v => by
    obtain ⟨r, hr⟩ := h (SecM.toSec P.A v)
    have : v = r • (SecM.ofSec P.A th : SecM P.A P.L 1 (Over.mk x)) := Subtype.ext (funext hr)
    rw [this, h0, smul_zero]
  have : Subsingleton (SecM P.A P.L 1 (Over.mk x)) := ⟨fun a b => (z a).trans (z b).symm⟩
  rw [Module.finrank_zero_of_subsingleton, one_pow] at hr
  exact zero_ne_one hr

theorem emb_span_eq_top : Out.Laws → Out.Laws2 → ∀ (o : Type) [CommRing o] (g N' : ℕ) (J : Type) (b : TBase o (N' ^ 2)) (S : Scheme.{0}) (s : S ⟶ Sp o) (t : TObj g (N' ^ 2) J b s) (m : ℕ) (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ S) σ, Odd N' → m ∣ N' → 2 ≤ m → t.Emb m (Over.mk x) σ → Submodule.span Γ((Over.mk x).left, ⊤) (Set.range fun a => (Out.SecM.ofSec t.A (σ a) : Out.SecM t.A t.L ((m : ℤ) ^ 2) (Over.mk x))) = ⊤ := by
  rintro hL - o _ g N' J b S s t m K _ _ x σ hodd ⟨d, hd⟩ hm ⟨th, s₁, α, U, hth, -, htw, hU, hσ⟩
  have := t.ab.comm
  have hN0 : N' ≠ 0 := hodd.pos.ne'
  have hdiv : N' / m = d := by rw [hd, Nat.mul_div_cancel_left _ (by omega)]
  have hK : ((N' ^ 2 : ℕ) : K) ≠ 0 := VVRank.natCast_ne_zero (x ≫ s) (by
    simpa using b.unit.map (Scheme.ΓSpecIso (CommRingCat.of o)).inv.hom)
  have hN : N' ^ 2 = m ^ 2 * d ^ 2 := by rw [hd, mul_pow]
  refine span_eq_top hL t.pol x (n := m ^ 2) (Nat.cast_pow m 2).symm (by nlinarith)
    (fun h => hK (by rw [hN, Nat.cast_mul, h, zero_mul])) U (fun y hy => ?_) s₁ σ hσ fun h0 => ?_
  · obtain ⟨a, ha⟩ := exists_pow_eq (G := (Over.mk x ⟶ t.A)) hN (pow_ne_zero _ hN0)
      (fun i => (Over.homMk x (by simp) : Over.mk x ⟶ Out.baseOver S) ≫ t.pt i)
      (fun i => by rw [← MonObj.comp_pow, t.torsion, MonObj.comp_one])
      (fun z hz => by simpa only [linComb, List.prod_ofFn] using t.bij K x z hz) y hy
    refine ⟨a, (hU a).pt_eq.trans (Eq.trans ?_ ha)⟩
    rw [hdiv, TObj.lab, VVRank.comp_linComb, linComb, List.prod_ofFn]
    rfl
  · have hint : IsIntegral (Over.mk x ⊗ t.A).left :=
      (forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ t.A.hom t.ab.smooth
        t.ab.geomConnected).geometrically_isIntegral x _ _ (IsPullback.of_hasPullback x t.A.hom).flip
    exact ne_zero_of_isGenSec hL t.pol x th hth (VVRank.ofSec_eq_zero_of_twist t.A t.isLB
      (pt_pow_and_surjective hL t.pol x m (by omega)).2 htw h0)

end GlobalTheory.EmbSpan
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise

namespace GlobalTheory.QuotientNorm

open TopologicalSpace

theorem exists_lb_of_cocycle {Y : Scheme.{0}} {K : Type} (V : K → Y.Opens) (hV : ⨆ i, V i = ⊤)
    (a : ∀ i, K → Γ(Y, V i)) (h₁ : ∀ i, a i i = 1) (hle : ∀ i j, Y.basicOpen (a i j) ≤ V j)
    (hc : ∀ i j k, resG Y (inf_le_left : V i ⊓ V j ≤ V i) (a i k) =
      resG Y (inf_le_left : V i ⊓ V j ≤ V i) (a i j) * resG Y (inf_le_right : V i ⊓ V j ≤ V j) (a j k)) :
    ∃ (L : LB Y) (σ : K → LB.Sec L), L.IsLB ∧ ∀ j, Out.nonzeroLocus (σ j) = V j := by
  have hu (i j) : IsUnit (resG Y (inf_le_left : V i ⊓ V j ≤ V i) (a i j)) :=
    IsUnit.of_mul_eq_one _ ((hc i j i).symm.trans (by rw [h₁, map_one]))
  have hg (i j) (y : Y) (hy : y ∈ V i ⊓ V j) :
      gs (𝟙 Y) y (V i ⊓ V j) (hu i j).unit.val = gs (𝟙 Y) y (V i) (a i j) := gs_res _ y _ hy _
  have hc' (i j k) (y : Y) (hy : y ∈ V i ⊓ V j) :
      gs (𝟙 Y) y (V i) (a i k) = gs (𝟙 Y) y (V i) (a i j) * gs (𝟙 Y) y (V j) (a j k) := by
    have e := congrArg (gs (𝟙 Y) y _) (hc i j k)
    rwa [gs_res _ y _ hy, gs_mul _ y _ hy, gs_res _ y _ hy, gs_res _ y _ hy] at e
  refine ⟨⟨K, V, fun i j => (hu i j).unit⟩, fun k => ⟨fun i => a i k, fun i j => hc i j k⟩,
    ⟨hV, fun i => Units.ext (fn_ext fun y hy => ?_), fun i j k => Units.ext (fn_ext fun y hy => ?_)⟩, fun j => ?_⟩
  · exact (gs_res (𝟙 Y) y (le_inf le_rfl le_rfl) hy _).trans ((hg i i y ⟨hy, hy⟩).trans (by rw [h₁]; rfl))
  · refine (gs_mul (𝟙 Y) y _ hy _ _).trans ?_
    refine (congrArg₂ (· * ·) ((gs_res (𝟙 Y) y inf_le_left hy _).trans (hg i j y hy.1))
      ((gs_res (𝟙 Y) y (le_inf (inf_le_left.trans inf_le_right) inf_le_right) hy _).trans
        (hg j k y ⟨hy.1.2, hy.2⟩))).trans ((hc' i j k y hy.1).symm.trans ?_)
    exact ((gs_res (𝟙 Y) y (le_inf (inf_le_left.trans inf_le_left) inf_le_right) hy _).trans
      (hg i k y ⟨hy.1.1, hy.2⟩)).symm
  · refine le_antisymm (iSup_le fun i => hle i j) (le_trans ?_ (basicOpen_le_nonzeroLocus _ j))
    exact (Y.basicOpen_of_isUnit (f := a j j) (h₁ j ▸ isUnit_one)).ge

variable {G : Type} [Group G] {X Y : Scheme.{0}} {ρ : G →* Aut X} {π : X ⟶ Y}

theorem eq_of_gs (h : IsAffineQuotient ρ π) {W : Y.Opens} {a b : Γ(Y, W)}
    (e : ∀ x, π x ∈ W → gs π x W a = gs π x W b) : a = b :=
  h.app_injective W (fn_ext fun x hx => (gs_pull (𝟙 X) π x W hx a).trans
    (((Category.id_comp π).symm ▸ e x hx :).trans (gs_pull (𝟙 X) π x W hx b).symm))

theorem exists_norm [Fintype G] (h : IsAffineQuotient ρ π) {W : Y.Opens} {D : X.Opens}
    (hD : ∀ g, π ⁻¹ᵁ W ≤ (ρ g).asIso.hom ⁻¹ᵁ D) (r : Γ(X, D)) :
    ∃ a : Γ(Y, W), ∀ x, π x ∈ W → gs π x W a = ∏ g, gs (ρ g).asIso.hom x D r := by
  obtain ⟨a, ha⟩ := h.mem_range_app W (∏ g, (ρ g).asIso.hom.appLE D _ (hD g) r) fun k => ⟨h.preimage_le W k, by
    rw [map_prod]
    refine Fintype.prod_equiv (Equiv.mulRight k) _ _ fun g => ?_
    have : (ρ (g * k)).asIso.hom = (ρ k).asIso.hom ≫ (ρ g).asIso.hom := by rw [map_mul]; rfl
    simp only [Equiv.coe_mulRight, ← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE, this]⟩
  refine ⟨a, fun x hx => ?_⟩
  have e := gs_pull (𝟙 X) π x W hx a
  rw [Category.id_comp] at e
  rw [← e, show (π.app W).hom a = _ from ha, gs_eq (𝟙 X) x (π ⁻¹ᵁ W) hx, map_prod, map_prod]
  refine Finset.prod_congr rfl fun g _ => ?_
  exact (gs_eq (𝟙 X) x (π ⁻¹ᵁ W) hx _).symm.trans ((gs_appLE _ D _ (hD g) (𝟙 X) x hx r).trans (by rw [Category.id_comp]))

theorem exists_affine_cover_of_quotient :
    ∀ (Γ : Type) [Group Γ] [Finite Γ] (X X' : Scheme.{0}) (ρ : Γ →* Aut X) (π : X ⟶ X'), (IsAffineHom π ∧ (∀ g, (ρ g).asIso.hom ≫ π = π) ∧ ∀ V : X'.Opens, Function.Injective (π.app V).hom ∧ ∀ f : Γ(X, π ⁻¹ᵁ V), (∀ g (h : π ⁻¹ᵁ V ≤ (ρ g).asIso.hom ⁻¹ᵁ (π ⁻¹ᵁ V)), ((ρ g).asIso.hom.appLE _ _ h).hom f = f) → f ∈ Set.range (π.app V).hom) → X.IsSeparated → ∀ (L : LB X) (n : ℕ) (σ : Fin n → LB.Sec L), L.IsLB → (∀ i, IsAffineOpen (Out.nonzeroLocus (σ i))) → (∀ x : X, ∃ i, ∀ g, (ρ g).asIso.hom x ∈ Out.nonzeroLocus (σ i)) → (∃ (L : LB X') (n : ℕ) (σ : Fin n → LB.Sec L), L.IsLB ∧ (∀ i, IsAffineOpen (Out.nonzeroLocus (σ i))) ∧ ⨆ i, Out.nonzeroLocus (σ i) = ⊤) := by
  rintro G _ _ X Y ρ π H _ L n σ - haff hcov
  classical
  have := Fintype.ofFinite G
  obtain ⟨-, hsurj, -, -, hst⟩ := quotient_isIntegral_surjective_orbits G X Y ρ π H
  have h : IsAffineQuotient ρ π :=
    ⟨H.2.1, H.1, fun W => (H.2.2 W).1, fun W s hs => (H.2.2 W).2 s fun g _ => (hs g).2⟩
  let W : Fin n → X.Opens := fun i => ⨅ g, (ρ g).asIso.hom ⁻¹ᵁ Out.nonzeroLocus (σ i)
  have hW (i x) : x ∈ W i ↔ ∀ g, (ρ g).asIso.hom x ∈ Out.nonzeroLocus (σ i) := by
    change x ∈ ((W i : X.Opens) : Set X) ↔ _
    simp only [W, Opens.coe_iInf, Set.mem_iInter]
    rfl
  choose V hV using fun i => hst (W i) fun k => by
    ext x
    change (ρ k).asIso.hom x ∈ W i ↔ x ∈ W i
    simp only [hW, ← aut_map_mul_apply]
    exact ⟨fun e g => by simpa using e (g * k⁻¹), fun e g => e _⟩
  have hm (i x) : π x ∈ V i ↔ ∀ g, (ρ g).asIso.hom x ∈ Out.nonzeroLocus (σ i) := by
    rw [← hW, ← hV]; rfl
  choose r hr using fun i j => AmpleSpan.exists_isRatio (σ j) (σ i)
  choose a ha using fun i j => exists_norm h (W := V i) (D := Out.nonzeroLocus (σ i)) (fun g x hx => (hm i x).1 hx g) (r i j)
  have top : ⨆ i, V i = ⊤ := top_le_iff.1 fun y _ => by
    obtain ⟨x, rfl⟩ := π.surjective y
    obtain ⟨i, hi⟩ := hcov x
    exact Opens.mem_iSup.2 ⟨i, (hm i x).2 hi⟩
  have hc (i j k) (f : X ⟶ X) (x : X) (hi : f x ∈ Out.nonzeroLocus (σ i)) (hj : f x ∈ Out.nonzeroLocus (σ j)) :
      gs f x _ (r i k) = gs f x _ (r i j) * gs f x _ (r j k) := by
    obtain ⟨l, hl⟩ := exists_chart_of_mem_nonzeroLocus hi
    refine ((mem_nonzeroLocus_iff_pull _ f x hl).1 hi).mul_right_cancel ?_
    rw [← (hr i k).gs f x hi hl, (hr j k).gs f x hj hl, (hr i j).gs f x hi hl]
    ring
  obtain ⟨L', σ', hL', hσ'⟩ := exists_lb_of_cocycle V top a
    (fun i => eq_of_gs h fun x hx => by
      rw [ha i i x hx, AmpleSpan.gs_one' _ _ _ hx]
      refine Finset.prod_eq_one fun g _ => ?_
      have hi := (hm i x).1 hx g
      obtain ⟨l, hl⟩ := exists_chart_of_mem_nonzeroLocus hi
      refine ((mem_nonzeroLocus_iff_pull _ _ x hl).1 hi).mul_right_cancel ?_
      rw [← (hr i i).gs _ x hi hl, _root_.one_mul])
    (fun i j y hy => by
      obtain ⟨x, rfl⟩ := π.surjective y
      have hx : π x ∈ V i := Y.basicOpen_le _ hy
      have u := (LBGerm.isUnit_gs_iff π x _ hx _).2 hy
      rw [ha i j x hx, IsUnit.prod_univ_iff] at u
      refine (hm j x).2 fun g => ?_
      have := (LBGerm.isUnit_gs_iff _ x _ ((hm i x).1 hx g) _).1 (u g)
      rw [(hr i j).basicOpen] at this
      exact this.2)
    (fun i j k => eq_of_gs h fun x hx => by
      rw [gs_res _ x _ hx, gs_mul _ x _ hx, gs_res _ x _ hx, gs_res _ x _ hx, ha i k x hx.1, ha i j x hx.1,
        ha j k x hx.2, ← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl fun g _ => hc i j k _ x ((hm i x).1 hx.1 g) ((hm j x).1 hx.2 g))
  refine ⟨L', n, σ', hL', fun i => ?_, by simp only [hσ', top]⟩
  rw [hσ']
  refine h.isAffineOpen_of_preimage ?_
  rw [hV]
  exact IsAffineOpen.iInf fun g => (haff i).preimage (ρ g).asIso.hom

end GlobalTheory.QuotientNorm
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

noncomputable section

namespace GlobalTheory.RigidBundleGlue

variable {X Y Z : Scheme.{0}}

theorem exists_gen_of_lbIso {P Q : LB X} (hP : P.IsLB) (hQ : Q.IsLB) (h : LBIso P Q)
    (H : ∃ t : LB.Gen P, t.IsGen) : ∃ t : LB.Gen Q, t.IsGen := by
  obtain ⟨w, hw⟩ := h.chartPull (chartPullId P) (chartPullPull Q (𝟙 X) (𝟙 X) rfl)
  obtain ⟨t, ht⟩ := H
  obtain ⟨a, ha⟩ := gen_chartPull (chartPullPull P (𝟙 X) (𝟙 X) rfl) t ht
  obtain ⟨c, hc, -⟩ := exists_up ((isGen_iff w).1 hw) hQ hP a ha
  exact gen_chartPull (chartPullUnpull Q _ (Category.id_comp _)) c hc

theorem LBIso.pull {P Q : LB X} (h : LBIso P Q) (f : Y ⟶ X) : LBIso (P.pull f) (Q.pull f) :=
  h.chartPull (chartPullPull P f f rfl) (chartPullPull Q f f rfl)

def chartPullComp (L : LB X) (f : Y ⟶ X) (g : Z ⟶ Y) (c : Z ⟶ X) (e : c = g ≫ f) :
    ChartPull (L.pull c) ((L.pull f).pull g) (𝟙 Z) := by
  subst e
  exact chartPullIn L (fun _ : PUnit => f) (fun _ => 1) g

theorem eq_one_of_section {S : Scheme.{0}} (A : Over S) [GrpObj A] (hA : IsAbelianScheme A) {e : S ⟶ A.left}
    (he : e ≫ A.hom = 𝟙 S) (V : S.Opens) (u : Γ(A.left, A.hom ⁻¹ᵁ V)) (h : V ≤ e ⁻¹ᵁ (A.hom ⁻¹ᵁ V))
    (hu : (e.appLE _ V h).hom u = 1) : u = 1 := by
  have := hA.smooth
  have := hA.proper
  have := forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ A.hom hA.smooth hA.geomConnected
  have := GlobalFunctions.isIso_app FlatFibreInjective.injective_baseChange exists_noetherian_model_of_smooth A.hom V
  obtain ⟨a, rfl⟩ := (ConcreteCategory.bijective_of_isIso (A.hom.app V)).2 u
  have k : ∀ (q : S ⟶ S) (_ : q = 𝟙 S) (l : V ≤ q ⁻¹ᵁ V), (q.appLE V V l).hom a = a := by
    rintro _ rfl l
    have : (𝟙 S : S ⟶ S).appLE V V l = 𝟙 _ := by
      simp [Scheme.Hom.appLE]
      exact S.presheaf.map_id _
    rw [this]; rfl
  have h₁ : (e.appLE _ V h).hom ((A.hom.app V).hom a) = a :=
    (congrArg (fun q => q.hom a) (Scheme.Hom.comp_appLE e A.hom V V h)).symm.trans (k (e ≫ A.hom) he h)
  rw [h₁.symm.trans hu, map_one]

theorem eSec_comm {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) : eSec G' ≫ φ = f ≫ eSec G := by
  have e := congrArg (fun z => z.left) (map_one (pushHom h (𝟙_ (Over S'))))
  have e₁ : (1 : 𝟙_ (Over S') ⟶ G') = η[G'] := by rw [Hom.one_def]; simp
  rw [e₁] at e
  refine e.trans ?_
  show (toUnit _ ≫ η[G]).left = _
  simp [eSec]

theorem exists_glue : ∀ (S : Scheme.{0}) (I : Type) (U : I → S.Opens) (A : Over S) [GrpObj A] (G : ∀ i, Over (U i).toScheme) [∀ i, GrpObj (G i)] (ψ : ∀ i, (G i).left ⟶ A.left), iSup U = ⊤ → (∀ i, IsGrpPullback (G i) A (U i).ι (ψ i)) → IsAbelianScheme A → (∀ i, IsAbelianScheme (G i)) → ∀ (M : ∀ i, LB (G i).left) (B : I → I → Scheme.{0}) (a : ∀ i j, B i j ⟶ (G i).left) (b : ∀ i j, B i j ⟶ (G j).left), (∀ i j, IsPullback (a i j) (b i j) (ψ i) (ψ j)) → (∀ i, (M i).IsLB) → (∀ i, Out.Rigidified (G i) (M i)) → (∀ i j, LBIso ((M i).pull (a i j)) ((M j).pull (b i j))) → ∃ L : LB A.left, L.IsLB ∧ Out.Rigidified A L ∧ ∀ i, LBIso (M i) (L.pull (ψ i)) := by
  intro S I U A _ G _ ψ hU hψ hA _ M B a b hB hM hr hiso
  have oi : ∀ i, IsOpenImmersion (ψ i) := fun i => CoverGlue.isOpenImmersion (hψ i).1
  choose N hN₁ hN₂ hN₃ hN₄ using fun i => GlobalTheory.T.exists_cechData_pullback_of_lineBundle_on_open _ _ (ψ i) (M i) (hM i)
  have hR : ∀ i x, x ∈ (ψ i).opensRange ↔ A.hom x ∈ U i := fun i x => CoverGlue.mem_range (hψ i).1 x
  have hNU : ∀ i k, (N i).U k ≤ (ψ i).opensRange := fun i k => (le_iSup (N i).U k).trans (hN₁ i).le
  let e : S ⟶ A.left := eSec A
  have he : e ≫ A.hom = 𝟙 S := Over.w η[A]
  obtain ⟨L, hL, hLr, hLi⟩ := GlobalTheory.T.exists_glue_rigidified_partial_line_bundles A.left S A.hom e I U N he (eq_one_of_section A hA he) hU
    (fun i => (hN₁ i).trans (TopologicalSpace.Opens.ext (Set.ext (hR i)))) hN₂
    (fun i => by
      refine (GlobalTheory.T.generator_iso_extend_from_open_containing_charts S (U i).toScheme (U i).ι).1 _ (fun k s hs => ?_) ?_
      · have h₁ := (hR i _).1 (hNU i _ (mem_pull.1 hs))
        rw [← Scheme.Hom.comp_apply, he] at h₁
        exact ⟨⟨s, h₁⟩, rfl⟩
      · let e' : (U i).toScheme ⟶ (G i).left := eSec (G i)
        have hc : e' ≫ ψ i = (U i).ι ≫ e := eSec_comm (hψ i)
        obtain ⟨t, ht⟩ := exists_gen_of_lbIso (pull_isLB (hM i) e') (pull_isLB (hN₃ i) e')
          (LBIso.pull (hN₄ i) e') (hr i)
        obtain ⟨t', ht'⟩ := gen_chartPull (chartPullComp (N i) (ψ i) e' _ hc.symm) t ht
        exact gen_chartPull (chartPullOut (N i) (fun _ : PUnit => e) (fun _ => 1) (U i).ι _ fun _ => rfl) t' ht')
    (fun i j => by
      have : IsOpenImmersion (a i j) :=
        MorphismProperty.of_isPullback (P := @IsOpenImmersion) (hB i j).flip (oi j)
      refine (GlobalTheory.T.generator_iso_extend_from_open_containing_charts A.left (B i j) (a i j ≫ ψ i)).2 _ _ (fun k l x hx => ?_) ?_
      · obtain ⟨y, hy⟩ := hNU i k hx.1
        obtain ⟨y', hy'⟩ := hNU j l hx.2
        obtain ⟨z, hz, -⟩ := Scheme.exists_preimage_of_isPullback (hB i j) y y' (hy.trans hy'.symm)
        exact ⟨z, by rw [Scheme.Hom.comp_apply, hz, hy]⟩
      · refine LBIso.chartPull (chartPullComp (N i) (ψ i) (a i j) _ rfl)
          (chartPullComp (N j) (ψ j) (b i j) _ (hB i j).w) ?_
        exact ((LBIso.pull (hN₄ i) (a i j)).symm.trans (pull_isLB (hN₃ i) _) (pull_isLB (hM i) _)
          (pull_isLB (hM j) _) (hiso i j)).trans (pull_isLB (hN₃ i) _) (pull_isLB (hM j) _) (pull_isLB (hN₃ j) _)
          (LBIso.pull (hN₄ j) (b i j)))
  exact ⟨L, hL, hLr, fun i => (hN₄ i).trans (hM i) (hN₃ i) (pull_isLB hL _) (LBIso.pull (hLi i) (ψ i))⟩

end GlobalTheory.RigidBundleGlue
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

theorem _root_.GlobalTheory.T.weilIs_local_on_base_of_openCover : ∀ (S : Scheme.{0}) (I : Type) (U : I → S.Opens) (A : Over S) [GrpObj A] (G : ∀ i, Over (U i).toScheme) [∀ i, GrpObj (G i)] (ψ : ∀ i, (G i).left ⟶ A.left), iSup U = ⊤ → (∀ i, IsGrpPullback (G i) A (U i).ι (ψ i)) → ∀ (L : LB A.left) (M : ∀ i, LB (G i).left), L.IsLB → (∀ i, (M i).IsLB) → (∀ i, LBIso (M i) (L.pull (ψ i))) → IsAbelianScheme A → (∀ i, IsAbelianScheme (G i)) → ∀ (k : ℤ) (x y : Out.baseOver S ⟶ A) (x' y' : ∀ i, Out.baseOver (U i).toScheme ⟶ G i) (c : Γ(S, ⊤)ˣ), (∀ i, (x' i).left ≫ ψ i = (U i).ι ≫ x.left) → (∀ i, (y' i).left ≫ ψ i = (U i).ι ≫ y.left) → (∀ i, Out.WeilIs (G i) (M i) k (x' i) (y' i) (Units.map (U i).ι.appTop.hom.toMonoidHom c)) → Out.WeilIs A L k x y c := by
  first | exact @GlobalTheory.weilIs_of_openCover | exact GlobalTheory.weilIs_of_openCover | (intros; apply GlobalTheory.weilIs_of_openCover <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

theorem _root_.GlobalTheory.T.determinantCondition_spreads_of_dense_points : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (S : Scheme.{0}) [IsReduced S] (G : Over S) [GrpObj G] [IsCommMonObj G] (g : ℕ) (act : OAct (𝓞 E) G) (o : Type) [CommRing o] (s : S ⟶ Sp o) (ρ : o), SmoothOfRelativeDimension g G.hom → ρ ^ 2 = -(H.d : o) → Dense {p : S | ∃ (K : Type) (_ : Field K) (_ : IsAlgClosed K) (_ : CharZero K) (x : Sp K ⟶ S) (β : o →+* K), p ∈ Set.range x ∧ x ≫ s = spMap β ∧ DetCond D act x (β ρ)} → ∀ (K : Type) [Field K] [IsAlgClosed K] [CharZero K] (x : Sp K ⟶ S) (β : o →+* K), x ≫ s = spMap β → DetCond D act x (β ρ) := by
  first | exact @GlobalTheory.DetSpread.detCond_of_dense | exact GlobalTheory.DetSpread.detCond_of_dense | (intros; apply GlobalTheory.DetSpread.detCond_of_dense <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

theorem _root_.GlobalTheory.T.exists_finite_scheme_latticeTorsionHom_primitiveRoot : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (n : ℕ) (La : Type) [AddCommGroup La] [Module.Free ℤ La] [Module.Finite ℤ La], IsAbelianScheme G → 0 < n → ∃ (Z : Over S) (et : La → (Z ⟶ G)) (c : Γ(Z.left, ⊤)ˣ), IsUnit (n : Γ(Z.left, ⊤)) ∧ (∀ a a', et (a + a') = et a * et a') ∧ (∀ a, et a ^ n = 1) ∧ c ^ n = 1 ∧ (∀ (K : Type) [Field K] (h : Sp K ⟶ Z.left) (ζ : Kˣ), Units.map h.appTop.hom.toMonoidHom c = unitOn ζ → IsPrimitiveRoot ζ n) ∧ (∀ (K : Type) [Field K] (x : Sp K ⟶ S) (et' : La → (Over.mk x ⟶ G)) (ζ : Kˣ), (n : K) ≠ 0 → (∀ a a', et' (a + a') = et' a * et' a') → (∀ a, et' a ^ n = 1) → IsPrimitiveRoot ζ n → ∃ h : Over.mk x ⟶ Z, (∀ a, h ≫ et a = et' a) ∧ Units.map h.left.appTop.hom.toMonoidHom c = unitOn ζ) ∧ ∀ (C : Set Z.left), IsClosed C → ∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ S), (n : K) ≠ 0 → Set.range x ⊆ closure (Z.hom '' C) → ∃ h : Over.mk x ⟶ Z, Set.range h.left ⊆ C := by
  first | exact @GlobalTheory.exists_latticeTorsionHom_primitiveRoot_param | exact GlobalTheory.exists_latticeTorsionHom_primitiveRoot_param | (intros; apply GlobalTheory.exists_latticeTorsionHom_primitiveRoot_param <;> assumption)
end
