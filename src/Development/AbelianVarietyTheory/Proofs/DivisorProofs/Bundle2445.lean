module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2405
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2417
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2363
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2406
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle859
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2408
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import Mathlib.Algebra.Order.Star.Rat
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle059
import Development.AbelianVarietyTheory.Definitions.Divisors.TupleReadBaseTupleEqFamily
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf

@[expose] public section

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep
open scoped CategoryTheory.Obj
attribute [local instance] CategoryTheory.Hom.group
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelMod)
open MonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Semi
set_option autoImplicit false
noncomputable section

namespace GlobalTheory.TorsSpec

theorem eq_section_of_isDominant {D G X' V Y₀ Y : Scheme.{0}} [IsReduced D] (g : G ⟶ X') [IsSeparated g]
    (ℓ : V ⟶ X') [IsOpenImmersion ℓ] (σ : D ⟶ G) (s : V ⟶ G) (hs : s ≫ g = ℓ) (y₀ : Y₀ ⟶ D) [IsDominant y₀]
    (z₀ : Y₀ ⟶ V) (h₀ : y₀ ≫ σ = z₀ ≫ s) (y : Y ⟶ D) (z : Y ⟶ V) (h : y ≫ σ ≫ g = z ≫ ℓ) :
    y ≫ σ = z ≫ s := by
  have h₀' : y₀ ≫ σ ≫ g = z₀ ≫ ℓ := by rw [reassoc_of% h₀, hs]
  have : IsReduced (pullback (σ ≫ g) ℓ) := isReduced_of_isOpenImmersion (pullback.fst (σ ≫ g) ℓ)
  have hd : IsDominant (pullback.lift y₀ z₀ h₀') := by
    constructor
    have h1 : Dense (Set.range y₀) := y₀.denseRange
    have h2 := h1.preimage (pullback.fst (σ ≫ g) ℓ).isOpenEmbedding.isOpenMap
    refine h2.mono ?_
    rintro u ⟨t, ht⟩
    refine ⟨t, (pullback.fst (σ ≫ g) ℓ).isOpenEmbedding.injective ?_⟩
    rw [← ht, ← Scheme.Hom.comp_apply, pullback.lift_fst]
  have key : pullback.fst (σ ≫ g) ℓ ≫ σ = pullback.snd (σ ≫ g) ℓ ≫ s := by
    refine ext_of_isDominant_of_isSeparated (s := g) ?_ (pullback.lift y₀ z₀ h₀') ?_
    · rw [Category.assoc, Category.assoc, hs, pullback.condition]
    · rw [pullback.lift_fst_assoc, pullback.lift_snd_assoc, h₀]
  have := pullback.lift y z h ≫= key
  rwa [pullback.lift_fst_assoc, pullback.lift_snd_assoc] at this

theorem fromSpecStalk_killed {X' : Scheme.{0}} (G : Over X') [GrpObj G] (n : ℕ) [Etale (torsion G n).hom]
    (a : G ⟶ G) [IsMonHom a] (ha : a ≫ mulN G n = mulN G n ≫ a)
    (K : Type) [Field K] (P : Sp K ⟶ (torsion G n).left)
    (hP : P ≫ (torsion.ι G n).left ≫ a.left =
      P ≫ (torsion G n).hom ≫ (MonObj.one : 𝟙_ (Over X') ⟶ G).left) (x : Sp K) :
    (torsion G n).left.fromSpecStalk (P x) ≫ (torsion.ι G n).left ≫ a.left =
      (torsion G n).left.fromSpecStalk (P x) ≫ (torsion G n).hom ≫ (MonObj.one : 𝟙_ (Over X') ⟶ G).left := by
  obtain rfl : x = IsLocalRing.closedPoint K := Subsingleton.elim _ _
  have hι : torsion.ι G n ≫ mulN G n = 1 := by
    rw [Hom.one_def]
    exact pullback.condition.trans (congrArg (· ≫ _) (CartesianMonoidalCategory.toUnit_unique _ _))
  have h0 : (MonObj.one : 𝟙_ (Over X') ⟶ G) ≫ mulN G n = (MonObj.one : 𝟙_ (Over X') ⟶ G) := by
    have e : (MonObj.one : 𝟙_ (Over X') ⟶ G) = 1 := by
      rw [Hom.one_def]
      exact (Category.id_comp _).symm.trans (congrArg (· ≫ _) (CartesianMonoidalCategory.toUnit_unique _ _))
    rw [GlobalTheory.GrpTangent.mulN_eq_pow, MonObj.comp_pow, Category.comp_id, e, one_pow]
  obtain ⟨u₁, hu₁⟩ := exists_lift_torsion n (torsion.ι G n ≫ a)
    (by rw [Category.assoc, ha, ← Category.assoc, hι, MonObj.one_comp])
  obtain ⟨u₂, hu₂⟩ := exists_lift_torsion n (1 : torsion G n ⟶ G)
    (by rw [Hom.one_def, Category.assoc, h0])
  have e₁ : u₁.left ≫ (torsion.ι G n).left = (torsion.ι G n).left ≫ a.left := congrArg (·.left) hu₁
  have e₂ : u₂.left ≫ (torsion.ι G n).left = (torsion G n).hom ≫ (MonObj.one : 𝟙_ (Over X') ⟶ G).left := by
    have := congrArg (·.left) hu₂
    simp only [Hom.one_def, Over.comp_left] at this
    rw [this]
    congr 1
  have := mono_torsion_ι G n
  have key : (torsion G n).left.fromSpecStalk (P (IsLocalRing.closedPoint K)) ≫ u₁.left =
      (torsion G n).left.fromSpecStalk (P (IsLocalRing.closedPoint K)) ≫ u₂.left := by
    refine GlobalTheory.T.eq_of_formallyUnramified_of_eq_at_closedPoint (torsion G n).hom _ _ _ ?_ K (Spec.map (Scheme.stalkClosedPointTo P)) ?_ ?_
    · rw [Category.assoc, Category.assoc, Over.w, Over.w]
    · intro x
      obtain rfl : x = IsLocalRing.closedPoint K := Subsingleton.elim _ _
      exact IsLocalRing.comap_closedPoint (Scheme.stalkClosedPointTo P).hom
    · rw [← Category.assoc, ← Category.assoc, Scheme.Spec_stalkClosedPointTo_fromSpecStalk,
        ← cancel_mono (torsion.ι G n).left, Category.assoc, Category.assoc, e₁, e₂, hP]
  rw [← e₁, ← e₂, reassoc_of% key]

theorem exists_valAt : ∀ {E : Type} [Field E] {X' : Scheme.{0}} [IsIntegral X'] [GlobalTheory.IsNormalScheme X'] (G : Over X') [GrpObj G] [IsCommMonObj G]
    [Smooth G.hom] (n : ℕ) (hn : IsUnit (n : Γ(X', ⊤))) {V : Scheme.{0}} [Nonempty V] (ℓ : V ⟶ X')
    [IsOpenImmersion ℓ] {M : Type} (w : M → (V ⟶ G.left)) (hw : ∀ c, w c ≫ G.hom = ℓ) [IsSeparated G.hom] (act : OAct (𝓞 E) G) (I : Ideal (𝓞 E))
    (hex : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (x : Sp Ω ⟶ V) (P : Sp Ω ⟶ G.left), P ≫ G.hom = x ≫ ℓ →
      (∀ a ∈ I, P ≫ (act.act a).left = P ≫ G.hom ≫ (MonObj.one : 𝟙_ (Over X') ⟶ G).left) → ∃ c, P = x ≫ w c)
    (K : Type) [Field K] [IsAlgClosed K] (P : Sp K ⟶ (torsion G n).left)
    (hP : ∀ a ∈ I, P ≫ (torsion.ι G n).left ≫ (act.act a).left = P ≫ (torsion G n).hom ≫ (MonObj.one : 𝟙_ (Over X') ⟶ G).left) (x : Sp K), ∃ c, GlobalTheory.TorsSpec.ValAt G n ℓ w (P x) c := by
  intro E _ X' _ _ G _ _ _ n hn V _ ℓ _ M w hw _ act I hex K _ _ P hP x
  have := GlobalTheory.GrpTangent.etale_torsion G hn
  have := isDomain_stalk_of_etale (torsion G n).hom (P x)
  obtain ⟨Ω, _, _, y₀, hy₀, _⟩ := GlobalTheory.T.exists_dominant_geometricGenericPoint_spec_domain ((torsion G n).left.presheaf.stalk (P x))
  obtain ⟨z₀, hz₀⟩ := GlobalTheory.T.exists_lift_geometricGenericPoint_stalk_of_flat (torsion G n).hom (P x) ℓ Ω y₀ hy₀
  have hw' : (torsion.ι G n).left ≫ G.hom = (torsion G n).hom := Over.w _
  obtain ⟨c, hc⟩ := hex Ω z₀ (y₀ ≫ (torsion G n).left.fromSpecStalk (P x) ≫ (torsion.ι G n).left)
    (by rw [Category.assoc, Category.assoc, hw', hz₀]) (fun a ha => by
      have := act.hom a
      have h := fromSpecStalk_killed G n (act.act a)
        (by rw [← act_natCast act, ← act.mul, ← act.mul, mul_comm]) K P (hP a ha) x
      simp only [Category.assoc]
      rw [h, reassoc_of% hw'])
  refine ⟨c, fun Ω' _ _ y z h => ?_⟩
  exact eq_section_of_isDominant G.hom ℓ _ (w c) (hw c) y₀ z₀ hc y z (by rw [Category.assoc, hw', h])

end GlobalTheory.TorsSpec
end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.ExpTie GlobalTheory.ExpTie.Lift

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ExpTie.Lift
variable {D : D7}

theorem U_sub_c_eq_w (L : SizeData₂ D) (j : Fin D.R.m) (τ : D.what₂.Tau) (a : ℕ) (ha : a < (Vc D j).rank) :
    ((wts L j).U (parOf L j) τ a : ℝ) - (wts L j).c τ =
      (((lamL j τ).w ⟨a, ha⟩ : ℤ) : ℝ) + ((Vc D j).rank : ℝ) / 2 - a := by
  have h1 := lamT_of_lt j τ a ha
  have h2 := congrArg (Int.cast : ℤ → ℝ) h1
  push_cast at h2
  show ((Formalism.CohomologicalDescent.UnitNormBounds.UN (Vc D j).rank (lamT j τ) a : ℤ) : ℝ) - cT j τ = _
  unfold Formalism.CohomologicalDescent.UnitNormBounds.UN cT
  push_cast
  rw [h2]
  ring

theorem valsAt_of_isLamPrime : ∀ {D : Formalism.BasicNotions.D7} (L : Formalism.BasicNotions.SizeData₂ D) (j : Fin D.R.m) (τ : D.what₂.Tau),
    Formalism.IndefR.Bridge.IsLamPrime (GlobalTheory.ExpTie.Lift.lamL j τ) ((j : ℕ) + 1) τ → GlobalTheory.ExpTie.Lift.ValsAt L j τ := by
  intro D L j τ h
  obtain ⟨hj, W, hk, hm, ht, hJ, he, hv, hb, hw⟩ := h
  obtain ⟨k, m, t, J, e, v, b⟩ := W
  simp only at hk hm ht hJ he hv hb
  subst hk hm ht hJ
  have hN := rank_eq j
  have hK := D.R.m_add_three_le_k
  have ht0 := D.R.t_odd.pos
  have hjm := j.2
  have hrk : ((Vc D j).rank : ℚ) = (D.R.k : ℚ) + D.R.m + D.R.t - 1 := by
    rw [hN, Nat.cast_add, Nat.cast_add, Nat.cast_sub (by omega)]; push_cast; ring
  have hmj : ((D.R.m - ((j : ℕ) + 1) : ℕ) : ℚ) = (D.R.m : ℚ) - j - 1 := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  have hk1 : ((D.R.k - 1 : ℕ) : ℚ) = (D.R.k : ℚ) - 1 := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  have hr1 : D.R.k + D.R.m - 1 + D.R.t = (Vc D j).rank := by omega
  have hp : D.R.k + ((j : ℕ) + 1) - 1 = D.R.k + j := by omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a ha
    have hal : a < (Vc D j).rank := by omega
    rw [U_sub_c_eq_w L j τ a hal]
    have hq := hw ⟨a, hal⟩
    simp only [Formalism.IndefR.IndefiniteWeightData.WeightData.lamPrime, Formalism.IndefR.IndefiniteWeightData.WeightData.thetaWt, Formalism.IndefR.IndefiniteWeightData.WeightData.dTau,
      Formalism.IndefR.IndefiniteWeightData.WeightData.aPlus, Formalism.IndefR.IndefiniteWeightData.WeightData.aMinus, Formalism.IndefR.IndefiniteWeightData.WeightData.lam,
      Formalism.IndefR.IndefiniteWeightData.WeightData.p, Formalism.IndefR.IndefiniteWeightData.WeightData.q, Formalism.IndefR.IndefiniteWeightData.WeightData.nV,
      Formalism.IndefR.IndefiniteWeightData.WeightData.r] at hq
    split_ifs at hq with c1 c2 <;> try omega
    rw [hr1, hp, hmj] at hq
    have hv' : ((v (a + 1 + 1) : ℤ) : ℚ) = (D.hc τ).v ⟨a, ha⟩ := hv ⟨a, ha⟩
    have hQ : (((lamL j τ).w ⟨a, hal⟩ : ℤ) : ℚ) + ((Vc D j).rank : ℚ) / 2 - a = (D.hc τ).v ⟨a, ha⟩ := by
      rw [hq, ← hv']; push_cast; ring
    have := congrArg (Rat.cast : ℚ → ℝ) hQ
    push_cast at this
    exact this
  · intro i hi
    have hal : D.R.k - 1 + i < (Vc D j).rank := by omega
    rw [U_sub_c_eq_w L j τ _ hal]
    have hq := hw ⟨_, hal⟩
    simp only [Formalism.IndefR.IndefiniteWeightData.WeightData.lamPrime, Formalism.IndefR.IndefiniteWeightData.WeightData.thetaWt, Formalism.IndefR.IndefiniteWeightData.WeightData.dTau,
      Formalism.IndefR.IndefiniteWeightData.WeightData.aPlus, Formalism.IndefR.IndefiniteWeightData.WeightData.aMinus, Formalism.IndefR.IndefiniteWeightData.WeightData.lam,
      Formalism.IndefR.IndefiniteWeightData.WeightData.p, Formalism.IndefR.IndefiniteWeightData.WeightData.q, Formalism.IndefR.IndefiniteWeightData.WeightData.nV,
      Formalism.IndefR.IndefiniteWeightData.WeightData.r] at hq
    split_ifs at hq with c1 c2 <;> try omega
    rw [hr1, hp, hmj, show D.R.k - 1 + (i : ℕ) + 1 - (D.R.k - 1) = (i : ℕ) + 1 by omega,
      show D.R.k - 1 + (i : ℕ) + 1 = D.R.k + i by omega] at hq
    have hb' := hb i
    have hQ : (((lamL j τ).w ⟨_, hal⟩ : ℤ) : ℚ) + ((Vc D j).rank : ℚ) / 2 - ((D.R.k - 1 + i : ℕ) : ℚ) = -(D.hc τ).b i := by
      rw [Nat.cast_add, hk1]
      push_cast at hq
      linarith
    have := congrArg (Rat.cast : ℚ → ℝ) hQ
    push_cast at this ⊢
    exact this
  · intro s hs
    have hal : D.R.k + j + s < (Vc D j).rank := by omega
    rw [U_sub_c_eq_w L j τ _ hal]
    have hq := hw ⟨_, hal⟩
    simp only [Formalism.IndefR.IndefiniteWeightData.WeightData.lamPrime, Formalism.IndefR.IndefiniteWeightData.WeightData.thetaWt, Formalism.IndefR.IndefiniteWeightData.WeightData.dTau,
      Formalism.IndefR.IndefiniteWeightData.WeightData.aPlus, Formalism.IndefR.IndefiniteWeightData.WeightData.aMinus, Formalism.IndefR.IndefiniteWeightData.WeightData.lam,
      Formalism.IndefR.IndefiniteWeightData.WeightData.p, Formalism.IndefR.IndefiniteWeightData.WeightData.q, Formalism.IndefR.IndefiniteWeightData.WeightData.nV,
      Formalism.IndefR.IndefiniteWeightData.WeightData.r] at hq
    split_ifs at hq with c1 c2 <;> try omega
    have c3 : D.R.k + ↑j + s + 1 ≤ D.R.k + ((j : ℕ) + 1) - 1 + D.R.t := by omega
    simp only [c3, if_true] at hq
    rw [hp, hmj] at hq
    have hQ : (((lamL j τ).w ⟨_, hal⟩ : ℤ) : ℚ) + ((Vc D j).rank : ℚ) / 2 - ((D.R.k + j + s : ℕ) : ℚ) =
        -(D.hc τ).e ⟨(j : ℕ) + 1 - 1, hj.2⟩ + ((D.R.t : ℚ) - 1) / 2 - s := by
      push_cast at hq he ⊢
      linarith
    have hwj : wj D ((j : ℕ) + 1) τ = (((D.hc τ).e ⟨(j : ℕ) + 1 - 1, hj.2⟩ : ℚ) : ℝ) := by
      unfold wj; rw [dite_eq_left hj.2]
    have := congrArg (Rat.cast : ℚ → ℝ) hQ
    rw [hwj]
    push_cast at this ⊢
    linarith
  · intro i hi
    have hal : D.R.k - 1 + i + D.R.t < (Vc D j).rank := by omega
    rw [U_sub_c_eq_w L j τ _ hal]
    have hq := hw ⟨_, hal⟩
    simp only [Formalism.IndefR.IndefiniteWeightData.WeightData.lamPrime, Formalism.IndefR.IndefiniteWeightData.WeightData.thetaWt, Formalism.IndefR.IndefiniteWeightData.WeightData.dTau,
      Formalism.IndefR.IndefiniteWeightData.WeightData.aPlus, Formalism.IndefR.IndefiniteWeightData.WeightData.aMinus, Formalism.IndefR.IndefiniteWeightData.WeightData.lam,
      Formalism.IndefR.IndefiniteWeightData.WeightData.p, Formalism.IndefR.IndefiniteWeightData.WeightData.q, Formalism.IndefR.IndefiniteWeightData.WeightData.nV,
      Formalism.IndefR.IndefiniteWeightData.WeightData.r] at hq
    split_ifs at hq with c1 c2 <;> try omega
    have c3 : ¬ (D.R.k - 1 + (i : ℕ) + D.R.t + 1 ≤ D.R.k + ((j : ℕ) + 1) - 1 + D.R.t) := by omega
    simp only [c3, if_false] at hq
    rw [show D.R.m - ((j : ℕ) + 1) + 1 - (D.R.m - ((j : ℕ) + 1) + 1 - (D.R.k - 1 + (i : ℕ) + D.R.t + 1 - (D.R.k + ((j : ℕ) + 1) - 1) - D.R.t))
        = (i : ℕ) - j by omega] at hq
    rw [show (j : ℕ) + 1 + ((i : ℕ) - j) = (i : ℕ) + 1 by omega, hp, hmj] at hq
    have hij : (((i : ℕ) - (j : ℕ) : ℕ) : ℚ) = (i : ℚ) - j := by
      rw [Nat.cast_sub (by omega)]
    have hb' := hb i
    have hQ : (((lamL j τ).w ⟨_, hal⟩ : ℤ) : ℚ) + ((Vc D j).rank : ℚ) / 2 - ((D.R.k - 1 + i + D.R.t : ℕ) : ℚ) = -(D.hc τ).b i := by
      rw [Nat.cast_add, Nat.cast_add, hk1]
      rw [hij] at hq
      push_cast at hq
      linarith
    have := congrArg (Rat.cast : ℚ → ℝ) hQ
    push_cast at this ⊢
    exact this

end GlobalTheory.ExpTie.Lift

end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.ExpTie GlobalTheory.ExpTie.Lift

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ExpTie.Lift

variable {D : D7}

theorem thick_of_mem (L : Formalism.BasicNotions.SizeData₂ D) (j : Fin D.R.m) (τ : D.what₂.Tau) (hv : ValsAt L j τ)
    (hτ : τ ∈ (wts L j).T2) :
    (parOf L j).Thick ((wts L j).e τ) ∧ ((wts L j).xp τ : ℝ) ≤ (parOf L j).h := by
  have hmem : (D.eTau τ : D.R.GG) ∈ D.host.thickPlaces := by
    simpa [wts] using hτ
  have hm2 := D.R.two_le_m
  have hj := j.2
  have h1 := L.win_thick ((j : ℕ) + 1) (by omega) (by omega) τ hmem
  have h2 := L.win_thick D.R.m (by omega) le_rfl τ hmem
  have hc := c_le L j τ hv
  have hb : (parOf L j).b = L.sc.b := rfl
  refine ⟨?_, ?_⟩
  · show (parOf L j).b ≤ wj D ((j : ℕ) + 1) τ ∧ wj D ((j : ℕ) + 1) τ ≤ (parOf L j).b + L.etaSz + 1
    rw [hb]; exact h1
  · have hfl : ((wts L j).xp τ : ℝ) ≤ cT j τ + L.Sc := by
      show ((⌊cT j τ + L.Sc⌋ : ℤ) : ℝ) ≤ cT j τ + L.Sc
      exact Int.floor_le _
    have hc' : cT j τ ≤ wj D D.R.m τ + ((D.R.t : ℝ) - 1) / 2 := hc
    have ht : (0 : ℝ) ≤ D.R.t := Nat.cast_nonneg _
    show ((wts L j).xp τ : ℝ) ≤ (parOf L j).b + L.Sc + L.etaSz + (D.R.t : ℝ) + 1
    rw [hb]
    linarith [h2.2]

end GlobalTheory.ExpTie.Lift

end
end

section

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.ExpTie GlobalTheory.ExpTie.Lift

namespace GlobalTheory.ExpTie.Lift

theorem low_dist : ∀ {D : Formalism.BasicNotions.D7} (L : Formalism.BasicNotions.SizeData₂ D) (P5 : Formalism.BasicNotions.ParameterChoice' D L) (j : Fin D.R.m) (τ : D.what₂.Tau), GlobalTheory.ExpTie.Lift.ValsAt L j τ → ∀ a, a < (GlobalTheory.ExpTie.parOf L j).Nr → ((Formalism.CohomologicalDescent.ShortWeightBounds.kc (GlobalTheory.ExpTie.parOf L j) ≤ a ∧ a < Formalism.CohomologicalDescent.ShortWeightBounds.kc (GlobalTheory.ExpTie.parOf L j) + (GlobalTheory.ExpTie.Lift.wts L j).j τ) ∨ Formalism.CohomologicalDescent.ShortWeightBounds.kc (GlobalTheory.ExpTie.parOf L j) + (GlobalTheory.ExpTie.Lift.wts L j).j τ + (GlobalTheory.ExpTie.parOf L j).t ≤ a) → 2 * (GlobalTheory.ExpTie.parOf L j).b / (GlobalTheory.ExpTie.parOf L j).lstar + ((GlobalTheory.ExpTie.parOf L j).t : ℝ) / 2 + 3 ≤ |((GlobalTheory.ExpTie.Lift.wts L j).U (GlobalTheory.ExpTie.parOf L j) τ a : ℝ) - (GlobalTheory.ExpTie.Lift.wts L j).c τ + (GlobalTheory.ExpTie.Lift.wts L j).e τ| ∧ |((GlobalTheory.ExpTie.Lift.wts L j).U (GlobalTheory.ExpTie.parOf L j) τ a : ℝ) - (GlobalTheory.ExpTie.Lift.wts L j).c τ + (GlobalTheory.ExpTie.Lift.wts L j).e τ| ≤ (GlobalTheory.ExpTie.parOf L j).η := by
  intro D L P5 j τ hv a ha hcase
  have hn := rank_eq j
  have hk := D.R.m_add_three_le_k
  have hjm := j.2
  change a < (Vc D j).rank at ha
  change (D.R.k - 1 ≤ a ∧ a < D.R.k - 1 + ((j : ℕ) + 1)) ∨ D.R.k - 1 + ((j : ℕ) + 1) + D.R.t ≤ a at hcase
  obtain ⟨i, hval⟩ : ∃ i : Fin D.R.m,
      ((wts L j).U (parOf L j) τ a : ℝ) - (wts L j).c τ = -(((D.hc τ).b i : ℚ) : ℝ) := by
    rcases hcase with ⟨h1, h2⟩ | h1
    · refine ⟨⟨a - (D.R.k - 1), by omega⟩, ?_⟩
      have h := hv.2.1 ⟨a - (D.R.k - 1), by omega⟩ (by simp only [Fin.le_def]; omega)
      have ha' : D.R.k - 1 + (a - (D.R.k - 1)) = a := by omega
      simp only [ha'] at h
      exact h
    · refine ⟨⟨a - (D.R.k - 1) - D.R.t, by omega⟩, ?_⟩
      have h := hv.2.2.2 ⟨a - (D.R.k - 1) - D.R.t, by omega⟩ (by simp only [Fin.lt_def]; omega)
      have ha' : D.R.k - 1 + (a - (D.R.k - 1) - D.R.t) + D.R.t = a := by omega
      simp only [ha'] at h
      exact h
  have he : (wts L j).e τ = (((D.hc τ).e j : ℚ) : ℝ) := by
    show wj D ((j : ℕ) + 1) τ = _
    unfold wj
    rw [dite_eq_left (by omega)]
    congr 3
  have habs : |((wts L j).U (parOf L j) τ a : ℝ) - (wts L j).c τ + (wts L j).e τ| =
      |(((D.hc τ).b i - (D.hc τ).e j : ℚ) : ℝ)| := by
    rw [hval, he, ← abs_neg]
    push_cast
    ring_nf
  rw [habs]
  refine ⟨?_, L.be_close τ i j⟩
  have hN : ((D.R.N D.R.m : ℕ) : ℝ) = (D.R.k : ℝ) + (D.R.m : ℝ) * ((D.R.t : ℝ) + 1) := by
    unfold Ranks.N
    push_cast
    ring
  have hls : (parOf L j).lstar = LevelStarExponents.lStar L := by
    unfold Formalism.CohomologicalDescent.LogSmallConstantBounds.Par.lstar LevelStarExponents.lStar
    rw [hN]
    rfl
  have hb : (parOf L j).b = L.sc.b := rfl
  rw [hls, hb]
  exact P5.lows_far τ i j

end GlobalTheory.ExpTie.Lift

end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.ExpTie GlobalTheory.ExpTie.Lift

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ExpTie.Lift

theorem block_centre : ∀ {D : Formalism.BasicNotions.D7} (L : Formalism.BasicNotions.SizeData₂ D) (j : Fin D.R.m) (τ : D.what₂.Tau), GlobalTheory.ExpTie.Lift.ValsAt L j τ → (∀ a, Formalism.CohomologicalDescent.ShortWeightBounds.kc (GlobalTheory.ExpTie.parOf L j) + (GlobalTheory.ExpTie.Lift.wts L j).j τ ≤ a → a < Formalism.CohomologicalDescent.ShortWeightBounds.kc (GlobalTheory.ExpTie.parOf L j) + (GlobalTheory.ExpTie.Lift.wts L j).j τ + (GlobalTheory.ExpTie.parOf L j).t → (GlobalTheory.ExpTie.Lift.wts L j).lam τ a = (GlobalTheory.ExpTie.Lift.wts L j).lam τ (Formalism.CohomologicalDescent.ShortWeightBounds.kc (GlobalTheory.ExpTie.parOf L j) + (GlobalTheory.ExpTie.Lift.wts L j).j τ)) ∧ (((GlobalTheory.ExpTie.Lift.wts L j).bot (GlobalTheory.ExpTie.parOf L j) τ : ℝ) + (((GlobalTheory.ExpTie.parOf L j).t : ℝ) - 1) / 2 - (GlobalTheory.ExpTie.Lift.wts L j).c τ = -(GlobalTheory.ExpTie.Lift.wts L j).e τ) := by
  intro D L j τ hv
  have hk := D.R.m_add_three_le_k
  have ht0 := D.R.t_odd.pos
  have hkc : Formalism.CohomologicalDescent.ShortWeightBounds.kc (parOf L j) + (wts L j).j τ = D.R.k + (j : ℕ) := by
    simp only [Formalism.CohomologicalDescent.ShortWeightBounds.kc, parOf, wts]; omega
  have htt : (parOf L j).t = D.R.t := rfl
  have he : (wts L j).e τ = wj D ((j : ℕ) + 1) τ := rfl
  constructor
  · intro a ha1 ha2
    rw [hkc] at ha1 ⊢
    rw [hkc, htt] at ha2
    obtain ⟨s, rfl⟩ := Nat.exists_eq_add_of_le ha1
    have h1 := hv.2.2.1 s (by omega)
    have h0 := hv.2.2.1 0 ht0
    simp only [add_zero, Nat.cast_zero, sub_zero] at h0
    have hU : ((wts L j).U (parOf L j) τ (D.R.k + j + s) : ℝ) = (((wts L j).U (parOf L j) τ (D.R.k + j) - s : ℤ) : ℝ) := by
      push_cast; linarith
    have hU' := Int.cast_injective (α := ℝ) hU
    change Formalism.CohomologicalDescent.UnitNormBounds.UN _ _ _ = Formalism.CohomologicalDescent.UnitNormBounds.UN _ _ _ - _ at hU'
    unfold Formalism.CohomologicalDescent.UnitNormBounds.UN at hU'
    push_cast at hU'
    omega
  · have hrow : Formalism.CohomologicalDescent.ShortWeightBounds.kc (parOf L j) + (wts L j).j τ + (parOf L j).t - 1 = D.R.k + (j : ℕ) + (D.R.t - 1) := by
      rw [hkc, htt]; omega
    have h := hv.2.2.1 (D.R.t - 1) (by omega)
    have hts : ((D.R.t - 1 : ℕ) : ℝ) = (D.R.t : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega)]; simp
    rw [hts] at h
    rw [Formalism.CohomologicalDescent.ShortWeightBounds.Wts.bot, hrow, htt, he]
    linarith

end GlobalTheory.ExpTie.Lift

end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.ExpTie GlobalTheory.ExpTie.Lift

theorem GlobalTheory.ExpTie.Lift.window_cloud : ∀ {D : Formalism.BasicNotions.D7} (L : Formalism.BasicNotions.SizeData₂ D) (j : Fin D.R.m) (τ : D.what₂.Tau), GlobalTheory.ExpTie.Lift.ValsAt L j τ → ((GlobalTheory.ExpTie.Lift.wts L j).c τ ≤ ((GlobalTheory.ExpTie.Lift.wts L j).xm τ : ℝ) ∧ (GlobalTheory.ExpTie.Lift.wts L j).xm τ ≤ (GlobalTheory.ExpTie.Lift.wts L j).xp τ ∧ ((GlobalTheory.ExpTie.Lift.wts L j).xp τ : ℝ) ≤ (GlobalTheory.ExpTie.Lift.wts L j).c τ + (GlobalTheory.ExpTie.parOf L j).S) ∧ ∀ a, a < Formalism.CohomologicalDescent.ShortWeightBounds.kc (GlobalTheory.ExpTie.parOf L j) → (GlobalTheory.ExpTie.Lift.wts L j).xm τ ≤ (GlobalTheory.ExpTie.Lift.wts L j).U (GlobalTheory.ExpTie.parOf L j) τ a ∧ (GlobalTheory.ExpTie.Lift.wts L j).U (GlobalTheory.ExpTie.parOf L j) τ a ≤ (GlobalTheory.ExpTie.Lift.wts L j).xp τ := by
  intro D L j τ hv
  have hS : (GlobalTheory.ExpTie.parOf L j).S = L.Sc := rfl
  have hkc : Formalism.CohomologicalDescent.ShortWeightBounds.kc (GlobalTheory.ExpTie.parOf L j) = D.R.k - 1 := rfl
  have hxm : (GlobalTheory.ExpTie.Lift.wts L j).xm τ = ⌈(GlobalTheory.ExpTie.Lift.wts L j).c τ⌉ := rfl
  have hxp : (GlobalTheory.ExpTie.Lift.wts L j).xp τ = ⌊(GlobalTheory.ExpTie.Lift.wts L j).c τ + L.Sc⌋ := rfl

  have hrow : ∀ a, a < D.R.k - 1 →
      (GlobalTheory.ExpTie.Lift.wts L j).xm τ ≤ (GlobalTheory.ExpTie.Lift.wts L j).U (GlobalTheory.ExpTie.parOf L j) τ a ∧
        (GlobalTheory.ExpTie.Lift.wts L j).U (GlobalTheory.ExpTie.parOf L j) τ a ≤ (GlobalTheory.ExpTie.Lift.wts L j).xp τ := by
    intro a ha
    have h1 := hv.1 a ha
    have h2 := L.cloud_v τ ⟨a, ha⟩
    have hlo : (GlobalTheory.ExpTie.Lift.wts L j).c τ ≤ ((GlobalTheory.ExpTie.Lift.wts L j).U (GlobalTheory.ExpTie.parOf L j) τ a : ℝ) := by
      have : (0 : ℝ) ≤ (((D.hc τ).v ⟨a, ha⟩ : ℚ) : ℝ) := by exact_mod_cast h2.1
      linarith
    have hhi : ((GlobalTheory.ExpTie.Lift.wts L j).U (GlobalTheory.ExpTie.parOf L j) τ a : ℝ) ≤ (GlobalTheory.ExpTie.Lift.wts L j).c τ + L.Sc := by
      have : (((D.hc τ).v ⟨a, ha⟩ : ℚ) : ℝ) ≤ L.Sc := by exact_mod_cast h2.2
      linarith
    rw [hxm, hxp]
    exact ⟨Int.ceil_le.2 hlo, Int.le_floor.2 hhi⟩
  have hk := D.R.m_add_three_le_k
  have hm2 := D.R.two_le_m
  have h0 := hrow 0 (by omega)
  refine ⟨⟨?_, le_trans h0.1 h0.2, ?_⟩, ?_⟩
  · rw [hxm]; exact Int.le_ceil _
  · rw [hxp, hS]; exact Int.floor_le _
  · intro a ha
    rw [hkc] at ha
    exact hrow a ha
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpTie GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds Formalism.CohomologicalDescent.LD Formalism.RankGapBounds.FormsTensorLocalization

theorem _root_.GlobalTheory.T.exists_jointRowWeight_dualWeylModule : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (N : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] (lam : ι → ℕ → ℕ) (Gm : Type) [AddCommGroup Gm] [Module (alg O N lam) Gm], Nontrivial Gm → ∃ w : ι → Fin N → ℕ, GlobalTheory.HighWt.JointWt O N lam Gm w := by
  first | exact @GlobalTheory.HighWt.exists_jointWt | exact GlobalTheory.HighWt.exists_jointWt | (intros; apply GlobalTheory.HighWt.exists_jointWt <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpTie GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds Formalism.CohomologicalDescent.LD Formalism.RankGapBounds.FormsTensorLocalization

theorem _root_.GlobalTheory.T.jointRowWeight_bounds_dualWeylModule : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (N : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] (lam : ι → ℕ → ℕ), (∀ τ, Antitone (res N (lam τ))) → ∀ (Gm : Type) [AddCommGroup Gm] [Module (alg O N lam) Gm] (w : ι → Fin N → ℕ), GlobalTheory.HighWt.JointWt O N lam Gm w → ∀ τ, ∑ a : Fin N, w τ a = ∑ a : Fin N, lam τ a ∧ ∀ a : Fin N, lam τ (N - 1) ≤ w τ a ∧ w τ a ≤ lam τ 0 := by
  first | exact @GlobalTheory.HighWt.jointWt_bounds | exact GlobalTheory.HighWt.jointWt_bounds | (intros; apply GlobalTheory.HighWt.jointWt_bounds <;> assumption)
end

end

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep
open scoped CategoryTheory.Obj
attribute [local instance] CategoryTheory.Hom.group
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelMod)
open MonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Semi


theorem _root_.GlobalTheory.T.exists_class_torsionPoint_localScheme : ∀ {E : Type} [Field E] {X' : Scheme.{0}} [IsIntegral X'] [GlobalTheory.IsNormalScheme X'] (G : Over X') [GrpObj G] [IsCommMonObj G]
    [Smooth G.hom] (n : ℕ) (hn : IsUnit (n : Γ(X', ⊤))) {V : Scheme.{0}} [Nonempty V] (ℓ : V ⟶ X')
    [IsOpenImmersion ℓ] {M : Type} (w : M → (V ⟶ G.left)) (hw : ∀ c, w c ≫ G.hom = ℓ) [IsSeparated G.hom] (act : OAct (𝓞 E) G) (I : Ideal (𝓞 E))
    (hex : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (x : Sp Ω ⟶ V) (P : Sp Ω ⟶ G.left), P ≫ G.hom = x ≫ ℓ →
      (∀ a ∈ I, P ≫ (act.act a).left = P ≫ G.hom ≫ (MonObj.one : 𝟙_ (Over X') ⟶ G).left) → ∃ c, P = x ≫ w c)
    (K : Type) [Field K] [IsAlgClosed K] (P : Sp K ⟶ (torsion G n).left)
    (hP : ∀ a ∈ I, P ≫ (torsion.ι G n).left ≫ (act.act a).left = P ≫ (torsion G n).hom ≫ (MonObj.one : 𝟙_ (Over X') ⟶ G).left) (x : Sp K), ∃ c, GlobalTheory.TorsSpec.ValAt G n ℓ w (P x) c := by
  first | exact @GlobalTheory.TorsSpec.exists_valAt | exact GlobalTheory.TorsSpec.exists_valAt | (intros; apply GlobalTheory.TorsSpec.exists_valAt <;> assumption)

end
end

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.ExpTie GlobalTheory.ExpTie.Lift

theorem _root_.GlobalTheory.T.liftWeightRho_block_constant_centred : ∀ {D : Formalism.BasicNotions.D7} (L : Formalism.BasicNotions.SizeData₂ D) (j : Fin D.R.m) (τ : D.what₂.Tau), GlobalTheory.ExpTie.Lift.ValsAt L j τ → (∀ a, Formalism.CohomologicalDescent.ShortWeightBounds.kc (GlobalTheory.ExpTie.parOf L j) + (GlobalTheory.ExpTie.Lift.wts L j).j τ ≤ a → a < Formalism.CohomologicalDescent.ShortWeightBounds.kc (GlobalTheory.ExpTie.parOf L j) + (GlobalTheory.ExpTie.Lift.wts L j).j τ + (GlobalTheory.ExpTie.parOf L j).t → (GlobalTheory.ExpTie.Lift.wts L j).lam τ a = (GlobalTheory.ExpTie.Lift.wts L j).lam τ (Formalism.CohomologicalDescent.ShortWeightBounds.kc (GlobalTheory.ExpTie.parOf L j) + (GlobalTheory.ExpTie.Lift.wts L j).j τ)) ∧ (((GlobalTheory.ExpTie.Lift.wts L j).bot (GlobalTheory.ExpTie.parOf L j) τ : ℝ) + (((GlobalTheory.ExpTie.parOf L j).t : ℝ) - 1) / 2 - (GlobalTheory.ExpTie.Lift.wts L j).c τ = -(GlobalTheory.ExpTie.Lift.wts L j).e τ) := by
  first | exact @GlobalTheory.ExpTie.Lift.block_centre | exact GlobalTheory.ExpTie.Lift.block_centre | (intros; apply GlobalTheory.ExpTie.Lift.block_centre <;> assumption)

end
end

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.ExpTie GlobalTheory.ExpTie.Lift

theorem _root_.GlobalTheory.T.liftWeightRho_entryValues : ∀ {D : Formalism.BasicNotions.D7} (L : Formalism.BasicNotions.SizeData₂ D) (j : Fin D.R.m) (τ : D.what₂.Tau), Formalism.IndefR.Bridge.IsLamPrime (GlobalTheory.ExpTie.Lift.lamL j τ) ((j : ℕ) + 1) τ → GlobalTheory.ExpTie.Lift.ValsAt L j τ := by
  first | exact @GlobalTheory.ExpTie.Lift.valsAt_of_isLamPrime | exact GlobalTheory.ExpTie.Lift.valsAt_of_isLamPrime | (intros; apply GlobalTheory.ExpTie.Lift.valsAt_of_isLamPrime <;> assumption)

end
end

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.ExpTie GlobalTheory.ExpTie.Lift

theorem _root_.GlobalTheory.T.liftWeightRho_lows_distance_bounds : ∀ {D : Formalism.BasicNotions.D7} (L : Formalism.BasicNotions.SizeData₂ D) (P5 : Formalism.BasicNotions.ParameterChoice' D L) (j : Fin D.R.m) (τ : D.what₂.Tau), GlobalTheory.ExpTie.Lift.ValsAt L j τ → ∀ a, a < (GlobalTheory.ExpTie.parOf L j).Nr → ((Formalism.CohomologicalDescent.ShortWeightBounds.kc (GlobalTheory.ExpTie.parOf L j) ≤ a ∧ a < Formalism.CohomologicalDescent.ShortWeightBounds.kc (GlobalTheory.ExpTie.parOf L j) + (GlobalTheory.ExpTie.Lift.wts L j).j τ) ∨ Formalism.CohomologicalDescent.ShortWeightBounds.kc (GlobalTheory.ExpTie.parOf L j) + (GlobalTheory.ExpTie.Lift.wts L j).j τ + (GlobalTheory.ExpTie.parOf L j).t ≤ a) → 2 * (GlobalTheory.ExpTie.parOf L j).b / (GlobalTheory.ExpTie.parOf L j).lstar + ((GlobalTheory.ExpTie.parOf L j).t : ℝ) / 2 + 3 ≤ |((GlobalTheory.ExpTie.Lift.wts L j).U (GlobalTheory.ExpTie.parOf L j) τ a : ℝ) - (GlobalTheory.ExpTie.Lift.wts L j).c τ + (GlobalTheory.ExpTie.Lift.wts L j).e τ| ∧ |((GlobalTheory.ExpTie.Lift.wts L j).U (GlobalTheory.ExpTie.parOf L j) τ a : ℝ) - (GlobalTheory.ExpTie.Lift.wts L j).c τ + (GlobalTheory.ExpTie.Lift.wts L j).e τ| ≤ (GlobalTheory.ExpTie.parOf L j).η := by
  first | exact @GlobalTheory.ExpTie.Lift.low_dist | exact GlobalTheory.ExpTie.Lift.low_dist | (intros; apply GlobalTheory.ExpTie.Lift.low_dist <;> assumption)

end
end

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.ExpTie GlobalTheory.ExpTie.Lift

theorem _root_.GlobalTheory.T.liftWeightRho_thickPlace_centre_window : ∀ {D : Formalism.BasicNotions.D7} (L : Formalism.BasicNotions.SizeData₂ D) (j : Fin D.R.m) (τ : D.what₂.Tau), GlobalTheory.ExpTie.Lift.ValsAt L j τ → τ ∈ (GlobalTheory.ExpTie.Lift.wts L j).T2 → (GlobalTheory.ExpTie.parOf L j).Thick ((GlobalTheory.ExpTie.Lift.wts L j).e τ) ∧ ((GlobalTheory.ExpTie.Lift.wts L j).xp τ : ℝ) ≤ (GlobalTheory.ExpTie.parOf L j).h := by
  first | exact @GlobalTheory.ExpTie.Lift.thick_of_mem | exact GlobalTheory.ExpTie.Lift.thick_of_mem | (intros; apply GlobalTheory.ExpTie.Lift.thick_of_mem <;> assumption)

end
end
