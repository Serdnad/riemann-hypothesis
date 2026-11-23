module

public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.CompactGapsGE
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle001
public import Mathlib.AlgebraicGeometry.Noetherian
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle003
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LatticeSubQuotientSplit
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle005
public import Mathlib.Basic.Complex.Basic
public import Mathlib.NumberTheory.NumberField.Basic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle038
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle061
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle007
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle010
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle006
public import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.Bundle014
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle008
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle011
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Bundle002
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle009
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle085
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle029
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.Bundle017
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle001
import Development.AutomorphicSpectrum.Definitions.AdelicLattices.Bundle001
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.GermComp1ZeroPointLeft
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsSplitGaussChars
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle004
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle084
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.HolJetA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.ValAtLem
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle052
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ExistsIntSmulIsAdicIntegralInTensorBasis
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle086
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.PermFinTwoUniv

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagStep

namespace GlobalTheory.CompanionTheory.Ar.FlagStep

theorem card_strictLower (n : ℕ) [Fintype {lk : Fin n × Fin n // lk.2 < lk.1}] :
    Fintype.card {lk : Fin n × Fin n // lk.2 < lk.1} = n.choose 2 := by
  let e : {lk : Fin n × Fin n // lk.2 < lk.1} ≃ Σ i : Fin n, Fin i.val :=
    { toFun := fun x => ⟨x.1.1, ⟨x.1.2.val, x.2⟩⟩
      invFun := fun y => ⟨(y.1, ⟨y.2.val, y.2.2.trans y.1.2⟩), y.2.2⟩
      left_inv := fun ⟨⟨_, _⟩, _⟩ => rfl
      right_inv := fun ⟨_, _⟩ => rfl }
  rw [Fintype.card_congr e, Fintype.card_sigma]
  simp only [Fintype.card_fin]
  rw [Fin.sum_univ_eq_sum_range (fun i => i) n, Finset.sum_range_id, Nat.choose_two_right]

theorem choose_two_add (p q : ℕ) :
    (p + q).choose 2 = p * q + p.choose 2 + q.choose 2 := by
  induction q with
  | zero => simp
  | succ k ih =>
    rw [← add_assoc, Nat.choose_succ_succ' (p + k) 1, Nat.choose_succ_succ' k 1, ih,
      Nat.choose_one_right, Nat.choose_one_right]
    ring

theorem dim_add_card_strictLower : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H)
    (c : Coeff l) [Fintype (CMType H)] [Fintype (Σ s : CMType H ⊕ CMType H, {lk : Fin (labelRk D s) × Fin (labelRk D s) // lk.2 < lk.1})],
    D.dim + Fintype.card (Σ s : CMType H ⊕ CMType H, {lk : Fin (labelRk D s) × Fin (labelRk D s) // lk.2 < lk.1}) =
      Top.dimFl (CMType H) (D.p + D.q) := by
  intro E _ _ _ H D l c _ _
  have hc : 2 * Fintype.card (CMType H) = Module.finrank ℚ E := by
    have h := (GlobalTheory.CompanionTheory.Ar.labels_all_once E H l c).2
    rw [Nat.card_eq_fintype_card, Fintype.card_sum] at h
    omega
  have hs : Fintype.card (Σ s : CMType H ⊕ CMType H,
      {lk : Fin (labelRk D s) × Fin (labelRk D s) // lk.2 < lk.1}) =
      Fintype.card (CMType H) * D.p.choose 2 + Fintype.card (CMType H) * D.q.choose 2 := by
    classical
    rw [← Nat.card_eq_fintype_card, Nat.card_sigma, Fintype.sum_sum_type]
    simp only [Nat.card_eq_fintype_card]
    rw [Finset.sum_congr rfl (fun a _ => card_strictLower (labelRk D (Sum.inl a))),
      Finset.sum_congr rfl (fun a _ => card_strictLower (labelRk D (Sum.inr a)))]
    simp only [labelRk, Sum.elim_inl, Sum.elim_inr, Finset.sum_const, Finset.card_univ, smul_eq_mul]
  rw [hs, Top.dimFl, Datum.dim, ← hc, ← Nat.choose_two_right, choose_two_add,
    Nat.mul_div_cancel_left _ (by norm_num : 0 < 2)]
  ring

end GlobalTheory.CompanionTheory.Ar.FlagStep
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric
open ReciprocityTheory.ChartRestriction.G.TB.ValAt ReciprocityTheory.ChartRestriction.G.PullbackSections
open GlobalTheory.CompanionTheory.Ar.Flat.GagaC

namespace GlobalTheory.CompanionTheory.Ar.Flat.GagaC.Transition

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Sp Ω ⟶ X}

theorem germ_res_val {U W : X.Opens} (h : W ≤ U) (u : Γ(X, U)ˣ) (q : X) (hq : q ∈ W) :
    X.presheaf.germ W q hq (res h u).val = X.presheaf.germ U q (h hq) u.val :=
  TopCat.Presheaf.germ_res_apply X.presheaf (homOfLE h) q hq u.val

theorem sec_ext {U : X.Opens} {s t : Γ(X, U)}
    (h : ∀ q (hq : q ∈ U), X.presheaf.germ U q hq s = X.presheaf.germ U q hq t) : s = t :=
  TopCat.Presheaf.section_ext X.sheaf U s t h

theorem exists_unit_of_unitAt [IsLocallyNoetherian X] (hξ : IsCptGen ξ) (U : X.Opens)
    (hU : ∀ q ∈ U, genPt ξ ⤳ q) (a : Ω) (ha : ∀ q (hq : q ∈ U), unitAt ξ ⟨q, hU q hq⟩ a) :
    ∃ u : Γ(X, U)ˣ, ∀ q (hq : q ∈ U), genMap ξ ⟨q, hU q hq⟩ (X.presheaf.germ U q hq u.val) = a := by
  by_cases hne : (U : Set X).Nonempty
  · obtain ⟨s, hs, -⟩ := RegSection.existsUnique_section X Ω ξ hξ U hU a hne fun q hq => (ha q hq).2.1
    obtain ⟨t, ht, -⟩ := RegSection.existsUnique_section X Ω ξ hξ U hU a⁻¹ hne fun q hq => (ha q hq).2.2
    have st : s * t = 1 := RegSection.section_eq hξ U hU _ _ fun q hq => by
      rw [map_mul, map_mul, hs q hq, ht q hq, map_one, map_one, mul_inv_cancel₀ (ha q hq).1]
    exact ⟨⟨s, t, st, by rw [mul_comm, st]⟩, hs⟩
  · exact ⟨1, fun q hq => (hne ⟨q, hq⟩).elim⟩

theorem exists_transition : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) [IsLocallyNoetherian X] (I : Type) (V : Option I → X.Opens) (T : I → Ω), IsCptGen ξ → (∀ i, ∀ q ∈ V (some i), genPt ξ ⤳ q) → (∀ q ∈ V none, ¬ genPt ξ ⤳ q) → (∀ (i j : I) (q : X) (hq : genPt ξ ⤳ q), q ∈ V (some i) → q ∈ V (some j) → unitAt ξ ⟨q, hq⟩ (T j / T i)) → (⨆ i, V i = ⊤) → ∃ g : ∀ i j, Γ(X, V i ⊓ V j)ˣ, (LB.mk (Option I) V g).IsLB ∧ ∀ (i j : I) (q : X) (hq : genPt ξ ⤳ q) (h : q ∈ V (some i) ⊓ V (some j)), genMap ξ ⟨q, hq⟩ (X.presheaf.germ _ q h (g (some i) (some j)).val) = T j / T i := by
  intro X Ω _ ξ _ I V T hξ hsome hnone hunit hcov
  have hU : ∀ (i j : I), ∀ q ∈ V (some i) ⊓ V (some j), genPt ξ ⤳ q := fun i j q hq => hsome i q hq.1
  have A := fun i j => exists_unit_of_unitAt hξ (V (some i) ⊓ V (some j)) (hU i j) (T j / T i)
    fun q hq => hunit i j q _ hq.1 hq.2
  choose u hu using A
  obtain ⟨g, hg₁, hg₂, hg₃⟩ : ∃ g : ∀ i j, Γ(X, V i ⊓ V j)ˣ, (∀ i j, g (some i) (some j) = u i j) ∧
      (∀ j, g none j = 1) ∧ (∀ i, g (some i) none = 1) :=
    ⟨fun i j => match i, j with
      | some i, some j => u i j
      | none, _ => 1
      | some _, none => 1, fun _ _ => rfl, fun _ => rfl, fun _ => rfl⟩
  have val : ∀ (i j : I) {W : X.Opens} (h : W ≤ V (some i) ⊓ V (some j)) (q : X) (hq : q ∈ W)
      (hq' : genPt ξ ⤳ q), genMap ξ ⟨q, hq'⟩ (X.presheaf.germ W q hq (res h (u i j)).val) = T j / T i := by
    intro i j W h q hq hq'
    rw [germ_res_val]
    exact hu i j q (h hq)
  refine ⟨g, ⟨hcov, ?_, ?_⟩, fun i j q hq h => ?_⟩
  · intro i
    dsimp only
    apply Units.ext
    rcases i with _ | i
    · simp only [hg₂, map_one]
    · apply sec_ext
      intro q hq
      have hq' := hsome i q hq
      apply hξ.inj ⟨q, hq'⟩
      rw [hg₁, val i i _ q hq hq', Units.val_one, map_one, map_one]
      exact div_self fun e => (hunit i i q hq' hq hq).1 (by simp [e])
  · intro i j k
    dsimp only
    apply Units.ext
    apply sec_ext
    rintro q ⟨⟨hi, hj⟩, hk⟩
    have bad : ∀ a : I, q ∈ V none → q ∈ V (some a) → False := fun a h h' => hnone q h (hsome a q h')
    rcases i with _ | i <;> rcases j with _ | j <;> rcases k with _ | k
    · simp only [hg₂, map_one, _root_.mul_one]
    · exact (bad _ hi hk).elim
    · exact (bad _ hi hj).elim
    · exact (bad _ hi hj).elim
    · exact (bad _ hj hi).elim
    · exact (bad _ hj hi).elim
    · exact (bad _ hk hi).elim
    · have hq' := hsome i q hi
      apply hξ.inj ⟨q, hq'⟩
      have n₁ := (hunit i j q hq' hi hj).1
      have t₁ : T i ≠ 0 := fun e => n₁ (by simp [e])
      have t₂ : T j ≠ 0 := fun e => n₁ (by simp [e])
      simp only [hg₁, Units.val_mul, map_mul]
      have hW : q ∈ V (some i) ⊓ V (some j) ⊓ V (some k) := ⟨⟨hi, hj⟩, hk⟩
      have e₁ := val i j (W := V (some i) ⊓ V (some j) ⊓ V (some k)) inf_le_left q hW hq'
      have e₂ := val j k (W := V (some i) ⊓ V (some j) ⊓ V (some k))
        (le_inf (inf_le_left.trans inf_le_right) inf_le_right) q hW hq'
      have e₃ := val i k (W := V (some i) ⊓ V (some j) ⊓ V (some k))
        (le_inf (inf_le_left.trans inf_le_left) inf_le_right) q hW hq'
      refine (congrArg₂ (· * ·) e₁ e₂).trans (Eq.trans ?_ e₃.symm)
      field_simp
  · simpa only [hg₁] using hu i j q h

end GlobalTheory.CompanionTheory.Ar.Flat.GagaC.Transition
end

section

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField

theorem _root_.GlobalTheory.T.lattice_sub_quotient_split : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (E : Type) [AddCommGroup E] [Module Ω E] (L : Lat ξ E) (T : Set (Cpt ξ)) (g s : ℕ) (W V : Submodule Ω E) (W' : Submodule Ω (E ⧸ V)), V ≤ W → L.IsVBOn T g W → (L.map V.mkQ).IsVBOn T s W' → (L.inter V).IsVBOn T (Module.finrank Ω V) V ∧ ∀ p ∈ T, ∃ Q : Submodule (regAt ξ p) E, Disjoint Q (L.inter V p) ∧ Q ⊔ L.inter V p = L p := by
  first | exact @GlobalTheory.CompanionTheory.Ar.inter_isVBOn_of_map | exact GlobalTheory.CompanionTheory.Ar.inter_isVBOn_of_map | (intros; apply GlobalTheory.CompanionTheory.Ar.inter_isVBOn_of_map <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.RootHt GroundTheory.Heights₂.Heights


theorem _root_.GlobalTheory.T.lie_model_value_lift : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (G : Over X) [GrpObj G]
    (Li : Type) [AddCommGroup Li] [Module Ω Li] (M : LieModel G ξ Li) (L : Type) [Field L] [NumberField L]
    (z : Sp (𝓞 L) ⟶ X) (σ : L →+* ℂ) (Bc : Type) [AddCommGroup Bc] [Module (𝓞 L) Bc] (MB : LieModel G z Bc) (x : Bc) (e : Li)
    (v : epsAt (spMap (algebraMap (𝓞 L) L) ≫ z) ⟶ G),
    M.ValAt _ e v → (v.left ≫ (𝟙 G.left) = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (GlobalTheory.CompanionTheory.Ar.dualMap (algebraMap (𝓞 L) L)) ≫ (MB.pt x).left) →
    ∃ v' : epsAt (spMap (σ.comp (algebraMap (𝓞 L) L)) ≫ z) ⟶ G, M.ValAt _ e v' ∧
      (v'.left ≫ (𝟙 G.left) = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (GlobalTheory.CompanionTheory.Ar.dualMap (σ.comp (algebraMap (𝓞 L) L))) ≫ (MB.pt x).left) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.RootHt.pull_lie_value | exact GlobalTheory.CompanionTheory.Ar.RootHt.pull_lie_value | (intros; apply GlobalTheory.CompanionTheory.Ar.RootHt.pull_lie_value <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.XR
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.full_level_structure_properties : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H), ∀ (X : Scheme.{0}) (t : SAB H X) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (N : ℕ), 0 < N → ∀ (z : Ωˣ) (ev : D.La → (Over.mk ξ ⟶ t.G)), IsFullLevelAt D t ξ N z ev → IsPrimitiveRoot z N ∧ (∀ a b, ev (a + b) = ev a * ev b) ∧ (∀ (r : 𝓞 E) a, ev (r • a) = ev a ≫ t.act.act r) ∧ (∀ a, ev a = 1 ↔ ∃ b, a = N • b) ∧ (∀ g : Over.mk ξ ⟶ t.G, g ^ N = 1 ↔ ∃ a, ev a = g) ∧ FullTorsion t.G ξ N ∧ ∀ (k : Type) [Field k] [IsAlgClosed k] (i : Ω →+* k) (a b : D.La) (g g' : Over.mk (spMap i ≫ ξ) ⟶ t.G), g.left = spMap i ≫ (ev a).left → g'.left = spMap i ≫ (ev b).left → Out.WeilIs t.G t.PP.L N g g' (unitOn (Units.map i.toMonoidHom z ^ D.EF a b)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.XR.fullLevel_props | exact GlobalTheory.CompanionTheory.Ar.XR.fullLevel_props | (intros; apply GlobalTheory.CompanionTheory.Ar.XR.fullLevel_props <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.Label

theorem automorphism_permutes_labels : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (l : Level H) (c : Coeff l) (g : HostAut H), ∃ π : CMType H ≃ CMType H, (∀ τ, (π τ).1 = τ.1.comp g.σ.toRingHom) ∧ ∀ s, labelEmb c (Sum.map π π s) = (labelEmb c s).comp g.s.toRingHom :=
  @PositivityTheory.UnitarySelfGeneration.cm_type_label_twist_permutation

end GlobalTheory.CompanionTheory.Ar.Label
end

section

open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)

namespace GlobalTheory.CompanionTheory.Ar.Num

def FamilyExistsPos : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l)
    (c : Coeff l) (O₀ : Type) [CommRing O₀] (β : O₀ →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω]
    (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω)
    (𝔐 : HodgeCpt Y S y) (d : ℕ), IsArithVar (mCoordIdeal y) (d + 1) → 0 < D.p + D.q →
    ∀ (b : ∀ t, Fin (labelRk D t) → 𝔐.Li), (∀ t, LinearIndependent Ω (b t) ∧ Submodule.span Ω (Set.range (b t)) = 𝔐.Vgen t) →
    ∀ p ∈ S, HT.HTFree 𝔐 p → p ≠ 2 → ¬ (p : ℤ) ∣ NumberField.discr E →
    ∀ φ : Equiv.Perm (CMType H ⊕ CMType H), IsFrobLabels c p φ →
    ∀ (A : Type) [CommRing A] [Algebra A Ω] [IsIntegralClosure A ℤ Ω],
      AtPlacesOver A Ω p fun O _ _ _ _ => ∀ t₀, ∃ (Sg : Type) (_ : Fintype Sg) (e : Sg → CMType H ⊕ CMType H)
        (φ' : Equiv.Perm Sg) (F : Type) (_ : Field F) (_ : Fintype F) (_ : CharP F p) (w : O)
        (σ : Sg → F →+* IsLocalRing.ResidueField O)
        (Df : (∀ k, J k) → LieLatticeData Ω F (D.p + D.q) Sg (fun τ => labelRk D (e τ)) fun τ => labelRk D (e τ).swap),
        t₀ ∈ Set.range e ∧ (∀ τ, e (φ' τ) = φ (e τ)) ∧ IsPreFamily O y p w σ φ' Df ∧
        IsFamilyOf O y Df (fun τ => 𝔐.dR (e τ)) (fun τ => 𝔐.HT p (e τ)) (fun τ => 𝔐.dR (e τ).swap)
          (fun τ => 𝔐.HT p (e τ).swap) (fun τ => b (e τ)) fun τ => b (e τ).swap

end GlobalTheory.CompanionTheory.Ar.Num
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

theorem _root_.GlobalTheory.T.hodge_gram_linear_combination : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (L : LB G.left) (x : Sp ℂ ⟶ S) (n n' : ℕ) (v : Fin n → (epsAt x ⟶ G)) (v' : Fin n' → (epsAt x ⟶ G)) (Γ : Matrix (Fin n) (Fin n) ℂ) (A : Matrix (Fin n') (Fin n) ℂ), (∀ k, IsTanAt G x (v k)) → IsHodgeGram G L x v Γ → (∀ k, IsComb (A k) v (v' k)) → IsHodgeGram G L x v' (A * Γ * Aᴴ) := by
  first | exact @GlobalTheory.CompanionTheory.Relay.hodge_gram_linear_combination | exact GlobalTheory.CompanionTheory.Relay.hodge_gram_linear_combination | (intros; apply GlobalTheory.CompanionTheory.Relay.hodge_gram_linear_combination <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

theorem _root_.GlobalTheory.T.lie_model_eigenvectors_action : ∀ (S : Scheme.{0}) (R : Type) [CommRing R] (G : Over S) [GrpObj G] (x : Sp R ⟶ S) (U : Type) [AddCommGroup U] [Module R U] (M : LieModel G x U), (∀ (n : ℕ) (c : Fin n → R) (u : Fin n → U) w, IsComb c (fun k => M.pt (u k)) w ↔ w = M.pt (∑ k, c k • u k)) ∧ ∀ (O : Type) [CommRing O] (act : OAct O G) (ρ : O →+* Module.End R U) (τ : O →+* R), M.IsActOf act.act ρ → (∀ u, IsEigVec act x τ (M.pt u) ↔ u ∈ eigSp ρ τ) ∧ ∀ (n : ℕ) (u : Fin n → U), IsEigFrame act x τ (fun k => M.pt (u k)) ↔ LinearIndependent R u ∧ Submodule.span R (Set.range u) = eigSp ρ τ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Fl.Bridge.comb_eig_frame | exact GlobalTheory.CompanionTheory.Ar.Fl.Bridge.comb_eig_frame | (intros; apply GlobalTheory.CompanionTheory.Ar.Fl.Bridge.comb_eig_frame <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.Flat.CPoint

theorem _root_.GlobalTheory.T.eigen_frame_iff_eigenspace_basis : ∀ (S : Scheme.{0}) (R : Type) [CommRing R] (G : Over S) [GrpObj G] [IsCommMonObj G] (x : Sp R ⟶ S) (Em : Type)
    [AddCommGroup Em] [Module R Em] (M : LieModel G x Em) (Oe : Type) [CommRing Oe] (act : OAct Oe G)
    (ρ : Oe →+* Module.End R Em) (τ : Oe →+* R) (n : ℕ) (b : Fin n → Em), M.IsActOf act.act ρ →
    (IsEigFrame act x τ (fun i => M.pt (b i)) ↔
      (∀ i, b i ∈ eigSp ρ τ) ∧ ∀ e ∈ eigSp ρ τ, ∃! cf : Fin n → R, e = ∑ i, cf i • b i) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.LieEigFrame.isEigFrame_pt_iff | exact GlobalTheory.CompanionTheory.Ar.Flat.LieEigFrame.isEigFrame_pt_iff | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.LieEigFrame.isEigFrame_pt_iff <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GlobalTheory.CompanionTheory.Ar.Cusp.FamEx

namespace GlobalTheory.CompanionTheory.Ar.Cusp.FamEx

theorem conj_eq_neg_of_sq {d : ℕ} (hd : 0 < d) {z : ℂ} (h : z ^ 2 = -(d : ℂ)) : starRingEnd ℂ z = -z :=
  _root_.UpperTheory.Reformulated.B.ConjEqNegOfSquare.conj_eq_neg_of_sq hd h

theorem exists_emb_label : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (l : Tor.Level H) (c : Coeff l) (κ : c.F →+* ℂ) (lab : CMType H ⊕ CMType H), ∃ s : E →+* ℂ, κ.comp (labelEmb c lab) = s.comp (algebraMap (𝓞 E) E) ∧ ∀ ρ : c.F, (ρ : ℂ) = H.rt0 → s (H.rt : E) = Sum.elim (fun _ => κ ρ) (fun _ => -κ ρ) lab := by
  intro E _ _ _ H l c κ lab
  rcases lab with τ | τ
  · refine ⟨κ.comp (τ.1.codRestrict c.F (c.conj τ.1)), rfl, fun ρ hρ => ?_⟩
    show κ _ = κ ρ
    congr 1
    apply Subtype.ext
    exact τ.2.trans hρ.symm
  · refine ⟨κ.comp ((τ.1.codRestrict c.F (c.conj τ.1)).comp (IsCMField.complexConj E : E →+* E)), ?_, fun ρ hρ => ?_⟩
    · refine RingHom.ext fun a => ?_
      show κ _ = κ _
      congr 1
      apply Subtype.ext
      show τ.1 ((H.bar a : 𝓞 E) : E) = τ.1 (IsCMField.complexConj E (a : E))
      rw [H.bar_eq]
    · show κ _ = -κ ρ
      rw [← map_neg]
      congr 1
      apply Subtype.ext
      show τ.1 (IsCMField.complexConj E (H.rt : E)) = -(ρ : ℂ)
      rw [IsCMField.complexEmbedding_complexConj, τ.2, hρ]
      exact conj_eq_neg_of_sq H.d_prime.pos H.sqrt_neg_disc_sq

end GlobalTheory.CompanionTheory.Ar.Cusp.FamEx
end

section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat

theorem GlobalTheory.CompanionTheory.Ar.Flat.lineLat_isDegOn : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (Fl : 𝔐.Flag) (xdeg : CMType H × Fin (D.p + D.q) → K → ℤ) (e : CMType H × Fin (D.p + D.q) → Ω) (τ : CMType H), Fl.RootLines xdeg e → (lineLat (𝔐.V (.inl τ)) (𝔐.V (.inr τ)) (labelRk D (.inl τ)) (labelRk D (.inr τ)) (exteriorPower.ιMulti Ω _ (Fl.b (.inl τ))) (exteriorPower.ιMulti Ω _ (Fl.b (.inr τ)))).IsDegOn Set.univ y (∑ i, xdeg (τ, i)) (∏ i, e (τ, i)) :=
  PositivityTheory.Xgn.hodge_component_flag_degree
end
