module

public import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.HasTeich
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle052
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle021
import Formalism.LocalToGlobal.CharacterGerms.ConstMemTypeSetOfNonneg
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.IntegralGermEqGaugedFormalGroupLawExpIntegral
public import Formalism.LocalToGlobal.CharacterGerms.RowTieFB
public import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.IsEigBasisIff
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle048
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle049
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle036
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle042
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsFormalGroupSeriesToricPointExtension
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle033
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle050
public import Formalism.LocalToGlobal.CharacterGerms.Bundle019
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Noetherian.Nilpotent
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle001
import Mathlib.Tactic.ReduceModChar

@[expose] public section

section

open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace GlobalTheory.RowLaw.ShiftSum

variable {C : Type} [Field C]

theorem coeff_tyS_congr (l m : ℕ) {a b : ℕ → C} (h : ∀ s ≤ m, a s = b s) :
    PowerSeries.coeff m (tyS l a) = PowerSeries.coeff m (tyS l b) := by
  unfold tyS
  rw [PowerSeries.coeff_mk, PowerSeries.coeff_mk]
  refine Finset.sum_congr rfl fun s hs => ?_
  rw [h s (Nat.lt_succ_iff.1 (Finset.mem_range.1 hs))]

theorem vpow_succ {N : Type} (s : ℕ) (x : ℕ → N → C) : Vpow (s + 1) x = Vpow 1 (Vpow s x) := by
  funext i n
  simp only [Vpow]
  by_cases h1 : i < 1
  · rw [if_pos h1, if_pos (by omega)]
  · rw [if_neg h1]
    by_cases h2 : i < s + 1
    · rw [if_pos h2, if_pos (by omega)]
    · rw [if_neg h2, if_neg (by omega)]
      congr 1
      omega

theorem partial_eq {N : Type} (y : ℕ → ℕ → N → C) (i M : ℕ) (hM : i < M) (n : N) :
    (∑ s ∈ Finset.range M, Vpow s (y s)) i n = sumV y i n := by
  simp only [sumV, Finset.sum_apply, Vpow]
  symm
  rw [← Finset.sum_subset (s₁ := Finset.range (i + 1)) (s₂ := Finset.range M)
    (Finset.range_subset_range.2 (by omega))]
  · refine Finset.sum_congr rfl fun s hs => ?_
    rw [if_neg (by have := Finset.mem_range.1 hs; omega)]
  · intro s _ hs
    rw [if_pos (by rw [Finset.mem_range] at hs; omega)]

variable {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] {κ : Type} [Fintype κ]

theorem vpow_mem (X : RawChart C d I κ) (V : VF C) (g : Fin 2) (x : ℕ → I g ⊕ JJ I g → C)
    (hx : x ∈ X.TySet V g) (s : ℕ) : Vpow s x ∈ X.TySet V g := by
  induction s with
  | zero =>
    have : Vpow 0 x = x := by
      funext i n
      simp [Vpow]
    rwa [this]
  | succ s ih =>
    rw [vpow_succ]
    exact X.V_mem V g _ ih

noncomputable def logOf (X : RawChart C d I κ) (V : VF C) (g : Fin 2) (x : ℕ → I g ⊕ JJ I g → C) :
    (κ → PowerSeries C) × (JJ I g → PowerSeries C) :=
  (fun i => ∑ c : I g, X.u g c i • tyS V.l (fun s => x s (Sum.inl c)),
   fun q => tyS V.l (fun s => x s (Sum.inr q)) -
        ∑ c : I g, if X.ty g c = X.ty (1 - g) q then
          X.sg1 (X.u g c) (X.u (1 - g) q) • tyS V.l (fun s => x s (Sum.inl c)) else 0)

theorem mem_tySet_iff (X : RawChart C d I κ) (V : VF C) (g : Fin 2) (x : ℕ → I g ⊕ JJ I g → C) :
    x ∈ X.TySet V g ↔ logOf X V g x ∈ Cv X V g := by
  constructor
  · rintro ⟨γ, lam, hγ, hlam, h1, h2⟩
    exact ⟨γ, lam, hγ, hlam, h1, fun q => sub_eq_iff_eq_add.2 (h2 q)⟩
  · rintro ⟨γ, lam, hγ, hlam, h1, h2⟩
    exact ⟨γ, lam, hγ, hlam, h1, fun q => sub_eq_iff_eq_add.1 (h2 q)⟩

theorem coeff_logOf_congr (X : RawChart C d I κ) (V : VF C) (g : Fin 2) {x x' : ℕ → I g ⊕ JJ I g → C} (m : ℕ)
    (h : ∀ s ≤ m, ∀ n, x s n = x' s n) :
    (∀ i, PowerSeries.coeff m ((logOf X V g x).1 i) = PowerSeries.coeff m ((logOf X V g x').1 i)) ∧
      ∀ q, PowerSeries.coeff m ((logOf X V g x).2 q) = PowerSeries.coeff m ((logOf X V g x').2 q) := by
  have key : ∀ n, PowerSeries.coeff m (tyS V.l (fun s => x s n)) = PowerSeries.coeff m (tyS V.l (fun s => x' s n)) :=
    fun n => coeff_tyS_congr V.l m fun s hs => h s hs n
  constructor
  · intro i

    simp only [logOf, map_sum, PowerSeries.coeff_smul, key]
  · intro q

    simp only [logOf, map_sub, map_sum, key]
    congr 1
    refine Finset.sum_congr rfl fun c _ => ?_
    split_ifs
    · simp only [PowerSeries.coeff_smul, key]
    · rfl

theorem sumV_mem_tySet : ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) [NeZero d] (I : Fin 2 → Type) [∀ g, Fintype (I g)] (κ : Type) [Fintype κ] (X : RawChart C d I κ), RLaw X V → ∀ g (y : ℕ → ℕ → I g ⊕ JJ I g → C), (∀ s, y s ∈ X.TySet V g) → sumV y ∈ X.TySet V g := by
  intro C _ V d _ I _ κ _ X hX g y hy
  have hlg0 : ∀ i, MvPowerSeries.constantCoeff (X.lg i) = 0 := fun i => by
    rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hX.lin i 0 (by simp),
      MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPowerSeries.constantCoeff_X]
  have h0 := X.zero_mem hlg0 (hX.axes 0) V g
  have hA := GlobalTheory.T.addCurveStable_of_integralGaugedFormalGroupLaw C V d I κ X hX
  have hP : ∀ M, ∑ s ∈ Finset.range M, Vpow s (y s) ∈ X.TySet V g := fun M =>
    X.sum_mem V g h0 (X.add_mem V g hA hX.uint) _ _ fun s _ => vpow_mem X V g _ (hy s) s
  rw [mem_tySet_iff]
  refine GlobalTheory.T.gaugedCurveLogarithms_closed_under_tadicLimits C V d I κ X hX g (fun M => logOf X V g (∑ s ∈ Finset.range M, Vpow s (y s))) _
    (fun M => (mem_tySet_iff X V g _).1 (hP M)) fun m => ⟨m + 1, fun M hM => ?_⟩
  exact coeff_logOf_congr X V g m fun s hs n => partial_eq y s M (by omega) n

end GlobalTheory.RowLaw.ShiftSum
end

section

open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

theorem _root_.GlobalTheory.T.integralGerm_eq_gaugedFormalGroupLaw_expIntegral : ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) [NeZero d] (I : Fin 2 → Type) [∀ g, Fintype (I g)] (κ : Type) [Fintype κ] (X : RawChart C d I κ), RLaw X V → ∀ (H : ∀ g, X.CartHyp V g) (S : ∀ g, Sys (RawChart.cart (H g))) (t : ∀ g, I g → MvPowerSeries (I g) C), (∀ g, (S g).IsT (t g)) → IntGerm V t = ExpInt X V := by
  first | exact @GlobalTheory.RowLaw.intGerm_eq_expInt | exact GlobalTheory.RowLaw.intGerm_eq_expInt | (intros; apply GlobalTheory.RowLaw.intGerm_eq_expInt <;> assumption)
end

section

open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

theorem _root_.GlobalTheory.T.hasGaugeAdjointTeichmullerEnd_pair_places : ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (O : Type) [CommRing O] [StarRing O] (dd : ℕ) (Y : FBChart C V O dd) (d : ℕ) [NeZero d] (I : Fin 2 → Type) [∀ g, Fintype (I g)] (p : PairData Y d I), ∀ g, HasTeich (Y.raw p) V g := by
  first | exact @GlobalTheory.TeichPair.hasTeich | exact GlobalTheory.TeichPair.hasTeich | (intros; apply GlobalTheory.TeichPair.hasTeich <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.abelianPart_lift_square_zero_unit_point : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : Out.DegPre R) (k : ℕ) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (c : Out.GtCoord I D k G) (S : Type) [CommRing S] [Algebra R S], Kills I k S → ∀ (S' : Type) [CommRing S'] [Algebra R S'] (ρ : S →ₐ[R] S') (σ : S' →ₐ[R] S), ρ.comp σ = AlgHom.id R S' → RingHom.ker ρ ^ 2 = ⊥ → ∀ y : sp (R₀ := R) S ⟶ D.P.A, spMap ρ ≫ y = 1 → ∃ z : sp (R₀ := R) S ⟶ G, spMap ρ ≫ z = 1 ∧ QRel c S z y := by
  first | exact @GlobalTheory.ChF.qRel_lift | exact GlobalTheory.ChF.qRel_lift | (intros; apply GlobalTheory.ChF.qRel_lift <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_series_eq_character_on_torsion : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O → ∀ [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] (d : ℕ) (F : FGLaw O d), FH p F.F → ∀ (k : ℕ) (κ : (PS O 1 d →ₐ[O] O) → C), (∀ φ φ' ψ, Killed F.F (p ^ k) φ → Killed F.F (p ^ k) φ' → IsSum F.F φ φ' ψ → κ ψ = κ φ * κ φ') → (∀ φ, (∀ f, φ f = MvPowerSeries.constantCoeff f) → κ φ = 1) → ∃ u : PS O 1 d, ∀ φ, Killed F.F (p ^ k) φ → algebraMap O C (φ u) = κ φ := by
  first | exact @GlobalTheory.character_on_torsion_points_eq_series | exact GlobalTheory.character_on_torsion_points_eq_series | (intros; apply GlobalTheory.character_on_torsion_points_eq_series <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_nilpotentGroupChart_smooth_commGroup : ∀ (R : Type) [CommRing R] [IsLocalRing R] (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (g : ℕ), SmoothOfRelativeDimension g G.hom → ∃ (F : FGLaw R g) (X : Fam G g), NilChart G F.F X := by
  first | exact @GlobalTheory.ChF.exists_nilChart | exact GlobalTheory.ChF.exists_nilChart | (intros; apply GlobalTheory.ChF.exists_nilChart <;> assumption)
end

section

set_option autoImplicit false
noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ChF

private theorem kills_of_algHom {R : Type} [CommRing R] {I : Ideal R} {S S' : Type} [CommRing S] [Algebra R S]
    [CommRing S'] [Algebra R S'] (φ : S →ₐ[R] S') (h : ∃ k, Kills I k S) : ∃ k, Kills I k S' := by
  obtain ⟨k, hk⟩ := h
  exact ⟨k, fun t ht => by rw [← φ.commutes, hk t ht, map_zero]⟩

private theorem exists_split_thickening {R : Type} [CommRing R] {d : ℕ} (S : Type) [CommRing S] [Algebra R S]
    (a : Fin d → S) (ha : ∀ i, IsNilpotent (a i)) :
    ∃ (T : Type) (_ : CommRing T) (_ : Algebra R T) (ρ π : T →ₐ[R] S) (σ : S →ₐ[R] T) (a' : Fin d → T),
      ρ.comp σ = AlgHom.id R S ∧ IsNilpotent (RingHom.ker ρ) ∧ (∀ i, ρ (a' i) = 0) ∧ ∀ i, π (a' i) = a i := by
  let J : Ideal S := Ideal.span (Set.range a)
  have hJ : IsNilpotent J := by
    refine (Ideal.FG.isNilpotent_iff_le_nilradical (Submodule.fg_span (Set.finite_range a))).2 ?_
    rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    exact ha i
  let T : Subalgebra R (S × S) := AlgHom.equalizer ((Ideal.Quotient.mkₐ R J).comp (AlgHom.fst R S S))
    ((Ideal.Quotient.mkₐ R J).comp (AlgHom.snd R S S))
  let ρ : T →ₐ[R] S := (AlgHom.fst R S S).comp T.val
  let π : T →ₐ[R] S := (AlgHom.snd R S S).comp T.val
  let σ : S →ₐ[R] T := ((AlgHom.id R S).prod (AlgHom.id R S)).codRestrict T (fun _ => rfl)
  have hm : ∀ i, ((0, a i) : S × S) ∈ T := fun i => by
    show Ideal.Quotient.mk J 0 = Ideal.Quotient.mk J (a i)
    rw [map_zero, eq_comm, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.subset_span ⟨i, rfl⟩
  refine ⟨T, inferInstance, inferInstance, ρ, π, σ, fun i => ⟨(0, a i), hm i⟩, rfl, ?_, fun _ => rfl, fun _ => rfl⟩
  obtain ⟨N, hN⟩ := hJ
  have hle : RingHom.ker ρ ≤ J.comap π := fun t ht => by
    have h1 : t.1.1 = 0 := ht
    have h2 : Ideal.Quotient.mk J t.1.1 = Ideal.Quotient.mk J t.1.2 := t.2
    rw [h1, map_zero, eq_comm, Ideal.Quotient.eq_zero_iff_mem] at h2
    exact h2
  refine ⟨N + 1, le_bot_iff.1 fun t ht => ?_⟩
  have h1 : t.1.1 = 0 := (Ideal.pow_le_self (Nat.succ_ne_zero N) ht : t ∈ RingHom.ker ρ)
  have h2 := Ideal.le_comap_pow π N (Ideal.pow_right_mono hle N (Ideal.pow_le_pow_right (Nat.le_succ N) ht))
  rw [hN] at h2
  have h3 : π t = 0 := by simpa using h2
  exact Subtype.ext (Prod.ext h1 h3)

private theorem exists_nilpotent_image {R : Type} [CommRing R] {I : Ideal R}
    {G : Over (Spec (CommRingCat.of R))} [GrpObj G] {B : Over (Spec (CommRingCat.of R))} [GrpObj B]
    {X : Type} [AddCommGroup X] (E : PtExt I G B X) {d g : ℕ} {F : Fin d → PS R 2 d} {FB : Fin g → PS R 2 g}
    {x : Fam G d} {xB : Fam B g} (hx : NilChart G F x) (hB : NilChart B FB xB)
    (S : Type) [CommRing S] [Algebra R S] (h : ∃ k, Kills I k S) (a : Fin d → S) (ha : ∀ i, IsNilpotent (a i)) :
    ∃ b : Fin g → S, (∀ j, IsNilpotent (b j)) ∧ E.q S h (x S a) = xB S b := by
  obtain ⟨T, _, _, ρ, π, σ, a', hσ, ⟨N, hN⟩, h0, h1⟩ := exists_split_thickening (R := R) S a ha
  have hT := kills_of_algHom σ h
  have hnil : ∀ t : T, ρ t = 0 → IsNilpotent t := fun t ht => ⟨N, by
    have := Ideal.pow_mem_pow (show t ∈ RingHom.ker ρ from ht) N
    rw [hN] at this
    simpa using this⟩
  have ha' : ∀ i, IsNilpotent (a' i) := fun i => hnil _ (h0 i)
  obtain ⟨b, hb, hz⟩ := hB.surj T S ρ σ hσ ⟨N, hN⟩ (E.q T hT (x T a')) (by
    rw [← E.q_nat T S ρ hT h, hx.nat T S ρ a' ha', show (fun i => ρ (a' i)) = 0 from funext h0, hx.zero,
      map_one])
  have hb' : ∀ j, IsNilpotent (b j) := fun j => hnil _ (hb j)
  refine ⟨fun j => π (b j), fun j => (hb' j).map π, ?_⟩
  rw [← hB.nat T S π b hb', ← hz, ← E.q_nat T S π hT h, hx.nat T S π a' ha', show (fun i => π (a' i)) = a from funext h1]

theorem ptExt_q_series : ∀ (R : Type) [CommRing R] (I : Ideal R) [IsAdicComplete I R] (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (B : Over (Spec (CommRingCat.of R))) [GrpObj B] [IsCommMonObj B] (X : Type) [AddCommGroup X] (E : PtExt I G B X) (d g : ℕ) (F : FGLaw R d) (FB : FGLaw R g) (x : Fam G d) (xB : Fam B g), NilChart G F.F x → NilChart B FB.F xB → ∃ Q : Fin g → PS R 1 d, IsHomF F.F FB.F Q ∧ (∀ (S : Type) [CommRing S] [Algebra R S] (h : ∃ k, Kills I k S) (a : Fin d → S), (∀ i, IsNilpotent (a i)) → E.q S h (x S a) = xB S (fun j => nv (algebraMap R S) (Q j) ![a])) := by
  intro R _ I hI G _ _ B _ _ X _ E d g F FB x xB hx hB
  classical
  let c : ∀ (S : Type) [CommRing S] [Algebra R S], (Fin d → S) → Fin g → S := fun S _ _ a =>
    if h : (∃ k, Kills I k S) ∧ ∀ i, IsNilpotent (a i) then
      (exists_nilpotent_image E hx hB S h.1 a h.2).choose else 0
  have hc : ∀ (S : Type) [CommRing S] [Algebra R S] (h : ∃ k, Kills I k S) (a : Fin d → S),
      (∀ i, IsNilpotent (a i)) → (∀ j, IsNilpotent (c S a j)) ∧ E.q S h (x S a) = xB S (c S a) := by
    intro S _ _ h a ha
    have : c S a = (exists_nilpotent_image E hx hB S h a ha).choose := dif_pos ⟨h, ha⟩
    rw [this]
    exact (exists_nilpotent_image E hx hB S h a ha).choose_spec
  have hnat : ∀ (S : Type) [CommRing S] [Algebra R S] (S' : Type) [CommRing S'] [Algebra R S'] (φ : S →ₐ[R] S')
      (a : Fin d → S), (∃ k, Kills I k S) → (∀ i, IsNilpotent (a i)) →
      (fun j => φ (c S a j)) = c S' (fun i => φ (a i)) := by
    intro S _ _ S' _ _ φ a h ha
    have h' := kills_of_algHom φ h
    have ha' : ∀ i, IsNilpotent (φ (a i)) := fun i => (ha i).map φ
    refine hB.inj S' _ _ (fun j => ((hc S h a ha).1 j).map φ) (hc S' h' _ ha').1 ?_
    rw [← (hc S' h' _ ha').2, ← hB.nat S S' φ _ (hc S h a ha).1, ← (hc S h a ha).2, ← E.q_nat S S' φ h h',
      hx.nat S S' φ a ha]
  choose Q hQ using fun j : Fin g => GlobalTheory.T.exists_powerSeries_of_natural_nilpotentPoints R I hI 1 d (fun _ _ _ => True) (fun _ _ => trivial)
    (fun S _ _ a => c S (a 0) j)
    (fun S _ _ S' _ _ φ a _ _ _ h ha => congrFun (hnat S S' φ (a 0) h (ha 0)) j)
  have hQ' : ∀ (S : Type) [CommRing S] [Algebra R S] (h : ∃ k, Kills I k S) (a : Fin d → S),
      (∀ i, IsNilpotent (a i)) → (fun j => nv (algebraMap R S) (Q j) ![a]) = c S a := by
    intro S _ _ h a ha
    funext j
    exact (hQ j S ![a] trivial h (fun i l => by fin_cases i; exact ha l)).symm
  have hconst : ∀ j, MvPowerSeries.constantCoeff (Q j) = 0 := by
    intro j
    refine IsHausdorff.haus (I := I) inferInstance _ fun k => ?_
    have hk : ∃ m, Kills I m (R ⧸ I ^ (k + 1)) := ⟨k, fun t ht => Ideal.Quotient.eq_zero_iff_mem.2 ht⟩
    have h0 : ∀ i : Fin d, IsNilpotent ((0 : Fin d → R ⧸ I ^ (k + 1)) i) := fun _ => IsNilpotent.zero
    have h1 : c (R ⧸ I ^ (k + 1)) 0 = 0 :=
      hB.inj _ _ _ (hc _ hk 0 h0).1 (fun _ => IsNilpotent.zero) (by
        rw [← (hc _ hk 0 h0).2, hx.zero, hB.zero, map_one])
    have h2 := congrFun (hQ' _ hk 0 h0) j
    have h3 := (nv_calculus R (R ⧸ I ^ (k + 1)) (algebraMap _ _) 1 d ![0]
      (fun i l => by fin_cases i; exact h0 l)).2.2.2.2.2 (fun i l i' l' => by fin_cases i; simp) (Q j)
    rw [h1] at h2
    rw [h2] at h3
    have h4 : algebraMap R (R ⧸ I ^ (k + 1)) (MvPowerSeries.constantCoeff (Q j)) = 0 := by
      simpa using h3.symm
    rw [SModEq.zero, smul_eq_mul, Ideal.mul_top]
    exact Ideal.pow_le_pow_right (Nat.le_succ k) (Ideal.Quotient.eq_zero_iff_mem.1 h4)
  refine ⟨Q, ⟨hconst, fun j => ?_⟩, fun S _ _ h a ha => by rw [hQ' S h a ha]; exact (hc S h a ha).2⟩
  refine GlobalTheory.T.powerSeries_eq_of_evalAtNilpotentPoints_eq R I inferInstance 2 d _ _ fun S _ _ k hk _ a ha => ?_
  have h : ∃ k, Kills I k S := ⟨k, hk⟩
  obtain ⟨⟨ψ, hψ, -, hX⟩, hn, hs, -⟩ := nv_calculus R S (algebraMap R S) 2 d a ha
  have hpt : ∀ i : Fin 2, ∀ l, nv (algebraMap R S) (ev (n := 2) ![pt R d i] (Q l)) a = c S (a i) l := by
    intro i l
    have e := hs 1 d ![pt R d i] (Q l) (fun i' l' => by fin_cases i'; simp [pt])
    have e2 : (fun i' l' => nv (algebraMap R S) ((![pt R d i] : Fin 1 → Fin d → PS R 2 d) i' l') a) = ![a i] := by
      funext i' l'
      fin_cases i'
      exact (hψ _).symm.trans (hX (i, l'))
    rw [e2] at e
    exact e.trans (congrFun (hQ' S h (a i) (ha i)) l)
  have hpc : ∀ i : Fin 2, ∀ l, MvPowerSeries.constantCoeff (ev (n := 2) ![pt R d i] (Q l)) = 0 := by
    intro i l
    refine MvPowerSeries.constantCoeff_subst_eq_zero (MvPowerSeries.hasSubst_of_constantCoeff_zero ?_) ?_ (hconst l)
    all_goals
      rintro ⟨i', l'⟩
      fin_cases i'
      simp [pt]
  have ea : a = ![a 0, a 1] := by funext i; fin_cases i <;> rfl
  have hFn : ∀ l, IsNilpotent (nv (algebraMap R S) (F.F l) a) := fun l => (hn _ (F.const l)).1
  have e1 := hs 1 d ![F.F] (Q j) (fun i' l' => by fin_cases i'; exact F.const l')
  have e2 : (fun i' l' => nv (algebraMap R S) ((![F.F] : Fin 1 → Fin d → PS R 2 d) i' l') a) =
      ![fun l => nv (algebraMap R S) (F.F l) a] := by
    funext i' l'
    fin_cases i'
    rfl
  rw [e2] at e1
  have e3 := hs 2 g ![fun i => ev (n := 2) ![pt R d 0] (Q i), fun i => ev (n := 2) ![pt R d 1] (Q i)] (FB.F j)
    (fun i' l' => by fin_cases i'; exacts [hpc 0 l', hpc 1 l'])
  have e4 : (fun i' l' => nv (algebraMap R S) ((![fun i => ev (n := 2) ![pt R d 0] (Q i),
      fun i => ev (n := 2) ![pt R d 1] (Q i)] : Fin 2 → Fin g → PS R 2 d) i' l') a) = ![c S (a 0), c S (a 1)] := by
    funext i' l'
    fin_cases i'
    exacts [hpt 0 l', hpt 1 l']
  rw [e4] at e3
  have hcn : ∀ i l, IsNilpotent ((![c S (a 0), c S (a 1)] : Fin 2 → Fin g → S) i l) := fun i l => by
    fin_cases i
    exacts [(hc S h _ (ha 0)).1 l, (hc S h _ (ha 1)).1 l]
  have key : c S (fun l => nv (algebraMap R S) (F.F l) a) =
      fun l => nv (algebraMap R S) (FB.F l) ![c S (a 0), c S (a 1)] := by
    refine hB.inj S _ _ (hc S h _ hFn).1
      (fun l => ((nv_calculus R S (algebraMap R S) 2 g _ hcn).2.1 _ (FB.const l)).1) ?_
    rw [← (hc S h _ hFn).2, ← hB.law S _ _ (hc S h _ (ha 0)).1 (hc S h _ (ha 1)).1, ← (hc S h _ (ha 0)).2,
      ← (hc S h _ (ha 1)).2, ← map_mul, hx.law S _ _ (ha 0) (ha 1), ← ea]
  rw [e3]
  exact e1.trans ((congrFun (hQ' S h _ hFn) j).trans (congrFun key j))

end GlobalTheory.ChF
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.formalGroup_series_separated_by_torsion : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O → ∀ [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] (d : ℕ) (F : FGLaw O d), FH p F.F → (∀ (k : ℕ) (f : PS O 1 d), (∀ φ, Killed F.F (p ^ k) φ → φ f = 0) → f ∈ Ideal.span (Set.range (mulF F.F (p ^ k)))) ∧ ∀ f : PS O 1 d, (∀ φ, Tors p F.F φ → φ f = 0) → f = 0 := by
  first | exact @GlobalTheory.ChF.mem_span_mulF_of_killed_and_eq_zero_of_tors | exact GlobalTheory.ChF.mem_span_mulF_of_killed_and_eq_zero_of_tors | (intros; apply GlobalTheory.ChF.mem_span_mulF_of_killed_and_eq_zero_of_tors <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_formalGroupSeries_toricPointExtension : ∀ (R : Type) [CommRing R] (I : Ideal R) [IsAdicComplete I R] (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (B : Over (Spec (CommRingCat.of R))) [GrpObj B] [IsCommMonObj B] (X : Type) [AddCommGroup X] (E : PtExt I G B X) (d g : ℕ) (F : FGLaw R d) (FB : FGLaw R g) (x : Fam G d) (xB : Fam B g), NilChart G F.F x → NilChart B FB.F xB → ∀ (r : ℕ) (β : Module.Basis (Fin r) ℤ X), ∃ J : Fin d → PS R 1 r, IsHomF (gmF R r) F.F J ∧ (∀ (S : Type) [CommRing S] [Algebra R S] (h : ∃ k, Kills I k S) (χ : Multiplicative X →* Sˣ) (t : Fin r → S), (∀ i, IsNilpotent (t i)) → (∀ j, (χ (Multiplicative.ofAdd (β j)) : S) = 1 + t j) → E.i S h χ = x S (fun j => nv (algebraMap R S) (J j) ![t])) := by
  first | exact @GlobalTheory.ChF.exists_series_torus | exact GlobalTheory.ChF.exists_series_torus | (intros; apply GlobalTheory.ChF.exists_series_torus <;> assumption)
end

section

open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw GlobalTheory.RowVal ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

theorem _root_.GlobalTheory.T.sum_hEnd_sub_hEnd_mem_logInt : ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (d : ℕ) (I : Fin 2 → Type) [∀ g, Fintype (I g)] (κ : Type) [Fintype κ] [DecidableEq κ] (X : RawChart C d I κ), RLaw X V → ∀ (Orb : Type) [Fintype Orb] (π : Orb → Fin 2 → Matrix κ κ C) (W W' : Matrix κ κ C), (∀ o g, IntEnd X V (π o g)) → IsEnd X V W W' → W + W' = 1 → (∀ o g o' g', ¬ (o = o' ∧ g' = 1 - g) → hEnd X (π o g) (W * π o' g') ∈ logInt V κ) → (∑ o, hEnd X (π o 0) (π o 1)) - hEnd X (∑ o, ∑ g, π o g) (W * ∑ o, ∑ g, π o g) ∈ logInt V κ := by
  first | exact @GlobalTheory.RowVal.MapSumDiagonal.diagonal_split | exact GlobalTheory.RowVal.MapSumDiagonal.diagonal_split | (intros; apply GlobalTheory.RowVal.MapSumDiagonal.diagonal_split <;> assumption)
end

section

open scoped BigOperators
open Formalism.IncomingBounds Formalism.UnitaryBoundIntegral Formalism.L2.FormalSeriesBounds

namespace GlobalTheory.OrbitPlan

theorem exists_good {S : ℕ} {G : Set ℕ} (h : Windows S G) {r : ℝ} (hr : 0 ≤ r) :
    ∃ y ∈ G, (y : ℝ) ≤ r ∧ r - y ≤ S := by
  have h1 := Nat.floor_le hr
  have h2 := Nat.lt_floor_add_one r
  by_cases hS : S ≤ ⌊r⌋₊ + 1
  · obtain ⟨y, hy, hy1, hy2⟩ := h.2 (⌊r⌋₊ + 1 - S)
    have a1 : y ≤ ⌊r⌋₊ := by omega
    have a2 : ⌊r⌋₊ + 1 ≤ y + S := by omega
    have b1 : (y : ℝ) ≤ ⌊r⌋₊ := by exact_mod_cast a1
    have b2 : (⌊r⌋₊ : ℝ) + 1 ≤ y + S := by exact_mod_cast a2
    exact ⟨y, hy, by linarith, by linarith⟩
  · have a2 : ⌊r⌋₊ + 1 ≤ S := by omega
    have b2 : (⌊r⌋₊ : ℝ) + 1 ≤ S := by exact_mod_cast a2
    exact ⟨0, h.1, by simpa using hr, by simp only [Nat.cast_zero]; linarith⟩

theorem logTerm_nonneg {l n : ℕ} (hl : 5 ≤ l) (hn : 1 ≤ n) :
    0 ≤ (n : ℝ) * (Real.logb l n + 1) := by
  have h1 : (1 : ℝ) < l := by exact_mod_cast (by omega : 1 < l)
  have h2 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have := Real.logb_nonneg h1 h2
  positivity

end GlobalTheory.OrbitPlan
end
