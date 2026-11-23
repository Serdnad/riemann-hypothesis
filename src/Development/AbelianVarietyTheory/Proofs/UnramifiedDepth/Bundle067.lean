module

public import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.HasTeich
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle052
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle065
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle060
public import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.IsEigBasisIff
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.UniformizationSplitFormalGroupLawEquivariant
public import Formalism.LocalToGlobal.CharacterGerms.Bundle005
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.RowDataMainTermNormalFormAndLevelOne
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle002
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsAbsoluteValueOfIsDiscreteValuationRing
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle028
public import Formalism.LocalToGlobal.ProjectiveLattices.PlaceBelow
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle008
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle066
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle056
import Formalism.LocalToGlobal.CharacterGerms.ConstMemTypeSetOfNonneg
import Formalism.LocalToGlobal.CharacterGerms.Bundle015
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle058
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle057
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import Mathlib.Tactic.ReduceModChar

@[expose] public section

section

open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace GlobalTheory.RowLaw

theorem cartHyp_of_rlaw : ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) [NeZero d] (I : Fin 2 → Type) [∀ g, Fintype (I g)] (κ : Type) [Fintype κ] (X : RawChart C d I κ), RLaw X V → HasProj X V → (∀ g, HasTeich X V g) → ∀ g, X.CartHyp V g := by
  intro C _ V d _ I _ κ _ X hL hP hT g
  have hlg0 : ∀ i, MvPowerSeries.constantCoeff (X.lg i) = 0 := fun i => by
    rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hL.lin i 0 (by simp),
      MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPowerSeries.constantCoeff_X]
  have hh := hL.axes 0
  refine
    { zero := X.zero_mem hlg0 hh V g
      add := X.add_mem V g (GlobalTheory.T.addCurveStable_of_integralGaugedFormalGroupLaw C V d I κ X hL) hL.uint
      neg := X.neg_mem V g hL.odd
      teich := X.teich_mem V g
      Vm := X.V_mem V g
      Fm := GlobalTheory.T.frobenius_mem_typicalCurveSet C V d I κ X hL g
      sumV := GlobalTheory.T.shiftedSum_mem_typicalCurveSet C V d I κ X hL g
      t2 := X.val_nonneg_leading_coeff_of_mem_tySet V g hL.lin hh ?_ (GlobalTheory.T.integral_gaugeBilinearTerm_of_type_ne C V d I κ X hL g (hT g))
      t3 := X.const_mem_type_set_of_nonneg hlg0 hh V g
      t4 := GlobalTheory.T.exists_pure_typical_curve_with_integral_tangent C V d I κ X hL hP g (hT g) }
  obtain ⟨w, hw, huw⟩ := hL.sat g
  refine ⟨w, hw, fun c c' => ?_⟩
  split_ifs with h
  · exact (huw c c').1 h
  · exact (huw c c').2 h

end GlobalTheory.RowLaw
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.uniformization_split_formal_group_law_equivariant : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : Out.DegData R I) (A : Out.PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : Out.UnifPre I D A G) [IsAdicComplete I R] (d g : ℕ) (F : FGLaw R d) (FB : FGLaw R g) (x : Fam G d) (xB : Fam D.toPre.P.A g), NilChart G F.F x → NilChart D.toPre.P.A FB.F xB → ∃ (r : ℕ) (J : Fin d → PS R 1 r) (Q : Fin g → PS R 1 d), ExtSer F.F FB.F J Q ∧ ∀ (OE : Type) [CommRing OE] [StarRing OE] [Module OE D.toPre.X] (io : Out.RingAct G OE) (oD : D.OAct OE) (oA : A.OAct OE), U.OLinear OE oD oA io → ∀ (α : OE → Fin d → PS R 1 d) (αB : OE → Fin g → PS R 1 g), (∀ a, Reads x x (io.act a) (α a)) → (∀ a, Reads xB xB (oD.onB.act a) (αB a)) → ∃ N : OE →+* Matrix (Fin r) (Fin r) ℤ, ∀ a, lin Q * lin (α a) = lin (αB a) * lin Q ∧ lin (α a) * lin J = lin J * (N a).map (Int.castRingHom R) := by
  first | exact @GlobalTheory.unif_extSer_equivariant | exact GlobalTheory.unif_extSer_equivariant | (intros; apply GlobalTheory.unif_extSer_equivariant <;> assumption)
end

section

open Formalism.L2.FormalSeriesBounds

theorem _root_.GlobalTheory.T.rowData_mainTerm_normalForm_and_levelOne : ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) [NeZero d] (I J : Fin 2 → Type) [∀ g, Fintype (I g)] [∀ g, Fintype (J g)] (X : RowData C V d I J), X.LemmaM ∧ X.LemmaMPlus := by
  first | exact @GlobalTheory.MainTerm.main | exact GlobalTheory.MainTerm.main | (intros; apply GlobalTheory.MainTerm.main <;> assumption)
end

section

open scoped BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj NumberField

namespace GlobalTheory.DvrClosedEmbedding

theorem exists_addValuation_log_norm {C : Type} [NormedField C] [IsUltrametricDist C] {r : ℝ}
    (hr0 : 0 < r) (hr1 : r < 1) :
    ∃ v : AddValuation C (WithTop ℝ),
      (∀ x, x ≠ 0 → v x = ((Real.log ‖x‖ / Real.log r : ℝ) : WithTop ℝ)) ∧
      ∀ (x : C) (n : ℕ), (((n : ℕ) : ℝ) : WithTop ℝ) ≤ v x ↔ ‖x‖ ≤ r ^ n := by
  classical
  have hl : Real.log r < 0 := Real.log_neg hr0 hr1
  let f : C → WithTop ℝ := fun x =>
    if x = 0 then ⊤ else ((Real.log ‖x‖ / Real.log r : ℝ) : WithTop ℝ)
  have hf0 : f 0 = ⊤ := by simp [f]
  have hf : ∀ x, x ≠ 0 → f x = ((Real.log ‖x‖ / Real.log r : ℝ) : WithTop ℝ) := fun x hx => by
    simp [f, hx]
  have hmono : ∀ x y : C, ‖x‖ ≤ ‖y‖ → f y ≤ f x := by
    intro x y h
    by_cases hx : x = 0
    · rw [hx, hf0]; exact le_top
    have hx' : 0 < ‖x‖ := norm_pos_iff.2 hx
    have hy : y ≠ 0 := norm_pos_iff.1 (hx'.trans_le h)
    rw [hf x hx, hf y hy, WithTop.coe_le_coe]
    exact div_le_div_of_nonpos_of_le hl.le (Real.log_le_log hx' h)
  refine ⟨AddValuation.of f hf0 ?_ ?_ ?_, hf, ?_⟩
  · rw [hf 1 one_ne_zero]; simp
  · intro x y
    rcases le_max_iff.1 (IsUltrametricDist.norm_add_le_max x y) with h | h
    · exact min_le_of_left_le (hmono _ _ h)
    · exact min_le_of_right_le (hmono _ _ h)
  · intro x y
    by_cases hx : x = 0
    · rw [hx, zero_mul, hf0, WithTop.top_add]
    by_cases hy : y = 0
    · rw [hy, mul_zero, hf0, WithTop.add_top]
    rw [hf x hx, hf y hy, hf _ (mul_ne_zero hx hy), norm_mul,
      Real.log_mul (norm_ne_zero_iff.2 hx) (norm_ne_zero_iff.2 hy), add_div, WithTop.coe_add]
  · intro x n
    change _ ≤ f x ↔ _
    by_cases hx : x = 0
    · rw [hx, hf0, norm_zero]
      exact ⟨fun _ => by positivity, fun _ => le_top⟩
    rw [hf x hx, WithTop.coe_le_coe, le_div_iff_of_neg hl, ← Real.log_pow,
      Real.log_le_log_iff (norm_pos_iff.2 hx) (pow_pos hr0 n)]

theorem exists_limit_of_norm_sub_le_pow {C : Type} [NormedField C] [IsUltrametricDist C]
    [CompleteSpace C] {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) (s : ℕ → C)
    (hs : ∀ n, ‖s (n + 1) - s n‖ ≤ r ^ n) : ∃ x, ∀ n, ‖x - s n‖ ≤ r ^ n := by
  have hc : CauchySeq s := by
    refine cauchySeq_of_le_geometric r 1 hr1 fun n => ?_
    rw [dist_comm, dist_eq_norm, one_mul]
    exact hs n
  obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hc
  refine ⟨L, fun n => ?_⟩
  refine le_of_tendsto ((hL.sub tendsto_const_nhds).norm) ?_
  filter_upwards [Filter.eventually_ge_atTop n] with m hm
  induction m, hm using Nat.le_induction with
  | base => simp; positivity
  | succ m hm ih =>
    have h := IsUltrametricDist.norm_add_le_max (s (m + 1) - s m) (s m - s n)
    rw [sub_add_sub_cancel] at h
    exact h.trans (max_le ((hs m).trans (pow_le_pow_of_le_one hr0.le hr1.le hm)) ih)

theorem exists_complete_isAlgClosed_addValuation :
    ∀ (T : CDVR) (p : ℕ), p.Prime → ¬ IsUnit (p : T.V) → ∃ (C : Type) (_ : Field C) (_ : CharZero C) (v : AddValuation C (WithTop ℝ)) (ι : T.Fr →+* C), v (p : C) = 1 ∧ (∀ x : T.Fr, x ≠ 0 → v (ι x) = (((vV T.V x : ℝ) / (vV T.V ((p : ℕ) : T.Fr) : ℝ) : ℝ) : WithTop ℝ)) ∧ IsAlgClosed C ∧ ∀ s : ℕ → C, (∀ n : ℕ, (((n : ℕ) : ℝ) : WithTop ℝ) ≤ v (s (n + 1) - s n)) → ∃ x, ∀ n : ℕ, (((n : ℕ) : ℝ) : WithTop ℝ) ≤ v (x - s n) := by
  intro T p hp hu
  have hp0 : (p : T.V) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
  have hr0 : (0 : ℝ) < 1 / 2 := by norm_num
  have hr1 : (1 / 2 : ℝ) < 1 := by norm_num
  obtain ⟨C, _, _, _, _, _, hC, hCp⟩ :=
    exists_complete_isAlgClosed_of_isDiscreteValuationRing T.V T.Fr hp0
      ((IsLocalRing.mem_maximalIdeal _).2 hu) hr0 hr1
  rw [map_natCast] at hCp
  have : CharZero T.Fr := charZero_of_injective_ringHom (IsFractionRing.injective T.V T.Fr)
  have : CharZero C := charZero_of_injective_ringHom (algebraMap T.Fr C).injective
  obtain ⟨v, hv, hvn⟩ := exists_addValuation_log_norm (C := C) hr0 hr1
  have hl : Real.log (1 / 2) ≠ 0 := (Real.log_neg hr0 hr1).ne
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible T.V
  have hz : ∀ x : T.Fr, x ≠ 0 → Real.log ‖algebraMap T.Fr C x‖ =
      (vV T.V x : ℝ) * Real.log ‖algebraMap T.Fr C (algebraMap T.V T.Fr π)‖ := fun x hx => by
    rw [ArcQ.norm_map_eq_zpow_vV (algebraMap T.Fr C) (fun a => (hC _).2 ⟨a, rfl⟩) hπ hx,
      Real.log_zpow]
  have hpF : (p : T.Fr) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
  have hzp := hz p hpF
  rw [hCp] at hzp
  refine ⟨C, inferInstance, inferInstance, v, algebraMap T.Fr C, ?_, fun x hx => ?_,
    inferInstance, fun s hs => ?_⟩
  · rw [map_natCast] at hCp
    rw [hv _ (Nat.cast_ne_zero.2 hp.ne_zero), hCp, div_self hl, WithTop.coe_one]
  · rw [hv _ ((map_ne_zero _).2 hx), hz x hx, hzp,
      mul_div_mul_right _ _ (right_ne_zero_of_mul (hzp ▸ hl))]
  · obtain ⟨x, hx⟩ := exists_limit_of_norm_sub_le_pow hr0 hr1 s fun n => (hvn _ n).1 (hs n)
    exact ⟨x, fun n => (hvn _ n).2 (hx n)⟩

end GlobalTheory.DvrClosedEmbedding
end

section

open scoped BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj NumberField

namespace GlobalTheory

theorem nabValN_lower_bound_baseChange : ∀ (T : CDVR) (C : Type) [Field C] [CharZero C] (v : AddValuation C (WithTop ℝ)) (ι : T.Fr →+* C) (R : Subring C), (∀ x, x ∈ R ↔ ((0 : ℝ) : WithTop ℝ) ≤ v x) → (∀ x : T.V, ((0 : ℝ) : WithTop ℝ) ≤ v (ι (algebraMap T.V T.Fr x))) → ∀ (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB T.Fr d O) (B' : FB C d O), (∀ i, B'.G.F i = MvPowerSeries.map ι (B.G.F i)) → (∀ a i, B'.A.act a i = MvPowerSeries.map ι (B.A.act a i)) → ∀ (h : PS T.Fr 2 d), MvPowerSeries.constantCoeff h = 0 → ∀ (w0 : O) (m : ℕ) (Ty : Type) [Fintype Ty] (r : Ty → ℕ) (n : ℕ) [Fintype (Letter Ty r n)] (cc : Ty → Ty) (isX : Ty → Prop) (a : Ty → ℕ → ℕ) (cp : Letter Ty r n → Fin n) (u : Letter Ty r n → Fin d → T.Fr) (ν : WithBot (WithTop ℝ)), (∀ P ∈ HaO r n T.Fr (algebraMap T.V T.Fr).range cc isX a, ∀ f : PS T.Fr n d, IsIntPS T f → ν ≤ (WithBot.some (v (ι (nabValN B T.Fr h w0 m f cp u P))) : WithBot (WithTop ℝ))) → ∀ P ∈ HaO r n C R cc isX a, ∀ f : PS C n d, (∀ μ, ((0 : ℝ) : WithTop ℝ) ≤ v (MvPowerSeries.coeff μ f)) → ν ≤ (WithBot.some (v (nabValN B' C (MvPowerSeries.map ι h) w0 m f cp (fun l j => ι (u l j)) P)) : WithBot (WithTop ℝ)) := by
  intro T C _ _ v ι R hR hV d O _ _ B B' hG hA h hh w0 m Ty _ r n _ cc isX a cp u ν hν P hP f hf
  obtain ⟨s, c, Q, hc, hQ, rfl⟩ := GlobalTheory.exists_integral_combination_of_mem_HaO Ty r n T.V T.Fr C ι R
    (fun x => (hR _).2 (hV x)) cc isX a P hP
  obtain ⟨-, -, hadd, hsm⟩ := GlobalTheory.nabValN_bilinear C d O B' (MvPowerSeries.map ι h) w0 m n
    (Letter Ty r n) cp (fun l j => ι (u l j))
  have hsum : ∀ (g : PS C n d) (F : Fin s → MvPolynomial (Letter Ty r n) C) (S : Finset (Fin s)),
      nabValN B' C (MvPowerSeries.map ι h) w0 m g cp (fun l j => ι (u l j)) (∑ j ∈ S, F j)
        = ∑ j ∈ S, nabValN B' C (MvPowerSeries.map ι h) w0 m g cp (fun l j => ι (u l j)) (F j) := by
    intro g F S
    classical
    induction S using Finset.induction_on with
    | empty =>
      have := hsm 0 g 0
      simpa using this
    | insert j S hj ih => rw [Finset.sum_insert hj, Finset.sum_insert hj, hadd, ih]
  obtain ⟨S, hS⟩ := GlobalTheory.T.exists_finset_nabValN_eq_sum_coeff_mul_monomial C d O B' (MvPowerSeries.map ι h) w0 m n
    (Letter Ty r n) cp (fun l j => ι (u l j))
    (∑ j, MvPolynomial.C (c j) * MvPolynomial.map ι (Q j))
  rw [hS f]
  induction ν using WithBot.recBotCoe with
  | bot => exact bot_le
  | coe w =>
    refine WithBot.coe_le_coe.2 ?_
    refine v.map_le_sum fun μ _ => ?_
    rw [v.map_mul, hsum]
    refine le_trans ?_ (le_add_of_nonneg_left (by simpa using hf μ))
    refine v.map_le_sum fun j _ => ?_
    rw [hsm, v.map_mul]
    refine le_trans ?_ (le_add_of_nonneg_left (by simpa using (hR _).1 (hc j)))
    have hmon : (MvPowerSeries.monomial μ (1 : C) : PS C n d)
        = MvPowerSeries.map ι (MvPowerSeries.monomial μ (1 : T.Fr) : PS T.Fr n d) := by
      rw [MvPowerSeries.map_monomial, map_one ι]
    rw [hmon, GlobalTheory.nabValN_map T.Fr C ι d O B B' hG hA h hh w0 m n _ (Letter Ty r n) cp u (Q j)]
    refine WithBot.coe_le_coe.1 (hν (Q j) (hQ j) _ ?_)
    intro ρ
    classical
    rw [MvPowerSeries.coeff_monomial]
    split_ifs
    · exact Subring.one_mem _
    · exact Subring.zero_mem _

end GlobalTheory
end
