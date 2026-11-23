module

public import Development.AbelianVarietyTheory.Definitions.Jets.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle006
public import Development.AbelianVarietyTheory.Definitions.Jets.Bundle003
public import Development.AbelianVarietyTheory.Definitions.Jets.Bundle004
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle150
public import Development.AbelianVarietyTheory.Definitions.Jets.CmLatticeCommutatorPairingPowEqOneOfGoodLift
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle140
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle021
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle014
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle031
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle090
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle105
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle110
public import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle009
public import Formalism.HermitianCurvature.RealInputsClosedAdmissibleSettings
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle312
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle308
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle292
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle368
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle135
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle134
public import Development.AbelianVarietyTheory.Statements.DiscreteSeriesShifts.Bundle001
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ContractionMapsAtRepresentatives
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle158
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle137
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle155
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.UwEllipticFlow
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle153
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle065
public import Formalism.HermitianCurvature.Bundle008
public import Formalism.HermitianCurvature.StatementD
public import Formalism.HermitianCurvature.StatementU
public import Formalism.HermitianCurvature.StatementQ
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CapelliEigenfunctionPowSmulCompPolyFamilyEigenSu
public import Formalism.LocalToGlobal.CharacterGerms.Bundle027
public import Formalism.LocalToGlobal.CharacterGerms.Bundle023
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle159
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
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Development.AbelianVarietyTheory.Definitions.Jets.DepthNumbersThresholdEq
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Jets.SupWOfSup
import Formalism.SharpRestriction.CuspSpanNormBounds.LeadMinorK

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS FB ev Dof)
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)
open GlobalTheory
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.depth_bound_from_characters_pointDatum : Laws → Laws2 → Laws4 → TwistBaseChangeStatement → (∀ (p : ℕ) [Fact p.Prime], ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (F : Type) [Field F] [IsAlgClosed F] [CharZero F] [Algebra (FractionRing V) F] [Algebra V F] [IsScalarTower V (FractionRing V) F] (y : FamGerm.Pt1 E H V F), letI := H.starRing; IsAdicComplete (Ideal.span {(p : TWO.Ov y.v)}) (TWO.Ov y.v) → ¬ IsUnit (p : TWO.Ov y.v) → ∀ a : 𝓞 E, a * star a = (p : 𝓞 E) → (∃ u u' : 𝓞 E, u * a + u' * star a = 1) → ∀ (T : Type) [Fintype T] [DecidableEq T] (rk : T → ℕ) (τ : T → 𝓞 E →+* TWO.Ov y.v) (e : (Σ t, Fin (rk t)) → Fin y.d → TWO.Ov y.v), (∀ (c : 𝓞 E) l, (dAct F y.B c).mulVec (fun i => (e l i : F)) = (τ l.1 c : F) • fun i => (e l i : F)) → (∀ t, τ t a ∈ Ideal.span {(p : TWO.Ov y.v)}) → (∀ t, ∃ lam : Fin (rk t) → Fin y.d → TWO.Ov y.v, ∀ i i', ∑ s, lam i s * e ⟨t, i'⟩ s = if i = i' then 1 else 0) → (∃ ε : T → 𝓞 E, ∀ t t', τ t' (ε t) - (if t = t' then 1 else 0) ∈ Ideal.span {(p : TWO.Ov y.v)}) → ∀ c : TWO.Ov y.v, (p - 1) • y.v (c : F) = y.v (p : F) → ∀ (n : ℕ) (col : ∀ t, Fin (rk t) → Fin n), (∀ t, Function.Injective (col t)) → ∃ yy : (Σ t, Fin (rk t)) × Fin n → TWO.Ov y.v, (∀ b, y.CharAt a p e (fun l => yy (l, b))) ∧ ∀ t (s : Fin (rk t)), y.v (((Matrix.of fun a i : Fin (s.val + 1) => yy (⟨t, Fin.castLE s.isLt a⟩, col t (Fin.castLE s.isLt i))).det : TWO.Ov y.v) : F) ≤ (s.val + 1) • y.v (c : F)) → ∀ (p : ℕ) [Fact p.Prime], ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (F : Type) [Field F] [IsAlgClosed F] [CharZero F] [Algebra (FractionRing V) F] [Algebra V F] [IsScalarTower V (FractionRing V) F] (y : FamGerm.Pt1 E H V F), letI := H.starRing; IsAdicComplete (Ideal.span {(p : TWO.Ov y.v)}) (TWO.Ov y.v) → ¬ IsUnit (p : TWO.Ov y.v) → ∀ (Dw : Datum H) (_I : TateIso Dw F (TFK (R := V) F ⟶ y.P.A.A) (fun a g => g ≫ y.P.oA.act a) (fun n g g' c => WeilIs y.P.A.A y.P.A.L n g g' (unitOn c))), ∀ (r : ℕ) (b : Module.Basis (Fin r) ℤ y.P.D.toPre.X) (Cc M₀ : ℝ), y.Red r b Cc M₀ → ∀ (a : 𝓞 E) (k : ℕ), a * star a = (p : 𝓞 E) → (∃ u u' : 𝓞 E, u * a + u' * star a = 1) → Nat.Coprime p k → ∀ (T : Type) [Fintype T] [DecidableEq T] (rk : T → ℕ) (τ : T → 𝓞 E →+* TWO.Ov y.v) (e : (Σ t, Fin (rk t)) → Fin y.d → TWO.Ov y.v), (∀ (c : 𝓞 E) l, (dAct F y.B c).mulVec (fun i => (e l i : F)) = (τ l.1 c : F) • fun i => (e l i : F)) → ∀ (isV : T → Prop) [DecidablePred isV], (∀ t, isV t → τ t a ∈ Ideal.span {(p : TWO.Ov y.v)}) → (∀ t, ¬ isV t → IsUnit (τ t a)) → (∃ lam : (Σ t, Fin (rk t)) → Fin y.d → TWO.Ov y.v, ∀ l l', ∑ s, lam l s * e l' s = if l = l' then 1 else 0) → (∃ ε : T → 𝓞 E, ∀ t t', τ t' (ε t) - (if t = t' then 1 else 0) ∈ Ideal.span {(p : TWO.Ov y.v)}) → ∀ (n : ℕ) (S : Finset (Fin n)) (col : ∀ t, Fin (rk t) → Fin n) (m : ∀ t, Fin (rk t) → ℕ), (∀ t, Function.Injective (col t)) → (∀ t i, col t i ∈ S ↔ isV t) → ∀ D : ℕ, D = ∑ t, ∑ s : Fin (rk t), m t s * (s.val + 1) → D < p - 1 → 4 * D + 4 ≤ k → (D : ℝ) * M₀ < k → ∀ h : PS F 2 y.d, y.B.IsCanonGauge F h → ∀ ep : ℚ, y.v (p : F) = (ep : ℚ) → ∃ (s : Fin n → Fam y.P.D.toPre F k) (s' t : Fin n → Fam y.P.D.toPre F (k * p)) (f : Fin n → PS F 1 y.d) (gm : ℚ), (∀ b, NuGe y.P.D y.Q F y.v (k) (s b) 0 ∧ PullAl y.P.D F y.P.oD a k p (s b) (s' b) ∧ y.Transl (k * p) (star a) (s' b) (t b) ∧ y.Germ (k * p) (t b) (f b)) ∧ y.v (y.colVal h (k * p) (fun l i => (e l i : F)) (FamGerm.minorsP F col m) f) = (gm : ℚ) ∧ (gm : ℝ) ≤ (D : ℝ) * ep / (p - 1) + S.card * r * Cc / (4 * k) + (D : ℝ) ^ 2 * Cc / k := by
  first | exact @GlobalTheory.DepthFromChars.depth_bound_of_chars | exact GlobalTheory.DepthFromChars.depth_bound_of_chars | (intros; apply GlobalTheory.DepthFromChars.depth_bound_of_chars <;> assumption)
end

section

open scoped BigOperators TensorProduct
open Classical NumberField IsDedekindDomain Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.L2.Pj Formalism.L2.DIV Formalism.BasicNotions GlobalTheory.RowLaw GlobalTheory.RowAt GlobalTheory.GoodDepth
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

theorem _root_.GlobalTheory.T.nonDeg_raw_pairData_and_rankMaximal : (∀ (C : Type) [Field C] [CharZero C] (V : VF C) (O : Type) [CommRing O] [StarRing O] (dd : ℕ) (Y : FBChart C V O dd) (d : ℕ) [NeZero d] (I : Fin 2 → Type) [∀ g, Fintype (I g)] (p : PairData Y d I), NDG Y → NonDeg (Y.raw p) V) ∧ RankMaximalOfNondegenerate := by
  first | exact @GlobalTheory.NonDegPair.nonDegenerate_and_rowConditionTwo_pairsOfPlaces | exact GlobalTheory.NonDegPair.nonDegenerate_and_rowConditionTwo_pairsOfPlaces | (intros; apply GlobalTheory.NonDegPair.nonDegenerate_and_rowConditionTwo_pairsOfPlaces <;> assumption)
end

section

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF

namespace GlobalTheory.HatNF.BoundedFactors

theorem star_prod_ofFn {A : Type} [Ring A] [StarRing A] {r : ℕ} (f g : Fin r → A)
    (h : ∀ l, star (f l) = g l) (hc : ∀ l m, Commute (g l) (g m)) :
    star (List.ofFn f).prod = (List.ofFn g).prod := by
  induction r with
  | zero => simp
  | succ n ih =>
    rw [List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.prod_cons, star_mul, h,
      ih (fun i => f i.succ) (fun i => g i.succ) (fun l => h _) (fun l m => hc _ _)]
    refine (Commute.list_prod_left _ _ ?_).eq
    intro x hx
    obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).1 hx
    exact hc _ _

theorem star_phase {A : Type} [Ring A] [StarRing A] [Algebra ℂ A] {r : ℕ} (L : LevelData A r)
    (hc : ∀ l, star (L.c l) = L.cb l) (hi : ∀ l, star (L.ci l) = L.cbi l) :
    star (L.Drb * L.Dri) = L.Dr * L.Drbi := by
  have h1 : star L.Drb = L.Dr :=
    star_prod_ofFn _ _ (fun l => by rw [← hc l, star_star])
      (fun l m => L.fns_comm _ (by simp) _ (by simp))
  have h2 : star L.Dri = L.Drbi :=
    star_prod_ofFn _ _ hi (fun l m => L.fns_comm _ (by simp) _ (by simp))
  rw [star_mul, h1, h2]
  refine (Commute.list_prod_left _ _ ?_).eq
  intro x hx
  obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).1 hx
  refine Commute.list_prod_right _ _ ?_
  intro y hy
  obtain ⟨j, rfl⟩ := (List.mem_ofFn' _ _).1 hy
  exact L.fns_comm _ (by simp) _ (by simp)

section

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
  {P : M.Par} {Bs : B.RealPlaceData P.k P.r Wp Wq}

theorem hsInner_self_norm (A : Wq →L[ℂ] Wp) : ‖B.hsInner A A‖ = ‖B.hsVec A‖ ^ 2 := by
  unfold B.hsInner
  rw [inner_self_eq_norm_sq_to_K]
  simp

theorem hsInner_norm_le (A C : Wq →L[ℂ] Wp) : ‖B.hsInner A C‖ ≤ ‖B.hsVec A‖ * ‖B.hsVec C‖ := by
  unfold B.hsInner
  rw [mul_comm]
  exact norm_inner_le_norm _ _

theorem ptB_of_star_mul_self (b : RA P Bs) (ha : PtAdj P Bs b) (hb : PtB P Bs (star b * b)) : PtB P Bs b := by
  obtain ⟨C, hC, h⟩ := hb
  refine ⟨Real.sqrt C, Real.sqrt_nonneg _, fun Φ x hx => ?_⟩
  have h1 := ha Φ (b.1 Φ) x hx
  have h2 : nv ((star b).1 (b.1 Φ)) x ≤ C * nv Φ x := h Φ x hx
  have h3 : nv (b.1 Φ) x ^ 2 ≤ nv Φ x * nv ((star b).1 (b.1 Φ)) x := by
    unfold nv
    rw [← hsInner_self_norm, h1]
    exact hsInner_norm_le _ _
  have h0 : 0 ≤ nv Φ x := norm_nonneg _
  have h4 : nv (b.1 Φ) x ^ 2 ≤ (Real.sqrt C * nv Φ x) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hC]
    nlinarith [mul_le_mul_of_nonneg_left h2 h0]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) h0) two_ne_zero).1 h4

theorem ptB_star (b : RA P Bs) (ha : PtAdj P Bs b) (hb : PtB P Bs b) : PtB P Bs (star b) := by
  obtain ⟨C, hC, h⟩ := hb
  refine ⟨C, hC, fun Ψ x hx => ?_⟩
  have h1 := ha ((star b).1 Ψ) Ψ x hx
  have h2 := h ((star b).1 Ψ) x hx
  have h3 : nv ((star b).1 Ψ) x ^ 2 ≤ nv (b.1 ((star b).1 Ψ)) x * nv Ψ x := by
    unfold nv
    rw [← hsInner_self_norm, ← h1]
    exact hsInner_norm_le _ _
  have h0 : 0 ≤ nv Ψ x := norm_nonneg _
  have h0' : 0 ≤ nv ((star b).1 Ψ) x := norm_nonneg _
  rcases h0'.eq_or_lt with he | hp
  · rw [← he]; exact mul_nonneg hC h0
  · have h4 : nv ((star b).1 Ψ) x * nv ((star b).1 Ψ) x ≤ nv ((star b).1 Ψ) x * (C * nv Ψ x) := by
      nlinarith [mul_le_mul_of_nonneg_right h2 h0]
    exact le_of_mul_le_mul_left h4 hp

end

theorem ptB_of_mem_bmon : ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (μ : Measure (Mt P.k P.r)) (L : LevelData (RA P Bs) P.r) (st : Start (RA P Bs)) (l0 : ℕ) (d : Q.NFData P (RA P Bs)), P5.IsData P Bs.z Bs.z' Bs.π Bs.π' X μ L st l0 → IsNF X d → ∀ b ∈ bmon d, PtB P Bs b := by
  intro Wp Wq _ _ _ _ _ _ P Bs X μ L st l0 d hD hN
  obtain ⟨⟨-, -, hRel, -, hc, hi, -⟩, -⟩ := GlobalTheory.T.normalForm_actualOperators_algebraicHypotheses Wp Wq P Bs X μ L st l0 d hD hN
  have hκ := GlobalTheory.T.radialPairConstants_pointwiseAdjoint_bounded Wp Wq P Bs X μ L st l0 d hD hN
  obtain ⟨⟨h1, hmul⟩, hζi, hζbi, hD1, hD2, hD3, hD4, -⟩ := GlobalTheory.T.pointwise_bounded_radial_ops_closure_and_functions Wp Wq P Bs X μ L st l0 d hD hN
  have hS := GlobalTheory.T.radialRaisingOperators_pointwiseAdjointPair Wp Wq P Bs X μ L st l0 d hD hN
  have hSb : ∀ l ∈ Finset.Icc 1 (P.k - 1), PtB P Bs (d.SS l) := fun l hl =>
    ptB_of_star_mul_self _ (hS l hl) (by rw [hRel.2.2.2.2.2 l hl]; exact (hκ _).2)
  have hSs : ∀ l ∈ Finset.Icc 1 (P.k - 1), PtB P Bs (star (d.SS l)) := fun l hl =>
    ptB_star _ (hS l hl) (hSb l hl)
  intro b hb
  induction hb using Submonoid.closure_induction with
  | one => exact h1
  | mul x y _ _ hx hy => exact hmul _ _ hx hy
  | mem x hx =>
    rcases hx with ((hx | ⟨f, rfl⟩) | ⟨l, hl, rfl⟩) | ⟨l, hl, rfl⟩
    · rcases hx with rfl | rfl | rfl | rfl
      exacts [hζi, hζbi, hD1, hD2]
    · exact (hκ f).2
    · exact hmul _ _ hD3 (hSb l (by simpa using hl))
    · show PtB P Bs (star (d.L.Drb * d.L.Dri * d.SS l))
      rw [star_mul, star_phase d.L hc hi]
      exact hmul _ _ (hSs l (by simpa using hl)) hD4

end GlobalTheory.HatNF.BoundedFactors
end

section

open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology

namespace GlobalTheory.MomOne.GenusOne

variable {q : ℕ} [Fact q.Prime]

theorem norm_root_eq (M : Mdl q) (h : M.Ok) (δ : ℂ) (hδ : δ ^ 12 = M.L.g₂ ^ 3 - 27 * M.L.g₃ ^ 2) :
    ‖M.ι δ‖ = ‖M.ι M.c‖ ∧ ‖M.ι M.c‖ ≠ 0 := by
  obtain ⟨hc, -, -, -, -, -, hΔ, h4, h6⟩ := h
  have hιc : M.ι M.c ≠ 0 := (map_ne_zero M.ι).mpr hc
  refine ⟨?_, norm_ne_zero_iff.mpr hιc⟩

  rw [map_div₀, map_pow, eq_div_iff (pow_ne_zero 4 hιc)] at h4
  rw [map_div₀, map_pow, eq_div_iff (pow_ne_zero 6 hιc)] at h6
  have key : M.ι δ ^ 12 = M.ι M.c ^ 12 * M.W.Δ := by
    have e : M.ι δ ^ 12 = M.ι M.L.g₂ ^ 3 - 27 * M.ι M.L.g₃ ^ 2 := by
      rw [← map_pow, hδ]; simp only [map_sub, map_mul, map_pow, map_ofNat]
    rw [e, ← h4, ← h6]
    linear_combination (-(M.ι M.c ^ 12) / 1728) * M.W.c_relation
  have hn := congrArg norm key
  rw [norm_mul, norm_pow, norm_pow, hΔ, mul_one] at hn
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) (by norm_num)).mp hn

theorem norm_period (M : Mdl q) (ω : ℂ_[q]) (h : M.MChart ω) : ‖ω‖ * ‖M.ι M.c‖ = 1 := by
  obtain ⟨hok, h0, -, h1⟩ := h
  obtain ⟨-, -, -, -, -, -, hdu, -, hsmall⟩ := uw_elliptic_flow q M hok
  obtain ⟨han, -⟩ := hsmall 0 (Or.inl (zero_mem _))
  obtain ⟨-, -, -, hcc, hder, -, -⟩ := TaylorRead.hat_laws q M.ι (C ω * logS) h0

  have hd0 : ∀ f : ℂ_[q]⟦X⟧, constantCoeff (PowerSeries.derivative f) = coeff 1 f := by
    intro f
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_derivative]
    simp
  have hℓ : coeff 1 (C ω * logS : ℂ_[q]⟦X⟧) = ω := by
    simp [logS, coeff_C_mul, coeff_mk]
  have e : coeff 1 (hat M.ι (C ω * logS) M.u) = ω * M.ι M.c := by
    rw [← hd0, hder M.u han, map_mul, hd0, hℓ, hcc, hdu]
  rw [e, norm_mul] at h1
  exact h1

theorem thetaLaws_unit_period : ∀ (d q : ℕ) [Fact q.Prime] (δ : ℂ), d.Prime → d % 16 = 7 → Split d q →
    δ ^ 12 = discr d → ∃ θ : ℂ → ℂ, IsTh d θ ∧ δ ≠ 0 ∧
      ∀ ι : ℂ ≃+* ℂ_[q], ∃ Ω : ℂ_[q], ‖Ω‖ = 1 ∧ ThetaLaws ι d (Ω / ι δ) θ := by
  intro d q _ δ hd h16 hsp hδ
  obtain ⟨⟨L, hL, hLd⟩, θ, hθ⟩ := GlobalTheory.T.exists_imagQuadOrder_pair_and_evenTheta d hd h16
  have hδ0 : δ ≠ 0 := by
    rintro rfl
    exact (Basic.discr_eq hL).2 (by rw [← hδ]; norm_num)
  refine ⟨θ, hθ, hδ0, fun ι => ?_⟩
  obtain ⟨M, hMι, hML, hok, a1, a2, a3, a4, a6⟩ := GlobalTheory.T.exists_goodReduction_algebraic_weierstrass_model d q ι L hd h16 hL
  subst hMι
  have hL' : IsOK d M.L := by rw [hML]; exact hL
  obtain ⟨ω₀, hω₀⟩ := GlobalTheory.T.exists_multiplicativeChart_at_splitPrime d q M hd h16 hsp hL' hok a1 a2 a3 a4 a6
  obtain ⟨a, -, hω, hgood⟩ := GlobalTheory.T.exists_normalised_multiplicativeChart d q M ω₀ hd h16 hsp hL' hω₀
  have hδM : δ ^ 12 = M.L.g₂ ^ 3 - 27 * M.L.g₃ ^ 2 := by rw [hML, hLd]; exact hδ
  obtain ⟨hn, -⟩ := norm_root_eq M hok δ hδM
  have hp := norm_period M (ω₀ * zc a) hω
  have hιδ : M.ι δ ≠ 0 := (map_ne_zero M.ι).mpr hδ0
  refine ⟨ω₀ * zc a * M.ι δ, by rw [norm_mul, hn]; exact hp, ?_⟩
  rw [mul_div_cancel_right₀ _ hιδ]
  have hU0 : U1 d 0 θ = θ := (GlobalTheory.T.cmLattice_heisenberg_relations_one_variable d hd.pos).2.1 θ
  have h0 : PrimeTo d q 0 := ⟨1, one_pos, Nat.coprime_one_left q, 0, 0, by simp⟩
  have hB := GlobalTheory.T.cm_even_theta_series_chart_coeff_integral d q M (ω₀ * zc a) θ hd h16 hsp hL' hω hθ
  refine ⟨fun t ht => ?_, GlobalTheory.T.weilOperator_theta_translate_shift_prime_to_q d q M (ω₀ * zc a) θ hd h16 hsp hL' hω hθ hgood,
    GlobalTheory.T.norm_translate_powerComb_le_coprimeTranslation d q M (ω₀ * zc a) θ hd h16 hsp hL' hω hθ⟩

  have := GlobalTheory.T.norm_translate_powerComb_le_coprimeTranslation d q M (ω₀ * zc a) θ hd h16 hsp hL' hω hθ 1 1 (fun _ => 1) (fun _ => 0) t 1
    (fun _ => h0) ht (by simpa [hU0] using hB)
  simpa [hU0] using this

end GlobalTheory.MomOne.GenusOne
end

section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

theorem _root_.GlobalTheory.T.exists_family_functionals : Hyps → ∀ (P : M.Par) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (p : KB.Pl P Wp Wq) (lam : Fin (2 * P.r + P.k + 1) → ℝ) (b bv ga h : ℝ) (q0 : ℕ) (R : (Fin (2 * P.r + P.k + 1) → ℤ) → Rep P.k P.r), Num P.k P.r lam P.u b bv ga h q0 → IsFam lam q0 R → ∃ (l : ∀ ν, (R ν).H → Wp) (l' : ∀ ν, (R ν).H → Wq) (dg : (Fin (2 * P.r + P.k + 1) → ℤ) → ℝ), (haveI := FiniteDimensional.complete ℂ Wp; SideFam p.T.base.z p.T.base.π p.T.base.μW p.T.base.μN p.T.base.μG q0 R l dg) ∧ (haveI := FiniteDimensional.complete ℂ Wq; SideFam p.T.base.z' p.T.base.π' p.T.base.μW' p.T.base.μN p.T.base.μG q0 R l' dg) := by
  first | exact @GlobalTheory.exists_sideFam_both_sides | exact GlobalTheory.exists_sideFam_both_sides | (intros; apply GlobalTheory.exists_sideFam_both_sides <;> assumption)
end

section

open BpJoin Formalism.FourierDecayAlt Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.BasicNotions Formalism.QuantumDeterminants GlobalTheory.ThA

namespace GlobalTheory.PlaceOfLocalBesselType

theorem isType_of_isHCTypeW (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (u : Fin k → ℝ) (U : ℕ → ℝ) (Wp : Type)
    [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] (π : B.Mat k r → (Wp →L[ℂ] Wp))
    (hz : inWb k r z) (hT : 0 < Tz k r z) (hπ : Formalism.MainNotions.S.IsHCTypeW k r z u π)
    (hU : ∀ i : Fin k, U (i.val + 1) = u i) : Q.IsType k r z π U := by
  have hπ' : PI.UpqRep.IsHCTypeW k r z u π := hπ
  obtain ⟨u', h1, h2, h3, h4, h5, -⟩ := GlobalTheory.CapelliOfHC.exists_isType k r Wp z π u hz hT hπ'
  exact ⟨h1, h2, h3, h4, h5, GlobalTheory.ThA.capParam_of_isHCTypeW k r z u U Wp π hz hT hπ hU⟩

noncomputable def ext {k : ℕ} (u : Fin k → ℝ) (i : ℕ) : ℝ := if h : i - 1 < k then u ⟨i - 1, h⟩ else 0

theorem ext_succ {k : ℕ} (u : Fin k → ℝ) (i : Fin k) : ext u (i.val + 1) = u i := by
  simp [ext]

theorem add_one_le {a b c l : ℝ} (ha : ∃ m : ℤ, a = m + c) (hb : ∃ m : ℤ, b = m + c) (h1 : a < l) (h2 : l < b) :
    a + 1 ≤ b := by
  obtain ⟨m, rfl⟩ := ha
  obtain ⟨n, rfl⟩ := hb
  have h : (m : ℝ) < n := by linarith
  have h' : m + 1 ≤ n := by exact_mod_cast h
  have h'' : (m : ℝ) + 1 ≤ n := by exact_mod_cast h'
  linarith

end GlobalTheory.PlaceOfLocalBesselType

namespace GlobalTheory

open PlaceOfLocalBesselType

theorem exists_place_of_locBessel : ∀ (k r : ℕ) (L : LocBessel k r) (μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (lam0 : Fin (2 * r + k + 1) → ℝ) (hk : k ≤ 2 * r + k + 1), 2 ≤ k → IsSection k r L.z L.z' μsec → InterlaceS hk L.u lam0 → InterlaceS hk L.u' lam0 → ∃ (U U' : ℕ → ℝ) (p : KB.Pl ⟨k, r, Tz k r L.z, Tz k r L.z', U, U'⟩ L.Wp L.Wq), (∀ i : Fin k, U (i.val + 1) = L.u i ∧ U' (i.val + 1) = L.u' i) ∧ IsStdOf L μsec p.T.base := by
  intro k r L μsec lam0 hk h2 hsec hI hI'
  have hk1 : 1 ≤ k := by omega
  obtain ⟨Bs, hBs⟩ := GlobalTheory.T.exists_normalised_localBesselDatum k r L μsec hk1 hsec
  obtain ⟨ν', m₀, hF⟩ := Formalism.FourierDecayAlt.P.HaarMassHermitianCurvature.frame_of Bs
  have hT := isType_of_isHCTypeW k r L.z L.u (ext L.u) L.Wp L.π L.hz.1 L.hz.2 L.hπ (ext_succ L.u)
  have hT' := isType_of_isHCTypeW k r L.z' L.u' (ext L.u') L.Wq L.π' L.hz'.1 L.hz'.2 L.hπ' (ext_succ L.u')
  have hZ := GlobalTheory.capelliParam_mem_int_add_half k r L.Wp L.z L.π _ L.hz.1 L.hz.2 hT
  have hZ' := GlobalTheory.capelliParam_mem_int_add_half k r L.Wq L.z' L.π' _ L.hz'.1 L.hz'.2 hT'
  have h1 : 1 ∈ Finset.Icc 1 k := Finset.mem_Icc.2 ⟨le_rfl, hk1⟩
  have hOK : (⟨k, r, Tz k r L.z, Tz k r L.z', ext L.u, ext L.u'⟩ : M.Par).OK := by
    refine ⟨hk1, L.hz.2, L.hz'.2, ?_, ?_, ?_⟩
    · intro i hi
      obtain ⟨m, hm⟩ := hZ i hi
      obtain ⟨n, hn⟩ := hZ 1 h1
      exact ⟨m - n, by dsimp only; rw [hm, hn]; push_cast; ring⟩
    · intro i hi
      obtain ⟨m, hm⟩ := hZ' i hi
      obtain ⟨n, hn⟩ := hZ 1 h1
      exact ⟨m - n, by dsimp only; rw [hm, hn]; push_cast; ring⟩
    · intro i hi
      dsimp only at hi
      rw [Finset.mem_Icc] at hi
      obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
      have hj : j + 1 < k := by omega
      have m1 : j + 1 ∈ Finset.Icc 1 k := Finset.mem_Icc.2 ⟨by omega, by omega⟩
      have m2 : j + 1 + 1 ∈ Finset.Icc 1 k := Finset.mem_Icc.2 ⟨by omega, by omega⟩
      obtain ⟨a1, a2⟩ := hI.1 j hj
      obtain ⟨b1, b2⟩ := hI'.1 j hj
      rw [← ext_succ L.u] at a1 a2
      rw [← ext_succ L.u'] at b1 b2
      dsimp only at a1 a2 b1 b2
      have c1 := add_one_le (hZ _ m2) (hZ _ m1) a2 a1
      have c2 := add_one_le (hZ _ m2) (hZ' _ m1) a2 b1
      have c3 := add_one_le (hZ' _ m2) (hZ _ m1) b2 a1
      have c4 := add_one_le (hZ' _ m2) (hZ' _ m1) b2 b1
      simp only [M.Par.lo, M.Par.hi]
      rcases max_choice (ext L.u (j + 1 + 1)) (ext L.u' (j + 1 + 1)) with e | e <;>
        rcases min_choice (ext L.u (j + 1)) (ext L.u' (j + 1)) with e' | e' <;> rw [e, e'] <;> linarith
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8⟩ := hBs
  obtain ⟨Cb, hCb⟩ := GlobalTheory.ThA.plExists
  obtain ⟨p, -, hp, -⟩ := hCb L.Wp L.Wq ⟨k, r, Tz k r L.z, Tz k r L.z', ext L.u, ext L.u'⟩ Bs ν' m₀ 1 le_rfl hk1 h2
    (by rw [e5]; exact L.hμW.2) (by rw [e6]; exact L.hμW'.2) e7 hF
    (by rw [e1, e2, e3, e4]; exact ⟨hOK, L.hz.1, L.hz'.1, rfl, rfl, hT, hT'⟩)
  refine ⟨ext L.u, ext L.u', p, fun i => ⟨ext_succ _ i, ext_succ _ i⟩, ?_⟩
  rw [hp]
  exact ⟨e1, e2, e3, e4, e5, e6, e7, e8⟩

end GlobalTheory
end

section

open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P.CutBP2

namespace GlobalTheory.WigSh

theorem par_gap_right (P : M.Par) (hP : P.OK) :
    ∀ i ∈ Finset.Icc 1 (P.k - 1), ∃ N : ℕ, P.u' i - P.u' (i + 1) = (N : ℝ) + 1 := by
  intro i hi
  have hi' := Finset.mem_Icc.mp hi
  obtain ⟨a, ha⟩ := hP.int_u' i (Finset.mem_Icc.mpr ⟨hi'.1, by omega⟩)
  obtain ⟨c, hc⟩ := hP.int_u' (i + 1) (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
  have hg := hP.gap i hi
  unfold M.Par.lo M.Par.hi at hg
  have h1 := le_max_right (P.u (i + 1)) (P.u' (i + 1))
  have h2 := min_le_right (P.u i) (P.u' i)
  have h3 : ((1 : ℤ) : ℝ) ≤ ((a - c : ℤ) : ℝ) := by push_cast; linarith
  have h4 : (1 : ℤ) ≤ a - c := by exact_mod_cast h3
  obtain ⟨N, hN⟩ : ∃ N : ℕ, a - c - 1 = (N : ℤ) := ⟨(a - c - 1).toNat, by omega⟩
  refine ⟨N, ?_⟩
  have h5 : ((a - c - 1 : ℤ) : ℝ) = ((N : ℤ) : ℝ) := by rw [hN]
  push_cast at h5
  linarith

theorem amapsShExists : GlobalTheory.WigSh.AmapsShExists := by
  obtain ⟨c₃, hc⟩ := GlobalTheory.WigSh.contraction_maps_at_representatives
  refine ⟨c₃, ?_⟩
  intro P Wp Wq Wqp Wqm _ _ _ _ _ _ _ _ _ _ _ _ up up' um um' p pp pm l n₀ b hpz hpz' hmz hmz' hpπ hmπ
    hpν hpm hmν hmm hl hlk hn hb hnb h1b hup hum
  have h0 := p.hT 0 (Nat.zero_le _)
  have h1 := pp.hT 0 (Nat.zero_le _)
  have h2 := pm.hT 0 (Nat.zero_le _)
  have hp : Q.IsType P.k P.r p.T.base.z' pp.T.base.π' up' := hpz' ▸ pp.hP.2.2.2.2.2.2
  have hm : Q.IsType P.k P.r p.T.base.z' pm.T.base.π' um' := hmz' ▸ pm.hP.2.2.2.2.2.2
  have hμp : pp.T.base.μSS = p.T.base.μSS :=
    GlobalTheory.unitaryMeasureDatum_productMeasure_eq_of_same_vectors Wp Wq Wqp P.k P.r p.T.base pp.T.base hpz hpz' h0.1 h0.2.1 h1.1 h1.2.1
      (h1.2.2.trans h0.2.2.symm)
  have hμm : pm.T.base.μSS = p.T.base.μSS :=
    GlobalTheory.unitaryMeasureDatum_productMeasure_eq_of_same_vectors Wp Wq Wqm P.k P.r p.T.base pm.T.base hmz hmz' h0.1 h0.2.1 h2.1 h2.2.1
      (h2.2.2.trans h0.2.2.symm)
  obtain ⟨Ap', Am', hAp, hAm, hlow⟩ := GlobalTheory.WigSh.exists_wigMap_pair_of_isType Wq Wqp Wqm P.k P.r p.T.base.z'
    p.T.base.π' pp.T.base.π' pm.T.base.π' P.u' up' um' l n₀ b p.T.base.z'_mem p.T.base.T'_pos
    p.hP.2.2.2.2.2.2 (par_gap_right P p.hP.1) hl hlk hn hb hnb h1b hp hm hup hum
  obtain ⟨Ap, Am, ApPt, AmPt, hPp, hPm, hrep, -, hfac, he, hbp, hbm⟩ :=
    hc Wp Wq Wqp Wqm P.k P.r p.T.base pp.T.base pm.T.base p.ν' p.m₀ n₀ b Ap' Am' hpz hpz' hpπ hμp hmz hmz' hmπ hμm
      p.hF hAp hAm hlow
  refine ⟨Ap, Am, ApPt, AmPt, hPp, hPm, hrep, ?_⟩
  intro A₀ f hA₀ hf
  obtain ⟨hfp, hfm⟩ := hfac A₀ f hA₀ hf
  refine ⟨?_, ?_, he, hbp, hbm⟩
  · intro γ hγ hG
    have h := hfp γ hγ hG
    unfold KB.Pl.V
    rw [hpν, hpm]
    exact h
  · intro γ hγ hG
    have h := hfm γ hγ hG
    unfold KB.Pl.V
    rw [hmν, hmm]
    exact h

end GlobalTheory.WigSh
end

section

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Filter Topology MeasureTheory

theorem _root_.GlobalTheory.T.topDensity_cutoff_eventually_eq_smoothCoefficient : ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (Cb : ℝ) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (χ : ℝ → ℝ) (w : List C.Letter), KB.InDDplus2 P p.l0 p.T.base Cb p.Θ → C6.IsCut0 χ → B.CkOn ⊤ (B.GV P.k P.r) f → KB.CutWord P p.l0 w → ∀ᵐ c : Fin (P.r + 1) → ℂ, ∀ᶠ ε in 𝓝[>] (0 : ℝ), TBB.Ew p (fun _ => 1) (D.cutF p.T.base χ f ε) (P.r + 1) w (TBB.bigPt P.r c) = TBB.Ew p (fun _ => 1) f (P.r + 1) w (TBB.bigPt P.r c) := by
  first | exact @GlobalTheory.TopVec.Ew_cutF_eventually_eq | exact GlobalTheory.TopVec.Ew_cutF_eventually_eq | (intros; apply GlobalTheory.TopVec.Ew_cutF_eventually_eq <;> assumption)
end

section

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Filter Topology MeasureTheory

theorem _root_.GlobalTheory.T.cutoff_compact_approximants_converge_decay_class : ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (Bs : B.RealPlaceData k r Wp Wq) (χ : ℝ → ℝ) (f : B.Mat k r → (Wq →L[ℂ] Wp)) (A₀ ε A : ℝ) (mm : ℕ), C6.IsCut0 χ → 0 < ε → B.CkOn ⊤ (B.GV k r) f → (∀ m : ℕ, B.InCC A₀ m f) → A + 1 + 2 * ((r : ℝ) + 1) * (mm : ℝ) ≤ A₀ → ∃ K : ℝ, 0 ≤ K ∧ B.CCle A mm (D.cutF Bs χ f ε) K ∧ ∀ n : ℕ, B.CCle A mm ((fun g : B.Mat k r => ((Real.smoothTransition ((4 - ∑ i, ∑ j, Complex.normSq ((((n : ℝ) + 1)⁻¹ • g) i j)) / 3) : ℝ) : ℂ) • D.cutF Bs χ f ε g)) K ∧ B.CCle A mm ((fun g : B.Mat k r => ((Real.smoothTransition ((4 - ∑ i, ∑ j, Complex.normSq ((((n : ℝ) + 1)⁻¹ • g) i j)) / 3) : ℝ) : ℂ) • D.cutF Bs χ f ε g) - (D.cutF Bs χ f ε)) (K / ((n : ℝ) + 1)) := by
  first | exact @GlobalTheory.cutF_approximants_ccle | exact GlobalTheory.cutF_approximants_ccle | (intros; apply GlobalTheory.cutF_approximants_ccle <;> assumption)
end

section

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Finset

theorem _root_.GlobalTheory.T.capelliEigenfunction_pow_smul_comp_polyFamily_eigenSum : ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (Wq' : Type) [NormedAddCommGroup Wq'] [InnerProductSpace ℂ Wq'] [FiniteDimensional ℂ Wq'] (z z' : Fin (2 * r + k + 1) → ℂ) (lam : Fin (2 * r + k + 1) → ℝ) (A₀ : ℝ) (p₀ dA : ℕ) (f : B.Mat k r → (Wq →L[ℂ] Wp)) (Aop : B.Mat k r → (Wq' →L[ℂ] Wq)), (∀ s t, s ≠ t → 2 * (((2 * r + 2) * p₀ + dA : ℕ) : ℝ) < |lam s - lam t|) → (B.CkOn ⊤ (B.GV k r) (f) ∧ ∀ m : ℕ, B.InCC (A₀) m (f)) → (∀ Y : ℝ, ∀ g ∈ B.GV k r, Q.CV k r (Y : ℂ) (f) g = ((∏ s, (Y + lam s) : ℝ) : ℂ) • (f) g) → (∃ (n₁ : ℕ) (c : Fin n₁ → B.Mat k r → ℂ) (L : Fin n₁ → (Wq' →L[ℂ] Wq)), (∀ i, U.IsPolyDeg dA (c i)) ∧ ∀ g, Aop g = ∑ i, c i g • L i) → (∃ (N₀ : ℕ) (Fi : Fin N₀ → B.Mat k r → (Wq' →L[ℂ] Wp)) (ν : Fin N₀ → Fin (2 * r + k + 1) → ℤ), (∀ i s, |ν i s| ≤ (((2 * r + 2) * p₀ + dA : ℕ) : ℤ)) ∧ (∀ i, (B.CkOn ⊤ (B.GV k r) (Fi i) ∧ ∀ m : ℕ, B.InCC (A₀ - (((2 * r + 2) * p₀ + dA : ℕ) : ℝ)) m (Fi i))) ∧ (∀ i, (∀ Y : ℝ, ∀ g ∈ B.GV k r, Q.CV k r (Y : ℂ) (Fi i) g = ((∏ s, (Y + lam s + (ν i s : ℝ)) : ℝ) : ℂ) • (Fi i) g)) ∧ ∀ g ∈ B.GV k r, (fun g => ((Gf k r z z' g ^ p₀ : ℝ) : ℂ) • (f g).comp (Aop g)) g = ∑ i, Fi i g) := by
  first | exact @GlobalTheory.gfPow_smul_comp_polyOp_eigenSum | exact GlobalTheory.gfPow_smul_comp_polyOp_eigenSum | (intros; apply GlobalTheory.gfPow_smul_comp_polyOp_eigenSum <;> assumption)
end

section

open scoped BigOperators TensorProduct
open Classical NumberField IsDedekindDomain Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.L2.Pj Formalism.L2.DIV Formalism.BasicNotions GlobalTheory.RowLaw GlobalTheory.RowAt GlobalTheory.GoodDepth
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

theorem _root_.GlobalTheory.T.rankMaximal_rawSelf_of_ndg : ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (O : Type) [CommRing O] [StarRing O] (dd : ℕ) (Y : FBChart C V O dd) (d : ℕ) [NeZero d] (I0 : Type) [Fintype I0] (p : SelfData Y d I0), NDG Y → ∀ Hc : ∀ g, (Y.rawSelf p).CartHyp V g, RawChart.RankMaximalCondition Hc := by
  first | exact @GlobalTheory.RowAtSelf.rowCondition_two_selfConjugate_of_nonDegenerate | exact GlobalTheory.RowAtSelf.rowCondition_two_selfConjugate_of_nonDegenerate | (intros; apply GlobalTheory.RowAtSelf.rowCondition_two_selfConjugate_of_nonDegenerate <;> assumption)
end
