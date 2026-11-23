module

public import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.HasTeich
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.AdjointEndPairMemGaugedCurveLogarithms
public import Formalism.LocalToGlobal.CharacterGerms.RowTieFB
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.EqZeroOfGe
public import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.IsEigBasisIff
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle041
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle019
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle017
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle036
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.NilpotentCoordinates
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle034
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle039
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle042
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle046
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Limits.Shapes.Connected
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
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.Linter.HaveILetI
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.DimSplitPf
public import Mathlib.CategoryTheory.MorphismProperty.Descent

@[expose] public section

section

open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

theorem _root_.GlobalTheory.T.adjointEndPair_mem_gaugedCurveLogarithms : ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) [NeZero d] (I : Fin 2 → Type) [∀ g, Fintype (I g)] (κ : Type) [Fintype κ] (X : RawChart C d I κ), RLaw X V → ∀ g (M M' : Matrix κ κ C) (s : JJ I g → C), IsEnd X V M M' → (∀ q, V.Ge 0 (s q)) → (∀ q, M'.mulVec (X.u (1 - g) q) = s q • X.u (1 - g) q) → ∀ a ∈ Cv X V g, ((fun i => ∑ j, M i j • a.1 j, fun q => s q • a.2 q) : ((κ → PowerSeries C) × (JJ I g → PowerSeries C))) ∈ Cv X V g := by
  first | exact @GlobalTheory.RowLaw.CvEnd.end_mem_Cv | exact GlobalTheory.RowLaw.CvEnd.end_mem_Cv | (intros; apply GlobalTheory.RowLaw.CvEnd.end_mem_Cv <;> assumption)
end

section

open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

theorem _root_.GlobalTheory.T.isGaugeAdjointIntegralEndPair_add : ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) (I : Fin 2 → Type) (κ : Type) [Fintype κ] (X : RawChart C d I κ), RLaw X V → ∀ M M' N N' : Matrix κ κ C, IsEnd X V M M' → IsEnd X V N N' → IsEnd X V (M + N) (M' + N') := by
  first | exact @GlobalTheory.RowLaw.EndSum.isEnd_add | exact GlobalTheory.RowLaw.EndSum.isEnd_add | (intros; apply GlobalTheory.RowLaw.EndSum.isEnd_add <;> assumption)
end

section

open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

theorem _root_.GlobalTheory.T.exists_integralEnd_of_ladic_action_limit : ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (O : Type) [CommRing O] [StarRing O] (dd : ℕ) (Y : FBChart C V O dd) (d : ℕ) (I : Fin 2 → Type) (X : RawChart C d I (Fin dd)), (X.lg = fun i => un1 (Y.lg i)) → (X.ex = fun i => un1 (Y.ex i)) → X.h = Y.h → ∀ a : ℕ → O, (∀ n, ∃ y, a (n + 1) - a n = (V.l : O) ^ n * y) → ∃ M M' : Matrix (Fin dd) (Fin dd) C, IsEnd X V M M' ∧ IsEnd X V M' M ∧ (∀ (N : ℕ) (v : Fin dd → C) i, ∃ n0, ∀ n ≥ n0, V.Ge N (M.mulVec v i - linAct (Y.B.A.act (a n)) v i)) ∧ (∀ (N : ℕ) (v : Fin dd → C) i, ∃ n0, ∀ n ≥ n0, V.Ge N (M'.mulVec v i - linAct (Y.B.A.act (star (a n))) v i)) := by
  first | exact @GlobalTheory.ActionLimit.exists_isEnd_of_limit_raw | exact GlobalTheory.ActionLimit.exists_isEnd_of_limit_raw | (intros; apply GlobalTheory.ActionLimit.exists_isEnd_of_limit_raw <;> assumption)
end

section

open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace GlobalTheory.TeichPair

theorem hasTeich : ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (O : Type) [CommRing O] [StarRing O] (dd : ℕ) (Y : FBChart C V O dd) (d : ℕ) [NeZero d] (I : Fin 2 → Type) [∀ g, Fintype (I g)] (p : PairData Y d I), ∀ g, HasTeich (Y.raw p) V g := by
  intro C _ _ V O _ _ dd Y d _ I _ p g
  obtain ⟨s, N, ζ, hs, hN, h1, h2, h3, hζ⟩ := exists_seq V Y.cpl (p.em g) (p.em_int g) (p.em_frob g)
    (fun a a' h => p.em_sep (g, a) (g, a') fun h' => h (congrArg Prod.snd h')) (p.em_unr g)
  obtain ⟨M, M', hM, -, hl, hl'⟩ := GlobalTheory.T.exists_adjointIntegralEnd_of_ladicLimit C V O dd Y d I p s hs
  have key : ∀ (a : ZMod d) (z w : C), V.Ge 0 w →
      (∀ N : ℕ, ∃ n0, ∀ n ≥ n0, V.Ge N (z - p.em g a (s n) * w)) → z = ζ a * w := fun a z w hw h => by
    rw [← sub_eq_zero]
    refine eq_zero_of_ge (V := V) fun n => ?_
    obtain ⟨n0, hn⟩ := h n
    have e1 := hn (max n0 n) (le_max_left _ _)
    have e2 := (hw.mul_int (hζ a (max n0 n))).mono (w' := n) (by exact_mod_cast le_max_right _ _)
    have := e1.sub e2
    convert this using 1
    ring
  have hconj : ∀ a x, p.em (1 - g) a (star x) = p.em g a x := fun a x => by
    fin_cases g
    · show p.em 1 a (star x) = p.em 0 a x
      rw [p.em_conj, star_star]
    · show p.em 0 a (star x) = p.em 1 a x
      rw [p.em_conj]
  refine ⟨N, ζ, M, M', hN, h1, h2, h3, hM, fun c => funext fun i => ?_, fun q => funext fun i => ?_⟩
  · refine key _ _ _ (p.u_int g c i) fun n => ?_
    have := hl n (p.u g c) i
    simp only [p.u_eig] at this
    exact this
  · refine key _ _ _ (p.u_int (1 - g) q i) fun n => ?_
    have := hl' n (p.u (1 - g) q) i
    simp only [p.u_eig, hconj] at this
    exact this

end GlobalTheory.TeichPair
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ChF

private lemma nv_eq_nEval {R S : Type} [CommRing R] [CommRing S] [Algebra R S] {n d : ℕ} (f : PS R n d)
    (a : Fin n → Fin d → S) :
    nv (algebraMap R S) f a = nEval f (fun q : Fin n × Fin d => a q.1 q.2) := by
  unfold nv nEval tEval
  rfl

private lemma sep_nil {R : Type} [CommRing R] {n d : ℕ} (f f' : PS R n d)
    (h : ∀ (S : Type) [CommRing S] [Algebra R S] (a : Fin n → Fin d → S), (∀ i j, IsNilpotent (a i j)) →
      nv (algebraMap R S) f a = nv (algebraMap R S) f' a) : f = f' :=
  GlobalTheory.T.powerSeries_eq_of_evalAtNilpotentPoints_eq R ⊥ inferInstance n d f f' (fun S _ _ _ _ _ a ha => h S a ha)

private lemma nv_ev {R S : Type} [CommRing R] [CommRing S] (s : R →+* S) {n m d : ℕ}
    (a : Fin n → Fin d → S) (ha : ∀ i j, IsNilpotent (a i j)) (b : Fin m → Fin d → PS R n d) (f : PS R m d)
    (hb : ∀ i j, MvPowerSeries.constantCoeff (b i j) = 0) :
    nv s (ev b f) a = nv s f (fun i j => nv s (b i j) a) :=
  (nv_calculus R S s n d a ha).2.2.1 m d b f hb

private lemma nv_X {R S : Type} [CommRing R] [CommRing S] (s : R →+* S) {n d : ℕ}
    (a : Fin n → Fin d → S) (ha : ∀ i j, IsNilpotent (a i j)) (i : Fin n) (j : Fin d) :
    nv s (MvPowerSeries.X (i, j)) a = a i j := by
  obtain ⟨ψ, h1, -, h3⟩ := (nv_calculus R S s n d a ha).1
  rw [← h1, h3]

private lemma nv_zero {R S : Type} [CommRing R] [CommRing S] (s : R →+* S) {n d : ℕ}
    (a : Fin n → Fin d → S) (ha : ∀ i j, IsNilpotent (a i j)) :
    nv s (0 : PS R n d) a = 0 := by
  obtain ⟨ψ, h1, -, -⟩ := (nv_calculus R S s n d a ha).1
  rw [← h1, map_zero]

private lemma nilpotent_eval_subst_pair {R S : Type} [CommRing R] [CommRing S] (s : R →+* S) {n d : ℕ}
    (a : Fin n → Fin d → S) (ha : ∀ i j, IsNilpotent (a i j)) (b c : Fin d → PS R n d) (f : PS R 2 d)
    (hb : ∀ j, MvPowerSeries.constantCoeff (b j) = 0) (hc : ∀ j, MvPowerSeries.constantCoeff (c j) = 0) :
    nv s (ev ![b, c] f) a = nv s f ![fun j => nv s (b j) a, fun j => nv s (c j) a] := by
  rw [nv_ev s a ha _ f (by intro i j; fin_cases i; exacts [hb j, hc j])]
  congr 1
  funext i j
  fin_cases i <;> rfl

private lemma const_pt {R : Type} [CommRing R] {n d : ℕ} (i : Fin n) (j : Fin d) :
    MvPowerSeries.constantCoeff (pt R d i j) = 0 := by
  simp [pt]

private lemma nv_pt {R S : Type} [CommRing R] [CommRing S] (s : R →+* S) {n d : ℕ}
    (a : Fin n → Fin d → S) (ha : ∀ i j, IsNilpotent (a i j)) (i : Fin n) :
    (fun j => nv s (pt R d i j) a) = a i := funext fun j => nv_X s a ha i j

private lemma nv_at_zero {R : Type} [CommRing R] {n d : ℕ} (f : PS R n d) :
    nv (algebraMap R R) f (0 : Fin n → Fin d → R) = MvPowerSeries.constantCoeff f := by
  have := (nv_calculus R R (algebraMap R R) n d 0 (fun _ _ => IsNilpotent.zero)).2.2.2.2.2
    (fun _ _ _ _ => by simp) f
  simpa using this

private lemma constantCoeff_germEvalTwo_eq_zero {R : Type} [CommRing R] {n d : ℕ} (b c : Fin d → PS R n d) (f : PS R 2 d)
    (hb : ∀ j, MvPowerSeries.constantCoeff (b j) = 0) (hc : ∀ j, MvPowerSeries.constantCoeff (c j) = 0)
    (hf : MvPowerSeries.constantCoeff f = 0) :
    MvPowerSeries.constantCoeff (ev ![b, c] f) = 0 := by
  rw [← nv_at_zero, nilpotent_eval_subst_pair _ _ (fun _ _ => IsNilpotent.zero) _ _ _ hb hc, ← hf, ← nv_at_zero]
  congr 1
  funext i j
  fin_cases i
  · exact (nv_at_zero _).trans (hb j)
  · exact (nv_at_zero _).trans (hc j)

theorem exists_nilChart : ∀ (R : Type) [CommRing R] [IsLocalRing R] (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (g : ℕ), SmoothOfRelativeDimension g G.hom → ∃ (F : FGLaw R g) (X : Fam G g), NilChart G F.F X := by
  intro R _ _ G _ _ g hG
  classical
  obtain ⟨x, h0, hnat, hinj, hsur⟩ := GlobalTheory.NilCoord.nilpotent_coordinates G g hG
  have hser := @GlobalTheory.exists_series_of_natural_on_nilpotent (@GlobalTheory.nEval_basic)
  obtain ⟨F0, hF0⟩ := GlobalTheory.ChLaw.groupLaw_powerSeries (@GlobalTheory.nEval_basic) (@hser) G g x ⟨h0, hnat, hinj, hsur⟩
  have hF : ∀ k : Fin g, ∃ f : PS R 2 g, ∀ (S : Type) [CommRing S] [Algebra R S] (u : Fin 2 × Fin g → S),
      (∀ i, IsNilpotent (u i)) → fAdd F0 (fun j => u (0, j)) (fun j => u (1, j)) k = nEval f u := by
    intro k
    refine hser (fun S _ _ u => fAdd F0 (fun j => u (0, j)) (fun j => u (1, j)) k) ?_
    intro S _ _ S' _ _ φ u hu
    unfold fAdd
    rw [((GlobalTheory.nEval_basic (F0 k) S _).2 (by rintro (i | i) <;> exact hu _)).1 S' φ]
    congr 1
    funext i
    rcases i with i | i <;> rfl
  choose F hF using hF
  have hFe : ∀ (S : Type) [CommRing S] [Algebra R S] (a b : Fin g → S), (∀ i, IsNilpotent (a i)) →
      (∀ i, IsNilpotent (b i)) → fAdd F0 a b = fun k => nv (algebraMap R S) (F k) ![a, b] := by
    intro S _ _ a b ha hb
    funext k
    rw [nv_eq_nEval, ← hF k S _ (by rintro ⟨i, j⟩; fin_cases i; exacts [ha j, hb j])]
    rfl
  have law : ∀ (S : Type) [CommRing S] [Algebra R S] (a b : Fin g → S), (∀ i, IsNilpotent (a i)) →
      (∀ i, IsNilpotent (b i)) → x S a * x S b = x S (fun k => nv (algebraMap R S) (F k) ![a, b]) := by
    intro S _ _ a b ha hb
    rw [← hFe S a b ha hb]
    exact (hF0 S a b ha hb).2
  have nil : ∀ (S : Type) [CommRing S] [Algebra R S] (a b : Fin g → S), (∀ i, IsNilpotent (a i)) →
      (∀ i, IsNilpotent (b i)) → ∀ k, IsNilpotent (nv (algebraMap R S) (F k) ![a, b]) := by
    intro S _ _ a b ha hb k
    have h1 := (hF0 S a b ha hb).1 k
    rw [hFe S a b ha hb] at h1
    have h : Ideal.span (Set.range a ∪ Set.range b) ≤ nilradical S := Ideal.span_le.2 (by
      rintro _ (⟨i, rfl⟩ | ⟨i, rfl⟩)
      exacts [mem_nilradical.2 (ha i), mem_nilradical.2 (hb i)])
    exact mem_nilradical.1 (h h1)
  have hz : ∀ (S : Type) [CommRing S] (i : Fin g), IsNilpotent ((0 : Fin g → S) i) :=
    fun S _ i => IsNilpotent.zero
  have unitL : ∀ (S : Type) [CommRing S] [Algebra R S] (a : Fin g → S), (∀ i, IsNilpotent (a i)) →
      (fun k => nv (algebraMap R S) (F k) ![0, a]) = a := by
    intro S _ _ a ha
    refine hinj S _ _ (nil S _ _ (hz S) ha) ha ?_
    rw [← law S _ _ (hz S) ha, h0, _root_.one_mul]
  have const : ∀ k, MvPowerSeries.constantCoeff (F k) = 0 := by
    intro k
    have h := congrFun (unitL R 0 (hz R)) k
    rw [← nv_at_zero]
    refine Eq.trans ?_ h
    congr 1
    funext i j
    fin_cases i <;> rfl
  refine ⟨⟨F, const, ?_, ?_, ?_⟩, x, ⟨h0, hnat, hinj, ?_, law⟩⟩
  · intro k
    refine sep_nil _ _ fun S _ _ a ha => ?_
    rw [nilpotent_eval_subst_pair _ a ha (0 : Fin g → PS R 1 g) _ _ (fun _ => map_zero _) (const_pt _), nv_pt _ a ha, nv_X _ a ha]
    have e : (fun j => nv (algebraMap R S) ((0 : Fin g → PS R 1 g) j) a) = 0 :=
      funext fun j => nv_zero _ a ha
    rw [e]
    exact congrFun (unitL S (a 0) (ha 0)) k
  · intro k
    refine sep_nil _ _ fun S _ _ a ha => ?_
    rw [nilpotent_eval_subst_pair _ a ha _ _ _ (const_pt _) (const_pt _), nv_pt _ a ha, nv_pt _ a ha]
    have e : a = ![a 0, a 1] := by
      funext i
      fin_cases i <;> rfl
    conv_rhs => rw [e]
    refine congrFun (hinj S _ _ (nil S _ _ (ha 1) (ha 0)) (nil S _ _ (ha 0) (ha 1)) ?_) k
    rw [← law S _ _ (ha 1) (ha 0), ← law S _ _ (ha 0) (ha 1), _root_.mul_comm]
  · intro k
    refine sep_nil _ _ fun S _ _ a ha => ?_
    rw [nilpotent_eval_subst_pair _ a ha _ _ _ (fun l => constantCoeff_germEvalTwo_eq_zero _ _ _ (const_pt _) (const_pt _) (const l)) (const_pt _),
      nilpotent_eval_subst_pair _ a ha _ _ _ (const_pt _) (fun l => constantCoeff_germEvalTwo_eq_zero _ _ _ (const_pt _) (const_pt _) (const l))]
    simp only [nilpotent_eval_subst_pair _ a ha _ _ _ (const_pt _) (const_pt _), nv_pt _ a ha]
    refine congrFun (hinj S _ _ (nil S _ _ (nil S _ _ (ha 0) (ha 1)) (ha 2))
      (nil S _ _ (ha 0) (nil S _ _ (ha 1) (ha 2))) ?_) k
    rw [← law S _ _ (nil S _ _ (ha 0) (ha 1)) (ha 2), ← law S _ _ (ha 0) (nil S _ _ (ha 1) (ha 2)),
      ← law S _ _ (ha 0) (ha 1), ← law S _ _ (ha 1) (ha 2), _root_.mul_assoc]
  · intro S _ _ S' _ _ ρ σ hρσ hn z hz'
    refine hsur S S' ρ (fun y => ⟨σ y, AlgHom.congr_fun hρσ y⟩) ?_ z hz'
    intro c hc
    obtain ⟨N, hN⟩ := hn
    have := Ideal.pow_mem_pow hc N
    rw [hN] at this
    exact ⟨N, by simpa using this⟩

end GlobalTheory.ChF
end

section

set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory.ChF

private theorem lift_of_smooth_affine {G B : Scheme.{0}} (q : G ⟶ B) [Smooth q] [IsAffineHom q]
    {S S' : Type} [CommRing S] [CommRing S'] (π : S →+* S') (hπ : Function.Surjective π)
    (hk : IsNilpotent (RingHom.ker π)) (y : Spec (CommRingCat.of S) ⟶ B) (x : Spec (CommRingCat.of S') ⟶ G)
    (h : x ≫ q = Spec.map (CommRingCat.ofHom π) ≫ y) :
    ∃ w : Spec (CommRingCat.of S) ⟶ G, w ≫ q = y ∧ Spec.map (CommRingCat.ofHom π) ≫ w = x := by
  have : IsAffine (pullback q y) := isAffine_of_isAffineHom (pullback.snd q y)
  let e := (pullback q y).isoSpec
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (pullback.lift x _ h ≫ e.hom)
  obtain ⟨α, hα⟩ := Spec.map_surjective (e.inv ≫ pullback.snd q y)
  have hs : RingHom.Smooth α.hom := by
    rw [← HasRingHomProperty.Spec_iff (P := @Smooth), hα]
    infer_instance
  have hφα : α ≫ φ = CommRingCat.ofHom π := by
    apply Spec.map_injective
    rw [Spec.map_comp, hα, hφ, Category.assoc, Iso.hom_inv_id_assoc, pullback.lift_snd]
  letI : Algebra S Γ(pullback q y, ⊤) := α.hom.toAlgebra
  letI : Algebra S S' := π.toAlgebra
  haveI : Algebra.Smooth S Γ(pullback q y, ⊤) := hs
  let φ' : Γ(pullback q y, ⊤) →ₐ[S] S' := ⟨φ.hom, fun r => congr($hφα r)⟩
  let ψ := Algebra.FormallySmooth.liftOfSurjective φ' (Algebra.ofId S S') hπ hk
  have hψ : (Algebra.ofId S S').comp ψ = φ' :=
    Algebra.FormallySmooth.comp_liftOfSurjective φ' (Algebra.ofId S S') hπ hk
  let ψ' : Γ(pullback q y, ⊤) ⟶ CommRingCat.of S := CommRingCat.ofHom ψ.toRingHom
  have h₁ : α ≫ ψ' = 𝟙 _ := by
    ext r
    exact ψ.commutes r
  have h₂ : ψ' ≫ CommRingCat.ofHom π = φ := by
    ext a
    exact congr($hψ a)
  refine ⟨Spec.map ψ' ≫ e.inv ≫ pullback.fst q y, ?_, ?_⟩
  · rw [Category.assoc, Category.assoc, pullback.condition, ← Category.assoc e.inv, ← hα, ← Category.assoc,
      ← Spec.map_comp, h₁, Spec.map_id, Category.id_comp]
  · rw [← Category.assoc, ← Spec.map_comp, h₂, hφ, Category.assoc, Iso.hom_inv_id_assoc, pullback.lift_fst]

theorem qRel_lift : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : Out.DegPre R) (k : ℕ) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (c : Out.GtCoord I D k G) (S : Type) [CommRing S] [Algebra R S], Kills I k S → ∀ (S' : Type) [CommRing S'] [Algebra R S'] (ρ : S →ₐ[R] S') (σ : S' →ₐ[R] S), ρ.comp σ = AlgHom.id R S' → RingHom.ker ρ ^ 2 = ⊥ → ∀ y : sp (R₀ := R) S ⟶ D.P.A, spMap ρ ≫ y = 1 → ∃ z : sp (R₀ := R) S ⟶ G, spMap ρ ≫ z = 1 ∧ QRel c S z y := by
  intro R _ _ I D k G _ _ c S _ _ hS S' _ _ ρ σ hρσ hk y hy
  have hS' : Kills I k S' := fun t ht => by rw [← ρ.commutes, hS t ht, map_zero]
  obtain ⟨hex, hmul⟩ := (qRel_existsUnique_mul_nat R I D k G c).1 S' hS'
  obtain ⟨y₀, hy₀, hu⟩ := hex 1
  have h1 : y₀ = 1 := by
    have h := hmul 1 1 y₀ y₀ hy₀ hy₀
    rw [_root_.mul_one] at h
    exact mul_eq_left.1 (hu _ h)
  subst h1
  obtain ⟨x, hx₁, hx₂⟩ := hy₀
  have := c.q_hom
  have := c.q_flat
  have := c.q_surj
  have := c.q_affine
  have := (H1.torus_dim (Spec (CommRingCat.of (R ⧸ I ^ (k + 1)))) D.X).smooth
  have : Smooth c.q.left := by
    refine MorphismProperty.of_isPullback_of_descendsAlong (P := @Smooth)
      (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact)
      ((H1.torsor_pullback c.i c.q c.isKernel).map (Over.forget _)).flip
      ⟨⟨‹_›, ‹_›⟩, inferInstanceAs (QuasiCompact c.q.left)⟩ ?_
    exact smooth_isStableUnderBaseChange.of_isPullback (IsPullback.of_hasPullback _ _) this
  have : IsClosedImmersion (Out.thick R I k) := IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  have hf : Mono (pullback.fst D.P.A.hom (Out.thick R I k)) := inferInstance
  let t : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of (R ⧸ I ^ (k + 1))) :=
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.lift (I ^ (k + 1)) (algebraMap R S) hS))
  have ht : t ≫ Out.thick R I k = Spec.map (CommRingCat.ofHom (algebraMap R S)) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rfl
  let y' : Spec (CommRingCat.of S) ⟶ (Out.thickObj R I k D.P.A).left :=
    pullback.lift y.left t ((Over.w y).trans ht.symm)
  have hy' : y' ≫ pullback.fst D.P.A.hom (Out.thick R I k) = y.left := pullback.lift_fst _ _ _
  have hyl : Spec.map (CommRingCat.ofHom ρ.toRingHom) ≫ y.left = (1 : sp (R₀ := R) S' ⟶ D.P.A).left :=
    congrArg (·.left) hy
  obtain ⟨w, hw₁, hw₂⟩ := lift_of_smooth_affine c.q.left ρ.toRingHom
    (fun a => ⟨σ a, congr($hρσ a)⟩) ⟨2, hk⟩ y' x (by
      refine (cancel_mono (pullback.fst D.P.A.hom (Out.thick R I k))).1 ?_
      exact ((Category.assoc _ _ _).trans hx₂).trans
        (hyl.symm.trans ((congrArg (_ ≫ ·) hy'.symm).trans (Category.assoc _ _ _).symm)))
  have hq : w ≫ c.pG.left = y.left := (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) hw₁).trans hy')
  have hz : (w ≫ (Out.fstG I k G).left) ≫ G.hom = Spec.map (CommRingCat.ofHom (algebraMap R S)) := by
    have a : (Out.fstG I k G).left ≫ G.hom = c.pG.left ≫ D.P.A.hom := (Over.w _).trans (Over.w _).symm
    exact (Category.assoc _ _ _).trans ((congrArg (w ≫ ·) a).trans
      ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ D.P.A.hom) hq).trans (Over.w y))))
  refine ⟨Over.homMk (w ≫ (Out.fstG I k G).left) hz, ?_, w, rfl, hq⟩
  apply Over.OverMorphism.ext
  exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ (Out.fstG I k G).left) hw₂).trans hx₁)

end GlobalTheory.ChF
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem character_on_torsion_points_eq_series : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O → ∀ [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] (d : ℕ) (F : FGLaw O d), FH p F.F → ∀ (k : ℕ) (κ : (PS O 1 d →ₐ[O] O) → C), (∀ φ φ' ψ, Killed F.F (p ^ k) φ → Killed F.F (p ^ k) φ' → IsSum F.F φ φ' ψ → κ ψ = κ φ * κ φ') → (∀ φ, (∀ f, φ f = MvPowerSeries.constantCoeff f) → κ φ = 1) → ∃ u : PS O 1 d, ∀ φ, Killed F.F (p ^ k) φ → algebraMap O C (φ u) = κ φ := by
  intro p _ C _ _ _ v O _ _ hv _ _ d F hFH k κ hmul hone
  obtain ⟨inst, hsum, hzero, hkill⟩ := GlobalTheory.T.exists_addCommMonoid_algHom_powerSeries_fgLaw p C v O hv d F
  letI := inst
  obtain ⟨hfree, hfin, -⟩ := hFH k
  have hinj : Function.Injective (algebraMap O C) := hv.hom_inj
  haveI : IsDomain O := hinj.isDomain (algebraMap O C)
  set J : Ideal (PS O 1 d) := Ideal.span (Set.range (mulF F.F (p ^ k))) with hJ
  let N : AddSubmonoid (PS O 1 d →ₐ[O] O) :=
    { carrier := {φ | (p ^ k) • φ = 0}
      zero_mem' := nsmul_zero _
      add_mem' := by
        intro a b ha hb
        simp only [Set.mem_setOf_eq] at ha hb ⊢
        rw [nsmul_add, ha, hb, add_zero] }
  have hN : ∀ n : N, Killed F.F (p ^ k) n.1 := fun n => (hkill _ _).1 n.2
  have hNJ : ∀ n : N, ∀ u ∈ J, n.1 u = 0 := by
    intro n u hu
    have hle : J ≤ RingHom.ker n.1 := by
      rw [hJ, Ideal.span_le]
      rintro _ ⟨j, rfl⟩
      exact hN n j
    exact hle hu
  let L : N → (QF F.F (p ^ k) →ₐ[O] O) := fun n => Ideal.Quotient.liftₐ J n.1 (hNJ n)
  have hL : ∀ (n : N) (u : PS O 1 d), L n (Ideal.Quotient.mk J u) = n.1 u := fun n u => rfl
  have hLinj : Function.Injective L := by
    intro a b hab
    apply Subtype.ext
    apply AlgHom.ext
    intro u
    rw [← hL, ← hL, hab]
  haveI : Finite N := Finite.of_injective L hLinj
  let T : QF F.F (p ^ k) →ₗ[O] (N → C) :=
    LinearMap.pi fun n => (Algebra.linearMap O C).comp (L n).toLinearMap
  have hmem : ∀ f : N → C, f ∈ LinearMap.range T ↔
      ∃ u : PS O 1 d, ∀ n : N, algebraMap O C (n.1 u) = f n := by
    intro f
    constructor
    · rintro ⟨q, rfl⟩
      obtain ⟨u, rfl⟩ := Ideal.Quotient.mk_surjective q
      exact ⟨u, fun n => rfl⟩
    · rintro ⟨u, hu⟩
      exact ⟨Ideal.Quotient.mk J u, funext hu⟩
  have hfg : (LinearMap.range T).FG := Module.Finite.iff_fg.1 inferInstance
  have hspan : Submodule.span C ((LinearMap.range T : Submodule O (N → C)) : Set (N → C)) = ⊤ := by
    let e : N → (PS O 1 d →* C) := fun n =>
      ((algebraMap O C).comp (n.1 : PS O 1 d →+* O) : PS O 1 d →+* C).toMonoidHom
    have he : Function.Injective e := by
      intro a b hab
      apply Subtype.ext
      apply AlgHom.ext
      intro u
      exact hinj (DFunLike.congr_fun hab u)
    have hli : LinearIndependent C (fun n : N => (e n : PS O 1 d → C)) :=
      (linearIndependent_monoidHom (PS O 1 d) C).comp e he
    have htop := span_flip_eq_top_iff_linearIndependent.2 hli
    rw [eq_top_iff, ← htop]
    apply Submodule.span_mono
    rintro _ ⟨u, rfl⟩
    exact (hmem _).2 ⟨u, fun n => rfl⟩
  have key := GlobalTheory.character_mem_lattice_of_comul C v O hv N (LinearMap.range T) hfg hspan ?_ ?_
    (fun n => κ n.1) (hone _ hzero)
    (fun x y => hmul _ _ _ (hN x) (hN y) ((hsum _ _ _).2 rfl))
  · obtain ⟨u, hu⟩ := (hmem _).1 key
    exact ⟨u, fun φ hφ => hu ⟨φ, (hkill _ _).2 hφ⟩⟩
  · intro f hf
    obtain ⟨u, hu⟩ := (hmem _).1 hf
    obtain ⟨m, g, h, hgh⟩ := GlobalTheory.T.exists_sum_mul_eval_two_points_of_free_finite_quotient p C v O hv d J hfree hfin (ev (n := 2) ![F.F] u)
    refine ⟨m, fun i n => algebraMap O C (n.1 (g i)), fun i n => algebraMap O C (n.1 (h i)),
      fun i => (hmem _).2 ⟨g i, fun n => rfl⟩, fun i => (hmem _).2 ⟨h i, fun n => rfl⟩, ?_⟩
    intro x y
    obtain ⟨Φ, h0, h1, h2⟩ := (hsum x.1 y.1 (x + y).1).2 rfl

    rw [← hu, ← h2, hgh Φ x.1 y.1 h0 h1 (hNJ x) (hNJ y), map_sum]
    simp only [map_mul]
  · intro f hf
    obtain ⟨u, hu⟩ := (hmem _).1 hf
    exact ⟨_, hu 0⟩

end GlobalTheory
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_tangentChartMatrix_of_basis : ∀ (R₀ : Type) [CommRing R₀] (B : BX R₀) (O : LAlg R₀) (g : ℕ) (F : FGLaw (O : Type) g) (Y : ∀ R : LAlg R₀, LHom O R → (Fin g → (R : Type)) → B.G R), BXChart B O F.F Y → ∀ gb : Module.Basis (Fin g) R₀ B.gg, ∃ S : Matrix (Fin g) (Fin g) (O : Type), IsUnit S ∧ TanMat B O Y gb S := by
  first | exact @GlobalTheory.ChF.exists_tanMat | exact GlobalTheory.ChF.exists_tanMat | (intros; apply GlobalTheory.ChF.exists_tanMat <;> assumption)
end
