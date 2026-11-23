module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle463
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle476
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle477
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StepLevelContainsDeepCongruenceAtBadPrime
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsBlockOrderedSumEquivTrueIndex
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle455
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle475
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemSmulLk
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle015
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle478
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_topStep_level_congruent_blockSum_one : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (u : B.Word) (a : I.ι) (i : ℕ), i = B.R.m → ∀ (b : (I.stp u a i).β) (κ : (I.stp u a i).G b) (P : SBof I a), ∃ g g' z, GlobalTheory.TwU.TopLev (R := B.R) I.Ch I.sel (I.tup a) (I.cst a) i P g z ∧ LiftsInv I κ P g' ∧ CongE P.1 (GlobalTheory.TwU.topDep I.sel (I.tup a) (I.cst a) P) g g' := by
  first | exact @GlobalTheory.Mem.Col2.AdT.exists_topLev_liftsInv | exact GlobalTheory.Mem.Col2.AdT.exists_topLev_liftsInv | (intros; apply GlobalTheory.Mem.Col2.AdT.exists_topLev_liftsInv <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.levelPrime_primes_not_over_bad_prime_place : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (a : I.ι) (P : SBof I a) (v : HeightOneSpectrum (𝓞 B.host.F)), Formalism.L2.Col.IsOver v P.1 → ∀ (u : B.Word), ∀ P' ∈ (B.primes X).vT u, ¬ Formalism.L2.Col.IsOver v P' := by
  first | exact @GlobalTheory.Mem.Col2.AdT.vT_notOver_SBof | exact GlobalTheory.Mem.Col2.AdT.vT_notOver_SBof | (intros; apply GlobalTheory.Mem.Col2.AdT.vT_notOver_SBof <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.AdT


private theorem mem_GLint_and_exists_liftsInv_of_congE : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (u : B.Word) (a : I.ι) (i : ℕ) (hi : i < B.R.m)
    (b : (I.stp u a i).β) (P : SBof I a) (g : Sp B.fields.E (B.R.N i) ≃ₗ[B.fields.E] Sp B.fields.E (B.R.N i)) (z : B.fields.K),
    MidAt I hi b P g z → g ∈ Formalism.L2.Col.GLint B.fields.E (B.R.N i) P.1 ∧
      ∀ g' ∈ Formalism.L2.Col.GLint B.fields.E (B.R.N i) P.1, CongE P.1 ((I.cst a).D P) g g' →
        ∃ κ : (I.stp u a i).G b, (I.stp u a i).gam b κ = 1 ∧ LiftsInv I κ P g' ∧ ∀ P', P' ≠ P → LiftsInv I κ P' 1 := by
  classical
  intro B X I hI u a i hi b P g z hmid
  have hO := hI.idx_ok a
  have hpr := (GlobalTheory.TwU.exists_midLev_iff (R := B.R) I.Ch I.sel (I.tup a) (I.cst a) i P
    ((I.idx a).h i (Idx.get b hi) P) g).mp ⟨z, hmid⟩
  have hgi : g ∈ Formalism.L2.Col.GLint B.fields.E (B.R.N i) P.1 := hO.int i (Idx.get b hi) P hpr
  refine ⟨hgi, fun g' hg' hc => ?_⟩
  have hb : b.1 = some (Idx.get b hi) := (Option.some_get _).symm
  have hstd : ∀ (k : ↥(Formalism.L2.Col.GLint B.fields.E (B.R.N i) P.1)) {x : Sp B.fields.E (B.R.N i)},
      x ∈ stdAt B.fields.E (B.R.N i) P.1 → k.1 x ∈ stdAt B.fields.E (B.R.N i) P.1 :=
    fun k _ hx => GlobalTheory.TopStep.glint_mem k hx
  refine ⟨⟨1, ⟨fun w => if h : w.1 = P.1 then
      (GlobalTheory.TopStep.redGL (B.R.N i) w.1 ⟨g, by rw [h]; exact hgi⟩)⁻¹ else 1, ?_⟩,
    ⟨fun w => if h : w.1 = P.1 then
      (⟨g', by rw [h]; exact hg'⟩ : ↥(Formalism.L2.Col.GLint B.fields.E (B.R.N i) w.1))⁻¹ else 1, ?_⟩⟩, ?_, ?_, ?_⟩
  · rw [LevFam.grp, Subgroup.mem_pi]
    intro w _
    simp only [levGAt, hb, Option.elim]
    by_cases hw : w.1 = P.1
    · rw [dite_eq_left hw]
      apply inv_mem
      rw [hO.grpG]
      obtain ⟨w, hwG⟩ := w
      simp only at hw
      subst hw
      exact ⟨g, hpr, fun x hx => GlobalTheory.TopStep.redV_redGL ⟨g, hgi⟩ hx⟩
    · rw [dite_eq_right hw]
      exact one_mem _
  · rw [LevQFam.grp, Subgroup.mem_pi]
    intro w _
    simp only [levQAt, hb, Option.elim]
    by_cases hw : w.1 = P.1
    · rw [dite_eq_left hw]
      apply inv_mem
      obtain ⟨w, hwQ⟩ := w
      simp only at hw
      subst hw
      have hgQ : (⟨g, hgi⟩ : ↥(Formalism.L2.Col.GLint B.fields.E (B.R.N i) P.1)) ∈
          ((I.idx a).levQ i (Idx.get b hi) ⟨P.1, hwQ⟩).H := by
        rw [hO.grpQ, Subgroup.mem_subgroupOf]
        exact hpr
      set k := (⟨g, hgi⟩ : ↥(Formalism.L2.Col.GLint B.fields.E (B.R.N i) P.1))⁻¹ with hk
      have hkg : ∀ v, k.1 (g v) = v := by
        intro v
        have h1 : k * (⟨g, hgi⟩ : ↥(Formalism.L2.Col.GLint B.fields.E (B.R.N i) P.1)) = 1 := inv_mul_cancel _
        exact congrArg (fun m : ↥(Formalism.L2.Col.GLint B.fields.E (B.R.N i) P.1) => m.1 v) h1
      have hdeep := levQ_deep I hI a i hi (Idx.get b hi) P hwQ (k * ⟨g', hg'⟩)
      obtain ⟨hd, -⟩ := hdeep (by
        intro x hx
        have hneg := Submodule.neg_mem _ (hstd k (hc x hx))
        rw [map_smul, map_sub, hkg, ← smul_neg, neg_sub] at hneg
        exact hneg)
      have e2 : (⟨g', hg'⟩ : ↥(Formalism.L2.Col.GLint B.fields.E (B.R.N i) P.1)) = ⟨g, hgi⟩ * (k * ⟨g', hg'⟩) := by
        rw [hk, mul_inv_cancel_left]
      rw [e2]
      exact mul_mem hgQ hd
    · rw [dite_eq_right hw]
      exact one_mem _
  · exact map_one (ufGL B.fields.E (B.R.N i))
  · refine ⟨hg', ?_, ?_⟩
    · intro h x hx
      dsimp only
      rw [dite_eq_left rfl, inv_inv, ← GlobalTheory.TopStep.redV_redGL ⟨g, hgi⟩ hx]
      have hD : (I.cst a).D P = 1 := hO.depthG P h
      have hq := hc x hx
      rw [hD, pow_one] at hq
      funext l
      have h1 : IntAt P.1 (g x l) := GlobalTheory.TopStep.mem_stdAt.mp (hstd ⟨g, hgi⟩ hx) l
      have h2 : IntAt P.1 (g' x l) := GlobalTheory.TopStep.mem_stdAt.mp (hstd ⟨g', hg'⟩ hx) l
      have h3 : IntAt P.1 (((qOf P.1 : ℕ) : B.fields.E)⁻¹ * (g x l - g' x l)) := GlobalTheory.TopStep.mem_stdAt.mp hq l
      have h0 := GlobalTheory.TopStep.redP_eq_zero_of_div (P := P.1) (a := g x l - g' x l) (by rw [div_eq_inv_mul]; exact h3)
      rw [GlobalTheory.TopStep.reduction_sub h1 h2, sub_eq_zero] at h0
      exact h0.symm
    · intro h
      dsimp only
      rw [dite_eq_left rfl, inv_inv]
  · intro P' hP'
    have hne : P'.1 ≠ P.1 := fun e => hP' (Subtype.ext e)
    refine ⟨one_mem _, ?_, ?_⟩
    · intro h x hx
      dsimp only
      rw [dite_eq_right hne, inv_one]
      simp
    · intro h
      dsimp only
      rw [dite_eq_right hne, inv_one]
      all_goals rfl


open Classical in
theorem midAt_lifts : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (u : B.Word) (a : I.ι) (i : ℕ) (hi : i < B.R.m)
    (b : (I.stp u a i).β) (P : SBof I a) (g : Sp B.fields.E (B.R.N i) ≃ₗ[B.fields.E] Sp B.fields.E (B.R.N i)) (z : B.fields.K),
    MidAt I hi b P g z → g ∈ Formalism.L2.Col.GLint B.fields.E (B.R.N i) P.1 ∧
      ∀ g' ∈ Formalism.L2.Col.GLint B.fields.E (B.R.N i) P.1, CongE P.1 ((I.cst a).D P) g g' →
        ∃ κ : (I.stp u a i).G b, (I.stp u a i).gam b κ = 1 ∧ LiftsInv I κ P g' ∧ ∀ P', P' ≠ P → LiftsInv I κ P' 1 := mem_GLint_and_exists_liftsInv_of_congE

end GlobalTheory.Mem.Col2.AdT

end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_unitaryAdelic_supported_at_bad_prime_place : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (a : I.ι) (i : ℕ) (hi : i ≤ B.R.m) (P : SBof I a) (v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F)), Formalism.L2.Col.IsOver v (GlobalTheory.TwU.seamP (sm I l Z) P.1) → ∀ A : GL (Fin ((I.rec7 l Z).R.N i)) (P.1.adicCompletion B.fields.E), ∃ z ∈ UPts (sigD (I.rec7 l Z)) (gramN (I.rec7 l Z) i hi) (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F), (∀ v', v' ≠ v → bc (prV (E := (I.rec7 l Z).host.E) v') z = 1) ∧ ∀ r s, adAt B.host.F P.1 (z.1 r s) = A.1 r s := by
  first | exact @GlobalTheory.Mem.Col2.AdLift.exists_lift | exact GlobalTheory.Mem.Col2.AdLift.exists_lift | (intros; apply GlobalTheory.Mem.Col2.AdLift.exists_lift <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.representativeLattice_eq_companion_of_adelicRep : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (i : ℕ) (hi : i ≤ B.R.m) (bad : Set (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (Ch : Type) (chOf : (I.stp u a i).Cl → Ch) (K : Charts I l Z u a i hi bad chOf) (k : Ch → GA B (B.R.N i)), ReadsAt I l Z K k → ∀ c : (I.stp u a i).Cl, ((I.stp u a i).rep c).1.1.deco.1.N = GlobalTheory.TwU.latCo (I.rec7 l Z).sp (gramN (I.rec7 l Z) i hi) 1 (B.fields.conjO (X.piT u)) ((K (chOf c)).y ⟨c, rfl⟩).1 (K (chOf c)).lev.Lb := by
  first | exact @GlobalTheory.Mem.Col2.AdT.lat_rep_eq_latCo | exact GlobalTheory.Mem.Col2.AdT.lat_rep_eq_latCo | (intros; apply GlobalTheory.Mem.Col2.AdT.lat_rep_eq_latCo <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.twistPrime_rowType_topRestriction_mul_levelChar_eq_one : ∀ {X : Fields} {R : Ranks} (ξ : Chr X.F X.E X.K) (Q : Finset (HeightOneSpectrum (𝓞 X.E))) (P : Q) (c M : ℕ), 1 ≤ M →
    ∀ (k : Formalism.L2.Col.GLint X.E (R.N R.m) P.1) (hk : k ∈ (levCong (N_m_succ R) P.1 c (rowTyQ R ξ Q P)).H)
    (g : Sp X.E (R.N R.m) ≃ₗ[X.E] Sp X.E (R.N R.m)) (g'' : Sp X.E ((R.N R.m - 1) + 0) ≃ₗ[X.E] Sp X.E ((R.N R.m - 1) + 0)),
    g'' ∈ LocE.JQ P.1 (qOf P.1) R.r (R.N R.m - 1) 0 →
    prXpG X.E (R.N R.m) ∘ₗ g.toLinearMap = g''.toLinearMap ∘ₗ prXpG X.E (R.N R.m) →
    CongE P.1 (2 * M) g (k⁻¹).1 →
    LocE.lamQB (resChar ξ P.1) R.r (R.N R.m - 1) g''.toLinearMap *
      (((levCong (N_m_succ R) P.1 c (rowTyQ R ξ Q P)).lam ⟨k, hk⟩ : X.Kˣ) : X.K) = 1 := by
  first | exact @GlobalTheory.TopRowsQ.lamQB_mul_levCong | exact GlobalTheory.TopRowsQ.lamQB_mul_levCong | (intros; apply GlobalTheory.TopRowsQ.lamQB_mul_levCong <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.couplingCosetInFrames_shape_at_bad_prime : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (u : B.Word) (a : I.ι) (i : ℕ) (p : PtAt B.R I.sel (I.tup a) (I.cst a) u i) (P : SBof I a), (i + 1 ≠ B.R.m → cosetIn p P = ∅) ∧ (i + 1 = B.R.m → (cosetIn p P).Nonempty ∧ (∀ y ∈ p.1.2, (frsF I.sel (I.tup a) p.1.1 P).symm y ∈ cosetIn p P) ∧ ∀ z ∈ cosetIn p P, (∀ z', z' ∈ cosetIn p P ↔ GlobalTheory.TwU.SameCoset I.sel (I.tup a) (I.cst a) P z' z) ∧ ∀ g g' : Sp B.fields.E (B.R.N i) ≃ₗ[B.fields.E] Sp B.fields.E (B.R.N i), g' ∈ Formalism.L2.Col.GLint B.fields.E (B.R.N i) P.1 → CongE P.1 ((I.cst a).D P) g g' → GlobalTheory.TwU.SameCoset I.sel (I.tup a) (I.cst a) P (g z) z → ∀ z', g' z' ∈ cosetIn p P ↔ z' ∈ cosetIn p P) := by
  first | exact @GlobalTheory.Mem.Col2.AdT.CosShape.cosShape | exact GlobalTheory.Mem.Col2.AdT.CosShape.cosShape | (intros; apply GlobalTheory.Mem.Col2.AdT.CosShape.cosShape <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_badPrime_over_bad_place_of_chain : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (a : I.ι) (v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F)), v ∈ badG (I.rec7 l Z) ∨ I.UnderQ a v → ∃ P ∈ SBof I a, Formalism.L2.Col.IsOver v (GlobalTheory.TwU.seamP (sm I l Z) P) := by
  first | exact @GlobalTheory.Mem.Col2.AdT.exists_SBof_over | exact GlobalTheory.Mem.Col2.AdT.exists_SBof_over | (intros; apply GlobalTheory.Mem.Col2.AdT.exists_SBof_over <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.typePrime_rowType_topRestriction_mul_levelChar_eq_one : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m) (w : {w // w ∈ Pr.vGs})
    (h0 : GL (Fin (R.N R.m - 1)) (𝓞 X.E ⧸ w.1.asIdeal)) (hh0 : h0 ∈ (rowTyG Ch (rPsymF Ch) w).H)
    (g g' : Sp X.E (R.N R.m) ≃ₗ[X.E] Sp X.E (R.N R.m)) (g'' : Sp X.E ((R.N R.m - 1) + 0) ≃ₗ[X.E] Sp X.E ((R.N R.m - 1) + 0)),
    g'' ∈ LocE.JGsym w.1 (qOf w.1) R.k R.rS R.r R.t (R.N R.m - 1) 0 →
    prXpG X.E (R.N R.m) ∘ₗ g.toLinearMap = g''.toLinearMap ∘ₗ prXpG X.E (R.N R.m) →
    g' ∈ Formalism.L2.Col.GLint X.E (R.N R.m) w.1 →
    (∀ x ∈ stdAt X.E (R.N R.m) w.1, redV w.1 (g' x) =
      ((diagEmb (𝓞 X.E ⧸ w.1.asIdeal) (Nat.sub_le (R.N R.m) 1) h0)⁻¹ : GL (Fin (R.N R.m)) (𝓞 X.E ⧸ w.1.asIdeal)).1.mulVec (redV w.1 x)) →
    CongE w.1 1 g g' →
    LocE.lamGBS (qOf w.1) (psi0P Ch w.1) (chiP Ch w.1) R.k R.r R.t R.m (R.N R.m - 1) 0 g''.toLinearMap *
      (((rowTyG Ch (rPsymF Ch) w).lam ⟨h0, hh0⟩ : X.Kˣ) : X.K) = 1 := by
  first | exact @GlobalTheory.Mem.Col2.AdT.lamGBS_top_mul_lam_eq_one | exact GlobalTheory.Mem.Col2.AdT.lamGBS_top_mul_lam_eq_one | (intros; apply GlobalTheory.Mem.Col2.AdT.lamGBS_top_mul_lam_eq_one <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.stepLevel_contains_deep_congruence_at_bad_prime : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (a : I.ι) (T i : ℕ) (hi : i ≤ B.R.m) (bad : Set (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (S : StepLevel (I.rec7 l Z).host.F (I.rec7 l Z).host.E (sigD (I.rec7 l Z)) (gramN (I.rec7 l Z) i hi) T (I.rec7 l Z).R.f bad) (P : SBof I a) (v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F)), Formalism.L2.Col.IsOver v (GlobalTheory.TwU.seamP (sm I l Z) P.1) → ∃ N : ℕ, ∀ z ∈ UPts (sigD (I.rec7 l Z)) (gramN (I.rec7 l Z) i hi) (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F), (∀ v', v' ≠ v → bc (prV (E := (I.rec7 l Z).host.E) v') z = 1) → GlobalTheory.TwU.CongAt (GlobalTheory.TwU.seamP (sm I l Z) P.1) N z → z ∈ S.U := by
  first | exact @GlobalTheory.Mem.Col2.AdT.Opn.level_contains_deep | exact GlobalTheory.Mem.Col2.AdT.Opn.level_contains_deep | (intros; apply GlobalTheory.Mem.Col2.AdT.Opn.level_contains_deep <;> assumption)
end

section

open Matrix NumberField MeasureTheory Formalism.DegreeFormula Formalism.MJ Formalism.UG Formalism.L2.Geo
open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.HodgeDomain GlobalTheory.TrueCx GlobalTheory.FlagFibre
open scoped ComplexOrder ENNReal

namespace GlobalTheory.FlagFibreInt

theorem dens_neg {m : ℕ} (B : Matrix (Fin m) (Fin m) ℂ) (y : Low m → ℂ) : dens (-B) y = dens B y := by
  unfold dens
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Matrix.mul_neg, Matrix.neg_mul, lminor, lminor, submatrix_neg, Pi.neg_apply, Pi.neg_apply, det_neg]
  simp

theorem shear_neg_J {p q : ℕ} (Z : Matrix (Fin p) (Fin q) ℂ) :
    shear (-Jpq p q) Z = fromBlocks (-1) (-Z) (-Zᴴ) (hQ Z) := by
  simp [shear, Jpq, hQ, fromBlocks_neg, fromBlocks_conjTranspose, fromBlocks_multiply, sub_eq_neg_add]

theorem flagConst_pos (m : ℕ) : 0 < flagConst m :=
  Finset.prod_pos fun i _ => by have := Real.pi_pos; positivity

theorem lintegral_dens_glue : ∀ (r p q : ℕ) (e : Fin r ≃ Fin p ⊕ Fin q), IsBlockSL2Embedding e → ∀ (A : Matrix (Fin r) (Fin r) ℂ), reindex e e A = -Jpq p q → ∀ v : Fin p × Fin q → ℂ, toMat v ∈ hcDom p q → ∫⁻ b : (Low q → ℂ) × (Low p → ℂ), ENNReal.ofReal (dens A (glue e (v, b))) = ENNReal.ofReal ((hQ (toMat v)).det.re ^ (-((p + q : ℕ) : ℤ)) / (flagConst p * flagConst q)) := by
  intro r p q e he A hA v hv
  set Z := toMat v with hZ
  have hH : (hQ Z).PosDef := hv
  have hd := hH.det_pos
  have hu : IsUnit (hQ Z).det := hd.ne'.isUnit
  set B : Matrix (Fin p) (Fin p) ℂ := 1 + Z * (hQ Z)⁻¹ * Zᴴ with hB
  have hBp : B.PosDef := PosDef.one.add_posSemidef (hH.inv.posSemidef.mul_mul_conjTranspose_same Z)
  have hs : schur (shear (-Jpq p q) Z) = -B := by
    rw [shear_neg_J, schur, hB]
    simp
    abel
  have h22 : (shear (-Jpq p q) Z).toBlocks₂₂ = hQ Z := by rw [shear_neg_J, toBlocks_fromBlocks₂₂]
  have hdet : B.det = ((hQ Z).det)⁻¹ := by
    have e1 : (1 : Matrix (Fin q) (Fin q) ℂ) + (hQ Z)⁻¹ * Zᴴ * Z = (hQ Z)⁻¹ := by
      rw [Matrix.mul_assoc, ← nonsing_inv_mul _ hu, ← Matrix.mul_add, hQ, sub_add_cancel, Matrix.mul_one]
    rw [hB, Matrix.mul_assoc, det_one_add_mul_comm, e1, det_nonsing_inv, Ring.inverse_eq_inv']
  obtain ⟨d, hd0, hdd⟩ : ∃ d : ℝ, 0 < d ∧ (hQ Z).det = d := by
    obtain ⟨h1, h2⟩ := Complex.pos_iff.1 hd
    exact ⟨_, h1, Complex.ext (by simp) (by simp [← h2])⟩
  have hpt : ∀ b : (Low q → ℂ) × (Low p → ℂ), ENNReal.ofReal (dens A (glue e (v, b))) =
      (ENNReal.ofReal (d ^ (-(2 * p : ℤ))) * ENNReal.ofReal (dens (hQ Z) b.1)) * ENNReal.ofReal (dens B b.2) := by
    intro b
    rw [GlobalTheory.T.leadingMinorFlagDensity_glueLowerUnitriangular r p q e he A (v, b) (by rw [hA]; exact h22 ▸ hu), hA]
    simp only [← hZ]
    rw [h22, hs, dens_neg, hdd, Complex.norm_real, Real.norm_of_nonneg hd0.le,
      ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (mul_nonneg (by positivity) (dens_nonneg _ _)),
      mul_comm (dens (hQ Z) b.1)]
  simp only [hpt]
  rw [Measure.volume_eq_prod, lintegral_prod_mul
    (f := fun y => ENNReal.ofReal (d ^ (-(2 * p : ℤ))) * ENNReal.ofReal (dens (hQ Z) y))
    (g := fun y => ENNReal.ofReal (dens B y))
    ((measurable_dens _).ennreal_ofReal.const_mul _).aemeasurable (measurable_dens _).ennreal_ofReal.aemeasurable,
    lintegral_const_mul _ (measurable_dens _).ennreal_ofReal, GlobalTheory.T.lintegral_leadingMinorFlagDensity_posDef _ _ hH, GlobalTheory.T.lintegral_leadingMinorFlagDensity_posDef _ _ hBp, hdet, hdd,
    ← Complex.ofReal_inv, Complex.ofReal_re, Complex.ofReal_re]
  have hp := flagConst_pos p
  have hq := flagConst_pos q
  rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  rw [_root_.inv_zpow', ← mul_div_assoc _ _ (flagConst q), div_mul_div_comm, ← zpow_add₀ hd0.ne', ← zpow_add₀ hd0.ne', mul_comm (flagConst q)]
  congr 2
  push_cast
  ring

end GlobalTheory.FlagFibreInt
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.HAt Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.exists_hermitianDownMove_at_levelPrime_place : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (H : Formalism.L2.Herm.HermColsCh (I.rec7 l Z)) (F : ∀ u, FormsTiedSym (I.rec7 l Z) u (H.Ch u) (H.chOf u)), (∀ u, I.StdF l Z u (F u) ∧ I.StdLvC l Z u (F u)) → CarH H F → ∀ u i v (c : ((I.rec7 l Z).mem u).C.cls i) (g : Module.Dual (((I.rec7 l Z).mem u).A.Fv v) (((I.rec7 l Z).fm u).lk i v c)), ∃ γ, i ≤ (I.rec7 l Z).R.m → g ≠ 0 → DnCl (F u).atT (F u).lv i v c g γ ∧ AdOf H u i c (((I.rec7 l Z).fm u).dn i v c g) γ v := by
  first | exact @GlobalTheory.Mem.Col2.HAt.dn_move_exists | exact GlobalTheory.Mem.Col2.HAt.dn_move_exists | (intros; apply GlobalTheory.Mem.Col2.HAt.dn_move_exists <;> assumption)
end
