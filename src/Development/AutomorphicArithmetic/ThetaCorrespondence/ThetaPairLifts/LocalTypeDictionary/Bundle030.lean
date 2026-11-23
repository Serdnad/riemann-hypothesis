module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1197
public import Development.AbelianVarietyTheory.Definitions.Divisors.PairsOfSquareTriple
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle475
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle010
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1521
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle424
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle225
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2141
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle016
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.MatchingAdjoints
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.HermitianOrthogonalExtensionData
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BlkGLMem
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle333
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1194
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulRealAdEqZero
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle204
import Mathlib.Tactic.Polynomial.Basic
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle011
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap

@[expose] public section

section

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
noncomputable section
namespace GlobalTheory.ThK.PolMatchStep
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.WeilM GlobalTheory.AdelicU
section Local
variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]
end Local
theorem polynomial_matching_on_succ : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W) (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a')
    (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched B G X om om' R Rf →
    ∀ (T : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F))) (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)), v ∈ T →
    ∀ h ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UAt σ G.W (GlobalTheory.AdelicU.evFin F v), ∀ Φ Φ',
    GlobalTheory.ThK.PolynomialMatching.PolMatchOn B G X R Rf T Φ Φ' → GlobalTheory.ThK.PolynomialMatching.PolMatchOn B G X R Rf T (om (1, h) Φ) (om' (1, h) Φ') := by
  classical
  intro hP F E _ _ _ _ _ σ B a a' G X om om' R Rf hM T v hv h hh Φ Φ' hPM
  obtain ⟨m, m', f, φ, f', φ', hφ, hφ', hΦ, hΦ', hsum⟩ := hPM
  have hT := hM.triple
  have ex := (_root_.GlobalTheory.T.theta_kernel_local_operator_action hP) F E σ B _ _ _ _ _ _ _ _ _ _ _ _ (GlobalTheory.ThK.Inhab.pairV hT) v
  have ex' := (_root_.GlobalTheory.T.theta_kernel_local_operator_action hP) F E σ B _ _ _ _ _ _ _ _ _ _ _ _ (GlobalTheory.ThK.Inhab.pairV' hT) v
  have h1 : (1 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ G.V.J) ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UAt σ G.V (GlobalTheory.AdelicU.evFin F v) := by
    intro u _
    show u • ((1 : Matrix _ _ _) - 1) = 0
    simp
  have h1' : (1 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ G.V'.J) ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UAt σ G.V' (GlobalTheory.AdelicU.evFin F v) := by
    intro u _
    show u • ((1 : Matrix _ _ _) - 1) = 0
    simp
  have E1 := fun x hx => (ex.1 1 h1 h hh x hx).exists
  have E1' := fun x hx => (ex'.1 1 h1' h hh x hx).exists
  let loc : ((Fin a × Fin (a + a') → Fv F v) → ℂ) → (Fin a × Fin (a + a') → Fv F v) → ℂ :=
    fun x => if hx : x ∈ GlobalTheory.WeilM.SB _ then (E1 x hx).choose else 0
  let loc' : ((Fin a' × Fin (a + a') → Fv F v) → ℂ) → (Fin a' × Fin (a + a') → Fv F v) → ℂ :=
    fun x => if hx : x ∈ GlobalTheory.WeilM.SB _ then (E1' x hx).choose else 0
  have hloc : ∀ x ∈ GlobalTheory.WeilM.SB (Fin a × Fin (a + a') → Fv F v), loc x ∈ GlobalTheory.WeilM.SB _ ∧
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (GlobalTheory.AdelicU.evFin F v) (om (1, h)) x (loc x) := fun x hx => by
    simp only [loc, dif_pos hx]; exact (E1 x hx).choose_spec
  have hloc' : ∀ x ∈ GlobalTheory.WeilM.SB (Fin a' × Fin (a + a') → Fv F v), loc' x ∈ GlobalTheory.WeilM.SB _ ∧
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (GlobalTheory.AdelicU.evFin F v) (om' (1, h)) x (loc' x) := fun x hx => by
    simp only [loc', dif_pos hx]; exact (E1' x hx).choose_spec
  have pre : ∀ y : Rf.Pi v, ∃ x ∈ GlobalTheory.WeilM.SB (Fin a × Fin (a + a') → Fv F v), Rf.p v x = y := fun y => by
    have hy : y ∈ (GlobalTheory.WeilM.SB _).map (Rf.p v) := by rw [hM.fin.onto v]; trivial
    exact hy
  have pre' : ∀ y : Rf.Pi v, ∃ x ∈ GlobalTheory.WeilM.SB (Fin a' × Fin (a + a') → Fv F v), Rf.p' v x = y := fun y => by
    have hy : y ∈ (GlobalTheory.WeilM.SB _).map (Rf.p' v) := by rw [hM.fin.onto' v]; trivial
    exact hy
  let A0 : Rf.Pi v → Rf.Pi v := fun y => Rf.p v (loc (pre y).choose)
  have K : ∀ x ∈ GlobalTheory.WeilM.SB (Fin a × Fin (a + a') → Fv F v), A0 (Rf.p v x) = Rf.p v (loc x) := by
    intro x hx
    obtain ⟨hx0, hx0e⟩ := (pre (Rf.p v x)).choose_spec
    obtain ⟨x', hx', hx'e⟩ := pre' (Rf.p v x)
    have a1 := hM.fin.equiv v h hh _ hx0 x' hx' _ (hloc _ hx0).1 _ (hloc' x' hx').1 (hloc _ hx0).2 (hloc' x' hx').2
      (hx0e.trans hx'e.symm)
    have a2 := hM.fin.equiv v h hh x hx x' hx' _ (hloc x hx).1 _ (hloc' x' hx').1 (hloc x hx).2 (hloc' x' hx').2
      hx'e.symm
    exact a1.trans a2.symm
  have K' : ∀ x' ∈ GlobalTheory.WeilM.SB (Fin a' × Fin (a + a') → Fv F v), A0 (Rf.p' v x') = Rf.p' v (loc' x') := by
    intro x' hx'
    obtain ⟨x, hx, hxe⟩ := pre (Rf.p' v x')
    rw [← hxe, K x hx]
    exact hM.fin.equiv v h hh x hx x' hx' _ (hloc x hx).1 _ (hloc' x' hx').1 (hloc x hx).2 (hloc' x' hx').2 hxe
  have Klin : ∀ x ∈ GlobalTheory.WeilM.SB (Fin a × Fin (a + a') → Fv F v), ∀ y ∈ GlobalTheory.WeilM.SB (Fin a × Fin (a + a') → Fv F v),
      ∀ c d : ℂ, loc (c • x + d • y) = c • loc x + d • loc y := by
    intro x hx y hy c d
    have hs : c • x + d • y ∈ GlobalTheory.WeilM.SB (Fin a × Fin (a + a') → Fv F v) :=
      add_mem ((GlobalTheory.WeilM.SB _).smul_mem c hx) ((GlobalTheory.WeilM.SB _).smul_mem d hy)
    exact acts_lin_eq v (om (1, h)) hx hy (hloc x hx).2 (hloc y hy).2 c d (hloc _ hs).2
  let A : Rf.Pi v →ₗ[ℂ] Rf.Pi v :=
    { toFun := A0
      map_add' := by
        intro y z
        obtain ⟨x, hx, rfl⟩ := pre y
        obtain ⟨w, hw, rfl⟩ := pre z
        rw [← map_add (f := _), K _ (add_mem hx hw), K x hx, K w hw, ← map_add (f := _)]
        congr 1
        simpa using Klin x hx w hw 1 1
      map_smul' := by
        intro c y
        obtain ⟨x, hx, rfl⟩ := pre y
        rw [← map_smul, K _ ((GlobalTheory.WeilM.SB _).smul_mem c hx), K x hx, RingHom.id_apply, ← map_smul]
        congr 1
        simpa using Klin x hx x hx c 0 }
  have hvT : ∀ w, w ∉ T → w ≠ v := fun w hw e => hw (e ▸ hv)
  have evc : ∀ {n : ℕ} {Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ Y G.W) (ρ : ∀ w : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (Fin n × Fin (a + a') → Fv F w) → ℂ),
      (∀ w, w ∉ T → ρ w = M.vac w) → M.IsGood B.ψ →
      ∀ᶠ w in Filter.cofinite, ρ w = Set.indicator {x | ∀ i, x i ∈ w.adicCompletionIntegers F} 1 := by
    intro n Y M ρ hρ hG
    have e0 : ∀ᶠ w in Filter.cofinite, ρ w = M.vac w :=
      Filter.eventually_cofinite.2 ((T.finite_toSet).subset fun w hw => by
        by_contra hc; exact hw (hρ w hc))
    filter_upwards [e0, hG.std] with w e1 e2
    rw [e1, e2]
  let φN : Fin m → ∀ w : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (Fin a × Fin (a + a') → Fv F w) → ℂ :=
    fun i => Function.update (φ i) v (loc (φ i v))
  let φN' : Fin m' → ∀ w : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (Fin a' × Fin (a + a') → Fv F w) → ℂ :=
    fun j => Function.update (φ' j) v (loc' (φ' j v))
  refine ⟨m, m', f, φN, f', φN', fun i => ⟨(hφ i).1, fun w => ?_, fun w hw => ?_⟩,
    fun j => ⟨(hφ' j).1, fun w => ?_, fun w hw => ?_⟩, ?_, ?_, ?_⟩
  · by_cases hw : w = v
    · subst hw; simp only [φN, Function.update_self]; exact (hloc _ ((hφ i).2.1 w)).1
    · simp only [φN, Function.update_of_ne hw]; exact (hφ i).2.1 w
  · simp only [φN, Function.update_of_ne (hvT w hw)]; exact (hφ i).2.2 w hw
  · by_cases hw : w = v
    · subst hw; simp only [φN', Function.update_self]; exact (hloc' _ ((hφ' j).2.1 w)).1
    · simp only [φN', Function.update_of_ne hw]; exact (hφ' j).2.1 w
  · simp only [φN', Function.update_of_ne (hvT w hw)]; exact (hφ' j).2.2 w hw

  · rw [hΦ, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    exact pure_update v (om (1, h)) (f i) (φ i) (hφ i).2.1 (evc G.M (φ i) (hφ i).2.2 hT.geo.hM)
      (hloc _ ((hφ i).2.1 v)).2

  · rw [hΦ', map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    exact pure_update v (om' (1, h)) (f' j) (φ' j) (hφ' j).2.1 (evc G.M' (φ' j) (hφ' j).2.2 hT.geo.hM')
      (hloc' _ ((hφ' j).2.1 v)).2
  · have key := congrArg (LinearMap.lTensor R.Pi (PiTensorProduct.map
      (Function.update (fun u : T => (LinearMap.id : Rf.Pi u.1 →ₗ[ℂ] Rf.Pi u.1)) ⟨v, hv⟩ A))) hsum

    simp only [map_sum, LinearMap.lTensor_tmul, PiTensorProduct.map_tprod] at key
    have e1 : ∀ i, (fun u : T => Function.update (fun u : T => (LinearMap.id : Rf.Pi u.1 →ₗ[ℂ] Rf.Pi u.1)) ⟨v, hv⟩ A u
        (Rf.p u (φ i u))) = fun u : T => Rf.p u (φN i u) := by
      intro i; funext u
      by_cases hu : u = ⟨v, hv⟩
      · subst hu; simp only [Function.update_self, φN]; exact K _ ((hφ i).2.1 v)
      · have hu' : u.1 ≠ v := fun e => hu (Subtype.ext e)
        simp only [Function.update_of_ne hu, φN, Function.update_of_ne hu', LinearMap.id_apply]
    have e2 : ∀ j, (fun u : T => Function.update (fun u : T => (LinearMap.id : Rf.Pi u.1 →ₗ[ℂ] Rf.Pi u.1)) ⟨v, hv⟩ A u
        (Rf.p' u (φ' j u))) = fun u : T => Rf.p' u (φN' j u) := by
      intro j; funext u
      by_cases hu : u = ⟨v, hv⟩
      · subst hu; simp only [Function.update_self, φN']; exact K' _ ((hφ' j).2.1 v)
      · have hu' : u.1 ≠ v := fun e => hu (Subtype.ext e)
        simp only [Function.update_of_ne hu, φN', Function.update_of_ne hu', LinearMap.id_apply]
    simp only [e1, e2] at key
    exact key
end GlobalTheory.ThK.PolMatchStep
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree

theorem _root_.GlobalTheory.T.polynomial_matching_induction : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W) (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a')
    (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched B G X om om' R Rf →
    ∀ (T : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F))) (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)), v ∈ T →
    ∀ h ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UAt σ G.W (GlobalTheory.AdelicU.evFin F v), ∀ Φ Φ',
    GlobalTheory.ThK.PolynomialMatching.PolMatchOn B G X R Rf T Φ Φ' → GlobalTheory.ThK.PolynomialMatching.PolMatchOn B G X R Rf T (om (1, h) Φ) (om' (1, h) Φ') := by
  first | exact @_root_.GlobalTheory.ThK.PolMatchStep.polynomial_matching_on_succ | exact _root_.GlobalTheory.ThK.PolMatchStep.polynomial_matching_on_succ | (intros; apply _root_.GlobalTheory.ThK.PolMatchStep.polynomial_matching_on_succ <;> assumption)
end
end

section

section
noncomputable section
open scoped Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open GlobalTheory.ArchUniq GlobalTheory.ArchUniq.Coord
open scoped Classical
open MeasureTheory
namespace GlobalTheory.ArchLine
open scoped SchwartzMap
theorem archimedean_real_line_invariance : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (ψ : AddChar (AF F) ℂ)
    (χX χW : Chr F E) (om : Rep σ X W), IsCMExt F E σ → IsStd ψ → M.IsWeil ψ χX χW om →
    ∀ γ ∈ Lines σ W, ∃ (l : Type) (_ : Fintype l) (_ : DecidableEq l)
      (Φ : SInf F (Fin n × Fin d) ≃L[ℂ] GlobalTheory.RealWeil.Sch l) (g : ℝ → Matrix (l ⊕ l) (l ⊕ l) ℝ)
      (T : ℝ → GlobalTheory.RealWeil.Sch l →ₗ[ℂ] GlobalTheory.RealWeil.Sch l),
      Continuous g ∧ g 0 = 1 ∧ (∀ s t, g (s + t) = g s * g t) ∧ (∀ t, g t ∈ Matrix.symplecticGroup l ℝ) ∧
      T 0 = LinearMap.id ∧ (∀ s t, T (s + t) = T s ∘ₗ T t) ∧
      (∀ (t : ℝ) (w : l ⊕ l → ℝ) (h h₁ : GlobalTheory.RealWeil.Sch l), ⇑h₁ = GlobalTheory.RealWeil.rhoFun w ⇑h →
        ⇑(T t h₁) = GlobalTheory.RealWeil.rhoFun (g t *ᵥ w) ⇑(T t h)) ∧
      (∀ (t : ℝ) (h : GlobalTheory.RealWeil.Sch l), ∫⁻ x, ‖T t h x‖ₑ ^ 2 = ∫⁻ x, ‖h x‖ₑ ^ 2) ∧
      (∀ (h : GlobalTheory.RealWeil.Sch l) (x : EuclideanSpace ℝ l), Continuous fun t => T t h x) ∧
      ∀ (t : ℝ) (f : SInf F (Fin n × Fin d)),
        Acts (evI F) (om (1, γ (Multiplicative.ofAdd t))) ⇑f ⇑(Φ.symm (T t (Φ f))) := by
  intro hP F E _ _ _ _ _ σ n d X W M ψ χX χW om hCM hψ hW γ hγ
  have hex : ∀ h ∈ UAt σ W (evI F), ∀ f : SInf F (Fin n × Fin d), ∃ f₁ : SInf F (Fin n × Fin d),
      Acts (evI F) (om (1, h)) ⇑f ⇑f₁ := fun h hh f => _root_.GlobalTheory.T.theta_action_archimedean_locality hP M ψ χX χW om hCM hψ hW h hh f
  obtain ⟨hadd, hsmul, hone, hmul⟩ := GlobalTheory.T.archimedean_weilOperators_linear_one_mul M ψ χX χW om hW hex
  obtain ⟨aadd, asmul, amul⟩ := GlobalTheory.T.unitary_archimedean_coordinate_action_linear_mul M
  have hγU : ∀ t : ℝ, γ (Multiplicative.ofAdd t) ∈ UAt σ W (evI F) := fun t => hγ.2 _
  have hγ0 : γ (Multiplicative.ofAdd 0) = 1 := by rw [ofAdd_zero, map_one]
  have hγadd : ∀ s t : ℝ, γ (Multiplicative.ofAdd (s + t)) = γ (Multiplicative.ofAdd s) * γ (Multiplicative.ofAdd t) :=
    fun s t => by rw [ofAdd_add, map_mul]
  obtain ⟨N, hN⟩ : ∃ N, Module.finrank ℝ (Fin n × Fin d → mixedEmbedding.mixedSpace F) = N := ⟨_, rfl⟩
  obtain ⟨C, φ, hφ, hC⟩ := pairingCoords (Fin n × Fin d → mixedEmbedding.mixedSpace F) (trP F (Fin n × Fin d))
    (isPairing_trP _) N hN
  let S : ℝ → SInf F (Fin n × Fin d) →ₗ[ℂ] SInf F (Fin n × Fin d) := fun t =>
    { toFun := archOp om (γ (Multiplicative.ofAdd t))
      map_add' := hadd _ (hγU t)
      map_smul' := hsmul _ (hγU t) }
  let A : ℝ → ((Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F)) →ₗ[ℝ]
      ((Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F)) := fun t =>
    { toFun := archAct M (γ (Multiplicative.ofAdd t))
      map_add' := aadd _
      map_smul' := asmul _ }
  let ψt : ℝ → (Fin N ⊕ Fin N → ℝ) →ₗ[ℝ] (Fin N ⊕ Fin N → ℝ) := fun t =>
    φ.toLinearMap ∘ₗ A t ∘ₗ φ.symm.toLinearMap
  have hψt : ∀ t w, ψt t w = φ (archAct M (γ (Multiplicative.ofAdd t)) (φ.symm w)) := fun t w => rfl
  let g : ℝ → Matrix (Fin N ⊕ Fin N) (Fin N ⊕ Fin N) ℝ := fun t => LinearMap.toMatrix' (ψt t)
  have hg : ∀ t w, g t *ᵥ w = ψt t w := fun t w => LinearMap.toMatrix'_mulVec _ _
  let P1 : SInf F (Fin n × Fin d) →L[ℂ] GlobalTheory.RealWeil.Sch (Fin N) :=
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (F := ℂ) C.symm
  let P2 : GlobalTheory.RealWeil.Sch (Fin N) →L[ℂ] SInf F (Fin n × Fin d) :=
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (F := ℂ) C
  let eΦ : SInf F (Fin n × Fin d) ≃L[ℂ] GlobalTheory.RealWeil.Sch (Fin N) := ContinuousLinearEquiv.equivOfInverse P1 P2
    (fun f => by ext x; simp [P1, P2]) (fun h => by ext x; simp [P1, P2])
  have hΦ : ∀ f x, eΦ f x = f (C.symm x) := fun f x => rfl
  have hΦs : ∀ h x, eΦ.symm h x = h (C x) := fun h x => rfl
  let T : ℝ → GlobalTheory.RealWeil.Sch (Fin N) →ₗ[ℂ] GlobalTheory.RealWeil.Sch (Fin N) := fun t =>
    eΦ.toLinearMap ∘ₗ S t ∘ₗ eΦ.symm.toLinearMap
  have hT : ∀ t h x, T t h x = archOp om (γ (Multiplicative.ofAdd t)) (eΦ.symm h) (C.symm x) := fun t h x => rfl
  refine ⟨Fin N, inferInstance, inferInstance, eΦ, g, T, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine continuous_pi fun i => continuous_pi fun j => ?_
    simp only [g, LinearMap.toMatrix'_apply]
    exact (continuous_apply i).comp ((LinearMap.continuous_of_finiteDimensional φ.toLinearMap).comp
      (GlobalTheory.T.continuous_oneParameter_unitary_coordinate_action M γ hγ _))
  · have e : ψt 0 = LinearMap.id := LinearMap.ext fun w => by rw [hψt, hγ0, archAct_one]; simp
    simp only [g, e, LinearMap.toMatrix'_id]
  · intro s t
    have e : ψt (s + t) = ψt s ∘ₗ ψt t := LinearMap.ext fun w => by
      rw [hψt, LinearMap.comp_apply, hψt, hψt, hγadd, amul, LinearEquiv.symm_apply_apply]
    simp only [g, e, LinearMap.toMatrix'_comp]
  · intro t
    have hsym : ∀ w w', GlobalTheory.RealWeil.sympl (ψt t w) (ψt t w') = GlobalTheory.RealWeil.sympl w w' := fun w w' => by
      rw [hψt, hψt, hφ, GlobalTheory.T.unitary_archimedean_coordinate_action_symplectic, ← hφ, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
    obtain ⟨Mx, hMx⟩ := symplMatrix (Fin N) (ψt t) hsym
    have e : g t = Mx := Matrix.toLin'.injective (LinearMap.ext fun w => by
      rw [Matrix.toLin'_apply, Matrix.toLin'_apply, hg, hMx])
    rw [e]; exact Mx.2
  · refine LinearMap.ext fun h => ?_
    ext x
    rw [hT, hγ0, hone, hΦs]
    simp
  · intro s t
    refine LinearMap.ext fun h => ?_
    ext x
    show archOp om (γ (Multiplicative.ofAdd (s + t))) (eΦ.symm h) (C.symm x) =
      archOp om (γ (Multiplicative.ofAdd s)) (eΦ.symm (T t h)) (C.symm x)
    rw [hγadd, hmul _ (hγU s) _ (hγU t)]
    congr 2
    exact (eΦ.symm_apply_apply (S t (eΦ.symm h))).symm
  · intro t w h h₁ hh₁
    have hf : ⇑(eΦ.symm h₁) = schrF (trP F (Fin n × Fin d)) (φ.symm w) ⇑(eΦ.symm h) := by
      have e1 : ⇑(eΦ.symm h) = ⇑h ∘ ⇑C := funext (hΦs h)
      rw [e1, hC, LinearEquiv.apply_symm_apply]
      funext y; rw [hΦs, hh₁]; rfl
    have key := GlobalTheory.T.archimedean_weilOperator_intertwines_schroedinger M ψ χX χW om hψ hW hex _ (hγU t) (φ.symm w) _ _ hf
    have e2 : ⇑(archOp om (γ (Multiplicative.ofAdd t)) (eΦ.symm h)) = ⇑(T t h) ∘ ⇑C := by
      funext y; rw [Function.comp_apply, hT, ContinuousLinearEquiv.symm_apply_apply]
    funext x
    rw [hT, key, e2, hC, hg, hψt]
    simp
  · intro t h
    have e := GlobalTheory.T.archWeilOperator_unitaryW_lintegral_norm_eq M ψ χX χW om hW hex _ (hγU t) N C (eΦ.symm h)
    refine Eq.trans ?_ (e.trans ?_)
    · rfl
    · simp only [hΦs, ContinuousLinearEquiv.apply_symm_apply]
  · intro h x
    exact GlobalTheory.T.continuous_oneParameter_archimedean_weilOperator M ψ χX χW om hW hex γ hγ (eΦ.symm h) (C.symm x)
  · intro t f
    have e : eΦ.symm (T t (eΦ f)) = archOp om (γ (Multiplicative.ofAdd t)) f := by
      ext y; rw [hΦs, hT]; simp
    rw [e]
    exact acts_archOp om _ f (hex _ (hγU t) f)
end GlobalTheory.ArchLine
end
end

section
open scoped Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun

theorem _root_.GlobalTheory.T.archimedean_line_spanned_by_weil_vector : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (ψ : AddChar (AF F) ℂ)
    (χX χW : Chr F E) (om : Rep σ X W), IsCMExt F E σ → IsStd ψ → M.IsWeil ψ χX χW om →
    ∀ γ ∈ Lines σ W, ∃ (l : Type) (_ : Fintype l) (_ : DecidableEq l)
      (Φ : SInf F (Fin n × Fin d) ≃L[ℂ] GlobalTheory.RealWeil.Sch l) (g : ℝ → Matrix (l ⊕ l) (l ⊕ l) ℝ)
      (T : ℝ → GlobalTheory.RealWeil.Sch l →ₗ[ℂ] GlobalTheory.RealWeil.Sch l),
      Continuous g ∧ g 0 = 1 ∧ (∀ s t, g (s + t) = g s * g t) ∧ (∀ t, g t ∈ Matrix.symplecticGroup l ℝ) ∧
      T 0 = LinearMap.id ∧ (∀ s t, T (s + t) = T s ∘ₗ T t) ∧
      (∀ (t : ℝ) (w : l ⊕ l → ℝ) (h h₁ : GlobalTheory.RealWeil.Sch l), ⇑h₁ = GlobalTheory.RealWeil.rhoFun w ⇑h →
        ⇑(T t h₁) = GlobalTheory.RealWeil.rhoFun (g t *ᵥ w) ⇑(T t h)) ∧
      (∀ (t : ℝ) (h : GlobalTheory.RealWeil.Sch l), ∫⁻ x, ‖T t h x‖ₑ ^ 2 = ∫⁻ x, ‖h x‖ₑ ^ 2) ∧
      (∀ (h : GlobalTheory.RealWeil.Sch l) (x : EuclideanSpace ℝ l), Continuous fun t => T t h x) ∧
      ∀ (t : ℝ) (f : SInf F (Fin n × Fin d)),
        Acts (evI F) (om (1, γ (Multiplicative.ofAdd t))) ⇑f ⇑(Φ.symm (T t (Φ f))) := by
  first | exact @_root_.GlobalTheory.ArchLine.archimedean_real_line_invariance | exact _root_.GlobalTheory.ArchLine.archimedean_real_line_invariance | (intros; apply _root_.GlobalTheory.ArchLine.archimedean_real_line_invariance <;> assumption)
end
end

section

section
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
noncomputable section
namespace GlobalTheory.SplitScalar
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable {σ : E →ₐ[F] E} {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
theorem metaplectic_splittings_differ_by_character : _root_.GlobalTheory.FunPr.ThetaLocalInputs →
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (α β κ : Type) [Fintype α]
    [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ] (ψ : AddChar (AF F) ℂ) (JA : Matrix α α (AE F E))
    (JB : Matrix β β (AE F E)) (d : Darboux (symp (R := AF F) (cA σ) (-1) JA JB) κ)
    (om ω₀ : UG (cA σ) JB →* Module.End ℂ ((κ → AF F) → ℂ)), IsStd ψ →
    IsUSplitting (adeleClass F) ψ d (actB (cA σ)) om →
    (∀ g : UG (cA σ) JB, At (evI F) ((g.1 : Matrix β β (AE F E)) - 1) →
        (∀ φ ∈ schA F κ, ω₀ g φ ∈ schA F κ) ∧
        (∀ w, ∀ φ ∈ schA F κ, ω₀ g (d.rho ψ w φ) = d.rho ψ (actB (cA σ) g w) (ω₀ g φ)) ∧
        ∀ μ : @Measure (κ → AF F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
          ∀ φ ∈ schA F κ, ∫⁻ x, ‖ω₀ g φ x‖ₑ ^ 2 ∂μ = ∫⁻ x, ‖φ x‖ₑ ^ 2 ∂μ) →
    (∀ l ∈ (adeleClass F).adm κ, ∀ φ ∈ schA F κ,
        ContinuousOn (fun g => l (ω₀ g φ)) {g : UG (cA σ) JB | At (evI F) ((g.1 : Matrix β β (AE F E)) - 1)}) →
    ∃ ν : UG (cA σ) JB → ℂ,
      (∀ g : UG (cA σ) JB, At (evI F) ((g.1 : Matrix β β (AE F E)) - 1) → ∀ φ ∈ schA F κ, om g φ = ν g • ω₀ g φ) ∧
      (∀ g h : UG (cA σ) JB, At (evI F) ((g.1 : Matrix β β (AE F E)) - 1) → At (evI F) ((h.1 : Matrix β β (AE F E)) - 1) →
        ν (g * h) = ν g * ν h) ∧
      ContinuousOn ν {g : UG (cA σ) JB | At (evI F) ((g.1 : Matrix β β (AE F E)) - 1)} ∧
      ∀ g : UG (cA σ) JB, At (evI F) ((g.1 : Matrix β β (AE F E)) - 1) → ν g ≠ 0 := by
  intro hP F E _ _ _ _ _ σ α β κ _ _ _ _ _ ψ JA JB d om ω₀ hψ hom hω hcont
  have key : ∀ g : UG (cA σ) JB, ∃ z : ℂ, At (evI F) ((g.1 : Matrix β β (AE F E)) - 1) →
      ∀ φ ∈ schA F κ, om g φ = z • ω₀ g φ := by
    intro g
    by_cases hg : At (evI F) ((g.1 : Matrix β β (AE F E)) - 1)
    swap
    · exact ⟨1, fun h => absurd h hg⟩
    have hgi := at_inv hg
    have hscalar : ∃ z : ℂ, ∀ φ ∈ schA F κ, (om g * ω₀ g⁻¹) φ = z • φ :=
      _root_.GlobalTheory.T.adelic_intertwiner_eq_scalar hP F κ ψ hψ (om g * ω₀ g⁻¹)
      (fun φ hφ => hom.pres g _ ((hω _ hgi).1 φ hφ))
      (fun w φ hφ => by
        have e1 : schr ψ w φ = d.rho ψ (d.e.symm w) φ := by simp [Darboux.rho]
        rw [Module.End.mul_apply, Module.End.mul_apply, e1, (hω _ hgi).2.1 _ φ hφ,
          hom.impl g _ _ ((hω _ hgi).1 φ hφ), actB_actB_inv]
        simp [Darboux.rho])
      (fun μ hμ φ hφ => by
        rw [Module.End.mul_apply, hom.unit μ hμ g _ ((hω _ hgi).1 φ hφ), (hω _ hgi).2.2 μ hμ φ hφ])
    obtain ⟨z, hz⟩ := hscalar
    refine ⟨z, fun _ φ hφ => ?_⟩
    have := hz (ω₀ g φ) ((hω g hg).1 φ hφ)
    rwa [Module.End.mul_apply, ← Module.End.mul_apply (ω₀ g⁻¹), ← map_mul, inv_mul_cancel, map_one,
      Module.End.one_apply] at this
  choose z hz using key
  by_cases h0 : ∃ φ₀ ∈ schA F κ, φ₀ ≠ 0
  swap
  · push_neg at h0
    refine ⟨fun _ => 1, fun g _ φ hφ => ?_, fun _ _ _ _ => by simp, continuousOn_const, fun _ _ => one_ne_zero⟩
    rw [h0 φ hφ, map_zero, map_zero, smul_zero]
  obtain ⟨φ₀, hφ₀, hne⟩ := h0
  refine ⟨z, hz, fun g h hg hh => ?_, fun g hg => ?_, fun g hg h0 => ?_⟩
  · have hgh := at_mul hg hh
    apply smul_left_injective ℂ (apply_ne_zero ω₀ (g * h) hne)
    show z (g * h) • ω₀ (g * h) φ₀ = (z g * z h) • ω₀ (g * h) φ₀
    rw [← hz _ hgh φ₀ hφ₀, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hz h hh φ₀ hφ₀, map_smul,
      hz g hg _ ((hω h hh).1 φ₀ hφ₀), smul_smul, mul_comm]
  · obtain ⟨x, hx⟩ := Function.ne_iff.1 (apply_ne_zero ω₀ g hne)
    have hl := proj_mem_adm F κ x
    have c1 : ContinuousWithinAt (fun q => (LinearMap.proj x : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ) (ω₀ q φ₀))
        {g : UG (cA σ) JB | At (evI F) ((g.1 : Matrix β β (AE F E)) - 1)} g := hcont _ hl φ₀ hφ₀ g hg
    have c2 : ContinuousWithinAt (fun q => (LinearMap.proj x : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ) (om q φ₀))
        {g : UG (cA σ) JB | At (evI F) ((g.1 : Matrix β β (AE F E)) - 1)} g :=
      (hom.cont _ hl φ₀ hφ₀).continuousWithinAt
    have hx' : (LinearMap.proj x : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ) (ω₀ g φ₀) ≠ 0 := hx
    have c3 := c2.div c1 hx'
    have hq : ∀ q, At (evI F) ((q.1 : Matrix β β (AE F E)) - 1) →
        (LinearMap.proj x : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ) (ω₀ q φ₀) ≠ 0 →
        z q = (LinearMap.proj x : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ) (om q φ₀) /
          (LinearMap.proj x : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ) (ω₀ q φ₀) := by
      intro q hqS hq0
      rw [hz q hqS φ₀ hφ₀, map_smul, smul_eq_mul, mul_div_cancel_right₀ _ hq0]
    refine c3.congr_of_eventuallyEq ?_ (hq g hg hx')
    filter_upwards [Filter.Tendsto.eventually_ne c1 hx', self_mem_nhdsWithin] with q hq0 hqS
    exact hq q hqS hq0
  · have := hz g hg φ₀ hφ₀
    rw [h0, zero_smul] at this
    exact apply_ne_zero om g hne this
end GlobalTheory.SplitScalar
end
end

section
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift

theorem _root_.GlobalTheory.T.metaplectic_splitting_unique_up_to_character : _root_.GlobalTheory.FunPr.ThetaLocalInputs →
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (α β κ : Type) [Fintype α]
    [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ] (ψ : AddChar (AF F) ℂ) (JA : Matrix α α (AE F E))
    (JB : Matrix β β (AE F E)) (d : Darboux (symp (R := AF F) (cA σ) (-1) JA JB) κ)
    (om ω₀ : UG (cA σ) JB →* Module.End ℂ ((κ → AF F) → ℂ)), IsStd ψ →
    IsUSplitting (adeleClass F) ψ d (actB (cA σ)) om →
    (∀ g : UG (cA σ) JB, At (evI F) ((g.1 : Matrix β β (AE F E)) - 1) →
        (∀ φ ∈ schA F κ, ω₀ g φ ∈ schA F κ) ∧
        (∀ w, ∀ φ ∈ schA F κ, ω₀ g (d.rho ψ w φ) = d.rho ψ (actB (cA σ) g w) (ω₀ g φ)) ∧
        ∀ μ : @Measure (κ → AF F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
          ∀ φ ∈ schA F κ, ∫⁻ x, ‖ω₀ g φ x‖ₑ ^ 2 ∂μ = ∫⁻ x, ‖φ x‖ₑ ^ 2 ∂μ) →
    (∀ l ∈ (adeleClass F).adm κ, ∀ φ ∈ schA F κ,
        ContinuousOn (fun g => l (ω₀ g φ)) {g : UG (cA σ) JB | At (evI F) ((g.1 : Matrix β β (AE F E)) - 1)}) →
    ∃ ν : UG (cA σ) JB → ℂ,
      (∀ g : UG (cA σ) JB, At (evI F) ((g.1 : Matrix β β (AE F E)) - 1) → ∀ φ ∈ schA F κ, om g φ = ν g • ω₀ g φ) ∧
      (∀ g h : UG (cA σ) JB, At (evI F) ((g.1 : Matrix β β (AE F E)) - 1) → At (evI F) ((h.1 : Matrix β β (AE F E)) - 1) →
        ν (g * h) = ν g * ν h) ∧
      ContinuousOn ν {g : UG (cA σ) JB | At (evI F) ((g.1 : Matrix β β (AE F E)) - 1)} ∧
      ∀ g : UG (cA σ) JB, At (evI F) ((g.1 : Matrix β β (AE F E)) - 1) → ν g ≠ 0 := by
  first | exact @_root_.GlobalTheory.SplitScalar.metaplectic_splittings_differ_by_character | exact _root_.GlobalTheory.SplitScalar.metaplectic_splittings_differ_by_character | (intros; apply _root_.GlobalTheory.SplitScalar.metaplectic_splittings_differ_by_character <;> assumption)
end
end
