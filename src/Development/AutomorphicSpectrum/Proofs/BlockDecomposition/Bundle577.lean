module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle286
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle570
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle502
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle543
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle569
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.TopoAF
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle509
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.IsTransl
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1784
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1741
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1465
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OneMemGoodCT
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.AffineGLForms.GenSpace
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle571
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankPosOfLeaves
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.EulerFactorLevels.EulerFinOf
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open scoped ENNReal
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology Polynomial
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs GlobalTheory.CompanionTheory.Conc
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.AutomorphicForm

theorem _root_.GlobalTheory.T.uniform_bound_siegel_set : ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) [MeasurableSpace (AdelicGLn.AdelicGL K n)] [BorelSpace (AdelicGLn.AdelicGL K n)] (μ : Measure (AdelicGLn.AdelicGL K n)) [μ.IsHaarMeasure] (ι : Type)
  (f : ι → AdelicGLn.AdelicGL K n → ℂ) (κ : ℕ → ℝ), (∀ i, Continuous (f i)) → UBnd f κ → (∀ r, 0 < r → r < n → κ r < An.rho K n r) →
  ∀ ω : Set (AdelicGLn.AdelicGL K n), IsCompact ω → ω ⊆ (adelicBorel (K := K) (n := n) : Set _) → ∀ (t₀ : ℝ) (η : ℝ≥0∞), 0 < η →
  ∃ Ω : Set (AdelicGLn.AdelicGL K n), IsCompact Ω ∧ ∀ i, ∫⁻ g in An.slab ω t₀ \ Ω, ‖f i g‖ₑ ^ 2 ∂μ ≤ η := by
  first | exact @GlobalTheory.CompanionTheory.Conc.TailU.tail_unif | exact GlobalTheory.CompanionTheory.Conc.TailU.tail_unif | (intros; apply GlobalTheory.CompanionTheory.Conc.TailU.tail_unif <;> assumption)
end

section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.FJE

theorem integral_mul_tsum_unimod {ι X : Type} [Countable ι] [MeasurableSpace X] (ν : Measure X) [IsFiniteMeasure ν]
    {c : ι → X → ℂ} {h : X → ℂ} {a : ι → ℂ} (hc : ∀ i, AEStronglyMeasurable (c i) ν)
    (hc1 : ∀ i x, ‖c i x‖ = 1) (hh : AEStronglyMeasurable h ν) {B : ℝ} (hB : ∀ x, ‖h x‖ ≤ B)
    (ha : Summable fun i => ‖a i‖) :
    ∫ x, h x * ∑' i, c i x * a i ∂ν = ∑' i, (∫ x, h x * c i x ∂ν) * a i := by
  have hbd : ∀ i x, ‖h x * (c i x * a i)‖ ≤ B * ‖a i‖ := fun i x => by
    rw [norm_mul, norm_mul, hc1, one_mul]
    exact mul_le_mul_of_nonneg_right (hB x) (norm_nonneg _)
  have hint : ∀ i, Integrable (fun x => h x * (c i x * a i)) ν := fun i =>
    Integrable.of_bound (hh.mul ((hc i).mul aestronglyMeasurable_const)) (B * ‖a i‖)
      (Eventually.of_forall (hbd i))
  have hsum : Summable fun i => ∫ x, ‖h x * (c i x * a i)‖ ∂ν := by
    refine Summable.of_nonneg_of_le (fun i => integral_nonneg fun x => norm_nonneg _) (fun i => ?_)
      ((ha.mul_left B).mul_left (ν.real Set.univ))
    calc ∫ x, ‖h x * (c i x * a i)‖ ∂ν ≤ ∫ _, B * ‖a i‖ ∂ν :=
          integral_mono (hint i).norm (integrable_const _) (hbd i)
      _ = ν.real Set.univ * (B * ‖a i‖) := by simp [integral_const]
  have key := hasSum_integral_of_summable_integral_norm hint hsum
  have e1 : ∀ x, ∑' i, h x * (c i x * a i) = h x * ∑' i, c i x * a i := fun x => tsum_mul_left
  have e2 : ∀ i, ∫ x, h x * (c i x * a i) ∂ν = (∫ x, h x * c i x ∂ν) * a i := fun i => by
    rw [← integral_mul_const]
    exact integral_congr_ae (Eventually.of_forall fun x => by simp only [mul_assoc])
  simp only [e1, e2] at key
  exact key.tsum_eq.symm

theorem parseval {D : D7} {ρ p : ℕ} (m : Meas D ρ p) (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsCharAF D.host.F ψ)
    (b₀ : HermE D ρ) (hb₀ : b₀.1.det ≠ 0) (a b : Matrix (Fin ρ) (Fin p) D.host.E → ℂ)
    (ha : Summable (fun η => ‖a η‖)) (hb : Summable (fun η => ‖b η‖)) :
    ∫ x in m.𝓕, (∑' η : Matrix (Fin ρ) (Fin p) D.host.E, chv ψ b₀ x (rt η) * a η) *
        conj (∑' ξ : Matrix (Fin ρ) (Fin p) D.host.E, chv ψ b₀ x (rt ξ) * b ξ) ∂m.μ =
      ∑' η : Matrix (Fin ρ) (Fin p) D.host.E, a η * conj (b η) := by
  classical
  obtain ⟨-, hadd, hnorm, hneg, -, hcont⟩ := GlobalTheory.T.heisenberg_character_bilinear_laws (p := p) ψ hψ b₀
  haveI : BorelSpace (Mx D ρ p) := ⟨rfl⟩
  haveI : Countable (Matrix (Fin ρ) (Fin p) D.host.E) :=
    inferInstanceAs (Countable (Fin ρ → Fin p → D.host.E))
  haveI : IsProbabilityMeasure (m.μ.restrict m.𝓕) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact m.hμ.2.2⟩
  have hcm : ∀ η : Matrix (Fin ρ) (Fin p) D.host.E,
      StronglyMeasurable (fun x : Mx D ρ p => chv ψ b₀ x (rt η)) := fun η =>
    (hcont.comp (Continuous.prodMk continuous_id continuous_const)).stronglyMeasurable
  have hcm' : ∀ ξ : Matrix (Fin ρ) (Fin p) D.host.E,
      StronglyMeasurable (fun x : Mx D ρ p => conj (chv ψ b₀ x (rt ξ))) := fun ξ =>
    Complex.continuous_conj.comp_stronglyMeasurable (hcm ξ)
  have hc1 : ∀ (η : Matrix (Fin ρ) (Fin p) D.host.E) (x : Mx D ρ p), ‖chv ψ b₀ x (rt η)‖ = 1 :=
    fun η x => hnorm x _
  have hc1' : ∀ (ξ : Matrix (Fin ρ) (Fin p) D.host.E) (x : Mx D ρ p),
      ‖conj (chv ψ b₀ x (rt ξ))‖ = 1 := fun ξ x => by rw [RCLike.norm_conj]; exact hc1 ξ x
  have horth : ∀ ξ η : Matrix (Fin ρ) (Fin p) D.host.E,
      ∫ x in m.𝓕, conj (chv ψ b₀ x (rt ξ)) * chv ψ b₀ x (rt η) ∂m.μ = if η = ξ then 1 else 0 := by
    intro ξ η
    by_cases h : η = ξ
    · subst h
      have e : ∀ x : Mx D ρ p, conj (chv ψ b₀ x (rt η)) * chv ψ b₀ x (rt η) = 1 := fun x => by
        rw [Complex.conj_mul', hc1]; simp
      simp [e]
    · have e : ∀ x : Mx D ρ p, conj (chv ψ b₀ x (rt ξ)) * chv ψ b₀ x (rt η) =
          chv ψ b₀ x (rt (η - ξ)) := fun x => by
        have hr : (rt (η - ξ) : Mx D ρ p) = rt η + -rt ξ := by
          rw [← sub_eq_add_neg]; exact rat_sub η ξ
        rw [hr, hadd, hneg, mul_comm]
      simp only [e, if_neg h]
      exact GlobalTheory.T.heisenberg_character_integral_vanishes m ψ hψ b₀ hb₀ (η - ξ) (sub_ne_zero.2 h)
  have hs : ∀ x : Mx D ρ p, Summable fun η => chv ψ b₀ x (rt η) * a η := fun x =>
    Summable.of_norm (by simpa only [norm_mul, hc1, one_mul] using ha)
  have hfm : StronglyMeasurable fun x : Mx D ρ p => ∑' η, chv ψ b₀ x (rt η) * a η :=
    tsum_meas (fun η => (hcm η).mul_const _) hs
  have hfB : ∀ x : Mx D ρ p, ‖∑' η, chv ψ b₀ x (rt η) * a η‖ ≤ ∑' η, ‖a η‖ := fun x => by
    have h1 := norm_tsum_le_tsum_norm (f := fun η => chv ψ b₀ x (rt η) * a η)
      (by simpa only [norm_mul, hc1, one_mul] using ha)
    simpa only [norm_mul, hc1, one_mul] using h1
  have hcoef : ∀ ξ : Matrix (Fin ρ) (Fin p) D.host.E,
      ∫ x in m.𝓕, (∑' η, chv ψ b₀ x (rt η) * a η) * conj (chv ψ b₀ x (rt ξ)) ∂m.μ = a ξ := by
    intro ξ
    have h1 := integral_mul_tsum_unimod (m.μ.restrict m.𝓕)
      (c := fun (η : Matrix (Fin ρ) (Fin p) D.host.E) (x : Mx D ρ p) => chv ψ b₀ x (rt η))
      (h := fun x => conj (chv ψ b₀ x (rt ξ))) (a := a) (B := 1)
      (fun η => (hcm η).aestronglyMeasurable) hc1 (hcm' ξ).aestronglyMeasurable
      (fun x => (hc1' ξ x).le) ha
    simp only [horth, ite_mul, one_mul, zero_mul, tsum_ite_eq] at h1
    rw [← h1]
    exact integral_congr_ae (Eventually.of_forall fun x => mul_comm _ _)
  have hconj : ∀ x : Mx D ρ p, conj (∑' ξ, chv ψ b₀ x (rt ξ) * b ξ) =
      ∑' ξ, conj (chv ψ b₀ x (rt ξ)) * conj (b ξ) := fun x => by
    rw [Complex.conj_tsum]; simp only [map_mul]
  have h2 := integral_mul_tsum_unimod (m.μ.restrict m.𝓕)
    (c := fun (ξ : Matrix (Fin ρ) (Fin p) D.host.E) (x : Mx D ρ p) => conj (chv ψ b₀ x (rt ξ)))
    (h := fun x => ∑' η, chv ψ b₀ x (rt η) * a η) (a := fun ξ => conj (b ξ))
    (fun ξ => (hcm' ξ).aestronglyMeasurable) hc1' hfm.aestronglyMeasurable hfB
    (by simpa only [RCLike.norm_conj] using hb)
  simp only [hconj, h2, hcoef]

end GlobalTheory.CompanionTheory.FJE
end
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.G8.Fin GlobalTheory.CompanionTheory.LocalHypotheses
open scoped Classical

noncomputable section

namespace GlobalTheory.CompanionTheory.LocalHypotheses

theorem thetaGL_id_mem {E : Type} [Field E] [NumberField E] (n : ℕ) (w : Pl E) {g : GLw n w}
    (hg : g ∈ GlobalTheory.LFun.KGL w (n := n)) : thetaGL n (RingHom.id _) g ∈ GlobalTheory.LFun.KGL w (n := n) := by
  have hid : GeneralLinearGroup.map (RingHom.id (w.adicCompletion E)) g = g :=
    Units.ext (Matrix.ext fun _ _ => rfl)
  change PhiU n _ * invT n _ (GeneralLinearGroup.map (RingHom.id _) g) * (PhiU n _)⁻¹ ∈ _
  exact mul_mem (mul_mem (GlobalTheory.ThetaSatake.phiU_mem _ n)
    (GlobalTheory.BCT.LocGlue.intst E n w w (RingHom.id _) (fun _ => rfl) g hg))
    (inv_mem (GlobalTheory.ThetaSatake.phiU_mem _ n))

theorem sgP_facts : ∀ (E : Type) [Field E] [NumberField E] (a b : ℕ) (w : Pl E),
    Continuous (sgP a b w) ∧ (∀ g, sgP a b w (sgP a b w g) = g) ∧
      ∀ k ∈ K2 (E := E) a b w, sgP a b w k ∈ K2 (E := E) a b w := by
  intro E _ _ a b w
  refine ⟨?_, ?_, ?_⟩
  · exact (GlobalTheory.LocTwist.continuous_thetaGL a (RingHom.id _) continuous_id).prodMap
      (GlobalTheory.LocTwist.continuous_thetaGL b (RingHom.id _) continuous_id)
  · rintro ⟨g₁, g₂⟩
    exact Prod.ext (GlobalTheory.LocTwist.thetaGL_thetaGL a (RingHom.id _) (fun _ => rfl) g₁)
      (GlobalTheory.LocTwist.thetaGL_thetaGL b (RingHom.id _) (fun _ => rfl) g₂)
  · rintro ⟨k₁, k₂⟩ hk
    exact ⟨thetaGL_id_mem a w hk.1, thetaGL_id_mem b w hk.2⟩

end GlobalTheory.CompanionTheory.LocalHypotheses

end
end

section

open NumberField GlobalTheory.CuspRep MeasureTheory PositivityTheory.Affgl GlobalTheory.CompanionTheory.CTFin

theorem _root_.GlobalTheory.T.constant_term_cofinite_ideal_transfer : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (r s : ℕ) (L : Subgroup (GL (Fin (r + s)) (Af E))), IsOpen (L : Set (GL (Fin (r + s)) (Af E))) → ∀ (W : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] (ρ : Representation ℂ (Kinf E (r + s)) W), GlobalTheory.Published.AutFin.IsContRep ρ → ∀ J : Set (Module.End ℂ (Sm E (r + s))), Cofin J → ∀ J₁ : Set (Module.End ℂ (Sm E r)), Cofin J₁ → (∀ F : Sm E (r + s), (∀ (x : BlockIx (r + s) r → Ad E) (g : GA E (r + s)), F.1 (unip x * g) = F.1 g) → (∀ z ∈ J, z F = 0) → ∀ G : Sm E r, (∀ m, G.1 m = F.1 (lev (Ad E) r s (m, 1))) → ∀ z ∈ J₁, z G = 0) → ∀ (t : GL (Fin (r + s)) (Af E)) (κ : Kinf E (r + s)), ∃ (L₁ : Subgroup (GL (Fin r) (Af E))) (ρ₁ : Representation ℂ (Kinf E r) W), IsOpen (L₁ : Set (GL (Fin r) (Af E))) ∧ GlobalTheory.Published.AutFin.IsContRep ρ₁ ∧ ∀ F ∈ goodCT L ρ J, ∀ m₂ : GA E s, ∃ G ∈ genSpace L₁ ρ₁ J₁, ∀ m₁ : GA E r, G.1 m₁ = F.1 (lev (Ad E) r s (m₁, m₂) * finGL E (r + s) t * infGL E (r + s) (Unitary.toUnits κ)) := by
  first | exact @GlobalTheory.CompanionTheory.CTFin.Slice1.slice_mem_genSpace | exact GlobalTheory.CompanionTheory.CTFin.Slice1.slice_mem_genSpace | (intros; apply GlobalTheory.CompanionTheory.CTFin.Slice1.slice_mem_genSpace <;> assumption)
end

section

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation
open GlobalTheory.CompanionTheory.EGlue

namespace GlobalTheory.CompanionTheory.EGlue.ConvStripProof

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def nodeRank : {N : ℕ} → Tr E N → Option ℕ
  | _, .leaf _ _ => none
  | _, @Tr.node _ _ _ _ r _ _ _ => some r

theorem nodeRank_heq {N M : ℕ} (u : Tr E N) (v : Tr E M) (h : N = M) (hh : HEq u v) :
    nodeRank u = nodeRank v := by
  subst h
  rw [eq_of_heq hh]

theorem twists_length_strip : ∀ {N : ℕ} (u : Tr E N), u.strip.twists.length = u.twists.length := by
  intro N u
  induction u with
  | leaf V z => rfl
  | node t₁ t₂ i₁ i₂ => simp [Tr.strip, Tr.twists, i₁, i₂]

theorem twists_length_eq {N : ℕ} {u v : Tr E N} (h : u.strip = v.strip) :
    u.twists.length = v.twists.length := by
  rw [← twists_length_strip u, h, twists_length_strip]

theorem leaf_of_strip {N : ℕ} (u : Tr E N) (V : Submodule ℂ (Sm E N)) (w : ℂ)
    (h : u.strip = .leaf V w) : ∃ z, u = .leaf V z := by
  revert V w h
  cases u with
  | leaf V' z =>
    intro V w h
    simp only [Tr.strip] at h
    injection h with _ h₁
    exact ⟨z, by rw [h₁]⟩
  | node a b =>
    intro V w h
    have := congrArg nodeRank h
    simp [Tr.strip, nodeRank] at this

theorem node_of_strip_eq : ∀ {N : ℕ} (u : Tr E N) {r s : ℕ} (_ : N = r + s) (x : Tr E r) (y : Tr E s),
    HEq u.strip (Tr.node x y) →
    ∃ (a : Tr E r) (b : Tr E s), HEq u (Tr.node a b) ∧ a.strip = x ∧ b.strip = y := by
  intro N u
  cases u with
  | leaf V z =>
    intro r s hN x y h
    subst hN
    have := congrArg nodeRank (eq_of_heq h)
    simp [Tr.strip, nodeRank] at this
  | @node r' s' a b =>
    intro r s hN x y h
    have h₁ : r' = r := by
      have := nodeRank_heq _ _ hN h
      simpa [Tr.strip, nodeRank] using this
    subst h₁
    have h₂ : s' = s := by omega
    subst h₂
    have h₃ := eq_of_heq h
    simp only [Tr.strip] at h₃
    injection h₃ with _ _ e₁ e₂
    exact ⟨a, b, HEq.rfl, e₁, e₂⟩

theorem node_of_strip {r s : ℕ} (u : Tr E (r + s)) (x : Tr E r) (y : Tr E s)
    (h : u.strip = Tr.node x y) :
    ∃ (a : Tr E r) (b : Tr E s), u = Tr.node a b ∧ a.strip = x ∧ b.strip = y := by
  obtain ⟨a, b, e, h₁, h₂⟩ := node_of_strip_eq u rfl x y (heq_of_eq h)
  exact ⟨a, b, eq_of_heq e, h₁, h₂⟩

theorem getD_append_left (A B : List ℂ) {i : ℕ} (h : i < A.length) :
    (A ++ B).getD i 0 = A.getD i 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_append_right (A B : List ℂ) (i : ℕ) :
    (A ++ B).getD (A.length + i) 0 = B.getD i 0 := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left]

theorem getD_of_le (A : List ℂ) {i : ℕ} (h : A.length ≤ i) : A.getD i 0 = 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]

theorem conv_forward {N : ℕ} {t : ℕ → Tr E N} {s : Tr E N} (h : Conv t s) :
    (∀ k, (t k).strip = s.strip) ∧
      ∀ i, Tendsto (fun k => ((t k).twists.getD i 0)) atTop (𝓝 (s.twists.getD i 0)) := by
  induction h with
  | leaf V z z₀ h =>
    refine ⟨fun k => rfl, fun i => ?_⟩
    cases i with
    | zero => simpa [Tr.twists] using h
    | succ i => simp [Tr.twists]
  | @node r s t₁ t₂ s₁ s₂ _ _ i₁ i₂ =>
    refine ⟨fun k => ?_, fun i => ?_⟩
    · simp only [Tr.strip, i₁.1 k, i₂.1 k]
    · have hl : ∀ k, (t₁ k).twists.length = s₁.twists.length := fun k => twists_length_eq (i₁.1 k)
      simp only [Tr.twists]
      by_cases hi : i < s₁.twists.length
      · rw [getD_append_left _ _ hi]
        have : (fun k => ((t₁ k).twists ++ (t₂ k).twists).getD i 0) = fun k => (t₁ k).twists.getD i 0 :=
          funext fun k => getD_append_left _ _ (by rw [hl k]; exact hi)
        rw [this]
        exact i₁.2 i
      · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le (not_lt.mp hi)
        rw [getD_append_right]
        have : (fun k => ((t₁ k).twists ++ (t₂ k).twists).getD (s₁.twists.length + j) 0) =
            fun k => (t₂ k).twists.getD j 0 :=
          funext fun k => by rw [← hl k, getD_append_right]
        rw [this]
        exact i₂.2 j

theorem conv_backward : ∀ {N : ℕ} (s : Tr E N) (t : ℕ → Tr E N), (∀ k, (t k).strip = s.strip) →
    (∀ i, Tendsto (fun k => ((t k).twists.getD i 0)) atTop (𝓝 (s.twists.getD i 0))) → Conv t s := by
  intro N s
  induction s with
  | leaf V z₀ =>
    intro t hs ht
    choose z hz using fun k => leaf_of_strip (t k) V 0 (hs k)
    obtain rfl : t = fun k => .leaf V (z k) := funext hz
    exact Conv.leaf V z z₀ (by simpa [Tr.twists] using ht 0)
  | @node r s s₁ s₂ i₁ i₂ =>
    intro t hs ht
    choose a b hab ha hb using fun k => node_of_strip (t k) s₁.strip s₂.strip (hs k)
    obtain rfl : t = fun k => .node (a k) (b k) := funext hab
    have hl : ∀ k, (a k).twists.length = s₁.twists.length := fun k => twists_length_eq (ha k)
    simp only [Tr.twists] at ht
    refine Conv.node (i₁ a ha fun i => ?_) (i₂ b hb fun i => ?_)
    · by_cases hi : i < s₁.twists.length
      · have h := ht i
        rw [getD_append_left _ _ hi] at h
        have e : (fun k => ((a k).twists ++ (b k).twists).getD i 0) = fun k => (a k).twists.getD i 0 :=
          funext fun k => getD_append_left _ _ (by rw [hl k]; exact hi)
        rwa [e] at h
      · have e : (fun k => (a k).twists.getD i 0) = fun _ => (0 : ℂ) :=
          funext fun k => getD_of_le _ (by rw [hl k]; exact not_lt.mp hi)
        rw [e, getD_of_le _ (not_lt.mp hi)]
        exact tendsto_const_nhds
    · have h := ht (s₁.twists.length + i)
      rw [getD_append_right] at h
      have e : (fun k => ((a k).twists ++ (b k).twists).getD (s₁.twists.length + i) 0) =
          fun k => (b k).twists.getD i 0 :=
        funext fun k => by rw [← hl k, getD_append_right]
      rwa [e] at h

theorem convStrip : ConvStrip := fun _ _ _ _ _ t s =>
  ⟨conv_forward, fun h => conv_backward s t h.1 h.2⟩

end GlobalTheory.CompanionTheory.EGlue.ConvStripProof

end
end

section

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation

namespace GlobalTheory.CompanionTheory.EGlue

theorem allLeaves_mono {E : Type} [Field E] [NumberField E] [IsCMField E]
    {P Q : ∀ M : ℕ, Submodule ℂ (Sm E M) → Prop} (hPQ : ∀ M V, P M V → Q M V) :
    ∀ {N : ℕ} {t : Tr E N}, t.AllLeaves P → t.AllLeaves Q := by
  intro N t
  induction t with
  | leaf V z => exact fun h => hPQ _ _ h
  | node t₁ t₂ i₁ i₂ => exact fun h => ⟨i₁ h.1, i₂ h.2⟩

theorem factorStep_holds : FactorStep := by
  set_option synthInstance.maxHeartbeats 400000 in
    intro h4 E _ _ _ N W hW
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · refine ⟨fun _ => ∅, fun M => ⟨Set.finite_empty, by simp⟩, fun K _ =>
        ⟨fun _ => ∅, fun M => ⟨Set.finite_empty, by simp⟩, ?_⟩⟩
      intro U _ _ _ _ _ _ hU
      obtain ⟨ψ, hψ, hne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hU
      refine ⟨.leaf ⊤ 0, LinearMap.id, trivial, Or.inl ⟨rfl, rfl, rfl⟩, Or.inl rfl,
        fun _ _ _ => rfl, fun χ _ => ?_, ψ, hψ, hne⟩
      exact ⟨(mulChi 0 (Model.absC E 0)).symm χ, trivial, by simp⟩
    · obtain ⟨Ω, hΩ, h⟩ := h4 E N W hW
      refine ⟨Ω, hΩ, fun K hK => ?_⟩
      obtain ⟨Θ, hΘ, h'⟩ := h K hK
      refine ⟨Θ, hΘ, ?_⟩
      intro U hs ha hg hn hc hi hU
      obtain ⟨t, T, hG, hL, he, hm, hne⟩ := h' U hN hs ha hg hn hc hi hU
      exact ⟨t, T, red_of_leaves hL, hG, allLeaves_mono (fun M V h => Or.inr h.2) hL, he, hm, hne⟩

end GlobalTheory.CompanionTheory.EGlue

end
end

section

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation

namespace GlobalTheory.CompanionTheory.EGlue

theorem typeB_of_mem_span {E : Type} [Field E] [NumberField E] [IsCMField E] {N : ℕ}
    {K : Subgroup (GL (Fin N) (Af E))} {W : Submodule ℂ (Kinf E N → ℂ)} {S : Set (Sm E N)}
    (hS : ∀ φ ∈ S, TypeB K W φ) {φ : Sm E N} (hφ : φ ∈ Submodule.span ℂ S) : TypeB K W φ := by
  induction hφ using Submodule.span_induction with
  | mem x hx => exact hS x hx
  | zero => exact ⟨fun _ _ _ => rfl, fun _ => W.zero_mem⟩
  | add x y _ _ hx hy =>
    refine ⟨fun u hu g => ?_, fun g => W.add_mem (hx.2 g) (hy.2 g)⟩
    show x.1 (g * finGL E N u) + y.1 (g * finGL E N u) = x.1 g + y.1 g
    rw [hx.1 u hu g, hy.1 u hu g]
  | smul c x _ hx =>
    refine ⟨fun u hu g => ?_, fun g => W.smul_mem c (hx.2 g)⟩
    show c • x.1 (g * finGL E N u) = c • x.1 g
    rw [hx.1 u hu g]

theorem hullGen : HullGen := by
  intro E _ _ _ N K W S hS hfd
  have hst : _root_.GlobalTheory.CuspRep.IsStable (hull S) := fun o φ hφ =>
    Submodule.mem_sInf.2 fun U hU => hU.2 o φ (Submodule.mem_sInf.1 hφ U hU)
  refine ⟨hst, ?_⟩
  have hsub : S ⊆ hull S := fun φ hφ => Submodule.mem_sInf.2 fun U hU => hU.1 hφ
  obtain ⟨t, ht⟩ := (Submodule.fg_iff_finiteDimensional _).2 hfd
  have htS : ∀ φ ∈ t, φ ∈ Submodule.span ℂ S := fun φ hφ => ht ▸ Submodule.subset_span hφ
  refine ⟨t, fun φ hφ => typeB_of_mem_span hS (htS φ hφ), fun φ hφ => ?_, fun U' hU' htU => ?_⟩
  · exact (Submodule.span_le.2 hsub) (htS φ hφ)
  · refine sInf_le ⟨?_, hU'⟩
    have h : Submodule.span ℂ S ≤ U' := ht ▸ Submodule.span_le.2 htU
    exact Submodule.subset_span.trans h

end GlobalTheory.CompanionTheory.EGlue

end
end

section

open GlobalTheory.CompanionTheory.EGlue

noncomputable section

open GlobalTheory.CuspRep GlobalTheory.UnitaryBC

namespace GlobalTheory.CompanionTheory.EGlue.Gl0

theorem topInf : GlobalTheory.CompanionTheory.EGlue.TopInf := by
  intro E _ _ _ τ
  refine ⟨rfl, fun u φ _ => ?_⟩
  simp [cap, Formalism.REAL.qdet, Formalism.REAL.qminor, Formalism.REAL.Tm]

end GlobalTheory.CompanionTheory.EGlue.Gl0

end
end
