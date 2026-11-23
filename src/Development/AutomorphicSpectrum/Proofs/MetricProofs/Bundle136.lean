module

public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle113
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle116
import Development.AutomorphicSpectrum.Proofs.MetricProofs.LogResolutionFunctorialHolomorphic
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle124
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle090
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.ColFlags
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle125
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle126
public import GroundTheory.PAdicHodge.Bundle004
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle128
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle127
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
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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
import Mathlib.Topology.Sheaves.Init
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle013
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan
open GlobalTheory.CompanionTheory.Ar.PB.PFl

theorem _root_.GlobalTheory.T.pMat_stepCols_entry : ∀ (Ψ : Type) (N j : ℕ) (keep : Ψ × Fin N → Prop) (q : PIdx j keep), j ≤ N → keep (q.1.1.1, pStep j keep q.1.1.1 q.1.1.2.2) ∧ IsProperStep N j (pStep j keep q.1.1.1 q.1.1.2.2) ∧ q.1.1.2.2 ∈ stepCols N j (pStep j keep q.1.1.1 q.1.1.2.2) ∧ q.1.1.2.1 ∉ stepCols N j (pStep j keep q.1.1.1 q.1.1.2.2) ∧ ∀ c : PIdx j keep → ℂ, pMat keep c q.1.1.1 q.1.1.2.1 q.1.1.2.2 = c q ∧ ∀ x ∈ stepCols N j (pStep j keep q.1.1.1 q.1.1.2.2), x ≠ q.1.1.2.2 → pMat keep c q.1.1.1 x q.1.1.2.2 = 0 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.PFl.SmallStep.pStep_reads | exact GlobalTheory.CompanionTheory.Ar.PB.PFl.SmallStep.pStep_reads | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.PFl.SmallStep.pStep_reads <;> assumption)
end

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan
open GlobalTheory.CompanionTheory.Ar.PB.PFl

theorem _root_.GlobalTheory.T.blockMap_frame_restriction : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (keep : Ψ × Fin N → Prop) (Kk : Type) [Fintype Kk] (ιk : Kk → Type) [∀ k, Fintype (ιk k)] (κ : Kk → K) (v : (Σ k, ιk k) → (Σ k, ι k)), IsBlockMap κ v → (∀ k, k ∈ Set.range κ ↔ ((∀ p, M.blk p ≠ some k) ∨ ∃ p, keep p ∧ M.blk p = some k)) → (∀ z ∈ mcPts (mCoordIdeal (y ∘ v)), pBase M v z ∈ mcPts (mCoordIdeal M.x)) ∧ ∀ z z' : (Σ k, ιk k) → ℂ, SameOrbit z z' → SameOrbit (pBase M v z) (pBase M v z') := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.PFl.PtsBase.main | exact GlobalTheory.CompanionTheory.Ar.PB.PFl.PtsBase.main | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.PFl.PtsBase.main <;> assumption)
end

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan
open GlobalTheory.CompanionTheory.Ar.PB.PFl

theorem _root_.GlobalTheory.T.minorIJ_lowerUni_swap : ∀ (N : ℕ) (X : Matrix (Fin N) (Fin N) ℂ) (S : Finset (Fin N)) (a b : Fin N), IsLowerUni X → a ∉ S → b ∈ S → b < a → (∀ c ∈ S, c ≠ b → X c b = 0) → minorIJ X (insert a (S.erase b)) S = pSgn S a b * X a b ∧ pSgn S a b ≠ 0 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.PFl.MatRead.minor_replace | exact GlobalTheory.CompanionTheory.Ar.PB.PFl.MatRead.minor_replace | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.PFl.MatRead.minor_replace <;> assumption)
end

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WMan.Gen

open GlobalTheory.CompanionTheory.Ar.Cmp.SncRes

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {P : Ideal (MRing ι)} {e : ℕ}

theorem analyticAt_eval {E σ : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {g : E → σ → ℂ} {w₀ : E}
    (hg : ∀ q, AnalyticAt ℂ (fun w => g w q) w₀) (f : MvPolynomial σ ℂ) :
    AnalyticAt ℂ (fun w => eval (g w) f) w₀ := by
  induction f using MvPolynomial.induction_on with
  | C a => simpa using analyticAt_const
  | add p q hp hq =>
    refine (hp.add hq).congr (Filter.Eventually.of_forall fun w => ?_)
    simp
  | mul_X p n hp =>
    refine (hp.mul (hg n)).congr (Filter.Eventually.of_forall fun w => ?_)
    simp

section Overlap

variable (hP : IsMultiHomogIdeal P) (C₁ C₂ : OrbitChart P e) (x₁ x₂ : PtsOf P)
include hP

theorem mem_O_of_mem_srcOf {w : Fin e → ℂ} (hw : w ∈ C₁.D) (h : clsT x₁ (C₁.φ w) ∈ srcOf C₂) : C₁.φ w ∈ C₂.O := by
  have h' : rep (cls (C₁.φ w) (C₁.mem w hw)) ∈ C₂.O := by
    rw [← clsT_of_mem x₁ (C₁.mem w hw)]
    exact h
  exact mem_O_of_orbit C₂ hP h' (Proj.orbit_symm (rep_cls_orbit _ _)) (rep_mem_mcPts _)

theorem rho_clsT {w : Fin e → ℂ} (hw : w ∈ C₁.D) (h : clsT x₁ (C₁.φ w) ∈ srcOf C₂) :
    C₂.ρ (rep (clsT x₁ (C₁.φ w))) = C₂.ρ (C₁.φ w) := by
  have hO := mem_O_of_mem_srcOf hP C₁ C₂ x₁ hw h
  refine C₂.ρ_orbit _ hO _ h ?_
  rw [clsT_of_mem x₁ (C₁.mem w hw)]
  exact rep_cls_orbit _ _

theorem isOpen_overlap :
    IsOpen ((orbChart hP C₁ x₁).target ∩ (orbChart hP C₁ x₁).symm ⁻¹' srcOf C₂) :=
  (orbChart hP C₁ x₁).isOpen_inter_preimage_symm (isOpen_srcOf hP C₂)

theorem analytic_transition :
    AnalyticOnNhd ℂ (orbChart hP C₂ x₂ ∘ (orbChart hP C₁ x₁).symm)
      ((orbChart hP C₁ x₁).target ∩ (orbChart hP C₁ x₁).symm ⁻¹' (orbChart hP C₂ x₂).source) := by
  have h1 : AnalyticOnNhd ℂ (fun w => C₂.ρ (C₁.φ w))
      ((orbChart hP C₁ x₁).target ∩ (orbChart hP C₁ x₁).symm ⁻¹' srcOf C₂) :=
    (GlobalTheory.T.orbit_chart_transition_analytic K ι P e C₁ C₂).mono fun w hw => ⟨hw.1, mem_O_of_mem_srcOf hP C₁ C₂ x₁ hw.1 hw.2⟩
  exact h1.congr (isOpen_overlap hP C₁ C₂ x₁) fun w hw => (rho_clsT hP C₁ C₂ x₁ hw.1 hw.2).symm

theorem analytic_lift (p : Σ k, ι k) :
    AnalyticOnNhd ℂ ((fun y : PtsOf P => C₂.φ (C₂.ρ (rep y)) p) ∘ (orbChart hP C₁ x₁).symm)
      ((orbChart hP C₁ x₁).target ∩ (orbChart hP C₁ x₁).symm ⁻¹' srcOf C₂) := by
  have h1 : AnalyticOnNhd ℂ (fun w => C₂.φ (C₂.ρ (C₁.φ w)) p)
      ((orbChart hP C₁ x₁).target ∩ (orbChart hP C₁ x₁).symm ⁻¹' srcOf C₂) := fun w hw => by
    have hO := mem_O_of_mem_srcOf hP C₁ C₂ x₁ hw.1 hw.2
    exact AnalyticAt.comp (g := fun v => C₂.φ v p) (f := fun w => C₂.ρ (C₁.φ w))
      (C₂.holo p _ (C₂.ρ_mem _ hO)) (GlobalTheory.T.orbit_chart_transition_analytic K ι P e C₁ C₂ w ⟨hw.1, hO⟩)
  refine h1.congr (isOpen_overlap hP C₁ C₂ x₁) fun w hw => ?_
  have e1 : C₂.ρ (rep (clsT x₁ (C₁.φ w))) = C₂.ρ (C₁.φ w) := rho_clsT hP C₁ C₂ x₁ hw.1 hw.2
  show C₂.φ (C₂.ρ (C₁.φ w)) p = C₂.φ (C₂.ρ (rep (clsT x₁ (C₁.φ w)))) p
  rw [e1]

theorem immersion_lift {x : PtsOf P} (hx₂ : x ∈ srcOf C₂) (hx₁ : x ∈ srcOf C₁) (p : (k : K) → ι k)
    (hp : ∀ k, C₂.φ (C₂.ρ (rep x)) ⟨k, p k⟩ ≠ 0) :
    (fderiv ℂ (fun y => affCoord p (C₂.φ (C₂.ρ (rep ((orbChart hP C₁ x₁).symm y)))))
      (orbChart hP C₁ x₁ x)).ker = ⊥ := by
  set ψ := orbChart hP C₁ x₁ with hψ
  have hw₀ : ψ x ∈ ψ.target := ψ.map_source hx₁
  have hsym : ψ.symm (ψ x) = x := ψ.left_inv hx₁
  have hV : ψ.target ∩ ψ.symm ⁻¹' srcOf C₂ ∈ 𝓝 (ψ x) :=
    (isOpen_overlap hP C₁ C₂ x₁).mem_nhds ⟨hw₀, by rw [Set.mem_preimage, hsym]; exact hx₂⟩
  have heq : (fun y => affCoord p (C₂.φ (C₂.ρ (rep (ψ.symm y))))) =ᶠ[𝓝 (ψ x)]
      fun y => affCoord p (C₁.φ y) := by
    filter_upwards [hV] with w hw
    have hm := C₁.mem w hw.1
    have h1 : SameOrbit (rep (ψ.symm w)) (C₁.φ w) := by
      show SameOrbit (rep (clsT x₁ (C₁.φ w))) (C₁.φ w)
      rw [clsT_of_mem x₁ hm]
      exact rep_cls_orbit _ hm
    exact Proj.affCoord_eq (Proj.orbit_trans (C₂.φ_ρ _ hw.2) h1) p
  rw [heq.fderiv_eq]
  have ho : SameOrbit (C₂.φ (C₂.ρ (rep x))) (C₁.φ (ψ x)) :=
    Proj.orbit_trans (C₂.φ_ρ _ hx₂) (Proj.orbit_symm (C₁.φ_ρ _ hx₁))
  exact C₁.immersion _ hw₀ p fun k => Proj.orbit_ne ho (hp k)

end Overlap

def atlasOf (hP : IsMultiHomogIdeal P) (Cx : PtsOf P → OrbitChart P e) (t : Finset (PtsOf P))
    (hcov : ∀ x, ∃ y ∈ t, x ∈ srcOf (Cx y)) : FinHolAtlas e (PtsOf P) where
  n := t.card
  chart j := orbChart hP (Cx (t.equivFin.symm j)) (t.equivFin.symm j)
  cover x := by
    obtain ⟨y, hy, hx⟩ := hcov x
    refine ⟨t.equivFin ⟨y, hy⟩, ?_⟩
    show x ∈ srcOf (Cx (t.equivFin.symm (t.equivFin ⟨y, hy⟩)))
    rw [Equiv.symm_apply_apply]
    exact hx
  holo j k := analytic_transition hP _ _ _ _

theorem isCompat_orbChart (hP : IsMultiHomogIdeal P) (Cx : PtsOf P → OrbitChart P e) (t : Finset (PtsOf P))
    (hcov : ∀ x, ∃ y ∈ t, x ∈ srcOf (Cx y)) (C : OrbitChart P e) (x₀ : PtsOf P) :
    IsCompatChart (atlasOf hP Cx t hcov) (orbChart hP C x₀) := fun _ =>
  ⟨analytic_transition hP _ _ _ _, analytic_transition hP _ _ _ _⟩

theorem holoOn_eval (hP : IsMultiHomogIdeal P) (Cx : PtsOf P → OrbitChart P e) (t : Finset (PtsOf P))
    (hcov : ∀ x, ∃ y ∈ t, x ∈ srcOf (Cx y)) (C : OrbitChart P e) (f : MvPolynomial (Σ k, ι k) ℂ) :
    (atlasOf hP Cx t hcov).HoloOn (srcOf C) (fun y => eval (C.φ (C.ρ (rep y))) f) := fun j w hw =>
  analyticAt_eval (g := fun w => C.φ (C.ρ (rep (((atlasOf hP Cx t hcov).chart j).symm w))))
    (fun q => analytic_lift hP _ C _ q w hw) f

def resOf (hP : IsMultiHomogIdeal P) (hnd : ¬ (⊤ : Ideal (MRing ι)) ≤ P) (Cx : PtsOf P → OrbitChart P e)
    (hCx : ∀ x, x ∈ srcOf (Cx x)) (t : Finset (PtsOf P)) (hcov : ∀ x, ∃ y ∈ t, x ∈ srcOf (Cx y)) :
    AnLogRes P ⊤ e where
  homog := ⟨{1}, fun f hf => ⟨0, by
    rw [Set.mem_singleton_iff.1 hf]
    intro m hm k
    have hm0 : m = 0 := by
      rw [MvPolynomial.support_one] at hm
      simpa using hm
    simp [hm0]⟩, by simp⟩
  nondeg := hnd
  X := PtsOf P
  top := inferInstance
  compact := Top.compactSpace_pts (isMultiHomogIdeal_pC hP)
  t2 := inferInstance
  A := atlasOf hP Cx t hcov
  U x := srcOf (Cx x)
  isOpen_U x := isOpen_srcOf hP _
  mem_U := hCx
  lift x y := (Cx x).φ ((Cx x).ρ (rep y))
  holo x p j := analytic_lift hP _ _ _ p
  mem x y hy := (Cx x).mem _ ((Cx x).ρ_mem _ hy)
  compat x x' y hy := Proj.orbit_trans ((Cx x).φ_ρ _ hy.1) (Proj.orbit_symm ((Cx x').φ_ρ _ hy.2))
  surj z hz _ := ⟨cls z hz, Proj.orbit_trans ((Cx _).φ_ρ _ (hCx _)) (rep_cls_orbit z hz)⟩
  inj x x' _ h := pts_eq_of_orbit (Proj.orbit_trans (Proj.orbit_symm ((Cx x).φ_ρ _ (hCx x)))
    (Proj.orbit_trans h ((Cx x').φ_ρ _ (hCx x'))))
  immersion x _ p hp j hj := immersion_lift hP _ (Cx x) _ (hCx x) hj p hp
  snc f a _ _ hz := ⟨0, Fin.elim0, Fin.elim0, fun x => ⟨orbChart hP (Cx x) x, isCompat_orbChart hP Cx t hcov _ _,
    hCx x, subset_rfl, Fin.elim0, fun k => k.elim0, fun k => k.elim0,
    fun y => eval ((Cx x).φ ((Cx x).ρ (rep y))) (map (Int.castRingHom ℂ) f),
    holoOn_eval hP Cx t hcov (Cx x) _,
    fun y hy h0 => Proj.not_mem_mcPts_top _ (hz _ ((Cx x).mem _ ((Cx x).ρ_mem _ hy)) h0),
    fun y _ => by simp⟩⟩
  null j := by
    have : {x : PtsOf P | (Cx x).φ ((Cx x).ρ (rep x)) ∈ mcPts (⊤ : Ideal (MRing ι))} = ∅ :=
      Set.eq_empty_of_forall_notMem fun x => Proj.not_mem_mcPts_top _
    rw [this]
    simp

theorem exists_anLogRes_of_orbitCharts : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (e : ℕ), Nonempty K → IsMultiHomogIdeal P → ¬ (⊤ : Ideal (MRing ι)) ≤ P → (∀ z ∈ mcPts P, ∃ C : OrbitChart P e, z ∈ C.O) → ∃ R : AnLogRes P ⊤ e, ∀ C : OrbitChart P e, (mcPts P).Nonempty → ∃ ψ : OpenPartialHomeomorph R.X (Fin e → ℂ), IsCompatChart R.A ψ ∧ ψ.target = C.D ∧ (∀ x, x ∈ ψ.source ↔ R.lift x x ∈ C.O) ∧ ∀ x ∈ ψ.source, SameOrbit (C.φ (ψ x)) (R.lift x x) := by
  intro K _ ι _ P e _ hP hnd hcov
  have h' : ∀ x : PtsOf P, ∃ C : OrbitChart P e, x ∈ srcOf C := fun x => hcov _ (rep_mem_mcPts x)
  choose Cx hCx using h'
  haveI : CompactSpace (PtsOf P) := Top.compactSpace_pts (isMultiHomogIdeal_pC hP)
  obtain ⟨t, ht⟩ := isCompact_univ.elim_nhds_subcover (fun x => srcOf (Cx x))
    (fun x _ => (isOpen_srcOf hP _).mem_nhds (hCx x))
  have hc : ∀ x, ∃ y ∈ t, x ∈ srcOf (Cx y) := fun x => by
    simpa using ht.2 (Set.mem_univ x)
  refine ⟨resOf hP hnd Cx hCx t hc, fun C hne => ?_⟩
  obtain ⟨z, hz⟩ := hne
  have ho : ∀ x : PtsOf P, SameOrbit ((Cx x).φ ((Cx x).ρ (rep x))) (rep x) := fun x => (Cx x).φ_ρ _ (hCx x)
  have hm : ∀ x : PtsOf P, (Cx x).φ ((Cx x).ρ (rep x)) ∈ mcPts P := fun x => (Cx x).mem _ ((Cx x).ρ_mem _ (hCx x))
  refine ⟨orbChart hP C (cls z hz), isCompat_orbChart hP Cx t hc C _, rfl, fun x => ?_, fun x hx => ?_⟩
  · exact ⟨fun h => mem_O_of_orbit C hP h (ho x) (rep_mem_mcPts x),
      fun h => mem_O_of_orbit C hP h (Proj.orbit_symm (ho x)) (hm x)⟩
  · exact Proj.orbit_trans (C.φ_ρ _ hx) (Proj.orbit_symm (ho x))

end GlobalTheory.CompanionTheory.Ar.PB.WMan.Gen
end
end

section

open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun GlobalTheory.CompanionTheory.Ar.PB.FMX.Frm

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.FMX.Frm.Inv

variable {Ψ : Type} {p q : ℕ} {Ω : Type} [Field Ω] {n : Ψ ⊕ Ψ → ℕ}

theorem bExt_posOf (B : ∀ s, Matrix (Fin (rk Ψ p q s)) (Fin (n s)) Ω) (s : Ψ ⊕ Ψ)
    (l : Fin (rk Ψ p q s)) (j : Fin (n s)) : bExt B s (posOf p q s l) j = B s l j := by
  have hinj := (BlockEmbeddings.posOf_strictMono (Ψ := Ψ) (p := p) (q := q) s).injective
  unfold bExt
  rw [Finset.sum_eq_single l]
  · rw [if_pos rfl]
  · intro b _ hb
    rw [if_neg fun h => hb (hinj h)]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem aExt_posOf (C : ∀ s, Matrix (Fin (n s)) (Fin (rk Ψ p q s)) Ω) (s : Ψ ⊕ Ψ)
    (j : Fin (n s)) (l : Fin (rk Ψ p q s)) : aExt C s j (posOf p q s l) = C s j l := by
  have hinj := (BlockEmbeddings.posOf_strictMono (Ψ := Ψ) (p := p) (q := q) s).injective
  unfold aExt
  rw [Finset.sum_eq_single l]
  · rw [if_pos rfl]
  · intro b _ hb
    rw [if_neg fun h => hb (hinj h)]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem aExt_of_forall_ne (C : ∀ s, Matrix (Fin (n s)) (Fin (rk Ψ p q s)) Ω) (s : Ψ ⊕ Ψ)
    (j : Fin (n s)) {b : Fin (p + q)} (h : ∀ l, posOf p q s l ≠ b) : aExt C s j b = 0 :=
  Finset.sum_eq_zero fun l _ => if_neg (h l)

theorem bExt_mul_aExt_row (C : ∀ s, Matrix (Fin (n s)) (Fin (rk Ψ p q s)) Ω)
    (B : ∀ s, Matrix (Fin (rk Ψ p q s)) (Fin (n s)) Ω) (hBC : ∀ s, B s * C s = 1) (s : Ψ ⊕ Ψ)
    (l : Fin (rk Ψ p q s)) (b : Fin (p + q)) :
    (bExt B s * aExt C s) (posOf p q s l) b = (1 : Matrix (Fin (p + q)) (Fin (p + q)) Ω) (posOf p q s l) b := by
  have hinj := (BlockEmbeddings.posOf_strictMono (Ψ := Ψ) (p := p) (q := q) s).injective
  rw [Matrix.mul_apply]
  simp only [bExt_posOf]
  by_cases hb : ∃ l', posOf p q s l' = b
  · obtain ⟨l', rfl⟩ := hb
    simp only [aExt_posOf]
    have h := congrFun (congrFun (hBC s) l) l'
    rw [Matrix.mul_apply] at h
    rw [h]
    by_cases e : l = l'
    · subst e
      simp
    · rw [Matrix.one_apply_ne e, Matrix.one_apply_ne fun h' => e (hinj h')]
  · have hb' : ∀ l', posOf p q s l' ≠ b := fun l' h' => hb ⟨l', h'⟩
    simp only [aExt_of_forall_ne C s _ hb', mul_zero, Finset.sum_const_zero]
    rw [Matrix.one_apply_ne (hb' l)]

theorem sum_strictMono_eq {M : Type} [AddCommMonoid M] {d m : ℕ} (f : (Fin d → Fin m) → M)
    (hf : ∀ J, ¬ StrictMono J → f J = 0) :
    ∑ J, f J = ∑ s : GroundTheory.PAdicHodge.KSubset m d, f s.emb := by
  classical
  symm
  refine Fintype.sum_of_injective (fun s : GroundTheory.PAdicHodge.KSubset m d => (s.emb : Fin d → Fin m))
    ?_ _ _ ?_ fun _ => rfl
  · intro s s' h
    have h' : Set.range s.emb = Set.range s'.emb := congrArg Set.range h
    rw [GroundTheory.PAdicHodge.KSubset.range_emb, GroundTheory.PAdicHodge.KSubset.range_emb] at h'
    exact Subtype.ext (Finset.coe_injective h')
  · intro J hJ
    refine hf J fun hm => hJ ?_
    have hc : (Finset.univ.image J).card = d := by
      rw [Finset.card_image_of_injective _ hm.injective]
      simp
    refine ⟨⟨Finset.univ.image J, hc⟩, ?_⟩
    exact (Finset.orderEmbOfFin_unique hc (fun x => by simp) hm).symm

theorem sum_sMin_mul_cMin : ∀ {Ψ : Type} {p q : ℕ} {Ω : Type} [Field Ω] {n : Ψ ⊕ Ψ → ℕ}
    (C : ∀ s, Matrix (Fin (n s)) (Fin (rk Ψ p q s)) Ω) (B : ∀ s, Matrix (Fin (rk Ψ p q s)) (Fin (n s)) Ω)
    (hBC : ∀ s, B s * C s = 1) (t : StepIx Ψ p q) (I I' : Finset (Fin (p + q)))
    (hI : I.card = (t.2 : ℕ) + 1) (hI' : I'.card = (t.2 : ℕ) + 1)
    (hp : ∀ a ∈ I, ∃ l, posOf p q t.1 l = a) (hp' : ∀ a ∈ I', ∃ l, posOf p q t.1 l = a),
    ∑ J : Fin ((t.2 : ℕ) + 1) → Fin (n t.1), sMin B t I J * cMin C t J I' = if I = I' then 1 else 0 := by
  intro Ψ p q Ω _ n C B hBC t I I' hI hI' hp _
  classical
  rw [sum_strictMono_eq (fun J => sMin B t I J * cMin C t J I') (fun J hJ => by
    simp only [sMin, if_neg hJ, zero_mul])]
  have hterm : ∀ s : GroundTheory.PAdicHodge.KSubset (n t.1) ((t.2 : ℕ) + 1),
      sMin B t I s.emb * cMin C t s.emb I' =
        (((bExt B t.1).submatrix (I.orderEmbOfFin hI) id).submatrix id s.emb).det *
          (((aExt C t.1).submatrix id (I'.orderEmbOfFin hI')).submatrix s.emb id).det := by
    intro s
    simp only [sMin, if_pos s.emb.strictMono, bMin, cMin, dif_pos hI, dif_pos hI']
    rfl
  simp only [hterm]
  rw [← GroundTheory.PAdicHodge.det_mul_eq_sum_minors]
  have hmat : (bExt B t.1).submatrix (I.orderEmbOfFin hI) id * (aExt C t.1).submatrix id (I'.orderEmbOfFin hI') =
      (1 : Matrix (Fin (p + q)) (Fin (p + q)) Ω).submatrix (I.orderEmbOfFin hI) (I'.orderEmbOfFin hI') := by
    ext x y
    obtain ⟨l, hl⟩ := hp _ (Finset.orderEmbOfFin_mem I hI x)
    have h := bExt_mul_aExt_row C B hBC t.1 l (I'.orderEmbOfFin hI' y)
    rw [hl] at h
    simpa [Matrix.mul_apply] using h
  rw [hmat]
  by_cases e : I = I'
  · subst e
    rw [if_pos rfl, Matrix.submatrix_one _ (I.orderEmbOfFin hI).injective, Matrix.det_one]
  · rw [if_neg e]
    have hns : ¬ I ⊆ I' := fun hs => e (Finset.eq_of_subset_of_card_le hs (by omega))
    obtain ⟨a, ha, ha'⟩ := Finset.not_subset.1 hns
    have hr : a ∈ Set.range (I.orderEmbOfFin hI) := by
      rw [Finset.range_orderEmbOfFin]
      exact ha
    obtain ⟨x, rfl⟩ := hr
    refine Matrix.det_eq_zero_of_row_eq_zero x fun y => ?_
    rw [Matrix.submatrix_apply]
    refine Matrix.one_apply_ne fun h => ha' ?_
    rw [h]
    exact Finset.orderEmbOfFin_mem _ _ _

end GlobalTheory.CompanionTheory.Ar.PB.FMX.Frm.Inv
end
end

section

open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun

theorem _root_.GlobalTheory.T.hodgeCpt_frame_degree_formula : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (K₀ : Type) [Fintype K₀] (J₀ : K₀ → Type) [∀ k, Fintype (J₀ k)] (x₀ : (Σ k, J₀ k) → Ω) (𝔐 : HodgeCpt Y S x₀) (bW : WBases 𝔐) (bO : OmBases 𝔐) (n m : CMType H ⊕ CMType H → ℕ) (φ : ∀ s, Fin (n s) → Module.Dual Ω (EE 𝔐)), FormsOK 𝔐 bW bO m φ → ∀ (Z : Scheme.{0}) (ξ' : Spec (CommRingCat.of (GenField Ω (rk (CMType H) D.p D.q))) ⟶ Z) (f : Z ⟶ 𝔐.X), @CoordTie Z _ _ ℤ _ (Ring.toIntAlgebra _) ξ' _ (seg (yv (p := D.p) (q := D.q) (aOf 𝔐 bW bO φ) x₀)) → (∀ q : Z, genPt ξ' ⤳ q) → GlobalTheory.CompanionTheory.Ar.Dominates ξ' 𝔐.ξ f (algebraMap Ω (GenField Ω (rk (CMType H) D.p D.q))) → Smooth f → IsNormalScheme Z := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.FMX.flag_total_normal | exact GlobalTheory.CompanionTheory.Ar.PB.FMX.flag_total_normal | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.FMX.flag_total_normal <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun

theorem _root_.GlobalTheory.T.basePart_yv_eq_algebraMap_xb : ∀ (Ψ : Type) [Fintype Ψ] (p q : ℕ) (Ω : Type) [Field Ω] (n : Ψ ⊕ Ψ → ℕ) (A : ∀ s, Matrix (Fin (n s)) (Fin (rk Ψ p q s)) Ω) (K₀ : Type) [Fintype K₀] (J₀ : K₀ → Type) [∀ k, Fintype (J₀ k)] (x₀ : (Σ k, J₀ k) → Ω), ∀ r, basePart (blkF Ψ p q K₀) (yv A x₀) r = algebraMap Ω (GenField Ω (rk Ψ p q)) (xb A x₀ r) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.FMX.YBase.basePart_yv | exact GlobalTheory.CompanionTheory.Ar.PB.FMX.YBase.basePart_yv | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.FMX.YBase.basePart_yv <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun

theorem _root_.GlobalTheory.T.isGenericFlag_gMat : ∀ (Ψ : Type) [Fintype Ψ] (p q : ℕ) (Ω : Type) [Field Ω], GlobalTheory.CompanionTheory.Ar.PB.IsGenericFlag Ω p (gMat (Ψ := Ψ) p q Ω) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.FMX.GenMat.gMat_isGenericFlag | exact GlobalTheory.CompanionTheory.Ar.PB.FMX.GenMat.gMat_isGenericFlag | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.FMX.GenMat.gMat_isGenericFlag <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun

theorem _root_.GlobalTheory.T.hodgeCpt_bases_linearIndependent_span : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (K₀ : Type) [Fintype K₀] (J₀ : K₀ → Type) [∀ k, Fintype (J₀ k)] (x₀ : (Σ k, J₀ k) → Ω) (𝔐 : HodgeCpt Y S x₀) (bW : WBases 𝔐) (bO : OmBases 𝔐), ∀ s, LinearIndependent Ω (cc 𝔐 bW bO s) ∧ Submodule.span Ω (Set.range (cc 𝔐 bW bO s)) = VV 𝔐 s := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.FMX.GenBases.cc_basis | exact GlobalTheory.CompanionTheory.Ar.PB.FMX.GenBases.cc_basis | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.FMX.GenBases.cc_basis <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun

theorem _root_.GlobalTheory.T.hodgeCpt_frame_leading_term : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (K₀ : Type) [Fintype K₀] (J₀ : K₀ → Type) [∀ k, Fintype (J₀ k)] (x₀ : (Σ k, J₀ k) → Ω) (𝔐 : HodgeCpt Y S x₀) (bW : WBases 𝔐) (bO : OmBases 𝔐) (n m : CMType H ⊕ CMType H → ℕ) (φ : ∀ s, Fin (n s) → Module.Dual Ω (EE 𝔐)), FormsOK 𝔐 bW bO m φ → ∃ (Z : Scheme.{0}) (ξ' : Spec (CommRingCat.of (GenField Ω (rk (CMType H) D.p D.q))) ⟶ Z) (f : Z ⟶ 𝔐.X), @CoordTie Z _ _ ℤ _ (Ring.toIntAlgebra _) ξ' _ (seg (yv (p := D.p) (q := D.q) (aOf 𝔐 bW bO φ) x₀)) ∧ (∀ q : Z, genPt ξ' ⤳ q) ∧ GlobalTheory.CompanionTheory.Ar.Dominates ξ' 𝔐.ξ f (algebraMap Ω (GenField Ω (rk (CMType H) D.p D.q))) ∧ Smooth f := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.FMX.exists_flagTotal | exact GlobalTheory.CompanionTheory.Ar.PB.FMX.exists_flagTotal | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.FMX.exists_flagTotal <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun

theorem _root_.GlobalTheory.T.hodgeCpt_frame_order_bound : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (K₀ : Type) [Fintype K₀] (J₀ : K₀ → Type) [∀ k, Fintype (J₀ k)] (x₀ : (Σ k, J₀ k) → Ω) (𝔐 : HodgeCpt Y S x₀) (bW : WBases 𝔐) (bO : OmBases 𝔐) (n m : CMType H ⊕ CMType H → ℕ) (φ : ∀ s, Fin (n s) → Module.Dual Ω (EE 𝔐)) (d : ℕ), FormsOK 𝔐 bW bO m φ → CoordTie ℤ 𝔐.ξ (seg (xb (p := D.p) (q := D.q) (aOf 𝔐 bW bO φ) x₀)) → IsArithVar (mCoordIdeal x₀) (d + 1) → IsArithVar (mCoordIdeal (xb (p := D.p) (q := D.q) (aOf 𝔐 bW bO φ) x₀)) (d + 1) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.FMX.DimBase.isArithVar_xb | exact GlobalTheory.CompanionTheory.Ar.PB.FMX.DimBase.isArithVar_xb | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.FMX.DimBase.isArithVar_xb <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun

theorem _root_.GlobalTheory.T.hodgeCpt_isVectorBundle_rank : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (K₀ : Type) [Fintype K₀] (J₀ : K₀ → Type) [∀ k, Fintype (J₀ k)] (x₀ : (Σ k, J₀ k) → Ω) (𝔐 : HodgeCpt Y S x₀), ∀ s, (LL 𝔐 s).IsVB (rk (CMType H) D.p D.q s) (VV 𝔐 s) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.FMX.LL_isVB | exact GlobalTheory.CompanionTheory.Ar.PB.FMX.LL_isVB | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.FMX.LL_isVB <;> assumption)
end
