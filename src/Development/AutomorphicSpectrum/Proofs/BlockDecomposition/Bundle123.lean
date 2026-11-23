module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle001
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle010
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle048
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle108
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle084
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle082
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle113
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle098
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle101
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle110
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle111
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CosetCongruenceRefinement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.TwistedKernels.ExPhiPlusOnto
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.TwistedKernels.TwKerLeComapOf
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.BinaryMassMeans.MeanVal

@[expose] public section

section

open Matrix Topology Filter

noncomputable section

namespace GlobalTheory.CompanionTheory.LinRedLie

variable {n : ℕ} {G : Set (Matrix (Fin n) (Fin n) ℂ)}

def unitsOf (hG : GlobalTheory.LinRed.IsLinRed G) : Subgroup (Matrix (Fin n) (Fin n) ℂ)ˣ where
  carrier := {u | (u : Matrix (Fin n) (Fin n) ℂ) ∈ G}
  one_mem' := hG.one_mem
  mul_mem' := fun {a b} ha hb => hG.mul_mem _ ha _ hb
  inv_mem' := fun {u} hu => by
    have h := hG.inv_mem _ hu
    rw [← Matrix.coe_units_inv] at h
    exact h

theorem isClosed_unitsOf (hG : GlobalTheory.LinRed.IsLinRed G) :
    IsClosed (unitsOf hG : Set (Matrix (Fin n) (Fin n) ℂ)ˣ) := by
  refine isClosed_of_closure_subset fun u hu => ?_
  refine hG.closed _ u.isUnit ?_
  exact closure_mono (fun v hv => hv) (map_mem_closure Units.continuous_val hu (fun v hv => hv))


open scoped Matrix.Norms.L2Operator in
theorem exists_subspace (hG : GlobalTheory.LinRed.IsLinRed G) :
    ∃ 𝔤 : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ), (∀ X ∈ 𝔤, NormedSpace.exp X ∈ G) ∧
      ∃ U : Set (Matrix (Fin n) (Fin n) ℂ), IsOpen U ∧ (0 : Matrix (Fin n) (Fin n) ℂ) ∈ U ∧
        ∀ X ∈ U, NormedSpace.exp X ∈ G → X ∈ 𝔤 := by
  obtain ⟨𝔤, h⟩ := GlobalTheory.CompanionTheory.ClosedSubgroupUnits.exists_isExpLieAlgebra (unitsOf hG) (isClosed_unitsOf hG)
  obtain ⟨U, hUo, h0, -, hU⟩ := h.exists_nhds
  exact ⟨𝔤, fun X hX => h.expUnit_mem X hX, U, hUo, h0, fun X hXU hX => hU X hXU hX⟩

theorem exists_lieAlgebra : ∀ {n : ℕ} {G : Set (Matrix (Fin n) (Fin n) ℂ)}, GlobalTheory.LinRed.IsLinRed G →
    ∃ 𝔤 : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ),
      (∀ X, X ∈ 𝔤 ↔ ∀ t : ℝ, NormedSpace.exp (t • X) ∈ G) ∧
      ∃ V ∈ 𝓝 (0 : Matrix (Fin n) (Fin n) ℂ), ∀ X ∈ V, NormedSpace.exp X ∈ G → X ∈ 𝔤 := by
  intro n G hG
  obtain ⟨𝔤, hexp, U, hUo, h0, hU⟩ := exists_subspace hG
  refine ⟨𝔤, fun X => ⟨fun hX t => hexp _ (𝔤.smul_mem t hX), fun hX => ?_⟩,
    U, hUo.mem_nhds h0, hU⟩
  have hc : Continuous fun t : ℝ => t • X := continuous_id.smul continuous_const
  have hev : ∀ᶠ t : ℝ in 𝓝 0, t • X ∈ U :=
    hc.continuousAt.eventually_mem (by simpa using hUo.mem_nhds h0)
  obtain ⟨t, htU, ht⟩ := ((hev.filter_mono nhdsWithin_le_nhds).and self_mem_nhdsWithin :
    ∀ᶠ t : ℝ in 𝓝[≠] 0, t • X ∈ U ∧ t ∈ ({0}ᶜ : Set ℝ)).exists
  exact (𝔤.smul_mem_iff ht).1 (hU _ htU (hX t))

end GlobalTheory.CompanionTheory.LinRedLie
end
end

section

open Matrix GlobalTheory.PRep GlobalTheory.BZMir GlobalTheory.BZMir.Fun GlobalTheory.SplitWeil ValuativeRel
open scoped Topology

namespace GlobalTheory.CompanionTheory.BZOnto.PerpSmall

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def box (m : ℕ) (s : kˣ) : AddSubgroup (Fin m → k) where
  carrier := {l | ∀ j, l j ∈ cball s}
  add_mem' ha hb j := add_mem_cball (ha j) (hb j)
  zero_mem' _ := by simp [cball]
  neg_mem' ha j := neg_mem_cball (ha j)

theorem mem_box {m : ℕ} {s : kˣ} {l : Fin m → k} : l ∈ box m s ↔ ∀ j, l j ∈ cball s := by
  exact Iff.rfl

theorem coe_box (m : ℕ) (s : kˣ) :
    (box m s : Set (Fin m → k)) = Set.univ.pi fun _ => cball s := by
  ext l
  simp only [SetLike.mem_coe, mem_box, Set.mem_univ_pi]

theorem isCompact_box (m : ℕ) (s : kˣ) : IsCompact (box m s : Set (Fin m → k)) := by
  rw [coe_box]
  exact isCompact_univ_pi fun _ => GlobalTheory.SplitWeil.isCompact_cball s

theorem box_mem_nhds (m : ℕ) (s : kˣ) : (box m s : Set (Fin m → k)) ∈ 𝓝 (0 : Fin m → k) := by
  rw [coe_box]
  exact set_pi_mem_nhds Set.finite_univ fun _ _ => GlobalTheory.SplitWeil.cball_mem_nhds s

theorem exists_box_subset {m : ℕ} {Ω : Set (Fin m → k)} (hΩ : Ω ∈ 𝓝 (0 : Fin m → k)) :
    ∃ r : kˣ, (box m r : Set (Fin m → k)) ⊆ Ω := by
  rw [nhds_pi, Filter.mem_pi'] at hΩ
  obtain ⟨I, t, ht, hsub⟩ := hΩ
  choose s hs using fun i => GlobalTheory.SplitWeil.exists_cball_subset (by simpa using ht i)
  by_cases hm : Nonempty (Fin m)
  · obtain ⟨i₀, -, hi₀⟩ := Finset.exists_min_image Finset.univ (fun i => ValuativeRel.valuation k (s i : k))
      Finset.univ_nonempty
    refine ⟨s i₀, fun l hl => hsub fun i _ => hs i ?_⟩
    exact le_trans (show ValuativeRel.valuation k (l i) ≤ _ from (mem_box.1 hl) i) (hi₀ i (Finset.mem_univ _))
  · exact ⟨1, fun l _ => hsub fun i _ => (hm ⟨i⟩).elim⟩

theorem dotProduct_mem_cball {m : ℕ} {r s : kˣ} {b l : Fin m → k} (hb : b ∈ box m (r * s⁻¹))
    (hl : l ∈ box m s) : b ⬝ᵥ l ∈ cball r := by
  unfold dotProduct
  refine Finset.sum_induction _ (· ∈ cball r) (fun a b ha hb => add_mem_cball ha hb) ?_ ?_
  · simp only [GlobalTheory.SplitWeil.cball, Set.mem_ofPred_eq]
    show ValuativeRel.valuation k 0 ≤ _
    simp
  · intro j _
    have h1 := (mem_box.1 hb) j
    have h2 := (mem_box.1 hl) j
    simp only [GlobalTheory.SplitWeil.cball, Set.mem_ofPred_eq]
    show ValuativeRel.valuation k (b j * l j) ≤ ValuativeRel.valuation k (r : k)
    rw [map_mul]
    calc ValuativeRel.valuation k (b j) * ValuativeRel.valuation k (l j)
        ≤ ValuativeRel.valuation k ((r * s⁻¹ : kˣ) : k) * ValuativeRel.valuation k (s : k) := mul_le_mul' h1 h2
      _ = ValuativeRel.valuation k (r : k) := by
        rw [← map_mul]
        congr 1
        simp

end GlobalTheory.CompanionTheory.BZOnto.PerpSmall
end

section

open MeasureTheory Filter Topology PositivityTheory.RgEis GlobalTheory.CompanionTheory.TubeFourier

theorem _root_.GlobalTheory.T.inverse_transform_locally_bounded : ∀ (X : Type) [NormedAddCommGroup X] [NormedSpace ℂ X] (T : Type) [TopologicalSpace T] (φ : ℝ × ℝ → T → X), ExpDecay φ → (∀ g : T, Continuous fun t => φ t g) → ∀ C : Set (ℝ × ℝ), IsCompact C → ∀ g : T, ∃ U ∈ 𝓝 g, ∃ M : ℝ, ∀ l ∈ tube C, ∀ g' ∈ U, ‖inv (fun t => φ t g') l‖ ≤ M := by
  first | exact @GlobalTheory.CompanionTheory.TubeFourier.inv_bounded_on_tube | exact GlobalTheory.CompanionTheory.TubeFourier.inv_bounded_on_tube | (intros; apply GlobalTheory.CompanionTheory.TubeFourier.inv_bounded_on_tube <;> assumption)
end

section

open MeasureTheory Filter Topology PositivityTheory.RgEis GlobalTheory.CompanionTheory.TubeFourier

theorem _root_.GlobalTheory.T.inverse_transform_recovers_function : ∀ (X : Type) [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X] (G : ℂ × ℂ → X) (x : ℝ × ℝ), Continuous (fun y => G (pt x y)) → (∃ M : ℝ, ∀ y : ℝ × ℝ, ‖G (pt x y)‖ ≤ M * Real.exp (-(y.1 ^ 2 + y.2 ^ 2))) → Continuous (phi G x) → (∃ ε : ℝ, 0 < ε ∧ ∃ M : ℝ, ∀ t : ℝ × ℝ, ‖phi G x t‖ ≤ M * Real.exp (-rdot x t) * Real.exp (-ε * (|t.1| + |t.2|))) → ∀ y : ℝ × ℝ, inv (phi G x) (pt x y) = G (pt x y) := by
  first | exact @GlobalTheory.CompanionTheory.TubeFourier.PhiInv.inv_phi_eq | exact GlobalTheory.CompanionTheory.TubeFourier.PhiInv.inv_phi_eq | (intros; apply GlobalTheory.CompanionTheory.TubeFourier.PhiInv.inv_phi_eq <;> assumption)
end

section

open MeasureTheory Filter Topology PositivityTheory.RgEis GlobalTheory.CompanionTheory.TubeFourier

theorem _root_.GlobalTheory.T.tube_transform_horizontal_invariance : ∀ (X : Type) [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X] (Ω : Set (ℝ × ℝ)) (G : ℂ × ℂ → X), GaussTube G Ω → ∀ a b c : ℝ, a ≤ b → (∀ s ∈ Set.Icc a b, (s, c) ∈ Ω) → ∀ t : ℝ × ℝ, phi G (a, c) t = phi G (b, c) t := by
  first | exact @GlobalTheory.CompanionTheory.TubeFourier.phi_shift_fst | exact GlobalTheory.CompanionTheory.TubeFourier.phi_shift_fst | (intros; apply GlobalTheory.CompanionTheory.TubeFourier.phi_shift_fst <;> assumption)
end

section

open MeasureTheory Filter Topology PositivityTheory.RgEis GlobalTheory.CompanionTheory.TubeFourier

theorem _root_.GlobalTheory.T.tube_transform_vertical_invariance : ∀ (X : Type) [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X] (Ω : Set (ℝ × ℝ)) (G : ℂ × ℂ → X), GaussTube G Ω → ∀ a b c : ℝ, a ≤ b → (∀ s ∈ Set.Icc a b, (c, s) ∈ Ω) → ∀ t : ℝ × ℝ, phi G (c, a) t = phi G (c, b) t := by
  first | exact @GlobalTheory.CompanionTheory.TubeFourier.phi_shift_snd | exact GlobalTheory.CompanionTheory.TubeFourier.phi_shift_snd | (intros; apply GlobalTheory.CompanionTheory.TubeFourier.phi_shift_snd <;> assumption)
end

section

open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.CompanionTheory.SiegelND.Integ.Hua GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS
open scoped Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.Decomp

def IsI {K : Type} [Field K] [NumberField K] (x : K) : Prop :=
  ∃ o : 𝓞 K, algebraMap (𝓞 K) K o = x

section I

variable {K : Type} [Field K] [NumberField K]

theorem IsI.add {x y : K} (hx : IsI x) (hy : IsI y) : IsI (x + y) := by
  obtain ⟨o, rfl⟩ := hx
  obtain ⟨p, rfl⟩ := hy
  exact ⟨o + p, by simp⟩

theorem IsI.neg {x : K} (hx : IsI x) : IsI (-x) := by
  obtain ⟨o, rfl⟩ := hx
  exact ⟨-o, by simp⟩

theorem IsI.mul {x y : K} (hx : IsI x) (hy : IsI y) : IsI (x * y) := by
  obtain ⟨o, rfl⟩ := hx
  obtain ⟨p, rfl⟩ := hy
  exact ⟨o * p, by simp⟩

theorem isI_zero : IsI (0 : K) := ⟨0, by simp⟩

theorem isI_sum {ι : Type} (s : Finset ι) (f : ι → K) (h : ∀ i ∈ s, IsI (f i)) :
    IsI (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (isI_zero : IsI (0 : K))
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem Kc_le_add {n : ℕ} (c h : Matrix (Fin n) (Fin n) K) (hh : ∀ a b, IsI (h a b)) :
    Kc c ≤ Kc (c + h) := by
  intro y hy i
  have h1 : IsI ((c *ᵥ fun j => algebraMap (𝓞 K) K (y j)) i) := hy i
  have h2 : IsI ((h *ᵥ fun j => algebraMap (𝓞 K) K (y j)) i) := by
    show IsI (∑ j, h i j * algebraMap (𝓞 K) K (y j))
    exact isI_sum (K := K) Finset.univ _ fun j _ => (hh i j).mul ⟨y j, rfl⟩
  have h3 := h1.add h2
  rw [Matrix.add_mulVec]
  exact h3

theorem Kc_add {n : ℕ} (c h : Matrix (Fin n) (Fin n) K) (hh : ∀ a b, IsI (h a b)) :
    Kc (c + h) = Kc c := by
  refine le_antisymm ?_ (Kc_le_add c h hh)
  have := Kc_le_add (c + h) (-h) fun a b => by simpa using IsI.neg (hh a b)
  simpa using this

theorem delta_add {n : ℕ} (c h : Matrix (Fin n) (Fin n) K) (hh : ∀ a b, IsI (h a b)) :
    delta (c + h) = delta c := by
  unfold delta
  rw [Kc_add c h hh]

theorem vec_out {m : ℕ} (t : Fin m → K) (i : Fin m) :
    IsI ((Quotient.out (Submodule.Quotient.mk t : (Fin m → K) ⧸ intVec K m) : Fin m → K) i - t i) := by
  have h : Submodule.Quotient.mk (Quotient.out (Submodule.Quotient.mk t : (Fin m → K) ⧸ intVec K m))
      = (Submodule.Quotient.mk t : (Fin m → K) ⧸ intVec K m) := Quotient.out_eq _
  have h2 := (Submodule.Quotient.eq _).1 h
  exact h2 i

end I

section H

variable {F E : Type} [Field F] [Field E] [Algebra F E] [NumberField E]

theorem herm_out (σ : E →ₐ[F] E) {n : ℕ} (t : hermE σ n) (a b : Fin n) :
    IsI ((Quotient.out (QuotientAddGroup.mk t : hermE σ n ⧸ hermO σ n)).1 a b - t.1 a b) := by
  have h : (QuotientAddGroup.mk (Quotient.out (QuotientAddGroup.mk t : hermE σ n ⧸ hermO σ n)) :
      hermE σ n ⧸ hermO σ n) = QuotientAddGroup.mk t := Quotient.out_eq _
  have h2 : IsI ((-(Quotient.out (QuotientAddGroup.mk t : hermE σ n ⧸ hermO σ n)) + t).1 a b) :=
    (QuotientAddGroup.eq.1 h) a b
  have h3 := h2.neg
  have e : -(-(Quotient.out (QuotientAddGroup.mk t : hermE σ n ⧸ hermO σ n)) + t).1 a b =
      (Quotient.out (QuotientAddGroup.mk t : hermE σ n ⧸ hermO σ n)).1 a b - t.1 a b := by
    simp
    ring
  rwa [e] at h3

def topB (σ : E →ₐ[F] E) {m : ℕ} (C : hermE σ (m + 1)) : hermE σ m :=
  ⟨fun a b => C.1 a.castSucc b.castSucc, fun a b => C.2 a.castSucc b.castSucc⟩

def lastCol {m : ℕ} (C : Matrix (Fin (m + 1)) (Fin (m + 1)) E) : Fin m → E :=
  fun a => C a.castSucc (Fin.last m)

theorem blk_cc (σ : E →ₐ[F] E) {m : ℕ} (c : Matrix (Fin m) (Fin m) E) (u : Fin m → E) (d : E)
    (a b : Fin m) : blk σ c u d a.castSucc b.castSucc = c a b := by simp [blk]

theorem blk_cl (σ : E →ₐ[F] E) {m : ℕ} (c : Matrix (Fin m) (Fin m) E) (u : Fin m → E) (d : E)
    (a : Fin m) : blk σ c u d a.castSucc (Fin.last m) = u a := by simp [blk]

theorem blk_lc (σ : E →ₐ[F] E) {m : ℕ} (c : Matrix (Fin m) (Fin m) E) (u : Fin m → E) (d : E)
    (b : Fin m) : blk σ c u d (Fin.last m) b.castSucc = σ (u b) := by simp [blk]

theorem blk_ll (σ : E →ₐ[F] E) {m : ℕ} (c : Matrix (Fin m) (Fin m) E) (u : Fin m → E) (d : E) :
    blk σ c u d (Fin.last m) (Fin.last m) = d := by simp [blk]

theorem blk_sub_isI (σ : E →ₐ[F] E) (hσ : ∀ x : E, IsI x → IsI (σ x)) {m : ℕ}
    (C : hermE σ (m + 1)) (c : Matrix (Fin m) (Fin m) E) (u : Fin m → E) (d : E)
    (hc : ∀ a b : Fin m, IsI (c a b - C.1 a.castSucc b.castSucc))
    (hu : ∀ a : Fin m, IsI (u a - C.1 a.castSucc (Fin.last m)))
    (hd : IsI (d - C.1 (Fin.last m) (Fin.last m))) (i j : Fin (m + 1)) :
    IsI (blk σ c u d i j - C.1 i j) := by
  induction i using Fin.lastCases with
  | last =>
    induction j using Fin.lastCases with
    | last => rw [blk_ll]; exact hd
    | cast b =>
      rw [blk_lc, ← C.2 (Fin.last m) b.castSucc, ← map_sub]
      exact hσ _ (hu b)
  | cast a =>
    induction j using Fin.lastCases with
    | last => rw [blk_cl]; exact hu a
    | cast b => rw [blk_cc]; exact hc a b

theorem herm_isI (σ : E →ₐ[F] E) (hσ : ∀ x : E, IsI x → IsI (σ x)) {m : ℕ}
    (D : hermE σ (m + 1))
    (hc : ∀ a b : Fin m, IsI (D.1 a.castSucc b.castSucc))
    (hu : ∀ a : Fin m, IsI (D.1 a.castSucc (Fin.last m)))
    (hd : IsI (D.1 (Fin.last m) (Fin.last m))) (i j : Fin (m + 1)) : IsI (D.1 i j) := by
  induction i using Fin.lastCases with
  | last =>
    induction j using Fin.lastCases with
    | last => exact hd
    | cast b =>
      rw [← D.2 (Fin.last m) b.castSucc]
      exact hσ _ (hu b)
  | cast a =>
    induction j using Fin.lastCases with
    | last => exact hu a
    | cast b => exact hc a b

end H

theorem isI_algebraMap {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] {y : F} (hy : IsI y) : IsI (algebraMap F E y) := by
  obtain ⟨o, rfl⟩ := hy
  have h : IsIntegral ℤ (algebraMap F E (algebraMap (𝓞 F) F o)) :=
    (RingOfIntegers.isIntegral_coe o).algebraMap
  exact ⟨IsIntegralClosure.mk' (𝓞 E) _ h, IsIntegralClosure.algebraMap_mk' _ _ h⟩

theorem hermClass_blocks : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ m : ℕ, ∃ ι : (hermE σ (m + 1) ⧸ hermO σ (m + 1)) → (hermE σ m ⧸ hermO σ m) × ((Fin m → E) ⧸ intVec E m) × FQ F, Function.Injective ι ∧ ∀ x, delta (Quotient.out x).1 = delta (blk σ (Quotient.out (ι x).1).1 (Quotient.out (ι x).2.1) (algebraMap F E ((Quotient.out (ι x).2.2 : Fin 1 → F) 0))) := by
  intro F E _ _ _ _ _ σ hcm m
  obtain ⟨-, hfix, hsO, -⟩ := GlobalTheory.T.cm_conjugation_properties F E σ hcm
  have hσ : ∀ x : E, IsI x → IsI (σ x) := by
    rintro x ⟨o, rfl⟩
    exact ⟨sO σ o, hsO o⟩
  have hcorner : ∀ C : hermE σ (m + 1), ∃ y : F,
      algebraMap F E y = C.1 (Fin.last m) (Fin.last m) := fun C => hfix _ (C.2 _ _)
  choose dd hdd using hcorner
  refine ⟨fun x => (QuotientAddGroup.mk (topB σ (Quotient.out x)),
    Submodule.Quotient.mk (lastCol (Quotient.out x).1),
    Submodule.Quotient.mk (fun _ => dd (Quotient.out x))), ?_, ?_⟩
  · intro x x' hxx
    obtain ⟨h1, h2, h3⟩ : _ ∧ _ ∧ _ := by simpa [Prod.ext_iff] using hxx
    have h1' := QuotientAddGroup.eq.1 h1
    have h2' := (Submodule.Quotient.eq _).1 h2
    have h3' := (Submodule.Quotient.eq _).1 h3
    rw [← Quotient.out_eq x, ← Quotient.out_eq x']
    refine QuotientAddGroup.eq.2 ?_
    refine fun i j => herm_isI σ hσ (-(Quotient.out x) + Quotient.out x') ?_ ?_ ?_ i j
    · intro a b
      exact h1' a b
    · intro a
      have : IsI (lastCol (Quotient.out x).1 a - lastCol (Quotient.out x').1 a) := h2' a
      have e := this.neg
      simpa [lastCol, add_comm, sub_eq_add_neg] using e
    · have : IsI (dd (Quotient.out x) - dd (Quotient.out x')) := h3' 0
      have e := (isI_algebraMap (E := E) this).neg
      simpa [hdd, add_comm, sub_eq_add_neg] using e
  · intro x
    dsimp only
    set C := Quotient.out x with hC
    set M := blk σ (Quotient.out (QuotientAddGroup.mk (topB σ C) : hermE σ m ⧸ hermO σ m)).1
      (Quotient.out (Submodule.Quotient.mk (lastCol C.1) : (Fin m → E) ⧸ intVec E m))
      (algebraMap F E ((Quotient.out (Submodule.Quotient.mk (fun _ => dd C) : FQ F) : Fin 1 → F) 0))
      with hM
    have hI : ∀ i j, IsI ((M - C.1) i j) := by
      intro i j
      refine blk_sub_isI σ hσ C _ _ _ ?_ ?_ ?_ i j
      · intro a b
        exact herm_out σ (topB σ C) a b
      · intro a
        exact vec_out (lastCol C.1) a
      · have h := isI_algebraMap (E := E) (vec_out (fun _ : Fin 1 => dd C) 0)
        rw [map_sub, hdd] at h
        exact h
    have := delta_add C.1 (M - C.1) hI
    rw [add_sub_cancel] at this
    exact this.symm

end GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.Decomp
end
end

section

noncomputable section

open GlobalTheory.PRep GlobalTheory.BZMir GlobalTheory.BZMir.Fun Matrix

namespace GlobalTheory.CompanionTheory.BZPhiPhi

theorem rowQ_mul_of_mem_Q (k : Type) [Field k] (n : ℕ) (q g : Mir k (n + 1)) (hq : q ∈ Q k n) :
    rowQ k n (q * g) = rowQ k n g := by
  have hb : (blockMat k (n + 1) ((q : GL (Fin (n + 2)) k) : Matrix (Fin (n + 2)) (Fin (n + 2)) k)) (Fin.last n) =
      eLast k n := by
    have h := (mem_Mir_iff k (mirabolicProjection k (n + 1) q)).1 hq
    exact h
  have hg : ∀ j : Fin (n + 1), ((g : GL (Fin (n + 2)) k) : Matrix (Fin (n + 2)) (Fin (n + 2)) k)
      (Fin.last (n + 1)) (Fin.castSucc j) = 0 := by
    intro j
    have := congrFun ((mem_Mir_iff k (g : GL (Fin (n + 2)) k)).1 g.2) (Fin.castSucc j)
    simpa [eLast, Fin.castSucc_ne_last] using this
  funext j
  have hb' : ∀ l : Fin (n + 1), ((q : GL (Fin (n + 2)) k) : Matrix (Fin (n + 2)) (Fin (n + 2)) k)
      (Fin.castSucc (Fin.last n)) (Fin.castSucc l) = eLast k n l := fun l => congrFun hb l
  simp only [rowQ, Subgroup.coe_mul, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_castSucc (n := n + 1), hg, hb', mul_zero, add_zero]
  simp [eLast, Pi.single_apply]

end GlobalTheory.CompanionTheory.BZPhiPhi

end
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter GlobalTheory.CompanionTheory.Equi
open scoped Classical

theorem _root_.GlobalTheory.T.coset_empty_places_lattice : ∀ (F : Type) [Field F] [NumberField F] (ι : Type) (I : Ideal (𝓞 F)) (x0 : ι → F), cosetOff (∅ : Finset (HeightOneSpectrum (𝓞 F))) I x0 = latCoset I x0 := by
  first | exact @GlobalTheory.CompanionTheory.Equi.cosetOff_empty_eq_latCoset | exact GlobalTheory.CompanionTheory.Equi.cosetOff_empty_eq_latCoset | (intros; apply GlobalTheory.CompanionTheory.Equi.cosetOff_empty_eq_latCoset <;> assumption)
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter GlobalTheory.CompanionTheory.Equi
open scoped Classical

theorem _root_.GlobalTheory.T.coset_unit_ideal_integral : ∀ (F : Type) [Field F] [NumberField F] (ι : Type) (S : Finset (HeightOneSpectrum (𝓞 F))), cosetOff S (⊤ : Ideal (𝓞 F)) (0 : ι → F) = {x : ι → F | ∀ v, v ∉ S → ∀ i, algebraMap F (Fv F v) (x i) ∈ v.adicCompletionIntegers F} := by
  first | exact @GlobalTheory.CompanionTheory.Equi.CosetTop.cosetOff_top | exact GlobalTheory.CompanionTheory.Equi.CosetTop.cosetOff_top | (intros; apply GlobalTheory.CompanionTheory.Equi.CosetTop.cosetOff_top <;> assumption)
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.Mass.MeanV PositivityTheory.Rg.Mass NumberField IsDedekindDomain MeasureTheory Topology Filter
open scoped ENNReal NNReal Classical

theorem _root_.GlobalTheory.T.exists_integral_multiple_bounded_places : ∀ (F : Type) [Field F] [NumberField F] (T : Finset (HeightOneSpectrum (𝓞 F))) (K : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v)), (∀ v ∈ T, IsCompact (K v)) → ∃ N : ℕ, 0 < N ∧ ∀ x ∈ IntOut T, (∀ v ∈ T, algebraMap F (Fv F v) x ∈ K v) → ∃ y : 𝓞 F, (y : F) = (N : F) * x := by
  first | exact @GlobalTheory.CompanionTheory.Mass.MeanV.exists_common_denominator | exact GlobalTheory.CompanionTheory.Mass.MeanV.exists_common_denominator | (intros; apply GlobalTheory.CompanionTheory.Mass.MeanV.exists_common_denominator <;> assumption)
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter GlobalTheory.CompanionTheory.Equi
open scoped Classical

theorem _root_.GlobalTheory.T.coset_congruence_refinement : ∀ (F : Type) [Field F] [NumberField F] (ι : Type) (S : Finset (HeightOneSpectrum (𝓞 F))) (v : HeightOneSpectrum (𝓞 F)), v ∉ S → ∀ (I : Ideal (𝓞 F)), I ≠ ⊥ → ¬ I ≤ v.asIdeal → ∀ (k : ℕ) (x0 : ι → F) (c : ι → Fv F v), ∃ x1 : ι → F, ∀ x : ι → F, (x ∈ cosetOff (insert v S) I x0 ∧ ∀ i, algebraMap F (Fv F v) (x i) - c i ∈ ballV v k) ↔ x ∈ cosetOff S (I * v.asIdeal ^ k) x1 := by
  first | exact @GlobalTheory.CompanionTheory.Equi.CosetStep.coset_step | exact GlobalTheory.CompanionTheory.Equi.CosetStep.coset_step | (intros; apply GlobalTheory.CompanionTheory.Equi.CosetStep.coset_step <;> assumption)
end
