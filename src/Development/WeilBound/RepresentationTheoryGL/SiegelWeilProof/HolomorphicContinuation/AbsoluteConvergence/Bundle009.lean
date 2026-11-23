module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.Bundle005
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.Bundle004
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.Normed.Module.HahnBanach
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section

open MeasureTheory Set Filter Topology Matrix

namespace PositivityTheory.Rg.Sw.AbsSt

open PositivityTheory.Rg.Sw

theorem factorL : FactorL := by
  intro G _ S l C hC hcont hlin hbd
  haveI : CompactSpace C := isCompact_iff_compactSpace.mp hC
  have hl0 : l 0 = 0 := by
    have h := hbd 0 S.zero_mem 0 (by simp)
    simpa using h
  let lS : S →ₗ[ℂ] ℂ :=
    { toFun := fun F => l F.1
      map_add' := fun F₁ F₂ => by
        have h := hlin 1 F₁.1 F₁.2 F₂.1 F₂.2
        simpa using h
      map_smul' := fun a F => by
        have h := hlin a F.1 F.2 0 S.zero_mem
        simpa [hl0] using h }
  let R : S →ₗ[ℂ] C(C, ℂ) :=
    { toFun := fun F => ⟨fun x => F.1 x, (hcont F.1 F.2).comp continuous_subtype_val⟩
      map_add' := fun F₁ F₂ => by
        ext x
        simp
      map_smul' := fun a F => by
        ext x
        simp }
  have hRnorm : ∀ F : S, ‖l F.1‖ ≤ ‖R F‖ := by
    intro F
    apply hbd F.1 F.2
    intro x hx
    exact (R F).norm_coe_le_norm ⟨x, hx⟩
  have hker : LinearMap.ker R ≤ LinearMap.ker lS := by
    intro F hF
    rw [LinearMap.mem_ker] at hF ⊢
    have h := hRnorm F
    rw [hF, norm_zero] at h
    exact norm_le_zero_iff.mp h
  let f : LinearMap.range R →ₗ[ℂ] ℂ :=
    ((LinearMap.ker R).liftQ lS hker).comp
      (R.quotKerEquivRange.symm : LinearMap.range R →ₗ[ℂ] S ⧸ LinearMap.ker R)
  have hf : ∀ F : S, f ⟨R F, LinearMap.mem_range_self R F⟩ = l F.1 := by
    intro F
    simp only [f, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearMap.quotKerEquivRange_symm_apply_image, Submodule.mkQ_apply, Submodule.liftQ_apply]
    rfl
  have hfb : ∀ v : LinearMap.range R, ‖f v‖ ≤ 1 * ‖v‖ := by
    rintro ⟨v, F, rfl⟩
    rw [hf F, one_mul]
    exact hRnorm F
  obtain ⟨g, hg, -⟩ := exists_extension_norm_eq (LinearMap.range R) (f.mkContinuous 1 hfb)
  refine ⟨g, fun F hFS hF => ?_⟩
  have h1 := hg ⟨R ⟨F, hFS⟩, LinearMap.mem_range_self R _⟩
  rw [LinearMap.mkContinuous_apply, hf] at h1
  exact h1.symm

theorem kRCpt : KRCpt := by
  intro n
  let S : Set (M2 n) := {g | InG g ∧ gᴴ * g = 1}
  have hcl : IsClosed S := by
    show IsClosed ({g : M2 n | InG g} ∩ {g : M2 n | gᴴ * g = 1})
    apply IsClosed.inter
    · exact isClosed_eq
        ((continuous_id.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul continuous_id)
        continuous_const
    · exact isClosed_eq (continuous_id.matrix_conjTranspose.matrix_mul continuous_id) continuous_const
  have hsub : S ⊆ univ.pi (fun _ => univ.pi (fun _ => Metric.closedBall (0 : ℂ) 1)) := by
    intro g hg i _ j _
    rw [Metric.mem_closedBall, dist_zero_right]
    have hu : g ∈ Matrix.unitaryGroup (Fin n ⊕ Fin n) ℂ := by
      rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
      exact hg.2
    exact entry_norm_bound_of_unitary hu i j
  have hcpt : IsCompact S :=
    (isCompact_univ_pi (fun _ => isCompact_univ_pi (fun _ => isCompact_closedBall (0 : ℂ) 1))).of_isClosed_subset
      hcl hsub
  haveI : CompactSpace S := isCompact_iff_compactSpace.mp hcpt
  have hinv : ∀ g : S, g.1 * g.1ᴴ = 1 := fun g => mul_eq_one_comm.mp g.2.2
  let u : S → GL (Fin n ⊕ Fin n) ℂ := fun g => ⟨g.1, g.1ᴴ, hinv g, g.2.2⟩
  have hu : Continuous u :=
    Units.continuous_iff.mpr ⟨continuous_subtype_val, continuous_subtype_val.matrix_conjTranspose⟩
  let ψ : S → KR n := fun g => ⟨⟨u g, g.2.1⟩, g.2⟩
  have hψ : Continuous ψ := (hu.subtype_mk _).subtype_mk _
  have hsurj : Function.Surjective ψ := by
    intro k
    refine ⟨⟨mR k.1, k.2⟩, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    apply Units.ext
    rfl
  exact Function.Surjective.compactSpace hψ hsurj

end PositivityTheory.Rg.Sw.AbsSt
end
end

section

noncomputable section

open MeasureTheory Matrix Set Filter Topology MvPolynomial
open scoped NNReal

namespace PositivityTheory.Rg.Sw.AbsSt.CycP

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.AbsSt

variable {m n : ℕ}

def gen (ε : Fin m → Bool) (k : Bool × Fin n × Fin n) : PX m n := Qb ε k.1 k.2.1 k.2.2

def Mon (ε : Fin m → Bool) (d : ℕ) : Submodule ℂ (PX m n) :=
  Submodule.span ℂ {M | ∃ l : List (Bool × Fin n × Fin n), l.length ≤ d ∧ M = (l.map (gen ε)).prod}

theorem mon_mono (ε : Fin m → Bool) {d d' : ℕ} (h : d ≤ d') : Mon (n := n) ε d ≤ Mon ε d' :=
  Submodule.span_mono fun _ ⟨l, hl, e⟩ => ⟨l, hl.trans h, e⟩

theorem gen_mul_mon (ε : Fin m → Bool) (d : ℕ) (k : Bool × Fin n × Fin n) {M : PX m n} (hM : M ∈ Mon ε d) :
    gen ε k * M ∈ Mon ε (d + 1) := by
  induction hM using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨l, hl, rfl⟩ := hx
    exact Submodule.subset_span ⟨k :: l, by simp; omega, by simp⟩
  | zero => simp
  | add x y _ _ hx hy => rw [mul_add]; exact add_mem hx hy
  | smul a x _ hx => rw [mul_smul_comm]; exact Submodule.smul_mem _ _ hx

theorem mon_mul (ε : Fin m → Bool) {d d' : ℕ} {a b : PX m n} (ha : a ∈ Mon ε d) (hb : b ∈ Mon ε d') :
    a * b ∈ Mon ε (d + d') := by
  induction ha using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨l, hl, rfl⟩ := hx
    induction hb using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨l', hl', rfl⟩ := hy
      exact Submodule.subset_span ⟨l ++ l', by simp; omega, by simp⟩
    | zero => simp
    | add u v _ _ hu hv => rw [mul_add]; exact add_mem hu hv
    | smul c u _ hu => rw [mul_smul_comm]; exact Submodule.smul_mem _ _ hu
  | zero => simp
  | add u v _ _ hu hv => rw [add_mul]; exact add_mem hu hv
  | smul c u _ hu => rw [smul_mul_assoc]; exact Submodule.smul_mem _ _ hu

theorem adjoin_le (ε : Fin m → Bool) {R : PX m n}
    (hR : R ∈ Algebra.adjoin ℂ (Set.range fun k : Bool × Fin n × Fin n => (Qb ε k.1 k.2.1 k.2.2 : PX m n))) :
    ∃ d, R ∈ Mon ε d := by
  induction hR using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨k, rfl⟩ := hx
    exact ⟨1, Submodule.subset_span ⟨[k], by simp, by simp [gen]⟩⟩
  | algebraMap r =>
    refine ⟨0, ?_⟩
    rw [Algebra.algebraMap_eq_smul_one]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨[], by simp, by simp⟩)
  | add x y _ _ hx hy =>
    obtain ⟨d, hd⟩ := hx
    obtain ⟨d', hd'⟩ := hy
    exact ⟨max d d', add_mem (mon_mono ε (le_max_left _ _) hd) (mon_mono ε (le_max_right _ _) hd')⟩
  | mul x y _ _ hx hy =>
    obtain ⟨d, hd⟩ := hx
    obtain ⟨d', hd'⟩ := hy
    exact ⟨d + d', mon_mul ε hd hd'⟩

theorem dsum_apply {ι : Type*} (s : Finset ι) (D : ι → Derivation ℂ (PX m n) (PX m n)) (x : PX m n) :
    (∑ i ∈ s, D i) x = ∑ i ∈ s, D i x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, add_apply, ih]

def eulD (H : Matrix (Fin n) (Fin n) ℂ) : Derivation ℂ (PX m n) (PX m n) :=
  ∑ a : Fin m, ∑ j : Fin n, ((∑ i, X (a, i, false) * C (H i j)) • pderiv (a, j, false) +
    (∑ i, X (a, i, true) * C (star (H i j))) • pderiv (a, j, true))

theorem eulH_eq (H : Matrix (Fin n) (Fin n) ℂ) (R : PX m n) : eulH H R = eulD H R := by
  simp [eulH, eulD, smul_eq_mul]

theorem eulD_X_false (H : Matrix (Fin n) (Fin n) ℂ) (a : Fin m) (j : Fin n) :
    eulD H (X (a, j, false) : PX m n) = ∑ i, X (a, i, false) * C (H i j) := by
  simp [eulD, pderiv_X, Pi.single_apply, ite_and, Finset.sum_ite_eq]

theorem eulD_X_true (H : Matrix (Fin n) (Fin n) ℂ) (a : Fin m) (j : Fin n) :
    eulD H (X (a, j, true) : PX m n) = ∑ i, X (a, i, true) * C (star (H i j)) := by
  simp [eulD, pderiv_X, Pi.single_apply, ite_and, Finset.sum_ite_eq]

theorem eulH_gen (ε : Fin m → Bool) (H : Matrix (Fin n) (Fin n) ℂ) (k : Bool × Fin n × Fin n) :
    eulH H (gen ε k) ∈ Mon ε 1 := by
  have : eulH H (gen ε k) = ∑ l, C (H l k.2.2) * gen ε (k.1, k.2.1, l) + ∑ l, C (star (H l k.2.1)) * gen ε (k.1, l, k.2.2) := by
    obtain ⟨b, i, j⟩ := k
    rw [eulH_eq]

    simp only [gen, Qb, map_sum, Derivation.leibniz, smul_eq_mul, eulD_X_false, eulD_X_true, Finset.mul_sum]
    rw [Finset.sum_add_distrib]
    congr 1
    · rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun a _ => by ring
    · rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun a _ => by ring
  rw [this]
  refine add_mem (Submodule.sum_mem _ fun l _ => ?_) (Submodule.sum_mem _ fun l _ => ?_)
  · rw [← smul_eq_C_mul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨[(k.1, k.2.1, l)], by simp, by simp⟩)
  · rw [← smul_eq_C_mul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨[(k.1, l, k.2.2)], by simp, by simp⟩)

theorem eulH_mon (ε : Fin m → Bool) (H : Matrix (Fin n) (Fin n) ℂ) (d : ℕ) {M : PX m n} (hM : M ∈ Mon ε d) :
    eulH H M ∈ Mon ε d := by
  rw [eulH_eq]
  induction hM using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨l, hl, rfl⟩ := hx
    induction l generalizing d with
    | nil => simp
    | cons k l ih =>
      simp only [List.map_cons, List.prod_cons, Derivation.leibniz, smul_eq_mul]
      simp only [List.length_cons] at hl
      have hd : l.length + 1 ≤ d := hl
      refine add_mem ?_ ?_
      · exact mon_mono ε hd (gen_mul_mon ε l.length k (ih l.length le_rfl))
      · have h1 := eulH_gen ε H k
        rw [eulH_eq] at h1
        have h2 : (l.map (gen ε)).prod ∈ Mon ε l.length := Submodule.subset_span ⟨l, le_rfl, rfl⟩
        rw [mul_comm ((l.map (gen ε)).prod)]
        exact mon_mono ε (by omega) (mon_mul ε h1 h2)
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul a x _ hx => rw [(eulD H).map_smul]; exact Submodule.smul_mem _ _ hx

end PositivityTheory.Rg.Sw.AbsSt.CycP
end
end

section

noncomputable section

open MeasureTheory Matrix Set Filter Topology

namespace PositivityTheory.Rg.Sw.AbsSt.SDM

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.AbsSt

variable {m n : ℕ}

def mulR (A : Matrix (Fin n) (Fin n) ℂ) (y : Fin m → Fin n → ℂ) : Fin m → Fin n → ℂ := fun a j => ∑ i, y a i * A i j

def aE (H : Matrix (Fin n) (Fin n) ℂ) (σ : ℝ) : Matrix (Fin n) (Fin n) ℂ := NormedSpace.exp ((σ : ℂ) • H)

def DMp (ε : Fin m → Bool) (c : ℝ) (H : Matrix (Fin n) (Fin n) ℂ) (R : PX m n) : PX m n :=
  eulH H R - MvPolynomial.C (2 * (c : ℂ)) *
    (∑ i, ∑ j, MvPolynomial.C (H i j) * (Qb ε true j i + Qb ε false j i)) * R

def CellM : Prop := ∀ (n : ℕ) (H : Matrix (Fin n) (Fin n) ℂ), H.IsHermitian → ∀ f : ℝ → GR n,
  (∀ σ : ℝ, mR (f σ) = fromBlocks (NormedSpace.exp ((σ : ℂ) • H)) 0 0 (NormedSpace.exp (-((σ : ℂ) • H)))) →
  ∀ g : GR n, (mR g).toBlocks₂₁.det ≠ 0 → ∃ (y₁ : GR n) (b : Matrix (Fin n) (Fin n) ℂ), IsUp y₁ ∧ b.IsHermitian ∧
    ∀ (p q : ℕ) (e : ℤ) (σ : ℝ), ∃ (mA w : GR n), IsUp mA ∧
      F0 p q e mA = Complex.exp (-((σ : ℂ) * ((p + q : ℕ) : ℂ) * H.trace)) ∧
      mR w = JJ n * nU (aE H (-σ) * b * aE H (-σ)) ∧ (aE H (-σ) * b * aE H (-σ)).IsHermitian ∧
      g * f σ = y₁ * mA * w

def CoV : Prop := ∀ (m n : ℕ) (A : Matrix (Fin n) (Fin n) ℂ), A.det ≠ 0 → ∀ F : (Fin m → Fin n → ℂ) → ℂ,
  ∫ x, F x = ((Complex.normSq A.det ^ m : ℝ) : ℂ) * ∫ y, F (mulR A y)

end PositivityTheory.Rg.Sw.AbsSt.SDM
end
end

section

noncomputable section

open MeasureTheory Matrix Set Filter Topology

namespace PositivityTheory.Rg.Sw.AbsSt

open PositivityTheory.Rg.Sw

variable {m n : ℕ}

def NDer : Prop := ∀ (m n : ℕ) (ε : Fin m → Bool) (c t : ℝ) (p q : ℕ) (e : ℤ) (sL : PX m n →ₗ[ℂ] (GR n → ℂ))
  (ρ : GR n → PX m n →ₗ[ℂ] PX m n), LocData ε c t p q e sL ρ → ∀ (R : PX m n) (H : Matrix (Fin n) (Fin n) ℂ),
    H.IsHermitian → ∀ f : ℝ → GR n, (∀ σ : ℝ, mR (f σ) = nU ((σ : ℂ) • H)) → ∀ g : GR n,
      (mR g).toBlocks₂₁.det ≠ 0 → ∀ s : ℝ, HasDerivAt (fun σ : ℝ => sL R (g * f σ)) (sL (DN ε t H R) (g * f s)) s

def MDer : Prop := ∀ (m n : ℕ) (ε : Fin m → Bool) (c t : ℝ) (p q : ℕ) (e : ℤ) (sL : PX m n →ₗ[ℂ] (GR n → ℂ))
  (ρ : GR n → PX m n →ₗ[ℂ] PX m n), LocData ε c t p q e sL ρ → ∀ (R : PX m n) (H : Matrix (Fin n) (Fin n) ℂ),
    H.IsHermitian → ∀ f : ℝ → GR n,
      (∀ σ : ℝ, mR (f σ) = fromBlocks (NormedSpace.exp ((σ : ℂ) • H)) 0 0 (NormedSpace.exp (-((σ : ℂ) • H)))) →
      ∀ g : GR n, (mR g).toBlocks₂₁.det ≠ 0 → ∀ s : ℝ,
        HasDerivAt (fun σ : ℝ => sL R (g * f σ)) (sL (DM ε c H R) (g * f s)) s

end PositivityTheory.Rg.Sw.AbsSt
end
end

section

noncomputable section

open MeasureTheory Matrix Set Filter Topology
open scoped NNReal

namespace PositivityTheory.Rg.Sw.AbsSt.Far

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.AbsSt

variable {m n : ℕ} {ε : Fin m → Bool} {c t : ℝ} {p q : ℕ} {e : ℤ} {sL : PX m n →ₗ[ℂ] (GR n → ℂ)}
  {ρ : GR n → PX m n →ₗ[ℂ] PX m n}

theorem sL_bound (hI : Iwa) (hM : Mult) (hD : CayleyBlocksInvertible) (hL : LocData ε c t p q e sL ρ) (Q : PX m n) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y : GR n, ‖sL Q y‖ ≤ C * ‖F0 p q e y‖ := by
  have hK := isCompact_KR (n := n)
  have hs : Continuous (sL Q) := hL.cont Q
  have hF : Continuous (F0 (n := n) p q e) := continuous_weight_factor hD p q e
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn hs.continuousOn
  have hne : ((KR n : Subgroup (GR n)) : Set (GR n)).Nonempty := ⟨1, (KR n).one_mem⟩
  obtain ⟨k0, -, hmin⟩ := hK.exists_isMinOn hne hF.norm.continuousOn
  set δ := ‖F0 p q e k0‖ with hδdef
  have hδ : 0 < δ := norm_pos_iff.mpr (weight_factor_ne_zero hD p q e k0)
  refine ⟨max B 0 / δ, div_nonneg (le_max_right _ _) hδ.le, fun y => ?_⟩
  obtain ⟨u, k, hu, hk, rfl⟩ := hI n y
  have hmk : δ ≤ ‖F0 p q e k‖ := hmin hk
  calc ‖sL Q (u * k)‖ = ‖F0 p q e u‖ * ‖sL Q k‖ := by rw [hL.law Q u k hu, norm_mul]
    _ ≤ ‖F0 p q e u‖ * max B 0 :=
        mul_le_mul_of_nonneg_left ((hB k hk).trans (le_max_left _ _)) (norm_nonneg _)
    _ = (max B 0 / δ) * (‖F0 p q e u‖ * δ) := by field_simp
    _ ≤ (max B 0 / δ) * (‖F0 p q e u‖ * ‖F0 p q e k‖) := by gcongr
    _ = (max B 0 / δ) * ‖F0 p q e (u * k)‖ := by rw [((hM n p q e).1 u k hk).1, norm_mul]

theorem rpow_le_add {a x₁ x₂ s : ℝ} (ha : 0 < a) (h₁ : x₁ ≤ s) (h₂ : s ≤ x₂) : a ^ s ≤ a ^ x₁ + a ^ x₂ := by
  rcases le_total 1 a with h | h
  · exact (Real.rpow_le_rpow_of_exponent_le h h₂).trans (le_add_of_nonneg_left (Real.rpow_nonneg ha.le _))
  · exact (Real.rpow_le_rpow_of_exponent_ge ha h h₁).trans (le_add_of_nonneg_right (Real.rpow_nonneg ha.le _))

section Glob

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
  [SecondCountableTopology G] {Pp Γ : Subgroup G} {ι : GR n →* G} {s₀ : ℂ} {Ht : G → ℝ≥0}
  {sec I : PX m n →ₗ[ℂ] (G → ℂ)} {Λ : Set ((G → ℂ) → ℂ)}

theorem Ht_pos (hD : CayleyBlocksInvertible) (hG : GlobData ε c sL ρ G Pp Γ ι s₀ Ht sec I Λ) (x : G) : 0 < (Ht x : ℝ) := by
  obtain ⟨x₀, y, S, r, hr, rfl, h⟩ := hG.split x
  rw [(h y).1]
  exact mul_pos hr (hLoc_pos hD y)

theorem sec_bound (hI : Iwa) (hM : Mult) (hD : CayleyBlocksInvertible) (hL : LocData ε c t p q e sL ρ)
    (hG : GlobData ε c sL ρ G Pp Γ ι s₀ Ht sec I Λ) (Q : PX m n) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : G, ‖sec Q x‖ ≤ C * ‖sec 1 x‖ := by
  obtain ⟨C, hC0, hC⟩ := sL_bound hI hM hD hL Q
  refine ⟨C, hC0, fun x => ?_⟩
  obtain ⟨x₀, y, S, r, hr, rfl, h⟩ := hG.split x
  rw [(h y).2 Q, (h y).2 1, hL.vac y, norm_mul, norm_mul]
  calc ‖S‖ * ‖sL Q y‖ ≤ ‖S‖ * (C * ‖F0 p q e y‖) := mul_le_mul_of_nonneg_left (hC y) (norm_nonneg _)
    _ = C * (‖S‖ * ‖F0 p q e y‖) := by ring

theorem norm_hz (hD : CayleyBlocksInvertible) (hG : GlobData ε c sL ρ G Pp Γ ι s₀ Ht sec I Λ) (z : ℂ) (Q : PX m n) (x : G) :
    ‖hz Ht sec s₀ z Q x‖ = (Ht x : ℝ) ^ (z.re - s₀.re) * ‖sec Q x‖ := by
  unfold hz
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (Ht_pos hD hG x), Complex.sub_re]

end Glob

end PositivityTheory.Rg.Sw.AbsSt.Far
end
end

section

noncomputable section

open MeasureTheory Matrix Set Filter Topology
open scoped NNReal

namespace PositivityTheory.Rg.Sw.AbsSt.Far

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.AbsSt

variable {m n : ℕ} {ε : Fin m → Bool} {c t : ℝ} {p q : ℕ} {e : ℤ} {sL : PX m n →ₗ[ℂ] (GR n → ℂ)}
  {ρ : GR n → PX m n →ₗ[ℂ] PX m n}
  {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
  [SecondCountableTopology G] {Pp Γ : Subgroup G} {ι : GR n →* G} {s₀ : ℂ} {Ht : G → ℝ≥0}
  {sec I : PX m n →ₗ[ℂ] (G → ℂ)} {Λ : Set ((G → ℂ) → ℂ)}

theorem split_mul (x₀ : G) (y k : GR n) : x₀ * ι y * ι k = x₀ * ι (y * k) := by
  rw [mul_assoc, ← map_mul]

theorem cont_hz (hD : CayleyBlocksInvertible) (hL : LocData ε c t p q e sL ρ) (hG : GlobData ε c sL ρ G Pp Γ ι s₀ Ht sec I Λ)
    (z : ℂ) (b : GR n) (x : G) : Continuous fun k : KR n => hz Ht sec s₀ z 1 (x * ι ((k : GR n) * b)) := by
  obtain ⟨x₀, y, S, r, hr, hx, h⟩ := hG.split x
  subst hx
  have hfun : (fun k : KR n => hz Ht sec s₀ z 1 (x₀ * ι y * ι ((k : GR n) * b))) =
      fun k : KR n => ((r * hLoc (y * ((k : GR n) * b)) : ℝ) : ℂ) ^ (z - s₀) *
        (S * sL 1 (y * ((k : GR n) * b))) := by
    funext k
    unfold hz
    rw [split_mul, (h _).1, (h _).2]
  rw [hfun]
  have hcy : Continuous fun k : KR n => y * ((k : GR n) * b) :=
    continuous_const.mul (continuous_subtype_val.mul continuous_const)
  refine Continuous.mul ?_ (continuous_const.mul ((hL.cont 1).comp hcy))
  refine Continuous.cpow ?_ continuous_const
    (fun k => Complex.ofReal_mem_slitPlane.2 (mul_pos hr (hLoc_pos hD _)))
  exact Complex.continuous_ofReal.comp (continuous_const.mul ((continuous_hLoc hD).comp hcy))

theorem pointId [MeasurableSpace (KR n)] (hD : CayleyBlocksInvertible) (hL : LocData ε c t p q e sL ρ)
    (hG : GlobData ε c sL ρ G Pp Γ ι s₀ Ht sec I Λ) {ν : Measure (KR n)} {κ : KR n → ℂ} {N : ℕ}
    {yy : Fin N → GR n} {QQ : Fin N → PX m n} {M : ℂ → Matrix (Fin N) (Fin N) ℂ}
    (hMid : ∀ (w : ℂ) (i : Fin N) (y' : GR n), ∫ k, κ k * ((hLoc (y' * (k : GR n) * yy i) : ℂ) ^ w *
        F0 p q e (y' * (k : GR n) * yy i)) ∂ν = (hLoc y' : ℂ) ^ w * ∑ j, M w i j * sL (QQ j) y')
    (z : ℂ) (i : Fin N) (x : G) :
    ∫ k, κ k * hz Ht sec s₀ z 1 (x * ι ((k : GR n) * yy i)) ∂ν = ∑ j, M (z - s₀) i j * hz Ht sec s₀ z (QQ j) x := by
  obtain ⟨x₀, y, S, r, hr, hx, h⟩ := hG.split x
  subst hx
  have key : ∀ (P : PX m n) (g : GR n), hz Ht sec s₀ z P (x₀ * ι g) =
      (r : ℂ) ^ (z - s₀) * S * ((hLoc g : ℂ) ^ (z - s₀) * sL P g) := by
    intro P g
    unfold hz
    rw [(h g).1, (h g).2, Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg hr.le (hLoc_pos hD g).le]
    ring
  have hx' : ∀ k : KR n, x₀ * ι y * ι ((k : GR n) * yy i) = x₀ * ι (y * (k : GR n) * yy i) := by
    intro k
    rw [split_mul, mul_assoc]
  simp_rw [hx', key, hL.vac]
  simp only [mul_left_comm (κ _) ((r : ℂ) ^ (z - s₀) * S)]
  rw [integral_const_mul, hMid (z - s₀) i y, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  ring

end PositivityTheory.Rg.Sw.AbsSt.Far
end
end
