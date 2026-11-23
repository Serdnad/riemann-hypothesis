module

public import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle007
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle031
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle037
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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

@[expose] public section

section

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem coprime_of_mod_one {g p : ℕ} (h : g % p = 1) : Nat.Coprime g p := by
  unfold Nat.Coprime
  rw [Nat.gcd_comm, Nat.gcd_rec, h, Nat.gcd_one_left]

theorem g_coprime_ram (D : D7) (k : Fin 2) (p : ℕ) (hp : p ∈ ({2, D.host.q, D.host.d} : Finset ℕ)) :
    Nat.Coprime (D.host.g k) p := by
  have hc := D.ntypes.g_cond k
  have hq8 := D.host.hyp.2.2.1
  have hd16 := D.host.hyp.2.2.2.1
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp
  apply coprime_of_mod_one
  rcases hp with rfl | rfl | rfl
  · have h2 : 2 ∣ D.host.QS := (dvd_pow_self 2 (Nat.succ_ne_zero _)).trans D.host.tower_dvd
    rw [← Nat.mod_mod_of_dvd _ (show 2 ∣ D.host.QS * D.host.q * D.host.d from
      (h2.mul_right _).mul_right _), hc]
  · rw [← Nat.mod_mod_of_dvd _ (show D.host.q ∣ D.host.QS * D.host.q * D.host.d from
      ⟨D.host.QS * D.host.d, by ring⟩), hc]
    exact Nat.mod_eq_of_lt (by omega)
  · rw [← Nat.mod_mod_of_dvd _ (show D.host.d ∣ D.host.QS * D.host.q * D.host.d from
      ⟨D.host.QS * D.host.q, by ring⟩), hc]
    exact Nat.mod_eq_of_lt (by omega)

theorem sum_extendByZero_le_sum {p : ℕ} (f : Fin p → ℕ) (m : ℕ) : ∑ i : Fin m, ext0 f i ≤ ∑ i, f i := by
  unfold ext0
  have e1 : ∑ i : Fin m, (if h : (i : ℕ) < p then f ⟨i, h⟩ else 0) =
      ∑ i ∈ Finset.range m, (if h : i < p then f ⟨i, h⟩ else 0) :=
    Fin.sum_univ_eq_sum_range (fun i => if h : i < p then f ⟨i, h⟩ else 0) m
  have e2 : ∑ i : Fin p, f i = ∑ i ∈ Finset.range p, (if h : i < p then f ⟨i, h⟩ else 0) := by
    rw [← Fin.sum_univ_eq_sum_range (fun i => if h : i < p then f ⟨i, h⟩ else 0) p]
    exact Finset.sum_congr rfl fun i _ => by rw [dite_eq_left i.2]
  rw [e1, e2, ← Finset.sum_filter_add_sum_filter_not (Finset.range m) (fun i => i < p)]
  have e3 : ∑ i ∈ (Finset.range m).filter (fun i => ¬ i < p), (if h : i < p then f ⟨i, h⟩ else 0) = 0 :=
    Finset.sum_eq_zero fun i hi => dif_neg (Finset.mem_filter.mp hi).2
  rw [e3, add_zero]
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (fun i hi => Finset.mem_range.mpr (Finset.mem_filter.mp hi).2) (fun _ _ _ => Nat.zero_le _)


open Classical in
theorem DF_wtA_le {D : D7} (T : Top D) (j : ℕ) (w : WeightFamilies.Wt D j) :
    Formalism.L2.Pj.DF (T.Q.Dw j) (wtA w) ≤ Formalism.MainNotions.WeightAlgebra.DF w := by
  show ∑ τ : D.host.E →+* ℂ, ∑ i : Fin ((T.Q.Dw j).mult τ), wtA w (τ, (i : ℕ)) ≤
    ∑ t, ((∑ i, w.aP t i) + ∑ i, w.aM t i)
  have hsw : ∀ τ : D.host.E →+* ℂ, ∑ i : Fin ((T.Q.Dw j).mult τ), wtA w (τ, (i : ℕ)) =
      ∑ t : D.what₂.Tau, ((if τ = DV.tauEmb D t then ∑ i : Fin ((T.Q.Dw j).mult τ), ext0 (w.aP t) (i : ℕ) else 0) +
        if τ = conjEmb (DV.tauEmb D t) then ∑ i : Fin ((T.Q.Dw j).mult τ), ext0 (w.aM t) (i : ℕ) else 0) := by
    intro τ
    simp only [wtA]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [Finset.sum_add_distrib]
    split_ifs <;> simp
  rw [Finset.sum_congr rfl fun τ _ => hsw τ, Finset.sum_comm]
  refine Finset.sum_le_sum fun t _ => ?_
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq']
  simp only [Finset.mem_univ, if_true]
  exact add_le_add (sum_extendByZero_le_sum _ _) (sum_extendByZero_le_sum _ _)

end ReciprocityTheory.ChartRestriction.G.PullbackSections
end
end

section

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor

def GamAt {D : D7} (T : Top D) : Prop :=
  ∀ (j : ℕ) (_hj : InR D j) (σ : T.Q.c.F →+* ℂ), GoodEmb T.Q.c σ → ∀ (k : (T.U j σ).Comp)
    (γ : GL (Fin D.R.r) D.host.E), IsUStab ((T.U j σ).X k).Gm ((T.U j σ).X k).Λ γ →
    (∀ x ∈ ((T.U j σ).X k).Λ, ∃ y ∈ ((T.U j σ).X k).Λ,
      Matrix.mulVec (γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E) x - x = (T.Q.l.M : D.host.E) • y) →
    γ ∈ ((T.U j σ).X k).Γ

def HalfDiffNormSt : Prop :=
  ∀ D : D7, 0 < Ideal.absNorm D.host.𝔟 ∧
    2 * Real.log (Ideal.absNorm D.host.𝔟 : ℝ) ≤ Real.log |((NumberField.discr D.host.E : ℤ) : ℝ)|

end ReciprocityTheory.ChartRestriction.G.PullbackSections
end
end

section

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ}

def netNorm (U : Unf Xo c σ r) (la : ∀ k, Wt (U.X k).Ψ r) (NN : Finset (FPt U.X)) (P : FDSec U.X) : ℝ :=
  Real.sqrt ((NN.card : ℝ)⁻¹ * ∑ p ∈ NN, ((U.X p.1).pnorm (la p.1) (P p.1) p.2) ^ 2)

def NnOf (U : Unf Xo c σ r) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (NN : Finset (FPt U.X)) (f : Rul Xo c) : ℝ :=
  dmet n (Module.finrank ℚ E / 2) r * netNorm U (laU U a n) NN (rdU U f)

def IsNet (U : Unf Xo c σ r) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (NN : Finset (FPt U.X)) : Prop :=
  NN.Nonempty ∧ ∀ P ∈ holSub U.X (laU U a n),
    supN U.X (laU U a n) P ≤ 4 * Real.sqrt NN.card * netNorm U (laU U a n) NN P

def NetExistsSt : Prop :=
  ∃ Cn : ℝ, ∀ (D : D7) (T : Top D) (_h : LawsP T) (large₂ : SizeData₂ D) (j : ℕ) (_hj : InR D j) (ka : WeightFamilies.Wt D j)
    (σ : T.Q.c.F →+* ℂ), GoodEmb T.Q.c σ → SupBoundPageRows D large₂ ka →
    ∃ NN : Finset (FPt (T.U j σ).X), IsNet (T.U j σ) (wtA ka) ka.n NN ∧
      Real.log (16 * NN.card) ≤ Cn * Zb D large₂ ^ 3

set_option synthInstance.maxHeartbeats 400000 in
def AlgInjAtSt : Prop :=
  ∀ (D : D7) (T : Top D) (_h : LawsP T) (j : ℕ) (_hj : InR D j) (ka : WeightFamilies.Wt D j) (σ : T.Q.c.F →+* ℂ),
    GoodEmb T.Q.c σ → ∀ (m : ℕ) (f : Fin m → T.C j ka),
      LinearIndependent T.Q.c.F f → LinearIndependent ℂ (fun i => rdU (T.U j σ) (f i : T.R j))

end ReciprocityTheory.ChartRestriction.G.PullbackSections
end
end

section

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra

attribute [local instance 2000] Submodule.module

section Read

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ} {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r}

theorem readings_holomorphic_cuspForms (hM5 : SiegelSpaceAlgebra (E := E)) {σ : c.F →+* ℂ} (hσ : GoodEmb c σ)
    (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) : RdHolCusp σ (laU (U σ) a n) (rdC U σ a n) := by
  intro f
  have h0 : (f : Rul Xo c) ∈ cusp Xo c U a n := f.2
  have h1 := (Submodule.mem_inf.mp h0).2
  rw [Submodule.mem_iInf] at h1
  have h2 := h1 σ
  rw [Submodule.mem_iInf] at h2
  have hf : rdC U σ a n f ∈ holSub (U σ).X (laU (U σ) a n) := h2 hσ
  let K : Submodule ℂ (FDSec (U σ).X) :=
    { carrier := {P | IsHolCusp (U σ).X (laU (U σ) a n) P}
      zero_mem' := by
        intro k
        exact ((hM5 r ((U σ).X k) (laU (U σ) a n k) (laU (U σ) a n k) 0).1).1
      add_mem' := by
        intro P Q hP hQ k
        exact ((hM5 r ((U σ).X k) (laU (U σ) a n k) (laU (U σ) a n k) 0).1).2.1 _ (hP k) _ (hQ k)
      smul_mem' := by
        intro z P hP k
        exact ((hM5 r ((U σ).X k) (laU (U σ) a n k) (laU (U σ) a n k) 0).1).2.2 z _ (hP k) }
  have hle : holSub (U σ).X (laU (U σ) a n) ≤ K := Submodule.span_le.mpr (fun P hP => hP)
  exact hle hf

theorem rdC_mem_holSub {σ : c.F →+* ℂ} (hσ : GoodEmb c σ) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ)
    (f : cusp Xo c U a n) : rdC U σ a n f ∈ holSub (U σ).X (laU (U σ) a n) := by
  have h0 : (f : Rul Xo c) ∈ cusp Xo c U a n := f.2
  have h1 := (Submodule.mem_inf.mp h0).2
  rw [Submodule.mem_iInf] at h1
  have h2 := h1 σ
  rw [Submodule.mem_iInf] at h2
  exact h2 hσ

theorem rdC_mem_holSub0 {σ : c.F →+* ℂ} (hσ : GoodEmb c σ) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ)
    (f : cusp Xo c U a n) : rdC U σ a n f ∈ holSub0 (U σ).X (laU (U σ) a n) := by
  refine Submodule.mem_inf.mpr ⟨rdC_mem_holSub hσ a n f, ?_⟩
  intro k x hx
  simp [rdC, rdU, hx]

end Read

def JInjAt {D : D7} {T : Top D} (h : LawsP T) (j : ℕ) (hj : InR D j) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ)
    (hd : Dom a n) : Prop :=
  JInj (T.V j T.σ₀) T.σ₀ (rdC (T.U j) T.σ₀ a n) (T.dict j T.σ₀) (T.mu j T.σ₀) (h.cuspidalL2Subspace j hj T.σ₀ T.good_σ₀ a n hd)

def JInjRd {D : D7} (T : Top D) (j : ℕ) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ) : Prop :=
  IndepToC (rdC (T.U j) T.σ₀ a n)

end ReciprocityTheory.ChartRestriction.G.PullbackSections
end
end
