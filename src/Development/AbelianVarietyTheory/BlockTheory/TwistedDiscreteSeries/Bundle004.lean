module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.LinearAlgebra.Trace
import Mathlib.Algebra.Module.StablyFree.Basic
public import Mathlib.LinearAlgebra.Matrix.Rank
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel MeasureTheory Matrix

namespace GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets

section General

variable {G V : Type} [Group G] [MeasurableSpace G] [AddCommGroup V] [Module ℂ V]

def IsIntegralOp (μ : Measure G) (π : Representation ℂ G V) (f : G → ℂ) (A : V →ₗ[ℂ] V) : Prop :=
  ∀ (v : V) (l : Module.Dual ℂ V),
    Integrable (fun g => f g * l (π g v)) μ ∧ l (A v) = ∫ g, f g * l (π g v) ∂μ

theorem IsIntegralOp.unique {μ : Measure G} {π : Representation ℂ G V} {f : G → ℂ} {A B : V →ₗ[ℂ] V}
    (hA : IsIntegralOp μ π f A) (hB : IsIntegralOp μ π f B) : A = B := by
  ext v
  rw [← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff ℂ]
  intro l
  rw [map_sub, (hA v l).2, (hB v l).2, sub_self]

def HasFinTrace (A : V →ₗ[ℂ] V) (c : ℂ) : Prop :=
  FiniteDimensional ℂ (LinearMap.range A) ∧
    LinearMap.trace ℂ (LinearMap.range A)
      (A.restrict (p := LinearMap.range A) (q := LinearMap.range A)
        fun v _ => LinearMap.mem_range_self A v) = c

def HasTrace (μ : Measure G) (π : Representation ℂ G V) (f : G → ℂ) (c : ℂ) : Prop :=
  ∃ A : V →ₗ[ℂ] V, IsIntegralOp μ π f A ∧ HasFinTrace A c

theorem HasTrace.unique {μ : Measure G} {π : Representation ℂ G V} {f : G → ℂ} {c d : ℂ}
    (hc : HasTrace μ π f c) (hd : HasTrace μ π f d) : c = d := by
  obtain ⟨A, hA, -, rfl⟩ := hc
  obtain ⟨B, hB, -, rfl⟩ := hd
  obtain rfl := hA.unique hB
  rfl

end General

section Local

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  (n : Type) [Fintype n] [DecidableEq n] [LinearOrder n]

def unipO : Subgroup (GL n k) := unipB k n ⊓ KO k n

def unipLowerOne : Subgroup (GL n k) := unipBLower k n ⊓ KOne k n

variable {k n}

def Contracts (t : n → kˣ) : Prop :=
  (∀ u ∈ unipO k n, diagT k n t * u * (diagT k n t)⁻¹ ∈ unipO k n) ∧
    ∀ u ∈ unipLowerOne k n, (diagT k n t)⁻¹ * u * diagT k n t ∈ unipLowerOne k n

def deltaB (t : n → kˣ) : ℝ := ∏ i, ∏ j with i < j, nabs k (t i / t j)

theorem deltaB_pos (t : n → kˣ) : 0 < deltaB t :=
  Finset.prod_pos fun _ _ => Finset.prod_pos fun _ _ => nabs_pos' k _

theorem deltaB_eq_modulus (t : n → kˣ) :
    deltaB t = modulus k (fun _ : n => Unit) (leviTorus k n t) := (modulus_torus t).symm

def iwahoriCoset (t : n → kˣ) : Set (GL n k) :=
  {g | ∃ a ∈ iwahori k n, ∃ b ∈ iwahori k n, g = a * diagT k n t * b}

def cosetInd (t : n → kˣ) : GL n k → ℂ := (iwahoriCoset t).indicator fun _ => 1

variable {V : Type} [AddCommGroup V] [Module ℂ V]


open scoped Classical in
def IsExponents (π : Representation ℂ (GL n k) V) (E : Multiset ((n → kˣ) →* ℂˣ)) : Prop := by
  classical
  exact (∀ χ ∈ E, ∀ s ∈ torusO k n, χ s = 1) ∧ ∀ χ, (E.count χ : ℕ∞) = expMult π χ

variable (k n)

def DominantContracts : Prop :=
  ∀ (ϖ : kˣ), valuation k (ϖ : k) = uniformizer k → ∀ a : n → ℤ, Antitone a → Contracts fun i => ϖ ^ a i

def TraceFormula : Prop :=
  ∀ [MeasurableSpace (GL n k)] [BorelSpace (GL n k)] (μ : Measure (GL n k)) [μ.IsHaarMeasure]
    (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL n k) V), IsAdmissible π →
    FiniteDimensional ℂ (fixed (jacBU π) (torusO k n)) ∧
    (∀ t : n → kˣ, Contracts t →
      HasTrace μ π (cosetInd t)
        ((μ.real (iwahori k n : Set (GL n k)) : ℂ) * ((deltaB t : ℂ))⁻¹ *
          LinearMap.trace ℂ (fixed (jacBU π) (torusO k n)) (jacBUFixed π t))) ∧
    ∃ E : Multiset ((n → kˣ) →* ℂˣ), IsExponents π E ∧
      ∀ t : n → kˣ, Contracts t →
        HasTrace μ π (cosetInd t)
          ((μ.real (iwahori k n : Set (GL n k)) : ℂ) * ((deltaB t : ℂ))⁻¹ *
            (E.map fun χ => (χ t : ℂ)).sum)

end Local

def IwahoriTrace : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (r : ℕ),
    DominantContracts k (Fin r) ∧ TraceFormula k (Fin r)

end GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets
end
end

section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL Matrix

namespace GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences

def sbRep {Γ X : Type} [Group Γ] [TopologicalSpace X] (r : X → Γ → X) (h1 : ∀ x, r x 1 = x)
    (hm : ∀ x g h, r x (g * h) = r (r x g) h) (hc : ∀ g, Continuous fun x => r x g) :
    Representation ℂ Γ (SB X) where
  toFun g :=
    { toFun := fun f => ⟨fun x => f.1 (r x g), f.2.1.comp_continuous (hc g),
        f.2.2.comp_homeomorph
          { toFun := fun x => r x g
            invFun := fun x => r x g⁻¹
            left_inv := fun x => by simp only [← hm, mul_inv_cancel, h1]
            right_inv := fun x => by simp only [← hm, inv_mul_cancel, h1]
            continuous_toFun := hc g
            continuous_invFun := hc g⁻¹ }⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  map_one' := LinearMap.ext fun f => Subtype.ext (funext fun x => congrArg f.1 (h1 x))
  map_mul' g h := LinearMap.ext fun f => Subtype.ext (funext fun x => congrArg f.1 (hm x g h))

section Ind

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {a b n Γ W : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Fintype n] [DecidableEq n]
  [Group Γ] [AddCommGroup W] [Module ℂ W]

def actFst (τ : Representation ℂ (Γ × (GL a k × GL b k)) W) (γ : Γ) :
    Representation.IntertwiningMap
      (MonoidHom.comp (τ.comp (MonoidHom.inr Γ _)) (leviTwo k a b).symm.toMonoidHom)
      (MonoidHom.comp (τ.comp (MonoidHom.inr Γ _)) (leviTwo k a b).symm.toMonoidHom) where
  toLinearMap := τ (γ, 1)
  isIntertwining' m := by
    show τ (γ, 1) * τ (1, _) = τ (1, _) * τ (γ, 1)
    rw [← map_mul, ← map_mul]
    simp

def indSnd (e : a ⊕ b ≃ n) (τ : Representation ℂ (Γ × (GL a k × GL b k)) W) :
    Representation ℂ (Γ × GL n k)
      (IndSp (two e) (MonoidHom.comp (τ.comp (MonoidHom.inr Γ _)) (leviTwo k a b).symm.toMonoidHom)) where
  toFun g := (parIndMap (two e) (actFst τ g.1)).toLinearMap ∘ₗ ind₂ e (τ.comp (MonoidHom.inr Γ _)) g.2
  map_one' := LinearMap.ext fun f => Subtype.ext (Subtype.ext (funext fun x => by
    show τ (1 : Γ × (GL a k × GL b k)) (f.1.1 (x * 1)) = f.1.1 x
    simp))
  map_mul' g h := LinearMap.ext fun f => Subtype.ext (Subtype.ext (funext fun x => by
    show τ (g.1 * h.1, 1) (f.1.1 (x * (g.2 * h.2))) = τ (g.1, 1) (τ (h.1, 1) (f.1.1 (x * g.2 * h.2)))
    rw [← Module.End.mul_apply, ← map_mul, mul_assoc]
    simp))

theorem indSnd_inr (e : a ⊕ b ≃ n) (τ : Representation ℂ (Γ × (GL a k × GL b k)) W) (h : GL n k) :
    indSnd e τ (1, h) = ind₂ e (τ.comp (MonoidHom.inr Γ _)) h :=
  LinearMap.ext fun f => Subtype.ext (Subtype.ext (funext fun x => by
    show τ (1 : Γ × (GL a k × GL b k)) (f.1.1 (x * h)) = f.1.1 (x * h)
    simp))

end Ind

section Model

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

def act (x : Matrix b a k) (γ : GL a k × GL b k) : Matrix b a k := (γ.2⁻¹ : GL b k).val * x * γ.1.val

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem act_one (x : Matrix b a k) : act x 1 = x := by simp [act]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem act_mul (x : Matrix b a k) (γ δ : GL a k × GL b k) : act x (γ * δ) = act (act x γ) δ := by
  simp only [act, Prod.fst_mul, Prod.snd_mul, _root_.mul_inv_rev, Units.val_mul, Matrix.mul_assoc]

theorem continuous_act (γ : GL a k × GL b k) : Continuous fun x : Matrix b a k => act x γ :=
  (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const


omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem rank_act (x : Matrix b a k) (γ : GL a k × GL b k) : (act x γ).rank = x.rank := by
  unfold act
  rw [rank_mul_eq_left_of_isUnit_det _ _ ((isUnit_iff_isUnit_det _).1 γ.1.isUnit),
    rank_mul_eq_right_of_isUnit_det _ _ ((isUnit_iff_isUnit_det _).1 (γ.2⁻¹).isUnit)]

variable (a b)

def omChar (μ : kˣ →* ℂˣ) : GL a k × GL b k →* ℂˣ :=
  (detChar a (μ⁻¹ * absPow k ((Fintype.card b : ℂ) / 2))).comp (MonoidHom.fst _ _) *
    (detChar b (μ * absPow k (-(Fintype.card a : ℂ) / 2))).comp (MonoidHom.snd _ _)

def omega (μ : kˣ →* ℂˣ) : Representation ℂ (GL a k × GL b k) (SB (Matrix b a k)) :=
  twist (sbRep act act_one act_mul continuous_act) (omChar a b μ)


variable (k) in
abbrev RankIn (s : Set ℕ) : Type := {x : Matrix b a k // x.rank ∈ s}

def omegaOn (μ : kˣ →* ℂˣ) (s : Set ℕ) : Representation ℂ (GL a k × GL b k) (SB (RankIn (k := k) (a := a) (b := b) s)) :=
  twist (sbRep (fun x γ => ⟨act x.1 γ, by rw [rank_act]; exact x.2⟩)
    (fun x => Subtype.ext (act_one x.1)) (fun x γ δ => Subtype.ext (act_mul x.1 γ δ))
    (fun γ => ((continuous_act γ).comp continuous_subtype_val).subtype_mk _)) (omChar a b μ)

variable {a b}

theorem omegaOn_apply (μ : kˣ →* ℂˣ) (s : Set ℕ) (γ : GL a k × GL b k) (Φ : SB (RankIn (k := k) (a := a) (b := b) s))
    (x : RankIn (k := k) (a := a) (b := b) s) :
    (omegaOn a b μ s γ Φ).1 x =
      (omChar a b μ γ : ℂ) * Φ.1 ⟨act x.1 γ, by rw [rank_act]; exact x.2⟩ := rfl


variable (a b) in
def filt (μ : kˣ →* ℂˣ) (s : Set ℕ) (κ : ℕ) : Subrepresentation (omegaOn a b μ s) where
  toSubmodule :=
    { carrier := {Φ | ∀ x : RankIn (k := k) (a := a) (b := b) s, x.1.rank < κ → Φ.1 x = 0}
      add_mem' := fun {f g} hf hg x hx => by
        show f.1 x + g.1 x = 0
        rw [hf x hx, hg x hx, add_zero]
      zero_mem' := fun _ _ => rfl
      smul_mem' := fun c f hf x hx => by
        show c * f.1 x = 0
        rw [hf x hx, mul_zero] }
  apply_mem_toSubmodule γ Φ hΦ x hx := by
    rw [omegaOn_apply, hΦ _ (by rwa [rank_act]), mul_zero]



end Model

section Statement

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

end Statement

end GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences
end
end
