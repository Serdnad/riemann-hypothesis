module

public import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle004
public import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle007
public import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle006
public import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle005
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
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Topology.Sheaves.Init
import Mathlib.Topology.UniformSpace.Uniformizable

@[expose] public section

section

noncomputable section

namespace GlobalTheory.ThK.Dbl

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {a a' : ℕ}
  {B : Base F E} {G : Geo σ a a'} {X : Chars F E} {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W}

theorem hecke_div {χ χ' : Chr F E} (h : IsHecke F E χ) (h' : IsHecke F E χ') : IsHecke F E (χ / χ') :=
  ⟨h.1.div' h'.1, fun x => by rw [MonoidHom.div_apply, h.2, h'.2, div_one]⟩

theorem res_div {K : Subgroup (AF F)ˣ} {χ χ' : Chr F E} {m n k : ℕ} (h : ResEtaPow K χ m) (h' : ResEtaPow K χ' n)
    (e : k = m + n) : ResEtaPow K (χ / χ') k := fun x => by
  rw [MonoidHom.div_apply, Circle.coe_div, h, h', e]
  split_ifs
  · simp
  · rw [pow_add, div_eq_mul_inv, ← inv_pow, inv_neg, inv_one]

theorem pairV (h : IsTriple B G X om om') :
    IsPair B G.M X.β (X.β / X.α) om (a - G.p) G.p (a + a' - (G.p + G.q)) (G.p + G.q) :=
  ⟨h.base, h.geo.hV, h.geo.hW, h.geo.hM, h.chars.heckeβ, hecke_div h.chars.heckeβ h.chars.heckeα, h.chars.resβ,
    res_div h.chars.resβ h.chars.resα rfl, h.weil⟩

theorem pairV' (h : IsTriple B G X om om') :
    IsPair B G.M' X.α (X.α / X.β) om' G.q (a' - G.q) (a + a' - (G.p + G.q)) (G.p + G.q) :=
  ⟨h.base, h.geo.hV', h.geo.hW, h.geo.hM', h.chars.heckeα, hecke_div h.chars.heckeα h.chars.heckeβ, h.chars.resα,
    res_div h.chars.resα h.chars.resβ (add_comm _ _), h.weil'⟩

theorem split_zero {W : Spc F E (a + a')} {d₁ : ℕ} (W₁ : Spc F E d₁) (H' : Plane E (a + a') d₁) (X : Chars F E) :
    Split2 (σ := σ) (W := W) W₁ H' X 0 0 0 :=
  ⟨fun _ _ _ _ _ _ => by simp, fun _ _ _ _ => by simp, fun _ _ _ _ => by simp⟩

theorem big_of (hB : NonZeroBot) (hT : TowerB) (hE : EvZero) (hC : CTBigZero) (hS : SchToPol) (hP : PolSch) (hL : LeviEx) (q : ℕ) :
    ∀ (a' : ℕ) (G : Geo σ a a') (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' → G.p = 0 → G.q = q →
      ∃ Φ ∈ PolData B G.M, G.M.I om Φ ≠ 0 := by
  induction q with
  | zero => exact fun a' G om om' h hp hq => (hB F E σ B a a' G X om om' h hp hq).1
  | succ q ih =>
    intro a' G om om' h hp hq
    obtain ⟨b, rfl⟩ : ∃ b, a' = b + 2 := ⟨a' - 2, by have := h.geo.aBig; omega⟩
    obtain ⟨V, V', W, h', G₁, H, H', c, om₁, om₁', h₁⟩ := hT F E σ B a b G X om om' h (by omega)
    obtain ⟨Φ₁, p1, n1⟩ := ih b G₁ om₁ om₁' h₁ (c.ep.trans hp) (by have : G₁.q + 1 = G.q := c.eq; omega)
    obtain ⟨⟨e, he⟩, he'⟩ := hE F E σ B _ _ _ _ _ _ _ _ _ _ _ _ (pairV h') _ G₁.V G₁.W H' _ _ G₁.M c.eV c.hH' h₁.geo.hM
    obtain ⟨Φ, p2, rfl⟩ := Submodule.mem_map.1 ((he' e he).ge p1)
    obtain ⟨C, hC0, hc⟩ := hC F E σ B a b _ G₁ H H' c e he
    by_contra hn
    push Not at hn
    have z : G.M.I om Φ = 0 := hS F E σ B _ _ _ _ _ _ _ _ _ _ _ _ (pairV h) (by omega) hn Φ
      (hP F E σ B _ _ _ _ _ _ _ _ _ _ _ _ (pairV h') Φ p2)
    refine n1 (funext fun g => ?_)
    obtain ⟨m, hm⟩ := hL F E σ B _ _ _ _ H' _ _ _ _ h.base h'.geo.hW c.hH' g
    have := hc X om om' om₁ om₁' h' h₁ Φ p2 0 0 (by
      show Split2 _ _ _ (G.M.I om Φ) 0 0
      rw [z]; exact split_zero _ _ _) g m hm 1
    have o : om (1, 1) Φ = Φ := DFunLike.congr_fun (map_one om) Φ
    erw [o] at this
    exact (mul_eq_zero.1 this.symm).resolve_left hC0

theorem small_of (hB : NonZeroBot) (hT : TowerA) (hE : EvZero) (hC : CTSmallZero) (hS : SchToPol) (hP : PolSch) (hL : LeviEx)
    (hZ : SplitEx) (p : ℕ) :
    ∀ (a : ℕ) (G : Geo σ a a') (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' → G.p = p → G.q = 0 →
      ∃ Φ ∈ PolData B G.M', G.M'.I om' Φ ≠ 0 := by
  induction p with
  | zero => exact fun a G om om' h hp hq => (hB F E σ B a a' G X om om' h hp hq).2
  | succ p ih =>
    intro a G om om' h hp hq
    obtain ⟨b, rfl⟩ : ∃ b, a = b + 2 := ⟨a - 2, by have := h.geo.aBig; have := h.geo.lt; omega⟩
    obtain ⟨V, V', W, h', G₁, H, H', c, om₁, om₁', h₁⟩ := hT F E σ B b a' G X om om' h hq (by omega)
    obtain ⟨Φ₁, p1, n1⟩ := ih b G₁ om₁ om₁' h₁ (by have : G₁.p + 1 = G.p := c.ep; omega) c.q1
    obtain ⟨⟨e, he⟩, he'⟩ := hE F E σ B _ _ _ _ _ _ _ _ _ _ _ _ (pairV' h') _ G₁.V' G₁.W H' _ _ G₁.M' c.eV c.hH' h₁.geo.hM'
    obtain ⟨Φ, p2, rfl⟩ := Submodule.mem_map.1 ((he' e he).ge p1)
    obtain ⟨C, hC0, hc⟩ := hC F E σ B b a' _ G₁ H H' c e he
    by_contra hn
    push Not at hn
    have z : G.M'.I om' Φ = 0 := hS F E σ B _ _ _ _ _ _ _ _ _ _ _ _ (pairV' h) (by omega) hn Φ
      (hP F E σ B _ _ _ _ _ _ _ _ _ _ _ _ (pairV' h') Φ p2)
    refine n1 (funext fun g => ?_)
    obtain ⟨m, hm⟩ := hL F E σ B _ _ _ _ H' _ _ _ _ h.base h'.geo.hW c.hH' g
    obtain ⟨fa, s1, s2⟩ := hc X om om' om₁ om₁' h' h₁ Φ p2
    have s3 : Split2 G₁.W H' X (G.M'.I om' Φ) fa 0 := s1
    rw [z] at s3
    have i0 : (reG G V V' W).M.I om 0 = 0 := funext fun x => by simp [Model.I, theta, thetaSum]
    have fz : fa = 0 := congrArg Prod.fst (((hZ F E σ B _ _ (reG G V V' W) X om om' h' _ G₁.W H' _ _ c.hH').1 0 (zero_mem _)).unique
      (y₁ := (fa, 0)) (y₂ := (0, 0)) (by rw [i0]; exact s3) (by rw [i0]; exact split_zero _ _ _))
    have := s2 g m hm 1
    have o : om' (1, 1) Φ = Φ := DFunLike.congr_fun (map_one om') Φ
    erw [fz, o] at this
    exact (mul_eq_zero.1 this.symm).resolve_left hC0

theorem nonZeroAn_of (hB : NonZeroBot) (hA : TowerA) (hT : TowerB) (hE : EvZero) (hC : CTBigZero) (hC' : CTSmallZero)
    (hS : SchToPol) (hP : PolSch) (hL : LeviEx) (hZ : SplitEx) (hO : ToSo) : NonZeroAn := by
  intro F E _ _ _ _ _ σ B a a' G X om om' h
  refine ⟨fun hp => big_of hB hT hE hC hS hP hL _ a' G om om' h hp rfl, fun hq => ?_⟩
  obtain ⟨Φ, p1, n1⟩ := small_of hB hA hE hC' hS hP hL hZ _ a G om om' h rfl hq
  obtain ⟨Ψ, p2, e⟩ := hO F E σ B a a' G X om om' h hq Φ p1
  exact ⟨Ψ, p2, e ▸ n1⟩

end GlobalTheory.ThK.Dbl

end
end

section

noncomputable section

namespace GlobalTheory.ThK.Dbl

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ} {Y : Spc F E n}

def SiegelWeilAniso : Prop := SWAniso ∧ SWAnisoX


variable (σ Y) in
def IsFrame2 (b : GL (Fin n ⊕ Fin n) E) : Prop :=
  (∃ ε : ℤˣ, b.1ᵀ * dbl Y.J * b.1.map σ = Matrix.fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0) ∧
    ∃ t : GL (Fin n) E, b.1.toCols₁ = diagCols (Fin n) * t.1


variable (F E) in
def intHat : AddSubgroup (AE F E) :=
  AddSubgroup.closure {z | ∃ a : AF F, evI F a = 0 ∧ (∀ v, evFin F v a ∈ v.adicCompletionIntegers F) ∧
    ∃ o : 𝓞 E, z = a • inclR (F := F) (AF F) (o : E)}


variable (F) in
def finOne : AF F := LinearMap.inr F (Ainf F) (Af F) 1

def inFrame (b : GL (Fin n ⊕ Fin n) E) (x : G2 σ Y) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E) :=
  incM F (b⁻¹).1 * mat2 x * incM F b.1

def IsStdK (B : Base F E) (b : GL (Fin n ⊕ Fin n) E) (K : Subgroup (G2 σ Y)) : Prop :=
  ∀ k, k ∈ K ↔ (∀ w, (inFrame b k).map (piInf (B.emb w)) * ((inFrame b k).map (piInf (B.emb w)))ᴴ = 1) ∧
    ∀ k' ∈ ({k, k⁻¹} : Set (G2 σ Y)), ∀ i j, finOne F • inFrame b k' i j ∈ intHat F E


variable (σ Y) in
def modFun : Submodule ℂ (G2 σ Y → ℂ) :=
  Submodule.span ℂ {f | Continuous f ∧ ∃ N : ℕ, ∀ x, ‖f x‖ ≤ (ht2 x : ℝ) ^ N}

def IsGrowForm (μ : modFun σ Y →ₗ[ℂ] ℂ) : Prop :=
  ∀ N : ℕ, ∃ C : ℝ, ∀ f : modFun σ Y, (∀ x, ‖f.1 x‖ ≤ (ht2 x : ℝ) ^ N) → ‖μ f‖ ≤ C

def EisBL : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n : ℕ) (Y : Spc F E n) r s, B.IsGood σ → 1 ≤ n → (Y.IsHerm σ B r s ∨ Y.IsSkew σ B r s) →
    ∀ χ : Chr F E, IsHecke F E χ → ∀ c : ℕ, ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χ c →
    ∀ b K a, IsFrame2 σ Y b → IsStdK (σ := σ) (Y := Y) B b K → IsHgt K a → ∀ s₁ f, IsSec K χ s₁ f →
      ∃ Ê : ℂ → G2 σ Y → ℂ, (∃ t : ℝ, (∀ s : ℂ, t < s.re → ∀ x, HasSum (eisTerm (flat a f s₁ s) x) (Ê s x)) ∧
          ∀ x, DifferentiableOn ℂ (Ê · x) {s | t < s.re}) ∧
        ∀ s₀, ∃ (k : ℕ) (U : Set ℂ) (H : ℂ → modFun σ Y), U ∈ 𝓝 s₀ ∧ (∀ s ∈ U, s ≠ s₀ → ∀ x, (H s).1 x = (s - s₀) ^ k * Ê s x) ∧
          ∀ μ, IsGrowForm μ → DifferentiableOn ℂ (fun s => μ (H s)) U

def FrameConj : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n : ℕ) (Y : Spc F E n) r s, B.IsGood σ → (Y.IsHerm σ B r s ∨ Y.IsSkew σ B r s) →
    ∀ K, IsStab2 (σ := σ) (Y := Y) B K → ∃ b K₀ p t, IsFrame2 σ Y b ∧ IsStdK B b K₀ ∧ IsPar p t ∧ ∀ k, k ∈ K ↔ p⁻¹ * k * p ∈ K₀

end GlobalTheory.ThK.Dbl

end
end

section

noncomputable section

namespace GlobalTheory.ThK.Dbl

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

def Bump : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ),
    IsPair B M χX χW om r s r' s' → n ≤ d → ∀ v ∈ B.P, ∃ φ ∈ SB (Fin n × Fin d → Fv F v), φ ≠ 0 ∧ ∀ g ∈ UAt σ X (evFin F v),
      (IntAt v g ∧ Acts (evFin F v) (om (g, 1)) φ φ) ∨ ∃ (u : Matrix (Fin n) (Fin d) (AE F E)) (c c' : ℂ), At (evFin F v) u ∧ c ≠ c' ∧
        Acts (evFin F v) (M.co.rho B.ψ u) φ (c • φ) ∧ Acts (evFin F v) (M.co.rho B.ψ (mat g * u)) φ (c' • φ)

def VacFix2 : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) r s r' s', B.IsGood σ → X.IsHerm σ B r s →
    W.IsSkew σ B r' s' → M.IsGood B.ψ → ∀ χ : Chr F E, IsHecke F E χ → ∀ dd om, IsDblCoordX M dd →
    IsUWeilSplit (cA σ) (adeleClass F) B.ψ (-1) (incM F W.J) (dbl (incM F X.J)) dd χ (diagCols (Fin n)) om →
    ∀ K, IsStab2 (σ := σ) (Y := X) B K → ∀ v, (∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) = v → UnrAt χ w) →
    ∀ k ∈ K, At (evFin F v) (mat2 k - 1) →
      Acts (evFin F v) (om k) (boxFun (M.vac v) (star (M.vac v))) (boxFun (M.vac v) (star (M.vac v)))

end GlobalTheory.ThK.Dbl

end
end

section

noncomputable section

namespace GlobalTheory.ThK.Dbl.TC

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

section Box

variable {A B : Type} [TopologicalSpace A] [TopologicalSpace B]

def boxL : (SB A) ⊗[ℂ] (SB B) →ₗ[ℂ] (A × B → ℂ) :=
  TensorProduct.lift (LinearMap.mk₂ ℂ (fun a b z => a.1 z.1 * b.1 z.2) (fun _ _ _ => funext fun _ => add_mul _ _ _)
    (fun _ _ _ => funext fun _ => mul_assoc _ _ _) (fun _ _ _ => funext fun _ => mul_add _ _ _)
    fun _ _ _ => funext fun _ => mul_left_comm _ _ _)

theorem boxL_tmul (a : SB A) (b : SB B) : boxL (a ⊗ₜ[ℂ] b) = fun z => a.1 z.1 * b.1 z.2 := rfl

theorem boxL_ker : LinearMap.ker (boxL (A := A) (B := B)) = ⊥ := by
  classical
  refine LinearMap.ker_eq_bot'.2 fun x hx => ?_
  let e := Module.Basis.ofVectorSpace ℂ (SB A)
  obtain ⟨c, rfl⟩ := TensorProduct.eq_repr_basis_left e x
  have h : ∀ i ∈ c.support, c i = 0 := fun i hi => Subtype.ext (funext fun y => by
    refine linearIndependent_iff'.1 e.linearIndependent c.support (fun i => (c i).1 y) (Subtype.ext (funext fun z => ?_)) i hi
    have := congrFun hx (z, y)

    simp only [Finsupp.sum, map_sum, boxL_tmul, Finset.sum_apply] at this
    simpa [mul_comm] using this)
  exact Finset.sum_eq_zero fun i hi => by simp [h i hi]

theorem mem_range_boxL [T2Space A] [T2Space B] {f : A × B → ℂ} (hf : f ∈ SB (A × B)) : f ∈ LinearMap.range boxL := by
  classical
  have hK : IsCompact (tsupport f) := hf.2
  have z : ∀ x y, (x, y) ∉ tsupport f → f (x, y) = 0 := fun x y h => image_eq_zero_of_notMem_tsupport h
  have hl : IsLocallyConstant fun x y => f (x, y) := (IsLocallyConstant.iff_eventually_eq _).2 fun x => by
    have h1 := (hK.image continuous_snd).eventually_forall_of_forall_eventually (x₀ := x)
      (P := fun x' y => f (x', y) = f (x, y)) fun y _ => by
        have a := (IsLocallyConstant.iff_eventually_eq _).1 hf.1 (x, y)
        have b : ∀ᶠ w : A × B in 𝓝 (x, y), f (x, w.2) = f (x, y) :=
          (IsLocallyConstant.iff_eventually_eq _).1 (hf.1.comp_continuous (f := fun w : A × B => (x, w.2)) (by fun_prop)) (x, y)
        filter_upwards [a, b] with w h h' using h.trans h'.symm
    filter_upwards [h1] with x' h
    funext y
    by_cases hy : y ∈ Prod.snd '' tsupport f
    · exact h y hy
    · rw [z _ _ fun h => hy ⟨_, h, rfl⟩, z _ _ fun h => hy ⟨_, h, rfl⟩]
  have hfin : ((fun x y => f (x, y)) '' (Prod.fst '' tsupport f)).Finite := by
    letI : TopologicalSpace (B → ℂ) := ⊥
    haveI : DiscreteTopology (B → ℂ) := ⟨rfl⟩
    exact ((hK.image continuous_fst).image hl.continuous).finite_of_discrete
  have e : f = ∑ g ∈ hfin.toFinset, fun w : A × B =>
      Set.indicator {x | (fun y => f (x, y)) = g} (fun x => if g = 0 then (0 : ℂ) else 1) w.1 * g w.2 := funext fun w => by
    rw [Finset.sum_apply, Finset.sum_eq_single (fun y => f (w.1, y)) (fun g _ hg => by simp [hg.symm])]
    · by_cases h : (fun y => f (w.1, y)) = 0
      · simpa [h] using congrFun h w.2
      · simp [h]
    · intro h
      exact mul_eq_zero_of_right _ (z w.1 w.2 fun h' => h (hfin.mem_toFinset.2 ⟨_, ⟨_, h', rfl⟩, rfl⟩))
  rw [e]
  refine Submodule.sum_mem _ fun g hg => ?_
  obtain ⟨x, -, rfl⟩ := hfin.mem_toFinset.1 hg
  refine ⟨(⟨_, (LocallyConstant.indicator (LocallyConstant.const A _) (hl.isClopen_fiber _)).2,
    HasCompactSupport.intro (hK.image continuous_fst) fun x' hx' => ?_⟩ : SB A) ⊗ₜ
    (⟨_, hf.1.comp_continuous (f := fun y => (x, y)) (by fun_prop),
      HasCompactSupport.intro (hK.image continuous_snd) fun y hy => z _ _ fun h => hy ⟨_, h, rfl⟩⟩ : SB B), rfl⟩
  have : (fun y => f (x', y)) = 0 := funext fun y => z _ _ fun h => hx' ⟨_, h, rfl⟩
  refine Set.indicator_apply_eq_zero.2 fun h => ?_
  exact if_pos (h.symm.trans this)

theorem sb_comp {f : B → ℂ} (hf : f ∈ SB B) (e : A ≃ₜ B) : (fun x => f (e x)) ∈ SB A :=
  ⟨hf.1.comp_continuous e.continuous, hf.2.comp_homeomorph e⟩

end Box

section Mat

variable {k : Type} [Field k] [TopologicalSpace k] [IsTopologicalRing k] {n n' d : ℕ}

def lrH (g : GL (Fin n) k) (h : GL (Fin d) k) : Matrix (Fin n) (Fin d) k ≃ₜ Matrix (Fin n) (Fin d) k where
  toFun Y := g.1 * Y * h.1
  invFun Y := (g⁻¹).1 * Y * (h⁻¹).1
  left_inv Y := by simp [Matrix.mul_assoc]
  right_inv Y := by simp [Matrix.mul_assoc]
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

theorem sb_right {f : Matrix (Fin n) (Fin d) k → ℂ} (hf : f ∈ SB _) (h : GL (Fin d) k) :
    (fun y : Matrix (Fin n) (Fin d) k => f (y * h.1)) ∈ SB _ := by
  simpa [lrH] using sb_comp hf (lrH 1 h)

theorem sb_left {f : Matrix (Fin n) (Fin d) k → ℂ} (hf : f ∈ SB _) (g : GL (Fin n) k) :
    (fun y : Matrix (Fin n) (Fin d) k => f (g.1 * y)) ∈ SB _ := by
  simpa [lrH] using sb_comp hf (lrH g 1)

def rowsH (e : Fin n ⊕ Fin n' ≃ Fin d) : Matrix (Fin d) (Fin d) k ≃ₜ Matrix (Fin n) (Fin d) k × Matrix (Fin n') (Fin d) k where
  toFun Y := ((Y.submatrix e id).toRows₁, (Y.submatrix e id).toRows₂)
  invFun Z := (Matrix.fromRows Z.1 Z.2).submatrix e.symm id
  left_inv Y := by simp
  right_inv Z := by simp
  continuous_toFun := by
    refine Continuous.prodMk (continuous_matrix fun i j => ?_) (continuous_matrix fun i j => ?_) <;>
      exact continuous_id.matrix_elem _ _
  continuous_invFun := continuous_matrix fun i j => by
    obtain ⟨i | i, rfl⟩ := e.surjective i <;>
      simp only [Matrix.submatrix_apply, Equiv.symm_apply_apply, Matrix.fromRows_apply_inl, Matrix.fromRows_apply_inr]
    exacts [continuous_fst.matrix_elem _ _, continuous_snd.matrix_elem _ _]

end Mat

theorem locBil (hL : LocDist) {F : Type} [Field F] [NumberField F] (v : Pl F) {n n' d : ℕ} (e : Fin n ⊕ Fin n' ≃ Fin d)
    (ξ : (Fv F v)ˣ →* ℂˣ) (hξ : ∀ t : ℝ, 0 < t → (ξ (unifAt v) : ℂ) ≠ t)
    (β : SB (Matrix (Fin n) (Fin d) (Fv F v)) →ₗ[ℂ] SB (Matrix (Fin n') (Fin d) (Fv F v)) →ₗ[ℂ] ℂ)
    (hβ : ∀ a b (h : GL (Fin d) (Fv F v)), β ⟨_, sb_right a.2 h⟩ ⟨_, sb_right b.2 h⟩ = ξ (Matrix.GeneralLinearGroup.det h) * β a b)
    (a b) (g : GL (Fin n) (Fv F v)) : β ⟨_, sb_left a.2 g⟩ b = ξ (Matrix.GeneralLinearGroup.det g) * β a b := by
  obtain ⟨q, hq⟩ := (boxL (A := Matrix (Fin n) (Fin d) (Fv F v)) (B := Matrix (Fin n') (Fin d) (Fv F v))).exists_leftInverse_of_injective boxL_ker
  let l := TensorProduct.lift β ∘ₗ q ∘ₗ LinearMap.funLeft ℂ ℂ (rowsH (k := Fv F v) e).symm
  have hl : ∀ x, l (fun y => boxL x (rowsH e y)) = TensorProduct.lift β x := fun x => by
    have : LinearMap.funLeft ℂ ℂ (rowsH (k := Fv F v) e).symm (fun y => boxL x (rowsH e y)) = boxL x := funext fun y => by
      simp [LinearMap.funLeft_apply]
    simp only [l, LinearMap.comp_apply, this]
    rw [← LinearMap.comp_apply q, hq, LinearMap.id_apply]
  let G : Matrix (Fin d) (Fin d) (Fv F v) := Matrix.reindex e e (Matrix.fromBlocks g.1 0 0 1)
  have hG : G.det = g.1.det := by simp [G]
  let G' := Matrix.GeneralLinearGroup.mkOfDetNeZero G (hG ▸ g.det_ne_zero)
  have key := (hL F v d d ξ hξ l (fun φ hφ h => ?_)).2 rfl (fun y => boxL (a ⊗ₜ b) (rowsH e y))
    (sb_comp (f := fun z => a.1 z.1 * b.1 z.2) ⟨(a.2.1.comp_continuous continuous_fst).mul (b.2.1.comp_continuous continuous_snd),
      HasCompactSupport.intro (a.2.2.prod b.2.2) fun z hz => ?_⟩ _) G'
  · rw [hl, show Matrix.GeneralLinearGroup.det G' = Matrix.GeneralLinearGroup.det g from Units.ext hG] at key
    rw [← TensorProduct.lift.tmul, ← hl, ← TensorProduct.lift.tmul, ← key]
    congr 1
    funext y
    have : rowsH e (G * y) = (g.1 * (rowsH e y).1, (rowsH e y).2) := by
      ext i j <;> simp [rowsH, G, Matrix.mul_apply, ← e.sum_comp, Matrix.one_apply]
    exact (congrArg (boxL (a ⊗ₜ b)) this).symm
  · obtain ⟨x, hx⟩ := mem_range_boxL (sb_comp hφ (rowsH e).symm)
    obtain rfl : φ = fun y => boxL x (rowsH e y) := funext fun y => by simp [hx]
    clear hx hφ
    induction x using TensorProduct.induction_on with
    | zero => simp [← Pi.zero_def]
    | add x y hx hy =>
      simp only [map_add (f := _), Pi.add_apply]
      rw [← Pi.add_def, ← Pi.add_def, map_add (f := _), map_add (f := _), hx, hy, mul_add]
    | tmul a b =>
      rw [hl, TensorProduct.lift.tmul, ← hβ, ← TensorProduct.lift.tmul, ← hl]
      rfl
  · by_cases h : z.1 ∈ tsupport a.1
    · rw [image_eq_zero_of_notMem_tsupport (f := b.1) fun h' => hz ⟨h, h'⟩, mul_zero]
    · rw [image_eq_zero_of_notMem_tsupport h, zero_mul]

end GlobalTheory.ThK.Dbl.TC

end
end

section

noncomputable section

namespace GlobalTheory.ThK.Dbl

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.Doubling (absE)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {m n : ℕ}

variable {Y : Spc F E n} {A : Spc F E m}

def DblX : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ),
    IsPair B M χX χW om r s r' s' → ∃ dd om₂ S l, IsDbl (σ := σ) (A := W) (Y := X) (κ := (Fin n × Fin d) ⊕ (Fin n × Fin d)) B.ψ dd χW om₂ S l ∧
      (∀ Φ₁ ∈ schA F _, ∀ Φ₂ ∈ schA F _, boxFun Φ₁ (star Φ₂) ∈ schA F _ ∧ ∀ h g g' x, IsEmb g g' x →
        detInv χW g' * thetaSum F (om₂ x (S h (boxFun Φ₁ (star Φ₂)))) = theta om Φ₁ g h * star (theta om Φ₂ g' h) ∧
        detInv χW g' • om₂ x (boxFun Φ₁ (star Φ₂)) = boxFun (om (g, 1) Φ₁) (star (om (g', 1) Φ₂))) ∧
      IsDblCoordX M dd ∧
      ∀ ν : @Measure (Fin n × Fin d → AF F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) ν → ∃ c' : ℝ, 0 < c' ∧
        ∀ Ψ₁ ∈ schA F _, ∀ Ψ₂ ∈ schA F _, l (boxFun Ψ₁ (star Ψ₂)) = c' * ∫ u, Ψ₁ u * star (Ψ₂ u) ∂ν

def BoxSecX : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) r s r' s', B.IsGood σ → 1 ≤ n → 1 ≤ d → X.IsHerm σ B r s →
    W.IsSkew σ B r' s' → min r' s' = 0 → M.IsGood B.ψ →
    ∀ χ : Chr F E, IsHecke F E χ → ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χ d →
    ∀ dd om S l, IsDblCoordX M dd → IsDbl (σ := σ) (A := W) (Y := X) B.ψ dd χ om S l →
    ∀ K a, IsStab2 B K → IsHgt K a →
    ∀ Φ₁ ∈ PolData B M, ∀ Φ₂ ∈ PolData B M, IsSec K χ (((d : ℂ) - n) / 2) (fun x => l (om x (boxFun Φ₁ (star Φ₂))))

def SWFullX : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) r s r' s', B.IsGood σ → 1 ≤ n → 1 ≤ d → X.IsHerm σ B r s →
    W.IsSkew σ B r' s' → min r' s' = 0 → M.IsGood B.ψ →
    ∀ χ : Chr F E, IsHecke F E χ → ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χ d →
    ∀ dd om S l, IsDblCoordX M dd → IsDbl (σ := σ) (A := W) (Y := X) B.ψ dd χ om S l →
    ∀ K a, IsStab2 B K → IsHgt K a →
    ∀ (μ : Measure (UA σ W.J)) (D : Set (UA σ W.J)), μ.IsHaarMeasure → IsFundamentalDomain (ratU σ W.J) D μ →
    ∀ Φ₁ ∈ PolData B M, ∀ Φ₂ ∈ PolData B M,
      ∃ U Ê, IsEisCont (flat a (fun x => l (om x (boxFun Φ₁ (star Φ₂)))) (((d : ℂ) - n) / 2)) U Ê ∧ (((d : ℂ) - n) / 2) ∈ U ∧
        ∀ x, Ê (((d : ℂ) - n) / 2) x = (if n < d then 1 else 2) * ⨍ h in D, thetaSum F (om x (S h (boxFun Φ₁ (star Φ₂)))) ∂μ

end GlobalTheory.ThK.Dbl

end
end
