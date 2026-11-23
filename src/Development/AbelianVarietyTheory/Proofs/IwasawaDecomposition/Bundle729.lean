module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle716
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PullLinInjective
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle630
public import Mathlib.Basic.Real.Basic
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle718
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
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle532
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle682
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle697
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle008
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd

@[expose] public section

section

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell

namespace GlobalTheory.PolFan

section Transfer

variable {O : Type} [CommRing O] (bar : O → O) {X : Type} [AddCommGroup X]

theorem isCell_transfer {φ : InvFun O} (m1 m2 : Module O X) (f1 : letI := m1; Module.Finite O X)
    (f2 : letI := m2; Module.Finite O X)
    (hbal : ∀ β, β ∈ (letI := m1; balForms bar X) ↔ β ∈ (letI := m2; balForms bar X))
    (hφ : ∀ B : X → X → ℝ, (letI := m1; letI := f1; φ.eval X B) = (letI := m2; letI := f2; φ.eval X B))
    {k : ℕ} {γ : Fin k → LinearMap.BilinForm ℤ X} (h : letI := m1; letI := f1; IsCell bar φ γ) :
    letI := m2; letI := f2; IsCell bar φ γ := by
  obtain ⟨hm, hn, hl, hs⟩ := h
  have hZ : ∀ β : LinearMap.BilinForm ℤ X, (letI := m1; letI := f1; φ.evalZ β) = (letI := m2; letI := f2; φ.evalZ β) :=
    fun β => hφ _
  obtain ⟨N, ℓ, hN, h1, h2, h3⟩ := hs
  letI := m2
  letI := f2
  refine ⟨fun i => (hbal _).1 (hm i), hn, fun c hc => ?_, N, ℓ, hN, fun i => ?_, fun β hβ hp => ?_, fun β hβ hp he => ?_⟩
  · rw [← hφ]
    simp only [← hZ]
    exact hl c hc
  · rw [← hZ]; exact h1 i
  · rw [← hZ]; exact h2 β ((hbal β).2 hβ) hp
  · exact h3 β ((hbal β).2 hβ) hp (by rw [hZ]; exact he)

theorem isStarDepth_transfer {ψ w : InvFun O} (m1 m2 : Module O X) (f1 : letI := m1; Module.Finite O X)
    (f2 : letI := m2; Module.Finite O X)
    (hbal : ∀ β, β ∈ (letI := m1; balForms bar X) ↔ β ∈ (letI := m2; balForms bar X))
    (hψ : ∀ B : X → X → ℝ, (letI := m1; letI := f1; ψ.eval X B) = (letI := m2; letI := f2; ψ.eval X B))
    (hw : ∀ B : X → X → ℝ, (letI := m1; letI := f1; w.eval X B) = (letI := m2; letI := f2; w.eval X B))
    {B₁ : X →ₗ[ℤ] X →ₗ[ℤ] ℝ} {t : ℝ} (h : letI := m1; letI := f1; IsStarDepth bar ψ w B₁ t) :
    letI := m2; letI := f2; IsStarDepth bar ψ w B₁ t := by
  obtain ⟨ht, k, γ, v, hc, hv, hpos, hw1, hin, hB, hBt⟩ := h
  exact ⟨ht, k, γ, v, isCell_transfer bar m1 m2 f1 f2 hbal hψ hc, (hbal v).1 hv, hpos, (hw _).symm.trans hw1, hin, hB,
    hBt⟩

end Transfer

section Twist

variable {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E)

theorem host_bar_map_comm (σ : 𝓞 E ≃+* 𝓞 E) (a : 𝓞 E) : σ (H.bar a) = H.bar (σ a) := by
  obtain ⟨φ⟩ : Nonempty (E →+* ℂ) := inferInstance
  let s : E ≃+* E := IsFractionRing.ringEquivOfRingEquiv σ
  have hs : ∀ x : 𝓞 E, ((σ x : 𝓞 E) : E) = s x := fun x =>
    (IsFractionRing.ringEquivOfRingEquiv_algebraMap σ x).symm
  apply RingOfIntegers.ext
  apply φ.injective
  rw [H.bar_eq, hs, hs, H.bar_eq, IsCMField.complexEmbedding_complexConj]
  exact IsCMField.complexEmbedding_complexConj E (φ.comp s.toRingHom) _

variable {X : Type} [AddCommGroup X] [Module (𝓞 E) X]

theorem mem_balForms_twist (τ : 𝓞 E ≃+* 𝓞 E) (β : LinearMap.BilinForm ℤ X) :
    β ∈ balForms H.bar X ↔ β ∈ (letI := Module.compHom X τ.toRingHom; balForms H.bar X) := by
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun a y z => ?_⟩
    show β (τ a • y) z = β y (τ (H.bar a) • z)
    rw [h2, host_bar_map_comm]
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun a y z => ?_⟩
    have := h2 (τ.symm a) y z
    change β (τ (τ.symm a) • y) z = β y (τ (H.bar (τ.symm a)) • z) at this
    rwa [host_bar_map_comm, τ.apply_symm_apply] at this

theorem eval_twist_of_isTwInv {φ : InvFun (𝓞 E)} (hφ : IsTwInv H φ) (τ : 𝓞 E ≃+* 𝓞 E) (hτ : τ H.w0 = H.w0)
    [Module.Finite (𝓞 E) X] (hf : letI := Module.compHom X τ.toRingHom; Module.Finite (𝓞 E) X) (B : X → X → ℝ) :
    φ.eval X B = (letI := Module.compHom X τ.toRingHom; letI := hf; φ.eval X B) := by
  obtain ⟨n, r, hr⟩ := Module.Finite.exists_fin' (𝓞 E) X
  rw [φ.eval_eq hr, ← hφ τ hτ]
  let g : (Fin n → 𝓞 E) →+ X := r.toAddMonoidHom.comp
    ⟨⟨fun a i => τ (a i), by ext; simp⟩, fun a b => by ext; simp⟩
  have hg : ∀ (c : 𝓞 E) a, g (c • a) = τ c • g a := fun c a => by
    change r _ = τ c • r _
    rw [← map_smul]
    congr 1
    ext i
    simp
  have hs : Function.Surjective g := hr.comp fun a => ⟨fun i => τ.symm (a i), funext fun i => τ.apply_symm_apply _⟩
  letI : Module (𝓞 E) X := Module.compHom _ τ.toRingHom
  letI := hf
  exact (φ.eval_eq (r := ⟨g.toAddHom, hg⟩) hs _).symm


omit [Module (𝓞 E) X] in
theorem depthSet_twist_subset {ψ w : InvFun (𝓞 E)} (hψ : IsTwInv H ψ) (hw : IsTwInv H w) (σ : 𝓞 E ≃+* 𝓞 E)
    (hσ : σ H.w0 = H.w0) (n : ℕ) (B : (Fin n → 𝓞 E) → (Fin n → 𝓞 E) → ℝ) :
    depthSet H.bar ψ w n (fun a b => B (fun i => σ (a i)) (fun i => σ (b i))) ⊆ depthSet H.bar ψ w n B := by
  rintro t ⟨X₁, i1, i2, i3, r, B₁, hr, hrad, hB, hd⟩
  set τ := σ.symm with hτdef
  have hτ : τ H.w0 = H.w0 := (σ.symm_apply_eq).2 hσ.symm
  let g : (Fin n → 𝓞 E) →+ X₁ := r.toAddMonoidHom.comp
    ⟨⟨fun a i => τ (a i), by ext; simp⟩, fun a b => by ext; simp⟩
  have hg : ∀ (c : 𝓞 E) a, g (c • a) = τ c • g a := fun c a => by
    change r _ = τ c • r _
    rw [← map_smul]
    congr 1
    ext i
    simp
  have hs : Function.Surjective g := hr.comp fun a => ⟨fun i => σ (a i), funext fun i => σ.symm_apply_apply _⟩
  have hgB : ∀ a b, B a b = B₁ (g a) (g b) := fun a b => by
    have := hB (fun i => τ (a i)) (fun i => τ (b i))
    simp only [hτdef, RingEquiv.apply_symm_apply] at this
    exact this
  have hf' : letI := Module.compHom X₁ τ.toRingHom; Module.Finite (𝓞 E) X₁ := by
    letI := Module.compHom X₁ τ.toRingHom
    exact Module.Finite.of_surjective (⟨g.toAddHom, hg⟩ : (Fin n → 𝓞 E) →ₗ[𝓞 E] X₁) hs
  have hd' := isStarDepth_transfer H.bar i2 (Module.compHom X₁ τ.toRingHom) i3 hf' (mem_balForms_twist H τ)
    (eval_twist_of_isTwInv H hψ τ hτ hf') (eval_twist_of_isTwInv H hw τ hτ hf') hd
  letI := Module.compHom X₁ τ.toRingHom
  exact ⟨X₁, i1, _, hf', ⟨g.toAddHom, hg⟩, B₁, hs, hrad, hgB, hd'⟩

theorem isTwInv_starDepth : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (ψ w : InvFun (𝓞 E)),
    IsTwInv H ψ → IsTwInv H w → IsTwInv H (starDepth H.bar ψ w) := by
  intro E _ _ _ H ψ w hψ hw σ hσ n B
  show sSup _ = sSup _
  congr 1
  refine Set.Subset.antisymm (depthSet_twist_subset H hψ hw σ hσ n B) ?_
  have h := depthSet_twist_subset H hψ hw σ.symm ((σ.symm_apply_eq).2 hσ.symm) n
    (fun a b => B (fun i => σ (a i)) (fun i => σ (b i)))
  simpa only [RingEquiv.apply_symm_apply] using h

end Twist

end GlobalTheory.PolFan
end
end

section

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef

namespace GlobalTheory.PolFan

namespace OrbMark

section Twist

variable {O : Type} [CommRing O]

def twv (σ : O ≃+* O) {n : ℕ} (a : Fin n → O) : Fin n → O := fun i => σ (a i)

@[simp] theorem twv_apply (σ : O ≃+* O) {n : ℕ} (a : Fin n → O) (i : Fin n) : twv σ a i = σ (a i) := rfl

theorem twv_zero (σ : O ≃+* O) (n : ℕ) : twv σ (0 : Fin n → O) = 0 := funext fun _ => map_zero σ

theorem twv_smul (σ : O ≃+* O) {n : ℕ} (c : O) (a : Fin n → O) : twv σ (c • a) = σ c • twv σ a :=
  funext fun _ => by simp [twv]

theorem twv_twv (σ τ : O ≃+* O) {n : ℕ} (a : Fin n → O) : twv τ (twv σ a) = twv (σ.trans τ) a := rfl

theorem twv_symm_twv (σ : O ≃+* O) {n : ℕ} (a : Fin n → O) : twv σ.symm (twv σ a) = a :=
  funext fun _ => σ.symm_apply_apply _

theorem twv_twv_symm (σ : O ≃+* O) {n : ℕ} (a : Fin n → O) : twv σ (twv σ.symm a) = a :=
  funext fun _ => σ.apply_symm_apply _

def conjLin (σ : O ≃+* O) {n m : ℕ} (r : (Fin n → O) →ₗ[O] (Fin m → O)) : (Fin n → O) →ₗ[O] (Fin m → O) where
  toFun a := twv σ.symm (r (twv σ a))
  map_add' a b := by
    have e : twv σ (a + b) = twv σ a + twv σ b := funext fun _ => map_add σ _ _
    rw [e, map_add (f := _)]
    exact funext fun _ => map_add σ.symm _ _
  map_smul' c a := by
    rw [twv_smul, map_smul, twv_smul, RingHom.id_apply, σ.symm_apply_apply]

theorem twv_conjLin (σ : O ≃+* O) {n m : ℕ} (r : (Fin n → O) →ₗ[O] (Fin m → O)) (a : Fin n → O) :
    twv σ (conjLin σ r a) = r (twv σ a) := twv_twv_symm σ _

theorem conjLin_surjective (σ : O ≃+* O) {n m : ℕ} {r : (Fin n → O) →ₗ[O] (Fin m → O)} (hr : Function.Surjective r) :
    Function.Surjective (conjLin σ r) := fun b => by
  obtain ⟨a, ha⟩ := hr (twv σ b)
  refine ⟨twv σ.symm a, ?_⟩
  show twv σ.symm (r (twv σ (twv σ.symm a))) = b
  rw [twv_twv_symm, ha, twv_symm_twv]

end Twist

section Mark

variable {O : Type} [CommRing O] {X₀ : Type} [AddCommGroup X₀] [Module O X₀]

def IsOrbForm (v : LinearMap.BilinForm ℤ X₀) (σ : O ≃+* O) (n : ℕ) (B : (Fin n → O) → (Fin n → O) → ℝ) : Prop :=
  ∃ s : (Fin n → O) →ₗ[O] (X₀ ⧸ (CarDim.orad v : Submodule O X₀)), Function.Surjective s ∧
    ∀ (a b : Fin n → O) (x y : X₀), Submodule.Quotient.mk x = s a → Submodule.Quotient.mk y = s b →
      B (twv σ a) (twv σ b) = v x y

theorem isOrbForm_comp_iff (v : LinearMap.BilinForm ℤ X₀) (σ : O ≃+* O) {n m : ℕ}
    {r : (Fin n → O) →ₗ[O] (Fin m → O)} (hr : Function.Surjective r) (B : (Fin m → O) → (Fin m → O) → ℝ) :
    IsOrbForm v σ n (fun a b => B (r a) (r b)) ↔ IsOrbForm v σ m B := by
  set r' := conjLin σ r
  have hr' : Function.Surjective r' := conjLin_surjective σ hr
  constructor
  · rintro ⟨s, hs, H⟩
    obtain ⟨t, ht⟩ := Module.projective_lifting_property r' LinearMap.id hr'
    have hrt : ∀ a, r' (t a) = a := fun a => LinearMap.congr_fun ht a
    have hker : ∀ z, r' z = 0 → s z = 0 := by
      intro z hz
      obtain ⟨x, hx⟩ := Submodule.mkQ_surjective _ (s z)
      rw [← hx]
      refine (Submodule.Quotient.mk_eq_zero _).2 fun c y => ?_
      obtain ⟨b, hb⟩ := hs (Submodule.Quotient.mk y)
      have h1 := H (c • z) b (c • x) y (by rw [Submodule.Quotient.mk_smul, map_smul]; exact congrArg _ hx) hb.symm
      have h2 := H 0 b 0 y (by rw [map_zero]; rfl) hb.symm
      have e : r (twv σ (c • z)) = 0 := by
        rw [← twv_conjLin, map_smul, hz, smul_zero, twv_zero]
      have e0 : r (twv σ 0) = 0 := by rw [twv_zero, map_zero]
      dsimp only at h1 h2
      rw [e] at h1
      rw [e0, map_zero, LinearMap.zero_apply] at h2
      exact_mod_cast h1.symm.trans h2
    refine ⟨s ∘ₗ t, fun y => ?_, fun a b x y hx hy => ?_⟩
    · obtain ⟨a, rfl⟩ := hs y
      refine ⟨r' a, ?_⟩
      have : s (a - t (r' a)) = 0 := hker _ (by rw [map_sub, hrt, sub_self])
      rw [map_sub, sub_eq_zero] at this
      exact this.symm
    · have h := H (t a) (t b) x y hx hy
      dsimp only at h
      rwa [← twv_conjLin, ← twv_conjLin, hrt, hrt] at h
  · rintro ⟨s, hs, H⟩
    refine ⟨s ∘ₗ r', hs.comp hr', fun a b x y hx hy => ?_⟩
    have h := H (r' a) (r' b) x y hx hy
    show B (r (twv σ a)) (r (twv σ b)) = _
    rwa [twv_conjLin, twv_conjLin] at h

theorem eq_zero_of_isOrbForm_zero {v : LinearMap.BilinForm ℤ X₀} {σ : O ≃+* O} {B : (Fin 0 → O) → (Fin 0 → O) → ℝ}
    (h : IsOrbForm v σ 0 B) : v = 0 := by
  obtain ⟨s, hs, -⟩ := h
  refine LinearMap.ext₂ fun x y => ?_
  have hx : x ∈ (CarDim.orad v : Submodule O X₀) := by
    obtain ⟨a, ha⟩ := hs (Submodule.Quotient.mk x)
    rw [Subsingleton.elim a 0, map_zero] at ha
    exact (Submodule.Quotient.mk_eq_zero _).1 ha.symm
  simpa using hx 1 y

end Mark

section Fun

variable (O : Type) [CommRing O] {X₀ : Type} [AddCommGroup X₀] [Module O X₀]


open Classical in
def orbFun (w0 : O) (v : LinearMap.BilinForm ℤ X₀) : InvFun O where
  toFun n B := if v ≠ 0 ∧ ∃ σ : O ≃+* O, σ w0 = w0 ∧ IsOrbForm v σ n B then 1 else 0
  inv n m r hr B := by
    simp only [isOrbForm_comp_iff v _ hr]
  zero B := by
    rw [if_neg]
    rintro ⟨hv, σ, -, h⟩
    exact hv (eq_zero_of_isOrbForm_zero h)

variable {O}

open Classical in
theorem orbFun_toFun (w0 : O) (v : LinearMap.BilinForm ℤ X₀) (n : ℕ) (B : (Fin n → O) → (Fin n → O) → ℝ) :
    (orbFun O w0 v).toFun n B = if v ≠ 0 ∧ ∃ σ : O ≃+* O, σ w0 = w0 ∧ IsOrbForm v σ n B then 1 else 0 := rfl

theorem orbFun_eval_eq_zero_or_one (w0 : O) (v : LinearMap.BilinForm ℤ X₀) {X : Type} [AddCommGroup X] [Module O X]
    [Module.Finite O X] (B : X → X → ℝ) : (orbFun O w0 v).eval X B = 0 ∨ (orbFun O w0 v).eval X B = 1 := by
  unfold InvFun.eval
  rw [orbFun_toFun]
  split_ifs
  · exact Or.inr rfl
  · exact Or.inl rfl

theorem eq_zero_of_isOrbForm_const {v : LinearMap.BilinForm ℤ X₀} {σ : O ≃+* O} {n : ℕ}
    (h : IsOrbForm v σ n fun _ _ => 0) : v = 0 := by
  obtain ⟨s, hs, H⟩ := h
  refine LinearMap.ext₂ fun x y => ?_
  obtain ⟨a, ha⟩ := hs (Submodule.Quotient.mk x)
  obtain ⟨b, hb⟩ := hs (Submodule.Quotient.mk y)
  have := H a b x y ha.symm hb.symm
  simp only [LinearMap.zero_apply]
  have h0 : ((v x y : ℤ) : ℝ) = 0 := this.symm
  exact_mod_cast h0

theorem orbFun_evalZ_zero (w0 : O) {v : LinearMap.BilinForm ℤ X₀} (hv : v ≠ 0) {X : Type} [AddCommGroup X] [Module O X]
    [Module.Finite O X] : (orbFun O w0 v).evalZ (0 : LinearMap.BilinForm ℤ X) = 0 := by
  obtain ⟨n, r, hr⟩ := Module.Finite.exists_fin' O X
  rw [InvFun.evalZ, (orbFun O w0 v).eval_eq hr, orbFun_toFun, if_neg]
  rintro ⟨-, σ, -, h⟩
  refine hv (eq_zero_of_isOrbForm_const (σ := σ) (n := n) ?_)
  simpa using h

theorem orbFun_evalZ_self (w0 : O) {v : LinearMap.BilinForm ℤ X₀} [Module.Finite O X₀] (hv : v ≠ 0)
    (hsym : ∀ y z, v y z = v z y) : (orbFun O w0 v).evalZ v = 1 := by
  obtain ⟨n, r, hr⟩ := Module.Finite.exists_fin' O X₀
  rw [InvFun.evalZ, (orbFun O w0 v).eval_eq hr, orbFun_toFun, if_pos]
  refine ⟨hv, RingEquiv.refl O, rfl, (CarDim.orad v).mkQ ∘ₗ r, (Submodule.mkQ_surjective _).comp hr,
    fun a b x y hx hy => ?_⟩
  have hx' : x - r a ∈ (CarDim.orad v : Submodule O X₀) := (Submodule.Quotient.eq _).1 hx
  have hy' : y - r b ∈ (CarDim.orad v : Submodule O X₀) := (Submodule.Quotient.eq _).1 hy
  have e1 : v x y = v (r a) y := by
    have := hx' 1 y
    rw [one_smul, map_sub, LinearMap.sub_apply, sub_eq_zero] at this
    exact this
  have e2 : v (r a) y = v (r a) (r b) := by
    have := hy' 1 (r a)
    rw [one_smul, map_sub, LinearMap.sub_apply, sub_eq_zero, hsym, hsym (r b)] at this
    exact this
  show ((v (r a) (r b) : ℤ) : ℝ) = (v x y : ℝ)
  rw [e1, e2]

end Fun

section Host

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {X₀ : Type} [AddCommGroup X₀] [Module (𝓞 E) X₀]

theorem isTwInv_orbFun (H : Host E) (v : LinearMap.BilinForm ℤ X₀) : IsTwInv H (orbFun (𝓞 E) H.w0 v) := by
  intro τ hτ n B
  rw [orbFun_toFun, orbFun_toFun]
  congr 2
  apply propext
  constructor
  · rintro ⟨σ, hσ, s, hs, h⟩
    exact ⟨σ.trans τ, by simp [hσ, hτ], s, hs, fun a b x y hx hy => h a b x y hx hy⟩
  · rintro ⟨σ, hσ, s, hs, h⟩
    refine ⟨σ.trans τ.symm, by simp [hσ, RingEquiv.symm_apply_eq, hτ], s, hs, fun a b x y hx hy => ?_⟩
    have := h a b x y hx hy
    show B (twv τ (twv (σ.trans τ.symm) a)) (twv τ (twv (σ.trans τ.symm) b)) = _
    rw [twv_twv, twv_twv]
    convert this using 3 <;> ext i <;> simp

end Host

end OrbMark

end GlobalTheory.PolFan
end
end

section

open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.GoodMetric GlobalTheory.LieBase GlobalTheory.GrassTop
open Classical


theorem _root_.GlobalTheory.T.isHomogeneous_of_mul_isHomogeneous_of_ne_zero_right : ∀ {σ : Type} (P Q : MvPolynomial σ ℝ) (a b : ℕ), Q ≠ 0 → Q.IsHomogeneous b → (P * Q).IsHomogeneous (a + b) → P.IsHomogeneous a := by
  first | exact @GlobalTheory.GrassTop.isHomogeneous_of_mul_isHomogeneous_right | exact GlobalTheory.GrassTop.isHomogeneous_of_mul_isHomogeneous_right | (intros; apply GlobalTheory.GrassTop.isHomogeneous_of_mul_isHomogeneous_right <;> assumption)
end
