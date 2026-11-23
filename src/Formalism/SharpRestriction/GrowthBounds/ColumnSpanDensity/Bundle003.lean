module

public import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.RhoLowerBoundLargeConductor
public import Formalism.PolynomialDimension.Bundle001
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree

def othW {n' m : ℕ} (TT : Finset (Fin n')) (lam0 : Fin n' → Fin (m + 1) → ℤ) : Fin n' → Fin (m + 1) → ℤ :=
  fun s => if s ∈ TT then 0 else lam0 s

def Pr {O Kf V₁ V₂ V : Type*} [CommRing O] [Field Kf] [Algebra O Kf] [AddCommGroup V₁] [Module Kf V₁] [Module O V₁]
    [AddCommGroup V₂] [Module Kf V₂] [Module O V₂] [AddCommGroup V] [Module Kf V] [Module O V]
    (μ : V₁ →ₗ[Kf] V₂ →ₗ[Kf] V) (M : Submodule O V₁) (N : Submodule O V₂) : Submodule O V :=
  Submodule.span O {x | ∃ F ∈ M, ∃ r ∈ N, x = μ F r}

def RestTensor : Prop :=
  ∀ (p n' : ℕ) (R : RS p n') (m : ℕ) (TT : Finset (Fin n')) (lam0 : Fin n' → Fin (m + 1) → ℤ), IsDominant lam0 →
    ∃ (μ : Vsp R.Kf (topW TT lam0) →ₗ[R.Kf] Vsp R.Kf (othW TT lam0) →ₗ[R.Kf] Vsp R.Kf lam0)
      (ν : Module.Dual R.Kf (Vsp R.Kf (topW TT lam0)) →ₗ[R.Kf] Module.Dual R.Kf (Vsp R.Kf (othW TT lam0)) →ₗ[R.Kf]
        Module.Dual R.Kf (Vsp R.Kf lam0)),
      (∀ G ρ F r, ν G ρ (μ F r) = G F * ρ r) ∧
      (∀ L : Submodule R.W (Fin (m + 1) → R.Qq), IsLattice R.W L →
        HL (O := R.O) R.ι R.σ lam0 L =
          Pr μ (HL (O := R.O) R.ι R.σ (topW TT lam0) L) (HL (O := R.O) R.ι R.σ (othW TT lam0) L)) ∧
      (∀ e : Edge R.W R.Qq (m + 1), IsEdge p n' 1 e →
        HLe p R.ι R.σ R.w lam0 e =
          Pr μ (HLe p R.ι R.σ R.w (topW TT lam0) e) (HLe p R.ι R.σ R.w (othW TT lam0) e)) ∧
      dimV R.Kf lam0 = dimV R.Kf (topW TT lam0) * dimV R.Kf (othW TT lam0)

def RestOrdBound : Prop :=
  ∀ (p n' : ℕ) (R : RS p n') (m : ℕ) (lamO : Fin n' → Fin (m + 1) → ℤ) (c : ℕ), IsDominant lamO →
    (∀ s i, |lamO s i| ≤ c) → ∀ e : Edge R.W R.Qq (m + 1), IsEdge p n' 1 e →
      Re p R.ι R.σ R.w 1 lamO e ≤
        scale (algebraMap R.O R.Kf R.w ^ (-((2 * n' * c : ℕ) : ℤ))) (HL R.ι R.σ lamO e.src) ∧
      Re' p R.ι R.σ R.w 1 lamO e ≤
        scale (algebraMap R.O R.Kf R.w ^ (-((2 * n' * c : ℕ) : ℤ)))
          (Formalism.GradedWeylDivisibility.dualLat R.O R.Kf (HL (O := R.O) R.ι R.σ lamO e.tgt))

section Formal

variable {O Kf V₁ V₂ V : Type*} [CommRing O] [Field Kf] [Algebra O Kf] [AddCommGroup V₁] [Module Kf V₁] [Module O V₁]
  [IsScalarTower O Kf V₁] [AddCommGroup V₂] [Module Kf V₂] [Module O V₂] [IsScalarTower O Kf V₂] [AddCommGroup V]
  [Module Kf V] [Module O V] [IsScalarTower O Kf V]

theorem scale_mono (c : Kf) {M M' : Submodule O V} (h : M ≤ M') : scale c M ≤ scale c M' := Submodule.map_mono h

theorem scale_scale_mem {a b : Kf} {M : Submodule O V} {x : V} (h : x ∈ scale a (scale b M)) :
    x ∈ scale (a * b) M := by
  obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp h
  obtain ⟨z, hz, rfl⟩ := Submodule.mem_map.mp hy
  refine Submodule.mem_map.mpr ⟨z, hz, ?_⟩
  simp [mul_smul]
  exact smul_comm _ _ _

theorem mem_scale_scale {a b : Kf} {M : Submodule O V} {x : V} (h : x ∈ scale (a * b) M) :
    x ∈ scale a (scale b M) := by
  obtain ⟨z, hz, rfl⟩ := Submodule.mem_map.mp h
  refine Submodule.mem_map.mpr ⟨b • z, Submodule.mem_map.mpr ⟨z, hz, by simp⟩, ?_⟩
  simp [mul_smul]
  exact smul_comm _ _ _

theorem mu_scale (μ : V₁ →ₗ[Kf] V₂ →ₗ[Kf] V) {a b : Kf} {M : Submodule O V₁} {N : Submodule O V₂} {F : V₁} {r : V₂}
    (hF : F ∈ scale a M) (hr : r ∈ scale b N) : μ F r ∈ scale (a * b) (Pr μ M N) := by
  obtain ⟨F0, hF0, rfl⟩ := Submodule.mem_map.mp hF
  obtain ⟨r0, hr0, rfl⟩ := Submodule.mem_map.mp hr
  refine Submodule.mem_map.mpr ⟨μ F0 r0, Submodule.subset_span ⟨F0, hF0, r0, hr0, rfl⟩, ?_⟩
  simp [mul_smul]
  exact smul_comm _ _ _

theorem nu_dual (μ : V₁ →ₗ[Kf] V₂ →ₗ[Kf] V)
    (ν : Module.Dual Kf V₁ →ₗ[Kf] Module.Dual Kf V₂ →ₗ[Kf] Module.Dual Kf V)
    (hν : ∀ G ρ F r, ν G ρ (μ F r) = G F * ρ r) {M : Submodule O V₁} {N : Submodule O V₂}
    {G : Module.Dual Kf V₁} {ρ : Module.Dual Kf V₂} (hG : G ∈ Formalism.GradedWeylDivisibility.dualLat O Kf M)
    (hρ : ρ ∈ Formalism.GradedWeylDivisibility.dualLat O Kf N) : ν G ρ ∈ Formalism.GradedWeylDivisibility.dualLat O Kf (Pr μ M N) := by
  intro v hv
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨F, hF, r, hr, rfl⟩ := hx
    obtain ⟨a, ha⟩ := hG F hF
    obtain ⟨b, hb⟩ := hρ r hr
    exact ⟨a * b, by rw [hν, map_mul, ha, hb]⟩
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    exact ⟨a + b, by rw [map_add (f := _), map_add (f := _), ha, hb]⟩
  | smul c x _ hx =>
    obtain ⟨a, ha⟩ := hx
    exact ⟨c * a, by rw [map_mul, ha, ← algebraMap_smul Kf c x, map_smul, smul_eq_mul]⟩

theorem nu_scale (μ : V₁ →ₗ[Kf] V₂ →ₗ[Kf] V)
    (ν : Module.Dual Kf V₁ →ₗ[Kf] Module.Dual Kf V₂ →ₗ[Kf] Module.Dual Kf V)
    (hν : ∀ G ρ F r, ν G ρ (μ F r) = G F * ρ r) {a b : Kf} {M : Submodule O V₁} {N : Submodule O V₂}
    {G : Module.Dual Kf V₁} {ρ : Module.Dual Kf V₂} (hG : G ∈ scale a (Formalism.GradedWeylDivisibility.dualLat O Kf M))
    (hρ : ρ ∈ scale b (Formalism.GradedWeylDivisibility.dualLat O Kf N)) :
    ν G ρ ∈ scale (a * b) (Formalism.GradedWeylDivisibility.dualLat O Kf (Pr μ M N)) := by
  obtain ⟨G0, hG0, rfl⟩ := Submodule.mem_map.mp hG
  obtain ⟨ρ0, hρ0, rfl⟩ := Submodule.mem_map.mp hρ
  refine Submodule.mem_map.mpr ⟨ν G0 ρ0, nu_dual μ ν hν hG0 hρ0, ?_⟩
  simp [mul_smul]
  exact smul_comm _ _ _

end Formal

theorem FactorsLE_of_index {O Kf V V' : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf]
    [Algebra O Kf] [AddCommGroup V] [Module O V] [AddCommGroup V'] [Module O V'] {p : ℕ} {be : V → V' → Kf}
    {A : Submodule O V} {A' : Submodule O V'} {D : ℝ} {I : Type*} [Fintype I] [DecidableEq I] (n : ℕ)
    (hcard : Fintype.card I = n) (x : I → V) (y : I → V') (hx : ∀ i, x i ∈ A) (hy : ∀ i, y i ∈ A') (z : O)
    (M : Matrix I I O) (hz : z ≠ 0) (hv : vLEO p z D)
    (hM : ∀ i j, ∑ l, be (x i) (y l) * algebraMap O Kf (M l j) = if i = j then algebraMap O Kf z else 0) :
    FactorsLE p be A A' n D := by
  unfold FactorsLE
  right
  let e : Fin n ≃ I := (Fintype.equivFinOfCardEq hcard).symm
  refine ⟨fun i => x (e i), fun i => y (e i), fun i => hx _, fun i => hy _, z, M.submatrix e e, hz, hv, fun i j => ?_⟩
  simp only [Matrix.submatrix_apply]
  rw [Equiv.sum_comp e (fun l => be (x (e i)) (y l) * algebraMap O Kf (M l (e j))), hM]
  simp [e.injective.eq_iff]

theorem othW_dom {n' m : ℕ} {TT : Finset (Fin n')} {lam0 : Fin n' → Fin (m + 1) → ℤ} (h : IsDominant lam0) :
    IsDominant (othW TT lam0) := by
  show ∀ s, Antitone (othW TT lam0 s)
  intro s
  simp only [othW]
  split_ifs
  · exact antitone_const
  · exact h s

theorem Ar_add {n' m : ℕ} (TT : Finset (Fin n')) (lam0 : Fin n' → Fin (m + 1) → ℤ) :
    Ar 1 lam0 = Ar 1 (topW TT lam0) + Ar 1 (othW TT lam0) := by
  unfold Ar
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  unfold lamAt topW othW
  by_cases hs : s ∈ TT <;> by_cases he : Even (s : ℕ) <;> simp [hs, he]

end Formalism.MainNotions.flipOneThree.Pf

end
end

section

noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree

structure RSIso {p n' : ℕ} (R₁ R₂ : RS p n') where
  φW : R₁.W ≃+* R₂.W
  φQ : R₁.Qq ≃+* R₂.Qq
  φO : R₁.O ≃+* R₂.O
  φK : R₁.Kf ≃+* R₂.Kf
  hWQ : ∀ x, φQ (algebraMap R₁.W R₁.Qq x) = algebraMap R₂.W R₂.Qq (φW x)
  hOK : ∀ x, φK (algebraMap R₁.O R₁.Kf x) = algebraMap R₂.O R₂.Kf (φO x)
  hι : ∀ x, φK (R₁.ι x) = R₂.ι (φQ x)
  hσ : ∀ x, φQ (R₁.σ x) = R₂.σ (φQ x)
  hj : ∀ x, φO (R₁.jO x) = R₂.jO (φW x)
  hw : φO R₁.w = R₂.w

def RestRSIso : Prop := ∀ (p n' : ℕ) (R₁ R₂ : RS p n'), Nonempty (RSIso R₁ R₂)

def RestHLTransport : Prop :=
  ∀ (p n' : ℕ) (R₁ R₂ : RS p n') (I : RSIso R₁ R₂) (m : ℕ) (lam0 : Fin n' → Fin (m + 1) → ℤ),
    ∃ (Φ : Submodule R₁.W (Fin (m + 1) → R₁.Qq) ≃ Submodule R₂.W (Fin (m + 1) → R₂.Qq))
      (Ψ : Vsp R₁.Kf lam0 ≃+ Vsp R₂.Kf lam0),
      (∀ (c : R₁.Kf) v, Ψ (c • v) = I.φK c • Ψ v) ∧
      (∀ L, IsLattice R₁.W L ↔ IsLattice R₂.W (Φ L)) ∧
      (∀ (r : ℕ) (e : Edge R₁.W R₁.Qq (m + 1)), IsEdge p n' r e ↔ IsEdge p n' r ⟨Φ e.src, Φ e.tgt⟩) ∧
      (∀ L x, x ∈ HL (O := R₁.O) R₁.ι R₁.σ lam0 L ↔ Ψ x ∈ HL (O := R₂.O) R₂.ι R₂.σ lam0 (Φ L)) ∧
      (∀ (e : Edge R₁.W R₁.Qq (m + 1)) x, x ∈ HLe p R₁.ι R₁.σ R₁.w lam0 e ↔
        Ψ x ∈ HLe p R₂.ι R₂.σ R₂.w lam0 ⟨Φ e.src, Φ e.tgt⟩) ∧
      dimV R₁.Kf lam0 = dimV R₂.Kf lam0

section Formal

variable {O₁ K₁ V₁ O₂ K₂ V₂ : Type*} [CommRing O₁] [Field K₁] [Algebra O₁ K₁] [AddCommGroup V₁] [Module K₁ V₁]
  [Module O₁ V₁] [IsScalarTower O₁ K₁ V₁] [CommRing O₂] [Field K₂] [Algebra O₂ K₂] [AddCommGroup V₂] [Module K₂ V₂]
  [Module O₂ V₂] [IsScalarTower O₂ K₂ V₂] (φO : O₁ ≃+* O₂) (φK : K₁ ≃+* K₂) (Ψ : V₁ ≃+ V₂)

theorem sl_symm (hΨ : ∀ (c : K₁) v, Ψ (c • v) = φK c • Ψ v) (c : K₂) (v : V₂) :
    Ψ.symm (c • v) = φK.symm c • Ψ.symm v := by
  apply Ψ.injective
  rw [hΨ, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]

def dT (hΨ : ∀ (c : K₁) v, Ψ (c • v) = φK c • Ψ v) (G : Module.Dual K₁ V₁) : Module.Dual K₂ V₂ where
  toFun v := φK (G (Ψ.symm v))
  map_add' x y := by rw [map_add (f := _), map_add (f := _), map_add (f := _)]
  map_smul' c x := by
    rw [sl_symm φK Ψ hΨ, map_smul, smul_eq_mul, map_mul, RingEquiv.apply_symm_apply, RingHom.id_apply, smul_eq_mul]

theorem dT_apply (hΨ : ∀ (c : K₁) v, Ψ (c • v) = φK c • Ψ v) (G : Module.Dual K₁ V₁) (v : V₁) : dT φK Ψ hΨ G (Ψ v) = φK (G v) := by
  show φK (G (Ψ.symm (Ψ v))) = _
  rw [AddEquiv.symm_apply_apply]

theorem dT_smul (hΨ : ∀ (c : K₁) v, Ψ (c • v) = φK c • Ψ v) (c : K₁) (G : Module.Dual K₁ V₁) : dT φK Ψ hΨ (c • G) = φK c • dT φK Ψ hΨ G := by
  ext v
  show φK ((c • G) (Ψ.symm v)) = φK c • φK (G (Ψ.symm v))
  rw [LinearMap.smul_apply, smul_eq_mul, map_mul, smul_eq_mul]

theorem sl_scale (hΨ : ∀ (c : K₁) v, Ψ (c • v) = φK c • Ψ v) (c : K₁) {M : Submodule O₁ V₁} {M' : Submodule O₂ V₂} (h : ∀ x, x ∈ M ↔ Ψ x ∈ M') {x : V₁}
    (hx : x ∈ scale c M) : Ψ x ∈ scale (φK c) M' := by
  obtain ⟨y, hy, rfl⟩ := hx
  exact ⟨Ψ y, (h y).1 hy, (hΨ c y).symm⟩

theorem sl_scale2 (hΨ : ∀ (c : K₁) v, Ψ (c • v) = φK c • Ψ v) (c d : K₁) {M : Submodule O₁ V₁} {M' : Submodule O₂ V₂} (h : ∀ x, x ∈ M ↔ Ψ x ∈ M') {x : V₁}
    (hx : x ∈ scale c (scale d M)) : Ψ x ∈ scale (φK c) (scale (φK d) M') := by
  obtain ⟨y, hy, rfl⟩ := hx
  exact ⟨Ψ y, sl_scale φK Ψ hΨ d h hy, (hΨ c y).symm⟩

theorem sl_dual (hΨ : ∀ (c : K₁) v, Ψ (c • v) = φK c • Ψ v) (hOK : ∀ x, φK (algebraMap O₁ K₁ x) = algebraMap O₂ K₂ (φO x)) {M : Submodule O₁ V₁}
    {M' : Submodule O₂ V₂} (h : ∀ x, x ∈ M ↔ Ψ x ∈ M') {G : Module.Dual K₁ V₁}
    (hG : G ∈ Formalism.GradedWeylDivisibility.dualLat O₁ K₁ M) : dT φK Ψ hΨ G ∈ Formalism.GradedWeylDivisibility.dualLat O₂ K₂ M' := by
  intro v hv
  have h1 : Ψ.symm v ∈ M := (h _).2 (by rwa [AddEquiv.apply_symm_apply])
  obtain ⟨a, ha⟩ := hG _ h1
  exact ⟨φO a, by show _ = φK (G (Ψ.symm v)); rw [← ha, hOK]⟩

theorem sl_scale_dual (hΨ : ∀ (c : K₁) v, Ψ (c • v) = φK c • Ψ v) (hOK : ∀ x, φK (algebraMap O₁ K₁ x) = algebraMap O₂ K₂ (φO x)) (c : K₁)
    {M : Submodule O₁ V₁} {M' : Submodule O₂ V₂} (h : ∀ x, x ∈ M ↔ Ψ x ∈ M') {G : Module.Dual K₁ V₁}
    (hG : G ∈ scale c (Formalism.GradedWeylDivisibility.dualLat O₁ K₁ M)) :
    dT φK Ψ hΨ G ∈ scale (φK c) (Formalism.GradedWeylDivisibility.dualLat O₂ K₂ M') := by
  obtain ⟨G₀, hG₀, rfl⟩ := hG
  exact ⟨dT φK Ψ hΨ G₀, sl_dual φO φK Ψ hΨ hOK h hG₀, (dT_smul φK Ψ hΨ c G₀).symm⟩

end Formal

end Formalism.MainNotions.flipOneThree.Pf

end
end

section

noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree


open Classical in
def RestOddTops : Prop :=
  ∀ (n' : ℕ) (TT : Finset (Fin n')), 2 ≤ numSeg TT → ∀ f : Fin n' → Fin n' → ℕ → ℝ,
    ∑ j : Fin (numSeg TT), ∑ i : Fin (segS TT j), f (segPos TT j i) (segStart TT j) ((segDists TT j).get i) =
      ∑ y ∈ TT.filter (fun y => ¬ IsTypeV y), f y (yPrev TT y) (dPrev TT y)

theorem tle_abs (Ct C N N1 p k Q L ar a' b' La La' ccl cS n' S S' : ℝ) (hCt : 0 < Ct) (hC : 4 * Ct + 4 ≤ C)
    (hN : 1 ≤ N) (hN1 : 1 ≤ N1) (hp : 0 < p) (hk : 1 ≤ k) (hQ : 1 ≤ Q) (hL : 0 ≤ L) (har : 0 ≤ ar)
    (ha0 : 0 ≤ a') (ha : a' ≤ 2 * ar) (hb : 0 < b') (hLa : 0 ≤ La) (hLa0 : 0 ≤ La') (hLa' : La' ≤ 2 * La)
    (hccl : 0 ≤ ccl) (hcS : 0 ≤ cS) (hn' : 0 ≤ n') (hS : S' ≤ S + N * ccl) :
    (S' + Ct * N * (a' / p ^ 2 + b' / p + La' * a' / (p * k) + La' * b' / k + k * Q +
        Q * (cS + 2 * N * ccl + 2 * n' * ccl))) + N * (La' * b' / k) + 1 + 2 * n' * ccl ≤
      S + C * N * N1 * (ar / p ^ 2 + b' / p + La * ar / (p * k) + La * b' / k) +
        C * N * (Q * (cS + C * N * k * L + 4 * N * ccl + 2 * n' * ccl) + k * Q + k * L + ccl) + 2 * n' * ccl := by
  have hN0 : 0 ≤ N := by linarith
  have hk0 : 0 < k := by linarith
  have hQ0 : 0 ≤ Q := by linarith
  have hC0 : 0 ≤ C := by linarith
  have hCN1 : C ≤ C * N1 := by nlinarith
  have hp2 : 0 < p ^ 2 := by positivity
  have hA : a' / p ^ 2 ≤ 2 * (ar / p ^ 2) := by
    rw [← mul_div_assoc]
    exact div_le_div_of_nonneg_right ha hp2.le
  have hA0 : 0 ≤ ar / p ^ 2 := by positivity
  have hB0 : 0 ≤ b' / p := by positivity
  have hE : La' * a' / (p * k) ≤ 4 * (La * ar / (p * k)) := by
    rw [← mul_div_assoc]
    apply div_le_div_of_nonneg_right _ (by positivity)
    have := mul_le_mul hLa' ha ha0 (by linarith : (0 : ℝ) ≤ 2 * La)
    linarith
  have hE0 : 0 ≤ La * ar / (p * k) := by positivity
  have hF : La' * b' / k ≤ 2 * (La * b' / k) := by
    rw [← mul_div_assoc]
    apply div_le_div_of_nonneg_right _ hk0.le
    nlinarith
  have hF0 : 0 ≤ La * b' / k := by positivity
  have hF'0 : 0 ≤ La' * b' / k := by positivity
  have t1 : Ct * N * (a' / p ^ 2) ≤ C * N * N1 * (ar / p ^ 2) := by
    have h1 := mul_le_mul_of_nonneg_left hA (mul_nonneg hCt.le hN0)
    have h2 := mul_le_mul_of_nonneg_right (by linarith : 2 * Ct ≤ C * N1) (mul_nonneg hN0 hA0)
    nlinarith
  have t2 : Ct * N * (b' / p) ≤ C * N * N1 * (b' / p) := by
    have h2 := mul_le_mul_of_nonneg_right (by linarith : Ct ≤ C * N1) (mul_nonneg hN0 hB0)
    nlinarith
  have t3 : Ct * N * (La' * a' / (p * k)) ≤ C * N * N1 * (La * ar / (p * k)) := by
    have h1 := mul_le_mul_of_nonneg_left hE (mul_nonneg hCt.le hN0)
    have h2 := mul_le_mul_of_nonneg_right (by linarith : 4 * Ct ≤ C * N1) (mul_nonneg hN0 hE0)
    nlinarith
  have t4 : Ct * N * (La' * b' / k) + N * (La' * b' / k) ≤ C * N * N1 * (La * b' / k) := by
    have h1 := mul_le_mul_of_nonneg_left hF (mul_nonneg (by linarith : (0 : ℝ) ≤ Ct + 1) hN0)
    have h2 := mul_le_mul_of_nonneg_right (by linarith : 2 * Ct + 2 ≤ C * N1) (mul_nonneg hN0 hF0)
    nlinarith
  have hNkQ : 1 ≤ N * k * Q := by
    have := one_le_mul_of_one_le_of_one_le hN hk
    exact one_le_mul_of_one_le_of_one_le this hQ
  have t5 : Ct * N * (k * Q) + 1 ≤ C * N * (k * Q) := by
    have h2 := mul_le_mul_of_nonneg_right (by linarith : (4 : ℝ) ≤ C - Ct) (by linarith : (0 : ℝ) ≤ N * k * Q)
    nlinarith
  have hX0 : 0 ≤ cS + 2 * N * ccl + 2 * n' * ccl := by positivity
  have hXY : cS + 2 * N * ccl + 2 * n' * ccl ≤ cS + C * N * k * L + 4 * N * ccl + 2 * n' * ccl := by
    have : 0 ≤ C * N * k * L := by positivity
    have : 0 ≤ N * ccl := by positivity
    linarith
  have t6 : Ct * N * (Q * (cS + 2 * N * ccl + 2 * n' * ccl)) ≤
      C * N * (Q * (cS + C * N * k * L + 4 * N * ccl + 2 * n' * ccl)) := by
    apply mul_le_mul (mul_le_mul_of_nonneg_right (by linarith) hN0)
      (mul_le_mul_of_nonneg_left hXY hQ0) (mul_nonneg hQ0 hX0) (mul_nonneg hC0 hN0)
  have t7 : N * ccl ≤ C * N * (k * L + ccl) := by
    have : 0 ≤ C * N * (k * L) := by positivity
    have h2 := mul_le_mul_of_nonneg_right (by linarith : (1 : ℝ) ≤ C) (mul_nonneg hN0 hccl)
    linarith
  linarith [t1, t2, t3, t4, t5, t6, t7]

theorem initial_level_formula (K : Cst) (X : Dat) (A B : X.TT → ℕ) :
    X.t0 K A B = (∑ j : Fin (numSeg X.TT), ∑ i : Fin (segS X.TT j),
        min ((ex B (segPos X.TT j i) : ℕ) : ℝ)
          (((ex A (segStart X.TT j) : ℕ) : ℝ) / (X.p : ℝ) ^ ((segDists X.TT j).get i))) +
      K.Ct * X.N * ((X.a : ℝ) / (X.p : ℝ) ^ 2 + X.b' / X.p + LaI K.C₀ X.N₁ X.a * X.a / (X.p * X.k) +
        LaI K.C₀ X.N₁ X.a * X.b' / X.k + X.k * (X.p : ℝ) ^ X.G' +
        (X.p : ℝ) ^ X.G' * ((X.cStar : ℝ) + 2 * X.N * X.ccl + 2 * X.n' * X.ccl)) := by
  unfold Dat.t0 t0I t0G4 Dat.c4 Dat.N Dat.k
  push_cast
  ring

end Formalism.MainNotions.flipOneThree.Pf

end
end

section

noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.GradedWeylDivisibility MvPolynomial

def wtPQ (m P Q : ℕ) : Fin (m + 1) → ℤ := fun i => if i = 0 then (P : ℤ) else if i = Fin.last m then -(Q : ℤ) else 0

def twoLat (O : Type) {Kf : Type} [CommRing O] [Field Kf] [Algebra O Kf] (m P Q : ℕ)
    (Λ : Submodule O (Fin (m + 1) → Kf)) : Submodule O (MvPolynomial (Bool × (Fin (m + 1) × Fin (m + 1))) Kf) :=
  tensorLat O Kf fun b : Bool => H0 O m (letterWt m (if b then P else Q) b) Λ

def twoSp (Kf : Type) [Field Kf] (m P Q : ℕ) : Submodule Kf (MvPolynomial (Bool × (Fin (m + 1) × Fin (m + 1))) Kf) :=
  tensorLat Kf Kf fun b : Bool => dualWeyl Kf (m + 1) (m + 1) (nuOf (letterWt m (if b then P else Q) b))

def SingleWeightLatticeComparison : Prop :=
  ∀ (p n' : ℕ) (R : RS p n') (m : ℕ), 2 ≤ m → ∀ (a P Q : ℕ), P + Q + 1 ≤ 8 * a →
    ∃ (i : ℕ → MvPolynomial (Fin (m + 1) × Fin (m + 1)) R.Kf →ₗ[R.Kf]
        MvPolynomial (Bool × (Fin (m + 1) × Fin (m + 1))) R.Kf)
      (pr : ℕ → MvPolynomial (Bool × (Fin (m + 1) × Fin (m + 1))) R.Kf →ₗ[R.Kf]
        MvPolynomial (Fin (m + 1) × Fin (m + 1)) R.Kf),
      (∀ x ∈ twoSp R.Kf m P Q, ∑ j ∈ Finset.range (min P Q + 1), i j (pr j x) = x) ∧
      (∀ j ≤ min P Q,
        (∀ x ∈ twoSp R.Kf m P Q, pr j x ∈ dualWeyl R.Kf (m + 1) (m + 1) (nuOf (wtPQ m (P - j) (Q - j)))) ∧
        (∀ y ∈ dualWeyl R.Kf (m + 1) (m + 1) (nuOf (wtPQ m (P - j) (Q - j))), i j y ∈ twoSp R.Kf m P Q)) ∧
      ∀ Λ : Submodule R.O (Fin (m + 1) → R.Kf), IsLattice R.O Λ → ∀ j ≤ min P Q,
        (∀ x ∈ twoLat R.O m P Q Λ,
          ((p : R.Kf) ^ ⌈((m : ℝ) + 2) * lgA p a m⌉₊) • pr j x ∈ H0 R.O m (wtPQ m (P - j) (Q - j)) Λ) ∧
        (∀ y ∈ H0 R.O m (wtPQ m (P - j) (Q - j)) Λ,
          ((p : R.Kf) ^ ⌈((m : ℝ) + 2) * lgA p a m⌉₊) • i j y ∈ twoLat R.O m P Q Λ)

end Formalism.MainNotions.flipOneThree.Pf

end
end

section

noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree

namespace Dat

variable (X : Dat) (K : Cst)

def ua : ℕ := ⌊X.ar + X.ar / (X.k * X.Y)⌋₊

def lb : ℕ := ⌈X.bl⌉₊

def ub : ℕ := ⌊X.bu⌋₊

def Wa (τ : ℕ) : Finset ℕ := Finset.Icc (X.a + τ) (X.ua + τ)

def Wb (τ : ℕ) : Finset ℕ := Finset.Icc (X.lb + τ) (X.ub + τ)

def WaP : Finset ℕ := Finset.Icc X.a (X.ua + X.Jn K + X.ccl)

def WbP : Finset ℕ := Finset.Icc X.lb (X.ub + X.Jn K + X.ccl)

end Dat

def meanN {ι : Type} [Fintype ι] [DecidableEq ι] (Sa Sb : Finset ℕ) (f : (ι → ℕ) → (ι → ℕ) → ℝ) : ℝ :=
  (∑ A ∈ Fintype.piFinset (fun _ : ι => Sa), ∑ B ∈ Fintype.piFinset (fun _ : ι => Sb), f A B) /
    ((Sa.card : ℝ) ^ Fintype.card ι * (Sb.card : ℝ) ^ Fintype.card ι)

def RestDims : Prop :=
  ∀ (p n' : ℕ) (R : RS p n') (m : ℕ), 1 ≤ m → ∀ (TT : Finset (Fin n')) (A B : TT → ℕ),
    dimHH (m := m) R.Kf TT (ex A) (ex B) = ∏ s, Formalism.CountingSumsFrames.dimPol m (A s) * Formalism.CountingSumsFrames.dimPol m (B s) ∧
    dimV R.Kf (flatW m A B) = ∏ s, Formalism.CountingSumsFrames.dimHar m (A s) (B s)

def KeyIneq (K : Cst) (X : Dat) (R : RS X.p X.n') : Prop :=
  ∀ A ∈ Fintype.piFinset (fun _ : X.TT => X.WaP K), ∀ B ∈ Fintype.piFinset (fun _ : X.TT => X.WbP K),
    ∑ j ∈ Fintype.piFinset (fun _ : X.TT => Finset.range (X.Jn K + 1)),
        X.kF K R (fun s => A s - j s) (fun s => B s - j s) *
          dL R (flatW X.m (fun s => A s - j s) (fun s => B s - j s)) ≤
      X.kx K R A B * ((dimHH (m := X.m) R.Kf X.TT (ex A) (ex B) : ℝ) / gaussianNumber (X.p ^ X.n') (X.m + 1))

def Avg (K : Cst) (X : Dat) (R : RS X.p X.n') (τ : ℕ) : Prop :=
  meanN (X.Wa τ) (X.Wb τ) (X.kF K R) ≤ 2 * meanN (X.WaP K) (X.WbP K) (X.kx K R)

def MeanX (K : Cst) (X : Dat) (R : RS X.p X.n') : Prop :=
  meanN (X.WaP K) (X.WbP K) (X.kx K R) ≤ (K.CA + K.Cs) * X.N * X.N₁ / X.Y

def MidMean (D : Formalism.BasicNotions.D7) (K : Cst) (F : Dat → Prop) : Prop :=
  K.admitted D → ∀ X : Dat, F X → ∀ R : RS X.p X.n',
    meanKap X.TT X.m X.Y X.ar X.bl X.bu (X.kText K R) ≤ K.Cmean * X.TT.card * X.N₁ / X.Y

end Formalism.MainNotions.flipOneThree.Pf

end
end
