module

public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle043
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle002
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.NatCastMulApply
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle001
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle044
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormDwLeSobNorm
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
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
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle003
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.SmoothForms Matrix
open NumberField IsDedekindDomain
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SmoothForms

theorem denom_norm_natCast_le_one {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (n : ℕ) :
    ‖(n : v.adicCompletion F)‖ ≤ 1 := by
  first
  | exact @_root_.GlobalTheory.AdicNatCastNorm.norm_natCast_adicCompletion_le_one
  | exact _root_.GlobalTheory.AdicNatCastNorm.norm_natCast_adicCompletion_le_one
  | (apply _root_.GlobalTheory.AdicNatCastNorm.norm_natCast_adicCompletion_le_one <;> assumption)

theorem denom_global {F : Type} [Field F] [NumberField F] (H : HeightOneSpectrum (𝓞 F) → NNReal)
    (hH : ∀ v, 1 ≤ H v) (hf : (Function.mulSupport H).Finite) :
    ∃ d : ℕ, 0 < d ∧ (d : NNReal) ≤ ∏ᶠ v, H v ∧
      ∀ v, ∀ y : v.adicCompletion F, ‖y‖₊ ≤ H v → ‖(d : v.adicCompletion F) * y‖ ≤ 1 := by
  first
  | exact @_root_.GlobalTheory.AdicNormZpowEstimates.exists_denominator
  | exact _root_.GlobalTheory.AdicNormZpowEstimates.exists_denominator
  | (apply _root_.GlobalTheory.AdicNormZpowEstimates.exists_denominator <;> assumption)

theorem denom_exists_int {E : Type} [Field E] [NumberField E] (e : E) :
    ∃ k : ℕ, 0 < k ∧ ∃ r : 𝓞 E, (r : E) = k * e := by
  first
  | exact @_root_.GlobalTheory.NatMulMemRingOfIntegers.exists_nat_mul_mem_ringOfIntegers
  | exact _root_.GlobalTheory.NatMulMemRingOfIntegers.exists_nat_mul_mem_ringOfIntegers
  | (apply _root_.GlobalTheory.NatMulMemRingOfIntegers.exists_nat_mul_mem_ringOfIntegers <;> assumption)


open GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies Formalism.L2.Pj in
theorem denomBound : ∀ (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D),
    DenomBound θ V := by
  first
  | exact @_root_.GlobalTheory.AdeleDenominators.denomBound

end GlobalTheory.SmoothForms
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.SmoothForms Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance 100] LieRing.ofAssociativeRing

theorem _root_.GlobalTheory.T.exists_finite_cosets_adelicUnitary_bounded_denominator : ∀ (D : D7) (V : HSp D) (U : Subgroup (GA D V)), IsOpen (U : Set (GA D V)) → ∀ d : ℕ, 0 < d → ∃ S : Finset (GA D V), ∀ k ∈ GfC V, BddDen V d k → ∃ x ∈ S, x⁻¹ * k ∈ U ∧ x⁻¹ * k ∈ GfC V := by
  first | exact @GlobalTheory.SmoothForms.Cover.exists_finset_cover | exact GlobalTheory.SmoothForms.Cover.exists_finset_cover | (intros; apply GlobalTheory.SmoothForms.Cover.exists_finset_cover <;> assumption)
end

section

noncomputable section

open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum

namespace GlobalTheory.TypeSum.CoefClos

variable {n : ℕ}

abbrev Ltr (ε : Fin n → Bool) : Type := {X : Mx n // X ∈ lieSet ε} ⊕ {k : Mx n // k ∈ Kset ε}

section Vec

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def ltrV (σ : Mx n → (H →L[ℂ] H)) {ε : Fin n → Bool} : Ltr ε → H → H
  | Sum.inl X => dRep σ X.1
  | Sum.inr k => σ k.1

def wordV (σ : Mx n → (H →L[ℂ] H)) {ε : Fin n → Bool} (u : List (Ltr ε)) (v : H) : H := u.foldr (ltrV σ) v

end Vec

def rder (X : Mx n) (f : Mx n → ℂ) (g : Mx n) : ℂ := deriv (fun t : ℝ => f (g * NormedSpace.exp (t • X))) 0

def ltrF {ε : Fin n → Bool} : Ltr ε → (Mx n → ℂ) → Mx n → ℂ
  | Sum.inl X => rder X.1
  | Sum.inr k => fun f g => f (g * k.1)

def wordF {ε : Fin n → Bool} (u : List (Ltr ε)) (f : Mx n → ℂ) : Mx n → ℂ := u.foldr ltrF f

def wordE {M : Type} [AddCommGroup M] [Module ℂ M] {ε : Fin n → Bool} (τ : Ltr ε → Module.End ℂ M)
    (u : List (Ltr ε)) (m : M) : M := u.foldr (fun x => τ x) m

def CSm (ε : Fin n → Bool) (f : Mx n → ℂ) : Prop :=
  ∃ F : List (Mx n) → Mx n → ℂ, (∀ g ∈ UJset ε, F [] g = f g) ∧ IsDerFam ε F ∧
    ∀ l : List (Mx n), (∀ Y ∈ l, Y ∈ lieSet ε) → ContinuousOn (F l) (UJset ε)

variable {ε : Fin n → Bool}

theorem CSm.congr {f f' : Mx n → ℂ} (h : CSm ε f) (e : ∀ g ∈ UJset ε, f g = f' g) : CSm ε f' := by
  obtain ⟨F, h1, h2, h3⟩ := h
  exact ⟨F, fun g hg => (h1 g hg).trans (e g hg), h2, h3⟩

theorem CSm.add {f f' : Mx n → ℂ} (h : CSm ε f) (h' : CSm ε f') : CSm ε (f + f') := by
  obtain ⟨F, h1, h2, h3⟩ := h
  obtain ⟨F', k1, k2, k3⟩ := h'
  refine ⟨fun l g => F l g + F' l g, fun g hg => by simp [h1 g hg, k1 g hg], fun l hl X hX g hg => ?_,
    fun l hl => (h3 l hl).add (k3 l hl)⟩
  exact (h2 l hl X hX g hg).add (k2 l hl X hX g hg)

theorem CSm.smul {f : Mx n → ℂ} (h : CSm ε f) (c : ℂ) : CSm ε (c • f) := by
  obtain ⟨F, h1, h2, h3⟩ := h
  refine ⟨fun l g => c * F l g, fun g hg => by simp [h1 g hg], fun l hl X hX g hg => ?_,
    fun l hl => continuousOn_const.mul (h3 l hl)⟩
  exact (h2 l hl X hX g hg).const_mul c

theorem CSm.zero : CSm ε (0 : Mx n → ℂ) :=
  ⟨fun _ _ => 0, fun _ _ => rfl, fun _ _ _ _ _ _ => hasDerivAt_const _ _, fun _ _ => continuousOn_const⟩

theorem CSm.hasDerivAt {f : Mx n → ℂ} (h : CSm ε f) {X : Mx n} (hX : X ∈ lieSet ε) {g : Mx n} (hg : g ∈ UJset ε) :
    HasDerivAt (fun t : ℝ => f (g * NormedSpace.exp (t • X))) (rder X f g) 0 := by
  obtain ⟨F, h1, h2, -⟩ := h
  have h0 : HasDerivAt (fun t : ℝ => f (g * NormedSpace.exp (t • X))) (F [X] g) 0 := by
    refine (h2 [] (by simp) X hX g hg).congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
    exact (h1 _ (mul_mem_UJ hg (exp_mem_UJ hX t))).symm
  rwa [rder, h0.deriv]

theorem CSm.rder_eq {f : Mx n → ℂ} {F : List (Mx n) → Mx n → ℂ} (h1 : ∀ g ∈ UJset ε, F [] g = f g)
    (h2 : IsDerFam ε F) {X : Mx n} (hX : X ∈ lieSet ε) {g : Mx n} (hg : g ∈ UJset ε) : rder X f g = F [X] g := by
  have h0 : HasDerivAt (fun t : ℝ => f (g * NormedSpace.exp (t • X))) (F [X] g) 0 := by
    refine (h2 [] (by simp) X hX g hg).congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
    exact (h1 _ (mul_mem_UJ hg (exp_mem_UJ hX t))).symm
  rw [rder, h0.deriv]

theorem CSm.rder {f : Mx n → ℂ} (h : CSm ε f) {X : Mx n} (hX : X ∈ lieSet ε) : CSm ε (rder X f) := by
  obtain ⟨F, h1, h2, h3⟩ := h
  refine ⟨fun l => F (l ++ [X]), fun g hg => (CSm.rder_eq h1 h2 hX hg).symm, fun l hl Y hY g hg => ?_,
    fun l hl => h3 _ ?_⟩
  · exact h2 (l ++ [X]) (fun Z hZ => (List.mem_append.1 hZ).elim (hl Z) (by simp_all)) Y hY g hg
  · exact fun Z hZ => (List.mem_append.1 hZ).elim (hl Z) (by simp_all)

theorem exp_conj_smul {k : Mx n} (hk : k ∈ UJset ε) (Y : Mx n) (t : ℝ) :
    k⁻¹ * NormedSpace.exp (t • Y) * k = NormedSpace.exp (t • (k⁻¹ * Y * k)) := by
  have hu : IsUnit k⁻¹ := (isUnit_of_UJ (inv_mem_UJ hk))
  have e := Matrix.exp_conj k⁻¹ (t • Y) hu
  rw [Matrix.nonsing_inv_nonsing_inv _ ((isUnit_iff_isUnit_det _).1 (isUnit_of_UJ hk))] at e
  rw [← e, Matrix.mul_smul, Matrix.smul_mul]

theorem CSm.rt {f : Mx n → ℂ} (h : CSm ε f) {k : Mx n} (hk : k ∈ Kset ε) : CSm ε (fun g => f (g * k)) := by
  obtain ⟨F, h1, h2, h3⟩ := h
  have hkU := K_le_UJ hk
  refine ⟨fun l g => F (l.map fun Y => k⁻¹ * Y * k) (g * k), fun g hg => by simpa using h1 _ (mul_mem_UJ hg hkU),
    fun l hl Y hY g hg => ?_, fun l hl => ?_⟩
  · have hl' : ∀ Z ∈ l.map (fun Y => k⁻¹ * Y * k), Z ∈ lieSet ε := by
      intro Z hZ
      obtain ⟨Z, hZ', rfl⟩ := List.mem_map.1 hZ
      exact conj_mem_lie (isUnit_Jm ε) hkU (hl Z hZ')
    have hY' : k⁻¹ * Y * k ∈ lieSet ε := conj_mem_lie (isUnit_Jm ε) hkU hY
    have := h2 _ hl' _ hY' (g * k) (mul_mem_UJ hg hkU)
    refine this.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
    show F _ (g * NormedSpace.exp (t • Y) * k) = F _ (g * k * NormedSpace.exp (t • (k⁻¹ * Y * k)))
    rw [← exp_conj_smul hkU Y t]
    congr 1
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_assoc g k, mul_inv_UJ hkU, Matrix.mul_one]
  · have hl' : ∀ Z ∈ l.map (fun Y => k⁻¹ * Y * k), Z ∈ lieSet ε := by
      intro Z hZ
      obtain ⟨Z, hZ', rfl⟩ := List.mem_map.1 hZ
      exact conj_mem_lie (isUnit_Jm ε) hkU (hl Z hZ')
    exact (h3 _ hl').comp (continuous_id.mul continuous_const).continuousOn fun g hg => mul_mem_UJ hg hkU

theorem CSm.ltrF {f : Mx n → ℂ} (h : CSm ε f) (x : Ltr ε) : CSm ε (ltrF x f) := by
  rcases x with X | k
  · exact h.rder X.2
  · exact h.rt k.2

theorem CSm.wordF {f : Mx n → ℂ} (h : CSm ε f) (u : List (Ltr ε)) : CSm ε (wordF u f) := by
  induction u with
  | nil => exact h
  | cons x u ih => exact ih.ltrF x

def Smo (ε : Fin n → Bool) : Submodule ℂ (Mx n → ℂ) where
  carrier := {f | (∀ g ∉ UJset ε, f g = 0) ∧ CSm ε f}
  add_mem' := fun {f f'} hf hf' => ⟨fun g hg => by simp [hf.1 g hg, hf'.1 g hg], hf.2.add hf'.2⟩
  zero_mem' := ⟨fun _ _ => rfl, CSm.zero⟩
  smul_mem' := fun c f hf => ⟨fun g hg => by simp [hf.1 g hg], hf.2.smul c⟩

theorem not_mem_of_mul_exp {X : Mx n} (hX : X ∈ lieSet ε) {g : Mx n} (hg : g ∉ UJset ε) (t : ℝ) :
    g * NormedSpace.exp (t • X) ∉ UJset ε := by
  intro h
  apply hg
  have := mul_mem_UJ h (exp_mem_UJ hX (-t))
  rwa [Matrix.mul_assoc, ← exp_add_smul, add_neg_cancel, zero_smul, NormedSpace.exp_zero, Matrix.mul_one] at this

theorem rder_off {f : Mx n → ℂ} (hf : ∀ g ∉ UJset ε, f g = 0) {X : Mx n} (hX : X ∈ lieSet ε) {g : Mx n}
    (hg : g ∉ UJset ε) : rder X f g = 0 := by
  have : (fun t : ℝ => f (g * NormedSpace.exp (t • X))) = fun _ => 0 :=
    funext fun t => hf _ (not_mem_of_mul_exp hX hg t)
  rw [rder, this, deriv_const]

theorem rt_off {f : Mx n → ℂ} (hf : ∀ g ∉ UJset ε, f g = 0) {k : Mx n} (hk : k ∈ Kset ε) {g : Mx n}
    (hg : g ∉ UJset ε) : f (g * k) = 0 := by
  refine hf _ fun h => hg ?_
  have := mul_mem_UJ h (inv_mem_UJ (K_le_UJ hk))
  rwa [Matrix.mul_assoc, mul_inv_UJ (K_le_UJ hk), Matrix.mul_one] at this

theorem ltrF_mem {f : Mx n → ℂ} (hf : f ∈ Smo ε) (x : Ltr ε) : ltrF x f ∈ Smo ε := by
  refine ⟨fun g hg => ?_, hf.2.ltrF x⟩
  rcases x with X | k
  · exact rder_off hf.1 X.2 hg
  · exact rt_off hf.1 k.2 hg

theorem rder_add {f f' : Mx n → ℂ} (hf : f ∈ Smo ε) (hf' : f' ∈ Smo ε) {X : Mx n} (hX : X ∈ lieSet ε) :
    rder X (f + f') = rder X f + rder X f' := by
  funext g
  by_cases hg : g ∈ UJset ε
  · exact ((hf.2.hasDerivAt hX hg).add (hf'.2.hasDerivAt hX hg)).deriv
  · simp [rder_off (Submodule.add_mem _ hf hf').1 hX hg, rder_off hf.1 hX hg, rder_off hf'.1 hX hg]

theorem rder_smul {f : Mx n → ℂ} (hf : f ∈ Smo ε) (c : ℂ) {X : Mx n} (hX : X ∈ lieSet ε) :
    rder X (c • f) = c • rder X f := by
  funext g
  by_cases hg : g ∈ UJset ε
  · exact ((hf.2.hasDerivAt hX hg).const_mul c).deriv
  · simp [rder_off (Submodule.smul_mem _ c hf).1 hX hg, rder_off hf.1 hX hg]

def ltrM (x : Ltr ε) : Module.End ℂ (Smo ε) where
  toFun f := ⟨ltrF x f.1, ltrF_mem f.2 x⟩
  map_add' f f' := by
    apply Subtype.ext
    rcases x with X | k
    · exact rder_add f.2 f'.2 X.2
    · rfl
  map_smul' c f := by
    apply Subtype.ext
    rcases x with X | k
    · exact rder_smul f.2 c X.2
    · rfl

theorem coe_wordE (u : List (Ltr ε)) (f : Smo ε) : ((wordE ltrM u f : Smo ε) : Mx n → ℂ) = wordF u f := by
  induction u with
  | nil => rfl
  | cons x u ih =>
    show ltrF x (wordE ltrM u f : Smo ε).1 = ltrF x (wordF u f.1)
    rw [ih]

theorem wordF_congr {f f' : Mx n → ℂ} (e : ∀ g ∈ UJset ε, f g = f' g) (u : List (Ltr ε)) :
    ∀ g ∈ UJset ε, wordF u f g = wordF u f' g := by
  induction u with
  | nil => exact e
  | cons x u ih =>
    intro g hg
    rcases x with X | k
    · show deriv _ 0 = deriv _ 0
      congr 1
      funext t
      exact ih _ (mul_mem_UJ hg (exp_mem_UJ X.2 t))
    · exact ih _ (mul_mem_UJ hg (K_le_UJ k.2))

end GlobalTheory.TypeSum.CoefClos

end
end

section

noncomputable section

open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.TypeSum GlobalTheory.LowTypeDetermined
open scoped InnerProductSpace

namespace GlobalTheory.TypeSum.CasBasis

variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Mx n → (H →L[ℂ] H)}

def casOp (σ : Mx n → (H →L[ℂ] H)) {d e : ℕ} (X : Fin d → Mx n) (Y : Fin e → Mx n) (v : H) : H :=
  ∑ b, dRep σ (Y b) (dRep σ (Y b) v) - ∑ i, dRep σ (X i) (dRep σ (X i) v)

theorem sm_dRep_sq (hσ : IsURepOn (UJset ε) σ) {Z : Mx n} (hZ : Z ∈ lieSet ε) {v : H} (hv : Sm ε σ v) :
    Sm ε σ (dRep σ Z (dRep σ Z v)) :=
  dRep_mem (isUnit_Jm ε) hσ (dRep_mem (isUnit_Jm ε) hσ hv hZ) hZ

theorem inner_dRep_sq (hσ : IsURepOn (UJset ε) σ) {Z : Mx n} (hZ : Z ∈ lieSet ε) {b v : H} (hb : Sm ε σ b)
    (hv : Sm ε σ v) : ⟪b, dRep σ Z (dRep σ Z v)⟫_ℂ = ⟪dRep σ Z (dRep σ Z b), v⟫_ℂ := by
  have hv1 := dRep_mem (isUnit_Jm ε) hσ hv hZ
  have hb1 := dRep_mem (isUnit_Jm ε) hσ hb hZ
  rw [inner_dRep (isUnit_Jm ε) hσ hb hv1 hZ, inner_dRep (isUnit_Jm ε) hσ hb1 hv hZ, neg_neg]

variable {d e : ℕ} {X : Fin d → Mx n} {Y : Fin e → Mx n}

theorem sm_casOp (hσ : IsURepOn (UJset ε) σ) (hX : ∀ i, X i ∈ lieSet ε) (hY : ∀ b, Y b ∈ lieSet ε) {v : H}
    (hv : Sm ε σ v) : Sm ε σ (casOp σ X Y v) :=
  (smooth (Jm ε) σ).sub_mem ((smooth (Jm ε) σ).sum_mem fun b _ => sm_dRep_sq hσ (hY b) hv)
    ((smooth (Jm ε) σ).sum_mem fun i _ => sm_dRep_sq hσ (hX i) hv)

theorem inner_casOp (hσ : IsURepOn (UJset ε) σ) (hX : ∀ i, X i ∈ lieSet ε) (hY : ∀ b, Y b ∈ lieSet ε) {b v : H}
    (hb : Sm ε σ b) (hv : Sm ε σ v) : ⟪b, casOp σ X Y v⟫_ℂ = ⟪casOp σ X Y b, v⟫_ℂ := by
  simp only [casOp, inner_sub_left, inner_sub_right, inner_sum, sum_inner, inner_dRep_sq hσ (hX _) hb hv,
    inner_dRep_sq hσ (hY _) hb hv]

theorem casOp_add (hσ : IsURepOn (UJset ε) σ) (hX : ∀ i, X i ∈ lieSet ε) (hY : ∀ b, Y b ∈ lieSet ε) {x y : H}
    (hx : Sm ε σ x) (hy : Sm ε σ y) : casOp σ X Y (x + y) = casOp σ X Y x + casOp σ X Y y := by
  have h : ∀ Z ∈ lieSet ε, dRep σ Z (dRep σ Z (x + y)) = dRep σ Z (dRep σ Z x) + dRep σ Z (dRep σ Z y) :=
    fun Z hZ => Dw_add hσ (l := [Z, Z]) (by simp [hZ]) hx hy
  simp only [casOp, h _ (hX _), h _ (hY _), Finset.sum_add_distrib]
  abel

theorem casOp_smul (hσ : IsURepOn (UJset ε) σ) (hX : ∀ i, X i ∈ lieSet ε) (hY : ∀ b, Y b ∈ lieSet ε) (c : ℂ)
    {x : H} (hx : Sm ε σ x) : casOp σ X Y (c • x) = c • casOp σ X Y x := by
  have h : ∀ Z ∈ lieSet ε, dRep σ Z (dRep σ Z (c • x)) = c • dRep σ Z (dRep σ Z x) :=
    fun Z hZ => Dw_smul hσ (l := [Z, Z]) (by simp [hZ]) c hx
  simp only [casOp, h _ (hX _), h _ (hY _), ← Finset.smul_sum, smul_sub]

end GlobalTheory.TypeSum.CasBasis

end
end

section

noncomputable section

open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined
open scoped InnerProductSpace

namespace GlobalTheory.TypeSum

variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Mx n → (H →L[ℂ] H)}

def onePlusCas (σ : Mx n → (H →L[ℂ] H)) {d : ℕ} (X : Fin d → Mx n) (v : H) : H :=
  v - ∑ i, dRep σ (X i) (dRep σ (X i) v)

theorem sm_onePlusCas (hσ : IsURepOn (UJset ε) σ) {d : ℕ} {X : Fin d → Mx n} (hX : ∀ i, X i ∈ lieSet ε)
    {v : H} (hv : Sm ε σ v) : Sm ε σ (onePlusCas σ X v) := by
  have h1 : ∀ i, Sm ε σ (dRep σ (X i) (dRep σ (X i) v)) := fun i =>
    dRep_mem (isUnit_Jm ε) hσ (dRep_mem (isUnit_Jm ε) hσ hv (hX i)) (hX i)
  exact (smooth (Jm ε) σ).sub_mem hv ((smooth (Jm ε) σ).sum_mem fun i _ => h1 i)

theorem sm_iterate_onePlusCas (hσ : IsURepOn (UJset ε) σ) {d : ℕ} {X : Fin d → Mx n} (hX : ∀ i, X i ∈ lieSet ε)
    {v : H} (hv : Sm ε σ v) (r : ℕ) : Sm ε σ ((onePlusCas σ X)^[r] v) := by
  induction r with
  | zero => simpa using hv
  | succ r ih => rw [Function.iterate_succ_apply']; exact sm_onePlusCas hσ hX ih

theorem inner_onePlusCas (hσ : IsURepOn (UJset ε) σ) {d : ℕ} {X : Fin d → Mx n} (hX : ∀ i, X i ∈ lieSet ε)
    {b v : H} (hb : Sm ε σ b) (hv : Sm ε σ v) : ⟪b, onePlusCas σ X v⟫_ℂ = ⟪onePlusCas σ X b, v⟫_ℂ := by
  have key : ∀ i, ⟪b, dRep σ (X i) (dRep σ (X i) v)⟫_ℂ = ⟪dRep σ (X i) (dRep σ (X i) b), v⟫_ℂ := fun i => by
    have hv1 := dRep_mem (isUnit_Jm ε) hσ hv (hX i)
    have hb1 := dRep_mem (isUnit_Jm ε) hσ hb (hX i)
    rw [inner_dRep (isUnit_Jm ε) hσ hb hv1 (hX i), inner_dRep (isUnit_Jm ε) hσ hb1 hv (hX i), neg_neg]
  simp only [onePlusCas, inner_sub_left, inner_sub_right, inner_sum, sum_inner, key]

theorem inner_iterate_onePlusCas (hσ : IsURepOn (UJset ε) σ) {d : ℕ} {X : Fin d → Mx n}
    (hX : ∀ i, X i ∈ lieSet ε) {b v : H} (hb : Sm ε σ b) (hv : Sm ε σ v) (r : ℕ) :
    ⟪b, (onePlusCas σ X)^[r] v⟫_ℂ = ⟪(onePlusCas σ X)^[r] b, v⟫_ℂ := by
  induction r generalizing v with
  | zero => rfl
  | succ r ih =>
    rw [Function.iterate_succ_apply, ih (sm_onePlusCas hσ hX hv), Function.iterate_succ_apply',
      inner_onePlusCas hσ hX (sm_iterate_onePlusCas hσ hX hb r) hv]

theorem onePlusCas_smul (hσ : IsURepOn (UJset ε) σ) {d : ℕ} {X : Fin d → Mx n} (hX : ∀ i, X i ∈ lieSet ε)
    (c : ℂ) {v : H} (hv : Sm ε σ v) : onePlusCas σ X (c • v) = c • onePlusCas σ X v := by
  have h : ∀ i, dRep σ (X i) (dRep σ (X i) (c • v)) = c • dRep σ (X i) (dRep σ (X i) v) := fun i =>
    Dw_smul hσ (l := [X i, X i]) (by simp [hX i]) c hv
  simp only [onePlusCas, h, smul_sub, Finset.smul_sum]

theorem iterate_onePlusCas_of_eq (hσ : IsURepOn (UJset ε) σ) {d : ℕ} {X : Fin d → Mx n}
    (hX : ∀ i, X i ∈ lieSet ε) {v : H} (hv : Sm ε σ v) {μ : ℂ} (h : onePlusCas σ X v = μ • v) (r : ℕ) :
    (onePlusCas σ X)^[r] v = μ ^ r • v := by
  induction r with
  | zero => simp
  | succ r ih => rw [Function.iterate_succ_apply', ih, onePlusCas_smul hσ hX _ hv, h, smul_smul, pow_succ]

end GlobalTheory.TypeSum

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open MeasureTheory Filter Topology

namespace GlobalTheory.AvgCont

theorem isClosed_UJset {n : ℕ} (ε : Fin n → Bool) : IsClosed (UJset ε) := by
  show IsClosed {g : Matrix (Fin n) (Fin n) ℂ | gᴴ * Formalism.REAL.Jm ε * g = Formalism.REAL.Jm ε}
  refine isClosed_eq ?_ continuous_const
  exact ((continuous_id.matrix_conjTranspose).matrix_mul continuous_const).matrix_mul continuous_id

theorem mul_mem_UJset_of_inUJ {n : ℕ} {ε : Fin n → Bool} {y m : Matrix (Fin n) (Fin n) ℂ}
    (hy : y ∈ UJset ε) (hm : Formalism.REAL.inUJ ε m) : y * m ∈ UJset ε := by
  have hy' : yᴴ * Formalism.REAL.Jm ε * y = Formalism.REAL.Jm ε := hy
  have hm' : mᴴ * Formalism.REAL.Jm ε * m = Formalism.REAL.Jm ε := hm
  show (y * m)ᴴ * Formalism.REAL.Jm ε * (y * m) = Formalism.REAL.Jm ε
  rw [Matrix.conjTranspose_mul]
  calc mᴴ * yᴴ * Formalism.REAL.Jm ε * (y * m) = mᴴ * (yᴴ * Formalism.REAL.Jm ε * y) * m := by
        simp only [Matrix.mul_assoc]
    _ = Formalism.REAL.Jm ε := by rw [hy', hm']

theorem continuous_maximalCompactSubgroup_toMatrix {n : ℕ} (ε : Fin n → Bool) :
    Continuous (fun k : Formalism.REAL.KG ε => Formalism.REAL.toMK k) :=
  Units.continuous_val.comp (continuous_subtype_val.comp continuous_subtype_val)

theorem continuousOn_avg_right_translates : ∀ (n : ℕ) (ε : Fin n → Bool) (f : GlobalTheory.TypeSum.Mx n → ℂ),
    ContinuousOn f (UJset ε) →
    ∀ e : ↥(Formalism.REAL.KG ε) → ℂ, Continuous e →
    ContinuousOn (fun y => ∫ k, e k * f (y * Formalism.REAL.toMK k) ∂(Formalism.REAL.muK ε)) (UJset ε) := by
  intro n ε f hf e he
  rw [continuousOn_iff_continuous_restrict]
  haveI : LocallyCompactSpace (Matrix (Fin n) (Fin n) ℂ) :=
    inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → ℂ))
  haveI : FirstCountableTopology (Matrix (Fin n) (Fin n) ℂ) :=
    inferInstanceAs (FirstCountableTopology (Fin n → Fin n → ℂ))
  haveI : LocallyCompactSpace (UJset ε) :=
    (isClosed_UJset ε).isClosedEmbedding_subtypeVal.locallyCompactSpace
  let F : UJset ε → Formalism.REAL.KG ε → ℂ := fun y k => e k * f ((y : Matrix (Fin n) (Fin n) ℂ) * Formalism.REAL.toMK k)
  have hF : Continuous (Function.uncurry F) := by
    refine (he.comp continuous_snd).mul ?_
    have hmaps : ∀ p : UJset ε × Formalism.REAL.KG ε,
        (p.1 : Matrix (Fin n) (Fin n) ℂ) * Formalism.REAL.toMK p.2 ∈ UJset ε :=
      fun p => mul_mem_UJset_of_inUJ p.1.2 ((p.2 : Formalism.REAL.UJ ε).2)
    exact hf.comp_continuous
      ((continuous_subtype_val.comp continuous_fst).matrix_mul
        ((continuous_maximalCompactSubgroup_toMatrix ε).comp continuous_snd)) hmaps
  have h := continuous_parametric_integral_of_continuous (μ := Formalism.REAL.muK ε) hF isCompact_univ
  simp only [Measure.restrict_univ] at h
  exact h

end GlobalTheory.AvgCont
end
