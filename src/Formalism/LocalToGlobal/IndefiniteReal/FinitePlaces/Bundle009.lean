module

public import Formalism.LocalToGlobal.HeckeThetaElements.IsHeckeElt
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.FinPartPhiE
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.Bundle003
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.Bundle010
public import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasWeil
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle008
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle015
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
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle007

@[expose] public section

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta IsDedekindDomain NumberField Polynomial
open scoped TensorProduct



namespace Formalism.IndefR.Fin

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem idemAt_eq_split {P : HeightOneSpectrum (𝓞 D.host.E)} (hP : ¬ Lev.IsConjPl (D := D) P P) {e e' : AE D}
    (he : Formalism.L2.NTheta.IsIdemAt e P) (he' : Formalism.L2.NTheta.IsIdemAt e' P) : e = e' := by
  obtain ⟨e₀, ι, he₀, -, hs₀, hz, hκ⟩ := idem_data P hP (belowPl P) rfl
  have key : ∀ f : AE D, Formalism.L2.NTheta.IsIdemAt f P → f = e₀ := by
    intro f hf
    rcases idem_class P hP e₀ ι hs₀ hz hκ he₀.1.1 he₀.1.2.1 f hf.1.1 hf.1.2.1 (below_of_idemAt hf) with h | h
    · exact h
    exfalso
    exact hP (conj_of_cA he₀ hf h)
  rw [key e he, key e' he']

theorem idem_orth {P Q : HeightOneSpectrum (𝓞 D.host.E)} (hP : ¬ Lev.IsConjPl (D := D) P P) {e e' : AE D}
    (he : Formalism.L2.NTheta.IsIdemAt e P) (he' : Formalism.L2.NTheta.IsIdemAt e' Q) (hPQ : P ≠ Q) : e * e' = 0 := by
  have hs := below_of_idemAt he
  have hs' := below_of_idemAt he'
  have heps : e * phiE (belowPl P) 1 = e := by rw [← hs, mul_add, he.1.1, he.1.2.1, add_zero]
  have heps' : e' * phiE (belowPl Q) 1 = e' := by rw [← hs', mul_add, he'.1.1, he'.1.2.1, add_zero]
  by_cases hv : belowPl P = belowPl Q
  · obtain ⟨e₀, ι, he₀, -, hs₀, hz, hκ⟩ := idem_data P hP (belowPl P) rfl
    have h0 : e = e₀ := idemAt_eq_split hP he he₀
    rw [← hv] at hs'
    rcases idem_class P hP e₀ ι hs₀ hz hκ he₀.1.1 he₀.1.2.1 e' he'.1.1 he'.1.2.1 hs' with h | h
    · exfalso
      apply hPQ
      apply HeightOneSpectrum.ext
      ext x
      by_cases hx0 : x = 0
      · subst hx0; simp only [zero_mem]
      rw [he.2 x hx0, he'.2 x hx0, h0, h]
    · rw [h, h0]; exact he₀.1.2.1
  · rw [← heps, ← heps']
    calc e * phiE (belowPl P) 1 * (e' * phiE (belowPl Q) 1) = e * e' * (phiE (belowPl P) 1 * phiE (belowPl Q) 1) := by ring
      _ = 0 := by rw [phiE_orth hv, mul_zero]

theorem idem_orth_conj {P Q : HeightOneSpectrum (𝓞 D.host.E)} (hP : ¬ Lev.IsConjPl (D := D) P P) {e e' : AE D}
    (he : Formalism.L2.NTheta.IsIdemAt e P) (he' : Formalism.L2.NTheta.IsIdemAt e' Q) (hPQ : ¬ Lev.IsConjPl (D := D) P Q) :
    e * cA D e' = 0 := by
  have hs := below_of_idemAt he
  have hs' := below_of_idemAt he'
  have heps : e * phiE (belowPl P) 1 = e := by rw [← hs, mul_add, he.1.1, he.1.2.1, add_zero]
  have heps' : cA D e' * phiE (belowPl Q) 1 = cA D e' := by
    rw [← hs', mul_add, mul_comm (cA D e') e', he'.1.2.1, zero_add, ← map_mul, he'.1.1]
  by_cases hv : belowPl P = belowPl Q
  · obtain ⟨e₀, ι, he₀, -, hs₀, hz, hκ⟩ := idem_data P hP (belowPl P) rfl
    have h0 : e = e₀ := idemAt_eq_split hP he he₀
    rw [← hv] at hs'
    rcases idem_class P hP e₀ ι hs₀ hz hκ he₀.1.1 he₀.1.2.1 e' he'.1.1 he'.1.2.1 hs' with h | h
    · rw [h, h0]; exact he₀.1.2.1
    · exfalso
      exact hPQ (conj_of_cA he he' (h.trans (congrArg (cA D) h0.symm)))
  · rw [← heps, ← heps']
    calc e * phiE (belowPl P) 1 * (cA D e' * phiE (belowPl Q) 1) =
        e * cA D e' * (phiE (belowPl P) 1 * phiE (belowPl Q) 1) := by ring
      _ = 0 := by rw [phiE_orth hv, mul_zero]

theorem not_two_primes {I : Ideal (𝓞 D.host.E)} (hI : I ≠ ⊤) {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q)
    (hpI : (p : 𝓞 D.host.E) ∈ I) (hqI : (q : 𝓞 D.host.E) ∈ I) : False := by
  have hc : IsCoprime (p : ℤ) (q : ℤ) := Nat.isCoprime_iff_coprime.2 ((Nat.coprime_primes hp hq).2 hne)
  obtain ⟨a, b, hab⟩ := hc.map (Int.castRingHom (𝓞 D.host.E))
  apply hI
  rw [Ideal.eq_top_iff_one, ← hab]
  simp only [eq_intCast, Int.cast_natCast]
  exact add_mem (I.mul_mem_left _ hpI) (I.mul_mem_left _ hqI)

theorem nat_mem_of_conj {P Q : HeightOneSpectrum (𝓞 D.host.E)} (h : Lev.IsConjPl (D := D) P Q) {n : ℕ}
    (hn : (n : 𝓞 D.host.E) ∈ P.asIdeal) : (n : 𝓞 D.host.E) ∈ Q.asIdeal := by
  obtain ⟨c, hc, hce⟩ := h _ hn
  have : c = (n : 𝓞 D.host.E) := by
    apply FaithfulSMul.algebraMap_injective (𝓞 D.host.E) D.host.E
    show (c : D.host.E) = ((n : 𝓞 D.host.E) : D.host.E)
    rw [hce]; push_cast; exact star_natCast n
  rwa [← this]

theorem char_mem {P : HeightOneSpectrum (𝓞 D.host.E)} {q : ℕ} (hq : q.Prime)
    (hc : Nat.card (Formalism.L2.DIV.kP P) = q) : (q : 𝓞 D.host.E) ∈ P.asIdeal := by
  have hfin : Finite (Formalism.L2.DIV.kP P) := Nat.finite_of_card_ne_zero (by rw [hc]; exact hq.ne_zero)
  have h0 : (Nat.card (Formalism.L2.DIV.kP P)) • (1 : Formalism.L2.DIV.kP P) = 0 := card_nsmul_eq_zero'
  rw [hc, nsmul_one] at h0
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  simpa using h0

end Formalism.IndefR.Fin

end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
  IsDedekindDomain NumberField Matrix
open scoped TensorProduct ComplexConjugate

namespace Formalism.IndefR.Fin

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

section Psi

variable {ψ : AddChar (AF D.host.F) ℂ}

theorem psi_norm (hψ : IsStdChar D ψ (-1)) (a : AF D.host.F) : ‖ψ a‖ = 1 := hψ.1.2.1 a

theorem psi_ne (hψ : IsStdChar D ψ (-1)) (a : AF D.host.F) : ψ a ≠ 0 := by
  intro h
  have h1 := psi_norm hψ a
  rw [h, norm_zero] at h1
  exact zero_ne_one h1

theorem psi_cont (hψ : IsStdChar D ψ (-1)) : Continuous ψ := hψ.1.1

end Psi

section Cont

variable (S T : HSp D)

theorem cont_trace : Continuous (Algebra.trace (AF D.host.F) (AE D)) :=
  IsModuleTopology.continuous_of_linearMap _

def cAlin (D : D7) : AE D →ₗ[AF D.host.F] AE D where
  toFun := cA D
  map_add' := map_add _
  map_smul' := Formalism.IndefR.PHeisTh.cA_smul

theorem cont_cA : Continuous (cA D) :=
  IsModuleTopology.continuous_of_linearMap (cAlin D)

theorem cont_hO : Continuous fun p : MO S T × MO S T => hO S T p.1 p.2 := by
  have hcA : Continuous (cA D) := cont_cA
  delta hO
  fun_prop

theorem cont_symplO : Continuous fun p : MO S T × MO S T => symplO S T p.1 p.2 := by
  have ht : Continuous (Algebra.trace (AF D.host.F) (AE D)) := cont_trace
  have hh := cont_hO S T
  delta symplO
  first
    | exact ht.comp (continuous_const.mul hh)
    | fun_prop

theorem cont_symplO_left (w : MO S T) : Continuous fun z : MO S T => symplO S T z w := by
  have h : Continuous (Function.uncurry (symplO S T)) := cont_symplO S T
  exact h.uncurry_right w

theorem cont_symplOH_left (w : MO S T) : Continuous fun z : MO S T => symplOH S T z w := by
  delta symplOH
  exact continuous_const.mul (cont_symplO_left S T w)

end Cont

section Per

variable (S T : HSp D)

end Per

section Theta

variable {ψ : AddChar (AF D.host.F) ℂ} (S T : HSp D)

theorem cont_heis (hψ : IsStdChar D ψ (-1)) {f : MO S T → ℂ} (hf : IsThetaFunO ψ S T f) (v : MO S T) :
    Continuous (heisO ψ S T v f) := by
  delta heisO
  exact ((psi_cont hψ).comp (cont_symplOH_left S T v)).mul (hf.3.comp (continuous_add_const v))

theorem theta_zero : IsThetaFunO ψ S T 0 := by
  exact ⟨fun γ w => by simp, ⟨⊤, by rw [AddSubgroup.coe_top]; exact isOpen_univ, fun u _ _ => by funext z; simp [heisO]⟩, continuous_zero,
    fun k L _ _ _ => contDiff_const⟩

theorem theta_add {f g : MO S T → ℂ} (hf : IsThetaFunO ψ S T f) (hg : IsThetaFunO ψ S T g) :
    IsThetaFunO ψ S T (f + g) := by
  obtain ⟨hq1, ⟨U1, hU1, hl1⟩, hc1, hs1⟩ := hf
  obtain ⟨hq2, ⟨U2, hU2, hl2⟩, hc2, hs2⟩ := hg
  refine ⟨fun γ w => ?_, ⟨U1 ⊓ U2, ?_, fun u hu h0 => ?_⟩, hc1.add hc2,
    fun k L hL h0 w => (hs1 k L hL h0 w).add (hs2 k L hL h0 w)⟩
  · simp only [Pi.add_apply, hq1 γ w, hq2 γ w, mul_add]
  · rw [AddSubgroup.coe_inf]
    exact hU1.inter hU2
  · have e1 := hl1 u hu.1 h0
    have e2 := hl2 u hu.2 h0
    funext z
    have z1 := congrFun e1 z
    have z2 := congrFun e2 z
    simp only [heisO, Pi.add_apply, Pi.zero_apply] at z1 z2 ⊢
    rw [mul_add, z1, z2]

theorem theta_smul (c : ℂ) {f : MO S T → ℂ} (hf : IsThetaFunO ψ S T f) : IsThetaFunO ψ S T (c • f) := by
  obtain ⟨hq1, ⟨U1, hU1, hl1⟩, hc1, hs1⟩ := hf
  refine ⟨fun γ w => ?_, ⟨U1, hU1, fun u hu h0 => ?_⟩, hc1.const_smul c,
    fun k L hL h0 w => (hs1 k L hL h0 w).const_smul c⟩
  · simp only [Pi.smul_apply, smul_eq_mul, hq1 γ w]
    ring
  · have e1 := hl1 u hu h0
    funext z
    have z1 := congrFun e1 z
    simp only [heisO, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at z1 ⊢
    rw [mul_left_comm, z1]

end Theta

section Svn

variable {ψ : AddChar (AF D.host.F) ℂ} (S T : HSp D)

end Svn

end Formalism.IndefR.Fin

end
end

section



noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Matrix
open scoped TensorProduct

namespace Formalism.IndefR.Fin

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (S T : HSp D)

theorem suppAt_inv_fp {e : AE D} {V : HSp D} {g : GA D V} (hg : SuppAt e V g) : SuppAt e V g⁻¹ := by
  have hinv : HMul.hMul (mt V g⁻¹) (mt V g) = (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) := by
    rw [← Formalism.IndefR.Eqv.mt_mul, inv_mul_cancel, Formalism.IndefR.Eqv.mt_one]
  have hd : (mt V g⁻¹ : Matrix (Fin V.rank) (Fin V.rank) (AE D)) - 1 =
      -(HMul.hMul (mt V g⁻¹) ((mt V g : Matrix (Fin V.rank) (Fin V.rank) (AE D)) - 1)) := by
    rw [Matrix.mul_sub, hinv, Matrix.mul_one, neg_sub]
  intro i j
  rw [hd, Matrix.neg_apply, mul_neg, Matrix.mul_apply, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mul_left_comm, hg k j]

theorem actO_nsmul (g : GA D S) (h : GA D T) (k : ℕ) (t : WO S T) : actO S T g h (k • t) = k • actO S T g h t := by
  induction k with
  | zero =>
    rw [zero_smul, zero_smul]
    unfold actO
    rw [Matrix.mul_zero, Matrix.zero_mul]
  | succ n ih => rw [succ_nsmul, succ_nsmul, Formalism.IndefR.Eqv.actO_add, ih]

theorem isHalf_actO_fp {e : AE D} (g : GA D S) (h : GA D T) {t : WO S T} (ht : IsHalf e t) :
    IsHalf e (actO S T g h t) := by
  intro i j
  unfold actO
  simp only [Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  conv_rhs => rw [← ht l k]
  ring

theorem isHalf_nsmul_fp {e : AE D} {v : WO S T} (hv : IsHalf e v) (m : ℕ) : IsHalf e (m • v) := fun i j => by
  rw [Matrix.smul_apply, nsmul_eq_mul, mul_left_comm, hv i j]

theorem isHalf_actO_iff {e : AE D} (g : GA D S) (h : GA D T) (t : WO S T) :
    IsHalf e (actO S T g h t) ↔ IsHalf e t := by
  refine ⟨fun h' => ?_, isHalf_actO_fp S T g h⟩
  have := isHalf_actO_fp S T g⁻¹ h⁻¹ h'
  rwa [Formalism.IndefR.Eqv.actO_actO_inv] at this

open Classical in
theorem halfInd_add {e : AE D} {Λ : AddSubgroup (WO S T)} {u : WO S T} (hu : u ∈ Λ) (hue : IsHalf e u)
    (s : WO S T) : halfInd e Λ (s + u) = halfInd e Λ s := by
  unfold halfInd
  have h1 : s + u ∈ Λ ↔ s ∈ Λ := ⟨fun h => by simpa using Λ.sub_mem h hu, fun h => Λ.add_mem h hu⟩
  have h2 : IsHalf e (s + u) ↔ IsHalf e s := by
    constructor
    · intro h i j
      have := h i j
      rw [Matrix.add_apply, mul_add, hue i j] at this
      exact add_right_cancel this
    · intro h i j
      rw [Matrix.add_apply, mul_add, h i j, hue i j]
  simp only [h1, h2]

theorem sb_comp {e : AE D} {Λ : AddSubgroup (WO S T)} (g : GA D S) (h : GA D T)
    {k₁ : ℕ} (hk₁ : 0 < k₁) (h₁ : ∀ t ∈ Λ, k₁ • actO S T g h t ∈ Λ)
    {k₂ : ℕ} (hk₂ : 0 < k₂) (h₂ : ∀ t ∈ Λ, k₂ • actO S T g⁻¹ h⁻¹ t ∈ Λ)
    {Φ : WO S T → ℂ} (hΦ : IsSBHalf e Λ Φ) : IsSBHalf e Λ (fun t => Φ (actO S T g h t)) := by
  obtain ⟨hs, k, hk, hi, hl⟩ := hΦ
  refine ⟨fun t ht => (isHalf_actO_iff S T g h t).1 (hs _ ht), k * k₁ * k₂, by positivity,
    fun u hu hue t => ?_, fun t ht => ?_⟩
  · show Φ (actO S T g h (t + (k * k₁ * k₂) • u)) = Φ (actO S T g h t)
    rw [Formalism.IndefR.Eqv.actO_add, actO_nsmul, show (k * k₁ * k₂) • actO S T g h u =
      k • (k₂ • (k₁ • actO S T g h u)) by rw [smul_smul, smul_smul]; ring_nf]
    exact hi _ (Λ.nsmul_mem (h₁ u hu) k₂)
      (isHalf_nsmul_fp S T (isHalf_nsmul_fp S T (isHalf_actO_fp S T g h hue) k₁) k₂) _
  · have h1 := hl _ ht
    have h2 := h₂ _ h1
    rw [actO_nsmul, Formalism.IndefR.Eqv.actO_actO_inv, smul_smul] at h2
    rw [show k * k₁ * k₂ = k₁ * (k₂ * k) by ring, ← smul_smul]
    exact Λ.nsmul_mem h2 k₁

end Formalism.IndefR.Fin

end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Matrix
open scoped TensorProduct

namespace Formalism.IndefR.Fin

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D)

def heisL (w : WO S T) : Module.End ℂ (WO S T → ℂ) where
  toFun := heisO ψ S T w
  map_add' f g := by
    funext x
    simp only [heisO, Pi.add_apply, mul_add]
  map_smul' c f := by
    funext x
    simp only [heisO, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

theorem heisL_apply (w : WO S T) (f : WO S T → ℂ) : heisL ψ S T w f = heisO ψ S T w f := rfl

def halfSub (e : AE D) : AddSubgroup (WO S T) where
  carrier := {u | IsHalf e u}
  add_mem' {a b} ha hb := fun i j => by rw [Matrix.add_apply, mul_add, ha i j, hb i j]
  zero_mem' := fun i j => by rw [Matrix.zero_apply, mul_zero]
  neg_mem' {a} ha := fun i j => by rw [Matrix.neg_apply, mul_neg, ha i j]

theorem heisO_heisO (w w' : WO S T) (f : WO S T → ℂ) :
    heisO ψ S T w (heisO ψ S T w' f) = ψ (symplOH S T w w') • heisO ψ S T (w + w') f := by
  funext x
  simp only [heisO, Pi.smul_apply, smul_eq_mul]
  rw [symplOH_add_left S T x w w', symplOH_add_right S T x w w', AddChar.map_add_eq_mul,
    AddChar.map_add_eq_mul, add_assoc x w w']
  ring

theorem psi_ne_zero (a : AF D.host.F) : ψ a ≠ 0 := by
  intro h
  have := ψ.map_add_eq_mul a (-a)
  rw [add_neg_cancel, AddChar.map_zero_eq_one, h, zero_mul] at this
  exact one_ne_zero this

theorem symplO_half {e : AE D} (he : e * cA D e = 0) {x y : WO S T} (hx : IsHalf e x) (hy : IsHalf e y) :
    symplO S T x y = 0 := by
  have hz : ∀ a b c d, incA D (S.gram⁻¹ a b) * cA D (y c b) * incA D (T.gram c d) * x d a = 0 := by
    intro a b c d
    rw [← hy c b, ← hx d a, map_mul]
    linear_combination (incA D (S.gram⁻¹ a b) * cA D (y c b) * incA D (T.gram c d) * x d a) * he
  simp [symplO, hO, hz]

theorem symplOH_half {e : AE D} (he : e * cA D e = 0) {x y : WO S T} (hx : IsHalf e x) (hy : IsHalf e y) :
    symplOH S T x y = 0 := by
  rw [symplOH, symplO_half S T he hx hy, mul_zero]

theorem heisL_add_half {e : AE D} (he : e * cA D e = 0) {x y : WO S T} (hx : IsHalf e x) (hy : IsHalf e y) :
    heisL ψ S T (x + y) = heisL ψ S T x * heisL ψ S T y := by
  ext1 f
  rw [Module.End.mul_apply, heisL_apply, heisL_apply, heisL_apply, heisO_heisO, symplOH_half S T he hx hy,
    AddChar.map_zero_eq_one, one_smul]

theorem heisL_comm (x y : WO S T) :
    heisL ψ S T x * heisL ψ S T y = ψ (symplO S T x y) • (heisL ψ S T y * heisL ψ S T x) := by
  ext1 f
  simp only [Module.End.mul_apply, LinearMap.smul_apply, heisL_apply]
  rw [heisO_heisO, heisO_heisO, smul_smul, add_comm y x, symplOH_swap S T x y, ← symplOH_two S T x y,
    ← AddChar.map_add_eq_mul, show symplOH S T x y + symplOH S T x y + -symplOH S T x y = symplOH S T x y by abel]

theorem cA_half_orth {e : AE D} (he : e * cA D e = 0) : cA D e * cA D (cA D e) = 0 := by
  rw [cA_cA, mul_comm, he]

end Formalism.IndefR.Fin

end
end
