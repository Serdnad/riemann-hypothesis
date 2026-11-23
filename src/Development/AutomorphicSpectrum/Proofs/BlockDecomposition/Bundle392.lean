module

public import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
public import Mathlib.Basic.Complex.Basic
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsUnitarisableOfCharIff
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower
public import Formalism.SatakeDualWeyl.Bundle001
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SmoothVecUnitaryModule
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle294
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsNormEmbId
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle286
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle317
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle386
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ClosedEvaluationEquivariant
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
public import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable
import Development.AutomorphicArithmetic.IntegralCasts.Bundle001

@[expose] public section

section

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BCT ValuativeRel
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.CompanionTheory.SmInd

def bump {G W : Type} [Group G] [AddCommGroup W] [Module ℂ W] (P : Subgroup G)
    (σ : Representation ℂ P W) (K : Subgroup G) (x : W) (g : G) : W :=
  if h : ∃ p : P, (p : G)⁻¹ * g ∈ K then σ h.choose x else 0

variable {G W : Type} [Group G] [AddCommGroup W] [Module ℂ W] {P : Subgroup G}
  {σ : Representation ℂ P W} {K : Subgroup G} {x : W}

theorem bump_eq (hx : ∀ p : P, (p : G) ∈ K → σ p x = x) {p : P} {g : G}
    (hp : (p : G)⁻¹ * g ∈ K) : bump P σ K x g = σ p x := by
  have h : ∃ p : P, (p : G)⁻¹ * g ∈ K := ⟨p, hp⟩
  have hq := h.choose_spec
  rw [bump, dite_eq_left h]
  set q := h.choose
  have hm : ((q⁻¹ * p : P) : G) ∈ K := by
    have := K.mul_mem hq (K.inv_mem hp)
    have e : (q : G)⁻¹ * g * ((p : G)⁻¹ * g)⁻¹ = ((q⁻¹ * p : P) : G) := by
      simp [mul_assoc]
    rwa [e] at this
  have h2 := hx _ hm
  have h3 : σ p x = σ q (σ (q⁻¹ * p) x) := by
    rw [← Module.End.mul_apply, ← map_mul]; simp
  rw [h3, h2]

theorem bump_of_not {g : G} (h : ¬ ∃ p : P, (p : G)⁻¹ * g ∈ K) : bump P σ K x g = 0 := by
  rw [bump, dite_eq_right h]

theorem bump_mul_left (hx : ∀ p : P, (p : G) ∈ K → σ p x = x) (p : P) (g : G) :
    bump P σ K x ((p : G) * g) = σ p (bump P σ K x g) := by
  by_cases h : ∃ q : P, (q : G)⁻¹ * g ∈ K
  · obtain ⟨q, hq⟩ := h
    have hq' : (((p * q : P) : G))⁻¹ * ((p : G) * g) ∈ K := by
      have e : (((p * q : P) : G))⁻¹ * ((p : G) * g) = (q : G)⁻¹ * g := by
        simp [mul_assoc]
      rwa [e]
    rw [bump_eq hx hq', bump_eq hx hq, map_mul, Module.End.mul_apply]
  · have h' : ¬ ∃ r : P, (r : G)⁻¹ * ((p : G) * g) ∈ K := by
      rintro ⟨r, hr⟩
      refine h ⟨p⁻¹ * r, ?_⟩
      have e : (((p⁻¹ * r : P) : G))⁻¹ * g = (r : G)⁻¹ * ((p : G) * g) := by
        simp [mul_assoc]
      rwa [e]
    rw [bump_of_not h, bump_of_not h', map_zero]

theorem bump_mul_right (hx : ∀ p : P, (p : G) ∈ K → σ p x = x) (g : G) {k : G} (hk : k ∈ K) :
    bump P σ K x (g * k) = bump P σ K x g := by
  by_cases h : ∃ q : P, (q : G)⁻¹ * g ∈ K
  · obtain ⟨q, hq⟩ := h
    have hq' : (q : G)⁻¹ * (g * k) ∈ K := by
      rw [← mul_assoc]; exact K.mul_mem hq hk
    rw [bump_eq hx hq', bump_eq hx hq]
  · have h' : ¬ ∃ r : P, (r : G)⁻¹ * (g * k) ∈ K := by
      rintro ⟨r, hr⟩
      refine h ⟨r, ?_⟩
      have := K.mul_mem hr (K.inv_mem hk)
      have e : (r : G)⁻¹ * (g * k) * k⁻¹ = (r : G)⁻¹ * g := by simp [mul_assoc]
      rwa [e] at this
    rw [bump_of_not h, bump_of_not h']

theorem bump_one (hx : ∀ p : P, (p : G) ∈ K → σ p x = x) : bump P σ K x 1 = x := by
  have h : ((1 : P) : G)⁻¹ * 1 ∈ K := by simp [K.one_mem]
  rw [bump_eq hx h]; simp

def bumpInd (hx : ∀ p : P, (p : G) ∈ K → σ p x = x) : indSpace P σ :=
  ⟨bump P σ K x, fun p g => bump_mul_left hx p g⟩

theorem ind_bumpInd (hx : ∀ p : P, (p : G) ∈ K → σ p x = x) {k : G} (hk : k ∈ K) :
    ind P σ k (bumpInd hx) = bumpInd hx := by
  apply Subtype.ext
  funext g
  exact bump_mul_right hx g hk

theorem fixed_smInd_ne_bot [TopologicalSpace G] [IsTopologicalGroup G] (hK : IsOpen (K : Set G))
    (hx0 : x ≠ 0) (hx : ∀ p : P, (p : G) ∈ K → σ p x = x) : fixed (smInd P σ) K ≠ ⊥ := by
  have hs : bumpInd hx ∈ smoothPart (ind P σ) :=
    mem_smoothPart_of_nhds (Filter.mem_of_superset (hK.mem_nhds K.one_mem)
      fun k hk => ind_bumpInd hx hk)
  refine (Submodule.ne_bot_iff _).2 ⟨⟨bumpInd hx, hs⟩, ?_, ?_⟩
  · intro k
    simp only [MonoidHom.one_apply, Units.val_one, one_smul]
    exact Subtype.ext (ind_bumpInd hx k.2)
  · intro h
    apply hx0
    have h1 := congrFun (congrArg (fun φ : smoothPart (ind P σ) => (φ.1 : G → W)) h) 1
    rw [← bump_one hx]
    exact h1

theorem fixed_smInd_ne_bot_of_fixed : ∀ (G W : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup W] [Module ℂ W] (P : Subgroup G) (σ : Representation ℂ P W) (K : Subgroup G), IsOpen (K : Set G) → ∀ x : W, x ≠ 0 → (∀ p : P, (p : G) ∈ K → σ p x = x) → fixed (smInd P σ) K ≠ ⊥ :=
  fun _ _ _ _ _ _ _ _ _ _ hK _ hx0 hx => fixed_smInd_ne_bot hK hx0 hx

end GlobalTheory.CompanionTheory.SmInd
end
end

section

open NumberField IsDedekindDomain Matrix Polynomial GlobalTheory.BCT GlobalTheory.UnitaryBC Formalism.UG
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompanionTheory.DiagRigid

theorem diag_rigid : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (n : ℕ) (y : Fin n → ℤ), Function.Injective y → ∀ (d d' : Fin n → Lˣ), (∀ i, ordL (d i : L) = y i) → (∀ i, ordL (d' i : L) = y i) → ∀ h : GL (Fin n) L, h⁻¹ * GlobalTheory.SmGL.diagT L (Fin n) d * h = GlobalTheory.SmGL.diagT L (Fin n) d' → d = d' ∧ ∃ s : Fin n → Lˣ, h = GlobalTheory.SmGL.diagT L (Fin n) s := by
  intro L _ _ n y hy d d' hd hd' h hh
  have key : GlobalTheory.SmGL.diagT L (Fin n) d * h = h * GlobalTheory.SmGL.diagT L (Fin n) d' := by
    rw [← hh]; simp only [mul_assoc, mul_inv_cancel_left]
  have key' : (Matrix.diagonal fun i => (d i : L)) * (h : Matrix (Fin n) (Fin n) L)
      = (h : Matrix (Fin n) (Fin n) L) * Matrix.diagonal fun i => (d' i : L) := by
    have := congrArg (fun g : GL (Fin n) L => (g : Matrix (Fin n) (Fin n) L)) key
    simpa only [Units.val_mul, GlobalTheory.SmGL.val_diagT] using this
  have ent : ∀ i j, (d i : L) * (h : Matrix (Fin n) (Fin n) L) i j
      = (h : Matrix (Fin n) (Fin n) L) i j * (d' j : L) := by
    intro i j
    have := congrFun (congrFun key' i) j
    rwa [Matrix.diagonal_mul, Matrix.mul_diagonal] at this
  have off : ∀ i j, i ≠ j → (h : Matrix (Fin n) (Fin n) L) i j = 0 := by
    intro i j hij
    by_contra hne
    have e : (d i : L) = (d' j : L) := by
      have := ent i j
      rw [mul_comm] at this
      exact mul_left_cancel₀ hne this
    apply hij
    apply hy
    rw [← hd i, ← hd' j, e]
  have hdiag : (h : Matrix (Fin n) (Fin n) L)
      = Matrix.diagonal fun i => (h : Matrix (Fin n) (Fin n) L) i i := by
    ext i j
    by_cases hij : i = j
    · subst hij; simp
    · rw [Matrix.diagonal_apply_ne _ hij]; exact off i j hij
  have hdet : ∏ i, (h : Matrix (Fin n) (Fin n) L) i i ≠ 0 := by
    have h1 : IsUnit (h : Matrix (Fin n) (Fin n) L).det :=
      (Matrix.isUnit_iff_isUnit_det _).1 h.isUnit
    rw [hdiag, Matrix.det_diagonal] at h1
    simpa [Matrix.diagonal_apply_eq] using h1.ne_zero
  have hii : ∀ i, (h : Matrix (Fin n) (Fin n) L) i i ≠ 0 := fun i =>
    (Finset.prod_ne_zero_iff.1 hdet) i (Finset.mem_univ i)
  refine ⟨?_, fun i => Units.mk0 _ (hii i), ?_⟩
  · funext i
    apply Units.ext
    have := ent i i
    rw [mul_comm] at this
    exact mul_left_cancel₀ (hii i) this
  · apply Units.ext
    rw [GlobalTheory.SmGL.val_diagT]
    simpa using hdiag

end GlobalTheory.CompanionTheory.DiagRigid
end

section

open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.CompanionTheory.CoefWord

theorem eword_coef : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (hσ : Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset ε) σ) (v : GlobalTheory.SmoothVecMod.smoothVec ε σ) (w : H) (l : List (Fin n × Fin n)), ∀ g ∈ Formalism.MainNotions.S.UJset ε, Formalism.REAL.Eword ε l (fun x => ⟪w, σ x (v : H)⟫_ℂ) g = ⟪w, σ g (((l.map fun ab => GlobalTheory.SmoothVecMod.unitAct hσ ab.1 ab.2).prod v : GlobalTheory.SmoothVecMod.smoothVec ε σ) : H)⟫_ℂ := by
  intro n ε H _ _ σ hσ v w l
  induction l with
  | nil =>
    intro g _
    rfl
  | cons p l ih =>
    intro g hg
    have hg' : Formalism.REAL.inUJ ε g := hg
    set u : GlobalTheory.SmoothVecMod.smoothVec ε σ :=
      (l.map fun ab => GlobalTheory.SmoothVecMod.unitAct hσ ab.1 ab.2).prod v with hu
    have h1 : Formalism.REAL.Eword ε (p :: l) (fun x => ⟪w, σ x (v : H)⟫_ℂ) g =
        Formalism.REAL.EabV ε p.1 p.2 (Formalism.REAL.Eword ε l (fun x => ⟪w, σ x (v : H)⟫_ℂ)) g := rfl
    have h2 : Formalism.REAL.EabV ε p.1 p.2 (Formalism.REAL.Eword ε l (fun x => ⟪w, σ x (v : H)⟫_ℂ)) g =
        Formalism.REAL.EabV ε p.1 p.2 (fun x => innerSL ℂ w (σ x (u : H))) g :=
      GlobalTheory.SmoothVecMod.eabV_congr (fun x hx => ih x hx) p.1 p.2 hg'
    have h3 := GlobalTheory.CapelliCoef.eabV_pair (innerSL ℂ w) (f := fun x => σ x (u : H)) u.2 p.1 p.2 hg'
    have h4 := GlobalTheory.SmoothVecMod.rep_eabV hσ u.2 p.1 p.2 hg'
    rw [h1, h2, ← h3, ← h4]
    simp only [List.map_cons, List.prod_cons, Module.End.mul_apply]
    rfl

end GlobalTheory.CompanionTheory.CoefWord
end
end

section

open MeasureTheory GlobalTheory.CompanionTheory.UnitaryFramesMetricPeriods
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.CompanionTheory.Godement

section Unitary

variable {Γ : Type} [Group Γ] [TopologicalSpace Γ] {B : Type} [NormedAddCommGroup B] [InnerProductSpace ℂ B]

theorem inner_map {ρ : Γ → (B →L[ℂ] B)} (hU : IsU ρ) (g : Γ) (x y : B) : ⟪ρ g x, ρ g y⟫_ℂ = ⟪x, y⟫_ℂ := by
  obtain ⟨-, -, hnorm, -⟩ := hU
  exact (LinearIsometry.mk (ρ g : B →ₗ[ℂ] B) (hnorm g)).inner_map_map x y

theorem inner_orbit {ρ : Γ → (B →L[ℂ] B)} (hU : IsU ρ) (v : B) (g h : Γ) :
    ⟪ρ g v, ρ h v⟫_ℂ = ⟪v, ρ (g⁻¹ * h) v⟫_ℂ := by
  rw [← GlobalTheory.CompanionTheory.Godement.inner_map hU g v (ρ (g⁻¹ * h) v)]
  obtain ⟨-, hmul, -, -⟩ := hU
  congr 1
  calc ρ h v = ρ (g * (g⁻¹ * h)) v := by rw [mul_inv_cancel_left]
    _ = ρ g (ρ (g⁻¹ * h) v) := by rw [hmul g (g⁻¹ * h), ContinuousLinearMap.mul_apply]

end Unitary

theorem mul_le_half_add (a b : ℝ≥0∞) : a * b ≤ 2⁻¹ * (a ^ 2 + b ^ 2) := by
  have h := ENNReal.young_inequality a b Real.HolderConjugate.two_two
  rw [ENNReal.rpow_two, ENNReal.rpow_two, ENNReal.ofReal_ofNat] at h
  calc a * b ≤ a ^ 2 / 2 + b ^ 2 / 2 := h
    _ = 2⁻¹ * (a ^ 2 + b ^ 2) := by
      rw [div_eq_mul_inv, div_eq_mul_inv, mul_comm (a ^ 2), mul_comm (b ^ 2), mul_add]

theorem norm_sq_integral_smul_le : ∀ {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [LocallyCompactSpace Γ]
    [SecondCountableTopology Γ] [MeasurableSpace Γ] [BorelSpace Γ] (ν : Measure Γ) [ν.IsHaarMeasure] [ν.IsMulRightInvariant]
    {B : Type} [NormedAddCommGroup B] [InnerProductSpace ℂ B] [CompleteSpace B] (ρ : Γ → (B →L[ℂ] B)), IsU ρ → ∀ v : B, Integrable (fun g => ⟪v, ρ g v⟫_ℂ) ν → ∀ f : Γ → ℂ, Measurable f → Integrable f ν →
    Integrable (fun g => ‖f g‖ ^ 2) ν →
    ‖∫ g, f g • ρ g v ∂ν‖ ^ 2 ≤ (∫ g, ‖f g‖ ^ 2 ∂ν) * ∫ g, ‖⟪v, ρ g v⟫_ℂ‖ ∂ν := by
  intro Γ _ _ _ _ _ _ _ ν _ _ B _ _ _ ρ hU v hφ f hf hfi hf2
  obtain ⟨-, -, -, hcont⟩ := id hU
  have hA : 0 ≤ ∫ g, ‖f g‖ ^ 2 ∂ν := integral_nonneg fun g => sq_nonneg _
  have hB : 0 ≤ ∫ g, ‖⟪v, ρ g v⟫_ℂ‖ ∂ν := integral_nonneg fun g => norm_nonneg _
  by_cases hF : Integrable (fun g => f g • ρ g v) ν
  swap
  · rw [integral_undef hF, norm_zero, zero_pow two_ne_zero]
    exact mul_nonneg hA hB
  have hψc : Continuous fun x : Γ => ‖⟪v, ρ x v⟫_ℂ‖ₑ := (continuous_const.inner (hcont v)).enorm
  have hψ : Measurable fun x : Γ => ‖⟪v, ρ x v⟫_ℂ‖ₑ := hψc.measurable
  have hfe : Measurable fun g : Γ => ‖f g‖ₑ ^ 2 := hf.enorm.pow_const 2
  have hswap : ∀ g h : Γ, ‖⟪v, ρ (h⁻¹ * g) v⟫_ℂ‖ₑ = ‖⟪v, ρ (g⁻¹ * h) v⟫_ℂ‖ₑ := by
    intro g h
    rw [← GlobalTheory.CompanionTheory.Godement.inner_orbit hU v h g, ← GlobalTheory.CompanionTheory.Godement.inner_orbit hU v g h,
      ← inner_conj_symm (ρ h v) (ρ g v), RCLike.enorm_conj]
  have hswapm : AEMeasurable (Function.uncurry fun h g : Γ =>
      2⁻¹ * (‖f g‖ₑ ^ 2 * ‖⟪v, ρ (h⁻¹ * g) v⟫_ℂ‖ₑ)) (ν.prod ν) := by
    apply Measurable.aemeasurable
    exact measurable_const.mul ((hfe.comp measurable_snd).mul
      (hψ.comp (measurable_fst.inv.mul measurable_snd)))
  have hm3 : Measurable fun h => 2⁻¹ * ‖f h‖ₑ ^ 2 * ∫⁻ x, ‖⟪v, ρ x v⟫_ℂ‖ₑ ∂ν :=
    (measurable_const.mul hfe).mul_const _
  have hm4 : Measurable fun h => 2⁻¹ * ‖f h‖ₑ ^ 2 := measurable_const.mul hfe
  have hII : ⟪∫ g, f g • ρ g v ∂ν, ∫ g, f g • ρ g v ∂ν⟫_ℂ =
      ∫ h, f h * starRingEnd ℂ (∫ g, f g * ⟪ρ h v, ρ g v⟫_ℂ ∂ν) ∂ν := by
    rw [← integral_inner hF]
    refine integral_congr_ae ?_
    filter_upwards with h
    rw [inner_smul_right, ← inner_conj_symm, ← integral_inner hF]
    simp only [inner_smul_right]
  have key : ‖⟪∫ g, f g • ρ g v ∂ν, ∫ g, f g • ρ g v ∂ν⟫_ℂ‖ₑ ≤
      (∫⁻ g, ‖f g‖ₑ ^ 2 ∂ν) * ∫⁻ x, ‖⟪v, ρ x v⟫_ℂ‖ₑ ∂ν := by
    rw [hII]
    calc ‖∫ h, f h * starRingEnd ℂ (∫ g, f g * ⟪ρ h v, ρ g v⟫_ℂ ∂ν) ∂ν‖ₑ
        ≤ ∫⁻ h, ‖f h * starRingEnd ℂ (∫ g, f g * ⟪ρ h v, ρ g v⟫_ℂ ∂ν)‖ₑ ∂ν :=
          enorm_integral_le_lintegral_enorm _
      _ ≤ ∫⁻ h, ∫⁻ g, 2⁻¹ * (‖f h‖ₑ ^ 2 + ‖f g‖ₑ ^ 2) * ‖⟪v, ρ (h⁻¹ * g) v⟫_ℂ‖ₑ ∂ν ∂ν := by
          refine lintegral_mono fun h => ?_
          beta_reduce
          rw [enorm_mul, RCLike.enorm_conj]
          calc ‖f h‖ₑ * ‖∫ g, f g * ⟪ρ h v, ρ g v⟫_ℂ ∂ν‖ₑ
              ≤ ‖f h‖ₑ * ∫⁻ g, ‖f g * ⟪ρ h v, ρ g v⟫_ℂ‖ₑ ∂ν := by
                gcongr
                exact enorm_integral_le_lintegral_enorm _
            _ ≤ ∫⁻ g, ‖f h‖ₑ * ‖f g * ⟪ρ h v, ρ g v⟫_ℂ‖ₑ ∂ν := lintegral_const_mul_le _ _
            _ ≤ _ := by
                refine lintegral_mono fun g => ?_
                beta_reduce
                rw [enorm_mul, GlobalTheory.CompanionTheory.Godement.inner_orbit hU, ← mul_assoc]
                gcongr ?_ * _
                exact GlobalTheory.CompanionTheory.Godement.mul_le_half_add _ _
      _ = ∫⁻ h, (2⁻¹ * ‖f h‖ₑ ^ 2 * ∫⁻ x, ‖⟪v, ρ x v⟫_ℂ‖ₑ ∂ν +
            ∫⁻ g, 2⁻¹ * (‖f g‖ₑ ^ 2 * ‖⟪v, ρ (h⁻¹ * g) v⟫_ℂ‖ₑ) ∂ν) ∂ν := by
          refine lintegral_congr fun h => ?_
          have hm : Measurable fun g => ‖⟪v, ρ (h⁻¹ * g) v⟫_ℂ‖ₑ := hψ.comp (measurable_const_mul h⁻¹)
          have hm2 : Measurable fun g => 2⁻¹ * ‖f h‖ₑ ^ 2 * ‖⟪v, ρ (h⁻¹ * g) v⟫_ℂ‖ₑ :=
            measurable_const.mul hm
          calc ∫⁻ g, 2⁻¹ * (‖f h‖ₑ ^ 2 + ‖f g‖ₑ ^ 2) * ‖⟪v, ρ (h⁻¹ * g) v⟫_ℂ‖ₑ ∂ν
              = ∫⁻ g, (2⁻¹ * ‖f h‖ₑ ^ 2 * ‖⟪v, ρ (h⁻¹ * g) v⟫_ℂ‖ₑ +
                  2⁻¹ * (‖f g‖ₑ ^ 2 * ‖⟪v, ρ (h⁻¹ * g) v⟫_ℂ‖ₑ)) ∂ν :=
                lintegral_congr fun g => by ring
            _ = ∫⁻ g, 2⁻¹ * ‖f h‖ₑ ^ 2 * ‖⟪v, ρ (h⁻¹ * g) v⟫_ℂ‖ₑ ∂ν +
                  ∫⁻ g, 2⁻¹ * (‖f g‖ₑ ^ 2 * ‖⟪v, ρ (h⁻¹ * g) v⟫_ℂ‖ₑ) ∂ν :=
                lintegral_add_left hm2 _
            _ = _ := by
                rw [lintegral_const_mul _ hm,
                  lintegral_mul_left_eq_self (fun x => ‖⟪v, ρ x v⟫_ℂ‖ₑ) h⁻¹]
      _ = (∫⁻ h, 2⁻¹ * ‖f h‖ₑ ^ 2 * ∫⁻ x, ‖⟪v, ρ x v⟫_ℂ‖ₑ ∂ν ∂ν) +
            ∫⁻ h, ∫⁻ g, 2⁻¹ * (‖f g‖ₑ ^ 2 * ‖⟪v, ρ (h⁻¹ * g) v⟫_ℂ‖ₑ) ∂ν ∂ν :=
          lintegral_add_left hm3 _
      _ = 2⁻¹ * (∫⁻ g, ‖f g‖ₑ ^ 2 ∂ν) * (∫⁻ x, ‖⟪v, ρ x v⟫_ℂ‖ₑ ∂ν) +
            2⁻¹ * (∫⁻ g, ‖f g‖ₑ ^ 2 ∂ν) * (∫⁻ x, ‖⟪v, ρ x v⟫_ℂ‖ₑ ∂ν) := by
          congr 1
          · rw [lintegral_mul_const _ hm4, lintegral_const_mul _ hfe]
          · rw [lintegral_lintegral_swap hswapm]
            calc ∫⁻ g, ∫⁻ h, 2⁻¹ * (‖f g‖ₑ ^ 2 * ‖⟪v, ρ (h⁻¹ * g) v⟫_ℂ‖ₑ) ∂ν ∂ν
                = ∫⁻ g, 2⁻¹ * ‖f g‖ₑ ^ 2 * ∫⁻ x, ‖⟪v, ρ x v⟫_ℂ‖ₑ ∂ν ∂ν := by
                  refine lintegral_congr fun g => ?_
                  have hm : Measurable fun h => ‖⟪v, ρ (g⁻¹ * h) v⟫_ℂ‖ₑ :=
                    hψ.comp (measurable_const_mul g⁻¹)
                  simp_rw [hswap g]
                  rw [← lintegral_mul_left_eq_self (fun x => ‖⟪v, ρ x v⟫_ℂ‖ₑ) g⁻¹,
                    ← lintegral_const_mul _ hm]
                  exact lintegral_congr fun h => by ring
              _ = _ := by
                  rw [lintegral_mul_const _ hm4, lintegral_const_mul _ hfe]
      _ = (∫⁻ g, ‖f g‖ₑ ^ 2 ∂ν) * ∫⁻ x, ‖⟪v, ρ x v⟫_ℂ‖ₑ ∂ν := by
          rw [← two_mul, ← mul_assoc, ← mul_assoc,
            ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_mul]
  have hX : ENNReal.ofReal (∫ g, ‖f g‖ ^ 2 ∂ν) = ∫⁻ g, ‖f g‖ₑ ^ 2 ∂ν := by
    rw [ofReal_integral_eq_lintegral_ofReal hf2 (Filter.Eventually.of_forall fun g => sq_nonneg _)]
    refine lintegral_congr fun g => ?_
    rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm]
  have hY : ENNReal.ofReal (∫ g, ‖⟪v, ρ g v⟫_ℂ‖ ∂ν) = ∫⁻ x, ‖⟪v, ρ x v⟫_ℂ‖ₑ ∂ν := by
    rw [ofReal_integral_eq_lintegral_ofReal hφ.norm (Filter.Eventually.of_forall fun g => norm_nonneg _)]
    exact lintegral_congr fun g => ofReal_norm_eq_enorm _
  have hL : ‖∫ g, f g • ρ g v ∂ν‖ ^ 2 = ‖⟪∫ g, f g • ρ g v ∂ν, ∫ g, f g • ρ g v ∂ν⟫_ℂ‖ := by
    rw [inner_self_eq_norm_sq_to_K]
    simp
  rw [hL, ← ENNReal.ofReal_le_ofReal_iff (mul_nonneg hA hB), ENNReal.ofReal_mul hA, hX, hY,
    ofReal_norm_eq_enorm]
  exact key

end GlobalTheory.CompanionTheory.Godement
end

section

noncomputable section

open MeasureTheory GlobalTheory.CompanionTheory.UnitaryFramesMetricPeriods
open scoped InnerProductSpace

namespace GlobalTheory.CompanionTheory.RgHeA

variable {Γ : Type} [Group Γ] [TopologicalSpace Γ] [SecondCountableTopology Γ] [MeasurableSpace Γ] [BorelSpace Γ]
  {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem integrable_smul_rep {ν : Measure Γ} {τ : Γ → (H →L[ℂ] H)} (hτ : IsU τ) {f : Γ → ℂ} (hf : Integrable f ν) (b : H) :
    Integrable (fun g => f g • τ g b) ν := by
  refine (hf.norm.mul_const ‖b‖).mono' (hf.aestronglyMeasurable.smul (hτ.4 b).aestronglyMeasurable)
    (.of_forall fun g => ?_)
  rw [norm_smul, hτ.norm]

theorem integrable_mul_inner {ν : Measure Γ} {τ : Γ → (H →L[ℂ] H)} (hτ : IsU τ) {f : Γ → ℂ} (hf : Integrable f ν) (a b : H) :
    Integrable (fun g => f g * ⟪a, τ g b⟫_ℂ) ν := by
  refine (hf.norm.mul_const (‖a‖ * ‖b‖)).mono'
    (hf.aestronglyMeasurable.mul (continuous_const.inner (hτ.4 b)).aestronglyMeasurable)
    (.of_forall fun g => ?_)
  rw [norm_mul]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  calc ‖⟪a, τ g b⟫_ℂ‖ ≤ ‖a‖ * ‖τ g b‖ := norm_inner_le_norm _ _
    _ = ‖a‖ * ‖b‖ := by rw [hτ.norm]

def coefOp (ν : Measure Γ) (τ : Γ → (H →L[ℂ] H)) (hτ : IsU τ) (f : Γ → ℂ) (hf : Integrable f ν) : H →L[ℂ] H :=
  LinearMap.mkContinuous
    { toFun := fun b => ∫ g, f g • τ g b ∂ν
      map_add' := fun x y => by
        rw [← integral_add (integrable_smul_rep hτ hf x) (integrable_smul_rep hτ hf y)]
        simp only [map_add (f := _), smul_add]
      map_smul' := fun c x => by
        simp only [RingHom.id_apply]
        rw [← integral_smul]
        simp only [map_smul, smul_comm c] }
    (∫ g, ‖f g‖ ∂ν) fun b => by
      refine (norm_integral_le_of_norm_le (hf.norm.mul_const ‖b‖) (.of_forall fun g => ?_)).trans_eq ?_
      · rw [norm_smul, hτ.norm]
      · rw [integral_mul_const]

theorem coefOp_apply (ν : Measure Γ) (τ : Γ → (H →L[ℂ] H)) (hτ : IsU τ) (f : Γ → ℂ) (hf : Integrable f ν) (b : H) :
    coefOp ν τ hτ f hf b = ∫ g, f g • τ g b ∂ν := rfl

theorem inner_coefOp (ν : Measure Γ) (τ : Γ → (H →L[ℂ] H)) (hτ : IsU τ) (f : Γ → ℂ) (hf : Integrable f ν) (a b : H) :
    ⟪a, coefOp ν τ hτ f hf b⟫_ℂ = ∫ g, f g * ⟪a, τ g b⟫_ℂ ∂ν := by
  rw [coefOp_apply, ← integral_inner (integrable_smul_rep hτ hf b)]
  simp only [inner_smul_right]

end GlobalTheory.CompanionTheory.RgHeA
end
end

section

open scoped ENNReal
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology Polynomial
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs GlobalTheory.CompanionTheory.Conc
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.AutomorphicForm

theorem _root_.GlobalTheory.T.smoothing_fundamental_domain_bound : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (N : ℕ) [MeasurableSpace (GA E N)] [BorelSpace (GA E N)] (μ : Measure (GA E N)) [μ.IsHaarMeasure] [MeasurableSpace (archGroup E N)] [BorelSpace (archGroup E N)] (ν : Measure (archGroup E N)) [ν.IsHaarMeasure] (F : Set (GA E N)) (β : archGroup E N → ℝ) (c : ℝ≥0∞), IsFundamentalDomain (latticeGL E N) F μ → Ker ν β →
  ∀ f : GA E N → ℂ, Continuous f → (∀ y ∈ tsupport β, ∫⁻ x in F, ‖f (x * infEmb E N y) - f x‖ₑ ^ 2 ∂μ ≤ c) →
  ∫⁻ x in F, ‖f x - sm ν β f x‖ₑ ^ 2 ∂μ ≤ c := by
  first | exact @GlobalTheory.CompanionTheory.Conc.smNear | exact GlobalTheory.CompanionTheory.Conc.smNear | (intros; apply GlobalTheory.CompanionTheory.Conc.smNear <;> assumption)
end

section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG
open scoped TensorProduct

theorem _root_.GlobalTheory.T.average_vanishes_closed_cell : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) (ψ : AddChar k Circle) (hψ : Continuous ψ) (τ : MRep k (i + 1)) (σ : GRep k (t + 1)) (hτ : IsSmooth τ.ρ) (hσ : IsSmooth σ.ρ) (f : XS τ σ) (h0 : eC ψ f = 0)
    (p : Mir k ((i + 1) + t + 1)) (hp : p ∈ Cl k i t),
  AvgVanish (HPG k (i + 1) (t + 1)) (sigX τ σ) (MirUin k ((i + 1) + t + 1)) (mirChar k ψ ((i + 1) + t)) f p := by
  first | exact @GlobalTheory.CompanionTheory.BZPhiPG.LocC.avgVanish_of_mem_Cl | exact GlobalTheory.CompanionTheory.BZPhiPG.LocC.avgVanish_of_mem_Cl | (intros; apply GlobalTheory.CompanionTheory.BZPhiPG.LocC.avgVanish_of_mem_Cl <;> assumption)
end

section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG
open scoped TensorProduct

theorem _root_.GlobalTheory.T.closed_evaluation_equivariant : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) (ψ : AddChar k Circle) (hψ : Continuous ψ) (τ : MRep k (i + 1)) (σ : GRep k (t + 1)) (hτ : IsSmooth τ.ρ) (hσ : IsSmooth σ.ρ) (u : MirUin k ((i + 1) + t + 1)) (f : XS τ σ),
  eC ψ (cInd (HPG k (i + 1) (t + 1)) (sigX τ σ) (u : Mir k ((i + 1) + t + 1)) f) =
      ((mirChar k ψ ((i + 1) + t) u : ℂˣ) : ℂ) • eC ψ f := by
  first | exact @GlobalTheory.CompanionTheory.BZPhiPG.TwC.eC_tw | exact GlobalTheory.CompanionTheory.BZPhiPG.TwC.eC_tw | (intros; apply GlobalTheory.CompanionTheory.BZPhiPG.TwC.eC_tw <;> assumption)
end
