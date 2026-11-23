module

public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsEigFrames
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.IntEmbInjective
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle021
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle025
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle044
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle037
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.AemeasurableCxPosDensity
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle043
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsHorizontalTwist
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle045
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.PiTensorProduct
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.Bundle001
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle006
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PUnipotentModulusMatrix
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens

@[expose] public section

section

open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume GroundTheory.Automorphic GlobalTheory.CompanionTheory.Ar.Cusp.Dict
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.Cusp.CMRank

theorem restrict_bijective (E : Type) [Field E] [NumberField E] :
    Function.Bijective (fun φ : E →+* ℂ => φ.comp (algebraMap (𝓞 E) E)) := by
  constructor
  · intro φ ψ h
    exact IsFractionRing.ringHom_ext (A := 𝓞 E) (K := E) (fun a => DFunLike.congr_fun h a)
  · intro s
    refine ⟨embOf s, ?_⟩
    ext a
    exact IsFractionRing.lift_algebraMap (intEmb_injective s) a

theorem natCard_intEmb (E : Type) [Field E] [NumberField E] :
    Nat.card (𝓞 E →+* ℂ) = Module.finrank ℚ E := by
  rw [← Nat.card_congr (Equiv.ofBijective _ (restrict_bijective E)), Nat.card_eq_fintype_card,
    NumberField.Embeddings.card]

theorem cmFam_sum_bijective {E : Type} [Field E] [NumberField E] [IsCMField E] {Ψ : Type} [Fintype Ψ]
    {σ : Ψ → (𝓞 E →+* ℂ)} (h : IsCMFam σ) :
    Function.Bijective
      (Sum.elim σ (fun τ => (starRingEnd ℂ).comp (σ τ)) : Ψ ⊕ Ψ → (𝓞 E →+* ℂ)) := by
  have hconj : ∀ s : 𝓞 E →+* ℂ, (starRingEnd ℂ).comp ((starRingEnd ℂ).comp s) = s := by
    intro s
    ext a
    simp
  obtain ⟨hinj, hiff⟩ := h
  constructor
  · rintro (a | a) (b | b) hab
    · exact congrArg Sum.inl (hinj hab)
    · exact absurd ⟨a, hab⟩ ((hiff (σ b)).1 ⟨b, rfl⟩)
    · exact absurd ⟨b, hab.symm⟩ ((hiff (σ a)).1 ⟨a, rfl⟩)
    · have hab' : (starRingEnd ℂ).comp (σ a) = (starRingEnd ℂ).comp (σ b) := hab
      have : σ a = σ b := by
        rw [← hconj (σ a), hab', hconj]
      exact congrArg Sum.inr (hinj this)
  · intro s
    by_cases hs : ∃ τ, σ τ = s
    · obtain ⟨τ, rfl⟩ := hs
      exact ⟨Sum.inl τ, rfl⟩
    · have hn : ∃ τ, σ τ = (starRingEnd ℂ).comp s := by
        by_contra hc
        exact hs ((hiff s).2 hc)
      obtain ⟨τ, hτ⟩ := hn
      refine ⟨Sum.inr τ, ?_⟩
      change (starRingEnd ℂ).comp (σ τ) = s
      rw [hτ, hconj]

theorem finrank_eq_two_mul_card : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Type) [Fintype Ψ]
    (σ : Ψ → (𝓞 E →+* ℂ)), IsCMFam σ → Module.finrank ℚ E = 2 * Fintype.card Ψ := by
  intro E _ _ _ Ψ _ σ h
  rw [← natCard_intEmb E, ← Nat.card_congr (Equiv.ofBijective _ (cmFam_sum_bijective h)),
    Nat.card_eq_fintype_card, Fintype.card_sum]
  omega

end GlobalTheory.CompanionTheory.Ar.Cusp.CMRank
end

section

open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun GlobalTheory.CompanionTheory.Ar.PB.FMX.GenFl

theorem _root_.GlobalTheory.T.isGenFam_revInv_subfamily : ∀ (Ω G : Type) [Field Ω] [Field G] [Algebra Ω G] (S : Type) [Finite S] (r : S → ℕ) (u : ∀ s, Matrix (Fin (r s)) (Fin (r s)) G) (P : S → Prop) [DecidablePred P], IsGenFam Ω G u → IsGenFam Ω G (fun s => if P s then revInv (u s) else u s) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.FMX.GenFl.isGenFam_revInv_ite | exact GlobalTheory.CompanionTheory.Ar.PB.FMX.GenFl.isGenFam_revInv_ite | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.FMX.GenFl.isGenFam_revInv_ite <;> assumption)
end

section

open MvPolynomial ReciprocityTheory.AnForm.R GlobalTheory.CompanionTheory.Ar.Cmp

theorem _root_.GlobalTheory.T.unit_times_parameter_monomial : ∀ (m e : ℕ) (I : Ideal (MvPolynomial (Fin m) ℂ)) (t : Fin m → ℂ) (r : Fin e → MvPolynomial (Fin m) ℂ) (Jf : Finset (Fin e)) (g : MvPolynomial (Fin m) ℂ) (u : (locRing I t)ˣ) (mm : Fin e → ℕ), (∀ h ∈ I, eval t h = 0) → IsRegularLocalRing (locRing I t) → ringKrullDim (locRing I t) = e → Ideal.span (Set.range fun l => algebraMap _ (locRing I t) (r l)) = Ideal.map (algebraMap _ (locRing I t)) (ptIdeal t) → algebraMap _ (locRing I t) g = u * ∏ i ∈ Jf, algebraMap _ (locRing I t) (r i) ^ mm i → ∀ i ∈ Jf, ∀ n : ℕ, (∃ s ∉ SncRes.Par.chPrime I t (r i), s * g ∈ SncRes.Par.chPrime I t (r i) ^ n ⊔ I) ↔ n ≤ mm i := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Par.exponent_eq_order_polynomial | exact GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Par.exponent_eq_order_polynomial | (intros; apply GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Par.exponent_eq_order_polynomial <;> assumption)
end

section

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Pub.CxInt GlobalTheory.CompanionTheory.Ar.Pub.CxComp Filter Topology
open ReciprocityTheory.AnForm.R (conePts)


theorem _root_.GlobalTheory.T.aemeasurable_cxPosDensity : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (Q : Ideal (MRingOver ℂ ι)) (e : ℕ) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ))
    (L : Fin e → HermLine ι) (g : ((Σ k, ι k) → ℂ) → ℝ),
    IsCxVar Q e → IsSetGoodProj (conePts Q) Ψ → (∀ j, IsSmoothHerm (L j)) → Measurable g →
    (∀ (c : K → ℂ) (z : (Σ k, ι k) → ℂ), (∀ k, c k ≠ 0) → g (fun p => c p.1 * z p) = g z) →
    AEMeasurable (cxPosDens (conePts Q) Ψ (pot L) g) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Pub.CxPosMeas.cxPosDens_aemeasurable | exact GlobalTheory.CompanionTheory.Ar.Pub.CxPosMeas.cxPosDens_aemeasurable | (intros; apply GlobalTheory.CompanionTheory.Ar.Pub.CxPosMeas.cxPosDens_aemeasurable <;> assumption)
end

section

open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder
open GlobalTheory.CompanionTheory.Ar.Cusp.Univ

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.Univ.CoordLat

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {g : ℕ} {Λ : Type} [AddCommGroup Λ] [Module (𝓞 E) Λ]

def ipLin (R : RiemLat E g Λ) (x : Fin g → ℂ) : (Fin g → ℂ) →ₗ[ℂ] ℂ where
  toFun := R.ip x
  map_add' y y' := by simp [RiemLat.ip, add_dotProduct]
  map_smul' c y := by simp [RiemLat.ip, smul_dotProduct]

theorem ip_eq_ipLin (R : RiemLat E g Λ) (x y : Fin g → ℂ) : R.ip x y = ipLin R x y := rfl

theorem conj_ip (R : RiemLat E g Λ) (x y : Fin g → ℂ) : starRingEnd ℂ (R.ip x y) = R.ip y x := by
  show star (y ⬝ᵥ R.Hm *ᵥ star x) = x ⬝ᵥ R.Hm *ᵥ star y
  rw [← star_dotProduct_star, star_mulVec, star_star, R.herm.eq, dotProduct_mulVec]

def diagAct (s : Fin g → (𝓞 E →+* ℂ)) : 𝓞 E →+* Module.End ℂ (Fin g → ℂ) where
  toFun a :=
    { toFun := fun x k => s k a * x k
      map_add' := fun x y => funext fun k => by simp [mul_add]
      map_smul' := fun r x => funext fun k => by simp [mul_left_comm] }
  map_one' := LinearMap.ext fun x => funext fun k => by simp
  map_mul' a b := LinearMap.ext fun x => funext fun k => by simp [mul_assoc]
  map_zero' := LinearMap.ext fun x => funext fun k => by simp
  map_add' a b := LinearMap.ext fun x => funext fun k => by simp [add_mul]

theorem diagAct_apply (s : Fin g → (𝓞 E →+* ℂ)) (a : 𝓞 E) (x : Fin g → ℂ) (k : Fin g) :
    diagAct s a x k = s k a * x k := rfl

section Frame

variable {ι : Type} [Fintype ι] [DecidableEq ι] (R : RiemLat E g Λ) (e : ι ≃ Fin g) (c : ι → Fin g → ℂ)

include e

theorem sum_ip_smul (hc : ∀ i i', R.ip (c i) (c i') = if i = i' then 1 else 0) (z : Fin g → ℂ) :
    ∑ i, R.ip (c i) z • c i = z := by
  have hli : LinearIndependent ℂ c := by
    rw [Fintype.linearIndependent_iff]
    intro a ha k
    have h := congrArg (ipLin R (c k)) ha

    rw [map_zero, map_sum] at h
    simp only [map_smul, ← ip_eq_ipLin, hc, smul_eq_mul] at h
    simpa using h
  have hspan : Submodule.span ℂ (Set.range c) = ⊤ :=
    hli.span_eq_top_of_card_eq_finrank' (by simp [Fintype.card_congr e])
  have hz : z ∈ Submodule.span ℂ (Set.range c) := hspan ▸ Submodule.mem_top
  obtain ⟨a, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 hz
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1

  rw [ip_eq_ipLin, map_sum]
  simp only [map_smul, ← ip_eq_ipLin, hc, smul_eq_mul]
  simp

theorem sum_ip_mul_conj (hc : ∀ i i', R.ip (c i) (c i') = if i = i' then 1 else 0) (u v : Fin g → ℂ) :
    ∑ i, R.ip (c i) u * starRingEnd ℂ (R.ip (c i) v) = R.ip v u := by
  conv_rhs => rw [← sum_ip_smul R e c hc u]

  rw [ip_eq_ipLin, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, ← ip_eq_ipLin, conj_ip, smul_eq_mul]

theorem ip_act (hc : ∀ i i', R.ip (c i) (c i') = if i = i' then 1 else 0) (s : ι → (𝓞 E →+* ℂ))
    (hs : ∀ i, c i ∈ eigSp R.B (s i)) (a : 𝓞 E) (i : ι) (z : Fin g → ℂ) :
    R.ip (c i) (R.B a z) = s i a * R.ip (c i) z := by
  have hB : ∀ l, R.B a (c l) = s l a • c l := fun l => by
    have h := (Submodule.mem_iInf _).1 (hs l) a
    have h' := LinearMap.mem_ker.1 h
    simpa [sub_eq_zero] using h'
  conv_lhs => rw [← sum_ip_smul R e c hc z]

  rw [map_sum, ip_eq_ipLin, map_sum]
  simp only [map_smul, hB, ← ip_eq_ipLin, hc, smul_eq_mul]
  simp [mul_comm]

end Frame

variable {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {j j' : ℕ}

theorem exists_riemLat_coord (R₀ : RiemLat E g Λ) (σ : Ψ → (𝓞 E →+* ℂ)) (e : Ix Ψ j j' ≃ Fin g)
    (c : Ix Ψ j j' → Fin g → ℂ) (hs : ∀ i, c i ∈ eigSp R₀.B (emb σ i))
    (hc : ∀ i i', R₀.ip (c i) (c i') = if i = i' then 1 else 0) :
    ∃ R₁ : RiemLat E g Λ, R₁.form = R₀.form ∧ R₁.Hm = 1 ∧ ∀ a x k, R₁.B a x k = emb σ (e.symm k) a * x k := by
  let P : Λ →+ (Fin g → ℂ) :=
    { toFun := fun x k => R₀.ip (c (e.symm k)) (R₀.P x)
      map_zero' := funext fun k => by simp [ip_eq_ipLin]
      map_add' := fun x y => funext fun k => by simp [ip_eq_ipLin] }
  have hP : ∀ x k, P x k = R₀.ip (c (e.symm k)) (R₀.P x) := fun _ _ => rfl
  refine ⟨{ free := R₀.free, fin := R₀.fin, rank := R₀.rank, form := R₀.form, alt := R₀.alt, unimod := R₀.unimod,
            adj := R₀.adj, P := P, Hm := 1, herm := isHermitian_one, pos := ?_, im := ?_,
            B := diagAct fun k => emb σ (e.symm k), act := ?_ }, rfl, rfl, fun _ _ _ => rfl⟩
  · intro z hz
    obtain ⟨k, hk⟩ := Function.ne_iff.1 hz
    have hk' : z k ≠ 0 := hk
    have : (z ⬝ᵥ (1 : Matrix (Fin g) (Fin g) ℂ) *ᵥ star z).re = ∑ l, Complex.normSq (z l) := by
      simp [dotProduct, Complex.mul_conj]
    rw [this]
    exact Finset.sum_pos' (fun l _ => Complex.normSq_nonneg _) ⟨k, Finset.mem_univ _, Complex.normSq_pos.2 hk'⟩
  · intro x y
    have key : P x ⬝ᵥ (1 : Matrix (Fin g) (Fin g) ℂ) *ᵥ star (P y) = R₀.P x ⬝ᵥ R₀.Hm *ᵥ star (R₀.P y) := by
      have h := sum_ip_mul_conj R₀ e c hc (R₀.P x) (R₀.P y)
      rw [← e.symm.sum_comp] at h
      rw [one_mulVec]
      exact h
    rw [key]
    exact R₀.im x y
  · intro a x
    funext k
    rw [diagAct_apply, hP, hP, R₀.act]
    exact ip_act R₀ e c hc (emb σ) hs a (e.symm k) (R₀.P x)

theorem coord_lat : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {j j' g : ℕ} {Λ : Type} [AddCommGroup Λ] [Module (𝓞 E) Λ] (R₀ : RiemLat E g Λ) (σ : Ψ → (𝓞 E →+* ℂ)) (e : Ix Ψ j j' ≃ Fin g) (c : Ix Ψ j j' → Fin g → ℂ), (∀ i, c i ∈ eigSp R₀.B (emb σ i)) → (∀ i i', R₀.ip (c i) (c i') = if i = i' then 1 else 0) → ∃ R₁ : RiemLat E g Λ, R₁.form = R₀.form ∧ R₁.Hm = 1 ∧ ∀ a x k, R₁.B a x k = emb σ (e.symm k) a * x k :=
  fun R₀ σ e c hs hc => exists_riemLat_coord R₀ σ e c hs hc

end GlobalTheory.CompanionTheory.Ar.Cusp.Univ.CoordLat
end
end

section

open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder
open GlobalTheory.CompanionTheory.Ar.Cusp.Univ

namespace GlobalTheory.CompanionTheory.Ar.Cusp.Univ.Frames

variable {E : Type} [Field E] [NumberField E] {Ψ : Type} {j j' g : ℕ}

theorem span_single_eq_eigSp {ι : Type} (σ : Ψ → (𝓞 E →+* ℂ)) (e : Ix Ψ j j' ≃ Fin g)
    (B : 𝓞 E →+* Module.End ℂ (Fin g → ℂ)) (hB : ∀ a x k, B a x k = emb σ (e.symm k) a * x k)
    (s : 𝓞 E →+* ℂ) (f : ι → Fin g) (h1 : ∀ i, emb σ (e.symm (f i)) = s)
    (h2 : ∀ k, emb σ (e.symm k) = s → ∃ i, f i = k) :
    Submodule.span ℂ (Set.range fun i : ι => (Pi.single (f i) 1 : Fin g → ℂ)) = eigSp B s := by
  have hmem : ∀ x : Fin g → ℂ, x ∈ eigSp B s ↔ ∀ a, B a x = s a • x := by
    intro x
    simp [eigSp, Submodule.mem_iInf, sub_eq_zero]
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    refine (hmem _).2 fun a => ?_
    funext k
    rw [hB]
    by_cases hk : k = f i
    · subst hk
      simp [h1 i]
    · simp [Pi.single_eq_of_ne hk]
  · intro x hx
    have hx' := (hmem x).1 hx
    have hsum : x = ∑ k, x k • (Pi.single k 1 : Fin g → ℂ) := by
      funext m
      simp [Finset.sum_apply, Pi.single_apply]
    rw [hsum]
    refine Submodule.sum_mem _ fun k _ => ?_
    by_cases hk : x k = 0
    · simp [hk]
    · have hs : emb σ (e.symm k) = s := by
        ext a
        have h := congrFun (hx' a) k
        rw [hB, Pi.smul_apply, smul_eq_mul] at h
        exact mul_right_cancel₀ hk h
      obtain ⟨i, rfl⟩ := h2 k hs
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)


omit [NumberField E] in
theorem conj_ne (σ : Ψ → (𝓞 E →+* ℂ)) (h : IsCMFam σ) (τ τ' : Ψ) : σ τ' ≠ (starRingEnd ℂ).comp (σ τ) :=
  fun hc => ((h.2 (σ τ)).1 ⟨τ, rfl⟩) ⟨τ', hc⟩


omit [NumberField E] in
theorem conj_comp_inj {s t : 𝓞 E →+* ℂ} (h : (starRingEnd ℂ).comp s = (starRingEnd ℂ).comp t) : s = t := by
  ext a
  have := congrArg (starRingEnd ℂ) (RingHom.congr_fun h a)
  simpa using this


omit [NumberField E] in
theorem conj_conj_comp (s : 𝓞 E →+* ℂ) : (starRingEnd ℂ).comp ((starRingEnd ℂ).comp s) = s := by
  ext a
  simp

theorem span_single_eigenspace [IsCMField E] [Fintype Ψ] (σ : Ψ → (𝓞 E →+* ℂ)) (e : Ix Ψ j j' ≃ Fin g)
    (B : 𝓞 E →+* Module.End ℂ (Fin g → ℂ)) (hcm : IsCMFam σ) (hB : ∀ a x k, B a x k = emb σ (e.symm k) a * x k) (τ : Ψ) :
    Submodule.span ℂ (Set.range fun i : Fin j' => (Pi.single (e (Sum.inl i, τ)) 1 : Fin g → ℂ)) = eigSp B (σ τ) ∧
      Submodule.span ℂ (Set.range fun i : Fin j => (Pi.single (e (Sum.inr i, τ)) 1 : Fin g → ℂ)) =
        eigSp B ((starRingEnd ℂ).comp (σ τ)) := by
  constructor
  · refine span_single_eq_eigSp σ e B hB (σ τ) (fun i : Fin j' => e (Sum.inl i, τ)) (fun i => ?_) fun k hk => ?_
    · simp [emb]
    · obtain ⟨⟨u, τ'⟩, rfl⟩ := e.surjective k
      rw [Equiv.symm_apply_apply] at hk
      rcases u with b | b
      · have h : σ τ' = σ τ := hk
        obtain rfl := hcm.1 h
        exact ⟨b, rfl⟩
      · have h : (starRingEnd ℂ).comp (σ τ') = σ τ := hk
        refine absurd ?_ (conj_ne σ hcm τ τ')
        rw [← h, conj_conj_comp]
  · refine span_single_eq_eigSp σ e B hB _ (fun i : Fin j => e (Sum.inr i, τ)) (fun i => ?_) fun k hk => ?_
    · simp [emb]
    · obtain ⟨⟨u, τ'⟩, rfl⟩ := e.surjective k
      rw [Equiv.symm_apply_apply] at hk
      rcases u with b | b
      · exact absurd (show σ τ' = (starRingEnd ℂ).comp (σ τ) from hk) (conj_ne σ hcm τ τ')
      · have h : (starRingEnd ℂ).comp (σ τ') = (starRingEnd ℂ).comp (σ τ) := hk
        obtain rfl := hcm.1 (conj_comp_inj h)
        exact ⟨b, rfl⟩

theorem span_single_eigSp : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {Ψ : Type} [Fintype Ψ] {j j' g : ℕ} (σ : Ψ → (𝓞 E →+* ℂ)) (e : Ix Ψ j j' ≃ Fin g) (B : 𝓞 E →+* Module.End ℂ (Fin g → ℂ)), IsCMFam σ → (∀ a x k, B a x k = emb σ (e.symm k) a * x k) → ∀ τ, Submodule.span ℂ (Set.range fun i : Fin j' => (Pi.single (e (Sum.inl i, τ)) 1 : Fin g → ℂ)) = eigSp B (σ τ) ∧ Submodule.span ℂ (Set.range fun i : Fin j => (Pi.single (e (Sum.inr i, τ)) 1 : Fin g → ℂ)) = eigSp B ((starRingEnd ℂ).comp (σ τ)) :=
  fun σ e B h hB τ => span_single_eigenspace σ e B h hB τ

end GlobalTheory.CompanionTheory.Ar.Cusp.Univ.Frames
end

section

open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder
open GlobalTheory.CompanionTheory.Ar.Cusp.Univ

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.Univ.GramPot

theorem one_sub_bigZ {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {j j' n : ℕ} (q : Ψ × Fin j × Fin j' ≃ Fin n) (t : Fin n → ℂ) :
    1 - (bigZ q t)ᴴ * bigZ q t = blockDiagonal fun τ =>
      fromBlocks (1 - (ballMat q t τ)ᴴ * ballMat q t τ) 0 0 (1 - ((ballMat q t τ)ᵀ)ᴴ * (ballMat q t τ)ᵀ) := by
  unfold bigZ
  rw [blockDiagonal_conjTranspose, ← blockDiagonal_mul, ← blockDiagonal_one, ← blockDiagonal_sub]
  congr 1
  funext τ
  rw [Pi.sub_apply, Pi.one_apply, fromBlocks_conjTranspose, fromBlocks_multiply, ← fromBlocks_one, sub_eq_add_neg, fromBlocks_neg, fromBlocks_add]
  simp [sub_eq_add_neg]

theorem inv_blockDiagonal_fromBlocks {o a b : Type} [Fintype o] [DecidableEq o] [Fintype a] [DecidableEq a]
    [Fintype b] [DecidableEq b] (A : o → Matrix a a ℂ) (D : o → Matrix b b ℂ)
    (hA : ∀ k, (A k).det ≠ 0) (hD : ∀ k, (D k).det ≠ 0) :
    (blockDiagonal fun k => fromBlocks (A k) 0 0 (D k))⁻¹ =
      blockDiagonal fun k => fromBlocks (A k)⁻¹ 0 0 (D k)⁻¹ := by
  apply Matrix.inv_eq_left_inv
  rw [← blockDiagonal_mul, ← blockDiagonal_one]
  congr 1
  funext k
  rw [fromBlocks_multiply, Pi.one_apply, ← fromBlocks_one]
  have h1 : (A k)⁻¹ * A k = 1 := Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (hA k))
  have h2 : (D k)⁻¹ * D k = 1 := Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (hD k))
  simp [h1, h2]

theorem det_conj_block {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (Z : Matrix b a ℂ) :
    (1 - (Zᵀ)ᴴ * Zᵀ).det = (1 - Zᴴ * Z).det := by
  rw [Matrix.det_one_sub_mul_comm, ← Matrix.det_transpose (1 - Zᴴ * Z)]
  congr 1
  rw [transpose_sub, transpose_one, transpose_mul]
  congr 1

theorem inv_apply_inl {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {j j' n : ℕ} (q : Ψ × Fin j × Fin j' ≃ Fin n) (t : Fin n → ℂ)
    (ht : t ∈ ballDom q) (τ : Ψ) (a b : Fin j') :
    (1 - (bigZ q t)ᴴ * bigZ q t)⁻¹ (Sum.inl a, τ) (Sum.inl b, τ) =
      ((1 - (ballMat q t τ)ᴴ * ballMat q t τ)⁻¹ : Matrix (Fin j') (Fin j') ℂ) a b := by
  have hA : ∀ k, (1 - (ballMat q t k)ᴴ * ballMat q t k).det ≠ 0 := fun k => (ht k).det_pos.ne'
  have hD : ∀ k, (1 - ((ballMat q t k)ᵀ)ᴴ * (ballMat q t k)ᵀ).det ≠ 0 := fun k => by
    rw [det_conj_block]; exact hA k
  rw [one_sub_bigZ, inv_blockDiagonal_fromBlocks _ _ hA hD]
  simp

theorem one_sub_bigZe {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {j j' n g : ℕ} (e : Ix Ψ j j' ≃ Fin g)
    (q : Ψ × Fin j × Fin j' ≃ Fin n) (t : Fin n → ℂ) :
    (1 - (bigZe e q t)ᴴ * bigZe e q t)⁻¹ = ((1 - (bigZ q t)ᴴ * bigZ q t)⁻¹).submatrix e.symm e.symm := by
  have h : 1 - (bigZe e q t)ᴴ * bigZe e q t = (1 - (bigZ q t)ᴴ * bigZ q t).submatrix e.symm e.symm := by
    unfold bigZe
    have h1 : (1 : Matrix (Fin g) (Fin g) ℂ) = (1 : Matrix (Ix Ψ j j') (Ix Ψ j j') ℂ).submatrix e.symm e.symm :=
      (submatrix_one_equiv e.symm).symm
    rw [conjTranspose_submatrix, submatrix_mul_equiv, h1]
    rfl
  rw [h, inv_submatrix_equiv]

theorem log_det_inv {a : Type} [Fintype a] [DecidableEq a] (A : Matrix a a ℂ) (hA : A.PosDef) :
    Real.log (A⁻¹).det.re = -Real.log A.det.re := by
  have hpos : 0 < A.det := hA.det_pos
  obtain ⟨hre, him⟩ := Complex.pos_iff.mp hpos
  have hreal : A.det = (A.det.re : ℂ) := by
    apply Complex.ext <;> simp [← him]
  have hinv : (A⁻¹).det = ((A.det.re)⁻¹ : ℝ) := by
    rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv', hreal]
    simp
  rw [hinv, Complex.ofReal_re, Real.log_inv]

theorem logDet_coord {E : Type} [Field E] [NumberField E] [IsCMField E] {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ]
    {j j' n g : ℕ} {Λ : Type} [AddCommGroup Λ] [Module (𝓞 E) Λ] (e : Ix Ψ j j' ≃ Fin g)
    (q : Ψ × Fin j × Fin j' ≃ Fin n) (t : Fin n → ℂ) (R : RiemLat E g Λ) (ht : t ∈ ballDom q)
    (hH : R.Hm = (1 - (bigZe e q t)ᴴ * bigZe e q t)⁻¹) :
    R.logDet (fun τ (i : Fin j') => (Pi.single (e (Sum.inl i, τ)) 1 : Fin g → ℂ)) = ballPot q t := by
  unfold RiemLat.logDet ballPot
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun τ _ => ?_
  have hG : R.gram (fun i : Fin j' => (Pi.single (e (Sum.inl i, τ)) 1 : Fin g → ℂ)) =
      ((1 - (ballMat q t τ)ᴴ * ballMat q t τ)⁻¹)ᵀ := by
    ext a b
    have hs : star (Pi.single (e (Sum.inl a, τ)) 1 : Fin g → ℂ) = Pi.single (e (Sum.inl a, τ)) 1 := by
      ext i
      by_cases h : i = e (Sum.inl a, τ)
      · subst h; simp
      · simp [Pi.single_eq_of_ne h]
    simp only [RiemLat.gram, RiemLat.ip, Matrix.of_apply, hs, transpose_apply]
    rw [Matrix.mulVec_single_one, single_one_dotProduct, hH, one_sub_bigZe]
    simp [inv_apply_inl q t ht]
  rw [hG, det_transpose, log_det_inv _ (ht τ)]

end GlobalTheory.CompanionTheory.Ar.Cusp.Univ.GramPot
end
end

section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo MeasureTheory GlobalTheory.CompanionTheory.Ar.Tw

theorem _root_.GlobalTheory.T.multAt_twist_quad_eq : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (p : ℕ) (J W : Ideal (MRing ι)), W ∈ J.minimalPrimes → (twist p W).IsPrime → multAt (J.map inc ⊔ Ideal.span {quad p}) (twist p W) = multAt J W := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Tw.multAt_twist | exact GlobalTheory.CompanionTheory.Ar.Tw.multAt_twist | (intros; apply GlobalTheory.CompanionTheory.Ar.Tw.multAt_twist <;> assumption)
end
