module

public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle003
public import Formalism.RealPlaceAnalysis.Bundle001
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle008
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle009
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle010
public import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.AffineMonoid.UniqueSums
public import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.AddMonoidHomEqZeroOfEventually
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsNumeratorOfInvolution
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.WeierstrassPAddOfNeOfDerivNeZero
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Rat
public import Mathlib.Algebra.Polynomial.SpecificDegree
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.FiniteDimensionalOfSz
public import Mathlib.Algebra.GCDMonoid.Basic
public import Mathlib.Algebra.Polynomial.Degree.Domain
public import Mathlib.Algebra.Polynomial.Degree.Lemmas
public import Mathlib.Algebra.Polynomial.Expand
public import Mathlib.RingTheory.PrincipalIdealDomain
public import Mathlib.LinearAlgebra.FreeModule.Finite.CardQuotient
public import Mathlib.Algebra.Polynomial.Monic
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import Mathlib.NumberTheory.NumberField.Basic

@[expose] public section

section

noncomputable section

open scoped ContDiff Topology
open Matrix

namespace GlobalTheory.SmoothForms

section Centre

variable {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ} {E : Fin n → Fin n → A}

theorem range_le_filt {d d' : ℕ} (h : d' < d) : LinearMap.range (wordMap E d') ≤ filt E d :=
  le_iSup₂_of_le (f := fun d' (_ : d' < d) => LinearMap.range (wordMap E d')) d' h le_rfl

theorem filt_mono {d d' : ℕ} (h : d ≤ d') : filt E d ≤ filt E d' :=
  iSup₂_le fun _ hk => range_le_filt (hk.trans_le h)

theorem filt_succ (d : ℕ) : filt E (d + 1) ≤ LinearMap.range (wordMap E d) ⊔ filt E d :=
  iSup₂_le fun k hk => by
    rcases (Nat.lt_succ_iff.1 hk).eq_or_lt with rfl | h
    · exact le_sup_left
    · exact (range_le_filt h).trans le_sup_right

theorem filt_ad (hE : Formalism.REAL.GlRel E) (d : ℕ) (a b : Fin n) {y : A} (hy : y ∈ filt E d) :
    E a b * y - y * E a b ∈ filt E d := by
  have : filt E d ≤ (filt E d).comap (LinearMap.mulLeft ℂ (E a b) - LinearMap.mulRight ℂ (E a b)) :=
    iSup₂_le fun k hk => by
      rintro _ ⟨M, rfl⟩
      change E a b * wordMap E k M - wordMap E k M * E a b ∈ filt E d
      rw [GlobalTheory.T.commutator_glGenerator_tensorWordMapMatrixUnits A n E hE]
      exact range_le_filt hk ⟨_, rfl⟩
  exact this hy

theorem polar_conjTranspose (d : ℕ) (a b : Fin n) : (polar n d a b)ᴴ = polar n d b a := by
  ext I K
  simp only [polar, conjTranspose_apply, of_apply, star_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  have : (K p = a ∧ I p = b ∧ ∀ q, q ≠ p → K q = I q) ↔ (I p = b ∧ K p = a ∧ ∀ q, q ≠ p → I q = K q) :=
    ⟨fun h => ⟨h.2.1, h.1, fun q hq => (h.2.2 q hq).symm⟩, fun h => ⟨h.2.1, h.1, fun q hq => (h.2.2 q hq).symm⟩⟩
  simp only [this]
  split_ifs <;> simp

theorem gelf_adjoin_comm (hE : Formalism.REAL.GlRel E) {c : A} (hc : c ∈ Algebra.adjoin ℂ (Set.range (gelfA E)))
    (a b : Fin n) : E a b * c = c * E a b := by
  have : Algebra.adjoin ℂ (Set.range (gelfA E)) ≤ Subalgebra.centralizer ℂ {E a b} := by
    refine Algebra.adjoin_le ?_
    rintro _ ⟨k, rfl⟩ _ rfl
    exact GlobalTheory.T.commute_gelfandInvariantMatrixUnits_of_glRel A n E hE k a b
  exact this hc _ rfl

theorem central_of_filt (hE : Formalism.REAL.GlRel E) (d : ℕ) : ∀ z ∈ filt E d, (∀ a b, E a b * z = z * E a b) →
    z ∈ Algebra.adjoin ℂ (Set.range (gelfA E)) := by
  induction d with
  | zero =>
    intro z hz _
    have : filt E 0 ≤ ⊥ := iSup₂_le fun k hk => absurd hk (Nat.not_lt_zero k)
    rw [(Submodule.mem_bot ℂ).1 (this hz)]
    exact zero_mem _
  | succ d ih =>
    intro z hz hc
    obtain ⟨_, ⟨M, rfl⟩, y, hy, rfl⟩ := Submodule.mem_sup.1 (filt_succ d hz)
    obtain ⟨M₀, h1, h2⟩ := GlobalTheory.T.commutant_lift_mod_stable_selfAdjoint _ (Set.range fun p : Fin n × Fin n => polar n d p.1 p.2)
      ((filt E d).comap (wordMap E d))
      (by rintro _ ⟨p, rfl⟩; exact ⟨(p.2, p.1), (polar_conjTranspose d p.1 p.2).symm⟩)
      (by
        rintro _ ⟨p, rfl⟩ N hN
        rw [Submodule.mem_comap, ← GlobalTheory.T.commutator_glGenerator_tensorWordMapMatrixUnits A n E hE]
        exact filt_ad hE d _ _ hN) M
      (by
        rintro _ ⟨p, rfl⟩
        rw [Submodule.mem_comap, ← GlobalTheory.T.commutator_glGenerator_tensorWordMapMatrixUnits A n E hE]
        have h3 := neg_mem (filt_ad hE d p.1 p.2 hy)
        have h4 := hc p.1 p.2
        rw [mul_add, add_mul] at h4
        convert h3 using 1
        rw [neg_sub, sub_eq_sub_iff_add_eq_add, h4, add_comm])
    have h3 : M₀ ∈ Submodule.span ℂ (Set.range (permMat n d)) := by
      refine GlobalTheory.T.bicommutant_tensorFactorPerm_mem_span n d M₀ fun T hT => ?_
      have : Algebra.adjoin ℂ (Set.range fun p : Fin n × Fin n => polar n d p.1 p.2) ≤
          Subalgebra.centralizer ℂ {M₀} := by
        refine Algebra.adjoin_le ?_
        rintro x hx _ rfl
        exact (h2 x hx).symm
      exact this (GlobalTheory.T.mem_adjoin_glAction_of_commute_tensorPerm n d T hT) _ rfl
    have h4 : Submodule.span ℂ (Set.range (permMat n d)) ≤
        (Subalgebra.toSubmodule (Algebra.adjoin ℂ (Set.range (gelfA E))) ⊔ filt E d).comap (wordMap E d) := by
      rw [Submodule.span_le]
      rintro _ ⟨π, rfl⟩
      obtain ⟨c, hc1, hc2⟩ := GlobalTheory.T.permutationWord_gelfandPolynomial_mod_shorter A n E hE d π
      exact Submodule.mem_sup.2 ⟨c, hc1, _, hc2, by abel⟩
    obtain ⟨c, hc1, u, hu, hcu⟩ := Submodule.mem_sup.1 (h4 h3)
    have h5 : wordMap E d M + y - c ∈ filt E d := by
      have h6 : wordMap E d (M - M₀) ∈ filt E d := h1
      have := add_mem (add_mem h6 hu) hy
      convert this using 1
      rw [map_sub, ← hcu]; abel
    have h7 := ih _ h5 fun a b => by rw [mul_sub, sub_mul, hc, gelf_adjoin_comm hE hc1]
    simpa using add_mem h7 hc1

theorem exists_filt {z : A} (hz : z ∈ Algebra.adjoin ℂ (Set.range fun p : Fin n × Fin n => E p.1 p.2)) :
    ∃ d, z ∈ filt E d := by
  have h : z ∈ Submodule.span ℂ (Submonoid.closure (Set.range fun p : Fin n × Fin n => E p.1 p.2) : Set A) := by
    rw [← Algebra.adjoin_eq_span]; exact hz
  clear hz
  induction h using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨l, hl, rfl⟩ := Submonoid.exists_list_of_mem_closure hx
    choose p hp using fun i : Fin l.length => hl (l.get i) (List.get_mem l i)
    refine ⟨l.length + 1, range_le_filt (Nat.lt_succ_self _)
      ⟨Matrix.single (fun i => (p i).1) (fun i => (p i).2) 1, ?_⟩⟩
    have e : (List.ofFn fun i => E (p i).1 (p i).2) = l := by
      simp only [hp]; exact List.ofFn_get l
    simp only [wordMap, LinearMap.coe_mk, AddHom.coe_mk, Matrix.single, of_apply, ite_smul, one_smul, zero_smul,
      ite_and]
    simp [e]
  | zero => exact ⟨0, zero_mem _⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    exact ⟨max a b, add_mem (filt_mono (le_max_left _ _) ha) (filt_mono (le_max_right _ _) hb)⟩
  | smul c x _ hx => exact ⟨_, Submodule.smul_mem _ c hx.choose_spec⟩

theorem center_eq_adjoin (hE : Formalism.REAL.GlRel E)
    (hgen : Algebra.adjoin ℂ (Set.range fun p : Fin n × Fin n => E p.1 p.2) = ⊤) :
    Subalgebra.center ℂ A = Algebra.adjoin ℂ (Set.range (gelfA E)) := by
  refine le_antisymm (fun z hz => ?_) fun c hc => ?_
  · obtain ⟨d, hd⟩ := exists_filt (E := E) (z := z) (hgen ▸ Algebra.mem_top)
    exact central_of_filt hE d z hd fun a b => Subalgebra.mem_center_iff.1 hz _
  · refine Subalgebra.mem_center_iff.2 fun b => ?_
    have : Algebra.adjoin ℂ (Set.range fun p : Fin n × Fin n => E p.1 p.2) ≤ Subalgebra.centralizer ℂ {c} := by
      refine Algebra.adjoin_le ?_
      rintro _ ⟨p, rfl⟩ _ rfl
      exact (gelf_adjoin_comm hE hc p.1 p.2).symm
    exact (this (hgen ▸ Algebra.mem_top : b ∈ _) _ rfl).symm

end Centre

section Operators

variable {𝔸 L G : Type} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [FiniteDimensional ℝ 𝔸] [NormedAddCommGroup L]
  [NormedSpace ℝ L] [Group G] {σ : 𝔸 →ₗ[ℝ] 𝔸} {j : L →ₗ[ℝ] 𝔸} {s : 𝔸 → G}

def smSub (e : L → G) : Submodule ℂ (G → ℂ) where
  carrier := {φ | Sm e φ}
  zero_mem' := fun _ => contDiff_const
  add_mem' := fun h h' g => (h g).add (h' g)
  smul_mem' := fun c _ h g => (h g).const_smul c

theorem Sm.differentiableAt {e : L → G} {φ : G → ℂ} (h : Sm e φ) (g : G) (X : L) :
    DifferentiableAt ℝ (fun t : ℝ => φ (g * e (t • X))) 0 :=
  (((h g).comp (contDiff_id.smul contDiff_const : ContDiff ℝ ∞ fun t : ℝ => t • X)).differentiable
    (by simp)).differentiableAt

def derOp (H : IsLieData σ j s) (hl : HasLog σ j) (X : L) : Module.End ℂ (smSub (expMap j s)) where
  toFun φ := ⟨Der (expMap j s) X φ.1, (GlobalTheory.T.rightDerivativeAlongLie_smooth_and_linear 𝔸 L G σ j s H hl φ.1 φ.2).1 X⟩
  map_add' φ ψ := Subtype.ext (funext fun g => deriv_add (Sm.differentiableAt φ.2 g X) (Sm.differentiableAt ψ.2 g X))
  map_smul' c φ := Subtype.ext (funext fun g => deriv_const_smul c (Sm.differentiableAt φ.2 g X))

theorem derOp_add (H : IsLieData σ j s) (hl : HasLog σ j) (X Y : L) :
    derOp H hl (X + Y) = derOp H hl X + derOp H hl Y :=
  LinearMap.ext fun φ => Subtype.ext ((GlobalTheory.T.rightDerivativeAlongLie_smooth_and_linear 𝔸 L G σ j s H hl φ.1 φ.2).2.1 X Y)

theorem derOp_smul (H : IsLieData σ j s) (hl : HasLog σ j) (c : ℝ) (X : L) :
    derOp H hl (c • X) = (c : ℂ) • derOp H hl X :=
  LinearMap.ext fun φ => Subtype.ext ((GlobalTheory.T.rightDerivativeAlongLie_smooth_and_linear 𝔸 L G σ j s H hl φ.1 φ.2).2.2 c X)

theorem derOp_bracket (H : IsLieData σ j s) (hl : HasLog σ j) (X Y Z : L) (h : j Z = j X * j Y - j Y * j X) :
    derOp H hl Z = derOp H hl X * derOp H hl Y - derOp H hl Y * derOp H hl X :=
  LinearMap.ext fun φ => Subtype.ext (GlobalTheory.T.rightDerivativeAlongLie_commutator_eq_bracket 𝔸 L G σ j s H hl φ.1 φ.2 X Y Z h).symm

theorem derOp_zero (H : IsLieData σ j s) (hl : HasLog σ j) : derOp H hl 0 = 0 := by
  simpa using derOp_smul H hl 0 0

end Operators

end GlobalTheory.SmoothForms

end
end

section

open NumberField IsDedekindDomain Polynomial GlobalTheory.FieldSize
open scoped IntermediateField

namespace GlobalTheory

theorem quotient_eq_linear_pow_char_of_derivative_eq_zero
    (k : Type) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (A D : k[X]) (hD : D ≠ 0)
    (hA : A.natDegree ≤ p) (hDp : D.natDegree < p)
    (hder : derivative A * D = A * derivative D) (hnc : ¬ ∃ c : k, A = C c * D) :
    ∃ a b c : k, a ≠ 0 ∧ c ≠ 0 ∧ D = C c ∧ A = C c * (C a * X ^ p + C b) := by
  classical
  have hp : p.Prime := Fact.out
  have hA0 : A ≠ 0 := fun h => hnc ⟨0, by simp [h]⟩
  obtain ⟨A₁, D₁, hA₁, hD₁, hu⟩ := extract_gcd A D
  have hcop : IsCoprime A₁ D₁ := (gcd_isUnit_iff A₁ D₁).1 hu
  generalize gcd A D = g at hA₁ hD₁
  subst hA₁ hD₁
  have hg : g ≠ 0 := left_ne_zero_of_mul hD
  have hD1 : D₁ ≠ 0 := right_ne_zero_of_mul hD
  have hA1 : A₁ ≠ 0 := right_ne_zero_of_mul hA0
  have h1 : derivative A₁ * D₁ = A₁ * derivative D₁ := by
    have h2 : g ^ 2 * (derivative A₁ * D₁) = g ^ 2 * (A₁ * derivative D₁) := by
      simp only [derivative_mul] at hder
      linear_combination hder
    exact mul_left_cancel₀ (pow_ne_zero 2 hg) h2
  have hdvd : D₁ ∣ derivative D₁ :=
    hcop.symm.dvd_of_dvd_mul_left ⟨derivative A₁, by rw [← h1, mul_comm]⟩
  have hD' : derivative D₁ = 0 := by
    by_contra hne
    exact absurd (degree_le_of_dvd hdvd hne) (not_le.2 (degree_derivative_lt hD1))
  have hA' : derivative A₁ = 0 := by
    rw [hD', mul_zero] at h1
    exact (mul_eq_zero.1 h1).resolve_right hD1
  rw [natDegree_mul hg hA1] at hA
  rw [natDegree_mul hg hD1] at hDp
  have eD := expand_contract p hD' hp.ne_zero
  have eA := expand_contract p hA' hp.ne_zero
  have nD := natDegree_expand p (contract p D₁)
  have nA := natDegree_expand p (contract p A₁)
  rw [eD] at nD
  rw [eA] at nA
  have hD0 : D₁.natDegree = 0 := by
    rcases Nat.eq_zero_or_pos (contract p D₁).natDegree with h | h
    · rw [nD, h, zero_mul]
    · have := Nat.le_mul_of_pos_left p h
      omega
  obtain ⟨d, rfl⟩ := natDegree_eq_zero.1 hD0
  have hd : d ≠ 0 := by
    rintro rfl
    exact hD1 (map_zero _)
  have hm : (contract p A₁).natDegree = 1 := by
    rcases Nat.lt_trichotomy (contract p A₁).natDegree 1 with h | h | h
    · exfalso
      have h0 : (contract p A₁).natDegree = 0 := by omega
      rw [h0, zero_mul] at nA
      obtain ⟨a, rfl⟩ := natDegree_eq_zero.1 nA
      refine hnc ⟨a * d⁻¹, ?_⟩
      have : (C a : k[X]) = C (a * d⁻¹) * C d := by
        rw [← map_mul, inv_mul_cancel_right₀ hd]
      rw [this]
      simp only [map_mul]
      ring
    · exact h
    · exfalso
      have h2 : 2 * p ≤ (contract p A₁).natDegree * p := Nat.mul_le_mul_right p h
      have := hp.pos
      omega
  rw [hm, one_mul] at nA
  have hg0 : g.natDegree = 0 := by omega
  obtain ⟨γ, rfl⟩ := natDegree_eq_zero.1 hg0
  have hγ : γ ≠ 0 := by
    rintro rfl
    exact hg (map_zero _)
  obtain ⟨a, ha, b, hab⟩ := natDegree_eq_one.1 hm
  refine ⟨a * d⁻¹, b * d⁻¹, γ * d, mul_ne_zero ha (inv_ne_zero hd), mul_ne_zero hγ hd,
    (map_mul _ _ _).symm, ?_⟩
  have hdd : (C d : k[X]) * C d⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel₀ hd, map_one]
  rw [← eA, ← hab]
  simp only [map_add (f := _), map_mul, expand_C, expand_X]
  linear_combination (-(C γ * (C a * X ^ p + C b))) * hdd

end GlobalTheory
end

section

open NumberField IsDedekindDomain Polynomial GlobalTheory.FieldSize
open scoped IntermediateField

namespace GlobalTheory

theorem relIndex_mul_periodLattice (L : PeriodPair) {α : ℂ} (h0 : α ≠ 0)
    (hα : ∀ l ∈ L.lattice, α * l ∈ L.lattice) :
    (((AddSubgroup.map (AddMonoidHom.mulLeft α) L.lattice.toAddSubgroup).relIndex
      L.lattice.toAddSubgroup : ℕ) : ℝ) = ‖α‖ ^ 2 := by
  classical
  let f : L.lattice →ₗ[ℤ] L.lattice := (LinearMap.mulLeft ℤ α).restrict (fun l hl => hα l hl)
  have hf : ∀ x : L.lattice, (f x : ℂ) = α * x := fun x => rfl
  have hinj : Function.Injective f := by
    intro x y hxy
    have := congrArg (fun t : L.lattice => (t : ℂ)) hxy
    simp only [hf] at this
    exact Subtype.ext (mul_left_cancel₀ h0 this)
  have hsub : (AddSubgroup.map (AddMonoidHom.mulLeft α) L.lattice.toAddSubgroup).addSubgroupOf
      L.lattice.toAddSubgroup = (LinearMap.range f).toAddSubgroup := by
    ext x
    rw [AddSubgroup.mem_addSubgroupOf, AddSubgroup.mem_map]
    constructor
    · rintro ⟨y, hy, hxy⟩
      exact ⟨⟨y, hy⟩, Subtype.ext hxy⟩
    · rintro ⟨y, hy⟩
      exact ⟨y, y.2, congrArg Subtype.val hy⟩
  have hidx := AddSubgroup.index_eq_natAbs_det L.latticeBasis (LinearMap.range f).toAddSubgroup
    (L.latticeBasis.map (LinearEquiv.ofInjective f hinj))
  have hdet : (L.latticeBasis.det fun i =>
      ((L.latticeBasis.map (LinearEquiv.ofInjective f hinj)) i : L.lattice)) =
      L.latticeBasis.repr (f (L.latticeBasis 0)) 0 * L.latticeBasis.repr (f (L.latticeBasis 1)) 1 -
      L.latticeBasis.repr (f (L.latticeBasis 1)) 0 * L.latticeBasis.repr (f (L.latticeBasis 0)) 1 := by
    rw [Module.Basis.det_apply, Matrix.det_fin_two]
    rfl
  have hrep : ∀ x : L.lattice, α * x = (L.latticeBasis.repr (f x) 0 : ℤ) * L.ω₁ +
      (L.latticeBasis.repr (f x) 1 : ℤ) * L.ω₂ := by
    intro x
    have := congrArg (fun t : L.lattice => (t : ℂ)) (L.latticeBasis.sum_repr (f x))
    simp only [Fin.sum_univ_two, hf] at this
    rw [← this]
    simp
  have h1 := hrep (L.latticeBasis 0)
  have h2 := hrep (L.latticeBasis 1)
  rw [AddSubgroup.relIndex, hsub]
  refine (congrArg Nat.cast (hidx.trans (congrArg Int.natAbs hdet))).trans ?_
  generalize L.latticeBasis.repr (f (L.latticeBasis 0)) 0 = a at h1 h2 ⊢
  generalize L.latticeBasis.repr (f (L.latticeBasis 0)) 1 = c at h1 h2 ⊢
  generalize L.latticeBasis.repr (f (L.latticeBasis 1)) 0 = b at h1 h2 ⊢
  generalize L.latticeBasis.repr (f (L.latticeBasis 1)) 1 = d at h1 h2 ⊢
  simp only [PeriodPair.latticeBasis_zero, PeriodPair.latticeBasis_one] at h1 h2
  have hD : L.ω₁.re * L.ω₂.im - L.ω₂.re * L.ω₁.im ≠ 0 := by
    intro hD
    have hind := LinearIndependent.pair_iff.mp L.indep
    have e1 := hind L.ω₂.im (-L.ω₁.im) (by
      apply Complex.ext <;> simp <;> linarith)
    have e2 := hind L.ω₂.re (-L.ω₁.re) (by
      apply Complex.ext <;> simp <;> linarith)
    have e3 : L.ω₂ = 0 := Complex.ext e2.1 e1.1
    have := hind 0 1 (by simp [e3])
    exact one_ne_zero this.2
  have r1 := congrArg Complex.re h1
  have i1 := congrArg Complex.im h1
  have r2 := congrArg Complex.re h2
  have i2 := congrArg Complex.im h2
  simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.intCast_re,
    Complex.intCast_im, zero_mul, sub_zero, add_zero] at r1 i1 r2 i2
  have key : ((a * d - b * c : ℤ) : ℝ) = ‖α‖ ^ 2 := by
    apply mul_right_cancel₀ hD
    rw [Complex.sq_norm, Complex.normSq_apply]
    push_cast
    have : (α.re * L.ω₁.re - α.im * L.ω₁.im) * (α.re * L.ω₂.im + α.im * L.ω₂.re) -
        (α.re * L.ω₂.re - α.im * L.ω₂.im) * (α.re * L.ω₁.im + α.im * L.ω₁.re) =
        (a * L.ω₁.re + c * L.ω₂.re) * (b * L.ω₁.im + d * L.ω₂.im) -
        (b * L.ω₁.re + d * L.ω₂.re) * (a * L.ω₁.im + c * L.ω₂.im) := by
      rw [r1, i1, r2, i2]
    linear_combination -this
  rw [Nat.cast_natAbs, Int.cast_abs, key]
  exact abs_of_nonneg (by positivity)

theorem exists_weierstrassP_mul_ode : ∀ (L : PeriodPair) (α : ℂ) (N : ℕ), α ≠ 0 → (∀ l ∈ L.lattice, α * l ∈ L.lattice) → ‖α‖ ^ 2 = N → ∃ A D : ℂ[X], D ≠ 0 ∧ A.natDegree = N ∧ D.natDegree + 1 = N ∧ (∀ z, α * z ∉ L.lattice → D.eval (L.weierstrassP z) ≠ 0 ∧ L.weierstrassP (α * z) = A.eval (L.weierstrassP z) / D.eval (L.weierstrassP z)) ∧ C (α ^ 2) * D * (4 * A ^ 3 - C L.g₂ * A * D ^ 2 - C L.g₃ * D ^ 3) = (derivative A * D - A * derivative D) ^ 2 * (4 * X ^ 3 - C L.g₂ * X - C L.g₃) := by
  intro L α N h0 hα hN
  obtain ⟨A, D, -, -, hmon, -, -, hA, hD, hz, hdiv⟩ :=
    exists_weierstrassP_mul_eq_div h0 hα ⊤ trivial trivial trivial (fun _ _ _ => trivial)
  have hAN : A.natDegree = N := by
    have := relIndex_mul_periodLattice L h0 hα
    rw [← hA, hN] at this
    exact_mod_cast this
  refine ⟨A, D, hmon.ne_zero, hAN, hD.trans hAN, fun z hz' => ⟨?_, hdiv z hz'⟩, ?_⟩
  · intro h
    exact hz' ((hz z (fun hl => hz' (hα z hl))).mp h)
  · apply Polynomial.eq_of_infinite_eval_eq
    have hfin : {x : ℂ | D.IsRoot x}.Finite := Polynomial.finite_setOfPred_isRoot hmon.ne_zero
    refine hfin.infinite_compl.mono ?_
    intro x hx
    obtain ⟨z, hzL, rfl⟩ := exists_weierstrassP_eq L x
    have hx' : D.eval (L.weierstrassP z) ≠ 0 := hx
    have hαz : α * z ∉ L.lattice := fun h => hx' ((hz z hzL).mpr h)
    have e1 := derivWeierstrassP_mul_eq hα hdiv hαz hx'
    have e2 := L.derivWeierstrassP_sq z hzL
    have e3 := L.derivWeierstrassP_sq _ hαz
    rw [hdiv z hαz] at e3
    simp only [Set.mem_ofPred_eq, eval_mul, eval_sub, eval_pow, eval_C, eval_X, eval_ofNat] at e1 ⊢
    rw [← e2]
    have e4 := congrArg (· ^ 2) e1
    simp only [mul_pow] at e4
    rw [e3] at e4
    field_simp at e4
    linear_combination e4

end GlobalTheory
end

section

set_option autoImplicit false

open NumberField IsDedekindDomain GlobalTheory.FieldSize
open scoped IntermediateField

namespace GlobalTheory.FieldSize.RayExistCurve

section Quadratic

variable {K : Type} [Field K] [NumberField K] {d : ℕ}

end Quadratic


set_option autoImplicit false in
open NumberField IsDedekindDomain Polynomial in
open scoped IntermediateField in
theorem _root_.GlobalTheory.FieldSize.RayExistCurve.finrank_adjoin {d : ℕ} (hd : 0 < d) {r : ℂ} (hr : r ^ 2 = -(d : ℂ)) :
    FiniteDimensional ℚ ℚ⟮r⟯ ∧ Module.finrank ℚ ℚ⟮r⟯ = 2 := by
  open Polynomial in
  have hroot : aeval r (X ^ 2 + C (d : ℚ)) = 0 := by simp [hr]
  have hmon : (X ^ 2 + C (d : ℚ)).Monic := monic_X_pow_add_C _ (by norm_num)
  have hint : IsIntegral ℚ r := ⟨_, hmon, by simpa [aeval_def] using hroot⟩
  have hdeg : (X ^ 2 + C (d : ℚ)).natDegree = 2 := natDegree_X_pow_add_C
  have hirr : Irreducible (X ^ 2 + C (d : ℚ)) := by
    apply irreducible_of_degree_le_three_of_not_isRoot
    · rw [hdeg]; decide
    · intro x hx
      have hx' : x ^ 2 + (d : ℚ) = 0 := by simpa using hx
      have hd' : (0 : ℚ) < d := by exact_mod_cast hd
      nlinarith [sq_nonneg x]
  have hmin : minpoly ℚ r = X ^ 2 + C (d : ℚ) :=
    (minpoly.eq_of_irreducible_of_monic hirr hroot hmon).symm
  refine ⟨IntermediateField.adjoin.finiteDimensional hint, ?_⟩
  rw [IntermediateField.adjoin.finrank hint, hmin, hdeg]

end GlobalTheory.FieldSize.RayExistCurve
end
