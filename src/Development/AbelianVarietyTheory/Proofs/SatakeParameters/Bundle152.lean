module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle145
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle006
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.NotInSupportOfSubsingleton
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle053
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.IsTemperedGLOfIsUnitaryLSeg
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle148
import Mathlib.Algebra.Module.StablyFree.Basic
public import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.WittEmbeddingsCompatible
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle149
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle012
public import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.Bundle001
import Formalism.SharpRestriction.AdmissibleParameterJoins.GandSp
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle008
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle134
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle010
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.TrivialOnInertiaOfUnr

@[expose] public section

section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead GlobalTheory.ProdReorder


theorem _root_.GlobalTheory.T.parabolicInductionTwoBlocks_empty_product_left : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (r t : ℕ) (h : t + r = r) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin r) k) V), IsSmooth π → ∀ (d : Fin 0 → ℕ) (X : Fin 0 → Type) [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)] (τ : ∀ a, Representation ℂ (GL (Fin (d a)) k) (X a)) (e : (Σ a, Fin (d a)) ≃ Fin t), Nonempty ((ind₂ (stdSum h) (extTensor (multiProd e τ) π)).Equiv π) := by
  first | exact @GlobalTheory.ProdReorder.ind₂_unit_left | exact GlobalTheory.ProdReorder.ind₂_unit_left | (intros; apply GlobalTheory.ProdReorder.ind₂_unit_left <;> assumption)
end

section

noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric GlobalTheory.KerStd GlobalTheory.KerStd.HypCoord Classical
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.D (F1 F2 OwOK TrDual phFF)
open Formalism.InvariantFactorPaths.G7 (UnrOK IsLawOfLog cob)

namespace GlobalTheory.KerStd.HypCoord

theorem posPl_succ_ne_of_parity (D : D7) (p : ℕ) (R : Finset (OrbitPlaces.Pl D)) (hev : Even (nP D p))
    (hR : OrbitPlaces.IsReps D p R) {r r' : OrbitPlaces.Pl D} (hr : r ∈ R) (hr' : r' ∈ R) {s s' : ℕ}
    (hs : s < nP D p) (hs' : s' < nP D p) (hpar : s % 2 = s' % 2) :
    posPl D p (posPl D p r s) 1 ≠ posPl D p r' s' := by
  intro h
  rw [posPl_add] at h
  have hrr : r = r' :=
    (hR (posPl D p r' s')).unique ⟨hr, s + 1, h⟩ ⟨hr', s', rfl⟩
  subst hrr
  have hpos : 0 < nP D p := by omega
  have h2 : posPl D p r ((s + 1) % nP D p) = posPl D p r s' := by rw [posPl_mod, h]
  have h3 : (s + 1) % nP D p = s' := posPl_inj D p r _ _ (Nat.mod_lt _ hpos) hs' h2
  obtain ⟨m, hm⟩ := hev
  rcases Nat.lt_or_ge (s + 1) (nP D p) with hlt | hge
  · rw [Nat.mod_eq_of_lt hlt] at h3
    omega
  · have hsn : s + 1 = nP D p := by omega
    rw [hsn, Nat.mod_self] at h3
    omega

theorem sum_sigma_comb_mul_comb (D : D7) (p : ℕ) [Fact p.Prime] (σ : MaximalUnramifiedExtension p →+* MaximalUnramifiedExtension p)
    (R : Finset (OrbitPlaces.Pl D)) {N N' n : ℕ} (g h : OrbitPlaces.Pl D → Fin N → Fin N' → Fin n → MaximalUnramifiedExtension p)
    (hev : Even (nP D p)) (hR : OrbitPlaces.IsReps D p R)
    (hg : ∀ z a b i, σ (g z a b i) = h (posPl D p z 1) a b i)
    (hp : ∀ w z a b a₁ b₁, ∑ i, h w a b i * g z a₁ b₁ i = if w = z ∧ a = a₁ ∧ b = b₁ then 1 else 0)
    {r r' : OrbitPlaces.Pl D} (hr : r ∈ R) (hr' : r' ∈ R) (a a' : Fin N) (b b' : Fin N')
    (c c' : ZMod (nP D p) → MaximalUnramifiedExtension p) (q : ℕ)
    (hc : ∀ t, t.val % 2 ≠ q → c t = 0) (hc' : ∀ t, t.val % 2 ≠ q → c' t = 0) :
    ∑ i, σ (∑ t, c t * g (OrbitPlaces.orbMap D p r t) a b i) * ∑ t, c' t * g (OrbitPlaces.orbMap D p r' t) a' b' i = 0 := by
  have hterm : ∀ t t' : ZMod (nP D p),
      ∑ i, (σ (c t) * h (posPl D p (OrbitPlaces.orbMap D p r t) 1) a b i) *
        (c' t' * g (OrbitPlaces.orbMap D p r' t') a' b' i) = 0 := by
    intro t t'
    by_cases h1 : t.val % 2 = q
    · by_cases h2 : t'.val % 2 = q
      · have hne : posPl D p (OrbitPlaces.orbMap D p r t) 1 ≠ OrbitPlaces.orbMap D p r' t' :=
          posPl_succ_ne_of_parity D p R hev hR hr hr' (ZMod.val_lt t) (ZMod.val_lt t') (h1.trans h2.symm)
        have e : ∀ i, (σ (c t) * h (posPl D p (OrbitPlaces.orbMap D p r t) 1) a b i) *
            (c' t' * g (OrbitPlaces.orbMap D p r' t') a' b' i) =
            (σ (c t) * c' t') * (h (posPl D p (OrbitPlaces.orbMap D p r t) 1) a b i *
              g (OrbitPlaces.orbMap D p r' t') a' b' i) := fun i => by ring
        simp only [e]
        rw [← Finset.mul_sum, hp, if_neg (fun hh => hne hh.1), mul_zero]
      · simp [hc' t' h2]
    · simp [hc t h1]

  simp only [map_sum, map_mul, hg, Finset.sum_mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun t _ => ?_
  rw [Finset.sum_comm]
  exact Finset.sum_eq_zero fun t' _ => hterm t t'

theorem fOf_isotropic : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (σ : MaximalUnramifiedExtension p →+* MaximalUnramifiedExtension p) (om oms : Fin (nP D p / 2) → MaximalUnramifiedExtension p) (R : Finset (OrbitPlaces.Pl D)) (N N' r : ℕ) (g h : OrbitPlaces.Pl D → Fin N → Fin N' → Fin r → MaximalUnramifiedExtension p), OrbitPlaces.OrbOK D p → OrbitPlaces.IsReps D p R → (∀ z a b i, σ (g z a b i) = h (posPl D p z 1) a b i) → (∀ w z a b a₁ b₁, ∑ i, h w a b i * g z a₁ b₁ i = if w = z ∧ a = a₁ ∧ b = b₁ then 1 else 0) → (∀ e e', ∑ i, σ (fOf D p σ om R g e i) * fOf D p σ om R g e' i = 0) ∧ (∀ e e', ∑ i, σ (fOf' D p σ oms R g e i) * fOf' D p σ oms R g e' i = 0) := by
  intro D p _ σ om oms R N N' r g h hO hR hg hp
  constructor
  · intro e e'
    have key := sum_sigma_comb_mul_comb D p σ R g h hO.even hR hg hp e.1.1.2 e'.1.1.2 e.2.1 e'.2.1 e.2.2 e'.2.2
      (fun t => if t.val % 2 = 0 then σ^[t.val] (om e.1.2) else 0)
      (fun t => if t.val % 2 = 0 then σ^[t.val] (om e'.1.2) else 0) 0
      (fun t ht => if_neg ht) (fun t ht => if_neg ht)
    simpa only [fOf, ite_mul, zero_mul] using key
  · intro e e'
    have key := sum_sigma_comb_mul_comb D p σ R g h hO.even hR hg hp e.1.1.2 e'.1.1.2 e.2.1 e'.2.1 e.2.2 e'.2.2
      (fun t => if t.val % 2 = 0 then 0 else σ^[t.val] (oms e.1.2))
      (fun t => if t.val % 2 = 0 then 0 else σ^[t.val] (oms e'.1.2)) 1
      (fun t ht => if_pos (by omega)) (fun t ht => if_pos (by omega))
    simpa only [fOf', ite_mul, zero_mul] using key

end GlobalTheory.KerStd.HypCoord
end
end

section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric GlobalTheory.KerStd GlobalTheory.KerStd.HypCoord Classical
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.D (F1 F2 OwOK TrDual phFF)
open Formalism.InvariantFactorPaths.G7 (UnrOK IsLawOfLog cob)

noncomputable section

namespace GlobalTheory.KerStd.HypCoord

theorem sum_coef_fOf (D : D7) (p : ℕ) [Fact p.Prime] (σ : MaximalUnramifiedExtension p →+* MaximalUnramifiedExtension p) (om oms : Fin (nP D p / 2) → MaximalUnramifiedExtension p)
    (R : Finset (OrbitPlaces.Pl D)) {N N' r : ℕ} (g : OrbitPlaces.Pl D → Fin N → Fin N' → Fin r → MaximalUnramifiedExtension p)
    (hdual : ∀ s t : ZMod (nP D p), s.val % 2 = t.val % 2 →
      ∑ k, σ^[s.val] (om k) * σ^[t.val] (oms k) = if s = t then 1 else 0)
    (r₀ : R) (a : Fin N) (b : Fin N') (i : Fin r) (s : ZMod (nP D p)) :
    ∑ k, (if s.val % 2 = 0 then fOf D p σ om R g ((r₀, k), a, b) i * σ^[s.val] (oms k)
      else fOf' D p σ oms R g ((r₀, k), a, b) i * σ^[s.val] (om k)) = g (OrbitPlaces.orbMap D p r₀ s) a b i := by
  by_cases hs : s.val % 2 = 0
  · simp only [hs, if_true, fOf, Finset.sum_mul]
    rw [Finset.sum_comm, Finset.sum_eq_single s]
    · simp only [hs, if_true]
      have h := hdual s s rfl
      rw [if_pos rfl] at h
      calc ∑ k, σ^[s.val] (om k) * g (OrbitPlaces.orbMap D p r₀ s) a b i * σ^[s.val] (oms k)
          = g (OrbitPlaces.orbMap D p r₀ s) a b i * ∑ k, σ^[s.val] (om k) * σ^[s.val] (oms k) := by
            rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring
        _ = _ := by rw [h, mul_one]
    · intro t _ hts
      by_cases ht : t.val % 2 = 0
      · simp only [ht, if_true]
        have h := hdual t s (by rw [ht, hs])
        rw [if_neg hts] at h
        calc ∑ k, σ^[t.val] (om k) * g (OrbitPlaces.orbMap D p r₀ t) a b i * σ^[s.val] (oms k)
            = g (OrbitPlaces.orbMap D p r₀ t) a b i * ∑ k, σ^[t.val] (om k) * σ^[s.val] (oms k) := by
              rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring
          _ = 0 := by rw [h, mul_zero]
      · simp [ht]
    · intro h; exact absurd (Finset.mem_univ s) h
  · simp only [hs, if_false, fOf', Finset.sum_mul]
    rw [Finset.sum_comm, Finset.sum_eq_single s]
    · simp only [hs, if_false]
      have h := hdual s s rfl
      rw [if_pos rfl] at h
      calc ∑ k, σ^[s.val] (oms k) * g (OrbitPlaces.orbMap D p r₀ s) a b i * σ^[s.val] (om k)
          = g (OrbitPlaces.orbMap D p r₀ s) a b i * ∑ k, σ^[s.val] (om k) * σ^[s.val] (oms k) := by
            rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring
        _ = _ := by rw [h, mul_one]
    · intro t _ hts
      by_cases ht : t.val % 2 = 0
      · simp [ht]
      · simp only [ht, if_false]
        have h := hdual s t (by omega)
        rw [if_neg (Ne.symm hts)] at h
        calc ∑ k, σ^[t.val] (oms k) * g (OrbitPlaces.orbMap D p r₀ t) a b i * σ^[s.val] (om k)
            = g (OrbitPlaces.orbMap D p r₀ t) a b i * ∑ k, σ^[s.val] (om k) * σ^[t.val] (oms k) := by
              rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring
          _ = 0 := by rw [h, mul_zero]
    · intro h; exact absurd (Finset.mem_univ s) h

theorem hypZ_term (D : D7) (p : ℕ) [Fact p.Prime] {N0 N1 : ℕ} (σ : MaximalUnramifiedExtension p →+* MaximalUnramifiedExtension p) (om oms : Fin (nP D p / 2) → MaximalUnramifiedExtension p)
    (R : Finset (OrbitPlaces.Pl D)) {n : Type} (f f' : (R × Fin (nP D p / 2)) × Fin N0 × Fin N1 → n → MaximalUnramifiedExtension p) (i : n)
    (e : (R × Fin (nP D p / 2)) × Fin N0 × Fin N1) :
    MvPowerSeries.C (f e i : ℂ_[p]) * linEv D p σ (oms e.1.2) e.1.1 e.2.1 e.2.2 +
      MvPowerSeries.C (f' e i : ℂ_[p]) * linOd D p σ (om e.1.2) e.1.1 e.2.1 e.2.2 =
    ∑ s : ZMod (nP D p), MvPowerSeries.C (((if s.val % 2 = 0 then f e i * σ^[s.val] (oms e.1.2)
      else f' e i * σ^[s.val] (om e.1.2) : MaximalUnramifiedExtension p)) : ℂ_[p]) * MvPowerSeries.X (OrbitPlaces.orbMap D p e.1.1 s, e.2.1, e.2.2) := by
  unfold linEv linOd
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun s _ => ?_
  by_cases hs : s.val % 2 = 0
  · simp [hs, map_mul, mul_assoc]
  · simp [hs, map_mul, mul_assoc]

theorem bijective_orbMap (D : D7) (p : ℕ) (R : Finset (OrbitPlaces.Pl D)) (hR : OrbitPlaces.IsReps D p R) :
    Function.Bijective (fun y : R × ZMod (nP D p) => OrbitPlaces.orbMap D p y.1 y.2) := by
  constructor
  · rintro ⟨r₁, s₁⟩ ⟨r₂, s₂⟩ h
    simp only at h
    have hr : (r₁ : OrbitPlaces.Pl D) = r₂ := by
      obtain ⟨r0, _, hu⟩ := hR (OrbitPlaces.orbMap D p r₁ s₁)
      have e1 := hu r₁ ⟨r₁.2, s₁.val, rfl⟩
      have e2 := hu r₂ ⟨r₂.2, s₂.val, h.symm⟩
      rw [e1, e2]
    have hr' : r₁ = r₂ := Subtype.ext hr
    subst hr'
    have hs : s₁ = s₂ := ZMod.val_injective _ (posPl_inj D p r₁ _ _ (ZMod.val_lt s₁) (ZMod.val_lt s₂) h)
    rw [hs]
  · intro z
    obtain ⟨r0, ⟨hr0, e, he⟩, _⟩ := hR z
    refine ⟨(⟨r0, hr0⟩, (e : ZMod (nP D p))), ?_⟩
    show posPl D p r0 (e : ZMod (nP D p)).val = z
    rw [ZMod.val_natCast, posPl_mod, he]

end GlobalTheory.KerStd.HypCoord

namespace GlobalTheory.KerStd.HypCoord

theorem hypZ_fOf (D : D7) (p : ℕ) [Fact p.Prime] (σ : MaximalUnramifiedExtension p →+* MaximalUnramifiedExtension p) (om oms : Fin (nP D p / 2) → MaximalUnramifiedExtension p)
    (R : Finset (OrbitPlaces.Pl D)) {N N' r : ℕ} (g : OrbitPlaces.Pl D → Fin N → Fin N' → Fin r → MaximalUnramifiedExtension p)
    (hR : OrbitPlaces.IsReps D p R)
    (hdual : ∀ s t : ZMod (nP D p), s.val % 2 = t.val % 2 →
      ∑ k, σ^[s.val] (om k) * σ^[t.val] (oms k) = if s = t then 1 else 0) (i : Fin r) :
    hypZ D p σ om oms R (fOf D p σ om R g) (fOf' D p σ oms R g) i =
      ∑ j : OrbitPlaces.Pl D × Fin N × Fin N', MvPowerSeries.C ((g j.1 j.2.1 j.2.2 i : MaximalUnramifiedExtension p) : ℂ_[p]) * MvPowerSeries.X j := by
  set F : (R × Fin (nP D p / 2)) × Fin N × Fin N' → ZMod (nP D p) → MvPowerSeries (OrbitPlaces.Pl D × Fin N × Fin N') ℂ_[p] :=
    fun e s => MvPowerSeries.C (((if s.val % 2 = 0 then fOf D p σ om R g e i * σ^[s.val] (oms e.1.2)
      else fOf' D p σ oms R g e i * σ^[s.val] (om e.1.2) : MaximalUnramifiedExtension p)) : ℂ_[p]) *
        MvPowerSeries.X (OrbitPlaces.orbMap D p e.1.1 s, e.2.1, e.2.2) with hF
  have hB : Function.Bijective (fun y : (R × ZMod (nP D p)) × Fin N × Fin N' => ((OrbitPlaces.orbMap D p y.1.1 y.1.2, y.2) :
      OrbitPlaces.Pl D × Fin N × Fin N')) :=
    (bijective_orbMap D p R hR).prodMap Function.bijective_id
  let eqv : ((R × ZMod (nP D p)) × Fin N × Fin N') × Fin (nP D p / 2) ≃
      ((R × Fin (nP D p / 2)) × Fin N × Fin N') × ZMod (nP D p) :=
    { toFun := fun y => (((y.1.1.1, y.2), y.1.2), y.1.1.2)
      invFun := fun x => (((x.1.1.1, x.2), x.1.2), x.1.1.2)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  unfold hypZ
  calc ∑ e, (MvPowerSeries.C (fOf D p σ om R g e i : ℂ_[p]) * linEv D p σ (oms e.1.2) e.1.1 e.2.1 e.2.2 +
        MvPowerSeries.C (fOf' D p σ oms R g e i : ℂ_[p]) * linOd D p σ (om e.1.2) e.1.1 e.2.1 e.2.2)
      = ∑ e, ∑ s, F e s := Finset.sum_congr rfl fun e _ => hypZ_term D p σ om oms R _ _ i e
    _ = ∑ x : ((R × Fin (nP D p / 2)) × Fin N × Fin N') × ZMod (nP D p), F x.1 x.2 := (Fintype.sum_prod_type' F).symm
    _ = ∑ y : ((R × ZMod (nP D p)) × Fin N × Fin N') × Fin (nP D p / 2), F ((y.1.1.1, y.2), y.1.2) y.1.1.2 :=
        (Fintype.sum_equiv eqv _ _ fun _ => rfl).symm
    _ = ∑ y : (R × ZMod (nP D p)) × Fin N × Fin N', ∑ k, F ((y.1.1, k), y.2) y.1.2 :=
        Fintype.sum_prod_type' (fun (y : (R × ZMod (nP D p)) × Fin N × Fin N') (k : Fin (nP D p / 2)) => F ((y.1.1, k), y.2) y.1.2)
    _ = ∑ y : (R × ZMod (nP D p)) × Fin N × Fin N',
          MvPowerSeries.C ((g (OrbitPlaces.orbMap D p y.1.1 y.1.2) y.2.1 y.2.2 i : MaximalUnramifiedExtension p) : ℂ_[p]) *
            MvPowerSeries.X ((OrbitPlaces.orbMap D p y.1.1 y.1.2, y.2) : OrbitPlaces.Pl D × Fin N × Fin N') := by
        refine Finset.sum_congr rfl fun y _ => ?_
        rw [← sum_coef_fOf D p σ om oms R g hdual y.1.1 y.2.1 y.2.2 i y.1.2, hF]

        simp only [← Finset.sum_mul, ← map_sum]
        congr 2
        push_cast
        rfl
    _ = _ := hB.sum_comp (fun j : OrbitPlaces.Pl D × Fin N × Fin N' =>
          MvPowerSeries.C ((g j.1 j.2.1 j.2.2 i : MaximalUnramifiedExtension p) : ℂ_[p]) * MvPowerSeries.X j)

theorem linForm_hypZ : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (σ : MaximalUnramifiedExtension p →+* MaximalUnramifiedExtension p) (om oms : Fin (nP D p / 2) → MaximalUnramifiedExtension p) (R : Finset (OrbitPlaces.Pl D)) (N N' r : ℕ) (κ : Type) (g : OrbitPlaces.Pl D → Fin N → Fin N' → Fin r → MaximalUnramifiedExtension p) (Λ : κ → Fin r → ℂ_[p]) (T : κ → OrbitPlaces.Pl D × Fin N × Fin N' → ℂ_[p]), OrbitPlaces.OrbOK D p → OrbitPlaces.IsReps D p R → (∀ s t : ZMod (nP D p), s.val % 2 = t.val % 2 → ∑ k, σ^[s.val] (om k) * σ^[t.val] (oms k) = if s = t then 1 else 0) → (∀ q z a b, ∑ i, Λ q i * ((g z a b i : MaximalUnramifiedExtension p) : ℂ_[p]) = T q (z, a, b)) → ∀ q, ∑ i, MvPowerSeries.C (Λ q i) * hypZ D p σ om oms R (fOf D p σ om R g) (fOf' D p σ oms R g) i = ∑ j, MvPowerSeries.C (T q j) * MvPowerSeries.X j := by
  intro D p _ σ om oms R N N' r κ g Λ T _ hR hdual hT q
  simp only [hypZ_fOf D p σ om oms R g hR hdual, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_

  rw [← hT q j.1 j.2.1 j.2.2, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, mul_assoc]

end GlobalTheory.KerStd.HypCoord
end
end

section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric GlobalTheory.KerStd GlobalTheory.KerStd.HypCoord Classical
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.D (F1 F2 OwOK TrDual phFF)
open Formalism.InvariantFactorPaths.G7 (UnrOK IsLawOfLog cob)

namespace GlobalTheory.KerStd.HypCoord

theorem posPl_inj_lt (D : D7) (p : ℕ) (z : OrbitPlaces.Pl D) {a b : ℕ} (hab : a ≤ b) (hb : b < nP D p)
    (he : posPl D p z a = posPl D p z b) : a = b := by
  have h1 : posPl D p (posPl D p z a) (b - a) = posPl D p z a := by
    rw [posPl_add, Nat.add_sub_cancel' hab, he]
  have hd := posPl_fix D p _ _ h1
  have := Nat.eq_zero_of_dvd_of_lt hd (by omega)
  omega

theorem orbMap_inj (D : D7) (p : ℕ) (z : OrbitPlaces.Pl D) {s s' : ZMod (nP D p)}
    (he : posPl D p z s.val = posPl D p z s'.val) : s = s' := by
  apply ZMod.val_injective
  rcases le_total s.val s'.val with h | h
  · exact posPl_inj_lt D p z h (ZMod.val_lt _) he
  · exact (posPl_inj_lt D p z h (ZMod.val_lt _) he.symm).symm

theorem iterate_mul_ringHom {K : Type*} [Semiring K] (σ : K →+* K) (m : ℕ) (x y : K) :
    σ^[m] (x * y) = σ^[m] x * σ^[m] y := by
  rw [← RingHom.coe_pow, map_mul]

theorem fOf_fOf'_dual : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (σ : MaximalUnramifiedExtension p →+* MaximalUnramifiedExtension p) (om oms : Fin (nP D p / 2) → MaximalUnramifiedExtension p) (R : Finset (OrbitPlaces.Pl D)) (N N' r : ℕ) (g h : OrbitPlaces.Pl D → Fin N → Fin N' → Fin r → MaximalUnramifiedExtension p), OrbitPlaces.OrbOK D p → OrbitPlaces.IsReps D p R → TrDual (nP D p) σ om oms → (∀ z a b i, σ (g z a b i) = h (posPl D p z 1) a b i) → (∀ w z a b a₁ b₁, ∑ i, h w a b i * g z a₁ b₁ i = if w = z ∧ a = a₁ ∧ b = b₁ then 1 else 0) → ∀ e e', ∑ i, σ (fOf D p σ om R g e i) * fOf' D p σ oms R g e' i = if e = e' then 1 else 0 := by
  intro D p _ σ om oms R N N' r g h hOK hR hTr hσg hpair e e'
  obtain ⟨⟨⟨r0, hr0⟩, k⟩, a, b⟩ := e
  obtain ⟨⟨⟨r1, hr1⟩, k'⟩, a', b'⟩ := e'
  obtain ⟨m, hm⟩ := hOK.even
  have hn2 := hOK.two
  have hval : ∀ t : ZMod (nP D p), t.val % 2 = 0 → (t + 1).val = t.val + 1 := by
    intro t ht
    have hlt := ZMod.val_lt t
    rw [ZMod.val_add, ZMod.val_one_eq_one_mod, Nat.mod_eq_of_lt (show 1 < nP D p by omega)]
    exact Nat.mod_eq_of_lt (by omega)
  have reps : ∀ (m0 m1 : ℕ), posPl D p r0 m0 = posPl D p r1 m1 → r0 = r1 := fun m0 m1 he =>
    (hR (posPl D p r1 m1)).unique ⟨hr0, m0, he⟩ ⟨hr1, m1, rfl⟩
  have hf : ∀ i, σ (fOf D p σ om R g ((⟨r0, hr0⟩, k), a, b) i) = ∑ t : ZMod (nP D p),
      (if t.val % 2 = 0 then σ^[t.val + 1] (om k) else 0) * h (posPl D p r0 (t.val + 1)) a b i := by
    intro i

    simp only [fOf, map_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    split_ifs with ht
    · rw [map_mul, hσg, ← Function.iterate_succ_apply' σ, OrbitPlaces.orbMap, posPl_add]
    · simp
  have hf' : ∀ i, fOf' D p σ oms R g ((⟨r1, hr1⟩, k'), a', b') i = ∑ t : ZMod (nP D p),
      (if t.val % 2 = 0 then 0 else σ^[t.val] (oms k')) * g (posPl D p r1 t.val) a' b' i := by
    intro i
    simp only [fOf', OrbitPlaces.orbMap]
    refine Finset.sum_congr rfl fun t _ => ?_
    split_ifs <;> simp
  have h2 : ∑ i, σ (fOf D p σ om R g ((⟨r0, hr0⟩, k), a, b) i) * fOf' D p σ oms R g ((⟨r1, hr1⟩, k'), a', b') i =
      ∑ t : ZMod (nP D p), ∑ t' : ZMod (nP D p), (if t.val % 2 = 0 then σ^[t.val + 1] (om k) else 0) *
        (if t'.val % 2 = 0 then 0 else σ^[t'.val] (oms k')) *
        (if posPl D p r0 (t.val + 1) = posPl D p r1 t'.val ∧ a = a' ∧ b = b' then 1 else 0) := by
    rw [Finset.sum_congr rfl fun i _ => by rw [hf i, hf' i, Finset.sum_mul_sum]]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun t' _ => ?_
    rw [← hpair, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => by ring
  have key : ∀ t t' : ZMod (nP D p), (if t.val % 2 = 0 then σ^[t.val + 1] (om k) else 0) *
        (if t'.val % 2 = 0 then 0 else σ^[t'.val] (oms k')) *
        (if posPl D p r0 (t.val + 1) = posPl D p r1 t'.val ∧ a = a' ∧ b = b' then 1 else 0) =
      if t' = t + 1 then (if t.val % 2 = 0 then σ^[t.val + 1] (om k * oms k') else 0) *
        (if r0 = r1 ∧ a = a' ∧ b = b' then 1 else 0) else 0 := by
    intro t t'
    by_cases ht : t.val % 2 = 0
    · have h1 := hval t ht
      by_cases htt : t' = t + 1
      · subst htt
        have hodd : ¬ (t.val + 1) % 2 = 0 := by omega
        rw [if_pos rfl, h1, if_pos ht, if_pos ht, if_neg hodd, iterate_mul_ringHom]
        by_cases hc : r0 = r1 ∧ a = a' ∧ b = b'
        · obtain ⟨rfl, rfl, rfl⟩ := hc
          simp
        · rw [if_neg hc, if_neg]
          rintro ⟨hp, ha, hb⟩
          exact hc ⟨reps _ _ hp, ha, hb⟩
      · rw [if_neg htt]
        by_cases ht' : t'.val % 2 = 0
        · simp [ht']
        · by_cases hc : posPl D p r0 (t.val + 1) = posPl D p r1 t'.val
          · exfalso
            have hr := reps _ _ hc
            subst hr
            rw [← h1] at hc
            exact htt (orbMap_inj D p r0 hc).symm
          · simp [hc]
    · simp [ht]
  rw [h2, Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun t' _ => key t t']
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [← Finset.sum_mul]
  have h3 : ∑ t : ZMod (nP D p), (if t.val % 2 = 0 then σ^[t.val + 1] (om k * oms k') else 0) =
      σ (∑ t : ZMod (nP D p), if t.val % 2 = 0 then σ^[t.val] (om k * oms k') else 0) := by

    rw [map_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    split_ifs
    · rw [Function.iterate_succ_apply']
    · simp
  rw [h3, hTr.2 k k']
  by_cases hk : k = k' <;> by_cases hr : r0 = r1 <;> by_cases ha : a = a' <;> by_cases hb : b = b' <;>
    simp [hk, hr, ha, hb]

end GlobalTheory.KerStd.HypCoord
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section
open scoped TensorProduct

namespace GlobalTheory.SegLen

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

theorem tmul_ne_zero_of_ne {X Y : Type} [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y] {x : X} {y : Y}
    (hx : x ≠ 0) (hy : y ≠ 0) : x ⊗ₜ[ℂ] y ≠ 0 := by
  obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual ℂ Y, φ y ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hy ((Module.forall_dual_apply_eq_zero_iff ℂ y).1 hc)
  intro h0
  have := congrArg ((TensorProduct.rid ℂ X).toLinearMap ∘ₗ LinearMap.lTensor X φ) h0
  simp only [LinearMap.comp_apply, LinearMap.lTensor_tmul, LinearEquiv.coe_coe, TensorProduct.rid_tmul,
    map_zero] at this
  exact hx ((smul_eq_zero.1 this).resolve_left hφ)

theorem lpChar_lpSp_one' (x : WD h) : x.lpChar (WD.lpSp (h := h) 1) = x := by
  have h1 : WD.lpSp (h := h) 1 = WD.lpOfChar h (WeilDeligne.unrChar h (qPow w 0)) (isSmooth_unrChar h _) := by
    refine WD.sound ⟨.refl _ _, fun σ v => ?_, fun v => ?_⟩
    · funext i
      simp [WDRep.spEig]
    · funext i
      simp [shiftEnd_apply]
  rw [h1, lpChar_lpOfChar]
  exact WD.lpTw_zero x

theorem not_mono0_lpChar_lpSp {x : WD h} (hx : IsIrrWD x) {n : ℕ} (hn : 2 ≤ n) :
    ¬ (x.lpChar (WD.lpSp (h := h) n)).mono0 := by
  have h0 := TemperedRec.monodromy_zero_of_irreducible_weilDeligne E Ω A w h x hx
  obtain ⟨m, b, rfl, hirr⟩ := hx
  have : Nontrivial (Fin m → ℂ) := Model.nontrivial_of_isIrreducible hirr
  obtain ⟨v, hv⟩ := exists_ne (0 : Fin m → ℂ)
  rw [WD.monodromyZero_ofWeilDeligneRepClass_iff] at h0
  rw [WD.lpSp, WD.lpChar_mk, WD.monodromyZero_ofWeilDeligneRepClass_iff, WDRep.tensor_N, h0, WDRep.sp_N, LinearMap.rTensor_zero, zero_add]
  intro hN
  obtain ⟨u, hu⟩ : ∃ u, shiftEnd n u ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact shiftEnd_ne_zero hn (LinearMap.ext hc)
  have := LinearMap.congr_fun hN (v ⊗ₜ u)
  rw [LinearMap.lTensor_tmul, LinearMap.zero_apply] at this
  exact tmul_ne_zero_of_ne hv hu this

end GlobalTheory.SegLen
end
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.tempered_rep_tempered_parameter : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (rc : IrrGL (k := w.adicCompletion E) → WD h), IsRec h rc → ∀ (n : ℕ) (σ : IrrRep (GL (Fin n) (w.adicCompletion E))), GlobalTheory.LocGL.IsTemperedGL σ.ρ → (rc (cls σ)).tempered := by
  first | exact @GlobalTheory.LocLanglands.tempered_of_isTemperedGL | exact GlobalTheory.LocLanglands.tempered_of_isTemperedGL | (intros; apply GlobalTheory.LocLanglands.tempered_of_isTemperedGL <;> assumption)
end

section


theorem _root_.GlobalTheory.T.nonempty_coefficient_field_embedding_padic_complex : ∀ (p : ℕ) [Fact p.Prime] (G : Formalism.MainNotions.G.GAtP p), 0 < G.P.nV → Nonempty (Formalism.L2.G.Pend.CEmb G) := by
  first | exact @GlobalTheory.nonempty_cEmb_of_pos_nV | exact GlobalTheory.nonempty_cEmb_of_pos_nV | (intros; apply GlobalTheory.nonempty_cEmb_of_pos_nV <;> assumption)
end
