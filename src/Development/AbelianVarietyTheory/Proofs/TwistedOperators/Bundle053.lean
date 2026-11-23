module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle003
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle045
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle004
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ExponentSeparation
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.FourierJacobiAverage
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnipotentRadicalBasic
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierTransformInversionLocalFieldPi
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegrableOfMemSB
public import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle046
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle047
public import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle048
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Analysis.CStarAlgebra.Classes
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
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower

@[expose] public section

section

open MeasureTheory ValuativeRel Matrix IsLocalRing
open scoped Pointwise ENNReal

noncomputable section
namespace GlobalTheory.LevelUnfold
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.LatPair GlobalTheory.IndefiniteRowSideFullHecke.FlagVolumeFiltration

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ} {q : Unif k}

theorem oneOrbit : OneOrbit k n c q := by
  have h1 : ∀ (L₁ L₂ : Submodule 𝒪[k] (n → k)) (f₁ f₂ : n → k), IsGlue L₁ f₁ → IsGlue L₂ f₂ →
      ∃ g : GL n k, g • L₁ = L₂ ∧ g • f₁ - f₂ ∈ L₂ := by
    intro L₁ L₂ f₁ f₂ g₁ g₂
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (GL n k) (glue g₁) (glue g₂)
    refine ⟨g, by rw [← glue_ker g₁, ← Pair.smul_ker, hg, glue_ker], ?_⟩
    have := (glue_hasVal g₁).gl_smul g
    rwa [hg, Pair.hasVal_one_iff (glue_hasVal g₂), glue_ker] at this
  refine ⟨h1, fun L₀ _ Q h₀ e h => ⟨?_, ?_⟩⟩
  · rintro ⟨u, hu, L'', f'', hG, H⟩
    obtain ⟨g, hg, hg'⟩ := h1 _ _ _ _ (Pair.isGlue Q.hasVal_vec) hG
    refine ⟨u * embX c g, mul_mem (Subgroup.mem_sup_right hu) (Subgroup.mem_sup_left ⟨g, rfl⟩),
      (u * embX c g * h₀)⁻¹ * h, ?_, by group⟩
    rw [MulAction.mem_stabilizer_iff, mul_smul, inv_smul_eq_iff, mul_smul, mul_smul, e, embX_smul_gluedS, hg, H,
      gluedS_congr hg']
  · rintro ⟨r, hr, κ, hκ, rfl⟩
    obtain ⟨g, u, hu, rfl⟩ := Radical.exists_of_mem_R hr
    refine ⟨_, Radical.conj_mem g hu, g • Q.ker, g • Q.vec, ?_, ?_⟩
    · simpa using Pair.isGlue (Q.hasVal_vec.gl_smul g)
    · rw [← embX_smul_gluedS, ← e, mul_smul _ κ, show κ • L₀ = L₀ from hκ]
      simp only [mul_smul, inv_smul_smul]

instance isLattice_interX (L : Submodule 𝒪[k] (n ⊕ Fin c → k)) [hL : L.IsFullLattice k] : (interX L).IsLattice k := by
  apply Submodule.IsLattice.of_fg k
  exact Submodule.fg_of_fg_map_injective (inX k n c)
    (fun x y h => funext fun r => congrFun h (Sum.inl r))
    (hL.fg.of_le (Submodule.map_comap_le _ _))

variable [MeasurableSpace k] [BorelSpace k] {ψ : AddChar k Circle} {ν : Measure k} [ν.IsAddHaarMeasure]

end GlobalTheory.LevelUnfold
end
end

section


theorem _root_.GlobalTheory.T.hasFiniteRankTraceOf_of_range_le_finiteDimensional : ∀ (X : Type) [AddCommGroup X] [Module ℂ X] (T : X →ₗ[ℂ] X) (Z : Submodule ℂ X)
    [FiniteDimensional ℂ Z] (hT : LinearMap.range T ≤ Z),
    GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.HasFinTrace T (LinearMap.trace ℂ Z (T.restrict (p := Z) (q := Z)
      fun x _ => hT (LinearMap.mem_range_self T x))) := by
  first | exact @GlobalTheory.IndefiniteRowSideFullHecke.RangeTrace.hasFinTrace_of_range_le | exact GlobalTheory.IndefiniteRowSideFullHecke.RangeTrace.hasFinTrace_of_range_le | (intros; apply GlobalTheory.IndefiniteRowSideFullHecke.RangeTrace.hasFinTrace_of_range_le <;> assumption)
end

section

open GlobalTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL ValuativeRel

namespace GlobalTheory.ConeCount

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

private theorem ord_zpow_twisted_operators (x : kˣ) (n : ℤ) : ord k (x ^ n) = n * ord k x := by
  let f : kˣ →* Multiplicative ℤ :=
    MonoidHom.mk' (fun y => Multiplicative.ofAdd (ord k y)) fun a b => by
      rw [ord_mul, ofAdd_add]
  have hf := congrArg Multiplicative.toAdd (map_zpow f x n)
  simpa [f, smul_eq_mul] using hf

theorem valuation_div_zpow_ord {ϖ : kˣ} (hϖ : valuation k (ϖ : k) = uniformizer k) (x : kˣ) :
    valuation k ((x / ϖ ^ ord k x : kˣ) : k) = 1 := by
  rw [← ord_eq_zero_iff, div_eq_mul_inv, ord_mul, ← zpow_neg, ord_zpow_twisted_operators, _root_.GlobalTheory.SmGL.ord_eq_one hϖ]
  ring

def powHom {G : Type} [CommGroup G] (ϖ : G) (r : ℕ) :
    Multiplicative (Fin r → ℤ) →* (Fin r → G) :=
  MonoidHom.mk' (fun a i => ϖ ^ (Multiplicative.toAdd a) i) fun a b => by
    funext i
    simp [zpow_add]

theorem eq_of_comp_powHom {ϖ : kˣ} (hϖ : valuation k (ϖ : k) = uniformizer k) {r : ℕ}
    {χ ψ : (Fin r → kˣ) →* ℂˣ} (hχ : ∀ t ∈ torusO k (Fin r), χ t = 1)
    (hψ : ∀ t ∈ torusO k (Fin r), ψ t = 1)
    (h : χ.comp (powHom ϖ r) = ψ.comp (powHom ϖ r)) : χ = ψ := by
  refine MonoidHom.ext fun t => ?_

  have hu : (fun i => t i / ϖ ^ ord k (t i)) ∈ torusO k (Fin r) := by
    show ∀ i, valuation k ((t i / ϖ ^ ord k (t i) : kˣ) : k) = 1
    exact fun i => valuation_div_zpow_ord hϖ (t i)
  have ht : t = (fun i => t i / ϖ ^ ord k (t i)) *
      powHom ϖ r (Multiplicative.ofAdd fun i => ord k (t i)) := by
    funext i
    show t i = t i / ϖ ^ ord k (t i) * ϖ ^ ord k (t i)
    rw [div_mul_cancel]
  have hp := DFunLike.congr_fun h (Multiplicative.ofAdd fun i => ord k (t i))
  rw [MonoidHom.comp_apply, MonoidHom.comp_apply] at hp
  rw [ht, map_mul, map_mul, hχ _ hu, hψ _ hu, one_mul, one_mul, hp]

theorem sum_count_eq_zero (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (ϖ : kˣ) (hϖ : valuation k (ϖ : k) = uniformizer k) (r n : ℕ)
    (E : Fin n → Multiset ((Fin r → kˣ) →* ℂˣ)) (c : Fin n → ℂ)
    (hE : ∀ i, ∀ χ ∈ E i, ∀ t ∈ torusO k (Fin r), χ t = 1)
    (h : ∀ t ∈ IndefiniteRowSideFullHecke.ExponentSeparationTwistedDiscreteSeries.strictCone ϖ r, ∑ i, c i * IndefiniteRowSideFullHecke.ExponentSeparationTwistedDiscreteSeries.charSum (E i) t = 0)
    [DecidableEq ((Fin r → kˣ) →* ℂˣ)] (χ : (Fin r → kˣ) →* ℂˣ) :
    ∑ i, c i * ((E i).count χ : ℂ) = 0 := by

  let M : Submonoid (Multiplicative (Fin r → ℤ)) :=
    { carrier := {a | Antitone (Multiplicative.toAdd a)}
      mul_mem' := by
        intro a b ha hb i j hij
        exact add_le_add (ha hij) (hb hij)
      one_mem' := by
        intro i j _
        exact le_rfl }
  let φ : M →* (Fin r → kˣ) := (powHom ϖ r).comp M.subtype

  let t₀ : Fin r → kˣ := fun i => ϖ ^ (-((i : ℕ) : ℤ))
  have hcone : ∀ m : M, t₀ * φ m ∈ IndefiniteRowSideFullHecke.ExponentSeparationTwistedDiscreteSeries.strictCone ϖ r := by
    intro m
    have hm : Antitone (Multiplicative.toAdd (m : Multiplicative (Fin r → ℤ))) := m.2
    refine ⟨fun i => -((i : ℕ) : ℤ) + Multiplicative.toAdd (m : Multiplicative (Fin r → ℤ)) i, ?_, ?_⟩
    · intro i j hij
      have h1 := hm hij.le
      have h2 : (i : ℕ) < j := hij
      simp only
      omega
    · funext i
      show ϖ ^ (-((i : ℕ) : ℤ)) * ϖ ^ (Multiplicative.toAdd (m : Multiplicative (Fin r → ℤ)) i) = _
      rw [← zpow_add]

  have hdiff : ∀ a : Multiplicative (Fin r → ℤ), ∃ m₁ m₂ : M,
      a = (m₁ : Multiplicative (Fin r → ℤ)) * (m₂ : Multiplicative (Fin r → ℤ))⁻¹ := by
    intro a
    set K : ℤ := ∑ l, |Multiplicative.toAdd a l| with hK
    have hK0 : 0 ≤ K := Finset.sum_nonneg fun l _ => abs_nonneg _
    have hKl : ∀ l, |Multiplicative.toAdd a l| ≤ K := fun l =>
      Finset.single_le_sum (f := fun l => |Multiplicative.toAdd a l|)
        (fun l _ => abs_nonneg _) (Finset.mem_univ l)
    let b : Multiplicative (Fin r → ℤ) := Multiplicative.ofAdd fun i => 2 * K * (-((i : ℕ) : ℤ))
    have hb : b ∈ M := by
      intro i j hij
      have h1 : ((i : ℕ) : ℤ) ≤ ((j : ℕ) : ℤ) := by exact_mod_cast hij
      show 2 * K * (-((j : ℕ) : ℤ)) ≤ 2 * K * (-((i : ℕ) : ℤ))
      nlinarith
    have hab : a * b ∈ M := by
      intro i j hij
      show Multiplicative.toAdd a j + 2 * K * (-((j : ℕ) : ℤ))
        ≤ Multiplicative.toAdd a i + 2 * K * (-((i : ℕ) : ℤ))
      rcases eq_or_lt_of_le hij with h | h
      · rw [h]
      · have h1 : ((i : ℕ) : ℤ) + 1 ≤ ((j : ℕ) : ℤ) := by
          have : (i : ℕ) < j := h
          omega
        have h2 := hKl i
        have h3 := hKl j
        have h4 := le_abs_self (Multiplicative.toAdd a j)
        have h5 := neg_abs_le (Multiplicative.toAdd a i)
        nlinarith
    exact ⟨⟨a * b, hab⟩, ⟨b, hb⟩, by simp⟩

  let S : Finset ((Fin r → kˣ) →* ℂˣ) := Finset.univ.biUnion fun i => (E i).toFinset
  have hS : ∀ ψ ∈ S, ∀ t ∈ torusO k (Fin r), ψ t = 1 := by
    intro ψ hψ t ht
    obtain ⟨i, -, hi⟩ := Finset.mem_biUnion.1 hψ
    exact hE i ψ (Multiset.mem_toFinset.1 hi) t ht

  let G : ((Fin r → kˣ) →* ℂˣ) → (M →* ℂ) := fun ψ => (Units.coeHom ℂ).comp (ψ.comp φ)
  have hinj : Function.Injective fun ψ : S => G ψ := by
    rintro ⟨ψ₁, h₁⟩ ⟨ψ₂, h₂⟩ h
    apply Subtype.ext
    have hM : ∀ m : M, ψ₁ (φ m) = ψ₂ (φ m) := fun m => Units.ext (DFunLike.congr_fun h m)
    refine eq_of_comp_powHom hϖ (hS ψ₁ h₁) (hS ψ₂ h₂) (MonoidHom.ext fun a => ?_)
    obtain ⟨m₁, m₂, rfl⟩ := hdiff a
    have e₁ := hM m₁
    have e₂ := hM m₂
    simp only [φ, MonoidHom.comp_apply, Submonoid.coe_subtype] at e₁ e₂
    simp only [MonoidHom.comp_apply, map_mul, map_inv, e₁, e₂]
  have hli := (linearIndependent_monoidHom M ℂ).comp (fun ψ : S => G ψ) hinj
  rw [Fintype.linearIndependent_iff] at hli

  have hsum : ∀ i t, IndefiniteRowSideFullHecke.ExponentSeparationTwistedDiscreteSeries.charSum (E i) t = ∑ ψ ∈ S, ((E i).count ψ : ℂ) * (ψ t : ℂ) := by
    intro i t
    unfold IndefiniteRowSideFullHecke.ExponentSeparationTwistedDiscreteSeries.charSum
    rw [Finset.sum_multiset_map_count]
    simp only [nsmul_eq_mul]
    refine Finset.sum_subset (fun ψ hψ => Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, hψ⟩) ?_
    intro ψ _ hψ
    rw [Multiset.count_eq_zero.2 fun h' => hψ (Multiset.mem_toFinset.2 h'), Nat.cast_zero, zero_mul]
  have hw := hli (fun ψ => (∑ i, c i * ((E i).count (ψ : (Fin r → kˣ) →* ℂˣ) : ℂ)) * (ψ.1 t₀ : ℂ))
    (by
      funext m
      have hm := h _ (hcone m)
      simp only [hsum, Finset.mul_sum] at hm
      rw [Finset.sum_comm, ← Finset.sum_coe_sort S] at hm
      rw [Finset.sum_apply, Pi.zero_apply, ← hm]
      refine Finset.sum_congr rfl fun ψ _ => ?_
      simp only [Function.comp_apply, Pi.smul_apply, smul_eq_mul, G, φ, MonoidHom.comp_apply,
        Units.coeHom_apply, map_mul, Units.val_mul, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring)
  by_cases hχ : χ ∈ S
  · have h0 := hw ⟨χ, hχ⟩
    exact (mul_eq_zero.1 h0).resolve_right (Units.ne_zero _)
  · refine Finset.sum_eq_zero fun i _ => ?_
    rw [Multiset.count_eq_zero.2 fun h' =>
      hχ (Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, Multiset.mem_toFinset.2 h'⟩)]
    simp

end GlobalTheory.ConeCount
end

section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage

theorem _root_.GlobalTheory.T.rootExchange_heisenbergVariable_sign : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c ρ : ℕ) (_ : 1 ≤ ρ) (_ : ρ < c), (∀ (x₀ : Matrix n n' k) (e : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free (ρ + 1) rs} → k) (β : n → k) (r : n) (i : Fin (c + 1)), i.val + 1 = ρ + 1 → ((1 - ((colE c (ρ + 1) β).val - 1)) * affPt (ρ + 1) x₀ e : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) (Sum.inl r) (Sum.inr i) = -β r) ∧ ∀ (ψ : AddChar k Circle) (ν : Measure k) [ν.IsAddHaarMeasure], Continuous ψ → ∀ (μ : kˣ →* ℂˣ) (Φ : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)) (β : n → k), (∀ x, om μ 1 (colE c (ρ + 1) β) Φ.1 x = Φ.1 ((1 - ((colE c (ρ + 1) β).val - 1)) * x)) ∧ ∀ x₀, fl ψ ν μ ρ Φ.1 x₀ β = opE ψ ν (ρ + 1) (fun x => Φ.1 (x + colM c (ρ + 1) (-β))) x₀ := by
  first | exact @GlobalTheory.RootEx.HeisenbergSign.sign | exact GlobalTheory.RootEx.HeisenbergSign.sign | (intros; apply GlobalTheory.RootEx.HeisenbergSign.sign <;> assumption)
end

section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage

theorem _root_.GlobalTheory.T.rootExchangeOperator_weil_rowUnipotent : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c p : ℕ) (_ : 1 ≤ p) (_ : p ≤ c) (ψ : AddChar k Circle) (_ : Continuous ψ) (ν : Measure k) [ν.IsAddHaarMeasure] (μ : kˣ →* ℂˣ) (Φ : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)) (u : n' → k) (x₀ : Matrix n n' k), opE ψ ν p (om μ (rowE (c + 1) p u) 1 Φ.1) x₀ = opE ψ ν p (fun x => Φ.1 (x + rowM n c p u)) x₀ := by
  first | exact @GlobalTheory.RootEx.RowSign.opE_om_rowE | exact GlobalTheory.RootEx.RowSign.opE_om_rowE | (intros; apply GlobalTheory.RootEx.RowSign.opE_om_rowE <;> assumption)
end

section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage

noncomputable section
namespace GlobalTheory.SplitWeil.FourierSurj

theorem hat_surjective : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n : Type) [Fintype n] [DecidableEq n] (ψ : AddChar k Circle) (_ : Continuous ψ) (_ : ψ ≠ 1) (ν : Measure k) (_ : IsSelfDual ψ ν), (∀ Φ₀ : SB (n → k), hat ψ ν Φ₀.1 ∈ SB (n → k)) ∧ ∀ g : SB (n → k), ∃ Φ₀ : SB (n → k), hat ψ ν Φ₀.1 = g.1 := by
  intro k _ _ _ _ _ _ n _ _ ψ hc h1 ν hν
  haveI := hν.1
  haveI := secondCountable k
  haveI := t2Space k
  have key := FourierPi.fourier_pi k n ψ hc h1 ν hν
  have hhat : ∀ f : (n → k) → ℂ,
      hat ψ ν f = fun y : n → k => ∫ x, f x * (ψ (x ⬝ᵥ y) : ℂ) ∂(Measure.pi fun _ => ν) := by
    intro f
    funext y
    simp only [hat, dotProduct_comm y]
  have hmem : ∀ f ∈ SB (n → k), hat ψ ν f ∈ SB (n → k) := fun f hf => hhat f ▸ (key f hf).1
  refine ⟨fun Φ₀ => hmem _ Φ₀.2, fun g => ?_⟩
  have hcomp : ∀ (e : (n → k) ≃ₜ (n → k)), ∀ f ∈ SB (n → k), (fun x => f (e x)) ∈ SB (n → k) :=
    fun e f hf => ⟨hf.1.comp_continuous e.continuous, hf.2.comp_homeomorph e⟩
  have hg' : (fun x => g.1 (-x)) ∈ SB (n → k) := hcomp (Homeomorph.neg _) _ g.2
  refine ⟨⟨_, hmem _ hg'⟩, ?_⟩
  funext u
  have hf : (fun x => g.1 (-(x + -u))) ∈ SB (n → k) := hcomp (Homeomorph.addRight (-u)) _ hg'
  have h2 := (key _ hf).2
  simp only [zero_add, neg_neg] at h2
  rw [← h2]
  show ∫ β, hat ψ ν (fun x => g.1 (-x)) β * (ψ (u ⬝ᵥ β) : ℂ) ∂(Measure.pi fun _ => ν) = _
  congr 1
  funext y
  rw [hhat, ← integral_mul_const,
    ← integral_add_right_eq_self (μ := Measure.pi fun _ : n => ν) _ (-u)]
  congr 1
  funext x
  rw [mul_assoc, ← Circle.coe_mul, ← AddChar.map_add_eq_mul, ← add_dotProduct, neg_add_cancel_right]

end GlobalTheory.SplitWeil.FourierSurj
end
end

section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage

namespace GlobalTheory.RootEx.FJUnipotent
open GlobalTheory.RootEx.Radical

section
variable {k : Type} [Field k] {n : Type} [Fintype n] [DecidableEq n] {c : ℕ}

def midLev (ρ : ℕ) : n ⊕ Fin c → ℕ :=
  Sum.elim (fun _ => 2 * ρ + 1) (fun i : Fin c => 2 * (i.val + 1))

def midGroup (k : Type) [Field k] (n : Type) [Fintype n] [DecidableEq n] (c ρ : ℕ) :
    Subgroup (GL (n ⊕ Fin c) k) where
  carrier := {g | Uni (midLev ρ) g.val}
  one_mem' := fun _ _ _ => rfl
  mul_mem' := fun hx hy => Uni.mul hx hy
  inv_mem' := fun hx => Uni.inv hx

theorem NFJ_le_midGroup (ρ : ℕ) : NFJ k n c ρ ≤ midGroup k n c ρ := by
  have key : ∀ p, p = ρ ∨ p = ρ + 1 → N k n c p ≤ midGroup k n c ρ := by
    rintro p hp g hg
    have hg' := (mem_N_iff g).1 hg
    show Uni (midLev ρ) g.val
    intro r s hrs
    apply hg' r s
    rcases r with r | i <;> rcases s with s | j <;>
      simp only [lev, midLev, Sum.elim_inl, Sum.elim_inr] at hrs ⊢ <;> omega
  exact sup_le (key ρ (Or.inl rfl)) (key (ρ + 1) (Or.inr rfl))

theorem exists_col (P : Fin c) {g : GL (n ⊕ Fin c) k} (hg : g ∈ midGroup k n c P.val) :
    ∃ u ∈ N k n c (P.val + 1), ∃ β : n → k, g = u * colE c (P.val + 1) β := by
  have hg' : ∀ r s, midLev (n := n) (c := c) P.val s ≤ midLev P.val r →
      g.val r s = (1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) r s := hg
  refine ⟨g * colE c (P.val + 1) (-fun r => g.val (Sum.inl r) (Sum.inr P)), ?_,
    fun r => g.val (Sum.inl r) (Sum.inr P), ?_⟩
  · rw [mem_N_iff]
    intro r s hrs
    rw [Units.val_mul]
    rcases s with s | j
    · rw [GlobalTheory.RootEx.Exchange.mul_colE_inl]
      apply hg'
      rcases r with r | i <;>
        simp only [lev, midLev, Sum.elim_inl, Sum.elim_inr] at hrs ⊢ <;> omega
    · rw [GlobalTheory.RootEx.Exchange.mul_colE_inr]
      by_cases hj : j = P
      · have hc : j.val + 1 = P.val + 1 := by rw [hj]
        rw [if_pos hc, hj]
        rcases r with r | i
        · have hX : ∀ t, g.val (Sum.inl r) (Sum.inl t) = if r = t then 1 else 0 := by
            intro t
            rw [hg' _ _ (by simp only [midLev, Sum.elim_inl]; omega)]
            simp [Matrix.one_apply]
          simp [hX]
        · have hi : P.val ≤ i.val := by
            rw [hj] at hrs
            simp only [lev, Sum.elim_inr] at hrs
            omega
          have h1 := hg' (Sum.inr i) (Sum.inr P) (by simp only [midLev, Sum.elim_inr]; omega)
          have h2 : ∀ t, g.val (Sum.inr i) (Sum.inl t) = 0 := fun t => by
            rw [hg' _ _ (by simp only [midLev, Sum.elim_inl, Sum.elim_inr]; omega)]
            simp
          simp [h1, h2]
      · have hj' : j.val ≠ P.val := fun h => hj (Fin.ext h)
        have hc : ¬ (j.val + 1 = P.val + 1) := fun h => hj' (by omega)
        rw [if_neg hc, add_zero]
        apply hg'
        rcases r with r | i <;>
          simp only [lev, midLev, Sum.elim_inl, Sum.elim_inr] at hrs ⊢ <;> omega
  · rw [mul_assoc, GlobalTheory.RootEx.Exchange.colE_neg_mul, mul_one]

end

theorem fj_unipotent : ∀ (k : Type) [Field k] (n : Type) [Fintype n] [DecidableEq n] (c ρ : ℕ) (_ : 1 ≤ ρ) (_ : ρ < c), (∀ g, g ∈ NFJ k n c ρ ↔ ∃ x ∈ N k n c ρ, ∃ y ∈ N k n c (ρ + 1), g = x * y) ∧ (∀ g : GL (n ⊕ Fin c) k, g ∈ NFJ k n c ρ ↔ ∀ r s : n ⊕ Fin c, Sum.elim (fun _ => 2 * ρ + 1) (fun i : Fin c => 2 * (i.val + 1)) s ≤ Sum.elim (fun _ => 2 * ρ + 1) (fun i : Fin c => 2 * (i.val + 1)) r → g.val r s = (1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) r s) ∧ ∀ g ∈ NFJ k n c ρ, ∃ u ∈ N k n c (ρ + 1), ∃ β : n → k, g = u * colE c (ρ + 1) β := by
  intro k _ n _ _ c ρ _ hρc
  have hle := NFJ_le_midGroup (k := k) (n := n) (c := c) ρ
  have hcol : ∀ g ∈ NFJ k n c ρ, ∃ u ∈ N k n c (ρ + 1), ∃ β : n → k,
      g = u * colE c (ρ + 1) β :=
    fun g hg => exists_col ⟨ρ, hρc⟩ (hle hg)
  have hcolN : ∀ β : n → k, colE c (ρ + 1) β ∈ N k n c ρ :=
    fun β => colE_mem β (Nat.lt_succ_self ρ)
  have hmid : ∀ g : GL (n ⊕ Fin c) k, g ∈ midGroup k n c ρ → g ∈ NFJ k n c ρ := by
    intro g hg
    obtain ⟨u, hu, β, rfl⟩ := exists_col (k := k) ⟨ρ, hρc⟩ hg
    exact (NFJ k n c ρ).mul_mem (le_sup_right (a := N k n c ρ) hu)
      (le_sup_left (b := N k n c (ρ + 1)) (hcolN β))
  refine ⟨fun g => ⟨fun hg => ?_, ?_⟩, fun g => ⟨fun hg => hle hg, fun hg => hmid g hg⟩, hcol⟩
  · obtain ⟨u, hu, β, hg'⟩ := hcol g⁻¹ ((NFJ k n c ρ).inv_mem hg)
    refine ⟨(colE c (ρ + 1) β)⁻¹, (N k n c ρ).inv_mem (hcolN β), u⁻¹,
      (N k n c (ρ + 1)).inv_mem hu, ?_⟩
    rw [← _root_.mul_inv_rev, ← hg', inv_inv]
  · rintro ⟨x, hx, y, hy, rfl⟩
    exact (NFJ k n c ρ).mul_mem (le_sup_left (b := N k n c (ρ + 1)) hx)
      (le_sup_right (a := N k n c ρ) hy)

end GlobalTheory.RootEx.FJUnipotent
end

section

open GlobalTheory.SplitFlip

theorem _root_.GlobalTheory.T.flipGridPathAtSquare_split : ∀ {γ : List Edge} {i j : ℕ}, IsPath γ → PassesThrough i j γ → ∃ l₁ l₂ : List Edge, γ = l₁ ++ [Edge.theta i j, Edge.ex i j] ++ l₂ ∧ flipPath i j γ = l₁ ++ [Edge.ex i (j + 1), Edge.theta (i + 1) j] ++ l₂ := by
  first | exact @GlobalTheory.SplitFlip.flipPath_split | exact GlobalTheory.SplitFlip.flipPath_split | (intros; apply GlobalTheory.SplitFlip.flipPath_split <;> assumption)
end

section

open GlobalTheory.SplitFlip

theorem _root_.GlobalTheory.T.isSplitThetaGridPath_flipGridPathAtSquare : ∀ {γ : List Edge} {i j : ℕ}, IsPath γ → PassesThrough i j γ → IsPath (flipPath i j γ) := by
  first | exact @GlobalTheory.SplitFlip.isPath_flipPath | exact GlobalTheory.SplitFlip.isPath_flipPath | (intros; apply GlobalTheory.SplitFlip.isPath_flipPath <;> assumption)
end

section

open GlobalTheory.SplitFlip

theorem _root_.GlobalTheory.T.mem_gridPathInnerVertices_flipGridPathAtSquare : ∀ {γ : List Edge} {i j : ℕ}, IsPath γ → PassesThrough i j γ → ∀ X ∈ innerVertices (flipPath i j γ), X ≠ (i, j) ∧ (X ≠ (i + 1, j + 1) → X ∈ innerVertices γ) := by
  first | exact @GlobalTheory.SplitFlip.mem_innerVertices_flipPath | exact GlobalTheory.SplitFlip.mem_innerVertices_flipPath | (intros; apply GlobalTheory.SplitFlip.mem_innerVertices_flipPath <;> assumption)
end

section

open GlobalTheory.SplitFlip

theorem _root_.GlobalTheory.T.splitThetaGridPath_avoids_opposite_corner : ∀ {γ : List Edge} {i j : ℕ}, IsPath γ → PassesThrough i j γ → ∀ b ∈ γ, b.src ≠ (i + 1, j + 1) ∧ b.tgt ≠ (i + 1, j + 1) := by
  first | exact @GlobalTheory.SplitFlip.pathAvoid | exact GlobalTheory.SplitFlip.pathAvoid | (intros; apply GlobalTheory.SplitFlip.pathAvoid <;> assumption)
end

section

open MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL

theorem _root_.GlobalTheory.T.transpose_invariant_of_conj_invariant_distribution_GL : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : Type) [Fintype n] [DecidableEq n] (T : SB (GL n k) →ₗ[ℂ] ℂ), (∀ (g : GL n k) (φ ψ : SB (GL n k)), (∀ x, ψ.1 x = φ.1 (g * x * g⁻¹)) → T ψ = T φ) → ∀ φ ψ : SB (GL n k), (∀ x y : GL n k, y.val = x.val.transpose → ψ.1 x = φ.1 y) → T ψ = T φ := by
  first | exact @GlobalTheory.GelfandKazhdan.transpose_invariant | exact GlobalTheory.GelfandKazhdan.transpose_invariant | (intros; apply GlobalTheory.GelfandKazhdan.transpose_invariant <;> assumption)
end
