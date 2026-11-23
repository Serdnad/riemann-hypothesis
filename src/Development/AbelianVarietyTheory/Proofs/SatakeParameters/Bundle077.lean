module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle009
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle071
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ValuationRingModel
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle010
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle088
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Cobdry
public import Formalism.FormalGroupWitt.Statement
public import Formalism.SharpRestriction.GlobalSchurBounds.GL3Theta
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.FiniteResidueFieldPadicInt
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.RepresentationTheory.Basic
public import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle017
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle068
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NotDvdCondN
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle277
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
import Mathlib.RingTheory.MvPowerSeries.Rename
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
import Mathlib.Topology.Algebra.Nonarchimedean.Completion
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle044
import Formalism.FormalGroupWitt.FormalGroupWittProofs.Bundle001
import Formalism.FormalGroupWitt.FormalGroupWittProofs.SolveV

@[expose] public section

section

open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits

theorem _root_.GlobalTheory.T.atMostTwoThick_in_window_long_orbit : ∀ {R : Ranks} (H : Host R) (τ φ : R.GG), 4 * H.Lw < orderOf φ.2 → WindowTwo (fun i : ZMod (orderOf φ) => Thick H (letter τ φ i)) H.Lw := by
  first | exact @GlobalTheory.HTW.LongWindow.main | exact GlobalTheory.HTW.LongWindow.main | (intros; apply GlobalTheory.HTW.LongWindow.main <;> assumption)
end

section

open Formalism.BasicNotions Formalism.ConjugateSelfDual Formalism.MainNotions Formalism.MainNotions.N Polynomial NumberField IsDedekindDomain ReciprocityTheory.Gal GlobalTheory.StringRepresentationDecomposition

theorem _root_.GlobalTheory.T.valuation_ring_model : ValRingModel := by
  first | exact @GlobalTheory.ValRing.valRingModel | exact GlobalTheory.ValRing.valRingModel | (intros; apply GlobalTheory.ValRing.valRingModel <;> assumption)
end

section

noncomputable section

namespace GlobalTheory.ThBe0.Inhab

open MvPowerSeries Formalism.FG.InjVAux GlobalTheory.SubringSeries Formalism.MainNotions.GL3Theta Formalism.MainNotions.TaylorLogMetric GlobalTheory.ThBe0

variable {l : ℕ} [hl : Fact l.Prime] {κ : Type}

theorem coeff_logF_cases (n : ℕ) : (PowerSeries.coeff n (logF l) = 0 ∧ ∀ j, n ≠ l ^ (2 * j)) ∨
    ∃ j, n = l ^ (2 * j) := by
  by_cases h : ∃ j, n = l ^ (2 * j)
  · exact Or.inr h
  · push Not at h
    refine Or.inl ⟨?_, h⟩
    rw [logF, PowerSeries.coeff_mk]
    exact Finset.sum_eq_zero fun j _ => if_neg (h j)

theorem coeff_zero_logF : PowerSeries.coeff 0 (logF l) = 0 := by
  rcases coeff_logF_cases (l := l) 0 with h | ⟨j, h⟩
  · exact h.1
  · exact absurd h.symm (pow_ne_zero _ hl.out.ne_zero)

theorem cc_logF : PowerSeries.constantCoeff (logF l) = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_zero_logF]

theorem hasSubst_pair_padicComplex_of_constantCoeff_zero {x y : MvPowerSeries κ ℂ_[l]} (hx : constantCoeff x = 0) (hy : constantCoeff y = 0) :
    HasSubst (fun i : Fin 2 => if i = 0 then x else y) :=
  hasSubst_of_constantCoeff_zero fun i => by split_ifs <;> assumption

theorem subst_powerSeriesEvalTwoGroups {κ' : Type} {a : κ → MvPowerSeries κ' ℂ_[l]} (ha : HasSubst a)
    {x y : MvPowerSeries κ ℂ_[l]} (hx : constantCoeff x = 0) (hy : constantCoeff y = 0)
    (E : MvPowerSeries (Fin 2) ℂ_[l]) : subst a (at2 E x y) = at2 E (subst a x) (subst a y) := by
  rw [at2, at2, subst_comp_subst_apply (hasSubst_pair_padicComplex_of_constantCoeff_zero hx hy) ha]
  congr 1
  funext i
  split_ifs <;> rfl

theorem subst_psubst {κ' : Type} {a : κ → MvPowerSeries κ' ℂ_[l]} (ha : HasSubst a)
    {x : MvPowerSeries κ ℂ_[l]} (hx : constantCoeff x = 0) (f : PowerSeries ℂ_[l]) :
    subst a (f.subst x) = f.subst (subst a x) :=
  subst_comp_subst_apply (PowerSeries.HasSubst.of_constantCoeff_zero hx).const ha f

theorem cc_lg (k : κ) : constantCoeff (lg k : MvPowerSeries κ ℂ_[l]) = 0 :=
  PowerSeries.constantCoeff_subst_eq_zero (constantCoeff_X k) _ cc_logF

section Frob

variable {σ : ℂ_[l] →+* ℂ_[l]}

end Frob

end GlobalTheory.ThBe0.Inhab
end
end

section

noncomputable section

namespace GlobalTheory.ThBe0

open Formalism.MainNotions.GL3Theta IsLocalRing Polynomial

theorem exists_coe_eq_of_pow_eq_one (l : ℕ) [Fact l.Prime] (ζ : ℂ_[l]) (n : ℕ) (hn : 0 < n)
    (h : ζ ^ n = 1) : ∃ a : PadicAlgCl l, (a : ℂ_[l]) = ζ ∧ a ^ n = 1 := by
  have hs : (X ^ n - C 1 : (PadicAlgCl l)[X]).Splits := IsAlgClosed.splits _
  have hne : (X ^ n - C 1 : (PadicAlgCl l)[X]) ≠ 0 := X_pow_sub_C_ne_zero hn 1
  have hr : ((X ^ n - C 1 : (PadicAlgCl l)[X]).map (algebraMap (PadicAlgCl l) ℂ_[l])).IsRoot ζ := by
    simp [h]
  obtain ⟨a, ha⟩ := hs.mem_range_of_isRoot hne hr
  refine ⟨a, ha, (algebraMap (PadicAlgCl l) ℂ_[l]).injective ?_⟩
  rw [map_pow, ha, h, map_one]

theorem exists_gal_pow (l : ℕ) [Fact l.Prime] :
    ∃ g : PadicAlgCl l ≃ₐ[ℚ_[l]] PadicAlgCl l,
      ∀ (x : PadicAlgCl l) (m : ℕ), Nat.Coprime m l → x ^ m = 1 → g x = x ^ l := by
  have e : (ℤ_[l] ⧸ maximalIdeal ℤ_[l]) ≃+* ZMod l := PadicInt.residueField
  have hl : l.Prime := Fact.out
  have : NeZero l := ⟨hl.ne_zero⟩
  have hcard : Nat.card (ℤ_[l] ⧸ maximalIdeal ℤ_[l]) = l := by
    rw [Nat.card_congr e.toEquiv, Nat.card_zmod]
  obtain ⟨φ, hφ⟩ := GlobalTheory.MemLoc.exists_algEquiv_rootOfUnity_eq_pow ℤ_[l] ℚ_[l]
    (Finite.of_equiv _ e.symm.toEquiv) (PadicAlgCl l)
  rw [hcard] at hφ
  refine ⟨φ, fun x m hm hx => hφ x m (fun h => ?_) hx⟩
  rw [← PadicInt.ker_toZMod, RingHom.mem_ker, map_natCast, ZMod.natCast_eq_zero_iff] at h
  exact (hl.coprime_iff_not_dvd.1 hm.symm) h

theorem isFrob_of_rootOfUnity {l : ℕ} [Fact l.Prime] (σ : ℂ_[l] →+* ℂ_[l]) (hσ : ∀ x, ‖σ x‖ = ‖x‖)
    (hζ : ∀ (ζ : ℂ_[l]) (n : ℕ), 0 < n → Nat.Coprime n l → ζ ^ n = 1 → σ ζ = ζ ^ l) : IsFrob σ := by
  have hl : l.Prime := Fact.out
  have hl0 : (l : ℂ_[l]) ≠ 0 := Nat.cast_ne_zero.2 hl.ne_zero
  have hc : Continuous σ := (AddMonoidHomClass.isometry_of_norm σ hσ).continuous
  refine ⟨hσ, fun x hx => ?_⟩
  have hcl : IsClosed (Wp l : Set ℂ_[l]) := Subring.isClosed_topologicalClosure _
  have hA : ∀ x ∈ Subring.closure {ζ : ℂ_[l] | ∃ n : ℕ, 0 < n ∧ Nat.Coprime n l ∧ ζ ^ n = 1},
      ∃ y ∈ Wp l, σ x = x ^ l + (l : ℂ_[l]) * y := by
    intro x hx
    have hW : ∀ {x}, x ∈ Subring.closure
        {ζ : ℂ_[l] | ∃ n : ℕ, 0 < n ∧ Nat.Coprime n l ∧ ζ ^ n = 1} → x ∈ Wp l :=
      fun h => Subring.le_topologicalClosure _ h
    induction hx using Subring.closure_induction with
    | mem x hx =>
      obtain ⟨n, hn, hnl, h⟩ := hx
      exact ⟨0, zero_mem _, by simp [hζ x n hn hnl h]⟩
    | zero => exact ⟨0, zero_mem _, by simp [hl.ne_zero]⟩
    | one => exact ⟨0, zero_mem _, by simp⟩
    | add x y hx hy ihx ihy =>
      obtain ⟨a, ha, ea⟩ := ihx
      obtain ⟨b, hb, eb⟩ := ihy
      obtain ⟨r, hr⟩ := exists_add_pow_prime_eq hl (⟨x, hW hx⟩ : Wp l) ⟨y, hW hy⟩
      have hr' := congrArg Subtype.val hr
      push_cast at hr'
      refine ⟨a + b - x * y * r, sub_mem (add_mem ha hb)
        (mul_mem (mul_mem (hW hx) (hW hy)) r.2), ?_⟩
      rw [map_add (f := _), ea, eb, hr']
      ring
    | neg x hx ihx =>
      obtain ⟨a, ha, ea⟩ := ihx
      rcases hl.eq_two_or_odd' with h2 | ho
      · refine ⟨-a - x ^ l, sub_mem (neg_mem ha) (pow_mem (hW hx) _), ?_⟩
        have he : Even l := h2 ▸ even_two
        have h2' : (l : ℂ_[l]) = 2 := by exact_mod_cast h2
        rw [map_neg, ea, he.neg_pow]
        linear_combination (x ^ l) * h2'
      · refine ⟨-a, neg_mem ha, ?_⟩
        rw [map_neg, ea, ho.neg_pow]
        ring
    | mul x y hx hy ihx ihy =>
      obtain ⟨a, ha, ea⟩ := ihx
      obtain ⟨b, hb, eb⟩ := ihy
      refine ⟨a * y ^ l + x ^ l * b + l * (a * b), add_mem (add_mem (mul_mem ha (pow_mem (hW hy) _))
        (mul_mem (pow_mem (hW hx) _) hb)) (mul_mem (natCast_mem _ _) (mul_mem ha hb)), ?_⟩
      rw [map_mul, ea, eb, mul_pow]
      ring
  have hf : Continuous fun x : ℂ_[l] => (σ x - x ^ l) * (l : ℂ_[l])⁻¹ := by fun_prop
  have hx' : x ∈ (fun x : ℂ_[l] => (σ x - x ^ l) * (l : ℂ_[l])⁻¹) ⁻¹' (Wp l : Set ℂ_[l]) := by
    refine closure_minimal (fun z hz => ?_) (hcl.preimage hf) hx
    obtain ⟨y, hy, e⟩ := hA z hz
    have : (σ z - z ^ l) * (l : ℂ_[l])⁻¹ = y := by
      rw [e]; field_simp; ring
    simpa [this] using hy
  refine ⟨_, hx', ?_⟩
  field_simp
  ring

end GlobalTheory.ThBe0
end
end

section

noncomputable section

namespace GlobalTheory.BiextInhab

open MvPowerSeries Formalism.FG.SolveVAux

def laK (K : Type) [Field K] (l d : ℕ) (s : ZMod d) : MvPowerSeries (ZMod d) K :=
  fun n => ∑ e ∈ Finset.range ((n.sum fun _ k => k) + 1),
    if n = Finsupp.single (s - ((2 * e : ℕ) : ZMod d)) (l ^ (2 * e)) then ((l : K) ^ e)⁻¹ else 0

section Field

variable {K : Type} [Field K] {l d : ℕ}

open MvPowerSeries in
variable {K : Type} [Field K] {l d : ℕ} in
theorem _root_.GlobalTheory.BiextInhab.laK_idMod2 (hl : l.Prime) :
    _root_.Formalism.FG.IsIdMod2 (_root_.GlobalTheory.BiextInhab.laK K l d) := by
  refine ⟨fun j => ?_, fun j i => ?_⟩
  · show _root_.GlobalTheory.BiextInhab.laK K l d j 0 = 0
    unfold _root_.GlobalTheory.BiextInhab.laK
    refine Finset.sum_eq_zero fun e _ => if_neg fun h => ?_
    exact pow_ne_zero _ hl.ne_zero (Finsupp.single_eq_zero.mp h.symm)
  · show _root_.GlobalTheory.BiextInhab.laK K l d j (Finsupp.single i 1) = _
    unfold _root_.GlobalTheory.BiextInhab.laK
    rw [Finset.sum_eq_single 0]
    · simp [Finsupp.single_left_inj one_ne_zero]
    · intro e _ he
      refine if_neg fun h => he ?_
      have h1 := congrArg (fun f : ZMod d →₀ ℕ => f.sum fun _ k => k) h
      simp only [Finsupp.sum_single_index] at h1
      rcases Nat.pow_eq_one.mp h1.symm with h2 | h2
      · exact absurd h2 hl.ne_one
      · omega
    · intro h
      simp at h

variable [NeZero d]

end Field

section Padic

open Formalism.G

variable {l : ℕ} [hl : Fact l.Prime] {d : ℕ} {τ : Type}

variable [NeZero d]

end Padic

section Main

open GlobalTheory.ThStr Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.GL3Theta

variable {l : ℕ} [hl : Fact l.Prime] {d : ℕ}

def serW (l : ℕ) [Fact l.Prime] (κ : Type) : Subring (MvPowerSeries κ ℂ_[l]) :=
  (MvPowerSeries.map (σ := κ) (Wp l).subtype).range

open MvPowerSeries in
variable {l : ℕ} [hl : Fact l.Prime] {d : ℕ} in
theorem _root_.GlobalTheory.BiextInhab.mem_serW {κ : Type} {F : MvPowerSeries κ ℂ_[l]} :
    F ∈ _root_.GlobalTheory.BiextInhab.serW l κ ↔ _root_.Formalism.MainNotions.GL3Theta.IntegralW F := by
  constructor
  · rintro ⟨G, rfl⟩ n
    exact (coeff n G).2
  · intro h
    exact ⟨fun n => ⟨coeff n F, h n⟩, by ext n; rfl⟩

variable [NeZero d]




open MvPowerSeries in
variable {l : ℕ} [hl : Fact l.Prime] {d : ℕ} in
variable [NeZero d] in
private theorem coeff_mapDomain_rename_of_injective {σ τ R : Type} [CommSemiring R] (f : σ → τ)
    [Filter.TendstoCofinite f] (hf : Function.Injective f) (p : MvPowerSeries σ R)
    (n : σ →₀ ℕ) : coeff (Finsupp.mapDomain f n) (rename f p) = coeff n p := by
  rw [coeff_rename, Finset.sum_eq_single n]
  · intro y hy hne
    simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hy
    exact absurd (Finsupp.mapDomain_injective hf hy) hne
  · intro hn
    exact absurd (by simp) hn


open MvPowerSeries in
variable {l : ℕ} [hl : Fact l.Prime] {d : ℕ} in
variable [NeZero d] in
theorem _root_.GlobalTheory.BiextInhab.bridge (l : ℕ) [Fact l.Prime] (d : ℕ) [NeZero d]
    {β : Type} (b : β) (s : ZMod d) :
    _root_.GlobalTheory.ThStr.laAt (l := l) (fun r : ZMod d => (r, b)) s =
      _root_.Formalism.BasicNotions.jetLogG l d (s, b) := by
  have hinj : Function.Injective (fun r : ZMod d => (r, b)) := fun x y h => (Prod.mk.inj h).1
  have hren : _root_.GlobalTheory.ThStr.laAt (l := l) (fun r : ZMod d => (r, b)) s =
      rename (fun r : ZMod d => (r, b)) (_root_.GlobalTheory.ThStr.laS l d s) := by
    rw [rename_eq_subst]
    rfl
  have hsingle : ∀ e : ℕ, (Finsupp.single (s - 2 * (e : ZMod d), b) ((l ^ 2) ^ e) :
      ZMod d × β →₀ ℕ) = Finsupp.mapDomain (fun r : ZMod d => (r, b))
        (Finsupp.single (s - ((2 * e : ℕ) : ZMod d)) (l ^ (2 * e))) := by
    intro e
    rw [Finsupp.mapDomain_single, pow_mul]
    push_cast
    rfl
  rw [hren]
  ext m
  by_cases hm : m ∈ Set.range (Finsupp.mapDomain (fun r : ZMod d => (r, b)))
  · obtain ⟨n, rfl⟩ := hm
    have hdeg : _root_.Formalism.BasicNotions.JetTdeg (Finsupp.mapDomain (fun r : ZMod d => (r, b)) n) =
        n.sum fun _ k => k := by
      unfold _root_.Formalism.BasicNotions.JetTdeg
      exact Finsupp.sum_mapDomain_index (fun _ => rfl) (fun _ _ _ => rfl)
    rw [coeff_mapDomain_rename_of_injective _ hinj]
    show _root_.GlobalTheory.ThStr.laS l d s n =
      _root_.Formalism.BasicNotions.jetLogG l d (s, b) (Finsupp.mapDomain (fun r : ZMod d => (r, b)) n)
    unfold _root_.GlobalTheory.ThStr.laS _root_.Formalism.BasicNotions.jetLogG
    dsimp only
    rw [hdeg]
    refine Finset.sum_congr rfl fun e _ => ?_
    simp only [hsingle e, (Finsupp.mapDomain_injective hinj).eq_iff]
  · rw [coeff_rename_eq_zero _ _ hm]
    show (0 : ℂ_[l]) = _root_.Formalism.BasicNotions.jetLogG l d (s, b) m
    unfold _root_.Formalism.BasicNotions.jetLogG
    dsimp only
    symm
    refine Finset.sum_eq_zero fun e _ => if_neg ?_
    rintro rfl
    exact hm ⟨_, (hsingle e).symm⟩

end Main

end GlobalTheory.BiextInhab
end
end

section

open GlobalTheory.LatHecke

namespace GlobalTheory.LatHecke

theorem satake_bound_of_isometric_spherical : ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Finite (IsLocalRing.ResidueField O)] [Field K] [Algebra O K] [IsFractionRing O K] (r : ℕ) (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] (ρ : Representation ℂ (GL (Fin r) K) V) (v : V) (α : Multiset ℂ), α.card = r → (∀ g x, ‖ρ g x‖ = ‖x‖) → v ≠ 0 → (∀ g, glMap g (std O K r).1 = (std O K r).1 → ρ g v = v) → (∀ k ≤ r, ∀ s : Finset (GL (Fin r) K), Set.BijOn (fun g => glMap g (std O K r).1) s (Subtype.val '' subElem k (std O K r)) → ∑ g ∈ s, ρ g v = ((((qRes O : ℝ) ^ ((k : ℝ) * ((r : ℝ) - k) / 2) : ℝ) : ℂ) * α.esymm k) • v) → ∀ a ∈ α, ‖a‖ ≤ (qRes O : ℝ) ^ (((r : ℝ) - 1) / 2) := by
  intro O K _ _ _ _ _ _ _ r V _ _ ρ v α hcard hnorm hv hinv heig
  classical
  have hmul : ∀ (a b : GL (Fin r) K) (x : V), ρ (a * b) x = ρ a (ρ b x) := fun a b x => by
    rw [map_mul]; rfl
  have hone : ∀ x : V, ρ 1 x = x := fun x => by
    rw [map_one]; rfl
  choose γ hγ using (GlobalTheory.T.generalLinear_transitive_on_lattices_over_DVR O K r).1
  have hγ' : ∀ L : Lat O K r, γ L • std O K r = L := fun L => Subtype.ext (hγ L)
  let φ : Lat O K r → V := fun L => ρ (γ L) v

  have hφ : ∀ g : GL (Fin r) K, φ (g • std O K r) = ρ g v := by
    intro g
    have hfix : ((γ (g • std O K r))⁻¹ * g) • std O K r = std O K r := by
      rw [mul_smul, inv_smul_eq_iff, hγ']
    have h1 : ρ ((γ (g • std O K r))⁻¹ * g) v = v :=
      hinv _ (congrArg Subtype.val hfix)
    have h2 : ρ g v = ρ (γ (g • std O K r) * ((γ (g • std O K r))⁻¹ * g)) v := by
      rw [mul_inv_cancel_left]
    change ρ (γ (g • std O K r)) v = ρ g v
    rw [h2, hmul, h1]
  have hφg : ∀ (g : GL (Fin r) K) (M : Lat O K r), φ (g • M) = ρ g (φ M) := by
    intro g M
    have h1 : g • M = (g * γ M) • std O K r := by rw [mul_smul, hγ']
    rw [h1, hφ, hmul]
  have hstd : φ (std O K r) = v := by
    have := hφ 1
    rwa [one_smul, hone] at this
  refine GlobalTheory.T.satakeParameters_bounded_lattice_eigenfunction O K r V φ α ‖v‖ hcard ?_ ?_ ?_
  · intro h
    exact hv (by rw [← hstd, h]; rfl)
  · intro L
    exact (hnorm _ _).le
  · intro k hk L

    have h0 : heckeElem k φ (std O K r)
        = ((((qRes O : ℝ) ^ ((k : ℝ) * ((r : ℝ) - k) / 2) : ℝ) : ℂ) * α.esymm k) • v := by
      rw [heckeElem_eq_sum, ← heig k hk ((subElem_finite k (std O K r)).toFinset.image γ)]
      · rw [Finset.sum_image]
        intro M _ M' _ h
        rw [← hγ' M, ← hγ' M', h]
      · refine ⟨?_, ?_, ?_⟩
        · intro g hg
          obtain ⟨M, hM, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hg)
          exact ⟨M, (Set.Finite.mem_toFinset _).1 hM, (hγ M).symm⟩
        · intro g hg g' hg' h
          obtain ⟨M, hM, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hg)
          obtain ⟨M', hM', rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hg')
          have h' : M = M' := Subtype.ext (by simpa only [hγ] using h)
          rw [h']
        · rintro _ ⟨M, hM, rfl⟩
          exact ⟨γ M, Finset.mem_coe.2 (Finset.mem_image.2
            ⟨M, (Set.Finite.mem_toFinset _).2 hM, rfl⟩), hγ M⟩

    have h1 : heckeElem k φ L = ρ (γ L) (heckeElem k φ (std O K r)) := by
      conv_lhs => rw [← hγ' L]

      rw [heckeElem_smul, heckeElem_eq_sum, heckeElem_eq_sum, map_sum]
      exact Finset.sum_congr rfl fun M _ => hφg _ _
    rw [h1, h0, map_smul]
end GlobalTheory.LatHecke
end

section

open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW.Rec

theorem existsUnique_over : ∀ {l : ℕ} [Fact l.Prime] (P : LocPrime l) (K LL : FinExt l) (W : Wach P K LL),
    K.1 ≤ MaximalUnramifiedExtension l → ∀ a, ∃! τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1, Over W τ a := by
  intro l _ P K LL W hK a
  have hle : K.1 ≤ K0 K := le_inf le_rfl hK
  have hsurj : Function.Surjective (IsScalarTower.toAlgHom ℚ_[l] ↥(K0 K) ↥K.1) := by
    intro x
    exact ⟨⟨x.1, hle x.2⟩, Subtype.ext rfl⟩
  let e : ↥(K0 K) ≃ₐ[ℚ_[l]] ↥K.1 :=
    AlgEquiv.ofBijective (IsScalarTower.toAlgHom ℚ_[l] ↥(K0 K) ↥K.1)
      ⟨(IsScalarTower.toAlgHom ℚ_[l] ↥(K0 K) ↥K.1).toRingHom.injective, hsurj⟩
  refine ⟨(W.emb a).comp e.symm.toAlgHom, ?_, ?_⟩
  · show ((W.emb a).comp e.symm.toAlgHom).comp (IsScalarTower.toAlgHom ℚ_[l] ↥(K0 K) ↥K.1) = W.emb a
    ext x
    have : e.symm ((IsScalarTower.toAlgHom ℚ_[l] ↥(K0 K) ↥K.1) x) = x := e.symm_apply_apply x
    simp only [AlgHom.comp_apply]
    exact congrArg (fun z => ((W.emb a z : ↥LL.1) : Om l)) this
  · intro τ hτ
    have hτ' : τ.comp (IsScalarTower.toAlgHom ℚ_[l] ↥(K0 K) ↥K.1) = W.emb a := hτ
    ext x
    obtain ⟨y, rfl⟩ := hsurj x
    have h1 : e.symm ((IsScalarTower.toAlgHom ℚ_[l] ↥(K0 K) ↥K.1) y) = y := e.symm_apply_apply y
    have h2 := congrArg (fun f => f y) hτ'
    simp only [AlgHom.comp_apply] at h2 ⊢
    rw [h2]
    exact congrArg (fun z => ((W.emb a z : ↥LL.1) : Om l)) h1.symm

end GlobalTheory.HTW.Rec
end

section

open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW.Rec

theorem enl_locChi_epsU : ∀ {D : D7} (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (C : Enl D i w hw), (∀ z : ℚ_[D.nd.l i], C.inc (algebraMap _ _ z) = algebraMap _ _ z) → ∀ s, C.inc ((Br.locChi D.nbr i w hw (epsU D.nd i) s : (Br.LL D.nbr i w hw)ˣ) : Br.LL D.nbr i w hw) = ((cycLL (Br.PD D.loc D.nbr i w hw) ↥C.LL.1 s : (↥C.LL.1)ˣ) : ↥C.LL.1) := by
  intro D i w hw C hC s
  rw [GlobalTheory.CycBridge.locChi_epsU D i w hw s]
  exact hC _

end GlobalTheory.HTW.Rec
end
