module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle002
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsLocalRingOfIdem
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle306
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.AdeleLC
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToBidualNaturalityDualSheafTranspose
public import Development.AbelianVarietyTheory.Definitions.Divisors.TorsTransport
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsEqOfNatCastMulMem
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1172
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle776
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle786
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle781
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle783
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsEffAddNsmulDiv
import Development.AbelianVarietyTheory.Definitions.Divisors.ToNatLengthEqRangeAddRange

@[expose] public section

section

open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT
open scoped Classical

noncomputable section

namespace GlobalTheory.LatTransfer

open GlobalTheory.UnitLemma

theorem avg_of_const {H : Type} [Group H] (u : H → ℂ) (c : ℂ) (hu : ∀ h, u h = c) : avg u = c := by
  have hs : rStab u = ⊤ := by
    rw [Subgroup.eq_top_iff']
    intro k x
    rw [hu, hu]
  have hi : (rStab u).index = 1 := by rw [hs, Subgroup.index_top]
  have hc : Nat.card (H ⧸ rStab u) = 1 := hi
  obtain ⟨x0, hx0⟩ := Nat.card_eq_one_iff_exists.1 hc
  unfold avg
  rw [hi, finsum_eq_single _ x0 (fun y hy => absurd (hx0 y) hy), hu]
  simp

theorem mulLat_eq_self_iff {O A : Type} [CommRing O] [CommRing A] [Algebra O A] (u : Aˣ)
    (L : Submodule O A) : mulLat O (u : A) L = L ↔ u ∈ stabLat O L := by
  constructor
  · intro h
    show ∀ y, y ∈ L ↔ (u : A) * y ∈ L
    intro y
    have := Orbit.mem_mulLat u L ((u : A) * y)
    rw [h, Units.inv_mul_cancel_left] at this
    exact this.symm
  · intro hu
    ext y
    rw [Orbit.mem_mulLat]
    have := hu (((u⁻¹ : Aˣ) : A) * y)
    rw [Units.mul_inv_cancel_left] at this
    exact this

theorem mulLat_mul {O A : Type} [CommRing O] [CommRing A] [Algebra O A] (s t : Aˣ)
    (L : Submodule O A) : mulLat O ((s * t : Aˣ) : A) L = mulLat O (s : A) (mulLat O (t : A) L) := by
  ext y
  rw [Orbit.mem_mulLat, Orbit.mem_mulLat, Orbit.mem_mulLat, _root_.mul_inv_rev, Units.val_mul, mul_assoc]

theorem cast_finsum {α : Type*} (u : α → ℚ) : ((∑ᶠ a, u a : ℚ) : ℂ) = ∑ᶠ a, ((u a : ℚ) : ℂ) := by
  by_cases h : (Function.support u).Finite
  · exact map_finsum (Rat.castHom ℂ) h
  · have e : Function.support (fun a => ((u a : ℚ) : ℂ)) = Function.support u :=
      Function.support_comp_eq (fun r : ℚ => (r : ℂ)) (fun {x} => Rat.cast_eq_zero) u
    have h' : ¬ (Function.support fun a => ((u a : ℚ) : ℂ)).Finite := by rw [e]; exact h
    rw [finsum_of_infinite_support h, finsum_of_infinite_support h', Rat.cast_zero]

theorem twCent_left {G : Type} [Group G] (θ : G →* G) (δ : G) {t : G} (ht : t ∈ twCent θ δ) (k y : G) :
    (t * y * k)⁻¹ * δ * θ (t * y * k) = k⁻¹ * (y⁻¹ * δ * θ y) * θ k := by
  have h : t * δ = δ * θ t := ht
  have h2 : t⁻¹ * δ * θ t = δ := by rw [mul_assoc, ← h]; group
  calc (t * y * k)⁻¹ * δ * θ (t * y * k) = k⁻¹ * (y⁻¹ * (t⁻¹ * δ * θ t) * θ y) * θ k := by
        simp only [map_mul]; group
    _ = _ := by rw [h2]

theorem twOrb_eq_N : ∀ (K : GlobalTheory.UnitLemma.UQ) (B : GlobalTheory.UnitLemma.InvAlg K) (x : B.A) (G : Type) [Group G] [TopologicalSpace G] (θ : G →* G) (Kg : Subgroup G) (δ : G) (f : G → ℂ) (φ : twCent θ δ ≃* B.T) (Λ : G → Submodule K.O B.A), (∀ k ∈ Kg, ∀ y, f (k⁻¹ * y * θ k) = f y) → (∀ y, f y = 0 ∨ f y = 1) → (∀ t : twCent θ δ, ((t : G) ∈ cptPart (twCent θ δ) ↔ (((φ t : B.T) : B.Aˣ)) ∈ GlobalTheory.UnitLemma.intUnits K.O B.A)) → (∀ q q' : G, Λ q = Λ q' ↔ q⁻¹ * q' ∈ Kg) → (∀ (t : twCent θ δ) (q : G), Λ ((t : G) * q) = GlobalTheory.UnitLemma.mulLat K.O ((((φ t : B.T) : B.Aˣ)) : B.A) (Λ q)) → (∀ q, Λ q ∈ B.X x ↔ f (q⁻¹ * δ * θ q) = 1) → (∀ L ∈ B.X x, ∃ q, Λ q = L) → twOrb θ Kg δ f = ((B.N x : ℚ) : ℂ) := by
  intro K B x G _ _ θ Kg δ f φ Λ hf h01 hcpt hΛK hΛT hΛX hsurj

  have havg : ∀ q : G, avg (fun k : Kg => f ((q * k)⁻¹ * δ * θ (q * k))) = f (q⁻¹ * δ * θ q) := by
    intro q
    refine avg_of_const _ _ fun k => ?_
    rw [← hf k k.2 (q⁻¹ * δ * θ q)]
    congr 1
    simp only [map_mul]
    group

  let ψ : twCent θ δ →* B.Aˣ := B.T.subtype.comp φ.toMonoidHom
  have hψ : ∀ t, ψ t = ((φ t : B.T) : B.Aˣ) := fun t => rfl
  have hle : cptPart (twCent θ δ) ≤ twCent θ δ := by
    unfold cptPart
    rw [Subgroup.closure_le]
    exact fun t ht => ht.1
  have hidx : ∀ q : G, (twCent θ δ ⊓ Kg.map (MulAut.conj q).toMonoidHom).relIndex (cptPart (twCent θ δ)) =
      (stabLat K.O (Λ q) ⊓ B.T).relIndex (intUnits K.O B.A ⊓ B.T) := by
    intro q
    rw [← Subgroup.relIndex_subgroupOf hle]
    have e1 : (twCent θ δ ⊓ Kg.map (MulAut.conj q).toMonoidHom).subgroupOf (twCent θ δ) =
        (stabLat K.O (Λ q) ⊓ B.T).comap ψ := by
      ext t
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_comap, Subgroup.mem_inf, Subgroup.mem_inf, hψ]
      simp only [t.2, (φ t).2, true_and, and_true]
      rw [← mulLat_eq_self_iff, ← hΛT, eq_comm, hΛK, Subgroup.mem_map]
      constructor
      · rintro ⟨k, hk, hkt⟩
        have : (t : G) = q * k * q⁻¹ := by rw [← hkt]; rfl
        rw [this]
        simpa [mul_assoc] using hk
      · intro h
        refine ⟨q⁻¹ * (t * q), h, ?_⟩
        show q * (q⁻¹ * (t * q)) * q⁻¹ = t
        group
    have e2 : (cptPart (twCent θ δ)).subgroupOf (twCent θ δ) = (intUnits K.O B.A ⊓ B.T).comap ψ := by
      ext t
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_comap, Subgroup.mem_inf, hψ, hcpt t]
      simp only [(φ t).2, and_true]
    rw [e1, e2, Subgroup.relIndex_comap, Subgroup.map_comap_eq_self]
    intro y hy
    exact ⟨φ.symm ⟨y, hy.2⟩, by rw [hψ]; simp⟩

  have hdc : ∀ t ∈ twCent θ δ, ∀ k ∈ Kg, ∀ q : G, f ((t * q * k)⁻¹ * δ * θ (t * q * k)) = f (q⁻¹ * δ * θ q) := by
    intro t ht k hk q
    rw [twCent_left θ δ ht k q, hf k hk]
  let r : B.X x → B.X x → Prop := fun L M => ∃ t ∈ B.T, (M : Submodule K.O B.A) = mulLat K.O (t : B.A) L
  have hr : Equivalence r := by
    refine ⟨fun L => ⟨1, B.T.one_mem, ((mulLat_eq_self_iff 1 L.1).2 (stabLat K.O L.1).one_mem).symm⟩, ?_, ?_⟩
    · rintro L M ⟨t, ht, h⟩
      refine ⟨t⁻¹, B.T.inv_mem ht, ?_⟩
      rw [h, ← mulLat_mul, inv_mul_cancel]
      exact ((mulLat_eq_self_iff 1 L.1).2 (stabLat K.O L.1).one_mem).symm
    · rintro L M N ⟨t, ht, h⟩ ⟨s, hs, h'⟩
      exact ⟨s * t, B.T.mul_mem hs ht, by rw [h', h, mulLat_mul]⟩
  let S := {d : DoubleCoset.Quotient (twCent θ δ : Set G) (Kg : Set G) //
    f ((Quotient.out d)⁻¹ * δ * θ (Quotient.out d)) = 1}
  let g : S → Orb K.O B.T (B.X x) := fun d => Quot.mk r ⟨Λ (Quotient.out d.1), (hΛX _).2 d.2⟩
  have hg_surj : Function.Surjective g := by
    intro o
    induction o using Quot.ind with
    | mk L =>
      obtain ⟨q, hq⟩ := hsurj L.1 L.2
      obtain ⟨t, ht, k, hk, hout⟩ := DoubleCoset.mk_out_eq_mul (twCent θ δ) Kg q
      have hf1 : f ((Quotient.out (DoubleCoset.mk (twCent θ δ) Kg q))⁻¹ * δ *
          θ (Quotient.out (DoubleCoset.mk (twCent θ δ) Kg q))) = 1 := by
        rw [hout, hdc t ht k hk q]
        exact (hΛX q).1 (hq ▸ L.2)
      refine ⟨⟨DoubleCoset.mk (twCent θ δ) Kg q, hf1⟩, ?_⟩
      refine (Quot.sound ?_).symm
      refine ⟨((φ ⟨t, ht⟩ : B.T) : B.Aˣ), (φ ⟨t, ht⟩).2, ?_⟩
      show Λ (Quotient.out (DoubleCoset.mk (twCent θ δ) Kg q)) = _
      rw [hout, ← hq, ← hΛT ⟨t, ht⟩ q]
      refine ((hΛK _ _).2 ?_).symm
      simpa [mul_assoc] using hk
  have hg_inj : Function.Injective g := by
    rintro ⟨d1, h1⟩ ⟨d2, h2⟩ h
    obtain ⟨s, hs, hs'⟩ := hr.eqvGen_iff.1 (Quot.eqvGen_exact h)
    apply Subtype.ext
    let t : twCent θ δ := φ.symm ⟨s, hs⟩
    have hts : ((φ t : B.T) : B.Aˣ) = s := by simp [t]
    have h3 : Λ ((t : G) * Quotient.out d1) = Λ (Quotient.out d2) := by
      rw [hΛT, hts]
      exact hs'.symm
    have := (@DoubleCoset.eq _ _ (twCent θ δ) Kg (Quotient.out d1) (Quotient.out d2)).2
      ⟨t, t.2, (t * Quotient.out d1)⁻¹ * Quotient.out d2, (hΛK _ _).1 h3, by group⟩
    rwa [DoubleCoset.out_eq', DoubleCoset.out_eq'] at this
  let e := Equiv.ofBijective g ⟨hg_inj, hg_surj⟩
  have hN : ((B.N x : ℚ) : ℂ) = ∑ᶠ o : Orb K.O B.T (B.X x), ((Orbit.orbWt B.T (B.X x) o : ℚ) : ℂ) := by
    unfold InvAlg.N
    rw [Orbit.orbSum_eq, cast_finsum]
  rw [hN, ← finsum_comp_equiv e]
  have hw : ∀ s : S, ((Orbit.orbWt B.T (B.X x) (e s) : ℚ) : ℂ) =
      (((stabLat K.O (Λ (Quotient.out s.1)) ⊓ B.T).relIndex (intUnits K.O B.A ⊓ B.T) : ℕ) : ℂ) := by
    intro s
    exact Rat.cast_natCast _
  rw [finsum_congr hw]
  unfold twOrb
  have hsub : (∑ᶠ s : S, (((stabLat K.O (Λ (Quotient.out s.1)) ⊓ B.T).relIndex (intUnits K.O B.A ⊓ B.T) : ℕ) : ℂ)) =
      ∑ᶠ (d : DoubleCoset.Quotient (twCent θ δ : Set G) (Kg : Set G))
        (_ : f ((Quotient.out d)⁻¹ * δ * θ (Quotient.out d)) = 1),
        (((stabLat K.O (Λ (Quotient.out d)) ⊓ B.T).relIndex (intUnits K.O B.A ⊓ B.T) : ℕ) : ℂ) :=
    finsum_subtype_eq_finsum_cond (f := fun d : DoubleCoset.Quotient (twCent θ δ : Set G) (Kg : Set G) =>
      (((stabLat K.O (Λ (Quotient.out d)) ⊓ B.T).relIndex (intUnits K.O B.A ⊓ B.T) : ℕ) : ℂ)) _
  rw [hsub]
  refine finsum_congr fun d => ?_
  rw [havg, hidx, finsum_eq_if]
  rcases h01 ((Quotient.out d)⁻¹ * δ * θ (Quotient.out d)) with h | h
  · rw [h, mul_zero, if_neg (by norm_num)]
  · rw [h, mul_one, if_pos rfl]

end GlobalTheory.LatTransfer
end
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT
open scoped Classical TensorProduct Pointwise

namespace GlobalTheory.LocFinU

theorem relIndex_ne_zero_of_subset_cpt {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (U P : Subgroup G) (hU : IsOpen (U : Set G)) (Ω : Set G) (hΩ : IsCompact Ω) (hP : (P : Set G) ⊆ Ω) :
    U.relIndex P ≠ 0 := by
  obtain ⟨s, hs⟩ := hΩ.elim_finite_subcover (fun g : Ω => (g : G) • (U : Set G)) (fun g => hU.smul _)
    (fun x hx => Set.mem_iUnion.2 ⟨⟨x, hx⟩, ⟨1, U.one_mem, mul_one x⟩⟩)
  have hmem : ∀ q : P ⧸ U.subgroupOf P, ∃ i : s, ((Quotient.out q : P) : G) ∈ ((i : Ω) : G) • (U : Set G) := by
    intro q
    have := hs (hP (Quotient.out q).2)
    simp only [Set.mem_iUnion] at this
    obtain ⟨i, hi, h⟩ := this
    exact ⟨⟨i, hi⟩, h⟩
  choose f hf using hmem
  have hinj : Function.Injective f := by
    intro q q' h
    have h1 := hf q
    have h2 := hf q'
    rw [h] at h1
    obtain ⟨u, hu, hu'⟩ := h1
    obtain ⟨u', hu2, hu2'⟩ := h2
    rw [← Quotient.out_eq q, ← Quotient.out_eq q']
    change QuotientGroup.mk _ = QuotientGroup.mk _
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [← hu', ← hu2']
    simp only [smul_eq_mul, _root_.mul_inv_rev, mul_assoc, inv_mul_cancel_left]
    exact U.mul_mem (U.inv_mem hu) hu2
  haveI : Finite (P ⧸ U.subgroupOf P) := Finite.of_injective f hinj
  exact Subgroup.index_ne_zero_of_finite

end GlobalTheory.LocFinU

namespace GlobalTheory.LocFinU

theorem continuous_cj {E : Type} [Field E] [NumberField E] [IsCMField E] (w : Pl E) : Continuous (cj w) := by
  unfold cj
  split_ifs with h
  · exact h.choose_spec.1
  · exact continuous_id

theorem isClosed_UL {E : Type} [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : Pl E) :
    IsClosed (UL n w : Set (GLw n w)) := by
  unfold UL
  split_ifs
  · exact isClosed_univ
  · have hc : Continuous fun g : GLw n w => cT (cj w) (g : Matrix (Fin n) (Fin n) _) * 1 * (g : Matrix (Fin n) (Fin n) _) :=
      ((Units.continuous_val.matrix_map (continuous_cj w)).matrix_transpose.matrix_mul continuous_const).matrix_mul
        Units.continuous_val
    exact isClosed_eq hc continuous_const

theorem isCompact_KL {E : Type} [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : Pl E) :
    IsCompact (KL n w : Set (UL n w)) := by
  rw [Subtype.isCompact_iff]
  have hK : IsCompact (GlobalTheory.LFun.KGL w (n := n) : Set (GLw n w)) :=
    GlobalTheory.LFun.IntPtsUnitary.isCompact_GLint _ (PI.AdicCompletionValuation.isCompact_adicCompletionIntegers E w)
  have : (Subtype.val '' (KL n w : Set (UL n w))) = (GlobalTheory.LFun.KGL w (n := n) : Set (GLw n w)) ∩ (UL n w : Set (GLw n w)) := by
    ext g
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨hx, x.2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨⟨g, h2⟩, h1, rfl⟩
  rw [this]
  exact hK.inter_right (isClosed_UL n w)

end GlobalTheory.LocFinU

namespace GlobalTheory.LocFinU

theorem cptPart_subset_of_comm {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    (T : Subgroup G) (hc : ∀ a ∈ T, ∀ b ∈ T, a * b = b * a) :
    (cptPart T : Set G) ⊆ {t | t ∈ T ∧ IsCompact (closure (Subgroup.zpowers t : Set G))} := by
  intro x hx
  induction hx using Subgroup.closure_induction with
  | mem x hx => exact hx
  | one =>
    refine ⟨T.one_mem, ?_⟩
    rw [Subgroup.zpowers_one_eq_bot, Subgroup.coe_bot, closure_singleton]
    exact isCompact_singleton
  | mul x y _ _ hx hy =>
    refine ⟨T.mul_mem hx.1 hy.1, ?_⟩
    have hxy : Commute x y := hc x hx.1 y hy.1
    have hcp : IsCompact (closure (Subgroup.zpowers x : Set G) * closure (Subgroup.zpowers y : Set G)) :=
      hx.2.mul hy.2
    refine hcp.of_isClosed_subset isClosed_closure (closure_minimal ?_ hcp.isClosed)
    rintro _ ⟨k, rfl⟩
    exact ⟨x ^ k, subset_closure ⟨k, rfl⟩, y ^ k, subset_closure ⟨k, rfl⟩, (hxy.mul_zpow k).symm⟩
  | inv x _ hx =>
    refine ⟨T.inv_mem hx.1, ?_⟩
    rw [Subgroup.zpowers_inv]
    exact hx.2

end GlobalTheory.LocFinU
end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Vert GlobalTheory.Vert.Model GlobalTheory.VB
open GlobalTheory.QCoh (pullbackSections res_pullbackSections pullbackSections_res
  pullback_map_app_pullbackSections)
open GlobalTheory.Twist (resM resM_resM app_resM)

namespace GlobalTheory.Vert.DivPull

section Sections

variable {X Y Y' W : Scheme.{0}}

theorem pullbackComp_inv_app (b : W ⟶ Y) (a : Y ⟶ X) (E : X.Modules) {U : X.Opens} {V : Y.Opens}
    {T : W.Opens} (h₁ : V ≤ a ⁻¹ᵁ U) (h₂ : T ≤ b ⁻¹ᵁ V) (h : T ≤ (b ≫ a) ⁻¹ᵁ U) (s : Γ(E, U)) :
    ((Scheme.Modules.pullbackComp b a).inv.app E).app T (pullbackSections (b ≫ a) E h s) =
      pullbackSections b _ h₂ (pullbackSections a E h₁ s) := by
  have e := unit_conjugateEquiv ((Scheme.Modules.pullbackPushforwardAdjunction a).comp
    (Scheme.Modules.pullbackPushforwardAdjunction b))
    (Scheme.Modules.pullbackPushforwardAdjunction (b ≫ a)) (Scheme.Modules.pullbackComp b a).inv E
  rw [Scheme.Modules.conjugateEquiv_pullbackComp_inv, Adjunction.comp_unit_app] at e
  refine (app_resM _ h _).trans (Eq.trans ?_ (pullbackSections_res b _ h₂ h₁ _).symm)
  exact congrArg (resM _ h) congr(($e).app U s).symm

theorem detUnit_congr {F : X.Modules} {r : ℕ} {U U' T T' V : X.Opens} {e : Fin r → Γ(F, U)}
    {e' : Fin r → Γ(F, U')} {d : Fin r → Γ(F, T)} {d' : Fin r → Γ(F, T')} (he : IsFrame e)
    (he' : IsFrame e') (hd : IsFrame d) (hd' : IsFrame d') (h : V ≤ U) (h' : V ≤ U') (k : V ≤ T)
    (k' : V ≤ T') (H : ∀ i, resM F h (e i) = resM F k (d i))
    (H' : ∀ i, resM F h' (e' i) = resM F k' (d' i)) :
    he.detUnit he' h h' = hd.detUnit hd' k k' := by
  have e₁ : he.basis h = hd.basis k :=
    DFunLike.ext _ _ fun i => by simp only [IsFrame.basis_apply, H]
  refine Units.ext ?_
  simp only [IsFrame.val_detUnit, e₁, H']

end Sections

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {Z Z₁ : Model O}
  {f : Z₁.X ⟶ Z.X} (hf : f ≫ Z.str = Z₁.str) {E E' : Z.X.Modules} {r : ℕ}

end GlobalTheory.Vert.DivPull
end
end

section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.LatVal
open scoped nonZeroDivisors

noncomputable section

namespace GlobalTheory.LatVal

open Neutral.B1

theorem exists_uniformisation_torsTransport {K : Type} [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K]
    (h2 : Module.finrank ℚ K = 2) (ι : K →+* ℂ) (Λ₀ : PeriodPair) (Ω₀ : ℂ)
    (hΛ : GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport.IsLatOf ι 1 Λ₀) (hΩ : Ω₀ ≠ 0) :
    letI : Algebra K ℂ := ι.toAlgebra
    ∃ (X : WeierstrassCurve ℂ) (_ : X.IsElliptic)
      (ξ : (ℂ ⧸ GlobalTheory.EllipticCM.idealSub (1 : FractionalIdeal (𝓞 K)⁰ K)) ≃+ X.toAffine.Point),
      GlobalTheory.EllipticCM.IsAnalyticIso ξ ∧ ∀ (σ : ℂ ≃ₐ[K] ℂ) (t : (Af K)ˣ),
        GlobalTheory.EllipticCM.Transports σ t one_ne_zero ξ →
        ∃ (Λ₁ : PeriodPair) (Ω₁ : ℂ), TorsTransport ι σ.toRingEquiv t Λ₀ Λ₁ Ω₀ Ω₁ :=
  GlobalTheory.T.exists_cmCurve_torsionTransport_secondPeriod h2 ι Λ₀ Ω₀ hΛ hΩ

theorem exists_globalArtinMap {K : Type} [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] {Ω : Type}
    [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] {art : Ideles K →* GlobalTheory.HeckeGal.Gab K Ω}
    (ha : GlobalTheory.HeckeGal.IsGlobalArtin art) (e : Ω ≃ₐ[K] AlgebraicClosure K) :
    ∃ Art : IdeleClassGroup K →* Field.absoluteGaloisGroupAbelianization K, IsGlobalArtinMap K Art ∧
      ∀ (s : Ideles K) (σ : Formalism.ConjugateSelfDual.G K Ω), (art s)⁻¹ = GlobalTheory.HeckeGal.toAb K Ω σ →
        Art (QuotientGroup.mk s) = Neutral.B1.toAb K ((e.symm.trans σ).trans e) := by
  obtain ⟨φ, hφc, hφb, hφ⟩ := GlobalTheory.T.exists_continuous_bijective_abelianization_of_algEquiv e
  let ψ : Ideles K →* Field.absoluteGaloisGroupAbelianization K := φ.comp art⁻¹
  have hψ : ∀ s, ψ s = φ (art s)⁻¹ := fun s => rfl
  have hle : (diagUnits K).range ≤ ψ.ker := by
    rintro _ ⟨k, rfl⟩
    have hk : diagUnits K k ∈ art.ker := by
      rw [ha.ker]
      exact Subgroup.le_topologicalClosure _ (Subgroup.mem_sup_left ⟨k, rfl⟩)
    rw [MonoidHom.mem_ker, hψ, MonoidHom.mem_ker.mp hk, inv_one, map_one]
  let Art : IdeleClassGroup K →* Field.absoluteGaloisGroupAbelianization K := QuotientGroup.lift _ ψ hle
  have hArt : ∀ s, Art (QuotientGroup.mk s) = φ ((art s)⁻¹) := fun s => rfl
  have hArtσ : ∀ (s : Ideles K) (σ : Formalism.ConjugateSelfDual.G K Ω), (art s)⁻¹ = GlobalTheory.HeckeGal.toAb K Ω σ →
      Art (QuotientGroup.mk s) = Neutral.B1.toAb K ((e.symm.trans σ).trans e) := fun s σ h => by
    rw [hArt, h, hφ]
  refine ⟨Art, ⟨?_, ?_, ?_, ?_, ?_⟩, hArtσ⟩
  · refine (QuotientGroup.isQuotientMap_mk _).continuous_iff.mpr ?_
    exact hφc.comp (ha.quot.continuous.inv)
  · intro c
    obtain ⟨y, rfl⟩ := hφb.2 c
    obtain ⟨x, rfl⟩ := ha.quot.surjective y
    exact ⟨QuotientGroup.mk x⁻¹, by rw [hArt, map_inv art, inv_inv]⟩
  · ext c
    obtain ⟨s, rfl⟩ := QuotientGroup.mk_surjective c
    rw [SetLike.mem_coe, MonoidHom.mem_ker, hArt, GlobalTheory.T.ideleClass_identityComponent_iff_artin_kernel ha,
      ← map_one φ, hφb.1.eq_iff, inv_eq_one]
  · intro L h v hv a hsupp
    obtain ⟨x, hx, rfl⟩ := GlobalTheory.T.supportedIdele_eq_localIdele hsupp
    obtain ⟨A, hA⟩ := ReciprocityTheory.Gal.exists_isPlaceOver Ω v
    constructor
    · intro hu Q hQ hQv
      rw [← hx] at hu
      obtain ⟨σ, hσ, hσe⟩ := (ha.frob v A hA (art (localIdele K v x))).1
        ⟨x, (GlobalTheory.T.isUniformiserAt_iff_adicCompletion_isUnifAt v x).1 hu, rfl⟩
      rw [hArtσ _ σ (by rw [← hσe, map_inv, inv_inv]), abRestrict_mk]
      exact GlobalTheory.T.isFrobAt_restrict_finiteAbelian_subextension e L h v A hA σ hσ Q hQ hQv
    · intro hu
      rw [← hx] at hu
      obtain ⟨σ, hσ, hσe⟩ := (ha.ine v A hA (art (localIdele K v x))).1 ⟨x, hu, rfl⟩
      rw [hArtσ _ σ⁻¹ (by rw [← hσe, map_inv]), abRestrict_mk]
      exact GlobalTheory.T.inertia_restrict_finiteAbelian_unramified_eq_one e L h v hv A hA σ⁻¹ ((ReciprocityTheory.Gal.Ine A).inv_mem hσ)
  · intro L h w hw
    exact absurd hw (InfinitePlace.not_isReal_iff_isComplex.mpr (IsTotallyComplex.isComplex w))

theorem periodEx_of_mainTheorem : GlobalTheory.Published.EllipticMainTheoremCM → PeriodEx := by
  intro hMT K _ _ _ ι h2 Λ₀ Ω₀ hΛ hΩ Ω _ _ _ j art hj ha g σ t hσg hsym
  letI : Algebra K ℂ := ι.toAlgebra
  have hg : ∀ x : K, g (algebraMap K ℂ x) = algebraMap K ℂ x := fun x => by
    change g (ι x) = ι x
    rw [← hj, RingHom.comp_apply, ← hσg, AlgEquiv.commutes]
  let gK : ℂ ≃ₐ[K] ℂ := AlgEquiv.ofRingEquiv (f := g) hg
  obtain ⟨X, hX, ξ, hξ, hT⟩ := exists_uniformisation_torsTransport h2 ι Λ₀ Ω₀ hΛ hΩ
  let e := IsAlgClosure.equiv K Ω (AlgebraicClosure K)
  obtain ⟨Art, hArt, hArtσ⟩ := exists_globalArtinMap ha e
  have hjK : ∀ x : K, j (algebraMap K Ω x) = algebraMap K ℂ x := fun x => by
    rw [← RingHom.comp_apply, hj]
    rfl
  let jK : Ω →ₐ[K] ℂ := { j with commutes' := hjK }
  have hR : GlobalTheory.EllipticCM.RestrictsTo gK (Art (QuotientGroup.mk (finIdele K t))) := by
    rw [hArtσ _ σ hsym]
    refine ⟨jK.comp e.symm.toAlgHom, (e.symm.trans σ).trans e, fun x => ?_, rfl⟩
    change g (j (e.symm x)) = j (e.symm (e (σ (e.symm x))))
    rw [AlgEquiv.symm_apply_apply, hσg]
  have hTr := hMT K h2 Art hArt gK (finIdele K t) hR X 1 one_ne_zero ξ hξ
  rw [show GlobalTheory.EllipticCM.finitePart (finIdele K t) = t from GlobalTheory.EllipticCM.finitePart_inr t] at hTr
  exact hT gK t hTr

end GlobalTheory.LatVal
end
end
