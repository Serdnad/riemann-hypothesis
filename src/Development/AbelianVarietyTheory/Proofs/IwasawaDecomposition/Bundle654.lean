module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle102
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.Bundle008
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle108
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsGlobalHolomorphicLatticeBasisConvex
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle624
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.NormConst
public import Development.AbelianVarietyTheory.Definitions.KeyFormula.KeyRootOfKeyFormula
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle640
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle641
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle639
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AmpleOnAbelianBase
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FnAlgClosedOfFixedPoints
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle001
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle631

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ShFam.Hor.LogCh

theorem exp_lattice_torsion_count : ∀ (Q : Type) [Group Q] (g r N : ℕ) (e : (Fin g → ℂ) → Q) (b : Fin r → Fin g → ℂ) (T : Set Q), 0 < N → (∀ v w, e (v + w) = e v * e w) → Function.Surjective e → IsLatBasis {w | e w = 1} b → (∀ τ ∈ T, τ ^ N = 1) → Nat.card {p : Q // p ^ N = 1} * Nat.card T = N ^ (2 * g) → ∃ S : Set (Fin r → ZMod N), N ^ r * Nat.card S = N ^ (2 * g) ∧ ∀ a : Fin r → ℤ, (fun j => (a j : ZMod N)) ∈ S → e ((N : ℂ)⁻¹ • ∑ j, a j • b j) ∈ T := by
  intro Q _ g r N e b T hN he _hs hb hT hcard
  haveI : NeZero N := ⟨hN.ne'⟩
  have e0 : e 0 = 1 := by
    have h := he 0 0
    rw [add_zero] at h
    exact mul_left_cancel (a := e 0) (h.symm.trans (_root_.mul_one _).symm)
  have esub : ∀ v w, e (v - w) = e v * (e w)⁻¹ := by
    intro v w
    have h := he (v - w) w
    rw [sub_add_cancel] at h
    exact eq_mul_inv_of_mul_eq h.symm
  have ensmul : ∀ (n : ℕ) v, e (n • v) = e v ^ n := by
    intro n v
    induction n with
    | zero => simp [e0]
    | succ n ih => rw [succ_nsmul, he, ih, pow_succ]
  set ψ : (Fin r → ℤ) → Q := fun a => e ((N : ℂ)⁻¹ • ∑ j, a j • b j) with hψ
  have hdiff : ∀ a a' : Fin r → ℤ, (N : ℂ)⁻¹ • ∑ j, a j • b j - (N : ℂ)⁻¹ • ∑ j, a' j • b j
      = (N : ℂ)⁻¹ • ∑ j, (a j - a' j) • b j := by
    intro a a'
    rw [← smul_sub, ← Finset.sum_sub_distrib]
    simp [sub_smul]
  have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'

  have hdvd : ∀ (c m : Fin r → ℤ), (N : ℂ)⁻¹ • ∑ j, c j • b j = ∑ j, m j • b j → ∀ j, c j = N * m j := by
    intro c m h
    have h2 : ∑ j, c j • b j = (N : ℂ) • ∑ j, m j • b j := by
      rw [← h, smul_smul, mul_inv_cancel₀ hN0, one_smul]
    have h3 : ∑ j, ((c j : ℝ) - (N : ℝ) * (m j : ℝ)) • b j = 0 := by
      simp only [sub_smul, mul_smul, Finset.sum_sub_distrib, ← Finset.smul_sum, Int.cast_smul_eq_zsmul]
      rw [h2, Nat.cast_smul_eq_nsmul ℂ, Nat.cast_smul_eq_nsmul ℝ, sub_self]
    have h4 := Fintype.linearIndependent_iff.1 hb.1 _ h3
    intro j
    have := h4 j
    rw [sub_eq_zero] at this
    exact_mod_cast this
  have key : ∀ a a' : Fin r → ℤ, ψ a = ψ a' ↔ ∀ j, (a j : ZMod N) = a' j := by
    intro a a'
    constructor
    · intro h
      have h1 : e ((N : ℂ)⁻¹ • ∑ j, (a j - a' j) • b j) = 1 := by
        rw [← hdiff, esub]
        exact mul_inv_eq_one.2 h
      obtain ⟨m, hm⟩ := (hb.2 _).1 h1
      have := hdvd (fun j => a j - a' j) m hm
      intro j
      rw [ZMod.intCast_eq_intCast_iff_dvd_sub]
      exact ⟨-m j, by have := this j; push_cast at this ⊢; linarith⟩
    · intro h
      have hk : ∀ j, ∃ k : ℤ, a j - a' j = N * k := fun j =>
        (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).1 (h j).symm |>.imp fun k hk => by linarith
      choose k hk using hk
      have h1 : e (∑ j, k j • b j) = 1 := (hb.2 _).2 ⟨k, rfl⟩
      have h2 : (N : ℂ)⁻¹ • ∑ j, (a j - a' j) • b j = ∑ j, k j • b j := by
        simp_rw [hk, mul_smul, ← Finset.smul_sum]
        rw [Nat.cast_smul_eq_nsmul ℤ]
        rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hN0, one_smul]
      have h3 := hdiff a a'
      rw [h2] at h3
      have h4 : (N : ℂ)⁻¹ • ∑ j, a j • b j = (N : ℂ)⁻¹ • ∑ j, a' j • b j + ∑ j, k j • b j := by
        rw [← h3]; abel
      simp only [hψ, h4, he, h1, _root_.mul_one]
  have hpow : ∀ a, ψ a ^ N = 1 := by
    intro a
    show e _ ^ N = 1
    rw [← ensmul, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, mul_inv_cancel₀ hN0, one_smul]
    exact (hb.2 _).2 ⟨a, rfl⟩
  have hsurj : ∀ p : Q, p ^ N = 1 → ∃ a, ψ a = p := by
    intro p hp
    obtain ⟨u, rfl⟩ := _hs p
    have h1 : e (N • u) = 1 := by rw [ensmul, hp]
    obtain ⟨m, hm⟩ := (hb.2 _).1 h1
    refine ⟨m, ?_⟩
    show e _ = e u
    rw [← hm, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hN0, one_smul]
  let F : (Fin r → ZMod N) → Q := fun s => ψ (fun j => ((s j).val : ℤ))
  have hFval : ∀ a : Fin r → ℤ, F (fun j => (a j : ZMod N)) = ψ a := by
    intro a
    exact (key _ _).2 fun j => by simp
  have hFinj : Function.Injective F := by
    intro s s' h
    funext j
    have h1 := (key _ _).1 h j
    simpa using h1
  have hR : Nat.card {p : Q // p ^ N = 1} = N ^ r := by
    have hbij : Function.Bijective (fun s => (⟨F s, hpow _⟩ : {p : Q // p ^ N = 1})) := by
      refine ⟨fun s s' h => hFinj (congrArg Subtype.val h), fun p => ?_⟩
      obtain ⟨a, ha⟩ := hsurj p.1 p.2
      exact ⟨fun j => (a j : ZMod N), Subtype.ext (by show F _ = _; rw [hFval, ha])⟩
    rw [← Nat.card_eq_of_bijective _ hbij]
    simp [Nat.card_eq_fintype_card, Fintype.card_fun, ZMod.card]
  refine ⟨{s | F s ∈ T}, ?_, ?_⟩
  · have hS : Nat.card {s | F s ∈ T} = Nat.card T := by
      have hbij : Function.Bijective (fun s : {s | F s ∈ T} => (⟨F s.1, s.2⟩ : T)) := by
        refine ⟨fun s s' h => Subtype.ext (hFinj (congrArg Subtype.val h)), fun τ => ?_⟩
        obtain ⟨a, ha⟩ := hsurj τ.1 (hT _ τ.2)
        refine ⟨⟨fun j => (a j : ZMod N), ?_⟩, Subtype.ext ?_⟩
        · show F _ ∈ T
          rw [hFval, ha]
          exact τ.2
        · show F _ = _
          rw [hFval, ha]
      exact Nat.card_eq_of_bijective _ hbij
    rw [hS, ← hR, hcard]
  · intro a ha
    show ψ a ∈ T
    rw [← hFval]
    exact ha

end GlobalTheory.ShFam.Hor.LogCh
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.ShFam.Hor.LogCh

theorem IsLatFam.pullback_analytic : ∀ (m n g : ℕ) (B : Set (Fin n → ℂ)) (B' : Set (Fin m → ℂ))
    (K : (Fin n → ℂ) → Set (Fin g → ℂ)) (φ : (Fin m → ℂ) → Fin n → ℂ),
    GlobalTheory.ShFam.Hor.LogCh.IsLatFam B K → IsOpen B' → AnalyticOnNhd ℂ φ B' → Set.MapsTo φ B' B →
      GlobalTheory.ShFam.Hor.LogCh.IsLatFam B' (fun b => K (φ b)) := by
  intro m n g B B' K φ hK hB' hφ hmaps
  obtain ⟨_, h2, h3, h4⟩ := hK
  let Ψ : (Fin m → ℂ) × (Fin g → ℂ) → (Fin n → ℂ) × (Fin g → ℂ) := fun q => (φ q.1, q.2)
  refine ⟨hB', fun b hb => h2 (φ b) (hmaps hb), ?_, ?_⟩
  · have hcont : ContinuousOn Ψ (B' ×ˢ (Set.univ : Set (Fin g → ℂ))) :=
      (hφ.continuousOn.comp continuousOn_fst
        (fun q (hq : q ∈ B' ×ˢ (Set.univ : Set (Fin g → ℂ))) => hq.1)).prodMk continuousOn_snd
    have hopen := hcont.isOpen_inter_preimage (hB'.prod isOpen_univ) h3
    convert hopen using 1
    ext q
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_prod, Set.mem_univ, and_true, Set.mem_preimage, Ψ]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, hmaps h1, h2⟩
    · rintro ⟨h1, _, h2⟩
      exact ⟨h1, h2⟩
  · intro b₀ hb₀ w₀ hw₀
    obtain ⟨ζ, hζ0, hζa, hev⟩ := h4 (φ b₀) (hmaps hb₀) w₀ hw₀
    refine ⟨fun b => ζ (φ b), hζ0, hζa.comp (hφ b₀ hb₀), ?_⟩
    have hΨ : ContinuousAt Ψ (b₀, w₀) :=
      ((hφ b₀ hb₀).continuousAt.comp continuousAt_fst).prodMk continuousAt_snd
    exact hΨ.tendsto.eventually hev

end GlobalTheory.ShFam.Hor.LogCh
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ShFam.Hor.LogCh

theorem exists_isLatBasis_of_isLatFam : ∀ (n g : ℕ) (B : Set (Fin n → ℂ)) (K : (Fin n → ℂ) → Set (Fin g → ℂ))
    (b₀ : Fin n → ℂ), IsLatFam B K → b₀ ∈ B → ∃ (r : ℕ) (b : Fin r → Fin g → ℂ), IsLatBasis (K b₀) b := by
  intro n g B K b₀ hK hb₀
  obtain ⟨H, hH⟩ := hK.2.1 b₀ hb₀
  have h0 : (0 : Fin g → ℂ) ∈ K b₀ := by rw [← hH]; exact H.zero_mem
  obtain ⟨ζ, hζ0, -, hζ⟩ := hK.2.2.2 b₀ hb₀ 0 h0
  have hcont : Filter.Tendsto (fun w : Fin g → ℂ => (b₀, w)) (𝓝 0) (𝓝 (b₀, 0)) :=
    (Continuous.prodMk continuous_const continuous_id).tendsto' _ _ rfl
  have hev : ∀ᶠ w in 𝓝 (0 : Fin g → ℂ), w ∈ K b₀ → w = 0 := by
    filter_upwards [hcont.eventually hζ] with w hw hwK
    rw [← hζ0]; exact hw.1 hwK
  let L : Submodule ℤ (Fin g → ℂ) := AddSubgroup.toIntSubmodule H
  have hL : ∀ w, w ∈ L ↔ w ∈ K b₀ := fun w => by
    rw [← hH]; rfl
  haveI : DiscreteTopology L := by
    obtain ⟨U, hU, hUo, h0U⟩ := mem_nhds_iff.1 hev
    refine discreteTopology_of_isOpen_singleton_zero ?_
    have : ({0} : Set L) = Subtype.val ⁻¹' U := by
      ext x
      simp only [Set.mem_singleton_iff, Set.mem_preimage]
      constructor
      · rintro rfl; exact h0U
      · intro hx; exact Subtype.ext (hU hx ((hL x).1 x.2))
    rw [this]; exact hUo.preimage continuous_subtype_val
  let bs := Module.finBasis ℤ L
  refine ⟨Module.finrank ℤ L, fun i => (bs i : Fin g → ℂ), GlobalTheory.linearIndependent_real_coe_basis bs, fun w => ?_⟩
  have hsp := GlobalTheory.span_range_coe_basis bs
  have hw : w ∈ L ↔ w ∈ Submodule.span ℤ (Set.range fun i => (bs i : Fin g → ℂ)) := by rw [hsp]
  rw [← hL, hw, Submodule.mem_span_range_iff_exists_fun]
  constructor
  · rintro ⟨m, hm⟩; exact ⟨m, hm.symm⟩
  · rintro ⟨m, hm⟩; exact ⟨m, hm.symm⟩

end GlobalTheory.ShFam.Hor.LogCh
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ShFam.Hor.LogCh

theorem IsLatFam.eventually_mem_of_graph {n g : ℕ} {K : (Fin n → ℂ) → Set (Fin g → ℂ)} {b₀ : Fin n → ℂ}
    {w₀ : Fin g → ℂ} {ζ : (Fin n → ℂ) → Fin g → ℂ} (hζ0 : ζ b₀ = w₀) (hζc : ContinuousAt ζ b₀)
    (hζ : ∀ᶠ q in 𝓝 (b₀, w₀), q.2 ∈ K q.1 ↔ q.2 = ζ q.1) : ∀ᶠ b in 𝓝 b₀, ζ b ∈ K b := by
  have ht : Filter.Tendsto (fun b => (b, ζ b)) (𝓝 b₀) (𝓝 (b₀, w₀)) := by
    have := (continuousAt_id.prodMk hζc).tendsto
    simpa [hζ0] using this
  filter_upwards [ht.eventually hζ] with b hb
  exact hb.2 rfl

theorem exists_isLatBasis_of_discrete {g : ℕ} (H : AddSubgroup (Fin g → ℂ))
    (hd : ∀ᶠ w in 𝓝 (0 : Fin g → ℂ), w ∈ H → w = 0)
    (hs : Submodule.span ℝ (H : Set (Fin g → ℂ)) = ⊤) :
    ∃ β : Fin (2 * g) → Fin g → ℂ, IsLatBasis (H : Set (Fin g → ℂ)) β := by
  set L : Submodule ℤ (Fin g → ℂ) := H.toIntSubmodule with hL
  have hLset : (L : Set (Fin g → ℂ)) = H := rfl
  haveI : DiscreteTopology L := by
    refine discreteTopology_of_isOpen_singleton_zero ?_
    obtain ⟨U, hU, hUo, h0U⟩ := eventually_nhds_iff.1 hd
    refine ⟨U, hUo, ?_⟩
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · intro hx
      exact Subtype.ext (hU x.1 hx x.2)
    · rintro rfl
      exact h0U
  haveI : IsZLattice ℝ L := ⟨by rw [hLset]; exact hs⟩
  have hr : Module.finrank ℤ L = 2 * g := by
    rw [ZLattice.rank ℝ L, Module.finrank_pi_fintype]
    simp [Complex.finrank_real_complex, mul_comm]
  let b := Module.finBasisOfFinrankEq ℤ L hr
  refine ⟨fun j => (b j : Fin g → ℂ), ?_, fun w => ⟨fun hw => ?_, ?_⟩⟩
  · have he : (fun j => (b j : Fin g → ℂ)) = ⇑(b.ofZLatticeBasis ℝ L) :=
      funext fun j => (Module.Basis.ofZLatticeBasis_apply ℝ L b j).symm
    rw [he]
    exact (b.ofZLatticeBasis ℝ L).linearIndependent
  · refine ⟨b.repr ⟨w, hw⟩, ?_⟩
    have h := congrArg (fun x : L => (x : Fin g → ℂ)) (b.sum_repr ⟨w, hw⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul] at h
    exact h.symm
  · rintro ⟨m, rfl⟩
    exact H.sum_mem fun j _ => H.zsmul_mem (b j).2 _

theorem IsLatFam.eventually_intComb {n g r : ℕ} {B : Set (Fin n → ℂ)} {K : (Fin n → ℂ) → Set (Fin g → ℂ)}
    {b₀ : Fin n → ℂ} (hK : IsLatFam B K) (hb₀ : b₀ ∈ B) {lam : (Fin n → ℂ) → Fin r → Fin g → ℂ}
    (hlc : ContinuousAt lam b₀) (hlK : ∀ᶠ b in 𝓝 b₀, ∀ j, lam b j ∈ K b) (hβ : IsLatBasis (K b₀) (lam b₀))
    (y : Fin g → ℂ) :
    ∀ᶠ q in 𝓝 (b₀, y), q.2 ∈ K q.1 → ∃ m : Fin r → ℤ, q.2 = ∑ j, m j • lam q.1 j := by
  by_cases hy : y ∈ K b₀
  · obtain ⟨m, hm⟩ := (hβ.2 y).1 hy
    obtain ⟨ζ, hζ0, -, hζ⟩ := hK.2.2.2 b₀ hb₀ y hy
    set f : (Fin n → ℂ) → Fin g → ℂ := fun b => ∑ j, m j • lam b j with hf
    have hfc : ContinuousAt f b₀ := by
      have : Continuous (fun v : Fin r → Fin g → ℂ => ∑ j, m j • v j) := by fun_prop
      exact this.continuousAt.comp hlc
    have hf0 : f b₀ = y := hm.symm
    have hfK : ∀ᶠ b in 𝓝 b₀, f b ∈ K b := by
      filter_upwards [hlK, hK.1.mem_nhds hb₀] with b hb hbB
      obtain ⟨H, hH⟩ := hK.2.1 b hbB
      rw [← hH] at hb ⊢
      exact H.sum_mem fun j _ => H.zsmul_mem (hb j) _
    have ht : Filter.Tendsto (fun b => (b, f b)) (𝓝 b₀) (𝓝 (b₀, y)) := by
      have := (continuousAt_id.prodMk hfc).tendsto
      simpa [hf0] using this
    have hfζ : ∀ᶠ b in 𝓝 b₀, f b = ζ b := by
      filter_upwards [ht.eventually hζ, hfK] with b h1 h2
      exact h1.1 h2
    have hq : ∀ᶠ q : (Fin n → ℂ) × (Fin g → ℂ) in 𝓝 (b₀, y), f q.1 = ζ q.1 :=
      (continuous_fst.tendsto (b₀, y)).eventually hfζ
    filter_upwards [hq, hζ] with q h1 h2 h3
    exact ⟨m, (h2.1 h3).trans h1.symm⟩
  · have ho := hK.2.2.1.mem_nhds (show (b₀, y) ∈ {q : (Fin n → ℂ) × (Fin g → ℂ) | q.1 ∈ B ∧ q.2 ∉ K q.1} from ⟨hb₀, hy⟩)
    filter_upwards [ho] with q hq h
    exact absurd h hq.2

theorem isLatBasis_of_ball {g : ℕ} (H : AddSubgroup (Fin g → ℂ)) (lam : Fin (2 * g) → Fin g → ℂ) (R : ℝ)
    (hli : LinearIndependent ℝ lam) (hmem : ∀ j, lam j ∈ H) (hR : ∑ j, ‖lam j‖ ≤ R)
    (hball : ∀ w ∈ Metric.closedBall (0 : Fin g → ℂ) R, w ∈ H → ∃ m : Fin (2 * g) → ℤ, w = ∑ j, m j • lam j) :
    IsLatBasis (H : Set (Fin g → ℂ)) lam := by
  first
  | exact @_root_.GlobalTheory.LatticeBasisClosedBall.isLatBasis_of_closedBall
  | exact _root_.GlobalTheory.LatticeBasisClosedBall.isLatBasis_of_closedBall
  | (apply _root_.GlobalTheory.LatticeBasisClosedBall.isLatBasis_of_closedBall <;> assumption)
  | (intros; apply _root_.GlobalTheory.LatticeBasisClosedBall.isLatBasis_of_closedBall <;> assumption)
  | (intros; apply @_root_.GlobalTheory.LatticeBasisClosedBall.isLatBasis_of_closedBall <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.LatticeBasisClosedBall.isLatBasis_of_closedBall ..)

theorem IsLatFam.exists_analytic_locBasis : ∀ (n g : ℕ) (B : Set (Fin n → ℂ)) (K : (Fin n → ℂ) → Set (Fin g → ℂ))
    (b₀ : Fin n → ℂ), IsLatFam B K → b₀ ∈ B → Submodule.span ℝ (K b₀) = ⊤ →
    ∃ lam : (Fin n → ℂ) → Fin (2 * g) → Fin g → ℂ, AnalyticAt ℂ lam b₀ ∧ ∀ᶠ b in 𝓝 b₀, IsLatBasis (K b) (lam b) := by
  intro n g B K b₀ hK hb₀ hs
  obtain ⟨H₀, hH₀⟩ := hK.2.1 b₀ hb₀
  have h0 : (0 : Fin g → ℂ) ∈ K b₀ := by rw [← hH₀]; exact H₀.zero_mem
  obtain ⟨ζ₀, hζ₀0, -, hζ₀⟩ := hK.2.2.2 b₀ hb₀ 0 h0
  have hd : ∀ᶠ w in 𝓝 (0 : Fin g → ℂ), w ∈ H₀ → w = 0 := by
    have ht : Filter.Tendsto (fun w : Fin g → ℂ => (b₀, w)) (𝓝 0) (𝓝 (b₀, 0)) :=
      (continuous_const.prodMk continuous_id).continuousAt.tendsto
    filter_upwards [ht.eventually hζ₀] with w hw hwH
    have hwK : w ∈ K b₀ := by rw [← hH₀]; exact hwH
    rw [hw.1 hwK, hζ₀0]
  obtain ⟨β, hβ⟩ := exists_isLatBasis_of_discrete H₀ hd (by rw [hH₀]; exact hs)
  rw [hH₀] at hβ
  have hβK : ∀ j, β j ∈ K b₀ := fun j =>
    (hβ.2 (β j)).2 ⟨Pi.single j 1, by simp [Pi.single_apply]⟩
  choose ζ hζ0 hζa hζ using fun j => hK.2.2.2 b₀ hb₀ (β j) (hβK j)
  have hla : AnalyticAt ℂ (fun b j => ζ j b) b₀ := AnalyticAt.pi hζa
  have hlc := hla.continuousAt
  have hl0 : (fun j => ζ j b₀) = β := funext hζ0
  have hlK : ∀ᶠ b in 𝓝 b₀, ∀ j, ζ j b ∈ K b :=
    Filter.eventually_all.2 fun j => IsLatFam.eventually_mem_of_graph (hζ0 j) (hζa j).continuousAt (hζ j)
  have hβ' : IsLatBasis (K b₀) ((fun b j => ζ j b) b₀) := by
    show IsLatBasis (K b₀) (fun j => ζ j b₀)
    rw [hl0]; exact hβ
  set R : ℝ := ∑ j, (‖β j‖ + 1) with hR
  have hball := (isCompact_closedBall (0 : Fin g → ℂ) R).eventually_forall_of_forall_eventually (x₀ := b₀)
    (P := fun b w => w ∈ K b → ∃ m : Fin (2 * g) → ℤ, w = ∑ j, m j • ζ j b) fun y _ => IsLatFam.eventually_intComb hK hb₀ hlc hlK hβ' y
  have hli : ∀ᶠ b in 𝓝 b₀, LinearIndependent ℝ (fun j => ζ j b) := by
    have h1 : LinearIndependent ℝ ((fun b j => ζ j b) b₀) := hβ'.1
    exact hlc.tendsto.eventually h1.eventually
  have hnorm : ∀ᶠ b in 𝓝 b₀, ∀ j, ‖ζ j b‖ ≤ ‖β j‖ + 1 := by
    refine Filter.eventually_all.2 fun j => ?_
    have hc : ContinuousAt (fun b => ‖ζ j b‖) b₀ := (hζa j).continuousAt.norm
    have hlt : (fun b => ‖ζ j b‖) b₀ < (fun _ => ‖β j‖ + 1) b₀ := by simp [hζ0 j]
    filter_upwards [hc.eventually_lt continuousAt_const hlt] with b hb
    exact hb.le
  refine ⟨fun b j => ζ j b, hla, ?_⟩
  filter_upwards [hball, hli, hnorm, hlK, hK.1.mem_nhds hb₀] with b h1 h2 h3 h4 h5
  obtain ⟨H, hH⟩ := hK.2.1 b h5
  rw [← hH]
  refine isLatBasis_of_ball H _ R h2 (fun j => ?_) (Finset.sum_le_sum fun j _ => h3 j) fun w hw hwH => ?_
  · show ζ j b ∈ (H : Set (Fin g → ℂ)); rw [hH]; exact h4 j
  · exact h1 w hw (by rw [← hH]; exact hwH)

end GlobalTheory.ShFam.Hor.LogCh
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_const_integral_coords_lattice_section : ∀ (n g r : ℕ) (B : Set (Fin n → ℂ)) (K : (Fin n → ℂ) → Set (Fin g → ℂ)) (lam : (Fin n → ℂ) → Fin r → Fin g → ℂ) (ζ : (Fin n → ℂ) → Fin g → ℂ) (b₀ : Fin n → ℂ), IsPreconnected B → ContinuousOn lam B → ContinuousOn ζ B → (∀ b ∈ B, IsLatBasis (K b) (lam b)) → (∀ b ∈ B, ζ b ∈ K b) → b₀ ∈ B → ∃ m : Fin r → ℤ, ∀ b ∈ B, ζ b = ∑ j, m j • lam b j := by
  first | exact @GlobalTheory.ShFam.Hor.LogCh.exists_const_coords | exact GlobalTheory.ShFam.Hor.LogCh.exists_const_coords | (intros; apply GlobalTheory.ShFam.Hor.LogCh.exists_const_coords <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_global_holomorphic_lattice_basis_convex : ∀ (n g r : ℕ) (B : Set (Fin n → ℂ)) (K : (Fin n → ℂ) → Set (Fin g → ℂ)), IsOpen B → Convex ℝ B → (∀ b₀ ∈ B, ∃ lam : (Fin n → ℂ) → Fin r → Fin g → ℂ, AnalyticAt ℂ lam b₀ ∧ ∀ᶠ b in 𝓝 b₀, IsLatBasis (K b) (lam b)) → ∃ lam : (Fin n → ℂ) → Fin r → Fin g → ℂ, DifferentiableOn ℂ lam B ∧ ∀ b ∈ B, IsLatBasis (K b) (lam b) := by
  first | exact @GlobalTheory.ShFam.Hor.LogCh.Glob.exists_global | exact GlobalTheory.ShFam.Hor.LogCh.Glob.exists_global | (intros; apply GlobalTheory.ShFam.Hor.LogCh.Glob.exists_global <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.ShFam GlobalTheory.LamT GlobalTheory.KeyFourth GlobalTheory.FrameUnif GlobalTheory.Reg
open scoped Matrix TensorProduct

theorem _root_.GlobalTheory.T.theta_key_rule_value_at_theta_point : ∀ κ : GlobalTheory.KeyCl.Rule, GlobalTheory.KeyCl.Homog (fun _ => 1) κ → GlobalTheory.KeyCl.ThetaOne κ → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => Formalism.L2.PjFree.relab c σ (e j).1)) (r : ℕ) (M : _root_.GlobalTheory.FrameUnif.ModelsOf F r) (k : Fin F.n) (T : ThetaData e F M k), ∀ b ∈ T.co ⁻¹' (M.X k).dom, ∀ (a : ℂ) (y : FrPt Xo c (CAt σ)) (Φ : FibKey Xo ℂ y.x), a ≠ 0 → IsThetaPt T b a y → Tied (S := ℂ) e y.s y.u Φ → a ^ 8 * (κ ℂ Φ.key : ℂ) = ((2 * Real.pi * Complex.I) ^ g * (T.h b).det) ^ 4 := by
  first | exact @GlobalTheory.KeyFourth.value_at_thetaPt | exact GlobalTheory.KeyFourth.value_at_thetaPt | (intros; apply GlobalTheory.KeyFourth.value_at_thetaPt <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.ShFam GlobalTheory.LamT GlobalTheory.KeyFourth GlobalTheory.FrameUnif GlobalTheory.Reg
open scoped Matrix TensorProduct

theorem _root_.GlobalTheory.T.theta_key_rule_triangular_frame_change_fourth_power : ∀ κ : GlobalTheory.KeyCl.Rule, GlobalTheory.KeyCl.Homog (fun _ => 1) κ → GlobalTheory.KeyCl.Funct κ → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (K : Type) [Field K] [CharZero K] [Algebra c.F K] (t : Ix Dw → Kˣ) (y y' : FrPt Xo c K) (Φ : FibKey Xo K y.x) (Φ' : FibKey Xo K y'.x), FrBor t y y' → Tied e y.s y.u Φ → Tied e y'.s y'.u Φ' → κ K Φ'.key = kch t ^ 4 * κ K Φ.key := by
  first | exact @GlobalTheory.KeyFourth.rule_frBor | exact GlobalTheory.KeyFourth.rule_frBor | (intros; apply GlobalTheory.KeyFourth.rule_frBor <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.BdArc Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (Data Frame Bor rmul lact mat col dmin Wt)

theorem _root_.GlobalTheory.T.arc_off_boundary_descends_to_moduli_localization : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (σ : c.F →+* ℂ) (A : Type) [CommRing A] (φ : c.F →+* A) (x : Sp A ⟶ gen Z) (fr : EigFrame Z φ (x ≫ genι Z)) (ψ : ℂ → (A →+* ℂ)) (r : ℝ) (y : ℂ → FrPt Xo c (CAt σ)), IsArc Z σ φ x ψ r → (∀ u ∈ Metric.ball (0 : ℂ) r, u ≠ 0 → Matches fr (ψ u) (y u)) → ∀ u₀ ∈ Metric.ball (0 : ℂ) r, u₀ ≠ 0 → ∃ (R : Type) (_ : CommRing R) (xR : Sp R ⟶ Xo.X) (vR : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Sp (DualNumber R) ⟶ Xo.univ.t.G.left)) (ev : ℂ → (R →+* ℂ)) (V : Set ℂ), IsOpen V ∧ u₀ ∈ V ∧ (∀ t, DifferentiableOn ℂ (fun u => ev u t) V) ∧ ∀ u ∈ V, (y u).x = spMap (show R →+* CAt σ from ev u) ≫ xR ∧ ∀ τ i, (y u).u τ i = spMap (dualMap (show R →+* CAt σ from ev u)) ≫ vR τ i := by
  first | exact @GlobalTheory.ShFam.BdArc.arc_descends_to_moduli | exact GlobalTheory.ShFam.BdArc.arc_descends_to_moduli | (intros; apply GlobalTheory.ShFam.BdArc.arc_descends_to_moduli <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.BdArc Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (Data Frame Bor rmul lact mat col dmin Wt)

theorem _root_.GlobalTheory.T.meromorphic_germ_vanishes_of_periodic_exp_modulus : ∀ (p L h a b : ℂ → ℂ) (T r : ℝ) (M n : ℕ) (ζ : ℂ), 0 < M → 0 < n → ζ ^ n = 1 → 0 < r → DifferentiableOn ℂ p {w | T < w.im} → DifferentiableOn ℂ L {w | T < w.im} → (∀ w : ℂ, T < w.im → p (w + M) = ζ * p w ∧ L (w + M) = L w ∧ ‖h (eTwoPi w)‖ = ‖p w‖ * ‖Complex.exp (L w)‖) → Tendsto p imTop (𝓝 0) → DifferentiableOn ℂ a (Metric.ball (0 : ℂ) r) → DifferentiableOn ℂ b (Metric.ball (0 : ℂ) r) → (∀ u ∈ Metric.ball (0 : ℂ) r, u ≠ 0 → b u ≠ 0 ∧ h u * b u = a u) → Tendsto h (𝓝[≠] 0) (𝓝 0) := by
  first | exact @GlobalTheory.ShFam.BdArc.tendsto_zero_of_norm_eq_mul_exp_periodic | exact GlobalTheory.ShFam.BdArc.tendsto_zero_of_norm_eq_mul_exp_periodic | (intros; apply GlobalTheory.ShFam.BdArc.tendsto_zero_of_norm_eq_mul_exp_periodic <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.BdArc Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (Data Frame Bor rmul lact mat col dmin Wt)

theorem _root_.GlobalTheory.T.boundary_arc_lift_not_converges_symmetric_domain : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (σ : c.F →+* ℂ) (N : ℕ) (U : Unf Xo c σ N) (A : Type) [CommRing A] (φ : c.F →+* A) (x : Sp A ⟶ gen Z) (fr : EigFrame Z φ (x ≫ genι Z)) (ψ : ℂ → (A →+* ℂ)) (r : ℝ) (y : ℂ → FrPt Xo c (CAt σ)) (k : U.Comp) (T : ℝ) (xx : ℂ → Frame (U.X k).Ψ N), GoodEmb c σ → IsUnf U → IsBdArc Z σ φ x ψ r → (∀ u ∈ Metric.ball (0 : ℂ) r, u ≠ 0 → Matches fr (ψ u) (y u)) → IsLift U k y T xx → ∀ x₀ ∈ (U.X k).dom, ∀ x' : ℂ → Frame (U.X k).Ψ N, Tendsto x' imTop (𝓝 x₀) → ¬ ∀ᶠ w in imTop, x' w ∈ (U.X k).dom ∧ SamePos (U.X k) (xx w) (x' w) := by
  first | exact @GlobalTheory.ShFam.BdArc.Leave.lift_not_converges | exact GlobalTheory.ShFam.BdArc.Leave.lift_not_converges | (intros; apply GlobalTheory.ShFam.BdArc.Leave.lift_not_converges <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.BdArc Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (Data Frame Bor rmul lact mat col dmin Wt)

theorem _root_.GlobalTheory.T.exists_holomorphic_arc_smooth_algebra_nonvanishing : ∀ (F A : Type) [Field F] [CommRing A] [IsDomain A] [Algebra F A], Algebra.Smooth F A → ∀ (ψ₀ : A →+* ℂ) (p : A), p ≠ 0 → ∃ (ψ : ℂ → (A →+* ℂ)) (r : ℝ), IsHolPts ψ r ∧ ψ 0 = ψ₀ ∧ (∀ u ∈ Metric.ball (0 : ℂ) r, (ψ u).comp (algebraMap F A) = ψ₀.comp (algebraMap F A)) ∧ ∀ u ∈ Metric.ball (0 : ℂ) r, u ≠ 0 → ψ u p ≠ 0 := by
  first | exact @GlobalTheory.HolArc.exists_holPts_ne_zero | exact GlobalTheory.HolArc.exists_holPts_ne_zero | (intros; apply GlobalTheory.HolArc.exists_holPts_ne_zero <;> assumption)
end
