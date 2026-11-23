module

public import Development.AutomorphicSpectrum.Definitions.AdelicLattices.Bundle001
public import Mathlib.Algebra.AffineMonoid.Basic
public import Mathlib.NumberTheory.NumberField.Discriminant.Basic
public import Mathlib.RingTheory.DedekindDomain.Different
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle002
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.Bundle018
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle003
public import Mathlib.RingTheory.Valuation.Integers
public import ReciprocityTheory.DualLattices.Bundle002
public import ReciprocityTheory.DualLattices.Bundle022
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle002
public import Development.WeilBound.CoreStatements.HodgeTatePoints.IsLocalHomOfFinite
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle005
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle048
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle022
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle033
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle043
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle038
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle007
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.GermComp1ZeroPointLeft
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle034
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.AlphaBetaAdjointExact
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsSplitGaussChars
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle031
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TensorProduct.IsBaseChangeFree
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
import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.IsEigBasisIff
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsTight
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.Bundle001
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Objects

@[expose] public section

section

open NumberField Matrix GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

theorem _root_.GlobalTheory.T.hermitian_log_norm_local_sum : ∀ (k E : Type) [Field k] [NumberField k] [Field E] [NumberField E] (τ : E →+* k) (N : LogNorms k) (ρ : k) (a r : E) (p q d : ℕ) (n : (k →+* ℂ) → ℝ) (x : ℝ) (t t' : Nat.Primes → E), ρ ≠ 0 → a ≠ 0 → 0 < d → r ^ 2 = -(d : E) → -(∑ s, Real.log (n s)) / Module.finrank ℚ k = x → (∀ s, N.inf s = Real.log ‖s ρ‖ + ((p : ℝ) - q) / 2 * (Real.log (n s) + Real.log d / 2) + Real.log ‖s (τ a)‖ / 2) → (∀ ℓ : Nat.Primes, ∑ j : E →+* ℂ_[ℓ], Real.log ‖j (t' ℓ)‖ = ∑ j : E →+* ℂ_[ℓ], Real.log ‖j (t ℓ)‖) → (∀ (ℓ : Nat.Primes) (j : E →+* ℂ_[ℓ]), Real.log ‖j (t ℓ)‖ + Real.log ‖j (t' ℓ)‖ + Real.log ‖j a‖ = -((p : ℝ) + q) * logIdeal (j.comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E))) → {ℓ : Nat.Primes | ∃ j : E →+* ℂ_[ℓ], Real.log ‖j (t ℓ)‖ ≠ 0}.Finite → (∀ (ℓ : Nat.Primes) (j : k →+* ℂ_[ℓ]), N.fin ℓ j + q * (logIdeal ((j.comp τ).comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E)) - Real.log ‖((d : ℕ) : ℂ_[ℓ])‖) = Real.log ‖j ρ‖ - Real.log ‖j (τ (t ℓ))‖ - q * logIdeal ((j.comp τ).comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E)) + ((q : ℝ) - p) * (logIdeal ((j.comp τ).comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E)) - Real.log ‖j (τ r)‖)) → N.IsAdelic ∧ N.deg = ((p : ℝ) - q) / 2 * (x - Real.log (rootDiscr E) + Real.log (Real.sqrt d)) + q * (2 * Real.log (Real.sqrt d) - Real.log (rootDiscr E)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Fl.LocalSum.deg_of_local_formulas | exact GlobalTheory.CompanionTheory.Ar.Fl.LocalSum.deg_of_local_formulas | (intros; apply GlobalTheory.CompanionTheory.Ar.Fl.LocalSum.deg_of_local_formulas <;> assumption)
end

section

open GlobalTheory.CompanionTheory.Ar.Num

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Num.LatticeGoodness

private theorem loc_free_base_change {o Ω C : Type} [CommRing o] [Field Ω] [Field C] [Algebra o Ω]
    [Algebra o C] [Algebra Ω C] (R : Subalgebra o Ω) (RC : Subalgebra o C)
    (hRC : ∀ a ∈ R, algebraMap Ω C a ∈ RC) {ι : Type} [Finite ι] {r : ℕ}
    {L : AddSubgroup (ι → Ω)} (hL : LocFree R r L) :
    LocFree RC r (spanOver RC (bcMap Ω C ι '' (L : Set (ι → Ω)))) := by
  obtain ⟨-, k, f, c, hf, hc, hsum, hb⟩ := hL
  refine ⟨fun a ha e he => SpanExact.smul_mem_spanOver RC _ ha he, k,
    fun l => algebraMap Ω C (f l), fun l => algebraMap Ω C (c l), fun l => hRC _ (hf l),
    fun l => hRC _ (hc l), ?_, fun l => ?_⟩
  · have h := congrArg (algebraMap Ω C) hsum

    simpa only [map_sum, map_mul, map_one] using h
  obtain ⟨b, hli, hsp, hiff⟩ := hb l
  have hbc := isBaseChange_bcMap Ω C ι
  let B : Module.Basis (Fin r) Ω (ι → Ω) := Module.Basis.mk hli hsp.ge
  let B' := hbc.basis B
  have hB' : (⇑B' : Fin r → ι → C) = fun q => bcMap Ω C ι (b q) := by
    funext q
    simp [B', B, IsBaseChange.basis_apply, Module.Basis.mk_apply]
  have hbl : ∀ q, ∃ m : ℕ, f l ^ m • b q ∈ L := fun q =>
    (hiff (b q)).2 ⟨Pi.single q 1, fun q' => ⟨0, by
      rcases eq_or_ne q' q with rfl | h
      · simp [one_mem]
      · simp [Pi.single_apply, h]⟩, by simp [Pi.single_apply]⟩
  refine ⟨fun q => bcMap Ω C ι (b q), by rw [← hB']; exact B'.linearIndependent,
    by rw [← hB']; exact B'.span_eq, fun e => ?_⟩
  beta_reduce
  by_cases hg : f l = 0
  · have hg' : algebraMap Ω C (f l) = 0 := by rw [hg, map_zero]
    constructor
    · intro _
      refine ⟨B'.repr e, fun q => ⟨1, by rw [hg', pow_one, zero_mul]; exact zero_mem _⟩, ?_⟩
      conv_lhs => rw [← B'.sum_repr e]
      rw [hB']
    · intro _
      exact ⟨1, by rw [hg', pow_one, zero_smul]; exact zero_mem _⟩
  have hg' : algebraMap Ω C (f l) ≠ 0 := (map_ne_zero _).2 hg
  have hgR : algebraMap Ω C (f l) ∈ RC := hRC _ (hf l)
  constructor
  · rintro ⟨m, hm⟩
    have key : ∀ x ∈ spanOver RC (bcMap Ω C ι '' (L : Set (ι → Ω))), ∃ a : Fin r → C,
        (∀ q, ∃ n : ℕ, algebraMap Ω C (f l) ^ n * a q ∈ RC) ∧
          x = ∑ q, a q • bcMap Ω C ι (b q) := by
      intro x hx
      unfold spanOver at hx
      induction hx using AddSubgroup.closure_induction with
      | mem x hx =>
        obtain ⟨a, ha, y, ⟨v, hv, rfl⟩, rfl⟩ := hx
        obtain ⟨av, hav, rfl⟩ := (hiff v).1 ⟨0, by rw [pow_zero, one_smul]; exact hv⟩
        refine ⟨fun q => a * algebraMap Ω C (av q), fun q => ?_, ?_⟩
        · obtain ⟨n, hn⟩ := hav q
          exact ⟨n, by rw [mul_left_comm, ← map_pow, ← map_mul]; exact mul_mem ha (hRC _ hn)⟩
        · set_option synthInstance.maxHeartbeats 100000 in
            simp only [map_sum, map_smul, Finset.smul_sum]
          refine Finset.sum_congr rfl fun q _ => ?_
          rw [← algebraMap_smul C (av q), smul_smul]
      | zero => exact ⟨0, fun q => ⟨0, by simp⟩, by simp⟩
      | add x y _ _ hx hy =>
        obtain ⟨a, ha, rfl⟩ := hx
        obtain ⟨a', ha', rfl⟩ := hy
        refine ⟨a + a', fun q => ?_, by simp [add_smul, Finset.sum_add_distrib]⟩
        obtain ⟨n, hn⟩ := ha q
        obtain ⟨n', hn'⟩ := ha' q
        refine ⟨n + n', ?_⟩
        have h2 : algebraMap Ω C (f l) ^ (n + n') * (a + a') q =
            algebraMap Ω C (f l) ^ n' * (algebraMap Ω C (f l) ^ n * a q) +
              algebraMap Ω C (f l) ^ n * (algebraMap Ω C (f l) ^ n' * a' q) := by
          rw [Pi.add_apply]; ring
        rw [h2]
        exact add_mem (mul_mem (pow_mem hgR _) hn) (mul_mem (pow_mem hgR _) hn')
      | neg x _ hx =>
        obtain ⟨a, ha, rfl⟩ := hx
        refine ⟨-a, fun q => ?_, by simp [neg_smul, Finset.sum_neg_distrib]⟩
        obtain ⟨n, hn⟩ := ha q
        exact ⟨n, by rw [Pi.neg_apply, mul_neg]; exact neg_mem hn⟩
    obtain ⟨a, ha, hae⟩ := key _ hm
    refine ⟨fun q => (algebraMap Ω C (f l) ^ m)⁻¹ * a q, fun q => ?_, ?_⟩
    · obtain ⟨n, hn⟩ := ha q
      refine ⟨n + m, ?_⟩
      rw [pow_add, mul_assoc, ← mul_assoc (algebraMap Ω C (f l) ^ m),
        mul_inv_cancel₀ (pow_ne_zero _ hg'), one_mul]
      exact hn
    · have he : e = (algebraMap Ω C (f l) ^ m)⁻¹ • (algebraMap Ω C (f l) ^ m • e) := by
        rw [smul_smul, inv_mul_cancel₀ (pow_ne_zero _ hg'), one_smul]
      rw [he, hae, Finset.smul_sum]
      simp only [smul_smul]
  · rintro ⟨a, ha, rfl⟩
    choose na hna using ha
    choose mb hmb using hbl
    refine ⟨∑ q, na q + ∑ q, mb q, ?_⟩
    rw [Finset.smul_sum]
    refine AddSubgroup.sum_mem _ fun q _ => ?_
    have h1 : na q ≤ ∑ q, na q :=
      Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ q)
    have h2 : mb q ≤ ∑ q, mb q :=
      Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ q)
    have e1 : algebraMap Ω C (f l) ^ (∑ q, na q + ∑ q, mb q) =
        algebraMap Ω C (f l) ^ (∑ q, na q - na q) * algebraMap Ω C (f l) ^ na q *
          (algebraMap Ω C (f l) ^ (∑ q, mb q - mb q) * algebraMap Ω C (f l) ^ mb q) := by
      rw [← pow_add, ← pow_add, ← pow_add, Nat.sub_add_cancel h1, Nat.sub_add_cancel h2]
    have hcoef : algebraMap Ω C (f l) ^ (∑ q, na q - na q) *
        algebraMap Ω C (f l) ^ (∑ q, mb q - mb q) * (algebraMap Ω C (f l) ^ na q * a q) ∈ RC :=
      mul_mem (mul_mem (pow_mem hgR _) (pow_mem hgR _)) (hna q)
    have hmem : (algebraMap Ω C (f l) ^ (∑ q, na q - na q) *
        algebraMap Ω C (f l) ^ (∑ q, mb q - mb q) * (algebraMap Ω C (f l) ^ na q * a q)) •
          bcMap Ω C ι (f l ^ mb q • b q) ∈ spanOver RC (bcMap Ω C ι '' (L : Set (ι → Ω))) :=
      AddSubgroup.subset_closure ⟨_, hcoef, _, ⟨_, hmb q, rfl⟩, rfl⟩
    convert hmem using 1
    rw [map_smul, ← algebraMap_smul C (f l ^ mb q), smul_smul, smul_smul, map_pow, e1]
    congr 1
    ring

theorem main : ∀ {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {F : Type} [Zero F] [One F] [Fintype F] {n : ℕ} {Sg : Type} {r s : Sg → ℕ} (D : LieLatticeData Ω F n Sg r s) (R : Subalgebra o Ω) (p : ℕ) (w : Ω) (χ : Sg → F → Ω), CharData R p w χ → D.Base R p w → D.Good₁ R p χ → D.Good₂ R p χ → (∀ τ, mulLat w (stdLat R _) ≤ D.af R p (χ τ)) → (∀ τ, LocFree R (r τ) (D.kerH R p τ (χ τ)) ∧ ∀ i, LocFree R 1 (D.dId R p (χ τ) i) ∧ LocFree R 1 ((D.stepGraph τ (χ τ) i).comap (AddMonoidHom.inl _ _))) ∧ ∀ (C : Type) [Field C] [Algebra o C] [Algebra Ω C] [IsScalarTower o Ω C] (RC : Subalgebra o C), (∀ a ∈ R, algebraMap Ω C a ∈ RC) → (D.bc RC).Good₂ RC p (fun τ a => algebraMap Ω C (χ τ a)) ∧ ∀ τ, (D.bc RC).kerH RC p τ (fun a => algebraMap Ω C (χ τ a)) = spanOver RC (bcMap Ω C _ '' D.kerH R p τ (χ τ)) ∧ ∀ i, (D.bc RC).dId RC p (fun a => algebraMap Ω C (χ τ a)) i = spanOver RC (algebraMap Ω C '' D.dId R p (χ τ) i) ∧ ((D.bc RC).stepGraph τ (fun a => algebraMap Ω C (χ τ a)) i).comap (AddMonoidHom.inl _ _) = spanOver RC (algebraMap Ω C '' (D.stepGraph τ (χ τ) i).comap (AddMonoidHom.inl _ _)) := by
  intro o Ω _ _ _ F _ _ _ n Sg r s D R p w χ hc hB hG1 hG2 haf
  obtain ⟨hdL, hdB⟩ := GlobalTheory.T.character_lattice_fibre_ideal_locally_free D R p w χ hc hB hG1 hG2
  obtain ⟨hsL, hsB⟩ := GlobalTheory.T.character_lattice_graph_comap_locally_free D R p w χ hc hB hG1 hG2
  have hkL := GlobalTheory.T.character_lattice_kernel_locally_free D R p w χ hc hB hG1 hG2 haf
  have h68 := GlobalTheory.T.lattice_good_base_change D R p w χ hc hB hG1
  refine ⟨fun τ => ⟨hkL τ, fun i => ⟨hdL τ i, hsL τ i⟩⟩, ?_⟩
  intro C _ _ _ _ RC hRC
  have hbc := h68.2 C RC hRC
  have h69 := GlobalTheory.T.kernel_graph_base_change_holds D R p w χ hc hB hG1 C RC hRC
  have h70 := GlobalTheory.T.lattice_image_base_change D R p w χ hc hB hG1 haf C RC hRC
  refine ⟨⟨fun τ i => ?_, fun τ i => ?_, fun τ i => ?_, fun τ => ?_⟩,
    fun τ => ⟨GlobalTheory.T.character_lattice_base_change_free D R p w χ hc hB hG1 hG2 haf C RC hRC τ,
      fun i => ⟨hdB C RC hRC τ i, hsB C RC hRC τ i⟩⟩⟩
  · beta_reduce
    rw [(hbc.2 τ).1, ← span_bcMap_annSub Ω C n i]
    exact (GlobalTheory.T.locally_free_base_change_summand R RC hRC (bcMap Ω C (Fin n)) (isBaseChange_bcMap Ω C (Fin n))
      (D.af R p (χ τ)) (annSub Ω n i) (h68.1 τ).1.1 (hG2.ann τ i)).1
  · rw [(h69 τ).1 i]
    exact loc_free_base_change R RC hRC (hG2.kk τ i)
  · beta_reduce
    rw [(h69 τ).2 i,
      show AddMonoidHom.snd C (Fin (r τ) → C) = (LinearMap.snd C C (Fin (r τ) → C)).toAddMonoidHom
        from rfl, SpanExact.map_spanOver]
    have himg : (LinearMap.snd C C (Fin (r τ) → C)) ''
        (Prod.map (algebraMap Ω C) (bcMap Ω C (Fin (r τ))) '' (D.stepGraph τ (χ τ) i : Set _)) =
          bcMap Ω C (Fin (r τ)) ''
            ((D.stepGraph τ (χ τ) i).map (AddMonoidHom.snd Ω (Fin (r τ) → Ω)) : Set _) := by
      rw [AddSubgroup.coe_map, Set.image_image, Set.image_image]
      rfl
    rw [himg]
    exact loc_free_base_change R RC hRC (hG2.step τ i)
  · beta_reduce
    rw [h70 τ]
    exact loc_free_base_change R RC hRC (hG2.im τ)

end GlobalTheory.CompanionTheory.Ar.Num.LatticeGoodness
end
end

section

open GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.GR ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up

namespace GlobalTheory.CompanionTheory.Ar.PtSeq

theorem pt_seq_lin : ∀ {o C : Type} [CommRing o] [Field C] [Algebra o C] (RC : Subalgebra o C) (p : ℕ) {F : Type} [Zero F] [Fintype F] {n : ℕ} {Sg : Type} {r s : Sg → ℕ} (D : LieLatticeData C F n Sg r s) (w : C) (χ : Sg → F → C) (τ : Sg), w ≠ 0 → mulLat w (stdLat RC _) ≤ D.af RC p (χ τ) → D.af RC p (χ τ) ≤ stdLat RC _ → ∀ (ht : (Fin n → C) →ₗ[C] (Fin (s τ) → C)) (hb : (Fin (r τ) → C) →ₗ[C] (Fin n → C)), Function.Injective hb → LinearMap.range hb = LinearMap.ker ht → (stdLat RC _).map ht.toAddMonoidHom = D.omHT τ → (stdLat RC _).comap hb.toAddMonoidHom = D.W τ → (D.hh RC p (χ τ)).map ht.toAddMonoidHom = D.om τ → (D.hh RC p (χ τ)).comap hb.toAddMonoidHom = divLat w (D.lie τ) → (∀ b c, (b, c) ∈ D.Del τ ↔ w • b ∈ stdLat RC _ ∧ c - ht b ∈ D.omHT τ) → (∀ a b, (a, b) ∈ D.Gam τ ↔ w • a ∈ D.W τ ∧ b - hb a ∈ stdLat RC _) → D.imH RC p τ (χ τ) = D.om τ ∧ D.kerH RC p τ (χ τ) = divLat w (D.lie τ) :=
  @PositivityTheory.Xgn.t_pt_seq_lin

end GlobalTheory.CompanionTheory.Ar.PtSeq
end

section

open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.CompanionTheory.Relay.tensor_product_hopf_orders : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (N₁ : Type) [AddCommGroup N₁] [Fintype N₁] [DecidableEq N₁], ∀ (N₂ : Type) [AddCommGroup N₂] [Fintype N₂] [DecidableEq N₂], ∀ (A₁ : HopfOrder (C := C) R N₁) (A₂ : HopfOrder (C := C) R N₂), ∃ AA : HopfOrder (C := C) R (N₁ × N₂), AA.carrier = tens A₁.carrier A₂.carrier ∧ AA.carrier.map (LinearMap.funLeft R C (AddMonoidHom.inl N₁ N₂ : N₁ → N₁ × N₂)) = A₁.carrier ∧ AA.carrier.map (LinearMap.funLeft R C (AddMonoidHom.inr N₁ N₂ : N₂ → N₁ × N₂)) = A₂.carrier ∧ (∀ g ∈ AA.carrier, (fun z : N₁ × N₂ => g (z.1, 0)) ∈ AA.carrier) ∧ (∀ g ∈ AA.carrier, (fun z : N₁ × N₂ => g (0, z.2)) ∈ AA.carrier) ∧ ∀ c₁ c₂, HasColen R v A₁.carrier c₁ → HasColen R v A₂.carrier c₂ → HasColen R v AA.carrier (c₁ ^ Fintype.card N₂ * c₂ ^ Fintype.card N₁) := by
  first | exact @PositivityTheory.HtPt.Re.tens_hopf | exact PositivityTheory.HtPt.Re.tens_hopf
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.GR

theorem _root_.GlobalTheory.CompanionTheory.Relay.dual_tower_hodge_tate_datum : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) {R₀ : Type} [CommRing R₀] (g : ℕ) (B : BX R₀) (Tw : ATowerL R₀ p) (Dt : DualTower Tw) [Algebra (Tw.O : Type) C], v.Integers (Tw.O : Type) → v (p : C) < 1 → ∀ [Algebra ℤ_[p] (Tw.O : Type)] (Oe : Type) [CommRing Oe] [Algebra ℤ_[p] Oe] (σ : Oe ≃ₐ[ℤ_[p]] Oe) (cp : (Tw.O : Type)) (D : Dat p g B Tw Dt Oe σ cp) (G : Over (Spec (CommRingCat.of R₀))) [GrpObj G] [IsCommMonObj G] (e : ∀ R : LAlg R₀, B.G R → (sp (R₀ := R₀) (R : Type) ⟶ G)), (∀ R, Function.Bijective (e R)) → (∀ R x y, e R (x + y) = e R x * e R y) → (∀ {R S : LAlg R₀} (f : LHom R S) (x : B.G R), e S (B.map f x) = spMap f.1 ≫ e R x) → ∀ (G' : Over (Spec (CommRingCat.of (Tw.O : Type)))) [GrpObj G'] [IsCommMonObj G'] (ψ : G'.left ⟶ G.left), Geo.Tor.IsGrpPullback G' G (Spec.map (CommRingCat.ofHom (algebraMap R₀ (Tw.O : Type)))) ψ → ∃ pt : Nb p g → (sp (R₀ := (Tw.O : Type)) (Tw.O : Type) ⟶ G'), (∀ t, (pt t).left ≫ ψ = (e Tw.O (ptOf B D.L.τ t)).left) ∧ IsTorsPts G' p pt ∧ ∀ T : TorsRep G' p, D.evImg C = torsFun C T pt := by
  first | exact @PositivityTheory.HtPt.Rf.htd_tie | exact PositivityTheory.HtPt.Rf.htd_tie
end

section

open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg restrictChart fnField ck rootNum SameGeneric LatLE IsPull IsPullBC)

theorem _root_.GlobalTheory.T.injective_mod_p_lattice_character_bound : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω), Function.Injective (algebraMap O Ω) → ∀ {F : Type} [Zero F] [One F] [Fintype F] {n : ℕ} {Sg : Type} [Fintype Sg] {r s : Sg → ℕ} (p : ℕ), p.Prime → ∀ (w : O) (χ : Sg → F → O) (φ : Equiv.Perm Sg) (D : (∀ k, ι k) → LieLatticeData Ω F n Sg r s), IsLatticeFamily O x p w χ φ D → (∀ c, mseg x c ≠ 0 → (D c).Good₁ (chartRing O (mseg x) c) p (fun τ a => algebraMap O Ω (χ τ a))) → (∀ c, mseg x c ≠ 0 → (D c).Facts (chartRing O (mseg x) c) p (algebraMap O Ω w) (fun τ a => algebraMap O Ω (χ τ a)) φ) → ∀ τ, QuotExact O x (fun c => divLat (algebraMap O Ω w) ((D c).lie τ)) (fun c => (D c).W τ) (fun c => (D c).hh (chartRing O (mseg x) c) p (fun a => algebraMap O Ω (χ τ a))) (fun c => stdLat (chartRing O (mseg x) c) (Fin n)) (fun c => (D c).om τ) (fun c => (D c).omHT τ) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.RelSeq.relSeq | exact GlobalTheory.CompanionTheory.Ar.Num.RelSeq.relSeq | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.RelSeq.relSeq <;> assumption)
end

section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj

namespace GlobalTheory.CompanionTheory.Ar.Conj

theorem rho_hom : ∀ (R : Type) [CommRing R] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB R d O), ∃ ρ : O →+* Matrix (Fin d) (Fin d) R, ∀ a, ρ a = rho B a := by
  intro R _ d O _ _ B
  obtain ⟨ρ, h⟩ := GlobalTheory.ChF.linPart_act_ringHom R d B.G O B.A R (RingHom.id R)
  refine ⟨ρ, fun a => ?_⟩
  rw [(h a).2]
  ext i j
  rfl

end GlobalTheory.CompanionTheory.Ar.Conj
end

section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj

theorem _root_.GlobalTheory.T.alpha_beta_adjoint_exact : ∀ (R : Type) [CommRing R] (p : ℕ) [Fact p.Prime] [CharP R p] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB R d O), (∀ u y, u ⬝ᵥ beta B p y = pairH B (alpha B p u) y) ∧ beta B p ∘ₗ alpha B p = 0 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Conj.Isotropy.beta_comp_alpha | exact GlobalTheory.CompanionTheory.Ar.Conj.Isotropy.beta_comp_alpha | (intros; apply GlobalTheory.CompanionTheory.Ar.Conj.Isotropy.beta_comp_alpha <;> assumption)
end

section

open GlobalTheory.CompanionTheory.Ar.Crv

namespace GlobalTheory.CompanionTheory.Ar.Crv

theorem deg_le_deg_of_le : ∀ (K : Type) [Field K] (C : ACurve K) (V : Type) [AddCommGroup V] [Module K V] [FiniteDimensional K V] (L L' : C.I → AddSubgroup V), IsBun C L → IsBun C L' → (∀ i, L i ≤ L' i) → deg C L ≤ deg C L' :=
  @PositivityTheory.HtPt.Ch.deg_mono

end GlobalTheory.CompanionTheory.Ar.Crv
end

section

open GlobalTheory.CompanionTheory.Ar.Crv

namespace GlobalTheory.CompanionTheory.Ar.Crv.SubDegSes

theorem subDeg_ses : ∀ (K : Type) [Field K] (C : ACurve K) (V : Type) [AddCommGroup V] [Module K V] [FiniteDimensional K V] (V' : Type) [AddCommGroup V'] [Module K V'] [FiniteDimensional K V'] (V'' : Type) [AddCommGroup V''] [Module K V''] [FiniteDimensional K V''] (L : C.I → AddSubgroup V) (L' : C.I → AddSubgroup V') (L'' : C.I → AddSubgroup V'') (f : V →ₗ[K] V') (g : V' →ₗ[K] V'') (X : Submodule K V'), IsBun C L' → ShortExact C L L' L'' f g → subDeg C L' X ≤ subDeg C L (X.comap f) + subDeg C L'' (X.map g) :=
  @PositivityTheory.HtPt.Ch.subdeg_ses

end GlobalTheory.CompanionTheory.Ar.Crv.SubDegSes
end

section

open GlobalTheory.CompanionTheory.Ar.Crv

namespace GlobalTheory.CompanionTheory.Ar.Crv

theorem subDeg_le_map_of_injective : ∀ (K : Type) [Field K] (C : ACurve K) (V : Type) [AddCommGroup V] [Module K V] [FiniteDimensional K V] (V' : Type) [AddCommGroup V'] [Module K V'] [FiniteDimensional K V'] (L : C.I → AddSubgroup V) (L' : C.I → AddSubgroup V') (f : V →ₗ[K] V') (W : Submodule K V), IsBun C L → IsBun C L' → Function.Injective f → IsHom C L L' f → subDeg C L W ≤ subDeg C L' (W.map f) :=
  PositivityTheory.HtPt.Ch.deg_inj

end GlobalTheory.CompanionTheory.Ar.Crv
end

section

open GlobalTheory.CompanionTheory.Ar.Crv

namespace GlobalTheory.CompanionTheory.Ar.Crv

theorem subDeg_le_zero_of_trivial : ∀ (K : Type) [Field K] (C : ACurve K) (V : Type) [AddCommGroup V] [Module K V] [FiniteDimensional K V] (n : ℕ) (b : Module.Basis (Fin n) K V) (L : C.I → AddSubgroup V) (W : Submodule K V), (∀ i, IsLatOf C i b (L i)) → subDeg C L W ≤ 0 :=
  @PositivityTheory.HtPt.Ch.subdeg_trivial

end GlobalTheory.CompanionTheory.Ar.Crv
end
