module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.SelmerSpannedByKappaLaurent
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
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

private theorem padicInt_ringHom_finite_field_eq {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Finite K]
    (φ ψ : ℤ_[p] →+* K) (z : ℤ_[p]) : φ z = ψ z := by
  have key : ∀ χ : ℤ_[p] →+* K, IsLocalRing.maximalIdeal ℤ_[p] ≤ RingHom.ker χ := by
    intro χ
    have hne : RingHom.ker χ ≠ ⊥ := by
      intro h
      have hinj : Function.Injective χ := (RingHom.injective_iff_ker_eq_bot χ).mpr h
      haveI : Finite ℤ_[p] := Finite.of_injective χ hinj
      haveI : Infinite ℤ_[p] := Infinite.of_injective (Nat.cast : ℕ → ℤ_[p]) Nat.cast_injective
      exact not_finite ℤ_[p]
    have hmax : (RingHom.ker χ).IsMaximal := (RingHom.ker_isPrime χ).isMaximal hne
    exact (IsLocalRing.eq_maximalIdeal hmax).ge
  have h1 := key φ (PadicInt.sub_zmodRepr_mem z)
  have h2 := key ψ (PadicInt.sub_zmodRepr_mem z)
  rw [RingHom.mem_ker, map_sub, sub_eq_zero] at h1 h2
  rw [h1, h2, map_natCast, map_natCast]

theorem UpperTheory.V.Pa.testVal :
    ∀ (l : ℕ) [Fact l.Prime] (S : Ctx l), ∀ (R : Type) [CommRing R] [Algebra S.F R] (e : R →ₐ[S.F] S.F) (θ : S.U.AA →+* R), S.Test R e θ → (∀ c : S.O, θ (algebraMap S.B S.U.AA (algebraMap S.O S.B c)) = algebraMap S.F R (algebraMap S.x.A S.F (algebraMap S.O S.x.A c))) ∧ (∀ (g : S.G.G₀) (m : ℤ), θ (algebraMap S.B S.U.AA ((S.G.frame.eps S.O S.B g ^ m : S.Bˣ) : S.B)) = algebraMap S.F R (algebraMap S.x.A S.F ((S.G.frame.eps ℤ_[l] S.x.A g ^ m : S.x.Aˣ) : S.x.A))) ∧ θ (algebraMap S.B S.U.AA S.P.s) = algebraMap S.F R (algebraMap S.x.A S.F S.x.t) ∧ (∀ v i g, e (θ (algebraMap S.B S.U.AA (S.u.ψ v i g))) = algebraMap S.x.A S.F (S.x.ψ v i g)) ∧ ∀ v i, ∀ g ∈ S.G.frame.mu v, θ (algebraMap S.B S.U.AA (S.u.ψ v i g)) = 1 := by
  intro l _ S R _ _ e θ hT
  have hB : ∀ b : S.B, algebraMap S.B S.U.AA b = algebraMap S.Bh S.U.AA (algebraMap S.B S.Bh b) :=
    fun b => IsScalarTower.algebraMap_apply S.B S.Bh S.U.AA b
  have hO : ∀ c : S.O, θ (algebraMap S.B S.U.AA (algebraMap S.O S.B c)) =
      algebraMap S.F R (algebraMap S.x.A S.F (algebraMap S.O S.x.A c)) := by
    intro c
    obtain ⟨o, ho⟩ := S.oo_O c
    rw [hB, ← ho, hT.oo o, ho, S.rF_f, S.P.f.commutes]
  have hpr : ∀ b : S.Bh, S.pr0 (algebraMap S.Bh S.U.AA b) = b := by
    intro b
    have h1 := (Ctx.exists_pr S (algebraMap S.Bh S.U.AA b)).choose_spec
    have h2 : algebraMap S.Bh S.U.AA b - algebraMap S.Bh S.U.AA (S.pr0 (algebraMap S.Bh S.U.AA b))
        ∈ (1 : Submodule S.Bh S.U.AA) := by
      rw [← map_sub]
      exact Submodule.mem_one.mpr ⟨_, rfl⟩
    have h4 := (Submodule.disjoint_def.mp S.U.compl.disjoint) _ h2 h1
    rw [← map_sub] at h4
    have h5 := S.U.inj (h4.trans (map_zero _).symm)
    exact (sub_eq_zero.mp h5).symm
  refine ⟨hO, ?_, ?_, ?_, ?_⟩
  · intro g m
    rw [← map_zpow, ← map_zpow]
    show θ (algebraMap S.B S.U.AA (algebraMap S.O S.B (algebraMap ℤ_[l] S.O _))) = _
    rw [hO]
    congr 2
    change algebraMap S.O S.x.A (algebraMap ℤ_[l] S.O _) = algebraMap ℤ_[l] S.x.A (algebraMap ℤ_[l] ℤ_[l] _)
    rw [Algebra.algebraMap_self, RingHom.id_apply,
      IsScalarTower.algebraMap_apply ℤ_[l] S.x.K (PowerSeries S.x.K),
      IsScalarTower.algebraMap_apply S.O S.x.K (PowerSeries S.x.K)]
    congr 1
    exact padicInt_ringHom_finite_field_eq ((algebraMap S.O S.x.K).comp (algebraMap ℤ_[l] S.O)) (algebraMap ℤ_[l] S.x.K) _
  · obtain ⟨o, ho⟩ := S.ordinaryPointSection
    rw [hB, ← ho, hT.oo o, ho, S.rF_f, S.P.f_s]
  · intro v i g
    rw [hT.res, hB, hpr, S.rF_f]
    have h := congrArg (fun χ => ((χ g : S.x.Aˣ) : S.x.A)) (S.P.maps.2 v i)
    exact congrArg _ h
  · intro v i g hg
    have hψ : ((S.u.ψ v i g : S.Bˣ) : S.B) = algebraMap S.O S.B ((S.r.th v i ⟨g, hg⟩ : S.Oˣ) : S.O) :=
      (S.u.psi v i).mu ⟨g, hg⟩
    have h := congrArg (fun χ => ((χ g : S.x.Aˣ) : S.x.A)) (S.P.maps.2 v i)
    have h' : S.P.f ((S.u.ψ v i g : S.Bˣ) : S.B) = ((S.x.ψ v i g : S.x.Aˣ) : S.x.A) := h
    rw [hψ, hO, ← S.P.f.commutes, ← hψ, h', S.x.ψ_mu v i g hg]
    simp
end

section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

section SlopeTestRemainingChoices
variable {A Fr G : Type} [CommRing A] [CommRing Fr] [Algebra A Fr] [TopologicalSpace G] {I : Ideal A} {t : A}

private theorem ac_const (c : A) : AdicCont I fun _ : G => c := fun _ => IsLocallyConstant.const _

end SlopeTestRemainingChoices

private theorem adicCont_add_and_adicCont_mul {R G : Type} [CommRing R] [TopologicalSpace G] {I : Ideal R} {φ ψ : G → R}
    (hφ : AdicCont I φ) (hψ : AdicCont I ψ) :
    AdicCont I (fun g => φ g + ψ g) ∧ AdicCont I (fun g => φ g * ψ g) := by
  unfold AdicCont at *
  constructor
  · intro N
    simpa [map_add (f := _)] using (hφ N).comp₂ (hψ N) (· + ·)
  · intro N
    simpa [map_mul] using (hφ N).comp₂ (hψ N) (· * ·)

private theorem adicCont_neg_of_adicCont {R G : Type} [CommRing R] [TopologicalSpace G] {I : Ideal R} {φ : G → R}
    (hφ : AdicCont I φ) : AdicCont I (fun g => -φ g) := by
  unfold AdicCont at *
  intro N
  simpa [map_neg, Function.comp_def] using (hφ N).comp (fun y => -y)

private theorem adicCont_comp_inv_of_isTopologicalGroup {R G : Type} [CommRing R] [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    {I : Ideal R} {φ : G → R} (hφ : AdicCont I φ) : AdicCont I (fun g => φ g⁻¹) := by
  unfold AdicCont at *
  intro N
  exact (hφ N).comp_continuous continuous_inv

theorem UpperTheory.V.Pa.bndOps :
    ∀ (K G : Type) [Field K] [TopologicalSpace G] [Group G] [IsTopologicalGroup G], (∀ c : FractionRing (PowerSeries K), BndF (PowerSeries.X : PowerSeries K) fun _ : G => c) ∧ (∀ φ ψ : G → FractionRing (PowerSeries K), BndF (PowerSeries.X : PowerSeries K) φ → BndF (PowerSeries.X : PowerSeries K) ψ → (BndF (PowerSeries.X : PowerSeries K) fun g => φ g + ψ g) ∧ (BndF (PowerSeries.X : PowerSeries K) fun g => φ g * ψ g) ∧ (BndF (PowerSeries.X : PowerSeries K) fun g => -φ g) ∧ BndF (PowerSeries.X : PowerSeries K) fun g => φ g⁻¹) ∧ (∀ (ι : Type) (s : Finset ι) (φ : ι → G → FractionRing (PowerSeries K)), (∀ i ∈ s, BndF (PowerSeries.X : PowerSeries K) (φ i)) → BndF (PowerSeries.X : PowerSeries K) fun g => ∑ i ∈ s, φ i g) ∧ (∀ φ : G → PowerSeries K, AdicCont (Ideal.span {(PowerSeries.X : PowerSeries K)}) φ → BndF (PowerSeries.X : PowerSeries K) fun g => algebraMap (PowerSeries K) (FractionRing (PowerSeries K)) (φ g)) ∧ ∀ (φ : G → FractionRing (PowerSeries K)), BndF (PowerSeries.X : PowerSeries K) φ → ∃ s₀ : ℕ, ∀ s, s₀ ≤ s → ∃ φ' : G → PowerSeries K, AdicCont (Ideal.span {(PowerSeries.X : PowerSeries K)}) φ' ∧ ∀ g, algebraMap (PowerSeries K) (FractionRing (PowerSeries K)) (φ' g) = algebraMap (PowerSeries K) (FractionRing (PowerSeries K)) PowerSeries.X ^ s * φ g := by
  intro K G _ _ _ _
  have hconst : ∀ c : FractionRing (PowerSeries K), BndF (PowerSeries.X : PowerSeries K) fun _ : G => c := by
    intro c
    obtain ⟨⟨a, b⟩, rfl⟩ := IsLocalization.mk'_surjective (nonZeroDivisors (PowerSeries K)) c
    have hb : (b : PowerSeries K) ≠ 0 := nonZeroDivisors.coe_ne_zero b
    obtain ⟨v, hv⟩ := PowerSeries.isUnit_divided_by_X_pow_order hb
    obtain ⟨n, hbv⟩ : ∃ n : ℕ, (b : PowerSeries K) = PowerSeries.X ^ n * (v : PowerSeries K) :=
      ⟨(b : PowerSeries K).order.toNat, by rw [hv, PowerSeries.X_pow_order_mul_divXPowOrder]⟩
    have hb0 : algebraMap (PowerSeries K) (FractionRing (PowerSeries K)) b ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective (PowerSeries K) (FractionRing (PowerSeries K)))).mpr hb
    unfold BndF
    refine ⟨n, fun _ => a * ↑v⁻¹, ac_const _, fun _ => ?_⟩
    dsimp only
    rw [IsFractionRing.mk'_eq_div, mul_div_assoc', eq_div_iff hb0,
      ← map_mul (algebraMap (PowerSeries K) (FractionRing (PowerSeries K))),
      ← map_pow (algebraMap (PowerSeries K) (FractionRing (PowerSeries K))),
      ← map_mul (algebraMap (PowerSeries K) (FractionRing (PowerSeries K)))]
    congr 1
    rw [hbv, show a * ↑v⁻¹ * (PowerSeries.X ^ n * ↑v) = PowerSeries.X ^ n * a * (↑v⁻¹ * ↑v) by ring,
      Units.inv_mul, mul_one]
  have hops : ∀ φ ψ : G → FractionRing (PowerSeries K), BndF (PowerSeries.X : PowerSeries K) φ →
      BndF (PowerSeries.X : PowerSeries K) ψ →
      (BndF (PowerSeries.X : PowerSeries K) fun g => φ g + ψ g) ∧
      (BndF (PowerSeries.X : PowerSeries K) fun g => φ g * ψ g) ∧
      (BndF (PowerSeries.X : PowerSeries K) fun g => -φ g) ∧
      BndF (PowerSeries.X : PowerSeries K) fun g => φ g⁻¹ := by
    intro φ ψ hφ hψ
    unfold BndF at hφ hψ ⊢
    obtain ⟨s1, φ1, hc1, he1⟩ := hφ
    obtain ⟨s2, ψ2, hc2, he2⟩ := hψ
    refine ⟨⟨s1 + s2, fun g => PowerSeries.X ^ s2 * φ1 g + PowerSeries.X ^ s1 * ψ2 g, ?_, fun g => ?_⟩,
      ⟨s1 + s2, fun g => φ1 g * ψ2 g, (adicCont_add_and_adicCont_mul hc1 hc2).2, fun g => ?_⟩,
      ⟨s1, fun g => -φ1 g, adicCont_neg_of_adicCont hc1, fun g => ?_⟩,
      ⟨s1, fun g => φ1 g⁻¹, adicCont_comp_inv_of_isTopologicalGroup hc1, fun g => he1 g⁻¹⟩⟩
    · exact (adicCont_add_and_adicCont_mul (adicCont_add_and_adicCont_mul (ac_const _) hc1).2 (adicCont_add_and_adicCont_mul (ac_const _) hc2).2).1
    · simp only [map_add (f := _), map_mul, map_pow, he1, he2]
      ring
    · simp only [map_mul, he1, he2]
      ring
    · simp only [map_neg, he1]
      ring
  refine ⟨hconst, hops, ?_, ?_, ?_⟩
  · intro ι s φ hφ
    classical
    revert hφ
    refine Finset.induction_on s ?_ ?_
    · intro _
      simpa using hconst 0
    · intro a t hat ih hall
      have h1 := hall a (Finset.mem_insert_self a t)
      have h2 := ih (fun i hi => hall i (Finset.mem_insert_of_mem hi))
      simp only [Finset.sum_insert hat]
      exact (hops _ _ h1 h2).1
  · intro φ hφ
    unfold BndF
    exact ⟨0, φ, hφ, fun g => by simp⟩
  · intro φ hφ
    unfold BndF at hφ
    obtain ⟨s0, φ0, hc0, he0⟩ := hφ
    refine ⟨s0, fun s hs => ⟨fun g => PowerSeries.X ^ (s - s0) * φ0 g, (adicCont_add_and_adicCont_mul (ac_const _) hc0).2, fun g => ?_⟩⟩
    rw [map_mul, map_pow, he0, ← mul_assoc, ← pow_add, Nat.sub_add_cancel hs]
end

section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

section
variable {X : Type} [CommRing X] {a g : ℕ} {c : Fin a → Fin g → X}

private theorem rel_C (r : X) : DD.Rel c (DD.C r) (DD.C r) :=
  ⟨rfl, rfl, fun k => by simp, fun j => by simp⟩

private theorem rel_zero : DD.Rel c 0 0 :=
  ⟨rfl, rfl, fun k => by simp, fun j => by simp⟩

private theorem rel_one : DD.Rel c 1 1 :=
  ⟨rfl, rfl, fun k => by simp, fun j => by simp⟩

private theorem rel_add {u u' : DD X a} {v v' : DD X g} (h : DD.Rel c u v) (h' : DD.Rel c u' v') :
    DD.Rel c (u + u') (v + v') := by
  obtain ⟨a1, a2, a3, a4⟩ := h
  obtain ⟨b1, b2, b3, b4⟩ := h'
  refine ⟨by simp [a1, b1], by simp [a2, b2], fun k => ?_, fun j => ?_⟩
  · simp [a3, b3, mul_add, Finset.sum_add_distrib]
  · simp [a4, b4, mul_add, Finset.sum_add_distrib]

private theorem rel_neg {u : DD X a} {v : DD X g} (h : DD.Rel c u v) : DD.Rel c (-u) (-v) := by
  obtain ⟨a1, a2, a3, a4⟩ := h
  refine ⟨by simp [a1], by simp [a2], fun k => ?_, fun j => ?_⟩
  · simp [a3]
  · simp [a4]

private theorem rel_pair {p q : Fin a → X} {s t : Fin g → X} (h : ∀ k, p k = ∑ j, c k j * s j)
    (h' : ∀ j, t j = ∑ k, c k j * q k) : ∑ k, p k * q k = ∑ j, s j * t j := by
  simp only [h, h', Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring

private theorem rel_mul {u u' : DD X a} {v v' : DD X g} (h : DD.Rel c u v) (h' : DD.Rel c u' v') :
    DD.Rel c (u * u') (v * v') := by
  obtain ⟨a1, a2, a3, a4⟩ := h
  obtain ⟨b1, b2, b3, b4⟩ := h'
  refine ⟨by simp [a1, b1], ?_, fun k => ?_, fun j => ?_⟩
  · have e1 := rel_pair a3 b4
    have e2 := rel_pair b3 a4
    have e3 : ∑ k, u.ep' k * u'.ep k = ∑ j, v.ep' j * v'.ep j := by
      simpa only [mul_comm] using e2
    simp only [DD.mul_eta, Finset.sum_add_distrib, e1, e3, a1, a2, b1, b2]
  · simp only [DD.mul_ep, a3, b3, a1, b1, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  · simp only [DD.mul_ep', a4, b4, a1, b1, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring

private theorem rel_sum {ι : Type} (s : Finset ι) (f : ι → DD X a) (f' : ι → DD X g)
    (h : ∀ i, DD.Rel c (f i) (f' i)) : DD.Rel c (∑ i ∈ s, f i) (∑ i ∈ s, f' i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using rel_zero
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    exact rel_add (h i) ih

end

theorem UpperTheory.V.Pa.relSub :
    ∀ (X : Type) [CommRing X] (a g : ℕ) (c : Fin a → Fin g → X), (∀ r : X, DD.Rel c (DD.C r) (DD.C r)) ∧ (∀ u v u' v', DD.Rel c u v → DD.Rel c u' v' → DD.Rel c (u + u') (v + v') ∧ DD.Rel c (u - u') (v - v') ∧ DD.Rel c (u * u') (v * v')) ∧ (∀ u v v', DD.Rel c u v → DD.Rel c u v' → v.ep = v'.ep → v = v') ∧ ∀ (n : ℕ) (l : List (Matrix (Fin n) (Fin n) (DD X a) × Matrix (Fin n) (Fin n) (DD X g))), (∀ p ∈ l, ∀ i j, DD.Rel c (p.1 i j) (p.2 i j)) → ∀ i j, DD.Rel c ((l.map Prod.fst).prod i j) ((l.map Prod.snd).prod i j) := by
  intro X _ a g c
  refine ⟨rel_C, fun u v u' v' h h' => ⟨rel_add h h', ?_, rel_mul h h'⟩, ?_, ?_⟩
  · rw [sub_eq_add_neg, sub_eq_add_neg]
    exact rel_add h (rel_neg h')
  · rintro u v v' ⟨a1, a2, -, a4⟩ ⟨b1, b2, -, b4⟩ e
    exact DD.ext (a1.symm.trans b1) e (funext fun j => (a4 j).trans (b4 j).symm) (a2.symm.trans b2)
  · intro n l
    induction l with
    | nil =>
      intro _ i j
      simp only [List.map_nil, List.prod_nil, Matrix.one_apply]
      split_ifs
      · exact rel_one
      · exact rel_zero
    | cons p l ih =>
      intro h i j
      simp only [List.map_cons, List.prod_cons, Matrix.mul_apply]
      exact rel_sum _ _ _ fun k => rel_mul (h p (List.mem_cons_self ..) i k)
        (ih (fun q hq => h q (List.mem_cons_of_mem _ hq)) k j)
end

section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

private theorem exists_semilinear_functional_nonzero {O B F M : Type} [CommRing O] [IsLocalRing O] [CommRing B] [Field F] [AddCommGroup M]
    [Module B M] (φ : O →+* B) (f : O →+* F) (hf : Function.Surjective f)
    (hM : ∀ o ∈ maximalIdeal O, ∀ m : M, φ o • m = 0) (q : M) (hq : q ≠ 0) :
    ∃ Φ : M →+ F, (∀ o m, Φ (φ o • m) = f o * Φ m) ∧ Φ q ≠ 0 := by
  letI : Module O M := Module.compHom M φ
  haveI hmax : (RingHom.ker f).IsMaximal := RingHom.ker_isMaximal_of_surjective f hf
  have hker : RingHom.ker f = maximalIdeal O := IsLocalRing.eq_maximalIdeal hmax
  have hT : Module.IsTorsionBySet O M (RingHom.ker f) := by
    rintro m ⟨o, ho⟩
    exact hM o (hker ▸ ho) m
  letI : Field (O ⧸ RingHom.ker f) := Ideal.Quotient.field _
  letI : Module (O ⧸ RingHom.ker f) M := hT.module
  haveI : Module.Free (O ⧸ RingHom.ker f) M := Module.Free.of_divisionRing _ _
  haveI : Module.Projective (O ⧸ RingHom.ker f) M := Module.Projective.of_free
  obtain ⟨Ψ, hΨ⟩ := Module.Projective.exists_dual_ne_zero (O ⧸ RingHom.ker f) hq
  let e := RingHom.quotientKerEquivOfSurjective hf
  refine ⟨(e : (O ⧸ RingHom.ker f) →+* F).toAddMonoidHom.comp Ψ.toAddMonoidHom, fun o m => ?_, ?_⟩
  · show e (Ψ (φ o • m)) = f o * e (Ψ m)
    have hs : (φ o • m : M) = (Ideal.Quotient.mk (RingHom.ker f) o) • m := (hT.mk_smul o m).symm
    rw [hs, map_smul, smul_eq_mul, map_mul, RingHom.quotientKerEquivOfSurjective_apply_mk]
  · show e (Ψ q) ≠ 0
    exact fun h => hΨ (e.injective (h.trans (map_zero e).symm))

theorem UpperTheory.V.Pa.phSep :
    ∀ (l : ℕ) [Fact l.Prime] (S : Ctx l), ∀ y : S.U.N, (∀ Φ ∈ S.Ph, Φ y = 0) → y ∈ S.J2 • (⊤ : Submodule S.Bh S.U.N) := by
  intro l _ S y hy
  by_contra hne
  let P := S.J2 • (⊤ : Submodule S.Bh S.U.N)
  have hq : (Submodule.Quotient.mk y : S.U.N ⧸ P) ≠ 0 := by
    rw [Ne, Submodule.Quotient.mk_eq_zero]
    exact hne
  have hJ : ∀ b ∈ S.J2, ∀ z : S.U.N, b • z ∈ P := fun b hb z => Submodule.smul_mem_smul hb trivial
  have hM : ∀ o ∈ maximalIdeal S.OO, ∀ m : S.U.N ⧸ P, algebraMap S.OO S.Bh o • m = 0 := by
    intro o ho m
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective P m
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    exact hJ _ (Ideal.mem_sup_left (Ideal.mem_sup_left (Ideal.mem_map_of_mem _ ho))) z
  obtain ⟨Φ0, hΦ0, hne0⟩ :=
    exists_semilinear_functional_nonzero (algebraMap S.OO S.Bh) (S.rF.comp (algebraMap S.OO S.Bh)) S.oo_surj hM _ hq
  let Φ : S.U.N →+ S.F := Φ0.comp P.mkQ.toAddMonoidHom
  have hmem : Φ ∈ S.Ph := by
    refine ⟨fun o z => ?_, fun b hb z => ?_⟩
    · show Φ0 (P.mkQ (algebraMap S.OO S.Bh o • z)) = S.rF (algebraMap S.OO S.Bh o) * Φ0 (P.mkQ z)
      rw [map_smul]
      exact hΦ0 o _
    · show Φ0 (P.mkQ (b • z)) = 0
      rw [Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero P).mpr (hJ b hb z), map_zero]
  exact hne0 (hy Φ hmem)
end

section

noncomputable section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools

namespace UpperTheory.V.Pa

def _root_.UpperTheory.V.W.DD.map {X Y : Type} [CommRing X] [CommRing Y] {g : ℕ} (f : X →+* Y) : DD X g →+* DD Y g where
  toFun u := ⟨f u.a, fun j => f (u.ep j), fun j => f (u.ep' j), f u.eta⟩
  map_one' := by ext <;> simp
  map_zero' := by ext <;> simp
  map_add' x y := by ext <;> simp
  map_mul' x y := by ext <;> simp

def DD.aug (X : Type) [CommRing X] (g : ℕ) : DD X g →ₐ[X] X where
  toFun u := u.a
  map_one' := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  commutes' _ := rfl

variable {l : ℕ} [Fact l.Prime] {L : Loc} {G G0 : Glob l L} (h : G.Hom G0) {n : ℕ} (x : NP G0.frame n) {e : ℕ}

def epC (u : G.G₀ → Matrix (Fin n) (Fin n) (DD x.Fr e)) (k : Fin e) (γ : G.G₀) : Matrix (Fin n) (Fin n) x.Fr :=
  (u γ).map (fun a => a.ep k) * x.ρX x.Fr (h.p₀ γ⁻¹)

def epC' (u : G.G₀ → Matrix (Fin n) (Fin n) (DD x.Fr e)) (k : Fin e) (γ : G.G₀) : Matrix (Fin n) (Fin n) x.Fr :=
  (u γ).map (fun a => a.ep' k) * x.ρX x.Fr (h.p₀ γ⁻¹)

structure DefU (u : G.G₀ → Matrix (Fin n) (Fin n) (DD x.Fr e)) (ψ : ∀ v, Fin n → L.Gv v →* (DD x.Fr e)ˣ) : Prop where
  one : u 1 = 1
  mul : ∀ g g', u (g * g') = u g * u g'
  red : ∀ g, (u g).map (fun a => a.a) = x.ρX x.Fr (h.p₀ g)
  even : ∀ g, u g ∈ blkMat n x.a (ddPart x.A x.Fr e true false true false) (ddPart x.A x.Fr e false true false true)
  form : ∀ g, (u g)ᵀ * u (G.frame.conj g) =
    algebraMap x.A (DD x.Fr e) ((G.frame.eps ℤ_[l] x.A g ^ (1 - (n : ℤ)) : x.Aˣ) : x.A) • (1 : Matrix (Fin n) (Fin n) (DD x.Fr e))
  ine : ∀ w, ∀ g ∈ G.frame.Iu w, u g = 1
  ψ_red : ∀ v i g, ((ψ v i g : (DD x.Fr e)ˣ) : DD x.Fr e).a = algebraMap x.A x.Fr (x.ψ v i g)
  ψ_even : ∀ v i g, ((ψ v i g : (DD x.Fr e)ˣ) : DD x.Fr e) ∈ ddPart x.A x.Fr e true false true false
  ψ_mu : ∀ v i, ∀ g ∈ G.frame.mu v, ψ v i g = 1
  ord : ∀ v (g : Fin n → L.Gv v), (List.ofFn fun i => u (G.φ v (g i)) -
    algebraMap (DD x.Fr e) (Matrix (Fin n) (Fin n) (DD x.Fr e)) (ψ v i (g i))).prod = 0
  bnd : BndD x.t u

end UpperTheory.V.Pa
end
end

section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

theorem UpperTheory.V.Pa.prAdd :
    ∀ (l : ℕ) [Fact l.Prime] (S : Ctx l), (∀ a, algebraMap S.Bh S.U.AA (S.pr0 a) + (S.pr1 a : S.U.AA) = a) ∧ (∀ (b : S.Bh) (y : S.U.N), S.pr0 (algebraMap S.Bh S.U.AA b + y) = b ∧ S.pr1 (algebraMap S.Bh S.U.AA b + y) = y) ∧ (∀ a a', S.pr0 (a + a') = S.pr0 a + S.pr0 a' ∧ S.pr1 (a + a') = S.pr1 a + S.pr1 a') ∧ (∀ (b : S.Bh) a, S.pr0 (b • a) = b * S.pr0 a ∧ S.pr1 (b • a) = b • S.pr1 a) ∧ (∀ a a', S.pr0 (a * a') - S.pr0 a * S.pr0 a' ∈ ired S.U.N ∧ S.pr1 (a * a') = S.pr0 a • S.pr1 a' + S.pr0 a' • S.pr1 a) ∧ ired S.U.N ≤ maximalIdeal S.Bh ∧ S.J2 ≤ maximalIdeal S.Bh := by
  intro l _ S
  have h1 : ∀ a, algebraMap S.Bh S.U.AA (S.pr0 a) + (S.pr1 a : S.U.AA) = a := by
    intro a
    simp [Ctx.pr1]
  have h2 : ∀ (b : S.Bh) (y : S.U.N), S.pr0 (algebraMap S.Bh S.U.AA b + y) = b ∧
      S.pr1 (algebraMap S.Bh S.U.AA b + y) = y := by
    intro b y
    have e := h1 (algebraMap S.Bh S.U.AA b + y)
    have hm : algebraMap S.Bh S.U.AA (S.pr0 (algebraMap S.Bh S.U.AA b + y) - b) ∈ S.U.N := by
      have : algebraMap S.Bh S.U.AA (S.pr0 (algebraMap S.Bh S.U.AA b + y) - b) =
          (y : S.U.AA) - (S.pr1 (algebraMap S.Bh S.U.AA b + y) : S.U.AA) := by
        rw [map_sub]; linear_combination e
      rw [this]
      exact S.U.N.sub_mem y.2 (S.pr1 _).2
    have hz : algebraMap S.Bh S.U.AA (S.pr0 (algebraMap S.Bh S.U.AA b + y) - b) = 0 :=
      Submodule.disjoint_def.1 S.U.compl.disjoint _ (Submodule.mem_one.2 ⟨_, rfl⟩) hm
    have hb : S.pr0 (algebraMap S.Bh S.U.AA b + y) = b :=
      sub_eq_zero.1 (S.U.inj (by rw [hz, map_zero]))
    refine ⟨hb, Subtype.ext ?_⟩
    rw [hb] at e
    exact add_left_cancel e
  have key : ∀ (a : S.U.AA) (b : S.Bh) (y : S.U.N), a = algebraMap S.Bh S.U.AA b + y →
      S.pr0 a = b ∧ S.pr1 a = y := by
    rintro a b y rfl
    exact h2 b y
  have hi : ired S.U.N ≤ maximalIdeal S.Bh := by
    refine Ideal.span_le.2 ?_
    rintro b ⟨x, hx, y, hy, e⟩
    obtain ⟨c, hc, e'⟩ := S.U.mul_mem x hx y hy
    have : b = c := S.U.inj (e.symm.trans e')
    rw [this]; exact hc
  refine ⟨h1, h2, fun a a' => key _ _ _ ?_, fun b a => key _ _ _ ?_, fun a a' => ?_, hi, ?_⟩
  · rw [map_add (f := _), Submodule.coe_add]
    linear_combination - h1 a - h1 a'
  · rw [map_mul, Submodule.coe_smul, Algebra.smul_def, Algebra.smul_def, ← mul_add, h1]
  · obtain ⟨c, -, e⟩ := S.U.mul_mem _ (S.pr1 a).2 _ (S.pr1 a').2
    have := key (a * a') (S.pr0 a * S.pr0 a' + c) (S.pr0 a • S.pr1 a' + S.pr0 a' • S.pr1 a) (by
      rw [map_add (f := _), map_mul, Submodule.coe_add, Submodule.coe_smul, Submodule.coe_smul, Algebra.smul_def,
        Algebra.smul_def, ← e]
      have e1 := h1 a
      have e2 := h1 a'
      linear_combination (- a') * e1 - (algebraMap S.Bh S.U.AA (S.pr0 a) + (S.pr1 a : S.U.AA)) * e2)
    refine ⟨?_, this.2⟩
    rw [this.1, add_sub_cancel_left]
    exact Ideal.subset_span ⟨_, (S.pr1 a).2, _, (S.pr1 a').2, e⟩
  · refine sup_le (sup_le ?_ (Ideal.pow_le_self two_ne_zero)) hi
    exact ((IsLocalRing.local_hom_tfae (algebraMap S.OO S.Bh)).out 1 3).1 (IsCO.isLocalHom (O := S.OO) (R := S.Bh))
end

section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

theorem UpperTheory.V.Pa.prVr :
    ∀ (l : ℕ) [Fact l.Prime] (S : Ctx l), ∀ g (i j : Fin S.n), S.rF (S.pr0 (S.U.vr g i j)) = S.ρ S.F g i j ∧ ((((i : ℕ) < S.x.a) ↔ ((j : ℕ) < S.x.a)) → S.pr1 (S.U.vr g i j) = 0) ∧ (¬ (((i : ℕ) < S.x.a) ↔ ((j : ℕ) < S.x.a)) → S.pr0 (S.U.vr g i j) = 0) := by
  intro l _ S g i j
  have hm : S.U.vr g ∈ blkMat S.n S.x.a (1 : Submodule S.Bh S.U.AA) S.U.N := by
    rw [← S.U.span]; exact Submodule.subset_span ⟨g, rfl⟩
  have hN : S.U.vr g i j - algebraMap S.Bh S.U.AA (S.pr0 (S.U.vr g i j)) ∈ S.U.N := (S.pr1 (S.U.vr g i j)).2
  have hd := Submodule.disjoint_def.1 S.U.compl.disjoint
  have h1 : algebraMap S.Bh S.U.AA (S.pr0 (S.U.vr g i j)) ∈ (1 : Submodule S.Bh S.U.AA) :=
    Submodule.mem_one.2 ⟨_, rfl⟩
  refine ⟨S.U.red g i j _ hN, fun e => ?_, fun e => ?_⟩
  · exact Subtype.ext (hd _ (Submodule.sub_mem _ ((hm i j).1 e) h1) hN)
  · apply S.U.inj
    rw [map_zero]
    refine hd _ h1 ?_
    have := S.U.N.sub_mem ((hm i j).2 e) hN
    rwa [sub_sub_cancel] at this
end
