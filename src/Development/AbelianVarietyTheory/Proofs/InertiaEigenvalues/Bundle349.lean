module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle308
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle337
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle314
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle316
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
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
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle008
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle009
import Formalism.SharpRestriction.LevelLetterCocycles.DeltaInvariantLattices
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle292

@[expose] public section

section

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pass GlobalTheory.Cut GlobalTheory.UseLoc Module TensorProduct GlobalTheory.UseLoc.Cases

namespace GlobalTheory.UseLoc.Cases

section Gen

variable {G : Type} [Group G] {O LL : Type} [CommRing O] [Field LL] [Algebra O LL]

theorem actT_latOne (hinj : Function.Injective (algebraMap O LL)) (ψ : G →* Oˣ) (g : G) :
    actT (latOne (LL := LL) hinj ψ) g = ((ψ g : Oˣ) : O) • LinearMap.id := by
  ext t
  change Formalism.WeaklyAdmissibleFiltrations.charRep (tableLineDegreeTwo.charL (LL := LL) ψ) g (t : LL) = (((ψ g : Oˣ) : O) • t : LL)
  simp [Formalism.WeaklyAdmissibleFiltrations.charRep, tableLineDegreeTwo.charL, Algebra.smul_def]

theorem actTw_latOne [TopologicalSpace G] (hinj : Function.Injective (algebraMap O LL)) (ψ : G →* Oˣ) (X : Type)
    [AddCommGroup X] [Module O X] (g : G) :
    tableLineDegreeTwo.actTw (latOne (LL := LL) hinj ψ) X ψ g = LinearMap.id := by
  rw [tableLineDegreeTwo.actTw, actT_latOne, LinearMap.rTensor_smul, LinearMap.rTensor_id, smul_smul]
  simp

theorem eq_zero_of_isUnr_latOne [TopologicalSpace G] (hinj : Function.Injective (algebraMap O LL)) (ψ : G →* Oˣ)
    (X : Type) [AddCommGroup X] [Module O X] (I : Subgroup G) (z : G → ↥(latOne (LL := LL) hinj ψ).T ⊗[O] X)
    (h : tableLineDegreeTwo.IsUnr (latOne (LL := LL) hinj ψ) X ψ I z) : ∀ g ∈ I, z g = 0 := by
  obtain ⟨m, hm⟩ := h
  intro g hg
  rw [hm g hg, actTw_latOne, LinearMap.id_apply, sub_self]

theorem mem_Z1urD_of_eq_zero {V : Type} [AddCommGroup V] [Module LL V] [Module O V] [IsScalarTower O LL V]
    {ρ : Representation LL G V} (L : Lattice (O := O) ρ) (I : Subgroup G) (c : G → V ⧸ L.T)
    (h : ∀ g ∈ I, c g = 0) : c ∈ Z1urD L I :=
  ⟨0, fun g hg => by rw [h g hg, map_zero, sub_zero]⟩

end Gen

end GlobalTheory.UseLoc.Cases

theorem GlobalTheory.UseLoc.Cases.readU_unr : ∀ (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (lam : ↥(OL C.LL)) (θ : Br.G D.nbr i w hw →* (↥(OL C.LL))ˣ) (a : ℕ) (I : Subgroup (Br.G D.nbr i w hw))
    (z' : Br.G D.nbr i w hw → ↥(latOne (LL := ↥C.LL.1) Subtype.val_injective (chiT C θ 1)).T ⊗[↥(OL C.LL)] ↥(Xq ↥C.LL.1 lam a)),
    tableLineDegreeTwo.IsUnr (latOne (LL := ↥C.LL.1) Subtype.val_injective (chiT C θ 1)) ↥(Xq ↥C.LL.1 lam a) (chiT C θ 1) I z' →
    (fun g => iotaC ↥C.LL.1 lam a (z' g)) ∈ Z1urD (latC C (locOC C (chiRatO D.nd i 1))) I := by
  intro D i w hw C lam θ a I z' h
  exact GlobalTheory.UseLoc.Cases.mem_Z1urD_of_eq_zero _ I _ (fun g hg =>
    (congrArg (iotaC ↥C.LL.1 lam a) (GlobalTheory.UseLoc.Cases.eq_zero_of_isUnr_latOne _ _ _ I z' h g hg)).trans (map_zero _))
end

section

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pass GlobalTheory.Cut GlobalTheory.UseLoc Module TensorProduct GlobalTheory.UseLoc.Cases

noncomputable section

namespace GlobalTheory.UseLoc.Cases

theorem chiT_one_eq {D : D7} {i : D.nd.Loc} {w : HeightOneSpectrum (𝓞 D.host.E)} {hw : w ∈ placesOver D.host.E (D.nd.l i)}
    (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (θ : Br.G D.nbr i w hw →* (↥(OL C.LL))ˣ) : chiT C θ 1 = θ := by
  simp [chiT, chiOC]

section GenRead

variable {O : Type} [CommRing O] {LL : Type} [Field LL] [Algebra O LL] {k : ℕ}

def iotaL (hinj : Function.Injective (algebraMap O LL)) {G : Type} [Group G]
    (M N : G →* Matrix (Fin k) (Fin k) O) (lam : O) (a : ℕ) :
    ↥(stdLatG (LL := LL) hinj M).T ⊗[O] ↥(Xq LL lam a) →ₗ[O] (Fin k → LL) ⧸ (stdLatG (LL := LL) hinj N).T :=
  iotaW LL lam a k

theorem iotaL_tmul (hinj : Function.Injective (algebraMap O LL)) {G : Type} [Group G]
    (M N : G →* Matrix (Fin k) (Fin k) O) (lam : O) (a : ℕ) (t : ↥(stdLatG (LL := LL) hinj M).T)
    (x : ↥(Xq LL lam a)) (s : LL) (hs : Submodule.Quotient.mk s = (x : LL ⧸ intO (O := O) LL)) :
    iotaL hinj M N lam a (t ⊗ₜ x) = Submodule.Quotient.mk (s • (t : Fin k → LL)) := by
  obtain ⟨x, hx⟩ := x
  change Submodule.Quotient.mk s = x at hs
  subst hs
  rfl

theorem matRep_twistM_apply {G : Type} [Group G] (N : G →* Matrix (Fin k) (Fin k) O) (θ : G →* Oˣ) (g : G)
    (v : Fin k → LL) :
    matRep (mapM (algebraMap O LL) (twistM N θ)) g v = ((θ g : Oˣ) : O) • matRep (mapM (algebraMap O LL) N) g v := by
  have hM : (mapM (algebraMap O LL) (twistM N θ)) g =
      algebraMap O LL ((θ g : Oˣ) : O) • (mapM (algebraMap O LL) N) g := by
    ext p q
    simp [mapM, twistM, Matrix.smul_apply, smul_eq_mul, map_mul]
  change ((mapM (algebraMap O LL) (twistM N θ)) g).mulVec v = ((θ g : Oˣ) : O) • ((mapM (algebraMap O LL) N) g).mulVec v
  rw [hM, Matrix.smul_mulVec, algebraMap_smul]

theorem actD_iotaL (hinj : Function.Injective (algebraMap O LL)) {G : Type} [Group G] [TopologicalSpace G]
    (N : G →* Matrix (Fin k) (Fin k) O) (θ χ : G →* Oˣ) (hχ : ∀ g, (((χ g)⁻¹ : Oˣ) : O) * ((θ g : Oˣ) : O) = 1)
    (lam : O) (a : ℕ) (g : G) (y : ↥(stdLatG (LL := LL) hinj (twistM N θ)).T ⊗[O] ↥(Xq LL lam a)) :
    actD (stdLatG hinj N) g (iotaL hinj (twistM N θ) N lam a y) =
      iotaL hinj (twistM N θ) N lam a (tableLineDegreeTwo.actTw (stdLatG hinj (twistM N θ)) ↥(Xq LL lam a) χ g y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add u v hu hv => simp only [map_add (f := _), hu, hv]
  | tmul t x =>
    obtain ⟨s, hs⟩ := Submodule.Quotient.mk_surjective _ (x : LL ⧸ intO (O := O) LL)
    rw [tableLineDegreeTwo.actTw, LinearMap.smul_apply, LinearMap.rTensor_tmul, map_smul, iotaL_tmul hinj _ N lam a _ x s hs,
      iotaL_tmul hinj _ N lam a _ x s hs, ← Submodule.Quotient.mk_smul]
    change Submodule.Quotient.mk (matRep (mapM (algebraMap O LL) N) g (s • (t : Fin k → LL))) =
      Submodule.Quotient.mk ((((χ g)⁻¹ : Oˣ) : O) • s • matRep (mapM (algebraMap O LL) (twistM N θ)) g (t : Fin k → LL))
    congr 1
    rw [matRep_twistM_apply, LinearMap.map_smul, smul_comm _ s, ← mul_smul, hχ g, one_smul]

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR] [Algebra Qp LL]
    [TopologicalSpace (Fin k → LL)] [ContinuousAdd (Fin k → LL)] [ContinuousConstSMul LL (Fin k → LL)]

theorem readW_gen (PD : PeriodData G Qp K₀ K B BdR) (hinj : Function.Injective (algebraMap O LL))
    (N : G →* Matrix (Fin k) (Fin k) O) (θ χ : G →* Oˣ) (hχ : ∀ g, (((χ g)⁻¹ : Oˣ) : O) * ((θ g : Oˣ) : O) = 1)
    (lam : O) (a : ℕ) (z' : G → ↥(stdLatG (LL := LL) hinj (twistM N θ)).T ⊗[O] ↥(Xq LL lam a))
    (hz : tableLineDegreeTwo.InHfX PD (stdLatG (LL := LL) hinj (twistM N θ)) (stdLatG hinj N) ↥(Xq LL lam a) χ z') :
    (fun g => iotaL hinj (twistM N θ) N lam a (z' g)) ∈ HfD PD (stdLatG (LL := LL) hinj N) := by
  obtain ⟨n, c, x, m, hc, hz⟩ := hz
  choose s hs using fun j => Submodule.Quotient.mk_surjective _ (x j : LL ⧸ intO (O := O) LL)
  have e : (fun g => iotaL hinj (twistM N θ) N lam a (z' g)) =
      (∑ j, LinearMap.compLeft (stdLatG (LL := LL) hinj N).T.mkQ G (s j • fun g => (c j g : Fin k → LL))) +
        LinearMap.pi (fun g => actD (stdLatG (LL := LL) hinj N) g - LinearMap.id)
          (iotaL hinj (twistM N θ) N lam a m) := by
    funext g

    rw [hz g, map_add (f := _), map_sum, map_sub, ← actD_iotaL hinj N θ χ hχ lam a g m]
    simp only [Pi.add_apply, Finset.sum_apply, LinearMap.pi_apply, LinearMap.sub_apply, LinearMap.id_apply]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [iotaL_tmul hinj _ N lam a _ (x j) (s j) (hs j)]
    rfl
  rw [e]
  refine add_mem (Submodule.sum_mem _ fun j _ => Submodule.mem_sup_left (Submodule.mem_map_of_mem ?_))
    (Submodule.mem_sup_right (LinearMap.mem_range_self _ _))
  exact (Submodule.restrictScalars_mem O _ _).2 ((finiteCocycles PD _).smul_mem (s j) (hc j).2)

end GenRead

theorem chiT_one_inv_mul {D : D7} {i : D.nd.Loc} {w : HeightOneSpectrum (𝓞 D.host.E)}
    {hw : w ∈ placesOver D.host.E (D.nd.l i)} (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (θ : Br.G D.nbr i w hw →* (↥(OL C.LL))ˣ)
    (g : Br.G D.nbr i w hw) :
    (((chiT C θ 1 g)⁻¹ : (↥(OL C.LL))ˣ) : ↥(OL C.LL)) * ((θ g : (↥(OL C.LL))ˣ) : ↥(OL C.LL)) = 1 := by
  rw [chiT_one_eq]
  simp

theorem readW_main : ∀ (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (lam : ↥(OL C.LL)) {k : ℕ} (N : Br.G D.nbr i w hw →* Matrix (Fin k) (Fin k) ↥(OL C.LL))
    (θ : Br.G D.nbr i w hw →* (↥(OL C.LL))ˣ) (a : ℕ) (z' : Br.G D.nbr i w hw → ↥(latC C (twistM N θ)).T ⊗[↥(OL C.LL)] ↥(Xq ↥C.LL.1 lam a)),
    tableLineDegreeTwo.InHfX (Br.PD D.loc D.nbr i w hw) (latC C (twistM N θ)) (latC C N) ↥(Xq ↥C.LL.1 lam a) (chiT C θ 1) z' →
    (fun g => iotaW ↥C.LL.1 lam a k (z' g)) ∈ HfD (Br.PD D.loc D.nbr i w hw) (latC C N) := by
  intro D i w hw C lam k N θ a z' hz
  exact readW_gen (Br.PD D.loc D.nbr i w hw) Subtype.val_injective N θ (chiT C θ 1) (chiT_one_inv_mul C θ) lam a z' hz

end GlobalTheory.UseLoc.Cases

end
end

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices GlobalTheory.WeakClosed
open scoped Topology PowerSeries.WithPiTopology



noncomputable section

namespace GlobalTheory.WeakClosed

theorem lt_of_mem_span_pow {l : ℕ} [Fact l.Prime] (ϖ : OCb l) (hϖ : ¬ IsUnit ϖ)
    (hdiv : ∀ a : OCb l, a ≠ 0 → ∃ m : ℕ, a ∣ ϖ ^ m) (c : Cb l) (hc : c ≠ 0) :
    ∃ m : ℕ, ∀ x ∈ Ideal.span {ϖ ^ m},
      (cbValued l).v (algebraMap (OCb l) (Cb l) x) < (cbValued l).v c := by
  letI := cbValued l
  have hle : ∀ x y : Cb l, Valued.v x ≤ Valued.v y ↔
      ∃ e : OCb l, algebraMap (OCb l) (Cb l) e * y = x := by
    intro x y
    change (∃ e : OCb l, e • y = x) ↔ _
    simp only [Algebra.smul_def]
  have hinj := IsFractionRing.injective (OCb l) (Cb l)
  obtain ⟨a, d, hd, rfl⟩ := IsFractionRing.div_surjective (OCb l) c
  have hd0 : algebraMap (OCb l) (Cb l) d ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hd
  have ha : a ≠ 0 := by
    rintro rfl
    simp at hc
  obtain ⟨m₀, b, hb⟩ := hdiv a ha
  refine ⟨m₀ + 1, fun x hx => ?_⟩
  obtain ⟨t, rfl⟩ := Ideal.mem_span_singleton'.1 hx
  change Valued.v _ < Valued.v _
  rw [← not_le, hle]
  rintro ⟨e, he⟩
  rw [eq_div_iff hd0] at he
  have he' : e * (t * ϖ ^ (m₀ + 1)) * d = a := hinj (by rw [map_mul, map_mul]; exact he)
  apply hϖ
  have h0 : a * (1 - ϖ * (e * t * d * b)) = 0 := by
    linear_combination (-1 : OCb l) * he' + e * t * d * ϖ * hb
  rcases mul_eq_zero.1 h0 with h | h
  · exact absurd h ha
  · exact isUnit_iff_exists_inv.2 ⟨e * t * d * b, (sub_eq_zero.1 h).symm⟩

theorem weakly_small : ∀ {l : ℕ} [Fact l.Prime] (ϖ : OCb l), ¬ IsUnit ϖ →
    (∀ a : OCb l, a ≠ 0 → ∃ m : ℕ, a ∣ ϖ ^ m) →
      (letI := wTop l
       ∀ U ∈ 𝓝 (0 : WCb l), ∃ N m : ℕ, ∀ w : Ainf l,
         (∀ n < N, w.coeff n ∈ Ideal.span {ϖ ^ m}) → inclW l w ∈ U) := by
  intro l _ ϖ hϖ hdiv
  letI := wTop l
  letI := cbTop l
  intro U hU
  rw [nhds_induced] at hU
  obtain ⟨t, ht, htU⟩ := Filter.mem_comap.1 hU
  rw [nhds_pi, Filter.mem_pi'] at ht
  obtain ⟨I, V, hV, hIV⟩ := ht
  have key : ∀ i, ∃ m : ℕ, ∀ x ∈ Ideal.span {ϖ ^ m}, algebraMap (OCb l) (Cb l) x ∈ V i := by
    intro i
    have h := hV i
    rw [WittVector.zero_coeff] at h
    obtain ⟨c, hc, hcV⟩ := (@GlobalTheory.WeakTop.mem_nhds_iff_lt _ _ _ _ (cbValued l) _ _).1 h
    obtain ⟨m, hm⟩ := lt_of_mem_span_pow ϖ hϖ hdiv c hc
    exact ⟨m, fun x hx => hcV (by simpa using hm x hx)⟩
  choose M hM using key
  refine ⟨I.sup id + 1, I.sup M, fun w hw => htU (hIV ?_)⟩
  intro i hi
  show (inclW l w).coeff i ∈ V i
  simp only [inclW, WittVector.map_coeff]
  apply hM i
  have hlt : i < I.sup id + 1 := Nat.lt_succ_of_le (Finset.le_sup (f := id) hi)
  exact Ideal.span_singleton_le_span_singleton.2 (pow_dvd_pow ϖ (Finset.le_sup hi)) (hw i hlt)

end GlobalTheory.WeakClosed
end
end

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices GlobalTheory.WeakClosed
open scoped Topology PowerSeries.WithPiTopology



noncomputable section
open Filter Topology

namespace GlobalTheory.WeakClosed

theorem continuous_frac_act {A K G : Type} [CommRing A] [IsDomain A] [ValuationRing A] [Field K]
    [Algebra A K] [IsFractionRing A K] [TopologicalSpace G] (τ : G → (A ≃+* A))
    (σ : G → (K ≃+* K)) (hσ : ∀ g a, σ g (algebraMap A K a) = algebraMap A K (τ g a))
    (ho : ∀ (x a : A) (g₀ : G), a ≠ 0 → ∀ᶠ g in 𝓝 g₀, ¬ (τ g x - τ g₀ x ∣ a)) :
    letI : Valued K (ValuationRing.ValueGroup A K) := Valued.mk' (ValuationRing.valuation A K)
    Continuous fun p : G × K => σ p.1 p.2 := by
  letI V : Valued K (ValuationRing.ValueGroup A K) := Valued.mk' (ValuationRing.valuation A K)
  have hle : ∀ x y : K, Valued.v x ≤ Valued.v y ↔ ∃ c : A, algebraMap A K c * y = x := by
    intro x y
    change (∃ c : A, c • y = x) ↔ _
    simp only [Algebra.smul_def]
  have hinj := IsFractionRing.injective A K
  refine GlobalTheory.WeakTop.continuous_act_of_orbits σ ?_ ?_
  · intro g x y
    simp only [← not_le, hle]
    rintro h ⟨c, hc⟩
    refine h ⟨(τ g).symm c, (σ g).injective ?_⟩
    rw [map_mul, hσ, RingEquiv.apply_symm_apply, hc]
  · have hA : ∀ x : A, Continuous fun g => σ g (algebraMap A K x) := by
      intro x
      rw [continuous_iff_continuousAt]
      intro g₀ s hs
      obtain ⟨c, hc, hs⟩ := GlobalTheory.WeakTop.mem_nhds_iff_lt.1 hs
      obtain ⟨a, d, hd, rfl⟩ := IsFractionRing.div_surjective A c
      have hd0 : algebraMap A K d ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hd
      have ha : a ≠ 0 := by
        rintro rfl
        simp at hc
      rw [mem_map]
      filter_upwards [ho x a g₀ ha] with g hg
      apply hs
      change Valued.v (σ g (algebraMap A K x) - σ g₀ (algebraMap A K x)) < _
      rw [← not_le, hle, hσ, hσ, ← map_sub]
      rintro ⟨e, he⟩
      refine hg ⟨e * d, hinj ?_⟩
      rw [eq_div_iff hd0] at he
      rw [← he, map_mul, map_mul]
      ring
    intro x
    obtain ⟨a, d, hd, rfl⟩ := IsFractionRing.div_surjective A x
    have hd0 : algebraMap A K d ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hd
    simp only [map_div₀]
    exact (hA a).div (hA d) fun g => by simpa using hd0

theorem continuous_autCb_cbTop : ∀ {l : ℕ} [Fact l.Prime] {P : LocPrime l} (AI : LocAinf l P),
    letI := cbTop l; Continuous fun q : GQ l × Cb l => autCb l (AI.actT q.1) q.2 := by
  intro l _ P AI
  refine continuous_frac_act (A := OCb l) (fun g => AI.actT g) (fun g => autCb l (AI.actT g))
    (fun g a => autCb_alg l _ a) fun x a g₀ ha => ?_
  obtain ⟨n, hn⟩ : ∃ n, PreTilt.coeff n a ≠ 0 := by
    by_contra! h
    refine ha (Perfection.ext fun n => ?_)
    change PreTilt.coeff n a = PreTilt.coeff n 0
    rw [h, map_zero]
  filter_upwards [GlobalTheory.WeakTop.eventually_coeff_eq AI x n g₀] with g hg
  rintro ⟨c, hc⟩
  apply hn
  rw [hc, map_mul, map_sub, hg, sub_self, zero_mul]

end GlobalTheory.WeakClosed
end
end

section

open GlobalTheory.GLq GlobalTheory.MirAvg Polynomial

noncomputable section

namespace GlobalTheory.GLq.HCFrobWeight

open scoped Classical

section Reg

variable {H : Type} [Group H] [Fintype H]

theorem sum_irr_coeff (h : H) :
    ∑ σ ∈ (irr_finite_and_finsum_zOf_eq_one H).1.toFinset, (zOf σ).coeff h = if h = 1 then 1 else 0 := by
  obtain ⟨hfin, hsum⟩ := irr_finite_and_finsum_zOf_eq_one H
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin] at hsum
  have e := congrArg (fun z : MonoidAlgebra ℂ H => z.coeff h) hsum
  simp only [MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply] at e
  rw [e, MonoidAlgebra.one_def, MonoidAlgebra.coeff_single, Finsupp.single_apply]
  by_cases hh : h = 1
  · simp [hh]
  · simp [hh, Ne.symm hh]

theorem exists_irr_sum_ne_zero (F : H → ℂ) (hF : F 1 ≠ 0) :
    ∃ σ : H → ℂ, IsIrr σ ∧ ∑ h, F h * σ h⁻¹ ≠ 0 := by
  by_contra hc
  push_neg at hc
  apply hF
  set s := (irr_finite_and_finsum_zOf_eq_one H).1.toFinset with hs
  have h0 : ∑ σ ∈ s, σ 1 / (Fintype.card H : ℂ) * ∑ h, F h * σ h⁻¹ = 0 := by
    refine Finset.sum_eq_zero fun σ hσ => ?_
    rw [hc σ (by simpa [hs] using hσ), mul_zero]
  rw [← h0]
  have e : ∑ σ ∈ s, σ 1 / (Fintype.card H : ℂ) * ∑ h, F h * σ h⁻¹ =
      ∑ h, F h * ∑ σ ∈ s, (zOf σ).coeff h := by
    simp_rw [Finset.mul_sum, ZSumOne.zOf_coeff]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun h _ => Finset.sum_congr rfl fun σ _ => ?_
    ring
  rw [e, hs]
  simp_rw [sum_irr_coeff]
  simp

end Reg

variable {g : ℕ} [Fact g.Prime]

theorem isClass_of_isIrr {n : ℕ} {ψ : Gn g n → ℂ} (hψ : IsIrr ψ) : IsClass ψ := by
  obtain ⟨V, _, hV⟩ := hψ
  intro x y
  rw [← hV, ← hV]
  exact FDRep.char_conj V x y

theorem ip_hc_eq_left (a b n : ℕ) (hn : n = a + b) (χ : Gn g n → ℂ) (hχ : IsClass χ) (α : Gn g a → ℂ)
    (β : Gn g b → ℂ) :
    ip χ (hc a b α β n) = (Fintype.card (Gn g a × Gn g b) : ℂ)⁻¹ *
      ∑ h : Gn g a, (∑ y : Gn g b, res a b χ h y * β y⁻¹) * α h⁻¹ := by
  rw [hc, FrobRecHC.hcT_adjoint g a b n hn χ _ hχ]
  unfold ip
  rw [Fintype.sum_prod_type]
  congr 1
  refine Finset.sum_congr rfl fun h _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun y _ => ?_
  simp only [Prod.fst_inv, Prod.snd_inv]
  ring

theorem ip_hc_eq_right (a b n : ℕ) (hn : n = a + b) (χ : Gn g n → ℂ) (hχ : IsClass χ) (α : Gn g a → ℂ)
    (β : Gn g b → ℂ) :
    ip χ (hc a b α β n) = (Fintype.card (Gn g a × Gn g b) : ℂ)⁻¹ *
      ∑ y : Gn g b, (∑ h : Gn g a, res a b χ h y * α h⁻¹) * β y⁻¹ := by
  rw [hc, FrobRecHC.hcT_adjoint g a b n hn χ _ hχ]
  unfold ip
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  congr 1
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun h _ => ?_
  simp only [Prod.fst_inv, Prod.snd_inv]
  ring

theorem thetaInv_det_inv (θ : (ZMod g)ˣ →* ℂˣ) (y : Gn g 1) :
    ((θ⁻¹ (Matrix.GeneralLinearGroup.det y⁻¹) : ℂˣ) : ℂ) = ((θ (Matrix.GeneralLinearGroup.det y) : ℂˣ) : ℂ) := by
  simp [map_inv]

end GlobalTheory.GLq.HCFrobWeight

namespace GlobalTheory.GLq.HCFrobWeight

open scoped Classical

theorem exists_irr_hc_thetaInv : ∀ (g : ℕ) [Fact g.Prime] (n : ℕ) (ψ : Gn g (n + 1) → ℂ), IsIrr ψ → ∀ θ : (ZMod g)ˣ →* ℂˣ,
    (∑ x : Gn g 1, ((θ (Matrix.GeneralLinearGroup.det x) : ℂˣ) : ℂ) * res n 1 ψ 1 x ≠ 0 →
      ∃ σ : Gn g n → ℂ, IsIrr σ ∧
        ip ψ (hc n 1 σ (fun y : Gn g 1 => ((θ⁻¹ (Matrix.GeneralLinearGroup.det y) : ℂˣ) : ℂ)) (n + 1)) ≠ 0) ∧
    (∑ x : Gn g 1, ((θ (Matrix.GeneralLinearGroup.det x) : ℂˣ) : ℂ) * res 1 n ψ x 1 ≠ 0 →
      ∃ σ : Gn g n → ℂ, IsIrr σ ∧
        ip ψ (hc 1 n (fun y : Gn g 1 => ((θ⁻¹ (Matrix.GeneralLinearGroup.det y) : ℂˣ) : ℂ)) σ (n + 1)) ≠ 0) := by
  intro g _ n ψ hψ θ
  have hcl := isClass_of_isIrr hψ
  constructor
  · intro hS
    obtain ⟨σ, hσ, hne⟩ := exists_irr_sum_ne_zero
      (fun h : Gn g n => ∑ y : Gn g 1, res n 1 ψ h y * ((θ⁻¹ (Matrix.GeneralLinearGroup.det y⁻¹) : ℂˣ) : ℂ))
      (by simp_rw [thetaInv_det_inv]; simpa [mul_comm] using hS)
    refine ⟨σ, hσ, ?_⟩
    rw [ip_hc_eq_left n 1 (n + 1) rfl ψ hcl]
    exact mul_ne_zero (inv_ne_zero (Nat.cast_ne_zero.2 Fintype.card_ne_zero)) hne
  · intro hS
    obtain ⟨σ, hσ, hne⟩ := exists_irr_sum_ne_zero
      (fun y : Gn g n => ∑ h : Gn g 1, res 1 n ψ h y * ((θ⁻¹ (Matrix.GeneralLinearGroup.det h⁻¹) : ℂˣ) : ℂ))
      (by simp_rw [thetaInv_det_inv]; simpa [mul_comm] using hS)
    refine ⟨σ, hσ, ?_⟩
    rw [ip_hc_eq_right 1 n (n + 1) (by omega) ψ hcl]
    exact mul_ne_zero (inv_ne_zero (Nat.cast_ne_zero.2 Fintype.card_ne_zero)) hne

end GlobalTheory.GLq.HCFrobWeight
end
end
