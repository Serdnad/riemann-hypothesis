module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle122
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle173
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle126
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.FieldTheory.Separable
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle137
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.Etale.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle174
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle141
public import Mathlib.RingTheory.PowerSeries.Substitution
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle175
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle147
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.MemSaturatedOrderIsoSubspaceSpanSymmApply
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle008
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle148
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
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.LocalProperties.Reduced
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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

@[expose] public section

section

open IsLocalRing Polynomial
open scoped TensorProduct

theorem _root_.GlobalTheory.T.hart_baseChange_of_flat : ∀ (A R M O : Type) [CommRing A] [IsNoetherianRing A] [CommRing R] [Algebra A R]
    [AddCommGroup M] [Module R M] [CommRing O] [Algebra R O] [Algebra A O] [IsScalarTower A R O]
    [Module.Flat R O], GlobalTheory.GoodEtale.Hart A R M → GlobalTheory.GoodEtale.Hart A O (O ⊗[R] M) := by
  first | (exact @GlobalTheory.GoodEtale.hart_tensor_of_flat) | (exact GlobalTheory.GoodEtale.hart_tensor_of_flat) | (intros; apply GlobalTheory.GoodEtale.hart_tensor_of_flat  <;> assumption)
end

section

open IsLocalRing Polynomial
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.KeyOriginCut.TorsorField

theorem exists_point_pi {K G A Ω : Type} [CommRing K] [Fintype G] [DecidableEq G] [CommRing A]
    [Algebra K A] [Field Ω] [Algebra K Ω] (z : (G → A) →ₐ[K] Ω) :
    ∃ g : G, ∀ f : G → A, z f = z (fun _ => f g) := by
  have hs : ∑ g, (Pi.single g (1 : A) : G → A) = 1 := by
    simpa using Finset.univ_sum_single (1 : G → A)
  have hsum : ∑ g, z (Pi.single g 1) = 1 := by rw [← map_sum, hs, map_one]
  obtain ⟨g, -, hg⟩ := Finset.exists_ne_zero_of_sum_ne_zero (s := Finset.univ)
    (f := fun g => z (Pi.single g 1)) (by rw [hsum]; exact one_ne_zero)
  have hidem : z (Pi.single g 1) = 1 := by
    have h2 : z (Pi.single g 1) * z (Pi.single g 1) = z (Pi.single g 1) * 1 := by
      rw [← map_mul, mul_one]; congr 1; funext h; by_cases hh : h = g <;> simp [Pi.single_apply, hh]
    exact mul_left_cancel₀ hg h2
  refine ⟨g, fun f => ?_⟩
  have hf : f * Pi.single g 1 = (fun _ => f g) * Pi.single g 1 := by
    funext h; by_cases hh : h = g <;> simp [Pi.single_apply, hh]
  calc z f = z f * z (Pi.single g 1) := by rw [hidem, mul_one]
    _ = z (fun _ => f g) * z (Pi.single g 1) := by rw [← map_mul, ← map_mul, hf]
    _ = z (fun _ => f g) := by rw [hidem, mul_one]

variable {K M : Type} [Field K] [CommRing M] [Algebra K M] {q : ℕ}

abbrev galMap (act : Multiplicative (ZMod q) →* (M ≃ₐ[K] M)) :
    M ⊗[K] M →ₐ[K] (Multiplicative (ZMod q) → M) :=
  Algebra.TensorProduct.productMap
    (Pi.algHom K (fun _ : Multiplicative (ZMod q) => M) (fun _ => AlgHom.id K M))
    (Pi.algHom K (fun _ : Multiplicative (ZMod q) => M) (fun g => (act g).toAlgHom))

theorem galMap_tmul (act : Multiplicative (ZMod q) →* (M ≃ₐ[K] M)) (a b : M) :
    galMap act (a ⊗ₜ b) = fun g => a * act g b := by
  funext g; simp [galMap, Algebra.TensorProduct.productMap_apply_tmul]

theorem exists_eq_comp [NeZero q] {Ω : Type} [Field Ω] [Algebra K Ω]
    (act : Multiplicative (ZMod q) →* (M ≃ₐ[K] M)) (hbij : Function.Bijective (galMap act))
    (x y : M →ₐ[K] Ω) : ∃ g, y = x.comp (act g).toAlgHom := by
  classical
  let Φ := AlgEquiv.ofBijective (galMap act) hbij
  let z := (Algebra.TensorProduct.productMap x y).comp Φ.symm.toAlgHom
  obtain ⟨g, hg⟩ := exists_point_pi z
  have key : ∀ a b : M, x a * y b = z (fun _ => a * act g b) := by
    intro a b
    have hΦ : Φ.symm (galMap act (a ⊗ₜ b)) = a ⊗ₜ b := by
      show Φ.symm (Φ (a ⊗ₜ b)) = _
      exact Φ.symm_apply_apply _
    have h1 : z (galMap act (a ⊗ₜ b)) = x a * y b := by
      show Algebra.TensorProduct.productMap x y (Φ.symm (galMap act (a ⊗ₜ b))) = _
      rw [hΦ, Algebra.TensorProduct.productMap_apply_tmul]
    rw [← h1, hg, galMap_tmul]
  have hx : ∀ a, x a = z (fun _ => a) := fun a => by simpa using key a 1
  refine ⟨g, AlgHom.ext fun b => ?_⟩
  have h := key 1 b
  rw [map_one, one_mul, one_mul] at h
  rw [h, ← hx]; rfl

theorem eq_of_comp_eq [NeZero q] {Ω : Type} [Field Ω] [Algebra K Ω]
    (act : Multiplicative (ZMod q) →* (M ≃ₐ[K] M)) (hbij : Function.Bijective (galMap act))
    (x : M →ₐ[K] Ω) {g g' : Multiplicative (ZMod q)}
    (h : x.comp (act g).toAlgHom = x.comp (act g').toAlgHom) : g = g' := by
  classical
  by_contra hne
  obtain ⟨w, hw⟩ := hbij.2 (Pi.single g 1)
  have hZ : ∀ k, Algebra.TensorProduct.productMap x (x.comp (act k).toAlgHom) =
      (x.comp (Pi.evalAlgHom K (fun _ => M) k)).comp (galMap act) := by
    intro k; apply Algebra.TensorProduct.ext'; intro a b
    rw [AlgHom.comp_apply, galMap_tmul, Algebra.TensorProduct.productMap_apply_tmul]
    simp
  have e1 := congrArg (fun F => F w) (hZ g)
  have e2 := congrArg (fun F => F w) (hZ g')
  simp only [AlgHom.comp_apply, hw, Pi.evalAlgHom_apply] at e1 e2
  rw [h] at e1
  rw [Pi.single_eq_same] at e1
  rw [Pi.single_eq_of_ne (Ne.symm hne)] at e2
  have := e1.symm.trans e2
  simp at this

end GlobalTheory.KeyOriginCut.TorsorField

namespace GlobalTheory.KeyOriginCut.TorsorField

variable {K M : Type} [Field K] [CommRing M] [Algebra K M] {q : ℕ}

theorem factor_isGalois_dvd [NeZero q] {L : Type} [Field L] [Algebra K L] [FiniteDimensional K L]
    [Algebra.IsSeparable K L] (act : Multiplicative (ZMod q) →* (M ≃ₐ[K] M))
    (hbij : Function.Bijective (galMap act)) (π : M →ₐ[K] L) (hπ : Function.Surjective π) :
    IsGalois K L ∧ Module.finrank K L ∣ q := by
  classical
  let Ω := AlgebraicClosure K
  let σ0 : L →ₐ[K] Ω := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  have hσ0inj : Function.Injective σ0 := σ0.toRingHom.injective
  let P : Multiplicative (ZMod q) → Prop := fun g => ∀ a, π a = 0 → π (act g a) = 0
  have hPmul : ∀ g h, P g → P h → P (g * h) := by
    intro g h hg hh a ha; rw [map_mul, AlgEquiv.mul_apply]; exact hg _ (hh a ha)
  have hPone : P 1 := by intro a ha; rw [map_one, AlgEquiv.one_apply]; exact ha
  have hPpow : ∀ g (n : ℕ), P g → P (g ^ n) := by
    intro g n hg; induction n with
    | zero => rw [pow_zero]; exact hPone
    | succ n ih => rw [pow_succ]; exact hPmul _ _ ih hg
  let H : Subgroup (Multiplicative (ZMod q)) :=
    { carrier := {g | P g}
      mul_mem' := fun {g h} hg hh => hPmul g h hg hh
      one_mem' := hPone
      inv_mem' := fun {g} hg => by
        show P g⁻¹
        have hc : g ^ (Fintype.card (Multiplicative (ZMod q)) - 1) * g = 1 := by
          rw [← pow_succ, Nat.sub_add_cancel Fintype.card_pos, pow_card_eq_one]
        rw [← eq_inv_of_mul_eq_one_left hc]
        exact hPpow g _ hg }
  have hτ : ∀ g, P g → ∃ τ : L →ₐ[K] L, τ.comp π = π.comp (act g).toAlgHom := by
    intro g hg
    let E := Ideal.quotientKerAlgEquivOfSurjective hπ
    let f := Ideal.Quotient.liftₐ (RingHom.ker π) (π.comp (act g).toAlgHom)
      (fun a ha => hg a (RingHom.mem_ker.1 ha))
    refine ⟨f.comp E.symm.toAlgHom, AlgHom.ext fun a => ?_⟩
    have hE : E.symm (π a) = Ideal.Quotient.mk _ a := E.symm_apply_eq.2 rfl
    show f (E.symm (π a)) = π (act g a)
    rw [hE]; rfl
  choose! τ hτc using hτ
  have hΨ : ∀ g, P g → (σ0.comp (τ g)).comp π = (σ0.comp π).comp (act g).toAlgHom := by
    intro g hg; rw [AlgHom.comp_assoc, hτc g hg, ← AlgHom.comp_assoc]
  have hB : ∀ σ : L →ₐ[K] Ω, ∃ g, P g ∧ σ.comp π = (σ0.comp π).comp (act g).toAlgHom := by
    intro σ
    obtain ⟨g, hg⟩ := exists_eq_comp act hbij (σ0.comp π) (σ.comp π)
    refine ⟨g, fun a ha => hσ0inj ?_, hg⟩
    have h := congrArg (fun F => F a) hg
    simp only [AlgHom.comp_apply] at h
    rw [map_zero]; exact h.symm.trans (by rw [ha, map_zero])
  have hcancel : ∀ σ σ' : L →ₐ[K] Ω, σ.comp π = σ'.comp π → σ = σ' := by
    intro σ σ' h; ext l; obtain ⟨a, rfl⟩ := hπ l
    exact congrArg (fun F => F a) h

  let Ψ : H → (L →ₐ[K] Ω) := fun g => σ0.comp (τ g)
  have hΨbij : Function.Bijective Ψ := by
    refine ⟨fun g g' h => Subtype.ext ?_, fun σ => ?_⟩
    · have h2 : (σ0.comp π).comp (act g.1).toAlgHom = (σ0.comp π).comp (act g'.1).toAlgHom := by
        rw [← hΨ _ g.2, ← hΨ _ g'.2]; exact congrArg (fun F => F.comp π) h
      exact eq_of_comp_eq act hbij _ h2
    · obtain ⟨g, hg, he⟩ := hB σ
      exact ⟨⟨g, hg⟩, hcancel _ _ ((hΨ g hg).trans he.symm)⟩
  have hcardΩ : Nat.card (L →ₐ[K] Ω) = Module.finrank K L := by
    rw [Nat.card_eq_fintype_card, AlgHom.card]
  have hcardH : Nat.card H = Module.finrank K L := (Nat.card_eq_of_bijective Ψ hΨbij).trans hcardΩ
  refine ⟨?_, ?_⟩
  ·
    have hsurj : Function.Surjective (fun τ' : L →ₐ[K] L => σ0.comp τ') := by
      intro σ
      obtain ⟨g, hg, he⟩ := hB σ
      exact ⟨τ g, hcancel _ _ ((hΨ g hg).trans he.symm)⟩
    have hinj : Function.Injective (fun τ' : L →ₐ[K] L => σ0.comp τ') := by
      intro a b h; ext l; exact hσ0inj (congrArg (fun F => F l) h)
    have hLL : Nat.card (L →ₐ[K] L) = Module.finrank K L :=
      (Nat.card_eq_of_bijective _ ⟨hinj, hsurj⟩).trans hcardΩ
    apply IsGalois.of_card_aut_eq_finrank
    rw [← hLL]
    exact Nat.card_congr (Algebra.IsAlgebraic.algEquivEquivAlgHom K L).toEquiv
  · rw [← hcardH]
    have := Subgroup.card_subgroup_dvd_card H
    simpa [Nat.card_eq_fintype_card] using this

end GlobalTheory.KeyOriginCut.TorsorField


open GlobalTheory.KeyOriginCut.TorsorField in
theorem GlobalTheory.KeyOriginCut.torsor_field_eq_prod_galois :
    ∀ (K M : Type) [Field K] [CommRing M] [Algebra K M] (q : ℕ)
    (act : Multiplicative (ZMod q) →* (M ≃ₐ[K] M)), 0 < q →
    GlobalTheory.KeyOriginCut.IsZTorsor K M q act →
    ∃ (ι : Type) (_ : Fintype ι) (L : ι → Type) (_ : ∀ i, Field (L i)) (_ : ∀ i, Algebra K (L i)),
      (∀ i, FiniteDimensional K (L i)) ∧ (∀ i, IsGalois K (L i)) ∧
      (∀ i, Module.finrank K (L i) ∣ q) ∧ Nonempty (M ≃ₐ[K] ∀ i, L i) := by
  intro K M _ _ _ q act hq htor
  haveI : NeZero q := ⟨hq.ne'⟩
  haveI : Algebra.Etale K M := GlobalTheory.KeyOriginCut.etale_of_isZTorsor K M q act htor
  obtain ⟨I, hI, L, hF, hA, e, hL⟩ := (Algebra.Etale.iff_exists_algEquiv_prod K M).1 inferInstance
  have hbij : Function.Bijective (galMap act) := htor.2.2.2
  have key : ∀ i, IsGalois K (L i) ∧ Module.finrank K (L i) ∣ q := by
    intro i
    haveI := (hL i).1
    haveI := (hL i).2
    exact factor_isGalois_dvd act hbij ((Pi.evalAlgHom K L i).comp e.toAlgHom)
      ((Function.surjective_eval i).comp e.surjective)
  exact ⟨I, Fintype.ofFinite I, L, hF, hA, fun i => (hL i).1, fun i => (key i).1,
    fun i => (key i).2, ⟨e⟩⟩
end
end

section

open IsLocalRing Polynomial

theorem _root_.GlobalTheory.T.zmodTorsor_exists_point_finite_separable : ∀ (B K : Type) [CommRing B] [Field K] (f : B →+* K) (D : Type) [CommRing D] [Algebra B D]
    (q : ℕ), 0 < q → ∀ (act : Multiplicative (ZMod q) →* (D ≃ₐ[B] D)),
    GlobalTheory.KeyOriginCut.IsZTorsor B D q act →
    ∃ (L : Type) (_ : Field L) (_ : Algebra K L) (_ : FiniteDimensional K L) (_ : Algebra.IsSeparable K L)
      (σ : D →+* L), σ.comp (algebraMap B D) = (algebraMap K L).comp f := by
  first | (exact @GlobalTheory.TorsorFieldPoint.exists_point_finite_separable) | (exact GlobalTheory.TorsorFieldPoint.exists_point_finite_separable) | (intros; apply GlobalTheory.TorsorFieldPoint.exists_point_finite_separable  <;> assumption)
end

section

open IsLocalRing Polynomial

theorem _root_.GlobalTheory.T.cyclic_torsor_etale : ∀ (B D : Type) [CommRing B] [CommRing D] [Algebra B D] (q : ℕ)
    (act : Multiplicative (ZMod q) →* (D ≃ₐ[B] D)),
    GlobalTheory.KeyOriginCut.IsZTorsor B D q act → Algebra.Etale B D := by
  first | (exact @GlobalTheory.KeyOriginCut.etale_of_isZTorsor) | (exact GlobalTheory.KeyOriginCut.etale_of_isZTorsor) | (intros; apply GlobalTheory.KeyOriginCut.etale_of_isZTorsor <;> assumption)
end

section

open GlobalTheory.AffineCurveNbhd

theorem _root_.GlobalTheory.T.isNbhd_away_of_add_algebraMap_mul_eq_one : ∀ (B A' : Type) [CommRing B] [CommRing A'] [Algebra B A'] (f : B) (h c : A'), IsNbhd B A' f → h + algebraMap B A' f * c = 1 → IsNbhd B (Localization.Away h) f := by
  first | (exact @GlobalTheory.AffineCurveNbhd.isNbhd_away_of_add_mul_eq_one) | (exact GlobalTheory.AffineCurveNbhd.isNbhd_away_of_add_mul_eq_one) | (intros; apply GlobalTheory.AffineCurveNbhd.isNbhd_away_of_add_mul_eq_one <;> assumption)
end

section

open GlobalTheory.AffineCurveNbhd

theorem _root_.GlobalTheory.T.exists_dvd_mul_pow_etale_nbhd_zeroLocus : ∀ (B A' : Type) [CommRing B] [IsDedekindDomain B] [CommRing A'] [Algebra B A'] [Algebra.Etale B A'] (f : B), f ≠ 0 → IsNbhd B A' f → ∀ a ∈ nonZeroDivisors A', ∀ M : Ideal A', M.IsMaximal → algebraMap B A' f ∈ M → ∃ s ∉ M, ∃ N : ℕ, a ∣ s * algebraMap B A' f ^ N := by
  first | (exact @GlobalTheory.LocDivEtale.exists_dvd_mul_pow) | (exact GlobalTheory.LocDivEtale.exists_dvd_mul_pow) | (intros; apply GlobalTheory.LocDivEtale.exists_dvd_mul_pow <;> assumption)
end

section

open Polynomial

theorem _root_.GlobalTheory.T.hasseDerivativePowerSeries_mul_subst_leibniz : ∀ (k : Type) [Field k] (a φ ψ : PowerSeries k) (l : ℕ), PowerSeries.constantCoeff a = 0 → ((GlobalTheory.PicDiv.hasse l (φ * ψ)).subst a : PowerSeries k) = ∑ p ∈ Finset.range (l + 1), ((GlobalTheory.PicDiv.hasse p φ).subst a : PowerSeries k) * (GlobalTheory.PicDiv.hasse (l - p) ψ).subst a := by
  first | exact @GlobalTheory.hasse_mul_subst | exact GlobalTheory.hasse_mul_subst | (intros; apply GlobalTheory.hasse_mul_subst <;> assumption)
end

section

open GlobalTheory.IndefiniteRowSideFullHecke.MultiplicationKernelIdentity GlobalTheory.HermitianPreEigenvalues Polynomial Module

noncomputable section
namespace GlobalTheory.HerbFin

variable {C : Type} [Field C] {v : AddValuation C (WithTop ℝ)} {S : Type} [Fintype S]
  [DecidableEq S]

theorem monic_prod (a : S → Int0 v) : (∏ s, (X - Polynomial.C (a s)) : (Int0 v)[X]).Monic :=
  monic_prod_of_monic _ _ fun s _ => monic_X_sub_C (a s)

def powBasis (a : S → Int0 v) : PowerBasis (Int0 v) (RS a) := AdjoinRoot.powerBasis' (monic_prod a)

instance finite_RS (a : S → Int0 v) : Module.Finite (Int0 v) (RS a) := (powBasis a).finite

theorem eq_zero_of_smul_RS (a : S → Int0 v) {c : Int0 v} (hc : c ≠ 0) {y : RS a}
    (h : c • y = 0) : y = 0 := by
  have b := (powBasis a).basis
  apply b.repr.injective
  refine Finsupp.ext fun i => ?_
  have h2 := congrArg (fun z => b.repr z i) h
  simp only [map_smul, Finsupp.smul_apply, smul_eq_mul, map_zero, Finsupp.coe_zero,
    Pi.zero_apply] at h2
  rw [map_zero, Finsupp.coe_zero, Pi.zero_apply]
  exact (mul_eq_zero.1 h2).resolve_left hc

theorem eq_zero_of_smul_pi (a : S → Int0 v) {N : ℕ} {c : Int0 v} (hc : c ≠ 0)
    {y : Fin N → RS a} (h : c • y = 0) : y = 0 := by
  funext i
  have h3 := congrFun h i
  simp only [Pi.smul_apply, Pi.zero_apply] at h3
  exact eq_zero_of_smul_RS a hc h3

theorem sat_kerMul (a : S → Int0 v) (r : RS a) (Q : Type) [AddCommGroup Q] [Module (RS a) Q]
    [Module (Int0 v) Q] [IsScalarTower (Int0 v) (RS a) Q]
    (htf : ∀ (c : Int0 v) (y : Q), c ≠ 0 → c • y = 0 → y = 0) :
    GlobalTheory.IsSaturatedSubmodule (kerMul a r Q) := by
  rw [GlobalTheory.isSaturatedSubmodule_iff]
  intro c hc x hx
  simp only [kerMul, Submodule.restrictScalars_mem, LinearMap.mem_ker, LinearMap.lsmul_apply] at hx ⊢
  rw [smul_comm] at hx
  exact htf c _ hc hx

theorem finite_main : ∀ (C : Type) [Field C] (v : AddValuation C (WithTop ℝ)) (S : Type) [Fintype S] [DecidableEq S] (a : S → Int0 v), Function.Injective a → ∀ (N : ℕ) (Fil : Submodule (RS a) (Fin N → RS a)), (∀ (c : Int0 v) (x : Fin N → RS a), c ≠ 0 → c • x ∈ Fil → x ∈ Fil) → ∀ τ : S, Module.Finite (Int0 v) (Fil.restrictScalars (Int0 v)) ∧ Module.Finite (Int0 v) (preEig a Fil τ) ∧ Module.Finite (Int0 v) (filKer a Fil τ) ∧ Module.Finite (Int0 v) (eigSub a τ (Fin N → RS a)) ∧ Module.Finite (Int0 v) (eigSub a τ ((Fin N → RS a) ⧸ Fil)) ∧ Module.Finite (Int0 v) (eigSub a τ Fil) ∧ Module.Finite (Int0 v) (kerMul a (cofac a τ) Fil) := by
  intro C _ v S _ _ a _ N Fil hFil τ
  have hsatF : GlobalTheory.IsSaturatedSubmodule (Fil.restrictScalars (Int0 v)) :=
    GlobalTheory.isSaturatedSubmodule_iff.2 fun c hc x hx => hFil c x hc hx
  have hT1 : ∀ (c : Int0 v) (y : Fin N → RS a), c ≠ 0 → c • y = 0 → y = 0 :=
    fun c y hc h => eq_zero_of_smul_pi a hc h
  have hT2 : ∀ (c : Int0 v) (y : Fil), c ≠ 0 → c • y = 0 → y = 0 := fun c y hc h =>
    Subtype.ext (hT1 c y hc (congrArg Subtype.val h))
  have hT3 : ∀ (c : Int0 v) (y : (Fin N → RS a) ⧸ Fil), c ≠ 0 → c • y = 0 → y = 0 := by
    intro c y hc h
    induction y using Submodule.Quotient.induction_on with
    | H x =>
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at h
      rw [Submodule.Quotient.mk_eq_zero]
      exact hFil c x hc h
  have hF : Module.Finite (Int0 v) (Fil.restrictScalars (Int0 v)) := hsatF.finite_of_valuationRing
  have hFil' : Module.Finite (Int0 v) Fil := hF
  have hQ : Module.Finite (Int0 v) ((Fin N → RS a) ⧸ Fil) :=
    Module.Finite.of_surjective (proj a Fil) (Submodule.mkQ_surjective Fil)
  refine ⟨hF, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (hsatF.comap (mulR a N (lin a τ))).finite_of_valuationRing
  · refine (hsatF.inf ?_).finite_of_valuationRing
    exact sat_kerMul a (cofac a τ) (Fin N → RS a) hT1
  · exact (sat_kerMul a (lin a τ) (Fin N → RS a) hT1).finite_of_valuationRing
  · exact (sat_kerMul a (lin a τ) _ hT3).finite_of_valuationRing
  · exact (sat_kerMul a (lin a τ) Fil hT2).finite_of_valuationRing
  · exact (sat_kerMul a (cofac a τ) Fil hT2).finite_of_valuationRing

end GlobalTheory.HerbFin
end
end

section

open Polynomial

namespace GlobalTheory.MonicRootRange

theorem isAlgClosed_fractionRing (T : Type) [CommRing T] [IsDomain T]
    (h : GlobalTheory.LocAcyc.AbsIntClosed T) : IsAlgClosed (FractionRing T) := by
  refine IsAlgClosed.of_exists_root _ fun p hmon hirr => ?_
  obtain ⟨b, hb, hq⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors T) p
  set q := IsLocalization.integerNormalization (nonZeroDivisors T) p
  set f := algebraMap T (FractionRing T)
  have hinj : Function.Injective f := IsFractionRing.injective T (FractionRing T)
  have hb0 : f b ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
  have hsmul : (b • p : (FractionRing T)[X]) = C (f b) * p := by
    rw [Algebra.smul_def, Polynomial.algebraMap_apply]
  have hn : 1 ≤ p.natDegree := natDegree_pos_iff_degree_pos.mpr (degree_pos_of_irreducible hirr)
  have hdeg : q.natDegree = p.natDegree := by
    have := congrArg natDegree hq
    rwa [natDegree_map_eq_of_injective hinj, hsmul, natDegree_C_mul hb0] at this
  have hq0 : q ≠ 0 := fun h0 => by rw [h0, natDegree_zero] at hdeg; omega
  have hc0 : f q.leadingCoeff ≠ 0 := (map_ne_zero_iff f hinj).mpr (leadingCoeff_ne_zero.mpr hq0)
  obtain ⟨w, hw⟩ := h q.integralNormalization (monic_integralNormalization hq0)
    (by rw [natDegree_integralNormalization]; omega)
  refine ⟨f w / f q.leadingCoeff, ?_⟩
  have key := integralNormalization_eval₂_leadingCoeff_mul (hdeg ▸ hn) f (f w / f q.leadingCoeff)
  rw [mul_div_cancel₀ _ hc0, eval₂_at_apply, hw, map_zero] at key
  have h2 : q.eval₂ f (f w / f q.leadingCoeff) = 0 :=
    (mul_eq_zero.mp key.symm).resolve_left (pow_ne_zero _ hc0)
  rw [← eval_map, hq, hsmul, eval_mul, eval_C] at h2
  exact (mul_eq_zero.mp h2).resolve_left hb0

end GlobalTheory.MonicRootRange
end

section

open IsLocalRing Polynomial

namespace GlobalTheory.VertUnits

def DivConst (T O : Type) [CommRing T] [CommRing O] [Algebra T O] : Prop :=
  ∀ (b c : O) (s : T), s ≠ 0 → b * c = algebraMap T O s →
    ∃ (a : T) (w : Oˣ), b = algebraMap T O a * (w : O)

def DivConstAll : Prop :=
  ∀ (T O : Type) [CommRing T] [IsDomain T] [IsLocalRing T] [CommRing O] [IsLocalRing O] [Algebra T O]
    [Algebra (Polynomial T) O] [IsScalarTower T (Polynomial T) O], GlobalTheory.LocAcyc.AbsIntClosed T →
    ∀ (P : Ideal (Polynomial T)) [P.IsPrime] (φ : Localization.AtPrime P →+* O),
    φ.comp (algebraMap (Polynomial T) _) = algebraMap (Polynomial T) O →
    GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsStrictHenselisation φ → DivConst T O

def DivConstWith (S : ∀ (T : Type) [CommRing T] [IsLocalRing T], Ideal (Polynomial T) → Prop) :
    Prop :=
  ∀ (T O : Type) [CommRing T] [IsDomain T] [IsLocalRing T] [CommRing O] [IsLocalRing O] [Algebra T O]
    [Algebra (Polynomial T) O] [IsScalarTower T (Polynomial T) O], GlobalTheory.LocAcyc.AbsIntClosed T →
    ∀ (P : Ideal (Polynomial T)) [P.IsPrime] (φ : Localization.AtPrime P →+* O),
    φ.comp (algebraMap (Polynomial T) _) = algebraMap (Polynomial T) O →
    GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsStrictHenselisation φ →
    P.comap (Polynomial.C : T →+* Polynomial T) = maximalIdeal T → S T P → DivConst T O

def DivConstLocal : Prop := DivConstWith (fun _ _ _ _ => True)

def DivConstGeneric : Prop :=
  DivConstWith (fun T _ _ P => P = (maximalIdeal T).map (Polynomial.C : T →+* Polynomial T))

def DivConstClosedPts : Prop :=
  DivConstWith (fun T _ _ P => P ≠ (maximalIdeal T).map (Polynomial.C : T →+* Polynomial T))

def DivConstOrigin : Prop :=
  DivConstWith (fun T _ _ P =>
    P = (maximalIdeal T).map (Polynomial.C : T →+* Polynomial T) ⊔ Ideal.span {Polynomial.X})

theorem divConstLocal_of (h₁ : DivConstClosedPts) (h₂ : DivConstGeneric) : DivConstLocal := by
  intro T O _ _ _ _ _ _ _ _ hT P _ φ hφ hsh hP _
  by_cases hg : P = (maximalIdeal T).map (Polynomial.C : T →+* Polynomial T)
  · exact h₂ T O hT P φ hφ hsh hP hg
  · exact h₁ T O hT P φ hφ hsh hP hg

end GlobalTheory.VertUnits
end
