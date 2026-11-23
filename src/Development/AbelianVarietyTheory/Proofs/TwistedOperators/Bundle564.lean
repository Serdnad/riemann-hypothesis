module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HalfLinearCocycle
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RealIdemMulOfReal
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOrEqOfPlaceIdem
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle357
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle402
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle561
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle316
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle557
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle439
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle513
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle534
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle136
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle374
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.UnitCharTriangle
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle160
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitCharEqOfNatCong
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle030
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2200
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle221
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle004
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle558
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle150

@[expose] public section

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SymmetricBilinearHalf

variable {D : D7}

theorem sb_zero {m n : ℕ} (e : AE D) (Λ : AddSubgroup (Mx D m n)) : IsSBHalf e Λ 0 :=
  ⟨fun _ h => absurd rfl h, 1, one_pos, fun _ _ _ _ => rfl, fun _ h => absurd rfl h⟩

theorem sb_smul {m n : ℕ} {e : AE D} {Λ : AddSubgroup (Mx D m n)} {Φ : Mx D m n → ℂ} (c : ℂ)
    (h : IsSBHalf e Λ Φ) : IsSBHalf e Λ (c • Φ) := by
  obtain ⟨h1, k, hk, h2, h3⟩ := h
  have ne : ∀ t, (c • Φ) t ≠ 0 → Φ t ≠ 0 := fun t ht h0 => ht (by rw [Pi.smul_apply, h0, smul_zero])
  exact ⟨fun t ht => h1 t (ne t ht), k, hk, fun u hu hh t => by rw [Pi.smul_apply, Pi.smul_apply, h2 u hu hh t],
    fun t ht => h3 t (ne t ht)⟩

theorem half_nsmul {m n : ℕ} {e : AE D} {u : Mx D m n} (k : ℕ) (h : IsHalf e u) : IsHalf e (k • u) := by
  rw [GlobalTheory.SplitScalar.isHalf_iff] at h ⊢
  rw [smul_comm, h]

theorem sb_add {m n : ℕ} {e : AE D} {Λ : AddSubgroup (Mx D m n)} {Φ Ψ : Mx D m n → ℂ}
    (h : IsSBHalf e Λ Φ) (h' : IsSBHalf e Λ Ψ) : IsSBHalf e Λ (Φ + Ψ) := by
  obtain ⟨h1, k, hk, h2, h3⟩ := h
  obtain ⟨h1', k', hk', h2', h3'⟩ := h'
  have ne : ∀ t, (Φ + Ψ) t ≠ 0 → Φ t ≠ 0 ∨ Ψ t ≠ 0 := fun t ht => by
    by_contra hc
    rw [not_or, not_not, not_not] at hc
    exact ht (by rw [Pi.add_apply, hc.1, hc.2, add_zero])
  refine ⟨fun t ht => (ne t ht).elim (h1 t) (h1' t), k * k', Nat.mul_pos hk hk', fun u hu hh t => ?_,
    fun t ht => ?_⟩
  · have e1 : Φ (t + (k * k') • u) = Φ t := by
      rw [mul_smul]; exact h2 _ (Λ.nsmul_mem hu k') (half_nsmul k' hh) t
    have e2 : Ψ (t + (k * k') • u) = Ψ t := by
      rw [mul_comm, mul_smul]; exact h2' _ (Λ.nsmul_mem hu k) (half_nsmul k hh) t
    rw [Pi.add_apply, Pi.add_apply, e1, e2]
  · rcases ne t ht with h | h
    · rw [mul_comm, mul_smul]; exact Λ.nsmul_mem (h3 t h) k'
    · rw [mul_smul]; exact Λ.nsmul_mem (h3' t h) k

theorem wAt_of_half {m n : ℕ} {p : Place D} {a c : AE D} (hac : a * c = 0) (hs : a + c = idem D p)
    {x : Mx D m n} (hx : IsHalf a x) : wAt p x = x := by
  funext i j
  show idem D p * x i j = x i j
  have := hx i j
  rw [← hs]
  linear_combination (1 - c) * this + (x i j) * hac

theorem placeModel_onto_local : ∀ (D : Formalism.BasicNotions.D7) (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF ↥(Formalism.BasicNotions.D7.host D).F) ℂ) (θ : Formalism.IndefR.Datum.InfFam D) (S T : Formalism.BasicNotions.TH.HSp D) (sS : Formalism.BasicNotions.Rows.Data.Tau (Formalism.BasicNotions.D7.what₂ D) → Matrix (Fin (Formalism.BasicNotions.HSpace.rank S)) (Fin (Formalism.BasicNotions.HSpace.rank S)) ℂ) (sT : Formalism.BasicNotions.Rows.Data.Tau (Formalism.BasicNotions.D7.what₂ D) → Matrix (Fin (Formalism.BasicNotions.HSpace.rank T)) (Fin (Formalism.BasicNotions.HSpace.rank T)) ℂ) (ΛS : Submodule (NumberField.RingOfIntegers (Formalism.BasicNotions.D7.host D).E) (Fin (Formalism.BasicNotions.HSpace.rank S) → (Formalism.BasicNotions.D7.host D).E)) (ΛT : Submodule (NumberField.RingOfIntegers (Formalism.BasicNotions.D7.host D).E) (Fin (Formalism.BasicNotions.HSpace.rank T) → (Formalism.BasicNotions.D7.host D).E)) (f₀ : Formalism.IndefR.Datum.WO S T → ℂ), GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.IsBase ψ θ S T sS sT ΛS ΛT f₀ → ∀ (v : GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.FinPl D) (a : Formalism.L2.Theta.AE D), Formalism.L2.Theta.IsSplitIdem D a → a + (Formalism.L2.Theta.cA D) a = GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.idem D (Sum.inl v) → (∃ (Tm : (Formalism.IndefR.Datum.Mx D (Formalism.BasicNotions.HSpace.rank T) (Formalism.BasicNotions.HSpace.rank S) → ℂ) →ₗ[ℂ] Formalism.IndefR.Datum.Mx D (Formalism.BasicNotions.HSpace.rank T) (Formalism.BasicNotions.HSpace.rank S) → ℂ), Formalism.IndefR.Datum.IsPlaceModel ψ (Formalism.IndefR.Datum.symplO S T) (Formalism.IndefR.Datum.heisO ψ S T) a (Formalism.IndefR.Datum.latO S T ↑ΛS ↑ΛT fun (x : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥(Formalism.BasicNotions.D7.host D).F)) ↦ True) (1 : ℂ) f₀ Tm) ∧ ∀ (Tm : (Formalism.IndefR.Datum.Mx D (Formalism.BasicNotions.HSpace.rank T) (Formalism.BasicNotions.HSpace.rank S) → ℂ) →ₗ[ℂ] Formalism.IndefR.Datum.Mx D (Formalism.BasicNotions.HSpace.rank T) (Formalism.BasicNotions.HSpace.rank S) → ℂ), Formalism.IndefR.Datum.IsPlaceModel ψ (Formalism.IndefR.Datum.symplO S T) (Formalism.IndefR.Datum.heisO ψ S T) a (Formalism.IndefR.Datum.latO S T ↑ΛS ↑ΛT fun (x : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥(Formalism.BasicNotions.D7.host D).F)) ↦ True) (1 : ℂ) f₀ Tm → (∀ (Φ : Formalism.IndefR.Datum.Mx D (Formalism.BasicNotions.HSpace.rank T) (Formalism.BasicNotions.HSpace.rank S) → ℂ), Formalism.IndefR.Datum.IsSBHalf a (Formalism.IndefR.Datum.latO S T ↑ΛS ↑ΛT fun (x : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥(Formalism.BasicNotions.D7.host D).F)) ↦ True) Φ → GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.IsLocal ψ θ S T sS sT ΛS ΛT (Sum.inl v) (Tm Φ)) ∧ ∀ (x : Formalism.IndefR.Datum.WO S T → ℂ), GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.IsLocal ψ θ S T sS sT ΛS ΛT (Sum.inl v) x → ∃ (Φ : Formalism.IndefR.Datum.Mx D (Formalism.BasicNotions.HSpace.rank T) (Formalism.BasicNotions.HSpace.rank S) → ℂ), Formalism.IndefR.Datum.IsSBHalf a (Formalism.IndefR.Datum.latO S T ↑ΛS ↑ΛT fun (x : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥(Formalism.BasicNotions.D7.host D).F)) ↦ True) Φ ∧ Tm Φ = x := by
  intro D ψ θ S T sS sT ΛS ΛT f₀ hb v a ha hs
  have h1 : a * a = a := ha.1
  have h2 : a * cA D a = 0 := ha.2.1
  have c1 : cA D a * cA D a = cA D a := by rw [← map_mul, h1]
  have hψ := base_std hb
  have hθ := base_inf hb
  have hS := hb.2.2.1
  have hT := hb.2.2.2.1
  obtain ⟨hgen, hspan⟩ := GlobalTheory.T.schwartzBruhatHalf_span_modulated_translates D ψ S T ΛS ΛT hψ hS hT a h1 h2 (GlobalTheory.PlaceModelSum.infPart_split ha)
  have st := fun f (hf : IsLocal ψ θ S T sS sT ΛS ΛT (.inl v) f) =>
    (GlobalTheory.T.fockVacua_localFactors_stable_heisenberg_away D ψ θ S T sS sT ΛS ΛT hψ hθ f hf.1).2 (.inl v) hf
  have l0 := base_isLocal hb (.inl v)
  have lz : IsLocal ψ θ S T sS sT ΛS ΛT (.inl v) 0 := by
    have := (st f₀ l0).2.1 (-1) f₀ l0
    rwa [neg_one_smul, neg_add_cancel] at this
  refine ⟨?_, fun Tm hTm => ⟨fun Φ hΦ => ?_, fun x hx => ?_⟩⟩
  · have ho : GlobalTheory.PlaceModelSum.IsOrthSum a :=
      ⟨Unit, {()}, fun _ => a, fun _ _ => ha, fun _ _ _ _ h => absurd rfl h, by rw [Finset.sum_singleton]⟩
    exact ho.exists_model hψ hS hT h2 hb.2.2.2.2.2.lat
  · refine Submodule.span_induction (p := fun Φ _ => IsLocal ψ θ S T sS sT ΛS ΛT (.inl v) (Tm Φ))
      ?_ ?_ ?_ ?_ (hspan Φ hΦ)
    · rintro _ ⟨x, y, hx, hy, rfl⟩
      rw [(hgen x y hx hy).2 f₀ Tm hTm]
      have e1 := (st f₀ l0).1 x
      rw [wAt_of_half h2 hs hx] at e1
      have e2 := (st _ e1).1 y
      rwa [wAt_of_half ((mul_comm _ _).trans h2) ((add_comm _ _).trans hs) hy] at e2
    · rw [map_zero]; exact lz
    · intro x y _ _ hx hy
      have := (st _ hx).2.1 1 _ hy
      rw [one_smul] at this
      rw [map_add (f := _)]; exact this
    · intro c x _ hx
      have := (st _ hx).2.1 c _ lz
      rw [add_zero] at this
      rw [map_smul]; exact this
  · refine Submodule.span_induction
      (p := fun x _ => ∃ Φ, IsSBHalf a (latO S T ΛS ΛT fun _ => True) Φ ∧ Tm Φ = x)
      ?_ ?_ ?_ ?_ (GlobalTheory.T.localFactor_mem_span_localHeisenbergTranslates D ψ θ S T sS sT ΛS ΛT f₀ hb v x hx)
    · rintro _ ⟨w, rfl⟩
      have hx : IsHalf a (a • w) := by rw [GlobalTheory.SplitScalar.isHalf_iff, smul_smul, h1]
      have hy : IsHalf (cA D a) (cA D a • w) := by rw [GlobalTheory.SplitScalar.isHalf_iff, smul_smul, c1]
      obtain ⟨g1, g2⟩ := hgen _ _ hx hy
      refine ⟨_, sb_smul (ψ (-symplOH S T (cA D a • w) (a • w))) g1, ?_⟩
      rw [map_smul, g2 f₀ Tm hTm, GlobalTheory.SplitScalar.heisO_heisO, smul_smul, ← AddChar.map_add_eq_mul, neg_add_cancel,
        AddChar.map_zero_eq_one, one_smul, ← add_smul, add_comm, hs]
      rfl
    · exact ⟨0, sb_zero _ _, map_zero _⟩
    · rintro _ _ _ _ ⟨Φ, hΦ, rfl⟩ ⟨Ψ, hΨ, rfl⟩
      exact ⟨Φ + Ψ, sb_add hΦ hΨ, map_add _ _ _⟩
    · rintro c _ _ ⟨Φ, hΦ, rfl⟩
      exact ⟨c • Φ, sb_smul c hΦ, map_smul _ _ _⟩

end GlobalTheory.SymmetricBilinearHalf

end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder

namespace GlobalTheory.PlaceTensor.PureScalar

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem wAt_zero {m n : ℕ} (p : Place D) : wAt p (0 : Mx D m n) = 0 := by
  rw [wAt_eq_smul, smul_zero]

theorem wAt_neg_wAt_self {m n : ℕ} (q : Place D) (w : Mx D m n) : wAt q (-(wAt q w)) = -(wAt q w) := by
  have hq : idem D q * idem D q = idem D q := (GlobalTheory.T.cmAdeleIdempotentOfPlace_properties D).1 q
  rw [wAt_eq_smul, wAt_eq_smul, smul_neg, smul_smul, hq]

theorem wAt_neg_wAt_ne {m n : ℕ} {p q : Place D} (hpq : p ≠ q) (w : Mx D m n) : wAt p (-(wAt q w)) = 0 := by
  have hpq' : idem D p * idem D q = 0 := (GlobalTheory.T.cmAdeleIdempotentOfPlace_properties D).2.1 p q hpq
  rw [wAt_eq_smul, wAt_eq_smul, smul_neg, smul_smul, hpq', zero_smul, neg_zero]

section

variable {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D}
  {sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ} {sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ}
  {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}
  {f₀ : WO S T → ℂ} {μ : Measure (WO S T)} {𝓕 : Set (WO S T)}

theorem ip_base (hb : IsBase ψ θ S T sS sT ΛS ΛT f₀) (hμ : IsCovolOne (ratL T S) μ 𝓕) : ipO μ 𝓕 f₀ f₀ = 1 := by
  have hself : ipO μ 𝓕 f₀ f₀ = (nrm2 μ 𝓕 f₀ : ℂ) :=
    (GlobalTheory.T.theta_inner_product_hermitian D ψ S T μ 𝓕 (base_std hb) hμ f₀ f₀ (base_theta hb) (base_theta hb)).2.2.2.2.1
  rw [hself, restrictedTensorBasePoint_norm_sq hb hμ, Complex.ofReal_one]

theorem finite_mulSupport_ip (hb : IsBase ψ θ S T sS sT ΛS ΛT f₀) (hμ : IsCovolOne (ratL T S) μ 𝓕)
    {x₁ x₂ : Place D → WO S T → ℂ} (h₁ : IsRestricted ψ θ S T sS sT ΛS ΛT f₀ x₁)
    (h₂ : IsRestricted ψ θ S T sS sT ΛS ΛT f₀ x₂) :
    (Function.mulSupport fun p => ipO μ 𝓕 (x₁ p) (x₂ p)).Finite := by

  refine (h₁.2.union h₂.2).subset fun p hp => ?_
  rw [Function.mem_mulSupport] at hp
  by_contra hout
  simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hout
  exact hp (by rw [hout.1, hout.2]; exact ip_base hb hμ)

private theorem heisO_zero_twisted_operators (f : WO S T → ℂ) : heisO ψ S T 0 f = f := by
  funext u
  simp [heisO, symplOH, symplO, hO]

theorem pureTensor_innerProduct_eq_finprod_local_of_finset (hb : IsBase ψ θ S T sS sT ΛS ΛT f₀) (hμ : IsCovolOne (ratL T S) μ 𝓕) (s : Finset (Place D)) :
    ∀ (x₁ x₂ : Place D → WO S T → ℂ) (f₁ f₂ : WO S T → ℂ), (∀ p, p ∉ s → x₁ p = f₀) →
      IsPure ψ θ S T sS sT ΛS ΛT μ 𝓕 f₀ x₁ f₁ → IsPure ψ θ S T sS sT ΛS ΛT μ 𝓕 f₀ x₂ f₂ →
      ipO μ 𝓕 f₁ f₂ = ∏ᶠ p, ipO μ 𝓕 (x₁ p) (x₂ p) := by
  classical
  have hθ₀ : IsThetaFunO ψ S T f₀ := base_theta hb

  have hsymm : ∀ f g, IsThetaFunO ψ S T f → IsThetaFunO ψ S T g → ipO μ 𝓕 g f = (starRingEnd ℂ) (ipO μ 𝓕 f g) :=
    fun f g hf hg => (GlobalTheory.T.theta_inner_product_hermitian D ψ S T μ 𝓕 (base_std hb) hμ f g hf hg).2.1
  have hadj : ∀ f g, IsThetaFunO ψ S T f → IsThetaFunO ψ S T g → ∀ w,
      ipO μ 𝓕 (heisO ψ S T w f) g = ipO μ 𝓕 f (heisO ψ S T (-w) g) :=
    fun f g hf hg w => ((GlobalTheory.T.theta_inner_product_hermitian D ψ S T μ 𝓕 (base_std hb) hμ f g hf hg).2.2.2.2.2.2.1 w).2
  induction s using Finset.induction_on with
  | empty =>

    intro x₁ x₂ f₁ f₂ hx h₁ h₂
    have hx₁ : x₁ = fun _ => f₀ := funext fun p => hx p (by simp)
    subst hx₁
    have hf₁ : f₁ = f₀ :=
      (GlobalTheory.T.existsUnique_pureTensor_restrictedFamily D ψ θ S T sS sT ΛS ΛT f₀ μ 𝓕 hb hμ _ h₁.1).unique h₁
        (GlobalTheory.T.isPureTensor_base_vector_and_local_factor D ψ θ S T sS sT ΛS ΛT f₀ μ 𝓕 hb hμ).1
    subst hf₁
    obtain ⟨hfin, hprod⟩ := h₂.2.2 0
    simp only [wAt_zero, heisO_zero_twisted_operators] at hfin hprod
    rw [hsymm f₂ f₁ h₂.2.1 hθ₀, hprod, map_finprod _ hfin]
    exact finprod_congr fun p => (hsymm (x₂ p) f₁ (h₂.1.1 p).1 hθ₀).symm
  | insert q s hq ih =>
    intro x₁ x₂ f₁ f₂ hx h₁ h₂

    have hres : IsRestricted ψ θ S T sS sT ΛS ΛT f₀ (Function.update x₁ q f₀) := by
      refine ⟨fun p => ?_, h₁.1.2.subset fun p hp => ?_⟩
      · by_cases hpq : p = q
        · subst hpq
          rw [Function.update_self]
          exact base_isLocal hb p
        · rw [Function.update_of_ne hpq]
          exact h₁.1.1 p
      · by_cases hpq : p = q
        · subst hpq
          simp at hp
        · simpa [Function.update_of_ne hpq] using hp
    have hoff : ∀ p, p ∉ s → Function.update x₁ q f₀ p = f₀ := by
      intro p hp
      by_cases hpq : p = q
      · subst hpq
        exact Function.update_self _ _ _
      · rw [Function.update_of_ne hpq]
        exact hx p (by simp [hpq, hp])
    obtain ⟨g₁, hg₁, -⟩ := GlobalTheory.T.existsUnique_pureTensor_restrictedFamily D ψ θ S T sS sT ΛS ΛT f₀ μ 𝓕 hb hμ _ hres

    obtain ⟨f', hf', hc⟩ := GlobalTheory.T.pureTensor_update_factor_from_base_vector D ψ θ S T sS sT ΛS ΛT f₀ μ 𝓕 hb hμ (Function.update x₁ q f₀) x₁ g₁ q hg₁
      (Function.update_self _ _ _) (fun p hp => (Function.update_of_ne hp _ _).symm) (h₁.1.1 q)
    have hf'₁ : f' = f₁ := (GlobalTheory.T.existsUnique_pureTensor_restrictedFamily D ψ θ S T sS sT ΛS ΛT f₀ μ 𝓕 hb hμ _ h₁.1).unique hf' h₁
    subst hf'₁
    have hθq : IsThetaFunO ψ S T (x₂ q) := (h₂.1.1 q).1
    have key := hc f₂ (x₂ q) (∏ᶠ (p) (_ : p ≠ q), ipO μ 𝓕 (x₁ p) (x₂ p)) h₂.2.1 hθq (fun w => by
      rw [hadj g₁ f₂ hg₁.2.1 h₂.2.1]
      have hpw := GlobalTheory.T.heisenberg_operator_pure_tensor_place_by_place D ψ θ S T sS sT ΛS ΛT f₀ μ 𝓕 hb hμ x₂ f₂ h₂ (-(wAt q w))
      rw [ih _ _ _ _ hoff hg₁ hpw, ← mul_finprod_cond_ne q (finite_mulSupport_ip hb hμ hres hpw.1),
        Function.update_self, wAt_neg_wAt_self, ← hadj f₀ (x₂ q) hθ₀ hθq, mul_comm]
      congr 1
      refine finprod_congr fun p => finprod_congr fun hp => ?_
      rw [Function.update_of_ne hp, wAt_neg_wAt_ne hp, heisO_zero_twisted_operators])
    rw [key, mul_comm]
    exact mul_finprod_cond_ne q (finite_mulSupport_ip hb hμ h₁.1 h₂.1)

end

theorem ip_pure_eq_finprod : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (f₀ : WO S T → ℂ) (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsBase ψ θ S T sS sT ΛS ΛT f₀ → IsCovolOne (ratL T S) μ 𝓕 → ∀ (x₁ x₂ : Place D → WO S T → ℂ) (f₁ f₂ : WO S T → ℂ), IsPure ψ θ S T sS sT ΛS ΛT μ 𝓕 f₀ x₁ f₁ → IsPure ψ θ S T sS sT ΛS ΛT μ 𝓕 f₀ x₂ f₂ → (Function.mulSupport fun p => ipO μ 𝓕 (x₁ p) (x₂ p)).Finite ∧ ipO μ 𝓕 f₁ f₂ = ∏ᶠ p, ipO μ 𝓕 (x₁ p) (x₂ p) := by
  intro D ψ θ S T sS sT ΛS ΛT f₀ μ 𝓕 hb hμ x₁ x₂ f₁ f₂ h₁ h₂
  refine ⟨finite_mulSupport_ip hb hμ h₁.1 h₂.1, ?_⟩

  exact pureTensor_innerProduct_eq_finprod_local_of_finset hb hμ h₁.1.2.toFinset x₁ x₂ f₁ f₂
    (fun p hp => by simpa [Set.Finite.mem_toFinset] using hp) h₁ h₂

end GlobalTheory.PlaceTensor.PureScalar

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.StdFstInv

theorem mul_sub_mem {R : Type} [CommRing R] (O : Subring R) (c : R) {b a : ℕ} (Z : Matrix (Fin b) (Fin b) R)
    (hZ : ∀ i j, ∃ w ∈ O, Z i j - (1 : Matrix (Fin b) (Fin b) R) i j = c * w)
    (Y : Matrix (Fin b) (Fin a) R) (hY : ∀ i j, Y i j ∈ O) (i : Fin b) (j : Fin a) :
    ∃ w ∈ O, (Z * Y) i j - Y i j = c * w := by
  choose w hwO hw using hZ
  refine ⟨∑ k, w i k * Y k j, O.sum_mem fun k _ => O.mul_mem (hwO i k) (hY k j), ?_⟩
  have hsplit : (Z * Y) i j - Y i j = ∑ k, (Z i k - (1 : Matrix (Fin b) (Fin b) R) i k) * Y k j := by
    simp only [sub_mul, Finset.sum_sub_distrib]
    rw [← Matrix.mul_apply, ← Matrix.mul_apply, Matrix.one_mul]
  rw [hsplit, Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by rw [hw i k, mul_assoc]

theorem mem_iff {R : Type} [CommRing R] (O : Subring R) (J : Ideal O) (N : ℕ) (hN : (N : O) ∈ J) {p q w : R}
    (hp : p ∈ O) (hw : w ∈ O) (h : q - p = (N : R) * w) :
    (∃ h : q ∈ O, (⟨q, h⟩ : O) ∈ J) ↔ ∃ h : p ∈ O, (⟨p, h⟩ : O) ∈ J := by
  have hq : q ∈ O := by
    have e : q = p + (N : R) * w := by linear_combination h
    rw [e]
    exact O.add_mem hp (O.mul_mem (natCast_mem O N) hw)
  have key : (⟨q, hq⟩ : O) = ⟨p, hp⟩ + (N : O) * ⟨w, hw⟩ := by
    apply Subtype.ext
    show q = p + ((N : O) : R) * w
    rw [show ((N : O) : R) = (N : R) from map_natCast O.subtype N]
    linear_combination h
  have hNw : (N : O) * ⟨w, hw⟩ ∈ J := J.mul_mem_right _ hN
  constructor
  · rintro ⟨_, hJ⟩
    refine ⟨hp, ?_⟩
    rw [key] at hJ
    exact (J.add_mem_iff_left hNw).1 hJ
  · rintro ⟨_, hJ⟩
    refine ⟨hq, ?_⟩
    rw [key]
    exact J.add_mem hJ hNw

theorem fixed_mul {R : Type} [CommRing R] {b a : ℕ} (e : R) (M : Matrix (Fin b) (Fin b) R) (x : Matrix (Fin b) (Fin a) R)
    (H : ∀ i j, e * x i j = x i j) (i : Fin b) (j : Fin a) : e * (M * x) i j = (M * x) i j := by
  rw [Matrix.mul_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mul_left_comm, H k j]

theorem fixed_iff {R : Type} [CommRing R] {b a : ℕ} (e : R) (M : GL (Fin b) R) (P : Matrix (Fin a) (Fin a) R) (hP : P = 1)
    (x : Matrix (Fin b) (Fin a) R) :
    (∀ i j, e * (M.val * x * P) i j = (M.val * x * P) i j) ↔ ∀ i j, e * x i j = x i j := by
  subst hP
  simp only [Matrix.mul_one]
  constructor
  · intro h i j
    have hx : x = (M⁻¹).val * (M.val * x) := by
      rw [← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
    rw [hx]
    exact fixed_mul e _ _ h i j
  · intro h i j
    exact fixed_mul e _ _ h i j

variable {D : D7}

theorem mt_one (V : HSp D) : Formalism.L2.Theta.mt V (1 : GA D V)⁻¹ = 1 := by
  unfold Formalism.L2.Theta.mt
  rw [inv_one, map_one, Units.val_one]

theorem actO_neg_one (A WW : HSp D) (κ : GA D WW) (x : WO A WW) :
    actO (GlobalTheory.Grid.neg A) WW 1 κ x = actO A WW 1 κ x := by
  unfold actO
  rw [mt_one, mt_one]

theorem isHalf_iff (A WW : HSp D) (κ : GA D WW) (e : AE D) (x : WO A WW) :
    IsHalf e (actO A WW 1 κ x) ↔ IsHalf e x := by
  unfold IsHalf actO
  exact fixed_iff e (matHom WW κ) _ (mt_one A) x

theorem frMapO_eq {A WW : HSp D} (βA : GL (Fin A.rank) (Lev.EAf D)) {βW : GL (Fin WW.rank) (Lev.EAf D)}
    {κ : GA D WW} {z : GL (Fin WW.rank) (Formalism.L2.Herm.intAf D.host.F D.host.E)}
    (hz : Formalism.L2.DIV.frGL βW z = Lev.finE WW κ) (x : WO A WW) :
    frMapO A WW βA βW (actO A WW 1 κ x) =
      ((intGL D.host.F D.host.E _ z⁻¹)⁻¹).val * frMapO A WW βA βW x *
        (intGL D.host.F D.host.E _ (1 : GL (Fin A.rank) (Formalism.L2.Herm.intAf D.host.F D.host.E))).val := by
  have h1 := GlobalTheory.FrameRed.frMapO_actO (βS := βA) (βT := βW) (g := (1 : GA D A)) (h := κ⁻¹)
    (y := 1) (z := z⁻¹) (by rw [map_one, map_one]) (by rw [map_inv, map_inv, hz]) x
  rw [inv_one, inv_inv] at h1
  exact h1


theorem frMapO_eq' {A WW : HSp D} (βA : GL (Fin A.rank) (Lev.EAf D)) {βW : GL (Fin WW.rank) (Lev.EAf D)}
    {κ : GA D WW} {z : GL (Fin WW.rank) (Formalism.L2.Herm.intAf D.host.F D.host.E)}
    (hz : Formalism.L2.DIV.frGL βW z = Lev.finE WW κ) (x : WO A WW) :
    frMapO A WW βA βW (actO A WW 1 κ x) = (intGL D.host.F D.host.E _ z).val * frMapO A WW βA βW x := by
  rw [frMapO_eq βA hz x, map_inv (intGL D.host.F D.host.E WW.rank), inv_inv,
    map_one (intGL D.host.F D.host.E A.rank), Units.val_one, Matrix.mul_one]

theorem topL_int {b a : ℕ} (k : ℕ) {Y : Matrix (Fin b) (Fin a) (Lev.EAf D)} (hY : IsIntM (D := D) Y) :
    IsIntM (D := D) (topL k Y) := by
  intro i j
  unfold topL
  split_ifs with hij
  · exact hY _ _
  · exact zero_mem _

theorem topL_sub {R : Type} [CommRing R] (O : Subring R) (c : R) {b a : ℕ} (k : ℕ) {Y Y' : Matrix (Fin b) (Fin a) R}
    (h : ∀ i j, ∃ w ∈ O, Y' i j - Y i j = c * w) (i j : Fin k) :
    ∃ w ∈ O, topL k Y' i j - topL k Y i j = c * w := by
  unfold topL
  split_ifs with hij
  · exact h _ _
  · exact ⟨0, O.zero_mem, by rw [sub_self, mul_zero]⟩


theorem stdFst_actO : ∀ (D : D7) (A WW : HSp D) (ν : (AE D)ˣ →* Circle) (e : AE D) (Sf : Finset (Formalism.L2.DIV.Pl D.host.E)), IsIdemSum e Sf → ∀ (I : Ideal (𝓞 D.host.E)) (βA : GL (Fin A.rank) (Lev.EAf D)) (βW : GL (Fin WW.rank) (Lev.EAf D)) (N : ℕ), 0 < N → ((N : ℕ) : 𝓞 D.host.E) ∈ I → (∀ w ∈ Sf, ((N : ℕ) : 𝓞 D.host.E) ∈ w.asIdeal) → (∀ u : (AE D)ˣ, infPart D (u : AE D) = 1 → (∃ w ∈ Formalism.L2.Herm.intAf D.host.F D.host.E, toEAf D (u : AE D) = 1 + (N : Lev.EAf D) * w) → (∃ w ∈ Formalism.L2.Herm.intAf D.host.F D.host.E, toEAf D ((u⁻¹ : (AE D)ˣ) : AE D) = 1 + (N : Lev.EAf D) * w) → ν u = 1) → ∀ (κ : GA D WW) (z : GL (Fin WW.rank) (Formalism.L2.Herm.intAf D.host.F D.host.E)), Formalism.L2.DIV.frGL βW z = Lev.finE WW κ → (∀ a b, ∃ w ∈ Formalism.L2.Herm.intAf D.host.F D.host.E, ((z.1 a b : Formalism.L2.Herm.intAf D.host.F D.host.E) : Lev.EAf D) - (1 : Matrix (Fin WW.rank) (Fin WW.rank) (Lev.EAf D)) a b = (N : Lev.EAf D) * w) → ∀ x, GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdFst ν e I A WW βA βW (actO (GlobalTheory.Grid.neg A) WW 1 κ x) = GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdFst ν e I A WW βA βW x := by
  intro D A WW ν e Sf hSf I βA βW N hN hNI hNS hν κ z hz hz1 x
  unfold GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdFst
  rw [actO_neg_one, isHalf_iff, frMapO_eq' βA hz x]
  have hInt : IsIntM (D := D) ((intGL D.host.F D.host.E _ z).val * frMapO A WW βA βW x) ↔
      IsIntM (D := D) (frMapO A WW βA βW x) := by
    have h2 := GlobalTheory.FrameRed.isIntM_iff (D := D) z⁻¹
      (1 : GL (Fin A.rank) (Formalism.L2.Herm.intAf D.host.F D.host.E)) (frMapO A WW βA βW x)
    rwa [map_inv (intGL D.host.F D.host.E WW.rank), inv_inv, map_one (intGL D.host.F D.host.E A.rank),
      Units.val_one, Matrix.mul_one] at h2
  by_cases hM : IsIntM (D := D) (frMapO A WW βA βW x)
  · have hc : ∀ i j, ∃ w ∈ Formalism.L2.Herm.intAf D.host.F D.host.E,
        ((intGL D.host.F D.host.E _ z).val * frMapO A WW βA βW x) i j - frMapO A WW βA βW x i j =
          (N : Lev.EAf D) * w :=
      mul_sub_mem (Formalism.L2.Herm.intAf D.host.F D.host.E) (N : Lev.EAf D) (intGL D.host.F D.host.E _ z).val hz1 _ hM
    have hNJ : ((N : ℕ) : Formalism.L2.Herm.intAf D.host.F D.host.E) ∈ Formalism.L2.DIV.idS D.host.F I := by
      rw [← map_natCast (Formalism.L2.DIV.oToS D.host.F D.host.E) N]
      exact Ideal.mem_map_of_mem _ hNI
    have hId : ∀ i j, GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.InId I (((intGL D.host.F D.host.E _ z).val * frMapO A WW βA βW x) i j) ↔
        GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.InId I (frMapO A WW βA βW x i j) := fun i j => by
      obtain ⟨w, hw, hq⟩ := hc i j
      exact GlobalTheory.StdFstInv.mem_iff _ _ N hNJ (hM i j) hw hq
    have hU := GlobalTheory.UnitCharCong.unitChar_eq_of_natCong D ν e Sf hSf N hN hNS hν _ _ (topL_int A.rank hM)
      (topL_sub _ _ A.rank hc)
    rw [hU]
    have hcond := and_congr (Iff.rfl (a := IsHalf e x)) (and_congr hInt
      (forall_congr' fun (i : Fin WW.rank) => forall_congr' fun (j : Fin A.rank) =>
        imp_congr (Iff.rfl (a := A.rank ≤ (i : ℕ))) (hId i j)))
    split_ifs with h1 h2 h2
    · rfl
    · exact absurd (hcond.1 h1) h2
    · exact absurd (hcond.2 h2) h1
    · rfl
  · rw [if_neg (fun h => hM (hInt.1 h.2.1)), if_neg (fun h => hM h.2.1)]

end GlobalTheory.StdFstInv

end
end

section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR GlobalTheory.WeilParts GlobalTheory.StepLaw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StepLaw

theorem fixesVacAt_nonsplit_of_charFrame : ∀ (D : D7) (C : Formalism.L2.Host.CharFrame D) (η : (AE D)ˣ →* Circle), ChrEq η C.eta → ResEta D η 1 → ∀ (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsWeilDatumO ψ S T χS χT om → IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ v ε, NonSplitAt D v ε → UnramAt ε χS → UnramAt ε χT → FixesVacAt ψ S T ΛS ΛT om v ε := by
  intro D C η hη hres ψ S T χS χT om ΛS ΛT hW hS hT v ε hv hχS hχT
  have hStd : IsStdChar D ψ (-1) := hW.std
  have hTilde : IsEtaTilde D η := GlobalTheory.T.isUnramifiedEtaTildeHeckeChar_of_local_components D C η hη hres
  exact GlobalTheory.T.weilDatum_fixes_vacuum_nonSplitPlace_unramified D ψ hStd S T ΛS ΛT hS hT χS χT om ⟨η, hTilde⟩ hW v ε hv hχS hχT

end GlobalTheory.StepLaw
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.LiftRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.thetaLift_adjoint_keeps_spherical_parts_off_tuple : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Hk3.HoweUnram → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → (∀ t P, GlobalTheory.Hk3.Good R t P → Formalism.DivisionValues.conjPl P = P → GlobalTheory.Hk3.FixAll R t P) → Kept R := by
  first | exact @GlobalTheory.KeptRows.kept | exact GlobalTheory.KeptRows.kept | (intros; apply GlobalTheory.KeptRows.kept <;> assumption)
end
