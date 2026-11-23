module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnipotentBlockColumnIndex
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle302
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle275
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle301
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNineTermTransgressionZeroApply
public import Formalism.GaloisCohomology.LocalTateDualityK
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LengthCyclotomicBlockCocyclesLeSha
public import Formalism.LocalRingCardinality.AdicCompletionLocal.InstIsAdicCompleteOCSpanSingletonSetCast
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle006
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle113
public import Formalism.SharpRestriction.LevelLetterCocycles.ElementDenominator
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle013
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle012
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Countable
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.IntegralCasts.Bundle001
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle014
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle012
import Formalism.SharpRestriction.LevelLetterCocycles.BlochKatoPhases
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
public import Mathlib.Algebra.Algebra.ZMod
public import Formalism.PeriodIntegrals.Bundle019

@[expose] public section

section

open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.CuspGeneric

namespace GlobalTheory.CuspGeneric

theorem colT_blkU_mul : ∀ (E : Type) [Field E] [NumberField E] (a : ℕ) (ψ : AddChar (Ad E) ℂ), StdPsi ψ →
    ∀ (m : ℕ) (f : GA E a → ℂ), Good ψ (m + 1) f → ∀ (y : UnipotentBlockColumnIndex a (m + 1) (m + 1) → Ad E) (g : GA E a),
      colT ψ (m + 1) f (blkU y * g) = ψ (dot (eLast a (m + 1)) y) * colT ψ (m + 1) f g := by
  intro E _ _ a ψ hψ m f hf y g
  have hper := per_coef (a := a) hψ (eLast a (m + 1)) hf.cont
    (fun c g' => hf.left _ (isMir_blkU c) g') g
  have hT := GlobalTheory.T.quotientAverage_translate_invariant (UnipotentBlockColumnIndex a (m + 1) (m + 1) → Ad E) (ratV E (UnipotentBlockColumnIndex a (m + 1) (m + 1)))
    (isCoLat_ratV E _) _ hper y
  have hpt : (fun x : UnipotentBlockColumnIndex a (m + 1) (m + 1) → Ad E =>
        ψ (-dot (eLast a (m + 1)) x) * f (blkU x * (blkU y * g))) =
      fun x => ψ (dot (eLast a (m + 1)) y) *
        (ψ (-dot (eLast a (m + 1)) (x + y)) * f (blkU (x + y) * g)) := by
    funext x
    have hd : dot (eLast a (m + 1)) (x + y) = dot (eLast a (m + 1)) x + dot (eLast a (m + 1)) y := by
      simp only [dot, Pi.add_apply, mul_add, Finset.sum_add_distrib]
    have hu : (blkU (x + y) : GA E a) = blkU x * blkU y := posU_add _ x y
    have h1 : ψ (dot (eLast a (m + 1)) y) * ψ (-dot (eLast a (m + 1)) y) = 1 := by
      rw [← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one]
    rw [hd, hu, neg_add, AddChar.map_add_eq_mul, mul_assoc (blkU x)]
    calc ψ (-dot (eLast a (m + 1)) x) * f (blkU x * (blkU y * g))
        = (ψ (dot (eLast a (m + 1)) y) * ψ (-dot (eLast a (m + 1)) y)) *
            (ψ (-dot (eLast a (m + 1)) x) * f (blkU x * (blkU y * g))) := by rw [h1, one_mul]
      _ = _ := by ring
  change avg _ (fun x => ψ (-dot (eLast a (m + 1)) x) * f (blkU x * (blkU y * g))) =
    _ * avg _ (fun x => ψ (-dot (eLast a (m + 1)) x) * f (blkU x * g))
  rw [hpt, avg_const_mul]
  exact congrArg _ hT

end GlobalTheory.CuspGeneric
end

section

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.CuspGeneric

namespace GlobalTheory.CuspGeneric

section General

variable {G₁ G₂ : Type} [AddCommGroup G₁] [TopologicalSpace G₁] [AddCommGroup G₂] [TopologicalSpace G₂]

variable [IsTopologicalAddGroup G₁] [LocallyCompactSpace G₁] [SecondCountableTopology G₁] [T2Space G₁]
  [IsTopologicalAddGroup G₂] [LocallyCompactSpace G₂] [SecondCountableTopology G₂] [T2Space G₂]

def swapEquiv (G₁ G₂ : Type) [AddCommGroup G₁] [TopologicalSpace G₁] [AddCommGroup G₂] [TopologicalSpace G₂] :
    (G₂ × G₁) ≃ₜ+ (G₁ × G₂) :=
  { AddEquiv.prodComm with
    continuous_toFun := continuous_swap
    continuous_invFun := continuous_swap }

theorem avg_comm_of_isCoLat {Γ₁ : AddSubgroup G₁} {Γ₂ : AddSubgroup G₂} (h₁ : IsCoLat Γ₁) (h₂ : IsCoLat Γ₂)
    (Φ : G₁ × G₂ → ℂ) (hΦ : Per (Γ₁.prod Γ₂) Φ) :
    avg Γ₁ (fun x => avg Γ₂ (fun y => Φ (x, y))) = avg Γ₂ (fun y => avg Γ₁ (fun x => Φ (x, y))) := by
  have hs : Per (Γ₂.prod Γ₁) (fun p : G₂ × G₁ => Φ (p.2, p.1)) := by
    refine ⟨hΦ.1.comp continuous_swap, fun γ hγ x => ?_⟩
    exact hΦ.2 (γ.2, γ.1) ⟨hγ.2, hγ.1⟩ (x.2, x.1)
  have a := GlobalTheory.T.quotientAverage_prod_fubini G₁ G₂ Γ₁ Γ₂ h₁ h₂ Φ hΦ
  have b := GlobalTheory.T.quotientAverage_prod_fubini G₂ G₁ Γ₂ Γ₁ h₂ h₁ _ hs
  have c := GlobalTheory.T.quotientAverage_map_lattice_equiv (G₂ × G₁) (G₁ × G₂) (Γ₂.prod Γ₁) (Γ₁.prod Γ₂) (isCoLat_prod h₂ h₁) (isCoLat_prod h₁ h₂) (swapEquiv G₁ G₂)
    (fun x => ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩) Φ hΦ
  exact a.symm.trans (c.symm.trans b)

end General

theorem avg_comm (E : Type) [Field E] [NumberField E] (ι κ : Type) [Fintype ι] [Fintype κ]
    (Φ : (ι → Ad E) × (κ → Ad E) → ℂ) (hΦ : Per ((ratV E ι).prod (ratV E κ)) Φ) :
    avg (ratV E ι) (fun x => avg (ratV E κ) (fun y => Φ (x, y))) =
      avg (ratV E κ) (fun y => avg (ratV E ι) (fun x => Φ (x, y))) :=
  avg_comm_of_isCoLat (isCoLat_ratV E ι) (isCoLat_ratV E κ) Φ hΦ

end GlobalTheory.CuspGeneric
end
end

section

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.CuspGeneric

namespace GlobalTheory.CuspGeneric

def sumArrowAddHomeo (A ι κ : Type) [AddCommGroup A] [TopologicalSpace A] :
    ((ι → A) × (κ → A)) ≃ₜ+ (ι ⊕ κ → A) where
  toFun p := Sum.elim p.1 p.2
  invFun f := (fun i => f (Sum.inl i), fun j => f (Sum.inr j))
  left_inv _ := rfl
  right_inv f := by ext (i | j) <;> rfl
  map_add' p q := by ext (i | j) <;> rfl
  continuous_toFun := by
    refine continuous_pi fun s => ?_
    rcases s with i | j
    · exact (continuous_apply i).comp continuous_fst
    · exact (continuous_apply j).comp continuous_snd
  continuous_invFun :=
    (continuous_pi fun i => continuous_apply _).prodMk (continuous_pi fun j => continuous_apply _)

theorem sum_elim_mem_ratV (E : Type) [Field E] [NumberField E] (ι κ : Type) (x : ι → Ad E) (y : κ → Ad E) :
    Sum.elim x y ∈ ratV E (ι ⊕ κ) ↔ x ∈ ratV E ι ∧ y ∈ ratV E κ := by
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨⟨fun i => c (Sum.inl i), funext fun i => congrFun hc (Sum.inl i)⟩,
      ⟨fun j => c (Sum.inr j), funext fun j => congrFun hc (Sum.inr j)⟩⟩
  · rintro ⟨⟨c, rfl⟩, ⟨d, rfl⟩⟩
    refine ⟨Sum.elim c d, funext fun s => ?_⟩
    rcases s with i | j <;> rfl

theorem avg_sum_index : ∀ (E : Type) [Field E] [NumberField E] (ι κ : Type) [Fintype ι] [Fintype κ]
    (Φ : (ι ⊕ κ → Ad E) → ℂ), Per (ratV E (ι ⊕ κ)) Φ →
    avg (ratV E (ι ⊕ κ)) Φ = avg (ratV E ι) (fun x => avg (ratV E κ) (fun y => Φ (Sum.elim x y))) := by
  intro E _ _ ι κ _ _ Φ hΦ
  have hι := isCoLat_ratV E ι
  have hκ := isCoLat_ratV E κ
  have hs := isCoLat_ratV E (ι ⊕ κ)
  have hp : IsCoLat ((ratV E ι).prod (ratV E κ)) := by
    obtain ⟨d₁, K₁, hK₁, c₁⟩ := hι
    obtain ⟨d₂, K₂, hK₂, c₂⟩ := hκ
    refine ⟨?_, K₁ ×ˢ K₂, hK₁.prod hK₂, fun x => ?_⟩
    · let f : ↥((ratV E ι).prod (ratV E κ)) → ratV E ι × ratV E κ := fun p => (⟨p.1.1, p.2.1⟩, ⟨p.1.2, p.2.2⟩)
      have hf : Continuous f :=
        (continuous_subtype_val.fst.subtype_mk _).prodMk (continuous_subtype_val.snd.subtype_mk _)
      refine DiscreteTopology.of_continuous_injective hf fun p q h => ?_
      have e₁ := congrArg (fun r => (r.1 : ι → Ad E)) h
      have e₂ := congrArg (fun r => (r.2 : κ → Ad E)) h
      exact Subtype.ext (Prod.ext e₁ e₂)
    · obtain ⟨γ₁, m₁, k₁⟩ := c₁ x.1
      obtain ⟨γ₂, m₂, k₂⟩ := c₂ x.2
      exact ⟨(γ₁, γ₂), ⟨m₁, m₂⟩, k₁, k₂⟩
  let e := sumArrowAddHomeo (Ad E) ι κ
  have he : ∀ p, e p ∈ ratV E (ι ⊕ κ) ↔ p ∈ (ratV E ι).prod (ratV E κ) := fun p =>
    (sum_elim_mem_ratV E ι κ p.1 p.2).trans AddSubgroup.mem_prod.symm
  have hper : Per ((ratV E ι).prod (ratV E κ)) (fun p => Φ (e p)) := by
    refine ⟨hΦ.1.comp e.continuous_toFun, fun γ hγ x => ?_⟩
    have : e (γ + x) = e γ + e x := map_add e γ x
    simp only [this]
    exact hΦ.2 _ ((he γ).2 hγ) _
  have h1 := GlobalTheory.T.quotientAverage_map_lattice_equiv _ _ _ _ hp hs e he Φ hΦ
  have h2 := GlobalTheory.T.quotientAverage_prod_fubini _ _ _ _ hι hκ _ hper
  rw [← h1, h2]
  rfl

end GlobalTheory.CuspGeneric
end
end

section

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published

namespace GlobalTheory.LocTwoOnto

theorem H0_twDual_eq_zero {R Γ M : Type} [CommRing R] [Group Γ] [AddCommGroup M] [Module R M]
    (μ : Γ →* Rˣ) (ρ : Representation R Γ M)
    (hc : ∀ φ : M →+ R, (∀ g h m, φ (ρ g (ρ h m)) = φ (ρ h (ρ g m))) → φ = 0)
    (y : H0 (twDual μ ρ)) : y = 0 := by
  obtain ⟨φ, hφ⟩ := y
  have hfix : ∀ g, twDual μ ρ g φ = φ := hφ
  let f : M →ₗ[R] R := φ

  have hmul : ∀ g m, f (ρ g m) = ((μ g : Rˣ) : R) * f m := by
    intro g m
    have h := congrArg (fun ψ : TDual R M => ψ (ρ g m)) (hfix g)
    simp only [twDual_apply, Representation.inv_self_apply] at h
    exact h.symm

  have hzero : f.toAddMonoidHom = 0 :=
    hc _ fun g h m => by
      simp only [LinearMap.toAddMonoidHom_coe, hmul]
      ring
  apply Subtype.ext
  apply DFunLike.ext
  intro m
  have hm := congrArg (fun k : M →+ R => k m) hzero
  simp only [LinearMap.toAddMonoidHom_coe, AddMonoidHom.zero_apply] at hm
  exact hm

theorem loc2_surjective : PoitouTateTotallyComplex → ∀ (F Ω : Type) [Field F] [NumberField F] [_root_.NumberField.IsTotallyComplex F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (Λ M : Type) [CommRing Λ] [AddCommGroup M] [Module Λ M] [Finite M] [TopologicalSpace M] [DiscreteTopology M] (S : Finset (HeightOneSpectrum (𝓞 F))) (Av : S → ValuationSubring Ω) (ρ : Representation Λ (GS Ω (S : Set (HeightOneSpectrum (𝓞 F)))) M), (∀ m : M, l • m = 0) → ContainsAbove S l → (∀ v, IsPlaceOver (Av v) v.1) → ContAction ρ → (∀ (C : Type) [AddCommGroup C] (φ : M →+ C), (∀ g h m, φ (ρ g (ρ h m)) = φ (ρ h (ρ g m))) → φ = 0) → ∀ x : ∀ v : S, H2 (ρ.comp (locFam S Av v)), ∃ y : H2 ρ, ∀ v, resH2 ρ (locFam S Av v) (continuous_locFam S Av v) y = x v := by
  intro hPT F Ω _ _ _ _ _ _ l _ Λ M _ _ _ _ _ _ S Av ρ hl hS hAv hρ hcomm x
  have hl0 : 0 < l ^ 1 := pow_pos (Fact.out : l.Prime).pos 1
  have : NeZero (l ^ (1 : ℕ)) := ⟨hl0.ne'⟩

  have hl1 : ∀ m : M, (l ^ (1 : ℕ)) • m = 0 := fun m => by rw [pow_one]; exact hl m
  have instZ : Module (ZMod (l ^ (1 : ℕ))) M := AddCommGroup.zmodModule hl1
  have : ContinuousConstSMul (ZMod (l ^ (1 : ℕ))) M := ⟨fun _ => continuous_of_discreteTopology⟩
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective

  obtain ⟨ζ, hζ⟩ := IsAlgClosed.exists_root (Polynomial.cyclotomic (l ^ (1 : ℕ)) Ω)
    (Polynomial.degree_cyclotomic_pos _ _ hl0).ne'
  have hζ' : IsPrimitiveRoot ζ (l ^ (1 : ℕ)) := (Polynomial.isRoot_cyclotomic_iff_charZero hl0).1 hζ
  obtain ⟨inv, -, hall⟩ := hPT F Ω l 1 one_pos ζ hζ'
  obtain ⟨μ, hμ⟩ := PoitouTate.exists_lift_cycMod (Ω := Ω) (r := 1) hS

  let ρ' : GS Ω (S : Set (HeightOneSpectrum (𝓞 F))) →* Module.End (ZMod (l ^ (1 : ℕ))) M :=
    { toFun := fun g => (ρ g).toAddMonoidHom.toZModLinearMap (l ^ (1 : ℕ))
      map_one' := by ext m; simp
      map_mul' := fun g h => by ext m; simp }
  have hρ' : ContAction ρ' := hρ
  obtain ⟨hNT, -⟩ := hall S hS Av hAv μ hμ M ρ' hρ'
  have hc' : ∀ φ : M →+ ZMod (l ^ (1 : ℕ)), (∀ g h m, φ (ρ' g (ρ' h m)) = φ (ρ' h (ρ' g m))) → φ = 0 :=
    fun φ hφ => hcomm (ZMod (l ^ (1 : ℕ))) φ hφ

  choose z hz using fun v => Submodule.Quotient.mk_surjective _ (x v)
  let z' : ∀ v : S, Z2 (ρ'.comp (locFam S Av v)) := fun v => ⟨(z v).1, (z v).2⟩

  obtain ⟨y', hy'⟩ := LinearMap.mem_range.1
    ((hNT.mem_range_localization_H2_iff (fun v => Submodule.Quotient.mk (z' v))).2 fun y => by
      rw [H0_twDual_eq_zero μ ρ' hc' y]
      simp)
  obtain ⟨w', hw'⟩ := Submodule.Quotient.mk_surjective _ y'
  let w : Z2 ρ := ⟨w'.1, w'.2⟩
  refine ⟨Submodule.Quotient.mk w, fun v => ?_⟩
  have hv := congrFun hy' v
  rw [← hw'] at hv
  change resH2 ρ' (locFam S Av v) (continuous_locFam S Av v) (Submodule.Quotient.mk w') =
    Submodule.Quotient.mk (z' v) at hv
  rw [resH2, Submodule.mapQ_apply, Submodule.Quotient.eq] at hv
  rw [← hz v, resH2, Submodule.mapQ_apply, Submodule.Quotient.eq]
  simp only [Submodule.mem_comap, Submodule.coe_subtype] at hv ⊢

  obtain ⟨c, hc, hcd⟩ := (separated_dvr_second_cohomology_mem _ _).1 hv
  refine (separated_dvr_second_cohomology_mem _ _).2 ⟨c, hc, ?_⟩
  funext p
  have hp := congrFun hcd p
  exact hp

end GlobalTheory.LocTwoOnto
end
end

section

noncomputable section

open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.GaloisCohomology Pointwise

namespace GlobalTheory.SelInfl

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
  {S : Set (HeightOneSpectrum (𝓞 F))} {R : Type} [CommRing R] {M : Type}
  [AddCommGroup M] [Module R M] [TopologicalSpace M] [IsTopologicalAddGroup M]
  [ContinuousConstSMul R M] [T2Space M] (rhoS : Representation R (GS Ω S) M) (A : Places F Ω)

theorem vanish {f : G F Ω → M} (hf : f ∈ Z1 (rhoS.comp (toGS Ω S) : Representation R (G F Ω) M))
    (hv0 : ∀ v ∉ S, ∃ m, ∀ g ∈ Ine (F := F) (A.1 v), f g = rhoS (toGS Ω S g) m - m) (n : G F Ω)
    (hn : n ∈ NS Ω S) : f n = 0 := by
  obtain ⟨hfc, hfco⟩ := (ReciprocityTheory.Gal.mem_Z1_iff_cocycle _ f).1 hf
  have ht : ∀ g ∈ NS Ω S, toGS Ω S g = 1 := fun g hg => (QuotientGroup.eq_one_iff g).2 hg
  have hρ : ∀ g ∈ NS Ω S, ∀ x : M, (rhoS.comp (toGS Ω S)) g x = x := by
    intro g hg x
    rw [MonoidHom.comp_apply, ht g hg, map_one, Module.End.one_apply]
  have h1 : f 1 = 0 := by
    have := hfco 1 1
    rw [mul_one, map_one, Module.End.one_apply] at this
    simpa using this
  have hinv : ∀ a ∈ NS Ω S, f a = 0 → f a⁻¹ = 0 := by
    intro a ha h0
    have := hfco a a⁻¹
    rw [mul_inv_cancel, h1, h0, zero_add, hρ a ha] at this
    exact this.symm
  let H : Subgroup (G F Ω) :=
    { carrier := {g | g ∈ NS Ω S ∧ f g = 0}
      one_mem' := ⟨(NS Ω S).one_mem, h1⟩
      mul_mem' := fun {a b} ha hb =>
        ⟨(NS Ω S).mul_mem ha.1 hb.1, by rw [hfco, ha.2, hb.2, map_zero, add_zero]⟩
      inv_mem' := fun {a} ha => ⟨(NS Ω S).inv_mem ha.1, hinv a ha.1 ha.2⟩ }
  have hconj : ∀ n ∈ H, ∀ g : G F Ω, g * n * g⁻¹ ∈ H := by
    intro n hn g
    refine ⟨(normal_NS S).conj_mem n hn.1 g, ?_⟩
    have e1 := hfco (g * n) g⁻¹
    have e2 := hfco g n
    have e3 := hfco g g⁻¹
    rw [map_mul, Module.End.mul_apply, hρ n hn.1, e2, hn.2, map_zero, add_zero] at e1
    rw [mul_inv_cancel, h1] at e3
    rw [e1, ← e3]
  have hHn : H.Normal := ⟨hconj⟩
  have hclosed : IsClosed (H : Set (G F Ω)) :=
    (isClosed_NS Ω S).inter (isClosed_singleton.preimage hfc)
  have hsub : (⋃ v ∈ Sᶜ, ⋃ A' ∈ {A' : ValuationSubring Ω | IsPlaceOver A' v}, Inertia (F := F) A') ⊆ H := by
    intro σ hσ
    have hσN : σ ∈ NS Ω S :=
      Subgroup.le_topologicalClosure _ (Subgroup.subset_normalClosure hσ)
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq] at hσ
    obtain ⟨v, hv, A', hA', hσA'⟩ := hσ
    obtain ⟨γ, hγ⟩ := exists_smul_eq_of_isPlaceOver (A.2 v) hA'
    have hσI : σ ∈ Ine (F := F) (γ • A.1 v) := by
      rw [hγ]
      exact mem_Ine.2 hσA'
    have hτ := GlobalTheory.Cut.ShaBound.conj_mem_Ine' hσI
    have hτN : γ⁻¹ * σ * γ ∈ NS Ω S := by
      have := (normal_NS S).conj_mem σ hσN γ⁻¹
      rwa [inv_inv] at this
    obtain ⟨m, hm⟩ := hv0 v hv
    have hfτ : f (γ⁻¹ * σ * γ) = 0 := by
      rw [hm _ hτ, ht _ hτN, map_one, Module.End.one_apply, sub_self]
    have := hconj _ ⟨hτN, hfτ⟩ γ
    have e : γ * (γ⁻¹ * σ * γ) * γ⁻¹ = σ := by group
    rw [e] at this
    exact this
  have hle : NS Ω S ≤ H :=
    Subgroup.topologicalClosure_minimal _ (Subgroup.normalClosure_le_normal hsub) hclosed
  exact (hle hn).2

theorem selAllLeInf : Formalism.GaloisCohomology.SelAllLeInf := by
  intro F Ω _ _ _ _ _ S R _ M _ _ _ _ _ _ rhoS _ A L hL x hx
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  have hloc := (ReciprocityTheory.Gal.mem_Sel _ _ _ _ _).1 hx
  have hv0 : ∀ v ∉ S, ∃ m, ∀ g ∈ Ine (F := F) (A.1 v), z.1 g = rhoS (toGS Ω S g) m - m := by
    intro v hv
    have h1 := hL v hv (hloc v)
    have h2 : (Submodule.Quotient.mk (restrictCocycles1 _ ((Ine (F := F) (A.1 v)).subgroupOf (Dec (F := F) (A.1 v))).subtype
        continuous_subtype_val (restrictCocycles1 _ (Dec (F := F) (A.1 v)).subtype continuous_subtype_val z)) :
        H1 _) = 0 := h1
    have h3 := (Submodule.Quotient.mk_eq_zero _).1 h2
    rw [Submodule.mem_comap] at h3
    obtain ⟨m, hm⟩ := (ReciprocityTheory.Gal.mem_coboundaries1 _ _).1 h3
    refine ⟨m, fun g hg => ?_⟩
    have gD : g ∈ Dec (F := F) (A.1 v) := Ine_le_Dec _ hg
    have gJ : (⟨g, gD⟩ : Dec (F := F) (A.1 v)) ∈ (Ine (F := F) (A.1 v)).subgroupOf (Dec (F := F) (A.1 v)) := by
      rw [Subgroup.mem_subgroupOf]
      exact hg
    exact hm ⟨⟨g, gD⟩, gJ⟩
  have hvan : ∀ n ∈ NS Ω S, z.1 n = 0 := fun n hn => vanish rhoS A z.2 hv0 n hn
  obtain ⟨hzc, hzco⟩ := (ReciprocityTheory.Gal.mem_Z1_iff_cocycle _ _).1 z.2
  have hwd : ∀ a b : G F Ω, a⁻¹ * b ∈ NS Ω S → z.1 a = z.1 b := by
    intro a b hab
    have := hzco a (a⁻¹ * b)
    rw [mul_inv_cancel_left, hvan _ hab, map_zero, add_zero] at this
    exact this.symm
  let z' : GS Ω S → M := fun q =>
    Quotient.liftOn' q z.1 (fun a b hab => hwd a b (QuotientGroup.leftRel_apply.1 hab))
  have hz'c : Continuous z' := Continuous.quotient_liftOn' hzc _
  have hz'co : ∀ p q : GS Ω S, z' (p * q) = z' p + rhoS p (z' q) := by
    intro p q
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective p
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective q
    exact hzco a b
  let w : Z1 rhoS := ⟨z', (ReciprocityTheory.Gal.mem_Z1_iff_cocycle _ _).2 ⟨hz'c, hz'co⟩⟩
  exact ⟨Submodule.Quotient.mk w, rfl⟩

end GlobalTheory.SelInfl

end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.Per

theorem exists_pow_eq_one_of_algClosure_zmod (l : ℕ) [hl : Fact l.Prime] (a : AlgebraicClosure (ZMod l))
    (ha : a ≠ 0) : ∃ m : ℕ, 0 < m ∧ ¬ l ∣ m ∧ a ^ m = 1 := by
  first
  | exact @_root_.GlobalTheory.ProofStatement.main
  | exact _root_.GlobalTheory.ProofStatement.main
  | (apply _root_.GlobalTheory.ProofStatement.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.ProofStatement.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.ProofStatement.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.ProofStatement.main ..)

theorem exists_isPrimitiveRoot_tilt (l : ℕ) [hl : Fact l.Prime] (m : ℕ) (hm : 0 < m) (hlm : ¬ l ∣ m) :
    ∃ e : Per.Fl l, IsPrimitiveRoot e m := by
  haveI : NeZero m := ⟨hm.ne'⟩
  obtain ⟨x, hx⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (Om l) m
  obtain ⟨e, he, hex⟩ := exists_tilt_root_of_unity l x m hm hlm hx.pow_eq_one
  refine ⟨e, he, fun d hd => hx.dvd_of_pow_eq_one d ?_⟩
  have h1 : e.untilt ^ d = 1 := by rw [← map_pow, hd, map_one]
  have h2 : (x : ℂ_[l]) ^ d = 1 := by
    rw [← hex]
    exact_mod_cast congrArg Subtype.val h1
  apply (algebraMap (Om l) ℂ_[l]).injective
  rw [map_pow, map_one]
  exact h2

theorem nonempty_algClosure_zmod_to_tilt :
    ∀ (l : ℕ) [Fact l.Prime], Nonempty (AlgebraicClosure (ZMod l) →+* Per.Fl l) := by
  intro l hl
  haveI : IsDomain (Per.Fl l) := inferInstance
  haveI : CharP (Per.Fl l) l := inferInstance
  let Ω := AlgebraicClosure (FractionRing (Per.Fl l))
  let j : Per.Fl l →+* Ω :=
    (algebraMap (FractionRing (Per.Fl l)) Ω).comp (algebraMap (Per.Fl l) (FractionRing (Per.Fl l)))
  have hj : Function.Injective j :=
    (algebraMap (FractionRing (Per.Fl l)) Ω).injective.comp (IsFractionRing.injective _ _)
  haveI : CharP Ω l := charP_of_injective_ringHom hj l
  letI : Algebra (ZMod l) Ω := ZMod.algebra Ω l
  let f₀ : AlgebraicClosure (ZMod l) →ₐ[ZMod l] Ω := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  have hr : ∀ a, (f₀ : AlgebraicClosure (ZMod l) →+* Ω) a ∈ j.range := by
    intro a
    by_cases ha : a = 0
    · rw [ha, map_zero]; exact zero_mem _
    obtain ⟨m, hm, hlm, ham⟩ := exists_pow_eq_one_of_algClosure_zmod l a ha
    obtain ⟨e, he⟩ := exists_isPrimitiveRoot_tilt l m hm hlm
    haveI : NeZero m := ⟨hm.ne'⟩
    obtain ⟨i, -, hi⟩ := (he.map_of_injective hj).eq_pow_of_pow_eq_one
      (ξ := (f₀ : AlgebraicClosure (ZMod l) →+* Ω) a) (by rw [← map_pow, ham, map_one])
    exact ⟨e ^ i, by rw [map_pow, hi]⟩
  let E : Per.Fl l ≃+* j.range := RingEquiv.ofBijective j.rangeRestrict
    ⟨fun x y h => hj (congrArg Subtype.val h), j.rangeRestrict_surjective⟩
  exact ⟨E.symm.toRingHom.comp ((f₀ : AlgebraicClosure (ZMod l) →+* Ω).codRestrict j.range hr)⟩

end GlobalTheory.Per
end

section

theorem _root_.GlobalTheory.T.frobenius_sub_one_surjective_witt_tilt : Formalism.MainNotions.ElementDenominator.ArtinSchreierWittOnto := fun l _ x =>
  PI.ArtSch.main_of witt_lift (tiltSurjectiveOfParts rootModP_holds tilt_divisibility smallSurjective) l x
end
