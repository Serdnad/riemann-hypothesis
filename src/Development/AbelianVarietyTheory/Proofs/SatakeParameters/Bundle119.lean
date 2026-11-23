module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle008
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.NotInSupportOfSubsingleton
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle008
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle049
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsLocallyConstantOrbit
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwahoriProjSurjective
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle122
import Mathlib.Algebra.Module.StablyFree.Basic
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle012
public import Formalism.SharpRestriction.Divisibility.JetPolynomialLogs.LetterLogIntegrality
public import Formalism.GaussJetBounds.GaussJetProofs.Transfer
public import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.BiextensionHypothesesOfLevelOne
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PhiMapsAndOmegaLaw
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.IsDiscriminantTwelfthRootOfIdealLattice
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsNotCongPow
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasExponentZeroIff
import Formalism.ConjugateSelfDual.Bundle001
import ReciprocityTheory.GaloisValuations.GlobalA

@[expose] public section

section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain GlobalTheory.PRep GlobalTheory.SmGL
  GlobalTheory.SplitWeil GlobalTheory.RowTie GlobalTheory.SplitRead ValuativeRel

namespace GlobalTheory.SatakeExists

theorem exists_eigenform {G V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V} (hρ : IsSmooth ρ) {H : Subgroup G}
    (hH : IsCompact (H : Set G)) (hcomm : ∀ a b : G, a * b = b * a)
    (hn : ∀ g, MonoidHom.id G g ∈ Subgroup.normalizer (H : Set G))
    [FiniteDimensional ℂ (fixed ρ H)] [Nontrivial (fixed ρ H)] :
    ∃ (χ : G →* ℂˣ) (l : V →ₗ[ℂ] ℂ), l ≠ 0 ∧ (∀ g v, l (ρ g v) = (χ g : ℂ) * l v) ∧
      ∀ h ∈ H, χ h = 1 := by
  have hc := LocGL.isCompl_fixed_twKer hρ hH
  let T : Subrepresentation ρ := ⟨twKer ρ H 1, fun g _ hv => twKer_le_comap ρ H g (hn g) hv⟩
  let σ := onFixed ρ H (MonoidHom.id G) hn
  let p : ρ.IntertwiningMap σ :=
    ⟨Submodule.projectionOnto _ _ hc, fun g => LinearMap.ext fun v => by
      obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 (hc.sup_eq_top ▸ Submodule.mem_top (x := v))
      have e1 := Submodule.projectionOnto_apply_left hc ⟨a, ha⟩
      have e2 := Submodule.projectionOnto_apply_right hc ⟨b, hb⟩
      have e3 := Submodule.projectionOnto_apply_left hc (σ g ⟨a, ha⟩)
      have e4 := Submodule.projectionOnto_apply_right hc ⟨ρ g b, T.apply_mem_toSubmodule g hb⟩
      simp only [LinearMap.comp_apply, map_add (f := _)]
      rw [e1, e2, e4, map_zero]
      exact congrArg (· + 0) e3⟩
  have hp : ∀ x : fixed ρ H, p x.1 = x := fun x => Submodule.projectionOnto_apply_left hc x
  obtain ⟨ψ, m, hm0, hm⟩ := GlobalTheory.exists_character_eigenvector_of_commute ℂ G _ σ.dual fun a b => by
    rw [← map_mul, hcomm, map_mul]
  have hm' : ∀ g x, m (σ g x) = ((ψ g)⁻¹ : ℂˣ) * m x := fun g x => by
    have := LinearMap.congr_fun (hm g⁻¹) x
    simpa [Representation.dual_apply, Module.Dual.transpose_apply] using this
  obtain ⟨x₀, hx₀⟩ : ∃ x, m x ≠ 0 := by
    by_contra h
    push_neg at h
    exact hm0 (LinearMap.ext fun x => by simpa using h x)
  refine ⟨ψ⁻¹, m ∘ₗ p.toLinearMap, fun h => hx₀ ?_, fun g v => ?_, fun h hh => ?_⟩
  · have := LinearMap.congr_fun h x₀.1
    simpa [hp] using this
  · show m (p (ρ g v)) = _
    rw [p.isIntertwining, hm']
    rfl
  · have h1 : σ h x₀ = x₀ := by
      apply Subtype.ext
      show ρ h x₀.1 = x₀.1
      simpa using x₀.2 ⟨h, hh⟩
    have h2 := hm' h x₀
    rw [h1] at h2
    have h3 : (((ψ h)⁻¹ : ℂˣ) : ℂ) = 1 := by
      have := mul_right_cancel₀ hx₀ (show (1 : ℂ) * m x₀ = (((ψ h)⁻¹ : ℂˣ) : ℂ) * m x₀ by rw [one_mul]; exact h2)
      exact this.symm
    exact Units.ext (by simpa using h3)

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem exists_eq_torusChar {n : ℕ} (μ : (Fin n → kˣ) →* ℂˣ) (hμ : ∀ t ∈ torusO k (Fin n), μ t = 1) :
    ∃ α : Fin n → ℂˣ, torusChar (fun i => unrChar k (α i)) = μ := by
  obtain ⟨ϖ, hϖ⟩ : ∃ ϖ : kˣ, valuation k (ϖ : k) = uniformizer k := by
    obtain ⟨c, hc⟩ := valuation_surjective (uniformizer k)
    refine ⟨Units.mk0 c fun h => ?_, hc⟩
    rw [h, map_zero] at hc
    exact IwahoriInj.unif_pos.ne hc
  let c : Fin n → kˣ →* ℂˣ := fun i => μ.comp (MonoidHom.mulSingle (fun _ => kˣ) i)
  have hc : ∀ i, IsUnram (c i) := fun i x hx => hμ _ fun j => by
    by_cases h : j = i
    · subst h; simpa using hx
    · simp [Pi.mulSingle_eq_of_ne h]
  refine ⟨fun i => c i ϖ, MonoidHom.ext fun t => ?_⟩
  rw [torusChar_apply]
  simp only [← GlobalTheory.SmGL.eq_unrChar (hc _) hϖ]
  conv_rhs => rw [← Finset.univ_prod_mulSingle t, map_prod]
  rfl

theorem isSubquotient_of_eigenform {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    {π : Representation ℂ (GL (Fin n) k) V} (hπ : IsSmooth π) (hirr : π.IsIrreducible)
    (μ : (Fin n → kˣ) →* ℂˣ) (l : Jacquet π (unipB k (Fin n)) →ₗ[ℂ] ℂ) (hl0 : l ≠ 0)
    (hl : ∀ t x, l (jacB π t x) = (μ t : ℂ) * l x) :
    IsSubquotient π (indB (ofChar μ)) := by
  let ρ : Representation ℂ (Levi k fun _ : Fin n => Unit) ℂ :=
    (ofChar μ).comp (leviTorus k (Fin n)).symm.toMonoidHom
  let φ : (GlobalTheory.SmGL.jac (points (Fin n)) π).IntertwiningMap ρ :=
    ⟨l, fun g => LinearMap.ext fun x => by
      obtain ⟨t, rfl⟩ := (leviTorus k (Fin n)).surjective g
      have e : (ρ (leviTorus k (Fin n) t)) (l x) = (μ t : ℂ) * l x := by
        show ofChar μ ((leviTorus k (Fin n)).symm (leviTorus k (Fin n) t)) _ = _
        rw [MulEquiv.symm_apply_apply, ofChar_apply]
      exact (hl t x).trans e.symm⟩
  obtain ⟨f, hf⟩ := (GlobalTheory.SmGL.Model.evalOne_bijective (points (Fin n)) hπ ρ).2 φ
  have hne : ∃ v, f v ≠ 0 := by
    by_contra h
    push_neg at h
    refine hl0 (LinearMap.ext fun x => ?_)
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    have h1 : φ (Submodule.Quotient.mk v) = (f v).1.1 1 := by rw [← hf]; rfl
    have h2 : l (Submodule.Quotient.mk v) = φ (Submodule.Quotient.mk v) := rfl
    rw [h2, h1, h v]
    rfl
  refine IsSubquotient.of_injective f ((injective_iff_map_eq_zero f.toLinearMap).2 ?_)
  let K : Subrepresentation π := ⟨LinearMap.ker f.toLinearMap, fun g v hv => by
    show f (π g v) = 0
    rw [f.isIntertwining]
    have : f v = 0 := hv
    rw [this, map_zero]⟩
  haveI := hirr
  rcases eq_bot_or_eq_top K with h | h
  · intro v hv
    have : v ∈ K.toSubmodule := hv
    rw [h] at this
    exact (Submodule.mem_bot ℂ).1 this
  · obtain ⟨v, hv⟩ := hne
    exact absurd (show v ∈ K.toSubmodule by rw [h]; trivial) hv

theorem exists_eigenform_jacBU {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    {π : Representation ℂ (GL (Fin n) k) V} (hadm : IsAdmissible π)
    (hI : fixed π (iwahori k (Fin n)) ≠ ⊥) :
    ∃ (χ : (Fin n → kˣ) →* ℂˣ) (l : Jacquet π (unipB k (Fin n)) →ₗ[ℂ] ℂ), l ≠ 0 ∧
      (∀ g v, l (jacBU π g v) = (χ g : ℂ) * l v) ∧ ∀ h ∈ torusO k (Fin n), χ h = 1 := by
  haveI := hadm.2 _ (SmGL.IwahoriOnto.isOpen_iwahori k (Fin n))
    (SmGL.IwahoriOnto.isCompact_iwahori k (Fin n))
  have hb := GlobalTheory.Published.BorelCasselman_holds k (Fin n) V π hadm
  haveI : FiniteDimensional ℂ (fixed (jacBU π) (torusO k (Fin n))) :=
    Module.Finite.of_surjective _ hb.2
  haveI : Nontrivial (fixed π (iwahori k (Fin n))) := Submodule.nontrivial_iff_ne_bot.2 hI
  haveI : Nontrivial (fixed (jacBU π) (torusO k (Fin n))) := hb.1.nontrivial
  exact exists_eigenform (isSmooth_jacBU hadm.1) (SmGL.UnramFixed.isCompact_torusO k (Fin n)) mul_comm
    fun _ => by rw [Subgroup.normalizer_eq_top]; trivial

theorem exists_isSubquotient_prinSeries {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    {π : Representation ℂ (GL (Fin n) k) V} (hadm : IsAdmissible π) (hirr : π.IsIrreducible)
    (hI : fixed π (iwahori k (Fin n)) ≠ ⊥) :
    ∃ α : Fin n → ℂˣ, IsSubquotient π (prinSeries fun i => unrChar k (α i)) := by
  obtain ⟨χ, l, hl0, hl, hχ⟩ := exists_eigenform_jacBU hadm hI
  let δ : (Fin n → kˣ) →* ℂˣ :=
    (deltaHalf k fun _ : Fin n => Unit).comp (leviTorus k (Fin n)).toMonoidHom
  obtain ⟨α, hα⟩ := exists_eq_torusChar (χ * δ⁻¹) fun t ht => by
    have : δ t = 1 := SmGL.UnramFixed.deltaHalf_torusO k ht
    simp [hχ t ht, this]
  refine ⟨α, ?_⟩
  have key := isSubquotient_of_eigenform hadm.1 hirr (χ * δ⁻¹) l hl0 fun t x => by
    rw [SmGL.UnramFixed.jacB_apply, map_smul, hl, smul_eq_mul, MonoidHom.mul_apply, Units.val_mul,
      MonoidHom.inv_apply]
    ring
  rw [← hα] at key
  exact key

theorem main : GlobalTheory.Published.BernsteinZelevinskyFiniteness → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (π : Irr k n), IsSpherical π.π → ∃ α : Fin n → ℂˣ, HasSatake π.π α := by
  intro hBZ k _ _ _ _ n π hs
  have hadm : IsAdmissible π.π := (hBZ k).1 (Fin n) π.V π.π π.smooth π.irr
  have hI : fixed π.π (iwahori k (Fin n)) ≠ ⊥ := by
    obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).1 hs
    refine (Submodule.ne_bot_iff _).2 ⟨v, fun h => ?_, hv0⟩
    exact hv ⟨h.1, iwahori_le_KO k _ h.2⟩
  obtain ⟨α, hα⟩ := exists_isSubquotient_prinSeries hadm π.irr hI
  exact ⟨α, π.irr, hs, hα⟩

end GlobalTheory.SatakeExists
end
end

section

noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric GlobalTheory.KerStd Classical
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.D (F1 F2 OwOK TrDual addC thetaInZ sumE)
open Formalism.InvariantFactorPaths.G7 (UnrOK IsLawOfLog cob)

namespace GlobalTheory.KerStd.StdHyp

open Formalism.DworkPowerSeriesWeights (BHyp NoLowBidegree degE degO letterLog mvExp de1 de2 Integral torus lw V2)
open Formalism.MainNotions.DIV.Bridge.LetterLogIntegrality (eV coeff_subst_scale lw_twist cobX_eq cobY_eq jetLog_rename coeff_subst_rename
  hasSubst_XeV letterLog_cc jetLogG_cc)

theorem kur_sub_wfrac (l : ℕ) [Fact l.Prime] : ∀ x ∈ MaximalUnramifiedExtension l, x ∈ product_zeroth_first_parts.Wfrac l := by
  have hS : {ζ : ℂ_[l] | ∃ n : ℕ, 0 < n ∧ ¬ l ∣ n ∧ ζ ^ n = 1} = product_zeroth_first_parts.rootsPrimeTo l := by
    ext ζ
    simp only [Set.mem_setOf_eq, product_zeroth_first_parts.rootsPrimeTo]
    refine exists_congr fun n => and_congr_right fun _ => and_congr_left fun _ => ?_
    rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd (Fact.out : l.Prime)]
  have halg : ∀ x ∈ product_zeroth_first_parts.rootsPrimeTo l, IsAlgebraic ℚ_[l] x := by
    rintro x ⟨n, hn, -, hx⟩
    exact (IsIntegral.of_pow hn (by rw [hx]; exact isIntegral_one)).isAlgebraic
  have hsub : (Subfield.closure (product_zeroth_first_parts.rootsPrimeTo l) : Set ℂ_[l]) ⊆ Algebra.adjoin ℚ_[l] (product_zeroth_first_parts.rootsPrimeTo l) := by
    intro x hx
    have h1 : Subfield.closure (product_zeroth_first_parts.rootsPrimeTo l) ≤
        (IntermediateField.adjoin ℚ_[l] (product_zeroth_first_parts.rootsPrimeTo l)).toSubfield :=
      Subfield.closure_le.mpr (IntermediateField.subset_adjoin _ _)
    have h2 := h1 hx
    rw [← IntermediateField.adjoin_toSubalgebra_of_isAlgebraic halg]
    exact h2
  intro x hx
  unfold MaximalUnramifiedExtension at hx
  rw [hS] at hx
  unfold product_zeroth_first_parts.Wfrac
  have hc : x ∈ closure (Subfield.closure (product_zeroth_first_parts.rootsPrimeTo l) : Set ℂ_[l]) := hx
  exact closure_mono hsub hc

theorem b3_of_noLowBidegree (l d : ℕ) [Fact l.Prime] [NeZero d] (be : MvPowerSeries (ZMod d) ℂ_[l])
    (h : NoLowBidegree be) : product_zeroth_first_parts.B3 l d be := by
  intro n hn
  obtain ⟨h1, h2, h3⟩ := h n hn
  have e1 : (product_zeroth_first_parts.bideg d n).1 = degE n := by
    unfold product_zeroth_first_parts.bideg degE
    simp only [Nat.even_iff]
    exact Finsupp.sum_fintype _ _ (by intro s; split_ifs <;> rfl)
  have e2 : (product_zeroth_first_parts.bideg d n).2 = degO n := by
    unfold product_zeroth_first_parts.bideg degO
    simp only [Nat.even_iff]
    exact Finsupp.sum_fintype _ _ (by intro s; split_ifs <;> rfl)
  refine ⟨by rw [e1]; exact h1.ne', by rw [e2]; exact h2.ne', ?_⟩
  intro hb
  apply h3
  have a := congrArg Prod.fst hb
  have b := congrArg Prod.snd hb
  exact ⟨e1 ▸ a, e2 ▸ b⟩

theorem b2_of_subst_torus_eq (l d : ℕ) [Fact l.Prime] [NeZero d] (ζ : ℂ_[l]) (hζ : IsPrimitiveRoot ζ (l ^ d - 1))
    (be : MvPowerSeries (ZMod d) ℂ_[l]) (h : MvPowerSeries.subst (torus l ζ) be = be) : product_zeroth_first_parts.B2 l d be := by
  intro u hu m
  haveI : NeZero (l ^ d - 1) := ⟨by
    have h1 := (Fact.out : l.Prime).one_lt
    have : 1 < l ^ d := Nat.one_lt_pow (NeZero.ne d) h1
    omega⟩
  obtain ⟨i, -, rfl⟩ := hζ.eq_pow_of_pow_eq_one hu
  have hm := congrArg (MvPowerSeries.coeff m) h
  have e : (torus l ζ : ZMod d → MvPowerSeries (ZMod d) ℂ_[l]) =
      fun s => MvPowerSeries.C (ζ ^ lw l s) * MvPowerSeries.X s := rfl
  rw [e, coeff_subst_scale] at hm
  by_cases hc : MvPowerSeries.coeff m be = 0
  · rw [hc, zero_mul]
  have hP : (m.prod fun s k => (ζ ^ lw l s) ^ k) = 1 :=
    mul_right_cancel₀ hc (by rw [one_mul]; exact hm)
  have hT : (m.prod fun s n => product_zeroth_first_parts.twist l d (ζ ^ i) s ^ n) = (m.prod fun s k => (ζ ^ lw l s) ^ k) ^ i := by
    unfold Finsupp.prod
    rw [← Finset.prod_pow]
    refine Finset.prod_congr rfl fun s _ => ?_
    show product_zeroth_first_parts.twist l d (ζ ^ i) s ^ m s = ((ζ ^ lw l s) ^ m s) ^ i
    rw [← lw_twist]
    simp only [← zpow_natCast, ← zpow_mul]
    congr 1
    ring
  rw [hT, hP, one_pow, mul_one]

theorem b4_of_coeff_subst_letterLog (l d : ℕ) [Fact l.Prime] [NeZero d] (D : MvPowerSeries (V2 d) ℂ_[l])
    (hD0 : MvPowerSeries.constantCoeff D = 0)
    (hW : ∀ n, MvPowerSeries.coeff n (MvPowerSeries.subst (letterLog (K := ℂ_[l]) l) (mvExp D)) ∈ product_zeroth_first_parts.Wint l)
    (h1 : MvPowerSeries.constantCoeff (MvPowerSeries.subst (letterLog (K := ℂ_[l]) l) (mvExp D)) = 1) :
    product_zeroth_first_parts.OverWOne l (MvPowerSeries.subst (Formalism.BasicNotions.jetLogG l d (β := Fin 2))
      (product_zeroth_first_parts.expS ℂ_[l] (MvPowerSeries.subst (fun u : Bool × ZMod d => (MvPowerSeries.X (eV d u) :
        MvPowerSeries (ZMod d × Fin 2) ℂ_[l])) D))) := by
  have hb := hasSubst_XeV l d
  have hbs : MvPowerSeries.HasSubst (fun w : ZMod d × Fin 2 => (MvPowerSeries.X ((eV d).symm w) :
      MvPowerSeries (V2 d) ℂ_[l])) := MvPowerSeries.hasSubst_of_constantCoeff_zero (fun w => by simp)
  have hJ : MvPowerSeries.HasSubst (Formalism.BasicNotions.jetLogG l d (β := Fin 2)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (jetLogG_cc l d)
  have hD : MvPowerSeries.HasSubst (fun _ : Unit => D) := MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ => hD0)
  have hLr : MvPowerSeries.HasSubst (fun v : ZMod d × Fin 2 => letterLog (K := ℂ_[l]) l ((eV d).symm v)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun v => letterLog_cc l d _)
  have hrn : (fun v : ZMod d × Fin 2 => MvPowerSeries.subst (fun w : ZMod d × Fin 2 => (MvPowerSeries.X ((eV d).symm w) :
      MvPowerSeries (V2 d) ℂ_[l])) (Formalism.BasicNotions.jetLogG l d (β := Fin 2) v)) =
      fun v => letterLog (K := ℂ_[l]) l ((eV d).symm v) := by
    funext v
    have := jetLog_rename l d ((eV d).symm v)
    rwa [Equiv.apply_symm_apply] at this
  have hexp : product_zeroth_first_parts.expS ℂ_[l] (MvPowerSeries.subst (fun u : Bool × ZMod d => (MvPowerSeries.X (eV d u) :
        MvPowerSeries (ZMod d × Fin 2) ℂ_[l])) D) =
      MvPowerSeries.subst (fun u : Bool × ZMod d => (MvPowerSeries.X (eV d u) :
        MvPowerSeries (ZMod d × Fin 2) ℂ_[l])) (mvExp D) := by
    unfold product_zeroth_first_parts.expS mvExp PowerSeries.subst
    rw [MvPowerSeries.subst_comp_subst_apply hD hb]
  have key : MvPowerSeries.subst (fun w : ZMod d × Fin 2 => (MvPowerSeries.X ((eV d).symm w) :
      MvPowerSeries (V2 d) ℂ_[l])) (MvPowerSeries.subst (Formalism.BasicNotions.jetLogG l d (β := Fin 2))
        (product_zeroth_first_parts.expS ℂ_[l] (MvPowerSeries.subst (fun u : Bool × ZMod d => (MvPowerSeries.X (eV d u) :
          MvPowerSeries (ZMod d × Fin 2) ℂ_[l])) D))) =
      MvPowerSeries.subst (letterLog (K := ℂ_[l]) l) (mvExp D) := by
    rw [hexp, MvPowerSeries.subst_comp_subst_apply hJ hbs, hrn, MvPowerSeries.subst_comp_subst_apply hb hLr]
    congr 1
    funext u
    rw [MvPowerSeries.subst_X hLr, Equiv.symm_apply_apply]
  refine ⟨fun n => ?_, ?_⟩
  · have := hW (Finsupp.equivMapDomain (eV d).symm n)
    rw [← key, coeff_subst_rename, Equiv.symm_symm, ← Finsupp.equivMapDomain_trans] at this
    simpa using this
  · have e := congrArg (MvPowerSeries.coeff 0) key
    rw [coeff_subst_rename, Finsupp.equivMapDomain_zero, MvPowerSeries.coeff_zero_eq_constantCoeff_apply,
      MvPowerSeries.coeff_zero_eq_constantCoeff_apply] at e
    rw [e, h1]

end GlobalTheory.KerStd.StdHyp

namespace GlobalTheory.KerStd

open Formalism.DworkPowerSeriesWeights (NoLowBidegree)
open Formalism.DworkPowerSeriesWeights.Transfer (map_defectOne map_defectTwo map_logExp constantCoeff_defectOne constantCoeff_defectTwo cc_of_noLow map_torus cc_torus)

theorem bHyps_of_beStd : ∀ (l d : ℕ) [Fact l.Prime] [NeZero d] (be : MvPowerSeries (ZMod d) ℂ_[l]), 5 ≤ l → 2 ≤ d →
    Even d → BeStd l d be → product_zeroth_first_parts.B1 l d be ∧ product_zeroth_first_parts.B2 l d be ∧ product_zeroth_first_parts.B3 l d be ∧ product_zeroth_first_parts.B4 l d be := by
  intro l d _ _ be _ hd2 hde hstd
  obtain ⟨σ, F, be0, om, oms, ζ, ⟨hσ, hF, hF1, -, hO, -, hζ⟩, rfl⟩ := hstd
  obtain ⟨-, h2, h3, ⟨h4, h4'⟩, ⟨h5, h5'⟩⟩ := Formalism.L2.Th1.D.biextension_hypotheses_of_level_one (MaximalUnramifiedExtension l) l d σ hσ hd2 hde F hF be0 hF1
    (Fin (d / 2)) om oms hO ζ hζ
  have hbe : beOf l d σ be0 om oms ζ =
      MvPowerSeries.map (MaximalUnramifiedExtension l).subtype (Formalism.L2.Th1.D.beMean (d := d) l σ be0 om oms ζ) := rfl
  rw [hbe]
  have hc := cc_of_noLow h3
  have hc' : MvPowerSeries.constantCoeff
      (MvPowerSeries.map (MaximalUnramifiedExtension l).subtype (Formalism.L2.Th1.D.beMean (d := d) l σ be0 om oms ζ)) = 0 := by
    rw [MvPowerSeries.constantCoeff_map, hc, map_zero]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro m
    rw [MvPowerSeries.coeff_map]
    exact StdHyp.kur_sub_wfrac l _ (SetLike.coe_mem _)
  · have ht := congrArg (MvPowerSeries.map (MaximalUnramifiedExtension l).subtype) h2
    rw [MvPowerSeries.map_subst (MvPowerSeries.hasSubst_of_constantCoeff_zero (cc_torus l ζ))] at ht
    simp only [map_torus] at ht
    exact StdHyp.b2_of_subst_torus_eq l d _ (hζ.map_of_injective (MaximalUnramifiedExtension l).subtype.injective) _ ht
  · apply StdHyp.b3_of_noLowBidegree
    intro n hn
    refine h3 n ?_
    intro h0
    rw [MvPowerSeries.coeff_map, h0, map_zero] at hn
    exact hn rfl
  · unfold product_zeroth_first_parts.B4
    rw [Formalism.MainNotions.DIV.Bridge.LetterLogIntegrality.cobX_eq, Formalism.MainNotions.DIV.Bridge.LetterLogIntegrality.cobY_eq]
    constructor
    · refine StdHyp.b4_of_coeff_subst_letterLog l d _ (constantCoeff_defectOne hc') (fun n => ?_) ?_
      · rw [← map_defectOne, ← map_logExp _ l (constantCoeff_defectOne hc), MvPowerSeries.coeff_map]
        exact ⟨StdHyp.kur_sub_wfrac l _ (SetLike.coe_mem _), h4 n⟩
      · rw [← map_defectOne, ← map_logExp _ l (constantCoeff_defectOne hc), MvPowerSeries.constantCoeff_map, h4', map_one]
    · refine StdHyp.b4_of_coeff_subst_letterLog l d _ (constantCoeff_defectTwo hc') (fun n => ?_) ?_
      · rw [← map_defectTwo, ← map_logExp _ l (constantCoeff_defectTwo hc), MvPowerSeries.coeff_map]
        exact ⟨StdHyp.kur_sub_wfrac l _ (SetLike.coe_mem _), h5 n⟩
      · rw [← map_defectTwo, ← map_logExp _ l (constantCoeff_defectTwo hc), MvPowerSeries.constantCoeff_map, h5', map_one]

end GlobalTheory.KerStd
end
end

section

open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.LocGL.LenOneSupport

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem eq_of_isCosocle_prodIrr_one (ρ x : IrrGL (k := k)) (y : Fin 1 → IrrGL (k := k)) (hy : ∀ a, y a = ρ)
    (hd : ∑ a, (y a).1 = x.1) (h : IsCosocle x.rep (prodIrr y hd)) : x = ρ := by
  have e : y = fun _ => ρ := funext hy
  subst e
  obtain ⟨n, c⟩ := x
  obtain ⟨m, r⟩ := ρ
  have hmn : m = n := by simpa using hd
  subst hmn
  obtain ⟨ψ⟩ := nonempty_equiv_prodIrr_one (⟨m, r⟩ : IrrGL (k := k)) hd
  have h2 := h.of_equiv (.refl _) ψ.symm
  obtain ⟨φ⟩ := (isCosocle_self r.rep.irr).unique h2
  have e1 := (IrrGL.of_eq_of (hs := c.rep.smooth) (hi := c.rep.irr) (hs' := r.rep.smooth) (hi' := r.rep.irr)).2 ⟨φ⟩
  exact (IrrGL.of_rep (⟨m, c⟩ : IrrGL (k := k))).symm.trans (e1.trans (IrrGL.of_rep (⟨m, r⟩ : IrrGL (k := k))))

theorem eq_first_of_isLSeg {Δ : Segment k} (hl : Δ.len = 1) {x : IrrGL (k := k)} (h : IsLSeg Δ x.rep) : x = Δ.first := by
  have e : Δ = Segment.single Δ.first Δ.isCusp_first := Segment.ext_first rfl hl
  rw [e] at h
  obtain ⟨hd, hc⟩ := h
  refine eq_of_isCosocle_prodIrr_one Δ.first x _ (fun a => ?_) hd hc
  rw [Fin.fin_one_eq_zero a]
  simp [Segment.term, Segment.single, Segment.ofFirst]
  rfl

theorem hasSupport_first_of_isL_len_one : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (c : ℕ) (Δ : Fin c → Segment k) (x : IrrGL (k := k)), (∀ i, (Δ i).len = 1) →
    IsL ((List.ofFn Δ : List (Segment k)) : Multiset (Segment k)) x.rep →
    HasSupport x.rep (Finset.univ.val.map fun i => (Δ i).first) := by
  intro k _ _ _ _ c Δ x hl hL
  obtain ⟨h, y, hd, ⟨Δ', ⟨hmap, -⟩, hy⟩, hcos⟩ := hL
  have hl' : ∀ i, (Δ' i).len = 1 := fun i => by
    have hm : Δ' i ∈ ((List.ofFn Δ : List (Segment k)) : Multiset (Segment k)) :=
      hmap ▸ Multiset.mem_map_of_mem _ (Finset.mem_univ_val i)
    obtain ⟨j, hj⟩ := List.mem_ofFn.1 (Multiset.mem_coe.1 hm)
    rw [← hj]; exact hl j
  have hyf : y = fun i => (Δ' i).first := funext fun i => eq_first_of_isLSeg (hl' i) (hy i)
  subst hyf
  have hs := hasSupport_of_isSubquotient hcos.1 (fun i => (Δ' i).isCusp_first) hcos.isSubquotient
  have e : (Finset.univ.val.map fun i => (Δ' i).first) = Finset.univ.val.map fun i => (Δ i).first := by
    have e2 : (Finset.univ.val.map Δ : Multiset (Segment k)) = ((List.ofFn Δ : List (Segment k)) : Multiset (Segment k)) := by
      rw [← Fin.univ_val_map]
    have m1 := Multiset.map_map Segment.first Δ' Finset.univ.val
    have m2 := Multiset.map_map Segment.first Δ Finset.univ.val
    simp only [Function.comp_def] at m1 m2
    rw [← m1, ← m2, hmap, e2]
  rw [e] at hs
  exact hs

end GlobalTheory.LocGL.LenOneSupport
end
end

section

open Formalism.L2.Col

namespace GlobalTheory.TopLaw

theorem blkDet_eq_dB : ∀ {κ : Type} [CommRing κ] {n : ℕ} (β : ℕ → ℕ) (c s t : ℕ), s + t ≤ n → (∀ i, i < n → (β i = c ↔ s ≤ i ∧ i < s + t)) → ∀ (M : btG n κ β) (A : ℕ → ℕ → κ), (∀ i j : Fin n, A i.1 j.1 = (M.1 : Matrix (Fin n) (Fin n) κ) i j) → ((blkDet n κ β c M : κˣ) : κ) = GlobalTheory.DatumLaw.dB A s t := by
  intro κ _ n β c s t hn hβ M A hA
  rw [blkDet_val]
  unfold GlobalTheory.DatumLaw.dB
  let e : Fin t ≃ {i : Fin n // β i.1 = c} :=
    { toFun := fun u => ⟨⟨s + u.1, by have := u.2; omega⟩, (hβ _ (by have := u.2; omega)).2 ⟨by simp, by have := u.2; simp⟩⟩
      invFun := fun i => ⟨i.1.1 - s, by have := (hβ _ i.1.2).1 i.2; omega⟩
      left_inv := fun u => Fin.ext (by simp)
      right_inv := fun i => Subtype.ext (Fin.ext (by have := (hβ _ i.1.2).1 i.2; simp only; omega)) }
  rw [← Matrix.det_submatrix_equiv_self e]
  congr 1
  ext u v
  exact (hA (e u).1 (e v).1).symm

end GlobalTheory.TopLaw
end
