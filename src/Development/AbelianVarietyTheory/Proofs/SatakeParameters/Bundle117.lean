module

import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SmulMemOfOne
public import Mathlib.NumberTheory.NumberField.Basic
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle011
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsNotCongPow
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FiniteDimensionalWdSpace
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MonodromyZeroOfWeilDeligneRepClassIff
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle112
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle013
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle010
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle111
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle081
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle009
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle075
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle069
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle070
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle089
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle102
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle110
import Formalism.LocalToGlobal.Columns.StdLatUnimodular
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle111
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle096
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.BadPrimesPeriodBound
import Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.Bundle004
import Formalism.LocalToGlobal.Columns.AlgebraMapMemMaximalIdealPowIff
import Formalism.LocalToGlobal.Divisibility.CoefMod
import Formalism.LocalToGlobal.KernelLattices.XiIndCClass
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
import ReciprocityTheory.GaloisValuations.GlobalB
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle013
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasExponentZeroIff
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.TrivialOnInertiaOfUnr
import Development.AutomorphicArithmetic.IntegralCasts.Bundle001
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import ReciprocityTheory.NeutralLocalFields.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle001

@[expose] public section

section

noncomputable section

namespace GlobalTheory.ColPeriodCompare

open NumberField IsDedekindDomain

section Lattices

variable {K : Type} [Field K] [NumberField K] {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

theorem exists_proj (L : Submodule (𝓞 K) V) (hfg : L.FG) (hsp : Submodule.span K (L : Set V) = ⊤) (W : Submodule K V) :
    ∃ P : V →ₗ[K] V, (∀ v, P v ∈ W) ∧ (∀ w ∈ W, P w = w) ∧ ∀ v ∈ L, P v ∈ L := by
  apply GlobalTheory.DegAsm.FrameMove.exists_proj <;> assumption

end Lattices


open Classical in
theorem deg_eq {ι : Type} {a b : ℕ} (e : ι × Fin b × Fin a →₀ ℕ) (τ : ι) :
    ((∑ k ∈ e.support.filter (fun k => k.1 = τ), e k : ℕ) : ℤ) = ∑ β, ∑ α, (e (τ, β, α) : ℤ) := by
  rw [← Finset.sum_product', Finset.univ_product_univ, Nat.cast_sum]
  rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.filter fun y : Fin b × Fin a => (τ, y) ∈ e.support))]
  · refine Finset.sum_bij (fun k _ => k.2) ?_ ?_ ?_ ?_
    · intro k hk
      obtain ⟨h1, rfl⟩ := Finset.mem_filter.1 hk
      exact Finset.mem_filter.2 ⟨Finset.mem_univ _, h1⟩
    · intro k hk k' hk' h
      exact Prod.ext ((Finset.mem_filter.1 hk).2.trans (Finset.mem_filter.1 hk').2.symm) h
    · intro y hy
      exact ⟨(τ, y), Finset.mem_filter.2 ⟨(Finset.mem_filter.1 hy).2, rfl⟩, rfl⟩
    · intro k hk
      obtain ⟨-, rfl⟩ := Finset.mem_filter.1 hk
      rfl
  · intro y _ hy
    have : (τ, y) ∉ e.support := fun h => hy (Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩)
    rw [show (τ, y.1, y.2) = (τ, y) from rfl, Finsupp.notMem_support_iff.1 this, Nat.cast_zero]

end GlobalTheory.ColPeriodCompare
end
end

section

noncomputable section

namespace GlobalTheory.ColPeriod

open NumberField IsDedekindDomain Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Ker
open GlobalTheory.IndefiniteRowSideFullHecke.BadPrimesPeriodBound (recSeam HostTie AnTie)
open GlobalTheory.IndefiniteRowSideFullHecke.SubstitutionAdjoint (WtCompat InDeg LatWithBasis)

def JetOpWeyl : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) (ι : Type) [Fintype ι] (a b : ℕ) (hab : a < b)
    (lam : ι → DomWeight a) (lam' : ι → DomWeight b) (s s' : ι → ℤ) (n : ι → ℕ), WtCompat hab lam lam' s s' n →
    ∀ (M : ι → Submodule (𝓞 K) (Fin a → K)) (MW : ι → Submodule (𝓞 K) (Fin b → K)),
      (∀ τ, Submodule.IsLattice K (M τ)) → (∀ τ, Submodule.IsLattice K (MW τ)) → LatWithBasis w M 1 → LatWithBasis w MW 1 →
      ∀ (c : K) (J : (DVar ι a b →₀ ℕ) → K), (∀ m, InDeg lam s' m → w.valuation K (c * J m) ≤ 1) →
        ∀ F ∈ localization₂ w.asIdeal (delK lam fun τ => dualFr (M τ)),
          c • jetOp lam lam' J n F ∈ localization₂ w.asIdeal (delK lam' fun τ => dualFr (MW τ))

end GlobalTheory.ColPeriod
end
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.AboveL

namespace GlobalTheory.AboveL.WeilUp

variable {K L Ω : Type} [Field Ω] [Field K] [NumberField K] [Algebra K Ω] [Field L] [NumberField L] [Algebra L Ω]
  [Algebra K L] [IsScalarTower K L Ω] {A : ValuationSubring Ω}

theorem modEq_of_cong {v' : HeightOneSpectrum (𝓞 L)} (h' : Formalism.ConjugateSelfDual.IsPlaceOver A v') {Q a b : ℕ}
    (hc : ∀ ζ : 𝓞 L, A.valuation ((algebraMap L Ω (ζ : L)) ^ (Q ^ b) - (algebraMap L Ω (ζ : L)) ^ (Q ^ a)) < 1) :
    Q ^ a ≡ Q ^ b [MOD Formalism.ConjugateSelfDual.normV v' - 1] := by
  haveI := v'.isMaximal
  letI : Field (𝓞 L ⧸ v'.asIdeal) := Ideal.Quotient.field _
  haveI : Finite (𝓞 L ⧸ v'.asIdeal) := v'.asIdeal.finiteQuotientOfFreeOfNeBot v'.ne_bot
  obtain ⟨u, hu⟩ := IsCyclic.exists_generator (α := (𝓞 L ⧸ v'.asIdeal)ˣ)
  have hord : orderOf u = Formalism.ConjugateSelfDual.normV v' - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hu, Nat.card_units]; rfl
  rw [← hord, ← pow_eq_pow_iff_modEq]
  obtain ⟨ζ, hζ⟩ := Ideal.Quotient.mk_surjective (u : 𝓞 L ⧸ v'.asIdeal)
  have hmem : ζ ^ (Q ^ b) - ζ ^ (Q ^ a) ∈ v'.asIdeal := by
    rw [← h']
    have e : algebraMap L Ω (((ζ ^ (Q ^ b) - ζ ^ (Q ^ a) : 𝓞 L)) : L) =
        (algebraMap L Ω (ζ : L)) ^ (Q ^ b) - (algebraMap L Ω (ζ : L)) ^ (Q ^ a) := by
      push_cast; simp [map_sub, map_pow]
    rw [e]; exact hc ζ
  have h0 := (Ideal.Quotient.eq_zero_iff_mem).mpr hmem
  rw [map_sub, map_pow, map_pow, hζ, sub_eq_zero] at h0
  apply Units.ext
  simp only [Units.val_pow_eq_pow_val]
  exact h0.symm

theorem dvd_of_modEq {q f n : ℕ} (hq : 1 < q) (h : q ^ n ≡ 1 [MOD q ^ f - 1]) : f ∣ n := by
  have h1 : 1 ≤ q ^ n := Nat.one_le_pow _ _ (by omega)
  have hd : q ^ f - 1 ∣ q ^ n - 1 := (Nat.modEq_iff_dvd' h1).mp h.symm
  have hg := Nat.pow_sub_one_gcd_pow_sub_one q f n
  rw [Nat.gcd_eq_left hd] at hg
  have h2 : 1 ≤ q ^ f := Nat.one_le_pow _ _ (by omega)
  have h3 : 1 ≤ q ^ (f.gcd n) := Nat.one_le_pow _ _ (by omega)
  have h4 : q ^ f = q ^ (f.gcd n) := by omega
  have h5 := Nat.pow_right_injective (Nat.succ_le_of_lt hq) h4
  rw [h5]; exact Nat.gcd_dvd_right f n

theorem actsAs_of_agree {q f a b : ℕ} {σ : Formalism.ConjugateSelfDual.G K Ω} {g : Formalism.ConjugateSelfDual.G L Ω} (hg : ∀ z : Ω, σ z = g z)
    (hσ : ActsAs A q σ (f * a) (f * b)) : ActsAs A (q ^ f) g a b := by
  have e : σ = (g.restrictScalars K : Formalism.ConjugateSelfDual.G K Ω) := AlgEquiv.ext hg
  subst e
  refine ⟨hσ.1, fun x hx => ?_⟩
  have := hσ.2 x hx
  rw [pow_mul, pow_mul] at this
  exact this

end GlobalTheory.AboveL.WeilUp

namespace GlobalTheory.AboveL


open GlobalTheory.AboveL.WeilUp in
theorem mem_weil_of_fix : ∀ (K L Ω : Type) [Field Ω] [Field K] [NumberField K] [Algebra K Ω] [IsAlgClosure K Ω] [Field L] [NumberField L] [Algebra L Ω] [IsAlgClosure L Ω] [Algebra K L] [IsScalarTower K L Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 K)) (v' : HeightOneSpectrum (𝓞 L)) (h : Formalism.ConjugateSelfDual.IsPlaceOver A v) (h' : Formalism.ConjugateSelfDual.IsPlaceOver A v') (σ : Weil h) (g : Formalism.ConjugateSelfDual.G L Ω), (∀ z : Ω, (σ : Formalism.ConjugateSelfDual.G K Ω) z = g z) → g ∈ Weil h' := by
  intro K L Ω _ _ _ _ _ _ _ _ _ _ _ A v v' h h' σ g hg
  obtain ⟨f, hf⟩ := normV_eq_pow v v' (comap_eq_of_placeOver h h')
  have hq : 1 < Formalism.ConjugateSelfDual.normV v := one_lt_normV v

  have hcong : ∀ a b : ℕ, ActsAs A (Formalism.ConjugateSelfDual.normV v) (σ : Formalism.ConjugateSelfDual.G K Ω) a b →
      Formalism.ConjugateSelfDual.normV v ^ a ≡ Formalism.ConjugateSelfDual.normV v ^ b [MOD Formalism.ConjugateSelfDual.normV v ^ f - 1] := by
    intro a b hab
    rw [← hf]
    refine modEq_of_cong h' fun ζ => ?_
    have hfix : (σ : Formalism.ConjugateSelfDual.G K Ω) (algebraMap L Ω (ζ : L)) = algebraMap L Ω (ζ : L) := by
      rw [hg]; exact g.commutes _
    have hint : A.valuation (algebraMap L Ω (ζ : L)) ≤ 1 := by
      rw [A.valuation_le_one_iff]
      exact mem_of_isIntegral_int A (ζ.2.algebraMap)
    have := hab.2 _ hint
    rwa [hfix] at this
  set d := deg σ with hd
  rcases le_total 0 d with hd0 | hd0
  · obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le hd0
    have hact := actsAs_of_deg (σ := σ) (a := n) (b := 0) (by rw [← hd, hn]; simp)
    have hdiv : f ∣ n := dvd_of_modEq hq (by simpa using hcong _ _ hact)
    obtain ⟨k, rfl⟩ := hdiv
    have hact' := actsAs_of_deg (σ := σ) (a := f * k) (b := f * 0) (by rw [← hd, hn]; simp)
    exact (mem_Weil h').mpr ⟨k, 0, hf ▸ actsAs_of_agree hg hact'⟩
  · obtain ⟨n, hn⟩ := Int.exists_eq_neg_ofNat hd0
    have hact := actsAs_of_deg (σ := σ) (a := 0) (b := n) (by rw [← hd, hn]; simp)
    have hdiv : f ∣ n := dvd_of_modEq hq (by simpa using (hcong _ _ hact).symm)
    obtain ⟨k, rfl⟩ := hdiv
    have hact' := actsAs_of_deg (σ := σ) (a := f * 0) (b := f * k) (by rw [← hd, hn]; simp)
    exact (mem_Weil h').mpr ⟨0, k, hf ▸ actsAs_of_agree hg hact'⟩

end GlobalTheory.AboveL
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.AboveL

theorem _root_.GlobalTheory.T.exists_weilGroup_restrict_extension : ∀ (K L Ω : Type) [Field Ω] [Field K] [NumberField K] [Algebra K Ω] [IsAlgClosure K Ω] [Field L] [NumberField L] [Algebra L Ω] [IsAlgClosure L Ω] [Algebra K L] [IsScalarTower K L Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 K)) (v' : HeightOneSpectrum (𝓞 L)) (h : Formalism.ConjugateSelfDual.IsPlaceOver A v) (h' : Formalism.ConjugateSelfDual.IsPlaceOver A v') (σ' : Weil h'), ∃ σ : Weil h, (∀ z : Ω, (σ : Formalism.ConjugateSelfDual.G K Ω) z = (σ' : Formalism.ConjugateSelfDual.G L Ω) z) ∧ (deg σ = 0 ↔ deg σ' = 0) := by
  first | exact @GlobalTheory.AboveL.exists_weil_restrict | exact GlobalTheory.AboveL.exists_weil_restrict | (intros; apply GlobalTheory.AboveL.exists_weil_restrict <;> assumption)
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.AboveL

theorem _root_.GlobalTheory.T.fontaineWeilDeligneSpace_restriction_equiv : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (ι : Qbar l ≃+* ℂ) (K L Ω : Type) [Field Ω] [Field K] [NumberField K] [Algebra K Ω] [IsAlgClosure K Ω] [Field L] [NumberField L] [Algebra L Ω] [IsAlgClosure L Ω] [Algebra K L] [IsScalarTower K L Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 K)) (v' : HeightOneSpectrum (𝓞 L)) (h : Formalism.ConjugateSelfDual.IsPlaceOver A v) (h' : Formalism.ConjugateSelfDual.IsPlaceOver A v') (O O' : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] [CommRing O'] [Algebra ℤ_[l] O'] [TopologicalSpace O'] (Bw : LocBridge l K Ω (ReciprocityTheory.Gal.Dec (F := K) A) O) (Bw' : LocBridge l L Ω (ReciprocityTheory.Gal.Dec (F := L) A) O') (hj : GlobalTheory.Pst.Induces Bw) (hj' : GlobalTheory.Pst.Induces Bw') (hle : Bw.Kw.1 ≤ Bw'.Kw.1), (∀ (σ : Weil h) (σ' : Weil h'), (∀ z : Ω, (σ : Formalism.ConjugateSelfDual.G K Ω) z = (σ' : Formalism.ConjugateSelfDual.G L Ω) z) → (weilToGK Bw' h' σ' : GQ l) = (weilToGK Bw h σ : GQ l)) → ∀ (LL : FinExt l) (V : Type) [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V] [FiniteDimensional ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK Bw.Kw) V) [FiniteDimensional ↥(MaximalUnramifiedExtension l) (DpstUr P ρ)] [FiniteDimensional ↥(MaximalUnramifiedExtension l) (DpstUr P (GlobalTheory.Pst.resTo ρ hle))], IsPst P ρ → ∃ e : WDSpace P ι ρ ≃ₗ[ℂ] WDSpace P ι (GlobalTheory.Pst.resTo ρ hle), (∀ (σ : Weil h) (σ' : Weil h'), (∀ z : Ω, (σ : Formalism.ConjugateSelfDual.G K Ω) z = (σ' : Formalism.ConjugateSelfDual.G L Ω) z) → ∀ x, e (wdRho P ι Bw h hj ρ σ x) = wdRho P ι Bw' h' hj' (GlobalTheory.Pst.resTo ρ hle) σ' (e x)) ∧ ∀ x, e (wdN P ι ρ x) = wdN P ι (GlobalTheory.Pst.resTo ρ hle) (e x) := by
  first | exact @GlobalTheory.Pst.ResLetter.wdSpace_resTo_equiv | exact GlobalTheory.Pst.ResLetter.wdSpace_resTo_equiv | (intros; apply GlobalTheory.Pst.ResLetter.wdSpace_resTo_equiv <;> assumption)
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.AboveL

theorem _root_.GlobalTheory.T.weilRep_equiv_of_charpoly_eq : ∀ (K Ω : Type) [Field Ω] [Field K] [NumberField K] [Algebra K Ω] [IsAlgClosure K Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 K)) (h : Formalism.ConjugateSelfDual.IsPlaceOver A v) (n m : ℕ) (a : WDRep h (Fin n → ℂ)) (b : WDRep h (Fin m → ℂ)), (∀ σ : Weil h, (a.ρ σ).charpoly = (b.ρ σ).charpoly) → ∃ e : (Fin n → ℂ) ≃ₗ[ℂ] (Fin m → ℂ), ∀ σ z, e (a.ρ σ z) = b.ρ σ (e z) := by
  first | exact @GlobalTheory.AboveL.weil_rep_equiv_of_charpoly_eq | exact GlobalTheory.AboveL.weil_rep_equiv_of_charpoly_eq | (intros; apply GlobalTheory.AboveL.weil_rep_equiv_of_charpoly_eq <;> assumption)
end

section

noncomputable section

open CategoryTheory Limits AlgebraicGeometry Opposite Matrix

namespace GlobalTheory.Et.Rel

variable {X Y : Scheme.{0}} {E : Type} [CommRing E] [TopologicalSpace E] [IsTopologicalRing E]
  {ι : Type} [Fintype ι] [DecidableEq ι] {Γ : Type} [Group Γ]

section
variable (f : X ⟶ Y)

end

variable (E) (f : X ⟶ Y) (Q' : RActPre X Γ) (Q : RActPre Y Γ) (ξ : Γ →* GL ι E)
  (e : ∀ T : Over X, Q'.P.obj (op T) ≃ Q.P.obj (op ((Over.map f).obj T)))
  (he : ∀ {T₁ T₂ : Over X} (v : T₁ ⟶ T₂) (η : Q'.P.obj (op T₂)),
    e T₁ (Q'.P.map v.op η) = Q.P.map ((Over.map f).map v).op (e T₂ η))
  (hq : ∀ (T : Over X) (γ : Γ) (η : Q'.P.obj (op T)), e T ((Q'.act γ).app (op T) η) = (Q.act γ).app _ (e T η))

end GlobalTheory.Et.Rel

namespace GlobalTheory.Et.Rel

variable {X Y : Scheme.{0}} {E : Type} [CommRing E] [TopologicalSpace E] [IsTopologicalRing E]
  {ι : Type} [Fintype ι] [DecidableEq ι] {Γ : Type} [Group Γ]
variable (E) (f : X ⟶ Y) (Q' : RActPre X Γ) (Q : RActPre Y Γ) (ξ : Γ →* GL ι E)
  (e : ∀ T : Over X, Q'.P.obj (op T) ≃ Q.P.obj (op ((Over.map f).obj T)))
  (he : ∀ {T₁ T₂ : Over X} (v : T₁ ⟶ T₂) (η : Q'.P.obj (op T₂)),
    e T₁ (Q'.P.map v.op η) = Q.P.map ((Over.map f).map v).op (e T₂ η))
  (hq : ∀ (T : Over X) (γ : Γ) (η : Q'.P.obj (op T)), e T ((Q'.act γ).app (op T) η) = (Q.act γ).app _ (e T η))

end GlobalTheory.Et.Rel

namespace GlobalTheory.Et.Rel

variable {X Y : Scheme.{0}} {E : Type} [CommRing E] [TopologicalSpace E] [IsTopologicalRing E]
  {ι : Type} [Fintype ι] [DecidableEq ι] {Γ : Type} [Group Γ]
variable (E) (f : X ⟶ Y) (Q' : RActPre X Γ) (Q : RActPre Y Γ) (ξ : Γ →* GL ι E)
  (e : ∀ T : Over X, Q'.P.obj (op T) ≃ Q.P.obj (op ((Over.map f).obj T)))
  (he : ∀ {T₁ T₂ : Over X} (v : T₁ ⟶ T₂) (η : Q'.P.obj (op T₂)),
    e T₁ (Q'.P.map v.op η) = Q.P.map ((Over.map f).map v).op (e T₂ η))
  (hq : ∀ (T : Over X) (γ : Γ) (η : Q'.P.obj (op T)), e T ((Q'.act γ).app (op T) η) = (Q.act γ).app _ (e T η))

end GlobalTheory.Et.Rel

namespace GlobalTheory.UPel.HT

open CategoryTheory Limits AlgebraicGeometry Opposite Matrix MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ}
  {S S' : Scheme.{0}} {s : S ⟶ Sp R} {s' : S' ⟶ Sp R} {o' : Obj b N s'} {o : Obj b N s} {f : S' ⟶ S}

def ObjMap.ptEquiv (m : ObjMap o' o f) (T : Over S') : (T ⟶ o'.A) ≃* ((Over.map f).obj T ⟶ o.A) :=
  MulEquiv.ofBijective (pushHom m.cart T) ⟨GlobalTheory.SiegelPull.push_injective m.cart T, GlobalTheory.SiegelPull.push_surjective m.cart T⟩

theorem ObjMap.ptEquiv_left (m : ObjMap o' o f) (T : Over S') (x : T ⟶ o'.A) :
    (m.ptEquiv T x).left = x.left ≫ m.φ := rfl

theorem ObjMap.ptEquiv_act (m : ObjMap o' o f) (T : Over S') (x : T ⟶ o'.A) (c : D.O) :
    m.ptEquiv T (x ≫ o'.act.act c) = m.ptEquiv T x ≫ o.act.act c :=
  Over.OverMorphism.ext (by
    rw [ObjMap.ptEquiv_left, Over.comp_left, Over.comp_left, ObjMap.ptEquiv_left, Category.assoc, m.act,
      Category.assoc])

theorem ObjMap.exists_ptEquiv (m : ObjMap o' o f) (Z : Over S) (g : Z.left ⟶ S') (hg : g ≫ f = Z.hom) :
    ∃ σ : (Over.mk g ⟶ o'.A) ≃* (Z ⟶ o.A), (∀ x, (σ x).left = x.left ≫ m.φ) ∧
      ∀ (n : ℤ) (a c : Over.mk g ⟶ o'.A) (z : Γ(Z.left, ⊤)ˣ),
        (Out.WeilIs o'.A (o'.P.pull (lift (𝟙 o'.A) (𝟙 o'.A)).left) n a c z ↔
          Out.WeilIs o.A (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left) n (σ a) (σ c) z) := by
  obtain ⟨Zl, Zr, Zh⟩ := Z
  change Zl ⟶ S' at g
  change g ≫ f = Zh at hg
  subst hg
  refine ⟨m.ptEquiv (Over.mk g), fun x => rfl, fun n a c z => ?_⟩
  exact GlobalTheory.weilIs_iff_of_isGrpPullback_comm _ _ o.A o'.A f m.φ _ _ (pull_isLB o.isLB _) (pull_isLB o'.isLB _)
    m.cart (GlobalTheory.SiegelPull.diag_iso m.sq m.pol) (Over.mk g) n a c _ _ z rfl rfl

end GlobalTheory.UPel.HT

namespace GlobalTheory.UPel.HT

open CategoryTheory Limits AlgebraicGeometry Opposite Matrix MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ}
  {S S' : Scheme.{0}} {s : S ⟶ Sp R} {s' : S' ⟶ Sp R} {o' : Obj b N s'} {o : Obj b N s} {f : S' ⟶ S}

end GlobalTheory.UPel.HT

namespace GlobalTheory.UPel.HT

open CategoryTheory Limits AlgebraicGeometry Opposite Matrix MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ}
  {S S' : Scheme.{0}} {s : S ⟶ Sp R} {s' : S' ⟶ Sp R} {o' : Obj b N s'} {o : Obj b N s} {f : S' ⟶ S}

end GlobalTheory.UPel.HT
end
end

section

open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW

theorem WordData.Mi_add_hi_le_two_mul {n : ℕ} (W : WordData n) (hB : W.Box) (hT : W.ThickOr) (i : ZMod n) :
    W.Mi i + W.hi i ≤ 2 * (W.b + W.η + W.S) := by
  obtain ⟨-, -, hw, -, -, -⟩ := hB
  have hs : W.sz i ≤ (W.b : ℤ) + W.η := by
    rcases hT i with h | h
    · exact h.2
    · omega
  unfold WordData.Mi WordData.hi
  split_ifs <;> omega

theorem pageWord_Mi_add_hi_le {D : D7} (L : SizeData₂ D) (C : ℝ) (j : Fin D.R.m) (ε : ℤˣ) (τ φ : D.R.GG)
    (hR : Roomy L C) (i : ZMod (orderOf φ)) :
    (((pageWord L j ε τ φ).Mi i + (pageWord L j ε τ φ).hi i : ℕ) : ℝ) ≤ 2 * hPage L := by
  have h1 := WordData.Mi_add_hi_le_two_mul _ (GlobalTheory.T.twistedDualOrbitPageWord_box L C j ε τ φ hR) (GlobalTheory.T.twistedDualOrbitPageWord_thickOr L C j ε τ φ hR) i
  have h2 := GlobalTheory.T.sum_roundedSizes_le_height L C hR
  have h3 : (((pageWord L j ε τ φ).Mi i + (pageWord L j ε τ φ).hi i : ℕ) : ℝ)
      ≤ ((2 * (bHat L + etaHat L + sHat L) : ℕ) : ℝ) := Nat.cast_le.mpr h1
  refine h3.trans ?_
  push_cast
  linarith

end GlobalTheory.HTW
end

section

open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW

theorem pageWord_inert_dichotomy : ∀ {D : D7} (L : SizeData₂ D) (C : ℝ) (j : Fin D.R.m) (ε : ℤˣ)
    (τ φ : D.R.GG) (l : ℕ), Roomy L C → 11 ≤ l → φ.1.2 = -1 →
    (pageWord L j ε τ φ).Box ∧ ((pageWord L j ε τ φ).HypNT ∨
      (φ = D.R.cc ∧ (pageWord L j ε τ φ).HypAT l ∧ ∀ i, (pageWord L j ε τ φ).thick i)) := by
  intro D L C j ε τ φ l hR hl hφ
  refine ⟨GlobalTheory.T.twistedDualOrbitPageWord_box L C j ε τ φ hR, ?_⟩
  by_cases h : φ = D.R.cc ∧ Thick D.host τ
  · obtain ⟨rfl, hτ⟩ := h
    exact Or.inr ⟨rfl, GlobalTheory.T.twistedDualOrbitPageWord_conj_hypAT_allThick L C j ε τ l hR hl hτ⟩
  · left
    have hLw : 3 ≤ D.host.Lw := by
      have := L.weightLength_ge_depth
      omega
    obtain ⟨h3, i, hi⟩ := GlobalTheory.T.inertPrime_nonthick_letter_no_three_thick D.host τ φ hLw hφ h
    have hth := GlobalTheory.T.twistedDualOrbitPageWord_thick_iff_thickEmbedding L C j ε τ φ hR
    refine ⟨(GlobalTheory.T.embeddingSign_alternate_of_sign_neg ε τ φ hφ).2, ⟨i, fun h' => hi ((hth i).1 h')⟩, ?_⟩
    intro k hk
    exact h3 k ⟨(hth _).1 hk.1, (hth _).1 hk.2.1, (hth _).1 hk.2.2⟩

end GlobalTheory.HTW
end

section

open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits

theorem _root_.GlobalTheory.T.twistedDualPageWord_jumps_in_windows : ∀ {D : D7} (L : SizeData₂ D) (C : ℝ) (j : Fin D.R.m) (ε : ℤˣ) (τ φ : D.R.GG), Roomy L C → (pageWord L j ε τ φ).T1 ∧ ∀ i, ∀ u ∈ (pageWord L j ε τ φ).J1 i, -((pageWord L j ε τ φ).Mi i : ℤ) ≤ u ∧ u ≤ (pageWord L j ε τ φ).hi i := by
  first | exact @GlobalTheory.HTW.pageWord_T1_and_J1_mem_window_of_roomy | exact GlobalTheory.HTW.pageWord_T1_and_J1_mem_window_of_roomy | (intros; apply GlobalTheory.HTW.pageWord_T1_and_J1_mem_window_of_roomy <;> assumption)
end

section

open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits

theorem _root_.GlobalTheory.T.pageWord_T2_and_J2_card_of_roomy : ∀ {D : D7} (L : SizeData₂ D) (C : ℝ) (j : Fin D.R.m) (ε : ℤˣ) (τ φ : D.R.GG), Roomy L C → (pageWord L j ε τ φ).T2 ∧ ∀ i, ((pageWord L j ε τ φ).J2 i).card = D.R.r ∧ (((pageWord L j ε τ φ).J2 i).filter fun u : ℤ => |u| ≤ (etaHat L : ℤ)).card = D.R.m := by
  first | exact @GlobalTheory.HTW.twistedDualPageWord_small_jumps_card | exact GlobalTheory.HTW.twistedDualPageWord_small_jumps_card | (intros; apply GlobalTheory.HTW.twistedDualPageWord_small_jumps_card <;> assumption)
end

section

open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits

theorem _root_.GlobalTheory.T.twistedDualPageWord_clusterDepth_long_orbit : ∀ {D : D7} (L : SizeData₂ D) (_ : ParameterChoice' D L) (C : ℝ) (j : Fin D.R.m) (ε : ℤˣ) (τ φ : D.R.GG) (l : ℕ), Roomy L C → 11 ≤ l → (l : ℝ) < LevelStarExponents.lA L → 4 * D.host.Lw < orderOf φ.2 → (pageWord L j ε τ φ).HypA (depth L l) := by
  first | exact @GlobalTheory.HTW.pageWord_hypA_depth_of_long_orbit | exact GlobalTheory.HTW.pageWord_hypA_depth_of_long_orbit | (intros; apply GlobalTheory.HTW.pageWord_hypA_depth_of_long_orbit <;> assumption)
end
