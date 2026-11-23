module

public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ContinuousAdeleNorm
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Formalism.ConjugateSelfDual.Bundle001
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RamificationInertia.Inertia
public import Mathlib.RingTheory.RamificationInertia.Ramification
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle594
public import Formalism.LocalRingCardinality.AdicCompletionLocal.InstIsAdicCompleteOCSpanSingletonSetCast
public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle260
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle507
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle592
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle513
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle501
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle595
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle510
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAdaptedOfSurjective
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
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
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle003
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsNotCongPow
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasExponentZeroIff
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.TrivialOnInertiaOfUnr
import Development.AutomorphicArithmetic.IntegralCasts.Bundle001
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle002
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.InvertibleSpanSingleton
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsAdicCompleteOfPowLe
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MemBallOfGaugeLt
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle015
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle024
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle593

@[expose] public section

section

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeightCounting GlobalTheory.Pst
  GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory

namespace GlobalTheory.NormKill

theorem loc_eq_one_of_compNorm_eq_one : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (ε : Formalism.L2.Host.HChar (maximalRealSubfield E)),
    compNorm E ε = 1 → ∀ v : HeightOneSpectrum (𝓞 (maximalRealSubfield E)), Formalism.MainNotions.SchurIrreducible.IsSplit (E := E) v →
    ∀ x, ε.loc v x = 1 := by
  intro E _ _ _ ε hε v hv x
  have h2 : Module.finrank (maximalRealSubfield E) E = 2 :=
    Algebra.IsQuadraticExtension.finrank_eq_two _ _

  have hnorm : Neutral.B1.localIdele (maximalRealSubfield E) v x ∈
      GlobalTheory.QuadSymbol.normGroup (maximalRealSubfield E) E
        (AdeleRing (𝓞 (maximalRealSubfield E)) (maximalRealSubfield E)) := by
    rw [GlobalTheory.IdeleNormChar.mem_normGroup_iff_everywhereNorm]
    refine ⟨fun w => ?_, fun w => ?_⟩
    · by_cases hw : w = v
      · subst hw
        have hx : GlobalTheory.IdeleNormChar.finComp (Neutral.B1.localIdele (maximalRealSubfield E) w x) w = x :=
          Units.ext (Neutral.B1.localIdele_snd_self _ w x)
        rw [hx]
        exact GlobalTheory.LFun.mem_normGroup_of_isSplit h2 hv x
      · have h1 : GlobalTheory.IdeleNormChar.finComp (Neutral.B1.localIdele (maximalRealSubfield E) v x) w = 1 := by
          apply Units.ext
          show (Neutral.B1.finiteSingle (maximalRealSubfield E) v (x : v.adicCompletion _)) w = 1
          exact GlobalTheory.LFun.finSingle_ne hw _
        rw [h1]
        exact one_mem _
    · have h1 : GlobalTheory.IdeleNormChar.infComp (Neutral.B1.localIdele (maximalRealSubfield E) v x) w = 1 :=
        Units.ext rfl
      rw [h1]
      exact one_mem _

  obtain ⟨z, hz⟩ := hnorm
  let y : (AdeleRing (𝓞 E) E)ˣ :=
    Units.map (GlobalTheory.UnitaryHeckeBaseChange.adeleEquiv (GlobalTheory.GalOfCusp.isCMExt_real E)).toRingHom.toMonoidHom z
  have hy : GlobalTheory.GalOfCusp.ideleNorm E y = Neutral.B1.localIdele (maximalRealSubfield E) v x := by
    apply Units.ext
    show Algebra.norm _ ((GlobalTheory.UnitaryHeckeBaseChange.adeleEquiv (GlobalTheory.GalOfCusp.isCMExt_real E)).symm
      ((GlobalTheory.UnitaryHeckeBaseChange.adeleEquiv (GlobalTheory.GalOfCusp.isCMExt_real E)) (z : _))) = _
    rw [RingEquiv.symm_apply_apply]
    exact congrArg Units.val hz
  have key : (GlobalTheory.GalOfCusp.compNorm E ε).1 y = (1 : Formalism.L2.Host.HChar E).1 y :=
    congrArg (fun χ : Formalism.L2.Host.HChar E => χ.1 y) hε
  rw [GlobalTheory.GalOfCusp.compNorm_apply, hy] at key
  exact key

end GlobalTheory.NormKill
end
end

section

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeightCounting GlobalTheory.Pst
  GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory

namespace GlobalTheory.FrobTrivChar

theorem eq_one_of_frob_trivial : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime]
    (φ : G E Ω →* (Qbar l)ˣ), Continuous φ →
    (∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, w.asIdeal.inertiaDeg ℤ = 1 → w.asIdeal.ramificationIdx ℤ = 1 →
      ∀ (A : ValuationSubring Ω) (σ : G E Ω), IsPlaceOver (F := E) A w → IsFrob (F := E) A (normV w) σ → φ σ = 1) →
    φ = 1 := by
  classical
  intro E Ω _ _ _ _ _ l _ φ hφ hev
  have : IsGalois E Ω := {}
  refine MonoidHom.ext fun g => ?_
  rw [MonoidHom.one_apply]
  by_contra hg
  have hV : IsOpen {x : G E Ω | φ x ≠ 1} := isOpen_ne_fun hφ continuous_const
  have hn : (fun u : G E Ω => u * g) ⁻¹' {x : G E Ω | φ x ≠ 1} ∈ nhds (1 : G E Ω) :=
    (hV.preimage (continuous_mul_const g)).mem_nhds (by simpa using hg)
  obtain ⟨L, hfd, hN, hL⟩ := (krullTopology_mem_nhds_one_iff_of_normal E Ω _).1 hn
  have hgal : IsGalois E L := {}
  have hS := Filter.eventually_cofinite.1 hev
  obtain ⟨v, hv, hf, he, B, hB, -, σ, hσ, hU⟩ := GlobalTheory.Published.cheb_holds E Ω L.fixingSubgroup
    L.fixingSubgroup_isOpen ((InfiniteGalois.normal_iff_isGalois L).2 hgal) g hS.toFinset
  simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_not] at hv
  have h1 := hL hU
  simp only [Set.mem_preimage, Set.mem_setOf_eq, inv_mul_cancel_right] at h1
  exact h1 (hv hf he B σ hB hσ)

end GlobalTheory.FrobTrivChar
end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

namespace GlobalTheory.AinfInvLim

theorem dvd_mul_entry {R : Type} [CommRing R] {d : ℕ} (c : R) (A B : Matrix (Fin d) (Fin d) R)
    (h : ∀ i j, c ∣ B i j) (i j : Fin d) : c ∣ (A * B) i j := by
  rw [Matrix.mul_apply]
  exact Finset.dvd_sum fun k _ => dvd_mul_of_dvd_right (h k j) _

theorem exists_mul_eq_smul_one : ∀ (l : ℕ) [Fact l.Prime] (d M : ℕ) (τ : Ainf l)
    (Y : Matrix (Fin d) (Fin d) (Ainf l)), IsUnit (Y.map (inclW l)) →
    (∀ n, ∃ Q : Matrix (Fin d) (Fin d) (Ainf l), ∀ i j, (l : WCb l) ^ n ∣
      (Y.map (inclW l) * Q.map (inclW l) - inclW l τ ^ M • (1 : Matrix (Fin d) (Fin d) (WCb l))) i j) →
    ∃ Y' : Matrix (Fin d) (Fin d) (Ainf l), Y * Y' = τ ^ M • (1 : Matrix (Fin d) (Fin d) (Ainf l)) := by
  intro l _ d M τ Y hY hQ
  have hinj : Function.Injective (inclW l) :=
    WittVector.map_injective _ (IsFractionRing.injective (OCb l) (Cb l))
  set A := Y.map (inclW l) with hA
  set c := inclW l τ ^ M with hc
  have hAinv : A * A⁻¹ = 1 := Matrix.mul_nonsing_inv A ((Matrix.isUnit_iff_isUnit_det A).1 hY)
  have hinvA : A⁻¹ * A = 1 := Matrix.nonsing_inv_mul A ((Matrix.isUnit_iff_isUnit_det A).1 hY)
  set Z := c • A⁻¹ with hZ
  have hZent : ∀ i j, ∃ a : Ainf l, Z i j = inclW l (1 * a) := by
    intro i j
    refine GlobalTheory.AinfSat.mem_ideal_of_saturated l 1 (by rw [map_one]; exact isUnit_one) 0 (Z i j) fun n => ?_
    obtain ⟨Q, hQn⟩ := hQ n
    have h1 := dvd_mul_entry _ A⁻¹ _ hQn i j
    have h2 : A⁻¹ * (A * Q.map (inclW l) - c • (1 : Matrix (Fin d) (Fin d) (WCb l))) =
        Q.map (inclW l) - Z := by
      rw [Matrix.mul_sub, ← Matrix.mul_assoc, hinvA, Matrix.one_mul, Matrix.mul_smul, Matrix.mul_one]
    rw [h2] at h1
    refine ⟨Q i j, ?_⟩
    rw [pow_zero, one_mul, one_mul, dvd_sub_comm]
    simpa [Matrix.sub_apply] using h1
  choose Y' hY' using hZent
  refine ⟨Matrix.of fun i j => Y' i j, ?_⟩
  have hmap : (Matrix.of fun i j => Y' i j).map (inclW l) = Z := by
    ext i j; simp [hY' i j]
  have key : (Y * Matrix.of fun i j => Y' i j).map (inclW l) =
      (τ ^ M • (1 : Matrix (Fin d) (Fin d) (Ainf l))).map (inclW l) := by
    rw [Matrix.map_mul, hmap, hZ, Matrix.mul_smul, ← hA, hAinv]
    ext i j
    simp [Matrix.one_apply, hc, Matrix.smul_apply]
    split_ifs <;> simp
  refine Matrix.ext fun i j => hinj ?_
  exact congrFun (congrFun (congrArg Matrix.of.symm key) i) j

end GlobalTheory.AinfInvLim
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory.FundSeq

theorem tensor_fundamental_sequence :
    ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] (V : Type) [AddCommGroup V] [Module LL V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] LL V], (∀ (u : V ⊗[ℚ_[l]] P.R.B) (w : V ⊗[ℚ_[l]] P.R.BdR), ∃ (x : V ⊗[ℚ_[l]] P.R.B) (y : V ⊗[ℚ_[l]] P.R.BdR), y ∈ FilV (P.PD K) (LL := LL) (V := V) 0 ∧ x - φVB (P.PD K) (LL := LL) (V := V) x = u ∧ ιV (P.PD K) (LL := LL) (V := V) x - y = w) ∧ ∀ x : V ⊗[ℚ_[l]] P.R.B, φVB (P.PD K) (LL := LL) (V := V) x = x → ιV (P.PD K) (LL := LL) (V := V) x ∈ FilV (P.PD K) (LL := LL) (V := V) 0 → ∃ v : V, x = v ⊗ₜ[ℚ_[l]] (1 : P.R.B) := by
  intro l _ P AI hT K LL _ _ V _ _ _ _
  obtain ⟨-, h1, h2⟩ := GlobalTheory.MemLoc.tied_regular_and_onto l P AI hT
  have hA : ∀ u : V ⊗[ℚ_[l]] P.R.B, ∃ x : V ⊗[ℚ_[l]] P.R.B,
      x - φVB (P.PD K) (LL := LL) (V := V) x = u := by
    intro u
    induction u using TensorProduct.induction_on with
    | zero => exact ⟨0, by simp⟩
    | tmul v b =>
      obtain ⟨x, hx⟩ := h1 b
      refine ⟨v ⊗ₜ x, ?_⟩
      have : φVB (P.PD K) (LL := LL) (V := V) (v ⊗ₜ x) = v ⊗ₜ (P.PD K).φ x := rfl
      rw [this, P.PD_φ, ← TensorProduct.tmul_sub, hx]
    | add u u' hu hu' =>
      obtain ⟨x, hx⟩ := hu
      obtain ⟨x', hx'⟩ := hu'
      refine ⟨x + x', ?_⟩
      rw [map_add (f := _), ← hx, ← hx']
      abel
  have hB : ∀ w : V ⊗[ℚ_[l]] P.R.BdR, ∃ x : V ⊗[ℚ_[l]] P.R.B,
      φVB (P.PD K) (LL := LL) (V := V) x = x ∧
        ιV (P.PD K) (LL := LL) (V := V) x - w ∈ FilV (P.PD K) (LL := LL) (V := V) 0 := by
    intro w
    induction w using TensorProduct.induction_on with
    | zero => exact ⟨0, by simp, by simp⟩
    | tmul v b =>
      obtain ⟨x, hx, hx'⟩ := h2 K b
      refine ⟨v ⊗ₜ x, ?_, ?_⟩
      · have : φVB (P.PD K) (LL := LL) (V := V) (v ⊗ₜ x) = v ⊗ₜ (P.PD K).φ x := rfl
        rw [this, P.PD_φ, hx]
      · have : ιV (P.PD K) (LL := LL) (V := V) (v ⊗ₜ x) = v ⊗ₜ (P.PD K).ι x := rfl
        rw [this, P.PD_ι, ← TensorProduct.tmul_sub]
        exact ⟨v ⊗ₜ ⟨P.ιB x - b, hx'⟩, rfl⟩
    | add w w' hw hw' =>
      obtain ⟨x, hx, hy⟩ := hw
      obtain ⟨x', hx', hy'⟩ := hw'
      refine ⟨x + x', by rw [map_add (f := _), hx, hx'], ?_⟩
      have := Submodule.add_mem _ hy hy'
      rw [map_add (f := _)]
      convert this using 1
      abel
  refine ⟨fun u w => ?_, fun x hx hF =>
    GlobalTheory.exists_tmul_one_of_frob_fixed_of_mem_fil_zero (P.PD K) x hx hF⟩
  obtain ⟨x₀, hx₀⟩ := hA u
  obtain ⟨x₁, hx₁, hy⟩ := hB (w - ιV (P.PD K) (LL := LL) (V := V) x₀)
  refine ⟨x₀ + x₁, _, hy, ?_, ?_⟩
  · rw [map_add (f := _), hx₁, ← hx₀]
    abel
  · rw [map_add (f := _)]
    abel

end GlobalTheory.FundSeq
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc
open scoped Formalism.Per NNReal

namespace GlobalTheory.Per.RatSpan

theorem crisSpan_rat : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K : FinExt l) (V : Type) [AddCommGroup V] [Module ℚ_[l] V] [FiniteDimensional ℚ_[l] V] (ρ : Representation ℚ_[l] ↥(GK K) V), IsCrys (P.PD K) ρ → ∀ y : V ⊗[ℚ_[l]] P.R.B, ∃ (m : ℕ) (b : Fin m → P.R.B) (d : Fin m → V ⊗[ℚ_[l]] P.R.B), (∀ i, d i ∈ Dcris (P.PD K) ρ) ∧ y = ∑ i, AlgebraTensorModule.map (LinearMap.id : V →ₗ[ℚ_[l]] V) (LinearMap.mulLeft ℚ_[l] (b i)) (d i) := by
  intro l _ P AI hT K V _ _ _ ρ hC y
  have hreg := (tied_regular_and_onto l P AI hT).1
  let LL : FinExt l := ⟨⊥, inferInstance⟩
  let e : (↥(LL.1)) ≃ₐ[ℚ_[l]] ℚ_[l] := IntermediateField.botEquiv ℚ_[l] (Om l)
  letI iM : Module (↥(LL.1)) V := Module.compHom V e.toRingEquiv.toRingHom
  haveI iT : IsScalarTower ℚ_[l] (↥(LL.1)) V :=
    ⟨fun q x v => by
      show e (q • x) • v = q • (e x • v)
      rw [show e (q • x) = q • e x from e.toLinearEquiv.map_smul q x, smul_eq_mul, mul_smul]⟩
  haveI iF : FiniteDimensional (↥(LL.1)) V := Module.Finite.of_restrictScalars_finite ℚ_[l] (↥(LL.1)) V
  let ρ' : Representation (↥(LL.1)) (↥(GK K)) V :=
    { toFun := fun g =>
        { toFun := ρ g, map_add' := (ρ g).map_add, map_smul' := fun x v => (ρ g).map_smul (e x) v }
      map_one' := by ext v; simp
      map_mul' := by intro g h; ext v; simp; rfl }
  have hact : ∀ g (x : V ⊗[ℚ_[l]] P.R.B), actVB (P.PD K) ρ' g x = actVB (P.PD K) ρ g x := by
    intro g x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul v b => rfl
    | add x z hx hz => rw [map_add (f := _), map_add (f := _), hx, hz]
  have hmem : ∀ x : V ⊗[ℚ_[l]] P.R.B, x ∈ Dcris (P.PD K) ρ' ↔ x ∈ Dcris (P.PD K) ρ := by
    intro x
    simp only [Dcris, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply,
      sub_eq_zero, hact]
  have hfr : ∀ (W : Type) [AddCommGroup W] [Module (↥(LL.1)) W] [Module ℚ_[l] W]
      [IsScalarTower ℚ_[l] (↥(LL.1)) W], Module.finrank (↥(LL.1)) W = Module.finrank ℚ_[l] W := by
    intro W _ _ _ _
    rw [← Module.finrank_mul_finrank ℚ_[l] (↥(LL.1)) W]
    have : Module.finrank ℚ_[l] (↥(LL.1)) = 1 := IntermediateField.finrank_bot
    rw [this, one_mul]
  let eq : ↥(Dcris (P.PD K) ρ') ≃ₗ[ℚ_[l]] ↥(Dcris (P.PD K) ρ) :=
    { toFun := fun x => ⟨x.1, (hmem x.1).1 x.2⟩
      invFun := fun x => ⟨x.1, (hmem x.1).2 x.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hC' : IsCrys (P.PD K) ρ' := by
    unfold IsCrys at hC ⊢
    rw [hfr, hfr, eq.finrank_eq, hC]
  obtain ⟨m, b, d, hd, hy⟩ := TiedSpan.tied_crisSpan l P AI hT hreg K LL V ρ' hC' y
  refine ⟨m, b, d, fun i => (hmem _).1 (hd i), ?_⟩
  rw [hy]
  refine Finset.sum_congr rfl fun i _ => ?_
  induction d i using TensorProduct.induction_on with
  | zero => simp
  | tmul v c => rfl
  | add x z hx hz => rw [map_add (f := _), map_add (f := _), hx, hz]

end GlobalTheory.Per.RatSpan
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

noncomputable section

namespace GlobalTheory.Per.CrisStrict

section Abstract

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    {V' : Type} [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V']

theorem ιV_map (f : V →ₗ[LL] V') (x : V ⊗[Qp] B) :
    ιV PD (LL := LL) (V := V') (AlgebraTensorModule.map f (LinearMap.id : B →ₗ[Qp] B) x) =
      AlgebraTensorModule.map f (LinearMap.id : BdR →ₗ[Qp] BdR) (ιV PD (LL := LL) (V := V) x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add (f := _), ha, hb]
  | tmul v b => simp [ιV]

theorem map_mem_Dcris (ρ : Representation LL G V) (ρ' : Representation LL G V') (f : V →ₗ[LL] V')
    (hf : ∀ g x, f (ρ g x) = ρ' g (f x)) {x : V ⊗[Qp] B} (hx : x ∈ Dcris PD ρ) :
    AlgebraTensorModule.map f (LinearMap.id : B →ₗ[Qp] B) x ∈ Dcris PD ρ' := by
  have key : ∀ (g : G) (z : V ⊗[Qp] B), actVB PD ρ' g (AlgebraTensorModule.map f (LinearMap.id : B →ₗ[Qp] B) z) =
      AlgebraTensorModule.map f (LinearMap.id : B →ₗ[Qp] B) (actVB PD ρ g z) := by
    intro g z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
    | tmul v b => simp [actVB, hf]
  rw [GlobalTheory.Per.CrisDR.mem_Dcris_iff] at hx ⊢
  intro g
  rw [key, hx g]

theorem map_mem_FilV (f : V →ₗ[LL] V') {a : ℤ} {x : V ⊗[Qp] BdR} (hx : x ∈ FilV PD (LL := LL) (V := V) a) :
    AlgebraTensorModule.map f (LinearMap.id : BdR →ₗ[Qp] BdR) x ∈ FilV PD (LL := LL) (V := V') a := by
  obtain ⟨z, rfl⟩ := hx
  refine ⟨AlgebraTensorModule.map f (LinearMap.id) z, ?_⟩
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add (f := _), ha, hb]
  | tmul v b => simp

theorem map_map_id {V'' : Type} [AddCommGroup V''] [Module LL V''] [Module Qp V''] [IsScalarTower Qp LL V'']
    (f : V →ₗ[LL] V') (g : V' →ₗ[LL] V'') (x : V ⊗[Qp] BdR) :
    AlgebraTensorModule.map g (LinearMap.id : BdR →ₗ[Qp] BdR)
      (AlgebraTensorModule.map f (LinearMap.id : BdR →ₗ[Qp] BdR) x) =
      AlgebraTensorModule.map (g ∘ₗ f) (LinearMap.id : BdR →ₗ[Qp] BdR) x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add (f := _), ha, hb]
  | tmul v b => simp

theorem mem_FilV_of_injective (f : V →ₗ[LL] V') (hi : Function.Injective f) {a : ℤ} {x : V ⊗[Qp] BdR}
    (hx : AlgebraTensorModule.map f (LinearMap.id : BdR →ₗ[Qp] BdR) x ∈ FilV PD (LL := LL) (V := V') a) :
    x ∈ FilV PD (LL := LL) (V := V) a := by
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective f (LinearMap.ker_eq_bot.2 hi)
  have := map_mem_FilV PD g hx
  rwa [map_map_id, hg, AlgebraTensorModule.map_id, LinearMap.id_apply] at this

end Abstract

theorem dcris_strict : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K LL : FinExt l), Function.Bijective (algebraMap ↥(K0 K) ↥K.1) → ∀ (V₁ : Type) [AddCommGroup V₁] [Module ↥LL.1 V₁] [Module ℚ_[l] V₁] [IsScalarTower ℚ_[l] ↥LL.1 V₁] [FiniteDimensional ↥LL.1 V₁] (ρ₁ : Representation ↥LL.1 ↥(GK K) V₁) (V₂ : Type) [AddCommGroup V₂] [Module ↥LL.1 V₂] [Module ℚ_[l] V₂] [IsScalarTower ℚ_[l] ↥LL.1 V₂] [FiniteDimensional ↥LL.1 V₂] (ρ₂ : Representation ↥LL.1 ↥(GK K) V₂) (π : V₁ →ₗ[↥LL.1] V₂), (∀ g x, π (ρ₁ g x) = ρ₂ g (π x)) → (Function.Surjective π → IsCrys (P.PD K) ρ₁ → ∀ a : ℤ, (FilCris (P.PD K) ρ₁ a).map (AlgebraTensorModule.map π (LinearMap.id : P.R.B →ₗ[ℚ_[l]] P.R.B)) = FilCris (P.PD K) ρ₂ a) ∧ (Function.Injective π → ∀ a : ℤ, ∀ y ∈ Dcris (P.PD K) ρ₁, AlgebraTensorModule.map π (LinearMap.id : P.R.B →ₗ[ℚ_[l]] P.R.B) y ∈ FilCris (P.PD K) ρ₂ a → y ∈ FilCris (P.PD K) ρ₁ a) := by
  intro l _ P AI T K LL hb V₁ _ _ _ _ _ ρ₁ V₂ _ _ _ _ _ ρ₂ π hπ
  refine ⟨fun hs hc a => le_antisymm ?_ ?_, fun hi a y hy hF => ?_⟩
  · rintro _ ⟨x, ⟨hxD, hxF⟩, rfl⟩
    refine ⟨map_mem_Dcris (P.PD K) ρ₁ ρ₂ π hπ hxD, Submodule.mem_comap.2 ?_⟩
    rw [ιV_map]
    exact map_mem_FilV (P.PD K) π (Submodule.mem_comap.1 hxF)
  · rintro y ⟨hyD, hyF⟩
    have hc2 := ((GlobalTheory.Per.CrysSubQuot.crys_sub_quot l P AI T K LL V₁ ρ₁ V₂ ρ₂ π hπ).2 hs hc).1
    have hyR : ιV (P.PD K) (LL := ↥LL.1) (V := V₂) y ∈ DdR (P.PD K) ρ₂ := by
      rw [← (GlobalTheory.Per.DdREqDcris.map_Dcris_eq_DdR l P AI T K LL hb V₂ ρ₂ hc2).1]
      exact Submodule.mem_map_of_mem hyD
    have hdr1 := (GlobalTheory.Per.CrisDR.isDR_of_isCrys l P AI T K LL V₁ ρ₁ hc).1
    obtain ⟨x', ⟨hx'D, hx'F⟩, hx'⟩ :=
      ((GlobalTheory.DRSubQuot.deRham_sub_quot l P AI T K LL V₁ ρ₁ V₂ ρ₂ π hπ).2 hs hdr1).2 a _ ⟨hyR, hyF⟩
    rw [← (GlobalTheory.Per.DdREqDcris.map_Dcris_eq_DdR l P AI T K LL hb V₁ ρ₁ hc).1] at hx'D
    obtain ⟨x, hx, rfl⟩ := hx'D
    refine ⟨x, ⟨hx, hx'F⟩, ?_⟩
    apply GlobalTheory.Per.DdREqDcris.ιV_injective (P.PD K) (LL := ↥LL.1)
    rw [ιV_map, hx']
  · refine ⟨hy, ?_⟩
    have h2 := Submodule.mem_comap.1 hF.2
    rw [ιV_map] at h2
    exact Submodule.mem_comap.2 (mem_FilV_of_injective (P.PD K) π hi h2)

end GlobalTheory.Per.CrisStrict
end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
open GlobalTheory.HodgeAt

namespace GlobalTheory

theorem card_eq_of_indep_spans_dR : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (a m : ℕ) (w : Fin m → Fin a → P.R.BdR), (∀ β : Fin m → P.R.BdR, ∑ i, β i • w i = 0 → β = 0) → (∀ j, ∃ u : Fin m → P.R.BdR, ∑ i, u i • w i = Pi.single j 1) → m = a := by
  intro l _ P AI T a m w hind hspan
  haveI : Nontrivial P.R.BdR := (GlobalTheory.DRFil.isField_dR T).nontrivial
  have hli : LinearIndependent P.R.BdR w := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    exact congrFun (hind g hg) i
  have h1 : m ≤ a := by
    have := hli.fintype_card_le_finrank
    simpa [Module.finrank_fin_fun] using this
  have hsurj : Function.Surjective (Fintype.linearCombination P.R.BdR w) := by
    rw [← LinearMap.range_eq_top, Submodule.eq_top_iff']
    intro x
    have hj : ∀ j, Pi.single j (x j) ∈ LinearMap.range (Fintype.linearCombination P.R.BdR w) := by
      intro j
      obtain ⟨u, hu⟩ := hspan j
      refine ⟨x j • u, ?_⟩
      rw [map_smul, Fintype.linearCombination_apply, hu]
      ext k
      by_cases h : k = j
      · subst h; simp
      · simp [Pi.single_apply, h]
    rw [← Finset.univ_sum_single x]
    exact Submodule.sum_mem _ fun j _ => hj j
  have h2 : a ≤ m := by
    simpa using card_le_of_surjective P.R.BdR _ hsurj
  exact le_antisymm h1 h2

end GlobalTheory
end
