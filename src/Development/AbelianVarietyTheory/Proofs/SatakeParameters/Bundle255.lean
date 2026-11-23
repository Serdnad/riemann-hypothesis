module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle008
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSupportOfIsSubquotientProdIrr
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitPlaceHeckeOperatorScalarOnSpherical
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle411
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle024
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle050
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceLocalComponentExistsUniqueClass
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPolarizedTwistAbsPow
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1892
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle713
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle081
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle078
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle013
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle226
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle164
import Formalism.LocalRingCardinality.SpanPowerMembership.LocAtA
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAffCoverSpec
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle248
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle246
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle247
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle249
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle003
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle022
import Formalism.AlgebraicWeights.IsAlgWeight
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import ReciprocityTheory.Automorphisms.PlaceA
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsNotCongPow
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsWeight
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle002
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle013
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasExponentZeroIff
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.TrivialOnInertiaOfUnr

@[expose] public section

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil

namespace GlobalTheory.CuspidalSupportZero

theorem exists_isCuspSupport_zero (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (π : Irr k 0) :
    ∃ (s : ℕ) (d : Fin s → ℕ) (σ : ∀ a, Irr k (d a)), IsCuspSupport π.π d (fun a => (σ a).π) := by
  haveI : Subsingleton (GL (Fin 0) k) := ⟨fun _ _ => Units.ext (Subsingleton.elim _ _)⟩
  let d : Fin 0 → ℕ := fun a => a.elim0
  let σ : ∀ a, Irr k (d a) := fun a => a.elim0
  refine ⟨0, d, σ, π.irr, fun a => a.elim0, ?_⟩
  let e : (Σ a, Fin (d a)) ≃ Fin 0 := Equiv.equivOfIsEmpty _ _
  refine ⟨e, ?_⟩
  obtain ⟨φ⟩ := GlobalTheory.LocGL.SupportRing.nonempty_equiv_unit (k := k) e (fun a => (σ a).π)
  have hirr := π.irr

  obtain ⟨v₀, hv₀⟩ : ∃ v : π.V, v ≠ 0 := by
    by_contra h
    push_neg at h
    apply (bot_ne_top : (⊥ : Subrepresentation π.π) ≠ ⊤)
    ext v
    simp [h v]
  let L : Subrepresentation π.π := ⟨ℂ ∙ v₀, fun g v hv => by
    rw [Subsingleton.elim g 1, map_one]; exact hv⟩
  have hL : L = ⊤ := by
    rcases eq_bot_or_eq_top L with h | h
    · exfalso
      have : v₀ ∈ L.toSubmodule := Submodule.mem_span_singleton_self v₀
      rw [h] at this
      exact hv₀ ((Submodule.mem_bot ℂ).1 this)
    · exact h
  let f : (multiProd e fun a => (σ a).π).IntertwiningMap π.π :=
    { toLinearMap := (LinearMap.toSpanSingleton ℂ π.V v₀) ∘ₗ φ.toLinearEquiv.toLinearMap
      isIntertwining' := fun g => by
        rw [Subsingleton.elim g 1, map_one, map_one]; rfl }
  refine IsSubquotient.of_surjective f fun v => ?_
  have hv : v ∈ L.toSubmodule := by rw [hL]; trivial
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hv
  refine ⟨φ.toLinearEquiv.symm c, ?_⟩
  show (LinearMap.toSpanSingleton ℂ π.V v₀) (φ.toLinearEquiv (φ.toLinearEquiv.symm c)) = c • v₀
  erw [LinearEquiv.apply_symm_apply]
  rfl

end GlobalTheory.CuspidalSupportZero
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.IsoTypFixLoc

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {W : Type} [AddCommGroup W] [Module ℂ W]

theorem rt_rt (h h' : GAf L n) (f : GAf L n → W) : NG.rt L n h (NG.rt L n h' f) = NG.rt L n (h * h') f := by
  funext g; simp [NG.rt, mul_assoc]

def LocEq (s : SplitPlace L) (τ : GlobalTheory.SmGL.IrrRep (GL (Fin n) (s.w.adicCompletion L)))
    (i : s.v.adicCompletion (maximalRealSubfield L) ≃+* s.w.adicCompletion L) (T : τ.V →ₗ[ℂ] (GAf L n → W)) : Prop :=
  ∀ x : GAf L n, TrivOutside {s.v} x → ∀ a, T (τ.ρ (Matrix.GeneralLinearGroup.map i.toRingHom (s.loc n x)) a) = NG.rt L n x (T a)

theorem le_iSup_range (ρ : Representation ℂ (GQ L n) W) (S : Submodule ℂ (GAf L n → W)) (hS : NG.IsIrrRep ρ S)
    (s : SplitPlace L) (τ : GlobalTheory.SmGL.IrrRep (GL (Fin n) (s.w.adicCompletion L)))
    (i : s.v.adicCompletion (maximalRealSubfield L) ≃+* s.w.adicCompletion L) (T0 : τ.V →ₗ[ℂ] (GAf L n → W))
    (hT0inj : Function.Injective T0) (hT0S : ∀ a, T0 a ∈ S) (hT0eq : LocEq s τ i T0) :
    S ≤ ⨆ T : {T : τ.V →ₗ[ℂ] (GAf L n → W) // LocEq s τ i T}, LinearMap.range T.1 := by
  obtain ⟨hdec, hcomm, -⟩ := GlobalTheory.T.unitaryFiniteAdeles_splitPlace_decomposition L n s
  have hnt : Nontrivial τ.V := by
    haveI := τ.irr
    by_contra hn
    rw [not_nontrivial_iff_subsingleton] at hn
    apply (bot_ne_top : (⊥ : Subrepresentation τ.ρ) ≠ ⊤)
    have : ∀ W : Subrepresentation τ.ρ, W = ⊥ := by
      intro W
      ext x
      simp [Subsingleton.elim x 0]
    rw [this ⊤]
  let Good : (τ.V →ₗ[ℂ] (GAf L n → W)) → Prop := fun T => LocEq s τ i T ∧ ∀ u, T u ∈ S
  let Wd : Submodule ℂ (GAf L n → W) := ⨆ T : {T // Good T}, LinearMap.range T.1
  have hWdS : Wd ≤ S := by
    refine iSup_le fun T => ?_
    rintro _ ⟨u, rfl⟩
    exact T.2.2 u
  have hWdle : Wd ≤ ⨆ T : {T : τ.V →ₗ[ℂ] (GAf L n → W) // LocEq s τ i T}, LinearMap.range T.1 :=
    iSup_le fun T => le_iSup_of_le (⟨T.1, T.2.1⟩ : {T : τ.V →ₗ[ℂ] (GAf L n → W) // LocEq s τ i T}) le_rfl
  have htr : ∀ (T : τ.V →ₗ[ℂ] (GAf L n → W)) (y : GAf L n), Good T → TrivOutside {s.v}ᶜ y → Good ((NG.rt L n y).comp T) := by
    intro T y hT hy
    refine ⟨fun x hx u => ?_, fun u => hS.1.stable y _ (hT.2 u)⟩
    simp only [LinearMap.comp_apply]
    rw [hT.1 x hx u, rt_rt, rt_rt, (hcomm x y hx hy).eq]
  have hstab : ∀ h, ∀ f ∈ Wd, NG.rt L n h f ∈ Wd := by
    intro h f hf
    refine Submodule.iSup_induction _ (motive := fun f => NG.rt L n h f ∈ Wd) hf ?_ ?_ ?_
    · rintro T _ ⟨u, rfl⟩
      obtain ⟨x, y, hx, hy, he⟩ := hdec h
      have e : NG.rt L n h (T.1 u) = ((NG.rt L n y).comp T.1) (τ.ρ (Matrix.GeneralLinearGroup.map i.toRingHom (s.loc n x)) u) := by
        rw [LinearMap.comp_apply, T.2.1 x hx u, rt_rt, he, (hcomm x y hx hy).eq]
      rw [e]
      exact Submodule.mem_iSup_of_mem (⟨_, htr T.1 y T.2 hy⟩ : {T // Good T}) ⟨_, rfl⟩
    · simp
    · intro f₁ f₂ h₁ h₂; rw [map_add (f := _)]; exact Submodule.add_mem _ h₁ h₂
  have hT0 : Good T0 := ⟨hT0eq, hT0S⟩
  rcases hS.2.2 Wd ⟨hWdS.trans hS.1.le, hstab⟩ hWdS with h0 | h0
  · exfalso
    obtain ⟨u, hu⟩ := exists_ne (0 : τ.V)
    have hmem : T0 u ∈ Wd := Submodule.mem_iSup_of_mem (⟨T0, hT0⟩ : {T // Good T}) ⟨u, rfl⟩
    rw [h0, Submodule.mem_bot] at hmem
    exact hu (hT0inj (hmem.trans (map_zero T0).symm))
  · rw [← h0]
    exact hWdle

theorem isoTyp_le (ρ : Representation ℂ (GQ L n) W) (S : Submodule ℂ (GAf L n → W))
    (s : SplitPlace L) (τ : GlobalTheory.SmGL.IrrRep (GL (Fin n) (s.w.adicCompletion L)))
    (i : s.v.adicCompletion (maximalRealSubfield L) ≃+* s.w.adicCompletion L) (T0 : τ.V →ₗ[ℂ] (GAf L n → W))
    (hT0inj : Function.Injective T0) (hT0S : ∀ a, T0 a ∈ S) (hT0eq : LocEq s τ i T0) :
    NG.isoTyp ρ S ≤ ⨆ T : {T : τ.V →ₗ[ℂ] (GAf L n → W) // LocEq s τ i T}, LinearMap.range T.1 := by
  refine sSup_le ?_
  rintro S' ⟨hS', E, hE⟩
  let T1 : τ.V →ₗ[ℂ] (GAf L n → W) := S'.subtype ∘ₗ (E : S →ₗ[ℂ] S') ∘ₗ LinearMap.codRestrict S T0 hT0S
  refine le_iSup_range ρ S' hS' s τ i T1 ?_ (fun a => (E _).2) ?_
  · intro a b hab
    apply hT0inj
    have := E.injective (Subtype.ext hab)
    exact congrArg Subtype.val this
  · intro x hx a
    exact hE x ⟨T0 a, hT0S a⟩ ⟨_, hT0S _⟩ (hT0eq x hx a)

end GlobalTheory.IsoTypFixLoc


open GlobalTheory.IsoTypFixLoc in
theorem GlobalTheory.IsoTypFixLoc.main : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (W : Type) [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ (GQ L n) W) (S : Submodule ℂ (GAf L n → W)), NG.IsIrrRep ρ S → ∀ (s : SplitPlace L) (τ : GlobalTheory.SmGL.IrrRep (GL (Fin n) (s.w.adicCompletion L))), IsLocS S s τ → ∀ (i : s.v.adicCompletion (maximalRealSubfield L) ≃+* s.w.adicCompletion L), Continuous i → (∀ x : L, i (s.i x) = algebraMap L (s.w.adicCompletion L) x) → ∀ f ∈ NG.isoTyp ρ S, f ≠ 0 → (∀ κ ∈ GlobalTheory.HeckeScalarSph.locK n s.v, NG.rt L n κ f = f) → ∃ a : τ.V, a ≠ 0 ∧ ∀ κ ∈ GlobalTheory.HeckeScalarSph.locK n s.v, τ.ρ (Matrix.GeneralLinearGroup.map i.toRingHom (s.loc n κ)) a = a := by
  intro L _ _ _ n W _ _ ρ S hS s τ hloc i hi hiL f hf hf0 hfix
  classical
  obtain ⟨i', T0, hi', hi'L, hT0inj, hT0S, hT0eq⟩ := hloc
  obtain rfl := GlobalTheory.splitPlace_completion_equiv_unique L s i' i hi' hi hi'L hiL
  have hspan := isoTyp_le ρ S s τ i' T0 hT0inj hT0S hT0eq hf
  have hI := GlobalTheory.T.unitaryFiniteAdeles_splitPlace_decomposition L n s
  let H : Subgroup (GAf L n) :=
    { carrier := {x | TrivOutside {s.v} x}
      mul_mem' := fun hx hy => GlobalTheory.HeckeScalarSph.triv_mul hx hy
      one_mem' := GlobalTheory.HeckeScalarSph.triv_one
      inv_mem' := fun hx => GlobalTheory.HeckeScalarSph.triv_inv hx }
  let φ : H →* GL (Fin n) (s.w.adicCompletion L) :=
    (Matrix.GeneralLinearGroup.map i'.toRingHom).comp ((s.loc n).comp H.subtype)
  have hφ : Function.Surjective φ := by
    intro h
    obtain ⟨x, ⟨hx, e⟩, -⟩ := hI.2.2 (Matrix.GeneralLinearGroup.map i'.symm.toRingHom h)
    refine ⟨⟨x, hx⟩, ?_⟩
    change Matrix.GeneralLinearGroup.map i'.toRingHom (s.loc n x) = h
    rw [e]
    exact Units.ext (Matrix.ext fun a b => i'.apply_symm_apply _)
  let σ' : Representation ℂ H τ.V := τ.ρ.comp φ
  have hσ' : σ'.IsIrreducible := GlobalTheory.LocCompSplit.isIrreducible_comp_of_surjective τ.ρ φ hφ τ.irr
  let ρ' : Representation ℂ H (GAf L n → W) :=
    { toFun := fun x => NG.rt L n (x : GAf L n)
      map_one' := by
        apply LinearMap.ext
        intro g
        funext a
        simp [NG.rt]
      map_mul' := fun x y => by
        apply LinearMap.ext
        intro g
        funext a
        simp [NG.rt, mul_assoc] }
  rw [Submodule.mem_iSup_iff_exists_finset] at hspan
  obtain ⟨t, ht⟩ := hspan
  let T : t → σ'.IntertwiningMap ρ' := fun j =>
    ⟨j.1.1, fun g => LinearMap.ext fun a => j.1.2 g.1 g.2 a⟩
  have hf' : f ∈ ⨆ j, LinearMap.range (T j).toLinearMap := by
    rw [iSup_subtype'] at ht
    exact ht
  let K : Subgroup H := (GlobalTheory.HeckeScalarSph.locK n s.v).comap H.subtype
  have hfixK : ∀ k ∈ K, ρ' k f = f := fun k hk => hfix k.1 hk
  have hne := GlobalTheory.UnrLoc.fixed_ne_bot_of_mem_iSup_range hσ' T K hf' hf0 hfixK
  rw [Submodule.ne_bot_iff] at hne
  obtain ⟨y, hy, hy0⟩ := hne
  refine ⟨y, hy0, fun κ hκ => ?_⟩
  exact (GlobalTheory.Parabolic.mem_fixed.1 hy) ⟨κ, hκ.2⟩ hκ
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.Published

noncomputable section


open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele (ideleMap ideleConj) in
open GlobalTheory.HeckeUnrExt in
theorem GlobalTheory.HeckeUnrExt.exists_ext_unr : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (χ : HChar (maximalRealSubfield E)) (b : ℤ), χ.IsAlg (fun _ => b) → (∀ w : HeightOneSpectrum (𝓞 E), ¬ GlobalTheory.UnitaryBC.IsSplitAt w → Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield E)) w.asIdeal ∧ χ.UnrAt (w.under (𝓞 (maximalRealSubfield E)))) → ∀ w₀ : HeightOneSpectrum (𝓞 E), GlobalTheory.UnitaryBC.IsSplitAt w₀ → ∃ (κ : HChar E) (m : (E →+* ℂ) → ℤ), κ.IsAlg m ∧ GlobalTheory.HeightCounting.Blocks.resReal κ = χ ∧ κ.UnrAt w₀ ∧ ∀ w : HeightOneSpectrum (𝓞 E), ¬ GlobalTheory.UnitaryBC.IsSplitAt w → κ.UnrAt w := by
  intro E _ _ _ ψ a hψ hns w₀ _
  classical
  obtain ⟨M, hM, hlev⟩ := GlobalTheory.Mem.HeckeLevel.exists_level_nat _ ψ
  obtain ⟨w₁, hw₁s, hw₁⟩ := GlobalTheory.T.exists_other_split_place_with_distinct_real_place E w₀
  set K : ℕ := Module.finrank ℚ E + 1 with hK
  set Q : ℕ := Ideal.absNorm w₁.asIdeal ^ K with hQ
  have hQ0 : 0 < Q := pow_pos (Nat.pos_of_ne_zero fun h => w₁.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)) _
  set N : ℕ := 3 * M * Q with hN
  have hN0 : 0 < N := by positivity
  let T : Set (HeightOneSpectrum (𝓞 E)) := {w | GlobalTheory.UnitaryBC.IsSplitAt w ∧ w ≠ w₀}
  let T' : Set (HeightOneSpectrum (𝓞 E)) := {w | ∀ w' : HeightOneSpectrum (𝓞 E),
      w'.under (𝓞 (maximalRealSubfield E)) = w.under (𝓞 (maximalRealSubfield E)) → w' ∈ T}
  have hw₁T : w₁ ∈ T' := fun w' e => by
    refine ⟨?_, fun h => hw₁ (h ▸ e).symm⟩
    by_cases h : w' = w₁
    · exact h ▸ hw₁s
    · exact ⟨w₁, fun h' => h h'.symm, e.symm⟩
  have hT'T : T' ⊆ T := fun w hw => hw w rfl
  have hF : ∀ b : Ideles (maximalRealSubfield E), ideleMap _ E b ∈ levT E T N → ψ.1 b = kap E a (ideleMap _ E b) := by
    intro b hb
    let z : (InfiniteAdeleRing (maximalRealSubfield E))ˣ := Units.map (MonoidHom.fst _ _) b
    have e : b = Units.map (MonoidHom.inl _ _) z * GlobalTheory.Mem.Chr.finPartI _ b :=
      Units.ext (Prod.ext (mul_one _).symm (one_mul _).symm)
    have h1 : ψ.1 (GlobalTheory.Mem.Chr.finPartI _ b) = 1 :=
      GlobalTheory.T.realSubfield_heckeChar_finitePart_eq_one E ψ M hlev (fun w hw => (hns w hw).2) w₀ N ⟨3 * Q, by rw [hN]; ring⟩ b hb
    have h2 : kap E a (ideleMap _ E b) = kap E a (ideleMap _ E (Units.map (MonoidHom.inl _ _) z)) := by
      apply Units.ext
      rw [coe_kap, coe_kap]
      rfl
    rw [h2, ← psi_eq_kap E ψ a hψ z]
    conv_lhs => rw [e, map_mul, h1, mul_one]
  have hprin : ∀ ε : Eˣ, diagUnits E ε ∈ levT E T' N → (∀ φ : E →+* ℂ, ‖φ ε‖ = 1) → ε = 1 := by
    intro ε hε hn
    refine Units.ext (GlobalTheory.T.eq_one_of_norm_one_valuation_sub_one_small E (ε : E) w₁ K (by omega) (fun v => ?_) hn ?_)
    · have e : Valued.v (algebraMap E (v.adicCompletion E) (ε : E)) = 1 := hε.1 v
      rw [GlobalTheory.UpIdeleMod.valued_algebraMap] at e
      exact e.le
    · have e : Valued.v (algebraMap E (w₁.adicCompletion E) (ε : E) - 1) ≤ Valued.v (N : w₁.adicCompletion E) := hε.2 w₁ hw₁T
      rw [← map_one (algebraMap E (w₁.adicCompletion E)), ← map_sub,
        ← map_natCast (algebraMap E (w₁.adicCompletion E)), GlobalTheory.UpIdeleMod.valued_algebraMap,
        GlobalTheory.UpIdeleMod.valued_algebraMap] at e
      refine e.trans ?_
      have eN : ((N : ℕ) : E) = algebraMap (𝓞 E) E ((3 * M : ℕ) : 𝓞 E) * algebraMap (𝓞 E) E ((Q : ℕ) : 𝓞 E) := by
        rw [← map_mul, ← Nat.cast_mul, map_natCast]
      rw [eN, map_mul]
      refine (mul_le_of_le_one_left' (HeightOneSpectrum.valuation_le_one _ _)).trans ?_
      rw [HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_le_pow_iff_mem]
      rw [hQ, Nat.cast_pow]
      exact Ideal.pow_mem_pow (Ideal.absNorm_mem w₁.asIdeal) K
  obtain ⟨ξ, hξ⟩ := glue
    (((ideleMap (maximalRealSubfield E) E).coprod (levT E T N).subtype).coprod (diagUnits E))
    ((MonoidHom.coprod ψ.1 ((kap E a).comp (levT E T N).subtype)).coprod 1) (by
      rintro ⟨⟨b, u, hu⟩, k⟩ h
      change ideleMap (maximalRealSubfield E) E b * u * diagUnits E k = 1 at h
      change ψ.1 b * kap E a u * 1 = 1
      let c := GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.conj (maximalRealSubfield E) E
      have h' := congrArg (ideleConj (maximalRealSubfield E) E) h
      have c1 : ideleConj (maximalRealSubfield E) E (ideleMap _ E b) = ideleMap _ E b :=
        Units.ext (GlobalTheory.UnitaryHeckeBaseChange.adeleConj_adeleMap _)
      have c2 : ideleConj (maximalRealSubfield E) E (diagUnits E k) =
          diagUnits E (Units.map c.toRingEquiv.toRingHom.toMonoidHom k) :=
        GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleConj_principalIdele _ E k
      have c3 : ideleConj (maximalRealSubfield E) E u ∈ levT E T' N := GlobalTheory.T.cmIdeleConj_mem_congruenceUnitIdeles_conj_places E T N u hu
      rw [map_mul, map_mul, map_one, c1, c2, ← h, mul_assoc, mul_assoc, mul_right_inj] at h'
      have h3 : diagUnits E (Units.map c.toRingEquiv.toRingHom.toMonoidHom k / k) =
          u / ideleConj (maximalRealSubfield E) E u := by
        rw [_root_.map_div, div_eq_div_iff_mul_eq_mul, mul_comm, h']
      have h4 := hprin _ (h3 ▸ div_mem (levT_anti E hT'T N hu) c3) fun φ => by
        rw [Units.val_div_eq_div_val, map_div₀, norm_div]
        have : φ (Units.map c.toRingEquiv.toRingHom.toMonoidHom k : Eˣ) = starRingEnd ℂ (φ k) :=
          GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.embedding_conj (maximalRealSubfield E) E φ k
        rw [this, Complex.norm_conj, div_self (by simp)]
      have h5 : IsCMField.complexConj E k = k := congrArg Units.val (div_eq_one.1 h4)
      have h6 : (k : E) ∈ maximalRealSubfield E := (IsCMField.complexConj_eq_self_iff E (k : E)).1 h5
      let k0 : (maximalRealSubfield E)ˣ := Units.mk0 ⟨k, h6⟩ fun h0 => k.ne_zero (congrArg Subtype.val h0)
      have h7 : ideleMap _ E (diagUnits _ k0) = diagUnits E k :=
        (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleMap_principalIdele _ E k0).trans (congrArg (diagUnits E) (Units.ext rfl))
      have h8 : ideleMap _ E (b * diagUnits _ k0) = u⁻¹ := by
        rw [map_mul, h7, eq_inv_iff_mul_eq_one, mul_right_comm, h]
      have h9 := hF _ (h8 ▸ inv_mem hu)
      rw [h8, map_mul, ψ.2.2, mul_one, map_inv] at h9
      rw [h9, inv_mul_cancel, one_mul])
  have hu : ∀ u ∈ levT E T N, ξ u = kap E a u := fun u hu => by
    simpa using hξ ((1, ⟨u, hu⟩), 1)
  let κ : HChar E := ⟨ξ, ?_, fun k => by simpa using hξ ((1, 1), k)⟩
  swap
  · refine continuous_of_continuousAt_one ξ ((continuous_kap E a).continuousAt.congr ?_)
    filter_upwards [levT_mem_nhds E T (N := N) (by omega)] with x hx
    exact (hu x hx).symm
  have hloc : ∀ w, w ∉ T → κ.UnrAt w := by
    intro w hw x hx
    have hmem : localIdele E w x ∈ levT E T N := by
      refine ⟨fun v => ?_, fun v hv => ?_⟩
      · by_cases hvw : v = w
        · subst hvw
          rw [GlobalTheory.HeckeProduct.localIdele_snd_self]
          exact hx
        · rw [GlobalTheory.HeckeProduct.localIdele_snd_ne E w v hvw]
          exact map_one _
      · have hvw : v ≠ w := fun e => hw (e ▸ hv)
        rw [GlobalTheory.HeckeProduct.localIdele_snd_ne E w v hvw]
        show Valued.v ((1 : v.adicCompletion E) - 1) ≤ _
        rw [sub_self, map_zero]
        exact zero_le
    show ξ (localIdele E w x) = 1
    rw [hu _ hmem]
    apply Units.ext
    rw [kap_of_fst a _ (1 : E) (by rw [GlobalTheory.HeckeProduct.localIdele_fst, map_one])]
    simp
  refine ⟨κ, fun φ => if (InfinitePlace.mk φ).embedding = φ then a else 0, fun k => ?_,
    Subtype.ext (MonoidHom.ext fun b => ?_), hloc w₀ fun h => h.2 rfl, fun w hw => hloc w fun h => hw h.1⟩
  · have h1 : infDiag k ∈ levT E T N := by
      refine lev_le_levT E T N ⟨fun v => ?_, fun v => ?_⟩
      · rw [coe_infDiag']
        exact map_one _
      · rw [coe_infDiag']
        show Valued.v ((1 : v.adicCompletion E) - 1) ≤ _
        rw [sub_self, map_zero]
        exact zero_le
    change ((ξ (infDiag k) : ℂˣ) : ℂ) = _
    rw [hu _ h1, kap_of_fst a _ (k : E) (by rw [coe_infDiag']), prod_type]
  · change ξ (ideleMap _ E b) = ψ.1 b
    simpa using hξ ((b, 1), 1)
end
end

section

open CategoryTheory AlgebraicGeometry KaehlerDifferential GlobalTheory GlobalTheory.PD ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PD.XCover

theorem _root_.GlobalTheory.T.algebraicIndependent_pulledBackProjCoordinateRatios : ∀ (d : ℕ) (Z : Scheme.{0}) [IsIntegral Z] (p : Z ⟶ Sp ℂ) [SmoothOfRelativeDimension d p] [inst : Algebra ℂ Z.functionField], inst = ffAlg p → ∀ (φ : Z ⟶ PSpace ℂ d) [IsFinite φ], φ ≫ PSpace.str ℂ d = p → (∀ i, genericPoint Z ∈ φ ⁻¹ᵁ chart d i) → AlgebraicIndependent ℂ (fun j : Fin d => rat φ 0 j.succ) := by
  first | (exact @GlobalTheory.PD.XCover.algebraicIndependent_rat) | (exact GlobalTheory.PD.XCover.algebraicIndependent_rat) | (intros; apply GlobalTheory.PD.XCover.algebraicIndependent_rat  <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry KaehlerDifferential GlobalTheory GlobalTheory.PD ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PD.XCover

theorem _root_.GlobalTheory.T.finite_projection_function_field : ∀ (d : ℕ) (Z : Scheme.{0}) [IsIntegral Z] (p : Z ⟶ Sp ℂ) [SmoothOfRelativeDimension d p] [inst : Algebra ℂ Z.functionField], inst = ffAlg p → ∀ (φ : Z ⟶ PSpace ℂ d) [IsFinite φ], φ ≫ PSpace.str ℂ d = p → (∀ i, genericPoint Z ∈ φ ⁻¹ᵁ chart d i) → FiniteDimensional (fld φ) Z.functionField := by
  first | (exact @GlobalTheory.PD.XCover.finiteDimensional_fld) | (exact GlobalTheory.PD.XCover.finiteDimensional_fld) | (intros; apply GlobalTheory.PD.XCover.finiteDimensional_fld  <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry KaehlerDifferential GlobalTheory GlobalTheory.PD GlobalTheory.CechDR GlobalTheory.HodgeCoh ReciprocityTheory.ChartRestriction.G.Geo.Tor

set_option autoImplicit false

namespace GlobalTheory.HodgeCoh

theorem formGermI_res : ∀ (Z : Scheme.{0}) [IsIntegral Z] (p : Z ⟶ Sp ℂ),
    letI := algΓ p
    ∀ [inst : Algebra ℂ Z.functionField] (hinst : inst = ffAlg p) (j : ℕ) (V V' : Z.Opens)
      (hV : IsAffineOpen V) (hV' : IsAffineOpen V') (hη : genericPoint Z ∈ V) (hη' : genericPoint Z ∈ V')
      (h : V' ≤ V) (y : sectionsOn (Omega p j) V),
      formGermI p j hV' hη' hinst (sectionsOn.res ℂ (Omega p j) h y) = formGermI p j hV hη hinst y := by
  intro Z _ p
  letI := algΓ p
  intro inst hinst j V V' hV hV' hη hη' h y
  subst hinst
  letI := ffAlg p
  have key : (toOmEquiv p j hV').symm (sectionsOn.toΓ _ _ (sectionsOn.res ℂ (Omega p j) h y)) =
      formRes p h j ((toOmEquiv p j hV).symm (sectionsOn.toΓ _ _ y)) := by
    apply (toOmEquiv p j hV').injective
    rw [LinearEquiv.apply_symm_apply, toOmEquiv_apply, ← res_toOm, ← toOmEquiv_apply p j hV,
      LinearEquiv.apply_symm_apply, sectionsOn.toΓ_res]
  change (semiHom_germSec p hη').mDR
      ((toOmEquiv p j hV').symm (sectionsOn.toΓ _ _ (sectionsOn.res ℂ (Omega p j) h y)) : DR ℂ (Sec p V')) =
    (semiHom_germSec p hη).mDR ((toOmEquiv p j hV).symm (sectionsOn.toΓ _ _ y) : DR ℂ (Sec p V))
  rw [key]
  exact congrArg Subtype.val (SemiHom.mOm_mOm (SemiHom.of_algHom (Sec.res p h)) (semiHom_germSec p hη')
    (semiHom_germSec p hη) (fun b ↦ by
      change (Z.presheaf.germ V' (genericPoint Z) hη').hom ((Z.presheaf.map (homOfLE h).op).hom b) =
        (Z.presheaf.germ V (genericPoint Z) hη).hom b
      exact congrArg (fun f ↦ f.hom (show Γ(Z, V) from b))
        (TopCat.Presheaf.germ_res Z.presheaf (homOfLE h) (genericPoint Z) hη')) _)

end GlobalTheory.HodgeCoh
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.Published GlobalTheory.AboveL

theorem _root_.GlobalTheory.T.exists_unique_splitPlaceComponent_definiteUnitary : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a : ℕ) (U : Submodule ℂ (UA E a → ℂ)), IsAutRepU U → ∀ w : HeightOneSpectrum (𝓞 E), IsSplitAt w → (∃ σ : SmIrr (GL (Fin a) (w.adicCompletion E)), IsCompAlong U (locU a w) ((cLoc w).comp (locU a w).subtype) σ.ρ) ∧ ∀ σ σ' : SmIrr (GL (Fin a) (w.adicCompletion E)), IsCompAlong U (locU a w) ((cLoc w).comp (locU a w).subtype) σ.ρ → IsCompAlong U (locU a w) ((cLoc w).comp (locU a w).subtype) σ'.ρ → Nonempty (σ.ρ.Equiv σ'.ρ) := by
  first | (exact @GlobalTheory.SplitComp.exists_comp_and_unique) | (exact GlobalTheory.SplitComp.exists_comp_and_unique) | (intros; apply GlobalTheory.SplitComp.exists_comp_and_unique  <;> assumption)
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU GlobalTheory.CuspRep GlobalTheory.PRep

theorem _root_.GlobalTheory.T.conjugates_automorphicForm_span_finiteDimensional : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (φ : UA E n → ℂ), IsAutFormU φ → ∃ M : Submodule ℂ (UA E n → ℂ), FiniteDimensional ℂ M ∧ ∀ (σ : ℂ ≃+* ℂ) (φ' : UA E n → ℂ), IsAutFormU φ' → (∀ g ∈ finU (E := E) (n := n), φ' g = σ (φ g)) → φ' ∈ M := by
  first | exact @GlobalTheory.ConjSpan.conj_span_finite | exact GlobalTheory.ConjSpan.conj_span_finite | (intros; apply GlobalTheory.ConjSpan.conj_span_finite; all_goals assumption)
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU GlobalTheory.CuspRep GlobalTheory.PRep

theorem _root_.GlobalTheory.T.exists_localComponent_eigenvector_splitPlace : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (U : Submodule ℂ (UA E n → ℂ)), IsAutRepU U → ∀ w, IsSplitAt w → ∀ (J : Subgroup (GL (Fin n) (w.adicCompletion E))), IsOpen (J : Set (GL (Fin n) (w.adicCompletion E))) → IsCompact (J : Set (GL (Fin n) (w.adicCompletion E))) → ∀ (χ : J →* ℂˣ) (φ : UA E n → ℂ), φ ∈ U → φ ≠ 0 → (∀ x ∈ locU n w, ∀ hx : cLoc w x ∈ J, RU E n x φ = (χ ⟨_, hx⟩ : ℂ) • φ) → ∃ σ : SmIrr (GL (Fin n) (w.adicCompletion E)), IsCompAlong U (locU n w) ((cLoc w).comp (locU n w).subtype) σ.ρ ∧ ∃ v : σ.V, v ≠ 0 ∧ ∀ g : J, σ.ρ g v = (χ g : ℂ) • v := by
  first | (exact @GlobalTheory.SplitEigen.exists_locComp_eigen) | (exact GlobalTheory.SplitEigen.exists_locComp_eigen) | (intros; apply GlobalTheory.SplitEigen.exists_locComp_eigen  <;> assumption)
end
