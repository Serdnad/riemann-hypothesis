module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsUnitarisableTrivChar
public import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.Narrow
public import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.NarrowAsc
public import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.NarrowSpeh
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.Bundle010
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.AbsGood
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle021
public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.OrdinaryHeckeAlgebraIntegral
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle009
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle051
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LaArith
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.ResidueFlagPoints.CycIne
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.ResidueFlagPoints.Bundle001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.Bundle007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.TaylorWilesObstructionBound
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle021
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.IsAlgClosureField

@[expose] public section

section




section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace UpperTheory.BaseChangeIdentities
theorem bcSpeh_alt : DefiniteN → GlobalTheory.BcSpeh.BcSpeh :=
  fun h => bcSpeh_of ascComp h
end UpperTheory.BaseChangeIdentities
end
end
end

section




section
noncomputable section
open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp IsLocalRing UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Af
namespace UpperTheory.V.Pr
section
variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l}
  {η : G ℚ Ω →* ℤˣ} {Ψ : G ℚ Ω →* c.Oˣ} {σ g₁ : G ℚ Ω} {B : ValuationSubring Ω} {M : ℕ}
  {L : Type} [Field L] [NumberField L] [IsCMField L] [Algebra L Ω] [IsAlgClosure L Ω] {Φ : Fr.Frame l (ResidueField c.O)}
end
def SeedPtOfAlt : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (c : Coef l)
    [CharP (ResidueField c.O) l] (N : ℕ) [NeZero N] (e : ℕ) (ψ : DirichletCharacter c.O N)
    (η : G ℚ Ω →* ℤˣ) (σ g₁ : G ℚ Ω) (B : ValuationSubring Ω) (M : ℕ), LinkHyp c N e η σ B M →
    ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] [Algebra L Ω] [IsAlgClosure L Ω] (Φ : Fr.Frame l (ResidueField c.O))
    (k : GalLink η (Chr.Psi l e (Chr.dirG ℚ Ω ψ)) σ g₁ B M L Φ)
    (c₁ : Coef l) [Fr.IsCoef l c₁.O] (f : ResidueField c.O →+* ResidueField c₁.O) (n : ℕ)
    (ka : G L Ω →* (Qbar l)ˣ) (R : CReal k c₁ f n ka), IsKa σ M ι n ka → ∀ (χ' : G ℚ Ω →* (Qbar l)ˣ) (j : ℕ), ¬ l ∣ orderOf χ' →
    (∀ s, ‖((cycBar ℚ Ω l ^ j * χ') s).val - (Chr.Psi l e (Chr.dirG ℚ Ω ψ) s).val.1‖ < 1) →
    ∀ (m : ℕ), 2 ≤ m → ∀ r : G L Ω →* GL (Fin n) (Qbar l),
    _root_.UpperTheory.V.Sd.IsSeedAlt ι σ (fun i => ((cycBar ℚ Ω l ^ j * χ') ^ Fr.w n i).comp (galEmb ℚ L Ω))
      (fun i => (χ' ^ Fr.w n i).comp (galEmb ℚ L Ω)) (fun i => m * Fr.w n i) ka r →
    ∀ J, R.B₀.PointTheoremBaseObject ι J → R.T.IdealSpecializationPoint J
end UpperTheory.V.Pr
end
end
end

section

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp IsLocalRing UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Af UpperTheory.V.Alg
open UpperTheory.V.W UpperTheory.V.Pr
namespace UpperTheory.V.J
section U
variable {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
  {s : HidaSetting l L Ω} {V : s.Lev} {c : Coef l} {n : ℕ} {r : Resid V.frame c.O n} {B : UniversalOrdinaryDeterminantRing r}
end U
def ModNAlt : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
    (s : HidaSetting l L Ω) (V : s.Lev), V.S' = s.S → (¬ ∃ ζ : L, IsPrimitiveRoot ζ l) →
    ∀ (c : Coef l), Large L c → ∀ (r : Resid V.frame c.O 3), r.V0ok → ∀ (B : UniversalOrdinaryDeterminantRing r) (Λ : LamObj r) (ι : Qbar l ≃+* ℂ),
      ∃ J : Ideal B.B, B.ModularAlt ι J Λ ∧ Num B Λ J
def IrrOpenAlt : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
    (s : HidaSetting l L Ω) (V : s.Lev) (c : Coef l) (n : ℕ) (r : Resid V.frame c.O n) (B : UniversalOrdinaryDeterminantRing r) (ι : Qbar l ≃+* ℂ)
    (J : Ideal B.B), 1 ≤ n → B.arithmeticPointPurityDense ι J → ∀ x : B.Pt, IrrPt x →
    ∃ b₀ : B.B, x b₀ ≠ 0 ∧ ∀ (y : B.Pt) (w : s.Wt n), J ≤ RingHom.ker y → y.Good w → y b₀ ≠ 0 → IrrPt y
def UnramifiedEndsStatement : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
    (s : HidaSetting l L Ω) (V : s.Lev) (c : Coef l) (n : ℕ) (r : Resid V.frame c.O n) (B : UniversalOrdinaryDeterminantRing r) (Λ : LamObj r)
    (ι : Qbar l ≃+* ℂ) (J : Ideal B.B) (m : ℕ), 1 ≤ n → Nonempty (Λ.Λ ≃ₐ[c.O] MvPowerSeries (Fin m) c.O) →
    B.Dense J → B.arithmeticPointPurityDense ι J → Num B Λ J → UnrAt B J
section Pt
variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l}
  {η : G ℚ Ω →* ℤˣ} {Ψ : G ℚ Ω →* c.Oˣ} {σ g₁ : G ℚ Ω} {B : ValuationSubring Ω} {M : ℕ}
  {L : Type} [Field L] [NumberField L] [IsCMField L] [Algebra L Ω] [IsAlgClosure L Ω] {Φ : Fr.Frame l (ResidueField c.O)}
  {k : GalLink η Ψ σ g₁ B M L Φ} {c₁ : Coef l} [Fr.IsCoef l c₁.O] {f : ResidueField c.O →+* ResidueField c₁.O} {n : ℕ}
  {ka : G L Ω →* (Qbar l)ˣ} (R : CReal k c₁ f n ka) (φ : R.B₀.B →ₐ[c₁.O] R.S.B) (ξ : R.S.R →ₐ[c₁.O] c₁.O)
end Pt
end UpperTheory.V.J
end
end
end

section




section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.CuspRep GlobalTheory.GalOfCusp
attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing UpperTheory.V.Pr.IsCD.complete in
theorem UpperTheory.V.Ws.Pt.point_representation_weights :
    _root_.UpperTheory.V.Af.HypothesesH' → ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : W.HidaSetting l L Ω) (V : s.Lev) (c : Coef l) (n : ℕ) (r : W.Resid V.frame c.O n) (B : W.UniversalOrdinaryDeterminantRing r) (ι : PadicAlgCl l ≃+* ℂ) (J : Ideal B.B), B.PointTheoremBaseObject ι J → ∀ (x : B.Pt) (ρ : G L Ω →* GL (Fin n) (PadicAlgCl l)) (m : W.Vl l L → Fin n → ℤ), 2 ≤ n → n ≤ 4 → x.IsRep ρ → Continuous ρ → _root_.UpperTheory.V.Z.Win.IsAutCsdA ι ρ → (∀ g ∈ Ine (F := L) (s.A s.v0), ρ g = 1) → (∀ v i j, i < j → m v j + 2 ≤ m v i) → (∀ v : W.Vl l L, W.HasFlag (ρ.comp (Dec (F := L) (s.A v)).subtype) (x.psi v)) → (∃ k : ℕ, 0 < k ∧ ∀ (v : W.Vl l L) i (g : Dec (F := L) (s.A v)), (g : G L Ω) ∈ Ine (F := L) (s.A v) → (x.psi v i g * cycBar L Ω l g ^ (-m v i)) ^ k = 1) → J ≤ RingHom.ker x := by
  intro hP l _ L Ω _ _ _ _ _ _ s V c n r B ι J hJ x ρ m hn2 hn4 hrep hc haut hv0 hm hfl ⟨k, hk, hw⟩
  have hov : ∀ v : W.Vl l L, (s.A v).valuation (l : Ω) < 1 := fun v => by
    simpa using (s.hA v _).2 v.2
  have hl : ∀ v : W.Vl l L, ((l : ℕ) : 𝓞 L) ∈ (s.w v).asIdeal := fun v => by
    refine (s.hw v _).1 ?_
    simpa using hov v
  refine hJ x (fun v j _ => -m v j) ρ hn2 hn4 ⟨fun v τ i j hij => ?_, fun v j => ?_⟩
    hrep hc haut hv0
    fun v => ⟨hfl v, fun i j hij => ?_⟩
  · have := hm v i j hij
    simp only
    omega
  · exact UpperTheory.V.Loc.laArith hP.toClassicalTheorems.litN.aut.art (s.hw v) (hl v) _ (psi_cont x v j) (m v j) k hk (hw v j)
  · have hne : 1 - m v i + m v j ≠ 0 := by
      rcases lt_trichotomy i j with h | h | h
      · have := hm v i j h
        omega
      · subst h
        omega
      · have := hm v j i h
        omega
    obtain ⟨g, hg, hg1⟩ := cycIne L Ω l (s.A v) (hov v) ((1 - m v i + m v j) * k)
      (mul_ne_zero hne (by exact_mod_cast hk.ne'))
    have hgD : g ∈ Dec (F := L) (s.A v) :=
      (GlobalTheory.WeilDeligne.Weil_le_Dec (s.hw v)) (GlobalTheory.WeilDeligne.ineIncl (s.hw v) ⟨g, hg⟩).2
    have h1 := hw v i ⟨g, hgD⟩ hg
    have h2 := hw v j ⟨g, hgD⟩ hg
    have e : x.psi v i ⟨g, hgD⟩ = x.psi v j ⟨g, hgD⟩ * cycBar L Ω l g := by
      rw [hij]; rfl
    apply hg1
    have e2 : x.psi v i ⟨g, hgD⟩ * cycBar L Ω l g ^ (-m v i) =
        (x.psi v j ⟨g, hgD⟩ * cycBar L Ω l g ^ (-m v j)) * cycBar L Ω l g ^ (1 - m v i + m v j) := by
      rw [e, mul_assoc, mul_assoc, ← zpow_add, ← zpow_one_add]
      congr 2
      ring
    change (x.psi v i ⟨g, hgD⟩ * cycBar L Ω l g ^ (-m v i)) ^ k = 1 at h1
    change (x.psi v j ⟨g, hgD⟩ * cycBar L Ω l g ^ (-m v j)) ^ k = 1 at h2
    rw [e2, mul_pow, h2, one_mul] at h1
    rw [zpow_mul, zpow_natCast, h1]
end
end

section




section
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement
open GlobalTheory.CuspRep GlobalTheory.GalOfCusp
namespace UpperTheory.V.Ws
variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} {D : Raw Ω c}
namespace Link
variable {T : Tower D} {c' : Coef l} {h : c.O ≤ c'.O} (K : Link T c' h) (X : Space (T.fr ∅) (inc h))
end Link
structure UnramifiedInputs : Prop where
  coh : CohomologyHyp
  pr : _root_.UpperTheory.V.Af.HypothesesH'
  modU : _root_.UpperTheory.V.W.ModUAlt
  lev : W.LevEx
  lam : W.LamEx
  b0 : W.ProModularRingExists
end UpperTheory.V.Ws
end
end
end

section




section
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.HV GlobalTheory.GalOfCusp
namespace UpperTheory.V.W
def HidaUAlt : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
    (s : HidaSetting l L Ω) (V : s.Lev), V.S' = s.S → (¬ ∃ ζ : L, IsPrimitiveRoot ζ l) →
    ∀ (c : Coef l), Large L c → ∀ (n : ℕ), 1 ≤ n → ∀ (r : Resid (HidaSetting.Lev.frame V) c.O n) (B : UniversalOrdinaryDeterminantRing r) (Λ : LamObj r) (ι : Qbar l ≃+* ℂ),
      ∃ J : Ideal B.B, B.HidaPropsAlt ι J Λ ∧ _root_.UpperTheory.V.Pa.HasAut B J
end UpperTheory.V.W
end
end
end

section




section
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.Pa.Lev
open UpperTheory.V.HV GlobalTheory.GalOfCusp
namespace UpperTheory.V.Th
variable {l : ℕ} [Fact l.Prime]
section Pt
variable {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] {n : ℕ}
variable {L : Loc} {G G0 : Glob l L} (h : G.Hom G0) (y : Pt G0.frame O n) (m : ℕ)
variable (T : TWGrp G0)
end Pt
section Mod
variable {L : Loc} {G0 : Glob l L} {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] {n : ℕ}
  {r : Resid G0.frame O n} {B : Type} [CommRing B] [Algebra O B] [IsCO O B] {u : Pair r B} {J : Ideal B} {D : ℕ}
  (b : TWBase u J Empty D) (x : B →ₐ[O] O)
variable {b} {G : Glob l L} {h : G.Hom G0} {q N : ℕ} (A : OpMod b h q N) (Nq : Fin q → ℕ) (ph ta : Fin q → G.G₀) (E : ℕ)
end Mod
section Bar
variable (F : GFrame l) {n : ℕ} (O : Type) [CommRing O] [Algebra ℤ_[l] O] [Algebra O (Qbar l)]
  (ρ : F.G₀ →* GL (Fin n) (Qbar l)) (P : GL (Fin n) (Qbar l))
end Bar
section Ar
variable {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
  {s : HidaSetting l L Ω} {V0 : s.Lev}
def LevelAtOrdinaryDeterminantRing {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] {n : ℕ} {r : Resid V0.frame O n} {B : UniversalOrdinaryDeterminantRing r}
    {J : Ideal B.B} {D : ℕ} (b : TWBase (pairOf B.u) J Empty D) : Prop :=
  ∀ (V : s.Lev) (h : (globOf r V).Hom (globOf r V0)) (q : ℕ) (v : Fin q → Plc (Lp L)) (w : Fin q → Plc L)
    (Bq : Fin q → ValuationSubring Ω), (∀ g, h.p (toGS Ω V.S' g) = toGS Ω V0.S' g) → Function.Injective v → (∀ j, v j ∉ s.S) →
    V.S' = s.S ∪ Set.range v → (∀ j, IsPlaceOver (Bq j) (w j)) → (∀ j, IsPlaceOver (Bq j) (v j)) →
    (∀ j, Dec (F := Lp L) (Bq j) ≤ (resP L Ω).range) → ∃ A : LevMod b h w, A.ClassicalAlt
variable {c : Coef l} {n : ℕ} {r : Resid V0.frame c.O n} (B : UniversalOrdinaryDeterminantRing r)
def LevelIdealCondition (J : Ideal B.B) : Prop :=
  ∃ b : TWBase (pairOf B.u) J Empty (n * Module.finrank ℚ (Lp L)), _root_.UpperTheory.V.Th.LevelAtOrdinaryDeterminantRing b ∧ (∀ k, b.wt.γ k ∈ V0.frame.Iv (b.wt.v k)) ∧
    ∀ (x : B.B →ₐ[c.O] c.O) (h : s.Wt n), (barPt B x).Arith h → CtrlH b x
end Ar
def HidaFamilyCondition : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
    (s : HidaSetting l L Ω) (V : s.Lev), V.S' = s.S → ∀ (c : Coef l) (n : ℕ), 1 ≤ n →
    ∀ (r : Resid V.frame c.O n) (B : UniversalOrdinaryDeterminantRing r) (Λ : LamObj r) (ι : Qbar l ≃+* ℂ), ∃ J : Ideal B.B, B.PointTheoremBaseObject ι J ∧ _root_.UpperTheory.V.Th.LevelIdealCondition B J
def HasHeckeOperatorDense : Prop :=
  _root_.UpperTheory.V.Pa.LocPAlt → ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
    (s : HidaSetting l L Ω) (V0 : s.Lev) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O]
    [Algebra ℤ_[l] O] (n : ℕ) (r : Resid V0.frame O n) (B : UniversalOrdinaryDeterminantRing r) (J : Ideal B.B) (D : ℕ)
    (b : TWBase (pairOf B.u) J Empty D), _root_.UpperTheory.V.Th.LevelAtOrdinaryDeterminantRing b → ∀ T : TWGrp (globOf r V0), TWPl r T → OpAt b T
def OrdinaryMainCase : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
    (s : HidaSetting l L Ω) (V0 : s.Lev) (c : Coef l) (n : ℕ) (r : Resid V0.frame c.O n) (B : UniversalOrdinaryDeterminantRing r) (J : Ideal B.B)
    (y : Pt (globOf r V0).frame c.O n) (x : B.B →ₐ[c.O] c.O) (h : s.Wt n) (q : ℕ) (sg : Fin q → V0.frame.G₀)
    (al : Fin q → Fin n → c.O), V0.S' = s.S → 1 ≤ n → _root_.UpperTheory.V.Th.LevelIdealCondition B J → J ≤ RingHom.ker x → (barPt B x).Arith h →
    B.u.Maps x.toRingHom (GDet.ofRep (mat y.ρ)) y.ψ → y.N4 V0.frame.D0 →
    (∀ j, sg j ∈ V0.frame.G' ∧ Function.Injective (al j) ∧
      (mat y.ρ (sg j)).charpoly = ∏ i, (Polynomial.X - Polynomial.C (al j i))) →
    DetQ (globOf r V0).frame c.O (pushRep (algebraMap c.O (Qbar l)) y.ρ)
      (GeneralLinearGroup.map (algebraMap c.O (Qbar l)) y.P) (Set.range sg) →
    ∀ δ : B.B →ₗ[c.O] c.O, IsDer x δ → (∀ v i, ∀ g ∈ V0.frame.Iv v, δ (B.u.ψ v i g : B.Bˣ) = 0) →
      ∀ g, δ (B.u.D.tr (MonoidAlgebra.single g 1)) = 0
end UpperTheory.V.Th
end
end
end
