module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle792
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsAdelicUnitaryTrivialOutsideSplitPlaceLocEq
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEqColGenMulBlkU
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegralMulConjEqOfLintegral
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle018
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle067
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle068
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle262
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParIndJacPlacing
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle007
import Development.AbelianVarietyTheory.Definitions.Divisors.LineOppositeParabolicUnitaryLeviSectionEq
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle648
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle738
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle787
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle394
import GroundTheory.GlobalFields.LocalFieldAtPlace
import GroundTheory.LocalFields.PadicLogSeries
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle797
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGlobalIntegerCongrTameGeneratorCharacter
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineExtensionClassBound
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
import Mathlib.FieldTheory.Galois.Profinite
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
import Formalism.LocalToGlobal.HilbertRowConditions.CenterIdempotentAction
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle003
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle008
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle007
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle022
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle016
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle021
import Formalism.AlgebraicWeights.IsAlgWeight
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
import Formalism.LocalToGlobal.PairingIndexBounds.ModelLatticeMoves.IsBichar
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import ReciprocityTheory.Automorphisms.PlaceA

@[expose] public section

section

open NumberField IsDedekindDomain ReciprocityTheory.Aut Formalism.AUTREP Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2 Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev GlobalTheory.TypeRec GlobalTheory.TypeVec
attribute [local instance] GlobalTheory.TypeRec.factG Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.TypeAct

section General

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

theorem trivOutside_mul {T : Set (HeightOneSpectrum (𝓞 (maximalRealSubfield L)))} {x y : GAf L n}
    (hx : TrivOutside T x) (hy : TrivOutside T y) : TrivOutside T (x * y) := by
  intro v hv
  show (((x.1 * y.1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L))).map (compAt L v) = 1
  rw [Units.val_mul, Matrix.map_mul, hx v hv, hy v hv, Matrix.one_mul]

theorem trivOutside_inv {T : Set (HeightOneSpectrum (𝓞 (maximalRealSubfield L)))} {x : GAf L n}
    (hx : TrivOutside T x) : TrivOutside T x⁻¹ := by
  intro v hv
  have e : (((x⁻¹ : GAf L n).1 : Matrix (Fin n) (Fin n) (AL L))).map (compAt L v) *
      ((x.1 : Matrix (Fin n) (Fin n) (AL L))).map (compAt L v) = 1 := by
    rw [← Matrix.map_mul]
    have : ((x⁻¹ : GAf L n).1 : Matrix (Fin n) (Fin n) (AL L)) * (x.1 : Matrix (Fin n) (Fin n) (AL L)) = 1 := by
      rw [← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel]; rfl
    rw [this, Matrix.map_one _ (map_zero _) (map_one _)]
  rwa [hx v hv, Matrix.mul_one] at e

theorem commute_of_ne {v w : HeightOneSpectrum (𝓞 (maximalRealSubfield L))} (hvw : v ≠ w) {x y : GAf L n}
    (hx : TrivOutside {v} x) (hy : TrivOutside {w} y) : Commute x y := by
  show x * y = y * x
  apply Subtype.ext; apply Units.ext
  show (x.1 : Matrix (Fin n) (Fin n) (AL L)) * y.1 = (y.1 : Matrix (Fin n) (Fin n) (AL L)) * x.1
  ext i k
  rw [← sub_eq_zero]
  apply GlobalTheory.InertUmax.eq_zero_of_compAt L
  intro u
  rw [map_sub, sub_eq_zero]
  have hmx : ∀ A B : Matrix (Fin n) (Fin n) (AL L),
      compAt L u ((A * B) i k) = (A.map (compAt L u) * B.map (compAt L u)) i k := by
    intro A B; rw [← Matrix.map_mul]; rfl
  rw [hmx, hmx]
  by_cases hu : u = v
  · subst hu
    rw [hy u (by simpa using hvw), mul_one, one_mul]
  · rw [hx u (by simpa using hu), mul_one, one_mul]

variable {g : ℕ} [Fact g.Prime]

theorem isLiftAt_mul {s : SplitPlace L} {j : ℚ_[g] ≃+* s.v.adicCompletion (maximalRealSubfield L)}
    {y y' : GL (Fin n) ℤ_[g]} {x x' : GAf L n} (h : IsLiftAt s j y x) (h' : IsLiftAt s j y' x') :
    IsLiftAt s j (y * y') (x * x') :=
  ⟨trivOutside_mul h.1 h'.1, by rw [map_mul, h.2, h'.2, map_mul, map_mul]⟩

theorem isLiftAt_inv {s : SplitPlace L} {j : ℚ_[g] ≃+* s.v.adicCompletion (maximalRealSubfield L)}
    {y : GL (Fin n) ℤ_[g]} {x : GAf L n} (h : IsLiftAt s j y x) : IsLiftAt s j y⁻¹ x⁻¹ :=
  ⟨trivOutside_inv h.1, by rw [map_inv, h.2, map_inv, map_inv]⟩

theorem exists_isLiftAt (s : SplitPlace L) (j : ℚ_[g] ≃+* s.v.adicCompletion (maximalRealSubfield L))
    (y : GL (Fin n) ℤ_[g]) : ∃ x : GAf L n, IsLiftAt s j y x :=
  GlobalTheory.SplitLift.exists_trivOutside_loc_eq n s _

end General

section Fix

variable (D : D7) (s : ∀ k : Fin 2, D.nd.PlG k → SplitPlace D.host.E)
    (j : ∀ k v, ℚ_[D.host.g k] ≃+* (s k v).v.adicCompletion (maximalRealSubfield D.host.E))
    {A : Type} [AddCommGroup A] [Module ℂ A] (ρA : GAf D.host.E D.R.r →* Module.End ℂ A)

theorem fix_of_mem {z : A} (hz : z ∈ KFix D s j ρA) {k : Fin 2} {v : D.nd.PlG k} {y : GL (Fin D.R.r) ℤ_[D.host.g k]}
    {x : GAf D.host.E D.R.r} (hl : IsLiftAt (s k v) (j k v) y x) (hy : GlobalTheory.GLp.red (D.host.g k) D.R.r y = 1) :
    ρA x z = z := by
  simp only [KFix, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply,
    sub_eq_zero] at hz
  exact hz k v ⟨y, hy⟩ x hl

theorem eq_of_red_eq {z : A} (hz : z ∈ KFix D s j ρA) {k : Fin 2} {v : D.nd.PlG k}
    {y y' : GL (Fin D.R.r) ℤ_[D.host.g k]} {x x' : GAf D.host.E D.R.r} (hl : IsLiftAt (s k v) (j k v) y x)
    (hl' : IsLiftAt (s k v) (j k v) y' x')
    (he : GlobalTheory.GLp.red (D.host.g k) D.R.r y = GlobalTheory.GLp.red (D.host.g k) D.R.r y') : ρA x z = ρA x' z := by
  have h1 := fix_of_mem D s j ρA hz (isLiftAt_mul (isLiftAt_inv hl) hl') (by rw [map_mul, map_inv, he, inv_mul_cancel])
  symm
  calc ρA x' z = ρA x (ρA (x⁻¹ * x') z) := by rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left]
    _ = ρA x z := by rw [h1]

variable {D s j}

theorem map_mem (hinj : Function.Injective (fun kv : (Σ k : Fin 2, D.nd.PlG k) => (s kv.1 kv.2).v))
    {z : A} (hz : z ∈ KFix D s j ρA) {k : Fin 2} {v : D.nd.PlG k} {y : GL (Fin D.R.r) ℤ_[D.host.g k]}
    {x : GAf D.host.E D.R.r} (hl : IsLiftAt (s k v) (j k v) y x) : ρA x z ∈ KFix D s j ρA := by
  simp only [KFix, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply,
    sub_eq_zero]
  rintro k' v' ⟨y', hy'⟩ x' hl'
  by_cases h : (⟨k', v'⟩ : Σ k : Fin 2, D.nd.PlG k) = ⟨k, v⟩
  · obtain ⟨rfl, hv⟩ := Sigma.mk.inj_iff.mp h
    cases eq_of_heq hv
    have h1 := fix_of_mem D s j ρA hz (isLiftAt_mul (isLiftAt_mul (isLiftAt_inv hl) hl') hl)
      (by rw [map_mul, map_mul, map_inv, hy', mul_one, inv_mul_cancel])
    rw [← Module.End.mul_apply, ← map_mul]
    conv_rhs => rw [← h1]
    rw [← Module.End.mul_apply, ← map_mul]
    simp only [mul_assoc, mul_inv_cancel_left]
  · have hne : (s k' v').v ≠ (s k v).v := fun e => h (hinj e)
    rw [← Module.End.mul_apply, ← map_mul, (commute_of_ne hne hl'.1 hl.1).eq, map_mul, Module.End.mul_apply,
      fix_of_mem D s j ρA hz hl' hy']

variable (D s j)

def liftAt (k : Fin 2) (v : D.nd.PlG k) (h : GL (Fin D.R.r) (ZMod (D.host.g k))) : GAf D.host.E D.R.r :=
  Classical.choose (exists_isLiftAt (n := D.R.r) (s k v) (j k v)
    (Function.surjInv (GlobalTheory.GLp.Model.red_surjective (g := D.host.g k) D.R.r) h))

theorem isLiftAt_liftAt (k : Fin 2) (v : D.nd.PlG k) (h : GL (Fin D.R.r) (ZMod (D.host.g k))) :
    IsLiftAt (s k v) (j k v) (Function.surjInv (GlobalTheory.GLp.Model.red_surjective (g := D.host.g k) D.R.r) h)
      (liftAt D s j k v h) :=
  Classical.choose_spec (exists_isLiftAt (n := D.R.r) (s k v) (j k v) _)

theorem red_surjInv (k : Fin 2) (h : GL (Fin D.R.r) (ZMod (D.host.g k))) :
    GlobalTheory.GLp.red (D.host.g k) D.R.r (Function.surjInv (GlobalTheory.GLp.Model.red_surjective (g := D.host.g k) D.R.r) h) = h :=
  Function.surjInv_eq _ h

theorem liftAt_apply {z : A} (hz : z ∈ KFix D s j ρA) {k : Fin 2} {v : D.nd.PlG k} {y : GL (Fin D.R.r) ℤ_[D.host.g k]}
    {x : GAf D.host.E D.R.r} (hl : IsLiftAt (s k v) (j k v) y x) :
    ρA (liftAt D s j k v (GlobalTheory.GLp.red (D.host.g k) D.R.r y)) z = ρA x z :=
  eq_of_red_eq D s j ρA hz (isLiftAt_liftAt D s j k v _) hl (red_surjInv D k _)

def factAct (hinj : Function.Injective (fun kv : (Σ k : Fin 2, D.nd.PlG k) => (s kv.1 kv.2).v)) (k : Fin 2)
    (v : D.nd.PlG k) : GL (Fin D.R.r) (ZMod (D.host.g k)) →* Module.End ℂ (KFix D s j ρA) where
  toFun h := (ρA (liftAt D s j k v h)).restrict (fun z hz => map_mem ρA hinj hz (isLiftAt_liftAt D s j k v h))
  map_one' := by
    apply LinearMap.ext; rintro ⟨z, hz⟩
    apply Subtype.ext
    simp only [LinearMap.restrict_apply, Module.End.one_apply]
    have := eq_of_red_eq D s j ρA hz (isLiftAt_liftAt D s j k v 1) (⟨?_, ?_⟩ : IsLiftAt (s k v) (j k v) 1 1)
      (by rw [red_surjInv, map_one])
    · rw [this, map_one, Module.End.one_apply]
    · intro u _; exact Matrix.map_one _ (map_zero _) (map_one _)
    · rw [map_one, map_one, map_one]
  map_mul' a b := by
    apply LinearMap.ext; rintro ⟨z, hz⟩
    apply Subtype.ext
    simp only [LinearMap.restrict_apply, Module.End.mul_apply]
    rw [eq_of_red_eq D s j ρA hz (isLiftAt_liftAt D s j k v (a * b))
      (isLiftAt_mul (isLiftAt_liftAt D s j k v a) (isLiftAt_liftAt D s j k v b))
      (by rw [red_surjInv, map_mul, red_surjInv, red_surjInv]), map_mul, Module.End.mul_apply]

theorem factAct_apply (hinj : Function.Injective (fun kv : (Σ k : Fin 2, D.nd.PlG k) => (s kv.1 kv.2).v))
    {k : Fin 2} {v : D.nd.PlG k} {y : GL (Fin D.R.r) ℤ_[D.host.g k]} {x : GAf D.host.E D.R.r}
    (hl : IsLiftAt (s k v) (j k v) y x) (z : KFix D s j ρA) :
    ((factAct D s j ρA hinj k v (GlobalTheory.GLp.red (D.host.g k) D.R.r y) z : KFix D s j ρA) : A) = ρA x z :=
  liftAt_apply D s j ρA z.2 hl

theorem factAct_commute (hinj : Function.Injective (fun kv : (Σ k : Fin 2, D.nd.PlG k) => (s kv.1 kv.2).v)) :
    Pairwise fun (a b : Σ k : Fin 2, D.nd.PlG k) => ∀ (x : GL (Fin D.R.r) (ZMod (D.host.g a.1)))
      (y : GL (Fin D.R.r) (ZMod (D.host.g b.1))),
      Commute (factAct D s j ρA hinj a.1 a.2 x) (factAct D s j ρA hinj b.1 b.2 y) := by
  rintro ⟨k, v⟩ ⟨k', v'⟩ hne x y
  have hv : (s k v).v ≠ (s k' v').v := fun e => hne (hinj e)
  have hc := commute_of_ne hv (isLiftAt_liftAt D s j k v x).1 (isLiftAt_liftAt D s j k' v' y).1
  apply LinearMap.ext; rintro ⟨z, hz⟩
  apply Subtype.ext
  show ρA (liftAt D s j k v x) (ρA (liftAt D s j k' v' y) z) = ρA (liftAt D s j k' v' y) (ρA (liftAt D s j k v x) z)
  rw [← Module.End.mul_apply, ← map_mul, hc.eq, map_mul, Module.End.mul_apply]

end Fix

theorem exists_rep : ∀ (D : D7) (s : ∀ k : Fin 2, D.nd.PlG k → SplitPlace D.host.E) (j : ∀ k v, ℚ_[D.host.g k] ≃+* (s k v).v.adicCompletion (maximalRealSubfield D.host.E)), Function.Injective (fun kv : (Σ k : Fin 2, D.nd.PlG k) => (s kv.1 kv.2).v) → ∀ (A : Type) [AddCommGroup A] [Module ℂ A] (ρA : GAf D.host.E D.R.r →* Module.End ℂ A), ∃ ρ : Representation ℂ (G0g D.nd) (KFix D s j ρA), ∀ (k : Fin 2) (v : D.nd.PlG k) (y : GL (Fin D.R.r) ℤ_[D.host.g k]) (x : GAf D.host.E D.R.r), IsLiftAt (s k v) (j k v) y x → ∀ z : KFix D s j ρA, ((ρ (GlobalTheory.GoodTypes.facHom D k v (GlobalTheory.GLp.red (D.host.g k) D.R.r y)) z : KFix D s j ρA) : A) = ρA x z := by
  intro D s j hinj A _ _ ρA
  classical
  refine ⟨MonoidHom.noncommPiCoprod (fun kv => factAct D s j ρA hinj kv.1 kv.2) (factAct_commute D s j ρA hinj), ?_⟩
  intro k v y x hl z
  rw [GlobalTheory.GoodTypes.facHom, MonoidHom.mulSingle_apply, MonoidHom.noncommPiCoprod_mulSingle]
  exact factAct_apply D s j ρA hinj hl z

end GlobalTheory.TypeAct

end
end

section

noncomputable section

open NumberField MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.CuspGeneric GlobalTheory.MirTower
open scoped ENNReal NNReal ComplexConjugate

namespace GlobalTheory.MirTower

theorem unfold_mirabolic : ∀ (E : Type) [Field E] [NumberField E] (a : ℕ) [MeasurableSpace (GA E a)] [BorelSpace (GA E a)] (μ : Measure (GA E a)) [μ.IsHaarMeasure] (ψ : AddChar (Ad E) ℂ), StdPsi ψ → ∀ (𝓕 𝓕₀ : Set (GA E a)), IsFundamentalDomain (ratMirU E a (a - 1)) 𝓕 μ → IsFundamentalDomain (ratMirU E a 0) 𝓕₀ μ → ∀ (w : GA E a → ℝ≥0), Measurable w → (∀ γ ∈ mirU E a (a - 1), ∀ g, w (ratGL E a γ * g) = w g) → (∀ (k : ℕ) (y : UnipotentBlockColumnIndex a k k → Ad E) (g : GA E a), w (blkU y * g) = w g) → (∀ f, Good ψ (a - 1) f → ∫⁻ g in 𝓕, ‖f g‖ₑ ^ 2 * w g ∂μ = ∫⁻ g in 𝓕₀, ‖whit ψ (a - 1) f g‖ₑ ^ 2 * w g ∂μ) ∧ ∀ f f', Good ψ (a - 1) f → Good ψ (a - 1) f' → ∫⁻ g in 𝓕, ‖f g‖ₑ ^ 2 * w g ∂μ ≠ ⊤ → ∫⁻ g in 𝓕, ‖f' g‖ₑ ^ 2 * w g ∂μ ≠ ⊤ → IntegrableOn (fun g => f g * conj (f' g) * (w g : ℝ)) 𝓕 μ ∧ IntegrableOn (fun g => whit ψ (a - 1) f g * conj (whit ψ (a - 1) f' g) * (w g : ℝ)) 𝓕₀ μ ∧ ∫ g in 𝓕, f g * conj (f' g) * (w g : ℝ) ∂μ = ∫ g in 𝓕₀, whit ψ (a - 1) f g * conj (whit ψ (a - 1) f' g) * (w g : ℝ) ∂μ := by
  intro E _ _ a _ _ μ _ ψ hψ 𝓕 𝓕₀ h𝓕 h𝓕₀ w hw hwΓ hwU

  have hm : a - 1 < a ∨ a - 1 = 0 := by omega

  have : SecondCountableTopology (GA E a) := secondCountable_GA

  have : LocallyCompactSpace (Ad E) := GlobalTheory.AdelicUnitaryTop.locallyCompact_adele E
  have : LocallyCompactSpace (Matrix (Fin a) (Fin a) (Ad E)) :=
    inferInstanceAs (LocallyCompactSpace (Fin a → Fin a → Ad E))
  have : LocallyCompactSpace (Matrix (Fin a) (Fin a) (Ad E))ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isClosedEmbedding.locallyCompactSpace
  have : LocallyCompactSpace (GA E a) := Units.isClosedEmbedding_embedProduct.locallyCompactSpace
  have : SigmaCompactSpace (GA E a) := sigmaCompactSpace_of_locallyCompact_secondCountable
  have : SFinite μ :=
    @MeasureTheory.instSFiniteOfSigmaFinite _ _ _ (Measure.IsHaarMeasure.sigmaFinite μ)
  refine ⟨fun f hf => ?_, fun f f' hf hf' h1 h2 => ?_⟩
  · exact lintegral_tower μ hψ hm h𝓕 h𝓕₀ (fun g => (w g : ℝ≥0∞)) (by fun_prop)
      (fun γ hγ g => by simp only [hwΓ γ hγ g]) (fun k _ y g => by simp only [hwU k y g]) hf
  · exact integral_tower μ hψ hm h𝓕 h𝓕₀ w hw hwΓ (fun k _ y g => hwU k y g) hf hf' h1 h2

end GlobalTheory.MirTower
end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations


theorem _root_.GlobalTheory.T.aeval_kills_potCrystalline_of_kills_potSemistable : ∀ {l : ℕ} [Fact l.Prime] (P : LocPrime l) (K K' L L' : FinExt l) (h : K.1 ≤ K'.1) (hN : (GKin h).Normal) (hF : (GKin h).FiniteIndex) (hS : ∀ (g : ↥(GK K)) (c : ↥(K0 K')), ∃ c' : ↥(K0 K'), (P.PD K).actB g (algebraMap ↥(K0 K') P.R.B c) = algebraMap ↥(K0 K') P.R.B c') (hL : L.1 ≤ L'.1) {V V' : Type} [AddCommGroup V] [Module ↥L.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥L.1 V] [AddCommGroup V'] [Module ↥L'.1 V'] [Module ℚ_[l] V'] [IsScalarTower ℚ_[l] ↥L'.1 V'] (ρ : Representation ↥L.1 ↥(GK K) V) (ρ' : Representation ↥L'.1 ↥(GK K) V') (f : V →ₗ[ℚ_[l]] V'), Function.Injective f → GlobalTheory.PstLine.IsMor hL f ρ ρ' → ∀ (g : ↥(GK K)) (q : (↥L.1)[X]), (∀ y ∈ GlobalTheory.Pst.Dpst P ρ', Polynomial.aeval (GlobalTheory.Pst.stRep P ρ' g) (q.map (IntermediateField.inclusion hL).toRingHom) y = 0) → ∀ d ∈ (pc P h hN hF hS).Dpcris ρ, Polynomial.aeval (actVB (P.PD K) ρ g) q d = 0 := by
  first | exact @GlobalTheory.PcrisPst.aeval_eq_zero_of_kills_Dpst | exact GlobalTheory.PcrisPst.aeval_eq_zero_of_kills_Dpst | (intros; apply GlobalTheory.PcrisPst.aeval_eq_zero_of_kills_Dpst <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.charOfLowerRightBlockDet_eventually_eq_one : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (r t : ℕ) (χ : kˣ →* ℂˣ), GlobalTheory.SmGL.IsSmoothChar χ → ∃ U : Set (GL (Fin (r + t)) k), IsOpen U ∧ (1 : GL (Fin (r + t)) k) ∈ U ∧ ∀ g ∈ U, GlobalTheory.BlockType.blockChar χ g = 1 := by
  first | exact @GlobalTheory.BlockType.blockChar_eventually_one | exact GlobalTheory.BlockType.blockChar_eventually_one | (intros; apply GlobalTheory.BlockType.blockChar_eventually_one <;> assumption)
end

section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel

noncomputable section

namespace GlobalTheory.SingleBlockJac

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem leviEmb_oneBlock (N : ℕ) (g : Levi k fun _ : Fin 1 => Fin N) :
    leviEmb k (GlobalTheory.JacTensor.oneBlock N) g = g 0 := by
  ext i j
  exact leviEmb_apply_same k (GlobalTheory.JacTensor.oneBlock N) g 0 i j

theorem deltaHalf_one (N : ℕ) (g : Levi k fun _ : Fin 1 => Fin N) :
    deltaHalf k (fun _ : Fin 1 => Fin N) g = 1 := by
  rw [deltaHalf_apply]
  refine Finset.prod_eq_one fun a _ => ?_
  have hm : modExp (fun _ : Fin 1 => Fin N) a = 0 := by
    unfold modExp
    rw [Finset.sum_eq_zero, Finset.sum_eq_zero, sub_zero]
    · intro c hc
      exact absurd (Finset.mem_filter.1 hc).2 (by rw [Subsingleton.elim c a]; exact lt_irrefl a)
    · intro c hc
      exact absurd (Finset.mem_filter.1 hc).2 (by rw [Subsingleton.elim c a]; exact lt_irrefl a)
  rw [hm]
  simp

theorem eq_one_of_mem_unipRad_oneBlock {N : ℕ} (e : (Σ _ : Fin 1, Fin N) ≃ Fin N) {g : GL (Fin N) k}
    (hg : g ∈ unipRad k e) : g = 1 := by
  obtain ⟨-, h2⟩ := mem_unipRad.1 hg
  refine Units.ext (Matrix.ext fun x y => ?_)
  obtain ⟨⟨a, i⟩, rfl⟩ := e.surjective x
  obtain ⟨⟨b, j⟩, rfl⟩ := e.surjective y
  obtain rfl : a = b := Subsingleton.elim a b
  rw [h2 a i j]
  simp [Matrix.one_apply, e.injective.eq_iff]

theorem twKer_eq_bot {V : Type} [AddCommGroup V] [Module ℂ V] {N : ℕ} (e : (Σ _ : Fin 1, Fin N) ≃ Fin N)
    (π : Representation ℂ (GL (Fin N) k) V) : twKer π (unipRad k e) 1 = ⊥ := by
  refine (Submodule.span_eq_bot).2 ?_
  rintro w ⟨n, v, rfl⟩
  rw [eq_one_of_mem_unipRad_oneBlock e n.2]
  simp

def toJac {V : Type} [AddCommGroup V] [Module ℂ V] (N : ℕ) (π : Representation ℂ (GL (Fin N) k) V) :
    (piTensor fun _ : Fin 1 => π).IntertwiningMap (_root_.GlobalTheory.SmGL.jac (GlobalTheory.JacTensor.oneBlock N) π) where
  toLinearMap := Submodule.mkQ _ ∘ₗ (PiTensorProduct.subsingletonEquiv (R := ℂ) (s := fun _ : Fin 1 => V) (0 : Fin 1)).toLinearMap
  isIntertwining' g := by
    refine LinearMap.ext fun x => ?_
    induction x using PiTensorProduct.induction_on with
    | smul_tprod c x =>
      simp only [LinearMap.comp_apply, map_smul, piTensor_tprod, LinearEquiv.coe_coe,
        PiTensorProduct.subsingletonEquiv_apply_tprod, Submodule.mkQ_apply]
      rw [jac_mk, deltaHalf_one, leviEmb_oneBlock]
      simp [Subsingleton.elim (0 : Fin 1) 0]
    | add x y hx hy =>
      simp only [map_add (f := _)] at hx hy ⊢
      rw [hx, hy]

theorem toJac_injective {V : Type} [AddCommGroup V] [Module ℂ V] (N : ℕ) (π : Representation ℂ (GL (Fin N) k) V) :
    Function.Injective (toJac N π) := by
  intro x y h
  have h' : (Submodule.mkQ (twKer π (unipRad k (GlobalTheory.JacTensor.oneBlock N)) 1))
      (PiTensorProduct.subsingletonEquiv (R := ℂ) (s := fun _ : Fin 1 => V) (0 : Fin 1) x) =
      (Submodule.mkQ (twKer π (unipRad k (GlobalTheory.JacTensor.oneBlock N)) 1))
      (PiTensorProduct.subsingletonEquiv (R := ℂ) (s := fun _ : Fin 1 => V) (0 : Fin 1) y) := h
  rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq, twKer_eq_bot,
    Submodule.mem_bot, sub_eq_zero] at h'
  exact (PiTensorProduct.subsingletonEquiv (R := ℂ) (s := fun _ : Fin 1 => V) (0 : Fin 1)).injective h'

end GlobalTheory.SingleBlockJac

theorem GlobalTheory.SingleBlockJac.isSubquotient_piTensor_jac : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (N : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V)
    (e : (Σ _ : Fin 1, Fin N) ≃ Fin N), IsSubquotient (piTensor fun _ : Fin 1 => π) (_root_.GlobalTheory.SmGL.jac e π) := by
  intro k _ _ _ _ N V _ _ π e
  obtain ⟨φ⟩ := (GlobalTheory.SmGL.Placing.parInd_jac_placing k (Fin 1) (Fin N) (fun _ => Fin N)
    (GlobalTheory.JacTensor.oneBlock N) e V).2 π
  exact IsSubquotient.of_injective ((φ.toIntertwiningMap).comp (GlobalTheory.SingleBlockJac.toJac N π))
    (φ.toLinearEquiv.injective.comp (GlobalTheory.SingleBlockJac.toJac_injective N π))
end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.exists_satakeParameter_of_unramified_inert_definiteUnitary : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (U : Submodule ℂ (UA L n → ℂ)), IsAutRepU U → ∀ (w : HeightOneSpectrum (𝓞 L)), Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield L)) w.asIdeal → ¬ IsSplitAt w → ∀ (s : w.adicCompletion L →+* w.adicCompletion L) (ϖ : w.adicCompletion L) (q : ℕ), (∀ x : L, s (algebraMap L _ x) = algebraMap L _ (IsCMField.complexConj L x)) → Formalism.UG.IsUnramInv ϖ s q → IsUnramU U w → ∃ α0 : Fin (n / 2) → ℂˣ, HasSatAt U w s ϖ q α0 := by
  first | exact @GlobalTheory.InertSatakeGiven.exists_hasSatAt | exact GlobalTheory.InertSatakeGiven.exists_hasSatAt | (intros; apply GlobalTheory.InertSatakeGiven.exists_hasSatAt <;> assumption)
end

section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory

theorem LocLanglands.isSmoothChar_of_comp {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    [IsAlgClosure E Ω] {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
    {a : Weil h →* (w.adicCompletion E)ˣ} (hs : Function.Surjective a)
    (hc : Continuous fun σ : Ine (F := E) A => a (ineIncl h σ))
    (ho : ∀ σ, ord (w.adicCompletion E) (a σ) = -deg σ) {χ : (w.adicCompletion E)ˣ →* ℂˣ}
    (hχ : WeilDeligne.IsSmooth (χ.comp a)) : IsSmoothChar χ := by
  haveI : CompactSpace (Ine (F := E) A) := isCompact_iff_compactSpace.1 (isClosed_Ine A).isCompact
  have hK : IsOpen {σ : Ine (F := E) A | χ (a (ineIncl h σ)) = 1} := hχ
  have hC : IsClosed ((fun σ : Ine (F := E) A => a (ineIncl h σ)) ''
      {σ : Ine (F := E) A | χ (a (ineIncl h σ)) = 1}ᶜ) :=
    (hK.isClosed_compl.isCompact.image hc).isClosed
  have hU : {x : (w.adicCompletion E)ˣ | valuation (w.adicCompletion E) (x : w.adicCompletion E) = 1} ∈ nhds 1 := by
    have h1 : {x : w.adicCompletion E | valuation (w.adicCompletion E) (x - 1) < 1} ∈ nhds 1 := by
      rw [IsValuativeTopology.mem_nhds_iff]
      exact ⟨1, fun z hz => by simpa [neg_add_eq_sub] using hz⟩
    have h2 := Units.continuous_val.continuousAt (x := (1 : (w.adicCompletion E)ˣ)) h1
    refine Filter.mem_of_superset h2 fun x hx => ?_
    have h3 : valuation (w.adicCompletion E) ((x : w.adicCompletion E) - 1) < 1 := hx
    have := Valuation.map_one_add_of_lt _ h3
    simpa using this
  refine Subgroup.isOpen_of_mem_nhds χ.ker (g := 1) ?_
  have h1 : (1 : (w.adicCompletion E)ˣ) ∈ ((fun σ : Ine (F := E) A => a (ineIncl h σ)) ''
      {σ : Ine (F := E) A | χ (a (ineIncl h σ)) = 1}ᶜ)ᶜ := by
    rintro ⟨σ, hσ, e⟩
    refine hσ ?_
    have e' : a (ineIncl h σ) = 1 := e
    simp [e']
  refine Filter.mem_of_superset (Filter.inter_mem hU (hC.isOpen_compl.mem_nhds h1)) ?_
  rintro x ⟨hx, hx'⟩
  obtain ⟨σ, rfl⟩ := hs x
  have h0 : deg σ = 0 := by
    have := ho σ
    rw [ord_eq_zero_iff.2 hx] at this
    omega
  by_contra hn
  exact hx' ⟨⟨σ, deg_eq_zero_iff.mp h0⟩, hn, rfl⟩

theorem localArtinExists_holds : LocalArtinExists := by
  intro E Ω _ _ _ _ _ A w h
  obtain ⟨art, hart⟩ := globalArtinReciprocity_holds E Ω
  obtain ⟨a, hs, ho, hg⟩ := T.exists_inverse_localArtin_weilGroup_hom E Ω A w h art hart
  have hc := T.inverseLocalArtin_continuousOn_inertia E Ω A w h art a hart ho hg
  refine ⟨a, hs, hc, ho, fun ξ hξ => ?_, fun art' hart' => ?_⟩
  · have hker : a.ker ≤ ξ.ker := fun σ hσ => by
      refine T.smoothWeilChar_eq_one_of_toAbsGaloisAb_eq_one E Ω A w h ξ hξ σ ?_
      rw [← hg σ, MonoidHom.mem_ker.1 hσ, map_one, map_one]
    have e : ξ = (a.liftOfSurjective hs ⟨ξ, hker⟩).comp a :=
      (MonoidHom.liftOfRightInverse_comp a _ (Function.rightInverse_surjInv hs) ⟨ξ, hker⟩).symm
    exact ⟨_, isSmoothChar_of_comp hs hc ho (e ▸ hξ), e⟩
  · rw [T.globalArtinReciprocityMap_unique E Ω art' art hart' hart]
    exact hg

end GlobalTheory
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.exists_globalInteger_congr_tameGenerator_character : ∀ (D : D7) (k : Fin 2) (v : D.nd.PlG k), ∃ (u : 𝓞 D.host.E) (hu : (u : D.host.E) ≠ 0), u ∉ (D.naut.plGw k v).asIdeal ∧ ∃ (ϖ : 𝓞 D.host.E) (π : D.nd.Om), ϖ ∈ (D.naut.plGw k v).asIdeal ∧ ϖ ∉ (D.naut.plGw k v).asIdeal ^ 2 ∧ π ^ (normV (D.naut.plGw k v) - 1) = algebraMap D.host.E D.nd.Om (ϖ : D.host.E) ∧ (D.nd.plOm.1 (D.naut.plGw k v)).valuation (D.ntypes.tg k v π / π - algebraMap D.host.E D.nd.Om (u : D.host.E)) < 1 := by
  first | exact @GlobalTheory.ChiTameUnit.exists_int_cong_tg | exact GlobalTheory.ChiTameUnit.exists_int_cong_tg | (intros; apply GlobalTheory.ChiTameUnit.exists_int_cong_tg <;> assumption)
end

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc

theorem _root_.GlobalTheory.T.crystalline_extension_class_bound : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW), admitted D HW F → ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let S := sit D.loc HW l (D.locA l) K s LL h; let E : S.Comparison₂ := ((F l).E K s LL h).tie; TBat S E := by
  first | exact @GlobalTheory.Cyc.ClassBound.class_bound | exact GlobalTheory.Cyc.ClassBound.class_bound | (intros; apply GlobalTheory.Cyc.ClassBound.class_bound <;> assumption)
end
