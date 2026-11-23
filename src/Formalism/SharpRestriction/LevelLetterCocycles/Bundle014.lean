module

public import Formalism.SharpRestriction.LevelLetterCocycles.BaseChangeMapMemLattice
public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.Bundle002
public import Formalism.SharpRestriction.LevelLetterCocycles.WachCoordinates
public import Formalism.AdmissibleDesigns.InvariantsEqBotIff
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle009
import Mathlib.Algebra.Module.StablyFree.Basic
public import Formalism.SharpRestriction.LevelLetterCocycles.BaseChangePreservesUnitaryOf
public import Formalism.SharpRestriction.LevelLetterCocycles.CrystallineLiftingInputs
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalTheoremOfGoodExtensions
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Order.Interval.Finset.Box
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

open Classical TensorProduct

namespace Formalism.MainNotions.UnusedSlot80.BCW

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions

section Crys

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR) {LL LL' : Type} [Field LL] [Field LL'] [Algebra Qp LL]
    [Algebra Qp LL'] [Algebra LL LL'] [IsScalarTower Qp LL LL']
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]

def matOf {k : ℕ} (b : Module.Basis (Fin k) LL V) (ρ : Representation LL G V) :
    G →* Matrix (Fin k) (Fin k) LL :=
  (LinearMap.toMatrixAlgEquiv b).toAlgHom.toRingHom.toMonoidHom.comp ρ

theorem matOf_equiv {k : ℕ} (b : Module.Basis (Fin k) LL V) (ρ : Representation LL G V) (g : G) (x : V) :
    b.equivFun (ρ g x) =
      ((Matrix.toLinAlgEquiv' : Matrix (Fin k) (Fin k) LL ≃ₐ[LL] _).toAlgHom.toRingHom.toMonoidHom.comp
        (matOf b ρ)) g (b.equivFun x) := by
  simp only [matOf, MonoidHom.coe_comp, Function.comp_apply, Module.Basis.equivFun_apply]
  change ⇑(b.repr ((ρ g) x)) = (Matrix.toLinAlgEquiv' (LinearMap.toMatrix b b (ρ g))) ⇑(b.repr x)
  rw [Matrix.toLinAlgEquiv'_apply, LinearMap.toMatrix_mulVec_repr]

theorem isCrys_bρ {k : ℕ} (b : Module.Basis (Fin k) LL V) (ρ : Representation LL G V)
    (h : IsCrys PD ρ) : IsCrys PD (bρ LL' ρ) := by
  have h1 := Formalism.MainNotions.N.K.Norm.isCrys_congr PD b.equivFun (matOf_equiv b ρ) h
  have h2 := coefficient_crystal_generation PD (IsScalarTower.toAlgHom Qp LL LL') (matOf b ρ) h1
  let b' : Module.Basis (Fin k) LL' (LL' ⊗[LL] V) := Algebra.TensorProduct.basis LL' b
  refine Formalism.MainNotions.N.K.Norm.isCrys_congr PD b'.equivFun.symm (fun g y => ?_) h2
  have hm : ∀ g, matOf b' (bρ LL' ρ) g =
      (IsScalarTower.toAlgHom Qp LL LL').mapMatrix (matOf b ρ g) := by
    intro g
    change LinearMap.toMatrix b' b' ((ρ g).baseChange LL') = (LinearMap.toMatrix b b (ρ g)).map _
    rw [LinearMap.toMatrix_baseChange]
    rfl
  apply b'.equivFun.injective
  rw [LinearEquiv.apply_symm_apply]
  have e1 := matOf_equiv b' (bρ LL' ρ) g (b'.equivFun.symm y)
  rw [LinearEquiv.apply_symm_apply] at e1
  rw [e1]
  simp only [MonoidHom.coe_comp, Function.comp_apply, hm]
  rfl

end Crys

section LocC

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR) {LL LL' O O' : Type} [Field LL] [Field LL']
    [Algebra Qp LL] [Algebra Qp LL'] [Algebra LL LL'] [IsScalarTower Qp LL LL']
    [TopologicalSpace LL] [TopologicalSpace LL'] [IsTopologicalRing LL'] [CommRing O] [IsDomain O]
    [Algebra O LL] [IsFractionRing O LL] [CommRing O'] [Algebra O' LL'] [Algebra O O'] [Algebra O LL']
    [IsScalarTower O O' LL'] [IsScalarTower O LL LL']

theorem crysLat_b (hc : Continuous (algebraMap LL LL')) (hO' : Function.Injective (algebraMap O' LL'))
    (T : LocLat G Qp LL O) (hT : Formalism.MainNotions.WachCoordinates.CrysLat PD T) :
    Formalism.MainNotions.WachCoordinates.CrysLat PD (bLoc (O' := O') hc hO' T) :=
  ⟨(bLoc (O' := O') hc hO' T).fdim, (bLoc (O' := O') hc hO' T).mtop, (bLoc (O' := O') hc hO' T).cont,
    isCrys_bρ PD (Module.finBasis LL T.V) T.ρ hT.2.2.2⟩

theorem finrank_b (hc : Continuous (algebraMap LL LL')) (hO' : Function.Injective (algebraMap O' LL'))
    (T : LocLat G Qp LL O) :
    Module.finrank LL' (bLoc (O' := O') hc hO' T).V = Module.finrank LL T.V :=
  Module.finrank_baseChange

end LocC

section Jmp

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR) {LL LL' : Type} [Field LL] [Field LL'] [Algebra Qp LL]
    [Algebra Qp LL'] [Algebra LL LL'] [IsScalarTower Qp LL LL']
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]

theorem isJumpV_bρ (hJ : Formalism.MainNotions.N.GlobalTheory.CoefJumpGen) {k : ℕ} (b : Module.Basis (Fin k) LL V)
    (ρ : Representation LL G V) (τ : K →ₐ[Qp] LL) (a : ℤ) :
    IsJumpV PD (bρ LL' ρ) ((IsScalarTower.toAlgHom Qp LL LL').comp τ) a ↔ IsJumpV PD ρ τ a := by
  let b' : Module.Basis (Fin k) LL' (LL' ⊗[LL] V) := Algebra.TensorProduct.basis LL' b
  have hm : ∀ g, matOf b' (bρ LL' ρ) g =
      (IsScalarTower.toAlgHom Qp LL LL').mapMatrix (matOf b ρ g) := by
    intro g
    change LinearMap.toMatrix b' b' ((ρ g).baseChange LL') = (LinearMap.toMatrix b b (ρ g)).map _
    rw [LinearMap.toMatrix_baseChange]
    rfl
  have e1 := Formalism.MainNotions.N.K.Norm.isJumpV_congr PD b.equivFun (matOf_equiv b ρ) τ a
  have e2 := hJ PD (IsScalarTower.toAlgHom Qp LL LL') (matOf b ρ) τ a
  have he' : ∀ g x, b'.equivFun (bρ LL' ρ g x) =
      ((Matrix.toLinAlgEquiv' : Matrix (Fin k) (Fin k) LL' ≃ₐ[LL'] _).toAlgHom.toRingHom.toMonoidHom.comp
        ((IsScalarTower.toAlgHom Qp LL LL').mapMatrix.toRingHom.toMonoidHom.comp (matOf b ρ))) g
        (b'.equivFun x) := by
    intro g x
    rw [matOf_equiv b' (bρ LL' ρ) g x]
    simp only [MonoidHom.coe_comp, Function.comp_apply, hm]
    rfl
  have e3 := Formalism.MainNotions.N.K.Norm.isJumpV_congr PD b'.equivFun he' ((IsScalarTower.toAlgHom Qp LL LL').comp τ) a
  rw [e3, ← e2, ← e1]

end Jmp

section Assemble

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR) {LL LL' O O' : Type} [Field LL] [Field LL']
    [Algebra Qp LL] [Algebra Qp LL'] [Algebra LL LL'] [IsScalarTower Qp LL LL']
    [TopologicalSpace LL] [TopologicalSpace LL'] [IsTopologicalRing LL'] [CommRing O] [IsDomain O]
    [Algebra O LL] [IsFractionRing O LL] [CommRing O'] [Algebra O' LL'] [Algebra O O'] [Algebra O LL']
    [IsScalarTower O O' LL'] [IsScalarTower O LL LL']

theorem bcAt_of (hc : Continuous (algebraMap LL LL')) (hO' : Function.Injective (algebraMap O' LL'))
    (hJ : Formalism.MainNotions.N.GlobalTheory.CoefJumpGen)
    (hL : ∀ (T₁ T₂ : LocLat G Qp LL O) (F : LatHom T₁.L T₂.L), Formalism.MainNotions.WachCoordinates.CrysLat PD T₁ →
      Formalism.MainNotions.WachCoordinates.CrysLat PD T₂ → F.Onto → ∀ e, (bHom (O' := O') hc hO' F).LiftF PD e → F.LiftF PD e)
    (hC : ∀ (T₁ T₂ : LocLat G Qp LL O) (F : LatHom T₁.L T₂.L), Formalism.MainNotions.WachCoordinates.CrysLat PD T₁ →
      Formalism.MainNotions.WachCoordinates.CrysLat PD T₂ → F.Onto → ∀ x, Formalism.MainNotions.TruncatedSeriesCountingBounds.ColLeR PD (bHom (O' := O') hc hO' F) x → Formalism.MainNotions.TruncatedSeriesCountingBounds.ColLeR PD F x) :
    Formalism.MainNotions.WachCoordinates.BCAt PD (LL := LL) (O := O) (O' := O') (IsScalarTower.toAlgHom Qp LL LL') := by
  intro T₁ T₂ F h₁ h₂ hF
  refine ⟨bLoc hc hO' T₁, bLoc hc hO' T₂, bHom hc hO' F, crysLat_b PD hc hO' T₁ h₁,
    crysLat_b PD hc hO' T₂ h₂, bHom_onto hc hO' F hF, fun τ a => ⟨?_, ?_⟩, finrank_b hc hO' T₂,
    hL T₁ T₂ F h₁ h₂ hF, hC T₁ T₂ F h₁ h₂ hF⟩
  · exact isJumpV_bρ PD hJ (Module.finBasis LL T₁.V) T₁.ρ τ a
  · exact isJumpV_bρ PD hJ (Module.finBasis LL T₂.V) T₂.ρ τ a

end Assemble

end Formalism.MainNotions.UnusedSlot80.BCW
end
end

section

noncomputable section

namespace Formalism.MainNotions.RamifiedCoefficientChains.S9.ExtensionLemmaAlt

open Module Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.RamifiedCoefficientChains TensorProduct

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

section Op

variable (W : LocWach PD LL O v n) (T : LocLat G Qp LL O)

def uniformizerInverse : W.EE := Ring.inverse (algebraMap (LetA O n) W.EE W.π₀)

def derivationOnWachModule : W.DD T →ₗ[O] W.DD T := Formalism.MainNotions.LiftingTheory.lifta_δ W T (uniformizerInverse W)

theorem derivation_on_wach_module_apply (x : W.DD T) : derivationOnWachModule W T x = uniformizerInverse W • (W.γ T x - x) := rfl

variable {W} in
theorem algebraMap_uniformizer_mul_inverse (hU : IsUnit (algebraMap (LetA O n) W.EE W.π₀)) :
    algebraMap (LetA O n) W.EE W.π₀ * uniformizerInverse W = 1 :=
  Ring.mul_inverse_cancel _ hU

theorem uniformizer_smul_derivation (hU : IsUnit (algebraMap (LetA O n) W.EE W.π₀)) (x : W.DD T) :
    W.π₀ • derivationOnWachModule W T x = W.γ T x - x := by
  rw [derivation_on_wach_module_apply, ← smul_assoc, Algebra.smul_def, algebraMap_uniformizer_mul_inverse hU, one_smul]

theorem inverse_smul_uniformizer_smul (hU : IsUnit (algebraMap (LetA O n) W.EE W.π₀)) (x : W.DD T) :
    uniformizerInverse W • (W.π₀ • x) = x := by
  rw [← algebraMap_smul W.EE W.π₀ x, smul_smul, mul_comm, algebraMap_uniformizer_mul_inverse hU, one_smul]

theorem smul_comm_letA_EE (a : LetA O n) (e : W.EE) (x : W.DD T) : a • (e • x) = e • (a • x) := by
  rw [← smul_assoc a e x, Algebra.smul_def a e, mul_comm, mul_smul, algebraMap_smul W.EE a x]

theorem gammaA_idempotent (g : W.Gam) (c : ZMod n) : W.γA g (letE c : LetA O n) = letE c := by
  funext i
  show W.γ₀ g ((Pi.single c (1 : PowerSeries O) : LetA O n) i) = (Pi.single c (1 : PowerSeries O) : LetA O n) i
  rw [Pi.single_apply]
  split_ifs <;> simp

theorem idempotent_smul_gamma (c : ZMod n) (x : W.DD T) :
    (letE c : LetA O n) • W.γ T x = W.γ T ((letE c : LetA O n) • x) := by
  show (letE c : LetA O n) • W.γD T W.gam x = W.γD T W.gam ((letE c : LetA O n) • x)
  rw [← algebraMap_smul W.EE (letE c : LetA O n) x, W.γD_smul, W.γE_ext,
    show letγ (W.γ₀ W.gam) (letE c : LetA O n) = letE c from gammaA_idempotent W W.gam c, algebraMap_smul]

theorem gammaD_gamma_comm (δ : W.Gam) (x : W.DD T) : W.γD T δ (W.γ T x) = W.γ T (W.γD T δ x) := by
  show W.γD T δ (W.γD T W.gam x) = W.γD T W.gam (W.γD T δ x)
  rw [← W.γD_mul, ← W.γD_mul, mul_comm]

theorem delta_fixes_inverse (a : LetA O n) (ha : a ∈ W.AΔ) (hU : IsUnit (algebraMap (LetA O n) W.EE a))
    (δ : W.Gam) (hδ : δ ∈ W.DelF) :
    W.γE δ (Ring.inverse (algebraMap (LetA O n) W.EE a)) = Ring.inverse (algebraMap (LetA O n) W.EE a) := by
  have ha' : ∀ δ ∈ W.DelF, W.γA δ a = a := ha
  have hfix : W.γE δ (algebraMap (LetA O n) W.EE a) = algebraMap (LetA O n) W.EE a := by
    rw [W.γE_ext]
    exact congrArg (algebraMap (LetA O n) W.EE) (ha' δ hδ)
  obtain ⟨u, hu⟩ := hU
  rw [← hu] at hfix ⊢
  rw [Ring.inverse_unit]
  have h1 : (u : W.EE) * W.γE δ ↑u⁻¹ = 1 := by
    rw [← hfix, ← map_mul, Units.mul_inv, map_one]
  exact (Units.inv_eq_of_mul_eq_one_right h1).symm

theorem invariantLetter_fixed_smul {c : ZMod n} (e : W.EE) (he : ∀ δ ∈ W.DelF, W.γE δ e = e) {x : W.DD T}
    (h : Formalism.MainNotions.CrystallineLiftingInputs.DL W T c x) : Formalism.MainNotions.CrystallineLiftingInputs.DL W T c (e • x) := by
  refine ⟨?_, fun δ hδ => ?_⟩
  · rw [smul_comm_letA_EE, h.1]
  · rw [W.γD_smul, he δ hδ, h.2 δ hδ]

theorem invariantLetter_gamma_sub {c : ZMod n} {x : W.DD T} (h : Formalism.MainNotions.CrystallineLiftingInputs.DL W T c x) :
    Formalism.MainNotions.CrystallineLiftingInputs.DL W T c (W.γ T x - x) := by
  refine ⟨?_, fun δ hδ => ?_⟩
  · rw [smul_sub, idempotent_smul_gamma, h.1]
  · rw [map_sub, gammaD_gamma_comm, h.2 δ hδ]

theorem invariantLetter_derivation (hπΔ : W.π₀ ∈ W.AΔ) (hU : IsUnit (algebraMap (LetA O n) W.EE W.π₀))
    {c : ZMod n} {x : W.DD T} (h : Formalism.MainNotions.CrystallineLiftingInputs.DL W T c x) :
    Formalism.MainNotions.CrystallineLiftingInputs.DL W T c (derivationOnWachModule W T x) := by
  rw [derivation_on_wach_module_apply]
  exact invariantLetter_fixed_smul W T (uniformizerInverse W)
    (fun δ hδ => delta_fixes_inverse W W.π₀ hπΔ hU δ hδ) (invariantLetter_gamma_sub W T h)

theorem invariantLetter_derivation_pow (hπΔ : W.π₀ ∈ W.AΔ) (hU : IsUnit (algebraMap (LetA O n) W.EE W.π₀))
    {c : ZMod n} (k : ℕ) {x : W.DD T} (h : Formalism.MainNotions.CrystallineLiftingInputs.DL W T c x) :
    Formalism.MainNotions.CrystallineLiftingInputs.DL W T c ((derivationOnWachModule W T ^ k) x) := by
  induction k with
  | zero => rw [pow_zero, Module.End.one_apply]; exact h
  | succ k ih => rw [pow_succ', Module.End.mul_apply]; exact invariantLetter_derivation W T hπΔ hU ih

theorem invariantLetter_polynomial_derivation (hπΔ : W.π₀ ∈ W.AΔ) (hU : IsUnit (algebraMap (LetA O n) W.EE W.π₀))
    {c : ZMod n} (P : Polynomial O) {x : W.DD T} (h : Formalism.MainNotions.CrystallineLiftingInputs.DL W T c x) :
    Formalism.MainNotions.CrystallineLiftingInputs.DL W T c (Polynomial.aeval (derivationOnWachModule W T) P x) := by
  induction P using Polynomial.induction_on'
  next p q hp hq =>
    rw [map_add (f := _), LinearMap.add_apply]
    exact ⟨by rw [smul_add, hp.1, hq.1], fun δ hδ => by rw [map_add (f := _), hp.2 δ hδ, hq.2 δ hδ]⟩
  next k a =>
    rw [Polynomial.aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply]
    have hk := invariantLetter_derivation_pow W T hπΔ hU k h
    exact ⟨by rw [smul_comm _ a, hk.1], fun δ hδ => by rw [map_smul, hk.2 δ hδ]⟩

def DerivationPreservesQLattice [NeZero n] : Prop :=
  Formalism.MainNotions.LiftingTheory.CaseA W → ∀ T : LocLat G Qp LL O, IsCrys PD T.ρ → ∀ (i : ZMod n) (k : ℤ) (x : W.DD T),
    Formalism.MainNotions.CrystallineLiftingInputs.InQN W T i k x → Formalism.MainNotions.CrystallineLiftingInputs.InQN W T i k (Formalism.MainNotions.CrystallineLiftingInputs.dOp W T x)

def QLattice (c : ZMod n) (k : ℕ) (x : W.DD T) : Prop :=
  Formalism.MainNotions.CrystallineLiftingInputs.DL W T c x ∧ Formalism.MainNotions.LiftingTheory.qp W ^ k • x ∈ W.N T

theorem qLattice_iff (c : ZMod n) (k : ℕ) (x : W.DD T) :
    Formalism.MainNotions.CrystallineLiftingInputs.InQN W T c (k : ℤ) x ↔ QLattice W T c k x := by
  unfold Formalism.MainNotions.CrystallineLiftingInputs.InQN QLattice
  simp

theorem qLattice_add {c : ZMod n} {k : ℕ} {x y : W.DD T} (hx : QLattice W T c k x)
    (hy : QLattice W T c k y) : QLattice W T c k (x + y) := by
  refine ⟨⟨?_, fun δ hδ => ?_⟩, ?_⟩
  · rw [smul_add, hx.1.1, hy.1.1]
  · rw [map_add (f := _), hx.1.2 δ hδ, hy.1.2 δ hδ]
  · rw [smul_add]
    exact add_mem hx.2 hy.2

theorem qLattice_smul {c : ZMod n} {k : ℕ} (a : O) {x : W.DD T} (hx : QLattice W T c k x) :
    QLattice W T c k (a • x) := by
  refine ⟨⟨?_, fun δ hδ => ?_⟩, ?_⟩
  · rw [smul_comm _ a, hx.1.1]
  · rw [map_smul, hx.1.2 δ hδ]
  · rw [smul_comm _ a, ← algebraMap_smul (LetA O n) a]
    exact Submodule.smul_mem _ _ hx.2

theorem qLattice_mono {c : ZMod n} {k k' : ℕ} (hk : k ≤ k') {x : W.DD T} (hx : QLattice W T c k x) :
    QLattice W T c k' x := by
  refine ⟨hx.1, ?_⟩
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
  rw [pow_add, mul_comm, mul_smul]
  exact Submodule.smul_mem _ _ hx.2

theorem qLattice_derivation [NeZero n] (hDS : DerivationPreservesQLattice W) (hA : Formalism.MainNotions.LiftingTheory.CaseA W)
    (hT : IsCrys PD T.ρ) (c : ZMod n) (k : ℕ)
    {x : W.DD T} (h : QLattice W T c k x) : QLattice W T c k (derivationOnWachModule W T x) := by
  rw [← qLattice_iff] at h ⊢
  rw [derivation_on_wach_module_apply]
  exact hDS hA T hT c (k : ℤ) x h

theorem qLattice_polynomial_derivation [NeZero n] (hDS : DerivationPreservesQLattice W) (hA : Formalism.MainNotions.LiftingTheory.CaseA W)
    (hT : IsCrys PD T.ρ) (c : ZMod n) (k : ℕ)
    (P : Polynomial O) {x : W.DD T} (h : QLattice W T c k x) :
    QLattice W T c k (Polynomial.aeval (derivationOnWachModule W T) P x) := by
  have hpow : ∀ j : ℕ, QLattice W T c k ((derivationOnWachModule W T ^ j) x) := by
    intro j
    induction j with
    | zero => rw [pow_zero, Module.End.one_apply]; exact h
    | succ j ih => rw [pow_succ', Module.End.mul_apply]; exact qLattice_derivation W T hDS hA hT c k ih
  induction P using Polynomial.induction_on'
  next p q hp hq =>
    rw [map_add (f := _), LinearMap.add_apply]
    exact qLattice_add W T hp hq
  next j a =>
    rw [Polynomial.aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply]
    exact qLattice_smul W T a (hpow j)

end Op

end Formalism.MainNotions.RamifiedCoefficientChains.S9.ExtensionLemmaAlt

end
end

section

noncomputable section

namespace Formalism.MainNotions.N.Ln34

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules

section Local

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n) (T : LocLat G Qp LL O)

def letS (c : ZMod n) : Submodule O (W.DD T) :=
  LinearMap.ker ((((letE c : LetA O n) • LinearMap.id - LinearMap.id :
    W.DD T →ₗ[LetA O n] W.DD T)).restrictScalars O)

def DelS : Submodule O (W.DD T) :=
  ⨅ δ ∈ W.DelF, LinearMap.ker (W.γD T δ - LinearMap.id)

def NcS (c : ZMod n) : Submodule O (W.DD T) :=
  (W.N T).restrictScalars O ⊓ DelS W T ⊓ letS W T c

def PcS (c : ZMod n) : Submodule O (W.DD T) :=
  (Formalism.MainNotions.DeltaInvariantLattices.φspan W T (W.Nl T (c - 1))).restrictScalars O ⊓ DelS W T ⊓ letS W T c

def LamPS (Eπ : LetA O n) (h' : ℕ) (c : ZMod n) : Submodule O (W.DD T) :=
  ((Formalism.MainNotions.DeltaInvariantLattices.φspan W T (W.Nl T (c - 1))).comap (Formalism.MainNotions.DeltaInvariantLattices.smulA W T (Eπ ^ h'))).restrictScalars O ⊓
    DelS W T ⊓ letS W T c

def PiNS (π' : LetA O n) (k : ℕ) : Submodule O (W.DD T) :=
  (Formalism.MainNotions.DeltaInvariantLattices.aN W T (π' ^ k)).restrictScalars O ⊓ DelS W T

def InvS (π' Eπ : LetA O n) (h' k : ℕ) (c : ZMod n) : Submodule O (W.DD T) :=
  LamPS W T Eπ h' c ⊓ (PiNS W T π' k).comap (W.γD T W.gamK - LinearMap.id)

abbrev LcQ (π' : LetA O n) (c : ZMod n) : Type :=
  ↥(NcS W T (c - 1)) ⧸ (PiNS W T π' 1).comap (NcS W T (c - 1)).subtype

def JCl (π' Eπ : LetA O n) (h' M : ℕ) (c : ZMod n) : Set (G → T.V) :=
  {κ | ∃ hκ : κ ∈ latticeCocycles T.L, ∃ w ∈ InvS W T π' Eπ h' M c, ∃ z ∈ PiNS W T π' M,
    ∃ hwz : (w, z) ∈ W.wachCocyclesDelta T,
      Submodule.mkQ ((latticeCoboundaries T.L).comap (latticeCocycles T.L).subtype) (⟨κ, hκ⟩ : ↥(latticeCocycles T.L)) = W.clK T ⟨(w, z), hwz⟩}

def JZ (π' Eπ : LetA O n) (h' M : ℕ) (c : ZMod n) : Submodule O (G → T.V) :=
  Submodule.span O (JCl W T π' Eπ h' M c)

end Local

section Record

variable {l : ℕ} [Fact l.Prime]

abbrev eK (K : FinExt l) : ℕ := finrank ↥(K0 K) ↥K.1

abbrev sK (l : ℕ) [Fact l.Prime] (K : FinExt l) : ℕ := (l - 1) / eK K

abbrev MK (l : ℕ) [Fact l.Prime] (K : FinExt l) (h' : ℕ) : ℕ := ⌈(4 * h' : ℝ) / (sK l K : ℝ)⌉₊

abbrev y2K (l : ℕ) [Fact l.Prime] (K : FinExt l) (h' S η : ℕ) : ℕ :=
  2 * sigA l (sK l K) h' + kapA l (eK K) h' S + rhoA l (eK K) h' + max (2 * sigA l (sK l K) h') (ycA l h' η)

def HypN (P : LocPrime l) (K LL : FinExt l) (T₁ T₂ : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL))
    (F : LatHom T₁.L T₂.L) (S η m h' : ℕ) (up : (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) → Bool)
    (b : (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) → ℕ) : Prop :=
  IsCrys (P.PD K) T₁.ρ ∧ IsCrys (P.PD K) T₂.ρ ∧ F.Onto ∧
    (∀ τ, JumpsInV (P.PD K) T₁.ρ τ (deep (up τ) (b τ) S ∪ Set.Icc (-(η : ℤ)) η)) ∧
    (∀ τ, JumpsInV (P.PD K) T₂.ρ τ (deep (up τ) (b τ) S ∪ Set.Icc (-(η : ℤ)) η)) ∧
    (∀ τ, η < b τ) ∧ (∀ τ, b τ + S ≤ h') ∧ 1 ≤ h' ∧
    (∀ τ, ∑ a ∈ Finset.Icc (-(η : ℤ)) η, multV (P.PD K) T₂.ρ τ a ≤ m) ∧
    (finrank ↥(K0 K) ↥K.1 = 2 ∨ ∀ τ τ', intersection_update_fsHerm_neg_one K τ = intersection_update_fsHerm_neg_one K τ' → up τ = up τ')

end Record

end Formalism.MainNotions.N.Ln34

end
end
