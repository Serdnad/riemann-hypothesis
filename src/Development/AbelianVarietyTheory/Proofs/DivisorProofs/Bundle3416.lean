module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle851
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3408
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle004
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrystallinePull2SumCup
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle018
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2610
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3385
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2231
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3376
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3146
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3397
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle041
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle012
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle002
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle014
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3208
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3394
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3403
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAbelianSchemeLiftWithPrincipalLineBundle
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3409
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2771
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2858
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.TypeStar
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUnifOfIsMumfordOf
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle064
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle532
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle005

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HTGlueIsoPol

open GlobalTheory.AbDual

section
variable {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R'] {I : Ideal R} {I' : Ideal R'}
  {S S' : Scheme.{0}} {κ : DividedPowers I} {t : S ⟶ Sp R} {A : Over S} [GrpObj A]
  {κ' : DividedPowers I'} {t' : S' ⟶ Sp R'} {A' : Over S'} [GrpObj A']
  {b : S' ⟶ S} {φ : A'.left ⟶ A.left} {m : GrpMor κ t A κ' t' A' (algebraMap R R') b φ}

theorem ext_of_isBC (hm : m.IsBC) {h₁ h₂ : Crys κ' t' A'} (e : ∀ c, h₁ (m.pull c) = h₂ (m.pull c)) :
    h₁ = h₂ := by
  refine LinearMap.ext fun c ↦ ?_
  obtain ⟨z, rfl⟩ := hm.2 c
  induction z with
  | add x y hx hy => simp only [map_add (f := _), hx, hy]
  | tmul x c => rw [liftSemi_tmul, map_smul, map_smul, e c]


omit [Algebra R R'] in
theorem crys_sum_apply {J : Type} (s : Finset J) (g : J → Crys κ' t' A') (q : prim κ' t' A') :
    (∑ i ∈ s, g i) q = ∑ i ∈ s, g i q := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, LinearMap.add_apply, ih]

theorem bcMap_pull (hm : m.IsBC) (h : Crys κ t A) (c : prim κ t A) :
    hm.bcMap h (m.pull c) = algebraMap R R' (h c) :=
  (hm.corr_iff (h := h)).2 rfl c


omit [Algebra R R'] in
theorem crys_add_apply (g g' : Crys κ' t' A') (q : prim κ' t' A') : (g + g') q = g q + g' q :=
  LinearMap.add_apply g g' q


omit [Algebra R R'] in
theorem crys_smul_apply (r : R') (g : Crys κ' t' A') (q : prim κ' t' A') : (r • g) q = r * g q :=
  LinearMap.smul_apply r g q
end

theorem tsze_coords {k : Type} [Field k] {d : ℕ} (a : k) (v : Fin d → k) :
    (TrivSqZeroExt.inl a + TrivSqZeroExt.inr v : TrivSqZeroExt k (Fin d → k)) =
      algebraMap k _ a + ∑ j, TrivSqZeroExt.inr (Pi.single j 1) * algebraMap k _ (v j) := by
  ext
  · simp [TrivSqZeroExt.algebraMap_eq_inl, TrivSqZeroExt.fst_sum]
  · simp [TrivSqZeroExt.algebraMap_eq_inl, TrivSqZeroExt.snd_sum, Finset.sum_apply, Pi.single_apply]

theorem glue_pairing_eq_zero {k : Type} [Field k] {d : ℕ} {H M : Type*} [AddCommGroup H] [Module k H]
    [AddCommGroup M] [Module (TrivSqZeroExt k (Fin d → k)) M]
    (bc : H →ₛₗ[algebraMap k (TrivSqZeroExt k (Fin d → k))] M)
    (Φ : M →ₗ[TrivSqZeroExt k (Fin d → k)] M →ₗ[TrivSqZeroExt k (Fin d → k)] TrivSqZeroExt k (Fin d → k))
    (φ : LinearMap.BilinForm k H) (key : ∀ u v, Φ (bc u) (bc v) = algebraMap k _ (φ u v))
    {x y : H} {u v : Fin d → H} (hxy : φ x y = 0) (huv : ∀ j, φ (u j) y + φ x (v j) = 0) :
    Φ (bc x + ∑ j, (TrivSqZeroExt.inr (Pi.single j 1) : TrivSqZeroExt k (Fin d → k)) • bc (u j))
      (bc y + ∑ j, (TrivSqZeroExt.inr (Pi.single j 1) : TrivSqZeroExt k (Fin d → k)) • bc (v j)) = 0 := by
  have hee : ∀ (j l : Fin d) (r : TrivSqZeroExt k (Fin d → k)),
      (TrivSqZeroExt.inr (Pi.single j 1) : TrivSqZeroExt k (Fin d → k)) * (TrivSqZeroExt.inr (Pi.single l 1) * r) = 0 :=
    fun j l r ↦ by rw [← _root_.mul_assoc, TrivSqZeroExt.inr_mul_inr, MulZeroClass.zero_mul]

  simp only [map_add (f := _), map_sum, map_smul, LinearMap.add_apply, LinearMap.sum_apply, LinearMap.smul_apply, key,
  smul_eq_mul, Finset.mul_sum, mul_add, hee, Finset.sum_const_zero, add_zero, hxy, map_zero, zero_add]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun j _ ↦ ?_
  rw [← mul_add, ← map_add (f := _), huv j, map_zero, mul_zero]



theorem glueFil_isotropic : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ Sp R) (o₀ : GlobalTheory.UPel.HT.Obj b N t) (β : R →+* k), t = spMap β → ∀ φ : LinearMap.BilinForm k (HdR o₀.A), GlobalTheory.AbDual.IsCorrForm (dp0 k) (𝟙 _) o₀.A o₀.A o₀.P φ → ∀ (d : ℕ) (f : Fin d → (HdR o₀.A →ₗ[k] HdR o₀.A)), (∀ j, IsKS (GlobalTheory.HTCount.crysAct o₀) φ (Fil o₀.A) (GlobalTheory.HTCount.lieZ o₀ β) (f j)) → (∀ Φ : Crys (divided₂ (GlobalTheory.FODef.sqZero k (Fin d → k))) (spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom) o₀.A →ₗ[(TrivSqZeroExt k (Fin d → k))] Crys (divided₂ (GlobalTheory.FODef.sqZero k (Fin d → k))) (spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom) o₀.A →ₗ[(TrivSqZeroExt k (Fin d → k))] (TrivSqZeroExt k (Fin d → k)), GlobalTheory.AbDual.IsCorrForm (divided₂ (GlobalTheory.FODef.sqZero k (Fin d → k))) (spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom) o₀.A o₀.A o₀.P Φ → ∀ x ∈ (GlobalTheory.HTGlue.glueFil o₀.A f), ∀ y ∈ (GlobalTheory.HTGlue.glueFil o₀.A f), Φ x y = 0) := by
  intro p _ D R _ b N hN hNp k _ _ t o₀ β hβ φ hφ d f hf Φ hΦ X hX Y hY
  have h2 := GlobalTheory.FODef.sqZero k (Fin d → k)
  have hA := o₀.ab
  obtain ⟨g, hg⟩ := GlobalTheory.AbelianDim.exists_relDim k o₀.A hA
  obtain ⟨A, _, i, hi, hAC, hgC⟩ := GlobalTheory.abelianScheme_constLift (TrivSqZeroExt k (Fin d → k)) k
    (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom (algebraMap k (TrivSqZeroExt k (Fin d → k)))
    (by ext; simp [TrivSqZeroExt.algebraMap_eq_inl]) o₀.A g hA hg
  have ADR := GlobalTheory.abelianDeRham
  have ADC := GlobalTheory.abelianDualCrystal_of_dualAbelianScheme GlobalTheory.dualAbelianScheme
  have CS := GlobalTheory.Published.AbelianDualCrystal.cupSquare_crys_prod ADR.1 ADC.2 (isDPNilpotent_squareZero h2)
    (fun r ↦ ⟨TrivSqZeroExt.inl r, rfl⟩) rfl hAC hgC hAC hgC hi hi
  have m := GlobalTheory.FODef.constMorV k (Fin d → k) o₀.A
  have hBC : m.IsBC := GlobalTheory.SqZeroCrys.isBC_trivSqZeroExt k (Fin d → k) o₀.A hA _ m
  have hP := o₀.isLB
  have e0 : LBIso (o₀.P.pull (𝟙 _)) o₀.P := by
    first
      | exact LBIso.chartPull (chartPullPull o₀.P (𝟙 _)) (chartPullId o₀.P) (PolBaseChange.lbIso_refl hP)
      | exact LBIso.chartPull (chartPullPull o₀.P (𝟙 _)) (chartPullId o₀.P) (ChernExists.lbIso_refl hP)
  obtain ⟨Ψ, hΨ, hΨc⟩ := hφ.pull hP m m (h := 𝟙 _) (by simp) (by simp) hP e0
  obtain rfl := hΦ.unique CS hP hΨ

  have key : ∀ u v : HdR o₀.A, Φ (hBC.bcMap u) (hBC.bcMap v) = algebraMap k _ (φ u v) := fun u v ↦
    hΨc u _ v _ ((hBC.corr_iff (h := u)).2 rfl) ((hBC.corr_iff (h := v)).2 rfl)

  have dec : ∀ Z ∈ GlobalTheory.HTGlue.glueFil o₀.A f, ∃ x ∈ Fil o₀.A, ∃ z : Fin d → HdR o₀.A, (∀ j, z j ∈ Fil o₀.A) ∧
      Z = hBC.bcMap x + ∑ j, (TrivSqZeroExt.inr (Pi.single j 1) : TrivSqZeroExt k (Fin d → k)) •
        hBC.bcMap (f j x + z j) := by
    rintro Z ⟨x, hx, z, hz, hZ⟩
    refine ⟨x, hx, z, hz, ext_of_isBC hBC fun c ↦ ?_⟩
    rw [hZ c, tsze_coords, crys_add_apply]
    refine (congrArg₂ (· + ·) (bcMap_pull hBC x c) ?_).symm
    exact (crys_sum_apply _ _ _).trans (Finset.sum_congr rfl fun j _ ↦
      (crys_smul_apply _ _ _).trans (congrArg _ (bcMap_pull hBC _ c)))
  have iso := (GlobalTheory.HTLagr.fil_lagrangian p D R b N k t o₀ φ ⟨g, hg⟩ hφ).1
  refine (dec X hX).elim fun x hx' ↦ (dec Y hY).elim fun y hy' ↦ ?_
  refine hx'.2.elim fun z hz' ↦ hy'.2.elim fun w hw' ↦ ?_
  refine (congrArg₂ (fun a b ↦ Φ a b) hz'.2 hw'.2).trans ?_
  refine glue_pairing_eq_zero hBC.bcMap Φ φ key (iso x hx'.1 y hy'.1) fun j ↦ ?_
  simp only [map_add (f := _), LinearMap.add_apply, iso _ (hz'.1 j) _ hy'.1, iso _ hx'.1 _ (hw'.1 j), add_zero]
  exact (hf j).2.2 x hx'.1 y hy'.1

end GlobalTheory.HTGlueIsoPol
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham

noncomputable section

open scoped TensorProduct

namespace GlobalTheory.HTGlue

variable {k : Type} [Field k] {d : ℕ}

theorem crys_ext (A₀ : Over (Sp k)) [GrpObj A₀] (hA : IsAbelianScheme A₀)
    {e e' : Crys (divided₂ (GlobalTheory.FODef.sqZero k (Fin d → k))) (spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom) A₀}
    (h : ∀ c, e ((GlobalTheory.FODef.constMorV k (Fin d → k) A₀).pull c) =
      e' ((GlobalTheory.FODef.constMorV k (Fin d → k) A₀).pull c)) : e = e' := by
  have hm := GlobalTheory.SqZeroCrys.isBC_trivSqZeroExt k (Fin d → k) A₀ hA (GlobalTheory.FODef.sqZero k (Fin d → k))
    (GlobalTheory.FODef.constMorV k (Fin d → k) A₀)
  let eqv := LinearEquiv.ofBijective _ hm
  have h1 : ∀ c, (GlobalTheory.FODef.constMorV k (Fin d → k) A₀).pull c = eqv (1 ⊗ₜ c) := fun c =>
    (one_smul (TrivSqZeroExt k (Fin d → k)) ((GlobalTheory.FODef.constMorV k (Fin d → k) A₀).pull c)).symm
  have key : e ∘ₗ eqv.toLinearMap = e' ∘ₗ eqv.toLinearMap := by
    refine TensorProduct.AlgebraTensorModule.ext fun r c => ?_
    have hr : (r ⊗ₜ c : TrivSqZeroExt k (Fin d → k) ⊗[k] primDR A₀) = r • (1 ⊗ₜ c) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, hr, map_smul, ← h1, h c]
  refine LinearMap.ext fun y => ?_
  obtain ⟨t, rfl⟩ := eqv.surjective y
  exact LinearMap.congr_fun key t

theorem crys_pull_smul (A₀ : Over (Sp k)) [GrpObj A₀]
    (e : Crys (divided₂ (GlobalTheory.FODef.sqZero k (Fin d → k))) (spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom) A₀)
    (a : k) (c : primDR A₀) :
    e ((GlobalTheory.FODef.constMorV k (Fin d → k) A₀).pull (a • c)) =
      TrivSqZeroExt.inl a * e ((GlobalTheory.FODef.constMorV k (Fin d → k) A₀).pull c) := by
  rw [LinearMap.map_smulₛₗ]
  exact e.map_smul (algebraMap k (TrivSqZeroExt k (Fin d → k)) a) ((GlobalTheory.FODef.constMorV k (Fin d → k) A₀).pull c)

theorem crys_pull_add (A₀ : Over (Sp k)) [GrpObj A₀]
    (e : Crys (divided₂ (GlobalTheory.FODef.sqZero k (Fin d → k))) (spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom) A₀)
    (a b : primDR A₀) :
    e ((GlobalTheory.FODef.constMorV k (Fin d → k) A₀).pull (a + b)) =
      e ((GlobalTheory.FODef.constMorV k (Fin d → k) A₀).pull a) + e ((GlobalTheory.FODef.constMorV k (Fin d → k) A₀).pull b) := by
  rw [LinearMap.map_add (f := _)]
  exact e.map_add _ _

def fstVal (A₀ : Over (Sp k)) [GrpObj A₀]
    (e : Crys (divided₂ (GlobalTheory.FODef.sqZero k (Fin d → k))) (spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom) A₀) :
    HdR A₀ where
  toFun c := (e ((GlobalTheory.FODef.constMorV k (Fin d → k) A₀).pull c)).fst
  map_add' a b := by
    rw [crys_pull_add]
    rfl
  map_smul' a c := by
    rw [crys_pull_smul]
    simp

def sndVal (A₀ : Over (Sp k)) [GrpObj A₀]
    (e : Crys (divided₂ (GlobalTheory.FODef.sqZero k (Fin d → k))) (spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom) A₀)
    (j : Fin d) : HdR A₀ where
  toFun c := (e ((GlobalTheory.FODef.constMorV k (Fin d → k) A₀).pull c)).snd j
  map_add' a b := by
    rw [crys_pull_add]
    rfl
  map_smul' a c := by
    rw [crys_pull_smul]
    simp

def constSub (A₀ : Over (Sp k)) [GrpObj A₀] (S : Submodule k (HdR A₀)) :
    Submodule (TrivSqZeroExt k (Fin d → k))
      (Crys (divided₂ (GlobalTheory.FODef.sqZero k (Fin d → k))) (spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom) A₀) where
  carrier := {e | ∃ x ∈ S, ∃ z : Fin d → HdR A₀, (∀ j, z j ∈ S) ∧
      ∀ c : primDR A₀, e ((GlobalTheory.FODef.constMorV k (Fin d → k) A₀).pull c) =
        TrivSqZeroExt.inl (x c) + TrivSqZeroExt.inr (fun j => z j c)}
  add_mem' := by
    rintro e e' ⟨x, hx, z, hz, he⟩ ⟨x', hx', z', hz', he'⟩
    refine ⟨x + x', add_mem hx hx', z + z', fun j => add_mem (hz j) (hz' j), fun c => ?_⟩
    rw [LinearMap.add_apply, he c, he' c]
    ext
    · simp
    · simp only [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, Pi.add_apply,
        LinearMap.add_apply, zero_add, add_zero, Pi.zero_apply]
  zero_mem' := ⟨0, zero_mem _, 0, fun _ => zero_mem _, fun c => by rw [LinearMap.zero_apply]; ext <;> simp⟩
  smul_mem' := by
    rintro r e ⟨x, hx, z, hz, he⟩
    refine ⟨r.fst • x, Submodule.smul_mem _ _ hx, fun j => r.fst • z j + r.snd j • x,
      fun j => add_mem (Submodule.smul_mem _ _ (hz j)) (Submodule.smul_mem _ _ hx), fun c => ?_⟩
    rw [LinearMap.smul_apply, he c, smul_eq_mul]
    ext
    · simp
    · simp only [TrivSqZeroExt.snd_mul, TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr,
        TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, Pi.add_apply, Pi.smul_apply,
        LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, add_zero, zero_add,
        MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op, Pi.zero_apply]



theorem mem_sup_of_coords (A₀ : Over (Sp k)) [GrpObj A₀] (hA : IsAbelianScheme A₀)
    (f : Fin d → (HdR A₀ →ₗ[k] HdR A₀)) (M₀ : Submodule k (HdR A₀))
    (e : Crys (divided₂ (GlobalTheory.FODef.sqZero k (Fin d → k))) (spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom) A₀)
    (x₁ m : HdR A₀) (hx₁ : x₁ ∈ Fil A₀) (hm : m ∈ M₀) (hxm : ∀ c, x₁ c + m c = (e ((GlobalTheory.FODef.constMorV k (Fin d → k) A₀).pull c)).fst)
    (z w : Fin d → HdR A₀) (hz : ∀ j, z j ∈ Fil A₀) (hw : ∀ j, w j ∈ M₀)
    (hzw : ∀ j c, z j c + w j c = (e ((GlobalTheory.FODef.constMorV k (Fin d → k) A₀).pull c)).snd j - f j x₁ c) :
    e ∈ glueFil A₀ f ⊔ constSub A₀ M₀ := by
  obtain ⟨g, hg⟩ := exists_coords (Fin d → k) A₀ hA
    ((Algebra.linearMap k (TrivSqZeroExt k (Fin d → k))) ∘ₗ x₁ + (TrivSqZeroExt.inrHom k (Fin d → k)) ∘ₗ
      LinearMap.pi fun j => f j x₁ + z j)
  have hgv : ∀ c, g ((GlobalTheory.FODef.constMorV k (Fin d → k) A₀).pull c) =
      TrivSqZeroExt.inl (x₁ c) + TrivSqZeroExt.inr (fun j => (f j x₁ + z j) c) := fun c => by
    rw [hg c]; ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl]
  have hgm : g ∈ glueFil A₀ f := ⟨x₁, hx₁, z, hz, hgv⟩
  obtain ⟨h, hh⟩ := exists_coords (Fin d → k) A₀ hA
    ((Algebra.linearMap k (TrivSqZeroExt k (Fin d → k))) ∘ₗ m + (TrivSqZeroExt.inrHom k (Fin d → k)) ∘ₗ
      LinearMap.pi fun j => w j)
  have hhv : ∀ c, h ((GlobalTheory.FODef.constMorV k (Fin d → k) A₀).pull c) =
      TrivSqZeroExt.inl (m c) + TrivSqZeroExt.inr (fun j => w j c) := fun c => by
    rw [hh c]; ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl]
  have hhm : h ∈ constSub A₀ M₀ := ⟨m, hm, w, hw, hhv⟩
  refine Submodule.mem_sup.2 ⟨g, hgm, h, hhm, crys_ext A₀ hA fun c => ?_⟩
  rw [LinearMap.add_apply, hgv c, hhv c]
  ext
  · simp only [TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr, add_zero, hxm c]
  · rename_i j
    simp only [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr,
      Pi.add_apply, zero_add, LinearMap.add_apply]
    linear_combination (hzw j c)

theorem isCompl_glueFil (A₀ : Over (Sp k)) [GrpObj A₀] (hA : IsAbelianScheme A₀)
    (f : Fin d → (HdR A₀ →ₗ[k] HdR A₀)) (M₀ : Submodule k (HdR A₀)) (hM : IsCompl (Fil A₀) M₀) :
    IsCompl (glueFil A₀ f) (constSub (d := d) A₀ M₀) := by
  constructor
  · rw [Submodule.disjoint_def]
    rintro e ⟨x, hx, z, hz, he⟩ ⟨m, hm, w, hw, he'⟩
    have hxm : x = m := LinearMap.ext fun c => by
      have := congrArg TrivSqZeroExt.fst ((he c).symm.trans (he' c))
      simpa using this
    have hx0 : x = 0 := by
      rw [← Submodule.mem_bot k, ← hM.inf_eq_bot]
      exact ⟨hx, hxm ▸ hm⟩
    have hzw : ∀ j, z j = w j := fun j => LinearMap.ext fun c => by
      have := congrFun (congrArg TrivSqZeroExt.snd ((he c).symm.trans (he' c))) j
      simpa [hx0] using this
    have hz0 : ∀ j, z j = 0 := fun j => by
      rw [← Submodule.mem_bot k, ← hM.inf_eq_bot]
      exact ⟨hz j, (hzw j) ▸ hw j⟩
    refine crys_ext A₀ hA fun c => ?_
    rw [he c, LinearMap.zero_apply]
    ext <;> simp [hx0, hz0]
  · rw [codisjoint_iff, eq_top_iff]
    rintro e -
    have hdec : ∀ u : HdR A₀, ∃ a ∈ Fil A₀, ∃ b ∈ M₀, a + b = u := fun u => by
      have hu : u ∈ Fil A₀ ⊔ M₀ := by rw [hM.sup_eq_top]; trivial
      rw [Submodule.mem_sup] at hu
      exact hu
    choose pa hpa pb hpb hpab using hdec
    exact mem_sup_of_coords A₀ hA f M₀ e _ _ (hpa _) (hpb _) (fun c => LinearMap.congr_fun (hpab (fstVal A₀ e)) c)
      (fun j => pa (sndVal A₀ e j - f j (pa (fstVal A₀ e))))
      (fun j => pb (sndVal A₀ e j - f j (pa (fstVal A₀ e)))) (fun _ => hpa _) (fun _ => hpb _)
      (fun j c => LinearMap.congr_fun (hpab (sndVal A₀ e j - f j (pa (fstVal A₀ e)))) c)

end GlobalTheory.HTGlue


open GlobalTheory.HTGlue in
theorem GlobalTheory.HTGlue.glueFil_hasCompl : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ Sp R) (o₀ : GlobalTheory.UPel.HT.Obj b N t) (β : R →+* k), t = spMap β → ∀ φ : LinearMap.BilinForm k (HdR o₀.A), GlobalTheory.AbDual.IsCorrForm (dp0 k) (𝟙 _) o₀.A o₀.A o₀.P φ → ∀ (d : ℕ) (f : Fin d → (HdR o₀.A →ₗ[k] HdR o₀.A)), (∀ j, IsKS (GlobalTheory.HTCount.crysAct o₀) φ (Fil o₀.A) (GlobalTheory.HTCount.lieZ o₀ β) (f j)) → (∃ M : Submodule (TrivSqZeroExt k (Fin d → k)) (Crys (divided₂ (GlobalTheory.FODef.sqZero k (Fin d → k))) (spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom) o₀.A), IsCompl (GlobalTheory.HTGlue.glueFil o₀.A f) M) := by
  intro p _ D R _ b N _ _ k _ _ t o₀ β _ φ _ d f _
  obtain ⟨M₀, hM⟩ := Submodule.exists_isCompl (Fil o₀.A)
  exact ⟨_, isCompl_glueFil o₀.A o₀.ab f M₀ hM⟩
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Poinc
open ReciprocityTheory.AnForm.R
open scoped CategoryTheory.Obj

namespace GlobalTheory.BdEqChart

theorem boundary_eq : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (S : Scheme.{0}) [S.IsSeparated] (j : F.X ⟶ S) [IsOpenImmersion j] (R : Type) [CommRing R] [IsRegularLocalRing R] [IsDomain R] [CharZero R] (b : cycAway n →+* R) (ξ : Sp R ⟶ S) (G₁ : Over (Sp R)) [GrpObj G₁] [IsCommMonObj G₁] (y : Sp (FractionRing R) ⟶ F.X) (A₁ : Over (Sp (FractionRing R))) [GrpObj A₁] (i₁ : A₁.left ⟶ G₁.left) (β : A₁.left ⟶ F.univ.A.left), IsSemiAbelian G₁ → IsGrpPullback A₁ G₁ (jK R) i₁ → IsGrpPullback A₁ F.univ.A y β → y ≫ j = jK R ≫ ξ → (∀ I : Ideal (S.presheaf.stalk (ξ (closedPoint R))), I.IsRadical → (I.map (Scheme.stalkClosedPointTo ξ).hom).IsRadical) → ∀ (m : ℕ) (t : Fin m → R), IsRelParam b t → (∀ p : Sp R, p ∈ abLocus G₁ ↔ ∏ k, t k ∉ p.asIdeal) → (∀ p : Sp R, ξ p ∈ Set.range j ↔ ∏ k, t k ∉ p.asIdeal) ∧ idlAlong (Scheme.IdealSheafData.vanishingIdeal j.opensRange.compl) ξ = Ideal.span {∏ k, t k} := by
  intro g n F S _ j _ R _ _ _ _ b ξ G₁ _ _ y A₁ _ i₁ β hG h₁ h₂ hy hrad m t ht hab
  have key : ∀ p : Sp R, ξ p ∈ Set.range j ↔ ∏ k, t k ∉ p.asIdeal := fun p =>
    ⟨fun h => (hab p).1 (GlobalTheory.T.mem_abelianLocus_of_mem_range_siegelModuli_chart g n F S j R ξ G₁ y A₁ i₁ β hG h₁ h₂ hy p h),
     fun h => GlobalTheory.T.abelian_locus_point_mem_range_siegelModuli_openImmersion g n F S j R b ξ G₁ y A₁ i₁ β hG h₁ h₂ hy p ((hab p).2 h)⟩
  refine ⟨key, GlobalTheory.T.idealAlongLocalSpec_vanishingIdeal_compl_eq_span S j.opensRange R ξ _ (GlobalTheory.T.isRadical_span_prod_relativeRegularParameters _ R b m t ht) (fun p => ?_) hrad⟩
  rw [Scheme.Hom.coe_opensRange]
  exact key p

end GlobalTheory.BdEqChart
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt

theorem GlobalTheory.MixHt.arCalc_of_principalisation :
    GlobalTheory.Published.Principalisation → GlobalTheory.Published.ArCalc := fun h =>
  (GlobalTheory.T.arithIntersectionCalculus_cycleHeights_of_analytic (GlobalTheory.T.archLogNormChernIntegrable_of_principalisation h) (GlobalTheory.T.archLogNormReciprocity_of_principalisation h)).1
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_abelianScheme_lift_with_principal_lineBundle : ∀ (R R₀ : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [CommRing R₀] [IsLocalRing R₀] (π : R →+* R₀), Function.Surjective π → RingHom.ker π ^ 2 = ⊥ → ∀ (Y₀ : Over (Sp R₀)) [GrpObj Y₀], IsAbelianScheme Y₀ → ∀ L₀ : LB Y₀.left, L₀.IsLB → RelAmple Y₀ L₀ → KTriv Y₀ L₀ → ∃ (Y : Over (Sp R)) (_ : GrpObj Y) (i : Y₀.left ⟶ Y.left) (l : (Y₀ ⊗ Y₀).left ⟶ (Y ⊗ Y).left) (Q : LB (Y ⊗ Y).left), IsAbelianScheme Y ∧ IsGrpPullback Y₀ Y (spMap π) i ∧ IsSquare i l ∧ Q.IsLB ∧ GlobalTheory.AbDual.IsAdditive Q ∧ GlobalTheory.AbDual.IsAdditive (GlobalTheory.AbDual.swap Q) ∧ LBIso (Q.pull l) (abelian₂ Y₀ L₀) := by
  first | exact @GlobalTheory.AltLift.exists_lift_lam | exact GlobalTheory.AltLift.exists_lift_lam | (intros; apply GlobalTheory.AltLift.exists_lift_lam <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
namespace GlobalTheory

theorem potModel_of_divAlg_leftAction : ∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] [Field K] [CharZero K] [Algebra V K] [IsFractionRing V K] (A : Over (Sp K)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ (O : Type) [Ring O] (act : O → (A ⟶ A)), (∀ a, IsMonHom (act a)) → act 1 = 𝟙 A → (∀ a b, act (a * b) = act b ≫ act a) → (∀ a b, act (a + b) = act a * act b) → ∀ (B : Type) [Ring B] [Algebra ℚ B] [Module.Finite ℚ B] (jj : O →+* B), (∀ x : B, x ≠ 0 → IsUnit x) → Function.Injective jj → Submodule.span ℚ (Set.range jj) = ⊤ → g < Module.finrank ℚ B → GlobalTheory.SS.PotModel V K A (fun _ _ _ G _ => IsAbelianScheme G) := by
  intro V K _ _ _ _ _ _ _ _ A _ g hA hg O _ act hmon h1 hmul hadd B _ _ _ jj hunit hinj hspan hdim
  haveI : Module.Finite ℚ Bᵐᵒᵖ :=
    Module.Finite.equiv (MulOpposite.opLinearEquiv ℚ (M := B))
  refine GlobalTheory.T.potentialGoodReduction_of_divisionAlgebra_order_action V K A g hA hg Oᵐᵒᵖ (fun a => act a.unop) (fun a => hmon a.unop) h1
    (fun a b => hmul b.unop a.unop) (fun a b => hadd a.unop b.unop) Bᵐᵒᵖ (RingHom.op jj)
    ?_ ?_ ?_ ?_
  · intro x hx
    have hx' : x.unop ≠ 0 := by simpa using hx
    simpa using (hunit x.unop hx').op
  · intro a b h
    exact MulOpposite.unop_injective (hinj (MulOpposite.op_injective h))
  · have : Set.range (RingHom.op jj) = (MulOpposite.opLinearEquiv ℚ (M := B)) '' Set.range jj := by
      ext x; constructor
      · rintro ⟨a, rfl⟩; exact ⟨jj a.unop, ⟨a.unop, rfl⟩, rfl⟩
      · rintro ⟨_, ⟨a, rfl⟩, rfl⟩; exact ⟨MulOpposite.op a, rfl⟩
    rw [this, ← LinearEquiv.coe_coe, Submodule.span_image, hspan, Submodule.map_top, LinearEquiv.range]
  · rwa [(MulOpposite.opLinearEquiv ℚ (M := B)).symm.finrank_eq]

end GlobalTheory
end
