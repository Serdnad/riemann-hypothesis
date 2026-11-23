module

public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle009
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle018
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1767
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.Bundle006
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1768
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyNormFinLeOne
import Development.AbelianVarietyTheory.Definitions.Foundations.NormEulerPolySubOneLe
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.LinearIndependentWave
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle029
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle011
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveAlgebraisationFormalCompleteLoca
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle013
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle050
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle004
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1610
import Formalism.LocalToGlobal.IndefiniteForms.IndefSide
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.SelfDualFirstProj

variable {F : Type} [Field F] [NumberField F] (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F))

instance charZero_Fv : CharZero (Fv F v) :=
  (RingHom.charZero_iff (algebraMap F (Fv F v)).injective).1 inferInstance

theorem isOpen_integers : IsOpen ((v.adicCompletionIntegers F : Set (Fv F v))) :=
  Valued.isOpen_valuationSubring _

theorem exists_nat_mem (c : Fv F v) (hc : c ≠ 0) :
    ∃ n : ℕ, 0 < n ∧ c⁻¹ * (n : Fv F v) ∈ v.adicCompletionIntegers F := by
  haveI := GlobalTheory.AdelicUnitaryTop.compactSpace_adicCompletionIntegers F v
  let O := v.adicCompletionIntegers F
  let S : AddSubgroup (Fv F v) := (O.toSubring.toAddSubgroup).comap (AddMonoidHom.mulLeft c⁻¹)
  let H : AddSubgroup O := S.comap (O.toSubring.subtype.toAddMonoidHom)
  have hS : IsOpen (S : Set (Fv F v)) :=
    (isOpen_integers v).preimage (continuous_const.mul continuous_id)
  have hH : IsOpen (H : Set O) := hS.preimage continuous_subtype_val
  let H' : OpenAddSubgroup O := ⟨H, hH⟩
  have : Finite (O ⧸ H) := AddSubgroup.instFiniteQuotientOfSeparatelyContinuousAddOfCompactSpace H'
  have hne : H.index ≠ 0 := AddSubgroup.index_ne_zero_of_finite
  refine ⟨H.index, Nat.pos_of_ne_zero hne, ?_⟩
  have hm := H.nsmul_index_mem (1 : O)
  simpa [H, S] using hm

theorem exists_finite_residues (n : ℕ) (hn : 0 < n) :
    ∃ R : Set (Fv F v), R.Finite ∧ ∀ y ∈ v.adicCompletionIntegers F,
      ∃ r ∈ R, ∃ u ∈ v.adicCompletionIntegers F, y = r + (n : Fv F v) * u := by
  haveI := GlobalTheory.AdelicUnitaryTop.compactSpace_adicCompletionIntegers F v
  let U : Set (Fv F v) := (v.adicCompletionIntegers F : Set (Fv F v))
  have hUo : IsOpen U := isOpen_integers v
  have hUc : IsCompact U := isCompact_iff_compactSpace.mpr inferInstance
  have hc : (n : Fv F v) ≠ 0 := by exact_mod_cast hn.ne'
  let V : U → Set (Fv F v) := fun x => (fun y => (y - (x : Fv F v)) * (n : Fv F v)⁻¹) ⁻¹' U
  have hVo : ∀ x, IsOpen (V x) := fun x =>
    hUo.preimage ((continuous_id.sub continuous_const).mul continuous_const)
  have hcov : U ⊆ ⋃ x, V x := by
    intro y hy
    refine Set.mem_iUnion.2 ⟨⟨y, hy⟩, ?_⟩
    show (y - y) * (n : Fv F v)⁻¹ ∈ U
    rw [sub_self, zero_mul]
    exact (v.adicCompletionIntegers F).zero_mem
  obtain ⟨t, ht⟩ := hUc.elim_finite_subcover V hVo hcov
  refine ⟨(fun x : U => (x : Fv F v)) '' (t : Set U), (t.finite_toSet).image _, ?_⟩
  intro y hy
  have := ht hy
  simp only [Set.mem_iUnion] at this
  obtain ⟨x, hxt, hyx⟩ := this
  refine ⟨x, ⟨x, hxt, rfl⟩, (y - (x : Fv F v)) * (n : Fv F v)⁻¹, hyx, ?_⟩
  field_simp
  ring

theorem exists_finite_residues_pi {κ : Type} [Fintype κ] (n : ℕ) (hn : 0 < n) :
    ∃ R : Set (κ → Fv F v), R.Finite ∧ ∀ t : κ → Fv F v, (∀ i, t i ∈ v.adicCompletionIntegers F) →
      ∃ r ∈ R, ∃ u : κ → Fv F v, (∀ i, u i ∈ v.adicCompletionIntegers F) ∧ t = r + n • u := by
  obtain ⟨R, hR, h⟩ := exists_finite_residues v n hn
  haveI := hR.to_subtype
  refine ⟨Set.range (fun f : κ → R => fun i => (f i : Fv F v)), Set.finite_range _, ?_⟩
  intro t ht
  choose r hr u hu hru using fun i => h (t i) (ht i)
  refine ⟨fun i => r i, ⟨fun i => ⟨r i, hr i⟩, rfl⟩, u, hu, ?_⟩
  funext i
  simp only [Pi.add_apply, Pi.smul_apply, nsmul_eq_mul]
  exact hru i

theorem exists_pair_of_annihilator : ∀ {F : Type} [Field F] [NumberField F] (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) {κ : Type} [Fintype κ]
    [DecidableEq κ] (ψk : AddChar (Fv F v) ℂ) (Λ : AddSubgroup ((κ → Fv F v) × (κ → Fv F v))) (c : Fv F v), c ≠ 0 →
    (∀ x : Fv F v, (∀ y ∈ v.adicCompletionIntegers F, ψk (x * y) = 1) ↔ x ∈ v.adicCompletionIntegers F) →
    (∀ w, w ∈ Λ ↔ ∀ l ∈ Λ, ψk (w.1 ⬝ᵥ l.2 - l.1 ⬝ᵥ w.2) = 1) →
    (∀ l ∈ Λ, ∀ i, c * l.1 i ∈ v.adicCompletionIntegers F ∧ c * l.2 i ∈ v.adicCompletionIntegers F) →
    ∀ η : κ → Fv F v, (∀ b : κ → Fv F v, ((0 : κ → Fv F v), b) ∈ Λ → ψk (η ⬝ᵥ b) = 1) → ∃ y, (η, y) ∈ Λ := by
  intro F _ _ v κ _ _ ψk Λ c hc hψ hself hbd η hη
  let O := v.adicCompletionIntegers F
  have ψ1 : ∀ x : Fv F v, x ∈ O → ψk x = 1 := fun x hx => by
    simpa using (hψ x).2 hx 1 O.one_mem
  have dotO : ∀ u w : κ → Fv F v, (∀ i, u i ∈ O) → (∀ i, w i ∈ O) → u ⬝ᵥ w ∈ O := by
    intro u w hu hw
    exact O.toSubring.sum_mem fun i _ => O.toSubring.mul_mem (hu i) (hw i)
  let L₀ : AddSubgroup (κ → Fv F v) := AddSubgroup.pi Set.univ (fun _ => O.toSubring.toAddSubgroup)
  have hL₀ : ∀ x, x ∈ L₀ ↔ ∀ i, x i ∈ O := fun x => by
    simp [L₀, AddSubgroup.mem_pi]
  let P : AddSubgroup (κ → Fv F v) := Λ.map (AddMonoidHom.fst _ _)
  have hP : ∀ x, x ∈ P ↔ ∃ y, (x, y) ∈ Λ := fun x => by
    simp only [P, AddSubgroup.mem_map, AddMonoidHom.coe_fst]
    constructor
    · rintro ⟨l, hl, rfl⟩; exact ⟨l.2, hl⟩
    · rintro ⟨y, hy⟩; exact ⟨(x, y), hy, rfl⟩

  have LB : ∀ u₁ u₂ : κ → Fv F v, (∀ i, u₁ i ∈ O) → (∀ i, u₂ i ∈ O) → (c • u₁, c • u₂) ∈ Λ := by
    intro u₁ u₂ h₁ h₂
    refine (hself _).2 fun l hl => ψ1 _ ?_
    have e1 : (c • u₁) ⬝ᵥ l.2 = u₁ ⬝ᵥ (c • l.2) := by rw [smul_dotProduct, dotProduct_smul]
    have e2 : l.1 ⬝ᵥ (c • u₂) = (c • l.1) ⬝ᵥ u₂ := by rw [smul_dotProduct, dotProduct_smul]
    simp only
    rw [e1, e2]
    exact O.toSubring.sub_mem (dotO _ _ h₁ fun i => (hbd l hl i).2) (dotO _ _ (fun i => (hbd l hl i).1) h₂)
  have hsingle : ∀ i (t : Fv F v), t ∈ O → ∀ j, (Pi.single i t : κ → Fv F v) j ∈ O := by
    intro i t ht j
    by_cases h : j = i
    · subst h; simpa using ht
    · simp [Pi.single_apply, h, O.zero_mem]

  have hcη : ∀ i, c * η i ∈ O := by
    intro i
    refine (hψ _).1 fun t ht => ?_
    have hb : ((0 : κ → Fv F v), c • Pi.single i t) ∈ Λ := by
      have := LB 0 (Pi.single i t) (fun _ => O.zero_mem) (hsingle i t ht)
      simpa using this
    have := hη _ hb
    rwa [dotProduct_smul, dotProduct_single, smul_eq_mul, ← mul_assoc] at this
  obtain ⟨N, hN, hNc⟩ := GlobalTheory.SelfDualFirstProj.exists_nat_mem v c hc
  have hNeq : ∀ z : Fv F v, (N : Fv F v) * z = (c⁻¹ * N) * (c * z) := fun z => by
    field_simp
  have bich : GlobalTheory.PlaceModel.IsBichar (fun x y : κ → Fv F v => ψk (x ⬝ᵥ y)) :=
    ⟨fun a b y => by simp only [add_dotProduct, AddChar.map_add_eq_mul],
     fun a y z => by simp only [dotProduct_add, AddChar.map_add_eq_mul],
     fun y => by simp, fun a => by simp⟩
  have hmem : η ∈ P := by
    refine GlobalTheory.DualTransfer.mem_of_double_annihilator (fun x y => ψk (x ⬝ᵥ y)) bich ⊤ ⊤ L₀ L₀ P
      le_top le_top le_top ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ N hN ?_ ?_ η trivial ?_ ?_
    · intro u hu y hy
      exact ψ1 _ (dotO _ _ ((hL₀ u).1 hu) ((hL₀ y).1 hy))
    · intro x _ h
      refine (hL₀ x).2 fun i => (hψ _).1 fun t ht => ?_
      have := h (Pi.single i t) ((hL₀ _).2 (hsingle i t ht))
      rwa [dotProduct_single] at this
    · intro y _ h
      refine (hL₀ y).2 fun i => (hψ _).1 fun t ht => ?_
      have := h (Pi.single i t) ((hL₀ _).2 (hsingle i t ht))
      rwa [single_dotProduct, mul_comm] at this
    · intro k hk x _
      refine ⟨((k : Fv F v)⁻¹) • x, trivial, ?_⟩
      have hk0 : (k : Fv F v) ≠ 0 := by exact_mod_cast hk.ne'
      rw [← Nat.cast_smul_eq_nsmul (Fv F v), smul_smul, mul_inv_cancel₀ hk0, one_smul]
    · intro k hk x _
      refine ⟨((k : Fv F v)⁻¹) • x, trivial, ?_⟩
      have hk0 : (k : Fv F v) ≠ 0 := by exact_mod_cast hk.ne'
      rw [← Nat.cast_smul_eq_nsmul (Fv F v), smul_smul, mul_inv_cancel₀ hk0, one_smul]
    · intro k hk t t' h
      have hk0 : (k : Fv F v) ≠ 0 := by exact_mod_cast hk.ne'
      funext i
      have := congrFun h i
      simp only [Pi.smul_apply, nsmul_eq_mul] at this
      exact mul_left_cancel₀ hk0 this
    · intro k hk
      obtain ⟨R, hR, h⟩ := GlobalTheory.SelfDualFirstProj.exists_finite_residues_pi (κ := κ) v k hk
      exact ⟨R, hR, fun t ht => by
        obtain ⟨r, hr, u, hu, e⟩ := h t ((hL₀ t).1 ht)
        exact ⟨r, hr, u, (hL₀ u).2 hu, e⟩⟩
    · intro k hk
      obtain ⟨R, hR, h⟩ := GlobalTheory.SelfDualFirstProj.exists_finite_residues_pi (κ := κ) v k hk
      exact ⟨R, hR, fun t ht => by
        obtain ⟨r, hr, u, hu, e⟩ := h t ((hL₀ t).1 ht)
        exact ⟨r, hr, u, (hL₀ u).2 hu, e⟩⟩
    · intro u hu
      have hu' := (hL₀ u).1 hu
      refine (hP _).2 ⟨c • (0 : κ → Fv F v), ?_⟩
      have := LB ((c⁻¹ * N) • u) 0 (fun i => O.toSubring.mul_mem hNc (hu' i)) (fun _ => O.zero_mem)
      convert this using 2
      rw [smul_smul, ← Nat.cast_smul_eq_nsmul (Fv F v)]
      congr 1
      field_simp
    · intro u hu
      obtain ⟨y, hy⟩ := (hP u).1 hu
      refine (hL₀ _).2 fun i => ?_
      simp only [Pi.smul_apply, nsmul_eq_mul]
      rw [hNeq]
      exact O.toSubring.mul_mem hNc (hbd _ hy i).1
    · refine (hL₀ _).2 fun i => ?_
      simp only [Pi.smul_apply, nsmul_eq_mul]
      rw [hNeq]
      exact O.toSubring.mul_mem hNc (hcη i)
    · intro y _ h
      refine hη y ((hself _).2 fun l hl => ?_)
      simp only [zero_dotProduct, zero_sub, AddChar.map_neg_eq_inv]
      rw [h l.1 ((hP _).2 ⟨l.2, hl⟩), inv_one]
  obtain ⟨y, hy⟩ := (hP η).1 hmem
  exact ⟨y, hy⟩

end GlobalTheory.SelfDualFirstProj
end
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.smoothOfRelativeDimension_finite_surjective_abelianVariety : ∀ (K : Type) [Field K] [IsAlgClosed K] (A A' : Over (Sp K)) [GrpObj A] [GrpObj A'] (g : ℕ) (q : A ⟶ A'), IsAbelianScheme A → IsAbelianScheme A' → IsFinite q.left → Surjective q.left → SmoothOfRelativeDimension g A.hom → SmoothOfRelativeDimension g A'.hom := by
  first | exact @GlobalTheory.FiniteSurjDimField.smoothOfRelativeDimension_of_finite_surjective | exact GlobalTheory.FiniteSurjDimField.smoothOfRelativeDimension_of_finite_surjective | (intros; apply GlobalTheory.FiniteSurjDimField.smoothOfRelativeDimension_of_finite_surjective <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.FormalAlg GlobalTheory.Degen.FormalEmb

namespace GlobalTheory.FramesBundle

theorem cg_cancel {G : Type} [CommGroup G] (a b c : G) : (a * b) * (a * c)⁻¹ = b * c⁻¹ := by
  apply Additive.ofMul.injective; simp only [ofMul_mul, ofMul_inv]; abel

theorem cg_cocycle {G : Type} [CommGroup G] (a b c : G) : (b * a⁻¹) * (c * b⁻¹) = c * a⁻¹ := by
  apply Additive.ofMul.injective; simp only [ofMul_mul, ofMul_inv]; abel

theorem cg_gen {G : Type} [CommGroup G] (a g c : G) : a⁻¹ = ((g * c) * a⁻¹ * g⁻¹) * c⁻¹ := by
  apply Additive.ofMul.injective; simp only [ofMul_mul, ofMul_inv]; abel

theorem frames_bundle : ∀ (X : Scheme.{0}) (L : LB X), L.IsLB → ∀ (n : ℕ) (D : Fin (n + 1) → X.Opens), ⨆ i, D i = ⊤ → ∀ (τ : ∀ (i : Fin (n + 1)) (m : L.ι), Γ(X, D i ⊓ L.U m)ˣ), (∀ i x m m', x ∈ D i ⊓ L.U m → x ∈ D i ⊓ L.U m' → gm (𝟙 X) x _ (τ i m) = gm (𝟙 X) x _ (L.g m m') * gm (𝟙 X) x _ (τ i m')) → ∃ g : ∀ i j, Γ(X, D i ⊓ D j)ˣ, (⟨Fin (n + 1), D, g⟩ : LB X).IsLB ∧ LBIso L ⟨Fin (n + 1), D, g⟩ ∧ ∀ i j m, res (inf_le_left : D i ⊓ D j ⊓ L.U m ≤ D i ⊓ D j) (g i j) = res (le_inf (inf_le_left.trans inf_le_right) inf_le_right : D i ⊓ D j ⊓ L.U m ≤ D j ⊓ L.U m) (τ j m) * (res (le_inf (inf_le_left.trans inf_le_left) inf_le_right : D i ⊓ D j ⊓ L.U m ≤ D i ⊓ L.U m) (τ i m))⁻¹ := by
  intro X L hL n D hD τ hτ
  have hg : ∀ i j, ∃ s : Γ(X, D i ⊓ D j)ˣ, ∀ m,
      res (inf_le_left : D i ⊓ D j ⊓ L.U m ≤ D i ⊓ D j) s =
        res (le_inf (inf_le_left.trans inf_le_right) inf_le_right : D i ⊓ D j ⊓ L.U m ≤ D j ⊓ L.U m) (τ j m) *
          (res (le_inf (inf_le_left.trans inf_le_left) inf_le_right : D i ⊓ D j ⊓ L.U m ≤ D i ⊓ L.U m) (τ i m))⁻¹ := by
    intro i j
    refine glue_unit (D i ⊓ D j) (fun m => D i ⊓ D j ⊓ L.U m) (fun m => inf_le_left) ?_ _ ?_
    · intro x hx
      obtain ⟨m, hm⟩ := exists_chart hL x
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨m, ⟨hx, hm⟩⟩
    · intro m m' x hx
      rw [map_mul, map_mul, map_inv, map_inv, gm_res _ x _ hx.1, gm_res _ x _ hx.1, gm_res _ x _ hx.2,
        gm_res _ x _ hx.2, hτ j x m m' ⟨hx.1.1.2, hx.1.2⟩ ⟨hx.2.1.2, hx.2.2⟩,
        hτ i x m m' ⟨hx.1.1.1, hx.1.2⟩ ⟨hx.2.1.1, hx.2.2⟩, cg_cancel]
  choose g hg' using hg
  have key : ∀ i j m x, x ∈ D i ⊓ D j ⊓ L.U m →
      gm (𝟙 X) x (D i ⊓ D j) (g i j) = gm (𝟙 X) x (D j ⊓ L.U m) (τ j m) * (gm (𝟙 X) x (D i ⊓ L.U m) (τ i m))⁻¹ := by
    intro i j m x hx
    rw [← gm_res _ x (inf_le_left : D i ⊓ D j ⊓ L.U m ≤ D i ⊓ D j) hx, hg' i j m, map_mul, map_inv,
      gm_res _ x _ hx, gm_res _ x _ hx]
  refine ⟨g, ⟨hD, ?_, ?_⟩, ⟨⟨fun p => (τ p.1 p.2)⁻¹⟩, ?_⟩, hg'⟩
  · intro i
    apply unit_ext
    intro x hx
    rw [gm_res _ x _ hx, map_one]
    obtain ⟨m, hm⟩ := exists_chart hL x
    exact (key i i m x ⟨⟨hx, hx⟩, hm⟩).trans (mul_inv_cancel _)
  · intro i j k
    apply unit_ext
    intro x hx
    rw [map_mul, gm_res _ x _ hx, gm_res _ x _ hx, gm_res _ x _ hx]
    obtain ⟨m, hm⟩ := exists_chart hL x
    have h1 := key i j m x ⟨⟨hx.1.1, hx.1.2⟩, hm⟩
    have h2 := key j k m x ⟨⟨hx.1.2, hx.2⟩, hm⟩
    have h3 := key i k m x ⟨⟨hx.1.1, hx.2⟩, hm⟩
    exact (congrArg₂ (· * ·) h1 h2).trans ((cg_cocycle _ _ _).trans h3.symm)
  · rintro ⟨i, m⟩ ⟨j, m'⟩
    apply unit_ext
    intro x hx
    have hx' : x ∈ D i ⊓ L.U m ⊓ (D j ⊓ L.U m') := hx
    have eL : ∀ h : D i ⊓ L.U m ⊓ (D j ⊓ L.U m') ≤ D i ⊓ L.U m,
        gm (𝟙 X) x (D i ⊓ L.U m ⊓ (D j ⊓ L.U m')) (res h (τ i m)⁻¹) = (gm (𝟙 X) x _ (τ i m))⁻¹ := by
      intro h
      rw [map_inv, map_inv, gm_res _ x _ hx']
    have eR : ∀ (h1 : D i ⊓ L.U m ⊓ (D j ⊓ L.U m') ≤ D i ⊓ D j) (h2 : D i ⊓ L.U m ⊓ (D j ⊓ L.U m') ≤ L.U m ⊓ L.U m')
        (h3 : D i ⊓ L.U m ⊓ (D j ⊓ L.U m') ≤ D j ⊓ L.U m'),
        gm (𝟙 X) x (D i ⊓ L.U m ⊓ (D j ⊓ L.U m')) (res h1 (g i j) * (res h2 (L.g m m'))⁻¹ * res h3 (τ j m')⁻¹) =
          gm (𝟙 X) x _ (g i j) * (gm (𝟙 X) x _ (L.g m m'))⁻¹ * (gm (𝟙 X) x _ (τ j m'))⁻¹ := by
      intro h1 h2 h3
      rw [map_mul, map_mul, map_inv, map_inv, map_inv, gm_res _ x _ hx', gm_res _ x _ hx', gm_res _ x _ hx']
    have h1 := key i j m x ⟨⟨hx'.1.1, hx'.2.1⟩, hx'.1.2⟩
    have h2 := hτ j x m m' ⟨hx'.2.1, hx'.1.2⟩ ⟨hx'.2.1, hx'.2.2⟩
    refine (eL _).trans (Eq.trans ?_ (eR _ _ _).symm)
    rw [h1, h2]
    exact cg_gen _ _ _

end GlobalTheory.FramesBundle
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar GlobalTheory.LiftRows GlobalTheory.LowRow

theorem _root_.GlobalTheory.T.standardMeasure_unitaryPQ_eq_volume_smul_compactDual : ∀ (cd : CDHaar) (p q : ℕ) (m : Measure (UpqT p q)), Lev.IsMinf m → m = ENNReal.ofReal (ReciprocityTheory.ChartRestriction.DS.volU (p + q)) • cd.cd p q := by
  first | exact @GlobalTheory.LowRow.CompactDualScale.isMinf_eq_volU_smul_cd | exact GlobalTheory.LowRow.CompactDualScale.isMinf_eq_volU_smul_cd | (intros; apply GlobalTheory.LowRow.CompactDualScale.isMinf_eq_volU_smul_cd <;> assumption)
end
