module

public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle001
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle017
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle013
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle036
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoIffBijectiveOverAlgClosed
public import Formalism.ConjugateSelfDual.Bundle001
public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Topology.Instances.Matrix
public import Formalism.LocalRingCardinality.SpanPowerMembership.Bundle006
public import Formalism.LocalToGlobal.CMDeterminantIdeals.DetIdeal
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Valuation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle578
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoeffZeroNeOfMonicIrr
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StarCoeffEisensteinSeriesReversePoly
public import Formalism.PadicSubsetSums.CentralIdempotents.Bundle001
public import Formalism.RealPlaceAnalysis.SmoothOnGVIff
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle579
public import Mathlib.Algebra.Module.Projective
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle539
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle581
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Limits.Shapes.Connected
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle367
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EmbGLMemRealSU
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle005
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle012
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle005
import Mathlib.RingTheory.MvPowerSeries.Basic
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle013
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.StTransl

@[expose] public section

section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped NumberField CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IwLevel.CoprimeTors

theorem isIsogDeg_of_coprime : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (O : Type) [CommRing O]
    (ρ : ReciprocityTheory.ChartRestriction.G.Out.RingAct A O) (𝔞 𝔟 : Ideal O), 𝔞 ⊔ 𝔟 = ⊤ →
    ∀ (K₁ K₂ K₃ : Over S) (i₁ : K₁ ⟶ A) (i₂ : K₂ ⟶ A) (i₃ : K₃ ⟶ A), Mono i₁ → Mono i₂ → Mono i₃ →
    (∀ (T : Over S) (x : T ⟶ A), GlobalTheory.IwLevel.InSub i₁ x ↔ GlobalTheory.IwLevel.KilledBy ρ 𝔞 x) →
    (∀ (T : Over S) (x : T ⟶ A), GlobalTheory.IwLevel.InSub i₂ x ↔ GlobalTheory.IwLevel.KilledBy ρ 𝔟 x) →
    (∀ (T : Over S) (x : T ⟶ A), GlobalTheory.IwLevel.InSub i₃ x ↔ GlobalTheory.IwLevel.KilledBy ρ (𝔞 * 𝔟) x) →
    ∀ (d e : ℕ), 0 < e → GlobalTheory.IwLevel.IsIsogDeg (toUnit K₃) (d * e) → GlobalTheory.IwLevel.IsIsogDeg (toUnit K₂) e →
    GlobalTheory.IwLevel.IsIsogDeg (toUnit K₁) d := by
  intro S A _ _ O _ ρ 𝔞 𝔟 hab K₁ K₂ K₃ i₁ i₂ i₃ _ _ _ h₁ h₂ h₃ d e he hK₃ hK₂
  have h1mem : (1 : O) ∈ 𝔞 ⊔ 𝔟 := hab ▸ Submodule.mem_top
  obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.1 h1mem
  have k₁ : ∀ a ∈ 𝔞, i₁ ≫ ρ.act a = 1 := fun a ha => (h₁ K₁ i₁).1 ⟨𝟙 _, Category.id_comp _⟩ a ha
  have k₂ : ∀ a ∈ 𝔟, i₂ ≫ ρ.act a = 1 := fun a ha => (h₂ K₂ i₂).1 ⟨𝟙 _, Category.id_comp _⟩ a ha
  have k₃ : ∀ a ∈ 𝔞 * 𝔟, i₃ ≫ ρ.act a = 1 := fun a ha => (h₃ K₃ i₃).1 ⟨𝟙 _, Category.id_comp _⟩ a ha
  have hadd : ∀ {T : Over S} (x : T ⟶ A) (a b : O),
      x ≫ ρ.act (a + b) = (x ≫ ρ.act a) * (x ≫ ρ.act b) := fun x a b => by
    rw [ρ.map_add]; exact MonObj.comp_mul x _ _
  have hone : ∀ {T : Over S} (x : T ⟶ A), x ≫ ρ.act 1 = x := fun x => by
    rw [ρ.map_one, Category.comp_id]
  have e₁ : i₁ ≫ ρ.act v = i₁ := by
    have := hadd i₁ v u
    rw [add_comm v u, huv, hone, k₁ u hu, _root_.mul_one] at this
    exact this.symm
  have e₂ : i₂ ≫ ρ.act u = i₂ := by
    have := hadd i₂ u v
    rw [huv, hone, k₂ v hv, _root_.mul_one] at this
    exact this.symm
  have hm : GlobalTheory.IwLevel.KilledBy ρ (𝔞 * 𝔟) ((fst K₁ K₂ ≫ i₁) * (snd K₁ K₂ ≫ i₂)) := fun c hc => by
    have := ρ.hom c
    have hc₁ : c ∈ 𝔞 := Ideal.mul_le_left (I := 𝔞) (J := 𝔟) hc
    have hc₂ : c ∈ 𝔟 := Ideal.mul_le_right (I := 𝔞) (J := 𝔟) hc
    rw [MonObj.mul_comp, Category.assoc, Category.assoc, k₁ c hc₁, k₂ c hc₂, MonObj.comp_one,
      MonObj.comp_one, _root_.mul_one]
  obtain ⟨m, hm'⟩ := (h₃ _ _).2 hm
  have hg₁ : GlobalTheory.IwLevel.KilledBy ρ 𝔞 (i₃ ≫ ρ.act v) := fun a ha => by
    rw [Category.assoc, ← ρ.map_mul]; exact k₃ _ (Ideal.mul_mem_mul ha hv)
  have hg₂ : GlobalTheory.IwLevel.KilledBy ρ 𝔟 (i₃ ≫ ρ.act u) := fun b hb => by
    rw [Category.assoc, ← ρ.map_mul, mul_comm]; exact k₃ _ (Ideal.mul_mem_mul hu hb)
  obtain ⟨g₁, hg₁'⟩ := (h₁ _ _).2 hg₁
  obtain ⟨g₂, hg₂'⟩ := (h₂ _ _).2 hg₂
  have iso : IsIso m := by
    refine ⟨⟨lift g₁ g₂, ?_, ?_⟩⟩
    · have hr := ρ.hom v
      have hs := ρ.hom u
      apply CartesianMonoidalCategory.hom_ext
      · rw [Category.assoc, lift_fst, Category.id_comp, ← cancel_mono i₁, Category.assoc, hg₁',
          ← Category.assoc, hm', MonObj.mul_comp, Category.assoc, Category.assoc, e₁, k₂ v hv,
          MonObj.comp_one, _root_.mul_one]
      · rw [Category.assoc, lift_snd, Category.id_comp, ← cancel_mono i₂, Category.assoc, hg₂',
          ← Category.assoc, hm', MonObj.mul_comp, Category.assoc, Category.assoc, e₂, k₁ u hu,
          MonObj.comp_one, _root_.one_mul]
    · rw [← cancel_mono i₃, Category.assoc, hm', MonObj.comp_mul, ← Category.assoc, lift_fst,
        ← Category.assoc, lift_snd, hg₁', hg₂', ← hadd, add_comm, huv, hone, Category.id_comp]
  have hP : GlobalTheory.IwLevel.IsIsogDeg (toUnit (K₁ ⊗ K₂)) (d * e) := by
    rw [toUnit_unique (toUnit (K₁ ⊗ K₂)) (m ≫ toUnit K₃), ← _root_.one_mul (d * e)]
    exact (GlobalTheory.IwLevel.IsIsogDeg.of_isIso m).comp hK₃
  have hpb : IsPullback (fst K₁ K₂) (snd K₁ K₂) (toUnit K₁) (toUnit K₂) :=
    ⟨⟨toUnit_unique _ _⟩, ⟨PullbackCone.IsLimit.mk _ (fun c ↦ lift c.fst c.snd) (fun _ ↦ lift_fst _ _)
      (fun _ ↦ lift_snd _ _) fun c m h₁ h₂ ↦ by ext <;> simp [h₁, h₂]⟩⟩
  have hfst : GlobalTheory.IwLevel.IsIsogDeg (fst K₁ K₂) e := hK₂.of_isPullback (hpb.flip.map (Over.forget S))
  have hcomp : fst K₁ K₂ ≫ toUnit K₁ = toUnit (K₁ ⊗ K₂) := toUnit_unique _ _
  have := hfst.fin; have := hfst.flat; have := hfst.surj
  have := hP.fin; have := hP.flat; have := hP.surj

  obtain ⟨t, -⟩ := (h₂ K₁ (1 : K₁ ⟶ A)).2 fun b _ => by have := ρ.hom b; exact MonObj.one_comp _
  let s : K₁ ⟶ K₁ ⊗ K₂ := lift (𝟙 K₁) t
  have hs : s ≫ fst K₁ K₂ = 𝟙 K₁ := lift_fst _ _
  have hsep : IsSeparated (fst K₁ K₂).left := inferInstance
  have : IsFinite (s.left ≫ (fst K₁ K₂).left) := by
    rw [← Over.comp_left, hs, Over.id_left]; infer_instance
  have : IsFinite s.left := IsFinite.of_comp s.left (fst K₁ K₂).left
  have hsu : s ≫ toUnit (K₁ ⊗ K₂) = toUnit K₁ := toUnit_unique _ _
  have hfin : IsFinite (toUnit K₁).left := by rw [← hsu, Over.comp_left]; infer_instance
  have : Flat ((fst K₁ K₂).left ≫ (toUnit K₁).left) := by rw [← Over.comp_left, hcomp]; infer_instance
  have hflat : Flat (toUnit K₁).left := flat_of_comp_of_flat_of_surjective (fst K₁ K₂).left _
  have : Surjective ((fst K₁ K₂).left ≫ (toUnit K₁).left) := by
    rw [← Over.comp_left, hcomp]; infer_instance
  have hsurj : Surjective (toUnit K₁).left := Surjective.of_comp (fst K₁ K₂).left _
  refine ⟨hfin, hflat, hsurj, fun y => ?_⟩
  have h := GlobalTheory.FinrankComp.finrank_comp_of_const (fst K₁ K₂).left (toUnit K₁).left e hfst.rank y
  rw [← Over.comp_left, hcomp, hP.rank, mul_comm d e] at h
  exact (Nat.eq_of_mul_eq_mul_left he h).symm

end GlobalTheory.IwLevel.CoprimeTors
end
end

section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped NumberField CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.FinEtRank.isIsogDeg_of_card :
  ∀ {S : Scheme.{0}} (A K : Over S) (i : K ⟶ A), Mono i → IsFinite K.hom → Etale K.hom → ∀ (d : ℕ), 1 ≤ d → (∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ S), Nat.card {y : Over.mk t ⟶ A // GlobalTheory.IwLevel.InSub i y} = d) → GlobalTheory.IwLevel.IsIsogDeg (toUnit K) d := by
  intro S A K i hi hfin het d hd hcard
  have h : (toUnit K).left = K.hom := by simpa using Over.w (toUnit K)
  have hrank : ∀ s : S, K.hom.finrank s = d := by
    intro s
    obtain ⟨k, _, _, t, ht⟩ := GlobalTheory.FinEt.exists_algClosed_point S s
    obtain ⟨z, rfl⟩ : s ∈ Set.range t := by rw [ht]; rfl
    obtain ⟨-, hc⟩ := GlobalTheory.FinEt.card_points_eq_finrank K.hom t z
    rw [← hc, ← hcard k t]
    refine Nat.card_congr (Equiv.ofBijective (fun x => ⟨Over.homMk x.1 x.2 ≫ i, ⟨Over.homMk x.1 x.2, rfl⟩⟩) ⟨?_, ?_⟩)
    · rintro ⟨a, ha⟩ ⟨b, hb⟩ hab
      have := (cancel_mono i).1 (congrArg Subtype.val hab)
      exact Subtype.ext (congrArg CommaMorphism.left this)
    · rintro ⟨y, y', hy'⟩
      refine ⟨⟨y'.left, Over.w y'⟩, Subtype.ext ?_⟩
      simp only
      rw [← hy']
      congr 1
  have hflat : Flat K.hom := inferInstance
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [h]; exact hfin
  · rw [h]; exact hflat
  · rw [h]; exact (Scheme.Hom.one_le_finrank_iff_surjective K.hom).1 fun s => (hrank s).symm ▸ hd
  · intro y; rw [h]; exact hrank y
end

section

open NumberField Matrix GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.LieDisc

theorem _root_.GlobalTheory.T.exists_integral_trace_one_unramified : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∃ t : E, IsIntegral ℤ t ∧ t + cc t = 1 := by
  first | exact @GlobalTheory.LieDisc.exists_integral_add_cc_eq_one | exact GlobalTheory.LieDisc.exists_integral_add_cc_eq_one | (intros; apply GlobalTheory.LieDisc.exists_integral_add_cc_eq_one <;> assumption)
end

section

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 200000

noncomputable section

open NumberField Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.ConjugateSelfDual

namespace GlobalTheory.GalIntegral

variable {l : ℕ} [Fact l.Prime] (LL : FinExt l)

def emb : ↥(OL LL) →+* PadicAlgCl l := LL.1.val.toRingHom.comp (OL LL).val.toRingHom

theorem emb_mem (x : ↥(OL LL)) : emb LL x ∈ LL.1 := (x : ↥LL.1).2

theorem norm_emb_le (x : ↥(OL LL)) : ‖emb LL x‖ ≤ 1 := (Examples₂.LB.mem_OL LL (x : ↥LL.1)).1 x.2

def lift (x : PadicAlgCl l) (hx : x ∈ LL.1) (h : ‖x‖ ≤ 1) : ↥(OL LL) :=
  ⟨⟨x, hx⟩, (Examples₂.LB.mem_OL LL ⟨x, hx⟩).2 h⟩

theorem norm_l : ‖(l : PadicAlgCl l)‖ = (l : ℝ)⁻¹ := by
  rw [← map_natCast (algebraMap ℚ_[l] (PadicAlgCl l)), PadicAlgCl.norm_extends, Padic.norm_p]

section Main

variable {LL}

def vec {n : ℕ} (v : Fin n → ↥(OL LL)) : Fin n → PadicAlgCl l := fun j => emb LL (v j)

variable {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω] {n : ℕ}

def stab (LL : FinExt l) (r : G E Ω →* GL (Fin n) (PadicAlgCl l)) : Submodule ↥(OL LL) (Fin n → ↥(OL LL)) where
  carrier := {v | ∀ g i, ‖(r g : Matrix (Fin n) (Fin n) (PadicAlgCl l)).mulVec (vec v) i‖ ≤ 1}
  zero_mem' := by
    intro g i
    have : vec (0 : Fin n → ↥(OL LL)) = 0 := funext fun j => by simp [vec]
    simp [this]
  add_mem' := by
    intro v w hv hw g i
    have : vec (v + w) = vec v + vec w := funext fun j => by simp [vec]
    rw [this, Matrix.mulVec_add, Pi.add_apply]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hv g i) (hw g i))
  smul_mem' := by
    intro a v hv g i
    have : vec (a • v) = emb LL a • vec v := funext fun j => by simp [vec]
    rw [this, Matrix.mulVec_smul, Pi.smul_apply, norm_smul]
    exact mul_le_one₀ (norm_emb_le LL a) (norm_nonneg _) (hv g i)

theorem stab_stable (LL : FinExt l) (r : G E Ω →* GL (Fin n) (PadicAlgCl l))
    (hLL : ∀ g i j, (r g : Matrix (Fin n) (Fin n) (PadicAlgCl l)) i j ∈ LL.1) (v : Fin n → ↥(OL LL)) (hv : v ∈ stab LL r) (g : G E Ω) :
    ∃ u ∈ stab LL r, vec u = (r g : Matrix (Fin n) (Fin n) (PadicAlgCl l)).mulVec (vec v) := by
  have hmem : ∀ i, (r g : Matrix (Fin n) (Fin n) (PadicAlgCl l)).mulVec (vec v) i ∈ LL.1 := fun i => by
    simp only [Matrix.mulVec, dotProduct]
    exact LL.1.sum_mem fun j _ => LL.1.mul_mem (hLL g i j) (emb_mem LL (v j))
  refine ⟨fun i => lift LL _ (hmem i) (hv g i), ?_, rfl⟩
  intro g' i
  have e : vec (fun i => lift LL _ (hmem i) (hv g i)) = (r g : Matrix (Fin n) (Fin n) (PadicAlgCl l)).mulVec (vec v) := rfl
  rw [e, Matrix.mulVec_mulVec, ← Units.val_mul, ← map_mul]
  exact hv (g' * g) i

theorem bdd [NumberField E] [IsAlgClosure E Ω] (r : G E Ω →* GL (Fin n) (PadicAlgCl l)) (hr : Continuous r) :
    ∃ B : ℝ, ∀ g i j, ‖(r g : Matrix (Fin n) (Fin n) (PadicAlgCl l)) i j‖ ≤ B := by
  let f : G E Ω → ℝ := fun g => ∑ i, ∑ j, ‖(r g : Matrix (Fin n) (Fin n) (PadicAlgCl l)) i j‖
  have hc : Continuous fun g => (r g : Matrix (Fin n) (Fin n) (PadicAlgCl l)) :=
    (Units.continuous_val (M := Matrix (Fin n) (Fin n) (PadicAlgCl l))).comp hr
  have hf : Continuous f := continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => (hc.matrix_elem i j).norm
  obtain ⟨B, hB⟩ := (isCompact_range hf).bddAbove
  refine ⟨B, fun g i j => le_trans ?_ (hB ⟨g, rfl⟩)⟩
  refine le_trans ?_ (Finset.single_le_sum (f := fun i' => ∑ j', ‖(r g : Matrix (Fin n) (Fin n) (PadicAlgCl l)) i' j'‖)
    (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ i))
  exact Finset.single_le_sum (f := fun j' => ‖(r g : Matrix (Fin n) (Fin n) (PadicAlgCl l)) i j'‖)
    (fun _ _ => norm_nonneg _) (Finset.mem_univ j)

end Main

section Conj

variable {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω] {n : ℕ}

theorem smul_mem_stab [NumberField E] [IsAlgClosure E Ω] (LL : FinExt l) (r : G E Ω →* GL (Fin n) (PadicAlgCl l)) (hr : Continuous r) :
    ∃ c : ↥(OL LL), emb LL c ≠ 0 ∧ ∀ v : Fin n → ↥(OL LL), c • v ∈ stab LL r := by
  obtain ⟨B, hB⟩ := bdd r hr
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt B (by exact_mod_cast (Fact.out : l.Prime).one_lt : (1 : ℝ) < l)
  have he : emb LL ((l : ↥(OL LL)) ^ k) = (l : PadicAlgCl l) ^ k := by rw [map_pow, map_natCast]
  refine ⟨(l : ↥(OL LL)) ^ k, ?_, ?_⟩
  · rw [he]
    exact pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero)
  · intro v g i
    have hv : vec (((l : ↥(OL LL)) ^ k) • v) = ((l : PadicAlgCl l) ^ k) • vec v := funext fun j => by
      simp only [vec, Pi.smul_apply, smul_eq_mul, map_mul, he]
    have hX : ‖(r g : Matrix (Fin n) (Fin n) (PadicAlgCl l)).mulVec (vec v) i‖ ≤ B := by
      simp only [Matrix.mulVec, dotProduct]
      refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg ((norm_nonneg _).trans (hB g i i)) fun j _ => ?_
      rw [norm_mul]
      exact (mul_le_of_le_one_right (norm_nonneg _) (norm_emb_le LL (v j))).trans (hB g i j)
    rw [hv, Matrix.mulVec_smul, Pi.smul_apply, norm_smul, norm_pow, norm_l, inv_pow]
    exact inv_mul_le_one_of_le₀ (hX.trans hk.le) (by positivity)

end Conj

theorem exists_basis {O : Type} [CommRing O] [IsDomain O] [IsPrincipalIdealRing O] {n : ℕ} (N : Submodule O (Fin n → O))
    {c : O} (hc : c ≠ 0) (hcN : ∀ v : Fin n → O, c • v ∈ N) : Nonempty (Module.Basis (Fin n) O N) := by
  obtain ⟨m, b0⟩ := Submodule.basisOfPid (Pi.basisFun O (Fin n)) N
  have hm : m = n := by
    have : Module.Finite O N := Module.Finite.of_basis b0
    have h1 : Module.finrank O N = m := by rw [Module.finrank_eq_card_basis b0, Fintype.card_fin]
    have h2 := Submodule.finrank_le N
    rw [Module.finrank_fin_fun] at h2
    let φ : (Fin n → O) →ₗ[O] (Fin n → O) :=
      { toFun := fun v j => c * v j
        map_add' := fun v w => funext fun j => mul_add c (v j) (w j)
        map_smul' := fun a v => funext fun j => mul_left_comm c a (v j) }
    have hinj : Function.Injective φ := fun x y hxy => funext fun j => mul_left_cancel₀ hc (congrFun hxy j)
    have h3 : LinearMap.range φ ≤ N := by
      rintro _ ⟨v, rfl⟩
      exact hcN v
    have h4 := Submodule.finrank_mono h3
    rw [LinearMap.finrank_range_of_inj hinj, Module.finrank_fin_fun] at h4
    omega
  exact ⟨b0.reindex (finCongr hm)⟩

theorem sum_repr_map {O K : Type} [CommRing O] [CommRing K] (e : O →+* K) {n : ℕ} {N : Submodule O (Fin n → O)}
    (b : Module.Basis (Fin n) O N) (x : N) (j : Fin n) :
    ∑ k, e ((b k : Fin n → O) j) * e (b.repr x k) = e ((x : Fin n → O) j) := by
  have := congrArg (fun y : N => e ((y : Fin n → O) j)) (b.sum_repr x)

  simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sum, map_mul] at this
  rw [← this]
  exact Finset.sum_congr rfl fun k _ => mul_comm _ _

theorem exists_conj_integral : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (n : ℕ) (LL : FinExt l) (r : G E Ω →* GL (Fin n) (PadicAlgCl l)), Continuous r → (∀ g i j, (r g : Matrix (Fin n) (Fin n) (PadicAlgCl l)) i j ∈ LL.1) → ∃ A : GL (Fin n) (PadicAlgCl l), (∀ i j, (A : Matrix (Fin n) (Fin n) (PadicAlgCl l)) i j ∈ LL.1) ∧ (∀ i j, ((A⁻¹ : GL (Fin n) (PadicAlgCl l)) : Matrix (Fin n) (Fin n) (PadicAlgCl l)) i j ∈ LL.1) ∧ ∀ g i j, ‖((A⁻¹ * r g * A : GL (Fin n) (PadicAlgCl l)) : Matrix (Fin n) (Fin n) (PadicAlgCl l)) i j‖ ≤ 1 := by
  intro E Ω _ _ _ _ _ l _ n LL r hr hLL
  obtain ⟨c, hc0, hcN⟩ := smul_mem_stab LL r hr
  have : IsDiscreteValuationRing ↥(OL LL) := Examples₂.LB.OL_dvr LL
  have hc : c ≠ 0 := fun h => hc0 (by rw [h, map_zero])
  obtain ⟨b⟩ := exists_basis (stab LL r) hc hcN
  have hrep := sum_repr_map (emb LL) b
  let A : Matrix (Fin n) (Fin n) (PadicAlgCl l) := fun i j => emb LL ((b j : Fin n → ↥(OL LL)) i)
  let D : Matrix (Fin n) (Fin n) (PadicAlgCl l) := fun k i => emb LL (b.repr ⟨c • Pi.single i 1, hcN _⟩ k)
  have hAD : A * D = emb LL c • (1 : Matrix (Fin n) (Fin n) (PadicAlgCl l)) := by
    ext j i
    rw [Matrix.mul_apply]
    refine (hrep ⟨c • Pi.single i 1, hcN _⟩ j).trans ?_
    simp only [Pi.smul_apply, Pi.single_apply, smul_eq_mul, Matrix.smul_apply, Matrix.one_apply]
    split_ifs <;> simp
  let Ai : Matrix (Fin n) (Fin n) (PadicAlgCl l) := (emb LL c)⁻¹ • D
  have h1 : A * Ai = 1 := by
    simp only [Ai]
    rw [Matrix.mul_smul, hAD, smul_smul, inv_mul_cancel₀ hc0, one_smul]
  have h2 : Ai * A = 1 := mul_eq_one_comm.1 h1
  let AU : GL (Fin n) (PadicAlgCl l) := ⟨A, Ai, h1, h2⟩
  refine ⟨AU, fun i j => emb_mem LL _, fun i j => ?_, fun g i j => ?_⟩
  · show ((emb LL c)⁻¹ • D) i j ∈ LL.1
    rw [Matrix.smul_apply, smul_eq_mul]
    exact LL.1.mul_mem (LL.1.inv_mem (emb_mem LL c)) (emb_mem LL _)
  · choose u hu hvu using fun j => stab_stable LL r hLL _ (b j).2 g
    let C : Matrix (Fin n) (Fin n) (PadicAlgCl l) := fun k j => emb LL (b.repr ⟨u j, hu j⟩ k)
    have hRA : (r g : Matrix (Fin n) (Fin n) (PadicAlgCl l)) * A = A * C := by
      ext i j
      rw [Matrix.mul_apply, Matrix.mul_apply]
      refine Eq.trans ?_ (hrep ⟨u j, hu j⟩ i).symm
      have h' := congrFun (hvu j) i
      simp only [vec, Matrix.mulVec, dotProduct] at h'
      exact h'.symm
    have hU : ((AU⁻¹ * r g * AU : GL (Fin n) (PadicAlgCl l)) : Matrix (Fin n) (Fin n) (PadicAlgCl l)) =
        Ai * (r g : Matrix (Fin n) (Fin n) (PadicAlgCl l)) * A := by
      simp only [Units.val_mul]
      rfl
    rw [hU, mul_assoc, hRA, ← mul_assoc, h2, one_mul]
    exact norm_emb_le LL _

end GlobalTheory.GalIntegral

end
end

section

open NumberField IsDedekindDomain
open scoped nonZeroDivisors

theorem _root_.GlobalTheory.T.exists_finset_valuation_div_le_one_of_isLocGen : ∀ (K : Type) [Field K] [NumberField K] (I : FractionalIdeal (𝓞 K)⁰ K) (u : K),
    ∃ S : Finset (HeightOneSpectrum (𝓞 K)), ∀ p ∉ S, ∀ a : K, Formalism.L2.LamCM.IsLocGen p a I → u ≠ 0 →
      p.valuation K (a / u) ≤ 1 := by
  first | exact @GlobalTheory.LocGenVal.valuation_div_le_one_cofinite | exact GlobalTheory.LocGenVal.valuation_div_le_one_cofinite | (intros; apply GlobalTheory.LocGenVal.valuation_div_le_one_cofinite <;> assumption)
end

section

open Polynomial CategoryTheory

theorem _root_.GlobalTheory.T.star_coeff_eisenstein_series_reverse_poly : ∀ {g : ℕ} [Fact g.Prime] {C : Formalism.IrreducibleCountingLemmas.TYPES.LabelConv (ZMod g)} (O : Formalism.IrreducibleCountingLemmas.TYPES.LabelMap (ZMod g) C), Formalism.IrreducibleCountingLemmas.TYPES.LabelMapEquivariant O → ∀ (r : ℕ) (f : Polynomial (ZMod g)), f.Monic → f.coeff 0 ≠ 0 → ∀ x, star ((Formalism.L2.NT.eSerO O r f).coeff x) = (Formalism.L2.NT.eSerO O r (Polynomial.C (f.coeff 0)⁻¹ * f.reverse)).coeff x := by
  first | exact @GlobalTheory.SerConj.star_coeff_eSerO | exact GlobalTheory.SerConj.star_coeff_eSerO | (intros; apply GlobalTheory.SerConj.star_coeff_eSerO <;> assumption)
end

section

open CategoryTheory Polynomial Formalism.IrreducibleCountingLemmas.TYPES

theorem _root_.GlobalTheory.T.exists_monotone_blocks_same_harishChandra_character : ∀ (K : Type) [Field K] [Fintype K] [DecidableEq K] (r s : ℕ) (b : Fin r → Fin s) (lam : ∀ c : Fin s, FDRep ℂ (GL {i // b i = c} K)), Function.Surjective b → (∀ c, Simple (lam c) ∧ IsCuspidal K (lam c)) → ∃ (b' : Fin r → Fin s) (lam' : ∀ c : Fin s, FDRep ℂ (GL {i // b' i = c} K)), Function.Surjective b' ∧ (∀ c, Simple (lam' c) ∧ IsCuspidal K (lam' c)) ∧ Monotone b' ∧ ∀ x : GL (Fin r) K, LinearMap.trace ℂ (hcSpace K b' lam') (hcRep K b' lam' x) = LinearMap.trace ℂ (hcSpace K b lam) (hcRep K b lam x) := by
  first | exact @GlobalTheory.HCSort.exists_monotone_same_trace | exact GlobalTheory.HCSort.exists_monotone_same_trace | (intros; apply GlobalTheory.HCSort.exists_monotone_same_trace <;> assumption)
end

section

open MeasureTheory Matrix
open Formalism.REAL (UJ KG toM toMK muK expG inG Jm Kset)

namespace GlobalTheory

theorem offDiagBlockNorm_cont_inv : ∀ (n : ℕ) (ε : Fin n → Bool), (Continuous fun g : UJ ε => ∑ z : {z : Fin n × Fin n // ε z.1 = true ∧ ε z.2 = false}, ‖(toM g) z.1.1 z.1.2‖ ^ 2) ∧ ∀ (k k' : KG ε) (g : UJ ε), ∑ z : {z : Fin n × Fin n // ε z.1 = true ∧ ε z.2 = false}, ‖(toM ((k : UJ ε) * g * (k' : UJ ε))) z.1.1 z.1.2‖ ^ 2 = ∑ z : {z : Fin n × Fin n // ε z.1 = true ∧ ε z.2 = false}, ‖(toM g) z.1.1 z.1.2‖ ^ 2 := by
  intro n ε
  refine ⟨?_, ?_⟩
  · have hM : Continuous fun g : UJ ε => toM g :=
      Units.continuous_val.comp continuous_subtype_val
    refine continuous_finsetSum _ fun z _ => ?_
    exact ((continuous_apply z.1.2).comp ((continuous_apply z.1.1).comp hM)).norm.pow 2
  · intro k k' g
    have hk : toM (k : UJ ε) ∈ Kset ε := k.2
    have hk' : toM (k' : UJ ε) ∈ Kset ε := k'.2
    have hmul : toM ((k : UJ ε) * g * (k' : UJ ε)) = toM (k : UJ ε) * toM g * toM (k' : UJ ε) := rfl
    rw [hmul]
    refine GlobalTheory.T.offDiagonalBlock_sum_sq_norm_blockUnitary_invariant n ε _ _ _ ?_ hk.2 ?_ hk'.2
    · exact Matrix.mem_unitaryGroup_iff'.mp hk.1
    · exact Matrix.mem_unitaryGroup_iff'.mp hk'.1

end GlobalTheory
end

section

open NumberField IsDedekindDomain Filter Topology

theorem _root_.GlobalTheory.T.exists_compact_open_subgroups : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (V : Set (κ → FiniteAdeleRing (𝓞 F) F)),
    V ∈ 𝓝 (0 : κ → FiniteAdeleRing (𝓞 F) F) →
    ∃ N : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F), AddSubgroup (v.adicCompletion F),
      (∀ v, IsOpen (N v : Set (v.adicCompletion F))) ∧ (∀ v, IsCompact (N v : Set (v.adicCompletion F))) ∧
      (∀ᶠ v in Filter.cofinite, (N v : Set (v.adicCompletion F)) = v.adicCompletionIntegers F) ∧
      {y : κ → FiniteAdeleRing (𝓞 F) F | ∀ i v, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (y i) ∈ N v} ∈ 𝓝 (0 : κ → FiniteAdeleRing (𝓞 F) F) ∧
      {y : κ → FiniteAdeleRing (𝓞 F) F | ∀ i v, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (y i) ∈ N v} ⊆ V := by
  first | exact @GlobalTheory.FinAdeleNbhd.exists_prod_openCompact_subset | exact GlobalTheory.FinAdeleNbhd.exists_prod_openCompact_subset | (intros; apply GlobalTheory.FinAdeleNbhd.exists_prod_openCompact_subset <;> assumption)
end

section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
open TensorProduct

theorem _root_.GlobalTheory.T.isAdicComplete_span_natCast_of_finite_projective' : ∀ (p : ℕ) (O A : Type) [CommRing O] [CommRing A] [Algebra O A] [Module.Finite O A] [Module.Projective O A] [IsAdicComplete (Ideal.span {(p : O)}) O], IsAdicComplete (Ideal.span {(p : A)}) A := by
  first | exact @GlobalTheory.FinProjComplete.isAdicComplete_span_natCast | exact GlobalTheory.FinProjComplete.isAdicComplete_span_natCast | (intros; apply GlobalTheory.FinProjComplete.isAdicComplete_span_natCast <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

theorem _root_.GlobalTheory.T.exists_finite_agreementLocus_separated : ∀ (H : Scheme.{0}) (Z G : Over H), IsFinite Z.hom → IsSeparated G.hom → ∀ (Ix : Type) [Finite Ix] (a b : Ix → (Z ⟶ G)), ∃ (Y : Over H) (i : Y ⟶ Z), IsFinite Y.hom ∧ (∀ k, i ≫ a k = i ≫ b k) ∧ ∀ (T : Over H) (h : T ⟶ Z), (∀ k, h ≫ a k = h ≫ b k) → ∃! h' : T ⟶ Y, h' ≫ i = h := by
  first | (exact @GlobalTheory.EqLocus.exists_finite_eqLocus) | (exact GlobalTheory.EqLocus.exists_finite_eqLocus) | (intros; apply GlobalTheory.EqLocus.exists_finite_eqLocus  <;> assumption)
end
