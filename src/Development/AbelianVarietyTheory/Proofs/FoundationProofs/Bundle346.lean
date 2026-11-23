module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle109
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle016
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
public import Mathlib.RingTheory.AdicCompletion.Noetherian
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle015
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle009
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle081
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle143
public import Formalism.LocalToGlobal.Divisibility.CoefModLemmas
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle339
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle335
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle107
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle133
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle003
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle001
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.IsSelfDualE
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LeafBounds.MeanMaxLeaf.LeafMMFree
import Formalism.QuotientMetricDivisors.Statement

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped Matrix

namespace GlobalTheory.Ord2

private theorem locEmb_conj {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    {A B : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 k)} (hA : IsPlaceOver A v) (hB : IsPlaceOver B v) :
    ∃ g : G k Ω, (∀ τ ∈ Ine (F := k) B, g⁻¹ * τ * g ∈ Ine (F := k) A) ∧
      (∀ τ ∈ Dec (F := k) B, g⁻¹ * τ * g ∈ Dec (F := k) A) ∧
      ∀ τ ∈ Dec (F := k) A, g * τ * g⁻¹ ∈ Dec (F := k) B := by
  obtain ⟨g, hg⟩ := exists_smul_eq_of_isPlaceOver (F := k) hA hB
  have h : IsLift (RingEquiv.refl k) g.toRingEquiv := fun x => g.commutes x
  have hm : ∀ x, g.toRingEquiv x ∈ B ↔ x ∈ A := fun x => by
    show g • x ∈ B ↔ _
    rw [← hg]
    exact ValuationSubring.smul_mem_pointwise_smul_iff
  have hm' : ∀ x, g.toRingEquiv.symm x ∈ A ↔ x ∈ B := fun x => by
    rw [← hm, RingEquiv.apply_symm_apply]
  exact ⟨g, fun τ hτ => conjGal_mem_Ine h hm hτ, fun τ hτ => conjGal_mem_Dec h hm hτ,
    fun τ hτ => conjGal_mem_Dec h.symm hm' hτ⟩

theorem bk_locEmb : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (W : R2 Ω l) (A : ValuationSubring Ω), OverL l A → ∀ z ∈ Z1 (Loc.colRep W), IsBK l (Loc.colRep W) z → ∃ ι : GQ l →* G ℚ Ω, Continuous ι ∧ (∀ σ, ι σ ∈ Dec (F := ℚ) A) ∧ (∀ s ∈ Dec (F := ℚ) A, ∃ σ, ι σ = s) ∧ (∀ σ ∈ Loc.Iq l, ι σ ∈ Ine (F := ℚ) A) ∧ (∀ σ, cycZ ℚ Ω l (ι σ) = Loc.cyc l l σ) ∧ (fun σ => z (ι σ)) ∈ Loc.finiteCocycles (MonoidHom.id (GQ l)) ((Loc.colRep W).comp ι) := by
  intro l _ Ω _ iA _ W A hA z hz hb
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  obtain rfl : iA = DivisionRing.toRatAlgebra := Subsingleton.elim _ _
  obtain ⟨v, hAv, hv⟩ := hA
  obtain ⟨j, -, -, x, hx⟩ := hb.above (algebraMap ℚ (Om l))
  obtain ⟨i1, i2, -, i4, i5, i6, -⟩ := Loc.iotaFacts j
  have h0 : (fun σ => z (Loc.iota j σ)) ∈
      Loc.finiteCocycles (MonoidHom.id (GQ l)) ((Loc.colRep W).comp (Loc.iota j)) :=
    ⟨⟨hz.1.comp i1.continuous, fun g h => (congrArg z (map_mul _ g h)).trans (hz.2 _ _)⟩, x,
      fun σ => hx ⟨(Loc.iota j σ, σ), fun y => (Loc.iota_spec j σ y).symm⟩⟩
  obtain ⟨g, g1, g2, g3⟩ := locEmb_conj hAv ((i6 v).2 hv)
  let ι : GQ l →* G ℚ Ω := (MulAut.conj g⁻¹).toMonoidHom.comp (Loc.iota j)
  have hι : ∀ σ, ι σ = g⁻¹ * Loc.iota j σ * g := fun σ => by simp [ι]
  have hc : Continuous ι := by
    have : (ι : GQ l → G ℚ Ω) = fun σ => g⁻¹ * Loc.iota j σ * g := funext hι
    rw [this]
    exact (continuous_const.mul i1.continuous).mul continuous_const
  refine ⟨ι, hc, fun σ => ?_, fun s hs => ?_, fun σ hσ => ?_, fun σ => ?_, ?_⟩
  · rw [hι]
    exact g2 _ (by rw [← i2]; exact ⟨σ, rfl⟩)
  · have h1 : g * s * g⁻¹ ∈ Dec (F := ℚ) (Loc.placeJ j) := g3 s hs
    rw [← i2] at h1
    obtain ⟨σ, hσ⟩ := h1
    exact ⟨σ, by rw [hι, hσ]; group⟩
  · rw [hι]
    exact g1 _ (by rw [← i4]; exact ⟨σ, hσ, rfl⟩)
  · rw [hι, map_mul, map_mul, map_inv, mul_comm _ (cycZ ℚ Ω l (Loc.iota j σ)), inv_mul_cancel_right]
    exact DFunLike.congr_fun (i5 l) σ
  · have h1 := Loc.z1fCoef (MonoidHom.id (GQ l)) ((Loc.colRep W).comp (Loc.iota j)) ((Loc.colRep W).comp ι)
      ((Loc.colRep W g⁻¹).restrictScalars ℚ_[l]) (LinearMap.continuous_on_pi (Loc.colRep W g⁻¹))
      (fun σ y => by
        show Loc.colRep W g⁻¹ (Loc.colRep W (Loc.iota j σ) y) = Loc.colRep W (ι σ) (Loc.colRep W g⁻¹ y)
        rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, hι, mul_inv_cancel_right]) _ h0
    have hcob : ∀ σ, Loc.colRep W (ι σ) (z g⁻¹) - z g⁻¹ = z (ι σ * g⁻¹) - z (ι σ) - z g⁻¹ := fun σ => by
      rw [hz.2]; abel
    have h2 : (fun σ => Loc.colRep W (ι σ) (z g⁻¹) - z g⁻¹) ∈
        Loc.finiteCocycles (MonoidHom.id (GQ l)) ((Loc.colRep W).comp ι) := by
      refine ⟨⟨?_, fun a b => ?_⟩, z g⁻¹ ⊗ₜ 1, fun σ => ?_⟩
      · rw [funext hcob]
        exact ((hz.1.comp (hc.mul continuous_const)).sub (hz.1.comp hc)).sub continuous_const
      · show Loc.colRep W (ι (a * b)) (z g⁻¹) - z g⁻¹ = Loc.colRep W (ι a) (z g⁻¹) - z g⁻¹ +
          Loc.colRep W (ι a) (Loc.colRep W (ι b) (z g⁻¹) - z g⁻¹)
        rw [map_mul, map_mul, Module.End.mul_apply, map_sub]; abel
      · simp [Loc.actC, TensorProduct.sub_tmul]
    have h3 := Submodule.sub_mem _ h1 h2
    convert h3 using 1
    funext σ
    show z (ι σ) = Loc.colRep W g⁻¹ (z (Loc.iota j σ)) - (Loc.colRep W (ι σ) (z g⁻¹) - z g⁻¹)
    have e1 := hz.2 g⁻¹ (Loc.iota j σ)
    rw [hcob, hι, mul_inv_cancel_right, e1]
    abel

end GlobalTheory.Ord2
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

noncomputable section

namespace GlobalTheory.Ord2

variable {l : ℕ} [Fact l.Prime]

theorem norm_le_one_of_mem_coef (c : Coef l) {x : Qbar l} (hx : x ∈ c.O) : ‖x‖ ≤ 1 :=
  _root_.UpperTheory.Reformulated.B.Rf3.norm_le_one_of_mem_coef c hx

theorem norm_natCast_l : ‖((l : ℕ) : Qbar l)‖ = (l : ℝ)⁻¹ := by
  have : ((l : ℕ) : Qbar l) = algebraMap ℚ_[l] (PadicAlgCl l) (l : ℚ_[l]) := by simp
  rw [this, norm_algebraMap', Padic.norm_p]

theorem norm_natCast_l_lt_one : ‖((l : ℕ) : Qbar l)‖ < 1 := by
  rw [norm_natCast_l]
  exact inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : l.Prime).one_lt)

theorem tendsto_norm_l_pow :
    Filter.Tendsto (fun n : ℕ => ‖((l : ℕ) : Qbar l) ^ n‖) Filter.atTop (nhds 0) := by
  simp only [norm_pow]
  exact tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) norm_natCast_l_lt_one

theorem eq_zero_of_forall_norm_le (x : Qbar l) (h : ∀ n : ℕ, ‖x‖ ≤ ‖((l : ℕ) : Qbar l) ^ n‖) : x = 0 := by
  have h0 : ‖x‖ ≤ 0 := ge_of_tendsto' tendsto_norm_l_pow h
  exact norm_le_zero_iff.1 h0

theorem cg_symm {n : ℕ} {a b : Qbar l} (h : Cg n a b) : Cg n b a := by
  unfold Cg at *; rwa [norm_sub_rev]

theorem cg_trans {n : ℕ} {a b d : Qbar l} (h : Cg n a b) (h' : Cg n b d) : Cg n a d := by
  unfold Cg at *
  have e : a - d = (a - b) + (b - d) := by ring
  rw [e]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le h h')

theorem cv_symm {n : ℕ} {a b : Fin 2 → Qbar l} (h : Cv n a b) : Cv n b a := fun i => cg_symm (h i)

theorem cv_trans {n : ℕ} {a b d : Fin 2 → Qbar l} (h : Cv n a b) (h' : Cv n b d) : Cv n a d :=
  fun i => cg_trans (h i) (h' i)

theorem eq_of_forall_cg {a b : Qbar l} (h : ∀ n, Cg n a b) : a = b :=
  sub_eq_zero.1 (eq_zero_of_forall_norm_le _ h)

end GlobalTheory.Ord2

end
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.RecOne GlobalTheory.AlmostEt
open scoped Matrix NNReal

namespace GlobalTheory.RecOne.CycDvd

theorem apply_eq_pow (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (n : ℕ) (s : G ℚ Ω)
    {t : Ω} (ht : t ^ (l ^ n) = 1) : s t = t ^ ((cycMod ℚ Ω l n s : (ZMod (l ^ n))ˣ) : ZMod (l ^ n)).val := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : CharZero Ω := algebraRat.charZero Ω
  haveI : NeZero (l : Ω) := ⟨by exact_mod_cast (Fact.out : l.Prime).ne_zero⟩
  have h1 := cyclotomicCharacter.spec (L := Ω) l (MulSemiringAction.toRingAut (G ℚ Ω) Ω s) t ht
  have h2 : (cyclotomicCharacter Ω l (MulSemiringAction.toRingAut (G ℚ Ω) Ω s)).val.toZModPow n =
      ((cycMod ℚ Ω l n s : (ZMod (l ^ n))ˣ) : ZMod (l ^ n)) := by
    simp [cycMod, cycZ]
  rw [h2] at h1
  exact h1

theorem exists_Ine_apply_eq (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω]
    (A : ValuationSubring Ω) (hA : A.valuation (l : Ω) < 1) (n : ℕ) {z μ : Ω} (hz : IsPrimitiveRoot z (l ^ n))
    (hμ : IsPrimitiveRoot μ (l ^ n)) : ∃ s ∈ Ine (F := ℚ) A, s z = μ := by
  have hpos : 0 < l ^ n := pow_pos (Fact.out : l.Prime).pos n
  haveI : NeZero (l ^ n) := ⟨hpos.ne'⟩
  obtain ⟨i, hi, hcop, rfl⟩ := (hz.isPrimitiveRoot_iff).1 hμ
  obtain ⟨⟨s, hs⟩, hsu⟩ := GlobalTheory.InertiaPowers.cycMod_Ine_surjective l Ω A hA n (ZMod.unitOfCoprime i hcop)
  refine ⟨s, hs, ?_⟩
  have hsu' : cycMod ℚ Ω l n s = ZMod.unitOfCoprime i hcop := hsu
  rw [apply_eq_pow l Ω n s hz.pow_eq_one, hsu', ZMod.coe_unitOfCoprime, ZMod.val_natCast, Nat.mod_eq_of_lt hi]

theorem cyclotomic_dvd : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (A : ValuationSubring Ω), OverL l A → ∀ (n : ℕ) (z : A), IsPrimitiveRoot (z : Ω) (l ^ n) → ∀ R : Polynomial (fixA A), Polynomial.aeval z R = 0 → Polynomial.cyclotomic (l ^ n) (fixA A) ∣ R := by
  intro l _ Ω _ _ _ A hO n z hz R hR
  classical
  have hA : A.valuation (l : Ω) < 1 := by
    obtain ⟨v, hv, hl⟩ := hO
    have h1 := (hv ((l : ℕ) : 𝓞 ℚ)).2 hl
    simpa using h1
  have hpos : 0 < l ^ n := pow_pos (Fact.out : l.Prime).pos n
  let f : fixA A →+* Ω := A.subtype.comp (fixA A).subtype
  have hf : Function.Injective f := Subtype.val_injective.comp Subtype.val_injective
  have h0 : Polynomial.eval₂ f (z : Ω) R = 0 := by
    have := Polynomial.hom_eval₂ R (algebraMap (fixA A) A) A.subtype z
    rw [← Polynomial.aeval_def, hR, map_zero] at this
    exact this.symm
  have hroot : ∀ μ ∈ primitiveRoots (l ^ n) Ω, (R.map f).eval μ = 0 := by
    intro μ hμ
    obtain ⟨s, hs, rfl⟩ := exists_Ine_apply_eq l Ω A hA n hz ((mem_primitiveRoots hpos).1 hμ)
    have e := Polynomial.hom_eval₂ R f (s : Ω →+* Ω) (z : Ω)
    have e2 : (s : Ω →+* Ω).comp f = f := RingHom.ext fun a => a.2 s hs
    rw [h0, map_zero, e2] at e
    rw [Polynomial.eval_map]
    exact e.symm
  rw [← Polynomial.map_dvd_map f hf (Polynomial.cyclotomic.monic _ _), Polynomial.map_cyclotomic,
    Polynomial.cyclotomic_eq_prod_X_sub_primitiveRoots hz]
  refine Finset.prod_dvd_of_coprime ?_ ?_
  · intro a _ b _ hab
    exact Polynomial.isCoprime_X_sub_C_of_isUnit_sub (sub_ne_zero.2 hab).isUnit
  · intro μ hμ
    exact Polynomial.dvd_iff_isRoot.2 (hroot μ hμ)

end GlobalTheory.RecOne.CycDvd
end

section

open NumberField IsDedekindDomain MvPolynomial Formalism.BasicNotions Formalism.L2.DIV Formalism.DivisionValues GlobalTheory.TestLat Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open scoped Matrix ComplexOrder

theorem _root_.GlobalTheory.T.dualLattice_isLattice_and_hermitianDual : DualFrLattice ∧ DualFrHdual := by
  first | exact @GlobalTheory.DualLat.dualFr_lattice_and_hdual | exact GlobalTheory.DualLat.dualFr_lattice_and_hdual | (intros; apply GlobalTheory.DualLat.dualFr_lattice_and_hdual <;> assumption)
end

section

namespace GlobalTheory.ColClassNumber

open Formalism.BasicNotions Formalism.MainNotions.StandardLattice

theorem classNumber_all (D : D7) (Lv : LevelData D) : ClassNumberFormula₂ D Lv :=
  classNumber_of_index GlobalTheory.T.selfDualLattice_over_columnBaseLattice GlobalTheory.T.stabiliser_self_dual_lattice_level_index_formula D Lv

end GlobalTheory.ColClassNumber
end
