module

import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.IsCompactSpanRange
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.SdVolWOfTop
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.AdeleLC
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.T2SpaceTensorProductFiniteExtension
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.Bundle004
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.Bundle003
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.Bundle002
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle018
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

namespace PI.OmLocU

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain MeasureTheory
  PI.VolStabSW PI.VolStabSW.PositiveNearLattice PI.VolStabSW.SdDualW
open scoped TensorProduct

section TopWs

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F)) {n : ℕ}

theorem sdc_exists_int_smul_mem (L : Submodule (𝓞 E) (Fin n → E))
    (hL : Submodule.span E (L : Set (Fin n → E)) = ⊤) (x : Fin n → E) :
    ∃ y : ℤ, y ≠ 0 ∧ y • x ∈ L := by
  classical
  have hx : x ∈ Submodule.span E (L : Set (Fin n → E)) := hL ▸ Submodule.mem_top
  obtain ⟨m, f, g, rfl⟩ := Submodule.mem_span_set'.1 hx
  obtain ⟨y, hy, hint⟩ := exists_integral_multiples ℤ ℚ (Finset.univ.image f)
  refine ⟨y, hy, ?_⟩
  rw [Finset.smul_sum]
  refine Submodule.sum_mem _ fun i _ => ?_
  have hi : IsIntegral ℤ (y • f i) := hint _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))
  convert L.smul_mem (⟨y • f i, hi⟩ : 𝓞 E) (g i).2 using 1
  rw [← smul_assoc]
  rfl

theorem exists_int_smul_mem_all (L : Submodule (𝓞 E) (Fin n → E))
    (hL : Submodule.span E (L : Set (Fin n → E)) = ⊤) {ι : Type} [Fintype ι] (w : ι → Fin n → E) :
    ∃ y : ℤ, y ≠ 0 ∧ ∀ j, y • w j ∈ L := by
  classical
  choose y hy hw using fun j => sdc_exists_int_smul_mem L hL (w j)
  refine ⟨∏ j, y j, Finset.prod_ne_zero_iff.2 fun j _ => hy j, fun j => ?_⟩
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ j), mul_smul]
  exact zsmul_mem (hw j) _

theorem ratV_single (i : Fin n) (e : E) :
    ratV (F := F) (Fv F v) (Pi.single i e : Fin n → E) =
      (Pi.single i (inclR (F := F) (Fv F v) e) : Fin n → Fv F v ⊗[F] E) := by
  funext j
  by_cases h : j = i
  · subst h
    simp [ratV]
  · simp [ratV, Pi.single_eq_of_ne h]

theorem ratV_mem_latLoc {Λ : Set (Fin n → E)} {x : Fin n → E} (hx : x ∈ Λ) :
    ratV (F := F) (Fv F v) x ∈ latLoc (E := E) v Λ :=
  Submodule.subset_span ⟨x, hx, rfl⟩

theorem sdc_isOpen_latLoc (Λ : Set (Fin n → E))
    (hL : ∃ L : Submodule (𝓞 E) (Fin n → E), Submodule.IsFullLattice E L ∧ (L : Set (Fin n → E)) = Λ) :
    IsOpen (latLoc (E := E) v Λ : Set (Fin n → Fv F v ⊗[F] E)) := by
  apply PI.OmLocU.isOpen_latLoc <;> assumption

theorem sdc_isCompact_latLoc (Λ : Set (Fin n → E))
    (hL : ∃ L : Submodule (𝓞 E) (Fin n → E), Submodule.IsLattice E L ∧ (L : Set (Fin n → E)) = Λ) :
    IsCompact (latLoc (E := E) v Λ : Set (Fin n → Fv F v ⊗[F] E)) := by
  apply PI.OmLocU.isCompact_latLoc <;> assumption

theorem topW_holds (Λ : Set (Fin n → E)) (a : ℕ)
    (hFull : ∃ L : Submodule (𝓞 E) (Fin n → E),
      Submodule.IsFullLattice E L ∧ (L : Set (Fin n → E)) = Λ) : TopW v Λ a := by
  intro hL
  have e : LamT (E := E) v Λ a =
      Set.pi Set.univ (fun _ : Fin a => (latLoc (E := E) v Λ : Set (Fin n → Fv F v ⊗[F] E))) := by
    ext X
    simp [LamT, Set.mem_pi]
  rw [e]
  exact ⟨isCompact_univ_pi fun _ => sdc_isCompact_latLoc v Λ hL,
    isOpen_set_pi Set.finite_univ fun _ _ => sdc_isOpen_latLoc v Λ hFull⟩

end TopWs

end PI.OmLocU
end
end

section

noncomputable section

namespace PI.OmLocU.Orb

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain Matrix Formalism.UG
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F)) (Λ : Set (Fin n → E))

theorem sigma_invol (hcm : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  let τ : E →ₐ[ℚ] ℂ := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  apply τ.toRingHom.injective
  have h1 := hcm.2.2.2 τ.toRingHom (σ x)
  have h2 := hcm.2.2.2 τ.toRingHom x
  rw [h1, h2, star_star]

theorem sigR_invol (hcm : IsCMExt F E σ) (z : Fv F v ⊗[F] E) : sigR (Fv F v) σ (sigR (Fv F v) σ z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul r e => simp [Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR, Algebra.TensorProduct.map_tmul, sigma_invol σ hcm]
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]

theorem sigR_inclR (e : E) : sigR (Fv F v) σ (inclR (F := F) (Fv F v) e) = inclR (F := F) (Fv F v) (σ e) := by
  simp [Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR, Algebra.TensorProduct.map_tmul]

theorem hR_conj (hcm : IsCMExt F E σ) (hJ : ∀ i j, σ (J j i) = J i j) (x y : Fin n → Fv F v ⊗[F] E) :
    sigR (Fv F v) σ (hR (Fv F v) σ J x y) = hR (Fv F v) σ J y x := by

  simp only [hR, hform, map_sum, map_mul, sigR_invol σ v hcm, JR, Matrix.map_apply, sigR_inclR, hJ]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

def NormOne : Prop :=
  StdHyp σ J ψ → UnramAt (E := E) v → ∀ u ∈ OEv (E := E) v, sigR (Fv F v) σ u = u →
    (∃ u' ∈ OEv (E := E) v, u * u' = 1) →
    ∃ l ∈ OEv (E := E) v, sigR (Fv F v) σ l * l * u = 1

def UnitNorm : Prop :=
  StdHyp σ J ψ → (∃ L : Submodule (𝓞 E) (Fin n → E), Submodule.IsLattice E L ∧ (L : Set (Fin n → E)) = Λ) →
    IsSDLoc σ J v Λ → UnramAt (E := E) v →
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (X : ι → Fin n → Fv F v ⊗[F] E), (∀ i, X i ∈ latLoc (E := E) v Λ) →
      UniG σ J v X → Fintype.card ι < n →
      ∃ p ∈ PerpG σ J v Λ X, ∃ u' ∈ OEv (E := E) v, hR (Fv F v) σ J p p * u' = 1

theorem unitV_of (hN : NormOne σ J ψ v) (hUN : UnitNorm σ J ψ v Λ) : UnitV σ J ψ v Λ := by
  intro hstd hL hsd hun ι _ _ X hX hUX hc
  obtain ⟨p, hp, u', hu'0, hu'⟩ := hUN hstd hL hsd hun ι X hX hUX hc
  have hcm := hstd.1
  have hJ := hstd.2.1.1
  have hu0 : hR (Fv F v) σ J p p ∈ OEv (E := E) v := (hsd p).1 hp.1 p hp.1
  obtain ⟨l, hl0, hl⟩ := hN hstd hun _ hu0 (hR_conj σ J v hcm hJ p p) ⟨u', hu'0, hu'⟩
  have hXl : ∀ i, hR (Fv F v) σ J (X i) (l • p) = 0 := by
    intro i
    rw [hR_smul_right, hp.2 i, mul_zero]
  refine ⟨l • p, ⟨oSmul v Λ hL l hl0 p hp.1, hXl⟩, ?_, ?_⟩
  · rw [hR_smul_left, hR_smul_right, ← mul_assoc]
    exact hl
  · intro i
    rw [← hR_conj σ J v hcm hJ, hXl i, map_zero]

theorem orbAll_of_norm (a : ℕ) (Y : TupV (E := E) v n a) (hN : NormOne σ J ψ v)
    (hUN : UnitNorm σ J ψ v Λ) : OrbAll σ J ψ v Λ a Y :=
  orbAll_of_unitV σ J ψ v Λ a Y (unitV_of σ J ψ v Λ hN hUN)

end PI.OmLocU.Orb
end
end

section

noncomputable section

namespace PI.OmLocU

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain MeasureTheory
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F)) (Λ : Set (Fin n → E))

def unifO (ϖ : Fv F v) : AddSubgroup (v.adicCompletionIntegers F) where
  carrier := {x | ∃ d : v.adicCompletionIntegers F, (x : Fv F v) = ϖ * d}
  add_mem' := fun {x y} ⟨d, hd⟩ ⟨e, he⟩ => ⟨d + e, by
    rw [AddMemClass.coe_add, AddMemClass.coe_add, hd, he, mul_add]⟩
  zero_mem' := ⟨0, by simp⟩
  neg_mem' := fun {x} ⟨d, hd⟩ => ⟨-d, by
    rw [NegMemClass.coe_neg, NegMemClass.coe_neg, hd, mul_neg]⟩

def ResIdx : Prop :=
  ∀ ϖ : Fv F v, IsUnif v ϖ → (unifO v ϖ).index = Ideal.absNorm v.asIdeal

def LatBasO (a : ℕ) (Y : TupV (E := E) v n a) : Prop :=
  GoodY σ J ψ v Λ a Y → ∃ b : Fin (2 * n) → (Fin n → Fv F v ⊗[F] E), LinearIndependent (Fv F v) b ∧
    ∀ x, x ∈ latLoc (E := E) v Λ ↔ ∃ c : Fin (2 * n) → v.adicCompletionIntegers F, x = ∑ i, (c i : Fv F v) • b i

theorem sc_smul_smul (ϖ r : Fv F v) (y : Fin n → Fv F v ⊗[F] E) :
    sc (E := E) v ϖ • (r • y) = (ϖ * r) • y := by
  funext p
  show sc (E := E) v ϖ * (r • y p) = (ϖ * r) • y p
  rw [mul_smul, Algebra.smul_def ϖ, Algebra.TensorProduct.algebraMap_apply]
  rfl

theorem idxV_of (a : ℕ) (Y : TupV (E := E) v n a) (hB : LatBasO σ J ψ v Λ a Y) (hR : ResIdx v) :
    IdxV σ J ψ v Λ a Y := by
  intro hG ϖ hϖ
  obtain ⟨b, hb, hmem⟩ := hB hG
  let φ : (Fin (2 * n) → v.adicCompletionIntegers F) →+ latA v Λ :=
    { toFun := fun c => ⟨∑ i, (c i : Fv F v) • b i, (hmem _).2 ⟨c, rfl⟩⟩
      map_zero' := by ext1; simp
      map_add' := fun c d => by
        ext1
        simp [add_smul, Finset.sum_add_distrib] }
  have hφs : Function.Surjective φ := by
    rintro ⟨x, hx⟩
    obtain ⟨c, rfl⟩ := (hmem x).1 hx
    exact ⟨c, rfl⟩
  have key : ((lattice₂ v Λ ϖ).addSubgroupOf (latA v Λ)).comap φ =
      AddSubgroup.pi Set.univ (fun _ => unifO v ϖ) := by
    ext c
    rw [AddSubgroup.mem_comap, AddSubgroup.mem_addSubgroupOf, AddSubgroup.mem_pi]
    constructor
    · rintro ⟨z, hz, hze⟩ i _
      obtain ⟨d, rfl⟩ := (hmem z).1 hz
      refine ⟨d i, ?_⟩
      have e : ∑ i, (c i : Fv F v) • b i = ∑ i, (ϖ * d i) • b i := by
        have : (DistribSMul.toAddMonoidHom (Fin n → Fv F v ⊗[F] E) (sc (E := E) v ϖ))
            (∑ i, (d i : Fv F v) • b i) = ∑ i, (ϖ * d i) • b i := by
          show sc (E := E) v ϖ • ∑ i, (d i : Fv F v) • b i = _
          rw [Finset.smul_sum]
          exact Finset.sum_congr rfl fun i _ => sc_smul_smul v ϖ _ _
        rw [← this, hze]
        rfl
      have h0 := Fintype.linearIndependent_iff.1 hb (fun i => (c i : Fv F v) - ϖ * d i)
        (by simp only [sub_smul, Finset.sum_sub_distrib, e, sub_self])
      exact sub_eq_zero.1 (h0 i)
    · intro h
      choose d hd using fun i => h i (Set.mem_univ i)
      refine ⟨∑ i, (d i : Fv F v) • b i, (hmem _).2 ⟨d, rfl⟩, ?_⟩
      show sc (E := E) v ϖ • ∑ i, (d i : Fv F v) • b i = ∑ i, (c i : Fv F v) • b i
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [sc_smul_smul, hd i]
  rw [AddSubgroup.relIndex, ← AddSubgroup.index_comap_of_surjective _ hφs, key, AddSubgroup.index_pi]
  simp only [hR ϖ hϖ, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

end PI.OmLocU
end
end

section

noncomputable section

namespace PI.OmLocU.Red

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain Formalism.UG
open PI.VolStabSW PI.OmLocU
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F))

abbrev IE : Ideal (𝓞 E) := v.asIdeal.map (algebraMap (𝓞 F) (𝓞 E))

abbrev QE : Type := 𝓞 E ⧸ IE (E := E) v

def sigO : 𝓞 E →+* 𝓞 E := RingOfIntegers.mapRingHom (σ : E →+* E)

theorem sigO_coe (x : 𝓞 E) : (sigO σ x : E) = σ (x : E) := rfl

theorem sigO_alg (a : 𝓞 F) : sigO σ (algebraMap (𝓞 F) (𝓞 E) a) = algebraMap (𝓞 F) (𝓞 E) a := by
  apply RingOfIntegers.ext
  rw [sigO_coe]
  show σ (algebraMap (𝓞 E) E (algebraMap (𝓞 F) (𝓞 E) a)) = algebraMap (𝓞 E) E (algebraMap (𝓞 F) (𝓞 E) a)
  rw [← IsScalarTower.algebraMap_apply (𝓞 F) (𝓞 E) E, IsScalarTower.algebraMap_apply (𝓞 F) F E]
  exact σ.commutes _

theorem IE_le : IE (E := E) v ≤ (IE (E := E) v).comap (sigO σ) := by
  rw [← Ideal.map_le_iff_le_comap, Ideal.map_map]
  have hc : (sigO σ).comp (algebraMap (𝓞 F) (𝓞 E)) = algebraMap (𝓞 F) (𝓞 E) := RingHom.ext (sigO_alg σ)
  rw [hc]

def sigQ : QE (E := E) v →+* QE (E := E) v := Ideal.quotientMap (IE (E := E) v) (sigO σ) (IE_le σ v)

theorem sigQ_mk (x : 𝓞 E) : sigQ σ v (Ideal.Quotient.mk _ x) = Ideal.Quotient.mk _ (sigO σ x) := rfl

theorem sig_sig (h : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply τ.injective
  rw [h.2.2.2 τ, h.2.2.2 τ, star_star]

theorem sigQ_sigQ (h : IsCMExt F E σ) (x : QE (E := E) v) : sigQ σ v (sigQ σ v x) = x := by
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [sigQ_mk, sigQ_mk]
  congr 1
  apply RingOfIntegers.ext
  simp only [sigO_coe]
  exact sig_sig σ h _

theorem sigQ_alg (c : 𝓞 F ⧸ v.asIdeal) :
    sigQ σ v (algebraMap (𝓞 F ⧸ v.asIdeal) (QE (E := E) v) c) = algebraMap (𝓞 F ⧸ v.asIdeal) (QE (E := E) v) c := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective c
  rw [Ideal.Quotient.algebraMap_quotient_map_quotient, sigQ_mk, sigO_alg]

def ResQ : Prop :=
  StdHyp σ J ψ → UnramAt (E := E) v → ∀ ϖ : Fv F v, IsUnif v ϖ →
    ∃ ρ : OR (E := E) v →+* QE (E := E) v, IsRes σ v ϖ (sigQ σ v) ρ

def EtaLink : Prop :=
  StdHyp σ J ψ → UnramAt (E := E) v → (etaV (E := E) v = 1 ↔ ¬ (IE (E := E) v).IsPrime)

def QInert : Prop :=
  StdHyp σ J ψ → UnramAt (E := E) v → (IE (E := E) v).IsPrime → sigQ σ v ≠ RingHom.id _

def QSplit : Prop :=
  StdHyp σ J ψ → UnramAt (E := E) v → ¬ (IE (E := E) v).IsPrime →
    ∃ e : QE (E := E) v ≃+* (𝓞 F ⧸ v.asIdeal) × (𝓞 F ⧸ v.asIdeal), ∀ x, e (sigQ σ v x) = (e x).swap

theorem card_res : Nat.card (𝓞 F ⧸ v.asIdeal) = Ideal.absNorm v.asIdeal := by
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]

theorem finite_res : Finite (𝓞 F ⧸ v.asIdeal) := by
  apply Nat.finite_of_card_ne_zero
  rw [card_res]
  exact fun h => v.ne_bot (Ideal.absNorm_eq_zero_iff.mp h)

theorem IE_ne_bot : IE (E := E) v ≠ ⊥ := by
  exact Ideal.map_ne_bot_of_ne_bot v.ne_bot

end PI.OmLocU.Red
end
end

section

noncomputable section

namespace PI.OmLocU

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain MeasureTheory
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F)) (Λ : Set (Fin n → E))

theorem omLocU_of_onto (a : ℕ) (Y : TupV (E := E) v n a)
    (hSd : (StdHyp σ J ψ → (∃ μ, SdW F E σ n J (Fv F v) (psiV F ψ v) a μ) ∧ ∃ ν, SdHerm F E σ (Fv F v) (psiV F ψ v) a ν))
    (hOm : OmUnique σ J ψ v a) (h1 : OrbAll σ J ψ v Λ a Y) (hO : HensOnto σ J v Λ ψ a Y)
    (hFull : ∃ L : Submodule (𝓞 E) (Fin n → E),
      Submodule.IsFullLattice E L ∧ (L : Set (Fin n → E)) = Λ)
    (h3 : CountU σ J ψ v Λ a Y) (h4 : SdVolW σ J ψ v Λ a) (h5 : SdVolH σ J ψ v a) :
    Formalism.L2.SG.Pf.NcLoc.OmLocU σ J ψ v Λ a Y :=
  omLocU_of_hens σ J ψ v Λ a Y hSd hOm h1 hFull (fibHens_of σ J v Λ ψ a Y hO) h3 h4 h5

theorem omLocU_of_tr (a : ℕ) (Y : TupV (E := E) v n a)
    (hSd : (StdHyp σ J ψ → (∃ μ, SdW F E σ n J (Fv F v) (psiV F ψ v) a μ) ∧ ∃ ν, SdHerm F E σ (Fv F v) (psiV F ψ v) a ν))
    (hOm : OmUnique σ J ψ v a) (h1 : OrbAll σ J ψ v Λ a Y) (hGI : GramInvO σ J v Λ ψ a Y) (hTr : TrOnto σ v)
    (hFull : ∃ L : Submodule (𝓞 E) (Fin n → E),
      Submodule.IsFullLattice E L ∧ (L : Set (Fin n → E)) = Λ)
    (h3 : CountU σ J ψ v Λ a Y) (h4 : SdVolW σ J ψ v Λ a) (h5 : SdVolH σ J ψ v a) :
    Formalism.L2.SG.Pf.NcLoc.OmLocU σ J ψ v Λ a Y :=
  omLocU_of_onto σ J ψ v Λ a Y hSd hOm h1 (hensOnto_of σ J v Λ ψ a Y hGI hTr) hFull h3 h4 h5

end PI.OmLocU
end
end
