module

public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle006
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle025
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsPrincipalIdealRingOfHenselian
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle056
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle001
public import Mathlib.NumberTheory.NumberField.Discriminant.Defs
public import Mathlib.RingTheory.FractionalIdeal.Norm
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle004
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FramePairCoordinatesTransportUnitaryMass
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle003
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle053
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TupleJacobianRightMulIsometry
public import Mathlib.Order.CompletePartialOrder
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle054
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BasisOfIsCompl
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle037
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SelfDualLatticeUnipotentTranslateStandard
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle042
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermInvariantsIndependentOfWitnesses
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle055
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FramesCharactersAgreeCommonStabiliser
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FramesCommonStabiliserEqPairingMatrixStabiliser
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MemConfTOfDetNeZero
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle015
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle045
import Formalism.FormalDegreeBessel.StatementWR
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes

@[expose] public section

section

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical

noncomputable section
namespace GlobalTheory.HL.SAN.IntParam

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]

theorem eich_int (L : LocE F E) {N : ℕ} {Hm : Matrix (Fin N) (Fin N) E}
    (hI : ∀ i j, Hm i j ∈ L.O) {x u v : Fin N → E} {s : E} (hx : ∀ j, x j ∈ L.O)
    (hu : ∀ j, u j ∈ L.O) (hs : s ∈ L.O) (hv : ∀ j, v j ∈ L.O) (j : Fin N) :
    eich L Hm x u s v j ∈ L.O := by
  simp only [eich, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  exact L.O.sub_mem (L.O.add_mem (hv j) (L.O.mul_mem (hf_int L hI hv hu) (hx j)))
    (L.O.mul_mem (hf_int L hI hv hx) (L.O.add_mem (hu j) (L.O.mul_mem hs (hx j))))

theorem prod_fix {N : ℕ} (y : Fin N → E) :
    ∀ l : List ((Fin N → E) ≃ₗ[E] (Fin N → E)), (∀ g ∈ l, g y = y) → l.prod y = y := by
  intro l
  induction l with
  | nil => intro _; simp
  | cons g l ih =>
    intro h
    rw [List.prod_cons, LinearEquiv.mul_apply, ih (fun g' hg' => h g' (List.mem_cons_of_mem _ hg')),
      h g List.mem_cons_self]

theorem finiteRing_sq_sub_mul_sq_eq_of_card (L : LocE F E) (N : ℕ) (Hm : Matrix (Fin N) (Fin N) E) (hH : IsHerm L Hm)
    (hI : ∀ i j, Hm i j ∈ L.O) : ∀ (r : ℕ) (X Y u : Fin r → Fin N → E) (s : Fin r → E)
    (e : Fin r → (Fin N → E) ≃ₗ[E] (Fin N → E)), (∀ i j, X i j ∈ L.O) → (∀ i j, Y i j ∈ L.O) →
    (∀ a b, hf L Hm (X a) (Y b) = if a = b then 1 else 0) → (∀ a b, hf L Hm (X a) (X b) = 0) →
    (∀ i, ∀ j, j ≤ i → hf L Hm (u i) (X j) = 0 ∧ hf L Hm (u i) (Y j) = 0) →
    (∀ i, s i + L.cj (s i) = hf L Hm (u i) (u i)) →
    (∀ i v, e i v = eich L Hm (X i) (u i) (s i) v) →
    (∀ x : Fin N → E, (∀ j, (List.ofFn e).prod x j ∈ L.O) ↔ ∀ j, x j ∈ L.O) →
    (∀ i j, u i j ∈ L.O) ∧ ∀ i, s i ∈ L.O := by
  intro r
  induction r with
  | zero => intro X Y u s e _ _ _ _ _ _ _ _; exact ⟨fun i => i.elim0, fun i => i.elim0⟩
  | succ r ih =>
    intro X Y u s e hX hY hXY hXX hu hs he hn
    set n' := (List.ofFn fun i : Fin r => e i.succ).prod with hn'def
    have hprod : ∀ x, (List.ofFn e).prod x = e 0 (n' x) := by
      intro x; rw [List.ofFn_succ, List.prod_cons, LinearEquiv.mul_apply]

    have hfix : n' (Y 0) = Y 0 := by
      refine prod_fix (Y 0) _ fun g hg => ?_
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hg
      have h1 : hf L Hm (Y 0) (u i.succ) = 0 := by
        rw [← GlobalTheory.HL.Eichler.hf_cj L hH, (hu i.succ 0 (Fin.zero_le _)).2, map_zero]
      have h2 : hf L Hm (Y 0) (X i.succ) = 0 := by
        rw [← GlobalTheory.HL.Eichler.hf_cj L hH, hXY, if_neg (Fin.succ_ne_zero i), map_zero]
      rw [he, eich, h1, h2]; simp
    have h0 : e 0 (Y 0) = Y 0 - (u 0 + s 0 • X 0) := by
      have h1 : hf L Hm (Y 0) (u 0) = 0 := by
        rw [← GlobalTheory.HL.Eichler.hf_cj L hH, (hu 0 0 le_rfl).2, map_zero]
      have h2 : hf L Hm (Y 0) (X 0) = 1 := by
        rw [← GlobalTheory.HL.Eichler.hf_cj L hH, hXY, if_pos rfl, map_one]
      rw [he, eich, h1, h2]; simp
    have hnY : ∀ j, (List.ofFn e).prod (Y 0) j ∈ L.O := (hn (Y 0)).2 (hY 0)
    rw [hprod, hfix, h0] at hnY
    have hw : ∀ j, (u 0 + s 0 • X 0) j ∈ L.O := by
      intro j
      have := L.O.sub_mem (hY 0 j) (hnY j)
      simpa using this
    have hs0 : s 0 ∈ L.O := by
      have h := hf_int L hI hw (hY 0)
      rwa [GlobalTheory.HL.Eichler.hf_add_l, GlobalTheory.HL.Eichler.hf_smul_l, (hu 0 0 le_rfl).2, hXY, if_pos rfl,
        mul_one, zero_add] at h
    have hu0 : ∀ j, u 0 j ∈ L.O := by
      intro j
      have h := L.O.sub_mem (hw j) (L.O.mul_mem hs0 (hX 0 j))
      simpa using h

    have he0 : ∀ x, (∀ j, e 0 x j ∈ L.O) ↔ ∀ j, x j ∈ L.O := by
      intro x
      constructor
      · intro h j
        have hinv := GlobalTheory.HL.Eichler.eich_inv L hH (X 0) (u 0) (s 0) (hXX 0 0) (hu 0 0 le_rfl).1 (hs 0) x
        rw [← hinv, ← he]
        exact eich_int L hI (hX 0) (fun k => L.O.neg_mem (hu0 k)) (GlobalTheory.UnramOrder.cj_mem L hs0) h j
      · intro h j
        rw [he]
        exact eich_int L hI (hX 0) hu0 hs0 h j
    have hn2 : ∀ x : Fin N → E, (∀ j, (List.ofFn fun i : Fin r => e i.succ).prod x j ∈ L.O) ↔
        ∀ j, x j ∈ L.O := by
      intro x
      rw [← hn x, hprod, ← hn'def]
      exact (he0 (n' x)).symm
    obtain ⟨hU, hS⟩ := ih (fun i => X i.succ) (fun i => Y i.succ) (fun i => u i.succ)
      (fun i => s i.succ) (fun i => e i.succ) (fun i => hX i.succ) (fun i => hY i.succ)
      (fun a b => by rw [hXY]; simp only [Fin.succ_inj]) (fun a b => hXX a.succ b.succ)
      (fun i j hj => hu i.succ j.succ (Fin.succ_le_succ_iff.mpr hj)) (fun i => hs i.succ)
      (fun i v => he i.succ v) hn2
    refine ⟨fun i => Fin.cases hu0 (fun i => hU i) i, fun i => Fin.cases hs0 (fun i => hS i) i⟩

theorem eich_prod_params_int : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E) (N r : ℕ) (Hm : Matrix (Fin N) (Fin N) E) (hH : IsHerm L Hm) (hI : ∀ i j, Hm i j ∈ L.O) (X Y u : Fin r → Fin N → E) (s : Fin r → E) (e : Fin r → (Fin N → E) ≃ₗ[E] (Fin N → E)) (hX : ∀ i j, X i j ∈ L.O) (hY : ∀ i j, Y i j ∈ L.O) (hXY : ∀ a b, hf L Hm (X a) (Y b) = if a = b then 1 else 0) (hXX : ∀ a b, hf L Hm (X a) (X b) = 0) (hu : ∀ i, ∀ j, j ≤ i → hf L Hm (u i) (X j) = 0 ∧ hf L Hm (u i) (Y j) = 0) (hs : ∀ i, s i + L.cj (s i) = hf L Hm (u i) (u i)) (he : ∀ i v, e i v = eich L Hm (X i) (u i) (s i) v) (hn : ∀ x : Fin N → E, (∀ j, (List.ofFn e).prod x j ∈ L.O) ↔ ∀ j, x j ∈ L.O), (∀ i j, u i j ∈ L.O) ∧ ∀ i, s i ∈ L.O := by
  intro F _ _ _ _ _ E _ _ _ L N r Hm hH hI X Y u s e hX hY hXY hXX hu hs he hn
  exact finiteRing_sq_sub_mul_sq_eq_of_card L N Hm hH hI r X Y u s e hX hY hXY hXX hu hs he hn

end GlobalTheory.HL.SAN.IntParam
end
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN GlobalTheory.SnMass.SkewVol
open scoped TensorProduct ENNReal nonZeroDivisors Classical

theorem _root_.GlobalTheory.T.absNorm_inverseDifferentIdealPow_eq_discr : ∀ (K : Type) [Field K] [NumberField K] (j : ℕ), (FractionalIdeal.absNorm (dInv K j) : ℝ) = (|(discr K : ℝ)| ^ j)⁻¹ := by
  first | exact @GlobalTheory.SnMass.VolN.absNorm_dInv_eq_abs_discr_pow_inv | exact GlobalTheory.SnMass.VolN.absNorm_dInv_eq_abs_discr_pow_inv | (intros; apply GlobalTheory.SnMass.VolN.absNorm_dInv_eq_abs_discr_pow_inv <;> assumption)
end

section

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

theorem _root_.GlobalTheory.T.tuple_jacobian_rightMul_isometry : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (ϖ : 𝒪[F]), Irreducible ϖ → ∀ {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E), IsHermND L Hm → ∀ Λ, IsSD L Hm Λ → ∀ m : ℕ, (∀ A : Matrix (Fin m) (Fin m) E, IsUnit A.det → ∀ T, IsCO (tupLat L Λ m) T → IsCO (tupLat L Λ m) ((fun x => rmul x A) '' T) ∧ cont (tupLat L Λ m) ((fun x => rmul x A) '' T) = (resQ ϖ : ℝ) ^ (-(vE L ϖ (A.det * L.cj A.det) * n)) * cont (tupLat L Λ m) T) ∧ ∀ g ∈ isomG L Hm, ∀ T, IsCO (tupLat L Λ m) T → IsCO (tupLat L Λ m) ((fun x a => g (x a)) '' T) ∧ cont (tupLat L Λ m) ((fun x a => g (x a)) '' T) = cont (tupLat L Λ m) T := by
  first | exact @GlobalTheory.HL.TupleJac.tuple_jacobian | exact GlobalTheory.HL.TupleJac.tuple_jacobian | (intros; apply GlobalTheory.HL.TupleJac.tuple_jacobian <;> assumption)
end

section

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

theorem _root_.GlobalTheory.T.commensurableCosetUnionContent_biUnion : ∀ {W : Type} [AddCommGroup W] (W0 : AddSubgroup W) {ι : Type} (s : Finset ι) (S : ι → Set W), (∀ i ∈ s, IsCO W0 (S i)) → IsCO W0 (⋃ i ∈ s, S i) ∧ ((∀ i ∈ s, ∀ j ∈ s, i ≠ j → Disjoint (S i) (S j)) → cont W0 (⋃ i ∈ s, S i) = ∑ i ∈ s, cont W0 (S i)) := by
  first | exact @GlobalTheory.HL.cont_biUnion | exact GlobalTheory.HL.cont_biUnion | (intros; apply GlobalTheory.HL.cont_biUnion <;> assumption)
end

section

open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc GlobalTheory.HL
open scoped Pointwise ENNReal Classical

theorem _root_.GlobalTheory.T.framePairCoordinates_transport_unitary_mass : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r k : ℕ) (P : LocNG.FPair H r), ∀ (S : Frames M.L r k) (c : Coord P S), (∀ g, g ∈ P.UW0 ↔ c.grp g ∈ S.H0) ∧ (∀ g, g ∈ P.K0 ↔ c.grp g ∈ S.K0) ∧ Function.Bijective c.lat ∧ (∀ g Λ, c.lat (LocNG.img g Λ) = c.grp g • c.lat Λ) ∧ (∀ g Λ, g ∈ LocNG.Aut Λ ↔ c.grp g ∈ MulAction.stabilizer S.GLV (c.lat Λ)) ∧ ∀ t : Term V M r, LocNG.mu P t = S.mu (c.lat t.abelian₂) := by
  first | exact @GlobalTheory.HL.CoordMass.transport | exact GlobalTheory.HL.CoordMass.transport | (intros; apply GlobalTheory.HL.CoordMass.transport <;> assumption)
end

section

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

theorem _root_.GlobalTheory.T.exists_nondegenerate_tuple_complement_fixer : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∃ x : Fin (2 * r + 2) → S.V, IsUnit (gramT L S.Hm x).det ∧ Submodule.span E (Set.range x) = S.ME ∧ S.H0 = fixG L S.Hm S.ME ∧ IsLat L (Submodule.span L.O (Set.range fun i => (Pi.single i 1 : S.V))) ∧ (∀ Mh, S.massSig Mh = sigMass L S.Hm S.ME (Submodule.span L.O (Set.range fun i => (Pi.single i 1 : S.V))) Mh) ∧ ∀ C, S.IsCls C → ∀ p ∈ C, ∃ (y : Fin (2 * r + 2) → S.V) (B : Matrix (Fin (2 * r + 2)) (Fin (2 * r + 2)) E), B.det * L.cj B.det = 1 ∧ y = rmul x B ∧ S.Mof p.1 p.2 = Submodule.span L.O (Set.range y) := by
  first | exact @GlobalTheory.HL.FrameTuple.main | exact GlobalTheory.HL.FrameTuple.main | (intros; apply GlobalTheory.HL.FrameTuple.main <;> assumption)
end

section

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.PrimTerm

section
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)

theorem spanTo_top (g : Fin (r + 1) → S.V) :
    S.spanTo g (r + 1) = Submodule.span E (Set.range g) := by
  unfold Frames.spanTo
  congr 1
  ext x
  constructor
  · rintro ⟨i, -, rfl⟩
    exact ⟨i, rfl⟩
  · rintro ⟨i, rfl⟩
    exact ⟨i, i.2, rfl⟩

theorem left_mem (g g' : Fin (r + 1) → S.V) (b : Fin (r + 1)) : g b ∈ S.Mof g g' :=
  Submodule.subset_span (Or.inl ⟨b, rfl⟩)

theorem diff_mem (g g' : Fin (r + 1) → S.V) (b : Fin (r + 1)) :
    algebraMap F E S.th⁻¹ • (g' b - g b) ∈ S.Mof g g' :=
  Submodule.subset_span (Or.inr ⟨b, rfl⟩)

theorem th_smul (h0 : S.th ≠ 0) (v : S.V) :
    algebraMap F E S.th • algebraMap F E S.th⁻¹ • v = v := by
  rw [smul_smul, ← map_mul, mul_inv_cancel₀ h0, map_one, one_smul]

theorem Mof_le_swap (h0 : S.th ≠ 0) (hO : algebraMap F E S.th ∈ L.O) (g g' : Fin (r + 1) → S.V) :
    S.Mof g' g ≤ S.Mof g g' := by
  refine Submodule.span_le.2 ?_
  rintro x (⟨b, rfl⟩ | ⟨b, rfl⟩)
  · have h1 := (S.Mof g g').smul_mem ⟨_, hO⟩ (diff_mem S g g' b)
    have h2 : (⟨_, hO⟩ : L.O) • algebraMap F E S.th⁻¹ • (g' b - g b) = g' b - g b :=
      th_smul S h0 _
    rw [h2] at h1
    have h3 := (S.Mof g g').add_mem h1 (left_mem S g g' b)
    rwa [sub_add_cancel] at h3
  · have h1 := (S.Mof g g').neg_mem (diff_mem S g g' b)
    rw [← smul_neg, neg_sub] at h1
    exact h1

theorem Mof_swap (h0 : S.th ≠ 0) (hO : algebraMap F E S.th ∈ L.O) (g g' : Fin (r + 1) → S.V) :
    S.Mof g' g = S.Mof g g' :=
  le_antisymm (Mof_le_swap S h0 hO g g') (Mof_le_swap S h0 hO g' g)

theorem mem_span_of_mem_Mof (P P' : Submodule E S.V) (hd : Disjoint P P')
    (g g' : Fin (r + 1) → S.V) (hg : ∀ b, g b ∈ P) (hg' : ∀ b, g' b ∈ P')
    (hi : LinearIndependent E g') (x : S.V) (hx : x ∈ S.Mof g g') (hP : x ∈ P) :
    x ∈ Submodule.span L.O (Set.range g) := by
  unfold Frames.Mof at hx
  rw [Submodule.span_union] at hx
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hx
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun L.O).1 hz
  have hyP : y ∈ P := by
    have : Submodule.span L.O (Set.range g) ≤ P.restrictScalars L.O := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨b, rfl⟩
      exact hg b
    exact this hy
  set e : Fin (r + 1) → E := fun b => (c b : E) * algebraMap F E S.th⁻¹ with he
  have hs : ∑ b, c b • algebraMap F E S.th⁻¹ • (g' b - g b) = ∑ b, e b • g' b - ∑ b, e b • g b := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [← smul_sub, he, mul_smul]
    rfl
  rw [hs] at hP ⊢
  have h1 : ∑ b, e b • g b ∈ P := P.sum_mem fun b _ => P.smul_mem _ (hg b)
  have h2 : ∑ b, e b • g' b ∈ P' := P'.sum_mem fun b _ => P'.smul_mem _ (hg' b)
  have h3 : ∑ b, e b • g' b ∈ P := by
    have := P.add_mem (P.sub_mem hP hyP) h1
    rwa [add_sub_cancel_left, sub_add_cancel] at this
  have h4 : ∑ b, e b • g' b = 0 := (Submodule.disjoint_def.1 hd) _ h3 h2
  have h5 : ∀ b, e b = 0 := Fintype.linearIndependent_iff.1 hi e h4
  simpa [h5] using hy

theorem trace_iff (Λ : Submodule L.O S.V) (f f' g g' : Fin (r + 1) → S.V)
    (hd : Disjoint (Submodule.span E (Set.range f)) (Submodule.span E (Set.range f')))
    (hg : ∀ b, g b ∈ Submodule.span E (Set.range f))
    (hg' : ∀ b, g' b ∈ Submodule.span E (Set.range f'))
    (hi : LinearIndependent E g') (hME : S.spanTo f (r + 1) ≤ S.ME) (hs : S.sat Λ = S.Mof g g')
    (x : S.V) : (x ∈ Λ ∧ x ∈ S.spanTo f (r + 1)) ↔ x ∈ Submodule.span L.O (Set.range fun b => g b) := by
  constructor
  · rintro ⟨h1, h2⟩
    have h3 : x ∈ S.sat Λ := ⟨h1, hME h2⟩
    rw [hs] at h3
    rw [spanTo_top] at h2
    exact mem_span_of_mem_Mof S _ _ hd g g' hg hg' hi x h3 h2
  · intro hx
    have : Submodule.span L.O (Set.range fun b => g b) ≤
        Λ ⊓ (S.spanTo f (r + 1)).restrictScalars L.O := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨b, rfl⟩
      have h1 : g b ∈ S.sat Λ := hs ▸ left_mem S g g' b
      refine ⟨h1.1, ?_⟩
      change g b ∈ S.spanTo f (r + 1)
      rw [spanTo_top]
      exact hg b
    exact this hx

end

theorem term_of_primitive : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ Λ, IsSD L S.Hm Λ → ∀ C, S.IsCls C → ∀ p ∈ C, S.sat Λ = S.Mof p.1 p.2 → ∃ d, S.IsTerm d Λ ∧ S.Fr d Λ = C ∧ S.BBzero d Λ := by
  intro F _ _ _ _ _ E _ _ _ L r k S Λ hΛ C hC p hp hs
  obtain ⟨n, hn, n', hn', rfl⟩ := hC
  rw [((GlobalTheory.HL.FrameClass.frame_classes L r k S _ _).2.1 p hp).2] at hs
  obtain ⟨hli, -, -, -, -, h0, hth, -⟩ := GlobalTheory.FrameBasic.main L r k S
  obtain ⟨hon, hon', -⟩ := GlobalTheory.HL.FrameOnto.unipotent_onto L r k S
  have hO : algebraMap F E S.th ∈ L.O :=
    (L.O_def _).2 (isIntegral_algebraMap (R := 𝒪[F]) (A := E) (x := ⟨S.th, hth⟩))
  obtain ⟨hf, hf', hd⟩ := linearIndependent_sum.1 hli
  have hf1 : LinearIndependent E S.f := hf
  have hf2 : LinearIndependent E S.f' := hf'
  have hd1 : Disjoint (Submodule.span E (Set.range S.f)) (Submodule.span E (Set.range S.f')) := hd
  have hi : LinearIndependent E fun b => n (S.f b) :=
    hf1.map' (n : S.V →ₗ[E] S.V) n.ker
  have hi' : LinearIndependent E fun b => n' (S.f' b) :=
    hf2.map' (n' : S.V →ₗ[E] S.V) n'.ker
  have hg : ∀ b, n (S.f b) ∈ Submodule.span E (Set.range S.f) := by
    obtain ⟨s, -, h⟩ := hon n hn
    intro b
    rw [h b]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hg' : ∀ b, n' (S.f' b) ∈ Submodule.span E (Set.range S.f') := by
    obtain ⟨s, -, h⟩ := hon' n' hn'
    intro b
    rw [h b]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  obtain ⟨A, hA, m, hm, hme, hΛA⟩ := GlobalTheory.HL.FrameLift.lift L r k S S.f S.es (Or.inl ⟨rfl, rfl⟩) Λ hΛ n hn
    (trace_iff S Λ S.f S.f' _ _ hd1 hg hg' hi' le_sup_left hs)
  obtain ⟨A', hA', m', hm', hme', hΛA'⟩ := GlobalTheory.HL.FrameLift.lift L r k S S.f' S.es' (Or.inr ⟨rfl, rfl⟩) Λ hΛ n' hn'
    (trace_iff S Λ S.f' S.f _ _ hd1.symm hg' hg hi le_sup_right (hs.trans (Mof_swap S h0 hO _ _)))
  have hW : S.IsTermW (A, A', S.graphOf Λ) Λ m m' := by
    refine ⟨hA, hA', hm, hm', hΛA, hΛA', fun b => ?_, rfl⟩
    rw [hme, hme']
    have h1 := diff_mem S (fun b => n (S.f b)) (fun b => n' (S.f' b)) b
    rw [← hs] at h1
    exact ⟨_, h1.1, (th_smul S h0 _).symm⟩
  obtain ⟨-, hM, hFr, -⟩ := GlobalTheory.HL.WitIndep.witness_independence L r k S _ _ _ _ hW
  simp only [hme, hme'] at hM hFr
  exact ⟨_, ⟨(m, m'), hW⟩, hFr, hM.trans hs.symm⟩

end GlobalTheory.HL.PrimTerm
end

section

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

theorem _root_.GlobalTheory.T.frameMove_character_ne_one : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ (j : Fin r) (β βJ : ℕ) (d : S.Datum) (Λ : Submodule L.O S.V), S.IsTerm d Λ → S.InFF β (j + 1) βJ d Λ → ∀ x ∈ S.spanTo S.f (j + 1), ∀ x' ∈ S.spanTo S.f' (j + 1), S.InTh Λ (x + x') → S.lev (S.fr d Λ) (S.fr' d Λ) (x + x') = j + 1 → ∀ al al' : Fin (r + 1) → E, x = ∑ i, al i • S.fr d Λ i → x' = ∑ i, al' i • S.fr' d Λ i → ∃ u ∈ Λ, u ∈ perp L S.Hm (S.spanTo S.f (j + 1) ⊔ S.spanTo S.f' (j + 1)) ∧ L.psi0 (-(algebraMap F E S.th⁻¹ * S.h (al j.castSucc • S.fr d Λ j.succ + al' j.castSucc • S.fr' d Λ j.succ) u)) ≠ 1 := by
  first | exact @GlobalTheory.HL.MoveChar.chi_ne_one | exact GlobalTheory.HL.MoveChar.chi_ne_one | (intros; apply GlobalTheory.HL.MoveChar.chi_ne_one <;> assumption)
end

section

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical

theorem _root_.GlobalTheory.T.hermitianFlagUnipotent_normalForm_rescaled : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E) (r k : ℕ) (S : Frames L r k) (g : Fin (r + 1) → S.V) (gs : Fin r → S.V) (hsel : (g = S.f ∧ gs = S.es) ∨ (g = S.f' ∧ gs = S.es')) (a : Fin r → Fˣ) (X Y : Fin r → S.V) (hX : ∀ i, algebraMap F E (a i) • g i.castSucc = X i) (hY : ∀ i, gs i = algebraMap F E (a i) • Y i), (∀ i j, S.h (X i) (Y j) = if i = j then 1 else 0) ∧ (∀ i j, S.h (X i) (X j) = 0) ∧ (∀ i j, S.h (Y i) (Y j) = 0) ∧ ∀ n : S.GLV, n ∈ S.Nof g ↔ ∃ (u : Fin r → S.V) (s : Fin r → E) (e : Fin r → S.GLV), (∀ i, (∀ j, j ≤ i → S.h (u i) (X j) = 0 ∧ S.h (u i) (Y j) = 0) ∧ s i + L.cj (s i) = S.h (u i) (u i) ∧ ∀ v, e i v = eich L S.Hm (X i) (u i) (s i) v) ∧ n = (List.ofFn e).prod := by
  first | exact @GlobalTheory.HL.nof_normal_form_rescaled | exact GlobalTheory.HL.nof_normal_form_rescaled | (intros; apply GlobalTheory.HL.nof_normal_form_rescaled <;> assumption)
end

section

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

theorem _root_.GlobalTheory.T.term_frames_congr_mod_theta_unitriangular : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : Formalism.MainNotions.S.Loc.LocE F E) (r k : ℕ) (S : GlobalTheory.HL.Frames L r k) (d : S.Datum) (Λ : Submodule L.O S.V), S.IsTerm d Λ → ∀ (y x : Fin (r + 1) → S.V) (B B' : Matrix (Fin (r + 1)) (Fin (r + 1)) E), (∀ a b, b < a → B a b = 0) → (∀ a, B a a = 1) → (∀ a b, b < a → B' a b = 0) → (∀ a, B' a a = 1) → (∀ b, y b = ∑ a, B a b • S.f a) → (∀ b, x b = ∑ a, B' a b • S.f' a) → (∀ a, y a ∈ Λ) → (∀ b, x b ∈ Λ) → ∃ ξ : Matrix (Fin (r + 1)) (Fin (r + 1)) E, (∀ a b, ξ a b ∈ L.O) ∧ (∀ a b, b < a → ξ a b = 0) ∧ (∀ a, ξ a a = 1) ∧ ∀ b, S.InTh Λ (x b - ∑ a, ξ a b • y a) := by
  first | exact @GlobalTheory.HL.FrameChange.frames_congr | exact GlobalTheory.HL.FrameChange.frames_congr | (intros; apply GlobalTheory.HL.FrameChange.frames_congr <;> assumption)
end

section

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

theorem _root_.GlobalTheory.T.frames_characters_agree_commonStabiliser : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ h ∈ S.St, S.psi h = S.psi' h := by
  first | exact @GlobalTheory.HL.CharAgree.psi_eq_psi' | exact GlobalTheory.HL.CharAgree.psi_eq_psi' | (intros; apply GlobalTheory.HL.CharAgree.psi_eq_psi' <;> assumption)
end

section

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

theorem _root_.GlobalTheory.T.frames_commonStabiliser_eq_pairingMatrix_stabiliser : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), (∀ h ∈ S.St, ∀ w ∈ S.W0, h w = w) ∧ ∀ s s' : Matrix (Fin (r + 1)) (Fin (r + 1)) E, ((∀ i j, j < i → s i j = 0) ∧ (∀ i, s i i = 1)) → ((∀ i j, j < i → s' i j = 0) ∧ (∀ i, s' i i = 1)) → (cT L s * S.Zh * s' = S.Zh ↔ ∃ h ∈ S.St, (∀ j, h (S.f j) = ∑ i, s i j • S.f i) ∧ ∀ j, h (S.f' j) = ∑ i, s' i j • S.f' i) := by
  first | exact @GlobalTheory.HL.FrameStab.stab_eq | exact GlobalTheory.HL.FrameStab.stab_eq | (intros; apply GlobalTheory.HL.FrameStab.stab_eq <;> assumption)
end
