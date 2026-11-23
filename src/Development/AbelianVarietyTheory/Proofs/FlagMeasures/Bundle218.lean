module

public import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.Bundle001
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle074
public import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPrAlt
public import Formalism.FlagUnipotentLattices.UnipotentStabiliserCharacterisation
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle076
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle060
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle010
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle140
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle290
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle385
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle004
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle206
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle008
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsRiemannianHaarUnitaryJSubgroupOfAlgebra
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FlagNilradicalFinrankAndAbsDetConj
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LeftQuotientCovolumeWithDensityDetNormSq
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle009
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GaugeVolumeEqOfSemilinearIsometryGenus
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GradedPieceSizesUnipotentLeviCompactMove
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RadicalCoordinatesBoundedMajorantLengths
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle010
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle203
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle011
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.UpperOff
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle007

@[expose] public section

section

open BranchingSupport GlobalTheory.CellAmp GlobalTheory.Amp Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.GapSetup

theorem isFamG_of_num (k r : ℕ) (lam : Fin (2 * r + k + 1) → ℝ) (u : ℕ → ℝ) (b bv ga h : ℝ) (q0 : ℕ)
    (R : (Fin (2 * r + k + 1) → ℤ) → Rep k r) (hN : Num k r lam u b bv ga h q0) (hF : IsFam lam q0 R) :
    IsFamG lam q0 R := by
  have H := GlobalTheory.NumFam.num_fam k r lam u b bv ga h q0 hN
  intro ν hν
  have hd := hF ν hν
  exact ⟨hd.1, hd.2, ⟨h / 2, (H.2 ν hν).2.2.1, H.1.2.2.2.2⟩⟩

theorem families_gap : (∀ (k r : ℕ) (lam : Fin (2 * r + k + 1) → ℝ) (u : ℕ → ℝ) (b bv ga h : ℝ) (q0 : ℕ) (R : (Fin (2 * r + k + 1) → ℤ) → Rep k r), Num k r lam u b bv ga h q0 → IsFam lam q0 R → IsFamG lam q0 R) ∧ ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] (lam : Fin (2 * r + k + 1) → ℝ) (u : ℕ → ℝ) (b bv ga h : ℝ) (q0 : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (π : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (Wp →L[ℂ] Wp)) (μW μN μG νq : Measure (Mt k r)) (R : (Fin (2 * r + k + 1) → ℤ) → Rep k r) (lb : ∀ ν, (R ν).H → Wp) (dg : (Fin (2 * r + k + 1) → ℤ) → ℝ), Setup lam u b bv ga h q0 z π μW μN μG νq R lb dg ↔ SetupG lam u b bv ga h q0 z π μW μN μG νq R lb dg := by
  refine ⟨isFamG_of_num, ?_⟩
  intro k r Wp _ _ _ lam u b bv ga h q0 z π μW μN μG νq R lb dg
  constructor
  · rintro ⟨hN, hF, hS, hSF⟩
    exact ⟨hN, isFamG_of_num k r lam u b bv ga h q0 R hN hF, hS, hSF⟩
  · rintro ⟨hN, hF, hS, hSF⟩
    exact ⟨hN, fun ν hν => GlobalTheory.isDS_of_isDG (hF ν hν), hS, hSF⟩

end GlobalTheory.GapSetup
end

section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.FlagPartialWedge

open Formalism.HermitianLatticeCounting.ExpansionTerms (majorantDistance)

theorem len_castLE {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {l n : ℕ} (hl : l ≤ n)
    (y : Fin n → V) (a : Fin l) :
    majorantDistance (fun b : Fin l => y (Fin.castLE hl b)) a = majorantDistance y (Fin.castLE hl a) := by
  have ha := a.isLt
  have hS : (fun b : Fin l => y (Fin.castLE hl b)) '' {b | b < a} = y '' {b | b < Fin.castLE hl a} := by
    ext v
    constructor
    · rintro ⟨b, hb, rfl⟩
      refine ⟨Fin.castLE hl b, ?_, rfl⟩
      simp only [Set.mem_ofPred_eq, Fin.lt_def, Fin.val_castLE] at hb ⊢
      exact hb
    · rintro ⟨b, hb, rfl⟩
      simp only [Set.mem_ofPred_eq, Fin.lt_def, Fin.val_castLE] at hb
      refine ⟨⟨b.val, by omega⟩, ?_, ?_⟩
      · simp only [Set.mem_ofPred_eq, Fin.lt_def]
        exact hb
      · exact congrArg y (Fin.ext rfl)
  unfold majorantDistance
  rw [hS]

theorem fixes_partial_wedge_and_length : ∀ (k r l : ℕ) (hl : l ≤ r + 1) (z : Fin (2 * r + k + 1) → ℂ), Formalism.QuantumDeterminants.inWb k r z → (∀ s ∈ Formalism.QuantumDeterminants.Sset k r z, cmp l s *ᵥ (wedge (fun a : Fin l => Formalism.QuantumDeterminants.fvec k r z (Fin.castLE hl a))) = (wedge (fun a : Fin l => Formalism.QuantumDeterminants.fvec k r z (Fin.castLE hl a)))) ∧ ∀ g ∈ GG k r, ∑ J, ‖(cmp l g⁻¹ *ᵥ (wedge (fun a : Fin l => Formalism.QuantumDeterminants.fvec k r z (Fin.castLE hl a)))) J‖ ^ 2 = ∏ a : Fin l, lenA k r z g (Fin.castLE hl a) ^ 2 := by
  intro k r l hl z hz
  refine ⟨fun s hs => ?_, fun g _ => ?_⟩
  ·
    obtain ⟨U, hU0, hU1, hsF⟩ := Formalism.QuantumDeterminants.S_F hz hs
    rw [GlobalTheory.TensLen.cmp_mulVec_wedge]
    refine GlobalTheory.FlagFix.wedge_eq_of_mul _ _ (U.submatrix (Fin.castLE hl) (Fin.castLE hl)) ?_ ?_ ?_
    · intro c a hac
      simp only [Matrix.submatrix_apply]
      refine hU0 _ _ ?_
      simp only [Fin.lt_def, Fin.val_castLE] at hac ⊢
      exact hac
    · intro c
      simp only [Matrix.submatrix_apply]
      exact hU1 _
    · intro i a
      have ha := a.isLt
      show (s *ᵥ Formalism.QuantumDeterminants.fvec k r z (Fin.castLE hl a)) i =
        ∑ c : Fin l, Formalism.QuantumDeterminants.fvec k r z (Fin.castLE hl c) i * U (Fin.castLE hl c) (Fin.castLE hl a)
      have h1 := congrFun (congrFun hsF i) (Fin.castLE hl a)
      simp only [Matrix.mul_apply, Formalism.QuantumDeterminants.Fm, Matrix.of_apply] at h1
      have h2 : (s *ᵥ Formalism.QuantumDeterminants.fvec k r z (Fin.castLE hl a)) i =
          ∑ j, s i j * Formalism.QuantumDeterminants.fvec k r z (Fin.castLE hl a) j := rfl
      rw [h2, h1]
      refine Formalism.QuantumDeterminants.sum_fin_castLE hl _ ?_
      intro j hj
      show Formalism.QuantumDeterminants.fvec k r z j i * U j (Fin.castLE hl a) = 0
      rw [hU0 j (Fin.castLE hl a) ?_, mul_zero]
      rw [Fin.lt_def, Fin.val_castLE]
      omega
  ·
    rw [GlobalTheory.TensLen.cmp_mulVec_wedge, GlobalTheory.TensLen.sum_norm_wedge]
    refine Finset.prod_congr rfl (fun a _ => ?_)
    congr 1
    exact len_castLE hl (fun b : Fin (r + 1) =>
      (WithLp.toLp 2 (g⁻¹ *ᵥ Formalism.QuantumDeterminants.fvec k r z b) : EuclideanSpace ℂ (Fin (2 * r + k + 1)))) a

end GlobalTheory.FlagPartialWedge
end

section

open Polynomial Formalism.MainNotions.ArithmeticCylinders GlobalTheory.GLq GlobalTheory.GLm
open scoped Classical

namespace GlobalTheory.GLm.ProdChar

theorem isChar_of_irr {G : Type} [Group G] {χ : G → ℂ} (h : IsIrr χ) : IsChar χ := by
  obtain ⟨V, -, hV⟩ := h
  exact ⟨V, hV⟩

theorem eq_zero_of_ip {G : Type} [Group G] [Fintype G] {f : G → ℂ} (hf : IsClass f)
    (h : ∀ ρ, IsIrr ρ → ip f ρ = 0) : f = 0 := by
  calc f = ∑ᶠ ρ ∈ {ρ : G → ℂ | IsIrr ρ}, ip f ρ • ρ := (GlobalTheory.T.character_decomposition_and_classFunction_expansion G f).2.1 hf
    _ = ∑ᶠ ρ ∈ {ρ : G → ℂ | IsIrr ρ}, (0 : G → ℂ) :=
        finsum_mem_congr rfl fun ρ hρ => by rw [h ρ hρ, zero_smul]
    _ = 0 := finsum_mem_zero _

theorem ip_prod {G₁ G₂ : Type} [Group G₁] [Fintype G₁] [Group G₂] [Fintype G₂] (Φ : G₁ × G₂ → ℂ)
    (α : G₁ → ℂ) (β : G₂ → ℂ) :
    ip Φ (fun z => α z.1 * β z.2) = ip (fun y => ip (fun x => Φ (x, y)) α) β := by
  simp only [ip, Fintype.card_prod, Nat.cast_mul, Fintype.sum_prod_type, Prod.fst_inv, Prod.snd_inv,
    Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun x _ => by ring

theorem isIrr_prod {G₁ G₂ : Type} [Group G₁] [Fintype G₁] [Group G₂] [Fintype G₂]
    {α : G₁ → ℂ} {β : G₂ → ℂ} (hα : IsIrr α) (hβ : IsIrr β) :
    IsIrr (fun z : G₁ × G₂ => α z.1 * β z.2) := by
  have hA : IsChar (fun z : G₁ × G₂ => α z.1) :=
    (GlobalTheory.T.isCharacterOfFDRep_comp_hom_and_mul).1 (G₁ × G₂) G₁ (MonoidHom.fst G₁ G₂) α (isChar_of_irr hα)
  have hB : IsChar (fun z : G₁ × G₂ => β z.2) :=
    (GlobalTheory.T.isCharacterOfFDRep_comp_hom_and_mul).1 (G₁ × G₂) G₂ (MonoidHom.snd G₁ G₂) β (isChar_of_irr hβ)
  have hC : IsChar (fun z : G₁ × G₂ => α z.1 * β z.2) := (GlobalTheory.T.isCharacterOfFDRep_comp_hom_and_mul).2 (G₁ × G₂) _ _ hA hB
  apply (GlobalTheory.T.character_decomposition_and_classFunction_expansion (G₁ × G₂) _).2.2.2.1 hC
  have h1 : ip α α = 1 := by simpa using (GlobalTheory.T.centralIdempotentOfIrrCharacter_orthogonal_central G₁ α α hα hα).2.2
  have h2 : ip β β = 1 := by simpa using (GlobalTheory.T.centralIdempotentOfIrrCharacter_orthogonal_central G₂ β β hβ hβ).2.2
  have key : ∀ y, ip (fun x => α x * β y) α = β y := by
    intro y
    have e : ip (fun x => α x * β y) α = β y * ip α α := by
      simp only [ip, Finset.mul_sum]
      exact Finset.sum_congr rfl fun x _ => by ring
    rw [e, h1, mul_one]
  rw [ip_prod]
  simp only [key]
  exact h2

theorem exists_prod_of_isIrr {G₁ G₂ : Type} [Group G₁] [Fintype G₁] [Group G₂] [Fintype G₂]
    {ρ : G₁ × G₂ → ℂ} (hρ : IsIrr ρ) :
    ∃ p : (G₁ → ℂ) × (G₂ → ℂ), (IsIrr p.1 ∧ IsIrr p.2) ∧ ρ = fun z => p.1 z.1 * p.2 z.2 := by
  by_contra hne
  push Not at hne
  have hcl : IsClass ρ := (GlobalTheory.T.character_decomposition_and_classFunction_expansion _ ρ).2.2.1 (isChar_of_irr hρ)
  have hip : ∀ α β, IsIrr α → IsIrr β → ip ρ (fun z : G₁ × G₂ => α z.1 * β z.2) = 0 := by
    intro α β hα hβ
    rw [(GlobalTheory.T.centralIdempotentOfIrrCharacter_orthogonal_central _ ρ _ hρ (isIrr_prod hα hβ)).2.2,
      ite_eq_right (by simpa using hne (α, β) ⟨hα, hβ⟩)]
  have hrow : ∀ y, (fun x => ρ (x, y)) = 0 := by
    intro y
    apply eq_zero_of_ip
    · intro x k
      simpa using hcl (x, y) (k, 1)
    · intro α hα
      have hF : (fun y' => ip (fun x => ρ (x, y')) α) = 0 := by
        apply eq_zero_of_ip
        · intro y' h
          have e : (fun x => ρ (x, h * y' * h⁻¹)) = fun x => ρ (x, y') := by
            funext x
            simpa using hcl (x, y') (1, h)
          exact congrArg (fun f => ip f α) e
        · intro β hβ
          exact (ip_prod ρ α β).symm.trans (hip α β hα hβ)
      exact congrFun hF y
  have hz : ρ = 0 := by
    funext z
    obtain ⟨x, y⟩ := z
    exact congrFun (hrow y) x
  have h1 := (GlobalTheory.T.centralIdempotentOfIrrCharacter_orthogonal_central _ ρ ρ hρ hρ).2.2
  rw [ite_eq_left rfl, hz] at h1
  simp [ip] at h1

private theorem sum_irr_prod_eq_sum_irr_mul {G₁ G₂ : Type} [Group G₁] [Fintype G₁] [Group G₂] [Fintype G₂]
    (L : List (G₁ × G₂ → ℂ)) (hL : ∀ ρ ∈ L, IsIrr ρ) :
    ∃ L' : List ((G₁ → ℂ) × (G₂ → ℂ)), (∀ p ∈ L', IsIrr p.1 ∧ IsIrr p.2) ∧
      ∀ x y, L.sum (x, y) = (L'.map fun p => p.1 x * p.2 y).sum := by
  induction L with
  | nil => exact ⟨[], by simp, by simp⟩
  | cons ρ L ih =>
    obtain ⟨p, hp, rfl⟩ := exists_prod_of_isIrr (hL ρ (by simp))
    obtain ⟨L', hL', hsum⟩ := ih fun r hr => hL r (List.mem_cons_of_mem _ hr)
    refine ⟨p :: L', ?_, ?_⟩
    · intro q hq
      rcases List.mem_cons.1 hq with rfl | hq
      · exact hp
      · exact hL' q hq
    · intro x y
      rw [List.sum_cons, Pi.add_apply, hsum]
      simp

theorem exists_list_prod : ∀ (G₁ G₂ : Type) [Group G₁] [Fintype G₁] [Group G₂] [Fintype G₂] (Φ : G₁ × G₂ → ℂ),
    IsChar Φ → ∃ L : List ((G₁ → ℂ) × (G₂ → ℂ)), (∀ p ∈ L, IsIrr p.1 ∧ IsIrr p.2) ∧
      ∀ x y, Φ (x, y) = (L.map fun p => p.1 x * p.2 y).sum := by
  intro G₁ G₂ _ _ _ _ Φ hΦ
  obtain ⟨L, hL, rfl⟩ := (GlobalTheory.T.character_decomposition_and_classFunction_expansion (G₁ × G₂) Φ).1 hΦ
  exact sum_irr_prod_eq_sum_irr_mul L hL

end GlobalTheory.GLm.ProdChar
end

section

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL GlobalTheory.IdxInt MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.RefVol

theorem relIndex_inf_of_le {G : Type*} [AddGroup G] (P A K : AddSubgroup G) (h : K ≤ P) :
    (P ⊓ A).relIndex K = A.relIndex K := by
  rw [← AddSubgroup.inf_relIndex_right (P ⊓ A) K, ← AddSubgroup.inf_relIndex_right A K]
  congr 1
  ext x
  simp only [AddSubgroup.mem_inf]
  exact ⟨fun hx => ⟨hx.1.2, hx.2⟩, fun hx => ⟨⟨h hx.2, hx.1⟩, hx.2⟩⟩

theorem relIndex_prod {G H : Type*} [AddGroup G] [AddGroup H] (A A' : AddSubgroup G)
    (B B' : AddSubgroup H) :
    (A.prod B).relIndex (A'.prod B') = A.relIndex A' * B.relIndex B' := by
  unfold AddSubgroup.relIndex
  rw [← AddSubgroup.index_prod,
    ← AddSubgroup.index_comap_of_surjective _ (f := (AddSubgroup.prodEquiv A' B').toAddMonoidHom)
      (AddSubgroup.prodEquiv A' B').surjective]
  congr 1

theorem relIndex_inf_comap {G H : Type*} [AddGroup G] [AddGroup H] (φ : G →+ H) (P : AddSubgroup G)
    (A B : AddSubgroup H) :
    (P ⊓ A.comap φ).relIndex (P ⊓ B.comap φ) = (A ⊓ P.map φ).relIndex (B ⊓ P.map φ) := by
  rw [relIndex_inf_of_le _ _ _ inf_le_left, AddSubgroup.relIndex_comap, inf_comm A,
    relIndex_inf_of_le _ _ _ inf_le_right]
  congr 1
  ext y
  simp only [AddSubgroup.mem_map, AddSubgroup.mem_inf, AddSubgroup.mem_comap]
  constructor
  · rintro ⟨x, ⟨h1, h2⟩, rfl⟩
    exact ⟨h2, x, h1, rfl⟩
  · rintro ⟨h2, x, h1, rfl⟩
    exact ⟨x, ⟨h1, h2⟩, rfl⟩

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)

theorem th_ne : S.th ≠ 0 := by
  unfold Frames.th
  split_ifs
  · exact fun h => S.ϖ_irr.ne_zero (Subtype.ext h)
  · exact one_ne_zero

noncomputable def sumDiv : S.V × S.V →+ S.V :=
  (algebraMap F E S.th⁻¹ • (LinearMap.id : S.V →ₗ[E] S.V)).toAddMonoidHom.comp
    (AddMonoidHom.fst S.V S.V + AddMonoidHom.snd S.V S.V)

theorem sumDiv_apply (p : S.V × S.V) : sumDiv S p = algebraMap F E S.th⁻¹ • (p.1 + p.2) := rfl

theorem th_mul : algebraMap F E S.th * algebraMap F E S.th⁻¹ = 1 := by
  rw [← map_mul, mul_inv_cancel₀ (th_ne S), map_one]

theorem refB_eq (J : ℕ) (Λ : Submodule L.O S.V) :
    S.refB J Λ = ((S.spanTo S.f J).toAddSubgroup.prod (S.spanTo S.f' J).toAddSubgroup) ⊓
      Λ.toAddSubgroup.comap (sumDiv S) := by
  unfold Frames.refB
  congr 1
  ext p
  simp only [AddSubgroup.mem_comap, AddSubgroup.mem_map, sumDiv_apply]
  constructor
  · rintro ⟨y, hy, h⟩
    have h' : algebraMap F E S.th • y = p.1 + p.2 := h
    rw [← h', smul_smul, mul_comm (algebraMap F E S.th⁻¹), th_mul, one_smul]
    exact hy
  · intro h
    refine ⟨_, h, ?_⟩
    change algebraMap F E S.th • (algebraMap F E S.th⁻¹ • (p.1 + p.2)) = p.1 + p.2
    rw [smul_smul, th_mul, one_smul]

theorem map_sumDiv (X X' : Submodule E S.V) :
    (X.toAddSubgroup.prod X'.toAddSubgroup).map (sumDiv S) = (X ⊔ X').toAddSubgroup := by
  ext y
  simp only [AddSubgroup.mem_map, AddSubgroup.mem_prod, Submodule.mem_toAddSubgroup, sumDiv_apply]
  constructor
  · rintro ⟨p, ⟨h1, h2⟩, rfl⟩
    exact Submodule.smul_mem _ _ (Submodule.add_mem_sup h1 h2)
  · intro h
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 h
    refine ⟨(algebraMap F E S.th • a, algebraMap F E S.th • b),
      ⟨X.smul_mem _ ha, X'.smul_mem _ hb⟩, ?_⟩
    rw [← smul_add, smul_smul, mul_comm (algebraMap F E S.th⁻¹), th_mul, one_smul]

theorem refB_relIndex (J : ℕ) (Λ Λ' : Submodule L.O S.V) :
    (S.refB J Λ).relIndex (S.refB J Λ') =
      (Λ ⊓ (S.spanTo S.f J ⊔ S.spanTo S.f' J).restrictScalars L.O).toAddSubgroup.relIndex
        (Λ' ⊓ (S.spanTo S.f J ⊔ S.spanTo S.f' J).restrictScalars L.O).toAddSubgroup := by
  rw [refB_eq, refB_eq, relIndex_inf_comap, map_sumDiv]
  rfl

theorem refA_relIndex (J : ℕ) (Λ Λ' : Submodule L.O S.V) :
    (S.refA J Λ).relIndex (S.refA J Λ') =
      (Λ ⊓ (S.spanTo S.f J ⊔ S.spanTo S.f' J).restrictScalars L.O).toAddSubgroup.relIndex
        (Λ' ⊓ (S.spanTo S.f J ⊔ S.spanTo S.f' J).restrictScalars L.O).toAddSubgroup *
      (Λ ⊓ (perp L S.Hm (S.spanTo S.f J ⊔ S.spanTo S.f' J)).restrictScalars L.O).toAddSubgroup.relIndex
        (Λ' ⊓ (perp L S.Hm (S.spanTo S.f J ⊔ S.spanTo S.f' J)).restrictScalars L.O).toAddSubgroup := by
  unfold Frames.refA
  rw [relIndex_prod, relIndex_prod, AddSubgroup.relIndex_self, mul_one, refB_relIndex]
  rfl

end GlobalTheory.RefVol

theorem GlobalTheory.RefVol.main : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ (j : Fin r) (β βJ : ℕ) (d : S.Datum) (Λ : Submodule L.O S.V), S.IsTerm d Λ → S.InFF β (j + 1) βJ d Λ → ∀ Λ', S.IsTerm d Λ' → S.InFF β (j + 1) βJ d Λ' → (S.refA (j + 1) Λ).relIndex (S.refA (j + 1) Λ') = (S.refA (j + 1) Λ').relIndex (S.refA (j + 1) Λ) ∧ (S.refA (j + 1) Λ).relIndex (S.refA (j + 1) Λ') ≠ 0 := by
  intro F _ _ _ _ _ E _ _ _ L r k S j β βJ d Λ h1 h2 Λ' h3 h4
  have a := GlobalTheory.T.hermitianFamily_trace_volume_const L r k S j β βJ d Λ h1 h2 Λ' h3 h4 _ (Or.inl rfl)
  have b := GlobalTheory.T.hermitianFamily_trace_volume_const L r k S j β βJ d Λ h1 h2 Λ' h3 h4 _ (Or.inr rfl)
  rw [GlobalTheory.RefVol.refA_relIndex, GlobalTheory.RefVol.refA_relIndex]
  exact ⟨by rw [a.1, b.1], mul_ne_zero a.2.1 b.2.1⟩
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.OrbitTerm

theorem _root_.GlobalTheory.T.detNorm_eq_one_of_mem_autGL_var : ∀ (E : Type) [Field E] [NumberField E], IsTotallyComplex E → ∀ (j : ℕ) (Λ : Submodule (𝓞 E) (Fin j → E)), Submodule.IsFullLattice E Λ → ∀ γ ∈ autGL E j Λ, detNorm E j γ = 1 := by
  intro E _ _ hE j Λ hΛ γ hγ
  letI := hΛ
  exact GlobalTheory.OrbitTerm.detNorm_eq_one_of_mem_autGL E hE j Λ inferInstance γ hγ
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

theorem _root_.GlobalTheory.T.exists_riemannianHaar_unitaryJSubgroupOfAlgebra : ∀ (n : ℕ) (ε : Fin n → Bool) (A : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ)) (d : ℕ) (E : Fin d → Matrix (Fin n) (Fin n) ℂ), (∀ X ∈ A, ∀ Y ∈ A, X * Y ∈ A) → (∀ i k, ((E i * (E k)ᴴ).trace).re = if i = k then 1 else 0) → (∀ X, (X ∈ A ∧ Formalism.REAL.inG ε X) ↔ X ∈ Submodule.span ℝ (Set.range E)) → ∃ μ : Measure (Formalism.REAL.UJ ε), SigmaFinite μ ∧ IsGaugeSub {g | uMat g - 1 ∈ A} d μ := by
  first | exact @GlobalTheory.GaugeSubExists.exists_isGaugeSub | exact GlobalTheory.GaugeSubExists.exists_isGaugeSub | (intros; apply GlobalTheory.GaugeSubExists.exists_isGaugeSub <;> assumption)
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

theorem _root_.GlobalTheory.T.flagNilradical_finrank_and_abs_det_conj : ∀ (n : ℕ) (f g : Matrix (Fin n) (Fin n) ℂ) (r : ℕ) (F : ℕ → Submodule ℂ (Fin n → ℂ)) (N : Submodule ℂ (Matrix (Fin n) (Fin n) ℂ)), f * g = 1 → ‖f.det‖ = 1 → Monotone F → F 0 = ⊥ → F r = ⊤ → (∀ s, ∀ y ∈ F s, f *ᵥ y ∈ F s) → (∀ X, X ∈ N ↔ ∀ s, s < r → ∀ y ∈ F (s + 1), X *ᵥ y ∈ F s) → Module.finrank ℂ N = ∑ s ∈ Finset.range r, (Module.finrank ℂ (F (s + 1)) - Module.finrank ℂ (F s)) * Module.finrank ℂ (F s) ∧ ∀ φ : N →ₗ[ℂ] N, (∀ X : N, ((φ X : N) : Matrix (Fin n) (Fin n) ℂ) = f * (X : Matrix (Fin n) (Fin n) ℂ) * g) → ‖LinearMap.det φ‖ = ∏ s ∈ Finset.range r, detOn f (F s) ^ Module.finrank ℂ (F (s + 1)) / detOn f (F (s + 1)) ^ Module.finrank ℂ (F s) := by
  first | exact @GlobalTheory.FlagModulus.flag_finrank_det | exact GlobalTheory.FlagModulus.flag_finrank_det | (intros; apply GlobalTheory.FlagModulus.flag_finrank_det <;> assumption)
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

theorem _root_.GlobalTheory.T.leftQuotientCovolume_withDensity_detNormSq : ∀ (E : Type) [Field E] [NumberField E], IsTotallyComplex E → ∀ (j : ℕ), 1 ≤ j → ∀ Λ : Submodule (𝓞 E) (Fin j → E), Submodule.IsFullLattice E Λ → ∀ F : ℝ → ENNReal, Measurable F → covol (autGL E j Λ) ((haarGL E j).withDensity fun x => F (detNorm E j x)) {x | 0 < detNorm E j x} = covol (autGL E j Λ) (haarGL E j) {x | 1 ≤ detNorm E j x ∧ detNorm E j x < Real.exp 1} * ∫⁻ t in Set.Ioi (0 : ℝ), F t / ENNReal.ofReal t := by
  intro E _ _ hE j hj Λ hΛ F hF
  first
  | exact GlobalTheory.DetSlab.covol_withDensity_detNorm E hE j hj Λ hΛ F hF
  | exact GlobalTheory.DetSlab.covol_withDensity_detNorm E hE j hj Λ hΛ.toIsLattice F hF
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

theorem _root_.GlobalTheory.T.gaugeVolume_eq_of_semilinear_isometry_genus : ∀ (I I' : AutInst) (e : I'.E ≃+* I.E) (A : Matrix (Fin I.n) (Fin I'.n) I.E) (xf : I.Gf), (∀ y, e (star y) = star (e y)) → I'.n = I.n → Aᴴ * I.J * A = I'.J.map e → (∀ y : Fin I'.n → I'.E, y ∈ I'.L ↔ A *ᵥ (fun i => e (y i)) ∈ lamX I (1, xf)) → ∀ (c : InfinitePlace I.F → ℝ) (μf : Measure I.Gf) [SigmaFinite μf] [μf.IsHaarMeasure] (c' : InfinitePlace I'.F → ℝ) (μf' : Measure I'.Gf) [SigmaFinite μf'] [μf'.IsHaarMeasure], IsGaugeAll I c → IsGaugeAll I' c' → gaugeVol I c μf = gaugeVol I' c' μf' := by
  first | exact @GlobalTheory.GaugeTransport.gaugeVol_transport | exact GlobalTheory.GaugeTransport.gaugeVol_transport | (intros; apply GlobalTheory.GaugeTransport.gaugeVol_transport <;> assumption)
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

theorem _root_.GlobalTheory.T.gradedPieceSizes_unipotent_levi_compact_move : ∀ (I : AutInst) (xf : I.Gf) (a : ℕ) (j : Fin a → ℕ), (∀ i, 1 ≤ j i) → ∀ (S : Fin (a + 1) → Submodule (𝓞 I.E) (Fin I.n → I.E)), IsSatFlag I (lamX I (1, xf)) j S → ∀ u m k : I.Ginf, (∀ v, u v ∈ flagN (I.ε v) (flagAt I S v)) → (∀ v, m v ∈ flagM (I.ε v) (flagAt I S v)) → (∀ v, k v ∈ maxK (I.ε v)) → ∀ i : Fin a, Formalism.HN.sizeQ (bas I) (frm I (u * m * k, xf)) (S i.succ) (S i.castSucc) ^ I.f = Formalism.HN.sizeQ (bas I) (frm I (1, xf)) (S i.succ) (S i.castSucc) ^ I.f * ∏ v, locSize j (flagAt I S v) (uMat (m v)) i := by
  first | exact @GlobalTheory.FlagMeas.SizeMove.size_move | exact GlobalTheory.FlagMeas.SizeMove.size_move | (intros; apply GlobalTheory.FlagMeas.SizeMove.size_move <;> assumption)
end

section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

theorem _root_.GlobalTheory.T.radical_coordinates_bounded_majorant_lengths : ∀ (k r : ℕ) (z z' : (Fin (2 * r + k + 1) → ℂ)) (g₀ : Mat k r) (β : Fin r → ℕ) (De R₀ : ℝ), TwoFl k r z z' g₀ → IsNormal k r β g₀ → DeOK k r z z' g₀ De → 1 ≤ R₀ → ∀ m ∈ UH (Hb k), ∀ (y : UToff β → ℂ) (q : PPar k r) (a : Fin r → ℝ), (∀ b, 0 < a b) → Sg k r z' (uEmb k r (upperOff β y) * pOf k r q * uEmb k r (Matrix.diagonal fun b => (a b : ℂ)) * mEmb k r m) ≤ R₀ → Sg k r z (g₀ * (uEmb k r (upperOff β y) * pOf k r q * uEmb k r (Matrix.diagonal fun b => (a b : ℂ)) * mEmb k r m)) ≤ R₀ → (∀ b, eucl (m⁻¹ *ᵥ q.1 b) ≤ r * R₀ ^ (2 * r - 1) * De) ∧ (∀ p, ‖q.2.1 p‖ ≤ r * R₀ ^ (4 * r - 2) * De ^ 2) ∧ ∀ b, |q.2.2 b| ≤ r * R₀ ^ (4 * r - 2) * De ^ 2 := by
  first | exact @GlobalTheory.Amp.RadBound.radical_coords_le | exact GlobalTheory.Amp.RadBound.radical_coords_le | (intros; apply GlobalTheory.Amp.RadBound.radical_coords_le <;> assumption)
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase

theorem _root_.GlobalTheory.T.flags_conjugate_of_same_adapted_models : ∀ (I I₀ : AutInst) (e : I₀.E ≃+* I.E) (xf : I.Gf) (a : ℕ) (j : Fin a → ℕ) (S : Fin (a + 1) → Submodule (𝓞 I.E) (Fin I.n → I.E)) (Λ : ∀ i, Submodule (𝓞 I.E) (Fin (j i) → I.E)) (x₀ : I₀.Gf) (T T' : ∀ i, Matrix (Fin I.n) (Fin (j i)) I.E) (T₀ : Matrix (Fin I.n) (Fin I₀.n) I.E), (∀ i, 1 ≤ j i) → IsAdapted I I₀ e xf j S Λ x₀ T T' T₀ → ∀ (xf' : I.Gf) (S' : Fin (a + 1) → Submodule (𝓞 I.E) (Fin I.n → I.E)) (U U' : ∀ i, Matrix (Fin I.n) (Fin (j i)) I.E) (U₀ : Matrix (Fin I.n) (Fin I₀.n) I.E), IsAdapted I I₀ e xf' j S' Λ x₀ U U' U₀ → ∃ γ ∈ I.GFset, ∃ k ∈ I.Kset, γ.2 * xf = xf' * k ∧ ∀ g : I.Ginf, sizesAt I xf' S' (γ.1 * g) = sizesAt I xf S g := by
  first | exact @GlobalTheory.FlagConj.conjugate_of_isAdapted | exact GlobalTheory.FlagConj.conjugate_of_isAdapted | (intros; apply GlobalTheory.FlagConj.conjugate_of_isAdapted <;> assumption)
end
