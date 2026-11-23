module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemTwKerIffAverage
public import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.UnitarySchrodingerLemmas.UnramifiedSchwartzDensity.SchCut
public import Development.WeilBound.CoreStatements.FiniteTypeHarishChandra.SupportExistsAll
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle081
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle120
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle111
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle112
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle110
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle109
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.CechAugRow
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.Bundle001
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle114
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CechVanishingFromCover
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AlmostFiniteModuleBoundedTorsion
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.TwistedRepresentations.Tens
public import Mathlib.RingTheory.Artinian.Defs
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle113
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
import Mathlib.RingTheory.Henselian
import Mathlib.RepresentationTheory.Maschke
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle107
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.TwistedKernels.TwKerLeComapOf
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsDPMorphismBot
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens

@[expose] public section

section

open Matrix GlobalTheory.PRep GlobalTheory.BZMir GlobalTheory.SplitWeil GlobalTheory.CompanionTheory.MirFourier ValuativeRel
open scoped Topology

noncomputable section

namespace GlobalTheory.CompanionTheory.FiniteFourier

open GlobalTheory.CompanionTheory.TwistedAverage

theorem sum_twOrbit_eq_zero {G V : Type} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (hρ : IsSmooth ρ) (L : Subgroup G)
    (hL : IsCompact (L : Set G)) (L₁ : Subgroup L) (hL₁ : IsOpen (L₁ : Set L)) (v : V)
    (hv : ∀ x ∈ L₁, ρ (x : G) v = v) (θ : L →* ℂˣ) (hθ : ∀ x ∈ L₁, θ x = 1)
    (hk : v ∈ twKer ρ L θ) [L₁.Normal] [Fintype (L ⧸ L₁)] :
    ∑ q : L ⧸ L₁, twOrbit ρ L θ v q.out = 0 := by
  classical
  have : CompactSpace L := isCompact_iff_compactSpace.mp hL
  have hle : L₁ ≤ θ.ker := fun x hx => hθ x hx
  have hopen : IsOpen (θ.ker : Set L) := Subgroup.isOpen_mono hle hL₁
  obtain ⟨M, hM, hsum⟩ := exists_sum_eq_zero hρ hL θ hopen hk
  have : L₁.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  set C : Subgroup L := (M ⊓ L₁).normalCore with hC
  have : C.Normal := Subgroup.normalCore_normal _
  have : C.FiniteIndex := inferInstance
  have : Fintype (L ⧸ C) := Fintype.ofFinite _
  have hCM : C ≤ M ⊓ L₁ := Subgroup.normalCore_le _
  have : Finite (L₁ ⧸ C.subgroupOf L₁) := inferInstance
  have : Fintype (L₁ ⧸ C.subgroupOf L₁) := Fintype.ofFinite _
  have h0 := hsum C (hCM.trans inf_le_left)
  rw [sum_out_refine (hCM.trans inf_le_right) (twOrbit ρ L θ v)
    (fun x k hk => twOrbit_mul_right ρ L θ v x k ⟨hv k hk, hθ k hk⟩)] at h0
  rw [← Nat.cast_smul_eq_nsmul ℂ, smul_eq_zero] at h0
  rcases h0 with h0 | h0
  · exact absurd h0 (Nat.cast_ne_zero.2 Fintype.card_ne_zero)
  · exact h0

theorem eq_zero_of_twKer :
    ∀ {G V : Type} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V), IsSmooth ρ → ∀ (L : Subgroup G), IsCompact (L : Set G) → ∀ (L₁ : Subgroup L), IsOpen (L₁ : Set L) → ∀ (v : V), (∀ x ∈ L₁, ρ (x : G) v = v) → ∀ {ι : Type} (R : Finset ι), R.Nonempty → ∀ (χ : ι → (L →* ℂˣ)), (∀ a ∈ R, ∀ x ∈ L₁, χ a x = 1) → (∀ a ∈ R, v ∈ twKer ρ L (χ a)) → (∀ x : L, x ∉ L₁ → ∑ a ∈ R, (((χ a x)⁻¹ : ℂˣ) : ℂ) = 0) → v = 0 := by
  intro G V _ _ _ _ _ ρ hρ L hL L₁ hL₁ v hv ι R hR χ hχ hker hsum
  classical
  have : CompactSpace L := isCompact_iff_compactSpace.mp hL
  have : Finite (L ⧸ L₁) := Subgroup.quotient_finite_of_isOpen _ hL₁
  have : L₁.Normal := inferInstance
  have : Fintype (L ⧸ L₁) := Fintype.ofFinite _
  have key : ∀ a ∈ R, ∑ q : L ⧸ L₁, twOrbit ρ L (χ a) v q.out = 0 := fun a ha =>
    sum_twOrbit_eq_zero ρ hρ L hL L₁ hL₁ v hv (χ a) (hχ a ha) (hker a ha)
  have h0 : ∑ q : L ⧸ L₁, ∑ a ∈ R, twOrbit ρ L (χ a) v q.out = 0 := by
    rw [Finset.sum_comm]
    exact Finset.sum_eq_zero key
  have hoff : ∀ q : L ⧸ L₁, q ≠ 1 → ∑ a ∈ R, twOrbit ρ L (χ a) v q.out = 0 := by
    intro q hq
    have hnot : q.out ∉ L₁ := by
      intro hmem
      apply hq
      rw [← QuotientGroup.out_eq' q]
      exact (QuotientGroup.eq_one_iff _).2 hmem
    simp only [twOrbit]
    rw [← Finset.sum_smul, hsum _ hnot, zero_smul]
  have hone : ((1 : L ⧸ L₁).out : L) ∈ L₁ := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.out_eq']
  have hmain : ∑ a ∈ R, twOrbit ρ L (χ a) v (1 : L ⧸ L₁).out = R.card • v := by
    rw [Finset.card_eq_sum_ones, Finset.sum_smul]
    refine Finset.sum_congr rfl fun a ha => ?_
    simp only [twOrbit]
    rw [hχ a ha _ hone, hv _ hone]
    simp
  rw [Finset.sum_eq_single (1 : L ⧸ L₁) (fun q _ hq => hoff q hq)
    (fun h => absurd (Finset.mem_univ _) h), hmain] at h0
  rw [← Nat.cast_smul_eq_nsmul ℂ, smul_eq_zero] at h0
  rcases h0 with h0 | h0
  · exact absurd h0 (Nat.cast_ne_zero.2 hR.card_pos.ne')
  · exact h0

end GlobalTheory.CompanionTheory.FiniteFourier
end
end

section

noncomputable section
open HeckeCharacterZeroLocus.SiegelWeilU NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

theorem _root_.GlobalTheory.T.archimedean_family_continuity : PositivityTheory.PfSWUS.SchInf.FamCont := by
  first | exact @GlobalTheory.CompanionTheory.PushFam.integrable_continuousAt_of_linear_push | exact GlobalTheory.CompanionTheory.PushFam.integrable_continuousAt_of_linear_push | (intros; apply GlobalTheory.CompanionTheory.PushFam.integrable_continuousAt_of_linear_push <;> assumption)
end
end

section

open ReciprocityTheory.Ty.Fin GlobalTheory.CompanionTheory.TyFin.ColStep

noncomputable section

namespace GlobalTheory.CompanionTheory.TyFin.ColStep

theorem colGeR_single (K : Type) [Field K] (d j : ℕ) (hj : 1 ≤ j) :
    colGeR K d j (Pi.single (⟨j - 1, by omega⟩ : Fin j) (1 : K) : Fin j → K) = colGeE K d j := by
  funext i l
  by_cases hl : (l : ℕ) = j
  · by_cases hi : (l : ℕ) = i + 1
    · have hlt : (i : ℕ) < j := by omega
      have hij : (⟨(i : ℕ), hlt⟩ : Fin j) = ⟨j - 1, by omega⟩ := Fin.ext (by simp; omega)
      simp only [colGeR, colGeE]
      rw [dite_eq_left ⟨hl, hlt⟩, hij]
      simp [hl, hi]
      omega
    · simp only [colGeR, colGeE]
      by_cases hlt : (i : ℕ) < j
      · rw [dite_eq_left ⟨hl, hlt⟩]
        have hne : (⟨(i : ℕ), hlt⟩ : Fin j) ≠ ⟨j - 1, by omega⟩ := by
          intro h; have := congrArg Fin.val h; simp at this; omega
        simp [hi, Pi.single_eq_of_ne hne]
      · rw [dite_eq_right (by tauto)]
        simp [hi]
  · simp only [colGeR, colGeE]
    rw [dite_eq_right (by tauto)]
    have : (j + 1 ≤ (l : ℕ)) ↔ j ≤ (l : ℕ) := by omega
    simp [this]

theorem wh_row_ne_zero (K : Type) [Field K] [Fintype K] [DecidableEq K] (d j : ℕ) (ψ₀ : AddChar K ℂ)
    (χ : GL (Fin d) K → ℂ) (hj : 1 ≤ j) (hd : j < d) (hχ : ∀ x y, χ (x * y * x⁻¹) = χ y)
    (r : Fin j → K) (hr : r ≠ 0) :
    wh (colGe d j) (colGeR K d j r) ψ₀ χ = wh (colGe d j) (colGeE K d j) ψ₀ χ := by
  have hs : (Pi.single (⟨j - 1, by omega⟩ : Fin j) (1 : K) : Fin j → K) ≠ 0 := by
    intro h
    have := congrFun h ⟨j - 1, by omega⟩
    simp at this
  obtain ⟨g, hg⟩ := GlobalTheory.T.GL_transitive_nonzero_vectors K j r _ hr hs
  obtain ⟨h, h1, h2⟩ := GlobalTheory.T.block_embedding_GL_inverse K d j hd.le g
  rw [GlobalTheory.T.whittaker_block_embedding_conj K d j ψ₀ χ g h r hd hχ h1 h2, hg, colGeR_single K d j hj]

theorem wh_step (K : Type) [Field K] [Fintype K] [DecidableEq K] (d j : ℕ) (ψ₀ : AddChar K ℂ)
    (τ : FDRep ℂ (GL (Fin d) K)) (hψ : ψ₀ ≠ 1) (hτ : IsCuspidal K τ) (hj : 1 ≤ j) (hd : j < d) :
    wh (colGe d (j + 1)) (colGeE K d (j + 1)) ψ₀ τ.character =
      ((Fintype.card K : ℂ) ^ j - 1) * wh (colGe d j) (colGeE K d j) ψ₀ τ.character := by
  rw [GlobalTheory.T.whittaker_column_recursion K d j ψ₀ τ.character hd (GlobalTheory.T.pattern_set_card_column_step K d j hd) (GlobalTheory.T.additive_character_sum_orthogonality K j ψ₀ hψ)]
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : Fin j → K)),
    GlobalTheory.T.whittaker_vanishes_of_radical_sums K d j ψ₀ τ.character (GlobalTheory.T.cuspidal_unipotent_radical_sum_zero K d j τ hj hd hτ), zero_add,
    Finset.sum_congr rfl (fun r hr => wh_row_ne_zero K d j ψ₀ τ.character hj hd
      (fun x y => FDRep.char_conj τ y x) r (Finset.ne_of_mem_erase hr))]
  rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
    Fintype.card_fun, Fintype.card_fin, nsmul_eq_mul]
  have h1 : 1 ≤ Fintype.card K ^ j := Nat.one_le_pow _ _ Fintype.card_pos
  rw [Nat.cast_sub h1]
  simp

theorem wh_top (K : Type) [Field K] [Fintype K] [DecidableEq K] (d : ℕ) (ψ₀ : AddChar K ℂ)
    (τ : FDRep ℂ (GL (Fin d) K)) :
    wh (colGe d d) (colGeE K d d) ψ₀ τ.character = (Module.finrank ℂ τ : ℂ) := by
  classical
  have hset : patSet K (colGe d d) = {1} := by
    ext u
    simp only [patSet, Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · intro h
      ext i l
      by_cases hil : i = l
      · subst hil; simpa using (h i i).1 rfl
      · have := (h i l).2 hil (fun hc => by have := hc.2; have := l.2; omega)
        simp [this, Matrix.one_apply_ne hil]
    · rintro rfl i l
      exact ⟨fun h => by simp [h], fun h _ => by simp [Matrix.one_apply_ne h]⟩
  have hE : patChar (colGeE K d d) ψ₀ (1 : GL (Fin d) K) = 1 := by
    have : ∀ i l : Fin d, colGeE K d d i l = 0 := by
      intro i l
      simp only [colGeE]
      rw [if_neg]
      rintro ⟨-, h⟩
      have := l.2
      omega
    simp [patChar, this]
  simp only [wh, hset, Set.ncard_singleton, Set.mem_singleton_iff]
  simp [hE, FDRep.char_one]

theorem wh_one_eq (K : Type) [Field K] [Fintype K] [DecidableEq K] (d : ℕ) (ψ₀ : AddChar K ℂ) (χ : GL (Fin d) K → ℂ) :
    wh (colGe d 1) (colGeE K d 1) ψ₀ χ = wh (fun i j : Fin d => i < j) (cutE K d 0) ψ₀ χ := by
  have h1 : colGe d 1 = fun i j : Fin d => i < j := by
    funext i l
    simp only [colGe, eq_iff_iff, and_iff_left_iff_imp]
    intro h
    have : (i : ℕ) < l := h
    omega
  have h2 : colGeE K d 1 = cutE K d 0 := by
    funext i l
    simp only [colGeE, cutE]
    congr 1
    apply propext
    omega
  rw [h1, h2]

theorem wh_prod (K : Type) [Field K] [Fintype K] [DecidableEq K] (d : ℕ) (ψ₀ : AddChar K ℂ)
    (τ : FDRep ℂ (GL (Fin d) K)) (hψ : ψ₀ ≠ 1) (hτ : IsCuspidal K τ) (k : ℕ) (hk : 1 ≤ k) (hkd : k ≤ d) :
    wh (colGe d k) (colGeE K d k) ψ₀ τ.character =
      wh (colGe d 1) (colGeE K d 1) ψ₀ τ.character * ∏ i ∈ Finset.Ico 1 k, ((Fintype.card K : ℂ) ^ i - 1) := by
  induction k, hk using Nat.le_induction with
  | base => simp
  | succ k hk ih =>
    rw [wh_step K d k ψ₀ τ hψ hτ hk (by omega), ih (by omega), Finset.prod_Ico_succ_top hk]
    ring

theorem cuspWh : ReciprocityTheory.Ty.Fin.St.CuspWh := by
  intro K _ _ _ d ψ₀ τ hψ hτ
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · rw [← wh_top K 0 ψ₀ τ]
    have h1 : colGe 0 0 = fun i j : Fin 0 => i < j := by
      funext i; exact i.elim0
    have h2 : colGeE K 0 0 = cutE K 0 0 := by
      funext i; exact i.elim0
    rw [h1, h2]
    simp
  · rw [← wh_top K d ψ₀ τ, wh_prod K d ψ₀ τ hψ hτ d hd le_rfl, wh_one_eq]

end GlobalTheory.CompanionTheory.TyFin.ColStep
end
end

section

open CategoryTheory ReciprocityTheory.Ty.Fin

noncomputable section

namespace GlobalTheory.CompanionTheory.FinRep

variable {Γ : Type} [Group Γ] [Fintype Γ]

def leftRep (N : Submodule (MonoidAlgebra ℂ Γ) (MonoidAlgebra ℂ Γ)) : Representation ℂ Γ N where
  toFun g :=
    { toFun := fun n => MonoidAlgebra.of ℂ Γ g • n
      map_add' := smul_add _
      map_smul' := fun c n => smul_comm _ c n }
  map_one' := by
    ext n
    simp
  map_mul' g h := by
    apply LinearMap.ext
    intro n
    change MonoidAlgebra.of ℂ Γ (g * h) • n = MonoidAlgebra.of ℂ Γ g • MonoidAlgebra.of ℂ Γ h • n
    rw [map_mul, mul_smul]

theorem leftRep_apply (N : Submodule (MonoidAlgebra ℂ Γ) (MonoidAlgebra ℂ Γ)) (g : Γ) (n : N) :
    leftRep N g n = MonoidAlgebra.of ℂ Γ g • n := rfl

theorem asAlgebraHom_leftRep (N : Submodule (MonoidAlgebra ℂ Γ) (MonoidAlgebra ℂ Γ))
    (x : MonoidAlgebra ℂ Γ) (n : N) : Representation.asAlgebraHom (leftRep N) x n = x • n := by
  induction x using MonoidAlgebra.induction_on with
  | of g => simp [Representation.asAlgebraHom_of, leftRep_apply]
  | add a b ha hb => simp [map_add (f := _), add_smul, ha, hb]
  | smul c a ha => simp [map_smul, ha]

instance finiteDimensional_leftIdeal (N : Submodule (MonoidAlgebra ℂ Γ) (MonoidAlgebra ℂ Γ)) :
    FiniteDimensional ℂ N :=
  inferInstanceAs (FiniteDimensional ℂ (N.restrictScalars ℂ))

theorem isIrr_leftRep (N : Submodule (MonoidAlgebra ℂ Γ) (MonoidAlgebra ℂ Γ))
    [IsSimpleModule (MonoidAlgebra ℂ Γ) N] : IsIrr (leftRep N) := by
  refine ⟨IsSimpleModule.nontrivial (MonoidAlgebra ℂ Γ) N, fun W hW => ?_⟩
  have hmem : ∀ (x : MonoidAlgebra ℂ Γ), ∀ w ∈ W, x • w ∈ W := by
    intro x w hw
    rw [← asAlgebraHom_leftRep]
    induction x using MonoidAlgebra.induction_on with
    | of g => simpa [Representation.asAlgebraHom_of] using hW g w hw
    | add a b ha hb => simpa [map_add (f := _)] using W.add_mem ha hb
    | smul c a ha => simpa [map_smul] using W.smul_mem c ha
  let W' : Submodule (MonoidAlgebra ℂ Γ) N :=
    { carrier := W
      add_mem' := W.add_mem
      zero_mem' := W.zero_mem
      smul_mem' := fun x w hw => hmem x w hw }
  rcases IsSimpleOrder.eq_bot_or_eq_top W' with h | h
  · left
    ext w
    have := congrArg (fun S : Submodule (MonoidAlgebra ℂ Γ) N => w ∈ S) h
    simpa [W'] using this
  · right
    ext w
    have := congrArg (fun S : Submodule (MonoidAlgebra ℂ Γ) N => w ∈ S) h
    simpa [W'] using this

theorem sepIrr : ReciprocityTheory.Ty.Fin.St.SepIrr := by
  intro Γ _ _ x hx
  have hsimple : ∀ N : Submodule (MonoidAlgebra ℂ Γ) (MonoidAlgebra ℂ Γ),
      IsSimpleModule (MonoidAlgebra ℂ Γ) N → ∀ n ∈ N, x * n = 0 := by
    intro N hN n hn
    have hS : Simple (FDRep.of (leftRep N)) :=
      (GlobalTheory.T.simple_iff_irreducible.1 Γ (FDRep.of (leftRep N))).2 (by
        simpa using isIrr_leftRep N)
    have h0 := hx _ hS
    have h1 : Representation.asAlgebraHom (leftRep N) x = 0 := by
      simpa using h0
    have h2 := asAlgebraHom_leftRep N x ⟨n, hn⟩
    rw [h1] at h2
    have h3 := congrArg Subtype.val h2
    simpa using h3.symm
  let J : Submodule (MonoidAlgebra ℂ Γ) (MonoidAlgebra ℂ Γ) :=
    { carrier := {n | ∀ a, x * (a * n) = 0}
      add_mem' := fun {u v} hu hv a => by
        rw [mul_add, mul_add, hu a, hv a, add_zero]
      zero_mem' := fun a => by simp
      smul_mem' := fun c n hn a => by
        simpa [mul_assoc] using hn (a * c) }
  have hJ : (⊤ : Submodule (MonoidAlgebra ℂ Γ) (MonoidAlgebra ℂ Γ)) ≤ J := by
    rw [← IsSemisimpleModule.sSup_simples_eq_top (R := MonoidAlgebra ℂ Γ)]
    refine sSup_le fun N hN n hn a => ?_
    exact hsimple N hN _ (by simpa using N.smul_mem a hn)
  have h1 : (1 : MonoidAlgebra ℂ Γ) ∈ J := hJ Submodule.mem_top
  simpa using h1 1

end GlobalTheory.CompanionTheory.FinRep
end
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory Opposite CrystallineSemistableComparison CrystallineSemistableComparison.CH
universe w w' w'' t t' v u v' u' v'' u''

theorem _root_.GlobalTheory.T.elements_bijective_of_bijective_app : ∀ {R : Type} [CommRing R] {C : Type u} [Category.{v} C] {E' E : C ⥤ Type t} (p : E' ⟶ E) (F : C ⥤ ModuleCat.{w} R), (∀ T, Function.Bijective (p.app T)) → ∀ n, Function.Bijective ((elMor p F).hom.f n) := by
  first | exact @GlobalTheory.CompanionTheory.Cech.elMor_bijective_of_bijective | exact GlobalTheory.CompanionTheory.Cech.elMor_bijective_of_bijective | (intros; apply GlobalTheory.CompanionTheory.Cech.elMor_bijective_of_bijective <;> assumption)
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

theorem _root_.GlobalTheory.T.cover_cup_action_basis : ∀ {O : Type} [CommRing O] {X : Scheme.{0}} (str : ∀ V : X.Opens, O →+* Γ(X, V)) {C : Type 1} [Category.{0} C] (F : C ⥤ ModuleCat.{0} O) {ι : Type}
    (U : ι → X.Opens) (U' : ι → ObjectProperty C) (m : ℕ) (κ : ι → Type) [∀ α, Fintype (κ α)]
    (act : ∀ {n : ℕ} (i : Fin (n + 1) → ι), Γ(X, capO U i) →+* AddMonoid.End (HU F (capT U' i) m))
    (b : ∀ {n : ℕ} (i : Fin (n + 1) → ι) (a : Fin (n + 1)), κ (i a) → HU F (capT U' i) m)
    (g : ∀ α β, κ α → κ β → Γ(X, U α ⊓ U β))
    (hfree : ∀ (n : ℕ) (i : Fin (n + 1) → ι) (a : Fin (n + 1)) (h : HU F (capT U' i) m),
      ∃! f : κ (i a) → Γ(X, capO U i), h = ∑ k, act i (f k) (b i a k))
    (hstr : ∀ (n : ℕ) (i : Fin (n + 1) → ι) (c : O) (h : HU F (capT U' i) m), act i (str _ c) h = c • h)
    (hres : ∀ (n : ℕ) (i : Fin (n + 2) → ι) (j : Fin (n + 2)) (f : Γ(X, capO U (i ∘ j.succAbove))) (h : HU F (capT U' (i ∘ j.succAbove)) m),
      (resU F (U := capT U' (i ∘ j.succAbove)) (V := capT U' i) (fun _ h _ => h _)).pull m (act (i ∘ j.succAbove) f h) =
        act i (rs (capO_comp U i j.succAbove) f) ((resU F (U := capT U' (i ∘ j.succAbove)) (V := capT U' i) (fun _ h _ => h _)).pull m h))
    (hb : ∀ (n : ℕ) (i : Fin (n + 2) → ι) (j : Fin (n + 2)) (a : Fin (n + 1)) (k : κ (i (j.succAbove a))),
      (resU F (U := capT U' (i ∘ j.succAbove)) (V := capT U' i) (fun _ h _ => h _)).pull m (b (i ∘ j.succAbove) a k) = b i (j.succAbove a) k)
    (hg : ∀ (n : ℕ) (i : Fin (n + 1) → ι) (a a' : Fin (n + 1)) (k' : κ (i a')),
      b i a' k' = ∑ k, act i (rs (le_inf (capO_le U i a) (capO_le U i a')) (g (i a) (i a') k k')) (b i a k)),
    Nonempty (VB str U (CrystallineSemistableComparison.Pb.cechH F U' m)) := by
  first | exact @GlobalTheory.CompanionTheory.CechVB.vb_basis | exact GlobalTheory.CompanionTheory.CechVB.vb_basis | (intros; apply GlobalTheory.CompanionTheory.CechVB.vb_basis <;> assumption)
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris ReciprocityTheory.ChartRestriction.G.Geo.Tor CrystallineSemistableComparison CrystallineSemistableComparison.Pb

theorem _root_.GlobalTheory.T.restrict_appLE_compat : ∀ {X Y : Scheme.{0}} (f : X ⟶ Y) (U : Y.Opens) {V W : X.Opens} (h : V ≤ W) (hW : W ≤ f ⁻¹ᵁ U)
    (s : Γ(Y, U)), rs h ((f.appLE U W hW).hom s) = (f.appLE U V (h.trans hW)).hom s := by
  first | exact @GlobalTheory.CompanionTheory.ConeRs.rs_appLE_apply | exact GlobalTheory.CompanionTheory.ConeRs.rs_appLE_apply | (intros; apply GlobalTheory.CompanionTheory.ConeRs.rs_appLE_apply <;> assumption)
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

theorem _root_.GlobalTheory.T.finite_modules_serre_class : ∀ (R : Type) [CommRing R] [IsNoetherianRing R], ∃ 𝒮 : Serre.{1} R,
    ∀ (M : Type 1) [AddCommGroup M] [Module R M], 𝒮.P M ↔ Module.Finite R M := by
  first | exact @GlobalTheory.CompanionTheory.SerreFin.exists_serre_finite | exact GlobalTheory.CompanionTheory.SerreFin.exists_serre_finite | (intros; apply GlobalTheory.CompanionTheory.SerreFin.exists_serre_finite <;> assumption)
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory CrystallineSemistableComparison CrystallineSemistableComparison.Pb
universe u v w

theorem _root_.GlobalTheory.T.cech_cohomology_full_subcategory_iso : ∀ {R : Type} [CommRing R] {C : Type u} [Category.{v} C] (F : C ⥤ ModuleCat.{w} R) (Q : ObjectProperty C) {ι : Type} (W : ι → ObjectProperty C), (∀ α, W α ≤ Q) → ∀ q p, Nonempty ((cechH (Q.ι ⋙ F) (fun α (T : Q.FullSubcategory) => W α T.obj) q).cx.H p ≃ₗ[R] (cechH F W q).cx.H p) := by
  first | exact @GlobalTheory.CompanionTheory.CechFull.cechH_fullSubcategory_H | exact GlobalTheory.CompanionTheory.CechFull.cechH_fullSubcategory_H | (intros; apply GlobalTheory.CompanionTheory.CechFull.cechH_fullSubcategory_H <;> assumption)
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

theorem _root_.GlobalTheory.T.cech_vanishing_from_cover : ∀ {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] (F : C ⥤ ModuleCat.{0} R) {ι : Type} [Fintype ι]
    (U : ι → ObjectProperty C) (hU : ∀ α, Cosieve (U α)) (hc : ∀ T, ∃ α, U α T) (s : ℕ),
    ((∀ S : Finset ι, S.Nonempty → ∀ j < s, Subsingleton (HU F (capS U S) j)) → ∀ j < s, Subsingleton (CH.H F j)) ∧
    ((∀ S : Finset ι, S.Nonempty → ∀ j, Subsingleton (HU F (capS U S) j)) → ∀ j, Subsingleton (CH.H F j)) ∧
    ((∀ S : Finset ι, S.Nonempty → ∀ j > s, Subsingleton (HU F (capS U S) j)) →
      ∀ j, s + Fintype.card ι ≤ j → Subsingleton (CH.H F j)) := by
  first | exact @GlobalTheory.CompanionTheory.CosieveMV.vanishing_of_cover | exact GlobalTheory.CompanionTheory.CosieveMV.vanishing_of_cover | (intros; apply GlobalTheory.CompanionTheory.CosieveMV.vanishing_of_cover <;> assumption)
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

theorem _root_.GlobalTheory.T.almost_finite_module_bounded_torsion : ∀ (R : Type) [CommRing R] (I : Ideal R) (c : R), I.FG → IsNilpotent I → I.IsPrime →
    (∀ x y : R, x ∈ Ideal.span {y} ⊔ I ∨ y ∈ Ideal.span {x} ⊔ I) → (∀ x : R, x ∉ I → ∃ n : ℕ, c ^ n ∈ Ideal.span {x} ⊔ I) →
    IsPrecomplete (Ideal.span {c}) R → (∀ x : R, (∀ n : ℕ, x ∈ Ideal.span {c ^ n} ⊔ I) → x ∈ I) →
    ∀ (M : Type 1) [AddCommGroup M] [Module R M], AFG c M → ∃ k : ℕ,
      (∀ (x : M) (n : ℕ), c ^ n • x = 0 → c ^ k • x = 0) ∧ (∀ x : M, (∀ n : ℕ, ∃ y, x = c ^ n • y) → c ^ k • x = 0) ∧
      ∀ x : ℕ → M, (∀ n, ∃ y, x (n + 1) - x n = c ^ n • y) → ∃ z : M, ∀ n, ∃ y, z - c ^ k • x n = c ^ n • y := by
  first | exact @GlobalTheory.CompanionTheory.AlmostFinite.afg_separated_complete | exact GlobalTheory.CompanionTheory.AlmostFinite.afg_separated_complete | (intros; apply GlobalTheory.CompanionTheory.AlmostFinite.afg_separated_complete <;> assumption)
end

section

open TensorProduct CrystallineSemistableComparison CrystallineSemistableComparison.Tw

theorem _root_.GlobalTheory.T.limit_divisible_of_vanishing_level : ∀ (W : Type) [CommRing W] (l : ℕ) (S S' : Sys.{1} W) (_ : LSeq l S S'), (∀ n, IsArtinian W (S.M n)) → ∀ n (x : S.lim), x.1 n = 0 → ∃ y : S.lim, x = ((l : W) ^ n) • y := by
  first | exact @GlobalTheory.CompanionTheory.Tower.lim_eq_pow_smul | exact GlobalTheory.CompanionTheory.Tower.lim_eq_pow_smul | (intros; apply GlobalTheory.CompanionTheory.Tower.lim_eq_pow_smul <;> assumption)
end
