module

public import Formalism.SharpRestriction.LevelLetterCocycles.DeltaInvariantLattices
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ValOfPowAssociated
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle451
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamComparisonIsFiltered
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle428
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle411
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle150
public import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle005
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.BlockCharactersCrystalline
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.JumpDictCrysAtOfWeights
public import Formalism.SharpRestriction.LevelLetterCocycles.TableLineDegreeTwo
public import Formalism.SharpRestriction.LevelLetterCocycles.AdmissibleParameterJ
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.BaseSizes
public import Formalism.SharpRestriction.ParConsts
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle459
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle336
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle397
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle449
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle105
public import Formalism.PadicSubsetSums.StableGradedCounts.Bundle003
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Algebra.Order.Star.Rat
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
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle008
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle009
public import Formalism.PadicSubsetSums.CentralIdempotents.Bundle001

@[expose] public section

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices

theorem GlobalTheory.NL.p9_statement : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW), P9 D HW F := by
  intro D HW F l _ K s LL h T hT hs hl
  have hp : ((D.loc l).PD K).p = l := (D.loc l).PD_p K
  rw [hp] at hl ⊢
  obtain ⟨hc, ⟨π', E', hr⟩, h1⟩ := GlobalTheory.DelParam.torsion_parameters D HW l K s LL h hs hl
  have md := GlobalTheory.T.wachLattice_deltaInvariant_basis D HW F l K s LL h T hT hs hl
  have hpos : 0 < ((HW l).W K s LL h).DelF.card :=
    Finset.card_pos.2 ⟨1, (((HW l).W K s LL h).DelF_def 1).2 ⟨1, one_pos, one_pow _⟩⟩
  have hl1 : 0 < l - 1 := Nat.sub_pos_of_lt (Fact.out : l.Prime).one_lt
  refine ⟨hc, ⟨π', E', hr, md _ _ _ _ (hc ▸ hpos) hr⟩, fun he => ⟨h1 he, md _ _ _ _ hl1 (h1 he)⟩⟩
end

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.exists_invertible_deRhamPeriodMatrix_of_isDR : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (n : Type) [Fintype n] [DecidableEq n] (K : FinExt l) (V : Type) [AddCommGroup V] [Module ℚ_[l] V] (b : Module.Basis n ℚ_[l] V) (ρ : Representation ℚ_[l] ↥(GK K) V), Formalism.MainNotions.N.IsDR (P.PD K) ρ → ∃ Q : GL n P.R.BdR, ∀ g : ↥(GK K), (LinearMap.toMatrix b b (ρ g)).map (algebraMap ℚ_[l] P.R.BdR) * (Q : Matrix n n P.R.BdR).map (P.actQdR (g : GQ l)) = Q := by
  first | exact @GlobalTheory.DRMat.exists_period_matrix_of_isDR | exact GlobalTheory.DRMat.exists_period_matrix_of_isDR | (intros; apply GlobalTheory.DRMat.exists_period_matrix_of_isDR <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
open scoped Formalism.Per

namespace GlobalTheory.TateFilQuot

open GlobalTheory.DRFil

section Abstract

variable {G B M : Type} [CommRing B] [AddCommGroup M] [Module B M]
  (σ : G → B →+* B) (ρ : G → M →+ M) (F : ℤ → AddSubgroup B) (FM : ℤ → AddSubgroup M)

theorem step_invariant
    (hρ : ∀ g (b : B) (m : M), ρ g (b • m) = σ g b • ρ g m)
    (hmul : ∀ a b x y, x ∈ F a → y ∈ F b → x * y ∈ F (a + b))
    (hsmul : ∀ a b x y, x ∈ F a → y ∈ FM b → x • y ∈ FM (a + b))
    (hFG : ∀ g a x, x ∈ F a → σ g x ∈ F a)
    (hMG : ∀ g a x, x ∈ FM a → ρ g x ∈ FM a)
    (hinv : ∀ a b, b ∈ F a → b ∉ F (a + 1) → ∃ β ∈ F (-a), β * b - 1 ∈ F 1)
    (hT : ∀ n e, e ∈ F n → (∀ g, σ g e - e ∈ F (n + 1)) →
      ∃ κ ∈ F 0, (∀ g, σ g κ = κ) ∧ (n ≠ 0 → κ = 0) ∧ e - κ ∈ F (n + 1))
    {ι : Type} [DecidableEq ι] (k : ι → ℤ) (d : ι → M) (hd : ∀ i g, ρ g (d i) = d i)
    (hdk : ∀ i, d i ∈ FM (k i)) (c : ℤ) (n : ℕ) :
    ∀ (s : Finset ι), s.card = n → ∀ b : ι → B, (∀ i ∈ s, b i ∈ F (c - k i)) →
      (∀ g, ρ g (∑ i ∈ s, b i • d i) - ∑ i ∈ s, b i • d i ∈ FM (c + 1)) →
      ∃ w ∈ FM c, (∀ g, ρ g w = w) ∧ ∑ i ∈ s, b i • d i - w ∈ FM (c + 1) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro s hn b hb hsum
  by_cases hs : ∃ i ∈ s, ∃ κ : ι → B, (∀ j, κ j ∈ F 0 ∧ (∀ g, σ g (κ j) = κ j) ∧ (k i ≠ k j → κ j = 0)) ∧
      d i + ∑ j ∈ s.erase i, κ j • d j ∈ FM (k i + 1)
  · obtain ⟨i, hi, κ, hκ, hmem⟩ := hs
    have heq : ∑ j ∈ s, b j • d j = b i • (d i + ∑ j ∈ s.erase i, κ j • d j) +
        ∑ j ∈ s.erase i, (b j - b i * κ j) • d j := by
      rw [← Finset.add_sum_erase s _ hi]
      simp only [smul_add, Finset.smul_sum, mul_smul, sub_smul, Finset.sum_sub_distrib]
      abel
    have h1 := hsmul _ _ _ _ (hb i hi) hmem
    rw [show c - k i + (k i + 1) = c + 1 by ring] at h1
    rw [heq] at hsum ⊢
    obtain ⟨w, hw, hwg, hw'⟩ := ih _ (hn ▸ Finset.card_erase_lt_of_mem hi) (s.erase i) rfl
      (fun j => b j - b i * κ j) (fun j hj => by
        refine (F _).sub_mem (hb j (Finset.mem_of_mem_erase hj)) ?_
        by_cases hk : k i = k j
        · have := hmul _ _ _ _ (hb i hi) (hκ j).1
          rwa [add_zero, hk] at this
        · rw [(hκ j).2.2 hk, mul_zero]
          exact (F _).zero_mem) (fun g => by
        have h2 := (FM _).sub_mem (hsum g) ((FM _).sub_mem (hMG g _ _ h1) h1)
        convert h2 using 1
        rw [map_add (ρ g) (b i • _)]
        abel)
    refine ⟨w, hw, hwg, ?_⟩
    rw [add_sub_assoc]
    exact (FM _).add_mem h1 hw'
  · have hg : ∀ g, ∀ i ∈ s, σ g (b i) - b i ∈ F (c - k i + 1) := fun g =>
      graded_indep σ ρ F FM hρ hmul hsmul hFG hMG hinv hT k d hd hdk s hs c
        (fun i => σ g (b i) - b i) (fun i hi => (F _).sub_mem (hFG _ _ _ (hb i hi)) (hb i hi)) (by
          convert hsum g using 1

          simp only [map_sum, hρ, hd, sub_smul, Finset.sum_sub_distrib])
    have hκ : ∀ i, ∃ κ ∈ F 0, (∀ g, σ g κ = κ) ∧ (c - k i ≠ 0 → κ = 0) ∧
        (i ∈ s → b i - κ ∈ F (c - k i + 1)) := fun i => by
      by_cases hi : i ∈ s
      · obtain ⟨κ, h1, h2, h3, h4⟩ := hT _ _ (hb i hi) (fun g => hg g i hi)
        exact ⟨κ, h1, h2, h3, fun _ => h4⟩
      · exact ⟨0, (F 0).zero_mem, fun g => map_zero _, fun _ => rfl, fun h => (hi h).elim⟩
    choose κ h1 h2 h3 h4 using hκ
    refine ⟨∑ i ∈ s, κ i • d i, (FM _).sum_mem fun i _ => ?_, fun g => ?_, ?_⟩
    · by_cases hk : c - k i = 0
      · have := hsmul _ _ _ _ (h1 i) (hdk i)
        rwa [show 0 + k i = c by omega] at this
      · rw [h3 i hk, zero_smul]
        exact (FM _).zero_mem

    · simp only [map_sum, hρ, hd, h2]
    · rw [← Finset.sum_sub_distrib]
      refine (FM _).sum_mem fun i hi => ?_
      have := hsmul _ _ _ _ (h4 i hi) (hdk i)
      rwa [show c - k i + 1 + k i = c + 1 by ring, sub_smul] at this

theorem invariant_mod
    (hρ : ∀ g (b : B) (m : M), ρ g (b • m) = σ g b • ρ g m)
    (hmul : ∀ a b x y, x ∈ F a → y ∈ F b → x * y ∈ F (a + b))
    (hsmul : ∀ a b x y, x ∈ F a → y ∈ FM b → x • y ∈ FM (a + b))
    (hFG : ∀ g a x, x ∈ F a → σ g x ∈ F a)
    (hMG : ∀ g a x, x ∈ FM a → ρ g x ∈ FM a)
    (hinv : ∀ a b, b ∈ F a → b ∉ F (a + 1) → ∃ β ∈ F (-a), β * b - 1 ∈ F 1)
    (hT : ∀ n e, e ∈ F n → (∀ g, σ g e - e ∈ F (n + 1)) →
      ∃ κ ∈ F 0, (∀ g, σ g κ = κ) ∧ (n ≠ 0 → κ = 0) ∧ e - κ ∈ F (n + 1))
    (hFa : Antitone F) (hMa : Antitone FM) (hFe : ∀ x, ∃ a, x ∈ F a) (hMe : ∀ x, ∃ a, x ∈ FM a)
    (hspan : ∀ y : M, ∃ (m : ℕ) (b : Fin m → B) (d : Fin m → M),
      (∀ i g, ρ g (d i) = d i) ∧ y = ∑ i, b i • d i)
    (a b : ℤ) (z : M) (hz : z ∈ FM a) (hg : ∀ g, ρ g z - z ∈ FM b) :
    ∃ w ∈ FM a, (∀ g, ρ g w = w) ∧ z - w ∈ FM b := by
  have key : ∀ c, a ≤ c → c ≤ max a b → ∃ w ∈ FM a, (∀ g, ρ g w = w) ∧ z - w ∈ FM c := by
    intro c hc
    induction c, hc using Int.leInduction with
    | base => exact fun _ => ⟨0, (FM _).zero_mem, fun g => map_zero _, by rwa [sub_zero]⟩
    | succ c hc ih =>
      intro hcb
      have hcb' : c + 1 ≤ b := by omega
      obtain ⟨w, hw, hwg, hzw⟩ := ih (by omega)
      obtain ⟨m, b₀, d₀, hd₀, e₀⟩ := hspan (z - w)
      obtain ⟨m', k', b', d', h, e⟩ := filtered σ ρ F FM hρ hmul hsmul hFG hMG hinv hT hFa hMa hFe hMe
        c (z - w) hzw m b₀ d₀ hd₀ e₀
      obtain ⟨w', hw', hwg', hzw'⟩ := step_invariant σ ρ F FM hρ hmul hsmul hFG hMG hinv hT k' d'
        (fun i => (h i).1) (fun i => (h i).2.1) c _ Finset.univ rfl b' (fun i _ => (h i).2.2)
        (fun g => by
          rw [← e, map_sub, hwg, sub_sub_sub_cancel_right]
          exact hMa hcb' (hg g))
      refine ⟨w + w', (FM _).add_mem hw (hMa hc hw'), fun g => by rw [map_add (f := _), hwg, hwg'], ?_⟩
      rwa [← e, sub_sub] at hzw'
  obtain ⟨w, hw, hwg, hzw⟩ := key (max a b) (le_max_left _ _) le_rfl
  exact ⟨w, hw, hwg, hMa (le_max_right _ _) hzw⟩

end Abstract

theorem tied_invariant_mod (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P)
    (TT : LocTied l P AI) (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL]
    [FiniteDimensional ℚ_[l] LL] (V : Type) [AddCommGroup V] [Module LL V] [Module ℚ_[l] V]
    [IsScalarTower ℚ_[l] LL V] [FiniteDimensional LL V] (ρ : Representation LL ↥(GK K) V)
    (hdR : IsDR (P.PD K) ρ) (a b : ℤ) (z : V ⊗[ℚ_[l]] P.R.BdR)
    (hz : z ∈ FilV (P.PD K) (LL := LL) (V := V) a)
    (hg : ∀ g, actVdR (P.PD K) ρ g z - z ∈ FilV (P.PD K) (LL := LL) (V := V) b) :
    ∃ w ∈ DdR (P.PD K) ρ ⊓ FilV (P.PD K) (LL := LL) (V := V) a,
      z - w ∈ FilV (P.PD K) (LL := LL) (V := V) b := by
  obtain ⟨Θ⟩ := GlobalTheory.MemLoc.TiedTheta.nonempty_thetaL l P AI TT
  have hspan := GlobalTheory.Per.DeRhamSpan.span_of_isField (P.PD K) ρ
    (GlobalTheory.Per.TiedField.tied_field l P AI TT).1 hdR
  let φ : P.R.BdR →+* Module.End LL (V ⊗[ℚ_[l]] P.R.BdR) :=
    { toFun := fun b => AlgebraTensorModule.map (LinearMap.id : V →ₗ[LL] V) (LinearMap.mulLeft ℚ_[l] b)
      map_one' := by ext; simp
      map_mul' := fun x y => by ext; simp [mul_assoc]
      map_zero' := by ext; simp
      map_add' := fun x y => by ext; simp [add_mul, tmul_add] }
  letI : Module P.R.BdR (V ⊗[ℚ_[l]] P.R.BdR) := Module.compHom _ φ
  have hsm : ∀ (b : P.R.BdR) (x : V ⊗[ℚ_[l]] P.R.BdR), b • x =
      AlgebraTensorModule.map (LinearMap.id : V →ₗ[LL] V) (LinearMap.mulLeft ℚ_[l] b) x := fun _ _ => rfl
  have hD : ∀ x, x ∈ DdR (P.PD K) ρ ↔ ∀ g, actVdR (P.PD K) ρ g x = x := fun x => by
    simp [DdR, Submodule.mem_iInf, sub_eq_zero]
  have htm : ∀ (a : ℤ) (v : V) (x : P.R.BdR), x ∈ (P.PD K).Fil a →
      v ⊗ₜ[ℚ_[l]] x ∈ FilV (P.PD K) (LL := LL) (V := V) a := fun a v x hx =>
    ⟨v ⊗ₜ ⟨x, hx⟩, rfl⟩
  have hind : ∀ (a : ℤ) (S : AddSubgroup (V ⊗[ℚ_[l]] P.R.BdR)),
      (∀ (v : V) (x : P.R.BdR), x ∈ (P.PD K).Fil a → v ⊗ₜ[ℚ_[l]] x ∈ S) →
      ∀ z ∈ FilV (P.PD K) (LL := LL) (V := V) a, z ∈ S := by
    rintro a S hS _ ⟨z, rfl⟩
    induction z using TensorProduct.induction_on with
    | zero => rw [map_zero]; exact S.zero_mem
    | tmul v x => exact hS v x x.2
    | add x y hx hy => rw [map_add (f := _)]; exact S.add_mem hx hy
  have hFa : Antitone fun a => ((P.PD K).Fil a).toAddSubgroup :=
    antitone_int_of_succ_le fun a => (P.PD K).Fil_anti a
  have hMa : Antitone fun a => (FilV (P.PD K) (LL := LL) (V := V) a).toAddSubgroup :=
    fun a a' h z hz => hind a' _ (fun v x hx => htm a v x (hFa h hx)) z hz
  obtain ⟨w, hw, hwg, hzw⟩ := invariant_mod (G := ↥(GK K))
    (fun g => ((P.PD K).actdR g : P.R.BdR →+* P.R.BdR))
    (fun g => (actVdR (P.PD K) ρ g).toAddMonoidHom)
    (fun a => ((P.PD K).Fil a).toAddSubgroup)
    (fun a => (FilV (P.PD K) (LL := LL) (V := V) a).toAddSubgroup)
    (fun g b x => by
      rw [hsm, hsm]
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul v x => simp [actVdR]
      | add x y hx hy => simp only [map_add (f := _), hx, hy])
    (P.PD K).Fil_mul
    (fun a c x z hx hz => hind c
      ((FilV (P.PD K) (LL := LL) (V := V) (a + c)).toAddSubgroup.comap (φ x).toAddMonoidHom)
      (fun v w hw => htm _ v (x * w) ((P.PD K).Fil_mul _ _ _ _ hx hw)) z hz)
    (P.PD K).Fil_G
    (fun g a z hz => hind a
      ((FilV (P.PD K) (LL := LL) (V := V) a).toAddSubgroup.comap (actVdR (P.PD K) ρ g).toAddMonoidHom)
      (fun v w hw => htm _ (ρ g v) ((P.PD K).actdR g w) ((P.PD K).Fil_G _ _ _ hw)) z hz)
    (graded_inv Θ K) (graded_invariants TT Θ K) hFa hMa (P.PD K).Fil_exh
    (fun x => by
      induction x using TensorProduct.induction_on with
      | zero => exact ⟨0, AddSubgroup.zero_mem _⟩
      | tmul v x =>
        obtain ⟨c, hc⟩ := (P.PD K).Fil_exh x
        exact ⟨c, htm c v x hc⟩
      | add x y hx hy =>
        obtain ⟨c, hc⟩ := hx
        obtain ⟨c', hc'⟩ := hy
        exact ⟨min c c', AddSubgroup.add_mem _ (hMa (min_le_left _ _) hc) (hMa (min_le_right _ _) hc')⟩)
    (fun y => by
      obtain ⟨m, b, d, hd, e⟩ := hspan y
      exact ⟨m, b, d, fun i g => (hD _).1 (hd i) g, e⟩)
    a b z hz hg
  exact ⟨w, ⟨(hD _).2 hwg, hw⟩, hzw⟩

theorem tate_fil_quot : ∀ D : D7, Formalism.MainNotions.LocalSituation.adm5 D := by
  intro D l _ K LL _ _ _ O _ _ hO A hA a b z hz hg
  haveI := hO.2.1
  exact tied_invariant_mod l (D.loc l) (D.locA l) (D.locT l) K LL A.V A.ρ hA a b z hz hg

end GlobalTheory.TateFilQuot
end

section

noncomputable section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module

namespace GlobalTheory.ChiOneNoPt

open GlobalTheory.IndefiniteRowSideFullHecke.JumpDictionary GlobalTheory.JumpDictionaryFoundation

abbrev sOne (D : D7) : ℝ := ((D.R.t : ℝ) - 1) / 2 + (1 - (D.R.nV : ℝ)) / 2

theorem charpoly_fin_one {R : Type} [CommRing R] (M : Matrix (Fin 1) (Fin 1) R) :
    M.charpoly = Polynomial.X - Polynomial.C (M 0 0) := by
  simp [Matrix.charpoly, Matrix.det_fin_one, Matrix.charmatrix_apply]

theorem integral (D : D7) (hB : BlockCharParam D) (i : D.nd.Loc) :
    ∀ τ : D.host.E →+* ℂ, ∀ z ∈ D.naut.infG (D.naut.tw (D.naut.muC i) D.naut.etaTinv) τ,
      ∃ k : ℤ, z + ((sOne D : ℝ) : ℂ) = (k : ℂ) := by
  intro τ z hz
  obtain ⟨ρ, b, rfl⟩ := exists_embOver D τ
  obtain ⟨a, ha⟩ := firstJump_int D i ρ b
  have hm : z + (blockExp D 1 : ℂ) ∈
      (D.naut.infG (D.naut.tw (D.naut.muC i) D.naut.etaTinv) (embOver D ρ b)).map (· + (blockExp D 1 : ℂ)) :=
    Multiset.mem_map_of_mem (· + (blockExp D 1 : ℂ)) hz
  rw [inf_block D hB i 1 ρ b, Multiset.mem_singleton] at hm
  have hs : blockExp D 1 = sOne D := by simp [blockExp, sOne]
  refine ⟨-a, ?_⟩
  rw [← hs, hm, ha]
  push_cast
  ring

theorem eq_chi (D : D7) (h5 : SumRepresentations.adm5 D) (i : D.nd.Loc) (w₀ : HeightOneSpectrum (𝓞 D.host.E))
    (hw₀ : w₀ ∈ placesOver D.host.E (D.nd.l i)) (ρ : GE D.nd →* GL (Fin 1) (Qbar (D.nd.l i)))
    (hc : Continuous fun g =>
      ((ρ g : GL (Fin 1) (Qbar (D.nd.l i))) : Matrix (Fin 1) (Fin 1) (Qbar (D.nd.l i))))
    (haway : ∀ w, w ∉ placesOver D.host.E (D.nd.l i) →
      D.naut.wdOf i ρ w = D.naut.lpTw (D.naut.locG (D.naut.tw (D.naut.muC i) D.naut.etaTinv) w) (sOne D)) :
    ρ = mapRep (iotaOQ D.nd D.naut i) (chiGL D i 1) := by
  have hl : (placesOver D.host.E (D.nd.l i)).Finite := by
    have h0 : ((D.nd.l i : ℕ) : 𝓞 D.host.E) ≠ 0 := Nat.cast_ne_zero.2 (D.nd.lPrime i).out.ne_zero
    refine (Ideal.finite_factors (I := Ideal.span {((D.nd.l i : ℕ) : 𝓞 D.host.E)})
      (by simpa [Ideal.span_singleton_eq_bot] using h0)).subset fun v hv => ?_
    exact Ideal.dvd_span_singleton.2 hv
  let Sg : Set (HeightOneSpectrum (𝓞 D.host.E)) :=
    placesOver D.host.E (D.nd.l i) ∪ ↑(D.nd.S i) ∪ ↑(D.nd.Q i)
  have hSg : Sg.Finite := (hl.union (D.nd.S i).finite_toSet).union (D.nd.Q i).finite_toSet
  have hd := h5.2.2.1 Sg hSg
  have key : (fun g => ((ρ g : GL (Fin 1) (Qbar (D.nd.l i))) : Matrix (Fin 1) (Fin 1) (Qbar (D.nd.l i))) 0 0) =
      fun g => iotaOQ D.nd D.naut i ((D.nd.chi i 1 g : (D.nd.O i)ˣ) : D.nd.O i) := by
    refine Continuous.ext_on (dense_iff_closure_eq.2 hd)
      ((continuous_apply 0).comp ((continuous_apply 0).comp hc))
      ((continuous_iotaOQ D i w₀ hw₀).comp (D.nd.chi_cont i 1)) ?_
    rintro σ ⟨w, hwS, hsp, B, hB, hσ⟩
    simp only [Sg, Set.mem_union, Finset.mem_coe, not_or] at hwS
    have hso : SplitOut D.nd i w := ⟨hsp, hwS.1.1, hwS.1.2, hwS.2⟩
    obtain ⟨hu, hf⟩ := D.naut.chi_mu i w hso
    have hun : D.naut.unr (D.naut.wdOf i ρ w) := by
      rw [haway w hwS.1.1]; exact (D.naut.unr_tw _ _).2 hu
    have e := D.naut.wdOf_frob i ρ w hwS.1.1 hc hun B σ hB hσ
    rw [haway w hwS.1.1, hf B σ hB hσ, Multiset.map_singleton, Multiset.prod_singleton, charpoly_fin_one,
      Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C] at e
    exact (D.naut.iotaQC i).injective (Polynomial.C_inj.1 (sub_right_injective e))
  ext g a b
  obtain rfl : a = 0 := Subsingleton.elim _ _
  obtain rfl : b = 0 := Subsingleton.elim _ _
  refine (congrFun key g).trans ?_
  rw [← chiGL_apply D i 1 g 0 0]
  rfl

theorem isConstituent_chiGL (D : D7) (i : D.nd.Loc) :
    GlobalTheory.IndefiniteRowSideFullHecke.BlockCharactersCrystallineNonGaloisCusps.IsConstituent D i (D.nd.chi i 1) ((Units.coeHom _).comp (chiGL D i 1)) := by
  refine ⟨fun _ => 1, fun h => one_ne_zero (congrFun h 0), fun g => ?_⟩
  funext a
  obtain rfl : a = 0 := Subsingleton.elim _ _
  simp [Matrix.mulVec, dotProduct, mapM, chiGL]

end GlobalTheory.ChiOneNoPt

end
end

section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pass GlobalTheory.Cut

namespace GlobalTheory.LocalPositionData

theorem position_data_exist : ∀ {eps : ℝ} (Fm : FamP eps), ∃ x0 : ℝ, ∀ x ≥ x0, Fm.x1 < x → ∀ (a : Fm.Ix x), AdmissibleParameterJ.JumpConditions (Fm.L x a) → ∀ l : ℕ, l.Prime → LevelStarExponents.lStar (Fm.L x a) < (l : ℝ) → (5 ≤ l ∧ (Fm.D x a).R.t + 1 < l ∧ l ≠ (Fm.D x a).host.q ∧ l ≠ (Fm.D x a).host.d ∧ l ∉ (Fm.D x a).host.small) ∧ (l ∉ GlobalTheory.IndefiniteRowSideFullHecke.BaseSizes.Exc (Fm.L x a) → ∀ j : ℕ, 1 ≤ j → j ≤ (Fm.D x a).R.m → ∀ (n : ℕ) [NeZero n] (up : ZMod n → Bool) (τ : ZMod n → (Fm.D x a).what₂.Tau), ∃ (h w η : ZMod n → ℕ) (typ : ZMod n → Bool) (U : ZMod n → Multiset ℤ), tableLineDegreeTwo.PositionHyps l n (Fm.D x a).R.t h w η typ U ∧ ∀ (c : ZMod n) (b : ℤ), ((U c).count (b + w c) = 1 ↔ (b : ℚ) ∈ AdmissibleParameterJ.JW (Fm.D x a) (up c) j (τ c)) ∧ (U c).count (b + w c) ≤ 1) := by
  intro eps Fm
  obtain ⟨x0, hx0⟩ := GlobalTheory.T.conductorPrimes_lt_specialPrimeThreshold_eventually Fm
  refine ⟨x0, fun x hx hx1 a _ l hl hlS => ?_⟩
  obtain ⟨hqS, hdS, hsS⟩ := hx0 x hx hx1 a
  obtain ⟨htη, hη, hB, hSc, hls1, hls2, hH⟩ := GlobalTheory.T.specialPrimeThreshold_numerics_along_family Fm x hx1 a
  have ht1 : 1 ≤ (Fm.D x a).R.t := by
    have := (Fm.D x a).R.rank_add_five_le; omega
  have htR : (0 : ℝ) ≤ (Fm.D x a).R.t := by positivity
  refine ⟨⟨?_, ?_, ?_, ?_, fun h => absurd (hsS l h) (not_lt.2 hlS.le)⟩, ?_⟩
  · have : (7 : ℝ) < l := by linarith
    exact_mod_cast (show 5 ≤ l by exact_mod_cast (show (5 : ℝ) ≤ l by linarith))
  · have : ((Fm.D x a).R.t : ℝ) + 1 < l := by linarith
    exact_mod_cast this
  · intro h; rw [h] at hlS; linarith
  · intro h; rw [h] at hlS; linarith
  intro hexc j hj1 hjm n _ up τ
  have hfinL : ∀ c, (AdmissibleParameterJ.lowT (Fm.D x a) (up c) j (τ c)).Finite := by
    intro c
    have h0 : (AdmissibleParameterJ.lowJ (Fm.D x a) j (τ c)).Finite :=
      (Set.finite_range (fun i : Fin (Fm.D x a).R.m => AdmissibleParameterJ.sz (Fm.D x a) j (τ c) - ((Fm.D x a).hc (τ c)).b i + AdmissibleParameterJ.c0 (Fm.D x a))).subset
        (by rintro q ⟨i, rfl⟩; exact ⟨i, rfl⟩)
    unfold AdmissibleParameterJ.lowT
    split_ifs
    · exact h0
    · exact h0.preimage (Set.injOn_of_injective (fun p q h => by unfold AdmissibleParameterJ.refl at h; linarith))
  have hfinC : ∀ c, (AdmissibleParameterJ.cloudT (Fm.D x a) (up c) j (τ c)).Finite := by
    intro c
    have h0 : (AdmissibleParameterJ.cloudJ (Fm.D x a) j (τ c)).Finite :=
      (Set.finite_range (fun i : Fin ((Fm.D x a).R.k - 1) => AdmissibleParameterJ.sz (Fm.D x a) j (τ c) + ((Fm.D x a).hc (τ c)).v i + AdmissibleParameterJ.c0 (Fm.D x a))).subset
        (by rintro q ⟨i, rfl⟩; exact ⟨i, rfl⟩)
    unfold AdmissibleParameterJ.cloudT
    split_ifs
    · exact h0
    · exact h0.preimage (Set.injOn_of_injective (fun p q h => by unfold AdmissibleParameterJ.refl at h; linarith))
  set Fl : ZMod n → Finset ℤ := fun c => GlobalTheory.PositionData.intPts (AdmissibleParameterJ.lowT (Fm.D x a) (up c) j (τ c)) with hFl
  set Fc : ZMod n → Finset ℤ := fun c => GlobalTheory.PositionData.intPts (AdmissibleParameterJ.cloudT (Fm.D x a) (up c) j (τ c)) with hFc
  have hdat : ∀ c, ∃ W0 ∈ GlobalTheory.IndefiniteRowSideFullHecke.BaseSizes.baseSizes (Fm.L x a),
      (∀ z ∈ Fl c, |(z : ℝ) - (((Fm.D x a).R.t : ℝ) - 1) / 2| ≤ (Fm.L x a).etaSz ∧
        2 * ((Fm.L x a).sc.b / LevelStarExponents.lStar (Fm.L x a)) + ((Fm.D x a).R.t : ℝ) / 2 + 3 ≤
          |(z : ℝ) - (((Fm.D x a).R.t : ℝ) - 1) / 2|) ∧
      (∀ z ∈ Fc c, W0 ≤ (if up c then (z : ℝ) - (((Fm.D x a).R.t : ℝ) - 1) / 2 else (((Fm.D x a).R.t : ℝ) - 1) / 2 - z) ∧
        (if up c then (z : ℝ) - (((Fm.D x a).R.t : ℝ) - 1) / 2 else (((Fm.D x a).R.t : ℝ) - 1) / 2 - z) ≤
          W0 + (Fm.L x a).Sc + (Fm.L x a).etaSz + 1) := by
    intro c
    obtain ⟨hlo, W0, hW0, hcl⟩ := GlobalTheory.T.lowJumps_and_cloud_in_windows_along_family Fm x hx1 a j hj1 hjm (up c) (τ c)
    refine ⟨W0, hW0, fun z hz => hlo z ((GlobalTheory.PositionData.mem_intPts (hfinL c) z).1 hz),
      fun z hz => hcl z ((GlobalTheory.PositionData.mem_intPts (hfinC c) z).1 hz)⟩
  set hh : ZMod n → ℕ := fun c => GlobalTheory.PositionData.hS (up c) (Fm.D x a).R.t (Fl c) (Fc c) with hhh
  have hhle : ∀ c, (hh c : ℝ) ≤ (Fm.L x a).sc.b + (Fm.L x a).Sc + 2 * (Fm.L x a).etaSz + 3 := by
    intro c
    obtain ⟨W0, hW0, hlo, hcl⟩ := hdat c
    obtain ⟨hW1, hW2⟩ := GlobalTheory.T.baseSize_bounds_along_family Fm x hx1 a W0 hW0
    have := GlobalTheory.T.shiftedJumpUpperBound_le_twist_bound (Fm.D x a).R.t (up c) (Fl c) (Fc c) (Fm.L x a).etaSz (Fm.L x a).Sc
      ((Fm.L x a).sc.b / LevelStarExponents.lStar (Fm.L x a)) W0 ht1 htη hB hSc hlo hcl hW1
    show ((GlobalTheory.PositionData.hS (up c) (Fm.D x a).R.t (Fl c) (Fc c) : ℕ) : ℝ) ≤ _
    linarith
  have hsg : ∀ c, (Formalism.MainNotions.tableLineDegreeTwo.sg n l hh c : ℝ) ≤ 2 * ((Fm.L x a).sc.b / LevelStarExponents.lStar (Fm.L x a)) := by
    intro c
    have hl2 : 2 ≤ l := hl.two_le
    set W := (Fm.L x a).sc.b + (Fm.L x a).Sc + 2 * (Fm.L x a).etaSz + 3 with hW
    have hW0 : 0 ≤ W := le_trans (Nat.cast_nonneg _) (hhle c)
    have h1 := Formalism.IrreducibleCountingLemmas.TOP.carryFloorLeGeom n l hh ⌊W⌋₊ hl2 (fun c' => Nat.le_floor (hhle c')) c
    have h2 : ((⌊W⌋₊ : ℕ) : ℝ) / ((l : ℝ) - 1) ≤ W / ((l : ℝ) - 1) := by
      apply div_le_div_of_nonneg_right (Nat.floor_le hW0)
      have : (2 : ℝ) ≤ l := by exact_mod_cast hl2
      linarith
    have h3 := Formalism.IrreducibleCountingLemmas.TOP.geomRatioBound l (LevelStarExponents.lStar (Fm.L x a)) (Fm.L x a).sc.b W hW0 hls1 hlS hH
    have h4 : (Formalism.MainNotions.tableLineDegreeTwo.sg n l hh c : ℝ) = (Formalism.IrreducibleCountingLemmas.TOP.sg n l hh c : ℝ) := rfl
    rw [h4, ← mul_div_assoc]
    linarith
  refine ⟨hh, fun c => GlobalTheory.PositionData.wS (up c) (Fl c) (Fc c), fun c => GlobalTheory.PositionData.etaS (Fm.D x a).R.t (Fl c),
    up, fun c => GlobalTheory.PositionData.US (up c) (Fl c) (Fc c), ?_, ?_⟩
  · intro c
    obtain ⟨W0, hW0, hlo, hcl⟩ := hdat c
    obtain ⟨hW1, -⟩ := GlobalTheory.T.baseSize_bounds_along_family Fm x hx1 a W0 hW0
    have hex : ∀ m : ℤ, W0 + (-(Fm.L x a).etaSz - 2 * (GlobalTheory.IndefiniteRowSideFullHecke.BaseSizes.sgPlus (Fm.L x a) : ℝ) - 3) ≤ (m : ℝ) →
        (m : ℝ) ≤ W0 + ((Fm.L x a).Sc + (Fm.L x a).etaSz + (Fm.L x a).etaSz +
          2 * (GlobalTheory.IndefiniteRowSideFullHecke.BaseSizes.sgPlus (Fm.L x a) : ℝ) + 4) → ¬ (l : ℤ) ∣ m :=
      fun m h1 h2 hd => hexc ⟨hl, hlS, W0, hW0, m, ⟨h1, h2⟩, hd⟩
    have hσP : Formalism.MainNotions.tableLineDegreeTwo.sg n l hh c ≤ GlobalTheory.IndefiniteRowSideFullHecke.BaseSizes.sgPlus (Fm.L x a) := by
      unfold GlobalTheory.IndefiniteRowSideFullHecke.BaseSizes.sgPlus
      apply Int.le_floor.mpr
      rw [mul_div_assoc]; exact hsg c
    have hT1 : 2 * (Fm.L x a).etaSz + 8 * ((Fm.L x a).sc.b / LevelStarExponents.lStar (Fm.L x a)) + 7 < (l : ℝ) := by linarith
    exact GlobalTheory.T.jump_position_conditions_at_letter l (Fm.D x a).R.t (up c) (Fl c) (Fc c) (Fm.L x a).etaSz (Fm.L x a).Sc
      ((Fm.L x a).sc.b / LevelStarExponents.lStar (Fm.L x a)) W0 (GlobalTheory.IndefiniteRowSideFullHecke.BaseSizes.sgPlus (Fm.L x a)) (Formalism.MainNotions.tableLineDegreeTwo.sg n l hh c)
      ht1 htη hB hSc hlo hcl hW1 hex (hsg c) hσP hT1
  · intro c b
    rw [GlobalTheory.PositionData.count_US]
    have hm : b ∈ Fl c ∪ Fc c ↔ (b : ℚ) ∈ AdmissibleParameterJ.JW (Fm.D x a) (up c) j (τ c) := by
      rw [Finset.mem_union, GlobalTheory.PositionData.mem_intPts (hfinL c), GlobalTheory.PositionData.mem_intPts (hfinC c)]
      unfold AdmissibleParameterJ.JW
      rw [Set.mem_union]; tauto
    rw [← hm]
    split_ifs <;> simp_all

end GlobalTheory.LocalPositionData
end

end

section

@[expose] public section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices

theorem _root_.GlobalTheory.T.wachModule_descent_to_tame_subextension : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW), P9 D HW F := by
  first | exact @GlobalTheory.NL.p9_statement | exact GlobalTheory.NL.p9_statement | (intros; apply GlobalTheory.NL.p9_statement <;> assumption)

end
end
