module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle221
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle263
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle315
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ColumnArrowKernelRealEqDetCharMulFockKernel
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasInfExpOfOrder
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle211
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle371
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalBlockDetBlockTriangular
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1830
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.OffPlacesPartMovedLevelKeepsStandardHomLattice
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneCosetOfIsTensor
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumOKEx
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationLeOneOfMem
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle664
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle009
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemSplit
public import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle004
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle686
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Std.Tactic.BVDecide.Normalize.Prop
import Std.Tactic.BVDecide.Normalize.BitVec
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle469

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.RowVal

open GlobalTheory.CellInt

theorem cellBot_iff {G : Type} [Group G] {R K : Subgroup G} {b x : G} :
    (∃ r ∈ R, ∃ a ∈ (⊥ : Subgroup G), ∃ k ∈ K, x = r * a * b * k) ↔ ∃ r ∈ R, ∃ k ∈ K, x = r * b * k := by
  constructor
  · rintro ⟨r, hr, a, ha, k, hk, rfl⟩
    rw [Subgroup.mem_bot] at ha
    subst ha
    exact ⟨r, hr, k, hk, by simp⟩
  · rintro ⟨r, hr, k, hk, rfl⟩
    exact ⟨r, hr, 1, Subgroup.one_mem _, k, hk, by simp⟩

theorem cellWt_eq {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
    (R K : Subgroup G) (ρ : Measure R) (μ : Measure G) (b : G) :
    cellWt ρ μ K b = (((μ (K : Set G)).toReal / (ρ (cellSet R K b b)).toReal : ℝ) : ℂ) := by
  simp only [cellWt, cellSet, measureReal_def, mul_assoc]

theorem niter_cellSum_at (ι : Type) [DecidableEq ι] (H : ι → Type) [∀ i, Group (H i)] [∀ i, TopologicalSpace (H i)]
    [∀ i, IsTopologicalGroup (H i)] [∀ i, MeasurableSpace (H i)] [∀ i, BorelSpace (H i)]
    (R K : ∀ i, Subgroup (H i)) (ρ : ∀ i, Measure (R i)) (μ : ∀ i, Measure (H i)) (l : List ι) (hl : l.Nodup)
    (hyp : ∀ i ∈ l, IsClosed (R i : Set (H i)) ∧ IsCompact (K i : Set (H i)) ∧ IsOpen (K i : Set (H i)) ∧
      (ρ i).IsHaarMeasure ∧ (ρ i).IsInvInvariant ∧ (μ i).IsHaarMeasure ∧ (μ i).IsMulRightInvariant) :
    ∀ (X : Type) (S : Finset X) (b : X → ∀ i, H i) (q : (∀ i, H i) → ℂ) (h : ∀ i, H i),
      (∀ β ∈ S, ∀ i, i ∉ l → b β i = h i) →
      (∀ β ∈ S, ∀ β' ∈ S, InCells (fun _ => ⊥) R K l (b β) (b β') → β = β') → BiInv R K l q →
      (∀ g, (∀ i, i ∉ l → g i = h i) → q g ≠ 0 → ∃ β ∈ S, InCells (fun _ => ⊥) R K l (b β) g) →
      NIter ρ μ q l h (∑ β ∈ S, (l.map fun i => cellWt (ρ i) (μ i) (K i) (b β i)).prod * q (b β)) := by
  induction l with
  | nil =>
    intro X S b q h hb hd _ hs
    simp only [NIter, List.map_nil, List.prod_nil, one_mul]
    have hbh : ∀ β ∈ S, b β = h := fun β hβ => funext fun i => hb β hβ i (by simp)
    have hsub : ∀ β ∈ S, ∀ β' ∈ S, β = β' := fun β hβ β' hβ' => hd β hβ β' hβ' (fun i hi => by simp at hi)
    by_cases hq : q h = 0
    · rw [hq]
      exact Finset.sum_eq_zero fun β hβ => by rw [hbh β hβ, hq]
    · obtain ⟨β, hβ, -⟩ := hs h (fun _ _ => rfl) hq
      rw [Finset.sum_eq_single β (fun β' hβ' hne => absurd (hsub β' hβ' β hβ) hne) (fun h' => absurd hβ h'), hbh β hβ]
  | cons i l' ih =>
    intro X S b q h hb hd hq hs
    classical
    obtain ⟨hi, hl'⟩ := List.nodup_cons.1 hl
    obtain ⟨hcl, hkc, hko, hρ, hρi, hμ, hμr⟩ := hyp i (by simp)
    have hyp' : ∀ j ∈ l', _ := fun j hj => hyp j (List.mem_cons_of_mem _ hj)
    have hq' : BiInv R K l' q := fun j hj => hq j (List.mem_cons_of_mem _ hj)
    have hne : ∀ j ∈ l', j ≠ i := fun j hj hji => hi (hji ▸ hj)
    set Wt' : X → ℂ := fun β => (l'.map fun j => cellWt (ρ j) (μ j) (K j) (b β j)).prod with hWt'
    have qinv : ∀ β g, g ∈ dcos (R i) (K i) (b β i) → q (Function.update (b β) i g) = q (b β) := by
      rintro β g ⟨r, hr, k, hk, rfl⟩
      have h1 := (hq i (by simp) (b β)).1 r hr
      have h2 := (hq i (by simp) (Function.update (b β) i (r * b β i))).2 k hk
      simp only [Function.update_self, Function.update_idem] at h2
      rw [h2, h1]
    refine ⟨fun g => ∑ β ∈ S, Wt' β * q (b β) * (if g ∈ dcos (R i) (K i) (b β i) then 1 else 0), ?_, ?_⟩
    · haveI := hρ; haveI := hρi; haveI := hμ
      have hS := quotient_integral_finset_sum S (fun β g => Wt' β * q (b β) * (if g ∈ dcos (R i) (K i) (b β i) then (1 : ℂ) else 0))
        (fun β => Wt' β * q (b β) * (((μ i (K i : Set (H i))).toReal / (ρ i (cellSet (R i) (K i) (b β i) (b β i))).toReal : ℝ) : ℂ))
        (fun β _ => by
          have := (isQuotientIntegral_indicator_doubleCoset (R i) (K i) hcl hkc hko (ρ i) (μ i) (b β i)).smul (Wt' β * q (b β))
          convert this using 1)
      convert hS using 1
      apply Finset.sum_congr rfl
      intro β _
      rw [List.map_cons, List.prod_cons, cellWt_eq (R i)]
      ring
    · intro g
      have key := ih hl' hyp' X (S.filter fun β => g ∈ dcos (R i) (K i) (b β i)) (fun β => Function.update (b β) i g) q
        (Function.update h i g) ?base ?dist hq' ?supp
      · convert key using 1
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro β _
        split_ifs with hg
        · have e : (l'.map fun j => cellWt (ρ j) (μ j) (K j) (Function.update (b β) i g j)).prod = Wt' β := by
            rw [hWt']
            congr 1
            apply List.map_congr_left
            intro j hj
            rw [Function.update_of_ne (hne j hj)]
          rw [e, qinv β g hg, mul_one]
        · simp
      case base =>
        intro β hβ j hj
        by_cases hji : j = i
        · subst hji; simp
        · rw [Function.update_of_ne hji, Function.update_of_ne hji]
          exact hb β (Finset.mem_filter.1 hβ).1 j (by simp [hji, hj])
      case dist =>
        intro β hβ β' hβ' hc
        obtain ⟨hβS, hgβ⟩ := Finset.mem_filter.1 hβ
        obtain ⟨hβS', hgβ'⟩ := Finset.mem_filter.1 hβ'
        refine hd β hβS β' hβS' ?_
        intro j hj
        rcases List.mem_cons.1 hj with rfl | hj'
        · rw [cellBot_iff]
          have e1 := dcos_eq_of_mem hgβ
          have e2 := dcos_eq_of_mem hgβ'
          have hm : b β' j ∈ dcos (R j) (K j) (b β' j) := ⟨1, Subgroup.one_mem _, 1, Subgroup.one_mem _, by simp⟩
          rw [← e2, e1] at hm
          exact hm
        · obtain ⟨r, hr, a, ha, k, hk, e⟩ := hc j hj'
          refine ⟨r, hr, a, ha, k, hk, ?_⟩
          simpa [Function.update_of_ne (hne j hj')] using e
      case supp =>
        intro g' hg' hq0
        have hgi : g' i = g := by simpa using hg' i hi
        obtain ⟨β, hβ, hc⟩ := hs g' (fun j hj => by
          have hji : j ≠ i := fun e => hj (e ▸ List.mem_cons_self ..)
          have := hg' j (fun hj' => hj (List.mem_cons_of_mem _ hj'))
          rwa [Function.update_of_ne hji] at this) hq0
        refine ⟨β, Finset.mem_filter.2 ⟨hβ, ?_⟩, ?_⟩
        · have := hc i (by simp)
          rw [cellBot_iff, hgi] at this
          exact this
        · intro j hj
          obtain ⟨r, hr, a, ha, k, hk, e⟩ := hc j (List.mem_cons_of_mem _ hj)
          refine ⟨r, hr, a, ha, k, hk, ?_⟩
          simpa [Function.update_of_ne (hne j hj)] using e

theorem niter_cellSum : ∀ (ι : Type) [DecidableEq ι] (H : ι → Type) [∀ i, Group (H i)] [∀ i, TopologicalSpace (H i)] [∀ i, IsTopologicalGroup (H i)] [∀ i, SecondCountableTopology (H i)] [∀ i, LocallyCompactSpace (H i)] [∀ i, T2Space (H i)] [∀ i, MeasurableSpace (H i)] [∀ i, BorelSpace (H i)] (R K : ∀ i, Subgroup (H i)) (l : List ι), l.Nodup → ∀ (ρ : ∀ i, Measure (R i)) (μ : ∀ i, Measure (H i)), (∀ i ∈ l, IsClosed (R i : Set (H i)) ∧ IsCompact (K i : Set (H i)) ∧ IsOpen (K i : Set (H i)) ∧ (ρ i).IsHaarMeasure ∧ (ρ i).IsInvInvariant ∧ (μ i).IsHaarMeasure ∧ (μ i).IsMulRightInvariant) → ∀ (X : Type) (S : Finset X) (b : X → ∀ i, H i) (q : (∀ i, H i) → ℂ), (∀ β ∈ S, ∀ i, i ∉ l → b β i = 1) → (∀ β ∈ S, ∀ β' ∈ S, InCells (fun _ => ⊥) R K l (b β) (b β') → β = β') → BiInv R K l q → (∀ h, (∀ i, i ∉ l → h i = 1) → q h ≠ 0 → ∃ β ∈ S, InCells (fun _ => ⊥) R K l (b β) h) → NIter ρ μ q l 1 (∑ β ∈ S, (l.map fun i => cellWt (ρ i) (μ i) (K i) (b β i)).prod * q (b β)) := by
  intro ι _ H _ _ _ _ _ _ _ _ R K l hl ρ μ hyp X S b q hb hd hq hs
  exact niter_cellSum_at ι H R K ρ μ l hl hyp X S b q 1 (fun β hβ i hi => by simpa using hb β hβ i hi) hd hq
    (fun g hg => hs g (fun i hi => by simpa using hg i hi))

end GlobalTheory.RowVal
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.RowRep
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

def locAt (B : Frames G) (t : T) (w : Pl D.host.E) (j : ℕ) (hj : j ≤ D.R.m) :
    GA D (G.V (.grid D.R.m j)) →* GL (Fin ((locGrid G t w).rank (D.R.m, j))) (Kw w) :=
  (inBasis (rank_vertex G t w (X := (D.R.m, j)) ⟨le_rfl, hj⟩) (B.β D.R.m j) w).comp (Lev.finE _)

theorem locAt_inf (B : Frames G) (t : T) (w : Pl D.host.E) (j : ℕ) (hj : j ≤ D.R.m) {a : GA D (G.V (.grid D.R.m j))}
    (ha : a ∈ GinfC _) : locAt B t w j hj a = 1 := by
  have h : Lev.finE (G.V (.grid D.R.m j)) a = 1 := by
    simp only [Lev.finE, GinfC, MonoidHom.mem_ker] at ha ⊢
    rw [MonoidHom.comp_apply, ha, map_one]
  simp only [locAt, MonoidHom.comp_apply, h, map_one]

theorem exists_isFinOf (V : HSp D) (g : GA D V) : ∃ b, GlobalTheory.RowVal.IsFinOf g b := by
  obtain ⟨-, -, -, ⟨e, he⟩, -⟩ := GlobalTheory.AdelicSplit.adelic_split D V
  obtain ⟨p, rfl⟩ := e.surjective g
  exact ⟨p.2, p.2.2, p.1, p.1.2, (he p).symm⟩

theorem elt_succ (t : T) (w : Pl D.host.E) (β : Cosets (G := locGrid G t w) one_le_sLen (givenLevel G t w))
    (i : Fin ((locGrid G t w).m - 2)) :
    (repsAt G t w).elt β ((locGrid G t w).m, i.1 + 1) = (repsAt G t w).rep i (β i) := by
  simp only [Reps.elt]
  rw [onColumn_apply]
  simp only [dif_pos i.2]

end GlobalTheory.RowRep

namespace GlobalTheory.RowRep
variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem loc_rep (B : Frames G) (t : T) (s : ℤˣ) (β : CosFam G t) (w : locPl G t) (i : Fin ((locGrid G t w.1).m - 2))
    (hj : i.1 + 1 ≤ D.R.m) (r : GA D (G.V (.grid D.R.m (i.1 + 1))))
    (ρ : GL (Fin ((locGrid G t w.1).rank (D.R.m, i.1 + 1))) (Kw w.1)) (hρ : ρ = (repsAt G t w.1).rep i (β w i))
    (hr : (inBasis (rank_vertex G t w.1 (X := (D.R.m, i.1 + 1)) ⟨le_rfl, hj⟩) (B.β D.R.m (i.1 + 1)) w.1)
      (Lev.finE (G.V (.grid D.R.m (i.1 + 1))) r) =
      GlobalTheory.RowVal.sgnAt G t s w.1 (i.1 + 1) * (repsAt G t w.1).elt (β w) (D.R.m, i.1 + 1)) :
    locAt B t w.1 (i.1 + 1) hj r = GlobalTheory.RowVal.sgnAt G t s w.1 (i.1 + 1) * ρ := by
  rw [hρ, ← elt_succ]
  exact hr

theorem mk_eq_of {Gp : Type} [Group Gp] (H K : Subgroup Gp) {A A' S X Y ρ ρ' : Gp}
    (e : A' * (S * ρ') = X * (A * (S * ρ)) * Y) (hN : (A' * S)⁻¹ * X * (A * S) ∈ H) (hY : Y ∈ K) :
    DoubleCoset.mk H K ρ = DoubleCoset.mk H K ρ' := by
  rw [DoubleCoset.eq]
  refine ⟨_, hN, Y, hY, ?_⟩
  rw [show (A' * S)⁻¹ * X * (A * S) * ρ * Y = (A' * S)⁻¹ * (X * (A * (S * ρ)) * Y) by group, ← e]
  group

theorem idx_le {j : ℕ} (h : j ∈ GlobalTheory.RowVal.idx D) : 1 ≤ j ∧ j + 2 ≤ D.R.m := by
  simp only [GlobalTheory.RowVal.idx, List.mem_range'_1] at h
  omega

end GlobalTheory.RowRep
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.RowRealEq

variable {D : D7} {T : Type} {L : LevCh D T}

theorem hasInfExp_attChr_mu {μ0 : T} (hL : L.Is μ0) (t : T) {j : ℕ} (hj : j < D.R.m) (n : ℕ) (τ : D.what₂.Tau) :
    HasInfExp D (Formalism.IndefR.Lift.attChr (L.mu t (j + 1)) L.eta n) τ
      (-(D.hc τ).e ⟨j, hj⟩ - if Odd n then 1 / 2 else 0) := by
  have h0 := GlobalTheory.ColKer.mu_exp hL t j hj τ
  have heta : HasInfExp D L.eta τ (1 / 2) :=
    GlobalTheory.HeckeInfExp.hasInfExp_of_chrEq D _ _ _ hL.eta
      (GlobalTheory.Chain.StepVac.hasInfQ_tau (a := fun _ => 1 / 2) ⟨_, fun _ => by norm_num, L.C.isEta.inf⟩) τ
  unfold Formalism.IndefR.Lift.attChr
  split_ifs
  · rw [sub_eq_add_neg]
    exact GlobalTheory.Chain.StepVac.hasInfExp_mul h0 (GlobalTheory.Chain.StepVac.hasInfExp_inv heta)
  · simpa using h0

theorem realEqAt : Big fun ch => RealEqAt ch := by
  refine ⟨0, fun ε CF _ => ⟨0, fun D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F hS ch _ _ => ?_⟩⟩
  have hL := hS.core.lev
  intro t t' j hj
  refine ⟨fun a ha b hb f hf => ?_, fun a ha b hb f hf => ?_⟩
  · exact GlobalTheory.RealEqWeil.weilDatum_realEq D _ _ _ _ _ _ _ _ _
      (ch.W.om_is (.top t j) (show j + 1 ≤ D.R.m by omega)) (ch.W.om_is (.top t' j) (show j + 1 ≤ D.R.m by omega))
      (fun τ => ⟨_, hasInfExp_attChr_mu hL t hj _ τ, hasInfExp_attChr_mu hL t' hj _ τ⟩)
      (fun τ => ⟨_, hasInfExp_attChr_mu hL t hj _ τ, hasInfExp_attChr_mu hL t' hj _ τ⟩) a ha b hb f hf
  · exact GlobalTheory.RealEqWeil.weilDatum_realEq D _ _ _ _ _ _ _ _ _
      (ch.W.om_is (.mu t D.R.m j) (show D.R.m ≤ D.R.m ∧ j + 1 ≤ D.R.m by omega))
      (ch.W.om_is (.mu t' D.R.m j) (show D.R.m ≤ D.R.m ∧ j + 1 ≤ D.R.m by omega))
      (fun τ => ⟨_, hasInfExp_attChr_mu hL t hj _ τ, hasInfExp_attChr_mu hL t' hj _ τ⟩)
      (fun τ => ⟨_, hasInfExp_attChr_mu hL t hj _ τ, hasInfExp_attChr_mu hL t' hj _ τ⟩) a ha b hb f hf

end GlobalTheory.RowRealEq
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.LatOfHasLoc

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField



theorem mem_latGrp_of_hasLoc : Big fun {D} _ _ _ _ _ _ _ _ _ _ _ ch => ∀ t, ∀ j, 1 ≤ j → ∀ (hj : j ≤ D.R.m)
    (x : GA D (ch.G.V (.grid D.R.m j)))
    (g : ∀ w : locPl ch.G t, GL (Fin ((locGrid ch.G t w.1).rank (D.R.m, j))) (Kw w.1)),
    HasLoc t ch.S.B hj x g → (∀ w, g w ∈ givenLevel ch.G t w.1 (D.R.m, j)) → x ∈ latGrp ch.G j := by
  refine ⟨0, fun _ _ _ => ⟨0, fun D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F hS ch _ _ => ?_⟩⟩
  intro t j h1 hj x g hx hg
  obtain ⟨e, he, hsupp, hloc⟩ := hx
  have hm : 1 ≤ D.R.m := by have := D.R.two_le_m; omega
  have e0 : infPart D e = 0 := (GlobalTheory.FunObj.Comparison₂.cpt_idemSum he).1
  have e0' : infPart D (cA D e) = 0 := GlobalTheory.PlaceDatum.infPart_cA e0
  refine ⟨GlobalTheory.LevelCut.mem_GfC_of _ x fun i k => ?_, ?_⟩
  · rw [← hsupp i k, map_mul, map_add (f := _), e0, e0', add_zero, zero_mul]
  · have hl : ∀ (w : Pl D.host.E) (X : ℕ × ℕ), 1 ≤ X.1 → 1 ≤ X.2 →
        givenLevel ch.G t w X = GlobalTheory.SplitWeil.KO (Kw w) _ := by
      rintro w ⟨_ | a, _ | b⟩ h h'
      · omega
      · simp at h
      · simp at h'
      · rfl
    have hβ : IsFrame (ch.S.B.β D.R.m j) (ch.G.Λ (.grid D.R.m j)) := ch.S.B.isFrame_β hS.core.lev le_rfl hj
    have hsd : IsSelfDualC _ (ch.G.Λ (.grid D.R.m j)) :=
      (ch.G.isV (X := .grid D.R.m j) ⟨le_rfl, hj⟩ fun k h => by
        have := (Node.grid.inj h).1; omega).sd
    set c : Lev.EAf D := toEAf D (e + cA D e) with hc
    have hX : (Lev.finE (ch.G.V (.grid D.R.m j)) x).val =
        c • (Lev.finE (ch.G.V (.grid D.R.m j)) x).val + (1 - c) • (1 : Matrix _ _ (Lev.EAf D)) := by
      have hM : (Lev.finE (ch.G.V (.grid D.R.m j)) x).val = (mt _ x).map (toEAf D) := rfl
      rw [hM]
      ext i k
      have h0 := congrArg (toEAf D) (hsupp i k)
      rw [map_mul, Matrix.sub_apply, map_sub] at h0
      simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.map_apply]
      by_cases hik : i = k
      · subst hik
        simp only [Matrix.one_apply_eq, map_one] at h0 ⊢
        rw [← hc] at h0
        linear_combination -h0
      · simp only [Matrix.one_apply_ne hik, map_zero, sub_zero, mul_zero, add_zero] at h0 ⊢
        exact h0.symm
    have key := GlobalTheory.FunObj.LevRowSucc.prodLev_inf_UA (V := ch.G.V (.grid D.R.m j)) (Λ := ch.G.Λ (.grid D.R.m j))
      (β := ch.S.B.β D.R.m j) hβ hsd (locPl ch.G t) (n' := fun w => (locGrid ch.G t w.1).rank (D.R.m, j))
      (fun w => rank_vertex ch.G t w.1 (X := (D.R.m, j)) ⟨le_rfl, hj⟩) (fun w => GlobalTheory.SplitWeil.KO (Kw w.1) _) fun _ => rfl
    have hmax : Lev.finE (ch.G.V (.grid D.R.m j)) x ∈ ch.G.levMax (.grid D.R.m j) := by
      rw [GridData.levMax, ← key]
      refine Subgroup.mem_inf.2 ⟨Subgroup.mem_inf.2 ⟨Subgroup.mem_iInf.2 fun w => ?_,
        Subgroup.mem_iInf.2 fun w' => Subgroup.mem_iInf.2 fun hw' => ?_⟩, GlobalTheory.LevSplit.finE_mem_UA _ x⟩
      · rw [Subgroup.mem_comap, hloc w]
        have := hg w
        rw [hl w.1 (D.R.m, j) hm h1] at this
        exact this
      · rw [Subgroup.mem_comap, (GlobalTheory.OffPartLattice.inBasis_mix (ch.S.B.β D.R.m j) _ _ c hX w').1
          (GlobalTheory.OffPartLattice.cpt_pair_zero (ch.G.V (.grid D.R.m j)) he w' hw')]
        exact one_mem _
    exact hmax

end GlobalTheory.LatOfHasLoc
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.SplitFlip GlobalTheory.SplitWeil

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.RowVal

theorem givenLevel_inner {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (t : T) (w : Pl D.host.E) :
    ∀ p : ℕ × ℕ, 1 ≤ p.1 → 1 ≤ p.2 → givenLevel G t w p = KO (Kw w) _ := by
  rintro ⟨_ | a, _ | b⟩ h1 h2
  · simp at h1
  · simp at h1
  · simp at h2
  · rfl

theorem oneAt : Big fun ch => OneAt ch := by
  refine ⟨0, fun ε CF _ => ⟨0, fun D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F s ch hch _ => ?_⟩⟩
  intro t Φ β hβ w hw0 i
  have hL : R.toLevCh.Is A.μ0 := s.core.lev
  have hde := GlobalTheory.FlipIntegrand.pde_ne_q_of_setting s
  have hc : ∀ P ∈ R.toLevCh.Q t, ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal := hch.guard t
  have hT := isTensor_Tflip hL ch.W ch.S.B t Φ hde hc w.2
  have hm : 0 < D.R.m := by have := D.R.two_le_m; omega
  have hcond : HasConductor (psiAt ch.W w.1) 1 :=
    (((Good.locGrid_isGood hL ch.G ch.W t hde hc).1 w.1 w.2).square 0 hm 0 hm).cond
  have hce : depthAt ch.G w.1 = cosExp ch.G w.1 := by
    have e : 1 ≤ cosExp ch.G w.1 := by
      classical
      unfold cosExp
      rw [if_pos hw0]
      exact ch.G.pl.depth_pos _ _
    rw [depthAt, max_eq_left e]
  rw [hce] at hT
  haveI := (isUnitVol_unitVol w.1).1
  have hJ : ∀ j, 0 < j → j < (locGrid ch.G t w.1).m →
      givenLevel ch.G t w.1 ((locGrid ch.G t w.1).m, j) = KO (Kw w.1) _ := fun j hj hj' =>
    givenLevel_inner ch.G t w.1 _ (by change 1 ≤ D.R.m; omega) hj
  have key := OneCosetProof.oneCoset_of_isTensor (ν := unitVol w.1) one_le_sLen hcond hT hJ
  have hk : keepAt ch.G w.1 = false := by
    classical
    unfold keepAt
    simp [hw0]
  have hβw := hβ w
  rw [hk] at hβw
  exact key (β w) hβw i

end GlobalTheory.RowVal
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.RowVal

theorem isIdemSum_unique {D : D7} {P : Finset (Formalism.L2.DIV.Pl D.host.E)} {e e' : AE D}
    (he : Formalism.IndefR.Datum.IsIdemSum e P) (he' : Formalism.IndefR.Datum.IsIdemSum e' P) : e = e' := by
  obtain ⟨⟨es, hes, rfl⟩, -⟩ := he
  obtain ⟨⟨es', hes', rfl⟩, -⟩ := he'
  exact Finset.sum_congr rfl fun PP hPP =>
    Formalism.IndefR.Fin.idemAt_eq_split (Formalism.IndefR.Fin.idemAt_split (hes PP hPP)) (hes PP hPP) (hes' PP hPP)

theorem suppAt_mul_of {D : D7} {V : HSp D} {e : AE D} {a b : GA D V} (ha : SuppAt e V a) (hb : SuppAt e V b) :
    SuppAt e V (a * b) := by
  intro i j
  have hab : mt V (a * b) = mt V a * mt V b := rfl
  have hm : mt V (a * b) - 1 = (mt V a - 1) * mt V b + (mt V b - 1) := by
    rw [hab]; noncomm_ring
  rw [hm, Matrix.add_apply, Matrix.mul_apply, mul_add, Finset.mul_sum, hb i j]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← mul_assoc, ha i k]

theorem hasLoc_mul : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (t : T) (B : Frames G) {j : ℕ}
    (hj : j ≤ D.R.m) (x y : GA D (G.V (.grid D.R.m j)))
    (g g' : ∀ w : locPl G t, GL (Fin ((locGrid G t w.1).rank (D.R.m, j))) (Kw w.1)), HasLoc t B hj x g → HasLoc t B hj y g' → HasLoc t B hj (x * y) (fun w => g w * g' w) := by
  intro D T L sc G t B j hj x y g g' ⟨e, he, hs, hg⟩ ⟨e', he', hs', hg'⟩
  rw [isIdemSum_unique he' he] at hs'
  refine ⟨e, he, suppAt_mul_of hs hs', fun w => ?_⟩
  rw [map_mul, map_mul, hg w, hg' w]

end GlobalTheory.RowVal
end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.L2.Pj Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.conjugate_baseLevel_of_howeUnramifiedCorrespondence : GlobalTheory.Hk3.HoweUnram → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T0 : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m} (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat3 D A3 T.Q.c.F) (F : Face3 D A3) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.toRealDat.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R.toRealDat i Unit (fun _ => A3.A.μ0)) (s : ℕ), A3.fam3.Ok3 s → A3.fam3.TypesSep3 → R.WeakCharacterisation F → R.toRealDat.ExAt → GlobalTheory.LiftRows.SourceLevelLawC R.toRealDat F.lv2 → GlobalTheory.LiftRows.InnerProductFormulaC R.toRealDat F.lv2 → GlobalTheory.LiftRows.FockCoefficientC R.toRealDat F.lv2 → GlobalTheory.LiftRows.FiniteZetaL R.toRealDat F.lv2 → (∀ i, R.phs i = 1) → IsStdChar D R.ψ (-1) → ∀ fw : FWTie T R.toRealDat κ v₀, BarTie fw → IoExt R.toRealDat → (∀ i, OMPins T R.toRealDat κ v₀ O i) → (∀ i, OneMapRow0 T R.toRealDat κ v₀ O i) → (∀ i, R.toRealDat.LUnif → PhaseTie T R.toRealDat κ v₀ O (fun i => (cj (twAt D.what₂.embLL A3.A.v0) (R.phs i))) i) → (∀ t, (A3.A.fam.R t).OkH ∧ (A3.rowI t).InertRationalAdjoint) → (∀ j t, (A3.A.fam.L j t).OkH ∧ (A3.liftI j t).InertRationalAdjoint) → R.PHecke F → R.PGUnit F → R.PGEquiv F → (R.toCx3 F).zs.InBlock → Formalism.IndefR.Rat.RowTest (R.toCx3 F) → Formalism.IndefR.Rat.LiftTest (R.toCx3 F) → Formalism.IndefR.Rat.LiftTestB (R.toCx3 F) false → (∀ hW, HeckeIntertwiningLifts A3 (R.toCx3 F) hW → U2.OntoC A3 (R.toCx3 F) F.P0 F.ψ0 F.P1 F.ψ1 hW) → 0 < R.kap → (∀ i t p, 0 < R.lam3 i t p A3.A.v0) → R.toRealDat.LUnif → R.PLevW F → R.PThmA → (R.toCx3 F).PartsW false → (R.toCx3 F).GalD F.cr false := by
  first | exact @GlobalTheory.ScalConjRow.galD_of_inputs | exact GlobalTheory.ScalConjRow.galD_of_inputs | (intros; apply GlobalTheory.ScalConjRow.galD_of_inputs <;> assumption)
end
