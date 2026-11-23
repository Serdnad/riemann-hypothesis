module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.UnitaryGaloisFamilies.IrrCaseT
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle053
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalFilDR
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle287
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.ReduceModChar

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp
open UpperTheory.V.Af UpperTheory.V.Af.Gu UpperTheory.V.Z.Win UpperTheory.V.Z.Win.Gu

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem tw_sumList {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w} (s : ℝ) (L : List (WD h)) :
    (sumList L).lpTw s = sumList (L.map fun x => x.lpTw s) := by
  induction L with
  | nil =>
    change (WD.lpZero (h := h)).lpTw s = WD.lpZero (h := h)
    rw [WD.lpZero, WD.lpTw_mk]
    exact WD.sound ⟨.refl _ _, fun _ _ => Subsingleton.elim _ _, fun _ => Subsingleton.elim _ _⟩
  | cons x L ih =>
    change (x.lpSum (sumList L)).lpTw s = (x.lpTw s).lpSum (sumList (L.map fun x => x.lpTw s))
    rw [WD.lpTw_sum, ih]

theorem UpperTheory.V.Z.Win.Gu.recTotT :
    ProdT → SpehT → RecTotT := by
  intro hProd hSpeh E Ω _ _ _ _ _ _ n c a d hn P w ρ σ hpos hP hS τ e A h rc hrc
  have h1 := hProd E Ω n c (fun i => d i * a i) hn w σ (fun i => (hS i).2.1) τ e A h rc hrc
  have h2 : ∀ i, rc (cl (σ i)) = sumList ((List.range (d i)).map fun k : ℕ =>
      (rc (cl (ρ i))).lpTw (((d i : ℝ) - 1) / 2 - k)) := fun i =>
    hSpeh E Ω (a i) (d i) (P i) w (ρ i) (σ i) (hpos i).1 (hpos i).2 (hP i) (hS i).1 (hS i).2.2 A h rc hrc
  have h3 : rc (algNorm τ) = (rc (cl τ)).lpTw ((1 - (n : ℝ)) / 2) := by
    obtain ⟨_, _, L⟩ := hrc
    exact L.nu _ _
  rw [h3, h1, tw_sumList, List.map_ofFn]
  refine congrArg sumList (congrArg List.ofFn (funext fun i => ?_))
  rw [Function.comp_apply, h2, tw_sumList, List.map_map, List.ofFn_eq_map, ← List.map_coe_finRange_eq_range,
    List.map_map]
  refine congrArg sumList (List.map_congr_left fun k _ => ?_)
  simp only [Function.comp_apply, WD.lpTw_add]
  refine congrArg₂ WD.lpTw rfl ?_
  simp only [ex]
  push_cast
  ring
end

section

open UpperTheory.V.Af UpperTheory.V.Af.Gu UpperTheory.V.Z.Win UpperTheory.V.Z.Win.Gu
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.UnitaryBC

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.V.Z.Win.Gu.sumFamG :
    SumTwoG → SumRed → SumFamG := by
  intro h2 hred E Ω _ _ _ _ _ l _ ι c hc
  obtain ⟨c, rfl⟩ : ∃ c', c = c' + 1 := ⟨c - 1, by omega⟩
  clear hc
  induction c with
  | zero =>
    intro N hN n hn r p HT H
    have hn' : N 0 = n := by simpa using hn
    subst hn'
    have e : ∀ w A h rc, sumList (List.ofFn fun i => p i w A h rc) = p 0 w A h rc := by
      intro w A h rc
      simp [sumList, WD.lpSum_zero]
    have e' : (fun τ => ∑ i, HT i τ) = HT 0 := by
      funext τ
      simp
    refine ⟨r 0, ⟨(H 0).cont, (H 0).ss, fun w hg => ?_, fun w A h rc hrc => ?_⟩, fun hi => ⟨rfl, fun i => ?_⟩⟩
    · rw [e']
      exact (H 0).ht w fun A h rc hrc => by
        have := hg A h rc hrc
        rwa [e] at this
    · rw [e]
      exact (H 0).par w A h rc hrc
    · obtain rfl : i = 0 := Subsingleton.elim (α := Fin 1) _ _
      exact hi
  | succ c ih =>
    intro N hN n hn r p HT H
    rw [Fin.sum_univ_succ] at hn
    subst hn
    obtain ⟨R, hR, -⟩ := ih (fun i => N i.succ) (fun i => hN i.succ) _ rfl (fun i => r i.succ) (fun i => p i.succ)
      (fun i => HT i.succ) (fun i => H i.succ)
    have hS := h2 E Ω l ι _ _ (r 0) R _ _ _ _ (H 0) hR
    have e : ∀ w A h rc, sumList (List.ofFn fun i => p i w A h rc) =
        (p 0 w A h rc).lpSum (sumList (List.ofFn fun i : Fin (c + 1) => p i.succ w A h rc)) := by
      intro w A h rc
      rw [List.ofFn_succ (f := fun i => p i w A h rc)]
      rfl
    have e' : (fun τ => ∑ i, HT i τ) = fun τ => HT 0 τ + ∑ i : Fin (c + 1), HT i.succ τ := by
      funext τ
      rw [Fin.sum_univ_succ]
    refine ⟨Formalism.MainNotions.SumRepresentations.At.sumRep (r 0) R, ⟨hS.cont, hS.ss, fun w hg => ?_, fun w A h rc hrc => ?_⟩, fun hi => ?_⟩
    · rw [e']
      exact hS.ht w fun A h rc hrc => by
        have := hg A h rc hrc
        rwa [e] at this
    · rw [e]
      exact hS.par w A h rc hrc
    · refine absurd hi (hred _ _ _ _ _ _ (hN 0) ?_)
      exact le_trans (hN (Fin.succ 0)) (Finset.single_le_sum (f := fun i : Fin (c + 1) => N i.succ) (fun _ _ => Nat.zero_le _) (Finset.mem_univ 0))
end

section

open UpperTheory.V.Af UpperTheory.V.Af.Gu UpperTheory.V.Z.Win UpperTheory.V.Z.Win.Gu

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N GlobalTheory.Pst

private theorem map_sum' {Γ : Type} [Group Γ] {k k' : Type} [CommRing k] [CommRing k'] {a b : ℕ}
    (f : k →+* k') (r₁ : Γ →* GL (Fin a) k) (r₂ : Γ →* GL (Fin b) k) :
    mapRep f (Formalism.MainNotions.SumRepresentations.At.sumRep r₁ r₂) = Formalism.MainNotions.SumRepresentations.At.sumRep (mapRep f r₁) (mapRep f r₂) := by
  ext g i j
  change f (Matrix.fromBlocks (r₁ g : Matrix (Fin a) (Fin a) k) 0 0 (r₂ g : Matrix (Fin b) (Fin b) k)
      (finSumFinEquiv.symm i) (finSumFinEquiv.symm j)) =
    Matrix.fromBlocks (mapRep f r₁ g : Matrix (Fin a) (Fin a) k') 0 0 (mapRep f r₂ g : Matrix (Fin b) (Fin b) k')
      (finSumFinEquiv.symm i) (finSumFinEquiv.symm j)
  rcases finSumFinEquiv.symm i with i | i <;> rcases finSumFinEquiv.symm j with j | j <;> simp [mapRep]

variable {l : ℕ} [Fact l.Prime] {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω]
  {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
  {Gw : Subgroup (Ω ≃ₐ[E] Ω)} {Bw : LocBridge l E Ω Gw O} {a b : ℕ}
  {r : ↥Gw →* GL (Fin a) (Om l)} {r' : ↥Gw →* GL (Fin b) (Om l)}

private theorem model_sum {L : FinExt l} {r₁ : ↥Gw →* GL (Fin a) ↥L.1} {r₂ : ↥Gw →* GL (Fin b) ↥L.1}
    (h₁ : IsModel Bw r L r₁) (h₂ : IsModel Bw r' L r₂) :
    IsModel Bw (Formalism.MainNotions.SumRepresentations.At.sumRep r r') L (Formalism.MainNotions.SumRepresentations.At.sumRep r₁ r₂) :=
  ⟨h₁.1, by rw [map_sum', h₁.2, h₂.2]⟩

private theorem dR_sum (h : IsdRAt (UpperTheory.V.Loc.PP l) Bw r) (h' : IsdRAt (UpperTheory.V.Loc.PP l) Bw r') :
    IsdRAt (UpperTheory.V.Loc.PP l) Bw (Formalism.MainNotions.SumRepresentations.At.sumRep r r') := by
  obtain ⟨L₁, r₁, m₁, -⟩ := id h
  obtain ⟨L₂, r₂, m₂, -⟩ := id h'
  have l₁ : L₁.1 ≤ (supExt L₁ L₂).1 := le_sup_left
  have l₂ : L₂.1 ≤ (supExt L₁ L₂).1 := le_sup_right
  have n₁ := m₁.enlarge l₁
  have n₂ := m₂.enlarge l₂
  exact ⟨_, _, model_sum n₁ n₂, (GlobalTheory.T.sumRep_deRham_iff_and_multiplicity_add l _ _ (UpperTheory.V.Loc.tiedP l) E Ω Gw O Bw _ a b _ _).1.2
    ⟨(n₁.isdRAt_iff _).1 h, (n₂.isdRAt_iff _).1 h'⟩⟩

private theorem jumps_sum {τ : E →+* Om l} {J J' : Multiset ℤ}
    (h : IsJumpsAt (UpperTheory.V.Loc.PP l) Bw r τ J) (h' : IsJumpsAt (UpperTheory.V.Loc.PP l) Bw r' τ J') :
    IsJumpsAt (UpperTheory.V.Loc.PP l) Bw (Formalism.MainNotions.SumRepresentations.At.sumRep r r') τ (J + J') := by
  obtain ⟨L₁, r₁, m₁, d₁, τ₁, t₁, -⟩ := id h
  obtain ⟨L₂, r₂, m₂, d₂, -⟩ := id h'
  have l₁ : L₁.1 ≤ (supExt L₁ L₂).1 := le_sup_left
  have l₂ : L₂.1 ≤ (supExt L₁ L₂).1 := le_sup_right
  have n₁ := m₁.enlarge l₁
  have n₂ := m₂.enlarge l₂
  have t : IsInduced Bw τ (LL' := supExt L₁ L₂) ((IntermediateField.inclusion l₁).comp τ₁) := t₁
  have S := GlobalTheory.T.sumRep_deRham_iff_and_multiplicity_add l _ _ (UpperTheory.V.Loc.tiedP l) E Ω Gw O Bw _ a b
    (mapRep (IntermediateField.inclusion l₁).toRingHom r₁) (mapRep (IntermediateField.inclusion l₂).toRingHom r₂)
  refine ⟨_, _, model_sum n₁ n₂, S.1.2 ⟨(n₁.isdRAt_iff _).1 ⟨_, _, m₁, d₁⟩, (n₂.isdRAt_iff _).1 ⟨_, _, m₂, d₂⟩⟩,
    _, t, fun c => ?_⟩
  rw [S.2, ← h.count_eq _ n₁ t, ← h'.count_eq _ n₂ t, Multiset.count_add, Nat.cast_add]

end

theorem UpperTheory.V.Z.Win.Gu.sumHTAt :
    SumHTAt := by
  intro E Ω _ _ _ _ _ l _ a b r r' _ _ HT HT' w H H' A hA O _ _ _ Bw hj
  obtain ⟨d, J⟩ := H A hA O Bw hj
  obtain ⟨d', J'⟩ := H' A hA O Bw hj
  have e : (Formalism.MainNotions.SumRepresentations.At.sumRep r r').comp (ReciprocityTheory.Gal.Dec (F := E) A).subtype =
      Formalism.MainNotions.SumRepresentations.At.sumRep (r.comp (ReciprocityTheory.Gal.Dec (F := E) A).subtype) (r'.comp (ReciprocityTheory.Gal.Dec (F := E) A).subtype) := by
    ext g i j
    rfl
  rw [e]
  exact ⟨dR_sum d d', fun τ L τ' t => jumps_sum (J τ L τ' t) (J' τ L τ' t)⟩
end
