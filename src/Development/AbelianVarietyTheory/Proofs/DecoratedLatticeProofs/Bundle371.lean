module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle022
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle328
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.OmVacuumEqSplitFacSmulSum
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle306
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle322
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PlacewiseToAdelicDecompositionForall
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle138
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle552
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergCombinationDisjointPlacesCommuteVacua
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle330
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IdempotentMulEntryEqZeroOfCutInverse
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualSplitComponentIsLatticeStabilizerEq
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PlacesToAdeles
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle343
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
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CombAtSingleZero
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiStarOfMid
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.UnitRatio

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.LocMod GlobalTheory.SplitWeil ValuativeRel

noncomputable section

namespace GlobalTheory.TensorLatO

theorem isSBHalf_tensorAt_of_bounds {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (p : Place D k) {S T : HSp D} {Y Y' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y']
    [DecidableEq Y'] (FS : GlobalTheory.LocMod.Frame k S.rank Y') (FT : GlobalTheory.LocMod.Frame k T.rank Y) (L : AddSubgroup (WO S T))
    (e : AE D) (he : e * p.e = 0) (hMap : ∀ u ∈ L, u.map (fun a => p.e * a) ∈ L)
    (A B : ℕ) (hA : 0 < A) (hB : 0 < B)
    (hAL : ∀ X : Matrix Y Y' k, (∀ r q, X r q ∈ 𝒪[k]) → A • p.up FS FT X ∈ L)
    (hBL : ∀ u ∈ L, ∀ r q, (B : k) * p.down FS FT u r q ∈ 𝒪[k])
    (Φ : WO S T → ℂ) (hΦ : IsSBHalf e L Φ) (Ψ : Matrix Y Y' k → ℂ) (hΨ : Ψ ∈ SB (Matrix Y Y' k)) :
    IsSBHalf (e + p.e) L (p.tensorAt FS FT Φ Ψ) := by
  classical
  unfold IsSBHalf at hΦ ⊢
  obtain ⟨hΦs, kΦ, hkΦ, hΦi, hΦl⟩ := hΦ
  obtain ⟨N, hN, hΨi, hΨl⟩ := GlobalTheory.SBUnif.uniform k Y Y' Ψ hΨ
  have hud : ∀ u : WO S T, p.up FS FT (p.down FS FT u) = u.map (fun a => p.e * a) := by
    intro u
    unfold Place.down Place.up
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, FT.βγ, Matrix.one_mul, Matrix.mul_assoc, FS.βγ, Matrix.mul_one]
    ext i j
    exact p.ι_π _
  have hupn : ∀ (n : ℕ) (X : Matrix Y Y' k), p.up FS FT (n • X) = n • p.up FS FT X :=
    fun n X => map_nsmul (Witness.upH p FS FT) n X
  have hdownn : ∀ (n : ℕ) (u : WO S T), p.down FS FT (n • u) = n • p.down FS FT u :=
    fun n u => map_nsmul (Witness.downH p FS FT) n u
  have hsupp : ∀ t, p.tensorAt FS FT Φ Ψ t ≠ 0 →
      Φ (t - p.up FS FT (p.down FS FT t)) ≠ 0 ∧ Ψ (p.down FS FT t) ≠ 0 := fun t ht =>
    ⟨left_ne_zero_of_mul ht, right_ne_zero_of_mul ht⟩
  refine ⟨fun t ht => ?_, kΦ * (N * B * A), Nat.mul_pos hkΦ (Nat.mul_pos (Nat.mul_pos hN hB) hA),
    fun u hu hhu t => ?_, fun t ht => ?_⟩
  · obtain ⟨h1, -⟩ := hsupp t ht
    have hs := hΦs _ h1
    have hw := Witness.up_half p FS FT (p.down FS FT t)
    intro i j
    have a1 := hs i j
    have a2 := hw i j
    have e1 : t i j = (t - p.up FS FT (p.down FS FT t)) i j + p.up FS FT (p.down FS FT t) i j := by
      rw [Matrix.sub_apply, sub_add_cancel]
    rw [e1]
    linear_combination (1 - p.e) * a1 + (1 - e) * a2 +
      (p.up FS FT (p.down FS FT t) i j + (t - p.up FS FT (p.down FS FT t)) i j) * he
  · set X := p.down FS FT u with hX
    have hXL : p.up FS FT X ∈ L := by rw [hX, hud]; exact hMap u hu
    have hYi : ∀ r q, (((kΦ * A : ℕ) : k) • ((B : k) • X)) r q ∈ 𝒪[k] := fun r q => by
      rw [Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul]
      exact mul_mem (natCast_mem _ _) (hBL u hu r q)
    have hd : p.down FS FT (t + (kΦ * (N * B * A)) • u) = p.down FS FT t + (kΦ * (N * B * A)) • X := by
      rw [Witness.down_add, hdownn]
    have e3 : p.down FS FT t + (kΦ * (N * B * A)) • X =
        p.down FS FT t + (N : k) • (((kΦ * A : ℕ) : k) • ((B : k) • X)) := by
      congr 1
      rw [← Nat.cast_smul_eq_nsmul k, smul_smul, smul_smul]
      congr 1
      push_cast; ring
    set w : WO S T := (N * B * A) • (u - p.up FS FT X) with hw
    have e2 : t + (kΦ * (N * B * A)) • u - p.up FS FT (p.down FS FT t + (kΦ * (N * B * A)) • X) =
        (t - p.up FS FT (p.down FS FT t)) + kΦ • w := by
      rw [Witness.up_add, hupn, hw, smul_smul, nsmul_sub]
      abel
    have hwL : w ∈ L := nsmul_mem (sub_mem hu hXL) _
    have hwH : IsHalf e w := by
      intro i j
      rw [hw, hX, hud, Matrix.smul_apply, Matrix.sub_apply, Matrix.map_apply, nsmul_eq_mul]
      linear_combination ((N * B * A : ℕ) : AE D) * hhu i j - ((N * B * A : ℕ) : AE D) * u i j * he
    show Φ (t + (kΦ * (N * B * A)) • u - p.up FS FT (p.down FS FT (t + (kΦ * (N * B * A)) • u))) *
        Ψ (p.down FS FT (t + (kΦ * (N * B * A)) • u)) =
      Φ (t - p.up FS FT (p.down FS FT t)) * Ψ (p.down FS FT t)
    rw [hd, e2, e3, hΦi w hwL hwH, hΨi _ _ hYi]
  · obtain ⟨h1, h2⟩ := hsupp t ht
    have a1 := hΦl _ h1
    have a2 : A • p.up FS FT (N • p.down FS FT t) ∈ L := hAL _ fun r q => by
      rw [Matrix.smul_apply, nsmul_eq_mul]; exact hΨl _ h2 r q
    rw [hupn] at a2
    have e1 : (kΦ * (N * B * A)) • t = (N * B * A) • (kΦ • (t - p.up FS FT (p.down FS FT t))) +
        kΦ • (B • (A • (N • p.up FS FT (p.down FS FT t)))) := by
      rw [smul_smul, smul_smul, smul_smul, smul_smul, mul_comm (N * B * A) kΦ,
        show kΦ * B * A * N = kΦ * (N * B * A) by ring, ← nsmul_add, sub_add_cancel]
    rw [e1]
    exact add_mem (nsmul_mem a1 _) (nsmul_mem (nsmul_mem a2 B) kΦ)

end GlobalTheory.TensorLatO
end

noncomputable section

namespace GlobalTheory.TensorLatO

theorem isSBHalf_tensorAt_latO : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (M : Lat S) (M' : Lat T), IsSelfDualC S M → IsSelfDualC T M' → ∀ (P : LocPl ψ S T M M') (e : AE D), e * P.q.e = 0 → ∀ Φ : WO S T → ℂ, IsSBHalf e (latO S T (M : Set _) (M' : Set _) fun _ => True) Φ → ∀ Ψ ∈ SB (Matrix P.Y P.Y' P.k), IsSBHalf (e + P.q.e) (latO S T (M : Set _) (M' : Set _) fun _ => True) ((ofSplit P.q).tensorAt P.FS P.FT Φ Ψ) := by
  classical
  intro D ψ S T M M' hS hT P e he Φ hΦ Ψ hΨ
  set L := latO S T (M : Set (Fin S.rank → D.host.E)) (M' : Set (Fin T.rank → D.host.E)) fun _ => True with hL
  set q := P.q with hq
  have hee : q.e * q.e = q.e := q.split.1

  have hMap : ∀ u ∈ L, u.map (fun a => (ofSplit q).e * a) ∈ L := fun u hu => by
    have h := GlobalTheory.SplitScalar.idem_smul_mem (LS := (M : Set (Fin S.rank → D.host.E)))
      (LT := (M' : Set (Fin T.rank → D.host.E))) hee u hu
    convert h using 1
    ext i j
    rfl

  obtain ⟨N₀, hN₀, h₀⟩ := GlobalTheory.FinPl.RdInt.exists_nat_mul_mem_fin
    (Sum.elim (fun x : Fin T.rank × P.Y => P.FT.β x.1 x.2) (fun x : P.Y' × Fin S.rank => P.FS.γ x.1 x.2))
  obtain ⟨K, hK, hmul⟩ := GlobalTheory.PlaceDatum.exists_nsmul_mem_latO (S := S) (T := T)
    (GlobalTheory.FinPl.PlacesAdeles.selfDual_isFull _ _ hS)
    (GlobalTheory.FinPl.PlacesAdeles.selfDual_isFull _ _ hT)
  have hAL : ∀ X : Matrix P.Y P.Y' P.k, (∀ r q, X r q ∈ 𝒪[P.k]) →
      (K * (N₀ * N₀)) • (ofSplit q).up P.FS P.FT X ∈ L := by
    intro X hX
    have hent := GlobalTheory.FinPl.RdInt.entry_mem P.FT.β P.FS.γ (fun i a => h₀ (Sum.inl (i, a)))
      (fun a j => h₀ (Sum.inr (a, j))) X hX
    have hh : IsHalf q.e ((N₀ * N₀) • (ofSplit q).up P.FS P.FT X) := fun i j => by
      rw [Matrix.smul_apply, nsmul_eq_mul, mul_left_comm]
      exact congrArg _ (Witness.up_half (ofSplit q) P.FS P.FT X i j)
    have hui : ∀ i j, toEAf D (((N₀ * N₀) • (ofSplit q).up P.FS P.FT X) i j) ∈
        Formalism.L2.Herm.intAf D.host.F D.host.E := by
      intro i j
      have h1 : ((N₀ * N₀) • (ofSplit q).up P.FS P.FT X) i j =
          q.sec (((N₀ * N₀ : ℕ) : P.k) * (P.FT.β * X * P.FS.γ) i j) := by
        rw [← nsmul_eq_mul, map_nsmul]
        rfl
      rw [h1]
      exact GlobalTheory.PlaceCoord.toEAf_mem ((q.int_iff _).1 (hent i j))
    have h1 := hmul _ (GlobalTheory.PlaceDatum.infPart_of_half (GlobalTheory.PlaceCoord.infPart_split q.split) hh) hui
    rwa [mul_nsmul']

  obtain ⟨M₀, hM₀, hden⟩ := GlobalTheory.PlaceDatum.exists_den_latO (S := S) (T := T) hS.1.fg hT.1.fg
  obtain ⟨K₁, hK₁, h₁⟩ := GlobalTheory.FinPl.RdBound.exists_nat_mul_mem_family
    (fun x : P.Y × Fin T.rank => P.FT.γ x.1 x.2)
  obtain ⟨K₂, hK₂, h₂⟩ := GlobalTheory.FinPl.RdBound.exists_nat_mul_mem_family
    (fun x : Fin S.rank × P.Y' => P.FS.β x.1 x.2)
  have hBL : ∀ u ∈ L, ∀ i j, ((K₁ * M₀ * K₂ : ℕ) : P.k) * (ofSplit q).down P.FS P.FT u i j ∈ 𝒪[P.k] := by
    intro u hu i j
    have heu := GlobalTheory.SplitScalar.idem_smul_mem (LS := (M : Set (Fin S.rank → D.host.E)))
      (LT := (M' : Set (Fin T.rank → D.host.E))) hee u hu
    have hint : ∀ a b, (M₀ : P.k) * q.pr (u a b) ∈ 𝒪[P.k] := fun a b => by
      rw [q.int_iff]
      have h1 : q.sec ((M₀ : P.k) * q.pr (u a b)) = (M₀ : AE D) * (q.e • u) a b := by
        rw [← nsmul_eq_mul, map_nsmul, nsmul_eq_mul, q.sec_pr]
        rfl
      rw [h1]
      refine GlobalTheory.PlaceDatum.finPart_mem_of_toEAf ?_
      rw [RingHom.map_mul, map_natCast]
      exact hden _ heu a b
    change (_ : P.k) * (P.FT.γ * Matrix.map u q.pr * P.FS.β) i j ∈ 𝒪[P.k]
    rw [Matrix.mul_apply, Finset.mul_sum]
    refine sum_mem fun b _ => ?_
    rw [Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum]
    refine sum_mem fun a _ => ?_
    have e : ((K₁ * M₀ * K₂ : ℕ) : P.k) * (P.FT.γ i a * Matrix.map u q.pr a b * P.FS.β b j) =
        ((K₁ : P.k) * P.FT.γ i a) * ((M₀ : P.k) * q.pr (u a b)) * ((K₂ : P.k) * P.FS.β b j) := by
      rw [Matrix.map_apply]; push_cast; ring
    rw [e]
    exact mul_mem (mul_mem (h₁ (i, a)) (hint a b)) (h₂ (b, j))
  exact isSBHalf_tensorAt_of_bounds (ofSplit q) P.FS P.FT L e he hMap (K * (N₀ * N₀)) (K₁ * M₀ * K₂)
    (Nat.mul_pos hK (Nat.mul_pos hN₀ hN₀)) (Nat.mul_pos (Nat.mul_pos hK₁ hM₀) hK₂) hAL hBL Φ hΦ Ψ hΨ

end GlobalTheory.TensorLatO
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.LocMod GlobalTheory.MiS ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Fam

noncomputable section

namespace GlobalTheory.CollectComb

theorem foldr_comp_eq {ι X : Type} (c o : ι → X → X) (hc : ∀ a b, a ≠ b → ∀ x, c a (o b x) = o b (c a x)) :
    ∀ (l : List ι), l.Nodup → ∀ F : X,
      l.foldr (fun i g => c i (o i g)) F = l.foldr (fun i g => c i g) (l.foldr (fun i g => o i g) F) := by
  have hpast : ∀ (b : ι) (t : List ι), b ∉ t → ∀ x,
      o b (t.foldr (fun i g => c i g) x) = t.foldr (fun i g => c i g) (o b x) := by
    intro b t hb x
    induction t with
    | nil => rfl
    | cons a t ih =>
      have hab : a ≠ b := fun h => hb (h ▸ List.mem_cons_self)
      have hbt : b ∉ t := fun h => hb (List.mem_cons_of_mem _ h)
      simp only [List.foldr_cons]
      rw [← ih hbt, hc a b hab]
  intro l hl F
  induction l with
  | nil => rfl
  | cons a t ih =>
    rw [List.nodup_cons] at hl
    simp only [List.foldr_cons]
    rw [ih hl.2, hpast a t hl.1]

end GlobalTheory.CollectComb

theorem GlobalTheory.CollectComb.main : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (M : GlobalTheory.FinPl.Lat S) (M' : GlobalTheory.FinPl.Lat T), IsSelfDualC S M → IsSelfDualC T M' → ∀ (n : ℕ) (L : Fin n → GlobalTheory.SeeSaw.LocPl ψ S T M M'), (Function.Injective fun i => (L i).q.v) → ∀ F, (List.finRange n).foldr (fun i g => comb ψ S T (L i).e (comb ψ S T (L i).o g)) F = (List.finRange n).foldr (fun i g => comb ψ S T (L i).e g) ((List.finRange n).foldr (fun i g => comb ψ S T (L i).o g) F) := by
  intro D ψ hψ S T M M' hM hM' n L hinj F
  have hat : ∀ i, GlobalTheory.FinPl.CombAt (· = (L i).q.v) (L i).e ∧ GlobalTheory.FinPl.CombAt (· = (L i).q.v) (L i).o := fun i =>
    ⟨fun u hu => GlobalTheory.FinPl.SplitHalfSuppImp.mxAt_of_isHalf D _ (L i).q u ((L i).e_is.1 u hu),
     fun u hu => GlobalTheory.FinPl.SplitHalfSuppImp.mxAt_of_isHalf D _ (L i).q u ((L i).o_at u hu)⟩
  refine GlobalTheory.CollectComb.foldr_comp_eq (fun i g => comb ψ S T (L i).e g) (fun i g => comb ψ S T (L i).o g) ?_ _
    (List.nodup_finRange n) F
  intro a b hab x
  have hdisj : ∀ p, p = (L a).q.v → ¬ p = (L b).q.v := fun p ha hb => hab (hinj (ha.symm.trans hb))
  exact (GlobalTheory.DisjComb.main D ψ hψ S T _ _ hdisj).1 _ _ (hat a).1 (hat b).2 x
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LevelCut

variable {D : D7}

theorem tensor_prod_zero {F A B E : Type} [Field F] [CommRing A] [CommRing B] [CommRing E] [Algebra F A]
    [Algebra F B] [Algebra F E] (z : (A × B) ⊗[F] E)
    (h1 : Algebra.TensorProduct.map (AlgHom.fst F A B) (AlgHom.id F E) z = 0)
    (h2 : Algebra.TensorProduct.map (AlgHom.snd F A B) (AlgHom.id F E) z = 0) : z = 0 := by
  have key : ∀ z : (A × B) ⊗[F] E, z =
      (LinearMap.inl F A B).rTensor E (Algebra.TensorProduct.map (AlgHom.fst F A B) (AlgHom.id F E) z) +
      (LinearMap.inr F A B).rTensor E (Algebra.TensorProduct.map (AlgHom.snd F A B) (AlgHom.id F E) z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a e => simp [← TensorProduct.add_tmul]
    | add x y hx hy =>
      simp only [map_add (f := _)]
      rw [add_add_add_comm, ← hx, ← hy]
  rw [key z, h1, h2]; simp

theorem adele_zero (z : AE D) (h1 : infPart D z = 0) (h2 : finPart D z = 0) : z = 0 :=
  tensor_prod_zero (F := D.host.F) (A := Ainf D.host.F) (B := Af D.host.F) (E := D.host.E) z h1 h2

theorem mem_GfC_of (V : HSp D) (y : GA D V) (hy : ∀ i j, infPart D ((mt V y - 1) i j) = 0) : y ∈ GfC V := by
  show infHom V y = 1
  apply Units.ext
  change (mt V y).map (infPart D) = 1
  ext i j
  have := hy i j
  rw [Matrix.sub_apply, RingHom.map_sub, sub_eq_zero] at this
  rw [Matrix.map_apply, this]
  by_cases hij : i = j <;> simp [Matrix.one_apply, hij]

theorem eq_one_of_parts (V : HSp D) (y : GA D V) (h1 : y ∈ GfC V) (h2 : y ∈ GinfC V) : y = 1 := by
  have k1 : (mt V y).map (infPart D) = 1 := by
    have := congrArg Units.val (show infHom V y = 1 from h1)
    exact this
  have k2 : (mt V y).map (finPart D) = 1 := by
    have := congrArg Units.val (show finHom V y = 1 from h2)
    exact this
  apply GlobalTheory.SplitCut.mt_injective
  rw [GlobalTheory.SplitCut.mt_one]
  ext i j
  apply sub_eq_zero.mp
  apply adele_zero
  · rw [RingHom.map_sub, sub_eq_zero]
    exact congrFun (congrFun (k1.trans (Matrix.map_one (infPart D) (RingHom.map_zero _) (RingHom.map_one _)).symm) i) j
  · rw [RingHom.map_sub, sub_eq_zero]
    exact congrFun (congrFun (k2.trans (Matrix.map_one (finPart D) (RingHom.map_zero _) (RingHom.map_one _)).symm) i) j

theorem mem_GfC_of_grpAt (V : HSp D) (P : Pl D → Prop) (x : GA D V) (hx : x ∈ grpAt V P) : x ∈ GfC V := by
  refine mem_GfC_of V x fun i j => ?_
  have h := congrArg (fun y : GL (Fin V.rank) (AE D ⧸ idAt D P) => y.1 i j) (show _ = (1 : GL _ _) from hx)
  change Ideal.Quotient.mk (idAt D P) (mt V x i j) = _ at h
  have h2 : Ideal.Quotient.mk (idAt D P) (mt V x i j) =
      Ideal.Quotient.mk (idAt D P) ((1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) i j) := by
    rw [h, Units.val_one]; by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
  have h4 : (mt V x - 1) i j ∈ idAt D P := by
    rw [Matrix.sub_apply]; exact Ideal.Quotient.eq.mp h2
  exact (RingHom.mem_ker).mp (Ideal.mem_inf.mp h4).1

theorem mem_GfC_of_supp (V : HSp D) {w : Pl D} (e : AE D) (he : ∃ ε, IsPlaceIdem D w ε ∧ e + cA D e = algebraMap (AF D.host.F) (AE D) ε)
    (y : GA D V) (hy : SuppAt e V y) : y ∈ GfC V := by
  obtain ⟨ε, ⟨α, rfl, -⟩, hε⟩ := he
  have h0 : infPart D (e + cA D e) = 0 := by
    rw [hε]
    exact TensorProduct.zero_tmul _ _
  refine mem_GfC_of V y fun i j => ?_
  rw [← hy i j, RingHom.map_mul, h0, zero_mul]

end GlobalTheory.LevelCut

namespace GlobalTheory.LevelCut

variable {D : D7}

theorem entry_mem_of (V : HSp D) (I : Ideal (AE D)) (g : GA D V) (hg : g ∈ congGrp V I) (i j : Fin V.rank) :
    (mt V g - 1) i j ∈ I := by
  have h := congrArg (fun y : GL (Fin V.rank) (AE D ⧸ I) => y.1 i j) (show _ = (1 : GL _ _) from hg)
  change Ideal.Quotient.mk I (mt V g i j) = _ at h
  have h2 : Ideal.Quotient.mk I (mt V g i j) =
      Ideal.Quotient.mk I ((1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) i j) := by
    rw [h, Units.val_one]; by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
  rw [Matrix.sub_apply]; exact Ideal.Quotient.eq.mp h2

theorem mem_of_entry (V : HSp D) (I : Ideal (AE D)) (g : GA D V) (hg : ∀ i j, (mt V g - 1) i j ∈ I) :
    g ∈ congGrp V I := by
  show (Matrix.GeneralLinearGroup.map (Ideal.Quotient.mk I)) (matHom V g) = 1
  apply Units.ext
  ext i j
  change Ideal.Quotient.mk I (mt V g i j) = (1 : GL (Fin V.rank) (AE D ⧸ I)).1 i j
  rw [Units.val_one]
  have h2 : Ideal.Quotient.mk I (mt V g i j) =
      Ideal.Quotient.mk I ((1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) i j) :=
    Ideal.Quotient.eq.mpr (by rw [← Matrix.sub_apply]; exact hg i j)
  rw [h2]; by_cases hij : i = j <;> simp [Matrix.one_apply, hij]

theorem congGrp_le (V : HSp D) {I J : Ideal (AE D)} (h : I ≤ J) : congGrp V I ≤ congGrp V J :=
  fun g hg => mem_of_entry V J g fun i j => h (entry_mem_of V I g hg i j)

theorem idAt_le_idOff_compl (P Q : Pl D → Prop) (hPQ : ∀ w, Q w → ¬ P w) : idAt D P ≤ idOff D Q := by
  intro a ha
  unfold idAt at ha
  unfold idOff
  simp only [Submodule.mem_inf, Submodule.mem_iInf] at ha ⊢
  intro u
  exact ha.2 ⟨u.1, hPQ u.1 u.2⟩

end GlobalTheory.LevelCut

namespace GlobalTheory.LevelCut

theorem grpAt_eq_prod_local : ∀ {D : D7} {c : Comm D} {v : VCom c} {n : ℕ}, c.Is → v.Is → ∀ (G : Fin n → GLoc v), GPin G →
    ∀ (j' : ℕ), ∀ x ∈ grpAt (c.V j') (· ∈ v.gP), ∃ xs : Fin n → GA D (c.V j'),
      (∀ i, SuppAt (G i).q.e (c.V j') (xs i)) ∧ x = (List.ofFn xs).prod := by
  intro D c v n _ _ G hG j' x hx
  have hoff : x ∈ grpOff (c.V j') (fun w => w ∉ Set.range fun i => (G i).q.v) := by
    refine congGrp_le (c.V j') (idAt_le_idOff_compl _ _ fun w hw hP => hw ?_) hx
    obtain ⟨i, hi⟩ := (hG.places w).mp hP
    exact ⟨i, hi.symm⟩
  obtain ⟨a, ha, h, hsupp, hcomm, -, hxa, -⟩ := GlobalTheory.SplitCut.prod_of_trivOff D (c.V j') (Fin n) (fun i => (G i).q.v)
    (fun i => (G i).q.e) hG.inj (fun i => ⟨(G i).q.split, (G i).q.above⟩) x hoff
  have hperm : (Finset.univ.toList.map h).prod = (List.ofFn h).prod := by
    rw [List.ofFn_eq_map]
    refine List.Perm.prod_eq' ((List.perm_of_nodup_nodup_toFinset_eq (Finset.nodup_toList _) (List.nodup_finRange n)
      (by ext i; simp)).map h) ?_
    exact List.Pairwise.map _ (fun i i' hii => hcomm i i' hii) (Finset.nodup_toList _)
  refine ⟨h, hsupp, ?_⟩
  have hP : (List.ofFn h).prod ∈ GfC (c.V j') := by
    refine (GfC (c.V j')).list_prod_mem fun y hy => ?_
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hy
    exact mem_GfC_of_supp (c.V j') _ (G i).q.above (h i) (hsupp i)
  have hxf : x ∈ GfC (c.V j') := mem_GfC_of_grpAt _ _ x hx
  rw [hperm] at hxa
  have haf : a ∈ GfC (c.V j') := by
    have : a = x * ((List.ofFn h).prod)⁻¹ := by rw [hxa, mul_inv_cancel_right]
    rw [this]
    exact mul_mem hxf (inv_mem hP)
  rw [hxa, eq_one_of_parts _ a haf ha, one_mul]

end GlobalTheory.LevelCut
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.LocMod GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain ValuativeRel

noncomputable section

namespace GlobalTheory.FixedLevelIsolate

theorem foldr_extract {ι X : Type} [DecidableEq ι] (g : ι → X → X) (i : ι)
    (hc : ∀ a, a ≠ i → ∀ x, g a (g i x) = g i (g a x)) :
    ∀ (l : List ι) (x : X), i ∈ l → l.foldr g x = g i ((l.erase i).foldr g x) := by
  intro l x hi
  induction l with
  | nil => simp at hi
  | cons a t ih =>
    by_cases ha : a = i
    · subst ha
      simp
    · have hit : i ∈ t := by
        rcases List.mem_cons.1 hi with h | h
        · exact absurd h.symm ha
        · exact h
      have he : (a :: t).erase i = a :: t.erase i := by
        simp [ha]
      rw [he, List.foldr_cons, List.foldr_cons, ih hit, hc a ha]

variable {D : D7}

theorem latO_mono {S T : HSp D} (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E))
    {P P' : Pl D → Prop} (h : ∀ p, P p → P' p) : latO S T LS LT P ≤ latO S T LS LT P' := by
  apply AddSubgroup.closure_mono
  rintro w ⟨α, hα, hv, rest⟩
  exact ⟨α, hα, fun p hp => hv p fun hq => hp (h p hq), rest⟩

theorem vac_mono {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {LS : Lat S} {LT : Lat T} {P P' : Pl D → Prop}
    (h : ∀ p, P p → P' p) {f : WO S T → ℂ} (hf : Vac ψ S T LS LT P' f) : Vac ψ S T LS LT P f :=
  ⟨hf.1, fun u hu => hf.2.1 u (latO_mono _ _ h hu), fun e he u hu hh => hf.2.2 e he u (latO_mono _ _ h hu) hh⟩

theorem eg_combAt {c : Comm D} {v : VCom c} (G : GLoc v) (j : ℕ) (hj : j ≤ G.s) : CombAt (· = G.q.v) (G.eg j) := by
  intro u hu a b
  have h := (G.eg_is j (G.s - j) (by omega)).1 u hu a b
  exact (GlobalTheory.FinPl.FrameLat.idem_iff G.q _).2 h

end GlobalTheory.FixedLevelIsolate

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.LocMod GlobalTheory.StepData

theorem _root_.GlobalTheory.T.flat_fourierJacobi_to_bessel_column_mul_laws : ∀ (D : D7), GlobalTheory.FinPl.FlatLaws D → OmLoc D → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (p : Place D k) (ψ : AddChar (AF D.host.F) ℂ) (ψk : AddChar k Circle), p.IsChar ψ ψk → ∀ (σ : ℕ) (J : JacLev D (σ + 1)) (B : BesLev D σ) (st : StepFB ψ J B) (s : k), s ≠ 0 → ∀ (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c : ℕ) (G₀ : Frame k J.W₀.rank n') (FW : Frame k J.W.rank (n' ⊕ Fin (c + 1))) (FA : Frame k B.A.rank n) (F₀ : Frame k B.V₀.rank (n ⊕ Unit)) (FV : Frame k B.V.rank (n ⊕ Fin c)), p.IsJacFrame J s (-p.xi ^ 2 * p.hz B) G₀ FW → p.IsCoreFrame B (s * p.xi) FA F₀ → p.IsBesFrame B (s * p.xi) FA FV → ∀ Tm, p.IsModel ψ FW FV Tm → ∀ (r : n ⊕ Fin c) (q : n' ⊕ Fin (c + 1)), (∃ i, q = Sum.inr i ∧ i.val ≤ σ ∧ ¬ Free (σ + 1) (r, q)) → ∀ (b : k) (Φ Φ' : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)), (∀ t, Φ'.1 t = (ψk (b * (t r q - basePt c (0 : Matrix n n' k) r q)) : ℂ) * Φ.1 t) → flatFB st (Tm Φ') = flatFB st (Tm Φ) := by
  first | exact @GlobalTheory.FlatColLawFB.flatFB_mulcol | exact GlobalTheory.FlatColLawFB.flatFB_mulcol | (intros; apply GlobalTheory.FlatColLawFB.flatFB_mulcol <;> assumption)
end
