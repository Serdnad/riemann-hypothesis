module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.CrystallineCardinalities.UnitStep
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.CrystallineCardinalities.CjFacts
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.CrystallineCardinalities.DualCard
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.CrystallineCardinalities.OkFin
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.CrystallineCardinalities.Bundle001
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr UpperTheory.V.Z.J

namespace UpperTheory.V.Z.J

private def triG (A : Type) [CommRing A] : AddSubgroup (Matrix (Fin 3) (Fin 3) A) where
  carrier := {X | UpT X}
  add_mem' := fun {a b} ha hb i j h => by
    rw [Matrix.add_apply, ha i j h, hb i j h, add_zero]
  zero_mem' := fun _ _ _ => rfl
  neg_mem' := fun {a} ha i j h => by rw [Matrix.neg_apply, ha i j h, neg_zero]

private theorem triG_card (A : Type) [CommRing A] [Finite A] : Nat.card A ^ 6 ≤ Nat.card (triG A) := by
  classical
  let f : ({p : Fin 3 × Fin 3 // p.1 ≤ p.2} → A) → triG A := fun g =>
    ⟨fun i j => if h : i ≤ j then g ⟨(i, j), h⟩ else 0, by
      show UpT _
      intro i j hij
      simp [not_le.mpr hij]⟩
  have hf : Function.Injective f := by
    intro g g' hgg
    funext p
    have := congrArg (fun x : triG A => (x : Matrix (Fin 3) (Fin 3) A) p.1.1 p.1.2) hgg
    simpa [f, p.2] using this
  have h1 := Nat.card_le_card_of_injective f hf
  rw [Nat.card_fun] at h1
  have h6 : Nat.card {p : Fin 3 × Fin 3 // p.1 ≤ p.2} = 6 := by
    rw [Nat.card_eq_fintype_card]; decide
  rwa [h6] at h1

private def zcG {D N : Type} [Group D] [TopologicalSpace D] [AddCommGroup N] (ρ : Representation ℤ D N) :
    AddSubgroup (D → N) where
  carrier := Zc ρ
  add_mem' := fun {a b} ha hb => ⟨ha.1.add hb.1, fun s t => by
    simp only [Pi.add_apply, ha.2 s t, hb.2 s t, map_add (f := _)]; abel⟩
  zero_mem' := ⟨IsLocallyConstant.const 0, fun s t => by simp⟩
  neg_mem' := fun {a} ha => ⟨ha.1.neg, fun s t => by
    simp only [Pi.neg_apply, ha.2 s t, map_neg]; abel⟩

private theorem local_lower_triangular_cohomology (l : ℕ) [Fact l.Prime] (A : Type) [CommRing A] [Finite A] (D : Type) [Group D]
    [TopologicalSpace D] [IsTopologicalGroup D] (I : Subgroup D) (ε : D →* ℤ_[l]ˣ) (d k : ℕ) (hk : 0 < k)
    (hA : ∀ x : A, l ^ k • x = 0) (hLE : LE l D ε d) (hI : GenI l I d)
    (c : D → Matrix (Fin 3) (Fin 3) A → Matrix (Fin 3) (Fin 3) A)
    (ρ : Representation ℤ D (Matrix (Fin 3) (Fin 3) A)) (hc : ∀ s X, ρ s X = c s X) (ho : IsOpen (ρ.ker : Set D))
    (hT : ∀ s X, UpT X → UpT (c s X) ∧ ∀ i, c s X i i = X i i)
    (W : Set (D → Matrix (Fin 3) (Fin 3) A))
    (hW : ∀ z, z ∈ W ↔ IsLocallyConstant z ∧ (∀ s s', z (s * s') = z s + c s (z s')) ∧ (∀ s, UpT (z s)) ∧
      ∀ s ∈ I, ∀ i, z s i i = 0) :
    W.Finite ∧ Nat.card A ^ (6 + 3 * d) ≤ W.ncard := by
  classical
  have hAm : ∀ x : Matrix (Fin 3) (Fin 3) A, l ^ k • x = 0 := fun x => by
    ext i j; simp [hA]
  have hWZ : W ⊆ Zc ρ := fun z hz => by
    obtain ⟨h1, h2, -, -⟩ := (hW z).1 hz
    exact ⟨h1, fun s t => by rw [h2, hc]⟩
  have hWfin : W.Finite := ((hLE k hk _ ρ hAm ho).1).subset hWZ
  refine ⟨hWfin, ?_⟩
  have hmem : ∀ s (x : triG A), ρ s x.1 ∈ triG A := fun s x => by
    show UpT _
    rw [hc]; exact (hT s x.1 x.2).1
  let f : D → (triG A →+ triG A) := fun s =>
    { toFun := fun x => ⟨ρ s x.1, hmem s x⟩
      map_zero' := Subtype.ext (map_zero (ρ s))
      map_add' := fun x y => Subtype.ext (map_add (ρ s) x.1 y.1) }
  let ρ' : Representation ℤ D (triG A) :=
    { toFun := fun s => (f s).toIntLinearMap
      map_one' := LinearMap.ext fun x => Subtype.ext (by
        show ρ 1 x.1 = x.1
        rw [map_one]; rfl)
      map_mul' := fun s t => LinearMap.ext fun x => Subtype.ext (by
        show ρ (s * t) x.1 = ρ s (ρ t x.1)
        rw [map_mul]; rfl) }
  have hρ' : ∀ s (x : triG A), (ρ' s x).1 = ρ s x.1 := fun s x => rfl
  have hker' : IsOpen (ρ'.ker : Set D) := by
    refine Subgroup.isOpen_mono (fun s hs => ?_) ho
    rw [MonoidHom.mem_ker] at hs ⊢
    exact LinearMap.ext fun x => Subtype.ext (by rw [hρ', hs]; rfl)
  have hNk : ∀ x : triG A, l ^ k • x = 0 := fun x =>
    Subtype.ext (by rw [AddSubgroup.coe_nsmul, hAm]; rfl)
  obtain ⟨hZfin, hZcard⟩ := hLE k hk (triG A) ρ' hNk hker'
  have h0 : (0 : D → triG A) ∈ Zc ρ' := ⟨IsLocallyConstant.const 0, fun s t => by simp⟩
  have hpos : 0 < (Zc ρ').ncard := (Set.ncard_pos hZfin).mpr ⟨0, h0⟩
  have hHom : 0 < (HomMu l k ε ρ').ncard := by
    rcases Nat.eq_zero_or_pos (HomMu l k ε ρ').ncard with h | h
    · rw [hZcard, h, mul_zero] at hpos; exact absurd hpos (lt_irrefl 0)
    · exact h
  have hbig : Nat.card A ^ (6 + 6 * d) ≤ (Zc ρ').ncard := by
    rw [hZcard]
    calc Nat.card A ^ (6 + 6 * d) = (Nat.card A ^ 6) ^ (1 + d) := by
          rw [← pow_mul]; congr 1; ring
      _ ≤ Nat.card (triG A) ^ (1 + d) := Nat.pow_le_pow_left (triG_card A) _
      _ ≤ _ := Nat.le_mul_of_pos_right _ hHom
  let Z := zcG ρ'
  haveI : Finite Z := hZfin.to_subtype
  let p : Fin 3 → (triG A →+ A) := fun j =>
    { toFun := fun x => x.1 j j, map_zero' := rfl, map_add' := fun x y => rfl }
  have hp : ∀ z ∈ Z, IsLocallyConstant z ∧
      ∀ (j : Fin 3) (s s' : D), p j (z (s * s')) = p j (z s) + p j (z s') := by
    intro z hz
    have hz' : z ∈ Zc ρ' := hz
    refine ⟨hz'.1, fun j s s' => ?_⟩
    show (z (s * s')).1 j j = (z s).1 j j + (z s').1 j j
    rw [hz'.2 s s']
    show (z s).1 j j + (ρ s (z s').1) j j = _
    rw [hc, (hT s _ (z s').2).2 j]
  have hcut := wtCut l D I d k 3 A (triG A) hI hA Z inferInstance p hp
  have hZc : Nat.card Z = (Zc ρ').ncard := Nat.card_coe_set_eq (Zc ρ')
  have hSW : {z | z ∈ Z ∧ ∀ (j : Fin 3), ∀ s ∈ I, p j (z s) = 0}.ncard ≤ W.ncard := by
    refine Set.ncard_le_ncard_of_injOn (fun z s => (z s).1) ?_ ?_ hWfin
    · rintro z ⟨hz, hI0⟩
      have hz' : z ∈ Zc ρ' := hz
      rw [hW]
      refine ⟨hz'.1.comp _, fun s s' => ?_, fun s => (z s).2, fun s hs i => hI0 i s hs⟩
      show (z (s * s')).1 = (z s).1 + c s (z s').1
      rw [hz'.2 s s', ← hc]; rfl
    · intro z _ z' _ h
      funext s; exact Subtype.ext (congrFun h s)
  have hApos : 0 < Nat.card A ^ (3 * d) := pow_pos Nat.card_pos _
  refine Nat.le_of_mul_le_mul_right ?_ hApos
  calc Nat.card A ^ (6 + 3 * d) * Nat.card A ^ (3 * d) = Nat.card A ^ (6 + 6 * d) := by
        rw [← pow_add]; congr 1; ring
    _ ≤ (Zc ρ').ncard := hbig
    _ = Nat.card Z := hZc.symm
    _ ≤ _ := hcut
    _ ≤ W.ncard * Nat.card A ^ (3 * d) := Nat.mul_le_mul_right _ hSW

end UpperTheory.V.Z.J

theorem UpperTheory.V.Z.J.locLow :
    ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (D : Type) [Group D] [TopologicalSpace D] [IsTopologicalGroup D] [CompactSpace D] (I : Subgroup D) (ε : D →* ℤ_[l]ˣ) (d : ℕ) (t : D →* GL (Fin 3) O), (l : O) ≠ 0 → LE l D ε d → GenI l I d → TriRep t → ∀ k, 0 < k → (ZF (l := l) I k t).Finite ∧ Nat.card (Ok l O k) ^ (6 + 3 * d) ≤ (ZF (l := l) I k t).ncard := by
  intro l _ O _ _ _ _ _ D _ _ _ _ I ε d t hl hLE hI ht k hk
  obtain ⟨hf, -, hA, -⟩ := okFin l O hl
  obtain ⟨⟨ρ, hc, ho⟩, -, hT, -⟩ := cjFacts l O D t k hl ht
  haveI := hf k
  exact local_lower_triangular_cohomology l (Ok l O k) D I ε d k hk (hA k) hLE hI (cj k t) ρ hc ho
    (fun s X hX => ⟨(hT s X hX).1, (hT s X hX).2.1⟩) _ (fun _ => Iff.rfl)
end

section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr UpperTheory.V.Z.J

private theorem lower_triangular_absorbs_torsion (l : ℕ) [Fact l.Prime] (D : Type) [Group D] [TopologicalSpace D] (I : Subgroup D)
    (ε : D →* ℤ_[l]ˣ) (d k : ℕ) (hk : 0 < k) (hLE : LE l D ε d) (hG : GenI l I d)
    (A N : Type) [AddCommGroup A] [Finite A] [AddCommGroup N] [Finite N]
    (hA : ∀ x : A, l ^ k • x = 0) (hN : ∀ x : N, l ^ k • x = 0) (ρ : Representation ℤ D N)
    (hρ : IsOpen (ρ.ker : Set D)) (hc : Nat.card A ^ 5 ≤ Nat.card N) (e : N →+ A) (he : Function.Surjective e)
    (hε : ∀ s x, e (ρ s x) = (PadicInt.toZModPow k (ε s : ℤ_[l])).val • e x)
    (p : Fin 2 → N →+ A) (hp : ∀ j s x, p j (ρ s x) = p j x) :
    (Zc ρ).Finite ∧ Nat.card A ^ (6 + 3 * d) ≤ {z | z ∈ Zc ρ ∧ ∀ j, ∀ s ∈ I, p j (z s) = 0}.ncard := by
  classical
  haveI : NeZero (l ^ k) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  obtain ⟨hZfin, hZcard⟩ := hLE k hk N ρ hN hρ
  refine ⟨hZfin, ?_⟩
  have h0 : (0 : D → N) ∈ Zc ρ := ⟨IsLocallyConstant.const 0, fun s t => by simp⟩
  obtain ⟨hdA, hcA⟩ := dualCard l k A hA
  obtain ⟨hdN, -⟩ := dualCard l k N hN
  haveI := hdA
  haveI := hdN
  have hHom : Nat.card A ≤ (HomMu l k ε ρ).ncard := by
    rw [← hcA, ← Set.ncard_univ]
    refine Set.ncard_le_ncard_of_injOn (fun φ => φ.comp e) ?_ ?_ (Set.toFinite _)
    · intro φ _ s x
      show φ (e (ρ s x)) = _ * φ (e x)
      rw [hε, map_nsmul, nsmul_eq_mul, ZMod.natCast_zmod_val]
    · intro φ _ ψ _ h
      exact (AddMonoidHom.cancel_right he).1 h
  have hbig : Nat.card A ^ (6 + 5 * d) ≤ (Zc ρ).ncard := by
    rw [hZcard]
    calc Nat.card A ^ (6 + 5 * d) = (Nat.card A ^ 5) ^ (1 + d) * Nat.card A := by
          rw [← pow_mul, ← pow_succ]; congr 1; ring
      _ ≤ Nat.card N ^ (1 + d) * (HomMu l k ε ρ).ncard :=
          Nat.mul_le_mul (Nat.pow_le_pow_left hc _) hHom
  let Z : AddSubgroup (D → N) :=
    { carrier := Zc ρ
      add_mem' := fun {a b} ha hb => ⟨ha.1.add hb.1, fun s t => by
        simp only [Pi.add_apply, ha.2 s t, hb.2 s t, map_add (f := _)]; abel⟩
      zero_mem' := h0
      neg_mem' := fun {a} ha => ⟨ha.1.neg, fun s t => by
        simp only [Pi.neg_apply, ha.2 s t, map_neg]; abel⟩ }
  haveI : Finite Z := hZfin.to_subtype
  have hpZ : ∀ z ∈ Z, IsLocallyConstant z ∧
      ∀ (j : Fin 2) (s s' : D), p j (z (s * s')) = p j (z s) + p j (z s') := by
    intro z hz
    have hz' : z ∈ Zc ρ := hz
    refine ⟨hz'.1, fun j s s' => ?_⟩
    rw [hz'.2 s s', map_add (f := _), hp]
  have hcut := wtCut l D I d k 2 A N hG hA Z inferInstance p hpZ
  have hZc : Nat.card Z = (Zc ρ).ncard := Nat.card_coe_set_eq (Zc ρ)
  have hApos : 0 < Nat.card A ^ (2 * d) := pow_pos Nat.card_pos _
  refine Nat.le_of_mul_le_mul_right ?_ hApos
  calc Nat.card A ^ (6 + 3 * d) * Nat.card A ^ (2 * d) = Nat.card A ^ (6 + 5 * d) := by
        rw [← pow_add]; congr 1; ring
    _ ≤ (Zc ρ).ncard := hbig
    _ = Nat.card Z := hZc.symm
    _ ≤ _ := hcut

private def b0 (A : Type) [AddCommGroup A] (i : Fin 2) : Submodule ℤ (Matrix (Fin 3) (Fin 3) A) where
  carrier := {X | UpT X ∧ X i.castSucc i.castSucc = X i.succ i.succ}
  zero_mem' := ⟨fun _ _ _ => rfl, rfl⟩
  add_mem' := fun {a b} ha hb => ⟨fun x y h => by simp [ha.1 x y h, hb.1 x y h], by simp [ha.2, hb.2]⟩
  smul_mem' := fun c a ha => ⟨fun x y h => by simp [ha.1 x y h], by simp [ha.2]⟩

private theorem card_borel_torsion_lower_bound (A : Type) [AddCommGroup A] [Finite A] (i : Fin 2) : Nat.card A ^ 5 ≤ Nat.card (b0 A i) := by
  classical
  have hlt : i.castSucc < i.succ := Fin.castSucc_lt_succ
  have hcc : i.castSucc ≤ i.castSucc ∧ (i.castSucc, i.castSucc) ≠ (i.succ, i.succ) :=
    ⟨le_rfl, fun h => hlt.ne (congrArg Prod.fst h)⟩
  let F : ({p : Fin 3 × Fin 3 // p.1 ≤ p.2 ∧ p ≠ (i.succ, i.succ)} → A) → Matrix (Fin 3) (Fin 3) A :=
    fun g a b => if h : a ≤ b ∧ (a, b) ≠ (i.succ, i.succ) then g ⟨(a, b), h⟩
      else if (a, b) = (i.succ, i.succ) then g ⟨(i.castSucc, i.castSucc), hcc⟩ else 0
  have hF : ∀ g, F g ∈ b0 A i := by
    intro g
    refine ⟨fun a b hab => ?_, ?_⟩
    · have h1 : ¬ (a ≤ b ∧ (a, b) ≠ (i.succ, i.succ)) := fun h => absurd h.1 (not_le.mpr hab)
      have h2 : (a, b) ≠ (i.succ, i.succ) := by
        intro h
        simp only [Prod.mk.injEq] at h
        rw [h.1, h.2] at hab
        exact lt_irrefl _ hab
      simp only [F, dif_neg h1, if_neg h2]
    · have h3 : ¬ (i.succ ≤ i.succ ∧ (i.succ, i.succ) ≠ (i.succ, i.succ)) := fun h => h.2 rfl
      simp only [F, dif_pos hcc, dif_neg h3]
      simp
  let f : ({p : Fin 3 × Fin 3 // p.1 ≤ p.2 ∧ p ≠ (i.succ, i.succ)} → A) → b0 A i := fun g => ⟨F g, hF g⟩
  have hf : Function.Injective f := by
    intro g g' hgg
    funext ⟨⟨a, b⟩, hp⟩
    have hp' : a ≤ b ∧ (a, b) ≠ (i.succ, i.succ) := hp
    have := congrArg (fun x : b0 A i => (x : Matrix (Fin 3) (Fin 3) A) a b) hgg
    simp only [f, F, dif_pos hp'] at this
    exact this
  have h1 := Nat.card_le_card_of_injective f hf
  rw [Nat.card_fun] at h1
  have h5 : Nat.card {p : Fin 3 × Fin 3 // p.1 ≤ p.2 ∧ p ≠ (i.succ, i.succ)} = 5 := by
    rw [Nat.card_eq_fintype_card]; fin_cases i <;> decide
  rwa [h5] at h1

private def ent (A : Type) [AddCommGroup A] (i : Fin 2) (a b : Fin 3) : b0 A i →+ A where
  toFun X := X.1 a b
  map_zero' := rfl
  map_add' _ _ := rfl

private theorem ent_surj (A : Type) [AddCommGroup A] (i : Fin 2) : Function.Surjective (ent A i i.castSucc i.succ) := by
  intro a
  have hlt : i.castSucc < i.succ := Fin.castSucc_lt_succ
  refine ⟨⟨Matrix.single i.castSucc i.succ a, ?_, ?_⟩, ?_⟩
  · intro x y h
    rw [Matrix.single_apply, if_neg]
    rintro ⟨rfl, rfl⟩
    exact absurd h (not_lt.mpr hlt.le)
  · simp [Matrix.single_apply, hlt.ne, hlt.ne']
  · show Matrix.single i.castSucc i.succ a i.castSucc i.succ = a
    simp

theorem UpperTheory.V.Z.J.low0 :
    ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (D : Type) [Group D] [TopologicalSpace D] [IsTopologicalGroup D] [CompactSpace D] (I : Subgroup D) (ε : D →* ℤ_[l]ˣ) (d : ℕ) (t : D →* GL (Fin 3) O), (l : O) ≠ 0 → LE l D ε d → GenI l I d → TriRep t → ∀ i : Fin 2, UnitStep I ε t i → ∀ k, 0 < k → Nat.card (Ok l O k) ^ (6 + 3 * d) ≤ {z | z ∈ ZF (l := l) I k t ∧ ∀ s, z s i.castSucc i.castSucc = z s i.succ i.succ}.ncard := by
  classical
  have key : ∀ (R : Type) [AddCommGroup R] (i : Fin 2) (M : Matrix (Fin 3) (Fin 3) R),
      M i.castSucc i.castSucc = M i.succ i.succ →
      (∀ j : Fin 2, M (if i = 0 then j.succ else j.castSucc) (if i = 0 then j.succ else j.castSucc) = 0) →
      ∀ a, M a a = 0 := by
    intro R _ i M h1 h2 a
    have h20 := h2 0
    have h21 := h2 1
    fin_cases i <;> fin_cases a <;> simp_all
  intro l _ O _ _ _ _ _ D _ _ _ _ I ε d t hl hLE hI hT i hU k hk
  obtain ⟨hfin, -, hkill, -, -, hsmul, -⟩ := okFin l O hl
  haveI := hfin k
  obtain ⟨⟨ρ, hρ, hker⟩, hinv, hcj, -⟩ := cjFacts l O D t k hl hT
  have hAm : ∀ x : Matrix (Fin 3) (Fin 3) (Ok l O k), l ^ k • x = 0 := fun x => by
    ext a b; simp [hkill]
  have hN : ∀ x : b0 (Ok l O k) i, l ^ k • x = 0 := fun x =>
    Subtype.ext (by rw [Submodule.coe_smul_of_tower]; exact hAm x.1)
  have hmem : ∀ s (x : b0 (Ok l O k) i), ρ s x.1 ∈ b0 (Ok l O k) i := fun s x => by
    obtain ⟨hx1, hx2⟩ := x.2
    refine ⟨?_, ?_⟩
    · rw [hρ]; exact (hcj s x.1 hx1).1
    · rw [hρ, (hcj s x.1 hx1).2.1, (hcj s x.1 hx1).2.1]; exact hx2
  let f : D → (b0 (Ok l O k) i →+ b0 (Ok l O k) i) := fun s =>
    { toFun := fun x => ⟨ρ s x.1, hmem s x⟩
      map_zero' := Subtype.ext (map_zero (ρ s))
      map_add' := fun x y => Subtype.ext (map_add (ρ s) x.1 y.1) }
  let q : Fin 2 → Fin 3 := fun j => if i = 0 then j.succ else j.castSucc
  let p : Fin 2 → (b0 (Ok l O k) i →+ Ok l O k) := fun j => ent (Ok l O k) i (q j) (q j)
  refine le_trans (lower_triangular_absorbs_torsion l D I ε d k hk hLE hI (Ok l O k) (b0 (Ok l O k) i) (hkill k) hN
      { toFun := fun s => (f s).toIntLinearMap
        map_one' := LinearMap.ext fun x => Subtype.ext (by
          show ρ 1 x.1 = x.1
          rw [map_one]; rfl)
        map_mul' := fun s s' => LinearMap.ext fun x => Subtype.ext (by
          show ρ (s * s') x.1 = ρ s (ρ s' x.1)
          rw [map_mul]; rfl) }
      ?_ (card_borel_torsion_lower_bound _ i) (ent _ i i.castSucc i.succ) (ent_surj _ i) ?_ p ?_).2 ?_
  · refine Subgroup.isOpen_mono (fun s hs => ?_) hker
    rw [MonoidHom.mem_ker] at hs ⊢
    exact LinearMap.ext fun x => Subtype.ext (by
      show ρ s x.1 = x.1
      rw [hs]; rfl)
  · intro s x
    obtain ⟨hx1, hx2⟩ := x.2
    show ρ s x.1 i.castSucc i.succ = _ • x.1 i.castSucc i.succ
    rw [hρ, (hcj s x.1 hx1).2.2 i, hx2, sub_self, smul_zero, sub_zero, ← hsmul k,
      hU.1 s, mul_assoc, (hinv s).2 i.succ, mul_one]
  · intro j s x
    show ρ s x.1 (q j) (q j) = x.1 (q j) (q j)
    rw [hρ, (hcj s x.1 x.2.1).2.1]
  · refine Set.ncard_le_ncard_of_injOn (fun z s => (z s).1) ?_ ?_ ?_
    · rintro z ⟨hz, hI0⟩
      refine ⟨⟨hz.1.comp _, fun s s' => ?_, fun s => (z s).2.1, fun s hs a => ?_⟩, fun s => (z s).2.2⟩
      · show (z (s * s')).1 = (z s).1 + cj k t s (z s').1
        rw [hz.2 s s', ← hρ]; rfl
      · exact key _ i (z s).1 (z s).2.2 (fun j => hI0 j s hs) a
    · intro z _ z' _ h
      funext s; exact Subtype.ext (congrFun h s)
    · exact (hLE k hk _ ρ hAm hker).1.subset (fun z hz => ⟨hz.1.1, fun s s' => by rw [hz.1.2.1, hρ]⟩)
end
