module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle003
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeightTwoFormalGroupUnramifiedMultiplier
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PhiTopAgree
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
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open PowerSeries GlobalTheory.Honda Formalism.L2.Th1.CM

theorem _root_.GlobalTheory.T.heightTwo_formalGroup_unramified_multiplier : ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] [CompleteSpace K] (l : ℕ) (σ : K →+* K), Unr K l σ → ResAlg K → ∀ (f e : K⟦X⟧), IntLog f e → ∀ w : K, CoefLe 1 (Formalism.L2.Th1.C.mulBy f e w) → σ (σ w) = w → ‖σ w - w‖ = 1 → (∃ n, n ≤ l ^ 2 ∧ ‖coeff n (Formalism.L2.Th1.C.mulBy f e (l : K))‖ = 1) → ∃ ε : K, ‖ε‖ = 1 ∧ CoefLe 1 (e.subst (C ε * ltLog K l)) := by
  first | exact @GlobalTheory.Honda.heightTwo_unitTwist | exact GlobalTheory.Honda.heightTwo_unitTwist | (intros; apply GlobalTheory.Honda.heightTwo_unitTwist <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.SymBridge

noncomputable section
namespace GlobalTheory.SymBridge.EntryBases

section Frames
variable {k : Type*} [Field k] {ι ι' n n' : Type*} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c c' : ℕ}

def ordExp : n ⊕ Fin c → ℤ := Sum.elim (fun _ => 0) (fun i => (i.val : ℤ) + 1)

theorem typeFrame_bas_val (ϖ : kˣ) (ord : ι ≃ n ⊕ Fin c) :
    (typeFrame ϖ ord).bas.val = diagonal (fun y : n ⊕ Fin c => (ϖ : k) ^ ordExp y) := by
  ext (i | i) (j | j) <;> simp [typeFrame, embA, GlobalTheory.SplitFlip.diagGL, ordExp, diagonal, fromBlocks, Matrix.one_apply]
  split_ifs <;> simp [← zpow_natCast]

theorem typeFrame_bas_inv_val (ϖ : kˣ) (ord : ι ≃ n ⊕ Fin c) :
    ((typeFrame ϖ ord).bas⁻¹).val = diagonal (fun y : n ⊕ Fin c => (ϖ : k) ^ (-ordExp y)) := by
  ext (i | i) (j | j) <;> simp [typeFrame, embA, GlobalTheory.SplitFlip.diagGL, ordExp, diagonal, fromBlocks, Matrix.one_apply]
  split_ifs <;> simp [← zpow_natCast]

theorem typeFrame_coords_apply (ϖ : kˣ) (ord : ι ≃ n ⊕ Fin c) (ord' : ι' ≃ n' ⊕ Fin c')
    (x : Matrix (n ⊕ Fin c) (n' ⊕ Fin c') k) (a : ι) (b : ι') :
    (typeFrame ϖ ord).coords (typeFrame ϖ ord') x a b =
      (ϖ : k) ^ (ordExp (ord' b) - ordExp (ord a)) * x (ord a) (ord' b) := by
  simp only [LatFrame.coords, typeFrame_bas_val, typeFrame_bas_inv_val, submatrix_apply, diagonal_mul, mul_diagonal]
  dsimp only [typeFrame]
  rw [sub_eq_add_neg, zpow_add₀ (Units.ne_zero ϖ)]
  ring

end Frames

section Index

theorem fIdx_of_lt {κ c n v : ℕ} (h : v < κ) : LocE.fIdx κ c n v = v := by
  unfold LocE.fIdx; rw [if_pos h]

theorem fIdx_of_mid {κ c n v : ℕ} (h₁ : κ ≤ v) (h₂ : v < κ + c) : LocE.fIdx κ c n v = n + (v - κ) := by
  unfold LocE.fIdx; rw [if_neg (by omega), if_pos h₂]

theorem fIdx_of_ge {κ c n v : ℕ} (h : κ + c ≤ v) : LocE.fIdx κ c n v = v - c := by
  unfold LocE.fIdx; rw [if_neg (by omega), if_neg (by omega)]

theorem scE_of_lt {n v : ℕ} (ex : ℕ → ℕ) (h : v < n) : LocE.scE n ex v = 0 := by
  unfold LocE.scE; rw [if_pos h]

theorem scE_add (n i : ℕ) (ex : ℕ → ℕ) : LocE.scE n ex (n + i) = ex i := by
  unfold LocE.scE; rw [if_neg (by omega), Nat.add_sub_cancel_left]

theorem stdOrd_place {κ τ j c l n N : ℕ} (h : j + c = l) (hn : n = κ + j * (τ + 1))
    (e : XIx (Fin κ) (Fin τ) j ⊕ Fin c ≃ Fin N) (he : IsOrd (yPos xPos n) e) (a : Ix (Fin κ ⊕ Fin l) (Fin τ) j) :
    (e (stdOrd (Fin κ) (Fin τ) j c h a)).val = LocE.fIdx κ c n (zPos a) ∧
      ordExp (stdOrd (Fin κ) (Fin τ) j c h a) = LocE.scE n (fun i => i + 1) (LocE.fIdx κ c n (zPos a)) := by
  have hn' : n = κ + j * τ + j := by rw [hn]; ring
  rcases a with (i | ⟨i, hi⟩) | p
  · rw [stdOrd_eps, he]
    have hz : zPos (κ := κ) (τ := τ) (j := j) (.inl (.inl i) : Ix (Fin κ ⊕ Fin l) (Fin τ) j) = i.val := rfl
    rw [hz, fIdx_of_lt i.isLt, scE_of_lt _ (by omega)]
    exact ⟨rfl, rfl⟩
  · by_cases hic : i < c
    · have hs : stdOrd (Fin κ) (Fin τ) j c h (.inl (.inr ⟨i, hi⟩)) = .inr ⟨i, hic⟩ := standardOrderExtendedBasis_apply_low_block (Fin κ) (Fin τ) j c h ⟨i, hic⟩
      rw [hs, he]
      have hz : zPos (κ := κ) (τ := τ) (j := j) (.inl (.inr ⟨i, hi⟩) : Ix (Fin κ ⊕ Fin l) (Fin τ) j) = κ + i := rfl
      rw [hz, fIdx_of_mid (by omega) (by omega), Nat.add_sub_cancel_left, scE_add]
      exact ⟨rfl, by simp [ordExp]⟩
    · obtain ⟨m, rfl⟩ : ∃ m, i = c + m := ⟨i - c, by omega⟩
      have hs : stdOrd (Fin κ) (Fin τ) j c h (.inl (.inr ⟨c + m, hi⟩)) = .inl (.inl (.inr ⟨m, by omega⟩)) :=
        stdOrd_f (Fin κ) (Fin τ) j c h ⟨m, by omega⟩
      rw [hs, he]
      have hz : zPos (κ := κ) (τ := τ) (j := j) (.inl (.inr ⟨c + m, hi⟩) : Ix (Fin κ ⊕ Fin l) (Fin τ) j) = κ + (c + m) := rfl
      rw [hz, fIdx_of_ge (by omega), scE_of_lt _ (by omega)]
      exact ⟨by simp [yPos, xPos]; omega, rfl⟩
  · rw [stdOrd_d, he]
    have hp : p.1.val * τ + p.2.val < j * τ := by
      have h1 : p.1.val * τ + p.2.val < (p.1.val + 1) * τ := by rw [add_mul, one_mul]; omega
      exact lt_of_lt_of_le h1 (Nat.mul_le_mul_right τ p.1.isLt)
    have hz : zPos (κ := κ) (τ := τ) (j := j) (.inr p : Ix (Fin κ ⊕ Fin l) (Fin τ) j) = κ + l + p.1.val * τ + p.2.val := rfl
    rw [hz, fIdx_of_ge (by omega), scE_of_lt _ (by omega)]
    exact ⟨by simp [yPos, xPos]; omega, rfl⟩

end Index

section Main
variable {E k : Type} [Field E] [Field k]

theorem atN_val {N : ℕ} (v : Fin N → E) (i : Fin N) : Loc.atN v i.val = v i := by
  unfold Loc.atN; rw [dite_eq_left i.isLt]

theorem eN_val {N : ℕ} (i : Fin N) : Loc.eN E N i.val = Pi.single i 1 := by
  funext l; unfold Loc.eN; rw [Pi.single_apply]; simp [Fin.ext_iff]

theorem typeFrame_coords_toLoc (ι : E →+* k) (q : ℕ) (ϖ : kˣ) (hϖ : (ϖ : k) = ι (q : E))
    {κ τ l j c j' c' n N n' N' : ℕ} (h : j + c = l) (h' : j' + c' = l) (hn : n = κ + j * (τ + 1)) (hn' : n' = κ + j' * (τ + 1))
    (e : XIx (Fin κ) (Fin τ) j ⊕ Fin c ≃ Fin N) (e' : XIx (Fin κ) (Fin τ) j' ⊕ Fin c' ≃ Fin N')
    (he : IsOrd (yPos xPos n) e) (he' : IsOrd (yPos xPos n') e') (x : (Fin N' → E) →ₗ[E] (Fin N → E))
    (a : Ix (Fin κ ⊕ Fin l) (Fin τ) j) (b : Ix (Fin κ ⊕ Fin l) (Fin τ) j') :
    (typeFrame ϖ (stdOrd (Fin κ) (Fin τ) j c h)).coords (typeFrame ϖ (stdOrd (Fin κ) (Fin τ) j' c' h')) (toLoc ι e e' x) a b =
      ι (LocE.entB q κ c' n' c n (fun i => i + 1) (fun i => i + 1) x (zPos a) (zPos b)) := by
  rw [map_natCast] at hϖ
  rw [typeFrame_coords_apply]
  obtain ⟨ha1, ha2⟩ := stdOrd_place h hn e he a
  obtain ⟨hb1, hb2⟩ := stdOrd_place h' hn' e' he' b
  simp only [LocE.entB, toLoc]
  rw [← ha2, ← hb2, ← ha1, ← hb1, eN_val, atN_val, map_mul, map_zpow₀, map_natCast, ← hϖ]
  ring

end Main

theorem entries_agree : ∀ (E K k : Type) [Field E] [NumberField E] [StarRing E] [Field K] [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (P : HeightOneSpectrum (𝓞 E)) (q : ℕ) (ι : E →+* k) (σ₀ : K →+* ℂ) (ψ₀ : AddChar (𝓞 E ⧸ P.asIdeal) K) (χ : ℕ → (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) (s κ : ℕ) (S : SymData k s κ), Comparison₂ P q ι σ₀ ψ₀ χ S → ∀ (τ j c : ℕ) (h : j + c = s) (n' c' n c₂ : ℕ), n' = κ + j * (τ + 1) → n = κ + (j + 1) * (τ + 1) → c' = c + 1 → c₂ = c → ∀ (e' : XIx (Fin κ) (Fin τ) j ⊕ Fin (c + 1) ≃ Fin (n' + c')) (e : XIx (Fin κ) (Fin τ) (j + 1) ⊕ Fin c ≃ Fin (n + c₂)), IsOrd (yPos xPos n') e' → IsOrd (yPos xPos n) e → ∀ (x : (Fin (n' + c') → E) →ₗ[E] (Fin (n + c₂) → E)) (a : Ix (Fin κ ⊕ Fin (s + 1)) (Fin τ) (j + 1)) (b : Ix (Fin κ ⊕ Fin (s + 1)) (Fin τ) j), (typeFrame S.ϖ (stdOrd (Fin κ) (Fin τ) (j + 1) c (by omega))).coords (typeFrame S.ϖ (stdOrd (Fin κ) (Fin τ) j (c + 1) (by omega))) (toLoc ι e e' x) a b = ι (LocE.entB q κ c' n' c₂ n (fun i => i + 1) (fun i => i + 1) x (zPos a) (zPos b)) := by
  intro E K k _ _ _ _ _ _ _ _ P q ι σ₀ ψ₀ χ s κ S hT τ j c h n' c' n c₂ hn' hn hc' hc₂ e' e he' he x a b
  subst hc' hc₂
  exact typeFrame_coords_toLoc ι q S.ϖ hT.compl.unif _ _ hn hn' e e' he he' x a b

end GlobalTheory.SymBridge.EntryBases
end
end

section

open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.SymBridge

namespace GlobalTheory.PatPlaces

theorem zPos_surj {κ τ l j p : ℕ} (hp : p < κ + l + j * τ) :
    ∃ a : Ix (Fin κ ⊕ Fin l) (Fin τ) j, zPos a = p := by
  by_cases h1 : p < κ
  · exact ⟨.inl (.inl ⟨p, h1⟩), rfl⟩
  by_cases h2 : p < κ + l
  · exact ⟨.inl (.inr ⟨p - κ, by omega⟩), by simp only [zPos]; omega⟩
  · have hτ : 0 < τ := by
      rcases Nat.eq_zero_or_pos τ with h | h
      · subst h; simp at hp; omega
      · exact h
    have hq : p - (κ + l) < τ * j := by rw [mul_comm]; omega
    refine ⟨.inr (⟨(p - (κ + l)) / τ, Nat.div_lt_of_lt_mul hq⟩, ⟨(p - (κ + l)) % τ, Nat.mod_lt _ hτ⟩), ?_⟩
    have := Nat.div_add_mod' (p - (κ + l)) τ
    simp only [zPos]; omega

theorem symIdx_cases (κ ρ i : ℕ) :
    (i < κ ∧ symIdx κ ρ i = i + ρ) ∨ (κ ≤ i ∧ i < κ + ρ ∧ symIdx κ ρ i = i - κ) ∨ (κ + ρ ≤ i ∧ symIdx κ ρ i = i) := by
  unfold symIdx; split_ifs <;> omega

theorem block_div {r τ i u : ℕ} (hu : u < τ) : (r + i * τ + u - r) / τ = i := by
  have : r + i * τ + u - r = u + τ * i := by rw [mul_comm]; omega
  rw [this, Nat.add_mul_div_left _ _ (by omega), Nat.div_eq_of_lt hu, zero_add]

theorem pattern_to_places (F : Type) [Zero F] [One F] (κ ρ s τ j : ℕ) (R : ℕ → ℕ → F) :
    (∀ (a b : Ix (Fin κ ⊕ Fin (s + 1)) (Fin τ) j), ¬ FreeIx ρ a b → R (zPos a) (zPos b) = if a = b then 1 else 0) →
    ((∀ p', p' < κ + s + 1 → R p' p' = 1 ∧ ∀ p, p < κ + s + 1 + j * τ → p ≠ p' →
        (κ + s + 1 ≤ p ∨ symIdx κ ρ p' < symIdx κ ρ p ∨ (p' = κ + ρ ∧ p < κ)) → R p p' = 0) ∧
      (∀ p p', κ + s + 1 ≤ p' → p' < κ + s + 1 + j * τ → p < κ + s + 1 + j * τ →
        (p' - (κ + s + 1)) / τ < (p - (κ + s + 1)) / τ → R p p' = 0)) := by
  intro hR
  have key : ∀ a b : Ix (Fin κ ⊕ Fin (s + 1)) (Fin τ) j, a ≠ b → ¬ FreeIx ρ a b → R (zPos a) (zPos b) = 0 :=
    fun a b hab h => by rw [hR a b h, if_neg hab]
  refine ⟨fun p' hp' => ⟨?_, fun p hp hne hc => ?_⟩, fun p p' h1 h2 h3 h4 => ?_⟩
  · obtain ⟨b, rfl⟩ := zPos_surj (κ := κ) (τ := τ) (l := s + 1) (j := j) (p := p') (by omega)
    rw [hR b b ?_, if_pos rfl]
    rcases b with (i | i) | ⟨i, u⟩
    · simp [FreeIx, FreeTop]
    · simp [FreeIx, FreeTop]
    · simp only [zPos] at hp'; omega
  · obtain ⟨b, rfl⟩ := zPos_surj (κ := κ) (τ := τ) (l := s + 1) (j := j) (p := p') (by omega)
    obtain ⟨a, rfl⟩ := zPos_surj (κ := κ) (τ := τ) (l := s + 1) (j := j) (p := p) (by omega)
    refine key a b (fun h => hne (h ▸ rfl)) ?_
    have c1 := symIdx_cases κ ρ (zPos a)
    have c2 := symIdx_cases κ ρ (zPos b)
    rcases a with (i | i) | ⟨i, u⟩ <;> rcases b with (i' | i') | ⟨i', u'⟩ <;>
      simp only [zPos, FreeIx, FreeTop, Fin.lt_def, not_lt, not_false_eq_true] at hp' hp hne hc c1 c2 ⊢ <;> omega
  · obtain ⟨b, rfl⟩ := zPos_surj (κ := κ) (τ := τ) (l := s + 1) (j := j) (p := p') (by omega)
    obtain ⟨a, rfl⟩ := zPos_surj (κ := κ) (τ := τ) (l := s + 1) (j := j) (p := p) (by omega)
    rcases b with (i' | i') | ⟨i', u'⟩
    · simp only [zPos] at h1; omega
    · simp only [zPos] at h1; omega
    rcases a with (i | i) | ⟨i, u⟩
    · simp only [zPos] at h4; rw [show (i : ℕ) - (κ + s + 1) = 0 by omega, Nat.zero_div] at h4; exact absurd h4 (Nat.not_lt_zero _)
    · simp only [zPos] at h4; rw [show κ + (i : ℕ) - (κ + s + 1) = 0 by omega, Nat.zero_div] at h4; exact absurd h4 (Nat.not_lt_zero _)
    have e1 : κ + (s + 1) + (i' : ℕ) * τ + u' = κ + s + 1 + (i' : ℕ) * τ + u' := by omega
    have e2 : κ + (s + 1) + (i : ℕ) * τ + u = κ + s + 1 + (i : ℕ) * τ + u := by omega
    simp only [zPos] at h4
    rw [e1, e2, block_div u'.isLt, block_div u.isLt] at h4
    refine key _ _ (fun h => ?_) ?_
    · simp only [Sum.inr.injEq, Prod.mk.injEq] at h; rw [h.1] at h4; exact lt_irrefl _ h4
    · simp only [FreeIx, Fin.le_def, not_le]; exact h4

end GlobalTheory.PatPlaces
end

section

open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix
open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col

noncomputable section
namespace GlobalTheory.AtTypeExists
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.SymBridge

section Compl
variable {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E))

theorem intAt_iff (a : E) : IntAt P a ↔ P.valuation E a ≤ 1 := by
  constructor
  · rintro ⟨r, s, hs, e⟩
    have h1 : P.valuation E (algebraMap (𝓞 E) E s) = 1 := by
      rw [HeightOneSpectrum.valuation_of_algebraMap]
      exact (HeightOneSpectrum.intValuation_eq_one_iff).2 hs
    have h2 := congrArg (P.valuation E) e
    rw [map_mul, h1, one_mul] at h2
    rw [h2]
    exact HeightOneSpectrum.valuation_le_one P r
  · intro h
    obtain ⟨r, s, e⟩ := HeightOneSpectrum.exists_primeCompl_mul_eq_of_integer P a h
    exact ⟨r, s.1, s.2, by rw [mul_comm]; exact e⟩

theorem valuation_norm (h : ((qOf P : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2) :
    P.valuation E ((qOf P : ℕ) : E) = WithZero.exp (-1 : ℤ) := by
  have hm : ((qOf P : ℕ) : 𝓞 E) ∈ P.asIdeal := Ideal.absNorm_mem _
  have e : ((qOf P : ℕ) : E) = algebraMap (𝓞 E) E ((qOf P : ℕ) : 𝓞 E) := by simp
  rw [e, HeightOneSpectrum.valuation_of_algebraMap]
  have h1 := (HeightOneSpectrum.intValuation_le_pow_iff_mem P ((qOf P : ℕ) : 𝓞 E) 1).2 (by simpa using hm)
  have h2 := mt (HeightOneSpectrum.intValuation_le_pow_iff_mem P ((qOf P : ℕ) : 𝓞 E) 2).1 h
  have h0 : P.intValuation ((qOf P : ℕ) : 𝓞 E) ≠ 0 := fun h0 => h2 (by rw [h0]; exact zero_le')
  rw [← WithZero.exp_log h0] at h1 h2 ⊢
  rw [WithZero.exp_le_exp] at h1 h2
  congr 1
  push_cast at h1 h2
  omega

end Compl

theorem exists_ord : (∀ κ τ j : ℕ, ∃ e : XIx (Fin κ) (Fin τ) j ≃ Fin (κ + j * (τ + 1)), IsOrd xPos e) ∧ (∀ κ τ l j : ℕ, ∃ e : Ix (Fin κ ⊕ Fin l) (Fin τ) j ≃ Fin (κ + l + j * τ), IsOrd zPos e) ∧ (∀ (A : Type) (n c : ℕ) (pos : A → ℕ) (d : A ≃ Fin n), IsOrd pos d → ∃ e : A ⊕ Fin c ≃ Fin (n + c), IsOrd (yPos pos n) e) ∧ (∀ (A : Type) (n N : ℕ) (pos : A → ℕ) (d : A ≃ Fin n), IsOrd pos d → N = n + 1 → ∃ e : A ⊕ Unit ≃ Fin N, IsOrd (Sum.elim pos fun _ => N - 1) e) := by
  refine ⟨fun κ τ j => ?_, fun κ τ l j => ?_, fun A n c pos d hd => ?_, fun A n N pos d hd hN => ?_⟩
  · refine ⟨((Equiv.sumCongr finSumFinEquiv finProdFinEquiv).trans finSumFinEquiv).trans (finCongr (by ring)), ?_⟩
    rintro ((i | i) | ⟨i, i'⟩) <;> simp [xPos, finProdFinEquiv]
    ring
  · refine ⟨(Equiv.sumCongr finSumFinEquiv finProdFinEquiv).trans finSumFinEquiv, ?_⟩
    rintro ((i | i) | ⟨i, i'⟩) <;> simp [zPos, finProdFinEquiv]
    ring
  · refine ⟨(Equiv.sumCongr d (Equiv.refl _)).trans finSumFinEquiv, ?_⟩
    rintro (i | i)
    · simpa [yPos] using hd i
    · simp [yPos]
  · subst hN
    refine ⟨(Equiv.sumCongr d (Equiv.ofUnique Unit (Fin 1))).trans finSumFinEquiv, ?_⟩
    rintro (i | i)
    · simpa using hd i
    · simp

end GlobalTheory.AtTypeExists
end
end

section

open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.SymBridge

namespace GlobalTheory

theorem patOfPlaces : ∀ (F : Type) [Zero F] [One F] (κ ρ s τ j : ℕ) (R : ℕ → ℕ → F), ((∀ p', p' < κ + s + 1 → R p' p' = 1 ∧ ∀ p, p < κ + s + 1 + j * τ → p ≠ p' →
        (κ + s + 1 ≤ p ∨ symIdx κ ρ p' < symIdx κ ρ p ∨ (p' = κ + ρ ∧ p < κ)) → R p p' = 0) ∧
      (∀ p p', κ + s + 1 ≤ p' → p' < κ + s + 1 + j * τ → p < κ + s + 1 + j * τ →
        (p' - (κ + s + 1)) / τ < (p - (κ + s + 1)) / τ → R p p' = 0)) → (∀ (a b : Ix (Fin κ ⊕ Fin (s + 1)) (Fin τ) j), ¬ FreeIx ρ a b → R (zPos a) (zPos b) = if a = b then 1 else 0) := by
  intro F _ _ κ ρ s τ j R hR a b hab
  obtain ⟨h1, h2⟩ := hR
  have hA : ∀ (i : Fin j) (u : Fin τ), κ + (s + 1) + i.val * τ + u.val < κ + s + 1 + j * τ := by
    intro i u
    have hi : i.val + 1 ≤ j := i.2
    have hu := u.2
    have : (i.val + 1) * τ ≤ j * τ := Nat.mul_le_mul_right _ hi
    have e : (i.val + 1) * τ = i.val * τ + τ := by ring
    omega
  have hdiv : ∀ (i : Fin j) (u : Fin τ), (κ + (s + 1) + i.val * τ + u.val - (κ + s + 1)) / τ = i.val := by
    intro i u
    have hτ : 0 < τ := Nat.pos_of_ne_zero (fun h => by subst h; exact u.elim0)
    have e : κ + (s + 1) + i.val * τ + u.val - (κ + s + 1) = u.val + τ * i.val := by
      rw [Nat.mul_comm]; omega
    rw [e, Nat.add_mul_div_left _ _ hτ, Nat.div_eq_of_lt u.2, zero_add]
  rcases a with (i | i) | ⟨i, u⟩ <;> rcases b with (i' | i') | ⟨i', u'⟩
  ·
    simp only [FreeIx, FreeTop, not_lt, Fin.le_def] at hab
    simp only [zPos]
    by_cases h : i.val = i'.val
    · have : i = i' := Fin.ext h
      subst this
      rw [if_pos rfl]
      exact (h1 _ (by omega)).1
    · rw [if_neg (by intro e; simp only [Sum.inl.injEq] at e; exact h (congrArg Fin.val e))]
      refine (h1 _ (by omega)).2 _ (by omega) (by omega) (Or.inr (Or.inl ?_))
      simp only [symIdx]; split_ifs <;> omega
  ·
    simp only [FreeIx, FreeTop, not_lt] at hab
    simp only [zPos]
    rw [if_neg (by simp)]
    rcases Nat.lt_or_eq_of_le hab with hl | hl
    · refine (h1 _ (by omega)).2 _ (by omega) (by omega) (Or.inr (Or.inl ?_))
      simp only [symIdx]; split_ifs <;> omega
    · exact (h1 _ (by omega)).2 _ (by omega) (by omega) (Or.inr (Or.inr ⟨by omega, by omega⟩))
  · simp [FreeIx] at hab
  ·
    simp only [FreeIx, FreeTop, not_lt] at hab
    simp only [zPos]
    rw [if_neg (by simp)]
    refine (h1 _ (by omega)).2 _ (by omega) (by omega) (Or.inr (Or.inl ?_))
    simp only [symIdx]; split_ifs <;> omega
  ·
    simp only [FreeIx, FreeTop, not_lt, Fin.le_def] at hab
    simp only [zPos]
    by_cases h : i.val = i'.val
    · have : i = i' := Fin.ext h
      subst this
      rw [if_pos rfl]
      exact (h1 _ (by omega)).1
    · rw [if_neg (by intro e; simp only [Sum.inl.injEq, Sum.inr.injEq] at e; exact h (congrArg Fin.val e))]
      refine (h1 _ (by omega)).2 _ (by omega) (by omega) (Or.inr (Or.inl ?_))
      simp only [symIdx]; split_ifs <;> omega
  · simp [FreeIx] at hab
  ·
    simp only [zPos]
    rw [if_neg (by simp)]
    have := hA i u
    exact (h1 _ (by omega)).2 _ (by omega) (by omega) (Or.inl (by omega))
  · simp only [zPos]
    rw [if_neg (by simp)]
    have := hA i u
    exact (h1 _ (by omega)).2 _ (by omega) (by omega) (Or.inl (by omega))
  ·
    simp only [FreeIx, not_le, Fin.lt_def] at hab
    simp only [zPos]
    rw [if_neg (by intro e; simp only [Sum.inr.injEq, Prod.mk.injEq] at e; rw [e.1] at hab; omega)]
    have hu := hA i u
    have hu' := hA i' u'
    apply h2 _ _ (by omega) (by omega) (by omega)
    rw [hdiv, hdiv]
    exact hab

end GlobalTheory
end

section

open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.SymBridge

noncomputable section
namespace GlobalTheory.SymBridge.Coords

theorem xPos_lt {κ τ j : ℕ} (a : XIx (Fin κ) (Fin τ) j) : xPos a < κ + j * (τ + 1) := by
  have e : j * (τ + 1) = j * τ + j := by ring
  rcases a with (i | i) | p
  · have := i.2; simp only [xPos]; omega
  · have := i.2; simp only [xPos]; omega
  · have h1 := p.1.2
    have h2 := p.2.2
    have h3 : (p.1.val + 1) * τ ≤ j * τ := Nat.mul_le_mul_right _ h1
    have h4 : (p.1.val + 1) * τ = p.1.val * τ + τ := by ring
    simp only [xPos]; omega

end GlobalTheory.SymBridge.Coords
end
end

section

open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.SymBridge

noncomputable section
namespace GlobalTheory.SymResidue

theorem dsum_shift {R : Type} [AddCommMonoid R] (n : ℕ) (f : ℕ → ℕ → R) :
    (∑ i : Fin n, ∑ j : Fin n, if (j : ℕ) = (i : ℕ) + 1 then f i j else 0) =
      ∑ i ∈ Finset.range (n - 1), f i (i + 1) := by
  have h1 : ∀ i : Fin n, (∑ j : Fin n, if (j : ℕ) = (i : ℕ) + 1 then f i j else 0) =
      if (i : ℕ) + 1 < n then f i ((i : ℕ) + 1) else 0 := by
    intro i
    rw [Fin.sum_univ_eq_sum_range (fun j => if j = (i : ℕ) + 1 then f i j else 0) n]
    simp [Finset.sum_ite_eq', Finset.mem_range]
  rw [Finset.sum_congr rfl (fun i _ => h1 i)]
  rw [Fin.sum_univ_eq_sum_range (fun i => if i + 1 < n then f i (i + 1) else 0) n]
  rw [← Finset.sum_filter]
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_range]
  omega

theorem intAt_sum {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) (n : ℕ) (f : ℕ → E)
    (h : ∀ i < n, IntAt P (f i)) : IntAt P (∑ i ∈ Finset.range n, f i) := by
  refine Finset.sum_induction f (IntAt P) (fun a b ha hb => IntAt.add ha hb) ?_ ?_
  · simpa using IntAt.coe P 0
  · intro i hi
    exact h i (Finset.mem_range.mp hi)

end GlobalTheory.SymResidue

open GlobalTheory.SymResidue in
theorem GlobalTheory.symLevel_lam_residue : ∀ (E K k : Type) [Field E] [NumberField E] [StarRing E] [Field K] [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (P : HeightOneSpectrum (𝓞 E)) (q : ℕ) (ι : E →+* k) (σ₀ : K →+* ℂ) (ψ₀ : AddChar (𝓞 E ⧸ P.asIdeal) K) (χ : ℕ → (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) (s κ : ℕ) (S : SymData k s κ), Comparison₂ P q ι σ₀ ψ₀ χ S → ∀ (M : ℕ → ℕ → E), (∀ p p', p < κ + s + 1 → p' < κ + s + 1 → IntAt P (M p p')) → ∀ (g : S.P.J), (g : GL (Fin κ ⊕ Fin (s + 1)) k).val = Matrix.of (fun a b => ι (M (GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.framePos κ (s + 1) a) (GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.framePos κ (s + 1) b))) → ((S.P.lam g : ℂˣ) : ℂ) = σ₀ (ψ₀ (redP P (∑ i ∈ Finset.range (κ - 1), M i (i + 1) + ∑ i ∈ Finset.range (κ + s + 1 - κ - 1), M (κ + i) (κ + i + 1)))) := by
  intro E K k _ _ _ _ _ _ _ _ P q ι σ₀ ψ₀ χ s κ S hT M hM g hg
  have hent : ∀ a b, (g : GL (Fin κ ⊕ Fin (s + 1)) k).val a b =
      ι (M (GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.framePos κ (s + 1) a) (GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.framePos κ (s + 1) b)) := by
    intro a b; rw [hg]; rfl
  set A : E := ∑ i ∈ Finset.range (κ - 1), M i (i + 1) with hA
  set B : E := ∑ i ∈ Finset.range (κ + s + 1 - κ - 1), M (κ + i) (κ + i + 1) with hB
  have hAi : IntAt P A := intAt_sum P _ _ (fun i hi => hM _ _ (by omega) (by omega))
  have hBi : IntAt P B := intAt_sum P _ _ (fun i hi => hM _ _ (by omega) (by omega))
  have hsimple : GlobalTheory.RootEx.simpleSum (g : GL (Fin κ ⊕ Fin (s + 1)) k) = ι B := by
    unfold GlobalTheory.RootEx.simpleSum
    simp only [hent, GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.framePos, Sum.elim_inr]

    rw [dsum_shift (s + 1) (fun i j => ι (M (κ + i) (κ + j))), hB, map_sum]
    have : κ + s + 1 - κ - 1 = s + 1 - 1 := by omega
    rw [this]
    rfl
  have hsuper : GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.superSum Fin.val (g : GL (Fin κ ⊕ Fin (s + 1)) k).val.toBlocks₁₁ = ι A := by
    unfold GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.superSum
    simp only [Matrix.toBlocks₁₁, Matrix.of_apply, hent, GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.framePos, Sum.elim_inl]

    rw [dsum_shift κ (fun i j => ι (M i j)), hA, map_sum]
  have hdiv : ∀ X : E, ((S.ϖ⁻¹ : kˣ) : k) * ι X = ι (X / (q : E)) := by
    intro X
    rw [Units.val_inv_eq_inv_val, hT.compl.unif, ← map_inv₀, ← map_mul, div_eq_inv_mul]
  rw [S.sym.2 g, hsimple, hsuper, hdiv, hdiv, hT.psi B hBi, hT.psi A hAi, ← map_mul,
    ← AddChar.map_add_eq_mul, ← reduction_add hBi hAi, add_comm B A]
end
end
