module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.ResEmbCompat
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle541
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
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.Bundle001
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PowerMatchingTraces.MatchCut

@[expose] public section

section

noncomputable section

open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Shin
open GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.CBC
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.Gal.InertialTypesAlt

def expand (D : List (ℕ × ℕ)) : List (ℕ × ℕ) := D.flatMap fun p => List.replicate p.1 (1, p.2)

def Pairs {G : Type} (Y T : G → ℂ) : Prop := ∑ᶠ g, star (Y g) * T g ≠ 0

def Lbl.Apart (a : Lbl) : Prop :=
  (∀ p ∈ a.D, p.2 < a.q - 1) ∧ (a.D.map Prod.snd).Nodup ∧ (∀ p ∈ a.L, 2 ≤ p.1) ∧
    a.L.Pairwise fun p r => p.1 = r.1 → ∀ i : ℕ, ¬ r.2 ≡ p.2 * a.q ^ i [MOD a.q ^ p.1 - 1]

def MixType : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (n : ℕ), 0 < n →
    ∀ (π : CuspSub E n) (Y : Pt E Ω n), Lifts (Pt.base Ω π) Y →
    ∀ (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 E)) (w : HeightOneSpectrum (𝓞 Y.K)), IsPlaceOver A v →
      IsPlaceOver A w → ∀ (g : ℕ) [Fact g.Prime] (i : ℚ_[g] ≃+* v.adicCompletion E), Continuous i →
    (∀ t ∈ Ine (F := E) A, UpperTheory.Gal.UnramifiedFromSplittingCriterion.Fixes Y.K t) →
    ∀ τ τ', π.IsLocComp v τ → Y.π.IsLocComp w τ' → Mixed (IrrGL.of τ.ρ τ.smooth τ.irred) →
    ∀ f : ℕ, normV w = g ^ f → (∀ s, HasSupport τ.ρ s → ∀ y ∈ s, y.1 ∣ f) →
      ∃ (c : ℕ) (d : Fin c → ℕ) (hd : ∑ b, d b = n) (θ : Fin c → 𝓀[w.adicCompletion Y.K]ˣ →* ℂˣ), (∀ b, 0 < d b) ∧
        Function.Injective θ ∧ UpperTheory.Gal.TypesAndIwahori.HasTypeVec τ'.ρ (stdBlocks d hd) θ

def MixUnlinked : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (n : ℕ), 0 < n →
    ∀ (π : CuspSub E n) (Y : Pt E Ω n), Lifts (Pt.base Ω π) Y →
    ∀ (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 E)) (w : HeightOneSpectrum (𝓞 Y.K)), IsPlaceOver A v →
      IsPlaceOver A w → ∀ (g : ℕ) [Fact g.Prime] (i : ℚ_[g] ≃+* v.adicCompletion E), Continuous i →
    (∀ t ∈ Ine (F := E) A, UpperTheory.Gal.UnramifiedFromSplittingCriterion.Fixes Y.K t) →
    ∀ τ τ', π.IsLocComp v τ → Y.π.IsLocComp w τ' → Mixed (IrrGL.of τ.ρ τ.smooth τ.irred) →
    ∀ f : ℕ, normV w = g ^ f → (∀ s, HasSupport τ.ρ s → ∀ y ∈ s, y.1 ∣ f) →
      ∀ s, HasSupport τ'.ρ s → GlobalTheory.RoadU.Unlinked s

theorem suppBC_of_mix (h₁ : SuppAny) (h₂ : MixUnlinked) : SuppBC := by
  intro E Ω _ _ _ _ _ _ n hn π Y hY A v w h h' g _ i hi hI τ τ' hτ hτ' hD f hf hs
  obtain ⟨ξ, hξ, H⟩ := h₁ E Ω n hn π Y hY A v w h h' g i hi hI τ τ' hτ hτ' hD f hf hs
  exact ⟨ξ, hξ, H, fun hM => h₂ E Ω n hn π Y hY A v w h h' g i hi hI τ τ' hτ hτ' hM f hf hs _ H.2.1⟩

def JAppend : Prop :=
  ∀ (F : Type) [Field F] [Finite F] (θ : AlgebraicClosure F →* ℂ) (L L' : List (ℕ × ℕ)) (n : ℕ), n = deg L + deg L' →
    J θ (L ++ L') n = hc (deg L) (deg L') (J θ L (deg L)) (J θ L' (deg L')) n

def SepOf : Prop := ∀ (a : Lbl) (Q : ℕ), a.Ok → a.Apart → a.Splits Q → a.Sep Q

def Group1 : Prop :=
  ∀ L₀ : List (ℕ × ℕ), (∀ p ∈ L₀, 0 < p.1) → ∃ D : List (ℕ × ℕ), (∀ p ∈ D, 0 < p.1 ∧ (1, p.2) ∈ L₀) ∧ (D.map Prod.snd).Nodup ∧
    (expand D ++ L₀.filter fun p => 2 ≤ p.1).Perm L₀

def HcPair : Prop :=
  ∀ (F : Type) [Field F] [Finite F] (a b n : ℕ), n = a + b → ∀ (α A : GL (Fin a) F → ℂ) (β B : GL (Fin b) F → ℂ),
    GlobalTheory.BI.IsChar ℂ ℂ α → GlobalTheory.BI.IsChar ℂ ℂ A → GlobalTheory.BI.IsChar ℂ ℂ β → GlobalTheory.BI.IsChar ℂ ℂ B → Pairs A α → Pairs B β →
    Pairs (hc a b A B n) (hc a b α β n)

def HcOne : Prop :=
  ∀ (F : Type) [Field F] [Finite F] (a b n : ℕ), n = a + b → ∀ (α : GL (Fin a) F → ℂ) (β : GL (Fin b) F → ℂ),
    α 1 ≠ 0 → β 1 ≠ 0 → hc a b α β n 1 ≠ 0

def DetPair : Prop :=
  ∀ (F : Type) [Field F] [Finite F] (θ : AlgebraicClosure F →* ℂ) (t c : ℕ),
    Pairs (J θ (List.replicate t (1, c)) t) (detc θ t c)

def JDPair : Prop :=
  ∀ (F : Type) [Field F] [Finite F] (θ : AlgebraicClosure F →* ℂ), Inj θ → ∀ a : Lbl, a.Ok → a.q = Nat.card F →
    deg (expand a.D ++ a.L) = a.rk ∧ Pairs (J θ (expand a.D ++ a.L) a.rk) (JD θ a.D a.L a.rk)

def CuspFrob : Prop :=
  ∀ (F : Type) [Field F] [Finite F] (θ : AlgebraicClosure F →* ℂ), Inj θ → ∀ m c c' i : ℕ, 0 < m →
    c' ≡ c * Nat.card F ^ i [MOD Nat.card F ^ m - 1] → cusp θ m c' = cusp θ m c

def AvgMap : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (H : Subgroup G) (U Z W X : Type) [AddCommGroup U] [Module ℂ U] [AddCommGroup Z] [Module ℂ Z]
    [AddCommGroup W] [Module ℂ W] [AddCommGroup X] [Module ℂ X] (ρ : Representation ℂ G U) (κ : Representation ℂ H Z)
    (η : Representation ℂ G X) (Φ : Z →ₗ[ℂ] U) (ev : U →ₗ[ℂ] W) (ψ : X →ₗ[ℂ] Z),
    (∀ (h : H) z, Φ (κ h z) = ρ h (Φ z)) → (∀ g ∉ H, ∀ z, ev (ρ g (Φ z)) = 0) → (∀ z, ev (Φ z) = 0 → z = 0) →
    (∀ (h : H) x, ψ (η h x) = κ h (ψ x)) → ψ ≠ 0 → ∃ Ψ : X →ₗ[ℂ] U, Ψ ≠ 0 ∧ ∀ g x, Ψ (η g x) = ρ g (Ψ x)

def IndMap : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N s : ℕ) (d : Fin s → ℕ) (hd : ∑ a, d a = N) (W Z : Type) [AddCommGroup W] [Module ℂ W] [AddCommGroup Z] [Module ℂ Z]
    (ρ : Representation ℂ (Levi k fun a => Fin (d a)) W) (κ : Representation ℂ (Levi 𝓀[k] fun a => Fin (d a)) Z) (j : Z →ₗ[ℂ] W),
    Function.Injective j →
    (∀ (x : leviK k fun a => Fin (d a)) (z : Z), j (κ (redLevi k _ x) z) = ρ (x : Levi k fun a => Fin (d a)) (j z)) →
    ∃ (Φ : Z →ₗ[ℂ] fixed (parInd (stdBlocks d hd) ρ) (KOne k (Fin N)))
      (ev : fixed (parInd (stdBlocks d hd) ρ) (KOne k (Fin N)) →ₗ[ℂ] W),
      (∀ (p : parab 𝓀[k] (stdBlocks d hd)) z,
        Φ (κ (leviProj 𝓀[k] (stdBlocks d hd) p) z) = levelZero (parInd (stdBlocks d hd) ρ) p (Φ z)) ∧
      (∀ γ ∉ parab 𝓀[k] (stdBlocks d hd), ∀ z, ev (levelZero (parInd (stdBlocks d hd) ρ) γ (Φ z)) = 0) ∧
      ∀ z, ev (Φ z) = 0 → z = 0

def TensInc : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (s : ℕ) (d : Fin s → ℕ) (V : Fin s → Type) [∀ a, AddCommGroup (V a)] [∀ a, Module ℂ (V a)]
    (σ : ∀ a, Representation ℂ (GL (Fin (d a)) k) (V a)),
    ∃ j : (PiTensorProduct ℂ fun a => fixed (σ a) (KOne k (Fin (d a)))) →ₗ[ℂ] PiTensorProduct ℂ V, Function.Injective j ∧
      ∀ (x : leviK k fun a => Fin (d a)) z, j (piTensor (fun a => levelZero (σ a)) (redLevi k _ x) z) =
        piTensor σ (x : Levi k fun a => Fin (d a)) (j z)

def UnlFull : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k] (N : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V)
    (s : ℕ) (x : Fin s → IrrGL (k := k)) (hd : ∑ a, (x a).1 = N), HasSupport π (Finset.univ.val.map x) →
    GlobalTheory.RoadU.Unlinked (Finset.univ.val.map x) → Nonempty (π.Equiv (prodIrr x hd))

def LblFull : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k] (θ : AlgebraicClosure 𝓀[k] →* ℂ) (N : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin N) k) V), IsSmooth π → π.IsIrreducible →
    ∀ (s : ℕ) (x : Fin s → IrrGL (k := k)) (c : Fin s → ℕ) (hd : ∑ a, (x a).1 = N), Nonempty (π.Equiv (prodIrr x hd)) →
    (∀ a γ, LinearMap.trace ℂ _ (levelZero (x a).rep γ) = cusp θ (x a).1 (c a) γ) →
    ∀ T : GL (Fin N) 𝓀[k] → ℂ, GlobalTheory.BI.IsChar ℂ ℂ T → Pairs (J θ (List.ofFn fun a => ((x a).1, c a)) N) T → Meets (levelZero π) T

def InertOf : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω)
    (v : HeightOneSpectrum (𝓞 E)), IsPlaceOver A v → ∀ (g : ℕ) [Fact g.Prime] (i : ℚ_[g] ≃+* v.adicCompletion E), Continuous i →
    ∀ (m : ℕ) (x y : IrrCl (GL (Fin m) (v.adicCompletion E))), IrrGL.IsCusp ⟨m, x⟩ → IrrGL.IsCusp ⟨m, y⟩ →
      UpperTheory.Zero.LLC.DZ ⟨m, x⟩ → UpperTheory.Zero.LLC.DZ ⟨m, y⟩ →
      (∀ γ, LinearMap.trace ℂ _ (levelZero x.rep.ρ γ) = LinearMap.trace ℂ _ (levelZero y.rep.ρ γ)) →
      IrrGL.Inert ⟨m, x⟩ ⟨m, y⟩

def LblMixed : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω)
    (v : HeightOneSpectrum (𝓞 E)), IsPlaceOver A v → ∀ (g : ℕ) [Fact g.Prime] (i : ℚ_[g] ≃+* v.adicCompletion E), Continuous i →
    ∀ (θ : AlgebraicClosure 𝓀[v.adicCompletion E] →* ℂ), Inj θ → ∀ (n : ℕ) (τ : SmIrr (GL (Fin n) (v.adicCompletion E))),
      Mixed (IrrGL.of τ.ρ τ.smooth τ.irred) →
      ∃ (a : Lbl) (s : Multiset (IrrGL (k := v.adicCompletion E))), HasLbl θ τ.ρ a ∧ a.Apart ∧ HasSupport τ.ρ s ∧
        ∀ p ∈ a.L, ∃ y ∈ s, y.1 = p.1

end UpperTheory.Gal.InertialTypesAlt
end
end

section

open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Shin
open GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.CBC UpperTheory.Gal.InertialTypesAlt
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem gcd_step {m m' c l : ℕ} (hm : 0 < m) (hl : l.Prime) (h : m' * Nat.gcd m c = m) :
    (if l ∣ m' then m' / l else m') * Nat.gcd m (c * l) = m := by
  have hg : 0 < Nat.gcd m c := Nat.gcd_pos_of_pos_left _ hm
  obtain ⟨m₁, c₁, hco, hm₁, hc₁⟩ := Nat.exists_coprime m c
  have hmm : m₁ = m' := by
    apply Nat.eq_of_mul_eq_mul_right hg
    rw [← hm₁, h]
  subst hmm
  set g := Nat.gcd m c with hgdef
  have hgcd : Nat.gcd m (c * l) = Nat.gcd m₁ l * g := by
    have e : c * l = (c₁ * l) * g := by
      rw [hc₁]; ring
    rw [e]
    conv_lhs => rw [hm₁]
    rw [Nat.gcd_mul_right, Nat.Coprime.gcd_mul_left_cancel_right l hco.symm]
  rw [hgcd]
  split_ifs with hd
  · rw [Nat.gcd_eq_right hd, ← mul_assoc, Nat.div_mul_cancel hd]
    exact h
  · have : Nat.gcd m₁ l = 1 := ((Nat.Prime.coprime_iff_not_dvd hl).2 hd).symm
    rw [this, one_mul]
    exact h

theorem UpperTheory.Gal.InertialTypesAlt.leRank :
    LiftOk → LeRank := by
  intro hOk a b ha hab
  have key : b.Ok ∧ ∃ c : ℕ, 0 < c ∧ b.q = a.q ^ c ∧
      ∀ p ∈ b.L, ∃ r ∈ a.L, p.1 * Nat.gcd r.1 c = r.1 := by
    induction hab with
    | refl =>
      refine ⟨ha, 1, Nat.one_pos, (pow_one _).symm, fun p hp => ⟨p, hp, ?_⟩⟩
      rw [Nat.gcd_one_right, mul_one]
    | @tail b' b'' _ hs ih =>
      obtain ⟨hb, c, hc, hq, hL⟩ := ih
      obtain ⟨l, hl, rfl⟩ := hs
      refine ⟨(hOk b' l hl hb).1, c * l, Nat.mul_pos hc hl.pos, ?_, ?_⟩
      · change b'.q ^ l = _
        rw [hq, pow_mul]
      · intro p hp
        have hp' : p ∈ liftAll b'.q l b'.L := hp
        unfold liftAll at hp'
        obtain ⟨s, hs, hps⟩ := List.mem_flatMap.1 hp'
        obtain ⟨r, hr, hsr⟩ := hL s hs
        refine ⟨r, hr, ?_⟩
        have hm : 0 < r.1 := (ha.2.2 r hr).1
        have hstep := gcd_step (l := l) hm hl hsr
        have hp1 : p.1 = if l ∣ s.1 then s.1 / l else s.1 := by
          split_ifs at hps ⊢ with hd
          · simp only [liftL, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_map] at hps
            obtain ⟨i, -, rfl⟩ := hps
            rfl
          · simp only [List.mem_singleton] at hps
            rw [hps]
        rw [hp1]
        exact hstep
  exact key.2
end

section

open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Shin
open GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.CBC UpperTheory.Gal.InertialTypesAlt
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem label_le_preserves_splitting (h₁ : LiftOk) (h₂ : LiftBlocks) {a b : Lbl} (ha : a.Ok) (hab : a.Le b) :
    b.Ok ∧ b.rk = a.rk ∧ ∀ Q, b.Splits Q → a.Splits Q ∧ b.blocks Q = a.blocks Q := by
  induction hab with
  | refl => exact ⟨ha, rfl, fun Q hQ => ⟨hQ, rfl⟩⟩
  | @tail m c _ hstep ih =>
    obtain ⟨l, hl, rfl⟩ := hstep
    obtain ⟨hb, hrk, hS⟩ := ih
    obtain ⟨hc, hrk'⟩ := h₁ m l hl hb
    refine ⟨hc, hrk'.trans hrk, fun Q hQ => ?_⟩
    obtain ⟨hbQ, hblk⟩ := h₂ m l Q hl hb hQ
    obtain ⟨haQ, hblk'⟩ := hS Q hbQ
    exact ⟨haQ, hblk.trans hblk'⟩

theorem UpperTheory.Gal.InertialTypesAlt.leTop :
    LiftOk → LiftBlocks → LeRank → LeTop := by
  intro h₁ h₂ h₃ a b ha hab hs
  obtain ⟨hb, hrk, hS⟩ := label_le_preserves_splitting h₁ h₂ ha hab
  obtain ⟨f, hf, hq, hd⟩ := hs
  obtain ⟨c, hc, hbq, hp⟩ := h₃ a b ha hab
  have hcf : c = f := Nat.pow_right_injective ha.1 (hbq.symm.trans hq)
  subst hcf
  have hone : ∀ p ∈ b.L, p.1 = 1 := by
    intro p hpL
    obtain ⟨r, hr, hpr⟩ := hp p hpL
    have hr0 : 0 < r.1 := (ha.2.2 r hr).1
    rw [Nat.gcd_eq_left (hd r hr)] at hpr
    exact Nat.eq_of_mul_eq_mul_right hr0 (by simpa using hpr)
  refine ⟨hb, hrk, hone, (hS b.q ⟨1, Nat.one_pos, (pow_one _).symm, fun p hpL => ?_⟩).2⟩
  rw [hone p hpL]
end

section

open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Shin
open GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.CBC UpperTheory.Gal.InertialTypesAlt
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem det_gal {A B : Type} [Field A] [Field B] (f : A →+* B) (n : ℕ) (x : GL (Fin n) A) :
    ((gal f n x : GL (Fin n) B) : Matrix (Fin n) (Fin n) B).det = f (x : Matrix (Fin n) (Fin n) A).det := by
  rw [RingHom.map_det]
  rfl

private theorem pow_apply_eq {F F' : Type} [Field F] [Field F'] [Algebra F F'] (s : F' ≃ₐ[F] F') (q : ℕ)
    (hs : ∀ z, s z = z ^ q) (i : ℕ) (z : F') : (s ^ i) z = z ^ (q ^ i) := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [pow_succ', AlgEquiv.mul_apply, ih, hs, ← pow_mul, pow_succ]

private theorem det_nrmG {F F' : Type} [Field F] [Field F'] [Algebra F F'] (s : F' ≃ₐ[F] F') (q : ℕ)
    (hs : ∀ z, s z = z ^ q) (t l : ℕ) (δ : GL (Fin t) F') :
    ((nrmG (galAct F F' t) s l δ : GL (Fin t) F') : Matrix (Fin t) (Fin t) F').det =
      (δ : Matrix (Fin t) (Fin t) F').det ^ ∑ i ∈ Finset.range l, q ^ i := by
  induction l with
  | zero => simp [nrmG]
  | succ l ih =>
    have h : nrmG (galAct F F' t) s (l + 1) δ =
        nrmG (galAct F F' t) s l δ * galAct F F' t (s ^ l) δ := by
      simp [nrmG, List.range_succ]
    rw [h, Units.val_mul, Matrix.det_mul, ih, galAct_apply, det_gal, Finset.sum_range_succ, pow_add]
    congr 1
    exact pow_apply_eq s q hs l _

theorem UpperTheory.Gal.InertialTypesAlt.liftDet :
    LiftDet := by
  intro F F' _ _ _ _ s hs ι θ t k hN
  funext δ
  unfold shLift
  rw [dite_eq_left (hN δ)]
  have hγ : IsNorm s δ (hN δ).choose := (hN δ).choose_spec
  generalize (hN δ).choose = γ at hγ
  have h1 : ((incl F F' t γ : GL (Fin t) F') : Matrix (Fin t) (Fin t) F').det =
      ((nrm s δ : GL (Fin t) F') : Matrix (Fin t) (Fin t) F').det := by
    have h := congrArg Units.val (isConj_iff_eq.1 ((Matrix.GeneralLinearGroup.det).map_isConj hγ))
    simpa using h
  have h2 : algebraMap F F' (γ : Matrix (Fin t) (Fin t) F).det =
      (δ : Matrix (Fin t) (Fin t) F').det ^ ∑ i ∈ Finset.range (Module.finrank F F'), Nat.card F ^ i := by
    rw [← det_nrmG s (Nat.card F) hs t _ δ]
    have h3 := det_gal (algebraMap F F') t γ
    rw [← h3]
    exact h1
  have h4 : pullθ ι θ (algebraMap F (AlgebraicClosure F) (γ : Matrix (Fin t) (Fin t) F).det) =
      θ (algebraMap F' (AlgebraicClosure F') (algebraMap F F' (γ : Matrix (Fin t) (Fin t) F).det)) := by
    change θ (ι _) = _
    rw [ι.commutes, IsScalarTower.algebraMap_apply F F' (AlgebraicClosure F')]
  simp only [detc]
  rw [h4, h2, map_pow, map_pow, ← pow_mul, mul_comm]
end

section

open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Shin
open GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.CBC UpperTheory.Gal.InertialTypesAlt
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

section ParConsAux

variable {F : Type} [Field F]

private theorem tl_entry {a n : ℕ} (M : Matrix (Fin n) (Fin n) F) (i j : Fin a) (I J : Fin n)
    (hI : (I : ℕ) = i) (hJ : (J : ℕ) = j) : GlobalTheory.Shin.tl a M i j = M I J := by
  unfold GlobalTheory.Shin.tl GlobalTheory.Shin.ent
  rw [dite_eq_left ⟨by rw [← hI]; exact I.isLt, by rw [← hJ]; exact J.isLt⟩]
  congr 1 <;> ext <;> simp [hI, hJ]

private theorem br_entry {a b n : ℕ} (M : Matrix (Fin n) (Fin n) F) (i j : Fin b) (I J : Fin n)
    (hI : (I : ℕ) = a + i) (hJ : (J : ℕ) = a + j) : GlobalTheory.Shin.br a b M i j = M I J := by
  unfold GlobalTheory.Shin.br GlobalTheory.Shin.ent
  rw [dite_eq_left ⟨by rw [← hI]; exact I.isLt, by rw [← hJ]; exact J.isLt⟩]
  congr 1 <;> ext <;> simp [hI, hJ]

private theorem units_of {a b n : ℕ} (hn : n = a + b) (p : GL (Fin n) F) (h : GlobalTheory.Shin.InPar a p) :
    IsUnit (GlobalTheory.Shin.tl a (p : Matrix (Fin n) (Fin n) F)) ∧
      IsUnit (GlobalTheory.Shin.br a b (p : Matrix (Fin n) (Fin n) F)) := by
  subst hn
  have hM : (p : Matrix (Fin (a + b)) (Fin (a + b)) F).submatrix finSumFinEquiv finSumFinEquiv =
      Matrix.fromBlocks (GlobalTheory.Shin.tl a (p : Matrix (Fin (a + b)) (Fin (a + b)) F))
        (Matrix.of fun i j => (p : Matrix (Fin (a + b)) (Fin (a + b)) F) (Fin.castAdd b i) (Fin.natAdd a j)) 0
        (GlobalTheory.Shin.br a b (p : Matrix (Fin (a + b)) (Fin (a + b)) F)) := by
    refine Matrix.ext fun i j => ?_
    rcases i with i | i <;> rcases j with j | j
    · simp only [Matrix.submatrix_apply, Matrix.fromBlocks_apply₁₁, finSumFinEquiv_apply_left]
      exact (tl_entry _ i j _ _ (by simp) (by simp)).symm
    · simp only [Matrix.submatrix_apply, Matrix.fromBlocks_apply₁₂, finSumFinEquiv_apply_left,
        finSumFinEquiv_apply_right, Matrix.of_apply]
    · simp only [Matrix.submatrix_apply, Matrix.fromBlocks_apply₂₁, finSumFinEquiv_apply_left,
        finSumFinEquiv_apply_right, Matrix.zero_apply]
      exact h _ _ (by simp) (by simp)
    · simp only [Matrix.submatrix_apply, Matrix.fromBlocks_apply₂₂, finSumFinEquiv_apply_right]
      exact (br_entry _ i j _ _ (by simp) (by simp)).symm
  have hu : IsUnit (p : Matrix (Fin (a + b)) (Fin (a + b)) F).det :=
    (Matrix.isUnit_iff_isUnit_det _).1 p.isUnit
  rw [← Matrix.det_submatrix_equiv_self finSumFinEquiv, hM, Matrix.det_fromBlocks_zero₂₁,
    IsUnit.mul_iff] at hu
  exact ⟨(Matrix.isUnit_iff_isUnit_det _).2 hu.1, (Matrix.isUnit_iff_isUnit_det _).2 hu.2⟩

private theorem toG_coe {n : ℕ} {M : Matrix (Fin n) (Fin n) F} (h : IsUnit M) :
    ((GlobalTheory.Shin.toG M : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = M := by
  unfold GlobalTheory.Shin.toG
  rw [dite_eq_left h]
  rfl

private theorem sv0 {s n : ℕ} (d : Fin (s + 1) → ℕ) (hd : ∑ i, d i = n) (i : Fin (d 0)) :
    ((GlobalTheory.SmGL.stdBlocks d hd ⟨0, i⟩ : Fin n) : ℕ) = i := by
  rw [GlobalTheory.SmGL.stdBlocks_val]
  simp

private theorem svS {s n b : ℕ} (d : Fin (s + 1) → ℕ) (hd : ∑ i, d i = n)
    (hb : ∑ i : Fin s, d i.succ = b) (c : Fin s) (i : Fin (d c.succ)) :
    ((GlobalTheory.SmGL.stdBlocks d hd ⟨c.succ, i⟩ : Fin n) : ℕ) =
      d 0 + ((GlobalTheory.SmGL.stdBlocks (fun i : Fin s => d i.succ) hb ⟨c, i⟩ : Fin b) : ℕ) := by
  rw [GlobalTheory.SmGL.stdBlocks_val, GlobalTheory.SmGL.stdBlocks_val]
  erw [Fin.sum_univ_succ]
  rw [add_assoc]
  congr 2

private theorem inPar_of {s n b : ℕ} (d : Fin (s + 1) → ℕ) (hd : ∑ i, d i = n)
    (hb : ∑ i : Fin s, d i.succ = b) (p : GL (Fin n) F)
    (hp : p ∈ GlobalTheory.SmGL.parab F (GlobalTheory.SmGL.stdBlocks d hd)) : GlobalTheory.Shin.InPar (d 0) p := by
  intro i j hj hi
  obtain ⟨⟨α, i'⟩, rfl⟩ := (GlobalTheory.SmGL.stdBlocks d hd).surjective i
  obtain ⟨⟨β, j'⟩, rfl⟩ := (GlobalTheory.SmGL.stdBlocks d hd).surjective j
  rw [GlobalTheory.SmGL.mem_parab_iff] at hp
  cases β using Fin.cases with
  | zero =>
    cases α using Fin.cases with
    | zero =>
      rw [sv0] at hi
      exact absurd i'.isLt (by omega)
    | succ c => exact hp _ _ _ _ (Fin.succ_pos c)
  | succ c =>
    rw [svS d hd hb] at hj
    omega

private theorem brG_entry {s n b : ℕ} (d : Fin (s + 1) → ℕ) (hd : ∑ i, d i = n)
    (hb : ∑ i : Fin s, d i.succ = b) (hn : n = d 0 + b) (p : GL (Fin n) F)
    (h : GlobalTheory.Shin.InPar (d 0) p) (c c' : Fin s) (i : Fin (d c.succ)) (j : Fin (d c'.succ)) :
    ((GlobalTheory.Shin.brG (d 0) b p : GL (Fin b) F) : Matrix (Fin b) (Fin b) F)
        (GlobalTheory.SmGL.stdBlocks (fun i : Fin s => d i.succ) hb ⟨c, i⟩)
        (GlobalTheory.SmGL.stdBlocks (fun i : Fin s => d i.succ) hb ⟨c', j⟩) =
      (p : Matrix (Fin n) (Fin n) F) (GlobalTheory.SmGL.stdBlocks d hd ⟨c.succ, i⟩)
        (GlobalTheory.SmGL.stdBlocks d hd ⟨c'.succ, j⟩) := by
  unfold GlobalTheory.Shin.brG
  rw [toG_coe (units_of hn p h).2]
  exact br_entry _ _ _ _ _ (svS d hd hb c i) (svS d hd hb c' j)

end ParConsAux

theorem UpperTheory.Gal.InertialTypesAlt.parCons :
    ParCons := by
  intro F _ s n d hd b hb p
  have hn : n = d 0 + b := by rw [← hd, ← hb, Fin.sum_univ_succ]
  refine ⟨⟨fun hp => ⟨inPar_of d hd hb p hp, ?_⟩, fun ⟨h1, h2⟩ => ?_⟩, fun hp hp' => ⟨?_, fun c => ?_⟩⟩
  · have h1 := inPar_of d hd hb p hp
    rw [GlobalTheory.SmGL.mem_parab_iff] at hp ⊢
    intro c c' i j hc
    rw [brG_entry d hd hb hn p h1]
    exact hp _ _ _ _ (Fin.succ_lt_succ_iff.2 hc)
  · rw [GlobalTheory.SmGL.mem_parab_iff] at h2 ⊢
    intro α β i j hαβ
    cases α using Fin.cases with
    | zero => exact absurd hαβ (Fin.not_lt_zero _)
    | succ c =>
      cases β using Fin.cases with
      | zero =>
        apply h1
        · rw [sv0]; exact j.isLt
        · rw [svS d hd hb]; omega
      | succ c' =>
        rw [← brG_entry d hd hb hn p h1]
        exact h2 _ _ _ _ (Fin.succ_lt_succ_iff.1 hαβ)
  · have h1 := inPar_of d hd hb p hp
    ext i j
    change (p : Matrix (Fin n) (Fin n) F) (GlobalTheory.SmGL.stdBlocks d hd ⟨0, i⟩)
      (GlobalTheory.SmGL.stdBlocks d hd ⟨0, j⟩) = _
    unfold GlobalTheory.Shin.tlG
    rw [toG_coe (units_of hn p h1).1]
    exact (tl_entry _ _ _ _ _ (sv0 d hd i) (sv0 d hd j)).symm
  · have h1 := inPar_of d hd hb p hp
    ext i j
    change (p : Matrix (Fin n) (Fin n) F) (GlobalTheory.SmGL.stdBlocks d hd ⟨c.succ, i⟩)
        (GlobalTheory.SmGL.stdBlocks d hd ⟨c.succ, j⟩) =
      ((GlobalTheory.Shin.brG (d 0) b p : GL (Fin b) F) : Matrix (Fin b) (Fin b) F)
        (GlobalTheory.SmGL.stdBlocks (fun i : Fin s => d i.succ) hb ⟨c, i⟩)
        (GlobalTheory.SmGL.stdBlocks (fun i : Fin s => d i.succ) hb ⟨c, j⟩)
    rw [brG_entry d hd hb hn p h1]
end

section

open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Shin
open GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.CBC UpperTheory.Gal.InertialTypesAlt
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.Gal.InertialTypesAlt.hcChar :
    HcChar := by
  intro F _ _ a b n hn A B hA hB
  exact GlobalTheory.T.harishChandraInductionGL_isCharacter F a b n hn A B hA hB
end
