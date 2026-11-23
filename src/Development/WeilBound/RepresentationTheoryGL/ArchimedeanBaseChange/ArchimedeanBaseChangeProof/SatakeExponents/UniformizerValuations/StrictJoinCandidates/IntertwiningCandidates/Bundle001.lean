module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.StrictJoinCandidates.IntertwiningCandidates.StrictJoin
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1264
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.PolynomialPairSpaces.Bundle001
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle326
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle587
import GroundTheory.LocalFields.PadicLogSeries
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.FiniteDiscreteFamilies.LocalCompatibilityGL.Bundle001
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.FiniteDiscreteFamilies.LocalCompatibilityGL.Bundle002
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section

namespace PositivityTheory.Rg.BcB.F.FX.Bo.IsoInverse

open GlobalTheory.PRep

variable {G V V' : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']

theorem mem_fixed_iff (ρ : Representation ℂ G V) (K : Subgroup G) (v : V) :
    v ∈ fixed ρ K ↔ ∀ h : K, ρ (h : G) v = v := by
  show (∀ h : K, ρ (h : G) v = ((1 : K →* ℂˣ) h : ℂ) • v) ↔ _
  simp

variable {ρ : Representation ℂ G V} {ρ' : Representation ℂ G V'}

theorem symm_intertwines (L : V ≃ₗ[ℂ] V') (hL : ∀ g v, L (ρ g v) = ρ' g (L v)) :
    ∀ g w, L.symm (ρ' g w) = ρ g (L.symm w) := by
  intro g w
  apply L.injective
  rw [hL, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]

theorem map_fixed_le (L : V ≃ₗ[ℂ] V') (hL : ∀ g v, L (ρ g v) = ρ' g (L v)) (K : Subgroup G) :
    (fixed ρ K).map (L : V →ₗ[ℂ] V') ≤ fixed ρ' K := by
  rintro _ ⟨v, hv, rfl⟩
  rw [SetLike.mem_coe, mem_fixed_iff] at hv
  rw [mem_fixed_iff]
  intro h
  simp only [LinearEquiv.coe_coe]
  rw [← hL, hv h]

theorem map_fixed_eq (L : V ≃ₗ[ℂ] V') (hL : ∀ g v, L (ρ g v) = ρ' g (L v)) (K : Subgroup G) :
    (fixed ρ K).map (L : V →ₗ[ℂ] V') = fixed ρ' K := by
  refine le_antisymm (map_fixed_le L hL K) ?_
  intro w hw
  have hm : (L.symm : V' →ₗ[ℂ] V) w ∈ (fixed ρ' K).map (L.symm : V' →ₗ[ℂ] V) := ⟨w, hw, rfl⟩
  refine ⟨L.symm w, map_fixed_le L.symm (symm_intertwines L hL) K hm, ?_⟩
  simp

def imap (L : V ≃ₗ[ℂ] V') (hL : ∀ g v, L (ρ g v) = ρ' g (L v)) : ρ.IntertwiningMap ρ' :=
  ⟨(L : V →ₗ[ℂ] V'), fun g => by ext v; exact hL g v⟩

theorem isSubquotient_of (L : V ≃ₗ[ℂ] V') (hL : ∀ g v, L (ρ g v) = ρ' g (L v)) :
    GlobalTheory.SmGL.IsSubquotient ρ' ρ :=
  GlobalTheory.SmGL.IsSubquotient.of_surjective (imap L hL) (fun w => ⟨L.symm w, L.apply_symm_apply w⟩)

end PositivityTheory.Rg.BcB.F.FX.Bo.IsoInverse

namespace PositivityTheory.Rg.BcB.F.FX.Bo

open GlobalTheory.PRep IsoInverse

theorem IsoInv_holds : IsoInv := by
  intro G V V' _ _ _ _ _ ρ ρ' ⟨e⟩ K
  have hL : ∀ g v, e.toLinearEquiv (ρ g v) = ρ' g (e.toLinearEquiv v) := fun g v =>
    Representation.IntertwiningMap.isIntertwining (f := e.toIntertwiningMap) (g := g) (v := v)
  have hL' := symm_intertwines e.toLinearEquiv hL
  let F := e.toLinearEquiv.ofSubmodules _ _ (map_fixed_eq e.toLinearEquiv hL K)
  refine ⟨fun W _ _ τ => ⟨fun h => h.trans (isSubquotient_of e.toLinearEquiv.symm hL'),
    fun h => h.trans (isSubquotient_of e.toLinearEquiv hL)⟩, F.finrank_eq,
    ⟨fun _ => F.finiteDimensional, fun _ => F.symm.finiteDimensional⟩⟩

end PositivityTheory.Rg.BcB.F.FX.Bo
end
end

section

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcB.F.F5 PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.BcB.SpectralAccumulation
open scoped Classical



attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.BcB.F.FX.Bo.He2

open PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.BcB.CG

theorem fin_reps {X : Type} {α : Type 1} [Finite X] (Q : X → α → Prop) :
    ∃ (k : ℕ) (Dl : Fin k → α), ∀ x D, Q x D → ∃ j, Q x (Dl j) := by
  obtain ⟨k, ⟨ε⟩⟩ := Finite.exists_equiv_fin {x // ∃ D, Q x D}
  refine ⟨k, fun j => (ε.symm j).2.choose, fun x D h => ⟨ε ⟨x, D, h⟩, ?_⟩⟩
  have := (ε.symm (ε ⟨x, D, h⟩)).2.choose_spec
  simp only [Equiv.symm_apply_apply] at this ⊢
  exact this



def ClauseB {hR : Rd.ReadLimit} {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} {π : Submodule ℂ (UA E n → ℂ)}
    {S : Finset (Pl E)} (F₀ : Frame0 hR π S) (d : LocData E n) : Prop :=
  ∀ w ∈ F₀.d₀.S₀, ∃ (k : ℕ) (Dl : Fin k → Pre E n), ∀ i s₁ s₂ Pa Pb D, F₀.Cand d i s₁ s₂ Pa Pb D →
      ∃ j, (∀ τ : SmIrr (GLw n w), GlobalTheory.SmGL.IsSubquotient τ.ρ (prodAt D w) ↔ GlobalTheory.SmGL.IsSubquotient τ.ρ (prodAt (Dl j) w)) ∧
        Module.finrank ℂ ↥(fixed (prodAt D w) (F₀.d₀.K' w)) = Module.finrank ℂ ↥(fixed (prodAt (Dl j) w) (F₀.d₀.K' w)) ∧
        FiniteDimensional ℂ ↥(fixed (prodAt (Dl j) w) (F₀.d₀.K' w))



theorem candB (hEq : StrictEqv) (hSPr : StrictProd) (hSJ : StrictJoin) (hII : IsoInv) (hAd : AdmProd)
    {hR : Rd.ReadLimit} {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} {π : Submodule ℂ (UA E n → ℂ)}
    {S : Finset (Pl E)} (F₀ : Frame0 hR π S) (d : LocData E n) (kA kB : F₀.C.ι → ℕ)
    (PA : ∀ i, Fin (kA i) → Pre E (F₀.C.a i)) (PB : ∀ i, Fin (kB i) → Pre E (n - F₀.C.a i))
    (hcls : ∀ i s₁ s₂ Pa Pb D, F₀.Cand d i s₁ s₂ Pa Pb D → (∃ ja, Strict Pa (PA i ja)) ∧ ∃ jb, Strict Pb (PB i jb)) :
    ClauseB F₀ d := by
  intro w hw
  obtain ⟨k, Dl, hD⟩ := fin_reps (X := Σ i : F₀.C.ι, Fin (kA i) × Fin (kB i)) (α := Pre E n) fun x D =>
    ∃ Pa Pb, IsJoin (F₀.μ ^ (n - F₀.C.a x.1)) (F₀.μ ^ F₀.C.a x.1) Pa Pb D ∧ Strict Pa (PA x.1 x.2.1) ∧ Strict Pb (PB x.1 x.2.2)
  refine ⟨k, Dl, fun i s₁ s₂ Pa Pb D hc => ?_⟩
  obtain ⟨⟨ja, ha⟩, ⟨jb, hb⟩⟩ := hcls i s₁ s₂ Pa Pb D hc
  obtain ⟨j, Pa', Pb', hj, ha', hb'⟩ := hD ⟨i, ja, jb⟩ D ⟨Pa, Pb, hc.ctx.join, ha, hb⟩
  have hs : Strict D (Dl j) := hSJ E n _ _ _ _ Pa Pa' Pb Pb' D _ hc.ctx.join hj
    ((hEq E _ Pa _ Pa').2 ha ((hEq E _ Pa' _ Pa').1 ha')) ((hEq E _ Pb _ Pb').2 hb ((hEq E _ Pb' _ Pb').1 hb'))
  have hI := hII _ _ _ (prodAt D w) (prodAt (Dl j) w) (hSPr E n D (Dl j) hs w) (F₀.d₀.K' w)
  exact ⟨j, fun τ => hI.1 τ.V τ.ρ, hI.2.1, hAd E n (Dl j) w _ (F₀.ok₀.K' w hw).1 (F₀.ok₀.K' w hw).2.1⟩

end PositivityTheory.Rg.BcB.F.FX.Bo.He2

end
end

section

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcB.F.F5 PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.BcB.SpectralAccumulation
open scoped Classical



attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.BcB.F.FX.Bo.CandidateLeafDecomposition

open PositivityTheory.Rg.BcB.F

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem allLeaves_iff (Q : ∀ M : ℕ, Submodule ℂ (Sm E M) → Prop) :
    ∀ {N : ℕ} (t : Tr E N), t.AllLeaves Q ↔ ∀ x ∈ t.leafList, Q x.1 x.2
  | _, .leaf V z => by simp [Tr.AllLeaves, Tr.leafList]
  | _, .node t₁ t₂ => by
    rw [Tr.AllLeaves, Tr.leafList, allLeaves_iff Q t₁, allLeaves_iff Q t₂]
    simp only [List.mem_append]
    constructor
    · rintro ⟨h₁, h₂⟩ x (hx | hx)
      · exact h₁ x hx
      · exact h₂ x hx
    · intro h
      exact ⟨fun x hx => h x (Or.inl hx), fun x hx => h x (Or.inr hx)⟩

theorem parts_of_leaves {N : ℕ} (t : Tr E N) (P : Pre E N) (Q : ∀ M : ℕ, Submodule ℂ (Sm E M) → Prop)
    (ht : TreeParts t P) (hl : t.AllLeaves fun M V => M = 0 ∨ Q M V) : ∀ j, Q (P.N j) (P.V j) := by
  intro j
  have hmem : (⟨P.N j, P.V j⟩ : Σ M : ℕ, Submodule ℂ (Sm E M)) ∈ t.leafList.filter fun x => 0 < x.1 := by
    rw [← ht]
    exact List.mem_ofFn.2 ⟨j, rfl⟩
  rw [List.mem_filter] at hmem
  obtain ⟨hx, hpos⟩ := hmem
  have h := (allLeaves_iff _ t).1 hl _ hx
  rcases h with h0 | hQ
  · simp only [decide_eq_true_eq] at hpos
    exact absurd h0 (Nat.pos_iff_ne_zero.1 hpos)
  · exact hQ

end PositivityTheory.Rg.BcB.F.FX.Bo.CandidateLeafDecomposition

namespace PositivityTheory.Rg.BcB.F.FX.Bo

open PositivityTheory.Rg.BcB.F

theorem CandParts_holds : CandParts := by
  intro hR E _ _ _ n π S F₀ d i s₁ s₂ Pa Pb D hC
  exact ⟨CandidateLeafDecomposition.parts_of_leaves s₁ Pa _ hC.ctx.t₁ hC.leaves₁,
    CandidateLeafDecomposition.parts_of_leaves s₂ Pb _ hC.ctx.t₂ hC.leaves₂⟩

end PositivityTheory.Rg.BcB.F.FX.Bo

end
end

section

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcB.SpectralAccumulation

namespace PositivityTheory.Rg.BcB.F.FX.Bo.StrictJoinAlt

open PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.BcB.F.FX.Bo

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem isoV_map_mulChi {N : ℕ} {V V' : Submodule ℂ (Sm E N)} (χ : HChar E) (h : IsoV V V') :
    IsoV (V.map (mulChi N χ).toLinearMap) (V'.map (mulChi N χ).toLinearMap) := by
  obtain ⟨T, hT⟩ := h
  let S : V ≃ₗ[ℂ] V.map (mulChi N χ).toLinearMap := (mulChi N χ).submoduleMap V
  let S' : V' ≃ₗ[ℂ] V'.map (mulChi N χ).toLinearMap := (mulChi N χ).submoduleMap V'
  refine ⟨(S.symm.trans T).trans S', fun o φ ψ hψ => ?_⟩
  obtain ⟨φ, rfl⟩ := S.surjective φ
  obtain ⟨ψ, rfl⟩ := S.surjective ψ
  have h1 : ψ.1 = ((opMul χ o : ℂˣ) : ℂ) • act o φ.1 + opAdd χ o • φ.1 := by
    apply (mulChi N χ).injective
    rw [← act_mulChi]
    exact hψ
  have hm : act o φ.1 ∈ V := by
    have h2 : ((opMul χ o : ℂˣ) : ℂ) • act o φ.1 ∈ V := by
      have h3 := V.sub_mem ψ.2 (V.smul_mem (opAdd χ o) φ.2)
      rwa [h1, add_sub_cancel_right] at h3
    exact (Submodule.smul_mem_iff _ (Units.ne_zero _)).1 h2
  let φo : V := ⟨act o φ.1, hm⟩
  have hψ' : ψ = ((opMul χ o : ℂˣ) : ℂ) • φo + opAdd χ o • φ := Subtype.ext h1
  rw [hψ']
  simp only [LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply, map_add (f := _), map_smul]
  change ((opMul χ o : ℂˣ) : ℂ) • mulChi N χ (T φo).1 + opAdd χ o • mulChi N χ (T φ).1 = act o (mulChi N χ (T φ).1)
  rw [act_mulChi, ← hT o φ φo rfl, map_add (f := _), map_smul, map_smul]

theorem sIso_twPart (χ : HChar E) {x y : Σ M : ℕ, Submodule ℂ (Sm E M)} (h : SIso x y) :
    SIso (twPart χ x) (twPart χ y) := by
  obtain ⟨M, V⟩ := x
  obtain ⟨M', V'⟩ := y
  obtain ⟨h1, h2⟩ := h
  cases h1
  exact ⟨rfl, isoV_map_mulChi χ h2⟩

def R (τ : E →+* ℂ) (x : Σ M : ℕ, Submodule ℂ (Sm E M)) (m : Multiset ℂ) : Prop :=
  HasInfCharGL x.2 τ m ∧ x.2 ≠ ⊥

def infs {n : ℕ} (P : Pre E n) (τ : E →+* ℂ) : List (Multiset ℂ) := List.ofFn fun i => P.m i τ

theorem forall₂_R {n : ℕ} (P : Pre E n) (τ : E →+* ℂ) : List.Forall₂ (R τ) (parts P) (infs P τ) := by
  rw [List.forall₂_iff_get]
  refine ⟨by simp [parts, infs], fun i h₁ h₂ => ?_⟩
  have hi : i < P.c := by simpa [infs] using h₂
  have key : ∀ (x : Σ M : ℕ, Submodule ℂ (Sm E M)) (m : Multiset ℂ), x = ⟨P.N ⟨i, hi⟩, P.V ⟨i, hi⟩⟩ →
      m = P.m ⟨i, hi⟩ τ → R τ x m := by
    rintro x m rfl rfl
    exact ⟨P.inf _ τ, (P.discrete _).ne_bot⟩
  exact key _ _ (by simp [parts]) (by simp [infs])

theorem R_twPart (χ : HChar E) {τ : E →+* ℂ} {x : Σ M : ℕ, Submodule ℂ (Sm E M)} {m : Multiset ℂ} (h : R τ x m) :
    R τ (twPart χ x) (m.map (· + expo χ τ)) := by
  obtain ⟨M, V⟩ := x
  refine ⟨GlobalTheory.BCT.TwistDisc.hasInfCharGL_map h.1 χ, fun h0 => h.2 ?_⟩
  exact (Submodule.map_eq_bot_iff (e := mulChi M χ)).1 h0

theorem eq_of_forall₂ {τ : E →+* ℂ} : ∀ {l : List (Σ M : ℕ, Submodule ℂ (Sm E M))} {l₁ l₂ : List (Multiset ℂ)},
    List.Forall₂ (R τ) l l₁ → List.Forall₂ (R τ) l l₂ → l₁ = l₂
  | _, _, _, .nil, .nil => rfl
  | _, _, _, .cons h₁ t₁, .cons h₂ t₂ => by
    rw [LemDd.InfUniq_holds E _ _ τ _ _ h₁.2 h₁.1 h₂.1, eq_of_forall₂ t₁ t₂]

theorem infs_eq_of_strict {n : ℕ} {P P' : Pre E n} (h : Strict P P') (τ : E →+* ℂ) : infs P τ = infs P' τ := by
  obtain ⟨-, hc, hm⟩ := h
  unfold infs
  rw [List.ofFn_congr hc]
  congr 1
  funext i
  rw [hm]
  rfl

end PositivityTheory.Rg.BcB.F.FX.Bo.StrictJoinAlt

namespace PositivityTheory.Rg.BcB.F.FX.Bo

open PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.RS StrictJoinAlt

theorem StrictJoin_holds : StrictJoin := by
  intro E _ _ _ n a b χ₁ χ₂ Pa Pa' Pb Pb' D D' hJ hJ' ha hb
  have hF : List.Forall₂ SIso (parts D) (parts D') := by
    rw [hJ, hJ']
    refine List.rel_append ?_ ?_
    · exact List.forall₂_map_left_iff.2 (List.forall₂_map_right_iff.2 (ha.1.imp fun _ _ h => sIso_twPart χ₁ h))
    · exact List.forall₂_map_left_iff.2 (List.forall₂_map_right_iff.2 (hb.1.imp fun _ _ h => sIso_twPart χ₂ h))
  have hc : D.c = D'.c := by
    have := hF.length_eq
    simpa [parts] using this
  refine ⟨hF, hc, fun i => ?_⟩
  funext τ
  have hI : ∀ {Q : Pre E a} {S : Pre E b} {Z : Pre E n}, IsJoin χ₁ χ₂ Q S Z →
      infs Z τ = (infs Q τ).map (fun m => m.map (· + expo χ₁ τ)) ++ (infs S τ).map (fun m => m.map (· + expo χ₂ τ)) := by
    intro Q S Z hZ
    refine eq_of_forall₂ (forall₂_R Z τ) ?_
    rw [hZ]
    refine List.rel_append ?_ ?_
    · exact List.forall₂_map_left_iff.2 (List.forall₂_map_right_iff.2
        ((forall₂_R Q τ).imp fun _ _ h => R_twPart χ₁ h))
    · exact List.forall₂_map_left_iff.2 (List.forall₂_map_right_iff.2
        ((forall₂_R S τ).imp fun _ _ h => R_twPart χ₂ h))
  have e : infs D τ = infs D' τ := by
    rw [hI hJ, hI hJ', infs_eq_of_strict ha, infs_eq_of_strict hb]
  unfold infs at e
  rw [List.ofFn_congr hc.symm (fun j => D'.m j τ)] at e
  have := congrFun (List.ofFn_injective e) i
  simpa using this

end PositivityTheory.Rg.BcB.F.FX.Bo

end
end

section

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcB.F.F5 PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.BcB.SpectralAccumulation
open scoped Classical



attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.BcB.F.FX.Bo

theorem AdmProd_holds : AdmProd := by
  intro E _ _ _ n P w K hKo hKle
  have hadm := GlobalTheory.CompanionTheory.ProdAdm.isAdmissible_multiProd_smIrr (w.adicCompletion E) P.N P.h (fun i => P.σ i w)
  have hKc : IsCompact (K : Set (GLw n w)) :=
    (GlobalTheory.CompanionTheory.IwLevels.isCompact_KGL w n).of_isClosed_subset (K.isClosed_of_isOpen hKo) hKle
  exact hadm.2 K hKo hKc

end PositivityTheory.Rg.BcB.F.FX.Bo

end
end

section

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcB.F.F5 PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.BcB.SpectralAccumulation
open scoped Classical



attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.BcB.F.FX.Bo

open PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.RS

namespace StrictEquivalence

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem siso_symm (x y : Σ M : ℕ, Submodule ℂ (Sm E M)) (hx : _root_.GlobalTheory.CuspRep.IsStable x.2) (h : SIso x y) : SIso y x := by
  obtain ⟨x1, x2⟩ := x
  obtain ⟨y1, y2⟩ := y
  obtain ⟨h, hI⟩ := h
  simp only at h
  subst h
  exact ⟨rfl, F5.Bo.isoV_symm' hx hI⟩

theorem siso_trans (x y z : Σ M : ℕ, Submodule ℂ (Sm E M)) (h : SIso x y) (h' : SIso y z) : SIso x z := by
  obtain ⟨x1, x2⟩ := x
  obtain ⟨y1, y2⟩ := y
  obtain ⟨z1, z2⟩ := z
  obtain ⟨h, hI⟩ := h
  obtain ⟨h', hI'⟩ := h'
  simp only at h h'
  subst h h'
  exact ⟨rfl, F5.Bo.isoV_trans' hI hI'⟩

theorem forall₂_flip_of {α : Type} {R S : α → α → Prop} {p : α → Prop} (hRS : ∀ x y, p x → R x y → S y x) :
    ∀ {l l' : List α}, (∀ x ∈ l, p x) → List.Forall₂ R l l' → List.Forall₂ S l' l
  | _, _, _, List.Forall₂.nil => List.Forall₂.nil
  | _, _, hp, List.Forall₂.cons hab htl =>
      List.Forall₂.cons (hRS _ _ (hp _ (List.mem_cons_self ..)) hab)
        (forall₂_flip_of hRS (fun x hx => hp x (List.mem_cons_of_mem _ hx)) htl)

theorem forall₂_trans_of {α : Type} {R : α → α → Prop} (hR : ∀ x y z, R x y → R y z → R x z) :
    ∀ {l l' l'' : List α}, List.Forall₂ R l l' → List.Forall₂ R l' l'' → List.Forall₂ R l l''
  | _, _, _, List.Forall₂.nil, List.Forall₂.nil => List.Forall₂.nil
  | _, _, _, List.Forall₂.cons hab htl, List.Forall₂.cons hbc htl' =>
      List.Forall₂.cons (hR _ _ _ hab hbc) (forall₂_trans_of hR htl htl')

theorem parts_stable {n : ℕ} (P : Pre E n) : ∀ x ∈ parts P, _root_.GlobalTheory.CuspRep.IsStable x.2 := by
  intro x hx
  rw [parts, List.mem_ofFn] at hx
  obtain ⟨i, rfl⟩ := hx
  exact (P.discrete i).stable

end StrictEquivalence

open StrictEquivalence in
theorem StrictEqv_holds : StrictEqv := by
  intro E _ _ _ n P P' P''
  refine ⟨fun ⟨hF, hc, hm⟩ => ⟨forall₂_flip_of (p := fun x => _root_.GlobalTheory.CuspRep.IsStable x.2) (fun x y hx h => siso_symm x y hx h)
      (parts_stable P) hF, hc.symm, fun i => ?_⟩, fun ⟨hF, hc, hm⟩ ⟨hF', hc', hm'⟩ =>
      ⟨forall₂_trans_of siso_trans hF hF', hc.trans hc', fun i => ?_⟩⟩
  · rw [hm (Fin.cast hc.symm i)]
    congr 1
  · rw [hm i, hm' (Fin.cast hc i)]
    congr 1

end PositivityTheory.Rg.BcB.F.FX.Bo

end
end

section

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcB.F.F5 PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.BcB.SpectralAccumulation
open scoped Classical



attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.BcB.F.FX.Bo

open PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.RS

theorem StrictProd_holds : StrictProd := by
  intro E _ _ _ n P P' hS w
  obtain ⟨c, N, h, V, σ, m, pos, disc, loc, inf⟩ := P
  obtain ⟨c', N', h', V', σ', m', pos', disc', loc', inf'⟩ := P'
  obtain ⟨hF, hc, -⟩ := hS
  simp only at hc
  subst hc
  have key : ∀ i : Fin c, SIso (E := E) ⟨N i, V i⟩ ⟨N' i, V' i⟩ := by
    intro i
    have := (List.forall₂_iff_get.1 hF).2 i.1 (by simp [parts]) (by simp [parts])
    simpa [parts] using this
  have hN : N = N' := funext fun i => (key i).1
  subst hN
  have hσ : ∀ i, Nonempty ((σ i w).ρ.Equiv (σ' i w).ρ) := by
    intro i
    obtain ⟨hNi, hiso⟩ := key i
    have hl : IsLocCompGL (V' i) w (σ i w) := Bo.LocIso_holds E (N i) (V i) (V' i) hiso w (σ i w) (loc i w)
    exact GlobalTheory.LocGL.IrrGL.of_eq_of.1 (Bo.LocUniq_holds E (N i) (V' i) (disc' i) w _ _ hl (loc' i w))
  exact ⟨GlobalTheory.LocGL.multiProdEquiv _ fun i => (hσ i).some⟩

end PositivityTheory.Rg.BcB.F.FX.Bo

end
end
