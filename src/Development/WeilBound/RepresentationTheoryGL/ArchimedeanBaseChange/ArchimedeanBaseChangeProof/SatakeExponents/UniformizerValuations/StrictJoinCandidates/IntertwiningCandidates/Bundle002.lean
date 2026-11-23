module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.StrictJoinCandidates.IntertwiningCandidates.StrictJoin
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.FiniteDiscreteFamilies.LocalCompatibilityGL.Bundle002
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.IwahoriPairLeMaximal
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle565
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.AdelicHeckeBlocks.PPositions
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.PolynomialPairSpaces.Bundle001
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

@[expose] public section

section

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcB.F.F5 PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.BcB.SpectralAccumulation
open scoped Classical



attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.BcB.F.FX.Bo

open PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.RS

namespace StrictPreorder

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem forall₂_ofFn {α β : Type} {R : α → β → Prop} {c c' : ℕ} (h : c = c') (f : Fin c → α) (g : Fin c' → β)
    (hR : List.Forall₂ R (List.ofFn f) (List.ofFn g)) (i : Fin c) : R (f i) (g (Fin.cast h i)) := by
  subst h
  have := hR.get (i := i.1) (by simp) (by simp)
  simpa using this

theorem cls_eq (x y : Σ M : ℕ, Submodule ℂ (Sm E M)) (hxy : SIso x y) (hy : IsDiscrete y.2)
    (w : HeightOneSpectrum (𝓞 E)) (σ : SmIrr (GL (Fin x.1) (w.adicCompletion E)))
    (σ' : SmIrr (GL (Fin y.1) (w.adicCompletion E))) (hσ : IsLocCompGL x.2 w σ) (hσ' : IsLocCompGL y.2 w σ') :
    GlobalTheory.LocGL.IrrGL.of σ.ρ σ.smooth σ.irred = GlobalTheory.LocGL.IrrGL.of σ'.ρ σ'.smooth σ'.irred := by
  obtain ⟨x1, x2⟩ := x
  obtain ⟨y1, y2⟩ := y
  obtain ⟨h, hI⟩ := hxy
  simp only at h
  subst h
  exact F5.Bo.LocUniq_holds E x1 y2 hy w σ σ' (F5.Bo.LocIso_holds E x1 x2 y2 hI w σ hσ) hσ'

end StrictPreorder

theorem StrictPre_holds : StrictPre := by
  intro E _ _ _ n P P' hS
  obtain ⟨hF, hc, hm⟩ := hS
  refine ⟨finCongr hc, fun i w => ?_, fun i τ => congrFun (hm i) τ⟩
  have hI : SIso ⟨P.N i, P.V i⟩ ⟨P'.N (Fin.cast hc i), P'.V (Fin.cast hc i)⟩ :=
    StrictPreorder.forall₂_ofFn hc (fun j => (⟨P.N j, P.V j⟩ : Σ M : ℕ, Submodule ℂ (Sm E M)))
      (fun j => (⟨P'.N j, P'.V j⟩ : Σ M : ℕ, Submodule ℂ (Sm E M))) hF i
  exact StrictPreorder.cls_eq _ _ hI (P'.discrete _) w (P.σ i w) (P'.σ _ w) (P.loc i w) (P'.loc _ w)

end PositivityTheory.Rg.BcB.F.FX.Bo

end
end

section

noncomputable section

open NumberField IsDedekindDomain Matrix Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcB.F.F5 PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.BcB.SpectralAccumulation
open PositivityTheory.Rg.BcB.G8
open scoped Classical



attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.BcB.F.FX.Bo.LevelOpenness

open PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.BcB.F.Rd.LevOC

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

def LOk (d : LocData E n) : Prop :=
  ∀ a ≤ n, ∀ w ∈ d.S₀ ∪ d.Bad, IsOpen (d.L a w : Set (GLw a w × GLw (n - a) w))

theorem LOk_of_ok (d : LocData E n) (hd : d.Ok) : LOk d := fun a ha w hw => (L_open_le d hd a ha w hw).1

theorem lev_open (d : LocData E n) (hd : LOk d) (a : ℕ) (ha : a ≤ n) (w : Pl E) :
    IsOpen (d.lev a w : Set (GLw a w × GLw (n - a) w)) := by
  unfold LocData.lev
  split_ifs with h1 h2
  · exact iwahori_pair_isOpen a (n - a) w
  · exact hd a ha w h2
  · exact maximal_pair_isOpen a (n - a) w

theorem lev₂_open (d : LocData E n) (hd : LOk d) (a : ℕ) (ha : a ≤ n) (w : Pl E) :
    IsOpen (d.lev₂ a w : Set (GLw a w × GLw (n - a) w)) := by
  unfold LocData.lev₂
  split_ifs with h2
  · exact hd a ha w h2
  · exact maximal_pair_isOpen a (n - a) w

theorem C_open (d : LocData E n) (hd : LOk d) (a : ℕ) (ha : a ≤ n) {S : Set (Pl E)} (i : Slot S) :
    IsOpen (C d a i) := by
  rcases i with w | w
  · exact lev_open d hd a ha w.1
  · exact lev₂_open d hd a ha w.1

theorem gSet_open' (hSl : Slots) {Sec : Set (Pl E)} (hS : IsSection Sec) (d : LocData E n) (hd : LOk d) (a : ℕ)
    (ha : a ≤ n) : IsOpen (gSet Sec d a) := by
  have hSl' := hSl E a (n - a) Sec hS
  obtain ⟨hKo1, -⟩ := GlobalTheory.T.finite_kernel_compact_open E a
  obtain ⟨hKo2, -⟩ := GlobalTheory.T.finite_kernel_compact_open E (n - a)
  set U : Set (Hf E a (n - a)) := (((Kf E a).prod (Kf E (n - a)) : Subgroup (Hf E a (n - a))) : Set (Hf E a (n - a)))
    with hU
  have hUo : IsOpen U := by
    rw [hU, Subgroup.coe_prod]
    exact hKo1.prod hKo2
  have hF := (Filter.eventually_cofinite.1 (C_cof d a (S := Sec)))
  set V : Set (Hf E a (n - a)) := U ∩ ⋂ i ∈ {i : Slot Sec | ¬ C d a i = (K2 a (n - a) i.pl : Set _)},
    (i.cp a (n - a)) ⁻¹' C d a i with hV
  have hVo : IsOpen V :=
    hUo.inter (hF.isOpen_biInter fun i _ => (C_open d hd a ha i).preimage (hSl'.2.1 i))
  have h1V : (1 : Hf E a (n - a)) ∈ V := by
    refine ⟨one_mem _, Set.mem_iInter₂.2 fun i _ => ?_⟩
    have h1 : (1 : Hf E a (n - a)) ∈ gSet Sec d a := (levSub Sec d a).one_mem
    rw [gSet_eq] at h1
    exact h1 i
  have hVsub : V ⊆ gSet Sec d a := by
    intro x hx
    rw [gSet_eq]
    intro i
    by_cases hi : C d a i = (K2 a (n - a) i.pl : Set _)
    · rw [hi]
      exact (hSl'.2.2.2.2.2.1 x).1 hx.1 i
    · exact Set.mem_iInter₂.1 hx.2 i hi
  exact Subgroup.isOpen_of_mem_nhds (levSub Sec d a) (g := 1) (Filter.mem_of_superset (hVo.mem_nhds h1V) hVsub)

theorem g₁_open (hSl : Slots) {Sec : Set (Pl E)} (hS : IsSection Sec) (d : LocData E n) (hd : LOk d) (a : ℕ)
    (ha : a ≤ n) : IsOpen (g₁ Sec d a : Set (GL (Fin a) (Af E))) := by
  rw [g₁_coe]
  exact (gSet_open' hSl hS d hd a ha).preimage (continuous_id.prodMk continuous_const)

theorem g₂_open (hSl : Slots) {Sec : Set (Pl E)} (hS : IsSection Sec) (d : LocData E n) (hd : LOk d) (a : ℕ)
    (ha : a ≤ n) : IsOpen (g₂ Sec d a : Set (GL (Fin (n - a)) (Af E))) := by
  rw [g₂_coe]
  exact (gSet_open' hSl hS d hd a ha).preimage (continuous_const.prodMk continuous_id)

theorem loc_LOk {hR : Rd.ReadLimit} {π : Submodule ℂ (UA E n → ℂ)} {S : Finset (Pl E)} (F₀ : Frame0 hR π S)
    (T' : Finset (Pl E)) c e b : LOk (F₀.loc T' c e b) :=
  fun a ha w hw => LOk_of_ok F₀.d₀ F₀.ok₀ a ha w hw

end PositivityTheory.Rg.BcB.F.FX.Bo.LevelOpenness

namespace PositivityTheory.Rg.BcB.F.FX.Bo

open PositivityTheory.Rg.BcB.F

theorem LevOpen_holds : LevOpen := by
  intro hR E _ _ _ n π S F₀ T' c e b a ha
  have hd := LevelOpenness.loc_LOk F₀ T' c e b
  exact ⟨LevelOpenness.g₁_open slots F₀.hSec _ hd a ha, LevelOpenness.g₂_open slots F₀.hSec _ hd a ha⟩

end PositivityTheory.Rg.BcB.F.FX.Bo

end
end

section

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcB.F.F5 PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.BcB.SpectralAccumulation

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.BcB.F.FX.Bo.Tw.StrictJoinAlt

open PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.BcB.F.FX.Bo

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem hasInf_map {a : ℕ} {V : Submodule ℂ (Sm E a)} {τ : E →+* ℂ} {m : Multiset ℂ}
    (h : HasInfCharGL V τ m) (χ : HChar E) :
    HasInfCharGL (V.map (mulChi a χ).toLinearMap) τ (m.map (· + expo χ τ)) := by
  refine ⟨by rw [Multiset.card_map]; exact h.1, ?_⟩
  rintro u _ ⟨φ, hφ, rfl⟩
  change cap τ u (mulChi a χ φ) = _ • mulChi a χ φ
  rw [cap_mulChi, h.2 _ φ hφ, map_smul, Multiset.map_map]
  congr 2
  exact Multiset.map_congr rfl fun x _ => by simp only [Function.comp_apply]; ring

theorem isoV_map {a : ℕ} {V V' : Submodule ℂ (Sm E a)} (hV : IsoV V V') (χ : HChar E) :
    IsoV (V.map (mulChi a χ).toLinearMap) (V'.map (mulChi a χ).toLinearMap) := by
  obtain ⟨T, hT⟩ := hV
  let M := mulChi a χ
  refine ⟨((M.submoduleMap V).symm.trans T).trans (M.submoduleMap V'), ?_⟩
  intro o φ ψ hψ
  set φ₀ := (M.submoduleMap V).symm φ with hφ₀
  set ψ₀ := (M.submoduleMap V).symm ψ with hψ₀
  have eφ : φ.1 = M φ₀.1 := by
    have := congrArg Subtype.val ((M.submoduleMap V).apply_symm_apply φ); rw [← this]; rfl
  have eψ : ψ.1 = M ψ₀.1 := by
    have := congrArg Subtype.val ((M.submoduleMap V).apply_symm_apply ψ); rw [← this]; rfl
  have key : ψ₀.1 = ((opMul χ o : ℂˣ) : ℂ) • act o φ₀.1 + opAdd χ o • φ₀.1 := by
    apply M.injective
    rw [← eψ, hψ, eφ]
    exact act_mulChi χ o φ₀.1
  have hmem : act o φ₀.1 ∈ V := by
    have : act o φ₀.1 = ((opMul χ o : ℂˣ) : ℂ)⁻¹ • (ψ₀.1 - opAdd χ o • φ₀.1) := by
      rw [key, add_sub_cancel_right, smul_smul, inv_mul_cancel₀ (Units.ne_zero _), one_smul]
    rw [this]
    exact V.smul_mem _ (V.sub_mem ψ₀.2 (V.smul_mem _ φ₀.2))
  have hψ' : ψ₀ = ((opMul χ o : ℂˣ) : ℂ) • (⟨act o φ₀.1, hmem⟩ : V) + opAdd χ o • φ₀ := Subtype.ext key
  have h1 := hT o φ₀ ⟨act o φ₀.1, hmem⟩ rfl
  change (M (T ψ₀).1) = act o (M (T φ₀).1)
  rw [act_mulChi, hψ', map_add (f := _), map_smul, map_smul]
  simp only [Submodule.coe_add, Submodule.coe_smul, h1]
  rfl

theorem sIso_tw {x y : Σ M : ℕ, Submodule ℂ (Sm E M)} (h : SIso x y) (χ : HChar E) :
    SIso (twPart χ x) (twPart χ y) := by
  obtain ⟨N, V⟩ := x
  obtain ⟨N', V'⟩ := y
  obtain ⟨e, hi⟩ := h
  dsimp only at e
  subst e
  exact ⟨rfl, isoV_map hi χ⟩

def SInf (x y : Σ M : ℕ, Submodule ℂ (Sm E M)) : Prop :=
  ∀ τ, ∃ m, HasInfCharGL x.2 τ m ∧ HasInfCharGL y.2 τ m

theorem length_parts {n : ℕ} (P : Pre E n) : (parts P).length = P.c := by simp [parts]

theorem sInf_tw {a : ℕ} {P P' : Pre E a} (h : Strict P P') (χ : HChar E) :
    List.Forall₂ SInf ((parts P).map (twPart χ)) ((parts P').map (twPart χ)) := by
  obtain ⟨hc, hm⟩ := h.2
  rw [List.forall₂_iff_get]
  refine ⟨by simp [length_parts, hc], fun i h₁ h₂ => ?_⟩
  intro τ
  have hi : i < P.c := by simpa [length_parts] using h₁
  refine ⟨(P.m ⟨i, hi⟩ τ).map (· + expo χ τ), ?_, ?_⟩
  · have e : ((parts P).map (twPart χ)).get ⟨i, h₁⟩ = twPart χ ⟨P.N ⟨i, hi⟩, P.V ⟨i, hi⟩⟩ := by
      simp [parts]
    rw [e]
    exact hasInf_map (P.inf _ τ) χ
  · have e : ((parts P').map (twPart χ)).get ⟨i, h₂⟩ =
        twPart χ ⟨P'.N (Fin.cast hc ⟨i, hi⟩), P'.V (Fin.cast hc ⟨i, hi⟩)⟩ := by
      simp [parts]
    rw [e, hm ⟨i, hi⟩]
    exact hasInf_map (P'.inf _ τ) χ

theorem strict_of {n : ℕ} {P P' : Pre E n} (h₁ : List.Forall₂ SIso (parts P) (parts P'))
    (h₂ : List.Forall₂ SInf (parts P) (parts P')) : Strict P P' := by
  have hc : P.c = P'.c := by rw [← length_parts, ← length_parts]; exact h₂.length_eq
  refine ⟨h₁, hc, fun i => funext fun τ => ?_⟩
  have hi : i.1 < (parts P).length := by rw [length_parts]; exact i.2
  have hi' : i.1 < (parts P').length := by rw [length_parts, ← hc]; exact i.2
  obtain ⟨m, hm, hm'⟩ := (List.forall₂_iff_get.1 h₂).2 i.1 hi hi' τ
  have e : (parts P).get ⟨i.1, hi⟩ = ⟨P.N i, P.V i⟩ := by simp [parts]
  have e' : (parts P').get ⟨i.1, hi'⟩ = ⟨P'.N (Fin.cast hc i), P'.V (Fin.cast hc i)⟩ := by
    simp only [parts, List.get_ofFn]; rfl
  rw [e] at hm
  rw [e'] at hm'
  have e1 := LemDd.InfUniq_holds E _ _ τ _ _ (P.discrete i).ne_bot (P.inf i τ) hm
  have e2 := LemDd.InfUniq_holds E _ _ τ _ _ (P'.discrete _).ne_bot (P'.inf _ τ) hm'
  rw [e1, e2]

end PositivityTheory.Rg.BcB.F.FX.Bo.Tw.StrictJoinAlt

namespace PositivityTheory.Rg.BcB.F.FX.Bo.Tw

open PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.BcB.F.FX.Bo StrictJoinAlt

theorem StrictJoin_holds : StrictJoin := by
  intro E _ _ _ n a b χ₁ χ₂ Pa Pa' Pb Pb' D D' hJ hJ' ha hb
  refine strict_of ?_ ?_
  · rw [hJ, hJ']
    exact List.rel_append
      (List.forall₂_map_left_iff.2 (List.forall₂_map_right_iff.2 (ha.1.imp fun _ _ h => sIso_tw h χ₁)))
      (List.forall₂_map_left_iff.2 (List.forall₂_map_right_iff.2 (hb.1.imp fun _ _ h => sIso_tw h χ₂)))
  · rw [hJ, hJ']
    exact List.rel_append (sInf_tw ha χ₁) (sInf_tw hb χ₂)

end PositivityTheory.Rg.BcB.F.FX.Bo.Tw

end
end
