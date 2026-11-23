module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.PartitionSolutions.SplitFacts
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.PartitionSolutions.Bundle003
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.PartitionSolutions.Bundle001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.PartitionSolutions.ZigFormal
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.Bundle002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.Bundle005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.Bundle003
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
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open UpperTheory.V.Cj.A UpperTheory.V.Lit UpperTheory.V.Lit.Dr UpperTheory.V.Lit.Geo

private theorem van_dOm {Γ V S I : Type} [Group Γ] [NormedAddCommGroup V] [NormedSpace ℝ V] {d : ℕ}
    (G : Dr.Geo Γ V S d) (C : I → S → Set V) (F : S → Set V) (hC : ∀ i s, IsOpen (C i s))
    (hF : ∀ s, IsOpen (F s)) {q : ℕ} (k : ℕ) (b : List I → G.Om q) (hb : Van G C F k b) :
    Van G C F k (fun x => G.dOm q (b x)) := by
  intro x hx s p hp hxC
  beta_reduce
  by_cases hY : p ∈ G.Y
  · rw [G.dOm_apply (b x) s hY]
    have hW : IsOpen (F s ∩ ⋂ i ∈ {i | i ∈ x}, C i s) :=
      (hF s).inter ((List.finite_toSet x).isOpen_biInter (fun i _ => hC i s))
    have hev : ((b x : G.Om q) : S → V → V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)) s =ᶠ[nhds p] fun _ => 0 := by
      filter_upwards [hW.mem_nhds ⟨hp, Set.mem_iInter₂.mpr hxC⟩] with y hy
      exact hb x hx s y hy.1 (fun i hi => Set.mem_iInter₂.mp hy.2 i hi)
    rw [extDeriv, hev.fderiv_eq, fderiv_const_apply]
    exact map_zero (ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ V (Fin d → ℂ))
  · exact ((G.dOm q (b x)).2 s).2 p hY

theorem UpperTheory.V.Cj.A.zigBwd :
    ZigBwd := by
  intro Γ V S I _ _ _ _ _ d G hY hne φ hφ C F hC hF hφC n c hc hdc hvc q
  obtain ⟨-, -, -, hhom, -, -⟩ := hdFacts
  obtain ⟨hi1, -, hi3⟩ := inclFacts Γ V S d G hY hne
  induction q with
  | zero =>
    intro k hk
    obtain rfl : k = n := by omega
    refine ⟨fun x => G.incl (c x), fun x _ => rfl, fun γ x hx => ?_, fun x _ => hi3.apply_apply_eq_zero _,
      fun x hx => ?_, fun x hx s p _ hp => ?_⟩
    · beta_reduce
      rw [hc γ x hx, hi1]
    · refine (hhom I _ _ G.incl.toAddMonoidHom c x).trans ?_
      rw [hdc x hx, map_zero]
    · by_cases hpY : p ∈ G.Y
      · ext1 v
        rw [G.incl_apply _ _ hpY, hvc x hx s p hp]
        rfl
      · exact ((G.incl (c x)).2 s).2 p hpY
  | succ q ih =>
    intro k hk
    obtain ⟨u, hz, hu, hdu, hhu, hvu⟩ := ih (k + 1) (by omega)
    obtain ⟨b, hb, hhb, hvb⟩ := bwdStep Γ V S I d G φ hφ C F hφC q k u hu hhu hvu
    refine ⟨fun x => G.dOm q (b x), ⟨b, hb, fun _ _ => rfl, ?_⟩, fun γ x hx => ?_,
      fun x _ => (dExact Γ V S d G hY q).apply_apply_eq_zero _, fun x hx => ?_,
      van_dOm G C F hC.isOpen hF k b hvb⟩
    · exact (zigFormal Γ V S I d G).1 q (k + 1) u (hd b) c (fun x hx => (hhb x hx).symm) hz
    · beta_reduce
      rw [hb γ x hx, dEquiv]
    · refine (hhom I _ _ (G.dOm q).toAddMonoidHom b x).trans ?_
      rw [hhb x hx]
      exact hdu x hx
end

section

open UpperTheory.V.Cj.A UpperTheory.V.Lit.Geo

theorem UpperTheory.V.Cj.A.bwdLast :
    BwdLast := by
  intro Γ V S I _ _ _ _ d G φ hφ C F hC q u hu hhd hvan
  obtain ⟨P, hP1, hPeq, hPvan⟩ := partOp Γ V S I d G φ hφ q
  have hconst : ∀ i j : I, u [i] = u [j] := by
    intro i j
    have h := hhd [i, j] rfl
    simp [UpperTheory.V.Lit.Geo.hd, Finset.sum_range_succ] at h
    have h' : u [j] - u [i] = 0 := by
      rw [sub_eq_add_neg]
      simpa using h
    exact (sub_eq_zero.mp h').symm
  refine ⟨P (fun i => u [i]), ?_, ?_, ?_⟩
  · intro γ
    have hinv : (fun i => (G.act q) γ (u [γ⁻¹ • i])) = fun i => u [i] := by
      funext i
      have h := hu γ [γ⁻¹ • i] rfl
      simp only [List.map_cons, List.map_nil, smul_inv_smul] at h
      exact h.symm
    rw [← hPeq γ (fun i => u [i]), hinv]
  · intro x hx
    match x, hx with
    | [i], _ =>
      have hfun : (fun j => u [j]) = fun _ => u [i] := by
        funext j
        exact hconst j i
      rw [hfun, hP1]
  · intro s p hp
    apply hPvan
    intro i hne
    refine hvan [i] rfl s p hp ?_
    intro i' hi'
    rw [List.mem_singleton] at hi'
    rw [hi']
    exact hC i s p hp hne
end

section

open UpperTheory.V.Cj.A

theorem UpperTheory.V.Cj.A.fwdStep :
    FwdStep := by
  intro Γ V S I _ _ _ _ _ d G hY r hr C hC q k u hu hcl hvan
  classical
  have hex : ∀ y : List I, y.length = k + 1 → ∃ η : G.Om q, G.dOm q η = u y ∧
      ∀ s, ∀ p ∈ {p | ∀ i ∈ y, p ∈ C i s}, (η : S → V → V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)) s p = 0 := by
    intro y hy
    obtain ⟨i0, t, rfl⟩ : ∃ i t, y = i :: t := by
      cases y with
      | nil => simp at hy
      | cons i t => exact ⟨i, t, rfl⟩
    refine relPrim Γ V S d G hY (fun s => {p | ∀ i ∈ i0 :: t, p ∈ C i s}) (fun s => ⟨?_, ?_⟩) q
      (u (i0 :: t)) (hcl _ hy) ?_
    · intro a ha b hb t1 t2 h1 h2 h i hi
      exact hC.convex i s (ha i hi) (hb i hi) h1 h2 h
    · intro p hp
      exact hC.sub i0 s (hp i0 List.mem_cons_self)
    · intro s p hp
      exact hvan _ hy s p (Set.mem_univ _) hp
  choose η hη using hex
  have hηc : ∀ (y y' : List I) (h : y.length = k + 1) (h' : y'.length = k + 1), y = y' → η y h = η y' h' := by
    rintro y _ h h' rfl
    rfl
  let g : List I → Γ := fun x => (x.head?.map r).getD 1
  have hg : ∀ (γ : Γ) (x : List I), x ≠ [] → g (x.map (γ • ·)) = γ * g x := by
    intro γ x hx
    cases x with
    | nil => exact absurd rfl hx
    | cons i t => simp [g, hr]
  have hlen : ∀ x : List I, (x.map ((g x)⁻¹ • ·)).length = x.length := fun x => List.length_map ..
  refine ⟨fun x => if h : x.length = k + 1 then
      G.act q (g x) (η (x.map ((g x)⁻¹ • ·)) ((hlen x).trans h)) else 0, ?_, ?_, ?_⟩
  · intro γ x hx
    have hx' : (x.map (γ • ·)).length = k + 1 := by simpa using hx
    have hne : x ≠ [] := by
      rintro rfl
      simp at hx
    simp only [dif_pos hx, dif_pos hx']
    have hn : (x.map (γ • ·)).map ((g (x.map (γ • ·)))⁻¹ • ·) = x.map ((g x)⁻¹ • ·) := by
      rw [hg γ x hne, List.map_map]
      congr 1
      funext i
      simp [smul_smul]
    rw [hηc _ _ _ ((hlen x).trans hx) hn, hg γ x hne, map_mul]
    rfl
  · intro x hx
    simp only [dif_pos hx]
    rw [UpperTheory.V.Lit.Dr.dEquiv Γ V S d G q, (hη _ _).1, ← hu (g x) _ ((hlen x).trans hx)]
    congr 1
    simp [List.map_map, Function.comp_def, smul_smul]
  · intro x hx s p _ hp
    simp only [dif_pos hx]
    have hp' : G.ρ (g x)⁻¹ p ∈ {p | ∀ i ∈ x.map ((g x)⁻¹ • ·), p ∈ C i ((G.σ (g x)⁻¹) s)} := by
      intro i hi
      obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hi
      exact (hC.equiv _ j s p).2 (hp j hj)
    ext v
    rw [UpperTheory.V.Lit.Dr.Geo.act_apply, (hη _ _).2 _ _ hp']
    simp
end
