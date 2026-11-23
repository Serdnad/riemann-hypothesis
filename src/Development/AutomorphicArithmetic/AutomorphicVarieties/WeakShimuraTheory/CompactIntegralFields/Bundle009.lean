module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.NearSplit
public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.Bundle007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.FerreroWashington
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RealPlaceConjugation.Bundle003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RealPlaceConjugation.BoundsExt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RealPlaceConjugation.KerQFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RealPlaceConjugation.KrFacts
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RealPlaceConjugation.PlacesBd
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RealPlaceConjugation.RankLocalCocycleSpacesLe
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdicLattices.Bundle001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdicLattices.Bundle002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdicLattices.OddVan
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdicLattices.TcSmall
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdicLattices.Vertex
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.Bundle001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.ContinuousResP
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.ContResQ
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RamifiedLineCharacters.Bundle003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RamifiedLineCharacters.GysinPsOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RamifiedLineCharacters.Bundle004
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RamifiedLineCharacters.SuppMMono
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
public import Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.ModulusAdjoinISqrtNegPrimes
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RbUVal
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdicLattices.CompanionTheory

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

theorem UpperTheory.V.Ws.x2 :
    CohomologyHyp → UpperTheory.V.Published.FerreroWashington → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c) (T : Tower D), T.Fit → TameL l T.F → ∃ C : ℕ, ∀ (T' : Tower D) (m : ℕ), T.Le T' → IsLayer l m T.F T'.F →
      ∀ (k : Type) [Field k] (a : c.O →+* k), (∀ x ∈ maximalIdeal c.O, a x = 0) → (T'.fr ∅).Bounds a T'.d C := by
  intro P hFW Ω _ _ _ l _ c D T hT _
  have hD : D.Good := hT.2.elim (fun h => h.1.1) fun h => h.1.1
  obtain ⟨ho, hc, hl⟩ := kerOverRationals_open_commutator_layer D hD T.F
  obtain ⟨r, hr⟩ := exists_iwasawaRank_bound_of_ferreroWashington hFW Ω l (kerQ D T.F) hD.l_odd ho hc inf_le_right
  have hN : (kerQ D T.F).Normal := ⟨fun x hx g => by
    have h : g * x * g⁻¹ * x⁻¹ ∈ kerQ D T.F := hc (Subgroup.commutator_mem_commutator (Subgroup.mem_top g) (Subgroup.mem_top x))
    simpa using mul_mem h hx⟩
  obtain ⟨g, hg⟩ := exists_uniform_bound_ncard_placesDividing Ω l (kerQ D T.F) (prodS D) hN ho (residualKernel_properties D hD T).2.2.2.2.2.2.1.1
  refine ⟨r + 2 + 2 * g, fun T' m _ hm k _ a ha => ?_⟩
  obtain ⟨e, hle⟩ := hl m T'.F hm
  have hg' := hg T'.F hle
  have hK : UpperTheory.V.Two.XRk l 1 T'.Kr r := (residualKernel_properties D hD T').2.2.2.2.2.2.2.2 r (e ▸ hr (m + 1))
  obtain ⟨b1, b2⟩ := rank_localCocycleSpaces_le P D hD T' g hg'
  obtain ⟨b3, b4, b5⟩ := rank_cocycleSpaces_le_of_towerIwasawaRank P D hD T' r g hg' hK
  have ea : a = (Ideal.Quotient.lift (maximalIdeal c.O) a ha : ResidueField c.O →+* k).comp (residue c.O) :=
    RingHom.ext fun _ => rfl
  rw [ea]
  refine cocycleBounds_of_ringHom_comp _ (ResidueField c.O) k _ _ _ _ ⟨b1.trans (by omega), fun w _ => (b3 w).trans (Nat.cast_le.2 (by omega)),
    fun w hw => (b4 w hw).trans (Nat.cast_le.2 (by omega)),
    fun w _ => (b5 w).trans (add_le_add le_rfl (Nat.cast_le.2 (by omega))),
    fun w _ => (b2 w).trans (add_le_add le_rfl (Nat.cast_le.2 (by omega)))⟩
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Lat

private theorem lat_six {Si : Set (ℤ × ℤ)} (h : CompanionTheory Si) (h1 : -wAl ∉ Si → -wTh ∉ Si) (h2 : wBe ∉ Si → wPs ∉ Si → -wAl ∉ Si) :
    wBe ∈ Si ∧ -wPs ∈ Si ∧ Si ⊆ nP := by
  rcases h with h | ⟨a, -, b⟩ | ⟨a, -, b⟩ | ⟨a, -, b⟩ | ⟨a, -, b⟩ | ⟨a, -, b⟩
  · exact h
  · exact absurd a (h2 (fun x => absurd (Finset.mem_coe.1 (b x)) (by decide)) fun x => absurd (Finset.mem_coe.1 (b x)) (by decide))
  · exact absurd a (h1 fun x => by simpa [wAl, wTh, wPs, wBe] using b x)
  · exact absurd a (h2 (fun x => absurd (Finset.mem_coe.1 (b x)) (by decide)) fun x => absurd (Finset.mem_coe.1 (b x)) (by decide))
  · exact absurd a (h1 fun x => by simpa [wAl, wTh, wPs, wBe] using b x)
  · exact absurd a (h1 fun x => by simpa [wAl, wTh, wPs, wBe] using b x)

theorem UpperTheory.V.Ws.lat :
    CohomologyHyp → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ∀ (𝔞 : Amb l) (pr : Bool) (g0 : G ℚ Ω), LabOk D pr →
      (∀ i j, i ≠ j → Raw.bar (chi D pr i) g0 ≠ Raw.bar (chi D pr j) g0) → ∀ P : PD Unit (G ℚ Ω) 𝔞.V, QPair D pr g0 𝔞 P → NearSplit D pr 𝔞 P → StarE P.r →
      ∃ P' : PD Unit (G ℚ Ω) 𝔞.V, QPair D pr g0 𝔞 P' ∧ IsConj4 (mapRep 𝔞.toK P.r) (mapRep 𝔞.toK P'.r) ∧ LatShape D pr g0 (𝔞.red c) (P'.map (residue 𝔞.V)) := by
  intro hP Ω _ _ _ l _ c D hD 𝔞 pr g0 _ hd P hQ hN hS
  obtain ⟨t, P', hT, h6⟩ := vertex 𝔞 P hQ.small (hQ.pair.low ())
    (fun g i j hij => by simpa [diagRep, Matrix.diagonal_apply_ne _ hij] using hN.red g i j) hN.flag hS
  obtain ⟨hp, hdg, hψ, hc⟩ := tcPair (frQ D pr g0) (𝔞.a c) 𝔞.toK Subtype.val_injective t P P' hT hQ.pair
  have hsm := tcSmall 𝔞 t P P' hT hQ.small
  have hred : ∀ x ∈ maximalIdeal c.O, 𝔞.red c x = 0 := fun x hx =>
    (residue_eq_zero_iff _).2 (map_nonunit (𝔞.a c) x hx)
  have hpre : PreRes (frQ D pr g0) (𝔞.red c) (P'.map (residue 𝔞.V)) := by
    refine ⟨hp.map _, fun g i => ?_, fun v s hs i => ?_, ?_⟩
    · refine Ideal.Quotient.eq.2 ?_
      rw [hdg]
      simpa [diagRep, frQ] using hN.red g i i
    · refine (PD.map_ψ P' _ v i s).trans (Ideal.Quotient.eq.2 ?_)
      exact (hψ v i s).symm ▸ hN.char s hs i
    · obtain ⟨A, _, _, _, f, P₁, hf, hcont, rfl⟩ := hsm
      haveI := hf.loc
      exact hcont.map ((residue 𝔞.V).comp f) fun x hx => (residue_eq_zero_iff _).2 (map_nonunit f x hx)
  have hmul : ∀ i g, (frQ D pr g0).χ i g * (frQ D pr g0).χ i.rev g = (frQ D pr g0).ν g := by
    intro i g
    cases pr <;> fin_cases i <;> simp [frQ, chi, lab, Raw.ps, Raw.th, Fin.rev, mul_comm]
  have hE := entVan _ _ _ hpre hmul (oddVan D hD hP.loc _ _ hred pr g0 hd)
  obtain ⟨n1, n2⟩ := noNeg _ _ _ hpre hE
  obtain ⟨s1, s2, s3⟩ := lat_six h6 n1 n2
  obtain ⟨u1, u2, u3, u4⟩ := shape _ _ _ hpre hE s1 s2 s3
  refine ⟨P', ⟨hsm, hp, fun s hs i => (hψ () i s).trans (hQ.inert s hs i)⟩, hc,
    ⟨hpre.pair, ⟨hpre.diag, hpre.char, .inl ⟨u1, u2⟩⟩, hpre.cont⟩, u1, u2 (), u3, u4.imp id ?_⟩
  rintro ⟨v1, ⟨v, v2, v3⟩, v4⟩
  refine ⟨v1, v2, fun s hs => ?_, fun ⟨m, hm⟩ => v4 ⟨fun _ => m, fun _ => hm⟩⟩
  have e : Raw.bar (chi D pr 0) s = Raw.bar (chi D pr 2) s := (𝔞.j c).injective (v3 s hs)
  have hu : Raw.bar D.al s ≠ 0 := ((D.al s).isUnit.map (residue c.O)).ne_zero
  have ht : Raw.bar D.th s = Raw.bar D.al s * Raw.bar D.Psi s := map_mul (residue c.O) (D.al s : c.O) (D.Psi s : c.O)
  cases pr
  · exact (mul_eq_left₀ hu).1 (ht.symm.trans e)
  · exact (mul_eq_left₀ hu).1 (ht.symm.trans e.symm)
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

theorem UpperTheory.V.Ws.gysinAl :
    CohomologyHyp → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c) (T : Tower D), T.Fit → ∀ (k : Type) [Field k] (a : c.O →+* k), (∀ x ∈ maximalIdeal c.O, a x = 0) → ∀ W : Finset ℕ, (∀ w ∈ W, w.Prime ∧ T.Splits w) → ∀ p p' : PD T.ι (G T.F Ω) k, (T.fr W).IsRes a p → (T.fr W).IsRes a p' → p.In nP → p'.In nP →
      ∃ (W' : Finset ℕ) (s s' : PD T.ι (G T.F Ω) k), W ⊆ W' ∧ (∀ w ∈ W', w.Prime ∧ T.Splits w) ∧ (T.fr W').IsRes a s ∧ (T.fr W').IsRes a s' ∧
        s.In qQ ∧ s'.In qQ ∧ s.SamePs p ∧ s'.SamePs p' ∧ s.SameAl s' ∧ Ent s.r (-wAl) := by
  intro P Ω _ _ _ l _ c D T hT k _ a ha W hW p p' hp hp' hs hs'
  have ok := fun W => (std P D T hT W c le_rfl).2 k a ha
  obtain ⟨r1, -, r3⟩ := Gys.rootCharacters_ne_one_at_basepoint (T.fr W) a (ok W)
  obtain ⟨y, y1, y2, y3, y4⟩ := Gys.dataPs (T.fr W) a p hp hs.1
  obtain ⟨y', y1', y2', y3', y4'⟩ := Gys.dataPs (T.fr W) a p' hp' hs'.1
  obtain ⟨W', s1, s2, hy, x, m, x1, x2, x3, ⟨g, hg⟩, hz⟩ := Gys.cupEx P D T hT k a ha W hW (-wAl) (-wPs) r1 r3 Bool
    (fun b => cond b y y') fun b => by cases b; exacts [⟨y1', y2'⟩, ⟨y1, y2⟩]
  obtain ⟨z, z1, z2⟩ := hz true
  obtain ⟨z', z1', z2'⟩ := hz false
  have hmu := Gys.mu_of (T.fr W) a hp fun v s hs => hs.1
  obtain ⟨s, a1, a2, a3, a4, a5, a6⟩ := Gys.ob (T.fr W') a (ok W') hmu x y z m _ x1 x2 x3 (hy true) y2 y3 z1 z2
  obtain ⟨s', b1, b2, b3, b4, b5, b6⟩ := Gys.ob (T.fr W') a (ok W') hmu x y' z' m _ x1 x2 x3 (hy false) y2' y3' z1' z2'
  exact ⟨W', s, s', s1, s2, a1, b1, a2, b2, ⟨fun g => (a5 g).trans (y4 g).symm, a6⟩, ⟨fun g => (b5 g).trans (y4' g).symm, b6⟩,
    ⟨fun g => (a3 g).trans (b3 g).symm, fun v => (a4 v).trans (b4 v).symm⟩, g, 1, 0, by decide,
    a3 g ▸ mul_ne_zero hg (((T.fr W').χ 0 g).isUnit.map a).ne_zero⟩
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

theorem UpperTheory.V.Ws.gysinPs :
    CohomologyHyp → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c) (T : Tower D), T.Fit → ∀ (k : Type) [Field k] (a : c.O →+* k), (∀ x ∈ maximalIdeal c.O, a x = 0) → ∀ W : Finset ℕ, (∀ w ∈ W, w.Prime ∧ T.Splits w) → ∀ p : PD T.ι (G T.F Ω) k, (T.fr W).IsRes a p → Supp nM p.r →
      ∃ (W' : Finset ℕ) (s : PD T.ι (G T.F Ω) k), W ⊆ W' ∧ (∀ w ∈ W', w.Prime ∧ T.Splits w) ∧ (T.fr W').IsRes a s ∧ s.In qQ ∧ s.SameAl p ∧ Ent s.r (-wPs) :=
  UpperTheory.V.Ws.Gys.gysinPs_of
end
