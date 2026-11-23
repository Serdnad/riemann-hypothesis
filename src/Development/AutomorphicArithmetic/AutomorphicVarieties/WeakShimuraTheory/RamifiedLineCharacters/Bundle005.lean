module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.Bundle007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RamifiedLineCharacters.MemRamLine
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RamifiedLineCharacters.Bundle002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RamifiedLineCharacters.Bundle003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RamifiedLineCharacters.Bundle004
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.Separation.CompletelyRegular

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

theorem UpperTheory.V.Ws.Gys.selBig :
    CohomologyHyp → ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (M : Type) [AddCommGroup M] [Module (ZMod (l ^ 1)) M] [Finite M] [TopologicalSpace M] [DiscreteTopology M], l ≠ 2 → ∀ (S₀ S : Finset (HeightOneSpectrum (𝓞 F))) (ρ : Representation (ZMod (l ^ 1)) (GS Ω (S : Set (HeightOneSpectrum (𝓞 F)))) M), S₀ ⊆ S → ContainsAbove S₀ l → ContAction ρ →
      (∀ v ∈ S, v ∉ S₀ → TrivAt l (ρ.comp (toGS Ω _)) v) → ∀ Av : S → ValuationSubring Ω, (∀ v, IsPlaceOver (Av v) v.1) → ∀ m0 : M, m0 ≠ 0 →
        2 ^ (S.card - S₀.card) ≤ Nat.card (gysSel S₀ S ρ Av m0) * (Nat.card (TDual (ZMod (l ^ 1)) M) * Nat.card M ^ (Module.finrank ℚ F + S₀.card)) := by
  classical
  intro P F Ω _ _ _ _ _ l _ M _ _ _ _ _ hl S₀ S ρ hSS hS₀ hρ htr Av hA m0 hm0
  have hS : ContainsAbove S l := fun v hv => hSS (hS₀ v hv)
  have e := gwLower P.gf P.gw F Ω l M hl S ρ hS hρ Av hA (gysL S₀ S ρ Av m0)
  have h0 : ∏ v : S, Nat.card (H0 (ρ.comp (locFam S Av v))) ≤ Nat.card M ^ S.card := by
    have := Finset.prod_le_pow_card Finset.univ (fun v : S => Nat.card (H0 (ρ.comp (locFam S Av v)))) (Nat.card M)
      (fun v _ => Nat.card_le_card_of_injective _ Subtype.val_injective)
    rwa [Finset.card_univ, Fintype.card_coe] at this
  have hloc : ∀ v : S, (if v.1 ∈ S₀ then 1 else 2 * Nat.card M) ≤ Nat.card (gysL S₀ S ρ Av m0 v) := by
    intro v
    by_cases hv : v.1 ∈ S₀
    · rw [if_pos hv, show gysL S₀ S ρ Av m0 v = ⊥ from if_pos hv]
      exact Nat.card_pos
    · rw [if_neg hv, show gysL S₀ S ρ Av m0 v = _ from if_neg hv]
      have ht := htr v.1 v.2 hv (Av v) (hA v)
      obtain ⟨φ₁, h1, φ₂, h2, a1, a2, g, a3, a4⟩ := locHoms P.loc.lt P.loc.le P.uo F Ω l (Av v) v.1 (hA v)
        (fun h => hv (hS₀ _ h)) (fun g hg => (ht g hg).2)
      have hc : ContAction (ρ.comp (locFam S Av v)) := hρ.comp ((continuous_locFam S Av v).prodMap continuous_id)
      obtain ⟨-, f1, -, -⟩ := P.loc.lf F Ω l 1 M (Av v) _ v.1 one_pos (hA v) hc
      exact ramCard _ _ M _ _ m0 (fun g => (ht g.1 g.2).1) hm0 f1 φ₁ h1 φ₂ h2 a1 a2 ⟨g, a3, a4⟩
  have h1 : (2 * Nat.card M) ^ (S.card - S₀.card) ≤ ∏ v : S, Nat.card (gysL S₀ S ρ Av m0 v) := by
    refine le_trans (le_of_eq ?_) (Finset.prod_le_prod' fun v _ => hloc v)
    rw [Finset.prod_coe_sort S (fun v => if v ∈ S₀ then 1 else 2 * Nat.card M), Finset.prod_ite, Finset.prod_const_one, one_mul,
      Finset.prod_const, ← Finset.sdiff_eq_filter, Finset.card_sdiff_of_subset hSS]
  have hpos : 0 < Nat.card M ^ (S.card - S₀.card) := pow_pos Nat.card_pos _
  refine Nat.le_of_mul_le_mul_right ?_ hpos
  rw [← mul_pow]
  refine h1.trans (e.trans ((Nat.mul_le_mul_left _ h0).trans (le_of_eq ?_)))
  have hc : Nat.card M ^ S.card = Nat.card M ^ S₀.card * Nat.card M ^ (S.card - S₀.card) := by
    rw [← pow_add, Nat.add_sub_cancel' (Finset.card_le_card hSS)]
  rw [hc, pow_add]
  ring
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

theorem UpperTheory.V.Ws.Gys.cupRaw :
    ∀ {O Γ k : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [Field k] (Φ : Fr O Γ) (a : O →+* k) (l : ℕ) [Fact l.Prime] [CharP k l], (Set.range a).Finite → Φ.Ok a → ∀ 𝒩 : Set Γ → Prop, Φ.Gys l 𝒩 → ∀ (w w' : ℤ × ℤ) (J : Type) [Finite J] (y : J → Γ → k), (∀ j, Φ.Coc a w' (y j)) →
      ∃ N', 𝒩 N' ∧ ∃ (x : Γ → k) (m : Φ.ι → k), (Φ.wN N').Coc a w x ∧ Φ.LocTriv a w x m ∧ (∃ g, a (Φ.rt w g) = 1 ∧ x g ≠ 0) ∧
        ∀ j, ∃ z, (Φ.wN N').Cup a w w' x (y j) z m := by
  intro O Γ k _ _ _ _ _ _ Φ a l _ _ hfin hok 𝒩 hG w w' J _ y hy
  obtain ⟨M, i1, i2, i3, i4, i5, ρ, p, q, m0, hc, hN, hp, hq, hm0, hpm⟩ :=
    Gys.extRep Φ a l hfin hok.lc w w' J y hy
  obtain ⟨N', hN', c, hcZ, hc0, hloc, g, hg1, hcg, hspan⟩ :=
    hG M ρ hc (fun g hg => hN g (hok.kill g hg) (fun j => (hy j).kill g hg)) m0 hm0
  obtain ⟨hcont, hcoc⟩ := (mem_Z1_iff_cocycle ρ c).1 hcZ
  have hlc : IsLocallyConstant c := (IsLocallyConstant.iff_continuous c).2 hcont
  have hrt : ∀ u, (Φ.wN N').rt u = Φ.rt u := fun u => rfl
  choose mm hmm using hloc
  have hpg : p (c g) ≠ 0 := hpm _ hspan hcg
  refine ⟨N', hN', fun s => p (c s), fun v => -p (mm v), ?_, ?_, ?_, ?_⟩
  · refine ⟨hlc.comp p, ?_, ?_⟩
    · intro s t
      rw [hrt, hcoc, map_add (f := _), hp]
    · intro s hs
      simp [hc0 s hs]
  · intro v s hs
    show p (c s) = -p (mm v) - a ↑((Φ.rt w) s) * -p (mm v)
    rw [hmm v s hs, map_sub, hp]
    ring
  · refine ⟨g, ?_, hpg⟩
    have h := hp g (c g)
    rw [hg1] at h
    change p (c g) = _ at h
    have h2 : (a ↑((Φ.rt w) g) - 1) * p (c g) = 0 := by linear_combination -h
    rcases mul_eq_zero.1 h2 with h3 | h3
    · exact sub_eq_zero.1 h3
    · exact absurd h3 hpg
  · intro j
    refine ⟨fun s => q j (c s), hlc.comp (q j), ?_, ?_, ?_⟩
    · intro s t
      simp only [hrt]
      rw [hcoc, map_add (f := _), hq]
      ring
    · intro s hs
      simp [hc0 s hs]
    · intro v
      refine ⟨-q j (mm v), fun s hs => ?_⟩
      simp only [hrt]
      rw [hmm v s hs, map_sub, hq]
      ring
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

section

variable {R Γ M : Type} [CommRing R] [Group Γ] [TopologicalSpace Γ] [AddCommGroup M] [Module R M] [TopologicalSpace M]
  [DiscreteTopology M]

private theorem coc_one {ρ : Representation R Γ M} {c : Γ → M} (hc : c ∈ Z1 ρ) : c 1 = 0 := by
  have h := hc.2 1 1
  simpa using h

private def killSub (ρ : Representation R Γ M) {c : Γ → M} (hc : c ∈ Z1 ρ) : Subgroup Γ where
  carrier := {g | ρ g = 1 ∧ c g = 0}
  one_mem' := ⟨map_one ρ, coc_one hc⟩
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    exact ⟨by rw [map_mul, ha, hb, one_mul], by rw [hc.2, ha', hb', map_zero, add_zero]⟩
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    have h1 : ρ a⁻¹ = 1 := by
      have : ρ (a * a⁻¹) = 1 := by rw [mul_inv_cancel, map_one]
      rwa [map_mul, ha, one_mul] at this
    refine ⟨h1, ?_⟩
    have h := hc.2 a a⁻¹
    rw [mul_inv_cancel, coc_one hc, ha', ha] at h
    simpa using h.symm

private theorem killSub_normal (ρ : Representation R Γ M) {c : Γ → M} (hc : c ∈ Z1 ρ) : (killSub ρ hc).Normal where
  conj_mem := by
    rintro g ⟨hg, hg'⟩ h
    refine ⟨by rw [map_mul, map_mul, hg, mul_one, ← map_mul, mul_inv_cancel, map_one], ?_⟩
    have e := hc.2 h h⁻¹
    rw [mul_inv_cancel, coc_one hc] at e
    rw [hc.2, hc.2, hg', map_zero, add_zero, map_mul, hg, mul_one]
    exact e.symm

private theorem killSub_closed (ρ : Representation R Γ M) (hρ : ContAction ρ) {c : Γ → M} (hc : c ∈ Z1 ρ) :
    IsClosed (killSub ρ hc : Set Γ) := by
  have e : (killSub ρ hc : Set Γ) = (⋂ m : M, {g | ρ g m = m}) ∩ {g | c g = 0} := by
    ext g
    simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_setOf_eq]
    exact and_congr_left' LinearMap.ext_iff
  rw [e]
  refine IsClosed.inter (isClosed_iInter fun m => isClosed_eq ?_ continuous_const) (isClosed_eq hc.1 continuous_const)
  exact Continuous.comp (g := fun p : Γ × M => ρ p.1 p.2) hρ (continuous_id.prodMk continuous_const)

private theorem module_finite_z1_padicInt [Finite M] (ρ : Representation R Γ M) [Finite (H1 ρ)] : Finite (Z1 ρ) := by
  haveI : Finite (B1 ρ) := (Set.finite_range (d0 ρ)).to_subtype
  haveI : Finite ((B1 ρ).comap (Z1 ρ).subtype) :=
    Finite.of_injective (fun x => (⟨x.1.1, x.2⟩ : B1 ρ)) fun x y h =>
      Subtype.ext (Subtype.ext (congrArg (fun z : B1 ρ => z.1) h))
  haveI : Finite ((B1 ρ).comap (Z1 ρ).subtype).toAddSubgroup := this
  haveI : Finite (Z1 ρ ⧸ ((B1 ρ).comap (Z1 ρ).subtype).toAddSubgroup) := ‹Finite (H1 ρ)›
  exact Finite.of_addSubgroup_quotient ((B1 ρ).comap (Z1 ρ).subtype).toAddSubgroup

end

theorem UpperTheory.V.Ws.Gys.zunrFin :
    GlobalFiniteness → ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (M : Type) [AddCommGroup M] [Module (ZMod (l ^ 1)) M] [Finite M] [TopologicalSpace M] [DiscreteTopology M] (ρ : Representation (ZMod (l ^ 1)) (G F Ω) M) (S : Finset (HeightOneSpectrum (𝓞 F))), ContainsAbove S l → ContAction ρ → UnrOut ρ S → (Zunr ρ S).Finite := by
  intro hGF F Ω _ _ _ _ _ l _ M _ _ _ _ _ ρ S hS hρ hU
  obtain ⟨ρS, hcomp, hρS⟩ := UpperTheory.V.Ws.Gys.descend F Ω _ M ρ S hρ hU
  obtain ⟨-, f1, -⟩ := hGF F Ω l 1 M S ρS one_pos hS hρS
  haveI := f1
  haveI := module_finite_z1_padicInt ρS
  refine (Set.finite_range fun c : Z1 ρS => c.1 ∘ toGS Ω (S : Set (HeightOneSpectrum (𝓞 F)))).subset ?_
  rintro c ⟨hc, hI⟩
  haveI := killSub_normal ρ hc
  have hle : NS Ω (S : Set (HeightOneSpectrum (𝓞 F))) ≤ killSub ρ hc := by
    refine Subgroup.topologicalClosure_minimal _ (Subgroup.normalClosure_le_normal fun g hg => ?_) (killSub_closed ρ hρ hc)
    simp only [Set.mem_iUnion] at hg
    obtain ⟨v, hv, A, hA, hg⟩ := hg
    exact ⟨hU v hv A hA g hg, hI v hv A hA g hg⟩
  let cS : GS Ω (S : Set (HeightOneSpectrum (𝓞 F))) → M := Quotient.lift c fun a b hab => by
    have h := (hle (QuotientGroup.leftRel_apply.1 hab)).2
    have e := hc.2 a (a⁻¹ * b)
    rw [mul_inv_cancel_left, h, map_zero, add_zero] at e
    exact e.symm
  refine ⟨⟨cS, hc.1.quotient_lift _, fun x y => ?_⟩, rfl⟩
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective y
  have e := hc.2 a b
  rw [← hcomp] at e
  exact e
end
