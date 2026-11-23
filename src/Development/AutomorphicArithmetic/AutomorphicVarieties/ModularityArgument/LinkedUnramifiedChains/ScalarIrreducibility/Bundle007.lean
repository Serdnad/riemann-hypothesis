module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.RedDefs
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MkMemAdmissibleAtIffCocycle
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.ScalarIrreducibility.Bundle006
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle268
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.ScalarIrreducibility.WtUnit
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LaArtin
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LaCyc
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle032
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.ScalarIrreducibility.DerExt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.ScalarIrreducibility.FreeEtaleSheafZmodExistsHomSendingGenerator
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.FieldTheory.Galois.Profinite
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

@[expose] public section

section

open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp IsLocalRing UpperTheory.V UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Af UpperTheory.V.Pr UpperTheory.V.Alg UpperTheory.V.J

private theorem add_vanish {l : ℕ} [Fact l.Prime] {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [CompactSpace H] (f : H → PadicAlgCl l) (hf : Continuous f) (hm : ∀ a b, f (a * b) = f a + f b)
    {ι : Type} (u : ι → H) (g : H)
    (hg : ∀ (A : Type) [CommGroup A] [Finite A], IsPGroup l A → ∀ χ : H →* A, IsOpen (χ.ker : Set H) →
      (∀ a, χ (u a) = 1) → χ g = 1) (hu : ∀ a, f (u a) = 0) : f g = 0 := by
  classical
  have f1 : f 1 = 0 := by
    have h11 := hm 1 1
    rw [mul_one] at h11
    have h12 : f 1 + f 1 = f 1 + 0 := by rw [add_zero, ← h11]
    exact add_left_cancel h12
  have fpow : ∀ (h : H) (m : ℕ), f (h ^ m) = (m : PadicAlgCl l) * f h := by
    intro h m
    induction m with
    | zero => simp [f1]
    | succ m ih =>
      rw [pow_succ, hm, ih]
      push_cast
      ring
  let fm : H →* Multiplicative (PadicAlgCl l) :=
    { toFun := fun h => Multiplicative.ofAdd (f h)
      map_one' := by
        show Multiplicative.ofAdd (f 1) = 1
        rw [f1]
        rfl
      map_mul' := fun a b => by
        show Multiplicative.ofAdd (f (a * b)) = Multiplicative.ofAdd (f a) * Multiplicative.ofAdd (f b)
        rw [hm]
        rfl }
  have hl : ‖((l : ℕ) : PadicAlgCl l)‖ = 1 / (l : ℝ) := by
    rw [← PadicAlgCl.valuation_coe, PadicAlgCl.valuation_p]
    simp
  have hl1 : 1 / (l : ℝ) < 1 := by
    have h2 : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
    exact (div_lt_one (by linarith)).mpr h2
  have key : ∀ ε : ℝ, 0 < ε → ‖f g‖ < ε := by
    intro ε hε
    let W : Subgroup (Multiplicative (PadicAlgCl l)) :=
      { carrier := {x | ‖Multiplicative.toAdd x‖ < ε}
        one_mem' := by
          show ‖(0 : PadicAlgCl l)‖ < ε
          rw [norm_zero]
          exact hε
        mul_mem' := fun {a b} ha hb => by
          show ‖Multiplicative.toAdd a + Multiplicative.toAdd b‖ < ε
          exact lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt ha hb)
        inv_mem' := fun {a} ha => by
          show ‖-Multiplicative.toAdd a‖ < ε
          rw [norm_neg]
          exact ha }
    let N : Subgroup fm.range := W.subgroupOf fm.range
    let χ : H →* fm.range ⧸ N := (QuotientGroup.mk' N).comp fm.rangeRestrict
    have hker : ∀ h, χ h = 1 ↔ ‖f h‖ < ε := by
      intro h
      simp only [χ, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
        Subgroup.mem_subgroupOf]
      rfl
    have hsurj : Function.Surjective χ :=
      (QuotientGroup.mk'_surjective N).comp fm.rangeRestrict_surjective
    have hopen : IsOpen (χ.ker : Set H) := by
      have hset : (χ.ker : Set H) = {h | ‖f h‖ < ε} := by
        ext h
        exact hker h
      rw [hset]
      exact isOpen_lt (continuous_norm.comp hf) continuous_const
    haveI : Finite (fm.range ⧸ N) := by
      haveI : Finite (H ⧸ χ.ker) := Subgroup.quotient_finite_of_isOpen _ hopen
      exact Finite.of_surjective (QuotientGroup.kerLift χ)
        (fun a => by
          obtain ⟨h, rfl⟩ := hsurj a
          exact ⟨h, rfl⟩)
    have hp : IsPGroup l (fm.range ⧸ N) := by
      intro a
      obtain ⟨h, rfl⟩ := hsurj a
      have hpos : (0 : ℝ) < ‖f h‖ + 1 := by positivity
      obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (div_pos hε hpos) hl1
      refine ⟨k, ?_⟩
      rw [← map_pow, hker, fpow, norm_mul, Nat.cast_pow, norm_pow, hl]
      calc (1 / (l : ℝ)) ^ k * ‖f h‖ ≤ (1 / (l : ℝ)) ^ k * (‖f h‖ + 1) := by
            gcongr
            linarith
        _ < ε / (‖f h‖ + 1) * (‖f h‖ + 1) := by gcongr
        _ = ε := by field_simp
    exact (hker g).mp (hg _ hp χ hopen (fun a => (hker _).mpr (by rw [hu a, norm_zero]; exact hε)))
  by_contra hne
  exact lt_irrefl _ (key _ (norm_pos_iff.mpr hne))

private theorem rank_le_card_add_rank_of_kernel {K M : Type} [Field K] [AddCommGroup M] [Module K M] {ι : Type} [Fintype ι]
    (P Q : Submodule K M) (e : ι → M →ₗ[K] K) (h : ∀ x ∈ P, (∀ i, e i x = 0) → x ∈ Q) :
    Module.rank K P ≤ (Fintype.card ι : ℕ) + Module.rank K Q := by
  classical
  let φ : P →ₗ[K] (ι → K) := LinearMap.pi (fun i => (e i).comp P.subtype)
  have h1 := LinearMap.rank_range_add_rank_ker φ
  have h2 : Module.rank K (LinearMap.range φ) ≤ (Fintype.card ι : ℕ) := by
    calc Module.rank K (LinearMap.range φ) ≤ Module.rank K (ι → K) := Submodule.rank_le _
      _ = _ := rank_fun'
  have h3 : Module.rank K (LinearMap.ker φ) ≤ Module.rank K Q := by
    rw [(Submodule.equivMapOfInjective P.subtype Subtype.val_injective (LinearMap.ker φ)).rank_eq]
    apply Submodule.rank_mono
    rintro _ ⟨x, hx, rfl⟩
    apply h _ x.2
    intro i
    have := congrFun (LinearMap.mem_ker.mp hx) i
    simpa [φ] using this
  rw [← h1]
  exact add_le_add h2 h3

set_option synthInstance.maxHeartbeats 200000 in
theorem UpperTheory.V.J.tanBound :
    ∀ (l : ℕ) [Fact l.Prime] (c : Coef l) [Fr.IsCoef l c.O] (F : Fr.Frame l (ResidueField c.O)) (C₀ n : ℕ), F.Ok C₀ → (n = 2 ∨ n = 3) →
        ∀ (S : Fr.Space c.O F n), ∀ ξ : S.A →ₐ[c.O] Qbar l, IntPt S ξ →
          Module.rank (Qbar l) (PtDer ξ (Qbar l)) ≤ (n * F.d : ℕ) + Module.rank (Qbar l) (FixTan S ξ) := by
  intro l _ c _ F C₀ n hF hn S ξ hξ
  choose u a₀ hu1 hu2 hgen using hF.gen
  let ev : S.A → ((S.A →ₗ[c.O] Qbar l) →ₗ[Qbar l] Qbar l) := fun x =>
    { toFun := fun D => D x, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  have key := rank_le_card_add_rank_of_kernel (PtDer ξ (Qbar l)) (FixTan S ξ)
    (fun j : (Σ v : F.V, Fin n × Fin (F.dv v)) => ev ↑(S.u.ψ j.1 j.2.1 (u j.1 j.2.2))) ?_
  · have hc : Fintype.card (Σ v : F.V, Fin n × Fin (F.dv v)) = n * F.d := by
      rw [Fintype.card_sigma, UpperTheory.V.Fr.Frame.d, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun v _ => ?_)
      rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
    rw [hc] at key
    exact key
  · intro D hD hz
    have hD' : ∀ x y, D (x * y) = ξ x • D y + ξ y • D x := hD
    refine Submodule.mem_inf.mpr ⟨hD, ?_⟩
    show ∀ (v : F.V) (i : Fin n), ∀ g ∈ F.Iv v, D ↑((S.u.ψ v i) g) = 0
    intro v i g hg
    obtain ⟨hx, hd⟩ := (derRep l c F C₀ n hF hn S ξ hξ D hD).2.2 v i
    have hne : ∀ h : F.Gv v, ξ ↑((S.u.ψ v i) h) ≠ 0 := by
      intro h hh
      have h1 := congrArg ξ (congrArg Units.val (mul_inv_cancel ((S.u.ψ v i) h)))
      rw [Units.val_mul, map_mul, hh, zero_mul, Units.val_one, map_one] at h1
      exact zero_ne_one h1
    let f : F.Gv v → PadicAlgCl l := fun h => D ↑((S.u.ψ v i) h) * (ξ ↑((S.u.ψ v i) h))⁻¹
    have hfc : Continuous f := hd.mul (hx.inv₀ hne)
    have hfm : ∀ a b, f (a * b) = f a + f b := by
      intro a b
      have ha := hne a
      have hb := hne b
      simp only [f, map_mul, Units.val_mul, hD', smul_eq_mul]
      field_simp
      ring
    have hzero : ∀ a, f (u v a) = 0 := by
      intro a
      have := hz ⟨v, (i, a)⟩
      simp only [f]
      rw [show D ↑((S.u.ψ v i) (u v a)) = 0 from this, zero_mul]
    have h0 := add_vanish f hfc hfm (u v) g
      (fun A _ _ hA χ ho h1 => hgen v A hA χ ho h1 g hg) hzero
    have hg0 := hne g
    simp only [f, mul_eq_zero, inv_eq_zero] at h0
    exact h0.resolve_right hg0
end

section

open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp IsLocalRing UpperTheory.V UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Af UpperTheory.V.Pr UpperTheory.V.Alg UpperTheory.V.J

section SlopeTestRemainingChoices

open IsDedekindDomain GlobalTheory.LocLanglands GlobalTheory.WeilDeligne UpperTheory.V.W

private theorem free_of {K : Type} [Field K] (α β : Fin 3 → Kˣ) (T : Kˣ) (hT : ∀ m : ℕ, 0 < m → T ^ m ≠ 1)
    (hβ : ∀ i, ∃ N : ℕ, 0 < N ∧ β i ^ N = 1) (heq : ∀ i : Fin 3, α i * β i = T ^ (-((i : ℕ) : ℤ))) :
    Pr.FreeRatios α := by
  intro i j hij m hm hαm
  obtain ⟨Ni, hNi, hbi⟩ := hβ i
  obtain ⟨Nj, hNj, hbj⟩ := hβ j
  have key : ∀ k : Fin 3, ∀ n : ℕ, β k ^ n = 1 → α k ^ n = T ^ (-((k : ℕ) : ℤ) * (n : ℤ)) := by
    intro k n hn
    have hk : α k = T ^ (-((k : ℕ) : ℤ)) * (β k)⁻¹ := eq_mul_inv_of_mul_eq (heq k)
    rw [hk, mul_pow, inv_pow, hn, inv_one, mul_one, ← zpow_natCast, ← zpow_mul]
  have hM : α i ^ (m * (Ni * Nj)) = α j ^ (m * (Ni * Nj)) := by
    rw [pow_mul (α i), pow_mul (α j), hαm]
  rw [key i _ (by rw [show m * (Ni * Nj) = Ni * (m * Nj) by ring, pow_mul, hbi, one_pow]),
    key j _ (by rw [show m * (Ni * Nj) = Nj * (m * Ni) by ring, pow_mul, hbj, one_pow])] at hM
  have hfin : IsOfFinOrder T := by
    rw [isOfFinOrder_iff_zpow_eq_one]
    refine ⟨-((i : ℕ) : ℤ) * ((m * (Ni * Nj) : ℕ) : ℤ) - -((j : ℕ) : ℤ) * ((m * (Ni * Nj) : ℕ) : ℤ), ?_, ?_⟩
    · intro h0
      apply hij
      have hMpos : (0 : ℤ) < ((m * (Ni * Nj) : ℕ) : ℤ) := by positivity
      have hz : (((j : ℕ) : ℤ) - ((i : ℕ) : ℤ)) * ((m * (Ni * Nj) : ℕ) : ℤ) = 0 := by linarith
      rcases mul_eq_zero.1 hz with h | h
      · exact Fin.ext (by omega)
      · omega
    · rw [zpow_sub, hM, mul_inv_cancel]
  obtain ⟨n, hn, hTn⟩ := isOfFinOrder_iff_pow_eq_one.1 hfin
  exact hT n hn hTn

private theorem prod_wt {l : ℕ} [Fact l.Prime] {F : Type} [Field F] [NumberField F] {w : Plc F} (τ₀ : Emb l w)
    (y : (w.adicCompletion F)ˣ) (hP : ∏ᶠ τ : Emb l w, τ.1 (y : w.adicCompletion F) = 1) (hh : Emb l w → ℤ) (j : ℤ)
    (h0 : hh τ₀ = 2 * j) (h1 : ∀ τ, τ ≠ τ₀ → hh τ = j) :
    ∏ᶠ τ : Emb l w, τ.1 (y : w.adicCompletion F) ^ (-hh τ) = τ₀.1 (y : w.adicCompletion F) ^ (-j) := by
  classical
  haveI := GlobalTheory.HeckeGal.finite_contEmb (l := l) w
  letI := Fintype.ofFinite (Emb l w)
  have hy : ∀ τ : Emb l w, τ.1 (y : w.adicCompletion F) ≠ 0 := fun τ =>
    (map_ne_zero τ.1).2 y.ne_zero
  have e : ∀ τ : Emb l w, τ.1 (y : w.adicCompletion F) ^ (-hh τ) = τ.1 (y : w.adicCompletion F) ^ (-j) *
      (if τ = τ₀ then τ₀.1 (y : w.adicCompletion F) ^ (-j) else 1) := fun τ => by
    by_cases hτ : τ = τ₀
    · subst hτ
      rw [if_pos rfl, h0, ← zpow_add₀ (hy τ)]
      congr 1
      ring
    · rw [if_neg hτ, h1 τ hτ, mul_one]
  rw [finprod_eq_prod_of_fintype] at hP ⊢
  simp only [e]
  rw [Finset.prod_mul_distrib, Finset.prod_zpow, hP, one_zpow, one_mul, Finset.prod_ite_eq', if_pos (Finset.mem_univ _)]

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField in
private theorem art_elt (hG : GlobalTheory.Published.GlobalArtinReciprocity) {L Ω : Type} [Field L] [NumberField L] [Field Ω]
    [Algebra L Ω] [IsAlgClosure L Ω] {l : ℕ} [Fact l.Prime] {A : ValuationSubring Ω} {w : Plc L}
    (h : IsPlaceOver A w) (hl : ((l : ℕ) : 𝓞 L) ∈ w.asIdeal) (y : (w.adicCompletion L)ˣ)
    (hv : Valued.v (y : w.adicCompletion L) = 1) (hP : ∏ᶠ τ : Emb l w, τ.1 (y : w.adicCompletion L) = 1) :
    ∃ (σ : Ine (F := L) A) (a : Weil h →* (w.adicCompletion L)ˣ), IsLocalArtin h a ∧ a (ineIncl h σ) = y ∧
      cycBar L Ω l (σ : G L Ω) = 1 := by
  obtain ⟨a, ha⟩ := UpperTheory.V.Loc.laArtin hG h
  have hv' : ValuativeRel.valuation (w.adicCompletion L) (y : w.adicCompletion L) = 1 := by
    haveI : (Valued.v : Valuation (w.adicCompletion L) _).Compatible := .ofValuation _
    exact (ValuativeRel.isEquiv (ValuativeRel.valuation (w.adicCompletion L)) Valued.v).eq_one_iff_eq_one.2 hv
  obtain ⟨σ, hσ⟩ := (GlobalTheory.PsType.ineIncl_onto_units L Ω A w h a ha).1 y hv'
  refine ⟨σ, a, ha, hσ, ?_⟩
  have hc := (UpperTheory.V.Loc.laCyc hG h hl).2 a ha σ
  simp only [hσ, neg_neg, zpow_one, hP, MonoidHom.one_apply, mul_one] at hc
  ext
  exact hc

private theorem place_free (hG : GlobalTheory.Published.GlobalArtinReciprocity) {L Ω : Type} [Field L] [NumberField L] [Field Ω]
    [CharZero Ω] [Algebra L Ω] [IsAlgClosure L Ω] {l : ℕ} [Fact l.Prime] {A : ValuationSubring Ω} {w : Plc L}
    (h : IsPlaceOver A w) (hl : ((l : ℕ) : 𝓞 L) ∈ w.asIdeal) (τ₀ : Emb l w) (b : 𝓞 L) (τ₁ τ₂ : Emb l w)
    (hne : τ₁.1 (algebraMap L (w.adicCompletion L) (b : L)) ≠ τ₂.1 (algebraMap L (w.adicCompletion L) (b : L)))
    (ψ : Fin 3 → Dec (F := L) A →* (Qbar l)ˣ) (ph : Fin 3 → Ine (F := L) A →* (Qbar l)ˣ) (hh : Fin 3 → Emb l w → ℤ)
    (h0 : ∀ j : Fin 3, hh j τ₀ = 2 * ((j : ℕ) : ℤ)) (h1 : ∀ (j : Fin 3) (τ : Emb l w), τ ≠ τ₀ → hh j τ = ((j : ℕ) : ℤ))
    (hp : ∀ j, IsWtPart h (ψ j) (hh j) (ph j)) :
    ∃ g : Dec (F := L) A, cycBar L Ω l (g : G L Ω) = 1 ∧ Pr.FreeRatios fun i => ψ i g := by
  obtain ⟨y, hyv, hyP, hyT⟩ := UpperTheory.V.J.Wu.exists_unit hl b τ₁ τ₂ hne
  obtain ⟨σ, a, ha, hσ, hcyc⟩ := art_elt hG h hl y hyv hyP
  refine ⟨Subgroup.inclusion (GlobalTheory.WeilDeligne.Weil_le_Dec h) (GlobalTheory.WeilDeligne.ineIncl h σ), hcyc, ?_⟩
  have hz : τ₀.1 (y : w.adicCompletion L) ≠ 0 := (map_ne_zero τ₀.1).2 y.ne_zero
  haveI : CompactSpace (Ine (F := L) A) :=
    isCompact_iff_compactSpace.1 (ReciprocityTheory.Gal.isClosed_Ine A).isCompact
  apply free_of (fun i => ψ i (Subgroup.inclusion (GlobalTheory.WeilDeligne.Weil_le_Dec h) (GlobalTheory.WeilDeligne.ineIncl h σ)))
    (fun i => ph i σ) (Units.mk0 _ hz)
  · intro m hm h1
    apply hyT τ₀ m hm
    have h2 := congrArg Units.val h1
    simpa using h2
  · intro i
    haveI := Subgroup.quotient_finite_of_isOpen _ (hp i).1
    refine ⟨(ph i).ker.index, Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite, ?_⟩
    rw [← map_pow]
    exact (ph i).mem_ker.1 (Subgroup.pow_index_mem _ σ)
  · intro i
    ext
    have hw := (hp i).2 a ha σ
    rw [hσ, prod_wt τ₀ y hyP (hh i) ((i : ℕ) : ℤ) (h0 i) (h1 i)] at hw
    simpa using hw

private theorem mem_G' {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω]
    [IsAlgClosure L Ω] {s : HidaSetting l L Ω} (V : s.Lev) (v : Vl l L) (g : Dec (F := L) (s.A v))
    (hc : cycBar L Ω l (g : G L Ω) = 1) : V.frame.φ v g ∈ V.frame.G' := by
  rw [UpperTheory.V.W.GFrame.G', MonoidHom.mem_ker]
  change V.ε ((toGS Ω V.S') (resP L Ω (g : G L Ω))) = 1
  have h1 : V.ε ((toGS Ω V.S') (resP L Ω (g : G L Ω))) = cycZ L Ω l (g : G L Ω) := by
    rw [← MonoidHom.comp_apply, V.hε]
    rfl
  rw [h1]
  have hv := congrArg Units.val hc
  simp only [GlobalTheory.GalOfCusp.cycBar, MonoidHom.comp_apply, Units.coe_map, Units.val_one] at hv
  have hinj : Function.Injective ((algebraMap ℚ_[l] (Qbar l)).comp PadicInt.Coe.ringHom) :=
    (algebraMap ℚ_[l] (Qbar l)).injective.comp Subtype.val_injective
  apply Units.ext
  apply hinj
  rw [Units.val_one, map_one]
  exact hv

end SlopeTestRemainingChoices

theorem UpperTheory.V.J.wtEx :
    GlobalTheory.Published.GlobalArtinReciprocity → WtEx := by
  intro hG Ω _ _ _ l _ ι c _ N _ e ψ η σ g₁ B M hlink L _ _ _ _ _ Φ k c₁ _ f ka R hlarge hka
  classical
  refine ⟨fun v j τ => if τ = Classical.choice ⟨τ⟩ then 2 * ((j : ℕ) : ℤ) else ((j : ℕ) : ℤ), ?_, ?_⟩
  · intro v τ a b hab
    have hab' : (a : ℕ) < b := hab
    dsimp only
    split_ifs <;> omega
  · intro x hx v
    change UpperTheory.V.W.Vl l L at v
    obtain ⟨ph, hp, -⟩ := hx.2 v
    haveI := k.ab
    have hlw : ((l : ℕ) : 𝓞 L) ∈ (R.s.w v.1).asIdeal := by
      apply (R.s.hw v.1 _).1
      have hA := (R.s.hA v.1 _).2 v.2
      simpa only [map_natCast] using hA
    have hbig : 5 < Φ.dv (R.K.e v) := R.big.2 (R.K.e v)
    rw [k.dv (R.K.e v)] at hbig
    obtain ⟨g, hgD, hgU⟩ : ∃ g ∈ Dec (F := ℚ) (k.pl (R.K.e v)), g ∉ upl Ω L := by
      by_contra hcon
      push_neg at hcon
      have h1 := Subgroup.relIndex_eq_one.2 hcon
      omega
    have hgD' : g ∈ Dec (F := ℚ) (R.s.A v.1) := by
      rw [R.A_pl v]
      exact hgD
    obtain ⟨y, -, hgy⟩ : ∃ y ∈ maximalRealSubfield L, g (algebraMap L Ω y) ≠ algebraMap L Ω y := by
      by_contra hcon
      push_neg at hcon
      exact hgU hcon
    obtain ⟨b, τ₁, τ₂, hne⟩ := UpperTheory.V.J.Wu.exists_sep (R.s.hw v.1) hlw g hgD' y hgy
    obtain ⟨g', hc, hfree⟩ := place_free hG (R.s.hw v.1) hlw (Classical.choice ⟨τ₁⟩) b τ₁ τ₂ hne (x.psi v) ph
      (fun j τ => if τ = Classical.choice ⟨τ⟩ then 2 * ((j : ℕ) : ℤ) else ((j : ℕ) : ℤ))
      (fun j => if_pos rfl) (fun j τ hτ => if_neg hτ) hp
    exact ⟨g', mem_G' R.V v g' hc, hfree⟩
end

section

open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp IsLocalRing UpperTheory.V UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Af UpperTheory.V.Pr UpperTheory.V.Alg UpperTheory.V.J

set_option synthInstance.maxHeartbeats 200000 in
theorem UpperTheory.V.J.fixLe :
    ∀ (l : ℕ) [Fact l.Prime] (c : Coef l) [Fr.IsCoef l c.O] (F : Fr.Frame l (ResidueField c.O)) (C₀ n : ℕ), F.Ok C₀ → (n = 2 ∨ n = 3) →
        ∀ (S : Fr.Space c.O F n), ∀ ξ : S.A →ₐ[c.O] Qbar l, IntPt S ξ → S.u.TI (RingHom.ker ξ) →
          (∀ D ∈ FixTan S ξ, ∃ X : Matrix (Fin n) (Fin n) (Qbar l), ∀ g, (S.u.r g).map D = X * (ptRep S ξ).r g - (ptRep S ξ).r g * X) →
          Module.rank (Qbar l) (FixTan S ξ) ≤ 1 := by
  intro l _ c _ F C₀ n hF hn S ξ hI hT hX
  have hirr : MatIrr ⊤ (ptRep S ξ).r :=
    (Fr.types hF hn S (Qbar l) (ξ : S.A →+* Qbar l)).1.2 hT
  have key : ∀ D ∈ FixTan S ξ, ∃ t : Qbar l,
      (∀ (g : F.G0) (i j : Fin n), D (S.u.r g i j) = t * ↑(Fr.w n i - Fr.w n j) * ξ (S.u.r g i j)) ∧
      ∀ (v : F.V) (i : Fin n) (g : F.Gv v), D ↑((S.u.ψ v i) g) = 0 := by
    intro D hD
    obtain ⟨X, hXD⟩ := hX D hD
    exact torus l c F C₀ n hF hn S ξ hI D hD.1 hirr X hXD
  by_cases h0 : ∀ D ∈ FixTan S ξ, D = 0
  · have hbot : FixTan S ξ = ⊥ := eq_bot_iff.2 fun D hD => (Submodule.mem_bot _).2 (h0 D hD)
    rw [hbot]
    simp
  push_neg at h0
  obtain ⟨D1, hD1, hne⟩ := h0
  obtain ⟨t1, h1r, h1ψ⟩ := key D1 hD1
  have ht1 : t1 ≠ 0 := by
    rintro rfl
    exact hne (derExt l c F C₀ n hF hn S ξ D1 hD1.1 (fun g i j => by simp [h1r]) h1ψ)
  haveI : Module.Free (Qbar l) (FixTan S ξ) := Module.Free.of_divisionRing _ _
  refine (rank_submodule_le_one_iff _).2 ⟨D1, hD1, fun D hD => ?_⟩
  obtain ⟨t, hr, hψ⟩ := key D hD
  have hE : t1 • D - t • D1 = 0 :=
    derExt l c F C₀ n hF hn S ξ _
      (Submodule.sub_mem _ (Submodule.smul_mem _ _ hD.1) (Submodule.smul_mem _ _ hD1.1))
      (fun g i j => by
        simp only [LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, hr, h1r]
        ring)
      (fun v i g => by simp [hψ, h1ψ])
  rw [Submodule.mem_span_singleton]
  refine ⟨t1⁻¹ * t, ?_⟩
  rw [mul_smul, ← sub_eq_zero.1 hE, smul_smul, inv_mul_cancel₀ ht1, one_smul]
end
