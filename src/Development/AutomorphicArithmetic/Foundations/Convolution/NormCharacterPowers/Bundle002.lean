module

public import Development.AutomorphicArithmetic.Foundations.Convolution.NormCharacterPowers.SumSatUnit
public import Development.AbelianVarietyTheory.BlockTheory.AdelicCMFields.UnitaryHeckeCharacterIdele
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle118
public import Development.WeilBound.RepresentationTheoryGL.JacquetShalikaBounds.AbsoluteRigidity.AbsoluteCharacterNorms.UnitExponentHolds
public import Development.WeilBound.RepresentationTheoryGL.JacquetShalikaBounds.AbsoluteRigidity.SatakeTwists.SatakeTwistHolds
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.Bundle001

@[expose] public section

section

open UpperTheory.ConvolutionTheory.R

theorem UpperTheory.ConvolutionTheory.R.twoParts :
    ClassChar → Count → NormCharPow → TwoParts := by
  classical
  intro hC hCount hN K M _ _ _ _ _ _ _ _ hp n π ι _ m P hn hm hι hW
  obtain ⟨η, hη⟩ := hC K M hp
  have h1 := hCount K M hp η hη n π π ι m P hn hm hW hW
  obtain ⟨a, b, hab⟩ := Fintype.exists_pair_of_one_lt_card (show 1 < Fintype.card ι from hι)
  have h2 : 1 < ((Finset.range (Module.finrank K M)).filter fun j => π = π.twist (η ^ j)).card := by
    rw [h1, Finset.one_lt_card]
    refine ⟨(a, a), by simp, (b, b), by simp, fun h => hab (congrArg Prod.fst h)⟩
  obtain ⟨j, hj, hj0⟩ := Finset.exists_mem_ne h2 0
  rw [Finset.mem_filter, Finset.mem_range] at hj
  exact ⟨η ^ j, (hN K M hp η hη).2 j (Nat.pos_of_ne_zero hj0) hj.1, hj.2.symm⟩
end

section

open UpperTheory.ConvolutionTheory.R

open GlobalTheory.CuspRep Formalism.L2.Host

theorem UpperTheory.ConvolutionTheory.R.fibreCG :
    ClassChar → Count → NormCharPow → FibreCG := by
  intro hC hN hP K M _ _ _ _ _ _ _ _ hl n π P hn hπ
  classical
  obtain ⟨η, hη⟩ := hC K M hl
  obtain ⟨hp1, hp2⟩ := hP K M hl η hη
  have key : ∀ π₁ : CG K n, UpperTheory.V.Published.WeakBC π₁.HasSat P.HasSat →
      ((Finset.range (Module.finrank K M)).filter fun j => π₁ = π.twist (η ^ j)).card = 1 := by
    intro π₁ h₁
    have := hN K M hl η hη n π π₁ Unit (fun _ => n) (fun _ => P) hn (fun _ => hn)
      (by rw [sumSat_unit]; exact hπ) (by rw [sumSat_unit]; exact h₁)
    convert this using 1
    simp
  refine ⟨fun χ hχ he => ?_, fun π₁ h₁ => ?_⟩
  · obtain ⟨j, hj0, hjl, rfl⟩ := hp1 χ hχ
    obtain ⟨a, ha⟩ := Finset.card_eq_one.1 (key π hπ)
    have h0 : 0 ∈ (Finset.range (Module.finrank K M)).filter fun j => π = π.twist (η ^ j) := by
      rw [Finset.mem_filter, Finset.mem_range, pow_zero, CG.twist_one]
      exact ⟨hl.pos, rfl⟩
    have h1 : j ∈ (Finset.range (Module.finrank K M)).filter fun j => π = π.twist (η ^ j) := by
      rw [Finset.mem_filter, Finset.mem_range]
      exact ⟨hjl, he.symm⟩
    rw [ha, Finset.mem_singleton] at h0 h1
    omega
  · obtain ⟨a, ha⟩ := Finset.card_eq_one.1 (key π₁ h₁)
    have h1 : a ∈ (Finset.range (Module.finrank K M)).filter fun j => π₁ = π.twist (η ^ j) := by
      rw [ha]; exact Finset.mem_singleton_self a
    rw [Finset.mem_filter, Finset.mem_range] at h1
    refine ⟨η ^ a, ?_, h1.2.symm⟩
    rcases Nat.eq_zero_or_pos a with rfl | h
    · exact Or.inl (pow_zero _)
    · exact Or.inr (hp2 a h h1.1)
end

section

open UpperTheory.ConvolutionTheory.R

open NumberField in
private theorem not_both (F : Type) [Field F] [NumberField F] (h : IsTotallyReal F) (h' : IsTotallyComplex F) : False := by
  obtain ⟨v⟩ : Nonempty (InfinitePlace F) := inferInstance
  exact (InfinitePlace.not_isReal_iff_isComplex.2 (h'.isComplex v)) (h.isReal v)

theorem UpperTheory.ConvolutionTheory.R.fibre :
    FibreCG → Fibre := by
  intro H K M _ _ _ _ _ _ hK hM hp n hn π P hbc
  rcases π with @⟨_, π⟩ | @⟨hR, π⟩
  swap
  · exact (not_both K hR hK).elim
  rcases P with @⟨_, P⟩ | @⟨hR, P⟩
  swap
  · exact (not_both M hR hM).elim
  obtain ⟨h1, h2⟩ := H K M hp n (GlobalTheory.CuspRep.CG.mk π) (GlobalTheory.CuspRep.CG.mk P) hn hbc
  refine ⟨fun η hη hi => h1 η hη (Quotient.sound hi), fun π₁ hbc₁ => ?_⟩
  rcases π₁ with @⟨_, π₁⟩ | @⟨hR, π₁⟩
  swap
  · exact (not_both K hR hK).elim
  obtain ⟨η, hη, e⟩ := h2 (GlobalTheory.CuspRep.CG.mk π₁) hbc₁
  exact ⟨η, hη, Quotient.exact e⟩
end

section

open UpperTheory.ConvolutionTheory.R

open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.L2.Host UpperTheory.V.Published

theorem UpperTheory.ConvolutionTheory.R.normCharPow :
    Count → NormCharPow := by
  classical
  intro hN K M _ _ _ _ _ _ _ _ hl η hη
  have hp : ∀ (n : ℕ) (v : HeightOneSpectrum (𝓞 K)), (η ^ n).val v = η.val v ^ n :=
    fun n v => MonoidHom.pow_apply η.1 n _
  refine ⟨fun χ hχ => ?_, fun j hj0 hjl => ⟨fun h => ?_, ?_, ?_⟩⟩
  · have hW : ∀ ψ : HChar K, (∀ᶠ w : HeightOneSpectrum (𝓞 M) in Filter.cofinite, ∀ f : ℕ,
        Formalism.ConjugateSelfDual.normV w = Formalism.ConjugateSelfDual.normV (w.under (𝓞 K)) ^ f → ψ.val (w.under (𝓞 K)) ^ f = 1) →
        WeakBC (CG.ofChar ψ).HasSat (sumSat (m := fun _ : Unit => 1) fun _ => CG.ofChar (1 : HChar M)) := by
      intro ψ h
      rw [sumSat_unit]
      filter_upwards [h, (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.tendsto_under K M).eventually
        (Filter.eventually_cofinite.2 (GlobalTheory.Mem.UnrAe.finite_ramified ψ))] with w h1 h2 f hf
      refine ⟨_, CG.hasSat_ofChar h2, ?_⟩
      rw [Multiset.map_singleton, h1 f hf]
      exact CG.hasSat_ofChar (χ := 1) (w := w) fun _ _ => rfl
    have h1 := hN K M hl η hη 1 (CG.ofChar 1) (CG.ofChar χ) Unit (fun _ => 1) (fun _ => CG.ofChar 1) le_rfl
      (fun _ => le_rfl) (hW 1 (Filter.Eventually.of_forall fun w f _ => one_pow f)) (hW χ hχ.2.2)
    have h2 : 0 < ((Finset.range (Module.finrank K M)).filter
        fun j => CG.ofChar χ = (CG.ofChar 1).twist (η ^ j)).card := by
      rw [h1]
      exact Finset.card_pos.2 ⟨((), ()), by simp⟩
    obtain ⟨j, hj⟩ := Finset.card_pos.1 h2
    rw [Finset.mem_filter, Finset.mem_range, CG.twist_ofChar, one_mul] at hj
    have e := CG.ofChar_injective hj.2
    refine ⟨j, Nat.pos_of_ne_zero ?_, hj.1, e⟩
    rintro rfl
    exact hχ.1 (e.trans (pow_zero _))
  · haveI := Fact.mk hl
    have ho := orderOf_eq_prime hη.1.2.1 hη.1.1
    have := Nat.le_of_dvd hj0 (orderOf_dvd_of_pow_eq_one h)
    omega
  · rw [← pow_mul, mul_comm, pow_mul, hη.1.2.1, one_pow]
  · refine hη.1.2.2.mono fun w hw f hf => ?_
    rw [hp, ← pow_mul, mul_comm, pow_mul, hw f hf, one_pow]
end

section

open UpperTheory.ConvolutionTheory.R
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V.Published PositivityTheory.RgJS

private theorem normV_eq {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    normV v = Ideal.absNorm v.asIdeal := by
  rw [normV, Ideal.absNorm_apply, Submodule.cardQuot_apply]

private theorem one_lt_normV {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) : 1 < normV v := by
  rw [normV_eq]
  exact NumberField.HeightOneSpectrum.one_lt_absNorm v

theorem UpperTheory.ConvolutionTheory.R.coverEx :
    Decomp → CoverEx := by
  classical
  intro hD K M _ _ _ _ _ _ _ _ hl η hη S₀ T₀
  have hD' := hD K M hl
  obtain ⟨⟨-, -, hN⟩, hG⟩ := hη
  have hNG := hN.and hG
  beta_reduce at hD'
  rw [Filter.eventually_cofinite] at hD' hNG
  have hten : Filter.Tendsto (fun w : HeightOneSpectrum (𝓞 M) => w.under (𝓞 K)) Filter.cofinite Filter.cofinite :=
    GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.tendsto_under K M
  set S : Finset (HeightOneSpectrum (𝓞 K)) :=
    S₀ ∪ hD'.toFinset ∪ (T₀ ∪ hNG.toFinset).image (fun w => w.under (𝓞 K)) with hS
  have hTfin : {w : HeightOneSpectrum (𝓞 M) | w.under (𝓞 K) ∈ S}.Finite := by
    have := hten.eventually S.eventually_cofinite_notMem
    rw [Filter.eventually_cofinite] at this
    simpa using this
  set T := hTfin.toFinset with hT
  have hmemT : ∀ w, w ∈ T ↔ w.under (𝓞 K) ∈ S := fun w => by simp [hT]
  have hgood : ∀ w : HeightOneSpectrum (𝓞 M), w.under (𝓞 K) ∉ S →
      (∀ f : ℕ, normV w = normV (w.under (𝓞 K)) ^ f → η.val (w.under (𝓞 K)) ^ f = 1) ∧ η.UnrAt (w.under (𝓞 K)) ∧
      (normV w = normV (w.under (𝓞 K)) ∨ IsPrimitiveRoot (η.val (w.under (𝓞 K))) (Module.finrank K M)) := by
    intro w hw
    by_contra h
    exact hw (Finset.mem_union_right _ (Finset.mem_image_of_mem _
      (Finset.mem_union_right _ (hNG.mem_toFinset.2 h))))
  have hdec : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S →
      (Nat.card {w : HeightOneSpectrum (𝓞 M) // w.under (𝓞 K) = v} = Module.finrank K M ∧
        ∀ w : HeightOneSpectrum (𝓞 M), w.under (𝓞 K) = v → normV w = normV v) ∨
      (Nat.card {w : HeightOneSpectrum (𝓞 M) // w.under (𝓞 K) = v} = 1 ∧
        ∀ w : HeightOneSpectrum (𝓞 M), w.under (𝓞 K) = v → normV w = normV v ^ Module.finrank K M) := by
    intro v hv
    by_contra h
    exact hv (Finset.mem_union_left _ (Finset.mem_union_right _ (hD'.mem_toFinset.2 h)))
  have hex : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → ∃ w : HeightOneSpectrum (𝓞 M), w.under (𝓞 K) = v := by
    intro v hv
    have : Nat.card {w : HeightOneSpectrum (𝓞 M) // w.under (𝓞 K) = v} ≠ 0 := by
      rcases hdec v hv with h | h
      · rw [h.1]; exact hl.ne_zero
      · rw [h.1]; exact one_ne_zero
    obtain ⟨⟨w, hw⟩⟩ := (Nat.card_ne_zero.1 this).1
    exact ⟨w, hw⟩
  have hne : ∀ v : HeightOneSpectrum (𝓞 K), normV v ^ Module.finrank K M ≠ normV v := by
    intro v
    have := Nat.pow_lt_pow_right (one_lt_normV v) hl.one_lt
    rw [pow_one] at this
    exact this.ne'
  let u : Off M T → Off K S := fun w => ⟨w.1.under (𝓞 K), fun h => w.2 ((hmemT _).2 h)⟩
  let f : Off M T → ℕ := fun w => if normV w.1 = normV (w.1.under (𝓞 K)) then 1 else Module.finrank K M
  have hnorm : ∀ w, normV w.1 = normV (u w).1 ^ f w := by
    intro w
    by_cases h : normV w.1 = normV (w.1.under (𝓞 K))
    · simp only [f, if_pos h, pow_one]; exact h
    · simp only [f, if_neg h]
      rcases hdec _ (u w).2 with h' | h'
      · exact absurd (h'.2 _ rfl) h
      · exact h'.2 _ rfl
  have hcard : ∀ v : Off K S, Nat.card {w // u w = v} =
      Nat.card {w : HeightOneSpectrum (𝓞 M) // w.under (𝓞 K) = v.1} := by
    intro v
    exact Nat.card_congr
      { toFun := fun w => ⟨w.1.1, congrArg Subtype.val w.2⟩
        invFun := fun w => ⟨⟨w.1, fun h => v.2 (w.2 ▸ (hmemT _).1 h)⟩, Subtype.ext w.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  refine ⟨S, T, u, f, fun v hv => Finset.mem_union_left _ (Finset.mem_union_left _ hv), fun w hw => (hmemT w).2
    (Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_union_left _ hw))), fun _ => rfl, ?_, hnorm, ?_, ?_⟩
  · intro v
    obtain ⟨w, hw⟩ := hex v.1 v.2
    exact hw ▸ (hgood w (hw ▸ v.2)).2.1
  · intro w
    simpa only [nq, normV_eq] using hnorm w
  · intro v
    obtain ⟨w₀, hw₀⟩ := hex v.1 v.2
    have hg := hgood w₀ (hw₀ ▸ v.2)
    rw [hw₀] at hg
    rcases hdec v.1 v.2 with h | h
    · refine Or.inl ⟨(hcard v).trans h.1, fun w hw => ?_, ?_⟩
      · have hw' : w.1.under (𝓞 K) = v.1 := congrArg Subtype.val hw
        exact if_pos (hw' ▸ h.2 _ hw')
      · have := hg.1 1 (by rw [pow_one]; exact h.2 _ hw₀)
        rw [pow_one] at this
        simp [this]
    · refine Or.inr ⟨(hcard v).trans h.1, fun w hw => ?_, ?_⟩
      · have hw' : w.1.under (𝓞 K) = v.1 := congrArg Subtype.val hw
        refine if_neg ?_
        rw [h.2 _ hw', hw']
        exact hne _
      · rcases hg.2.2 with h' | h'
        · exact absurd ((h.2 _ hw₀).symm.trans h') (hne _)
        · exact IsPrimitiveRoot.coe_units_iff.2 h'
end

section

open UpperTheory.ConvolutionTheory.R
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V.Published PositivityTheory.RgJS

section

variable {E : Type} [Field E] [NumberField E]

private theorem val_pow' (χ : HChar E) (j : ℕ) (w : HeightOneSpectrum (𝓞 E)) : (χ ^ j).val w = χ.val w ^ j :=
  MonoidHom.pow_apply χ.1 j _

private theorem unr_pow {χ : HChar E} {w : HeightOneSpectrum (𝓞 E)} (h : χ.UnrAt w) (j : ℕ) : (χ ^ j).UnrAt w := by
  intro x hx
  have e : (χ ^ j).loc w x = χ.loc w x ^ j := MonoidHom.pow_apply χ.1 j _
  rw [e, h x hx, one_pow]

private theorem unr_inv {χ : HChar E} {w : HeightOneSpectrum (𝓞 E)} (h : χ.UnrAt w) : (χ⁻¹).UnrAt w := by
  intro x hx
  have e : (χ⁻¹).loc w x = (χ.loc w x)⁻¹ := rfl
  rw [e, h x hx, inv_one]

private theorem unit_of_pow {χ : HChar E} {l : ℕ} (hl : l ≠ 0) (h : χ ^ l = 1) : χ.IsUnitary := by
  intro x
  have e : χ.1 x ^ l = 1 := by
    have e1 : (χ ^ l).1 x = χ.1 x ^ l := MonoidHom.pow_apply χ.1 l _
    rw [← e1, h]; rfl
  have e2 : ((χ.1 x : ℂˣ) : ℂ) ^ l = 1 := by rw [← Units.val_pow_eq_pow_val, e, Units.val_one]
  exact Complex.norm_eq_one_of_pow_eq_one e2 hl

variable [_root_.NumberField.IsTotallyComplex E]

private theorem unit_twist {n : ℕ} {π : CG E n} (h : π.IsUnitary) {χ : HChar E} (hχ : χ.IsUnitary) :
    (π.twist χ).IsUnitary := by
  obtain ⟨ω, hω, hc⟩ := h
  refine ⟨_, fun x => ?_, hc.twist χ⟩
  have e : (ω * χ ^ n).1 x = ω.1 x * χ.1 x ^ n := congrArg (ω.1 x * ·) (MonoidHom.pow_apply χ.1 n _)
  rw [e, Units.val_mul, Units.val_pow_eq_pow_val, norm_mul, norm_pow, hω x, hχ x, one_pow, one_mul]

private theorem sat_untw {n : ℕ} {π : CG E n} {χ : HChar E} {w : HeightOneSpectrum (𝓞 E)} (hχ : χ.UnrAt w)
    (h : ∃ B, (π.twist χ).HasSat w B) : ∃ B, π.HasSat w B := by
  obtain ⟨B, hB⟩ := h
  have := satake_twist_holds E n _ χ⁻¹ w B (unr_inv hχ) hB
  rw [← CG.twist_mul, mul_inv_cancel, CG.twist_one] at this
  exact ⟨_, this⟩

private theorem sat_key {n : ℕ} {π : CG E n} {χ : HChar E} {w : HeightOneSpectrum (𝓞 E)} (hχ : χ.UnrAt w)
    {α : Fin n → ℂˣ} (hα : π.HasSat w (Finset.univ.val.map α)) {B : Multiset ℂˣ} (hB : (π.twist χ).HasSat w B) :
    B.map (fun u : ℂˣ => (u : ℂ)) = Finset.univ.val.map fun a => (α a : ℂ) * (χ.val w : ℂ) := by
  rw [hB.unique (satake_twist_holds E n π χ w _ hχ hα), Multiset.map_map, Multiset.map_map]
  exact Multiset.map_congr rfl fun a _ => by simp

end

private theorem ev_sat {K M : Type} [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M]
    {S : Finset (HeightOneSpectrum (𝓞 K))} {T : Finset (HeightOneSpectrum (𝓞 M))} {u : Off M T → Off K S}
    {f : Off M T → ℕ} (hu : ∀ w, (u w).1 = w.1.under (𝓞 K)) (hf : ∀ w, normV w.1 = normV (u w).1 ^ f w)
    (hs : Function.Surjective u) {sat : HeightOneSpectrum (𝓞 K) → Multiset ℂˣ → Prop}
    {satE : HeightOneSpectrum (𝓞 M) → Multiset ℂˣ → Prop} (h : WeakBC sat satE) :
    (∀ᶠ v in Filter.cofinite, ∃ B, sat v B) ∧ ∀ᶠ w in Filter.cofinite, ∃ B, satE w B := by
  constructor
  · have h' := Filter.eventually_cofinite.1 h
    have h2 := (h'.image fun w : HeightOneSpectrum (𝓞 M) => w.under (𝓞 K)).eventually_cofinite_notMem
    filter_upwards [h2, S.eventually_cofinite_notMem] with v hv hvS
    obtain ⟨w, hw⟩ := hs ⟨v, hvS⟩
    have e : w.1.under (𝓞 K) = v := (hu w).symm.trans (congrArg Subtype.val hw)
    by_contra hc
    refine hv ⟨w.1, fun hg => hc ?_, e⟩
    obtain ⟨B, hB, -⟩ := hg (f w) (by rw [← hu w]; exact hf w)
    exact ⟨B, e ▸ hB⟩
  · filter_upwards [h, T.eventually_cofinite_notMem] with w hw hwT
    obtain ⟨B, -, hB⟩ := hw (f ⟨w, hwT⟩) (by have := hf ⟨w, hwT⟩; rwa [hu] at this)
    exact ⟨_, hB⟩

private theorem lift_eq {K M : Type} [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M]
    [_root_.NumberField.IsTotallyComplex K] [_root_.NumberField.IsTotallyComplex M] {n : ℕ} {π : CG K n} {ν : HChar K} {t : ℝ} (hν : ν.IsAbsPow t)
    {ι : Type} [Fintype ι] {m : ι → ℕ} {P : ∀ i, CG M (m i)} {ν' : ι → HChar M} {s : ι → ℝ}
    (hν' : ∀ i, (ν' i).IsAbsPow (s i)) {v : HeightOneSpectrum (𝓞 K)} {w : HeightOneSpectrum (𝓞 M)} {f : ℕ}
    {α : Fin n → ℂˣ} (hα : π.HasSat v (Finset.univ.val.map α)) {β : ∀ i, Fin (m i) → ℂˣ}
    (hβ : ∀ i, (P i).HasSat w (Finset.univ.val.map (β i)))
    (h : ∃ B, (π.twist ν).HasSat v B ∧ sumSat (fun i => (P i).twist (ν' i)) w (B.map (· ^ f))) :
    ∑ i, Finset.univ.val.map (fun a => (β i a : ℂ) * ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ (-(s i : ℂ))) =
      Finset.univ.val.map fun a => ((α a : ℂ) * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(t : ℂ))) ^ f := by
  obtain ⟨B, hB, B', hB', e⟩ := h
  have e1 := sat_key (hν.1 v) hα hB
  have e2 := fun i => sat_key ((hν' i).1 w) (hβ i) (hB' i)
  simp only [(hν' _).2.1 w] at e2
  rw [hν.2.1 v] at e1
  have e3 := congrArg (Multiset.map fun u : ℂˣ => (u : ℂ)) e
  have e4 : Multiset.map (fun u : ℂˣ => (u : ℂ)) (∑ i, B' i) = ∑ i, Multiset.map (fun u : ℂˣ => (u : ℂ)) (B' i) :=
    map_sum (Multiset.mapAddMonoidHom fun u : ℂˣ => (u : ℂ)) B' Finset.univ
  have e5 := congrArg (Multiset.map fun c : ℂ => c ^ f) e1
  rw [Multiset.map_map, Multiset.map_map] at e5
  rw [e4, Multiset.map_map] at e3
  simp only [e2] at e3
  rw [← e3]
  exact Eq.trans (Multiset.map_congr rfl fun a _ => by simp) e5

theorem UpperTheory.ConvolutionTheory.R.count :
    AbsCount → SysEx → CoverEx → Count := by
  intro hA hS hC K M _ _ _ _ _ _ _ _ hl η hη n π π₁ ι _ m P hn hm hπ hπ₁
  classical
  obtain ⟨ν, hν, hU⟩ := unit_exponent_holds K
  obtain ⟨ν', hν', hU'⟩ := unit_exponent_holds M
  obtain ⟨π0, t, hu0, rfl⟩ := hU n π hn
  obtain ⟨π1, t1, hu1, rfl⟩ := hU n π₁ hn
  choose P0 s huP hP using fun i => hU' (m i) (P i) (hm i)
  obtain rfl : P = fun i => (P0 i).twist (ν' (s i)) := funext hP
  have hηl : η ^ Module.finrank K M = 1 := hη.1.2.1
  have hηu : ∀ j : ℕ, (η ^ j).IsUnitary := fun j =>
    unit_of_pow hl.ne_zero (by rw [← pow_mul, mul_comm, pow_mul, hηl, one_pow])
  obtain ⟨S1, T1, u1, f1, -, -, hu1', hunr1, hf1, hc1⟩ := hC K M hl η hη ∅ ∅
  have hs1 : Function.Surjective u1 := fun v => by
    have : Nat.card {w // u1 w = v} ≠ 0 := by
      rcases hc1.fib v with h | h
      · rw [h.1]; exact hl.ne_zero
      · rw [h.1]; exact one_ne_zero
    obtain ⟨⟨w, hw⟩⟩ := (Nat.card_ne_zero.1 this).1
    exact ⟨w, hw⟩
  obtain ⟨e0, eP⟩ := ev_sat hu1' hf1 hs1 hπ
  obtain ⟨e1, -⟩ := ev_sat hu1' hf1 hs1 hπ₁
  let X : Set (Σ a, CG K a) := insert ⟨n, π1⟩ (Set.range fun j : ℕ => ⟨n, π0.twist (η ^ j)⟩)
  let X' : Set (Σ a, CG M a) := Set.range fun i => ⟨m i, P0 i⟩
  have hXf : X.Finite := by
    refine Set.Finite.insert _ (((Set.finite_lt_nat (Module.finrank K M)).image
      fun j : ℕ => (⟨n, π0.twist (η ^ j)⟩ : Σ a, CG K a)).subset ?_)
    rintro _ ⟨j, rfl⟩
    exact ⟨j % Module.finrank K M, Nat.mod_lt _ hl.pos, by
      beta_reduce; rw [← pow_eq_pow_mod j hηl]⟩
  obtain ⟨S0, hS0⟩ := hS K X hXf (by
    rintro _ (rfl | ⟨j, rfl⟩)
    · exact ⟨hn, hu1, e1.mono fun v hv => sat_untw ((hν _).1 v) hv⟩
    · refine ⟨hn, unit_twist hu0 (hηu j), ?_⟩
      filter_upwards [e0, S1.eventually_cofinite_notMem] with v hv hvS
      obtain ⟨B, hB⟩ := sat_untw ((hν _).1 v) hv
      exact ⟨_, satake_twist_holds K n π0 _ v B (unr_pow (hunr1 ⟨v, hvS⟩) j) hB⟩)
  obtain ⟨T0, hT0⟩ := hS M X' (Set.finite_range _) (by
    rintro _ ⟨i, rfl⟩
    exact ⟨hm i, huP i, eP.mono fun w ⟨B, B', hB', _⟩ => sat_untw ((hν' _).1 w) ⟨_, hB' i⟩⟩)
  have hbad := Filter.eventually_cofinite.1 (hπ.and hπ₁)
  obtain ⟨S, T, u, f, hS0S, hT0T, hu, hunr, hf, hc⟩ := hC K M hl η hη S0 (T0 ∪ hbad.toFinset)
  obtain ⟨α, hα, hsys⟩ := hS0 S hS0S
  obtain ⟨β, hβ, hsys'⟩ := hT0 T (Finset.subset_union_left.trans hT0T)
  have hgood : ∀ w : Off M T, (∃ B, (π0.twist (ν t)).HasSat (u w).1 B ∧
      sumSat (fun i => (P0 i).twist (ν' (s i))) w.1 (B.map (· ^ f w))) ∧ ∃ B, (π1.twist (ν t1)).HasSat (u w).1 B ∧
      sumSat (fun i => (P0 i).twist (ν' (s i))) w.1 (B.map (· ^ f w)) := fun w => by
    have h1 := hf w
    rw [hu] at h1 ⊢
    have h2 : w.1 ∉ hbad.toFinset := fun h => w.2 (hT0T (Finset.mem_union_right _ h))
    rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_not] at h2
    exact ⟨h2.1 _ h1, h2.2 _ h1⟩
  let x : X := ⟨⟨n, π1⟩, Or.inl rfl⟩
  let y : ℕ → X := fun j => ⟨⟨n, π0.twist (η ^ j)⟩, Or.inr ⟨j, rfl⟩⟩
  let z : ι → X' × ℝ := fun i => (⟨⟨m i, P0 i⟩, i, rfl⟩, s i)
  have hy0 : ∀ v : Off K S, π0.HasSat v.1 (Finset.univ.val.map (α (y 0) v)) := fun v => by
    have : (π0.twist (η ^ 0)).HasSat v.1 (Finset.univ.val.map (α (y 0) v)) := hα (y 0) v
    rwa [pow_zero, CG.twist_one] at this
  obtain ⟨ht, hs, hcount⟩ := hA _ _ _ nq nq u f _ hl.pos hc X X' _ _ _ _ hsys hsys' ι x y z t1 t
    (fun j v => by
      have := sat_key (unr_pow (hunr v) j) (hy0 v) (hα (y j) v)
      rw [Multiset.map_map, val_pow', Units.val_pow_eq_pow_val] at this
      rw [Multiset.map_map]
      exact this)
    (fun w => lift_eq (hν t1) (fun i => hν' (s i)) (hα x (u w)) (fun i => hβ (z i).1 w) (hgood w).2)
    (fun w => lift_eq (hν t) (fun i => hν' (s i)) (hy0 (u w)) (fun i => hβ (z i).1 w) (hgood w).1)
  subst ht
  have hs' : ∀ i, s i = t1 := hs
  have key : ∀ {a b : ℕ} (σ : CG M a) (σ' : CG M b) (χ : HChar M),
      (⟨a, σ.twist χ⟩ : Σ a, CG M a) = ⟨b, σ'.twist χ⟩ ↔ (⟨a, σ⟩ : Σ a, CG M a) = ⟨b, σ'⟩ := by
    intro a b σ σ' χ
    constructor
    · intro e
      obtain rfl : a = b := (Sigma.mk.inj e).1
      exact congrArg _ (CG.twist_injective χ (eq_of_heq (Sigma.mk.inj e).2))
    · intro e
      obtain rfl : a = b := (Sigma.mk.inj e).1
      rw [eq_of_heq (Sigma.mk.inj e).2]
  refine Eq.trans (congrArg Finset.card (Finset.ext fun j => ?_))
    (hcount.trans (congrArg Finset.card (Finset.ext fun p => ?_)))
  · simp only [Finset.mem_filter]
    refine and_congr_right fun _ => ?_
    rw [← CG.twist_mul, mul_comm, CG.twist_mul, Subtype.ext_iff]
    constructor
    · intro e
      exact congrArg (Sigma.mk n) (CG.twist_injective _ e)
    · intro e
      rw [eq_of_heq (Sigma.mk.inj e).2]
  · simp only [Finset.mem_filter]
    refine and_congr_right fun _ => ?_
    rw [Subtype.ext_iff, hs' p.1, hs' p.2, key]
end
