module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GlESymmApply
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle196
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle191
public import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Formalism.LocalToGlobal.GlobalTheory.GL6.Statement
import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.HCFFromRecipA

@[expose] public section

section

open Formalism.BasicNotions Formalism.L2.Forms Formalism.UG Formalism.L2.GlobalTheoryTheory.LocalLatticeBases NumberField IsDedekindDomain Matrix GlobalTheory.LevelHecke
open scoped TensorProduct

namespace GlobalTheory.LevelHecke.UpInj

variable {R V k W : Type} [CommRing R] [AddCommGroup V] [Module R V] [Field k] [AddCommGroup W] [Module k W]
  {res : R →+* k} {t : R} {Λ : Submodule R V} {π : V → W}

def Rel (res : R →+* k) (t : R) (Λ : Submodule R V) (π : V → W) (q : Pr R V k) (w : W) : Prop :=
  q.Ok res ∧ q.IsKer Λ ∧ ∃ e, q.f e = 1 ∧ π (t • e) = w

theorem mem_of_one {q : Pr R V k} (h : q.Ok res) {e : V} (he : q.f e = 1) : e ∈ q.L := by
  by_contra hn
  rw [h.off e hn] at he
  exact zero_ne_one he

theorem f_sub {q : Pr R V k} (h : q.Ok res) {x y : V} (hx : x ∈ q.L) (hy : y ∈ q.L) :
    q.f (x - y) = q.f x - q.f y := by
  have := h.add (x - y) (sub_mem hx hy) y hy
  rw [sub_add_cancel] at this
  rw [this]; ring

theorem pi_sub (h : Red res t Λ π) {x y : V} (hx : x ∈ Λ) (hy : y ∈ Λ) : π (x - y) = π x - π y := by
  have := h.add (x - y) (sub_mem hx hy) y hy
  rw [sub_add_cancel] at this
  rw [this]; abel

theorem te_mem (ht : res t = 0) {q : Pr R V k} (h : q.Ok res) (hk : q.IsKer Λ) {e : V} (he : e ∈ q.L) :
    t • e ∈ Λ :=
  (hk _).2 ⟨q.L.smul_mem _ he, by rw [h.smul _ _ he, ht, zero_mul]⟩

theorem mem_of_pi (htf : ∀ x : V, t • x = 0 → x = 0) (hsat : ∀ s x, res s ≠ 0 → s • x ∈ Λ → x ∈ Λ)
    (hr : Red res t Λ π) {x : V} (hx : t • x ∈ Λ) (h0 : π (t • x) = 0) : x ∈ Λ := by
  obtain ⟨y, hy, s, hs, h⟩ := (hr.ker _ hx).1 h0
  have : s • x - y = 0 := htf _ (by rw [smul_sub, smul_comm, h, sub_self])
  exact hsat s x hs (by rw [sub_eq_zero.1 this]; exact hy)

theorem rel_fun (ht : res t = 0) (hr : Red res t Λ π) {q : Pr R V k} {w w' : W}
    (h : Rel res t Λ π q w) (h' : Rel res t Λ π q w') : w = w' := by
  obtain ⟨ho, hk, e, he, rfl⟩ := h
  obtain ⟨-, -, e', he', rfl⟩ := h'
  have m := mem_of_one ho he
  have m' := mem_of_one ho he'
  have h1 : e - e' ∈ Λ := (hk _).2 ⟨sub_mem m m', by rw [f_sub ho m m', he, he', sub_self]⟩
  have h2 := hr.smul t _ h1
  rw [ht, zero_smul, smul_sub, pi_sub hr (te_mem ht ho hk m) (te_mem ht ho hk m')] at h2
  exact sub_eq_zero.1 h2

theorem le_of_sub (hs : Function.Surjective res) {q q' : Pr R V k} (ho : q.Ok res) (hk : q.IsKer Λ)
    (ho' : q'.Ok res) (hk' : q'.IsKer Λ) {e e' : V} (he : q.f e = 1) (he' : q'.f e' = 1) (h : e - e' ∈ Λ)
    (y : V) (hy : y ∈ q.L) : y ∈ q'.L ∧ q'.f y = q.f y := by
  have m := mem_of_one ho he
  have m' := mem_of_one ho' he'
  obtain ⟨a, ha⟩ := hs (q.f y)
  have h1 : y - a • e ∈ Λ := (hk _).2 ⟨sub_mem hy (q.L.smul_mem _ m), by
    rw [f_sub ho hy (q.L.smul_mem _ m), ho.smul _ _ m, he, ha, mul_one, sub_self]⟩
  have h2 : y - a • e' ∈ Λ := by
    have := add_mem h1 (Λ.smul_mem a h)
    rwa [smul_sub, sub_add_sub_cancel] at this
  obtain ⟨h3, h4⟩ := (hk' _).1 h2
  have h5 : y ∈ q'.L := by
    have := add_mem h3 (q'.L.smul_mem a m')
    rwa [sub_add_cancel] at this
  refine ⟨h5, ?_⟩
  rw [f_sub ho' h5 (q'.L.smul_mem _ m'), ho'.smul _ _ m', he', mul_one, ha] at h4
  exact sub_eq_zero.1 h4

theorem rel_inj (hs : Function.Surjective res) (ht : res t = 0) (htf : ∀ x : V, t • x = 0 → x = 0)
    (hsat : ∀ s x, res s ≠ 0 → s • x ∈ Λ → x ∈ Λ) (hr : Red res t Λ π) {q q' : Pr R V k} {w : W}
    (h : Rel res t Λ π q w) (h' : Rel res t Λ π q' w) : q = q' := by
  obtain ⟨ho, hk, e, he, rfl⟩ := h
  obtain ⟨ho', hk', e', he', hw⟩ := h'
  have m := te_mem ht ho hk (mem_of_one ho he)
  have m' := te_mem ht ho' hk' (mem_of_one ho' he')
  have h1 : e - e' ∈ Λ := mem_of_pi htf hsat hr (by rw [smul_sub]; exact sub_mem m m')
    (by rw [smul_sub, pi_sub hr m m', hw, sub_self])
  have h2 : e' - e ∈ Λ := by rw [← neg_sub]; exact neg_mem h1
  have A := le_of_sub hs ho hk ho' hk' he he' h1
  have B := le_of_sub hs ho' hk' ho hk he' he h2
  ext y
  · exact ⟨fun h => (A y h).1, fun h => (B y h).1⟩
  · by_cases hy : y ∈ q.L
    · exact (A y hy).2.symm
    · rw [ho.off y hy, ho'.off y (fun h => hy (B y h).1)]

theorem rel_ne (ht : res t = 0) (htf : ∀ x : V, t • x = 0 → x = 0)
    (hsat : ∀ s x, res s ≠ 0 → s • x ∈ Λ → x ∈ Λ) (hr : Red res t Λ π) (q : Pr R V k) :
    ¬ Rel res t Λ π q 0 := by
  rintro ⟨ho, hk, e, he, h⟩
  have := ((hk _).1 (mem_of_pi htf hsat hr (te_mem ht ho hk (mem_of_one ho he)) h)).2
  rw [he] at this
  exact one_ne_zero this

theorem rel_ex (hs : Function.Surjective res) {q : Pr R V k} (ho : q.Ok res) (hk : q.IsKer Λ) :
    ∃ w, Rel res t Λ π q w := by
  obtain ⟨x, hx⟩ := ho.ne
  have m : x ∈ q.L := by
    by_contra hn
    exact hx (ho.off x hn)
  obtain ⟨a, ha⟩ := hs (q.f x)⁻¹
  exact ⟨_, ho, hk, a • x, by rw [ho.smul _ _ m, ha, inv_mul_cancel₀ hx], rfl⟩

theorem rel_dil (hs : Function.Surjective res) (ht : res t = 0) (hr : Red res t Λ π) {q : Pr R V k} {w : W}
    (h : Rel res t Λ π q w) {a : k} (ha : a ≠ 0) : Rel res t Λ π (q.dil a⁻¹) (a • w) := by
  obtain ⟨ho, hk, e, he, rfl⟩ := h
  obtain ⟨b, rfl⟩ := hs a
  have m := mem_of_one ho he
  refine ⟨ho.dil (inv_ne_zero ha), fun y => ?_, b • e, ?_, ?_⟩
  · rw [hk y]
    show _ ↔ y ∈ q.L ∧ (res b)⁻¹ * q.f y = 0
    simp [ha]
  · show (res b)⁻¹ * q.f (b • e) = 1
    rw [ho.smul _ _ m, he, mul_one, inv_mul_cancel₀ ha]
  · rw [smul_comm, hr.smul _ _ (te_mem ht ho hk m)]

end GlobalTheory.LevelHecke.UpInj

namespace GlobalTheory.LevelHecke


open UpInj in
theorem eq_zero_of_upSum_of_norm : ∀ (R V k W M : Type) [CommRing R] [AddCommGroup V] [Module R V] [Field k] [AddCommGroup W] [Module k W] [Fintype k] [DecidableEq k] [Finite W] [AddCommGroup M] [Module ℂ M] (res : R →+* k) (t : R) (Λ : Submodule R V) (π : V → W) (Φ : Pr R V k → M), Function.Surjective res → res t = 0 → (∀ x : V, t • x = 0 → x = 0) → (∀ s x, res s ≠ 0 → s • x ∈ Λ → x ∈ Λ) → Red res t Λ π → (∀ g : Module.Dual k W, g ≠ 0 → ∃ d : Pr R V k, d.L = Λ ∧ (∀ x ∈ Λ, d.f x = g (π x)) ∧ ∑ᶠ q ∈ {q | Pr.Inc res t d q}, Φ q = 0) → (∀ q : Pr R V k, q.Ok res → q.IsKer Λ → ∑ a : kˣ, Φ (q.dil (a : k)) = 0) → ∀ q : Pr R V k, q.Ok res → q.IsKer Λ → Φ q = 0 := by
  intro R V k W M _ _ _ _ _ _ _ _ _ _ _ res t Λ π Φ hs ht htf hsat hr hup hnm
  classical
  let ψ : W → M := fun w => if h : ∃ q, Rel res t Λ π q w then Φ h.choose else 0
  have ψ1 : ∀ q w, Rel res t Λ π q w → ψ w = Φ q := fun q w h => by
    have h0 : ∃ q, Rel res t Λ π q w := ⟨q, h⟩
    simp only [ψ, dif_pos h0]
    rw [rel_inj hs ht htf hsat hr h0.choose_spec h]
  have ψ0 : ∀ w, (¬ ∃ q, Rel res t Λ π q w) → ψ w = 0 := fun w h => dif_neg h
  let j : Pr R V k → W := fun q => if h : ∃ w, Rel res t Λ π q w then h.choose else 0
  have j1 : ∀ q : Pr R V k, q.Ok res → q.IsKer Λ → Rel res t Λ π q (j q) := fun q ho hk => by
    have h0 : ∃ w, Rel res t Λ π q w := rel_ex hs ho hk
    simp only [j, dif_pos h0]
    exact h0.choose_spec
  have key := GlobalTheory.T.eq_zero_of_affineHyperplane_line_sums k W M ψ (ψ0 _ fun ⟨q, h⟩ => rel_ne ht htf hsat hr q h) (fun g hg => ?_) (fun w => ?_)
  · intro q ho hk
    rw [← ψ1 q _ (j1 q ho hk)]
    exact key _
  · obtain ⟨d, rfl, hd, hsum⟩ := hup g hg
    have hinj : Set.InjOn j {q | Pr.Inc res t d q} := fun q hq q' hq' h =>
      rel_inj hs ht htf hsat hr (j1 q hq.1 hq.2.1) (h ▸ j1 q' hq'.1 hq'.2.1)
    have e1 : ∑ᶠ x ∈ {x | g x = 1}, ψ x = ∑ᶠ x ∈ j '' {q | Pr.Inc res t d q}, ψ x := by
      apply finsum_mem_inter_support_eq'
      intro w hw
      have hex : ∃ q, Rel res t d.L π q w := by
        by_contra hn
        exact hw (ψ0 w hn)
      obtain ⟨q, hq⟩ := hex
      constructor
      · intro hg1
        refine ⟨q, ?_, rel_fun ht hr (j1 q hq.1 hq.2.1) hq⟩
        obtain ⟨ho, hk, e, he, rfl⟩ := hq
        exact ⟨ho, hk, e, he, by rw [hd _ (te_mem ht ho hk (mem_of_one ho he))]; exact hg1⟩
      · rintro ⟨q', ⟨ho, hk, e, he, h1⟩, rfl⟩
        rw [hd _ (te_mem ht ho hk (mem_of_one ho he))] at h1
        show g _ = 1
        rw [rel_fun ht hr (j1 q' ho hk) ⟨ho, hk, e, he, rfl⟩]
        exact h1
    rw [e1, finsum_mem_image hinj, ← hsum]
    exact finsum_mem_congr rfl fun q hq => ψ1 q _ (j1 q hq.1 hq.2.1)
  · by_cases hex : ∃ q, Rel res t Λ π q w
    · obtain ⟨q, hq⟩ := hex
      rw [← hnm q hq.1 hq.2.1, ← Equiv.sum_comp (Equiv.inv kˣ)]
      refine Finset.sum_congr rfl fun a _ => ?_
      have := ψ1 _ _ (rel_dil hs ht hr hq (a⁻¹).ne_zero)
      rw [Units.val_inv_eq_inv_val, inv_inv] at this
      rw [← this, Equiv.inv_apply, Units.val_inv_eq_inv_val]
    · refine Finset.sum_eq_zero fun a _ => ψ0 _ ?_
      rintro ⟨q, hq⟩
      have := rel_dil hs ht hr hq (inv_ne_zero a.ne_zero)
      rw [smul_smul, inv_mul_cancel₀ a.ne_zero, one_smul] at this
      exact hex ⟨_, this⟩

end GlobalTheory.LevelHecke
end

section

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal

namespace GlobalTheory.HeckeGal

theorem exists_units_hom {Γ K : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [Field K] [TopologicalSpace K]
    (F : Γ →* K) (hF : Continuous F) : ∃ f : Γ →* Kˣ, Continuous f ∧ ∀ x, ((f x : Kˣ) : K) = F x :=
  ⟨F.toHomUnits, Units.continuous_iff.mpr ⟨hF, hF.comp continuous_inv⟩, fun _ => rfl⟩

theorem exists_infPow_hom : ∀ (E : Type) [Field E] [NumberField E] (n : (E →+* ℂ) → ℤ), ∃ f : Ideles E →* ℂˣ, Continuous f ∧ ∀ x : Ideles E, ((f x : ℂˣ) : ℂ) = infPow n x := by
  intro E _ _ n
  have h0 : ∀ (x : Ideles E) (w : InfinitePlace E), (x : AdeleRing (𝓞 E) E).1 w ≠ 0 := fun x w =>
    left_ne_zero_of_mul_eq_one (congrArg (fun y : AdeleRing (𝓞 E) E => y.1 w) x.mul_inv)
  haveI : ∀ w : InfinitePlace E, Fintype {i : w.Completion →+* ℂ // Continuous i} := fun w =>
    @Fintype.ofFinite _ (finite_contEmbInf w)
  have e : ∀ x : Ideles E, infPow n x = ∏ w : InfinitePlace E, ∏ i : {i : w.Completion →+* ℂ // Continuous i},
      i.1 ((x : AdeleRing (𝓞 E) E).1 w) ^ n (i.1.comp (algebraMap E w.Completion)) := fun x =>
    Finset.prod_congr rfl fun w _ => finprod_eq_prod_of_fintype _
  let F : Ideles E →* ℂ :=
    { toFun := infPow n
      map_one' := by
        rw [e]
        refine Finset.prod_eq_one fun w _ => Finset.prod_eq_one fun i _ => ?_
        rw [show ((1 : Ideles E) : AdeleRing (𝓞 E) E).1 w = 1 from rfl, map_one, one_zpow]
      map_mul' := fun x y => by
        rw [e, e, e, ← Finset.prod_mul_distrib]
        refine Finset.prod_congr rfl fun w _ => ?_
        rw [← Finset.prod_mul_distrib]
        refine Finset.prod_congr rfl fun i _ => ?_
        rw [← mul_zpow, ← map_mul]
        rfl }
  refine exists_units_hom F ?_
  show Continuous (infPow n)
  rw [funext e]
  refine continuous_finsetProd _ fun w _ => continuous_finsetProd _ fun i _ => ?_
  refine Continuous.zpow₀ ?_ _ fun x => Or.inl ((map_ne_zero i.1).mpr (h0 x w))
  exact i.2.comp ((continuous_apply w).comp (continuous_fst.comp Units.continuous_val))

theorem exists_lPow_hom : ∀ (E : Type) [Field E] [NumberField E] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (n : (E →+* ℂ) → ℤ), ∃ f : Ideles E →* (Qbar l)ˣ, Continuous f ∧ ∀ x : Ideles E, ((f x : (Qbar l)ˣ) : Qbar l) = lPow ι n x := by
  intro E _ _ l _ ι n
  have hl : l.Prime := Fact.out
  have h0 : ∀ (x : Ideles E) (v : HeightOneSpectrum (𝓞 E)), (x : AdeleRing (𝓞 E) E).2 v ≠ 0 := fun x w =>
    left_ne_zero_of_mul_eq_one (congrArg (fun y : AdeleRing (𝓞 E) E => y.2 w) x.mul_inv)
  haveI : ∀ v : HeightOneSpectrum (𝓞 E), Fintype {j : v.adicCompletion E →+* Qbar l // Continuous j} := fun v =>
    @Fintype.ofFinite _ (finite_contEmb v)
  have hI : Ideal.span {((l : ℕ) : 𝓞 E)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast hl.ne_zero
  have e : ∀ x : Ideles E, lPow ι n x = ∏ v ∈ (Ideal.finite_factors hI).toFinset,
      ∏ j : {j : v.adicCompletion E →+* Qbar l // Continuous j}, j.1 ((x : AdeleRing (𝓞 E) E).2 v) ^
        n ((ι.toRingHom.comp j.1).comp (algebraMap E (v.adicCompletion E))) := fun x => by
    unfold lPow
    rw [finprod_eq_prod_of_mulSupport_subset (s := (Ideal.finite_factors hI).toFinset)]
    · exact Finset.prod_congr rfl fun w _ => finprod_eq_prod_of_fintype _
    · intro v hv
      by_contra h
      refine hv (locPow_of_notMem ι n (fun hm => h ?_) _)
      exact Finset.mem_coe.mpr ((Set.Finite.mem_toFinset _).mpr (Ideal.dvd_span_singleton.mpr hm))
  let F : Ideles E →* Qbar l :=
    { toFun := lPow ι n
      map_one' := by
        rw [e]
        refine Finset.prod_eq_one fun w _ => Finset.prod_eq_one fun i _ => ?_
        rw [show ((1 : Ideles E) : AdeleRing (𝓞 E) E).2 w = 1 from rfl, map_one, one_zpow]
      map_mul' := fun x y => by
        rw [e, e, e, ← Finset.prod_mul_distrib]
        refine Finset.prod_congr rfl fun w _ => ?_
        rw [← Finset.prod_mul_distrib]
        refine Finset.prod_congr rfl fun i _ => ?_
        rw [← mul_zpow, ← map_mul]
        rfl }
  refine exists_units_hom F ?_
  show Continuous (lPow ι n)
  rw [funext e]
  refine continuous_finsetProd _ fun w _ => continuous_finsetProd _ fun i _ => ?_
  refine Continuous.zpow₀ ?_ _ fun x => Or.inl ((map_ne_zero i.1).mpr (h0 x w))
  exact i.2.comp ((RestrictedProduct.continuous_eval w).comp (continuous_snd.comp Units.continuous_val))

theorem infPow_diagUnits : ∀ (E : Type) [Field E] [NumberField E] (n : (E →+* ℂ) → ℤ) (k : Eˣ), infPow n (diagUnits E k) = ∏ φ : E →+* ℂ, φ (k : E) ^ n φ := by
  intro E _ _ n k
  classical
  let J : InfinitePlace E → Type := fun w => {i : w.Completion →+* ℂ // Continuous i}
  let res : (Σ w, J w) → (E →+* ℂ) := fun p => p.2.1.comp (algebraMap E p.1.Completion)
  have hd : ∀ w : InfinitePlace E, DenseRange (algebraMap E w.Completion) := fun w => by
    refine Dense.mono ?_ (InfinitePlace.Completion.denseRange_coe w)
    rintro _ ⟨a, rfl⟩
    exact ⟨WithAbs.equiv w.1 a, by simp [AbsoluteValue.Completion.algebraMap_def, WithAbs.algebraMap_right_apply]⟩
  have hmk : ∀ p : Σ w, J w, InfinitePlace.mk (res p) = p.1 := by
    rintro ⟨w, i⟩
    have hn : ∀ y : w.Completion, ‖i.1 y‖ = ‖y‖ := fun y => by
      rcases w.isReal_or_isComplex with hw | hw
      · let e := InfinitePlace.Completion.ringEquivRealOfIsReal hw
        have he : Isometry e.symm := (InfinitePlace.Completion.isometryEquivRealOfIsReal hw).symm.isometry
        have h1 := Complex.ringHom_eq_ofReal_of_continuous (f := i.1.comp e.symm.toRingHom) (i.2.comp he.continuous)
        obtain ⟨z, rfl⟩ := e.symm.surjective y
        rw [he.norm_map_of_map_zero (map_zero _)]
        exact (congrArg norm (DFunLike.congr_fun h1 z)).trans (Complex.norm_real z)
      · let e := InfinitePlace.Completion.ringEquivComplexOfIsComplex hw
        have he : Isometry e.symm := (InfinitePlace.Completion.isometryEquivComplexOfIsComplex hw).symm.isometry
        obtain ⟨z, rfl⟩ := e.symm.surjective y
        rw [he.norm_map_of_map_zero (map_zero _)]
        rcases Complex.ringHom_eq_id_or_conj_of_continuous (f := i.1.comp e.symm.toRingHom)
          (i.2.comp he.continuous) with h1 | h1
        · exact congrArg norm (DFunLike.congr_fun h1 z)
        · exact (congrArg norm (DFunLike.congr_fun h1 z)).trans (Complex.norm_conj z)
    refine InfinitePlace.ext _ _ fun a => ?_
    rw [InfinitePlace.apply]
    apply (hn _).trans
    simpa [AbsoluteValue.Completion.algebraMap_def, WithAbs.algebraMap_right_apply] using
      (InfinitePlace.Completion.norm_coe w (WithAbs.toAbs _ a))
  have hinj : Function.Injective res := by
    rintro ⟨v, j⟩ ⟨v', j'⟩ h
    obtain rfl : v = v' := (hmk ⟨v, j⟩).symm.trans ((congrArg InfinitePlace.mk h).trans (hmk ⟨v', j'⟩))
    congr 1
    apply Subtype.ext
    apply DFunLike.coe_injective
    refine (hd v).equalizer j.2 j'.2 ?_
    funext a
    exact DFunLike.congr_fun h a
  have hsurj : Function.Surjective res := by
    intro φ
    obtain ⟨j, hj, e⟩ := GlobalTheory.InfTypeLocal.exists_ext φ
    exact ⟨⟨_, j, hj⟩, RingHom.ext e⟩
  haveI : ∀ w, Fintype (J w) := fun w => @Fintype.ofFinite _ (finite_contEmbInf w)
  rw [← Fintype.prod_bijective res ⟨hinj, hsurj⟩ (fun p => res p (k : E) ^ n (res p)) _ fun _ => rfl,
    Fintype.prod_sigma]
  exact Finset.prod_congr rfl fun w _ => finprod_eq_prod_of_fintype _

theorem isOpenEmbedding_val_inf (E : Type) [Field E] [NumberField E] :
    Topology.IsOpenEmbedding (Units.val : (InfiniteAdeleRing E)ˣ → InfiniteAdeleRing E) :=
  Units.isOpenEmbedding_val (R := ∀ w : InfinitePlace E, w.Completion)

theorem isOpen_connectedComponentOfOne_inf : ∀ (E : Type) [Field E] [NumberField E], IsOpen ((Subgroup.connectedComponentOfOne (InfiniteAdeleRing E)ˣ : Subgroup (InfiniteAdeleRing E)ˣ) : Set (InfiniteAdeleRing E)ˣ) := by
  intro E _ _
  haveI : ∀ w : InfinitePlace E, LocallyConnectedSpace w.Completion := fun w => by
    rcases w.isReal_or_isComplex with hw | hw
    · exact (InfinitePlace.Completion.isometryEquivRealOfIsReal hw).toHomeomorph.locallyConnectedSpace
    · exact (InfinitePlace.Completion.isometryEquivComplexOfIsComplex hw).toHomeomorph.locallyConnectedSpace
  haveI : LocallyConnectedSpace (InfiniteAdeleRing E) :=
    inferInstanceAs (LocallyConnectedSpace (∀ w : InfinitePlace E, w.Completion))
  haveI : LocallyConnectedSpace (InfiniteAdeleRing E)ˣ := (isOpenEmbedding_val_inf E).locallyConnectedSpace
  exact isOpen_connectedComponent

theorem denseRange_units_inf : ∀ (E : Type) [Field E] [NumberField E], DenseRange (fun k : Eˣ => (Units.map (algebraMap E (InfiniteAdeleRing E)).toMonoidHom k : (InfiniteAdeleRing E)ˣ)) := by
  intro E _ _
  rw [DenseRange, dense_iff_inter_open]
  rintro U hU ⟨u, hu⟩
  obtain ⟨k, v, hv, hk⟩ := (InfiniteAdeleRing.denseRange_algebraMap E).exists_mem_open
    ((isOpenEmbedding_val_inf E).isOpenMap U hU) ⟨_, u, hu, rfl⟩
  have hk0 : k ≠ 0 := by
    rintro rfl
    obtain ⟨w⟩ : Nonempty (InfinitePlace E) := inferInstance
    rw [map_zero] at hk
    have h1 := congrFun v.mul_inv w
    rw [hk, zero_mul] at h1
    exact zero_ne_one (α := w.Completion) h1
  exact ⟨v, hv, Units.mk0 k hk0, Units.ext hk.symm⟩

theorem pos_of_mem_connectedComponentOfOne : ∀ (E : Type) [Field E] [NumberField E] (k : Eˣ), (Units.map (algebraMap E (InfiniteAdeleRing E)).toMonoidHom k : (InfiniteAdeleRing E)ˣ) ∈ Subgroup.connectedComponentOfOne (InfiniteAdeleRing E)ˣ → ∀ φ : E →+* ℝ, 0 < φ (k : E) := by
  intro E _ _ k hk φ
  obtain ⟨e, he, hek⟩ := GlobalTheory.InfTypeLocal.exists_ext (Complex.ofRealHom.comp φ)
  let w := InfinitePlace.mk (Complex.ofRealHom.comp φ)
  have hd : DenseRange (algebraMap E w.Completion) := by
    refine Dense.mono ?_ (InfinitePlace.Completion.denseRange_coe w)
    rintro _ ⟨a, rfl⟩
    exact ⟨WithAbs.equiv w.1 a, by simp [AbsoluteValue.Completion.algebraMap_def, WithAbs.algebraMap_right_apply]⟩
  have him : ∀ y : w.Completion, (e y).im = 0 := fun y =>
    congrFun (hd.equalizer (g := fun y => (e y).im) (h := fun _ => 0) (Complex.continuous_im.comp he)
      continuous_const (funext fun a => (congrArg Complex.im (hek a)).trans (by simp))) y
  let g : (InfiniteAdeleRing E)ˣ → ℝ := fun u => (e ((u : InfiniteAdeleRing E) w)).re
  have hg : Continuous g :=
    Complex.continuous_re.comp (he.comp ((continuous_apply w).comp Units.continuous_val))
  have hg0 : ∀ u, g u ≠ 0 := fun u h => by
    have h1 : e ((u : InfiniteAdeleRing E) w) = 0 := Complex.ext h (him _)
    exact left_ne_zero_of_mul_eq_one (congrFun u.mul_inv w) ((map_eq_zero e).mp h1)
  have hg1 : g 1 = 1 := by
    show (e 1).re = 1
    simp
  have hgk : g (Units.map (algebraMap E (InfiniteAdeleRing E)).toMonoidHom k) = φ k := by
    show (e (algebraMap E _ (k : E))).re = _
    rw [hek]
    simp
  by_contra hneg
  have := isPreconnected_connectedComponent.intermediate_value hk mem_connectedComponent hg.continuousOn
    (show (0 : ℝ) ∈ Set.Icc _ _ from ⟨by rw [hgk]; exact not_lt.mp hneg, by rw [hg1]; exact zero_le_one⟩)
  obtain ⟨u, -, hu⟩ := this
  exact hg0 u hu

end GlobalTheory.HeckeGal

end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.GoodProjLift

theorem exists_factor {U H X : Type} [AddCommGroup U] [Module ℂ U] [AddCommGroup H] [Module ℂ H]
    [AddCommGroup X] [Module ℂ X] (e : H →ₗ[ℂ] X) (he : Function.Injective e) (f : U →ₗ[ℂ] X)
    (hf : ∀ x, f x ∈ LinearMap.range e) : ∃ g : U →ₗ[ℂ] H, ∀ x, e (g x) = f x := by
  refine ⟨(LinearEquiv.ofInjective e he).symm.toLinearMap ∘ₗ f.codRestrict _ hf, fun x => ?_⟩
  have h := (LinearEquiv.ofInjective e he).apply_symm_apply (f.codRestrict _ hf x)
  exact congrArg Subtype.val h

theorem postOn_sum_smul {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) {G : Type} [Fintype G]
    (c : G → ℂ) (L : G → (GA D V → ℂ) →ₗ[ℂ] (GA D V → ℂ)) (T : MMap M) :
    postOn M (∑ g, c g • L g) T = ∑ g, c g • postOn M (L g) T := by
  ext v h
  simp [postOn_apply, LinearMap.sum_apply]

theorem postOn_sum_mem_range {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) {G : Type} [Fintype G]
    {H : Type} [AddCommGroup H] [Module ℂ H] (e : H →ₗ[ℂ] MMap M)
    (c : G → ℂ) (L : G → (GA D V → ℂ) →ₗ[ℂ] (GA D V → ℂ)) (a : G → H →ₗ[ℂ] H)
    (ha : ∀ g y, e (a g y) = postOn M (L g) (e y)) {T : MMap M} (hT : T ∈ LinearMap.range e) :
    postOn M (∑ g, c g • L g) T ∈ LinearMap.range e := by
  obtain ⟨y, rfl⟩ := hT
  refine ⟨∑ g, c g • a g y, ?_⟩

  rw [postOn_sum_smul, map_sum]
  exact Finset.sum_congr rfl fun g _ => by rw [map_smul, ha]

theorem is_inj {X : Type} [AddCommGroup X] [Module ℂ X] {M : HMod X} {V : Submodule ℂ X} {ip : X → X → ℂ}
    (h : M.Is V ip) : Function.Injective M.e := h.1

theorem is_range {X : Type} [AddCommGroup X] [Module ℂ X] {M : HMod X} {V : Submodule ℂ X} {ip : X → X → ℂ}
    (h : M.Is V ip) : LinearMap.range M.e = V := h.2.1

theorem exists_factor_hmod {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} {M : DSModel V S} {G : Type} [Fintype G]
    {U : Type} [AddCommGroup U] [Module ℂ U] {H : HMod (MMap M)} {W : Submodule ℂ (MMap M)}
    {ip : MMap M → MMap M → ℂ} (hH : H.Is W ip)
    (c : G → ℂ) {L : G → (GA D V → ℂ) →ₗ[ℂ] (GA D V → ℂ)} {a : G → H.H →ₗ[ℂ] H.H}
    (ha : ∀ g y, H.e (a g y) = postOn M (L g) (H.e y)) (f : U →ₗ[ℂ] MMap M) (hf : ∀ x, f x ∈ W) :
    ∃ th : U →ₗ[ℂ] H.H, ∀ x, H.e (th x) = postOn M (∑ g, c g • L g) (f x) :=
  exists_factor _ (is_inj hH) (postOn M (∑ g, c g • L g) ∘ₗ f) fun x =>
    postOn_sum_mem_range M H.e c L a ha (by rw [is_range hH]; exact hf x)



theorem exists_thG : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → R.IsFam → R.IsModels → R.thP_thF_mem → ∃ th, ({ R with thG := th } : RealDat D A Ks).thP_thG := by
  intro D G _ _ Pl0 T A Ks _ _ _ R _ _ hM hF
  have key : ∀ i t, ∃ th : (R.HV i t).H →ₗ[ℂ] (R.HW i (sg0 D A)).H,
      ∀ x, (R.HW i (sg0 D A)).e (th x) = postOn _ (R.eWf i (sg0 D A)) (R.thF i t x) := fun i t =>
    exists_factor_hmod (hM.HW i (sg0 D A)) (RealDat.eC (A := A) (sg0 D A)) (hM.gW i (sg0 D A)) (R.thF i t) (hF i t)
  choose th hth using key
  exact ⟨th, hth⟩

end GlobalTheory.GoodProjLift
end
