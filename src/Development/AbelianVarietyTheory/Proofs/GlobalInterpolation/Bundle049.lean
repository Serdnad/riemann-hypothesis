module

public import Formalism.LocalToGlobal.KernelLattices.DeterminantCokernelCount.CokernelIndexFactors.Bundle001
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.IsDiscriminantTwelfthRootOfIdealLattice
public import Mathlib.GroupTheory.Index
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Formalism.LocalToGlobal.Columns.StdLatUnimodular
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
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Mathlib.Topology.Sheaves.Presheaf
import Std.Tactic.BVDecide.Normalize.Prop
import Formalism.SatakeDualWeyl.Statement
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.Bundle001
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Mathlib.RingTheory.Filtration

@[expose] public section

section

noncomputable section
open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker

namespace GlobalTheory.MomentPinned

theorem isLocallyConstant_toZModPow {p : ℕ} [Fact p.Prime] (n : ℕ) :
    IsLocallyConstant (PadicInt.toZModPow (p := p) n) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  have hq : (0 : ℝ) < (p : ℝ) ^ (-(n : ℤ)) := zpow_pos (by exact_mod_cast (Fact.out : p.Prime).pos) _
  filter_upwards [Metric.ball_mem_nhds x hq] with y hy
  rw [← sub_eq_zero, ← map_sub, ← RingHom.mem_ker, PadicInt.ker_toZModPow, ← PadicInt.norm_le_pow_iff_mem_span_pow]
  rw [Metric.mem_ball, dist_eq_norm] at hy
  exact hy.le

theorem isLocallyConstant_red {p : ℕ} [Fact p.Prime] (r n : ℕ) :
    IsLocallyConstant (fun a : Fin r → ℤ_[p] => fun i => PadicInt.toZModPow n (a i)) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  have : ∀ i, ∀ᶠ y in nhds x, PadicInt.toZModPow n (y i) = PadicInt.toZModPow n (x i) := fun i =>
    ((isLocallyConstant_toZModPow n).comp_continuous (continuous_apply i)).eventually_eq x
  filter_upwards [Filter.eventually_all.2 this] with y hy using funext hy

theorem continuous_zc {p : ℕ} [Fact p.Prime] : Continuous (JMB.zc : ℤ_[p] → ℂ_[p]) := by
  unfold JMB.zc
  exact (continuous_algebraMap ℚ_[p] ℂ_[p]).comp continuous_subtype_val

theorem continuous_pairD {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (Ω : ℂ_[p]) {g : ℕ} (d : ℕ)
    (Hm : Matrix (Fin g) (Fin g) ℂ) {r : ℕ} (b : Fin r → Fin g → ℂ) (y : Fin g → ℂ) :
    Continuous (JMB.pairD lam Ω d Hm b y) := by
  unfold JMB.pairD
  have := continuous_zc (p := p)
  fun_prop

theorem continuous_charPart {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) {g : ℕ}
    (Hm : Matrix (Fin g) (Fin g) ℂ) {r : ℕ} (n : ℕ) (b : Fin r → Fin g → ℂ) (Y : Fin g → ℂ) :
    Continuous fun a : Fin r → ℤ_[p] => JMB.lamA lam (JMB.kap Hm (JMB.vecA n b a) Y) :=
  ((isLocallyConstant_red (p := p) r n).comp (fun s : Fin r → ZMod (p ^ n) =>
    JMB.lamA lam (JMB.kap Hm (∑ i, (((s i).val : ℕ) : ℂ) • b i) Y))).continuous

theorem eq_of_natCast : ∀ (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (Ω : ℂ_[p]) (g : ℕ) (S : JMB.Setup g) (r n k : ℕ) (bS : Fin r → Fin g → ℂ) (Y : Fin g → ℂ) (ys : Fin k → Fin g → ℂ) (f : C(Fin r → ℤ_[p], ℂ_[p])), (∀ a : Fin r → ℕ, f (fun i => (a i : ℤ_[p])) = JMB.lamA lam (JMB.kap S.Hm (JMB.vecA n bS (fun i => (a i : ℤ_[p]))) Y) * ∏ j, JMB.pairD lam Ω S.d S.Hm bS (ys j) (fun i => (a i : ℤ_[p]))) → ∀ a, f a = JMB.lamA lam (JMB.kap S.Hm (JMB.vecA n bS a) Y) * ∏ j, JMB.pairD lam Ω S.d S.Hm bS (ys j) a := by
  intro p _ lam Ω g S r n k bS Y ys f h a
  have hR : Continuous fun a : Fin r → ℤ_[p] =>
      JMB.lamA lam (JMB.kap S.Hm (JMB.vecA n bS a) Y) * ∏ j, JMB.pairD lam Ω S.d S.Hm bS (ys j) a :=
    (continuous_charPart lam S.Hm n bS Y).mul
      (continuous_finsetProd Finset.univ fun j _ => continuous_pairD lam Ω S.d S.Hm bS (ys j))
  have hd : DenseRange (fun a : Fin r → ℕ => fun i => (a i : ℤ_[p])) :=
    DenseRange.piMap fun _ : Fin r => PadicInt.denseRange_natCast (p := p)
  exact congr_fun (hd.equalizer f.continuous hR (funext h)) a

end GlobalTheory.MomentPinned
end
end

section

open NumberField

namespace GlobalTheory.InverseHalfDifferent

theorem exists_single_mem_span {E M ι : Type} [Field E] [NumberField E] [Field M] [NumberField M]
    [Finite ι] [DecidableEq ι] (f : ι → E →+* M) (hf : Function.Injective f) (i : ι) :
    ∃ s : M, s ≠ 0 ∧ (Pi.single i s : ι → M) ∈
      Submodule.span (𝓞 M) (Set.range fun a : 𝓞 E => fun j => f j (a : E)) := by
  classical
  cases nonempty_fintype ι

  let χ : ι → (𝓞 E →* M) := fun j => ((f j).comp (algebraMap (𝓞 E) E)).toMonoidHom
  have hχ : Function.Injective χ := by
    intro j k h
    apply hf
    apply IsFractionRing.ringHom_ext (A := 𝓞 E)
    intro x
    exact DFunLike.congr_fun h x
  have hli : LinearIndependent M (fun j => (χ j : 𝓞 E → M)) :=
    (linearIndependent_monoidHom (𝓞 E) M).comp χ hχ

  have htop : Submodule.span M (Set.range fun a : 𝓞 E => fun j => f j (a : E)) = ⊤ := by
    by_contra hne
    obtain ⟨φ, hφ0, hφ⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.mpr hne)
    apply hφ0
    have hc : ∀ j, φ (fun k => if j = k then 1 else 0) = 0 := by
      have key : ∑ j, φ (fun k => if j = k then 1 else 0) • (χ j : 𝓞 E → M) = 0 := by
        funext a
        have ha : φ (fun j => f j (a : E)) = 0 := hφ (Submodule.subset_span ⟨a, rfl⟩)
        rw [LinearMap.pi_apply_eq_sum_univ] at ha
        simpa [χ, Finset.sum_apply, mul_comm] using ha
      exact Fintype.linearIndependent_iff.mp hli _ key
    refine LinearMap.ext fun x => ?_
    rw [LinearMap.pi_apply_eq_sum_univ]
    simp [hc]

  have h1 : (Pi.single i 1 : ι → M) ∈ Submodule.span M (Set.range fun a : 𝓞 E => fun j => f j (a : E)) := by
    rw [htop]; exact Submodule.mem_top
  obtain ⟨y, hy, z, hz⟩ := (IsLocalization.mem_span_iff (nonZeroDivisors (𝓞 M))).mp h1
  refine ⟨algebraMap (𝓞 M) M z, IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors z.2, ?_⟩
  have hy' : y = algebraMap (𝓞 M) M z • (Pi.single i 1 : ι → M) := by
    rw [hz, smul_smul, IsLocalization.mk'_spec', map_one, one_smul]
  have : (Pi.single i (algebraMap (𝓞 M) M z) : ι → M) = y := by
    rw [hy']
    ext k
    by_cases hk : k = i
    · subst hk; simp
    · simp [hk]
  rw [this]
  exact hy

open Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric

theorem integers_mem_inverse_half_different {R : Ranks} (H : Host R) (a : 𝓞 H.E) :
    (a : H.E) ∈ (H.AA0 : Submodule (𝓞 H.E) H.E) := by

  have hb : H.𝔟 ≠ ⊥ := by
    intro h
    have h2 := H.𝔟_spec.2
    simp [h] at h2
  have hle : (H.𝔟 : FractionalIdeal (nonZeroDivisors (𝓞 H.E)) H.E) ≤ 1 := FractionalIdeal.coeIdeal_le_one
  have hne : (H.𝔟 : FractionalIdeal (nonZeroDivisors (𝓞 H.E)) H.E) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.mpr hb

  have h1 : (1 : FractionalIdeal (nonZeroDivisors (𝓞 H.E)) H.E) ≤ H.AA0 := by
    have := FractionalIdeal.inv_anti_mono hne hle
    simpa [Host.AA0] using this
  exact h1 ((FractionalIdeal.mem_one_iff _).mpr ⟨a, rfl⟩)

theorem emb_injective {R : Ranks} (H : Host R) : Function.Injective H.emb := by
  intro g g' h
  have hσ : H.sigmaOf g = H.sigmaOf g' := by
    ext x
    have hx := DFunLike.congr_fun h x
    simp only [Host.emb, RingHom.comp_apply] at hx
    exact H.φ₀.injective hx
  exact H.gal.symm.injective hσ

theorem embT_injective (D : D7) : Function.Injective (embT D) := by
  intro τ τ' h
  exact D.eTau.injective (Subtype.ext (emb_injective D.host h))

theorem ellT_ne_bot {D : D7} {M : IntermediateField ℚ ℂ} [NumberField M]
    (hM : ∀ (τ : D.what₂.Tau) (x : D.host.E), (embT D τ : D.host.E → ℂ) x ∈ M)
    (τ : D.what₂.Tau) : ellT D M τ ≠ ⊥ := by
  classical

  let f : D.what₂.Tau → D.host.E →+* M := fun σ => (embT D σ).codRestrict M (hM σ)
  have hf : Function.Injective f := by
    intro σ σ' h
    apply embT_injective D
    ext x
    exact congrArg Subtype.val (DFunLike.congr_fun h x)
  obtain ⟨s, hs0, hs⟩ := exists_single_mem_span f hf τ

  have hle : Submodule.span (𝓞 M) (Set.range fun a : 𝓞 D.host.E => fun j => f j (a : D.host.E)) ≤ mmM D M := by
    rw [Submodule.span_le]
    rintro _ ⟨a, rfl⟩
    refine Submodule.subset_span ⟨(a : D.host.E), integers_mem_inverse_half_different D.host a, ?_⟩
    funext j
    unfold Formalism.MainNotions.TaylorLogMetric.liftM
    rw [dite_eq_left (hM j _)]
    rfl
  intro h
  have hs' : s ∈ ellT D M τ := by
    rw [ellT, Submodule.mem_comap]
    simpa using hle hs
  rw [h, Submodule.mem_bot] at hs'
  exact hs0 hs'

end GlobalTheory.InverseHalfDifferent
end

section

open NumberField IsDedekindDomain Matrix Formalism.UG Formalism.BasicNotions Formalism.MainNotions.StandardLattice
open scoped TensorProduct

namespace GlobalTheory

theorem exists_mem_proj_eq_on_finset {G ι : Type} [Group G] {Gv : ι → Type}
    [∀ v, Group (Gv v)] (π : ∀ v, G →* Gv v) (H : Subgroup G) (Kv : ∀ v, Subgroup (Gv v))
    (hH : ∀ v, ∀ h ∈ Kv v, ∃ g ∈ H, π v g = h ∧ ∀ w, w ≠ v → π w g = 1)
    (h : ∀ v, Gv v) (hh : ∀ v, h v ∈ Kv v) (T : Finset ι) :
    ∃ g ∈ H, (∀ v ∈ T, π v g = h v) ∧ ∀ v, v ∉ T → π v g = 1 := by
  classical
  induction T using Finset.induction_on with
  | empty => exact ⟨1, H.one_mem, by simp, by simp⟩
  | insert a T ha ih =>
    obtain ⟨g, hg, h1, h2⟩ := ih
    obtain ⟨g', hg', h3, h4⟩ := hH a (h a) (hh a)
    refine ⟨g' * g, H.mul_mem hg' hg, ?_, ?_⟩
    · intro v hv
      rcases Finset.mem_insert.1 hv with rfl | hv
      · rw [map_mul, h3, h2 _ ha, mul_one]
      · have hne : v ≠ a := fun e => ha (e ▸ hv)
        rw [map_mul, h4 v hne, h1 v hv, one_mul]
    · intro v hv
      rw [Finset.mem_insert, not_or] at hv
      rw [map_mul, h4 v hv.1, h2 v hv.2, one_mul]

theorem index_pi_univ_dep {ι : Type} [Fintype ι] {G : ι → Type} [∀ i, Group (G i)]
    (H : ∀ i, Subgroup (G i)) :
    (Subgroup.pi Set.univ H).index = ∏ i, (H i).index := by
  simp_rw [Subgroup.index, ← Nat.card_pi]
  refine Nat.card_congr
    ((Quotient.congrRight (fun x y ↦ ?_)).trans (Setoid.piQuotientEquiv _).symm)
  rw [QuotientGroup.leftRel_pi]

theorem relIndex_eq_prod_local :
    ∀ (G ι : Type) [Group G] (Gv : ι → Type) [∀ v, Group (Gv v)] (π : ∀ v, G →* Gv v)
      (H K U : Subgroup G) (Kv Uv : ∀ v, Subgroup (Gv v)) (S : Finset ι),
      (∀ v, ∀ h ∈ Kv v, ∃ g ∈ H, π v g = h ∧ ∀ w, w ≠ v → π w g = 1) →
      (∀ g, g ∈ K ↔ g ∈ H ∧ ∀ v, π v g ∈ Kv v) →
      (∀ g, g ∈ U ↔ g ∈ H ∧ ∀ v, π v g ∈ Uv v) →
      (∀ v, v ∉ S → Kv v ≤ Uv v) →
      U.relIndex K = ∏ v ∈ S, (Uv v).relIndex (Kv v) := by
  intro G ι _ Gv _ π H K U Kv Uv S hH hK hU hS
  classical
  let f : K →* (∀ v : S, Kv v) :=
    { toFun := fun g v => ⟨π v g, ((hK g).1 g.2).2 v⟩
      map_one' := by
        funext v
        apply Subtype.ext
        simp
      map_mul' := by
        intro a b
        funext v
        apply Subtype.ext
        simp }
  have hf : Function.Surjective f := by
    intro x
    let h : ∀ v, Gv v := fun v => if hv : v ∈ S then (x ⟨v, hv⟩ : Gv v) else 1
    have hh : ∀ v, h v ∈ Kv v := by
      intro v
      by_cases hv : v ∈ S
      · simp only [h, dif_pos hv]; exact (x ⟨v, hv⟩).2
      · simp only [h, dif_neg hv]; exact (Kv v).one_mem
    obtain ⟨g, hg, h1, h2⟩ := exists_mem_proj_eq_on_finset π H Kv hH h hh S
    have hgK : g ∈ K := by
      refine (hK g).2 ⟨hg, fun v => ?_⟩
      by_cases hv : v ∈ S
      · rw [h1 v hv]; exact hh v
      · rw [h2 v hv]; exact (Kv v).one_mem
    refine ⟨⟨g, hgK⟩, ?_⟩
    funext v
    apply Subtype.ext
    change π v g = _
    rw [h1 v v.2]
    simp only [h, dif_pos v.2]
  have hc : U.subgroupOf K =
      (Subgroup.pi Set.univ fun v : S => (Uv v).subgroupOf (Kv v)).comap f := by
    ext g
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_comap, Subgroup.mem_pi, hU]
    constructor
    · rintro ⟨-, h⟩ v -
      exact Subgroup.mem_subgroupOf.2 (h v)
    · intro h
      refine ⟨((hK g).1 g.2).1, fun v => ?_⟩
      by_cases hv : v ∈ S
      · exact Subgroup.mem_subgroupOf.1 (h ⟨v, hv⟩ (Set.mem_univ _))
      · exact hS v hv (((hK g).1 g.2).2 v)
  rw [Subgroup.relIndex, hc, Subgroup.index_comap_of_surjective _ hf, index_pi_univ_dep]
  exact Finset.prod_coe_sort S (fun v => (Uv v).relIndex (Kv v))

end GlobalTheory
end

section

open NumberField IsDedekindDomain

namespace GlobalTheory

theorem ringHom_eq_of_comap_eq_unramified_degree_one
    (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] (φ ψ : E →+* K)
    (w : HeightOneSpectrum (𝓞 K)) (Q : HeightOneSpectrum (𝓞 E)) (p : ℕ) (hp : p.Prime)
    (hN : Ideal.absNorm Q.asIdeal = p) (hsq : ((p : ℕ) : 𝓞 E) ∉ Q.asIdeal ^ 2)
    (hφ : ∀ r : 𝓞 E, r ∈ Q.asIdeal ↔ RingOfIntegers.mapRingHom φ r ∈ w.asIdeal)
    (hψ : ∀ r : 𝓞 E, r ∈ Q.asIdeal ↔ RingOfIntegers.mapRingHom ψ r ∈ w.asIdeal) :
    φ = ψ := by
  set f := RingOfIntegers.mapRingHom φ with hf
  set g := RingOfIntegers.mapRingHom ψ with hg
  have hpQ : ((p : ℕ) : 𝓞 E) ∈ Q.asIdeal := hN ▸ Ideal.absNorm_mem Q.asIdeal
  have hQp := Q.isPrime

  have h1 : ∀ x : 𝓞 E, ∃ a : ℤ, x - (a : 𝓞 E) ∈ Q.asIdeal := by
    intro x
    haveI : Fact p.Prime := ⟨hp⟩
    have hc : Nat.card (𝓞 E ⧸ Q.asIdeal) = p := by
      rw [← hN, Ideal.absNorm_apply, Submodule.cardQuot_apply]
    have h := mem_zmultiples_of_prime_card (g := (1 : 𝓞 E ⧸ Q.asIdeal))
      (g' := Ideal.Quotient.mk Q.asIdeal x) hc one_ne_zero
    obtain ⟨a, ha⟩ := AddSubgroup.mem_zmultiples_iff.1 h
    refine ⟨a, Ideal.Quotient.eq.1 ?_⟩
    rw [← ha, map_intCast, zsmul_one]
  have h2 : Ideal.span {((p : ℕ) : 𝓞 E)} ⊔ Q.asIdeal ^ 2 = Q.asIdeal := by
    have h := Ideal.eq_prime_pow_of_succ_lt_of_le (P := Q.asIdeal) (i := 1)
      (I := Ideal.span {((p : ℕ) : 𝓞 E)} ⊔ Q.asIdeal ^ 2) Q.ne_bot ?_ ?_
    · simpa using h
    · refine lt_of_le_of_ne le_sup_right fun h => hsq ?_
      have h' : ((p : ℕ) : 𝓞 E) ∈ Ideal.span {((p : ℕ) : 𝓞 E)} ⊔ Q.asIdeal ^ 2 :=
        Ideal.mem_sup_left (Ideal.mem_span_singleton_self _)
      rw [← h] at h'
      exact h'
    · rw [pow_one]
      exact sup_le ((Ideal.span_singleton_le_iff_mem _).2 hpQ) (Ideal.pow_le_self two_ne_zero)
  have h3 : ∀ n : ℕ, Q.asIdeal ≤ Ideal.span {((p : ℕ) : 𝓞 E)} ⊔ Q.asIdeal ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rcases n with _ | n
      · simp
      refine h2.ge.trans (sup_le le_sup_left ?_)
      rw [sq]
      refine (Ideal.mul_mono_right ih).trans ?_
      rw [Ideal.mul_sup, ← pow_succ']
      exact sup_le_sup_right Ideal.mul_le_right _
  have hmap : ∀ (k : 𝓞 E →+* 𝓞 K), (∀ r : 𝓞 E, r ∈ Q.asIdeal ↔ k r ∈ w.asIdeal) →
      ∀ (n : ℕ) (z : 𝓞 E), z ∈ Q.asIdeal ^ n → k z ∈ w.asIdeal ^ n := by
    intro k hk n z hz
    have h := Ideal.mem_map_of_mem k hz
    rw [Ideal.map_pow] at h
    refine Ideal.pow_right_mono ?_ n h
    exact Ideal.map_le_iff_le_comap.2 fun r hr => (hk r).1 hr
  have hpw : ((p : ℕ) : 𝓞 K) ∈ w.asIdeal := by
    simpa using (hφ _).1 hpQ
  have h4 : ∀ (n : ℕ) (x : 𝓞 E), f x - g x ∈ w.asIdeal ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      intro x
      obtain ⟨a, ha⟩ := h1 x
      obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.1 (h3 (n + 1) ha)
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hy
      have hx : x = c * p + z + a := by rw [hyz]; ring
      have he : f x - g x = (f c - g c) * p + (f z - g z) := by
        rw [hx]; simp only [map_add (f := _), map_mul, map_natCast, map_intCast]; ring
      rw [he]
      refine add_mem ?_ (sub_mem (hmap f hφ _ _ hz) (hmap g hψ _ _ hz))
      rw [pow_succ]
      exact Ideal.mul_mem_mul (ih c) hpw
  have h5 : ∀ x : 𝓞 E, f x = g x := by
    intro x
    have hb := Ideal.iInf_pow_eq_bot_of_isDomain w.asIdeal w.isPrime.ne_top
    have : f x - g x ∈ (⊥ : Ideal (𝓞 K)) := by
      rw [← hb]; exact Ideal.mem_iInf.2 fun n => h4 n x
    exact sub_eq_zero.1 (Ideal.mem_bot.1 this)
  refine IsFractionRing.ringHom_ext (A := 𝓞 E) fun x => ?_
  exact congrArg (algebraMap (𝓞 K) K) (h5 x)

end GlobalTheory
end
