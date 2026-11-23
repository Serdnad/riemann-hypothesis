module

public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle012
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle001
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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

@[expose] public section

section

set_option autoImplicit false

namespace GlobalTheory.CMTypeOrConjugate

open NumberField

theorem conj_eq_neg_of_sq {z : ℂ} {d : ℕ} (hd : 0 < d) (hz : z ^ 2 = -(d : ℂ)) :
    starRingEnd ℂ z = -z := by
  have h1 : (starRingEnd ℂ z) ^ 2 = z ^ 2 := by
    rw [← map_pow, hz, map_neg, map_natCast]
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp h1 with h | h
  · exfalso
    obtain ⟨x, rfl⟩ := Complex.conj_eq_iff_real.mp h
    have h2 : x ^ 2 = -(d : ℝ) := by exact_mod_cast hz
    have h3 : (0 : ℝ) < d := by exact_mod_cast hd
    nlinarith [sq_nonneg x]
  · exact h

theorem inPsi_or_inPsi_conjugate {E : Type} [Field E] [NumberField E] [IsCMField E]
    (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (τ : E →+* ℂ) :
    Formalism.L2.Pj.InPsi H τ ∨ Formalism.L2.Pj.InPsi H (ComplexEmbedding.conjugate τ) := by
  have hE : (H.rt : E) ^ 2 = -(H.d : E) := by
    have h := congrArg (algebraMap (𝓞 E) E) H.rt_sq
    rw [map_pow, map_neg, map_natCast] at h
    exact h
  have hz : (τ (H.rt : E)) ^ 2 = -(H.d : ℂ) := by
    rw [← map_pow, hE, map_neg, map_natCast]
  unfold Formalism.L2.Pj.InPsi
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp (hz.trans H.sqrt_neg_disc_sq.symm) with h | h
  · exact Or.inl h
  · right
    rw [ComplexEmbedding.conjugate_coe_eq, conj_eq_neg_of_sq H.d_prime.pos hz, h, neg_neg]

end GlobalTheory.CMTypeOrConjugate
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem exists_pow_mul_coprime_le {R : Type} [CommRing R] [IsDedekindDomain R] (A K : Ideal R) (hK : K ≠ 0) :
    ∃ (j : ℕ) (J : Ideal R), A ^ j * J ≤ K ∧ A ⊔ J = ⊤ := by
  classical
  rw [Ne, Submodule.zero_eq_bot] at hK
  have hne : ({J : Ideal R | ∃ j : ℕ, A ^ j * J ≤ K}).Nonempty := ⟨K, 0, by simp⟩
  obtain ⟨J, ⟨j, hj⟩, hmax⟩ :=
    set_has_maximal_iff_noetherian.mpr (inferInstance : IsNoetherian R R) _ hne
  refine ⟨j, J, hj, ?_⟩

  have hKJ : K ≤ J := by
    by_contra h
    refine hmax (J ⊔ K) ⟨j, ?_⟩ (lt_of_le_of_ne le_sup_left ?_)
    · rw [Ideal.mul_sup]
      exact sup_le hj (Ideal.mul_le_inf.trans inf_le_right)
    · intro e
      exact h (le_sup_right.trans e.symm.le)
  have hJ0 : J ≠ 0 := by
    rw [Ne, Submodule.zero_eq_bot]
    rintro rfl
    exact hK (le_bot_iff.mp hKJ)

  by_contra hne'
  obtain ⟨P, hP, hle⟩ := Ideal.exists_le_maximal _ hne'
  have hJP : J ≤ P := le_trans le_sup_right hle
  have hAP : A ≤ P := le_trans le_sup_left hle
  obtain ⟨Q, hQ⟩ := Ideal.dvd_iff_le.mpr hJP
  have hQmem : A ^ (j + 1) * Q ≤ K :=
    calc A ^ (j + 1) * Q = A ^ j * (A * Q) := by rw [pow_succ, _root_.mul_assoc]
      _ ≤ A ^ j * (P * Q) := Ideal.mul_mono_right (Ideal.mul_mono_left hAP)
      _ = A ^ j * J := by rw [hQ]
      _ ≤ K := hj
  have hJQ : J ≤ Q := by
    rw [hQ]
    exact (Ideal.mul_le_inf.trans inf_le_right)
  have hQJ : Q = J := by
    by_contra h
    exact hmax Q ⟨j + 1, hQmem⟩ (lt_of_le_of_ne hJQ (Ne.symm h))
  rw [hQJ] at hQ

  exact hP.ne_top (mul_right_cancel₀ hJ0 (hQ.symm.trans (Ideal.top_mul J).symm))

private theorem comp_act_eq_one_of_pow_eq_killed {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    {l : Level H} (Xo : Moduli Dw l) {T : Over Xo.X} (t w : T ⟶ Xo.univ.t.G) (N : ℕ)
    (ht : KilledBy Xo l.Mb t) (hw : w ^ N = t) :
    ∀ x ∈ Ideal.span {(N : 𝓞 E)} * l.Mb, w ≫ Xo.univ.t.act.act x = 1 := by
  unfold KilledBy at ht
  have h0 : Xo.univ.t.act.act 0 = 1 := by
    have h := Xo.univ.t.act.add 0 0
    rw [add_zero] at h
    have h' := congrArg (fun f => f * (Xo.univ.t.act.act 0)⁻¹) h
    simpa using h'.symm

  have hnat : ∀ (n : ℕ) (y : 𝓞 E), Xo.univ.t.act.act ((n : 𝓞 E) * y) = Xo.univ.t.act.act y ^ n := by
    intro n y
    induction n with
    | zero => simp [h0]
    | succ n ih => rw [Nat.cast_succ, add_mul, _root_.one_mul, Xo.univ.t.act.add, ih, pow_succ]
  intro x hx
  refine Submodule.mul_induction_on hx ?_ ?_
  · intro m hm b hb
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hm
    have := Xo.univ.t.act.hom b
    have := Xo.univ.t.act.hom c
    have e : c * (N : 𝓞 E) * b = (N : 𝓞 E) * b * c := by ring
    rw [e, Xo.univ.t.act.mul, hnat, ← Category.assoc, MonObj.comp_pow, ← MonObj.pow_comp, hw, ht b hb,
      MonObj.one_comp]
  · intro y z hy hz
    rw [Xo.univ.t.act.add, MonObj.comp_mul, hy, hz, _root_.one_mul]

theorem exists_root_killedBy {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    {l : Level H} (Xo : Moduli Dw l) {T : Over Xo.X} (t w : T ⟶ Xo.univ.t.G) (N : ℕ)
    (ht : KilledBy Xo l.Mb t) (hw : w ^ N = t) (I J : Ideal (𝓞 E)) (hI : I ≤ l.Mb) (hIJ : I ⊔ J = ⊤)
    (hle : I * J ≤ Ideal.span {(N : 𝓞 E)} * l.Mb) :
    ∃ t' : T ⟶ Xo.univ.t.G, t' ^ N = t ∧ KilledBy Xo I t' := by
  obtain ⟨i, hi, j, hj, hij⟩ := Submodule.mem_sup.mp (hIJ ▸ Submodule.mem_top : (1 : 𝓞 E) ∈ I ⊔ J)
  have ht' := ht
  unfold KilledBy at ht'
  refine ⟨w ≫ Xo.univ.t.act.act j, ?_, ?_⟩
  · have := Xo.univ.t.act.hom j
    rw [← MonObj.pow_comp, hw]
    have h1 : t ≫ Xo.univ.t.act.act i = 1 := ht' i (hI hi)
    calc t ≫ Xo.univ.t.act.act j = (t ≫ Xo.univ.t.act.act i) * (t ≫ Xo.univ.t.act.act j) := by
          rw [h1, _root_.one_mul]
      _ = t ≫ Xo.univ.t.act.act (i + j) := by rw [Xo.univ.t.act.add, MonObj.comp_mul]
      _ = t := by rw [hij, Xo.univ.t.act.one, Category.comp_id]
  · unfold KilledBy
    intro a ha
    rw [Category.assoc, ← Xo.univ.t.act.mul]
    exact comp_act_eq_one_of_pow_eq_killed Xo t w N ht hw _ (hle (_root_.mul_comm a j ▸ Ideal.mul_mem_mul ha hj))

theorem exists_root_killedBy_pow :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (T : Over Xo.X) (t w : T ⟶ Xo.univ.t.G) (N : ℕ), 0 < N → KilledBy Xo l.Mb t → w ^ N = t → (∃ t' : T ⟶ Xo.univ.t.G, t' ^ N = t ∧ ∃ j : ℕ, KilledBy Xo (l.Mb ^ j) t') ∧ (N = l.M → ∃ t' : T ⟶ Xo.univ.t.G, t' ^ N = t ∧ KilledBy Xo (l.Mb ^ 2) t') := by
  intro E _ _ _ H Dw l Xo T t w N hN ht hw
  have hMb0 : l.Mb ≠ 0 := by
    intro h
    have hp := l.prod
    rw [h, zero_mul, Submodule.zero_eq_bot, eq_comm, Ideal.span_singleton_eq_bot] at hp
    have hM : l.M = 0 := by exact_mod_cast hp
    have := l.three_le
    omega
  have hN0 : Ideal.span {(N : 𝓞 E)} ≠ 0 := by
    rw [Ne, Submodule.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast hN.ne'
  obtain ⟨j, J, hj, hcop⟩ := exists_pow_mul_coprime_le l.Mb _ (mul_ne_zero hN0 hMb0)
  refine ⟨?_, ?_⟩
  · obtain ⟨t', ht'N, ht'⟩ := exists_root_killedBy Xo t w N ht hw (l.Mb ^ (j + 1)) J
      (Ideal.pow_le_self (Nat.succ_ne_zero j)) (Ideal.pow_sup_eq_top hcop)
      (by rw [pow_succ', _root_.mul_assoc]; exact (Ideal.mul_le_inf.trans inf_le_right).trans hj)
    exact ⟨t', ht'N, j + 1, ht'⟩
  · intro hNM
    refine exists_root_killedBy Xo t w N ht hw (l.Mb ^ 2) (l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E))
      (Ideal.pow_le_self two_ne_zero) (Ideal.pow_sup_eq_top l.coprime) (le_of_eq ?_)
    rw [sq, _root_.mul_assoc, l.prod, _root_.mul_comm, hNM]

end GlobalTheory
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FramedBaseChange

theorem spec_comp {S T U : Type} [CommRing S] [CommRing T] [CommRing U] (φ : S →+* T) (ψ : T →+* U) :
    spMap (ψ.comp φ) = spMap ψ ≫ spMap φ := by
  simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]

theorem dual_comp {S T U : Type} [CommRing S] [CommRing T] [CommRing U] (φ : S →+* T) (ψ : T →+* U) :
    dualMap (ψ.comp φ) = (dualMap ψ).comp (dualMap φ) :=
  RingHom.ext fun x => by ext <;> simp [dualMap]

theorem spec_algHom_id (K : Type) [Field K] (T : Type) [CommRing T] [Algebra K T] :
    spMap (AlgHom.id K T).toRingHom = 𝟙 _ := by
  simp [spMap]

theorem dual_id (T : Type) [CommRing T] : dualMap (RingHom.id T) = RingHom.id _ :=
  RingHom.ext fun x => by
    show TrivSqZeroExt.inl x.fst + TrivSqZeroExt.inr x.snd = x
    exact TrivSqZeroExt.inl_fst_add_inr_snd_eq x

theorem appLE_eq_of_eq {X Y : Scheme.{0}} {f g : X ⟶ Y} (e : f = g) (U : Y.Opens) (V : X.Opens)
    (hf : V ≤ f ⁻¹ᵁ U) (hg : V ≤ g ⁻¹ᵁ U) : f.appLE U V hf = g.appLE U V hg := by
  subst e
  rfl

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem chart_le {S T : Type} [CommRing S] [CommRing T] {x : Sp S ⟶ Xo.X} {x' : Sp T ⟶ Xo.X}
    (pm : Gx x' ⟶ Gx x)
    (hs : pm ≫ (snd (Over.mk x) Xo.univ.t.G).left = (snd (Over.mk x') Xo.univ.t.G).left)
    (i : Fin 1 → Xo.univ.t.PP.L.ι) : (PPx x').U i ≤ pm ⁻¹ᵁ (PPx x).U i := by
  intro p hp
  have hp' : ∀ k, p ∈ (snd (Over.mk x') Xo.univ.t.G).left.base ⁻¹' (Xo.univ.t.PP.L.U (i k) : Set _) :=
    Set.mem_iInter.1 hp
  have e := congrArg (fun f : Gx x' ⟶ Xo.univ.t.G.left => f.base p) hs
  show pm.base p ∈ ⋂ k, (snd (Over.mk x) Xo.univ.t.G).left.base ⁻¹' (Xo.univ.t.PP.L.U (i k) : Set _)
  refine Set.mem_iInter.2 fun k => ?_
  show (pm ≫ (snd (Over.mk x) Xo.univ.t.G).left).base p ∈ (Xo.univ.t.PP.L.U (i k) : Set _)
  rw [e]
  exact hp' k

theorem pulledGroup_hom_ext {S : Type} [CommRing S] {x : Sp S ⟶ Xo.X} {W : Scheme.{0}} (a b : W ⟶ Gx x)
    (hs : a ≫ (snd (Over.mk x) Xo.univ.t.G).left = b ≫ (snd (Over.mk x) Xo.univ.t.G).left)
    (hf : a ≫ (fst (Over.mk x) Xo.univ.t.G).left = b ≫ (fst (Over.mk x) Xo.univ.t.G).left) : a = b := by
  have hw : a ≫ (Over.mk x ⊗ Xo.univ.t.G).hom = b ≫ (Over.mk x ⊗ Xo.univ.t.G).hom := by
    have e1 := Over.w (snd (Over.mk x) Xo.univ.t.G)
    rw [← e1, ← Category.assoc, hs, Category.assoc]
  let a' : Over.mk (a ≫ (Over.mk x ⊗ Xo.univ.t.G).hom) ⟶ Over.mk x ⊗ Xo.univ.t.G := Over.homMk a rfl
  let b' : Over.mk (a ≫ (Over.mk x ⊗ Xo.univ.t.G).hom) ⟶ Over.mk x ⊗ Xo.univ.t.G := Over.homMk b hw.symm
  have e : a' = b' := by
    apply CartesianMonoidalCategory.hom_ext
    · exact Over.OverMorphism.ext hf
    · exact Over.OverMorphism.ext hs
  exact congrArg CommaMorphism.left e

theorem refl {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) :
    FrMap (AlgHom.id c.F S) y y := by
  have eid := spec_algHom_id c.F S
  have did : spMap (dualMap (AlgHom.id c.F S).toRingHom) = 𝟙 _ := by
    show spMap (dualMap (RingHom.id S)) = _
    rw [dual_id]
    simp [spMap]
  refine ⟨by rw [eid, Category.id_comp], fun τ i => by rw [did, Category.id_comp], 𝟙 _,
    Category.id_comp _, by rw [eid]; exact (Category.id_comp _).trans (Category.comp_id _).symm, ?_⟩
  intro i h
  have e : Scheme.Hom.appLE (𝟙 (Gx y.x)) ((PPx y.x).U i) ((PPx y.x).U i) h = 𝟙 _ := by
    rw [Scheme.Hom.appLE, Scheme.Hom.id_app]
    refine (Category.id_comp _).trans ?_
    rw [← (Gx y.x).presheaf.map_id]
    rfl
  rw [e, CommRingCat.hom_id, RingHom.id_apply]

theorem trans {S T U : Type} [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T] [CommRing U]
    [Algebra c.F U] (φ : S →ₐ[c.F] T) (ψ : T →ₐ[c.F] U) {y : FrPt Xo c S} {z : FrPt Xo c T} {w : FrPt Xo c U}
    (h₁ : FrMap φ y z) (h₂ : FrMap ψ z w) : FrMap (ψ.comp φ) y w := by
  obtain ⟨hx1, hu1, pm1, hs1, hf1, ha1⟩ := h₁
  obtain ⟨hx2, hu2, pm2, hs2, hf2, ha2⟩ := h₂
  have esp : spMap (ψ.comp φ).toRingHom = spMap ψ.toRingHom ≫ spMap φ.toRingHom := by
    exact spec_comp φ.toRingHom ψ.toRingHom
  have edsp : spMap (dualMap (ψ.comp φ).toRingHom) =
      spMap (dualMap ψ.toRingHom) ≫ spMap (dualMap φ.toRingHom) := by
    show spMap (dualMap (ψ.toRingHom.comp φ.toRingHom)) = _
    rw [dual_comp, spec_comp]
  refine ⟨?_, ?_, pm2 ≫ pm1, ?_, ?_, ?_⟩
  · rw [hx2, hx1, esp, Category.assoc]
  · intro τ i
    rw [hu2 τ i, hu1 τ i, edsp, Category.assoc]
  · rw [Category.assoc, hs1, hs2]
  · rw [Category.assoc, hf1, ← Category.assoc, hf2, esp, Category.assoc]
  · intro i h
    have h1' := chart_le pm1 hs1 i
    have h2' := chart_le pm2 hs2 i
    have e : (pm2 ≫ pm1).appLE _ _ h = pm1.appLE _ _ h1' ≫ pm2.appLE _ _ h2' :=
      (Scheme.Hom.appLE_comp_appLE pm2 pm1 _ _ _ h1' h2').symm
    rw [e, CommRingCat.hom_comp, RingHom.comp_apply, ha1 i h1', ha2 i h2']

theorem cancel {S T U : Type} [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T] [CommRing U]
    [Algebra c.F U] (φ : S →ₐ[c.F] T) (κ : T →ₐ[c.F] U) {y0 : FrPt Xo c S} {y : FrPt Xo c T} {z : FrPt Xo c U}
    (h₁ : FrMap φ y0 y) (h₂ : FrMap (κ.comp φ) y0 z) : FrMap κ y z := by
  obtain ⟨hx1, hu1, pm1, hs1, hf1, ha1⟩ := h₁
  obtain ⟨hx2, hu2, pm2, hs2, hf2, ha2⟩ := h₂
  have esp : spMap (κ.comp φ).toRingHom = spMap κ.toRingHom ≫ spMap φ.toRingHom :=
    spec_comp φ.toRingHom κ.toRingHom
  have edsp : spMap (dualMap (κ.comp φ).toRingHom) =
      spMap (dualMap κ.toRingHom) ≫ spMap (dualMap φ.toRingHom) := by
    show spMap (dualMap (κ.toRingHom.comp φ.toRingHom)) = _
    rw [dual_comp, spec_comp]
  have hx : spMap κ.toRingHom ≫ y.x = z.x := by rw [hx2, hx1, esp, Category.assoc]
  let pm : Gx z.x ⟶ Gx y.x :=
    ((Over.homMk (spMap κ.toRingHom) hx : Over.mk z.x ⟶ Over.mk y.x) ▷ Xo.univ.t.G).left
  have hs : pm ≫ (snd (Over.mk y.x) Xo.univ.t.G).left = (snd (Over.mk z.x) Xo.univ.t.G).left := by
    rw [← Over.comp_left, whiskerRight_snd]
  have hf : pm ≫ (fst (Over.mk y.x) Xo.univ.t.G).left =
      (fst (Over.mk z.x) Xo.univ.t.G).left ≫ spMap κ.toRingHom := by
    rw [← Over.comp_left, whiskerRight_fst]
    rfl
  have hcomp : pm ≫ pm1 = pm2 := by
    apply pulledGroup_hom_ext
    · rw [Category.assoc, hs1, hs, hs2]
    · rw [Category.assoc, hf1, ← Category.assoc, hf, Category.assoc, ← esp, hf2]
  refine ⟨?_, ?_, pm, hs, hf, ?_⟩
  · rw [hx2, hx1, esp, Category.assoc]
  · intro τ i
    rw [hu2 τ i, hu1 τ i, edsp, Category.assoc]
  · intro i h
    have h1' := chart_le pm1 hs1 i
    have h2' := chart_le pm2 hs2 i
    rw [← ha1 i h1', ← ha2 i h2']
    have e : pm1.appLE _ _ h1' ≫ pm.appLE _ _ h = pm2.appLE ((PPx y0.x).U i) ((PPx z.x).U i) h2' := by
      rw [Scheme.Hom.appLE_comp_appLE]
      exact appLE_eq_of_eq hcomp _ _ _ _
    rw [← e, CommRingCat.hom_comp, RingHom.comp_apply]

theorem unique {S T : Type} [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T]
    (φ : S →ₐ[c.F] T) {y : FrPt Xo c S} {z z' : FrPt Xo c T} (h₁ : FrMap φ y z) (h₂ : FrMap φ y z') :
    z = z' := by
  obtain ⟨x1, o1, u1, tan1, eig1, basis1, s1, gen1⟩ := z
  obtain ⟨x2, o2, u2, tan2, eig2, basis2, s2, gen2⟩ := z'
  obtain ⟨hx1, hu1, pm1, hs1, hf1, ha1⟩ := h₁
  obtain ⟨hx2, hu2, pm2, hs2, hf2, ha2⟩ := h₂
  dsimp only at hx1 hu1 pm1 hs1 hf1 ha1 hx2 hu2 pm2 hs2 hf2 ha2
  have hx : x1 = x2 := hx1.trans hx2.symm
  subst hx
  have hu : u1 = u2 := funext fun τ => funext fun i => (hu1 τ i).trans (hu2 τ i).symm
  subst hu
  have hpm : pm1 = pm2 := pulledGroup_hom_ext _ _ (hs1.trans hs2.symm) (hf1.trans hf2.symm)
  subst hpm
  have hsf : s1.f = s2.f := funext fun i =>
    (ha1 i (chart_le pm1 hs1 i)).symm.trans (ha2 i (chart_le pm1 hs1 i))
  obtain ⟨f1, c1⟩ := s1
  obtain ⟨f2, c2⟩ := s2
  dsimp only at hsf
  subst hsf
  rfl

theorem isPullSec {S T : Type} [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T]
    (φ : S →ₐ[c.F] T) {y : FrPt Xo c S} {z : FrPt Xo c T} (hm : FrMap φ y z)
    (h : ptO Xo z.x ⟶ ptO Xo y.x) (hh : h.left = spMap φ.toRingHom) :
    IsPullSec Xo.univ.t.G Xo.univ.t.PP.L 1 (h ▷ Xo.univ.t.G) (whiskerRight_snd _ _) y.s z.s := by
  obtain ⟨hx, hu, pm, hs, hf, ha⟩ := hm
  have hpm : pm = (h ▷ Xo.univ.t.G).left := by
    apply pulledGroup_hom_ext
    · rw [hs, ← Over.comp_left, whiskerRight_snd]
    · rw [hf, ← Over.comp_left, whiskerRight_fst, Over.comp_left, hh]
  subst hpm
  intro j
  exact (ha j (chart_le _ hs j)).symm

end GlobalTheory.FramedBaseChange

namespace GlobalTheory

theorem framedPoint_baseChange_laws : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), (∀ (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S), FrMap (AlgHom.id c.F S) y y) ∧ (∀ (S T U : Type) [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T] [CommRing U] [Algebra c.F U] (φ : S →ₐ[c.F] T) (ψ : T →ₐ[c.F] U) (y : FrPt Xo c S) (z : FrPt Xo c T) (w : FrPt Xo c U), FrMap φ y z → (FrMap ψ z w ↔ FrMap (ψ.comp φ) y w)) ∧ (∀ (S T : Type) [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T] (φ : S →ₐ[c.F] T) (y : FrPt Xo c S) (z z' : FrPt Xo c T), FrMap φ y z → FrMap φ y z' → z = z') ∧ ∀ (S T : Type) [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T] (φ : S →ₐ[c.F] T) (y : FrPt Xo c S) (z : FrPt Xo c T), FrMap φ y z → ∀ h : ptO Xo z.x ⟶ ptO Xo y.x, h.left = spMap φ.toRingHom → IsPullSec Xo.univ.t.G Xo.univ.t.PP.L 1 (h ▷ Xo.univ.t.G) (whiskerRight_snd _ _) y.s z.s :=
  fun _ _ _ _ _ _ _ _ _ =>
    ⟨fun _ _ _ y => FramedBaseChange.refl y,
     fun _ _ _ _ _ _ _ _ _ φ ψ _ _ _ h₁ =>
       ⟨fun h₂ => FramedBaseChange.trans φ ψ h₁ h₂, fun h₂ => FramedBaseChange.cancel φ ψ h₁ h₂⟩,
     fun _ _ _ _ _ _ φ _ _ _ h₁ h₂ => FramedBaseChange.unique φ h₁ h₂,
     fun _ _ _ _ _ _ φ _ _ hm h hh => FramedBaseChange.isPullSec φ hm h hh⟩

end GlobalTheory
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem exists_natCast_smul_coeff_isIntegral {σ K : Type} [Field K] [CharZero K] [FiniteDimensional ℚ K]
    (P : MvPolynomial σ K) :
    ∃ N : ℕ, 0 < N ∧ ∀ m, IsIntegral ℤ (((N : K) • P).coeff m) := by
  first
  | exact @_root_.GlobalTheory.NatMultipleIntegralCoefficients.exists_nat_smul_coeff_isIntegral
  | exact _root_.GlobalTheory.NatMultipleIntegralCoefficients.exists_nat_smul_coeff_isIntegral
  | (apply _root_.GlobalTheory.NatMultipleIntegralCoefficients.exists_nat_smul_coeff_isIntegral <;> assumption)
  | (intros; apply _root_.GlobalTheory.NatMultipleIntegralCoefficients.exists_nat_smul_coeff_isIntegral <;> assumption)
  | (intros; apply @_root_.GlobalTheory.NatMultipleIntegralCoefficients.exists_nat_smul_coeff_isIntegral <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.NatMultipleIntegralCoefficients.exists_nat_smul_coeff_isIntegral ..)

theorem smul_mem_HHa {T : Type} {r : T → ℕ} {n : ℕ} {k : Type} [Field k] {cc : T → T} {isX : T → Prop}
    {a : T → ℕ → ℕ} {P : MvPolynomial (Letter T r n) k} (t : k) (hP : P ∈ HHa r n k cc isX a) :
    t • P ∈ HHa r n k cc isX a :=
  ⟨Submodule.smul_mem _ t hP.1,
    fun σ i i' h s => by rw [map_smul, hP.2.1 σ i i' h s],
    fun m hm => hP.2.2 m (MvPolynomial.support_smul hm)⟩

theorem exists_natCast_smul_mem_harmA :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (c : Coeff l) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (P : MvPolynomial (LtN Dw n) c.F), P ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)) → ∃ N : ℕ, 0 < N ∧ (N : c.F) • P ∈ harmA c a n ∧ ((N : c.F) • P).support = P.support := by
  intro E _ _ _ H Dw l c a n P hP
  haveI := c.fin
  obtain ⟨N, hN, h⟩ := exists_natCast_smul_coeff_isIntegral (K := c.F) P
  refine ⟨N, hN, ⟨smul_mem_HHa _ hP, fun m => h m⟩, ?_⟩
  have hN' : (N : c.F) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  ext m
  simp [MvPolynomial.mem_support_iff, MvPolynomial.coeff_smul, hN']

end GlobalTheory
end
