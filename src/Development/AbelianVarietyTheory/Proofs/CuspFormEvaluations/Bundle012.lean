module

import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle028
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle008
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DualRestrictSurjectiveOfIsTorsionFreeQuotient
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle001
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle013
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.Bundle006
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
public import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.MajPos
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle009
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.LemmaNA
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.Bundle012

@[expose] public section

section

namespace GlobalTheory.ConjugateEmbeddingSquareRoot

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem conj_eq_neg_of_sq {z : ℂ} {r : ℝ} (hr : 0 < r) (h : z ^ 2 = -(r : ℂ)) :
    (starRingEnd ℂ) z = -z := by
  apply GlobalTheory.CompanionTheory.Ar.Fl.RelDiff.conj_eq_neg_of_sq <;> assumption

theorem conjEmb_rt {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) (τ : E →+* ℂ) :
    conjEmb τ (H.rt : E) = -τ (H.rt : E) := by
  have hd : (0 : ℝ) < (H.d : ℝ) := by exact_mod_cast H.d_prime.pos
  have h1 : ((H.rt : E)) ^ 2 = -(H.d : E) := by
    have := congrArg (algebraMap (𝓞 E) E) H.rt_sq
    simpa using this
  have h2 : (τ (H.rt : E)) ^ 2 = -(((H.d : ℝ)) : ℂ) := by
    rw [← map_pow, h1]
    simp
  exact conj_eq_neg_of_sq hd h2

end GlobalTheory.ConjugateEmbeddingSquareRoot
end

section

open Module Function

namespace GlobalTheory


open Module Function in
theorem _root_.GlobalTheory.exists_symplectic_coordinates_adapted {Λ : Type*} [AddCommGroup Λ] [Module.Free ℤ Λ]
    [Module.Finite ℤ Λ] {ω : LinearMap.BilinForm ℤ Λ} (hω : ω.IsAlt) (hp : Bijective ω)
    {I : Submodule ℤ Λ} (hsat : ∀ (k : ℤ) (x : Λ), k ≠ 0 → k • x ∈ I → x ∈ I)
    (hiso : ∀ x ∈ I, ∀ y ∈ I, ω x y = 0) {ε : ℤ} (hε : ε = 1 ∨ ε = -1) :
    ∃ (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] Λ) (S : Finset (Fin g)),
      (∀ a b, ω (bas a) (bas b) = ε * _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.omegaStd a b) ∧
      I = Submodule.span ℤ ((fun k => bas (Pi.single (Sum.inl k) 1)) '' (S : Set (Fin g))) ∧
      2 * g = finrank ℤ Λ := by
  obtain ⟨r, v⟩ := Submodule.basisOfPid (Module.Free.chooseBasis ℤ Λ) I
  have htf : Module.IsTorsionFree ℤ (Λ ⧸ I) := (_root_.GlobalTheory.isTorsionFree_quotient_iff I).mpr hsat
  have hle : I ≤ ω.orthogonal I := fun x hx =>
    (LinearMap.BilinForm.mem_orthogonal_iff).mpr fun y hy => hiso y hy x hx
  obtain ⟨g, b, hb, hbv⟩ := _root_.GlobalTheory.exists_isSymplecticBasis_extend hω hp htf hle v
  set e : Fin r ⊕ Fin g ≃ Fin (r + g) := finSumFinEquiv
  set b' := b.reindex (e.sumCongr e) with hb'
  have hsymp : _root_.GlobalTheory.IsSymplecticBasis ω b' := hb.reindex e
  have hb'v : ∀ i, b' (Sum.inl (e (Sum.inl i))) = (v i : Λ) := by
    intro i
    rw [hb', Module.Basis.reindex_apply]
    simp [hbv]
  obtain ⟨u, hu⟩ : IsUnit ε := Int.isUnit_iff.mpr hε
  let D : (Fin (r + g) ⊕ Fin (r + g) → ℤ) ≃ₗ[ℤ] (Fin (r + g) ⊕ Fin (r + g) → ℤ) :=
    LinearEquiv.piCongrRight fun i => LinearEquiv.smulOfUnit (Sum.elim (fun _ => 1) (fun _ => u) i)
  have hD : ∀ a i, D a i = Sum.elim (fun _ => (1 : ℤ)) (fun _ => ε) i * a i := by
    intro a i
    rcases i with i | i <;> change (_ : ℤˣ) • a _ = _ <;> simp [Units.smul_def, hu]
  refine ⟨r + g, D.trans b'.equivFun.symm, Finset.univ.image fun i => e (Sum.inl i), ?_, ?_, ?_⟩
  · intro a c
    rw [hsymp.apply_eq_sum hω]
    unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.omegaStd
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [LinearEquiv.trans_apply, ← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply, hD,
      Sum.elim_inl, Sum.elim_inr]
    ring
  · have hspan : Submodule.span ℤ (Set.range fun i => (v i : Λ)) = I := by
      have h := congrArg (Submodule.map I.subtype) v.span_eq
      rw [Submodule.map_span, Submodule.map_subtype_top, ← Set.range_comp] at h
      exact h
    have hsingle : ∀ k, D (Pi.single (Sum.inl k) 1) = Pi.single (Sum.inl k) 1 := by
      intro k
      funext i
      rw [hD]
      rcases i with i | i <;> simp [Pi.single_apply]
    rw [← hspan]
    congr 1
    ext x
    simp only [Set.mem_image, Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_range,
      LinearEquiv.trans_apply, hsingle, _root_.Basis.equivFun_symm_single]
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨e (Sum.inl i), ⟨i, rfl⟩, hb'v i⟩
    · rintro ⟨k, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, (hb'v i).symm⟩
  · rw [Module.finrank_eq_card_basis b']
    simp
    ring

end GlobalTheory
end

section

open NumberField ReciprocityTheory.ChartRestriction.G.FD Topology

namespace GlobalTheory

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

namespace CuspNet

theorem exists_finset_rmul_near_one {r : ℕ} (X : Data E r) {K : Set (Frame X.Ψ r)}
    (hK : IsCompact K) (hKd : K ⊆ X.dom) {δ : ℝ} (hδ : 0 < δ) :
    ∃ N : Finset (Frame X.Ψ r), (∀ y ∈ N, y ∈ K) ∧ ∀ x ∈ K, ∃ A : Frame X.Ψ r,
      (∀ τ a b, ‖A τ a b - (if a = b then 1 else 0)‖ ≤ δ) ∧ rmul x A ∈ N := by
  obtain ⟨N, hN, hcov⟩ := hK.elim_nhdsWithin_subcover
    (fun y => {x | ∀ τ a b, ‖((mat x τ)⁻¹ * mat y τ) a b - (if a = b then 1 else 0)‖ ≤ δ})
    (fun y hy => by
      simp only [Set.ofPred_forall]
      refine Filter.iInter_mem.2 fun τ => Filter.iInter_mem.2 fun a =>
        Filter.iInter_mem.2 fun b => ?_
      have hc : ContinuousOn (fun x : Frame X.Ψ r =>
          ‖((mat x τ)⁻¹ * mat y τ) a b - (if a = b then 1 else 0)‖) K := by
        refine (ContinuousOn.sub ?_ continuousOn_const).norm
        simp only [Matrix.mul_apply]
        refine continuousOn_finsetSum _ fun k _ => ContinuousOn.mul ?_ continuousOn_const
        exact GramSchmidtCont.continuousOn_inv_apply (GramSchmidtCont.continuous_mat X τ)
          (fun x hx => (hKd hx τ).1) a k
      have h0 : ‖((mat y τ)⁻¹ * mat y τ) a b - (if a = b then 1 else 0)‖ < δ := by
        rw [Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 (hKd hy τ).1), Matrix.one_apply,
          sub_self, norm_zero]
        exact hδ
      exact (hc y hy).eventually (eventually_le_nhds h0))
  refine ⟨N, hN, fun x hx => ?_⟩
  obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.1 (hcov hx)
  refine ⟨fun τ => ((mat x τ)⁻¹ * mat y τ : Matrix (Fin r) (Fin r) ℂ), hxy, ?_⟩
  convert hy using 1
  funext τ
  show mat x τ * ((mat x τ)⁻¹ * mat y τ) = mat y τ
  rw [Matrix.mul_nonsing_inv_cancel_left _ _ (isUnit_iff_ne_zero.2 (hKd hx τ).1)]

end CuspNet

namespace CuspNet

end CuspNet

end GlobalTheory
end

section

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.I2

namespace GlobalTheory.LevelTupleSum

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

def Gen (Λ : Submodule (𝓞 E) (Fin r → E)) (t : Fin r → Fin r → E) : Prop :=
  (∀ j, (25 : E) • t j ∈ Λ) ∧
    ∀ u ∈ Λ, ∃ c : Fin r → 𝓞 E, ∃ y ∈ Λ, u = ∑ j, (c j : E) • ((25 : E) • t j) + (5 : E) • y

omit [IsCMField E] in
theorem coe_smul_mem (Λ : Submodule (𝓞 E) (Fin r → E)) (c : 𝓞 E) {v : Fin r → E} (hv : v ∈ Λ) :
    (c : E) • v ∈ Λ := Λ.smul_mem c hv

omit [IsCMField E] in
theorem nat_smul_mem (Λ : Submodule (𝓞 E) (Fin r → E)) (n : ℕ) {v : Fin r → E} (hv : v ∈ Λ) :
    (n : E) • v ∈ Λ := by
  rw [Nat.cast_smul_eq_nsmul]
  exact nsmul_mem hv n

omit [IsCMField E] in
theorem Gen.of_sub {Λ : Submodule (𝓞 E) (Fin r → E)} {t t' : Fin r → Fin r → E} (h : Gen Λ t)
    (hs : ∀ j, t j - t' j ∈ Λ) : Gen Λ t' := by
  refine ⟨fun j => ?_, fun u hu => ?_⟩
  · have h1 : (25 : E) • (t j - t' j) ∈ Λ := by simpa using nat_smul_mem Λ 25 (hs j)
    have : (25 : E) • t' j = (25 : E) • t j - (25 : E) • (t j - t' j) := by module
    rw [this]
    exact Λ.sub_mem (h.1 j) h1
  · obtain ⟨c, y, hy, rfl⟩ := h.2 u hu
    refine ⟨c, y + ∑ j, (c j : E) • ((5 : E) • (t j - t' j)), Λ.add_mem hy (Λ.sum_mem fun j _ =>
      coe_smul_mem Λ _ (by simpa using nat_smul_mem Λ 5 (hs j))), ?_⟩
    rw [smul_add, Finset.smul_sum, add_comm ((5 : E) • y), ← add_assoc, ← Finset.sum_add_distrib]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    module

omit [IsCMField E] in
theorem exists_finite_res (Λ : Submodule (𝓞 E) (Fin r → E)) (hΛ : Λ.FG) :
    ∃ S : Set (Fin r → E), S.Finite ∧ ∀ v, (25 : E) • v ∈ Λ → ∃ s ∈ S, v - s ∈ Λ := by
  have : Module.Finite (𝓞 E) Λ := Module.Finite.iff_fg.2 hΛ
  have : Module.Finite ℤ Λ := Module.Finite.trans (𝓞 E) Λ
  have : AddGroup.FG Λ := Module.Finite.iff_addGroup_fg.1 inferInstance
  have := AddSubgroup.finiteIndex_range_nsmulAddMonoidHom_of_fg Λ (n := 25) (by norm_num)
  refine ⟨Set.range fun q : Λ ⧸ (nsmulAddMonoidHom (α := Λ) 25).range =>
    (25 : E)⁻¹ • ((q.out : Λ) : Fin r → E), Set.finite_range _, fun v hv => ?_⟩
  obtain ⟨⟨z, y, hy⟩, hz⟩ := QuotientAddGroup.mk_out_eq_mul (nsmulAddMonoidHom (α := Λ) 25).range ⟨_, hv⟩
  refine ⟨_, ⟨QuotientAddGroup.mk ⟨_, hv⟩, rfl⟩, ?_⟩
  simp only [hz]
  subst hy
  have : v - (25 : E)⁻¹ • ((25 : E) • v + (25 : ℕ) • (y : Fin r → E)) = -(y : Fin r → E) := by
    rw [← Nat.cast_smul_eq_nsmul E, Nat.cast_ofNat, ← smul_add, inv_smul_smul₀ (by norm_num)]
    abel
  simp only [nsmulAddMonoidHom_apply, Submodule.coe_add, AddSubmonoidClass.coe_nsmul]
  rw [this]
  exact Λ.neg_mem y.2

omit [IsCMField E] in
theorem exists_reps (Λ : Submodule (𝓞 E) (Fin r → E)) (hΛ : Λ.FG) :
    ∃ 𝒯 : Finset (Fin r → Fin r → E), (∀ t ∈ 𝒯, Gen Λ t) ∧
      ∀ t, Gen Λ t → ∃! t', t' ∈ 𝒯 ∧ ∀ j, t j - t' j ∈ Λ := by
  obtain ⟨S, hS, hres⟩ := exists_finite_res Λ hΛ
  let ρ : (Fin r → E) → (Fin r → E) := fun v => (Submodule.Quotient.mk (p := Λ) v).out
  have hρ : ∀ v, v - ρ v ∈ Λ := fun v => (Submodule.Quotient.eq Λ).1 (Submodule.Quotient.mk_out _).symm
  have hρe : ∀ v w, v - w ∈ Λ → ρ v = ρ w := fun v w h => by
    simp only [ρ, (Submodule.Quotient.eq Λ).2 h]
  have hfin : {t : Fin r → Fin r → E | Gen Λ t ∧ ∀ j, ρ (t j) = t j}.Finite := by
    refine (Set.Finite.pi' fun _ : Fin r => hS.image ρ).subset ?_
    rintro t ⟨hg, ht⟩ j
    obtain ⟨s, hs, h⟩ := hres _ (hg.1 j)
    exact ⟨s, hs, by rw [← hρe _ _ h, ht]⟩
  refine ⟨hfin.toFinset, fun t ht => (hfin.mem_toFinset.1 ht).1, fun t ht => ⟨fun j => ρ (t j),
    ⟨hfin.mem_toFinset.2 ⟨ht.of_sub fun j => hρ _, fun j => (hρe _ _ (hρ _)).symm⟩, fun j => hρ _⟩, ?_⟩⟩
  rintro t' ⟨h1, h2⟩
  funext j
  rw [hρe _ _ (h2 j), (hfin.mem_toFinset.1 h1).2 j]

theorem torus_r {X : Data E r} {x : Frame X.Ψ r} (A : TorusAt X x) : A.T.r = r := by
  obtain ⟨τ⟩ : Nonempty X.Ψ := Fintype.card_pos_iff.1 (QuadraticCoefficientForms.card_Psi_pos (X := X))
  have h := A.T.dim_conj τ.1
  rw [A.dim_pos τ, A.dim_neg τ] at h
  have := X.p0_le
  omega

theorem map_injective {X : Data E r} {x : Frame X.Ψ r} (hx : x ∈ X.dom) (A : TorusAt X x) :
    Function.Injective A.φ := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro v hv
  by_contra hne
  have : Nonempty X.Ψ := Fintype.card_pos_iff.1 (QuadraticCoefficientForms.card_Psi_pos (X := X))
  have h := TorusAtDataPf.norm_sq_eq X x A v
  have hpos : 0 < ∑ τ : X.Ψ, X.c τ * X.maj x τ (Data.emb τ.1 v) := by
    refine Finset.sum_pos (fun τ _ => mul_pos ?_ ?_) Finset.univ_nonempty
    · have : τ.1 X.ξ0 ≠ 0 := (map_ne_zero τ.1).2 X.ξ0_ne
      unfold Data.c
      positivity
    · refine X.maj_pos hx τ fun h0 => hne (funext fun a => ?_)
      exact (map_eq_zero τ.1).1 (congrFun h0 a)
  rw [← h, hv] at hpos
  simp at hpos

theorem map_nat_smul {X : Data E r} {x : Frame X.Ψ r} (A : TorusAt X x) (n : ℕ) (v : Fin r → E) :
    A.φ ((n : E) • v) = (n : ℂ) • A.φ v := by
  rw [Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul, map_nsmul]

theorem map_five {X : Data E r} {x : Frame X.Ψ r} (A : TorusAt X x) (v : Fin r → E) :
    A.φ ((5 : E) • v) = (5 : ℂ) • A.φ v := by
  simpa only [Nat.cast_ofNat] using map_nat_smul A 5 v

theorem map_twentyfive {X : Data E r} {x : Frame X.Ψ r} (A : TorusAt X x) (v : Fin r → E) :
    A.φ ((25 : E) • v) = ((5 : ℂ) ^ 2) • A.φ v := by
  rw [show (5 : ℂ) ^ 2 = 25 by norm_num]
  simpa only [Nat.cast_ofNat] using map_nat_smul A 25 v

theorem map_mem_iff {X : Data E r} {x : Frame X.Ψ r} (hx : x ∈ X.dom) (A : TorusAt X x) (v : Fin r → E) :
    A.φ v ∈ A.T.L ↔ v ∈ X.Λ := by
  rw [A.lat]
  exact ⟨fun ⟨w, hw, h⟩ => map_injective hx A h ▸ hw, fun h => ⟨v, h, rfl⟩⟩

theorem gen_iff {X : Data E r} {x : Frame X.Ψ r} (hx : x ∈ X.dom) (A : TorusAt X x)
    (t : Fin r → Fin r → E) :
    Gen X.Λ t ↔ (∀ j, ((5 : ℂ) ^ 2) • A.φ (t j) ∈ A.T.L) ∧ ∀ z ∈ A.T.L, ∃ c : Fin r → 𝓞 E, ∃ y ∈ A.T.L,
      z = ∑ j, act (c j) (((5 : ℂ) ^ 2) • A.φ (t j)) + (5 : ℂ) • y := by
  have key : ∀ (c : Fin r → 𝓞 E) (y : Fin r → E),
      A.φ (∑ j, (c j : E) • ((25 : E) • t j) + (5 : E) • y) =
        ∑ j, act (c j) (((5 : ℂ) ^ 2) • A.φ (t j)) + (5 : ℂ) • A.φ y := by
    intro c y

    rw [map_add (f := _), map_sum, map_five]
    congr 1
    exact Finset.sum_congr rfl fun j _ => by rw [A.act_eq, map_twentyfive]
  refine and_congr (forall_congr' fun j => by rw [← map_twentyfive, map_mem_iff hx]) ⟨fun h z hz => ?_, fun h u hu => ?_⟩
  · obtain ⟨u, hu, rfl⟩ := (A.lat z).1 hz
    obtain ⟨c, y, hy, rfl⟩ := h u hu
    exact ⟨c, A.φ y, (map_mem_iff hx A y).2 hy, key c y⟩
  · obtain ⟨c, y, hy, e⟩ := h _ ((map_mem_iff hx A u).2 hu)
    obtain ⟨w, hw, rfl⟩ := (A.lat y).1 hy
    exact ⟨c, w, hw, map_injective hx A (by rw [key, e])⟩

theorem sum_eq {X : Data E r} {x : Frame X.Ψ r} (hx : x ∈ X.dom) (A : TorusAt X x)
    (𝒯 : Finset (Fin r → Fin r → E)) (h1 : ∀ t ∈ 𝒯, Gen X.Λ t)
    (h2 : ∀ t, Gen X.Λ t → ∃! t', t' ∈ 𝒯 ∧ ∀ j, t j - t' j ∈ X.Λ) (n : ℕ) (hn : n = r) :
    (∑ᶠ (a : Fin n → Vsp A.T.dim) (_ : a ∈ {a : Fin n → Vsp A.T.dim |
      (∀ j, a j ∈ ZSpan.fundamentalDomain A.T.b) ∧ (∀ j, ((5 : ℂ) ^ 2) • a j ∈ A.T.L) ∧
        ∀ x ∈ A.T.L, ∃ c : Fin n → 𝓞 E, ∃ y ∈ A.T.L,
          x = ∑ j, act (c j) (((5 : ℂ) ^ 2) • a j) + (5 : ℂ) • y}),
      ∏ b, A.T.ptN2 1 A.s (fun _ => a b) / A.T.l2 1 A.s) =
      ∑ t ∈ 𝒯, ∏ b, A.T.ptN2 1 A.s (fun _ => A.φ (t b)) / A.T.l2 1 A.s := by
  subst hn
  rw [← finsum_mem_coe_finset]
  symm
  refine finsum_mem_eq_of_bijOn (fun t j => ZSpan.fract A.T.b (A.φ (t j))) ⟨?_, ?_, ?_⟩ ?_
  · intro t ht
    have hl : ∀ j, ∃ v ∈ X.Λ, A.φ v = (ZSpan.floor A.T.b (A.φ (t j)) : Vsp A.T.dim) := fun j =>
      (A.lat _).1 (ZSpan.floor A.T.b (A.φ (t j))).2
    choose v hv hv' using hl
    have e : ∀ j, ZSpan.fract A.T.b (A.φ (t j)) = A.φ (t j - v j) := fun j => by
      rw [ZSpan.fract_apply, map_sub, hv']
    refine ⟨fun j => ZSpan.fract_mem_fundamentalDomain _ _, ?_⟩
    simp only [e]
    exact (gen_iff hx A _).1 ((h1 t ht).of_sub fun j => by simpa using hv j)
  · intro t ht t' ht' h
    refine ((h2 t (h1 t ht)).unique ⟨ht, fun j => by simp⟩ ⟨ht', fun j => ?_⟩)
    have := (ZSpan.fract_eq_fract A.T.b _ _).1 (congrFun h j).symm
    rw [← map_mem_iff hx A, map_sub, sub_eq_neg_add]
    exact this
  · rintro a ⟨ha, hb, hc⟩
    choose v hv hv' using fun j => (A.lat _).1 (hb j)
    have e : ∀ j, A.φ ((25 : E)⁻¹ • v j) = a j := fun j => by
      have h5 : ((5 : ℂ) ^ 2) ≠ 0 := by norm_num
      refine smul_right_injective _ h5 ?_
      simp only
      rw [← map_twentyfive, smul_inv_smul₀ (by norm_num), hv']
    have hg : Gen X.Λ fun j => (25 : E)⁻¹ • v j := (gen_iff hx A _).2 (by simp only [e]; exact ⟨hb, hc⟩)
    obtain ⟨t', ⟨ht', hs⟩, -⟩ := h2 _ hg
    refine ⟨t', ht', funext fun j => ?_⟩
    show ZSpan.fract A.T.b (A.φ (t' j)) = a j
    rw [← (ZSpan.fract_eq_self (b := A.T.b)).2 (ha j), ZSpan.fract_eq_fract, ← e j, ← sub_eq_neg_add, ← map_sub]
    exact (map_mem_iff hx A _).2 (hs j)
  · intro t _
    refine Finset.prod_congr rfl fun j _ => ?_
    congr 1
    have := pointwiseNormSq_add_period A.T (n := 1) A.s_mem
      (γ := fun _ => (ZSpan.floor A.T.b (A.φ (t j)) : Vsp A.T.dim)) (fun _ => (ZSpan.floor A.T.b (A.φ (t j))).2)
      (fun _ => ZSpan.fract A.T.b (A.φ (t j)))
    rw [← this]
    congr 1
    funext k
    simp [ZSpan.fract_apply]

end GlobalTheory.LevelTupleSum
end
