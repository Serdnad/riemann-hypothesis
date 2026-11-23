module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.HodgeTateFromSandwich
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.UnitaryHyperbolicOrbitCount
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IntegralityNearIdentity.Bundle001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.SignatureTorusFixedPoints.ThFacts
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
import Mathlib.RingTheory.Valuation.Integral
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

noncomputable section

open ValuativeRel Polynomial UpperTheory.V.Hi

namespace UpperTheory.V.Z.Sym.Sig

open Loc Glob

section Alg

variable {K : Type} [Field K] {τ a b : K}

private theorem ev_star (ha : a * a = τ * a - 1) (hb : b * b = τ * b - 1) (hs : a + b = τ)
    (x : Etau K τ) : ev ha (star x) = ev hb x := by
  show (star x).re + a * (star x).im = x.re + b * x.im
  rw [QuadraticAlgebra.re_star, QuadraticAlgebra.im_star]
  linear_combination (-x.im) * hs

private theorem ev_quo (ha : a * a = τ * a - 1) (hb : b * b = τ * b - 1) (hs : a + b = τ)
    (z : (Etau K τ)ˣ) : ev ha (quo z) = ((evU ha z / evU hb z : Kˣ) : K) := by
  show ev ha ((z : Etau K τ) * star ((z⁻¹ : (Etau K τ)ˣ) : Etau K τ)) = _
  rw [map_mul, ev_star ha hb hs, div_eq_mul_inv, ← map_inv, Units.val_mul]
  rfl

private theorem ev_ext (ha : a * a = τ * a - 1) (hb : b * b = τ * b - 1) (hab : a ≠ b)
    {x y : Etau K τ} (h1 : ev ha x = ev ha y) (h2 : ev hb x = ev hb y) : x = y := by
  have e1 : x.re + a * x.im = y.re + a * y.im := h1
  have e2 : x.re + b * x.im = y.re + b * y.im := h2
  have him : x.im = y.im := by
    have e3 : (a - b) * (x.im - y.im) = 0 := by linear_combination e1 - e2
    rcases mul_eq_zero.mp e3 with h | h
    · exact absurd (sub_eq_zero.mp h) hab
    · exact sub_eq_zero.mp h
  refine QuadraticAlgebra.ext ?_ him
  rw [him] at e1
  linear_combination e1

private theorem ev_exists (ha : a * a = τ * a - 1) (hb : b * b = τ * b - 1) (hab : a ≠ b)
    (u v : K) : ∃ x : Etau K τ, ev ha x = u ∧ ev hb x = v := by
  have hne : a - b ≠ 0 := sub_ne_zero.mpr hab
  refine ⟨⟨u - a * ((u - v) / (a - b)), (u - v) / (a - b)⟩, ?_, ?_⟩
  · show (u - a * ((u - v) / (a - b))) + a * ((u - v) / (a - b)) = u
    ring
  · show (u - a * ((u - v) / (a - b))) + b * ((u - v) / (a - b)) = v
    field_simp
    ring

private theorem ev_surj (ha : a * a = τ * a - 1) (hb : b * b = τ * b - 1) (hab : a ≠ b) :
    Function.Surjective (evU ha / evU hb) := by
  intro t
  obtain ⟨x, hx1, hx2⟩ := ev_exists ha hb hab (t : K) 1
  obtain ⟨y, hy1, hy2⟩ := ev_exists ha hb hab ((t⁻¹ : Kˣ) : K) 1
  have hxy : x * y = 1 := ev_ext ha hb hab
    (by rw [map_mul, map_one, hx1, hy1, Units.mul_inv])
    (by rw [map_mul, map_one, hx2, hy2, mul_one])
  refine ⟨⟨x, y, hxy, by rw [mul_comm]; exact hxy⟩, ?_⟩
  apply Units.ext
  rw [MonoidHom.div_apply, Units.val_div_eq_div_val]
  show ev ha x / ev hb x = t
  rw [hx1, hx2, div_one]

variable {O : Type} [CommRing O] [Algebra O K]

private theorem ev_algebraMap (ha : a * a = τ * a - 1) (r : O) :
    ev ha (algebraMap O (Etau K τ) r) = algebraMap O K r := by
  show algebraMap O K r + a * 0 = algebraMap O K r
  ring

private theorem isIntegral_ev (ha : a * a = τ * a - 1) {w : Etau K τ} (h : IsIntegral O w) :
    IsIntegral O (ev ha w) := by
  let f : Etau K τ →ₐ[O] K := { ev ha with commutes' := fun r => ev_algebraMap ha r }
  exact h.map f

private theorem isIntegral_of_ev (ha : a * a = τ * a - 1) (hb : b * b = τ * b - 1) (hab : a ≠ b)
    {w : Etau K τ} {p q : O} (h1 : ev ha w = algebraMap O K p) (h2 : ev hb w = algebraMap O K q) :
    IsIntegral O w := by
  refine ⟨(X - C p) * (X - C q), (monic_X_sub_C p).mul (monic_X_sub_C q), ?_⟩
  rw [eval₂_mul, eval₂_sub, eval₂_sub, eval₂_X, eval₂_C, eval₂_C]
  apply ev_ext ha hb hab
  · rw [map_mul, map_sub, map_sub, ev_algebraMap, ev_algebraMap, h1, sub_self, zero_mul, map_zero]
  · rw [map_mul, map_sub, map_sub, ev_algebraMap, ev_algebraMap, h2, sub_self, mul_zero, map_zero]

end Alg

theorem roots : Roots := by
  intro k _ _ _ _ O _ _ hO a ha1
  have hl := root_left (K := k) a
  have hr := root_right (K := k) a
  have hs : (a : k) + ((a⁻¹ : kˣ) : k) = (a : k) + ((a⁻¹ : kˣ) : k) := rfl
  have hs' : ((a⁻¹ : kˣ) : k) + (a : k) = (a : k) + ((a⁻¹ : kˣ) : k) := add_comm _ _
  have hab : (a : k) ≠ ((a⁻¹ : kˣ) : k) := by
    intro h
    have h2 : valuation k (a : k) * valuation k (a : k) = 1 := by
      rw [← map_mul]
      nth_rewrite 2 [h]
      rw [Units.mul_inv, map_one]
    have h3 := pow_lt_one₀ zero_le' ha1 (n := 2) two_ne_zero
    rw [sq, h2] at h3
    exact lt_irrefl _ h3
  have hint : (valuation k).Integers O :=
    ⟨hO.inj, fun x => (hO.range _).mp ⟨x, rfl⟩, fun r hr => (hO.range r).mpr hr⟩
  refine ⟨ev_surj hl hr hab, ?_, fun z => ⟨ev_quo hl hr hs z, ev_quo hr hl hs' z⟩⟩
  ext z
  show (IsIntegral O (quo z) ∧ IsIntegral O (quo z⁻¹)) ↔ valuation k (((evU hl / evU hr) z : kˣ) : k) = 1
  rw [MonoidHom.div_apply]
  have q1 : ev hl (quo z) = ((evU hl z / evU hr z : kˣ) : k) := ev_quo hl hr hs z
  have q2 : ev hr (quo z) = ((evU hr z / evU hl z : kˣ) : k) := ev_quo hr hl hs' z
  have q3 : ev hl (quo z⁻¹) = ((evU hr z / evU hl z : kˣ) : k) := by
    rw [ev_quo hl hr hs z⁻¹, map_inv, map_inv, inv_div_inv]
  have q4 : ev hr (quo z⁻¹) = ((evU hl z / evU hr z : kˣ) : k) := by
    rw [ev_quo hr hl hs' z⁻¹, map_inv, map_inv, inv_div_inv]
  have hprod : valuation k ((evU hl z / evU hr z : kˣ) : k) * valuation k ((evU hr z / evU hl z : kˣ) : k) = 1 := by
    rw [← map_mul, ← Units.val_mul, div_mul_div_comm, mul_comm (evU hr z) (evU hl z), div_self', Units.val_one, map_one]
  constructor
  · rintro ⟨i1, i2⟩
    have v1 : valuation k ((evU hl z / evU hr z : kˣ) : k) ≤ 1 := by
      have := hint.mem_of_integral (isIntegral_ev hl i1)
      rw [q1] at this
      exact (Valuation.mem_integer_iff _ _).mp this
    have v2 : valuation k ((evU hr z / evU hl z : kˣ) : k) ≤ 1 := by
      have := hint.mem_of_integral (isIntegral_ev hl i2)
      rw [q3] at this
      exact (Valuation.mem_integer_iff _ _).mp this
    refine le_antisymm v1 ?_
    calc (1 : ValueGroupWithZero k) = _ := hprod.symm
      _ ≤ valuation k ((evU hl z / evU hr z : kˣ) : k) * 1 := by gcongr
      _ = _ := mul_one _
  · intro hv
    have hv2 : valuation k ((evU hr z / evU hl z : kˣ) : k) = 1 := by
      rw [hv, one_mul] at hprod
      exact hprod
    obtain ⟨p, hp⟩ := (hO.range _).mpr hv.le
    obtain ⟨q, hq⟩ := (hO.range _).mpr hv2.le
    exact ⟨isIntegral_of_ev hl hr hab (q1.trans hp.symm) (q2.trans hq.symm),
      isIntegral_of_ev hl hr hab (q3.trans hq.symm) (q4.trans hp.symm)⟩

end UpperTheory.V.Z.Sym.Sig

end
end

section

open MulAction

namespace UpperTheory.V.Z.Sym.Sig

private theorem relIndex_smul {T Y : Type} [Group T] [MulAction T Y] (C : Subgroup T) (hC : C.Normal)
    (t : T) (y : Y) : (stabilizer T (t • y)).relIndex C = (stabilizer T y).relIndex C := by
  have hc : C.map (MulAut.conj t).toMonoidHom = C := by
    rw [MulEquiv.toMonoidHom_eq_coe, ← Subgroup.mem_normalizer_iff_map_conj_eq, Subgroup.normalizer_eq_top_iff.mpr hC]
    exact Subgroup.mem_top t
  rw [stabilizer_smul_eq_stabilizer_map_conj]
  conv_lhs => rw [← hc]
  exact Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj t).injective

private theorem wcount_congr {T Y Y' : Type} [Group T] [MulAction T Y] [MulAction T Y']
    (C : Subgroup T) (hC : C.Normal) (φ : Y ≃ Y') (hφ : ∀ (t : T) (y : Y), φ (t • y) = t • φ y)
    (k : Y → ℂ) (k' : Y' → ℂ) (hk : ∀ y, k y = k' (φ y)) (hinv : ∀ (t : T) (y : Y'), k' (t • y) = k' y) :
    wcount C k = wcount C k' := by
  have hkT : ∀ (t : T) (y : Y), k (t • y) = k y := by
    intro t y
    rw [hk, hk, hφ, hinv]
  have hst : ∀ y : Y, stabilizer T (φ y) = stabilizer T y := by
    intro y
    ext t
    rw [mem_stabilizer_iff, mem_stabilizer_iff, ← hφ]
    exact φ.injective.eq_iff
  have cls' : ∀ (y z : Y'), z ∈ orbit T y →
      ((stabilizer T z).relIndex C : ℂ) * k' z = ((stabilizer T y).relIndex C : ℂ) * k' y := by
    intro y z h
    obtain ⟨t, rfl⟩ := mem_orbit_iff.mp h
    rw [relIndex_smul C hC, hinv]
  let q : orbitRel.Quotient T Y ≃ orbitRel.Quotient T Y' :=
    Quotient.congr φ (by
      intro a b
      rw [orbitRel_apply, orbitRel_apply, mem_orbit_iff, mem_orbit_iff]
      constructor
      · rintro ⟨t, h⟩
        exact ⟨t, by rw [← hφ, h]⟩
      · rintro ⟨t, h⟩
        exact ⟨t, φ.injective (by rw [hφ, h])⟩)
  unfold wcount
  refine finsum_eq_of_bijective q q.bijective ?_
  intro o
  have hq : q o = Quotient.mk _ (φ (Quotient.out o)) := by
    conv_lhs => rw [← Quotient.out_eq o]
    rfl
  have ho : Quotient.out (q o) ∈ orbit T (φ (Quotient.out o)) := by
    rw [← orbitRel_apply]
    exact Quotient.exact (by rw [Quotient.out_eq]; exact hq)
  rw [cls' _ _ ho, hst, ← hk]

private def qmap {G G' : Type} [Group G] [Group G'] (e : G →* G') (U' : Subgroup G') :
    G ⧸ U'.comap e → G' ⧸ U' :=
  Quotient.map' e (by
    intro a b h
    rw [QuotientGroup.leftRel_apply] at h ⊢
    simpa using h)

private theorem qmap_mk {G G' : Type} [Group G] [Group G'] (e : G →* G') (U' : Subgroup G') (g : G) :
    qmap e U' (g : G ⧸ U'.comap e) = (e g : G' ⧸ U') := rfl

private theorem qmap_bij {G G' : Type} [Group G] [Group G'] (e : G →* G') (he : Function.Bijective e)
    (U' : Subgroup G') : Function.Bijective (qmap e U') := by
  constructor
  · intro x y h
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective y
    rw [qmap_mk, qmap_mk, QuotientGroup.eq] at h
    rw [QuotientGroup.eq, Subgroup.mem_comap, map_mul, map_inv]
    exact h
  · intro z
    obtain ⟨c, rfl⟩ := QuotientGroup.mk_surjective z
    obtain ⟨a, rfl⟩ := he.2 c
    exact ⟨a, qmap_mk e U' a⟩

private theorem f_out {G' : Type} [Group G'] (θ' : G' →* G') (U' : Subgroup G') (f : G' → ℂ)
    (hf : ∀ u ∈ U', ∀ x, f (u⁻¹ * x * θ' u) = f x) (x z : G') :
    f ((z : G' ⧸ U').out⁻¹ * x * θ' (z : G' ⧸ U').out) = f (z⁻¹ * x * θ' z) := by
  have hu : z⁻¹ * (z : G' ⧸ U').out ∈ U' :=
    QuotientGroup.eq.mp (QuotientGroup.out_eq' (z : G' ⧸ U')).symm
  obtain ⟨u, hu, hw⟩ : ∃ u ∈ U', (z : G' ⧸ U').out = z * u :=
    ⟨_, hu, (mul_inv_cancel_left z _).symm⟩
  rw [hw, ← hf u hu (z⁻¹ * x * θ' z)]
  congr 1
  rw [map_mul]
  group

end UpperTheory.V.Z.Sym.Sig

theorem UpperTheory.V.Z.Sym.Sig.orbMap :
    UpperTheory.V.Z.Sym.Sig.OrbMap := by
  classical
  intro T G G' _ _ _ e he ι C θ θ' hθ U' f δ hf hδ hC
  let E : G ≃* G' := MulEquiv.ofBijective e he
  have hc : ∀ (g : G), e (g⁻¹ * δ * θ g) = (e g)⁻¹ * e δ * θ' (e g) := by
    intro g
    rw [map_mul, map_mul, map_inv, hθ]
  refine ⟨?_, ?_, ?_⟩
  · letI : MulAction T (G ⧸ U'.comap e) := MulAction.compHom _ ι
    letI : MulAction T (G' ⧸ U') := MulAction.compHom _ (e.comp ι)
    unfold UpperTheory.V.Z.Sym.orb
    refine UpperTheory.V.Z.Sym.Sig.wcount_congr C hC
      (Equiv.ofBijective _ (UpperTheory.V.Z.Sym.Sig.qmap_bij e he U')) ?_ _ _ ?_ ?_
    · intro t y
      obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective y
      rw [MulAction.compHom_smul_def, MulAction.compHom_smul_def]
      simp only [Equiv.ofBijective_apply, MulAction.Quotient.smul_coe, smul_eq_mul,
        UpperTheory.V.Z.Sym.Sig.qmap_mk, map_mul, MonoidHom.comp_apply]
    · intro y
      simp only [Equiv.ofBijective_apply]
      conv_rhs => rw [← QuotientGroup.out_eq' y, UpperTheory.V.Z.Sym.Sig.qmap_mk, UpperTheory.V.Z.Sym.Sig.f_out θ' U' f hf]
      rw [hc]
    · intro t y
      obtain ⟨z, rfl⟩ := QuotientGroup.mk_surjective y
      rw [MulAction.compHom_smul_def, MulAction.Quotient.smul_coe, smul_eq_mul,
        UpperTheory.V.Z.Sym.Sig.f_out θ' U' f hf, UpperTheory.V.Z.Sym.Sig.f_out θ' U' f hf, MonoidHom.comp_apply]
      congr 1
      have h1 : e ((ι t)⁻¹ * δ * θ (ι t)) = e δ := by rw [hδ]
      rw [hc] at h1
      have key : (e (ι t) * z)⁻¹ * e δ * θ' (e (ι t) * z)
          = z⁻¹ * ((e (ι t))⁻¹ * e δ * θ' (e (ι t))) * θ' z := by
        rw [map_mul]
        group
      rw [key, h1]
  · unfold UpperTheory.V.Z.Sym.FinOrb
    constructor
    · rintro ⟨S, hS⟩
      refine ⟨S.image e, fun y hy => ?_⟩
      obtain ⟨g, rfl⟩ := he.2 y
      rw [← hc] at hy
      obtain ⟨t, s, hs, u, hu, rfl⟩ := hS g hy
      exact ⟨t, e s, Finset.mem_image_of_mem e hs, e u, hu, by simp [map_mul]⟩
    · rintro ⟨S, hS⟩
      refine ⟨S.image E.symm, fun g hg => ?_⟩
      simp only at hg
      rw [hc] at hg
      obtain ⟨t, s, hs, u, hu, h⟩ := hS (e g) hg
      refine ⟨t, E.symm s, Finset.mem_image_of_mem _ hs, E.symm u, ?_, ?_⟩
      · rw [Subgroup.mem_comap]
        show E (E.symm u) ∈ U'
        rw [MulEquiv.apply_symm_apply]
        exact hu
      · apply E.injective
        rw [map_mul, map_mul, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
        exact h
  · intro y
    ext t
    simp only [Subgroup.mem_comap, mem_stabilizer_iff, MonoidHom.comp_apply,
      MulAction.Quotient.smul_coe, smul_eq_mul, QuotientGroup.eq, map_mul, map_inv]
end

section

noncomputable section

open ValuativeRel Matrix Polynomial GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V.Hi UpperTheory.V.Z.Sym.Sig

namespace UpperTheory.V.Z.Sym.Sig

private theorem exists_conj_diag {k : Type} [Field k] (N : GL (Fin 3) k) (μ : Fin 3 → kˣ)
    (hμ : Function.Injective μ) (hroot : ∀ i, ((N : Matrix (Fin 3) (Fin 3) k).charpoly).IsRoot (μ i : k)) :
    ∃ g : GL (Fin 3) k, N = g * diagT k (Fin 3) μ * g⁻¹ :=
  UpperTheory.V.Lib.Small.conj_of_roots (fun i => (μ i : k)) (fun _ _ e => hμ (Units.ext e)) N _ (GlobalTheory.SmGL.val_diagT k μ) hroot

private theorem diag_of_comm {k : Type} [Field k] (μ : Fin 3 → kˣ) (hμ : Function.Injective μ)
    (e : GL (Fin 3) k) (h : e * diagT k (Fin 3) μ = diagT k (Fin 3) μ * e) :
    ∃ u : Fin 3 → kˣ, e = diagT k (Fin 3) u := by
  have hoff : ∀ i j, i ≠ j → (e : Matrix (Fin 3) (Fin 3) k) i j = 0 := by
    intro i j hij
    have h1 := congrArg (fun M : Matrix (Fin 3) (Fin 3) k => M i j) (congrArg Units.val h)
    simp only [Units.val_mul, val_diagT, Matrix.mul_diagonal, Matrix.diagonal_mul] at h1
    have h2 : (μ j : k) ≠ μ i := fun h' => hij (hμ (Units.ext h')).symm
    have h3 : (e : Matrix (Fin 3) (Fin 3) k) i j * ((μ j : k) - μ i) = 0 := by
      rw [mul_sub, h1]; ring
    exact (mul_eq_zero.1 h3).resolve_right (sub_ne_zero.2 h2)
  have hdiag : (e : Matrix (Fin 3) (Fin 3) k) = Matrix.diagonal fun i => (e : Matrix (Fin 3) (Fin 3) k) i i := by
    ext i j
    by_cases hij : i = j
    · subst hij; simp
    · simp [hoff i j hij, Matrix.diagonal_apply_ne _ hij]
  have hdet : (e : Matrix (Fin 3) (Fin 3) k).det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).1 e.isUnit).ne_zero
  have hne : ∀ i, (e : Matrix (Fin 3) (Fin 3) k) i i ≠ 0 := by
    intro i hi
    apply hdet
    rw [hdiag, Matrix.det_diagonal]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simpa using hi)
  refine ⟨fun i => Units.mk0 _ (hne i), Units.ext ?_⟩
  rw [val_diagT]
  simpa using hdiag

end UpperTheory.V.Z.Sym.Sig

theorem UpperTheory.V.Z.Sym.Sig.normalG :
    UpperTheory.V.Z.Sym.Sig.NormalG := by
  intro k _ _ _ _
  obtain ⟨-, -, hd, hθ, hΦ, hi, hc⟩ := thFacts k (Lev.iw k)
  obtain hP := (thFacts k (Lev.iw k)).1
  have ht : ∀ u : GL (Fin 3) k, th' k u = Phi k * th k 3 u * (Phi k)⁻¹ := fun u => rfl
  have hprod : ∀ x y z : kˣ, dg ![x, y, z] * th' k (dg ![x, y, z]) = dg ![x / z, 1, z / x] := by
    intro x y z
    rw [hd, ← map_mul]
    congr 1
    funext i
    fin_cases i <;> simp [div_eq_mul_inv, mul_comm]
  refine ⟨fun g₀ x y z => ?_, fun δ a ha hch => ?_⟩
  · rw [← hprod x y z, ht]
    simp only [map_mul, map_inv, hθ, hΦ]
    group
  · have ha0 : (a : k) ≠ 0 := a.ne_zero
    have hgt : 1 < valuation k ((a⁻¹ : kˣ) : k) := by
      rw [Units.val_inv_eq_inv_val, map_inv₀]
      exact (one_lt_inv₀ (zero_lt_iff.2 ((valuation k).ne_zero_iff.2 ha0))).2 ha
    have h1 : (a : k) ≠ 1 := fun h => by rw [h, map_one] at ha; exact lt_irrefl _ ha
    have h2 : ((a⁻¹ : kˣ) : k) ≠ 1 := fun h => by rw [h, map_one] at hgt; exact lt_irrefl _ hgt
    have h3 : (a : k) ≠ ((a⁻¹ : kˣ) : k) := fun h => by
      rw [← h] at hgt; exact lt_asymm ha hgt
    have hμ : Function.Injective (![a, 1, a⁻¹] : Fin 3 → kˣ) := by
      intro i j hij
      fin_cases i <;> fin_cases j <;> first
        | rfl
        | (exfalso
           have hij' := congrArg Units.val hij
           simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val, Units.val_one] at hij'
           first
             | exact h1 hij' | exact h1 hij'.symm | exact h2 hij' | exact h2 hij'.symm
             | exact h3 hij' | exact h3 hij'.symm)
    have hroot : ∀ i, (((δ * th k 3 δ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k).charpoly).IsRoot
        (((![a, 1, a⁻¹] : Fin 3 → kˣ) i : kˣ) : k) := by
      intro i
      rw [hch]
      fin_cases i <;> simp [Polynomial.IsRoot]
    obtain ⟨g₀, hN⟩ := exists_conj_diag (δ * th k 3 δ) _ hμ hroot
    set n : GL (Fin 3) k := dg ![a, 1, a⁻¹] with hn
    set e : GL (Fin 3) k := g₀⁻¹ * δ * th k 3 g₀ * (Phi k)⁻¹ with he
    have hen : e * th' k e = n := by
      have : e * th' k e = g₀⁻¹ * (δ * th k 3 δ) * g₀ := by
        rw [ht, he]
        simp only [map_mul, map_inv, hθ, hΦ, inv_inv]
        group
      rw [this, hN]
      simp only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one]
      try rfl
    have hfix : th' k n = n := by
      rw [hn, hd]
      simp
    have hne : th' k e * e = n := by
      have := congrArg (th' k) hen
      rwa [map_mul, hP.invol, hfix] at this
    have hcomm : e * n = n * e := by
      nth_rewrite 1 [← hne]
      nth_rewrite 1 [← hen]
      group
    obtain ⟨u, hu⟩ := diag_of_comm _ hμ e hcomm
    have hu' : u = ![u 0, u 1, u 2] := by
      funext i; fin_cases i <;> rfl
    refine ⟨g₀, u 0, u 1, u 2, ?_, ?_⟩
    · have : dg ![u 0, u 1, u 2] = e := by rw [hu]; exact congrArg _ hu'.symm
      rw [this, he]
      group
    · have h4 : dg ![u 0 / u 2, 1, u 2 / u 0] = n := by
        rw [← hprod, ← hu' , ← hen, hu]
      have h5 := congrArg (fun M : Matrix (Fin 3) (Fin 3) k => M 0 0) (congrArg Units.val h4)
      simp only [hn, dg, val_diagT] at h5
      simpa [Units.ext_iff] using h5

end
end
