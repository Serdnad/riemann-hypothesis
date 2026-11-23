module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdjointMemSp4
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.Bundle004
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
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open IsLocalRing UpperTheory.V UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

namespace UpperTheory.V.Ws.X1

variable {k : Type} [Field k]

private theorem ent (X : sp4 k) (i j : Fin 4) : (sgn i * sgn j) • X.1 j.rev i.rev = -X.1 i j := by
  have h : adj X.1 = -X.1 := X.2
  have h' := congrFun (congrFun h i) j
  rwa [adj_apply, Matrix.neg_apply] at h'

private theorem conj_mem (n : M4 k) (X : sp4 k) : adj n * X.1 * n ∈ sp4 k := by
  show adj (adj n * X.1 * n) = -(adj n * X.1 * n)
  rw [(grp k).1, (grp k).1, (grp k).2.1, show adj X.1 = -X.1 from X.2]
  noncomm_ring

private noncomputable def cj (n : M4 k) : sp4 k →ₗ[k] sp4 k where
  toFun X := ⟨adj n * X.1 * n, conj_mem n X⟩
  map_add' X Y := Subtype.ext (by simp [mul_add, add_mul])
  map_smul' c X := Subtype.ext (by simp)

private noncomputable def cjE (n : M4 k) (hn : IsGSp 1 n) : sp4 k ≃ₗ[k] sp4 k :=
  LinearEquiv.ofLinear (cj n) (cj (adj n))
    (LinearMap.ext fun X => Subtype.ext (by
      have h : adj n * n = 1 := by simpa [IsGSp] using hn
      show adj n * (adj (adj n) * X.1 * adj n) * n = X.1
      rw [(grp k).2.1, mul_assoc n, ← mul_assoc (adj n), h, one_mul, mul_assoc, h, mul_one]))
    (LinearMap.ext fun X => Subtype.ext (by
      have h : adj n * n = 1 := by simpa [IsGSp] using hn
      have h' : n * adj n = 1 := mul_eq_one_comm.mp h
      show adj (adj n) * (adj n * X.1 * n) * adj n = X.1
      rw [(grp k).2.1, mul_assoc (adj n), ← mul_assoc n, h', one_mul, mul_assoc, h', mul_one]))

private theorem cj_one (X : M4 k) : adj 1 * X * 1 = X := by
  rw [(grp k).2.2.2.2.1, one_mul, mul_one]

private theorem mem_borel_identity_iff_upper (X : sp4 k) : X ∈ bor (1 : M4 k) ↔ IsUp X.1 := by
  show IsUp (adj 1 * X.1 * 1) ↔ _
  rw [cj_one]

private theorem mem_nilradical_identity_iff (X : sp4 k) : X ∈ nil (1 : M4 k) ↔ ∀ i j, i ≤ j → X.1 i j = 0 := by
  show (∀ i j, i ≤ j → (adj 1 * X.1 * 1 : M4 k) i j = 0) ↔ _
  rw [cj_one]

private theorem bor_eq (n : M4 k) (hn : IsGSp 1 n) : bor n = (bor 1).comap (cjE n hn : sp4 k →ₗ[k] sp4 k) := by
  ext X
  rw [Submodule.mem_comap, mem_borel_identity_iff_upper]
  rfl

private theorem nil_eq (n : M4 k) (hn : IsGSp 1 n) : nil n = (nil 1).comap (cjE n hn : sp4 k →ₗ[k] sp4 k) := by
  ext X
  rw [Submodule.mem_comap, mem_nilradical_identity_iff]
  rfl

private theorem compl1 : IsCompl (bor (1 : M4 k)) (nil 1) := by
  constructor
  · rw [Submodule.disjoint_def]
    intro X h1 h2
    rw [mem_borel_identity_iff_upper] at h1
    rw [mem_nilradical_identity_iff] at h2
    apply Subtype.ext
    ext i j
    rcases lt_or_ge j i with h | h
    · exact h1 i j h
    · exact h2 i j h
  · rw [codisjoint_iff, eq_top_iff]
    intro X _
    let L : M4 k := Matrix.of fun i j => if j < i then X.1 i j else 0
    have hL : L ∈ sp4 k := by
      show adj L = -L
      ext i j
      rw [adj_apply, Matrix.neg_apply]
      simp only [L, Matrix.of_apply, Fin.rev_lt_rev]
      split_ifs with h
      · exact ent X i j
      · simp
    have hU : X.1 - L ∈ sp4 k := Submodule.sub_mem _ X.2 hL
    rw [Submodule.mem_sup]
    refine ⟨⟨X.1 - L, hU⟩, ?_, ⟨L, hL⟩, ?_, ?_⟩
    · rw [mem_borel_identity_iff_upper]
      intro i j h
      simp [L, h]
    · rw [mem_nilradical_identity_iff]
      intro i j h
      simp [L, not_lt.mpr h]
    · apply Subtype.ext
      simp

private theorem up_mem (a b c d e f : k) : (!![a, c, d, e; 0, b, f, d; 0, 0, -b, -c; 0, 0, 0, -a] : M4 k) ∈ sp4 k := by
  show adj _ = -_
  ext i j
  fin_cases i <;> fin_cases j <;> simp [adj_apply, sgn, Fin.rev]

private theorem up_zero (X : sp4 k) (hu : IsUp X.1) (h0 : X.1 0 0 = 0) (h1 : X.1 1 1 = 0) (h2 : X.1 0 1 = 0)
    (h3 : X.1 0 2 = 0) (h4 : X.1 0 3 = 0) (h5 : X.1 1 2 = 0) : X = 0 := by
  apply Subtype.ext
  ext i j
  have e := ent X i j
  fin_cases i <;> fin_cases j <;> simp [sgn, Fin.rev, h0, h1, h2, h3, h4, h5] at e ⊢ <;>
    first
    | exact hu _ _ (by decide)
    | exact e
    | exact neg_eq_zero.mp e.symm
    | skip

private theorem bor1 : Module.finrank k (bor (1 : M4 k)) = 6 := by
  let f : bor (1 : M4 k) →ₗ[k] (Fin 6 → k) :=
    { toFun := fun X => ![X.1.1 0 0, X.1.1 1 1, X.1.1 0 1, X.1.1 0 2, X.1.1 0 3, X.1.1 1 2]
      map_add' := fun X Y => by
        ext t
        fin_cases t <;> rfl
      map_smul' := fun c X => by
        ext t
        fin_cases t <;> rfl }
  have hinj : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro X hX
    have hc : ∀ t, f X t = 0 := fun t => congrFun hX t
    exact Subtype.ext (up_zero X.1 ((mem_borel_identity_iff_upper X.1).mp X.2) (hc 0) (hc 1) (hc 2) (hc 3) (hc 4) (hc 5))
  have hsurj : Function.Surjective f := by
    intro v
    refine ⟨⟨⟨!![v 0, v 2, v 3, v 4; 0, v 1, v 5, v 3; 0, 0, -v 1, -v 2; 0, 0, 0, -v 0],
      up_mem _ _ _ _ _ _⟩, ?_⟩, ?_⟩
    · rw [mem_borel_identity_iff_upper]
      intro i j h
      fin_cases i <;> fin_cases j <;> simp_all
    · ext t
      fin_cases t <;> rfl
  rw [LinearEquiv.finrank_eq (LinearEquiv.ofBijective f ⟨hinj, hsurj⟩), Module.finrank_fin_fun]

private theorem tor2 : Module.finrank k (tor k) = 2 := by
  let f : tor k →ₗ[k] (Fin 2 → k) :=
    { toFun := fun X => ![X.1.1 0 0, X.1.1 1 1]
      map_add' := fun X Y => by
        ext t
        fin_cases t <;> rfl
      map_smul' := fun c X => by
        ext t
        fin_cases t <;> rfl }
  have hinj : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro X hX
    have h0 : X.1.1 0 0 = 0 := congrFun hX 0
    have h1 : X.1.1 1 1 = 0 := congrFun hX 1
    have hd : Matrix.IsDiag X.1.1 := X.2
    apply Subtype.ext
    apply Subtype.ext
    ext i j
    have e := ent X.1 i j
    fin_cases i <;> fin_cases j <;> simp [sgn, Fin.rev, h0, h1] at e ⊢ <;>
      first
      | exact hd (by decide)
      | exact e
      | exact neg_eq_zero.mp e.symm
  have hsurj : Function.Surjective f := by
    intro v
    refine ⟨⟨⟨!![v 0, 0, 0, 0; 0, v 1, 0, 0; 0, 0, -v 1, -0; 0, 0, 0, -v 0],
      up_mem _ _ _ _ _ _⟩, ?_⟩, ?_⟩
    · show Matrix.IsDiag _
      intro i j h
      fin_cases i <;> fin_cases j <;> simp_all
    · ext t
      fin_cases t <;> rfl
  rw [LinearEquiv.finrank_eq (LinearEquiv.ofBijective f ⟨hinj, hsurj⟩), Module.finrank_fin_fun]

end UpperTheory.V.Ws.X1

theorem UpperTheory.V.Ws.X1.spDims :
    ∀ (k : Type) [Field k], (2 : k) ≠ 0 → Module.finrank k (tor k) = 2 ∧ ∀ n : M4 k, IsGSp 1 n → Module.finrank k (bor n) = 6 ∧ IsCompl (bor n) (nil n) := by
  intro k _ _
  refine ⟨X1.tor2, fun n hn => ⟨?_, ?_⟩⟩
  · have hm : (bor (1 : M4 k)).map ((X1.cjE n hn).symm : sp4 k →ₗ[k] sp4 k)
        = (bor 1).comap (X1.cjE n hn : sp4 k →ₗ[k] sp4 k) :=
      Submodule.map_equiv_eq_comap_symm _ _
    rw [X1.bor_eq n hn, ← hm, LinearEquiv.finrank_map_eq, X1.bor1]
  · rw [X1.bor_eq n hn, X1.nil_eq n hn]
    exact (Submodule.orderIsoMapComap (X1.cjE n hn)).symm.isCompl X1.compl1
end

section

open IsLocalRing UpperTheory.V UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem exists_strictHenselian_absolutely_closed_local_ring {k A : Type} [CommRing k] [CommRing A] (π : A → k) (μ : k → A)
    (h1 : ∀ c d, μ (c + d) = μ c + μ d) (h2 : ∀ (a : A) c, μ (π a * c) = a * μ c) :
    ∃ T : M4 k →+ M4 A, (∀ Y, Y.map μ = T Y) ∧
      (∀ (M : M4 A) Y, M * T Y = T (M.map π * Y)) ∧
      (∀ (M : M4 A) Y, T Y * M = T (Y * M.map π)) ∧ (∀ Y, adj (T Y) = T (adj Y)) ∧
      ∀ Y, IsUp Y → IsUp (T Y) := by
  let m : k →+ A := AddMonoidHom.mk' μ h1
  have h3 : ∀ (a : A) c, m (π a * c) = a * m c := h2
  refine ⟨m.mapMatrix, fun Y => rfl, fun M Y => ?_, fun M Y => ?_, fun Y => ?_, fun Y hY i j h => ?_⟩
  · ext a b

    simp only [AddMonoidHom.mapMatrix_apply, Matrix.map_apply, Matrix.mul_apply, map_sum, h3]
  · ext a b

    simp only [AddMonoidHom.mapMatrix_apply, Matrix.map_apply, Matrix.mul_apply, map_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [mul_comm (Y a c), h3, mul_comm]
  · ext a b
    simp only [AddMonoidHom.mapMatrix_apply, Matrix.map_apply, adj_apply, map_zsmul]
  · simp only [AddMonoidHom.mapMatrix_apply, Matrix.map_apply, hY i j h, map_zero]

private theorem isUp_mul {k : Type} [CommRing k] {X Y : M4 k} (hX : IsUp X) (hY : IsUp Y) : IsUp (X * Y) := by
  intro i j h
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun c _ => ?_
  by_cases hc : c < i
  · rw [hX i c hc, zero_mul]
  · rw [hY c j (lt_of_lt_of_le h (not_lt.1 hc)), mul_zero]

private theorem isUp_add {k : Type} [CommRing k] {X Y : M4 k} (hX : IsUp X) (hY : IsUp Y) : IsUp (X + Y) := by
  intro i j h
  rw [Matrix.add_apply, hX i j h, hY i j h, add_zero]

private theorem alg_id {S : Type} [Ring S] (a n B g y : S) (h : n * a = 1) :
    a * (B * g - (g * y - y * g)) * n + (a * (g * (y * n)) + a * -y * g * n) = a * B * n * (a * g * n) := by
  have : a * B * n * (a * g * n) = a * B * (n * a) * g * n := by simp only [mul_assoc]
  rw [this, h]
  noncomm_ring

private theorem rb_lc {Λ : Type} [CommRing Λ] [IsLocalRing Λ] {Γ : Type} [TopologicalSpace Γ]
    {R : Type} [CommRing R] [Algebra Λ R] [IsCO Λ R] (r : Γ → M4 R) (rb : Γ → M4 (ResidueField Λ))
    (hc : ∀ i j, AdicCont (maximalIdeal R) fun g => r g i j) (hr : ∀ g, (r g).map (res Λ R) = rb g) :
    IsLocallyConstant rb := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro s
  have : ∀ a b, ∀ᶠ t in nhds s, rb t a b = rb s a b := fun a b => by
    filter_upwards [(hc a b 1).eventually_eq s] with t ht
    rw [Ideal.Quotient.eq, pow_one, ← res_eq_zero_iff Λ, map_sub, sub_eq_zero] at ht
    rw [← hr, ← hr]
    exact ht
  filter_upwards [Filter.eventually_all.2 fun a => Filter.eventually_all.2 (this a)] with t ht
  ext a b
  exact ht a b

theorem UpperTheory.V.Ws.X1.obCor :
    ∀ {Λ : Type} [CommRing Λ] [IsLocalRing Λ] [IsNoetherianRing Λ] [IsAdicComplete (maximalIdeal Λ) Λ] {Γ V : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] {Gv : V → Type} [∀ v, Group (Gv v)] [∀ v, TopologicalSpace (Gv v)] [∀ v, IsTopologicalGroup (Gv v)] (loc : ∀ v, Gv v →* Γ), (∀ v, Continuous (loc v)) → ∀ {A R : Type} [CommRing A] [Algebra Λ A] [IsCO Λ A] [CommRing R] [Algebra Λ R] [IsCO Λ R] (p : A →ₐ[Λ] R), Function.Surjective p → maximalIdeal A * RingHom.ker p = ⊥ → ∀ (ν : Γ →* Λˣ) (r : Γ →* M4 R) (n : V → M4 R), AdicCont (maximalIdeal Λ) (fun g => (ν g : Λ)) → WP loc (fun g => algebraMap Λ R (ν g)) r n → (∀ i j, AdicCont (maximalIdeal R) fun g => r g i j) → ∀ (rb : Γ →* M4 (ResidueField Λ)) (nb : V → M4 (ResidueField Λ)) (hb : ∀ g, ∃ x, IsGSp x (rb g)), (∀ g, (r g).map (res Λ R) = rb g) → (∀ v, (n v).map (res Λ R) = nb v) → ∀ (D : SL loc ν r n p) (μ : ResidueField Λ → A), (∀ c d, μ (c + d) = μ c + μ d) → (∀ (a : A) c, μ (res Λ A a * c) = a * μ c) → (∀ c, p (μ c) = 0) → ∀ x ∈ Fr.continuousCoboundaries2 loc (adSp rb hb) (fun v => bor (nb v)), (∀ s t, D.om s t = ((x.1 (s, t)).1 * rb (s * t)).map μ) → (∀ v s, D.de v s = ((x.2 v s).1 * rb (loc v s)).map μ) → WLift loc ν r n p := by
  intro Λ _ _ _ _ Γ V _ _ _ Gv _ _ _ loc hloc A R _ _ _ _ _ _ p hp hs ν r n hν hW hc rb nb hb hr hn D μ m1 m2 m3
    x hx x1 x2
  obtain ⟨T, T0, Tl, Tr, Ta, Tu⟩ := exists_strictHenselian_absolutely_closed_local_ring (res Λ A) μ m1 m2
  simp only [T0, SL.om, SL.de] at x1 x2
  have lc := rb_lc r rb hc hr
  obtain ⟨h, y, b1, b3, b4⟩ := hx
  obtain ⟨class_group_mod_eq_torsion, -, gA3, -, -, gA6, -⟩ := grp A
  obtain ⟨gR1, -, -, -, -, gR6, -⟩ := grp R
  obtain ⟨gk1, -⟩ := grp (ResidueField Λ)
  have aA : ∀ X : M4 A, (adj X).map (res Λ A) = adj (X.map (res Λ A)) := fun X =>
    (gA6 _ (res Λ A : A →+* ResidueField Λ) X).symm
  have aR : ∀ X : M4 R, (adj X).map (res Λ R) = adj (X.map (res Λ R)) := fun X =>
    (gR6 _ (res Λ R : R →+* ResidueField Λ) X).symm
  have mR : ∀ X Y : M4 R, (X * Y).map (res Λ R) = X.map (res Λ R) * Y.map (res Λ R) := fun X Y =>
    Matrix.map_mul (f := (res Λ R : R →+* ResidueField Λ))
  have Tp : ∀ Y, (T Y).map p = 0 := fun Y => by
    rw [← T0]; ext a b; exact m3 _
  have Tres : ∀ Y, (T Y).map (res Λ A) = 0 := fun Y => by
    rw [← T0]; ext a b
    show res Λ A (μ _) = 0
    rw [← UpperTheory.V.Alg.res_map p, m3, map_zero]
  have TT : ∀ Y Y', T Y * T Y' = 0 := fun Y Y' => by rw [Tl, Tres, zero_mul, map_zero]
  have rtres : ∀ s, (D.rt s).map (res Λ A) = rb s := fun s => by
    ext a b
    rw [Matrix.map_apply, ← UpperTheory.V.Alg.res_map p, ← hr, ← D.rt_map, Matrix.map_apply, Matrix.map_apply]
  have ntres : ∀ v, (D.nt v).map (res Λ A) = nb v := fun s => by
    ext a b
    rw [Matrix.map_apply, ← UpperTheory.V.Alg.res_map p, ← hn, ← D.nt_map, Matrix.map_apply, Matrix.map_apply]
  have pert : ∀ (c : A) (g : M4 A) (Y : M4 (ResidueField Λ)), IsGSp c g → Y ∈ sp4 (ResidueField Λ) →
      IsGSp c (g + T (Y * g.map (res Λ A))) := fun c g Y hg hY => by
    have hY' : adj Y = -Y := hY
    unfold IsGSp at *
    rw [gA3, Ta, gk1, hY', add_mul, mul_add, mul_add, TT, Tl, Tr, hg, aA]
    simp only [mul_neg, neg_mul, map_neg, mul_assoc]
    abel
  have inv1 : ∀ s, rb s * rb s⁻¹ = 1 := fun s => by rw [← map_mul, mul_inv_cancel, map_one]
  have inv2 : ∀ s, rb s⁻¹ * rb s = 1 := fun s => by rw [← map_mul, inv_mul_cancel, map_one]
  set f : Γ → M4 A := fun s => D.rt s - T ((h s).1 * rb s) with hf
  have fH : ∀ s, IsGSp (algebraMap Λ A (ν s)) (f s) := fun s => by
    have := pert _ _ _ (D.rt_mult s) (-h s).2
    rw [rtres, Submodule.coe_neg, neg_mul, map_neg, ← sub_eq_add_neg] at this
    exact this
  have fmul : ∀ s t, f (s * t) = f s * f t := fun s t => by
    have e := x1 s t
    rw [b3, sub_eq_iff_eq_add] at e
    have e' : ((dOne (adSp rb hb) h (s, t)).1 : M4 _) * rb (s * t) =
        (h s).1 * rb s * rb t + rb s * ((h t).1 * rb t) - (h (s * t)).1 * rb (s * t) := by
      show ((h s).1 + rb s * (h t).1 * rb s⁻¹ - (h (s * t)).1) * rb (s * t) = _
      rw [sub_mul, add_mul, map_mul, mul_assoc (rb s * (h t).1), ← mul_assoc (rb s⁻¹), inv2, one_mul]
      simp only [mul_assoc]
    rw [hf]
    simp only
    rw [sub_mul, mul_sub, mul_sub, TT, Tl, Tr, rtres, rtres, e, e', map_sub, map_add (f := _)]
    abel
  have fone : f 1 = 1 := by
    have hu : adj (f 1) * f 1 = 1 := by
      have := fH 1
      unfold IsGSp at this
      rw [this]; simp
    have := fmul 1 1
    rw [mul_one] at this
    calc f 1 = adj (f 1) * f 1 * f 1 := by rw [hu, one_mul]
      _ = 1 := by rw [mul_assoc, ← this, hu]
  have fp : ∀ s, (f s).map p = r s := fun s => by
    rw [hf]
    simp only
    rw [Matrix.map_sub _ (map_sub p), Tp, D.rt_map, sub_zero]
  have fres : ∀ s, (f s).map (res Λ A) = rb s := fun s => by
    ext a b
    rw [Matrix.map_apply, ← UpperTheory.V.Alg.res_map p, ← hr, ← fp, Matrix.map_apply, Matrix.map_apply]
  refine ⟨{ toFun := f, map_one' := fone, map_mul' := fmul }, fun v => D.nt v + T ((y v).1 * nb v),
    ⟨fH, fun v => ?_, fun v s => ?_⟩, fun a b N => ?_, fp, fun v => ?_⟩
  · have := pert _ _ _ (D.nt_sp v) (y v).2
    rwa [ntres] at this
  · have n1 : adj (D.nt v) * D.nt v = 1 := by
      have := D.nt_sp v
      unfold IsGSp at this
      rw [this, one_smul]
    have n2 : adj (nb v) * nb v = 1 := by
      rw [← ntres, ← aA]
      have := congrArg (fun X : M4 A => X.map (res Λ A : A →+* ResidueField Λ)) n1
      simp only [Matrix.map_mul] at this
      rw [Matrix.map_one _ (map_zero _) (map_one _)] at this
      exact this
    have n3 : nb v * adj (nb v) = 1 := mul_eq_one_comm.1 n2
    have u1 : IsUp (adj (nb v) * rb (loc v s) * nb v) := fun i j hij => by
      rw [← hn, ← hr, ← aR, ← mR, ← mR, Matrix.map_apply, hW.flag v s i j hij, map_zero]
    have u2 : IsUp (adj (nb v) * ((x.2 v s).1 - ((h (loc v s)).1 - (rb (loc v s) * (y v).1 * rb (loc v s)⁻¹ - (y v).1)))
      * nb v) := b4 v s
    set B := (x.2 v s).1 - ((h (loc v s)).1 - (rb (loc v s) * (y v).1 * rb (loc v s)⁻¹ - (y v).1)) with hB
    have e := x2 v s
    rw [sub_eq_iff_eq_add] at e
    have hy : adj (y v).1 = -(y v).1 := (y v).2
    have e1 : f (loc v s) = D.nt v * D.t v s * adj (D.nt v) +
        T (B * rb (loc v s) - (rb (loc v s) * (y v).1 - (y v).1 * rb (loc v s))) := by
      have : B * rb (loc v s) - (rb (loc v s) * (y v).1 - (y v).1 * rb (loc v s)) =
          (x.2 v s).1 * rb (loc v s) - (h (loc v s)).1 * rb (loc v s) := by
        rw [hB, sub_mul, sub_mul, sub_mul, mul_assoc _ _ (rb (loc v s)), inv2, mul_one]
        abel
      rw [this, map_sub, hf]
      simp only
      rw [e]
      abel
    have e2 : adj (D.nt v) * f (loc v s) * D.nt v = D.t v s +
        T (adj (nb v) * (B * rb (loc v s) - (rb (loc v s) * (y v).1 - (y v).1 * rb (loc v s))) * nb v) := by
      rw [e1, mul_add, add_mul, Tl, Tr, aA, ntres]
      congr 1
      rw [← mul_assoc, ← mul_assoc, n1, one_mul, mul_assoc, n1, mul_one]
    have key : adj (D.nt v + T ((y v).1 * nb v)) * f (loc v s) * (D.nt v + T ((y v).1 * nb v)) =
        D.t v s + T ((adj (nb v) * B * nb v) * (adj (nb v) * rb (loc v s) * nb v)) := by
      rw [gA3, Ta, gk1, hy, add_mul, add_mul, mul_add, mul_add, e2, Tr (f _), TT, Tr (D.nt v),
        mul_assoc (adj (D.nt v)), Tl, Tl, fres, aA, ntres, add_zero, add_assoc, add_assoc, ← map_add, ← map_add]
      exact congrArg (fun Z => D.t v s + T Z) (alg_id _ _ _ _ _ n3)
    show IsUp (adj (D.nt v + T ((y v).1 * nb v)) * f (loc v s) * (D.nt v + T ((y v).1 * nb v)))
    rw [key]
    exact isUp_add (D.t_up v s) (Tu _ (isUp_mul u2 u1))
  · have c1 := D.rt_cont a b N
    have c2 : IsLocallyConstant fun s => Ideal.Quotient.mk (maximalIdeal A ^ N) (T ((h s).1 * rb s) a b) :=
      ((b1.comp Subtype.val).mul lc).comp fun Y => Ideal.Quotient.mk (maximalIdeal A ^ N) (T Y a b)
    have c3 := c1.sub c2
    convert c3 using 2 with s
    exact map_sub _ _ _
  · show (D.nt v + T _).map p = _
    rw [Matrix.map_add _ (map_add p), Tp, add_zero, D.nt_map]
end

section

open IsLocalRing UpperTheory.V UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem up_mul {k : Type} [CommRing k] {A B : M4 k} (hA : IsUp A) (hB : IsUp B) : IsUp (A * B) := by
  intro i j hij
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun l _ => ?_
  by_cases hl : l < i
  · rw [hA i l hl, zero_mul]
  · rw [hB l j (lt_of_lt_of_le hij (not_lt.mp hl)), mul_zero]

theorem UpperTheory.V.Ws.X1.adFacts :
    ∀ {k Γ : Type} [Field k] [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] (r : Γ →* M4 k) (h : ∀ g, ∃ x, IsGSp x (r g)), ((∀ i j, IsLocallyConstant fun g => r g i j) → IsOpen ((adSp r h).ker : Set Γ) ∧ ∀ X, IsLocallyConstant fun g => adSp r h g X) ∧ ∀ (n : M4 k) (s : Γ), IsGSp 1 n → IsUp (adj n * r s * n) → IsUp (adj n * r s⁻¹ * n) → ∀ X ∈ bor n, adSp r h s X ∈ bor n := by
  intro k Γ _ _ _ _ r h
  refine ⟨fun hloc => ?_, fun n s hn h1 h2 X hX => ?_⟩
  · have hr : IsLocallyConstant fun g => r g := by
      rw [IsLocallyConstant.iff_isOpen_fiber]
      intro M
      have hset : (fun g => r g) ⁻¹' {M} = ⋂ i, ⋂ j, (fun g => r g i j) ⁻¹' {M i j} := by
        ext g
        simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_iInter]
        exact ⟨fun e i j => by rw [e], fun e => Matrix.ext e⟩
      rw [hset]
      exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => (hloc i j).isOpen_fiber _
    refine ⟨?_, fun X => ?_⟩
    · have hker : IsOpen ((r.ker : Subgroup Γ) : Set Γ) := by
        have : ((r.ker : Subgroup Γ) : Set Γ) = (fun g => r g) ⁻¹' {1} := by
          ext g
          simp [MonoidHom.mem_ker]
        rw [this]
        exact hr.isOpen_fiber _
      refine Subgroup.isOpen_mono ?_ hker
      intro g hg
      rw [MonoidHom.mem_ker] at hg ⊢
      apply LinearMap.ext
      intro Y
      apply Subtype.ext
      have hgi : r g⁻¹ = 1 := by
        have e := r.map_mul g⁻¹ g
        rw [inv_mul_cancel, r.map_one, hg, mul_one] at e
        exact e.symm
      rw [adSp_val, hg, hgi]
      simp
    · have hinv : IsLocallyConstant fun g => r g⁻¹ := hr.comp_continuous continuous_inv
      have hprod : IsLocallyConstant fun g => r g * (X : M4 k) * r g⁻¹ :=
        IsLocallyConstant.comp₂ (IsLocallyConstant.comp₂ hr (IsLocallyConstant.const (X : M4 k)) (· * ·)) hinv (· * ·)
      refine IsLocallyConstant.desc _ (fun Y : sp4 k => (Y : M4 k)) ?_ Subtype.val_injective
      convert hprod using 1
      funext g
      simp [adSp_val]
  · have hn' : n * adj n = 1 := by
      have e : adj n * n = 1 := by simpa [IsGSp] using hn
      exact Matrix.mul_eq_one_comm_of_equiv (Equiv.refl _) |>.mp e
    show IsUp (adj n * ((adSp r h s X : sp4 k) : M4 k) * n)
    rw [adSp_val]
    have key : adj n * (r s * (X : M4 k) * r s⁻¹) * n
        = (adj n * r s * n) * (adj n * (X : M4 k) * n) * (adj n * r s⁻¹ * n) := by
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc n (adj n), hn', Matrix.one_mul, ← Matrix.mul_assoc n (adj n), hn', Matrix.one_mul]
    rw [key]
    exact up_mul (up_mul h1 hX) h2
end
