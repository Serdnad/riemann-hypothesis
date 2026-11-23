module

public import Development.AbelianVarietyTheory.Definitions.Divisors.PullHlComp
public import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.IsChart
public import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle006
public import GroundTheory.FunctionField.PlaceAbove
public import Development.AutomorphicArithmetic.RepresentationRank.RepOfRank
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle004
public import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle007
public import Development.EtaleCohomology.EtaleSheaves.Bundle003
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
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
import Mathlib.RingTheory.Henselian
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.RingTheory.SimpleRing.Principal
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
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.Topology.Sheaves.Init
public import Mathlib.RingTheory.RootsOfUnity.EnoughRootsOfUnity
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoIffBijectiveOverAlgClosed
public import Development.AbelianVarietyTheory.Definitions.Divisors.GalMapMul

@[expose] public section

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

theorem UpperTheory.nonempty_primitive_root_of_strictly_henselian :
    ∀ (q : ℕ) [NeZero q] (O : Type) [CommRing O], SH O → IsUnit (q : O) → Nonempty (Prim q O) := by
  intro q _ O _ hO hq
  obtain ⟨hH, hsep⟩ := hO
  have key : ∀ (p : Polynomial O) (x : O), IsLocalRing.residue O (p.eval x) =
      (p.map (IsLocalRing.residue O)).eval (IsLocalRing.residue O x) := by
    intro p x
    rw [Polynomial.eval_map, Polynomial.eval₂_hom]
  have hqk : ((q : ℕ) : IsLocalRing.ResidueField O) ≠ 0 := by
    have := (IsLocalRing.residue_ne_zero_iff_isUnit (q : O)).2 hq
    simpa using this
  haveI : NeZero ((q : ℕ) : IsLocalRing.ResidueField O) := ⟨hqk⟩
  have hdeg : (Polynomial.cyclotomic q (IsLocalRing.ResidueField O)).degree ≠ 0 := by
    rw [Polynomial.degree_cyclotomic]
    exact_mod_cast (Nat.totient_pos.2 (Nat.pos_of_ne_zero (NeZero.ne q))).ne'
  obtain ⟨r, hr⟩ := IsSepClosed.exists_root _ hdeg
    (Polynomial.separable_cyclotomic q (IsLocalRing.ResidueField O))
  obtain ⟨a₀, rfl⟩ := IsLocalRing.residue_surjective r
  have h1 : (Polynomial.cyclotomic q O).eval a₀ ∈ IsLocalRing.maximalIdeal O := by
    rw [← IsLocalRing.residue_eq_zero_iff, key, Polynomial.map_cyclotomic]
    exact hr
  have h2 : IsUnit ((Polynomial.derivative (Polynomial.cyclotomic q O)).eval a₀) := by
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit, key, ← Polynomial.derivative_map,
      Polynomial.map_cyclotomic]
    have h0 := (Polynomial.separable_cyclotomic q (IsLocalRing.ResidueField O)).aeval_derivative_ne_zero
      (x := IsLocalRing.residue O a₀) (by simpa [Polynomial.coe_aeval_eq_eval] using hr)
    simpa [Polynomial.coe_aeval_eq_eval] using h0
  obtain ⟨a, ha, -⟩ := HenselianLocalRing.is_henselian (Polynomial.cyclotomic q O)
    (Polynomial.cyclotomic.monic q O) a₀ h1 h2
  refine ⟨⟨a, hq, ?_⟩⟩
  rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, Polynomial.map_cyclotomic]
  exact ha
end

section

open CategoryTheory AlgebraicGeometry GlobalTheory.EtC

theorem UpperTheory.primitive_root_eq_pow_locally :
    ∀ (q : ℕ) [NeZero q] (A : Type) [CommRing A] (ξ ζ : Prim q A) (p : Ideal A) [p.IsPrime], ∃ (f : A) (a : (ZMod q)ˣ), f ∉ p ∧ ∀ (B : Type) [CommRing B] (φ : A →+* B), IsUnit (φ f) → φ ξ.1 = (φ ζ.1) ^ (a : ZMod q).val := by
  intro q _ A _ ξ ζ p _
  have hpow : ∀ η : Prim q A, η.1 ^ q = 1 := by
    intro η
    obtain ⟨g, hg⟩ := Polynomial.cyclotomic.dvd_X_pow_sub_one q ℤ
    have h1 := congrArg (Polynomial.aeval η.1) hg
    simp only [map_sub, map_pow, Polynomial.aeval_X, map_one, map_mul, η.2.2, zero_mul] at h1
    exact sub_eq_zero.mp h1
  have hq' : IsUnit ((q : ℕ) : A ⧸ p) := by
    simpa using ζ.2.1.map (Ideal.Quotient.mk p)
  haveI : NeZero ((q : ℕ) : A ⧸ p) := ⟨hq'.ne_zero⟩
  have prim : ∀ η : Prim q A, IsPrimitiveRoot (Ideal.Quotient.mk p η.1) q := by
    intro η
    have h0 : Ideal.Quotient.mk p (Polynomial.aeval η.1 (Polynomial.cyclotomic q ℤ)) = 0 := by
      rw [η.2.2, map_zero]
    rw [Polynomial.aeval_def, Polynomial.hom_eval₂] at h0
    rw [← Polynomial.isRoot_cyclotomic_iff, ← Polynomial.map_cyclotomic_int, Polynomial.IsRoot,
      Polynomial.eval_map]
    have e : (Ideal.Quotient.mk p).comp (algebraMap ℤ A) = Int.castRingHom (A ⧸ p) :=
      RingHom.ext_int _ _
    rw [e] at h0
    exact h0
  obtain ⟨k, hk, hkξ⟩ := (prim ζ).eq_pow_of_pow_eq_one (prim ξ).pow_eq_one
  have hcop : k.Coprime q := ((prim ζ).pow_iff_coprime (NeZero.pos q) k).1 (hkξ ▸ prim ξ)
  have hcq : (ζ.1 ^ k) ^ q = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, hpow ζ, one_pow]
  have hf : (∑ i ∈ Finset.range q, ξ.1 ^ i * (ζ.1 ^ k) ^ (q - 1 - i)) * (ξ.1 - ζ.1 ^ k) = 0 := by
    rw [geom_sum₂_mul, hpow ξ, hcq, sub_self]
  refine ⟨∑ i ∈ Finset.range q, ξ.1 ^ i * (ζ.1 ^ k) ^ (q - 1 - i), ZMod.unitOfCoprime k hcop, ?_, ?_⟩
  · intro hmem
    have hz := Ideal.Quotient.eq_zero_iff_mem.mpr hmem
    have hc : Ideal.Quotient.mk p (ζ.1 ^ k) = Ideal.Quotient.mk p ξ.1 := by
      rw [map_pow, hkξ]
    have hcu : IsUnit (Ideal.Quotient.mk p ξ.1) := by
      refine (Units.ofPowEqOne _ q ?_ (NeZero.ne q)).isUnit
      rw [← map_pow, hpow ξ, map_one]

    rw [map_sum] at hz
    have hsum : ∑ i ∈ Finset.range q, Ideal.Quotient.mk p (ξ.1 ^ i * (ζ.1 ^ k) ^ (q - 1 - i)) =
        ∑ i ∈ Finset.range q, (Ideal.Quotient.mk p ξ.1) ^ (q - 1) := by
      refine Finset.sum_congr rfl ?_
      intro i hi
      rw [map_mul, map_pow, map_pow, hc, ← pow_add]
      congr 1
      have := Finset.mem_range.mp hi
      omega
    rw [hsum, Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hz
    exact (hq'.mul (hcu.pow _)).ne_zero hz
  · intro B _ φ hφ
    have h1 := congrArg φ hf
    rw [map_mul, map_zero, hφ.mul_right_eq_zero, map_sub, sub_eq_zero] at h1
    rw [h1, map_pow, ZMod.coe_unitOfCoprime, ZMod.val_natCast, Nat.mod_eq_of_lt hk]
end

section

open GroundTheory.FunctionField UpperTheory.Et.Sel
open scoped TensorProduct

private theorem functionField_isAlgebraic_of_tower (k K K' : Type) [Field k] [Field K] [Field K'] [Algebra k K] [Algebra k K']
    [Algebra K K'] [IsScalarTower k K K'] [IsFunctionField k K] [IsFunctionField k K'] :
    Algebra.IsAlgebraic K K' := by
  have h := trdeg_add_eq k K (A := K')
  rw [trdeg_eq_one (k := k) (K := K), trdeg_eq_one (k := k) (K := K')] at h
  have hfin : Algebra.trdeg K K' < Cardinal.aleph0 :=
    lt_of_le_of_lt (h ▸ le_add_self) Cardinal.one_lt_aleph0
  obtain ⟨n, hn⟩ := Cardinal.lt_aleph0.mp hfin
  rw [hn] at h
  have hn0 : n = 0 := by
    have : ((1 + n : ℕ) : Cardinal) = ((1 : ℕ) : Cardinal) := by push_cast; exact h
    have := Nat.cast_injective this
    omega
  rw [← trdeg_eq_zero_iff, hn, hn0, Nat.cast_zero]

theorem UpperTheory.finite_kummerSelmer_of_finite_extension :
    ∀ (k K K' : Type) [Field k] [IsAlgClosed k] [Field K] [Field K'] [Algebra k K] [Algebra k K'] [Algebra K K'] [IsScalarTower k K K'] [IsFunctionField k K] [IsFunctionField k K'] (q : ℕ) [NeZero q], IsUnit (q : k) → FinCls q (SelAll k K' q) → FinCls q (SelAll k K q) := by
  classical
  intro k K K' _ _ _ _ _ _ _ _ _ _ q _ hq hK'
  have := functionField_isAlgebraic_of_tower k K K'
  have : Algebra.EssFiniteType k K' := essFiniteType
  have : Algebra.EssFiniteType K K' := Algebra.EssFiniteType.of_comp k K K'
  have : Module.Finite K K' := Algebra.finite_of_essFiniteType_of_isAlgebraic
  have : NeZero (q : k) := ⟨hq.ne_zero⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot k q
  obtain ⟨T0, hT0⟩ := UpperTheory.finite_kernel_powClasses_of_primitive_root K K' q
    ⟨algebraMap k K ζ, hζ.map_of_injective (algebraMap k K).injective⟩
  obtain ⟨T', hT'⟩ := hK'
  let φ : Kˣ →* K'ˣ := Units.map (algebraMap K K' : K →* K')
  have hφ : ∀ x : Kˣ, ((φ x : K'ˣ) : K') = algebraMap K K' (x : K) := fun x => rfl
  have himg : ∀ f ∈ SelAll k K q, φ f ∈ SelAll k K' q := by
    intro f hf w
    have hw := (Place.liesOver_comap w).ord_algebraMap (f : K)
    show (q : ℤ) ∣ w.ord ((φ f : K'ˣ) : K')
    rw [hφ, hw]
    exact Dvd.dvd.mul_left (hf _) _
  let g : K'ˣ → Kˣ := fun t' =>
    if h : ∃ f ∈ SelAll k K q, ∃ u : K'ˣ, φ f = t' * u ^ q then h.choose else 1
  refine ⟨Finset.image₂ (· * ·) (T'.image g) T0, ?_⟩
  intro f hf
  obtain ⟨t', ht', u, hu⟩ := hT' (φ f) (himg f hf)
  have hex : ∃ f ∈ SelAll k K q, ∃ u : K'ˣ, φ f = t' * u ^ q := ⟨f, hf, u, hu⟩
  have hg : g t' = hex.choose := dif_pos hex
  obtain ⟨_, u0, hu0⟩ := hex.choose_spec
  set f0 := hex.choose
  have hmem : f * f0⁻¹ ∈ {a : Kˣ | ∃ b : K', algebraMap K K' (a : K) = b ^ q} := by
    refine ⟨((u * u0⁻¹ : K'ˣ) : K'), ?_⟩
    rw [← hφ, map_mul, map_inv, hu, hu0]
    push_cast
    rw [mul_pow, inv_pow]
    field_simp
  obtain ⟨s, hs, w, hw⟩ := hT0 _ hmem
  refine ⟨f0 * s, Finset.mem_image₂.mpr ⟨f0, Finset.mem_image.mpr ⟨t', ht', hg⟩, s, hs, rfl⟩, w, ?_⟩
  rw [mul_assoc, ← hw, mul_comm f, mul_inv_cancel_left]
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory

theorem UpperTheory.clopRep_finite_etale_of_constant_rank :
    ∀ {S : Scheme.{0}} (G Y : Over S) (U : (Y ⊗ G).left.Opens) (n : ℕ), IsFinite G.hom → Etale G.hom → (∀ s, G.hom.finrank s = n) → UpperTheory.RepresentationRank.Rep G Y U → IsFinite Y.hom ∧ Etale Y.hom := by
  intro S G Y U n hf he hn hR
  obtain ⟨S', t, h1, h2, h3, hs⟩ := GlobalTheory.FinEt.exists_isSplitOfRank_pullback G.hom hn
  obtain ⟨Y'', U'', hR'', hf'', he''⟩ := UpperTheory.exists_clopRep_of_isSplitOfRank ((Over.pullback t).obj G) n hs
  obtain ⟨U', hR'⟩ := UpperTheory.exists_clopRep_pullback t G Y U hR
  obtain ⟨e⟩ := UpperTheory.clopRep_unique _ _ _ _ _ hR' hR''
  have hcomp : pullback.snd Y.hom t = e.hom.left ≫ Y''.hom := (Over.w e.hom).symm
  have hiso : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget S').map e.hom))
  have hqf : IsFinite (pullback.snd Y.hom t) := by
    rw [hcomp]; infer_instance
  have hqe : Etale (pullback.snd Y.hom t) := by
    rw [hcomp]; infer_instance
  have hpb := IsPullback.of_hasPullback Y.hom t
  refine ⟨UpperTheory.isFinite_of_isPullback_fpqc _ _ _ _ hpb h3 inferInstance inferInstance hqf, ?_⟩
  exact MorphismProperty.of_isPullback_of_descendsAlong (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) hpb.flip ⟨⟨h3, inferInstance⟩, inferInstance⟩ hqe
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.t_E6Cut

private theorem conn_square {R : Type} [CommRing R] {F : Shv R} {c : ℤ} {E₁ E₂ E₃ E₄ : Spc} {u : E₁ ⟶ E₂}
    {v : E₃ ⟶ E₄} {a : E₁ ⟶ E₃} {b : E₂ ⟶ E₄} (w : u ≫ b = a ≫ v) (ha : Eqv R a F) (hb : Eqv R b F)
    (hu : Conn R F c u) : Conn R F c v := by
  have key : ∀ (n : ℤ) (x : H R E₄ F n), pull R a F n (pull R v F n x) = pull R u F n (pull R b F n x) := by
    intro n x
    rw [← pull_comp, ← pull_comp, w]
  have inj : ∀ n : ℤ, Function.Injective (pull R u F n) → Function.Injective (pull R v F n) := by
    intro n hi x y h
    exact (hb n).1 (hi ((key n x).symm.trans ((congrArg _ h).trans (key n y))))
  have sur : ∀ n : ℤ, Function.Surjective (pull R u F n) → Function.Surjective (pull R v F n) := by
    intro n hs y
    obtain ⟨z, hz⟩ := hs (pull R a F n y)
    obtain ⟨x, rfl⟩ := (hb n).2 z
    exact ⟨x, (ha n).1 ((key n x).trans hz)⟩
  intro n
  exact ⟨fun hn => ⟨inj n ((hu n).1 hn).1, sur n ((hu n).1 hn).2⟩, fun hn => inj n ((hu n).2 hn)⟩

private theorem eqv_of_iso {R : Type} [CommRing R] {F : Shv R} {E E' : Spc} (e : E ≅ E') : Eqv R e.hom F := by
  intro n
  refine Function.bijective_iff_has_inverse.2 ⟨pull R e.inv F n, fun x => ?_, fun x => ?_⟩
  · rw [← pull_comp, e.inv_hom_id, pull_id]
  · rw [← pull_comp, e.hom_inv_id, pull_id]

private theorem conn_level {R : Type} [CommRing R] {F : Shv R} {c : ℤ} {P Q : PSh} (ψ : P ⟶ Q) {Z Z' : Scheme.{0}}
    (k : Z' ⟶ Z) (e : yoneda.obj Z ≅ Q) (e' : yoneda.obj Z' ≅ P) (h : e'.hom ≫ ψ = yoneda.map k ≫ e.hom)
    (hk : Conn R F c (sch.map k)) : Conn R F c (disc.map ψ) := by
  refine conn_square (u := sch.map k) (a := (disc.mapIso e').hom) (b := (disc.mapIso e).hom) ?_
    (eqv_of_iso _) (eqv_of_iso _) hk
  change disc.map (yoneda.map k) ≫ disc.map e.hom = disc.map e'.hom ≫ disc.map ψ
  rw [← Functor.map_comp, ← Functor.map_comp, h]

private theorem cech_zero {V Y : Scheme.{0}} (f : V ⟶ Y) :
    ∃ e : yoneda.obj V ≅ (cech f).obj (op (SimplexCategory.mk 0)),
      e.hom ≫ (cechAug f).app (op (SimplexCategory.mk 0)) = yoneda.map f := by
  let π₀ : Fin 1 → (yoneda.obj V ⟶ yoneda.obj Y) := fun _ => yoneda.map f
  let h : yoneda.obj V ⟶ widePullback (yoneda.obj Y) (fun _ : Fin 1 => yoneda.obj V) π₀ :=
    WidePullback.lift (yoneda.map f) (fun _ => 𝟙 _) (fun _ => Category.id_comp _)
  let k : widePullback (yoneda.obj Y) (fun _ : Fin 1 => yoneda.obj V) π₀ ⟶ yoneda.obj V :=
    WidePullback.π π₀ 0
  have hk : h ≫ k = 𝟙 _ := WidePullback.lift_π _ _ _ _ _
  have hb : h ≫ WidePullback.base π₀ = yoneda.map f := WidePullback.lift_base _ _ _ _
  have kh : k ≫ h = 𝟙 _ := by
    apply WidePullback.hom_ext
    · intro j
      obtain rfl : j = 0 := Subsingleton.elim _ _
      rw [Category.assoc, Category.id_comp]
      change k ≫ h ≫ k = k
      rw [hk, Category.comp_id]
    · rw [Category.assoc, hb, Category.id_comp]
      exact WidePullback.π_arrow π₀ 0
  exact ⟨⟨h, k, hk, kh⟩, hb⟩

set_option backward.isDefEq.respectTransparency false in
private theorem smooth_of_cover {V Y : Scheme.{0}} (f : V ⟶ Y)
    (hcov : ∃ (ι : Type) (O : ι → Scheme.{0}) (j : ∀ a, O a ⟶ V), (∀ a, IsOpenImmersion (j a)) ∧ (∀ a b, a ≠ b → Disjoint (Set.range (j a)) (Set.range (j b))) ∧ (∀ y : V, ∃ a, y ∈ Set.range (j a)) ∧ ∀ a, IsOpenImmersion (j a ≫ f)) :
    Smooth f := by
  obtain ⟨ι, O, j, hj, -, hc, hf⟩ := hcov
  let 𝒰 : V.OpenCover := Scheme.Cover.mkOfCovers ι O j (fun y => by
    obtain ⟨a, x, hx⟩ := hc y
    exact ⟨a, x, hx⟩)
  refine IsZariskiLocalAtSource.of_openCover (P := @Smooth) 𝒰 fun a => ?_
  have := hf a
  change Smooth (j a ≫ f)
  infer_instance

end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.t_E6Cut

private theorem conn_iso {R : Type} [CommRing R] (F : Shv R) (c : ℤ) {E E' : Spc} (f : E ⟶ E') [IsIso f] :
    Conn R F c f := by
  have hb : ∀ n, Function.Bijective (pull R f F n) := fun n =>
    Function.bijective_iff_has_inverse.2 ⟨pull R (inv f) F n,
      fun x => by rw [← pull_comp, IsIso.inv_hom_id, pull_id],
      fun x => by rw [← pull_comp, IsIso.hom_inv_id, pull_id]⟩
  exact fun n => ⟨fun _ => hb n, fun _ => (hb n).1⟩

private theorem conn_congr {R : Type} [CommRing R] {F : Shv R} {c : ℤ} {X : Scheme.{0}} {U U' : X.Opens} (e : U = U')
    (h : Conn R F c (sch.map U.ι)) : Conn R F c (sch.map U'.ι) := e ▸ h

private theorem conn_top {R : Type} [CommRing R] (F : Shv R) (c : ℤ) {X : Scheme.{0}} {U : X.Opens} (e : U = ⊤) :
    Conn R F c (sch.map U.ι) := by
  subst e
  haveI : IsIso (⊤ : X.Opens).ι := by
    first
      | infer_instance
      | (rw [← Scheme.topIso_hom]; infer_instance)
      | exact isIso_of_isOpenImmersion_of_opensRange_eq_top _ (by simp)
  exact conn_iso F c _

private theorem exists_good {R : Type} [CommRing R] {F : Shv R} {c : ℤ} {X : Scheme.{0}} {U : X.Opens}
    (H : ∀ x : X, x ∉ U → ∀ W : X.Opens, x ∈ W → ∃ (Y : Scheme.{0}) (j : Y ⟶ X) (_ : IsOpenImmersion j),
      x ∈ Set.range j ∧ Set.range j ⊆ (W : Set X) ∧ Conn R F c (sch.map (j ⁻¹ᵁ U).ι))
    {Y : Scheme.{0}} (j : Y ⟶ X) [IsOpenImmersion j] (y : Y) :
    ∃ (O : Scheme.{0}) (o : O ⟶ Y) (_ : IsOpenImmersion o), y ∈ Set.range o ∧
      Conn R F c (sch.map ((o ≫ j) ⁻¹ᵁ U).ι) := by
  by_cases hy : j y ∈ U
  · refine ⟨_, (j ⁻¹ᵁ U).ι, inferInstance, ?_, conn_top F c ?_⟩
    · rw [Scheme.Opens.range_ι]
      exact hy
    · rw [Scheme.Hom.comp_preimage]
      exact Scheme.Opens.ι_preimage_self _
  · obtain ⟨Y', j', hj', hx, hsub, hC⟩ := H (j y) hy j.opensRange ⟨y, rfl⟩
    have hle : Set.range j' ⊆ Set.range j := hsub
    have hfac : IsOpenImmersion.lift j j' hle ≫ j = j' := IsOpenImmersion.lift_fac j j' hle
    haveI : IsOpenImmersion (IsOpenImmersion.lift j j' hle ≫ j) := by rw [hfac]; exact hj'
    refine ⟨Y', IsOpenImmersion.lift j j' hle, IsOpenImmersion.of_comp _ j, ?_, ?_⟩
    · obtain ⟨z, hz⟩ := hx
      refine ⟨z, j.isOpenEmbedding.injective ?_⟩
      rw [← hz, ← Scheme.Hom.comp_apply, hfac]
    · rw [hfac]
      exact hC

end
end
