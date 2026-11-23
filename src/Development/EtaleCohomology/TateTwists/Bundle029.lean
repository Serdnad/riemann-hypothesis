module

public import Development.EtaleCohomology.TateTwists.Bundle019
public import Development.EtaleCohomology.TateTwists.Bundle004
public import Development.EtaleCohomology.TateTwists.Bundle005
public import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.SelmerDuality.Bundle001
public import Mathlib.RingTheory.Etale.StandardEtale
import Development.EtaleCohomology.TateTwists.Bundle013
public import Development.EtaleCohomology.TateTwists.Bundle024
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.CategoryTheory.Sites.EpiMono
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
import Mathlib.Tactic.TypeStar

@[expose] public section

section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped DirectSum TensorProduct

namespace LateralTheory.EtaleFoundations

variable {R : Type} [CommRing R]

noncomputable section

abbrev shK {I J : Cx R} (T : TensPre I J) : Cx R :=
  ((presheafToSheaf Scheme.etaleTopology.{0} (ModuleCat.{1} (ULift.{1} R))).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj T.P

abbrev tS {I J : Cx R} (T : TensPre I J) (U : Scheme.{0}) (w : ℤ) :
    Tens I J U w →ₗ[ULift.{1} R] Sec ((shK T).X w) U :=
  ((toSheafify Scheme.etaleTopology.{0} (T.P.X w)).app (op U)).hom ∘ₗ (T.e U w).toLinearMap

theorem tS_nat {I J : Cx R} (T : TensPre I J) {V U : Scheme.{0}} (g : V ⟶ U) (w : ℤ) (x : Tens I J U w) :
    Sec.res g (tS T U w x) = tS T V w (Tens.res g w x) := by
  have h1 := ConcreteCategory.congr_hom ((toSheafify Scheme.etaleTopology.{0} (T.P.X w)).naturality g.op) (T.e U w x)
  simp only [ConcreteCategory.comp_apply] at h1
  show Sec.res g (((toSheafify Scheme.etaleTopology.{0} (T.P.X w)).app (op U)).hom (T.e U w x)) =
    ((toSheafify Scheme.etaleTopology.{0} (T.P.X w)).app (op V)).hom (T.e V w (Tens.res g w x))
  rw [T.nat]
  exact h1.symm

theorem tS_d {I J : Cx R} (T : TensPre I J) (U : Scheme.{0}) (w : ℤ) (x : Tens I J U w) :
    Sec.map ((shK T).d w (w + 1)) (tS T U w x) =
      ((toSheafify Scheme.etaleTopology.{0} (T.P.X (w + 1))).app (op U)).hom
        (((T.P.d w (w + 1)).app (op U)).hom (T.e U w x)) := by
  simp only [tS, LinearMap.comp_apply, LinearEquiv.coe_coe]
  exact (ConcreteCategory.congr_hom (congrArg (fun f => NatTrans.app f (op U))
    (toSheafify_naturality Scheme.etaleTopology.{0} (T.P.d w (w + 1)))) _).symm

def shPair {I J : Cx R} (T : TensPre I J) : Pair I J (shK T) where
  mul U s t w h := (TensorProduct.mk _ _ _).compr₂ (tS T U w ∘ₗ DirectSum.lof (ULift.{1} R) {p : ℤ × ℤ // p.1 + p.2 = w} (fun p => Sec (I.X p.1.1) U ⊗[ULift.{1} R] Sec (J.X p.1.2) U) ⟨(s, t), h⟩)
  nat {V} {U} g s t w h a b := by
    change Sec.res g (tS T U w (DirectSum.of _ ⟨(s, t), h⟩ (a ⊗ₜ b))) =
      tS T V w (DirectSum.of _ ⟨(s, t), h⟩ (Sec.res g a ⊗ₜ Sec.res g b))
    rw [tS_nat, Tens.res, DirectSum.lmap_of, TensorProduct.map_tmul]
  leibniz U s t w h a b := by
    change Sec.map ((shK T).d w (w + 1))
      (tS T U w (DirectSum.of _ ⟨(s, t), h⟩ (a ⊗ₜ b))) = _
    rw [tS_d, T.leibniz]
    simp only [map_add, Units.smul_def, map_zsmul]
    rfl

theorem shPair_lift {I J : Cx R} (T : TensPre I J) (U : Scheme.{0}) (w : ℤ) :
    (shPair T).lift U w = tS T U w := by
  classical
  apply DirectSum.linearMap_ext; intro p; apply TensorProduct.ext'; intro a b
  simp [Pair.lift, shPair, DirectSum.toModule_lof]

theorem shPair_isTensor {I J : Cx R} (T : TensPre I J) : (shPair T).IsTensor := by
  refine ⟨fun U w y => ?_, fun U w x hx => ?_⟩
  · obtain ⟨S, hS, hP⟩ := tt_sheafify_locSurj (T.P.X w) U y
    refine ⟨S, hS, fun V g hg => ?_⟩
    obtain ⟨x, hx⟩ := hP V g hg
    refine ⟨(T.e V w).symm x, ?_⟩
    rw [shPair_lift]
    show ((toSheafify Scheme.etaleTopology.{0} (T.P.X w)).app (op V)).hom (T.e V w ((T.e V w).symm x)) = _
    rw [LinearEquiv.apply_symm_apply]
    exact hx
  · rw [shPair_lift] at hx
    obtain ⟨S, hS, hP⟩ := tt_sheafify_locInj (T.P.X w) U (T.e U w x) hx
    refine ⟨S, hS, fun V g hg => ?_⟩
    have h2 := hP V g hg
    simp only at h2 ⊢
    rw [← T.nat] at h2
    exact (LinearEquiv.map_eq_zero_iff _).mp h2

theorem etale_presheaf_tensor_data_sheafification_is_tensor_complex : tt_tens_sheafify := fun _ _ _ _ T => ⟨_, shPair T, shPair_isTensor T⟩

end

end LateralTheory.EtaleFoundations
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
open scoped TensorProduct DirectSum

noncomputable section
namespace LateralTheory.EtaleFoundations.GenIsoInj

theorem ulift_smul_eq {q : ℕ} [NeZero q] {M : Type*} [AddCommGroup M] [Module (ULift.{1} (ZMod q)) M]
    (r : ULift.{1} (ZMod q)) (x : M) : r • x = r.down.val • x := by
  have : r = ((r.down.val : ℕ) : ULift.{1} (ZMod q)) := by
    apply ULift.ext; simp only [ULift.down_natCast, ZMod.natCast_zmod_val]
  conv_lhs => rw [this]
  rw [Nat.cast_smul_eq_nsmul]

theorem q_smul {q : ℕ} [NeZero q] {M : Type*} [AddCommGroup M] [Module (ULift.{1} (ZMod q)) M]
    (c : ℕ) (hc : q ∣ c) (x : M) : c • x = 0 := by
  rw [← Nat.cast_smul_eq_nsmul (ULift.{1} (ZMod q))]
  have : ((c : ℕ) : ULift.{1} (ZMod q)) = 0 := by
    ext; simpa using (ZMod.natCast_eq_zero_iff c q).2 hc
  rw [this, zero_smul]

theorem exists_functional {q : ℕ} [NeZero q] {M : Type 1} [AddCommGroup M] [Module (ULift.{1} (ZMod q)) M]
    (g : M) (hg : ∀ c : ℕ, c • g = 0 → q ∣ c) :
    ∃ F : M →ₗ[ULift.{1} (ZMod q)] ULift.{1} (ZMod q), F g = 1 := by
  letI : Module (ZMod q) M :=
    Module.compHom M (ULift.ringEquiv.symm : ZMod q ≃+* ULift.{1} (ZMod q)).toRingHom
  have hsm : ∀ (r : ZMod q) (x : M), r • x = (ULift.up r : ULift.{1} (ZMod q)) • x := fun r x => rfl
  let f : ZMod q →ₗ[ZMod q] M := LinearMap.toSpanSingleton (ZMod q) M g
  have hf : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro r hr
    have h1 : r.val • g = 0 := by
      have h2 : (ULift.up r : ULift.{1} (ZMod q)) • g = 0 := hr
      have h4 := ulift_smul_eq (M := M) (ULift.up r : ULift.{1} (ZMod q)) g
      exact h4.symm.trans h2
    have h3 := hg _ h1
    rw [← ZMod.natCast_zmod_val r]
    exact (ZMod.natCast_eq_zero_iff _ _).2 h3
  obtain ⟨h, hh⟩ := (KStar.Selmer.zmod_baer (N := q)).extension_property f hf LinearMap.id
  refine ⟨{ toFun := fun x => ULift.up (h x), map_add' := fun x y => by ext; simp,
             map_smul' := fun r x => ?_ }, ?_⟩
  · change ULift.up (h (r.down • x)) = r • ULift.up (h x)
    rw [h.map_smul]
    ext; simp [smul_eq_mul]
  · have := LinearMap.congr_fun hh 1
    simp only [LinearMap.comp_apply, f, LinearMap.toSpanSingleton_apply, one_smul, LinearMap.id_apply] at this
    ext; simpa using this

theorem dvd_of_tmul {q : ℕ} [NeZero q] {M N : Type 1} [AddCommGroup M] [Module (ULift.{1} (ZMod q)) M]
    [AddCommGroup N] [Module (ULift.{1} (ZMod q)) N] (g : M) (g' : N)
    (hg : ∀ c : ℕ, c • g = 0 → q ∣ c) (hg' : ∀ c : ℕ, c • g' = 0 → q ∣ c) (c : ℕ)
    (h : c • (g ⊗ₜ[ULift.{1} (ZMod q)] g') = 0) : q ∣ c := by
  obtain ⟨F, hF⟩ := exists_functional g hg
  obtain ⟨F', hF'⟩ := exists_functional g' hg'
  let L := TensorProduct.lift ((LinearMap.mul (ULift.{1} (ZMod q)) (ULift.{1} (ZMod q))).compl₂ F' ∘ₗ F)
  have := congrArg L h
  simp only [map_nsmul, L, TensorProduct.lift.tmul, LinearMap.comp_apply, LinearMap.compl₂_apply,
    LinearMap.mul_apply', hF, hF', mul_one, map_zero, nsmul_eq_mul] at this
  have h2 := congrArg ULift.down this
  simp at h2
  exact (ZMod.natCast_eq_zero_iff _ _).1 h2

end LateralTheory.EtaleFoundations.GenIsoInj

namespace LateralTheory.EtaleFoundations.GenIsoInj

theorem res_comp {R : Type} [CommRing R] {F : Shv R} {W V U : Scheme.{0}} (h : W ⟶ V) (g : V ⟶ U)
    (x : Sec F U) : Sec.res (h ≫ g) x = Sec.res h (Sec.res g x) := by
  simp [Sec.res]

theorem sm_nsmul {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} (c : ℕ) (x : Sec F U) :
    Sec.map φ (c • x) = c • Sec.map φ x := map_nsmul _ _ _
theorem sm_zero {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} :
    Sec.map φ (0 : Sec F U) = 0 := map_zero _
theorem sr_nsmul {R : Type} [CommRing R] {F : Shv R} {V U : Scheme.{0}} (g : V ⟶ U) (c : ℕ) (x : Sec F U) :
    Sec.res g (c • x) = c • Sec.res g x := map_nsmul _ _ _
theorem sr_zero {R : Type} [CommRing R] {F : Shv R} {V U : Scheme.{0}} (g : V ⟶ U) :
    Sec.res g (0 : Sec F U) = 0 := map_zero _

theorem sgl_smul_eq_zero {q : ℕ} {F : Shv (ZMod q)} {U : Scheme.{0}} (c : ℕ) (x : Sec F U)
    (h : c • Sec.map (sglι F) x = 0) : c • x = 0 := by
  let ψ : (sgl F).X 0 ⟶ F := (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 F).hom
  have hψ : sglι F ≫ ψ = 𝟙 F := (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 F).inv_hom_id
  have e : ∀ y : Sec F U, Sec.map ψ (Sec.map (sglι F) y) = y := fun y => by
    rw [TwMulPf.sec_map_comp, hψ, TwMulPf.sec_map_id]
  have h' : Sec.map (sglι F) (c • x) = Sec.map (sglι F) 0 := by
    rw [show Sec.map (sglι F) (c • x) = c • Sec.map (sglι F) x from map_nsmul _ c x, h]
    exact (map_zero _).symm
  have := congrArg (Sec.map ψ) h'
  rwa [e, e] at this

end LateralTheory.EtaleFoundations.GenIsoInj


open LateralTheory.EtaleFoundations.GenIsoInj LateralTheory.EtaleFoundations.TwMulPf in
theorem LateralTheory.EtaleFoundations.etale_tate_twist_generator_map_injective_of_sections_glue (hts : LateralTheory.EtaleFoundations.EtaleTateTwistSectionsLocallyGenerated)
    (hlb : LateralTheory.EtaleFoundations.EtaleLocalPropertyBasicClosure) (hsg : LateralTheory.EtaleFoundations.EtaleSheafSectionsSeparatedAndGlue) :
    LateralTheory.EtaleFoundations.EtaleTateTwistGeneratorMapSectionsInjective := by
  classical
  intro q _ i j k T μ hμ hk φ hφ U a ha
  have nt : ∀ (l : ℤ) (W : Scheme.{0}) [Nonempty W] (ζ : Prim q Γ(W, ⊤)) (c : ℕ),
      c • Sec.map (sglι (tw q l)) (twGen l ζ) = 0 → q ∣ c :=
    fun l W _ ζ c h => (hts q l).2.2.1 W ζ c (LateralTheory.EtaleFoundations.GenIsoInj.sgl_smul_eq_zero c _ h)
  refine hlb.2.2.2.2.1 U _ (hlb.2.1 U _ _ ((hts q k).1 U a) ?_)
  rintro V g (h0 | ⟨ζ, c, hc⟩)
  · exact hlb.1 V _ fun W h => by rw [LateralTheory.EtaleFoundations.GenIsoInj.res_comp, h0, LateralTheory.EtaleFoundations.GenIsoInj.sr_zero]
  · have h1 : c • μ.mul V 0 0 0 (add_zero 0) (Sec.map (sglι _) (twGen i ζ))
        (Sec.map (sglι _) (twGen j ζ)) = 0 := by
      rw [← hφ V ζ, ← LateralTheory.EtaleFoundations.GenIsoInj.sm_nsmul, ← LateralTheory.EtaleFoundations.GenIsoInj.sm_nsmul, ← hc, ← LateralTheory.EtaleFoundations.TwMulPf.sec_res_map, ha, LateralTheory.EtaleFoundations.GenIsoInj.sr_zero, LateralTheory.EtaleFoundations.GenIsoInj.sm_zero]
    let x : Tens (sgl (tw q i)) (sgl (tw q j)) V 0 :=
      DirectSum.lof (ULift.{1} (ZMod q)) {p : ℤ × ℤ // p.1 + p.2 = 0}
        (fun p => Sec ((sgl (tw q i)).X p.1.1) V ⊗[ULift.{1} (ZMod q)] Sec ((sgl (tw q j)).X p.1.2) V)
        ⟨(0, 0), rfl⟩ (c • (Sec.map (sglι _) (twGen i ζ) ⊗ₜ Sec.map (sglι _) (twGen j ζ)))
    have hx : μ.lift V 0 x = 0 := by
      simp only [x, Pair.lift, DirectSum.toModule_lof, map_nsmul, TensorProduct.lift.tmul]
      exact h1
    refine hlb.2.1 V _ _ (hμ.2 V 0 x hx) fun W h hW => ?_
    have hW' : c • (Sec.res h (Sec.map (sglι _) (twGen i ζ)) ⊗ₜ[ULift.{1} (ZMod q)]
        Sec.res h (Sec.map (sglι _) (twGen j ζ))) = 0 := by
      have := congrArg (DirectSum.component (ULift.{1} (ZMod q)) {p : ℤ × ℤ // p.1 + p.2 = 0}
        (fun p => Sec ((sgl (tw q i)).X p.1.1) W ⊗[ULift.{1} (ZMod q)] Sec ((sgl (tw q j)).X p.1.2) W)
        ⟨(0, 0), rfl⟩) hW
      simpa [x, Tens.res, DirectSum.component.lof_self] using this
    show Sec.res (h ≫ g) a = 0
    rw [LateralTheory.EtaleFoundations.GenIsoInj.res_comp, hc, LateralTheory.EtaleFoundations.GenIsoInj.sr_nsmul]
    by_cases hne : Nonempty W
    · rw [LateralTheory.EtaleFoundations.TwMulPf.sec_res_map, LateralTheory.EtaleFoundations.TwMulPf.sec_res_map, (hts q i).2.2.2.1, (hts q j).2.2.2.1] at hW'
      exact LateralTheory.EtaleFoundations.GenIsoInj.q_smul c (LateralTheory.EtaleFoundations.GenIsoInj.dvd_of_tmul _ _ (nt i W _) (nt j W _) c hW') _
    · have : IsEmpty W := not_nonempty_iff.1 hne
      exact (hsg (ZMod q) (tw q k) W).1 _ _ (hlb.2.2.2.2.2.2 W _)
end
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC Polynomial

namespace LateralTheory.EtaleFoundations.PrimLocExPf

noncomputable abbrev cyc (A : Type) [CommRing A] (q : ℕ) : A[X] := (cyclotomic q ℤ).map (Int.castRingHom A)

theorem cyc_monic (A : Type) [CommRing A] (q : ℕ) : (cyc A q).Monic :=
  (cyclotomic.monic q ℤ).map _

theorem cyc_cond (A : Type) [CommRing A] (q : ℕ) [NeZero q] (hq : IsUnit (q : A)) :
    ∃ p₁ p₂ : A[X], derivative (cyc A q) * p₁ + cyc A q * p₂ = 1 := by
  obtain ⟨h, hh⟩ := cyclotomic.dvd_X_pow_sub_one q ℤ
  have hh' : (X ^ q - 1 : A[X]) = cyc A q * h.map (Int.castRingHom A) := by
    have := congrArg (Polynomial.map (Int.castRingHom A)) hh
    simpa [Polynomial.map_mul] using this
  set H := h.map (Int.castRingHom A)
  have hd : (C (q : A)) * X ^ (q - 1) = derivative (cyc A q) * H + cyc A q * derivative H := by
    have := congrArg derivative hh'
    rw [derivative_mul] at this
    rw [← this]; simp [derivative_X_pow]
  obtain ⟨u, hu⟩ := hq
  refine ⟨C (↑u⁻¹ : A) * X * H, C (↑u⁻¹ : A) * (X * derivative H - C (q : A) * H), ?_⟩
  have hX : X * X ^ (q - 1) = (X ^ q : A[X]) := by
    rw [← pow_succ', Nat.sub_add_cancel (Nat.pos_of_neZero q)]
  have key : C (q : A) * X ^ q = X * (derivative (cyc A q) * H + cyc A q * derivative H) := by
    rw [← hd, ← hX]; ring
  have hXq : (X ^ q : A[X]) = cyc A q * H + 1 := by rw [← hh']; ring
  have hCu : C (↑u⁻¹ : A) * C (q : A) = 1 := by rw [← C_mul, ← hu, Units.inv_mul, C_1]
  calc derivative (cyc A q) * (C (↑u⁻¹ : A) * X * H) + cyc A q * (C (↑u⁻¹ : A) * (X * derivative H - C (q : A) * H))
      = C (↑u⁻¹ : A) * (X * (derivative (cyc A q) * H + cyc A q * derivative H) - C (q : A) * (cyc A q * H)) := by ring
    _ = C (↑u⁻¹ : A) * (C (q : A) * X ^ q - C (q : A) * (cyc A q * H)) := by rw [key]
    _ = C (↑u⁻¹ : A) * C (q : A) := by rw [hXq]; ring
    _ = 1 := hCu

noncomputable def pair (A : Type) [CommRing A] (q : ℕ) [NeZero q] (hq : IsUnit (q : A)) :
    StandardEtalePair A where
  f := cyc A q
  monic_f := cyc_monic A q
  g := 1
  cond := by obtain ⟨p₁, p₂, h⟩ := cyc_cond A q hq; exact ⟨p₁, p₂, 0, by simpa using h⟩

theorem hasMap_root (A : Type) [CommRing A] (q : ℕ) [NeZero q] (hq : IsUnit (q : A)) :
    (pair A q hq).HasMap (AdjoinRoot.root (cyc A q)) := by
  refine ⟨?_, ?_⟩
  · have : (pair A q hq).f = cyc A q := rfl
    rw [this, AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]
  · have : (pair A q hq).g = 1 := rfl
    rw [this, map_one]; exact isUnit_one

noncomputable def equivB (A : Type) [CommRing A] (q : ℕ) [NeZero q] (hq : IsUnit (q : A)) :
    (pair A q hq).Ring ≃ₐ[A] AdjoinRoot (cyc A q) := by
  refine AlgEquiv.ofAlgHom ((pair A q hq).lift (AdjoinRoot.root (cyc A q)) (hasMap_root A q hq))
    (AdjoinRoot.liftAlgHom (cyc A q) (Algebra.ofId A _) (pair A q hq).X
      (pair A q hq).hasMap_X.1) ?_ ?_
  · apply AdjoinRoot.algHom_ext
    simp only [AlgHom.coe_comp, Function.comp_apply, AlgHom.coe_id, id_eq]
    exact (congrArg ((pair A q hq).lift _ (hasMap_root A q hq)) (AdjoinRoot.liftAlgHom_root _ _ _ _)).trans
      (StandardEtalePair.lift_X _ _ _)
  · apply StandardEtalePair.hom_ext
    simp only [AlgHom.coe_comp, Function.comp_apply, AlgHom.coe_id, id_eq]
    exact (congrArg (AdjoinRoot.liftAlgHom (cyc A q) (Algebra.ofId A _) (pair A q hq).X
      (pair A q hq).hasMap_X.1) (StandardEtalePair.lift_X _ _ _)).trans (AdjoinRoot.liftAlgHom_root _ _ _ _)

theorem etaleB (A : Type) [CommRing A] (q : ℕ) [NeZero q] (hq : IsUnit (q : A)) :
    Algebra.Etale A (AdjoinRoot (cyc A q)) := by
  haveI : Algebra.IsStandardEtale A (AdjoinRoot (cyc A q)) :=
    Algebra.IsStandardEtale.of_equiv (equivB A q hq)
  infer_instance

theorem surjB (A : Type) [CommRing A] (q : ℕ) [NeZero q] :
    Function.Surjective (PrimeSpectrum.comap (algebraMap A (AdjoinRoot (cyc A q)))) := by
  intro p
  haveI : Nontrivial A := ⟨⟨0, 1, fun h => p.2.ne_top (by rw [Ideal.eq_top_iff_one, ← h]; exact p.1.zero_mem)⟩⟩
  have hm := cyc_monic A q
  have hdeg : 0 < (cyc A q).natDegree := by
    show 0 < ((cyclotomic q ℤ).map (Int.castRingHom A)).natDegree
    rw [(cyclotomic.monic q ℤ).natDegree_map, natDegree_cyclotomic]; exact Nat.totient_pos.mpr (Nat.pos_of_neZero q)
  haveI : Module.Free A (AdjoinRoot (cyc A q)) := .of_basis (AdjoinRoot.powerBasis' hm).basis
  haveI : Nontrivial (AdjoinRoot (cyc A q)) := by
    have hne : (AdjoinRoot.powerBasis' hm).basis ⟨0, hdeg⟩ ≠ 0 := (AdjoinRoot.powerBasis' hm).basis.ne_zero _
    exact nontrivial_of_ne _ _ hne
  exact PrimeSpectrum.comap_surjective_of_faithfullyFlat p

end LateralTheory.EtaleFoundations.PrimLocExPf

namespace LateralTheory.EtaleFoundations.PrimLocExPf

def primMap {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) (q : ℕ) (ζ : Prim q R) : Prim q S :=
  ⟨φ ζ.1, by simpa using ζ.2.1.map φ, by
    have h := Polynomial.aeval_algHom_apply φ.toIntAlgHom ζ.1 (Polynomial.cyclotomic q ℤ)
    rw [ζ.2.2, map_zero] at h
    simpa using h⟩

theorem root_prim (A : Type) [CommRing A] (q : ℕ) (hq : IsUnit (q : A)) :
    IsUnit (q : AdjoinRoot (cyc A q)) ∧
      aeval (AdjoinRoot.root (cyc A q)) (cyclotomic q ℤ) = 0 := by
  refine ⟨by simpa using hq.map (algebraMap A (AdjoinRoot (cyc A q))), ?_⟩
  have : cyc A q = (cyclotomic q ℤ).map (algebraMap ℤ A) := by rw [algebraMap_int_eq]
  rw [← Polynomial.aeval_map_algebraMap A, ← this, AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]

theorem mono_prim (q : ℕ) {U : Scheme.{0}} : ∀ (V W : Scheme.{0}) (g : V ⟶ U) (k : W ⟶ V),
    Nonempty (Prim q Γ(V, ⊤)) → Nonempty (Prim q Γ(W, ⊤)) := by
  rintro V W g k ⟨ζ⟩
  exact ⟨primMap k.appTop.hom q ζ⟩

end LateralTheory.EtaleFoundations.PrimLocExPf

namespace LateralTheory.EtaleFoundations

open PrimLocExPf in
theorem etale_locally_exists_primitive_root_of_unity_of_invertible_order : EtaleLocallyExistsPrimitiveRootOfUnityOfInvertibleOrder := by
  intro q _ U hq
  rw [etale_sheaf_section_locally_iff_of_presheaf_facts U (fun V _ => Nonempty (Prim q Γ(V, ⊤))) (mono_prim q)]
  intro y
  obtain ⟨W, hWa, hyW, -⟩ : ∃ W : U.Opens, IsAffineOpen W ∧ y ∈ W ∧ W ≤ ⊤ :=
    (TopologicalSpace.Opens.isBasis_iff_nbhd.mp U.isBasis_affineOpens) (show y ∈ (⊤ : U.Opens) from trivial)
  have hqA : IsUnit (q : Γ(U, W)) := by
    simpa using hq.map (U.presheaf.map (homOfLE le_top).op).hom
  have hE := etaleB Γ(U, W) q hqA
  let φ : Γ(U, W) ⟶ CommRingCat.of (AdjoinRoot (cyc Γ(U, W) q)) := CommRingCat.ofHom (algebraMap _ _)
  have hφ : Etale (Spec.map φ) :=
    HasRingHomProperty.Spec_iff.mpr
      ((RingHom.etale_algebraMap (R := Γ(U, W)) (S := AdjoinRoot (cyc Γ(U, W) q))).mpr hE)
  refine ⟨_, Spec.map φ ≫ hWa.fromSpec, inferInstance, inferInstance, ?_, ?_⟩
  · have hy : y ∈ Set.range hWa.fromSpec := by rw [hWa.range_fromSpec]; exact hyW
    obtain ⟨p, rfl⟩ := hy
    obtain ⟨r, hr⟩ := surjB Γ(U, W) q p
    exact ⟨r, congrArg hWa.fromSpec hr⟩
  · have h := root_prim Γ(U, W) q hqA
    exact ⟨primMap (Scheme.ΓSpecIso (CommRingCat.of (AdjoinRoot (cyc Γ(U, W) q)))).inv.hom q
      ⟨AdjoinRoot.root _, h.1, h.2⟩⟩

end LateralTheory.EtaleFoundations
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations.acycIffPf

variable {R : Type} [CommRing R]

abbrev ev (U : Scheme.{0}) : Shv R ⥤ ModuleCat.{1} (ULift.{1} R) :=
  sheafToPresheaf Scheme.etaleTopology.{0} (ModuleCat.{1} (ULift.{1} R)) ⋙ (evaluation _ _).obj (op U)

theorem app_comp {F G H : Shv R} (φ : F ⟶ G) (ψ : G ⟶ H) (U : Scheme.{0}) (x : Sec F U) :
    Sec.map (φ ≫ ψ) x = Sec.map ψ (Sec.map φ x) := rfl

theorem map_res {F G : Shv R} (φ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U) (x : Sec F U) :
    Sec.map φ (Sec.res g x) = Sec.res g (Sec.map φ x) :=
  congrArg (fun f => f.hom x) (φ.hom.naturality g.op)

theorem iCycles_inj (S : ShortComplex (Shv R)) (U : Scheme.{0}) :
    Function.Injective (Sec.map S.iCycles (U := U)) := by
  have : Mono ((ev U).map S.iCycles) := inferInstance
  exact (ModuleCat.mono_iff_injective _).1 this

theorem iCycles_surj (S : ShortComplex (Shv R)) (U : Scheme.{0}) (z : Sec S.X₂ U) (hz : Sec.map S.g z = 0) :
    ∃ c : Sec S.cycles U, Sec.map S.iCycles c = z := by
  let S' : ShortComplex (Shv R) := ShortComplex.mk S.iCycles S.g S.iCycles_g
  have hS' : S'.Exact := S'.exact_of_f_is_kernel S.cyclesIsKernel
  have hE : (S'.map (ev U)).Exact := hS'.map_of_mono_of_preservesKernel (ev U) (inferInstanceAs (Mono S.iCycles)) inferInstance
  exact (ShortComplex.moduleCat_exact_iff _).1 hE z hz

theorem exact_iff (S : ShortComplex (Shv R)) : S.Exact ↔
    ∀ (U : Scheme.{0}) (z : Sec S.X₂ U), Sec.map S.g z = 0 →
      Loc U fun V g => ∃ y : Sec S.X₁ V, Sec.map S.f y = Sec.res g z := by
  rw [S.exact_iff_epi_toCycles, ← Sheaf.isLocallySurjective_iff_epi' _ S.toCycles]
  constructor
  · intro h U z hz
    obtain ⟨c, rfl⟩ := iCycles_surj S U z hz
    refine ⟨_, Presheaf.imageSieve_mem Scheme.etaleTopology.{0} S.toCycles.hom (U := op U) c, ?_⟩
    rintro V g ⟨t, ht⟩
    refine ⟨t, ?_⟩
    have h1 : Sec.map S.f t = Sec.map S.iCycles (Sec.map S.toCycles t) := by
      rw [← app_comp, S.toCycles_i]
    rw [h1, ← map_res]
    exact congrArg _ ht
  · intro h
    constructor
    intro U c
    obtain ⟨Sv, hSv, hP⟩ := h U (Sec.map S.iCycles c) (by rw [← app_comp, S.iCycles_g]; rfl)
    refine Scheme.etaleTopology.{0}.superset_covering ?_ hSv
    intro V g hg
    obtain ⟨y, hy⟩ := hP V g hg
    refine ⟨y, iCycles_inj S V ?_⟩
    change Sec.map S.iCycles (Sec.map S.toCycles y) = Sec.map S.iCycles (Sec.res g c)
    rw [← app_comp, S.toCycles_i, hy, map_res]

end LateralTheory.EtaleFoundations.acycIffPf

open LateralTheory.EtaleFoundations.acycIffPf in
theorem LateralTheory.EtaleFoundations.acyc.acycIff_of : LateralTheory.EtaleFoundations.acyc.acycIff := by
  intro R _ C
  unfold LateralTheory.EtaleFoundations.acyc.LocAcyc
  constructor
  · intro h U n z hz
    have := (HomologicalComplex.exactAt_iff' C (n - 1) n (n + 1) (by simp) (by simp)).1 (h n)
    exact (exact_iff _).1 this U z hz
  · intro h n
    rw [HomologicalComplex.exactAt_iff' C (n - 1) n (n + 1) (by simp) (by simp)]
    exact (exact_iff _).2 fun U z hz => h U n z hz
end
