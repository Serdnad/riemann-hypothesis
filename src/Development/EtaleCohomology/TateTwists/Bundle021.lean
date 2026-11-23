module

public import Development.EtaleCohomology.TateTwists.Bundle010
public import Development.EtaleCohomology.TateTwists.Bundle015
public import Development.EtaleCohomology.TateTwists.Bundle011
public import Development.EtaleCohomology.TateTwists.Bundle016
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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

@[expose] public section

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section
namespace LateralTheory.EtaleFoundations.TensExPf
open LateralTheory.EtaleFoundations.TwMulPf
open scoped TensorProduct DirectSum

variable {R : Type} [CommRing R]

theorem sec_map_zero {F G : Shv R} {U : Scheme.{0}} (x : Sec F U) : Sec.map (0 : F ⟶ G) x = 0 := by
  rfl

theorem sec_zero_of_isZero {Z : Shv R} (hZ : IsZero Z) {U : Scheme.{0}} (y : Sec Z U) : y = 0 := by
  have h : Sec.map (𝟙 Z) y = Sec.map 0 y := by rw [hZ.eq_of_src (𝟙 Z) 0]
  rw [sec_map_id, sec_map_zero] at h
  exact h

theorem isZero_sglX (F : Shv R) {w : ℤ} (hw : w ≠ 0) : IsZero ((sgl F).X w) :=
  HomologicalComplex.isZero_single_obj_X _ _ _ _ hw

theorem sgl_d (F : Shv R) (a : ℤ) : (sgl F).d a (a + 1) = 0 := by
  by_cases ha : a = 0
  · exact (isZero_sglX F (by omega)).eq_of_tgt _ _
  · exact (isZero_sglX F ha).eq_of_src _ _

def eIso (K : Cx R) (w : ℤ) (h : w = 0) : K.X w ≅ (sgl (K.X 0)).X w :=
  K.XIsoOfEq h ≪≫ (HomologicalComplex.singleObjXIsoOfEq (ComplexShape.up ℤ) 0 (K.X 0) w h).symm

def e (K : Cx R) (w : ℤ) : K.X w ⟶ (sgl (K.X 0)).X w :=
  if h : w = 0 then (eIso K w h).hom else 0

theorem e_pos (K : Cx R) {w : ℤ} (h : w = 0) : e K w = (eIso K w h).hom := dif_pos h

def μ {A B : Shv R} {K : Cx R} (τ : Pair (sgl A) (sgl B) K) : Pair (sgl A) (sgl B) (sgl (K.X 0)) where
  mul U s t w h := (τ.mul U s t w h).compr₂ (secL (e K w) U)
  nat g s t w h a b := by
    change Sec.res g (Sec.map (e K w) _) = Sec.map (e K w) _
    rw [sec_res_map, τ.nat]
  leibniz U s t w h a b := by
    change Sec.map ((sgl (K.X 0)).d w (w + 1)) _ =
      Sec.map (e K (w + 1)) (τ.mul U (s + 1) t (w + 1) _ (Sec.map ((sgl A).d s (s + 1)) a) b) +
        s.negOnePow • Sec.map (e K (w + 1)) (τ.mul U s (t + 1) (w + 1) _ a (Sec.map ((sgl B).d t (t + 1)) b))
    simp only [sgl_d, sec_map_zero, map_zero, LinearMap.zero_apply, smul_zero, add_zero]

theorem μ_lift {A B : Shv R} {K : Cx R} (τ : Pair (sgl A) (sgl B) K) (U : Scheme.{0}) (w : ℤ)
    (x : Tens (sgl A) (sgl B) U w) : (μ τ).lift U w x = Sec.map (e K w) (τ.lift U w x) := by
  classical
  change _ = secL (e K w) U (τ.lift U w x)
  rw [← LinearMap.comp_apply]
  congr 1
  refine DirectSum.linearMap_ext _ fun p => TensorProduct.ext' fun a b => ?_
  simp [Pair.lift, μ]

theorem tens_summand_zero {A B : Shv R} {a b : ℤ} (hab : a ≠ 0 ∨ b ≠ 0) {U : Scheme.{0}}
    (z : Sec ((sgl A).X a) U ⊗[ULift.{1} R] Sec ((sgl B).X b) U) : z = 0 := by
  refine TensorProduct.induction_on (motive := fun z => z = 0) z rfl (fun u v => ?_) (fun x y hx hy => by rw [hx, hy, add_zero])
  rcases hab with h | h
  · rw [sec_zero_of_isZero (isZero_sglX A h) u, TensorProduct.zero_tmul]
  · rw [sec_zero_of_isZero (isZero_sglX B h) v, TensorProduct.tmul_zero]

theorem tens_zero {A B : Shv R} {U : Scheme.{0}} {w : ℤ} (hw : w ≠ 0) (x : Tens (sgl A) (sgl B) U w) : x = 0 := by
  refine DirectSum.ext fun p => ?_
  rw [DirectSum.zero_apply]
  refine tens_summand_zero ?_ _
  have := p.2
  by_contra hc
  push Not at hc
  omega

theorem μ_isTensor {A B : Shv R} {K : Cx R} (τ : Pair (sgl A) (sgl B) K) (hτ : τ.IsTensor) :
    (μ τ).IsTensor := by
  refine ⟨fun U w y => ?_, fun U w x hx => ?_⟩
  · by_cases hw : w = 0
    · refine loc_mono (hτ.1 U w (Sec.map (eIso K w hw).inv y)) fun V g ⟨x, hx⟩ => ⟨x, ?_⟩
      rw [μ_lift, hx, ← sec_res_map, e_pos K hw, sec_map_comp, Iso.inv_hom_id, sec_map_id]
    · refine ⟨⊤, Scheme.etaleTopology.top_mem U, fun V g _ => ⟨0, ?_⟩⟩
      rw [map_zero]
      exact (sec_zero_of_isZero (isZero_sglX _ hw) _).symm
  · by_cases hw : w = 0
    · refine hτ.2 U w x ?_
      rw [μ_lift, e_pos K hw] at hx
      have := congrArg (Sec.map (eIso K w hw).inv) hx
      rw [sec_map_comp, Iso.hom_inv_id, sec_map_id] at this
      rw [this]
      exact map_zero _
    · obtain rfl := tens_zero hw x
      exact ⟨⊤, Scheme.etaleTopology.top_mem U, fun _ _ _ => map_zero _⟩

end LateralTheory.EtaleFoundations.TensExPf

open LateralTheory.EtaleFoundations.TensExPf in
theorem LateralTheory.EtaleFoundations.etale_tate_twist_multiplication_tensor_exists_of_complex_tensor_exists
    (hex : ∀ (R : Type) [CommRing R] (I J : Cx R), ∃ (K : Cx R) (τ : Pair I J K), τ.IsTensor) :
    LateralTheory.EtaleFoundations.EtaleTateTwistTensorPairingExists := by
  intro q _ i j
  obtain ⟨K, τ, hτ⟩ := hex (ZMod q) (sgl (tw q i)) (sgl (tw q j))
  exact ⟨K.X 0, μ τ, μ_isTensor τ hτ⟩
end
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
open scoped TensorProduct

namespace LateralTheory.EtaleFoundations.TwSide

def tw_mul : Prop := ∀ (q : ℕ) [NeZero q] (i j k : ℤ), i + j = k → ∃ μ : Pair (sgl (tw q i)) (sgl (tw q j)) (sgl (tw q k)), μ.IsTensor ∧ ∀ (U : Scheme.{0}) (ζ : Prim q Γ(U, ⊤)), μ.mul U 0 0 0 (add_zero 0) (Sec.map (sglι _) (twGen i ζ)) (Sec.map (sglι _) (twGen j ζ)) = Sec.map (sglι _) (twGen k ζ)

def tw_flat : Prop := ∀ (q : ℕ) [NeZero q] (i : ℤ), FlatS (tw q i)

def flip_ex : Prop := ∀ (R : Type) [CommRing R] {I J K : Cx R} (μ : Pair I J K), ∃ ν : Pair J I K, μ.IsFlip ν ∧ ν.IsFlip μ ∧ (μ.IsTensor → ν.IsTensor)

def tens_qis : Prop := ∀ (R : Type) [CommRing R] {I I' J T T' : Cx R} [I.IsStrictlyGE 0] [I'.IsStrictlyGE 0] [J.IsStrictlyGE 0] (τ : Pair I J T) (τ' : Pair I' J T'), τ.IsTensor → τ'.IsTensor → (∀ t, FlatS (J.X t)) → ∀ (f : I ⟶ I') [QuasiIso f] (u : T ⟶ T'), τ.Compat τ' f (𝟙 J) u → QuasiIso u

variable {R : Type} [CommRing R]

theorem sec_sub {F : Shv R} (h : IsZero F) (U : Scheme.{0}) : Subsingleton (Sec F U) := by
  constructor; intro a b
  have : 𝟙 F = 0 := h.eq_of_src _ _
  have ha : a = Sec.map (𝟙 F) a := rfl
  have hb : b = Sec.map (𝟙 F) b := rfl
  rw [ha, hb, this]; rfl

theorem flat_zero {F : Shv R} (h : IsZero F) : FlatS F := by
  refine ⟨F.obj, 𝟙 _, fun U y => LateralTheory.EtaleFoundations.TensFam.loc_top fun V g => ⟨Sec.res g y, rfl⟩,
    fun U x _ => LateralTheory.EtaleFoundations.TensFam.loc_top fun V g => @Subsingleton.elim _ (sec_sub h V) _ _, fun U _ => ?_⟩
  haveI := sec_sub h U
  infer_instance

open ZeroObject in
theorem flat_sgl {F : Shv R} (hF : FlatS F) (t : ℤ) : FlatS ((sgl F).X t) := by
  by_cases ht : t = 0
  · subst ht
    exact (show FlatS (if (0:ℤ) = 0 then F else 0) by rw [if_pos rfl]; exact hF)
  · exact flat_zero (HomologicalComplex.isZero_single_obj_X _ _ _ _ ht)

theorem sgl_sub (F : Shv R) {t : ℤ} (ht : t ≠ 0) (U : Scheme.{0}) : Subsingleton (Sec ((sgl F).X t) U) :=
  sec_sub (HomologicalComplex.isZero_single_obj_X _ _ _ _ ht) U

theorem map_res {F G : Shv R} (φ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U) (x : Sec F U) :
    Sec.res g (Sec.map φ x) = Sec.map φ (Sec.res g x) :=
  (congrArg (fun f => ModuleCat.Hom.hom f x) (φ.hom.naturality g.op)).symm

theorem map_comp' {F G H : Shv R} (f : F ⟶ G) (g : G ⟶ H) {U : Scheme.{0}} (x : Sec F U) :
    Sec.map (f ≫ g) x = Sec.map g (Sec.map f x) := rfl

theorem map_zero' {F G : Shv R} {U : Scheme.{0}} (x : Sec F U) : Sec.map (0 : F ⟶ G) x = 0 := rfl

theorem tens_ind {I J : Cx R} {U : Scheme.{0}} {w : ℤ} (P : Tens I J U w → Prop) (h0 : P 0)
    (hadd : ∀ x y, P x → P y → P (x + y))
    (ht : ∀ p a b, P (DirectSum.lof (ULift.{1} R) _ _ p (a ⊗ₜ b))) (x : Tens I J U w) : P x := by
  induction x using DirectSum.induction_on with
  | zero => exact h0
  | add x y hx hy => exact hadd _ _ hx hy
  | of p z =>
    induction z using TensorProduct.induction_on with
    | zero => simpa using h0
    | tmul a b => simpa [DirectSum.lof_eq_of] using ht p a b
    | add z1 z2 h1 h2 => rw [map_add (f := _)]; exact hadd _ _ h1 h2

theorem lift_lof {I J K : Cx R} (τ : Pair I J K) (U : Scheme.{0}) (w : ℤ) p a b :
    τ.lift U w (DirectSum.lof (ULift.{1} R) _ _ p (a ⊗ₜ b)) = τ.mul U p.1.1 p.1.2 w p.2 a b := by
  simp [Pair.lift, DirectSum.toModule_lof]

theorem shv_isZero {F : Shv R} (h : ∀ U : Scheme.{0}, ∀ y : Sec F U, y = 0) : IsZero F := by
  rw [IsZero.iff_id_eq_zero]
  ext U y
  exact h _ y

end LateralTheory.EtaleFoundations.TwSide

namespace LateralTheory.EtaleFoundations.TwSide
variable {q : ℕ} [NeZero q]

noncomputable def T {A B J : Cx (ZMod q)} (ε : B ⟶ J) (U : Scheme.{0}) (w : ℤ) :
    Tens A B U w →ₗ[ULift.{1} (ZMod q)] Tens A J U w :=
  DirectSum.toModule _ _ _ fun p => (DirectSum.lof (ULift.{1} (ZMod q)) {p : ℤ × ℤ // p.1 + p.2 = w}
      (fun p => Sec (A.X p.1.1) U ⊗[ULift.{1} (ZMod q)] Sec (J.X p.1.2) U) p).comp
    (TensorProduct.map LinearMap.id ((ε.f p.1.2).hom.app (op U)).hom)

theorem T_lof {A B J : Cx (ZMod q)} (ε : B ⟶ J) (U : Scheme.{0}) (w : ℤ) (p : {p : ℤ × ℤ // p.1 + p.2 = w})
    (a : Sec (A.X p.1.1) U) (b : Sec (B.X p.1.2) U) :
    T ε U w (DirectSum.lof (ULift.{1} (ZMod q)) _ _ p (a ⊗ₜ b)) =
      DirectSum.lof (ULift.{1} (ZMod q)) _ _ p (a ⊗ₜ Sec.map (ε.f p.1.2) b) := by
  simp [T, DirectSum.toModule_lof]

theorem smul_eq (c : ULift.{1} (ZMod q)) : c = ((c.down.val : ℕ) : ULift.{1} (ZMod q)) := by
  apply ULift.ext; rw [ULift.down_natCast, ZMod.natCast_zmod_val]

noncomputable def ofFam {F G : Shv (ZMod q)} (φ : ∀ U : Scheme.{0}, Sec F U →+ Sec G U)
    (hφ : ∀ (V U : Scheme.{0}) (g : V ⟶ U) y, Sec.res g (φ U y) = φ V (Sec.res g y)) : F ⟶ G :=
  ObjectProperty.homMk
    { app := fun U => ModuleCat.ofHom
        { toFun := φ U.unop
          map_add' := map_add _
          map_smul' := fun c y => by
            rw [smul_eq c]
            simp only [Nat.cast_smul_eq_nsmul, map_nsmul, RingHom.id_apply] }
      naturality := fun U V g => by
        ext y
        exact (hφ V.unop U.unop g.unop y).symm }

theorem twist_side (htm : tw_mul) (htf : tw_flat) (hfl : flip_ex) (hqis : tens_qis) (i j k : ℤ) (hk : i + j = k)
    {J M : Cx (ZMod q)} (e' : ∀ U : Scheme.{0}, Prim q Γ(U, ⊤) → Sec (J.X 0) U) (hJ : IsTwRes q j J e')
    (hflat : ∀ t, FlatS (J.X t)) (σ : Pair (sgl (tw q i)) J M) (hσ : σ.IsTensor) :
    IsTwRes q k M fun U ζ => σ.mul U 0 0 0 (add_zero 0) (Sec.map (sglι (tw q i)) (twGen i ζ)) (e' U ζ) := by
  obtain ⟨μ, hμ, hgen⟩ := htm q i j k hk
  obtain ⟨hJge, ε', hε', hε'gen⟩ := hJ

  have hMge : M.IsStrictlyGE 0 := by
    refine (CochainComplex.isStrictlyGE_iff M 0).2 fun w hw => shv_isZero fun U y => ?_
    apply LateralTheory.EtaleFoundations.TensFam.sep
    obtain ⟨S, hS, h1⟩ := hσ.1 U w y
    refine ⟨S, hS, fun V g hg => ?_⟩
    obtain ⟨x, hx⟩ := h1 V g hg
    rw [← hx, show Sec.res g (0 : Sec (M.X w) U) = 0 from map_zero _]
    refine tens_ind (fun x => σ.lift V w x = 0) (map_zero _) (fun x y hx hy => by rw [map_add (f := _), hx, hy, add_zero])
      (fun p a b => ?_) x
    rw [lift_lof]
    rcases p with ⟨⟨s, t⟩, hst⟩
    by_cases hs : s = 0
    · have ht : t < 0 := by simp only at hst; omega
      haveI := sec_sub (CochainComplex.isZero_of_isStrictlyGE J 0 t (by omega)) V
      rw [Subsingleton.elim b 0, map_zero]
    · haveI := sgl_sub (tw q i) hs V
      rw [Subsingleton.elim a 0, map_zero, LinearMap.zero_apply]
  let b : ∀ U : Scheme.{0}, Tens (sgl (tw q i)) (sgl (tw q j)) U 0 →+ Sec (M.X 0) U :=
    fun U => ((σ.lift U 0).comp (T ε' U 0)).toAddMonoidHom
  have hbv : ∀ U p a c, b U (DirectSum.lof (ULift.{1} (ZMod q)) _ _ p (a ⊗ₜ c)) =
      σ.mul U p.1.1 p.1.2 0 p.2 a (Sec.map (ε'.f p.1.2) c) := by
    intro U p a c
    simp only [b, LinearMap.toAddMonoidHom_coe, LinearMap.comp_apply, T_lof, lift_lof]
  have hb : ∀ (V U : Scheme.{0}) (g : V ⟶ U) x, Sec.res g (b U x) = b V (Tens.res g 0 x) := by
    intro V U g x
    refine tens_ind (fun x => Sec.res g (b U x) = b V (Tens.res g 0 x)) (by simp)
      (fun x y hx hy => by simp only [map_add (f := _), hx, hy]) (fun p a c => ?_) x
    rw [hbv, σ.nat, map_res]
    simp only [Tens.res, DirectSum.lmap_lof, TensorProduct.map_tmul]
    rw [hbv]
  obtain ⟨φ, hφnat, hφlift⟩ := LateralTheory.EtaleFoundations.etale_tensor_hom_descends_along_tensor_pairing (ZMod q) (ZMod q) μ hμ 0 (M.X 0) b hb
  have hd : ∀ U (y : Sec ((sgl (tw q k)).X 0) U), Sec.map (M.d 0 (0 + 1)) (φ U y) = 0 := by
    intro U y
    apply LateralTheory.EtaleFoundations.TensFam.sep
    obtain ⟨S, hS, h1⟩ := hμ.1 U 0 y
    refine ⟨S, hS, fun V g hg => ?_⟩
    obtain ⟨x, hx⟩ := h1 V g hg
    rw [show Sec.res g (0 : Sec (M.X (0 + 1)) U) = 0 from map_zero _, map_res, hφnat, ← hx, hφlift]
    refine tens_ind (fun x => Sec.map (M.d 0 (0 + 1)) (b V x) = 0) (by simp)
      (fun x y hx hy => by simp only [map_add (f := _), hx, hy, add_zero]) (fun p a c => ?_) x
    rcases p with ⟨⟨s, t⟩, hst⟩
    rw [hbv]
    have hl := σ.leibniz V s t 0 hst a (Sec.map (ε'.f t) c)
    have hz : ∀ (F : Shv (ZMod q)) (m n : ℤ), (sgl F).d m n = 0 := fun F m n => HomologicalComplex.single_obj_d _ _ _ _ _
    rw [hl, ← map_comp', ε'.comm, map_comp', hz, hz]
    simp only [map_zero', map_zero, LinearMap.zero_apply, smul_zero, add_zero]
  let u : sgl (tw q k) ⟶ M := HomologicalComplex.mkHomFromSingle (sglι (tw q k) ≫ ofFam φ hφnat) (by
    intro l hl
    obtain rfl : l = 0 + 1 := by simp at hl; omega
    ext U y
    exact hd _ _)
  have hu0 : ∀ U (z : Sec ((sgl (tw q k)).X 0) U), Sec.map (u.f 0) z = φ U z := by
    intro U z
    rw [HomologicalComplex.mkHomFromSingle_f, ← Category.assoc]
    show Sec.map (ofFam φ hφnat) (Sec.map ((HomologicalComplex.singleObjXSelf _ 0 (tw q k)).hom ≫ (HomologicalComplex.singleObjXSelf _ 0 (tw q k)).inv) z) = _
    rw [Iso.hom_inv_id]; rfl
  have cmp : ∀ (U : Scheme.{0}) (s t w : ℤ) (h : s + t = w) (a : Sec ((sgl (tw q i)).X s) U) (c : Sec ((sgl (tw q j)).X t) U),
      Sec.map (u.f w) (μ.mul U s t w h a c) = σ.mul U s t w h a (Sec.map (ε'.f t) c) := by
    intro U s t w h a c
    by_cases hs : s = 0
    · by_cases ht : t = 0
      · subst hs ht
        obtain rfl : w = 0 := by omega
        rw [hu0]
        have := hφlift U (DirectSum.lof (ULift.{1} (ZMod q)) _ _ ⟨(0,0), h⟩ (a ⊗ₜ c))
        rw [lift_lof] at this
        rw [this, hbv]
      · haveI := sgl_sub (tw q j) ht U
        rw [Subsingleton.elim c 0]
        simp only [map_zero]
    · haveI := sgl_sub (tw q i) hs U
      rw [Subsingleton.elim a 0]
      simp only [map_zero, LinearMap.zero_apply]
  obtain ⟨μf, hμf, -, hμfT⟩ := hfl (ZMod q) μ
  obtain ⟨σf, hσf, -, hσfT⟩ := hfl (ZMod q) σ
  haveI := hJge
  haveI := hε'
  have hcomp : μf.Compat σf ε' (𝟙 _) u := by
    intro U s t w h a c
    rw [HomologicalComplex.id_f]
    show _ = σf.mul U s t w h (Sec.map (ε'.f s) a) c
    rw [hμf U t s w (by omega) c a, hσf U t s w (by omega) c _, Units.smul_def, Units.smul_def, ← cmp]
    exact map_zsmul ((u.f w).hom.app (op U)).hom _ _
  have hu : QuasiIso u := hqis (ZMod q) μf σf (hμfT hμ) (hσfT hσ) (flat_sgl (htf q i)) ε' u hcomp
  refine ⟨hMge, u, hu, fun U ζ => ?_⟩
  rw [← hgen U ζ, cmp, hε'gen]

end LateralTheory.EtaleFoundations.TwSide

theorem LateralTheory.EtaleFoundations.tt_twist_side_of (htm : LateralTheory.EtaleFoundations.TwSide.tw_mul) (htf : LateralTheory.EtaleFoundations.TwSide.tw_flat)
    (hfl : LateralTheory.EtaleFoundations.TwSide.flip_ex) (hqis : LateralTheory.EtaleFoundations.TwSide.tens_qis) : LateralTheory.EtaleFoundations.tt_twist_side := by
  intro q _ i j k hk J M e' hJ hflat σ hσ
  exact LateralTheory.EtaleFoundations.TwSide.twist_side htm htf hfl hqis i j k hk e' hJ hflat σ hσ
end

section

namespace LateralTheory.EtaleFoundations.QFFlat

universe u v

open TensorProduct

theorem zmod_P (q : ℕ) [NeZero q] (a : ZMod q) :
    ∃ b : ZMod q, b * a = 0 ∧ ∀ r : ZMod q, r * b = 0 → ∃ c, c * a = r := by
  have hq : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  set n := a.val with hn
  set g := Nat.gcd n q with hg
  have hgq : g ∣ q := Nat.gcd_dvd_right n q
  have hgn : g ∣ n := Nat.gcd_dvd_left n q
  have hgpos : 0 < g := Nat.gcd_pos_of_pos_right n hq
  have ha : (n : ZMod q) = a := ZMod.natCast_zmod_val a
  refine ⟨((q / g : ℕ) : ZMod q), ?_, fun r hr => ?_⟩
  · rw [← ha, ← Nat.cast_mul, ZMod.natCast_eq_zero_iff]
    obtain ⟨t, ht⟩ := hgn
    refine ⟨t, ?_⟩
    rw [ht, ← mul_assoc, Nat.div_mul_cancel hgq]
  · have hr' : (r.val : ZMod q) = r := ZMod.natCast_zmod_val r
    rw [← hr', ← Nat.cast_mul, ZMod.natCast_eq_zero_iff] at hr
    have hqg : 0 < q / g := Nat.div_pos (Nat.le_of_dvd hq hgq) hgpos
    have hdiv : g ∣ r.val := by
      have h1 : g * (q / g) ∣ r.val * (q / g) := by rwa [Nat.mul_div_cancel' hgq]
      exact Nat.dvd_of_mul_dvd_mul_right hqg h1
    obtain ⟨j, hj⟩ := hdiv
    have hbez : ((g : ℤ) : ZMod q) = (n : ZMod q) * ((Nat.gcdA n q : ℤ) : ZMod q) := by
      rw [hg, Nat.gcd_eq_gcd_ab n q]
      push_cast
      simp
    refine ⟨((Nat.gcdA n q : ℤ) : ZMod q) * (j : ZMod q), ?_⟩
    rw [← hr', hj, ← ha]
    push_cast at hbez ⊢
    rw [hbez]
    ring

theorem ulift_P (q : ℕ) [NeZero q] (a : ULift.{1} (ZMod q)) :
    ∃ b : ULift.{1} (ZMod q), b * a = 0 ∧ ∀ r : ULift.{1} (ZMod q), r * b = 0 → ∃ c, c * a = r := by
  obtain ⟨b, hb, h⟩ := zmod_P q a.down
  refine ⟨ULift.up b, ULift.ext hb, fun r hr => ?_⟩
  obtain ⟨c, hc⟩ := h r.down (congrArg ULift.down hr)
  exact ⟨ULift.up c, ULift.ext hc⟩

theorem key {R : Type u} {M : Type v} [CommRing R] [Small.{v} R] [AddCommGroup M] [Module R M] (hM : Module.Injective R M)
    (hP : ∀ a : R, ∃ b : R, b * a = 0 ∧ ∀ r : R, r * b = 0 → ∃ c, c * a = r)
    (a : R) (m : M) (h : a • m = 0) : ∃ (b : R) (m' : M), b * a = 0 ∧ m = b • m' := by
  obtain ⟨b, hba, hb⟩ := hP a
  have wd : ∀ c c' : R, c * b = c' * b → c • m = c' • m := by
    intro c c' hcc
    obtain ⟨e, he⟩ := hb (c - c') (by rw [sub_mul, hcc, sub_self])
    rw [← sub_eq_zero, ← sub_smul, ← he, mul_smul, h, smul_zero]
  have hc : ∀ x : Ideal.span {b}, (Ideal.mem_span_singleton'.1 x.2).choose * b = x :=
    fun x => (Ideal.mem_span_singleton'.1 x.2).choose_spec
  let g : Ideal.span {b} →ₗ[R] M :=
    { toFun := fun x => (Ideal.mem_span_singleton'.1 x.2).choose • m
      map_add' := fun x y => by
        rw [← add_smul]
        apply wd
        rw [add_mul, hc, hc, hc, Submodule.coe_add]
      map_smul' := fun r x => by
        rw [RingHom.id_apply, ← mul_smul]
        apply wd
        rw [mul_assoc, hc, hc, Submodule.coe_smul, smul_eq_mul] }
  obtain ⟨G, hG⟩ := Module.Baer.of_injective hM (Ideal.span {b}) g
  refine ⟨b, G 1, hba, ?_⟩
  have hbm : b ∈ Ideal.span {b} := Ideal.subset_span rfl
  rw [← map_smul, smul_eq_mul, mul_one, hG b hbm]
  change m = (Ideal.mem_span_singleton'.1 hbm).choose • m
  conv_lhs => rw [← one_smul R m]
  apply wd
  rw [hc ⟨b, hbm⟩, one_mul]

theorem flat_of {R : Type u} {M : Type v} [CommRing R] [Small.{v} R] [IsPrincipalIdealRing R] [AddCommGroup M] [Module R M]
    (hM : Module.Injective R M)
    (hP : ∀ a : R, ∃ b : R, b * a = 0 ∧ ∀ r : R, r * b = 0 → ∃ c, c * a = r) : Module.Flat R M := by
  rw [Module.Flat.iff_lift_lsmul_comp_subtype_injective]
  intro I _
  obtain ⟨a, ha⟩ := Submodule.IsPrincipal.principal I
  have mem : a ∈ I := by rw [ha]; exact Submodule.mem_span_singleton_self a
  have hrep : ∀ t : I ⊗[R] M, ∃ m : M, t = (⟨a, mem⟩ : I) ⊗ₜ m := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => exact ⟨0, by simp⟩
    | tmul x n =>
      have hx : (x : R) ∈ Submodule.span R {a} := ha ▸ x.2
      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 hx
      refine ⟨c • n, ?_⟩
      rw [← smul_tmul]
      congr 1
      ext
      simp
      rw [← hc, smul_eq_mul]
    | add x y hx hy =>
      obtain ⟨mx, rfl⟩ := hx
      obtain ⟨my, rfl⟩ := hy
      exact ⟨mx + my, by rw [tmul_add]⟩
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro t ht
  obtain ⟨m, rfl⟩ := hrep t
  have ham : a • m = 0 := by simpa using ht
  obtain ⟨b, m', hba, rfl⟩ := key hM hP a m ham
  rw [← smul_tmul]
  have h0 : b • (⟨a, mem⟩ : I) = 0 := Subtype.ext (by simp [hba])
  rw [h0, zero_tmul]

end LateralTheory.EtaleFoundations.QFFlat

theorem LateralTheory.EtaleFoundations.zmod_injective_module_flat_holds : LateralTheory.EtaleFoundations.ZModInjectiveModuleFlat := by
  intro q _ N _ _ hN
  have : IsPrincipalIdealRing (ZMod q) :=
    IsPrincipalIdealRing.of_surjective (Int.castRingHom (ZMod q)) ZMod.intCast_surjective
  have : IsPrincipalIdealRing (ULift.{1} (ZMod q)) :=
    IsPrincipalIdealRing.of_surjective (ULift.ringEquiv (R := ZMod q)).symm
      (ULift.ringEquiv (R := ZMod q)).symm.surjective
  exact LateralTheory.EtaleFoundations.QFFlat.flat_of hN (LateralTheory.EtaleFoundations.QFFlat.ulift_P q)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

theorem LateralTheory.EtaleFoundations.etale_single_sheaf_homotopic_maps_equal_holds : LateralTheory.EtaleFoundations.EtaleSingleSheafHomotopicMapsToNonnegComplexEqual := by
  intro R _ F I _ a b ⟨h⟩
  apply HomologicalComplex.hom_ext
  intro i
  by_cases hi : i = 0
  · subst hi
    rw [h.comm 0]
    have h1 : dNext 0 h.hom = 0 := by
      rw [dNext_eq h.hom (show (ComplexShape.up ℤ).Rel 0 1 by simp)]
      rw [show (sgl F).d 0 1 = 0 from
        (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 F 1 (by omega)).eq_of_tgt _ _]
      simp
    have h2 : prevD 0 h.hom = 0 := by
      rw [prevD_eq h.hom (show (ComplexShape.up ℤ).Rel (-1) 0 by simp)]
      rw [show h.hom 0 (-1) = 0 from (CochainComplex.isZero_of_isStrictlyGE I 0 (-1) (by omega)).eq_of_tgt _ _]
      simp
    rw [h1, h2]; simp
  · exact (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 F i hi).eq_of_src _ _
end
