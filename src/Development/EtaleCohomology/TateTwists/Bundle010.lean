module

public import Development.EtaleCohomology.TateTwists.Bundle002
public import Development.EtaleCohomology.KummerTheory.CupAWCutEv
public import Development.EtaleCohomology.TateTwists.Bundle007
public import Development.EtaleCohomology.TateTwists.Bundle003
public import Development.EtaleCohomology.TateTwists.Bundle009
public import Development.EtaleCohomology.TateTwists.Bundle004
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
import Mathlib.Tactic.TypeStar
import Development.AbelianVarietyTheory.BlockTheory.CMModuli.ProjectiveSpaceOverSpec

@[expose] public section

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
open LateralTheory.KummerTheory.AW

namespace LateralTheory.EtaleFoundations.AWLeib
variable {R : Type} [CommRing R]

theorem bd_map {E : Spc} {U : Scheme.{0}} {G G' : Type*} [AddCommGroup G] [AddCommGroup G'] (φ : G →+ G')
    (f : ∀ p : ℕ, Sx E p U → G) (p : ℕ) (y : Sx E p U) : φ (bd f p y) = bd (fun q z => φ (f q z)) p y := by
  cases p with
  | zero => simp [bd]
  | succ p => simp [bd, map_sum, map_zsmul]

theorem ev_delta_bd {E : Spc} {I : Cx R} {n m : ℤ} (hm : n + 1 = m) (α : Cochain ((chains R).obj E) I n) (p : ℕ)
    (s t : ℤ) (hs : -(p : ℤ) + n = s) (ht : -(p : ℤ) + m = t) (U : Scheme.{0}) (x : Sx E p U) :
    ev (R := R) (δ n m α) p t ht U x = Sec.map (I.d s t) (ev (R := R) α p s hs U x) +
      m.negOnePow • bd (fun q z => if hh : -(q : ℤ) + n = t then ev (R := R) α q t hh U z else 0) p x := by
  have ev_eq {k : ℤ} (a : Cochain ((chains R).obj E) I k) (q : ℕ) (j : ℤ)
      (h : -(q : ℤ) + k = j) (y : Sx E q U) :
      ev (R := R) a q j h U y = Sec.map ((chainsXIso R E q).inv ≫ a.v _ _ h) (freeGen R _ U y) := rfl
  cases p with
  | zero =>
    rw [ev_eq, δ_v n m hm α _ _ ht s 1 (by omega) (by simp),
      (isZero_pos E 1 one_pos).eq_of_tgt (((chains R).obj E).d _ 1) 0]
    simp only [zero_comp, smul_zero, add_zero, bd]
    rfl
  | succ p =>
    have hp : -(p : ℤ) + n = t := by omega
    rw [ev_eq, δ_v n m hm α _ _ ht s (-(p : ℤ)) (by omega) (by omega),
      Preadditive.comp_add, Linear.comp_units_smul, reassoc_of% (chains_d (R := R) E p),
      Preadditive.sum_comp]
    refine (sec_map_add _ _ _).trans ?_
    congr 1
    rw [Units.smul_def, Units.smul_def, sec_map_zsmul, sec_map_sum]
    congr 1
    simp only [bd, dite_eq_left hp]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Preadditive.zsmul_comp, sec_map_zsmul, ev_eq]
    congr 1
    exact congrArg (Sec.map ((chainsXIso R E p).inv ≫ α.v (-(p : ℤ)) t hp)) (map_freeGen (E.δ i) U x)

theorem mul_congr {I J K : Cx R} (μ : Pair I J K) (U : Scheme.{0}) {E : Spc} {n m : ℤ}
    (α : Cochain ((chains R).obj E) I n) (β : Cochain ((chains R).obj E) J m) (p q : ℕ) (y : Sx E p U) (z : Sx E q U)
    (s t w s' t' : ℤ) (h : s + t = w) (h' : s' + t' = w) (hs : -(p : ℤ) + n = s) (ht : -(q : ℤ) + m = t)
    (hs' : -(p : ℤ) + n = s') (ht' : -(q : ℤ) + m = t') :
    μ.mul U s t w h (ev (R := R) α p s hs U y) (ev (R := R) β q t ht U z) =
      μ.mul U s' t' w h' (ev (R := R) α p s' hs' U y) (ev (R := R) β q t' ht' U z) := by
  subst hs ht hs' ht'; rfl

theorem leib' {I J K : Cx R} (μ : Pair I J K) (U : Scheme.{0}) (s t w s' t' w' : ℤ) (h : s + t = w) (hs : s + 1 = s')
    (ht : t + 1 = t') (hw : w + 1 = w') (a : Sec (I.X s) U) (b : Sec (J.X t) U) :
    Sec.map (K.d w w') (μ.mul U s t w h a b) = μ.mul U s' t w' (by omega) (Sec.map (I.d s s') a) b +
      s.negOnePow • μ.mul U s t' w' (by omega) a (Sec.map (J.d t t') b) := by
  subst hs ht hw; exact μ.leibniz U s t w h a b

theorem mul_bd_left {I J K : Cx R} (μ : Pair I J K) {E : Spc} {U : Scheme.{0}} (s t w : ℤ) (h : s + t = w)
    (f : ∀ q : ℕ, Sx E q U → Sec (I.X s) U) (p : ℕ) (y : Sx E p U) (b : Sec (J.X t) U) :
    μ.mul U s t w h (bd f p y) b = bd (fun q z => μ.mul U s t w h (f q z) b) p y :=
  bd_map (((μ.mul U s t w h).flip b).toAddMonoidHom) f p y

theorem mul_bd_right {I J K : Cx R} (μ : Pair I J K) {E : Spc} {U : Scheme.{0}} (s t w : ℤ) (h : s + t = w)
    (f : ∀ q : ℕ, Sx E q U → Sec (J.X t) U) (p : ℕ) (y : Sx E p U) (a : Sec (I.X s) U) :
    μ.mul U s t w h a (bd f p y) = bd (fun q z => μ.mul U s t w h a (f q z)) p y :=
  bd_map ((μ.mul U s t w h a).toAddMonoidHom) f p y

theorem secmap_sum {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} {ι : Type*} (s : Finset ι) (f : ι → Sec F U) :
    Sec.map φ (∑ i ∈ s, f i) = ∑ i ∈ s, Sec.map φ (f i) := map_sum ((φ.hom.app (op U)).hom) f s

theorem secmap_zsmul {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} (c : ℤ) (a : Sec F U) :
    Sec.map φ (c • a) = c • Sec.map φ a := map_zsmul ((φ.hom.app (op U)).hom) c a

def Fm {I J K : Cx R} (μ : Pair I J K) {E : Spc} {n m : ℤ} (α : Cochain ((chains R).obj E) I n)
    (β : Cochain ((chains R).obj E) J m) (U : Scheme.{0}) (w : ℤ) (p q : ℕ) (y : Sx E p U) (z : Sx E q U) :
    Sec (K.X w) U :=
  if hh : (-(p : ℤ) + n) + (-(q : ℤ) + m) = w then μ.mul U _ _ w hh (ev (R := R) α p _ rfl U y) (ev (R := R) β q _ rfl U z) else 0

theorem recombine {G : Type*} [AddCommGroup G] (X Y BF BF' BB BB' : G) (c s K c' P e1 e2 c2 e3 : ℤ) (hF : BF' = BF)
    (hB : BB' = BB) (h2 : c * s = e2 * c2) (h3 : K * c' = c * e1) (h4 : K * (c * P) = e2 * (c2 * e3)) :
    c • (X + s • Y) + K • (c' • BF + c • P • BB) = c • (X + e1 • BF') + e2 • c2 • (Y + e3 • BB') := by
  subst hF hB
  simp only [smul_add, smul_smul]
  rw [h2, h3, h4]
  abel

theorem sign_nat (p : ℕ) : ((-1 : ℤ) ^ p) = (((p : ℤ).negOnePow : ℤˣ) : ℤ) := by
  simp [Int.negOnePow_def]

end LateralTheory.EtaleFoundations.AWLeib


open LateralTheory.EtaleFoundations.AWLeib in
theorem LateralTheory.EtaleFoundations.etaleAlexanderWhitneyCup_leibniz_of_pairing : LateralTheory.EtaleFoundations.EtaleAlexanderWhitneyCupLeibniz := by
  intro R _ I J K μ E n m k hk α β γ γ₁ γ₂ hγ h1 h2
  have ev_ext (a b : Cochain ((chains R).obj E) K (k + 1))
      (h : ∀ p s hs U x, ev (R := R) a p s hs U x = ev (R := R) b p s hs U x) : a = b := by
    ext i j hij : 1
    by_cases hi : 0 < i
    · exact (isZero_pos E i hi).eq_of_src _ _
    obtain ⟨p, rfl⟩ : ∃ p : ℕ, i = -(p : ℤ) := ⟨(-i).toNat, by omega⟩
    rw [← cancel_epi (chainsXIso R E p).inv]
    exact free_ext _ _ (fun U x => h p j hij U x)
  apply ev_ext
  intro N w hw U x
  have ev_add : ev (R := R) (γ₁ + n.negOnePow • γ₂) N w hw U x =
      ev (R := R) γ₁ N w hw U x + ev (R := R) (n.negOnePow • γ₂) N w hw U x := by
    unfold ev
    rw [Cochain.add_v, Preadditive.comp_add]
    rfl
  have ev_units_smul : ev (R := R) (n.negOnePow • γ₂) N w hw U x = n.negOnePow • ev (R := R) γ₂ N w hw U x := by
    change Sec.map ((chainsXIso R E N).inv ≫ (n.negOnePow • γ₂).v _ _ hw) (freeGen R _ U x) = _
    rw [Cochain.units_smul_v, Linear.comp_units_smul, Units.smul_def, sec_map_zsmul]
    rfl
  rw [ev_add, ev_units_smul, ev_delta_bd rfl γ N (-(N : ℤ) + k) w rfl hw U x, hγ N _ rfl U x, h1 N w hw U x,
    h2 N w hw U x]
  rw [bd_congr (g := fun N' y => ∑ p : Fin (N' + 1), ((m * (p : ℕ)).negOnePow : ℤ) •
      Fm μ α β U w p (N' - p) (y.sub 0 p (by omega)) (y.sub p (N' - p) (by omega))) ?_ x]
  swap
  · intro N' y hN
    rw [dite_eq_left (by omega), hγ N' w _ U y]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Units.smul_def]
    unfold Fm
    rw [dite_eq_left (by omega)]
  rw [bd_aw (Fm μ α β U w) (fun p : ℕ => ((m * (p : ℤ)).negOnePow : ℤ)) (fun p : ℕ => ((m * ((p : ℤ) - 1)).negOnePow : ℤ))
    (fun p => by congr 2; push_cast; ring) N x]
  rw [secmap_sum, Finset.smul_sum, Finset.smul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  have hp := p.2
  rw [Units.smul_def, secmap_zsmul, leib' μ U _ _ _ (-((p : ℕ) : ℤ) + (n + 1)) (-((N - p : ℕ) : ℤ) + (m + 1)) w _ (by ring) (by ring) (by omega)]
  rw [ev_delta_bd rfl α p (-((p : ℕ) : ℤ) + n) _ rfl _ U, ev_delta_bd rfl β (N - p) (-((N - p : ℕ) : ℤ) + m) _ rfl _ U]
  simp only [map_add (f := _), map_zsmul, LinearMap.add_apply, LinearMap.smul_apply, Units.smul_def, mul_bd_left, mul_bd_right]
  refine recombine _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_ ?_ ?_
  · refine bd_congr (fun q z hq => ?_) _
    rw [dite_eq_left (by omega)]
    unfold Fm
    rw [dite_eq_left (by omega)]
    exact mul_congr μ U α β _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  · refine bd_congr (fun q z hq => ?_) _
    rw [dite_eq_left (by omega)]
    unfold Fm
    rw [dite_eq_left (by omega)]
    exact mul_congr μ U α β _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  · simp only [← Units.val_mul, ← Int.negOnePow_add]
    congr 1
    rw [Int.negOnePow_eq_iff]
    exact ⟨-((p : ℕ) : ℤ), by ring⟩
  · subst hk
    simp only [← Units.val_mul, ← Int.negOnePow_add]
    congr 1
    rw [Int.negOnePow_eq_iff]
    exact ⟨0, by ring⟩
  · subst hk
    rw [sign_nat]
    simp only [← Units.val_mul, ← Int.negOnePow_add]
    congr 1
    rw [Int.negOnePow_eq_iff]
    exact ⟨0, by ring⟩
end
end

section

namespace LateralTheory.Fin.EtaleFreeSheafUniversalProperty
theorem etale_free_module_cohomology_hom_of_components : LateralTheory.EtaleFoundations.EtaleFreeSheafUniversalProperty := by
  apply LateralTheory.EtaleFoundations.etale_free_sheaf_hom_universal_property_holds
theorem intersectionNumber_baseChange : LateralTheory.EtaleFoundations.EtaleFreeSheafUniversalProperty := etale_free_module_cohomology_hom_of_components
end LateralTheory.Fin.EtaleFreeSheafUniversalProperty
end

section

namespace LateralTheory.Fin.EtaleMayerVietorisChainsShortExact
theorem etale_mayer_vietoris_short_exact_sequence_free_of_components : LateralTheory.EtaleFoundations.EtaleFreePresheafMayerVietorisShortExact := by
  apply LateralTheory.EtaleFoundations.etale_free_presheaf_mayer_vietoris_short_exact_holds
theorem etale_mayer_vietoris_short_exact_sequence_of_components : LateralTheory.EtaleFoundations.EtaleMayerVietorisChainsShortExact := by
  apply LateralTheory.EtaleFoundations.etale_chains_mayer_vietoris_short_exact_of_free <;> first | exact etale_mayer_vietoris_short_exact_sequence_free_of_components
theorem intersectionNumber_baseChange : LateralTheory.EtaleFoundations.EtaleMayerVietorisChainsShortExact := etale_mayer_vietoris_short_exact_sequence_of_components
end LateralTheory.Fin.EtaleMayerVietorisChainsShortExact
end

section

namespace LateralTheory.Fin.PrimitiveRootsOfUnityBasicIdentities
theorem etale_torsion_cohomology_primary_part_basic : LateralTheory.EtaleFoundations.PrimitiveRootsOfUnityBasicIdentities := by
  apply LateralTheory.EtaleFoundations.PrimPf.cyclotomic_primitive_root_product_identities_of_adjoin_root
theorem intersectionNumber_baseChange : LateralTheory.EtaleFoundations.PrimitiveRootsOfUnityBasicIdentities := etale_torsion_cohomology_primary_part_basic
end LateralTheory.Fin.PrimitiveRootsOfUnityBasicIdentities
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section
namespace LateralTheory.EtaleFoundations.TwMulPf

variable {R : Type} [CommRing R]

theorem sec_res_map {F G : Shv R} (φ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U) (x : Sec F U) :
    Sec.res g (Sec.map φ x) = Sec.map φ (Sec.res g x) := by
  have := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom (φ.hom.naturality g.op)) x
  simpa using this.symm

theorem sec_map_comp {F G H : Shv R} (φ : F ⟶ G) (ψ : G ⟶ H) {U : Scheme.{0}} (x : Sec F U) :
    Sec.map ψ (Sec.map φ x) = Sec.map (φ ≫ ψ) x := by
  simp [Sec.map]

theorem sec_map_id {F : Shv R} {U : Scheme.{0}} (x : Sec F U) : Sec.map (𝟙 F) x = x := by
  simp [Sec.map]

theorem loc_mono {U : Scheme.{0}} {P Q : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (h : Loc U P)
    (hPQ : ∀ V g, P V g → Q V g) : Loc U Q := by
  obtain ⟨S, hS, hP⟩ := h
  exact ⟨S, hS, fun V g hg => hPQ V g (hP V g hg)⟩

def secL {F G : Shv R} (φ : F ⟶ G) (U : Scheme.{0}) : Sec F U →ₗ[ULift.{1} R] Sec G U :=
  (φ.hom.app (op U)).hom

def transp {I J K K' : Cx R} (μ : Pair I J K) (ψ : K ≅ K') : Pair I J K' where
  mul U s t w h := (μ.mul U s t w h).compr₂ (secL (ψ.hom.f w) U)
  nat g s t w h a b := by
    change Sec.res g (Sec.map (ψ.hom.f w) _) = Sec.map (ψ.hom.f w) _
    rw [sec_res_map, μ.nat]
  leibniz U s t w h a b := by
    change Sec.map (K'.d w (w + 1)) (Sec.map (ψ.hom.f w) _) =
      Sec.map (ψ.hom.f (w + 1)) _ + s.negOnePow • Sec.map (ψ.hom.f (w + 1)) _
    rw [sec_map_comp, ψ.hom.comm w (w + 1), ← sec_map_comp, μ.leibniz]
    simp only [Sec.map, map_add (f := _), map_zsmul_unit]

theorem transp_lift {I J K K' : Cx R} (μ : Pair I J K) (ψ : K ≅ K') (U : Scheme.{0}) (w : ℤ)
    (x : Tens I J U w) : (transp μ ψ).lift U w x = Sec.map (ψ.hom.f w) (μ.lift U w x) := by
  classical
  change _ = secL (ψ.hom.f w) U (μ.lift U w x)
  rw [← LinearMap.comp_apply]
  congr 1
  refine DirectSum.linearMap_ext _ fun p => TensorProduct.ext' fun a b => ?_
  simp [Pair.lift, transp]

theorem transp_isTensor {I J K K' : Cx R} (μ : Pair I J K) (ψ : K ≅ K') (hμ : μ.IsTensor) :
    (transp μ ψ).IsTensor := by
  refine ⟨fun U w y => ?_, fun U w x hx => ?_⟩
  · refine loc_mono (hμ.1 U w (Sec.map (ψ.inv.f w) y)) fun V g ⟨x, hx⟩ => ⟨x, ?_⟩
    rw [transp_lift, hx, ← sec_res_map, sec_map_comp, ← HomologicalComplex.comp_f, ψ.inv_hom_id,
      HomologicalComplex.id_f, sec_map_id]
  · refine hμ.2 U w x ?_
    rw [transp_lift] at hx
    have := congrArg (Sec.map (ψ.inv.f w)) hx
    rw [sec_map_comp, ← HomologicalComplex.comp_f, ψ.hom_inv_id, HomologicalComplex.id_f, sec_map_id] at this
    rw [this]
    exact map_zero _

theorem sgl_map_f_zero {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} (x : Sec F U) :
    Sec.map (((CochainComplex.singleFunctor (Shv R) 0).map φ).f 0) (Sec.map (sglι F) x) =
      Sec.map (sglι G) (Sec.map φ x) := by
  rw [sec_map_comp, sec_map_comp]
  congr 1

end LateralTheory.EtaleFoundations.TwMulPf


open LateralTheory.EtaleFoundations.TwMulPf in
def LateralTheory.EtaleFoundations.EtaleTateTwistTensorPairingExists : Prop :=
  ∀ (q : ℕ) [NeZero q] (i j : ℤ), ∃ (T : Shv (ZMod q)) (μ : Pair (sgl (tw q i)) (sgl (tw q j)) (sgl T)), μ.IsTensor

def LateralTheory.EtaleFoundations.EtaleTateTwistGeneratorCompatibleMapExists : Prop :=
  ∀ (q : ℕ) [NeZero q] (i j k : ℤ) (T : Shv (ZMod q)) (μ : Pair (sgl (tw q i)) (sgl (tw q j)) (sgl T)),
    μ.IsTensor → i + j = k → ∃ φ : tw q k ⟶ T, ∀ (U : Scheme.{0}) (ζ : Prim q Γ(U, ⊤)),
      Sec.map (sglι T) (Sec.map φ (twGen k ζ)) =
        μ.mul U 0 0 0 (add_zero 0) (Sec.map (sglι _) (twGen i ζ)) (Sec.map (sglι _) (twGen j ζ))

def LateralTheory.EtaleFoundations.EtaleTateTwistGeneratorCompatibleMapIsIso : Prop :=
  ∀ (q : ℕ) [NeZero q] (i j k : ℤ) (T : Shv (ZMod q)) (μ : Pair (sgl (tw q i)) (sgl (tw q j)) (sgl T)),
    μ.IsTensor → i + j = k → ∀ φ : tw q k ⟶ T, (∀ (U : Scheme.{0}) (ζ : Prim q Γ(U, ⊤)),
      Sec.map (sglι T) (Sec.map φ (twGen k ζ)) =
        μ.mul U 0 0 0 (add_zero 0) (Sec.map (sglι _) (twGen i ζ)) (Sec.map (sglι _) (twGen j ζ))) → IsIso φ

open LateralTheory.EtaleFoundations.TwMulPf in
theorem LateralTheory.EtaleFoundations.etale_tate_twist_tensor_iso_of_generator_map_iso (h1 : LateralTheory.EtaleFoundations.EtaleTateTwistTensorPairingExists)
    (h2 : LateralTheory.EtaleFoundations.EtaleTateTwistGeneratorCompatibleMapExists) (h3 : LateralTheory.EtaleFoundations.EtaleTateTwistGeneratorCompatibleMapIsIso) :
    LateralTheory.EtaleFoundations.EtaleTateTwistSingletonTensorGenMul := by
  intro q _ i j k hk
  obtain ⟨T, μ, hμ⟩ := h1 q i j
  obtain ⟨φ, hφ⟩ := h2 q i j k T μ hμ hk
  have := h3 q i j k T μ hμ hk φ hφ
  let ψ : sgl T ≅ sgl (tw q k) := (CochainComplex.singleFunctor (Shv (ZMod q)) 0).mapIso (asIso φ).symm
  refine ⟨transp μ ψ, transp_isTensor μ ψ hμ, fun U ζ => ?_⟩
  change Sec.map (ψ.hom.f 0) (μ.mul U 0 0 0 (add_zero 0) _ _) = _
  rw [← hφ U ζ]
  change Sec.map (((CochainComplex.singleFunctor (Shv (ZMod q)) 0).map (inv φ)).f 0) _ = _
  rw [sgl_map_f_zero, sec_map_comp, sec_map_comp, IsIso.hom_inv_id_assoc]
end
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations

def tt_tens_ex : Prop :=
  ∀ (R : Type) [CommRing R] (I J : Cx R), ∃ (K : Cx R) (μ : Pair I J K), μ.IsTensor

def tt_tens_ge : Prop :=
  ∀ (R : Type) [CommRing R] {I J K : Cx R} (μ : Pair I J K), I.IsStrictlyGE 0 → J.IsStrictlyGE 0 → μ.IsTensor →
    K.IsStrictlyGE 0

def tt_twist_side : Prop :=
  ∀ (q : ℕ) [NeZero q] (i j k : ℤ), i + j = k → ∀ {J M : Cx (ZMod q)}
    (e' : ∀ U : Scheme.{0}, Prim q Γ(U, ⊤) → Sec (J.X 0) U), IsTwRes q j J e' → (∀ t, FlatS (J.X t)) →
    ∀ σ : Pair (sgl (tw q i)) J M, σ.IsTensor →
      IsTwRes q k M fun U ζ => σ.mul U 0 0 0 (add_zero 0) (Sec.map (sglι (tw q i)) (twGen i ζ)) (e' U ζ)

def tt_res_side : Prop :=
  ∀ (q : ℕ) [NeZero q] (i : ℤ) {I J M T : Cx (ZMod q)} (e : ∀ U : Scheme.{0}, Prim q Γ(U, ⊤) → Sec (I.X 0) U),
    IsTwRes q i I e → J.IsStrictlyGE 0 → (∀ t, FlatS (J.X t)) →
    ∀ (σ : Pair (sgl (tw q i)) J M) (τ : Pair I J T), σ.IsTensor → τ.IsTensor →
      ∃ m : M ⟶ T, QuasiIso m ∧ ∀ (U : Scheme.{0}) (ζ : Prim q Γ(U, ⊤)) (b : Sec (J.X 0) U),
        Sec.map (m.f 0) (σ.mul U 0 0 0 (add_zero 0) (Sec.map (sglι (tw q i)) (twGen i ζ)) b) =
          τ.mul U 0 0 0 (add_zero 0) (e U ζ) b

theorem etale_tensor_twisted_resolution_of_existence_bound_and_sides (hex : tt_tens_ex) (hge : tt_tens_ge) (htw : tt_twist_side) (hres : tt_res_side) :
    EtaleTensorPairTwistResolutionMul := by
  intro q _ i j k hk I J T e e' hI hJ hflat τ hτ
  obtain ⟨M, σ, hσ⟩ := hex (ZMod q) (sgl (tw q i)) J
  obtain ⟨-, ε₁, hε₁, hgen₁⟩ := htw q i j k hk e' hJ hflat σ hσ
  obtain ⟨m, hm, hgen⟩ := hres q i e hI hJ.1 hflat σ τ hσ hτ
  refine ⟨hge (ZMod q) τ hI.1 hJ.1 hτ, ε₁ ≫ m, inferInstance, fun U ζ => ?_⟩
  refine Eq.trans ?_ (hgen U ζ (e' U ζ))
  refine Eq.trans ?_ (congrArg (Sec.map (m.f 0)) (hgen₁ U ζ))
  rfl

end LateralTheory.EtaleFoundations
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite TensorProduct GlobalTheory.EtC GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec

namespace LateralTheory.EtaleFoundations.TwLocPf

theorem ofRings_sec_res {R : Type} [CommRing R] (M : CommRingCat.{0} ⥤ ModuleCat.{1} (ULift.{1} R)) {V U : Scheme.{0}}
    (g : V ⟶ U) (x : M.obj Γ(U, ⊤)) :
    Sec.res g (ofRings.sec M U x) = ofRings.sec M V ((M.map g.appTop).hom x) := by
  have h := congrArg (fun f => f.hom x)
    ((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ M)).naturality g.op)
  simp only [ModuleCat.hom_comp] at h
  exact h.symm

theorem twGen_res (q : ℕ) (i : ℤ) (V U : Scheme.{0}) (g : V ⟶ U) (ζ : Prim q Γ(U, ⊤)) :
    Sec.res g (twGen i ζ) = twGen i (ζ.map g.appTop.hom) := by
  refine (ofRings_sec_res (twF q i) g _).trans ?_
  unfold twGen
  congr 1
  change Submodule.Quotient.mk (Finsupp.mapDomain (Prim.map g.appTop.hom) (Finsupp.single ζ 1)) = _
  rw [Finsupp.mapDomain_single]

def TwSecLoc : Prop := ∀ (q : ℕ) [NeZero q] (i : ℤ) (U : Scheme.{0}) (ζ : Prim q Γ(U, ⊤)) (y : Sec (tw q i) U),
  Loc U fun V g => ∃ c : ℕ, Sec.res g y = c • twGen i (ζ.map g.appTop.hom)

def TwTors : Prop := ∀ (q : ℕ) [NeZero q] (i : ℤ) (U : Scheme.{0}) [Nonempty U] (ζ : Prim q Γ(U, ⊤)) (c : ℕ),
  c • twGen i ζ = 0 → q ∣ c

theorem TwLoc_of (h1 : TwSecLoc) (h2 : TwTors) : LateralTheory.EtaleFoundations.CongruenceLocalDecomposition.TwLoc := by
  intro q _ i
  exact ⟨fun U ζ y => h1 q i U ζ y, fun U _ ζ c hc => h2 q i U ζ c hc, fun V U g ζ => twGen_res q i V U g ζ⟩

end LateralTheory.EtaleFoundations.TwLocPf
end
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations

def cupflip_aw_cochain : Prop :=
  ∀ (R : Type) [CommRing R] {I J K : Cx R} (μ : Pair I J K) (E : Spc) {n m k : ℤ} (hk : n + m = k)
    (α : Cochain ((chains R).obj E) I n) (β : Cochain ((chains R).obj E) J m),
    ∃ γ : Cochain ((chains R).obj E) K k, μ.IsAW hk α β γ

def cupflip_aw_leibniz : Prop :=
  ∀ (R : Type) [CommRing R] {I J K : Cx R} (μ : Pair I J K) {E : Spc} {n m k : ℤ} (hk : n + m = k)
    (α : Cochain ((chains R).obj E) I n) (β : Cochain ((chains R).obj E) J m) (γ : Cochain ((chains R).obj E) K k)
    (γ₁ γ₂ : Cochain ((chains R).obj E) K (k + 1)),
    μ.IsAW hk α β γ → μ.IsAW (by omega) (δ n (n + 1) α) β γ₁ → μ.IsAW (by omega) α (δ m (m + 1) β) γ₂ →
      δ k (k + 1) γ = γ₁ + n.negOnePow • γ₂

theorem ev_zero_cochain {R : Type} [CommRing R] {E : Spc} {I : Cx R} {n : ℤ} (p : ℕ) (s : ℤ)
    (h : -(p : ℤ) + n = s) (U : Scheme.{0}) (x : Sx E p U) :
    ev (R := R) (0 : Cochain ((chains R).obj E) I n) p s h U x = 0 := by
  simp [ev]

theorem isAW_zero_left {R : Type} [CommRing R] {I J K : Cx R} (μ : Pair I J K) {E : Spc} {n m k : ℤ}
    (hk : n + m = k) (β : Cochain ((chains R).obj E) J m) : μ.IsAW hk 0 β 0 := by
  intro N w h U x
  simp [ev_zero_cochain]

theorem isAW_zero_right {R : Type} [CommRing R] {I J K : Cx R} (μ : Pair I J K) {E : Spc} {n m k : ℤ}
    (hk : n + m = k) (α : Cochain ((chains R).obj E) I n) : μ.IsAW hk α 0 0 := by
  intro N w h U x
  simp [ev_zero_cochain]

theorem cupflip_aw_exists_of (hc : cupflip_aw_cochain) (hl : cupflip_aw_leibniz) : cupflip_aw_exists := by
  intro R _ I J K μ E n m k hk α β
  obtain ⟨γ, hγ⟩ := hc R μ E hk α.1 β.1
  have hα : δ n (n + 1) α.1 = 0 := Cocycle.δ_eq_zero α (n + 1)
  have hβ : δ m (m + 1) β.1 = 0 := Cocycle.δ_eq_zero β (m + 1)
  have h1 : μ.IsAW (by omega) (δ n (n + 1) α.1) β.1 (0 : Cochain ((chains R).obj E) K (k + 1)) := by
    rw [hα]; exact isAW_zero_left μ _ β.1
  have h2 : μ.IsAW (by omega) α.1 (δ m (m + 1) β.1) (0 : Cochain ((chains R).obj E) K (k + 1)) := by
    rw [hβ]; exact isAW_zero_right μ _ α.1
  have hδ : δ k (k + 1) γ = 0 := by
    rw [hl R μ hk α.1 β.1 γ 0 0 hγ h1 h2]; simp
  exact ⟨Cocycle.mk γ (k + 1) rfl hδ, hγ⟩

end LateralTheory.EtaleFoundations
end
