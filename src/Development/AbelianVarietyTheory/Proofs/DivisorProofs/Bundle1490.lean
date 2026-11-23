module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle023
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CobOneEqZeroOfConnecting
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1299
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1399
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1148
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle573
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle024
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WhitMulLocGLDiagPowOfFixed
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle031
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1398
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1300
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1099
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1088
public import Mathlib.Algebra.MvPolynomial.Funext
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle033
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1164
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1303
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1400
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1165
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle036
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1403
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.HasBoundedPolesGlobalData
import Development.AbelianVarietyTheory.Definitions.Divisors.HermSysHypOneLeLambdaZero
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle012
import Development.AbelianVarietyTheory.Definitions.Divisors.MemSubPtsCutBaseChangeIff
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.Bundle001
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle035

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu

namespace GlobalTheory.Dieu.Theory

theorem frobProj_omega_surjective {p : ℕ} [Fact p.Prime] {k : Type} [Field k] [CharP k p] [PerfectRing k p]
    (G : PDivGroup p k) : Function.Surjective (frobProj (p_eq_zero p k) G).omega := by
  letI := (frobRing (p_eq_zero p k)).toAlgebra
  intro t
  obtain ⟨x, rfl⟩ := (omega_baseChange_bijective G k (p_eq_zero p k)).2 t
  induction x using TensorProduct.inductionOn with
  | add x y hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    exact ⟨a + b, (map_add _ a b).trans ((congrArg₂ (· + ·) ha hb).trans (map_add _ x y).symm)⟩
  | tmul r w =>
    refine ⟨(frobeniusEquiv k p).symm r • w, ?_⟩
    rw [liftSemi_tmul, map_smulₛₗ]
    congr 1
    show frobRing (p_eq_zero p k) _ = r
    rw [frobRing_apply, frobeniusEquiv_symm_pow_p]

theorem hodge_filtration : ∀ (p : ℕ) [Fact p.Prime] (T : Theory p) (k : Type) [Field k] [CharP k p] [PerfectRing k p] (G : PDivGroup p k), (∀ x : ((G.cocycles × G.omega) ⧸ _root_.LinearMap.range (G.cob.prod (_root_.LinearMap.codRestrict G.omegaSub ((_root_.LinearMap.piMap fun i => _root_.GlobalTheory.AugCot.d (_root_.Bialgebra.counitAlgHom _ (G.A i))).domRestrict G.funs) (fun b n => (_root_.GlobalTheory.PDiv.cotMap_d _ _).trans (_root_.congrArg _ (b.2 n)))))), (∃ m, T.red G (T.V G m) = x) ↔ x ∈ LinearMap.range G.rigOfOmega) ∧ (∀ m, T.red G (T.V G m) = 0 ↔ ∃ n, m = T.F G n) ∧ (∀ m, G.rigToLie (p_eq_zero p k) (T.red G m) = 0 ↔ ∃ n, m = T.V G n) ∧ Function.Injective G.rigOfOmega := by
  intro p _ T k _ _ _ G
  obtain ⟨-, hVinj, hVsm, -, -⟩ := GlobalTheory.T.dieudonneTheory_V_eq_verschiebung_injective p T k G
  obtain ⟨hbij, -, -⟩ := GlobalTheory.T.dieudonne_frobeniusTwist_bijective_relFrobenius p T.base k G
  obtain ⟨-, -, -, hver, -, -, -⟩ := rigExt_field_of_charP p k (p_eq_zero p k) G
  have key : ∀ m, SemiHom.rig (frobProj (p_eq_zero p k) G) (T.red G (T.V G m)) =
      rigExtMap (verschiebung (p_eq_zero p k) G) (T.red G m) := by
    intro m
    rw [← T.base.red_smap trivial trivial (frobProj (p_eq_zero p k) G), hVsm]
    rw [← SemiHom.ofHom_rig]
    exact T.base.red_smap trivial trivial (SemiHom.ofHom _) m
  have rinj : Function.Injective (frobProj (p_eq_zero p k) G).rig := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨m, rfl⟩ := T.base.red_surjective G trivial x
    rw [← T.base.red_smap trivial trivial (frobProj (p_eq_zero p k) G)] at hx
    have hx' := (T.base.red_eq_zero (frobTwist (p_eq_zero p k) G) trivial _).1 hx
    clear hx
    obtain ⟨n, hn⟩ := hx'
    obtain ⟨n', rfl⟩ := hbij.2 n
    have hm : m = p • n' := hbij.1 (by rw [hn, map_nsmul])
    exact (T.base.red_eq_zero G trivial m).2 ⟨n', hm⟩
  have osurj := frobProj_omega_surjective G
  have h1 : ∀ x : G.RigExt, (∃ m, T.red G (T.V G m) = x) ↔ x ∈ LinearMap.range G.rigOfOmega := by
    intro x
    constructor
    · rintro ⟨m, rfl⟩
      have hm : SemiHom.rig (frobProj (p_eq_zero p k) G) (T.red G (T.V G m)) ∈
          LinearMap.range (frobTwist (p_eq_zero p k) G).rigOfOmega := by
        rw [key, ← hver]; exact ⟨_, rfl⟩
      obtain ⟨w', hw'⟩ := hm
      obtain ⟨w, rfl⟩ := osurj w'
      exact ⟨w, rinj ((SemiHom.rig_rigOfOmega _ w).trans hw')⟩
    · rintro ⟨w, rfl⟩
      have hw : (frobTwist (p_eq_zero p k) G).rigOfOmega (SemiHom.omega (frobProj (p_eq_zero p k) G) w) ∈
          LinearMap.range (rigExtMap (verschiebung (p_eq_zero p k) G)) := by
        rw [hver]; exact ⟨_, rfl⟩
      obtain ⟨y, hy⟩ := hw
      obtain ⟨m, rfl⟩ := T.base.red_surjective G trivial y
      exact ⟨m, rinj ((key m).trans (hy.trans (SemiHom.rig_rigOfOmega _ w).symm))⟩
  have h2 : ∀ m, T.red G (T.V G m) = 0 ↔ ∃ n, m = T.F G n := by
    intro m
    refine (T.base.red_eq_zero G trivial _).trans ⟨fun ⟨n, hn⟩ => ⟨n, hVinj ?_⟩, fun ⟨n, hn⟩ => ⟨n, ?_⟩⟩
    · rw [hn]; exact (T.V_F G n).symm
    · rw [hn]; exact T.V_F G n
  refine ⟨h1, h2, fun m => ?_, G.rigOfOmega_injective_of_eq_zero (p_eq_zero p k)⟩
  rw [G.exact_rigOfOmega_rigToLie (p_eq_zero p k) (T.red G m)]
  constructor
  · intro hm
    obtain ⟨m', hm'⟩ := (h1 _).2 hm
    have h0 : T.red G (m - T.V G m') = 0 := by rw [map_sub, hm', sub_self]
    obtain ⟨n, hn⟩ := (T.base.red_eq_zero G trivial _).1 h0
    refine ⟨m' + T.F G n, ?_⟩
    rw [map_add (f := _), T.V_F G n, ← hn, add_sub_cancel]
  · rintro ⟨n, rfl⟩
    obtain ⟨w, hw⟩ := (h1 (T.red G (T.V G n))).1 ⟨n, rfl⟩
    exact ⟨w, hw⟩

end GlobalTheory.Dieu.Theory
end
end

section

noncomputable section
open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun Matrix
open scoped ContDiff

namespace GlobalTheory.JSW

theorem map_pLoc_pFin_finGL_locGL_of_ne {E : Type} [Field E] [NumberField E] {a : ℕ}
    {v w : HeightOneSpectrum (𝓞 E)} (h : v ≠ w) (k : GL (Fin a) (w.adicCompletion E)) :
    GeneralLinearGroup.map ((pLoc E v).comp (pFin E)) (finGL E a (locGL E a w k)) = 1 := by
  have e : GeneralLinearGroup.map ((pLoc E v).comp (pFin E)) (finGL E a (locGL E a w k)) =
      GeneralLinearGroup.map (pLoc E v) (GeneralLinearGroup.map (pFin E) (finGL E a (locGL E a w k))) := by
    ext; rfl
  rw [e, pFin_finGL, pLoc_locGL_of_ne h]

theorem whit_mul_list_prod (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ)
    (π : CuspSub E a) (α : HeightOneSpectrum (𝓞 E) → Fin a → ℂˣ) (φ) (hφV : φ ∈ π.V)
    (ϖ : ∀ w : HeightOneSpectrum (𝓞 E), (w.adicCompletion E)ˣ) (l : HeightOneSpectrum (𝓞 E) → Fin a → ℕ)
    (L : List (HeightOneSpectrum (𝓞 E))) (hL : L.Nodup)
    (hw : ∀ w ∈ L, (∀ x : w.adicCompletion E, (∀ y ∈ Ov E w, (GroundTheory.Global.adelicChar _ (GlobalTheory.CuspRep.sFin _ (GlobalTheory.CuspRep.sLoc _ w (x * y))) : ℂ) = 1) ↔ x ∈ Ov E w) ∧
      HasSatGL w (π.locRep w) (Finset.univ.val.map (α w)) ∧
      (∀ k ∈ KGL w (n := a), act (.fin (locGL E a w k)) φ = φ) ∧ IsUnifV E w (ϖ w : w.adicCompletion E)) :
    ∀ g : GA E a, (∀ w ∈ L, GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) g = 1) →
      GlobalTheory.JSW.whit φ.1 (g * (L.map fun w => finGL E a (locGL E a w (diagPow (ϖ w) (l w)))).prod) =
        (L.map fun w => GlobalTheory.JSW.sphW (qV E w) (fun i => (α w i : ℂ)) (l w)).prod * GlobalTheory.JSW.whit φ.1 g := by
  induction L with
  | nil => intro g _; simp
  | cons w L ih =>
    intro g hg
    rw [List.nodup_cons] at hL
    have hw0 := hw w (List.mem_cons_self ..)
    have ih' := ih hL.2 (fun v hv => hw v (List.mem_cons_of_mem _ hv))
    simp only [List.map_cons, List.prod_cons]
    rw [← mul_assoc, ih' (g * finGL E a (locGL E a w (diagPow (ϖ w) (l w)))) ?_,
      whit_mul_locGL_diagPow E a π w (α w) hw0.1 hw0.2.1 φ hφV hw0.2.2.1 g (hg w (List.mem_cons_self ..))
        (ϖ w) hw0.2.2.2 (l w)]
    · ring
    · intro v hv
      have hne : v ≠ w := fun h => hL.1 (h ▸ hv)
      rw [map_mul, hg v (List.mem_cons_of_mem _ hv), map_pLoc_pFin_finGL_locGL_of_ne hne, one_mul]

theorem whit_mul_tl : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))), (∀ w ∉ S, ∀ x : w.adicCompletion E, (∀ y ∈ Ov E w, (GroundTheory.Global.adelicChar _ (GlobalTheory.CuspRep.sFin _ (GlobalTheory.CuspRep.sLoc _ w (x * y))) : ℂ) = 1) ↔ x ∈ Ov E w) → ∀ (π : CuspSub E a) (α : HeightOneSpectrum (𝓞 E) → Fin a → ℂˣ), (∀ w ∉ S, HasSatGL w (π.locRep w) (Finset.univ.val.map (α w))) → ∀ φ ∈ π.V, (∀ w ∉ S, ∀ k ∈ KGL w (n := a), act (.fin (locGL E a w k)) φ = φ) → ∀ (ϖ : ∀ w : HeightOneSpectrum (𝓞 E), (w.adicCompletion E)ˣ), (∀ w, IsUnifV E w (ϖ w : w.adicCompletion E)) → ∀ l : HeightOneSpectrum (𝓞 E) →₀ (Fin a → ℕ), (∀ w ∈ l.support, w ∉ S) → ∀ x ∈ GlobalTheory.JSW.supS (E := E) (a := a) S, GlobalTheory.JSW.whit φ.1 (x * GlobalTheory.JSW.tl ϖ l) = (∏ w ∈ l.support, GlobalTheory.JSW.sphW (qV E w) (fun i => (α w i : ℂ)) (l w)) * GlobalTheory.JSW.whit φ.1 x := by
  intro E _ _ _ a S hψ π α hα φ hφV hφ ϖ hϖ l hl x hx
  have hmem : ∀ w ∈ l.support.toList, w ∉ S := fun w hw => hl w (Finset.mem_toList.1 hw)
  rw [tl, whit_mul_list_prod E a π α φ hφV ϖ l l.support.toList (Finset.nodup_toList _)
      (fun w hw => ⟨hψ w (hmem w hw), hα w (hmem w hw), hφ w (hmem w hw), hϖ w⟩) x
      (fun w hw => hx w (hmem w hw))]
  congr 1
  exact Finset.prod_map_toList _ _

end GlobalTheory.JSW
end
end

section

set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.PicGlue Opposite
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PicGlue

variable {S : Scheme.{0}} {A : Over S} [GrpObj A]

theorem AddCls.pull_lift_one_eq_zero {T : Over S} {c : Pic (A ⊗ T).left} (h : AddCls A c) {Y : Over S} (t : Y ⟶ T) :
    CechPic.pull (lift (1 : Y ⟶ A) t).left c = 0 := by
  have h1 := h Y 1 1 t
  rw [_root_.mul_one] at h1
  exact left_eq_add.1 h1

theorem AddCls.pull_eq_zero_of_unit {T Z : Over S} (z : Z ⟶ T) {c : Pic (A ⊗ Z).left} (h : AddCls A c)
    {T' : Scheme.{0}} (t : T' ⟶ (A ⊗ Z).left) (s : T' ⟶ T.left)
    (hts : t ≫ (A ◁ z).left = s ≫ (lift (1 : T ⟶ A) (𝟙 T)).left) : CechPic.pull t c = 0 := by
  let Y : Over S := Over.mk (t ≫ (A ⊗ Z).hom)
  let t' : Y ⟶ A ⊗ Z := Over.homMk t rfl
  have hs : s ≫ T.hom = t ≫ (A ⊗ Z).hom := by
    rw [← Over.w (A ◁ z), ← Category.assoc, hts, Category.assoc, Over.w]
  let s' : Y ⟶ T := Over.homMk s hs
  have h1 : t' ≫ A ◁ z = s' ≫ lift (1 : T ⟶ A) (𝟙 T) := Over.OverMorphism.ext hts
  have h2 : t' ≫ fst A Z = 1 := by
    have h3 := congrArg (· ≫ fst A T) h1
    simpa only [Category.assoc, whiskerLeft_fst, lift_fst, MonObj.comp_one] using h3
  have h4 : t' = lift (1 : Y ⟶ A) (t' ≫ snd A Z) := by
    rw [← h2, lift_comp_fst_snd]
  have h5 := h.pull_lift_one_eq_zero (t' ≫ snd A Z)
  rw [← h4] at h5
  exact h5

theorem pull_eq_of_compat {T Z Z' : Over S} (z : Z ⟶ T) (z' : Z' ⟶ T) (y : (addF A).obj (op Z))
    (y' : (addF A).obj (op Z'))
    (h : ∀ (Y : Over S) (a : Y ⟶ Z) (b : Y ⟶ Z'), a ≫ z = b ≫ z' → (addF A).map a.op y = (addF A).map b.op y')
    {T' : Scheme.{0}} (a : T' ⟶ (A ⊗ Z).left) (b : T' ⟶ (A ⊗ Z').left)
    (hab : a ≫ (A ◁ z).left = b ≫ (A ◁ z').left) : CechPic.pull a y.1 = CechPic.pull b y'.1 := by
  let Y : Over S := Over.mk (a ≫ (A ⊗ Z).hom)
  let a' : Y ⟶ A ⊗ Z := Over.homMk a rfl
  have hb : b ≫ (A ⊗ Z').hom = a ≫ (A ⊗ Z).hom := by
    rw [← Over.w (A ◁ z), ← Over.w (A ◁ z'), ← Category.assoc, ← hab, Category.assoc]
  let b' : Y ⟶ A ⊗ Z' := Over.homMk b hb
  have h1 : a' ≫ A ◁ z = b' ≫ A ◁ z' := Over.OverMorphism.ext hab
  have h2 : a' ≫ fst A Z = b' ≫ fst A Z' := by
    have h3 := congrArg (· ≫ fst A T) h1
    simpa only [Category.assoc, whiskerLeft_fst] using h3
  have h3 : (a' ≫ snd A Z) ≫ z = (b' ≫ snd A Z') ≫ z' := by
    have h3 := congrArg (· ≫ snd A T) h1
    simpa only [Category.assoc, whiskerLeft_snd] using h3
  have h4 := congrArg Subtype.val (h Y _ _ h3)
  rw [addF_map_val, addF_map_val] at h4
  have ha' : a' = lift (a' ≫ fst A Z) (𝟙 Y) ≫ A ◁ (a' ≫ snd A Z) := by
    rw [lift_whiskerLeft, Category.id_comp, lift_comp_fst_snd]
  have hb' : b' = lift (a' ≫ fst A Z) (𝟙 Y) ≫ A ◁ (b' ≫ snd A Z') := by
    rw [lift_whiskerLeft, Category.id_comp, h2, lift_comp_fst_snd]
  have h5 := congrArg (CechPic.pull (lift (a' ≫ fst A Z) (𝟙 Y)).left) h4
  rw [← pull_comp, ← pull_comp, ← Over.comp_left, ← Over.comp_left, ← ha', ← hb'] at h5
  exact h5

theorem addF_glue : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A], IsAbelianScheme A → (∀ (T : Over S) (J : Type) (Z : J → Over S) (z : ∀ i, Z i ⟶ T) (y : ∀ i, (addF A).obj (op (Z i))), (∀ i, IsOpenImmersion (z i).left) → (∀ p : T.left, ∃ i, p ∈ Set.range (z i).left) → (∀ (i k : J) (Y : Over S) (a : Y ⟶ Z i) (b : Y ⟶ Z k), a ≫ z i = b ≫ z k → (addF A).map a.op (y i) = (addF A).map b.op (y k)) → ∃ y₀ : (addF A).obj (op T), ∀ i, (addF A).map (z i).op y₀ = y i) := by
  intro S A _ hA T J Z z y hz hcov hc
  have he : (lift (1 : T ⟶ A) (𝟙 T)).left ≫ (snd A T).left = 𝟙 T.left := by
    rw [← Over.comp_left, lift_snd, Over.id_left]
  obtain ⟨c₀, h0, hc₀⟩ := GlobalTheory.T.exists_glue_rigidified_line_bundle_classes (A ⊗ T).left T.left (snd A T).left (lift (1 : T ⟶ A) (𝟙 T)).left he
    (GlobalTheory.T.isPreimageSectionsBijective_abelianScheme_snd S A T hA) J (fun i ↦ (A ⊗ Z i).left) (fun i ↦ (A ◁ z i).left)
    (fun i ↦ haveI := hz i; (z i).left.opensRange) (fun i ↦ (y i).1)
    (fun i ↦ (GlobalTheory.whiskerLeft_isOpenImmersion_range S A T (Z i) (z i) (hz i)).1)
    (fun i x ↦ (GlobalTheory.whiskerLeft_isOpenImmersion_range S A T (Z i) (z i) (hz i)).2 x)
    (fun p ↦ hcov p)
    (fun i T' t s hts ↦ AddCls.pull_eq_zero_of_unit (z i) (y i).2 t s hts)
    (fun i k T' a b hab ↦ pull_eq_of_compat (z i) (z k) (y i) (y k) (hc i k) a b hab)
  refine ⟨⟨c₀, GlobalTheory.T.additive_picClass_of_locally_additive S A T hA c₀ h0 fun p ↦ ?_⟩, fun i ↦ Subtype.ext (hc₀ i)⟩
  obtain ⟨i, hi⟩ := hcov p
  refine ⟨Z i, z i, hz i, hi, ?_⟩
  rw [hc₀ i]
  exact (y i).2

end GlobalTheory.PicGlue
end
end

section

open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology

theorem _root_.GlobalTheory.T.prodDerivWeierstrassPOverSquares_pow_eight_mul : ∀ (p : ℕ) (F : IntermediateField ℚ ℂ) (L : PeriodPair) (t : ℂ), p.Prime → p % 4 = 3 → 3 < p → Datum p F L t → sqProd p L t ^ 8 * (p : ℂ) ^ 6 = (latticeCurve L).Δ ^ (p - 1) := by
  first | exact @GlobalTheory.CMModel.sqProd_pow_eight_mul | exact GlobalTheory.CMModel.sqProd_pow_eight_mul | (intros; apply GlobalTheory.CMModel.sqProd_pow_eight_mul <;> assumption)
end

section

open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology

theorem _root_.GlobalTheory.T.prodDerivWeierstrassPOverSquares_sq_mem_stable : ∀ (p : ℕ) (F : IntermediateField ℚ ℂ) (L : PeriodPair) (t : ℂ), p.Prime → p % 4 = 3 → 3 < p → Datum p F L t → sqProd p L t ^ 2 ∈ F ∧ (sqProd p L t ∈ F → Stable L F (sqPt p t)) := by
  first | exact @GlobalTheory.CMModel.sqProd_sq_mem_and_stable | exact GlobalTheory.CMModel.sqProd_sq_mem_and_stable | (intros; apply GlobalTheory.CMModel.sqProd_sq_mem_and_stable <;> assumption)
end

section

open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HermTools GlobalTheory.HilbertSamuel GlobalTheory.HSChoice GlobalTheory.HSShort

set_option autoImplicit false

namespace GlobalTheory.HSShortDiv

variable {F : Type} [Field F] {D N : ℕ}

noncomputable def lastSubst (l₀ : Fin N → F) : Fin (D + 1) × Fin N → MvPolynomial (Fin (D + 1) × Fin N) F :=
  fun p => if p.1 = Fin.last D then C (l₀ p.2) else X p

theorem eval_aeval_lastSubst (l₀ : Fin N → F) (x : Fin (D + 1) × Fin N → F)
    (f : MvPolynomial (Fin (D + 1) × Fin N) F) :
    eval x (aeval (lastSubst l₀) f) = eval (fun p => if p.1 = Fin.last D then l₀ p.2 else x p) f := by
  induction f using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => rw [map_add (f := _), map_add (f := _), hp, hq, map_add (f := _)]
  | mul_X p q hp =>
    simp only [map_mul, hp, aeval_X, eval_X, lastSubst]
    split_ifs <;> simp

theorem replace_eq_join (l : Fin N → F) (x : Fin (D + 1) × Fin N → F) :
    (fun p : Fin (D + 1) × Fin N => if p.1 = Fin.last D then l p.2 else x p) =
      join (fun i j => x (i.castSucc, j)) l := by
  funext ⟨i, j⟩
  induction i using Fin.lastCases with
  | last => simp [join]
  | cast i => simp [join, Fin.castSucc_ne_last]

theorem eval_last_zero {δ : ℕ} (hδ : 1 ≤ δ) (f : MvPolynomial (Fin (D + 1) × Fin N) F)
    (hf : IsMultiHomogeneous (fun _ => δ) f) (x : Fin (D + 1) × Fin N → F) :
    eval (fun p => if p.1 = Fin.last D then 0 else x p) f = 0 := by
  rw [eval_eq']
  refine Finset.sum_eq_zero fun d hd => ?_
  have hs := hf d hd (Fin.last D)
  have hne : (∑ j : Fin N, d (Fin.last D, j)) ≠ 0 := by simp only at hs; omega
  obtain ⟨j, -, hj⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
  refine mul_eq_zero_of_right _ (Finset.prod_eq_zero (i := (Fin.last D, j)) (Finset.mem_univ _) ?_)
  simp [zero_pow hj]

theorem pow_dvd_of_specialisations (F : Type) [Field F] [CharZero F] (D N δ b : ℕ) (f G : MvPolynomial (Fin (D + 1) × Fin N) F)
    (Q : MvPolynomial (Fin D × Fin N) F) (hδ : 1 ≤ δ) (hf : IsMultiHomogeneous (fun _ => δ) f)
    (hirr : Irreducible f) (hQ : Q ≠ 0)
    (hG : ∀ s : Fin D → Fin N → F, eval (fun p => s p.1 p.2) Q ≠ 0 → ∃ (E : Type) (_ : Field E)
      (_ : Algebra F E) (γ : E), ∀ l : Fin N → F,
        algebraMap F E (eval (join s l) G) = γ * algebraMap F E (eval (join s l) f) ^ b) :
    f ^ b ∣ G := by
  haveI : Infinite F := Infinite.of_injective Nat.cast Nat.cast_injective
  have hf0 : f ≠ 0 := hirr.ne_zero

  obtain ⟨x₀, hx₀⟩ : ∃ x₀, eval x₀ f ≠ 0 := by
    by_contra h
    push_neg at h
    exact hf0 (MvPolynomial.funext fun x => by simp [h x])
  set l₀ : Fin N → F := fun j => x₀ (Fin.last D, j) with hl₀
  set g := aeval (lastSubst l₀) f with hg
  set G₀ := aeval (lastSubst l₀) G with hG₀
  set Q' : MvPolynomial (Fin (D + 1) × Fin N) F :=
    rename (fun p : Fin D × Fin N => (p.1.castSucc, p.2)) Q with hQ'
  have hQ'0 : Q' ≠ 0 := by
    intro h
    apply hQ
    apply rename_injective _ _ (h.trans (map_zero _).symm)
    intro p q hpq
    simp only [Prod.mk.injEq, Fin.castSucc_inj] at hpq
    exact Prod.ext hpq.1 hpq.2

  have key : Q' * (G * g ^ b - f ^ b * G₀) = 0 := by
    apply MvPolynomial.funext
    intro x
    set s : Fin D → Fin N → F := fun i j => x (i.castSucc, j) with hs
    have hx : x = join s (fun j => x (Fin.last D, j)) := by
      rw [← replace_eq_join]
      funext p
      split_ifs with h
      · rw [← h]
      · rfl
    have hQx : eval x Q' = eval (fun p => s p.1 p.2) Q := by
      rw [hQ', eval_rename]; rfl
    simp only [map_mul, map_sub, map_pow, map_zero]
    by_cases hq : eval (fun p => s p.1 p.2) Q = 0
    · rw [hQx, hq, zero_mul]
    · obtain ⟨E, _, _, γ, hγ⟩ := hG s hq
      have h1 := hγ (fun j => x (Fin.last D, j))
      have h2 := hγ l₀
      rw [← hx] at h1
      have hgx : eval x g = eval (join s l₀) f := by rw [hg, eval_aeval_lastSubst, replace_eq_join]
      have hGx : eval x G₀ = eval (join s l₀) G := by rw [hG₀, eval_aeval_lastSubst, replace_eq_join]
      rw [hgx, hGx]
      have : eval x G * eval (join s l₀) f ^ b - eval x f ^ b * eval (join s l₀) G = 0 := by
        apply (algebraMap F E).injective
        simp only [map_sub, map_mul, map_pow, map_zero, h1, h2]
        ring
      rw [this, mul_zero]
  have heq : G * g ^ b = f ^ b * G₀ := by
    have := (mul_eq_zero.mp key).resolve_left hQ'0
    exact sub_eq_zero.mp this
  have hp : Prime f := hirr.prime

  have hndvd : ¬ f ∣ g := by
    rintro ⟨h, hh⟩
    have hg0 : g ≠ 0 := by
      intro h0
      have := congrArg (eval x₀) h0
      rw [hg, eval_aeval_lastSubst, map_zero] at this
      apply hx₀
      have hpt : (fun p : Fin (D + 1) × Fin N => if p.1 = Fin.last D then l₀ p.2 else x₀ p) = x₀ := by
        funext p
        split_ifs with hp1
        · rw [hl₀]; simp only; rw [← hp1]
        · rfl
      rw [hpt] at this
      exact this
    apply hg0
    apply MvPolynomial.funext
    intro x
    have e1 : eval x g = eval (fun p => if p.1 = Fin.last D then 0 else x p) g := by
      rw [hg, eval_aeval_lastSubst, eval_aeval_lastSubst]
      have hpt : (fun p : Fin (D + 1) × Fin N => if p.1 = Fin.last D then l₀ p.2 else x p) =
          (fun p => if p.1 = Fin.last D then l₀ p.2 else if p.1 = Fin.last D then 0 else x p) := by
        funext p
        split_ifs <;> rfl
      rw [hpt]
    rw [e1, hh, map_mul, eval_last_zero hδ f hf, zero_mul, map_zero]
  have hndvd' : ¬ f ∣ g ^ b := fun h => hndvd (hp.dvd_of_dvd_pow h)
  exact hp.pow_dvd_of_dvd_mul_right b hndvd' ⟨G₀, heq⟩

end GlobalTheory.HSShortDiv
end

section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.PtExt

theorem exists_pushout_torsor (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] [IsCommMonObj A]
    (n : ℕ) (hn : (n : R) = 0) (hR : HasRoots A n) (b : Fn0 A) (hb : IsTorsChar n b) :
    ∃ (u : Fn1 A) (g : Fn2 A), IsCoc (whole A) u ∧ IsAdd u g ∧
      ∀ (D : Type) [CommRing D] [Algebra R D] (x : Pt A D), (x ^ n : Pt A D) = 1 →
        chi n g D x = b D x := by
  have hSec := GlobalTheory.T.exists_pushoutTorsorSection_every_point R A n hR b hb
  let S : SecFam A := fun D _ _ x ↦ Classical.choose (hSec D x)
  have hS : ∀ (D : Type) [CommRing D] [Algebra R D] (x : Pt A D), IsSec n b x (S D x) :=
    fun D _ _ x ↦ Classical.choose_spec (hSec D x)
  obtain ⟨u, hu⟩ := GlobalTheory.T.exists_sectionDifference_one_cochain R A n hR b hb S hS
  obtain ⟨g, hg⟩ := GlobalTheory.T.exists_sectionAddition_two_point_function R A n hR b hb S hS
  exact ⟨u, g, isCoc_of_isSecDiff R A n hR b hb S hS u hu,
    isAdd_of_isSecDiff_isSecAdd R A n hR b hb S hS u g hu hg,
    chi_eq_of_torsion R A n hn hR b hb S hS g hg⟩

end GlobalTheory.PtExt
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr

theorem _root_.GlobalTheory.T.exists_finite_set_controlling_regularity_of_quotient : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p), ∀ s : X.functionField, s ∈ P.H 0 1 → s ≠ 0 → ∃ S : Set X, S.Finite ∧ ∀ (x : X) i j, x ∈ P.L.B.U i → x ∈ P.A.B.U j → ∀ τ g : X.functionField, RegAt x τ → (∀ z ∈ S, z ⤳ x → UnitAt z τ) → RegAt x g → RegAt x (g * τ / P.loc 0 1 s i j) → RegAt x (g / P.loc 0 1 s i j) := by
  first | exact @GlobalTheory.VolBr.exists_finite_controlling_points | exact GlobalTheory.VolBr.exists_finite_controlling_points | (intros; apply GlobalTheory.VolBr.exists_finite_controlling_points <;> assumption)
end
