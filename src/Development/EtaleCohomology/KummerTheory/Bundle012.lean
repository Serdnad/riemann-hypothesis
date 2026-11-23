module

public import Development.EtaleCohomology.KummerTheory.Bundle003
public import Mathlib.Order.CompletePartialOrder
public import Development.EtaleCohomology.KummerTheory.Bundle004
public import Development.EtaleCohomology.TateTwists.Bundle004
public import Development.EtaleCohomology.TateTwists.Bundle005
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.QuasiAffine
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
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
public import Mathlib.Data.ZMod.Units

@[expose] public section

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite

namespace LateralTheory.KummerTheory.IndPf

open LateralTheory.KummerTheory.ContCut

theorem isMV_opens {Y : Scheme.{0}} (U V : Y.Opens) (h : U ⊔ V = ⊤) :
    IsMV (Y.homOfLE inf_le_left) (Y.homOfLE inf_le_right) U.ι V.ι := by
  refine ⟨inferInstance, inferInstance, isPullback_opens_inf U V, fun x => ?_⟩
  rw [Scheme.Opens.range_ι, Scheme.Opens.range_ι]
  have hx : x ∈ (U ⊔ V) := by rw [h]; trivial
  exact hx

theorem inf_affine {Y : Scheme.{0}} {R : CommRingCat.{0}} (q : Y ⟶ Spec R) [IsSeparated q]
    {V₁ V₂ : Y.Opens} (h1 : IsAffineOpen V₁) (h2 : IsAffineOpen V₂) : IsAffineOpen (V₁ ⊓ V₂) :=
  (isAffineHom_diagonal_iff (f := q)).mp inferInstance ⊤ (isAffineOpen_top _) V₁ (by simp) V₂ (by simp) h1 h2

theorem iSup_fin_succ_eq {Y : Scheme.{0}} {n : ℕ} (V : Fin (n + 1) → Y.Opens) :
    (⨆ i, V i) = (⨆ i : Fin n, V i.castSucc) ⊔ V (Fin.last n) := by
  apply le_antisymm
  · refine iSup_le fun i => ?_
    refine Fin.lastCases ?_ (fun j => ?_) i
    · exact le_sup_right
    · exact le_sup_of_le_left (le_iSup (fun j : Fin n => V j.castSucc) j)
  · exact sup_le (iSup_le fun j => le_iSup V j.castSucc) (le_iSup V _)

theorem main (R : CommRingCat.{0}) (P : ∀ X : Scheme.{0}, (X ⟶ Spec R) → Prop)
    (hA : ∀ (X : Scheme.{0}) [IsAffine X] (p : X ⟶ Spec R), P X p)
    (hM : ∀ {W U V X : Scheme.{0}} (a : W ⟶ U) (b : W ⟶ V) (f : U ⟶ X) (g : V ⟶ X) (p : X ⟶ Spec R), IsMV a b f g →
      P U (f ≫ p) → P V (g ≫ p) → P W (a ≫ f ≫ p) → P X p) :
    ∀ (n : ℕ) (Y : Scheme.{0}) (q : Y ⟶ Spec R) [IsSeparated q] (V : Fin n → Y.Opens),
      (∀ i, IsAffineOpen (V i)) → (⨆ i, V i) = ⊤ → P Y q := by
  intro n
  induction n with
  | zero =>
    intro Y q _ V _ hV
    have : IsEmpty Y := by
      refine ⟨fun x => ?_⟩
      have hx : x ∈ (⊤ : Y.Opens) := trivial
      rw [← hV] at hx
      obtain ⟨i, _⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
      exact i.elim0
    have : IsAffine Y := inferInstance
    exact hA Y q
  | succ n ih =>
    intro Y q _ V hA' hV
    set U : Y.Opens := ⨆ i : Fin n, V i.castSucc with hUdef
    set V' : Y.Opens := V (Fin.last n)
    have hUV : U ⊔ V' = ⊤ := by rw [← hV, iSup_fin_succ_eq]
    refine hM _ _ U.ι V'.ι q (isMV_opens U V' hUV) ?_ ?_ ?_
    ·
      refine ih U (U.ι ≫ q) (fun i => U.ι ⁻¹ᵁ V i.castSucc) (fun i => ?_) ?_
      · exact (hA' _).preimage_of_isOpenImmersion U.ι
          (by rw [Scheme.Opens.opensRange_ι]; exact le_iSup (fun j : Fin n => V j.castSucc) i)
      · rw [← Scheme.Hom.preimage_iSup, Scheme.Opens.ι_preimage_self]
    · have : IsAffine V' := hA' (Fin.last n)
      exact hA _ _
    ·
      rw [← Category.assoc, Scheme.homOfLE_ι]
      refine ih _ ((U ⊓ V').ι ≫ q) (fun i => (U ⊓ V').ι ⁻¹ᵁ (V i.castSucc ⊓ V')) (fun i => ?_) ?_
      · exact (inf_affine q (hA' _) (hA' _)).preimage_of_isOpenImmersion _
          (by rw [Scheme.Opens.opensRange_ι]
              exact inf_le_inf_right _ (le_iSup (fun j : Fin n => V j.castSucc) i))
      · rw [← Scheme.Hom.preimage_iSup, ← iSup_inf_eq, Scheme.Opens.ι_preimage_self]

theorem Ind_of : LateralTheory.KummerTheory.ContCut.Ind := by
  intro R P hA hM X p _ _
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
  obtain ⟨s, hs, hU⟩ := (isCompact_and_isOpen_iff_finite_and_eq_biUnion_affineOpens (X := X)
    (U := Set.univ)).mp ⟨isCompact_univ, isOpen_univ⟩
  have : Finite s := hs
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin s
  refine main R P hA hM n X p (fun i => ((e.symm i : s) : X.affineOpens)) (fun i => (e.symm i : s).1.2) ?_
  ext x
  simp only [TopologicalSpace.Opens.coe_top, Set.mem_univ, iff_true]
  have hx : x ∈ (Set.univ : Set X) := trivial
  rw [hU] at hx
  obtain ⟨a, ha, hxa⟩ := Set.mem_iUnion₂.mp hx
  refine TopologicalSpace.Opens.mem_iSup.mpr ⟨e ⟨a, ha⟩, ?_⟩
  simpa using hxa

end LateralTheory.KummerTheory.IndPf
end
end

section

noncomputable section
open Polynomial IsLocalRing GlobalTheory.EtC

namespace LateralTheory.KummerTheory.PrimitiveRootTorsion

theorem aeval_cyc {S : Type} [CommRing S] (q : ℕ) (x : S) :
    aeval x (cyclotomic q ℤ) = eval x (cyclotomic q S) := by
  rw [aeval_def, eval₂_eq_eval_map, algebraMap_int_eq, map_cyclotomic_int]

theorem prim_pow {q : ℕ} {B : Type} [CommRing B] (ζ : Prim q B) : ζ.1 ^ q = 1 := by
  obtain ⟨g, hg⟩ := cyclotomic.dvd_X_pow_sub_one q ℤ
  have h := congrArg (aeval ζ.1) hg
  rw [map_mul, ζ.2.2, zero_mul] at h
  simpa [sub_eq_zero] using h

theorem pow_mod_q {q : ℕ} {B : Type} [CommRing B] {x : B} (h : x ^ q = 1) (n : ℕ) : x ^ n = x ^ (n % q) := by
  conv_lhs => rw [← Nat.div_add_mod n q, pow_add, pow_mul, h, one_pow, one_mul]

variable {q : ℕ} [NeZero q] {B : Type} [CommRing B] [IsLocalRing B]

theorem neZero_res (hq : IsUnit (q : B)) : NeZero (q : ResidueField B) :=
  ⟨by simpa using (hq.map (residue B)).ne_zero⟩

theorem uniq (hq : IsUnit (q : B)) {u v : B} (hu : u ^ q = 1) (hv : v ^ q = 1)
    (h : residue B u = residue B v) : u = v := by
  have hq' := neZero_res hq
  have hS : IsUnit (∑ i ∈ Finset.range q, u ^ i * v ^ (q - 1 - i)) := by
    apply isUnit_of_map_unit (residue B)

    rw [map_sum]
    simp only [map_mul, map_pow, h]
    rw [geom_sum₂_self]
    have hv' : residue B v ^ q = 1 := by rw [← map_pow, hv, map_one]
    have hu1 : IsUnit (residue B v) := IsUnit.of_pow_eq_one hv' (NeZero.ne q)
    exact (isUnit_iff_ne_zero.2 (NeZero.ne _)).mul (hu1.pow _)
  have e := geom_sum₂_mul u v q
  rw [hu, hv, sub_self] at e
  exact sub_eq_zero.1 ((hS.mul_right_eq_zero).1 e)

theorem prim_res (hq : IsUnit (q : B)) (ζ : Prim q B) : IsPrimitiveRoot (residue B ζ.1) q := by
  have := neZero_res hq
  rw [← isRoot_cyclotomic_iff, IsRoot, ← aeval_cyc]
  have e := Polynomial.aeval_algHom_apply (residue B).toIntAlgHom ζ.1 (cyclotomic q ℤ)
  rw [ζ.2.2, map_zero] at e
  exact e

theorem exists_idx (hq : IsUnit (q : B)) (ζ ξ : Prim q B) :
    ∃ a : (ZMod q)ˣ, ξ.1 = ζ.1 ^ (a : ZMod q).val := by
  have hζ := prim_res hq ζ
  have hξ := prim_res hq ξ
  obtain ⟨i, hi, he⟩ := hζ.eq_pow_of_pow_eq_one hξ.pow_eq_one
  have hc : i.Coprime q := (hζ.pow_iff_coprime (Nat.pos_of_ne_zero (NeZero.ne q)) i).1 (he ▸ hξ)
  refine ⟨ZMod.unitOfCoprime i hc, ?_⟩
  have hval : ((ZMod.unitOfCoprime i hc : (ZMod q)ˣ) : ZMod q).val = i := by
    rw [ZMod.coe_unitOfCoprime, ZMod.val_natCast, Nat.mod_eq_of_lt hi]
  rw [hval]
  refine uniq hq (prim_pow ξ) (by rw [← pow_mul, mul_comm, pow_mul, prim_pow ζ, one_pow]) ?_
  rw [map_pow, he]

theorem idx_unique (hq : IsUnit (q : B)) (ζ : Prim q B) {a b : (ZMod q)ˣ}
    (h : ζ.1 ^ (a : ZMod q).val = ζ.1 ^ (b : ZMod q).val) : a = b := by
  have h' := congrArg (residue B) h
  rw [map_pow, map_pow] at h'
  exact Units.ext (ZMod.val_injective q ((prim_res hq ζ).pow_inj (ZMod.val_lt _) (ZMod.val_lt _) h'))

theorem idx_mul {ζ0 ζ ξ : Prim q B} {a b : (ZMod q)ˣ} (hb : ζ.1 = ζ0.1 ^ (b : ZMod q).val)
    (ha : ξ.1 = ζ.1 ^ (a : ZMod q).val) : ξ.1 = ζ0.1 ^ ((a * b : (ZMod q)ˣ) : ZMod q).val := by
  rw [Units.val_mul, ZMod.val_mul, ← pow_mod_q (prim_pow ζ0), ha, hb, ← pow_mul, mul_comm]

end LateralTheory.KummerTheory.PrimitiveRootTorsion

namespace LateralTheory.KummerTheory.PrimitiveRootTorsion

theorem exists_prim {q : ℕ} [NeZero q] {B : Type} [CommRing B] [HenselianLocalRing B]
    [IsSepClosed (ResidueField B)] (hq : IsUnit (q : B)) : Nonempty (Prim q B) := by
  have := neZero_res hq
  obtain ⟨μ, hμ⟩ := IsSepClosed.exists_root (cyclotomic q (ResidueField B))
    (degree_cyclotomic_pos q _ (Nat.pos_of_ne_zero (NeZero.ne q))).ne' (separable_cyclotomic q _)
  obtain ⟨a0, rfl⟩ := residue_surjective μ
  have hev : residue B (eval a0 (cyclotomic q B)) = eval (residue B a0) (cyclotomic q (ResidueField B)) := by
    rw [← Polynomial.eval₂_hom, ← Polynomial.eval_map, map_cyclotomic]
  have hder : residue B (eval a0 (derivative (cyclotomic q B))) =
      eval (residue B a0) (derivative (cyclotomic q (ResidueField B))) := by
    rw [← Polynomial.eval₂_hom, ← Polynomial.eval_map, ← Polynomial.derivative_map, map_cyclotomic]
  obtain ⟨a, ha, -⟩ := HenselianLocalRing.is_henselian (cyclotomic q B) (cyclotomic.monic q B) a0
    (by rw [← residue_eq_zero_iff, hev]; exact hμ)
    (by
      apply isUnit_of_map_unit (residue B)
      rw [hder, isUnit_iff_ne_zero]
      have h := (separable_cyclotomic q (ResidueField B)).aeval_derivative_ne_zero
        (x := residue B a0) (by rw [Polynomial.coe_aeval_eq_eval]; exact hμ)
      rwa [Polynomial.coe_aeval_eq_eval] at h)
  exact ⟨⟨a, hq, by rw [aeval_cyc]; exact ha⟩⟩

end LateralTheory.KummerTheory.PrimitiveRootTorsion

namespace LateralTheory.KummerTheory
open LateralTheory.KummerTheory.PrimitiveRootTorsion

theorem PrimTors_of : PrimTors := by
  intro q _ B _ hSH hq
  obtain ⟨_, _⟩ := hSH
  refine ⟨exists_prim hq, fun i ζ => ?_⟩
  classical
  have hex : ∀ ξ : Prim q B, ∃ a : (ZMod q)ˣ, ξ.1 = ζ.1 ^ (a : ZMod q).val := fun ξ => exists_idx hq ζ ξ
  let ind : Prim q B → (ZMod q)ˣ := fun ξ => (hex ξ).choose
  have hind : ∀ ξ, ξ.1 = ζ.1 ^ (ind ξ : ZMod q).val := fun ξ => (hex ξ).choose_spec
  let v : Prim q B → ULift.{1} (ZMod q) := fun ξ => ULift.up (((ind ξ) ^ i : (ZMod q)ˣ) : ZMod q)
  let φ := Finsupp.linearCombination (ULift.{1} (ZMod q)) v
  have hker : twRel q i B ≤ LinearMap.ker φ := by
    refine Submodule.span_le.2 ?_
    rintro x ⟨ζ', ξ, a, h, rfl⟩
    have hi : ind ξ = a * ind ζ' := idx_unique hq ζ (by rw [← hind ξ]; exact idx_mul (hind ζ') h)
    change φ _ = 0
    rw [map_sub, Finsupp.linearCombination_single, Finsupp.linearCombination_single, sub_eq_zero]
    apply ULift.ext
    simp [v, hi, mul_zpow]
  let ψ := (twRel q i B).liftQ φ hker
  constructor
  · intro t t' h
    have h2 := congrArg ψ h
    simp only [LinearMap.map_smul, ψ, Submodule.liftQ_apply, φ, Finsupp.linearCombination_single,
      one_smul] at h2
    have h3 := congrArg ULift.down h2
    change t * (((ind ζ) ^ i : (ZMod q)ˣ) : ZMod q) = t' * (((ind ζ) ^ i : (ZMod q)ˣ) : ZMod q) at h3
    exact (Units.mul_left_inj _).1 h3
  · intro y
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    induction x using Finsupp.induction_linear with
    | zero => exact ⟨0, by simp⟩
    | add f g hf hg =>
      obtain ⟨a, ha⟩ := hf
      obtain ⟨b, hb⟩ := hg
      refine ⟨a + b, ?_⟩
      simp only at ha hb ⊢
      rw [Submodule.Quotient.mk_add, ← ha, ← hb, ← add_smul]
      rfl
    | single ξ c =>
      have hmem : Finsupp.single ξ 1 - Finsupp.single ζ (ULift.up (((ind ξ) ^ i : (ZMod q)ˣ) : ZMod q)) ∈
          twRel q i B := Submodule.subset_span ⟨ζ, ξ, ind ξ, hind ξ, rfl⟩
      have he : (Submodule.Quotient.mk (Finsupp.single ξ 1) : _ ⧸ twRel q i B) =
          Submodule.Quotient.mk (Finsupp.single ζ (ULift.up (((ind ξ) ^ i : (ZMod q)ˣ) : ZMod q))) :=
        (Submodule.Quotient.eq _).2 hmem
      refine ⟨(c * ULift.up (((ind ξ) ^ i : (ZMod q)ˣ) : ZMod q)).down, ?_⟩
      have hs : Finsupp.single ζ (ULift.up (((ind ξ) ^ i : (ZMod q)ˣ) : ZMod q)) =
          (ULift.up (((ind ξ) ^ i : (ZMod q)ˣ) : ZMod q)) • Finsupp.single ζ (1 : ULift.{1} (ZMod q)) := by
        rw [Finsupp.smul_single_one]
      simp only [ULift.up_down]
      rw [← Finsupp.smul_single_one ξ c, Submodule.Quotient.mk_smul, he, hs, Submodule.Quotient.mk_smul, smul_smul]

end LateralTheory.KummerTheory
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.KummerTheory.RedExPf
open LateralTheory.KummerTheory.BockCut

theorem nsmul_congr {q : ℕ} {i : ℤ} {U : Scheme.{0}} (y : Sec (tw q i) U) {n m : ℕ}
    (h : (n : ZMod q) = (m : ZMod q)) : n • y = m • y := by
  rw [← Nat.cast_smul_eq_nsmul (ULift.{1} (ZMod q)) n y, ← Nat.cast_smul_eq_nsmul (ULift.{1} (ZMod q)) m y]
  congr 1
  exact ULift.ext (by simpa using h)

theorem RedEx_of (hZ : ZHom) (hT : LateralTheory.EtaleFoundations.EtaleTateTwistSectionsLocallyGenerated) (hP : LateralTheory.EtaleFoundations.PrimitiveRootsOfUnityBasicIdentities) : RedEx := by
  intro Q q _ h i
  have hq : NeZero q := ⟨ne_zero_of_dvd_ne_zero (NeZero.ne Q) h⟩
  choose ρ hρ using fun (U : Scheme.{0}) (ζ : Prim Q Γ(U, ⊤)) => (hP Q Γ(U, ⊤)).2.2.2.2.2 q h ζ
  let M : Shv (ZMod Q) := (restr (ZMod.castHom h (ZMod q))).obj (tw q i)
  let e : ∀ U : Scheme.{0}, Prim Q Γ(U, ⊤) → Sec M U := fun U ζ => (twGen i (ρ U ζ) : Sec (tw q i) U)
  have he1 : ∀ (V U : Scheme.{0}) (g : V ⟶ U) ζ, Sec.res g (e U ζ) = e V (ζ.map g.appTop.hom) := by
    intro V U g ζ
    have hx : ρ V (ζ.map g.appTop.hom) = (ρ U ζ).map g.appTop.hom := by
      apply Subtype.ext
      rw [hρ]
      show (g.appTop.hom ζ.1) ^ (Q / q) = g.appTop.hom ((ρ U ζ).1)
      rw [hρ, map_pow]
    show Sec.res (F := tw q i) g (twGen i (ρ U ζ)) = twGen i (ρ V (ζ.map g.appTop.hom))
    rw [hx, (hT q i).2.2.2.1]
  have he2 : ∀ (U : Scheme.{0}) (ζ ξ : Prim Q Γ(U, ⊤)) (a : (ZMod Q)ˣ), ξ.1 = ζ.1 ^ (a : ZMod Q).val →
      e U ξ = ((a ^ i : (ZMod Q)ˣ) : ZMod Q).val • e U ζ := by
    intro U ζ ξ a hξa
    let b : (ZMod q)ˣ := ZMod.unitsMap h a
    have hb : ∀ x : ZMod Q, ((ZMod.castHom h (ZMod q) x : ZMod q)) = (x.val : ZMod q) := fun x =>
      ZMod.cast_eq_val x
    have hpow : (ρ U ξ).1 = (ρ U ζ).1 ^ (b : ZMod q).val := by
      have h1 : (ρ U ζ).1 ^ q = 1 := (hP q Γ(U, ⊤)).1 (ρ U ζ)
      have hbv : (b : ZMod q).val = (a : ZMod Q).val % q := by
        show (ZMod.castHom h (ZMod q) (a : ZMod Q)).val = _
        rw [hb, ZMod.val_natCast]
      rw [hρ, hρ, hξa, hbv, ← pow_mul, mul_comm, pow_mul]
      conv_lhs => rw [← Nat.div_add_mod (a : ZMod Q).val q]
      rw [hρ] at h1
      rw [pow_add, pow_mul, h1, one_pow, one_mul]
    show twGen i (ρ U ξ) = _ • (twGen i (ρ U ζ) : Sec (tw q i) U)
    rw [(hT q i).2.2.2.2.1 U (ρ U ζ) (ρ U ξ) b hpow]
    apply nsmul_congr
    rw [ZMod.natCast_zmod_val]
    have : ((b ^ i : (ZMod q)ˣ) : ZMod q) = ZMod.castHom h (ZMod q) ((a ^ i : (ZMod Q)ˣ) : ZMod Q) := by
      rw [show b ^ i = ZMod.unitsMap h (a ^ i) from (map_zpow _ _ _).symm]
      rfl
    rw [this, hb]
  obtain ⟨φ, hφ, -⟩ := (hT Q i).2.2.2.2.2 M e he1 he2
  obtain ⟨π, hπ⟩ := hZ (TZ Q i) (TZ q i)
    (fun U => AddMonoidHom.mk' (fun a => (Sec.map φ (show Sec (tw Q i) U from a) : Sec (tw q i) U))
      (fun a b => map_add (φ.hom.app (op U)).hom a b))
    (fun V U g a => by
      have := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom (φ.hom.naturality g.op)) a
      exact this.symm)
  refine ⟨π, fun U ζ ξ hξ => ?_⟩
  rw [hπ]
  have hx : ξ = ρ U ζ := Subtype.ext (by rw [hξ, hρ])
  subst hx
  exact hφ U ζ

end LateralTheory.KummerTheory.RedExPf
end
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.KummerTheory.TwSESPf
open LateralTheory.KummerTheory.BockCut

theorem smap_add {R : Type} [CommRing R] {F G : Shv R} (f g : F ⟶ G) {U : Scheme.{0}} (x : Sec F U) :
    Sec.map (f + g) x = Sec.map f x + Sec.map g x := by
  show ((f+g).hom.app (op U)).hom x = (f.hom.app (op U)).hom x + (g.hom.app (op U)).hom x
  simp

theorem smap_zero {R : Type} [CommRing R] {F G : Shv R} {U : Scheme.{0}} (x : Sec F U) :
    Sec.map (0 : F ⟶ G) x = 0 := by
  show ((0 : F ⟶ G).hom.app (op U)).hom x = 0
  simp

theorem smap_nsmul {R : Type} [CommRing R] {F G : Shv R} (f : F ⟶ G) (n : ℕ) {U : Scheme.{0}}
    (x : Sec F U) : Sec.map (n • f) x = n • Sec.map f x := by
  induction n with
  | zero => simp [smap_zero]
  | succ n ih => rw [succ_nsmul, smap_add, ih, succ_nsmul]

theorem smap_comp {R : Type} [CommRing R] {F G H : Shv R} (f : F ⟶ G) (g : G ⟶ H) {U : Scheme.{0}}
    (x : Sec F U) : Sec.map (f ≫ g) x = Sec.map g (Sec.map f x) := rfl

theorem smap_id {R : Type} [CommRing R] {F : Shv R} {U : Scheme.{0}} (x : Sec F U) :
    Sec.map (𝟙 F) x = x := rfl

theorem sres_zero {R : Type} [CommRing R] {F : Shv R} {V U : Scheme.{0}} (g : V ⟶ U) :
    Sec.res g (0 : Sec F U) = 0 := map_zero _

theorem smap_res {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U)
    (x : Sec F U) : Sec.map φ (Sec.res g x) = Sec.res g (Sec.map φ x) := by
  show (φ.hom.app (op V)).hom ((F.obj.map g.op).hom x) = (G.obj.map g.op).hom ((φ.hom.app (op U)).hom x)
  rw [← ModuleCat.comp_apply, ← ModuleCat.comp_apply, φ.hom.naturality]

theorem tz_kill (q : ℕ) (i : ℤ) {U : Scheme.{0}} (y : Sec (TZ q i) U) : q • y = 0 := by
  change q • (show ((tw q i).obj.obj (op U) : ModuleCat (ULift (ZMod q))) from y) = 0
  rw [← Nat.cast_smul_eq_nsmul (ULift (ZMod q))]
  have : ((q : ℕ) : ULift (ZMod q)) = 0 := by ext; simp
  rw [this, zero_smul]

theorem TwSES_of (hEpi : RedEpi) (hKer : RedKer) (hME : LateralTheory.EtaleFoundations.EtaleSheafMonoEpiSectionCriteria)
    (hEx : LateralTheory.EtaleFoundations.EtaleSheafShortComplexExactIffLocallyLifts) (hL : LateralTheory.EtaleFoundations.EtaleLocalPropertyBasicClosure) : TwSES := by
  intro l _ b a i π₁ π₂ h₁ h₂
  have : NeZero (l ^ (b + a)) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  have : Epi π₁ := hEpi l (b + a) a (by omega) i π₁ h₁
  have : Epi π₂ := hEpi l (b + a) b (by omega) i π₂ h₂
  have hm1 : l ^ (b + a) = l ^ b * l ^ a := pow_add _ _ _
  have hm2 : l ^ (b + a) = l ^ a * l ^ b := by rw [pow_add, mul_comm]
  have hk : kernel.ι π₁ ≫ (l ^ b • 𝟙 _) = 0 := by
    refine ((hME ℤ (kernel.ι π₁ ≫ (l ^ b • 𝟙 _))).2.2.2 0 fun U x => ?_)
    rw [smap_zero, smap_comp, smap_nsmul, smap_id]
    exact ((hKer _ _ _ hm1 i π₁ h₁ U _).1).1 (by rw [← smap_comp, kernel.condition, smap_zero])
  let ι := Abelian.epiDesc π₁ (l ^ b • 𝟙 _) hk
  have hι : π₁ ≫ ι = l ^ b • 𝟙 _ := Abelian.comp_epiDesc _ _ _
  have hιs : ∀ {U : Scheme.{0}} (y : Sec (TZ (l ^ (b + a)) i) U), Sec.map ι (Sec.map π₁ y) = l ^ b • y := by
    intro U y; rw [← smap_comp, hι, smap_nsmul, smap_id]
  have w : ι ≫ π₂ = 0 := by
    rw [← cancel_epi π₁, ← Category.assoc, hι, comp_zero]
    refine ((hME ℤ _).2.2.2 0 fun U y => ?_)
    rw [smap_zero, smap_comp, smap_nsmul, smap_id]
    refine ((hKer _ _ _ hm2 i π₂ h₂ U _).1).2 ?_
    rw [smul_smul, ← hm2]; exact tz_kill _ _ _
  refine ⟨ι, hι, w, ?_⟩
  have : Mono ι := by
    refine (hME ℤ ι).2.1.2 fun U x hx => ?_
    refine hL.2.1 _ _ _ ((hME ℤ π₁).2.2.1.1 ‹_› U x) fun V g ⟨y, hy⟩ => ?_
    rw [← hy]
    refine ((hKer _ _ _ hm1 i π₁ h₁ V y).1).2 ?_
    rw [← hιs, hy, smap_res, hx, sres_zero]
  refine ShortComplex.ShortExact.mk' ?_ ‹Mono ι› ‹Epi π₂›
  refine (hEx ℤ _).2 fun U y hy => ?_
  refine hL.2.1 _ _ _ ((hKer _ _ _ hm2 i π₂ h₂ U y).2 hy) fun V g ⟨x, hx⟩ => ⟨Sec.map π₁ x, ?_⟩
  show Sec.map ι (Sec.map π₁ x) = _
  rw [hιs, hx]

end LateralTheory.KummerTheory.TwSESPf
end
