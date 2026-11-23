module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.CharZeroOfIsPrimitiveRoot
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsPowEqOfBaseChange
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle078
public import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.ExistsLevelStructureOfWeilPairing
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle002
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle007
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.WittVector.IsPoly
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

@[expose] public section

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex

namespace GlobalTheory.GaugeValues

theorem vF_eq {F : Type} [Field F] {X Y : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    {J : (Sp F ⟶ X) → L.ι} (hJ : ∀ ψ : Sp F ⟶ X, ⊤ ≤ ψ ⁻¹ᵁ L.U (J ψ)) (z : Sp F) (t : LB.Gen (LB.LinComb L φ ε))
    (r : Sp F ⟶ Y) : (((TorusExt.stalkUnits z).symm (val t r z J) : Fˣ) : F) = vF t r J := by
  have h : ⊤ ≤ r ⁻¹ᵁ LB.wchart L φ (fun k => J (r ≫ φ k)) := fun w _ =>
    Good.mem (L := L) (z := w) (J := J) (fun ψ => hJ ψ trivial) φ r
  refine (TorusExt.stalkConst z).injective ?_
  rw [← TorusExt.stalkUnits_val, MulEquiv.apply_symm_apply]
  exact (gs_unit r z _ (h trivial) _).symm.trans (TorusExt.gs_eq_stalkConst r z h _)

variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R)

theorem val_sym_one {T : Over (Spec (CommRingCat.of R))} {z : T.left} {J} (hJ : Good D.P.L z J) :
    val D.sym (1 : T ⟶ D.P.A).left z J = 1 := by
  have s := val_corr hJ D.sym_rig (toUnit T).left
  rw [val_pull hJ, val_one] at s
  exact s

theorem prod_sym {T : Over (Spec (CommRingCat.of R))} (x : T ⟶ D.P.A) {U : Type} [CommGroup U]
    (h : (T.left ⟶ D.P.A.left) → U) :
    ∏ i : Fin 2, h (x.left ≫ ![(ι[D.P.A]).left, 𝟙 D.P.A.left] i) ^ (![1, -1] : Fin 2 → ℤ) i =
      h (x⁻¹).left * (h x.left)⁻¹ := by
  rw [Fin.prod_univ_two]
  show h (x ≫ ι[D.P.A]).left ^ (1 : ℤ) * h (x.left ≫ 𝟙 _) ^ (-1 : ℤ) = _
  rw [zpow_one, zpow_neg_one, Category.comp_id]; rfl

theorem val_sym_mul (hG : GlobalFnsSt) {T : Over (Spec (CommRingCat.of R))} {z : T.left} {J} (hJ : Good D.P.L z J)
    (x y : T ⟶ D.P.A) :
    val D.sym (x * y).left z J * cubV D.cub z J x x⁻¹ y⁻¹ =
      val D.sym x.left z J * val D.sym y.left z J * cubV D.cub z J y y⁻¹ x := by
  let p : D.P.A ⊗ D.P.A ⟶ D.P.A := fst _ _
  let q : D.P.A ⊗ D.P.A ⟶ D.P.A := snd _ _
  have ev : ∀ {T' : Over (Spec (CommRingCat.of R))} (a b : T' ⟶ D.P.A) {z : T'.left} {J}, Good D.P.L z J →
      val (LB.mulGen D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ D.sym (p * q).left)
        (LB.pullGen D.P.L (thφ D.P.A (x3 D.P.A)) thε D.cub.t (lift p (lift p⁻¹ q⁻¹)).left)) (lift a b).left z J =
        val D.sym (a * b).left z J * cubV D.cub z J a a⁻¹ b⁻¹ ∧
      val (LB.mulGen D.P.L _ _ _ _ (LB.mulGen D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ D.sym p.left)
        (LB.pullGen D.P.L _ _ D.sym q.left))
        (LB.pullGen D.P.L (thφ D.P.A (x3 D.P.A)) thε D.cub.t (lift q (lift q⁻¹ p)).left)) (lift a b).left z J =
        val D.sym a.left z J * val D.sym b.left z J * cubV D.cub z J b b⁻¹ a := by
    intro T' a b z J hJ
    have e₁ : lift a b ≫ p = a := lift_fst _ _
    have e₂ : lift a b ≫ q = b := lift_snd _ _
    have e₃ : lift a b ≫ (p * q) = a * b := (MonObj.comp_mul _ _ _).trans (by rw [e₁, e₂])
    have e₄ : lift a b ≫ p⁻¹ = a⁻¹ := (map_inv (preHom (lift a b)) p).trans (congrArg (·⁻¹) e₁)
    have e₅ : lift a b ≫ q⁻¹ = b⁻¹ := (map_inv (preHom (lift a b)) q).trans (congrArg (·⁻¹) e₂)
    have vs : ∀ w : D.P.A ⊗ D.P.A ⟶ D.P.A, val (LB.pullGen D.P.L _ _ D.sym w.left) (lift a b).left z J =
        val D.sym (lift a b ≫ w).left z J := fun w => val_pull hJ _ _ _
    refine ⟨((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (vs _) (val_cub D.cub _ hJ _ _ _))).trans ?_,
      ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (vs _) (vs _)))
        (val_cub D.cub _ hJ _ _ _))).trans ?_⟩
    · rw [e₁, e₃, e₄, e₅]
    · rw [e₁, e₂, e₅]
  let e : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ D.P.A ⊗ D.P.A := lift 1 1
  have he : e.left ≫ (snd D.P.A D.P.A).left ≫ D.P.A.hom = 𝟙 _ := by
    rw [Over.w]; exact Over.w e
  refine (ev x y hJ).1.symm.trans (Eq.trans (gen_unique' D.P.isLB (fun V _ k => ?_) _ e.left he
    (surj_comp (surj_snd hG D.P.isAb _) (hG _ _ D.P.isAb).2)
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ _ D.sym_gen _) (DVR.pullGen_isGen _ _ _ _ D.cub.isGen _))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ _ D.sym_gen _)
      (DVR.pullGen_isGen _ _ _ _ D.sym_gen _)) (DVR.pullGen_isGen _ _ _ _ D.cub.isGen _))
    (fun w I hI => ?_) _ (lift x y).left z J hJ) (ev x y hJ).2)
  · refine (DVR.prod_sum₂ (K := Fin 2 ⊕ Fin 2) (K' := thK) (U := V) _
      (DVR.prod_sum₂ (K := Fin 2) (K' := Fin 2) (U := V) _ (prod_sym D p k) (prod_sym D q k))
      (prod_cub q q⁻¹ p k)).trans (Eq.trans ?_ (DVR.prod_sum₂ (K := Fin 2) (K' := thK) (U := V) _
        (prod_sym D (p * q) k) (prod_cub p p⁻¹ q⁻¹ k)).symm)
    rw [mul_inv_cancel, mul_inv_cancel, _root_.one_mul, _root_.one_mul, mul_inv, mul_comm q p, mul_comm q⁻¹ p]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  · have C : IsCub (cubV D.cub (T := 𝟙_ (Over (Spec (CommRingCat.of R)))) w I) := isCub_cubV D.cub hI
    refine (ev 1 1 hI).1.trans (Eq.trans ?_ (ev 1 1 hI).2.symm)
    rw [_root_.mul_one, C.face, C.face, val_sym_one D hI, _root_.mul_one, _root_.mul_one]

theorem exists_numOf : Laws → ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R), D.PsiEven → D.TauBimult → ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] (J : (Sp F ⟶ D.P.A.left) → D.P.L.ι), (∀ ψ, ⊤ ≤ ψ ⁻¹ᵁ D.P.L.U (J ψ)) → ∀ th : H0 D.P.L 1, (∀ s : H0 D.P.L 1, ∃ r : R, ∀ j, s.f j = resTop _ (scal D.P.A.hom r) * th.f j) → ∃ (N : NumD F) (ν : NumOf D F N), ν.J = J ∧ ν.th = th := by
  intro hL R _ _ D hE hB F _ _ J hJ th hth
  let z : (TF (R := R) F).left := IsLocalRing.closedPoint F
  have g : Good D.P.L z J := fun ψ => hJ ψ trivial
  let u : ((TF (R := R) F).left.presheaf.stalk z)ˣ ≃* Fˣ := (TorusExt.stalkUnits (F := F) z).symm
  have C : IsCub (cubV D.cub (T := TF (R := R) F) z J) := isCub_cubV D.cub g
  let ρ : ((TF (R := R) F).left.presheaf.stalk z)ˣ := val (L := D.P.L) (φ := fun _ : PUnit => eSec D.P.A)
    (ε := fun _ => 1) D.rig (TF (R := R) F).hom z J
  let P : D.X → ((TF (R := R) F).left.presheaf.stalk z)ˣ := fun χ =>
    val (Z := (TF (R := R) F).left) (D.psi χ) (jFK (R := R) F) z J
  obtain ⟨b, e⟩ := TauValues.main R D F
  let N : NumD F :=
    { A := TF (R := R) F ⟶ D.P.A
      θ := fun x y w => u (cubV D.cub z J x y w)
      cub := ⟨fun x y => (congrArg u (C.face x y)).trans (map_one u), fun x y w => congrArg u (C.s01 x y w),
        fun x y w => congrArg u (C.s12 x y w), fun x x' x'' y =>
          (map_mul u _ _).symm.trans ((congrArg u (C.coc x x' x'' y)).trans (map_mul u _ _))⟩
      σ := fun x => u (val D.sym x.left z J)
      σ_one := (congrArg u (val_sym_one D g)).trans (map_one u)
      σ_mul := fun x y => by
        simpa only [map_mul] using congrArg u (val_sym_mul D hL.globalFns g x y)
      th := fun x => sF th x.left J * ((u ρ)⁻¹ : Fˣ)
      X := D.X
      c := DegPre.cF D F
      c_add := fun a a' => (congrArg (toUnit _ ≫ ·) (D.c_add a a')).trans (MonObj.comp_mul _ _ _)
      ψ := fun χ => u (P χ * ρ)
      even := fun χ => by
        have h : P (-χ) * val D.sym (DegPre.cF D F χ).left z J = P χ := e.2 hE z J g χ
        rw [← map_mul, mul_right_comm, h]
      bimult := fun a a' m => by
        have h : P (a + a' + m) * P a * P a' * P m * ρ *
            cubV D.cub z J (DegPre.cF D F a) (DegPre.cF D F a') (DegPre.cF D F m) =
            P (a + a') * P (a + m) * P (a' + m) := b.2 hB z J g a a' m
        simp only [← map_div, ← map_mul]
        refine congrArg u (Additive.ofMul.injective ?_)
        have h' := congrArg Additive.ofMul h
        simp only [ofMul_mul, ofMul_div] at h' ⊢
        linear_combination (norm := abel) h' }
  have hρ : ((u ρ : Fˣ) : F) = vF (L := D.P.L) (φ := fun _ : PUnit => eSec D.P.A) (ε := fun _ => 1) D.rig
      (TF (R := R) F).hom J := vF_eq hJ z _ _
  exact ⟨N,
    { J := J, good := hJ, th := th, th_gen := hth, eA := MulEquiv.refl _, eX := AddEquiv.refl _
      c_eq := fun _ => rfl
      θ_eq := fun _ _ _ => vF_eq hJ z _ _
      σ_eq := fun _ => vF_eq hJ z _ _
      th_eq := fun x => (congrArg (N.th x * ·) hρ.symm).trans (Units.inv_mul_cancel_right _ _)
      ψ_eq := fun χ => (congrArg Units.val (map_mul u _ _)).trans ((Units.val_mul _ _).trans
        (congrArg₂ (· * ·) (vF_eq hJ z _ _) hρ)) }, rfl, rfl⟩

end GlobalTheory.GaugeValues
end

section

set_option autoImplicit false

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex

noncomputable section

namespace GlobalTheory.FullLevel

section Abstract

variable {G L : Type} [CommGroup G] [AddCommGroup L] {r n : ℕ} {ev : L → G}

theorem ev_basis (add : ∀ a b, ev (a + b) = ev a * ev b) (bas : (Fin r → ℤ) ≃ₗ[ℤ] L) (c : Fin r → ℤ) :
    ev (bas c) = ∏ i, ev (bas (Pi.single i 1)) ^ c i := by
  let f : L →+ Additive G := AddMonoidHom.mk' (fun a => Additive.ofMul (ev a)) fun a b => by rw [add, ofMul_mul]
  have hc : c = ∑ i, c i • (Pi.single i 1 : Fin r → ℤ) := by
    funext j
    simp [Finset.sum_apply, Pi.single_apply]
  have h : f (bas c) = ∑ i, c i • f (bas (Pi.single i 1)) := by
    conv_lhs => rw [hc]

    simp only [map_sum, map_zsmul]
  have h' := congrArg Additive.toMul h
  rw [toMul_sum] at h'
  simp only [toMul_zsmul] at h'
  exact h'

theorem card_torsion (hn : 0 < n) (add : ∀ a b, ev (a + b) = ev a * ev b) (ker : ∀ a, ev a = 1 ↔ ∃ b, a = n • b)
    (onto : ∀ x, x ^ n = 1 ↔ ∃ a, ev a = x) (bas : (Fin r → ℤ) ≃ₗ[ℤ] L) :
    Nat.card {x : G // x ^ n = 1} = n ^ r := by
  let f : (Fin r → Fin n) → {x : G // x ^ n = 1} := fun c => ⟨ev (bas fun i => (c i : ℕ)), (onto _).2 ⟨_, rfl⟩⟩
  have hn' : (0 : ℤ) < n := by exact_mod_cast hn
  have hb : Function.Bijective f := by
    refine ⟨fun c c' h => ?_, fun x => ?_⟩
    · have h₁ : ev (bas fun i => (c i : ℕ)) = ev (bas fun i => (c' i : ℕ)) := congrArg Subtype.val h
      have h₂ := add (bas (fun i => (c i : ℕ)) - bas fun i => (c' i : ℕ)) (bas fun i => (c' i : ℕ))
      rw [sub_add_cancel, h₁] at h₂
      obtain ⟨b, hb⟩ := (ker _).1 (mul_eq_right.1 h₂.symm)
      obtain ⟨b, rfl⟩ := bas.surjective b
      rw [← map_sub, ← map_nsmul] at hb
      funext i
      have h₃ : ((c i : ℕ) : ℤ) - (c' i : ℕ) = n * b i := by simpa using congrFun (bas.injective hb) i
      have h₄ : ((c' i : ℕ) : ℤ) ≡ (c i : ℕ) [ZMOD n] := (Int.modEq_iff_dvd).2 ⟨_, h₃⟩
      exact Fin.ext (Nat.ModEq.eq_of_lt_of_lt (Int.natCast_modEq_iff.1 h₄) (c' i).2 (c i).2).symm
    · obtain ⟨a, ha⟩ := (onto _).1 x.2
      obtain ⟨a, rfl⟩ := bas.surjective a
      have h₀ : ∀ i, 0 ≤ a i % n := fun i => Int.emod_nonneg _ hn'.ne'
      refine ⟨fun i => ⟨(a i % n).toNat, by have := Int.emod_lt_of_pos (a i) hn'; have := h₀ i; omega⟩,
        Subtype.ext ?_⟩
      have e : a = (fun i => (((a i % n).toNat : ℕ) : ℤ)) + n • fun i => a i / n := by
        funext i
        simp only [Pi.add_apply, Pi.smul_apply, nsmul_eq_mul, Int.toNat_of_nonneg (h₀ i)]
        exact (Int.emod_add_mul_ediv _ _).symm
      rw [← ha]
      conv_rhs => rw [e, map_add (f := _), add, map_nsmul, (ker _).2 ⟨_, rfl⟩, _root_.mul_one]
  rw [← Nat.card_eq_of_bijective f hb]
  simp

end Abstract

end GlobalTheory.FullLevel

namespace GlobalTheory


open FullLevel in
theorem exists_level_of_full : Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H), ∀ (g : ℕ) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] D.La), (∀ i j, D.EF (bas (Pi.single i 1)) (bas (Pi.single j 1)) = stdSymp g i j) → ∀ (K : Type) [Field K] [IsAlgClosed K] (o : Full D K) (M : ℕ), 0 < M → ∃ (hg : o.P.g = g) (lev : Out.Level o.P M (unitOn (o.I.ζ M))), (∀ i, levelBasis lev hg i = o.I.ev M (bas (Pi.single i 1))) ∧ ∀ c : Fin (2 * g) → ℤ, levelPoint lev hg (fun i => (c i : ZMod M)) = o.I.ev M (bas c) := by
  intro hL E _ _ _ H D g bas hb K _ _ o M hM
  have := o.charZero
  have := o.P.isAb.comm
  have : NeZero M := ⟨hM.ne'⟩
  have hg : o.P.g = g := by
    have h₁ := (hL.mulN _ o.P 2 one_le_two).2.2.2.2 K (𝟙 _) (by norm_num)
    have h₂ := card_torsion (G := baseOver (Sp K) ⟶ o.P.A) two_pos (o.I.add 2) (o.I.ker 2 two_pos)
      (o.I.onto 2 two_pos) bas
    have h₃ := Nat.pow_right_injective le_rfl (h₁.symm.trans h₂)
    omega
  subst hg
  have prim : ∀ {R : Type} [CommRing R] [Nontrivial R] (φ : K →+* R),
      IsPrimitiveRoot (Units.map φ.toMonoidHom (o.I.ζ M)) M := fun φ =>
    (o.I.ζ_prim M hM).map_of_injective (f := Units.map φ.toMonoidHom) (Units.map_injective φ.injective)
  have nt : ∀ (F : Type) [Field F], Nontrivial Γ(Spec (CommRingCat.of F), ⊤) := fun F _ =>
    (Scheme.ΓSpecIso (CommRingCat.of F)).commRingCatIsoToRingEquiv.toEquiv.nontrivial
  have tor : ∀ a, o.I.ev M a ^ M = 1 := fun a => (o.I.onto M hM _).2 ⟨a, rfl⟩
  obtain ⟨lev, hlev⟩ := exists_level_of_pairing hL.globalFns hL.weil hL.mulN (Sp K) o.P M (unitOn (o.I.ζ M))
    (by have := nt K; exact prim (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom)
    (fun F _ s => by
      have := nt F
      refine ⟨?_, prim (s.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom)⟩
      have : CharZero F := charZero_of_injective_ringHom (Spec.preimage s).hom.injective
      exact Nat.cast_ne_zero.2 hM.ne')
    (fun i => o.I.ev M (bas (Pi.single i 1))) (fun i => tor _)
    (fun i j => by
      have h := o.I.isom M hM (bas (Pi.single i 1)) (bas (Pi.single j 1))
      rw [hb] at h
      have e : unitOn (o.I.ζ M ^ stdSymp o.P.g i j) = unitOn (o.I.ζ M) ^ stdSymp o.P.g i j := map_zpow _ _ _
      exact e ▸ h)
  refine ⟨rfl, lev, fun i => congrFun hlev i, fun c => ?_⟩
  rw [levelPoint_rfl, Level.toPt, hlev, ev_basis (G := baseOver (Sp K) ⟶ o.P.A) (o.I.add M) bas c, linComb,
    List.prod_ofFn]
  exact Finset.prod_congr rfl fun i _ => by rw [← zpow_natCast, ZMod.val_intCast, ← zpow_eq_zpow_emod' _ (tor _)]

end GlobalTheory
end
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN

noncomputable section
namespace GlobalTheory.LN.FourthSide

local instance (priority := high) grpObjFourthSideThick {R : Type} [CommRing R] (I : Ideal R) (e : ℕ)
    (G : Over (Spec (CommRingCat.of R))) [GrpObj G] : GrpObj (thickObj R I e G) :=
  letI : (Over.pullback (thick R I e)).Monoidal :=
    (Over.instBraidedPullback (f := thick R I e)).toMonoidal
  Functor.grpObjObj (F := Over.pullback (thick R I e))

section General
variable {S Z : Scheme.{0}} {G : Over S} [GrpObj G] {s s' : Z ⟶ S}

theorem mul_left_congr {x y : Over.mk s ⟶ G} {x' y' : Over.mk s' ⟶ G} (hx : x.left = x'.left)
    (hy : y.left = y'.left) : (x * y).left = (x' * y').left := by
  obtain rfl : s = s' := (Over.w x).symm.trans ((congrArg (· ≫ G.hom) hx).trans (Over.w x'))
  rw [Over.OverMorphism.ext hx, Over.OverMorphism.ext hy]

theorem cubV_congr [IsCommMonObj G] {L : RigLB G} (c : CubicalStr G L) (z : Z) (J) {x y u : Over.mk s ⟶ G}
    {x' y' u' : Over.mk s' ⟶ G} (hx : x.left = x'.left) (hy : y.left = y'.left) (hu : u.left = u'.left) :
    @id (Z.presheaf.stalk z)ˣ (cubV c (T := Over.mk s) z J x y u) =
      @id (Z.presheaf.stalk z)ˣ (cubV c (T := Over.mk s') z J x' y' u') := by
  obtain rfl : s = s' := (Over.w x).symm.trans ((congrArg (· ≫ G.hom) hx).trans (Over.w x'))
  rw [Over.OverMorphism.ext hx, Over.OverMorphism.ext hy, Over.OverMorphism.ext hu]

end General

theorem cube_alg {A A₀ A₁ A₂ M : Type} [CommGroup A] [CommGroup A₀] [CommGroup A₁] [CommGroup A₂] [CommGroup M]
    (n : A →* A₀) (a : A →* A₁) (b : A →* A₂) {W : A → M} {W₀ : A₀ → M} {W₁ : A₁ → M} {W₂ : A₂ → M}
    (sq : ∀ x, W₂ (b x) * W x = W₀ (n x) * W₁ (a x)) (x y u : A) {C C' E E' : M}
    (h₀ : C * W₀ (n x * n y) * W₀ (n x * n u) * W₀ (n y * n u) * W₀ 1 =
      W₀ (n x * n y * n u) * W₀ (n x) * W₀ (n y) * W₀ (n u) * E)
    (h₁ : E * W₁ (a x * a y) * W₁ (a x * a u) * W₁ (a y * a u) * W₁ 1 =
      W₁ (a x * a y * a u) * W₁ (a x) * W₁ (a y) * W₁ (a u) * E')
    (h₂ : C * W₂ (b x * b y) * W₂ (b x * b u) * W₂ (b y * b u) * W₂ 1 =
      W₂ (b x * b y * b u) * W₂ (b x) * W₂ (b y) * W₂ (b u) * C') :
    C' * W (x * y) * W (x * u) * W (y * u) * W 1 = W (x * y * u) * W x * W y * W u * E' := by
  have e : ∀ x, W x = (W₂ (b x))⁻¹ * (W₀ (n x) * W₁ (a x)) := fun x => eq_inv_mul_of_mul_eq (sq x)
  simp only [e, map_mul, map_one]
  apply Additive.ofMul.injective
  have k₀ := congrArg Additive.ofMul h₀
  have k₁ := congrArg Additive.ofMul h₁
  have k₂ := congrArg Additive.ofMul h₂
  simp only [ofMul_mul, ofMul_inv] at k₀ k₁ k₂ ⊢
  linear_combination (norm := abel) k₀ + k₁ - k₂

theorem sym_alg {A A₀ A₁ A₂ M : Type} [CommGroup A] [CommGroup A₀] [CommGroup A₁] [CommGroup A₂] [CommGroup M]
    (n : A →* A₀) (a : A →* A₁) (b : A →* A₂) {W : A → M} {W₀ : A₀ → M} {W₁ : A₁ → M} {W₂ : A₂ → M}
    (sq : ∀ x, W₂ (b x) * W x = W₀ (n x) * W₁ (a x)) (x : A) {C C' E E' : M}
    (h₀ : C * W₀ (n x) = W₀ (n x)⁻¹ * E) (h₁ : E * W₁ (a x) = W₁ (a x)⁻¹ * E')
    (h₂ : C * W₂ (b x) = W₂ (b x)⁻¹ * C') : C' * W x = W x⁻¹ * E' := by
  have e : ∀ x, W x = (W₂ (b x))⁻¹ * (W₀ (n x) * W₁ (a x)) := fun x => eq_inv_mul_of_mul_eq (sq x)
  simp only [e, map_inv]
  apply Additive.ofMul.injective
  have k₀ := congrArg Additive.ofMul h₀
  have k₁ := congrArg Additive.ofMul h₁
  have k₂ := congrArg Additive.ofMul h₂
  simp only [ofMul_mul, ofMul_inv] at k₀ k₁ k₂ ⊢
  linear_combination (norm := abel) k₀ + k₁ - k₂

theorem rig_alg {M : Type} [CommGroup M] {W W₀ W₁ W₂ C C' E E' : M} (sq : W₂ * W = W₀ * W₁) (h₀ : C = W₀ * E)
    (h₁ : E = W₁ * E') (h₂ : C = W₂ * C') : C' = W * E' :=
  mul_left_cancel (a := W₂) (by rw [← h₂, h₀, h₁, ← _root_.mul_assoc, ← _root_.mul_assoc, sq])

theorem pG_mul {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R}
    {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] {e : ℕ} (g : GtCoord I D e G)
    (T : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (x y : T ⟶ thickObj R I e G) :
    toBase (A' := thickObj R I e G) (f := thick R I e) (g := g.pG.left) (Over.w g.pG) (x * y) =
      toBase (Over.w g.pG) x * toBase (Over.w g.pG) y := by
  have := g.q_hom
  have := toBase_mul_pullback D.P.A (thick R I e) T (x ≫ g.q) (y ≫ g.q)
  rw [← MonObj.mul_comp] at this
  have a : ∀ x : T ⟶ thickObj R I e G, toBase (Over.w g.pG) x =
      toBase (A := D.P.A) (g := pullback.fst D.P.A.hom (thick R I e)) pullback.condition (x ≫ g.q) :=
    fun x => Over.OverMorphism.ext (Category.assoc _ _ _).symm
  exact (a _).trans (this.trans (congrArg₂ (· * ·) (a x) (a y)).symm)



theorem fourth_side_vals : ∀ (hG : GlobalFnsSt) (R V : Type) [CommRing R] [IsDomain R] [CommRing V] [IsDomain V] (I : Ideal R) (I' : Ideal V) (φ : R →+* V), I.map φ ≤ I' → ∀ (D : DegPre R) (D' : DegPre V) (A : PolAV (Sp (FractionRing R))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (G' : Over (Spec (CommRingCat.of V))) [GrpObj G'] [IsCommMonObj G'] (U : PreU I D A G) (P' : CP G') (F : G'.left ⟶ G.left) (hF : F ≫ G.hom = G'.hom ≫ spMap φ) (wL : LB.Iso P'.L.L (U.P.L.L.pull F)), IsCPMap P' U.P (spMap φ) F hF wL → ∀ (β : D'.P.A.left ⟶ D.P.A.left) (hβ : β ≫ D.P.A.hom = D'.P.A.hom ≫ spMap φ) (v : LB.Iso D'.P.L (D.P.L.pull β)), IsCPMap (CP.ofDegPre hG D') (CP.ofDegPre hG D) (spMap φ) β hβ v → ∀ (e : ℕ) (g' : GtCoord I' D' e G') (h : (thickObj V I' e G').left ⟶ (thickObj R I e G).left), h ≫ (fstG I e G).left = (fstG I' e G').left ≫ F → g'.pG.left ≫ β = h ≫ (U.gt e).pG.left → ∀ w' : LB.Iso (P'.L.L.pull (fstG I' e G').left) (D'.P.L.pull g'.pG.left), (∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj V I' e G').left) (z : Z) (jM : D.P.L.ι) (jM' : D'.P.L.ι) (jL : U.P.L.L.ι) (jL' : P'.L.L.ι), β (g'.pG.left (r z)) ∈ D.P.L.U jM → g'.pG.left (r z) ∈ D'.P.L.U jM' → F ((fstG I' e G').left (r z)) ∈ U.P.L.L.U jL → (fstG I' e G').left (r z) ∈ P'.L.L.U jL' → gw v (r ≫ g'.pG.left) z jM jM' * gw w' r z jM' (fun _ => jL') = gw (U.w e) (r ≫ h) z jM (fun _ => jL) * gw wL (r ≫ (fstG I' e G').left) z jL jL') → ∀ (T : Over (Spec (CommRingCat.of (V ⧸ I' ^ (e + 1))))) (z : T.left) (JG : (T.left ⟶ G'.left) → P'.L.L.ι) (J : (T.left ⟶ D'.P.A.left) → D'.P.L.ι), Good P'.L.L z JG → Good D'.P.L z J → ∀ W : (T ⟶ thickObj V I' e G') → (T.left.presheaf.stalk z)ˣ, (∀ x, W x = gw w' x.left z (J (x.left ≫ g'.pG.left)) (fun _ => JG (x.left ≫ (fstG I' e G').left))) → (val (L := D'.P.L) (φ := fun _ : PUnit => eSec D'.P.A) (ε := fun _ => 1) D'.rig (T.hom ≫ thick V I' e) z J = W 1 * val (L := P'.L.L) (φ := fun _ : PUnit => eSec G') (ε := fun _ => 1) P'.L.rig (T.hom ≫ thick V I' e) z JG) ∧ (∀ x : T ⟶ thickObj V I' e G', val D'.sym (x.left ≫ g'.pG.left) z J * W x = W x⁻¹ * val P'.sym (x.left ≫ (fstG I' e G').left) z JG) ∧ ∀ x y u : T ⟶ thickObj V I' e G', @id (T.left.presheaf.stalk z)ˣ (cubV D'.cub (T := (Over.map (thick V I' e)).obj T) z J ((Over.map (thick V I' e)).map x ≫ g'.pG) ((Over.map (thick V I' e)).map y ≫ g'.pG) ((Over.map (thick V I' e)).map u ≫ g'.pG)) * W (x * y) * W (x * u) * W (y * u) * W 1 = W (x * y * u) * W x * W y * W u * @id (T.left.presheaf.stalk z)ˣ (cubV P'.c (T := (Over.map (thick V I' e)).obj T) z JG ((Over.map (thick V I' e)).map x ≫ fstG I' e G') ((Over.map (thick V I' e)).map y ≫ fstG I' e G') ((Over.map (thick V I' e)).map u ≫ fstG I' e G')) := by
  intro hG R V _ _ _ _ I I' φ hle D D' A G _ _ G' _ _ U P' F hF wL hwL β hβ v hv e g' h hh hp w' hsq T z JG J hJG hJ W hW
  have hpow : I ^ (e + 1) ≤ (I' ^ (e + 1)).comap φ := by
    rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow]
    exact Ideal.pow_right_mono hle _
  obtain ⟨σ, hσ⟩ : ∃ σ : Spec (CommRingCat.of (V ⧸ I' ^ (e + 1))) ⟶ Spec (CommRingCat.of (R ⧸ I ^ (e + 1))),
      σ ≫ thick R I e = thick V I' e ≫ spMap φ :=
    ⟨spMap (Ideal.quotientMap (I' ^ (e + 1)) φ hpow), by rw [← Spec.map_comp, ← Spec.map_comp]; rfl⟩
  have : IsClosedImmersion (thick R I e) := IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  have := Cmp.mono_fstG I e G
  have hb : (T.hom ≫ σ) ≫ thick R I e = (T.hom ≫ thick V I' e) ≫ spMap φ := by
    rw [Category.assoc, hσ, Category.assoc]
  let a := toBaseHom (toBase_mul_pullback G' (thick V I' e)) T
  let b := toBaseHom (pG_mul g') T
  have ha : ∀ x : T ⟶ thickObj V I' e G', (x.left ≫ h) ≫ (fstG I e G).left = (a x).left ≫ F := fun x =>
    (Category.assoc _ _ _).trans ((congrArg (x.left ≫ ·) hh).trans (Category.assoc _ _ _).symm)
  have hq : ∀ x : T ⟶ thickObj V I' e G', (x.left ≫ h) ≫ (U.gt e).pG.left = (b x).left ≫ β := fun x =>
    (Category.assoc _ _ _).trans ((congrArg (x.left ≫ ·) hp.symm).trans (Category.assoc _ _ _).symm)
  have hs : ∀ x : T ⟶ thickObj V I' e G', (x.left ≫ h) ≫ (thickObj R I e G).hom = T.hom ≫ σ := fun x => by
    rw [← cancel_mono (thick R I e), hb, Category.assoc]
    refine (congrArg ((x.left ≫ h) ≫ ·) (Over.w (fstG I e G)).symm).trans ?_
    refine (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ G.hom) (ha x)).trans ?_)
    exact Over.w (toBase (T := Over.mk (T.hom ≫ thick V I' e)) hF (a x))
  let n₀ : (T ⟶ thickObj V I' e G') → (Over.mk (T.hom ≫ σ) ⟶ thickObj R I e G) :=
    fun x => Over.homMk (x.left ≫ h) (hs x)
  let n : (T ⟶ thickObj V I' e G') →* (Over.mk (T.hom ≫ σ) ⟶ thickObj R I e G) := MonoidHom.mk' n₀ fun x y => by
    refine Over.OverMorphism.ext ((cancel_mono (fstG I e G).left).1 ((ha (x * y)).trans ?_))
    rw [map_mul]
    refine (congrArg (fun q => q.left) (hwL.mul _ (a x) (a y))).trans (Eq.trans ?_
      (congrArg (fun q => q.left) (toBase_mul_pullback G (thick R I e) _ (n₀ x) (n₀ y))).symm)
    exact mul_left_congr (ha x).symm (ha y).symm
  obtain ⟨K, hK⟩ := exists_good_pt U.P.L.isLB z
  obtain ⟨J₀, hJ₀⟩ := exists_good_pt D.P.isLB z
  obtain ⟨W₀, hW₀⟩ : ∃ W₀ : (Over.mk (T.hom ≫ σ) ⟶ thickObj R I e G) → (T.left.presheaf.stalk z)ˣ, ∀ x, W₀ x =
    gw (U.w e) x.left z (J₀ (x.left ≫ (U.gt e).pG.left)) (fun _ => K (x.left ≫ (fstG I e G).left)) :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨W₁, hW₁⟩ : ∃ W₁ : (Over.mk (T.hom ≫ thick V I' e) ⟶ G') → (T.left.presheaf.stalk z)ˣ, ∀ x, W₁ x =
    gw wL x.left z (K (x.left ≫ F)) (JG x.left) := ⟨_, fun _ => rfl⟩
  obtain ⟨W₂, hW₂⟩ : ∃ W₂ : (Over.mk (T.hom ≫ thick V I' e) ⟶ D'.P.A) → (T.left.presheaf.stalk z)ˣ, ∀ x, W₂ x =
    gw v x.left z (J₀ (x.left ≫ β)) (J x.left) := ⟨_, fun _ => rfl⟩
  obtain ⟨p₁, p₂, p₃⟩ := U.w_vals e (Over.mk (T.hom ≫ σ)) z K J₀ hK hJ₀ W₀ hW₀
  obtain ⟨q₁, q₂, q₃⟩ := hwL.vals (Over.mk (T.hom ≫ thick V I' e)) z JG K hJG hK W₁ hW₁
  obtain ⟨r₁, r₂, r₃⟩ := hv.vals (Over.mk (T.hom ≫ thick V I' e)) z J J₀ hJ hJ₀ W₂ hW₂
  have sq : ∀ x, W₂ (b x) * W x = W₀ (n x) * W₁ (a x) := fun x => by
    have k := hsq _ x.left z _ _ _ _ (hJ₀ ((b x).left ≫ β)) (hJ (b x).left) (hK ((a x).left ≫ F)) (hJG (a x).left)
    have k₀ : W₀ (n x) = gw (U.w e) (x.left ≫ h) z (J₀ ((b x).left ≫ β)) (fun _ => K ((a x).left ≫ F)) := by
      rw [← ha, ← hq]
      exact hW₀ (n x)
    rw [k₀, hW, hW₁, hW₂]
    exact k
  refine ⟨?_, fun x => ?_, fun x y u => ?_⟩
  · have k := sq 1
    rw [map_one, map_one, map_one] at k
    have p : val (L := D.P.L) (φ := fun _ : PUnit => eSec D.P.A) (ε := fun _ => 1) D.rig
        ((T.hom ≫ σ) ≫ thick R I e) z J₀ = W₀ 1 * val (L := U.P.L.L) (φ := fun _ : PUnit => eSec G) (ε := fun _ => 1)
          U.P.L.rig ((T.hom ≫ σ) ≫ thick R I e) z K := p₁
    rw [hb] at p
    exact rig_alg k p q₁ r₁
  · have p : val D.sym ((x.left ≫ h) ≫ (U.gt e).pG.left) z J₀ * W₀ (n x) =
        W₀ (n x)⁻¹ * val U.P.sym ((x.left ≫ h) ≫ (fstG I e G).left) z K := p₂ (n x)
    rw [ha, hq] at p
    have q : val U.P.sym ((x.left ≫ (fstG I' e G').left) ≫ F) z K * W₁ (a x) =
        W₁ (a x)⁻¹ * val P'.sym (x.left ≫ (fstG I' e G').left) z JG := q₂ (a x)
    have r : val D.sym ((x.left ≫ g'.pG.left) ≫ β) z J₀ * W₂ (b x) =
        W₂ (b x)⁻¹ * val D'.sym (x.left ≫ g'.pG.left) z J := r₂ (b x)
    exact sym_alg n a b sq x p q r
  · let C : (T.left.presheaf.stalk z)ˣ := cubV D.cub (T := Over.mk ((T.hom ≫ thick V I' e) ≫ spMap φ)) z J₀
      (toBase (T := Over.mk (T.hom ≫ thick V I' e)) hβ (b x))
      (toBase (T := Over.mk (T.hom ≫ thick V I' e)) hβ (b y))
      (toBase (T := Over.mk (T.hom ≫ thick V I' e)) hβ (b u))
    let E : (T.left.presheaf.stalk z)ˣ := cubV U.P.c (T := Over.mk ((T.hom ≫ thick V I' e) ≫ spMap φ)) z K
      (toBase (T := Over.mk (T.hom ≫ thick V I' e)) hF (a x))
      (toBase (T := Over.mk (T.hom ≫ thick V I' e)) hF (a y))
      (toBase (T := Over.mk (T.hom ≫ thick V I' e)) hF (a u))
    let C' : (T.left.presheaf.stalk z)ˣ := cubV D'.cub (T := Over.mk (T.hom ≫ thick V I' e)) z J (b x) (b y) (b u)
    let E' : (T.left.presheaf.stalk z)ˣ := cubV P'.c (T := Over.mk (T.hom ≫ thick V I' e)) z JG (a x) (a y) (a u)
    let C₀ : (T.left.presheaf.stalk z)ˣ := cubV D.cub (T := (Over.map (thick R I e)).obj (Over.mk (T.hom ≫ σ))) z J₀
      ((Over.map (thick R I e)).map (n x) ≫ (U.gt e).pG) ((Over.map (thick R I e)).map (n y) ≫ (U.gt e).pG)
      ((Over.map (thick R I e)).map (n u) ≫ (U.gt e).pG)
    let E₀ : (T.left.presheaf.stalk z)ˣ := cubV U.P.c (T := (Over.map (thick R I e)).obj (Over.mk (T.hom ≫ σ))) z K
      ((Over.map (thick R I e)).map (n x) ≫ fstG I e G) ((Over.map (thick R I e)).map (n y) ≫ fstG I e G)
      ((Over.map (thick R I e)).map (n u) ≫ fstG I e G)
    have hC : C₀ = C := cubV_congr (s := (T.hom ≫ σ) ≫ thick R I e) (s' := (T.hom ≫ thick V I' e) ≫ spMap φ)
      D.cub z J₀ (hq x) (hq y) (hq u)
    have hE : E₀ = E := cubV_congr (s := (T.hom ≫ σ) ≫ thick R I e) (s' := (T.hom ≫ thick V I' e) ≫ spMap φ)
      U.P.c z K (ha x) (ha y) (ha u)
    have p : C₀ * W₀ (n x * n y) * W₀ (n x * n u) * W₀ (n y * n u) * W₀ 1 =
      W₀ (n x * n y * n u) * W₀ (n x) * W₀ (n y) * W₀ (n u) * E₀ := p₃ (n x) (n y) (n u)
    have q : E * W₁ (a x * a y) * W₁ (a x * a u) * W₁ (a y * a u) * W₁ 1 =
      W₁ (a x * a y * a u) * W₁ (a x) * W₁ (a y) * W₁ (a u) * E' := q₃ (a x) (a y) (a u)
    have r : C * W₂ (b x * b y) * W₂ (b x * b u) * W₂ (b y * b u) * W₂ 1 =
      W₂ (b x * b y * b u) * W₂ (b x) * W₂ (b y) * W₂ (b u) * C' := r₃ (b x) (b y) (b u)
    rw [hC, hE] at p
    have k := cube_alg n a b sq x y u p q r
    have hC' : C' = cubV D'.cub (T := (Over.map (thick V I' e)).obj T) z J
        ((Over.map (thick V I' e)).map x ≫ g'.pG) ((Over.map (thick V I' e)).map y ≫ g'.pG)
        ((Over.map (thick V I' e)).map u ≫ g'.pG) :=
      cubV_congr (s := T.hom ≫ thick V I' e) (s' := T.hom ≫ thick V I' e) D'.cub z J rfl rfl rfl
    have hE' : E' = cubV P'.c (T := (Over.map (thick V I' e)).obj T) z JG
        ((Over.map (thick V I' e)).map x ≫ fstG I' e G') ((Over.map (thick V I' e)).map y ≫ fstG I' e G')
        ((Over.map (thick V I' e)).map u ≫ fstG I' e G') :=
      cubV_congr (s := T.hom ≫ thick V I' e) (s' := T.hom ≫ thick V I' e) P'.c z JG rfl rfl rfl
    rw [hC', hE'] at k
    exact k

end GlobalTheory.LN.FourthSide
end
end
