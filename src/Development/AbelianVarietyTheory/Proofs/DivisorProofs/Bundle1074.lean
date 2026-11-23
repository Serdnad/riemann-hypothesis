module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1056
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Mathlib.Tactic.ENatToNat
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsTorusAndQuotientHom
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle228
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.MvPowerSeries.Derivative
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle417
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle290
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle436
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle437
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle419
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TaylorIsRingHom
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle352
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle535
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1040
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle770
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle519
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle948
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1041
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
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.TangentLinearity.ConstPullback
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle029
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle314
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLineBundleDescentToSubfield
import Development.AbelianVarietyTheory.PublishedTheorems.AbelianLaws.PrincipalPolarisationOneSection
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CharKer

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CharKer

theorem pullTop_pullTop_comp {X Y Z : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) (u : Γ(Z, ⊤)ˣ) :
    pullTop f (pullTop g u) = pullTop (f ≫ g) u := rfl

theorem exists_unit_of_triv {X Y Z : Scheme.{0}} (p : X ⟶ Y) (M : LB Y) (hM : M.IsLB)
    (e : ∀ k, Γ(X, p ⁻¹ᵁ M.U k)ˣ) (he : IsPullGen p M e) (t : M.Gen) (ht : t.IsGen)
    (a b : Z ⟶ X) (hab : a ≫ p = b ≫ p) (c : Γ(Z, ⊤)ˣ)
    (hc : ∀ (k : M.ι) (W : Z.Opens) (h₁ : W ≤ a ⁻¹ᵁ (p ⁻¹ᵁ M.U k)) (h₂ : W ≤ b ⁻¹ᵁ (p ⁻¹ᵁ M.U k)),
      res h₁ (pullU a _ (e k)) = res le_top c * res h₂ (pullU b _ (e k))) :
    ∃ f : Γ(X, ⊤)ˣ, pullTop a f = c * pullTop b f := by
  obtain ⟨f, hf⟩ := glue_unit (X := X) (J := M.ι) ⊤ (fun k => p ⁻¹ᵁ M.U k) (fun _ => le_top)
    (fun x _ => by
      obtain ⟨k, hk⟩ := exists_chart hM (p x)
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨k, hk⟩)
    (fun k => e k * (pullU p _ (t.s k))⁻¹) (fun k l x hx => by
      have h₁ := congrArg (gm (𝟙 X) x _) (he k l (p ⁻¹ᵁ M.U k ⊓ p ⁻¹ᵁ M.U l) inf_le_left inf_le_right
        (p.preimage_inf (U := M.U k) (V := M.U l)).ge)
      have h₂ := congrArg (gm p x _) (ht k l)
      rw [map_mul, gm_res _ x _ hx, gm_res _ x _ hx, gm_res _ x _ hx, gm_pull (𝟙 X) p x (M.U k ⊓ M.U l) hx,
        Category.id_comp] at h₁
      rw [map_mul, gm_res p x _ hx, gm_res p x _ hx] at h₂
      rw [map_mul, map_mul, map_inv, map_inv, gm_pull (𝟙 X) p x _ hx.1, gm_pull (𝟙 X) p x _ hx.2,
        Category.id_comp, h₁, h₂,
        mul_inv_rev, mul_comm (gm p x _ (M.g k l)), _root_.mul_assoc, mul_comm (gm p x _ (t.s l))⁻¹,
        mul_inv_cancel_left])
  refine ⟨f, unit_ext fun z hz => ?_⟩
  obtain ⟨k, hk⟩ := exists_chart hM (p (a z))
  have hk' : p (b z) ∈ M.U k := by
    rwa [← Scheme.Hom.comp_apply, ← hab, Scheme.Hom.comp_apply]
  have hz' : z ∈ a ⁻¹ᵁ (p ⁻¹ᵁ M.U k) ⊓ b ⁻¹ᵁ (p ⁻¹ᵁ M.U k) := ⟨hk, hk'⟩
  have h := congrArg (gm (𝟙 Z) z _) (hc k _ inf_le_left inf_le_right)
  rw [map_mul, gm_res _ z _ hz', gm_res _ z _ hz', gm_res _ z _ hz', gm_pull (𝟙 Z) a z (p ⁻¹ᵁ M.U k) hk,
    gm_pull (𝟙 Z) b z (p ⁻¹ᵁ M.U k) hk',
    Category.id_comp, Category.id_comp] at h
  have key : ∀ d : Z ⟶ X, p (d z) ∈ M.U k →
      gm (𝟙 Z) z ⊤ (pullTop d f) = gm d z _ (e k) * (gm (d ≫ p) z _ (t.s k))⁻¹ := fun d hd => by
    have h' := congrArg (gm d z _) (hf k)
    rw [gm_res d z _ hd, map_mul, map_inv, gm_pull d p z _ hd] at h'
    rw [← h']
    exact gm_pull (𝟙 Z) d z ⊤ trivial f
  rw [map_mul, key a hk, key b hk', h, hab, _root_.mul_assoc]

theorem exists_pullTop_snd {S : Scheme.{0}} (A T : Over S) [GrpObj A] (hA : IsAbelianScheme A)
    (f : Γ((A ⊗ T).left, ⊤)ˣ) : ∃ u : Γ(T.left, ⊤)ˣ, pullTop (snd A T).left u = f := by
  have hb : Function.Bijective (snd A T).left.appTop.hom :=
    GlobalTheory.SemiRigid.globalFns _ _ (Out.TLinPf.isAb_pullback T.hom A hA)
  let φ := RingEquiv.ofBijective _ hb
  exact ⟨Units.map (φ.symm : Γ((A ⊗ T).left, ⊤) →* Γ(T.left, ⊤)) f, Units.ext (φ.apply_symm_apply f.val)⟩

theorem character_eq_one_of_triv : ∀ (K : Type) [Field K] (A A' N T : Over (Sp K)) [GrpObj A] [GrpObj A'] [GrpObj N] (i : N ⟶ A) (q : A ⟶ A') (χ : Γ((N ⊗ T).left, ⊤)ˣ) (M : LB (A' ⊗ T).left) (e : ∀ k, Γ((A ⊗ T).left, (pmap q T).left ⁻¹ᵁ M.U k)ˣ), IsAbelianScheme A → IsMonHom q → IsPullback i (toUnit N) q η[A'] → M.IsLB → IsEquivGen i q χ M e → Triv M → χ = 1 := by
  intro K _ A A' N T _ _ _ i q χ M e hA hq hk hM he ⟨t, ht⟩
  have hab : actMap i T ≫ pmap q T = prMap A N T ≫ pmap q T := by
    have hi : i ≫ q = 1 := hk.w
    simp only [actMap, prMap, pmap, comp_lift, lift_fst_assoc, lift_snd, MonObj.mul_comp, Category.assoc, hi,
      MonObj.comp_one, _root_.mul_one]
  obtain ⟨f, hf⟩ := exists_unit_of_triv _ M hM e he.1 t ht (actMap i T).left (prMap A N T).left
    (congrArg (·.left) hab) _ he.2
  obtain ⟨u, rfl⟩ := exists_pullTop_snd A T hA f
  have h₁ : (actMap i T).left ≫ (snd A T).left = (prMap A N T).left ≫ (snd A T).left := by
    rw [← Over.comp_left, ← Over.comp_left, actMap, prMap, lift_snd, lift_snd]
  rw [pullTop_pullTop_comp, pullTop_pullTop_comp, h₁, right_eq_mul] at hf
  have h₂ : (lift (1 : N ⊗ T ⟶ A) (𝟙 (N ⊗ T))).left ≫ (snd A (N ⊗ T)).left = 𝟙 _ := by
    rw [← Over.comp_left, lift_snd, Over.id_left]
  have h₃ := congrArg (pullTop (lift (1 : N ⊗ T ⟶ A) (𝟙 (N ⊗ T))).left) hf
  rw [pullTop_pullTop_comp, h₂, map_one] at h₃
  exact h₃

end GlobalTheory.CharKer
end
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CharKer

namespace GlobalTheory.CharKer

variable {S : Scheme.{0}}

theorem comp_one_hom {X Y M : Over S} [GrpObj M] (u : Y ⟶ X) : u ≫ (1 : X ⟶ M) = 1 := by
  rw [Hom.one_def, Hom.one_def, ← Category.assoc, toUnit_unique (u ≫ toUnit X) (toUnit Y)]

theorem pmap_isPullback_actMap : ∀ (S : Scheme.{0}) (A A' N T : Over S) [GrpObj A] [GrpObj A'] [GrpObj N] (i : N ⟶ A) (q : A ⟶ A'), IsMonHom i → IsMonHom q → IsPullback i (toUnit N) q η[A'] → IsPullback (prMap A N T) (actMap i T) (pmap q T) (pmap q T) := by
  intro S A A' N T _ _ _ i q hi hq hker
  have hiq : i ≫ q = 1 := by rw [hker.w, Hom.one_def]
  have hpf : pmap q T ≫ fst A' T = fst A T ≫ q := by simp [pmap]
  have hps : pmap q T ≫ snd A' T = snd A T := by simp [pmap]
  have hc : prMap A N T ≫ pmap q T = actMap i T ≫ pmap q T := by
    apply CartesianMonoidalCategory.hom_ext
    · rw [Category.assoc, Category.assoc, hpf]
      simp only [prMap, actMap, lift_fst_assoc, mul_comp, Category.assoc, hiq]
      simp only [comp_one_hom, _root_.mul_one]
    · rw [Category.assoc, Category.assoc, hps]
      simp [prMap, actMap]
  have hfs : ∀ s : PullbackCone (pmap q T) (pmap q T), (s.fst ≫ fst A T) ≫ q = (s.snd ≫ fst A T) ≫ q := by
    intro s
    have h := congrArg (· ≫ fst A' T) s.condition
    simp only [Category.assoc, hpf] at h
    simpa only [Category.assoc] using h
  have hss : ∀ s : PullbackCone (pmap q T) (pmap q T), s.fst ≫ snd A T = s.snd ≫ snd A T := by
    intro s
    have h := congrArg (· ≫ snd A' T) s.condition
    simpa only [Category.assoc, hps] using h
  have hk : ∀ s : PullbackCone (pmap q T) (pmap q T),
      ((s.fst ≫ fst A T)⁻¹ * (s.snd ≫ fst A T)) ≫ q = toUnit s.pt ≫ η[A'] := by
    intro s
    rw [mul_comp, GrpObj.inv_comp, hfs s, _root_.inv_mul_cancel, Hom.one_def]
  refine ⟨⟨hc⟩, ⟨PullbackCone.IsLimit.mk hc
    (fun s => lift (s.fst ≫ fst A T)
      (lift (hker.lift ((s.fst ≫ fst A T)⁻¹ * (s.snd ≫ fst A T)) (toUnit _) (hk s)) (s.fst ≫ snd A T)))
    ?_ ?_ ?_⟩⟩
  · intro s
    apply CartesianMonoidalCategory.hom_ext <;> simp [prMap]
  · intro s
    apply CartesianMonoidalCategory.hom_ext
    · simp only [actMap, Category.assoc, lift_fst, comp_mul, lift_fst_assoc, lift_snd_assoc, hker.lift_fst]
      exact _root_.mul_inv_cancel_left _ _
    · simp [actMap, hss]
  · intro s m h1 h2
    have ha : m ≫ fst A (N ⊗ T) = s.fst ≫ fst A T := by rw [← h1]; simp [prMap]
    have ht : m ≫ snd A (N ⊗ T) ≫ snd N T = s.fst ≫ snd A T := by rw [← h1]; simp [prMap]
    have hb : m ≫ fst A (N ⊗ T) * m ≫ snd A (N ⊗ T) ≫ fst N T ≫ i = s.snd ≫ fst A T := by
      rw [← h2]; simp [actMap, comp_mul]
    apply CartesianMonoidalCategory.hom_ext
    · simpa using ha
    · apply CartesianMonoidalCategory.hom_ext
      · apply hker.hom_ext
        · simp only [Category.assoc, lift_snd_assoc, lift_fst_assoc, hker.lift_fst]
          rw [← ha]
          exact eq_inv_mul_of_mul_eq hb
        · exact toUnit_unique _ _
      · simpa using ht

end GlobalTheory.CharKer
end

section

open IsLocalRing GlobalTheory.FormalOrigin GlobalTheory.FormalOrigin.Extend

namespace GlobalTheory.FormalOrigin.Extend

noncomputable def pdZ {σ R : Type} [CommRing R] (j : σ) : Derivation ℤ (MvPowerSeries σ R) (MvPowerSeries σ R) where
  toFun := MvPowerSeries.pderiv (R := R) j
  map_add' := map_add _
  map_smul' m x := by simpa using map_zsmul (MvPowerSeries.pderiv (R := R) j) m x
  map_one_eq_zero' := MvPowerSeries.pderiv_one
  leibniz' := (MvPowerSeries.pderiv (R := R) j).leibniz

theorem pdZ_apply {σ R : Type} [CommRing R] (j : σ) (F : MvPowerSeries σ R) :
    pdZ j F = MvPowerSeries.pderiv (R := R) j F := rfl

theorem add_sum_apply {σ R ι : Type} [CommRing R] [Fintype ι] (E : Derivation ℤ (MvPowerSeries σ R) (MvPowerSeries σ R))
    (G : ι → MvPowerSeries σ R) (P : ι → Derivation ℤ (MvPowerSeries σ R) (MvPowerSeries σ R))
    (F : MvPowerSeries σ R) : (E + ∑ j, G j • P j) F = E F + ∑ j, G j * P j F := by
  rw [Derivation.add_apply]
  congr 1

  rw [← Derivation.coeFnAddMonoidHom_apply, map_sum, Finset.sum_apply]
  change ∑ j, (G j • P j) F = ∑ j, G j * P j F
  simp [Derivation.smul_apply, smul_eq_mul]

theorem derivation_extends : ∀ (R A : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] [CommRing A] [IsLocalRing A] [IsNoetherianRing A] (inc : R →+* A) (ev : A →+* R), (∀ r, ev (inc r) = r) → ∀ (n : ℕ) (ds : Fin n → Derivation ℤ A A) (z : Fin n → A), (∀ i, ev (z i) = 0) → (∀ a i, ev (ds a (z i)) = if a = i then 1 else 0) → maximalIdeal A = (maximalIdeal R).map inc ⊔ Ideal.span (Set.range z) → (∀ a r, ds a (inc r) = 0) → ∀ (d : Derivation ℤ A A) (D : Derivation ℤ R R), (∀ r, d (inc r) = inc (D r)) → ∃ dΩ : Derivation ℤ (MvPowerSeries (Fin n) R) (MvPowerSeries (Fin n) R), (∀ r, dΩ (MvPowerSeries.C r) = MvPowerSeries.C (D r)) ∧ ∀ f, dΩ (taylor ev (fun i => ⇑(ds i)) f) = taylor ev (fun i => ⇑(ds i)) (d f) := by
  intro R A _ _ _ _ _ _ _ _ inc ev hev n ds z hz hdz hm hinc d D hdD
  obtain ⟨T, hT⟩ := taylor_isRingHom A R n ev ds
  simp only [← hT]
  obtain ⟨E, hE⟩ := GlobalTheory.T.exists_coeffwise_derivation_mvPowerSeries (Fin n) R D
  have hEC : ∀ r, E (MvPowerSeries.C r) = MvPowerSeries.C (D r) := by
    intro r; ext α
    rw [hE, MvPowerSeries.coeff_C, MvPowerSeries.coeff_C]
    split_ifs <;> simp
  have hTinc : ∀ r, T (inc r) = MvPowerSeries.C r := by
    intro r; rw [hT, taylor_const A R n ev ds (inc r) (fun i => hinc i r), hev]
  obtain ⟨G, hG⟩ := GlobalTheory.T.exists_solve_mvPowerSeries_matrix_identity_const n R (fun i j => pdZ j (T (z i))) (by
    intro i j
    simp only [pdZ_apply]
    rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPowerSeries.coeff_pderiv, zero_add, hT,
      GlobalTheory.T.coeff_single_derivationTaylorPowerSeries, hdz]
    simp [eq_comm]) (fun i => T (d (z i)) - E (T (z i)))
  set dΩ : Derivation ℤ (MvPowerSeries (Fin n) R) (MvPowerSeries (Fin n) R) := E + ∑ j, G j • pdZ j with hdΩ
  have hΩ : ∀ F, dΩ F = E F + ∑ j, G j * pdZ j F := fun F => add_sum_apply E G _ F
  refine ⟨dΩ, fun r => ?_, ?_⟩
  · simp [hΩ, hEC, pdZ_apply]
  ·
    set e : A → MvPowerSeries (Fin n) R := fun f => dΩ (T f) - T (d f) with he
    have e_add : ∀ f g, e (f + g) = e f + e g := by
      intro f g; simp only [he, map_add (f := _)]; ring
    have e_mul : ∀ f g, e (f * g) = T f * e g + T g * e f := by
      intro f g; simp only [he, map_mul, Derivation.leibniz, smul_eq_mul, map_add (f := _)]; ring
    have e_neg : ∀ f, e (-f) = - e f := by
      intro f; simp only [he, map_neg]; ring
    have e_one : e 1 = 0 := by simp [he]
    let Q : Subring A :=
      { carrier := {f | e f = 0}
        mul_mem' := fun {f g} hf hg => by simp only [Set.mem_setOf_eq] at *; rw [e_mul, hf, hg]; ring
        one_mem' := e_one
        add_mem' := fun {f g} hf hg => by simp only [Set.mem_setOf_eq] at *; rw [e_add, hf, hg]; ring
        zero_mem' := by simp [he]
        neg_mem' := fun {f} hf => by simp only [Set.mem_setOf_eq] at *; rw [e_neg, hf, neg_zero] }
    have hQ : Subring.closure (Set.range inc ∪ Set.range z) ≤ Q := by
      rw [Subring.closure_le]
      rintro _ (⟨r, rfl⟩ | ⟨i, rfl⟩)
      · change e (inc r) = 0
        simp [he, hTinc, hdD, hΩ, hEC, pdZ_apply]
      · change e (z i) = 0
        have := hG i
        simp only [he, hΩ]
        rw [this]; ring

    have hc0 : ∀ x, MvPowerSeries.constantCoeff (T x) = ev x := by
      intro x
      rw [hT, ← MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
      change (∏ i, (((0 : Fin n →₀ ℕ) i).factorial : ℚ))⁻¹ • ev (iterOp _ 0 x) = _
      rw [iterOp_zero]; simp
    have hloc : ∀ x ∈ maximalIdeal A, ev x ∈ maximalIdeal R := by
      intro x hx
      rw [mem_maximalIdeal, mem_nonunits_iff]
      intro hu
      have h1 : x - inc (ev x) ∈ maximalIdeal A := by
        apply le_maximalIdeal (RingHom.ker_ne_top ev)
        rw [RingHom.mem_ker, map_sub, hev, sub_self]
      have h2 : inc (ev x) ∈ maximalIdeal A := by simpa using Ideal.sub_mem _ hx h1
      exact (mem_maximalIdeal _).1 h2 (hu.map inc)
    have hT1 : ∀ x ∈ maximalIdeal A, T x ∈ filt (maximalIdeal R) 1 := by
      intro x hx α
      by_cases hα : α = 0
      · subst hα
        simp only [map_zero, Nat.sub_zero, pow_one]
        rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hc0]
        exact hloc x hx
      · have : 1 - α.degree = 0 := by
          have : α.degree ≠ 0 := by
            intro h0; exact hα ((Finsupp.degree_eq_zero_iff α).1 h0)
          omega
        rw [this, pow_zero, Ideal.one_eq_top]; trivial
    have hTk : ∀ k, ∀ x ∈ maximalIdeal A ^ k, T x ∈ filt (maximalIdeal R) k := by
      intro k
      induction k with
      | zero => intro x _ α; simp
      | succ k ih =>
        intro x hx
        rw [pow_succ'] at hx
        refine Submodule.mul_induction_on hx (fun a ha b hb => ?_) (fun a b ha hb => ?_)
        · rw [map_mul, add_comm]
          exact GlobalTheory.T.mvPowerSeriesDegreeAdicFiltration_mul_le (Fin n) R _ 1 k (Ideal.mul_mem_mul (hT1 a ha) (ih b hb))
        · rw [map_add (f := _)]; exact Ideal.add_mem _ ha hb
    have hek : ∀ k, ∀ x ∈ maximalIdeal A ^ (k + 1), e x ∈ filt (maximalIdeal R) k := by
      intro k
      induction k with
      | zero => intro x _ α; simp
      | succ k ih =>
        intro x hx
        rw [pow_succ'] at hx
        refine Submodule.mul_induction_on hx (fun a ha b hb => ?_) (fun a b ha hb => ?_)
        · rw [e_mul]
          refine Ideal.add_mem _ ?_ (Ideal.mul_mem_right _ _ (hTk _ b hb))
          rw [add_comm]
          exact GlobalTheory.T.mvPowerSeriesDegreeAdicFiltration_mul_le (Fin n) R _ 1 k (Ideal.mul_mem_mul (hT1 a ha) (ih b hb))
        · rw [e_add]; exact Ideal.add_mem _ ha hb
    intro f
    have : e f = 0 := by
      refine eq_zero_of_forall_mem_filt (maximalIdeal R) _ fun k => ?_
      obtain ⟨p, hp, hfp⟩ := GlobalTheory.T.exists_coordinate_polynomial_sub_mem_maximalIdeal_pow R A inc ev hev n z hm (k + 1) f
      have h1 : e f = e p + e (f - p) := by rw [← e_add]; congr 1; ring
      rw [h1, show e p = 0 from hQ hp, zero_add]
      exact hek k _ hfp
    exact sub_eq_zero.1 this

end GlobalTheory.FormalOrigin.Extend
end

section

open IsLocalRing Polynomial

namespace GlobalTheory.KeyOriginEnlarge

theorem etale_enlarge : ∀ (T O : Type) [CommRing T] [IsDomain T] [IsLocalRing T] [CommRing O] [IsLocalRing O] [Algebra T O]
    [Algebra (Polynomial T) O] [IsScalarTower T (Polynomial T) O], GlobalTheory.LocAcyc.AbsIntClosed T →
    ∀ (P : Ideal (Polynomial T)) [P.IsPrime] (φ : Localization.AtPrime P →+* O),
    φ.comp (algebraMap (Polynomial T) _) = algebraMap (Polynomial T) O →
    GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsStrictHenselisation φ → P = GlobalTheory.KeyOriginCut.originIdeal T →
    ∀ (q : ℕ), 0 < q → IsUnit (q : T) →
    ∀ (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] [IsIntegrallyClosed A]
      [Algebra.EssFiniteType ℤ A] (i : A →+* T)
      (EA : Type) [CommRing EA] [Algebra (Polynomial A) EA] [Algebra A EA]
      [IsScalarTower A (Polynomial A) EA] [Algebra.Etale (Polynomial A) EA]
      (QA : Ideal EA) [QA.IsPrime] (jA : Localization.AtPrime QA →+* O)
      (ψA : GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA) →+* GlobalTheory.LocAcyc.GenFib T O)
      (DA : Type) [CommRing DA] [Algebra (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA]
      (actA : Multiplicative (ZMod q) →* (DA ≃ₐ[GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)] DA)),
    GlobalTheory.KeyOriginEnlarge.Fits T O q A i EA QA jA ψA DA actA →
    ∀ ρ : Localization.AtPrime QA →+* A, GlobalTheory.KeyOriginEnlarge.Retracts T O A i EA QA jA ρ →
    GlobalTheory.KeyOriginEnlarge.PointAtZero A (Localization.AtPrime QA) DA ρ →
    ∃ (A' : Type) (_ : CommRing A') (_ : IsDomain A') (_ : IsLocalRing A') (_ : IsNoetherianRing A')
      (_ : IsIntegrallyClosed A') (_ : Algebra.EssFiniteType ℤ A') (i' : A' →+* T)
      (EA' : Type) (_ : CommRing EA') (_ : Algebra (Polynomial A') EA') (_ : Algebra A' EA')
      (_ : IsScalarTower A' (Polynomial A') EA') (_ : Algebra.Etale (Polynomial A') EA')
      (QA' : Ideal EA') (_ : QA'.IsPrime) (jA' : Localization.AtPrime QA' →+* O)
      (ψA' : GlobalTheory.LocAcyc.GenFib A' (Localization.AtPrime QA') →+* GlobalTheory.LocAcyc.GenFib T O)
      (DA' : Type) (_ : CommRing DA') (_ : Algebra (GlobalTheory.LocAcyc.GenFib A' (Localization.AtPrime QA')) DA')
      (actA' : Multiplicative (ZMod q) →* (DA' ≃ₐ[GlobalTheory.LocAcyc.GenFib A' (Localization.AtPrime QA')] DA')),
      GlobalTheory.KeyOriginEnlarge.Fits T O q A' i' EA' QA' jA' ψA' DA' actA' ∧
      (∃ ρ' : Localization.AtPrime QA' →+* A',
        GlobalTheory.KeyOriginEnlarge.Retracts T O A' i' EA' QA' jA' ρ' ∧ GlobalTheory.KeyOriginNoeth.Good A' (Localization.AtPrime QA') DA' ρ') ∧
      ∃ (β : GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA) →+* GlobalTheory.LocAcyc.GenFib A' (Localization.AtPrime QA')) (h : DA →+* DA'),
        ψA'.comp β = ψA ∧
        h.comp (algebraMap (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA) = (algebraMap (GlobalTheory.LocAcyc.GenFib A' (Localization.AtPrime QA')) DA').comp β := by
  intro T O _ _ _ _ _ _ _ _ hT P _ φ hφ hsh hP q hq hqT A _ _ _ _ _ _ i EA _ _ _ _ _ QA _ jA ψA DA _ _ actA hFits ρ hρ hpt
  have htor := hFits.2.2.2.2.2.2
  obtain ⟨a, ha0, ha⟩ := GlobalTheory.T.exists_ne_zero_closureEtaleAt_alt q A EA QA DA actA hq hFits.2.2.1 htor
  obtain ⟨A₁, _, _, _, _, _, _, f, i₁, hf, hi₁, hloc₁, hcomp, hK⟩ :=
    GlobalTheory.T.exists_kummerEnlargement_rootsOfUniformisers T hT q hq hqT A i hFits.1 hFits.2.1 a ha0
  obtain ⟨EA₁, _, _, _, _, _, QA₁, _, jA₁, ψA₁, DA₁, _, _, actA₁, hFits₁, ⟨ρ₁, hρ₁, hpt₁⟩, hEt, β, h, hβ, hh⟩ :=
    GlobalTheory.T.baseChange_integralClosure_etale_height_one T O hT P φ hφ hsh hP q hq hqT A i EA QA jA ψA DA actA hFits ρ hρ hpt a ha0 ha
      A₁ f i₁ hf hi₁ hloc₁ hcomp hK
  refine ⟨A₁, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, i₁,
    EA₁, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, QA₁, inferInstance, jA₁, ψA₁,
    DA₁, inferInstance, inferInstance, actA₁, hFits₁, ⟨ρ₁, hρ₁, ?_⟩, β, h, hβ, hh⟩
  exact (GlobalTheory.KeyOriginEnlarge.good_iff_etaleAt _ _ _ _).2
    ⟨GlobalTheory.T.integralClosureEtaleAt_of_height_le_one_purity q A₁ EA₁ QA₁ DA₁ actA₁ hFits₁.2.2.2.2.2.2 hEt, hpt₁⟩

end GlobalTheory.KeyOriginEnlarge
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.LBDescent

theorem _root_.GlobalTheory.T.twisted_frame_invariant_under_descentDatum : ∀ {X Y : Scheme.{0}} (f : X ⟶ Y) (L : LB X) (φ : ∀ i j, Γ(pullback f f, chart f L i j)ˣ)
    (V : Y.Opens) (t : ∀ i, Γ(X, f ⁻¹ᵁ V ⊓ L.U i)ˣ), (∀ (i j : L.ι) (x : X), f x ∈ V → x ∈ L.U i → x ∈ L.U j →
      gm (𝟙 X) x _ (t i) = gm (𝟙 X) x _ (L.g i j) * gm (𝟙 X) x _ (t j)) →
    ∀ (c : Γ(pullback f f, pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V)ˣ),
      (∀ (z : ↥(pullback f f)) (i j : L.ι), f (pullback.fst f f z) ∈ V → pullback.fst f f z ∈ L.U i →
        pullback.snd f f z ∈ L.U j →
        gm (𝟙 _) z _ c = gm (pullback.fst f f) z _ (t i) * gm (𝟙 _) z _ (φ i j) * (gm (pullback.snd f f) z _ (t j))⁻¹) →
    ∀ (V' : Y.Opens), V' ≤ V → ∀ u : Γ(X, f ⁻¹ᵁ V')ˣ, (∀ z : ↥(pullback f f), f (pullback.fst f f z) ∈ V' →
        gm (pullback.fst f f) z _ u * gm (𝟙 _) z _ c = gm (pullback.snd f f) z _ u) →
    ∃ s : ∀ i, Γ(X, f ⁻¹ᵁ V' ⊓ L.U i)ˣ,
      (∀ (i j : L.ι) (x : X), f x ∈ V' → x ∈ L.U i → x ∈ L.U j →
        gm (𝟙 X) x _ (s i) = gm (𝟙 X) x _ (L.g i j) * gm (𝟙 X) x _ (s j)) ∧
      ∀ (z : ↥(pullback f f)) (i j : L.ι), f (pullback.fst f f z) ∈ V' → pullback.fst f f z ∈ L.U i →
        pullback.snd f f z ∈ L.U j →
        gm (pullback.fst f f) z _ (s i) * gm (𝟙 _) z _ (φ i j) = gm (pullback.snd f f) z _ (s j) := by
  first | exact @GlobalTheory.LBDescent.twist_frame_descent | exact GlobalTheory.LBDescent.twist_frame_descent | (intros; apply GlobalTheory.LBDescent.twist_frame_descent <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.LBDescent

theorem _root_.GlobalTheory.T.descentDatum_frame_cocycle_unit : ∀ {X Y : Scheme.{0}} (f : X ⟶ Y) (L : LB X), L.IsLB →
    ∀ (φ : ∀ i j, Γ(pullback f f, chart f L i j)ˣ), DescCompat f L φ → DescCocycle f L φ →
    ∀ (V : Y.Opens) (t : ∀ i, Γ(X, f ⁻¹ᵁ V ⊓ L.U i)ˣ), (∀ (i j : L.ι) (x : X), f x ∈ V → x ∈ L.U i → x ∈ L.U j →
      gm (𝟙 X) x _ (t i) = gm (𝟙 X) x _ (L.g i j) * gm (𝟙 X) x _ (t j)) →
    ∃ c : Γ(pullback f f, pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V)ˣ,
      (∀ (z : ↥(pullback f f)) (i j : L.ι), f (pullback.fst f f z) ∈ V → pullback.fst f f z ∈ L.U i →
        pullback.snd f f z ∈ L.U j →
        gm (𝟙 _) z _ c = gm (pullback.fst f f) z _ (t i) * gm (𝟙 _) z _ (φ i j) * (gm (pullback.snd f f) z _ (t j))⁻¹) ∧
      ∀ w : ↥(Triple f), f (pullback.fst f f (pullback.fst (pullback.snd f f) (pullback.fst f f) w)) ∈ V →
        gm (pullback.fst (pullback.snd f f) (pullback.fst f f)) w _ c *
          gm (pullback.snd (pullback.snd f f) (pullback.fst f f)) w _ c = gm (pr13 f) w _ c := by
  first | exact @GlobalTheory.LBDescent.frame_cocycle | exact GlobalTheory.LBDescent.frame_cocycle | (intros; apply GlobalTheory.LBDescent.frame_cocycle <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.LBDescent
open TensorProduct

theorem _root_.GlobalTheory.T.unit_cocycle_descends_on_triple_overlaps : ∀ {X Y : Scheme.{0}} (f : X ⟶ Y) [IsFinite f] (V V₀ : Y.Opens), IsAffineOpen V₀ →
    ∀ (h : pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V₀ ≤ pullback.snd f f ⁻¹ᵁ f ⁻¹ᵁ V₀)
      (hle : pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V₀ ≤ pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V) (c : Γ(pullback f f, pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V)ˣ),
    (∀ w : ↥(Triple f), f (pullback.fst f f (pullback.fst (pullback.snd f f) (pullback.fst f f) w)) ∈ V →
        gm (pullback.fst (pullback.snd f f) (pullback.fst f f)) w _ c *
          gm (pullback.snd (pullback.snd f f) (pullback.fst f f)) w _ c = gm (pr13 f) w _ c) →
    letI : Algebra Γ(Y, V₀) Γ(X, f ⁻¹ᵁ V₀) := (f.app V₀).hom.toAlgebra
    ∀ e : Γ(X, f ⁻¹ᵁ V₀) ⊗[Γ(Y, V₀)] Γ(X, f ⁻¹ᵁ V₀) ≃+* Γ(pullback f f, pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V₀),
      (∀ a b : Γ(X, f ⁻¹ᵁ V₀), e (a ⊗ₜ b) =
        ((pullback.fst f f).app (f ⁻¹ᵁ V₀)).hom a * ((pullback.snd f f).appLE (f ⁻¹ᵁ V₀) _ h).hom b) →
      Algebra.TensorProduct.includeLeft (R := Γ(Y, V₀)) (S := Γ(Y, V₀)) (A := Γ(X, f ⁻¹ᵁ V₀) ⊗[Γ(Y, V₀)] Γ(X, f ⁻¹ᵁ V₀)) (B := Γ(X, f ⁻¹ᵁ V₀)) (e.symm (res hle c).val) *
          Algebra.TensorProduct.map (Algebra.TensorProduct.includeRight (R := Γ(Y, V₀)) (A := Γ(X, f ⁻¹ᵁ V₀)) (B := Γ(X, f ⁻¹ᵁ V₀))) (AlgHom.id Γ(Y, V₀) Γ(X, f ⁻¹ᵁ V₀)) (e.symm (res hle c).val) =
        Algebra.TensorProduct.map (Algebra.TensorProduct.includeLeft (R := Γ(Y, V₀)) (S := Γ(Y, V₀)) (A := Γ(X, f ⁻¹ᵁ V₀)) (B := Γ(X, f ⁻¹ᵁ V₀))) (AlgHom.id Γ(Y, V₀) Γ(X, f ⁻¹ᵁ V₀)) (e.symm (res hle c).val) := by
  first | exact @GlobalTheory.LBDescent.CocycleTensor.cocycle_tensor_of_pointwise | exact GlobalTheory.LBDescent.CocycleTensor.cocycle_tensor_of_pointwise | (intros; apply GlobalTheory.LBDescent.CocycleTensor.cocycle_tensor_of_pointwise <;> assumption)
end
