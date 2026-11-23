module

import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle022
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.DegProd
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.SiegelPullbackTransfer.ExistsGenTransfer
public import Development.AbelianVarietyTheory.Definitions.Uniformization.SmulOneSecEqZeroIff
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle021
public import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ThetaGrpActIterateEqOfPowEqOne
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
import Mathlib.Tactic.Lemma
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.GeneratorPullback.PullAlong
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.SiegelPullbackTransfer.AdelicGL2ExtOfLocalComponents
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.QuadTie

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.BoxSymLoc

open ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison (gU unit_ext gU_res gU_pullU gU_pullU_congr gU_pullU_res)
open ReciprocityTheory.ChartRestriction.G.Out.LBxP

variable {X X' Y : Scheme.{0}} (L : LB X) {J K : Type} [Fintype J] [Fintype K]

lemma gU_pull_box_g (F : J → (X' ⟶ X)) (a : Y ⟶ X') (i j : J → L.ι) (y : Y)
    (hy : y ∈ a ⁻¹ᵁ ((LB.LinComb L F (fun _ => 1)).U i ⊓ (LB.LinComb L F (fun _ => 1)).U j))
    (hy' : ∀ m, y ∈ (a ≫ F m) ⁻¹ᵁ (L.U (i m) ⊓ L.U (j m))) :
    gU y hy (pullU a _ ((LB.LinComb L F (fun _ => 1)).g i j)) =
      ∏ m, gU y (hy' m) (pullU (a ≫ F m) _ (L.g (i m) (j m))) := by
  refine (gU_pullU a _ y hy _).trans ?_
  have e := gU_lcg L F (fun _ => 1) i j (a.base y) hy
  refine (congrArg (Units.map (RingHom.toMonoidHom (a.stalkMap y).hom)) e).trans ?_
  refine (map_prod _ _ _).trans (Finset.prod_congr rfl fun m _ => ?_)
  refine (congrArg (Units.map (RingHom.toMonoidHom (a.stalkMap y).hom)) (zpow_one _)).trans ?_
  refine (gU_pullU a _ y _ _).symm.trans ?_
  exact gU_pullU_comp a (F m) _ _ y _ _

lemma isGen_boxGen (F : J → (X' ⟶ X)) (φ : K → (Y ⟶ X')) (ε : K → ℤ)
    (t : ∀ i, LB.Gen (LB.LinComb (L.pull (F i)) φ ε)) (ht : ∀ i, (t i).IsGen) :
    (GeneratorPullback.boxGen L F φ ε t).IsGen := by
  apply GlobalTheory.BoxCubical.isGen_boxGen <;> assumption

lemma exists_restrict {S : Scheme.{0}} {A B : Over S} (f : A ⟶ B) (U : S.Opens) :
    ∃ ρ : (A.hom ⁻¹ᵁ U).toScheme ⟶ (B.hom ⁻¹ᵁ U).toScheme,
      ρ ≫ (B.hom ⁻¹ᵁ U).ι = (A.hom ⁻¹ᵁ U).ι ≫ f.left := by
  refine ⟨f.left.resLE _ _ ?_, Scheme.Hom.resLE_comp_ι _ _⟩
  rw [← Scheme.Hom.comp_preimage, Over.w]

end GlobalTheory.BoxSymLoc

namespace GlobalTheory

open BoxSymLoc ReciprocityTheory.ChartRestriction.G.Out.LBxP

theorem rigidified_sym_boxLB (S : Scheme.{0}) (G' G : Over S) [GrpObj G'] [IsCommMonObj G']
    [GrpObj G] [IsCommMonObj G] (j : ℕ) (p : IsPowGrp G' G j) (L : LB G.left) (_hL : L.IsLB) :
    (Rigidified G L → Rigidified G' (boxLB L p.pr)) ∧
      (Out.Sym G L → Out.Sym G' (boxLB L p.pr)) := by
  constructor
  · rintro ⟨t, ht⟩
    have he : ∀ i : Fin j, ∀ _k : PUnit, eSec G' ≫ (p.pr i).left = 𝟙 _ ≫ eSec G := by
      intro i _
      have := p.hom i
      rw [Category.id_comp, eSec, eSec, ← Over.comp_left, IsMonHom.one_hom]
    exact ⟨GeneratorPullback.boxGen L (fun i => (p.pr i).left) (fun _ => eSec G') (fun _ => 1)
      (fun i => GeneratorPullback.pullAlong L (p.pr i).left (𝟙 _) (fun _ => eSec G) _ _ (he i) t),
      isGen_boxGen L _ _ _ _ fun i => isGen_pullAlong L _ _ _ _ _ (he i) t ht⟩
  · intro h s
    obtain ⟨U, hs, t, ht⟩ := h s
    refine ⟨U, hs, ?_⟩
    choose ρ hρ using fun i => exists_restrict (p.pr i) U
    have he : ∀ i : Fin j, ∀ k : Fin 2,
        (![(G'.hom ⁻¹ᵁ U).ι ≫ (GrpObj.inv : G' ⟶ G').left, (G'.hom ⁻¹ᵁ U).ι] :
          Fin 2 → ((G'.hom ⁻¹ᵁ U).toScheme ⟶ G'.left)) k ≫ (p.pr i).left =
        ρ i ≫ (![(G.hom ⁻¹ᵁ U).ι ≫ (GrpObj.inv : G ⟶ G).left, (G.hom ⁻¹ᵁ U).ι] :
          Fin 2 → ((G.hom ⁻¹ᵁ U).toScheme ⟶ G.left)) k := by
      intro i k
      have := p.hom i
      fin_cases k
      · have h0 : (GrpObj.inv : G' ⟶ G').left ≫ (p.pr i).left =
            (p.pr i).left ≫ (GrpObj.inv : G ⟶ G).left := inv_pr p i 0
        show ((G'.hom ⁻¹ᵁ U).ι ≫ (GrpObj.inv : G' ⟶ G').left) ≫ (p.pr i).left =
          ρ i ≫ (G.hom ⁻¹ᵁ U).ι ≫ (GrpObj.inv : G ⟶ G).left
        rw [Category.assoc, h0, ← Category.assoc, ← hρ i, Category.assoc]
      · exact (hρ i).symm
    exact ⟨GeneratorPullback.boxGen L (fun i => (p.pr i).left) _ _
      (fun i => GeneratorPullback.pullAlong L (p.pr i).left (ρ i) _ _ _ (he i) t),
      isGen_boxGen L _ _ _ _ fun i => isGen_pullAlong L _ _ _ _ _ (he i) t ht⟩

end GlobalTheory
end
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory

theorem exists_sum_tmul_linearIndependent {F M N : Type} [Field F] [AddCommGroup M] [Module F M]
    [AddCommGroup N] [Module F N] (t : TensorProduct F M N) :
    ∃ (m : ℕ) (e : Fin m → M) (c : Fin m → N), LinearIndependent F e ∧ t = ∑ k, TensorProduct.tmul F (e k) (c k) := by
  classical
  let B := Module.Basis.ofVectorSpace F M
  obtain ⟨c, hc⟩ := TensorProduct.eq_repr_basis_left B t
  let σ := c.support.equivFin.symm
  refine ⟨_, fun k => B (σ k), fun k => c (σ k), ?_, ?_⟩
  · exact B.linearIndependent.comp (fun k => (σ k).val) (Subtype.val_injective.comp σ.injective)
  · rw [← hc, Finsupp.sum, ← Finset.sum_coe_sort]
    exact (Equiv.sum_comp σ (fun i => TensorProduct.tmul F (B i) (c i))).symm

section
variable {F : Type} [CommRing F] {Z Y T : Scheme.{0}} {L : LB Z} (p : Y ⟶ Spec (CommRingCat.of F))
  {K : Type} [Fintype K] (φ : K → (Y ⟶ Z)) (ε : K → ℤ)

noncomputable def svalAddHom (r : T ⟶ Y) (z : T) {J : (T ⟶ Z) → L.ι} (hJ : Good L z J) :
    SecMod p (LB.LinComb L φ ε) →+ T.presheaf.stalk z :=
  AddMonoidHom.mk' (fun s => sval s.sec r z J) (fun _ _ => gs_add r z _ (hJ.mem φ r) _ _)

theorem svalAddHom_smul (r : T ⟶ Y) (z : T) {J : (T ⟶ Z) → L.ι} (hJ : Good L z J) (c : F)
    (s : SecMod p (LB.LinComb L φ ε)) :
    svalAddHom p φ ε r z hJ (c • s) =
      gs (r ≫ p) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom c) * svalAddHom p φ ε r z hJ s :=
  (gs_mul r z _ (hJ.mem φ r) _ _).trans (congrArg (· * _)
    ((gs_res r z le_top (hJ.mem φ r) _).trans (gs_pull r p z ⊤ trivial _)))

noncomputable def secCompAddHom (N : LB Y) (j : N.ι) : SecMod p N →+ Γ(Y, N.U j) :=
  AddMonoidHom.mk' (fun s => s.sec.f j) (fun _ _ => rfl)

end

theorem tensor_sections_eq_zero_iff : ∀ (F : Type) [Field F] (Z : Scheme.{0}) (L : LB Z), L.IsLB → ∀ (Y₁ Y₂ : Scheme.{0}) (p₁ : Y₁ ⟶ Spec (CommRingCat.of F)) (p₂ : Y₂ ⟶ Spec (CommRingCat.of F)) [QuasiCompact p₁] [IsSeparated p₁] [QuasiCompact p₂] [IsSeparated p₂] (K₁ K₂ : Type) [Fintype K₁] [Fintype K₂] (φ₁ : K₁ → (Y₁ ⟶ Z)) (ε₁ : K₁ → ℤ) (φ₂ : K₂ → (Y₂ ⟶ Z)) (ε₂ : K₂ → ℤ) (n : ℕ) (a : Fin n → SecMod p₁ (LB.LinComb L φ₁ ε₁)) (b : Fin n → SecMod p₂ (LB.LinComb L φ₂ ε₂)), (∑ i, TensorProduct.tmul F (a i) (b i) = 0) ↔ ∀ (T : Scheme.{0}) (r₁ : T ⟶ Y₁) (r₂ : T ⟶ Y₂), r₁ ≫ p₁ = r₂ ≫ p₂ → ∀ (z : T) (J), Good L z J → ∑ i, sval (a i).sec r₁ z J * sval (b i).sec r₂ z J = 0 := by
  intro F _ Z L hL Y₁ Y₂ p₁ p₂ _ _ _ _ K₁ K₂ _ _ φ₁ ε₁ φ₂ ε₂ n a b
  have key : ∀ (T : Scheme.{0}) (r₁ : T ⟶ Y₁) (r₂ : T ⟶ Y₂), r₁ ≫ p₁ = r₂ ≫ p₂ → ∀ (z : T) (J), Good L z J →
      ∃ Φ : TensorProduct F (SecMod p₁ (LB.LinComb L φ₁ ε₁)) (SecMod p₂ (LB.LinComb L φ₂ ε₂)) →+ T.presheaf.stalk z,
        ∀ s t, Φ (TensorProduct.tmul F s t) = sval s.sec r₁ z J * sval t.sec r₂ z J := by
    intro T r₁ r₂ h z J hJ
    refine ⟨TensorProduct.liftAddHom
      ((AddMonoidHom.mul.compl₂ (svalAddHom p₂ φ₂ ε₂ r₂ z hJ)).comp (svalAddHom p₁ φ₁ ε₁ r₁ z hJ)) ?_, fun s t => rfl⟩
    intro c s t
    change svalAddHom p₁ φ₁ ε₁ r₁ z hJ (c • s) * svalAddHom p₂ φ₂ ε₂ r₂ z hJ t =
      svalAddHom p₁ φ₁ ε₁ r₁ z hJ s * svalAddHom p₂ φ₂ ε₂ r₂ z hJ (c • t)
    rw [svalAddHom_smul, svalAddHom_smul, h]
    ring
  constructor
  · intro h0 T r₁ r₂ h z J hJ
    obtain ⟨Φ, hΦ⟩ := key T r₁ r₂ h z J hJ
    have := congrArg Φ h0
    rwa [map_sum, map_zero, Finset.sum_congr rfl (fun i _ => hΦ (a i) (b i))] at this
  · intro H
    obtain ⟨m, e, c, he, ht⟩ := exists_sum_tmul_linearIndependent (∑ i, TensorProduct.tmul F (a i) (b i))
    have : QuasiCompact (Over.mk p₁).hom := ‹QuasiCompact p₁›
    have : IsSeparated (Over.mk p₁).hom := ‹IsSeparated p₁›
    have : QuasiCompact (Over.mk p₂).hom := ‹QuasiCompact p₂›
    have : IsSeparated (Over.mk p₂).hom := ‹IsSeparated p₂›
    have hc := (GlobalTheory.T.section_lin_comb_fiber_product_separated F Z L hL (Over.mk p₁) (Over.mk p₂) K₁ K₂ φ₁ ε₁ φ₂ ε₂).2 m
      (fun k => (e k).sec) (fun k => (c k).sec) (fun d hd => by
        have h1 : ∑ k, d k • e k = 0 := DVR.SecOps.sec_ext fun j =>
          (map_sum (secCompAddHom p₁ _ j) _ _).trans (hd j)
        exact funext (Fintype.linearIndependent_iff.1 he d h1)) (fun z J hJ => by
        have w : (fst (Over.mk p₁) (Over.mk p₂)).left ≫ p₁ = (snd (Over.mk p₁) (Over.mk p₂)).left ≫ p₂ :=
          (Over.w (fst (Over.mk p₁) (Over.mk p₂))).trans (Over.w (snd (Over.mk p₁) (Over.mk p₂))).symm
        obtain ⟨Φ, hΦ⟩ := key _ _ _ w z J hJ
        have h2 := congrArg Φ ht

        rw [map_sum, map_sum, Finset.sum_congr rfl (fun i _ => hΦ (a i) (b i)),
        Finset.sum_congr rfl (fun i _ => hΦ (e i) (c i))] at h2
        exact h2.symm.trans (H _ _ _ w z J hJ))
    rw [ht]
    refine Finset.sum_eq_zero fun k _ => ?_
    have : c k = 0 := DVR.SecOps.sec_ext fun j => hc k j
    rw [this, TensorProduct.tmul_zero]

end GlobalTheory
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT
namespace GlobalTheory.AdicSum
section
variable {R : Type} [CommRing R] {I : Ideal R} {E E' Ix : Type} [AddCommGroup E] [Module R E]
  [AddCommGroup E'] [Module R E']


open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing in
open scoped CategoryTheory.Obj in
attribute [local instance] Over.cartesianMonoidalCategory in
variable {R : Type} [CommRing R] {I : Ideal R} {E E' Ix : Type} [AddCommGroup E] [Module R E]
  [AddCommGroup E'] [Module R E'] in
theorem _root_.GlobalTheory.AdicSum.sumI_unique [IsNoetherianRing R] (hI : I ≤ Ideal.jacobson ⊥)
    {x : Ix → E} {s s' : E}
    (h : _root_.GlobalTheory.UT.SumI I x s) (h' : _root_.GlobalTheory.UT.SumI I x s') : s = s' := by
  classical
  obtain ⟨N, hN, hs, -, hconv⟩ := h
  obtain ⟨N', hN', hs', -, hconv'⟩ := h'
  set M := N ⊔ N' with hM
  have hMfg : M.FG := hN.sup hN'
  haveI : Module.Finite R M := Module.Finite.iff_fg.mpr hMfg
  have hmem : s - s' ∈ M := M.sub_mem (Submodule.mem_sup_left hs) (Submodule.mem_sup_right hs')
  have hpow : ∀ n : ℕ, (⟨s - s', hmem⟩ : M) ∈ I ^ n • (⊤ : Submodule R M) := by
    intro n
    obtain ⟨S, hS⟩ := hconv n
    obtain ⟨S', hS'⟩ := hconv' n
    have h1 := hS (S ∪ S') Finset.subset_union_left
    have h2 := hS' (S ∪ S') Finset.subset_union_right
    have h3 : s - s' ∈ I ^ n • M := by
      have e : s - s' = (s - ∑ i ∈ S ∪ S', x i) - (s' - ∑ i ∈ S ∪ S', x i) := by abel
      rw [e]
      exact Submodule.sub_mem _ (Submodule.smul_mono le_rfl le_sup_left h1)
        (Submodule.smul_mono le_rfl le_sup_right h2)
    rw [← Submodule.map_subtype_top M, ← Submodule.map_smul''] at h3
    obtain ⟨y, hy, hyeq⟩ := h3
    have hy' : y = ⟨s - s', hmem⟩ := Subtype.ext hyeq
    rwa [← hy']
  have h0 : (⟨s - s', hmem⟩ : M) = 0 := by
    rw [Ideal.jacobson_bot] at hI
    have hK := Ideal.iInf_pow_smul_eq_bot_of_le_jacobson (M := M) I hI
    rw [← Submodule.mem_bot R, ← hK, Submodule.mem_iInf]
    exact hpow
  exact sub_eq_zero.mp (congrArg Subtype.val h0)


open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing in
open scoped CategoryTheory.Obj in
attribute [local instance] Over.cartesianMonoidalCategory in
variable {R : Type} [CommRing R] {I : Ideal R} {E E' Ix : Type} [AddCommGroup E] [Module R E]
  [AddCommGroup E'] [Module R E'] in
theorem _root_.GlobalTheory.AdicSum.sumI_map (f : E →ₗ[R] E') {x : Ix → E} {s : E}
    (h : _root_.GlobalTheory.UT.SumI I x s) :
    _root_.GlobalTheory.UT.SumI I (fun i => f (x i)) (f s) := by
  obtain ⟨N, hN, hs, hx, hconv⟩ := h
  refine ⟨N.map f, hN.map f, Submodule.mem_map_of_mem hs,
    fun i => Submodule.mem_map_of_mem (hx i), fun n => ?_⟩
  obtain ⟨S, hS⟩ := hconv n
  refine ⟨S, fun T hT => ?_⟩

  rw [← Submodule.map_smul'', ← map_sum, ← map_sub]
  exact Submodule.mem_map_of_mem (hS T hT)


open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing in
open scoped CategoryTheory.Obj in
attribute [local instance] Over.cartesianMonoidalCategory in
variable {R : Type} [CommRing R] {I : Ideal R} {E E' Ix : Type} [AddCommGroup E] [Module R E]
  [AddCommGroup E'] [Module R E'] in
theorem _root_.GlobalTheory.AdicSum.sumI_add {x x' : Ix → E} {s s' : E}
    (h : _root_.GlobalTheory.UT.SumI I x s) (h' : _root_.GlobalTheory.UT.SumI I x' s') :
    _root_.GlobalTheory.UT.SumI I (fun i => x i + x' i) (s + s') := by
  classical
  obtain ⟨N, hN, hs, hx, hconv⟩ := h
  obtain ⟨N', hN', hs', hx', hconv'⟩ := h'
  refine ⟨N ⊔ N', hN.sup hN', Submodule.add_mem_sup hs hs',
    fun i => Submodule.add_mem_sup (hx i) (hx' i), fun n => ?_⟩
  obtain ⟨S, hS⟩ := hconv n
  obtain ⟨S', hS'⟩ := hconv' n
  refine ⟨S ∪ S', fun T hT => ?_⟩
  have e : s + s' - ∑ i ∈ T, (x i + x' i) = (s - ∑ i ∈ T, x i) + (s' - ∑ i ∈ T, x' i) := by
    rw [Finset.sum_add_distrib]; abel
  rw [e]
  exact Submodule.add_mem _
    (Submodule.smul_mono le_rfl le_sup_left (hS T (Finset.union_subset_left hT)))
    (Submodule.smul_mono le_rfl le_sup_right (hS' T (Finset.union_subset_right hT)))


open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing in
open scoped CategoryTheory.Obj in
attribute [local instance] Over.cartesianMonoidalCategory in
variable {R : Type} [CommRing R] {I : Ideal R} {E E' Ix : Type} [AddCommGroup E] [Module R E]
  [AddCommGroup E'] [Module R E'] in
theorem _root_.GlobalTheory.AdicSum.sumI_comp_iff {Jx : Type} {e : Jx → Ix}
    (he : Function.Injective e) {x : Ix → E}
    (h0 : ∀ i, i ∉ Set.range e → x i = 0) {s : E} :
    _root_.GlobalTheory.UT.SumI I (x ∘ e) s ↔ _root_.GlobalTheory.UT.SumI I x s := by
  classical
  constructor
  · rintro ⟨N, hN, hs, hx, hconv⟩
    refine ⟨N, hN, hs, fun i => ?_, fun n => ?_⟩
    · by_cases hi : i ∈ Set.range e
      · obtain ⟨j, rfl⟩ := hi
        exact hx j
      · rw [h0 i hi]
        exact N.zero_mem
    · obtain ⟨S, hS⟩ := hconv n
      refine ⟨S.map ⟨e, he⟩, fun T hT => ?_⟩
      rw [← Finset.sum_preimage e T he.injOn x (fun i _ hi => h0 i hi)]
      refine hS _ fun j hj => ?_
      rw [Finset.mem_preimage]
      exact hT (Finset.mem_map_of_mem _ hj)
  · rintro ⟨N, hN, hs, hx, hconv⟩
    refine ⟨N, hN, hs, fun j => hx (e j), fun n => ?_⟩
    obtain ⟨S, hS⟩ := hconv n
    refine ⟨S.preimage e he.injOn, fun T hT => ?_⟩
    have hpre : (T.map ⟨e, he⟩ ∪ S).preimage e he.injOn = T := by
      ext j
      simp only [Finset.mem_preimage, Finset.mem_union, Finset.mem_map,
        Function.Embedding.coeFn_mk, he.eq_iff, exists_eq_right]
      exact ⟨fun hj => hj.elim id fun hj => hT (Finset.mem_preimage.mpr hj), Or.inl⟩
    have hsum := hS (T.map ⟨e, he⟩ ∪ S) Finset.subset_union_right
    rw [← Finset.sum_preimage e _ he.injOn x (fun i _ hi => h0 i hi), hpre] at hsum
    exact hsum

end


open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing in
open scoped CategoryTheory.Obj in
attribute [local instance] Over.cartesianMonoidalCategory in
theorem _root_.GlobalTheory.AdicSum.sumF_calculus : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R),
    _root_.ReciprocityTheory.ChartRestriction.G.Out.AdmBase R I → ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] (Ix : Type)
    (x x' : Ix → F) (s s' : F),
    (_root_.GlobalTheory.UT.SumF I F x s → _root_.GlobalTheory.UT.SumF I F x s' →
      s = s') ∧
    (_root_.GlobalTheory.UT.SumF I F x s → _root_.GlobalTheory.UT.SumF I F x' s' →
      ∀ c : F, _root_.GlobalTheory.UT.SumF I F (fun i => c * x i + x' i) (c * s + s')) ∧
    ∀ (Jx : Type) (e : Jx → Ix), Function.Injective e → (∀ i, i ∉ Set.range e → x i = 0) →
      (_root_.GlobalTheory.UT.SumF I F (x ∘ e) s ↔
        _root_.GlobalTheory.UT.SumF I F x s) := by
  intro R _ _ I hadm F _ _ Ix x x' s s'
  obtain ⟨hnoeth, -, -, hcomplete⟩ := hadm
  haveI := hnoeth
  haveI := hcomplete
  letI : Module R F := Module.compHom F (algebraMap R (FractionRing R))
  refine ⟨fun h h' => _root_.GlobalTheory.AdicSum.sumI_unique (IsAdicComplete.le_jacobson_bot I) h h',
    fun h h' c => ?_, fun Jx e he h0 => _root_.GlobalTheory.AdicSum.sumI_comp_iff he h0⟩
  let f : F →ₗ[R] F :=
    { toFun := fun y => c * y
      map_add' := mul_add c
      map_smul' := fun r y => by
        show c * (algebraMap R (FractionRing R) r • y) = algebraMap R (FractionRing R) r • (c * y)
        exact Algebra.mul_smul_comm _ _ _ }
  exact _root_.GlobalTheory.AdicSum.sumI_add (_root_.GlobalTheory.AdicSum.sumI_map f h) h'

end GlobalTheory.AdicSum
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

namespace GlobalTheory.CrossTheta

theorem gs_comp_stalk {X Y Z : Scheme.{0}} (r : Z ⟶ Y) (g : Y ⟶ X) (z : Z) (U : X.Opens) (h : g (r z) ∈ U)
    (a : Γ(X, U)) : gs (r ≫ g) z U a = (r.stalkMap z).hom (gs g (r z) U a) := by
  rw [gs_eq (r ≫ g) z U h, gs_eq g (r z) U h]
  exact (Scheme.Hom.germ_stalkMap_apply r (g ⁻¹ᵁ U) z h _).symm

theorem cross_val {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB) (p : Y ⟶ X) (b : Y ⟶ Y) {k k' : ℤ}
    (s₁ s₂ : LB.Sec (LB.LinComb L (fun _ : Fin 1 => p) (fun _ => k)))
    (s₁' s₂' : LB.Sec (LB.LinComb L (fun _ : Fin 1 => p) (fun _ => k')))
    (H : ∀ y J, Good L y J → sval s₁ b y J * sval s₂' (𝟙 _) y J = sval s₂ b y J * sval s₁' (𝟙 _) y J)
    {Z : Scheme.{0}} (r : Z ⟶ Y) (z : Z) {J} (hJ : Good L z J) :
    sval s₁ (r ≫ b) z J * sval s₂' r z J = sval s₂ (r ≫ b) z J * sval s₁' r z J := by
  obtain ⟨I, hI, e⟩ := exists_good L hL (r z) (K := Bool) (fun c => cond c (b ≫ p) (𝟙 _ ≫ p))
    (fun c => J (r ≫ cond c (b ≫ p) (𝟙 _ ≫ p))) (fun a c e => congrArg (fun q => J (r ≫ q)) e)
    (fun c => hJ (r ≫ cond c (b ≫ p) (𝟙 _ ≫ p)))
  have v : ∀ (c : Y ⟶ Y) {m : ℤ} (s : LB.Sec (LB.LinComb L (fun _ : Fin 1 => p) (fun _ => m))),
      I (c ≫ p) = J (r ≫ c ≫ p) → sval s (r ≫ c) z J = (r.stalkMap z).hom (sval s c (r z) I) := by
    intro c m s hc
    rw [sval_of s (r ≫ c) z J (fun _ => I (c ≫ p)) (fun _ => by rw [Category.assoc, hc])]
    exact gs_comp_stalk r c z _ (hI.mem (fun _ : Fin 1 => p) c) _
  have h := congrArg (r.stalkMap z).hom (H (r z) I hI)
  rw [map_mul, map_mul, ← v b s₁ (e true), ← v b s₂ (e true), ← v (𝟙 _) s₁' (e false), ← v (𝟙 _) s₂' (e false),
    Category.comp_id] at h
  exact h

theorem translT_whisker {S : Scheme.{0}} (A : Over S) [GrpObj A] {T : Over S} (a : A ⟶ A) [IsMonHom a] (x : T ⟶ A) :
    translT A x ≫ T ◁ a = T ◁ a ≫ translT A (x ≫ a) := by
  apply CartesianMonoidalCategory.hom_ext
  · simp [translT]
  · simp only [translT, Category.assoc, whiskerLeft_snd, lift_snd, lift_snd_assoc, ThetaPowOrder.translPt_eq,
      MonObj.comp_mul, MonObj.mul_comp, whiskerLeft_fst_assoc]

theorem cross_act {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} (hL : L.IsLB) {T : Over S}
    (a : A ⟶ A) [IsMonHom a] {k k' : ℤ} (θ : ThetaGrp A L k T) (θ' : ThetaGrp A L k' T) (hp : θ.pt = θ'.pt ≫ a)
    {t₁ t₂ T₁ T₂ : LB.Sec (LPow A L k T)} {t₁' t₂' T₁' T₂' : LB.Sec (LPow A L k' T)}
    (h₁ : IsActOf A L k θ t₁ T₁) (h₂ : IsActOf A L k θ t₂ T₂) (h₁' : IsActOf A L k' θ' t₁' T₁')
    (h₂' : IsActOf A L k' θ' t₂' T₂') :
    (∀ y J, Good L y J → sval (L := L) t₁ (T ◁ a).left y J * sval (L := L) t₂' (𝟙 _) y J =
      sval (L := L) t₂ (T ◁ a).left y J * sval (L := L) t₁' (𝟙 _) y J) ↔
    (∀ y J, Good L y J → sval (L := L) T₁ (T ◁ a).left y J * sval (L := L) T₂' (𝟙 _) y J =
      sval (L := L) T₂ (T ◁ a).left y J * sval (L := L) T₁' (𝟙 _) y J) := by
  have c : (T ◁ a).left ≫ (translT A θ.pt).left = (translT A θ'.pt).left ≫ (T ◁ a).left := by
    rw [← Over.comp_left, ← Over.comp_left, hp, translT_whisker]
  have key : ∀ {Z : Scheme.{0}} (r : Z ⟶ (T ⊗ A).left) (z : Z) {J}, Good L z J →
      (sval (L := L) T₁ (r ≫ (T ◁ a).left) z J * sval (L := L) T₂' r z J =
        sval (L := L) T₂ (r ≫ (T ◁ a).left) z J * sval (L := L) T₁' r z J ↔
      sval (L := L) t₁ ((r ≫ (translT A θ'.pt).left) ≫ (T ◁ a).left) z J *
          sval (L := L) t₂' (r ≫ (translT A θ'.pt).left) z J =
        sval (L := L) t₂ ((r ≫ (translT A θ'.pt).left) ≫ (T ◁ a).left) z J *
          sval (L := L) t₁' (r ≫ (translT A θ'.pt).left) z J) := by
    intro Z r z J hJ
    rw [ThetaPowOrder.act_sval h₁ _ z hJ, ThetaPowOrder.act_sval h₂ _ z hJ, ThetaPowOrder.act_sval h₁' _ z hJ,
      ThetaPowOrder.act_sval h₂' _ z hJ, Category.assoc, c, ← Category.assoc, _root_.mul_mul_mul_comm,
      _root_.mul_mul_mul_comm _ (sval (L := L) t₂ _ z J), ← Units.val_mul, Units.mul_right_inj]
  constructor
  · intro H y J hJ
    have h := (key (𝟙 _) y hJ).2 (cross_val hL _ _ t₁ t₂ t₁' t₂' H _ y hJ)
    rwa [Category.id_comp] at h
  · intro H y J hJ
    have h := (key (translT A θ'.pt⁻¹).left y hJ).1 (cross_val hL _ _ T₁ T₂ T₁' T₂' H _ y hJ)
    rwa [← Over.comp_left, ThetaPowOrder.translT_comp, mul_inv_cancel, ThetaPowOrder.translT_one, Over.id_left,
      Category.id_comp] at h

end GlobalTheory.CrossTheta

namespace GlobalTheory

theorem cross_iff_of_isActOf : LL → ∀ (R : Type) [CommRing R] [IsDomain R] (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (F : Type) [Field F] [Algebra (FractionRing R) F] (a : A.A ⟶ A.A), IsMonHom a → ∀ (j j' : ℕ) (θ : ThetaGrp A.A A.L (j : ℤ) (TFK (R := R) F)) (θ' : ThetaGrp A.A A.L (j' : ℤ) (TFK (R := R) F)), θ.pt = θ'.pt ≫ a → ∀ (t₁ t₂ T₁ T₂ : SecA A F j) (t₁' t₂' T₁' T₂' : SecA A F j'), IsActOf A.A A.L j θ t₁ T₁ → IsActOf A.A A.L j θ t₂ T₂ → IsActOf A.A A.L j' θ' t₁' T₁' → IsActOf A.A A.L j' θ' t₂' T₂' → (Cross a t₁ t₂ t₁' t₂' ↔ Cross a T₁ T₂ T₁' T₂') := by
  intro _ R _ _ A F _ _ a ha j j' θ θ' hp t₁ t₂ T₁ T₂ t₁' t₂' T₁' T₂' h₁ h₂ h₁' h₂'
  exact CrossTheta.cross_act A.isLB a θ θ' hp h₁ h₂ h₁' h₂'

end GlobalTheory
end
