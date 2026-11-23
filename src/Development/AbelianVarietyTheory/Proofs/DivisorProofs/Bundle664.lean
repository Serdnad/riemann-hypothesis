module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle535
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle620
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle589
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OmegaFactorization
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle597
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle546
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle621
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAffineHomOfIsPullback
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle008
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Module.LinearMap.Star
public import Mathlib.Analysis.Complex.Norm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle623
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
import Mathlib.RingTheory.SimpleRing.Principal
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle547
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat

noncomputable section

namespace GlobalTheory.HomFixMatEx

theorem liftTop (Rg : Type) [CommRing Rg] (A : Over (Sp Rg)) (R : Type) [CommRing R] (t : Sp R ⟶ Sp Rg)
    (A' : Over (Sp R)) (φA' : A'.left ⟶ A.left) (hpb : IsPullback φA' A'.hom A.hom t) :
    ∃ ψ : A'.left ⟶ (topS Rg ⊗ A).left, ψ ≫ (snd (topS Rg) A).left = φA' := by
  let a0 : A'.left ⟶ (⊤ : (Sp Rg).Opens).toScheme :=
    IsOpenImmersion.lift (⊤ : (Sp Rg).Opens).ι (A'.hom ≫ t) (by simp)
  let X : Over (Sp Rg) := Over.mk (A'.hom ≫ t)
  let a : X ⟶ topS Rg := Over.homMk a0 (by simp only [a0, X, topS, overRes, baseOver, Over.mk_hom, Category.comp_id]; exact IsOpenImmersion.lift_fac _ _ _)
  let b : X ⟶ A := Over.homMk φA' hpb.w
  refine ⟨(lift a b).left, ?_⟩
  rw [← Over.comp_left, lift_snd]
  rfl

theorem zero_comp (Rg : Type) [CommRing Rg] (A : Over (Sp Rg)) [GrpObj A] (R : Type) [CommRing R]
    (t : Sp R ⟶ Sp Rg) (A' : Over (Sp R)) [GrpObj A'] (φA' : A'.left ⟶ A.left) (h : IsGrpPullback A' A t φA') :
    zeroPt A' ≫ φA' = t ≫ eSec A := by
  let T : Over (Sp R) := 𝟙_ (Over (Sp R))
  let u : Over.mk (T.hom ≫ t) ⟶ A := Over.homMk ((1 : T ⟶ A').left ≫ φA') (by
    simp only [Over.mk_hom, Category.assoc]
    rw [h.1.w, ← Category.assoc, Over.w])
  have hu : u * u = u := Over.OverMorphism.ext (by
    rw [h.2 T 1 1 u u rfl rfl, _root_.mul_one]; rfl)
  have hu1 : u = 1 := mul_eq_left.1 hu
  have e := congrArg (fun x => Over.Hom.left x) hu1
  simp only [u, Over.homMk_left] at e
  rw [Hom.one_def, Hom.one_def] at e
  simp at e
  exact e
end GlobalTheory.HomFixMatEx

namespace GlobalTheory.HomFixMatEx

theorem res_appLE {X Y : Scheme.{0}} (f : X ⟶ Y) {U : Y.Opens} {V V' : X.Opens} (e : V ≤ f ⁻¹ᵁ U) (h : V' ≤ V)
    (x : Γ(Y, U)) :
    (X.presheaf.map (homOfLE h).op).hom ((f.appLE U V e).hom x) = (f.appLE U V' (h.trans e)).hom x := by
  rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_map]

end GlobalTheory.HomFixMatEx

namespace GlobalTheory.HomFixMat
open GlobalTheory.HomFixMatEx

theorem exists_isMat : ∀ (Rg : Type) [CommRing Rg] [IsNoetherianRing Rg] (A B : Over (Sp Rg)) [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B] (L : LB A.left) (M : LB B.left) (k : ℕ) (mA mB : ℕ) (bA : Fin mA → LB.Sec (LPow A L (k : ℤ) (topS Rg))) (bB : Fin mB → LB.Sec (LPow B M (k : ℤ) (topS Rg))) (eA : LB.Gen (L.pull (eSec A))) (eB : LB.Gen (M.pull (eSec B))), Hyps L M k bA bB eA eB → ∀ (R : Type) [CommRing R] (t : Sp R ⟶ Sp Rg) (A' B' : Over (Sp R)) [GrpObj A'] [GrpObj B'] (φA' : A'.left ⟶ A.left) (φB' : B'.left ⟶ B.left) (Φ' : A' ⟶ B'), IsTest A B L M t A' B' φA' φB' Φ' → ∃ c, IsMat L M k bA bB eA eB t A' B' φA' φB' Φ' c := by
  intro Rg _ _ A B _ _ _ _ L M k mA mB bA bB eA eB hH R _ t A' B' _ _ φA' φB' Φ' hT
  obtain ⟨_, _, hL, hM, heA, heB, _, _, _, hbA, _⟩ := hH
  obtain ⟨hpA, hpB, hΦ, hiso⟩ := hT
  obtain ⟨ψA, hψA⟩ := liftTop Rg A R t A' φA' hpA.1
  obtain ⟨ψB, hψB⟩ := liftTop Rg B R t B' φB' hpB.1
  obtain ⟨w, hw⟩ := hiso
  have eg : (Φ'.left ≫ ψB) ≫ (snd (topS Rg) B).left = Φ'.left ≫ φB' := by rw [Category.assoc, hψB]
  obtain ⟨α₀, hα₀⟩ : ∃ α₀ : LB.Gen (isoLB (L := L) (M := M) k Φ' ψA ψB), α₀.IsGen := by
    have := GlobalTheory.T.exists_lineBundlePower_iso_reindexed_charts L M φA' Φ'.left φB' k w hw
    show ∃ α₀ : LB.Gen (LB.div (powPull M ((Φ'.left ≫ ψB) ≫ (snd (topS Rg) B).left) (k : ℤ))
      (powPull L (ψA ≫ (snd (topS Rg) A).left) (k : ℤ))), α₀.IsGen
    rw [eg, hψA]; exact this
  have hΦ0 : zeroPt A' ≫ Φ'.left = zeroPt B' := by
    haveI := hΦ
    exact congrArg Over.Hom.left (IsMonHom.one_hom (f := Φ'))
  have hz1 : zeroPt A' ≫ (ψA ≫ (snd (topS Rg) A).left) = t ≫ eSec A := by
    rw [hψA]; exact zero_comp Rg A R t A' φA' hpA
  have hz2 : zeroPt A' ≫ ((Φ'.left ≫ ψB) ≫ (snd (topS Rg) B).left) = t ≫ eSec B := by
    rw [eg, ← Category.assoc, hΦ0]; exact zero_comp Rg B R t B' φB' hpB
  have hzπ : zeroPt A' ≫ A'.hom = 𝟙 (Sp R) := Over.w η[A']
  obtain ⟨α, hα, hrig⟩ := GlobalTheory.T.exists_rescaled_lineBundlePower_iso_generator (Z₀ := Sp Rg) L M (ψA ≫ (snd (topS Rg) A).left)
    ((Φ'.left ≫ ψB) ≫ (snd (topS Rg) B).left) (eSec A) (eSec B) t (zeroPt A') A'.hom k eA eB α₀
    hL hM heA heB hα₀ hzπ hz1 hz2
  have key : ∀ j : Fin mB, ∃ cj : Fin mA → Γ(Sp R, ⊤), ∀ p : (Fin 1 → M.ι) × (Fin 1 → L.ι),
      ((Φ'.left ≫ ψB).appLE (LB.wchart M (fun _ : Fin 1 => (snd (topS Rg) B).left) p.1)
          ((isoLB (L := L) (M := M) k Φ' ψA ψB).U p)
          (inf_le_left.trans (GlobalTheory.HomFixMat.wchart_comp_le M _ _ p.1))).hom ((bB j).f p.1) =
        (α.s p).val * ∑ i, (A'.hom.appLE ⊤ ((isoLB (L := L) (M := M) k Φ' ψA ψB).U p) (by simp)).hom (cj i) *
          (ψA.appLE (LB.wchart L (fun _ : Fin 1 => (snd (topS Rg) A).left) p.2)
            ((isoLB (L := L) (M := M) k Φ' ψA ψB).U p)
            (inf_le_right.trans (GlobalTheory.HomFixMat.wchart_comp_le L _ _ p.2))).hom ((bA i).f p.2) := by
    intro j
    obtain ⟨σ, hσ⟩ := GlobalTheory.T.exists_lineBundlePowerPullback_section_pullback M (snd (topS Rg) B).left (Φ'.left ≫ ψB) (k : ℤ) (bB j)
    obtain ⟨s, hs⟩ := GlobalTheory.T.power_pullback_section_exists L M (ψA ≫ (snd (topS Rg) A).left) ((Φ'.left ≫ ψB) ≫ (snd (topS Rg) B).left)
      (k : ℤ) α hα hL hM σ
    obtain ⟨c, hc⟩ := GlobalTheory.T.exists_coeff_pullback_baseChangeStableSectionBasis Rg A L k mA bA hbA R t A' φA' hpA.1 ψA hψA s
    refine ⟨c, fun p => ?_⟩
    have e1 := hs p

    rw [hσ p.1, hc p.2, map_sum] at e1
    erw [res_appLE] at e1
    simp only [map_mul] at e1
    erw [e1]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
    · exact res_appLE _ _ _ _
    · exact res_appLE _ _ _ _
  choose cj hcj using key
  exact ⟨fun i j => cj j i, ψA, ψB, α, hψA, hψB, hα, hrig, fun j p => hcj j p⟩

end GlobalTheory.HomFixMat
end
end

section

open Matrix NumberField GlobalTheory.UPel.HT GlobalTheory.UPel.HT.LieLin GlobalTheory.UPel.HT.LieLin.RankIdeal

theorem _root_.GlobalTheory.T.eigenPartProjectionMatrix_map_mulVec_of_eigenvector : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (B : Type) [CommRing B]
    (βB : R →+* B) (n : ℕ) (M : 𝓞 D.F →+* Matrix (Fin n) (Fin n) B) (K : Type) [CommRing K] (g : B →+* K)
    (i : Fin D.a) (v : Fin n → K), (∀ c : 𝓞 D.F, (M c).map g *ᵥ v = g (βB (b.t i c)) • v) →
      (projMat b βB M i).map g *ᵥ v = v := by
  first | (exact @GlobalTheory.UPel.HT.LieLin.RankIdeal.projMat_map_mulVec_of_eig) | (exact GlobalTheory.UPel.HT.LieLin.RankIdeal.projMat_map_mulVec_of_eig) | (intros; apply GlobalTheory.UPel.HT.LieLin.RankIdeal.projMat_map_mulVec_of_eig  <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

noncomputable section
namespace GlobalTheory.UPel.HT.Hecke.PullInj

variable {X Y Z : Scheme.{0}}

theorem gen_germ {L : LB X} {w : LB.Gen L} (hw : w.IsGen) (r : Z ⟶ X) (z : Z) {k l : L.ι}
    (hk : r z ∈ L.U k) (hl : r z ∈ L.U l) :
    gm r z _ (w.s k) = gm r z (L.U k ⊓ L.U l) (L.g k l) * gm r z _ (w.s l) := by
  have hm : r z ∈ L.U k ⊓ L.U l := ⟨hk, hl⟩
  exact (gm_res r z inf_le_left hm _).symm.trans ((congrArg (gm r z _) (hw k l)).trans
    ((map_mul _ _ _).trans (congrArg _ (gm_res r z inf_le_right hm _))))

theorem gm_pull_g (Q : LB Y) (F : X ⟶ Y) (r : Z ⟶ X) (z : Z) {j j' : PUnit → Q.ι}
    (hj : F (r z) ∈ Q.U (j PUnit.unit)) (hj' : F (r z) ∈ Q.U (j' PUnit.unit)) :
    gm r z ((Q.pull F).U j ⊓ (Q.pull F).U j') ((Q.pull F).g j j') =
      gm (r ≫ F) z (Q.U (j PUnit.unit) ⊓ Q.U (j' PUnit.unit)) (Q.g (j PUnit.unit) (j' PUnit.unit)) := by
  have hp : r z ∈ (Q.pull F).U j ⊓ (Q.pull F).U j' := ⟨mem_pull.2 hj, mem_pull.2 hj'⟩
  show gm r z _ (∏ _k : PUnit, (res _ (pullU F _ (Q.g _ _))) ^ (1 : ℤ)) = _
  rw [Fintype.prod_unique, zpow_one]
  exact (gm_res r z _ hp _).trans (gm_pull r F z (Q.U (j PUnit.unit) ⊓ Q.U (j' PUnit.unit)) ⟨hj, hj'⟩ _)

theorem germ_div_g (M L : LB X) (r : Z ⟶ X) (z : Z) {p q : M.ι × L.ι}
    (hp : r z ∈ (LB.div M L).U p) (hq : r z ∈ (LB.div M L).U q) :
    gm r z _ ((LB.div M L).g p q) =
      gm r z (M.U p.1 ⊓ M.U q.1) (M.g p.1 q.1) * (gm r z (L.U p.2 ⊓ L.U q.2) (L.g p.2 q.2))⁻¹ := by
  have hm : r z ∈ (LB.div M L).U p ⊓ (LB.div M L).U q := ⟨hp, hq⟩
  show gm r z _ (res _ (M.g _ _) * (res _ (L.g _ _))⁻¹) = _
  exact (map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res r z _ hm _) ((map_inv _ _).trans (congrArg _ (gm_res r z _ hm _))))

theorem mem_divPull {Q₁ Q₂ : LB Y} {F : X ⟶ Y} {x : X} {k : (PUnit → Q₂.ι) × (PUnit → Q₁.ι)} :
    x ∈ (LB.div (Q₂.pull F) (Q₁.pull F)).U k ↔ F x ∈ Q₂.U (k.1 PUnit.unit) ∧ F x ∈ Q₁.U (k.2 PUnit.unit) :=
  ⟨fun h => ⟨mem_pull.1 h.1, mem_pull.1 h.2⟩, fun h => ⟨mem_pull.2 h.1, mem_pull.2 h.2⟩⟩

theorem gm_top_eq {S : Scheme.{0}} (A : Over S) [GrpObj A] (hA : IsAbelianScheme A) (g : Γ(A.left, ⊤)ˣ)
    (r r' : Z ⟶ A.left) (e : r ≫ A.hom = r' ≫ A.hom) (z : Z) : gm r z ⊤ g = gm r' z ⊤ g := by
  obtain ⟨c, hc⟩ := (GlobalTheory.globalFns_holds S A hA).2 g.val
  have h1 : ∀ r₀ : Z ⟶ A.left, gs r₀ z ⊤ g.val = gs (r₀ ≫ A.hom) z ⊤ c := fun r₀ => by
    rw [← hc]; exact gs_pull r₀ A.hom z ⊤ trivial c
  apply Units.ext
  rw [← gs_unit r z ⊤ trivial, ← gs_unit r' z ⊤ trivial, h1, h1, e]

end GlobalTheory.UPel.HT.Hecke.PullInj

namespace GlobalTheory.UPel.HT.Hecke.PullInj

variable {S : Scheme.{0}}

theorem transl_axis₁ (A : Over S) [GrpObj A] [IsCommMonObj A] (h : 𝟙_ (Over S) ⟶ A) :
    lift (1 : A ⟶ A) (𝟙 A) ≫ transl (lift (1 : 𝟙_ (Over S) ⟶ A) h : 𝟙_ (Over S) ⟶ G2 A) =
      transl h ≫ lift (1 : A ⟶ A) (𝟙 A) := by
  apply CartesianMonoidalCategory.hom_ext
  · simp [transl, MonObj.mul_comp, MonObj.comp_mul]
  · simp [transl, MonObj.mul_comp, MonObj.comp_mul]

theorem transl_axis₂ (A : Over S) [GrpObj A] [IsCommMonObj A] (h : 𝟙_ (Over S) ⟶ A) :
    lift (𝟙 A) (1 : A ⟶ A) ≫ transl (lift h (1 : 𝟙_ (Over S) ⟶ A) : 𝟙_ (Over S) ⟶ G2 A) =
      transl h ≫ lift (𝟙 A) (1 : A ⟶ A) := by
  apply CartesianMonoidalCategory.hom_ext
  · simp [transl, MonObj.mul_comp, MonObj.comp_mul]
  · simp [transl, MonObj.mul_comp, MonObj.comp_mul]

theorem grpScheme_monHom_square_lift_one_left {A A' : Over S} [GrpObj A] [IsCommMonObj A] [GrpObj A'] [IsCommMonObj A'] (ψ : A ⟶ A')
    [IsMonHom ψ] : lift (1 : A ⟶ A) (𝟙 A) ≫ lift (fst A A ≫ ψ) (snd A A ≫ ψ) = ψ ≫ lift (1 : A' ⟶ A') (𝟙 A') := by
  apply CartesianMonoidalCategory.hom_ext
  · simp
  · simp

theorem grpScheme_monHom_square_lift_one_right {A A' : Over S} [GrpObj A] [IsCommMonObj A] [GrpObj A'] [IsCommMonObj A'] (ψ : A ⟶ A')
    [IsMonHom ψ] : lift (𝟙 A) (1 : A ⟶ A) ≫ lift (fst A A ≫ ψ) (snd A A ≫ ψ) = ψ ≫ lift (𝟙 A') (1 : A' ⟶ A') := by
  apply CartesianMonoidalCategory.hom_ext
  · simp
  · simp

end GlobalTheory.UPel.HT.Hecke.PullInj
end
end

section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.WeightTwoSum
open scoped ContDiff nonZeroDivisors

namespace GlobalTheory.WeightTwoCompare

variable {E : Type} [Field E] [NumberField E] {I : Type} [Fintype I]

theorem prodCpow {J : Type} (t : Finset J) (f : J → ℝ) (hf : ∀ j, 0 ≤ f j) (w : ℂ) :
    ∏ j ∈ t, ((f j : ℝ) : ℂ) ^ w = (((∏ j ∈ t, f j : ℝ)) : ℂ) ^ w := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha, ih, Complex.ofReal_mul,
      Complex.mul_cpow_ofReal_nonneg (hf a) (Finset.prod_nonneg fun j _ => hf j)]

theorem norm_cpow_eq_exp {h : ℂ} (hh : h ≠ 0) (σ : ℂ) :
    ((‖h‖ : ℝ) : ℂ) ^ (-2 * σ) = Complex.exp (-σ * ((Real.log (Complex.normSq h) : ℝ) : ℂ)) := by
  have hn : ((‖h‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.2 hh
  rw [Complex.cpow_def_of_ne_zero hn, ← Complex.ofReal_log (norm_nonneg _), Complex.normSq_eq_norm_sq,
    Real.log_pow]
  congr 1
  push_cast
  ring

variable [IsCMField E]

theorem defCoord_eq (φ : I → E →+* ℂ) (e : I ≃ Emb (maximalRealSubfield E))
    (he : ∀ (i : I) (a : maximalRealSubfield E), φ i (a : E) = ((e i a : ℝ) : ℂ)) (θ : E) {z : I → ℂ}
    (hz : z ∈ polydisc I) (a b : maximalRealSubfield E) (i : I) :
    defCoord φ z ((a : E) + (b : E) * θ) i =
      (1 + z i) / (2 * (Real.pi : ℂ) * Complex.I) * latPt (modPt φ e θ z) (a, b) (e i) := by
  have h1 := one_add_ne_zero hz i
  have hπ : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
    have : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    exact mul_ne_zero (mul_ne_zero two_ne_zero this) Complex.I_ne_zero
  simp only [defCoord, latPt, modPt, Equiv.symm_apply_apply, map_add (f := _), map_mul, he, Complex.conj_ofReal]
  field_simp
  ring

theorem defTerm_eq (φ : I → E →+* ℂ) (e : I ≃ Emb (maximalRealSubfield E))
    (he : ∀ (i : I) (a : maximalRealSubfield E), φ i (a : E) = ((e i a : ℝ) : ℂ)) (θ : E) {z : I → ℂ}
    (hz : z ∈ polydisc I) (σ : ℂ) (a b : maximalRealSubfield E) :
    defTerm φ 2 z σ ((a : E) + (b : E) * θ) =
      (homFac z)⁻¹ ^ 2 * Complex.exp (-σ * logFac z) * eisTerm 2 σ (modPt φ e θ z) (a, b) := by
  set w := latPt (modPt φ e θ z) (a, b)
  set c : I → ℂ := fun i => (1 + z i) / (2 * (Real.pi : ℂ) * Complex.I)
  have hc : homFac z = ∏ i, c i := rfl
  have hw : ∏ τ, w τ = ∏ i, w (e i) := (Equiv.prod_comp e w).symm
  unfold defTerm eisTerm logFac
  simp only [defCoord_eq φ e he θ hz a b]
  rw [Finset.prod_mul_distrib]
  have h1 : ∏ i, (c i * w (e i))⁻¹ ^ 2 = (homFac z)⁻¹ ^ 2 * (∏ τ, w τ)⁻¹ ^ 2 := by
    rw [hc, hw, ← Finset.prod_inv_distrib, ← Finset.prod_inv_distrib, ← Finset.prod_pow, ← Finset.prod_pow,
      ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [mul_inv, mul_pow]
  have h2 : ∏ i, ((‖c i * w (e i)‖ : ℝ) : ℂ) ^ (-2 * σ) =
      ((‖homFac z‖ : ℝ) : ℂ) ^ (-2 * σ) * ((‖∏ τ, w τ‖ : ℝ) : ℂ) ^ (-2 * σ) := by
    rw [prodCpow _ _ (fun i => norm_nonneg _), hc, hw, norm_prod, norm_prod,
      ← Complex.mul_cpow_ofReal_nonneg (Finset.prod_nonneg fun i _ => norm_nonneg _)
        (Finset.prod_nonneg fun i _ => norm_nonneg _), ← Complex.ofReal_mul, ← Finset.prod_mul_distrib]
    simp only [norm_mul]
  rw [h1, h2, norm_cpow_eq_exp (homFac_ne_zero hz)]
  ring

end GlobalTheory.WeightTwoCompare

namespace GlobalTheory.WeightTwoCompare

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem eq_of_add_mul {θ : E} (hθ : θ ∉ maximalRealSubfield E) {a b a' b' : maximalRealSubfield E}
    (h : (a : E) + (b : E) * θ = (a' : E) + (b' : E) * θ) : a = a' ∧ b = b' := by
  by_cases hb : b = b'
  · subst hb
    refine ⟨Subtype.ext ?_, rfl⟩
    simpa using h
  · exfalso
    apply hθ
    have hb' : ((b : E) - (b' : E)) ≠ 0 := by
      intro h0; apply hb; exact Subtype.ext (sub_eq_zero.1 h0)
    have : θ = ((a' : E) - (a : E)) / ((b : E) - (b' : E)) := by
      field_simp
      linear_combination h
    rw [this]
    exact div_mem (sub_mem a'.2 a.2) (sub_mem b.2 b'.2)

end GlobalTheory.WeightTwoCompare

namespace GlobalTheory.WeightTwoCompare

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem algebraMap_unit (u : (OF E)ˣ) :
    algebraMap (OF E) E (u : OF E) = (((u : 𝓞 (maximalRealSubfield E)) : maximalRealSubfield E) : E) := rfl

noncomputable def classMap (𝔞 𝔟 : Frac (maximalRealSubfield E)) (θ : E) (L : Set E) (hθ : θ ∉ maximalRealSubfield E)
    (hL : ∀ x : E, x ∈ L ↔ ∃ a ∈ latM 𝔞, ∃ b ∈ (𝔟 : FractionalIdeal (𝓞 (maximalRealSubfield E))⁰ (maximalRealSubfield E)),
      x = (a : E) + (b : E) * θ)
    (c : Quotient (latRel 𝔞 𝔟)) : modUnits L :=
  ⟨Quotient.mk _ ((c.out.1.1 : E) + (c.out.1.2 : E) * θ),
    (c.out.1.1 : E) + (c.out.1.2 : E) * θ, (hL _).2 ⟨_, c.out.2.1, _, c.out.2.2.1, rfl⟩, fun h0 => c.out.2.2.2 (by
      have h := eq_of_add_mul hθ (a := c.out.1.1) (b := c.out.1.2) (a' := 0) (b' := 0) (by simpa using h0)
      exact Prod.ext h.1 h.2), rfl⟩

end GlobalTheory.WeightTwoCompare

namespace GlobalTheory.WeightTwoCompare

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem classMap_bijective (𝔞 𝔟 : Frac (maximalRealSubfield E)) (θ : E) (L : Set E) (hθ : θ ∉ maximalRealSubfield E)
    (hL : ∀ x : E, x ∈ L ↔ ∃ a ∈ latM 𝔞, ∃ b ∈ (𝔟 : FractionalIdeal (𝓞 (maximalRealSubfield E))⁰ (maximalRealSubfield E)),
      x = (a : E) + (b : E) * θ) :
    Function.Bijective (classMap 𝔞 𝔟 θ L hθ hL) := by
  constructor
  · intro c c' h
    have h1 := Quotient.exact (congrArg Subtype.val h)
    obtain ⟨u, hu⟩ := h1
    rw [algebraMap_unit, mul_add, ← mul_assoc, ← Subfield.coe_mul, ← Subfield.coe_mul] at hu
    obtain ⟨ha, hb⟩ := eq_of_add_mul hθ hu
    rw [← Quotient.out_eq c, ← Quotient.out_eq c']
    exact Quotient.sound ⟨u, ha, hb⟩
  · rintro ⟨q, x, hxL, hx0, rfl⟩
    obtain ⟨a, ha, b, hb, rfl⟩ := (hL x).1 hxL
    have hp : ((a, b) : maximalRealSubfield E × maximalRealSubfield E) ≠ 0 := by
      intro h0
      apply hx0
      have h1 : a = 0 := congrArg Prod.fst h0
      have h2 : b = 0 := congrArg Prod.snd h0
      simp [h1, h2]
    let p : LatPair 𝔞 𝔟 := ⟨(a, b), ha, hb, hp⟩
    refine ⟨Quotient.mk _ p, Subtype.ext ?_⟩
    obtain ⟨ε, h1, h2⟩ : (latRel 𝔞 𝔟).r (Quotient.mk (latRel 𝔞 𝔟) p).out p := Quotient.exact (Quotient.out_eq _)
    show Quotient.mk _ _ = Quotient.mk _ _
    refine Quotient.sound ⟨ε, ?_⟩
    rw [algebraMap_unit]
    have e1 : a = p.1.1 := rfl
    have e2 : b = p.1.2 := rfl
    rw [e1, e2, h1, h2, Subfield.coe_mul, Subfield.coe_mul]
    ring

end GlobalTheory.WeightTwoCompare

namespace GlobalTheory.WeightTwoCompare

theorem hasSum_defTerm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] (φ : I → E →+* ℂ)
    (e : I ≃ Emb (maximalRealSubfield E)), (∀ (i : I) (a : maximalRealSubfield E), φ i (a : E) = ((e i a : ℝ) : ℂ)) →
    ∀ (𝔞 𝔟 : Frac (maximalRealSubfield E)) (θ : E) (L : Set E), θ ∉ maximalRealSubfield E →
    (∀ x : E, x ∈ L ↔ ∃ a ∈ latM 𝔞, ∃ b ∈ (𝔟 : FractionalIdeal (𝓞 (maximalRealSubfield E))⁰ (maximalRealSubfield E)),
      x = (a : E) + (b : E) * θ) →
    ∀ z ∈ polydisc I, ∀ (σ S : ℂ), HasSum (eisClass 𝔞 𝔟 2 σ (modPt φ e θ z)) S →
      HasSum (fun q : modUnits L => defTerm φ 2 z σ q.1.out) ((homFac z)⁻¹ ^ 2 * Complex.exp (-σ * logFac z) * S) := by
  intro E _ _ _ I _ φ e he 𝔞 𝔟 θ L hθ hL z hz σ S hS
  let g := Equiv.ofBijective _ (classMap_bijective 𝔞 𝔟 θ L hθ hL)
  rw [← g.hasSum_iff]
  have key1 : ∀ c, defTerm φ 2 z σ (g c).1.out =
      (homFac z)⁻¹ ^ 2 * Complex.exp (-σ * logFac z) * eisClass 𝔞 𝔟 2 σ (modPt φ e θ z) c := by
    intro c
    set x : E := (c.out.1.1 : E) + (c.out.1.2 : E) * θ with hx
    have hg : (g c).1 = Quotient.mk _ x := rfl
    obtain ⟨u, hu⟩ : unitRel.r x (g c).1.out := Quotient.exact (by rw [hg, Quotient.out_eq])
    rw [hu, hx, algebraMap_unit, mul_add, ← mul_assoc, ← Subfield.coe_mul, ← Subfield.coe_mul,
      defTerm_eq φ e he θ hz, eisTerm_unit (by decide)]
    rfl
  have key : (fun q : modUnits L => defTerm φ 2 z σ q.1.out) ∘ g =
      fun c => (homFac z)⁻¹ ^ 2 * Complex.exp (-σ * logFac z) * eisClass 𝔞 𝔟 2 σ (modPt φ e θ z) c := by
    funext c
    simp only [Function.comp_apply]
    exact key1 c
  rw [key]
  exact hS.mul_left _

end GlobalTheory.WeightTwoCompare
end

section

noncomputable section

namespace GlobalTheory.UPel.HT.HeckeAd

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke

variable {S : Scheme.{0}} {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R}

def IsTranslA (f : D.La →+ D.La) (c k N : ℕ) {s : S ⟶ Sp R} (o : Obj b (N * k) s) (o' : Obj b N s)
    (ψ : o.A ⟶ o'.A) : Prop :=
  IsMonHom ψ ∧ (∀ a : D.O, o.act.act a ≫ ψ = ψ ≫ o'.act.act a) ∧ (∀ x, o'.eta x = o.eta (f x) ≫ ψ) ∧
    GlobalTheory.ZM.IsGaloisCover (heckeSubA o f N) (fun h => (transl h.1).left) ψ.left ∧
    Nonempty (LBIso (Hecke.lbPow o.P (k ^ 2 / c)) (o'.P.pull (sq2 ψ))) ∧ c ∣ k ^ 2

end GlobalTheory.UPel.HT.HeckeAd
end
end

section

open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.baseChangeSectionsComparisonHom_bijective : ∀ (R₀ R₁ : Type) [CommRing R₀] [CommRing R₁] [Algebra R₀ R₁] (X₀ X₁ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀) (s₁ : X₁ ⟶ Sp R₁) (pr : X₁ ⟶ X₀) (hp : IsPullback pr s₁ s₀ (spMap (algebraMap R₀ R₁))) (U : X₀.affineOpens), Function.Bijective (GlobalTheory.Obs.BaseChg.beta hp U) := by
  first | exact @GlobalTheory.Obs.BaseChg.beta_bijective | exact GlobalTheory.Obs.BaseChg.beta_bijective | (intros; apply GlobalTheory.Obs.BaseChg.beta_bijective <;> assumption)
end

section

open Classical GlobalTheory.FinWeil
open scoped BigOperators

theorem _root_.GlobalTheory.T.invariantForm_normalizedHeisenbergIntertwiner : ∀ {R X M : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M] {σ : R →+* R} {w : R} {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M}, IsHeis σ w γ W → (∀ x y, ‖γ x y‖ = 1) → ∀ lam : ℕ →* ℂ, GoodNorm σ lam → ∀ A : Submodule R X, SelfDual γ A → Submodule.span ℂ {m : M | ∃ x e, Fixes W A e ∧ m = W x e} = ⊤ → ∀ (φ : X →ₗ[R] X), (∀ x y, γ (φ x) (φ y) = γ x y) → SelfDual γ (A.map φ) → idx A (A.map φ) ≠ 0 → ∀ T : M →ₗ[ℂ] M, (∀ x v, T (W x v) = W (φ x) (T v)) → (∀ e, Fixes W A e → T e = normOp lam W A (A.map φ) e) → ∀ B : M →ₗ[ℂ] M →ₗ⋆[ℂ] ℂ, (∀ x u v, B (W x u) (W x v) = B u v) → ∀ u v, B (T u) (T v) = B u v := by
  first | exact @GlobalTheory.FinWeil.invForm_intertwiner | exact GlobalTheory.FinWeil.invForm_intertwiner | (intros; apply GlobalTheory.FinWeil.invForm_intertwiner <;> assumption)
end
