module

public import Development.AbelianVarietyTheory.Definitions.CMLattices.Bundle001
public import Development.AbelianVarietyTheory.Definitions.CMLattices.IsDiffOf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsGenTranslEqPairing
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsUniqueDescendOfTorsionInvariant
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle017
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle093
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle112
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle097
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LbIsoCubeLBOfWeilIsAdjoint
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle159
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IntegralFrameChangeIntegralInvertibleMatrix
public import Development.AbelianVarietyTheory.Definitions.CMLattices.IntegralOf
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle017
public import Development.AbelianVarietyTheory.Statements.PrincipalLattices.Bundle001
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle063
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle049
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle029
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle040
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle031
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Development.AbelianVarietyTheory.Definitions.CMLattices.LamLetters
import Formalism.LocalToGlobal.CMDeterminantIdeals.DetIdeal
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM


theorem _root_.GlobalTheory.T.nonempty_tensor_of_onto_full_family : Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (σ : R →+* ℂ) (ω : R) (C : Ell H R ω) (D : Datum H) (ε : ℤˣ) (h : D.La → D.La → OK H) (T : PAT H (Sp R)) (ψ : (⊤ : Submodule (𝓞 E) D.La) → (C.P.A ⟶ T.t.G)), Function.Injective σ → IsKForm D ε h → (∀ x : D.La, x ≠ 0 → 0 < (ε : ℤ) * D.EF (H.w0 • x) x) → IsFam C T h ⊤ ψ → OntoAt ψ (spMap σ) → Nonempty (IsTen C D h T) := by
  first | exact @GlobalTheory.CM.nonempty_isTen_of_isFam_top | exact GlobalTheory.CM.nonempty_isTen_of_isFam_top | (intros; apply GlobalTheory.CM.nonempty_isTen_of_isFam_top <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM


theorem _root_.GlobalTheory.T.degree_lie_lattice_hermitian_invariant : ThetaUnifAV → Out.Laws → ∀ (K : Type) [Field K] [NumberField K] (P : Out.PolAV (Sp (𝓞 K))) (F : GenFib P) (F' : GenFib P) (h : HermFam K (Fin F.P₀.g → K)) (h' : HermFam K (Fin F'.P₀.g → K)), F.IsHerm h → F'.IsHerm h' → deg h F.lieLat = deg h' F'.lieLat ∧ ∀ (O : Type) [CommRing O] (act : OAct O P.A) (τ : O →+* 𝓞 K), deg h (F.eigLat act τ) = deg h' (F'.eigLat act τ) := by
  first | exact @GlobalTheory.FibIndep.deg_lieLat_eq | exact GlobalTheory.FibIndep.deg_lieLat_eq | (intros; apply GlobalTheory.FibIndep.deg_lieLat_eq <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF


theorem _root_.GlobalTheory.T.hermitianLength_image_eigenBasisVector_le : ThetaUnifAV → Out.Laws → ∀ (K : Type) [Field K] [NumberField K] (P P' : Out.PolAV (Sp (𝓞 K))) (F : GenFib P) (F' : GenFib P') (h : HermFam K (Fin F.P₀.g → K)) (h' : HermFam K (Fin F'.P₀.g → K)) (f : P.A ⟶ P'.A) (g : P.A ⟶ P.A), F.IsHerm h → F'.IsHerm h' → IsMonHom f → IsMonHom g → LamEq P'.L f f P.L g (𝟙 P.A) → ∀ (i : Fin F.P₀.g) (t : K) (w : epsR K ⟶ F.P₀.A) (U : Fin F'.P₀.g → K) (w' : epsR K ⟶ F'.P₀.A), IsLieComb (Pi.single i t) F.v w → (F.v i).left ≫ F.φ ≫ g.left = w.left ≫ F.φ → IsLieComb U F'.v w' → w'.left ≫ F'.φ = (F.v i).left ≫ F.φ ≫ f.left → ∀ s : K →+* ℂ, (h'.form s U U).re ≤ ‖s t‖ * (h.form s (Pi.single i 1) (Pi.single i 1)).re := by
  first | exact @GlobalTheory.LamF.LenOne.form_image_le | exact GlobalTheory.LamF.LenOne.form_image_le | (intros; apply GlobalTheory.LamF.LenOne.form_image_le <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

noncomputable section

namespace GlobalTheory.CM.LamOfWeil

open ReciprocityTheory.ChartRestriction.G.Out CommutatorPairing DescentPairing IsoDescent

section

variable {S : Scheme.{0}} {A T T' : Over S} [GrpObj A] [IsCommMonObj A]

abbrev sqφ (a b : T ⟶ A) : ULift.{0} (Finset (Fin 2)) → (T.left ⟶ A.left) := fun I => (psum A ![a, b] I.down).left

abbrev sqε : ULift.{0} (Finset (Fin 2)) → ℤ := fun I => (-1) ^ (2 - I.down.card)

theorem prod_sq (ρ : T' ⟶ T) (a b : T ⟶ A) {U : Type} [CommGroup U] (h : (T'.left ⟶ A.left) → U) :
    ∏ I, h (ρ.left ≫ sqφ a b I) ^ sqε I =
      h ((ρ ≫ a) * (ρ ≫ b)).left * (h (ρ ≫ a).left)⁻¹ * (h (ρ ≫ b).left)⁻¹ * h (1 : T' ⟶ A).left := by
  have p := NormRos.prod_square a b (fun q => h (ρ.left ≫ q))
  simp only [← Over.comp_left, MonObj.comp_mul, MonObj.comp_one] at p
  exact p

theorem exists_gen_axis {L : LB A.left} (hL : L.IsLB) (ρ : T' ⟶ T) (a b : T ⟶ A) (H : ρ ≫ a = 1 ∨ ρ ≫ b = 1) :
    ∃ t : LB.Gen (LB.LinComb L (fun I => ρ.left ≫ sqφ a b I) sqε), t.IsGen :=
  AdjointOfPairing.exists_gen_of_formEq_zero hL fun U _ h => by
    rw [prod_sq]
    rcases H with H | H
    · rw [H, _root_.one_mul]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_one]
      abel
    · rw [H, _root_.mul_one]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_one]
      abel

end

theorem exists_gen_div {X X' Y Y' : Scheme.{0}} {K K' : Type} [Fintype K] [Fintype K'] (L : LB X) (L' : LB X')
    (φ : K → (Y ⟶ X)) (ε : K → ℤ) (φ' : K' → (Y ⟶ X')) (ε' : K' → ℤ) (f : Y' ⟶ Y)
    (H : LBIso (LB.LinComb L (fun k => f ≫ φ k) ε) (LB.LinComb L' (fun k => f ≫ φ' k) ε')) :
    ∃ t : LB.Gen ((LB.div (LB.LinComb L' φ' ε') (LB.LinComb L φ ε)).pull f), t.IsGen := by
  obtain ⟨w, hw⟩ := H.chartPull (chartPullOut L φ ε f _ fun _ => rfl) (chartPullOut L' φ' ε' f _ fun _ => rfl)
  exact gen_chartPull (IsoDescent.chartPullDiv _ _ f) w hw

variable {k : Type} [Field k] {X Y : Over (Sp k)} [GrpObj X] [GrpObj Y]

theorem exists_gen_fibre (hG : GlobalFnsSt) (hC : CubeSt) (P : PolAV (Sp k)) (f₁ : X ⟶ P.A) (f₂ : Y ⟶ P.A)
    [IsMonHom f₁] [IsMonHom f₂] (n : ℕ) (x : 𝟙_ (Over (Sp k)) ⟶ X) (hx : x ^ n = 1) :
    ∃ u : LB.Gen (LB.LinComb P.L (fun I => (mulA Y n).left ≫ (lift (toUnit Y ≫ x) (𝟙 Y)).left ≫
        sqφ (fst X Y ≫ f₁) (snd X Y ≫ f₂) I) sqε),
      u.IsGen ∧ ∀ (y : 𝟙_ (Over (Sp k)) ⟶ Y) (c : Γ((𝟙_ (Over (Sp k))).left, ⊤)ˣ), y ^ n = 1 →
        WeilIs P.A P.L n (x ≫ f₁) (y ≫ f₂) c → ∀ (z : Y.left) (J), Good P.L z J →
          val u ((toUnit Y ≫ y) * 𝟙 Y).left z J = val u (𝟙 _) z J * gm (toUnit Y).left z ⊤ c := by
  have := P.isAb.comm
  obtain ⟨rig, hrig⟩ := P.rigid
  let L : RigLB P.A := ⟨P.L, rig, P.isLB, hrig⟩
  obtain ⟨⟨cb⟩, -⟩ := hC _ P L rfl
  let T := 𝟙_ (Over (Sp k))
  let p₀ : T.left := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum k)
  have hT : ∀ p : T.left, p = p₀ := fun p => Subsingleton.elim (α := PrimeSpectrum k) p p₀
  have hx₁ : (x ≫ f₁) ^ n = 1 := by rw [← MonObj.pow_comp, hx, MonObj.one_comp]
  obtain ⟨u₀, hu₀, v₀⟩ := PairingDetermines.exists_gen_transl hG P.isAb cb p₀ hT n (x ≫ f₁) hx₁
  obtain ⟨σ, hσ⟩ := exists_frame P.isLB (K := Fin 2) ![(x ≫ f₁).left, (1 : T ⟶ P.A).left] ![-1, 1] p₀ hT
  obtain ⟨u, hu, v⟩ := exists_gen P.isLB
    (φ' := fun I => (mulA Y n).left ≫ (lift (toUnit Y ≫ x) (𝟙 Y)).left ≫
      sqφ (fst X Y ≫ f₁) (snd X Y ≫ f₂) I) (ε' := sqε)
    (fun U _ h => by
      have e₀ : mulA Y n ≫ lift (toUnit Y ≫ x) (𝟙 Y) = lift (toUnit Y ≫ x) (𝟙 Y ^ n) := by
        rw [comp_lift, comp_toUnit_assoc, Category.comp_id]
      have e₁ : lift (toUnit Y) f₂ ≫ mulT P.A T n ≫ translPt P.A (x ≫ f₁) =
          (toUnit Y ≫ x ≫ f₁) * ((𝟙 Y ^ n) ≫ f₂) := by
        rw [← Category.assoc, mulT, comp_lift, lift_translPt, lift_fst, MonObj.comp_pow, lift_snd,
          MonObj.pow_comp, Category.id_comp]
      have e₂ : lift (toUnit Y) f₂ ≫ snd T P.A ^ n = (𝟙 Y ^ n) ≫ f₂ := by
        rw [MonObj.comp_pow, lift_snd, MonObj.pow_comp, Category.id_comp]
      have e₃ : toUnit Y ≫ (1 : T ⟶ P.A) = 1 := MonObj.comp_one _
      have e := prod_sq (lift (toUnit Y ≫ x) (𝟙 Y ^ n)) (fst X Y ≫ f₁) (snd X Y ≫ f₂) h
      rw [lift_fst_assoc, lift_snd_assoc, Category.assoc] at e
      refine Eq.trans ?_ (e.symm.trans (Finset.prod_congr rfl fun I _ => by
        rw [← e₀, Over.comp_left, Category.assoc]))
      refine (Fintype.prod_sum_type _).trans ?_
      simp only [Sum.elim_inl, Sum.elim_inr, Fin.prod_univ_succ, Fin.prod_univ_zero, Matrix.cons_val_zero,
        Matrix.cons_val_succ, ← Over.comp_left, e₁, e₂, e₃, Category.assoc, zpow_neg, zpow_one, _root_.mul_one]
      ac_rfl)
    (LB.mulGen P.L _ _ _ _ (LB.pullGen P.L _ _ u₀ (lift (toUnit Y) f₂).left) (LB.pullGen P.L _ _ σ (toUnit Y).left))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ _ hu₀ _) (DVR.pullGen_isGen _ _ _ _ hσ _))
  refine ⟨u, hu, fun y c hy hc z J hJ => ?_⟩
  have hy₂ : (y ≫ f₂) ^ n = 1 := by rw [← MonObj.pow_comp, hy, MonObj.one_comp]
  have w : ∀ a : Y ⟶ Y, val u a.left z J =
      val u₀ (lift (toUnit Y) (a ≫ f₂)).left z J * val σ (toUnit Y).left z J := fun a => by
    rw [v _ _ z J hJ, val_mul hJ, val_pull hJ, val_pull hJ, ← Over.comp_left, ← Over.comp_left, comp_lift,
      comp_toUnit]
  have w₀ := v₀ (y ≫ f₂) c hy₂ hc Y (toUnit Y) (𝟙 Y ≫ f₂) z J hJ
  refine (w _).trans (Eq.trans ?_ (congrArg (· * _) (w (𝟙 Y))).symm)
  rw [MonObj.mul_comp, Category.assoc, mul_right_comm]
  exact congrArg (fun q => q * _) w₀

end GlobalTheory.CM.LamOfWeil

namespace GlobalTheory.CM

open LamOfWeil IsoDescent

theorem lamEq_of_weilEq : Out.Laws → ∀ (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (X Y A B : Out.PolAV (Sp k)) (f₁ : X.A ⟶ A.A) (f₂ : Y.A ⟶ A.A) (g₁ : X.A ⟶ B.A) (g₂ : Y.A ⟶ B.A), IsMonHom f₁ → IsMonHom f₂ → IsMonHom g₁ → IsMonHom g₂ → WeilEq A.L f₁ f₂ B.L g₁ g₂ (𝟙 (Sp k)) → LamEq A.L f₁ f₂ B.L g₁ g₂ := by
  intro hL k _ _ _ X Y A B f₁ f₂ g₁ g₂ hf₁ hf₂ hg₁ hg₂ hW
  haveI : IsCommMonObj A.A := A.isAb.comm
  haveI : IsCommMonObj B.A := B.isAb.comm
  haveI : IsCommMonObj Y.A := Y.isAb.comm
  have axis : ∀ {Z : Over (Sp k)} (ρ : Z ⟶ X.A ⊗ Y.A), ρ ≫ fst _ _ = 1 ∨ ρ ≫ snd _ _ = 1 →
      ∃ t : LB.Gen ((LB.div (LB.LinComb B.L (sqφ (fst X.A Y.A ≫ g₁) (snd X.A Y.A ≫ g₂)) sqε)
        (LB.LinComb A.L (sqφ (fst X.A Y.A ≫ f₁) (snd X.A Y.A ≫ f₂)) sqε)).pull ρ.left), t.IsGen := by
    intro Z ρ H
    obtain ⟨u, hu⟩ := exists_gen_axis A.isLB ρ (fst X.A Y.A ≫ f₁) (snd X.A Y.A ≫ f₂)
      (H.imp (fun h => by rw [reassoc_of% h, MonObj.one_comp]) (fun h => by rw [reassoc_of% h, MonObj.one_comp]))
    obtain ⟨u', hu'⟩ := exists_gen_axis B.isLB ρ (fst X.A Y.A ≫ g₁) (snd X.A Y.A ≫ g₂)
      (H.imp (fun h => by rw [reassoc_of% h, MonObj.one_comp]) (fun h => by rw [reassoc_of% h, MonObj.one_comp]))
    exact exists_gen_div _ _ _ _ _ _ _ (lbIso_of_gens A.isLB B.isLB _ _ _ _ u hu u' hu')
  refine T.seesaw_triviality_on_dense_fibres_product_abelian hL.globalFns k X.A Y.A
    (LB.div (LB.LinComb B.L (sqφ (fst X.A Y.A ≫ g₁) (snd X.A Y.A ≫ g₂)) sqε)
      (LB.LinComb A.L (sqφ (fst X.A Y.A ≫ f₁) (snd X.A Y.A ≫ f₂)) sqε)) Y.L X.isAb Y.isAb Y.isLB Y.ample
    (LB.isLB_div (DVR.linComb_isLB _ B.isLB _ _) (DVR.linComb_isLB _ A.isLB _ _))
    (axis _ (Or.inl (lift_fst _ _))) ?_ (axis _ (Or.inr (lift_snd _ _)))
  refine (TorsionDense.dense_torsion X hL.irred hL.kerPow).mono (Set.biUnion_subset_biUnion_left ?_)
  rintro x ⟨n, hn, hx⟩
  obtain ⟨u, hu, v⟩ := exists_gen_fibre hL.globalFns hL.cube A f₁ f₂ n x hx
  obtain ⟨u', hu', v'⟩ := exists_gen_fibre hL.globalFns hL.cube B g₁ g₂ n x hx
  refine exists_gen_div _ _ _ _ _ _ _ ?_
  refine lbIso_of_invariant A.isLB B.isLB _ _ _ _ (Out.mulA Y.A n).left
    (I := {y : 𝟙_ (Over (Sp k)) ⟶ Y.A // y ^ n = 1}) (fun y => ((toUnit Y.A ≫ y.1) * 𝟙 Y.A).left) (fun y => ?_)
    (fun U f hf => torsion_invariant_descends (fun S _ P n hn => by
      obtain ⟨a, b, c, e, -⟩ := hL.mulN S P n hn
      exact ⟨a, b, c, e⟩) k Y n (Nat.cast_ne_zero.2 hn.ne') U f fun y hy => hf ⟨y, hy⟩) u hu u' hu'
    (fun y z J J' hJ hJ' => ?_)
  · rw [← Over.comp_left, Out.mulA, MonObj.comp_pow, Category.comp_id, mul_pow, ← MonObj.comp_pow, y.2,
      MonObj.comp_one, _root_.one_mul]
  · have hx₁ : (x ≫ f₁) ^ n = 1 := by rw [← MonObj.pow_comp, hx, MonObj.one_comp]
    have hy₂ : (y.1 ≫ f₂) ^ n = 1 := by rw [← MonObj.pow_comp, y.2, MonObj.one_comp]
    obtain ⟨c, hc, -⟩ := (hL.weil _ A n _).1 (x ≫ f₁) (y.1 ≫ f₂) hx₁ hy₂
    obtain ⟨c, rfl⟩ : ∃ c₀ : kˣ, unitOn c₀ = c :=
      ⟨Units.map (Scheme.ΓSpecIso (CommRingCat.of k)).hom.hom.toMonoidHom c,
        Units.ext ((Scheme.ΓSpecIso (CommRingCat.of k)).hom_inv_id_apply c.val)⟩
    have h₁ := v y.1 (unitOn c) y.2 hc z J hJ
    have h₂ := v' y.1 (unitOn c) y.2 ((hW n x y.1 c hn hx y.2).1 hc) z J' hJ'
    refine (congrArg₂ (fun a b => a * b⁻¹) h₂ h₁).trans ?_
    exact mul_div_mul_right_eq_div _ _ _ |> fun h => by simpa only [div_eq_mul_inv] using h

end GlobalTheory.CM

end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM Formalism.L2.Pj
open scoped ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.Frames GlobalTheory.LamT

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LamT.LocLie

open GlobalTheory.IntRebase
open Formalism.L2.PjFree (spMap_comp' epsMul_comp_alg)

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l}

theorem comb_eq {S : Type} [CommRing S] {x : Sp S ⟶ Xo.X} {m : ℕ}
    {v : Fin m → (Sp (DualNumber S) ⟶ Xo.univ.t.G.left)} (hv : ∀ j, IsTanAt x (v j)) {a : Fin m → S}
    {w : Sp (DualNumber S) ⟶ Xo.univ.t.G.left} (h : IsCombAt x v a w) :
    (combT x (fun j => ovT (t := Xo.univ.t) (hv j)) a).left = w :=
  (isCombAtG_iff Xo.univ.t x (fun j => ovT (t := Xo.univ.t) (hv j)) _ _).1 h

theorem lieInt_change (T : CDVR) (io : c.F →+* T.Fr) {G : SAB H (Sp T.V)} {t' : SAB H (Sp T.Fr)}
    {x : Sp T.Fr ⟶ Xo.X} (m1 : SABMap t' Xo.univ.t x) (m2 : SABMap t' G (spMap (algebraMap T.V T.Fr)))
    (u : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Sp (DualNumber T.Fr) ⟶ Xo.univ.t.G.left))
    (hu : ∀ τ j, IsTanAt x (u τ j)) (h : LieInt T io m1 m2 u)
    (k : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) T.V) (hk : ∀ τ, IsUnit (k τ).det) :
    LieInt T io m1 m2 (fun τ i => (combT x (fun j => ovT (t := Xo.univ.t) (hu τ j))
      (fun j => algebraMap T.V T.Fr (k τ j i))).left) := by
  obtain ⟨ub, htan, heig, hbas, hlift⟩ := h
  let Ub : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (tEpsG (𝟙 (Sp T.V)) ⟶ G.G) := fun τ j => kap ≫ ub τ j
  have hUb0 : ∀ τ j, smT (𝟙 (Sp T.V)) 0 (Ub τ j) = 1 := fun τ j => smT_zero_kap _ (htan τ j)
  have hUbE : ∀ τ j (a : 𝓞 E) (z : T.V), algebraMap T.V T.Fr z = io (embK c τ a) →
      Ub τ j ≫ G.act.act a = smT (𝟙 (Sp T.V)) z (Ub τ j) := fun τ j =>
    (isEigV_kapI_iff io G τ _).1 (by rw [kapI_kap_assoc]; exact heig τ j)
  refine ⟨fun τ i => kapI ≫ combT (𝟙 (Sp T.V)) (Ub τ) (fun j => k τ j i), ?_, ?_, ?_, ?_⟩
  · intro τ i
    exact isTan_kapI _ (combT_tan _ _ (hUb0 τ) _)
  · intro τ i
    refine (isEigV_kapI_iff io G τ _).2 fun a z hz => ?_
    have := G.act.hom a
    exact combT_eig _ _ _ _ (fun j => hUbE τ j a z hz) _
  · intro τ w hw he
    have h1 : ∃! a : Fin (Dw.mult τ) → T.V, kap ≫ w = combT (𝟙 (Sp T.V)) (Ub τ) a := by
      obtain ⟨a, ha, hu⟩ := hbas τ w hw he
      refine ⟨a, (isComb_iff _ _ _).1 (by rw [kapI_kap_assoc]; exact ha), fun b hb => hu b ?_⟩
      have h2 := (isComb_iff (ub τ) b (kap ≫ w)).2 hb
      rw [kapI_kap_assoc] at h2
      exact h2
    obtain ⟨a, ha, hu⟩ := reframe_basis _ (Ub τ) (hUb0 τ) (k τ) (hk τ) _ h1
    have e : (fun i => kap ≫ (kapI ≫ combT (𝟙 (Sp T.V)) (Ub τ) (fun j => k τ j i))) =
        fun i => combT (𝟙 (Sp T.V)) (Ub τ) (fun j => k τ j i) := funext fun i => kap_kapI_assoc _
    refine ⟨a, ?_, fun b hb => hu b ?_⟩
    · have h2 := (isComb_iff (fun i => kapI ≫ combT (𝟙 (Sp T.V)) (Ub τ) (fun j => k τ j i)) a (kap ≫ w)).2
        (by rw [e]; exact ha)
      rw [kapI_kap_assoc] at h2
      exact h2
    · have h2 := (isComb_iff (fun i => kapI ≫ combT (𝟙 (Sp T.V)) (Ub τ) (fun j => k τ j i)) b (kap ≫ w)).1
        (by rw [kapI_kap_assoc]; exact hb)
      rw [e] at h2
      exact h2
  · intro τ i
    choose u' hu1 hu2 using hlift τ
    have hδ : spMap (Formalism.L2.Pj.dualMap (algebraMap T.V T.Fr)) ≫
        spMap ((algebraMap T.V (DualNumber T.V)).comp (algebraMap T.V T.V)) =
        spMap (algebraMap T.Fr (DualNumber T.Fr)) ≫ spMap (algebraMap T.V T.Fr) := by
      rw [spMap_comp', spMap_comp']
      show spMap ((Formalism.L2.Pj.dualMap (algebraMap T.V T.Fr)).comp (algebraMap T.V (DualNumber T.V))) = _
      rw [dualMap_comp_alg]
    have hov : ∀ j, u' j ≫ t'.G.hom = spMap (algebraMap T.Fr (DualNumber T.Fr)) := by
      intro j
      apply spMap_frac_cancel (V := T.V)
      rw [Category.assoc, ← m2.cart.1.w, ← Category.assoc, hu2 j, Category.assoc, Over.w (ub τ j)]
      exact hδ
    let T' : Over (Sp T.Fr) := Over.mk (spMap (algebraMap T.Fr (DualNumber T.Fr)))
    let cf : Fin (Dw.mult τ) → T.Fr := fun j => algebraMap T.V T.Fr (k τ j i)
    let Y : Fin (Dw.mult τ) → (T' ⟶ t'.G) := fun j => Over.homMk (spMap (epsMul (cf j)) ≫ u' j) (by
      show (spMap (epsMul (cf j)) ≫ u' j) ≫ t'.G.hom = spMap (algebraMap T.Fr (DualNumber T.Fr))
      rw [Category.assoc, hov, spMap_comp', epsMul_comp_alg])
    refine ⟨(∏ j, Y j).left, ?_, ?_⟩
    · have hA := grpPull_prod m1.cart T' Finset.univ Y
        (fun j => smT x (cf j) (ovT (t := Xo.univ.t) (hu τ j))) (fun j => by
          show spMap (epsMul (cf j)) ≫ u τ j = (spMap (epsMul (cf j)) ≫ u' j) ≫ m1.φ
          rw [Category.assoc, hu1])
      exact hA.symm
    · let δ : Over.mk (T'.hom ≫ spMap (algebraMap T.V T.Fr)) ⟶ epsOver T.V T.V :=
        Over.homMk (spMap (Formalism.L2.Pj.dualMap (algebraMap T.V T.Fr))) hδ
      have hB := grpPull_prod m2.cart T' Finset.univ Y
        (fun j => δ ≫ kapI ≫ smT (𝟙 (Sp T.V)) (k τ j i) (Ub τ j)) (fun j => by
          simp only [Over.comp_left, δ, kapI, IntRebase.kap, Ub, smT_left, Over.homMk_left, Category.id_comp, Y,
            Category.assoc]
          rw [hu2 j, ← Category.assoc, ← Category.assoc, spMap_comp', spMap_comp', dualMap_comp_epsMul])
      rw [← hB, ← comp_prodT, ← comp_prodT]
      rfl

end GlobalTheory.LamT.LocLie


open GlobalTheory.LamT.LocLie in
theorem GlobalTheory.LamT.lieInt_exists_and_change : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (T : CDVR) (io : c.F →+* T.Fr) (G : SAB H (Sp T.V)) (t' : SAB H (Sp T.Fr)) (x : Sp T.Fr ⟶ Xo.X) (m1 : SABMap t' Xo.univ.t x) (m2 : SABMap t' G (spMap (algebraMap T.V T.Fr))), letI := io.toAlgebra; ∀ y : FrPt Xo c T.Fr, y.x = x → (∃ g : (∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) T.Fr), (∀ b, IsUnit (g b).det) ∧ ∀ (a : T.Fr) (y' : FrPt Xo c T.Fr), FrChg g a y y' → LieInt T io m1 m2 y'.u) ∧ (LieInt T io m1 m2 y.u → ∀ (X : (∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) T.V)) (a : T.Fr) (y' : FrPt Xo c T.Fr), (∀ b, IsUnit (X b).det) → FrChg (fun b => (X b).map (algebraMap T.V T.Fr)) a y y' → LieInt T io m1 m2 y'.u) := by
  intro E _ _ _ H Dw l Xo c T io G t' x m1 m2
  let _ := io.toAlgebra
  intro y hy
  subst hy
  refine ⟨?_, fun h X a y' hX hch => ?_⟩
  · obtain ⟨ub, u, hint, ht, he, hb, hcf⟩ := lieFree Xo c T io G t' y.x m1 m2 y.x_over y.u y.tan y.eig y.basis
    choose cf hd hz hc using hcf
    refine ⟨fun b => Matrix.of (cf b), fun b => ?_, fun a y' hch => ?_⟩
    · show IsUnit (Matrix.of (cf b)).det
      rw [Matrix.det_of_isLowerTriangular (Matrix.of (cf b)) (fun i j hij => hz b i j hij)]
      exact IsUnit.prod_univ_iff.2 (hd b)
    · have e : y'.u = u := funext fun τ => funext fun i =>
        (comb_eq (y.tan τ) (hch.2.1 τ i)).symm.trans (comb_eq (y.tan τ) (hc τ i))
      rw [e]
      exact ⟨ub, hint⟩
  · have h2 := lieInt_change T io m1 m2 y.u y.tan h (fun τ => (X τ).transpose)
      (fun τ => by rw [Matrix.det_transpose]; exact hX τ)
    have e : y'.u = _ := funext fun τ => funext fun i => (comb_eq (y.tan τ) (hch.2.1 τ i)).symm
    rw [e]
    exact h2
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF

namespace GlobalTheory.LamF

theorem two_mul_deg_eigLat_of_polAV : DegSt → ThetaUnifAV → Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [NeZero H.d] (χ : DirichletCharacter ℂ H.d), IsKroneckerChar χ → ∀ (K : Type) [Field K] [NumberField K] (ρ : 𝓞 K) (P : Out.PolAV (Sp (𝓞 K))) (act : OAct (𝓞 E) P.A), (∀ a, LamEq P.L (act.act a) (𝟙 P.A) P.L (𝟙 P.A) (act.act (H.bar a))) → Splits E K → ρ ^ 2 = -(H.d : 𝓞 K) → HasType H act ρ 1 0 → ∀ (F : GenFib P) (h : HermFam K (Fin F.P₀.g → K)), F.IsHerm h → ∀ τ : 𝓞 E →+* 𝓞 K, τ H.rt = ρ → ((2 * deg h (F.eigLat act τ) : ℝ) : ℂ) = logOm E χ := by
  intro hD hT hL E _ _ _ H _ χ hχ K _ _ ρ P act hbal hs hρ ht F h hh τ hτ
  obtain ⟨T, e, -, hlin, hlam⟩ := exists_pat_of_polAV hL E H (𝓞 K) P act hbal
  obtain ⟨F₁⟩ := GenFib.nonempty_of_baseChange hL.polBaseChange K T.pol
  obtain ⟨h₁, hh₁⟩ := (LieMetric.exists_unique_isHerm hT hL K T.pol F₁).1
  have ht₁ : HasType H T.t.act ρ 1 0 := hasType_of_iso E H (𝓞 K) _ _ _ _ e ρ 1 0 hlin ht
  rw [← deg_eigLat_eq_of_iso hT hL K T.pol P F₁ F h₁ h (𝓞 E) T.t.act act e hh₁ hh hlin hlam τ]
  exact hD E H χ hχ K ρ T hs hρ ht₁ F₁ h₁ hh₁ τ hτ

end GlobalTheory.LamF
end

end

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF


theorem _root_.GlobalTheory.T.two_mul_deg_eigenLattice_polarizedAbelianScheme : DegSt → ThetaUnifAV → Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [NeZero H.d] (χ : DirichletCharacter ℂ H.d), IsKroneckerChar χ → ∀ (K : Type) [Field K] [NumberField K] (ρ : 𝓞 K) (P : Out.PolAV (Sp (𝓞 K))) (act : OAct (𝓞 E) P.A), (∀ a, LamEq P.L (act.act a) (𝟙 P.A) P.L (𝟙 P.A) (act.act (H.bar a))) → Splits E K → ρ ^ 2 = -(H.d : 𝓞 K) → HasType H act ρ 1 0 → ∀ (F : GenFib P) (h : HermFam K (Fin F.P₀.g → K)), F.IsHerm h → ∀ τ : 𝓞 E →+* 𝓞 K, τ H.rt = ρ → ((2 * deg h (F.eigLat act τ) : ℝ) : ℂ) = logOm E χ := by
  first | exact @GlobalTheory.LamF.two_mul_deg_eigLat_of_polAV | exact GlobalTheory.LamF.two_mul_deg_eigLat_of_polAV | (intros; apply GlobalTheory.LamF.two_mul_deg_eigLat_of_polAV <;> assumption)

end
end
