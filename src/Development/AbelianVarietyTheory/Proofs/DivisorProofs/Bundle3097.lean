module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle071
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle024
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle023
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2935
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3039
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle147
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSiegPreOfPolAV
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaObjectEighthPowerPrincipalSiegel
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle152
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle028
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3020
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3024
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3000
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2999
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3025
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3023
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2901
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle189
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle023
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3063
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibreIsoCarriesSharpPointsToConjugates
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorDataPsiMemMaximalIdealTendstoZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorDegenerationDataPsiEven
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle074
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2932
import Mathlib.Tactic.Polynomial.Basic
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle068

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.TensPow

open GlobalTheory.CechPic GlobalTheory.SiegelOfPolarised GlobalTheory.PrimNorm GlobalTheory.PrimNormPol GlobalTheory.SiegelPower GlobalTheory.MumFam GlobalTheory.MumFam.TensPol

theorem exists_pow_data_polAV : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] (Q : Data R) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ), ((W + W.transpose).map (Int.cast : ℤ → ℝ)).PosDef → IsUnit (W + W.transpose).det → ∃ (P' : PolAV (Sp R)) (pr : Fin r → (P'.A ⟶ Q.B)), (∀ i, IsMonHom (pr i)) ∧ Nonempty (IsLimit (Fan.mk P'.A pr)) ∧ LBIso P'.L (LB.LinComb Q.M.L (tensφ pr) (tensε W)) := by
  intro R _ _ _ _ Q r W hpd hdet
  obtain ⟨L₁, -⟩ := abelianSchemeLaws_all
  have hG := L₁.globalFns
  let c := siegLamData hG Q
  have hP : c.P.IsLB := c.isLB
  have hD : c.diag.IsLB := pull_isLB hP _
  have hamp : RelAmple c.A c.diag := relAmple_diag Q hD
  let G := Out.powObj Q.B r
  let pr : Fin r → (G ⟶ Q.B) := Out.powPr Q.B
  have hpr : ∀ u, IsMonHom (pr u) := fun u => inferInstance
  have hu : ∀ (T : Over (Sp R)) (y : Fin r → (T ⟶ Q.B)), ∃! x : T ⟶ G, ∀ u, x ≫ pr u = y u := fun T y =>
    ⟨(Out.powIsLimit Q.B r).lift (Fan.mk T y), fun u => (Out.powIsLimit Q.B r).fac (Fan.mk T y) ⟨u⟩,
      fun x hx => (Out.powIsLimit Q.B r).uniq (Fan.mk T y) x fun u => hx u.as⟩
  have hB : ∀ (T : Over (Sp R)) (x x' y : T ⟶ c.A), bi hP (x * x') y = bi hP x y + bi hP x' y := fun T x x' y => by
    have e := (cls_eq_zero_iff (LB.isLB_linComb hP _ _)).2
      (GlobalTheory.T.biadditive_of_trivial_on_axes hG (Sp R) c.A c.diag c.ab hD hamp c.P hP c.rig₁ c.rig₂ T x x' y).1
    rw [cls_linComb hP, Fin.sum_univ_three] at e
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, one_smul, neg_smul] at e
    rw [← sub_eq_zero, ← e]
    simp only [bi]
    abel
  have hs : ∀ (T : Over (Sp R)) (x y : T ⟶ c.A), bi hP x y = bi hP y x := fun T x y => by
    have e : cls c.P hP = bi hP (snd c.A c.A) (fst c.A c.A) := (cls_eq_iff hP (pull_isLB hP _)).2 c.symm
    rw [bi, e, pull_bi, lift_fst, lift_snd]
  have hLB : (sharp c.P pr W).IsLB := LB.isLB_linComb hP _ _
  refine ⟨{ A := G
            isAb := isAbelianScheme_powObj_of_isAbelianScheme Q.B Q.isAb r
            g := r * Q.g
            smoothDim := powObj_smoothOfRelativeDimension_mul _ _ _ r Q.smoothDim
            L := sharp c.P pr W
            isLB := hLB
            rigid := rigidified_sharp hP pr W hpr hB
            sym := sym_sharp hP pr W hpr hB hs
            ample := GlobalTheory.T.relAmple_formBundle_power_of_posDef hG 0 1 r R 1 (Sp R) (𝟙 _) c G pr W hpr hu hamp hpd
            ktriv := kTriv_sharp hP pr W hpr hB hs hu (GlobalTheory.Mum.PowPol.det_eq_one W hpd hdet)
              (fun T x hx => eq_one_of_lam Q.M.isLB Q.ktriv x hx) }, pr, hpr, ⟨Out.powIsLimit Q.B r⟩, ?_⟩
  refine lbIso_nested Q.M.isLB _ _ (fun uv : Fin r × Fin r => (lift (pr uv.1) (pr uv.2)).left) (fun uv => W uv.1 uv.2) _ _ ?_
  simp only [prod_lam (pr _) (pr _) (PrimNorm.cls Q.M.L)]
  rw [Fintype.prod_prod_type (f := fun k : (Fin r × Fin r) × Fin 4 => PrimNorm.cls Q.M.L (tensφ pr k) ^ tensε W k)]
  refine Finset.prod_congr rfl fun uv _ => ?_
  simp only [Fin.prod_univ_four, tensφ, tensε, GlobalTheory.PolDeg.lamPts, Oε, diff₂, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val, zpow_mul]
  simp only [zpow_one, zpow_neg, mul_zpow, inv_zpow]

end GlobalTheory.Mum.TensPow
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_tensorTrivialisation_powerLattice_points : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (A' : Over (Spec (CommRingCat.of R))) [GrpObj A'] (L' : LB A'.left), L'.IsLB → ∀ (pr : Fin r → (A' ⟶ D.P.A)) (w : LB.Iso L' (LB.LinComb D.P.L (tensφ pr) (tensε W))), w.IsGen → ∀ (x : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ A') (y : Fin r → D.X), (∀ i, x ≫ pr i = D.c (y i)) → ∃ ψ : LB.Gen (LB.LinComb L' (K := PUnit) (fun _ => ptK x) (fun _ => -1)), ψ.IsGen ∧ ∀ (z : (TK R).left) (J : ((TK R).left ⟶ D.P.A.left) → D.P.L.ι) (J' : ((TK R).left ⟶ A'.left) → L'.ι), Good D.P.L z J → Good L' z J' → val ψ (𝟙 _) z J' = gm (ptK x) z _ (w.s (fun k => J (ptK x ≫ tensφ pr k), J' (ptK x))) * ∏ i, ∏ j, val (D.tau (y i) (y j)) (𝟙 _) z J ^ W i j := by
  first | exact @GlobalTheory.Mum.tensPsi_exists | exact GlobalTheory.Mum.tensPsi_exists | (intros; apply GlobalTheory.Mum.tensPsi_exists <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_pullback_eighth_power_endomorphisms_field_point : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (R : Type) [CommRing R] (P : PolAV (Sp R)) (ε : Matrix (Fin 8) (Fin 8) ℤ → (P.A ⟶ P.A)) (u' : Sp R ⟶ F.X), IsDiagEnd F W P u' ε → ∀ (K : Type) [Field K] (yK : R →+* K), ∃ (A : PolAV (Sp K)) (φ : A.A.left ⟶ P.A.left) (_ : IsGrpPullback A.A P.A (spMap yK) φ) (_ : LBIso A.L (P.L.pull φ)) (εA : Matrix (Fin 8) (Fin 8) ℤ → (A.A ⟶ A.A)), IsDiagEnd F W A (spMap yK ≫ u') εA ∧ ∀ (Y : Over (Sp K)) (x x' : Y ⟶ A.A) (E : Matrix (Fin 8) (Fin 8) ℤ), x'.left ≫ φ = x.left ≫ φ ≫ (ε E).left → x' = x ≫ εA E := by
  first | exact @GlobalTheory.Poinc.DiagPull.exists_pull_field | exact GlobalTheory.Poinc.DiagPull.exists_pull_field | (intros; apply GlobalTheory.Poinc.DiagPull.exists_pull_field <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

theorem _root_.GlobalTheory.T.eighthPower_trivialisation_eq_unit_mul_monomial : ∀ (W : Matrix (Fin 8) (Fin 8) ℤ), PosW W → ∀ (V V₁ : Type) [CommRing V] [IsDomain V] [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁] (Q : Data V) (ρ : V →+* V₁), Function.Injective ρ → ∀ (m : ℕ) (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ Q.X), (∀ k a b, δ k a b = δ k b a) → (∀ k a, 0 ≤ δ k a a) → (∀ k, t k ≠ 0) → Q.IsMonomialTau t δ → ∀ (D : DegPre V₁) (e : (Fin 8 → Q.X) ≃+ D.X), SharpRef W Q ρ D e → ∀ mu, ∃ u : V₁ˣ, Formalism.L2.Pj.PsiCoord D (e mu) (u * mono W (fun k => ρ (t k)) δ mu) := by
  first | exact @GlobalTheory.Poinc.Sep.psi_unit_mono | exact GlobalTheory.Poinc.Sep.psi_unit_mono | (intros; apply GlobalTheory.Poinc.Sep.psi_unit_mono <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.rechartings_thetaSetup_same_geometric_fibre_at_trait : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X : Setup F W i) (ε : Matrix (Fin 8) (Fin 8) ℤ → (X.ρ.P.A ⟶ X.ρ.P.A)) (p : ℕ) [Fact p.Prime] (z : X.M.Z) (c : CTrait X p z) (c₀ : X.Ω₁) (hc : c₀ ≠ 0) (R' : Subalgebra X.o₁ X.Ω₁) (fg : R'.FG) (frac : ∀ x : X.Ω₁, ∃ a ∈ R', ∃ b ∈ R', x = a / b) (hth : ∀ x, c₀ * X.S.th x ∈ R') (hev : ∀ x k, c₀ * X.S.ev x k ∈ R') (ρ' : (X.S.rechart c₀ hc R' fg frac hth hev).Real) (ε' : Matrix (Fin 8) (Fin 8) ℤ → (ρ'.P.A ⟶ ρ'.P.A)), Same X.ρ ε ρ' ε' (fun x => x) (RingHom.id _) → R' ≤ X.M.O ((gPt p ≫ c.y) (closedPoint (PadicAlgCl p))) → ∀ (y₀ : R' →+* PadicAlgCl p), (∀ a : R', y₀ a = X.M.val (gPt p ≫ c.y) a) → ∀ (c₁ : X.Ω₁) (hc₁ : c₁ ≠ 0) (R'' : Subalgebra X.o₁ X.Ω₁) (fg₁ : R''.FG) (frac₁ : ∀ x : X.Ω₁, ∃ a ∈ R'', ∃ b ∈ R'', x = a / b) (hth₁ : ∀ x, c₁ * X.S.th x ∈ R'') (hev₁ : ∀ x k, c₁ * X.S.ev x k ∈ R'') (ρ'' : (X.S.rechart c₁ hc₁ R'' fg₁ frac₁ hth₁ hev₁).Real) (ε'' : Matrix (Fin 8) (Fin 8) ℤ → (ρ''.P.A ⟶ ρ''.P.A)), Same X.ρ ε ρ'' ε'' (fun x => x) (RingHom.id _) → R'' ≤ X.M.O ((gPt p ≫ c.y) (closedPoint (PadicAlgCl p))) → ∀ (y₁ : R'' →+* PadicAlgCl p), (∀ a : R'', y₁ a = X.M.val (gPt p ≫ c.y) a) → ∀ (u : ρ'.UTest p y₀) (u' : ρ''.UTest p y₁), ∃ (P₀ : PolAV (Sp (PadicAlgCl p))) (a : P₀.A.left ⟶ u.A.A.left) (a' : P₀.A.left ⟶ u'.A.A.left), IsGrpPullback P₀.A u.A.A (spMap (algebraMap (FractionRing u.V) (PadicAlgCl p))) a ∧ IsGrpPullback P₀.A u'.A.A (spMap (algebraMap (FractionRing u'.V) (PadicAlgCl p))) a' ∧ LBIso P₀.L (u.A.L.pull a) ∧ LBIso P₀.L (u'.A.L.pull a') ∧ (∀ b : X.S.Gam, ∃ (w : Sp (PadicAlgCl p) ⟶ P₀.A.left) (x : TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A) (x' : TFK (R := u'.V) (PadicAlgCl p) ⟶ u'.A.A), w ≫ P₀.A.hom = 𝟙 _ ∧ w ≫ a = x.left ∧ w ≫ a' = x'.left ∧ x.left ≫ u.φ = spMap y₀ ≫ (ρ'.pt b).left ∧ x'.left ≫ u'.φ = spMap y₁ ≫ (ρ''.pt b).left) ∧ ∀ (E : Matrix (Fin 8) (Fin 8) ℤ) (w w₂ : Sp (PadicAlgCl p) ⟶ P₀.A.left), w ≫ P₀.A.hom = 𝟙 _ → w₂ ≫ P₀.A.hom = 𝟙 _ → w₂ ≫ a ≫ u.φ = w ≫ a ≫ u.φ ≫ (ε' E).left → w₂ ≫ a' ≫ u'.φ = w ≫ a' ≫ u'.φ ≫ (ε'' E).left := by
  first | exact @GlobalTheory.Poinc.Spread.main | exact GlobalTheory.Poinc.Spread.main | (intros; apply GlobalTheory.Poinc.Spread.main <;> assumption)
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem tens_lam_core : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D D' : DegData R I) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (T : Tens D.toPre D'.toPre W), ∃ w₁ : LB.Iso (abelian₂ D'.toPre.P.A D'.toPre.P.L) (LB.LinComb D.toPre.P.L (fun k : (Fin r × Fin r) × Fin 4 => GlobalTheory.PolDeg.lamPts (fst D'.toPre.P.A D'.toPre.P.A ≫ T.pr k.1.1) (snd D'.toPre.P.A D'.toPre.P.A ≫ T.pr k.1.2) k.2) (fun k => (W + W.transpose) k.1.1 k.1.2 * Oε k.2)), w₁.IsGen ∧ ∀ (a b : D'.toPre.X) (z : (TK R).left) (J : ((TK R).left ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι) (J' : ((TK R).left ⟶ D'.toPre.P.A.left) → D'.toPre.P.L.ι), Good D.toPre.P.L z J → Good D'.toPre.P.L z J' → val (D'.toPre.tau a b) (𝟙 _) z J' = gm (lift (toUnit (TK R) ≫ D'.toPre.c a) (toUnit (TK R) ≫ D'.toPre.c b)).left z _ (w₁.s (fun k => J ((lift (toUnit (TK R) ≫ D'.toPre.c a) (toUnit (TK R) ≫ D'.toPre.c b)).left ≫ GlobalTheory.PolDeg.lamPts (fst D'.toPre.P.A D'.toPre.P.A ≫ T.pr k.1.1) (snd D'.toPre.P.A D'.toPre.P.A ≫ T.pr k.1.2) k.2), fun I => J' ((lift (toUnit (TK R) ≫ D'.toPre.c a) (toUnit (TK R) ≫ D'.toPre.c b)).left ≫ (psum D'.toPre.P.A (x2 D'.toPre.P.A) I.down).left))) * ∏ i, ∏ j, val (D.toPre.tau (T.xe a i) (T.xe b j)) (𝟙 _) z J ^ ((W + W.transpose) i j) := by
  intro R _ _ I D D' r W T
  obtain ⟨v, hv, hvv⟩ := GlobalTheory.T.exists_linCombPullbackTransportIso_with_values (L := D.toPre.P.L) (L' := D'.toPre.P.L) (tensφ T.pr) (tensε W) T.w T.w_gen
    D.toPre.P.isLB D'.toPre.P.isLB
    (fun K : ULift.{0} (Finset (Fin 2)) => (psum D'.toPre.P.A (x2 D'.toPre.P.A) K.down).left)
    (fun K => (-1 : ℤ) ^ (2 - K.down.card))
  obtain ⟨c, hc, hcv⟩ := GlobalTheory.T.exists_cubeStep_generator_tensorPowerPairs (⟨D.toPre.P.L, D.toPre.rig, D.toPre.P.isLB, D.toPre.rig_gen⟩ : RigLB D.toPre.P.A)
    D.toPre.cub W T.pr T.pr_hom
  obtain ⟨u, hu, huv⟩ := GlobalTheory.T.exists_lineBundleIso_comp_linCombGenerator (A := abelian₂ D'.toPre.P.A D'.toPre.P.L) _ _
    (fun k : (Fin r × Fin r) × Fin 4 => GlobalTheory.PolDeg.lamPts (fst D'.toPre.P.A D'.toPre.P.A ≫ T.pr k.1.1)
      (snd D'.toPre.P.A D'.toPre.P.A ≫ T.pr k.1.2) k.2)
    (fun k => (W + W.transpose) k.1.1 k.1.2 * Oε k.2) D.toPre.P.isLB (LB.isLB_linComb D'.toPre.P.isLB _ _) v hv c hc
  refine ⟨u, hu, fun a b z J J' hJ hJ' => ?_⟩
  have e1 := hvv _ (lift (toUnit (TK R) ≫ D'.toPre.c a) (toUnit (TK R) ≫ D'.toPre.c b)).left z J J' hJ hJ'
  have e2 := hcv (TK R) (lift (toUnit (TK R) ≫ D'.toPre.c a) (toUnit (TK R) ≫ D'.toPre.c b)) z J hJ
  rw [huv _ _ z J _ (hJ'.mem _ _) hJ, e2]
  refine (GlobalTheory.T.theta_value_product_formula_degeneration R I D D' W T a b z J J' hJ hJ').trans ?_
  exact congrArg (· * _) (congrArg (· * _) e1.symm)

end GlobalTheory.Mum
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc.GLift

theorem transport : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i), 1 ≤ g → 3 ≤ n → Odd n → IsOpenImmersion i → IsE8 W → ThetaInt F W i → IsProjOver X₁.M.s → ∀ (ε₁ : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), IsDiagEnd F W X₁.ρ.P X₁.u ε₁ → ∀ (D : Deep X₁ ε₁) (p : ℕ) [Fact p.Prime] (z₁ : X₁.M.Z) (c : CTrait X₁ p z₁) (y : Sp (OO p) ⟶ D.X.M.Z) (h : y ≫ D.q = c.y)
  (c₀ : X₁.Ω₁) (hc : c₀ ≠ 0) (R' : Subalgebra X₁.o₁ X₁.Ω₁) (fg : R'.FG) (frac : ∀ x : X₁.Ω₁, ∃ a ∈ R', ∃ b ∈ R', x = a / b) (hth : ∀ x, c₀ * X₁.S.th x ∈ R') (hev : ∀ x k, c₀ * X₁.S.ev x k ∈ R') (ρ' : (X₁.S.rechart c₀ hc R' fg frac hth hev).Real) (ε' : Matrix (Fin 8) (Fin 8) ℤ → (ρ'.P.A ⟶ ρ'.P.A)), Same X₁.ρ ε₁ ρ' ε' (fun x => x) (RingHom.id _) → ρ'.i₀ = X₁.ρ.i₀ → R' ≤ X₁.M.O ((gPt p ≫ c.y) (closedPoint (PadicAlgCl p))) → ∀ (y₀ : R' →+* PadicAlgCl p), (∀ a : R', y₀ a = X₁.M.val (gPt p ≫ c.y) a) → ∀ (u : ρ'.UTest p y₀)
  (c₂ : D.X.Ω₁) (hc₂ : c₂ ≠ 0) (R₂ : Subalgebra D.X.o₁ D.X.Ω₁) (fg₂ : R₂.FG) (frac₂ : ∀ x : D.X.Ω₁, ∃ a ∈ R₂, ∃ b ∈ R₂, x = a / b) (hth₂ : ∀ x, c₂ * D.X.S.th x ∈ R₂) (hev₂ : ∀ x k, c₂ * D.X.S.ev x k ∈ R₂) (ρ₂ : (D.X.S.rechart c₂ hc₂ R₂ fg₂ frac₂ hth₂ hev₂).Real) (ε₂ : Matrix (Fin 8) (Fin 8) ℤ → (ρ₂.P.A ⟶ ρ₂.P.A)), Same D.X.ρ D.ε ρ₂ ε₂ (fun x => x) (RingHom.id _) → ρ₂.i₀ = D.X.ρ.i₀ → R₂ ≤ D.X.M.O ((gPt p ≫ y) (closedPoint (PadicAlgCl p))) → ∀ (y₂ : R₂ →+* PadicAlgCl p), (∀ a : R₂, y₂ a = D.X.M.val (gPt p ≫ y) a) →
  ∃ (u₂ : ρ₂.UTest p y₂) (e : u₂.D.toPre.X ≃+ u.D.toPre.X) (T : (TFK (R := u₂.V) (PadicAlgCl p) ⟶ u₂.A.A) ≃ (TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A)),
    (∀ χ r, u.PsiNorm (e χ) r → u₂.PsiNorm χ r) ∧
    (∀ x₂ a, x₂.left ≫ u₂.φ = spMap y₂ ≫ (ρ₂.pt (D.lab a)).left ↔ (T x₂).left ≫ u.φ = spMap y₀ ≫ (ρ'.pt a).left) ∧
    (∀ x₂ x₂' E, x₂'.left ≫ u₂.φ = x₂.left ≫ u₂.φ ≫ (ε₂ E).left → (T x₂').left ≫ u.φ = (T x₂).left ≫ u.φ ≫ (ε' E).left) ∧
    (∀ (m : ℕ) (pk₂ : QkPt u₂.D.toPre (PadicAlgCl p) m) x₂, 1 ≤ m → QkToAkU u₂.U.toUnifPre (PadicAlgCl p) m pk₂ x₂ → ∃ pk : QkPt u.D.toPre (PadicAlgCl p) m, pk.y = e pk₂.y ∧ QkToAkU u.U.toUnifPre (PadicAlgCl p) m pk (T x₂)) ∧
    (∀ (m : ℕ) (pk : QkPt u.D.toPre (PadicAlgCl p) m) x, 1 ≤ m → QkToAkU u.U.toUnifPre (PadicAlgCl p) m pk x → ∃ pk₂ : QkPt u₂.D.toPre (PadicAlgCl p) m, e pk₂.y = pk.y ∧ QkToAkU u₂.U.toUnifPre (PadicAlgCl p) m pk₂ (T.symm x)) := by
  intro g n F W Z i X₁ hg hn hodd himm he8 hth hproj ε₁ hdiag D p _ z₁ c y h c₀ hc R' fg frac hth' hev ρ' ε' hS hi hR y₀ hy₀ u c₂ hc₂ R₂ fg₂ frac₂ hth₂ hev₂ ρ₂ ε₂ hS₂ hi₂ hR₂ y₂ hy₂
  obtain ⟨V₂, _, _, _, _, hV₂c, hV₂n, σ, hσ, hval⟩ := GlobalTheory.T.exists_complete_dvr_field_values_deeper_point g n F W Z i X₁ hg hn hodd himm he8 hth hproj ε₁ hdiag D p z₁ c y h u.V u.complete u.norm_le
  obtain ⟨u', τ, e, T, hτ, hpsi, hT, hfw, hbw⟩ := GlobalTheory.T.uniformisedModel_baseChange_complete_dvr_extension _ _ _ ρ' p y₀ u V₂ hV₂c hV₂n σ hσ
  have hval' : ∀ a ∈ D.X.M.O ((gPt p ≫ y) (closedPoint (PadicAlgCl p))),
      D.X.M.val (gPt p ≫ y) a ∈ (algebraMap (FractionRing u'.V) (PadicAlgCl p)).range := by
    intro a ha
    obtain ⟨b, hb⟩ := hval a ha
    exact ⟨τ b, by rw [← hb, ← hτ]; rfl⟩
  have hSS := GlobalTheory.T.sameGenericFibre_chain_rescaled_deeper_realisation g n F W Z i X₁ ε₁ D c₀ hc R' fg frac hth' hev ρ' ε' c₂ hc₂ R₂ fg₂ frac₂ hth₂ hev₂ ρ₂ ε₂ hS hS₂
  obtain ⟨f₂, φ₂, hf₂, hcart, hlb, htor, heps⟩ := GlobalTheory.T.realisations_same_genericFibre_agree_at_points g n F W Z i X₁ hg hn hodd himm he8 hth hproj ε₁ hdiag D p z₁ c y h
    c₀ hc R' fg frac hth' hev ρ' ε' hR y₀ hy₀ c₂ hc₂ R₂ fg₂ frac₂ hth₂ hev₂ ρ₂ ε₂ hSS hR₂ y₂ hy₂
    (FractionRing u'.V) (algebraMap _ _) u'.yK u'.fac hval' u'.A u'.φ u'.cart u'.lb
  let u₂ : ρ₂.UTest p y₂ :=
    { V := u'.V, complete := u'.complete, norm_le := u'.norm_le, yK := f₂, fac := hf₂, A := u'.A, φ := φ₂,
      cart := hcart, lb := hlb, G := u'.G, semi := u'.semi, D := u'.D, U := u'.U }
  refine ⟨u₂, e, T, hpsi, ?_, ?_, hfw, hbw⟩
  · intro x₂ a
    rw [hT]
    exact htor x₂.left a (Over.w x₂)
  · intro x₂ x₂' E hxx
    rw [hT, ← Category.assoc, hT, Category.assoc]
    exact (heps x₂.left x₂'.left E (Over.w x₂) (Over.w x₂')).1 hxx

end GlobalTheory.Poinc.GLift
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

open ReciprocityTheory.ChartRestriction.G.DVR

namespace GlobalTheory.TensBimult

theorem alg {U X X' : Type} [CommGroup U] [AddCommGroup X] [AddCommGroup X'] {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ)
    (e : X' ≃+ (Fin r → X)) (Ψ : X → U) (ρ : U) (O ψ' : X' → U) (τ' : X' → X' → U) (t : X → X → U) (c' rig' : U)
    (a a' b : X') (ht : ∀ u v, t u v = Ψ (u + v) * (Ψ u)⁻¹ * (Ψ v)⁻¹ * ρ⁻¹)
    (hψ : ∀ u, ψ' u = O u * ∏ i, ∏ j, t (e u i) (e u j) ^ W i j)
    (hτ : ∀ u v, τ' u v = ψ' (u + v) * (ψ' u)⁻¹ * (ψ' v)⁻¹ * rig'⁻¹) (hr : ψ' 0 * rig' = 1)
    (hc : c' * (O (a + a' + b) * (O (a + a'))⁻¹ * (O (a + b))⁻¹ * (O (a' + b))⁻¹ * O a * O a' * O b * (O 0)⁻¹) =
      ∏ k : (Fin r × Fin r) × Fin 4,
        (t (![e a k.1.1 + e a k.1.2, e a k.1.1, e a k.1.2, 0] k.2) (![e b k.1.1 + e b k.1.2, e b k.1.1, e b k.1.2, 0] k.2) *
          t (![e a' k.1.1 + e a' k.1.2, e a' k.1.1, e a' k.1.2, 0] k.2) (![e b k.1.1 + e b k.1.2, e b k.1.1, e b k.1.2, 0] k.2) *
          (t (![e a k.1.1 + e a k.1.2, e a k.1.1, e a k.1.2, 0] k.2 + ![e a' k.1.1 + e a' k.1.2, e a' k.1.1, e a' k.1.2, 0] k.2)
            (![e b k.1.1 + e b k.1.2, e b k.1.1, e b k.1.2, 0] k.2))⁻¹) ^ tensε W k) :
    τ' (a + a') b * c' = τ' a b * τ' a' b := by
  have hr' : rig'⁻¹ = ψ' 0 := (eq_inv_of_mul_eq_one_right hr).symm ▸ inv_inv _
  rw [eq_mul_inv_of_mul_eq hc, hτ, hτ, hτ, hr']
  simp only [hψ, ht, Fintype.prod_prod_type, Fin.prod_univ_four, tensε, Oε, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, map_add, Pi.add_apply, map_zero, Pi.zero_apply,
    add_zero, zero_add]
  have e1 : ∀ x x1, Ψ (e a x + e a x1 + (e a' x + e a' x1) + (e b x + e b x1)) = Ψ (e a x + e a' x + e b x + (e a x1 + e a' x1 + e b x1)) := fun x x1 => congrArg Ψ (by abel)
  have e2 : ∀ x x1, Ψ (e a x + e a x1 + (e a' x + e a' x1)) = Ψ (e a x + e a' x + (e a x1 + e a' x1)) := fun x x1 => congrArg Ψ (by abel)
  have e3 : ∀ x x1, Ψ (e a x + e a x1 + (e b x + e b x1)) = Ψ (e a x + e b x + (e a x1 + e b x1)) := fun x x1 => congrArg Ψ (by abel)
  have e4 : ∀ x x1, Ψ (e a' x + e a' x1 + (e b x + e b x1)) = Ψ (e a' x + e b x + (e a' x1 + e b x1)) := fun x x1 => congrArg Ψ (by abel)
  simp only [e1, e2, e3, e4]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, ofMul_prod, ofMul_zpow, smul_add, smul_neg, Finset.sum_add_distrib,
    Finset.sum_neg_distrib, _root_.mul_one, mul_neg, neg_smul]
  abel

end GlobalTheory.TensBimult

namespace GlobalTheory.TensBimult

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D : DegData R (maximalIdeal R)) (D' : DegPre R) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ), Tens D.toPre D' W → (∀ (z : (TK R).left) (J : ((TK R).left ⟶ D'.P.A.left) → D'.P.L.ι), Good D'.P.L z J → val (D'.psi 0) (𝟙 _) z J * val D'.rigK (𝟙 _) z J = 1) → D'.TauBimult := by
  intro R _ _ _ _ D D' r W T hn a a' b
  have hG : GlobalFnsSt := GlobalTheory.lawsAndExpansions.1.1.globalFns
  refine corr_of_val D'.P.isLB fun y J' hJ' => ?_
  obtain ⟨J, hJ⟩ : ∃ J, Good D.toPre.P.L y J :=
    ⟨fun ψ => (exists_chart D.toPre.P.isLB (ψ y)).choose, fun ψ => (exists_chart D.toPre.P.isLB (ψ y)).choose_spec⟩
  have key := GlobalTheory.T.tensorPreData_cubicalStructure_eq_prod_pulled_back hG R D.toPre D' W T (TK R) y J J' hJ hJ' (cP D' _ a) (cP D' _ a') (cP D' _ b)
  have hψ : ∀ u, val (D'.psi u) (𝟙 _) y J' = gm (cP D' (TK R) u).left y _ (T.w.s (fun k => J ((cP D' (TK R) u).left ≫ tensφ T.pr k), J' (cP D' (TK R) u).left)) * ∏ i, ∏ j, val (D.toPre.tau (T.xe u i) (T.xe u j)) (𝟙 _) y J ^ W i j :=
    fun u => T.psi u y J J' hJ hJ'
  have vt : ∀ u v, val (D'.tau u v) (𝟙 _) y J' = val (D'.psi (u + v)) (𝟙 _) y J' * (val (D'.psi u) (𝟙 _) y J')⁻¹ * (val (D'.psi v) (𝟙 _) y J')⁻¹ * (val D'.rigK (𝟙 _) y J')⁻¹ := by
    intro u v; simp only [DegPre.tau, val_mul hJ', val_inv]
  have vtE : ∀ u v, val (D.toPre.tau u v) (𝟙 _) y J = val (D.toPre.psi (u + v)) (𝟙 _) y J * (val (D.toPre.psi u) (𝟙 _) y J)⁻¹ * (val (D.toPre.psi v) (𝟙 _) y J)⁻¹ * (val D.toPre.rigK (𝟙 _) y J)⁻¹ := by
    intro u v; simp only [DegPre.tau, val_mul hJ, val_inv]
  have hB : ∀ u u' v, val (D.toPre.tau (u + u') v) (𝟙 _) y J * cubV D.toPre.cub y J (cP D.toPre _ u) (cP D.toPre _ u') (cP D.toPre _ v) = val (D.toPre.tau u v) (𝟙 _) y J * val (D.toPre.tau u' v) (𝟙 _) y J := fun u u' v =>
    (GlobalTheory.TauBimultBox.val_lhs D.toPre hJ u u' v).symm.trans ((val_corr hJ (D.tau_bimult u u' v) (𝟙 _)).trans (val_mul hJ _ _ _))
  have c0 : ∀ (E : DegPre R) (S : Over (Spec (CommRingCat.of R))), cP E S 0 = 1 := fun E S => by
    have := cPoint_add E S 0 0
    rw [add_zero] at this
    exact mul_eq_left.1 this.symm
  have hP : ∀ u (k : (Fin r × Fin r) × Fin 4), cP D' (TK R) u ≫ ![T.pr k.1.1 * T.pr k.1.2, T.pr k.1.1, T.pr k.1.2, 1] k.2 = cP D.toPre (TK R) (![T.xe u k.1.1 + T.xe u k.1.2, T.xe u k.1.1, T.xe u k.1.2, 0] k.2) := by
    intro u k
    have e : ∀ i, cP D' (TK R) u ≫ T.pr i = cP D.toPre (TK R) (T.xe u i) := fun i => by
      rw [cP, Category.assoc, T.c_pr]; rfl
    obtain ⟨⟨i, j⟩, m⟩ := k
    fin_cases m
    · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
      rw [MonObj.comp_mul, e, e, cPoint_add]
    · simpa using e i
    · simpa using e j
    · simp only [Fin.reduceFinMk, Fin.isValue, Matrix.cons_val]
      rw [c0]; simp [Hom.one_def]
  rw [GlobalTheory.TauBimultBox.val_lhs D' hJ' a a' b, val_mul hJ']
  have hC : ∀ u u' v, cubV D.toPre.cub y J (cP D.toPre _ u) (cP D.toPre _ u') (cP D.toPre _ v) = val (D.toPre.tau u v) (𝟙 _) y J * val (D.toPre.tau u' v) (𝟙 _) y J * (val (D.toPre.tau (u + u') v) (𝟙 _) y J)⁻¹ := fun u u' v => by
    rw [← hB u u' v, mul_comm, inv_mul_cancel_left]
  simp only [hP, hC] at key
  have h1 : cP D' (TK R) a * cP D' (TK R) a' * cP D' (TK R) b = cP D' (TK R) (a + a' + b) := by rw [cPoint_add, cPoint_add]
  have h2 : cP D' (TK R) a * cP D' (TK R) a' = cP D' (TK R) (a + a') := (cPoint_add _ _ _ _).symm
  have h3 : cP D' (TK R) a * cP D' (TK R) b = cP D' (TK R) (a + b) := (cPoint_add _ _ _ _).symm
  have h4 : cP D' (TK R) a' * cP D' (TK R) b = cP D' (TK R) (a' + b) := (cPoint_add _ _ _ _).symm
  rw [h1, h2, h3, h4, ← c0 D' (TK R)] at key
  refine alg W T.xe (fun u => val (D.toPre.psi u) (𝟙 _) y J) (val D.toPre.rigK (𝟙 _) y J)
    (fun u => gm (cP D' (TK R) u).left y _ (T.w.s (fun k => J ((cP D' (TK R) u).left ≫ tensφ T.pr k), J' (cP D' (TK R) u).left)))
    (fun u => val (D'.psi u) (𝟙 _) y J') (fun u v => val (D'.tau u v) (𝟙 _) y J') (fun u v => val (D.toPre.tau u v) (𝟙 _) y J)
    (cubV D'.cub y J' (cP D' (TK R) a) (cP D' (TK R) a') (cP D' (TK R) b)) (val D'.rigK (𝟙 _) y J') a a' b vtE hψ vt (hn y J' hJ') ?_
  beta_reduce
  exact key

end GlobalTheory.TensBimult
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.TensPolBimult

theorem base_of_isCN {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] (h : IsCN R) : Base R :=
  ⟨⟨h.1, inferInstance, h.2.1, h.2.2.1⟩, h.2.2.2⟩

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], IsCN R → ∀ (Q : Data R) (D' : DegPre R) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (pr : Fin r → (D'.P.A ⟶ Q.B)), (∀ i, IsMonHom (pr i)) → IsLimit (Fan.mk D'.P.A pr) → ∀ (xe : D'.X ≃+ (Fin r → Q.X)), (∀ z i, D'.c z ≫ pr i = Q.c (xe z i)) → ∀ (w : LB.Iso D'.P.L (LB.LinComb Q.M.L (tensφ pr) (tensε W))), w.IsGen → (∀ y z J J', Good Q.M.L z J → Good D'.P.L z J' → val (D'.psi y) (𝟙 _) z J' = gm (D'.xK y) z _ (w.s (fun k => J (D'.xK y ≫ tensφ pr k), J' (D'.xK y))) * ∏ i, ∏ j, val (Q.tau (xe y i) (xe y j)) (𝟙 _) z J ^ W i j) → (∀ (z : (TK R).left) (J : ((TK R).left ⟶ D'.P.A.left) → D'.P.L.ι), Good D'.P.L z J → val (D'.psi 0) (𝟙 _) z J * val D'.rigK (𝟙 _) z J = 1) → D'.TauBimult := by
  intro R _ _ _ hR Q D' r W pr hpr hlim xe hc w hw hpsi hn
  exact GlobalTheory.PolTensBimult.main R (base_of_isCN hR) Q D' W pr xe ⟨hpr, ⟨hlim⟩, hc, w, hw, hpsi⟩ hn

end GlobalTheory.TensPolBimult
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.fibre_iso_carries_sharp_points_to_conjugates : ∀ (g l : ℕ), l.Prime → Odd l → ∀ W : Matrix (Fin 8) (Fin 8) ℤ, IsE8 W → ∃ j₀ : ℕ, ∀ j, j₀ ≤ j → ∀ (V V₁ : Type) [CommRing V] [IsDomain V] [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → IsUnit (l : V₁) → ∀ (Q : Data V), Q.g ≤ g → ∀ (ρ : V →+* V₁), Function.Injective ρ → ∀ (D : DegPre V₁) (e : (Fin 8 → Q.X) ≃+ D.X), SharpRef W Q ρ D e → ∀ (C : Type) (u : (Fin 8 → Q.X) → C → V₁) (mo : (Fin 8 → Q.X) → V₁), (∀ mu, mo mu ≠ 0 ∧ ∃ c, IsUnit (u mu c)) → IsThetaTerms D ((l ^ j) ^ 2) e (fun mu c => u mu c * mo mu) → ∀ (K : Type) [Field K] [IsAlgClosed K] (ev : V₁ →+* K) (k₀ : Subfield K), IsAlgClosed k₀ → (∀ mu c c', IsUnit (u mu c') → ∃ r ∈ k₀, ev (u mu c) = r * ev (u mu c')) → ∀ (σ : K ≃+* K), (∀ r ∈ k₀, σ r = r) → ∀ (f : ((Over.pullback (spMap ev)).obj D.P.A).left ⟶ ((Over.pullback (spMap (σ.toRingHom.comp ev))).obj D.P.A).left), IsGrpPullback ((Over.pullback (spMap ev)).obj D.P.A) ((Over.pullback (spMap (σ.toRingHom.comp ev))).obj D.P.A) (𝟙 _) f → LBIso (D.P.L.pull (pullback.fst D.P.A.hom (spMap ev))) (D.P.L.pull (f ≫ pullback.fst D.P.A.hom (spMap (σ.toRingHom.comp ev)))) → (∀ (y : Over.mk (spMap ev) ⟶ D.P.A), y ^ ((l ^ j) ^ 2) = 1 → ∀ q : Sp K ⟶ ((Over.pullback (spMap ev)).obj D.P.A).left, q ≫ pullback.fst D.P.A.hom (spMap ev) = y.left → q ≫ pullback.snd D.P.A.hom (spMap ev) = 𝟙 _ → q ≫ f ≫ pullback.fst D.P.A.hom (spMap (σ.toRingHom.comp ev)) = spMap σ.toRingHom ≫ y.left) → (∀ mu (q : Sp K ⟶ ((Over.pullback (spMap ev)).obj D.P.A).left), q ≫ pullback.fst D.P.A.hom (spMap ev) = spMap ev ≫ (D.c (e mu)).left → q ≫ pullback.snd D.P.A.hom (spMap ev) = 𝟙 _ → q ≫ f ≫ pullback.fst D.P.A.hom (spMap (σ.toRingHom.comp ev)) = spMap σ.toRingHom ≫ q ≫ pullback.fst D.P.A.hom (spMap ev)) := by
  first | exact @GlobalTheory.Poinc.Sep.conj_sharp_points | exact GlobalTheory.Poinc.Sep.conj_sharp_points | (intros; apply GlobalTheory.Poinc.Sep.conj_sharp_points <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.tensorData_psi_mem_maximalIdeal_tendsto_zero : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D : DegData R (maximalIdeal R)) (D' : DegPre R) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ), ((W + W.transpose).map (Int.cast : ℤ → ℝ)).PosDef → Tens D.toPre D' W → (∀ χ : D'.X, χ ≠ 0 → D'.PsiIn χ (maximalIdeal R)) ∧ ∀ n : ℕ, {χ : D'.X | ¬ D'.PsiIn χ (maximalIdeal R ^ n)}.Finite := by
  first | exact @GlobalTheory.Mum.TensPos.psi_pos_tendsto | exact GlobalTheory.Mum.TensPos.psi_pos_tendsto | (intros; apply GlobalTheory.Mum.TensPos.psi_pos_tendsto <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum

theorem _root_.GlobalTheory.T.tensorDegenerationData_psi_even : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], IsCN R → ∀ (Q : Data R) (D' : DegPre R) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (pr : Fin r → (D'.P.A ⟶ Q.B)), (∀ i, IsMonHom (pr i)) → IsLimit (Fan.mk D'.P.A pr) → ∀ (xe : D'.X ≃+ (Fin r → Q.X)), (∀ z i, D'.c z ≫ pr i = Q.c (xe z i)) → ∀ (w : LB.Iso D'.P.L (LB.LinComb Q.M.L (tensφ pr) (tensε W))), w.IsGen → (∀ y z J J', Good Q.M.L z J → Good D'.P.L z J' → val (D'.psi y) (𝟙 _) z J' = gm (D'.xK y) z _ (w.s (fun k => J (D'.xK y ≫ tensφ pr k), J' (D'.xK y))) * ∏ i, ∏ j, val (Q.tau (xe y i) (xe y j)) (𝟙 _) z J ^ W i j) → D'.PsiEven := by
  first | exact @GlobalTheory.PolTensEven.main | exact GlobalTheory.PolTensEven.main | (intros; apply GlobalTheory.PolTensEven.main <;> assumption)
end
