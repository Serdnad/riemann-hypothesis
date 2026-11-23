module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsOfBalanced
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1990
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle116
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardLatticeDoubleCosetClassesStabilisers
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle305
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsAdeleRingTensorEquivInfiniteProdFinite
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UnivIdentity
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SymmetricLiftOddOrderExistsUnique
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle166
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle127
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle070
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CmCurveGoodOutsidePrimePremises
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle381
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2043
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle487
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HeckeFunctionalEquationAbs
public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import Mathlib.NumberTheory.NumberField.CMField
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsConstAlongSingleton
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1917
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2047
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2048
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2049
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
import Mathlib.RingTheory.Radical.NatInt
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
public import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2037
import Mathlib.Tactic.Polynomial.Basic
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.Bundle002
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.Bundle001
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Definitions.Foundations.NormEulerPolySubOneLe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1891

@[expose] public section

section

open NumberField IsDedekindDomain
open scoped Classical Pointwise
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 lamOf Th La Iop Qbar lamC)
open Formalism.MainNotions.StandardLatticesGL3 (TT stdL pt oddE0 Wd La0 Crv inc OhE IntU)
open GlobalTheory.NormSum (Pair intG)
open GlobalTheory.FunObj.SqNum (hatId CongOne skewLat unitBlock cosetVec)
open GlobalTheory.NormExact (Reads Setup IsFinIdl HasFinPart finPt)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (InId IsUnitDet unitChar stdFst)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StdRead

noncomputable section

open scoped TensorProduct

namespace GlobalTheory.FinIdlRead

open GlobalTheory.Mem.Col2.SplitChar

theorem toFinE_eq_adEquiv (D : D7) (y : Formalism.MainNotions.StandardLatticesGL3.AE D) : GlobalTheory.BotFormula.toFinE D y = adEquiv D y := by
  let f : Formalism.MainNotions.StandardLatticesGL3.AE D →+* Formalism.MainNotions.StandardLatticesGL3.AE D := (adEquiv D).symm.toRingHom.comp (GlobalTheory.BotFormula.toFinE D).toRingHom
  have hf : ∀ z, adEquiv D (f z) = GlobalTheory.BotFormula.toFinE D z := fun z => (adEquiv D).apply_symm_apply _
  have hι : ∀ (x : D.host.E) (a : FiniteAdeleRing (𝓞 ℚ) ℚ), (GlobalTheory.BotFormula.toFinE D).toRingHom (x ⊗ₜ[ℚ] a) =
      algebraMap D.host.E _ x * GlobalTheory.AdeleBaseChange.adMap ℚ D.host.E a := GlobalTheory.BotClassDict.toFinE_tmul
  have hinc : ∀ a : D.host.E, f (inc D a) = inc D a := fun a => by
    apply (adEquiv D).injective
    rw [hf, adEquiv_inc]
    have h1 : GlobalTheory.BotFormula.toFinE D (inc D a) = algebraMap D.host.E _ a * GlobalTheory.AdeleBaseChange.adMap ℚ D.host.E 1 :=
      GlobalTheory.BotClassDict.toFinE_tmul a 1
    rw [h1, map_one, mul_one]
  have hint : ∀ r ∈ OhE D, f r ∈ OhE D := fun r hr => by
    rw [mem_OhE_iff, hf]
    exact GlobalTheory.AdeleBaseChange.map_mem_int (F := ℚ) (E := D.host.E) hι hr
  have h0 : f y - y = 0 := by
    refine GlobalTheory.AdeleBaseChange.eq_zero_of_divisible (F := ℚ) (E := D.host.E) (f y - y) fun N hN => ?_
    obtain ⟨a, r, hr, e⟩ := exists_approx y hN
    refine ⟨f r - r, sub_mem (hint r hr) hr, ?_⟩
    rw [nsmul_eq_mul]
    change f y - y = (N : Formalism.MainNotions.StandardLatticesGL3.AE D) * (f r - r)
    rw [e, map_add (f := _), map_mul, map_natCast, hinc]
    ring
  rw [← hf, sub_eq_zero.1 h0]

theorem finAdEquiv_one_tmul (D : D7) (x : D.host.E) :
    GlobalTheory.LFun.finAdEquiv D.host.F D.host.E ((1 : Af D.host.F) ⊗ₜ[D.host.F] x) =
      algebraMap D.host.E (FiniteAdeleRing (𝓞 D.host.E) D.host.E) x := by
  show GlobalTheory.LFun.toFinAd D.host.F D.host.E ((1 : Af D.host.F) ⊗ₜ[D.host.F] x) = _
  rw [GlobalTheory.LFun.toFinAd_tmul, map_one, one_mul]

theorem mem_intAE_iff_finAdEquiv (D : D7) (y : Af D.host.F ⊗[D.host.F] D.host.E) :
    y ∈ intAE D ↔ ∀ P : HeightOneSpectrum (𝓞 D.host.E), Valued.v (GlobalTheory.LFun.finAdEquiv D.host.F D.host.E y P) ≤ 1 := by
  let c := (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E).toRingEquiv
  let ι : Formalism.L2.DIV.AfE D.host.F D.host.E →+* FiniteAdeleRing (𝓞 D.host.E) D.host.E :=
    (GlobalTheory.LFun.finAdEquiv D.host.F D.host.E).toRingHom.comp c.symm.toRingHom
  have hι : ∀ x a, ι (x ⊗ₜ[D.host.F] a) = algebraMap D.host.E _ x * GlobalTheory.AdeleBaseChange.adMap D.host.F D.host.E a :=
    fun x a => (GlobalTheory.LFun.toFinAd_tmul a x).trans (mul_comm _ _)
  have e : ι (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E y) = GlobalTheory.LFun.finAdEquiv D.host.F D.host.E y := by
    change GlobalTheory.LFun.finAdEquiv D.host.F D.host.E (c.symm (c y)) = _
    rw [c.symm_apply_apply]
  rw [GlobalTheory.HostAdeleIso.mem_intAE_iff_comm]
  constructor
  · intro hy
    have := GlobalTheory.AdeleBaseChange.map_mem_int hι hy
    rw [e] at this
    exact this
  · intro hy
    refine GlobalTheory.AdeleBaseChange.mem_int_of_map hι ?_
    rw [e]
    exact hy

theorem chr_finIdl : ∀ {D : D7} (ν : (AE D)ˣ →* Circle) (χ : Formalism.L2.Host.HChar D.host.E), ChrEq ν χ → ∀ x y, IsFinIdl x y →
    ((ν x : Circle) : ℂ) = ((χ.1 (GlobalTheory.Mem.Col2.SplitChar.finIdl D y) : ℂˣ) : ℂ) := by
  intro D ν χ h x y hxy
  obtain ⟨Φ, -, hΦ', h1, h2, h3⟩ := GlobalTheory.DetRootRead.exists_adele_equiv_fin D (GlobalTheory.LFun.finAdEquiv D.host.F D.host.E)
    (finAdEquiv_one_tmul D) (mem_intAE_iff_finAdEquiv D)
  rw [GlobalTheory.DetRootRead.read_of_equiv D ν χ h Φ hΦ' h1 h2 x]
  obtain ⟨s, hs, -⟩ := GlobalTheory.AdSplit.exists_adele_equiv D.host.F D.host.E
  have split : ∀ z w : AE D, infPart D z = infPart D w → finPart D z = finPart D w → z = w := fun z w hi hf =>
    s.injective (Prod.ext ((hs z).1.trans (hi.trans (hs w).1.symm)) ((hs z).2.trans (hf.trans (hs w).2.symm)))
  have hfst : (Φ (x : AE D)).1 = 1 := by
    let w : AE D := Φ.symm (1, (Φ (x : AE D)).2)
    have hw : Φ w = (1, (Φ (x : AE D)).2) := Φ.apply_symm_apply _
    have hwi : infPart D w = 1 := (h3 w).1 (by rw [hw])
    have hwf : finPart D w = finPart D (x : AE D) := by
      apply (GlobalTheory.LFun.finAdEquiv D.host.F D.host.E).injective
      rw [← (h3 w).2, ← (h3 (x : AE D)).2, hw]
    have : w = (x : AE D) := split _ _ (hwi.trans hxy.1.symm) hwf
    rw [← this, hw]
  have he : Units.map Φ.toRingHom.toMonoidHom x = GlobalTheory.Mem.Col2.SplitChar.finIdl D y := by
    refine Units.ext (Prod.ext ?_ ?_)
    · exact hfst
    · change (Φ (x : AE D)).2 = adEquiv D (y : Formalism.MainNotions.StandardLatticesGL3.AE D)
      rw [(h3 _).2, hxy.2, toFinE_eq_adEquiv]
  rw [he]

end GlobalTheory.FinIdlRead
end
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

noncomputable section

namespace GlobalTheory.ThetaSquare
open GlobalTheory.SymLiftOdd GlobalTheory.UT.SymFrame

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} {T : Over S}

theorem eq_liftFun_mul (hL : L.IsLB) {k : ℤ} (s s' : LB.Sec (LPow A L k T)) (a : Γ(T.left, ⊤))
    (h : ∀ y J, Good L y J →
      sval (L := L) (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => k) s' (𝟙 _) y J =
        gs (fst T A).left y ⊤ a * sval (L := L) (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => k) s (𝟙 _) y J)
    (j) : s'.f j = liftFun A _ a * s.f j := by
  refine fn_ext fun y hy => ?_
  choose I hI using fun χ : (T ⊗ A).left ⟶ A.left => exists_chart hL (χ y)
  have e₁ := sec_trans (L := L) (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => k) s' (𝟙 _) y hy (Good.mem hI _ (𝟙 _))
  have e₂ := sec_trans (L := L) (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => k) s (𝟙 _) y hy (Good.mem hI _ (𝟙 _))
  have e₃ : gs (𝟙 _) y _ (liftFun A ((LPow A L k T).U j) a) = gs (fst T A).left y ⊤ a :=
    (gs_res (𝟙 _) y le_top hy _).trans ((gs_pull (𝟙 _) (fst T A).left y ⊤ trivial a).trans (by rw [Category.id_comp]))
  refine e₁.trans (Eq.trans ?_ ((gs_mul _ y _ hy _ _).trans (congrArg₂ (· * ·) e₃ e₂)).symm)
  exact (congrArg _ (h y I hI)).trans (mul_left_comm _ _ _)

theorem indep (hG : GlobalFnsSt) (hA : IsAbelianScheme A) (hL : L.IsLB) {P v} (h : GRep L (T ⊗ A) P v)
    (hP : ∀ (U : Type) [CommGroup U] (h : ((T ⊗ A).left ⟶ A.left) → U), P U h = 1) (m m' : T ⊗ A ⟶ A)
    (y : (T ⊗ A).left) (J) (hJ : Good L y J) : v _ (lift (fst T A) m) y J = v _ (lift (fst T A) m') y J := by
  obtain ⟨K, _, φ, ε, s, hs, p, hv⟩ := h
  obtain ⟨a, ha⟩ := exists_constT hG hA hL (fun U _ h => (p U h).trans (hP U h)) hs
  exact (hv _ _ y J hJ).symm.trans ((ha m y J hJ).trans ((ha m' y J hJ).symm.trans (hv _ _ y J hJ)))

theorem grep_sigma {σ : LB.Gen (LB.LinComb L (K := Fin 2) ![(ι[A]).left, 𝟙 A.left] ![1, -1])} (hσ : σ.IsGen)
    {Y : Over S} (w : Y ⟶ A) :
    GRep L Y (fun _ _ h => h (w⁻¹).left * (h w.left)⁻¹) (fun _ r z J => val σ (r ≫ w).left z J) :=
  (grep_gen σ hσ w.left).congr
    (fun _ _ h => by
      rw [Fin.prod_univ_two]
      show h (w⁻¹).left ^ (1 : ℤ) * h (w.left ≫ 𝟙 _) ^ (-1 : ℤ) = _
      rw [Category.comp_id, zpow_one, zpow_neg_one])
    (fun _ _ _ _ _ => rfl)

theorem grep_two {n : T ⊗ A ⟶ A} {a b : ℤ}
    {α : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T A).left, n.left] ![a, b])} (hα : α.IsGen) (w : T ⊗ A ⟶ A) :
    GRep L (T ⊗ A) (fun _ _ h => h w.left ^ a * h (lift (fst T A) w ≫ n).left ^ b)
      (fun _ r z J => val α (r ≫ lift (fst T A) w).left z J) :=
  (grep_gen α hα (lift (fst T A) w).left).congr
    (fun _ _ h => by
      rw [Fin.prod_univ_two]
      show h (lift (fst T A) w ≫ snd T A).left ^ a * h (lift (fst T A) w ≫ n).left ^ b = _
      rw [lift_snd])
    (fun _ _ _ _ _ => rfl)

theorem square_val (hG : GlobalFnsSt) (hA : IsAbelianScheme A) (hL : L.IsLB)
    {σ : LB.Gen (LB.LinComb L (K := Fin 2) ![(ι[A]).left, 𝟙 A.left] ![1, -1])} (hσ : σ.IsGen)
    (hσ₁ : LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ σ (eSec A)) (LB.oneGen L))
    (θ : ThetaGrp A L ((4 : ℕ) : ℤ) T) (hx : θ.pt ^ 4 = 1) (nu : LB.Gen (negLB A L ((4 : ℕ) : ℤ) T))
    (hnu : ∀ y J, Good L y J → ∀ m, negVal nu y J m = (val σ m.left y J ^ 4)⁻¹)
    (hs : LB.Gen.Corr L _ _ _ _ (symGen A L ((4 : ℕ) : ℤ) θ nu) (LB.oneGen L))
    {α : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T A).left, (snd T A ^ 2).left] ![((4 : ℕ) : ℤ), -((1 : ℕ) : ℤ)])}
    (hα : α.IsGen) (y : (T ⊗ A).left) (J) (hJ : Good L y J) :
    thetaVal θ y J (snd T A) * (thetaVal θ y J ((fst T A ≫ θ.pt) * snd T A) *
      val α (lift (fst T A) ((fst T A ≫ θ.pt) * ((fst T A ≫ θ.pt) * snd T A))).left y J) =
      val σ ((fst T A ≫ θ.pt) ^ 2).left y J * val α (lift (fst T A) (snd T A)).left y J := by
  have := hA.comm
  have hX : (fst T A ≫ θ.pt) ^ 4 = 1 := by rw [← MonObj.comp_pow, hx, MonObj.comp_one]
  have s₁ : val σ (1 : T ⊗ A ⟶ A).left y J = 1 :=
    (val_pull hJ σ (eSec A) (T ⊗ A).hom).symm.trans ((val_corr hJ hσ₁ _).trans (val_one _))
  have sy := (val_symGen θ nu rfl hJ 1).symm.trans ((val_corr hJ hs _).trans (val_one _))
  rw [hnu y J hJ, hnu y J hJ, s₁, _root_.mul_one, inv_one] at sy
  have gθ := fun w => grep_two (L := L) (n := translPt A θ.pt) (a := ((4 : ℕ) : ℤ)) (b := -((4 : ℕ) : ℤ))
    (α := θ.φ) θ.isGen w
  have cl : ∀ m w : T ⊗ A ⟶ A, lift (fst T A) m ≫ lift (fst T A) w = lift (fst T A) (lift (fst T A) m ≫ w) :=
    fun m w => by rw [comp_lift, lift_fst]
  have H₁ := indep hG hA hL (((gθ (snd T A)).mul ((gθ ((fst T A ≫ θ.pt) * snd T A)).mul
    (grep_two hα ((fst T A ≫ θ.pt) * ((fst T A ≫ θ.pt) * snd T A))))).mul (grep_two hα (snd T A)).inv)
    (fun U _ h => by
      have e : ((fst T A ≫ θ.pt) * ((fst T A ≫ θ.pt) * snd T A)) ^ 2 = snd T A ^ 2 := by
        rw [← _root_.mul_assoc, mul_pow, ← sq, ← pow_mul, hX, _root_.one_mul]
      simp only [lift_translPt, MonObj.comp_pow, lift_snd, e]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_one]
      module) (snd T A) (fst T A ≫ θ.pt)⁻¹ y J hJ
  have H₂ := indep hG hA hL ((((grep_sigma hσ (snd T A)⁻¹).pow 4).inv.mul ((grep_two hα (snd T A)).mul
    (grep_two hα (snd T A)⁻¹).inv)).mul (grep_sigma hσ (snd T A ^ 2)).inv)
    (fun U _ h => by
      simp only [MonObj.comp_pow, lift_snd, inv_inv, inv_pow]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow, ofMul_one]
      module) (fst T A ≫ θ.pt) 1 y J hJ
  simp only [cl, MonObj.comp_mul, MonObj.comp_pow, GrpObj.comp_inv, lift_snd, lift_fst_assoc, mul_inv_cancel, _root_.mul_one,
    inv_one, one_pow, s₁] at H₁ H₂
  replace H₁ := congrArg Additive.ofMul H₁
  replace H₂ := congrArg Additive.ofMul H₂
  replace sy := congrArg Additive.ofMul sy
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, ofMul_pow, ofMul_one, thetaVal] at H₁ H₂ sy ⊢
  linear_combination (norm := module) H₁ + H₂ + sy

theorem exists_symmetric_square : ∀ (R : Type) [CommRing R] [IsDomain R] (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (x : TFK (R := R) F ⟶ A.A), x ^ 4 = 1 → ∀ σ : LB.Gen (LB.LinComb A.L (K := Fin 2) ![(ι[A.A]).left, 𝟙 A.A.left] ![1, -1]), σ.IsGen → LB.Gen.Corr A.L _ _ _ _ (LB.pullGen A.L _ _ σ (eSec A.A)) (LB.oneGen A.L) → ∃ θ : ThetaGrp A.A A.L ((4 : ℕ) : ℤ) (TFK (R := R) F), θ.pt = x ∧ (∃ nu : LB.Gen (negLB A.A A.L ((4 : ℕ) : ℤ) (TFK (R := R) F)), nu.IsGen ∧ LB.Gen.Corr A.L _ _ _ _ (symGen A.A A.L ((4 : ℕ) : ℤ) θ nu) (LB.oneGen A.L)) ∧ ∃ c : F, (∀ z J, Good A.L z J → (val σ (x ^ 2).left z J).val = @id ((TFK (R := R) F).left.presheaf.stalk z) (cst (R := R) F z c)) ∧ ∀ (ψ : TFK (R := R) F ⊗ A.A ⟶ TFK (R := R) F ⊗ A.A) (m : TFK (R := R) F ⊗ A.A ⟶ A.A) (hm : ψ ≫ snd _ _ = m), ψ ≫ fst _ _ = fst _ _ → m = snd _ _ ^ 2 → ∀ α : LB.Gen (LB.LinComb A.L (K := Fin 2) ![(snd (TFK (R := R) F) A.A).left, m.left] ![((4 : ℕ) : ℤ), -((1 : ℕ) : ℤ)]), α.IsGen → ∀ (t : SecA A F 1) (t₁ t₂ t₃ : SecA A F 4), IsTwistPull A.A A.L ψ m hm ((4 : ℕ) : ℤ) ((1 : ℕ) : ℤ) α t t₁ → IsActOf A.A A.L ((4 : ℕ) : ℤ) θ t₁ t₂ → IsActOf A.A A.L ((4 : ℕ) : ℤ) θ t₂ t₃ → ∀ j, t₃.f j = liftFun A.A _ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom c) * t₁.f j := by
  intro R _ _ A F _ _ _ x hx σ hσ hσ₁
  have hG : GlobalFnsSt := GlobalTheory.firstFiveLaws.1.globalFns
  have hL := A.isLB
  have := A.isAb.comm
  obtain ⟨θ₀, h₀⟩ := GlobalTheory.ThetaLift.exists_theta_of_field (FractionRing R) A (TFK (R := R) F) F (Iso.refl _) 4 x hx
  obtain ⟨nu, hnu, vn⟩ := ((grep_sigma hσ (snd (TFK (R := R) F) A.A)).pow 4).inv.out hL
    ![(snd (TFK (R := R) F) A.A).left, (snd (TFK (R := R) F) A.A ≫ ι[A.A]).left] ![((4 : ℕ) : ℤ), -((4 : ℕ) : ℤ)]
    (fun U _ h => by
      rw [Fin.prod_univ_two]
      show _ = h (snd (TFK (R := R) F) A.A).left ^ ((4 : ℕ) : ℤ) * h ((snd (TFK (R := R) F) A.A)⁻¹).left ^ (-((4 : ℕ) : ℤ))
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow]
      module)
  have vn' : ∀ y J, Good A.L y J → ∀ m, negVal (L := A.L) (k := ((4 : ℕ) : ℤ)) nu y J m = (val σ m.left y J ^ 4)⁻¹ :=
    fun y J hJ m => (vn _ _ y J hJ).trans (by beta_reduce; rw [lift_snd])
  obtain ⟨a, ha⟩ := exists_symConst hG A.isAb hL θ₀ (nu := nu) hnu
  obtain ⟨b, hb⟩ : ∃ b : Γ((TFK (R := R) F).left, ⊤)ˣ, a = b ^ 2 := by
    let e := (Scheme.ΓSpecIso (CommRingCat.of F)).commRingCatIsoToRingEquiv
    obtain ⟨r, hr⟩ := IsAlgClosed.exists_pow_nat_eq (k := F) (e a.val) two_pos
    have e₁ : (e.symm r) ^ 2 = a.val := by rw [← map_pow, hr, RingEquiv.symm_apply_apply]
    have u : IsUnit (e.symm r) := (isUnit_pow_iff two_ne_zero).1 (e₁ ▸ a.isUnit)
    exact ⟨u.unit, Units.ext e₁.symm⟩
  obtain ⟨θ, hpt, hv⟩ := exists_scale hL θ₀ b⁻¹
  have hθ : θ.pt = x := hpt.trans h₀
  have hs : LB.Gen.Corr A.L _ _ _ _ (symGen A.A A.L ((4 : ℕ) : ℤ) θ nu) (LB.oneGen A.L) := corr_of_val hL fun y J hJ => by
    have e₁ := (val_symGen θ₀ nu h₀ hJ (snd _ _)).symm.trans (ha _ y J hJ)
    rw [val_one, id_eq_lift, val_symGen θ nu hθ hJ, hv y J hJ, hv y J hJ, map_inv]
    rw [hb, map_pow] at e₁
    apply Additive.ofMul.injective
    replace e₁ := congrArg Additive.ofMul e₁
    simp only [ofMul_mul, ofMul_pow, ofMul_inv, ofMul_one] at e₁ ⊢
    linear_combination (norm := module) e₁
  obtain ⟨K, _, φ, ε, s, hs', p, vs⟩ := grep_sigma hσ (x ^ 2)
  obtain ⟨c, hc⟩ := H1.exists_const A.L hL (𝟙 _) (fun v => ⟨v, by simp⟩) s hs' (fun U _ h => (p U h).trans (by
    have e : (x ^ 2)⁻¹ = x ^ 2 := by rw [inv_eq_iff_mul_eq_one, ← pow_add]; exact hx
    beta_reduce
    rw [e, mul_inv_cancel]))
  have ec : (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom ((Scheme.ΓSpecIso (CommRingCat.of F)).hom.hom c) = c :=
    (Scheme.ΓSpecIso (CommRingCat.of F)).hom_inv_id_apply c
  refine ⟨θ, hθ, ⟨nu, hnu, hs⟩, (Scheme.ΓSpecIso (CommRingCat.of F)).hom.hom c, fun z J hJ => ?_, ?_⟩
  · have e₁ := vs _ (𝟙 _) z J hJ
    have e₂ := hc _ (𝟙 _) z J hJ
    beta_reduce at e₁
    rw [Category.id_comp, Over.id_left] at e₁
    rw [Category.id_comp] at e₂
    exact (congrArg Units.val e₁).symm.trans (e₂.trans (congrArg (gs _ z ⊤) ec.symm))
  · rintro ψ m hm hψ rfl α hα t t₁ t₂ t₃ h₁ h₂ h₃ j
    rw [ec]
    refine eq_liftFun_mul hL t₁ t₃ c (fun y J hJ => ?_) j
    subst hθ
    have key := square_val hG A.isAb hL hσ hσ₁ θ hx nu vn' hs hα y J hJ
    have e₁ := vs _ (fst _ A.A) y J hJ
    have e₂ := hc _ (fst _ A.A).left y J hJ
    beta_reduce at e₁
    rw [MonObj.comp_pow] at e₁
    rw [Category.comp_id, e₁] at e₂
    have hX : (fst (TFK (R := R) F) A.A ≫ θ.pt) ^ 4 = 1 := by rw [← MonObj.comp_pow, hx, MonObj.comp_one]
    have eψ : lift (fst (TFK (R := R) F) A.A) ((fst _ _ ≫ θ.pt) * ((fst _ _ ≫ θ.pt) * snd _ _)) ≫ ψ =
        lift (fst _ _) (snd _ _) ≫ ψ := by
      refine CartesianMonoidalCategory.hom_ext _ _ ?_ ?_
      · rw [Category.assoc, Category.assoc, hψ, lift_fst, lift_fst]
      · rw [Category.assoc, Category.assoc, hm, MonObj.comp_pow, MonObj.comp_pow, lift_snd, lift_snd,
          ← _root_.mul_assoc, mul_pow, ← sq, ← pow_mul, hX, _root_.one_mul]
    rw [← e₂, id_eq_lift, ThetaLin.sval_of_isTwistPull A.A h₃ _ y hJ, ThetaLin.sval_of_isTwistPull A.A h₂ _ y hJ,
      ThetaLin.sval_of_isTwistPull A.A h₁ _ y hJ, ThetaLin.sval_of_isTwistPull A.A h₁ _ y hJ]
    simp only [← Over.comp_left]
    rw [lift_translT, lift_translT, eψ]
    have alg : ∀ {M : Type} [CommMonoid M] (a b c d e : Mˣ) (w : M), a * (b * c) = d * e →
        a.val * (b.val * (c.val * w)) = d.val * (e.val * w) := fun a b c d e w h => by
      have h' := congrArg (fun u => Units.val u * w) h
      simpa only [Units.val_mul, _root_.mul_assoc] using h'
    exact alg _ _ _ _ _ _ key

end GlobalTheory.ThetaSquare

end
end

section

open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology

namespace GlobalTheory.CMModel

theorem natCast_notMem_pow_three_of_quadratic (p : ℕ) (K : Type) [Field K] [NumberField K]
    [Algebra K ℂ] (h2 : Module.finrank ℚ K = 2) (x : K) (hx : x ^ 2 = -(p : K))
    (L₀ : PeriodPair) [NumberField ℚ⟮(latticeCurve L₀).j⟯]
    (w : HeightOneSpectrum (𝓞 ℚ⟮(latticeCurve L₀).j⟯)) (hp : p.Prime)
    (hL : IsIntegersLattice p L₀) : (p : 𝓞 ℚ⟮(latticeCurve L₀).j⟯) ∉ w.asIdeal ^ 3 := by
  intro hw
  have := isTotallyComplex_of_sq_eq_neg hp.pos hx
  obtain ⟨⟨⟨hfin, -, hun⟩, -⟩, -⟩ :=
    GlobalTheory.Laid.hcfj_holds K h2 L₀ ((isIntegersLattice_iff hp.pos h2 hx L₀).mp hL)
  have : NumberField K⟮(latticeCurve L₀).j⟯ := NumberField.of_module_finite K _
  have hle : ℚ⟮(latticeCurve L₀).j⟯ ≤
      (K⟮(latticeCurve L₀).j⟯.toSubfield.toIntermediateField fun q =>
        SubfieldClass.ratCast_mem _ q) :=
    IntermediateField.adjoin_simple_le_iff.mpr (IntermediateField.mem_adjoin_simple_self K _)
  let f : ℚ⟮(latticeCurve L₀).j⟯ →+* K⟮(latticeCurve L₀).j⟯ :=
    RingHom.codRestrict (algebraMap ℚ⟮(latticeCurve L₀).j⟯ ℂ) K⟮(latticeCurve L₀).j⟯
      fun z => hle z.2
  obtain ⟨P, hP, hP0, hPp⟩ := GlobalTheory.T.exists_prime_natCast_mem_pow_of_ringHom' _ _ f w p 3 hw
  exact GlobalTheory.T.natPrime_not_mem_prime_cube_of_isUnramifiedAt p K K⟮(latticeCurve L₀).j⟯ x P hp h2 hx hP0 (hun P hP0) hPp

theorem natCast_notMem_pow_three_adjoin_j : ∀ (p : ℕ) (L₀ : PeriodPair)
    [NumberField ℚ⟮(latticeCurve L₀).j⟯] (w : HeightOneSpectrum (𝓞 ℚ⟮(latticeCurve L₀).j⟯)),
    p.Prime → IsIntegersLattice p L₀ → (p : 𝓞 ℚ⟮(latticeCurve L₀).j⟯) ∉ w.asIdeal ^ 3 := by
  intro p L₀ _ w hp hL
  have hint : IsIntegral ℚ (sqrtNegNat p) :=
    IsIntegral.of_pow two_pos (by rw [sqrtNegNat_sq]; exact (isIntegral_natCast p).neg)
  have : FiniteDimensional ℚ ℚ⟮sqrtNegNat p⟯ := IntermediateField.adjoin.finiteDimensional hint
  have : NumberField ℚ⟮sqrtNegNat p⟯ := NumberField.of_module_finite ℚ _
  have hx : (IntermediateField.AdjoinSimple.gen ℚ (sqrtNegNat p)) ^ 2 =
      -(p : ℚ⟮sqrtNegNat p⟯) := Subtype.ext (by simpa using sqrtNegNat_sq p)
  have := isTotallyComplex_of_sq_eq_neg hp.pos hx
  have h2 : Module.finrank ℚ ℚ⟮sqrtNegNat p⟯ = 2 := by
    have hle : Module.finrank ℚ ℚ⟮sqrtNegNat p⟯ ≤ 2 := by
      rw [IntermediateField.adjoin.finrank hint]
      have hm : (Polynomial.X ^ 2 + Polynomial.C (p : ℚ)).Monic :=
        Polynomial.monic_X_pow_add_C _ two_ne_zero
      have := Polynomial.natDegree_le_of_dvd (minpoly.dvd ℚ (sqrtNegNat p)
        (p := Polynomial.X ^ 2 + Polynomial.C (p : ℚ)) (by simp [sqrtNegNat_sq])) hm.ne_zero
      rwa [Polynomial.natDegree_X_pow_add_C] at this
    have h1 := IsTotallyComplex.finrank ℚ⟮sqrtNegNat p⟯
    have h3 : 0 < Module.finrank ℚ ℚ⟮sqrtNegNat p⟯ := Module.finrank_pos
    omega
  exact natCast_notMem_pow_three_of_quadratic p _ h2 _ hx L₀ w hp hL

end GlobalTheory.CMModel
end

section

open NumberField IsDedekindDomain GlobalTheory.CMVal

theorem _root_.GlobalTheory.T.norm_completedHeckeL_CM_one_le_phragmenLindelof : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] (φ : I → E →+* ℂ),
    GlobalTheory.Published.HeckeFunctionalEquationAbs → GlobalTheory.IndefiniteRowSideFullHecke.CompletedLStripBounds.CompletedLBoundedInStrips → IsCMType φ →
    ∀ (χ : HChar E) (m : I → ℤ) (a : HeightOneSpectrum (𝓞 E) →₀ ℕ) (Λ : ℂ → ℂ),
    IsUnitary χ → TrivOnF χ → HasInf χ φ m → (∀ i, 0 < m i) → (∀ v, ExpAt χ v (a v)) → IsHeckeL χ Λ →
    ‖Λ 1‖ ≤ ‖riemannZeta (3 / 2)‖ ^ Module.finrank ℚ E *
      ((((discr E).natAbs * a.prod fun v k => Ideal.absNorm v.asIdeal ^ k : ℕ) : ℝ)) * ∏ i, (1 + (m i : ℝ)) := by
  first | exact @GlobalTheory.HeckeLOneBound.norm_heckeL_one_le | exact GlobalTheory.HeckeLOneBound.norm_heckeL_one_le | (intros; apply GlobalTheory.HeckeLOneBound.norm_heckeL_one_le <;> assumption)
end

section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet
open scoped TensorProduct

namespace GlobalTheory.TieStd

theorem exists_coeff_of_mem_colSpan {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {n r s : ℕ} (hs : s ≤ r) (X : Matrix (Fin n) (Fin r) E) (I : Set (Fin r)) (P : Fin s → Prop)
    (hI : ∀ i ∈ I, ∃ j, Fin.castLE hs j = i ∧ P j) {y : Fin n → AF F ⊗[F] E}
    (hy : y ∈ GlobalTheory.StdPar.colSpan F X I) :
    ∃ a : Fin s → AF F ⊗[F] E, (∀ j, ¬ P j → a j = 0) ∧ adMat F (X.submatrix id (Fin.castLE hs)) *ᵥ a = y := by
  first
  | exact @_root_.GlobalTheory.ColumnSpanCoefficients.exists_coeff_of_mem_colSpan
  | exact _root_.GlobalTheory.ColumnSpanCoefficients.exists_coeff_of_mem_colSpan
  | (apply _root_.GlobalTheory.ColumnSpanCoefficients.exists_coeff_of_mem_colSpan <;> assumption)
  | (intros; apply _root_.GlobalTheory.ColumnSpanCoefficients.exists_coeff_of_mem_colSpan <;> assumption)
  | (intros; apply @_root_.GlobalTheory.ColumnSpanCoefficients.exists_coeff_of_mem_colSpan <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.ColumnSpanCoefficients.exists_coeff_of_mem_colSpan ..)

theorem unip_le_unipFlag : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y → ∀ (S : Finset (Fin r)) (s : ℕ) (hs : s ≤ r), (∀ i : Fin r, i.val < s ↔ ∃ k ∈ S, i ≤ k) → ∀ d : Fin s → ℕ, (∀ i, d i = (S.filter (· < Fin.castLE hs i)).card) → GlobalTheory.StdPar.unip σ J X S ≤ GlobalTheory.UAut.unipFlag σ J (X.submatrix id (Fin.castLE hs)) d := by
  intro F E _ _ _ _ _ σ _ n J _ r X Y _ S s hs hS d hd g hg
  refine Subgroup.subset_closure (?_ : g ∈ GlobalTheory.UAut.unipSet σ J (X.submatrix id (Fin.castLE hs)) d)
  have hlt : ∀ i : Fin r, (∃ k ∈ S, i ≤ k) → ∃ j : Fin s, Fin.castLE hs j = i :=
    fun i h => ⟨⟨i.val, (hS i).2 h⟩, rfl⟩
  refine ⟨fun i => ?_, fun x hx => ?_⟩
  · have h1 := (Subgroup.mem_iInf.1 hg.1 (Fin.castLE hs i)).2 _ (Submodule.subset_span ⟨Fin.castLE hs i, rfl, rfl⟩)
    obtain ⟨a, ha, e⟩ := exists_coeff_of_mem_colSpan hs X {i' | ∃ k ∈ S, i' ≤ k ∧ k < Fin.castLE hs i} (fun j => d j < d i) (fun i' ⟨k, hk, h1, h2⟩ => by
      obtain ⟨j, rfl⟩ := hlt i' ⟨k, hk, h1⟩
      exact ⟨j, rfl, (depth_lt_iff S s hs d hd i j).2 ⟨k, hk, h1, h2⟩⟩) h1
    refine ⟨a, fun j hj => ha j (not_lt.2 hj), ?_⟩
    rw [sub_mulVec, one_mulVec, e]
    rfl
  · have hp : (fun i => inclR (F := F) (AF F) (x i)) ∈ GlobalTheory.StdPar.colPerp σ J X {i | ∃ k ∈ S, i ≤ k} := by
      simp only [GlobalTheory.StdPar.colPerp, Submodule.mem_iInf, LinearMap.mem_ker]
      intro i hi
      obtain ⟨j, rfl⟩ := hlt i hi
      refine (RingHom.map_mulVec (inclR (F := F) (AF F)) _ x (Fin.castLE hs j)).symm.trans ?_
      rw [show ((Formalism.UG.cT (σ : E →+* E) X * J) *ᵥ x) (Fin.castLE hs j) =
        ((Formalism.UG.cT (σ : E →+* E) (X.submatrix id (Fin.castLE hs)) * J) *ᵥ x) j from rfl, hx]
      exact map_zero _
    obtain ⟨a, -, e⟩ := exists_coeff_of_mem_colSpan hs X _ (fun _ => True)
      (fun i' h => let ⟨j, hj⟩ := hlt i' h; ⟨j, hj, trivial⟩) (hg.2.2 _ hp)
    exact ⟨a, by rw [sub_mulVec, one_mulVec, e]⟩

end GlobalTheory.TieStd
end

section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.ThK.SquareIntegrability

theorem _root_.GlobalTheory.T.standardParabolicUnipotent_le_flagUnipotentRadical : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y →
      ∀ (S : Finset (Fin r)) (m : Fin r), m ∈ S → (∀ k ∈ S, k ≤ m) →
        GlobalTheory.StdPar.unip σ J X S ≤ GlobalTheory.UAut.unipFlag σ J (GlobalTheory.StdPar.initCols X m) (fun i => (S.filter fun k => k.val < i.val).card) := by
  first | exact @GlobalTheory.StdPar.unip_le_unipFlag_initCols | exact GlobalTheory.StdPar.unip_le_unipFlag_initCols | (intros; apply GlobalTheory.StdPar.unip_le_unipFlag_initCols <;> assumption)
end

section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet
open scoped TensorProduct

theorem _root_.GlobalTheory.T.gradedIsotropicFlagLevi_le_leviSubgroup : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y → ∀ (S : Finset (Fin r)) (s : ℕ) (hs : s ≤ r), (∀ i : Fin r, i.val < s ↔ ∃ k ∈ S, i ≤ k) → ∀ d : Fin s → ℕ, (∀ i, d i = (S.filter (· < Fin.castLE hs i)).card) → GlobalTheory.UAut.leviFlag σ J (X.submatrix id (Fin.castLE hs)) (Y.submatrix id (Fin.castLE hs)) d ≤ GlobalTheory.StdPar.levi σ J X Y S := by
  first | exact @GlobalTheory.TieStd.leviFlag_le_levi | exact GlobalTheory.TieStd.leviFlag_le_levi | (intros; apply GlobalTheory.TieStd.leviFlag_le_levi <;> assumption)
end
