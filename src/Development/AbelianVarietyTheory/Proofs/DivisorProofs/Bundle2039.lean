module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2001
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormEulerPolySubOneLe
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsValCharTwist
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle181
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle110
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1984
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle313
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeCharacterFiniteOrderValuesInField
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle144
import Formalism.LocalToGlobal.UnitaryNorms.CharUniq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle451
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped ComplexConjugate Matrix NNReal
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (sZero)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP (Pair Unram SphFun openOff integrand wcoef rcoef up)

namespace GlobalTheory.BottomIPData

theorem dSfun_bottom_ne_zero : GBig fun {D} T Lc _ G _ _ _ _ => ∀ (W : G.Weil) (i j : Fin D.R.m) (A A' WW : HSp D) (X : Tri T A A' WW),
  IsBottomTri W i j X → ∀ t : T, GlobalTheory.LFun.dSfun D.host.E ((GlobalTheory.BottomIPData.sfB G t : Finset (FinPl D)) : Set (FinPl D)) (GlobalTheory.Grid.neg A).rank WW.rank ((A'.rank : ℂ) / 2) ≠ 0 := by
  refine ⟨0, fun ε CF _ => ⟨0, 0, fun C _ D large₂ _ _ _ T Lc μ₀ _ G => ?_⟩⟩
  intro W i j A A' WW X h t
  apply GlobalTheory.LFun.dSfun_ne_zero_of_re_pos
  have h2 := (GlobalTheory.FunObj.SqNum.Model.bot_ranks (D := D) i j).1
  have hp : (0 : ℝ) < A'.rank := by rw [h.rank']; exact_mod_cast (by omega : 0 < SqNum.botSmall D i j)
  rw [show ((A'.rank : ℂ) / 2) = (((A'.rank : ℝ) / 2 : ℝ) : ℂ) by push_cast; ring, Complex.ofReal_re]
  positivity

end GlobalTheory.BottomIPData
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SqStepBig

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Geo Chars)

variable {D : D7} {T : Type} {Lc : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts}

def EmbCM (Bs : Base D.host.F D.host.E) : Prop := ∀ w, ∃ τ, ∀ x, (Bs.emb w).1 x = starRingEnd ℂ (tauE D τ x)

def OverH (c : D.host.E) (A : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E)) {n : ℕ}
    (V : Spc D.host.F D.host.E n) : Prop :=
  ∃ h : A.rank = n, V.J = c • Matrix.reindex (finCongr h) (finCongr h) A.gram ∧
    ∀ y, y ∈ V.L ↔ (fun i => star (y (finCongr h i))) ∈ Λ

def OverW (WW : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin WW.rank → D.host.E)) {d : ℕ} (Z : Spc D.host.F D.host.E d) : Prop :=
  ∃ h : WW.rank = d, Z.J = D.host.xi0 • Matrix.reindex (finCongr h) (finCongr h) WW.gram.transpose ∧
    ∀ y, y ∈ Z.L ↔ (fun i => y (finCongr h i)) ∈ GlobalTheory.SkewLat.scLat D.host.AA Λ

def Over {A A' WW : HSp D} (X : Tri T A A' WW) {a a' : ℕ} (Γ : Geo D.sp.cm.sig a a') : Prop :=
  OverH 1 A X.rA.Λ Γ.V ∧ OverH (-1) A' X.rA'.Λ Γ.V' ∧ OverW WW X.rW.Λ Γ.W

def Fit (G : GridData Lc sc) (W : G.Weil) (i j : Fin D.R.m) (t μ₀ : T) (Bs : Base D.host.F D.host.E) (a a' : ℕ) : Prop :=
  GlobalTheory.SqStep.BaseFits G W i j t Bs ∧ Bs.IsGood D.sp.cm.sig ∧ EmbCM Bs ∧ (GlobalTheory.SqStep.chs G i j t).IsGood Bs a a' ∧
    (GlobalTheory.SqStep.chs G i j μ₀).IsGood Bs a a' ∧ ∀ w, ((a + a' : ℕ) : ℤ) < Bs.mα w - Bs.mβ w

theorem OverH.eq {c : D.host.E} {A : HSp D} {Λ : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E)} {n : ℕ}
    {V V₂ : Spc D.host.F D.host.E n} (h : OverH c A Λ V) (h₂ : OverH c A Λ V₂) : V₂.J = V.J ∧ V₂.L = V.L := by
  obtain ⟨e, hJ, hL⟩ := h
  obtain ⟨e₂, hJ₂, hL₂⟩ := h₂
  exact ⟨hJ₂.trans hJ.symm, Submodule.ext fun y => (hL₂ y).trans (hL y).symm⟩

theorem OverW.eq {WW : HSp D} {Λ : Submodule (𝓞 D.host.E) (Fin WW.rank → D.host.E)} {d : ℕ}
    {Z Z₂ : Spc D.host.F D.host.E d} (h : OverW WW Λ Z) (h₂ : OverW WW Λ Z₂) : Z₂.J = Z.J ∧ Z₂.L = Z.L := by
  obtain ⟨e, hJ, hL⟩ := h
  obtain ⟨e₂, hJ₂, hL₂⟩ := h₂
  exact ⟨hJ₂.trans hJ.symm, Submodule.ext fun y => (hL₂ y).trans (hL y).symm⟩

theorem Fit.down_left {G : GridData Lc sc} {W : G.Weil} {i j : Fin D.R.m} {t μ₀ : T} {Bs : Base D.host.F D.host.E} {b a' : ℕ}
    (h : Fit G W i j t μ₀ Bs (b + 2) a') : Fit G W i j t μ₀ Bs b a' := by
  obtain ⟨h1, h2, h3, c, c₀, hk⟩ := h
  refine ⟨h1, h2, h3, ⟨c.heckeα, c.heckeβ, c.resα, fun x => ?_, c.expα, c.expβ, c.disj, c.sub, c.ram, c.unrα, c.unrβ, c.good⟩,
    ⟨c₀.heckeα, c₀.heckeβ, c₀.resα, fun x => ?_, c₀.expα, c₀.expβ, c₀.disj, c₀.sub, c₀.ram, c₀.unrα, c₀.unrβ, c₀.good⟩, fun w => ?_⟩
  · rw [c.resβ x]; simp [pow_add]
  · rw [c₀.resβ x]; simp [pow_add]
  · have := hk w
    push_cast at this ⊢
    omega

theorem Fit.down_right {G : GridData Lc sc} {W : G.Weil} {i j : Fin D.R.m} {t μ₀ : T} {Bs : Base D.host.F D.host.E} {a b : ℕ}
    (h : Fit G W i j t μ₀ Bs a (b + 2)) : Fit G W i j t μ₀ Bs a b := by
  obtain ⟨h1, h2, h3, c, c₀, hk⟩ := h
  refine ⟨h1, h2, h3, ⟨c.heckeα, c.heckeβ, fun x => ?_, c.resβ, c.expα, c.expβ, c.disj, c.sub, c.ram, c.unrα, c.unrβ, c.good⟩,
    ⟨c₀.heckeα, c₀.heckeβ, fun x => ?_, c₀.resβ, c₀.expα, c₀.expβ, c₀.disj, c₀.sub, c₀.ram, c₀.unrα, c₀.unrβ, c₀.good⟩, fun w => ?_⟩
  · rw [c.resα x]; simp [pow_add]
  · rw [c₀.resα x]; simp [pow_add]
  · have := hk w
    push_cast at this ⊢
    omega

end GlobalTheory.SqStepBig

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

private theorem chrEq_pow' {D : D7} {c : (AE D)ˣ →* Circle} {χ : HChar D.host.E} (h : ChrEq c χ) (a : ℕ) :
    ChrEq (c ^ a) (χ ^ a) := by
  refine ⟨⟨?_, fun x => ?_⟩, fun P e he k x hx => ?_⟩
  · have : ((c ^ a : (AE D)ˣ →* Circle) : (AE D)ˣ → Circle) = fun x => c x ^ a := by
      funext x; simp
    rw [this]
    exact h.1.1.pow a
  · have h1 := h.1.2 x
    simp only [MonoidHom.pow_apply, h1, one_pow]
  · have hp : (χ ^ a).locK P k = χ.locK P k ^ a := by
      have : ∀ x, (χ ^ a).1 x = χ.1 x ^ a := fun x => by rw [SubgroupClass.coe_pow, MonoidHom.pow_apply]
      exact this _
    rw [MonoidHom.pow_apply, hp, Units.val_pow_eq_pow_val, ← h.2 P e he k x hx]
    exact map_pow Circle.coeHom _ _

private theorem exists_prime_power_pow_eq_one {D : D7} {c : (AE D)ˣ →* Circle} {χ : HChar D.host.E} (h : ChrEq c χ) {n : ℕ}
    (hn : χ.OrderDvd n) : c ^ n = 1 := by
  have h1 := chrEq_pow' h n
  rw [show χ ^ n = 1 from hn] at h1
  exact MonoidHom.ext fun x => GlobalTheory.ChrEqUnique.eq_one_of_chrEq h1 x

theorem _root_.GlobalTheory.T.squareNu_ratio_values_roots_of_unity : GBig fun {D} T _ _ G μ₀ _ _ _ => ∀ (W : G.Weil) (S : GridChoice W Set.univ), NumbersIn D.what₂.embLL S μ₀ →
    ∀ (i j : Fin D.R.m) (t : T) (k : (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := D.host.F) (E := D.host.E))ˣ), ∃ ζ : D.what₂.LL, GlobalTheory.Square.IsAwayUnit (Qn G t) ζ ∧
      (((GlobalTheory.SqStep.chs G i j t).ν k / (GlobalTheory.SqStep.chs G i j μ₀).ν k : Circle) : ℂ) = D.what₂.embLL ζ := by
  refine ⟨0, fun _ _ _ => ⟨0, 0, fun _ _ D _ _ _ _ T Lc μ₀ hL G W S hN i j t k => ?_⟩⟩
  obtain ⟨n, hn, ho⟩ := hL.xi_fin t
  have hc1 : Lc.xi μ₀ k = 1 := GlobalTheory.ChrEqUnique.eq_one_of_chrEq (hL.xi_base ▸ hL.xi μ₀) k
  have e : (GlobalTheory.SqStep.chs G i j t).ν k / (GlobalTheory.SqStep.chs G i j μ₀).ν k = Lc.xi t k := by
    have key : ∀ {Γ : Type} [CommGroup Γ] (a x y e c : Γ), y = 1 → (a * x * e / (c * e)) / (a * y * e / (c * e)) = x := by
      intro Γ _ a x y e c hy
      subst hy
      rw [mul_one, div_div_div_cancel_right, mul_div_mul_right_eq_div, mul_div_cancel_left]
    exact key (Lc.mu0 ((j : ℕ) + 1) k) (Lc.xi t k) (Lc.xi μ₀ k) ((Lc.eta ^ (rankV D i j % 2)) k) (G.ch.chi (D.R.m - i) k) hc1
  obtain ⟨y, hy⟩ := GlobalTheory.Adopt.heckeCharacter_finiteOrder_values_in_field D (Lc.xi t) (Lc.xiH t) n _ D.what₂.embLL (hL.xi t) hn ho ((hN.chars.xi t).valuesIn) k
  have h1 : ((Lc.xi t k : Circle) : ℂ) ^ n = 1 := by
    have := DFunLike.congr_fun (exists_prime_power_pow_eq_one (hL.xi t) ho) k
    rw [MonoidHom.pow_apply, MonoidHom.one_apply] at this
    exact (map_pow Circle.coeHom _ _).symm.trans (congrArg _ this)
  have hyn : (y : D.what₂.LL) ^ n = 1 := D.what₂.embLL.injective (by rw [map_pow, hy, h1, map_one])
  exact ⟨y, GlobalTheory.KappaArith.isAwayUnit_of_pow_eq_one _ hn hyn, by rw [e, hy]⟩
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SqStepArith

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Chars Base stepFac chrW eps idealVal gauss unifAt)

theorem chrW_chs {D : D7} {T : Type} {Lc : LevCh D T} {sc : Consts} (G : GridData Lc sc) {μ₀ : T} (hL : Lc.Is μ₀)
    (i j : Fin D.R.m) (t : T) {v : HeightOneSpectrum (𝓞 D.host.F)} (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v)
    (x : (Fv D.host.F v)ˣ) :
    chrW (GlobalTheory.SqStep.chs G i j t).ν τ x = (nuH G t i j).loc (GlobalTheory.AdelicU.splitPrime τ)
      (Units.map (GlobalTheory.LFun.complMap (GlobalTheory.AdelicU.splitPrime_under τ)).toMonoidHom x) := by
  have e : (GlobalTheory.SqStep.chs G i j t).ν = G.nu t i (j + 1) := by
    show (Lc.mu t (j + 1) * Lc.eta ^ _) / (G.ch.chi _ * Lc.eta ^ _) = _
    rw [mul_div_mul_right_eq_div]
    rfl
  show GlobalTheory.LFun.locChar (GlobalTheory.SqStep.chs G i j t).ν _ _ = _
  rw [e, GlobalTheory.LFun.locChar_eq_of_chrEq (chrEq_nu G t i j hL)]

theorem eps_mul_of_condExp {F : Type} [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ) {v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)}
    (ν₀ ξ : (Fv F v)ˣ →* ℂˣ) (s : (Fv F v)ˣ) (z : ℤ)
    (h : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.condExp (ν₀ * ξ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.condExp ν₀) :
    (ν₀ s : ℂ) * eps ψ ν₀ z * gauss ψ (ν₀ * ξ) =
      (((ξ (s * unifAt v ^ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.condExp ν₀))⁻¹ : ℂˣ) : ℂ) * gauss ψ ν₀ *
        (((ν₀ * ξ) s : ℂ) * eps ψ (ν₀ * ξ) z) := by
  unfold eps
  rw [h]
  simp only [MonoidHom.mul_apply, map_mul, map_pow, Units.val_mul, Units.val_pow_eq_pow_val, mul_inv, Units.val_inv_eq_inv_val]
  have h1 : (ξ s : ℂ) ≠ 0 := Units.ne_zero _
  have h2 : (ξ (unifAt v) : ℂ) ≠ 0 := Units.ne_zero _
  field_simp
  ring

theorem chs_T_base {D : D7} {T : Type} {Lc : LevCh D T} {sc : Consts} (G : GridData Lc sc) {μ₀ : T} (hL : Lc.Is μ₀)
    (i j : Fin D.R.m) : (GlobalTheory.SqStep.chs G i j μ₀).T = G.pl.S0 := by
  classical
  have hQ : Lc.Q μ₀ = ∅ := by
    refine Finset.eq_empty_of_forall_notMem fun PP hPP => ?_
    have h := (hL.Q_ram μ₀ PP).2 (Or.inl hPP)
    apply h
    rw [hL.xi_base]
    intro x _
    rfl
  have htw : twPl G μ₀ = ∅ := by
    unfold twPl locPl
    rw [hQ, Finset.union_empty]
    exact Finset.filter_false_of_mem fun w hw h => h hw
  show G.pl.S0 ∪ (twPl G μ₀).image _ = _
  rw [htw, Finset.image_empty, Finset.union_empty]

end GlobalTheory.SqStepArith
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Chars Base stepFac chrW eps idealVal gauss unifAt PsiUnr)

namespace GlobalTheory.SqStepIdeal

open GlobalTheory.LFun

theorem val_mem {D : D7} {χ : HChar D.host.E} {n : ℕ} (h1 : χ.OrderDvd n) (h2 : LocIn D.what₂.embLL χ)
    (w : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.E)) :
    χ.val w ^ n = 1 ∧ ((χ.val w : ℂˣ) : ℂ) ∈ D.what₂.embLL.fieldRange := by
  refine ⟨?_, ?_⟩
  · have e1 : (χ.1 : _ →* ℂˣ) ^ n = 1 := by
      have := congrArg Subtype.val h1
      simpa using this
    have e2 : ∀ y, χ.1 y ^ n = 1 := fun y => by
      have := DFunLike.congr_fun e1 y
      simpa [MonoidHom.pow_apply] using this
    exact e2 _
  · obtain ⟨y, hy⟩ := h2 w (Formalism.L2.Host.atFin w (Formalism.L2.Host.unif w))
    exact ⟨y, hy⟩

theorem mulSupport_finite {E : Type} [Field E] [NumberField E] (f : IsDedekindDomain.HeightOneSpectrum (𝓞 E) → ℂˣ)
    (𝔞 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) :
    (Function.mulSupport fun w => f w ^ FractionalIdeal.count E w 𝔞).Finite := by
  refine (Filter.eventually_cofinite.1 (FractionalIdeal.finite_factors 𝔞)).subset fun w hw => ?_
  intro h
  apply hw
  simp only [h, zpow_zero]

theorem idealVal_chs_base : ∀ {D : D7} {T : Type} {Lc : LevCh D T} {sc : Consts} (G : GridData Lc sc) {μ₀ : T}, Lc.Is μ₀ →
    ∀ (W : G.Weil) (S : GridChoice W Set.univ), NumbersIn D.what₂.embLL S μ₀ → ∀ (i j : Fin D.R.m) (t : T)
    (𝔞 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E), ∃ b : D.what₂.LL, (∃ n : ℕ, 0 < n ∧ b ^ n = 1) ∧
      ((idealVal (GlobalTheory.SqStep.chs G i j μ₀).ν 𝔞 : ℂˣ) : ℂ) = D.what₂.embLL b * ((idealVal (GlobalTheory.SqStep.chs G i j t).ν 𝔞 : ℂˣ) : ℂ) := by
  intro D T Lc sc G μ₀ hL W S hN i j t 𝔞
  have e : ∀ s, (GlobalTheory.SqStep.chs G i j s).ν = G.nu s i (j + 1) := fun s => by
    show (Lc.mu s (j + 1) * Lc.eta ^ _) / (G.ch.chi _ * Lc.eta ^ _) = _
    rw [mul_div_mul_right_eq_div]
    rfl
  have hν : (GlobalTheory.SqStep.chs G i j μ₀).ν = (GlobalTheory.SqStep.chs G i j t).ν * ((Lc.xi t)⁻¹ * Lc.xi μ₀) := by
    rw [e, e]
    refine MonoidHom.ext fun x => ?_
    show Lc.mu0 (j + 1) x * Lc.xi μ₀ x / G.ch.chi (D.R.m - i) x =
      Lc.mu0 (j + 1) x * Lc.xi t x / G.ch.chi (D.R.m - i) x * ((Lc.xi t x)⁻¹ * Lc.xi μ₀ x)
    rw [div_mul_eq_mul_div, mul_assoc (Lc.mu0 (j + 1) x) (Lc.xi t x), mul_inv_cancel_left]
  obtain ⟨n, hn, hfin⟩ := hL.xi_fin t
  let c : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.E) → ℂˣ := fun w => ((Lc.xiH t).val w)⁻¹
  have hw : ∀ w, val (GlobalTheory.SqStep.chs G i j μ₀).ν w = val (GlobalTheory.SqStep.chs G i j t).ν w * c w := fun w => by
    rw [hν, val_mul, val_mul, val_inv, val_eq_of_chrEq (hL.xi t) w, val_eq_of_chrEq (hL.xi μ₀) w, hL.xi_base]
    rw [show (1 : HChar D.host.E).val w = 1 from rfl, mul_one]
  let H : Subgroup ℂˣ :=
    { carrier := {z | z ^ n = 1 ∧ (z : ℂ) ∈ D.what₂.embLL.fieldRange}
      mul_mem' := fun ha hb => ⟨by rw [mul_pow, ha.1, hb.1, one_mul], by rw [Units.val_mul]; exact mul_mem ha.2 hb.2⟩
      one_mem' := ⟨one_pow _, by rw [Units.val_one]; exact one_mem _⟩
      inv_mem' := fun ha => ⟨by rw [inv_pow, ha.1, inv_one], by rw [Units.val_inv_eq_inv_val]; exact inv_mem ha.2⟩ }
  have hc : ∀ w, c w ∈ H := fun w => H.inv_mem (val_mem hfin (hN.chars.xi t) w)
  have hprod : idealVal (GlobalTheory.SqStep.chs G i j μ₀).ν 𝔞 =
      idealVal (GlobalTheory.SqStep.chs G i j t).ν 𝔞 * ∏ᶠ w, c w ^ FractionalIdeal.count D.host.E w 𝔞 := by
    unfold idealVal
    simp_rw [hw, mul_zpow]
    exact finprod_mul_distrib (mulSupport_finite _ 𝔞) (mulSupport_finite _ 𝔞)
  have hz : ∏ᶠ w, c w ^ FractionalIdeal.count D.host.E w 𝔞 ∈ H := by
    rw [finprod_eq_prod_of_mulSupport_subset _ (s := (mulSupport_finite c 𝔞).toFinset) (by simp)]
    exact H.prod_mem fun w _ => H.zpow_mem (hc w) _
  obtain ⟨hzn, hzr⟩ := hz
  obtain ⟨b, hb⟩ := RingHom.mem_fieldRange.1 hzr
  refine ⟨b, ⟨n, hn, ?_⟩, ?_⟩
  · apply D.what₂.embLL.injective
    rw [map_pow, hb, map_one, ← Units.val_pow_eq_pow_val, hzn, Units.val_one]
  · rw [hprod, Units.val_mul, hb, mul_comm]

end GlobalTheory.SqStepIdeal
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SqStep

variable {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts}

theorem nuH_not_unrAt_above {μ₀ : T} (hL : L.Is μ₀) (G : GridData L sc) (t : T) (i j : Fin D.R.m)
    (P : HeightOneSpectrum (𝓞 D.host.E)) (hP : P.under (𝓞 D.host.F) ∈ G.pl.S0) : ¬ (nuH G t i j).UnrAt P := by
  have hm : 1 ≤ D.R.m - (i : ℕ) ∧ D.R.m - (i : ℕ) ≤ D.R.m := ⟨by omega, by omega⟩
  have e : G.ch.chiH (D.R.m - i) = L.C.mu0 j * L.xiH t * (nuH G t i j)⁻¹ := by
    rw [← div_eq_mul_inv, nuH, div_div_cancel]
  intro hn
  rcases G.pl.mem_S0_of_sum_eq.1 hP with hv | hv
  · have hmu : (L.C.mu0 j).UnrAt P := (L.C.isMu0 j).unr _ fun k hk => G.ch.basePlace_not_mem_chiGridBadPlaces (by
      have h : ((D.host.g k : ℕ) : 𝓞 D.host.F) ∈ (P.under (𝓞 D.host.F)).asIdeal := by
        show algebraMap _ (𝓞 D.host.E) _ ∈ P.asIdeal
        rw [map_natCast]; exact hk
      rw [hv] at h
      refine (S1_mem_OmF D).2 ?_
      fin_cases k
      · exact Or.inl h
      · exact Or.inr (Or.inl h))
    have hxi : (L.xiH t).UnrAt P := by
      by_contra hc
      rcases (hL.Q_ram t _).1 hc with h | ⟨PP', h, hc'⟩
      · exact G.pl.levelPlace_ne_basePlace t _ h hv
      · exact G.pl.levelPlace_ne_basePlace t PP' h ((GlobalTheory.LevelPlaces.under_eq_of_isConjPl hc').trans hv)
    apply (G.ch.lev0 _ hm.1 hm.2 _ hv).2
    rw [e]
    exact (hmu.mul hxi).mul hn.inv
  · apply (G.ch.lev1 _ hm.1 hm.2 P hv).2
    rw [e]
    exact (Formalism.L2.Host.HChar.LevelLe.mul ((L.C.isMu0 j).tame P) (hL.xi_tame t P)).mul (hn.levelLe 1).inv

theorem heckeL_eq_of_ram {K : Type} [Field K] [NumberField K] {χ : HChar K} {S : Set (HeightOneSpectrum (𝓞 K))}
    (hr : ∀ w ∈ S, ¬ χ.UnrAt w) {Λ : ℂ → ℂ} (hΛ : IsHeckeL χ Λ) {s : ℂ} (hs : 1 < s.re) :
    GlobalTheory.LFun.heckeL S χ s = Λ s := by
  have e : ({w | w ∉ S} : Set (HeightOneSpectrum (𝓞 K))).mulIndicator (GlobalTheory.CMVal.eulerFactor χ s) =
      GlobalTheory.CMVal.eulerFactor χ s :=
    Set.mulIndicator_eq_self.2 fun w hw => by
      by_contra h
      exact hw (if_neg (hr w (not_not.1 h)))
  have h := (hasProd_subtype_iff_mulIndicator (s := {w | w ∉ S}) (f := GlobalTheory.CMVal.eulerFactor χ s)).2
    (by rw [e]; exact hΛ.2 s hs)
  unfold GlobalTheory.LFun.heckeL GlobalTheory.LFun.eulerProd
  simp only [GlobalTheory.LFun.locL_heckeFam]
  exact h.tprod_eq

theorem chs_nu (G : GridData L sc) (i j : Fin D.R.m) (t : T) : (chs G i j t).ν = G.nu t i (j + 1) :=
  mul_div_mul_right_eq_div _ _ _

theorem charL_chs_eq : GBig fun {D} T _ _ G _ _ _ _ => ∀ (i j : Fin D.R.m) (t : T) (s : ℕ) (Λ : ℂ → ℂ), 2 ≤ s → IsHeckeL (nuH G t i j) Λ →
    GlobalTheory.LFun.charL (GlobalTheory.SqStep.chs G i j t).ν (G.pl.S0 : Set (HeightOneSpectrum (𝓞 D.host.F))) (s : ℂ) = Λ s := by
  refine ⟨0, fun _ _ _ => ⟨0, 0, fun _ _ D _ _ _ _ T Lc μ₀ hL G i j t s Λ hs hΛ => ?_⟩⟩
  rw [chs_nu, GlobalTheory.LFun.charL_eq_of_chrEq (chrEq_nu G t i j hL)]
  refine heckeL_eq_of_ram (fun w hw => nuH_not_unrAt_above hL G t i j w hw) hΛ ?_
  rw [Complex.natCast_re]
  exact_mod_cast (by omega : 1 < s)

end GlobalTheory.SqStep
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RowTest GlobalTheory.SumSize GlobalTheory.RowClaim
open Formalism.DivisionValues (vw lw)
open MeasureTheory ValuativeRel GlobalTheory.UnfoldLoss

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField GlobalTheory.FunObj.borelKw
  GlobalTheory.FunObj.borelSpaceKw

namespace GlobalTheory.UnfoldLoss

theorem varCount_le_of_rank_le {k : Type*} [Field k] (G : Grid k) (hs : 1 ≤ G.s) (N : ℕ)
    (hN : ∀ j < G.m, G.rank (G.m, j) ≤ N) : varCount G ≤ G.m * N ^ 2 := by
  unfold varCount
  have hterm : ∀ j : Fin (G.m - 1),
      Nat.card (StepVar (Fin (topRank G (j + 1))) (G.m - 2 - j) (Fin (topRank G j))) ≤ N ^ 2 := by
    intro j
    have hj := j.2
    refine (Finite.card_subtype_le _).trans ?_
    rw [Nat.card_prod, Nat.card_sum, Nat.card_sum]
    simp only [Nat.card_eq_fintype_card, Fintype.card_fin]
    have h1 := topRank_add hs (G := G) (j + 1)
    have h2 := topRank_add hs (G := G) j
    have h3 := hN (j + 1) (by omega)
    have h4 := hN j (by omega)
    rw [sq]
    exact Nat.mul_le_mul (by omega) (by omega)
  calc _ ≤ ∑ _j : Fin (G.m - 1), N ^ 2 := Finset.sum_le_sum fun j _ => hterm j
    _ = (G.m - 1) * N ^ 2 := by simp
    _ ≤ G.m * N ^ 2 := Nat.mul_le_mul_right _ (Nat.sub_le _ _)

theorem varCount_locGrid_le : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (t : T) (w : Pl D.host.E),
    varCount (locGrid G t w) ≤ D.R.m * bigN D ^ 2 := by
  intro D T L sc G t w
  refine varCount_le_of_rank_le (locGrid G t w) (show 1 ≤ D.R.r + 6 by omega) _ fun j hj => ?_
  change j < D.R.m at hj
  have h1 := Nat.mul_le_mul_right D.R.t hj.le
  have hr : D.R.r ≤ D.R.k + D.R.m := by
    have : D.R.r = D.R.k + D.R.m - 1 := rfl
    omega
  change D.R.r + j * D.R.t + D.R.m * (D.R.r + 6) ≤ D.R.k + D.R.m * (D.R.t + (D.R.r + 6) + 1)
  nlinarith

end GlobalTheory.UnfoldLoss
end
