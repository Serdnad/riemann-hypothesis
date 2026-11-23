module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1949
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.UnitCharTriangle
public import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1990
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1980
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsUniqueIdeleOfLinearEquivQuotientLocal
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle060
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle326
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
import Development.AbelianVarietyTheory.Proofs.HeightProofs.CmTypeRestrictRealSubfieldInfinitePlaceBijective
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsIsArchimedeanAdeleChartOfRealChart
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle033
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle079
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1997
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2001
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle333
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
import Mathlib.RingTheory.Finiteness.Lattice
public import Mathlib.RingTheory.Polynomial.IsIntegral
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.LocallyCompactUnipFlag
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Definitions.Foundations.NormEulerPolySubOneLe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1196

@[expose] public section

section

noncomputable section

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

namespace GlobalTheory.StdRead

variable {D : D7}

def toE (D : D7) : Formalism.MainNotions.StandardLatticesGL3.AE D →+* EAf D :=
  ((Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E).toAlgHom.toRingHom).comp
    (GlobalTheory.BotFormula.toAfE D).toRingHom

def matE {a : ℕ} (k : Formalism.MainNotions.StandardLatticesGL3.GA D a) : Matrix (Fin a) (Fin a) (EAf D) :=
  ((k : GL (Fin a) (Formalism.MainNotions.StandardLatticesGL3.AE D)) : Matrix (Fin a) (Fin a) (Formalism.MainNotions.StandardLatticesGL3.AE D)).map (toE D)

def IsIntE {a d : ℕ} (z : Matrix (Fin d) (Fin a) D.host.E) : Prop := ∀ i j, ∃ b : 𝓞 D.host.E, z i j = (b : D.host.E)

def Approx (𝔪 : Ideal (𝓞 D.host.E)) (o : ℕ) {a d : ℕ} (k : Formalism.MainNotions.StandardLatticesGL3.GA D a) (z : Matrix (Fin d) (Fin a) D.host.E) : Prop :=
  ∀ i j, (z.map (inc D) - (unitBlock D o a d).map (inc D) *
    (((k : GL (Fin a) (Formalism.MainNotions.StandardLatticesGL3.AE D))⁻¹ : GL (Fin a) (Formalism.MainNotions.StandardLatticesGL3.AE D)) :
      Matrix (Fin a) (Fin a) (Formalism.MainNotions.StandardLatticesGL3.AE D))) i j ∈ hatId D 𝔪

def GoodMod (e : AE D) (𝔪 : Ideal (𝓞 D.host.E)) : Prop :=
  ∃ (SS : Finset (Formalism.L2.DIV.Pl D.host.E)) (c : Formalism.L2.DIV.Pl D.host.E → ℕ), IsIdemSum e SS ∧ (∀ w ∈ SS, 0 < c w) ∧
    𝔪 = ∏ w ∈ SS, w.asIdeal ^ c w ∧ IsCoprime 𝔪 D.host.𝔟

def KillsCong (ν : (AE D)ˣ →* Circle) (𝔪 : Ideal (𝓞 D.host.E)) : Prop :=
  ∀ x y, IsFinIdl x y → IntU D y → (y : Formalism.MainNotions.StandardLatticesGL3.AE D) - 1 ∈ hatId D (𝔪 * D.host.conj • 𝔪) → ν x = 1

def cosInd (e : AE D) (𝔪 : Ideal (𝓞 D.host.E)) {S T : HSp D} {a d : ℕ} (hS : S.rank = a) (hT : T.rank = d)
    (z : Matrix (Fin d) (Fin a) D.host.E) (t : WO S T) : ℂ :=
  if IsHalf e t ∧ ∀ i j, InId 𝔪 (toEAf D (t i j) - toEAf D e * eToEAf D (z (Fin.cast hT i) (Fin.cast hS j))) then 1 else 0

def cosV (δ : ℂ) (𝔪 : Ideal (𝓞 D.host.E)) {a d : ℕ} (z : Matrix (Fin d) (Fin a) D.host.E) (G : VC D a d → ℂ) : VC D a d → ℂ :=
  ((Real.sqrt ((Ideal.absNorm 𝔪 : ℝ) ^ (a * d)) : ℂ))⁻¹ •
    Wd D (tor0 D ⊤ δ) (pt D (tor0 D ⊤ δ) δ z)
      (Iop D (tor0 D ⊤ δ) (La0 D (tor0 D ⊤ δ) a d) (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d)) G)

theorem cosV_smul (δ : ℂ) (𝔪 : Ideal (𝓞 D.host.E)) {a d : ℕ} (z : Matrix (Fin d) (Fin a) D.host.E) (c : ℂ)
    (G : VC D a d → ℂ) : cosV δ 𝔪 z (c • G) = c • cosV δ 𝔪 z G := by
  have hU : ∀ (x : VC D a d) (F : VC D a d → ℂ),
      Formalism.MainNotions.TaylorLogMetric.U D (tor0 D ⊤ δ) x (c • F) = c • Formalism.MainNotions.TaylorLogMetric.U D (tor0 D ⊤ δ) x F := fun x F => by
    funext y
    simp only [Formalism.MainNotions.TaylorLogMetric.U, Pi.smul_apply, smul_eq_mul, mul_assoc]
  have hI : ∀ A B : AddSubgroup (VC D a d), Iop D (tor0 D ⊤ δ) A B (c • G) = c • Iop D (tor0 D ⊤ δ) A B G := fun A B => by
    funext y
    simp only [Iop, hU, Pi.smul_apply, smul_eq_mul, mul_left_comm _ c]
    rw [← mul_finsum, mul_left_comm]
  funext y
  simp only [cosV, Wd, hI, hU, Pi.smul_apply, smul_eq_mul]
  ring

theorem GoodMod.ne_bot {e : AE D} {𝔪 : Ideal (𝓞 D.host.E)} (h : GoodMod e 𝔪) : 𝔪 ≠ ⊥ := by
  obtain ⟨SS, c, -, -, rfl, -⟩ := h
  exact Finset.prod_ne_zero_iff.2 fun w _ => pow_ne_zero _ w.ne_bot

theorem exists_approx {𝔪 : Ideal (𝓞 D.host.E)} (h𝔪 : 𝔪 ≠ ⊥) (o : ℕ) {a : ℕ} (d : ℕ) {k : Formalism.MainNotions.StandardLatticesGL3.GA D a}
    (hk : k ∈ intG D a) : ∃ z : Matrix (Fin d) (Fin a) D.host.E, IsIntE z ∧ Approx 𝔪 o k z := by
  have hn : 0 < Ideal.absNorm 𝔪 := Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.2 h𝔪)
  have hI : ∀ i j, ((unitBlock D o a d).map (inc D) *
      (((k : GL (Fin a) (Formalism.MainNotions.StandardLatticesGL3.AE D))⁻¹ : GL (Fin a) (Formalism.MainNotions.StandardLatticesGL3.AE D)) :
        Matrix (Fin a) (Fin a) (Formalism.MainNotions.StandardLatticesGL3.AE D))) i j ∈ OhE D := by
    intro i j
    rw [Matrix.mul_apply]
    refine sum_mem fun l _ => mul_mem ?_ (((GlobalTheory.NormSum.mem_intG k).1 hk) l j).2
    by_cases h : i.1 = o + l.1
    · simp [unitBlock, h]
    · simp [unitBlock, h]
  choose b w hw hb using fun i j => GlobalTheory.CongApprox.exists_int_approx D _ hn _ (hI i j)
  refine ⟨Matrix.of fun i j => (b i j : D.host.E), fun i j => ⟨b i j, rfl⟩, fun i j => ?_⟩
  rw [Matrix.sub_apply, hb i j]
  have e : (Matrix.of fun i j => (b i j : D.host.E)).map (inc D) i j -
      (inc D (b i j : D.host.E) + (Ideal.absNorm 𝔪 : Formalism.MainNotions.StandardLatticesGL3.AE D) * w i j) =
      inc D (((Ideal.absNorm 𝔪 : 𝓞 D.host.E)) : D.host.E) * (-w i j) := by
    simp
  rw [e]
  exact AddSubgroup.subset_closure ⟨_, Ideal.absNorm_mem 𝔪, _, neg_mem (hw i j), rfl⟩

end GlobalTheory.StdRead
end
end

section

open NumberField MeasureTheory
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 Hf lamOf area Th U)
open Formalism.MainNotions.StandardLatticesGL3 (WeilO HeckeU TT stdL pt oddE0)
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact
open GlobalTheory.BotFormula (IsFinPt)
open GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral (IsDefiniteSpace IsOpenCompactLevel)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.NormExact.InfExp

open IsDedekindDomain

theorem finAdEquiv_one_tmul (D : D7) (k : D.host.E) :
    GlobalTheory.LFun.finAdEquiv D.host.F D.host.E ((1 : Af D.host.F) ⊗ₜ[D.host.F] k) =
      GlobalTheory.BotFormula.toFinE D (Formalism.MainNotions.StandardLatticesGL3.inc D k) := by
  apply FiniteAdeleRing.ext
  intro w
  rw [GlobalTheory.LFun.finAdEquiv_tmul]
  simp only [GlobalTheory.BotFormula.toFinE, Formalism.MainNotions.StandardLatticesGL3.inc, Formalism.UG.inclE, RingEquiv.trans_apply,
    AlgEquiv.coe_toRingEquiv, AlgEquiv.coe_ringEquiv, Algebra.TensorProduct.includeLeftRingHom_apply,
    Algebra.TensorProduct.comm_tmul]
  rw [GlobalTheory.LFun.finAdEquiv_tmul]
  simp

theorem eq_inf {D : D7} {N : ℕ} (c : HeckeU D N) (e : ℤ) (χ : (AE D)ˣ →* Circle) (hχ : IsHeckeChar D χ)
    (hf : HasFinPart χ c e) (k : D.host.Eˣ) (x y : (AE D)ˣ) (hxy : Units.map (incA D).toMonoidHom k = x * y)
    (hy : infPart D (y : AE D) = 1) (hy' : finPart D (y : AE D) = (1 : Af D.host.F) ⊗ₜ[D.host.F] (k : D.host.E)) :
    ((χ x : Circle) : ℂ) =
      ∏ τ, (embT D τ (k : D.host.E) / ((‖embT D τ (k : D.host.E)‖ : ℝ) : ℂ)) ^ (e * c.n τ) := by
  have hfin : ((χ y : Circle) : ℂ) = ((c.f (Units.map (Formalism.MainNotions.StandardLatticesGL3.inc D).toMonoidHom k) ^ e : ℂˣ) : ℂ) :=
    hf y _ ⟨hy, by rw [hy']; exact finAdEquiv_one_tmul D k⟩
  have h5 : ((χ x : Circle) : ℂ) * ((χ y : Circle) : ℂ) = 1 := by
    rw [← Circle.coe_mul, ← map_mul, ← hxy, hχ.2 k, Circle.coe_one]
  have haut := c.aut k
  set F : ℂ := ((c.f (Units.map (Formalism.MainNotions.StandardLatticesGL3.inc D).toMonoidHom k) : ℂˣ) : ℂ) with hF
  have hF0 : F ≠ 0 := (c.f _).ne_zero
  have hP : ∏ τ, (embT D τ (k : D.host.E) / ((‖embT D τ (k : D.host.E)‖ : ℝ) : ℂ)) ^ (c.n τ) = F⁻¹ :=
    eq_inv_of_mul_eq_one_right haut
  rw [Units.val_zpow_eq_zpow_val, ← hF] at hfin
  rw [hfin] at h5
  have hx : ((χ x : Circle) : ℂ) = (F ^ e)⁻¹ := eq_inv_of_mul_eq_one_left h5
  rw [hx, ← inv_zpow, ← hP, ← Finset.prod_zpow]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [← zpow_mul, mul_comm]



open Formalism.MainNotions Formalism.L2.Pj Formalism.IndefR.Links Formalism.L2.JoinChr Formalism.L2.Host GlobalTheory.FockCompare GlobalTheory.HeckeFinTrivial in
theorem hasInfExp_of_hasFinPart : ∀ {D : D7} {N : ℕ} (c : HeckeU D N) (e : ℤ) (χ : (AE D)ˣ →* Circle), IsHeckeChar D χ →
    HasFinPart χ c e → ∀ τ, HasInfExp D χ τ ((e : ℚ) * (c.n τ : ℚ) / 2) := by
  intro D N c e χ hχ hf τ₀
  obtain ⟨⟨θ', hθ'⟩, -⟩ := GlobalTheory.Member.infiniteAdele_bijective D
  refine ⟨e * c.n τ₀, by push_cast; ring, ⟨fun τ => θ' (tauE D τ), fun τ => hθ' _⟩, fun θ hθ => ?_⟩
  obtain ⟨ρ, hρ, r1, r0⟩ := exists_real_chart D θ hθ (GlobalTheory.CMTypePlaces.places_bijective D)
  obtain ⟨s, hs⟩ := RealChart.exists_chart D θ hθ ρ hρ r1 r0
  obtain ⟨-, a, b, -, -, hab, ha, hb⟩ := GlobalTheory.IdeleParts.congr_open_and_parts D
  haveI : Nonempty D.what₂.Tau := ⟨τ₀⟩
  have ext : ∀ a b : AE D, finPart D a = finPart D b → (∀ τ, θ τ (infPart D a) = θ τ (infPart D b)) → a = b := by
    intro a b h1 h2
    rw [← sub_eq_zero]
    exact hs.ext _ (by rw [RingHom.map_sub, h1, sub_self]) fun τ => by
      rw [RingHom.map_sub, RingHom.map_sub, h2, sub_self]
  let t : (D.what₂.Tau → ℂˣ) → AE D := fun z => s (fun τ => (z τ : ℂ)) + (1 - s 1)
  have tf : ∀ z, finPart D (t z) = 1 := fun z => by
    simp only [t, RingHom.map_add (f := _), RingHom.map_sub, RingHom.map_one, hs.fin, zero_add, sub_zero]
  have ti : ∀ z τ, θ τ (infPart D (t z)) = z τ := fun z τ => by
    simp only [t, RingHom.map_add (f := _), RingHom.map_sub, RingHom.map_one, hs.comp, Pi.one_apply, sub_self, add_zero]
  have tc : Continuous t :=
    (hs.cont.comp (continuous_pi fun τ => Units.continuous_val.comp (continuous_apply τ))).add continuous_const
  let T : (D.what₂.Tau → ℂˣ) →* AE D :=
    { toFun := t
      map_one' := ext _ _ (by rw [tf, RingHom.map_one]) fun τ => by
        rw [ti, RingHom.map_one, RingHom.map_one]; rfl
      map_mul' := fun x y => ext _ _ (by rw [RingHom.map_mul, tf, tf, tf, mul_one]) fun τ => by
        rw [RingHom.map_mul, RingHom.map_mul, ti, ti, ti]; rfl }
  have Tc : Continuous T.toHomUnits := Units.continuous_iff.2 ⟨tc, tc.comp continuous_inv⟩
  have hT : ∀ x : (AE D)ˣ, finPart D (x : AE D) = 1 →
      x = T.toHomUnits fun τ => Units.map ((θ τ).comp (infPart D)).toMonoidHom x := fun x hx =>
    Units.ext (ext _ _ (hx.trans (tf _).symm) fun τ =>
      (ti (fun τ => Units.map ((θ τ).comp (infPart D)).toMonoidHom x) τ).symm)
  have hd : DenseRange fun (k : D.host.E) τ => tauE D τ k := by
    intro z
    have := mem_closure_range (tauE D) θ (fun τ => (hθ τ).1) (fun τ => (hθ τ).2) (infPart D (s z))
    rwa [show (fun i => θ i (infPart D (s z))) = z from funext fun τ => hs.comp z τ] at this
  have key : ∀ z : D.what₂.Tau → ℂˣ,
      ((χ (T.toHomUnits z) : Circle) : ℂ) = ∏ τ, ((z τ : ℂ) / ((‖(z τ : ℂ)‖ : ℝ) : ℂ)) ^ (e * c.n τ) := by
    intro z
    refine (denseRange_units (tauE D) hd).induction_on z (isClosed_eq
      (continuous_subtype_val.comp (hχ.1.comp Tc)) (continuous_finsetProd _ fun τ _ => ?_)) fun k => ?_
    · have h1 : Continuous fun z : D.what₂.Tau → ℂˣ => (z τ : ℂ) := Units.continuous_val.comp (continuous_apply τ)
      have h2 : ∀ z : D.what₂.Tau → ℂˣ, ((‖(z τ : ℂ)‖ : ℝ) : ℂ) ≠ 0 := fun z =>
        Complex.ofReal_ne_zero.2 (norm_ne_zero_iff.2 (z τ).ne_zero)
      exact (h1.div (Complex.continuous_ofReal.comp h1.norm) h2).zpow₀ _ fun z =>
        Or.inl (div_ne_zero (z τ).ne_zero (h2 z))
    · refine Eq.trans ?_ (GlobalTheory.NormExact.InfExp.eq_inf c e χ hχ hf k _ _ (hab _) (hb _).1 (hb _).2)
      rw [hT _ (ha (Units.map (incA D).toMonoidHom k)).2]
      congr 3
      funext τ
      exact Units.ext ((congrArg (θ τ) (ha (Units.map (incA D).toMonoidHom k)).1).trans ((hθ τ).1 k)).symm
  intro x hx hx'
  refine (congrArg (fun u => ((χ u : Circle) : ℂ)) (hT x hx)).trans ((key _).trans ?_)
  refine Finset.prod_eq_single τ₀ (fun τ _ hτ => ?_) (fun h => absurd (Finset.mem_univ _) h)
  have : ((Units.map ((θ τ).comp (infPart D)).toMonoidHom x : ℂˣ) : ℂ) = 1 := hx' τ hτ
  rw [this, norm_one, Complex.ofReal_one, div_one, one_zpow]

end GlobalTheory.NormExact.InfExp
end

section

open scoped TensorProduct NNReal Matrix IsMulCommutative
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB
open GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.LeviHC

namespace GlobalTheory.LeviHC

theorem monicFactorFinite : MonicFactorFinite := by
  intro N _ _ p q hp hq hpp hqq hpq v hfin
  rcases subsingleton_or_nontrivial N with hN | hN
  · infer_instance
  obtain ⟨d, c₀, hcd, hpc₀⟩ := hp
  obtain ⟨e, b₀, hbe, hqb₀⟩ := hq
  set T := Algebra.adjoin ℂ (Set.range fun u => p u * q u) with hT
  set Wsp := Submodule.span ℂ {y | ∃ a ∈ T, y = a v} with hWsp
  let s : Set (Module.End ℂ N) := Set.range p ∪ Set.range q
  have hcomm : ∀ a ∈ s, ∀ b ∈ s, a * b = b * a := by
    rintro a (⟨u, rfl⟩ | ⟨u, rfl⟩) b (⟨u', rfl⟩ | ⟨u', rfl⟩)
    · exact hpp u u'
    · exact hpq u u'
    · exact (hpq u' u).symm
    · exact hqq u u'
  let S := Algebra.adjoin ℂ s
  have : IsMulCommutative S := Algebra.isMulCommutative_adjoin ℂ fun a ha b hb _ => hcomm a ha b hb

  let c : ℕ → Module.End ℂ N := fun i => if i < d + 1 then c₀ i else 0
  let b : ℕ → Module.End ℂ N := fun i => if i < e + 1 then b₀ i else 0
  have hpc : ∀ u, p u = ∑ i ∈ Finset.range (d + 1), u ^ i • c i := fun u => by
    rw [hpc₀ u]; exact Finset.sum_congr rfl fun i hi => by
      show _ = u ^ i • (if i < d + 1 then c₀ i else 0); rw [ite_eq_left (Finset.mem_range.1 hi)]
  have hqb : ∀ u, q u = ∑ i ∈ Finset.range (e + 1), u ^ i • b i := fun u => by
    rw [hqb₀ u]; exact Finset.sum_congr rfl fun i hi => by
      show _ = u ^ i • (if i < e + 1 then b₀ i else 0); rw [ite_eq_left (Finset.mem_range.1 hi)]
  have hpS : Submodule.span ℂ (Set.range p) ≤ Subalgebra.toSubmodule S :=
    Submodule.span_le.2 fun x hx => Algebra.subset_adjoin (Or.inl hx)
  have hqS : Submodule.span ℂ (Set.range q) ≤ Subalgebra.toSubmodule S :=
    Submodule.span_le.2 fun x hx => Algebra.subset_adjoin (Or.inr hx)
  have hcS : ∀ i, c i ∈ S := fun i => by
    by_cases h : i < d + 1
    · show (if i < d + 1 then c₀ i else 0) ∈ S
      rw [ite_eq_left h]; exact hpS (coeff_mem_span hpc₀ h)
    · show (if i < d + 1 then c₀ i else 0) ∈ S
      rw [ite_eq_right h]; exact S.zero_mem
  have hbS : ∀ i, b i ∈ S := fun i => by
    by_cases h : i < e + 1
    · show (if i < e + 1 then b₀ i else 0) ∈ S
      rw [ite_eq_left h]; exact hqS (coeff_mem_span hqb₀ h)
    · show (if i < e + 1 then b₀ i else 0) ∈ S
      rw [ite_eq_right h]; exact S.zero_mem
  let c' : ℕ → S := fun i => ⟨c i, hcS i⟩
  let b' : ℕ → S := fun i => ⟨b i, hbS i⟩
  let P : Polynomial S := ∑ i ∈ Finset.range (d + 1), Polynomial.monomial i (c' i)
  let Q : Polynomial S := ∑ i ∈ Finset.range (e + 1), Polynomial.monomial i (b' i)
  have hPe : ∀ u, ((P.eval (algebraMap ℂ S u) : S) : Module.End ℂ N) = p u := fun u => by
    rw [hpc u]
    simp only [P, Polynomial.eval_finsetSum, Polynomial.eval_monomial]
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Algebra.smul_def, Algebra.commutes, map_pow]
  have hQe : ∀ u, ((Q.eval (algebraMap ℂ S u) : S) : Module.End ℂ N) = q u := fun u => by
    rw [hqb u]
    simp only [Q, Polynomial.eval_finsetSum, Polynomial.eval_monomial]
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Algebra.smul_def, Algebra.commutes, map_pow]
  have hPc : ∀ i, i < d + 1 → P.coeff i = c' i := fun i hi => by
    simp only [P, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial_apply]
    rw [Finset.sum_ite_eq', ite_eq_left (Finset.mem_range.2 hi)]
  have hPm : P.Monic := by
    refine Polynomial.monic_of_degree_le d ?_ ?_
    · refine (Polynomial.degree_sum_le _ _).trans (Finset.sup_le fun i hi => ?_)
      exact (Polynomial.degree_monomial_le _ _).trans (by exact_mod_cast Nat.lt_succ_iff.1 (Finset.mem_range.1 hi))
    · rw [hPc d (Nat.lt_succ_self d)]
      exact Subtype.ext (by simp [c', c, hcd])
  have hQm : Q.Monic := by
    refine Polynomial.monic_of_degree_le e ?_ ?_
    · refine (Polynomial.degree_sum_le _ _).trans (Finset.sup_le fun i hi => ?_)
      exact (Polynomial.degree_monomial_le _ _).trans (by exact_mod_cast Nat.lt_succ_iff.1 (Finset.mem_range.1 hi))
    · simp only [Q, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial_apply]
      rw [Finset.sum_ite_eq', ite_eq_left (Finset.mem_range.2 (Nat.lt_succ_self e))]
      exact Subtype.ext (by simp [b', b, hbe])

  let R : Subalgebra ℂ S :=
    Algebra.adjoin ℂ (Set.range fun u => P.eval (algebraMap ℂ S u) * Q.eval (algebraMap ℂ S u))
  have hRT : ∀ r ∈ R, ((r : S) : Module.End ℂ N) ∈ T := by
    intro r hr
    have hle : R ≤ Subalgebra.comap S.val T := Algebra.adjoin_le (by
      rintro _ ⟨u, rfl⟩
      show ((P.eval (algebraMap ℂ S u) * Q.eval (algebraMap ℂ S u) : S) : Module.End ℂ N) ∈ T
      rw [Subalgebra.coe_mul, hPe, hQe]
      exact Algebra.subset_adjoin ⟨u, rfl⟩)
    exact hle hr

  have hPQR : ∀ k, (P * Q).coeff k ∈ R := by
    intro k
    by_cases hk : k < (P * Q).natDegree + 1
    · have hf : ∀ u, (P * Q).eval (algebraMap ℂ S u) =
          ∑ i ∈ Finset.range ((P * Q).natDegree + 1), u ^ i • (P * Q).coeff i := fun u => by
        rw [Polynomial.eval_eq_sum_range]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Algebra.smul_def, map_pow, mul_comm]
      have h1 := coeff_mem_span hf hk
      have h2 : Submodule.span ℂ (Set.range fun u => (P * Q).eval (algebraMap ℂ S u)) ≤ Subalgebra.toSubmodule R := by
        refine Submodule.span_le.2 ?_
        rintro _ ⟨u, rfl⟩
        show Polynomial.eval (algebraMap ℂ S u) (P * Q) ∈ R
        rw [Polynomial.eval_mul]
        exact Algebra.subset_adjoin ⟨u, rfl⟩
      exact h2 h1
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]
      exact R.zero_mem
  have hlift : P * Q ∈ Polynomial.lifts (algebraMap R S) :=
    (Polynomial.lifts_iff_coeff_lifts (f := algebraMap R S) (P * Q)).2 fun k => ⟨⟨_, hPQR k⟩, rfl⟩
  obtain ⟨F, hF, -, hFm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hlift (hPm.mul hQm)

  let C : Set S := c' '' (Finset.range (d + 1) : Set ℕ)
  have hCf : C.Finite := (Finset.range (d + 1)).finite_toSet.image c'
  have hCi : ∀ x ∈ C, IsIntegral R x := by
    rintro _ ⟨i, hi, rfl⟩
    have := Polynomial.isIntegral_coeff_of_dvd F P hFm hPm (by rw [hF]; exact dvd_mul_right P Q) i
    rwa [hPc i (Finset.mem_range.1 hi)] at this
  obtain ⟨G, hG⟩ := fg_adjoin_of_finite hCf hCi

  let B : Subalgebra ℂ S := (Algebra.adjoin R C).restrictScalars ℂ
  have hpB : Algebra.adjoin ℂ (Set.range fun u => P.eval (algebraMap ℂ S u)) ≤ B := by
    refine Algebra.adjoin_le ?_
    rintro _ ⟨u, rfl⟩
    simp only [P, Polynomial.eval_finsetSum, Polynomial.eval_monomial]
    refine B.sum_mem fun i hi => B.mul_mem ?_ (B.pow_mem (B.algebraMap_mem u) _)
    exact (Subalgebra.mem_restrictScalars _).2 (Algebra.subset_adjoin ⟨i, hi, rfl⟩)
  have hmap : Algebra.adjoin ℂ (Set.range p) =
      (Algebra.adjoin ℂ (Set.range fun u => P.eval (algebraMap ℂ S u))).map S.val := by
    rw [AlgHom.map_adjoin, ← Set.range_comp]
    exact congrArg (fun f => Algebra.adjoin ℂ (Set.range f)) (funext fun u => (hPe u).symm)

  let Xs : Submodule ℂ N := ⨆ g : (G : Set S), (Wsp.map ((g : S) : Module.End ℂ N) : Submodule ℂ N)
  have : FiniteDimensional ℂ Wsp := hfin
  have key : ∀ x ∈ Submodule.span R (G : Set S), ∀ t ∈ T, ((x : S) : Module.End ℂ N) (t v) ∈ Xs := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem g hg =>
      intro t ht
      have h1 : t v ∈ Wsp := Submodule.subset_span ⟨t, ht, rfl⟩
      exact (le_iSup (fun g : (G : Set S) => (Wsp.map ((g : S) : Module.End ℂ N) : Submodule ℂ N)) ⟨g, hg⟩)
        (Submodule.mem_map_of_mem h1)
    | zero =>
      intro t _
      rw [Subalgebra.coe_zero, LinearMap.zero_apply]
      exact Xs.zero_mem
    | add x y _ _ ihx ihy =>
      intro t ht
      rw [Subalgebra.coe_add, LinearMap.add_apply]
      exact Xs.add_mem (ihx t ht) (ihy t ht)
    | smul a x _ ih =>
      intro t ht
      have e1 : (a • x : S) = x * (a : S) := by rw [Algebra.smul_def, mul_comm]; rfl
      rw [e1, Subalgebra.coe_mul, mul_apply_eq_comp]
      have := ih _ (T.mul_mem (hRT a a.2) ht)
      rwa [mul_apply_eq_comp] at this
  refine Submodule.finiteDimensional_of_le (S₂ := Xs) (Submodule.span_le.2 ?_)
  rintro _ ⟨a, ha, rfl⟩
  rw [hmap] at ha
  obtain ⟨x, hx, rfl⟩ := Subalgebra.mem_map.1 ha
  have hx' : x ∈ Submodule.span R (G : Set S) := by
    rw [hG]; exact (Subalgebra.mem_restrictScalars _).1 (hpB hx)
  have := key x hx' 1 T.one_mem
  simpa using this

end GlobalTheory.LeviHC
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

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Geo Chars)

theorem gbig_two {Q1 Q2 Q : GP} (h1 : GBig Q1) (h2 : GBig Q2)
    (H : ∀ {D : D7} {T : Type} {Lc : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} (G : GridData Lc sc) (μ₀ : T) (C x b : ℝ),
      Q1 G μ₀ C x b → Q2 G μ₀ C x b → Q G μ₀ C x b) : GBig Q := by
  obtain ⟨a1, h1⟩ := h1
  obtain ⟨a2, h2⟩ := h2
  refine ⟨max a1 a2, fun ε CF hCF => ?_⟩
  obtain ⟨c1, x1, g1⟩ := h1 ε CF (le_trans (le_max_left _ _) hCF)
  obtain ⟨c2, x2, g2⟩ := h2 ε CF (le_trans (le_max_right _ _) hCF)
  refine ⟨max c1 c2, max x1 x2, fun C hC D large₂ hε hx hR T Lc μ₀ hμ G => H G μ₀ C _ _ ?_ ?_⟩
  · exact g1 C (le_trans (le_max_left _ _) hC) D large₂ hε (le_trans (le_max_left _ _) hx) hR T Lc μ₀ hμ G
  · exact g2 C (le_trans (le_max_right _ _) hC) D large₂ hε (le_trans (le_max_right _ _) hx) hR T Lc μ₀ hμ G

variable {D : D7} {T : Type} {Lc : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts}

def Carried (G : GridData Lc sc) (W : G.Weil) (i j : Fin D.R.m) {A A' WW : HSp D} (X : Tri T A A' WW)
    (Bs : Base D.host.F D.host.E) (FA : GlobalTheory.ChainFr.Fr A) (FA' : GlobalTheory.ChainFr.Fr A') (FW : GlobalTheory.ChainFr.Fr WW)
    (Γ : Geo D.sp.cm.sig A.rank A'.rank) (s : T) : Prop :=
  GlobalTheory.SquareComm.IsFinF W.ψ W.θ true FA FW (X.f s) ∧ GlobalTheory.SquareComm.IsFinF W.ψ W.θ false FA' FW (X.f' s) ∧
    (∀ P g h, thetaKO (X.ω s) g h (GlobalTheory.SquareComm.fockF W.ψ W.θ true FA FW (X.f s) P) = X.ker W.ψ W.θ s P h g) ∧
    (∀ P g h, thetaKO (X.ω' s) g h (GlobalTheory.SquareComm.fockF W.ψ W.θ false FA' FW (X.f' s) P) = X.ker' W.ψ W.θ s P h g) ∧
    ∀ om om', GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ (GlobalTheory.SqStep.chs G i j s) om om' →
      ∃ e cA cB, GlobalTheory.SquareAgree.IsOver W.ψ W.θ FA FA' FW (GlobalTheory.SqStep.chs G i j s).α (GlobalTheory.SqStep.chs G i j s).β X.m X.fd
        X.m' X.fd' (X.ω s) (X.ω' s) e Bs Γ (GlobalTheory.SqStep.chs G i j s) om om' cA cB

end GlobalTheory.SqStepBig

end
end
