module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle410
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualSplitComponentIsLatticeStabilizerEq
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WittDecompositionCoreProjMulCoreEqOne
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsSelfDualCHyperbolicExtensionLatticeConjStable
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsOneComb
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsOpenKerUnramMulTame
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.JointSmooth
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiStarOfMid
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MidChart
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV Moves MonoAt OrthAt PrimAt idAt intAt grpAt colMul Lat SplitPt GoodBF GluedCore IsSumFrame)
open GlobalTheory.SeeSaw (idV dI FI)
open ValuativeRel
open GlobalTheory.Core.Mi.LatMatch

namespace GlobalTheory.Core.Mi.LatMatch

open GlobalTheory.FinPl.FrameLat

section

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem mulVec_sec_w (p : SplitPt D k) {m n : ℕ} (a : Matrix (Fin m) (Fin n) (AE D)) (y : Fin n → k) :
    a *ᵥ (fun i => p.sec (y i)) = fun i => p.sec ((a.map p.pr *ᵥ y) i) := by
  funext i

  simp only [Matrix.mulVec, dotProduct, map_sum, Matrix.map_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mul_comm, sec_mul_right, mul_comm]

theorem inc_mul_sec_mem_iff (p : SplitPt D k) (α : D.host.E) (x : k) :
    incA D α * p.sec x ∈ intAt D (· = p.v) ↔ p.pr (incA D α) * x ∈ 𝒪[k] := by
  rw [mul_comm, sec_mul_right, mul_comm x]
  exact ⟨fun h => (p.int_iff _).2 h.2, sec_mem_intAt p _⟩

theorem proj_mulVec_add {R : Type} [CommRing R] {l m n : ℕ} {P : Matrix (Fin m) (Fin l) R} {J : Matrix (Fin l) (Fin m) R}
    {J' : Matrix (Fin l) (Fin n) R} (h1 : P * J = 1) (h0 : P * J' = 0) (u : Fin m → R) (v : Fin n → R) :
    P *ᵥ (J *ᵥ u + J' *ᵥ v) = u := by
  rw [Matrix.mulVec_add, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, h1, h0, Matrix.one_mulVec, Matrix.zero_mulVec, add_zero]

end



theorem wShape_of_mono (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : SplitPt D k) (S S₀ A Ln : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (o : OrthDec S₀ A Ln) (ζ : Fin Ln.rank → D.host.E)
    (L : Lat S) (M : Lat S₀) (N : Lat A) (α α' : Fin ρ → D.host.E) (μ : D.host.E) (g : GA D A)
    (hmono : MonoAt d L M p.v)
    (hX : ∀ i, ∀ a ∈ idAt D (· = p.v), colMul d.jX i a ∈ latV S L (· = p.v) ↔ incA D (α i) * a ∈ intAt D (· = p.v))
    (hY : ∀ i, ∀ a ∈ idAt D (· = p.v), colMul d.jY i a ∈ latV S L (· = p.v) ↔ incA D (α' i) * a ∈ intAt D (· = p.v))
    (hline : LineAt (vecB o ζ) μ M p.v) (hsplit : SplitsAt o M p.v) (htr : TraceAt o g N M p.v) :
    WShape p d o ζ L (fun i => p.pr (incA D (α i))) (fun i => p.pr (incA D (α' i))) (p.pr (incA D μ)) g N := by
  intro x x' t y
  let f : D.host.E →+* k := p.pr.comp (incA D)
  have hz : o.jB *ᵥ (fun i => p.sec ((t • (f ∘ ζ)) i)) = p.sec t • ratV (vecB o ζ) := by
    rw [mulVec_sec_w, Matrix.mulVec_smul]
    funext i
    have h := RingHom.map_mulVec f o.iB ζ i
    rw [Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, sec_mul_right]
    exact congrArg (fun u => p.sec (t * u)) h.symm
  obtain ⟨c, hc⟩ : ∃ c : Fin S₀.rank → AE D, c = o.jB *ᵥ (fun i => p.sec ((t • (f ∘ ζ)) i)) +
    o.jA *ᵥ (Formalism.L2.Theta.mt A g *ᵥ fun r => p.sec (y r)) := ⟨_, rfl⟩
  have hcid : ∀ i, c i ∈ idAt D (· = p.v) := fun i => by
    rw [hc, mulVec_sec_w, mulVec_sec_w, mulVec_sec_w]
    exact add_mem (sec_mem_idAt p _) (sec_mem_idAt p _)
  have hvec : (fun r => p.sec ((atW p d.e *ᵥ x + atW p d.e' *ᵥ x' + t • (fun r' => p.pr (incA D ((d.i₀ *ᵥ vecB o ζ) r'))) +
        atW p (d.i₀ * o.iA) *ᵥ ((Formalism.L2.Theta.mt A g).map p.pr *ᵥ y)) r)) =
      d.jX *ᵥ (fun i => p.sec (x i)) + d.jY *ᵥ (fun i => p.sec (x' i)) + d.j0 *ᵥ c := by
    have h1 : (fun r' => p.pr (incA D ((d.i₀ *ᵥ vecB o ζ) r'))) = d.i₀.map f *ᵥ (o.iB.map f *ᵥ (f ∘ ζ)) := by
      have h2 : o.iB.map f *ᵥ (f ∘ ζ) = f ∘ vecB o ζ := by
        funext i; exact (RingHom.map_mulVec f o.iB ζ i).symm
      rw [h2]
      funext i; exact RingHom.map_mulVec f d.i₀ _ i
    have h3 : atW p (d.i₀ * o.iA) = d.i₀.map f * o.iA.map f := Matrix.map_mul (f := f)
    rw [hc, Matrix.mulVec_add, h1, h3, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_smul, ← Matrix.mulVec_smul]
    have e1 : d.jX.map p.pr = atW p d.e := rfl
    have e2 : d.jY.map p.pr = atW p d.e' := rfl
    have e3 : d.j0.map p.pr = d.i₀.map f := rfl
    have e4 : o.jA.map p.pr = o.iA.map f := rfl
    have e5 : o.jB.map p.pr = o.iB.map f := rfl
    rw [mulVec_sec_w p d.jX, mulVec_sec_w p d.jY, mulVec_sec_w p o.jB, mulVec_sec_w p d.j0,
      mulVec_sec_w p (Formalism.L2.Theta.mt A g), mulVec_sec_w p o.jA, mulVec_sec_w p d.j0, e1, e2, e3, e4, e5]
    funext r
    simp only [Pi.add_apply, map_add p.sec, add_assoc]
  rw [hvec, hmono]
  simp only [Matrix.mulVec_add, Matrix.mulVec_mulVec, d.pX_jX, d.pX_jY, d.pX_j0, d.pY_jX, d.pY_jY, d.pY_j0, d.p0_jX,
    d.p0_jY, d.p0_j0, Matrix.one_mulVec, Matrix.zero_mulVec, add_zero, zero_add]
  have hA : o.pA *ᵥ c = Formalism.L2.Theta.mt A g *ᵥ fun r => p.sec (y r) := by
    rw [hc, add_comm]; exact proj_mulVec_add o.pA_jA o.pA_jB _ _
  have hB : o.pB *ᵥ c = fun i => p.sec ((t • (f ∘ ζ)) i) := by
    rw [hc]; exact proj_mulVec_add o.pB_jB o.pB_jA _ _
  rw [hsplit c hcid, hA, hB, hz, hline _ (sec_mem_idAt p t), ← htr _ (fun i => sec_mem_idAt p _), inc_mul_sec_mem_iff]
  refine and_congr (forall_congr' fun i => ?_) (and_congr (forall_congr' fun i => ?_) and_comm)
  · rw [hX i _ (sec_mem_idAt p _), inc_mul_sec_mem_iff]
  · rw [hY i _ (sec_mem_idAt p _), inc_mul_sec_mem_iff]

end GlobalTheory.Core.Mi.LatMatch
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV Moves MonoAt OrthAt PrimAt idAt intAt grpAt colMul Lat SplitPt GoodBF GluedCore IsSumFrame)
open GlobalTheory.SeeSaw (idV dI FI)
open ValuativeRel
open GlobalTheory.Core.Mi.LatMatch

noncomputable section

namespace GlobalTheory.Core.Mi.LatMatch

open GlobalTheory.SeeSaw.SplitLat

variable {D : D7}

theorem pair_eq_dot {n : ℕ} (G : Matrix (Fin n) (Fin n) D.host.E) (x y : Fin n → D.host.E) :
    ∑ i, ∑ j, star (x i) * G i j * y j = star x ⬝ᵥ (G *ᵥ y) := by
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, Pi.star_apply, mul_assoc]

theorem pair_i₀ {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (x : Fin S.rank → D.host.E) (y : Fin S₀.rank → D.host.E) :
    ∑ i, ∑ j, star (x i) * S.gram i j * (d.i₀ *ᵥ y) j = ∑ i, ∑ j, star ((d.q0 *ᵥ x) i) * S₀.gram i j * y j := by
  have hG : S.gram * d.i₀ = d.q0ᴴ * S₀.gram := by
    rw [gram_eq d]
    simp only [Matrix.add_mul, Matrix.mul_assoc, qX_i₀, qY_i₀, wittDecomposition_coreProj_mul_core_eq_one, Matrix.mul_zero, Matrix.mul_one, add_zero,
      zero_add]
  rw [pair_eq_dot, pair_eq_dot, Matrix.mulVec_mulVec, hG, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
    Matrix.star_mulVec]

theorem mulVec_eq_sum_cols {m n : ℕ} (M : Matrix (Fin m) (Fin n) D.host.E) (w : Fin n → D.host.E) :
    M *ᵥ w = ∑ i, fun r => w i * M r i := by
  funext r
  simp only [Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]

theorem colProj_mulVec' {S : HSp D} {ρ m : ℕ} (q : Matrix (Fin ρ) (Fin m) D.host.E)
    (f : Matrix (Fin S.rank) (Fin ρ) D.host.E) (i : Fin ρ) (x : Fin m → D.host.E) :
    colProj q f i *ᵥ x = fun r => (q *ᵥ x) i * f r i := by
  funext k
  simp only [colProj, Matrix.mulVec, dotProduct, Matrix.of_apply, Finset.sum_mul]
  exact Finset.sum_congr rfl fun l _ => by ring

theorem selfDual_core_monoAt (D : D7) (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (L : Lat S) (hL : IsSelfDualC S L)
    (hcol : ∀ y ∈ L, ∀ i, (fun r => (d.qX *ᵥ y) i * d.e r i) ∈ L ∧ (fun r => (d.qY *ᵥ y) i * d.e' r i) ∈ L) :
    IsSelfDualC S₀ (coreLat d L) ∧ ∀ v : GlobalTheory.FinPl.Pl D, MonoAt d L (coreLat d L) v := by

  have hcore : ∀ y ∈ L, d.q0 *ᵥ y ∈ coreLat d L := by
    intro y hy
    rw [mem_coreLat]
    have hdec : y = d.e *ᵥ (d.qX *ᵥ y) + d.i₀ *ᵥ (d.q0 *ᵥ y) + d.e' *ᵥ (d.qY *ᵥ y) := by
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Matrix.add_mulVec, ← Matrix.add_mulVec,
        d.sum_eq_one_rat, Matrix.one_mulVec]
    have hX : d.e *ᵥ (d.qX *ᵥ y) ∈ L := by
      rw [mulVec_eq_sum_cols]; exact sum_mem fun i _ => (hcol y hy i).1
    have hY : d.e' *ᵥ (d.qY *ᵥ y) ∈ L := by
      rw [mulVec_eq_sum_cols]; exact sum_mem fun i _ => (hcol y hy i).2
    have key : ∀ a b c z : Fin S.rank → D.host.E, z = a + b + c → b = z - a - c := by
      intro a b c z hz; rw [hz]; abel
    have h : d.i₀ *ᵥ (d.q0 *ᵥ y) = y - d.e *ᵥ (d.qX *ᵥ y) - d.e' *ᵥ (d.qY *ᵥ y) := key _ _ _ _ hdec
    rw [h]
    exact sub_mem (sub_mem hy hX) hY
  have hinj : Function.Injective ((Matrix.mulVecLin d.i₀).restrictScalars (𝓞 D.host.E)) := by
    intro x x' hxx
    have h := congrArg (fun z => d.q0 *ᵥ z) hxx
    simpa only [LinearMap.coe_restrictScalars, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, wittDecomposition_coreProj_mul_core_eq_one,
      Matrix.one_mulVec] using h
  refine ⟨⟨⟨?_, ?_⟩, fun y => ⟨fun hy x hx => ?_, fun h => ?_⟩⟩, fun v => ?_⟩
  ·
    refine Submodule.fg_of_fg_map_injective _ hinj ?_
    have hLfg : L.FG := hL.1.fg
    haveI : IsNoetherian (𝓞 D.host.E) L := isNoetherian_of_fg_of_noetherian L hLfg
    have hle : (coreLat d L).map ((Matrix.mulVecLin d.i₀).restrictScalars (𝓞 D.host.E)) ≤ L :=
      Submodule.map_comap_le _ _
    have h1 : (((coreLat d L).map ((Matrix.mulVecLin d.i₀).restrictScalars (𝓞 D.host.E))).comap L.subtype).FG :=
      IsNoetherian.noetherian _
    have h2 := h1.map L.subtype
    rwa [Submodule.map_comap_subtype, inf_eq_right.mpr hle] at h2
  ·
    intro s hs hli
    exact (LinearIndependent.iff_fractionRing _ _).mp hli
  ·
    obtain ⟨b, hb⟩ := (hL.2 (d.i₀ *ᵥ y)).1 hy (d.i₀ *ᵥ x) hx
    refine ⟨b, ?_⟩
    rw [hb, pair_i₀, Matrix.mulVec_mulVec, wittDecomposition_coreProj_mul_core_eq_one, Matrix.one_mulVec]
  ·
    rw [mem_coreLat]
    refine (hL.2 (d.i₀ *ᵥ y)).2 fun x hx => ?_
    obtain ⟨b, hb⟩ := h (d.q0 *ᵥ x) (hcore x hx)
    exact ⟨b, hb.trans (pair_i₀ d x y).symm⟩
  ·
    have hX : ∀ i : Fin ρ, ∀ x ∈ L, colProj d.qX d.e i *ᵥ x ∈ L := fun i x hx => by
      rw [colProj_mulVec']; exact (hcol x hx i).1
    have hY : ∀ i : Fin ρ, ∀ x ∈ L, colProj d.qY d.e' i *ᵥ x ∈ L := fun i x hx => by
      rw [colProj_mulVec']; exact (hcol x hx i).2
    intro y
    constructor
    · intro hy
      refine ⟨fun i => ?_, fun i => ?_, ?_⟩
      · change colMul (rat d.e) i ((rat d.qX *ᵥ y) i) ∈ _
        rw [colMul_rat]
        exact rat_mulVec_mem_latV _ (hX i) _ hy
      · change colMul (rat d.e') i ((rat d.qY *ᵥ y) i) ∈ _
        rw [colMul_rat]
        exact rat_mulVec_mem_latV _ (hY i) _ hy
      · exact rat_mulVec_mem_latV d.q0 hcore _ hy
    · rintro ⟨h1, h3, h2⟩
      have e : y = d.jX *ᵥ (d.pX *ᵥ y) + d.j0 *ᵥ (d.p0 *ᵥ y) + d.jY *ᵥ (d.pY *ᵥ y) := by
        rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Matrix.add_mulVec, ← Matrix.add_mulVec,
          d.sum_eq_one, Matrix.one_mulVec]
      rw [e, mulVec_eq_sum_colMul d.jX, mulVec_eq_sum_colMul d.jY]
      refine add_mem (add_mem (sum_mem fun i _ => h1 i) ?_) (sum_mem fun i _ => h3 i)
      exact rat_mulVec_mem_latV d.i₀ (fun x hx => hx) _ h2

end GlobalTheory.Core.Mi.LatMatch

end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.LatPair GlobalTheory.SeeSaw GlobalTheory.FinPl ValuativeRel
open scoped TensorProduct nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SeeSaw.SplitLat

variable {D : D7} {S S₀ : HSp D} {ρ : ℕ}

theorem sum_pair_eq {n : ℕ} (G : Matrix (Fin n) (Fin n) D.host.E) (x y : Fin n → D.host.E) :
    ∑ i, ∑ j, star (x i) * G i j * y j = star x ⬝ᵥ (G *ᵥ y) := by
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, Pi.star_apply, mul_assoc]

theorem pair_mul {m n : ℕ} (A B : Matrix (Fin m) (Fin n) D.host.E) (x y : Fin n → D.host.E) :
    star x ⬝ᵥ ((Aᴴ * B) *ᵥ y) = star (A *ᵥ x) ⬝ᵥ (B *ᵥ y) := by
  rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.star_mulVec]

variable (d : HypDec S S₀ ρ)

theorem pair_decomp (x y : Fin S.rank → D.host.E) :
    star x ⬝ᵥ (S.gram *ᵥ y) = star (d.qY *ᵥ x) ⬝ᵥ (d.qX *ᵥ y) + star (d.q0 *ᵥ x) ⬝ᵥ (S₀.gram *ᵥ (d.q0 *ᵥ y)) +
      star (d.qX *ᵥ x) ⬝ᵥ (d.qY *ᵥ y) := by
  rw [gram_eq d, Matrix.add_mulVec, Matrix.add_mulVec, dotProduct_add, dotProduct_add, pair_mul, pair_mul, pair_mul,
    ← Matrix.mulVec_mulVec]

theorem star_single (i : Fin ρ) (b : D.host.E) : star (Pi.single i b : Fin ρ → D.host.E) = Pi.single i (star b) := by
  funext j; by_cases h : j = i <;> simp [h, Pi.single_apply]

theorem pair_e (i : Fin ρ) (b : D.host.E) (y : Fin S.rank → D.host.E) :
    star (d.e *ᵥ Pi.single i b) ⬝ᵥ (S.gram *ᵥ y) = star b * (d.qY *ᵥ y) i := by
  rw [pair_decomp d]
  simp only [Matrix.mulVec_mulVec, qX_e, wittDecomposition_coreProj_mul_e_eq_zero, qY_e, Matrix.one_mulVec, Matrix.zero_mulVec, star_zero,
    zero_dotProduct, add_zero, zero_add, star_single, single_dotProduct]

theorem pair_e' (i : Fin ρ) (c : D.host.E) (y : Fin S.rank → D.host.E) :
    star (d.e' *ᵥ Pi.single i c) ⬝ᵥ (S.gram *ᵥ y) = star c * (d.qX *ᵥ y) i := by
  rw [pair_decomp d]
  simp only [Matrix.mulVec_mulVec, qX_e', wittZeroProjection_mul_dualBasis_eq_zero, qY_e', Matrix.one_mulVec, Matrix.zero_mulVec, star_zero,
    zero_dotProduct, add_zero, zero_add, star_single, single_dotProduct]

theorem pair_i₀ (x₀ : Fin S₀.rank → D.host.E) (y : Fin S.rank → D.host.E) :
    star (d.i₀ *ᵥ x₀) ⬝ᵥ (S.gram *ᵥ y) = star x₀ ⬝ᵥ (S₀.gram *ᵥ (d.q0 *ᵥ y)) := by
  rw [pair_decomp d]
  simp only [Matrix.mulVec_mulVec, qX_i₀, wittDecomposition_coreProj_mul_core_eq_one, qY_i₀, Matrix.one_mulVec, Matrix.zero_mulVec, star_zero,
    zero_dotProduct, add_zero, zero_add]

theorem decomp (y : Fin S.rank → D.host.E) : y = d.e *ᵥ (d.qX *ᵥ y) + d.i₀ *ᵥ (d.q0 *ᵥ y) + d.e' *ᵥ (d.qY *ᵥ y) := by
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Matrix.add_mulVec, ← Matrix.add_mulVec,
    d.sum_eq_one_rat, Matrix.one_mulVec]

theorem exists_ne_zero {𝔟 : FI D} (h : 𝔟 ≠ 0) : ∃ b ∈ 𝔟, b ≠ 0 := by
  by_contra hc
  push_neg at hc
  exact h (FractionalIdeal.eq_zero_iff.2 hc)

theorem exists_ne_zero_dualC (𝔟 : FI D) : ∃ c ∈ dualC 𝔟, c ≠ 0 := by
  obtain ⟨a, ha, hint⟩ := 𝔟.isFractional
  refine ⟨star (algebraMap (𝓞 D.host.E) D.host.E a), fun b hb => ?_, ?_⟩
  · obtain ⟨r, hr⟩ := hint b hb
    have : star b * star (algebraMap (𝓞 D.host.E) D.host.E a) = star (algebraMap (𝓞 D.host.E) D.host.E r) := by
      rw [hr, Algebra.smul_def, star_mul', mul_comm]
    rw [this]
    exact GlobalTheory.HypLattice.star_mem_int ⟨r, rfl⟩
  · rw [Ne, star_eq_zero]
    exact (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 D.host.E) D.host.E)).2 (nonZeroDivisors.ne_zero ha)

theorem dualC_le_span {𝔟 : FI D} (h : 𝔟 ≠ 0) : ∃ γ : D.host.E, dualC 𝔟 ≤ Submodule.span (𝓞 D.host.E) {γ} := by
  obtain ⟨β, hβ, hβ0⟩ := exists_ne_zero h
  refine ⟨(star β)⁻¹, fun c hc => ?_⟩
  obtain ⟨o, ho⟩ := hc β hβ
  have hs : star β ≠ 0 := by rwa [Ne, star_eq_zero]
  refine Submodule.mem_span_singleton.2 ⟨o, ?_⟩
  rw [Algebra.smul_def, ho, mul_comm (star β), mul_assoc, mul_inv_cancel₀ hs, mul_one]

theorem mulVec_single_smul {n : ℕ} (M : Matrix (Fin S.rank) (Fin n) D.host.E) (i : Fin n) {a b : D.host.E} (hb : b ≠ 0) :
    M *ᵥ Pi.single i a = (a * b⁻¹) • (M *ᵥ Pi.single i b) := by
  rw [← Matrix.mulVec_smul, ← Pi.single_smul', smul_eq_mul, mul_assoc, inv_mul_cancel₀ hb, mul_one]

variable {L₀ : Lat S₀} {𝔟 : ℕ → FI D}

theorem isLattice_splitL (h𝔟 : ∀ i, 𝔟 i ≠ 0) (hL₀ : Submodule.IsLattice D.host.E L₀) :
    Submodule.IsLattice D.host.E (splitL d L₀ 𝔟) := by
  choose γ hγ using fun i : Fin ρ => dualC_le_span (h𝔟 i)
  refine ⟨?_, ?_⟩
  · let T : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E) :=
      (⨆ i : Fin ρ, (𝔟 i : Submodule (𝓞 D.host.E) D.host.E).map
          ((LinearMap.toSpanSingleton D.host.E _ (d.e *ᵥ Pi.single i 1)).restrictScalars (𝓞 D.host.E))) ⊔
        L₀.map ((Matrix.mulVecLin d.i₀).restrictScalars (𝓞 D.host.E)) ⊔
        ⨆ i : Fin ρ, (Submodule.span (𝓞 D.host.E) {γ i}).map
          ((LinearMap.toSpanSingleton D.host.E _ (d.e' *ᵥ Pi.single i 1)).restrictScalars (𝓞 D.host.E))
    have hT : T.FG :=
      ((Submodule.fg_iSup _ fun i : Fin ρ => (FractionalIdeal.fg_of_isNoetherianRing le_rfl (𝔟 i)).map _).sup
        (hL₀.fg.map _)).sup (Submodule.fg_iSup _ fun i : Fin ρ => (Submodule.fg_span_singleton _).map _)
    refine hT.of_le fun y hy => ?_
    obtain ⟨h1, h2, h3⟩ := (mem_splitL d L₀ 𝔟 y).1 hy
    have hs : ∀ (M : Matrix (Fin S.rank) (Fin ρ) D.host.E) (w : Fin ρ → D.host.E), M *ᵥ w = ∑ i, w i • (M *ᵥ Pi.single i 1) := by
      intro M w
      conv_lhs => rw [← Finset.univ_sum_single w]
      rw [Matrix.mulVec_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Matrix.mulVec_smul, ← Pi.single_smul', smul_eq_mul, mul_one]
    rw [decomp d y, hs d.e, hs d.e']
    refine add_mem (add_mem (Submodule.mem_sup_left (Submodule.mem_sup_left ?_))
      (Submodule.mem_sup_left (Submodule.mem_sup_right ⟨_, h2, rfl⟩)))
      (Submodule.mem_sup_right ?_)
    · exact sum_mem fun i _ => Submodule.mem_iSup_of_mem i ⟨_, h1 i, rfl⟩
    · exact sum_mem fun i _ => Submodule.mem_iSup_of_mem i ⟨_, hγ i (h3 i), rfl⟩
  · intro s hs hli
    exact (LinearIndependent.iff_fractionRing _ _).mp hli
theorem isSelfDualC_splitL (h𝔟 : ∀ i, 𝔟 i ≠ 0) (hL₀ : IsSelfDualC S₀ L₀) : IsSelfDualC S (splitL d L₀ 𝔟) := by
  have hR : ∀ z : D.host.E, (∃ b : 𝓞 D.host.E, (b : D.host.E) = z) ↔ z ∈ (algebraMap (𝓞 D.host.E) D.host.E).range :=
    fun z => Iff.rfl
  have h0 : ∀ y₀ : Fin S₀.rank → D.host.E, y₀ ∈ L₀ ↔ ∀ x₀ ∈ L₀, star x₀ ⬝ᵥ (S₀.gram *ᵥ y₀) ∈
      (algebraMap (𝓞 D.host.E) D.host.E).range := fun y₀ => by
    rw [hL₀.2 y₀]
    simp only [hR, sum_pair_eq]
  refine ⟨isLattice_splitL d h𝔟 hL₀.1, fun y => ?_⟩
  simp only [hR, sum_pair_eq]
  constructor
  · intro hy x hx
    obtain ⟨hy1, hy2, hy3⟩ := (mem_splitL d L₀ 𝔟 y).1 hy
    obtain ⟨hx1, hx2, hx3⟩ := (mem_splitL d L₀ 𝔟 x).1 hx
    rw [pair_decomp]
    refine add_mem (add_mem (sum_mem fun i _ => ?_) ((h0 _).1 hy2 _ hx2)) (sum_mem fun i _ => ?_)
    · have := GlobalTheory.HypLattice.star_mem_int (hx3 i _ (hy1 i))
      rwa [star_mul', star_star, mul_comm] at this
    · exact hy3 i _ (hx1 i)
  · intro hy
    refine (mem_splitL d L₀ 𝔟 y).2 ⟨fun i => ?_, ?_, fun i => ?_⟩
    · have hi : 𝔟 i ≠ 0 := h𝔟 i
      rw [← inv_inv (𝔟 i), FractionalIdeal.mem_inv_iff (inv_ne_zero hi)]
      intro z hz
      have hc : star z ∈ dualC (𝔟 i) := fun b hb => by
        have := GlobalTheory.HypLattice.star_mem_int (GlobalTheory.HypLattice.mem_one_iff_range.1 ((FractionalIdeal.mem_inv_iff hi).1 hz b hb))
        rwa [star_mul', mul_comm] at this
      have := hy _ (e'_mem (single_mem_of_mem (I := fun j => dualC (𝔟 j)) i hc))
      rw [pair_e', star_star, mul_comm] at this
      exact GlobalTheory.HypLattice.mem_one_iff_range.2 this
    · rw [h0]
      intro x₀ hx₀
      have := hy _ (i₀_mem (d := d) (𝔟 := 𝔟) hx₀)
      rwa [pair_i₀] at this
    · intro b hb
      have := hy _ (e_mem (L₀ := L₀) (single_mem_of_mem (I := fun j => (𝔟 j : Submodule (𝓞 D.host.E) D.host.E)) i hb))
      rwa [pair_e] at this

end GlobalTheory.SeeSaw.SplitLat

namespace GlobalTheory.SeeSaw

end GlobalTheory.SeeSaw

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StepData GlobalTheory.SplitWeil ValuativeRel

noncomputable section

namespace GlobalTheory.LevGlue

theorem mem_levS_datY_single : ∀ (D : D7) (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (r t j : ℕ) (hr : r ≤ V.rank) (Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (P : Formalism.L2.DIV.LevelP Pg r ℂ) (χ : ℕ → ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ) (ξ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ) (PP : Formalism.L2.DIV.Pl D.host.E), PP ∈ Q → (∀ PP' ∈ Pg, (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP') ≠ (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)) → (∀ PP' ∈ Q, (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP') = (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) → PP' = PP) → ∀ (κ : GA D V), κ ∈ GfC V → (∀ PP' : Formalism.L2.DIV.Pl D.host.E, (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP') ≠ (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) → Lev.finE V κ ∈ Formalism.L2.DIV.St β → Formalism.L2.DIV.redFn β PP' (Lev.finE V κ) = 1) → (κ ∈ levS V β (Lev.datY V.rank r t j hr Pg Q P χ ξ Lev.Frm.B) ↔ Lev.finE V κ ∈ Formalism.L2.DIV.St β ∧ Formalism.L2.DIV.redFn β PP (Lev.finE V κ) ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blk2 r)) ∧ (Lev.finE V κ ∈ Formalism.L2.DIV.St β → Lev.levChi V β (Lev.datY V.rank r t j hr Pg Q P χ ξ Lev.Frm.B) κ = (((ξ PP (Formalism.L2.DIV.dBlk (Formalism.L2.DIV.blk2 r) 1 (Formalism.L2.DIV.redFn β PP (Lev.finE V κ))))⁻¹ : ℂˣ) : ℂ)) := by
  intro D V β r t j hr Pg Q P χ ξ PP hPQ hPg hQ κ hκ hoff
  have hPgoff : Lev.finE V κ ∈ Formalism.L2.DIV.St β → ∀ PP' ∈ Pg, Formalism.L2.DIV.redFn β PP' (Lev.finE V κ) = 1 :=
    fun hSt PP' hP => hoff PP' (hPg PP' hP) hSt
  have hQoff : Lev.finE V κ ∈ Formalism.L2.DIV.St β → ∀ PP' ∈ Q, PP' ≠ PP → Formalism.L2.DIV.redFn β PP' (Lev.finE V κ) = 1 :=
    fun hSt PP' hP hne => hoff PP' (fun e => hne (hQ PP' hP e)) hSt
  have hrt : Lev.finE V κ ∈ Formalism.L2.DIV.St β →
      Formalism.L2.DIV.rTup β (Lev.datY V.rank r t j hr Pg Q P χ ξ Lev.Frm.B) (Lev.finE V κ) = 1 := by
    intro hSt
    funext PP'
    show Formalism.L2.DIV.upperLeftBlock _ (Formalism.L2.DIV.redFn β PP'.1 _) = 1
    rw [hPgoff hSt _ PP'.2]
    exact Formalism.L2.DIV.blockDiagonalExtendByOnePrimeField_one _ _
  refine ⟨⟨fun h => ?_, fun ⟨hSt, hP⟩ => ?_⟩, fun hSt => ?_⟩
  · have h' : κ ∈ Lev.levG V β (Lev.datY V.rank r t j hr Pg Q P χ ξ Lev.Frm.B) := h
    rw [Lev.levG, Lev.levA, Subgroup.mem_inf, Subgroup.mem_comap, Formalism.L2.DIV.mem_lev, Formalism.L2.DIV.mem_parLev] at h'
    obtain ⟨_, ⟨_, hSt, _, hq⟩, _⟩ := h'
    exact ⟨hSt, hq PP hPQ⟩
  · show κ ∈ Lev.levG V β (Lev.datY V.rank r t j hr Pg Q P χ ξ Lev.Frm.B)
    rw [Lev.levG, Lev.levA, Subgroup.mem_inf, Subgroup.mem_comap, Formalism.L2.DIV.mem_lev, Formalism.L2.DIV.mem_parLev]
    refine ⟨hκ, ⟨GlobalTheory.LevSplit.finE_mem_UA _ _, hSt, ?_, ?_⟩, ?_⟩
    · intro PP' hP'
      rw [hPgoff hSt PP' hP']
      exact one_mem _
    · intro PP' hP'
      by_cases e : PP' = PP
      · rw [e]
        exact hP
      · rw [hQoff hSt PP' hP' e]
        exact one_mem _
    · rw [hrt hSt]
      exact one_mem _
  · simp only [Lev.levChi]
    congr 1
    simp only [Formalism.L2.DIV.levFn]
    rw [hrt hSt, Formalism.L2.DIV.blockDiagonalExtendByOnePrimeField_one, one_mul]
    rw [Finset.prod_eq_one (fun PP' hP' => Finset.prod_eq_one fun c _ => by
      rw [hPgoff hSt PP' hP', Formalism.L2.DIV.dBlk, Formalism.L2.DIV.blockDiagonalExtendByOnePrimeField_one, map_one]), one_mul]
    rw [Finset.prod_eq_single_of_mem (s := (Lev.datY V.rank r t j hr Pg Q P χ ξ Lev.Frm.B).Q) PP hPQ fun PP' hP hne => by
      rw [hQoff hSt PP' hP hne, Formalism.L2.DIV.dBlk, Formalism.L2.DIV.blockDiagonalExtendByOnePrimeField_one, map_one]]
    simp [Lev.datY]

end GlobalTheory.LevGlue

end
end
