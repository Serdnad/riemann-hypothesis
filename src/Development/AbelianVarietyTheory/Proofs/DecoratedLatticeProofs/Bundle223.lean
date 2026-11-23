module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.MemMulAAOfTrace
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle322
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemHomLatticeCompletionIffSupportedMaps
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle147
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsFlagDualMatrix
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsIntegralBasisOfLatticeAtPlaceStable
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualSplitComponentIsLatticeStabilizerEq
import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators
import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasWeil
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsPairingSingleNe
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle195
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle196
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Monotonicity.Lemmas
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
import Std.Tactic.BVDecide.Normalize.BitVec
import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.JointSmooth
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsGlOfEquiv
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.LatPair GlobalTheory.SeeSaw GlobalTheory.FinPl ValuativeRel
open scoped TensorProduct nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.HermLine

abbrev signLine (D : D7) (p q : ℕ) : HSp D :=
  Examples₂.stdSpace (E := D.host.E) Examples₂.star_isIntegral (p + q) (fun i => decide (p ≤ (i : ℕ))) p q

theorem signLine_norm (D : D7) (c : D.host.E) (p q : ℕ) (h : p + q = 1) :
    star (fun _ : Fin (signLine D p q).rank => c) ⬝ᵥ (signLine D p q).gram *ᵥ (fun _ : Fin (signLine D p q).rank => c) =
      (Examples₂.sgn (decide (p ≤ 0)) : D.host.E) * (c * star c) := by
  obtain ⟨i0, hi⟩ : ∃ i0 : Fin (p + q), (i0 : ℕ) = 0 := ⟨⟨0, by omega⟩, rfl⟩
  have huniq : ∀ i : Fin (p + q), i = i0 := fun i => Fin.ext (by omega)
  show ∑ i : Fin (p + q), star c * ∑ j : Fin (p + q), (signLine D p q).gram i j * c = _
  have hsum : ∀ f : Fin (p + q) → D.host.E, ∑ i, f i = f i0 := by
    intro f
    rw [Finset.sum_eq_single i0 (fun b _ hb => absurd (huniq b) hb) (by simp)]
  rw [hsum, hsum, Examples₂.stdSpace_gram_apply, if_pos rfl, hi]
  ring

theorem exists_line_vec (D : D7) (c : D.host.E) (ε : ℤˣ) (hc : c ≠ 0) :
    ∃ (L : HSp D) (ζ : Fin L.rank → D.host.E), IsLineVec L ζ ∧ L.SigOK ∧
      star ζ ⬝ᵥ L.gram *ᵥ ζ = ((ε : ℤ) : D.host.E) * (c * star c) ∧
      ∀ τ, L.sig τ = if ε = 1 then (1, 0) else (0, 1) := by
  have hcc : c * star c ≠ 0 := mul_ne_zero hc (star_ne_zero.2 hc)
  rcases Int.units_eq_one_or ε with rfl | rfl
  · have hn := signLine_norm D c 1 0 rfl
    simp only [Examples₂.sgn, zero_add, nonpos_iff_eq_zero, one_ne_zero, decide_false, Bool.false_eq_true,
      if_false, one_mul] at hn
    refine ⟨signLine D 1 0, fun _ => c, ⟨rfl, ?_⟩, GlobalTheory.Ker.Inhab.sigOK_std D 1 0, ?_, fun τ => ?_⟩
    · rw [hn]; exact hcc
    · rw [hn]; simp
    · simp; rfl
  · have hn := signLine_norm D c 0 1 rfl
    simp only [Examples₂.sgn, le_refl, decide_true, if_true] at hn
    refine ⟨signLine D 0 1, fun _ => c, ⟨rfl, ?_⟩, GlobalTheory.Ker.Inhab.sigOK_std D 0 1, ?_, fun τ => ?_⟩
    · rw [hn, neg_one_mul]; exact neg_ne_zero.2 hcc
    · rw [hn]; simp
    · rw [if_neg (by decide)]; rfl

end GlobalTheory.HermLine
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.BesSplit

theorem tens_ext {F E A B : Type} [Field F] [Field E] [Algebra F E] [CommRing A] [CommRing B] [Algebra F A]
    [Algebra F B] (z w : (A × B) ⊗[F] E)
    (h1 : Algebra.TensorProduct.map (AlgHom.fst F A B) (AlgHom.id F E) z =
      Algebra.TensorProduct.map (AlgHom.fst F A B) (AlgHom.id F E) w)
    (h2 : Algebra.TensorProduct.map (AlgHom.snd F A B) (AlgHom.id F E) z =
      Algebra.TensorProduct.map (AlgHom.snd F A B) (AlgHom.id F E) w) : z = w := by
  have hz : ∀ z : (A × B) ⊗[F] E, z = LinearMap.rTensor E (LinearMap.inl F A B)
        (Algebra.TensorProduct.map (AlgHom.fst F A B) (AlgHom.id F E) z) +
      LinearMap.rTensor E (LinearMap.inr F A B)
        (Algebra.TensorProduct.map (AlgHom.snd F A B) (AlgHom.id F E) z) := by
    intro z
    induction z with
    | tmul x y => simp [← TensorProduct.add_tmul]
    | add x y hx hy =>
      simp only [map_add (f := _)]
      rw [add_add_add_comm, ← hx, ← hy]
  rw [hz z, hz w, h1, h2]

theorem entry_eq {R R₁ R₂ : Type} [CommRing R] [CommRing R₁] [CommRing R₂] (φ : R →+* R₁) (ψ : R →+* R₂)
    (hinj : ∀ z w, φ z = φ w → ψ z = ψ w → z = w) {n k m : ℕ} {M N K : Matrix (Fin n) (Fin n) R}
    (hi : M.map φ = N.map φ) (hf : M.map ψ = K.map ψ) (P : Matrix (Fin k) (Fin n) R) (Q : Matrix (Fin n) (Fin m) R)
    (i : Fin k) (j : Fin m) {c : R} (hN : (P * (N * Q)) i j = c) (hK : (P * (K * Q)) i j = c) :
    (P * (M * Q)) i j = c := by
  refine hinj _ _ ?_ ?_
  · have e : (P * (M * Q)).map φ = (P * (N * Q)).map φ := by
      rw [Matrix.map_mul, Matrix.map_mul, Matrix.map_mul, Matrix.map_mul, hi]
    exact (congrFun (congrFun e i) j).trans (congrArg φ hN)
  · have e : (P * (M * Q)).map ψ = (P * (K * Q)).map ψ := by
      rw [Matrix.map_mul, Matrix.map_mul, Matrix.map_mul, Matrix.map_mul, hf]
    exact (congrFun (congrFun e i) j).trans (congrArg ψ hK)

theorem mat_eq {R R₁ R₂ : Type} [CommRing R] [CommRing R₁] [CommRing R₂] (φ : R →+* R₁) (ψ : R →+* R₂)
    (hinj : ∀ z w, φ z = φ w → ψ z = ψ w → z = w) {n k m : ℕ} {M N K : Matrix (Fin n) (Fin n) R}
    (hi : M.map φ = N.map φ) (hf : M.map ψ = K.map ψ) (P : Matrix (Fin k) (Fin n) R) (Q : Matrix (Fin n) (Fin m) R)
    {C : Matrix (Fin k) (Fin m) R} (hN : P * (N * Q) = C) (hK : P * (K * Q) = C) : P * (M * Q) = C :=
  Matrix.ext fun i j => entry_eq φ ψ hinj hi hf P Q i j (congrFun (congrFun hN i) j) (congrFun (congrFun hK i) j)

variable {D : D7}

def realPart (D : D7) : AE D →+* Ainf D.host.F ⊗[D.host.F] D.host.E :=
  (Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E)).toRingHom

def finitePart (D : D7) : AE D →+* Af D.host.F ⊗[D.host.F] D.host.E :=
  (Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E)).toRingHom

theorem ext_parts (z w : AE D) (h1 : realPart D z = realPart D w) (h2 : finitePart D z = finitePart D w) : z = w :=
  tens_ext (A := Ainf D.host.F) (B := Af D.host.F) z w h1 h2

theorem map_real_eq {S : HSp D} {x y : GA D S} (h : infHom S x = infHom S y) :
    (Formalism.L2.Theta.mt S x).map (realPart D) = (Formalism.L2.Theta.mt S y).map (realPart D) := congrArg Units.val h

theorem map_finite_eq {S : HSp D} {x y : GA D S} (h : finHom S x = finHom S y) :
    (Formalism.L2.Theta.mt S x).map (finitePart D) = (Formalism.L2.Theta.mt S y).map (finitePart D) := congrArg Units.val h



theorem mem_besGrp_of_parts {S S₀ A L : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (o : OrthDec S₀ A L) {x y z : GA D S}
    (hi : infHom S x = infHom S y) (hf : finHom S x = finHom S z) (hy : y ∈ besGrp d o) (hz : z ∈ besGrp d o) :
    x ∈ besGrp d o := by
  have key : ∀ g : GA D S, g ∈ besGrp d o ↔ g ∈ jacGrp d ∧
      HMul.hMul d.p0 (HMul.hMul (Formalism.L2.Theta.mt S g) (HMul.hMul d.j0 o.jB)) = o.jB := fun g => by
    have e := Set.ext_iff.1 (GlobalTheory.BesClosed.besGrp_eq_inter d o) g
    rw [← Matrix.mul_assoc (Formalism.L2.Theta.mt S g), ← Matrix.mul_assoc]
    exact e
  have hi' := map_real_eq hi
  have hf' := map_finite_eq hf
  obtain ⟨hy1, hy2⟩ := (key y).1 hy
  obtain ⟨hz1, hz2⟩ := (key z).1 hz
  obtain ⟨hy3, hy4, hy5⟩ := (GlobalTheory.BesClosed.mem_jacGrp_iff_mat d y).1 hy1
  obtain ⟨hz3, hz4, hz5⟩ := (GlobalTheory.BesClosed.mem_jacGrp_iff_mat d z).1 hz1
  refine (key x).2 ⟨(GlobalTheory.BesClosed.mem_jacGrp_iff_mat d x).2 ⟨?_, ?_, fun i j => ⟨fun hji => ?_, ?_⟩⟩, ?_⟩
  · exact mat_eq (realPart D) (finitePart D) ext_parts hi' hf' _ _ hy3 hz3
  · exact mat_eq (realPart D) (finitePart D) ext_parts hi' hf' _ _ hy4 hz4
  · exact entry_eq (realPart D) (finitePart D) ext_parts hi' hf' _ _ i j ((hy5 i j).1 hji) ((hz5 i j).1 hji)
  · exact entry_eq (realPart D) (finitePart D) ext_parts hi' hf' _ _ i i (hy5 i j).2 (hz5 i j).2
  · exact mat_eq (realPart D) (finitePart D) ext_parts hi' hf' _ _ hy2 hz2

theorem besGrp_split : ∀ (D : D7) (V V₀ A L : HSp D) (ρ : ℕ) (d : HypDec V V₀ ρ) (o : OrthDec V₀ A L),
    ∀ a ∈ GinfC V, ∀ b ∈ GfC V, a * b ∈ besGrp d o → a ∈ besGrp d o ∧ b ∈ besGrp d o := by
  intro D V V₀ A L ρ d o a ha b hb hab
  have ha' : finHom V a = 1 := MonoidHom.mem_ker.1 ha
  have hb' : infHom V b = 1 := MonoidHom.mem_ker.1 hb
  exact ⟨mem_besGrp_of_parts d o (by rw [map_mul, hb', mul_one]) (by rw [ha', map_one]) hab (one_mem _),
    mem_besGrp_of_parts d o (by rw [hb', map_one]) (by rw [map_mul, ha', one_mul]) (one_mem _) hab⟩

end GlobalTheory.BesSplit
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section



namespace GlobalTheory.FinPl.SelfDualCompl

open GlobalTheory.FinPlLoc

variable {D : D7}

theorem cA_tmul (a : AF D.host.F) (e : D.host.E) : cA D (a ⊗ₜ[D.host.F] e) = a ⊗ₜ[D.host.F] star e := by
  show Algebra.TensorProduct.map (AlgHom.id _ _) _ (a ⊗ₜ[D.host.F] e) = _
  rw [Algebra.TensorProduct.map_tmul]
  rfl

theorem incA_eq (e : D.host.E) : incA D e = (1 : AF D.host.F) ⊗ₜ[D.host.F] e := rfl

def hA (S : HSp D) (y s : Fin S.rank → AE D) : AE D :=
  ∑ i, ∑ j, cA D (s i) * incA D (HSpace.gram S i j) * y j

theorem intAt_zero (P : Pl D → Prop) : (0 : AE D) ∈ intAt D P :=
  ⟨zero_mem _, by rw [map_zero]; exact zero_mem _⟩

theorem intAt_add {P : Pl D → Prop} {a b : AE D} (ha : a ∈ intAt D P) (hb : b ∈ intAt D P) : a + b ∈ intAt D P :=
  ⟨add_mem ha.1 hb.1, by rw [map_add]; exact add_mem ha.2 hb.2⟩

theorem intAt_neg {P : Pl D → Prop} {a : AE D} (ha : a ∈ intAt D P) : -a ∈ intAt D P :=
  ⟨neg_mem ha.1, by rw [map_neg]; exact neg_mem ha.2⟩

theorem hA_zero_left (S : HSp D) (s : Fin S.rank → AE D) : hA S 0 s = 0 := by
  simp [hA]

theorem hA_add_left (S : HSp D) (y y' s : Fin S.rank → AE D) : hA S (y + y') s = hA S y s + hA S y' s := by
  simp [hA, mul_add, Finset.sum_add_distrib]

theorem hA_neg_left (S : HSp D) (y s : Fin S.rank → AE D) : hA S (-y) s = -hA S y s := by
  simp [hA, Finset.sum_neg_distrib]

theorem hA_zero_right (S : HSp D) (y : Fin S.rank → AE D) : hA S y 0 = 0 := by
  simp [hA]

theorem hA_add_right (S : HSp D) (y s s' : Fin S.rank → AE D) : hA S y (s + s') = hA S y s + hA S y s' := by
  simp [hA, add_mul, Finset.sum_add_distrib]

theorem hA_neg_right (S : HSp D) (y s : Fin S.rank → AE D) : hA S y (-s) = -hA S y s := by
  simp [hA, Finset.sum_neg_distrib]

theorem hA_gen (S : HSp D) (α β : Af D.host.F) (x x' : Fin S.rank → D.host.E) :
    hA S (fun j => pairA D.host.F 0 α ⊗ₜ[D.host.F] (1 * x j)) (fun i => pairA D.host.F 0 β ⊗ₜ[D.host.F] (1 * x' i)) =
      pairA D.host.F 0 (β * α) ⊗ₜ[D.host.F] (∑ i, ∑ j, star (x' i) * HSpace.gram S i j * x j) := by
  simp only [hA, cA_tmul, incA_eq, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul, ← TensorProduct.tmul_sum,
    pairA_mul]

theorem hA_mem {S : HSp D} {LS : Lat S} (hS : IsSelfDualC S LS) {P : Pl D → Prop} {y s : Fin S.rank → AE D}
    (hy : y ∈ latV S LS P) (hs : s ∈ latV S LS P) : hA S y s ∈ intAt D P := by
  induction hs using AddSubgroup.closure_induction with
  | mem s hs =>
    obtain ⟨β, hβi, hβ, a, ha, x', hx', rfl⟩ := hs
    rw [Set.mem_singleton_iff] at ha
    subst ha
    induction hy using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨α, hαi, hα, a, ha, x, hx, rfl⟩ := hy
      rw [Set.mem_singleton_iff] at ha
      subst ha
      rw [hA_gen]
      obtain ⟨c, hc⟩ := (hS.2 x).1 hx x' hx'
      rw [← hc]
      refine ⟨pair_mem_idAt P _ (fun v hv => by rw [map_mul, hα v hv, mul_zero]) _, ?_⟩
      rw [finPart_pair]
      exact AddSubgroup.subset_closure ⟨β * α, GlobalTheory.FinPl.LatMem.intAf_mul' hβi hαi, c, rfl⟩
    | zero => rw [hA_zero_left]; exact intAt_zero P
    | add y y' _ _ h h' => rw [hA_add_left]; exact intAt_add h h'
    | neg y _ h => rw [hA_neg_left]; exact intAt_neg h
  | zero => rw [hA_zero_right]; exact intAt_zero P
  | add s s' _ _ h h' => rw [hA_add_right]; exact intAt_add h h'
  | neg s _ h => rw [hA_neg_right]; exact intAt_neg h

theorem wachExpansion_smul_compatible {S : HSp D} {LS : Lat S} (P : Pl D → Prop) {s : Fin S.rank → D.host.E} (hs : s ∈ LS)
    {z : Af D.host.F ⊗[D.host.F] D.host.E} (hz : z ∈ intAE D) :
    (idem D P * finIn D z) • (fun l => incA D (s l)) ∈ latV S LS P := by
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, ha, o, rfl⟩ := hz
    refine AddSubgroup.subset_closure ⟨ePl D P * a, GlobalTheory.FinPl.LatMem.intAf_mul' (ePl_int P) ha,
      fun w hw => by rw [map_mul, evalV_ePl, if_neg hw, zero_mul], 1, rfl, o • s, LS.smul_mem o hs, ?_⟩
    funext l
    simp only [Pi.smul_apply, smul_eq_mul, idem, finIn_tmul, incA_eq, Algebra.TensorProduct.tmul_mul_tmul, pairA_mul,
      mul_one, one_mul]
    congr 1
  | zero => rw [map_zero, mul_zero, zero_smul]; exact zero_mem _
  | add z z' _ _ h h' => rw [map_add (f := _), mul_add, add_smul]; exact add_mem h h'
  | neg z _ h => rw [map_neg, mul_neg, neg_smul]; exact neg_mem h

theorem smul_mem {S : HSp D} {LS : Lat S} {P : Pl D → Prop} {c : AE D} (hc : c ∈ intAt D P) {s : Fin S.rank → D.host.E}
    (hs : s ∈ LS) : c • (fun l => incA D (s l)) ∈ latV S LS P := by
  have h1 : idem D P * c = c := (mem_idAt_iff P c).1 hc.1
  have h2 : c = finIn D (finPart D c) := eq_finIn (infPart_of_idAt hc.1)
  have := wachExpansion_smul_compatible P hs hc.2
  rwa [← h2, h1] at this

theorem cA_test (P : Pl D → Prop) (e : D.host.E) :
    cA D (pairA D.host.F 0 (ePl D P) ⊗ₜ[D.host.F] (1 * e)) = idem D P * incA D (star e) := by
  rw [cA_tmul, idem, incA_eq, Algebra.TensorProduct.tmul_mul_tmul, one_mul, one_mul, mul_one]

theorem selfDual_latV : ∀ (D : D7) (S : HSp D) (LS : Lat S), IsSelfDualC S LS → ∀ (P : Pl D → Prop)
    (y : Fin S.rank → AE D), (∀ r, y r ∈ idAt D P) →
    (y ∈ latV S LS P ↔ ∀ s ∈ latV S LS P, (∑ i, ∑ j, cA D (s i) * incA D (HSpace.gram S i j) * y j) ∈ intAt D P) := by
  intro D S LS hS P y hy
  refine ⟨fun h s hs => hA_mem hS h hs, fun h => ?_⟩
  obtain ⟨m, s, s', hs, hs', hdual⟩ := GlobalTheory.FinPl.LatMem.exists_dualBasis S hS
  let t : Fin m → Fin S.rank → AE D := fun i l => pairA D.host.F 0 (ePl D P) ⊗ₜ[D.host.F] (1 * s' i l)
  have ht : ∀ i, t i ∈ latV S LS P := fun i =>
    AddSubgroup.subset_closure ⟨ePl D P, ePl_int P, fun w hw => by rw [evalV_ePl, if_neg hw], 1, rfl, s' i, hs' i, rfl⟩
  have hyeq : y = ∑ i, hA S y (t i) • (fun a => incA D (s i a)) := by
    funext a
    have hya : y a = idem D P * y a := ((mem_idAt_iff P (y a)).1 (hy a)).symm
    have hsum : ∀ j, idem D P * y j * incA D (if a = j then 1 else 0) = if a = j then idem D P * y j else 0 := by
      intro j
      split_ifs <;> simp
    calc y a = ∑ j, idem D P * y j * incA D (if a = j then 1 else 0) := by
          rw [Finset.sum_congr rfl fun j _ => hsum j, Finset.sum_ite_eq, if_pos (Finset.mem_univ a)]
          exact hya
      _ = ∑ j, idem D P * y j * incA D (∑ i, s i a * ∑ k, star (s' i k) * HSpace.gram S k j) := by
          simp only [hdual]
      _ = _ := by

          simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hA, t, cA_test, map_sum, map_mul, Finset.mul_sum,
          Finset.sum_mul]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => ?_
          ring
  rw [hyeq]
  exact sum_mem fun i _ => smul_mem (h (t i) (ht i)) (hs i)

end GlobalTheory.FinPl.SelfDualCompl
end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.IwaPlace Matrix

namespace GlobalTheory.IwaFlag

variable {D : D7} {v : Pl D}

def intGrpAt (D : D7) (v : Pl D) : AddSubgroup (AE D) where
  carrier := intAt D (· = v)
  zero_mem' := ⟨zero_mem _, by rw [RingHom.map_zero]; exact zero_mem _⟩
  add_mem' := fun ha hb => ⟨add_mem ha.1 hb.1, by rw [RingHom.map_add (f := _)]; exact add_mem ha.2 hb.2⟩
  neg_mem' := fun ha => ⟨neg_mem ha.1, by rw [RingHom.map_neg]; exact neg_mem ha.2⟩

theorem mul_mem_intAt {a b : AE D} (ha : a ∈ intAt D (· = v)) (hb : b ∈ intAt D (· = v)) : a * b ∈ intAt D (· = v) :=
  ⟨Ideal.mul_mem_left _ _ hb.1, by rw [RingHom.map_mul]; exact FrameLat.mul_mem_intAE ha.2 hb.2⟩

theorem exists_nat_isIntegral (z : D.host.E) : ∃ n : ℕ, 0 < n ∧ IsIntegral ℤ ((n : D.host.E) * z) := by
  have hz : IsAlgebraic ℤ z := (IsFractionRing.isAlgebraic_iff ℤ ℚ D.host.E).2 (Algebra.IsAlgebraic.isAlgebraic z)
  obtain ⟨y, hy, h⟩ := hz.exists_integral_multiple
  refine ⟨y.natAbs, Int.natAbs_pos.2 hy, ?_⟩
  rw [zsmul_eq_mul] at h
  rw [← Int.cast_natCast]
  rcases Int.natAbs_eq y with e | e
  · rw [← e]; exact h
  · have e' : ((y.natAbs : ℕ) : ℤ) = -y := by omega
    rw [e', Int.cast_neg, neg_mul]; exact h.neg

theorem exists_nat_isIntegral_fin {ι : Type} [Fintype ι] (z : ι → D.host.E) :
    ∃ d : ℕ, 0 < d ∧ ∀ l, IsIntegral ℤ ((d : D.host.E) * z l) := by
  classical
  choose c hc hi using fun p : ι => exists_nat_isIntegral (z p)
  refine ⟨∏ p, c p, Finset.prod_pos fun p _ => hc p, fun l => ?_⟩
  rw [← Finset.prod_erase_mul Finset.univ c (Finset.mem_univ l), Nat.cast_mul, mul_assoc]
  refine IsIntegral.mul ?_ (hi l)
  rw [← Int.cast_natCast]
  exact isIntegral_algebraMap (R := ℤ)

theorem mul_incA_mem {ε : AE D} (hεI : ε ∈ intAt D (· = v)) {o : D.host.E} (ho : IsIntegral ℤ o) :
    ε * incA D o ∈ intAt D (· = v) := by
  have h : finPart D (incA D o) ∈ intAE D :=
    AddSubgroup.subset_closure ⟨1, fun w => by rw [map_one]; exact one_mem _, ⟨o, ho⟩, rfl⟩
  exact ⟨Ideal.mul_mem_right _ _ hεI.1, by rw [RingHom.map_mul]; exact FrameLat.mul_mem_intAE hεI.2 h⟩

theorem princ_intGrpAt {ε : AE D} (hεε : ε * ε = ε) (hεc : cA D ε = ε) (hεI : ε ∈ intAt D (· = v))
    (hε : ∀ a, a ∈ idAt D (· = v) ↔ ε * a = a) (ht : Tame D v) : Princ ε (intGrpAt D v) := by
  rintro J h1 h2 ⟨m, hm, h3⟩ ⟨N, hN, h4⟩
  obtain ⟨β, β', g1, g2, g3, g4, g5⟩ := GlobalTheory.IwaPlace.FreeAt.exists_basis D 1 v ε (J.comap (Pi.evalAddMonoidHom (fun _ : Fin 1 => AE D) 0))
    ht hεε hεc hεI hε
    (fun y hy i => by rw [Subsingleton.elim i 0]; exact (hε _).2 (h1 _ hy))
    (fun a ha y hy => h2 a ha _ hy)
    ⟨m, hm, fun y hy => by
      have := h2 _ (hy 0) _ h3
      rw [mul_left_comm, mul_comm (y 0), (hε _).1 (hy 0).1] at this
      exact this⟩
    ⟨N, hN, fun y hy i => by rw [Subsingleton.elim i 0]; exact h4 _ hy⟩
  have e3 : β 0 0 * β' 0 0 = ε := by
    have := congrFun (congrFun g3 0) 0
    rwa [Matrix.mul_apply, Fin.sum_univ_one, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one] at this
  have ev : ∀ (a : AE D) (i : Fin 1), (β' *ᵥ fun _ => a) i = β' 0 0 * a := fun a i => by
    rw [Subsingleton.elim i 0, Matrix.mulVec, dotProduct, Fin.sum_univ_one]
  refine ⟨β 0 0, (g5 (fun _ => β 0 0) fun _ => g1 0 0).2 fun i => ?_, β' 0 0, (hε _).1 (g2 0 0), e3, fun a ha => ?_⟩
  · rw [ev, mul_comm, e3]; exact hεI
  · have := (g5 (fun _ => a) fun _ => (hε _).2 (h1 a ha)).1 ha 0
    rw [ev] at this
    exact this

theorem exists_flag_basis : ∀ (D : D7) (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (v : Pl D) (ε : AE D) (hεε : ε * ε = ε) (hεc : cA D ε = ε) (hεI : ε ∈ intAt D (· = v)) (hε : ∀ a, a ∈ idAt D (· = v) ↔ ε * a = a), Tame D v → ∀ M : AddSubgroup (Fin S.rank → AE D), IsSDAt S v M → ∃ b : Mx D ρ ρ, (∀ i j, j < i → b i j = 0) ∧ (∀ i j, b i j ∈ idAt D (· = v)) ∧ (∀ i, (fun k => (d.jX ⬝ b) k i) ∈ M) ∧ ∃ c' : Mx D S.rank ρ, (∀ i, (fun k => c' k i) ∈ M) ∧ adj c' ⬝ (gA S ⬝ (d.jX ⬝ b)) = ε • (1 : Mx D ρ ρ) := by
  intro D S S₀ ρ d v ε hεε hεc hεI hε ht M ⟨hsupp, ⟨m, hm, hmul⟩, hdual⟩
  obtain ⟨K, hK, hint⟩ := exists_nat_isIntegral_fin
    (Sum.elim (fun p : Fin S.rank × Fin ρ => d.e p.1 p.2) (fun p : Fin S.rank × Fin ρ => d.e' p.1 p.2))
  have hcol : ∀ z : Fin S.rank → D.host.E, (∀ l, IsIntegral ℤ ((K : D.host.E) * z l)) →
      (fun l => ((m * K : ℕ) : AE D) * ε * incA D (z l)) ∈ M := fun z hz => by
    have e : (fun l => ((m * K : ℕ) : AE D) * ε * incA D (z l)) =
        (m : AE D) • fun l => ε * incA D ((K : D.host.E) * z l) := by
      funext l
      rw [Pi.smul_apply, smul_eq_mul, RingHom.map_mul, map_natCast, Nat.cast_mul]
      ring
    rw [e]
    exact hmul _ fun l => mul_incA_mem hεI (hz l)
  obtain ⟨b, h1, h2, h3, c', h4, h5⟩ := exists_flag_dual_matrix (c := cA D) (O := intGrpAt D v) (M := M) (gA S)
    cA_cA hεε hεc hεI (fun a ha => (hε a).1 ha.1) (fun a ha b hb => mul_mem_intAt ha hb)
    (fun a ha => ⟨(hε _).2 (by rw [← hεc, ← RingHom.map_mul, (hε a).1 ha.1]), (FrameLat.cA_int_iff a).2 ha.2⟩)
    (princ_intGrpAt hεε hεc hεI hε ht) (fun y hy i => (hε _).1 (hsupp y hy i))
    (fun y hy => hdual y fun i => (hε _).2 (hy i)) d.jX d.jY d.gram_YX (m * K) (Nat.mul_pos hm hK)
    (fun k => hcol (fun l => d.e l k) fun l => hint (Sum.inl (l, k)))
    (fun k => hcol (fun l => d.e' l k) fun l => hint (Sum.inr (l, k)))
  exact ⟨b, h1, fun i j => (hε _).2 (h2 i j), h3, c', h4, h5⟩

end GlobalTheory.IwaFlag

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep
open GlobalTheory.FinZeta (Gv embV Kv VacFin IsLocKer KerU)
open GlobalTheory.SphTheta (IsStd CayleyRule intMat liftPar)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke IsCommensurated Tj SatU ordL Ov)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.order_det_one_add_of_integral_inverse_unitary : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q : ℕ), IsUnramInv ϖ σ q → ∀ (n : ℕ) (g t : GU σ n) (d : Fin n → ℤ), t.1.1 = Matrix.diagonal (fun i => ϖ ^ d i) → ∀ k₁ ∈ KU σ n, ∀ k₂ ∈ KU σ n, g⁻¹ = k₁ * t * k₂ → (1 + g.1.1).det ≠ 0 → (1 + g.1.1)⁻¹ ∈ intMat L (Fin n) (Fin n) → ordL (1 + g.1.1).det = -∑ i, max (d i) 0 := by
  first | exact @GlobalTheory.ChainOnto.ordL_det_one_add_of_inv_int | exact GlobalTheory.ChainOnto.ordL_det_one_add_of_inv_int | (intros; apply GlobalTheory.ChainOnto.ordL_det_one_add_of_inv_int <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep
open GlobalTheory.FinZeta (Gv embV Kv VacFin IsLocKer KerU)
open GlobalTheory.SphTheta (IsStd CayleyRule intMat liftPar)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke IsCommensurated Tj SatU ordL Ov)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.thetaKernel_mul_conj_cuspForm_integrableOn : GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → ∀ θ : InfFam D, IsInfFam θ → ∀ (ν : Measure (GA D S)) (𝓕 : Set (GA D S)), ν.IsHaarMeasure → IsFundamentalDomain (GQ S) 𝓕 ν → ∀ (u : WO S T → ℂ) (y : GA D S → ℂ), IsThetaFunO ψ S T u → IsAutFunSm θ S y → IsCuspFun S y → ∀ (a : GA D S) (x : GA D T), IntegrableOn (fun g => thetaKO om g x u * conj (y (g * a))) 𝓕 ν := by
  first | exact @GlobalTheory.ChainOnto.ThetaFirstVar.thetaKO_mul_conj_integrableOn | exact GlobalTheory.ChainOnto.ThetaFirstVar.thetaKO_mul_conj_integrableOn | (intros; apply GlobalTheory.ChainOnto.ThetaFirstVar.thetaKO_mul_conj_integrableOn <;> assumption)
end
