module

public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.MapsExist
import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasWeil
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle093
public import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.LocalBaseChange.StrictDominanceCasselman.IsStrictlyDominant
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle391
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle375
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle474
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle382
public import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle008
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsCompactStandardMaximal
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Dynamics.Ergodic.Action.Regular
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.Bundle001

@[expose] public section

section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.FJE

variable {D : D7} {n ρ p : ℕ} {hn : ρ + p = n}

abbrev rt (ξ : Matrix (Fin ρ) (Fin p) D.host.E) : Mx D ρ p := ξ.map (incA D)

def chv (ψ : AddChar (AF D.host.F) ℂ) (b₀ : HermE D ρ) (x y : Mx D ρ p) : ℂ :=
  ψ (trA (Matrix.trace (pr b₀ x y)))

def jc (y x : Mx D ρ p) : hermA D ρ :=
  ⟨(HMul.hMul y (adj x) : Mx D ρ ρ) + (HMul.hMul x (adj y) : Mx D ρ ρ), by
    have key : ∀ a b : Mx D ρ p, adj (HMul.hMul a (adj b) : Mx D ρ ρ) = (HMul.hMul b (adj a) : Mx D ρ ρ) := by
      intro a b
      ext i j

      simp only [adj, Matrix.transpose_apply, Matrix.map_apply, Matrix.mul_apply, map_sum, map_mul,
      Formalism.L2.Theta.cA_cA]
      exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
    show adj _ = _
    have : adj ((HMul.hMul y (adj x) : Mx D ρ ρ) + (HMul.hMul x (adj y) : Mx D ρ ρ)) = adj (HMul.hMul y (adj x) : Mx D ρ ρ) + adj (HMul.hMul x (adj y) : Mx D ρ ρ) := by
      ext i j
      simp only [adj, Matrix.transpose_apply, Matrix.map_apply, Matrix.add_apply, map_add (f := _)]
    rw [this, key, key, add_comm]⟩

def dsum (ψ : AddChar (AF D.host.F) ℂ) (b₀ : HermE D ρ) (Φ : Mx D ρ p → ℂ) (x y : Mx D ρ p) : ℂ :=
  ∑' ξ : Matrix (Fin ρ) (Fin p) D.host.E, chv ψ b₀ x (rt ξ) * Φ (rt ξ + y)

def Ap (ψ : AddChar (AF D.host.F) ℂ) (b₀ : HermE D ρ) (Φ φ : Mx D ρ p → ℂ) (v : Mx D ρ p × Mx D ρ p) : ℂ :=
  dsum ψ b₀ Φ v.2 v.1 * conj (dsum ψ b₀ φ v.2 v.1)

theorem th_zero (ψ : AddChar (AF D.host.F) ℂ) (b₀ : HermE D ρ) (φ : Mx D ρ p → ℂ) (x y : Mx D ρ p) :
    th ψ b₀ φ 0 x y = dsum ψ b₀ φ x y := by
  have h0 : chz ψ b₀ (0 : hermA D ρ) = 1 := by
    have : (Matrix.trace (HMul.hMul (b₀.1.map (incA D)) (0 : hermA D ρ).1 : Mx D ρ ρ)) = 0 := by
      simp
    rw [chz, this]
    simp [halfTr, trA]
  rw [th, h0, one_mul]
  rfl

theorem tsum_meas {ι X : Type} [Countable ι] [MeasurableSpace X] {f : ι → X → ℂ}
    (hf : ∀ i, StronglyMeasurable (f i)) (hs : ∀ a, Summable fun i => f i a) :
    StronglyMeasurable fun a => ∑' i, f i a := by
  refine stronglyMeasurable_of_tendsto (u := (atTop : Filter (Finset ι)))
    (f := fun (s : Finset ι) a => ∑ i ∈ s, f i a) (fun s => ?_) ?_
  · exact Finset.stronglyMeasurable_fun_sum _ fun i _ => hf i
  · exact tendsto_pi_nhds.2 fun a => (hs a).hasSum

end GlobalTheory.CompanionTheory.FJE
end
end

section

noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.StdUnn GlobalTheory.StdUnn.Model PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.PcFc

variable {D : D7} {n ρ p : ℕ}

theorem adj_bl (hn : ρ + p = n) (a : Mx D ρ ρ) (b : Mx D ρ p) (c : Mx D p ρ) (d : Mx D p p) :
    adj (bl hn a b c d : Mx D n n) = bl hn (adj a) (adj c) (adj b) (adj d) := by
  ext i j
  simp only [adj, bl, Matrix.transpose_apply, Matrix.map_apply, Matrix.submatrix_apply]
  rcases h1 : (finSumFinEquiv.trans (finCongr hn)).symm i with i' | i' <;>
    rcases h2 : (finSumFinEquiv.trans (finCongr hn)).symm j with j' | j' <;> rfl

def bT (hn : ρ + p = n) (z : hermA D ρ) (x : Mx D ρ p) (y : hermA D p) : hermA D n :=
  ⟨bl hn z.1 x (adj x) y.1, by
    show adj (bl hn z.1 x (adj x) y.1 : Mx D n n) = _
    rw [adj_bl, adj_adj]
    have hz : adj z.1 = z.1 := z.2
    have hy : adj y.1 = y.1 := y.2
    rw [hz, hy]⟩

def dsum (hn : ρ + p = n) (b₀ : HermE D ρ) (β' : HermE D p) : HermE D n :=
  ⟨bl hn b₀.1 0 0 β'.1, by
    have h1 := b₀.2
    have h2 := β'.2
    refine Matrix.ext fun i j => ?_
    simp only [bl, Matrix.transpose_apply, Matrix.map_apply, Matrix.submatrix_apply]
    rcases h1' : (finSumFinEquiv.trans (finCongr hn)).symm i with i' | i' <;>
      rcases h2' : (finSumFinEquiv.trans (finCongr hn)).symm j with j' | j' <;>
      simp only [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂,
        Matrix.zero_apply, map_zero]
    · exact congrFun (congrFun h1 i') j'
    · exact congrFun (congrFun h2 i') j'⟩

def cg (a : GL (Fin n) D.host.E) (β : HermE D n) : HermE D n :=
  ⟨(a.1.map (D.sp.cm.sig : D.host.E → D.host.E)).transpose * β.1 * a.1, by
    have h : ∀ M : Matrix (Fin n) (Fin n) D.host.E, (M.map (D.sp.cm.sig : D.host.E → D.host.E)).transpose = Mᴴ := fun _ => rfl
    have hb : β.1ᴴ = β.1 := β.2
    rw [h, h, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hb, Matrix.mul_assoc]⟩

def IsPer (Φ : hermA D n → ℂ) : Prop := ∀ γ ∈ ratHerm D n, ∀ x, Φ (γ + x) = Φ x

def chn (ψ : AddChar (AF D.host.F) ℂ) (β : HermE D n) (b : hermA D n) : ℂ :=
  ψ (-halfTr (Matrix.trace (HMul.hMul (β.1.map (incA D)) b.1 : Mx D n n)))

def pm (hn : ρ + p = n) (m : Meas D ρ p) (ψ : AddChar (AF D.host.F) ℂ) (b₀ : HermE D ρ) (Φ : hermA D n → ℂ) (y : hermA D p) : ℂ :=
  ∫ x in m.𝓕, ∫ z in m.𝓖, Φ (bT hn z x y) * conj (chz ψ b₀ z) ∂m.lz ∂m.μ

end GlobalTheory.CompanionTheory.PcFc

namespace GlobalTheory.CompanionTheory.PcFc

section Transport
variable {A B : Type} [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A] [T2Space A] [LocallyCompactSpace A]
  [SecondCountableTopology A] [MeasurableSpace A] [BorelSpace A]
  [AddCommGroup B] [TopologicalSpace B] [IsTopologicalAddGroup B] [T2Space B] [LocallyCompactSpace B]
  [SecondCountableTopology B] [MeasurableSpace B] [BorelSpace B]

theorem mean_transport (Γ : AddSubgroup A) (Δ : AddSubgroup B) [Countable Γ] [Countable Δ] (T : A ≃ₜ+ B)
    (hT : ∀ a, T a ∈ Δ ↔ a ∈ Γ) (μ : Measure A) (ν : Measure B) [μ.IsAddHaarMeasure] [ν.IsAddHaarMeasure]
    {s : Set A} {t : Set B} (hs : IsAddFundamentalDomain Γ s μ) (ht : IsAddFundamentalDomain Δ t ν) (hs1 : μ s = 1) (ht1 : ν t = 1)
    (f : B → ℂ) (hf : ∀ γ ∈ Δ, ∀ x, f (γ + x) = f x) :
    ∫ a in s, f (T a) ∂μ = ∫ b in t, f b ∂ν := by
  have hm : Measurable T := T.continuous.measurable
  have hAC : (μ.map T).IsAddHaarMeasure := ContinuousAddEquiv.isAddHaarMeasure_map μ T
  have hAC2 : (ν.map T.symm).IsAddHaarMeasure := ContinuousAddEquiv.isAddHaarMeasure_map ν T.symm
  have hsm : Measure.QuasiMeasurePreserving (T.symm.toAddEquiv.toEquiv) ν μ :=
    ⟨T.symm.continuous.measurable.aemeasurable, Measure.absolutelyContinuous_isAddHaarMeasure _ _⟩
  let eΓ : Δ ≃ Γ :=
    { toFun := fun d => ⟨T.symm d.1, (hT _).1 (by simpa using d.2)⟩
      invFun := fun c => ⟨T c.1, (hT _).2 c.2⟩
      left_inv := fun d => Subtype.ext (by simp)
      right_inv := fun c => Subtype.ext (by simp) }
  have hFD : IsAddFundamentalDomain Δ (T.toAddEquiv.toEquiv '' s) ν :=
    hs.image_of_equiv T.toAddEquiv.toEquiv hsm eΓ (fun g x => by
      show T (T.symm g.1 + x) = g.1 + T x
      simp)
  have h1 : ν (T.toAddEquiv.toEquiv '' s) = 1 := by rw [hFD.measure_eq ht, ht1]
  have hemb : MeasurableEmbedding T := T.toHomeomorph.measurableEmbedding
  have h2 : μ.map T (T.toAddEquiv.toEquiv '' s) = 1 := by
    rw [hemb.map_apply, show T ⁻¹' (T.toAddEquiv.toEquiv '' s) = s from Set.preimage_image_eq _ T.injective, hs1]
  have h3 : μ.map T = ν := by
    have h4 := Measure.isAddLeftInvariant_eq_smul (μ.map T) ν
    rw [h4] at h2
    have hc : Measure.addHaarScalarFactor (μ.map T) ν = 1 := by
      rw [Measure.smul_apply, h1, ENNReal.smul_def, smul_eq_mul, mul_one] at h2
      exact_mod_cast h2
    rw [h4, hc, one_smul]
  have h5 : ∫ a in s, f (T a) ∂μ = ∫ b in T.toAddEquiv.toEquiv '' s, f b ∂ν := by
    rw [← h3, hemb.setIntegral_map, show T ⁻¹' (T.toAddEquiv.toEquiv '' s) = s from Set.preimage_image_eq _ T.injective]
  rw [h5]
  exact hFD.setIntegral_eq ht (fun g x => hf g.1 g.2 x)
end Transport
end GlobalTheory.CompanionTheory.PcFc
end
end

section

noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.FJLim

theorem fj_tendsto : PcBound → ∀ (D : D7) (n ρ p : ℕ) (hn : ρ + p = n) (M : Maps D hn) (m : Meas D ρ p) (ψ : AddChar (AF D.host.F) ℂ), IsCharAF D.host.F ψ → ∀ (b₀ : HermE D ρ) {ι : Type} (l : Filter ι) (Fs : ι → G D n → ℂ) (A : G D n → ℂ), Continuous A → LeftInv (GF D n) A → (∀ᶠ i in l, Continuous (Fs i) ∧ LeftInv (GF D n) (Fs i)) → (∀ C : Set (G D n), IsCompact C → ∀ ε : ℝ, 0 < ε → ∀ᶠ i in l, ∀ c ∈ C, ‖Fs i c - A c‖ ≤ ε) → (∀ᶠ i in l, ∀ (y : Mx D ρ p) (g : G D n), pc M m ψ b₀ (Fs i - A) (M.sh y * g) = pc M m ψ b₀ (Fs i) (M.sh y * g) - pc M m ψ b₀ A (M.sh y * g)) → ∀ (g : G D n) (φ : Mx D ρ p → ℂ), Integrable φ m.μ → Tendsto (fun i => FJ M m ψ b₀ (Fs i) g φ) l (𝓝 (FJ M m ψ b₀ A g φ)) := by
  intro hPc D n ρ p hn M m ψ hψ b₀ ι l Fs A hAc hAinv hFs hunif hadd g φ hφ
  haveI : BorelSpace (Mx D ρ p) := ⟨rfl⟩
  obtain ⟨hcont, hbd⟩ := hPc D n ρ p hn M m ψ hψ b₀
  obtain ⟨C, hC, -, hCb⟩ := hbd g
  have hφc : Integrable (fun y => conj (φ y)) m.μ := Complex.conjCLE.toContinuousLinearMap.integrable_comp hφ
  have hint : ∀ F : G D n → ℂ, Continuous F → LeftInv (GF D n) F →
      Integrable (fun y => pc M m ψ b₀ F (M.sh y * g) * conj (φ y)) m.μ := by
    intro F hF hinv
    obtain ⟨B, hB⟩ := hC.exists_bound_of_continuousOn hF.continuousOn
    have hc : Continuous fun y => pc M m ψ b₀ F (M.sh y * g) :=
      (hcont F hF hinv).comp (M.sh_cont.mul continuous_const)
    exact hφc.bdd_mul hc.aestronglyMeasurable (Eventually.of_forall fun y => hCb F hF hinv B hB y)
  rw [Metric.tendsto_nhds]
  intro ε hε
  set N : ℝ := ∫ y, ‖φ y‖ ∂m.μ with hN
  have hN0 : 0 ≤ N := integral_nonneg fun _ => norm_nonneg _
  have hδ : 0 < ε / (N + 1) := by positivity
  filter_upwards [hFs, hadd, hunif C hC _ hδ] with i hi hai hui
  have hsub : Continuous (Fs i - A) := hi.1.sub hAc
  have hsinv : LeftInv (GF D n) (Fs i - A) := fun γ hγ x => by
    simp only [Pi.sub_apply, hi.2 γ hγ x, hAinv γ hγ x]
  have hpt : ∀ y, ‖pc M m ψ b₀ (Fs i) (M.sh y * g) - pc M m ψ b₀ A (M.sh y * g)‖ ≤ ε / (N + 1) := by
    intro y
    rw [← hai y g]
    exact hCb _ hsub hsinv _ (fun c hc => by simpa using hui c hc) y
  have hdiff : FJ M m ψ b₀ (Fs i) g φ - FJ M m ψ b₀ A g φ =
      ∫ y, (pc M m ψ b₀ (Fs i) (M.sh y * g) - pc M m ψ b₀ A (M.sh y * g)) * conj (φ y) ∂m.μ := by
    unfold FJ
    rw [← integral_sub (hint _ hi.1 hi.2) (hint _ hAc hAinv)]
    simp only [sub_mul]
  have hle : ‖FJ M m ψ b₀ (Fs i) g φ - FJ M m ψ b₀ A g φ‖ ≤ ε / (N + 1) * N := by
    rw [hdiff, hN, ← integral_const_mul]
    refine norm_integral_le_of_norm_le (hφ.norm.const_mul _) (Eventually.of_forall fun y => ?_)
    rw [norm_mul, RCLike.norm_conj]
    exact mul_le_mul_of_nonneg_right (hpt y) (norm_nonneg _)
  rw [dist_eq_norm]
  refine lt_of_le_of_lt hle ?_
  rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
  nlinarith

end GlobalTheory.CompanionTheory.FJLim
end
end

section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.PcZero

theorem blockMatrix_zero {R : Type} [Zero R] {p : ℕ} (hn : 0 + p = p) (a : Matrix (Fin 0) (Fin 0) R)
    (b : Matrix (Fin 0) (Fin p) R) (c : Matrix (Fin p) (Fin 0) R) : bl hn a b c 0 = 0 := by
  ext i j
  obtain ⟨i, rfl⟩ := (finSumFinEquiv.trans (finCongr hn)).surjective i
  obtain ⟨j, rfl⟩ := (finSumFinEquiv.trans (finCongr hn)).surjective j
  rcases i with i | i
  · exact i.elim0
  rcases j with j | j
  · exact j.elim0
  simp only [bl, Matrix.submatrix_apply, Equiv.symm_apply_apply, Matrix.fromBlocks_apply₂₂, Matrix.zero_apply]

theorem nzx_eq_one {D : D7} {p : ℕ} {hn : 0 + p = p} (M : Maps D hn) (z : hermA D 0) (x : Mx D 0 p) :
    M.nzx z x = 1 := by
  apply Subtype.ext
  apply Units.ext
  have h : mat (M.nzx z x) = 1 := by
    rw [M.nzx_mat, blockMatrix_zero]
    unfold blk4
    rw [Matrix.fromBlocks_one, Matrix.submatrix_one_equiv]
  exact h

theorem chz_eq_one {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (b₀ : HermE D 0) (z : hermA D 0) : chz ψ b₀ z = 1 := by
  unfold chz halfTr trA
  simp [Matrix.trace]

theorem zc_eq {D : D7} {p : ℕ} {hn : 0 + p = p} (M : Maps D hn) (m : Meas D 0 p) (ψ : AddChar (AF D.host.F) ℂ)
    (b₀ : HermE D 0) (F : G D p → ℂ) (g : G D p) : zc M m ψ b₀ F g = F g := by
  unfold zc
  simp only [nzx_eq_one, chz_eq_one, one_mul, map_one, mul_one]
  rw [setIntegral_const, Measure.real, m.hz.2.2]
  simp

theorem pc_eq : ∀ (D : D7) (p : ℕ) (hn : 0 + p = p) (M : Maps D hn) (m : Meas D 0 p) (ψ : AddChar (AF D.host.F) ℂ)
    (b₀ : HermE D 0) (F : G D p → ℂ) (g : G D p), pc M m ψ b₀ F g = F g := by
  intro D p hn M m ψ b₀ F g
  unfold PositivityTheory.Rg.Rsw.pc
  simp only [zc_eq, nzx_eq_one, one_mul]
  rw [setIntegral_const, Measure.real, m.hμ.2.2]
  simp

end GlobalTheory.CompanionTheory.PcZero

end
end

section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.FamMajorant

theorem fam_majorant : ∀ (D : D7) (n : ℕ) (H : G D n → ℝ≥0), IsHt H → (∃ C : Set (G D n), IsCompact C ∧ ∀ g, ∃ q ∈ P D n, ∃ c ∈ C, g = q * c) →
    ∀ (χ : (AE D)ˣ →* Circle) (s₁ : ℂ) (φ : G D n → ℂ), Continuous φ → IsLaw χ s₁ φ →
      ∃ B : ℝ, 0 ≤ B ∧ ∀ (z : ℂ) (g : G D n), ‖fam H φ s₁ z g‖ ≤ B * (H g : ℝ) ^ (z.re + (n : ℝ) / 2) := by
  rintro D n H hH ⟨C, hC, hcov⟩ χ s₁ φ hφ hlaw
  have hHpos : ∀ g, 0 < (H g : ℝ) := fun g => NNReal.coe_pos.2 (hH.2.1 g)
  have hpos : ∀ g, 0 < (H g : ℝ) ^ (s₁.re + (n : ℝ) / 2) := fun g => Real.rpow_pos_of_pos (hHpos g) _
  have hcont : Continuous fun g => ‖φ g‖ / (H g : ℝ) ^ (s₁.re + (n : ℝ) / 2) :=
    hφ.norm.div ((NNReal.continuous_coe.comp hH.1).rpow_const fun g => Or.inl (hHpos g).ne') fun g => (hpos g).ne'
  obtain ⟨δ, hδ⟩ := hC.exists_bound_of_continuousOn hcont.continuousOn
  have hB0 : 0 ≤ max δ 0 := le_max_right _ _
  have hon : ∀ c ∈ C, ‖φ c‖ ≤ max δ 0 * (H c : ℝ) ^ (s₁.re + (n : ℝ) / 2) := by
    intro c hc
    have h1 := (hδ c hc).trans (le_max_left δ 0)
    rwa [Real.norm_of_nonneg (div_nonneg (norm_nonneg _) (hpos c).le), div_le_iff₀ (hpos c)] at h1
  have hall : ∀ g, ‖φ g‖ ≤ max δ 0 * (H g : ℝ) ^ (s₁.re + (n : ℝ) / 2) := by
    intro g
    obtain ⟨q, hq, c, hc, rfl⟩ := hcov g
    obtain ⟨a, ha⟩ := GlobalTheory.StdUnn.LeftInvSect.exists_blkA hq
    have hr : 0 < absA D (Matrix.GeneralLinearGroup.det a) := hom_pos _ _
    rw [hlaw q hq a ha c, hH.2.2 q hq a ha c]
    have e1 : ‖npow (absA D (Matrix.GeneralLinearGroup.det a)) (s₁ + (n : ℂ) / 2)‖ =
        (absA D (Matrix.GeneralLinearGroup.det a) : ℝ) ^ (s₁.re + (n : ℝ) / 2) := by
      rw [norm_npow hr]; congr 1; simp
    have e2 : ((absA D (Matrix.GeneralLinearGroup.det a) * H c : ℝ≥0) : ℝ) ^ (s₁.re + (n : ℝ) / 2) =
        (absA D (Matrix.GeneralLinearGroup.det a) : ℝ) ^ (s₁.re + (n : ℝ) / 2) * (H c : ℝ) ^ (s₁.re + (n : ℝ) / 2) := by
      rw [NNReal.coe_mul, Real.mul_rpow (NNReal.coe_nonneg _) (NNReal.coe_nonneg _)]
    rw [e2, norm_mul, norm_mul, e1]
    simp only [Circle.norm_coe, one_mul]
    have h0 : 0 ≤ (absA D (Matrix.GeneralLinearGroup.det a) : ℝ) ^ (s₁.re + (n : ℝ) / 2) :=
      Real.rpow_nonneg (NNReal.coe_nonneg _) _
    calc _ ≤ (absA D (Matrix.GeneralLinearGroup.det a) : ℝ) ^ (s₁.re + (n : ℝ) / 2) *
          (max δ 0 * (H c : ℝ) ^ (s₁.re + (n : ℝ) / 2)) := mul_le_mul_of_nonneg_left (hon c hc) h0
      _ = _ := by ring
  refine ⟨max δ 0, hB0, fun z g => ?_⟩
  have e3 : ‖npow (H g) (z - s₁)‖ = (H g : ℝ) ^ (z.re - s₁.re) := by
    rw [norm_npow (hH.2.1 g)]; congr 1
  have e4 : (H g : ℝ) ^ (z.re + (n : ℝ) / 2) = (H g : ℝ) ^ (z.re - s₁.re) * (H g : ℝ) ^ (s₁.re + (n : ℝ) / 2) := by
    rw [← Real.rpow_add (hHpos g)]; congr 1; ring
  have h0 : 0 ≤ (H g : ℝ) ^ (z.re - s₁.re) := (Real.rpow_pos_of_pos (hHpos g) _).le
  simp only [fam]
  rw [norm_mul, e3, e4]
  calc _ ≤ (H g : ℝ) ^ (z.re - s₁.re) * (max δ 0 * (H g : ℝ) ^ (s₁.re + (n : ℝ) / 2)) :=
        mul_le_mul_of_nonneg_left (hall g) h0
    _ = _ := by ring

end GlobalTheory.CompanionTheory.FamMajorant

end
end

section

open GlobalTheory.PRep GlobalTheory.SmGL ValuativeRel PositivityTheory.Lbc

namespace GlobalTheory.CompanionTheory.Lbc

theorem heckeOp_nilpotent_on_ker :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N h : ℕ) (d : Fin h → ℕ) (hd : ∑ a, d a = N) (J : Subgroup (GL (Fin N) k)), IsOpen (J : Set (GL (Fin N) k)) → IsCompact (J : Set (GL (Fin N) k)) → HasIwahoriFact k N J d hd → (∀ a, 0 < d a) → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), IsSmooth π → ∀ t : Levi k (Bl d), IsStrictlyDominant k N J d hd t → ∀ T : Module.End ℂ (fixed π J), IsHeckeOp π J (leviEmb k (stdBlocks d hd) t) T → ∀ v : fixed π J, (Submodule.Quotient.mk (v : V) : Jacquet π (unipRad k (stdBlocks d hd))) = 0 → ∃ r : ℕ, (T ^ r) v = 0 := by
  intro k _ _ _ _ N h d hd J hJo hJc hJf hpos V _ _ π hπ t ht T hT v hv
  set e := leviEmb k (stdBlocks d hd) with he

  have hdom : ∀ r : ℕ, IsDominant k N J d hd (t ^ r) := by
    intro r
    induction r with
    | zero => simpa using (isDominant_one_and_mul k N J h d hd).1
    | succ r ih =>
      rw [pow_succ]
      exact (isDominant_one_and_mul k N J h d hd).2 _ _ ih ht.1

  have hecke : ∀ r : ℕ, IsHeckeOp π J (e (t ^ r)) (T ^ r) := by
    intro r
    induction r with
    | zero =>
      intro w l _
      simp
    | succ r ih =>
      rw [pow_succ, pow_succ T]
      exact GlobalTheory.T.jacquet_fixed_first_condition k N h d hd J hJo hJc hJf hpos V π hπ _ _ (hdom r) ht.1 _ _ ih hT

  have key : ∀ u ∈ twKer π (unipRad k (stdBlocks d hd)) 1, ∃ R : ℕ, ∀ r ≥ R,
      ∀ l : Module.Dual ℂ V, (∀ x ∈ J, l ∘ₗ π x = l) → l (π (e t ^ r) u) = 0 := by
    intro u hu
    induction hu using Submodule.span_induction with
    | mem u hu =>
      obtain ⟨n, w, rfl⟩ := hu
      obtain ⟨R, hR⟩ := GlobalTheory.T.strictly_dominant_contracts_unipotent k N h d hd J hJo hJc hJf hpos t ht (n : GL (Fin N) k) n.2
      refine ⟨R, fun r hr l hl => ?_⟩
      obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hr
      have hmem : e t ^ (R + j) * (n : GL (Fin N) k) * (e t ^ (R + j))⁻¹ ∈ KN k N J d hd := by
        have := (hdom j).1 _ hR
        rw [map_pow] at this
        convert this using 1
        rw [add_comm R j, pow_add]
        group
        rfl
      have hx := hl _ hmem.1
      have hy := LinearMap.congr_fun hx (π (e t ^ (R + j)) w)
      simp only [LinearMap.comp_apply] at hy
      have hz : π (e t ^ (R + j) * (n : GL (Fin N) k) * (e t ^ (R + j))⁻¹) (π (e t ^ (R + j)) w)
          = π (e t ^ (R + j)) (π (n : GL (Fin N) k) w) := by
        rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
        congr 2
        group
      rw [hz] at hy
      simp only [MonoidHom.one_apply, Units.val_one, one_smul, map_sub, hy, sub_self]
    | zero => exact ⟨0, fun r _ l _ => by simp⟩
    | add a b _ _ ha hb =>
      obtain ⟨A, hA⟩ := ha
      obtain ⟨B, hB⟩ := hb
      refine ⟨max A B, fun r hr l hl => ?_⟩
      rw [map_add (f := _), map_add (f := _), hA r (le_trans (le_max_left _ _) hr) l hl,
        hB r (le_trans (le_max_right _ _) hr) l hl, add_zero]
    | smul c a _ ha =>
      obtain ⟨A, hA⟩ := ha
      refine ⟨A, fun r hr l hl => ?_⟩
      rw [map_smul, map_smul, hA r hr l hl, smul_zero]
  obtain ⟨R, hR⟩ := key _ ((Submodule.Quotient.mk_eq_zero _).1 hv)
  refine ⟨R, ?_⟩
  have h0 : (((T ^ R) v : fixed π J) : V) = 0 := by
    refine GlobalTheory.T.fixed_vector_zero_of_dual _ J hJc V π hπ _ ((T ^ R) v).2 fun l hl => ?_
    rw [← hecke R v l hl, map_pow]
    exact hR R le_rfl l hl
  exact Subtype.ext h0

end GlobalTheory.CompanionTheory.Lbc
end

section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl
open GlobalTheory.Doubling (absE)

theorem _root_.GlobalTheory.T.isCompact_standard_maximal : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n : ℕ) (Y : Spc F E n) (r s : ℕ), B.IsGood σ → 1 ≤ n → (Y.IsHerm σ B r s ∨ Y.IsSkew σ B r s) → ∀ (b : GL (Fin n ⊕ Fin n) E) (K : Subgroup (G2 σ Y)) (a : G2 σ Y → ℝ), IsFrame2 σ Y b → IsStdK (σ := σ) (Y := Y) B b K → IsHgt K a → IsCompact (K : Set (G2 σ Y)) := by
  first | exact @GlobalTheory.CompanionTheory.StdK.isCompact_K | exact GlobalTheory.CompanionTheory.StdK.isCompact_K | (intros; apply GlobalTheory.CompanionTheory.StdK.isCompact_K <;> assumption)
end
