module

public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.Bundle001
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle352
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FourierZeroHolds
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyCosocles.LUnlinkedComm
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle002
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle500
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle698
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle697
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle652
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle048
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle080
import GroundTheory.LocalFields.PadicLogSeries
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.WeakApproximationFinitePlace
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle699
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle241
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.Bundle001
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacobiMapsExist
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.MapsExist
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Prop
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.HermitianCellMeasures.Bundle001

@[expose] public section

section

noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.HermFD

theorem integrable_of_cover {A : Type*} [AddGroup A] [TopologicalSpace A] [MeasurableSpace A] [BorelSpace A]
    [SecondCountableTopology A] [MeasurableAdd A] [ContinuousAdd A] (L : AddSubgroup A) [Countable L]
    (μ : Measure A) [μ.IsAddLeftInvariant] (𝓖 : Set A) (hFD : IsAddFundamentalDomain L 𝓖 μ) (h1 : μ 𝓖 = 1)
    (f : A → ℝ) (hf : Continuous f) (hf0 : ∀ z, 0 ≤ f z) (hS : Summable (fun ζ : L => f ζ.1))
    (K : Set A) (hK : ∀ x, ∃ γ ∈ L, γ + x ∈ K) (κ : ℝ) (hκ : 0 ≤ κ)
    (hb : ∀ ζ ∈ L, ∀ z ∈ K, f (ζ + z) ≤ κ * f ζ) : Integrable f μ := by
  have hpt : ∀ z : A, ∑' ζ : L, ENNReal.ofReal (f (ζ.1 + z)) ≤ ENNReal.ofReal (κ * ∑' ζ : L, f ζ.1) := by
    intro z
    obtain ⟨γ, hγ, hz⟩ := hK z
    have h2 : ∀ ζ : L, ENNReal.ofReal (f (ζ.1 + z)) ≤
        ENNReal.ofReal (κ * f ((Equiv.subRight (⟨γ, hγ⟩ : L) ζ).1)) := by
      intro ζ
      apply ENNReal.ofReal_le_ofReal
      have e : ζ.1 + z = (ζ.1 - γ) + (γ + z) := by simp [sub_eq_add_neg, add_assoc]
      rw [e]
      exact hb _ (L.sub_mem ζ.2 hγ) _ hz
    refine (ENNReal.tsum_le_tsum h2).trans ?_
    rw [(Equiv.subRight (⟨γ, hγ⟩ : L)).tsum_eq (fun ζ : L => ENNReal.ofReal (κ * f ζ.1)),
      ← tsum_mul_left, ENNReal.ofReal_tsum_of_nonneg (fun ζ => mul_nonneg hκ (hf0 _)) (hS.mul_left κ)]
  have hm : ∀ g : L, AEMeasurable (fun x : A => ENNReal.ofReal (f (g +ᵥ x))) (μ.restrict 𝓖) := fun g =>
    (ENNReal.measurable_ofReal.comp (hf.comp (continuous_const.add continuous_id)).measurable).aemeasurable
  have hI : ∫⁻ x, ENNReal.ofReal (f x) ∂μ ≤ ENNReal.ofReal (κ * ∑' ζ : L, f ζ.1) := by
    rw [hFD.lintegral_eq_tsum'', ← lintegral_tsum hm]
    calc _ ≤ ∫⁻ _ in 𝓖, ENNReal.ofReal (κ * ∑' ζ : L, f ζ.1) ∂μ :=
          lintegral_mono fun x => hpt x
      _ = _ := by simp [h1]
  exact ⟨hf.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal (.of_forall hf0)).2 (hI.trans_lt ENNReal.ofReal_lt_top)⟩



theorem integrable_of_periodisation_bound : ∀ (D : D7) (ρ : ℕ) (lz : Measure (hermA D ρ)) (𝓖 : Set (hermA D ρ)), IsCovolOneH lz 𝓖 →
  ∀ f : hermA D ρ → ℝ, Continuous f → (∀ z, 0 ≤ f z) → Summable (fun ζ : ratHerm D ρ => f ζ.1) →
  ∀ K : Set (hermA D ρ), (∀ x, ∃ γ ∈ ratHerm D ρ, γ + x ∈ K) → ∀ κ : ℝ, 0 ≤ κ →
    (∀ ζ ∈ ratHerm D ρ, ∀ z ∈ K, f (ζ + z) ≤ κ * f ζ) → Integrable f lz := by
  intro D ρ lz 𝓖 hC f hf hf0 hS K hK κ hκ hb
  obtain ⟨hlam, hFD, h1⟩ := hC
  obtain ⟨i1, i2, i3, i4, -, -⟩ := GlobalTheory.TowerResNonzero.lattice_ratMx D ρ ρ
  haveI : BorelSpace (Mx D ρ ρ) := ⟨rfl⟩
  haveI : BorelSpace (hermA D ρ) := Subtype.borelSpace _
  haveI : SecondCountableTopology (hermA D ρ) := TopologicalSpace.Subtype.secondCountableTopology _
  haveI : ContinuousAdd (hermA D ρ) := ⟨Continuous.subtype_mk ((continuous_subtype_val.comp continuous_fst).add
    (continuous_subtype_val.comp continuous_snd)) _⟩
  haveI : MeasurableAdd (hermA D ρ) := ContinuousAdd.measurableAdd
  haveI : DiscreteTopology (ratHerm D ρ) := GlobalTheory.CompanionTheory.FourierN.discrete_ratHerm
  haveI : Countable (ratHerm D ρ) := by
    haveI : SecondCountableTopology (ratHerm D ρ) := TopologicalSpace.Subtype.secondCountableTopology _
    exact (TopologicalSpace.separableSpace_iff_countable).1 inferInstance
  exact integrable_of_cover (ratHerm D ρ) lz 𝓖 hFD h1 f hf hf0 hS K hK κ hκ hb

end GlobalTheory.CompanionTheory.HermFD
end
end

section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.hypotheses_preserved_by_linear_pullback : ∀ (D : D7) (r : ℕ) (V : HSp D) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (μ : Measure (Mx D V.rank r)) (lam : Measure (hermA D r)) (ν : Measure (GA D V)) (φ : Mx D V.rank r → ℂ) (a : Matrix (Fin r) (Fin r) D.host.E), a.det ≠ 0 → Hyp D r V ψ θ μ lam ν φ → Hyp D r V ψ θ μ lam ν (pull a φ) := by
  first | exact @GlobalTheory.CompanionTheory.WeilSiegel.Deg.hyp_pull | exact GlobalTheory.CompanionTheory.WeilSiegel.Deg.hyp_pull | (intros; apply GlobalTheory.CompanionTheory.WeilSiegel.Deg.hyp_pull <;> assumption)
end

section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Cos

namespace GlobalTheory.CompanionTheory.FineProd

theorem sum_map_filter {β : Type*} (p : β → Prop) [DecidablePred p] (f : β → ℕ) (l : List β) :
    ((l.filter fun a => decide (p a)).map f).sum = (l.map fun j => if p j then f j else 0).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    by_cases hp : p a
    · simp [List.filter_cons, hp, ih]
    · simp [List.filter_cons, hp, ih]

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem deg_sub {h : ℕ} (W : List (IrrGL (k := k))) (c : Fin W.length → Fin h) (i : Fin h) :
    ((sub W c i).map Sigma.fst).sum = ∑ j, if c j = i then (W.get j).1 else 0 := by
  show ((List.map W.get (List.filter (fun p => decide (c p = i)) (List.finRange W.length))).map
    Sigma.fst).sum = _
  rw [List.map_map, Fin.sum_univ_def]
  exact sum_map_filter (fun p => c p = i) (fun p => (W.get p).1) (List.finRange W.length)

theorem deg_decWord (Γ : Segment k) : ((decWord Γ).map Sigma.fst).sum = Γ.deg := by
  have h : ∀ a, (Γ.term a).1 = Γ.d := fun a => rfl
  show ((List.ofFn Γ.term).reverse.map Sigma.fst).sum = Γ.len * Γ.d
  rw [List.map_reverse, List.sum_reverse, List.map_ofFn, List.sum_ofFn]
  simp only [Function.comp_def, h, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]

def colourMat {h : ℕ} (W : List (IrrGL (k := k))) (c : Fin W.length → Fin h) (i : Fin h) (j : Fin W.length) : ℕ :=
  if c j = i then (W.get j).1 else 0

theorem sum_colourMat {h : ℕ} (W : List (IrrGL (k := k))) (c : Fin W.length → Fin h) (j : Fin W.length) :
    ∑ i, colourMat W c i j = (W.get j).1 := by
  simp [colourMat]

end GlobalTheory.CompanionTheory.FineProd


open GlobalTheory.CompanionTheory.FineProd in
theorem GlobalTheory.CompanionTheory.FineProd.jmL_prodIrr : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.Published.IrreducibleAdmissibleGL → LSegJacquet k → ∀ {h N : ℕ} (Γ : Fin h → Segment k) (x : Fin h → IrrGL (k := k)) (hd : ∑ a, (x a).1 = N), (∀ i, IsLSeg (Γ i) (x i).rep) → ∀ W : List (IrrGL (k := k)), (∀ w ∈ W, w.IsCusp) → jmL W (prodIrr x hd) = (shuffleCount W (fun i => decWord (Γ i)) : ℕ∞) := by
  intro k _ _ _ _ hA hJ h N Γ x hd hΓ W hW
  classical
  have hΓd : ∀ i, ((decWord (Γ i)).map Sigma.fst).sum = (x i).1 := fun i =>
    (deg_decWord _).trans (hΓ i).deg_eq
  let S : Finset (Fin W.length → Fin h) := Finset.univ.filter fun c => ∀ i, sub W c i = decWord (Γ i)
  have hcount : shuffleCount W (fun i => decWord (Γ i)) = S.card := by
    unfold shuffleCount
    congr
  have hrowS : ∀ c ∈ S, ∀ i, ∑ j, colourMat W c i j = (x i).1 := fun c hc i => by
    have h1 := (Finset.mem_filter.1 hc).2 i
    have h2 := deg_sub W c i
    rw [h1, hΓd] at h2
    exact h2.symm
  have hSdeg : ∀ c ∈ S, ∑ a, (W.get a).1 = N := fun c hc => by
    rw [← hd, ← Finset.sum_congr rfl fun i _ => hrowS c hc i, Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ => (sum_colourMat W c j).symm
  have hpos : ∀ j, 0 < (W.get j).1 := fun j => (hW _ (List.get_mem _ _)).1
  rw [hcount]
  by_cases hWd : ∑ a, (W.get a).1 = N
  swap
  · have hSe : S = ∅ := Finset.eq_empty_of_forall_notMem fun c hc => hWd (hSdeg c hc)
    rw [hSe, jmL, dite_eq_right hWd]
    simp
  let m : Fin h → Type := fun i => Fin (x i).1
  let m' : Fin W.length → Type := fun j => Fin (W.get j).1
  haveI : Fintype (SizeMatrix m m') := Fintype.ofFinite _
  have hr : ∀ (b : SizeMatrix m m') i, ∑ j, b.1 i j = (x i).1 := fun b i => by
    simpa [m] using b.2.1 i
  have hc : ∀ (b : SizeMatrix m m') j, ∑ i, b.1 i j = (W.get j).1 := fun b j => by
    simpa [m'] using b.2.2 j
  have hτ : (piTensor fun j => (W.get j).rep).IsIrreducible :=
    GlobalTheory.T.piExteriorTensor_smoothIrreducible_isIrreducible GlobalTheory.CompanionTheory.Published.bernsteinZelevinskyFiniteness k _ _ fun j => (W.get j).2.rep
  have key := ((GlobalTheory.CompanionTheory.GeoLink.geometricLemma k).1).jhMult_eq (m := m) (m' := m')
    (stdBlocks (fun a => (x a).1) hd) (stdBlocks (fun a => (W.get a).1) hWd)
    (isSmooth_piTensor fun i => (x i).2.rep.smooth)
    (fun b i => stdBlocks (b.1 i) (hr b i)) (fun b j => stdBlocks (fun i => b.1 i j) (hc b j)) hτ
  have hF : ∀ b : SizeMatrix m m', jhMult (piTensor fun j => (W.get j).rep)
      (cellFunctor (c := fun i j => Fin (b.1 i j)) (fun i => stdBlocks (b.1 i) (hr b i))
        (fun j => stdBlocks (fun i => b.1 i j) (hc b j)) (piTensor fun i => (x i).rep)) =
      if ∃ c ∈ S, b.1 = colourMat W c then 1 else 0 := by
    intro b
    split_ifs with hb
    · obtain ⟨c, hcS, hbc⟩ := hb
      rw [GlobalTheory.T.cuspidal_cell_multiplicity_of_colouring x W b.1 (hr b) (hc b) c (fun i j => by rw [hbc]; rfl)]
      refine Finset.prod_eq_one fun i _ => ?_
      refine ((GlobalTheory.T.segment_rep_jacquet_word_multiplicity hA hJ (Γ i) (x i).rep (hΓ i) (sub W c i) fun w hw => ?_).1
        ((Finset.mem_filter.1 hcS).2 i))
      obtain ⟨p, -, rfl⟩ := List.mem_map.1 hw
      exact hW _ (List.get_mem _ _)
    · by_cases hm : ∃ (j : Fin W.length) (i i' : Fin h), i ≠ i' ∧ b.1 i j ≠ 0 ∧ b.1 i' j ≠ 0
      · obtain ⟨j, i, i', hii, h1, h2⟩ := hm
        exact GlobalTheory.T.cuspidal_cell_multiplicity_zero_of_split_column hA x (fun j => W.get j) (fun j => hW _ (List.get_mem _ _)) b.1 (hr b) (hc b) j i i' hii h1 h2
      · push_neg at hm
        have hex : ∀ j, ∃ i, b.1 i j ≠ 0 := fun j => by
          by_contra hne
          push_neg at hne
          have := hc b j
          rw [Finset.sum_eq_zero fun i _ => hne i] at this
          exact (hpos j).ne this
        choose c hcj using hex
        have hzero : ∀ i j, c j ≠ i → b.1 i j = 0 := fun i j hij => by
          by_contra hne
          exact hne (hm j (c j) i hij (hcj j))
        have hbc : b.1 = colourMat W c := by
          funext i j
          unfold colourMat
          split_ifs with hij
          · subst hij
            rw [← hc b j]
            exact (Finset.sum_eq_single (c j) (fun i _ hi => hzero i j (Ne.symm hi)) (by simp)).symm
          · exact hzero i j hij
        have hcS : c ∉ S := fun hcS => hb ⟨c, hcS, hbc⟩
        have hex2 : ∃ i, sub W c i ≠ decWord (Γ i) := by
          by_contra hne
          push_neg at hne
          exact hcS (Finset.mem_filter.2 ⟨Finset.mem_univ _, hne⟩)
        obtain ⟨i, hi⟩ := hex2
        rw [GlobalTheory.T.cuspidal_cell_multiplicity_of_colouring x W b.1 (hr b) (hc b) c (fun i j => by rw [hbc]; rfl)]
        refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
        refine (GlobalTheory.T.segment_rep_jacquet_word_multiplicity hA hJ (Γ i) (x i).rep (hΓ i) (sub W c i) (fun w hw => ?_)).2 hi
        obtain ⟨p, -, rfl⟩ := List.mem_map.1 hw
        exact hW _ (List.get_mem _ _)
  rw [jmL, dite_eq_left hWd]
  refine Eq.trans key ?_
  have hcard : (Finset.univ.filter fun b : SizeMatrix m m' => ∃ c ∈ S, b.1 = colourMat W c).card = S.card := by
    symm
    let mk : ∀ c, c ∈ S → SizeMatrix m m' := fun c hc =>
      ⟨colourMat W c, fun i => by simpa [m] using hrowS c hc i, fun j => by simpa [m'] using sum_colourMat W c j⟩
    refine Finset.card_bij mk (fun c hc => Finset.mem_filter.2 ⟨Finset.mem_univ _, c, hc, rfl⟩) ?_ ?_
    · intro c hc c' hc' he
      funext j
      have h1 : colourMat W c (c j) j = colourMat W c' (c j) j :=
        congrFun (congrFun (congrArg Subtype.val he) (c j)) j
      by_contra hne
      have h2 : c' j ≠ c j := fun e => hne e.symm
      simp only [colourMat, if_true, if_neg h2] at h1
      exact (hpos j).ne' h1
    · intro b hb
      obtain ⟨c, hc, hbc⟩ := (Finset.mem_filter.1 hb).2
      exact ⟨c, hc, Subtype.ext hbc.symm⟩
  rw [Finset.sum_congr rfl fun b _ => hF b, Finset.sum_boole, hcard]
end
end

section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L PositivityTheory.Rg.Rsw.Em
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField

namespace GlobalTheory.CompanionTheory.EmbK

open GlobalTheory.CompanionTheory.JacobiMaps

section Entries

variable {R : Type} [CommRing R] {n r t : ℕ}

theorem block_matrix_apply_inl_inl (a b c d : Matrix (Fin n) (Fin n) R) (i j : Fin n) :
    blk4 a b c d (finSumFinEquiv (Sum.inl i)) (finSumFinEquiv (Sum.inl j)) = a i j := by
  simp only [blk4, Matrix.submatrix_apply, Equiv.symm_apply_apply, Matrix.fromBlocks_apply₁₁]

theorem block_matrix_apply_inl_inr (a b c d : Matrix (Fin n) (Fin n) R) (i j : Fin n) :
    blk4 a b c d (finSumFinEquiv (Sum.inl i)) (finSumFinEquiv (Sum.inr j)) = b i j := by
  simp only [blk4, Matrix.submatrix_apply, Equiv.symm_apply_apply, Matrix.fromBlocks_apply₁₂]

theorem block_matrix_apply_inr_inl (a b c d : Matrix (Fin n) (Fin n) R) (i j : Fin n) :
    blk4 a b c d (finSumFinEquiv (Sum.inr i)) (finSumFinEquiv (Sum.inl j)) = c i j := by
  simp only [blk4, Matrix.submatrix_apply, Equiv.symm_apply_apply, Matrix.fromBlocks_apply₂₁]

theorem block_matrix_apply_inr_inr (a b c d : Matrix (Fin n) (Fin n) R) (i j : Fin n) :
    blk4 a b c d (finSumFinEquiv (Sum.inr i)) (finSumFinEquiv (Sum.inr j)) = d i j := by
  simp only [blk4, Matrix.submatrix_apply, Equiv.symm_apply_apply, Matrix.fromBlocks_apply₂₂]

theorem entry (hn : r + t = n) (a b c d : Matrix (Fin t) (Fin t) R) (i j : Fin (n + n)) :
    blk4 (bl hn 1 0 0 a) (bl hn 0 0 0 b) (bl hn 0 0 0 c) (bl hn 1 0 0 d) i j = (1 : Matrix (Fin (n + n)) (Fin (n + n)) R) i j ∨
    ∃ i' j', blk4 (bl hn 1 0 0 a) (bl hn 0 0 0 b) (bl hn 0 0 0 c) (bl hn 1 0 0 d) i j = blk4 a b c d i' j' ∧
      (1 : Matrix (Fin (t + t)) (Fin (t + t)) R) i' j' = (1 : Matrix (Fin (n + n)) (Fin (n + n)) R) i j := by
  have h1 : (1 : Matrix (Fin (n + n)) (Fin (n + n)) R) =
      blk4 (bl hn 1 0 0 1) (bl hn 0 0 0 0) (bl hn 0 0 0 0) (bl hn 1 0 0 1) := by
    have z : bl hn (0 : Matrix (Fin r) (Fin r) R) 0 0 (0 : Matrix (Fin t) (Fin t) R) = 0 := blockMatrix_zero hn
    rw [blockRowSubstitution_one, z, GlobalTheory.StdUnn.Model.block_matrix_one]
  have h2 : (1 : Matrix (Fin (t + t)) (Fin (t + t)) R) = blk4 1 0 0 1 := GlobalTheory.StdUnn.Model.block_matrix_one.symm
  rw [h1, h2]
  have bll : ∀ (a : Matrix (Fin r) (Fin r) R) b c (d : Matrix (Fin t) (Fin t) R) i j,
      bl hn a b c d ((finSumFinEquiv.trans (finCongr hn)) (Sum.inl i)) ((finSumFinEquiv.trans (finCongr hn)) (Sum.inl j)) = a i j := by
    intro a b c d i j; simp only [bl, Matrix.submatrix_apply, Equiv.symm_apply_apply, Matrix.fromBlocks_apply₁₁]
  have blr : ∀ (a : Matrix (Fin r) (Fin r) R) b c (d : Matrix (Fin t) (Fin t) R) i j,
      bl hn a b c d ((finSumFinEquiv.trans (finCongr hn)) (Sum.inl i)) ((finSumFinEquiv.trans (finCongr hn)) (Sum.inr j)) = b i j := by
    intro a b c d i j; simp only [bl, Matrix.submatrix_apply, Equiv.symm_apply_apply, Matrix.fromBlocks_apply₁₂]
  have brl : ∀ (a : Matrix (Fin r) (Fin r) R) b c (d : Matrix (Fin t) (Fin t) R) i j,
      bl hn a b c d ((finSumFinEquiv.trans (finCongr hn)) (Sum.inr i)) ((finSumFinEquiv.trans (finCongr hn)) (Sum.inl j)) = c i j := by
    intro a b c d i j; simp only [bl, Matrix.submatrix_apply, Equiv.symm_apply_apply, Matrix.fromBlocks_apply₂₁]
  have brr : ∀ (a : Matrix (Fin r) (Fin r) R) b c (d : Matrix (Fin t) (Fin t) R) i j,
      bl hn a b c d ((finSumFinEquiv.trans (finCongr hn)) (Sum.inr i)) ((finSumFinEquiv.trans (finCongr hn)) (Sum.inr j)) = d i j := by
    intro a b c d i j; simp only [bl, Matrix.submatrix_apply, Equiv.symm_apply_apply, Matrix.fromBlocks_apply₂₂]
  obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
  obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective j
  rcases i with i | i <;> rcases j with j | j <;>
    obtain ⟨i, rfl⟩ := (finSumFinEquiv.trans (finCongr hn)).surjective i <;>
    obtain ⟨j, rfl⟩ := (finSumFinEquiv.trans (finCongr hn)).surjective j <;>
    rcases i with i | i <;> rcases j with j | j <;>
    simp only [block_matrix_apply_inl_inl, block_matrix_apply_inl_inr, block_matrix_apply_inr_inl, block_matrix_apply_inr_inr, bll, blr, brl, brr, true_or] <;>
    first
    | exact Or.inl rfl
    | exact Or.inr ⟨_, _, (block_matrix_apply_inl_inl a b c d i j).symm, block_matrix_apply_inl_inl _ _ _ _ i j⟩
    | exact Or.inr ⟨_, _, (block_matrix_apply_inl_inr a b c d i j).symm, block_matrix_apply_inl_inr _ _ _ _ i j⟩
    | exact Or.inr ⟨_, _, (block_matrix_apply_inr_inl a b c d i j).symm, block_matrix_apply_inr_inl _ _ _ _ i j⟩
    | exact Or.inr ⟨_, _, (block_matrix_apply_inr_inr a b c d i j).symm, block_matrix_apply_inr_inr _ _ _ _ i j⟩

theorem map_one_apply {T : Type} [CommRing T] {N : ℕ} (f : R →+* T) (i j : Fin N) :
    f ((1 : Matrix (Fin N) (Fin N) R) i j) = (1 : Matrix (Fin N) (Fin N) T) i j := by
  by_cases h : i = j
  · subst h; simp
  · simp [Matrix.one_apply_ne h]

end Entries

variable {D : D7} {n r t : ℕ} {hn : r + t = n}

theorem emb_entries_one (M : Maps D hn) {T : Type} [CommRing T] (f : AE D →+* T) {u : G D t}
    (hu : ∀ i j, f (mat u i j) = (1 : Matrix (Fin (t + t)) (Fin (t + t)) T) i j) (i j : Fin (n + n)) :
    f (mat (M.emb u) i j) = (1 : Matrix (Fin (n + n)) (Fin (n + n)) T) i j := by
  rw [M.emb_mat u _ _ _ _ (block_matrix_of_blocks (mat u)).symm]
  rcases entry hn (b11 (mat u)) (b12 (mat u)) (b21 (mat u)) (b22 (mat u)) i j with h | ⟨i', j', h, h'⟩
  · rw [h, map_one_apply]
  · rw [h, block_matrix_of_blocks, hu i' j', ← map_one_apply f i' j', h', map_one_apply]

theorem emb_entries_mem (M : Maps D hn) {T : Type} [CommRing T] (f : AE D →+* T) (P : Subring T) {u : G D t}
    (hu : ∀ i j, f (mat u i j) ∈ P) (i j : Fin (n + n)) : f (mat (M.emb u) i j) ∈ P := by
  rw [M.emb_mat u _ _ _ _ (block_matrix_of_blocks (mat u)).symm]
  rcases entry hn (b11 (mat u)) (b12 (mat u)) (b21 (mat u)) (b22 (mat u)) i j with h | ⟨i', j', h, -⟩
  · rw [h, map_one_apply]
    by_cases e : i = j
    · subst e; simpa using P.one_mem
    · simpa [Matrix.one_apply_ne e] using P.zero_mem
  · rw [h, block_matrix_of_blocks]
    exact hu i' j'

theorem stab_entries {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {N : ℕ}
    {v : HeightOneSpectrum (𝓞 F)} {m : GL (Fin N) (Fv F v ⊗[F] E)}
    (h : m ∈ Formalism.UG.stabGL (latLoc F (stdLattice E N) v)) (i j : Fin N) :
    m.1 i j ∈ intLoc F E v ∧ (m⁻¹).1 i j ∈ intLoc F E v := by
  have hs : (Pi.single j 1 : Fin N → Fv F v ⊗[F] E) ∈ latLoc F (stdLattice E N) v := by
    refine mem_latLoc_stdLattice.2 fun k => ?_
    by_cases e : k = j
    · subst e; simpa using (intLoc F E v).one_mem
    · simpa [Pi.single_eq_of_ne e] using (intLoc F E v).zero_mem
  constructor
  · have h1 := mem_latLoc_stdLattice.1 ((h _).1 hs) i
    simpa using h1
  · have e : m.1 *ᵥ ((m⁻¹).1 *ᵥ (Pi.single j 1 : Fin N → Fv F v ⊗[F] E)) = Pi.single j 1 := by
      rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
    have h2 : (m⁻¹).1 *ᵥ (Pi.single j 1 : Fin N → Fv F v ⊗[F] E) ∈ latLoc F (stdLattice E N) v :=
      (h _).2 (by rw [e]; exact hs)
    have h1 := mem_latLoc_stdLattice.1 h2 i
    simpa using h1

theorem emb_mem_KOff : ∀ {D : D7} {n r t : ℕ} {hn : r + t = n} (M : Maps D hn) (S : Finset (Pl D)) (u : G D t),
    u ∈ KOff D t S → M.emb u ∈ KOff D n S := by
  intro D n r t hn M S u hu
  obtain ⟨hf, h1, h2⟩ := mem_levelOff.1 hu
  refine mem_levelOff.2 ⟨mem_finPts_iff_forall.2 fun w => ?_, fun v hv => ?_, fun v hv => ?_⟩
  · have hw := mem_finPts_iff_forall.1 hf w
    have ent : ∀ i j, compInf D.host.F D.host.E w (mat u i j) = (1 : Matrix (Fin (t + t)) (Fin (t + t)) _) i j := fun i j => by
      have e := congrArg (fun g => (matHom _ D.sp.cm.sig (Jst D t) g).1 i j) hw
      simp only [map_one, Units.val_one] at e
      exact e
    apply matHom_injective
    apply Units.ext
    ext i j
    rw [matHom_projArch, map_one]
    exact emb_entries_one M _ ent i j
  · have ent : ∀ i j, cv D v (mat u i j) = (1 : Matrix (Fin (t + t)) (Fin (t + t)) _) i j := fun i j => by
      have e := congrArg (fun g => (matHom _ D.sp.cm.sig (Jst D t) g).1 i j) (h1 v hv)
      simp only [map_one, Units.val_one] at e
      exact e
    apply matHom_injective
    apply Units.ext
    ext i j
    rw [matHom_proj, map_one]
    exact emb_entries_one M _ ent i j
  · have key : ∀ x : G D t, proj D.sp.cm.sig (Jst D t) v x ∈ stabLoc D.sp.cm.sig (Jst D t) (stdLattice D.host.E (t + t)) v →
        ∀ i j, (matHom _ D.sp.cm.sig (Jst D n) (proj D.sp.cm.sig (Jst D n) v (M.emb x))).1 i j ∈ intLoc D.host.F D.host.E v := by
      intro x hx i j
      exact emb_entries_mem M (cv D v) _ (fun i j => (stab_entries hx i j).1) i j
    refine GlobalTheory.StdUnn.StabFin.mem_stab_std (key u (h2 v hv)) fun i j => ?_
    rw [← map_inv, ← map_inv, ← map_inv]
    exact key u⁻¹ (by rw [map_inv]; exact inv_mem (h2 v hv)) i j

end GlobalTheory.CompanionTheory.EmbK
end

section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.integrable_schwartz_restriction_columns : ∀ {D : D7} {n r t : ℕ} {θ : InfFam D} (hθ : IsInfFam θ) {a : ℕ} (hn : r + t = n) (μt : Measure (Mx D a t)) [μt.IsAddHaarMeasure] (Φ : schwartzA θ a n) (x : Mx D a r), Integrable (fun v => Φ.1 (jn hn x v)) μt := by
  first | exact @GlobalTheory.CompanionTheory.ColSlice.integrable_slice | exact GlobalTheory.CompanionTheory.ColSlice.integrable_slice | (intros; apply GlobalTheory.CompanionTheory.ColSlice.integrable_slice <;> assumption)
end
