module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle003
public import Formalism.HermitianLattices.Bundle003
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle159
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle115
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianLatticeDiscriminantOrderNeZeroUnimodula
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MaximalHermitianLatticeLocalStructureDiscriminan
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle052
public import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.IdealsOfNormEqIndexSet
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle007
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsHermIsometryGraphModScalarFlagPairIota
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.JetUniquenessAlgebraic
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MirabolicInductionBlockDiagEqHarishChandraGelfan
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle162
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.NoncompactArrFiniteDimensional
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.NoncompactGeneratorRaisesPfil
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle008
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AutPointRationalEquivariance
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurableSetHasFlag
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle163
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsScalarStableLatticeAutomorphismFundamental
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PosPartUnitaryMul
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.EigenfunctionFiniteCoefficients
import Formalism.FormalDegreeBessel.StatementWR
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
import Std.Tactic.BVDecide.Normalize.Bool
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurableSetHsBall
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle010

@[expose] public section

section

open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical

noncomputable section

namespace GlobalTheory.Mass.FewOrbits

theorem mem_iff_prod_le {R : Type*} [CommRing R] {A : Set (Ideal R)} (hA : A.Finite)
    (hm : ∀ P ∈ A, P.IsMaximal) (P : Ideal R) : P ∈ A ↔ P.IsMaximal ∧ ∏ᶠ Q ∈ A, Q ≤ P := by
  rw [finprod_mem_eq_finite_toFinset_prod _ hA]
  constructor
  · intro hP
    exact ⟨hm P hP, Ideal.prod_le_inf.trans (Finset.inf_le (hA.mem_toFinset.2 hP))⟩
  · rintro ⟨hPm, hle⟩
    obtain ⟨Q, hQ, hQP⟩ := (Ideal.IsPrime.prod_le hPm.isPrime).1 hle
    have hQm := hm Q (hA.mem_toFinset.1 hQ)
    exact (hQm.eq_of_le hPm.ne_top hQP) ▸ hA.mem_toFinset.1 hQ

theorem nondeg {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
    (h : V →ₗ⋆[K] V →ₗ[K] K) (hp : PD h) : h.Nondegenerate := by
  obtain ⟨τ⟩ : Nonempty (K →+* ℂ) := inferInstance
  have key : ∀ x : V, h x x = 0 → x = 0 := by
    intro x hx
    by_contra hne
    have := hp τ x hne
    rw [hx, map_zero, Complex.zero_re] at this
    exact lt_irrefl _ this
  exact ⟨fun x hx => key x (hx x), fun y hy => key y (hy y)⟩

theorem main : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K), IsCMUnram K → h.IsSymm → PD h → (∀ (W : Type) [AddCommGroup W] [Module K W] [FiniteDimensional K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W] (k : W →ₗ⋆[K] W →ₗ[K] K), k.IsSymm → PD k → (∃ L : Submodule (𝓞 K) W, Submodule.IsLattice K L ∧ IsUnimodular k L) → ∃ I : Submodule (𝓞 K) W, IsOrthoLattice k I (Module.finrank K W)) → ∀ (j n : ℕ), 1 ≤ n → ∃ s : Finset (Submodule K V), (s.card : ℝ) ≤ (n : ℝ) ^ (1 + Real.logb 2 (Module.finrank ℚ K)) ∧ (∀ U ∈ s, Module.finrank K U = j) ∧ ∀ U : Submodule K V, Module.finrank K U = j → (latsDisc (R := 𝓞 K) (hRes h U) n).Nonempty → ∃ U₀ ∈ s, ∃ g : isom h, g • U₀ = U := by
  intro K V _ _ _ _ _ _ _ _ h hK hs hp hO j n hn
  have hW := GlobalTheory.T.witt_extension_totally_definite_hermitian K V h hK hs hp
  have hmaxOf : ∀ (U : Submodule K V) (M : Submodule (𝓞 K) U), ∀ P ∈ badP (hRes h U) M, P.IsMaximal := by
    intro U M P hP
    unfold badP at hP
    exact hP.1
  obtain ⟨Q, hQ⟩ : ∃ Q : Submodule K V → Ideal (𝓞 K) → Prop, ∀ U I, Q U I ↔
      (Module.finrank K U = j ∧ ∃ M : Submodule (𝓞 K) U, IsMaxLat (hRes h U) M ∧
        ∏ᶠ P ∈ badP (hRes h U) M, P = I) := ⟨_, fun _ _ => Iff.rfl⟩
  have hpick : ∀ I : Ideal (𝓞 K), ∃ U₀ : Submodule K V, (∃ U, Q U I) → Q U₀ I := by
    intro I
    by_cases hI : ∃ U, Q U I
    · obtain ⟨U, hU⟩ := hI
      exact ⟨U, fun _ => hU⟩
    · exact ⟨⊥, fun h' => absurd h' hI⟩
  choose pick hpickQ using hpick
  obtain ⟨hfin, hcard⟩ := Formalism.HermitianLatticeCounting.P.ideal_norm_le_count K (n : ℝ) (by exact_mod_cast hn)
  refine ⟨(hfin.toFinset.filter (fun I => ∃ U, Q U I)).image pick, ?_, ?_, ?_⟩
  · calc _ ≤ (hfin.toFinset.card : ℝ) := by
          exact_mod_cast Finset.card_image_le.trans (Finset.card_filter_le _ _)
      _ = _ := by rw [Set.ncard_eq_toFinset_card _ hfin]
      _ ≤ _ := hcard
  · intro U hU
    obtain ⟨I, hI, rfl⟩ := Finset.mem_image.1 hU
    exact ((hQ _ _).1 (hpickQ I (Finset.mem_filter.1 hI).2)).1
  · intro U hUj hne
    obtain ⟨L, hL⟩ := hne
    unfold latsDisc at hL
    obtain ⟨hLi, hLd⟩ := hL
    obtain ⟨-, hsU, hpU, -⟩ := hW.2 U
    have hnU := nondeg (hRes h U) hpU
    obtain ⟨M, hM, hLM⟩ := (GlobalTheory.T.exists_maximal_integralHermitianLattice_orthonormal_maximal K U (hRes h U) hK hsU hnU).1 L hLi
    have hd := (GlobalTheory.Mass.DiscOrder.main K U (hRes h U) hK hsU hnU L hLi).2.2.1 M hM.1 hLM
    obtain ⟨hbf, hdisc, -, -⟩ := GlobalTheory.MaxLatStruct.main K U (hRes h U) hK hsU hnU M hM
    obtain ⟨I, hIdef⟩ : ∃ I, ∏ᶠ P ∈ badP (hRes h U) M, P = I := ⟨_, rfl⟩
    have hnorm : Ideal.absNorm I = discN (hRes h U) M := by
      rw [hdisc, ← hIdef, finprod_mem_eq_finite_toFinset_prod _ hbf,
        finprod_mem_eq_finite_toFinset_prod _ hbf, map_prod]
    have hdv : Ideal.absNorm I ∣ n := ⟨idxN M L ^ 2, by rw [hnorm, ← hLd]; exact hd.2⟩
    have hpos : 0 < Ideal.absNorm I := Nat.pos_of_dvd_of_pos hdv hn
    have hID : I ∈ hfin.toFinset := by
      refine hfin.mem_toFinset.2 ⟨fun hb => by simp [hb] at hpos, ?_⟩
      exact_mod_cast Nat.le_of_dvd hn hdv
    have hex : ∃ U', Q U' I := ⟨U, (hQ U I).2 ⟨hUj, M, hM, hIdef⟩⟩
    obtain ⟨hj0, M₀, hM₀, hkey⟩ := (hQ _ _).1 (hpickQ I hex)
    obtain ⟨-, hs0, hp0, -⟩ := hW.2 (pick I)
    have hn0 := nondeg (hRes h (pick I)) hp0
    obtain ⟨hbf0, -, -, -⟩ := GlobalTheory.MaxLatStruct.main K (pick I) (hRes h (pick I)) hK hs0 hn0 M₀ hM₀
    have hbeq : badP (hRes h (pick I)) M₀ = badP (hRes h U) M := by
      ext P
      rw [mem_iff_prod_le hbf0 (hmaxOf _ _) P, mem_iff_prod_le hbf (hmaxOf _ _) P, hkey, hIdef]
    obtain ⟨e, he⟩ := GlobalTheory.T.definite_hermitian_isometric_of_same_bad_primes K (pick I) (hRes h (pick I)) hK hs0 hp0 hO (↥U) (hRes h U) hsU hpU
      (by rw [hj0, hUj]) M₀ M hM₀ hM hbeq
    obtain ⟨g, hg, hgx⟩ := hW.1 (pick I) U e (fun x y => he x y)
    refine ⟨pick I, Finset.mem_image.2 ⟨I, Finset.mem_filter.2 ⟨hID, hex⟩, rfl⟩, ⟨g, hg⟩, ?_⟩
    ext y
    change y ∈ Formalism.HermitianLatticesTheory.gmap g (pick I) ↔ y ∈ U
    unfold Formalism.HermitianLatticesTheory.gmap
    rw [Submodule.mem_map]
    constructor
    · rintro ⟨x, hx, rfl⟩
      have := hgx ⟨x, hx⟩
      change g x ∈ U
      rw [this]
      exact (e ⟨x, hx⟩).2
    · intro hy
      refine ⟨(e.symm ⟨y, hy⟩ : V), (e.symm ⟨y, hy⟩).2, ?_⟩
      change g _ = y
      rw [hgx (e.symm ⟨y, hy⟩)]
      simp

end GlobalTheory.Mass.FewOrbits
end
end

section

open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical

theorem _root_.GlobalTheory.T.isHermIsometryGraphModScalar_flagPairIota : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ) (N : NF H r), ∀ (g : ℕ) (Λ : Submodule (𝓞 K) V), 1 ≤ g → N.IsTerm g Λ → IsModIso H (g : 𝓞 K) (flagPairDefinitePartLattice N.F' N.F Λ) (flagPairDefinitePartLattice N.F N.F' Λ) (iotaGraph N.F N.F' Λ (g : 𝓞 K)) := by
  first | exact @GlobalTheory.ModIdent.isModIso_iota | exact GlobalTheory.ModIdent.isModIso_iota | (intros; apply GlobalTheory.ModIdent.isModIso_iota <;> assumption)
end

section

open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.DSId GlobalTheory.Jet
open scoped InnerProductSpace ComplexOrder

theorem _root_.GlobalTheory.T.jet_uniqueness_algebraic : ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (n : ℕ) (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ V) (lam : Fin n → ℝ) (g : ℝ) (u : V), GlRel E → IsUnitary ε E → KHighest ε E (LamOf ε lam) u → FiniteDimensional ℂ (kSpan ε E u) → (∀ a b : Fin n, a < b → ε a ≠ ε b → g ≤ lam a - lam b) → 2 * (n : ℝ) < g → ∀ (V' : Type) [AddCommGroup V'] [Module ℂ V'] (E' : Fin n → Fin n → Module.End ℂ V') (ι : V →ₗ[ℂ] V') (ev : V' →ₗ[ℂ] V), GlRel E' → (∀ c d, ε c = ε d → ∀ x ∈ kSpan ε E u, ι (E c d x) = E' c d (ι x)) → (∀ y, ev y ∈ kSpan ε E u) → (∀ c d, ε c = ε d → ∀ y, ev (E' c d y) = E c d (ev y)) → (∀ G ∈ Vminus ε E (LamOf ε lam) u, ∑ a, ∑ b, E' a b (ι (at1 G a b)) = 0) → (∀ x ∈ kSpan ε E u, ev (ι x) = 0) → ∀ (w : List (Fin n × Fin n)), ∀ x ∈ kSpan ε E u, ev (ew E' w (ι x)) = 0 := by
  first | exact @GlobalTheory.Jet.UniqAlg.uniqAlg | exact GlobalTheory.Jet.UniqAlg.uniqAlg | (intros; apply GlobalTheory.Jet.UniqAlg.uniqAlg <;> assumption)
end

section

open Polynomial Formalism.MainNotions.ArithmeticCylinders GlobalTheory.GLq GlobalTheory.GLm
open scoped Classical

theorem _root_.GlobalTheory.T.mirabolicInduction_blockDiag_eq_harishChandra_gelfandGraev : ∀ (g : ℕ) [Fact g.Prime] (ψ : AddChar (ZMod g) ℂ) (i k : ℕ) (ρ : Gn g i → ℂ), i ≤ k → IsClass ρ → ∀ h : Gn g k, indR ψ i (k + 1) ρ (diag1 h (k + 1)) = hc i (k - i) ρ (gg ψ (k - i)) k h := by
  first | exact @GlobalTheory.GLm.indR_diag1_eq_hc_gg | exact GlobalTheory.GLm.indR_diag1_eq_hc_gg | (intros; apply GlobalTheory.GLm.indR_diag1_eq_hc_gg <;> assumption)
end

section

open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.DSId GlobalTheory.Jet
open scoped InnerProductSpace ComplexOrder

noncomputable section

namespace GlobalTheory.Jet.Schmid

theorem rhoN_add_rhoC {n : ℕ} (ε : Fin n → Bool) (a : Fin n) :
    Formalism.REAL.rhoN ε a + Formalism.REAL.rhoC ε a = ((n : ℝ) - 1) / 2 - ((a : ℕ) : ℝ) := by
  have h1 : (univ.filter fun b => a < b ∧ ε b = ε a).card + (univ.filter fun b => a < b ∧ ε b ≠ ε a).card
      = n - 1 - a := by
    rw [← Finset.filter_filter, ← Finset.filter_filter, Finset.card_filter_add_card_filter_not,
      Finset.filter_lt_eq_Ioi, Fin.card_Ioi]
  have h2 : (univ.filter fun b => b < a ∧ ε b = ε a).card + (univ.filter fun b => b < a ∧ ε b ≠ ε a).card
      = a := by
    rw [← Finset.filter_filter, ← Finset.filter_filter, Finset.card_filter_add_card_filter_not,
      Finset.filter_gt_eq_Iio, Fin.card_Iio]
  have ha := a.2
  have h3 : (univ.filter fun b => a < b ∧ ε b = ε a).card + (univ.filter fun b => a < b ∧ ε b ≠ ε a).card
      + a + 1 = n := by omega
  have h3' := congrArg (Nat.cast : ℕ → ℝ) h3
  have h2' := congrArg (Nat.cast : ℕ → ℝ) h2
  push_cast at h3' h2'
  unfold Formalism.REAL.rhoN Formalism.REAL.rhoC
  linarith

theorem nsq_sub_root {n : ℕ} (u : Fin n → ℝ) {a b : Fin n} (hab : a ≠ b) :
    Formalism.REAL.nsq (u - Formalism.REAL.root a b) = Formalism.REAL.nsq u - 2 * (u a - u b) + 2 := by
  have : ∀ i, (u - Formalism.REAL.root a b) i * (u - Formalism.REAL.root a b) i =
      u i * u i - 2 * ((if i = a then u i else 0) - (if i = b then u i else 0)) +
        ((if i = a then 1 else 0) + (if i = b then 1 else 0)) := by
    intro i
    simp only [Formalism.REAL.root, Pi.sub_apply, Pi.single_apply]
    by_cases h1 : i = a <;> by_cases h2 : i = b
    · exact absurd (h1.symm.trans h2) hab
    all_goals simp [h1, h2, hab, hab.symm]
    all_goals ring
  simp only [Formalism.REAL.nsq, Formalism.REAL.dot, this, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  simp
  norm_num

theorem vNormSq_sub_root_lt {n : ℕ} (ε : Fin n → Bool) {μ : Fin n → ℝ} (hμ : StrictAnti μ)
    {a b : Fin n} (hab : a < b) :
    Formalism.MainNotions.S.vNormSq ε (Formalism.QuantumDeterminants.lowK ε μ - Formalism.REAL.root a b) < Formalism.MainNotions.S.vNormSq ε (Formalism.QuantumDeterminants.lowK ε μ) := by
  unfold Formalism.MainNotions.S.vNormSq
  rw [show Formalism.QuantumDeterminants.lowK ε μ - Formalism.REAL.root a b + (2 : ℝ) • Formalism.REAL.rhoC ε
      = (Formalism.QuantumDeterminants.lowK ε μ + (2 : ℝ) • Formalism.REAL.rhoC ε) - Formalism.REAL.root a b by abel,
    nsq_sub_root _ hab.ne]
  have h1 := hμ hab
  have h2 := rhoN_add_rhoC ε a
  have h3 := rhoN_add_rhoC ε b
  have h4 : ((a : ℕ) : ℝ) + 1 ≤ ((b : ℕ) : ℝ) := by exact_mod_cast hab
  simp only [Formalism.QuantumDeterminants.lowK, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  linarith

theorem thetaA_one {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {n : ℕ}
    (E : Fin n → Fin n → Module.End ℂ V) (G : Arr V n 1) :
    thetaA E 1 G = ∑ a, ∑ b, E a b (at1 G a b) := by
  rw [theta_map_word_sum_apply, ← Fintype.sum_prod_type']
  refine Fintype.sum_equiv (Equiv.funUnique (Fin 1) (Fin n × Fin n)) _ _ fun α => ?_
  have h : α = fun _ => (α 0) := fin_one_fun_eq_const_apply_zero α
  have e : at1 G (α 0).1 (α 0).2 = G α := by
    conv_rhs => rw [h]
    rfl
  simp only [Equiv.funUnique_apply]
  change _ = E (α 0).1 (α 0).2 (at1 G (α 0).1 (α 0).2)
  rw [e]
  simp [ew]

theorem mul_vminus_eq_zero : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (V : Submodule ℂ H) (E : Fin n → Fin n → Module.End ℂ V) (lam : Fin n → ℝ) (u : V), IsHCParam lam → IsDS ε lam σ → IsDer ε σ V E → KHighest ε E (LamOf ε lam) u → FiniteDimensional ℂ (kSpan ε E u) → ∀ G ∈ Vminus ε E (LamOf ε lam) u, ∑ a, ∑ b, E a b (at1 G a b) = 0 := by
  intro n ε H _ _ _ σ V E lam u hl hσ hD hu hfd F hF
  have hg := hD.1
  obtain ⟨-, hθ⟩ := (arr_module_facts V n ε E 1).1 hg
  obtain ⟨-, -, hst, -, -, -, hpf⟩ := pfil_facts_hold V n ε E u hg
  have hker : Vminus ε E (LamOf ε lam) u ≤ LinearMap.ker (thetaA E 1) := by
    apply isotypic_part_le_of_forall
    intro y hy μ hμ hyh
    apply compact_span_le_of_stable
    · intro c d _ x hx
      rw [LinearMap.mem_ker] at hx ⊢
      rw [hθ, hx, map_zero]
    · rw [LinearMap.mem_ker]
      obtain ⟨a, b, hba, hne, rfl⟩ := hμ
      by_contra hw0
      have hμeq : LamOf ε lam + Formalism.REAL.root a b = lowK ε lam - Formalism.REAL.root b a := by
        rw [root_swap' a b, sub_eq_add_neg]; rfl
      have hwh : KHighest ε E (lowK ε lam - Formalism.REAL.root b a) (thetaA E 1 y) := by
        refine ⟨fun c => ?_, fun c d hcd hcomp => ?_⟩
        · rw [← hθ, hyh.1 c, map_smul, hμeq]
        · rw [← hθ, hyh.2 c d hcd hcomp, map_zero]
      have hmem : thetaA E 1 y ∈ pfil ε E u 1 := (theta_filtration_holds V n ε E u hg).1 1 y hy
      have := hpf hfd 1
      have hf : FiniteDimensional ℂ (kSpan ε E (thetaA E 1 y)) :=
        Submodule.finiteDimensional_of_le (compact_span_le_of_stable (hst 1) hmem)
      have hK := (GlobalTheory.Jet.KType.kType_iff n ε H σ V E hσ.2.2.1 hD).1 _ _ hw0 hwh hf
      exact absurd (hσ.2.2.2.2.2.2 _ _ hK) (not_le.mpr (vNormSq_sub_root_lt ε hl.1 hba))
  rw [← thetaA_one]
  exact hker hF

end GlobalTheory.Jet.Schmid
end
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.IwConst

namespace GlobalTheory.IwConst

theorem finrank_le_card_of_isotropic {n : ℕ} (ε : Fin n → Bool) (V : Submodule ℂ (Fin n → ℂ))
    (hV : ∀ x ∈ V, star x ⬝ᵥ (Formalism.REAL.Jm ε *ᵥ x) = 0) (b : Bool) :
    Module.finrank ℂ V ≤ (univ.filter fun a => ε a = b).card := by

  let f : V →ₗ[ℂ] ({a // ε a = b} → ℂ) :=
    (LinearMap.funLeft ℂ ℂ (Subtype.val : {a // ε a = b} → Fin n)) ∘ₗ V.subtype
  have hf : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    have hx0 : ∀ a, ε a = b → (x : Fin n → ℂ) a = 0 := fun a ha => by
      simpa [f] using congrFun hx ⟨a, ha⟩
    have hterm : ∀ a, star ((x : Fin n → ℂ) a) * ((if ε a then (1 : ℂ) else -1) * (x : Fin n → ℂ) a)
        = (if b then (-1 : ℂ) else 1) * ((Complex.normSq ((x : Fin n → ℂ) a) : ℝ) : ℂ) := by
      intro a
      by_cases ha : ε a = b
      · simp [hx0 a ha]
      · have hb : ε a = !b := by cases h1 : ε a <;> cases b <;> simp_all
        rw [Complex.normSq_eq_conj_mul_self, hb]
        cases b <;> simp [Complex.star_def] <;> ring
    have h0 := hV x x.2
    simp only [Formalism.REAL.Jm, Matrix.mulVec_diagonal, dotProduct, Pi.star_apply, hterm,
      ← Finset.mul_sum] at h0
    have hc : (if b then (-1 : ℂ) else 1) ≠ 0 := by cases b <;> simp
    have hsum : (∑ a, Complex.normSq ((x : Fin n → ℂ) a) : ℝ) = 0 := by
      have := (mul_eq_zero.mp h0).resolve_left hc
      exact_mod_cast this
    have hall := (Finset.sum_eq_zero_iff_of_nonneg (fun a _ => Complex.normSq_nonneg _)).mp hsum
    ext a
    simpa using hall a (Finset.mem_univ a)
  calc Module.finrank ℂ V ≤ Module.finrank ℂ ({a // ε a = b} → ℂ) :=
        LinearMap.finrank_le_finrank_of_injective hf
    _ = Fintype.card {a // ε a = b} := Module.finrank_fintype_fun_eq_card ℂ
    _ = (univ.filter fun a => ε a = b).card := Fintype.card_subtype _

private theorem finrank_last_eq_sum_of_finrank_succ {n : ℕ} : ∀ (a : ℕ) (j : Fin a → ℕ)
    (W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)), W 0 = ⊥ →
    (∀ i : Fin a, Module.finrank ℂ (W i.succ) = Module.finrank ℂ (W i.castSucc) + j i) →
    Module.finrank ℂ (W (Fin.last a)) = ∑ i, j i := by
  intro a
  induction a with
  | zero =>
    intro j W h0 _
    simp [show Fin.last 0 = (0 : Fin 1) from rfl, h0]
  | succ a ih =>
    intro j W h0 hstep
    have hprev := ih (fun i => j i.castSucc) (fun i => W i.castSucc) (by simpa using h0)
      (fun i => by have hs := hstep i.castSucc; rw [Fin.succ_castSucc] at hs; exact hs)
    rw [Fin.sum_univ_castSucc, ← hprev, ← Fin.succ_last, hstep (Fin.last a)]

theorem finrank_last_eq_sum {n : ℕ} {ε : Fin n → Bool} {a : ℕ} {j : Fin a → ℕ}
    {W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)} (h : IsIsoFlag ε j W) :
    Module.finrank ℂ (W (Fin.last a)) = ∑ i, j i :=
  finrank_last_eq_sum_of_finrank_succ a j W h.1 h.2.2.1

private theorem sq_sum_eq_sum_sq_add_two_mul_sum_lt' {a : ℕ} (j : Fin a → ℕ) :
    (∑ i, j i) ^ 2 = ∑ i, j i ^ 2 + 2 * ∑ i, ∑ k ∈ univ.filter (fun k => i < k), j i * j k := by
  have split : ∀ i k : Fin a, j i * j k = (if i < k then j i * j k else 0) +
      (if i = k then j i * j k else 0) + (if k < i then j i * j k else 0) := by
    intro i k
    rcases lt_trichotomy i k with h | h | h
    · simp [h, h.ne, not_lt.mpr h.le]
    · simp [h]
    · simp [h, h.ne', not_lt.mpr h.le]
  have hsym : ∑ i, ∑ k, (if k < i then j i * j k else 0) = ∑ i, ∑ k, (if i < k then j i * j k else 0) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
    rw [mul_comm]
  have hexp : ∑ i, ∑ k, j i * j k = ∑ i, ∑ k, ((if i < k then j i * j k else 0) +
      (if i = k then j i * j k else 0) + (if k < i then j i * j k else 0)) :=
    Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => split i k
  have hdiag : ∑ i, ∑ k, (if i = k then j i * j k else 0) = ∑ i, j i ^ 2 := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_ite_eq]
    simp [sq]
  rw [sq, Finset.sum_mul_sum, hexp]
  simp only [Finset.sum_add_distrib]
  rw [hsym, hdiag]
  simp only [Finset.sum_filter]
  ring

theorem flag_dims : ∀ (n : ℕ) (ε : Fin n → Bool) (a : ℕ) (j : Fin a → ℕ) (W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)), IsIsoFlag ε j W → ∀ (p q : ℕ), (univ.filter fun a => ε a = true).card = p → (univ.filter fun a => ε a = false).card = q → p + q = n ∧ n ^ 2 = 2 * dimN n j + ((n - 2 * ∑ i, j i) ^ 2 + 2 * ∑ i, j i ^ 2) ∧ p ^ 2 + q ^ 2 = dimN n j + ((p - ∑ i, j i) ^ 2 + (q - ∑ i, j i) ^ 2 + ∑ i, j i ^ 2) := by
  intro n ε a j W h p q hp hq
  have hpq : p + q = n := by
    rw [← hp, ← hq]
    have := Finset.card_filter_add_card_filter_not (s := (univ : Finset (Fin n)))
      (fun a => ε a = true)
    simpa using this

  have hV : ∀ x ∈ W (Fin.last a), star x ⬝ᵥ (Formalism.REAL.Jm ε *ᵥ x) = 0 :=
    fun x hx => h.2.2.2 x hx x hx
  have hS := finrank_last_eq_sum h
  have hSp : ∑ i, j i ≤ p := by
    rw [← hS, ← hp]; exact finrank_le_card_of_isotropic ε _ hV true
  have hSq : ∑ i, j i ≤ q := by
    rw [← hS, ← hq]; exact finrank_le_card_of_isotropic ε _ hV false
  have hsq := sq_sum_eq_sum_sq_add_two_mul_sum_lt' j
  subst hpq
  simp only [dimN]
  set S := ∑ i, j i
  set X := ∑ i, j i ^ 2
  set T := ∑ i, ∑ k ∈ univ.filter (fun k => i < k), j i * j k
  obtain ⟨P, rfl⟩ := Nat.exists_eq_add_of_le hSp
  obtain ⟨Q, rfl⟩ := Nat.exists_eq_add_of_le hSq
  have e1 : S + P + (S + Q) - 2 * S = P + Q := by omega
  have e2 : S + P - S = P := by omega
  have e3 : S + Q - S = Q := by omega
  rw [e1, e2, e3]
  refine ⟨by trivial, ?_, ?_⟩ <;> nlinarith [hsq]

end GlobalTheory.IwConst
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

noncomputable section

namespace GlobalTheory.FlagMeas

theorem typeSet_measurable_invariant : ∀ (I : AutInst) (a : ℕ) (j : Fin a → ℕ) (B : Set (Fin a → ℝ)), MeasurableSet B → MeasurableSet (typeSet I j B) ∧ (∀ γ ∈ I.GFset, ∀ x ∈ typeSet I j B, γ * x ∈ typeSet I j B) ∧ ∀ x ∈ typeSet I j B, ∀ k ∈ I.Kset, (x.1, x.2 * k) ∈ typeSet I j B := by
  intro I a j B hB
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨s, hs, hm, he⟩ := type_measurable I a j
    have : typeSet I j B = {x : I.GA | ∃ τ, HasType I x j τ} ∩ s ⁻¹' B := by
      ext x
      constructor
      · rintro ⟨τ, h1, h2⟩
        exact ⟨⟨τ, h2⟩, by rw [Set.mem_preimage, he x τ h2]; exact h1⟩
      · rintro ⟨⟨τ, h2⟩, h1⟩
        rw [Set.mem_preimage, he x τ h2] at h1
        exact ⟨τ, h1, h2⟩
    rw [this]
    exact hm.inter (hs hB)
  · rintro γ ⟨g, hg, h1, h2⟩ x ⟨τ, hτ, h⟩
    exact ⟨τ, hτ, ((GlobalTheory.PointEquivariance.equivariance I x g γ hg h1 h2).2.2.2.2.1 a j τ).2 h⟩
  · rintro x ⟨τ, hτ, h⟩ k hk
    refine ⟨τ, hτ, GlobalTheory.PointEquivariance.hasType_of I x (x.1, x.2 * k) (OrderIso.refl _) ?_
      (fun _ => rfl) (fun _ => rfl) j τ h⟩
    have e : ((x.1, x.2 * k) : I.GA) = x * (1, k) := Prod.ext (mul_one _).symm rfl
    rw [e]
    exact (GlobalTheory.PointEquivariance.lamX_mul_eq_iff I x (1, k)).1 hk

end GlobalTheory.FlagMeas
end
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

theorem _root_.GlobalTheory.T.det_conj_on_matrices_killing_into_subspace : ∀ (n : ℕ) (f g : Matrix (Fin n) (Fin n) ℂ) (P Q : Submodule ℂ (Fin n → ℂ)) (H : Submodule ℂ (Matrix (Fin n) (Fin n) ℂ)), f * g = 1 → ‖f.det‖ = 1 → (∀ y ∈ P, f *ᵥ y ∈ P) → (∀ y ∈ Q, f *ᵥ y ∈ Q) → (∀ X, X ∈ H ↔ (∀ y ∈ P, X *ᵥ y = 0) ∧ ∀ y, X *ᵥ y ∈ Q) → Module.finrank ℂ H = (n - Module.finrank ℂ P) * Module.finrank ℂ Q ∧ ∀ φ : H →ₗ[ℂ] H, (∀ X : H, ((φ X : H) : Matrix (Fin n) (Fin n) ℂ) = f * (X : Matrix (Fin n) (Fin n) ℂ) * g) → ‖LinearMap.det φ‖ = detOn f Q ^ (n - Module.finrank ℂ P) * detOn f P ^ Module.finrank ℂ Q := by
  first | exact @GlobalTheory.HomConjDet.det_conj_hom | exact GlobalTheory.HomConjDet.det_conj_hom | (intros; apply GlobalTheory.HomConjDet.det_conj_hom <;> assumption)
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase

theorem _root_.GlobalTheory.T.exists_scalarStable_latticeAutomorphismFundamentalDomain : ∀ (E : Type) [Field E] [NumberField E], IsTotallyComplex E → ∀ j : ℕ, ∀ Λ : Submodule (𝓞 E) (Fin j → E), Submodule.IsFullLattice E Λ → ∃ D : Set (MatInf E j), MeasurableSet D ∧ D ⊆ {g | 0 < detNorm E j g} ∧ (∀ g, 0 < detNorm E j g → ∃ γ ∈ autGL E j Λ, γ * g ∈ D) ∧ (∀ g ∈ D, ∀ t : ℝ, 0 < t → (fun w a b => (t : ℂ) * g w a b) ∈ D) ∧ ∀ (G : MatInf E j → ENNReal) (A : Set (MatInf E j)), Measurable (fun g => {g | 0 < detNorm E j g}.indicator G g) → (∀ γ ∈ autGL E j Λ, ∀ g, 0 < detNorm E j g → G (γ * g) = G g) → MeasurableSet A → A ⊆ {g | 0 < detNorm E j g} → (∀ γ ∈ autGL E j Λ, ∀ g ∈ A, γ * g ∈ A) → covol (autGL E j Λ) (((haarGL E j).restrict {g | 0 < detNorm E j g}).withDensity G) A = ∫⁻ g in A ∩ D, G g ∂(haarGL E j) := by
  first
  | exact @GlobalTheory.LatDom.exists_cone_domain
  | intro E _ _ hE j Λ hΛ
    exact GlobalTheory.LatDom.exists_cone_domain E hE j Λ hΛ.toIsLattice
end
