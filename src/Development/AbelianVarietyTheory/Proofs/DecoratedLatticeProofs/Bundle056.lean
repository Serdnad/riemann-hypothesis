module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.EntryAgree
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle005
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle058
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PhiTopAgree
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle052
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle053
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BlockDetLowUEmb
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle033
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle051
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ResiduesOfCompletionAtPrimeWithUniformizer
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle063
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle066
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle070
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle064
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ZpowMulMemPow
public import Formalism.LocalToGlobal.Columns.HeckeSp
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CardKerSubspacesAndHeckePolyOfConvolution
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.Coalgebra.CoassocSimps
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.VolumeFlatSection
import Development.AbelianVarietyTheory.Definitions.Foundations.IsIwasawaOfIsCompact
import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle003
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle073
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle038
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell

@[expose] public section

section

open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.TwBridge GlobalTheory.SymBridge GlobalTheory.LatClass GlobalTheory.IndefiniteRowSideFullHecke.NormalRepresentationLattice

noncomputable section
namespace GlobalTheory.TwNormalReps

theorem val_unif_of {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {ϖ : kˣ} (hϖ : GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.IsUnif ϖ) : valuation k (ϖ : k) = uniformizer k := by
  apply le_antisymm
  · rw [le_uniformizer_iff]; exact (hϖ _).2 le_rfl
  · obtain ⟨x, hx⟩ := ValuativeRel.valuation_surjective (uniformizer k)
    rw [← hx]
    exact (hϖ x).1 (by rw [hx]; exact uniformizer_lt_one)

theorem isGL_one {X : Fields} {R : Ranks} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {ι : X.E →+* k} {j c : ℕ} {g : GL (XIx (Fin R.k) (Fin R.t) j ⊕ Fin c) k}
    (hg : IsGL ι (1 : AutY X R j) g) : g = 1 := by
  obtain ⟨e, -, he⟩ := hg
  apply Units.ext
  rw [he]
  ext i l
  simp [toLoc, Pi.single_apply, e.injective.eq_iff, Matrix.one_apply]

theorem exists_normal_rep : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S₀ : Set ℕ) (mu : Tup X.F X.E X.K S₀) (cst : LocCst X (rowSG Pr sel mu)) (σ₀ : X.K →+* ℂ) (P : rowSG Pr sel mu) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : X.E →+* k) (s : ℕ) (W : TwData k) [MeasurableSpace k] [BorelSpace k] (ν : Measure k), IsUnitVol ν → cst.Ok → AtTwist (R := R) sel mu cst σ₀ P ι s W → ∀ (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (G : ChGlob X R.m), L.Ok Ch sel mu cst G s → IdxProd sel mu cst L → (∀ j c (h : j + 1 + c = s) (b : L.β (j + 1)) (g' : GL (XIx (Fin R.k) (Fin R.t) (j + 1) ⊕ Fin (c + 1)) k), IsGL ι (L.h (j + 1) b P) g' → ∃ (al : L.β j) (g : GL (XIx (Fin R.k) (Fin R.t) (j) ⊕ Fin (c + 1 + 1)) k), IsGL ι (L.h j al P) g ∧ flat W.ψ ν ((W.T s R).mu (j + 1)) ((W.T s R).Phi j (c + 1) (by omega)) g g' ≠ 0) → ∀ j c (h : j + c = s) (al : L.β j) (g : GL (XIx (Fin R.k) (Fin R.t) (j) ⊕ Fin (c + 1)) k), IsGL ι (L.h j al P) g → ∃ r ∈ GlobalTheory.RootEx.R k (XIx (Fin R.k) (Fin R.t) (j)) (c + 1) 1, GlobalTheory.IndefiniteRowSideFullHecke.NormalRepresentationLattice.IsNormalRep (W.T s R) W.ϖ j c h (r * g) := by
  intro X Pr R Ch sel S₀ mu cst σ₀ P k _ _ _ _ ι s W _ _ ν hν hcst hAt L G hL hIdx hstep
  haveI := hν.1
  have hϖ := val_unif_of W.unif
  have hb : ∀ j c h, latOf ((W.T s R).bas j c h) = latOf 1 := fun _ _ _ => rfl
  have H : (∀ j c h x, (W.T s R).Phi j c h x ≠ 0 → IntM x) ∧
      (∀ j c h x y, MaxM y → (W.T s R).Phi j c h (x + y) = (W.T s R).Phi j c h x) ∧
      ∀ j c h, ((W.T s R).lev j c h).J ≤ KO k _ :=
    GlobalTheory.Proof.TwistSupportPeriodicLevels.ofTwist_support_periodic_levels k s _ _ _ _ W.δ W.tame W.η _ _ (fun _ _ _ => rfl)
  obtain ⟨hs, hp, -⟩ := H
  intro j
  induction j with
  | zero =>
    intro c h al g hg
    rw [hL.zero_h] at hg
    obtain rfl := isGL_one hg
    exact ⟨1, one_mem _, by rw [one_mul]; exact normal_one hb c h⟩
  | succ j ih =>
    intro c h al g' hg'
    obtain ⟨al', g, hg, hf⟩ := hstep j c h al g' hg'
    obtain ⟨r, hr, e', z', he', hz', hl⟩ := ih (c + 1) (by omega) al' g hg
    rw [lat_bas hb, ← nfBasis_one] at hl
    obtain ⟨x₀, h0⟩ := Function.ne_iff.1 (GlobalTheory.FlatSourceStable.flat_ne_zero_of_mem_R k _ _ c W.ψ ν _ _ g g' hf r hr)
    obtain ⟨r₂, hr₂, e, z, he, hz, hl₂⟩ := step_normal (NormalForm.normalFormModN k) hϖ W.cond he' hz'
      (hl ▸ om_supp (hs _ _ _) (r * g) g') (hl ▸ om_per hϖ (hp _ _ _) (r * g) g') h0
    exact ⟨r₂, hr₂, e, z, he, hz, by rw [lat_bas hb]; exact hl₂⟩

end GlobalTheory.TwNormalReps
end
end

section

open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.TwBridge GlobalTheory.SymBridge

noncomputable section
namespace GlobalTheory.TwBridge.TopHat

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem hat_coset_box [MeasurableSpace k] [BorelSpace k] {n : Type} [Fintype n]
    {ψ : AddChar k Circle} (hψ : HasConductor ψ 1) {ν : Measure k} (hν : IsUnitVol ν) {ε : k}
    (hε : ε ∈ 𝒪[k]) (c : kˣ) (y₀ : n → k) {η : n → k} (hη : ∀ i, η i * (c : k) ∈ 𝒪[k]) :
    hat ψ ν ε (cosetInd (box n c) (Submodule.Quotient.mk y₀)) η =
      ((nabs k c ^ Fintype.card n : ℝ) : ℂ) * ψ (ε * (η ⬝ᵥ y₀)) := by
  have := hν.1
  have := secondCountable k
  unfold hat
  rw [← integral_add_left_eq_self _ y₀]
  have e : ∀ y : n → k, cosetInd (box n c) (Submodule.Quotient.mk y₀) (y₀ + y) * (ψ (ε * (η ⬝ᵥ (y₀ + y))) : ℂ) =
      (Set.pi Set.univ fun _ => cball c).indicator (fun _ => (ψ (ε * (η ⬝ᵥ y₀)) : ℂ)) y := fun y => by
    have hy : (y₀ + y ∈ {y' : n → k | Submodule.Quotient.mk (p := box n c) y' = Submodule.Quotient.mk y₀}) ↔
        y ∈ Set.pi Set.univ fun _ => cball c := by
      simp [Submodule.Quotient.eq, mem_box, cball]
    by_cases h : y ∈ Set.pi Set.univ fun _ => cball c
    · have hi : ε * (η ⬝ᵥ y) ∈ 𝒪[k] := by
        refine mul_mem hε (sum_mem fun i _ => ?_)
        have h1 : valuation k (y i) ≤ valuation k (c : k) := h i trivial
        have h2 := (Valuation.mem_integer_iff _ _).1 (hη i)
        rw [Valuation.mem_integer_iff, map_mul]
        rw [map_mul] at h2
        calc valuation k (η i) * valuation k (y i) ≤ valuation k (η i) * valuation k (c : k) := mul_le_mul' le_rfl h1
          _ ≤ 1 := h2
      rw [cosetInd, Set.indicator_of_mem (hy.2 h), Set.indicator_of_mem h, dotProduct_add, mul_add,
        AddChar.map_add_eq_mul, hψ.eq_one (show _ ∈ cball (1 : kˣ) from hi)]
      simp
    · rw [cosetInd, Set.indicator_of_notMem (mt hy.1 h), Set.indicator_of_notMem h, zero_mul]
  simp only [e]
  rw [integral_indicator_const _ (MeasurableSet.univ_pi fun _ => (isOpen_cball c).measurableSet), Measure.real,
    Measure.pi_pi]
  simp only [measure_cball ν c, hν.2, mul_one, Finset.prod_const, Finset.card_univ]
  simp [nabs, ENNReal.toReal_pow]

theorem hat_coset_eq_ftY : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S₀ : Set ℕ) (mu : Tup X.F X.E X.K S₀) (cst : LocCst X (rowSG Pr sel mu)) (σ₀ : X.K →+* ℂ) (P : rowSG Pr sel mu) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : X.E →+* k) (s : ℕ) (W : TwData k) [MeasurableSpace k] [BorelSpace k] (ν : Measure k), IsUnitVol ν → cst.Ok → AtTwist (R := R) sel mu cst σ₀ P ι s W → 2 * cst.M ≤ cst.D P →
  ∀ (e' : XIx (Fin R.k) (Fin R.t) (s + 1) ≃ Fin (R.N (s + 1))) (e : Ix (Fin R.k ⊕ Fin (s + 1)) (Fin R.t) (s + 2) ⊕ Unit ≃ Fin (R.N R.m)),
    IsOrd xPos e' → IsOrd (Sum.elim zPos fun _ => R.N R.m - 1) e →
    ∀ (y : HomE X.E (R.N (s + 1)) (R.N R.m)) (y' : Sp X.E (R.N (s + 1))), (∀ l, IntAt P.1 ((qOf P.1 : X.E) ^ cst.M * y' l)) →
      hat W.ψ ν (-1) (cosetInd (box _ (W.ϖ ^ cst.M)) (Submodule.Quotient.mk fun a => ι (y' (e' a)))) ((toLoc ι e e' y) (Sum.inr ())) =
        σ₀ (ftY sel mu cst P (atNL X.E (R.N R.m) (R.N R.m - 1) ∘ₗ y) y') := by
  classical
  intro X Pr R Ch sel S₀ mu cst σ₀ P k _ _ _ _ ι s W _ _ ν hν _ hA hD e' e _ he y y' hy'
  haveI := hν.1
  have hint : ∀ a : X.E, ι a ∈ 𝒪[k] ↔ IntAt P.1 a := hA.compl.int
  have hlast : (e (Sum.inr ())).val = R.N R.m - 1 := he (Sum.inr ())
  have hNpos : R.N R.m - 1 < R.N R.m := by have := (e (Sum.inr ())).isLt; omega
  set η' := atNL X.E (R.N R.m) (R.N R.m - 1) ∘ₗ y with hη'
  have hη'v : ∀ v, η' v = y v (e (Sum.inr ())) := fun v => by
    simp only [hη', LinearMap.comp_apply, atNL, dif_pos hNpos, LinearMap.proj_apply]
    rw [show (⟨R.N R.m - 1, hNpos⟩ : Fin (R.N R.m)) = e (Sum.inr ()) from Fin.ext hlast.symm]
  have hrow : (toLoc ι e e' y) (Sum.inr ()) = fun a => ι (η' (Pi.single (e' a) 1)) := by
    funext a; simp [toLoc, hη'v]
  have hsum : η' y' = ∑ i, y' i * η' (Pi.single i 1) := by
    have : y' = ∑ i, y' i • Pi.single i (1 : X.E) := by ext j; simp [Pi.single_apply]
    conv_lhs => rw [this]

    simp [map_sum, map_smul]
  have hdot : (fun a => ι (η' (Pi.single (e' a) 1))) ⬝ᵥ (fun a => ι (y' (e' a))) = ι (η' y') := by

    rw [hsum, map_sum, dotProduct]
    exact Fintype.sum_equiv e' _ _ (fun a => by simp [mul_comm])
  have hϖ : (W.ϖ : k) = ι (qOf P.1 : X.E) := hA.compl.unif
  have hcM : ((W.ϖ ^ cst.M : kˣ) : k) = ι ((qOf P.1 : X.E) ^ cst.M) := by
    rw [Units.val_pow_eq_pow_val, hϖ, map_pow]
  rw [hrow, ftY, if_neg hA.nmem]
  by_cases hη : ∀ i : Fin (R.N (s + 1)), IntAt P.1 ((qOf P.1 : X.E) ^ cst.M * η' (Pi.single i 1))
  · rw [if_pos hη, hat_coset_box W.cond hν (neg_mem (one_mem _)) _ _ (fun a => ?_), hdot]
    · have hres : resCard k = qOf P.1 := ComplRes.resCard_eq hA.compl W.unif
      obtain ⟨p, hp, hpϖ⟩ := GlobalTheory.PeriodicIntegral.exists_irreducible_of_isUnif W.unif
      have hnabs : nabs k W.ϖ = (resCard k : ℝ)⁻¹ := nabs_uniformiser hp hpϖ.symm
      have hnM : nabs k (W.ϖ ^ cst.M) = ((qOf P.1 : ℝ) ^ cst.M)⁻¹ := by
        rw [show nabs k (W.ϖ ^ cst.M) = nabs k W.ϖ ^ cst.M by simp [nabs], hnabs, hres, inv_pow]
      have hcard : Fintype.card (XIx (Fin R.k) (Fin R.t) (s + 1)) = R.N (s + 1) := by
        simpa using Fintype.card_congr e'
      have hqi : ∀ j, ι ((qOf P.1 : X.E) ^ j) ∈ 𝒪[k] := fun j => by
        rw [map_pow, map_natCast]; exact pow_mem (natCast_mem _ _) _
      have hi : IntAt P.1 ((qOf P.1 : X.E) ^ cst.D P * ((epsSg : X.E) * η' y')) := by
        rw [← hint, hsum]
        obtain ⟨d, hd⟩ : ∃ d, cst.D P = d + 2 * cst.M := ⟨_, (Nat.sub_add_cancel hD).symm⟩
        have : (qOf P.1 : X.E) ^ cst.D P * ((epsSg : X.E) * ∑ i, y' i * η' (Pi.single i 1)) =
            -((qOf P.1 : X.E) ^ d *
              ∑ i, ((qOf P.1 : X.E) ^ cst.M * y' i) * ((qOf P.1 : X.E) ^ cst.M * η' (Pi.single i 1))) := by
          rw [hd, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_neg_distrib]
          refine Finset.sum_congr rfl fun i _ => ?_
          simp only [epsSg, Int.cast_neg, Int.cast_one]
          ring

        rw [this, map_neg, map_mul, map_sum]
        exact neg_mem (mul_mem (hqi _) (sum_mem fun i _ => by
          rw [map_mul]; exact mul_mem ((hint _).2 (hy' i)) ((hint _).2 (hη i))))
      have h1 := hA.psi _ hi
      have h2 : ι ((epsSg : X.E) * η' y') = -1 * ι (η' y') := by simp [epsSg]
      rw [map_mul σ₀, ← h1, h2, map_inv₀, map_pow, map_natCast, hnM, hcard]
      push_cast
      rw [inv_pow, ← pow_mul]
    · rw [show (fun a => ι (η' (Pi.single (e' a) 1))) a * ((W.ϖ ^ cst.M : kˣ) : k) =
        ι ((qOf P.1 : X.E) ^ cst.M * η' (Pi.single (e' a) 1)) by rw [hcM, ← map_mul, mul_comm]]
      exact (hint _).2 (hη _)
  · rw [if_neg hη, map_zero]
    by_contra hne
    have hm := mul_mem_of_hat_cosetInd_ne_zero k W.ψ W.cond ν _ (W.ϖ ^ cst.M) (-1) _ _ hne
    refine hη fun i => (hint _).1 ?_
    have h' := neg_mem (hm (e'.symm i))
    convert h' using 1
    rw [map_mul, ← hcM]
    simp only [Equiv.apply_symm_apply]
    ring

end GlobalTheory.TwBridge.TopHat
end
end

section

open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.SymBridge

theorem _root_.GlobalTheory.T.completionChain_lattice_entries_agree : ∀ (E K k : Type) [Field E] [NumberField E] [StarRing E] [Field K] [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (P : HeightOneSpectrum (𝓞 E)) (q : ℕ) (ι : E →+* k) (σ₀ : K →+* ℂ) (ψ₀ : AddChar (𝓞 E ⧸ P.asIdeal) K) (χ : ℕ → (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) (s κ : ℕ) (S : SymData k s κ), Comparison₂ P q ι σ₀ ψ₀ χ S → ∀ (τ j c : ℕ) (h : j + c = s) (n' c' n c₂ : ℕ), n' = κ + j * (τ + 1) → n = κ + (j + 1) * (τ + 1) → c' = c + 1 → c₂ = c → ∀ (e' : XIx (Fin κ) (Fin τ) j ⊕ Fin (c + 1) ≃ Fin (n' + c')) (e : XIx (Fin κ) (Fin τ) (j + 1) ⊕ Fin c ≃ Fin (n + c₂)), IsOrd (yPos xPos n') e' → IsOrd (yPos xPos n) e → ∀ (x : (Fin (n' + c') → E) →ₗ[E] (Fin (n + c₂) → E)) (a : Ix (Fin κ ⊕ Fin (s + 1)) (Fin τ) (j + 1)) (b : Ix (Fin κ ⊕ Fin (s + 1)) (Fin τ) j), (typeFrame S.ϖ (stdOrd (Fin κ) (Fin τ) (j + 1) c (by omega))).coords (typeFrame S.ϖ (stdOrd (Fin κ) (Fin τ) j (c + 1) (by omega))) (toLoc ι e e' x) a b = ι (LocE.entB q κ c' n' c₂ n (fun i => i + 1) (fun i => i + 1) x (zPos a) (zPos b)) := by
  first | exact @GlobalTheory.SymBridge.EntryBases.entries_agree | exact GlobalTheory.SymBridge.EntryBases.entries_agree | (intros; apply GlobalTheory.SymBridge.EntryBases.entries_agree <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.SymBridge

theorem _root_.GlobalTheory.T.iteratedLevelPattern_of_framePlaces : ∀ (F : Type) [Zero F] [One F] (κ ρ s τ j : ℕ) (R : ℕ → ℕ → F), ((∀ p', p' < κ + s + 1 → R p' p' = 1 ∧ ∀ p, p < κ + s + 1 + j * τ → p ≠ p' →
        (κ + s + 1 ≤ p ∨ symIdx κ ρ p' < symIdx κ ρ p ∨ (p' = κ + ρ ∧ p < κ)) → R p p' = 0) ∧
      (∀ p p', κ + s + 1 ≤ p' → p' < κ + s + 1 + j * τ → p < κ + s + 1 + j * τ →
        (p' - (κ + s + 1)) / τ < (p - (κ + s + 1)) / τ → R p p' = 0)) → (∀ (a b : Ix (Fin κ ⊕ Fin (s + 1)) (Fin τ) j), ¬ FreeIx ρ a b → R (zPos a) (zPos b) = if a = b then 1 else 0) := by
  first | exact @GlobalTheory.patOfPlaces | exact GlobalTheory.patOfPlaces | (intros; apply GlobalTheory.patOfPlaces <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.SymBridge

theorem _root_.GlobalTheory.T.iteratedLevelPattern_to_framePlaces : ∀ (F : Type) [Zero F] [One F] (κ ρ s τ j : ℕ) (R : ℕ → ℕ → F), (∀ (a b : Ix (Fin κ ⊕ Fin (s + 1)) (Fin τ) j), ¬ FreeIx ρ a b → R (zPos a) (zPos b) = if a = b then 1 else 0) → ((∀ p', p' < κ + s + 1 → R p' p' = 1 ∧ ∀ p, p < κ + s + 1 + j * τ → p ≠ p' →
        (κ + s + 1 ≤ p ∨ symIdx κ ρ p' < symIdx κ ρ p ∨ (p' = κ + ρ ∧ p < κ)) → R p p' = 0) ∧
      (∀ p p', κ + s + 1 ≤ p' → p' < κ + s + 1 + j * τ → p < κ + s + 1 + j * τ →
        (p' - (κ + s + 1)) / τ < (p - (κ + s + 1)) / τ → R p p' = 0)) := by
  first | exact @GlobalTheory.PatPlaces.pattern_to_places | exact GlobalTheory.PatPlaces.pattern_to_places | (intros; apply GlobalTheory.PatPlaces.pattern_to_places <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.SymBridge

theorem _root_.GlobalTheory.T.symLevel_character_by_residueCharacter : ∀ (E K k : Type) [Field E] [NumberField E] [StarRing E] [Field K] [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (P : HeightOneSpectrum (𝓞 E)) (q : ℕ) (ι : E →+* k) (σ₀ : K →+* ℂ) (ψ₀ : AddChar (𝓞 E ⧸ P.asIdeal) K) (χ : ℕ → (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) (s κ : ℕ) (S : SymData k s κ), Comparison₂ P q ι σ₀ ψ₀ χ S → ∀ (M : ℕ → ℕ → E), (∀ p p', p < κ + s + 1 → p' < κ + s + 1 → IntAt P (M p p')) → ∀ (g : S.P.J), (g : GL (Fin κ ⊕ Fin (s + 1)) k).val = Matrix.of (fun a b => ι (M (GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.framePos κ (s + 1) a) (GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.framePos κ (s + 1) b))) → ((S.P.lam g : ℂˣ) : ℂ) = σ₀ (ψ₀ (redP P (∑ i ∈ Finset.range (κ - 1), M i (i + 1) + ∑ i ∈ Finset.range (κ + s + 1 - κ - 1), M (κ + i) (κ + i + 1)))) := by
  first | exact @GlobalTheory.symLevel_lam_residue | exact GlobalTheory.symLevel_lam_residue | (intros; apply GlobalTheory.symLevel_lam_residue <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.SymBridge

theorem GlobalTheory.symLevel_lam_residue_elim : ∀ (E K k : Type) [Field E] [NumberField E] [StarRing E] [Field K] [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (P : HeightOneSpectrum (𝓞 E)) (q : ℕ) (ι : E →+* k) (σ₀ : K →+* ℂ) (ψ₀ : AddChar (𝓞 E ⧸ P.asIdeal) K) (χ : ℕ → (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) (s κ : ℕ) (S : SymData k s κ), Comparison₂ P q ι σ₀ ψ₀ χ S → ∀ (M : ℕ → ℕ → E), (∀ p p', p < κ + (s + 1) → p' < κ + (s + 1) → IntAt P (M p p')) → ∀ g : S.P.J, (g : GL (Fin κ ⊕ Fin (s + 1)) k).val = Matrix.of (fun a b => ι (M (Sum.elim (fun i => i.val) (fun i => κ + i.val) a) (Sum.elim (fun i => i.val) (fun i => κ + i.val) b))) → (S.P.lam g : ℂ) = σ₀ (ψ₀ (redP P (∑ i ∈ Finset.range (κ - 1), M i (i + 1) + ∑ i ∈ Finset.range (κ + s + 1 - κ - 1), M (κ + i) (κ + i + 1)))) := by
  intro E K k _ _ _ _ _ _ _ _ P q ι σ₀ ψ₀ χ s κ S hT M hM g hg
  exact GlobalTheory.symLevel_lam_residue E K k P q ι σ₀ ψ₀ χ s κ S hT M hM g hg
end

section

open NumberField IsDedekindDomain Matrix Formalism.L2.Col GlobalTheory.SymBridge

noncomputable section
namespace GlobalTheory.VolBridge

variable {E k : Type} [Field E] [Field k] (ι : E →+* k) {A : Type} [Fintype A] [DecidableEq A] {N : ℕ} (e : A ≃ Fin N)

def locHom : (Sp E N ≃ₗ[E] Sp E N) →* GL A k where
  toFun x := ⟨toLoc ι e e x.toLinearMap, toLoc ι e e (x⁻¹ : Sp E N ≃ₗ[E] Sp E N).toLinearMap,
    by
      rw [← toLoc_comp_square]
      have h : x.toLinearMap ∘ₗ (x⁻¹ : Sp E N ≃ₗ[E] Sp E N).toLinearMap = LinearMap.id := by
        ext v i; simp [LinearEquiv.coe_inv]
      rw [h, toLoc_id_square],
    by
      rw [← toLoc_comp_square]
      have h : (x⁻¹ : Sp E N ≃ₗ[E] Sp E N).toLinearMap ∘ₗ x.toLinearMap = LinearMap.id := by
        ext v i; simp [LinearEquiv.coe_inv]
      rw [h, toLoc_id_square]⟩
  map_one' := by
    ext1
    show toLoc ι e e (LinearEquiv.refl E (Sp E N)).toLinearMap = 1
    exact toLoc_id_square ι e
  map_mul' x y := by
    ext1
    show toLoc ι e e (x * y).toLinearMap = toLoc ι e e x.toLinearMap * toLoc ι e e y.toLinearMap
    rw [← toLoc_comp_square]
    rfl

theorem locHom_val (x : Sp E N ≃ₗ[E] Sp E N) : (locHom ι e x).val = toLoc ι e e x.toLinearMap := rfl

section Num
variable {A : Type} {N c c' : ℕ} (e : A ⊕ Fin c ≃ Fin (N + c')) (hcc : c' = c)
  (he : ∀ i : Fin c, (e (Sum.inr i)).val = N + i.val)

include hcc he in
theorem eX_lt (a : A) : (e (Sum.inl a)).val < N := by
  by_contra h
  push Not at h
  have hc : (e (Sum.inl a)).val - N < c := by have := (e (Sum.inl a)).isLt; omega
  have h2 : e (Sum.inr ⟨_, hc⟩) = e (Sum.inl a) := Fin.ext (by rw [he]; simp; omega)
  exact absurd (e.injective h2) (by simp)

def eX : A ≃ Fin N :=
  Equiv.ofBijective (fun a => ⟨(e (Sum.inl a)).val, eX_lt e hcc he a⟩) (by
    constructor
    · intro a b hab
      have : e (Sum.inl a) = e (Sum.inl b) := Fin.ext (by simpa using congrArg Fin.val hab)
      simpa using e.injective this
    · intro m
      rcases hm : e.symm (Fin.castAdd c' m) with a | i
      · refine ⟨a, Fin.ext ?_⟩
        have := congrArg (fun z => (e z).val) hm
        simp at this
        simp [← this]
      · exfalso
        have := congrArg (fun z => (e z).val) hm
        simp [he] at this
        have := m.isLt
        omega)

theorem eX_val (a : A) : ((eX e hcc he a : Fin N) : ℕ) = (e (Sum.inl a)).val := rfl

end Num

section Ext
variable {E : Type} [Field E] {N c : ℕ}

def extX (c : ℕ) (y : Sp E N ≃ₗ[E] Sp E N) : Sp E (N + c) ≃ₗ[E] Sp E (N + c) :=
  (LinearEquiv.funCongrLeft E E finSumFinEquiv) ≪≫ₗ (LinearEquiv.sumArrowLequivProdArrow (Fin N) (Fin c) E E) ≪≫ₗ
    (y.prodCongr (LinearEquiv.refl E (Fin c → E))) ≪≫ₗ (LinearEquiv.sumArrowLequivProdArrow (Fin N) (Fin c) E E).symm ≪≫ₗ
    (LinearEquiv.funCongrLeft E E finSumFinEquiv).symm

theorem extX_castAdd (y : Sp E N ≃ₗ[E] Sp E N) (v : Sp E (N + c)) (i : Fin N) :
    extX c y v (Fin.castAdd c i) = y (fun i => v (Fin.castAdd c i)) i := by
  simp [extX, LinearEquiv.funCongrLeft_apply, LinearMap.funLeft, LinearEquiv.sumArrowLequivProdArrow, LinearEquiv.funCongrLeft, Equiv.sumArrowEquivProdArrow]
  rfl

theorem extX_natAdd (y : Sp E N ≃ₗ[E] Sp E N) (v : Sp E (N + c)) (i : Fin c) :
    extX c y v (Fin.natAdd N i) = v (Fin.natAdd N i) := by
  simp [extX, LinearEquiv.funCongrLeft_apply, LinearMap.funLeft, LinearEquiv.sumArrowLequivProdArrow, LinearEquiv.funCongrLeft, Equiv.sumArrowEquivProdArrow]

end Ext

end GlobalTheory.VolBridge
end
end

section

open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.SymBridge

theorem _root_.GlobalTheory.T.residues_of_completionAtPrimeWithUniformizer : ∀ (E k : Type) [Field E] [NumberField E] [StarRing E] [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (P : HeightOneSpectrum (𝓞 E)) (q : ℕ) (ι : E →+* k) (ϖ : kˣ), IsCompl P q ι ϖ → GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.IsUnif ϖ → (∀ a, valuation k (ι a) < 1 ↔ IntAt P (a / (q : E))) ∧ (∀ a, IntAt P a → (valuation k (ι a) < 1 ↔ redP P a = 0)) ∧ (∀ a, IntAt P a → (valuation k (ι a) = 1 ↔ IsUnit (redP P a))) ∧ (q : E) ≠ 0 ∧ ((q : ℕ) : 𝓞 E) ∈ P.asIdeal ∧ ((q : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2 ∧ resCard k = q ∧ ∀ (n : ℕ) (x : k), x ∈ 𝒪[k] → ∃! i : ℕ, i < q ^ n ∧ valuation k (x - (i : k)) ≤ valuation k ((ϖ : k) ^ n) := by
  first | exact @GlobalTheory.SymBridge.ComplRes.residues | exact GlobalTheory.SymBridge.ComplRes.residues | (intros; apply GlobalTheory.SymBridge.ComplRes.residues <;> assumption)
end

section

open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound GlobalTheory.ParHecke GlobalTheory.LowerHecke
open Classical

namespace GlobalTheory.LowerHeckeSupp

theorem lowU_add {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {A D : Type} [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (a b : Matrix D A k) :
    lowU (a + b) = lowU a * lowU b := by
  ext1
  rw [Units.val_mul, val_lowU, val_lowU, val_lowU, fromBlocks_multiply]
  simp [add_comm]

theorem biType_lowU_emb : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (ξ : kˣ →* ℂˣ), IsTame ξ → ¬ IsUnram ξ → ∀ φ : GL (A ⊕ D) k → ℂ, IsBiType ξ φ → ∀ (ν : Matrix D A k) (y : GL D k), φ (lowU ν * emb₂ k (Equiv.refl (A ⊕ D)) (1, y)) = if ∃ ν₁ ν₂ : Matrix D A k, (∀ i a, valuation k (ν₁ i a) < 1) ∧ (∀ i a, valuation k (ν₂ i a) < 1) ∧ ν = ν₁ + y.1 * ν₂ then φ (emb₂ k (Equiv.refl (A ⊕ D)) (1, y)) else 0 := by
  intro k _ _ _ _ A D _ _ _ _ ξ hT hU φ hφ ν y
  split_ifs with h
  · obtain ⟨ν₁, ν₂, h₁, h₂, rfl⟩ := h
    have hd : ∀ μ : Matrix D A k, ((1 : kˣ) : k) = ((lowU μ : GL (A ⊕ D) k) : Matrix (A ⊕ D) (A ⊕ D) k).toBlocks₂₂.det := by
      intro μ; simp [val_lowU]
    rw [lowU_add, mul_assoc, ← emb_mul_lowU]
    rw [(hφ _ (lowU_mem h₁) 1 (hd ν₁) _).1, (hφ _ (lowU_mem h₂) 1 (hd ν₂) _).2]
    simp
  · by_contra hne
    obtain ⟨x, z, j, hj, j', hj', he⟩ := GlobalTheory.ParHeckeSupp.support_levi k A D ξ hT hU φ hφ _ hne
    have hv : (lowU ν * emb₂ k (Equiv.refl (A ⊕ D)) (1, y)).1 = fromBlocks 1 0 ν y.1 := by
      rw [Units.val_mul, val_lowU, val_emb_one, fromBlocks_multiply]; simp
    exact h (GlobalTheory.ParHeckeCap.lowerUni_mem_cap k A D _ ν y hv ⟨x, z, j, hj, j', hj', he⟩)

end GlobalTheory.LowerHeckeSupp
end

section

open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound GlobalTheory.ParHecke

namespace GlobalTheory.RangeKerCount

open GlobalTheory.KerRangeCount Formalism.L2.Col

theorem card_above_range_eq_sum : ∀ (κ : Type) [Field κ] [Finite κ] (U U' : Type) [AddCommGroup U] [Module κ U] [FiniteDimensional κ U] [AddCommGroup U'] [Module κ U'] [FiniteDimensional κ U'] (f : U →ₗ[κ] U') (t e : ℕ), Module.finrank κ U' = Module.finrank κ U + t → e ≤ Module.finrank κ U' → Nat.card {X : Submodule κ U' // LinearMap.range f ≤ X ∧ Module.finrank κ X + e = Module.finrank κ U'} = ∑ n ∈ Finset.range (Module.finrank κ U + 1), (if n ≤ e then Nat.card κ ^ (n * (t - (e - n))) * Formalism.L2.Col.gaussBin (Nat.card κ) t (e - n) else 0) * Nat.card {X : Submodule κ U // X ≤ LinearMap.ker f ∧ Module.finrank κ X = n} := by
  intro κ _ _ U U' _ _ _ _ _ _ f t e hU' he
  classical
  letI : Fintype κ := Fintype.ofFinite κ
  rw [Nat.card_eq_fintype_card (α := κ)]
  have hq0 : Fintype.card κ ≠ 0 := Fintype.card_ne_zero
  have hrk := f.finrank_range_add_finrank_ker
  have hin : ∀ n, Nat.card {X : Submodule κ U // X ≤ LinearMap.ker f ∧ Module.finrank κ X = n} =
      Formalism.L2.Col.gaussBin (Fintype.card κ) (Module.finrank κ (LinearMap.ker f)) n := by
    intro n
    rw [← card_below (LinearMap.ker f) n]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun X => and_comm)
  have hL : Nat.card {X : Submodule κ U' // LinearMap.range f ≤ X ∧ Module.finrank κ X + e = Module.finrank κ U'} =
      Formalism.L2.Col.gaussBin (Fintype.card κ) (Module.finrank κ (LinearMap.ker f) + t) e := by
    by_cases hem : e ≤ Module.finrank κ (LinearMap.ker f) + t
    · rw [gaussBin_symm hq0 (Module.finrank κ (LinearMap.ker f) + t) e
        (Module.finrank κ (LinearMap.ker f) + t - e) (by omega)]
      have h := card_above (k := κ) (LinearMap.range f) (Module.finrank κ (LinearMap.ker f) + t - e)
      rw [show Module.finrank κ U' - Module.finrank κ (LinearMap.range f) =
        Module.finrank κ (LinearMap.ker f) + t by omega] at h
      rw [← h]
      exact Nat.card_congr (Equiv.subtypeEquivRight fun X =>
        ⟨fun h => ⟨by omega, h.1⟩, fun h => ⟨h.2, by omega⟩⟩)
    · have : IsEmpty {X : Submodule κ U' // LinearMap.range f ≤ X ∧ Module.finrank κ X + e = Module.finrank κ U'} :=
        ⟨fun X => by have := Submodule.finrank_mono X.2.1; have := X.2.2; omega⟩
      rw [Nat.card_of_isEmpty, gaussBin_eq_zero _ (by omega)]
  set q := Fintype.card κ
  set m := Module.finrank κ (LinearMap.ker f)
  set g : ℕ → ℕ := fun n => (if n ≤ e then q ^ (n * (t - (e - n))) * Formalism.L2.Col.gaussBin q t (e - n) else 0) *
    Formalism.L2.Col.gaussBin q m n with hg
  have hR : ∑ n ∈ Finset.range (Module.finrank κ U + 1), (if n ≤ e then q ^ (n * (t - (e - n))) *
      Formalism.L2.Col.gaussBin q t (e - n) else 0) *
      Nat.card {X : Submodule κ U // X ≤ LinearMap.ker f ∧ Module.finrank κ X = n} =
      ∑ n ∈ Finset.range (Module.finrank κ U + 1), g n :=
    Finset.sum_congr rfl fun n _ => by rw [hin]
  have h2 : ∑ n ∈ Finset.range (e + 1), g n = ∑ n ∈ Finset.range (e + Module.finrank κ U + 1), g n :=
    Finset.sum_subset (Finset.range_mono (by omega)) fun n _ hn => by
      rw [Finset.mem_range] at hn
      simp only [hg]
      rw [if_neg (by omega), zero_mul]
  have h3 : ∑ n ∈ Finset.range (Module.finrank κ U + 1), g n =
      ∑ n ∈ Finset.range (e + Module.finrank κ U + 1), g n :=
    Finset.sum_subset (Finset.range_mono (by omega)) fun n _ hn => by
      rw [Finset.mem_range] at hn
      simp only [hg]
      rw [gaussBin_eq_zero q (show m < n by omega), mul_zero]
  rw [hL, hR, h3, ← h2, gaussBin_add hq0 m t e, ← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [Finset.mem_range] at hn
  simp only [hg]
  rw [if_pos (by omega), show e + 1 - 1 - n = e - n by omega, show e - (e - n) = n by omega]
  ring

end GlobalTheory.RangeKerCount
end
