module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle007
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle080
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle471
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle009
public import Formalism.SharpRestriction.LevelLetterCocycles.IdempotentChoiceDepthZero
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle267
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle336
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IndexDvdClassNumber
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle380
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle257
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle317
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle342
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle318
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle266
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LengthQuotEqZeroIff
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle268
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle010
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle290
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle340
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle531
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle487
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HarishChandraSeriesWeightSquarefreeLabelGelfandG
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle020
public import Formalism.SharpRestriction.LevelLetterCocycles.ArcLiftingSetup
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle532
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle021
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle007
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle534
public import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle535
public import Formalism.SatakeDualWeyl.StatementG
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle533
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Rat
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
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle011
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle004
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BoundAtTwoThreeFamily
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.CoeSelfDualLatticeInFrameCoordinatesEq
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.PermutesRefl
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.XiValIffXiAt

@[expose] public section

section

open Formalism.Per GlobalTheory.PSer
open scoped Formalism.Per

namespace GlobalTheory.PSerExist

theorem norm_l_lt_one (l : ℕ) [Fact l.Prime] : ‖(l : ℂ_[l])‖ < 1 := by
  have h := PadicComplex.norm_extends' l (l : ℚ_[l])
  have h2 : ‖(l : ℚ_[l])‖ < 1 := Padic.norm_p_lt_one
  have h3 : ((l : ℚ_[l]) : ℂ_[l]) = (l : ℂ_[l]) := by push_cast; rfl
  rw [h3] at h
  rw [h]; exact h2

theorem exists_zeros (l : ℕ) [Fact l.Prime] (h : ℕ) (μ : Fin h → ℂ_[l]) (hh : 2 ≤ h) (hμ : μ ≠ 0) :
    ∃ y : Fin h → ℕ → Fl l, (∀ a k, ‖sh (y a k)‖ ≤ ‖(l : ℂ_[l])‖) ∧
      (∀ a, ∑ i : Fin h, μ i * abelian₂ h i (y a) = 0) ∧
      ∀ c : Fin h → ℚ_[l], (∀ j : ℕ, j < 2 → ∑ a, algebraMap ℚ_[l] ℂ_[l] (c a) * abelian₂ h j (y a) = 0) →
        c = 0 := by
  have h1 : 1 ≤ h := le_trans (by norm_num) hh
  obtain ⟨τ, hsurj, x, hxS, hxη, hxind⟩ := GlobalTheory.T.untiltFrobeniusSeries_onto_and_independent_zeros l h μ h1 hμ
  let η : Fl l → Unit → ℂ_[l] := fun y _ => ∑ i : Fin h, μ i * lam h i y
  let S : Set (Fl l) := {y | ‖sh y‖ ≤ ‖(l : ℂ_[l])‖}
  have hlift := GlobalTheory.T.lift_hasSum_zero_of_surjective_mod_prime l (Fl l) Unit η (fun _ => τ) S
    (fun t ht => by
      obtain ⟨y, hy, hyt⟩ := hsurj (t ()) (ht ())
      exact ⟨y, hy, fun i => by cases i; exact hyt⟩)
  have hy : ∀ a : Fin h, ∃ z : ℕ → Fl l, z 0 = x a ∧ (∀ k, z k ∈ S) ∧
      ∀ i, HasSum (fun k : ℕ => (l : ℂ_[l]) ^ k * η (z k) i) 0 :=
    fun a => hlift (x a) (hxS a) (fun _ => hxη a)
  choose y hy0 hyS hysum using hy
  have hr : ‖(l : ℂ_[l])‖ < 1 := norm_l_lt_one l
  have hyS' : ∀ a k, ‖sh (y a k)‖ ≤ ‖(l : ℂ_[l])‖ := fun a k => hyS a k
  refine ⟨y, hyS', ?_, ?_⟩
  · intro a
    have hs : ∀ i : Fin h, HasSum (fun k : ℕ => μ i * ((l : ℂ_[l]) ^ k * lam h i (y a k)))
        (μ i * abelian₂ h i (y a)) := fun i =>
      ((GlobalTheory.T.untiltFrobeniusDoubleSeries_hasSum_and_norm_bounds l h i ‖(l : ℂ_[l])‖ (y a) h1 hr (hyS' a)).1).mul_left (μ i)
    have hsum := hasSum_sum (s := Finset.univ) (fun i _ => hs i)
    have hsum' : HasSum (fun k : ℕ => (l : ℂ_[l]) ^ k * η (y a k) ())
        (∑ i : Fin h, μ i * abelian₂ h i (y a)) := by
      convert hsum using 1
      funext k
      dsimp [η]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => by ring
    exact hsum'.unique (hysum a ())
  · refine GlobalTheory.T.untiltFrobeniusSeries_linearIndependent_of_firstTerms l h h ‖(l : ℂ_[l])‖ y hh (norm_nonneg _) hr hyS' ?_
    intro n hn a
    simp only [hy0] at hn
    exact hxind n hn a

end GlobalTheory.PSerExist
end

section

open GlobalTheory.TypeLeaf Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.ArithmeticCylinders Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain

theorem _root_.GlobalTheory.T.exists_reduction_teichmullerEmbedding_at_localisation : ∀ (D : D7) (i : D.nd.Loc) (k : Fin 2), D.nd.l i ≠ D.host.g k → ∃ ι : Fb (D.host.g k) (D.host.g_prime k) →* Formalism.CyclotomicNorms.Fbar (D.nd.l i), InjPrimeTo (D.nd.l i) ι ∧ RedVia D i k ι := by
  first | exact @GlobalTheory.TypeLeaf.exists_redVia | exact GlobalTheory.TypeLeaf.exists_redVia | (intros; apply GlobalTheory.TypeLeaf.exists_redVia <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pass GlobalTheory.Cut Module

noncomputable section

namespace GlobalTheory.CutCoreUnit

variable {D : D7} (i : D.nd.Loc)

theorem ccOff_univ (π : D.nd.X i) : ccOff i Set.univ π = ccAt (D.nd.T i) (D.nd.Z i) π := by
  rw [ccOff, ccAt, Ideal.map]
  congr 1
  ext a
  constructor
  · rintro ⟨f, hf, h0, rfl⟩
    refine ⟨⟨f, hf⟩, ?_, rfl⟩
    change (⟨f, hf⟩ : D.nd.T i) ∈ RingHom.ker _
    rw [RingHom.mem_ker]
    funext y
    exact h0 y.1 trivial y.2
  · rintro ⟨f, hf, rfl⟩
    refine ⟨f.1, f.2, fun x _ hx => ?_, rfl⟩
    change f ∈ RingHom.ker _ at hf
    rw [RingHom.mem_ker] at hf
    exact congrFun hf ⟨x, hx⟩


set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 4000000 in
theorem main : GlobalTheory.Published.GlobalArtinReciprocity → ∀ (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (S : IdempotentChoiceData D.nd i), GoodR D.nd i r → IdempotentChoiceDepthZero.IsOrthogonalIdempotentDecomposition D.nd r ρ π S → π ∈ D.nd.Z i → NoChiOff i r Set.univ → UnrOut i r Set.univ → (∀ v ∈ D.nd.S i, (QuadAt i r Set.univ v ∧ IsUnit (D.nd.zeta i v - 1)) ∨ PolyAt i r Set.univ π v) → (∀ v ∈ D.nd.Q i, QuadAt i r Set.univ v ∧ D.nd.zeta i v ≠ 1) → (∀ w (hw : w ∈ placesOver D.host.E (D.nd.l i)), (LocBound i w hw r Set.univ (WpO D.nd i ρ π) 0 ∧ (∀ c ∈ Finset.Icc 2 D.R.t, ∀ z ∈ cutCoc i w hw r Set.univ (chiRatO D.nd i c), z ∈ BD (Br.locLat D.nbr i w hw (chiRatO D.nd i c))) ∧ ∀ z ∈ cutCoc i w hw r Set.univ (chiRatO D.nd i 1), z ∈ Z1urD (Br.locLat D.nbr i w hw (chiRatO D.nd i 1)) (Br.inert D.nbr i w hw))) → Br.sFin D.loc D.nbr i ρ π → (∀ e ∈ Finset.Ioo 0 D.R.t, Formalism.GaloisCohomology.shaLen (D.nd.ldat (D.nd.l i)) (e : ℤ) < ⊤) → D.nd.vcc i π ≤ Br.sPi D.loc D.nbr i ρ π + (∑ e ∈ Finset.Ioo 0 D.R.t, (D.what₂.shaLen (D.nd.l i) e : ℚ)) + (padicValNat (D.nd.l i) (hE D.host) : ℚ) + (D.R.t : ℚ) * ∑ q ∈ D.nd.Q i, lenUnit (O := D.nd.O i) (D.nd.l i) (D.nd.O i ⧸ Ideal.span {D.nd.zeta i q - 1}) := by
  intro hA D i r ρ π S hr hS hZ hN hU hSv hQ hl hsel hsha
  classical
  have hπ : π ∈ (Set.univ : Set (D.nd.X i)) := trivial
  obtain ⟨L, hL⟩ := CutCore.exists_length_quot (GlobalTheory.LenUnitPow.natCast_ne_zero (D.nd.l i) (O := D.nd.O i))
  have hL0 : L ≠ 0 := by
    rintro rfl
    exact GlobalTheory.LenUnitPow.natCast_not_isUnit (D.nd.l i) (O := D.nd.O i) (CutCore.length_quot_eq_zero_iff.mp hL)
  have hd : lenQ i (del51 D.nd S S.π') = 0 :=
    CutCore.length_quot_eq_zero_iff.mpr hS.2.2.2.2.2.2.2.2.2.2.1.2.2.2
  obtain ⟨s, hs⟩ := ENat.ne_top_iff_exists.mp (ne_of_lt hsel)

  have hρ : Module.length (D.nd.O i) ↥(cocRho i r S Set.univ) ≤ (s : ℕ∞) := by
    obtain ⟨C, hC, hfin, hlen⟩ := GlobalTheory.T.length_global_cocycles_le_sum_places_over D i r Set.univ _ (WpO D.nd i ρ π) (cocRho i r S Set.univ) 0
      (fun w hw => ⟨(hl w hw).1, (GlobalTheory.T.localCocycles_aboveEll_inCut_unitDelta D i r ρ π Set.univ S hr hS hπ w hw).1⟩)
    rw [mul_zero, Nat.cast_zero, zero_mul, zero_add] at hlen
    refine hlen.trans ((GlobalTheory.T.length_cocycles_le_coboundaries_add_selmer D i ρ π C (hC.trans (GlobalTheory.T.finiteQuotientCocycleSpans_le_continuousCocycles D i r ρ π Set.univ S hr hS hπ).1) hfin ?_).trans ?_)
    · intro v h1 h2 h3
      exact CutCore.resIne_eq_bot_of_le i hC
        (GlobalTheory.Proof.LocalGlobalSelmer.main D i r Set.univ S _ S.ψρ (CutCore.inR'_one i r S) hU v h1 h2 h3)
    · have hc := (CutCore.lenCob_mono i _ hC).trans (GlobalTheory.T.length_cutCoboundaryModule_le_unitDelta D i r ρ π Set.univ S hr hS hπ).1
      rw [hd, mul_zero, nonpos_iff_eq_zero] at hc
      rw [hc, zero_add, ← hs]

  have hχ : ∀ c : Fin D.R.t, Module.length (D.nd.O i) ↥(cocChi i r S Set.univ c) ≤
      lenQ i ((D.nd.l i : ℕ) : D.nd.O i) * (if (c : ℕ) = 0 then ((padicValNat (D.nd.l i) (hE D.host) : ℕ) : ℕ∞)
          else Formalism.GaloisCohomology.shaLen (D.nd.ldat (D.nd.l i)) ((c : ℕ) : ℤ)) +
        ∑ q ∈ D.nd.Q i, lenQ i (D.nd.zeta i q - 1) := by
    intro c
    obtain ⟨C', hC', hq, hlen'⟩ := GlobalTheory.Cut.Peel.main D i 1 (cocChi i r S Set.univ c) (D.nd.Q i)
    have hZ1 := hC'.trans ((GlobalTheory.T.finiteQuotientCocycleSpans_le_continuousCocycles D i r ρ π Set.univ S hr hS hπ).2 c)
    have hunr : ∀ v, v ∉ placesOver D.host.E (D.nd.l i) → resIne i C' v = ⊥ := by
      intro v h1
      by_cases h3 : v ∈ D.nd.Q i
      · exact hq v h3
      refine CutCore.resIne_eq_bot_of_le i hC' ?_
      by_cases h2 : v ∈ D.nd.S i
      · rcases hSv v h2 with ⟨hqd, hu⟩ | hp
        · have h := GlobalTheory.T.inertiaCocycleBlock_length_le_of_quadraticRelation D i r ρ π Set.univ S hr hS hπ v (Or.inl h2) hqd c
          rw [lenQ, CutCore.length_quot_eq_zero_iff.mpr hu, nonpos_iff_eq_zero, Module.length_eq_zero_iff] at h
          exact Submodule.subsingleton_iff_eq_bot.mp h
        · exact GlobalTheory.T.inertia_restriction_polynomial_condition_second_form D i r ρ π Set.univ S hr hS hπ v h2 hp c
      · exact GlobalTheory.Proof.LocalGlobalSelmer.main D i r Set.univ S _ _ (CutCore.inR'_one i r S) hU v h1 h2 h3
    refine hlen'.trans (add_le_add ?_ (Finset.sum_le_sum fun q hq' =>
      GlobalTheory.T.inertiaCocycleBlock_length_le_of_quadraticRelation D i r ρ π Set.univ S hr hS hπ q (Or.inr hq') (hQ q hq').1 c))
    by_cases hc : (c : ℕ) = 0
    · rw [if_pos hc]
      have e : (c : ℕ) + 1 = 1 := by omega
      rw [e] at hZ1
      have hloc : ∀ w (hw : w ∈ placesOver D.host.E (D.nd.l i)), ∀ f ∈ C',
          InCut i r Set.univ (chiRatO D.nd i 1) w hw f := by
        intro w hw f hf
        have h := (GlobalTheory.T.localCocycles_aboveEll_inCut_unitDelta D i r ρ π Set.univ S hr hS hπ w hw).2 c f (hC' hf)
        rwa [e] at h
      refine GlobalTheory.UnramHom.length_le_classNumber hA D i C' hZ1 fun v => ?_
      by_cases hv : v ∈ placesOver D.host.E (D.nd.l i)
      · exact GlobalTheory.CutTrivIne.main D i C' v hv fun f hf =>
          (Submodule.span_le.mpr fun z hz => (hl v hv).2.2 z hz) (hloc v hv f hf)
      · exact hunr v hv
    · rw [if_neg hc]
      have h2 : 2 ≤ (c : ℕ) + 1 := by omega
      have ht : (c : ℕ) + 1 ≤ D.R.t := c.2
      have h := GlobalTheory.T.length_cyclotomic_block_cocycles_le_sha D i ((c : ℕ) + 1) C' hZ1 h2 ht
        (fun f hf w hw => (Submodule.span_le.mpr fun z hz =>
          (hl w hw).2.1 _ (Finset.mem_Icc.mpr ⟨h2, ht⟩) z hz)
            ((GlobalTheory.T.localCocycles_aboveEll_inCut_unitDelta D i r ρ π Set.univ S hr hS hπ w hw).2 c f (hC' hf))) hunr
      rw [Nat.add_sub_cancel] at h
      have hc0 := (CutCore.lenCob_mono i _ hC').trans ((GlobalTheory.T.length_cutCoboundaryModule_le_unitDelta D i r ρ π Set.univ S hr hS hπ).2 c)
      rw [hd, mul_zero, nonpos_iff_eq_zero] at hc0
      rw [hc0, zero_add] at h
      exact h

  have hz : ∀ q ∈ D.nd.Q i, lenQ i (D.nd.zeta i q - 1) = ((lenQ i (D.nd.zeta i q - 1)).toNat : ℕ∞) := by
    intro q hq
    obtain ⟨n, hn⟩ := CutCore.exists_length_quot (sub_ne_zero.mpr (hQ q hq).2)
    rw [lenQ, hn, ENat.toNat_coe]
  set z : HeightOneSpectrum (𝓞 D.host.E) → ℕ := fun q => (lenQ i (D.nd.zeta i q - 1)).toNat with hzdef
  set g : ℕ → ℕ := fun e => (Formalism.GaloisCohomology.shaLen (D.nd.ldat (D.nd.l i)) (e : ℤ)).toNat with hg
  have hg' : ∀ e ∈ Finset.Ioo 0 D.R.t, Formalism.GaloisCohomology.shaLen (D.nd.ldat (D.nd.l i)) (e : ℤ) = (g e : ℕ∞) :=
    fun e he => (ENat.coe_toNat (hsha e he).ne).symm
  have ht : 0 < D.R.t := D.R.t_odd.pos
  set h := padicValNat (D.nd.l i) (hE D.host) with hh
  have hχ' : ∀ c : Fin D.R.t, Module.length (D.nd.O i) ↥(cocChi i r S Set.univ c) ≤
      ((L * (if (c : ℕ) = 0 then h else g c) + ∑ q ∈ D.nd.Q i, z q : ℕ) : ℕ∞) := by
    intro c
    refine (hχ c).trans (le_of_eq ?_)
    rw [Finset.sum_congr rfl hz, lenQ, hL]
    by_cases hc : (c : ℕ) = 0
    · rw [if_pos hc, if_pos hc]
      push_cast
      rfl
    · rw [if_neg hc, if_neg hc, hg' c (Finset.mem_Ioo.mpr ⟨Nat.pos_of_ne_zero hc, c.2⟩)]
      push_cast
      rfl
  have htot := (GlobalTheory.T.length_heckeValueIdeal_le_determinant_bound D i r ρ π Set.univ S hr hS hπ hZ hN).trans
    (add_le_add hρ (Finset.sum_le_sum fun c _ => hχ' c))
  rw [← Nat.cast_sum, ← Nat.cast_add] at htot
  have hnat := ENat.toNat_le_of_le_coe htot
  have hsum : ∑ c : Fin D.R.t, (L * (if (c : ℕ) = 0 then h else g c) + ∑ q ∈ D.nd.Q i, z q) =
      L * (h + ∑ e ∈ Finset.Ioo 0 D.R.t, g e) + D.R.t * ∑ q ∈ D.nd.Q i, z q := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, CutCore.sum_fin_ite ht, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, smul_eq_mul]
  rw [hsum] at hnat
  have hsp : Br.sPi D.loc D.nbr i ρ π = (s : ℚ) / L := by
    rw [Br.sPi, lenUnit, hL, ← hs, ENat.toNat_coe, ENat.toNat_coe]
  have hsh : ∑ e ∈ Finset.Ioo 0 D.R.t, (D.what₂.shaLen (D.nd.l i) e : ℚ) =
      ((∑ e ∈ Finset.Ioo 0 D.R.t, g e : ℕ) : ℚ) := by
    rw [Nat.cast_sum]
    exact Finset.sum_congr rfl fun e he =>
      D.nd.sha_eq _ e (Finset.mem_Ioo.mp he).1 (Finset.mem_Ioo.mp he).2 _ (hg' e he)
  have hzq : ∑ q ∈ D.nd.Q i,
      lenUnit (O := D.nd.O i) (D.nd.l i) (D.nd.O i ⧸ Ideal.span {D.nd.zeta i q - 1}) =
        ((∑ q ∈ D.nd.Q i, z q : ℕ) : ℚ) / L := by
    rw [Nat.cast_sum, Finset.sum_div]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [lenUnit, hL, ENat.toNat_coe]
    rfl
  show lenUnit (O := D.nd.O i) (D.nd.l i) (D.nd.O i ⧸ ccAt (D.nd.T i) (D.nd.Z i) π) ≤ _
  rw [← ccOff_univ, hsp, hsh, hzq, lenUnit, hL, ENat.toNat_coe]
  have hLq : (0 : ℚ) < L := by exact_mod_cast Nat.pos_of_ne_zero hL0
  generalize (Module.length (D.nd.O i) (D.nd.O i ⧸ ccOff i Set.univ π)).toNat = a at hnat
  generalize ∑ e ∈ Finset.Ioo 0 D.R.t, g e = G at hnat ⊢
  generalize ∑ q ∈ D.nd.Q i, z q = Z at hnat ⊢
  have hq : (a : ℚ) ≤ ((s + (L * (h + G) + D.R.t * Z) : ℕ) : ℚ) := Nat.cast_le.mpr hnat
  push_cast at hq
  rw [div_le_iff₀ hLq]
  have e : ((s : ℚ) / L + G + (h : ℚ) + (D.R.t : ℚ) * ((Z : ℚ) / L)) * L =
      s + G * L + h * L + D.R.t * Z := by
    field_simp
  rw [e]
  nlinarith [hq]

end GlobalTheory.CutCoreUnit
end
end

section

open GlobalTheory.GLq Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical

namespace GlobalTheory.GLq

theorem finite_natDegree_eq {R : Type} [Semiring R] [Finite R] (n : ℕ) :
    {f : R[X] | f.natDegree = n}.Finite := by
  refine Set.Finite.of_finite_image (f := fun p : R[X] => fun i : Fin (n + 1) => p.coeff i)
    (Set.toFinite _) ?_
  intro p hp q hq hpq
  have hp' : p.natDegree = n := hp
  have hq' : q.natDegree = n := hq
  ext i
  by_cases hi : i ≤ n
  · exact congrFun hpq ⟨i, Nat.lt_succ_of_le hi⟩
  · rw [coeff_eq_zero_of_natDegree_lt (by omega), coeff_eq_zero_of_natDegree_lt (by omega)]

theorem eSerC_eq_sum {g : ℕ} [Fact g.Prime] (L : LabelDatum g) (n : ℕ)
    (hfin : {χ : Gn g n → ℂ | IsIrr χ}.Finite) (f : (ZMod g)[X]) :
    eSerC L n f = ∑ χ ∈ hfin.toFinset.filter (fun χ => HasLabel L χ f), zOf χ := by
  have hset : {χ : Gn g n → ℂ | IsIrr χ ∧ HasLabel L χ f} =
      ↑(hfin.toFinset.filter (fun χ => HasLabel L χ f)) := by
    ext χ
    simp [Set.Finite.mem_toFinset]
  rw [eSerC, hset, finsum_mem_coe_finset]

theorem eSerC_laws : ∀ (g : ℕ) [Fact g.Prime] (L : LabelDatum g), 5 ≤ g → Green → ∀ n : ℕ, (∀ f, eSerC L n f * eSerC L n f = eSerC L n f) ∧ (∀ f a, eSerC L n f * a = a * eSerC L n f) ∧ (∀ f f', f ≠ f' → eSerC L n f * eSerC L n f' = 0) ∧ (∀ f, ¬ (f.Monic ∧ f.natDegree = n ∧ f.coeff 0 ≠ 0) → eSerC L n f = 0) ∧ ∃ S : Finset (ZMod g)[X], (∀ f, f ∈ S ↔ f.Monic ∧ f.natDegree = n ∧ f.coeff 0 ≠ 0) ∧ ∑ f ∈ S, eSerC L n f = 1 := by
  intro g _ L hg hG n
  obtain ⟨hfin, hsum⟩ := GlobalTheory.T.finite_irrCharacters_and_finsum_centralIdempotents_eq_one (Gn g n)
  obtain ⟨huniq, hprops, -⟩ := GlobalTheory.T.harishChandraSeriesLabel_exists_unique_GLn g L hg hG n
  have horth := GlobalTheory.T.centralIdempotentOfIrrCharacter_orthogonal_central (Gn g n)
  have he : ∀ f, eSerC L n f = ∑ χ ∈ hfin.toFinset.filter (fun χ => HasLabel L χ f), zOf χ :=
    fun f => eSerC_eq_sum L n hfin f
  have hmem : ∀ f χ, χ ∈ hfin.toFinset.filter (fun χ => HasLabel L χ f) ↔ IsIrr χ ∧ HasLabel L χ f := by
    intro f χ
    simp [Set.Finite.mem_toFinset]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro f
    rw [he f, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun χ hχ => ?_
    have hχi := ((hmem f χ).1 hχ).1
    rw [Finset.sum_congr rfl fun χ' hχ' => (horth χ χ' hχi ((hmem f χ').1 hχ').1).1,
      Finset.sum_ite_eq, if_pos hχ]
  · intro f a
    rw [he f, Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun χ hχ =>
      (horth χ χ ((hmem f χ).1 hχ).1 ((hmem f χ).1 hχ).1).2.1 a
  · intro f f' hff'
    rw [he f, he f', Finset.sum_mul_sum]
    refine Finset.sum_eq_zero fun χ hχ => Finset.sum_eq_zero fun χ' hχ' => ?_
    obtain ⟨hi, hl⟩ := (hmem f χ).1 hχ
    obtain ⟨hi', hl'⟩ := (hmem f' χ').1 hχ'
    rw [(horth χ χ' hi hi').1, if_neg]
    rintro rfl
    exact hff' ((huniq χ hi).unique hl hl')
  · intro f hf
    rw [he f]
    exact Finset.sum_eq_zero fun χ hχ => absurd (hprops χ f ((hmem f χ).1 hχ).2) hf
  · have hS := finite_natDegree_eq (R := ZMod g) n
    have hSmem : ∀ f, f ∈ hS.toFinset.filter (fun f => f.Monic ∧ f.coeff 0 ≠ 0) ↔
        f.Monic ∧ f.natDegree = n ∧ f.coeff 0 ≠ 0 := by
      intro f
      simp only [Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
      tauto
    refine ⟨_, hSmem, ?_⟩
    calc ∑ f ∈ hS.toFinset.filter (fun f => f.Monic ∧ f.coeff 0 ≠ 0), eSerC L n f
        = ∑ f ∈ hS.toFinset.filter (fun f => f.Monic ∧ f.coeff 0 ≠ 0),
            ∑ χ ∈ hfin.toFinset, if HasLabel L χ f then zOf χ else 0 := by
          refine Finset.sum_congr rfl fun f _ => ?_
          rw [he f, Finset.sum_filter]
      _ = ∑ χ ∈ hfin.toFinset, ∑ f ∈ hS.toFinset.filter (fun f => f.Monic ∧ f.coeff 0 ≠ 0),
            if HasLabel L χ f then zOf χ else 0 := Finset.sum_comm
      _ = ∑ χ ∈ hfin.toFinset, zOf χ := by
          refine Finset.sum_congr rfl fun χ hχ => ?_
          have hi : IsIrr χ := hfin.mem_toFinset.1 hχ
          obtain ⟨f0, hf0, hu⟩ := huniq χ hi
          rw [Finset.sum_eq_single f0]
          · rw [if_pos hf0]
          · intro b _ hb
            rw [if_neg]
            exact fun h => hb (hu b h)
          · intro h0
            exact absurd ((hSmem f0).2 (hprops χ f0 hf0)) h0
      _ = 1 := by
          rw [← finsum_mem_coe_finset, Set.Finite.coe_toFinset]
          exact hsum

end GlobalTheory.GLq
end

section

open GlobalTheory.GLq GlobalTheory.Published Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical

theorem _root_.GlobalTheory.T.card_cuspidal_multisets_total_degree_le : ∀ (g : ℕ) [Fact g.Prime] (n : ℕ), 0 < n → ∀ S : Finset (Multiset (Pc g)), (∀ M ∈ S, (M.map fun p => p.1).sum = n ∧ ∀ p ∈ M, IsCusp p.2) → S.card ≤ g ^ n - g ^ (n - 1) := by
  first | exact @GlobalTheory.GLq.CuspMultisetCount.card_le | exact GlobalTheory.GLq.CuspMultisetCount.card_le | (intros; apply GlobalTheory.GLq.CuspMultisetCount.card_le <;> assumption)
end

section

open GlobalTheory.GLq Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical

theorem _root_.GlobalTheory.T.harishChandraSeriesWeight_squarefree_label_gelfandGraev : ∀ (g : ℕ) [Fact g.Prime] (L : LabelDatum g), 5 ≤ g → Green → ∀ (ψ : AddChar (ZMod g) ℂ), ψ ≠ 1 → ∀ (n : ℕ) (f : (ZMod g)[X]), f.Monic → f.natDegree = n → f.coeff 0 ≠ 0 → Squarefree f → wtC L (eU g n ψ) f = 1 / ((UniqueFactorizationMonoid.normalizedFactors f).map (fun P => (g : ℝ) ^ P.natDegree - 1)).prod := by
  first | exact @GlobalTheory.Adopt.harishChandraSeriesWeight_squarefree_label_gelfandGraev | exact GlobalTheory.Adopt.harishChandraSeriesWeight_squarefree_label_gelfandGraev | (intros; apply GlobalTheory.Adopt.harishChandraSeriesWeight_squarefree_label_gelfandGraev <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

theorem _root_.GlobalTheory.T.rowsCD_rowCondition_localBounds : ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (C₂ : ℝ) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (dc : TruncatedSeriesCountingIdentities.Decl D i), ArcLiftingSetup.aux₃ D HW F 320 → RamifiedCoefficientChains.aux₃ D HW F 25 → LiftingTheory.aux₃ D HW F 10 23 32 32 → EmbeddingTypeJumps.ParametersPolynomiallyBounded L → 11 ≤ D.nd.l i → π ∈ D.nd.Zgood i → LocalRepresentationCongruenceCondition L HW i r ρ π → TruncatedSeriesCountingIdentities.LengthBoundAtPlaces i r ρ π dc (lenRowCD L (fun lam => bandOf L HW 320 i r ρ lam) (rowC C₂).K₁ (rowC C₂).K₂ (rowC C₂).K₃ (D.nd.l i)) := by
  first | exact @GlobalTheory.NLink.lengthBoundAtPlaces_of_jointCond | exact GlobalTheory.NLink.lengthBoundAtPlaces_of_jointCond | (intros; apply GlobalTheory.NLink.lengthBoundAtPlaces_of_jointCond <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

theorem _root_.GlobalTheory.T.weilDatumCharacters_unramified_offLevels : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Laws R F → ∀ (i : Fin D.R.m) (t : T) (v : HeightOneSpectrum (𝓞 D.host.F)) (f : AE D), IsFinIdem D v f → (∀ P, P ∈ R.Pg ∨ P ∈ R.Q t → ∀ e f', IsPrimeIdem P e f' → f' ≠ f) → ∀ w : HeightOneSpectrum (𝓞 D.host.E), w.under (𝓞 D.host.F) = v → GlobalTheory.LFun.UnrAt (Formalism.IndefR.Lift.chrTh (R.toLevCh.mu t) R.eta ((i : ℕ) + 1)).1 w ∧ GlobalTheory.LFun.UnrAt (Formalism.IndefR.Lift.chrTh (R.toLevCh.mu t) R.eta ((i : ℕ) + 1)).2 w := by
  first | exact @GlobalTheory.GoodModUnr.chrTh_unrAt | exact GlobalTheory.GoodModUnr.chrTh_unrAt | (intros; apply GlobalTheory.GoodModUnr.chrTh_unrAt <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
open Classical

theorem _root_.GlobalTheory.T.fixedVectorCoefficient_left_invariant_levelGroup : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Laws R F → ∀ i t, LevFix R i t → ∀ (μ : Measure (WO (Vc D i) (Wc D i))) (𝓕 : Set (WO (Vc D i) (Wc D i))), IsCovolOne (ratL (Wc D i) (Vc D i)) μ 𝓕 → ∀ k ∈ levW R i, ∀ g, coef R i t μ 𝓕 (k * g) = coef R i t μ 𝓕 g := by
  first | exact @GlobalTheory.RawLift.CoefLeft.coef_lev_mul | exact GlobalTheory.RawLift.CoefLeft.coef_lev_mul | (intros; apply GlobalTheory.RawLift.CoefLeft.coef_lev_mul <;> assumption)
end

section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.Member GlobalTheory.CompRat GlobalTheory.FinalJoin
open scoped TensorProduct Matrix

theorem _root_.GlobalTheory.T.cover_component_eq_implies_base_component_eq : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j, Formalism.L2.Pj.InR D j → ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ → ∀ C : Cover T j σ, C.IsUnif → ∀ h h' : GA D (T.V j σ), (C.dict₂ h).1 = (C.dict₂ h').1 → (T.dict j σ h).1 = (T.dict j σ h').1 := by
  first | exact @GlobalTheory.CoverRead.CompIndep.comp_eq_of_cover | exact GlobalTheory.CoverRead.CompIndep.comp_eq_of_cover | (intros; apply GlobalTheory.CoverRead.CompIndep.comp_eq_of_cover <;> assumption)
end

section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.Member GlobalTheory.CompRat GlobalTheory.FinalJoin
open scoped TensorProduct Matrix

theorem _root_.GlobalTheory.T.base_cover_frames_differ_by_rational_isometry : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j, Formalism.L2.Pj.InR D j → ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ → ∀ C : Cover T j σ, C.IsUnif → ∀ h : GA D (T.V j σ), ∃ γ : GL (Fin D.R.r) D.host.E, (((T.U j σ).X (T.dict j σ h).1).Λ : Set (Fin D.R.r → D.host.E)) = (γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec '' ((C.U₂.X (C.dict₂ h).1).Λ : Set _) ∧ (∀ v w, herm ((T.U j σ).X (T.dict j σ h).1).Gm ((γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec v) ((γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec w) = herm (C.U₂.X (C.dict₂ h).1).Gm v w) ∧ (∀ (τ : D.host.E →+* ℂ) (h₂ : τ ∈ (C.U₂.X (C.dict₂ h).1).Ψ) (h₁ : τ ∈ ((T.U j σ).X (T.dict j σ h).1).Ψ), mat (T.dict j σ h).2 ⟨τ, h₁⟩ = (γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).map τ * mat (C.dict₂ h).2 ⟨τ, h₂⟩) := by
  first | exact @GlobalTheory.CoverFrameMove.frames_differ | exact GlobalTheory.CoverFrameMove.frames_differ | (intros; apply GlobalTheory.CoverFrameMove.frames_differ <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

theorem _root_.GlobalTheory.T.finite_place_split_idempotent_or_inert : ∀ (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) (f : Formalism.L2.Theta.AE D), IsFinIdem D v f → (∃ e, Formalism.L2.Theta.IsSplitIdem D e ∧ e + Formalism.L2.Theta.cA D e = f) ∨ (∃ w : HeightOneSpectrum (𝓞 D.host.E), Formalism.UG.IsInertAt D.host.F D.host.E v w) := by
  first | exact @GlobalTheory.PlaceDichotomy.split_or_inert_idem | exact GlobalTheory.PlaceDichotomy.split_or_inert_idem | (intros; apply GlobalTheory.PlaceDichotomy.split_or_inert_idem <;> assumption)
end
