module

public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.UnipotentCharacterArgumentMulStabilizer
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemZmuOfPowPred
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.RedPEqZeroOfDiv
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnfoldingIsGoodCyclotomicInvariantReferenceLatti
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle286
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle025
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1766
public import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1752
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle048
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.HolomorphicHomDetermined
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FrameUniformEmbeddingSecond
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormDwLeSobNorm
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle307
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle271
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowDict
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle180
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.NotDvdCardOfInjective
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle030
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.Bundle002
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ConcreteLevelAdelicSubset
import Formalism.LocalToGlobal.IndefiniteReal.Bundle017
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowsJoinPinned

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.Col Formalism.L2.DIV GlobalTheory.QNormal GlobalTheory.Mem.Col2.IdxEx

noncomputable section

namespace GlobalTheory.Mem.Col2.BddG

open GlobalTheory.LastSteps GlobalTheory.ColPeriod

theorem homBdd_of_good {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {P : HeightOneSpectrum (𝓞 E)}
    {n' c' n c m : ℕ} (hc' : c' ≤ m) (hc : c + 1 ≤ m) {Φ : HomE E (n' + c') (n + c) → K}
    (h : Good P (homS (LocE.lamY P (qOf P) n' c' fun i => i + 1) (LocE.lamY P (qOf P) n c fun i => i + 1)) Φ) :
    HomBdd P m Φ := by
  have hq : (qOf P : E) ≠ 0 := GlobalTheory.TopStep.qOf_ne_zero
  refine ⟨fun x hx => (intHom_iff _).2 fun s l => ?_, fun x y hy => ?_⟩
  · have h1 := mem_homS_sclLat.1 (h.1 x hx) l s
    have hs := s.2
    have e : 0 ≤ (m : ℤ) - (LocE.scE n' (fun i => i + 1) s.1 - LocE.scE n (fun i => i + 1) l.1) := by
      unfold LocE.scE
      dsimp only
      split_ifs <;> omega
    convert h1.mul (intAt_zpow e) using 1
    rw [mul_assoc, ← zpow_add₀ hq, add_sub_cancel, zpow_natCast, LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul, mul_comm]
  · have h1 : ((qOf P : E) ^ ((m : ℤ) - 1)) • y ∈
        homS (LocE.lamY P (qOf P) n' c' fun i => i + 1) (LocE.lamY P (qOf P) n c fun i => i + 1) := by
      refine mem_homS_sclLat.2 fun l s => ?_
      have hl := l.2
      have e : 0 ≤ (m : ℤ) - 1 + (LocE.scE n' (fun i => i + 1) s.1 - LocE.scE n (fun i => i + 1) l.1) := by
        unfold LocE.scE
        dsimp only
        split_ifs <;> omega
      convert ((intHom_iff _).1 hy s l).mul (intAt_zpow e) using 1
      rw [zpow_add₀ hq, LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul]
      ring
    have h2 := h.2.1 x _ h1
    rwa [smul_smul, zpow_sub_one₀ hq, mul_comm _ (qOf P : E)⁻¹, mul_inv_cancel_left₀ hq, zpow_natCast] at h2

theorem good_omPhi_two {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)
    (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)
    (cst : LocCst X (rowSG Pr sel mu)) (i : ℕ) (P : rowSG Pr sel mu) (hi : i + 2 ≤ R.m) (hP : P.1 ∈ Pr.vGs)
    {hal : AutY X R i} {h : AutY X R (i + 1)} (ha : hal ∈ stabL X.E _ (lamYat (Pr := Pr) (R := R) i P.1))
    (hb : h ∈ stabL X.E _ (lamYat (Pr := Pr) (R := R) (i + 1) P.1)) :
    Good P.1 (homS (LocE.lamY P.1 (qOf P.1) (R.N i) (cOf R i) fun i => i + 1)
      (LocE.lamY P.1 (qOf P.1) (R.N (i + 1)) (cOf R (i + 1)) fun i => i + 1)) (omPhi Ch sel mu cst i P hal h) := by
  have h1 : R.k ≤ R.N i := Nat.le_add_right _ _
  have h2 : R.k ≤ R.N (i + 1) := Nat.le_add_right _ _
  have h3 : R.r + (i + 1 - 1) * R.t = R.N i + cOf R i := by
    unfold Ranks.r Ranks.N cOf
    rw [Nat.add_sub_cancel, mul_add i]
    omega
  have h4 : R.N i + cOf R i ≤ R.N (i + 1) + cOf R (i + 1) := by
    unfold Ranks.N cOf
    rw [add_mul i]
    omega
  unfold lamYat at ha hb
  rw [if_pos hP] at ha hb
  refine good_om_two ?_ _ _ _ ha hb
  unfold PhiAt
  rw [if_pos hP]
  split_ifs
  · exact good_PhiGS _ _ h1 h2 h3 h4
  · exact good_PhiG _ _ h1 h2 h3 h4

theorem omPhi_bdd_type {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)
    (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)
    (cst : LocCst X (rowSG Pr sel mu)) (i : ℕ) (P : rowSG Pr sel mu) (hi : i + 2 ≤ R.m) (hP : P.1 ∈ Pr.vGs)
    (hal : AutY X R i) (h : AutY X R (i + 1)) (ha : hal ∈ stabL X.E _ (lamYat (Pr := Pr) (R := R) i P.1))
    (hb : h ∈ stabL X.E _ (lamYat (Pr := Pr) (R := R) (i + 1) P.1)) :
    HomBdd P.1 R.m (omPhi Ch sel mu cst i P hal h) ∧
      ∀ x, omPhi Ch sel mu cst i P hal h x ≠ 0 → IntAt P.1 ((qOf P.1 : X.E) * Loc.chArg x) := by
  have hg := good_omPhi_two Ch sel mu cst i P hi hP ha hb
  refine ⟨homBdd_of_good (by unfold cOf; omega) (by unfold cOf; omega) hg, fun x hx => ?_⟩
  have := GlobalTheory.IndefiniteRowSideFullHecke.SourceLatticeInvariance.intAt_neg (chArg_int (hg.1 x hx))
  rwa [mul_neg, neg_neg] at this

end GlobalTheory.Mem.Col2.BddG

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OneMapRef GlobalTheory.WeilParts

namespace GlobalTheory.OneMapRef.FactsLat

variable {D : D7}

theorem selfDual_frame_level_one_lattice_eq_standard {V : HSp D} {β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)}
    {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)} (h : IsSDFrame V β Λ 1) :
    (Λ : Set (Fin V.rank → D.host.E)) = Formalism.MainNotions.StandardLattice.L0c D V := by
  obtain ⟨c, -, -, -, h1, h2⟩ := h
  simp only [one_pow, Nat.cast_one, one_smul] at h1 h2
  exact Set.ext fun x => ⟨h2 x, h1 x⟩

theorem pi_eq_stdL (E : Type) [Field E] [NumberField E] (n : ℕ) :
    (Submodule.pi Set.univ fun _ => (1 : Submodule (𝓞 E) E)) = stdL E n := by
  apply le_antisymm
  · intro x hx
    rw [← Finset.univ_sum_single x]
    refine Submodule.sum_mem _ fun a _ => ?_
    obtain ⟨b, hb⟩ := Submodule.mem_one.1 (hx a trivial)
    have : (Pi.single a (x a) : Fin n → E) = b • (Pi.single a 1 : Fin n → E) := by
      rw [← Pi.single_smul, ← hb, Algebra.smul_def, mul_one]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨a, rfl⟩ j -
    by_cases h : j = a
    · subst h
      exact Submodule.mem_one.2 ⟨1, by simp⟩
    · simp [h]

theorem arr_injective {n : ℕ} {q : ℕ} (hq : q ≤ n) : Function.Injective (arr q : Fin n → Fin n) := by
  intro a b h
  have h' := congrArg Fin.val h
  have := a.2
  have := b.2
  unfold arr at h'
  apply Fin.ext
  split_ifs at h' <;> simp only at h' <;> omega

section Model

variable {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) {p q : ℕ} (hpq : p + q = V.rank)
  (hε : ∀ τ a, M.ε τ a = decide ((a : ℕ) < p))
include hpq hε

theorem nNeg_eq (τ : D.what₂.Tau) : nNeg (M.ε τ) = q := by
  rw [nNeg_shape (by omega) (hε τ)]; omega

theorem negM_eq (τ : D.what₂.Tau) :
    negM V q = diagonal fun c => (if M.ε τ (arr (nNeg (M.ε τ)) c) = true then (1 : ℂ) else -1) := by
  unfold negM
  congr 1
  funext c
  have := c.2
  rw [nNeg_eq M hpq hε, hε, arr, sgn]
  by_cases h : (c : ℕ) < q
  · rw [dite_eq_left h, if_pos h, if_neg (by simp only [decide_eq_true_eq]; omega)]; simp
  · rw [dite_eq_right h, if_neg h, if_pos (by simp only [decide_eq_true_eq]; omega)]; simp

theorem isONeg_x0Mat : IsONeg V q (x0Mat M) := by
  intro τ
  have hu := (Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ)
  have h1 : M.fr τ * (M.fr τ)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hu
  have h2 : (onb M τ)ᴴ * gramAt D V τ * onb M τ = Formalism.REAL.Jm (M.ε τ) := by
    rw [← M.fr_gram τ]; unfold onb
    calc _ = (M.fr τ * (M.fr τ)⁻¹)ᴴ * Formalism.REAL.Jm (M.ε τ) * (M.fr τ * (M.fr τ)⁻¹) := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = _ := by rw [h1]; simp
  have h3 : (x0Mat M τ)ᴴ * gramAt D V τ * x0Mat M τ =
      ((onb M τ)ᴴ * gramAt D V τ * onb M τ).submatrix (arr (nNeg (M.ε τ))) (arr (nNeg (M.ε τ))) := rfl
  rw [h3, h2, negM_eq M hpq hε τ, Formalism.REAL.Jm, Matrix.submatrix_diagonal _ _ (arr_injective (nNeg_le _))]
  rfl

theorem cart_eq_cartZ : cart M = cartZ V q (x0Mat M) := by
  funext τ
  have hn : negM V q * negM V q = 1 := by
    rw [negM_eq M hpq hε τ, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1; funext a; split_ifs <;> simp
  have h1 : (negM V q * ((x0Mat M τ)ᴴ * gramAt D V τ)) * x0Mat M τ = 1 := by
    rw [Matrix.mul_assoc, isONeg_x0Mat M hpq hε τ, hn]
  have hu : IsUnit (x0Mat M τ).det := Matrix.isUnit_det_of_left_inverse h1
  rw [cartZ, negM_eq M hpq hε τ, ← torus_x0Mat M τ fun a => if M.ε τ a = true then (1 : ℂ) else -1,
    Matrix.mul_nonsing_inv_cancel_right _ _ hu]
  rfl

end Model

theorem muVal_cast {V W : HSp D} (hV : V = W) {χ : (AE D)ˣ →* Circle} {mu : GA D V → ℂ} (h : MuVal V χ mu) :
    MuVal W χ (castDict hV mu) := by
  subst hV; exact h

theorem latEmb_cast {V W : HSp D} (hV : V = W) {r : ℕ} (hr : V.rank = r) (hr' : W.rank = r) {La : Type} [AddCommGroup La]
    [Module (𝓞 D.host.E) La] (ι : La →ₗ[𝓞 D.host.E] (Fin r → D.host.E))
    (h : LatEmb V (LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast hr) ∘ₗ ι)) :
    LatEmb W (LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast hr') ∘ₗ ι) := by
  subst hV; exact h

theorem isAA_span {k : ℕ} (L : Lt D.host.E k) : GlobalTheory.Ker.IsAA (Submodule.span (𝓞 D.host.E)
    {w | ∃ a : D.host.E, a ∈ D.host.AA ∧ ∃ v ∈ L, w = a • v}) L := by
  intro v
  rw [← Submodule.mem_toAddSubgroup]
  constructor
  · intro hv
    induction hv using Submodule.span_induction with
    | mem x hx => exact AddSubgroup.subset_closure hx
    | zero => exact zero_mem _
    | add x y _ _ hx hy => exact add_mem hx hy
    | smul c x hx' hx =>
      clear hx'
      induction hx using AddSubgroup.closure_induction with
      | mem x hx =>
        obtain ⟨a, ha, t, ht, rfl⟩ := hx
        exact AddSubgroup.subset_closure ⟨a, ha, c • t, L.smul_mem c ht, smul_comm _ _ _⟩
      | zero => rw [smul_zero]; exact zero_mem _
      | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
      | neg x _ hx => rw [smul_neg]; exact neg_mem hx
  · intro hv
    exact (AddSubgroup.closure_le _).2 (fun x hx => Submodule.subset_span hx) hv

theorem isMov_hLat (W : HSp D) (h : GA D W) :
    GlobalTheory.Ker.IsMov (GlobalTheory.Ker.fmt W h) (Bridge.hLat W 1) (Bridge.hLat W (FWT.fin W h)) := by
  intro u
  rw [GlobalTheory.MovedLat.hLat_one]
  have := Set.ext_iff.1 (GlobalTheory.MovedLat.hat_hLat W (FWT.fin W h)) u
  exact this.trans ⟨fun ⟨z, hz, e⟩ => ⟨z, hz, e.symm⟩, fun ⟨z, hz, e⟩ => ⟨z, hz, e.symm⟩⟩

end GlobalTheory.OneMapRef.FactsLat
end

section

namespace GlobalTheory.OneMapRef.DictPt

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory

theorem isDerivAt0_comp {X : Scheme.{0}} {g g' : ℕ} {e : (Fin g → ℂ) → (Sp ℂ ⟶ X)} (hol : IsHolTo Set.univ e)
    (ρ : (Fin g' → ℂ) →L[ℂ] (Fin g → ℂ)) {w : Fin g' → ℂ} {u : Sp (DualNumber ℂ) ⟶ X} (h : IsDerivAt0 e (ρ w) u) :
    IsDerivAt0 (fun z => e (ρ z)) w u := by
  rw [HolHom.isDerivAt0_iff] at h ⊢
  refine ⟨h.1.trans (congrArg e (map_zero ρ).symm), fun U hU f => ?_⟩
  have hU' : ⊤ ≤ e 0 ⁻¹ᵁ U := by simpa only [map_zero] using hU
  have h1 : HasFDerivAt (fun t => valAt' (e t) U f) (fderiv ℂ (fun t => valAt' (e t) U f) 0) (ρ 0) := by
    rw [map_zero]; exact ((HolHom.holAt_of_isHolTo hol (Set.mem_univ 0) U hU').2 f).hasFDerivAt
  exact (h.2 U hU' f).trans (congrArg (· w) (h1.comp 0 ρ.hasFDerivAt).fderiv).symm

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
  {l : Geo.Tor.Level H} {Xo : Moduli Dw l} {σ : KA l →+* ℂ} {g g' : ℕ} {ty : Fin g' → (E →+* ℂ)}

theorem isHolTo_ex (F : FamilyUnif Xo σ ty) (i : Fin F.n) {P : (F.Di i).La →+ (Fin g' → ℂ)}
    (hP : IsPeriod (F.Di i) ty P) : IsHolTo Set.univ (fun z => (F.ex i P z).left) := by
  have h := (F.hol i 0 Set.univ (fun _ => P) isOpen_univ ⟨fun _ _ => hP, fun _ => differentiableOn_const _⟩).2
  exact HolHom.isHolTo_of_holAt isOpen_univ fun z _ =>
    (HolHom.holAt_of_isHolTo h (z := (0, z)) ⟨trivial, trivial⟩).precomp (k := fun z => (0, z)) (by fun_prop)

theorem levPt_eq (F : FamilyUnif Xo σ ty) (i : Fin F.n) {Pm : (F.Di i).La →+ (Fin g' → ℂ)}
    (hper : IsPeriod (F.Di i) ty Pm) (π : Fin g ≃ Fin g') {y : Sp ℂ ⟶ Xo.X} (h : y = F.u i Pm)
    (ex : (Fin g → ℂ) → (ptO Xo y ⟶ Xo.univ.t.G)) (u : Fin g' → (Sp (DualNumber ℂ) ⟶ Xo.univ.t.G.left))
    (b1 : ∀ z w, ex (z + w) = ex z * ex w) (b2 : IsHolTo Set.univ (fun z => (ex z).left))
    (b3 : ∀ m, IsDerivAt0 (fun z => (ex z).left) (Pi.single (π.symm m) 1) (u m))
    (b4 : ∀ m, IsDerivAt0 (fun z => (F.ex i Pm z).left) (Pi.single m 1) (u m))
    (a : Dw.La) (ha : a ∈ Mfr l • (⊤ : Submodule (𝓞 E) Dw.La)) :
    levPt Xo y a = ex (fun j => (l.M : ℂ)⁻¹ * Pm (F.t i a) (π j)) := by
  subst h
  let ρ : (Fin g' → ℂ) →L[ℂ] (Fin g → ℂ) := ContinuousLinearMap.pi fun j => ContinuousLinearMap.proj (π j)
  have hρ : ∀ m, ρ (Pi.single m 1) = Pi.single (π.symm m) 1 := fun m => by
    funext j
    change (Pi.single m 1 : Fin g' → ℂ) (π j) = _
    simp only [Pi.single_apply, Equiv.eq_symm_apply]
  have E : (fun z => ex (ρ z)) = F.ex i Pm :=
    GlobalTheory.AnUniq.exp_eq (fun z w => by rw [map_add (f := _), b1]) (F.ex_add _ _ hper)
      (HolHom.isHolTo_of_holAt isOpen_univ fun z _ =>
        (HolHom.holAt_of_isHolTo b2 (Set.mem_univ (ρ z))).precomp ρ.differentiableAt) (isHolTo_ex F _ hper)
      u (fun m => isDerivAt0_comp b2 ρ (by rw [hρ]; exact b3 m)) b4
  exact (F.ex_eta i Pm hper a ha).trans (congrFun E _).symm

theorem ex_add_ker {y : Sp ℂ ⟶ Xo.X} (ex : (Fin g → ℂ) → (ptO Xo y ⟶ Xo.univ.t.G))
    (b1 : ∀ z w, ex (z + w) = ex z * ex w) (z k z' : Fin g → ℂ) (hk : ex k = 1) (h : z' = z + k) : ex z = ex z' := by
  rw [h, b1, hk, _root_.mul_one]

theorem sub_eq_nsmul {A : Type} [AddCommGroup A] (M : ℕ) (p q z w w' : A) (e : p - z = M • w)
    (e' : q - z = M • w') : p - q = M • (w - w') := by
  rw [smul_sub, ← e, ← e', sub_sub_sub_cancel_right]

end GlobalTheory.OneMapRef.DictPt

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OneMapRef GlobalTheory.WeilParts

theorem GlobalTheory.OneMapRef.DictPt.exists_sub_eq {D : D7} (V : HSp D) (g : GA D V) (M : ℕ) (hM : M ≠ 0)
    (p q : Fin V.rank → D.host.E) (z w w' : Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E)
    (hw : w ∈ latGHat V g) (hw' : w' ∈ latGHat V g) (e : finVec V p - z = M • w) (e' : finVec V q - z = M • w') :
    (M : D.host.E)⁻¹ • (p - q) ∈ latG V g := by
  rw [(GlobalTheory.MarkCoset.latG_spec D V g).1]
  have hM' : (M : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 hM
  have h1 : M • finVec V ((M : D.host.E)⁻¹ • (p - q)) = M • (w - w') := by
    refine Eq.trans ?_ (GlobalTheory.OneMapRef.DictPt.sub_eq_nsmul M _ _ z w w' e e')
    funext i
    change M • ((1 : Af D.host.F) ⊗ₜ[D.host.F] ((M : D.host.E)⁻¹ * (p i - q i))) = 1 ⊗ₜ p i - 1 ⊗ₜ q i
    rw [← TensorProduct.tmul_smul, nsmul_eq_mul, mul_inv_cancel_left₀ hM', TensorProduct.tmul_sub]
  have h2 : finVec V ((M : D.host.E)⁻¹ • (p - q)) = w - w' :=
    GlobalTheory.MarkCoset.nsmul_cancel D.host.F M (Nat.cast_ne_zero.2 hM) h1
  rw [h2]
  exact sub_mem hw hw'



theorem GlobalTheory.OneMapRef.DictPt.dict_point : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (W : HSp D) (r : ℕ) (hr : W.rank = r) (U : Unf Xo c σ r) (dict : GA D W → Σ k, Frame (U.X k).Ψ r) (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin W.rank → D.host.E)) (g₀ : ℕ) (e₀ : Fin g₀ ≃ Σ τ : D.host.E →+* ℂ, Fin (Dw.mult τ)) (F : ReciprocityTheory.ChartRestriction.G.Geo.Tor.FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e₀ j).1)) (ik : U.Comp → Fin F.n) (φ : ∀ k, (F.Di (ik k)).La ≃ₗ[𝓞 D.host.E] (U.X k).Λ) (th : ∀ k, (U.X k).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ) (θ : InfFam D) (Z₀ : Fam W), GoodEmb c σ → IsUnf U → 1 ≤ r → IsInfFam θ → (∀ k τ, IsInfEmb τ.1 (th k τ)) → DictLat U W hr dict ι e₀ F ik φ th x₀ → (∀ ρ, x₀ (tauE D ρ) = Matrix.reindex (finCongr hr) (finCongr hr) (Z₀ ρ)) → ∀ h : GA D W, ∃ γ ∈ GQ W, MarkBy U W hr dict ι F ik φ h γ ∧ latW hr (U.X (dict h).1).Λ = latG W (γ * h) ∧ (∀ eT : D.what₂.Tau ≃ (U.X (dict h).1).Ψ, (∀ ρ, (eT ρ).1 = tauE D ρ) → (dict h).2 = frOf hr eT (mvZ θ (γ * h) Z₀)) ∧ ∀ (hx : (dict h).2 ∈ (U.X (dict h).1).dom) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] (U.X (dict h).1).Λ) (idx : Fin g ≃ (U.X (dict h).1).Ψ × Fin r) (e : Fin g ≃ Lt1 Dw), IsSympl (U.X (dict h).1) bas → Matched c σ (U.X (dict h).1) idx e → letI : Algebra c.F ℂ := σ.toAlgebra; ∀ (A : AnFib (U.X (dict h).1) bas idx e (dict h).2 (U.X (dict h).1).Λ (ptC U (dict h).1 ⟨(dict h).2, hx⟩)) (mk : Dw.La →ₗ[𝓞 D.host.E] (Fin r → D.host.E)), (∀ a, mk a ∈ (U.X (dict h).1).Λ) → MarkAd hr l ι (γ * h) mk → A.Marked mk := by
  intro D H Dw l Xo c σ W r hr U dict ι g₀ e₀ F ik φ th x₀ θ Z₀ hσ hU h1 hθ hth hD hx₀ h
  subst hr
  obtain ⟨γ, hγ, hl, hm, hf⟩ := hD.2 h
  have hΛ : (U.X (dict h).1).Λ = latG W (γ * h) := SetLike.ext' (hl.trans (Set.image_id _))
  refine ⟨γ, hγ, ⟨hγ, hl, hm⟩, hΛ, fun eT heT => ?_, ?_⟩
  · funext τ
    obtain ⟨ρ, rfl⟩ := eT.surjective τ
    have e1 : th _ (eT ρ) = θ ρ :=
      GlobalTheory.SmoothForms.RealPts.infEmb_unique _ _ _ (hth _ (eT ρ)) (by rw [heT]; exact hθ ρ)
    have := hf (eT ρ)
    rw [e1, heT, hx₀] at this
    funext a b
    simp only [frOf, Equiv.symm_apply_apply]
    exact congrFun (congrFun this a) b
  · intro hx g bas idx e hs hM
    letI : Algebra c.F ℂ := σ.toAlgebra
    intro A mk hmk hA a ha
    obtain ⟨Pm, hPm, hP, hu, hder⟩ := hD.1.2 (dict h).1 ⟨(dict h).2, hx⟩
    have hM0 : l.M ≠ 0 := by have := l.three_le; omega
    have key := GlobalTheory.OneMapRef.DictPt.levPt_eq F _ hP (e.trans e₀.symm) hu A.ex (fun m => (U.un _ ⟨(dict h).2, hx⟩).u (e₀ m).1 (e₀ m).2)
      A.ex_add A.hol (fun m => A.der (e₀ m)) (fun m => by simpa only [Sigma.eta, Equiv.symm_apply_apply] using hder (e₀ m).1 (e₀ m).2) a ha
    obtain ⟨w, hw, ew⟩ := hA a ha
    obtain ⟨w', hw', ew'⟩ := hm a ha
    have hmem := GlobalTheory.OneMapRef.DictPt.exists_sub_eq W (γ * h) l.M hM0 _ _ _ w w' hw hw' ew ew'
    rw [← hΛ] at hmem
    have hk := (A.ex_ker _).2 ⟨_, hmem, rfl⟩
    refine key.trans (GlobalTheory.OneMapRef.DictPt.ex_add_ker A.ex A.ex_add _ _ _ hk ?_)
    funext j
    have e3 : ∀ v (ℓ ℓ' : Lt1 Dw), ℓ = ℓ' → perFr (U.X (dict h).1) (dict h).2 v (relab c σ ℓ.1) ℓ.2 =
        perFr (U.X (dict h).1) (dict h).2 v (relab c σ ℓ'.1) ℓ'.2 := fun v ℓ ℓ' hℓ => by rw [hℓ]
    rw [Pi.add_apply, hPm, Equiv.trans_apply, e3 _ _ _ (e₀.apply_symm_apply (e j)), ← hM.1]
    have e2 : ∀ p q : Fin W.rank → D.host.E, (l.M : D.host.E)⁻¹ • p =
        (l.M : D.host.E)⁻¹ • q + (l.M : D.host.E)⁻¹ • (p - q) := fun p q => by rw [← smul_add, add_sub_cancel]
    rw [e2 (mk a) (φ _ (F.t _ a))]
    simp only [pv, Function.comp_apply, per_add, Pi.add_apply]
    congr 1
    rw [per_smul, map_inv₀, map_natCast]
end

section

open MeasureTheory Matrix Filter Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum
open scoped InnerProductSpace Topology

theorem _root_.GlobalTheory.T.exists_averaged_operator_mapping_to_KFinite : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mx n → (H →L[ℂ] H)), Std ε σ → ∀ a : H, a ≠ 0 → ∀ v, IsKFin ε σ v → ∃ T : H → H, IsAvg ε σ T ∧ T a = v := by
  first | exact @GlobalTheory.TypeSum.exists_isAvg_apply_eq | exact GlobalTheory.TypeSum.exists_isAvg_apply_eq | (intros; apply GlobalTheory.TypeSum.exists_isAvg_apply_eq <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.SymFrame

variable {D : D7}

def EwAt (X : HidaSetting D) (w : HeightOneSpectrum (𝓞 D.host.E)) : Prop :=
  ∀ y ∈ X.B.I.Lf, (1 - X.ew) • y ∈ wLf X w


open Classical in
def epsW (X : HidaSetting D) (w : HeightOneSpectrum (𝓞 D.host.E)) : Fin D.R.k → VA X.B.I :=
  if EwAt X w then X.bw else fun i => X.bwd (Fin.rev i)

def symVec (X : HidaSetting D) (w : HeightOneSpectrum (𝓞 D.host.E)) : Fin D.R.r → VA X.B.I :=
  GlobalTheory.SeeConjRead.flagV D.R.rS D.R.k D.R.r X.e0 X.f0 (epsW X w) X.z0

def IsMatIn (X : HidaSetting D) (w : HeightOneSpectrum (𝓞 D.host.E)) {g : ℕ} (u : Fin D.R.r → VA X.B.I) (x : X.B.I.Gf)
    (N : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod g)) : Prop :=
  ∀ i, X.B.I.fmat x *ᵥ u i - ∑ j, (((N j i).val : ℕ) : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) • u j ∈ wLf X w

end GlobalTheory.Mem.SymFrame

end

namespace GlobalTheory.Mem.SymFrame

theorem isMatIn_perm {D : D7} {X : HidaSetting D} {w : HeightOneSpectrum (𝓞 D.host.E)} {g : ℕ}
    (s : Fin D.R.r → VA X.B.I) (x : X.B.I.Gf) (N : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod g)) (π : Equiv.Perm (Fin D.R.r))
    (hN : IsMatIn X w (fun j => s (π.symm j)) x N) : IsMatIn X w s x (N.submatrix π π) := by
  intro i
  have h1 := hN (π i)
  rw [← Equiv.sum_comp π] at h1
  simpa [Matrix.submatrix_apply] using h1

theorem mem_unipSym_bc {κ κ' : Type} [CommRing κ] [CommRing κ'] (f : κ ≃+* κ') {r ρ k : ℕ} (u : GL (Fin r) κ) :
    Formalism.UG.bc (f : κ →+* κ') u ∈ unipSym κ' r ρ k ↔ u ∈ unipSym κ r ρ k := by
  have e : ∀ i j, ((Formalism.UG.bc (f : κ →+* κ') u : GL (Fin r) κ') : Matrix (Fin r) (Fin r) κ') i j =
      f ((u : Matrix (Fin r) (Fin r) κ) i j) := fun _ _ => rfl
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    refine ⟨⟨fun i j hij => ?_, fun i => ?_⟩, fun i j ha hb hc => ?_⟩
    · have := h1 hij; rw [e] at this; exact f.injective (this.trans (map_zero f).symm)
    · have := h2 i; rw [e] at this; exact f.injective (this.trans (map_one f).symm)
    · have := h3 i j ha hb hc; rw [e] at this; exact f.injective (this.trans (map_zero f).symm)
  · rintro ⟨⟨h1, h2⟩, h3⟩
    refine ⟨⟨fun i j hij => ?_, fun i => ?_⟩, fun i j ha hb hc => ?_⟩
    · show ((Formalism.UG.bc (f : κ →+* κ') u : GL (Fin r) κ') : Matrix (Fin r) (Fin r) κ') i j = 0
      rw [e, h1 hij, map_zero]
    · rw [e, h2 i, map_one]
    · rw [e, h3 i j ha hb hc, map_zero]

theorem edgeSum_bc {κ κ' : Type} [CommRing κ] [CommRing κ'] (f : κ ≃+* κ') {r : ℕ} (Ed : Fin r → Fin r → Prop)
    [DecidableRel Ed] (u : GL (Fin r) κ) : edgeSum Ed (Formalism.UG.bc (f : κ →+* κ') u) = f (edgeSum Ed u) := by
  unfold edgeSum

  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_

  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  split_ifs
  · rfl
  · rw [map_zero]

end GlobalTheory.Mem.SymFrame
end
