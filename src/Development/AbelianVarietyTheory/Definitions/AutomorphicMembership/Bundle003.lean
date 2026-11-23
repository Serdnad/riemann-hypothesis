module

public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle011
public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.Analysis.Normed.Lp.lpHolder
public import Formalism.LocalToGlobal.UnitaryNorms.Bundle006
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Algebra.Order.Star.Rat
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

namespace GlobalTheory.FockSeq

open MvPolynomial GlobalTheory.FockAlg

variable {σ : Type}

abbrev L2 (σ : Type) : Type := lp (fun _ : σ →₀ ℕ => ℂ) 2

def mfact (α : σ →₀ ℕ) : ℕ := α.prod fun _ k => k.factorial

theorem mfact_pos (α : σ →₀ ℕ) : 0 < mfact α := by
  unfold mfact Finsupp.prod
  exact Finset.prod_pos fun l _ => Nat.factorial_pos (α l)

theorem mfact_cast (α : σ →₀ ℕ) : ((mfact α : ℕ) : ℂ) = α.prod fun _ k => (k.factorial : ℂ) := by
  unfold mfact Finsupp.prod
  push_cast
  rfl

def wt (α : σ →₀ ℕ) : ℂ := (Real.sqrt (mfact α) : ℝ)

theorem wt_ne_zero (α : σ →₀ ℕ) : wt α ≠ 0 := by
  have h : 0 < Real.sqrt (mfact α : ℝ) := Real.sqrt_pos.2 (Nat.cast_pos.2 (mfact_pos α))
  unfold wt
  exact_mod_cast h.ne'

theorem star_wt_mul (α : σ →₀ ℕ) : (starRingEnd ℂ) (wt α) * wt α = (mfact α : ℕ) := by
  have h : Real.sqrt (mfact α : ℝ) * Real.sqrt (mfact α : ℝ) = (mfact α : ℝ) :=
    Real.mul_self_sqrt (Nat.cast_nonneg _)
  unfold wt
  rw [Complex.conj_ofReal, ← Complex.ofReal_mul, h, Complex.ofReal_natCast]

variable [DecidableEq σ]

def emb (σ : Type) [DecidableEq σ] : MvPolynomial σ ℂ →ₗ[ℂ] L2 σ :=
  (basisMonomials σ ℂ).constr ℂ fun α => lp.single 2 α (wt α)

theorem emb_monomial (α : σ →₀ ℕ) (c : ℂ) : emb σ (monomial α c) = lp.single 2 α (c * wt α) := by
  have h : monomial α c = c • basisMonomials σ ℂ α := by
    rw [coe_basisMonomials, smul_monomial, smul_eq_mul, mul_one]
  rw [h, map_smul, emb, Module.Basis.constr_basis, ← smul_eq_mul, lp.single_smul]

theorem emb_apply (f : MvPolynomial σ ℂ) (α : σ →₀ ℕ) : emb σ f α = AddMonoidAlgebra.coeff f α * wt α := by
  induction f using MvPolynomial.induction_on' with
  | monomial β c =>
    rw [emb_monomial, lp.single_apply, coeff_monomial]
    by_cases h : β = α
    · subst h
      simp
    · simp [h]
  | add f g hf hg =>
    rw [map_add (f := _), lp.coeFn_add, Pi.add_apply, hf, hg, MvPolynomial.coeff_add, add_mul]

theorem emb_injective : Function.Injective (emb σ) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro f hf
  ext α
  have h : emb σ f α = 0 := by rw [hf]; rfl
  rw [emb_apply] at h
  simpa [AddMonoidAlgebra.coeff] using (mul_eq_zero.1 h).resolve_right (wt_ne_zero α)

theorem dense_range_emb : Dense (Set.range (emb σ)) := by
  intro x
  have hx := lp.hasSum_single (E := fun _ : σ →₀ ℕ => ℂ) (p := 2) ENNReal.ofNat_ne_top x
  rw [HasSum] at hx
  refine mem_closure_of_tendsto hx (Filter.Eventually.of_forall fun s => ?_)
  refine ⟨∑ α ∈ s, monomial α (x α / wt α), ?_⟩

  rw [map_sum]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [emb_monomial, div_mul_cancel₀ _ (wt_ne_zero α)]

theorem isFockIsometry_embedding : IsFockIP (emb σ) := by
  intro α β
  rw [emb_monomial, emb_monomial, lp.inner_single_left, lp.single_apply, one_mul, one_mul]
  by_cases h : α = β
  · subst h
    rw [Pi.single_eq_same, if_pos rfl, RCLike.inner_apply, mul_comm, star_wt_mul, mfact_cast]
  · rw [Pi.single_eq_of_ne h, if_neg h, inner_zero_right]


omit [DecidableEq σ] in
def diag (c : (σ →₀ ℕ) → ℂ) (hc : ∀ α, ‖c α‖ = 1) : L2 σ →L[ℂ] L2 σ :=
  lp.mapCLM 2 (fun α => c α • ContinuousLinearMap.id ℂ ℂ) zero_le_one fun α => by
    simp [norm_smul, hc]


omit [DecidableEq σ] in
@[simp] theorem diag_apply (c : (σ →₀ ℕ) → ℂ) (hc : ∀ α, ‖c α‖ = 1) (x : L2 σ) (α : σ →₀ ℕ) :
    diag c hc x α = c α * x α := rfl


omit [DecidableEq σ] in
theorem norm_diag (c : (σ →₀ ℕ) → ℂ) (hc : ∀ α, ‖c α‖ = 1) (x : L2 σ) : ‖diag c hc x‖ = ‖x‖ := by
  have hp : 0 < (2 : ENNReal).toReal := by norm_num
  rw [lp.norm_eq_tsum_rpow hp, lp.norm_eq_tsum_rpow hp]
  congr 1
  refine tsum_congr fun α => ?_
  rw [diag_apply, norm_mul, hc, one_mul]

theorem diag_emb_monomial (c : (σ →₀ ℕ) → ℂ) (hc : ∀ α, ‖c α‖ = 1) (α : σ →₀ ℕ) (a : ℂ) :
    diag c hc (emb σ (monomial α a)) = c α • emb σ (monomial α a) := by
  ext β
  rw [diag_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, emb_monomial, lp.single_apply]
  by_cases h : β = α
  · subst h
    rfl
  · rw [Pi.single_eq_of_ne h, mul_zero, mul_zero]

theorem continuous_of_dense {G H : Type*} [TopologicalSpace G] [NormedAddCommGroup H] [NormedSpace ℂ H]
    (π : G → H →L[ℂ] H) (hπ : ∀ g x, ‖π g x‖ = ‖x‖) {S : Set H} (hS : Dense S)
    (h : ∀ x ∈ S, Continuous fun g => π g x) (x : H) : Continuous fun g => π g x := by
  rw [continuous_iff_continuousAt]
  intro g₀
  rw [ContinuousAt, Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨y, hyS, hxy⟩ := Metric.mem_closure_iff.1 (hS x) (ε / 3) (by positivity)
  have hy := (h y hyS).continuousAt (x := g₀)
  rw [ContinuousAt, Metric.tendsto_nhds] at hy
  have hd : ∀ g, dist (π g x) (π g y) = dist x y := fun g => by
    rw [dist_eq_norm, dist_eq_norm, ← map_sub, hπ]
  filter_upwards [hy (ε / 3) (by positivity)] with g hg
  have h₁ := hd g
  have h₂ := hd g₀
  rw [dist_comm] at h₂
  calc dist (π g x) (π g₀ x)
      ≤ dist (π g x) (π g y) + dist (π g y) (π g₀ y) + dist (π g₀ y) (π g₀ x) :=
        dist_triangle4 _ _ _ _
    _ < ε := by rw [h₁, h₂]; linarith

end GlobalTheory.FockSeq
end
end

section

noncomputable section

namespace GlobalTheory.HeightCounting

open Formalism.BasicNotions Formalism.L2.Host NumberField IsDedekindDomain

def rowsEta {R : Ranks} (what₂ : Rows.Data R) (η : ℕ → what₂.places.Pl → ℚ) (hη : ∀ j w, 0 ≤ η j w) : Rows.Data R :=
  { what₂ with etaJ := η, etaJ_nonneg := hη }

structure NLay0 (R : Ranks) (H : Host R) (what₂ : Rows.Data R) [NumberField what₂.LL] [StarRing what₂.LL]
    (LL0 : IntermediateField ℚ what₂.LL) where
  loc : LocTheory
  locA : ∀ (l : ℕ) [Fact l.Prime], LocAinf l (loc l)
  locT : ∀ (l : ℕ) [Fact l.Prime], LocTied l (loc l) (locA l)
  nd : NData R H what₂
  ntw : NTw R H what₂ LL0 nd
  naut : NAut nd
  nbc : NBC naut
  nexp : NExp R H what₂ LL0 nd ntw
  ntypes : NTypes naut
  nStage_trivialCharacter_compat : ntypes.IdempotentMatchesAction
  nStage_trivialCharacter_coeff_eq : ∀ g : G0g nd, what₂.embLL ((nexp.eLL0 g : ↥LL0) : what₂.LL) = ntypes.e0.coeff g
  nth : NTh R H what₂ LL0 nd ntw nexp
  nbr : ∀ (i : nd.Loc) (w : HeightOneSpectrum (𝓞 H.E)), w ∈ Formalism.BasicNotions.placesOver H.E (nd.l i) →
    Formalism.BasicNotions.LocBridge (nd.l i) H.E nd.Om (ReciprocityTheory.Gal.Dec (F := H.E) (nd.plOm.1 w)) (nd.O i)
  nbr_ind : ∀ (i : nd.Loc) (w : HeightOneSpectrum (𝓞 H.E)) (hw : w ∈ Formalism.BasicNotions.placesOver H.E (nd.l i))
    (x : nd.Om), x ∈ nd.plOm.1 w ↔ ‖(nbr i w hw).j x‖ ≤ 1
  self_good : ∀ (i : nd.Loc) (w : HeightOneSpectrum (𝓞 H.E)) (hw : w ∈ Formalism.BasicNotions.placesOver H.E (nd.l i)),
    Formalism.BasicNotions.Loc.GoodCoef H.condN (nbr i w hw).LL
  ntwbr : ∀ (i : ntw.Tw) (w : HeightOneSpectrum (𝓞 H.E)), w ∈ Formalism.BasicNotions.placesOver H.E (ntw.l i) →
    Formalism.BasicNotions.LocBridge (ntw.l i) H.E nd.Om (ReciprocityTheory.Gal.Dec (F := H.E) (nd.plOm.1 w)) (ntw.O0 i)
  ntwbr_ind : ∀ (i : ntw.Tw) (w : HeightOneSpectrum (𝓞 H.E)) (hw : w ∈ Formalism.BasicNotions.placesOver H.E (ntw.l i))
    (x : nd.Om), x ∈ nd.plOm.1 w ↔ ‖(ntwbr i w hw).j x‖ ≤ 1
  loc_tie : Formalism.MainNotions.N.LocTie nd naut loc nbr
  bc_tie : Formalism.MainNotions.N.BcTie nd naut ntypes
  rbar_tie : Formalism.MainNotions.N.RbarTie nd naut ntypes
  mtpar_tie : Formalism.MainNotions.N.MtParTie nd naut ntypes

section
variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} [NumberField what₂.LL] [StarRing what₂.LL]
    {LL0 : IntermediateField ℚ what₂.LL}

def NLay0.ZOk (L : NLay0 R H what₂ LL0) : Prop :=
  (∀ i x, x ∈ L.nd.Z i ↔ x ∈ Formalism.MainNotions.N.ZN L.nd L.naut i) ∧ ∀ i x, x ∈ L.nd.Zgood i ↔ x ∈ Formalism.MainNotions.N.ZgoodN L.nd L.naut i

def ndZ (N : NData R H what₂) (Z Zg : ∀ i, Finset (N.X i)) : NData R H what₂ := { N with Z := Z, Zgood := Zg }



def NLay0.setZ (L : NLay0 R H what₂ LL0) (Z Zg : ∀ i, Finset (L.nd.X i)) : NLay0 R H what₂ LL0 :=
  { loc := L.loc, locA := L.locA, locT := L.locT, nd := ndZ L.nd Z Zg, ntw := { L.ntw with }, naut := { L.naut with }
    nbc := { L.nbc with }, nexp := { L.nexp with }, ntypes := { L.ntypes with }, nStage_trivialCharacter_compat := L.nStage_trivialCharacter_compat, nStage_trivialCharacter_coeff_eq := L.nStage_trivialCharacter_coeff_eq
    nth := { L.nth with }, nbr := L.nbr, nbr_ind := L.nbr_ind, self_good := L.self_good, ntwbr := L.ntwbr
    ntwbr_ind := L.ntwbr_ind, loc_tie := L.loc_tie, bc_tie := L.bc_tie, rbar_tie := L.rbar_tie, mtpar_tie := L.mtpar_tie }


open Classical in
def NLay0.fixZ (L : NLay0 R H what₂ LL0) : NLay0 R H what₂ LL0 :=
  L.setZ (fun i => Finset.univ.filter fun x => x ∈ Formalism.MainNotions.N.ZN L.nd L.naut i)
    (fun i => Finset.univ.filter fun x => x ∈ Formalism.MainNotions.N.ZgoodN L.nd L.naut i)



def NLay0.reEta (L : NLay0 R H what₂ LL0) (η : ℕ → what₂.places.Pl → ℚ) (hη : ∀ j w, 0 ≤ η j w) :
    @NLay0 R H (rowsEta what₂ η hη) ‹NumberField what₂.LL› ‹StarRing what₂.LL› LL0 :=
  letI : NumberField (rowsEta what₂ η hη).LL := ‹NumberField what₂.LL›
  letI : StarRing (rowsEta what₂ η hη).LL := ‹StarRing what₂.LL›
  { loc := L.loc, locA := L.locA, locT := L.locT, nd := { L.nd with }, ntw := { L.ntw with }, naut := { L.naut with }
    nbc := { L.nbc with }, nexp := { L.nexp with }, ntypes := { L.ntypes with }, nStage_trivialCharacter_compat := L.nStage_trivialCharacter_compat, nStage_trivialCharacter_coeff_eq := L.nStage_trivialCharacter_coeff_eq
    nth := { L.nth with }, nbr := L.nbr, nbr_ind := L.nbr_ind, self_good := L.self_good, ntwbr := L.ntwbr
    ntwbr_ind := L.ntwbr_ind, loc_tie := L.loc_tie, bc_tie := L.bc_tie, rbar_tie := L.rbar_tie, mtpar_tie := L.mtpar_tie }


open Classical in
def NLay0.eta (L : NLay0 R H what₂ LL0) (j : ℕ) (w : what₂.places.Pl) : ℚ :=
  if 1 ≤ j ∧ j ≤ R.m then ∑ i ∈ L.nd.locs j w, L.nd.etaLoc i else what₂.etaJ j w

theorem NLay0.eta_nonneg (L : NLay0 R H what₂ LL0) (j : ℕ) (w : what₂.places.Pl) : 0 ≤ L.eta j w := by
  unfold NLay0.eta
  split_ifs
  · exact Finset.sum_nonneg fun i _ => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  · exact what₂.etaJ_nonneg j w

theorem NLay0.zOk_fixZ (L : NLay0 R H what₂ LL0) : L.fixZ.ZOk := by
  classical
  refine ⟨fun i x => ?_, fun i x => ?_⟩
  · exact ((@Finset.mem_filter _ _ (fun _ => Classical.propDecidable _) _ _).trans (and_iff_right (Finset.mem_univ _)))
  · exact ((@Finset.mem_filter _ _ (fun _ => Classical.propDecidable _) _ _).trans (and_iff_right (Finset.mem_univ _)))


theorem NLay0.ZOk.reEta {L : NLay0 R H what₂ LL0} (h : L.ZOk) (η : ℕ → what₂.places.Pl → ℚ) (hη : ∀ j w, 0 ≤ η j w) :
    @NLay0.ZOk R H (rowsEta what₂ η hη) ‹NumberField what₂.LL› ‹StarRing what₂.LL› LL0 (L.reEta η hη) := h

def NLay0.EtaOk (L : NLay0 R H what₂ LL0) : Prop :=
  ∀ j w, 1 ≤ j → j ≤ R.m → what₂.etaJ j w = ∑ i ∈ L.nd.locs j w, L.nd.etaLoc i


theorem NLay0.etaOk_reEta (L : NLay0 R H what₂ LL0) :
    @NLay0.EtaOk R H (rowsEta what₂ L.eta L.eta_nonneg) ‹NumberField what₂.LL› ‹StarRing what₂.LL› LL0
      (L.reEta L.eta L.eta_nonneg) := fun _ _ h1 h2 => if_pos ⟨h1, h2⟩

end

abbrev Lay0 (D : D7) : Type _ := NLay0 D.R D.host D.what₂ D.LL0



def setRaw (D : D7) (η : ℕ → D.what₂.places.Pl → ℚ) (hη : ∀ j w, 0 ≤ η j w)
    (P : @NLay0 D.R D.host (rowsEta D.what₂ η hη) D.nfLL D.starLL D.LL0)
    (hZ : @NLay0.ZOk D.R D.host (rowsEta D.what₂ η hη) D.nfLL D.starLL D.LL0 P)
    (hE : @NLay0.EtaOk D.R D.host (rowsEta D.what₂ η hη) D.nfLL D.starLL D.LL0 P) : D7 :=
  letI : NumberField (rowsEta D.what₂ η hη).LL := D.nfLL
  letI : StarRing (rowsEta D.what₂ η hη).LL := D.starLL
  { D with
    what₂ := rowsEta D.what₂ η hη
    loc := P.loc, locA := P.locA, locT := P.locT, nd := P.nd, ntw := P.ntw, naut := P.naut, nbc := P.nbc, nexp := P.nexp
    ntypes := P.ntypes, nStage_trivialCharacter_compat := P.nStage_trivialCharacter_compat, nStage_trivialCharacter_coeff_eq := P.nStage_trivialCharacter_coeff_eq, nth := P.nth, nbr := P.nbr, nbr_ind := P.nbr_ind
    self_good := P.self_good, ntwbr := P.ntwbr, ntwbr_ind := P.ntwbr_ind, loc_tie := P.loc_tie, bc_tie := P.bc_tie
    rbar_tie := P.rbar_tie, mtpar_tie := P.mtpar_tie, Z_tie := hZ.1, Zgood_tie := hZ.2, etaJ_tie := hE }

def setN (D : D7) (L : Lay0 D) : D7 :=
  setRaw D L.fixZ.eta L.fixZ.eta_nonneg (L.fixZ.reEta L.fixZ.eta L.fixZ.eta_nonneg) (L.zOk_fixZ.reEta _ _) L.fixZ.etaOk_reEta

def setK (D : D7) (P : Lay0 D) (hZ : P.ZOk) (hE : P.EtaOk) : D7 :=
  { D with
    loc := P.loc, locA := P.locA, locT := P.locT, nd := P.nd, ntw := P.ntw, naut := P.naut, nbc := P.nbc, nexp := P.nexp
    ntypes := P.ntypes, nStage_trivialCharacter_compat := P.nStage_trivialCharacter_compat, nStage_trivialCharacter_coeff_eq := P.nStage_trivialCharacter_coeff_eq, nth := P.nth, nbr := P.nbr, nbr_ind := P.nbr_ind
    self_good := P.self_good, ntwbr := P.ntwbr, ntwbr_ind := P.ntwbr_ind, loc_tie := P.loc_tie, bc_tie := P.bc_tie
    rbar_tie := P.rbar_tie, mtpar_tie := P.mtpar_tie, Z_tie := hZ.1, Zgood_tie := hZ.2, etaJ_tie := hE }

def cfK {D : D7} (P : Lay0 D) (hZ : P.ZOk) (hE : P.EtaOk) (c : CharFrame D) : CharFrame (setK D P hZ hE) :=
  ⟨c.P, c.W, c.mu0, c.eta, c.chiPsi, c.del, c.del', c.isMu0, c.isEta, c.isChi, c.isDel, c.isDel'⟩

def cfTr {D : D7} (L : Lay0 D) (c : CharFrame D) : CharFrame (setN D L) :=
  ⟨c.P, c.W, c.mu0, c.eta, c.chiPsi, c.del, c.del', c.isMu0, c.isEta, c.isChi, c.isDel, c.isDel'⟩

def lay0 (D : D7) : Lay0 D :=
  { loc := D.loc, locA := D.locA, locT := D.locT, nd := D.nd, ntw := D.ntw, naut := D.naut, nbc := D.nbc, nexp := D.nexp
    ntypes := D.ntypes, nStage_trivialCharacter_compat := D.nStage_trivialCharacter_compat, nStage_trivialCharacter_coeff_eq := D.nStage_trivialCharacter_coeff_eq, nth := D.nth, nbr := D.nbr, nbr_ind := D.nbr_ind
    self_good := D.self_good, ntwbr := D.ntwbr, ntwbr_ind := D.ntwbr_ind, loc_tie := D.loc_tie, bc_tie := D.bc_tie
    rbar_tie := D.rbar_tie, mtpar_tie := D.mtpar_tie }

end GlobalTheory.HeightCounting

end
end
