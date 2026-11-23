module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle008
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle009
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle256
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle010
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedCoefficientFieldInComplex
public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.FiniteDimensionalOfSz
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle260
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.PiTensorProduct
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
import ReciprocityTheory.GaloisValuations.GlobalA
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section

open Formalism.BasicNotions GlobalTheory.Mem GlobalTheory.MemN NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial

namespace GlobalTheory.MemN

theorem nonempty_places_closure (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] :
    Nonempty (Formalism.GaloisCohomology.Places E Ω) :=
  ⟨⟨fun v => (exists_valuationSubring_over (Ω := Ω) v).choose,
    fun v => (exists_valuationSubring_over (Ω := Ω) v).choose_spec⟩⟩

def emptyLayer (B : Base) (C : Cols B) (W : RowsRest B C) (χ : Chi B.toPre)
    (ldat : ∀ (p : ℕ) [Fact p.Prime], Formalism.GaloisCohomology.LData B.host.E (AlgebraicClosure B.host.E) p)
    (h : ∀ (p : ℕ) [Fact p.Prime] (e : ℕ), 0 < e → e < B.R.t → ∀ n : ℕ,
      Formalism.GaloisCohomology.shaLen (ldat p) (e : ℤ) = (n : ℕ∞) → W.shaLen p e = (n : ℚ)) :
    NData B.R B.host W.what₂ where
  Om := AlgebraicClosure B.host.E
  plOm := (nonempty_places_closure B.host.E (AlgebraicClosure B.host.E)).some
  ldat := ldat
  sha_eq := h
  Loc := Empty
  l := fun i => i.elim
  lPrime := fun i => i.elim
  j := fun i => i.elim
  j_range := fun i => i.elim
  mu := fun i => i.elim
  w := fun i => i.elim
  w_l := fun i => i.elim
  mu_w := fun i => i.elim
  w_tw := fun i => i.elim
  locs := fun _ _ => ∅
  locs_mem := fun _ _ i => i.elim
  O := fun i => i.elim
  instO := fun i => i.elim
  domO := fun i => i.elim
  dvrO := fun i => i.elim
  algO := fun i => i.elim
  finO := fun i => i.elim
  topO := fun i => i.elim
  trO := fun i => i.elim
  O_adic := fun i => i.elim
  O_complete := fun i => i.elim
  embK := fun i => i.elim
  embK_w := fun i => i.elim
  X := fun i => i.elim
  finX := fun i => i.elim
  neX := fun i => i.elim
  T := fun i => i.elim
  T_local := fun i => i.elim
  T_sep := fun i => i.elim
  Mt := fun i => i.elim
  acgMt := fun i => i.elim
  modMt := fun i => i.elim
  freeMt := fun i => i.elim
  finMt := fun i => i.elim
  act := fun i => i.elim
  act_inj := fun i => i.elim
  prMt := fun i => i.elim
  prMt_span := fun i => i.elim
  prMt_lat := fun i => i.elim
  eig_ne := fun i => i.elim
  chi := fun i => i.elim
  chi_cont := fun i => i.elim
  chi_def := fun i => i.elim
  Z := fun i => i.elim
  Zgood := fun i => i.elim
  s0 := fun i => i.elim
  restNLevelExponent_of_odd := fun i => i.elim
  restNLevelExponent_of_two := fun i => i.elim
  S := fun i => i.elim
  Q := fun i => i.elim
  SQ_split := fun i => i.elim
  SQ_disj := fun i => i.elim
  SQ_l := fun i => i.elim
  S_def := fun i => i.elim
  hT := fun i => i.elim
  T_gen := fun i => i.elim
  gam0 := fun i => i.elim
  locNd_chebotarevPlace_mem := fun i => i.elim
  restN_tameGenerator_generates := fun i => i.elim
  chi_ram_Q := fun i => i.elim
  Bj := fun i => i.elim
  acgBj := fun i => i.elim
  modBj := fun i => i.elim
  freeBj := fun i => i.elim
  finBj := fun i => i.elim
  g_split := fun k =>
    (GlobalTheory.HostSplit.split_of_one_mod B.R B.host _ (B.host.g_prime k) (B.toPre.g_cond k)).1
  PlG := fun _ => Fin B.R.f
  card_PlG := fun _ => Fintype.card_fin _
  lab := fun _ _ _ => (Polynomial.X - 1) ^ B.R.r
  lab_monic := fun k _ _ => by
    haveI : Fact (B.host.g k).Prime := ⟨B.host.g_prime k⟩
    have h1 : (Polynomial.X - 1 : Polynomial (ZMod (B.host.g k))) = Polynomial.X - Polynomial.C 1 := by simp
    rw [h1]
    exact ⟨(Polynomial.monic_X_sub_C _).pow _, by
      rw [(Polynomial.monic_X_sub_C _).natDegree_pow, Polynomial.natDegree_X_sub_C, mul_one]⟩
  chiT := χ
  restN_card_levelGroup_eq := rfl

end GlobalTheory.MemN

end
end

section

noncomputable section

namespace GlobalTheory.Mem.RowsModel

open Formalism.BasicNotions NumberField IsDedekindDomain

abbrev Euc (n : ℕ) : Type := EuclideanSpace ℂ (Fin n)

def stdOLat (O : Type) [CommRing O] (φ : O →+* ℂ) (n : ℕ) : Rows.OLat O φ (Euc n) := by
  classical
  exact
    { gen := Finset.univ.image (fun i => EuclideanSpace.basisFun (Fin n) ℂ i)
      span_top := by
        rw [Finset.coe_image, Finset.coe_univ, Set.image_univ]
        exact (EuclideanSpace.basisFun (Fin n) ℂ).toBasis.span_eq }

theorem mem_stdOLat {O : Type} [CommRing O] {φ : O →+* ℂ} {n : ℕ} {x : Euc n}
    (hx : x ∈ (stdOLat O φ n).gen) : ∃ i, EuclideanSpace.basisFun (Fin n) ℂ i = x := by
  classical
  simpa [stdOLat] using hx

def coordEmb {K : Type} [Field K] (σ : K →+* ℂ) (n : ℕ) : (Fin n → K) →ₛₗ[σ] Euc n where
  toFun x := WithLp.toLp 2 (fun i => σ (x i))
  map_add' x y := by ext i; simp
  map_smul' a x := by ext i; simp

theorem coordEmb_single {K : Type} [Field K] (σ : K →+* ℂ) (n : ℕ) (i : Fin n) :
    coordEmb σ n (Pi.single i 1) = EuclideanSpace.basisFun (Fin n) ℂ i := by
  ext j
  by_cases h : j = i
  · subst h; simp [coordEmb]
  · simp [coordEmb, h]

theorem coordEmb_basis {K : Type} [Field K] (σ : K →+* ℂ) (n : ℕ) {ι : Type}
    (b : Module.Basis ι K (Fin n → K)) :
    LinearIndependent ℂ (fun i => coordEmb σ n (b i)) ∧
      Submodule.span ℂ (Set.range (fun i => coordEmb σ n (b i))) = ⊤ := by
  classical
  letI : Fintype ι := FiniteDimensional.fintypeBasisIndex b
  have hs : ⊤ ≤ Submodule.span ℂ (Set.range (fun i => coordEmb σ n (b i))) := by
    rw [← (EuclideanSpace.basisFun (Fin n) ℂ).toBasis.span_eq, Submodule.span_le]
    rintro _ ⟨i, rfl⟩

    rw [OrthonormalBasis.coe_toBasis, ← coordEmb_single σ, ← b.sum_repr (Pi.single i 1), map_sum]
    refine Submodule.sum_mem _ fun a _ => ?_
    rw [LinearMap.map_smulₛₗ]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)
  refine ⟨linearIndependent_of_top_le_span_of_card_eq_finrank hs ?_, top_le_iff.mp hs⟩
  rw [← Module.finrank_eq_card_basis b]
  simp

theorem exists_frame {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (c : InnerProductSpace.Core ℂ V) :
    ∃ e : Euc (Module.finrank ℂ V) ≃ₗ[ℂ] V, ∀ x y, inner ℂ x y = c.inner (e x) (e y) := by
  letI : NormedAddCommGroup V := c.toNormedAddCommGroup
  letI : InnerProductSpace ℂ V := InnerProductSpace.ofCore c.toCore
  refine ⟨(stdOrthonormalBasis ℂ V).repr.symm.toLinearEquiv, fun x y => ?_⟩
  exact ((stdOrthonormalBasis ℂ V).repr.symm.inner_map_map x y).symm

variable {B : Base} (C : Cols B)

def ramCore (u : B.Word)
    (h1 : ∀ φ ∈ (C.mem u).A.Mram, ∀ ψ ∈ (C.mem u).A.Mram,
      (C.fm u).ipC 0 ψ φ = starRingEnd ℂ ((C.fm u).ipC 0 φ ψ))
    (h2 : ∀ φ ∈ (C.mem u).A.Mram, φ ≠ 0 → 0 < ((C.fm u).ipC 0 φ φ).re) :
    InnerProductSpace.Core ℂ (C.mem u).A.Mram where
  inner φ ψ := (C.fm u).ipC 0 φ.1 ψ.1
  conj_inner_symm φ ψ := (h1 ψ.1 ψ.2 φ.1 φ.2).symm
  re_inner_nonneg φ := by
    by_cases h : φ.1 = 0
    · show 0 ≤ ((C.fm u).ipC 0 φ.1 φ.1).re
      rw [h]
      simp [MemberForms.ipC]
    · exact (h2 φ.1 φ.2 h).le
  add_left φ ψ χ := by
    show (C.fm u).ipC 0 (φ.1 + ψ.1) χ.1 = _
    simp [MemberForms.ipC, mul_add, Finset.sum_add_distrib]
  smul_left φ ψ r := by
    show (C.fm u).ipC 0 (r • φ.1) ψ.1 = _
    simp [MemberForms.ipC, Finset.mul_sum, mul_left_comm]
  definite φ h := by
    by_contra hne
    have := h2 φ.1 φ.2 (fun h0 => hne (Subtype.ext h0))
    change (C.fm u).ipC 0 φ.1 φ.1 = 0 at h
    rw [h] at this
    simp at this

theorem mram_fd (u : B.Word) : FiniteDimensional ℂ (C.mem u).A.Mram := by
  have := (C.mem u).A.Mu0_fd
  exact Submodule.finiteDimensional_of_le (show (C.mem u).A.Mram ≤ (C.mem u).A.Mu0 from inf_le_left)

def eucCast {a b : ℕ} (h : a = b) : Euc a ≃ₗᵢ[ℂ] Euc b :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (finCongr h)


open Classical in
def model (n : C.Tup → ℕ) (D : ℕ)
    (e0 : ∀ u, (C.mem u).P.Mt ≃ₗ[ℂ] Euc (n C.mu0)) (eTw : ∀ u μ, (C.PTw u μ).Mt ≃ₗ[ℂ] Euc (n μ))
    (eM : ∀ u, Euc (C.mem u).A.du ≃ₗ[ℂ] (C.mem u).A.Mram)
    (heM : ∀ u φ ψ, inner ℂ φ ψ = (C.fm u).ipC 0 (eM u φ).1 (eM u ψ).1) : RowsRest B C where
  muAt _ := C.mu0
  muAt_conj _ := rfl
  muTw _ := C.mu0
  muTw_conj _ := rfl
  muAt_or _ := Or.inl rfl
  EE := Euc D
  Drows := D
  onb := EuclideanSpace.basisFun (Fin D) ℂ
  Dall := D
  delp := 0
  delp_le_one := zero_le_one
  D_eq := by simp
  EE0 := Euc D
  D0 := D
  onb0 := EuclideanSpace.basisFun (Fin D) ℂ
  FT := Unit
  ft _ := ()
  ft0 _ := ()
  Amb μ := Euc (n μ)
  Mult μ j := Euc (if j = 0 then D else n μ)
  multZero _ := eucCast (if_pos rfl)
  multTop _ := eucCast (if_neg (by have := B.R.two_le_m; omega))
  io _ _ := Matrix.toEuclideanLin (Matrix.of fun a b => if (a : ℕ) = (b : ℕ) then 1 else 0)
  Mtilde μ := stdOLat _ _ (n μ)
  eOp _ := LinearMap.id
  eOp_idem _ := rfl
  eOp_sa _ _ _ := rfl
  Mu u := Euc (C.mem u).A.du
  perCol u μ φ F :=
    if h : μ = C.mu0 then (C.mem u).P.PtilCol (eM u φ).1 ((e0 u).symm (eucCast (congrArg n h) F))
    else (C.PTw u μ).PtilCol (C.e0Tw u μ (eM u φ).1) ((eTw u μ).symm F)
  Bu _ φ F := (∑ a, φ a) * ∑ b, F b
  ze _ _ := 1
  rowsRest_wordColumnUnit_baseTuple _ := rfl
  Mj _ := Euc D
  MjLat _ := stdOLat _ _ D
  kaBig _ _ _ := 0
  kaSmall _ _ _ := 0
  Mt _ _ := Euc D
  MtLat _ _ := stdOLat _ _ D
  MtL _ _ := Fin D → B.LL
  jMt _ _ := coordEmb B.embLL D
  jMt_basis _ _ b := coordEmb_basis B.embLL D b
  MtLat_sub _ _ x hx := by
    obtain ⟨i, rfl⟩ := mem_stdOLat hx
    exact ⟨_, coordEmb_single _ _ i⟩
  eMt _ _ := LinearMap.id
  eMt_idem _ _ := rfl
  eMt_sa _ _ _ _ := rfl
  eMt_LL _ _ x := ⟨x, rfl⟩
  thetaP _ _ := LinearMap.id
  isot _ _ := ⊤
  lamP _ _ _ := 1
  Ij _ _ _ := 0
  jw _ _ _ := 0
  etaJ _ _ := 0
  etaJ_nonneg _ _ := le_rfl
  shaLen _ _ := 0
  shaLen_nonneg _ _ := le_rfl
  eMu := eM
  eMt0 := e0
  perCol_base_eq_PtilCol u φ F := by
    rw [dite_eq_left rfl]
    rfl
  Bu_linL _ F := ⟨fun φ ψ => by simp [Finset.sum_add_distrib, add_mul],
    fun a φ => by simp [← Finset.mul_sum, mul_assoc]⟩
  Bu_linR _ φ := ⟨fun F G => by simp [Finset.sum_add_distrib, mul_add],
    fun a F => by simp [← Finset.mul_sum, mul_left_comm]⟩
  eMtTw := eTw
  perCol_tie u μ h φ F := dif_neg h
  eMu_isom := heM

end GlobalTheory.Mem.RowsModel

namespace GlobalTheory.Mem


theorem RowsModel.ipC_cols (B : Base) (u : B.Word)
    (φ ψ : ((ColsModel.cols B).mem u).C.cls 0 → ((ColsModel.cols B).mem u).C.Y 0 → ℂ) :
    ((ColsModel.cols B).fm u).ipC 0 φ ψ = ∑ c, starRingEnd ℂ (φ c ()) * ψ c () := by
  refine Finset.sum_congr rfl fun c _ => ?_
  show ((Nat.card PUnit : ℕ) : ℂ)⁻¹ * (starRingEnd ℂ (φ c ()) * ψ c ()) = _
  simp


end GlobalTheory.Mem

end
end

section

noncomputable section
namespace GlobalTheory.MemN
open Formalism.BasicNotions GlobalTheory.Mem NumberField IsDedekindDomain

section
variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} [NumberField what₂.LL] [StarRing what₂.LL]
  {LL0 : IntermediateField ℚ what₂.LL} {nd : NData R H what₂} (tw : NTw R H what₂ LL0 nd)

def nexpOfEmpty [IsEmpty tw.Tw] (e : G0g nd → ↥LL0) : NExp R H what₂ LL0 nd tw where
  U := ⊥
  eLL0 := e
  Fm := fun i => isEmptyElim i
  acgFm := fun i => isEmptyElim i
  modFmK := fun i => isEmptyElim i
  modFmO := fun i => isEmptyElim i
  towFm := fun i => isEmptyElim i
  fdFm := fun i => isEmptyElim i
  actG := fun i => isEmptyElim i
  psiU := fun i => isEmptyElim i
  eAlg := fun i => isEmptyElim i
  eAlg_def := fun i => isEmptyElim i
  eAlg_idem := fun i => isEmptyElim i
  eAlg_central := fun i => isEmptyElim i
  Bsup := fun i => isEmptyElim i
  Dat := fun i => isEmptyElim i
  th := fun i => isEmptyElim i
  lev := fun i => isEmptyElim i
  thPsi := fun i => isEmptyElim i
  thPsi_one := fun i => isEmptyElim i
  thU := fun i => isEmptyElim i
  twPsi := fun i => isEmptyElim i
  twPsi_one := fun i => isEmptyElim i
  twDel := fun i => isEmptyElim i
  delU := fun i => isEmptyElim i
  delU_unr := fun i => isEmptyElim i
  delU_l := fun i => isEmptyElim i
  delU_anti := fun i => isEmptyElim i
  delU_open := fun i => isEmptyElim i
  delU_res := fun i => isEmptyElim i
  delU_conj := fun i => isEmptyElim i
  MtV := fun i => isEmptyElim i
  acgMt := fun i => isEmptyElim i
  modMtK := fun i => isEmptyElim i
  modMtO := fun i => isEmptyElim i
  towMt := fun i => isEmptyElim i
  fdMt := fun i => isEmptyElim i
  MtLat := fun i => isEmptyElim i
  MtLat_fg := fun i => isEmptyElim i
  MtLat_span := fun i => isEmptyElim i
  thP := fun i => isEmptyElim i
  hkF := fun i => isEmptyElim i
  embB := fun i => isEmptyElim i
  embB_inj := fun i => isEmptyElim i
  eH := fun i => isEmptyElim i
  eH_idem := fun i => isEmptyElim i

def nthOfEmpty [IsEmpty tw.Tw] (Y : NExp R H what₂ LL0 nd tw) : NTh R H what₂ LL0 nd tw Y where
  iC := fun i => isEmptyElim i
  iC_int := fun i => isEmptyElim i
  aL := fun i => isEmptyElim i
  aL_g := fun i => isEmptyElim i
  aL_off := fun i => isEmptyElim i
  Pt := fun i => isEmptyElim i
  ev := fun i => isEmptyElim i
  ev_smul := fun i => isEmptyElim i
  ev_inj := fun i => isEmptyElim i
  Lt := fun i => isEmptyElim i
  acgLt := fun i => isEmptyElim i
  modLt := fun i => isEmptyElim i
  freeLt := fun i => isEmptyElim i
  finLt := fun i => isEmptyElim i
  Let := fun i => isEmptyElim i
  finLet := fun i => isEmptyElim i
  Harm := fun i => isEmptyElim i
  Ctr := fun i => isEmptyElim i
  ctrC := fun i => isEmptyElim i
  Harm_def := fun i => isEmptyElim i
  thV := fun i => isEmptyElim i
  thV_add := fun i => isEmptyElim i
  thV_smul := fun i => isEmptyElim i
  thV_addP := fun i => isEmptyElim i
  thV_smulP := fun i => isEmptyElim i
  datPhi := fun i => isEmptyElim i
  datP := fun i => isEmptyElim i
  recDet := fun i => isEmptyElim i
  Kq := fun i => isEmptyElim i
  grpKq := fun i => isEmptyElim i
  actK := fun i => isEmptyElim i
  actK_one := fun i => isEmptyElim i
  actK_mul := fun i => isEmptyElim i
  recDetq := fun i => isEmptyElim i
  recDetq_mem := fun i => isEmptyElim i
  recDet_act := fun i => isEmptyElim i
  recDetq_act := fun i => isEmptyElim i
  hkIdx := fun i => isEmptyElim i
  finHk := fun i => isEmptyElim i
  hkMove := fun i => isEmptyElim i
  hkU := fun i => isEmptyElim i
  hk_ev := fun i => isEmptyElim i
  MaximalUnramifiedExtension := fun i => isEmptyElim i
  FmUr := fun i => isEmptyElim i
  FmUr_smul := fun i => isEmptyElim i
  FmUr_span := fun i => isEmptyElim i
  Bsup_def := fun i => isEmptyElim i

end

theorem exists_nexp_nth_of_isEmpty (B : Base) (C : Cols B) (W : RowsRest B C) (nd : NData B.R B.host W.what₂)
    (tw : NTw B.R B.host W.what₂ B.LL0 nd) (h : IsEmpty tw.Tw) (e : G0g nd → ↥B.LL0) :
    ∃ Y : NExp B.R B.host W.what₂ B.LL0 nd tw, Y.eLL0 = e ∧ Nonempty (NTh B.R B.host W.what₂ B.LL0 nd tw Y) :=
  ⟨nexpOfEmpty tw e, rfl, ⟨nthOfEmpty tw _⟩⟩

end GlobalTheory.MemN
end
end

section

open Formalism.BasicNotions NumberField IsDedekindDomain GlobalTheory.Mem
open Formalism.L2.Col

namespace GlobalTheory.Mem

theorem wts_ok_and_sizes :
    ∀ (B : Base) (X : PreX B.toPre), B.wts.Ok ∧ Sizes (B.primes X) B.wts X.a :=
  fun B X => ⟨B.wts_isOk, B.primes_sizes X⟩

end GlobalTheory.Mem
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Host GlobalTheory.NT GlobalTheory.Mem GlobalTheory.Mem.Fld GlobalTheory.FieldSize
open scoped IntermediateField

theorem _root_.GlobalTheory.T.rayClassField_degree_le_and_rootDiscrBound : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (φ : E →+* ℂ) (N : ℕ) (M : IntermediateField ℚ ℂ) (h : IsRayFieldIn φ (natIdeal E N) M), N ≠ 0 → degOver φ M h.emb_mem ≤ classNumber E * N ^ Module.finrank ℚ E ∧ Sz M (Real.log (Module.finrank ℚ E) + Real.log (degOver φ M h.emb_mem)) (Real.log |((discr E : ℤ) : ℝ)| / Module.finrank ℚ E + Real.log N + Real.log (degOver φ M h.emb_mem)) := by
  first | exact @GlobalTheory.Mem.Fld.RaySize.degOver_le_and_sz | exact GlobalTheory.Mem.Fld.RaySize.degOver_le_and_sz | (intros; apply GlobalTheory.Mem.Fld.RaySize.degOver_le_and_sz <;> assumption)
end
