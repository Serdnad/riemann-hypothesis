module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.LieSumDecompositions.Bundle002
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.TensorOperatorTrees.TwShift
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.Bundle004
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.Bundle007
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.LieSumDecompositions.Bundle003
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CommuteRtOfMemZalg
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConstantTermAuxiliaryStatementB
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle536
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.Bundle005
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
import Mathlib.Tactic.Cases
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

open NumberField IsDedekindDomain
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.CompanionTheory.CTFin GlobalTheory.SmGL PositivityTheory.Rg.Rs

namespace PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.TwistConcentration

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

omit [IsCMField E] in
theorem chiDet_unip {a r : ℕ} (χ : Formalism.L2.Host.HChar E) (x : BlockIx a r → Ad E) : chiDet a χ (unip x) = 1 := by
  change (χ : GlobalTheory.Mem.Chr.Ideles E →* ℂˣ) (Matrix.GeneralLinearGroup.det (unip x)) = 1
  rw [det_unip, map_one]

omit [IsCMField E] in
theorem chiDet_lev {r s : ℕ} (χ : Formalism.L2.Host.HChar E) (m : GA E r × GA E s) :
    chiDet (r + s) χ (lev (Ad E) r s m) = chiDet r χ m.1 * chiDet s χ m.2 := by
  change (χ : GlobalTheory.Mem.Chr.Ideles E →* ℂˣ) (Matrix.GeneralLinearGroup.det (lev (Ad E) r s m)) =
    (χ : GlobalTheory.Mem.Chr.Ideles E →* ℂˣ) (Matrix.GeneralLinearGroup.det m.1) *
      (χ : GlobalTheory.Mem.Chr.Ideles E →* ℂˣ) (Matrix.GeneralLinearGroup.det m.2)
  rw [← map_mul]
  congr 1
  apply Units.ext
  simp only [Units.val_mul, Matrix.GeneralLinearGroup.val_det_apply]
  have h : (lev (Ad E) r s m : Matrix (Fin (r + s)) (Fin (r + s)) (Ad E)) =
      Matrix.reindex (stdSum (rfl : r + s = r + s)) (stdSum (rfl : r + s = r + s))
        (Matrix.fromBlocks m.1.val 0 0 m.2.val) := by
    ext i j
    obtain ⟨i, rfl⟩ := (stdSum (rfl : r + s = r + s)).surjective i
    obtain ⟨j, rfl⟩ := (stdSum (rfl : r + s = r + s)).surjective j
    simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply]
    rcases i with i | i <;> rcases j with j | j <;>
      simp [lev, emb₂, leviEmb, leviTwo, two, Matrix.blockDiagonal'_apply]
  rw [h, Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁]

omit [IsCMField E] in
theorem chiDet_zero (χ : Formalism.L2.Host.HChar E) (g : GA E 0) : chiDet 0 χ g = 1 := by
  have h : Matrix.GeneralLinearGroup.det g = 1 := by
    ext
    simp [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_isEmpty]
  change (χ : GlobalTheory.Mem.Chr.Ideles E →* ℂˣ) (Matrix.GeneralLinearGroup.det g) = 1
  rw [h, map_one]

theorem mulChi_mulChi {n : ℕ} (a b : ℂ) (φ : Sm E n) :
    mulChi n (Model.absC E b) (mulChi n (Model.absC E a) φ) = mulChi n (Model.absC E (a + b)) φ := by
  refine Subtype.ext (funext fun g => ?_)
  rw [mulChi_apply, mulChi_apply, mulChi_apply, ExponentTwist.chiDet_absC_val, ExponentTwist.chiDet_absC_val,
    ExponentTwist.chiDet_absC_val, mul_assoc, ← Complex.exp_add, add_mul]

theorem tw_tw {n : ℕ} (V : Submodule ℂ (Sm E n)) (a b : ℂ) : tw (tw V a) b = tw V (a + b) := by
  unfold tw
  rw [← Submodule.map_comp]
  congr 1
  ext φ : 1
  exact mulChi_mulChi a b φ

theorem tw_zero_dim (V : Submodule ℂ (Sm E 0)) (z : ℂ) : tw V z = V := by
  have h : (mulChi 0 (Model.absC E z)).toLinearMap = LinearMap.id := by
    ext φ : 1
    refine Subtype.ext (funext fun g => ?_)
    rw [LinearEquiv.coe_coe, mulChi_apply, chiDet_zero, Units.val_one, mul_one]
    rfl
  unfold tw
  rw [h, Submodule.map_id]

theorem tw_zero' {n : ℕ} (V : Submodule ℂ (Sm E n)) : tw V 0 = V := by
  have h : (mulChi n (Model.absC E 0)).toLinearMap = LinearMap.id := by
    ext φ : 1
    refine Subtype.ext (funext fun g => ?_)
    rw [LinearEquiv.coe_coe, mulChi_apply, ExponentTwist.chiDet_absC_val, zero_mul, Complex.exp_zero, mul_one]
    rfl
  unfold tw
  rw [h, Submodule.map_id]

variable {r s : ℕ}

theorem tensor_span_mul_det_character {W₁ : Submodule ℂ (Sm E r)} {W₂ : Submodule ℂ (Sm E s)} (z : ℂ) {F : GA E r × GA E s → ℂ}
    (hF : F ∈ tens2 W₁ W₂) :
    (fun m => F m * (((chiDet r (Model.absC E z) m.1 : ℂˣ) : ℂ) * ((chiDet s (Model.absC E z) m.2 : ℂˣ) : ℂ))) ∈
      tens2 (tw W₁ z) (tw W₂ z) := by
  induction hF using Submodule.span_induction with
  | mem F hF =>
    obtain ⟨φ₁, h₁, φ₂, h₂, rfl⟩ := hF
    refine Submodule.subset_span ⟨mulChi r (Model.absC E z) φ₁, ⟨φ₁, h₁, rfl⟩, mulChi s (Model.absC E z) φ₂,
      ⟨φ₂, h₂, rfl⟩, funext fun m => ?_⟩
    simp only [mulChi_apply]
    ring
  | zero =>
    convert zero_mem (tens2 (tw W₁ z) (tw W₂ z)) using 1
    funext m
    simp
  | add F G _ _ hF hG =>
    convert add_mem hF hG using 1
    funext m
    simp [add_mul]
  | smul c F _ hF =>
    convert Submodule.smul_mem _ c hF using 1
    funext m
    simp [mul_assoc]

theorem memInd2_tw {W₁ : Submodule ℂ (Sm E r)} {W₂ : Submodule ℂ (Sm E s)} (z : ℂ) {φ : Sm E (r + s)}
    (hφ : MemInd2 W₁ W₂ φ) : MemInd2 (tw W₁ z) (tw W₂ z) (mulChi (r + s) (Model.absC E z) φ) := by
  refine ⟨fun x g => ?_, fun k g => ?_⟩
  · rw [mulChi_apply, mulChi_apply, hφ.1 x g, map_mul, chiDet_unip, one_mul]
  · set y := infGL E (r + s) (Unitary.toUnits k) * finGL E (r + s) g
    have h1 := Submodule.smul_mem _ ((chiDet (r + s) (Model.absC E z) y : ℂˣ) : ℂ) (tensor_span_mul_det_character z (hφ.2 k g))
    convert h1 using 1
    funext m
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [mulChi_apply, map_mul, chiDet_lev, Units.val_mul, Units.val_mul]
    ring

theorem memInd2_tw_iff {W₁ : Submodule ℂ (Sm E r)} {W₂ : Submodule ℂ (Sm E s)} (z : ℂ) (ψ : Sm E (r + s)) :
    (MemInd2 (tw W₁ z) (tw W₂ z) ψ ∧ ψ ∈ GlobalTheory.DiscSpec.finVec (cptRep E (r + s))) ↔
      ∃ φ, (MemInd2 W₁ W₂ φ ∧ φ ∈ GlobalTheory.DiscSpec.finVec (cptRep E (r + s))) ∧ mulChi (r + s) (Model.absC E z) φ = ψ := by
  constructor
  · rintro ⟨h, hK⟩
    refine ⟨mulChi (r + s) (Model.absC E (-z)) ψ, ⟨?_, Trees.mulChi_mem_finVec _ hK⟩, ParabolicProjection.mulChi_absC_neg' _ z ψ⟩
    have h2 := memInd2_tw (-z) h
    rwa [tw_tw, tw_tw, add_neg_cancel, tw_zero', tw_zero'] at h2
  · rintro ⟨φ, ⟨hφ, hK⟩, rfl⟩
    exact ⟨memInd2_tw z hφ, Trees.mulChi_mem_finVec _ hK⟩

theorem span_memInd2_tw (W₁ : Submodule ℂ (Sm E r)) (W₂ : Submodule ℂ (Sm E s)) (z : ℂ) :
    Submodule.span ℂ {φ | MemInd2 (tw W₁ z) (tw W₂ z) φ ∧ φ ∈ GlobalTheory.DiscSpec.finVec (cptRep E (r + s))} =
      tw (Submodule.span ℂ {φ | MemInd2 W₁ W₂ φ ∧ φ ∈ GlobalTheory.DiscSpec.finVec (cptRep E (r + s))}) z := by
  rw [show tw (Submodule.span ℂ {φ | MemInd2 W₁ W₂ φ ∧ φ ∈ GlobalTheory.DiscSpec.finVec (cptRep E (r + s))}) z =
    (Submodule.span ℂ {φ | MemInd2 W₁ W₂ φ ∧ φ ∈ GlobalTheory.DiscSpec.finVec (cptRep E (r + s))}).map
      (mulChi (r + s) (Model.absC E z)).toLinearMap from rfl,
    Submodule.map_span]
  congr 1
  ext ψ
  exact memInd2_tw_iff z ψ

def twT (z : ℂ) : {N : ℕ} → Tr E N → Tr E N
  | M, .leaf V w => .leaf V (if M = 0 then w else w + z)
  | _, .node t₁ t₂ => .node (twT z t₁) (twT z t₂)

theorem space_twT (z : ℂ) {N : ℕ} (t : Tr E N) : (twT z t).space = tw t.space z := by
  induction t with
  | @leaf M V w =>
    by_cases hM : M = 0
    · subst hM
      simp only [twT, Tr.space, tw_zero_dim]
    · simp only [twT, if_neg hM, Tr.space]
      rw [tw_tw]
  | @node r s t₁ t₂ ih₁ ih₂ =>
    simp only [twT, Tr.space]
    rw [ih₁, ih₂, tw_tw, tw_tw, add_comm z, add_comm z, ← tw_tw _ _ z, ← tw_tw _ _ z, span_memInd2_tw]

theorem good_twT {z : ℂ} (hz : z.re = 0) {N : ℕ} (t : Tr E N) (ht : t.Good) : (twT z t).Good := by
  induction t with
  | @leaf M V w =>
    rcases ht with ⟨hM, hV, hw⟩ | ⟨hM, hV, hw⟩
    · subst hM
      simp only [twT]
      exact Or.inl ⟨rfl, hV, hw⟩
    · simp only [twT, if_neg hM.ne']
      exact Or.inr ⟨hM, hV, by rw [Complex.add_re, hw, hz, add_zero]⟩
  | @node r s t₁ t₂ ih₁ ih₂ =>
    exact ⟨ih₁ ht.1, ih₂ ht.2⟩

theorem pos_twT (z : ℂ) {N : ℕ} (t : Tr E N) (ht : t.AllLeaves (fun M _ => 0 < M)) :
    (twT z t).AllLeaves (fun M _ => 0 < M) := by
  induction t with
  | @leaf M V w => exact ht
  | @node r s t₁ t₂ ih₁ ih₂ => exact ⟨ih₁ ht.1, ih₂ ht.2⟩

end PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.TwistConcentration

namespace PositivityTheory.Rg.BcB.SpectralAccumulation.Cz

open TwistConcentration in
theorem twConc_holds : TwConc := by
  intro E _ _ _ N U z hz hU φ _ hc
  obtain ⟨t, T, ht, hpos, hTe, hTm, hT0⟩ := hc
  refine ⟨twT z t, ParabolicProjection.twMap N z T, good_twT hz t ht, pos_twT z t hpos, ParabolicProjection.twMap_equiv hU.1 hTe, fun ψ hψ => ?_, ?_⟩
  · rw [space_twT]
    exact ParabolicProjection.twMap_mem hTm ψ hψ
  · rw [ParabolicProjection.twMap_apply, ParabolicProjection.mulChi_absC_neg]
    exact (LinearEquiv.map_ne_zero_iff _).2 hT0

end PositivityTheory.Rg.BcB.SpectralAccumulation.Cz
end
end

section

noncomputable section

open NumberField IsDedekindDomain
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs

namespace PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.KTypeSlices

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

section KAux

def k_castGL {R : Type} [CommRing R] {a b : ℕ} (h : a = b) (g : GL (Fin a) R) : GL (Fin b) R := h ▸ g

omit [Field E] [NumberField E] [IsCMField E] in
theorem k_castGL_apply {R : Type} [CommRing R] {a b : ℕ} (h : a = b) (g : GL (Fin a) R) (i j : Fin b) :
    (k_castGL h g : Matrix (Fin b) (Fin b) R) i j = (g : Matrix (Fin a) (Fin a) R) (Fin.cast h.symm i) (Fin.cast h.symm j) := by
  subst h; rfl

omit [Field E] [NumberField E] [IsCMField E] in
theorem k_castGL_castGL {R : Type} [CommRing R] {a b : ℕ} (h : a = b) (g : GL (Fin a) R) :
    k_castGL h.symm (k_castGL h g) = g := by
  subst h; rfl

omit [Field E] [NumberField E] [IsCMField E] in
theorem levi_embed_left_zero {R : Type} [CommRing R] {r : ℕ} (g : GL (Fin r) R) : lev R r 0 (g, 1) = g := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  exact InducedTensorMap.B.lev_cc (s := 0) (g, 1) i j

omit [Field E] [NumberField E] [IsCMField E] in
theorem k_lev_0s {R : Type} [CommRing R] {s : ℕ} (u : GL (Fin s) R) :
    lev R 0 s (1, u) = k_castGL (Nat.zero_add s).symm u := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  obtain ⟨i', rfl⟩ : ∃ i' : Fin s, i = Fin.natAdd 0 i' := ⟨Fin.cast (Nat.zero_add s) i, Fin.ext (by simp)⟩
  obtain ⟨j', rfl⟩ : ∃ j' : Fin s, j = Fin.natAdd 0 j' := ⟨Fin.cast (Nat.zero_add s) j, Fin.ext (by simp)⟩
  rw [InducedTensorMap.B.lev_nn (r := 0) (1, u) i' j', k_castGL_apply]
  have e : ∀ x : Fin s, Fin.cast (Nat.zero_add s).symm.symm (Fin.natAdd 0 x) = x := fun x => Fin.ext (by simp)
  rw [e, e]

omit [IsCMField E] in
theorem k_mem_cast {F : ∀ n : ℕ, Subgroup (GL (Fin n) (Af E))} {a b : ℕ} (h : a = b) {u : GL (Fin a) (Af E)}
    (hu : u ∈ F a) : k_castGL h u ∈ F b := by
  subst h; exact hu

omit [Field E] [NumberField E] [IsCMField E] in
theorem k_isOpen_inf {G : Type} [Group G] [TopologicalSpace G] {H H' : Subgroup G} (h : IsOpen (H : Set G))
    (h' : IsOpen (H' : Set G)) : IsOpen ((H ⊓ H' : Subgroup G) : Set G) := by
  rw [Subgroup.coe_inf]; exact h.inter h'

omit [Field E] [NumberField E] [IsCMField E] in
theorem k_isOpen_iInf {G : Type} [Group G] [TopologicalSpace G] {ι : Sort*} [Finite ι] {H : ι → Subgroup G}
    (h : ∀ i, IsOpen (H i : Set G)) : IsOpen ((⨅ i, H i : Subgroup G) : Set G) := by
  rw [Subgroup.coe_iInf]; exact isOpen_iInter_of_finite h

end KAux


open Classical in
def Tset (r s : ℕ) (L : Subgroup (GL (Fin (r + s)) (Af E))) : Finset (GL (Fin (r + s)) (Af E)) :=
  if r = 0 ∨ s = 0 then {1} else if h : IsOpen (L : Set (GL (Fin (r + s)) (Af E))) then
    Classical.choose (IwaAd.iwasawa_finite_cosets E r s L h) else ∅

theorem Tset_spec {r s : ℕ} {L : Subgroup (GL (Fin (r + s)) (Af E))} (hL : IsOpen (L : Set (GL (Fin (r + s)) (Af E))))
    (g : GA E (r + s)) : ∃ (x : BlockIx (r + s) r → Ad E) (m : GA E r × GA E s) (t : GL (Fin (r + s)) (Af E))
      (k : Kinf E (r + s)) (l : GL (Fin (r + s)) (Af E)), t ∈ Tset r s L ∧ l ∈ L ∧
      g = unip x * lev (Ad E) r s m * finGL E (r + s) t * infGL E (r + s) (Unitary.toUnits k) * finGL E (r + s) l := by
  by_cases hr : r = 0 ∨ s = 0
  · have hT : Tset r s L = {1} := by rw [Tset, if_pos hr]
    rcases hr with rfl | rfl
    · refine ⟨0, (1, k_castGL (Nat.zero_add s) g), 1, 1, 1, by rw [hT]; exact Finset.mem_singleton_self _, L.one_mem, ?_⟩
      rw [InducedTensorMap.unip_zero, k_lev_0s, k_castGL_castGL, map_one, map_one, map_one]
      simp
    · refine ⟨0, (g, 1), 1, 1, 1, by rw [hT]; exact Finset.mem_singleton_self _, L.one_mem, ?_⟩
      rw [InducedTensorMap.unip_zero, levi_embed_left_zero, map_one, map_one, map_one]
      simp
  · have hT : Tset r s L = Classical.choose (IwaAd.iwasawa_finite_cosets E r s L hL) := by
      rw [Tset, if_neg hr, dite_eq_left hL]
    rw [hT]
    exact Classical.choose_spec (IwaAd.iwasawa_finite_cosets E r s L hL) g

def topK (N : ℕ) (K : Subgroup (GL (Fin N) (Af E))) (n : ℕ) : Subgroup (GL (Fin n) (Af E)) :=
  if h : n = N then h ▸ K else ⊤

def Kf (N : ℕ) (K : Subgroup (GL (Fin N) (Af E))) (n : ℕ) : Subgroup (GL (Fin n) (Af E)) :=
  topK N K n ⊓ detKer n ⊓
    (⨅ (s : Fin (N + 1)) (_ : 0 < (s : ℕ) ∧ n + s ≤ N),
      ⨅ t : {t // t ∈ Tset n s (Kf N K (n + s))}, Slice1.levelOne s (Kf N K (n + s)) t.1) ⊓
    (⨅ (s : Fin (N + 1)) (_ : 0 < (s : ℕ) ∧ (s : ℕ) + n ≤ N),
      ⨅ t : {t // t ∈ Tset s n (Kf N K (s + n))}, Slice2.L₂ s (Kf N K (s + n)) t.1)
termination_by N - n
decreasing_by all_goals omega

variable {N : ℕ} {K : Subgroup (GL (Fin N) (Af E))}

theorem isOpen_Kf (hK : IsOpen (K : Set (GL (Fin N) (Af E)))) (n : ℕ) :
    IsOpen (Kf N K n : Set (GL (Fin n) (Af E))) := by
  induction' hd : N - n using Nat.strong_induction_on with d ih generalizing n
  rw [Kf]
  refine k_isOpen_inf (k_isOpen_inf (k_isOpen_inf ?_ (isOpen_detKer n)) ?_) ?_
  · unfold topK
    split_ifs with h
    · subst h; exact hK
    · rw [Subgroup.coe_top]; exact isOpen_univ
  · refine k_isOpen_iInf fun s' => k_isOpen_iInf fun hs => k_isOpen_iInf fun t => ?_
    exact Slice1.isOpen_levelOne (ih _ (by omega) _ rfl) _
  · refine k_isOpen_iInf fun s' => k_isOpen_iInf fun hs => k_isOpen_iInf fun t => ?_
    exact Slice2.isOpen_L₂ (ih _ (by omega) _ rfl) _

theorem Kf_le_det (n : ℕ) : Kf N K n ≤ detKer n := by
  rw [Kf]
  exact inf_le_left.trans (inf_le_left.trans inf_le_right)

theorem Kf_top : Kf N K N ≤ K := by
  intro u hu
  rw [Kf] at hu
  have h := hu.1.1.1
  unfold topK at h
  rw [dite_eq_left rfl] at h
  exact h

theorem Kf_left {r s : ℕ} (hN : r + s ≤ N) {t : GL (Fin (r + s)) (Af E)} (ht : t ∈ Tset r s (Kf N K (r + s)))
    {u : GL (Fin r) (Af E)} (hu : u ∈ Kf N K r) : t⁻¹ * lev (Af E) r s (u, 1) * t ∈ Kf N K (r + s) := by
  rcases Nat.eq_zero_or_pos s with rfl | hs
  · have hT : Tset r 0 (Kf N K (r + 0)) = {1} := by rw [Tset, if_pos (Or.inr rfl)]
    rw [hT, Finset.mem_singleton] at ht
    subst ht
    rw [inv_one, one_mul, mul_one, levi_embed_left_zero]
    exact hu
  · rw [Kf] at hu
    have h := (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 hu).1).2
    rw [Subgroup.mem_iInf] at h
    have h2 := h ⟨s, by omega⟩
    rw [Subgroup.mem_iInf] at h2
    have h3 := h2 ⟨hs, hN⟩
    rw [Subgroup.mem_iInf] at h3
    exact Slice1.mem_levelOne.1 (h3 ⟨t, ht⟩)

theorem Kf_right {r s : ℕ} (hN : r + s ≤ N) {t : GL (Fin (r + s)) (Af E)} (ht : t ∈ Tset r s (Kf N K (r + s)))
    {u : GL (Fin s) (Af E)} (hu : u ∈ Kf N K s) : t⁻¹ * lev (Af E) r s (1, u) * t ∈ Kf N K (r + s) := by
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · have hT : Tset 0 s (Kf N K (0 + s)) = {1} := by rw [Tset, if_pos (Or.inl rfl)]
    rw [hT, Finset.mem_singleton] at ht
    subst ht
    rw [inv_one, one_mul, mul_one, k_lev_0s]
    exact k_mem_cast (F := Kf N K) (Nat.zero_add s).symm hu
  · rw [Kf] at hu
    have h := (Subgroup.mem_inf.1 hu).2
    rw [Subgroup.mem_iInf] at h
    have h2 := h ⟨r, by omega⟩
    rw [Subgroup.mem_iInf] at h2
    have h3 := h2 ⟨hr, hN⟩
    rw [Subgroup.mem_iInf] at h3
    have h4 := h3 ⟨t, ht⟩
    simpa [Slice2.L₂, Slice2.lev2, MulAut.conj_apply] using h4

end PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.KTypeSlices

end
end
