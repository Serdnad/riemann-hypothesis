module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle015
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ContinuousCycMod
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FirstHalfLocalCohomologyVanishingOfLocalDualityT
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle016
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.Bundle003
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RowParamOfThetaLiftBaseChange
import Mathlib.Algebra.AffineMonoid.UniqueSums
public import Formalism.SharpRestriction.LevelLetterCocycles.EndomorphismIndexBound
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsAlgebraMapEqRoot
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle286
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle236
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsAuxiliaryHeckeCharacter
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle344
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle245
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle008

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel

theorem _root_.GlobalTheory.T.firstHalfLocalCohomologyVanishing_of_localDualityTheorems : LocalFiniteness → LocalTateDuality → LocalEulerChar → TameLocal → ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X) (i : X.Tw) (s : X.Sig i), GalHyp bkP i s → FirstHalf i s := by
  first | exact @GlobalTheory.ScalarFrob.firstHalf | exact GlobalTheory.ScalarFrob.firstHalf | (intros; apply GlobalTheory.ScalarFrob.firstHalf <;> assumption)
end

section

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.L2 NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module Polynomial GlobalTheory.Pass GlobalTheory.PendOf

noncomputable section

namespace GlobalTheory.ParOfPoint

theorem inePol_foldr (D : D7) {w : PlE D.host} (x : D.naut.LP w) {α : Type} (c : α → ℝ) (l : List α)
    (σ : GE D.nd) (hσ : σ ∈ Ine (F := D.host.E) (D.nd.plOm.1 w)) :
    D.naut.inePol (l.foldr (fun k acc => D.naut.lpSum (D.naut.lpTw x (c k)) acc) (D.naut.lpZero w)) σ =
      D.naut.inePol x σ ^ l.length := by
  induction l with
  | nil =>
    have h := ((D.naut.unr_iff_ine (D.naut.lpZero w)).1 (D.naut.lpZero_unr w)).2 σ hσ
    rw [D.naut.lpDim_zero, pow_zero] at h
    simpa using h
  | cons k l ih =>
    simp only [List.foldr_cons, List.length_cons]
    rw [D.naut.inePol_sum, D.naut.inePol_tw _ _ σ hσ, ih, pow_succ, mul_comm]

theorem inePol_twistIso (D : D7) (hT : SumRepresentations.At.TieLP D.nd D.naut) (L : List (Part D.naut.CG)) (w : PlE D.host)
    (σ : GE D.nd) (hσ : σ ∈ Ine (F := D.host.E) (D.nd.plOm.1 w)) :
    D.naut.inePol (isoLoc D.nd D.naut (twistIso D.nd D.naut L D.naut.etaTinv) w) σ =
      D.naut.inePol (isoLoc D.nd D.naut L w) σ := by
  have hd : D.naut.lpDim (D.naut.locG D.naut.etaTinv w) = 1 := D.naut.locG_dim _ w
  have hu : D.naut.inePol (D.naut.locG D.naut.etaTinv w) σ = X - C 1 := by
    have h := ((D.naut.unr_iff_ine _).1 (D.naut.etaTinv_def w).1).2 σ hσ
    rw [hd, pow_one] at h
    rw [h, map_one]
  have hpart : ∀ {a : ℕ} (π : D.naut.CG a),
      D.naut.inePol (D.naut.locG (D.naut.tw π D.naut.etaTinv) w) σ = D.naut.inePol (D.naut.locG π w) σ := by
    intro a π
    rw [D.naut.locG_tw, ((hT w (D.naut.locG π w) (D.naut.locG π w) _ _ 0 hd hd).2.2.2.2.2 σ hσ).2 1 hu,
      Polynomial.scaleRoots_one]
  induction L with
  | nil => rfl
  | cons p L ih =>
    show D.naut.inePol (D.naut.lpSum (spehLoc D.nd D.naut ⟨p.a, D.naut.tw p.π D.naut.etaTinv, p.d⟩ w)
      (isoLoc D.nd D.naut (twistIso D.nd D.naut L D.naut.etaTinv) w)) σ =
      D.naut.inePol (D.naut.lpSum (spehLoc D.nd D.naut p w) (isoLoc D.nd D.naut L w)) σ
    rw [D.naut.inePol_sum, D.naut.inePol_sum, ih]
    unfold spehLoc
    rw [inePol_foldr D _ _ _ σ hσ, inePol_foldr D _ _ _ σ hσ, hpart]

theorem eq_pow_of_mul_eq (A B : ℂ[X]) (n : ℕ) (hA : A.Monic) (hB : B.Monic) (h : A * B = (X - 1) ^ n) :
    A = (X - 1) ^ A.natDegree := by
  have hdvd : A ∣ (X - C 1) ^ n := by rw [map_one, ← h]; exact dvd_mul_right A B
  obtain ⟨j, -, hj⟩ := (dvd_prime_pow (Polynomial.prime_X_sub_C (1 : ℂ)) n).1 hdvd
  have e := Polynomial.eq_of_monic_of_associated hA ((monic_X_sub_C (1 : ℂ)).pow j) hj
  rw [e, (monic_X_sub_C (1 : ℂ)).natDegree_pow, natDegree_X_sub_C, mul_one, map_one]

theorem tw_back (D : D7) (hT : SumRepresentations.At.TieLP D.nd D.naut)
    (hAN : ∀ Pa Pa' : List (Part D.naut.CG), (∀ p ∈ Pa, 1 ≤ p.a ∧ p.d = 1) → (∀ p ∈ Pa', 1 ≤ p.a ∧ p.d = 1) →
      (∀ᶠ w in Filter.cofinite, isoLoc D.nd D.naut Pa w = isoLoc D.nd D.naut Pa' w) → Pa.Perm Pa')
    {a : ℕ} (ha : 1 ≤ a) (π : D.naut.CG a) : D.naut.tw (D.naut.tw π D.naut.etaTinv) D.naut.etaT = π := by
  have hsing : ∀ (π' : D.naut.CG a) w, isoLoc D.nd D.naut [⟨a, π', 1⟩] w = D.naut.locG π' w := by
    intro π' w
    show D.naut.lpSum (spehLoc D.nd D.naut ⟨a, π', 1⟩ w) (D.naut.lpZero w) = _
    rw [D.naut.lpSum_zero]
    unfold spehLoc
    simp [D.naut.lpSum_zero, D.naut.lpTw_zero]
  have h := hAN [⟨a, D.naut.tw (D.naut.tw π D.naut.etaTinv) D.naut.etaT, 1⟩] [⟨a, π, 1⟩]
    (by simp [ha]) (by simp [ha]) (Filter.Eventually.of_forall fun w => by
      rw [hsing, hsing, D.naut.locG_tw, D.naut.locG_tw]
      exact (GlobalTheory.RowThetaParam.lpChar_eta_inv D.nd D.naut hT _).2)
  rw [List.singleton_perm_singleton] at h
  injection h with _ h2

theorem main : ∀ D : D7, (∀ S : Formalism.L2.ParC D, ∃ σ' : D.ntypes.Par, ∀ w, D.ntypes.locPar σ' w = isoLoc D.nd D.naut S.1 w) → SumRepresentations.tie0 D → SumRepresentations.adm5 D → (∀ (k : Fin 2) (v : D.nd.PlG k), IsSplitPl D.host (D.naut.plGw k v)) → LabDepth D → DepthZ D → ParSurj D := by
  intro D hPar h0 h5 hsplit hLab hDZ i x Sig hX
  obtain ⟨P, -, hB⟩ := hX
  have hT : SumRepresentations.At.TieLP D.nd D.naut := h0.1
  have hAN := h5.1
  set χ := D.naut.etaTinv with hχ
  have htw : twistIso D.nd D.naut (Sig ++ [muPart D.nd D.naut i]) χ =
      twistIso D.nd D.naut Sig χ ++ twistIso D.nd D.naut [muPart D.nd D.naut i] χ := List.map_append

  have hparts : ∀ p ∈ Sig, 1 ≤ p.a ∧ 1 ≤ p.d ∧ D.naut.csd p.π := by
    intro p hp
    have hm : (⟨p.a, D.naut.tw p.π χ, p.d⟩ : Part D.naut.CG) ∈
        twistIso D.nd D.naut (Sig ++ [muPart D.nd D.naut i]) χ := by
      rw [htw]
      exact List.mem_append_left _ (List.mem_map.2 ⟨p, hp, rfl⟩)
    obtain ⟨ha, hd, hc⟩ := hB.1 _ hm
    refine ⟨ha, hd, ?_⟩
    have e := tw_back D hT hAN ha p.π
    rw [← e]
    exact D.naut.csd_tw _ _ h0.2.1.1.1 hc

  have hnodup : (Sig.map fun p => ((⟨p.a, p.π⟩ : Σ a, D.naut.CG a), p.d)).Nodup := by
    have h2 := hB.2.1
    rw [htw, List.map_append] at h2
    have h3 := (List.nodup_append.1 h2).1
    have e : (twistIso D.nd D.naut Sig χ).map (fun p => ((⟨p.a, p.π⟩ : Σ a, D.naut.CG a), p.d)) =
        (Sig.map fun p => ((⟨p.a, p.π⟩ : Σ a, D.naut.CG a), p.d)).map
          (fun q => ((⟨q.1.1, D.naut.tw q.1.2 χ⟩ : Σ a, D.naut.CG a), q.2)) := by
      unfold twistIso
      rw [List.map_map, List.map_map]
      rfl
    rw [e] at h3
    exact h3.of_map _

  have hrank : rankIso D.nd D.naut Sig = D.R.r := by
    have hr := hB.2.2.1
    have e1 : rankIso D.nd D.naut (twistIso D.nd D.naut (Sig ++ [muPart D.nd D.naut i]) χ) =
        rankIso D.nd D.naut (Sig ++ [muPart D.nd D.naut i]) := by
      unfold rankIso twistIso
      rw [List.map_map]
      rfl
    rw [e1] at hr
    unfold rankIso at hr ⊢
    rw [List.map_append, List.sum_append] at hr
    simp only [muPart, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, one_mul, add_zero] at hr
    have : D.R.nV = D.R.r + D.R.t := rfl
    omega

  have hlab : ∀ (k : Fin 2) (v : D.nd.PlG k),
      (D.naut.items₂ k (D.naut.plGw k v) (isoLoc D.nd D.naut Sig (D.naut.plGw k v))).Monic ∧
      (D.naut.items₂ k (D.naut.plGw k v) (isoLoc D.nd D.naut Sig (D.naut.plGw k v))).natDegree = D.R.r := by
    intro k v
    set w := D.naut.plGw k v with hw
    have hover := D.naut.plGw_over k v
    obtain ⟨hmon, hiff⟩ := hLab k w hover (isoLoc D.nd D.naut Sig w)
    refine ⟨hmon, ?_⟩
    rw [← hrank, ← lpDim_isoLoc]
    apply hiff.2
    intro σ hσ hwild
    have hloc := hB.2.2.2.1 w (hsplit k v)
    have htame := hDZ i P k w hover σ hσ hwild
    rw [← hloc, inePol_twistIso D hT _ w σ hσ, GlobalTheory.RowThetaParam.isoLoc_append, D.naut.inePol_sum] at htame
    have hd1 : D.naut.lpDim (D.naut.locG D.naut.etaT w) = 1 := D.naut.locG_dim _ w
    have hm1 := ((hT w (isoLoc D.nd D.naut Sig w) (isoLoc D.nd D.naut Sig w) _ _ 0 hd1 hd1).2.2.2.2.2 σ hσ).1
    have hm2 := ((hT w (isoLoc D.nd D.naut [muPart D.nd D.naut i] w)
      (isoLoc D.nd D.naut [muPart D.nd D.naut i] w) _ _ 0 hd1 hd1).2.2.2.2.2 σ hσ).1
    have e := eq_pow_of_mul_eq _ _ _ hm1.1 hm2.1 htame
    rw [e, hm1.2]
  exact hPar ⟨Sig, hparts, hnodup, hrank, hlab⟩

end GlobalTheory.ParOfPoint
end
end

section

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.L2 NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module Polynomial GlobalTheory.Pass GlobalTheory.PendOf Formalism.MainNotions.PairedCharacterCondition
open scoped TensorProduct

namespace GlobalTheory.PendOf.CenKey

theorem stable (D : D7) (i : D.nd.Loc) (h : OnMtPreservesTypeV D) (c : MonoidAlgebra ℂ (G0g D.nd))
    (s : Set (D.naut.AV i)) (F : D.what₂.Mt (D.nd.mu i) (D.nd.j i))
    (hF : F ∈ ⨆ P ∈ s, D.naut.typeV i P) :
    D.ntypes.onMt (D.nd.mu i) (D.nd.j i) c F ∈ ⨆ P ∈ s, D.naut.typeV i P := by
  have : (⨆ P ∈ s, D.naut.typeV i P) ≤
      (⨆ P ∈ s, D.naut.typeV i P).comap (D.ntypes.onMt (D.nd.mu i) (D.nd.j i) c) := by
    refine iSup₂_le fun P hP G hG => ?_
    exact le_biSup (D.naut.typeV i) hP (h i P c G hG)
  exact this hF

theorem phi_mem (D : D7) (i : D.nd.Loc) (S : Sec D i)
    (u : TensorProduct (D.nd.O i) (KK D.nd i) (D.nd.Mt i)) :
    S.Φ u ∈ ⨆ P ∈ {P | D.naut.ptV i P ≠ none}, D.naut.typeV i P := by
  have hu : u ∈ ⨆ x, heckeEig (D.nd.T i) (D.nd.act i) x := by
    rw [Formalism.MainNotions.TruncatedSeriesCountingIdentities.Br.EigSpan_holds D.nd i]; exact Submodule.mem_top
  induction hu using Submodule.iSup_induction' with
  | mem x u hu =>
    have hle : typeSum D i (some x) ≤ ⨆ P ∈ {P | D.naut.ptV i P ≠ none}, D.naut.typeV i P := by
      refine iSup₂_le fun P hP => ?_
      have hP' : D.naut.ptV i P = some x := hP
      exact le_biSup (D.naut.typeV i)
        (show P ∈ {P | D.naut.ptV i P ≠ none} from by simp [hP'])
    exact hle (S.eig x u hu)
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add a b _ _ ha hb => rw [map_add (f := _)]; exact Submodule.add_mem _ ha hb

theorem phi_onMt : ∀ (D : D7) (i : D.nd.Loc) (S : Sec D i), OnMtPreservesTypeV D →
    ∀ (c : MonoidAlgebra ℂ (G0g D.nd)) (x y : D.what₂.MtL (D.nd.mu i) (D.nd.j i)),
    D.what₂.jMt _ _ y = D.ntypes.onMt (D.nd.mu i) (D.nd.j i) c (D.what₂.jMt _ _ x) →
    S.Φ (D.nd.prMt i y) = D.ntypes.onMt (D.nd.mu i) (D.nd.j i) c (S.Φ (D.nd.prMt i x)) := by
  intro D i S h c x y hxy
  have hd : Disjoint (⨆ P ∈ {P | D.naut.ptV i P ≠ none}, D.naut.typeV i P)
      (⨆ P ∈ {P | D.naut.ptV i P = none}, D.naut.typeV i P) :=
    (D.naut.typeV_indep i).disjoint_biSup_biSup
      (Set.disjoint_left.2 fun P h1 h2 => h1 h2)
  have h1 := Submodule.sub_mem _ (phi_mem D i S (D.nd.prMt i y))
    (stable D i h c _ _ (phi_mem D i S (D.nd.prMt i x)))
  have h2 := Submodule.sub_mem _ (stable D i h c {P | D.naut.ptV i P = none} _ (S.split x)) (S.split y)
  have e : D.ntypes.onMt (D.nd.mu i) (D.nd.j i) c (D.what₂.jMt _ _ x - S.Φ (D.nd.prMt i x)) -
      (D.what₂.jMt _ _ y - S.Φ (D.nd.prMt i y)) =
      S.Φ (D.nd.prMt i y) - D.ntypes.onMt (D.nd.mu i) (D.nd.j i) c (S.Φ (D.nd.prMt i x)) := by
    rw [map_sub, hxy]; abel
  rw [e] at h2
  exact sub_eq_zero.1 (Submodule.disjoint_def.1 hd _ h1 h2)

end GlobalTheory.PendOf.CenKey
end

section

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.L2 NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module Polynomial GlobalTheory.Pass GlobalTheory.PendOf

noncomputable section

namespace GlobalTheory.PendOf.PrTypeProof

theorem typeSum_indep (D : D7) (i : D.nd.Loc) : iSupIndep (typeSum D i) := by
  intro o
  have hd : Disjoint {P | D.naut.ptV i P = o} {P | D.naut.ptV i P ≠ o} :=
    Set.disjoint_left.2 fun P h h' => h' h
  refine ((D.naut.typeV_indep i).disjoint_biSup_biSup hd).mono_right ?_
  refine iSup₂_le fun o' ho' => iSup₂_le fun P hP => ?_
  exact le_biSup (D.naut.typeV i) (show P ∈ {P | D.naut.ptV i P ≠ o} from fun e => ho' (hP.symm.trans e))

theorem typeV_le_typeSum (D : D7) (i : D.nd.Loc) (P : D.naut.AV i) :
    D.naut.typeV i P ≤ typeSum D i (D.naut.ptV i P) :=
  le_biSup (D.naut.typeV i) (show P ∈ {Q | D.naut.ptV i Q = D.naut.ptV i P} from rfl)

theorem main : ∀ D : D7, (∀ i, Nonempty (Sec D i)) → PrType D := by
  intro D hS i PI x hx
  classical
  let s := (hS i).some
  set v := D.nd.prMt i x with hvdef
  have hvtop : v ∈ ⨆ y, heckeEig (D.nd.T i) (D.nd.act i) y := by
    rw [Formalism.MainNotions.TruncatedSeriesCountingIdentities.Br.EigSpan_holds D.nd i]; exact Submodule.mem_top
  obtain ⟨f, hf, hsum⟩ := (Submodule.mem_iSup_iff_exists_finsupp _ v).1 hvtop
  have hΦv : s.Φ v = ∑ y ∈ f.support, s.Φ (f y) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← hsum, Finsupp.sum, map_sum]
  have hn := s.split x
  have hind := typeSum_indep D i
  have hjx : D.what₂.jMt _ _ x ∈ typeSum D i (D.naut.ptV i PI) := typeV_le_typeSum D i PI hx
  have key : ∀ y, some y ≠ D.naut.ptV i PI → f y = 0 := by
    intro y hy
    by_cases hs : y ∈ f.support
    · have e : s.Φ (f y) = (D.what₂.jMt _ _ x - (D.what₂.jMt _ _ x - s.Φ v)) -
          ∑ y' ∈ f.support.erase y, s.Φ (f y') := by
        rw [sub_sub_cancel, hΦv, ← Finset.add_sum_erase _ _ hs, add_sub_cancel_right]
      have m2 : s.Φ (f y) ∈ ⨆ (o) (_ : o ≠ some y), typeSum D i o := by
        rw [e]
        refine Submodule.sub_mem _ (Submodule.sub_mem _ ?_ ?_) (Submodule.sum_mem _ fun y' hy' => ?_)
        · exact Submodule.mem_iSup_of_mem _ (Submodule.mem_iSup_of_mem (Ne.symm hy) hjx)
        · exact Submodule.mem_iSup_of_mem none (Submodule.mem_iSup_of_mem (by simp) hn)
        · refine Submodule.mem_iSup_of_mem (some y') (Submodule.mem_iSup_of_mem ?_ (s.eig y' _ (hf y')))
          exact fun e' => Finset.ne_of_mem_erase hy' (Option.some_injective _ e')
      have h0 : s.Φ (f y) = 0 := (Submodule.disjoint_def.1 (hind (some y))) _ (s.eig y _ (hf y)) m2
      exact s.inj (h0.trans (map_zero s.Φ).symm)
    · exact Finsupp.notMem_support_iff.1 hs
  refine ⟨fun p hp => ?_, fun hp => ?_⟩
  · rw [← hsum, Finsupp.sum]
    refine Submodule.sum_mem _ fun y _ => ?_
    by_cases hyp : y = p
    · subst hyp; exact hf y
    · rw [key y (by rw [hp]; exact fun e => hyp (Option.some_injective _ e))]
      exact Submodule.zero_mem _
  · rw [← hsum, Finsupp.sum]
    exact Finset.sum_eq_zero fun y _ => key y (by rw [hp]; simp)

end GlobalTheory.PendOf.PrTypeProof

end
end

section

open PowerSeries GlobalTheory.BK

namespace GlobalTheory.BK.MonIntegral

variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K]
  [IsUnitBall O K] {l e a : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
  [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a]
  {η H : ℕ} (D : BKDat O K l e a ι η H)

omit [CompleteSpace K] in
theorem pow_smul_mem (W : Submodule O D.Pol) (n : ℕ) {w : D.Pol} (hw : w ∈ W) : (l : K) ^ n • w ∈ W := by
  rw [← Nat.cast_pow, Nat.cast_smul_eq_nsmul]
  exact nsmul_mem hw _


omit [CompleteSpace K] [NeZero e] in
theorem E_smul_mem_EM {p : Vec K a ι} (hp : p ∈ D.L) : E K l e • p ∈ D.EM η := by
  rw [mem_divE, smul_comm]
  exact D.M.smul_mem (EIn l e (A O K)) (D.upper p hp)


omit [CompleteSpace K] in
theorem cls_E_smul_eq_zero {f : Vec K a ι} (hf : Ezpow K l e (-(2 * H : ℤ)) • f ∈ D.Man) :
    D.cls (E K l e • f) = 0 := by
  have h := D.smul_mem_Man (pow_mem (E_mem l e (Rpi O K l e)) (2 * H + 1)) hf
  have h1 : E K l e ^ (2 * H) * Ezpow K l e (-(2 * H : ℤ)) = 1 := by
    simpa using E_pow_mul_Ezpow_neg (K := K) l e (2 * H)
  rw [smul_smul, pow_succ', mul_assoc, h1, mul_one] at h
  exact D.cls_eq_zero_iff.2 h

end GlobalTheory.BK.MonIntegral


open GlobalTheory.BK.MonIntegral in
theorem GlobalTheory.BK.pow_smul_Mon_add_phi_mem_Z : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (η H : ℕ) (D : BKDat O K l e a ι η H), 1 ≤ η → η < H → 14 * H < l → 10 * H + 2 ≤ l → ∀ r : ℕ, 1 ≤ r → (∀ τ, ∀ c ∈ D.desc.chars τ, frobPeriod l c ≤ r) → (r + 2) * η < l + 1 → l ≠ 2 → ∀ y ∈ D.Y', ∀ m ∈ D.Minv, (l : K) ^ (η * (r + 1)) • D.Mon (y + D.phi m) ∈ D.Z := by
  intro O K _ _ _ _ _ _ l e a ι _ _ _ _ _ _ _ η H D hη hH h14 h10 r hr hc hrl hl y hy m hm
  obtain ⟨hsplit, hfil, -⟩ := GlobalTheory.T.breuilKisin_integrality_computation O K l e a ι η H D hH h10
  have hint := GlobalTheory.T.breuilKisin_descent_operator_preserves_lattice O K l e a ι η H D hH h10
  have hyY : y ∈ D.Y := D.desc.Y'_le_Y η hy
  set W : Submodule O D.Pol :=
    ((D.EM η).restrictScalars O).map (D.cls.restrictScalars O) with hW
  have hL : ∀ p ∈ D.L, D.cls (E K l e • p) ∈ W := fun p hp => ⟨_, E_smul_mem_EM D hp, rfl⟩
  have hMM : ∀ μ ∈ D.MM, D.cls (E K l e • μ) ∈ W := fun μ hμ => by
    obtain ⟨p, hp, f, hf, rfl⟩ := hsplit μ hμ
    rw [smul_add, map_add (f := _), cls_E_smul_eq_zero D (hfil f hf), add_zero]
    exact hL p hp
  have h1 : D.Mon y ∈ W := by
    rw [D.Mon_eq]
    refine sub_mem (hint _ (D.desc.cls_mem_Z hyY)).1 ?_
    obtain ⟨p, hp, f, hf, h⟩ := GlobalTheory.T.breuilKisin_zeta_fine_bound_second_basis O K l e a ι η H D hη hH h14 y hy
    rw [h, smul_add, map_add (f := _), smul_comm (E K l e) _ p, smul_comm (E K l e) _ f,
      D.cls.map_smul ((l : K) ^ _), D.cls.map_smul (_⁻¹ : K), cls_E_smul_eq_zero D (hfil f hf), smul_zero, add_zero]
    exact pow_smul_mem D W _ (hL p hp)
  have h2 : (l : K) ^ (η * (r + 1)) • D.Mon (D.phi m) ∈ W := by
    rw [D.Mon_eq, smul_sub, BKDat.Lc_cls, PhiMod.EN_apply]
    refine sub_mem (pow_smul_mem D W _ (hMM _ (D.conn_mem_MM
      (D.ext_mono (A_le_S l e) (D.phi_mem_L hm.1))))) ?_
    rw [← map_smul, ← smul_comm (E K l e)]
    exact hMM _ (GlobalTheory.T.prime_pow_smul_descent_phi_mem_lattice_of_orbit_bound O K l e a ι η H D r hr hc hrl hl m hm)
  refine ⟨?_, ?_⟩
  · rw [map_add (f := _), smul_add]
    exact add_mem (pow_smul_mem D W _ h1) h2
  · refine D.desc.actPol.invariants.smul_mem _ (D.desc.Mon_mem_invariants (add_mem hyY.2 fun g => ?_))
    rw [D.desc.act_phi, hm.2 g]
end

section

open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.MainNotions Formalism.FrobeniusOrbits Formalism.L2.Host GlobalTheory.CMVal GlobalTheory.ToricDenom GlobalTheory.LamTie

namespace GlobalTheory.LamTie

theorem basecond_exists_above {E : Type} [Field E] [NumberField E] (v : HeightOneSpectrum (OF E)) :
    ∃ P : HeightOneSpectrum (𝓞 E), below P = v := by
  have hinj : Function.Injective (algebraMap (OF E) (𝓞 E)) :=
    FaithfulSMul.algebraMap_injective (OF E) (𝓞 E)
  obtain ⟨Q, -, hQ, hQv⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (S := 𝓞 E) v.asIdeal ⊥
    (by
      intro x hx
      rw [Ideal.mem_comap, Ideal.mem_bot, ← map_zero (algebraMap (OF E) (𝓞 E))] at hx
      rw [hinj hx]
      exact v.asIdeal.zero_mem)
  have hQne : Q ≠ ⊥ := by
    rintro rfl
    apply v.ne_bot
    rw [← hQv]
    exact Ideal.comap_bot_of_injective _ hinj
  refine ⟨⟨Q, hQ, hQne⟩, ?_⟩
  ext x
  simp [below, Ideal.under, ← hQv]

theorem basecond_natCast_mem_below {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) (n : ℕ) :
    (n : OF E) ∈ (below P).asIdeal ↔ (n : 𝓞 E) ∈ P.asIdeal := by
  simp [below, Ideal.under, Ideal.mem_comap, map_natCast]

theorem isBaseCond_cond0 : ∀ (R : Ranks) (H : Formalism.BasicNotions.Host R) (q0 : ℕ) (w0 : HeightOneSpectrum (𝓞 H.E)), (∀ p ∈ [H.g 0, H.g 1, H.pde, H.pde', q0], ∀ P : HeightOneSpectrum (𝓞 H.E), (p : 𝓞 H.E) ∈ P.asIdeal → Splits (below P)) → PlacesOk H q0 w0 → IsBaseCond (cond0 H w0) := by
  intro R H q0 w0 hspl hok
  have hprime : ∀ p ∈ [H.g 0, H.g 1, H.pde, H.pde', q0], p.Prime := fun p hp => (hok.splits p hp).1

  have hN0 : ((H.g 0 * H.g 1 * H.pde * H.pde' : ℕ) : OF H.E) ≠ 0 := by
    have h : H.g 0 * H.g 1 * H.pde * H.pde' ≠ 0 := by
      refine mul_ne_zero (mul_ne_zero (mul_ne_zero ?_ ?_) ?_) ?_ <;>
        exact (hprime _ (by simp)).ne_zero
    exact_mod_cast h
  have hle : cond0 H w0 ≤ (below w0).asIdeal := by
    unfold cond0
    first
    | exact Ideal.mul_le_right
    | exact Ideal.mul_le_left
  refine ⟨?_, ?_, ?_⟩
  · intro h
    rcases Ideal.mul_eq_bot.mp h with h1 | h1
    · rw [← Ideal.zero_eq_bot] at h1
      have h2 := pow_eq_zero_iff (two_ne_zero) |>.mp h1
      rw [Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot] at h2
      exact hN0 h2
    · exact (below w0).ne_bot h1
  · intro h
    exact (below w0).isPrime.ne_top (top_le_iff.mp (h ▸ hle))
  · intro v hv

    obtain ⟨p, hp, hpv⟩ : ∃ p ∈ [H.g 0, H.g 1, H.pde, H.pde', q0], ((p : ℕ) : OF H.E) ∈ v.asIdeal := by
      have hvp : Prime v.asIdeal := Ideal.prime_of_isPrime v.ne_bot v.isPrime
      rcases hvp.dvd_or_dvd hv with h | h
      · have h1 : ((H.g 0 * H.g 1 * H.pde * H.pde' : ℕ) : OF H.E) ∈ v.asIdeal :=
          (Ideal.span_singleton_le_iff_mem _).mp (Ideal.le_of_dvd (hvp.dvd_of_dvd_pow h))
        push_cast at h1
        rcases v.isPrime.mem_or_mem h1 with h1 | h1
        · rcases v.isPrime.mem_or_mem h1 with h1 | h1
          · rcases v.isPrime.mem_or_mem h1 with h1 | h1
            · exact ⟨H.g 0, by simp, h1⟩
            · exact ⟨H.g 1, by simp, h1⟩
          · exact ⟨H.pde, by simp, h1⟩
        · exact ⟨H.pde', by simp, h1⟩
      · have h1 : (below w0).asIdeal = v.asIdeal :=
          ((below w0).isMaximal).eq_of_le v.isPrime.ne_top (Ideal.le_of_dvd h)
        refine ⟨q0, by simp, ?_⟩
        rw [← h1, basecond_natCast_mem_below]
        exact hok.referencePlaceOverPrime
    obtain ⟨P, hPv⟩ := basecond_exists_above v
    have hpP : ((p : ℕ) : 𝓞 H.E) ∈ P.asIdeal := by
      rw [← basecond_natCast_mem_below, hPv]
      exact hpv
    obtain ⟨hpr, hp2, hdisc, hnorm⟩ := hok.splits p hp
    refine ⟨hPv ▸ hspl p hp P hpP, ?_, p, hpr, hp2, hpv, hdisc, hnorm⟩

    obtain ⟨e4, eb, e0⟩ := GlobalTheory.T.conductor_exponent_at_places R H q0 w0 hok P
    rw [← hPv]
    by_cases h4 : Over4 H P
    · rw [e4 h4]
    · by_cases hb : below P = below w0
      · rw [(eb hb).2]; norm_num
      · rw [e0 h4 hb]; norm_num

end GlobalTheory.LamTie
end
