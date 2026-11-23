module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SplitLineSubtraction.SubtractOf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle862
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalFilDR
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle274
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle556
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle053
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle290
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle272
import Mathlib.Algebra.AffineMonoid.UniqueSums
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle276
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle006
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle806
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WdParameterMonodromyZeroIffPotentiallyCrystallin
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle139
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFixedIff
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsSteinberg
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.MetAndHolds
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.ConclusionFinite
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle012
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open NumberField IsDedekindDomain
open Neutral.B1 hiding G Dec
open Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC
open Formalism.MainNotions.SumRepresentations.At (sumRep)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (FrobEig algSat RepIso tw)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.Gal.TP.Sub

private theorem exists_finExt_gl {l n : ℕ} [Fact l.Prime] (A : GL (Fin n) (Qbar l)) :
    ∃ K : FinExt l, ∀ i j, (A : Matrix (Fin n) (Fin n) (Qbar l)) i j ∈ K.1 ∧
      ((A⁻¹ : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l)) i j ∈ K.1 := by
  let s : Set (Qbar l) := Set.range (fun p : Fin n × Fin n => (A : Matrix (Fin n) (Fin n) (Qbar l)) p.1 p.2) ∪
    Set.range (fun p : Fin n × Fin n => ((A⁻¹ : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l)) p.1 p.2)
  have hs : s.Finite := (Set.finite_range _).union (Set.finite_range _)
  haveI : Finite s := hs.to_subtype
  refine ⟨⟨IntermediateField.adjoin ℚ_[l] s,
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x⟩, fun i j => ⟨?_, ?_⟩⟩
  · exact IntermediateField.subset_adjoin _ _ (Or.inl ⟨(i, j), rfl⟩)
  · exact IntermediateField.subset_adjoin _ _ (Or.inr ⟨(i, j), rfl⟩)

private theorem isdRAt_conj {l : ℕ} [Fact l.Prime] {P : LocPrime l} {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω]
    {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] {Gw : Subgroup (Ω ≃ₐ[E] Ω)}
    {Bw : LocBridge l E Ω Gw O} {m : ℕ} {r : ↥Gw →* GL (Fin m) (Qbar l)} (A : GL (Fin m) (Qbar l)) (K : FinExt l)
    (hA : ∀ i j, (A : Matrix (Fin m) (Fin m) (Qbar l)) i j ∈ K.1 ∧
      ((A⁻¹ : GL (Fin m) (Qbar l)) : Matrix (Fin m) (Fin m) (Qbar l)) i j ∈ K.1)
    (hr : IsdRAt P Bw r) : IsdRAt P Bw ((MulAut.conj A⁻¹).toMonoidHom.comp r) := by
  obtain ⟨LL', r₀, hm, hc⟩ := hr
  obtain ⟨h, M, hM⟩ := GlobalTheory.ConjCrys.exists_conj_model A K hA hm
  obtain ⟨-, hdR2, -, -⟩ := GlobalTheory.Pst.local_ext P Bw h r₀
  exact ⟨_, _, hM, (GlobalTheory.ConjCrys.local_conj P Bw _ M _).2.1 (hdR2.2 hc)⟩

theorem UpperTheory.Gal.TP.Sub.clConj_holds :
    CpFacts → ContLeft → PstOfDR → ClConj := by
  intro hCp hCont hPst E Ω _ _ _ _ _ l _ ι a r r' hr hiso w S J hcl
  obtain ⟨g, hg⟩ := id hiso
  obtain ⟨h1, h2⟩ := hcl
  refine ⟨fun hl A hA => ?_, ?_⟩
  · obtain ⟨i1, i2⟩ := h1 hl A hA
    refine ⟨fun s hs => ?_, fun σ hσ => ?_⟩
    · rw [hg, i1 s hs]
      simp
    · have e : (r' σ⁻¹ : Matrix (Fin a) (Fin a) (Qbar l)).charpoly =
          (r σ⁻¹ : Matrix (Fin a) (Fin a) (Qbar l)).charpoly :=
        (hCp (G E Ω) (Qbar l) a a).2.2 r r' hiso σ⁻¹
      rw [e]
      exact i2 σ hσ
  · intro P AI hT A h O _ _ _ Bw hj
    obtain ⟨c1, c2, c3, c4⟩ := h2 P AI hT A h O Bw hj
    obtain ⟨K, hK⟩ := exists_finExt_gl (g⁻¹)
    have e : r'.comp (Dec (F := E) A).subtype =
        (MulAut.conj (g⁻¹)⁻¹).toMonoidHom.comp (r.comp (Dec (F := E) A).subtype) := by
      ext1 x
      simp [hg, MulAut.conj_apply]
    have hc' : Continuous r' := (hCont (G E Ω) (Qbar l) a a).2.1 r r' hiso hr
    have cρ : Continuous (r.comp (Dec (F := E) A).subtype) := hr.comp continuous_subtype_val
    have cρ' : Continuous (r'.comp (Dec (F := E) A).subtype) := hc'.comp continuous_subtype_val
    have d' : IsdRAt P Bw (r'.comp (Dec (F := E) A).subtype) := by
      rw [e]
      exact isdRAt_conj _ K hK c2
    refine ⟨?_, d', fun τ LL' τ' hI => ?_, fun x => ?_⟩
    · rw [e]
      exact GlobalTheory.ConjCrys.isCrysAt_conj _ K hK c1
    · rw [e]
      exact GlobalTheory.ConjCrys.isJumpsAt_conj _ K hK (c3 τ LL' τ' hI)
    · rw [GlobalTheory.ConjGal.wdAt_conj P ι Bw h hj (r.comp (Dec (F := E) A).subtype)
        (r'.comp (Dec (F := E) A).subtype) g (fun x => hg x)
        (hPst l P AI hT E Ω A O Bw a _ cρ c2) (hPst l P AI hT E Ω A O Bw a _ cρ' d')]
      exact c4 x
end

section

open NumberField IsDedekindDomain
open Neutral.B1 hiding Dec
open Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC
open Formalism.MainNotions.SumRepresentations.At (sumRep)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (FrobEig algSat RepIso tw)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.Gal.TP.Sub

theorem UpperTheory.Gal.TP.Sub.twLoc_holds :
    TwLoc := by
  intro l _ P AI hT E Ω _ _ _ _ _ A O _ _ _ Bw a r c
  have h := GlobalTheory.TwistAbove.twist_above l P AI hT E Ω (Dec (F := E) A) O Bw a r (tw r c) c
    (fun g => UpperTheory.V.Af.tw_val r c g)
  exact ⟨h.1, h.2.1⟩
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC
open Formalism.MainNotions.SumRepresentations.At (sumRep)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (FrobEig algSat RepIso tw)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.Gal.TP.Sub

private theorem scaleRoots_X_sub_C' (a d : ℂ) : (X - C a : ℂ[X]).scaleRoots d = X - C (a * d) := by
  rw [sub_eq_add_neg, ← C_neg, X_add_C_scaleRoots, neg_mul, C_neg, ← sub_eq_add_neg]

private theorem scaleRoots_unrPol (S : Multiset ℂ) (m : ℤ) (c : ℂ) :
    (unrPol S m).scaleRoots (c ^ (-m)) = unrPol (S.map (· * c)) m := by
  unfold unrPol
  induction S using Multiset.induction_on with
  | empty => simp
  | cons a S ih =>
    simp only [Multiset.map_cons, Multiset.prod_cons, mul_scaleRoots_of_noZeroDivisors, ih,
      scaleRoots_X_sub_C', mul_zpow]

theorem UpperTheory.Gal.TP.Sub.wDFacts_holds :
    WDFacts := by
  intro E Ω _ _ _ _ _ A w h x y
  induction x using WD.ind with | _ n a => ?_
  induction y using WD.ind with | _ m b => ?_
  refine ⟨?_, fun g => WD.charPol_lpSum _ _ g, ?_, ?_⟩
  · rw [WD.lpSum_mk, WD.unr_mk, WD.unr_mk]
    unfold WDRep.Unr
    simp only [WDRep.sum]
    rintro ⟨hN, hρ⟩
    refine ⟨?_, fun σ => ?_⟩
    · apply LinearMap.ext
      intro v
      have hv := congrArg (fun f => (f (v, 0)).1) hN
      simpa using hv
    · apply LinearMap.ext
      intro v
      have hv := congrArg (fun f => (f (v, 0)).1) (hρ σ)
      simpa [Representation.prod] using hv
  · rw [WD.lpChar_mk, WD.unr_mk, WD.unr_mk, WD.unr_mk]
    unfold WDRep.Unr
    simp only [WDRep.tensor]
    rintro ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨by simp [ha, hb], fun σ => ?_⟩
    rw [Representation.tprod_apply, ha' σ, hb' σ]
    simp
  · intro g S c hx hy
    rw [WD.charPol_mk] at hx hy
    rw [WD.lpChar_mk, WD.charPol_mk, WDRep.tensor_ρ]
    have hm : m = 1 := by
      have hd := congrArg Polynomial.natDegree hy
      rw [LinearMap.charpoly_natDegree] at hd
      unfold unrPol at hd
      simpa using hd
    subst hm
    have hb : b.ρ g = c ^ (-deg g) • (1 : Module.End ℂ (Fin 1 → ℂ)) := by
      have hct := LinearMap.aeval_self_charpoly (b.ρ g)
      rw [hy] at hct
      unfold unrPol at hct
      simp only [Multiset.map_singleton, Multiset.prod_singleton, map_sub, aeval_X, aeval_C] at hct
      rw [sub_eq_zero] at hct
      rw [hct, Algebra.algebraMap_eq_smul_one]
    have ht : c ^ (-deg g) ≠ 0 := by
      intro ht0
      have h0 : b.ρ g = 0 := by
        rw [hb, ht0, zero_smul]
      have h1 : b.ρ (g * g⁻¹) = 1 := by
        rw [mul_inv_cancel, map_one]
      rw [map_mul, h0, zero_mul] at h1
      exact zero_ne_one h1
    rw [hb, TensorProduct.map_smul_right, GlobalTheory.CompanionTheory.RelOpsLeaf.charpoly_smul_eq_scaleRoots _ ht,
      GlobalTheory.CompanionTheory.RelOpsLeaf.charpoly_map_one (by simp), hx, scaleRoots_unrPol]
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC
open Formalism.MainNotions.SumRepresentations.At (sumRep)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (FrobEig algSat RepIso tw)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.Gal.TP.Sub

theorem UpperTheory.Gal.TP.Sub.peelOne_holds :
    DgFacts → CpFacts → EigTransfer → EigSum → SplitLine → SSLeft → PeelOne := by
  intro hDg hCp hTr hEig hSplit hSS Γ k _ _ _ _ m m' t t' r r' a a' hr hr' hne hcp
  set c := a (Fin.last t) with hc
  have hR1 : IsSSRep (sumRep r (dg a')) := GlobalTheory.BCGal.ss_sumRep _ _ hr (hDg Γ k t' a').1
  have hR2 : IsSSRep (sumRep r' (dg a)) := GlobalTheory.BCGal.ss_sumRep _ _ hr' (hDg Γ k (t + 1) a).1
  have hcpR : ∀ g, cp (sumRep r (dg a')) g = cp (sumRep r' (dg a)) g := by
    intro g
    rw [(hCp Γ k (m + 1) t').1, (hCp Γ k m' (t + 1)).1, (hDg Γ k t' a').2, (hDg Γ k (t + 1) a).2]
    exact hcp g
  have hv2 := (hEig Γ k m' (t + 1) r' a c).1 ⟨Fin.last t, rfl⟩
  have hv1 := hTr Γ k _ _ (sumRep r (dg a')) (sumRep r' (dg a)) hR1 hR2 hcpR c hv2
  have hv := (hEig Γ k (m + 1) t' r a' c).2 (fun j h => hne (Fin.last t) j h.symm) hv1
  obtain ⟨s, hs⟩ := hSplit Γ k m r hr c hv
  have hsum : IsSSRep (sumRep s (rk1 c)) := (hSS Γ k (m + 1) 0).2.1 r _ hs hr
  refine ⟨s, (hSS Γ k m 1).1 s (rk1 c) hsum, hs, ?_⟩
  intro g
  have h1 : cp r g = cp s g * (X - C ((c g : kˣ) : k)) := by
    rw [← (hCp Γ k (m + 1) 0).2.2 r _ hs g, (hCp Γ k m 1).1, (hCp Γ k m 1).2.1]
  have h2 : lin a g = lin (fun i => a i.castSucc) g * (X - C ((c g : kˣ) : k)) := by
    simp only [lin]
    rw [Fin.prod_univ_castSucc]
  have hX : (X - C ((c g : kˣ) : k) : k[X]) ≠ 0 := Polynomial.X_sub_C_ne_zero _
  have key := hcp g
  rw [h1, h2] at key
  apply mul_right_cancel₀ hX
  calc cp s g * lin a' g * (X - C ((c g : kˣ) : k))
      = cp s g * (X - C ((c g : kˣ) : k)) * lin a' g := by ring
    _ = cp r' g * (lin (fun i => a i.castSucc) g * (X - C ((c g : kˣ) : k))) := key
    _ = cp r' g * lin (fun i => a i.castSucc) g * (X - C ((c g : kˣ) : k)) := by ring
end

section

noncomputable section

open Formalism.MainNotions.N Polynomial
open Formalism.MainNotions.SumRepresentations.At (sumRep)

namespace UpperTheory.Gal.TP.Sub

section

variable {Γ k : Type} [Group Γ] [Field k]

private theorem dg_val {t : ℕ} (a : Fin t → Γ →* kˣ) (g : Γ) :
    ((dg a g : GL (Fin t) k) : Matrix (Fin t) (Fin t) k) = Matrix.diagonal fun i => (a i g : k) := rfl

private theorem ss_dg_one (b : Fin 1 → Γ →* kˣ) : IsSSRep (dg b) := by
  have key : ∀ (W : Submodule k (Fin 1 → k)), IsInv (dg b) W := by
    intro W g v hv
    have : ((dg b g : GL (Fin 1) k) : Matrix (Fin 1) (Fin 1) k).mulVec v = ((b 0 g : kˣ) : k) • v := by
      ext i
      fin_cases i
      simp [dg_val, Matrix.mulVec_diagonal]
    rw [this]
    exact W.smul_mem _ hv
  intro W _
  obtain ⟨W', hW'⟩ := exists_isCompl W
  exact ⟨W', key W', hW'⟩

private theorem dg_succ {t : ℕ} (a : Fin (t + 1) → Γ →* kˣ) :
    dg a = sumRep (dg fun i : Fin t => a i.castSucc) (dg fun _ : Fin 1 => a (Fin.last t)) := by
  ext g : 1
  apply Units.ext
  rw [GlobalTheory.BCGal.sumRep_val, dg_val, dg_val, dg_val]
  ext i j
  obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
  obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [Matrix.diagonal_apply, Matrix.reindex_apply, Matrix.submatrix_apply]
  · rfl
  · intro h
    have h' := congrArg Fin.val h
    simp only [Fin.val_castAdd, Fin.val_natAdd] at h'
    omega
  · intro h
    have h' := congrArg Fin.val h
    simp only [Fin.val_castAdd, Fin.val_natAdd] at h'
    omega
  · obtain rfl : i = 0 := Subsingleton.elim _ _
    obtain rfl : j = 0 := Subsingleton.elim _ _
    rfl

private theorem ss_dg {t : ℕ} (a : Fin t → Γ →* kˣ) : IsSSRep (dg a) := by
  induction t with
  | zero => exact GlobalTheory.BCGal.ss_zero _
  | succ t ih =>
    rw [dg_succ]
    exact GlobalTheory.BCGal.ss_sumRep _ _ (ih _) (ss_dg_one _)

end

theorem dgFacts_holds : DgFacts := by
  intro Γ k _ _ t a
  refine ⟨ss_dg a, fun g => ?_⟩
  show ((dg a g : GL (Fin t) k) : Matrix (Fin t) (Fin t) k).charpoly = _
  rw [dg_val, Matrix.charpoly_diagonal]

end UpperTheory.Gal.TP.Sub

end
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC
open Formalism.MainNotions.SumRepresentations.At (sumRep)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (FrobEig algSat RepIso tw)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.Gal.TP.Sub

private theorem dg_mulVec {Γ k : Type} [Group Γ] [Field k] {t : ℕ} (a : Fin t → Γ →* kˣ) (g : Γ)
    (u : Fin t → k) (i : Fin t) :
    ((dg a g : GL (Fin t) k) : Matrix (Fin t) (Fin t) k).mulVec u i = (a i g : k) * u i := by
  simp [dg, Matrix.mulVec_diagonal]

theorem UpperTheory.Gal.TP.Sub.eigSum_holds :
    EigSum := by
  intro Γ k _ _ m t r a c
  refine ⟨?_, ?_⟩
  · rintro ⟨i, hi⟩
    let e : Fin t → k := Pi.single i 1
    let w : Fin (m + t) → k := fun x => (finSumFinEquiv.symm x).elim (fun _ => 0) e
    have hwl : w ∘ ⇑finSumFinEquiv ∘ Sum.inl = 0 := by
      funext y
      simp [w]
    have hwr : w ∘ ⇑finSumFinEquiv ∘ Sum.inr = e := by
      funext y
      simp [w]
    refine ⟨w, ?_, ?_⟩
    · intro h
      have := congrFun hwr i
      rw [h] at this
      simp [e] at this
    · intro g
      funext x
      obtain ⟨y, rfl⟩ := finSumFinEquiv.surjective x
      rcases y with y | y
      · rw [GlobalTheory.EigTwist.sumRep_mulVec_inl, hwl, Matrix.mulVec_zero, Pi.smul_apply]
        have := congrFun hwl y
        simp only [Function.comp_apply] at this
        rw [this]
        simp
      · rw [GlobalTheory.EigTwist.sumRep_mulVec_inr, hwr, dg_mulVec]
        have := congrFun hwr y
        simp only [Function.comp_apply] at this
        rw [Pi.smul_apply, this, smul_eq_mul]
        by_cases hy : y = i
        · subst hy
          rw [hi]
        · simp [e, Pi.single_apply, hy]
  · intro hne hex
    obtain ⟨w, hw0, hw⟩ := hex
    rcases GlobalTheory.EigTwist.eigen_pair c r (dg a) w hw0 hw with h | ⟨v, hv0, hv⟩
    · exact h
    · exfalso
      obtain ⟨j, hj⟩ : ∃ j, v j ≠ 0 := by
        by_contra hcon
        push_neg at hcon
        exact hv0 (funext hcon)
      apply hne j
      ext g
      have := congrFun (hv g) j
      rw [dg_mulVec, Pi.smul_apply, smul_eq_mul] at this
      exact mul_right_cancel₀ hj this
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC
open Formalism.MainNotions.SumRepresentations.At (sumRep)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (FrobEig algSat RepIso tw)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.Gal.TP.Sub

theorem UpperTheory.Gal.TP.Sub.cpFacts_holds :
    CpFacts := by
  intro Γ k _ _ a b
  refine ⟨fun r s g => GlobalTheory.EigTwist.charpoly_sumRep r s g, ?_, ?_⟩
  · intro c g
    simp [cp, rk1, Matrix.charpoly, Matrix.charmatrix, Matrix.det_unique]
  · rintro r r' ⟨u, hu⟩ g
    simp only [cp, hu, Units.val_mul]
    rw [Matrix.coe_units_inv]
    exact Matrix.charpoly_units_conj u (r g : Matrix (Fin a) (Fin a) k)
end

section

open NumberField IsDedekindDomain
open Neutral.B1 hiding G Dec
open Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC
open Formalism.MainNotions.SumRepresentations.At (sumRep)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (FrobEig algSat RepIso tw)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.Gal.TP.Sub

theorem UpperTheory.Gal.TP.Sub.charAbove_holds :
    GlobalTheory.Published.HeckeLAdicCharacter → GlobalTheory.Published.HeckeLAdicCharacterDeRham → GlobalTheory.Published.AlgebraicCharacterWD → PstOfDR → ContLeft → CharAbove := by
  intro H hD hW hP hC E Ω _ _ _ _ _ l _ ι art ha χ n μ h1 h2 h3 w hu P AI hT A h O _ _ _ Bw hj
  obtain ⟨a, ha'⟩ := GlobalTheory.localArtinExists_holds E Ω A w h
  have hξ := GlobalTheory.Published.ParamAboveModel.isComp_loc (w := w) χ
  have d := hD E Ω l P AI hT ι art ha χ n μ h1 h2 h3 w A h O Bw hj
  have hc : Continuous ((rk1 μ).comp (Dec (F := E) A).subtype) :=
    ((hC (G E Ω) (Qbar l) 0 0).2.2.2 μ h2).comp continuous_subtype_val
  have hr := hP l P AI hT E Ω A O Bw 1 _ hc d.1
  have e := hW E Ω l P AI hT ι art ha χ n μ h1 h2 h3 w A h O Bw hj _ hξ a ha'
  have hun := (GlobalTheory.Published.CharCrysModel.isUnram_iff χ w).2 hu
  refine ⟨?_, d.1, d.2, fun g => ?_⟩
  · rw [← GlobalTheory.PstLaws.unr_wdAt_iff Bw h hj P ι _ hr, e, GlobalTheory.LocLanglands.Test.unr_lpOfChar_iff ha' hξ.1]
    exact hun
  · have hv : (χ.loc w (a g) : ℂ) = ((χ.val w : ℂˣ) : ℂ) ^ (-deg g) := by
      have ho : GlobalTheory.SmGL.ord (w.adicCompletion E) (atFin w (unif w)) = 1 := by
        rw [GlobalTheory.SmGL.SphCompletion.ord_completion, show Valued.v ((atFin w (unif w) : (w.adicCompletion E)ˣ) : w.adicCompletion E) = _ from unif_spec w]
        simp
      have h1 : ∀ x : (w.adicCompletion E)ˣ, χ.loc w x = χ.val w ^ GlobalTheory.SmGL.ord (w.adicCompletion E) x := fun x => by
        have h0 : GlobalTheory.SmGL.ord (w.adicCompletion E) (x * (atFin w (unif w) ^ GlobalTheory.SmGL.ord (w.adicCompletion E) x)⁻¹) = 0 := by
          have hz : ∀ (y : (w.adicCompletion E)ˣ), GlobalTheory.SmGL.unrChar (w.adicCompletion E) (Units.mk0 2 two_ne_zero) y =
              (Units.mk0 (2:ℂ) two_ne_zero) ^ GlobalTheory.SmGL.ord _ y := fun _ => rfl
          let φ : (w.adicCompletion E)ˣ →* Multiplicative ℤ := MonoidHom.mk' (fun y => Multiplicative.ofAdd (GlobalTheory.SmGL.ord _ y))
            fun y z => by rw [GlobalTheory.SmGL.ord_mul, ofAdd_add]
          have : φ (x * (atFin w (unif w) ^ GlobalTheory.SmGL.ord (w.adicCompletion E) x)⁻¹) = 1 := by
            rw [map_mul, map_inv, map_zpow]
            simp [φ, ho, ← ofAdd_zsmul]
          exact this
        have := hun _ ((GlobalTheory.SmGL.ord_eq_zero_iff).1 h0)
        rw [map_mul, map_inv, map_zpow, mul_inv_eq_one] at this
        exact this
      rw [h1, ha'.ord_eq, Units.val_zpow_eq_zpow_val]
    rw [e, WD.charPol_eq_prod, GlobalTheory.LocLanglands.eig_lpOfChar]
    simp [unrPol, hv]
end
