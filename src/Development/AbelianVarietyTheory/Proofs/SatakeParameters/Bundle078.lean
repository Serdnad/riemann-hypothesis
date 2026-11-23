module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NotDvdCondN
public import Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.Bundle003
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle058
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle072
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.TcoMem
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EqOneOfMemLev
public import Development.AutomorphicArithmetic.ResidueCharacters.TwistedPlaces
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle071
public import Formalism.LocalRingCardinality.Bundle007
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
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.CoassocSimps
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW.Rec

theorem jA_eq_depth : ∀ {D : D7} (L : SizeData₂ D) (l : ℕ), 11 ≤ l → (l : ℝ) < LevelStarExponents.lA L → jA L l = depth L l := by
  intro D L l hl hlA
  have hl' : (11 : ℝ) ≤ l := by exact_mod_cast hl
  have hx : (1 : ℝ) < (l : ℝ) - 1 := by linarith
  have hA : (0 : ℝ) < LevelStarExponents.lA L := by linarith
  have key : ∀ j : ℕ, LevelStarExponents.lA L ≤ ((l : ℝ) - 1) ^ j ↔ ⌈Real.logb ((l : ℝ) - 1) (LevelStarExponents.lA L)⌉₊ ≤ j := by
    intro j
    rw [Nat.ceil_le, Real.logb_le_iff_le_rpow hx hA, Real.rpow_natCast]
  have hlog : 1 < Real.logb ((l : ℝ) - 1) (LevelStarExponents.lA L) := by
    rw [Real.lt_logb_iff_rpow_lt hx hA, Real.rpow_one]; linarith
  have hc : 1 ≤ ⌈Real.logb ((l : ℝ) - 1) (LevelStarExponents.lA L)⌉₊ := by
    rw [Nat.one_le_ceil_iff]; linarith
  have hset : {j : ℕ | LevelStarExponents.lA L ≤ ((l : ℝ) - 1) ^ j} = Set.Ici ⌈Real.logb ((l : ℝ) - 1) (LevelStarExponents.lA L)⌉₊ := by
    ext j; simp only [Set.mem_setOf_eq, Set.mem_Ici]; exact key j
  unfold jA depth
  rw [hset, csInf_Ici, max_eq_right hc]

end GlobalTheory.HTW.Rec
end

section

open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW.Rec

theorem exists_base_reads : ∀ {R : Ranks} (H : Host R) {l : ℕ} [Fact l.Prime] (K LL : FinExt l) (c : H.E →+* ↥K.1) (ι : Om l ≃+* ℂ) (τ₀ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (g₀ : R.GG), ι.toRingHom.comp (LL.1.val.toRingHom.comp (τ₀.toRingHom.comp c)) = H.emb g₀ → ∃ κ : H.E →+* ↥LL.1, ∀ (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (g : R.GG), ι.toRingHom.comp (LL.1.val.toRingHom.comp (τ.toRingHom.comp c)) = H.emb g → Reads H c κ τ g := by
  intro R H l _ K LL c ι τ₀ g₀ h₀
  refine ⟨τ₀.toRingHom.comp (c.comp ((H.sigmaOf g₀).symm : H.E →+* H.E)), ?_⟩
  intro τ g hτ x
  have hinj : Function.Injective (fun y : ↥LL.1 => ι (LL.1.val y)) :=
    ι.injective.comp (LL.1.val.injective)
  apply hinj
  have e1 := DFunLike.congr_fun hτ x
  have e2 := DFunLike.congr_fun h₀ ((H.sigmaOf g₀).symm (H.sigmaOf g x))
  simp only [RingHom.comp_apply] at e1 e2
  simp only [RingHom.comp_apply]
  change ι (LL.1.val (τ (c x))) = ι (LL.1.val (τ₀ (c ((H.sigmaOf g₀).symm (H.sigmaOf g x)))))
  have e1' : ι (LL.1.val (τ (c x))) = H.emb g x := e1
  have e2' : ι (LL.1.val (τ₀ (c ((H.sigmaOf g₀).symm (H.sigmaOf g x))))) = H.emb g₀ ((H.sigmaOf g₀).symm (H.sigmaOf g x)) := e2
  rw [e1', e2']
  simp [Host.emb]

end GlobalTheory.HTW.Rec
end

section

noncomputable section

namespace GlobalTheory.HTW.Rec.Model

open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N

instance decThickN {n b η : ℕ} (sz : ZMod n → ℕ) : DecidablePred (ThickN b η sz) := fun i => by
  unfold ThickN; infer_instance

section Input

variable (D : D7) (j : Fin D.R.m) (ε : ℤˣ) {l : ℕ} [Fact l.Prime] {K LL : FinExt l}
  (c : D.host.E →+* ↥K.1) (κ : D.host.E →+* ↥LL.1)

end Input

end GlobalTheory.HTW.Rec.Model
end
end

section

open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits

noncomputable section

namespace GlobalTheory.HTW.Rec

theorem wB_nonneg {D : D7} (L : SizeData₂ D) : 0 ≤ wB L := by
  have hx : 0 < L.sc.x := lt_trans one_pos L.sc.one_lt_alt
  have hb : 0 < L.sc.b := Real.exp_pos _
  have hb' : 0 < L.sc.b' := by
    unfold Scale.b' Scale.a Scale.X'
    positivity
  have h0 : 0 ≤ L.sc.w'' D.R.n := by unfold Scale.w''; positivity
  have h1 := L.etaSz_pos
  exact le_trans (by linarith) (le_max_left _ _)

theorem floor_size_le_wB {D : D7} (L : SizeData₂ D) (g : D.R.GG) (j : Fin D.R.m) (hg : ¬ Thick D.host g) :
    ((⌊(hcAt D g).e j⌋.toNat : ℕ) : ℝ) ≤ wB L := by
  set ρ := D.eTau.symm ⟨plc g, plc_mem g⟩ with hρ
  have hρ' : (D.eTau ρ : D.R.GG) = plc g := by rw [hρ, Equiv.apply_symm_apply]
  have hj : j.1 + 1 ≤ D.R.m := j.2
  have hw : wj D (j.1 + 1) ρ = (((D.hc ρ).e j : ℚ) : ℝ) := by
    have hj' : j.1 + 1 - 1 < D.R.m := by have := j.2; omega
    rw [wj, dite_eq_left hj']
    have : (⟨j.1 + 1 - 1, hj'⟩ : Fin D.R.m) = j := Fin.ext (by simp)
    rw [this]
  have hthick : (D.eTau ρ : D.R.GG) ∉ D.host.thickPlaces := by rw [hρ']; exact hg
  have key : wj D (j.1 + 1) ρ ≤ wB L := by
    by_cases h2 : (D.eTau ρ : D.R.GG) ∈ D.host.topPlaces
    · obtain ⟨t, ht', e⟩ := Finset.mem_image.mp h2
      have a := (L.win_top _ (by omega) hj ρ ⟨t, ht'⟩ e.symm).2
      have b : (L.bT (⟨t, ht'⟩ : D.host.TT) : ℝ) ≤ ⨆ t : D.host.TT, (L.bT t : ℝ) :=
        le_ciSup (f := fun t : D.host.TT => (L.bT t : ℝ)) (Set.finite_range _).bddAbove ⟨t, ht'⟩
      exact le_trans (by linarith) (le_max_right _ _)
    · have a := (L.win_thin (j.1 + 1) (by omega) hj ρ ⟨(D.eTau ρ).2, h2, hthick⟩).2
      exact le_trans a (le_max_left _ _)
  rw [hw] at key
  have he : (hcAt D g).e j = (D.hc ρ).e j := rfl
  rw [he]
  rcases le_or_gt 0 ⌊(D.hc ρ).e j⌋ with h | h
  · rw [show ((⌊(D.hc ρ).e j⌋.toNat : ℕ) : ℝ) = ((⌊(D.hc ρ).e j⌋ : ℤ) : ℝ) by
      exact_mod_cast Int.toNat_of_nonneg h]
    have := Int.floor_le ((D.hc ρ).e j)
    have : (((⌊(D.hc ρ).e j⌋ : ℤ) : ℚ) : ℝ) ≤ (((D.hc ρ).e j : ℚ) : ℝ) := by exact_mod_cast this
    push_cast at this
    linarith
  · rw [Int.toNat_eq_zero.2 h.le]
    simpa using wB_nonneg L

theorem wMax_le_wB : ∀ {D : D7} (L : SizeData₂ D), (wMax D : ℝ) ≤ wB L ∧ (wHat D : ℝ) ≤ wP L := by
  intro D L
  have hB := wB_nonneg L
  have h1 : wMax D ≤ ⌊wB L⌋₊ := by
    apply csSup_le'
    rintro s ⟨g, j, hg, rfl⟩
    exact Nat.le_floor (floor_size_le_wB L g j hg)
  have h2 : (wMax D : ℝ) ≤ wB L :=
    le_trans (by exact_mod_cast h1) (Nat.floor_le hB)
  refine ⟨h2, ?_⟩
  have h3 : (((D.R.t + 1) / 2 : ℕ) : ℝ) ≤ ((D.R.t : ℝ) + 1) / 2 := by
    have := Nat.cast_div_le (α := ℝ) (m := D.R.t + 1) (n := 2)
    push_cast at this
    exact this
  unfold wHat wP
  push_cast
  linarith

end GlobalTheory.HTW.Rec
end
end

section

open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits

noncomputable section

namespace GlobalTheory.SubWp

theorem enl_loc_eq {D : D7} {i : D.nd.Loc} {w : HeightOneSpectrum (𝓞 D.host.E)}
    {hw : w ∈ placesOver D.host.E (D.nd.l i)} (C : Enl D i w hw) {k : ℕ}
    (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) (χ : GE D.nd →* (D.nd.O i)ˣ) (g : Br.G D.nbr i w hw) :
    C.loc (twistM M χ) g =
      (C.inc.comp (Br.toLLK (D.nbr i w hw))) (toK D.nd i ((χ (decS D.nd w (Br.iota D.nbr i w hw g)) : (D.nd.O i)ˣ) : D.nd.O i)) •
        (mapM (toK D.nd i) M (decS D.nd w (Br.iota D.nbr i w hw g))).map (C.inc.comp (Br.toLLK (D.nbr i w hw))) := by
  refine Matrix.ext fun a b => ?_
  change C.inc ((D.nbr i w hw).toLL (((χ (decS D.nd w (Br.iota D.nbr i w hw g)) : (D.nd.O i)ˣ) : D.nd.O i) *
      M (decS D.nd w (Br.iota D.nbr i w hw g)) a b)) =
    C.inc (Br.toLLK (D.nbr i w hw) (toK D.nd i ((χ (decS D.nd w (Br.iota D.nbr i w hw g)) : (D.nd.O i)ˣ) : D.nd.O i))) *
      C.inc (Br.toLLK (D.nbr i w hw) (toK D.nd i (M (decS D.nd w (Br.iota D.nbr i w hw g)) a b)))
  rw [Br.toLLK_alg, Br.toLLK_alg, ← map_mul, ← map_mul, ← map_mul]
  rfl

end GlobalTheory.SubWp

open GlobalTheory.SubWp in
theorem GlobalTheory.subWp_sub : ∀ {D : D7} (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (C : Enl D i w hw) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i), GlobalTheory.IndefiniteRowSideFullHecke.CrystallineAtPlaces.Splits D i r ρ π → IsSubOfSums (matRep (C.loc (WpO D.nd i ρ π))) (fun (_ : Unit) s => C.loc (rTwO D.nd i r π) s) := by
  intro D i w hw C r ρ π ⟨e, he⟩
  set f : KK D.nd i →+* ↥C.LL.1 := C.inc.comp (Br.toLLK (D.nbr i w hw)) with hf
  let A : Matrix (Fin D.R.nV) (Fin D.R.r) (KK D.nd i) :=
    LinearMap.toMatrix' (e.symm.toLinearMap ∘ₗ LinearMap.inl (KK D.nd i) _ _)
  let B : Matrix (Fin D.R.r) (Fin D.R.nV) (KK D.nd i) :=
    LinearMap.toMatrix' (LinearMap.fst (KK D.nd i) _ _ ∘ₗ e.toLinearMap)
  have hBA : B * A = 1 := by
    rw [← LinearMap.toMatrix'_comp, ← LinearMap.toMatrix'_id]
    congr 1
    refine LinearMap.ext fun v => ?_
    simp
  have hRA : ∀ g, mapM (toK D.nd i) (rO D.nd i r π) g * A = A * mapM (toK D.nd i) (rhoO D.nd i ρ π) g := by
    intro g
    apply Matrix.toLin'.injective
    rw [Matrix.toLin'_mul, Matrix.toLin'_mul, Matrix.toLin'_toMatrix']
    refine LinearMap.ext fun v => ?_
    simp only [LinearMap.coe_comp, Function.comp_apply, Matrix.toLin'_apply, LinearEquiv.coe_coe,
      LinearMap.inl_apply]
    apply e.injective
    rw [he, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
    simp <;> rfl
  refine ⟨1, fun _ => (), (LinearMap.pi fun _ => Matrix.mulVecLin (A.map f)), ?_, ?_⟩
  · intro v v' h
    have h1 := congrArg (fun z => (B.map f).mulVec (z 0)) h
    simp only [LinearMap.pi_apply, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, ← Matrix.map_mul, hBA,
      Matrix.map_one f (map_zero f) (map_one f), Matrix.one_mulVec] at h1
    exact h1
  · intro g v
    funext a
    simp only [LinearMap.pi_apply, Matrix.mulVecLin_apply]
    change (A.map f).mulVec ((C.loc (WpO D.nd i ρ π) g).mulVec v) = (C.loc (rTwO D.nd i r π) g).mulVec ((A.map f).mulVec v)
    rw [WpO, rTwO, enl_loc_eq, enl_loc_eq, Matrix.smul_mulVec, Matrix.smul_mulVec, Matrix.mulVec_smul, Matrix.mulVec_mulVec,
      Matrix.mulVec_mulVec, ← hf, ← Matrix.map_mul, ← Matrix.map_mul, hRA]
end
end

section

open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits
open Module TensorProduct

noncomputable section

namespace GlobalTheory.HTW.Rec

section Transport

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    {V' : Type} [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V']

theorem finrank_eq_of_equiv_tensor {C : Type} [AddCommGroup C] [Module Qp C] (e : V ≃ₗ[LL] V')
    (S : Submodule LL (V ⊗[Qp] C)) (S' : Submodule LL (V' ⊗[Qp] C))
    (a : ∀ x ∈ S, SumJumps.ext1 Qp C e.toLinearMap x ∈ S')
    (b : ∀ x ∈ S', SumJumps.ext1 Qp C e.symm.toLinearMap x ∈ S) :
    finrank LL S = finrank LL S' := by
  have h1 : ∀ x : V ⊗[Qp] C, SumJumps.ext1 Qp C e.symm.toLinearMap
      (SumJumps.ext1 Qp C e.toLinearMap x) = x := by
    intro x
    rw [SumJumps.ext1_comp_ext1]
    convert SumJumps.ext1_id (LL := LL) x
    ext v; simp
  have h2 : ∀ x : V' ⊗[Qp] C, SumJumps.ext1 Qp C e.toLinearMap
      (SumJumps.ext1 Qp C e.symm.toLinearMap x) = x := by
    intro x
    rw [SumJumps.ext1_comp_ext1]
    convert SumJumps.ext1_id (LL := LL) x
    ext v; simp
  refine LinearEquiv.finrank_eq (LinearEquiv.ofLinear
    ((SumJumps.ext1 Qp C e.toLinearMap).restrict a)
    ((SumJumps.ext1 Qp C e.symm.toLinearMap).restrict b) ?_ ?_)
  · ext x
    simp [LinearMap.restrict_apply, h2]
  · ext x
    simp [LinearMap.restrict_apply, h1]

variable {ρ : Representation LL G V} {ρ' : Representation LL G V'}

theorem symm_equivariant (e : V ≃ₗ[LL] V') (he : ∀ g v, e (ρ g v) = ρ' g (e v)) (g : G) (v : V') :
    e.symm.toLinearMap (ρ' g v) = ρ g (e.symm.toLinearMap v) := by
  apply e.injective
  rw [he]
  simp

theorem finrank_dcris_eq_of_equiv (e : V ≃ₗ[LL] V') (he : ∀ g v, e (ρ g v) = ρ' g (e v)) :
    finrank LL (Dcris PD ρ) = finrank LL (Dcris PD ρ') :=
  finrank_eq_of_equiv_tensor e _ _ (SumJumps.dcris_map PD e.toLinearMap he)
    (SumJumps.dcris_map PD e.symm.toLinearMap (symm_equivariant e he))

theorem finrank_fildR_eq_of_equiv (e : V ≃ₗ[LL] V') (he : ∀ g v, e (ρ g v) = ρ' g (e v))
    (τ : K →ₐ[Qp] LL) (a : ℤ) :
    finrank LL (FildR PD ρ τ a) = finrank LL (FildR PD ρ' τ a) :=
  finrank_eq_of_equiv_tensor e _ _ (SumJumps.fildR_map PD e.toLinearMap he τ a)
    (SumJumps.fildR_map PD e.symm.toLinearMap (symm_equivariant e he) τ a)

theorem multV_eq_of_equiv (e : V ≃ₗ[LL] V') (he : ∀ g v, e (ρ g v) = ρ' g (e v))
    (τ : K →ₐ[Qp] LL) (a : ℤ) : multV PD ρ τ a = multV PD ρ' τ a := by
  simp only [multV, finrank_fildR_eq_of_equiv PD e he]

theorem isCrys_of_equiv (e : V ≃ₗ[LL] V') (he : ∀ g v, e (ρ g v) = ρ' g (e v))
    (h : IsCrys PD ρ') : IsCrys PD ρ := by
  unfold IsCrys at h ⊢
  rw [finrank_dcris_eq_of_equiv PD e he, h, e.finrank_eq]

end Transport

theorem isCrys_multV_of_isMatRep {l : ℕ} [Fact l.Prime] (P : LocPrime l) (K LL : FinExt l) (T : Lat K LL) {r : ℕ}
    (M : ↥(GK K) →* Matrix (Fin r) (Fin r) ↥LL.1) (h : IsMatRep T M) :
    (IsCrys (P.PD K) (matRep M) → IsCrys (P.PD K) T.ρ) ∧
      ∀ τ u, multV (P.PD K) T.ρ τ u = multV (P.PD K) (matRep M) τ u := by
  obtain ⟨e, he⟩ := h
  have he' : ∀ g v, e (T.ρ g v) = matRep M g (e v) := by
    intro g v
    rw [he]
    simp [matRep, Matrix.toLinAlgEquiv'_apply]
  exact ⟨isCrys_of_equiv _ e he', fun τ u => multV_eq_of_equiv _ e he' τ u⟩

end GlobalTheory.HTW.Rec
end
end

section

open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits

namespace GlobalTheory.InertPrimeEleven

theorem eleven_le : ∀ eps : ℝ, 0 < eps → ∃ x0 : ℝ, ∀ (D : D7) (L : SizeData₂ D) (l : ℕ),
    L.sc.ez = eps → x0 ≤ L.sc.x → l.Prime → InertUnr D l → 11 ≤ l := by
  intro eps heps
  refine ⟨(11 : ℝ) ^ (5 / eps), ?_⟩
  intro D L l he hx hl hin
  have hlt := GlobalTheory.InertPrimeLarge.lt_prime L l hl hin.ne_two hin.2.2.2
  rw [he] at hlt
  have h0 : (0 : ℝ) ≤ (11 : ℝ) ^ (5 / eps) := Real.rpow_nonneg (by norm_num) _
  have hmono : ((11 : ℝ) ^ (5 / eps)) ^ (eps / 5) ≤ L.sc.x ^ (eps / 5) :=
    Real.rpow_le_rpow h0 hx (by positivity)
  have h11 : ((11 : ℝ) ^ (5 / eps)) ^ (eps / 5) = 11 := by
    rw [← Real.rpow_mul (by norm_num)]
    have : 5 / eps * (eps / 5) = 1 := by field_simp
    rw [this, Real.rpow_one]
  have : (11 : ℝ) < l := by linarith
  exact_mod_cast this.le

end GlobalTheory.InertPrimeEleven
end

section

open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits

noncomputable section
namespace GlobalTheory.HTW.Rec

theorem enlLoc_apply {D : D7} {i : D.nd.Loc} {w : HeightOneSpectrum (𝓞 D.host.E)}
    {hw : w ∈ placesOver D.host.E (D.nd.l i)} (C : Enl D i w hw) {k : ℕ}
    (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) (g : Br.G D.nbr i w hw) (a b : Fin k) :
    C.loc M g a b = C.inc ((D.nbr i w hw).toLL (M (decS D.nd w (Br.iota D.nbr i w hw g)) a b)) := rfl

theorem twistedDuals_eq_tateDuals : ∀ {D : D7} (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (C : Enl D i w hw) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i), (∀ s, C.inc ((Br.locChi D.nbr i w hw (epsU D.nd i) s : (Br.LL D.nbr i w hw)ˣ) : Br.LL D.nbr i w hw) = ((cycLL (Br.PD D.loc D.nbr i w hw) ↥C.LL.1 s : (↥C.LL.1)ˣ) : ↥C.LL.1)) → (∀ x, C.loc (rDuO D.nd i r x) = twistM (dualM (C.loc (rTwO D.nd i r x))) (cycLL (Br.PD D.loc D.nbr i w hw) ↥C.LL.1)) ∧ C.loc (T2O D.nd i ρ π) = twistM (dualM (C.loc (WpO D.nd i ρ π))) (cycLL (Br.PD D.loc D.nbr i w hw) ↥C.LL.1) := by
  intro D i w hw C r ρ π h
  have hc : ∀ g, ((cycLL (Br.PD D.loc D.nbr i w hw) ↥C.LL.1 g : (↥C.LL.1)ˣ) : ↥C.LL.1) =
      C.inc ((D.nbr i w hw).toLL ((epsU D.nd i (decS D.nd w (Br.iota D.nbr i w hw g)) : (D.nd.O i)ˣ) : D.nd.O i)) :=
    fun g => (h g).symm
  refine ⟨fun x => ?_, ?_⟩
  · ext g a b
    rw [enlLoc_apply]
    simp only [twistM, dualM, MonoidHom.coe_mk, OneHom.coe_mk, Matrix.smul_apply, Matrix.transpose_apply, smul_eq_mul, hc, enlLoc_apply, rDuO, rTwO, map_inv, Units.val_mul, map_mul]
    simp only [MonoidHom.mul_apply, MonoidHom.inv_apply, inv_inv, Units.val_mul, map_mul]
    exact congrArg _ (by ring)
  · ext g a b
    rw [enlLoc_apply]
    simp only [twistM, dualM, MonoidHom.coe_mk, OneHom.coe_mk, Matrix.smul_apply, Matrix.transpose_apply, smul_eq_mul, hc, enlLoc_apply, T2O, map_inv, Units.val_mul, map_mul]

end GlobalTheory.HTW.Rec
end
end

section

open GlobalTheory GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

theorem _root_.GlobalTheory.T.trace_eval_origin_eq_fibre_trace : ∀ (k : Type) [Field k] [CharZero k] (F K : Type) [Field F] [Field K] [Algebra k F] [Algebra k K] [Algebra F K] [IsScalarTower k F K] (d : ℕ) (x : Fin (d + 1) → F), IsFinCover k K x → ∀ ev : rA k x {0} →ₐ[k] k, RingHom.ker ev = Ideal.span (Set.range fun j : Fin d => (⟨x j.succ / x 0, Algebra.subset_adjoin ⟨0, Finset.mem_singleton_self 0, j.succ, rfl⟩⟩ : rA k x {0})) → ∀ (h : rB k K x {0}) (a : rA k x {0}), (a : F) = Algebra.trace F K (h : K) → ev a = Algebra.trace k ((rB k K x {0}) ⧸ (Ideal.span (Set.range fun j : Fin d => (⟨_, tco_mem k K x j⟩ : (rB k K x {0}))))) (Ideal.Quotient.mk _ h) := by
  first | (exact @GlobalTheory.PD.TraceOrigin.ev_eq_trace_quot) | (exact GlobalTheory.PD.TraceOrigin.ev_eq_trace_quot) | (intros; apply GlobalTheory.PD.TraceOrigin.ev_eq_trace_quot  <;> assumption)
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host
open GlobalTheory.HeckeUnrExt
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele (ideleMap ideleConj)

theorem _root_.GlobalTheory.T.cmIdeleConj_mem_congruenceUnitIdeles_conj_places : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (T : Set (HeightOneSpectrum (𝓞 E))) (N : ℕ) (u : Ideles E), u ∈ levT E T N → ideleConj (maximalRealSubfield E) E u ∈ levT E {w | ∀ w' : HeightOneSpectrum (𝓞 E), w'.under (𝓞 (maximalRealSubfield E)) = w.under (𝓞 (maximalRealSubfield E)) → w' ∈ T} N := by
  first | exact @GlobalTheory.HeckeConjLev.ideleConj_mem_levT | exact GlobalTheory.HeckeConjLev.ideleConj_mem_levT | (intros; apply GlobalTheory.HeckeConjLev.ideleConj_mem_levT <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal

theorem _root_.GlobalTheory.T.inert_prime_ne_typePrime : ∀ (D : D7) (l : ℕ) (k : Fin 2), TwistedPlaces.InertK D l → l ≠ D.host.g k := by
  first | exact @GlobalTheory.InertNotType.main | exact GlobalTheory.InertNotType.main | (intros; apply GlobalTheory.InertNotType.main <;> assumption)
end

section

open Formalism.BasicNotions Classical

namespace GlobalTheory.KFiMu0

theorem fi_eq_range' {R : Ranks} {LL : Type} [Field LL] [NumberField LL] [StarRing LL] {embLL : LL →+* ℂ} {Pl : Rows.Places LL}
    {Tau : Type} [Fintype Tau] {hc : Tau → HCParam R} {C : ColumnChain R Tau hc} {A : ColumnsAtT R C} {P : PeriodMap R C}
    (M : MemberForms LL embLL Pl Tau hc C A P) (j : ℕ) : M.Fi j = Submodule.span ℂ (Set.range (M.emb j)) := by
  refine le_antisymm ?_ (Submodule.span_le.2 ?_)
  · rw [← (M.emb_basis j).2]
    exact Submodule.span_mono (by rintro _ ⟨a, rfl⟩; exact ⟨_, rfl⟩)
  · rintro _ ⟨x, rfl⟩

    rw [← (M.emb_basis j).2, ← (M.lat j).b.sum_repr x, map_sum]
    refine Submodule.sum_mem _ fun a _ => ?_
    rw [LinearMap.map_smulₛₗ]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)

theorem carries_one {R : Ranks} {LL : Type} [Field LL] [NumberField LL] [StarRing LL] {embLL : LL →+* ℂ} {Pl : Rows.Places LL}
    {Tau : Type} [Fintype Tau] {hc : Tau → HCParam R} {C C' : ColumnChain R Tau hc} (h : C' = C)
    {A : ColumnsAtT R C} {P : PeriodMap R C} {A' : ColumnsAtT R C'} {P' : PeriodMap R C'}
    (M : MemberForms LL embLL Pl Tau hc C A P) (M' : MemberForms LL embLL Pl Tau hc C' A' P')
    (e : ∀ j, j ≤ R.m → ((M.lat j).V ≃ₗ[LL] (M'.lat j).V)) (he : ∀ j hj x, HEq (M'.emb j (e j hj x)) (M.emb j x))
    (i : ℕ) (hi : i < R.m) (H : ∀ φ ∈ M'.Fi i, C'.K i φ ∈ M'.Fi (i + 1)) :
    ∀ φ ∈ M.Fi i, C.K i φ ∈ M.Fi (i + 1) := by
  subst h
  have k : ∀ j, j ≤ R.m → M.Fi j = M'.Fi j := fun j hj => by
    rw [fi_eq_range', fi_eq_range']
    congr 1
    ext φ
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨e j hj x, eq_of_heq (he j hj x)⟩
    · rintro ⟨y, rfl⟩
      obtain ⟨x, rfl⟩ := (e j hj).surjective y
      exact ⟨x, (eq_of_heq (he j hj x)).symm⟩
  intro φ hφ
  rw [k _ hi.le] at hφ
  rw [k _ hi]
  exact H φ hφ

theorem memberForms_stable_of_reference_tuple : ∀ (D : D7) (T : TwForms D) (u : D.what₂.Word), ∀ i < D.R.m,
    (∀ φ ∈ (T.fm u D.what₂.mu0).Fi i, (D.chTw u D.what₂.mu0).K i φ ∈ (T.fm u D.what₂.mu0).Fi (i + 1)) →
    ∀ φ ∈ (D.fm u).Fi i, (D.mem u).C.K i φ ∈ (D.fm u).Fi (i + 1) :=
  fun D T u i hi H => carries_one (D.memberColumns_twistedChain_base u) (D.fm u) (T.fm u D.what₂.mu0) (T.eMu0 u) (T.eMu0_emb u) i hi H

end GlobalTheory.KFiMu0
end
