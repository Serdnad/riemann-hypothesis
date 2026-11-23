module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle009
public import Formalism.SharpRestriction.LevelLetterCocycles.DecompositionData
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle010
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.Finsupp.Pointwise
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open GlobalTheory.TypeLeaf Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.ArithmeticCylinders Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain

namespace GlobalTheory.TypeLeaf


open Polynomial NumberField IsDedekindDomain in
theorem _root_.GlobalTheory.TypeLeaf.lpChar_eq_triv_of_mul_eq_one (D : _root_.Formalism.BasicNotions.D7) (w : _root_.Formalism.BasicNotions.PlE D.host)
    (χ χ' : D.naut.LP w) (c c' : ℂ)
    (hu : D.naut.unr χ) (hu' : D.naut.unr χ') (hd' : D.naut.lpDim χ' = 1)
    (hc : D.naut.frobEig χ = {c}) (hc' : D.naut.frobEig χ' = {c'}) (h : c * c' = 1) :
    D.naut.lpChar χ χ' = D.naut.lpUnr w {1} := by
  have hu2 := D.naut.unr_char χ χ' hd' hu hu'
  rw [D.naut.unr_eq_lpUnr _ hu2, D.naut.frobEig_char χ χ' c' hu hu' hd' hc', hc]
  simp [h]

open Polynomial NumberField IsDedekindDomain in
private lemma exists_frobEig_etaT_inv_etaTinv (D : _root_.Formalism.BasicNotions.D7) (w : _root_.Formalism.BasicNotions.PlE D.host) :
    ∃ c : ℂ, c ≠ 0 ∧ D.naut.frobEig (D.naut.locG D.naut.etaT w) = {c} ∧
      D.naut.frobEig (D.naut.locG D.naut.etaTinv w) = {c⁻¹} := by
  have hu := D.naut.etaT_unr w
  have hcard : (D.naut.frobEig (D.naut.locG D.naut.etaT w)).card = 1 := by
    rw [D.naut.frobEig_card _ hu, D.naut.locG_dim]
  obtain ⟨c, hc⟩ := Multiset.card_eq_one.1 hcard
  have hne := D.naut.frobEig_ne_zero _ hu
  refine ⟨c, fun h0 => hne (by rw [hc, h0]; exact Multiset.mem_singleton_self 0), hc, ?_⟩
  rw [(D.naut.etaTinv_def w).2, hc]
  simp


open Polynomial NumberField IsDedekindDomain in
theorem _root_.GlobalTheory.TypeLeaf.twistInv_of_charLaws_multOne :
    ∀ D : _root_.Formalism.BasicNotions.D7, _root_.GlobalTheory.TypeLeaf.CharLaws D → _root_.GlobalTheory.TypeLeaf.MultOne D →
      _root_.GlobalTheory.TypeLeaf.TwistInv D := by
  intro D hlaw hmult
  have hdim : ∀ w : _root_.Formalism.BasicNotions.PlE D.host, D.naut.lpDim (D.naut.locG D.naut.etaT w) = 1 :=
    fun w => D.naut.locG_dim _ w
  have hdim' : ∀ w : _root_.Formalism.BasicNotions.PlE D.host, D.naut.lpDim (D.naut.locG D.naut.etaTinv w) = 1 :=
    fun w => D.naut.locG_dim _ w
  constructor
  · intro a π ha
    refine hmult a _ _ ha fun w => ?_
    obtain ⟨c, hc0, hc, hc'⟩ := exists_frobEig_etaT_inv_etaTinv D w
    rw [D.naut.locG_tw, D.naut.locG_tw, (hlaw w _ _ _ (hdim w) (hdim' w)).1,
      _root_.GlobalTheory.TypeLeaf.lpChar_eq_triv_of_mul_eq_one D w _ _ c c⁻¹ (D.naut.etaT_unr w)
        (D.naut.etaTinv_def w).1 (hdim' w) hc hc' (mul_inv_cancel₀ hc0),
      (hlaw w _ _ _ (hdim w) (hdim w)).2]
  · intro a π ha
    refine hmult a _ _ ha fun w => ?_
    obtain ⟨c, hc0, hc, hc'⟩ := exists_frobEig_etaT_inv_etaTinv D w
    rw [D.naut.locG_tw, D.naut.locG_tw, (hlaw w _ _ _ (hdim' w) (hdim w)).1,
      _root_.GlobalTheory.TypeLeaf.lpChar_eq_triv_of_mul_eq_one D w _ _ c⁻¹ c (D.naut.etaTinv_def w).1
        (D.naut.etaT_unr w) (hdim w) hc' hc (inv_mul_cancel₀ hc0),
      (hlaw w _ _ _ (hdim w) (hdim w)).2]

end GlobalTheory.TypeLeaf
end

section

noncomputable section

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Cut

namespace GlobalTheory.CutTrivIne

section Gen

variable {l : ℕ} [Fact l.Prime] {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω]
  {Gw : Subgroup (Ω ≃ₐ[E] Ω)} {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
  (Bw : LocBridge l E Ω Gw O) [IsDomain O]



theorem eq_zero_of_phi (k : ℕ) (x : KOG O k) (hx : Br.phi Bw k x = 0) : x = 0 := by
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  have h1 : Br.vecS Bw k v ∈ stdG (Br.Ow Bw) (Br.LLw Bw) k :=
    (Submodule.Quotient.mk_eq_zero _).1 hx
  obtain ⟨u, hu⟩ := h1
  refine (Submodule.Quotient.mk_eq_zero _).2 ⟨fun j => Bw.eO.symm (u j), ?_⟩
  funext j
  apply (Br.toLLK Bw).injective
  have h2 := Br.toLLK_alg Bw (Bw.eO.symm (u j))
  rw [RingEquiv.apply_symm_apply] at h2
  exact h2.trans (congrFun hu j)

end Gen

theorem actD_eq_of_eq_one {G LL O : Type} [Group G] [Field LL] [CommRing O] [Algebra O LL] {k : ℕ}
    (M : G →* Matrix (Fin k) (Fin k) LL) (L : Lattice (O := O) (matRep M)) (g : G) (hg : M g = 1)
    (x : (Fin k → LL) ⧸ L.T) : actD L g x = x := by
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  have h : matRep M g v = v := by
    show Matrix.toLin' (M g) v = v
    rw [hg, Matrix.toLin'_one]
    rfl
  show Submodule.Quotient.mk (matRep M g v) = _
  rw [h]

theorem chiRatO_one (D : D7) (i : D.nd.Loc) (γ : GE D.nd) : chiRatO D.nd i 1 γ = 1 := by
  simp [chiRatO, twistM]



theorem main : ∀ (D : D7) (i : D.nd.Loc) (C : Submodule (D.nd.O i) (GE D.nd → KOG (D.nd.O i) 1)), ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)), (∀ f ∈ C, locFun i (chiRatO D.nd i 1) w hw f ∈ Z1urD (Br.locLat D.nbr i w hw (chiRatO D.nd i 1)) (Br.inert D.nbr i w hw)) → resIne i C w = ⊥ := by
  intro D i C w hw h
  rw [eq_bot_iff]
  rintro _ ⟨f, hf, rfl⟩
  obtain ⟨x, hx⟩ := h f hf
  rw [Submodule.mem_bot]
  funext γ
  obtain ⟨g, hg⟩ := (Br.ι_bijective (D.nbr i w hw)).2 ⟨γ.1, Ine_le_Dec _ γ.2⟩
  have hg' : ((Br.iota D.nbr i w hw g : Gw D.nd w) : GE D.nd) = γ.1 := congrArg Subtype.val hg
  have hmem : g ∈ Br.inert D.nbr i w hw := by
    show ((Br.iota D.nbr i w hw g : Gw D.nd w) : GE D.nd) ∈ Ine (F := D.host.E) (D.nd.plOm.1 w)
    rw [hg']
    exact γ.2
  have h1 : Br.loc D.nbr i w hw (chiRatO D.nd i 1) g = 1 := by
    show (algebraMap (Br.Ow (D.nbr i w hw)) (Br.LLw (D.nbr i w hw))).mapMatrix
      ((D.nbr i w hw).eO.toRingHom.mapMatrix
        (chiRatO D.nd i 1 ((Br.iota D.nbr i w hw g : Gw D.nd w) : GE D.nd))) = 1
    rw [chiRatO_one, map_one, map_one]
  have h2 := hx g hmem
  rw [actD_eq_of_eq_one _ _ g h1, sub_self] at h2
  have h3 := eq_zero_of_phi (D.nbr i w hw) 1 _ h2
  rw [hg'] at h3
  exact h3

end GlobalTheory.CutTrivIne

end
end

section

noncomputable section

namespace GlobalTheory.TypeLeaf

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.ArithmeticCylinders Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain

theorem pointPar_of_twist (D : D7) (hT : TwistInv D) (hc : D.naut.csd D.naut.etaT)
    (hz : ∀ τ : D.host.E →+* ℂ, ∀ z ∈ D.naut.infG D.naut.etaTinv τ,
      ∃ k : ℤ, z + ((-(D.R.t : ℝ) / 2 : ℝ) : ℂ) = (k : ℂ)) : PointPar D := by
  intro i x π hx
  obtain ⟨P, -, hB⟩ := hx
  have hp : (⟨D.R.r, D.naut.tw π D.naut.etaTinv, 1⟩ : Formalism.BasicNotions.Part D.naut.CG) ∈
      twistIso D.nd D.naut ([⟨D.R.r, π, 1⟩] ++ [muPart D.nd D.naut i]) D.naut.etaTinv :=
    List.mem_cons_self
  obtain ⟨h1, -, h2⟩ := hB.1 _ hp
  refine ⟨?_, (D.naut.ralg_def π).2 fun τ => ?_⟩
  · have := D.naut.csd_tw _ _ hc h2
    rwa [hT.2 _ π h1] at this
  obtain ⟨s, hs⟩ := Multiset.card_eq_one.mp (D.naut.infG_card D.naut.etaTinv τ)
  obtain ⟨k0, hk0⟩ := hz τ s (by rw [hs]; exact Multiset.mem_singleton_self s)
  have hW : (D.naut.infWt i τ).Nodup ∧
      ∀ z ∈ D.naut.infWt i τ, ∃ k : ℤ, z = (k : ℂ) + ((D.R.nV : ℂ) - 1) / 2 := by
    rw [D.nbc.embAV_inf i P]
    exact D.nbc.infW_alg _ _ τ
  have hle : (D.naut.infG π τ).map (· + s) ≤ D.naut.infWt i τ := by
    rw [← hB.2.2.2.2.2 τ, ← D.naut.infG_tw π _ τ s hs]
    simp [isoInf, twistIso]
  refine ⟨Multiset.Nodup.of_map _ (Multiset.nodup_of_le hle hW.1), fun y hy => ?_⟩
  obtain ⟨k, hk⟩ := hW.2 _ (Multiset.mem_of_le hle (Multiset.mem_map_of_mem _ hy))
  refine ⟨k - k0, ?_⟩
  rw [Ranks.nV] at hk
  push_cast at hk hk0 ⊢
  linear_combination hk - hk0

end GlobalTheory.TypeLeaf
end
end

section

noncomputable section

namespace GlobalTheory.TypeLeaf

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.ArithmeticCylinders Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain

theorem isOpen_ker_map_of_isOpen_ker {Γ A B : Type} [Group Γ] [TopologicalSpace Γ] [CommRing A] [CommRing B]
    [TopologicalSpace A] [IsTopologicalRing A] {n : ℕ} (f : A →+* B) (hf : IsOpen ((RingHom.ker f : Ideal A) : Set A))
    (ρ : Γ →* GL (Fin n) A) (hρ : Continuous (fun g => ((ρ g : GL _ _) : Matrix (Fin n) (Fin n) A))) :
    IsOpen (((Matrix.GeneralLinearGroup.map f).comp ρ).ker : Set Γ) := by
  classical

  let U : Set (Matrix (Fin n) (Fin n) A) :=
    {M | ∀ i j, M i j - (1 : Matrix (Fin n) (Fin n) A) i j ∈ RingHom.ker f}
  have hU : IsOpen U := by
    have : U = ⋂ i, ⋂ j, (fun M : Matrix (Fin n) (Fin n) A =>
        M i j - (1 : Matrix (Fin n) (Fin n) A) i j) ⁻¹' ((RingHom.ker f : Ideal A) : Set A) := by
      ext M; simp [U]
    rw [this]
    refine isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => ?_
    exact hf.preimage ((continuous_id.matrix_elem i j).sub continuous_const)

  have hker : (((Matrix.GeneralLinearGroup.map f).comp ρ).ker : Set Γ) =
      (fun g => ((ρ g : GL _ _) : Matrix (Fin n) (Fin n) A)) ⁻¹' U := by
    ext g
    simp only [SetLike.mem_coe, MonoidHom.mem_ker, MonoidHom.comp_apply, Set.mem_preimage, U,
      Set.mem_ofPred_eq, RingHom.mem_ker, map_sub, sub_eq_zero]
    rw [Units.ext_iff]
    change f.mapMatrix ((ρ g : GL _ _) : Matrix (Fin n) (Fin n) A) =
      ((1 : GL (Fin n) B) : Matrix (Fin n) (Fin n) B) ↔ _
    rw [Units.val_one, ← Matrix.ext_iff]
    refine forall_congr' fun i => forall_congr' fun j => ?_
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.one_apply]
    split_ifs <;> simp
  rw [hker]
  exact hU.preimage hρ

theorem redF_ker_isOpen (D : D7) (i : D.nd.Loc) (ρ : G D.host.E D.nd.Om →* GL (Fin D.R.r) (D.nd.O i))
    (hρ : Continuous (fun g => ((ρ g : GL _ _) : Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O i)))) :
    IsOpen ((redF D i ρ).ker : Set (G D.host.E D.nd.Om)) := by

  have hk : ((RingHom.ker ((D.naut.kFbar i).comp (IsLocalRing.residue (D.nd.O i))) : Ideal (D.nd.O i)) :
      Set (D.nd.O i)) = (IsLocalRing.maximalIdeal (D.nd.O i) : Set (D.nd.O i)) := by
    ext x
    simp [RingHom.mem_ker, IsLocalRing.residue_eq_zero_iff]
  have hm : IsOpen (IsLocalRing.maximalIdeal (D.nd.O i) : Set (D.nd.O i)) := by
    simpa using (isAdic_iff.mp (D.nd.O_adic i)).1 1
  exact isOpen_ker_map_of_isOpen_ker _ (hk ▸ hm) ρ hρ

end GlobalTheory.TypeLeaf
end
end

section

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass

namespace GlobalTheory.StepGlobalPf

variable {D : D7} (i : D.nd.Loc)

theorem mapM_twistM {k : ℕ} (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) (χ : GE D.nd →* (D.nd.O i)ˣ)
    (g : GE D.nd) :
    mapM (toK D.nd i) (twistM M χ) g = toK D.nd i ((χ g : (D.nd.O i)ˣ) : D.nd.O i) • mapM (toK D.nd i) M g := by
  ext a b
  simp [mapM, twistM, RingHom.mapMatrix_apply, Matrix.map_apply]

variable (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
  (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)

theorem chi_one_eq_one (hD : TruncatedSeriesCountingIdentities.SemisimpleDecomposition i r ρ π) {γ : GE D.nd} (hγ : r π γ = 1) : chiU D.nd i 1 γ = 1 := by
  obtain ⟨e, he⟩ := hD
  have ht : 0 < D.R.t := D.R.t_odd.pos
  set u := e.symm (0, Pi.single (⟨0, ht⟩ : Fin D.R.t) 1) with hu
  have h := congrArg (fun p => p.2 (⟨0, ht⟩ : Fin D.R.t)) (he γ u)
  have h1 : mapM (toK D.nd i) (rO D.nd i r π) γ = 1 := by
    simp [mapM, rO, hγ]
  simp only [h1, Matrix.one_mulVec, hu, LinearEquiv.apply_symm_apply, Pi.single_eq_same, mul_one] at h
  apply Units.ext
  apply IsFractionRing.injective (D.nd.O i) (KK D.nd i)
  simpa using h.symm

theorem noChiOff (Xs : Set (D.nd.X i)) (hG6 : TruncatedSeriesCountingIdentities.admG6 i r) : GlobalTheory.Cut.NoChiOff i r Xs := by
  intro x _ hxZ u hu
  by_contra hu0
  refine hxZ (hG6 x ⟨u, hu0, fun g => ?_⟩)
  have h := hu g
  rw [rTwO, mapM_twistM, Matrix.smul_mulVec] at h
  conv_rhs => rw [← h]
  rw [smul_smul, ← map_mul, MonoidHom.inv_apply, ← Units.val_mul, mul_inv_cancel, Units.val_one, map_one,
    one_smul]

theorem unrOut (Xs : Set (D.nd.X i)) (hG4 : TruncatedSeriesCountingIdentities.admG4 i r) (hD : TruncatedSeriesCountingIdentities.SemisimpleDecomposition i r ρ π) :
    GlobalTheory.Cut.UnrOut i r Xs := by
  intro v hvl hvS hvQ x _ γ hγ
  have hχ := chi_one_eq_one i r ρ π hD (hG4 π v hvl hvS hvQ γ hγ)
  have hx : rO D.nd i r x γ = 1 := by simp [rO, hG4 x v hvl hvS hvQ γ hγ]
  rw [rTwO, twistM]
  simp [hx, hχ]

theorem atS (Xs : Set (D.nd.X i)) (hG5 : TruncatedSeriesCountingIdentities.admG5 i r) (hG5x : TruncatedSeriesCountingIdentities.TameGeneratorConditions i) :
    ∀ v ∈ D.nd.S i, (GlobalTheory.Cut.QuadAt i r Xs v ∧ IsUnit (D.nd.zeta i v - 1)) ∨ GlobalTheory.Cut.PolyAt i r Xs π v := by
  intro v hv
  have hS := ((D.nd.S_def i v).1 hv).1
  have hv5 := hG5 v (Or.inl hv)
  have hv5x := hG5x v (Or.inl hv)
  have hp : (∃ k, v ∈ placesOver D.host.E (D.host.g k)) ∨
      (v ∈ placesOver D.host.E D.host.pde ∨
        (D.nd.l i = D.host.pde ∧ v ∈ placesOver D.host.E D.host.pde')) := by
    rcases hS with h | h | h
    · exact Or.inl ⟨0, h⟩
    · exact Or.inl ⟨1, h⟩
    · right
      split_ifs at h with hl
      · exact Or.inr ⟨hl, h⟩
      · exact Or.inl h
  rcases hp with hk | hp
  · right
    obtain ⟨Pp, hu, hP⟩ := hv5.2 hk hv hv5x.1
    refine ⟨Pp, fun x _ γ hγ => hP x γ hγ, ?_⟩
    rw [Polynomial.eval_map]
    have hz : D.nd.zeta i v = evT D.nd i π (algebraMap (D.nd.O i) (D.nd.T i) (chi1 D.nd i (D.nd.gam0 i v))) := rfl
    rw [hz, Polynomial.eval₂_at_apply]
    exact hu.map _
  · left
    exact ⟨fun x _ γ hγ => ((hv5.1 (Or.inr hp)) x).1 γ hγ, hv5x.2.2.2 hv hp⟩

theorem atQ (Xs : Set (D.nd.X i)) (hG5 : TruncatedSeriesCountingIdentities.admG5 i r) (hG5x : TruncatedSeriesCountingIdentities.TameGeneratorConditions i) :
    ∀ v ∈ D.nd.Q i, GlobalTheory.Cut.QuadAt i r Xs v ∧ D.nd.zeta i v ≠ 1 := fun v hv =>
  ⟨fun x _ γ hγ => ((hG5 v (Or.inr hv)).1 (Or.inl hv) x).1 γ hγ, (hG5x v (Or.inr hv)).2.2.1 hv⟩


end GlobalTheory.StepGlobalPf
end

section

section
open GlobalTheory.GLq Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical

namespace CompanionTheory.Member.TraceCoefficientSum

variable {G : Type} [Group G] [Fintype G]

theorem coeff_zOf (χ : G → ℂ) (x : G) : (zOf χ).coeff x = χ 1 / (Fintype.card G : ℂ) * χ x⁻¹ := by
  simp [zOf, MonoidAlgebra.coeff_sum, Finsupp.single_apply]

theorem eq_sum_single (a : MonoidAlgebra ℂ G) : a = ∑ x, MonoidAlgebra.single x (a.coeff x) := by
  ext y
  simp [MonoidAlgebra.coeff_sum, Finsupp.single_apply]

theorem coeff_mul_zOf (a : MonoidAlgebra ℂ G) (χ : G → ℂ) :
    (a * zOf χ).coeff 1 = χ 1 / (Fintype.card G : ℂ) * ∑ x, a.coeff x * χ x := by
  conv_lhs => rw [eq_sum_single a]
  rw [Finset.sum_mul, MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [MonoidAlgebra.coeff_single_mul_apply, coeff_zOf, mul_one, inv_inv]
  ring

theorem trace_alg (a : MonoidAlgebra ℂ G) (V : FDRep ℂ G) :
    ∑ x, a.coeff x * V.character x =
      LinearMap.trace ℂ V (Representation.asAlgebraHom (V.ρ : Representation ℂ G V) a) := by
  conv_rhs => rw [eq_sum_single a]

  rw [map_sum, map_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Representation.asAlgebraHom_single, map_smul, smul_eq_mul]
  rfl

theorem trace_nat (a : MonoidAlgebra ℂ G) (ha : a * a = a) (V : FDRep ℂ G) :
    ∃ m : ℕ, ∑ x, a.coeff x * V.character x = m := by
  have hi : IsIdempotentElem (Representation.asAlgebraHom (V.ρ : Representation ℂ G V) a) := by
    unfold IsIdempotentElem
    rw [← map_mul, ha]
  rw [trace_alg]
  exact ⟨_, (LinearMap.IsIdempotentElem.isProj_range _ hi).trace⟩

theorem re_nonneg (a : MonoidAlgebra ℂ G) (ha : a * a = a) (χ : G → ℂ) (hχ : IsIrr χ) :
    0 ≤ ((a * zOf χ).coeff 1).re := by
  obtain ⟨V, -, hV⟩ := hχ
  obtain ⟨m, hm⟩ := trace_nat a ha V
  rw [coeff_mul_zOf, ← hV 1, FDRep.char_one]
  simp only [← hV]
  rw [hm, ← Complex.ofReal_natCast, ← Complex.ofReal_natCast, ← Complex.ofReal_natCast m,
    ← Complex.ofReal_div, ← Complex.ofReal_mul, Complex.ofReal_re]
  positivity

end CompanionTheory.Member.TraceCoefficientSum

theorem CompanionTheory.Member.harishChandraSeriesWeight_nonneg_of_idempotent : ∀ (g : ℕ) [Fact g.Prime] (L : LabelDatum g) (n : ℕ) (a : MonoidAlgebra ℂ (Gn g n)), a * a = a → 0 ≤ (a.coeff 1).re → ∀ f, 0 ≤ wtC L a f := by
  intro g _ L n a ha h1 f
  refine div_nonneg ?_ h1
  unfold eSerC
  refine finsum_mem_induction (fun b => 0 ≤ ((a * b).coeff 1).re) (by simp) ?_ ?_
  · intro x y hx hy
    rw [mul_add, MonoidAlgebra.coeff_add, Finsupp.add_apply, Complex.add_re]
    exact add_nonneg hx hy
  · intro χ hχ
    exact CompanionTheory.Member.TraceCoefficientSum.re_nonneg a ha χ hχ.1

end

section
open GlobalTheory.GLq Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical
theorem _root_.GlobalTheory.Adopt.harishChandraSeriesWeight_nonneg_of_idempotent_glnPrime : ∀ (g : ℕ) [Fact g.Prime] (L : LabelDatum g) (n : ℕ) (a : MonoidAlgebra ℂ (Gn g n)), a * a = a → 0 ≤ (a.coeff 1).re → ∀ f, 0 ≤ wtC L a f := by
  first | exact @CompanionTheory.Member.harishChandraSeriesWeight_nonneg_of_idempotent | exact CompanionTheory.Member.harishChandraSeriesWeight_nonneg_of_idempotent | (intros; apply CompanionTheory.Member.harishChandraSeriesWeight_nonneg_of_idempotent <;> assumption)

end
end

section

open GlobalTheory.GLq Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical

namespace GlobalTheory.GLq.TrIdem

theorem zOf_coeff {G : Type} [Group G] [Fintype G] (χ : G → ℂ) (y : G) :
    (zOf χ).coeff y = χ 1 / (Fintype.card G : ℂ) * χ y⁻¹ := by
  simp only [zOf, MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply, MonoidAlgebra.single_apply,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem coeff_mul_zOf_one {G : Type} [Group G] [Fintype G] (a : MonoidAlgebra ℂ G) (χ : G → ℂ) :
    (a * zOf χ).coeff 1 = χ 1 / (Fintype.card G : ℂ) * tr a χ := by
  rw [MonoidAlgebra.coeff_mul, Finsupp.sum_fintype _ _ (by simp)]
  simp only [tr, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finsupp.sum_fintype _ _ (by simp)]
  simp only [zOf_coeff, mul_eq_one_iff_eq_inv', Finset.sum_ite_eq', Finset.mem_univ, if_true, inv_inv]
  ring

theorem trace_asAlgebraHom {G : Type} [Group G] [Fintype G] (V : FDRep ℂ G) (a : MonoidAlgebra ℂ G) :
    LinearMap.trace ℂ V (Representation.asAlgebraHom (k := ℂ) (V.ρ : Representation ℂ G V) a) =
      tr a V.character := by
  simp only [tr, Representation.asAlgebraHom_def, MonoidAlgebra.lift_apply, FDRep.character]

  rw [Finsupp.sum_fintype _ _ (by simp), map_sum]
  simp

theorem tr_idem_nat {G : Type} [Group G] [Fintype G] (a : MonoidAlgebra ℂ G) (χ : G → ℂ)
    (ha : a * a = a) (hχ : IsChar χ) : ∃ n : ℕ, tr a χ = n := by
  obtain ⟨V, hV⟩ := hχ
  have hc : V.character = χ := funext hV
  set f := Representation.asAlgebraHom (k := ℂ) (V.ρ : Representation ℂ G V) a with hf
  have hi : IsIdempotentElem f := by
    rw [IsIdempotentElem, hf, ← map_mul, ha]
  refine ⟨Module.finrank ℂ (LinearMap.range f), ?_⟩
  rw [← hc, ← trace_asAlgebraHom, ← hf]
  exact (LinearMap.IsIdempotentElem.isProj_range f hi).trace

theorem irr_one_pos {G : Type} [Group G] (χ : G → ℂ) (hχ : IsIrr χ) : ∃ d : ℕ, 0 < d ∧ χ 1 = d := by
  obtain ⟨V, hs, hV⟩ := hχ
  refine ⟨Module.finrank ℂ V, Nat.pos_of_ne_zero fun h => ?_, by rw [← hV, FDRep.char_one]⟩
  apply CategoryTheory.Simple.not_isZero V
  rw [CategoryTheory.Limits.IsZero.iff_id_eq_zero]
  have : Subsingleton V := Module.finrank_zero_iff.mp h
  ext x
  exact Subsingleton.elim _ _

end GlobalTheory.GLq.TrIdem

theorem GlobalTheory.GLq.trIdem : ∀ (G : Type) [Group G] [Fintype G] (a : MonoidAlgebra ℂ G) (χ : G → ℂ),
    (a * a = a → IsChar χ → ∃ n : ℕ, tr a χ = n) ∧ (IsIrr χ → ∃ d : ℕ, 0 < d ∧ χ 1 = d) ∧
      (a * zOf χ).coeff 1 = χ 1 / (Fintype.card G : ℂ) * tr a χ :=
  fun _ _ _ a χ => ⟨GlobalTheory.GLq.TrIdem.tr_idem_nat a χ, GlobalTheory.GLq.TrIdem.irr_one_pos χ,
    GlobalTheory.GLq.TrIdem.coeff_mul_zOf_one a χ⟩
end
