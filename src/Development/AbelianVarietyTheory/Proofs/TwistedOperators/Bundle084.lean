module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle006
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle035
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
public import Mathlib.MeasureTheory.Measure.Haar.MulEquivHaarChar
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle073
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwahoriProjSurjective
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Cartan
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasLenOfLatLen
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle038

@[expose] public section

section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.InertSupp ValuativeRel Matrix MeasureTheory
open GlobalTheory.IwahoriInj (Deep)

namespace GlobalTheory.JacquetExact

section Abstract

variable {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem exists_finset_of_mem_twKer {τ : Representation ℂ G W} {N : Subgroup G} {w : W}
    (hw : w ∈ twKer τ N 1) :
    ∃ S : Finset G, (∀ u ∈ S, u ∈ N) ∧ ∀ H : Subgroup G, (∀ u ∈ S, u ∈ H) → w ∈ twKer τ H 1 := by
  classical
  induction hw using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨u, v, rfl⟩ := hx
    refine ⟨{(u : G)}, by simp, fun H hH => ?_⟩
    simpa using GlobalTheory.IwahoriInj.sub_mem_twKer (π := τ) (hH u (by simp)) v
  | zero => exact ⟨∅, by simp, fun _ _ => zero_mem _⟩
  | add x y _ _ hx hy =>
    obtain ⟨S, hS, hx⟩ := hx
    obtain ⟨T, hT, hy⟩ := hy
    refine ⟨S ∪ T, fun u hu => (Finset.mem_union.1 hu).elim (hS u) (hT u), fun H hH => add_mem
      (hx H fun u hu => hH u (Finset.mem_union_left _ hu))
      (hy H fun u hu => hH u (Finset.mem_union_right _ hu))⟩
  | smul c x _ hx =>
    obtain ⟨S, hS, hx⟩ := hx
    exact ⟨S, hS, fun H hH => Submodule.smul_mem _ c (hx H hH)⟩

theorem map_mem_twKer {σ : Representation ℂ G V} {τ : Representation ℂ G W} (f : σ.IntertwiningMap τ)
    {H : Subgroup G} {v : V} (hv : v ∈ twKer σ H 1) : f v ∈ twKer τ H 1 := by
  have h : twKer σ H 1 ≤ (twKer τ H 1).comap f.toLinearMap := Submodule.span_le.2 (by
    rintro _ ⟨n, v, rfl⟩
    refine Submodule.subset_span ⟨n, f v, ?_⟩
    simp [f.isIntertwining])
  exact h hv

variable [TopologicalSpace G] [IsTopologicalGroup G]

theorem mem_twKer_of_compact {σ : Representation ℂ G V} {τ : Representation ℂ G W} (hτ : IsSmooth τ)
    (f : σ.IntertwiningMap τ) (hf : Function.Injective f) {H : Subgroup G} (hH : IsCompact (H : Set G))
    {v : V} (hv : f v ∈ twKer τ H 1) : v ∈ twKer σ H 1 := by
  have hσ : IsSmooth σ := (IsSubquotient.of_injective f hf).isSmooth hτ
  obtain ⟨v', hv', he⟩ := IwahoriOnto.exists_fixed_map_eq hσ hH (twKer σ H 1).mkQ v fun h hh =>
    (Submodule.Quotient.eq _).2 (GlobalTheory.IwahoriInj.sub_mem_twKer hh v)
  have h1 : v' - v ∈ twKer σ H 1 := (Submodule.Quotient.eq _).1 he
  have h2 : f v' ∈ twKer τ H 1 := by
    have := add_mem (map_mem_twKer f h1) hv
    rwa [map_sub, sub_add_cancel] at this
  have h3 : f v' ∈ fixed τ H := GlobalTheory.IwahoriInj.mem_fixed.2 fun h hh => by
    rw [← f.isIntertwining, GlobalTheory.IwahoriInj.mem_fixed.1 hv' h hh]
  have h4 : v' = 0 := hf ((GlobalTheory.IwahoriInj.eq_zero_of_fixed hτ hH h3 h2).trans (map_zero f).symm)
  rw [h4, zero_sub] at h1
  exact neg_mem_iff.1 h1

end Abstract

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : Type} [Fintype n] [DecidableEq n] {V W : Type} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup W] [Module ℂ W] {s : ℕ} {d : Fin s → ℕ}

theorem jacMap_injective (e : (Σ a, Fin (d a)) ≃ n) {σ : Representation ℂ (GL n k) V}
    {τ : Representation ℂ (GL n k) W} (hτ : IsSmooth τ) (f : σ.IntertwiningMap τ)
    (hf : Function.Injective f) : Function.Injective (jacMap e f) := by
  refine (injective_iff_map_eq_zero _).2 fun x hx => ?_
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  have h1 : f v ∈ twKer τ (unipRad k e) 1 := (Submodule.Quotient.mk_eq_zero _).1 hx
  let c : n → ℤ := fun i => (blk e i).val
  have hN : unipRad k e = unipOf k c := unipRad_eq_unipOf k fun i j => by simp [c]
  obtain ⟨S, hS, h2⟩ := exists_finset_of_mem_twKer h1
  have hcompact : ∃ H : Subgroup (GL n k), H ≤ unipOf k c ∧
      IsCompact (H : Set (GL n k)) ∧ ∀ u ∈ S, u ∈ H := by
    let K (m : ℕ) := GlobalTheory.IwahoriInj.grp k (GlobalTheory.UnipCompact.conc_mul_sub c m)
    have hentries {u : GL n k} (hu : u ∈ unipOf k c) :
        ∀ᶠ m : ℕ in Filter.atTop, ∀ i j, Deep ((m : ℤ) * (c i - c j)) (u.val i j) := by
      simp only [Filter.eventually_all]
      intro i j
      by_cases hij : c i < c j
      · filter_upwards [GlobalTheory.IwahoriInj.eventually_deep (u.val i j)] with m hm
        exact hm.mono (by nlinarith [Int.natCast_nonneg m])
      · rw [mem_unipOf.1 hu i j hij]
        refine Filter.Eventually.of_forall fun m => ?_
        by_cases heq : i = j
        · subst j
          simp [GlobalTheory.IwahoriInj.deep_zero_iff]
        · simp [one_apply_ne heq, GlobalTheory.IwahoriInj.deep_zero]
    have hmem : ∀ᶠ m in Filter.atTop, ∀ u ∈ S, u ∈ K m :=
      (Filter.eventually_all_finset S).2 fun u hu => by
        have hu' := hN ▸ hS u hu
        exact (hentries hu').and (hentries (inv_mem hu'))
    obtain ⟨m, hm⟩ := hmem.exists
    refine ⟨K m ⊓ unipOf k c, inf_le_right, ?_, fun u hu => ⟨hm u hu, hN ▸ hS u hu⟩⟩
    obtain ⟨_, _⟩ := Model.secondCountable_and_t2_local_field (k := k)
    have hclosed : IsClosed (unipOf k c : Set (GL n k)) := by
      have heq : (unipOf k c : Set (GL n k)) =
          ⋂ i, ⋂ j, ⋂ (_ : ¬ c i < c j), {g : GL n k | g.val i j = (1 : Matrix n n k) i j} := by
        ext g
        simp only [SetLike.mem_coe, mem_unipOf, Set.mem_iInter, Set.mem_ofPred_eq]
      rw [heq]
      exact isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ =>
        isClosed_eq (Units.continuous_val.matrix_elem i j) continuous_const
    rw [Subgroup.coe_inf]
    exact (GlobalTheory.IwahoriInj.isCompact_grp _).inter_right hclosed
  obtain ⟨H, hle, hH, hSH⟩ := hcompact
  refine (Submodule.Quotient.mk_eq_zero _).2 ?_
  exact GlobalTheory.IwahoriInj.twKer_mono (hle.trans hN.ge) (mem_twKer_of_compact hτ f hf hH (h2 H hSH))

theorem jacMap_surjective (e : (Σ a, Fin (d a)) ≃ n) {σ : Representation ℂ (GL n k) V}
    {τ : Representation ℂ (GL n k) W} (f : σ.IntertwiningMap τ)
    (hf : Function.Surjective f) : Function.Surjective (jacMap e f) := fun y => by
  obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  obtain ⟨v, rfl⟩ := hf w
  exact ⟨Submodule.Quotient.mk v, rfl⟩

theorem isSubquotient_jac (e : (Σ a, Fin (d a)) ≃ n) {π : Representation ℂ (GL n k) V}
    {τ : Representation ℂ (GL n k) W} (hτ : IsSmooth τ) (h : IsSubquotient π τ) :
    IsSubquotient (_root_.GlobalTheory.SmGL.jac e π) (_root_.GlobalTheory.SmGL.jac e τ) := by
  obtain ⟨S, f, hf⟩ := h
  let ι : S.toRepresentation.IntertwiningMap τ := ⟨S.toSubmodule.subtype, fun _ => rfl⟩
  exact (IsSubquotient.of_surjective _ (jacMap_surjective e f hf)).trans
    (.of_injective _ (jacMap_injective e hτ ι Subtype.val_injective))

end Local

theorem inSupport_of_isSubquotient (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (n : Type) [Fintype n] [DecidableEq n] (V : Type) [AddCommGroup V]
    [Module ℂ V] (W : Type) [AddCommGroup W] [Module ℂ W] (π : Representation ℂ (GL n k) V)
    (τ : Representation ℂ (GL n k) W) (χ : kˣ →* ℂˣ) (hτ : IsSmooth τ) (h : IsSubquotient π τ)
    (hχ : InSupport π χ) : InSupport τ χ := by
  obtain ⟨s, d, e, a, ha, Y, i1, i2, σ, hσ, hsub, hact⟩ := hχ
  exact ⟨s, d, e, a, ha, Y, i1, i2, σ, hσ, hsub.trans (isSubquotient_jac e hτ h), hact⟩

end GlobalTheory.JacquetExact
end
end

section

open MeasureTheory Topology Matrix NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx GlobalTheory.ModuLR
open scoped NNReal ENNReal TensorProduct

theorem _root_.GlobalTheory.T.haarModulusOfUnit_completionsAtPlaces_eq_prod_norm : ∀ (F : Type) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F))) (x : SPart F S), IsUnit x → (modu (SPart F S) x : ℝ) = ∏ v : S, ‖x v‖ := by
  first | exact @GlobalTheory.ModuPiLocal.modu_sPart | exact GlobalTheory.ModuPiLocal.modu_sPart | (intros; apply GlobalTheory.ModuPiLocal.modu_sPart <;> assumption)
end

section

open MeasureTheory Topology Matrix NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx GlobalTheory.ModuLR
open scoped NNReal ENNReal TensorProduct

theorem _root_.GlobalTheory.T.addEquivAddHaarChar_mulVec_artinian_reduced : ∀ (B : Type) [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [LocallyCompactSpace B] [T2Space B] [SecondCountableTopology B] [MeasurableSpace B] [BorelSpace B], IsArtinianRing B → IsReduced B → ∀ (κ : Type) [Fintype κ] [DecidableEq κ] [MeasurableSpace (κ → B)] [BorelSpace (κ → B)] (M : Matrix κ κ B) (hM : IsUnit M.det), addEquivAddHaarChar (mulVecCE M hM) = modu B M.det := by
  first | exact @GlobalTheory.ModuArtin.addEquivAddHaarChar_mulVecCE | exact GlobalTheory.ModuArtin.addEquivAddHaarChar_mulVecCE | (intros; apply GlobalTheory.ModuArtin.addEquivAddHaarChar_mulVecCE <;> assumption)
end

section

open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound

noncomputable section

namespace GlobalTheory.CellDisjoint

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def reix {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m] (e : n ≃ m) :
    GL n k →* GL m k :=
  Units.map (Matrix.reindexAlgEquiv k k e).toAlgHom.toMonoidHom

theorem reix_val {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m] (e : n ≃ m)
    (g : GL n k) : (reix e g).1 = g.1.submatrix e.symm e.symm := rfl

theorem reix_mem_KO {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m] (e : n ≃ m)
    {g : GL n k} (hg : g ∈ KO k n) : reix e g ∈ KO k m := by
  obtain ⟨h, rfl⟩ := hg
  refine ⟨Units.map (Matrix.reindexAlgEquiv 𝒪[k] 𝒪[k] e).toAlgHom.toMonoidHom h, Units.ext ?_⟩
  ext i j
  rfl

theorem reix_torusElt {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m] (e : n ≃ m)
    (ϖ : kˣ) (f : n → ℤ) : reix e (torusElt k n ϖ f) = torusElt k m ϖ (f ∘ e.symm) := by
  ext1
  rw [reix_val, val_torusElt, val_torusElt, submatrix_diagonal_equiv]
  rfl

theorem perm_of_eq {N : ℕ} {ϖ : kˣ} (hϖ : valuation k (ϖ : k) = uniformizer k) (a b : Fin N → ℤ)
    (x y : GL (Fin N) k) (hx : x ∈ KO k (Fin N)) (hy : y ∈ KO k (Fin N))
    (h : x * torusElt k (Fin N) ϖ a * y = torusElt k (Fin N) ϖ b) :
    List.Perm (List.ofFn a) (List.ofFn b) := by
  let σ := Tuple.sort (fun i => -a i)
  let τ := Tuple.sort (fun i => -b i)
  have ha : Antitone (a ∘ σ) := fun i j hij => by
    have := Tuple.monotone_sort (fun i => -a i) hij
    simp only [Function.comp_apply, neg_le_neg_iff] at this
    exact this
  have hb : Antitone (b ∘ τ) := fun i j hij => by
    have := Tuple.monotone_sort (fun i => -b i) hij
    simp only [Function.comp_apply, neg_le_neg_iff] at this
    exact this
  obtain ⟨S₁, h₁, e₁⟩ := Formalism.UG.P.cartan_perm_glint (L := k) 𝒪[k] σ.symm
  obtain ⟨S₂, h₂, e₂⟩ := Formalism.UG.P.cartan_perm_glint (L := k) 𝒪[k] σ
  obtain ⟨T₁, h₃, e₃⟩ := Formalism.UG.P.cartan_perm_glint (L := k) 𝒪[k] τ.symm
  obtain ⟨T₂, h₄, e₄⟩ := Formalism.UG.P.cartan_perm_glint (L := k) 𝒪[k] τ
  have hA : torusElt k (Fin N) ϖ a = S₁ * torusElt k (Fin N) ϖ (a ∘ σ) * S₂ := by
    ext1
    simp only [Units.val_mul, val_torusElt, e₁, e₂]
    exact Formalism.UG.P.cartan_diag_perm (fun i => (ϖ : k) ^ a i) σ
  have hB : torusElt k (Fin N) ϖ b = T₁ * torusElt k (Fin N) ϖ (b ∘ τ) * T₂ := by
    ext1
    simp only [Units.val_mul, val_torusElt, e₃, e₄]
    exact Formalism.UG.P.cartan_diag_perm (fun i => (ϖ : k) ^ b i) τ
  have E : (T₁⁻¹ * x * S₁) * torusElt k (Fin N) ϖ (a ∘ σ) * (S₂ * y * T₂⁻¹) =
      torusElt k (Fin N) ϖ (b ∘ τ) := by
    have h' : torusElt k (Fin N) ϖ (b ∘ τ) = T₁⁻¹ * torusElt k (Fin N) ϖ b * T₂⁻¹ := by
      rw [hB]; group
    rw [h', ← h, hA]; group
  have hab : a ∘ σ = b ∘ τ := by
    refine Formalism.UG.P.cartan_unique_gen 𝒪[k] (valuation k) (fun _ => Iff.rfl) (ϖ : k) ϖ.ne_zero
      (hϖ ▸ uniformizer_lt_one) (a ∘ σ) (b ∘ τ) ha hb (T₁⁻¹ * x * S₁)
      (mul_mem (mul_mem (inv_mem h₃) hx) h₁) (S₂ * y * T₂⁻¹) (mul_mem (mul_mem h₂ hy) (inv_mem h₄)) ?_
    have := congrArg Units.val E
    simp only [Units.val_mul, val_torusElt] at this
    simpa only [Units.val_mul, Matrix.mul_assoc] using this
  exact (Equiv.Perm.ofFn_comp_perm σ a).symm.trans (hab ▸ Equiv.Perm.ofFn_comp_perm τ b)

end GlobalTheory.CellDisjoint

namespace GlobalTheory.CellDisjoint

theorem dcell_pairwise_disjoint : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (ϖ : kˣ),
    valuation k (ϖ : k) = uniformizer k → ∀ (r l t : ℕ),
    Pairwise (Function.onFun Disjoint fun e : {e : Fin (l * t) → ℤ // Antitone e} =>
      (dcell ϖ (e.1 ∘ (blkEquiv l t).symm) : Set (GL (Fin r ⊕ Blocks l t) k))) := by
  intro k _ _ _ _ ϖ hϖ r l t a b hab
  refine Set.disjoint_left.2 fun g ha hb => hab (Subtype.ext ?_)
  obtain ⟨x, hx, y, hy, rfl⟩ := DoubleCoset.mem_doubleCoset.1 ha
  obtain ⟨x', hx', y', hy', e⟩ := DoubleCoset.mem_doubleCoset.1 hb
  have hK : ∀ z : GL (Fin r ⊕ Blocks l t) k, z ∈ (parahoric k (Fin r) (Blocks l t) : Set _) →
      z ∈ KO k (Fin r ⊕ Blocks l t) := fun z hz => (mem_parahoric.1 hz).1
  have e' : (x'⁻¹ * x) * mtor ϖ (a.1 ∘ (blkEquiv l t).symm) * (y * y'⁻¹) =
      mtor ϖ (b.1 ∘ (blkEquiv l t).symm) := by
    calc _ = x'⁻¹ * (x * mtor ϖ (a.1 ∘ (blkEquiv l t).symm) * y) * y'⁻¹ := by group
      _ = _ := by rw [e]; group
  let ρ : Fin (r + l * t) ≃ Fin r ⊕ Blocks l t :=
    finSumFinEquiv.symm.trans (Equiv.sumCongr (Equiv.refl (Fin r)) (blkEquiv l t))
  have hρ : ∀ f : Fin (l * t) → ℤ,
      (Sum.elim (0 : Fin r → ℤ) (f ∘ (blkEquiv l t).symm)) ∘ ρ.symm.symm = Fin.append (0 : Fin r → ℤ) f := by
    intro f
    funext j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · simp [ρ]
    · simp [ρ]
  have e'' := congrArg (reix (k := k) ρ.symm) e'
  simp only [map_mul, mtor, reix_torusElt, hρ] at e''
  have hp := perm_of_eq hϖ _ _ _ _ (mul_mem (reix_mem_KO _ (inv_mem (hK _ hx'))) (reix_mem_KO _ (hK _ hx)))
    (mul_mem (reix_mem_KO _ (hK _ hy)) (reix_mem_KO _ (inv_mem (hK _ hy')))) e''
  rw [List.ofFn_fin_append, List.ofFn_fin_append, List.perm_append_left_iff] at hp
  exact List.ofFn_injective (List.Perm.eq_of_sortedGE (List.sortedGE_ofFn_iff.2 a.2)
    (List.sortedGE_ofFn_iff.2 b.2) hp)

end GlobalTheory.CellDisjoint
end
end

section

open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound

noncomputable section

namespace GlobalTheory.TorusIntegrand

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem mtor_val {A D : Type} [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (ϖ : kˣ) (e : D → ℤ) :
    (mtor ϖ e : GL (A ⊕ D) k).val = diagonal (Sum.elim (fun _ => (1 : k)) (fun d => (ϖ : k) ^ e d)) := by
  unfold mtor
  rw [val_torusElt]
  congr 1
  funext i
  cases i <;> simp

theorem integral_and_iff (ϖ : kˣ) (hϖ : (ϖ : k) ∈ 𝒪[k]) (y : k) (n : ℤ) :
    (y ∈ 𝒪[k] ∧ y * (ϖ : k) ^ n ∈ 𝒪[k]) ↔ y * (ϖ : k) ^ (-max 0 (-n)) ∈ 𝒪[k] := by
  rcases le_or_gt 0 n with h | h
  · have h0 : -max 0 (-n) = 0 := by omega
    rw [h0, zpow_zero, mul_one]
    obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le h
    rw [zpow_natCast]
    exact ⟨fun h => h.1, fun hy => ⟨hy, Subring.mul_mem _ hy (Subring.pow_mem _ hϖ m)⟩⟩
  · have h0 : -max 0 (-n) = n := by omega
    rw [h0]
    refine ⟨fun h => h.2, fun hy => ⟨?_, hy⟩⟩
    obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ -n by omega)
    have hne : (ϖ : k) ≠ 0 := ϖ.ne_zero
    have : y = y * (ϖ : k) ^ n * (ϖ : k) ^ m := by
      rw [mul_assoc, ← zpow_natCast, ← zpow_add₀ hne, ← hm, add_neg_cancel, zpow_zero, mul_one]
    rw [this]
    exact Subring.mul_mem _ hy (Subring.pow_mem _ hϖ m)

theorem integrand : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (ϖ : kˣ), valuation k (ϖ : k) = uniformizer k →
    ∀ (A D E : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] [Fintype E] [DecidableEq E]
    (ξ : kˣ →* ℂˣ), IsUnitaryChar ξ → ∀ (e : D → ℤ) (x : Matrix (A ⊕ E) (A ⊕ D) k),
    datum ξ (x * (mtor ϖ e : GL (A ⊕ D) k).val) * starRingEnd ℂ (datum ξ x) =
      Set.indicator {y : Matrix (A ⊕ E) (A ⊕ D) k | InSupp (y * (mtor ϖ (fun i => -max 0 (-e i)) : GL (A ⊕ D) k).val)}
        (fun _ => (1 : ℂ)) x := by
  intro k _ _ _ _ ϖ hϖv A D E _ _ _ _ _ _ ξ hξ e x
  have hϖ : (ϖ : k) ∈ 𝒪[k] := by
    rw [Valuation.mem_integer_iff, hϖv]
    exact uniformizer_lt_one.le
  have hA : ∀ (M : Matrix (A ⊕ E) (A ⊕ D) k) (g : D → ℤ) i a,
      (M * (mtor ϖ g : GL (A ⊕ D) k).val) i (.inl a) = M i (.inl a) := by
    intro M g i a
    rw [mtor_val, mul_diagonal]
    simp
  have hD : ∀ (M : Matrix (A ⊕ E) (A ⊕ D) k) (g : D → ℤ) i d,
      (M * (mtor ϖ g : GL (A ⊕ D) k).val) i (.inr d) = M i (.inr d) * (ϖ : k) ^ g d := by
    intro M g i d
    rw [mtor_val, mul_diagonal]
    simp
  have h11 : ∀ (M : Matrix (A ⊕ E) (A ⊕ D) k) (g : D → ℤ),
      (M * (mtor ϖ g : GL (A ⊕ D) k).val).toBlocks₁₁ = M.toBlocks₁₁ := by
    intro M g
    ext i j
    simp [toBlocks₁₁, hA]
  have hsupp : ∀ M : Matrix (A ⊕ E) (A ⊕ D) k, InSupp M ↔
      (∀ i a, M i (.inl a) ∈ 𝒪[k]) ∧ (∀ i d, M i (.inr d) ∈ 𝒪[k]) ∧
        valuation k M.toBlocks₁₁.det = 1 ∧ ∀ i j, valuation k (M (.inr i) (.inl j)) < 1 := by
    intro M
    unfold InSupp
    simp only [Sum.forall, forall_and]
    tauto
  have hsuppm : ∀ (M : Matrix (A ⊕ E) (A ⊕ D) k) (g : D → ℤ), InSupp (M * (mtor ϖ g : GL (A ⊕ D) k).val) ↔
      (∀ i a, M i (.inl a) ∈ 𝒪[k]) ∧ (∀ i d, M i (.inr d) * (ϖ : k) ^ g d ∈ 𝒪[k]) ∧
        valuation k M.toBlocks₁₁.det = 1 ∧ ∀ i j, valuation k (M (.inr i) (.inl j)) < 1 := by
    intro M g
    rw [hsupp, h11]
    simp only [hA, hD]
  have hQ : ((∀ i d, x i (.inr d) ∈ 𝒪[k]) ∧ ∀ i d, x i (.inr d) * (ϖ : k) ^ e d ∈ 𝒪[k]) ↔
      ∀ i d, x i (.inr d) * (ϖ : k) ^ (-max 0 (-e d)) ∈ 𝒪[k] := by
    simp only [← forall_and]
    exact forall_congr' fun i => forall_congr' fun d => integral_and_iff ϖ hϖ _ _
  have hboth : (InSupp x ∧ InSupp (x * (mtor ϖ e : GL (A ⊕ D) k).val)) ↔
      InSupp (x * (mtor ϖ (fun i => -max 0 (-e i)) : GL (A ⊕ D) k).val) := by
    rw [hsupp, hsuppm, hsuppm, ← hQ]
    tauto
  set S := {y : Matrix (A ⊕ E) (A ⊕ D) k | InSupp (y * (mtor ϖ (fun i => -max 0 (-e i)) : GL (A ⊕ D) k).val)} with hS
  unfold datum
  by_cases h2 : InSupp x
  · by_cases h1 : InSupp (x * (mtor ϖ e : GL (A ⊕ D) k).val)
    · rw [dite_eq_left h1, dite_eq_left h2, Set.indicator_of_mem (show x ∈ S from hboth.1 ⟨h2, h1⟩)]
      have hu : Units.mk0 _ h1.det_ne = Units.mk0 _ h2.det_ne := by
        ext
        simp [h11]
      rw [hu, ← map_inv, Complex.mul_conj, Complex.normSq_eq_norm_sq, hξ]
      simp
    · rw [dite_eq_right h1, Set.indicator_of_notMem (show x ∉ S from fun h => h1 (hboth.2 h).2)]
      simp
  · rw [dite_eq_right h2, Set.indicator_of_notMem (show x ∉ S from fun h => h2 (hboth.2 h).1)]
    simp

end GlobalTheory.TorusIntegrand
end
end

section

noncomputable section

open Matrix

namespace GlobalTheory.InertZeta

theorem smul_mem_integral_submodule_of_valuation_le_one {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ}
    {P : Submodule (Formalism.UG.intL L) (Fin n → L)} {x : L} (hx : Valued.v x ≤ 1) {w : Fin n → L} (hw : w ∈ P) :
    x • w ∈ P :=
  P.smul_mem (⟨x, hx⟩ : Formalism.UG.intL L) hw

theorem addVec : AddVec := by
  intro L _ _ n M k ρ e hM hρ he
  rcases he with rfl | ⟨i₀, hi₀⟩
  · refine ⟨M, by simpa using hM, ?_⟩
    refine sup_eq_left.2 ((Submodule.span_singleton_le_iff_mem _ _).2 (mem_rowLat.2 ⟨ρ, fun i => ?_, rfl⟩))
    exact (by simpa using hρ i : Valued.v (ρ i) ≤ 1)
  · have h0 : ρ i₀ ≠ 0 := fun h => by rw [h, map_zero] at hi₀; exact WithZero.exp_ne_zero hi₀.symm
    refine ⟨M.updateRow i₀ (ρ ᵥ* M), ?_, ?_⟩
    · rw [Matrix.vecMul_eq_sum, Matrix.det_updateRow_sum, smul_eq_mul, map_mul, hi₀, hM, ← WithZero.exp_add, add_comm]
    · apply le_antisymm
      · refine sup_le (rowLat_le.2 fun i => ?_) ((Submodule.span_singleton_le_iff_mem _ _).2 ?_)
        · by_cases hi : i = i₀
          · subst hi
            have hs : ρ ᵥ* M = ρ i • M i + ∑ j ∈ Finset.univ.erase i, ρ j • M j := by
              rw [Matrix.vecMul_eq_sum]; exact (Finset.add_sum_erase _ (fun j => ρ j • M j) (Finset.mem_univ _)).symm
            have : M i = (ρ i)⁻¹ • (M.updateRow i (ρ ᵥ* M)) i -
                ∑ j ∈ Finset.univ.erase i, ((ρ i)⁻¹ * ρ j) • (M.updateRow i (ρ ᵥ* M)) j := by
              rw [Matrix.updateRow_self, hs, smul_add, smul_smul, inv_mul_cancel₀ h0, one_smul, Finset.smul_sum]
              rw [add_sub_assoc, ← Finset.sum_sub_distrib]
              rw [Finset.sum_eq_zero, add_zero]
              intro j hj
              rw [Matrix.updateRow_ne (Finset.ne_of_mem_erase hj), smul_smul, sub_self]
            rw [this]
            have hv : Valued.v (ρ i)⁻¹ = WithZero.exp (-(e : ℤ)) := by rw [map_inv₀, hi₀, WithZero.exp_neg]
            refine Submodule.sub_mem _ (smul_mem_integral_submodule_of_valuation_le_one ?_ (row_mem_rowLat _ _)) (Submodule.sum_mem _ fun j _ => smul_mem_integral_submodule_of_valuation_le_one ?_ (row_mem_rowLat _ _))
            · rw [hv, ← WithZero.exp_zero, WithZero.exp_le_exp]; omega
            · rw [map_mul, hv]
              calc WithZero.exp (-(e : ℤ)) * Valued.v (ρ j) ≤ WithZero.exp (-(e : ℤ)) * WithZero.exp (e : ℤ) :=
                    mul_le_mul' le_rfl (hρ j)
                _ = 1 := by rw [← WithZero.exp_add, neg_add_cancel, WithZero.exp_zero]
          · have := row_mem_rowLat (M.updateRow i₀ (ρ ᵥ* M)) i
            rwa [Matrix.updateRow_ne hi] at this
        · have := row_mem_rowLat (M.updateRow i₀ (ρ ᵥ* M)) i₀
          rwa [Matrix.updateRow_self] at this
      · refine rowLat_le.2 fun i => ?_
        by_cases hi : i = i₀
        · subst hi
          rw [Matrix.updateRow_self]
          exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)
        · rw [Matrix.updateRow_ne hi]
          exact Submodule.mem_sup_left (row_mem_rowLat _ _)

end GlobalTheory.InertZeta
end
end
