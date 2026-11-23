module

public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle009
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle303
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle304
public import Development.AbelianVarietyTheory.Definitions.Foundations.GLintEqKOAndPrincEqKOne
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotCoboundaryConstantOne
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HodgeTateCupKummerClassesEqDlogDeterminant
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EventuallyAlgebraMapMemIntegers
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle234
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle255
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle233
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle271
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle101
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsTraceCompatibleTorusEmbeddingStandardTorus
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle305
public import Formalism.LocalToGlobal.JointCharacters.LocEMulLocE
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFinitePlaceIdempotentBaseChangeAdeles
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf

@[expose] public section

section

open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups TensorProduct

theorem _root_.GlobalTheory.T.kummerCharacters_invariant_compatible_family : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (l : ℕ) [Fact l.Prime], [IsAlgClosed Ω] → JHol X → ∀ (N w : ℕ) (c : Fin (w + 1) → X.Khat l), (∀ i, c i ∈ X.A l) → (∀ γ ∈ Gam N l, ∀ i, c i = ∑ k, (cf w (γ : Matrix (Fin 2) (Fin 2) ℤ) i k : ℤ_[l]) • X.kmap l (X.sl (ofSL γ)).toRingEquiv (c k)) → ∃ Φ, IsFam l w (Gam N l) Φ ∧ ∀ n i, Kum X l n (c i) (fun δ => AddMonoidAlgebra.coeff (Φ n δ) (Finsupp.single 0 (i : ℕ) + Finsupp.single 1 (w - (i : ℕ)))) := by
  first | exact @GlobalTheory.KZ.H3.kum_family | exact GlobalTheory.KZ.H3.kum_family | (intros; apply GlobalTheory.KZ.H3.kum_family <;> assumption)
end

section

open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups TensorProduct

theorem _root_.GlobalTheory.T.kummerPotentialRelation_linear_hecke_stable : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (l : ℕ) [Fact l.Prime], (∀ b b' F F', Rel X l b F → Rel X l b' F' → Rel X l (b + b') (F + F')) ∧ Rel X l 0 0 ∧ (∀ (c : ℤ_[l]) b F, Rel X l b F → Rel X l (c • b) (c • F)) ∧ (∀ (m : Matrix (Fin 2) (Fin 2) ℤ) b F, Rel X l b F → Rel X l (X.act l m b) (opP ℤ_[l] m F)) ∧ (∀ (N : ℕ) (T : Letter) b F, Rel X l b F → Rel X l (X.op N l T b) (opL ℤ_[l] N l T F)) := by
  first | exact @GlobalTheory.KZ.H3.rel_ops | exact GlobalTheory.KZ.H3.rel_ops | (intros; apply GlobalTheory.KZ.H3.rel_ops <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.NTheta IsDedekindDomain NumberField GlobalTheory.SplitHecke
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdelicU.SplitFrame

variable {D : D7} {e : AE D} {v : HeightOneSpectrum (𝓞 D.host.F)} {π : AE D →+* Fv D.host.F v}

theorem map_map_sndA {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] (u : HeightOneSpectrum (𝓞 F))
    (z : AF F ⊗[F] E) :
    Algebra.TensorProduct.map (evalV F u) (AlgHom.id F E) (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E) z) =
      compFin F E u z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add (f := _), hx, hy]
  | tmul a x => rfl

theorem vecLoc_finPart {n : ℕ} (u : HeightOneSpectrum (𝓞 D.host.F)) (e : AE D) (y : Fin n → AE D) :
    vecLoc u (fun i => finPart D (e * y i)) =
      compFin D.host.F D.host.E u e • fun i => compFin D.host.F D.host.E u (y i) :=
  funext fun i => (map_map_sndA u (e * y i)).trans ((compFin D.host.F D.host.E u).map_mul e (y i))

theorem compFin_eq_zero (he : IsSplitIdem D e) (hπ : Chart e v π) {u : HeightOneSpectrum (𝓞 D.host.F)}
    (hu : u ≠ v) : compFin D.host.F D.host.E u e = 0 := by
  obtain ⟨h1, h2, v', ε, ⟨α, rfl, -, ha⟩, hε⟩ := he
  have p1 : π e = 1 := by
    have := (hπ.2.1 (1 - e)).2 (by rw [mul_sub, mul_one, h1, sub_self])
    rw [map_sub, map_one, sub_eq_zero] at this
    exact this.symm
  have p2 : π (cA D e) = 0 := (hπ.2.1 _).2 h2
  have p3 : evalV D.host.F v α = 1 := by
    have := hπ.2.2.1 (pairA D.host.F 0 α)
    rw [← hε, map_add (f := _), p1, p2, add_zero] at this
    exact this.symm
  have hv : v = v' := by
    by_contra hne
    rw [ha v hne] at p3
    exact zero_ne_one p3
  subst hv
  have p4 : compFin D.host.F D.host.E u (e + cA D e) = 0 := by
    rw [hε]
    change (evalV D.host.F u α) ⊗ₜ[D.host.F] (1 : D.host.E) = 0
    rw [ha u hu, TensorProduct.zero_tmul]
  have p5 : e = e * (e + cA D e) := by rw [mul_add, h1, h2, add_zero]
  rw [p5, map_mul, p4, mul_zero]

theorem mem_latHat_iff_of_support {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} (h : IsCMExt F E σ) {n : ℕ} {v : HeightOneSpectrum (𝓞 F)} (τ : E →ₐ[F] Fv F v)
    {L : Submodule (𝓞 E) (Fin n → E)} (hL : L.FG) {y : Fin n → Af F ⊗[F] E} {z : Fin n → Fv F v}
    (hv : vecLoc v y = splitIncl h τ z) (hu : ∀ u, u ≠ v → vecLoc u y = 0) :
    y ∈ Formalism.MainNotions.StandardLattice.latHat F E (L : Set (Fin n → E)) ↔ z ∈ splitLat τ L := by
  rw [mem_latHat_iff hL, ← splitIncl_mem_latLoc_iff h, ← hv]
  refine ⟨fun h => h v, fun h u => ?_⟩
  by_cases huv : u = v
  · subst huv; exact h
  · rw [hu u huv]; exact zero_mem _

theorem vecLoc_self (he : IsSplitIdem D e) (hπ : Chart e v π) {n : ℕ} (y : Fin n → AE D) :
    vecLoc v (fun i => finPart D (e * y i)) = splitIncl (isCMExt_host D) (chartEmb hπ) (fun k => π (y k)) := by
  have : (fun k => π (y k)) = splitVec (chartEmb hπ) (fun k => compFin D.host.F D.host.E v (y k)) :=
    funext fun k => chart_eq_splitProj hπ _
  rw [this, splitIncl_splitVec, vecLoc_finPart, compFin_eq_splitIdem he hπ]

theorem vecLoc_ne (he : IsSplitIdem D e) (hπ : Chart e v π) {n : ℕ} (y : Fin n → AE D)
    (u : HeightOneSpectrum (𝓞 D.host.F)) (hu : u ≠ v) : vecLoc u (fun i => finPart D (e * y i)) = 0 := by
  rw [vecLoc_finPart, compFin_eq_zero he hπ hu]
  exact funext fun i => zero_mul _

theorem lamHat_eq (V : HSp D) :
    LamHat V = Formalism.MainNotions.StandardLattice.latHat D.host.F D.host.E (frameLat V : Set (Fin V.rank → D.host.E)) :=
  congrArg (Formalism.MainNotions.StandardLattice.latHat D.host.F D.host.E) (hermitianSpaceBaseLattice_eq_frameLattice V)

theorem mem_lamHat_iff (he : IsSplitIdem D e) (hπ : Chart e v π) (V : HSp D) (y : Fin V.rank → AE D) :
    (fun i => finPart D (e * y i)) ∈ LamHat V ↔ (fun k => π (y k)) ∈ splitLat (chartEmb hπ) (frameLat V) := by
  rw [lamHat_eq]
  exact mem_latHat_iff_of_support (isCMExt_host D) _ (frameLat_fg V) (vecLoc_self he hπ y) (vecLoc_ne he hπ y)

theorem frame_iff_isSplitBasis : ∀ {D : D7} {e : AE D} {v : HeightOneSpectrum (𝓞 D.host.F)}
    {π : AE D →+* Fv D.host.F v}, IsSplitIdem D e → ∀ (hπ : Chart e v π) (V : HSp D)
    (β : GL (Fin V.rank) (Fv D.host.F v)),
    Frame V e π β ↔ GlobalTheory.AdelicU.IsSplitBasis (GlobalTheory.AdelicU.chartEmb hπ) (GlobalTheory.AdelicU.frameLat V) β := by
  intro D e v π he hπ V β
  refine ⟨fun h u => ?_, fun h y => ?_⟩
  · choose y hy using fun k => hπ.1 ((β.1 *ᵥ u) k)
    have h1 := h y
    rw [mem_lamHat_iff he hπ, show (fun k => π (y k)) = β.1 *ᵥ u from funext hy, Matrix.mulVec_mulVec,
      Units.inv_mul, Matrix.one_mulVec] at h1
    simpa only [isInt_Ov] using h1.symm
  · rw [mem_lamHat_iff he hπ, h.mem_iff]
    simp only [isInt_Ov]

end GlobalTheory.AdelicU.SplitFrame
end

section

open Formalism.UG GlobalTheory.PRep GlobalTheory.LFun

namespace GlobalTheory.LFun


open Polynomial in
theorem exists_multiset_esymm_eq (n : ℕ) (e : ℕ → ℂ) (h0 : e 0 = 1) (hn : e n ≠ 0) :
    ∃ A : Multiset ℂ, A.card = n ∧ (0 : ℂ) ∉ A ∧ ∀ j ≤ n, A.esymm j = e j := by
  set p : ℂ[X] := ∑ k ∈ Finset.range (n + 1), monomial k ((-1) ^ (n - k) * e (n - k)) with hp
  have hc : ∀ k, p.coeff k = if k ≤ n then (-1) ^ (n - k) * e (n - k) else 0 := fun k => by
    rw [hp, finsetSum_coeff]
    simp only [coeff_monomial_apply, Finset.sum_ite_eq', Finset.mem_range, Nat.lt_succ_iff]
  have hle : p.natDegree ≤ n := natDegree_le_iff_coeff_eq_zero.2 fun k hk => by rw [hc, if_neg (by omega)]
  have hcn : p.coeff n = 1 := by simp [hc, h0]
  have hd : p.natDegree = n := natDegree_eq_of_le_of_coeff_ne_zero hle (by simp [hcn])
  have hl : p.leadingCoeff = 1 := by rw [leadingCoeff, hd, hcn]
  have hr : p.roots.card = p.natDegree := (IsAlgClosed.splits p).natDegree_eq_card_roots.symm
  refine ⟨p.roots, hr.trans hd, fun hz => ?_, fun j hj => ?_⟩
  · have := isRoot_of_mem_roots hz
    rw [IsRoot, ← coeff_zero_eq_eval_zero, hc] at this
    simp [hn] at this
  · have := coeff_eq_esymm_roots_of_card hr (k := n - j) (by omega)
    rw [hc, if_pos (by omega), hl, hd, one_mul, Nat.sub_sub_self hj] at this
    exact (mul_left_cancel₀ (pow_ne_zero _ (by norm_num)) this).symm

theorem exists_satEig_eq : ∀ (q n : ℕ), q ≠ 0 → ∀ c : ℕ → ℂ, c 0 = 1 → c n ≠ 0 →
    ∃ B : Multiset ℂˣ, B.card = n ∧ ∀ j ≤ n, satEig q n B j = c j := by
  intro q n hq c h0 hn
  have hw : ∀ j : ℕ, (q : ℂ) ^ (((j : ℂ) * ((n : ℂ) - j)) / 2) ≠ 0 := fun j h =>
    hq (by exact_mod_cast ((Complex.cpow_eq_zero_iff _ _).1 h).1)
  obtain ⟨A, hA, hz, he⟩ := exists_multiset_esymm_eq n
    (fun j => c j / (q : ℂ) ^ (((j : ℂ) * ((n : ℂ) - j)) / 2)) (by simp [h0]) (div_ne_zero hn (hw n))
  refine ⟨A.pmap (fun a (h : a ≠ 0) => Units.mk0 a h) (fun a ha h => hz (h ▸ ha)), by simp [hA], fun j hj => ?_⟩
  rw [satEig, Multiset.map_pmap]
  simp only [Units.val_mk0, Multiset.pmap_eq_map, Multiset.map_id']
  rw [he j hj]
  exact mul_div_cancel₀ _ (hw j)

end GlobalTheory.LFun
end

section

open GlobalTheory.K5

theorem _root_.GlobalTheory.T.hodgeTate_cup_kummer_classes_eq_dlog_determinant : ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∃ c : ℕ, ∀ (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω →
  ∀ (T : Tower p Ω) (n : ℕ), 1 ≤ n → ∀ ι : On p n →ₐ[O0 p] Ω, IsEmb T n ι →
  ∀ (k l : ℤ) (w w' : (On p n)ˣ) (α β α' β' : On p n), IsDlog p n (w : On p n) α β → IsDlog p n (w' : On p n) α' β' →
  ∀ r s : Ω, r ^ (p ^ n) = (T.ζ n - 1) ^ k * ι w → s ^ (p ^ n) = (T.ζ n - 1) ^ l * ι w' →
  ∀ a b lz lq : Gal p Ω → ZMod (p ^ n), IsKum T n (Gn T n) r a → IsKum T n (Gn T n) s b →
    IsKum T n (Gn T n) (T.ζ (2 * n)) lz → IsKum T n (Gn T n) (T.qq (2 * n)) lq →
    Cob2 n (Gn T n) (fun g h => (p : Ω) ^ c * (((a g).val : Ω) * ((b h).val : Ω)) +
      (p : Ω) ^ c * (ι (fPi p n k l α β α' β') / (T.ζ n - 1)) * (((lz g).val : Ω) * ((lq h).val : Ω))) := by
  first | exact @GlobalTheory.K5.KummerCup.cup_kummer_dlog | exact GlobalTheory.K5.KummerCup.cup_kummer_dlog | (intros; apply GlobalTheory.K5.KummerCup.cup_kummer_dlog <;> assumption)
end

section

noncomputable section

namespace GlobalTheory.Doubling

open scoped TensorProduct
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.AdelicU

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
  {Q : Matrix (Fin (n + n)) (Fin (n + n)) E}

theorem exists_siegelH_proj_eq (x : ∀ v : HeightOneSpectrum (𝓞 F), siegelH (Fv F v) σ Q)
    (S : Finset (HeightOneSpectrum (𝓞 F))) : ∃ p : siegelH (AF F) σ Q,
      (∀ v ∈ S, proj σ Q v p = x v) ∧ (∀ v ∉ S, proj σ Q v p = 1) ∧ ∀ w, projArch σ Q w p = 1 := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨1, by simp, fun v _ => map_one _, fun w => map_one _⟩
  | insert u S hu ih =>
    obtain ⟨p, h1, h2, h3⟩ := ih
    refine ⟨embP u (x u) * p, fun v hv => ?_, fun v hv => ?_, fun w => ?_⟩
    · rw [Subgroup.coe_mul, map_mul, coe_embP]
      rcases Finset.mem_insert.1 hv with rfl | hv
      · rw [proj_emb_self, h2 _ hu, mul_one]
      · rw [proj_emb_ne σ Q (ne_of_mem_of_not_mem hv hu), h1 v hv, one_mul]
    · rw [Finset.mem_insert, not_or] at hv
      rw [Subgroup.coe_mul, map_mul, coe_embP, proj_emb_ne σ Q hv.1, h2 v hv.2, mul_one]
    · rw [Subgroup.coe_mul, map_mul, coe_embP, projArch_emb, h3, mul_one]

theorem exists_siegelH_projArch_eq (x : ∀ w : InfinitePlace F, siegelH w.Completion σ Q)
    (S : Finset (InfinitePlace F)) : ∃ p : siegelH (AF F) σ Q,
      (∀ w ∈ S, projArch σ Q w p = x w) ∧ (∀ w ∉ S, projArch σ Q w p = 1) ∧ ∀ v, proj σ Q v p = 1 := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨1, by simp, fun v _ => map_one _, fun w => map_one _⟩
  | insert u S hu ih =>
    obtain ⟨p, h1, h2, h3⟩ := ih
    refine ⟨embArchP u (x u) * p, fun v hv => ?_, fun v hv => ?_, fun w => ?_⟩
    · rw [Subgroup.coe_mul, map_mul, coe_embArchP]
      rcases Finset.mem_insert.1 hv with rfl | hv
      · rw [projArch_embArch_self, h2 _ hu, mul_one]
      · rw [projArch_embArch_ne σ Q (ne_of_mem_of_not_mem hv hu), h1 v hv, one_mul]
    · rw [Finset.mem_insert, not_or] at hv
      rw [Subgroup.coe_mul, map_mul, coe_embArchP, projArch_embArch_ne σ Q hv.1, h2 v hv.2, mul_one]
    · rw [Subgroup.coe_mul, map_mul, coe_embArchP, proj_embArch, h3, mul_one]

variable {L : Submodule (𝓞 E) (Fin n → E)} [Submodule.IsFullLattice E L] {a : GL (Fin n) (AF F ⊗[F] E)}

theorem HasIwasawa.adelic (hf : ∀ v : HeightOneSpectrum (𝓞 F), HasIwasawa σ Q (KFin σ Q L v))
    (hi : ∀ w : InfinitePlace F, HasIwasawa σ Q (KArch σ Q w (bc (compInf F E w) a))) :
    HasIwasawa σ Q (KAd σ Q L a) := fun g => by
  choose x k hk hx using fun v => hf v (proj σ Q v g)
  choose y l hl hy using fun w => hi w (projArch σ Q w g)
  have hS := Filter.eventually_cofinite.1 (eventually_proj_mem_stabLoc σ Q (sumLat finSumFinEquiv L L) g)
  obtain ⟨p, h1, h2, h3⟩ := exists_siegelH_proj_eq x hS.toFinset
  obtain ⟨q, h4, -, h5⟩ := exists_siegelH_projArch_eq y Finset.univ
  refine ⟨p * q, (↑(p * q) : GAd σ Q)⁻¹ * g, mem_KAd.2 ⟨fun v => ?_, fun w => ?_⟩, (mul_inv_cancel_left _ _).symm⟩
  · rw [map_mul, map_inv, Subgroup.coe_mul, map_mul, h5, mul_one]
    by_cases hv : v ∈ hS.toFinset
    · rw [h1 v hv, hx v, inv_mul_cancel_left]
      exact hk v
    · rw [h2 v hv, inv_one, one_mul]
      exact not_not.1 fun h => hv (hS.mem_toFinset.2 h)
  · rw [map_mul, map_inv, Subgroup.coe_mul, map_mul, h3, one_mul, h4 w (Finset.mem_univ w), hy w, inv_mul_cancel_left]
    exact hl w

end GlobalTheory.Doubling

end
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.FinWeil
open scoped BigOperators

namespace GlobalTheory.FinWeil.Vacuum

theorem sd_std (D : D7) (N : ℕ) : SD D (stdL D N) := by
  obtain ⟨Lt, h1, h2, -⟩ := GlobalTheory.T.Lt_eq_iff_inv_mul_mem_intG_and_transport D N
  exact h2 ▸ (h1 1).2

theorem pt_nsmul (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) {N N' : ℕ} (m : ℕ)
    (z : Matrix (Fin N') (Fin N) D.host.E) :
    pt D (tor0 D cc δ) δ (m • z) = m • pt D (tor0 D cc δ) δ z := by
  funext τ i j
  simp only [pt, embV, tor0, Pi.smul_apply, Matrix.smul_apply, map_nsmul]
  exact smul_comm _ _ _

theorem map_nsmul_inc (D : D7) {N N' : ℕ} (m : ℕ) (z : Matrix (Fin N') (Fin N) D.host.E) :
    (m • z).map (inc D) = m • z.map (inc D) := by
  ext i j
  simp only [Matrix.map_apply, Matrix.smul_apply, map_nsmul]

theorem nsmul_inv_smul {X : Type*} [AddCommGroup X] [Module ℚ X] {m : ℕ} (hm : 0 < m) (a : X) :
    m • ((m : ℚ)⁻¹ • a) = a := by
  rw [← Nat.cast_smul_eq_nsmul ℚ, smul_smul, mul_inv_cancel₀ (by exact_mod_cast hm.ne'), one_smul]

theorem level_fixed {D : D7} (hg : admG1 D) {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (hc : Crv D cc δ) {N N' : ℕ}
    {w : 𝓞 D.host.E} {γ : XA D N N' → XA D N N' → ℂ}
    {WA : XA D N N' → TTs D (tor0 D cc δ) N N' →ₗ[ℂ] TTs D (tor0 D cc δ) N N'}
    (hM : GlobalTheory.FinWeil.IsModel D cc δ N N' w γ WA) (v : TTs D (tor0 D cc δ) N N') (m : ℕ)
    (hv : ∀ x ∈ La0 D (tor0 D cc δ) N N', Wd D (tor0 D cc δ) (m • x) v = v) :
    ∀ b ∈ latA D cc N N', WA (m • b) v = v := by
  intro b hb
  obtain ⟨-, -, -, hW, hC⟩ := hM
  obtain ⟨h1, -, h3, -⟩ := GlobalTheory.T.completedStandardAdelicLattice_properties D hg cc δ hc N N'
  obtain ⟨m', hm', h⟩ := hC (m • b) v
  obtain ⟨z, a, ha, hz⟩ := h3 b m' hm'
  have hz' : pt D (tor0 D cc δ) δ z ∈ La0 D (tor0 D cc δ) N N' := by
    rw [← h1, hz]
    exact add_mem hb (nsmul_mem ha _)
  have e : (m • z).map (inc D) = m • b + m' • (m • a) := by
    rw [map_nsmul_inc, hz, smul_add, smul_comm m m' a]
  rw [← h _ (nsmul_mem ha m), ← e]
  apply Subtype.ext
  rw [hW, pt_nsmul]
  exact hv _ hz'

theorem vacuum_fixed_span : ∀ (D : D7), admG1 D → ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∀ (N N' : ℕ) w γ WA, GlobalTheory.FinWeil.IsModel D cc δ N N' w γ WA → ∀ e0 ∈ Th D (tor0 D cc δ) (stdL D N) (stdL D N'), e0 ≠ 0 → ∃ h : e0 ∈ TTs D (tor0 D cc δ) N N', Fixes WA (latA D cc N N') ⟨e0, h⟩ ∧ Submodule.span ℂ (Set.range fun ζ => WA ζ ⟨e0, h⟩) = ⊤ := by
  intro D hg cc δ hc N N' w γ WA hM e0 he0 hne
  obtain ⟨hL, hWd, -⟩ := GlobalTheory.T.theta_space_selfDual_pair_at_most_line D hg cc δ hc N N' (La0 D (tor0 D cc δ) N N')
    (Or.inr ⟨_, _, sd_std D _, sd_std D _, rfl⟩)
  obtain ⟨h1, h2, -⟩ := GlobalTheory.T.completedStandardAdelicLattice_properties D hg cc δ hc N N'
  have h0 : ∀ x ∈ La0 D (tor0 D cc δ) N N', Wd D (tor0 D cc δ) ((1 : ℕ) • x) e0 = e0 := fun x hx => by
    rw [one_smul, hWd x hx]
    funext z
    exact he0.2 x hx z
  have hT : e0 ∈ TTs D (tor0 D cc δ) N N' := ⟨he0.1, 1, one_pos, h0⟩
  refine ⟨hT, fun a ha => ?_, ?_⟩
  · have := level_fixed hg hc hM ⟨e0, hT⟩ 1 h0 a ha
    rwa [one_smul] at this
  refine GlobalTheory.T.span_heisenberg_translates_vacuum_eq_top hM.1 _ hM.2.1 _ (fun v hv => ?_) (fun v => ?_)
  · have hv' : (v : VC D N N' → ℂ) ∈ ThSp D (tor0 D cc δ) (La0 D (tor0 D cc δ) N N') := by
      refine ⟨v.2.1, fun x hx y => ?_⟩
      have e := hWd x hx v
      obtain ⟨z, rfl⟩ := h2 x hx
      rw [← hM.2.2.2.1, hv _ ((h1 z).2 hx)] at e
      exact (congrFun e y).symm
    obtain ⟨c, hc'⟩ := hL _ hv' e0 he0 hne
    exact ⟨c, Subtype.ext hc'⟩
  · obtain ⟨-, m, hm, hv⟩ := v.2
    refine ⟨(latA D cc N N').comap (m • LinearMap.id), GlobalTheory.T.heisenbergRelativeIndex_completedStandard_ne_zero D hg cc δ hc N N' m hm _ (fun ζ hζ => hζ),
      fun a _ hT' => ?_⟩
    have hb : (m : ℚ)⁻¹ • a ∈ latA D cc N N' := by
      refine (hM.2.1 _).2 fun a' ha' => ?_
      have ht : (m : ℚ)⁻¹ • a' ∈ (latA D cc N N').comap (m • LinearMap.id) := by
        change m • ((m : ℚ)⁻¹ • a') ∈ latA D cc N N'
        rwa [nsmul_inv_smul hm]
      rw [← nsmul_inv_smul hm a', hM.1.nsmul_right, ← hM.1.nsmul_left, nsmul_inv_smul hm]
      exact hT' _ ht
    have := level_fixed hg hc hM v m hv _ hb
    rwa [nsmul_inv_smul hm] at this

end GlobalTheory.FinWeil.Vacuum
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.FinWeil
open scoped BigOperators

theorem _root_.GlobalTheory.T.completedStandardAdelicLattice_selfDual : ∀ (D : D7), admG1 D → ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∀ ψ : AE D → ℂ, IsPsi D cc δ ψ → ∀ (N N' : ℕ), SelfDual (gamA ψ) (latA D cc N N') := by
  first | exact @GlobalTheory.FinWeil.LatSelfDual.latA_selfDual | exact GlobalTheory.FinWeil.LatSelfDual.latA_selfDual | (intros; apply GlobalTheory.FinWeil.LatSelfDual.latA_selfDual <;> assumption)
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.FinWeil
open scoped BigOperators

theorem _root_.GlobalTheory.T.thetaIntertwiner_eq_normalisedAdelicSum : ∀ (D : D7), admG1 D → ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∀ (N N' : ℕ) w γ WA, GlobalTheory.FinWeil.IsModel D cc δ N N' w γ WA → ∀ (g : GA D N) (g' : GA D N') L₁ L₁', Moves D (g : GL (Fin N) (AE D)) L₁ → Moves D (g' : GL (Fin N') (AE D)) L₁' → SelfDual γ ((latA D cc N N').map (actA D N N' (g, g'))) → ∀ F : TTs D (tor0 D cc δ) N N', Fixes WA (latA D cc N N') F → Iop D (tor0 D cc δ) (La0 D (tor0 D cc δ) N N') (La D (tor0 D cc δ) L₁ L₁') F = ((Real.sqrt (idx (latA D cc N N') ((latA D cc N N').map (actA D N N' (g, g'))) : ℝ))⁻¹ : ℂ) • ((sumOp WA (latA D cc N N') ((latA D cc N N').map (actA D N N' (g, g'))) F : TTs D (tor0 D cc δ) N N') : VC D N N' → ℂ) := by
  first | exact @GlobalTheory.FinWeil.iop_eq_sumOp | exact GlobalTheory.FinWeil.iop_eq_sumOp | (intros; apply GlobalTheory.FinWeil.iop_eq_sumOp <;> assumption)
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.ThetaConj
open scoped BigOperators

theorem _root_.GlobalTheory.T.torsionTranslate_mem_thetaPullbackSpan : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∀ (N N' r : ℕ) (b : Fin r → Matrix (Fin N') (Fin N) D.host.E), OnB D b → ∀ F ∈ Tr D (tor0 D cc δ) b, ∀ (t : VC D N N') (m : ℕ), 0 < m → m • t ∈ LaB D (tor0 D cc δ) b → U D (tor0 D cc δ) t F ∈ Tr D (tor0 D cc δ) b := by
  first | exact @GlobalTheory.TorsionTranslate.translate_mem | exact GlobalTheory.TorsionTranslate.translate_mem | (intros; apply GlobalTheory.TorsionTranslate.translate_mem <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.Links Formalism.L2.JoinChr Formalism.L2.Host
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_baseChangeFiniteAdele_ringEquiv : ∀ D : D7, ∃ ι : (Af D.host.F ⊗[D.host.F] D.host.E) ≃+* FiniteAdeleRing (𝓞 D.host.E) D.host.E, (∀ x : D.host.E, ι ((1 : Af D.host.F) ⊗ₜ[D.host.F] x) = algebraMap D.host.E (FiniteAdeleRing (𝓞 D.host.E) D.host.E) x) ∧ (∀ y, y ∈ intAE D ↔ ∀ P : HeightOneSpectrum (𝓞 D.host.E), Valued.v (ι y P) ≤ 1) ∧ (∀ (a : Af D.host.F) (k : D.host.F) (P : HeightOneSpectrum (𝓞 D.host.E)) (n : ℕ), Valued.v (a (P.under (𝓞 D.host.F)) - algebraMap D.host.F _ k) ≤ WithZero.exp (-(n : ℤ)) → Valued.v (ι (a ⊗ₜ[D.host.F] (1 : D.host.E)) P - algebraMap D.host.E _ (algebraMap D.host.F D.host.E k)) ≤ WithZero.exp (-(n : ℤ))) := by
  first | exact @GlobalTheory.HostAdeleIso.exists_finiteAdele_equiv | exact GlobalTheory.HostAdeleIso.exists_finiteAdele_equiv | (intros; apply GlobalTheory.HostAdeleIso.exists_finiteAdele_equiv <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.Links Formalism.L2.JoinChr Formalism.L2.Host
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_finitePlaceIdempotent_baseChangeAdeles : ∀ (D : D7) (ι : (Af D.host.F ⊗[D.host.F] D.host.E) ≃+* FiniteAdeleRing (𝓞 D.host.E) D.host.E), (∀ x : D.host.E, ι ((1 : Af D.host.F) ⊗ₜ[D.host.F] x) = algebraMap D.host.E (FiniteAdeleRing (𝓞 D.host.E) D.host.E) x) → (∀ y, y ∈ intAE D ↔ ∀ P : HeightOneSpectrum (𝓞 D.host.E), Valued.v (ι y P) ≤ 1) → (∀ (a : Af D.host.F) (k : D.host.F) (P : HeightOneSpectrum (𝓞 D.host.E)) (n : ℕ), Valued.v (a (P.under (𝓞 D.host.F)) - algebraMap D.host.F _ k) ≤ WithZero.exp (-(n : ℤ)) → Valued.v (ι (a ⊗ₜ[D.host.F] (1 : D.host.E)) P - algebraMap D.host.E _ (algebraMap D.host.F D.host.E k)) ≤ WithZero.exp (-(n : ℤ))) → (∀ P : HeightOneSpectrum (𝓞 D.host.E), ∃ e : AE D, IsPlIdem D e P ∧ infPart D e = 0 ∧ ι (finPart D e) P = 1 ∧ ∀ P' : HeightOneSpectrum (𝓞 D.host.E), P' ≠ P → ι (finPart D e) P' = 0) := by
  first | exact @GlobalTheory.PlaceIdem.exists_isPlIdem | exact GlobalTheory.PlaceIdem.exists_isPlIdem | (intros; apply GlobalTheory.PlaceIdem.exists_isPlIdem <;> assumption)
end
