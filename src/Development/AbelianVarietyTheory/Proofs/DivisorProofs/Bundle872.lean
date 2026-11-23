module

public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle001
public import Mathlib.RingTheory.SimpleRing.Principal
public import Formalism.LocalToGlobal.Columns.RowForms
public import Formalism.LocalToGlobal.Divisibility.Bundle002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle840
public import Formalism.LocalToGlobal.Divisibility.LiftLatLemmas
public import Formalism.LocalToGlobal.Divisibility.GoodPartHermitianSpec
public import Formalism.SharpRestriction.Divisibility.PrimeDegreeVariant
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle820
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle841
public import Formalism.LocalToGlobal.Divisibility.RowSideTie
public import Formalism.LocalToGlobal.Divisibility.ProjLemmas
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle018
public import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle082
public import Formalism.PadicSubsetSums.CentralIdempotents.Bundle002
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle009
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle783
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle842
public import Formalism.PieriBlockIdeals.BlockIdealBound5Derived
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightedIdempotentLocalShareBadTuplesLe
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EmbGLMemRealSU
import Formalism.LocalToGlobal.IndefiniteForms.IndefSide
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.Definitions.Divisors.HasBlockOfOccurs

@[expose] public section

section

open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up
open scoped ENNReal


theorem _root_.GlobalTheory.T.self_dual_lattice_real_completion : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (G : Matrix (Fin r) (Fin r) E) (Λ : Submodule (𝓞 E) (Fin r → E)) (g0 : Matrix (Fin r) (Fin r) (RA (maximalRealSubfield E) E)), SelfDualLat G Λ → IsUA (IsCMField.complexConj E) G g0 → ∃ L : Submodule (𝓞 E) (Fin r → E), (L : Set (Fin r → E)) = latOf (maximalRealSubfield E) g0 (Λ : Set (Fin r → E)) ∧ (hat (maximalRealSubfield E) (L : Set (Fin r → E)) : Set (Fin r → RA (maximalRealSubfield E) E)) = g0.mulVec '' (hat (maximalRealSubfield E) (Λ : Set (Fin r → E)) : Set (Fin r → RA (maximalRealSubfield E) E)) ∧ SelfDualLat G L := by
  first | exact @GlobalTheory.UCls.selfDual_latOf_translate | exact GlobalTheory.UCls.selfDual_latOf_translate | (intros; apply GlobalTheory.UCls.selfDual_latOf_translate <;> assumption)
end

section

open Module NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Col Matrix
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.RowLevIndex

section Gen

variable {κ : Type} [CommRing κ]

theorem firstDiagonalBlock_of_diagonal_embedding {n r : ℕ} (h : r ≤ n) (bl : List ℕ) (p : GL (Fin r) κ) (M : GL (Fin n) κ)
    (hM : M ∈ blockUT n κ r bl) (e : M = diagEmb κ h p) : blk0 n κ h bl ⟨M, hM⟩ = p := by
  subst e
  apply Units.ext
  ext i j
  rw [blockZero_val]
  show (diagEmb κ h p : Matrix (Fin n) (Fin n) κ) (Fin.castLE h i) (Fin.castLE h j) = _
  rw [diagEmb_val, diagMat_of_lt _ (show (Fin.castLE h i).val < r from i.2) (show (Fin.castLE h j).val < r from j.2)]
  rfl

theorem HK_le_HPar {n r : ℕ} (h : r ≤ n) (bl : List ℕ) (H₀ : Subgroup (GL (Fin r) κ)) :
    HK n κ r bl ≤ HPar n κ h bl H₀ := by
  rw [HK_eq_HPar h bl]
  intro M hM
  obtain ⟨hb, h0⟩ := mem_HPar.mp hM
  exact mem_HPar.mpr ⟨hb, by rw [Subgroup.mem_bot] at h0; rw [h0]; exact H₀.one_mem⟩

theorem mem_HK_iff {n r : ℕ} (h : r ≤ n) (bl : List ℕ) (M : GL (Fin n) κ) (hM : M ∈ blockUT n κ r bl) :
    M ∈ HK n κ r bl ↔ blk0 n κ h bl ⟨M, hM⟩ = 1 := by
  rw [HK_eq_HPar h bl, mem_HPar]
  constructor
  · rintro ⟨_, h0⟩
    exact (Subgroup.mem_bot).mp h0
  · intro h0
    exact ⟨hM, (Subgroup.mem_bot).mpr h0⟩

end Gen

section Rows

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Formalism.L2.Col.Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)


open Classical in
abbrev inL (v : Pr.vGs) : rowSG Pr sel mu := ⟨v.1, Finset.mem_union_left _ v.2⟩

theorem rowTy_inL (P : LevFam X.E X.K R.r Pr.vGs) (v : Pr.vGs) :
    rowTy Ch sel mu P (inL sel mu v) = rowTyG Ch P v := LevFam.glue_of_mem _ _ _ v.2

theorem rowTyKK_inL (v : Pr.vGs) :
    rowTyKK Ch sel mu (inL sel mu v) = rowTyK Ch v := LevFam.glue_of_mem _ _ _ v.2

theorem rowTy_H_of_not (P : LevFam X.E X.K R.r Pr.vGs) (w : rowSG Pr sel mu) (hw : w.1 ∉ Pr.vGs) :
    (rowTy Ch sel mu P w).H = (rowTyKK Ch sel mu w).H := by
  unfold rowTy rowTyKK
  rw [LevFam.glue_of_not _ _ _ hw, LevFam.glue_of_not _ _ _ hw]

theorem memP (P : LevFam X.E X.K R.r Pr.vGs) (x : ↥(rowTy Ch sel mu P).inv.grp) (v : Pr.vGs) :
    x.1 (inL sel mu v) ∈ HPar (R.N R.m - 1) (𝓞 X.E ⧸ v.1.asIdeal) (r_le_X' R) (List.replicate R.m R.t) (P v).H := by
  have h := x.2 (inL sel mu v) (Set.mem_univ _)
  change x.1 (inL sel mu v) ∈ (rowTy Ch sel mu P (inL sel mu v)).H at h
  rw [rowTy_inL] at h
  exact h

theorem grp_le (P : LevFam X.E X.K R.r Pr.vGs) :
    (rowTyKK Ch sel mu).inv.grp ≤ (rowTy Ch sel mu P).inv.grp := by
  intro x hx w _
  have h := hx w (Set.mem_univ _)
  change x w ∈ (rowTyKK Ch sel mu w).H at h
  change x w ∈ (rowTy Ch sel mu P w).H
  by_cases hw : w.1 ∈ Pr.vGs
  · have e1 := rowTyKK_inL Ch sel mu ⟨w.1, hw⟩
    have e2 := rowTy_inL Ch sel mu P ⟨w.1, hw⟩
    change rowTyKK Ch sel mu w = _ at e1
    change rowTy Ch sel mu P w = _ at e2
    rw [e1] at h
    rw [e2]
    exact GlobalTheory.RowLevIndex.HK_le_HPar _ _ _ h
  · rw [rowTy_H_of_not Ch sel mu P w hw]
    exact h

def blkMap (P : LevFam X.E X.K R.r Pr.vGs) : FormG (rowTy Ch sel mu P).inv →* GLG (E := X.E) (n := R.r) (SG := Pr.vGs) where
  toFun x v := blk0 (R.N R.m - 1) (𝓞 X.E ⧸ v.1.asIdeal) (r_le_X' R) (List.replicate R.m R.t)
    ⟨x.2.1 (inL sel mu v), HPar_le _ _ _ (memP Ch sel mu P x.2 v)⟩
  map_one' := by
    funext v
    exact map_one (blk0 (R.N R.m - 1) (𝓞 X.E ⧸ v.1.asIdeal) (r_le_X' R) (List.replicate R.m R.t))
  map_mul' a b := by
    funext v
    exact map_mul (blk0 (R.N R.m - 1) (𝓞 X.E ⧸ v.1.asIdeal) (r_le_X' R) (List.replicate R.m R.t))
      ⟨a.2.1 (inL sel mu v), HPar_le _ _ _ (memP Ch sel mu P a.2 v)⟩ ⟨b.2.1 (inL sel mu v), HPar_le _ _ _ (memP Ch sel mu P b.2 v)⟩

end Rows

section Rows2

variable {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)
  (P : LevFam X.E X.K R.r Pr.vGs)

def incl : FormG (rowTyKK Ch sel mu).inv →* FormG (rowTy Ch sel mu P).inv :=
  MonoidHom.prodMap (MonoidHom.id _) (Subgroup.inclusion (grp_le Ch sel mu P))

theorem incl_injective : Function.Injective (incl Ch sel mu P) := by
  intro a b e
  have e1 := congrArg Prod.fst e
  have e2 := congrArg (fun x => (x.2 : GLG (E := X.E) (n := R.N R.m - 1) (SG := rowSG Pr sel mu))) e
  exact Prod.ext e1 (Subtype.ext e2)

theorem range_incl : (incl Ch sel mu P).range = (blkMap Ch sel mu P).ker := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    rw [MonoidHom.mem_ker]
    funext v
    have h := y.2.2 (inL sel mu v) (Set.mem_univ _)
    change y.2.1 (inL sel mu v) ∈ (rowTyKK Ch sel mu (inL sel mu v)).H at h
    rw [rowTyKK_inL] at h
    exact (GlobalTheory.RowLevIndex.mem_HK_iff (r_le_X' R) _ _ _).mp h
  · intro hx
    rw [MonoidHom.mem_ker] at hx
    have hmem : x.2.1 ∈ (rowTyKK Ch sel mu).inv.grp := by
      intro w _
      change x.2.1 w ∈ (rowTyKK Ch sel mu w).H
      by_cases hw : w.1 ∈ Pr.vGs
      · have e1 := rowTyKK_inL Ch sel mu ⟨w.1, hw⟩
        change rowTyKK Ch sel mu w = _ at e1
        rw [e1]
        exact (GlobalTheory.RowLevIndex.mem_HK_iff (r_le_X' R) _ _ (HPar_le _ _ _ (memP Ch sel mu P x.2 ⟨w.1, hw⟩))).mpr
          (congrFun hx ⟨w.1, hw⟩)
      · rw [← rowTy_H_of_not Ch sel mu P w hw]
        exact x.2.2 w (Set.mem_univ _)
    exact ⟨(x.1, ⟨x.2.1, hmem⟩), rfl⟩

open Classical in
theorem range_blkMap : (blkMap Ch sel mu P).range = P.grp := by
  ext p
  constructor
  · rintro ⟨x, rfl⟩
    intro v _
    obtain ⟨_, h0⟩ := mem_HPar.mp (memP Ch sel mu P x.2 v)
    exact h0
  · intro hp
    let h : GLG (E := X.E) (n := R.N R.m - 1) (SG := rowSG Pr sel mu) := fun w =>
      if hw : w.1 ∈ Pr.vGs then diagEmb _ (r_le_X' R) (p ⟨w.1, hw⟩) else 1
    have hmem : h ∈ (rowTy Ch sel mu P).inv.grp := by
      intro w _
      change h w ∈ (rowTy Ch sel mu P w).H
      by_cases hw : w.1 ∈ Pr.vGs
      · have e2 := rowTy_inL Ch sel mu P ⟨w.1, hw⟩
        change rowTy Ch sel mu P w = _ at e2
        rw [e2]
        have hh : h w = diagEmb _ (r_le_X' R) (p ⟨w.1, hw⟩) := dif_pos hw
        rw [hh]
        exact mem_HPar.mpr ⟨diagEmb_mem_blockUT _ _ _, by
          rw [GlobalTheory.RowLevIndex.firstDiagonalBlock_of_diagonal_embedding _ _ (p ⟨w.1, hw⟩) _ _ rfl]; exact hp ⟨w.1, hw⟩ (Set.mem_univ _)⟩
      · have hh : h w = 1 := dif_neg hw
        rw [hh]
        exact Subgroup.one_mem _
    refine ⟨((1 : UF X.E (R.N R.m - 1)), ⟨h, hmem⟩), ?_⟩
    funext v
    exact GlobalTheory.RowLevIndex.firstDiagonalBlock_of_diagonal_embedding _ _ (p v) _ _ (dif_pos v.2)

end Rows2

theorem index_eq : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} (W : Formalism.L2.Col.Wts X Pr.Word R) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S) (P : LevFam X.E X.K R.r Pr.vGs), ∃ ι : (mtildeKGSD W Ch sel mu).G →* (mtildeGSD W Ch sel mu P).G, Function.Injective ι ∧ (∀ (a : (mtildeKGSD W Ch sel mu).G) (d : (mtildeKGSD W Ch sel mu).D), ι a • d = a • d) ∧ ι.range.index = Nat.card P.grp := by
  intro X Pr R W Ch sel S mu P
  refine ⟨incl Ch sel mu P, incl_injective Ch sel mu P, fun a d => rfl, ?_⟩
  rw [range_incl, Subgroup.index_ker, range_blkMap]

end GlobalTheory.RowLevIndex
end
end

section

open Module NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Col Matrix
open scoped ComplexOrder

theorem _root_.GlobalTheory.T.goodPart_levelForm_infinitePlace_eq_classSum : ∀ {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 : Type} (B : BlockDat K G Pl0) (ℓ : Lvl K G) (v0 : InfinitePlace K) (s : ℕ), BlockHyp B ℓ v0 s → ∀ v : InfinitePlace K, (B.HV ℓ).map v.embedding = ((Nat.card ℓ.P : ℂ)⁻¹) • (((B.vE ℓ).map v.embedding).conjTranspose * B.S.H.map v.embedding * (B.vE ℓ).map v.embedding) := by
  first | exact @GlobalTheory.hv_map_embedding | exact GlobalTheory.hv_map_embedding | (intros; apply GlobalTheory.hv_map_embedding <;> assumption)
end

section

open Module NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Col Matrix
open scoped ComplexOrder

namespace GlobalTheory.GoodPartLevelForms

theorem lvlE_lvlPr_vE : ∀ {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 : Type} (B : BlockDat K G Pl0) (ℓ : Lvl K G) (v0 : InfinitePlace K) (s : ℕ), BlockHyp B ℓ v0 s → B.S.lvlE B.r ℓ.P ℓ.ψ * B.S.lvlPr B.r ℓ.P ℓ.ψ * B.vE ℓ = B.vE ℓ := by
  intro K _ _ _ G _ _ Pl0 B ℓ v0 s h
  exact Formalism.L2.DIV.BlockDat.lf_lvl_vE h

end GlobalTheory.GoodPartLevelForms
end

section

noncomputable section

namespace GlobalTheory.GoodSetOfChars

open GlobalTheory.FinGL Formalism.L2.DIV Module

theorem eS_eq_chiIdem {K : Type} [Field K] {G : Type} [Group G] [Fintype G] (T : Formalism.MainNotions.PrimeDegreeVariant.GoodSet K G) (s : T.S) :
    Formalism.MainNotions.PrimeDegreeVariant.eS T s = chiIdem fun g => LinearMap.trace K (T.W s) (T.tau s g) := by
  unfold Formalism.MainNotions.PrimeDegreeVariant.eS chiIdem
  refine Finset.sum_congr rfl fun x _ => ?_
  simp [LinearMap.trace_one]

theorem exists_goodSet (K : Type) [Field K] [CharZero K] (G : Type) [Group G] [Fintype G] (X : Finset (G → K))
    (hX : ∀ χ ∈ X, IsAbsIrrChar χ) (P0 : Formalism.MainNotions.PrimeDegreeVariant.Pair K G) [Fintype P0.H]
    (h1 : ∀ χ ∈ X, ∑ h : P0.H, χ (h : G) * (((P0.chi h)⁻¹ : Kˣ) : K) = (Fintype.card P0.H : K)) :
    ∃ T : Formalism.MainNotions.PrimeDegreeVariant.GoodSet K G,
      (∀ χ, χ ∈ X ↔ ∃ s, χ = fun g => LinearMap.trace K (T.W s) (T.tau s g)) ∧
        Formalism.MainNotions.PrimeDegreeVariant.M1 T P0 ∧ Formalism.MainNotions.PrimeDegreeVariant.eG T = idemOf X := by
  classical
  have key : ∀ s : X, ∃ (n : ℕ) (τ : Representation K G (Fin n → K)), 0 < n ∧
      Function.Surjective τ.asAlgebraHom ∧ ∀ g, LinearMap.trace K (Fin n → K) (τ g) = (s : G → K) g :=
    fun s => GlobalTheory.T.exists_rep_realising_char_of_multiplicity_one K G s (hX s s.2) P0.H P0.chi (h1 s s.2)
  choose n τ hn hs ht using key
  have ht' : ∀ s : X, (fun g => LinearMap.trace K (Fin (n s) → K) (τ s g)) = (s : G → K) := fun s => funext (ht s)
  let T : Formalism.MainNotions.PrimeDegreeVariant.GoodSet K G :=
    { S := X
      W := fun s => Fin (n s) → K
      ntW := fun s => by
        have : Nonempty (Fin (n s)) := ⟨⟨0, hn s⟩⟩
        infer_instance
      tau := τ
      irr := hs
      inj := fun a b hab => Subtype.ext (by rw [← ht' a, ← ht' b]; exact hab) }
  refine ⟨T, fun χ => ⟨fun h => ⟨⟨χ, h⟩, (ht' ⟨χ, h⟩).symm⟩, ?_⟩, fun s => ?_, ?_⟩
  · rintro ⟨s, rfl⟩
    exact (ht' s).symm ▸ s.2
  · have h2 := (GlobalTheory.CuspidalIdempotentCharacters.finrank_eq_one_iff (τ s) P0.H P0.chi).2 (by
      simp_rw [ht s]
      rw [h1 _ s.2, Nat.card_eq_fintype_card])
    rw [← GlobalTheory.CuspidalIdempotentCharacters.eps_eq_lvlIdem] at h2
    exact h2
  · unfold Formalism.MainNotions.PrimeDegreeVariant.eG idemOf
    rw [← Finset.sum_coe_sort X]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [eS_eq_chiIdem]
    exact congrArg chiIdem (ht' s)

end GlobalTheory.GoodSetOfChars
end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2.DIV Formalism.L2.Indef

namespace GlobalTheory

theorem range_op_eq_span_of_formsTie :
    ∀ {K : Type} [Field K] [NumberField K] [StarRing K] {n k : ℕ} (σ : K →+* ℂ) {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] (j : (Fin n → K) →ₛₗ[σ] W) (H E : Matrix (Fin n) (Fin n) K) (op : W →ₗ[ℂ] W) (V : Matrix (Fin n) (Fin k) K), FormsTie σ j H E op → LinearMap.range E.mulVecLin = LinearMap.range V.mulVecLin → LinearMap.range op = Submodule.span ℂ (Set.range fun x => j (V.mulVec x)) := by
  intro K _ _ _ n k σ W _ _ j H E op V h hr
  apply le_antisymm
  · rw [← Submodule.map_top, ← h.span, Submodule.map_span, Submodule.span_le]
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    have hm : E.mulVec (Pi.single i 1) ∈ LinearMap.range V.mulVecLin := by
      rw [← hr]
      exact ⟨Pi.single i 1, rfl⟩
    obtain ⟨y, hy⟩ := hm
    refine Submodule.subset_span ⟨y, ?_⟩
    have hy' : V.mulVec y = E.mulVec (Pi.single i 1) := hy
    show j (V.mulVec y) = op (j (Pi.single i 1))
    rw [h.op_eq, hy']
  · rw [Submodule.span_le]
    rintro _ ⟨y, rfl⟩
    have hm : V.mulVec y ∈ LinearMap.range E.mulVecLin := by
      rw [hr]
      exact ⟨y, rfl⟩
    obtain ⟨x, hx⟩ := hm
    have hx' : E.mulVec x = V.mulVec y := hx
    refine ⟨j x, ?_⟩
    show op (j x) = j (V.mulVec y)
    rw [h.op_eq, hx']

end GlobalTheory
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2.DIV Formalism.L2.Indef

namespace GlobalTheory

theorem range_lvlOp_idemOf_eq_range_lvlPr_mul_V0E {K : Type} [Field K] [NumberField K] [StarRing K] (S : CSD K)
    {G : Type} [Group G] [Fintype G] (r : Representation K G S.Forms) (X : Finset (G → K)) (P : Subgroup G)
    (ψ : P →* Kˣ) :
    LinearMap.range (S.lvlOp r P ψ (idemOf X)).mulVecLin =
      LinearMap.range (S.lvlPr r P ψ * S.V0E r X P ψ).mulVecLin := by
  have hE : LinearMap.range (S.lvlE r P ψ).mulVecLin =
      LinearMap.range (S.gaMat r (lvlIdem P ψ)).mulVecLin := (image_idempotent_spec K _ _).2
  have hV : LinearMap.range (S.V0E r X P ψ).mulVecLin =
      LinearMap.range (S.gaMat r (goodAt X P ψ)).mulVecLin := (image_idempotent_spec K _ _).2
  have hm : S.gaMat r (goodAt X P ψ) = S.gaMat r (idemOf X) * S.gaMat r (lvlIdem P ψ) :=
    (group_action_matrix_hom K S G r).2 _ _
  unfold CSD.lvlOp
  rw [Matrix.mulVecLin_mul, Matrix.mulVecLin_mul, Matrix.mulVecLin_mul, LinearMap.range_comp, LinearMap.range_comp,
    hE, hV, hm, Matrix.mulVecLin_mul, LinearMap.range_comp, Submodule.map_comp]

theorem range_goodProjector_eq_range_goodCoordinates : ∀ (D : D7) {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {m : ℕ}
    (A : FamIn D.what₂.LL G Pl0 T m) (s : ℕ), A.fam.Ok s → ∀ (P : Subgroup G) (ψ : P →* D.what₂.LLˣ) (t : T),
    LinearMap.range (rE D A P ψ t).mulVecLin = LinearMap.range (rV0 D A P ψ t).mulVecLin := by
  intro D G _ _ Pl0 T m A s _ P ψ t
  exact range_lvlOp_idemOf_eq_range_lvlPr_mul_V0E (A.fam.R t).S (A.fam.R t).r A.X P ψ

end GlobalTheory
end

section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.tangentBasis_moves_along_semiAbelianTripleMap : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X X' : Scheme.{0}) (t : SAB H X) (t' : SAB H X') (j : X' ⟶ X) (m : SABMap t' t j) (S T : Type) [CommRing S] [CommRing T] (ψ : S →+* T) (x : Sp S ⟶ X) (x' : Sp T ⟶ X'), x' ≫ j = spMap ψ ≫ x → ∀ (n : ℕ) (v : Fin n → (Sp (DualNumber S) ⟶ t.G.left)), (∀ i, IsTanAtG t x (v i)) → (∀ w, IsTanAtG t x w → ∃! cf : Fin n → S, IsCombAtG t x v cf w) → ∃ v' : Fin n → (Sp (DualNumber T) ⟶ t'.G.left), (∀ i, v' i ≫ m.φ = spMap (dualMap ψ) ≫ v i) ∧ (∀ i, IsTanAtG t' x' (v' i)) ∧ ∀ w, IsTanAtG t' x' w → ∃! cf : Fin n → T, IsCombAtG t' x' v' cf w := by
  first | exact @GlobalTheory.SabTan.tanBasis_sabMap | exact GlobalTheory.SabTan.tanBasis_sabMap | (intros; apply GlobalTheory.SabTan.tanBasis_sabMap <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.L2.Host

namespace GlobalTheory.HCharRam

theorem ram_finite : ∀ (K : Type) [Field K] [NumberField K] (χ : HChar K),
    {w : HeightOneSpectrum (𝓞 K) | ¬ χ.UnrAt w}.Finite := by
  intro K _ _ χ
  exact Filter.eventually_cofinite.1 (GlobalTheory.HeckeSplit.eventually_unrAt χ.1 χ.2.1)

end GlobalTheory.HCharRam
end

section

open CategoryTheory Polynomial Formalism.IrreducibleCountingLemmas.TYPES Formalism.L2.DIV GlobalTheory.HcIrr

theorem _root_.GlobalTheory.T.hasCuspidalFactorAtBlock_leviPiTensor : ∀ (K : Type) [Field K] [Fintype K] [DecidableEq K] (r s : ℕ) (b : Fin r → Fin s) (lam : ∀ c : Fin s, FDRep ℂ (GL {i // b i = c} K)), (∀ c, Simple (lam c)) → ∀ (c : Fin s) (d : ℕ) (h : Fintype.card (GlobalTheory.IndefiniteRowSideFullHecke.BlockEmbeddingFactors.Block (natBlocks b) (c : ℕ)) = d) (W : Type) [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ (GL (Fin d) K) W), GlobalTheory.IndefiniteRowSideFullHecke.BlockEmbeddingFactors.HasFactor (natBlocks b) (leviTensor b lam) (c : ℕ) h ρ → ∃ (e : {i // b i = c} ≃ Fin d) (L : W ≃ₗ[ℂ] (lam c : Type)), ∀ g v, L (ρ g v) = (lam c).ρ ((glEquiv K e).symm g) (L v) := by
  first | exact @GlobalTheory.HcIrr.Factor.factor_iso | exact GlobalTheory.HcIrr.Factor.factor_iso | (intros; apply GlobalTheory.HcIrr.Factor.factor_iso <;> assumption)
end

section

set_option autoImplicit false

noncomputable section

open MvPolynomial
open Formalism.GradedWeylDivisibility Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LD GlobalTheory.ExpFrame

namespace GlobalTheory.HighWtEmb

abbrev BVar (N : ℕ) (ι : Type) : Type := ι × (Fin N × Fin N)

abbrev OVar (N : ℕ) {ι : Type} (τ : ι) : Type := {p : BVar N ι // p.1 ≠ τ}

def blockRed (O : Type) [CommRing O] (N : ℕ) {ι : Type} (ϖ : O) (τ : ι) :
    MvPolynomial (Fin N × Fin N) O →ₐ[O] MvPolynomial (BVar N ι) (O ⧸ Ideal.span {ϖ}) :=
  aeval fun v => X (τ, v)

def redT (O : Type) [CommRing O] (N : ℕ) {ι : Type} [Fintype ι] [DecidableEq ι] (mu : ι → ℕ → ℕ) (ϖ : O) :
    NablaT O N mu →ₗ[O] MvPolynomial (BVar N ι) (O ⧸ Ideal.span {ϖ}) :=
  PiTensorProduct.lift ((MultilinearMap.mkPiAlgebra O ι (MvPolynomial (BVar N ι) (O ⧸ Ideal.span {ϖ}))).compLinearMap
    fun τ => (blockRed O N ϖ τ).toLinearMap ∘ₗ (dualWeyl O N N (res N (mu τ))).subtype)

def nabK (k : Type) [CommRing k] (N : ℕ) {ι : Type} [Fintype ι] (ν : ι → Fin N → ℕ) : Submodule k (MvPolynomial (BVar N ι) k) :=
  Submodule.span k {P | ∃ f : ι → MvPolynomial (Fin N × Fin N) k, (∀ τ, f τ ∈ dualWeyl k N N (ν τ)) ∧
    P = ∏ τ, rename (fun v : Fin N × Fin N => ((τ, v) : BVar N ι)) (f τ)}

def toBlock (k : Type) [CommRing k] (N : ℕ) {ι : Type} [DecidableEq ι] (τ : ι) :
    MvPolynomial (BVar N ι) k →ₐ[k] MvPolynomial (Fin N × Fin N) (MvPolynomial (OVar N τ) k) :=
  aeval fun p => if h : p.1 = τ then X p.2 else C (X ⟨p, h⟩)

def blockSub (k : Type) [CommRing k] (N : ℕ) {ι : Type} (A : ι → Matrix (Fin N) (Fin N) k) :
    MvPolynomial (BVar N ι) k →ₐ[k] MvPolynomial (BVar N ι) k :=
  aeval fun p => ∑ b : Fin N, C (A p.1 p.2.1 b) * X (p.1, (b, p.2.2))

def blockW (N : ℕ) {ι : Type} [DecidableEq ι] (τ : ι) : BVar N ι → (Fin N → ℕ) :=
  fun p => if p.1 = τ then Pi.single p.2.1 1 else 0

end GlobalTheory.HighWtEmb

end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ArithmeticCylinders

theorem _root_.GlobalTheory.T.weightedIdempotent_localShare_bad_tuples_le : ∀ (D : D7) (ψ₀ : ∀ k : Fin 2, AddChar (ZMod (D.host.g k)) ℂ), (∀ k, ψ₀ k ≠ 1) → admLq D → TieAdmG D → 100 ≤ D.R.r → (∀ k : Fin 2, 2 ^ 12 ≤ D.host.g k) → ∀ (k : Fin 2) (S : Finset (Tup D k)), (∀ t ∈ S, ¬ goodAt D k t) → locShare D (fun k _ => eUk D k (ψ₀ k)) k S ≤ 3 * (D.R.f : ℝ) / (D.host.g k : ℝ) + 23 * (D.R.f : ℝ) * Real.log (D.host.g k : ℝ) / Real.sqrt (D.host.g k : ℝ) + 2 * (D.R.f : ℝ) * (D.R.m : ℝ) * (1 / (4 * ((min D.host.q D.host.d : ℕ) : ℝ)) + (1 + Real.log (D.R.r : ℝ)) / ((D.host.g k : ℝ) - 1)) + (D.R.r : ℝ) / 2 * (7 / 8 : ℝ) ^ D.R.f + Real.exp (-(D.R.f : ℝ) / (5 * Real.log (D.R.r : ℝ))) := by
  first | exact @GlobalTheory.PropWU.propW_eUk | exact GlobalTheory.PropWU.propW_eUk | (intros; apply GlobalTheory.PropWU.propW_eUk <;> assumption)
end
