module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1871
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1780
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1916
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2169
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1887
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1890
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2616
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2617
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2482
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2549
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2233
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2257
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle211
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2170
public import Formalism.LocalToGlobal.ProjectiveLattices.CompHt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2222
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2623
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2265
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle022
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2596
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2624
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2603
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2625
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle013
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle012
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle063
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle631

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.FunObj

theorem squareTriple_of_standing {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T}
    (hL : L.Is μ₀) (W : G.Weil) (t : T) (i j : Fin D.R.m) (hst : SquareStanding G t) : SquareTriple W t i j := by
  intro M hM
  obtain ⟨S₀, Q, hSQ, hX⟩ := GlobalTheory.T.squareCharacters_isGood_gridPlaces hL t i j hst
  choose τf hτf using (GlobalTheory.T.exists_conj_tauE_comp_algebraMap_eq_embedding (D := D))
  obtain ⟨mα, mβ, hα, hβ, hκ⟩ := GlobalTheory.T.thetaGridCharacters_archExponents_gap_gt_rank hL t i j hst τf hτf
  obtain ⟨v₁, hv₁P, hv₁s, hv₁l, ⟨τ₁⟩⟩ := GlobalTheory.T.exists_splitCompletely_auxiliary_place_outside_finset (G := G) hL t (S₀ ∪ Q)
  have hτP : ∀ v : (S₀ ∪ Q : Finset (HeightOneSpectrum (𝓞 D.host.F))),
      Nonempty (D.host.E →ₐ[D.host.F] Fv D.host.F v) := fun v => (hSQ v v.2).2
  let B : Base D.host.F D.host.E :=
    ⟨W.ψ, fun w => ⟨_, hτf w⟩, mα, mβ, S₀ ∪ Q, fun v => (hτP v).some, v₁, τ₁⟩
  have hB : B.IsGood D.sp.cm.sig := GlobalTheory.T.isAdmissibleCMBaseData_of_squareTupleStanding hL W t hst B rfl fun v hv => (hSQ v hv).1
  have hemb : ∀ w x, (B.emb w).1 x = conj (tauE D (τf w) x) := fun _ _ => rfl
  obtain ⟨e⟩ := GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.nonempty_num (G := G) (i := i) (j := j) hL (by omega) (by omega)
  obtain ⟨ΛV, basV, hV⟩ := GlobalTheory.T.exists_hermitian_lattice_local_bases hL W i j B τf hemb
  obtain ⟨ΛV', basV', hV'⟩ := GlobalTheory.T.exists_negConj_member_hermitianLatticeSpaceData hL W i j B τf hemb
  obtain ⟨ΛW, basW, hW⟩ := GlobalTheory.T.gridSquare_skewSumSpace_isSkewHermitianSelfDual hL W i j e B τf hemb
  obtain ⟨co, vac, dom, hMo⟩ := GlobalTheory.T.exists_goodSchrodingerModel_conjugateDoubled hL t i j M hM B hB _ _ rfl _ _ _ _ hV hW
  obtain ⟨co', vac', dom', hMo'⟩ := GlobalTheory.T.squareModel_negSpace_goodSchroedinger hL t i j M hM B hB _ _ rfl _ _ _ _ hV' hW
  obtain ⟨om, hom⟩ := GlobalTheory.T.exists_weilRep_dualPair_characters_beta_quotient hL t i j hst B hB _ _ _ _ _ _ hV hW _ hMo
  obtain ⟨om', hom'⟩ := GlobalTheory.T.exists_weilRep_squarePair_characters_alpha_quotient hL t i j hst B hB _ _ _ _ _ _ hV' hW _ hMo'
  obtain ⟨h1, h2, h3, h4⟩ := GlobalTheory.T.thetaGridSquare_rank_inequalities (G := G) hL i j
  refine ⟨e, B, ⟨(D.R.m - j - 1) / 2, (D.R.m - j) / 2, _, _, _, Model.mk co vac ((M.ν (.grid ((i : ℕ) + 1) ((j : ℕ) + 1))).map
      (conjU (spW G i j) (J := (1 : D.host.E) • (spW G i j).gram) 1 rfl)) dom,
    Model.mk co' vac' ((M.ν (.grid (i : ℕ) (j : ℕ))).map
      (conjU (spW₁ G i j) (J := (-1 : D.host.E) • (spW₁ G i j).gram) (-1) rfl)) dom'⟩,
    ⟨alpha G t i j, beta G i j, S₀, Q⟩, om, om', ?_, ?_, hv₁l⟩
  · exact ⟨rfl, rfl, rfl, rfl, fun w => ⟨τf w, fun _ => rfl, rfl, rfl, rfl⟩, rfl, rfl, rfl, rfl⟩
  · exact ⟨hB, ⟨h1, h2, hκ, h3, h4, hV, hV', hW, hMo, hMo'⟩, hX B subset_rfl hv₁P hv₁s hα hβ, hom, hom'⟩

end GlobalTheory.FunObj

end
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc
open GlobalTheory.CechPic GlobalTheory.AbDual

namespace GlobalTheory.ZarhinFam

def sig : Fin 8 → Fin 4 ⊕ Fin 4 :=
  ![.inl 0, .inl 1, .inl 2, .inl 3, .inr 0, .inr 1, .inr 2, .inr 3]

def oMat (d : ℕ) (k : Fin 8) : ord d :=
  ⟨Matrix.single (Sum.inl 0) (sig k) 1, fun i j => by simp [Matrix.single]⟩

def jlMap (h : ℕ) : (Fin h ⊕ Fin h → ℤ) →+ (Fin (8 * h) ⊕ Fin (8 * h) → ℤ) where
  toFun a := fun
    | .inl i => if hi : (i : ℕ) < h then a (.inl ⟨i, hi⟩) else 0
    | .inr i => if hi : (i : ℕ) < h then a (.inr ⟨i, hi⟩) else 0
  map_zero' := by
    funext i; rcases i with i | i <;> simp
  map_add' a b := by
    funext i; rcases i with i | i <;> simp only [Pi.add_apply] <;> split_ifs <;> simp

def formZ (d h : ℕ) (X Y : Fin 8 → Fin h ⊕ Fin h → ℤ) : ℤ :=
  ∑ k, ∑ l, form d (sig k) (sig l) * omegaStd (X k) (Y l)

def KappaOK (h M d : ℕ) (κ : Fin 8 → (Fin (8 * h) ⊕ Fin (8 * h) → ℤ) →+ (Fin h ⊕ Fin h → ℤ)) : Prop :=
  (∀ a b, formZ d h (fun k => κ k a) (fun k => κ k b) ≡ omegaStd a b [ZMOD (M : ℤ)]) ∧
    (∀ a, κ 0 (jlMap h a) = a) ∧ ∀ k, k ≠ 0 → ∀ a, κ k (jlMap h a) = 0

section Obj

variable {S : Scheme.{0}} (A B : Over S) [GrpObj A] [GrpObj B] [IsCommMonObj A] [IsCommMonObj B]

abbrev Zob : Over S := Out.powObj A 4 ⊗ Out.powObj B 4

def pa (i : Fin 4) : Zob A B ⟶ A := fst _ _ ≫ Out.powPr A i

def pb (j : Fin 4) : Zob A B ⟶ B := snd _ _ ≫ Out.powPr B j

def mkZ {T : Over S} (u : Fin 4 → (T ⟶ A)) (v : Fin 4 → (T ⟶ B)) : T ⟶ Zob A B :=
  lift ((Out.powIsLimit A 4).lift (Fan.mk T u)) ((Out.powIsLimit B 4).lift (Fan.mk T v))

def actZ (d : ℕ) (la : A ⟶ B) (mu : B ⟶ A) (N : ord d) : Zob A B ⟶ Zob A B :=
  mkZ A B
    (fun i => ∏ j, (pa A B j ^ ((N : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) ℤ) (Sum.inl j) (Sum.inl i)) *
      (pb A B j ≫ mu) ^ ((N : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) ℤ) (Sum.inr j) (Sum.inl i) / (d : ℤ))))
    (fun i => ∏ j, ((pa A B j ≫ la) ^ ((N : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) ℤ) (Sum.inl j) (Sum.inr i)) *
      pb A B j ^ ((N : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) ℤ) (Sum.inr j) (Sum.inr i))))

def incZ : A ⟶ Zob A B := mkZ A B (fun i => if i = 0 then 𝟙 A else 1) (fun _ => 1)

def prZ : Zob A B ⟶ A := pa A B 0

def zCls {P : LB (A ⊗ A).left} (hP : P.IsLB) {Q : LB (A ⊗ B).left} (hQ : Q.IsLB) (d : ℕ) (mu : B ⟶ A) :
    CechPic.Pic (Zob A B ⊗ Zob A B).left :=
  (∑ i, CechPic.pull (lift (fst (Zob A B) (Zob A B) ≫ pa A B i) (snd (Zob A B) (Zob A B) ≫ pa A B i)).left
      (cls P hP)) +
    (∑ i, ∑ j, quat d j i • CechPic.pull (lift (fst (Zob A B) (Zob A B) ≫ pa A B i)
      (snd (Zob A B) (Zob A B) ≫ pb A B j)).left (cls Q hQ)) +
    (∑ i, ∑ j, quat d j i • CechPic.pull (lift (snd (Zob A B) (Zob A B) ≫ pa A B i)
      (fst (Zob A B) (Zob A B) ≫ pb A B j)).left (cls Q hQ)) +
    ∑ j, CechPic.pull (lift (snd (Zob A B) (Zob A B) ≫ pb A B j ≫ mu) (fst (Zob A B) (Zob A B) ≫ pb A B j)).left
      (cls Q hQ)

def zP {P : LB (A ⊗ A).left} (hP : P.IsLB) {Q : LB (A ⊗ B).left} (hQ : Q.IsLB) (d : ℕ) (mu : B ⟶ A) :
    LB (Zob A B ⊗ Zob A B).left :=
  (cls_surj (zCls A B hP hQ d mu)).choose

theorem zarhinBundle_isLineBundle {P : LB (A ⊗ A).left} (hP : P.IsLB) {Q : LB (A ⊗ B).left} (hQ : Q.IsLB) (d : ℕ) (mu : B ⟶ A) :
    (zP A B hP hQ d mu).IsLB :=
  (cls_surj (zCls A B hP hQ d mu)).choose_spec.choose

theorem cls_zP {P : LB (A ⊗ A).left} (hP : P.IsLB) {Q : LB (A ⊗ B).left} (hQ : Q.IsLB) (d : ℕ) (mu : B ⟶ A) :
    cls (zP A B hP hQ d mu) (zarhinBundle_isLineBundle A B hP hQ d mu) = zCls A B hP hQ d mu :=
  (cls_surj (zCls A B hP hQ d mu)).choose_spec.choose_spec

end Obj

def levZ {S : Scheme.{0}} {A Z : Over S} [GrpObj Z] [IsCommMonObj Z] {O : Type} {h h' n : ℕ}
    (lev : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over S) ⟶ A)) (inc : A ⟶ Z) (act : O → (Z ⟶ Z)) (o : Fin n → O)
    (κ : Fin n → (Fin h' ⊕ Fin h' → ℤ) →+ (Fin h ⊕ Fin h → ℤ)) (a : Fin h' ⊕ Fin h' → ℤ) : 𝟙_ (Over S) ⟶ Z :=
  (List.ofFn fun k => lev (κ k a) ≫ inc ≫ act (o k)).prod

def ZData {S : Scheme.{0}} {h M : ℕ} {t : S ⟶ Sp (cycAway M)} (c : SiegPre h M (zetaAway M) t) (d : ℕ)
    (B : Over S) [GrpObj B] [IsCommMonObj B] (Q : LB (c.A ⊗ B).left) (la : c.A ⟶ B) (mu : B ⟶ c.A) : Prop :=
  IsAbelianScheme B ∧ IsDual c.A B Q ∧ IsDual B c.A (swap Q) ∧ IsMonHom la ∧ IsMonHom mu ∧
    la ≫ mu = 𝟙 c.A ^ d ∧ mu ≫ la = 𝟙 B ^ d ∧ LBIso c.P (ev Q (fst c.A c.A) (snd c.A c.A ≫ la))

end GlobalTheory.ZarhinFam
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical

noncomputable section

namespace GlobalTheory.LogPole

theorem eq_of_eq_lower_mul_upper {S : Type} [CommRing S] {m : ℕ} {M B L N : Matrix (Fin m) (Fin m) S}
    (hB : ∀ i j, i < j → B i j = 0) (hL : ∀ i j, i < j → L i j = 0)
    (hN : ∀ i j, j < i → N i j = 0) (hN1 : ∀ i, N i i = 1)
    (hM : ∀ i j, j < i → M i j = 0) (hM1 : ∀ i, M i i = 1) (h : M = B * (L * N)) : M = N := by
  set C := B * L with hC
  have hClow : ∀ i j, i < j → C i j = 0 := fun i j hij => by
    rw [hC, Matrix.mul_apply]
    refine Finset.sum_eq_zero fun l _ => ?_
    rcases lt_or_ge i l with h1 | h1
    · rw [hB i l h1, zero_mul]
    · rw [hL l j (lt_of_le_of_lt h1 hij), mul_zero]
  have hMC : M = C * N := by rw [h, hC, Matrix.mul_assoc]
  have hNt : N.BlockTriangular id := fun i j hij => hN i j hij
  have hdet : IsUnit N.det := by
    rw [Matrix.det_of_upperTriangular hNt]
    simp [hN1]
  have hCM : C = M * N⁻¹ := by
    rw [hMC, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hdet, Matrix.mul_one]
  letI := N.invertibleOfIsUnitDet hdet
  have hMt : M.BlockTriangular id := fun i j hij => hM i j hij
  have hCup : C.BlockTriangular id := hCM ▸ hMt.mul (Matrix.blockTriangular_inv_of_blockTriangular hNt)
  have hC1 : C = 1 := by
    ext i j
    rcases lt_trichotomy i j with h1 | rfl | h1
    · rw [hClow i j h1, Matrix.one_apply_ne h1.ne]
    · have e := congrFun (congrFun hMC i) i
      rw [Matrix.mul_apply, Finset.sum_eq_single i (fun l _ hl => ?_) (by simp), hN1, mul_one, hM1] at e
      · rw [← e, Matrix.one_apply_eq]
      · rcases lt_or_gt_of_ne hl with h2 | h2
        · rw [hCup (show id l < id i from h2), zero_mul]
        · rw [hN l i h2, mul_zero]
    · rw [hCup (show id j < id i from h1), Matrix.one_apply_ne h1.ne']
  rw [hMC, hC1, Matrix.one_mul]

theorem top_le_basicOpen_of_isUnit {S : Type} [CommRing S] {X : Scheme.{0}} (x : Sp S ⟶ X) (U : X.Opens)
    (h : ⊤ ≤ x ⁻¹ᵁ U) (a : Γ(X, U)) (hu : IsUnit (ev x U h a)) : ⊤ ≤ x ⁻¹ᵁ X.basicOpen a := by
  have hu' : IsUnit ((x.appLE U ⊤ h).hom a) := by
    have : (x.appLE U ⊤ h).hom a = (Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom (ev x U h a) := by
      show _ = (Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom ((Scheme.ΓSpecIso (CommRingCat.of S)).hom.hom _)
      rw [← CommRingCat.comp_apply, Iso.hom_inv_id]
      rfl
    rw [this]
    exact hu.map _
  have e := Scheme.basicOpen_appLE x ⊤ U h a
  rw [Scheme.basicOpen_of_isUnit _ hu', top_inf_eq] at e
  exact e.le

theorem exists_basicOpen_sub {A : Type} [CommRing A] (O : (Sp A).Opens) (p : Sp A) (hp : p ∈ O) :
    ∃ f : A, f ∉ p.asIdeal ∧ ∀ q : Sp A, f ∉ q.asIdeal → q ∈ O := by
  have hO : IsOpen ((O : Set (Sp A)) : Set (PrimeSpectrum A)) := O.isOpen
  obtain ⟨_, ⟨f, rfl⟩, hpf, hfle⟩ := (PrimeSpectrum.isTopologicalBasis_basic_opens (R := A)).exists_subset_of_mem_open
    (a := p) hp hO
  exact ⟨f, hpf, fun q hq => hfle hq⟩

theorem exists_away_sub {R : Type} [CommRing R] (c : R) (O : (Sp (Localization.Away c)).Opens)
    (p : Sp (Localization.Away c)) (hp : p ∈ O) :
    ∃ (h : R) (ι : Localization.Away c →+* Localization.Away (c * h)), ¬ IsNilpotent (c * h) ∧
      (∀ x, ι (algebraMap R _ x) = algebraMap R _ x) ∧ ⊤ ≤ spMap ι ⁻¹ᵁ O := by
  obtain ⟨f, hpf, hfle⟩ := exists_basicOpen_sub O p hp
  obtain ⟨⟨h', s⟩, hs⟩ := IsLocalization.mk'_surjective (Submonoid.powers c) f
  have hfs : f * algebraMap R (Localization.Away c) s.1 = algebraMap R _ h' := by
    rw [← hs]; exact IsLocalization.mk'_spec _ h' s
  let ι : Localization.Away c →+* Localization.Away (c * h') := IsLocalization.Away.awayToAwayRight c h'
  have hι : ∀ x, ι (algebraMap R _ x) = algebraMap R (Localization.Away (c * h')) x :=
    fun x => IsLocalization.Away.awayToAwayRight_eq c h' x
  have hgu : IsUnit (algebraMap R (Localization.Away (c * h')) (c * h')) :=
    IsLocalization.Away.algebraMap_isUnit _
  have hιf : IsUnit (ι f) := by
    have e := congrArg ι hfs
    rw [map_mul, hι, hι] at e
    rw [map_mul] at hgu
    have hh' := isUnit_of_mul_isUnit_right hgu
    rw [← e] at hh'
    exact isUnit_of_mul_isUnit_left hh'
  refine ⟨h', ι, ?_, hι, fun q _ => ?_⟩
  · rintro ⟨m, hm⟩
    have hA : (algebraMap R (Localization.Away c) (c * h')) ^ m ∈ p.asIdeal := by
      rw [← map_pow, hm, map_zero]; exact p.asIdeal.zero_mem
    have hA' := p.isPrime.mem_of_pow_mem _ hA
    rw [map_mul, ← hfs] at hA'
    have hCa : IsUnit (algebraMap R (Localization.Away c) c) := IsLocalization.Away.algebraMap_isUnit _
    have hsu : IsUnit (algebraMap R (Localization.Away c) s.1) := IsLocalization.map_units _ s
    rcases p.isPrime.mem_or_mem hA' with h1 | h1
    · exact p.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ h1 hCa)
    · rcases p.isPrime.mem_or_mem h1 with h2 | h2
      · exact hpf h2
      · exact p.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ h2 hsu)
  · have : f ∉ ((spMap ι) q).asIdeal := fun hq => q.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hq hιf)
    exact hfle _ this

theorem not_isNilpotent_of_comp_eq {R T : Type} [CommRing R] [CommRing T] (g : R) (hg : ¬ IsNilpotent g)
    (φ : R →+* T) (ψ : T →+* Localization.Away g) (h : ψ.comp φ = algebraMap R _) : ¬ IsNilpotent (φ g) := by
  rintro ⟨m, hm⟩
  have e : algebraMap R (Localization.Away g) (g ^ m) = 0 := by
    rw [map_pow, ← h, RingHom.comp_apply, ← map_pow, hm, map_zero]
  obtain ⟨⟨_, m', rfl⟩, hm'⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers g) _ _).1 e
  exact hg ⟨m' + m, by rw [pow_add]; exact hm'⟩

theorem exists_section_of_away {X Y : Scheme.{0}} (f : Y ⟶ X) (U : X.Opens) (W V : Y.Opens) (hWU : W ≤ f ⁻¹ᵁ U)
    {I : Type} (cc : I → Γ(Y, W)) (a : Γ(X, U)) (ha : f ⁻¹ᵁ X.basicOpen a ≤ V)
    (z₁ : Sp (Localization.Away (MvPolynomial.C a : MvPolynomial I Γ(X, U))) ⟶ Y) (hV : ⊤ ≤ z₁ ⁻¹ᵁ V)
    (hU : ⊤ ≤ (z₁ ≫ f) ⁻¹ᵁ U)
    (hbase : ∀ r, ev (z₁ ≫ f) U hU r = algebraMap (MvPolynomial I Γ(X, U)) _ (MvPolynomial.C r))
    (p : Sp (Localization.Away (MvPolynomial.C a : MvPolynomial I Γ(X, U)))) (hp : p ∈ z₁ ⁻¹ᵁ W)
    (hrel : ∀ (S : Type) [CommRing S] (ψ : Localization.Away (MvPolynomial.C a : MvPolynomial I Γ(X, U)) →+* S)
      (hW : ⊤ ≤ (spMap ψ ≫ z₁) ⁻¹ᵁ W) (i : I),
      ev (spMap ψ ≫ z₁) W hW (cc i) = ψ (algebraMap (MvPolynomial I Γ(X, U)) _ (MvPolynomial.X i))) :
    ∃ g : MvPolynomial I Γ(X, U), ¬ IsNilpotent (MvPolynomial.eval₂Hom (f.appLE U W hWU).hom cc g) ∧
      (∀ (S : Type) [CommRing S] (z₀ : Sp S ⟶ Y) (hz₀ : ⊤ ≤ z₀ ⁻¹ᵁ W),
        IsUnit (ev z₀ W hz₀ (MvPolynomial.eval₂Hom (f.appLE U W hWU).hom cc g)) → ⊤ ≤ z₀ ⁻¹ᵁ V) ∧
      ∃ (z : Sp (Localization.Away g) ⟶ Y) (hz : ⊤ ≤ z ⁻¹ᵁ W), ⊤ ≤ z ⁻¹ᵁ V ∧
        (∀ r, ev z W hz ((f.appLE U W hWU).hom r) =
          algebraMap (MvPolynomial I Γ(X, U)) (Localization.Away g) (MvPolynomial.C r)) ∧
        ∀ i, ev z W hz (cc i) = algebraMap (MvPolynomial I Γ(X, U)) (Localization.Away g) (MvPolynomial.X i) := by
  obtain ⟨h', ι, hnil, hι, hz⟩ := exists_away_sub _ (z₁ ⁻¹ᵁ W) p hp
  have hz' : ⊤ ≤ (spMap ι ≫ z₁) ⁻¹ᵁ W := hz
  have hbz : ∀ r, ev (spMap ι ≫ z₁) W hz' ((f.appLE U W hWU).hom r) =
      algebraMap (MvPolynomial I Γ(X, U)) _ (MvPolynomial.C r) := fun r => by
    rw [FlagMod.ev_appLE (spMap ι ≫ z₁) f hWU hz' (FlagMod.le_preimage_map f hWU hz'),
      FlagMod.ev_congr (Category.assoc _ _ _) U _ (FlagMod.le_preimage_comp (spMap ι) hU),
      FlagMod.ev_spMap ι (z₁ ≫ f) U hU, RingHom.comp_apply, hbase, hι]
  have hcz : ∀ i, ev (spMap ι ≫ z₁) W hz' (cc i) =
      algebraMap (MvPolynomial I Γ(X, U)) _ (MvPolynomial.X i) := fun i => by
    rw [hrel _ ι hz' i, hι]
  refine ⟨MvPolynomial.C a * h', ?_, ?_, spMap ι ≫ z₁, hz', FlagMod.le_preimage_comp _ hV, hbz, hcz⟩
  · refine not_isNilpotent_of_comp_eq _ hnil _ (ev (spMap ι ≫ z₁) W hz') ?_
    refine MvPolynomial.ringHom_ext (fun r => ?_) (fun i => ?_)
    · rw [RingHom.comp_apply, MvPolynomial.eval₂Hom_C]
      exact hbz r
    · rw [RingHom.comp_apply, MvPolynomial.eval₂Hom_X']
      exact hcz i
  · intro S _ z₀ hz₀ hu
    rw [map_mul, map_mul] at hu
    have hu1 := isUnit_of_mul_isUnit_left hu
    rw [MvPolynomial.eval₂Hom_C, FlagMod.ev_appLE z₀ f hWU hz₀ (FlagMod.le_preimage_map f hWU hz₀)] at hu1
    have hb := top_le_basicOpen_of_isUnit _ _ _ a hu1
    exact fun q _ => ha (hb (Set.mem_univ q))

theorem map_entry_eq_of_lower_mul {R A S : Type} [CommRing R] [CommRing A] [CommRing S] {m : ℕ} (χ : R →+* S)
    (ε : A →+* S) (t : ∀ i j : Fin m, i < j → R) {L N : Matrix (Fin m) (Fin m) A} {b : Matrix (Fin m) (Fin m) S}
    (hL : ∀ i j, i < j → L i j = 0) (hN : ∀ i j, j < i → N i j = 0) (hN1 : ∀ i, N i i = 1)
    (hb : ∀ i j, i < j → b i j = 0)
    (hbe : ∀ i j, χ (if h : i < j then t i j h else if i = j then 1 else 0) = ∑ k, b i k * ε ((L * N) k j))
    (i j : Fin m) (hij : i < j) : ε (N i j) = χ (t i j hij) := by
  have key := eq_of_eq_lower_mul_upper
    (M := Matrix.of fun i j => χ (if h : i < j then t i j h else if i = j then 1 else 0))
    (B := b) (L := L.map ε) (N := N.map ε) hb
    (fun i j hij => by simp [Matrix.map_apply, hL i j hij])
    (fun i j hij => by simp [Matrix.map_apply, hN i j hij])
    (fun i => by simp [Matrix.map_apply, hN1 i])
    (fun i j hij => by simp [Matrix.of_apply, not_lt.2 hij.le, hij.ne'])
    (fun i => by simp [Matrix.of_apply])
    (by
      ext i j
      rw [Matrix.of_apply, hbe i j, ← Matrix.map_mul, Matrix.mul_apply]
      rfl)
  have e := congrFun (congrFun key i) j
  simp only [Matrix.of_apply, Matrix.map_apply, dif_pos hij] at e
  exact e.symm

theorem exists_cell_section : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), FnAlgClosed (Xo := Xo) (c := c) → ∀ (U : TF.Y.X.affineOpens) (n : ℕ) (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n) (v : Fin n → (Sp (DualNumber Γ(TF.Y.X, U.1)) ⟶ TF.Y.t.G.left)), IsEigBasis TF U e v → ∀ (W : (Y₀ TF.X Z).Opens) (k : TF.X.F.J) (L N : ∀ σ : E →+* ℂ, Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) Γ(Y₀ TF.X Z, W)) (h : IsCell TF Z U e v W k L N), Nonempty W → ∃ g : MvPolynomial (VIx Dw) Γ(TF.Y.X, U.1), ¬ IsNilpotent (MvPolynomial.eval₂Hom ((toBase TF Z).appLE U.1 W h.2.1).hom (cellCoord N) g) ∧ (∀ (S : Type) [CommRing S] (z₀ : Sp S ⟶ Y₀ TF.X Z) (hz₀ : ⊤ ≤ z₀ ⁻¹ᵁ W), IsUnit (ev z₀ W hz₀ (MvPolynomial.eval₂Hom ((toBase TF Z).appLE U.1 W h.2.1).hom (cellCoord N) g)) → ⊤ ≤ z₀ ⁻¹ᵁ U₀ TF.X Z) ∧ ∃ (z : Sp (Localization.Away g) ⟶ Y₀ TF.X Z) (hz : ⊤ ≤ z ⁻¹ᵁ W), ⊤ ≤ z ⁻¹ᵁ U₀ TF.X Z ∧ (∀ r, ev z W hz (((toBase TF Z).appLE U.1 W h.2.1).hom r) = algebraMap (MvPolynomial (VIx Dw) Γ(TF.Y.X, U.1)) (Localization.Away g) (MvPolynomial.C r)) ∧ ∀ i, ev z W hz (cellCoord N i) = algebraMap (MvPolynomial (VIx Dw) Γ(TF.Y.X, U.1)) (Localization.Away g) (MvPolynomial.X i) := by
  intro E _ _ _ H Dw l Xo c TF Z hF U n e v hv W k L N h hWne
  have h1 := exists_basicOpen_cell_choose E H Dw l Xo c TF Z U W k h.2.1 h.2.2.1 hWne
  refine h1.elim fun a ha => ?_
  have h2 := GlobalTheory.T.exists_bigCellSection_over_basicOpen_interior E H Dw l Xo c TF Z hF U n e v hv W k L N h a ha.1 ha.2
  refine h2.elim fun z₁ hz₁ => hz₁.2.1.elim fun hU hbase => hz₁.2.2.1.elim fun p hp => ?_
  refine exists_section_of_away (toBase TF Z) U.1 W (U₀ TF.X Z) h.2.1 (cellCoord N) a ?_ z₁ hz₁.1 hU hbase p hp ?_
  · intro w hw
    have hcomp : toBase TF Z w = TF.X.π w.1 := Scheme.Hom.comp_apply _ _ _
    have hI : toBase TF Z w ∈ LogKS.interior TF.Y := (ha.1 hw).1.1
    rw [hcomp] at hI
    exact hI
  · intro S _ ψ hW i
    refine (hz₁.2.2.2 S ψ hW i.1).elim fun b hb => ?_
    exact map_entry_eq_of_lower_mul (ψ.comp (algebraMap (MvPolynomial (VIx Dw) Γ(TF.Y.X, U.1)) _))
      (ev (spMap ψ ≫ z₁) W hW) (fun i' j' hij => MvPolynomial.X ⟨i.1, ⟨(i', j'), hij⟩⟩)
      (h.2.2.2.1 i.1) (h.2.2.2.2.2.1 i.1) (h.2.2.2.2.2.2.1 i.1) hb.1 hb.2 i.2.1.1 i.2.1.2 i.2.2

end GlobalTheory.LogPole
end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Heat.Gauge

theorem chart_fn_mul_gen_pow : ∀ (R : Type) [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (n : ℕ) (X : Scheme.{0}) (m m₁ : G.left ⟶ X) (L : LB X) (dd : Fin n → Fld G.left) (D : R → R) (h₁ : Heat G m₁ L dd D) (e : LB.Gen (LB.LinComb L ![m, m₁] ![1, -1])), L.IsLB → e.IsGen → ∀ (k : ℕ) (σ : SecM m₁ L k) (ρ : SecM m L k), (∀ (Z : Scheme.{0}) (r : Z ⟶ G.left) (z : Z) (J : (Z ⟶ X) → L.ι), Good L z J → sval ρ r z J = sval σ r z J * ((val e r z J) ^ k).val) → ∀ (p : h₁.J × (Fin 2 → L.ι)), rsT (ρ.f fun _ => p.2 0) (GlobalTheory.Heat.Gauge.W m h₁ p) = (GlobalTheory.Heat.Gauge.gU m h₁ e p).val ^ k * rsT (σ.f fun _ => h₁.j p.1) (GlobalTheory.Heat.Gauge.W m h₁ p) := by
  intro R _ G _ _ n X m m₁ L dd D h₁ e hL he k σ ρ hρ p
  have le₀ : W m h₁ p ≤ LB.wchart L (K := Fin 1) (fun _ => m) (fun _ => p.2 0) :=
    fun y hy => Set.mem_iInter.2 fun _ => W_le_m m h₁ p hy
  have le₁ : W m h₁ p ≤ LB.wchart L (K := Fin 1) (fun _ => m₁) (fun _ => h₁.j p.1) :=
    fun y hy => Set.mem_iInter.2 fun _ => (W_le_m₁ m h₁ p hy).2
  refine fn_ext fun y hy => ?_
  choose J hJ using fun χ : G.left ⟶ X => exists_chart hL (χ y)
  have hJ' : Good L y J := hJ
  have hy' : (𝟙 G.left : G.left ⟶ G.left) y ∈ W m h₁ p := hy
  have e₀ : gs (𝟙 G.left) y _ (rsT (ρ.f fun _ => p.2 0) (W m h₁ p)) =
      (trF (fun _ : Fin 1 => m) (fun _ => (k : ℤ)) (𝟙 G.left) y (fun _ => p.2 0) (fun _ => J (𝟙 G.left ≫ m))).val *
        sval ρ (𝟙 G.left) y J :=
    (congrArg (gs (𝟙 G.left) y _) (GlobalTheory.KS.rsT_of_le le₀ _)).trans ((gs_res (𝟙 G.left) y le₀ hy' _).trans
      (sec_trans ρ (𝟙 G.left) y (le₀ hy) (hJ'.mem _ (𝟙 G.left))))
  have e₁ : gs (𝟙 G.left) y _ (rsT (σ.f fun _ => h₁.j p.1) (W m h₁ p)) =
      (trF (fun _ : Fin 1 => m₁) (fun _ => (k : ℤ)) (𝟙 G.left) y (fun _ => h₁.j p.1) (fun _ => J (𝟙 G.left ≫ m₁))).val *
        sval σ (𝟙 G.left) y J :=
    (congrArg (gs (𝟙 G.left) y _) (GlobalTheory.KS.rsT_of_le le₁ _)).trans ((gs_res (𝟙 G.left) y le₁ hy' _).trans
      (sec_trans σ (𝟙 G.left) y (le₁ hy) (hJ'.mem _ (𝟙 G.left))))
  have e₂ : gm (𝟙 G.left) y _ (gU m h₁ e p) =
      (trF ![m, m₁] ![1, -1] (𝟙 G.left) y p.2 (fun a => J (𝟙 G.left ≫ ![m, m₁] a)) * val e (𝟙 G.left) y J) *
        gm (𝟙 G.left ≫ m₁) y _ (L.g (p.2 1) (h₁.j p.1)) :=
    (map_mul _ _ _).trans (congrArg₂ (· * ·)
      ((gm_res (𝟙 G.left) y (W_le_wchart m h₁ p) hy' _).trans
        (gen_trans he (𝟙 G.left) y (W_le_wchart m h₁ p hy) (hJ'.mem _ (𝟙 G.left))))
      ((gm_res (𝟙 G.left) y (W_le_m₁ m h₁ p) hy' _).trans (gm_pull (𝟙 G.left) m₁ y _ (W_le_m₁ m h₁ p hy) _)))
  have e₃ : gs (𝟙 G.left) y _ ((gU m h₁ e p).val ^ k) = (gm (𝟙 G.left) y _ (gU m h₁ e p) ^ k).val := by
    rw [← Units.val_pow_eq_pow_val, gs_unit _ _ _ hy', map_pow]
  have hc := gm_cocycle hL (𝟙 G.left ≫ m₁) y (W_le_m₁ m h₁ p hy).1 (W_le_m₁ m h₁ p hy).2 (hJ (𝟙 G.left ≫ m₁))
  rw [gs_mul _ _ _ hy', e₀, e₁, e₃, e₂, hρ _ _ y J hJ', ← _root_.mul_assoc, ← _root_.mul_assoc, mul_right_comm, ← Units.val_mul,
    ← Units.val_mul]
  congr 2
  simp only [trF, Fin.prod_univ_two, Fin.prod_univ_one, Matrix.cons_val_zero, Matrix.cons_val_one, zpow_natCast,
    zpow_one, zpow_neg]
  rw [← mul_pow, ← mul_pow]
  congr 1
  rw [_root_.mul_assoc _ (gm _ _ _ (L.g (p.2 1) _)), hc]
  rw [mul_right_comm _ (val e _ y J)]
  exact congrArg (· * val e _ y J) (inv_mul_cancel_right _ _).symm

end GlobalTheory.Heat.Gauge
end
end

section

open AlgebraicGeometry CategoryTheory TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg GlobalTheory.FlagEmb GlobalTheory.ProjSpace GlobalTheory.FlagMod GlobalTheory.FlagMod.FieldFlag
open GlobalTheory.FlagMod.LowRank (ECh Proj str)

theorem _root_.GlobalTheory.T.flagCellFrames_lastStep_eigenmodules : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (p : Proj (RingHom.id c.F)) (A : Atlas Y p) (Z : Scheme.{0}) (π : Z ⟶ Y.X) (g : ∀ en : En Dw.mult, Z ⟶ PSpace c.F (plN A.N en.1)) (κ : ∀ b, Pm Dw.mult → (Sp (CR Dw.mult (A.V b)) ⟶ Z)) [∀ b w, IsOpenImmersion (κ b w)] (hZ : Cells A π g κ) (ht : FlagCellFrameChangeTriangular hZ), (cellFrames hZ ht).TopEigen := by
  first | exact @GlobalTheory.FlagMod.FieldFlag.cellFrames_topEigen | exact GlobalTheory.FlagMod.FieldFlag.cellFrames_topEigen | (intros; apply GlobalTheory.FlagMod.FieldFlag.cellFrames_topEigen <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.HermitianCompactForm GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.DetLine

theorem _root_.GlobalTheory.T.determinantSection_unit_integral_frames_dvr : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (O' : Type) [CommRing O'] (β' : O' →+* c.F) (Z : Model Xo c β') (U : Set (Xo.XF c)) (τ : E →+* ℂ) (σZ : RuleY Z) (σ : RuleU Xo c), SecY Z (compactOf Z U) τ σZ → NzY Z (compactOf Z U) τ σZ → Restricts Z U τ σZ σ → ∀ (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K] (j : c.F →+* R) (xR : Sp R ⟶ gen Y) (x : Sp K ⟶ Xo.XF c) (V : Set (gen Y)) vR wR v w vb wb, FrY Y V τ j xR vR wR → FrU Xo c U τ ((algebraMap R K).comp j) x v w → x ≫ Y.jQ = spMap (algebraMap R K) ≫ xR → SameVecs Y x v vb → SameVecs Y x w wb → (∀ i, (vb i).left = spMap (Chart.dualMapR (algebraMap R K)) ≫ (vR i).left) → (∀ i, (wb i).left = spMap (Chart.dualMapR (algebraMap R K)) ≫ (wR i).left) → ∃ u : Rˣ, σ K x v w = algebraMap R K u := by
  first | exact @GlobalTheory.DetLine.DvrUnit.unit_in_integral_frame | exact GlobalTheory.DetLine.DvrUnit.unit_in_integral_frame | (intros; apply GlobalTheory.DetLine.DvrUnit.unit_in_integral_frame <;> assumption)
end
