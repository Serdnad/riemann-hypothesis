module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle047
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceUnitaryLocalPointsEquivGL
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2155
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1818
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle133
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle337
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle297
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.AdeleLC
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle054
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2140
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2110
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle055
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanThetaLocalAction
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2141
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Linter.HaveILetI
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
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle057

@[expose] public section

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.BCT.LocCpt

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

omit [IsCMField E] in
theorem continuous_mapLoc (w : Pl E) : Continuous (GeneralLinearGroup.map (n := Fin n) (pLoc E w)) :=
  Continuous.units_map _ (continuous_id.matrix_map (RestrictedProduct.continuous_eval w))

omit [IsCMField E] in
theorem entry_mem_of_mem_KGL {w : Pl E} {g : GL (Fin n) (w.adicCompletion E)} (hg : g ∈ GlobalTheory.LFun.KGL w (n := n)) (i j : Fin n) :
    g.val i j ∈ (w.adicCompletionIntegers E : Set (w.adicCompletion E)) := by
  obtain ⟨k, rfl⟩ := hg
  exact (k.val i j).2


omit [IsCMField E] in
theorem isCompact_box (D : ∀ w : Pl E, Set (GL (Fin n) (w.adicCompletion E))) (hD : ∀ w, IsCompact (D w))
    (hDK : ∀ᶠ w in cofinite, D w ⊆ GlobalTheory.LFun.KGL w (n := n)) :
    IsCompact {g : GL (Fin n) (Af E) | ∀ w, GeneralLinearGroup.map (pLoc E w) g ∈ D w} := by
  let Q : Fin n → Fin n → ∀ w : Pl E, Set (w.adicCompletion E) := fun i j w =>
    (fun g : GL (Fin n) (w.adicCompletion E) => g.val i j) '' D w
  let Q' : Fin n → Fin n → ∀ w : Pl E, Set (w.adicCompletion E) := fun i j w =>
    (fun g : GL (Fin n) (w.adicCompletion E) => (g⁻¹).val i j) '' D w
  have hQ : ∀ i j w, IsCompact (Q i j w) := fun i j w =>
    (hD w).image (Units.continuous_val.matrix_elem i j)
  have hQ' : ∀ i j w, IsCompact (Q' i j w) := fun i j w =>
    (hD w).image (Units.continuous_coe_inv.matrix_elem i j)
  have hQK : ∀ i j, ∀ᶠ w in cofinite, Q i j w ⊆ (w.adicCompletionIntegers E : Set (w.adicCompletion E)) :=
    fun i j => hDK.mono fun w hw => by
      rintro _ ⟨g, hg, rfl⟩
      exact entry_mem_of_mem_KGL (hw hg) i j
  have hQK' : ∀ i j, ∀ᶠ w in cofinite, Q' i j w ⊆ (w.adicCompletionIntegers E : Set (w.adicCompletion E)) :=
    fun i j => hDK.mono fun w hw => by
      rintro _ ⟨g, hg, rfl⟩
      exact entry_mem_of_mem_KGL ((GlobalTheory.LFun.KGL w (n := n)).inv_mem (hw hg)) i j
  let P : Set (Matrix (Fin n) (Fin n) (Af E)) :=
    Set.univ.pi fun i => Set.univ.pi fun j => {a : Af E | ∀ w, a w ∈ Q i j w}
  let P' : Set (Matrix (Fin n) (Fin n) (Af E)) :=
    Set.univ.pi fun i => Set.univ.pi fun j => {a : Af E | ∀ w, a w ∈ Q' i j w}
  have hP : IsCompact P := isCompact_univ_pi fun i => isCompact_univ_pi fun j =>
    GlobalTheory.IdeleCyl.isCompact_restrictedProduct_forall_mem (fun w : Pl E => w.adicCompletion E)
      (fun w => (w.adicCompletionIntegers E : Set (w.adicCompletion E))) (Q i j) (hQ i j) (hQK i j)
  have hP' : IsCompact P' := isCompact_univ_pi fun i => isCompact_univ_pi fun j =>
    GlobalTheory.IdeleCyl.isCompact_restrictedProduct_forall_mem (fun w : Pl E => w.adicCompletion E)
      (fun w => (w.adicCompletionIntegers E : Set (w.adicCompletion E))) (Q' i j) (hQ' i j) (hQK' i j)
  have hC : IsClosed {g : GL (Fin n) (Af E) | ∀ w, GeneralLinearGroup.map (pLoc E w) g ∈ D w} := by
    simp only [Set.setOf_forall]
    refine isClosed_iInter fun w => ?_
    haveI : T2Space (GL (Fin n) (w.adicCompletion E)) := Units.isEmbedding_embedProduct.t2Space
    exact (hD w).isClosed.preimage (continuous_mapLoc w)
  refine IsCompact.of_isClosed_subset (Units.isClosedEmbedding_embedProduct.isCompact_preimage
    (hP.prod (hP'.image MulOpposite.continuous_op))) hC ?_
  intro g hg
  refine ⟨fun i _ j _ w => ⟨GeneralLinearGroup.map (pLoc E w) g, hg w, rfl⟩, ⟨(g⁻¹ : GL (Fin n) (Af E)).val, fun i _ j _ w => ?_, rfl⟩⟩
  refine ⟨GeneralLinearGroup.map (pLoc E w) g, hg w, ?_⟩
  show ((GeneralLinearGroup.map (pLoc E w) g)⁻¹ : GL (Fin n) (w.adicCompletion E)).val i j = _
  rw [← map_inv]
  rfl

end GlobalTheory.BCT.LocCpt

namespace GlobalTheory.BCT.LocCpt

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem mem_GLint_of_entries' {K : Type} [Field K] (O : Subring K) (g : GL (Fin n) K)
    (h1 : ∀ a b, g.val a b ∈ O) (h2 : ∀ a b, (g⁻¹).val a b ∈ O) : g ∈ Formalism.UG.GLint (Fin n) O := by
  have inj : Function.Injective (O.subtype.mapMatrix (m := Fin n)) :=
    fun A B h => by ext i j; exact congrFun (congrFun h i) j
  let A : Matrix (Fin n) (Fin n) O := fun i j => ⟨g.val i j, h1 i j⟩
  let B : Matrix (Fin n) (Fin n) O := fun i j => ⟨(g⁻¹).val i j, h2 i j⟩
  have hA : O.subtype.mapMatrix A = g.val := rfl
  have hB : O.subtype.mapMatrix B = (g⁻¹).val := rfl
  refine ⟨⟨A, B, inj ?_, inj ?_⟩, Units.ext rfl⟩
  · rw [map_mul, hA, hB, map_one, Units.mul_inv]
  · rw [map_mul, hA, hB, map_one, Units.inv_mul]

theorem mem_or_conj_mem {S : Set (Pl E)} (hS : IsSection S) (w : Pl E) :
    w ∈ S ∨ conjSrc (GlobalTheory.SplitPts.conjE E) w ∈ S := by
  obtain ⟨u, ⟨huS, hu⟩, -⟩ := hS w
  by_cases hw : IsSplitAt w
  · rcases (GlobalTheory.SplitPts.over_split hw).2.2 u hu with rfl | rfl
    · exact Or.inl huS
    · exact Or.inr huS
  · left
    by_contra hwS
    exact hw ⟨u, fun h => hwS (h ▸ huS), hu⟩

theorem cLoc_eq_invT (x : UA E n) (w : Pl E) :
    cLoc w x = invT n _ (GeneralLinearGroup.map (conjLoc (GlobalTheory.SplitPts.conjE E) w)
      (cLoc (conjSrc (GlobalTheory.SplitPts.conjE E) w) x)) := by
  set Y := GeneralLinearGroup.map (conjLoc (GlobalTheory.SplitPts.conjE E) w) (cLoc (conjSrc (GlobalTheory.SplitPts.conjE E) w) x)
  have h : (Y.val)ᵀ * (cLoc w x).val = 1 := GlobalTheory.SplitPts.comp_eq x w
  apply Units.ext
  show (cLoc w x).val = ((Y⁻¹).val)ᵀ
  calc (cLoc w x).val = ((Y⁻¹).val)ᵀ * ((Y.val)ᵀ * (cLoc w x).val) := by
        rw [← Matrix.mul_assoc, ← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one, Matrix.one_mul]
    _ = ((Y⁻¹).val)ᵀ := by rw [h, Matrix.mul_one]

end GlobalTheory.BCT.LocCpt


open GlobalTheory.BCT.LocCpt in
theorem GlobalTheory.BCT.LocCpt.loc_cpt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, ∀ S : Set (Pl E),
    IsSection S → ∀ C : ∀ w : Pl E, Set (UL n w), (∀ w, IsCompact (C w)) → (∀ᶠ w in cofinite, C w = KL n w) →
    IsCompact {x : finU (E := E) (n := n) | ∀ w ∈ S, toSub (UL n w) (cLoc w (x : UA E n)) ∈ C w} := by
  intro E _ _ _ hU n S hS C hC hCK
  set c := GlobalTheory.SplitPts.conjE E
  let φ : ∀ w : Pl E, GL (Fin n) ((conjSrc c w).adicCompletion E) → GL (Fin n) (w.adicCompletion E) :=
    fun w g => invT n _ (GeneralLinearGroup.map (conjLoc c w) g)
  have hφ : ∀ w, Continuous (φ w) := fun w => (GlobalTheory.SplitPts.continuous_invT _).comp
    (Continuous.units_map _ (continuous_id.matrix_map (conjLoc_spec c w).1))
  let D : ∀ w : Pl E, Set (GL (Fin n) (w.adicCompletion E)) := fun w =>
    if w ∈ S then Subtype.val '' C w else φ w '' (Subtype.val '' C (conjSrc c w))
  have hD : ∀ w, IsCompact (D w) := by
    intro w
    by_cases hw : w ∈ S
    · simp only [D, if_pos hw]; exact (hC w).image continuous_subtype_val
    · simp only [D, if_neg hw]; exact ((hC _).image continuous_subtype_val).image (hφ w)
  have hDK : ∀ᶠ w in cofinite, D w ⊆ GlobalTheory.LFun.KGL w (n := n) := by
    have h1 : ∀ᶠ w in cofinite, C (conjSrc c w) = KL n (conjSrc c w) :=
      (conjSrc_injective c).tendsto_cofinite.eventually hCK
    filter_upwards [hCK, h1] with w hw hw'
    by_cases hwS : w ∈ S
    · simp only [D, if_pos hwS, hw]
      rintro _ ⟨k, hk, rfl⟩
      exact Subgroup.mem_subgroupOf.1 hk
    · simp only [D, if_neg hwS, hw']
      rintro _ ⟨_, ⟨k, hk, rfl⟩, rfl⟩
      have hk' : (k : GL (Fin n) _) ∈ GlobalTheory.LFun.KGL (conjSrc c w) (n := n) := Subgroup.mem_subgroupOf.1 hk
      have hO : ∀ y, y ∈ ((conjSrc c w).adicCompletionIntegers E : Set _) →
          conjLoc c w y ∈ (w.adicCompletionIntegers E : Set (w.adicCompletion E)) := fun y hy => by
        rw [SetLike.mem_coe, HeightOneSpectrum.mem_adicCompletionIntegers, (conjLoc_spec c w).2.2 y]
        exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 hy
      apply mem_GLint_of_entries'
      · intro a b
        exact hO _ (entry_mem_of_mem_KGL ((GlobalTheory.LFun.KGL _ (n := n)).inv_mem hk') b a)
      · intro a b
        exact hO _ (entry_mem_of_mem_KGL hk' b a)
  have hB := isCompact_box D hD hDK

  have hmem : ∀ (x : finU (E := E) (n := n)) (w : Pl E), toSub (UL n w) (cLoc w (x : UA E n)) ∈ C w ↔
      cLoc w (x : UA E n) ∈ Subtype.val '' C w := by
    intro x w
    have hx := GlobalTheory.BCT.ThBasic.cLoc_mem_UL hU n w (x : UA E n)
    rw [toSub, dite_eq_left hx]
    constructor
    · intro h; exact ⟨_, h, rfl⟩
    · rintro ⟨k, hk, e⟩
      have : k = ⟨_, hx⟩ := Subtype.ext e
      rwa [← this]
  have hclosed : IsClosed {x : finU (E := E) (n := n) | ∀ w ∈ S, toSub (UL n w) (cLoc w (x : UA E n)) ∈ C w} := by
    simp only [hmem, Set.setOf_forall]
    refine isClosed_iInter fun w => isClosed_iInter fun _ => ?_
    haveI : T2Space (GL (Fin n) (w.adicCompletion E)) := Units.isEmbedding_embedProduct.t2Space
    exact ((hC w).image continuous_subtype_val).isClosed.preimage
      ((GlobalTheory.DefU.Inert.continuous_cLoc w).comp continuous_subtype_val)

  haveI := GlobalTheory.DefU.LocAdm.t2Space_adelicGL_cmField (E := E) (n := n)
  have hfc : IsClosed ((finU (E := E) (n := n) : Subgroup (UA E n)) : Set (UA E n)) := by
    haveI : T2Space (GL (Fin n) (Cinf E)) := Units.isEmbedding_embedProduct.t2Space
    have hc := GlobalTheory.CuspRep.ContAut.continuous_map_pInf E n
    exact isClosed_eq (hc.comp continuous_subtype_val) continuous_const
  have hι : Topology.IsClosedEmbedding (fun x : finU (E := E) (n := n) => ((x : UA E n) : GA E n)) :=
    GlobalTheory.DefU.LocAdm.isClosed_UA.isClosedEmbedding_subtypeVal.comp hfc.isClosedEmbedding_subtypeVal
  refine IsCompact.of_isClosed_subset (hι.isCompact_preimage (hB.image GlobalTheory.DefU.LocAdm.continuous_finGL)) hclosed ?_
  intro x hx
  refine ⟨GeneralLinearGroup.map (pFin E) ((x : UA E n) : GA E n), fun w => ?_, ?_⟩
  · have e : ∀ u : Pl E, GeneralLinearGroup.map (pLoc E u) (GeneralLinearGroup.map (pFin E) ((x : UA E n) : GA E n)) =
        cLoc u (x : UA E n) := fun u => Units.ext rfl
    rw [e]
    by_cases hwS : w ∈ S
    · simp only [D, if_pos hwS]
      exact (hmem x w).1 (hx w hwS)
    · simp only [D, if_neg hwS]
      have hw' := (mem_or_conj_mem hS w).resolve_left hwS
      refine ⟨cLoc (conjSrc c w) (x : UA E n), (hmem x _).1 (hx _ hw'), ?_⟩
      exact (cLoc_eq_invT (x : UA E n) w).symm
  · have h1 : GeneralLinearGroup.map (pInf E) ((x : UA E n) : GA E n) = 1 := x.2
    exact ga_ext (by rw [pInf_finGL, h1]) (by rw [pFin_finGL])
end
end

section

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine GlobalTheory.SphEis
open GlobalTheory.ResLine (IsHt SemiLat)
open GlobalTheory.Doubling (absE npow)
open Formalism.UG (cT bc)

noncomputable section

namespace GlobalTheory.SphEis.UnipCrd

section Ring

variable {R : Type} [CommRing R] (s : R →+* R) {n : ℕ} (A : Matrix (Fin n) (Fin n) R)

theorem cT_add' {p q : Type} (M N : Matrix p q R) : cT s (M + N) = cT s M + cT s N := by
  ext i k; simp [cT]

theorem cT_sub' {p q : Type} (M N : Matrix p q R) : cT s (M - N) = cT s M - cT s N := by
  ext i k; simp [cT]

def gr {p q : ℕ} (X : Matrix (Fin n) (Fin p) R) (Y : Matrix (Fin n) (Fin q) R) : Matrix (Fin p) (Fin q) R :=
  cT s X * A * Y

variable {p q k : ℕ}

theorem gr_add_left (X X' : Matrix (Fin n) (Fin p) R) (Y : Matrix (Fin n) (Fin q) R) :
    gr s A (X + X') Y = gr s A X Y + gr s A X' Y := by
  simp [gr, cT_add', Matrix.add_mul]

theorem gr_sub_left (X X' : Matrix (Fin n) (Fin p) R) (Y : Matrix (Fin n) (Fin q) R) :
    gr s A (X - X') Y = gr s A X Y - gr s A X' Y := by
  simp [gr, cT_sub', Matrix.sub_mul]

theorem gr_add_right (X : Matrix (Fin n) (Fin p) R) (Y Y' : Matrix (Fin n) (Fin q) R) :
    gr s A X (Y + Y') = gr s A X Y + gr s A X Y' := by
  simp [gr, Matrix.mul_add]

theorem gr_sub_right (X : Matrix (Fin n) (Fin p) R) (Y Y' : Matrix (Fin n) (Fin q) R) :
    gr s A X (Y - Y') = gr s A X Y - gr s A X Y' := by
  simp [gr, Matrix.mul_sub]

theorem gr_mul_left (X : Matrix (Fin n) (Fin k) R) (M : Matrix (Fin k) (Fin p) R) (Y : Matrix (Fin n) (Fin q) R) :
    gr s A (X * M) Y = cT s M * gr s A X Y := by
  simp [gr, Formalism.UG.cT_mul, Matrix.mul_assoc]

theorem gr_mul_right (X : Matrix (Fin n) (Fin p) R) (Y : Matrix (Fin n) (Fin k) R) (M : Matrix (Fin k) (Fin q) R) :
    gr s A X (Y * M) = gr s A X Y * M := by
  simp [gr, Matrix.mul_assoc]

end Ring

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)

theorem cT_adMat {p q : Type} (X : Matrix p q E) :
    cT (sigR (AF F) σ) (adMat F X) = adMat F (cT (σ : E →+* E) X) := by
  ext i k; simp [cT, adMat, sigR, inclR]

theorem gr_adMat {n p q : ℕ} (J : Matrix (Fin n) (Fin n) E) (X : Matrix (Fin n) (Fin p) E) (Y : Matrix (Fin n) (Fin q) E) :
    gr (sigR (AF F) σ) (adMat F J) (adMat F X) (adMat F Y) = adMat F (cT (σ : E →+* E) X * J * Y) := by
  simp only [gr, cT_adMat, adMat, Matrix.map_mul]

theorem invol (h : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  let τ : E →+* ℂ := (IsAlgClosed.lift (R := ℚ) (M := ℂ) (S := E)).toRingHom
  apply τ.injective
  rw [h.2.2.2, h.2.2.2, star_star]

theorem sigR_invol (h : IsCMExt F E σ) (x : AF F ⊗[F] E) : sigR (AF F) σ (sigR (AF F) σ x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a e => simp [sigR, invol σ h]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem cT_cT (h : IsCMExt F E σ) {p q : Type} (M : Matrix p q (AF F ⊗[F] E)) :
    cT (sigR (AF F) σ) (cT (sigR (AF F) σ) M) = M := by
  ext i k; simp [cT, sigR_invol σ h]

theorem cT_inv_herm {m : ℕ} (J₀ : Matrix (Fin m) (Fin m) E) (h : IsHermND σ J₀) :
    cT (σ : E →+* E) J₀⁻¹ = J₀⁻¹ := by
  have hJ : cT (σ : E →+* E) J₀ = J₀ := by
    ext i k; simp [cT, h.1]
  have hu : IsUnit J₀.det := isUnit_iff_ne_zero.mpr h.2
  have e : cT (σ : E →+* E) J₀⁻¹ * J₀ = 1 := by
    calc cT (σ : E →+* E) J₀⁻¹ * J₀ = cT (σ : E →+* E) J₀⁻¹ * cT (σ : E →+* E) J₀ := by rw [hJ]
      _ = cT (σ : E →+* E) (J₀ * J₀⁻¹) := (Formalism.UG.cT_mul _ _ _).symm
      _ = 1 := by rw [Matrix.mul_nonsing_inv _ hu, Formalism.UG.cT_one]
  exact (Matrix.inv_eq_left_inv e).symm

theorem exists_unipRad_crd : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (j m : ℕ) (C D : Matrix (Fin n) (Fin j) E) (Z : Matrix (Fin n) (Fin m) E) (J₀ : Matrix (Fin m) (Fin m) E), Fr σ J C D Z J₀ → ∀ (b : Matrix (Fin j) (Fin m) (AF F ⊗[F] E)) (c : Matrix (Fin j) (Fin j) (AF F ⊗[F] E)), c + cT (sigR (AF F) σ) c + b * plus σ J₀ b = 0 → ∃ u ∈ unipRad σ J C, Crd σ J C D Z J₀ u b c := by
  intro F E _ _ _ _ _ σ n J j m C D Z J₀ hF b c hc
  set s := sigR (AF F) σ with hs
  set p := plus σ J₀ b with hp
  have hu : IsUnit J₀.det := isUnit_iff_ne_zero.mpr hF.herm₀.2
  have key : cT s p * adMat F J₀ = b := by
    rw [hp, plus, Formalism.UG.cT_mul, cT_cT σ hF.cm, cT_adMat, cT_inv_herm σ J₀ hF.herm₀, Matrix.mul_assoc, adMat,
      adMat, ← Matrix.map_mul, Matrix.nonsing_inv_mul _ hu, Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one]
  have g0 : ∀ {p q : ℕ} (X : Matrix (Fin n) (Fin p) E) (Y : Matrix (Fin n) (Fin q) E), cT (σ : E →+* E) X * J * Y = 0 →
      gr s (adMat F J) (adMat F X) (adMat F Y) = 0 := by
    intro p q X Y h; rw [gr_adMat, h]; simp
  have g1 : ∀ (X Y : Matrix (Fin n) (Fin j) E), cT (σ : E →+* E) X * J * Y = 1 →
      gr s (adMat F J) (adMat F X) (adMat F Y) = 1 := by
    intro X Y h; rw [gr_adMat, h]; exact Matrix.map_one _ (map_zero _) (map_one _)
  have gzz : gr s (adMat F J) (adMat F Z) (adMat F Z) = adMat F J₀ := by rw [gr_adMat, hF.zz]
  have hcc := g0 C C hF.cc
  have hdd := g0 D D hF.dd
  have hcz := g0 C Z hF.cz
  have hdz := g0 D Z hF.dz
  have hzc := g0 Z C hF.zc
  have hzd := g0 Z D hF.zd
  have hcd := g1 C D hF.cd
  have hdc := g1 D C hF.dc
  have Ecd : cT s (adMat F C) * adMat F J * (adMat F D - adMat F Z * p + adMat F C * c) = 1 := by
    show gr s (adMat F J) _ _ = 1
    simp only [gr_add_right, gr_sub_right, gr_mul_right, hcd, hcz, hcc]
    simp
  have Ecz : cT s (adMat F C) * adMat F J * (adMat F Z + adMat F C * b) = 0 := by
    show gr s (adMat F J) _ _ = 0
    simp only [gr_add_right, gr_mul_right, hcz, hcc]
    simp
  have Ezz : cT s (adMat F Z + adMat F C * b) * adMat F J * (adMat F Z + adMat F C * b) = adMat F J₀ := by
    show gr s (adMat F J) _ _ = _
    simp only [gr_add_right, gr_add_left, gr_mul_right, gr_mul_left, hcz, hcc, hzc, gzz]
    simp
  have Edz : cT s (adMat F D - adMat F Z * p + adMat F C * c) * adMat F J * (adMat F Z + adMat F C * b) = 0 := by
    show gr s (adMat F J) _ _ = 0
    simp only [gr_add_right, gr_add_left, gr_sub_left, gr_mul_right, gr_mul_left, hcz, hcc, hzc, gzz, hdz, hdc]
    simp [key]
  have Edd : cT s (adMat F D - adMat F Z * p + adMat F C * c) * adMat F J * (adMat F D - adMat F Z * p + adMat F C * c) = 0 := by
    show gr s (adMat F J) _ _ = 0
    simp only [gr_add_right, gr_add_left, gr_sub_left, gr_sub_right, gr_mul_right, gr_mul_left, hcz, hcc, hzc, gzz,
      hdz, hdc, hcd, hdd, hzd]
    simp only [Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_one, Matrix.one_mul, sub_zero, zero_add, add_zero, zero_sub,
      sub_neg_eq_add, key]
    simp only [Matrix.neg_mul, sub_neg_eq_add]
    rw [← hc]
    abel
  obtain ⟨g, h1, h2, h3⟩ := GlobalTheory.T.exists_unitaryAdelicPoint_prescribed_frameImages F E σ n J j m C D Z J₀ hF (adMat F C) (adMat F D - adMat F Z * p + adMat F C * c)
    (adMat F Z + adMat F C * b) hcc Edd Ecd Ecz Edz Ezz
  exact ⟨g, (GlobalTheory.T.mem_isotropicUnipotentRadical_iff_frame F E σ n J j m C D Z J₀ hF g).mpr ⟨h1, b, h2⟩, h1, h2, h3⟩

end GlobalTheory.SphEis.UnipCrd
end
end

section

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine GlobalTheory.SphEis
open GlobalTheory.ResLine (IsHt SemiLat)
open GlobalTheory.Doubling (absE npow)
open Formalism.UG (cT bc)

namespace GlobalTheory.SphEis

theorem adelicConjTranspose_adelicMatrixOfTensor {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] (σ : E →ₐ[F] E)
    {a b : Type} (X : Matrix a b E) :
    cT (sigR (AF F) σ) (adMat F X) = adMat F (cT (σ : E →+* E) X) := by
  ext i k
  simp [cT, adMat, sigR, inclR]

theorem adelicMatrixOfTensor_gram_conjTranspose_mul {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] (σ : E →ₐ[F] E)
    {n a b : ℕ} (J : Matrix (Fin n) (Fin n) E) (X : Matrix (Fin n) (Fin a) E) (Y : Matrix (Fin n) (Fin b) E) :
    cT (sigR (AF F) σ) (adMat F X) * adMat F J * adMat F Y = adMat F (cT (σ : E →+* E) X * J * Y) := by
  rw [adelicConjTranspose_adelicMatrixOfTensor]
  simp only [adMat, Matrix.map_mul]

theorem ringHomConjTranspose_mul_rev {A : Type} [CommRing A] (s : A →+* A) {a b c : ℕ} (X : Matrix (Fin a) (Fin b) A)
    (Y : Matrix (Fin b) (Fin c) A) : cT s (X * Y) = cT s Y * cT s X := by
  simp [cT, Matrix.map_mul, Matrix.transpose_mul]

theorem core_embeds : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (j m : ℕ) (C D : Matrix (Fin n) (Fin j) E) (Z : Matrix (Fin n) (Fin m) E) (J₀ : Matrix (Fin m) (Fin m) E), Fr σ J C D Z J₀ → ∃ e : GAd σ J₀ →* GAd σ J, Continuous e ∧ (∀ g, e g ∈ fixG σ J C ∧ e g ∈ fixG σ J D ∧ (matHom _ σ J (e g)).1 * adMat F Z = adMat F Z * (matHom _ σ J₀ g).1) ∧ ∀ g ∈ ratPts σ J₀, e g ∈ ratPts σ J := by
  intro F E _ _ _ _ _ σ n J j m C D Z J₀ hF
  have hU : ∀ g : GAd σ J₀, cT (sigR (AF F) σ) (matHom _ σ J₀ g).1 * adMat F J₀ * (matHom _ σ J₀ g).1 = adMat F J₀ :=
    fun g => g.2
  have hZ' : ∀ g : GAd σ J₀, cT (sigR (AF F) σ) (adMat F Z * (matHom _ σ J₀ g).1) * adMat F J *
      (adMat F Z * (matHom _ σ J₀ g).1) = adMat F J₀ := by
    intro g
    rw [ringHomConjTranspose_mul_rev]
    have h := adelicMatrixOfTensor_gram_conjTranspose_mul (F := F) σ J Z Z
    rw [hF.zz] at h
    calc _ = cT (sigR (AF F) σ) (matHom _ σ J₀ g).1 * (cT (sigR (AF F) σ) (adMat F Z) * adMat F J * adMat F Z) *
          (matHom _ σ J₀ g).1 := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [h, hU]
  have img : ∀ g : GAd σ J₀, ∃ h : GAd σ J, (matHom _ σ J h).1 * adMat F C = adMat F C ∧
      (matHom _ σ J h).1 * adMat F Z = adMat F Z * (matHom _ σ J₀ g).1 ∧ (matHom _ σ J h).1 * adMat F D = adMat F D :=
    fun g => GlobalTheory.T.exists_unitaryAdelicPoint_prescribed_frameImages F E σ n J j m C D Z J₀ hF (adMat F C) (adMat F D) (adMat F Z * (matHom _ σ J₀ g).1)
      (by rw [adelicMatrixOfTensor_gram_conjTranspose_mul, hF.cc]; simp [adMat]) (by rw [adelicMatrixOfTensor_gram_conjTranspose_mul, hF.dd]; simp [adMat])
      (by rw [adelicMatrixOfTensor_gram_conjTranspose_mul, hF.cd]; simp [adMat])
      (by rw [← Matrix.mul_assoc, adelicMatrixOfTensor_gram_conjTranspose_mul, hF.cz]; simp [adMat])
      (by rw [← Matrix.mul_assoc, adelicMatrixOfTensor_gram_conjTranspose_mul, hF.dz]; simp [adMat]) (hZ' g)
  choose f hC hZ hD using img
  have hmul : ∀ a b, f (a * b) = f a * f b := by
    intro a b
    apply GlobalTheory.SphEis.eq_of_frame_cols F E σ n J j m C D Z J₀ hF
    · rw [hC, map_mul, Units.val_mul, Matrix.mul_assoc, hC, hC]
    · rw [hZ]
      symm
      calc (matHom _ σ J (f a * f b)).1 * adMat F Z
          = (matHom _ σ J (f a)).1 * ((matHom _ σ J (f b)).1 * adMat F Z) := by
            rw [map_mul, Units.val_mul, Matrix.mul_assoc]
        _ = ((matHom _ σ J (f a)).1 * adMat F Z) * (matHom _ σ J₀ b).1 := by rw [hZ, Matrix.mul_assoc]
        _ = _ := by rw [hZ, map_mul, Units.val_mul, Matrix.mul_assoc]
    · rw [hD, map_mul, Units.val_mul, Matrix.mul_assoc, hD, hD]
  refine ⟨MonoidHom.mk' f hmul, ?_, fun g => ⟨hC g, hD g, hZ g⟩, ?_⟩
  · haveI : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
    haveI : IsTopologicalRing (AF F ⊗[F] E) := IsModuleTopology.isTopologicalRing (AF F) _
    apply GlobalTheory.T.continuous_unitaryAdelic_of_frameColumns F E σ n J j m C D Z J₀ hF (GAd σ J₀) f
    · simp only [hC]; exact continuous_const
    · simp only [hZ]
      exact continuous_const.matrix_mul (Units.continuous_val.comp (isEmbedding_matHom (AF F) σ J₀).continuous)
    · simp only [hD]; exact continuous_const
  · intro g hg
    change (matHom _ σ J₀ g) ∈ HFin (AF F) σ J₀ at hg
    rw [HFin, Subgroup.mem_map] at hg
    obtain ⟨γ, -, hγ⟩ := hg
    have hg' : (matHom _ σ J₀ g).1 = adMat F γ.1 := by
      rw [← hγ]; rfl
    apply GlobalTheory.T.mem_unitaryRationalPoints_of_frameImages_rational F E σ n J j m C D Z J₀ hF (f g) C D (Z * γ.1) (hC g)
    · rw [hZ, hg', adMat, adMat, adMat, Matrix.map_mul]
    · exact hD g

end GlobalTheory.SphEis
end

section

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun

theorem _root_.GlobalTheory.T.archimedean_theta_local_action : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (g : UA σ G.V'.J) (h : UA σ G.W.J), At (evI F) (mat g - 1) → At (evI F) (mat h - 1) →
    ∀ (f : SInf F (Fin a' × Fin (a + a'))) (φ : ∀ w : Pl (F := F), (Fin a' × Fin (a + a') → Fv F w) → ℂ),
    (∀ w, φ w ∈ SB (Fin a' × Fin (a + a') → Fv F w)) → (∀ᶠ w in Filter.cofinite, φ w = G.M'.vac w) →
    ∃ f₂ : SInf F (Fin a' × Fin (a + a')), om' (g, h) (pure f φ) = pure f₂ φ := by
  first | exact @GlobalTheory.ArchPure.arch_pure | exact GlobalTheory.ArchPure.arch_pure | (intros; apply GlobalTheory.ArchPure.arch_pure <;> assumption)
end

section

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Classical

theorem _root_.GlobalTheory.T.triple_lattice_invariant_schwartz_local : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (w : Pl (F := F)) (g : (Fin a' × Fin (a + a') → Fv F w) → ℂ), g ∈ SB (Fin a' × Fin (a + a') → Fv F w) →
    (∀ γ ∈ latAtV G.V' G.W w, ∀ c : ℂ, Acts (evFin F w) (G.M'.co.rho B.ψ γ) (G.M'.vac w) (c • G.M'.vac w) →
      Acts (evFin F w) (G.M'.co.rho B.ψ γ) g (c • g)) →
    ∃ r : ℂ, g = r • G.M'.vac w := by
  first | exact @GlobalTheory.VacLine.eigen_line | exact GlobalTheory.VacLine.eigen_line | (intros; apply GlobalTheory.VacLine.eigen_line <;> assumption)
end
